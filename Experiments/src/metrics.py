"""Scaled scalar quantization direction-error metrics."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Optional

import numpy as np

from .datatypes import ScalarFormat
from .oracle_batch import OracleBackend, nearest_direction_cosines_batch
from .utils import angle_from_dot, random_unit_vectors


MAX_EXACT_SCALED_SCALAR_QUANT_POSITIVE_LEVELS = 255
MAX_SCALED_SCALAR_QUANT_BREAKPOINT_ENTRIES_PER_BATCH = 2_000_000


@dataclass
class MetricConfig:
    query_chunk_size: int = 4096
    query_vectors: int = 20_000
    seed: int = 0
    metric_device: str = "auto"


@dataclass(frozen=True)
class MetricBackend:
    name: str
    device: str
    torch: Any = None

    @property
    def is_torch(self) -> bool:
        return self.torch is not None


@dataclass(frozen=True)
class ScalarQuantizationDirectionErrorStats:
    mean: float
    median: float
    p95: float
    p99: float
    worst: float


def _numpy_backend() -> MetricBackend:
    return MetricBackend(name="numpy", device="cpu")


def _import_torch() -> Any:
    try:
        import torch
    except ImportError as exc:
        raise ValueError(
            "PyTorch is required for GPU metric execution. Install a CUDA-enabled PyTorch build, "
            "or use --metric-device cpu."
        ) from exc
    return torch


def resolve_metric_backend(metric_device: str = "auto") -> MetricBackend:
    requested = metric_device.strip().lower()
    if requested in {"", "auto"}:
        try:
            torch = _import_torch()
        except ValueError:
            return _numpy_backend()
        if torch.cuda.is_available():
            return MetricBackend(name="torch", device="cuda", torch=torch)
        return _numpy_backend()

    if requested in {"cpu", "numpy"}:
        return _numpy_backend()

    torch = _import_torch()
    device = str(torch.device(requested))
    if not device.startswith("cuda"):
        raise ValueError(
            "Only CUDA GPU execution is supported because the metrics are kept in float64 for correctness. "
            "Use --metric-device auto/cpu or a CUDA device such as cuda or cuda:0."
        )
    if not torch.cuda.is_available():
        raise ValueError("CUDA metric execution was requested, but torch.cuda.is_available() is False.")
    return MetricBackend(name="torch", device=device, torch=torch)


def _coerce_metric_backend(backend: Optional[MetricBackend]) -> MetricBackend:
    return _numpy_backend() if backend is None else backend


def _oracle_backend_from_metric_backend(backend: MetricBackend) -> OracleBackend:
    if backend.is_torch:
        return OracleBackend(name="torch", device=backend.device, torch=backend.torch)
    return OracleBackend(name="numpy", device="cpu")


def _nan_scalar_quantization_direction_error_stats() -> ScalarQuantizationDirectionErrorStats:
    return ScalarQuantizationDirectionErrorStats(
        mean=np.nan,
        median=np.nan,
        p95=np.nan,
        p99=np.nan,
        worst=np.nan,
    )


def _scalar_quantization_metric_dict(
    metric_prefix: str,
    stats: ScalarQuantizationDirectionErrorStats,
) -> dict[str, float]:
    return {
        f"mean_{metric_prefix}_rad": float(stats.mean),
        f"median_{metric_prefix}_rad": float(stats.median),
        f"p95_{metric_prefix}_rad": float(stats.p95),
        f"p99_{metric_prefix}_rad": float(stats.p99),
        f"max_{metric_prefix}_rad": float(stats.worst),
    }


def _extract_signed_scalar_levels(ordered_scalars: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    ordered_scalars = np.asarray(ordered_scalars, dtype=np.float64)
    if ordered_scalars.ndim != 1 or ordered_scalars.size == 0:
        raise ValueError("ordered_scalars must be a non-empty 1D array.")

    if not np.any(ordered_scalars == 0.0):
        raise ValueError("ordered_scalars must contain 0.0 for scaled scalar quantization search.")

    positive_levels = ordered_scalars[ordered_scalars > 0.0]
    negative_levels = -ordered_scalars[ordered_scalars < 0.0][::-1]
    if positive_levels.size == 0 and negative_levels.size == 0:
        raise ValueError("ordered_scalars must contain at least one non-zero value.")
    return positive_levels, negative_levels


def _scaled_scalar_quantization_batch_size(
    requested_batch_size: int,
    dimension: int,
    level_count_per_coordinate: int,
) -> int:
    if requested_batch_size < 1:
        raise ValueError("requested_batch_size must be at least 1.")
    if dimension < 1:
        raise ValueError("dimension must be at least 1.")
    if level_count_per_coordinate < 1:
        raise ValueError("level_count_per_coordinate must be at least 1.")

    max_batch_size = max(
        1,
        MAX_SCALED_SCALAR_QUANT_BREAKPOINT_ENTRIES_PER_BATCH // (dimension * level_count_per_coordinate),
    )
    return min(requested_batch_size, max_batch_size)


def _prepare_backend_matrix(matrix: np.ndarray, backend: MetricBackend) -> np.ndarray | Any:
    matrix64 = np.ascontiguousarray(matrix, dtype=np.float64)
    if backend.is_torch:
        return backend.torch.as_tensor(
            matrix64,
            dtype=backend.torch.float64,
            device=backend.device,
        )
    return matrix64


def _summarize_scalar_quantization_direction_errors(
    angular_errors: np.ndarray,
) -> ScalarQuantizationDirectionErrorStats:
    angular_errors = np.asarray(angular_errors, dtype=np.float64)
    if angular_errors.size == 0:
        return _nan_scalar_quantization_direction_error_stats()

    median, p95, p99 = np.percentile(angular_errors, [50.0, 95.0, 99.0])
    return ScalarQuantizationDirectionErrorStats(
        mean=float(np.mean(angular_errors)),
        median=float(median),
        p95=float(p95),
        p99=float(p99),
        worst=float(np.max(angular_errors)),
    )


def scaled_sampled_scalar_quantization_direction_errors(
    dimension: int,
    query_vectors: int,
    seed: int,
    scalar_format: ScalarFormat,
    ordered_scalars: Optional[np.ndarray] = None,
    batch_size: int = 2048,
    backend: Optional[MetricBackend] = None,
) -> ScalarQuantizationDirectionErrorStats:
    """Return direction-error summary stats for the best positive rescaling.

    For each random unit vector u, this searches every distinct coordinatewise
    scalar-quantization region induced by positive rescalings of u and reports
    the minimum angular error between the original direction and the quantized
    direction.
    """
    backend = _coerce_metric_backend(backend)
    rng = np.random.default_rng(seed)

    if ordered_scalars is None:
        ordered_scalars = scalar_format.ordered_values(dimension)

    unit_queries = random_unit_vectors(query_vectors, dimension, rng)
    if unit_queries.shape[0] == 0:
        return _summarize_scalar_quantization_direction_errors(np.array([], dtype=np.float64))

    positive_levels, negative_levels = _extract_signed_scalar_levels(ordered_scalars)
    effective_batch_size = _scaled_scalar_quantization_batch_size(
        requested_batch_size=batch_size,
        dimension=dimension,
        level_count_per_coordinate=max(positive_levels.size, negative_levels.size),
    )
    oracle_backend = _oracle_backend_from_metric_backend(backend)

    prepared_queries = unit_queries
    if backend.is_torch:
        prepared_queries = _prepare_backend_matrix(unit_queries, backend)

    dots = nearest_direction_cosines_batch(
        prepared_queries,
        positive_levels,
        negative_levels=negative_levels,
        backend=oracle_backend,
        batch_size=effective_batch_size,
        targets_prepared=True,
    )
    angular = angle_from_dot(dots)
    return _summarize_scalar_quantization_direction_errors(angular)


def compute_scaled_scalar_quantization_only_metrics(
    dimension: int,
    config: MetricConfig,
    scalar_format: ScalarFormat,
    backend: Optional[MetricBackend] = None,
) -> dict[str, float]:
    backend = resolve_metric_backend(config.metric_device) if backend is None else _coerce_metric_backend(backend)

    ordered_scalars = scalar_format.normalized_ordered_values(dimension)
    try:
        positive_levels, negative_levels = _extract_signed_scalar_levels(ordered_scalars)
    except ValueError:
        scaled_scalar_quant_error_stats = _nan_scalar_quantization_direction_error_stats()
    else:
        if max(positive_levels.size, negative_levels.size) > MAX_EXACT_SCALED_SCALAR_QUANT_POSITIVE_LEVELS:
            scaled_scalar_quant_error_stats = _nan_scalar_quantization_direction_error_stats()
        else:
            scaled_scalar_quant_error_stats = scaled_sampled_scalar_quantization_direction_errors(
                dimension=dimension,
                query_vectors=config.query_vectors,
                seed=config.seed + 505,
                scalar_format=scalar_format,
                ordered_scalars=ordered_scalars,
                batch_size=config.query_chunk_size,
                backend=backend,
            )

    return _scalar_quantization_metric_dict("worst_case_angular_error", scaled_scalar_quant_error_stats)
