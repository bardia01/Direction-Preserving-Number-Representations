"""Shared batched exact-coverage oracle with optional CUDA execution."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Optional, Sequence

import numpy as np


@dataclass(frozen=True)
class OracleBackend:
    name: str
    device: str
    torch: Any = None

    @property
    def is_torch(self) -> bool:
        return self.torch is not None


def _numpy_backend() -> OracleBackend:
    return OracleBackend(name="numpy", device="cpu")


def _import_torch() -> Any:
    try:
        import torch
    except ImportError as exc:
        raise ValueError(
            "PyTorch is required for CUDA oracle execution. Install a CUDA-enabled PyTorch build, "
            "or use device='cpu' / device='numpy'."
        ) from exc
    return torch


def resolve_oracle_backend(device: str = "auto") -> OracleBackend:
    requested = device.strip().lower()
    if requested in {"", "auto"}:
        try:
            torch = _import_torch()
        except ValueError:
            return _numpy_backend()
        if torch.cuda.is_available():
            return OracleBackend(name="torch", device="cuda", torch=torch)
        return _numpy_backend()

    if requested in {"cpu", "numpy"}:
        return _numpy_backend()

    torch = _import_torch()
    resolved_device = str(torch.device(requested))
    if not resolved_device.startswith("cuda"):
        raise ValueError(
            "Only CUDA GPU execution is supported for the batched oracle. "
            "Use device='auto'/'cpu' or a CUDA device such as 'cuda' or 'cuda:0'."
        )
    if not torch.cuda.is_available():
        raise ValueError("CUDA oracle execution was requested, but torch.cuda.is_available() is False.")
    return OracleBackend(name="torch", device=resolved_device, torch=torch)


def _coerce_backend(backend: Optional[OracleBackend]) -> OracleBackend:
    return _numpy_backend() if backend is None else backend


def _validate_positive_levels(
    levels: Sequence[float],
    *,
    name: str,
    allow_empty: bool = False,
) -> np.ndarray:
    levels_np = np.sort(np.asarray(levels, dtype=np.float64))
    if levels_np.ndim != 1:
        raise ValueError(f"{name} must be a 1D array.")
    if levels_np.size == 0 and not allow_empty:
        raise ValueError(f"{name} must be a non-empty 1D array.")
    if np.any(levels_np <= 0.0):
        raise ValueError(f"{name} must be strictly positive.")
    return levels_np


def _pad_quantization_levels(levels: np.ndarray, padded_mid_count: int) -> tuple[np.ndarray, np.ndarray]:
    if padded_mid_count < 0:
        raise ValueError("padded_mid_count must be non-negative.")

    q_levels = np.concatenate([np.array([0.0], dtype=np.float64), levels])
    mids = 0.5 * (q_levels[:-1] + q_levels[1:])

    mids_padded = np.full(padded_mid_count, np.inf, dtype=np.float64)
    mids_padded[: mids.size] = mids

    q_levels_padded = np.full(padded_mid_count + 1, q_levels[-1], dtype=np.float64)
    q_levels_padded[: q_levels.size] = q_levels
    return mids_padded, q_levels_padded


def prepare_unit_vectors_for_backend(
    vectors: np.ndarray | Any,
    backend: Optional[OracleBackend] = None,
) -> np.ndarray | Any:
    backend = _coerce_backend(backend)
    if backend.is_torch and isinstance(vectors, backend.torch.Tensor):
        prepared = vectors.to(device=backend.device, dtype=backend.torch.float64)
        if prepared.ndim != 2:
            raise ValueError("vectors must be a 2D array of shape (count, dimension).")
        norms = backend.torch.linalg.vector_norm(prepared, dim=1, keepdim=True)
        if backend.torch.any(norms <= 0.0):
            raise ValueError("vectors must not contain zero rows.")
        return prepared / norms

    prepared_np = np.ascontiguousarray(np.asarray(vectors, dtype=np.float64))
    if prepared_np.ndim != 2:
        raise ValueError("vectors must be a 2D array of shape (count, dimension).")
    norms = np.linalg.norm(prepared_np, axis=1, keepdims=True)
    if np.any(norms <= 0.0):
        raise ValueError("vectors must not contain zero rows.")
    prepared_np = prepared_np / norms
    if backend.is_torch:
        return backend.torch.as_tensor(
            prepared_np,
            dtype=backend.torch.float64,
            device=backend.device,
        )
    return prepared_np


def _interval_probes_numpy(sorted_breakpoints: np.ndarray, dedup_rtol: float) -> tuple[np.ndarray, np.ndarray]:
    batch = sorted_breakpoints.shape[0]
    zeros = np.zeros((batch, 1), dtype=np.float64)
    infs = np.full((batch, 1), np.inf, dtype=np.float64)
    left = np.concatenate([zeros, sorted_breakpoints], axis=1)
    right = np.concatenate([sorted_breakpoints, infs], axis=1)

    finite_left = np.isfinite(left)
    finite_right = np.isfinite(right)
    valid_start = (left == 0.0) & finite_right & (right > 0.0)
    valid_finite = finite_left & finite_right & (right > left * (1.0 + dedup_rtol))
    valid_tail = finite_left & ~finite_right
    valid = valid_start | valid_finite | valid_tail

    alphas = np.ones_like(left)
    alphas[valid_start] = 0.5 * right[valid_start]
    alphas[valid_tail] = 2.0 * left[valid_tail]
    finite_products = left[valid_finite] * right[valid_finite]
    alphas[valid_finite] = np.sqrt(finite_products)
    return alphas, valid


def _interval_probes_torch(sorted_breakpoints: Any, dedup_rtol: float, backend: OracleBackend) -> tuple[Any, Any]:
    torch = backend.torch
    batch = sorted_breakpoints.shape[0]
    zeros = torch.zeros((batch, 1), dtype=torch.float64, device=backend.device)
    infs = torch.full((batch, 1), float("inf"), dtype=torch.float64, device=backend.device)
    left = torch.cat([zeros, sorted_breakpoints], dim=1)
    right = torch.cat([sorted_breakpoints, infs], dim=1)

    finite_left = torch.isfinite(left)
    finite_right = torch.isfinite(right)
    valid_start = (left == 0.0) & finite_right & (right > 0.0)
    valid_finite = finite_left & finite_right & (right > left * (1.0 + dedup_rtol))
    valid_tail = finite_left & ~finite_right
    valid = valid_start | valid_finite | valid_tail

    alphas = torch.ones_like(left)
    alphas = torch.where(valid_start, 0.5 * right, alphas)
    alphas = torch.where(valid_tail, 2.0 * left, alphas)
    alphas = torch.where(valid_finite, torch.sqrt(left * right), alphas)
    return alphas, valid


def _nearest_direction_cosines_batch_numpy(
    targets: np.ndarray,
    levels: np.ndarray,
    batch_size: int,
    dedup_rtol: float,
) -> np.ndarray:
    q_levels = np.concatenate([[0.0], levels])
    mids = 0.5 * (q_levels[:-1] + q_levels[1:])
    best_cosines = np.empty(targets.shape[0], dtype=np.float64)

    for start in range(0, targets.shape[0], batch_size):
        stop = min(start + batch_size, targets.shape[0])
        w = np.abs(targets[start:stop])
        ratios = (w[:, :, None] / mids[None, None, :]).reshape(w.shape[0], -1)
        ratios[~np.isfinite(ratios) | (ratios <= 0.0)] = np.inf
        sorted_breakpoints = np.sort(ratios, axis=1)
        alphas, valid_intervals = _interval_probes_numpy(sorted_breakpoints, dedup_rtol)

        scaled = np.full((w.shape[0], alphas.shape[1], w.shape[1]), np.inf, dtype=np.float64)
        np.divide(w[:, None, :], alphas[:, :, None], out=scaled, where=alphas[:, :, None] > 0.0)
        indices = np.searchsorted(mids, scaled, side="right")
        q_abs = q_levels[indices]
        q_norms = np.linalg.norm(q_abs, axis=2)
        dots = np.sum(w[:, None, :] * q_abs, axis=2)

        cosines = np.full_like(dots, -np.inf, dtype=np.float64)
        valid = valid_intervals & (q_norms > 0.0)
        np.divide(dots, q_norms, out=cosines, where=valid)
        batch_best = np.max(cosines, axis=1)
        if not np.all(np.isfinite(batch_best)):
            raise RuntimeError("Failed to find a nonzero codeword direction for one or more targets.")
        best_cosines[start:stop] = batch_best

    return np.clip(best_cosines, -1.0, 1.0)


def _nearest_direction_cosines_asymmetric_batch_numpy(
    targets: np.ndarray,
    positive_levels: np.ndarray,
    negative_levels: np.ndarray,
    batch_size: int,
    dedup_rtol: float,
) -> np.ndarray:
    positive_mid_count = positive_levels.size
    negative_mid_count = negative_levels.size
    max_mid_count = max(positive_mid_count, negative_mid_count)

    positive_mids, positive_q_levels = _pad_quantization_levels(positive_levels, max_mid_count)
    negative_mids, negative_q_levels = _pad_quantization_levels(negative_levels, max_mid_count)
    zero_mids = np.full(max_mid_count, np.inf, dtype=np.float64)
    zero_q_levels = np.zeros(max_mid_count + 1, dtype=np.float64)

    best_cosines = np.empty(targets.shape[0], dtype=np.float64)

    for start in range(0, targets.shape[0], batch_size):
        stop = min(start + batch_size, targets.shape[0])
        target_batch = np.asarray(targets[start:stop], dtype=np.float64)
        w = np.abs(target_batch)
        positive_mask = target_batch > 0.0
        negative_mask = target_batch < 0.0

        mids_table = np.broadcast_to(zero_mids, (w.shape[0], w.shape[1], max_mid_count)).copy()
        q_levels_table = np.broadcast_to(zero_q_levels, (w.shape[0], w.shape[1], max_mid_count + 1)).copy()
        mids_table[positive_mask] = positive_mids
        mids_table[negative_mask] = negative_mids
        q_levels_table[positive_mask] = positive_q_levels
        q_levels_table[negative_mask] = negative_q_levels

        ratios = np.full_like(mids_table, np.inf, dtype=np.float64)
        np.divide(
            w[:, :, None],
            mids_table,
            out=ratios,
            where=np.isfinite(mids_table) & (mids_table > 0.0),
        )
        ratios[~np.isfinite(ratios) | (ratios <= 0.0)] = np.inf
        sorted_breakpoints = np.sort(ratios.reshape(w.shape[0], -1), axis=1)
        alphas, valid_intervals = _interval_probes_numpy(sorted_breakpoints, dedup_rtol)

        scaled = np.full((w.shape[0], alphas.shape[1], w.shape[1]), np.inf, dtype=np.float64)
        np.divide(w[:, None, :], alphas[:, :, None], out=scaled, where=alphas[:, :, None] > 0.0)

        indices = np.zeros(scaled.shape, dtype=np.intp)
        for mid_index in range(max_mid_count):
            indices += scaled >= mids_table[:, None, :, mid_index]

        q_abs = np.take_along_axis(
            q_levels_table[:, None, :, :],
            indices[:, :, :, None],
            axis=3,
        ).squeeze(3)
        q_norms = np.linalg.norm(q_abs, axis=2)
        dots = np.sum(w[:, None, :] * q_abs, axis=2)

        cosines = np.full_like(dots, -np.inf, dtype=np.float64)
        valid = valid_intervals & (q_norms > 0.0)
        np.divide(dots, q_norms, out=cosines, where=valid)
        batch_best = np.max(cosines, axis=1)
        if not np.all(np.isfinite(batch_best)):
            raise RuntimeError("Failed to find a nonzero codeword direction for one or more targets.")
        best_cosines[start:stop] = batch_best

    return np.clip(best_cosines, -1.0, 1.0)


def _nearest_direction_cosines_batch_torch(
    targets: Any,
    levels: np.ndarray,
    backend: OracleBackend,
    batch_size: int,
    dedup_rtol: float,
) -> np.ndarray:
    torch = backend.torch
    q_levels = torch.as_tensor(
        np.concatenate([[0.0], levels]),
        dtype=torch.float64,
        device=backend.device,
    )
    mids = 0.5 * (q_levels[:-1] + q_levels[1:])
    best_cosines = np.empty(targets.shape[0], dtype=np.float64)

    for start in range(0, targets.shape[0], batch_size):
        stop = min(start + batch_size, targets.shape[0])
        w = torch.abs(targets[start:stop])
        ratios = (w.unsqueeze(-1) / mids.view(1, 1, -1)).reshape(w.shape[0], -1)
        infs = torch.full_like(ratios, float("inf"))
        ratios = torch.where(torch.isfinite(ratios) & (ratios > 0.0), ratios, infs)
        sorted_breakpoints, _ = torch.sort(ratios, dim=1)
        alphas, valid_intervals = _interval_probes_torch(sorted_breakpoints, dedup_rtol, backend)

        scaled = w.unsqueeze(1) / alphas.unsqueeze(-1)
        indices = torch.searchsorted(mids, scaled, right=True)
        q_abs = q_levels[indices]
        q_norms = torch.linalg.vector_norm(q_abs, dim=2)
        dots = torch.sum(w.unsqueeze(1) * q_abs, dim=2)

        denom = torch.where(q_norms > 0.0, q_norms, torch.ones_like(q_norms))
        cosines = dots / denom
        cosines = torch.where(valid_intervals & (q_norms > 0.0), cosines, torch.full_like(cosines, -torch.inf))
        batch_best = torch.max(cosines, dim=1).values
        if not bool(torch.all(torch.isfinite(batch_best)).item()):
            raise RuntimeError("Failed to find a nonzero codeword direction for one or more targets.")
        best_cosines[start:stop] = batch_best.detach().cpu().numpy()

    return np.clip(best_cosines, -1.0, 1.0)


def _nearest_direction_cosines_asymmetric_batch_torch(
    targets: Any,
    positive_levels: np.ndarray,
    negative_levels: np.ndarray,
    backend: OracleBackend,
    batch_size: int,
    dedup_rtol: float,
) -> np.ndarray:
    torch = backend.torch
    positive_mid_count = positive_levels.size
    negative_mid_count = negative_levels.size
    max_mid_count = max(positive_mid_count, negative_mid_count)

    positive_mids_np, positive_q_levels_np = _pad_quantization_levels(positive_levels, max_mid_count)
    negative_mids_np, negative_q_levels_np = _pad_quantization_levels(negative_levels, max_mid_count)
    positive_mids = torch.as_tensor(positive_mids_np, dtype=torch.float64, device=backend.device)
    negative_mids = torch.as_tensor(negative_mids_np, dtype=torch.float64, device=backend.device)
    positive_q_levels = torch.as_tensor(positive_q_levels_np, dtype=torch.float64, device=backend.device)
    negative_q_levels = torch.as_tensor(negative_q_levels_np, dtype=torch.float64, device=backend.device)
    zero_mids = torch.full((max_mid_count,), float("inf"), dtype=torch.float64, device=backend.device)
    zero_q_levels = torch.zeros((max_mid_count + 1,), dtype=torch.float64, device=backend.device)

    best_cosines = np.empty(targets.shape[0], dtype=np.float64)

    for start in range(0, targets.shape[0], batch_size):
        stop = min(start + batch_size, targets.shape[0])
        target_batch = targets[start:stop]
        w = torch.abs(target_batch)
        positive_mask = target_batch > 0.0
        negative_mask = target_batch < 0.0

        mids_table = zero_mids.view(1, 1, -1).expand(w.shape[0], w.shape[1], -1).clone()
        q_levels_table = zero_q_levels.view(1, 1, -1).expand(w.shape[0], w.shape[1], -1).clone()
        mids_table = torch.where(positive_mask.unsqueeze(-1), positive_mids.view(1, 1, -1), mids_table)
        mids_table = torch.where(negative_mask.unsqueeze(-1), negative_mids.view(1, 1, -1), mids_table)
        q_levels_table = torch.where(
            positive_mask.unsqueeze(-1),
            positive_q_levels.view(1, 1, -1),
            q_levels_table,
        )
        q_levels_table = torch.where(
            negative_mask.unsqueeze(-1),
            negative_q_levels.view(1, 1, -1),
            q_levels_table,
        )

        ratios = w.unsqueeze(-1) / mids_table
        infs = torch.full_like(ratios, float("inf"))
        ratios = torch.where(torch.isfinite(mids_table) & (mids_table > 0.0), ratios, infs)
        ratios = torch.where(torch.isfinite(ratios) & (ratios > 0.0), ratios, infs)
        sorted_breakpoints, _ = torch.sort(ratios.reshape(w.shape[0], -1), dim=1)
        alphas, valid_intervals = _interval_probes_torch(sorted_breakpoints, dedup_rtol, backend)

        scaled = w.unsqueeze(1) / alphas.unsqueeze(-1)
        indices = torch.zeros_like(scaled, dtype=torch.long)
        for mid_index in range(max_mid_count):
            indices = indices + (scaled >= mids_table[:, None, :, mid_index]).to(dtype=torch.long)

        q_abs = torch.gather(
            q_levels_table.unsqueeze(1).expand(-1, scaled.shape[1], -1, -1),
            dim=3,
            index=indices.unsqueeze(-1),
        ).squeeze(-1)
        q_norms = torch.linalg.vector_norm(q_abs, dim=2)
        dots = torch.sum(w.unsqueeze(1) * q_abs, dim=2)

        denom = torch.where(q_norms > 0.0, q_norms, torch.ones_like(q_norms))
        cosines = dots / denom
        cosines = torch.where(
            valid_intervals & (q_norms > 0.0),
            cosines,
            torch.full_like(cosines, float("-inf")),
        )
        batch_best = torch.max(cosines, dim=1).values
        if not bool(torch.all(torch.isfinite(batch_best)).item()):
            raise RuntimeError("Failed to find a nonzero codeword direction for one or more targets.")
        best_cosines[start:stop] = batch_best.detach().cpu().numpy()

    return np.clip(best_cosines, -1.0, 1.0)


def nearest_direction_cosines_batch(
    targets: np.ndarray | Any,
    levels: Sequence[float],
    *,
    negative_levels: Optional[Sequence[float]] = None,
    backend: Optional[OracleBackend] = None,
    batch_size: int = 2048,
    dedup_rtol: float = 1e-14,
    targets_prepared: bool = False,
) -> np.ndarray:
    backend = _coerce_backend(backend)
    if batch_size < 1:
        raise ValueError("batch_size must be at least 1.")

    positive_levels_np = _validate_positive_levels(
        levels,
        name="levels",
        allow_empty=negative_levels is not None,
    )
    negative_levels_np = positive_levels_np
    if negative_levels is not None:
        negative_levels_np = _validate_positive_levels(
            negative_levels,
            name="negative_levels",
            allow_empty=positive_levels_np.size > 0,
        )
    if positive_levels_np.size == 0 and negative_levels_np.size == 0:
        raise ValueError("At least one of levels or negative_levels must be non-empty.")

    prepared_targets = targets if targets_prepared else prepare_unit_vectors_for_backend(targets, backend)
    if prepared_targets.shape[0] == 0:
        return np.empty(0, dtype=np.float64)

    is_symmetric = (
        positive_levels_np.shape == negative_levels_np.shape
        and np.array_equal(positive_levels_np, negative_levels_np)
    )
    if backend.is_torch:
        if is_symmetric:
            return _nearest_direction_cosines_batch_torch(
                prepared_targets,
                positive_levels_np,
                backend=backend,
                batch_size=batch_size,
                dedup_rtol=dedup_rtol,
            )
        return _nearest_direction_cosines_asymmetric_batch_torch(
            prepared_targets,
            positive_levels_np,
            negative_levels_np,
            backend=backend,
            batch_size=batch_size,
            dedup_rtol=dedup_rtol,
        )
    prepared_targets_np = np.asarray(prepared_targets, dtype=np.float64)
    if is_symmetric:
        return _nearest_direction_cosines_batch_numpy(
            prepared_targets_np,
            positive_levels_np,
            batch_size=batch_size,
            dedup_rtol=dedup_rtol,
        )
    return _nearest_direction_cosines_asymmetric_batch_numpy(
        prepared_targets_np,
        positive_levels_np,
        negative_levels_np,
        batch_size=batch_size,
        dedup_rtol=dedup_rtol,
    )


def nearest_direction_angles_batch(
    targets: np.ndarray | Any,
    levels: Sequence[float],
    *,
    negative_levels: Optional[Sequence[float]] = None,
    backend: Optional[OracleBackend] = None,
    batch_size: int = 2048,
    dedup_rtol: float = 1e-14,
    targets_prepared: bool = False,
) -> np.ndarray:
    cosines = nearest_direction_cosines_batch(
        targets,
        levels,
        negative_levels=negative_levels,
        backend=backend,
        batch_size=batch_size,
        dedup_rtol=dedup_rtol,
        targets_prepared=targets_prepared,
    )
    return np.arccos(np.clip(cosines, -1.0, 1.0))
