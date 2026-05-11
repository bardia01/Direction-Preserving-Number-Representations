"""Command-line runner for worst-case angular-error experiments."""

from __future__ import annotations

import argparse
import json
import shlex
import sys
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path
from time import perf_counter

import numpy as np
import pandas as pd

from .datatypes import FORMATS, ScalarFormat, create_scalar_format_from_values, get_format
from .directional_coverage_optimizer import (
    DEFAULT_OPTIMIZER_INIT_MODE,
    OPTIMIZER_INIT_MODES,
    OptimizedScalarLevelsResult,
    optimise_scalar_levels,
)
from .metrics import (
    MetricConfig,
    compute_scaled_scalar_quantization_only_metrics,
    resolve_metric_backend,
)
from .utils import degrees


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OPTIMIZER_TARGETS_PER_STAGE = (384, 1536)
OPTIMIZED_CODE_DETAILS_DIR = Path("results/optimized_code")
WORST_CASE_ANGULAR_ERROR_SEED_METRIC_COLUMN = "max_worst_case_angular_error_deg"
RADIAN_TO_DEGREE_COLUMN_MAP = {
    "mean_worst_case_angular_error_rad": "mean_worst_case_angular_error_deg",
    "median_worst_case_angular_error_rad": "median_worst_case_angular_error_deg",
    "p95_worst_case_angular_error_rad": "p95_worst_case_angular_error_deg",
    "p99_worst_case_angular_error_rad": "p99_worst_case_angular_error_deg",
    "max_worst_case_angular_error_rad": "max_worst_case_angular_error_deg",
}


def build_optimized_code_details_path(
    stage_1_number_of_targets: int,
    stage_2_number_of_targets: int,
) -> Path:
    """Legacy helper kept for callers that still import it.

    The runner now writes optimized code details inside the selected output
    directory instead of using this global path.
    """
    return (
        OPTIMIZED_CODE_DETAILS_DIR
        / f"optimized_code_details_s1_{stage_1_number_of_targets}_s2_{stage_2_number_of_targets}.csv"
    )


OPTIMIZED_CODE_DETAILS_PATH = build_optimized_code_details_path(*DEFAULT_OPTIMIZER_TARGETS_PER_STAGE)


@dataclass
class OptimizedDatatypeArtifact:
    scalar_format: ScalarFormat
    full_alphabet: np.ndarray
    positive_levels: np.ndarray
    optimisation_result: object | None = None


@dataclass
class DatatypeRunResult:
    row: dict[str, float | str | int]
    optimized_code_detail: dict[str, object] | None = None


# Cache for optimized datatypes to avoid recomputation.
# Key: (
#   bitwidth,
#   dimension,
#   seed,
#   optimizer_device,
#   optimizer_batch_size,
#   optimizer_targets_stage1,
#   optimizer_targets_stage2,
#   optimizer_initialization_mode,
#   optimizer_de_iter,
#   optimizer_pm_iter,
# )
_OPTIMIZED_FORMAT_CACHE: dict[tuple[object, ...], OptimizedDatatypeArtifact] = {}


def _parse_optimized_datatype_name(name: str) -> tuple[bool, int]:
    """Parse an optimized_X datatype name."""
    prefix = "optimized_"
    if name.startswith(prefix):
        try:
            return True, int(name[len(prefix) :])
        except ValueError:
            pass
    return False, 0


def _extract_positive_levels(full_alphabet: np.ndarray) -> np.ndarray:
    full_alphabet = np.asarray(full_alphabet, dtype=np.float64)
    if full_alphabet.ndim != 1 or full_alphabet.size < 3 or full_alphabet.size % 2 == 0:
        raise ValueError("Optimized full alphabet must be a 1D array with odd length at least 3.")

    midpoint = full_alphabet.size // 2
    if not np.isclose(full_alphabet[midpoint], 0.0):
        raise ValueError("Optimized full alphabet must contain 0.0 at the midpoint.")

    positive_levels = full_alphabet[midpoint + 1 :]
    if positive_levels.size == 0 or not np.all(np.diff(positive_levels) > 0.0):
        raise ValueError("Optimized positive levels must be strictly increasing.")
    if not np.all(positive_levels > 0.0):
        raise ValueError("Optimized positive levels must be strictly positive.")
    return positive_levels


def _json_list(values: np.ndarray) -> str:
    return json.dumps([float(value) for value in np.asarray(values, dtype=np.float64).tolist()])


def _build_basic_optimized_code_detail_row(
    datatype_name: str,
    dimension: int,
    seed: int,
    artifact: OptimizedDatatypeArtifact,
) -> dict[str, object]:
    return {
        "datatype": datatype_name,
        "dimension": dimension,
        "bitwidth_per_element": artifact.scalar_format.bitwidth,
        "seed": seed,
        "optimized_code": _json_list(artifact.positive_levels),
        "ordered_scalars": _json_list(artifact.full_alphabet),
    }


def _get_or_create_optimized_artifact(
    bitwidth: int,
    dimension: int,
    seed: int,
    optimizer_device: str = "auto",
    optimizer_batch_size: int = 2048,
    optimizer_targets_stage1: int = DEFAULT_OPTIMIZER_TARGETS_PER_STAGE[0],
    optimizer_targets_stage2: int = DEFAULT_OPTIMIZER_TARGETS_PER_STAGE[1],
    optimizer_initialization_mode: str = DEFAULT_OPTIMIZER_INIT_MODE,
    include_details: bool = False,
    verbose: bool = False,
    de_iter: int = 40,
    pm_iter: int = 80,
) -> OptimizedDatatypeArtifact:
    """Get or create an optimized datatype artifact from cache."""
    if bitwidth != 4:
        raise NotImplementedError("Only optimized_4 datatypes are supported.")
    if optimizer_targets_stage1 < 1 or optimizer_targets_stage2 < 1:
        raise ValueError("Optimizer targets per stage must both be at least 1.")

    cache_key = (
        bitwidth,
        dimension,
        seed,
        optimizer_device,
        optimizer_batch_size,
        optimizer_targets_stage1,
        optimizer_targets_stage2,
        optimizer_initialization_mode,
        de_iter,
        pm_iter,
    )
    cached = _OPTIMIZED_FORMAT_CACHE.get(cache_key)
    if cached is not None and (not include_details or cached.optimisation_result is not None):
        return cached

    optimisation_output = optimise_scalar_levels(
        bitwidth=bitwidth,
        dimension=dimension,
        num_targets_stage1=optimizer_targets_stage1,
        num_targets_stage2=optimizer_targets_stage2,
        seed=seed,
        verbose=verbose,
        device=optimizer_device,
        batch_size=optimizer_batch_size,
        return_details=include_details,
        de_iter=de_iter,
        pm_iter=pm_iter,
        initialization_mode=optimizer_initialization_mode,
    )

    if isinstance(optimisation_output, OptimizedScalarLevelsResult):
        full_alphabet = np.asarray(optimisation_output.full_alphabet, dtype=np.float64)
        positive_levels = np.asarray(optimisation_output.positive_levels, dtype=np.float64)
        optimisation_result = optimisation_output.optimisation_result
    else:
        full_alphabet = np.asarray(optimisation_output, dtype=np.float64)
        positive_levels = _extract_positive_levels(full_alphabet)
        optimisation_result = None

    fmt = create_scalar_format_from_values(
        name=f"optimized_{bitwidth}",
        ordered_scalar_values=full_alphabet,
        description=f"Optimized {bitwidth}-bit scalar alphabet for dimension {dimension}",
    )
    artifact = OptimizedDatatypeArtifact(
        scalar_format=fmt,
        full_alphabet=full_alphabet,
        positive_levels=positive_levels,
        optimisation_result=optimisation_result,
    )
    _OPTIMIZED_FORMAT_CACHE[cache_key] = artifact
    return artifact


def resolve_output_dir(output_dir: Path) -> Path:
    return output_dir if output_dir.is_absolute() else REPO_ROOT / output_dir


def build_output_bundle_paths(output_dir: Path) -> tuple[Path, Path]:
    name = output_dir.name
    if not name:
        raise ValueError("Output directory must have a final path component to use as the run name.")
    return (
        output_dir / f"{name}_results.csv",
        output_dir / f"{name}_command.txt",
    )


def _json_safe_arg_value(value: object) -> object:
    if isinstance(value, Path):
        return str(value)
    if isinstance(value, tuple):
        return [_json_safe_arg_value(item) for item in value]
    if isinstance(value, list):
        return [_json_safe_arg_value(item) for item in value]
    return value


def build_rerun_command(cli_args: list[str]) -> str:
    command_parts = [sys.executable, "-m", "src.runner", *cli_args]
    return " ".join(shlex.quote(part) for part in command_parts)


def write_command_file(command_path: Path, args: argparse.Namespace, cli_args: list[str]) -> None:
    serialized_args = {
        key: _json_safe_arg_value(value)
        for key, value in vars(args).items()
    }
    cli_args_line = " ".join(shlex.quote(arg) for arg in cli_args) if cli_args else "(none)"
    content = "\n".join(
        [
            f"Repository root: {REPO_ROOT}",
            "",
            "CLI args:",
            cli_args_line,
            "",
            "Re-run command:",
            f"cd {shlex.quote(str(REPO_ROOT))}",
            build_rerun_command(cli_args),
            "",
            "Parsed args:",
            json.dumps(serialized_args, indent=2, sort_keys=True),
            "",
        ]
    )
    command_path.parent.mkdir(parents=True, exist_ok=True)
    command_path.write_text(content, encoding="utf-8")


def _resolve_requested_seeds(args: argparse.Namespace) -> list[int]:
    seeds = getattr(args, "seeds", None)
    if seeds is not None:
        return [int(seed) for seed in seeds]
    num_seeds = getattr(args, "num_seeds", None)
    starting_seed = int(getattr(args, "seed", 0))
    if num_seeds is not None:
        return list(range(starting_seed, starting_seed + int(num_seeds)))
    return [starting_seed]


def _copy_args_with_seed(args: argparse.Namespace, seed: int) -> argparse.Namespace:
    copied_args = argparse.Namespace(**vars(args))
    copied_args.seed = int(seed)
    return copied_args


def _has_larger_seed_error(
    candidate: DatatypeRunResult,
    incumbent: DatatypeRunResult,
    metric_column: str = WORST_CASE_ANGULAR_ERROR_SEED_METRIC_COLUMN,
) -> bool:
    candidate_metric = candidate.row.get(metric_column)
    incumbent_metric = incumbent.row.get(metric_column)
    if candidate_metric is None or incumbent_metric is None:
        raise ValueError(
            f"Multi-seed selection requires '{metric_column}' in every result row."
        )

    candidate_metric = float(candidate_metric)
    incumbent_metric = float(incumbent_metric)
    if not np.isnan(candidate_metric) and np.isnan(incumbent_metric):
        return True
    if np.isnan(candidate_metric):
        return False
    if candidate_metric > incumbent_metric:
        return True
    if candidate_metric < incumbent_metric:
        return False
    return int(candidate.row["seed"]) < int(incumbent.row["seed"])


def _select_largest_seed_error_results(run_results: list[DatatypeRunResult]) -> list[DatatypeRunResult]:
    if len(run_results) <= 1:
        return run_results

    largest_error_results_by_job: dict[tuple[str, int], DatatypeRunResult] = {}
    for result in run_results:
        key = (str(result.row["datatype"]), int(result.row["dimension"]))
        incumbent = largest_error_results_by_job.get(key)
        if incumbent is None or _has_larger_seed_error(result, incumbent):
            largest_error_results_by_job[key] = result
    return list(largest_error_results_by_job.values())


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Evaluate worst-case angular error for number formats."
    )
    parser.add_argument(
        "--dimensions",
        "--dimension",
        dest="dimensions",
        type=int,
        nargs="+",
        required=True,
        help="One or more vector dimensions n to evaluate, for example: --dimension 4 8 16",
    )
    datatype_group = parser.add_mutually_exclusive_group(required=True)
    datatype_group.add_argument(
        "--datatypes",
        nargs="+",
        help=(
            "Datatypes to evaluate. Include standard names (e.g., int4, fp4_e2m1) "
            "or optimized_4 for optimized scalar alphabets."
        ),
    )
    datatype_group.add_argument(
        "--all",
        action="store_true",
        help="Evaluate all supported datatypes for each requested dimension.",
    )
    parser.add_argument(
        "--query-vectors",
        type=int,
        default=20_000,
        help="Number of random sphere queries for worst-case angular-error estimates.",
    )
    parser.add_argument(
        "--query-chunk-size",
        type=int,
        default=4096,
        help="Target query batch size for worst-case angular-error estimates.",
    )
    parser.add_argument("--seed", type=int, default=0, help="Random seed, or starting seed when using --num-seeds.")
    parser.add_argument(
        "--seeds",
        type=int,
        nargs="+",
        help=(
            "One or more explicit random seeds to evaluate in the same runner invocation. "
            "The output keeps the seed with the largest max_worst_case_angular_error_deg."
        ),
    )
    parser.add_argument(
        "--num-seeds",
        type=int,
        help=(
            "Number of consecutive seeds to evaluate, starting from --seed. "
            "The output keeps the seed with the largest max_worst_case_angular_error_deg."
        ),
    )
    parser.add_argument(
        "--metric-device",
        type=str,
        default="auto",
        help="Metric execution device: auto, cpu, cuda, or cuda:N. CUDA requires PyTorch.",
    )
    parser.add_argument(
        "--parallel-workers",
        type=int,
        default=1,
        help="Number of parallel (datatype, dimension) jobs to run. Use 1 for serial execution.",
    )
    parser.add_argument(
        "--optimizer-device",
        type=str,
        default="auto",
        help="Device for optimized datatype search: auto, cpu, numpy, cuda, or cuda:N.",
    )
    parser.add_argument(
        "--optimizer-batch-size",
        type=int,
        default=2048,
        help="Batch size for optimized datatype oracle evaluations.",
    )
    parser.add_argument(
        "--optimizer-targets-per-stage",
        type=int,
        nargs=2,
        metavar=("STAGE1", "STAGE2"),
        default=list(DEFAULT_OPTIMIZER_TARGETS_PER_STAGE),
        help=(
            "Number of random target directions used for optimized datatype search "
            "in stage 1 and stage 2."
        ),
    )
    parser.add_argument(
        "--optimizer-init-mode",
        choices=OPTIMIZER_INIT_MODES,
        default=DEFAULT_OPTIMIZER_INIT_MODE,
        help="Seed initialisation mode for optimized datatype search.",
    )
    parser.add_argument(
        "--optimizer-de-iter",
        type=int,
        default=40,
        help="Maximum differential-evolution generations for optimized datatype search stage 1.",
    )
    parser.add_argument(
        "--optimizer-pm-iter",
        type=int,
        default=80,
        help="Maximum Powell iterations for optimized datatype search stage 2 polishing.",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        required=True,
        help=(
            "Directory for this run's output bundle. The final path component is used "
            "as the run name for <name>_results.csv and <name>_command.txt."
        ),
    )
    parser.add_argument("--standard-form-output", type=bool, default=True, help=argparse.SUPPRESS)

    args = parser.parse_args(argv)

    if args.all:
        args.datatypes = list(FORMATS.keys())

    if any(dimension < 1 for dimension in args.dimensions):
        raise ValueError("All dimensions must be at least 1.")
    if args.query_vectors < 0:
        raise ValueError("--query-vectors must be non-negative.")
    if args.query_chunk_size < 1:
        raise ValueError("--query-chunk-size must be at least 1.")
    if args.seeds is not None and args.num_seeds is not None:
        raise ValueError("Pass at most one of --seeds and --num-seeds.")
    if args.num_seeds is not None and args.num_seeds < 1:
        raise ValueError("--num-seeds must be at least 1.")
    args.seeds = _resolve_requested_seeds(args)
    args.seed = args.seeds[0]

    optimizer_targets_stage1, optimizer_targets_stage2 = args.optimizer_targets_per_stage
    if optimizer_targets_stage1 < 1 or optimizer_targets_stage2 < 1:
        raise ValueError("--optimizer-targets-per-stage values must both be at least 1.")
    args.optimizer_targets_per_stage = (optimizer_targets_stage1, optimizer_targets_stage2)
    if args.optimizer_de_iter < 0:
        raise ValueError("--optimizer-de-iter must be at least 0.")
    if args.optimizer_pm_iter < 0:
        raise ValueError("--optimizer-pm-iter must be at least 0.")

    for datatype_name in args.datatypes:
        is_optimized, bitwidth = _parse_optimized_datatype_name(datatype_name)
        if is_optimized:
            if bitwidth != 4:
                raise ValueError("Only optimized_4 datatypes are supported.")
            continue
        if datatype_name not in FORMATS:
            supported = ", ".join(sorted(FORMATS.keys()))
            raise ValueError(
                f"Unknown datatype '{datatype_name}'. "
                f"Supported standard datatypes: {supported}. "
                "Or use optimized_4 for optimized scalar alphabets."
            )

    return args


def _add_available_degree_columns(row: dict[str, float | str | int]) -> None:
    for rad_key, deg_key in RADIAN_TO_DEGREE_COLUMN_MAP.items():
        if rad_key not in row:
            continue
        rad_value = row[rad_key]
        row[deg_key] = degrees(float(rad_value)) if np.isfinite(rad_value) else np.nan


def _build_worst_case_angular_error_row(
    datatype_name: str,
    dimension: int,
    fmt: ScalarFormat,
    metric_config: MetricConfig,
) -> dict[str, float | str | int]:
    row: dict[str, float | str | int] = {
        "datatype": datatype_name,
        "dimension": dimension,
        "seed": metric_config.seed,
        "bitwidth_per_element": fmt.bitwidth,
    }
    row.update(
        compute_scaled_scalar_quantization_only_metrics(
            dimension=dimension,
            config=metric_config,
            scalar_format=fmt,
        )
    )
    _add_available_degree_columns(row)
    return row


def _run_one_datatype(
    args: argparse.Namespace,
    datatype_name: str,
    dimension: int,
    include_optimized_details: bool = False,
) -> DatatypeRunResult:
    started_at = perf_counter()
    is_optimized, bitwidth = _parse_optimized_datatype_name(datatype_name)
    optimized_detail_row = None

    if is_optimized:
        optimizer_targets_stage1, optimizer_targets_stage2 = getattr(
            args,
            "optimizer_targets_per_stage",
            DEFAULT_OPTIMIZER_TARGETS_PER_STAGE,
        )
        optimized_artifact = _get_or_create_optimized_artifact(
            bitwidth=bitwidth,
            dimension=dimension,
            seed=args.seed,
            optimizer_device=getattr(args, "optimizer_device", "auto"),
            optimizer_batch_size=int(getattr(args, "optimizer_batch_size", 2048)),
            optimizer_targets_stage1=int(optimizer_targets_stage1),
            optimizer_targets_stage2=int(optimizer_targets_stage2),
            optimizer_initialization_mode=str(
                getattr(args, "optimizer_init_mode", DEFAULT_OPTIMIZER_INIT_MODE)
            ),
            include_details=False,
            verbose=False,
            de_iter=int(getattr(args, "optimizer_de_iter", 40)),
            pm_iter=int(getattr(args, "optimizer_pm_iter", 80)),
        )
        fmt = optimized_artifact.scalar_format
        if include_optimized_details:
            optimized_detail_row = _build_basic_optimized_code_detail_row(
                datatype_name=datatype_name,
                dimension=dimension,
                seed=args.seed,
                artifact=optimized_artifact,
            )
    else:
        fmt = get_format(datatype_name)

    metric_config = MetricConfig(
        query_chunk_size=args.query_chunk_size,
        query_vectors=args.query_vectors,
        seed=args.seed,
        metric_device=args.metric_device,
    )
    row = _build_worst_case_angular_error_row(
        datatype_name=datatype_name,
        dimension=dimension,
        fmt=fmt,
        metric_config=metric_config,
    )
    row["wall_time_seconds"] = float(perf_counter() - started_at)
    return DatatypeRunResult(row=row, optimized_code_detail=optimized_detail_row)


def run_one_datatype(args: argparse.Namespace, datatype_name: str, dimension: int) -> dict[str, float | str | int]:
    return _run_one_datatype(args, datatype_name, dimension, include_optimized_details=False).row


def _run_job(job: tuple[argparse.Namespace, str, int, bool]) -> DatatypeRunResult:
    args, datatype_name, dimension, include_optimized_details = job
    return _run_one_datatype(args, datatype_name, dimension, include_optimized_details=include_optimized_details)


def collect_run_results(
    args: argparse.Namespace,
    include_optimized_details: bool = False,
) -> list[DatatypeRunResult]:
    if args.parallel_workers < 1:
        raise ValueError("--parallel-workers must be at least 1.")

    requested_seeds = _resolve_requested_seeds(args)
    jobs = [
        (_copy_args_with_seed(args, seed), name, dimension, include_optimized_details)
        for dimension in args.dimensions
        for name in args.datatypes
        for seed in requested_seeds
    ]
    if args.parallel_workers == 1 or len(jobs) <= 1:
        run_results = [
            _run_one_datatype(job_args, name, dimension, include_optimized_details=include_optimized_details)
            for job_args, name, dimension, _ in jobs
        ]
        return _select_largest_seed_error_results(run_results) if len(requested_seeds) > 1 else run_results

    backend = resolve_metric_backend(args.metric_device)
    if backend.is_torch:
        raise ValueError(
            "Parallel workers > 1 are only supported with CPU metrics. "
            "Use --parallel-workers 1 when running metrics on CUDA."
        )

    max_workers = min(args.parallel_workers, len(jobs))
    try:
        with ProcessPoolExecutor(max_workers=max_workers) as executor:
            run_results = list(executor.map(_run_job, jobs, chunksize=1))
    except (OSError, PermissionError, NotImplementedError):
        print("Process-based parallelism unavailable; falling back to thread-based parallelism.")
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            run_results = list(executor.map(_run_job, jobs))
    return _select_largest_seed_error_results(run_results) if len(requested_seeds) > 1 else run_results


def collect_rows(args: argparse.Namespace) -> list[dict[str, float | str | int]]:
    return [result.row for result in collect_run_results(args, include_optimized_details=False)]


def save_optimized_code_details(
    detail_rows: list[dict[str, object]],
    path: Path = OPTIMIZED_CODE_DETAILS_PATH,
) -> None:
    if not detail_rows:
        return

    df = pd.DataFrame(detail_rows)
    df = df.where(pd.notna(df), "NaN")
    path.parent.mkdir(parents=True, exist_ok=True)
    df.to_csv(path, index=False)


def should_include_optimized_code_details(datatypes: list[str]) -> bool:
    return any(_parse_optimized_datatype_name(datatype_name) == (True, 4) for datatype_name in datatypes)


def main(argv: list[str] | None = None) -> None:
    total_started_at = perf_counter()
    cli_args = list(sys.argv[1:] if argv is None else argv)
    args = parse_args(cli_args)
    output_dir = resolve_output_dir(args.output_dir)
    results_path, command_path = build_output_bundle_paths(output_dir)
    include_optimized_details = should_include_optimized_code_details(args.datatypes)
    optimized_code_details_path = (
        output_dir / f"{output_dir.name}_optimized_code_details.csv"
        if include_optimized_details
        else None
    )

    backend = resolve_metric_backend(args.metric_device)
    print(f"Metric backend: {backend.name} ({backend.device})")
    if args.parallel_workers > 1:
        print(f"Parallel workers: {args.parallel_workers}")

    run_results = collect_run_results(args, include_optimized_details=include_optimized_details)
    rows = [result.row for result in run_results]
    optimized_detail_rows = [
        result.optimized_code_detail
        for result in run_results
        if result.optimized_code_detail is not None
    ]
    df = pd.DataFrame(rows)
    df = df.where(pd.notna(df), "NaN")

    output_dir.mkdir(parents=True, exist_ok=True)
    df.to_csv(results_path, index=False)
    if optimized_code_details_path is not None:
        save_optimized_code_details(optimized_detail_rows, path=optimized_code_details_path)
    write_command_file(command_path=command_path, args=args, cli_args=cli_args)

    print(df.to_string(index=False))
    print(f"\nSaved results to: {results_path}")
    if optimized_detail_rows and optimized_code_details_path is not None:
        print(f"Saved optimized code details to: {optimized_code_details_path}")
    print(f"Saved re-run command to: {command_path}")
    print(f"Total wall time: {perf_counter() - total_started_at:.6f} seconds")


if __name__ == "__main__":
    main()
