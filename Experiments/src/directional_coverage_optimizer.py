from __future__ import annotations

import math
import time
from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np
from scipy.optimize import differential_evolution, minimize

try:
    from .oracle_batch import (
        OracleBackend,
        nearest_direction_angles_batch,
        prepare_unit_vectors_for_backend,
        resolve_oracle_backend,
    )
except ImportError:
    from number_format_sphere_project.experiments.src.oracle_batch import (  # type: ignore
        OracleBackend,
        nearest_direction_angles_batch,
        prepare_unit_vectors_for_backend,
        resolve_oracle_backend,
    )


# ============================================================
# Problem setup
#   - choose NUM_POS_LEVELS positive levels S = {s1 < ... < s_m}
#   - signed scalar alphabet is B = {0} U S U (-S)
#   - vectors live in B^DIM
#   - objective: approximately minimise spherical covering radius
#     of the induced direction set
#
# Here NUM_POS_LEVELS = 7, so the scalar alphabet has
#   1 + 2 * 7 = 15 levels,
# which fits naturally in 4 bits.
#
# Notes
# -----
# 1. Global scaling of S does not change the direction set, so we fix s1 = 1.
# 2. We do NOT enforce the Golomb condition. Instead, we use Golomb-like seeds
#    and report a Golomb diagnostic for the final result.
# 3. The inner nearest-direction oracle is exact except for measure-zero tie
#    cases at quantisation breakpoints, which are irrelevant in random sampling.
# ============================================================

NUM_POS_LEVELS = 7
NUM_GAPS = NUM_POS_LEVELS - 1
THETA_DIM = NUM_GAPS  # (NUM_GAPS - 1) gap logits + 1 log-span
DIM = 16
DEFAULT_OPTIMIZER_INIT_MODE = "default"
CUSTOM_OPTIMIZER_INIT_MODE = "custom"
OPTIMIZER_INIT_MODES = (DEFAULT_OPTIMIZER_INIT_MODE, CUSTOM_OPTIMIZER_INIT_MODE)
CUSTOM_INITIAL_POSITIVE_LEVELS = np.array([1, 2, 3, 122/25, 6, 17/2, 12], dtype=float)


# -----------------------------
# Utilities
# -----------------------------

def softmax(x: np.ndarray) -> np.ndarray:
    x = np.asarray(x, dtype=float)
    x = x - np.max(x)
    ex = np.exp(x)
    return ex / np.sum(ex)


def unit_sphere_samples(num_samples: int, dim: int, rng: np.random.Generator) -> np.ndarray:
    """Draw random points uniformly from S^{dim-1}."""
    x = rng.normal(size=(num_samples, dim))
    x /= np.linalg.norm(x, axis=1, keepdims=True)
    return x


# -----------------------------
# Golomb diagnostics in log-space
# -----------------------------

def golomb_differences(a: Sequence[float]) -> np.ndarray:
    a = np.asarray(a, dtype=float)
    diffs = []
    for i in range(len(a)):
        for j in range(i + 1, len(a)):
            diffs.append(a[j] - a[i])
    return np.array(diffs, dtype=float)


def golomb_margin(a: Sequence[float]) -> float:
    """Minimum separation between distinct positive differences."""
    diffs = np.sort(golomb_differences(a))
    if len(diffs) < 2:
        return math.inf
    return float(np.min(np.diff(diffs)))


def is_golomb(a: Sequence[float], tol: float = 1e-10) -> bool:
    return golomb_margin(a) > tol


# -----------------------------
# Parametrisation of S
# -----------------------------
# We use THETA_DIM optimisation parameters:
#   theta[0 : NUM_GAPS - 1] -> free logits for NUM_GAPS positive gaps,
#                              with one extra fixed logit 0
#   theta[-1]               -> total log-span L = exp(theta[-1])
# Then
#   a1 = 0,
#   a_{j+1} - a_j = L * p_j,
#   s_j = exp(a_j).
# This fixes s1 = 1 and leaves the overall log-span free.
# -----------------------------

def theta_to_log_levels(theta: Sequence[float]) -> np.ndarray:
    theta = np.asarray(theta, dtype=float)
    if theta.shape != (THETA_DIM,):
        raise ValueError(f"theta must have shape ({THETA_DIM},)")

    gap_logits = np.concatenate([theta[:-1], np.array([0.0])])
    p = softmax(gap_logits)
    span = math.exp(theta[-1])
    gaps = span * p

    a = np.zeros(NUM_POS_LEVELS, dtype=float)
    a[1:] = np.cumsum(gaps)
    return a


def theta_to_levels(theta: Sequence[float]) -> np.ndarray:
    a = theta_to_log_levels(theta)
    return np.exp(a)


def log_levels_to_seed_theta(log_levels: Sequence[float]) -> np.ndarray:
    """Convert strictly increasing log-levels with a[0] fixed to 0 into seed theta."""
    a = np.asarray(log_levels, dtype=float)
    if a.shape != (NUM_POS_LEVELS,):
        raise ValueError(f"log_levels must have shape ({NUM_POS_LEVELS},)")
    if not np.all(np.isfinite(a)):
        raise ValueError("log_levels must be finite")
    if not np.all(np.diff(a) > 0):
        raise ValueError("log_levels must be strictly increasing")
    if not np.isclose(a[0], 0.0, atol=1e-12, rtol=0.0):
        raise ValueError("log_levels must start at 0.0 because the parametrisation fixes s1 = 1")

    gaps = np.diff(a)
    total_span = float(np.sum(gaps))
    p = gaps / total_span

    logits = np.log(p[:-1]) - np.log(p[-1])
    theta = np.zeros(THETA_DIM, dtype=float)
    theta[:-1] = logits
    theta[-1] = math.log(total_span)
    return theta


def positive_levels_to_seed_theta(levels: Sequence[float]) -> np.ndarray:
    """Convert positive levels into an exact seed theta when the first level is 1."""
    levels = np.asarray(levels, dtype=float)
    if levels.shape != (NUM_POS_LEVELS,):
        raise ValueError(f"levels must have shape ({NUM_POS_LEVELS},)")
    if not np.all(np.isfinite(levels)):
        raise ValueError("levels must be finite")
    if not np.all(levels > 0):
        raise ValueError("levels must be strictly positive")
    if not np.all(np.diff(levels) > 0):
        raise ValueError("levels must be strictly increasing")
    if not np.isclose(levels[0], 1.0, atol=1e-12, rtol=0.0):
        raise ValueError("levels must start at 1.0 because the parametrisation fixes s1 = 1")

    return log_levels_to_seed_theta(np.log(levels))


def pattern_to_seed_theta(pattern: Sequence[float], total_span: float) -> np.ndarray:
    """
    Convert an increasing pattern with first entry 0 into a seed theta.
    The pattern is first normalised to [0, 1], then stretched to total_span.
    """
    pattern = np.asarray(pattern, dtype=float)
    if len(pattern) != NUM_POS_LEVELS:
        raise ValueError(f"pattern must have length {NUM_POS_LEVELS}")
    if not np.all(np.diff(pattern) > 0):
        raise ValueError("pattern must be strictly increasing")
    pattern = pattern - pattern[0]
    pattern = pattern / pattern[-1]
    a = total_span * pattern
    return log_levels_to_seed_theta(a)


# -----------------------------
# Data containers
# -----------------------------
@dataclass
class CoverageResult:
    levels: np.ndarray
    log_levels: np.ndarray
    worst_angle: float
    mean_angle: float
    q95_angle: float
    q99_angle: float
    golomb_margin: float
    is_golomb: bool


@dataclass
class OptimisationResult:
    theta: np.ndarray
    levels: np.ndarray
    log_levels: np.ndarray
    objective_value: float
    local_objective_value: Optional[float]
    stats: CoverageResult


@dataclass
class OptimizedScalarLevelsResult:
    bitwidth: int
    dimension: int
    positive_levels: np.ndarray
    full_alphabet: np.ndarray
    optimisation_result: OptimisationResult


# -----------------------------
# Coverage evaluation
# -----------------------------

def coverage_angles(
    levels: Sequence[float],
    targets: np.ndarray | Any,
    backend: Optional[OracleBackend] = None,
    batch_size: int = 2048,
    targets_prepared: bool = False,
) -> np.ndarray:
    levels = np.asarray(levels, dtype=float)
    return nearest_direction_angles_batch(
        targets,
        levels,
        backend=backend,
        batch_size=batch_size,
        targets_prepared=targets_prepared,
    )


def coverage_statistics(
    levels: Sequence[float],
    targets: np.ndarray | Any,
    backend: Optional[OracleBackend] = None,
    batch_size: int = 2048,
    targets_prepared: bool = False,
) -> CoverageResult:
    levels = np.asarray(levels, dtype=float)
    angles = coverage_angles(
        levels,
        targets,
        backend=backend,
        batch_size=batch_size,
        targets_prepared=targets_prepared,
    )
    a = np.log(levels)
    return CoverageResult(
        levels=levels,
        log_levels=a,
        worst_angle=float(np.max(angles)),
        mean_angle=float(np.mean(angles)),
        q95_angle=float(np.quantile(angles, 0.95)),
        q99_angle=float(np.quantile(angles, 0.99)),
        golomb_margin=golomb_margin(a),
        is_golomb=is_golomb(a),
    )


class ProgressLogger:
    def __init__(
        self,
        label: str,
        verbose: bool = True,
        print_every_evals: int = 25,
    ) -> None:
        self.label = label
        self.verbose = verbose
        self.print_every_evals = print_every_evals
        self.start_time = time.time()
        self.eval_count = 0
        self.best_value = math.inf
        self.best_theta: Optional[np.ndarray] = None

    def _elapsed(self) -> float:
        return time.time() - self.start_time

    def log(self, message: str) -> None:
        if self.verbose:
            print(f"[{self.label:>8}] {message}")

    def note_value(self, theta: Sequence[float], value: float, force: bool = False) -> None:
        self.eval_count += 1
        improved = value < self.best_value
        if improved:
            self.best_value = float(value)
            self.best_theta = np.asarray(theta, dtype=float).copy()
        if self.verbose and (force or improved or self.eval_count % self.print_every_evals == 0):
            tag = "improved" if improved else "status"
            self.log(
                f"eval={self.eval_count:5d}  best={self.best_value:.8f}  current={value:.8f}  "
                f"elapsed={self._elapsed():.1f}s  ({tag})"
            )


# -----------------------------
# Optimisation objective
# -----------------------------

def objective_from_angles(angles: np.ndarray, mean_weight: float = 0.15, q99_weight: float = 0.35) -> float:
    """A smoother surrogate than pure worst-case angle. Lower is better."""
    worst = float(np.max(angles))
    mean = float(np.mean(angles))
    q99 = float(np.quantile(angles, 0.99))
    return worst + mean_weight * mean + q99_weight * q99


class CoverageObjective:
    def __init__(
        self,
        dim: int = DIM,
        num_targets: int = 512,
        seed: int = 0,
        mean_weight: float = 0.15,
        q99_weight: float = 0.35,
        duplicate_penalty_weight: float = 0.0,
        duplicate_margin_target: float = 1e-3,
        device: str = "auto",
        batch_size: int = 2048,
    ) -> None:
        self.dim = dim
        self.num_targets = num_targets
        self.rng = np.random.default_rng(seed)
        self.targets = unit_sphere_samples(num_targets, dim, self.rng)
        self.backend = resolve_oracle_backend(device)
        self.batch_size = batch_size
        self.prepared_targets = prepare_unit_vectors_for_backend(self.targets, self.backend)
        self.mean_weight = mean_weight
        self.q99_weight = q99_weight
        self.duplicate_penalty_weight = duplicate_penalty_weight
        self.duplicate_margin_target = duplicate_margin_target
        self.cache: Dict[Tuple[float, ...], float] = {}

    def evaluate_levels(self, levels: Sequence[float]) -> float:
        levels_key = tuple(np.round(np.asarray(levels, dtype=float), 14))
        if levels_key in self.cache:
            return self.cache[levels_key]

        angles = nearest_direction_angles_batch(
            self.prepared_targets,
            levels_key,
            backend=self.backend,
            batch_size=self.batch_size,
            targets_prepared=True,
        )
        obj = objective_from_angles(angles, mean_weight=self.mean_weight, q99_weight=self.q99_weight)

        if self.duplicate_penalty_weight > 0.0:
            a = np.log(np.asarray(levels_key, dtype=float))
            margin = golomb_margin(a)
            penalty = max(0.0, self.duplicate_margin_target - margin)
            obj += self.duplicate_penalty_weight * penalty

        self.cache[levels_key] = float(obj)
        return float(obj)

    def __call__(self, theta: Sequence[float]) -> float:
        levels = theta_to_levels(theta)
        return self.evaluate_levels(levels)


class LoggedObjective:
    def __init__(self, objective: CoverageObjective, logger: Optional[ProgressLogger] = None) -> None:
        self.objective = objective
        self.logger = logger

    def __call__(self, theta: Sequence[float]) -> float:
        value = self.objective(theta)
        if self.logger is not None:
            self.logger.note_value(theta, value)
        return value


# -----------------------------
# Seed families
# -----------------------------

def golomb_seed_thetas(total_spans: Iterable[float]) -> List[np.ndarray]:
    pattern = np.array([0, 1, 4, 10, 18, 23, 25], dtype=float)
    return [pattern_to_seed_theta(pattern, total_span=L) for L in total_spans]


def prime_log_seed_thetas(total_spans: Iterable[float]) -> List[np.ndarray]:
    pattern = np.log(np.array([2, 3, 5, 7, 11, 13, 17], dtype=float))
    pattern = pattern - pattern[0]
    return [pattern_to_seed_theta(pattern, total_span=L) for L in total_spans]


def geometric_seed_thetas(total_spans: Iterable[float]) -> List[np.ndarray]:
    pattern = np.linspace(0.0, 1.0, NUM_POS_LEVELS)
    return [pattern_to_seed_theta(pattern, total_span=L) for L in total_spans]


def custom_seed_thetas() -> List[np.ndarray]:
    return [positive_levels_to_seed_theta(CUSTOM_INITIAL_POSITIVE_LEVELS)]


# -----------------------------
# Optimisation driver
# -----------------------------

def optimise_levels(
    dim: int = DIM,
    num_targets_stage1: int = 384,
    num_targets_stage2: int = 2048,
    seed: int = 0,
    polish: bool = True,
    duplicate_penalty_weight: float = 0.0,
    duplicate_margin_target: float = 1e-3,
    device: str = "auto",
    batch_size: int = 2048,
    verbose: bool = True,
    progress_every_evals: int = 25,
    de_iter: int = 40,
    pm_iter: int = 80,
    initialization_mode: str = DEFAULT_OPTIMIZER_INIT_MODE,
) -> OptimisationResult:
    """
    Stage 1: global search with differential evolution on a coarse target set.
    Stage 2: local polishing on a refined target set.
    """
    overall_start = time.time()

    obj1 = CoverageObjective(
        dim=dim,
        num_targets=num_targets_stage1,
        seed=seed,
        duplicate_penalty_weight=duplicate_penalty_weight,
        duplicate_margin_target=duplicate_margin_target,
        device=device,
        batch_size=batch_size,
    )
    logger1 = ProgressLogger("stage1", verbose=verbose, print_every_evals=progress_every_evals)
    logged_obj1 = LoggedObjective(obj1, logger1)

    bounds = [(-4.0, 4.0)] * (THETA_DIM - 1) + [(math.log(0.3), math.log(6.0))]

    if initialization_mode == DEFAULT_OPTIMIZER_INIT_MODE:
        seed_spans = [0.6, 1.0, 1.6, 2.4, 3.5]
        seeds: List[np.ndarray] = []
        seeds.extend(golomb_seed_thetas(seed_spans))
        seeds.extend(prime_log_seed_thetas(seed_spans))
        seeds.extend(geometric_seed_thetas(seed_spans))
    elif initialization_mode == CUSTOM_OPTIMIZER_INIT_MODE:
        seeds = custom_seed_thetas()
        logger1.log(
            "using custom initial positive levels "
            + np.array2string(CUSTOM_INITIAL_POSITIVE_LEVELS, precision=8, separator=", ")
        )
    else:
        raise ValueError(
            f"Unknown initialization_mode '{initialization_mode}'. "
            f"Expected one of: {', '.join(OPTIMIZER_INIT_MODES)}."
        )

    best_theta: Optional[np.ndarray] = None
    best_value = math.inf

    logger1.log(f"evaluating {len(seeds)} seed points")
    for idx, th in enumerate(seeds, start=1):
        val = logged_obj1(th)
        if val < best_value:
            best_value = val
            best_theta = np.asarray(th, dtype=float).copy()
        if verbose:
            logger1.log(f"seed {idx:2d}/{len(seeds)}  value={val:.8f}  best={best_value:.8f}")

    de_generation = {"count": 0}

    def de_callback(xk: np.ndarray, convergence: float) -> bool:
        de_generation["count"] += 1
        current_val = obj1(xk)
        logger1.note_value(xk, current_val, force=True)
        logger1.log(
            f"DE generation {de_generation['count']:2d}  convergence={convergence:.6e}  current_best={current_val:.8f}"
        )
        return False

    logger1.log("starting differential evolution")
    de_result = differential_evolution(
        logged_obj1,
        bounds=bounds,
        strategy="best1bin",
        maxiter=de_iter,
        popsize=12,
        tol=1e-3,
        mutation=(0.5, 1.0),
        recombination=0.7,
        polish=False,
        seed=seed,
        updating="deferred",
        workers=1,
        x0=best_theta,
        callback=de_callback,
    )

    if de_result.fun < best_value:
        best_theta = np.asarray(de_result.x, dtype=float).copy()
        best_value = float(de_result.fun)
    logger1.log(f"stage 1 complete in {time.time() - overall_start:.1f}s  best={best_value:.8f}")

    local_best_value: Optional[float] = None

    if polish:
        assert best_theta is not None
        obj2 = CoverageObjective(
            dim=dim,
            num_targets=num_targets_stage2,
            seed=seed + 1,
            duplicate_penalty_weight=duplicate_penalty_weight,
            duplicate_margin_target=duplicate_margin_target,
            device=device,
            batch_size=batch_size,
        )
        logger2 = ProgressLogger("stage2", verbose=verbose, print_every_evals=progress_every_evals)
        logged_obj2 = LoggedObjective(obj2, logger2)

        logger2.log("starting Powell local polishing")

        def powell_callback(xk: np.ndarray) -> None:
            current_val = obj2(xk)
            logger2.note_value(xk, current_val, force=True)
            logger2.log("Powell iteration completed")

        baseline_local_value = obj2(best_theta)
        logger2.note_value(best_theta, baseline_local_value, force=True)

        local_result = minimize(
            logged_obj2,
            best_theta,
            method="Powell",
            callback=powell_callback,
            options={"maxiter": pm_iter, "xtol": 1e-3, "ftol": 1e-3, "disp": verbose},
        )
        if local_result.fun < baseline_local_value:
            best_theta = np.asarray(local_result.x, dtype=float).copy()
            local_best_value = float(local_result.fun)
        else:
            local_best_value = float(baseline_local_value)
        logger2.log(f"stage 2 complete  best={local_best_value:.8f}")

    assert best_theta is not None
    levels = theta_to_levels(best_theta)

    if verbose:
        print("[   final] computing final coverage statistics")
    rng = np.random.default_rng(seed + 12345)
    final_targets = unit_sphere_samples(max(4096, num_targets_stage2), dim, rng)
    final_backend = resolve_oracle_backend(device)
    prepared_final_targets = prepare_unit_vectors_for_backend(final_targets, final_backend)
    stats = coverage_statistics(
        levels,
        prepared_final_targets,
        backend=final_backend,
        batch_size=batch_size,
        targets_prepared=True,
    )
    if verbose:
        print(f"[   final] finished in {time.time() - overall_start:.1f}s")

    return OptimisationResult(
        theta=best_theta,
        levels=levels,
        log_levels=np.log(levels),
        objective_value=float(best_value),
        local_objective_value=local_best_value,
        stats=stats,
    )


# -----------------------------
# Runner entrypoint
# -----------------------------

def optimise_scalar_levels(
    bitwidth: int,
    dimension: int,
    num_targets_stage1: int = 384,
    num_targets_stage2: int = 1536,
    seed: int = 0,
    verbose: bool = False,
    device: str = "auto",
    batch_size: int = 2048,
    return_details: bool = False,
    de_iter: int = 40,
    pm_iter: int = 80,
    initialization_mode: str = DEFAULT_OPTIMIZER_INIT_MODE,
) -> np.ndarray | OptimizedScalarLevelsResult:
    """Optimise a scalar alphabet for directional coverage.

    Parameters
    ----------
    bitwidth:
        Target bitwidth. Currently only 4 bits is supported (7 positive levels).
    dimension:
        Vector dimension for optimization (affects coverage goal).
    num_targets_stage1:
        Number of target unit vectors for coarse stage 1 optimization.
    num_targets_stage2:
        Number of target unit vectors for fine stage 2 polishing.
    seed:
        Random seed for reproducibility.
    verbose:
        If True, print optimization progress.
    device:
        Oracle execution device: auto, cpu/numpy, or cuda[:N].
    batch_size:
        Number of target directions to evaluate per oracle batch.
    return_details:
        If True, return the full optimization summary alongside the signed scalar alphabet.
    initialization_mode:
        Seed selection mode for the optimizer. "default" evaluates the built-in
        Golomb, prime-log, and geometric seed families. "custom" forces the
        exact CUSTOM_INITIAL_POSITIVE_LEVELS as the initial seed.

    Returns
    -------
    If return_details is False:
        np.ndarray of shape (2 * NUM_POS_LEVELS + 1,) containing the full scalar alphabet:
            [-s_k, ..., -s_1, 0, s_1, ..., s_k]
        where s_1 < ... < s_k are the optimized positive levels.
    If return_details is True:
        OptimizedScalarLevelsResult containing the positive levels, signed alphabet,
        and optimization statistics.

    Raises
    ------
    NotImplementedError:
        If bitwidth != 4 (only 4-bit is currently supported due to hardcoded NUM_POS_LEVELS=7).
    """
    if bitwidth != 4:
        raise NotImplementedError(
            f"Only 4-bit alphabets are currently supported (bitwidth=4). "
            f"Got bitwidth={bitwidth}. "
            f"(NUM_POS_LEVELS={NUM_POS_LEVELS} is hardcoded; generalization requires refactoring.)"
        )

    result = optimise_levels(
        dim=dimension,
        num_targets_stage1=num_targets_stage1,
        num_targets_stage2=num_targets_stage2,
        seed=seed,
        polish=True,
        duplicate_penalty_weight=0.0,
        duplicate_margin_target=1e-3,
        device=device,
        batch_size=batch_size,
        verbose=verbose,
        progress_every_evals=25,
        de_iter=de_iter,
        pm_iter=pm_iter,
        initialization_mode=initialization_mode,
    )

    positive_levels = result.levels
    negative_levels = -positive_levels[::-1]
    full_alphabet = np.concatenate([negative_levels, [0.0], positive_levels])

    if return_details:
        return OptimizedScalarLevelsResult(
            bitwidth=bitwidth,
            dimension=dimension,
            positive_levels=positive_levels.copy(),
            full_alphabet=full_alphabet.copy(),
            optimisation_result=result,
        )

    return full_alphabet
