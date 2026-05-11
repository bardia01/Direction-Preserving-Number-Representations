"""Small utility helpers used across the project."""

from __future__ import annotations

import numpy as np


def angle_from_dot(dot_values: np.ndarray) -> np.ndarray:
    """Safely convert dot products to angles in radians."""
    # Here, it is okay to clip because the dot product of two unit vectors should be in [-1, 1], and any deviation from that is due to numerical issues. Clipping ensures we don't get NaNs from arccos. 
    return np.arccos(np.clip(dot_values, -1.0, 1.0))

def normalize_rows(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Normalize rows to unit length and remove zero rows."""
    norms = np.linalg.norm(x, axis=1)
    keep = norms > 0.0
    x = x[keep]
    norms = norms[keep]
    normalized_x = x / norms[:, None]
    return normalized_x, norms


def random_unit_vectors(count: int, dimension: int, rng: np.random.Generator) -> np.ndarray:
    """Sample random unit vectors uniformly from the sphere S^(dimension-1)."""
    x = rng.normal(size=(count, dimension))
    return normalize_rows(x)[0]


def degrees(rad: float) -> float:
    return float(np.degrees(rad))
