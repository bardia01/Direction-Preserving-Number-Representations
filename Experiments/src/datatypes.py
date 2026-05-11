"""Datatype definitions and scalar-value generation.

This module contains exact scalar-value generators for supported formats.

The code intentionally favors readability and explicit formulas.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Iterable, Optional
import numpy as np


@dataclass(frozen=True)
class ScalarFormat:
    """Description of a scalar datatype used in the experiments."""

    name: str
    bitwidth: int
    ordered_values_fn: Optional[Callable[[int], np.ndarray]] = None
    description: str = ""

    def ordered_values(self, dimension: int) -> np.ndarray:
        if self.ordered_values_fn is None:
            raise ValueError(f"{self.name} does not support exact scalar enumeration.")
        return self.ordered_values_fn(dimension)

    def normalized_ordered_values(self, dimension: int = 0) -> np.ndarray:
        """Return ordered values scaled by their maximum absolute magnitude."""
        ordered_values = self.ordered_values(dimension)
        abs_max = np.max(np.abs(ordered_values))
        if abs_max == 0.0:
            raise ValueError(f"{self.name} ordered values cannot be normalized because abs_max is zero.")
        return ordered_values / abs_max


def _unique_sorted(values: np.ndarray) -> np.ndarray:
    """Return unique sorted finite values as float64.

    We convert to float64 for stable downstream computations.
    Signed zeros collapse to a single +0.0 here, which is what we want for grid generation.
    """
    values = np.asarray(values, dtype=np.float64)
    values = values[np.isfinite(values)]
    values[values == 0.0] = 0.0  # Canonicalize any surviving -0.0 to +0.0.
    values = np.unique(values)
    values.sort()
    return values


def _enumerate_binary_float_values(
    *,
    total_bits: int,
    exponent_bits: int,
    mantissa_bits: int,
    bias: int,
    exclude_all_max_exponent: bool = False,
    excluded_mantissas_at_max_exponent: Optional[Iterable[int]] = None,
) -> np.ndarray:
    """Enumerate finite values of a binary floating-point format.

    Parameters
    ----------
    total_bits:
        Total encoding width, including sign.
    exponent_bits:
        Number of exponent bits.
    mantissa_bits:
        Number of explicit trailing significand bits.
    bias:
        Exponent bias.
    exclude_all_max_exponent:
        If True, all encodings with exponent field all ones are excluded.
        This matches IEEE-like formats where exponent-all-ones encodes Inf/NaN.
    excluded_mantissas_at_max_exponent:
        Specific mantissas to exclude when exponent is all ones.
        This is used for E4M3, where only mantissa=all-ones is NaN and the
        remaining exponent-all-ones patterns are finite.
    """
    if total_bits != 1 + exponent_bits + mantissa_bits:
        raise ValueError("Expected total_bits == 1 + exponent_bits + mantissa_bits")

    exponent_max = (1 << exponent_bits) - 1
    mantissa_max = (1 << mantissa_bits) - 1
    excluded_mantissas = set(excluded_mantissas_at_max_exponent or [])

    values = []
    for bits in range(1 << total_bits):
        sign = (bits >> (exponent_bits + mantissa_bits)) & 0x1
        exponent = (bits >> mantissa_bits) & exponent_max
        mantissa = bits & mantissa_max

        if exponent == exponent_max:
            if exclude_all_max_exponent or mantissa in excluded_mantissas:
                continue

        if exponent == 0:
            if mantissa == 0:
                value = 0.0
            else:
                value = (2.0 ** (1 - bias)) * (mantissa / (2.0 ** mantissa_bits))
        else:
            value = (2.0 ** (exponent - bias)) * (
                1.0 + mantissa / (2.0 ** mantissa_bits)
            )

        if sign:
            value = -value

        values.append(value)

    out = _unique_sorted(np.array(values, dtype=np.float64))
    return out


def fp8_e4m3_values(_dimension: int = 0) -> np.ndarray:
    """Enumerate all finite scalar values of OCP OFP8 E4M3.

    Format details used:
    - 1 sign bit
    - 4 exponent bits with bias 7
    - 3 mantissa bits
    - E=0, M>0 are subnormals
    - E=15, M=7 are NaN encodings and are excluded
    - E4M3 has no infinities
    """
    return _enumerate_binary_float_values(
        total_bits=8,
        exponent_bits=4,
        mantissa_bits=3,
        bias=7,
        excluded_mantissas_at_max_exponent={0x7},
    )


def fp8_e5m2_values(_dimension: int = 0) -> np.ndarray:
    """Enumerate all finite scalar values of OCP OFP8 E5M2.

    Format details used:
    - 1 sign bit
    - 5 exponent bits with bias 15
    - 2 mantissa bits
    - E=0, M>0 are subnormals
    - E=31, M=0 are infinities and are excluded
    - E=31, M>0 are NaNs and are excluded
    """
    return _enumerate_binary_float_values(
        total_bits=8,
        exponent_bits=5,
        mantissa_bits=2,
        bias=15,
        exclude_all_max_exponent=True,
    )


def fp4_e2m1_values(_dimension: int = 0) -> np.ndarray:
    """Enumerate all finite scalar values of MX FP4 E2M1.

    Format details used:
    - 1 sign bit
    - 2 exponent bits with bias 1
    - 1 mantissa bit
    - E=0, M>0 is the only nonzero subnormal magnitude
    - No infinities, no NaNs
    """
    return _enumerate_binary_float_values(
        total_bits=4,
        exponent_bits=2,
        mantissa_bits=1,
        bias=1,
    )


def fp4_e1m2_positive_values() -> np.ndarray:
    """Return positive values for a 4-bit E1M2-style signed format.

    The modeled format uses:
    - 1 sign bit
    - 1 exponent bit with bias 1
    - 2 mantissa bits
    - one explicit zero encoding
    - no infinities, or NaNs
    - includes subnormals

    That leaves seven positive nonzero magnitudes.
    """
    return np.array([0.5, 1,  1.5,  2,   2.5,  3,  3.5], dtype=np.float64)


def fp4_e1m2_values(_dimension: int = 0) -> np.ndarray:
    """Enumerate all scalar values of the custom FP4 E1M2 format."""
    positive = fp4_e1m2_positive_values()
    values = np.concatenate((-positive[::-1], np.array([0.0]), positive))
    return _unique_sorted(values)


def fp4_e1m2_ns_positive_values() -> np.ndarray:
    """Return positive values for FP4 E1M2 without subnormals."""
    return np.array([0.625, 0.75, 0.875, 1.0, 1.25, 1.5, 1.75], dtype=np.float64)


def fp4_e1m2_ns_values(_dimension: int = 0) -> np.ndarray:
    """Enumerate all scalar values of FP4 E1M2 without subnormals."""
    positive = fp4_e1m2_ns_positive_values()
    values = np.concatenate((-positive[::-1], np.array([0.0]), positive))
    return _unique_sorted(values)


def twos_complement_integer_values(bits: int) -> np.ndarray:
    """Return the signed integer values representable in two's complement."""
    min_value = -(2 ** (bits - 1))
    max_value = (2 ** (bits - 1)) - 1
    return np.arange(min_value, max_value + 1, dtype=np.float64)


def int8_values(_dimension: int = 0) -> np.ndarray:
    return twos_complement_integer_values(8)


def int4_values(_dimension: int = 0) -> np.ndarray:
    #Use asymmetrical int4
    # return np.array([-8,-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7], dtype=np.float64)
    return twos_complement_integer_values(4)


def fp4_e3m0_positive_values() -> np.ndarray:
    """Return the positive levels of the 4-bit signed powers-of-two alphabet."""
    return np.array([1.0, 2.0, 4.0, 8.0, 16.0, 32.0, 64.0], dtype=np.float64)


def fp4_e3m0_values(_dimension: int = 0) -> np.ndarray:
    """Return a 4-bit signed powers-of-two alphabet with an explicit zero."""
    positive = fp4_e3m0_positive_values()
    values = np.concatenate((-positive[::-1], np.array([0.0]), positive))
    return _unique_sorted(values)


def create_scalar_format_from_values(
    name: str,
    ordered_scalar_values: np.ndarray,
    description: str = "",
) -> ScalarFormat:
    """Create a ScalarFormat from an explicit array of ordered scalar values.
    
    This is useful for dynamically generated alphabets (e.g., from optimization).
    The ordered_scalar_values array is captured by closure in the returned function.
    
    Parameters
    ----------
    name:
        Name of the format.
    ordered_scalar_values:
        1D array of sorted finite scalar values (required to be sorted and unique).
    description:
        Optional description string.
    
    Returns
    -------
    ScalarFormat with ordered_values_fn set to return the provided values.
    
    Raises
    ------
    ValueError:
        If values are not finite, not sorted, not unique, or empty.
    """
    values = np.asarray(ordered_scalar_values, dtype=np.float64)
    
    if values.ndim != 1:
        raise ValueError(f"ordered_scalar_values must be 1-dimensional, got shape {values.shape}")
    
    if values.size == 0:
        raise ValueError("ordered_scalar_values must not be empty")
    
    if not np.all(np.isfinite(values)):
        raise ValueError("All values must be finite")
    
    if not np.all(np.diff(values) > 0):
        raise ValueError("Values must be strictly increasing (sorted and unique)")
    
    # Infer bitwidth from the number of unique values.
    # We assume a symmetric signed alphabet: [-s_k, ..., -s_1, 0, s_1, ..., s_k]
    # Total count = 2k + 1, so bitwidth = ceil(log2(2k+1))
    num_values = len(values)
    inferred_bitwidth = int(np.ceil(np.log2(num_values)))
    
    # Create a closure that captures the values array.
    def ordered_values_fn(dimension: int) -> np.ndarray:
        # Dimension parameter is ignored for static formats; return the same values.
        return values.copy()
    
    return ScalarFormat(
        name=name,
        bitwidth=inferred_bitwidth,
        ordered_values_fn=ordered_values_fn,
        description=description or f"Optimized scalar format with {num_values} values",
    )


FORMATS: dict[str, ScalarFormat] = {
    "fp8_e4m3": ScalarFormat(
        name="fp8_e4m3",
        ordered_values_fn=fp8_e4m3_values,
        description="OCP OFP8 E4M3",
        bitwidth=8
    ),
    "fp8_e5m2": ScalarFormat(
        name="fp8_e5m2",
        ordered_values_fn=fp8_e5m2_values,
        description="OCP OFP8 E5M2",
        bitwidth=8
    ),
    "int8": ScalarFormat(
        name="int8",
        ordered_values_fn=int8_values,
        description="Two's-complement INT8 modeled as -128..127",
        bitwidth=8
    ),
    "fp4_e2m1": ScalarFormat(
        name="fp4_e2m1",
        ordered_values_fn=fp4_e2m1_values,
        description="OCP MX FP4 E2M1",
        bitwidth=4
    ),
    "fp4_e1m2": ScalarFormat(
        name="fp4_e1m2",
        ordered_values_fn=fp4_e1m2_values,
        description="Custom FP4 E1M2 with bias 1 and seven positive finite magnitudes",
        bitwidth=4
    ),
    "fp4_e1m2_ns": ScalarFormat(
        name="fp4_e1m2_ns",
        ordered_values_fn=fp4_e1m2_ns_values,
        description="Custom FP4 E1M2 without subnormals",
        bitwidth=4
    ),
    "int4": ScalarFormat(
        name="int4",
        ordered_values_fn=int4_values,
        description="Asymmetrical INT4 modeled as -8..7",
        bitwidth=4
    ),
    "fp4_e3m0": ScalarFormat(
        name="fp4_e3m0",
        ordered_values_fn=fp4_e3m0_values,
        description="Signed 4-bit powers-of-two alphabet: ±{1, 2, 4, 8, 16, 32, 64} and 0",
        bitwidth=4
    ),
}


def get_format(name: str) -> ScalarFormat:
    try:
        return FORMATS[name]
    except KeyError as exc:
        supported = ", ".join(sorted(FORMATS))
        raise ValueError(f"Unknown datatype '{name}'. Supported: {supported}") from exc
