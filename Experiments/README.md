# Experimental Platform

This directory contains the source python code for the experimental platform and optimizer (src/), along with an example output (final/). 

The goal of the experimental platform code is to estimate the worst case angular error for scalar datatypes when those datatypes are used to populate elements of a vector.

For each `(datatype, dimension, seed)` job, `src.runner` samples random unit
query directions, finds the nearest direction representable by the datatype
after scalar rescaling, and writes the maximum angular error observed, along with additional summary statistics.
The reported statistics are:

- max 
- mean
- median
- p95
- p99

All angle statistics are written in radians and degrees.

The repository also includes an optimizer, as described in the paper, for generating a 4-bit scalar
alphabet for a requested dimension `directional_coverage_optimizer`. 

`runner.py` will call the optimizer, if one of the datatypes selected requires it. Currently the optimizer only supports 4-bit datatypes.
## Installation

```bash
python -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
```

PyTorch is optional. With a CUDA-enabled PyTorch install, metric evaluation and
optimizer evaluation can run on `cuda` or `cuda:N`. Otherwise use `cpu` or
`numpy`.

## Quick Start

Run fixed datatypes for dimensions 4 and 8:

```bash
.venv/bin/python -m src.runner \
  --dimension 4 8 \
  --datatypes fp4_e2m1 fp4_e1m2 fp4_e1m2_ns int4 fp4_e3m0 \
  --query-vectors 10000 \
  --metric-device cpu \
  --output-dir results/example_angular_error
```

Run all registered fixed datatypes:

```bash
.venv/bin/python -m src.runner \
  --dimension 4 8 \
  --all \
  --query-vectors 10000 \
  --metric-device cpu \
  --output-dir results/all_datatypes
```

Run the optimized 4-bit datatype alongside fixed 4-bit datatypes:

```bash
.venv/bin/python -m src.runner \
  --dimension 4 8 16 \
  --datatypes optimized_4 fp4_e2m1 fp4_e1m2 fp4_e1m2_ns fp4_e3m0 int4 \
  --query-vectors 20000 \
  --seed 1 \
  --optimizer-targets-per-stage 384 1536 \
  --optimizer-de-iter 40 \
  --optimizer-pm-iter 80 \
  --optimizer-init-mode default \
  --metric-device cpu \
  --optimizer-device cpu \
  --output-dir results/optimized_4_example
```

On a CUDA machine, use device flags such as:

```bash
--metric-device cuda --optimizer-device cuda
```

## CLI

Required arguments:

- `--dimension` or `--dimensions`: one or more vector dimensions.
- `--datatypes ...` or `--all`: fixed datatype names, or `optimized_4` for
  generated 4-bit alphabets.
- `--output-dir`: output bundle directory.

Sampling and seed arguments:

- `--query-vectors`: number of sampled unit query directions. Default: `20000`.
- `--query-chunk-size`: query batch size. Default: `4096`.
- `--seed`: random seed, or starting seed with `--num-seeds`.
- `--seeds ...`: explicit seed list.
- `--num-seeds N`: evaluate `N` consecutive seeds.

When multiple seeds are evaluated, the output keeps one row per
`(datatype, dimension)`: the seed with the largest
`max_worst_case_angular_error_deg`. Ties keep the smaller seed.

Execution arguments:

- `--metric-device`: `auto`, `cpu`, `numpy`, `cuda`, or `cuda:N`.
- `--parallel-workers`: parallel CPU jobs. CUDA metric runs require
  `--parallel-workers 1`.

Optimizer arguments, used only with `optimized_4`:

- `--optimizer-device`: `auto`, `cpu`, `numpy`, `cuda`, or `cuda:N`.
- `--optimizer-batch-size`: oracle batch size for optimizer evaluations.
- `--optimizer-targets-per-stage STAGE1 STAGE2`: sampled target counts for the
  two optimizer stages.
- `--optimizer-init-mode`: `default` or `custom`.
- `--optimizer-de-iter`: differential-evolution generation limit.
- `--optimizer-pm-iter`: Powell polishing iteration limit.

## Supported Datatypes

Fixed datatypes:

- `fp8_e4m3`
- `fp8_e5m2`
- `int8`
- `fp4_e2m1`
- `fp4_e1m2`
- `fp4_e1m2_ns`
- `int4`
- `fp4_e3m0`

Optimized datatypes:

- `optimized_4`

Only optimized 4-bit scalar alphabets are implemented.

## Outputs

For `--output-dir results/example_angular_error`, the runner writes:

- `results/example_angular_error/example_angular_error_results.csv`
- `results/example_angular_error/example_angular_error_command.txt`

If an optimized datatype is included, it also writes:

- `results/example_angular_error/example_angular_error_optimized_code_details.csv`

The results CSV contains:

- `datatype`
- `dimension`
- `seed`
- `bitwidth_per_element`
- `mean_worst_case_angular_error_rad`
- `median_worst_case_angular_error_rad`
- `p95_worst_case_angular_error_rad`
- `p99_worst_case_angular_error_rad`
- `max_worst_case_angular_error_rad`
- `mean_worst_case_angular_error_deg`
- `median_worst_case_angular_error_deg`
- `p95_worst_case_angular_error_deg`
- `p99_worst_case_angular_error_deg`
- `max_worst_case_angular_error_deg`
- `wall_time_seconds`

The optimized-code details CSV contains:

- `datatype`
- `dimension`
- `bitwidth_per_element`
- `seed`
- `optimized_code`: positive scalar levels generated by the optimizer.
- `ordered_scalars`: full ordered scalar alphabet, including negatives and
  zero.

The command file records the repository root, original CLI arguments, a re-run
command, and parsed argument values.

## Directory Layout
- `src/runner.py`: command-line entry point and output writer.
- `src/metrics.py`: sampled angular error metric implementation.
- `src/oracle_batch.py`: batched nearest-direction oracle.
- `src/datatypes.py`: fixed scalar alphabets.
- `src/directional_coverage_optimizer.py`: optimizer for `optimized_4`.
- `src/utils.py`: numerical helpers.
- `final/`: checked-in example output files.
