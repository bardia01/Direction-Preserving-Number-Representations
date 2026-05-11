# Direction-Preserving Number Representations

This repository contains the public code and proof artifacts for the paper
[Direction-Preserving Number Representations](https://arxiv.org/abs/2605.07662)
by Bardia Zadeh and George A. Constantinides.

The repository is organized around two parts of the paper:

- `PaperProofs/`: a Lean formalization of the paper's main theoretical results.
- `Experiments/`: Python code for the experimental platform, including the
  optimizer for direction-preserving scalar alphabets and scripts for estimating
  angular error.

Each directory has its own README with build and usage instructions.

_For an inuitive introduction to how scalar number formats affects angular coverage, try our [Directional Coverage Explorer](https://bardia01.github.io/directional_coverage_explorer/)_
## Paper

The paper is available on arXiv:

> Bardia Zadeh and George A. Constantinides.
> *Direction-Preserving Number Representations*.
> arXiv:2605.07662, 2026.
> https://arxiv.org/abs/2605.07662

The arXiv DOI is
[10.48550/arXiv.2605.07662](https://doi.org/10.48550/arXiv.2605.07662).

## Citation

If you use this repository, please cite the paper:

```bibtex
@misc{zadeh2026directionpreserving,
  title = {Direction-Preserving Number Representations},
  author = {Zadeh, Bardia and Constantinides, George A.},
  year = {2026},
  eprint = {2605.07662},
  archivePrefix = {arXiv},
  url = {https://arxiv.org/abs/2605.07662}
}
```

## Formal Proofs

The `PaperProofs/` directory contains the Lean project used to formalize the
paper's theoretical statements.

See [`PaperProofs/README.md`](PaperProofs/README.md) for build instructions,
the Lean project layout, and a mapping from paper statements to Lean
declarations.

## Experiments

The `Experiments/` directory contains the Python implementation used to generate
optimized scalar alphabets and estimate angular error for fixed and optimized
number formats.

It includes:

- `Experiments/src/`: source code for the runner, metric evaluation, datatype
  definitions, nearest-direction oracle, and optimizer.
- `Experiments/final/`: checked-in output files from the paper-scale experiment.
- `Experiments/README.md`: installation instructions, quick-start commands, CLI
  reference, supported datatypes, and output format documentation.

See [`Experiments/README.md`](Experiments/README.md) for details.

## Repository Layout

```text
.
+-- PaperProofs/      Lean formalization of the paper's theoretical results
+-- Experiments/      Python experimental platform and checked-in outputs
`-- README.md         This overview
```
