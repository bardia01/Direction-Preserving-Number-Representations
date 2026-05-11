# PaperProofs

Lean artifact for the paper *Direction-Preserving Number Representations*.

This directory is a standalone Lean package. The declarations that correspond
directly to statements in the paper live in the `PaperProofs` namespace. The
`PaperProofs/Internal` directory contains the supporting development needed by
those declarations.

## Build

The Lean version is specified by `lean-toolchain`, and the Mathlib dependency
closure is pinned by `lake-manifest.json`. From this directory, run:

```bash
lake exe cache get
lake build PaperProofs
```

If the Mathlib cache is already present, `lake build PaperProofs` is sufficient.

## Layout

- `PaperProofs.lean`: root module.
- `PaperProofs/Definitions.lean`: paper-facing definitions and notation.
- `PaperProofs/Wyner.lean`: Wyner's spherical-cap covering theorem.
- `PaperProofs/ProductVsSpherical.lean`: product-vs-spherical comparison and
  asymptotic separation results.
- `PaperProofs/DimensionTwo.lean`: dimension-2 classification results.
- `PaperProofs/StandardFormats.lean`: standard-format and floating-point
  results.
- `PaperProofs/NearestQuantization.lean`: nearest-quantization and scaling
  result.
- `PaperProofs/Internal/`: supporting Lean development used by the artifact.

## Paper Mapping

This table follows the numbering in the final preprint. It lists only
declarations that correspond directly to definitions, theorems, lemmas, and
corollaries stated in the paper. Supporting Lean lemmas are intentionally
omitted. Lean declaration names are stable identifiers and do not necessarily
repeat the paper number.

| Paper item | Paper title | Lean declaration | File |
|---|---|---|---|
| Definition 1 | Finite scalar alphabets | `Aq` | `PaperProofs/Definitions.lean` |
| Definition 2 | Product code direction set | `P`, `Pdir` | `PaperProofs/Definitions.lean` |
| Definition 3 | Product code covering objective | `F` | `PaperProofs/Definitions.lean` |
| Definition 4 | Best achievable value at fixed alphabet size | `w` | `PaperProofs/Definitions.lean` |
| Definition 5 | Optimal spherical covering radius | `rhoSph` | `PaperProofs/Definitions.lean` |
| Definition 6 | Harmonic witness | `H`, `harmonicWitness` | `PaperProofs/Definitions.lean` |
| Definition 7 | Sign counts | `pPos`, `pNeg`, `mSign` | `PaperProofs/Definitions.lean` |
| Definition 8 | Spherical cap covering number | `Mc`, `OptimalAlphabets.SphericalCapCover`, `OptimalAlphabets.sphericalCapCoveringNumber` | `PaperProofs/Wyner.lean`, `PaperProofs/Internal/OptimalAlphabets/SphericalCapCovering.lean` |
| Definition 9 | Canonical floating-point family | `PhiPlus`, `Phi`, `fpSplits`, `fpExponentBits`, `bestFpCos`, `normBestFpCos` | `PaperProofs/Definitions.lean` |
| Lemma 1 | Exact spherical optimum on the circle | `lemma1_exact_spherical_optimum_on_circle` | `PaperProofs/DimensionTwo.lean` |
| Theorem 1 | Complete dimension-2 classification | `theorem1_complete_dimension2_classification` | `PaperProofs/DimensionTwo.lean` |
| Theorem 2 | Sign-count bound | `theorem2_sign_count_bound` | `PaperProofs/ProductVsSpherical.lean` |
| Corollary 1 | Uniform q-element consequence | `corollary1_uniform_q_element_consequence` | `PaperProofs/ProductVsSpherical.lean` |
| Theorem 3 | Wyner asymptotic covering formula | `theorem3_wyner_full_log_limit`, `theorem3_wyner_full_log_error_isLittleO` | `PaperProofs/Wyner.lean` |
| Corollary 2 | Exponential spherical upper bound | `corollary2_exponential_spherical_upper_bound` | `PaperProofs/ProductVsSpherical.lean` |
| Theorem 4 | Asymptotic strict separation | `theorem4_asymptotic_strict_separation_fixed_alphabet_size`, `theorem4_best_value_consequence` | `PaperProofs/ProductVsSpherical.lean` |
| Lemma 2 | Fixed sign-symmetric alphabets | `lemma2_fixed_sign_symmetric_alphabets` | `PaperProofs/StandardFormats.lean` |
| Corollary 3 | Floating-point normalized obstruction | `corollary3_limsup` | `PaperProofs/StandardFormats.lean` |
| Theorem 5 | Arbitrary alphabets | `corollary4_liminf` | `PaperProofs/StandardFormats.lean` |
| Theorem 6 | Superiority of arbitrary alphabets | `theorem5_superiority_of_arbitrary_alphabets`, `theorem5_liminf_limsup_chain` | `PaperProofs/StandardFormats.lean` |
| Appendix Lemma A1 | Pointwise comparison with spherical codes | `appendix_lemma3_pointwise_comparison` | `PaperProofs/ProductVsSpherical.lean` |
| Appendix Lemma A2 | Antitonicity in the code size | `appendix_lemma4_antitonicity_in_code_size` | `PaperProofs/ProductVsSpherical.lean` |
| Appendix Lemma A3 | Collisions in dimension 2 | `appendix_lemma5_collisions_in_dimension2` | `PaperProofs/DimensionTwo.lean` |
| Appendix Lemma A4 | No-collision case | `appendix_lemma6_no_collision_case` | `PaperProofs/DimensionTwo.lean` |
| Appendix Lemma A5 | Binary no-collision case | `appendix_lemma7_binary_no_collision_case` | `PaperProofs/DimensionTwo.lean` |
| Appendix Corollary A1 | Uniform dimension-2 strict separation for q >= 3 | `corollary5_uniform_dimension2_strict_separation` | `PaperProofs/DimensionTwo.lean` |
| Appendix Lemma B1 | Rearrangement inequality | `OptimalAlphabets.AsymmetricProduct.sum_harmonicWeight_subset_le_initial` | `PaperProofs/Internal/OptimalAlphabets/AsymmetricProduct/ProductLowerBound.lean` |
| Appendix Lemma B2 | Partial sums of harmonic witness | `OptimalAlphabets.AsymmetricProduct.harmonicWeightNat_partial_sum_le` | `PaperProofs/Internal/OptimalAlphabets/AsymmetricProduct/ProductLowerBound.lean` |
| Appendix Lemma B3 | Step-vector estimate | `OptimalAlphabets.AsymmetricProduct.inner_harmonicWeights_tupleVector_le_posCount` | `PaperProofs/Internal/OptimalAlphabets/AsymmetricProduct/ProductLowerBound.lean` |
| Appendix Lemma D1 | Product-code coverage in the limit | `appendix_lemma11_product_code_coverage_in_limit` | `PaperProofs/StandardFormats.lean` |
| Appendix Lemma D2 | Unmatched scalar | `appendix_lemmaD2_unmatched_scalar` | `PaperProofs/StandardFormats.lean` |
| Appendix Lemma D3 | Quadratic form | `appendix_lemma13_quadratic_form` | `PaperProofs/StandardFormats.lean` |
| Appendix Lemma D4 | Consecutive floating-point ratios | `appendix_lemma14_consecutive_floating_point_ratios` | `PaperProofs/StandardFormats.lean` |
| Appendix Lemma D5 | m-level cosine lower bound | `appendix_lemma15_m_level_cosine_lower_bound` | `PaperProofs/StandardFormats.lean` |
| Appendix Theorem E.1 | Scaling to find minimum codeword | `theorem6_scaling_to_find_minimum_codeword` | `PaperProofs/NearestQuantization.lean` |
