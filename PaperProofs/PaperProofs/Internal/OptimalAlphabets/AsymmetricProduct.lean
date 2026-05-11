import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.Defs
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.Bridge
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.HarmonicWitness
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.ProductLowerBound
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.SphericalBudget
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.AsymptoticSeparation
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.Correlation
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.NormalizedObjective
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.SignedLevels
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.FloatingPoint
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.LayerCake
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.BlockHardy
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.NormalizedSeparation

/-!
# OptimalAlphabets.AsymmetricProduct

Clean asymmetric-product layer for arbitrary finite scalar alphabets.

The main result is
`OptimalAlphabets.AsymmetricProduct.eventually_rho_sph_pow_lt_F_asym`, which
compares arbitrary `q`-element product alphabets against unconstrained
spherical codes with the same bit budget `q ^ n`.

The normalized correlation-based separation is staged in
`OptimalAlphabets.AsymmetricProduct.NormalizedSeparation`; it now uses the
standalone `blockHardy_lower` theorem for the unconditional final assembly.
For a prose guide to that proof, see
`OptimalAlphabets/AsymmetricProduct/NormalizedSeparationProof.md`.
-/
