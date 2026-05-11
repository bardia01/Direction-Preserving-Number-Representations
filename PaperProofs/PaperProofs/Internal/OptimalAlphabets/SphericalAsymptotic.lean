import PaperProofs.Internal.OptimalAlphabets.SphericalCodes

/-!
# OptimalAlphabets.SphericalAsymptotic

Abstract asymptotic input packages for comparing product codes with
unconstrained spherical codes.

These predicates isolate the external geometric facts that will eventually be
 supplied by separate random-covering and growth arguments.
-/

noncomputable section

open Filter

namespace OptimalAlphabets
/-- Eventual upper bound for `rho_sph(n, floor(λ^n))` at a fixed angle `θ`. -/
def EventualSphericalUpperBoundAt (lam theta : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → rho_sph n ⌊lam ^ n⌋₊ ≤ theta
end OptimalAlphabets
