import PaperProofs.Internal.OptimalAlphabets.SphericalRandomCovering
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.Defs

/-!
# OptimalAlphabets.AsymmetricProduct.SphericalBudget

Bit-budget spherical upper bounds for the asymmetric-product comparison.

This file only wraps the generic random-covering theorem so that the point
budget appears as the exact scalar storage budget `q ^ n`.
-/

noncomputable section

open Set Filter Topology Real Metric

namespace OptimalAlphabets
namespace AsymmetricProduct

theorem Nat_floor_real_pow_natCast (q n : ℕ) :
    ⌊((q : ℝ) ^ n)⌋₊ = q ^ n := by
  rw [← Nat.cast_pow, Nat.floor_natCast]

/-- Spherical random-covering upper bound with exact product-code bit budget. -/
theorem eventual_rho_sph_pow_le_of_mul_sin_gt_one {q : ℕ} (hq : 2 ≤ q)
    {theta : ℝ} (htheta0 : 0 < theta) (htheta_pi2 : theta < Real.pi / 2)
    (hmul : 1 < (q : ℝ) * Real.sin theta) :
    ∃ N : ℕ, ∀ n, N ≤ n → rho_sph n (q ^ n) ≤ theta := by
  have hq_real : 1 < (q : ℝ) := by
    exact_mod_cast (show 1 < q by omega)
  rcases eventualSphericalUpperBoundAt_of_mul_sin_gt_one
      (lam := (q : ℝ)) (theta := theta) hq_real htheta0 htheta_pi2 hmul with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  simpa [Nat_floor_real_pow_natCast q n] using hN n hn

end AsymmetricProduct
end OptimalAlphabets

