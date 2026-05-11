import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.SphericalBudget
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.ProductLowerBound

/-!
# OptimalAlphabets.AsymmetricProduct.AsymptoticSeparation

Assembly layer for the asymmetric product vs bit-budget spherical comparison.

The final theorem combines the harmonic product lower bound with the
random-covering spherical upper bound. The comparison is by scalar storage
budget `q ^ n`, not by the number of directions induced by the product code.
-/

noncomputable section

open Set Filter Topology Real Metric

namespace OptimalAlphabets
namespace AsymmetricProduct

/-- Product-side eventual lower bound at fixed alphabet cardinality and angle. -/
def EventuallyAsymProductLowerBound (q : ℕ) (theta : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → ∀ A : Finset ℝ, A.card = q → theta < F_asym n A

/-- The target eventual strict bit-budget comparison at fixed alphabet cardinality. -/
def EventuallyAsymmetricBitBudgetSeparation (q : ℕ) : Prop :=
  ∃ N : ℕ, 2 ≤ N ∧ ∀ n, N ≤ n → ∀ A : Finset ℝ,
    A.card = q → rho_sph n (q ^ n) < F_asym n A

/-- Pick a spherical angle above `arcsin (1 / q)` but below `π / 2`. -/
theorem exists_theta_for_bit_budget {q : ℕ} (hq : 2 ≤ q) :
    ∃ theta : ℝ,
      Real.arcsin (1 / (q : ℝ)) < theta ∧
      0 < theta ∧
      theta < Real.pi / 2 ∧
      1 < (q : ℝ) * Real.sin theta := by
  have hq_real : 1 < (q : ℝ) := by
    exact_mod_cast (show 1 < q by omega)
  have hq_pos : 0 < (q : ℝ) := lt_trans zero_lt_one hq_real
  have hinv_pos : 0 < (1 / (q : ℝ)) := one_div_pos.mpr hq_pos
  have hinv_lt_one : (1 / (q : ℝ)) < 1 := by
    rwa [div_lt_one hq_pos]
  have harc_pos : 0 < Real.arcsin (1 / (q : ℝ)) := by
    exact (Real.arcsin_pos : 0 < Real.arcsin (1 / (q : ℝ)) ↔
      0 < (1 / (q : ℝ))).2 hinv_pos
  have harc_lt_pi2 : Real.arcsin (1 / (q : ℝ)) < Real.pi / 2 := by
    simpa using
      (Real.arcsin_lt_pi_div_two : Real.arcsin (1 / (q : ℝ)) < Real.pi / 2 ↔
        (1 / (q : ℝ)) < 1).2 hinv_lt_one
  rcases exists_between harc_lt_pi2 with ⟨theta, htheta_gt, htheta_pi2⟩
  have htheta0 : 0 < theta := lt_trans harc_pos htheta_gt
  have htheta_mem_Ioc : theta ∈ Set.Ioc (-(Real.pi / 2)) (Real.pi / 2) := by
    refine ⟨?_, htheta_pi2.le⟩
    linarith [Real.pi_pos, htheta0]
  have hsin_lower : (1 / (q : ℝ)) < Real.sin theta := by
    exact (Real.arcsin_lt_iff_lt_sin' htheta_mem_Ioc).1 htheta_gt
  have hmul : 1 < (q : ℝ) * Real.sin theta := by
    have htmp : 1 < Real.sin theta * (q : ℝ) := (div_lt_iff₀ hq_pos).1 hsin_lower
    simpa [mul_comm] using htmp
  exact ⟨theta, htheta_gt, htheta0, htheta_pi2, hmul⟩

/-- Combination theorem: spherical random covering plus a product lower bound
at the same angle implies the bit-budget strict separation. -/
theorem eventually_asymmetric_bitBudget_separation_of_product_lower
    {q : ℕ} (hq : 2 ≤ q) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta_pi2 : theta < Real.pi / 2)
    (hmul : 1 < (q : ℝ) * Real.sin theta)
    (hprod : EventuallyAsymProductLowerBound q theta) :
    EventuallyAsymmetricBitBudgetSeparation q := by
  rcases eventual_rho_sph_pow_le_of_mul_sin_gt_one hq htheta0 htheta_pi2 hmul with
    ⟨N₁, hN₁⟩
  rcases hprod with ⟨N₂, hN₂⟩
  refine ⟨max (max N₁ N₂) 2, le_max_right _ _, ?_⟩
  intro n hn A hA
  have hN₁n : N₁ ≤ n := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hN₂n : N₂ ≤ n := by
    exact le_trans (le_max_right N₁ N₂) (le_trans (le_max_left _ _) hn)
  exact lt_of_le_of_lt (hN₁ n hN₁n) (hN₂ n hN₂n A hA)

/-- Parameter-free assembly theorem: it is enough to prove the product side
eventually beats every `θ` strictly between `arcsin (1 / q)` and `π / 2`. -/
theorem eventually_asymmetric_bitBudget_separation_of_product_lower_above_arcsin
    {q : ℕ} (hq : 2 ≤ q)
    (hprod : ∀ theta : ℝ,
      Real.arcsin (1 / (q : ℝ)) < theta →
      theta < Real.pi / 2 →
      EventuallyAsymProductLowerBound q theta) :
    EventuallyAsymmetricBitBudgetSeparation q := by
  rcases exists_theta_for_bit_budget hq with
    ⟨theta, htheta_gt, htheta0, htheta_pi2, hmul⟩
  exact eventually_asymmetric_bitBudget_separation_of_product_lower hq
    htheta0 htheta_pi2 hmul (hprod theta htheta_gt htheta_pi2)

/-- If `H n` is larger than the square threshold dictated by `θ`, then the
cardinality-only harmonic arccos lower bound is above `θ`. -/
theorem theta_lt_arccos_card_bound_of_H_gt {q n : ℕ} {theta : ℝ}
    (htheta0 : 0 < theta) (htheta_pi2 : theta < Real.pi / 2)
    (hH :
      (2 * Real.sqrt (q : ℝ) / Real.cos theta) ^ 2 < H n) :
    theta < Real.arccos (2 * Real.sqrt (q : ℝ) / Real.sqrt (H n)) := by
  have htheta_mem_Ioo : theta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    exact ⟨by linarith [Real.pi_pos, htheta0], htheta_pi2⟩
  have hcos_pos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo htheta_mem_Ioo
  have hHpos : 0 < H n := by
    exact lt_of_le_of_lt (sq_nonneg _) hH
  have hsqrtH_pos : 0 < Real.sqrt (H n) := Real.sqrt_pos_of_pos hHpos
  have hleft_lt_sqrtH :
      2 * Real.sqrt (q : ℝ) / Real.cos theta < Real.sqrt (H n) :=
    Real.lt_sqrt_of_sq_lt hH
  have hnum_lt :
      2 * Real.sqrt (q : ℝ) < Real.sqrt (H n) * Real.cos theta :=
    (div_lt_iff₀ hcos_pos).1 hleft_lt_sqrtH
  have harg_lt_cos :
      2 * Real.sqrt (q : ℝ) / Real.sqrt (H n) < Real.cos theta := by
    exact (div_lt_iff₀ hsqrtH_pos).2 (by
      simpa [mul_comm] using hnum_lt)
  have harg_nonneg :
      0 ≤ 2 * Real.sqrt (q : ℝ) / Real.sqrt (H n) := by
    positivity
  have htheta_le_pi : theta ≤ Real.pi := by
    linarith [Real.pi_pos, htheta_pi2]
  have hlt_arccos :
      Real.arccos (Real.cos theta) <
        Real.arccos (2 * Real.sqrt (q : ℝ) / Real.sqrt (H n)) := by
    exact Real.arccos_lt_arccos (by linarith) harg_lt_cos (Real.cos_le_one theta)
  simpa [Real.arccos_cos htheta0.le htheta_le_pi] using hlt_arccos

/-- Product-side eventual lower bound from the harmonic witness. -/
theorem eventually_product_lower_bound_above_arcsin {q : ℕ} (hq : 2 ≤ q) :
    ∀ theta : ℝ,
      Real.arcsin (1 / (q : ℝ)) < theta →
      theta < Real.pi / 2 →
      EventuallyAsymProductLowerBound q theta := by
  intro theta htheta_gt htheta_pi2
  have hq_real : 1 < (q : ℝ) := by
    exact_mod_cast (show 1 < q by omega)
  have hq_pos : 0 < (q : ℝ) := lt_trans zero_lt_one hq_real
  have hinv_pos : 0 < (1 / (q : ℝ)) := one_div_pos.mpr hq_pos
  have harc_pos : 0 < Real.arcsin (1 / (q : ℝ)) := by
    exact (Real.arcsin_pos : 0 < Real.arcsin (1 / (q : ℝ)) ↔
      0 < (1 / (q : ℝ))).2 hinv_pos
  have htheta0 : 0 < theta := lt_trans harc_pos htheta_gt
  let B : ℝ := (2 * Real.sqrt (q : ℝ) / Real.cos theta) ^ 2
  rcases eventually_H_gt B with ⟨N, hN⟩
  refine ⟨max N 1, ?_⟩
  intro n hn A hA
  have hNn : N ≤ n := le_trans (le_max_left N 1) hn
  have h1n : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnpos : 0 < n := Nat.succ_le_iff.mp h1n
  have hH : (2 * Real.sqrt (q : ℝ) / Real.cos theta) ^ 2 < H n := by
    simpa [B] using hN n hNn
  exact lt_of_lt_of_le
    (theta_lt_arccos_card_bound_of_H_gt htheta0 htheta_pi2 hH)
    (arccos_card_bound_le_F_asym hnpos hA)

/-- Final high-dimensional asymmetric-product versus bit-budget spherical
separation theorem. -/
theorem eventually_asymmetric_bitBudget_separation {q : ℕ} (hq : 2 ≤ q) :
    EventuallyAsymmetricBitBudgetSeparation q :=
  eventually_asymmetric_bitBudget_separation_of_product_lower_above_arcsin hq
    (eventually_product_lower_bound_above_arcsin hq)

/-- Expanded statement of the final theorem. -/
theorem eventually_rho_sph_pow_lt_F_asym {q : ℕ} (hq : 2 ≤ q) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n, N ≤ n → ∀ A : Finset ℝ,
      A.card = q → rho_sph n (q ^ n) < F_asym n A :=
  eventually_asymmetric_bitBudget_separation hq

end AsymmetricProduct
end OptimalAlphabets
