import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.Defs
import Mathlib.Analysis.PSeries

/-!
# OptimalAlphabets.AsymmetricProduct.HarmonicWitness

The harmonic witness and basic harmonic-number facts used in the asymmetric
product lower-bound argument.
-/

noncomputable section

open Set Filter Topology Real Metric
open NormedSpace

namespace OptimalAlphabets
namespace AsymmetricProduct

/-- Finite harmonic sum `1 + 1/2 + ... + 1/n`. -/
def H (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (((i : ℝ) + 1)⁻¹)

theorem H_tendsto_atTop :
    Tendsto H atTop atTop := by
  simpa [H] using Real.tendsto_sum_range_one_div_nat_succ_atTop

theorem eventually_H_gt (B : ℝ) :
    ∃ N : ℕ, ∀ n, N ≤ n → B < H n := by
  have hlarge : ∀ᶠ n : ℕ in atTop, B < H n :=
    H_tendsto_atTop.eventually_gt_atTop B
  exact eventually_atTop.1 hlarge

theorem H_pos {n : ℕ} (hn : 0 < n) :
    0 < H n := by
  unfold H
  refine Finset.sum_pos' (fun i hi => ?_) ?_
  · positivity
  · refine ⟨0, Finset.mem_range.mpr hn, ?_⟩
    norm_num

/-- The unnormalized weak-`ℓ₂` harmonic weight vector. -/
def harmonicWeights (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm
    fun i => 1 / Real.sqrt ((i : ℕ) + 1 : ℝ)

@[simp] theorem harmonicWeights_apply {n : ℕ} (i : Fin n) :
    harmonicWeights n i = 1 / Real.sqrt ((i : ℕ) + 1 : ℝ) := by
  simp [harmonicWeights]

theorem harmonicWeights_ne_zero {n : ℕ} (hn : 0 < n) :
    harmonicWeights n ≠ 0 := by
  intro hzero
  have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hn⟩) hzero
  simp [harmonicWeights] at hcoord

/-- The normalized harmonic witness on `S^{n-1}`. -/
def harmonicWitness (n : ℕ) (hn : 0 < n) : SpherePoint n :=
  ⟨NormedSpace.normalize (harmonicWeights n), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact NormedSpace.norm_normalize (x := harmonicWeights n) (harmonicWeights_ne_zero hn)⟩

end AsymmetricProduct
end OptimalAlphabets
