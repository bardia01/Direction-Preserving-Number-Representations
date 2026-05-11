import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.ProductLowerBound

/-!
# OptimalAlphabets.AsymmetricProduct.Correlation

Direct correlation objective for arbitrary finite scalar alphabets.

The main normalized-separation proof works with `alpha_asym` rather than with
`Real.cos (F_asym n A)`.  The compatibility theorem with `F_asym` is kept as a
separate interface theorem.

Definitions:

* `tupleCorr u x` is `<u,x> / ||x||` for a unit witness `u` and a raw tuple
  `x`.
* `maxCorr_asym n A u` maximizes `tupleCorr` over nonzero tuples in `A^n`.
* `alpha_asym n A` takes the infimum of this maximum over all unit witnesses.

The important structural lemmas for the normalized separation are:

* `alpha_asym_ge_neg_one` and `alpha_asym_le_one`, used to bound the `sSup`
  in `bestAsymCos`;
* `alpha_asym_mono_of_pos`, used when the arbitrary block alphabet is enlarged
  by the explicit extra scalar to obtain exactly `2^b` values;
* `le_alpha_asym_of_forall_exists_tuple`, used by the Block-Hardy sign
  alignment layer to lower-bound `alpha_asym` by constructing one good product
  tuple for every witness.
-/

noncomputable section

open Set Filter Topology Real Metric
open NormedSpace

namespace OptimalAlphabets
namespace AsymmetricProduct

/-- Correlation of a unit witness `u` against a nonzero raw product tuple. -/
def tupleCorr {n : ℕ} (u : SpherePoint n) (x : Fin n → ℝ) : ℝ :=
  inner ℝ u.1 (tupleVector x) / ‖tupleVector x‖

/-- For fixed `u`, maximize correlation over the nonzero product tuples.  If
there are no nonzero product tuples, use the harmless sentinel value `-1`. -/
def maxCorr_asym (n : ℕ) (A : Finset ℝ) (u : SpherePoint n) : ℝ :=
  if h : (nonzeroAsymProductTuples n A).Nonempty then
    (nonzeroAsymProductTuples n A).sup' h fun x => tupleCorr u x
  else
    -1

/-- Worst-case product correlation for an arbitrary finite scalar alphabet. -/
def alpha_asym (n : ℕ) (A : Finset ℝ) : ℝ :=
  sInf (Set.range (maxCorr_asym n A))

/-- A concrete point on `S^{n-1}` for `0 < n`. -/
def firstSpherePoint (n : ℕ) (hn : 0 < n) : SpherePoint n :=
  ⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    norm_num⟩

theorem tupleCorr_ge_neg_one {n : ℕ} (u : SpherePoint n) {x : Fin n → ℝ}
    (hx : tupleVector x ≠ 0) :
    -1 ≤ tupleCorr u x := by
  have hunorm : ‖u.1‖ = 1 := norm_spherePoint u
  have hxnorm_pos : 0 < ‖tupleVector x‖ := norm_pos_iff.mpr hx
  have habs :
      |inner ℝ u.1 (tupleVector x)| ≤ ‖u.1‖ * ‖tupleVector x‖ :=
    abs_real_inner_le_norm u.1 (tupleVector x)
  have hleft : -‖tupleVector x‖ ≤ inner ℝ u.1 (tupleVector x) := by
    have hleft' := (abs_le.mp habs).1
    simpa [hunorm] using hleft'
  have hdiv :=
    div_le_div_of_nonneg_right hleft hxnorm_pos.le
  unfold tupleCorr
  calc
    (-1 : ℝ) = -‖tupleVector x‖ / ‖tupleVector x‖ := by
      field_simp [hxnorm_pos.ne']
    _ ≤ inner ℝ u.1 (tupleVector x) / ‖tupleVector x‖ := hdiv

theorem tupleCorr_le_one {n : ℕ} (u : SpherePoint n) {x : Fin n → ℝ}
    (hx : tupleVector x ≠ 0) :
    tupleCorr u x ≤ 1 := by
  have hunorm : ‖u.1‖ = 1 := norm_spherePoint u
  have hxnorm_pos : 0 < ‖tupleVector x‖ := norm_pos_iff.mpr hx
  have habs :
      |inner ℝ u.1 (tupleVector x)| ≤ ‖u.1‖ * ‖tupleVector x‖ :=
    abs_real_inner_le_norm u.1 (tupleVector x)
  have hright : inner ℝ u.1 (tupleVector x) ≤ ‖tupleVector x‖ := by
    have hright' : inner ℝ u.1 (tupleVector x) ≤
        |inner ℝ u.1 (tupleVector x)| := le_abs_self _
    exact le_trans hright' (by simpa [hunorm] using habs)
  unfold tupleCorr
  exact div_le_one_of_le₀ hright hxnorm_pos.le

theorem maxCorr_asym_ge_neg_one {n : ℕ} (A : Finset ℝ) (u : SpherePoint n) :
    -1 ≤ maxCorr_asym n A u := by
  unfold maxCorr_asym
  split_ifs with h
  · let x₀ := Classical.choose h
    have hx₀_mem : x₀ ∈ nonzeroAsymProductTuples n A := Classical.choose_spec h
    have hx₀_ne : tupleVector x₀ ≠ 0 :=
      (mem_nonzeroAsymProductTuples.1 hx₀_mem).2
    exact le_trans (tupleCorr_ge_neg_one u hx₀_ne)
      (Finset.le_sup' (s := nonzeroAsymProductTuples n A)
        (f := fun x => tupleCorr u x) hx₀_mem)
  · norm_num

theorem maxCorr_asym_le_one {n : ℕ} (A : Finset ℝ) (u : SpherePoint n) :
    maxCorr_asym n A u ≤ 1 := by
  unfold maxCorr_asym
  split_ifs with h
  · rw [Finset.sup'_le_iff]
    intro x hx
    exact tupleCorr_le_one u (mem_nonzeroAsymProductTuples.1 hx).2
  · norm_num

/-- The direct correlation objective is bounded above by `1`. -/
theorem alpha_asym_le_one {n : ℕ} (hn : 0 < n) (A : Finset ℝ) :
    alpha_asym n A ≤ 1 := by
  unfold alpha_asym
  have hbdd : BddBelow (Set.range (maxCorr_asym n A)) := by
    refine ⟨-1, ?_⟩
    rintro y ⟨u, rfl⟩
    exact maxCorr_asym_ge_neg_one A u
  exact le_trans
    (csInf_le hbdd (Set.mem_range_self (firstSpherePoint n hn)))
    (maxCorr_asym_le_one A (firstSpherePoint n hn))

/-- The infimum defining `alpha_asym` is bounded above by evaluating at any
chosen sphere witness. -/
theorem alpha_asym_le_maxCorr {n : ℕ} (A : Finset ℝ) (u : SpherePoint n) :
    alpha_asym n A ≤ maxCorr_asym n A u := by
  unfold alpha_asym
  have hbdd : BddBelow (Set.range (maxCorr_asym n A)) := by
    refine ⟨-1, ?_⟩
    rintro y ⟨v, rfl⟩
    exact maxCorr_asym_ge_neg_one A v
  exact csInf_le hbdd (Set.mem_range_self u)

/-- To upper-bound `maxCorr_asym`, it is enough to upper-bound every nonzero
product tuple, together with the sentinel value used for an empty product. -/
theorem maxCorr_asym_le_of_forall {n : ℕ} {A : Finset ℝ}
    {u : SpherePoint n} {C : ℝ} (hC : -1 ≤ C)
    (hbound : ∀ x, x ∈ nonzeroAsymProductTuples n A → tupleCorr u x ≤ C) :
    maxCorr_asym n A u ≤ C := by
  unfold maxCorr_asym
  split_ifs with h
  · rw [Finset.sup'_le_iff]
    intro x hx
    exact hbound x hx
  · exact hC

/-- Any explicit nonzero product tuple lower-bounds the per-witness maximum. -/
theorem tupleCorr_le_maxCorr_asym {n : ℕ} {A : Finset ℝ}
    {u : SpherePoint n} {x : Fin n → ℝ}
    (hx : x ∈ nonzeroAsymProductTuples n A) :
    tupleCorr u x ≤ maxCorr_asym n A u := by
  unfold maxCorr_asym
  have hne : (nonzeroAsymProductTuples n A).Nonempty := ⟨x, hx⟩
  rw [dif_pos hne]
  exact Finset.le_sup' (s := nonzeroAsymProductTuples n A)
    (f := fun x => tupleCorr u x) hx

/-- To lower-bound `maxCorr_asym`, it is enough to exhibit one tuple attaining
that lower bound. -/
theorem le_maxCorr_asym_of_exists_tuple {n : ℕ} {A : Finset ℝ}
    {u : SpherePoint n} {C : ℝ}
    (hbound :
      ∃ x, x ∈ nonzeroAsymProductTuples n A ∧ C ≤ tupleCorr u x) :
    C ≤ maxCorr_asym n A u := by
  rcases hbound with ⟨x, hx, hxC⟩
  exact le_trans hxC (tupleCorr_le_maxCorr_asym hx)

/-- To lower-bound `alpha_asym`, it is enough to lower-bound every
per-witness maximum. -/
theorem le_alpha_asym_of_forall_le_maxCorr {n : ℕ} (hn : 0 < n)
    {A : Finset ℝ} {C : ℝ}
    (hbound : ∀ u : SpherePoint n, C ≤ maxCorr_asym n A u) :
    C ≤ alpha_asym n A := by
  unfold alpha_asym
  refine le_csInf ?_ ?_
  · exact ⟨maxCorr_asym n A (firstSpherePoint n hn),
      Set.mem_range_self (firstSpherePoint n hn)⟩
  · rintro y ⟨u, rfl⟩
    exact hbound u

/-- A convenient tuple-exhibition form of the lower-bound principle for
`alpha_asym`. -/
theorem le_alpha_asym_of_forall_exists_tuple {n : ℕ} (hn : 0 < n)
    {A : Finset ℝ} {C : ℝ}
    (hbound : ∀ u : SpherePoint n,
      ∃ x, x ∈ nonzeroAsymProductTuples n A ∧ C ≤ tupleCorr u x) :
    C ≤ alpha_asym n A :=
  le_alpha_asym_of_forall_le_maxCorr hn fun u =>
    le_maxCorr_asym_of_exists_tuple (hbound u)

/-- Pointwise monotonicity of the per-witness maximum under alphabet
enlargement. -/
theorem maxCorr_asym_mono {n : ℕ} {A B : Finset ℝ} (hAB : A ⊆ B)
    (u : SpherePoint n) :
    maxCorr_asym n A u ≤ maxCorr_asym n B u := by
  have htuples :
      nonzeroAsymProductTuples n A ⊆ nonzeroAsymProductTuples n B := by
    intro x hx
    rcases mem_nonzeroAsymProductTuples.1 hx with ⟨hxA, hxne⟩
    exact mem_nonzeroAsymProductTuples.2 ⟨fun i => hAB (hxA i), hxne⟩
  unfold maxCorr_asym
  by_cases hA : (nonzeroAsymProductTuples n A).Nonempty
  · have hB : (nonzeroAsymProductTuples n B).Nonempty := by
      rcases hA with ⟨x, hx⟩
      exact ⟨x, htuples hx⟩
    simp [hA, hB]
    obtain ⟨y, hy, hymax⟩ :=
      Finset.exists_mem_eq_sup' hB (fun x => tupleCorr u x)
    refine ⟨y, hy, ?_⟩
    intro x hx
    have hx_le :
        tupleCorr u x ≤
          (nonzeroAsymProductTuples n B).sup' hB
            (fun x => tupleCorr u x) :=
      Finset.le_sup' (s := nonzeroAsymProductTuples n B)
        (f := fun x => tupleCorr u x) (htuples hx)
    simpa [hymax] using hx_le
  · simp [hA]
    exact maxCorr_asym_ge_neg_one B u

/-- Monotonicity of `alpha_asym` under alphabet enlargement, for nonempty
ambient spheres. -/
theorem alpha_asym_mono_of_pos {n : ℕ} (hn : 0 < n) {A B : Finset ℝ}
    (hAB : A ⊆ B) :
    alpha_asym n A ≤ alpha_asym n B := by
  unfold alpha_asym
  have hA_bdd : BddBelow (Set.range (maxCorr_asym n A)) := by
    refine ⟨-1, ?_⟩
    rintro y ⟨u, rfl⟩
    exact maxCorr_asym_ge_neg_one A u
  refine le_csInf ?_ ?_
  · exact ⟨maxCorr_asym n B (firstSpherePoint n hn),
      Set.mem_range_self (firstSpherePoint n hn)⟩
  · rintro y ⟨u, rfl⟩
    exact le_trans
      (csInf_le hA_bdd (Set.mem_range_self u))
      (maxCorr_asym_mono hAB u)

end AsymmetricProduct
end OptimalAlphabets
