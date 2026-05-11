import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.HarmonicWitness
import Mathlib.Algebra.BigOperators.Fin

/-!
# OptimalAlphabets.AsymmetricProduct.ProductLowerBound

Product-side harmonic witness estimates for arbitrary finite scalar alphabets.

This file deliberately works with the clean asymmetric-product definitions
instead of the older normalized/signed product-code layer.
-/

noncomputable section

open Set Filter Topology Real Metric
open NormedSpace
open scoped BigOperators

namespace OptimalAlphabets
namespace AsymmetricProduct

/-- The unnormalised harmonic weight as a scalar sequence. -/
def harmonicWeightNat (i : ℕ) : ℝ :=
  1 / Real.sqrt ((i : ℝ) + 1)

theorem harmonicWeightNat_nonneg (i : ℕ) :
    0 ≤ harmonicWeightNat i := by
  unfold harmonicWeightNat
  positivity

theorem harmonicWeightNat_antitone :
    Antitone harmonicWeightNat := by
  intro i j hij
  unfold harmonicWeightNat
  have hsqrt :
      Real.sqrt ((i : ℝ) + 1) ≤ Real.sqrt ((j : ℝ) + 1) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.succ_le_succ hij
  exact one_div_le_one_div_of_le (by positivity) hsqrt

/-- One summand in the telescoping estimate for the weak-`ℓ₂` profile. -/
theorem harmonicWeightNat_le_two_mul_sqrt_sub (m : ℕ) :
    harmonicWeightNat m ≤
      2 * (Real.sqrt ((m : ℝ) + 1) - Real.sqrt (m : ℝ)) := by
  let a : ℝ := Real.sqrt ((m : ℝ) + 1)
  let b : ℝ := Real.sqrt (m : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hsum_pos : 0 < a + b := by
    positivity
  have hb_le_a : b ≤ a := by
    dsimp [a, b]
    apply Real.sqrt_le_sqrt
    linarith
  have hden : a + b ≤ 2 * a := by
    nlinarith
  have h_inv : 1 / (2 * a) ≤ 1 / (a + b) := by
    exact one_div_le_one_div_of_le (by positivity) hden
  have hdiff : a - b = 1 / (a + b) := by
    rw [eq_div_iff hsum_pos.ne']
    have ha_sq : a ^ 2 = (m : ℝ) + 1 := by
      dsimp [a]
      rw [Real.sq_sqrt]
      positivity
    have hb_sq : b ^ 2 = (m : ℝ) := by
      dsimp [b]
      rw [Real.sq_sqrt]
      positivity
    nlinarith
  calc
    harmonicWeightNat m = 1 / a := by
      rfl
    _ = 2 * (1 / (2 * a)) := by
      field_simp [ha.ne']
    _ ≤ 2 * (1 / (a + b)) := by
      exact mul_le_mul_of_nonneg_left h_inv (by norm_num)
    _ = 2 * (a - b) := by
      rw [hdiff]

/-- The elementary partial-sum estimate `∑_{i < m} 1 / sqrt (i+1) ≤ 2 sqrt m`. -/
theorem harmonicWeightNat_partial_sum_le (m : ℕ) :
    ∑ i ∈ Finset.range m, harmonicWeightNat i ≤ 2 * Real.sqrt (m : ℝ) := by
  induction m with
  | zero =>
      simp [harmonicWeightNat]
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hterm := harmonicWeightNat_le_two_mul_sqrt_sub m
      calc
        (∑ i ∈ Finset.range m, harmonicWeightNat i) + harmonicWeightNat m
            ≤ 2 * Real.sqrt (m : ℝ) +
                2 * (Real.sqrt ((m : ℝ) + 1) - Real.sqrt (m : ℝ)) := by
              exact add_le_add ih hterm
        _ = 2 * Real.sqrt ((m : ℝ) + 1) := by
              ring
        _ = 2 * Real.sqrt ((Nat.succ m : ℕ) : ℝ) := by
              simp

/-- If a strictly increasing map `Fin m → ℕ` is used to list `m` naturals,
then its `i`-th value is at least `i`. -/
theorem strictMono_nat_ge_index {m : ℕ} {f : Fin m → ℕ}
    (hf : StrictMono f) (i : Fin m) :
    (i : ℕ) ≤ f i := by
  rcases i with ⟨k, hk⟩
  induction k with
  | zero =>
      exact Nat.zero_le _
  | succ k ih =>
      have hklt : k < m := Nat.lt_trans (Nat.lt_succ_self k) hk
      have hstep : f ⟨k, hklt⟩ < f ⟨k + 1, hk⟩ := by
        apply hf
        simp [Fin.lt_def]
      exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih hklt) hstep)

/-- Among all subsets of `Fin n` of size `m`, the initial segment maximizes the
sum of the decreasing harmonic weights. -/
theorem sum_harmonicWeight_subset_le_initial {n : ℕ} (S : Finset (Fin n)) :
    ∑ i ∈ S, harmonicWeightNat (i : ℕ) ≤
      ∑ i ∈ Finset.range S.card, harmonicWeightNat i := by
  classical
  let e := S.orderEmbOfFin (rfl : S.card = S.card)
  have hstrict : StrictMono fun i : Fin S.card => ((e i : Fin n) : ℕ) := by
    intro i j hij
    exact Fin.lt_def.mp (e.strictMono hij)
  have hsum_enum :
      (∑ i : Fin S.card, harmonicWeightNat ((e i : Fin n) : ℕ)) =
        ∑ i ∈ S, harmonicWeightNat (i : ℕ) := by
    refine Finset.sum_bij (fun i _hi => e i) ?_ ?_ ?_ ?_
    · intro i _hi
      exact Finset.orderEmbOfFin_mem S (rfl : S.card = S.card) i
    · intro i₁ _hi₁ i₂ _hi₂ hij
      exact e.injective hij
    · intro b hb
      have hmap : Finset.map e.toEmbedding Finset.univ = S := by
        simp [e]
      have hbmap : b ∈ Finset.map e.toEmbedding Finset.univ := by
        simpa [hmap] using hb
      rcases Finset.mem_map.1 hbmap with ⟨i, hi, hbi⟩
      exact ⟨i, hi, hbi⟩
    · intro i _hi
      rfl
  calc
    ∑ i ∈ S, harmonicWeightNat (i : ℕ)
        = ∑ i : Fin S.card, harmonicWeightNat ((e i : Fin n) : ℕ) := by
          exact hsum_enum.symm
    _ ≤ ∑ i : Fin S.card, harmonicWeightNat (i : ℕ) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          exact harmonicWeightNat_antitone (strictMono_nat_ge_index hstrict i)
    _ = ∑ i ∈ Finset.range S.card, harmonicWeightNat i := by
          exact (Finset.sum_range (fun i => harmonicWeightNat i)).symm

/-- A subset form of the partial-sum estimate. -/
theorem sum_harmonicWeight_subset_le {n : ℕ} (S : Finset (Fin n)) :
    ∑ i ∈ S, harmonicWeightNat (i : ℕ) ≤ 2 * Real.sqrt (S.card : ℝ) :=
  (sum_harmonicWeight_subset_le_initial S).trans
    (harmonicWeightNat_partial_sum_le S.card)

@[simp] theorem harmonicWeights_apply_harmonicWeightNat {n : ℕ} (i : Fin n) :
    harmonicWeights n i = harmonicWeightNat (i : ℕ) := by
  simp [harmonicWeightNat]

/-- The Euclidean norm of the unnormalised harmonic witness is `sqrt (H n)`. -/
theorem harmonicWeights_norm (n : ℕ) :
    ‖harmonicWeights n‖ = Real.sqrt (H n) := by
  rw [EuclideanSpace.norm_eq, H, Finset.sum_range]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [harmonicWeights_apply_harmonicWeightNat]
  unfold harmonicWeightNat
  rw [Real.norm_eq_abs, sq_abs]
  have hpos : 0 < Real.sqrt (((i : ℕ) : ℝ) + 1) := by
    positivity
  field_simp [hpos.ne']
  rw [Real.sq_sqrt (by positivity)]

/-- Coordinates where a raw tuple is positive. -/
def positiveCoordinateSet {n : ℕ} (x : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => 0 < x i

@[simp] theorem mem_positiveCoordinateSet {n : ℕ} {x : Fin n → ℝ} {i : Fin n} :
    i ∈ positiveCoordinateSet x ↔ 0 < x i := by
  classical
  simp [positiveCoordinateSet]

/-- Coordinates where a raw tuple takes a specified scalar value. -/
def coordinateFiber {n : ℕ} (x : Fin n → ℝ) (a : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => x i = a

@[simp] theorem mem_coordinateFiber {n : ℕ} {x : Fin n → ℝ} {a : ℝ} {i : Fin n} :
    i ∈ coordinateFiber x a ↔ x i = a := by
  classical
  simp [coordinateFiber]

theorem inner_harmonicWeights_tupleVector {n : ℕ} (x : Fin n → ℝ) :
    inner ℝ (harmonicWeights n) (tupleVector x) =
      ∑ i : Fin n, harmonicWeightNat (i : ℕ) * x i := by
  simp [PiLp.inner_apply, tupleVector, harmonicWeightNat, mul_comm]

theorem inner_harmonicWeights_tupleVector_le_positive_sum {n : ℕ}
    (x : Fin n → ℝ) :
    inner ℝ (harmonicWeights n) (tupleVector x) ≤
      ∑ i ∈ positiveCoordinateSet x, harmonicWeightNat (i : ℕ) * x i := by
  rw [inner_harmonicWeights_tupleVector]
  classical
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => 0 < x i)
      (f := fun i => harmonicWeightNat (i : ℕ) * x i)
  have hnonpos :
      ∑ i ∈ Finset.univ with ¬ 0 < x i, harmonicWeightNat (i : ℕ) * x i ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro i hi
    have hnot : ¬ 0 < x i := by
      simpa using hi
    have hxi : x i ≤ 0 := le_of_not_gt hnot
    exact mul_nonpos_of_nonneg_of_nonpos (harmonicWeightNat_nonneg (i : ℕ)) hxi
  have hsum :
      (∑ i : Fin n, harmonicWeightNat (i : ℕ) * x i) =
        (∑ i ∈ positiveCoordinateSet x, harmonicWeightNat (i : ℕ) * x i) +
          ∑ i ∈ Finset.univ with ¬ 0 < x i, harmonicWeightNat (i : ℕ) * x i := by
    rw [← hsplit]
    simp [positiveCoordinateSet]
  rw [hsum]
  linarith

/-- The raw harmonic dot product is bounded using only the number of positive
alphabet values. -/
theorem inner_harmonicWeights_tupleVector_le_posCount {n : ℕ}
    {A : Finset ℝ} {x : Fin n → ℝ} (hxA : ∀ i, x i ∈ A) :
    inner ℝ (harmonicWeights n) (tupleVector x) ≤
      2 * Real.sqrt (posCount A : ℝ) * ‖tupleVector x‖ := by
  classical
  let S := positiveCoordinateSet x
  let P := posPart A
  let m : ℝ → ℕ := fun a => (S.filter fun i => x i = a).card
  have hmaps : ∀ i ∈ S, x i ∈ P := by
    intro i hi
    have hpos : 0 < x i := by simpa [S] using hi
    have hmem : x i ∈ A := hxA i
    simp [P, posPart, hmem, hpos]
  have hpositive_sum_fiber :
      (∑ i ∈ S, harmonicWeightNat (i : ℕ) * x i) =
        ∑ a ∈ P, ∑ i ∈ S with x i = a,
          harmonicWeightNat (i : ℕ) * x i := by
    exact (Finset.sum_fiberwise_of_maps_to
      (s := S) (t := P) (g := fun i => x i) hmaps
      (f := fun i => harmonicWeightNat (i : ℕ) * x i)).symm
  have hfiber_bound (a : ℝ) (ha : a ∈ P) :
      ∑ i ∈ S with x i = a, harmonicWeightNat (i : ℕ) * x i ≤
        a * (2 * Real.sqrt (m a : ℝ)) := by
    have hapos : 0 < a := by
      have hmem : a ∈ A ∧ 0 < a := by
        simpa [P, posPart] using ha
      exact hmem.2
    have hconst :
        (∑ i ∈ S with x i = a, harmonicWeightNat (i : ℕ) * x i) =
          a * ∑ i ∈ S with x i = a, harmonicWeightNat (i : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hmem : i ∈ S ∧ x i = a := by
        simpa using hi
      have hxia : x i = a := hmem.2
      rw [hxia]
      ring
    have hsubset :
        ∑ i ∈ S with x i = a, harmonicWeightNat (i : ℕ) ≤
          2 * Real.sqrt (m a : ℝ) := by
      simpa [m] using sum_harmonicWeight_subset_le (S.filter fun i => x i = a)
    rw [hconst]
    exact mul_le_mul_of_nonneg_left hsubset hapos.le
  have hpositive_sum_bound :
      (∑ i ∈ S, harmonicWeightNat (i : ℕ) * x i) ≤
        2 * ∑ a ∈ P, a * Real.sqrt (m a : ℝ) := by
    rw [hpositive_sum_fiber]
    calc
      ∑ a ∈ P, ∑ i ∈ S with x i = a, harmonicWeightNat (i : ℕ) * x i
          ≤ ∑ a ∈ P, a * (2 * Real.sqrt (m a : ℝ)) := by
            exact Finset.sum_le_sum hfiber_bound
      _ = 2 * ∑ a ∈ P, a * Real.sqrt (m a : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro a ha
            ring
  have hsquares_fiber :
      (∑ i ∈ S, (x i) ^ 2) =
        ∑ a ∈ P, ∑ i ∈ S with x i = a, (x i) ^ 2 := by
    exact (Finset.sum_fiberwise_of_maps_to
      (s := S) (t := P) (g := fun i => x i) hmaps
      (f := fun i => (x i) ^ 2)).symm
  have hsquares_eq :
      ∑ a ∈ P, (a * Real.sqrt (m a : ℝ)) ^ 2 =
        ∑ i ∈ S, (x i) ^ 2 := by
    rw [hsquares_fiber]
    refine Finset.sum_congr rfl ?_
    intro a ha
    have hm_nonneg : 0 ≤ (m a : ℝ) := by positivity
    calc
      (a * Real.sqrt (m a : ℝ)) ^ 2
          = a ^ 2 * (m a : ℝ) := by
            rw [mul_pow, Real.sq_sqrt hm_nonneg]
      _ = ∑ i ∈ S with x i = a, (x i) ^ 2 := by
            have hconst :
                (∑ i ∈ S with x i = a, (a ^ 2 : ℝ)) = (m a : ℝ) * a ^ 2 := by
              simp [m]
            calc
              a ^ 2 * (m a : ℝ) = (m a : ℝ) * a ^ 2 := by ring
              _ = ∑ i ∈ S with x i = a, (a ^ 2 : ℝ) := hconst.symm
              _ = ∑ i ∈ S with x i = a, (x i) ^ 2 := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    have hmem : i ∈ S ∧ x i = a := by
                      simpa using hi
                    rw [hmem.2]
  have hsquares_le_norm :
      ∑ a ∈ P, (a * Real.sqrt (m a : ℝ)) ^ 2 ≤ ‖tupleVector x‖ ^ 2 := by
    rw [hsquares_eq]
    calc
      ∑ i ∈ S, (x i) ^ 2 ≤ ∑ i : Fin n, (x i) ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by intro i hi; simp)
          (by intro i _hi _hnot; positivity)
      _ = ‖tupleVector x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp [tupleVector, Real.norm_eq_abs, sq_abs]
  have hcauchy :
      ∑ a ∈ P, a * Real.sqrt (m a : ℝ) ≤
        Real.sqrt (∑ a ∈ P, (a * Real.sqrt (m a : ℝ)) ^ 2) *
          Real.sqrt (∑ _a ∈ P, (1 : ℝ) ^ 2) := by
    simpa using
      Real.sum_mul_le_sqrt_mul_sqrt P
        (fun a => a * Real.sqrt (m a : ℝ)) (fun _a => (1 : ℝ))
  have hcard :
      Real.sqrt (∑ _a ∈ P, (1 : ℝ) ^ 2) = Real.sqrt (posCount A : ℝ) := by
    simp [P, posCount]
  have hsqrt_norm :
      Real.sqrt (∑ a ∈ P, (a * Real.sqrt (m a : ℝ)) ^ 2) ≤ ‖tupleVector x‖ := by
    calc
      Real.sqrt (∑ a ∈ P, (a * Real.sqrt (m a : ℝ)) ^ 2)
          ≤ Real.sqrt (‖tupleVector x‖ ^ 2) := Real.sqrt_le_sqrt hsquares_le_norm
      _ = ‖tupleVector x‖ := Real.sqrt_sq (norm_nonneg _)
  calc
    inner ℝ (harmonicWeights n) (tupleVector x)
        ≤ ∑ i ∈ S, harmonicWeightNat (i : ℕ) * x i :=
          inner_harmonicWeights_tupleVector_le_positive_sum x
    _ ≤ 2 * ∑ a ∈ P, a * Real.sqrt (m a : ℝ) := hpositive_sum_bound
    _ ≤ 2 *
        (Real.sqrt (∑ a ∈ P, (a * Real.sqrt (m a : ℝ)) ^ 2) *
          Real.sqrt (posCount A : ℝ)) := by
          rw [← hcard]
          exact mul_le_mul_of_nonneg_left hcauchy (by norm_num)
    _ ≤ 2 * (‖tupleVector x‖ * Real.sqrt (posCount A : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hsqrt_norm (by positivity)) (by norm_num)
    _ = 2 * Real.sqrt (posCount A : ℝ) * ‖tupleVector x‖ := by
          ring

/-- Norm of a bundled sphere point. -/
theorem norm_spherePoint {n : ℕ} (u : SpherePoint n) :
    ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have hu := u.2
  rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hu

/-- Membership in the bundled asymmetric spherical code comes from a nonzero
raw product tuple. -/
theorem exists_tuple_of_mem_asymProdSphericalCode {n : ℕ} {A : Finset ℝ}
    {c : SpherePoint n} (hc : c ∈ asymProdSphericalCode n A) :
    ∃ x, x ∈ nonzeroAsymProductTuples n A ∧
      NormedSpace.normalize (tupleVector x) = c.1 := by
  classical
  unfold asymProdSphericalCode at hc
  rcases Finset.mem_map.1 hc with ⟨v, _hv, hvc⟩
  rcases mem_asymProdDirections.1 v.2 with ⟨x, hx, hxnorm⟩
  refine ⟨x, hx, ?_⟩
  have hval : v.1 = c.1 := by
    exact congrArg (fun p : SpherePoint n => p.1) hvc
  exact hxnorm.trans hval

/-- Normalized harmonic witness correlation against any nonzero raw product
tuple. -/
theorem inner_harmonicWitness_normalized_tuple_le_posCount
    {n : ℕ} (hn : 0 < n) {A : Finset ℝ} {x : Fin n → ℝ}
    (hx : x ∈ nonzeroAsymProductTuples n A) :
    inner ℝ (harmonicWitness n hn).1 (NormedSpace.normalize (tupleVector x)) ≤
      2 * Real.sqrt (posCount A : ℝ) / Real.sqrt (H n) := by
  have hxA : ∀ i, x i ∈ A := (mem_nonzeroAsymProductTuples.1 hx).1
  have hxne : tupleVector x ≠ 0 := (mem_nonzeroAsymProductTuples.1 hx).2
  have hHpos : 0 < H n := H_pos hn
  have hraw := inner_harmonicWeights_tupleVector_le_posCount (n := n) (A := A) (x := x) hxA
  have hscale_nonneg :
      0 ≤ ‖harmonicWeights n‖⁻¹ * ‖tupleVector x‖⁻¹ := by
    positivity
  have hinner :
      inner ℝ (harmonicWitness n hn).1 (NormedSpace.normalize (tupleVector x)) =
        (‖harmonicWeights n‖⁻¹ * ‖tupleVector x‖⁻¹) *
          inner ℝ (harmonicWeights n) (tupleVector x) := by
    simp [harmonicWitness, NormedSpace.normalize, real_inner_smul_left,
      real_inner_smul_right, mul_assoc, mul_comm]
  calc
    inner ℝ (harmonicWitness n hn).1 (NormedSpace.normalize (tupleVector x))
        = (‖harmonicWeights n‖⁻¹ * ‖tupleVector x‖⁻¹) *
          inner ℝ (harmonicWeights n) (tupleVector x) := hinner
    _ ≤ (‖harmonicWeights n‖⁻¹ * ‖tupleVector x‖⁻¹) *
          (2 * Real.sqrt (posCount A : ℝ) * ‖tupleVector x‖) := by
            exact mul_le_mul_of_nonneg_left hraw hscale_nonneg
    _ = 2 * Real.sqrt (posCount A : ℝ) / Real.sqrt (H n) := by
            rw [harmonicWeights_norm n]
            have hHsqrt_ne : Real.sqrt (H n) ≠ 0 := Real.sqrt_ne_zero'.mpr hHpos
            have hxnorm_ne : ‖tupleVector x‖ ≠ 0 := norm_ne_zero_iff.mpr hxne
            field_simp [hHsqrt_ne, hxnorm_ne]

/-- Product-code angular lower bound from the harmonic witness, with the
constant depending on the number of positive alphabet entries. -/
theorem arccos_posCount_bound_le_F_asym {n : ℕ} (hn : 0 < n) (A : Finset ℝ) :
    Real.arccos (2 * Real.sqrt (posCount A : ℝ) / Real.sqrt (H n)) ≤
      F_asym n A := by
  let u := harmonicWitness n hn
  let C := asymProdSphericalCode n A
  have hcode_angle (c : SpherePoint n) (hc : c ∈ C) :
      Real.arccos (2 * Real.sqrt (posCount A : ℝ) / Real.sqrt (H n)) ≤
        InnerProductGeometry.angle u.1 c.1 := by
    rcases exists_tuple_of_mem_asymProdSphericalCode (n := n) (A := A) hc with
      ⟨x, hx, hcval⟩
    have hinner :
        inner ℝ u.1 c.1 ≤
          2 * Real.sqrt (posCount A : ℝ) / Real.sqrt (H n) := by
      rw [← hcval]
      exact inner_harmonicWitness_normalized_tuple_le_posCount hn hx
    have hunorm : ‖u.1‖ = 1 := norm_spherePoint u
    have hcnorm : ‖c.1‖ = 1 := norm_spherePoint c
    have hangle :
        InnerProductGeometry.angle u.1 c.1 = Real.arccos (inner ℝ u.1 c.1) := by
      rw [InnerProductGeometry.angle, hunorm, hcnorm]
      norm_num
    rw [hangle]
    exact Real.arccos_le_arccos hinner
  have hmin :
      Real.arccos (2 * Real.sqrt (posCount A : ℝ) / Real.sqrt (H n)) ≤
        minAngleToSphericalCode C u := by
    unfold minAngleToSphericalCode
    split_ifs with hC
    · exact Finset.le_inf' hC _ hcode_angle
    · exact Real.arccos_le_pi _
  unfold F_asym covrad_sph
  exact le_trans hmin
    (le_csSup (bddAbove_range_minAngleToSphericalCode C) (Set.mem_range_self u))

/-- Uniform cardinality version of the harmonic product lower bound. -/
theorem arccos_card_bound_le_F_asym {n q : ℕ} (hn : 0 < n)
    {A : Finset ℝ} (hA : A.card = q) :
    Real.arccos (2 * Real.sqrt (q : ℝ) / Real.sqrt (H n)) ≤ F_asym n A := by
  have hbase := arccos_posCount_bound_le_F_asym hn A
  have hcount : (posCount A : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (hA ▸ posCount_le_card A)
  have hsqrt : Real.sqrt (posCount A : ℝ) ≤ Real.sqrt (q : ℝ) :=
    Real.sqrt_le_sqrt hcount
  have hden_nonneg : 0 ≤ (Real.sqrt (H n))⁻¹ := by
    positivity
  have harg :
      2 * Real.sqrt (posCount A : ℝ) / Real.sqrt (H n) ≤
        2 * Real.sqrt (q : ℝ) / Real.sqrt (H n) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) hden_nonneg
  exact le_trans (Real.arccos_le_arccos harg) hbase

end AsymmetricProduct
end OptimalAlphabets
