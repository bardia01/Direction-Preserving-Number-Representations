import PaperProofs.Definitions

/-!
# Product codes versus spherical codes

Paper-facing wrappers for the product-vs-spherical part of the paper.
-/

noncomputable section

open Set Filter Topology Real Metric

namespace PaperProofs

/-- Appendix Lemma 3: pointwise comparison with spherical codes. -/
theorem appendix_lemma3_pointwise_comparison (n : Nat) (A : Finset Real) :
    rhoSph n (Pdir n A).card <= F n A := by
  simpa [rhoSph, Pdir, F] using
    OptimalAlphabets.AsymmetricProduct.rho_sph_asymProdDirections_card_le_F_asym n A

/-- Appendix Lemma 4: antitonicity in the code size. -/
theorem appendix_lemma4_antitonicity_in_code_size
    {n m1 m2 : Nat} (hn : 2 <= n) (_hm1 : 1 <= m1) (hm12 : m1 <= m2) :
    rhoSph n m2 <= rhoSph n m1 := by
  simpa [rhoSph] using
    OptimalAlphabets.rho_sph_monotone_points hn hm12

/-- Product-code directions are monotone under scalar-alphabet enlargement. -/
theorem P_mono_of_subset {n : Nat} {A B : Finset Real} (hAB : A ⊆ B) :
    P n A ⊆ P n B := by
  classical
  intro c hc
  rcases OptimalAlphabets.AsymmetricProduct.exists_tuple_of_mem_asymProdSphericalCode
      (n := n) (A := A) hc with
    ⟨x, hx, hcval⟩
  have hxB :
      x ∈ OptimalAlphabets.AsymmetricProduct.nonzeroAsymProductTuples n B := by
    rw [OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples]
    exact ⟨fun i =>
        hAB ((OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1 hx).1 i),
      (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1 hx).2⟩
  unfold P OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode
  rw [Finset.mem_map]
  have hdir :
      NormedSpace.normalize (OptimalAlphabets.AsymmetricProduct.tupleVector x) ∈
        OptimalAlphabets.AsymmetricProduct.asymProdDirections n B := by
    rw [OptimalAlphabets.AsymmetricProduct.mem_asymProdDirections]
    exact ⟨x, hxB, rfl⟩
  refine ⟨⟨_, hdir⟩, Finset.mem_attach _ _, ?_⟩
  exact Subtype.ext hcval

/-- Enlarging the scalar alphabet can only decrease the product-code covering
objective. -/
theorem F_antitone_of_subset {n : Nat} (hn : 0 < n)
    {A B : Finset Real} (hAB : A ⊆ B) :
    F n B <= F n A := by
  unfold F OptimalAlphabets.AsymmetricProduct.F_asym
  exact OptimalAlphabets.covrad_sph_anti
    ⟨OptimalAlphabets.AsymmetricProduct.firstSpherePoint n hn⟩
    (P_mono_of_subset hAB)

theorem arccos_min_one (x : Real) :
    Real.arccos (min 1 x) = Real.arccos x := by
  by_cases hx : x <= 1
  · rw [min_eq_right hx]
  · have hxlt : 1 < x := lt_of_not_ge hx
    have hxone : 1 <= x := hxlt.le
    rw [min_eq_left hxone, Real.arccos_one, Real.arccos_of_one_le hxone]

/-- The positive count of the negated alphabet is the negative count of the
original alphabet. -/
theorem posCount_negatedAlphabet_eq_negCount (A : Finset Real) :
    OptimalAlphabets.AsymmetricProduct.posCount
        (A.map OptimalAlphabets.AsymmetricProduct.negEmbedding) =
      OptimalAlphabets.AsymmetricProduct.negCount A := by
  classical
  unfold OptimalAlphabets.AsymmetricProduct.posCount
    OptimalAlphabets.AsymmetricProduct.posPart
    OptimalAlphabets.AsymmetricProduct.negCount
    OptimalAlphabets.AsymmetricProduct.negPart
  rw [Finset.filter_map]
  simp [OptimalAlphabets.AsymmetricProduct.negEmbedding, Function.comp_def]

/-- Negating a nonzero product tuple sends it into the negated alphabet. -/
theorem negatedTuple_mem_nonzeroAsymProductTuples
    {n : Nat} {A : Finset Real} {x : Fin n -> Real}
    (hx : x ∈ OptimalAlphabets.AsymmetricProduct.nonzeroAsymProductTuples n A) :
    (fun i => -x i) ∈
      OptimalAlphabets.AsymmetricProduct.nonzeroAsymProductTuples n
        (A.map OptimalAlphabets.AsymmetricProduct.negEmbedding) := by
  classical
  rw [OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples]
  have hxmem : forall i, x i ∈ A :=
    (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1 hx).1
  have hxne : OptimalAlphabets.AsymmetricProduct.tupleVector x ≠ 0 :=
    (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1 hx).2
  constructor
  · intro i
    exact Finset.mem_map.2
      ⟨x i, hxmem i, by simp [OptimalAlphabets.AsymmetricProduct.negEmbedding]⟩
  · intro hzero
    apply hxne
    rw [OptimalAlphabets.AsymmetricProduct.tupleVector_eq_zero_iff]
    intro i
    have hi := congrArg
      (fun v : EuclideanSpace Real (Fin n) => v i) hzero
    have hneg : -x i = 0 := by
      simpa [OptimalAlphabets.AsymmetricProduct.tupleVector] using hi
    exact neg_eq_zero.mp hneg

/-- The antipodal harmonic witness used for the negative-count half of
Theorem 2. -/
def negHarmonicWitness (n : Nat) (hn : 0 < n) : OptimalAlphabets.SpherePoint n :=
  ⟨-(harmonicWitness n hn).1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    rw [norm_neg]
    exact OptimalAlphabets.AsymmetricProduct.norm_spherePoint (harmonicWitness n hn)⟩

/-- Normalized harmonic-witness correlation bound using negative alphabet
entries. -/
theorem inner_negHarmonicWitness_normalized_tuple_le_negCount
    {n : Nat} (hn : 0 < n) {A : Finset Real} {x : Fin n -> Real}
    (hx : x ∈ OptimalAlphabets.AsymmetricProduct.nonzeroAsymProductTuples n A) :
    inner Real (-(harmonicWitness n hn).1)
        (NormedSpace.normalize (OptimalAlphabets.AsymmetricProduct.tupleVector x)) <=
      2 * Real.sqrt (pNeg A : Real) / Real.sqrt (H n) := by
  let z : Fin n -> Real := fun i => -x i
  let negA : Finset Real := A.map OptimalAlphabets.AsymmetricProduct.negEmbedding
  have hz :
      z ∈ OptimalAlphabets.AsymmetricProduct.nonzeroAsymProductTuples n negA := by
    simpa [z, negA] using
      negatedTuple_mem_nonzeroAsymProductTuples (n := n) (A := A) (x := x) hx
  have hbase :=
    OptimalAlphabets.AsymmetricProduct.inner_harmonicWitness_normalized_tuple_le_posCount
      (n := n) (A := negA) (x := z) hn hz
  have hvec :
      OptimalAlphabets.AsymmetricProduct.tupleVector z =
        -OptimalAlphabets.AsymmetricProduct.tupleVector x := by
    ext i
    simp [z, OptimalAlphabets.AsymmetricProduct.tupleVector]
  have hnormalize :
      NormedSpace.normalize (OptimalAlphabets.AsymmetricProduct.tupleVector z) =
        -NormedSpace.normalize (OptimalAlphabets.AsymmetricProduct.tupleVector x) := by
    rw [hvec, NormedSpace.normalize_neg]
  calc
    inner Real (-(harmonicWitness n hn).1)
        (NormedSpace.normalize (OptimalAlphabets.AsymmetricProduct.tupleVector x))
        = inner Real (harmonicWitness n hn).1
            (NormedSpace.normalize (OptimalAlphabets.AsymmetricProduct.tupleVector z)) := by
          rw [hnormalize]
          simp
    _ <= 2 * Real.sqrt
          (OptimalAlphabets.AsymmetricProduct.posCount negA : Real) / Real.sqrt (H n) := by
          simpa [harmonicWitness, H] using hbase
    _ = 2 * Real.sqrt (pNeg A : Real) / Real.sqrt (H n) := by
          simp [negA, pNeg, H, posCount_negatedAlphabet_eq_negCount]

/-- Theorem 2, Lean-native positive-count form. -/
theorem theorem2_positive_count_bound {n : Nat} (hn : 0 < n) (A : Finset Real) :
    Real.arccos (2 * Real.sqrt (pPos A : Real) / Real.sqrt (H n)) <= F n A := by
  simpa [pPos, H, F] using
    OptimalAlphabets.AsymmetricProduct.arccos_posCount_bound_le_F_asym
      (n := n) hn A

/-- Theorem 2, Lean-native negative-count form. -/
theorem theorem2_negative_count_bound {n : Nat} (hn : 0 < n) (A : Finset Real) :
    Real.arccos (2 * Real.sqrt (pNeg A : Real) / Real.sqrt (H n)) <= F n A := by
  let u := negHarmonicWitness n hn
  let C := OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode n A
  have hcode_angle (c : OptimalAlphabets.SpherePoint n) (hc : c ∈ C) :
      Real.arccos (2 * Real.sqrt (pNeg A : Real) / Real.sqrt (H n)) <=
        InnerProductGeometry.angle u.1 c.1 := by
    rcases OptimalAlphabets.AsymmetricProduct.exists_tuple_of_mem_asymProdSphericalCode
        (n := n) (A := A) hc with
      ⟨x, hx, hcval⟩
    have hinner :
        inner Real u.1 c.1 <=
          2 * Real.sqrt (pNeg A : Real) / Real.sqrt (H n) := by
      rw [← hcval]
      change inner Real (-(harmonicWitness n hn).1)
          (NormedSpace.normalize (OptimalAlphabets.AsymmetricProduct.tupleVector x)) <=
        2 * Real.sqrt (pNeg A : Real) / Real.sqrt (H n)
      exact inner_negHarmonicWitness_normalized_tuple_le_negCount hn hx
    have hunorm : ‖u.1‖ = 1 :=
      OptimalAlphabets.AsymmetricProduct.norm_spherePoint u
    have hcnorm : ‖c.1‖ = 1 :=
      OptimalAlphabets.AsymmetricProduct.norm_spherePoint c
    have hangle :
        InnerProductGeometry.angle u.1 c.1 = Real.arccos (inner Real u.1 c.1) := by
      rw [InnerProductGeometry.angle, hunorm, hcnorm]
      norm_num
    rw [hangle]
    exact Real.arccos_le_arccos hinner
  have hmin :
      Real.arccos (2 * Real.sqrt (pNeg A : Real) / Real.sqrt (H n)) <=
        OptimalAlphabets.minAngleToSphericalCode C u := by
    unfold OptimalAlphabets.minAngleToSphericalCode
    split_ifs with hC
    · exact Finset.le_inf' hC _ hcode_angle
    · exact Real.arccos_le_pi _
  unfold F OptimalAlphabets.AsymmetricProduct.F_asym OptimalAlphabets.covrad_sph
  exact le_trans hmin
    (le_csSup (OptimalAlphabets.bddAbove_range_minAngleToSphericalCode C)
      (Set.mem_range_self u))

/-- Cardinality arccos lower bound for the best value `w_{n,q}`. -/
theorem arccos_card_bound_le_w {n q : Nat} (hn : 0 < n) :
    Real.arccos (2 * Real.sqrt (q : Real) / Real.sqrt (H n)) <= w n q := by
  unfold w
  refine le_csInf ?_ ?_
  · refine ⟨F n (OptimalAlphabets.AsymmetricProduct.canonicalRealFinset q), ?_⟩
    refine ⟨OptimalAlphabets.AsymmetricProduct.canonicalRealFinset q, ?_, rfl⟩
    simp [Aq]
  · rintro y ⟨A, hA, rfl⟩
    simpa [Aq, H, F] using
      OptimalAlphabets.AsymmetricProduct.arccos_card_bound_le_F_asym
        (n := n) (q := q) hn (A := A) hA

/-- Exact printed statement of Theorem 2. -/
theorem theorem2_sign_count_bound {n : Nat} (hn : 2 <= n) (A : Finset Real) :
    Real.arccos (min 1 (2 * Real.sqrt (mSign A : Real) / Real.sqrt (H n))) <=
      F n A := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn
  by_cases hle : pPos A <= pNeg A
  · have hm : mSign A = pPos A := by
      simp [mSign, pPos, OptimalAlphabets.AsymmetricProduct.signMinCount,
        min_eq_left hle]
    rw [hm, arccos_min_one]
    exact theorem2_positive_count_bound hnpos A
  · have hle' : pNeg A <= pPos A := le_of_lt (lt_of_not_ge hle)
    have hm : mSign A = pNeg A := by
      simp [mSign, pNeg, OptimalAlphabets.AsymmetricProduct.signMinCount,
        min_eq_right hle']
    rw [hm, arccos_min_one]
    exact theorem2_negative_count_bound hnpos A

/-- Exact printed floor/sign-count statement of Corollary 1. -/
theorem corollary1_uniform_q_element_consequence
    {n q : Nat} (hn : 2 <= n) (_hq : 2 <= q)
    {A : Finset Real} (hA : A ∈ Aq q) :
    Real.arccos
        (min 1 (2 * Real.sqrt ((q / 2 : Nat) : Real) / Real.sqrt (H n))) <=
      F n A := by
  have hcard : A.card = q := by
    simpa [Aq] using hA
  have hmle : mSign A <= q / 2 := by
    have hbase :=
      OptimalAlphabets.AsymmetricProduct.signMinCount_le_card_div_two A
    simpa [mSign, hcard] using hbase
  have hcount : (mSign A : Real) <= ((q / 2 : Nat) : Real) := by
    exact_mod_cast hmle
  have hsqrt :
      Real.sqrt (mSign A : Real) <=
        Real.sqrt ((q / 2 : Nat) : Real) :=
    Real.sqrt_le_sqrt hcount
  have hden_nonneg : 0 <= (Real.sqrt (H n))⁻¹ := by
    positivity
  have harg :
      2 * Real.sqrt (mSign A : Real) / Real.sqrt (H n) <=
        2 * Real.sqrt ((q / 2 : Nat) : Real) / Real.sqrt (H n) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) hden_nonneg
  have hmin :
      min 1 (2 * Real.sqrt (mSign A : Real) / Real.sqrt (H n)) <=
        min 1 (2 * Real.sqrt ((q / 2 : Nat) : Real) / Real.sqrt (H n)) :=
    min_le_min le_rfl harg
  exact le_trans (Real.arccos_le_arccos hmin)
    (theorem2_sign_count_bound (n := n) hn A)

/-- Corollary 2: exponential spherical upper bound, formalized in the threshold
form needed downstream. -/
theorem corollary2_exponential_spherical_upper_bound
    {lambda theta : Real}
    (hlambda : 1 < lambda) (htheta0 : 0 < theta)
    (htheta_pi2 : theta < Real.pi / 2)
    (hmul : 1 < lambda * Real.sin theta) :
    ∃ N : Nat, forall n, N <= n -> rhoSph n (Nat.floor (lambda ^ n)) <= theta := by
  simpa [rhoSph, OptimalAlphabets.EventualSphericalUpperBoundAt] using
    OptimalAlphabets.eventualSphericalUpperBoundAt_of_mul_sin_gt_one
      (lam := lambda) (theta := theta) hlambda htheta0 htheta_pi2 hmul

/-- Theorem 4: asymptotic strict separation for fixed alphabet size. -/
theorem theorem4_asymptotic_strict_separation_fixed_alphabet_size
    {q : Nat} (hq : 2 <= q) :
    ∃ N : Nat, 2 <= N ∧ forall n, N <= n -> forall A : Finset Real,
      A ∈ Aq q -> rhoSph n (q ^ n) < F n A := by
  simpa [Aq, rhoSph, F] using
    OptimalAlphabets.AsymmetricProduct.eventually_rho_sph_pow_lt_F_asym
      (q := q) hq

/-- Printed `w_{n,q}` consequence of Theorem 4. -/
theorem theorem4_best_value_consequence
    {q : Nat} (hq : 2 <= q) :
    ∃ N : Nat, 2 <= N ∧ forall n, N <= n -> rhoSph n (q ^ n) < w n q := by
  rcases OptimalAlphabets.AsymmetricProduct.exists_theta_for_bit_budget
      (q := q) hq with
    ⟨theta, _htheta_gt, htheta0, htheta_pi2, hmul⟩
  rcases OptimalAlphabets.AsymmetricProduct.eventual_rho_sph_pow_le_of_mul_sin_gt_one
      (q := q) hq htheta0 htheta_pi2 hmul with
    ⟨N₁, hN₁⟩
  let B : Real := (2 * Real.sqrt (q : Real) / Real.cos theta) ^ 2
  rcases OptimalAlphabets.AsymmetricProduct.eventually_H_gt B with ⟨N₂, hN₂⟩
  refine ⟨max (max N₁ N₂) 2, le_max_right _ _, ?_⟩
  intro n hn
  have hN₁n : N₁ <= n := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hN₂n : N₂ <= n := by
    exact le_trans (le_max_right N₁ N₂) (le_trans (le_max_left _ _) hn)
  have h2n : 2 <= n := le_trans (le_max_right (max N₁ N₂) 2) hn
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) h2n
  have hH :
      (2 * Real.sqrt (q : Real) / Real.cos theta) ^ 2 < H n := by
    simpa [B, H] using hN₂ n hN₂n
  have hrho_le_theta : rhoSph n (q ^ n) <= theta := by
    simpa [rhoSph] using hN₁ n hN₁n
  have htheta_lt_arccos :
      theta <
        Real.arccos (2 * Real.sqrt (q : Real) / Real.sqrt (H n)) := by
    simpa [H] using
      OptimalAlphabets.AsymmetricProduct.theta_lt_arccos_card_bound_of_H_gt
        (q := q) (n := n) (theta := theta) htheta0 htheta_pi2 hH
  exact lt_of_le_of_lt hrho_le_theta
    (lt_of_lt_of_le htheta_lt_arccos (arccos_card_bound_le_w (n := n) (q := q) hnpos))

end PaperProofs
