import PaperProofs.ProductVsSpherical
import PaperProofs.NearestQuantization
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Standard-format separation

Paper-facing wrappers for the normalized product-code comparison between
canonical floating-point alphabets and arbitrary alphabets.
-/

noncomputable section

open Set Filter Topology Real Metric
open scoped BigOperators

namespace PaperProofs

/-- Lemma 2: fixed sign-symmetric alphabets, theorem-backed layer-cake form. -/
theorem lemma2_fixed_sign_symmetric_alphabets
    {n m : Nat} (hn : 0 < n) (hm : 1 <= m)
    {c : Fin m -> Real}
    (hpos : forall j, 0 < c j)
    (hdesc : forall {i j : Fin m}, i < j -> c j < c i) :
    Real.sqrt (H n) *
        alpha n (OptimalAlphabets.AsymmetricProduct.signedLevelsOfSeq c) <=
      OptimalAlphabets.AsymmetricProduct.layerCakeConstant c := by
  simpa [H, alpha] using
    OptimalAlphabets.AsymmetricProduct.signSymmetricLayerCake_obstruction
      (n := n) (m := m) hn hm (c := c) hpos hdesc

/-- Corollary 3: floating-point normalized obstruction, finite-n theorem-backed
form stronger than the printed limsup statement. -/
theorem corollary3_floating_point_normalized_obstruction
    {n b : Nat} (hn : 0 < n) (hb : 2 <= b) :
    normBestFpCos n b <= fpConst b := by
  simpa [normBestFpCos, fpConst] using
    OptimalAlphabets.AsymmetricProduct.normBestFpCos_le_fpConst
      (n := n) (b := b) hn hb

/-- A signed positive scalar alphabet has nonnegative worst-case correlation:
for every witness, choose the scalar signs coordinatewise. -/
theorem alpha_fpAlphabet_nonneg
    {n e t : Nat} (hn : 0 < n) (he : 1 <= e) :
    0 <= alpha n (Phi e t) := by
  let hcard : 0 < OptimalAlphabets.floatPositiveCard e t := by
    simp [OptimalAlphabets.floatPositiveCard]
    have hpow : 2 <= 2 ^ (e + t) := by
      have hmono : 2 ^ 1 <= 2 ^ (e + t) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
      simpa using hmono
    omega
  let a : Real :=
    OptimalAlphabets.floatingPositiveLevels e t ⟨0, hcard⟩
  have ha_pos : 0 < a := by
    dsimp [a]
    exact OptimalAlphabets.floatingPositiveLevels_pos e t ⟨0, hcard⟩
  have ha_mem : a ∈ OptimalAlphabets.AsymmetricProduct.fpPositiveFinset e t := by
    dsimp [a]
    exact Finset.mem_map.2 ⟨⟨0, hcard⟩, by simp, rfl⟩
  refine
    OptimalAlphabets.AsymmetricProduct.le_alpha_asym_of_forall_exists_tuple
      (n := n) hn ?_
  intro u
  let x : Fin n -> Real := fun i => if 0 <= u.1 i then a else -a
  have hxmem : forall i, x i ∈ Phi e t := by
    intro i
    rw [Phi, OptimalAlphabets.AsymmetricProduct.fpAlphabet,
      OptimalAlphabets.AsymmetricProduct.mem_signedFinset]
    by_cases hi : 0 <= u.1 i
    · exact Or.inr (Or.inl (by simpa [x, hi] using ha_mem))
    · exact Or.inr (Or.inr (by simpa [x, hi] using ha_mem))
  have hxne : OptimalAlphabets.AsymmetricProduct.tupleVector x ≠ 0 := by
    rw [OptimalAlphabets.AsymmetricProduct.tupleVector_ne_zero_iff]
    refine ⟨⟨0, hn⟩, ?_⟩
    by_cases h0 : 0 <= u.1 ⟨0, hn⟩
    · simpa [x, h0] using ha_pos.ne'
    · simpa [x, h0] using (neg_ne_zero.mpr ha_pos.ne')
  have hinner_nonneg :
      0 <= inner Real u.1 (OptimalAlphabets.AsymmetricProduct.tupleVector x) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_nonneg ?_
    intro i _hi
    by_cases hi : 0 <= u.1 i
    · simpa [OptimalAlphabets.AsymmetricProduct.tupleVector, x, hi, mul_comm] using
        mul_nonneg ha_pos.le hi
    · have hui : u.1 i <= 0 := le_of_not_ge hi
      simpa [OptimalAlphabets.AsymmetricProduct.tupleVector, x, hi, mul_comm] using
        mul_nonpos_of_nonneg_of_nonpos ha_pos.le hui
  refine ⟨x,
    OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.2
      ⟨hxmem, hxne⟩, ?_⟩
  unfold OptimalAlphabets.AsymmetricProduct.tupleCorr
  exact div_nonneg hinner_nonneg (norm_nonneg _)

/-- Floating-point optimized normalized cosine is nonnegative for valid
bit-widths. -/
theorem normBestFpCos_nonneg
    {n b : Nat} (hn : 0 < n) (hb : 2 <= b) :
    0 <= normBestFpCos n b := by
  have hsplit : (OptimalAlphabets.AsymmetricProduct.fpSplitIndices b).Nonempty :=
    OptimalAlphabets.AsymmetricProduct.fpSplitIndices_nonempty hb
  let t₀ : Nat := Classical.choose hsplit
  have ht₀ : t₀ ∈ OptimalAlphabets.AsymmetricProduct.fpSplitIndices b :=
    Classical.choose_spec hsplit
  have he₀ : 1 <= OptimalAlphabets.AsymmetricProduct.fpExponentBits b t₀ :=
    OptimalAlphabets.AsymmetricProduct.fpExponentBits_pos hb ht₀
  have halpha :
      0 <=
        alpha n (Phi (OptimalAlphabets.AsymmetricProduct.fpExponentBits b t₀) t₀) :=
    alpha_fpAlphabet_nonneg (n := n) (e := OptimalAlphabets.AsymmetricProduct.fpExponentBits b t₀)
      (t := t₀) hn he₀
  have hbest : 0 <= bestFpCos n b := by
    unfold bestFpCos OptimalAlphabets.AsymmetricProduct.bestFpCos
    rw [dif_pos hsplit]
    exact le_trans halpha
      (Finset.le_sup' (s := OptimalAlphabets.AsymmetricProduct.fpSplitIndices b)
        (f := fun t =>
          OptimalAlphabets.AsymmetricProduct.alpha_asym n
            (OptimalAlphabets.AsymmetricProduct.fpAlphabet
              (OptimalAlphabets.AsymmetricProduct.fpExponentBits b t) t))
        ht₀)
  unfold normBestFpCos OptimalAlphabets.AsymmetricProduct.normBestFpCos
  exact mul_nonneg (Real.sqrt_nonneg _) hbest

/-- Corollary 4: arbitrary alphabets, theorem-backed eventual epsilon form. -/
theorem corollary4_arbitrary_alphabets_eventual
    {b : Nat} (hb : 2 <= b) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : Nat in atTop,
      arbConst b - epsilon <= normBestAlpha n (2 ^ b) := by
  simpa [arbConst, normBestAlpha] using
    OptimalAlphabets.AsymmetricProduct.normBestAsymCos_ge_arbConst_sub_eps_of_blockHardy
      OptimalAlphabets.AsymmetricProduct.blockHardy_lower
      (b := b) hb (ε := epsilon) hepsilon

/-- Harmonic-witness upper bound for the arbitrary-alphabet normalized
objective at fixed cardinality. -/
theorem normBestAlpha_le_card_const
    {n q : Nat} (hn : 0 < n) :
    normBestAlpha n q <= 2 * Real.sqrt (q : Real) := by
  have hHpos : 0 < H n :=
    OptimalAlphabets.AsymmetricProduct.H_pos hn
  have hsqrtH_pos : 0 < Real.sqrt (H n) :=
    Real.sqrt_pos_of_pos hHpos
  have hbest :
      OptimalAlphabets.AsymmetricProduct.bestAsymCos n q <=
        2 * Real.sqrt (q : Real) / Real.sqrt (H n) := by
    unfold OptimalAlphabets.AsymmetricProduct.bestAsymCos
    refine csSup_le ?_ ?_
    · refine ⟨OptimalAlphabets.AsymmetricProduct.alpha_asym n
          (OptimalAlphabets.AsymmetricProduct.canonicalRealFinset q), ?_⟩
      exact ⟨OptimalAlphabets.AsymmetricProduct.canonicalRealFinset q,
        OptimalAlphabets.AsymmetricProduct.canonicalRealFinset_card q, rfl⟩
    · rintro y ⟨A, hA, rfl⟩
      have hC : -1 <= 2 * Real.sqrt (q : Real) / Real.sqrt (H n) := by
        have hnonneg :
            0 <= 2 * Real.sqrt (q : Real) / Real.sqrt (H n) := by
          exact div_nonneg
            (mul_nonneg (by norm_num : (0 : Real) <= 2) (Real.sqrt_nonneg _))
            hsqrtH_pos.le
        linarith
      have hmax :
          OptimalAlphabets.AsymmetricProduct.maxCorr_asym n A (harmonicWitness n hn) <=
            2 * Real.sqrt (q : Real) / Real.sqrt (H n) := by
        refine OptimalAlphabets.AsymmetricProduct.maxCorr_asym_le_of_forall
          (n := n) (A := A) (u := harmonicWitness n hn) hC ?_
        intro x hx
        have hraw :=
          OptimalAlphabets.AsymmetricProduct.inner_harmonicWitness_normalized_tuple_le_posCount
            (n := n) (A := A) (x := x) hn hx
        have hcorr :
            OptimalAlphabets.AsymmetricProduct.tupleCorr (harmonicWitness n hn) x =
              inner Real (harmonicWitness n hn).1
                (NormedSpace.normalize (OptimalAlphabets.AsymmetricProduct.tupleVector x)) := by
          unfold OptimalAlphabets.AsymmetricProduct.tupleCorr NormedSpace.normalize
          simp [real_inner_smul_right, div_eq_mul_inv, mul_comm]
        have hcount : (OptimalAlphabets.AsymmetricProduct.posCount A : Real) <= (q : Real) := by
          exact_mod_cast (hA ▸ OptimalAlphabets.AsymmetricProduct.posCount_le_card A)
        have hsqrt :
            Real.sqrt (OptimalAlphabets.AsymmetricProduct.posCount A : Real) <=
              Real.sqrt (q : Real) :=
          Real.sqrt_le_sqrt hcount
        have hden_nonneg : 0 <= (Real.sqrt (H n))⁻¹ := by
          positivity
        have harg :
            2 * Real.sqrt (OptimalAlphabets.AsymmetricProduct.posCount A : Real) /
                Real.sqrt (H n) <=
              2 * Real.sqrt (q : Real) / Real.sqrt (H n) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) hden_nonneg
        exact le_trans (by simpa [← hcorr, H] using hraw) harg
      exact le_trans
        (OptimalAlphabets.AsymmetricProduct.alpha_asym_le_maxCorr A (harmonicWitness n hn))
        hmax
  unfold normBestAlpha OptimalAlphabets.AsymmetricProduct.normBestAsymCos
  calc
    Real.sqrt (OptimalAlphabets.AsymmetricProduct.H n) *
        OptimalAlphabets.AsymmetricProduct.bestAsymCos n q
        <= Real.sqrt (H n) *
            (2 * Real.sqrt (q : Real) / Real.sqrt (H n)) := by
          exact mul_le_mul_of_nonneg_left hbest (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (q : Real) := by
          field_simp [H, hsqrtH_pos.ne']

/-- Theorem 5: superiority of arbitrary alphabets, theorem-backed eventual
normalized-cosine form. -/
theorem theorem5_superiority_of_arbitrary_alphabets
    {b : Nat} (hb : 3 <= b) :
    ∀ᶠ n : Nat in atTop,
      normBestFpCos n b < normBestAlpha n (2 ^ b) := by
  simpa [normBestFpCos, normBestAlpha] using
    OptimalAlphabets.AsymmetricProduct.eventually_normBestFpCos_lt_normBestAsymCos
      (b := b) hb

/-- Corollary 3, literal limsup form. -/
theorem corollary3_limsup
    {b : Nat} (hb : 2 <= b) :
    Filter.limsup (fun n : Nat => normBestFpCos n b) atTop <= fpConst b := by
  refine Filter.limsup_le_of_le ?_ ?_
  · exact Filter.isCoboundedUnder_le_of_eventually_le atTop
      (Filter.eventually_atTop.2 ⟨1, fun n hn =>
        normBestFpCos_nonneg (n := n) (b := b) (Nat.succ_le_iff.mp hn) hb⟩)
  · exact (Filter.eventually_atTop.2 ⟨1, fun n hn =>
      corollary3_floating_point_normalized_obstruction
        (n := n) (b := b) (Nat.succ_le_iff.mp hn) hb⟩)

/-- Corollary 4, literal liminf form. -/
theorem corollary4_liminf
    {b : Nat} (hb : 2 <= b) :
    arbConst b <=
      Filter.liminf (fun n : Nat => normBestAlpha n (2 ^ b)) atTop := by
  let u : Nat -> Real := fun n => normBestAlpha n (2 ^ b)
  have hbdd : atTop.IsBoundedUnder (· ≥ ·) u := by
    exact Filter.isBoundedUnder_of_eventually_ge
      (corollary4_arbitrary_alphabets_eventual
        (b := b) hb (epsilon := 1) (by norm_num))
  have hcobdd : atTop.IsCoboundedUnder (· ≥ ·) u := by
    exact Filter.isCoboundedUnder_ge_of_eventually_le atTop
      (Filter.eventually_atTop.2 ⟨1, fun n hn =>
        normBestAlpha_le_card_const (n := n) (q := 2 ^ b)
          (Nat.succ_le_iff.mp hn)⟩)
  rw [Filter.le_liminf_iff hcobdd hbdd]
  intro y hy
  let epsilon : Real := (arbConst b - y) / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hylt : y < arbConst b - epsilon := by
    dsimp [epsilon]
    linarith
  filter_upwards
    [corollary4_arbitrary_alphabets_eventual (b := b) hb
      (epsilon := epsilon) hepsilon] with n hn
  exact lt_of_lt_of_le hylt hn

/-- Closed-form constant gap used by Theorem 5. -/
theorem fpConst_lt_arbConst {b : Nat} (hb : 3 <= b) :
    fpConst b < arbConst b := by
  simpa [fpConst, arbConst] using
    OptimalAlphabets.AsymmetricProduct.fpConst_lt_arbConst (b := b) hb

/-- Appendix Lemma 14: consecutive floating-point ratios. -/
theorem appendix_lemma14_consecutive_floating_point_ratios
    (e t : Nat) {j : Nat} (hj : j + 1 < OptimalAlphabets.floatPositiveCard e t) :
    OptimalAlphabets.floatingPositiveLevels e t ⟨j + 1, hj⟩ <=
      2 * OptimalAlphabets.floatingPositiveLevels e t
        ⟨j, Nat.lt_of_succ_lt hj⟩ := by
  simpa using
    OptimalAlphabets.AsymmetricProduct.fp_consecutive_ratio_le_two
      (e := e) (t := t) (j := j) hj

/-- Appendix Lemma 15: m-level cosine lower bound, theorem-backed block-Hardy
form. -/
theorem appendix_lemma15_m_level_cosine_lower_bound :
    OptimalAlphabets.AsymmetricProduct.BlockHardyLowerBound :=
  OptimalAlphabets.AsymmetricProduct.blockHardy_lower

/-- Product-code covering radii are nonnegative. -/
theorem F_nonneg (n : Nat) (A : Finset Real) :
    0 <= F n A := by
  simpa [F] using
    OptimalAlphabets.covrad_sph_nonneg
      (OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode n A)

/-- A product code over an alphabet with both signs has a codeword within
angle `pi/2` of every sphere point. -/
theorem minAngleToSphericalCode_le_pi_div_two_of_pos_neg
    {n : Nat} (hn : 0 < n) {A : Finset Real}
    (hpos : ∃ a : Real, a ∈ A ∧ 0 < a)
    (hneg : ∃ a : Real, a ∈ A ∧ a < 0)
    (u : OptimalAlphabets.SpherePoint n) :
    OptimalAlphabets.minAngleToSphericalCode (P n A) u <= Real.pi / 2 := by
  rcases hpos with ⟨ap, hap_mem, hap_pos⟩
  rcases hneg with ⟨an, han_mem, han_neg⟩
  let x : Fin n -> Real := fun i => if 0 <= u.1 i then ap else an
  have hxmem : forall i, x i ∈ A := by
    intro i
    by_cases hi : 0 <= u.1 i
    · simpa [x, hi] using hap_mem
    · simpa [x, hi] using han_mem
  have hxne : OptimalAlphabets.AsymmetricProduct.tupleVector x ≠ 0 := by
    rw [OptimalAlphabets.AsymmetricProduct.tupleVector_ne_zero_iff]
    refine ⟨⟨0, hn⟩, ?_⟩
    by_cases hi : 0 <= u.1 ⟨0, hn⟩
    · simpa [x, hi] using hap_pos.ne'
    · simpa [x, hi] using (ne_of_lt han_neg)
  have hx :
      x ∈ OptimalAlphabets.AsymmetricProduct.nonzeroAsymProductTuples n A := by
    exact OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.2
      ⟨hxmem, hxne⟩
  let v : EuclideanSpace Real (Fin n) :=
    NormedSpace.normalize (OptimalAlphabets.AsymmetricProduct.tupleVector x)
  have hvdir : v ∈ OptimalAlphabets.AsymmetricProduct.asymProdDirections n A := by
    rw [OptimalAlphabets.AsymmetricProduct.mem_asymProdDirections]
    exact ⟨x, hx, rfl⟩
  let c : OptimalAlphabets.SpherePoint n :=
    ⟨v, OptimalAlphabets.AsymmetricProduct.mem_sphere_of_mem_asymProdDirections hvdir⟩
  have hc : c ∈ P n A := by
    unfold P OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode
    refine Finset.mem_map.2 ?_
    refine ⟨⟨v, hvdir⟩, by simp, ?_⟩
    exact Subtype.ext rfl
  have hinner_raw :
      0 <= inner Real u.1 (OptimalAlphabets.AsymmetricProduct.tupleVector x) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_nonneg ?_
    intro i _hi
    by_cases hi : 0 <= u.1 i
    · simpa [OptimalAlphabets.AsymmetricProduct.tupleVector, x, hi, mul_comm] using
        mul_nonneg hap_pos.le hi
    · have hui : u.1 i <= 0 := le_of_not_ge hi
      have han_nonpos : an <= 0 := han_neg.le
      simpa [OptimalAlphabets.AsymmetricProduct.tupleVector, x, hi, mul_comm] using
        mul_nonneg_of_nonpos_of_nonpos hui han_nonpos
  have hinner_c : 0 <= inner Real u.1 c.1 := by
    have hscale : 0 <= ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖⁻¹ := by
      positivity
    have hmul := mul_nonneg hscale hinner_raw
    simpa [c, v, NormedSpace.normalize, real_inner_smul_right] using hmul
  have hangle : InnerProductGeometry.angle u.1 c.1 <= Real.pi / 2 := by
    rw [InnerProductGeometry.angle, Real.arccos_le_pi_div_two]
    exact div_nonneg hinner_c
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  unfold OptimalAlphabets.minAngleToSphericalCode
  split_ifs with hC
  · exact le_trans (Finset.inf'_le _ hc) hangle
  · exact False.elim (hC ⟨c, hc⟩)

/-- Appendix Lemma 11, upper-bound half: if the scalar alphabet contains both
signs, then the product code has covering radius at most `pi/2` in every
positive dimension. -/
theorem appendix_lemma11_product_code_coverage_upper_bound
    {n : Nat} (hn : 0 < n) {A : Finset Real}
    (hpos : ∃ a : Real, a ∈ A ∧ 0 < a)
    (hneg : ∃ a : Real, a ∈ A ∧ a < 0) :
    F n A <= Real.pi / 2 := by
  unfold F OptimalAlphabets.AsymmetricProduct.F_asym OptimalAlphabets.covrad_sph
  refine csSup_le ?_ ?_
  · refine ⟨OptimalAlphabets.minAngleToSphericalCode
        (OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode n A)
        (OptimalAlphabets.AsymmetricProduct.firstSpherePoint n hn), ?_⟩
    exact Set.mem_range_self _
  · rintro theta ⟨u, rfl⟩
    exact minAngleToSphericalCode_le_pi_div_two_of_pos_neg
      (n := n) hn (A := A) hpos hneg u

/-- Two sign witnesses force the scalar alphabet to have cardinality at least
two. -/
theorem two_le_card_of_pos_neg {A : Finset Real}
    (hpos : ∃ a : Real, a ∈ A ∧ 0 < a)
    (hneg : ∃ a : Real, a ∈ A ∧ a < 0) :
    2 <= A.card := by
  rcases hpos with ⟨ap, hap_mem, hap_pos⟩
  rcases hneg with ⟨an, han_mem, han_neg⟩
  have hne : ap ≠ an := by
    intro h
    subst an
    linarith
  have hne' : an ≠ ap := hne.symm
  have hsubset : ({ap, an} : Finset Real) ⊆ A := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hap_mem
    · exact han_mem
  have hcard := Finset.card_le_card hsubset
  have hpair : ({ap, an} : Finset Real).card = 2 := by
    simp [hne]
  omega

/-- Appendix Lemma 11, lower-bound half in liminf form. -/
theorem appendix_lemma11_product_code_coverage_liminf_lower_bound
    {A : Finset Real}
    (hpos : ∃ a : Real, a ∈ A ∧ 0 < a)
    (hneg : ∃ a : Real, a ∈ A ∧ a < 0) :
    Real.pi / 2 <= Filter.liminf (fun n : Nat => F n A) atTop := by
  have hq : 2 <= A.card := two_le_card_of_pos_neg hpos hneg
  have hbdd : atTop.IsBoundedUnder (· ≥ ·) (fun n : Nat => F n A) := by
    exact Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun n => F_nonneg n A)
  have hcobdd : atTop.IsCoboundedUnder (· ≥ ·) (fun n : Nat => F n A) := by
    exact Filter.isCoboundedUnder_ge_of_eventually_le atTop
      (Filter.eventually_atTop.2 ⟨1, fun n hn =>
        appendix_lemma11_product_code_coverage_upper_bound
          (n := n) (Nat.succ_le_iff.mp hn) (A := A) hpos hneg⟩)
  rw [Filter.le_liminf_iff' hcobdd hbdd]
  intro y hy
  by_cases hy_nonpos : y <= 0
  · exact Filter.Eventually.of_forall fun n =>
      le_trans hy_nonpos (F_nonneg n A)
  · have hy_pos : 0 < y := lt_of_not_ge hy_nonpos
    have hy_pi : y <= Real.pi := by
      linarith [Real.pi_pos]
    have hcos_pos : 0 < Real.cos y := by
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hy⟩
    have hratio :
        Tendsto
          (fun n : Nat =>
            2 * Real.sqrt ((A.card / 2 : Nat) : Real) / Real.sqrt (H n))
          atTop (nhds 0) := by
      have hden :
          Tendsto (fun n : Nat => Real.sqrt (H n)) atTop atTop := by
        simpa [H] using
          Real.tendsto_sqrt_atTop.comp
            OptimalAlphabets.AsymmetricProduct.H_tendsto_atTop
      exact tendsto_const_nhds.div_atTop hden
    filter_upwards
      [hratio.eventually (Iio_mem_nhds hcos_pos),
        Filter.eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hsmall hn
    have harg :
        min 1
            (2 * Real.sqrt ((A.card / 2 : Nat) : Real) / Real.sqrt (H n))
          <= Real.cos y :=
      le_trans (min_le_right _ _) hsmall.le
    have hy_arccos :
        y <= Real.arccos
          (min 1
            (2 * Real.sqrt ((A.card / 2 : Nat) : Real) / Real.sqrt (H n))) := by
      rw [← Real.arccos_cos hy_pos.le hy_pi]
      exact Real.arccos_le_arccos harg
    exact le_trans hy_arccos
      (corollary1_uniform_q_element_consequence
        (n := n) (q := A.card) hn hq (A := A) (by simp [Aq]))

/-- Appendix Lemma 11, upper-bound half in limsup form. -/
theorem appendix_lemma11_product_code_coverage_limsup_upper_bound
    {A : Finset Real}
    (hpos : ∃ a : Real, a ∈ A ∧ 0 < a)
    (hneg : ∃ a : Real, a ∈ A ∧ a < 0) :
    Filter.limsup (fun n : Nat => F n A) atTop <= Real.pi / 2 := by
  refine Filter.limsup_le_of_le ?_ ?_
  · exact Filter.isCoboundedUnder_le_of_eventually_le atTop
      (Filter.Eventually.of_forall fun n => F_nonneg n A)
  · exact Filter.eventually_atTop.2 ⟨1, fun n hn =>
      appendix_lemma11_product_code_coverage_upper_bound
        (n := n) (Nat.succ_le_iff.mp hn) (A := A) hpos hneg⟩

/-- Lemma 11: product-code coverage in the limit. -/
def appendix_lemma11_product_code_coverage_in_limit_statement : Prop :=
  forall A : Finset Real,
    (∃ a : Real, a ∈ A ∧ 0 < a) ->
    (∃ a : Real, a ∈ A ∧ a < 0) ->
    Tendsto (fun n : Nat => F n A) atTop (nhds (Real.pi / 2))

/-- Appendix Lemma 11, literal theorem-backed statement. -/
theorem appendix_lemma11_product_code_coverage_in_limit :
    appendix_lemma11_product_code_coverage_in_limit_statement := by
  intro A hpos hneg
  have hupper_eventually :
      ∀ᶠ n : Nat in atTop, F n A <= Real.pi / 2 :=
    Filter.eventually_atTop.2 ⟨1, fun n hn =>
      appendix_lemma11_product_code_coverage_upper_bound
        (n := n) (Nat.succ_le_iff.mp hn) (A := A) hpos hneg⟩
  have hlower_eventually :
      ∀ᶠ n : Nat in atTop, 0 <= F n A :=
    Filter.Eventually.of_forall fun n => F_nonneg n A
  have hbdd_le :
      atTop.IsBoundedUnder (· <= ·) (fun n : Nat => F n A) :=
    Filter.isBoundedUnder_of_eventually_le hupper_eventually
  have hbdd_ge :
      atTop.IsBoundedUnder (· >= ·) (fun n : Nat => F n A) :=
    Filter.isBoundedUnder_of_eventually_ge hlower_eventually
  exact tendsto_of_le_liminf_of_limsup_le
    (appendix_lemma11_product_code_coverage_liminf_lower_bound
      (A := A) hpos hneg)
    (appendix_lemma11_product_code_coverage_limsup_upper_bound
      (A := A) hpos hneg)
    hbdd_le hbdd_ge
/-- Appendix Lemma 12, easy monotonic half: adding a scalar cannot worsen the
product-code covering radius. -/
theorem appendix_lemma12_unmatched_scalar_easy_direction
    {n : Nat} (hn : 0 < n) (B : Finset Real) (a : Real) :
    F n (insert a B) <= F n B := by
  exact F_antitone_of_subset hn (A := B) (B := insert a B)
    (by intro x hx; exact Finset.mem_insert_of_mem hx)
/-- A nontrivial negation-closed alphabet containing zero has both signs.
This is the sign-existence part of Appendix Lemma 12's hypotheses. -/
theorem exists_pos_neg_of_zero_negClosed_ne_singleton
    {B : Finset Real}
    (hzero : (0 : Real) ∈ B)
    (hnegClosed : forall x : Real, x ∈ B -> -x ∈ B)
    (hne : B ≠ ({0} : Finset Real)) :
    (∃ b : Real, b ∈ B ∧ 0 < b) ∧
      (∃ b : Real, b ∈ B ∧ b < 0) := by
  classical
  have hnonzero : ∃ b : Real, b ∈ B ∧ b ≠ 0 := by
    by_contra hnone
    apply hne
    ext x
    constructor
    · intro hx
      have hxzero : x = 0 := by
        by_contra hxne
        exact hnone ⟨x, hx, hxne⟩
      simp [hxzero]
    · intro hx
      have hxzero : x = 0 := by
        simpa using hx
      simpa [hxzero] using hzero
  rcases hnonzero with ⟨b, hb, hbne⟩
  rcases lt_or_gt_of_ne hbne.symm with hbpos | hbneg
  · exact ⟨⟨b, hb, hbpos⟩, ⟨-b, hnegClosed b hb, by linarith⟩⟩
  · exact ⟨⟨-b, hnegClosed b hb, by linarith⟩, ⟨b, hb, hbneg⟩⟩

/-- The alphabet obtained by adding an unmatched scalar to the hypotheses of
Appendix Lemma 12 still contains zero and both signs. -/
theorem insert_unmatched_scalar_has_zero_pos_neg
    {B : Finset Real}
    (hzero : (0 : Real) ∈ B)
    (hnegClosed : forall x : Real, x ∈ B -> -x ∈ B)
    (hne : B ≠ ({0} : Finset Real)) (a : Real) :
    (0 : Real) ∈ insert a B ∧
      (∃ b : Real, b ∈ insert a B ∧ 0 < b) ∧
      (∃ b : Real, b ∈ insert a B ∧ b < 0) := by
  rcases exists_pos_neg_of_zero_negClosed_ne_singleton hzero hnegClosed hne with
    ⟨hpos, hneg⟩
  refine ⟨Finset.mem_insert_of_mem hzero, ?_, ?_⟩
  · rcases hpos with ⟨b, hb, hbpos⟩
    exact ⟨b, Finset.mem_insert_of_mem hb, hbpos⟩
  · rcases hneg with ⟨b, hb, hbneg⟩
    exact ⟨b, Finset.mem_insert_of_mem hb, hbneg⟩

/-- The sphere point in the orthant opposite to the unmatched scalar.  If the
unmatched scalar is positive this is `-|u|`; if it is negative this is `|u|`.
-/
def unmatchedOppositeOrthantPoint {n : Nat} (u : OptimalAlphabets.SpherePoint n)
    (s : Real) (hs_abs : |s| = 1) : OptimalAlphabets.SpherePoint n :=
  let y : Fin n -> Real :=
    fun i => -s * |u.1 i|
  ⟨OptimalAlphabets.AsymmetricProduct.tupleVector y, by
    have hy_eq :
        OptimalAlphabets.AsymmetricProduct.tupleVector y =
          (-s) •
            OptimalAlphabets.AsymmetricProduct.tupleVector
              (OptimalAlphabets.AsymmetricProduct.absSphereTuple u) := by
      ext i
      simp [y, OptimalAlphabets.AsymmetricProduct.tupleVector,
        OptimalAlphabets.AsymmetricProduct.absSphereTuple]
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, hy_eq, norm_smul,
      OptimalAlphabets.AsymmetricProduct.norm_tupleVector_absSphereTuple u]
    simp [hs_abs]⟩

@[simp] theorem unmatchedOppositeOrthantPoint_apply {n : Nat}
    (u : OptimalAlphabets.SpherePoint n) (s : Real) (hs_abs : |s| = 1)
    (i : Fin n) :
    (unmatchedOppositeOrthantPoint u s hs_abs).1 i = -s * |u.1 i| := by
  simp [unmatchedOppositeOrthantPoint,
    OptimalAlphabets.AsymmetricProduct.tupleVector]

/-- Align a tuple in the opposite orthant back to the witness `u`. -/
def alignOppositeOrthantTuple {n : Nat} (u : OptimalAlphabets.SpherePoint n)
    (s : Real) (x : Fin n -> Real) : Fin n -> Real :=
  fun i => if 0 <= u.1 i then -s * x i else s * x i

theorem alignOppositeOrthantTuple_mem_of_negClosed
    {n : Nat} {B : Finset Real}
    (hnegClosed : forall x : Real, x ∈ B -> -x ∈ B)
    {u : OptimalAlphabets.SpherePoint n} {s : Real}
    (hs_one : s = 1 ∨ s = -1) {x : Fin n -> Real}
    (hxmem : forall i, x i ∈ B) :
    forall i, alignOppositeOrthantTuple u s x i ∈ B := by
  intro i
  by_cases hi : 0 <= u.1 i
  · rcases hs_one with rfl | rfl
    · simpa [alignOppositeOrthantTuple, hi] using hnegClosed (x i) (hxmem i)
    · simpa [alignOppositeOrthantTuple, hi] using hxmem i
  · rcases hs_one with rfl | rfl
    · simpa [alignOppositeOrthantTuple, hi] using hxmem i
    · simpa [alignOppositeOrthantTuple, hi] using hnegClosed (x i) (hxmem i)

theorem tupleVector_alignOppositeOrthantTuple_ne_zero
    {n : Nat} {u : OptimalAlphabets.SpherePoint n} {s : Real}
    (hs_one : s = 1 ∨ s = -1) {x : Fin n -> Real}
    (hxne : OptimalAlphabets.AsymmetricProduct.tupleVector x ≠ 0) :
    OptimalAlphabets.AsymmetricProduct.tupleVector
        (alignOppositeOrthantTuple u s x) ≠ 0 := by
  rw [OptimalAlphabets.AsymmetricProduct.tupleVector_ne_zero_iff] at hxne ⊢
  rcases hxne with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  by_cases hui : 0 <= u.1 i
  · rcases hs_one with rfl | rfl
    · simpa [alignOppositeOrthantTuple, hui] using (neg_ne_zero.mpr hi)
    · simpa [alignOppositeOrthantTuple, hui] using hi
  · rcases hs_one with rfl | rfl
    · simpa [alignOppositeOrthantTuple, hui] using hi
    · simpa [alignOppositeOrthantTuple, hui] using (neg_ne_zero.mpr hi)

theorem tupleCorr_alignOppositeOrthantTuple
    {n : Nat} (u : OptimalAlphabets.SpherePoint n) {s : Real}
    (hs_one : s = 1 ∨ s = -1) (hs_abs : |s| = 1) (x : Fin n -> Real) :
    OptimalAlphabets.AsymmetricProduct.tupleCorr u
        (alignOppositeOrthantTuple u s x) =
      OptimalAlphabets.AsymmetricProduct.tupleCorr
        (unmatchedOppositeOrthantPoint u s hs_abs) x := by
  have hnorm :
      ‖OptimalAlphabets.AsymmetricProduct.tupleVector
          (alignOppositeOrthantTuple u s x)‖ =
        ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ := by
    have hsq :
        ‖OptimalAlphabets.AsymmetricProduct.tupleVector
            (alignOppositeOrthantTuple u s x)‖ ^ 2 =
          ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases hui : 0 <= u.1 i
      · rcases hs_one with rfl | rfl <;>
          simp [alignOppositeOrthantTuple, hui, pow_two]
      · rcases hs_one with rfl | rfl <;>
          simp [alignOppositeOrthantTuple, hui, pow_two]
    apply le_antisymm
    · exact le_of_sq_le_sq hsq.le (norm_nonneg _)
    · exact le_of_sq_le_sq hsq.ge (norm_nonneg _)
  have hinner :
      inner Real u.1
          (OptimalAlphabets.AsymmetricProduct.tupleVector
            (alignOppositeOrthantTuple u s x)) =
        inner Real (unmatchedOppositeOrthantPoint u s hs_abs).1
          (OptimalAlphabets.AsymmetricProduct.tupleVector x) := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    by_cases hui : 0 <= u.1 i
    · have habs : |u.1 i| = u.1 i := abs_of_nonneg hui
      rcases hs_one with rfl | rfl <;>
        simp [alignOppositeOrthantTuple, hui, habs,
          unmatchedOppositeOrthantPoint, OptimalAlphabets.AsymmetricProduct.tupleVector,
          mul_comm]
    · have hle : u.1 i <= 0 := le_of_not_ge hui
      have habs : |u.1 i| = -u.1 i := abs_of_nonpos hle
      rcases hs_one with rfl | rfl <;>
        simp [alignOppositeOrthantTuple, hui, habs,
          unmatchedOppositeOrthantPoint, OptimalAlphabets.AsymmetricProduct.tupleVector,
          mul_comm]
  unfold OptimalAlphabets.AsymmetricProduct.tupleCorr
  rw [hinner, hnorm]

theorem tupleVector_dropUnmatched_norm_le
    {n : Nat} {x : Fin n -> Real} {a : Real} :
    let x' : Fin n -> Real := fun i => if x i = a then 0 else x i
    ‖OptimalAlphabets.AsymmetricProduct.tupleVector x'‖ <=
      ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ := by
  intro x'
  have hsq :
      ‖OptimalAlphabets.AsymmetricProduct.tupleVector x'‖ ^ 2 <=
        ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum ?_
    intro i _hi
    by_cases hia : x i = a
    · simp [x', hia, sq_nonneg]
    · simp [x', hia]
  have habs := (sq_le_sq.mp hsq)
  simpa [abs_of_nonneg (norm_nonneg _)] using habs

theorem exists_B_tuple_corr_ge_drop_unmatched
    {n : Nat} {B : Finset Real}
    (hzero : (0 : Real) ∈ B)
    {a : Real} {s : Real} (hsa_pos : 0 < s * a)
    {u : OptimalAlphabets.SpherePoint n} (hs_abs : |s| = 1)
    {x : Fin n -> Real}
    (hx : x ∈ nonzeroProductTuples n (insert a B))
    (hx_corr_pos :
      0 < OptimalAlphabets.AsymmetricProduct.tupleCorr
        (unmatchedOppositeOrthantPoint u s hs_abs) x) :
    ∃ y : Fin n -> Real,
      y ∈ nonzeroProductTuples n B ∧
        OptimalAlphabets.AsymmetricProduct.tupleCorr
            (unmatchedOppositeOrthantPoint u s hs_abs) x <=
          OptimalAlphabets.AsymmetricProduct.tupleCorr
            (unmatchedOppositeOrthantPoint u s hs_abs) y := by
  let x' : Fin n -> Real := fun i => if x i = a then 0 else x i
  have hxmem_insert :
      forall i, x i ∈ insert a B :=
    (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1
      (by simpa [nonzeroProductTuples] using hx)).1
  have hxne :
      OptimalAlphabets.AsymmetricProduct.tupleVector x ≠ 0 :=
    (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1
      (by simpa [nonzeroProductTuples] using hx)).2
  have hx'mem : forall i, x' i ∈ B := by
    intro i
    by_cases hia : x i = a
    · simpa [x', hia] using hzero
    · have hmem := hxmem_insert i
      simp only [Finset.mem_insert] at hmem
      rcases hmem with hxa | hxB
      · exact False.elim (hia hxa)
      · simpa [x', hia] using hxB
  have hcoord_nonpos :
      forall i : Fin n,
        (unmatchedOppositeOrthantPoint u s hs_abs).1 i * a <= 0 := by
    intro i
    have habs_nonneg : 0 <= |u.1 i| := abs_nonneg _
    have hprod_nonneg : 0 <= (s * a) * |u.1 i| :=
      mul_nonneg hsa_pos.le habs_nonneg
    have hcoord :
        (unmatchedOppositeOrthantPoint u s hs_abs).1 i * a =
          -((s * a) * |u.1 i|) := by
      simp [unmatchedOppositeOrthantPoint,
        OptimalAlphabets.AsymmetricProduct.tupleVector]
      ring
    rw [hcoord]
    exact neg_nonpos.mpr hprod_nonneg
  have hinner_le :
      inner Real (unmatchedOppositeOrthantPoint u s hs_abs).1
          (OptimalAlphabets.AsymmetricProduct.tupleVector x) <=
        inner Real (unmatchedOppositeOrthantPoint u s hs_abs).1
          (OptimalAlphabets.AsymmetricProduct.tupleVector x') := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    refine Finset.sum_le_sum ?_
    intro i _hi
    by_cases hia : x i = a
    · simpa [x', hia, OptimalAlphabets.AsymmetricProduct.tupleVector,
        mul_comm, mul_left_comm, mul_assoc] using
        hcoord_nonpos i
    · simp [x', hia, OptimalAlphabets.AsymmetricProduct.tupleVector]
  have hx_inner_pos :
      0 < inner Real (unmatchedOppositeOrthantPoint u s hs_abs).1
        (OptimalAlphabets.AsymmetricProduct.tupleVector x) := by
    have hxnorm_pos :
        0 < ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ :=
      norm_pos_iff.mpr hxne
    have hmul := mul_lt_mul_of_pos_right hx_corr_pos hxnorm_pos
    unfold OptimalAlphabets.AsymmetricProduct.tupleCorr at hmul
    simpa [div_eq_mul_inv, mul_assoc, hxnorm_pos.ne'] using hmul
  have hx'_inner_pos :
      0 < inner Real (unmatchedOppositeOrthantPoint u s hs_abs).1
        (OptimalAlphabets.AsymmetricProduct.tupleVector x') :=
    lt_of_lt_of_le hx_inner_pos hinner_le
  have hx'ne :
      OptimalAlphabets.AsymmetricProduct.tupleVector x' ≠ 0 := by
    intro hzero_vec
    rw [hzero_vec, inner_zero_right] at hx'_inner_pos
    exact (lt_irrefl (0 : Real)) hx'_inner_pos
  have hx' :
      x' ∈ nonzeroProductTuples n B := by
    exact OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.2
      ⟨hx'mem, hx'ne⟩
  have hnormx_pos :
      0 < ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ :=
    norm_pos_iff.mpr hxne
  have hnormx'_pos :
      0 < ‖OptimalAlphabets.AsymmetricProduct.tupleVector x'‖ :=
    norm_pos_iff.mpr hx'ne
  have hnorm_le :
      ‖OptimalAlphabets.AsymmetricProduct.tupleVector x'‖ <=
        ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ :=
    tupleVector_dropUnmatched_norm_le (x := x) (a := a)
  have hcorr_le :
      OptimalAlphabets.AsymmetricProduct.tupleCorr
          (unmatchedOppositeOrthantPoint u s hs_abs) x <=
        OptimalAlphabets.AsymmetricProduct.tupleCorr
          (unmatchedOppositeOrthantPoint u s hs_abs) x' := by
    have hfirst :
        inner Real (unmatchedOppositeOrthantPoint u s hs_abs).1
              (OptimalAlphabets.AsymmetricProduct.tupleVector x) /
            ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ <=
          inner Real (unmatchedOppositeOrthantPoint u s hs_abs).1
              (OptimalAlphabets.AsymmetricProduct.tupleVector x') /
            ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ :=
      div_le_div_of_nonneg_right hinner_le hnormx_pos.le
    have hinv :
        (‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖)⁻¹ <=
          (‖OptimalAlphabets.AsymmetricProduct.tupleVector x'‖)⁻¹ :=
      by
        have hinv_div :
            1 / ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ <=
              1 / ‖OptimalAlphabets.AsymmetricProduct.tupleVector x'‖ :=
          one_div_le_one_div_of_le hnormx'_pos hnorm_le
        simpa [one_div] using hinv_div
    have hsecond :
        inner Real (unmatchedOppositeOrthantPoint u s hs_abs).1
              (OptimalAlphabets.AsymmetricProduct.tupleVector x') /
            ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ <=
          inner Real (unmatchedOppositeOrthantPoint u s hs_abs).1
              (OptimalAlphabets.AsymmetricProduct.tupleVector x') /
            ‖OptimalAlphabets.AsymmetricProduct.tupleVector x'‖ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv hx'_inner_pos.le
    unfold OptimalAlphabets.AsymmetricProduct.tupleCorr
    exact le_trans hfirst hsecond
  exact ⟨x', hx', hcorr_le⟩

/-- Appendix Lemma D2: adding one unmatched scalar to a nontrivial
zero-containing sign-symmetric alphabet does not change the product-code
covering radius. -/
theorem appendix_lemmaD2_unmatched_scalar
    {n : Nat} (hn : 2 <= n) {B : Finset Real}
    (hzero : (0 : Real) ∈ B)
    (hnegSymm : forall x : Real, x ∈ B ↔ -x ∈ B)
    (hne : B ≠ ({0} : Finset Real)) (a : Real) :
    F n (insert a B) = F n B := by
  classical
  let hnegClosed : forall x : Real, x ∈ B -> -x ∈ B :=
    fun x hx => (hnegSymm x).1 hx
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn
  apply le_antisymm
  · exact appendix_lemma12_unmatched_scalar_easy_direction hnpos B a
  · by_cases haB : a ∈ B
    · simp [haB]
    · have hane : a ≠ 0 := by
        intro hazero
        exact haB (by simpa [hazero] using hzero)
      let s : Real := if 0 < a then 1 else -1
      have hs_one : s = 1 ∨ s = -1 := by
        by_cases ha_pos : 0 < a
        · exact Or.inl (by simp [s, ha_pos])
        · exact Or.inr (by simp [s, ha_pos])
      have hs_abs : |s| = 1 := by
        rcases hs_one with hs | hs
        · rw [hs]
          norm_num
        · rw [hs]
          norm_num
      have hsa_pos : 0 < s * a := by
        by_cases ha_pos : 0 < a
        · simp [s, ha_pos]
        · have ha_neg : a < 0 := lt_of_le_of_ne (le_of_not_gt ha_pos) hane
          simp [s, ha_pos]
          linarith
      rcases exists_pos_neg_of_zero_negClosed_ne_singleton hzero hnegClosed hne with
        ⟨hposB, hnegB⟩
      have hA := insert_unmatched_scalar_has_zero_pos_neg hzero hnegClosed hne a
      unfold F OptimalAlphabets.AsymmetricProduct.F_asym OptimalAlphabets.covrad_sph
      refine csSup_le ?_ ?_
      · refine ⟨OptimalAlphabets.minAngleToSphericalCode
            (OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode n B)
            (OptimalAlphabets.AsymmetricProduct.firstSpherePoint n hnpos), ?_⟩
        exact Set.mem_range_self _
      · rintro theta ⟨u, rfl⟩
        let w : OptimalAlphabets.SpherePoint n :=
          unmatchedOppositeOrthantPoint u s hs_abs
        rcases exists_angularMaximizer_positive_tupleCorr
            (A := insert a B) hA.1 hA.2.1 hA.2.2 w with
          ⟨xstar, hxstar, hopt, hxstar_pos⟩
        rcases exists_B_tuple_corr_ge_drop_unmatched
            (B := B) hzero (a := a) (s := s) hsa_pos
            (u := u) hs_abs hxstar hxstar_pos with
          ⟨y, hy, hcorr_xy⟩
        let z : Fin n -> Real := alignOppositeOrthantTuple u s y
        have hzmem : forall i, z i ∈ B := by
          simpa [z] using
            alignOppositeOrthantTuple_mem_of_negClosed
              (B := B) hnegClosed (u := u) (s := s) hs_one
              (x := y)
              ((OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1
                (by simpa [nonzeroProductTuples] using hy)).1)
        have hz_ne :
            OptimalAlphabets.AsymmetricProduct.tupleVector z ≠ 0 := by
          simpa [z] using
            tupleVector_alignOppositeOrthantTuple_ne_zero
              (u := u) (s := s) hs_one
              ((OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1
                (by simpa [nonzeroProductTuples] using hy)).2)
        have hz : z ∈ nonzeroProductTuples n B := by
          exact OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.2
            ⟨hzmem, hz_ne⟩
        have hangle_align :
            angleToRaw u z = angleToRaw w y := by
          rw [angleToRaw_eq_arccos_tupleCorr, angleToRaw_eq_arccos_tupleCorr]
          congr 1
          simpa [w, z] using
            tupleCorr_alignOppositeOrthantTuple u hs_one hs_abs y
        have hangle_y_le_x :
            angleToRaw w y <= angleToRaw w xstar :=
          angleToRaw_le_angleToRaw_of_tupleCorr_le w hcorr_xy
        have hminB_le :
            OptimalAlphabets.minAngleToSphericalCode
                (OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode n B) u <=
              angleToRaw u z :=
          minAngleToSphericalCode_le_angleToRaw_of_mem_nonzeroProductTuples
            (A := B) u hz
        have hminA_eq :
            OptimalAlphabets.minAngleToSphericalCode
                (OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode n (insert a B)) w =
              angleToRaw w xstar :=
          minAngleToSphericalCode_eq_angleToRaw_of_angularMaximizer
            (A := insert a B) w hxstar hopt
        have hminA_le_cov :
            OptimalAlphabets.minAngleToSphericalCode
                (OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode n (insert a B)) w <=
              sSup (Set.range
                (OptimalAlphabets.minAngleToSphericalCode
                  (OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode n (insert a B)))) :=
          le_csSup
            (OptimalAlphabets.bddAbove_range_minAngleToSphericalCode
              (OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode n (insert a B)))
            (Set.mem_range_self w)
        calc
          OptimalAlphabets.minAngleToSphericalCode
              (OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode n B) u
              <= angleToRaw u z := hminB_le
          _ = angleToRaw w y := hangle_align
          _ <= angleToRaw w xstar := hangle_y_le_x
          _ = OptimalAlphabets.minAngleToSphericalCode
              (OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode n (insert a B)) w :=
                hminA_eq.symm
          _ <= sSup (Set.range
                (OptimalAlphabets.minAngleToSphericalCode
                  (OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode n (insert a B)))) :=
                hminA_le_cov

/-- Matrix appearing in Appendix Lemma 13:
`Q i j = c_{max i j}^2`, using zero-based Lean indices. -/
def appendixLemma13Matrix {m : Nat} (c : Fin m -> Real) :
    Matrix (Fin m) (Fin m) Real :=
  fun i j => (c (max i j)) ^ 2

/-- Closed form for `c^T Q^{-1} c` in Appendix Lemma 13. -/
def appendixLemma13Constant {m : Nat} (c : Fin m -> Real) : Real :=
  1 +
    ∑ j : Fin (m - 1),
      (c ⟨j.1, by have hj := j.2; omega⟩ -
          c ⟨j.1 + 1, by have hj := j.2; omega⟩) /
        (c ⟨j.1, by have hj := j.2; omega⟩ +
          c ⟨j.1 + 1, by have hj := j.2; omega⟩)

/-- Paper hypothesis `c_1 > c_2 > ... > c_m > 0`, in zero-based Lean
indexing. -/
def appendixLemma13StrictPositiveDecreasing {m : Nat} (c : Fin m -> Real) :
    Prop :=
  (forall i : Fin m, 0 < c i) ∧
    forall {i j : Fin m}, i < j -> c j < c i
/-- Lower-triangular prefix-sum matrix from the proof of Appendix Lemma 13. -/
def appendixLemma13PrefixMatrix (m : Nat) :
    Matrix (Fin m) (Fin m) Real :=
  fun j i => if i <= j then 1 else 0

/-- Diagonal matrix of positive increments
`c_j^2 - c_{j+1}^2`, with bottom entry `c_m^2`. -/
def appendixLemma13EnergyDiagonal {m : Nat} (c : Fin m -> Real) :
    Matrix (Fin m) (Fin m) Real :=
  Matrix.diagonal (fun j =>
    OptimalAlphabets.AsymmetricProduct.layerEnergyCoeff c j)
/-- The positive diagonal coefficients in the prefix-sum factorization used in
the proof of Appendix Lemma 13. -/
theorem appendixLemma13_layerEnergyCoeff_pos
    {m : Nat} {c : Fin m -> Real}
    (hc : appendixLemma13StrictPositiveDecreasing c) (j : Fin m) :
    0 < OptimalAlphabets.AsymmetricProduct.layerEnergyCoeff c j := by
  unfold OptimalAlphabets.AsymmetricProduct.layerEnergyCoeff
  exact mul_pos
    (OptimalAlphabets.AsymmetricProduct.layerDiff_pos hc.1 hc.2 j)
    (OptimalAlphabets.AsymmetricProduct.layerWidth_pos hc.1 j)

/-- The energy diagonal in the prefix-sum factorization is positive definite. -/
theorem appendixLemma13EnergyDiagonal_posDef
    {m : Nat} {c : Fin m -> Real}
    (hc : appendixLemma13StrictPositiveDecreasing c) :
    (appendixLemma13EnergyDiagonal c).PosDef := by
  exact Matrix.PosDef.diagonal
    (fun j : Fin m => appendixLemma13_layerEnergyCoeff_pos hc j)

/-- Tail sums of the Appendix Lemma 13 energy coefficients telescope to
`c_l^2`. -/
theorem appendixLemma13_tail_energy_sum_eq_sq
    {m : Nat} {c : Fin m -> Real} (l : Fin m) :
    (∑ j ∈ Finset.Ico (l : Nat) m,
        OptimalAlphabets.AsymmetricProduct.layerEnergyCoeffNat c j) =
      (c l) ^ 2 := by
  simpa [OptimalAlphabets.AsymmetricProduct.levelValueNat, l.2] using
    (OptimalAlphabets.AsymmetricProduct.sum_Ico_layerEnergyCoeffNat_eq_levelValueNat_sq
      (m := m) (c := c) (l := (l : Nat)) l.2)

/-- Entrywise tail-sum form of the prefix factorization in Appendix Lemma 13. -/
theorem appendixLemma13_prefix_factor_entry
    {m : Nat} (c : Fin m -> Real) (i j : Fin m) :
    (∑ k : Fin m,
        (if i <= k then (1 : Real) else 0) *
          OptimalAlphabets.AsymmetricProduct.layerEnergyCoeff c k *
          (if j <= k then (1 : Real) else 0)) =
      (c (max i j)) ^ 2 := by
  classical
  let l : Fin m := max i j
  have hpoint :
      (∑ k : Fin m,
          (if i <= k then (1 : Real) else 0) *
            OptimalAlphabets.AsymmetricProduct.layerEnergyCoeff c k *
            (if j <= k then (1 : Real) else 0)) =
        ∑ k : Fin m,
          if l <= k then
            OptimalAlphabets.AsymmetricProduct.layerEnergyCoeff c k
          else 0 := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    have hlk : l <= k ↔ i <= k ∧ j <= k := by
      simp [l]
    by_cases hlik : l <= k
    · have hik : i <= k := (hlk.mp hlik).1
      have hjk : j <= k := (hlk.mp hlik).2
      simp [hik, hjk, hlik]
    · have hnot : ¬ (i <= k ∧ j <= k) := by
        intro h
        exact hlik (hlk.mpr h)
      by_cases hik : i <= k
      · by_cases hjk : j <= k
        · exact False.elim (hnot ⟨hik, hjk⟩)
        · simp [hik, hjk, hlik]
      · simp [hik, hlik]
  have hfin_to_range :
      (∑ k : Fin m,
          if l <= k then
            OptimalAlphabets.AsymmetricProduct.layerEnergyCoeff c k
          else 0) =
        ∑ k ∈ Finset.range m,
          if (l : Nat) <= k then
            OptimalAlphabets.AsymmetricProduct.layerEnergyCoeffNat c k
          else 0 := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < m := by simpa using hk
    simp [OptimalAlphabets.AsymmetricProduct.layerEnergyCoeffNat, hklt, Fin.le_def]
  have hfilter :
      (∑ k ∈ Finset.range m,
          if (l : Nat) <= k then
            OptimalAlphabets.AsymmetricProduct.layerEnergyCoeffNat c k
          else 0) =
        ∑ k ∈ Finset.Ico (l : Nat) m,
          OptimalAlphabets.AsymmetricProduct.layerEnergyCoeffNat c k := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ ?_
    · ext k
      simp [Finset.mem_Ico, and_comm]
    · intro k _hk
      rfl
  calc
    (∑ k : Fin m,
        (if i <= k then (1 : Real) else 0) *
          OptimalAlphabets.AsymmetricProduct.layerEnergyCoeff c k *
          (if j <= k then (1 : Real) else 0))
        = ∑ k : Fin m,
          if l <= k then
            OptimalAlphabets.AsymmetricProduct.layerEnergyCoeff c k
          else 0 := hpoint
    _ = ∑ k ∈ Finset.range m,
          if (l : Nat) <= k then
            OptimalAlphabets.AsymmetricProduct.layerEnergyCoeffNat c k
          else 0 := hfin_to_range
    _ = ∑ k ∈ Finset.Ico (l : Nat) m,
          OptimalAlphabets.AsymmetricProduct.layerEnergyCoeffNat c k := hfilter
    _ = (c l) ^ 2 := appendixLemma13_tail_energy_sum_eq_sq (c := c) l
    _ = (c (max i j)) ^ 2 := rfl

/-- Prefix-sum factorization of the Appendix Lemma 13 matrix:
`Q = L^T D L`. -/
theorem appendixLemma13Matrix_eq_prefix_factor
    {m : Nat} (c : Fin m -> Real) :
    appendixLemma13Matrix c =
      (appendixLemma13PrefixMatrix m).transpose *
        appendixLemma13EnergyDiagonal c *
        appendixLemma13PrefixMatrix m := by
  classical
  ext i j
  rw [appendixLemma13Matrix]
  symm
  simpa [appendixLemma13PrefixMatrix, appendixLemma13EnergyDiagonal,
    Matrix.mul_apply, Matrix.diagonal, mul_assoc] using
    (appendixLemma13_prefix_factor_entry (c := c) i j)

/-- The prefix-sum matrix in Appendix Lemma 13 is unit lower triangular. -/
theorem appendixLemma13PrefixMatrix_det (m : Nat) :
    (appendixLemma13PrefixMatrix m : Matrix (Fin m) (Fin m) Real).det = 1 := by
  classical
  rw [Matrix.det_of_lowerTriangular
    (appendixLemma13PrefixMatrix m : Matrix (Fin m) (Fin m) Real)]
  · simp [appendixLemma13PrefixMatrix]
  · intro i j hji
    have hij : i < j := by
      simpa using hji
    have hnot : ¬ j <= i := not_le.mpr hij
    simp [appendixLemma13PrefixMatrix, hnot]

/-- The prefix-sum matrix is invertible. -/
theorem appendixLemma13PrefixMatrix_isUnit (m : Nat) :
    IsUnit (appendixLemma13PrefixMatrix m :
      Matrix (Fin m) (Fin m) Real) := by
  classical
  have hdet :
      IsUnit (appendixLemma13PrefixMatrix m :
        Matrix (Fin m) (Fin m) Real).det := by
    rw [appendixLemma13PrefixMatrix_det]
    exact isUnit_one
  exact
    (Matrix.isUnit_iff_isUnit_det
      (appendixLemma13PrefixMatrix m :
        Matrix (Fin m) (Fin m) Real)).mpr hdet

/-- The prefix-sum matrix has injective matrix-vector multiplication. -/
theorem appendixLemma13PrefixMatrix_mulVec_injective (m : Nat) :
    Function.Injective
      (appendixLemma13PrefixMatrix m : Matrix (Fin m) (Fin m) Real).mulVec := by
  classical
  exact Matrix.mulVec_injective_iff_isUnit.mpr
    (appendixLemma13PrefixMatrix_isUnit m)
/-- Positive-definiteness half of Appendix Lemma 13, proved from the
unit-lower-triangular prefix factorization. -/
theorem appendixLemma13Matrix_posDef
    {m : Nat} {c : Fin m -> Real}
    (hc : appendixLemma13StrictPositiveDecreasing c) :
    (appendixLemma13Matrix c).PosDef := by
  rw [appendixLemma13Matrix_eq_prefix_factor (c := c)]
  have hD : (appendixLemma13EnergyDiagonal c).PosDef :=
    appendixLemma13EnergyDiagonal_posDef hc
  simpa [Matrix.conjTranspose, appendixLemma13PrefixMatrix] using
    hD.conjTranspose_mul_mul_same
      (B := appendixLemma13PrefixMatrix m)
      (appendixLemma13PrefixMatrix_mulVec_injective m)

/-- The layer-difference vector used in the inverse calculation for Appendix
Lemma 13. -/
def appendixLemma13LayerDiff {m : Nat} (c : Fin m -> Real) :
    Fin m -> Real :=
  fun j => OptimalAlphabets.AsymmetricProduct.layerDiff c j

/-- The diagonal-inverse vector `layerDiff / layerEnergyCoeff` used in the
inverse calculation for Appendix Lemma 13. -/
def appendixLemma13LayerQuotient {m : Nat} (c : Fin m -> Real) :
    Fin m -> Real :=
  fun j =>
    OptimalAlphabets.AsymmetricProduct.layerDiff c j /
      OptimalAlphabets.AsymmetricProduct.layerEnergyCoeff c j

/-- Tail sums of the layer differences telescope to the level value `c_l`. -/
theorem appendixLemma13_tail_diff_sum_eq_value
    {m : Nat} {c : Fin m -> Real} (l : Fin m) :
    (∑ j ∈ Finset.Ico (l : Nat) m,
        OptimalAlphabets.AsymmetricProduct.layerDiffNat c j) =
      c l := by
  simpa [OptimalAlphabets.AsymmetricProduct.levelValueNat, l.2] using
    (OptimalAlphabets.AsymmetricProduct.sum_Ico_layerDiffNat_eq_levelValueNat
      (m := m) (c := c) (l := (l : Nat)) l.2)

/-- The transpose prefix matrix sends layer differences to the level vector
`c`: in paper notation, `L^T Δ = c`. -/
theorem appendixLemma13PrefixTranspose_mulVec_layerDiff
    {m : Nat} (c : Fin m -> Real) :
    Matrix.mulVec (appendixLemma13PrefixMatrix m).transpose
        (appendixLemma13LayerDiff c) = c := by
  classical
  ext i
  have hfin_to_range :
      (∑ j : Fin m,
          if i <= j then
            OptimalAlphabets.AsymmetricProduct.layerDiff c j
          else 0) =
        ∑ j ∈ Finset.range m,
          if (i : Nat) <= j then
            OptimalAlphabets.AsymmetricProduct.layerDiffNat c j
          else 0 := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjlt : j < m := by simpa using hj
    simp [OptimalAlphabets.AsymmetricProduct.layerDiffNat, hjlt, Fin.le_def]
  have hfilter :
      (∑ j ∈ Finset.range m,
          if (i : Nat) <= j then
            OptimalAlphabets.AsymmetricProduct.layerDiffNat c j
          else 0) =
        ∑ j ∈ Finset.Ico (i : Nat) m,
          OptimalAlphabets.AsymmetricProduct.layerDiffNat c j := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ ?_
    · ext j
      simp [Finset.mem_Ico, and_comm]
    · intro j _hj
      rfl
  calc
    (Matrix.mulVec (appendixLemma13PrefixMatrix m).transpose
        (appendixLemma13LayerDiff c)) i
        = ∑ j : Fin m,
          if i <= j then
            OptimalAlphabets.AsymmetricProduct.layerDiff c j
          else 0 := by
            simp [Matrix.mulVec, dotProduct, appendixLemma13PrefixMatrix,
              appendixLemma13LayerDiff]
    _ = ∑ j ∈ Finset.range m,
          if (i : Nat) <= j then
            OptimalAlphabets.AsymmetricProduct.layerDiffNat c j
          else 0 := hfin_to_range
    _ = ∑ j ∈ Finset.Ico (i : Nat) m,
          OptimalAlphabets.AsymmetricProduct.layerDiffNat c j := hfilter
    _ = c i := appendixLemma13_tail_diff_sum_eq_value (c := c) i

/-- Applying the energy diagonal to the quotient vector recovers the layer
differences. -/
theorem appendixLemma13EnergyDiagonal_mulVec_layerQuotient
    {m : Nat} {c : Fin m -> Real}
    (hc : appendixLemma13StrictPositiveDecreasing c) :
    Matrix.mulVec (appendixLemma13EnergyDiagonal c)
        (appendixLemma13LayerQuotient c) =
      appendixLemma13LayerDiff c := by
  ext j
  have hEpos := appendixLemma13_layerEnergyCoeff_pos hc j
  rw [appendixLemma13EnergyDiagonal, Matrix.mulVec_diagonal]
  dsimp [appendixLemma13LayerQuotient, appendixLemma13LayerDiff]
  field_simp [hEpos.ne']

/-- Inverting the energy diagonal sends layer differences to the quotient
vector. -/
theorem appendixLemma13EnergyDiagonal_inv_mulVec_layerDiff
    {m : Nat} {c : Fin m -> Real}
    (hc : appendixLemma13StrictPositiveDecreasing c) :
    Matrix.mulVec (appendixLemma13EnergyDiagonal c)⁻¹
        (appendixLemma13LayerDiff c) =
      appendixLemma13LayerQuotient c := by
  classical
  letI := (appendixLemma13EnergyDiagonal_posDef hc).isUnit.invertible
  exact Matrix.inv_mulVec_eq_vec
    (A := appendixLemma13EnergyDiagonal c)
    (u := appendixLemma13LayerDiff c)
    (v := appendixLemma13LayerQuotient c)
    (hM := (appendixLemma13EnergyDiagonal_mulVec_layerQuotient hc).symm)

/-- Inverting the transpose prefix matrix sends the level vector `c` to the
layer-difference vector. -/
theorem appendixLemma13PrefixTranspose_inv_mulVec_level
    {m : Nat} (c : Fin m -> Real) :
    Matrix.mulVec ((appendixLemma13PrefixMatrix m).transpose)⁻¹ c =
      appendixLemma13LayerDiff c := by
  classical
  have hdet :
      IsUnit ((appendixLemma13PrefixMatrix m).transpose :
        Matrix (Fin m) (Fin m) Real).det := by
    rw [Matrix.det_transpose, appendixLemma13PrefixMatrix_det]
    exact isUnit_one
  have hunit :
      IsUnit ((appendixLemma13PrefixMatrix m).transpose :
        Matrix (Fin m) (Fin m) Real) :=
    (Matrix.isUnit_iff_isUnit_det
      ((appendixLemma13PrefixMatrix m).transpose :
        Matrix (Fin m) (Fin m) Real)).mpr hdet
  letI := hunit.invertible
  exact Matrix.inv_mulVec_eq_vec
    (A := (appendixLemma13PrefixMatrix m).transpose)
    (u := c)
    (v := appendixLemma13LayerDiff c)
    (hM := (appendixLemma13PrefixTranspose_mulVec_layerDiff c).symm)

/-- The layer-difference/quotient dot product is exactly the sum of layer
ratios. -/
theorem appendixLemma13_dot_layerDiff_layerQuotient_eq_sum_layerRatioCoeff
    {m : Nat} {c : Fin m -> Real}
    (hc : appendixLemma13StrictPositiveDecreasing c) :
    dotProduct (appendixLemma13LayerDiff c)
        (appendixLemma13LayerQuotient c) =
      ∑ j : Fin m, OptimalAlphabets.AsymmetricProduct.layerRatioCoeff c j := by
  classical
  unfold dotProduct appendixLemma13LayerDiff appendixLemma13LayerQuotient
  refine Finset.sum_congr rfl ?_
  intro j _hj
  have hdpos :
      0 < OptimalAlphabets.AsymmetricProduct.layerDiff c j :=
    OptimalAlphabets.AsymmetricProduct.layerDiff_pos hc.1 hc.2 j
  have hwpos :
      0 < OptimalAlphabets.AsymmetricProduct.layerWidth c j :=
    OptimalAlphabets.AsymmetricProduct.layerWidth_pos hc.1 j
  unfold OptimalAlphabets.AsymmetricProduct.layerEnergyCoeff
    OptimalAlphabets.AsymmetricProduct.layerRatioCoeff
  field_simp [hdpos.ne', hwpos.ne']

/-- Explicit inverse-vector calculation for the Appendix Lemma 13 matrix. -/
theorem appendixLemma13Matrix_inv_mulVec_level
    {m : Nat} {c : Fin m -> Real}
    (hc : appendixLemma13StrictPositiveDecreasing c) :
    Matrix.mulVec (appendixLemma13Matrix c)⁻¹ c =
      Matrix.mulVec (appendixLemma13PrefixMatrix m)⁻¹
        (appendixLemma13LayerQuotient c) := by
  classical
  rw [appendixLemma13Matrix_eq_prefix_factor (c := c)]
  rw [Matrix.mul_inv_rev]
  rw [Matrix.mul_inv_rev]
  rw [← Matrix.mulVec_mulVec]
  rw [← Matrix.mulVec_mulVec]
  rw [appendixLemma13PrefixTranspose_inv_mulVec_level]
  rw [appendixLemma13EnergyDiagonal_inv_mulVec_layerDiff hc]

/-- The closed-form scalar in Appendix Lemma 13 is the layer-ratio sum used by
the upstream layer-cake proof. -/
theorem appendixLemma13Constant_eq_sum_layerRatioCoeff
    {m : Nat} (hm : 1 <= m) {c : Fin m -> Real}
    (hpos : forall j : Fin m, 0 < c j) :
    appendixLemma13Constant c =
      ∑ j : Fin m, OptimalAlphabets.AsymmetricProduct.layerRatioCoeff c j := by
  rw [OptimalAlphabets.AsymmetricProduct.sum_layerRatioCoeff_eq_layerCakeArg
    (m := m) hm (c := c) hpos]
  unfold appendixLemma13Constant
  congr 1
  rw [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjlt : j < m - 1 := by simpa using hj
  have hjsucc : j + 1 < m := by omega
  simp [OptimalAlphabets.AsymmetricProduct.layerCakeStepTerm, hjlt, hjsucc]

/-- General quadratic-form identity in Appendix Lemma 13. -/
theorem appendixLemma13_quadratic_form_identity
    {m : Nat} (hm : 1 <= m) {c : Fin m -> Real}
    (hc : appendixLemma13StrictPositiveDecreasing c) :
    dotProduct c (Matrix.mulVec (appendixLemma13Matrix c)⁻¹ c) =
      appendixLemma13Constant c := by
  classical
  let L : Matrix (Fin m) (Fin m) Real := appendixLemma13PrefixMatrix m
  let Delta : Fin m -> Real := appendixLemma13LayerDiff c
  let R : Fin m -> Real := appendixLemma13LayerQuotient c
  have hLunit : IsUnit L := by
    dsimp [L]
    exact appendixLemma13PrefixMatrix_isUnit m
  letI := hLunit.invertible
  have hdot :
      dotProduct c (Matrix.mulVec L⁻¹ R) = dotProduct Delta R := by
    calc
      dotProduct c (Matrix.mulVec L⁻¹ R)
          = dotProduct (Matrix.mulVec L.transpose Delta)
              (Matrix.mulVec L⁻¹ R) := by
                dsimp [L, Delta]
                rw [appendixLemma13PrefixTranspose_mulVec_layerDiff]
      _ = dotProduct (Matrix.vecMul Delta L) (Matrix.mulVec L⁻¹ R) := by
                rw [Matrix.mulVec_transpose]
      _ = dotProduct (Matrix.vecMul (Matrix.vecMul Delta L) L⁻¹) R := by
                rw [Matrix.dotProduct_mulVec]
      _ = dotProduct (Matrix.vecMul Delta (L * L⁻¹)) R := by
                rw [Matrix.vecMul_vecMul]
      _ = dotProduct Delta R := by
                rw [Matrix.mul_inv_of_invertible]
                simp [Matrix.vecMul_one]
  calc
    dotProduct c (Matrix.mulVec (appendixLemma13Matrix c)⁻¹ c)
        = dotProduct c (Matrix.mulVec L⁻¹ R) := by
            dsimp [L, R]
            rw [appendixLemma13Matrix_inv_mulVec_level hc]
    _ = dotProduct Delta R := hdot
    _ = ∑ j : Fin m, OptimalAlphabets.AsymmetricProduct.layerRatioCoeff c j := by
          dsimp [Delta, R]
          exact appendixLemma13_dot_layerDiff_layerQuotient_eq_sum_layerRatioCoeff hc
    _ = appendixLemma13Constant c := by
          exact (appendixLemma13Constant_eq_sum_layerRatioCoeff
            (m := m) hm (c := c) hc.1).symm
/-- Appendix Lemma 13, theorem-backed general statement. -/
theorem appendix_lemma13_quadratic_form
    (m : Nat) (hm : 1 <= m) (c : Fin m -> Real)
    (hc : appendixLemma13StrictPositiveDecreasing c) :
    (appendixLemma13Matrix c).PosDef ∧
      dotProduct c (Matrix.mulVec (appendixLemma13Matrix c)⁻¹ c) =
        appendixLemma13Constant c := by
  exact ⟨appendixLemma13Matrix_posDef hc,
    appendixLemma13_quadratic_form_identity (m := m) hm (c := c) hc⟩
/-- Theorem 5, literal liminf/limsup chain statement. -/
theorem theorem5_liminf_limsup_chain
    {b : Nat} (hb : 3 <= b) :
    arbConst b <= Filter.liminf (fun n : Nat => normBestAlpha n (2 ^ b)) atTop ∧
    fpConst b < arbConst b ∧
    Filter.limsup (fun n : Nat => normBestFpCos n b) atTop <= fpConst b := by
  have hb2 : 2 <= b := le_trans (by norm_num : 2 <= 3) hb
  exact ⟨corollary4_liminf (b := b) hb2,
    fpConst_lt_arbConst (b := b) hb,
    corollary3_limsup (b := b) hb2⟩

end PaperProofs
