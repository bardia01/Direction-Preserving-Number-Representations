import PaperProofs.Internal.OptimalAlphabets.SphericalCapMeasure.ExactFormula

/-!
# OptimalAlphabets.SphericalCapMeasure.LowerBound

Lower bounds for normalized spherical cap measure.
-/

noncomputable section

open Set Filter Topology Real Metric MeasureTheory intervalIntegral
open scoped ENNReal NNReal Pointwise

namespace OptimalAlphabets

theorem capMeasure_lower_bound
    (n : ℕ) (hn : 2 ≤ n) (a δ : ℝ)
    (ha0 : 0 < a) (hapi : a < Real.pi / 2)
    (hδ0 : 0 < δ) (hδ : δ < a) :
    capMeasure n a ≥
      (sphereArea (n - 2) / sphereArea (n - 1)) *
        δ * Real.sin (a - δ) ^ (n - 2) := by
  let f : ℝ → ℝ := fun t => Real.sin t ^ (n - 2)
  have ha0' : 0 ≤ a := ha0.le
  have hsub_nonneg : 0 ≤ a - δ := sub_nonneg.mpr hδ.le
  have hsub_le_a : a - δ ≤ a := by linarith
  have hfa0 : IntervalIntegrable f volume 0 (a - δ) := by
    exact Continuous.intervalIntegrable (by
      simp [f]
      fun_prop) 0 (a - δ)
  have hfδ : IntervalIntegrable f volume (a - δ) a := by
    exact Continuous.intervalIntegrable (by
      simp [f]
      fun_prop) (a - δ) a
  have hsplit :
      (∫ t in 0..a, f t) = (∫ t in 0..(a - δ), f t) + ∫ t in (a - δ)..a, f t := by
    simpa [f] using (intervalIntegral.integral_add_adjacent_intervals hfa0 hfδ).symm
  have hnonneg_left : 0 ≤ ∫ t in 0..(a - δ), f t := by
    refine intervalIntegral.integral_nonneg hsub_nonneg ?_
    intro t ht
    have hs : 0 ≤ Real.sin t := by
      apply Real.sin_nonneg_of_mem_Icc
      exact ⟨ht.1, ht.2.trans (by linarith [hapi])⟩
    exact pow_nonneg hs _
  have hrestrict :
      ∫ t in (a - δ)..a, f t ≤ ∫ t in 0..a, f t := by
    linarith [hsplit, hnonneg_left]
  have hsin_mono :
      ∀ t ∈ Set.Icc (a - δ) a, Real.sin (a - δ) ≤ Real.sin t := by
    intro t ht
    have hleft_lower : -(Real.pi / 2) ≤ a - δ := by
      have hpi : 0 < Real.pi / 2 := by positivity
      linarith
    have hmem :
        t ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · exact le_trans hleft_lower ht.1
      · exact ht.2.trans hapi.le
    have hleft :
        a - δ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · exact hleft_lower
      · linarith
    exact Real.monotoneOn_sin hleft hmem ht.1
  have hpow_mono :
      ∀ t ∈ Set.Icc (a - δ) a,
        Real.sin (a - δ) ^ (n - 2) ≤ Real.sin t ^ (n - 2) := by
    intro t ht
    have hs0 : 0 ≤ Real.sin (a - δ) := by
      apply Real.sin_nonneg_of_mem_Icc
      constructor
      · exact hsub_nonneg
      · linarith
    exact pow_le_pow_left₀ hs0 (hsin_mono t ht) (n - 2)
  have hconst_lower :
      ∫ t in (a - δ)..a, Real.sin (a - δ) ^ (n - 2) ≤
        ∫ t in (a - δ)..a, f t := by
    refine intervalIntegral.integral_mono_on
      (μ := volume) (a := a - δ) (b := a)
      (f := fun _ => Real.sin (a - δ) ^ (n - 2)) (g := f)
      hsub_le_a _root_.intervalIntegrable_const hfδ ?_
    intro t ht
    simpa [f] using hpow_mono t ht
  have hconst_eval :
      ∫ t in (a - δ)..a, Real.sin (a - δ) ^ (n - 2) =
        δ * Real.sin (a - δ) ^ (n - 2) := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul, sub_eq_add_neg]
  have hratio_nonneg : 0 ≤ sphereArea (n - 2) / sphereArea (n - 1) := by
    exact div_nonneg (sphereArea_nonneg (n - 2)) (sphereArea_nonneg (n - 1))
  calc
    capMeasure n a
        = (sphereArea (n - 2) / sphereArea (n - 1)) * ∫ t in 0..a, f t := by
          simpa [f] using capMeasure_eq_mul_intervalIntegral_sin_pow n hn a ha0' hapi
    _ ≥ (sphereArea (n - 2) / sphereArea (n - 1)) * ∫ t in (a - δ)..a, f t := by
          exact mul_le_mul_of_nonneg_left hrestrict hratio_nonneg
    _ ≥ (sphereArea (n - 2) / sphereArea (n - 1)) *
          (∫ t in (a - δ)..a, Real.sin (a - δ) ^ (n - 2)) := by
          exact mul_le_mul_of_nonneg_left hconst_lower hratio_nonneg
    _ = (sphereArea (n - 2) / sphereArea (n - 1)) *
          (δ * Real.sin (a - δ) ^ (n - 2)) := by
          rw [hconst_eval]
    _ = (sphereArea (n - 2) / sphereArea (n - 1)) *
          δ * Real.sin (a - δ) ^ (n - 2) := by
          ring

end OptimalAlphabets
