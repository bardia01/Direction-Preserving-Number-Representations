import PaperProofs.Internal.OptimalAlphabets.SphericalNets
import PaperProofs.Internal.OptimalAlphabets.SphericalCapMeasure.UniformLowerBound
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Data.Nat.Find
import Mathlib.MeasureTheory.Measure.Real

/-!
# OptimalAlphabets.SphericalCapCovering

Finite spherical-cap covers and the true cap-covering number.

This file is deliberately independent of the downstream `rho_sph` API: it packages the
covering problem in the language of finite cap covers, proves the minimality/positivity
facts needed for asymptotic arguments, and records the elementary measure lower bound.
-/

noncomputable section

open Set Filter Topology Real Metric MeasureTheory Asymptotics intervalIntegral
open scoped ENNReal NNReal Pointwise

namespace OptimalAlphabets

/-- A finite set of centers whose spherical caps of angular radius `theta` cover
the whole unit sphere in `ℝ^n`. -/
def SphericalCapCover (n : ℕ) (theta : ℝ) (C : Finset (SpherePoint n)) : Prop :=
  ∀ u : SpherePoint n, ∃ c ∈ C, InnerProductGeometry.angle u.1 c.1 ≤ theta

/-- There is a spherical cap cover with exactly `m` centers. -/
def HasSphericalCapCover (n : ℕ) (theta : ℝ) (m : ℕ) : Prop :=
  ∃ C : Finset (SpherePoint n), SphericalCapCover n theta C ∧ C.card = m

/-- The true spherical-cap covering number, totalized to `0` only if no finite cover exists. -/
noncomputable def sphericalCapCoveringNumber (n : ℕ) (theta : ℝ) : ℕ := by
  classical
  exact if h : ∃ m, HasSphericalCapCover n theta m then Nat.find h else 0

/-- The Wyner covering exponent, `-log(sin theta)`. -/
def coveringExponent (theta : ℝ) : ℝ :=
  - Real.log (Real.sin theta)

@[simp]
theorem coveringExponent_eq (theta : ℝ) :
    coveringExponent theta = - Real.log (Real.sin theta) := rfl

/-- Positive-radius caps have a finite cover by compactness of the sphere. -/
theorem exists_sphericalCapCover_of_pos
    (n : ℕ) {theta : ℝ} (htheta0 : 0 < theta) :
    ∃ C : Finset (SpherePoint n), SphericalCapCover n theta C := by
  let ε : ℝ := min theta 1
  have hε0 : 0 < ε := by
    dsimp [ε]
    exact lt_min htheta0 zero_lt_one
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    exact min_le_right _ _
  rcases exists_finset_card_le_and_angle_cover n hε0 hε1 with ⟨C, hCcover, -⟩
  refine ⟨C, ?_⟩
  intro u
  rcases hCcover u with ⟨c, hc, huc⟩
  exact ⟨c, hc, huc.trans (min_le_left _ _)⟩

theorem exists_hasSphericalCapCover_of_pos
    (n : ℕ) {theta : ℝ} (htheta0 : 0 < theta) :
    ∃ m, HasSphericalCapCover n theta m := by
  rcases exists_sphericalCapCover_of_pos n htheta0 with ⟨C, hC⟩
  exact ⟨C.card, C, hC, rfl⟩

/-- The minimum is attained whenever a finite cover exists. -/
theorem sphericalCapCoveringNumber_spec
    {n : ℕ} {theta : ℝ} (h : ∃ m, HasSphericalCapCover n theta m) :
    HasSphericalCapCover n theta (sphericalCapCoveringNumber n theta) := by
  classical
  rw [sphericalCapCoveringNumber]
  simp [h, Nat.find_spec h]

/-- A concrete finite cover bounds the covering number from above. -/
theorem sphericalCapCoveringNumber_le_of_cover
    {n : ℕ} {theta : ℝ} {C : Finset (SpherePoint n)}
    (hC : SphericalCapCover n theta C) :
    sphericalCapCoveringNumber n theta ≤ C.card := by
  classical
  have h : ∃ m, HasSphericalCapCover n theta m := ⟨C.card, C, hC, rfl⟩
  rw [sphericalCapCoveringNumber]
  simpa [h] using Nat.find_min' h ⟨C, hC, rfl⟩

/-- The minimal cover itself is a cover for positive angular radius. -/
theorem exists_cover_card_sphericalCapCoveringNumber
    {n : ℕ} {theta : ℝ} (htheta0 : 0 < theta) :
    ∃ C : Finset (SpherePoint n),
      SphericalCapCover n theta C ∧ C.card = sphericalCapCoveringNumber n theta := by
  rcases sphericalCapCoveringNumber_spec
      (exists_hasSphericalCapCover_of_pos n htheta0) with ⟨C, hC, hcard⟩
  exact ⟨C, hC, hcard⟩

/-- In dimensions at least two, a positive-radius cap cover with radius below `π`
has at least one center. -/
theorem sphericalCapCoveringNumber_pos
    {n : ℕ} {theta : ℝ} (hn : 2 ≤ n) (htheta0 : 0 < theta)
    (_htheta_pi : theta < Real.pi) :
    0 < sphericalCapCoveringNumber n theta := by
  classical
  rw [sphericalCapCoveringNumber]
  have h : ∃ m, HasSphericalCapCover n theta m :=
    exists_hasSphericalCapCover_of_pos n htheta0
  simp [h]
  rintro ⟨C, hC, hcard⟩
  have hCempty : C = ∅ := Finset.card_eq_zero.mp hcard
  have hsp : Nonempty (SpherePoint n) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    subst n
    simpa [Nat.add_comm] using spherePoint_nonempty m
  rcases hsp with ⟨u⟩
  rcases hC u with ⟨c, hc, -⟩
  simp [hCempty] at hc
/-- A finite cap cover has total cap measure at least one. -/
theorem one_le_card_mul_capMeasure_of_sphericalCapCover
    {n : ℕ} (hn : 2 ≤ n) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta_pi2 : theta ≤ Real.pi / 2)
    {C : Finset (SpherePoint n)} (hC : SphericalCapCover n theta C) :
    1 ≤ (C.card : ℝ) * capMeasure n theta := by
  have hn0 : 0 < n := by omega
  let μ : ProbabilityMeasure (SpherePoint n) := sphereProbabilityMeasure n hn0
  have hsubset :
      (Set.univ : Set (SpherePoint n)) ⊆ ⋃ c ∈ C, capAround c theta := by
    intro u _
    rcases hC u with ⟨c, hc, huc⟩
    exact mem_iUnion.2 ⟨c, mem_iUnion.2 ⟨hc, huc⟩⟩
  calc
    1 = ((μ : Measure (SpherePoint n)).real Set.univ) := by
          simp [Measure.real_def, μ]
    _ ≤ ((μ : Measure (SpherePoint n)).real (⋃ c ∈ C, capAround c theta)) := by
          exact MeasureTheory.measureReal_mono hsubset
            (measure_ne_top (μ := (μ : Measure (SpherePoint n))) _)
    _ ≤ ∑ c ∈ C, ((μ : Measure (SpherePoint n)).real (capAround c theta)) := by
          simpa using
            MeasureTheory.measureReal_biUnion_finset_le
              (μ := (μ : Measure (SpherePoint n))) C (fun c => capAround c theta)
    _ = ∑ c ∈ C, capMeasure n theta := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          exact sphereProbabilityMeasure_real_capAround_eq_capMeasure hn c htheta0 htheta_pi2
    _ = (C.card : ℝ) * capMeasure n theta := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- The covering number satisfies the same measure lower bound. -/
theorem one_le_sphericalCapCoveringNumber_mul_capMeasure
    {n : ℕ} (hn : 2 ≤ n) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta_pi2 : theta ≤ Real.pi / 2) :
    1 ≤ (sphericalCapCoveringNumber n theta : ℝ) * capMeasure n theta := by
  rcases exists_cover_card_sphericalCapCoveringNumber (n := n) htheta0 with ⟨C, hC, hcard⟩
  have h := one_le_card_mul_capMeasure_of_sphericalCapCover
    (n := n) hn htheta0.le htheta_pi2 hC
  simpa [hcard] using h

/-- A crude upper bound for consecutive sphere-area ratios. -/
theorem sphereArea_ratio_upper_bound (m : ℕ) :
    sphereArea m / sphereArea (m + 1) ≤ (m + 1 : ℝ) := by
  refine Nat.twoStepInduction
    (P := fun m => sphereArea m / sphereArea (m + 1) ≤ (m + 1 : ℝ)) ?_ ?_ ?_ m
  · have hbase : sphereArea 0 / sphereArea 1 ≤ (((0 : ℕ) + 1 : ℕ) : ℝ) := by
      rw [sphereArea_zero, sphereArea_one]
      have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
      calc
        2 / (2 * Real.pi) = 1 / Real.pi := by field_simp [Real.pi_ne_zero]
        _ ≤ (((0 : ℕ) + 1 : ℕ) : ℝ) := by
              calc
                1 / Real.pi ≤ Real.pi / Real.pi := by
                  exact div_le_div_of_nonneg_right hpi Real.pi_pos.le
                _ = (((0 : ℕ) + 1 : ℕ) : ℝ) := by
                  field_simp [Real.pi_ne_zero]
                  norm_num
    simpa [sphereArea, zero_add] using hbase
  · have hbase : sphereArea 1 / sphereArea 2 ≤ (((1 : ℕ) + 1 : ℕ) : ℝ) := by
      have h2 : sphereArea 2 = 4 * Real.pi := by
        rw [sphereArea_rec_two 0, sphereArea_zero]
        ring
      rw [sphereArea_one, h2]
      calc
        (2 * Real.pi) / (4 * Real.pi) = (1 / 2 : ℝ) := by
          field_simp [Real.pi_ne_zero]
          norm_num
        _ ≤ (((1 : ℕ) + 1 : ℕ) : ℝ) := by norm_num
    simpa [sphereArea, one_add_one_eq_two] using hbase
  · intro k hk _hk1
    have hstep :
        sphereArea (k + 2) / sphereArea (k + 3) =
          ((k + 2 : ℝ) / (k + 1)) * (sphereArea k / sphereArea (k + 1)) := by
      rw [sphereArea_rec_two k, sphereArea_rec_two (k + 1)]
      have hk1 : ((k + 1 : ℝ) : ℝ) ≠ 0 := by positivity
      have hk2 : ((k + 2 : ℝ) : ℝ) ≠ 0 := by positivity
      have hsk : sphereArea k ≠ 0 := (sphereArea_pos k).ne'
      have hsk1 : sphereArea (k + 1) ≠ 0 := (sphereArea_pos (k + 1)).ne'
      field_simp [hk1, hk2, hsk, hsk1]
      norm_num [Nat.cast_add]
      ring_nf
    rw [hstep]
    have hfac_nonneg : 0 ≤ ((k + 2 : ℝ) / (k + 1)) := by positivity
    calc
      ((k + 2 : ℝ) / (k + 1)) * (sphereArea k / sphereArea (k + 1))
        ≤ ((k + 2 : ℝ) / (k + 1)) * (k + 1 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hk hfac_nonneg
      _ = (k + 2 : ℝ) := by
            have hk1 : ((k + 1 : ℝ) : ℝ) ≠ 0 := by positivity
            field_simp [hk1]
      _ ≤ ((k + 2 : ℕ) : ℝ) + 1 := by norm_num

/-- An exponentially sharp but polynomially lossy upper bound for cap measure in
the range used for Wyner's lower bound. -/
theorem capMeasure_upper_bound
    {n : ℕ} (hn : 2 ≤ n) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta_pi2 : theta < Real.pi / 2) :
    capMeasure n theta ≤
      (n - 1 : ℝ) * theta * Real.sin theta ^ (n - 2) := by
  have htheta0' : 0 ≤ theta := htheta0.le
  rw [capMeasure_eq_mul_intervalIntegral_sin_pow n hn theta htheta0' htheta_pi2]
  have hratio :
      sphereArea (n - 2) / sphereArea (n - 1) ≤ (n - 1 : ℝ) := by
    have hratio0 := sphereArea_ratio_upper_bound (n - 2)
    have hsub : n - 2 + 1 = n - 1 := by omega
    have hcast : (((n - 2 : ℕ) : ℝ) + 1) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn]
      ring
    simpa [hsub, hcast] using hratio0
  have hsintheta_nonneg : 0 ≤ Real.sin theta := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> linarith [Real.pi_pos, htheta_pi2]
  have hintegral_nonneg :
      0 ≤ ∫ t in (0 : ℝ)..theta, Real.sin t ^ (n - 2) := by
    refine intervalIntegral.integral_nonneg htheta0' ?_
    intro t ht
    have hs : 0 ≤ Real.sin t := by
      apply Real.sin_nonneg_of_mem_Icc
      exact ⟨ht.1, by linarith [ht.2, htheta_pi2, Real.pi_pos]⟩
    exact pow_nonneg hs (n - 2)
  have hintegral_le :
      ∫ t in (0 : ℝ)..theta, Real.sin t ^ (n - 2) ≤
        theta * Real.sin theta ^ (n - 2) := by
    have hmono :
        ∀ t ∈ Set.Icc (0 : ℝ) theta,
          Real.sin t ^ (n - 2) ≤ Real.sin theta ^ (n - 2) := by
      intro t ht
      have ht_nonneg : 0 ≤ t := ht.1
      have ht_le_pi2 : t ≤ Real.pi / 2 := by linarith [ht.2, htheta_pi2]
      have hsint_nonneg : 0 ≤ Real.sin t :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [ht_nonneg],
          by linarith [ht_le_pi2, Real.pi_pos]⟩
      have hsin_le : Real.sin t ≤ Real.sin theta := by
        exact Real.monotoneOn_sin
          ⟨by linarith [ht_nonneg, Real.pi_pos],
            by linarith [ht_le_pi2]⟩
          ⟨by linarith [htheta0, Real.pi_pos],
            by linarith [htheta_pi2]⟩ ht.2
      exact pow_le_pow_left₀ hsint_nonneg hsin_le (n - 2)
    calc
      ∫ t in (0 : ℝ)..theta, Real.sin t ^ (n - 2)
        ≤ ∫ t in (0 : ℝ)..theta, Real.sin theta ^ (n - 2) := by
            refine intervalIntegral.integral_mono_on htheta0' ?_ ?_ hmono
            · exact (continuous_sin.pow (n - 2)).intervalIntegrable _ _
            · exact _root_.intervalIntegrable_const
      _ = theta * Real.sin theta ^ (n - 2) := by
            simp [intervalIntegral.integral_const, smul_eq_mul]
  have hright_nonneg : 0 ≤ theta * Real.sin theta ^ (n - 2) :=
    mul_nonneg htheta0.le (pow_nonneg hsintheta_nonneg (n - 2))
  calc
    (sphereArea (n - 2) / sphereArea (n - 1)) *
        ∫ t in (0 : ℝ)..theta, Real.sin t ^ (n - 2)
      ≤ (sphereArea (n - 2) / sphereArea (n - 1)) *
          (theta * Real.sin theta ^ (n - 2)) := by
            exact mul_le_mul_of_nonneg_left hintegral_le
              (div_nonneg (sphereArea_nonneg _) (sphereArea_nonneg _))
    _ ≤ (n - 1 : ℝ) * (theta * Real.sin theta ^ (n - 2)) := by
          exact mul_le_mul_of_nonneg_right hratio hright_nonneg
    _ = (n - 1 : ℝ) * theta * Real.sin theta ^ (n - 2) := by ring

end OptimalAlphabets
