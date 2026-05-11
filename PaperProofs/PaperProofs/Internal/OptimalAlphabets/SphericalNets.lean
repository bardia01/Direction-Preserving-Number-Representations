import PaperProofs.Internal.OptimalAlphabets.SphericalCodes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# OptimalAlphabets.SphericalNets

Finite angular nets on the unit sphere with exponential cardinality bounds.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace OptimalAlphabets

@[simp]
theorem norm_spherePoint' {n : ℕ} (x : SpherePoint n) :
    ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have hx := x.2
  rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx

/-- If the angular distance between two sphere points is larger than `ε`, then their ambient
Euclidean distance is larger than `ε / 2`, provided `ε ≤ 1`. -/
theorem half_eps_lt_dist_of_angle_gt
    {n : ℕ} {u v : SpherePoint n} {ε : ℝ}
    (hε0 : 0 < ε) (_hε1 : ε ≤ 1)
    (hangle : ε < InnerProductGeometry.angle u.1 v.1) :
    ε / 2 < dist u v := by
  let θ := InnerProductGeometry.angle u.1 v.1
  have hε1 : ε ≤ 1 := _hε1
  have hθ_nonneg : 0 ≤ θ := InnerProductGeometry.angle_nonneg _ _
  have hθ_le_pi : θ ≤ Real.pi := InnerProductGeometry.angle_le_pi _ _
  have hε_half_mem : ε / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · have : 0 ≤ ε / 2 := by positivity
      linarith
    · have hε_pi : ε / 2 ≤ Real.pi / 2 := by
        linarith [hε1, Real.pi_gt_three]
      exact hε_pi
  have hθ_half_mem : θ / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith
    · linarith
  have hsin_lt :
      Real.sin (ε / 2) < Real.sin (θ / 2) := by
    exact Real.strictMonoOn_sin hε_half_mem hθ_half_mem (by linarith)
  have hquarter_le_sin :
      ε / 4 ≤ Real.sin (ε / 2) := by
    have hhalf_nonneg : 0 ≤ ε / 2 := by positivity
    have hhalf_le_pi2 : ε / 2 ≤ Real.pi / 2 := by
      linarith [hε1, Real.pi_gt_three]
    have hmul : (2 / Real.pi) * (ε / 2) ≤ Real.sin (ε / 2) :=
      Real.mul_le_sin hhalf_nonneg hhalf_le_pi2
    have hmul'' : ε / 4 ≤ (2 / Real.pi) * (ε / 2) := by
      have hcoeff : (1 / 4 : ℝ) ≤ 1 / Real.pi := by
        simpa using one_div_le_one_div_of_le Real.pi_pos Real.pi_le_four
      have hmul' : ε * (1 / 4 : ℝ) ≤ ε * (1 / Real.pi) := by
        exact mul_le_mul_of_nonneg_left hcoeff hε0.le
      calc
        ε / 4 = ε * (1 / 4 : ℝ) := by ring
        _ ≤ ε * (1 / Real.pi) := hmul'
        _ = (2 / Real.pi) * (ε / 2) := by ring
    exact hmul''.trans hmul
  have hquarter_lt : ε / 4 < Real.sin (θ / 2) :=
    by simpa [div_eq_mul_inv, mul_assoc] using lt_of_le_of_lt hquarter_le_sin hsin_lt
  have hnorm_sq :
      dist u v * dist u v = 4 * Real.sin (θ / 2) * Real.sin (θ / 2) := by
    have hu : ‖u.1‖ = 1 := norm_spherePoint' u
    have hv : ‖v.1‖ = 1 := norm_spherePoint' v
    change ‖u.1 - v.1‖ * ‖u.1 - v.1‖ = 4 * Real.sin (θ / 2) * Real.sin (θ / 2)
    calc
      ‖u.1 - v.1‖ * ‖u.1 - v.1‖
          = ‖u.1‖ * ‖u.1‖ + ‖v.1‖ * ‖v.1‖
              - 2 * ‖u.1‖ * ‖v.1‖ * Real.cos θ := by
                simpa [θ] using
                  InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
                    u.1 v.1
      _ = 2 - 2 * Real.cos θ := by rw [hu, hv]; ring
      _ = 4 * Real.sin (θ / 2) * Real.sin (θ / 2) := by
            rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
            have hhalf : 2 * (θ / 2) / 2 = θ / 2 := by ring
            rw [hhalf]
            nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hdist_nonneg : 0 ≤ dist u v := dist_nonneg
  have hsin_nonneg : 0 ≤ Real.sin (θ / 2) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> linarith
  nlinarith

/-- A Euclidean distance bound of `ε / 2` implies an angular distance bound of `ε`
for sphere points, provided `ε ≤ 1`. -/
theorem angle_le_of_dist_le_half_eps
    {n : ℕ} {u v : SpherePoint n} {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hdist : dist u v ≤ ε / 2) :
    InnerProductGeometry.angle u.1 v.1 ≤ ε := by
  by_contra hgt
  have : ε / 2 < dist u v :=
    half_eps_lt_dist_of_angle_gt hε0 hε1 (lt_of_not_ge hgt)
  linarith

/-- A separated finite subset of the unit sphere has size at most `(5 / ε)^n`. -/
theorem spherePoint_finset_card_le_of_separated
    {n : ℕ} (s : Finset (SpherePoint n)) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hsep : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ε / 2 < dist u v) :
    (s.card : ℝ) ≤ (5 / ε) ^ n := by
  let E := EuclideanSpace ℝ (Fin n)
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := ε / 4
  let ρ : ℝ := 1 + ε / 4
  have hδ_pos : 0 < δ := by positivity
  have hρ_pos : 0 < ρ := by positivity
  set A : Set E := ⋃ c ∈ s, Metric.ball (c.1 : E) δ with hA
  have hdisj :
      Set.Pairwise (s : Set (SpherePoint n))
        (fun c d => Disjoint (Metric.ball (c.1 : E) δ) (Metric.ball (d.1 : E) δ)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    have hdist : ε / 2 < dist c d := hsep c hc d hd hcd
    have hdelta : δ + δ = ε / 2 := by
      simp [δ]
      ring
    change δ + δ ≤ dist c.1 d.1
    simpa [hdelta, Subtype.dist_eq, dist_eq_norm] using hdist.le
  have hA_subset : A ⊆ Metric.ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    have hxnorm : dist x.1 0 ≤ 1 := by
      rw [dist_eq_norm, sub_zero]
      exact (norm_spherePoint' x).le
    calc
      δ + dist x.1 0 ≤ δ + 1 := by
        linarith
      _ ≤ ρ := by
        dsimp [δ, ρ]
        linarith
  have hmeasure :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ n) * μ (Metric.ball 0 1) ≤
        ENNReal.ofReal (ρ ^ n) * μ (Metric.ball 0 1) := by
    have hsum :
        ∑ x ∈ s, μ (Metric.ball (x.1 : E) δ) =
          (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ n) * μ (Metric.ball (0 : E) 1) := by
      calc
        ∑ x ∈ s, μ (Metric.ball (x.1 : E) δ)
            = ∑ x ∈ s, ENNReal.ofReal (δ ^ n) * μ (Metric.ball (0 : E) 1) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                simpa [E] using (μ.addHaar_ball_of_pos (x.1 : E) hδ_pos)
        _ = (s.card : ℝ≥0∞) * (ENNReal.ofReal (δ ^ n) * μ (Metric.ball (0 : E) 1)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
        _ = (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ n) * μ (Metric.ball (0 : E) 1) := by
              rw [mul_assoc]
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ n) * μ (Metric.ball 0 1)
          = μ A := by
              rw [hA, measure_biUnion_finset hdisj fun _ _ => measurableSet_ball]
              exact hsum.symm
      _ ≤ μ (Metric.ball (0 : E) ρ) := measure_mono hA_subset
      _ = ENNReal.ofReal (ρ ^ n) * μ (Metric.ball 0 1) := by
            simpa [E] using (μ.addHaar_ball_of_pos (0 : E) hρ_pos)
  have hmeasure' : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ n) ≤ ENNReal.ofReal (ρ ^ n) := by
    exact
      (ENNReal.mul_le_mul_iff_left
        (measure_ball_pos (μ := μ) (0 : E) zero_lt_one).ne'
        measure_ball_lt_top.ne).1 hmeasure
  have hmeasure_real : (s.card : ℝ) * δ ^ n ≤ ρ ^ n := by
    have hδpow_nonneg : 0 ≤ δ ^ n := by positivity
    have hmeasure_real' :
        ENNReal.ofReal ((s.card : ℝ) * δ ^ n) ≤ ENNReal.ofReal (ρ ^ n) := by
      simpa [ENNReal.ofReal_mul, hδpow_nonneg, mul_comm, mul_left_comm, mul_assoc] using hmeasure'
    exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hρ_pos.le n)).1 hmeasure_real'
  have hratio :
      (s.card : ℝ) ≤ (ρ / δ) ^ n := by
    have hδpow_pos : 0 < δ ^ n := pow_pos hδ_pos n
    have hratio' : (s.card : ℝ) ≤ ρ ^ n / δ ^ n := by
      exact (le_div_iff₀ hδpow_pos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmeasure_real)
    simpa [div_pow] using hratio'
  have hratio_le : ρ / δ ≤ 5 / ε := by
    have hcalc : ρ / δ = (4 + ε) / ε := by
      field_simp [ρ, δ, hε0.ne']
      ring
    rw [hcalc]
    have hnum : 4 + ε ≤ 5 := by linarith
    exact div_le_div_of_nonneg_right hnum hε0.le
  have hratio_nonneg : 0 ≤ ρ / δ := by positivity
  exact hratio.trans (pow_le_pow_left₀ hratio_nonneg hratio_le n)

/-- Existence of finite angular `ε`-nets on the unit sphere with cardinality bounded by
`(5 / ε)^n`. -/
theorem exists_finset_card_le_and_angle_cover
    (n : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : Finset (SpherePoint n),
      (∀ u : SpherePoint n, ∃ v ∈ N, InnerProductGeometry.angle u.1 v.1 ≤ ε) ∧
      (N.card : ℝ) ≤ (5 / ε) ^ n := by
  let r : ℝ≥0 := ⟨ε / 4, by positivity⟩
  have hr_ne : r ≠ 0 := by
    have hr_pos : (0 : ℝ≥0) < r := by
      change (0 : ℝ) < ε / 4
      positivity
    exact ne_of_gt hr_pos
  obtain ⟨C, -, hCfin, hCcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact (ε := r)
      (s := (Set.univ : Set (SpherePoint n))) hr_ne isCompact_univ
  have hExt_ne_top :
      Metric.externalCoveringNumber r (Set.univ : Set (SpherePoint n)) ≠ ⊤ := by
    refine ne_of_lt <| lt_of_le_of_lt hCcover.externalCoveringNumber_le_encard ?_
    exact hCfin.encard_lt_top
  have hPack_ne_top :
      Metric.packingNumber (2 * r) (Set.univ : Set (SpherePoint n)) ≠ ⊤ := by
    refine ne_of_lt <| lt_of_le_of_lt
      (Metric.packingNumber_two_mul_le_externalCoveringNumber r (Set.univ : Set (SpherePoint n))) ?_
    exact hExt_ne_top.lt_top
  let S := Metric.maximalSeparatedSet (2 * r) (Set.univ : Set (SpherePoint n))
  have hSfin : S.Finite := by
    apply Set.encard_lt_top_iff.mp
    rw [Metric.encard_maximalSeparatedSet (A := (Set.univ : Set (SpherePoint n))) hPack_ne_top]
    exact hPack_ne_top.lt_top
  let N : Finset (SpherePoint n) := hSfin.toFinset
  refine ⟨N, ?_, ?_⟩
  · intro u
    obtain ⟨v, hvS, hvdist⟩ :=
      Metric.isCover_maximalSeparatedSet (ε := 2 * r) (A := (Set.univ : Set (SpherePoint n)))
        hPack_ne_top (by simp : u ∈ (Set.univ : Set (SpherePoint n)))
    refine ⟨v, hSfin.mem_toFinset.mpr hvS, ?_⟩
    have hvdist' : dist u v ≤ (2 * r : ℝ) := by
      rw [dist_edist]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (by simpa using hvdist)
    have hvdist'' : dist u v ≤ ε / 2 := by
      have htwo : (2 * r : ℝ) = ε / 2 := by
        change 2 * (ε / 4) = ε / 2
        ring
      simpa [htwo] using hvdist'
    exact angle_le_of_dist_le_half_eps hε0 hε1 hvdist''
  · have hsep :
        ∀ u ∈ N, ∀ v ∈ N, u ≠ v → ε / 2 < dist u v := by
      intro u hu v hv huv
      have huS : u ∈ S := hSfin.mem_toFinset.mp hu
      have hvS : v ∈ S := hSfin.mem_toFinset.mp hv
      have hsep' :=
        Metric.isSeparated_maximalSeparatedSet
          (ε := 2 * r) (A := (Set.univ : Set (SpherePoint n))) huS hvS huv
      have : ENNReal.ofReal (ε / 2) < edist u v := by
        have htwo : ENNReal.ofReal (ε / 2) = (2 * r : ℝ≥0∞) := by
          calc
            ENNReal.ofReal (ε / 2) = ENNReal.ofReal (2 * (ε / 4)) := by congr 1; ring
            _ = ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (ε / 4) := by
                  rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
            _ = 2 * ENNReal.ofReal (ε / 4) := by norm_num
            _ = (2 * r : ℝ≥0∞) := by
                  congr 1
                  simpa [r] using
                    (ENNReal.ofReal_eq_coe_nnreal (show 0 ≤ ε / 4 by positivity))
        simpa [htwo] using hsep'
      have this' : ENNReal.ofReal (ε / 2) < ENNReal.ofReal (dist u v) := by
        simpa [edist_dist] using this
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 this'
    simpa [N] using spherePoint_finset_card_le_of_separated N hε0 hε1 hsep

end OptimalAlphabets
