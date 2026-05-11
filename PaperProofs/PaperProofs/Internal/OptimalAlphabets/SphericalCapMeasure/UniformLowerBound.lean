import PaperProofs.Internal.OptimalAlphabets.SphericalCapMeasure.LowerBound

/-!
# OptimalAlphabets.SphericalCapMeasure.UniformLowerBound

Auxiliary lemmas for spherical caps centered at arbitrary points.
-/

noncomputable section

open Set Filter Topology Real Metric MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace OptimalAlphabets

/-- The spherical cap of angular radius `a` around the sphere point `v`. -/
def capAround {n : ℕ} (v : SpherePoint n) (a : ℝ) : Set (SpherePoint n) :=
  {x | InnerProductGeometry.angle x.1 v.1 ≤ a}

@[simp]
theorem mem_capAround {n : ℕ} {v x : SpherePoint n} {a : ℝ} :
    x ∈ capAround v a ↔ InnerProductGeometry.angle x.1 v.1 ≤ a :=
  Iff.rfl

@[simp]
theorem norm_spherePoint {n : ℕ} (x : SpherePoint n) :
    ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have hx := x.2
  rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx

/-- The reflection sending `e₁` to the sphere point `v`. -/
def capCenterReflection {n : ℕ} (v : SpherePoint n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Submodule.reflection (ℝ ∙ (e1Vec n - v.1))ᗮ

theorem capCenterReflection_map_e1Vec {n : ℕ} (hn : 0 < n) (v : SpherePoint n) :
    capCenterReflection v (e1Vec n) = v.1 := by
  have hvnorm : ‖v.1‖ = 1 := norm_spherePoint v
  have heq : ‖e1Vec n‖ = ‖v.1‖ := by
    rw [norm_e1Vec hn, hvnorm]
  simpa [capCenterReflection] using
    (Submodule.reflection_sub (v := e1Vec n) (w := v.1) heq)

theorem capCenterReflection_symm_apply_v {n : ℕ} (hn : 0 < n) (v : SpherePoint n) :
    (capCenterReflection v).symm v.1 = e1Vec n := by
  have hmap := capCenterReflection_map_e1Vec hn v
  simpa using (congrArg (capCenterReflection v).symm hmap).symm

theorem image_capSet_eq_capAround {n : ℕ} (hn : 0 < n) (v : SpherePoint n) (a : ℝ) :
    capCenterReflection v '' ((↑) '' capSet n a) = ((↑) '' capAround v a) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨⟨capCenterReflection v z.1, ?_⟩, ?_, rfl⟩
    · rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact ((capCenterReflection v).norm_map z.1).trans (norm_spherePoint z)
    · have hangle :
          InnerProductGeometry.angle ((capCenterReflection v) z.1)
            ((capCenterReflection v) (e1Vec n)) ≤ a := by
        calc
          InnerProductGeometry.angle ((capCenterReflection v) z.1)
              ((capCenterReflection v) (e1Vec n))
            = InnerProductGeometry.angle z.1 (e1Vec n) := by
                simpa using
                  ((capCenterReflection v).toLinearIsometry.angle_map z.1 (e1Vec n))
          _ ≤ a := hz
      simpa [capCenterReflection_map_e1Vec hn v] using hangle
  · rintro ⟨x', hx', rfl⟩
    refine ⟨(capCenterReflection v).symm x'.1, ?_, by simp⟩
    refine ⟨⟨(capCenterReflection v).symm x'.1, ?_⟩, ?_, rfl⟩
    · rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact ((capCenterReflection v).symm.norm_map x'.1).trans (norm_spherePoint x')
    · have hangle :
          InnerProductGeometry.angle ((capCenterReflection v).symm x'.1)
            ((capCenterReflection v).symm v.1) ≤ a := by
        calc
          InnerProductGeometry.angle ((capCenterReflection v).symm x'.1)
              ((capCenterReflection v).symm v.1)
            = InnerProductGeometry.angle x'.1 v.1 := by
                simpa using
                  ((capCenterReflection v).symm.toLinearIsometry.angle_map x'.1 v.1)
          _ ≤ a := hx'
      simpa [capCenterReflection_symm_apply_v hn v] using hangle

theorem preimage_capAroundCone_eq_capCone
    {n : ℕ} (hn : 0 < n) (v : SpherePoint n) (a : ℝ) :
    capCenterReflection v ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' capAround v a)) =
      Set.Ioo (0 : ℝ) 1 • ((↑) '' capSet n a) := by
  ext x
  constructor
  · intro hx
    rw [← image_capSet_eq_capAround hn v a] at hx
    rcases hx with ⟨r, hr, y, hy, hxy⟩
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨r, hr, z, hz, ?_⟩
    apply (capCenterReflection v).injective
    simpa using hxy
  · rintro ⟨r, hr, y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨r, hr, capCenterReflection v z.1, ?_, ?_⟩
    · refine ⟨⟨capCenterReflection v z.1, ?_⟩, ?_, rfl⟩
      · rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
        exact ((capCenterReflection v).norm_map z.1).trans (norm_spherePoint z)
      · have hangle :
            InnerProductGeometry.angle ((capCenterReflection v) z.1)
              ((capCenterReflection v) (e1Vec n)) ≤ a := by
          calc
            InnerProductGeometry.angle ((capCenterReflection v) z.1)
                ((capCenterReflection v) (e1Vec n))
              = InnerProductGeometry.angle z.1 (e1Vec n) := by
                  simpa using
                    ((capCenterReflection v).toLinearIsometry.angle_map z.1 (e1Vec n))
            _ ≤ a := hz
        simpa [capCenterReflection_map_e1Vec hn v] using hangle
    · exact ((capCenterReflection v).map_smul r z.1).symm

theorem measurableSet_capAround {n : ℕ} (v : SpherePoint n)
    {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    MeasurableSet (capAround v a) := by
  have hcont :
      Continuous fun x : SpherePoint n =>
        inner ℝ (x : EuclideanSpace ℝ (Fin n)) v.1 := by
    fun_prop
  have hcap :
      capAround v a = {x : SpherePoint n | Real.cos a ≤ inner ℝ (x : EuclideanSpace ℝ (Fin n)) v.1} := by
    ext x
    have hxnorm : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_spherePoint x
    have hvnorm : ‖v.1‖ = 1 := norm_spherePoint v
    constructor
    · intro hx
      have hapi' : a ≤ Real.pi := by linarith [Real.pi_pos]
      have hcos :
          Real.cos a ≤ Real.cos (InnerProductGeometry.angle x.1 v.1) :=
        Real.cos_le_cos_of_nonneg_of_le_pi
          (InnerProductGeometry.angle_nonneg _ _) hapi' hx
      calc
        Real.cos a ≤ Real.cos (InnerProductGeometry.angle x.1 v.1) := hcos
        _ = inner ℝ x.1 v.1 := by
          rw [InnerProductGeometry.cos_angle, hxnorm, hvnorm]
          norm_num
    · intro hx
      have h_arccos :
          Real.arccos (inner ℝ x.1 v.1) ≤ Real.arccos (Real.cos a) :=
        Real.arccos_le_arccos hx
      have hacos : Real.arccos (Real.cos a) = a := by
        have hapi' : a ≤ Real.pi := by linarith [Real.pi_pos]
        exact Real.arccos_cos ha0 hapi'
      have hangle :
          InnerProductGeometry.angle x.1 v.1 = Real.arccos (inner ℝ x.1 v.1) := by
        simp [InnerProductGeometry.angle, hxnorm, hvnorm]
      change InnerProductGeometry.angle x.1 v.1 ≤ a
      rw [hangle]
      exact le_trans h_arccos hacos.le
  rw [hcap]
  exact (isClosed_le continuous_const hcont).measurableSet

theorem sphereSurfaceMeasure_capAround_eq_capSet
    {n : ℕ} (hn : 0 < n) (v : SpherePoint n)
    {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    (sphereSurfaceMeasure n).real (capAround v a) =
      (sphereSurfaceMeasure n).real (capSet n a) := by
  let coneAround : Set (EuclideanSpace ℝ (Fin n)) := Set.Ioo (0 : ℝ) 1 • ((↑) '' capAround v a)
  let coneCap : Set (EuclideanSpace ℝ (Fin n)) := Set.Ioo (0 : ℝ) 1 • ((↑) '' capSet n a)
  have hsAround : MeasurableSet (capAround v a) := measurableSet_capAround v ha0 hapi
  have hAround :
      (sphereSurfaceMeasure n).real (capAround v a) =
        n * (volume : Measure (EuclideanSpace ℝ (Fin n))).real coneAround := by
    simpa [sphereSurfaceMeasure, coneAround, measureReal_def, finrank_euclideanSpace_fin] using
      congrArg ENNReal.toReal
        (Measure.toSphere_apply' (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hsAround)
  have hCap :
      (sphereSurfaceMeasure n).real (capSet n a) =
        n * (volume : Measure (EuclideanSpace ℝ (Fin n))).real coneCap := by
    simpa [coneCap] using
      sphereSurfaceMeasure_capSet_eq_mul_volume_capCone (n := n) hn ha0 hapi
  have hpre :
      capCenterReflection v ⁻¹' coneAround = coneCap := by
    simpa [coneAround, coneCap] using preimage_capAroundCone_eq_capCone hn v a
  have hpres :
      MeasurePreserving (capCenterReflection v).toMeasurableEquiv
        (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa using
      ((capCenterReflection v).measurePreserving :
        MeasurePreserving (capCenterReflection v)
          (volume : Measure (EuclideanSpace ℝ (Fin n)))
          (volume : Measure (EuclideanSpace ℝ (Fin n))))
  have hvol :
      (volume : Measure (EuclideanSpace ℝ (Fin n))) coneAround =
        (volume : Measure (EuclideanSpace ℝ (Fin n))) coneCap := by
    have hmp :
        (volume : Measure (EuclideanSpace ℝ (Fin n)))
            (((capCenterReflection v).toMeasurableEquiv) ⁻¹' coneAround) =
          (volume : Measure (EuclideanSpace ℝ (Fin n))) coneAround := by
      simpa using hpres.measure_preimage_equiv coneAround
    have hpre' :
        (volume : Measure (EuclideanSpace ℝ (Fin n)))
            (((capCenterReflection v).toMeasurableEquiv) ⁻¹' coneAround) =
          (volume : Measure (EuclideanSpace ℝ (Fin n))) coneCap := by
      simpa using
        congrArg (fun s : Set (EuclideanSpace ℝ (Fin n)) =>
          (volume : Measure (EuclideanSpace ℝ (Fin n))) s) hpre
    exact hmp.symm.trans hpre'
  have hvolReal :
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real coneAround =
        (volume : Measure (EuclideanSpace ℝ (Fin n))).real coneCap :=
    congrArg ENNReal.toReal hvol
  rw [hAround, hCap, hvolReal]

theorem sphereSurfaceMeasure_ne_zero {n : ℕ} (hn : 0 < n) :
    sphereSurfaceMeasure n ≠ 0 := by
  letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    infer_instance
  change ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) ≠ 0
  exact Measure.toSphere_ne_zero (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))

/-- The normalized surface measure on `S^(n-1)`. -/
noncomputable def sphereProbabilityMeasure (n : ℕ) (hn : 0 < n) :
    ProbabilityMeasure (SpherePoint n) := by
  letI : NeZero (sphereSurfaceMeasure n) := ⟨sphereSurfaceMeasure_ne_zero hn⟩
  letI : IsFiniteMeasure (sphereSurfaceMeasure n) := by
    dsimp [sphereSurfaceMeasure]
    infer_instance
  exact ⟨((sphereSurfaceMeasure n) Set.univ)⁻¹ • sphereSurfaceMeasure n,
    show IsProbabilityMeasure (((sphereSurfaceMeasure n) Set.univ)⁻¹ • sphereSurfaceMeasure n) from
      inferInstance⟩

theorem sphereProbabilityMeasure_real_apply
    {n : ℕ} (hn : 0 < n) (s : Set (SpherePoint n)) :
    ((sphereProbabilityMeasure n hn : Measure (SpherePoint n)).real s) =
      (sphereSurfaceMeasure n).real s / sphereArea (n - 1) := by
  letI : NeZero (sphereSurfaceMeasure n) := ⟨sphereSurfaceMeasure_ne_zero hn⟩
  letI : IsFiniteMeasure (sphereSurfaceMeasure n) := by
    dsimp [sphereSurfaceMeasure]
    infer_instance
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  have hrealuniv :
      (sphereSurfaceMeasure n).real Set.univ = sphereArea (n - 1) := by
    rw [sphereArea_def, hsub]
  have huniv :
      (sphereSurfaceMeasure n) Set.univ = ENNReal.ofReal (sphereArea (n - 1)) := by
    rw [← ofReal_measureReal (μ := sphereSurfaceMeasure n) (s := Set.univ)
      (h := (measure_lt_top (sphereSurfaceMeasure n) Set.univ).ne)]
    rw [hrealuniv]
  unfold sphereProbabilityMeasure
  simp [measureReal_ennreal_smul_apply, huniv, div_eq_mul_inv, mul_comm]

theorem sphereProbabilityMeasure_real_capAround_eq_capMeasure
    {n : ℕ} (hn : 2 ≤ n) (v : SpherePoint n) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    ((sphereProbabilityMeasure n (show 0 < n by omega) : Measure (SpherePoint n)).real (capAround v a)) =
      capMeasure n a := by
  have hn0 : 0 < n := by omega
  calc
    ((sphereProbabilityMeasure n hn0 : Measure (SpherePoint n)).real (capAround v a))
      = (sphereSurfaceMeasure n).real (capAround v a) / sphereArea (n - 1) :=
          sphereProbabilityMeasure_real_apply hn0 (capAround v a)
    _ = (sphereSurfaceMeasure n).real (capSet n a) / sphereArea (n - 1) := by
          rw [sphereSurfaceMeasure_capAround_eq_capSet hn0 v ha0 hapi]
    _ = capMeasure n a := by
          symm
          exact capMeasure_eq_div_surfaceMeasure hn0 a

theorem sphereArea_rec_two (m : ℕ) :
    sphereArea (m + 2) = (2 * Real.pi / (m + 1)) * sphereArea m := by
  have hball :
      (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).real (Metric.ball 0 1) =
        Real.sqrt Real.pi ^ (m + 1) / Real.Gamma (((m + 1 : ℝ) / 2) + 1) := by
    have hnonneg :
        0 ≤ Real.sqrt Real.pi ^ (m + 1) / Real.Gamma (((m + 1 : ℝ) / 2) + 1) := by
      positivity
    rw [Measure.real, EuclideanSpace.volume_ball]
    simp [hnonneg]
  have hball' :
      (volume : Measure (EuclideanSpace ℝ (Fin (m + 3)))).real (Metric.ball 0 1) =
        Real.sqrt Real.pi ^ (m + 3) / Real.Gamma (((m + 3 : ℝ) / 2) + 1) := by
    have hnonneg :
        0 ≤ Real.sqrt Real.pi ^ (m + 3) / Real.Gamma (((m + 3 : ℝ) / 2) + 1) := by
      positivity
    rw [Measure.real, EuclideanSpace.volume_ball]
    simp [hnonneg]
  have hpow :
      Real.sqrt Real.pi ^ (m + 3) = Real.pi * Real.sqrt Real.pi ^ (m + 1) := by
    have hsqrt :
        Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := by
      nlinarith [Real.sq_sqrt Real.pi_nonneg]
    calc
      Real.sqrt Real.pi ^ (m + 3)
          = Real.sqrt Real.pi ^ (m + 1) * (Real.sqrt Real.pi * Real.sqrt Real.pi) := by
              rw [show m + 3 = (m + 1) + 2 by omega, pow_add, pow_two]
      _ = Real.sqrt Real.pi ^ (m + 1) * Real.pi := by rw [hsqrt]
      _ = Real.pi * Real.sqrt Real.pi ^ (m + 1) := by ring
  have hgamma :
      Real.Gamma (((m + 3 : ℝ) / 2) + 1) =
        ((m + 3 : ℝ) / 2) * Real.Gamma (((m + 1 : ℝ) / 2) + 1) := by
    have hm : (((m + 3 : ℝ) / 2) : ℝ) ≠ 0 := by positivity
    calc
      Real.Gamma (((m + 3 : ℝ) / 2) + 1)
        = ((m + 3 : ℝ) / 2) * Real.Gamma ((m + 3 : ℝ) / 2) := by
            simpa using Real.Gamma_add_one (s := (((m + 3 : ℝ) / 2) : ℝ)) hm
      _ = ((m + 3 : ℝ) / 2) * Real.Gamma (((m + 1 : ℝ) / 2) + 1) := by
            congr 1
            ring_nf
  rw [sphereArea_eq_finrank_mul_volume_ball, sphereArea_eq_finrank_mul_volume_ball]
  rw [hball', hball, hpow, hgamma]
  have hm1 : ((m + 1 : ℝ) : ℝ) ≠ 0 := by positivity
  have hm3 : (((m + 3 : ℝ) / 2) : ℝ) ≠ 0 := by positivity
  have hG : Real.Gamma (((m + 1 : ℝ) / 2) + 1) ≠ 0 := by positivity
  field_simp [hm1, hm3, hG]
  norm_num [Nat.cast_add]
  ring_nf

theorem sphereArea_zero : sphereArea 0 = 2 := by
  rw [sphereArea_eq_finrank_mul_volume_ball]
  norm_num
  have hvol :
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) = ENNReal.ofReal 2 := by
    simpa using
      (InnerProductSpace.volume_ball_of_dim_odd
        (E := EuclideanSpace ℝ (Fin 1)) (k := 0) (by simp)
        (0 : EuclideanSpace ℝ (Fin 1)) (1 : ℝ))
  have hvolreal :
      (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) = 2 := by
    rw [Measure.real_def, hvol]
    norm_num
  rw [hvolreal]

theorem sphereArea_one : sphereArea 1 = 2 * Real.pi := by
  rw [sphereArea_eq_finrank_mul_volume_ball]
  norm_num
  have hvol :
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) = ENNReal.ofReal Real.pi := by
    rw [EuclideanSpace.volume_ball_fin_two]
    norm_num
  have hvolreal :
      (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) = Real.pi := by
    rw [Measure.real_def, hvol]
    exact ENNReal.toReal_ofReal Real.pi_nonneg
  rw [hvolreal]

theorem sphereArea_ratio_lower_bound (m : ℕ) :
    1 / Real.pi ≤ sphereArea m / sphereArea (m + 1) := by
  refine Nat.twoStepInduction
    (P := fun m => 1 / Real.pi ≤ sphereArea m / sphereArea (m + 1)) ?_ ?_ ?_ m
  · change 1 / Real.pi ≤ sphereArea 0 / sphereArea 1
    rw [sphereArea_zero, sphereArea_one]
    field_simp [Real.pi_ne_zero]
    norm_num
  · have h2 : sphereArea 2 = 4 * Real.pi := by
      rw [sphereArea_rec_two 0, sphereArea_zero]
      ring
    change 1 / Real.pi ≤ sphereArea 1 / sphereArea 2
    rw [sphereArea_one, h2]
    field_simp [Real.pi_ne_zero]
    have htwo_lt_pi : (2 : ℝ) < Real.pi := by
      linarith [Real.pi_gt_three]
    nlinarith [htwo_lt_pi]
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
    have hfac : 1 ≤ ((k + 2 : ℝ) / (k + 1)) := by
      have hk1 : (0 : ℝ) < k + 1 := by positivity
      have hk12 : (k + 1 : ℝ) ≤ k + 2 := by nlinarith
      exact (one_le_div hk1).2 hk12
    have hratio_nonneg : 0 ≤ sphereArea k / sphereArea (k + 1) := by
      exact div_nonneg (sphereArea_nonneg k) (sphereArea_nonneg (k + 1))
    calc
      1 / Real.pi ≤ sphereArea k / sphereArea (k + 1) := hk
      _ ≤ ((k + 2 : ℝ) / (k + 1)) * (sphereArea k / sphereArea (k + 1)) := by
            have := mul_le_mul_of_nonneg_right hfac hratio_nonneg
            simpa using this

theorem capMeasure_uniform_lower_bound
    (n : ℕ) (hn : 2 ≤ n) (a δ : ℝ)
    (ha0 : 0 < a) (hapi : a < Real.pi / 2)
    (hδ0 : 0 < δ) (hδ : δ < a) :
    capMeasure n a ≥ (δ / Real.pi) * Real.sin (a - δ) ^ n := by
  have hbase :=
    capMeasure_lower_bound n hn a δ ha0 hapi hδ0 hδ
  have hratio :
      1 / Real.pi ≤ sphereArea (n - 2) / sphereArea (n - 1) := by
    have hsub : n - 2 + 1 = n - 1 := by omega
    simpa [hsub] using sphereArea_ratio_lower_bound (n - 2)
  set s := Real.sin (a - δ)
  have hs_nonneg : 0 ≤ s := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor
    · linarith
    · linarith [Real.pi_pos, hapi]
  have hs_le_one : s ≤ 1 := by
    simpa [s] using Real.sin_le_one (a - δ)
  have hpow :
      s ^ n ≤ s ^ (n - 2) := by
    have hnsub : n - 2 ≤ n := Nat.sub_le _ _
    exact pow_le_pow_of_le_one hs_nonneg hs_le_one hnsub
  have hstep1 :
      (δ / Real.pi) * s ^ n ≤ (δ / Real.pi) * s ^ (n - 2) := by
    exact mul_le_mul_of_nonneg_left hpow (div_nonneg hδ0.le Real.pi_pos.le)
  have hstep2 :
      (δ / Real.pi) * s ^ (n - 2) ≤
        ((sphereArea (n - 2) / sphereArea (n - 1)) * δ) * s ^ (n - 2) := by
    have hδ_nonneg : 0 ≤ δ := hδ0.le
    have hleft :
        δ / Real.pi ≤ (sphereArea (n - 2) / sphereArea (n - 1)) * δ := by
      have := mul_le_mul_of_nonneg_right hratio hδ_nonneg
      calc
        δ / Real.pi = (1 / Real.pi) * δ := by
          field_simp [Real.pi_ne_zero]
        _ ≤ (sphereArea (n - 2) / sphereArea (n - 1)) * δ := this
    exact mul_le_mul_of_nonneg_right hleft (pow_nonneg hs_nonneg (n - 2))
  have hbase' :
      ((sphereArea (n - 2) / sphereArea (n - 1)) * δ) * s ^ (n - 2) ≤ capMeasure n a := by
    subst s
    exact hbase
  calc
    (δ / Real.pi) * s ^ n ≤ (δ / Real.pi) * s ^ (n - 2) := hstep1
    _ ≤ ((sphereArea (n - 2) / sphereArea (n - 1)) * δ) * s ^ (n - 2) := hstep2
    _ ≤ capMeasure n a := hbase'

end OptimalAlphabets
