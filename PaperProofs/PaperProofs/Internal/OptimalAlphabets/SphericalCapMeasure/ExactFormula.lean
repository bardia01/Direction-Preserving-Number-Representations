import PaperProofs.Internal.OptimalAlphabets.SphericalCapMeasure.Defs

/-!
# OptimalAlphabets.SphericalCapMeasure.ExactFormula

The exact spherical-cap formula.

The geometric proof is intended to be supplied via the polar-coordinate route described in the
project plan. For now the downstream lower-bound argument is isolated from that proof by exposing a
single theorem name.
-/

noncomputable section

open Set Filter Topology Real Metric MeasureTheory intervalIntegral
open scoped ENNReal NNReal Pointwise

namespace OptimalAlphabets

/-- Split `ℝ^(n+1)` into its first coordinate and the remaining `n` coordinates. -/
def splitFirstCoord (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ℝ × EuclideanSpace ℝ (Fin n) :=
  (x 0, show EuclideanSpace ℝ (Fin n) from WithLp.toLp 2 (fun i : Fin n => x i.succ))

/-- Reassemble a vector in `ℝ^(n+1)` from its first coordinate and tail. -/
def joinFirstCoord (n : ℕ) (u : ℝ × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  show EuclideanSpace ℝ (Fin (n + 1)) from
    WithLp.toLp 2 (Fin.cons u.1 fun i : Fin n => u.2 i)

@[simp]
theorem splitFirstCoord_fst_apply_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    (splitFirstCoord n x).1 = x 0 := rfl

@[simp]
theorem splitFirstCoord_snd_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    (splitFirstCoord n x).2 i = x i.succ := by
  simp [splitFirstCoord]

@[simp]
theorem joinFirstCoord_apply_zero (n : ℕ)
    (u : ℝ × EuclideanSpace ℝ (Fin n)) :
    joinFirstCoord n u 0 = u.1 := by
  simp [joinFirstCoord]

@[simp]
theorem joinFirstCoord_apply_succ (n : ℕ)
    (u : ℝ × EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    joinFirstCoord n u i.succ = u.2 i := by
  simp [joinFirstCoord]

@[simp]
theorem joinFirstCoord_splitFirstCoord (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    joinFirstCoord n (splitFirstCoord n x) = x := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [joinFirstCoord, splitFirstCoord]
  · intro j
    simp [joinFirstCoord, splitFirstCoord]

@[simp]
theorem splitFirstCoord_joinFirstCoord (n : ℕ) (u : ℝ × EuclideanSpace ℝ (Fin n)) :
    splitFirstCoord n (joinFirstCoord n u) = u := by
  refine Prod.ext ?_ ?_
  · simp [splitFirstCoord, joinFirstCoord]
  · ext i
    simp [splitFirstCoord, joinFirstCoord]

/-- The coordinate splitting equivalence `ℝ^(n+1) ≃ ℝ × ℝ^n`. -/
def splitFirstCoordEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ ℝ × EuclideanSpace ℝ (Fin n) where
  toFun := splitFirstCoord n
  invFun := joinFirstCoord n
  left_inv := joinFirstCoord_splitFirstCoord n
  right_inv := splitFirstCoord_joinFirstCoord n

@[simp]
theorem splitFirstCoordEquiv_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    splitFirstCoordEquiv n x = splitFirstCoord n x := rfl

@[simp]
theorem splitFirstCoordEquiv_symm_apply (n : ℕ) (u : ℝ × EuclideanSpace ℝ (Fin n)) :
    (splitFirstCoordEquiv n).symm u = joinFirstCoord n u := rfl

/-- The first-coordinate splitting map as a measurable equivalence. -/
def splitFirstCoordMeasurableEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin n) :=
  ((MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin n → ℝ))))

@[simp]
theorem splitFirstCoordMeasurableEquiv_apply (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    splitFirstCoordMeasurableEquiv n x = splitFirstCoord n x := by
  change (x.ofLp 0, WithLp.toLp 2 (Fin.tail x.ofLp)) = splitFirstCoord n x
  refine Prod.ext ?_ ?_
  · rfl
  · ext i
    simp [splitFirstCoord, Fin.tail]

theorem measurePreserving_splitFirstCoord (n : ℕ) :
    MeasurePreserving (splitFirstCoord n)
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))
      (volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))) := by
  let e₁ : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm
  let e₂ : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let e₃ : ℝ × (Fin n → ℝ) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin n) :=
    (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin n → ℝ))
  have h₁ : MeasurePreserving e₁
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))
      (volume : Measure (Fin (n + 1) → ℝ)) := by
    simpa [e₁] using (PiLp.volume_preserving_ofLp (Fin (n + 1)))
  have h₂ : MeasurePreserving e₂
      (volume : Measure (Fin (n + 1) → ℝ))
      (volume : Measure (ℝ × (Fin n → ℝ))) := by
    simpa [e₂] using
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
  have h₃ : MeasurePreserving e₃
      (volume : Measure (ℝ × (Fin n → ℝ)))
      (volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))) := by
    simpa [e₃, Measure.volume_eq_prod] using
      (MeasurePreserving.id (μ := (volume : Measure ℝ))).prod
        (PiLp.volume_preserving_toLp (Fin n))
  simpa [splitFirstCoordMeasurableEquiv, splitFirstCoordMeasurableEquiv_apply] using
    h₁.trans (h₂.trans h₃)

theorem norm_sq_eq_splitFirstCoord (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖x‖ ^ 2 = (splitFirstCoord n x).1 ^ 2 + ‖(splitFirstCoord n x).2‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp [EuclideanSpace.norm_sq_eq, splitFirstCoord]

theorem mem_capSet_iff_cos_le_splitFirstCoord_zero (n : ℕ)
    {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) (x : SpherePoint (n + 1)) :
    x ∈ capSet (n + 1) a ↔
      Real.cos a ≤ (splitFirstCoord n (x : EuclideanSpace ℝ (Fin (n + 1)))).1 := by
  simpa [splitFirstCoord] using
    (mem_capSet_iff_cos_le_coord0 (hn := Nat.succ_pos _) ha0 hapi x)

/-- The open radial cone over a spherical cap. -/
def capCone (n : ℕ) (a : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Set.Ioo (0 : ℝ) 1 • ((↑) '' capSet n a)

theorem mem_capCone_succ_iff (n : ℕ)
    {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    x ∈ capCone (n + 1) a ↔
      0 < ‖x‖ ∧
      ‖x‖ < 1 ∧
      Real.cos a * ‖x‖ ≤ (splitFirstCoord n x).1 := by
  constructor
  · rintro ⟨r, hr, z, hz, rfl⟩
    rcases hz with ⟨u, hu, rfl⟩
    have hucoord :
        Real.cos a ≤
          (splitFirstCoord n
            (((u : SpherePoint (n + 1)) : EuclideanSpace ℝ (Fin (n + 1))))).1 := by
      exact (mem_capSet_iff_cos_le_splitFirstCoord_zero n ha0 hapi u).1 hu
    have hunorm :
        ‖(((u : SpherePoint (n + 1)) : EuclideanSpace ℝ (Fin (n + 1))))‖ = 1 := by
      have hu' := u.2
      rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hu'
    constructor
    · simpa [norm_smul, hunorm, abs_of_pos hr.1] using hr.1
    constructor
    · simpa [norm_smul, hunorm, abs_of_pos hr.1] using hr.2
    · simpa [splitFirstCoord, norm_smul, hunorm, abs_of_pos hr.1,
        mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hucoord hr.1.le
  · rintro ⟨hxnorm_pos, hxnorm_lt, hcoord⟩
    have hxnorm_ne : ‖x‖ ≠ 0 := hxnorm_pos.ne'
    let u : SpherePoint (n + 1) :=
      ⟨‖x‖⁻¹ • x, by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hxnorm_pos), inv_mul_cancel₀ hxnorm_ne]⟩
    have hu_mem : u ∈ capSet (n + 1) a := by
      refine (mem_capSet_iff_cos_le_splitFirstCoord_zero n ha0 hapi u).2 ?_
      have hdiv : Real.cos a ≤ (splitFirstCoord n x).1 / ‖x‖ :=
        (le_div_iff₀ hxnorm_pos).2 hcoord
      simpa [u, splitFirstCoord, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
    refine ⟨‖x‖, ⟨hxnorm_pos, hxnorm_lt⟩,
      (((u : SpherePoint (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)))),
      ⟨u, hu_mem, rfl⟩, ?_⟩
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    simp [smul_smul, hxnorm_ne]

/-- The cap cone expressed in split first-coordinate / tail coordinates. -/
def capConeProd (n : ℕ) (a : ℝ) : Set (ℝ × EuclideanSpace ℝ (Fin n)) :=
  {p | joinFirstCoord n p ∈ capCone (n + 1) a}

theorem norm_joinFirstCoord (n : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    ‖joinFirstCoord n p‖ = Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_splitFirstCoord]
  simp

theorem mem_capConeProd_iff (n : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    p ∈ capConeProd n a ↔
      0 < p.1 ∧ p.1 ^ 2 + ‖p.2‖ ^ 2 < 1 ∧ ‖p.2‖ ≤ p.1 * Real.tan a := by
  rcases p with ⟨u, y⟩
  have hcos_pos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, hapi⟩
  have hsin_nonneg : 0 ≤ Real.sin a := by
    have hpi : a ≤ Real.pi := by linarith
    exact Real.sin_nonneg_of_nonneg_of_le_pi ha0 hpi
  constructor
  · intro hp
    have hmem :=
      (mem_capCone_succ_iff n ha0 hapi.le (joinFirstCoord n (u, y))).1 hp
    rcases hmem with ⟨hnorm_pos, hnorm_lt, hcoord⟩
    have hu_pos : 0 < u := by
      have hleft_pos : 0 < Real.cos a * ‖joinFirstCoord n (u, y)‖ :=
        mul_pos hcos_pos hnorm_pos
      exact lt_of_lt_of_le hleft_pos (by simpa using hcoord)
    have hball : u ^ 2 + ‖y‖ ^ 2 < 1 := by
      rw [norm_joinFirstCoord] at hnorm_lt
      have hball' : u ^ 2 + ‖y‖ ^ 2 < 1 ^ 2 := (Real.sqrt_lt' one_pos).1 hnorm_lt
      simpa using hball'
    have hcoord' : Real.cos a * Real.sqrt (u ^ 2 + ‖y‖ ^ 2) ≤ u := by
      simpa [norm_joinFirstCoord] using hcoord
    have hsqrt_le : Real.sqrt (u ^ 2 + ‖y‖ ^ 2) ≤ u / Real.cos a := by
      have hcoord'' : Real.sqrt (u ^ 2 + ‖y‖ ^ 2) * Real.cos a ≤ u := by
        simpa [mul_comm] using hcoord'
      exact (le_div_iff₀ hcos_pos).2 hcoord''
    have hsquare : u ^ 2 + ‖y‖ ^ 2 ≤ (u / Real.cos a) ^ 2 := by
      exact (Real.sqrt_le_iff).1 hsqrt_le |>.2
    have hsquare_mul :
        (Real.cos a) ^ 2 * (u ^ 2 + ‖y‖ ^ 2) ≤ u ^ 2 := by
      have h :=
        mul_le_mul_of_nonneg_left hsquare (sq_nonneg (Real.cos a))
      have hcancel : (Real.cos a) ^ 2 * (u / Real.cos a) ^ 2 = u ^ 2 := by
        field_simp [hcos_pos.ne']
      simpa [hcancel] using h
    have hpoly : (Real.cos a) ^ 2 * ‖y‖ ^ 2 ≤ u ^ 2 * (Real.sin a) ^ 2 := by
      nlinarith [hsquare_mul, Real.sin_sq_add_cos_sq a]
    have hcosy_sq : (Real.cos a * ‖y‖) ^ 2 ≤ (u * Real.sin a) ^ 2 := by
      nlinarith [hpoly]
    have hcosy : Real.cos a * ‖y‖ ≤ u * Real.sin a := by
      have hleft_nonneg : 0 ≤ Real.cos a * ‖y‖ :=
        mul_nonneg hcos_pos.le (norm_nonneg _)
      have hright_nonneg : 0 ≤ u * Real.sin a :=
        mul_nonneg hu_pos.le hsin_nonneg
      have habs := (sq_le_sq.1 hcosy_sq)
      simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs
    have htan : ‖y‖ ≤ u * Real.tan a := by
      have hcosy' : ‖y‖ * Real.cos a ≤ u * Real.sin a := by
        simpa [mul_comm] using hcosy
      have hdiv : ‖y‖ ≤ (u * Real.sin a) / Real.cos a :=
        (le_div_iff₀ hcos_pos).2 hcosy'
      simpa [Real.tan_eq_sin_div_cos, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    exact ⟨hu_pos, hball, htan⟩
  · rintro ⟨hu_pos, hball, htan⟩
    have hnorm_pos : 0 < ‖joinFirstCoord n (u, y)‖ := by
      rw [norm_joinFirstCoord]
      have : 0 < u ^ 2 + ‖y‖ ^ 2 := by positivity
      exact Real.sqrt_pos.2 this
    have hnorm_lt : ‖joinFirstCoord n (u, y)‖ < 1 := by
      rw [norm_joinFirstCoord]
      have hball' : u ^ 2 + ‖y‖ ^ 2 < 1 ^ 2 := by simpa using hball
      exact (Real.sqrt_lt' one_pos).2 hball'
    have hcosy : Real.cos a * ‖y‖ ≤ u * Real.sin a := by
      rw [Real.tan_eq_sin_div_cos] at htan
      have h :=
        mul_le_mul_of_nonneg_left htan hcos_pos.le
      have hcancel : Real.cos a * (u * (Real.sin a / Real.cos a)) = u * Real.sin a := by
        field_simp [hcos_pos.ne']
      simpa [mul_assoc, hcancel] using h
    have hcosy_sq : (Real.cos a * ‖y‖) ^ 2 ≤ (u * Real.sin a) ^ 2 := by
      have hleft_nonneg : 0 ≤ Real.cos a * ‖y‖ :=
        mul_nonneg hcos_pos.le (norm_nonneg _)
      have hright_nonneg : 0 ≤ u * Real.sin a :=
        mul_nonneg hu_pos.le hsin_nonneg
      exact (sq_le_sq.2 <| by
        simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using hcosy)
    have hsquare :
        (Real.cos a) ^ 2 * (u ^ 2 + ‖y‖ ^ 2) ≤ u ^ 2 := by
      nlinarith [hcosy_sq, Real.sin_sq_add_cos_sq a]
    have hsq :
        (Real.cos a * Real.sqrt (u ^ 2 + ‖y‖ ^ 2)) ^ 2 ≤ u ^ 2 := by
      have hnonneg : 0 ≤ u ^ 2 + ‖y‖ ^ 2 := by positivity
      calc
        (Real.cos a * Real.sqrt (u ^ 2 + ‖y‖ ^ 2)) ^ 2
            = (Real.cos a) ^ 2 * (Real.sqrt (u ^ 2 + ‖y‖ ^ 2)) ^ 2 := by
              ring
        _ = (Real.cos a) ^ 2 * (u ^ 2 + ‖y‖ ^ 2) := by
              rw [Real.sq_sqrt hnonneg]
        _ ≤ u ^ 2 := hsquare
    have hcoord_sqrt : Real.cos a * Real.sqrt (u ^ 2 + ‖y‖ ^ 2) ≤ u := by
      have hleft_nonneg : 0 ≤ Real.cos a * Real.sqrt (u ^ 2 + ‖y‖ ^ 2) :=
        mul_nonneg hcos_pos.le (Real.sqrt_nonneg _)
      have hright_nonneg : 0 ≤ u := hu_pos.le
      have habs := (sq_le_sq.1 hsq)
      simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs
    have hcoord : Real.cos a * ‖joinFirstCoord n (u, y)‖ ≤ u := by
      simpa [norm_joinFirstCoord] using hcoord_sqrt
    simpa [capConeProd] using
      (mem_capCone_succ_iff n ha0 hapi.le (joinFirstCoord n (u, y))).2
        ⟨hnorm_pos, hnorm_lt, hcoord⟩

theorem preimage_mk_capConeProd (n : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) (u : ℝ) :
    Prod.mk u ⁻¹' capConeProd n a =
      if 0 < u then
        {y : EuclideanSpace ℝ (Fin n) | u ^ 2 + ‖y‖ ^ 2 < 1 ∧ ‖y‖ ≤ u * Real.tan a}
      else
        ∅ := by
  by_cases hu : 0 < u
  · ext y
    simp [mem_capConeProd_iff, ha0, hapi, hu]
  · ext y
    simp [mem_capConeProd_iff, ha0, hapi, hu]

theorem u_sq_add_u_mul_tan_sq_lt_one_of_lt_cos
    {a u : ℝ} (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) (hu : 0 ≤ u) (hu_lt : u < Real.cos a) :
    u ^ 2 + (u * Real.tan a) ^ 2 < 1 := by
  have hcos_pos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, hapi⟩
  have hu_sq_lt : u ^ 2 < (Real.cos a) ^ 2 := by
    nlinarith [hu, hu_lt, hcos_pos]
  have hmul_lt :
      u ^ 2 * (1 + Real.tan a ^ 2) < (Real.cos a) ^ 2 * (1 + Real.tan a ^ 2) := by
    have hpos : 0 < 1 + Real.tan a ^ 2 := by positivity
    exact mul_lt_mul_of_pos_right hu_sq_lt hpos
  have htrig : (Real.cos a) ^ 2 * (1 + Real.tan a ^ 2) = 1 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.one_add_tan_sq_mul_cos_sq_eq_one hcos_pos.ne')
  calc
    u ^ 2 + (u * Real.tan a) ^ 2 = u ^ 2 * (1 + Real.tan a ^ 2) := by ring
    _ < (Real.cos a) ^ 2 * (1 + Real.tan a ^ 2) := hmul_lt
    _ = 1 := htrig

theorem sqrt_one_sub_u_sq_le_u_mul_tan_of_cos_le
    {a u : ℝ} (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2)
    (hu : 0 < u) (hcos_le : Real.cos a ≤ u) :
    Real.sqrt (1 - u ^ 2) ≤ u * Real.tan a := by
  have hcos_pos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, hapi⟩
  have htan_nonneg : 0 ≤ Real.tan a :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two ha0 hapi.le
  have hright_nonneg : 0 ≤ u * Real.tan a := mul_nonneg hu.le htan_nonneg
  have hcos_sq_le : (Real.cos a) ^ 2 ≤ u ^ 2 := by
    nlinarith [hcos_le, hcos_pos]
  have hmul_le :
      (Real.cos a) ^ 2 * (1 + Real.tan a ^ 2) ≤ u ^ 2 * (1 + Real.tan a ^ 2) := by
    have hnonneg : 0 ≤ 1 + Real.tan a ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right hcos_sq_le hnonneg
  have htrig : (Real.cos a) ^ 2 * (1 + Real.tan a ^ 2) = 1 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.one_add_tan_sq_mul_cos_sq_eq_one hcos_pos.ne')
  have hone_le : 1 ≤ u ^ 2 * (1 + Real.tan a ^ 2) := by
    calc
      1 = (Real.cos a) ^ 2 * (1 + Real.tan a ^ 2) := htrig.symm
      _ ≤ u ^ 2 * (1 + Real.tan a ^ 2) := hmul_le
  have hsq_le : 1 - u ^ 2 ≤ (u * Real.tan a) ^ 2 := by
    have hsum : 1 ≤ u ^ 2 + (u * Real.tan a) ^ 2 := by
      calc
        1 ≤ u ^ 2 * (1 + Real.tan a ^ 2) := hone_le
        _ = u ^ 2 + (u * Real.tan a) ^ 2 := by ring
    nlinarith
  exact (Real.sqrt_le_iff).2 ⟨hright_nonneg, hsq_le⟩

theorem preimage_mk_capConeProd_eq_closedBall_of_lt_cos (n : ℕ) {a u : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) (hu : 0 < u) (hu_lt : u < Real.cos a) :
    Prod.mk u ⁻¹' capConeProd n a =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (u * Real.tan a) := by
  ext y
  rw [preimage_mk_capConeProd n ha0 hapi u, if_pos hu, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  constructor
  · intro hy
    exact hy.2
  · intro hy
    constructor
    · have hy_sq : ‖y‖ ^ 2 ≤ (u * Real.tan a) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hy 2
      have hbound : u ^ 2 + (u * Real.tan a) ^ 2 < 1 :=
        u_sq_add_u_mul_tan_sq_lt_one_of_lt_cos ha0 hapi hu.le hu_lt
      nlinarith
    · exact hy

theorem preimage_mk_capConeProd_eq_ball_of_cos_le (n : ℕ) {a u : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) (hu : 0 < u) (hcos_le : Real.cos a ≤ u) :
    Prod.mk u ⁻¹' capConeProd n a =
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (1 - u ^ 2)) := by
  ext y
  rw [preimage_mk_capConeProd n ha0 hapi u, if_pos hu, Metric.mem_ball, dist_eq_norm, sub_zero]
  constructor
  · intro hy
    have hsub_nonneg : 0 ≤ 1 - u ^ 2 := by
      nlinarith [hy.1, sq_nonneg ‖y‖]
    have hy_sq : ‖y‖ ^ 2 < 1 - u ^ 2 := by
      nlinarith [hy.1]
    exact (Real.lt_sqrt (norm_nonneg _)).2 hy_sq
  · intro hy
    have hsqrt_pos : 0 < Real.sqrt (1 - u ^ 2) := by
      exact lt_of_le_of_lt (norm_nonneg _) hy
    have hsub_nonneg : 0 ≤ 1 - u ^ 2 := by
      exact le_of_lt (Real.sqrt_pos.1 hsqrt_pos)
    have hy_sq : ‖y‖ ^ 2 < 1 - u ^ 2 := by
      exact (Real.lt_sqrt (norm_nonneg _)).1 hy
    have hball : u ^ 2 + ‖y‖ ^ 2 < 1 := by
      nlinarith
    have hradius_le : Real.sqrt (1 - u ^ 2) ≤ u * Real.tan a :=
      sqrt_one_sub_u_sq_le_u_mul_tan_of_cos_le ha0 hapi hu hcos_le
    have htan : ‖y‖ ≤ u * Real.tan a := le_trans hy.le hradius_le
    exact ⟨hball, htan⟩

theorem volume_fiber_eq_piecewise_ball (n : ℕ) (hn : 0 < n) {a u : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (Prod.mk u ⁻¹' capConeProd n a) =
      if 0 < u then
        if u < Real.cos a then
          (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 (u * Real.tan a))
        else
          (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 (Real.sqrt (1 - u ^ 2)))
      else 0 := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  by_cases hu : 0 < u
  · by_cases hu_lt : u < Real.cos a
    · rw [if_pos hu, if_pos hu_lt]
      rw [preimage_mk_capConeProd_eq_closedBall_of_lt_cos n ha0 hapi hu hu_lt]
      rw [EuclideanSpace.volume_closedBall, EuclideanSpace.volume_ball]
    · rw [if_pos hu, if_neg hu_lt]
      rw [preimage_mk_capConeProd_eq_ball_of_cos_le n ha0 hapi hu (le_of_not_gt hu_lt)]
  · rw [if_neg hu]
    rw [preimage_mk_capConeProd n ha0 hapi u, if_neg hu, measure_empty]

theorem measurableSet_capConeProd (n : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    MeasurableSet (capConeProd n a) := by
  have hset :
      capConeProd n a =
        {p : ℝ × EuclideanSpace ℝ (Fin n) |
          0 < p.1 ∧ p.1 ^ 2 + ‖p.2‖ ^ 2 < 1 ∧ ‖p.2‖ ≤ p.1 * Real.tan a} := by
    ext p
    simpa using (mem_capConeProd_iff n ha0 hapi p)
  rw [hset]
  have hcont_sqnorm :
      Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => p.1 ^ 2 + ‖p.2‖ ^ 2 := by
    fun_prop
  have hcont_tan :
      Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => p.1 * Real.tan a := by
    fun_prop
  exact (isOpen_lt continuous_const continuous_fst).measurableSet.inter <|
    (isOpen_lt hcont_sqnorm continuous_const).measurableSet.inter <|
      (isClosed_le (continuous_norm.comp continuous_snd) hcont_tan).measurableSet

theorem volume_capCone_eq_volume_capConeProd (n : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (capCone (n + 1) a) =
      (volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))) (capConeProd n a) := by
  rw [← (measurePreserving_splitFirstCoord n).map_eq]
  rw [Measure.map_apply (measurePreserving_splitFirstCoord n).measurable
    (measurableSet_capConeProd n ha0 hapi)]
  congr 1
  ext x
  simp [capConeProd]

theorem volume_capCone_eq_lintegral_fiber (n : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (capCone (n + 1) a) =
      ∫⁻ u, (volume : Measure (EuclideanSpace ℝ (Fin n))) (Prod.mk u ⁻¹' capConeProd n a)
        ∂(volume : Measure ℝ) := by
  rw [volume_capCone_eq_volume_capConeProd n ha0 hapi]
  rw [Measure.volume_eq_prod ℝ (EuclideanSpace ℝ (Fin n))]
  rw [Measure.prod_apply (measurableSet_capConeProd n ha0 hapi)]

theorem volume_capCone_eq_lintegral_fiber_piecewise_ball (n : ℕ) (hn : 0 < n) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (capCone (n + 1) a) =
      ∫⁻ u, if 0 < u then
          if u < Real.cos a then
            (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 (u * Real.tan a))
          else
            (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 (Real.sqrt (1 - u ^ 2)))
        else 0
        ∂(volume : Measure ℝ) := by
  rw [volume_capCone_eq_lintegral_fiber n ha0 hapi]
  refine lintegral_congr_ae ?_
  filter_upwards with u
  rw [volume_fiber_eq_piecewise_ball n hn ha0 hapi]

theorem volume_fiber_eq_piecewise_pow (n : ℕ) (hn : 0 < n) {a u : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (Prod.mk u ⁻¹' capConeProd n a) =
      if 0 < u then
        if u < Real.cos a then
          ENNReal.ofReal ((u * Real.tan a) ^ n) *
            (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1)
        else
          ENNReal.ofReal ((Real.sqrt (1 - u ^ 2)) ^ n) *
            (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1)
      else 0 := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [volume_fiber_eq_piecewise_ball n hn ha0 hapi]
  by_cases hu : 0 < u
  · by_cases hu_lt : u < Real.cos a
    · rw [if_pos hu, if_pos hu_lt]
      have htan_nonneg : 0 ≤ u * Real.tan a := by
        have htan_nonneg : 0 ≤ Real.tan a :=
          Real.tan_nonneg_of_nonneg_of_le_pi_div_two ha0 hapi.le
        exact mul_nonneg hu.le htan_nonneg
      rw [Measure.addHaar_ball (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (x := (0 : EuclideanSpace ℝ (Fin n))) (hr := htan_nonneg)]
      simp [hu, hu_lt]
    · rw [if_pos hu, if_neg hu_lt]
      rw [Measure.addHaar_ball (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (x := (0 : EuclideanSpace ℝ (Fin n))) (hr := Real.sqrt_nonneg _)]
      simp [hu, hu_lt]
  · simp [hu]

theorem volume_capCone_eq_lintegral_fiber_piecewise_pow (n : ℕ) (hn : 0 < n) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (capCone (n + 1) a) =
      ∫⁻ u, if 0 < u then
          if u < Real.cos a then
            ENNReal.ofReal ((u * Real.tan a) ^ n) *
              (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1)
          else
            ENNReal.ofReal ((Real.sqrt (1 - u ^ 2)) ^ n) *
              (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1)
        else 0
        ∂(volume : Measure ℝ) := by
  rw [volume_capCone_eq_lintegral_fiber_piecewise_ball n hn ha0 hapi]
  refine lintegral_congr_ae ?_
  filter_upwards with u
  exact
    (volume_fiber_eq_piecewise_ball n hn (a := a) (u := u) ha0 hapi).symm.trans
      (volume_fiber_eq_piecewise_pow n hn (a := a) (u := u) ha0 hapi)

/-- The one-dimensional piecewise power integrand arising from the first-coordinate fiber
decomposition of the cap cone. -/
def capConeFiberPowIntegrand (n : ℕ) (a u : ℝ) : ℝ≥0∞ :=
  if 0 < u then
    if u < Real.cos a then
      ENNReal.ofReal ((u * Real.tan a) ^ n)
    else
      ENNReal.ofReal ((Real.sqrt (1 - u ^ 2)) ^ n)
  else
    0

theorem measurable_capConeFiberPowIntegrand (n : ℕ) (a : ℝ) :
    Measurable (capConeFiberPowIntegrand n a) := by
  classical
  unfold capConeFiberPowIntegrand
  refine Measurable.piecewise measurableSet_Ioi ?_ measurable_const
  refine Measurable.piecewise measurableSet_Iio ?_ ?_
  · fun_prop
  · fun_prop

theorem volume_capCone_eq_lintegral_capConeFiberPow_mul_unitBall
    (n : ℕ) (hn : 0 < n) {a : ℝ} (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (capCone (n + 1) a) =
      (∫⁻ u, capConeFiberPowIntegrand n a u ∂(volume : Measure ℝ)) *
        (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1) := by
  let C : ℝ≥0∞ := (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1)
  have hC : C ≠ ∞ := by
    exact measure_ball_lt_top.ne
  rw [volume_capCone_eq_lintegral_fiber_piecewise_pow n hn ha0 hapi]
  have hrewrite :
      (∫⁻ u, if 0 < u then
          if u < Real.cos a then
            ENNReal.ofReal ((u * Real.tan a) ^ n) * C
          else
            ENNReal.ofReal ((Real.sqrt (1 - u ^ 2)) ^ n) * C
        else 0
        ∂(volume : Measure ℝ)) =
      ∫⁻ u, capConeFiberPowIntegrand n a u * C ∂(volume : Measure ℝ) := by
    refine lintegral_congr_ae ?_
    filter_upwards with u
    by_cases hu : 0 < u <;> simp [capConeFiberPowIntegrand, hu, C]
  rw [hrewrite, lintegral_mul_const' C (capConeFiberPowIntegrand n a) hC]

theorem volumeReal_capCone_eq_lintegral_capConeFiberPow_mul_unitBall
    (n : ℕ) (hn : 0 < n) {a : ℝ} (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).real (capCone (n + 1) a) =
      (∫⁻ u, capConeFiberPowIntegrand n a u ∂(volume : Measure ℝ)).toReal *
        (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) := by
  rw [measureReal_def, volume_capCone_eq_lintegral_capConeFiberPow_mul_unitBall n hn ha0 hapi,
    ENNReal.toReal_mul, measureReal_def]

theorem capCone_subset_ball (n : ℕ) (a : ℝ) :
    capCone n a ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rintro x ⟨r, hr, y, ⟨u, _, rfl⟩, rfl⟩
  rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul]
  have hu_norm : ‖((u : SpherePoint n) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    have hu_sphere := u.2
    rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hu_sphere
  simp [abs_of_pos hr.1, hu_norm, hr.2]

theorem sphereSurfaceMeasure_capSet_eq_mul_volume_capCone
    {n : ℕ} (hn : 0 < n) {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    (sphereSurfaceMeasure n).real (capSet n a) =
      n * (volume : Measure (EuclideanSpace ℝ (Fin n))).real (capCone n a) := by
  have hs : MeasurableSet (capSet n a) := measurableSet_capSet hn ha0 hapi
  have hcone_fin :
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (capCone n a) ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (measure_mono (capCone_subset_ball n a)) measure_ball_lt_top
  have hcone :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) (capSet n a) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) *
          (volume : Measure (EuclideanSpace ℝ (Fin n))) (capCone n a) := by
    simpa [capCone] using
      (Measure.toSphere_apply' (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hs)
  simpa [sphereSurfaceMeasure, measureReal_def, finrank_euclideanSpace_fin,
    hcone_fin] using congrArg ENNReal.toReal hcone

theorem capMeasure_eq_volume_capCone_div_volume_ball
    (n : ℕ) (hn : 0 < n) {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    capMeasure n a =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real (capCone n a) /
        (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) := by
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  have hcast : (((n - 1 : ℕ) : ℝ) + 1) = n := by
    exact_mod_cast hsub
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [capMeasure_eq_div_surfaceMeasure hn]
  rw [sphereSurfaceMeasure_capSet_eq_mul_volume_capCone hn ha0 hapi]
  rw [sphereArea_eq_finrank_mul_volume_ball]
  rw [hsub, hcast]
  simpa using
    (mul_div_mul_left
      (a := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (capCone n a))
      (b := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1))
      (c := (n : ℝ)) hn')

theorem capMeasure_eq_lintegral_capConeFiberPow
    (n : ℕ) (hn : 2 ≤ n) (a : ℝ) (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    capMeasure n a =
      (∫⁻ u, capConeFiberPowIntegrand (n - 1) a u ∂(volume : Measure ℝ)).toReal *
        (volume : Measure (EuclideanSpace ℝ (Fin (n - 1)))).real (Metric.ball 0 1) /
          (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) := by
  cases n with
  | zero =>
      cases hn
  | succ m =>
      have hm_pos : 0 < m := by
        apply Nat.succ_lt_succ_iff.mp
        have : 1 < m + 1 := lt_of_lt_of_le (by decide : 1 < 2) hn
        simpa using this
      rw [capMeasure_eq_volume_capCone_div_volume_ball (m + 1) (Nat.succ_pos _) ha0 hapi.le]
      rw [volumeReal_capCone_eq_lintegral_capConeFiberPow_mul_unitBall m hm_pos ha0 hapi]
      simp

def capConeFiberPowIntegrandReal (n : ℕ) (a u : ℝ) : ℝ :=
  if 0 < u then
    if u < Real.cos a then
      (u * Real.tan a) ^ n
    else
      (Real.sqrt (1 - u ^ 2)) ^ n
  else
    0

@[simp] theorem capConeFiberPowIntegrandReal_def (n : ℕ) (a u : ℝ) :
    capConeFiberPowIntegrandReal n a u =
      if 0 < u then
        if u < Real.cos a then
          (u * Real.tan a) ^ n
        else
          (Real.sqrt (1 - u ^ 2)) ^ n
      else
        0 := rfl

theorem capConeFiberPowIntegrandReal_eq_toReal
    (n : ℕ) (a u : ℝ) (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    capConeFiberPowIntegrandReal n a u = (capConeFiberPowIntegrand n a u).toReal := by
  by_cases hu : 0 < u
  · by_cases huc : u < Real.cos a
    · have htan_nonneg : 0 ≤ Real.tan a :=
        Real.tan_nonneg_of_nonneg_of_le_pi_div_two ha0 hapi
      have hpow_nonneg : 0 ≤ (u * Real.tan a) ^ n := by
        exact pow_nonneg (mul_nonneg hu.le htan_nonneg) _
      simp [capConeFiberPowIntegrandReal_def, capConeFiberPowIntegrand, hu, huc, hpow_nonneg]
    · have hsqrt_nonneg : 0 ≤ (Real.sqrt (1 - u ^ 2)) ^ n := by
        exact pow_nonneg (Real.sqrt_nonneg _) _
      simp [capConeFiberPowIntegrandReal_def, capConeFiberPowIntegrand, hu, huc]
  · simp [capConeFiberPowIntegrandReal_def, capConeFiberPowIntegrand, hu]

theorem capConeFiberPowIntegrandReal_eq_zero_of_nonpos
    (n : ℕ) (a u : ℝ) (hu : u ≤ 0) :
    capConeFiberPowIntegrandReal n a u = 0 := by
  simp [capConeFiberPowIntegrandReal_def, not_lt_of_ge hu]

theorem capConeFiberPowIntegrandReal_eq_zero_of_one_le
    (n : ℕ) (hn : 0 < n) (a u : ℝ) (hu : 1 ≤ u) :
    capConeFiberPowIntegrandReal n a u = 0 := by
  by_cases hu0 : 0 < u
  · have huc : ¬ u < Real.cos a := by
      exact not_lt.mpr (le_trans (Real.cos_le_one a) hu)
    have hsqrt : Real.sqrt (1 - u ^ 2) = 0 := by
      apply Real.sqrt_eq_zero_of_nonpos
      have hu_sq : 1 ≤ u ^ 2 := by
        nlinarith [sq_nonneg (u - 1)]
      linarith
    simp [capConeFiberPowIntegrandReal_def, hu0, huc, hsqrt, hn.ne']
  · simp [capConeFiberPowIntegrandReal_def, hu0]

theorem indicator_capConeFiberPowIntegrandReal_Ioc
    (n : ℕ) (hn : 0 < n) (a : ℝ) :
    Set.indicator (Set.Ioc 0 1) (capConeFiberPowIntegrandReal n a) =
      capConeFiberPowIntegrandReal n a := by
  funext u
  by_cases hu : u ∈ Set.Ioc 0 1
  · simp [hu]
  · rw [Set.indicator_of_notMem hu]
    by_cases hu0 : u ≤ 0
    · exact (capConeFiberPowIntegrandReal_eq_zero_of_nonpos n a u hu0).symm
    · have hu1 : 1 ≤ u := by
        by_contra hu1
        apply hu
        constructor
        · linarith
        · linarith
      exact (capConeFiberPowIntegrandReal_eq_zero_of_one_le n hn a u hu1).symm

theorem capConeFiberPowIntegrandReal_eq_left
    (n : ℕ) (hn : 0 < n) (a : ℝ) (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2)
    {u : ℝ} (hu : u ∈ Set.Icc 0 (Real.cos a)) :
    capConeFiberPowIntegrandReal n a u = (u * Real.tan a) ^ n := by
  by_cases hu0 : 0 < u
  · by_cases huc : u < Real.cos a
    · simp [capConeFiberPowIntegrandReal_def, hu0, huc]
    · have hueq : u = Real.cos a := le_antisymm hu.2 (not_lt.mp huc)
      have hcos_pos : 0 < Real.cos a := by
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · have hpi : 0 < Real.pi / 2 := by positivity
          linarith
        · exact hapi
      have hsin_nonneg : 0 ≤ Real.sin a := by
        exact Real.sin_nonneg_of_mem_Icc ⟨ha0, by linarith [hapi]⟩
      have hsqrt : Real.sqrt (1 - Real.cos a ^ 2) = Real.sin a := by
        have hsq : 1 - Real.cos a ^ 2 = Real.sin a ^ 2 := by
          nlinarith [Real.sin_sq_add_cos_sq a]
        rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hsin_nonneg]
      have hmul : Real.cos a * Real.tan a = Real.sin a := by
        rw [Real.tan_eq_sin_div_cos]
        field_simp [hcos_pos.ne']
      rw [capConeFiberPowIntegrandReal_def, if_pos hu0, if_neg huc, hueq, hsqrt, hmul]
  · have hzero : u = 0 := le_antisymm (le_of_not_gt hu0) hu.1
    simp [capConeFiberPowIntegrandReal_def, hzero, hn.ne']

theorem capConeFiberPowIntegrandReal_eq_right
    (n : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2)
    {u : ℝ} (hu : u ∈ Set.Icc (Real.cos a) 1) :
    capConeFiberPowIntegrandReal n a u = (Real.sqrt (1 - u ^ 2)) ^ n := by
  have hcos_pos : 0 < Real.cos a := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have hpi : 0 < Real.pi / 2 := by positivity
      linarith
    · exact hapi
  have hu0 : 0 < u := lt_of_lt_of_le hcos_pos hu.1
  simp [capConeFiberPowIntegrandReal_def, hu0, not_lt.mpr hu.1]

theorem lintegral_capConeFiberPow_eq_boundary_add_integral_sin_pow
    (n : ℕ) (hn : 0 < n) (a : ℝ) (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (∫⁻ u, capConeFiberPowIntegrand n a u ∂(volume : Measure ℝ)).toReal =
      Real.sin a ^ n * Real.cos a / (n + 1) +
        ∫ t in 0..a, Real.sin t ^ (n + 1) := by
  let f : ℝ → ℝ := capConeFiberPowIntegrandReal n a
  have hfinite : ∀ᵐ u ∂(volume : Measure ℝ), capConeFiberPowIntegrand n a u < ∞ := by
    filter_upwards with u
    by_cases hu : 0 < u
    · by_cases huc : u < Real.cos a
      · simp [capConeFiberPowIntegrand, hu, huc]
      · simp [capConeFiberPowIntegrand, hu, huc]
    · simp [capConeFiberPowIntegrand, hu]
  have htoReal :
      (∫⁻ u, capConeFiberPowIntegrand n a u ∂(volume : Measure ℝ)).toReal =
        ∫ u, f u ∂(volume : Measure ℝ) := by
    calc
      (∫⁻ u, capConeFiberPowIntegrand n a u ∂(volume : Measure ℝ)).toReal
          = ∫ u, (capConeFiberPowIntegrand n a u).toReal ∂(volume : Measure ℝ) := by
              simpa using
                (MeasureTheory.integral_toReal
                  (μ := (volume : Measure ℝ))
                  (f := capConeFiberPowIntegrand n a)
                  (hfm := (measurable_capConeFiberPowIntegrand n a).aemeasurable)
                  (hf := hfinite)).symm
      _ = ∫ u, f u ∂(volume : Measure ℝ) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with u
            simpa [f] using (capConeFiberPowIntegrandReal_eq_toReal n a u ha0 hapi.le).symm
  have hindicator :
      ∫ u, f u ∂(volume : Measure ℝ) = ∫ u in Set.Ioc 0 1, f u ∂(volume : Measure ℝ) := by
    simpa [f, indicator_capConeFiberPowIntegrandReal_Ioc n hn a] using
      (MeasureTheory.integral_indicator
        (μ := (volume : Measure ℝ))
        (s := Set.Ioc 0 1)
        (f := f)
        measurableSet_Ioc)
  have hleft_int :
      ∫ u in 0..Real.cos a, f u = ∫ u in 0..Real.cos a, (u * Real.tan a) ^ n := by
    have hcos_nonneg : 0 ≤ Real.cos a := by
      exact (Real.cos_pos_of_mem_Ioo
        ⟨by
            have hpi : 0 < Real.pi / 2 := by positivity
            linarith,
          hapi⟩).le
    refine intervalIntegral.integral_congr ?_
    intro u hu
    have hu' : u ∈ Set.Icc 0 (Real.cos a) := by
      simpa [uIcc_of_le hcos_nonneg] using hu
    exact capConeFiberPowIntegrandReal_eq_left n hn a ha0 hapi hu'
  have hright_int :
      ∫ u in Real.cos a..1, f u = ∫ u in Real.cos a..1, (Real.sqrt (1 - u ^ 2)) ^ n := by
    refine intervalIntegral.integral_congr ?_
    intro u hu
    have hu' : u ∈ Set.Icc (Real.cos a) 1 := by
      simpa [uIcc_of_le (Real.cos_le_one a)] using hu
    exact capConeFiberPowIntegrandReal_eq_right n a ha0 hapi hu'
  have hf_left :
      IntervalIntegrable f volume 0 (Real.cos a) := by
    have hf_left' : IntervalIntegrable (fun u => (u * Real.tan a) ^ n) volume 0 (Real.cos a) := by
      exact Continuous.intervalIntegrable (by fun_prop) 0 (Real.cos a)
    have hcos_nonneg : 0 ≤ Real.cos a := by
      exact (Real.cos_pos_of_mem_Ioo
        ⟨by
            have hpi : 0 < Real.pi / 2 := by positivity
            linarith,
          hapi⟩).le
    refine hf_left'.congr ?_
    intro u hu
    symm
    have huIoc : u ∈ Set.Ioc 0 (Real.cos a) := by
      simpa [uIoc_of_le hcos_nonneg] using hu
    have hu' : u ∈ Set.Icc 0 (Real.cos a) := ⟨huIoc.1.le, huIoc.2⟩
    exact capConeFiberPowIntegrandReal_eq_left n hn a ha0 hapi hu'
  have hf_right :
      IntervalIntegrable f volume (Real.cos a) 1 := by
    have hf_right' :
        IntervalIntegrable (fun u => (Real.sqrt (1 - u ^ 2)) ^ n) volume (Real.cos a) 1 := by
      exact Continuous.intervalIntegrable (by fun_prop) (Real.cos a) 1
    refine hf_right'.congr ?_
    intro u hu
    symm
    have huIoc : u ∈ Set.Ioc (Real.cos a) 1 := by
      simpa [uIoc_of_le (Real.cos_le_one a)] using hu
    have hu' : u ∈ Set.Icc (Real.cos a) 1 := ⟨huIoc.1.le, huIoc.2⟩
    exact capConeFiberPowIntegrandReal_eq_right n a ha0 hapi hu'
  have hsplit :
      ∫ x in 0..1, f x = (∫ x in 0..Real.cos a, f x) + ∫ x in Real.cos a..1, f x := by
    exact (intervalIntegral.integral_add_adjacent_intervals hf_left hf_right).symm
  have hfirst :
      ∫ u in 0..Real.cos a, (u * Real.tan a) ^ n =
        Real.sin a ^ n * Real.cos a / (n + 1) := by
    have hcos_pos : 0 < Real.cos a := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · have hpi : 0 < Real.pi / 2 := by positivity
        linarith
      · exact hapi
    calc
      ∫ u in 0..Real.cos a, (u * Real.tan a) ^ n
          = ∫ u in 0..Real.cos a, u ^ n * (Real.tan a) ^ n := by
              refine intervalIntegral.integral_congr ?_
              intro u hu
              simp [mul_pow]
      _ = (∫ u in 0..Real.cos a, u ^ n) * (Real.tan a) ^ n := by
            rw [intervalIntegral.integral_mul_const]
      _ = (Real.cos a ^ (n + 1) / (n + 1)) * (Real.tan a) ^ n := by
            rw [integral_pow]
            simp [hn.ne']
      _ = Real.sin a ^ n * Real.cos a / (n + 1) := by
            rw [Real.tan_eq_sin_div_cos, div_pow]
            field_simp [hcos_pos.ne']
            ring
  have hsecond :
      ∫ u in Real.cos a..1, (Real.sqrt (1 - u ^ 2)) ^ n =
        ∫ t in 0..a, Real.sin t ^ (n + 1) := by
    let g : ℝ → ℝ := fun u => (Real.sqrt (1 - u ^ 2)) ^ n
    have hchange :
        ∫ t in 0..a, (g ∘ Real.cos) t * (-Real.sin t) =
          ∫ u in Real.cos 0..Real.cos a, g u := by
      refine intervalIntegral.integral_comp_mul_deriv
        (a := 0) (b := a)
        (f := Real.cos) (f' := fun t => -Real.sin t) (g := g) ?_ ?_ ?_
      · intro t ht
        simpa using (Real.hasDerivAt_cos t)
      · fun_prop
      · fun_prop
    calc
      ∫ u in Real.cos a..1, g u = -∫ u in 1..Real.cos a, g u := by
            rw [intervalIntegral.integral_symm]
      _ = -∫ t in 0..a, (g ∘ Real.cos) t * (-Real.sin t) := by
            simpa using congrArg Neg.neg hchange.symm
      _ = ∫ t in 0..a, (g ∘ Real.cos) t * Real.sin t := by
            rw [← intervalIntegral.integral_neg]
            refine intervalIntegral.integral_congr ?_
            intro t ht
            ring
      _ = ∫ t in 0..a, Real.sin t ^ (n + 1) := by
            refine intervalIntegral.integral_congr ?_
            intro t ht
            have ht' : t ∈ Set.Icc 0 a := by
              simpa [uIcc_of_le ha0] using ht
            have hsin_nonneg : 0 ≤ Real.sin t := by
              apply Real.sin_nonneg_of_mem_Icc
              exact ⟨ht'.1, by linarith [ht'.2, hapi]⟩
            have hsqrt : Real.sqrt (1 - Real.cos t ^ 2) = Real.sin t := by
              have hsq : 1 - Real.cos t ^ 2 = Real.sin t ^ 2 := by
                nlinarith [Real.sin_sq_add_cos_sq t]
              rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hsin_nonneg]
            calc
              (g ∘ Real.cos) t * Real.sin t
                  = (Real.sqrt (1 - Real.cos t ^ 2)) ^ n * Real.sin t := by
                      simp [g]
              _ = Real.sin t ^ n * Real.sin t := by rw [hsqrt]
              _ = Real.sin t ^ (n + 1) := by rw [pow_succ]
  calc
    (∫⁻ u, capConeFiberPowIntegrand n a u ∂(volume : Measure ℝ)).toReal
        = ∫ u, f u ∂(volume : Measure ℝ) := htoReal
    _ = ∫ u in Set.Ioc 0 1, f u ∂(volume : Measure ℝ) := hindicator
    _ = ∫ x in 0..1, f x := by
          rw [intervalIntegral.integral_of_le zero_le_one]
    _ = (∫ x in 0..Real.cos a, f x) + ∫ x in Real.cos a..1, f x := hsplit
    _ = (∫ x in 0..Real.cos a, (x * Real.tan a) ^ n) + ∫ x in Real.cos a..1, f x := by
          exact congrArg (fun z : ℝ => z + ∫ x in Real.cos a..1, f x) hleft_int
    _ = (∫ x in 0..Real.cos a, (x * Real.tan a) ^ n) +
          ∫ x in Real.cos a..1, (Real.sqrt (1 - x ^ 2)) ^ n := by
          exact congrArg (fun z : ℝ => (∫ x in 0..Real.cos a, (x * Real.tan a) ^ n) + z) hright_int
    _ = Real.sin a ^ n * Real.cos a / (n + 1) +
          ∫ x in Real.cos a..1, (Real.sqrt (1 - x ^ 2)) ^ n := by
          exact congrArg
            (fun z : ℝ => z + ∫ x in Real.cos a..1, (Real.sqrt (1 - x ^ 2)) ^ n) hfirst
    _ = Real.sin a ^ n * Real.cos a / (n + 1) +
          ∫ t in 0..a, Real.sin t ^ (n + 1) := by
          simpa using congrArg (fun z => Real.sin a ^ n * Real.cos a / (n + 1) + z) hsecond

/--
Exact normalized spherical-cap formula on `0 ≤ a < π / 2`.

-/
theorem capMeasure_eq_mul_intervalIntegral_sin_pow
    (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    capMeasure n a =
      (sphereArea (n - 2) / sphereArea (n - 1)) *
        ∫ t in 0..a, Real.sin t ^ (n - 2) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm] at hm
  subst n
  have hm_pos : 0 < m + 1 := Nat.succ_pos _
  have hcap :
      capMeasure (m + 2) a =
        (∫⁻ u, capConeFiberPowIntegrand (m + 1) a u ∂(volume : Measure ℝ)).toReal *
          (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).real (Metric.ball 0 1) /
            (volume : Measure (EuclideanSpace ℝ (Fin (m + 2)))).real (Metric.ball 0 1) := by
    simpa using
      capMeasure_eq_lintegral_capConeFiberPow (m + 2) (Nat.le_add_left 2 m) a ha0 hapi
  have hlin :
      (∫⁻ u, capConeFiberPowIntegrand (m + 1) a u ∂(volume : Measure ℝ)).toReal =
        Real.sin a ^ (m + 1) * Real.cos a / (m + 2) +
          ∫ t in 0..a, Real.sin t ^ (m + 2) := by
    have htmp :=
      lintegral_capConeFiberPow_eq_boundary_add_integral_sin_pow (m + 1) hm_pos a ha0 hapi
    calc
      (∫⁻ u, capConeFiberPowIntegrand (m + 1) a u ∂(volume : Measure ℝ)).toReal
          = Real.sin a ^ (m + 1) * Real.cos a / (↑m + (1 + 1 : ℝ)) +
              ∫ t in 0..a, Real.sin t ^ (m + 2) := by
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using htmp
      _ = Real.sin a ^ (m + 1) * Real.cos a / (m + 2) +
            ∫ t in 0..a, Real.sin t ^ (m + 2) := by
            congr 1
            ring
  have hrec :
      Real.sin a ^ (m + 1) * Real.cos a / (m + 2) + ∫ t in 0..a, Real.sin t ^ (m + 2) =
        ((m + 1 : ℝ) / (m + 2 : ℝ)) * ∫ t in 0..a, Real.sin t ^ m := by
    have hpow := integral_sin_pow (a := 0) (b := a) (n := m)
    calc
      Real.sin a ^ (m + 1) * Real.cos a / (m + 2) + ∫ t in 0..a, Real.sin t ^ (m + 2)
          = Real.sin a ^ (m + 1) * Real.cos a / (m + 2) +
              ((Real.sin 0 ^ (m + 1) * Real.cos 0 - Real.sin a ^ (m + 1) * Real.cos a) /
                (m + 2) + ((m + 1 : ℝ) / (m + 2 : ℝ)) * ∫ t in 0..a, Real.sin t ^ m) := by
                  rw [hpow]
      _ = ((m + 1 : ℝ) / (m + 2 : ℝ)) * ∫ t in 0..a, Real.sin t ^ m := by
            simp
            ring
  have hratio :
      ((m + 1 : ℝ) / (m + 2 : ℝ)) *
          ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).real (Metric.ball 0 1) /
            (volume : Measure (EuclideanSpace ℝ (Fin (m + 2)))).real (Metric.ball 0 1)) =
        sphereArea m / sphereArea (m + 1) := by
    have hball_pos :
        0 <
          (volume : Measure (EuclideanSpace ℝ (Fin (m + 2)))).real (Metric.ball 0 1) := by
      exact ENNReal.toReal_pos
        (measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin (m + 2))))
          (0 : EuclideanSpace ℝ (Fin (m + 2))) zero_lt_one).ne'
        measure_ball_lt_top.ne
    rw [sphereArea_eq_finrank_mul_volume_ball, sphereArea_eq_finrank_mul_volume_ball]
    field_simp [hball_pos.ne', show (m + 2 : ℝ) ≠ 0 by positivity]
    ring_nf
    simp [Nat.cast_add, add_comm]
    nlinarith
  calc
    capMeasure (m + 2) a
        = (∫⁻ u, capConeFiberPowIntegrand (m + 1) a u ∂(volume : Measure ℝ)).toReal *
            (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).real (Metric.ball 0 1) /
              (volume : Measure (EuclideanSpace ℝ (Fin (m + 2)))).real (Metric.ball 0 1) := hcap
    _ = (Real.sin a ^ (m + 1) * Real.cos a / (m + 2) +
            ∫ t in 0..a, Real.sin t ^ (m + 2)) *
          ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).real (Metric.ball 0 1) /
            (volume : Measure (EuclideanSpace ℝ (Fin (m + 2)))).real (Metric.ball 0 1)) := by
          rw [hlin]
          ring
    _ = (((m + 1 : ℝ) / (m + 2 : ℝ)) * ∫ t in 0..a, Real.sin t ^ m) *
          ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).real (Metric.ball 0 1) /
            (volume : Measure (EuclideanSpace ℝ (Fin (m + 2)))).real (Metric.ball 0 1)) := by
          rw [hrec]
    _ = (((m + 1 : ℝ) / (m + 2 : ℝ)) *
            ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).real (Metric.ball 0 1) /
              (volume : Measure (EuclideanSpace ℝ (Fin (m + 2)))).real (Metric.ball 0 1))) *
          ∫ t in 0..a, Real.sin t ^ m := by
          ring
    _ = (sphereArea m / sphereArea (m + 1)) * ∫ t in 0..a, Real.sin t ^ m := by
          rw [hratio]

end OptimalAlphabets
