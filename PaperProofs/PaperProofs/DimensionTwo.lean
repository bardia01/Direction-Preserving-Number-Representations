import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Measure.Real
import PaperProofs.Definitions
import PaperProofs.ProductVsSpherical

/-!
# Dimension-two classification

This module records the exact dimension-2 statements from the paper: the exact
circle-covering radius, the scalar collision/no-collision classification, the
binary no-collision equality case, and the complete dimension-2 dichotomy.
-/

noncomputable section

open Set Filter Topology Real Metric MeasureTheory
open scoped MeasureTheory

namespace PaperProofs

local instance : DecidableEq Real.Angle := Classical.decEq _
local instance : DecidableEq (OptimalAlphabets.SpherePoint 2) := Classical.decEq _
local instance : Fact (0 < (2 * Real.pi : Real)) := ⟨by positivity⟩
local instance : MeasureSpace Real.Angle :=
  inferInstanceAs (MeasureSpace (AddCircle (2 * Real.pi)))

/-- The complex unit-circle point corresponding to a point of `S^1 ⊂ R^2`. -/
def sphere2Circle (u : OptimalAlphabets.SpherePoint 2) : Circle :=
  ⟨Complex.orthonormalBasisOneI.repr.symm u.1, by
    change
      Complex.orthonormalBasisOneI.repr.symm u.1 ∈
        Metric.sphere (0 : Complex) 1
    rw [mem_sphere_zero_iff_norm]
    have hu : ‖u.1‖ = 1 := by
      have hdist : dist u.1 (0 : EuclideanSpace Real (Fin 2)) = 1 := u.2
      rw [dist_eq_norm, sub_zero] at hdist
      exact hdist
    exact (Complex.orthonormalBasisOneI.repr.symm.norm_map u.1).trans hu⟩

/-- The angular coordinate of a point of `S^1`, as an element of `R / 2πZ`. -/
def sphere2Angle (u : OptimalAlphabets.SpherePoint 2) : Real.Angle :=
  (Complex.arg (sphere2Circle u : Complex) : Real.Angle)

/-- The point of `S^1 ⊂ R^2` with angular coordinate `theta`. -/
def angleToSphere2 (theta : Real.Angle) : OptimalAlphabets.SpherePoint 2 :=
  ⟨Complex.orthonormalBasisOneI.repr (theta.toCircle : Complex), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact
      (Complex.orthonormalBasisOneI.repr.norm_map
        (theta.toCircle : Complex)).trans (Circle.norm_coe theta.toCircle)⟩

@[simp] theorem sphere2Angle_angleToSphere2 (theta : Real.Angle) :
    sphere2Angle (angleToSphere2 theta) = theta := by
  simp [sphere2Angle, sphere2Circle, angleToSphere2]

@[simp] theorem angleToSphere2_sphere2Angle
    (u : OptimalAlphabets.SpherePoint 2) :
    angleToSphere2 (sphere2Angle u) = u := by
  apply Subtype.ext
  have hz :
      Real.Angle.toCircle (sphere2Angle u) = sphere2Circle u := by
    simp [sphere2Angle]
  change
    Complex.orthonormalBasisOneI.repr
        (Real.Angle.toCircle (sphere2Angle u) : Complex) = u.1
  rw [hz]
  change
    Complex.orthonormalBasisOneI.repr
      (Complex.orthonormalBasisOneI.repr.symm u.1) = u.1
  exact Complex.orthonormalBasisOneI.repr.apply_symm_apply u.1

/-- The norm on `Real.Angle = R / 2πZ` is the absolute value of the
principal representative in `(-π, π]`. -/
theorem angle_norm_eq_abs_toReal (theta : Real.Angle) :
    ‖theta‖ = |theta.toReal| := by
  have hperiod_ne : (2 * Real.pi : Real) ≠ 0 := by positivity
  have hperiod_pos : 0 < (2 * Real.pi : Real) := by positivity
  have hperiod : |(2 * Real.pi : Real)| / 2 = Real.pi := by
    rw [abs_of_pos hperiod_pos]
    ring
  have hle : |theta.toReal| ≤ |(2 * Real.pi : Real)| / 2 := by
    rw [hperiod]
    exact Real.Angle.abs_toReal_le_pi theta
  have hnorm :=
    (AddCircle.norm_coe_eq_abs_iff
      (p := 2 * Real.pi) (x := theta.toReal) hperiod_ne).2 hle
  change ‖((theta.toReal : Real.Angle))‖ = |theta.toReal| at hnorm
  simpa using hnorm

/-- Under the angular coordinate above, Euclidean angle on `S^1` is the
geodesic norm of the difference of angular coordinates. -/
theorem sphere2_angle_eq_norm_sub
    (u v : OptimalAlphabets.SpherePoint 2) :
    InnerProductGeometry.angle u.1 v.1 =
      ‖sphere2Angle u - sphere2Angle v‖ := by
  have hcomplex :
      InnerProductGeometry.angle u.1 v.1 =
        InnerProductGeometry.angle
          (sphere2Circle u : Complex) (sphere2Circle v : Complex) := by
    simpa [sphere2Circle] using
      (LinearIsometry.angle_map
        (Complex.orthonormalBasisOneI.repr.symm.toLinearIsometry :
          EuclideanSpace Real (Fin 2) →ₗᵢ[Real] Complex)
        u.1 v.1).symm
  rw [hcomplex]
  have hu_ne : (sphere2Circle u : Complex) ≠ 0 := Circle.coe_ne_zero _
  have hv_ne : (sphere2Circle v : Complex) ≠ 0 := Circle.coe_ne_zero _
  rw [Complex.angle_eq_abs_arg hu_ne hv_ne]
  rw [angle_norm_eq_abs_toReal]
  have harg :
      ((Complex.arg ((sphere2Circle u : Complex) / (sphere2Circle v : Complex)) :
          Real) : Real.Angle) =
        sphere2Angle u - sphere2Angle v := by
    simpa [sphere2Angle] using
      Complex.arg_div_coe_angle hu_ne hv_ne
  have hto :
      (sphere2Angle u - sphere2Angle v).toReal =
        Complex.arg ((sphere2Circle u : Complex) / (sphere2Circle v : Complex)) := by
    rw [← harg]
    exact Real.Angle.toReal_coe_eq_self_iff.2
      ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  rw [hto]

/-- The minimum geodesic distance from an angle to a finite angle code. -/
def angleMinDistToCode (C : Finset Real.Angle) (theta : Real.Angle) : Real :=
  if h : C.Nonempty then
    C.inf' h (fun c => ‖theta - c‖)
  else
    Real.pi

/-- Covering radius for a finite code in `Real.Angle`. -/
def angleCovrad (C : Finset Real.Angle) : Real :=
  sSup (Set.range (angleMinDistToCode C))

/-- Finite angle codes of a prescribed cardinality. -/
def angleCodesOfCard (m : Nat) : Set (Finset Real.Angle) :=
  {C | C.card = m}

/-- Optimal covering radius for `m` points on the additive circle. -/
def rhoAngle (m : Nat) : Real :=
  sInf (angleCovrad '' angleCodesOfCard m)

/-- The angular step of the regular `m`-gon in `Real.Angle`. -/
def regularAngleStep (m : Nat) : Real.Angle :=
  (((2 * Real.pi) / (m : Real) : Real) : Real.Angle)

/-- The regular `m`-point angle code.  For `m = 0` this is empty. -/
def regularAngleCode (m : Nat) : Finset Real.Angle :=
  (Finset.range m).image fun k : Nat => k • regularAngleStep m

theorem addOrderOf_regularAngleStep {m : Nat} (hm : 0 < m) :
    addOrderOf (regularAngleStep m) = m := by
  haveI : Fact (0 < (2 * Real.pi : Real)) := ⟨by positivity⟩
  simpa [regularAngleStep] using
    (AddCircle.addOrderOf_period_div
      (p := (2 * Real.pi : Real)) (𝕜 := Real) hm)

@[simp] theorem regularAngleCode_card {m : Nat} (hm : 0 < m) :
    (regularAngleCode m).card = m := by
  classical
  have hinj :
      Set.InjOn (fun k : Nat => k • regularAngleStep m) (Finset.range m) := by
    intro a ha b hb hab
    have ha_lt : a < addOrderOf (regularAngleStep m) := by
      simpa [addOrderOf_regularAngleStep hm] using Finset.mem_range.mp ha
    have hb_lt : b < addOrderOf (regularAngleStep m) := by
      simpa [addOrderOf_regularAngleStep hm] using Finset.mem_range.mp hb
    exact nsmul_injOn_Iio_addOrderOf ha_lt hb_lt hab
  calc
    (regularAngleCode m).card = (Finset.range m).card := by
      simpa [regularAngleCode] using
        (Finset.card_image_of_injOn
          (s := Finset.range m)
          (f := fun k : Nat => k • regularAngleStep m) hinj)
    _ = m := Finset.card_range m

theorem regularAngleCode_mem_angleCodesOfCard {m : Nat} (hm : 0 < m) :
    regularAngleCode m ∈ angleCodesOfCard m := by
  simpa [angleCodesOfCard] using regularAngleCode_card hm

/-- Every angular displacement on `Real.Angle` has geodesic norm at most `pi`. -/
theorem angle_norm_le_pi (theta : Real.Angle) :
    ‖theta‖ <= Real.pi := by
  have hperiod_ne : (2 * Real.pi : Real) ≠ 0 := by positivity
  have hperiod_pos : 0 < (2 * Real.pi : Real) := by positivity
  have h :=
    AddCircle.norm_le_half_period
      (p := (2 * Real.pi : Real)) (x := theta) hperiod_ne
  have hperiod : |(2 * Real.pi : Real)| / 2 = Real.pi := by
    rw [abs_of_pos hperiod_pos]
    ring
  have hpi_abs : |Real.pi| = Real.pi := abs_of_pos Real.pi_pos
  simpa [hperiod, hpi_abs] using h

theorem angleMinDistToCode_le_pi {C : Finset Real.Angle}
    (hC : C.Nonempty) (theta : Real.Angle) :
    angleMinDistToCode C theta <= Real.pi := by
  classical
  rcases hC with ⟨c, hc⟩
  unfold angleMinDistToCode
  rw [dif_pos ⟨c, hc⟩]
  exact
    (Finset.inf'_le (s := C) (f := fun c => ‖theta - c‖) hc).trans
      (angle_norm_le_pi (theta - c))

theorem regularAngleCode_nonempty {m : Nat} (hm : 0 < m) :
    (regularAngleCode m).Nonempty := by
  simpa [regularAngleCode] using
    (Finset.nonempty_range_iff.2 hm.ne').image
      (fun k : Nat => k • regularAngleStep m)

/-- Every angle is within `pi / m` of some point of the regular `m`-point code. -/
theorem exists_regularAngleCode_norm_sub_le_pi_div
    {m : Nat} (hm : 0 < m) (theta : Real.Angle) :
    ∃ c ∈ regularAngleCode m, ‖theta - c‖ <= Real.pi / (m : Real) := by
  classical
  haveI : Fact (0 < (2 * Real.pi : Real)) := ⟨by positivity⟩
  let psi : Real.Angle :=
    ((((m • theta).toReal / (m : Real)) : Real) : Real.Angle)
  have hm_real_pos : 0 < (m : Real) := by exact_mod_cast hm
  have hm_real_ne : (m : Real) ≠ 0 := ne_of_gt hm_real_pos
  have hm_real_ge_one : (1 : Real) <= (m : Real) := by exact_mod_cast hm
  have hmpsi : m • psi = m • theta := by
    calc
      m • psi =
          (((m : Real) * ((m • theta).toReal / (m : Real)) : Real) :
            Real.Angle) := by
        simp [psi]
      _ = (((m • theta).toReal : Real) : Real.Angle) := by
        rw [mul_div_cancel₀ _ hm_real_ne]
      _ = m • theta := Real.Angle.coe_toReal (m • theta)
  have hker : m • (theta - psi) = 0 := by
    rw [nsmul_sub, hmpsi, sub_self]
  rcases
      (AddCircle.nsmul_eq_zero_iff
        (p := (2 * Real.pi : Real)) (u := theta - psi) hm).1 hker with
    ⟨k, hklt, hk⟩
  let c : Real.Angle := k • regularAngleStep m
  have hc : c ∈ regularAngleCode m := by
    exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 hklt, rfl⟩
  have hc_eq : c = theta - psi := by
    rw [← hk]
    change k • ((((2 * Real.pi) / (m : Real) : Real) : Real.Angle)) =
      (((k : Real) / (m : Real) * (2 * Real.pi) : Real) :
        Real.Angle)
    calc
      k • ((((2 * Real.pi) / (m : Real) : Real) : Real.Angle))
          =
            (((k • ((2 * Real.pi) / (m : Real) : Real)) : Real) :
              Real.Angle) := by
        exact
          (AddCircle.coe_nsmul
            (p := (2 * Real.pi : Real)) (n := k)
            (x := ((2 * Real.pi) / (m : Real) : Real))).symm
      _ = (((k : Real) / (m : Real) * (2 * Real.pi) : Real) :
            Real.Angle) := by
        congr 1
        simp [nsmul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have htheta_sub : theta - c = psi := by
    rw [hc_eq]
    simp [sub_eq_add_neg, add_comm]
  have hpsi_abs_le_pi_div :
      |(m • theta).toReal / (m : Real)| <= Real.pi / (m : Real) := by
    rw [abs_div, abs_of_pos hm_real_pos]
    exact div_le_div_of_nonneg_right
      (Real.Angle.abs_toReal_le_pi (m • theta)) hm_real_pos.le
  have hperiod_ne : (2 * Real.pi : Real) ≠ 0 := by positivity
  have hperiod_pos : 0 < (2 * Real.pi : Real) := by positivity
  have hperiod : |(2 * Real.pi : Real)| / 2 = Real.pi := by
    rw [abs_of_pos hperiod_pos]
    ring
  have hpsi_abs_le_pi :
      |(m • theta).toReal / (m : Real)| <= |(2 * Real.pi : Real)| / 2 := by
    rw [hperiod]
    exact hpsi_abs_le_pi_div.trans
      (div_le_self Real.pi_pos.le hm_real_ge_one)
  have hpsi_norm_eq :
      ‖psi‖ = |(m • theta).toReal / (m : Real)| := by
    change
      ‖((((m • theta).toReal / (m : Real)) : Real) : Real.Angle)‖ =
        |(m • theta).toReal / (m : Real)|
    exact
      (AddCircle.norm_coe_eq_abs_iff
        (p := (2 * Real.pi : Real))
        (x := (m • theta).toReal / (m : Real)) hperiod_ne).2 hpsi_abs_le_pi
  refine ⟨c, hc, ?_⟩
  rw [htheta_sub, hpsi_norm_eq]
  exact hpsi_abs_le_pi_div

theorem angleMinDistToRegularAngleCode_le_pi_div
    {m : Nat} (hm : 0 < m) (theta : Real.Angle) :
    angleMinDistToCode (regularAngleCode m) theta <=
      Real.pi / (m : Real) := by
  classical
  rcases exists_regularAngleCode_norm_sub_le_pi_div hm theta with
    ⟨c, hc, hle⟩
  unfold angleMinDistToCode
  rw [dif_pos (regularAngleCode_nonempty hm)]
  exact
    (Finset.inf'_le
      (s := regularAngleCode m) (f := fun c => ‖theta - c‖) hc).trans hle

theorem angleCovrad_regularAngleCode_le_pi_div
    {m : Nat} (hm : 0 < m) :
    angleCovrad (regularAngleCode m) <= Real.pi / (m : Real) := by
  unfold angleCovrad
  refine Real.sSup_le ?_ (div_nonneg Real.pi_nonneg (Nat.cast_nonneg m))
  rintro r ⟨theta, rfl⟩
  exact angleMinDistToRegularAngleCode_le_pi_div hm theta

theorem angleMinDistToCode_nonneg
    (C : Finset Real.Angle) (theta : Real.Angle) :
    0 <= angleMinDistToCode C theta := by
  classical
  unfold angleMinDistToCode
  split_ifs with hC
  · exact
      Finset.le_inf'
        (s := C) (H := hC) (f := fun c => ‖theta - c‖)
        (fun c _hc => norm_nonneg (theta - c))
  · exact Real.pi_nonneg

theorem angleCovrad_nonneg (C : Finset Real.Angle) :
    0 <= angleCovrad C := by
  unfold angleCovrad
  refine Real.sSup_nonneg ?_
  rintro r ⟨theta, rfl⟩
  exact angleMinDistToCode_nonneg C theta

theorem angleMinDistToCode_le_angleCovrad
    {C : Finset Real.Angle} (hC : C.Nonempty) (theta : Real.Angle) :
    angleMinDistToCode C theta <= angleCovrad C := by
  unfold angleCovrad
  have hbdd : BddAbove (Set.range (angleMinDistToCode C)) :=
    ⟨Real.pi, by
      rintro r ⟨theta, rfl⟩
      exact angleMinDistToCode_le_pi hC theta⟩
  exact le_csSup hbdd ⟨theta, rfl⟩

theorem volumeReal_univ_angle :
    volume.real (Set.univ : Set Real.Angle) = 2 * Real.pi := by
  change (volume (Set.univ : Set (AddCircle (2 * Real.pi)))).toReal =
    2 * Real.pi
  rw [AddCircle.measure_univ]
  exact ENNReal.toReal_ofReal (by positivity)

theorem volumeReal_closedBall_angle
    {theta : Real.Angle} {r : Real} (hr_nonneg : 0 <= r)
    (hr_le_pi : r <= Real.pi) :
    volume.real (Metric.closedBall theta r) = 2 * r := by
  change (volume (Metric.closedBall (theta : AddCircle (2 * Real.pi)) r)).toReal =
    2 * r
  have hvol :
      volume (Metric.closedBall (theta : AddCircle (2 * Real.pi)) r) =
        ENNReal.ofReal (min (2 * Real.pi) (2 * r)) :=
    AddCircle.volume_closedBall (x := (theta : AddCircle (2 * Real.pi))) (ε := r)
  rw [hvol]
  have hmin : min (2 * Real.pi) (2 * r) = 2 * r :=
    min_eq_right (by nlinarith [hr_le_pi])
  rw [hmin]
  exact ENNReal.toReal_ofReal (mul_nonneg zero_le_two hr_nonneg)

theorem exists_angleMinDistToCode_gt_of_lt_pi_div_card
    {C : Finset Real.Angle} {r : Real} (hC : C.Nonempty)
    (hr_nonneg : 0 <= r) (hr : r < Real.pi / (C.card : Real)) :
    ∃ theta : Real.Angle, r < angleMinDistToCode C theta := by
  classical
  have hcard_pos_nat : 0 < C.card := Finset.card_pos.2 hC
  have hcard_pos : 0 < (C.card : Real) := by exact_mod_cast hcard_pos_nat
  have hcard_ge_one : (1 : Real) <= C.card := by
    exact_mod_cast (Nat.succ_le_of_lt hcard_pos_nat)
  have hr_mul : r * (C.card : Real) < Real.pi := by
    rwa [lt_div_iff₀ hcard_pos] at hr
  have hr_le_pi : r <= Real.pi :=
    (hr.trans_le (div_le_self Real.pi_pos.le hcard_ge_one)).le
  let U : Set Real.Angle := ⋃ c ∈ C, Metric.closedBall c r
  have hU_ne_univ : U ≠ Set.univ := by
    intro hU
    have hvol_le :=
      measureReal_biUnion_finset_le
        (μ := volume) C (fun c : Real.Angle => Metric.closedBall c r)
    have hvol_le' :
        2 * Real.pi <=
          ∑ c ∈ C, volume.real (Metric.closedBall c r) := by
      simpa [U, hU, volumeReal_univ_angle] using hvol_le
    have hsum_eq :
        (∑ c ∈ C, volume.real (Metric.closedBall c r)) =
          (C.card : Real) * (2 * r) := by
      simp [volumeReal_closedBall_angle hr_nonneg hr_le_pi]
    have hsum_lt :
        (∑ c ∈ C, volume.real (Metric.closedBall c r)) <
          2 * Real.pi := by
      rw [hsum_eq]
      nlinarith
    exact (not_lt_of_ge hvol_le') hsum_lt
  have hnot_cover : ∃ theta : Real.Angle, theta ∉ U := by
    by_contra h
    apply hU_ne_univ
    exact eq_univ_iff_forall.2 fun theta => by
      by_contra htheta
      exact h ⟨theta, htheta⟩
  rcases hnot_cover with ⟨theta, htheta⟩
  refine ⟨theta, ?_⟩
  have hdist : ∀ c ∈ C, r < ‖theta - c‖ := by
    intro c hc
    have hnot_ball : theta ∉ Metric.closedBall c r := by
      intro hmem
      exact htheta (by
        refine Set.mem_iUnion.2 ⟨c, ?_⟩
        exact Set.mem_iUnion.2 ⟨hc, hmem⟩)
    rw [Metric.mem_closedBall, dist_eq_norm] at hnot_ball
    exact not_le.1 hnot_ball
  unfold angleMinDistToCode
  rw [dif_pos hC]
  exact (Finset.lt_inf'_iff (s := C) (H := hC)
    (f := fun c => ‖theta - c‖)).2 hdist

theorem pi_div_card_le_angleCovrad
    {C : Finset Real.Angle} (hC : C.Nonempty) :
    Real.pi / (C.card : Real) <= angleCovrad C := by
  by_contra h
  have hlt : angleCovrad C < Real.pi / (C.card : Real) := lt_of_not_ge h
  rcases
      exists_angleMinDistToCode_gt_of_lt_pi_div_card
        (C := C) hC (angleCovrad_nonneg C) hlt with
    ⟨theta, htheta⟩
  exact not_lt_of_ge (angleMinDistToCode_le_angleCovrad hC theta) htheta

theorem pi_div_le_rhoAngle {m : Nat} (hm : 1 <= m) :
    Real.pi / (m : Real) <= rhoAngle m := by
  classical
  have hm_pos : 0 < m := by omega
  unfold rhoAngle
  refine le_csInf ?hne ?lower
  · exact
      ⟨angleCovrad (regularAngleCode m),
        ⟨regularAngleCode m, regularAngleCode_mem_angleCodesOfCard hm_pos, rfl⟩⟩
  · rintro r ⟨C, hC, rfl⟩
    have hcard : C.card = m := by
      simpa [angleCodesOfCard] using hC
    have hC_nonempty : C.Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    simpa [hcard] using pi_div_card_le_angleCovrad hC_nonempty

theorem rhoAngle_le_pi_div {m : Nat} (hm : 1 <= m) :
    rhoAngle m <= Real.pi / (m : Real) := by
  classical
  have hm_pos : 0 < m := by omega
  unfold rhoAngle
  have hbdd : BddBelow (angleCovrad '' angleCodesOfCard m) := by
    refine ⟨0, ?_⟩
    rintro r ⟨C, _hC, rfl⟩
    exact angleCovrad_nonneg C
  have hmem :
      angleCovrad (regularAngleCode m) ∈ angleCovrad '' angleCodesOfCard m :=
    ⟨regularAngleCode m, regularAngleCode_mem_angleCodesOfCard hm_pos, rfl⟩
  exact
    (csInf_le hbdd hmem).trans
      (angleCovrad_regularAngleCode_le_pi_div hm_pos)

theorem rhoAngle_eq_pi_div {m : Nat} (hm : 1 <= m) :
    rhoAngle m = Real.pi / (m : Real) :=
  le_antisymm (rhoAngle_le_pi_div hm) (pi_div_le_rhoAngle hm)

theorem angleToSphere2_injective : Function.Injective angleToSphere2 := by
  intro theta psi h
  have h' := congrArg sphere2Angle h
  simpa using h'

theorem sphere2Angle_injective : Function.Injective sphere2Angle := by
  intro u v h
  have h' := congrArg angleToSphere2 h
  simpa using h'

@[simp] theorem angleToSphere2_image_card (C : Finset Real.Angle) :
    (C.image angleToSphere2).card = C.card := by
  classical
  exact Finset.card_image_of_injective C angleToSphere2_injective

@[simp] theorem sphere2Angle_image_card
    (C : Finset (OptimalAlphabets.SpherePoint 2)) :
    (C.image sphere2Angle).card = C.card := by
  classical
  exact Finset.card_image_of_injective C sphere2Angle_injective

theorem minAngleToSphericalCode_angleToSphere2_image
    (C : Finset Real.Angle) (theta : Real.Angle) :
    OptimalAlphabets.minAngleToSphericalCode
        (C.image angleToSphere2) (angleToSphere2 theta) =
      angleMinDistToCode C theta := by
  classical
  unfold OptimalAlphabets.minAngleToSphericalCode angleMinDistToCode
  by_cases hC : C.Nonempty
  · have hImg : (C.image angleToSphere2).Nonempty := hC.image _
    rw [dif_pos hImg, dif_pos hC]
    rw [Finset.inf'_image hImg]
    refine Finset.inf'_congr hC rfl ?_
    intro c hc
    simpa using sphere2_angle_eq_norm_sub (angleToSphere2 theta) (angleToSphere2 c)
  · have hImg : ¬ (C.image angleToSphere2).Nonempty := by
      simpa [Finset.image_nonempty] using hC
    rw [dif_neg hImg, dif_neg hC]

theorem angleMinDistToCode_sphere2Angle_image
    (C : Finset (OptimalAlphabets.SpherePoint 2))
    (u : OptimalAlphabets.SpherePoint 2) :
    angleMinDistToCode (C.image sphere2Angle) (sphere2Angle u) =
      OptimalAlphabets.minAngleToSphericalCode C u := by
  classical
  unfold OptimalAlphabets.minAngleToSphericalCode angleMinDistToCode
  by_cases hC : C.Nonempty
  · have hImg : (C.image sphere2Angle).Nonempty := hC.image _
    rw [dif_pos hImg, dif_pos hC]
    rw [Finset.inf'_image hImg]
    refine Finset.inf'_congr hC rfl ?_
    intro v hv
    simpa [InnerProductGeometry.angle_comm, norm_neg, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc] using
      (sphere2_angle_eq_norm_sub u v).symm
  · have hImg : ¬ (C.image sphere2Angle).Nonempty := by
      simpa [Finset.image_nonempty] using hC
    rw [dif_neg hImg, dif_neg hC]

/-- Transport of covering radius from angle codes to spherical codes in
dimension two. -/
theorem covrad_sph_angleToSphere2_image (C : Finset Real.Angle) :
    OptimalAlphabets.covrad_sph (C.image angleToSphere2) =
      angleCovrad C := by
  unfold OptimalAlphabets.covrad_sph angleCovrad
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨sphere2Angle u, ?_⟩
    calc
      angleMinDistToCode C (sphere2Angle u)
          = OptimalAlphabets.minAngleToSphericalCode
              (C.image angleToSphere2) (angleToSphere2 (sphere2Angle u)) := by
            exact (minAngleToSphericalCode_angleToSphere2_image
              C (sphere2Angle u)).symm
      _ = OptimalAlphabets.minAngleToSphericalCode
              (C.image angleToSphere2) u := by
            rw [angleToSphere2_sphere2Angle u]
  · rintro ⟨theta, rfl⟩
    exact ⟨angleToSphere2 theta,
      minAngleToSphericalCode_angleToSphere2_image C theta⟩

/-- Transport of covering radius from spherical codes in dimension two to
angle codes. -/
theorem angleCovrad_sphere2Angle_image
    (C : Finset (OptimalAlphabets.SpherePoint 2)) :
    angleCovrad (C.image sphere2Angle) =
      OptimalAlphabets.covrad_sph C := by
  unfold OptimalAlphabets.covrad_sph angleCovrad
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨theta, rfl⟩
    refine ⟨angleToSphere2 theta, ?_⟩
    calc
      OptimalAlphabets.minAngleToSphericalCode C (angleToSphere2 theta)
          = angleMinDistToCode
              (C.image sphere2Angle) (sphere2Angle (angleToSphere2 theta)) := by
            exact (angleMinDistToCode_sphere2Angle_image
              C (angleToSphere2 theta)).symm
      _ = angleMinDistToCode (C.image sphere2Angle) theta := by
            rw [sphere2Angle_angleToSphere2 theta]
  · rintro ⟨u, rfl⟩
    exact ⟨sphere2Angle u, angleMinDistToCode_sphere2Angle_image C u⟩

/-- The dimension-2 spherical-code optimization is exactly the finite
covering-radius optimization on `Real.Angle`. -/
theorem rhoSph_two_eq_rhoAngle (m : Nat) :
    rhoSph 2 m = rhoAngle m := by
  classical
  unfold rhoSph OptimalAlphabets.rho_sph rhoAngle angleCodesOfCard
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨C, hC, rfl⟩
    refine ⟨C.image sphere2Angle, ?_, ?_⟩
    · have hcardC : C.card = m := by
        simpa [OptimalAlphabets.sphericalCodesOfCard] using hC
      have hcard : (C.image sphere2Angle).card = m := by
        rw [sphere2Angle_image_card C, hcardC]
      simpa [angleCodesOfCard] using hcard
    · exact angleCovrad_sphere2Angle_image C
  · rintro ⟨C, hC, rfl⟩
    refine ⟨C.image angleToSphere2, ?_, ?_⟩
    · have hcard : (C.image angleToSphere2).card = m := by
        rw [angleToSphere2_image_card C, hC]
      simpa [OptimalAlphabets.sphericalCodesOfCard] using hcard
    · exact covrad_sph_angleToSphere2_image C

/-- Lemma 1: exact spherical optimum on the circle. -/
def lemma1_exact_spherical_optimum_on_circle_statement : Prop :=
  forall m : Nat, 1 <= m -> rhoSph 2 m = Real.pi / (m : Real)

/-- Lemma 1, theorem-backed literal statement. -/
theorem lemma1_exact_spherical_optimum_on_circle :
    lemma1_exact_spherical_optimum_on_circle_statement := by
  intro m hm
  rw [rhoSph_two_eq_rhoAngle, rhoAngle_eq_pi_div hm]

/-- Theorem 1: complete dimension-2 classification. -/
def theorem1_complete_dimension2_classification_statement : Prop :=
  forall A : Finset Real, 2 <= A.card ->
    (IsAntipodalBinary A ∧ F 2 A = rhoSph 2 (A.card ^ 2)) ∨
    ((¬ IsAntipodalBinary A) ∧ rhoSph 2 (A.card ^ 2) < F 2 A)

/-- Appendix Lemma 5: collisions in dimension 2. -/
def appendix_lemma5_collisions_in_dimension2_statement : Prop :=
  forall A : Finset Real, 2 <= A.card ->
    ((0 : Real) ∈ A ∨
      (∃ a : Real, ∃ b : Real,
        a ∈ A ∧ b ∈ A ∧ 0 < a ∧ 0 < b ∧ a ≠ b) ∨
      (∃ a : Real, ∃ b : Real,
        a ∈ A ∧ b ∈ A ∧ a < 0 ∧ b < 0 ∧ a ≠ b)) ->
    (Pdir 2 A).card <= A.card ^ 2 - 1 ∧
      F 2 A > Real.pi / ((A.card ^ 2 : Nat) : Real)

/-- Cardinality half of Appendix Lemma 5. -/
def appendix_lemma5_direction_count_statement : Prop :=
  forall A : Finset Real, 2 <= A.card ->
    ((0 : Real) ∈ A ∨
      (∃ a : Real, ∃ b : Real,
        a ∈ A ∧ b ∈ A ∧ 0 < a ∧ 0 < b ∧ a ≠ b) ∨
      (∃ a : Real, ∃ b : Real,
        a ∈ A ∧ b ∈ A ∧ a < 0 ∧ b < 0 ∧ a ≠ b)) ->
    (Pdir 2 A).card <= A.card ^ 2 - 1

private theorem nonzeroProductTuples_subset_productTuples
    (n : Nat) (A : Finset Real) :
    nonzeroProductTuples n A ⊆ productTuples n A := by
  intro x hx
  exact OptimalAlphabets.AsymmetricProduct.mem_asymProductTuples.2
    (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1 hx).1

private theorem productTuples_card_two (A : Finset Real) :
    (productTuples 2 A).card = A.card ^ 2 := by
  simpa [productTuples] using
    (OptimalAlphabets.AsymmetricProduct.asymProductTuples_card 2 A)

private theorem Pdir_card_le_nonzeroProductTuples_card
    (n : Nat) (A : Finset Real) :
    (Pdir n A).card <= (nonzeroProductTuples n A).card := by
  classical
  simpa [Pdir, nonzeroProductTuples] using
    (Finset.card_image_le
      (s := OptimalAlphabets.AsymmetricProduct.nonzeroAsymProductTuples n A)
      (f := fun x : Fin n -> Real =>
        NormedSpace.normalize
          (OptimalAlphabets.AsymmetricProduct.tupleVector x)))

private theorem Pdir_card_lt_nonzeroProductTuples_card_of_collision
    {A : Finset Real} {x y : Fin 2 -> Real}
    (hx : x ∈ nonzeroProductTuples 2 A)
    (hy : y ∈ nonzeroProductTuples 2 A)
    (hxy : x ≠ y)
    (hdir :
      NormedSpace.normalize (OptimalAlphabets.AsymmetricProduct.tupleVector x) =
        NormedSpace.normalize (OptimalAlphabets.AsymmetricProduct.tupleVector y)) :
    (Pdir 2 A).card < (nonzeroProductTuples 2 A).card := by
  classical
  have hnotinj :
      ¬ Set.InjOn
        (fun z : Fin 2 -> Real =>
          NormedSpace.normalize
            (OptimalAlphabets.AsymmetricProduct.tupleVector z))
        (nonzeroProductTuples 2 A) := by
    intro hinj
    exact hxy (hinj hx hy hdir)
  have hcard_ne :
      ((nonzeroProductTuples 2 A).image
        (fun z : Fin 2 -> Real =>
          NormedSpace.normalize
            (OptimalAlphabets.AsymmetricProduct.tupleVector z))).card ≠
        (nonzeroProductTuples 2 A).card := by
    intro hcard_eq
    exact hnotinj (Finset.injOn_of_card_image_eq hcard_eq)
  simpa [Pdir] using lt_of_le_of_ne Finset.card_image_le hcard_ne

private theorem Pdir_card_lt_card_sq_of_zero_mem
    {A : Finset Real} (hzero : (0 : Real) ∈ A) :
    (Pdir 2 A).card < A.card ^ 2 := by
  classical
  let z : Fin 2 -> Real := fun _ => 0
  have hz_prod : z ∈ productTuples 2 A :=
    OptimalAlphabets.AsymmetricProduct.mem_asymProductTuples.2
      (fun _ => hzero)
  have hz_not_nonzero : z ∉ nonzeroProductTuples 2 A := by
    intro hz
    have hz_ne :=
      (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1 hz).2
    apply hz_ne
    ext i
    simp [z, OptimalAlphabets.AsymmetricProduct.tupleVector]
  have hsubset := nonzeroProductTuples_subset_productTuples 2 A
  have hstrict : nonzeroProductTuples 2 A ⊂ productTuples 2 A :=
    (Finset.ssubset_iff_of_subset hsubset).2 ⟨z, hz_prod, hz_not_nonzero⟩
  calc
    (Pdir 2 A).card <= (nonzeroProductTuples 2 A).card :=
      Pdir_card_le_nonzeroProductTuples_card 2 A
    _ < (productTuples 2 A).card := Finset.card_lt_card hstrict
    _ = A.card ^ 2 := productTuples_card_two A

private theorem Pdir_card_lt_card_sq_of_same_ray_pair
    {A : Finset Real} {a b : Real}
    (ha_mem : a ∈ A) (hb_mem : b ∈ A)
    (ha_ne : a ≠ 0) (hb_ne : b ≠ 0)
    (hab : a ≠ b) (hscale_pos : 0 < a / b) :
    (Pdir 2 A).card < A.card ^ 2 := by
  classical
  let x : Fin 2 -> Real := fun _ => a
  let y : Fin 2 -> Real := fun _ => b
  have hx : x ∈ nonzeroProductTuples 2 A := by
    refine OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.2
      ⟨fun _ => ha_mem, ?_⟩
    rw [OptimalAlphabets.AsymmetricProduct.tupleVector_ne_zero_iff]
    exact ⟨0, by simpa [x] using ha_ne⟩
  have hy : y ∈ nonzeroProductTuples 2 A := by
    refine OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.2
      ⟨fun _ => hb_mem, ?_⟩
    rw [OptimalAlphabets.AsymmetricProduct.tupleVector_ne_zero_iff]
    exact ⟨0, by simpa [y] using hb_ne⟩
  have hxy : x ≠ y := by
    intro h
    exact hab (by simpa [x, y] using congrFun h (0 : Fin 2))
  have hvec :
      OptimalAlphabets.AsymmetricProduct.tupleVector x =
        (a / b) • OptimalAlphabets.AsymmetricProduct.tupleVector y := by
    ext i
    simp [x, y, OptimalAlphabets.AsymmetricProduct.tupleVector]
    field_simp [hb_ne]
  have hdir :
      NormedSpace.normalize
          (OptimalAlphabets.AsymmetricProduct.tupleVector x) =
        NormedSpace.normalize
          (OptimalAlphabets.AsymmetricProduct.tupleVector y) := by
    rw [hvec]
    exact NormedSpace.normalize_smul_of_pos hscale_pos
      (OptimalAlphabets.AsymmetricProduct.tupleVector y)
  have hlt_nonzero :=
    Pdir_card_lt_nonzeroProductTuples_card_of_collision
      (A := A) hx hy hxy hdir
  have hle_nonzero :
      (nonzeroProductTuples 2 A).card <= A.card ^ 2 := by
    calc
      (nonzeroProductTuples 2 A).card <= (productTuples 2 A).card :=
        Finset.card_le_card (nonzeroProductTuples_subset_productTuples 2 A)
      _ = A.card ^ 2 := productTuples_card_two A
  exact lt_of_lt_of_le hlt_nonzero hle_nonzero

/-- Appendix Lemma 5, theorem-backed direction-count half. -/
theorem appendix_lemma5_direction_count_bound :
    appendix_lemma5_direction_count_statement := by
  intro A _hcard hcollision
  have hlt : (Pdir 2 A).card < A.card ^ 2 := by
    rcases hcollision with hzero | hsameSign
    · exact Pdir_card_lt_card_sq_of_zero_mem hzero
    · rcases hsameSign with hpos | hneg
      · rcases hpos with ⟨a, b, ha_mem, hb_mem, ha_pos, hb_pos, hab⟩
        exact Pdir_card_lt_card_sq_of_same_ray_pair
          ha_mem hb_mem (ne_of_gt ha_pos) (ne_of_gt hb_pos) hab
          (div_pos ha_pos hb_pos)
      · rcases hneg with ⟨a, b, ha_mem, hb_mem, ha_neg, hb_neg, hab⟩
        exact Pdir_card_lt_card_sq_of_same_ray_pair
          ha_mem hb_mem (ne_of_lt ha_neg) (ne_of_lt hb_neg) hab
          (div_pos_of_neg_of_neg ha_neg hb_neg)
  exact Nat.le_sub_one_of_lt hlt

/-- Appendix Lemma 6: no-collision case. -/
def appendix_lemma6_no_collision_case_statement : Prop :=
  forall A : Finset Real, 2 <= A.card ->
    ¬ ((0 : Real) ∈ A) ->
    ¬ (∃ a : Real, ∃ b : Real,
      a ∈ A ∧ b ∈ A ∧ 0 < a ∧ 0 < b ∧ a ≠ b) ->
    ¬ (∃ a : Real, ∃ b : Real,
      a ∈ A ∧ b ∈ A ∧ a < 0 ∧ b < 0 ∧ a ≠ b) ->
    ∃ u : Real, ∃ v : Real,
      0 < u ∧ 0 < v ∧
        forall x : Real, x ∈ A ↔ x = -u ∨ x = v

/-- Appendix Lemma 6: theorem-backed scalar no-collision classification.

If a finite real alphabet has at least two elements, no zero, and no two
distinct elements of the same sign, then it consists of exactly one negative
and one positive value. -/
theorem appendix_lemma6_no_collision_case :
    appendix_lemma6_no_collision_case_statement := by
  intro A hcard hzero hposPair hnegPair
  have hone : 1 < A.card := by omega
  rcases Finset.one_lt_card_iff.1 hone with ⟨a, b, ha, hb, hab⟩
  have hane : a ≠ 0 := by
    intro ha0
    exact hzero (by simpa [ha0] using ha)
  have hbne : b ≠ 0 := by
    intro hb0
    exact hzero (by simpa [hb0] using hb)
  rcases lt_or_gt_of_ne hane.symm with ha_pos | ha_neg
  · rcases lt_or_gt_of_ne hbne.symm with hb_pos | hb_neg
    · exact False.elim
        (hposPair ⟨a, b, ha, hb, ha_pos, hb_pos, hab⟩)
    · refine ⟨-b, a, by linarith, ha_pos, ?_⟩
      intro x
      constructor
      · intro hx
        have hxne : x ≠ 0 := by
          intro hx0
          exact hzero (by simpa [hx0] using hx)
        rcases lt_or_gt_of_ne hxne.symm with hx_pos | hx_neg
        · have hxa : x = a := by
            by_contra hxa
            exact hposPair ⟨x, a, hx, ha, hx_pos, ha_pos, hxa⟩
          exact Or.inr hxa
        · have hxb : x = b := by
            by_contra hxb
            exact hnegPair ⟨x, b, hx, hb, hx_neg, hb_neg, hxb⟩
          exact Or.inl (by linarith)
      · rintro (hxb | hxa)
        · have hxb' : x = b := by linarith
          simpa [hxb'] using hb
        · simpa [hxa] using ha
  · rcases lt_or_gt_of_ne hbne.symm with hb_pos | hb_neg
    · refine ⟨-a, b, by linarith, hb_pos, ?_⟩
      intro x
      constructor
      · intro hx
        have hxne : x ≠ 0 := by
          intro hx0
          exact hzero (by simpa [hx0] using hx)
        rcases lt_or_gt_of_ne hxne.symm with hx_pos | hx_neg
        · have hxb : x = b := by
            by_contra hxb
            exact hposPair ⟨x, b, hx, hb, hx_pos, hb_pos, hxb⟩
          exact Or.inr hxb
        · have hxa : x = a := by
            by_contra hxa
            exact hnegPair ⟨x, a, hx, ha, hx_neg, ha_neg, hxa⟩
          exact Or.inl (by linarith)
      · rintro (hxa | hxb)
        · have hxa' : x = a := by linarith
          simpa [hxa'] using ha
        · simpa [hxb] using hb
    · exact False.elim
        (hnegPair ⟨a, b, ha, hb, ha_neg, hb_neg, hab⟩)

/-- Antipodal binary alphabets have exactly two scalar values. -/
theorem IsAntipodalBinary.card_eq_two {A : Finset Real}
    (hA : IsAntipodalBinary A) :
    A.card = 2 := by
  classical
  rcases hA with ⟨a, ha_pos, hmem⟩
  have hAeq : A = ({-a, a} : Finset Real) := by
    ext x
    simpa [Finset.mem_insert, Finset.mem_singleton] using hmem x
  have hne : -a ≠ a := by
    intro h
    have : a = 0 := by linarith
    linarith
  rw [hAeq]
  simp [hne]

/-- In dimension two, every alphabet with at least three values satisfies one
of the collision alternatives from Appendix Lemma 5. -/
theorem dimension2_collision_condition_of_card_ge_three
    {A : Finset Real} (hcard : 3 <= A.card) :
    (0 : Real) ∈ A ∨
      (∃ a : Real, ∃ b : Real,
        a ∈ A ∧ b ∈ A ∧ 0 < a ∧ 0 < b ∧ a ≠ b) ∨
      (∃ a : Real, ∃ b : Real,
        a ∈ A ∧ b ∈ A ∧ a < 0 ∧ b < 0 ∧ a ≠ b) := by
  classical
  by_cases hzero : (0 : Real) ∈ A
  · exact Or.inl hzero
  · by_cases hposPair :
        ∃ a : Real, ∃ b : Real,
          a ∈ A ∧ b ∈ A ∧ 0 < a ∧ 0 < b ∧ a ≠ b
    · exact Or.inr (Or.inl hposPair)
    · by_cases hnegPair :
          ∃ a : Real, ∃ b : Real,
            a ∈ A ∧ b ∈ A ∧ a < 0 ∧ b < 0 ∧ a ≠ b
      · exact Or.inr (Or.inr hnegPair)
      · have hnocoll := appendix_lemma6_no_collision_case
          (A := A) (by omega) hzero hposPair hnegPair
        rcases hnocoll with ⟨u, v, hu_pos, hv_pos, hmem⟩
        have hAeq : A = ({-u, v} : Finset Real) := by
          ext x
          simpa [Finset.mem_insert, Finset.mem_singleton] using hmem x
        have hne : -u ≠ v := by
          intro h
          linarith
        have hcard_two : A.card = 2 := by
          rw [hAeq]
          simp [hne]
        omega

/-- The cardinality half of Corollary 5: for every `q >= 3`, the
dimension-2 product directions have a collision. -/
theorem corollary5_direction_count_bound
    {q : Nat} (hq : 3 <= q) {A : Finset Real} (hA : A ∈ Aq q) :
    (Pdir 2 A).card <= q ^ 2 - 1 := by
  have hcard : A.card = q := by
    simpa [Aq] using hA
  have hcollision :
      (0 : Real) ∈ A ∨
        (∃ a : Real, ∃ b : Real,
          a ∈ A ∧ b ∈ A ∧ 0 < a ∧ 0 < b ∧ a ≠ b) ∨
        (∃ a : Real, ∃ b : Real,
          a ∈ A ∧ b ∈ A ∧ a < 0 ∧ b < 0 ∧ a ≠ b) :=
    dimension2_collision_condition_of_card_ge_three
      (A := A) (by omega)
  have hbound :=
    appendix_lemma5_direction_count_bound
      A (by omega) hcollision
  simpa [hcard] using hbound

private theorem exists_nonzero_mem_of_one_lt_card {A : Finset Real}
    (hcard : 1 < A.card) :
    ∃ a : Real, a ∈ A ∧ a ≠ 0 := by
  classical
  by_contra h
  have hzero : ∀ a : Real, a ∈ A -> a = 0 := by
    intro a ha
    by_contra hane
    exact h ⟨a, ha, hane⟩
  have hsubset : A ⊆ ({0} : Finset Real) := by
    intro a ha
    simp [hzero a ha]
  have hle : A.card <= ({0} : Finset Real).card :=
    Finset.card_le_card hsubset
  simp at hle
  omega

private theorem Pdir_two_nonempty_of_one_lt_card {A : Finset Real}
    (hcard : 1 < A.card) :
    (Pdir 2 A).Nonempty := by
  classical
  rcases exists_nonzero_mem_of_one_lt_card hcard with ⟨a, ha, hane⟩
  let x : Fin 2 -> Real := fun _ => a
  have hx : x ∈ nonzeroProductTuples 2 A := by
    refine OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.2
      ⟨fun _ => ha, ?_⟩
    rw [OptimalAlphabets.AsymmetricProduct.tupleVector_ne_zero_iff]
    exact ⟨0, by simpa [x] using hane⟩
  refine
    ⟨NormedSpace.normalize
      (OptimalAlphabets.AsymmetricProduct.tupleVector x), ?_⟩
  rw [Pdir, OptimalAlphabets.AsymmetricProduct.mem_asymProdDirections]
  exact ⟨x, hx, rfl⟩

/-- If a two-dimensional product alphabet has fewer directions than raw
tuples, the exact circle optimum makes the product covering radius strictly
larger than the `|A|^2`-point spherical optimum. -/
theorem dimension2_strict_lower_bound_of_direction_count
    {A : Finset Real} (hcard : 2 <= A.card)
    (hdir : (Pdir 2 A).card <= A.card ^ 2 - 1) :
    Real.pi / ((A.card ^ 2 : Nat) : Real) < F 2 A := by
  have hP_nonempty : (Pdir 2 A).Nonempty :=
    Pdir_two_nonempty_of_one_lt_card (by omega)
  have hP_pos_nat : 0 < (Pdir 2 A).card :=
    Finset.card_pos.2 hP_nonempty
  have hP_pos : 0 < ((Pdir 2 A).card : Real) := by
    exact_mod_cast hP_pos_nat
  have hcard_pos_nat : 0 < A.card := by omega
  have hsq_pos_nat : 0 < A.card ^ 2 :=
    Nat.pow_pos hcard_pos_nat
  have hsq_pos : 0 < ((A.card ^ 2 : Nat) : Real) := by
    exact_mod_cast hsq_pos_nat
  have hP_lt_sq_nat : (Pdir 2 A).card < A.card ^ 2 := by
    omega
  have hP_lt_sq :
      ((Pdir 2 A).card : Real) < ((A.card ^ 2 : Nat) : Real) := by
    exact_mod_cast hP_lt_sq_nat
  have hpi_strict :
      Real.pi / ((A.card ^ 2 : Nat) : Real) <
        Real.pi / ((Pdir 2 A).card : Real) := by
    rw [div_lt_div_iff₀ hsq_pos hP_pos]
    nlinarith [Real.pi_pos, hP_lt_sq]
  have hrho_eq :
      rhoSph 2 (Pdir 2 A).card =
        Real.pi / ((Pdir 2 A).card : Real) :=
    lemma1_exact_spherical_optimum_on_circle
      (Pdir 2 A).card (Nat.succ_le_of_lt hP_pos_nat)
  calc
    Real.pi / ((A.card ^ 2 : Nat) : Real)
        < Real.pi / ((Pdir 2 A).card : Real) := hpi_strict
    _ = rhoSph 2 (Pdir 2 A).card := hrho_eq.symm
    _ <= F 2 A := appendix_lemma3_pointwise_comparison 2 A

/-- Appendix Lemma 5, theorem-backed full collision statement. -/
theorem appendix_lemma5_collisions_in_dimension2 :
    appendix_lemma5_collisions_in_dimension2_statement := by
  intro A hcard hcollision
  have hdir := appendix_lemma5_direction_count_bound A hcard hcollision
  exact
    ⟨hdir,
      dimension2_strict_lower_bound_of_direction_count
        (A := A) hcard hdir⟩

private def vec2 (x y : Real) : EuclideanSpace Real (Fin 2) :=
  OptimalAlphabets.AsymmetricProduct.tupleVector fun i =>
    if (i : Nat) = 0 then x else y

@[simp] private theorem vec2_zero (x y : Real) :
    vec2 x y 0 = x := by
  simp [vec2]

@[simp] private theorem vec2_one (x y : Real) :
    vec2 x y 1 = y := by
  simp [vec2]

private theorem euclidean2_eq_vec2_coords
    (z : EuclideanSpace Real (Fin 2)) :
    z = vec2 (z 0) (z 1) := by
  ext i
  fin_cases i <;> simp [vec2]

private theorem vec2_smul (r x y : Real) :
    vec2 (r * x) (r * y) = r • vec2 x y := by
  ext i
  fin_cases i <;> simp [vec2]

private theorem tupleVector_eq_vec2 {x : Fin 2 -> Real} :
    OptimalAlphabets.AsymmetricProduct.tupleVector x =
      vec2 (x 0) (x 1) := by
  ext i
  fin_cases i <;> simp [vec2]

private theorem inner_vec2 (a b c d : Real) :
    inner Real (vec2 a b) (vec2 c d) = a * c + b * d := by
  rw [vec2, vec2]
  simp [OptimalAlphabets.AsymmetricProduct.tupleVector, PiLp.inner_apply]
  ring

private theorem norm_sq_vec2 (a b : Real) :
    ‖vec2 a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  calc
    ‖vec2 a b‖ ^ 2 = inner Real (vec2 a b) (vec2 a b) := by
      exact (real_inner_self_eq_norm_sq (vec2 a b)).symm
    _ = a ^ 2 + b ^ 2 := by
      rw [inner_vec2]
      ring

private theorem norm_vec2 (a b : Real) :
    ‖vec2 a b‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  calc
    ‖vec2 a b‖ = Real.sqrt (‖vec2 a b‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ = Real.sqrt (a ^ 2 + b ^ 2) := by
      rw [norm_sq_vec2]

private theorem cos_angle_vec2 (a b c d : Real) :
    Real.cos (InnerProductGeometry.angle (vec2 a b) (vec2 c d)) =
      (a * c + b * d) /
        (Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2)) := by
  rw [InnerProductGeometry.cos_angle, inner_vec2, norm_vec2, norm_vec2]

private theorem div_sqrt_mul_sqrt_lt_sqrt_two_div_two_of_sq_lt
    {a X Y : Real} (hX : 0 < X) (hY : 0 < Y)
    (hsq : 2 * a ^ 2 < X * Y) :
    a / (Real.sqrt X * Real.sqrt Y) < Real.sqrt 2 / 2 := by
  by_cases ha : a < 0
  · have hpos : 0 < Real.sqrt 2 / 2 := by positivity
    have hden_pos : 0 < Real.sqrt X * Real.sqrt Y :=
      mul_pos (Real.sqrt_pos.2 hX) (Real.sqrt_pos.2 hY)
    have hdiv_neg : a / (Real.sqrt X * Real.sqrt Y) < 0 := by
      exact div_neg_of_neg_of_pos ha hden_pos
    exact hdiv_neg.trans hpos
  · have ha_nonneg : 0 <= a := le_of_not_gt ha
    have hden_pos : 0 < Real.sqrt X * Real.sqrt Y :=
      mul_pos (Real.sqrt_pos.2 hX) (Real.sqrt_pos.2 hY)
    rw [div_lt_iff₀ hden_pos]
    have hrhs_nonneg :
        0 <= Real.sqrt 2 / 2 * (Real.sqrt X * Real.sqrt Y) := by
      positivity
    have hden_sq : (Real.sqrt X * Real.sqrt Y) ^ 2 = X * Y := by
      rw [mul_pow, Real.sq_sqrt hX.le, Real.sq_sqrt hY.le]
    rw [← sq_lt_sq₀ ha_nonneg hrhs_nonneg]
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : Real) <= 2),
      hden_sq]
    norm_num
    nlinarith

private theorem pi_div_four_lt_angle_of_cos_lt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {x y : E}
    (hcos : Real.cos (InnerProductGeometry.angle x y) < Real.sqrt 2 / 2) :
    Real.pi / 4 < InnerProductGeometry.angle x y := by
  by_contra hnot
  have hle : InnerProductGeometry.angle x y <= Real.pi / 4 :=
    le_of_not_gt hnot
  have hcos_ge :
      Real.sqrt 2 / 2 <= Real.cos (InnerProductGeometry.angle x y) := by
    rw [← Real.cos_pi_div_four]
    exact Real.cos_le_cos_of_nonneg_of_le_pi
      (InnerProductGeometry.angle_nonneg x y)
      (by linarith [Real.pi_pos]) hle
  exact not_lt_of_ge hcos_ge hcos

private theorem angle_le_pi_div_four_of_cos_ge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {x y : E}
    (hcos : Real.sqrt 2 / 2 <=
      Real.cos (InnerProductGeometry.angle x y)) :
    InnerProductGeometry.angle x y <= Real.pi / 4 := by
  by_contra hnot
  have hgt : Real.pi / 4 < InnerProductGeometry.angle x y :=
    lt_of_not_ge hnot
  have hcos_lt :
      Real.cos (InnerProductGeometry.angle x y) < Real.sqrt 2 / 2 := by
    rw [← Real.cos_pi_div_four]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      (by positivity)
      (InnerProductGeometry.angle_le_pi x y)
      hgt
  exact not_lt_of_ge hcos hcos_lt

private theorem angle_vec2_corner_le_pi_div_four
    {a b s t : Real}
    (hsq : a ^ 2 + b ^ 2 = 1)
    (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (has : 0 <= a * s) (hbt : 0 <= b * t) :
    InnerProductGeometry.angle (vec2 a b) (vec2 s t) <=
      Real.pi / 4 := by
  apply angle_le_pi_div_four_of_cos_ge
  rw [cos_angle_vec2, hsq, hs, ht]
  have hsum_ge_one : (1 : Real) <= a * s + b * t := by
    have hsum_nonneg : 0 <= a * s + b * t := by linarith
    have hsq_le : (1 : Real) ^ 2 <= (a * s + b * t) ^ 2 := by
      have hprod_nonneg : 0 <= (a * s) * (b * t) :=
        mul_nonneg has hbt
      nlinarith
    exact le_of_sq_le_sq hsq_le hsum_nonneg
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  norm_num
  rw [le_div_iff₀ hsqrt2_pos]
  have hmul : Real.sqrt 2 / 2 * Real.sqrt 2 = 1 := by
    rw [div_mul_eq_mul_div, ← sq, Real.sq_sqrt (by norm_num)]
    norm_num
  simpa [hmul] using hsum_ge_one

private theorem pi_div_four_lt_angle_vec2_of_sq
    {a b c d : Real}
    (hX : 0 < a ^ 2 + b ^ 2) (hY : 0 < c ^ 2 + d ^ 2)
    (hsq :
      2 * (a * c + b * d) ^ 2 <
        (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) :
    Real.pi / 4 < InnerProductGeometry.angle (vec2 a b) (vec2 c d) := by
  apply pi_div_four_lt_angle_of_cos_lt
  rw [cos_angle_vec2]
  exact div_sqrt_mul_sqrt_lt_sqrt_two_div_two_of_sq_lt hX hY hsq

private theorem pi_div_four_lt_angle_vec2_of_inner_neg
    {a b c d : Real}
    (hX : 0 < a ^ 2 + b ^ 2) (hY : 0 < c ^ 2 + d ^ 2)
    (hdot : a * c + b * d < 0) :
    Real.pi / 4 < InnerProductGeometry.angle (vec2 a b) (vec2 c d) := by
  apply pi_div_four_lt_angle_of_cos_lt
  rw [cos_angle_vec2]
  have hden_pos :
      0 < Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) :=
    mul_pos (Real.sqrt_pos.2 hX) (Real.sqrt_pos.2 hY)
  have hdiv_neg :
      (a * c + b * d) /
          (Real.sqrt (a ^ 2 + b ^ 2) *
            Real.sqrt (c ^ 2 + d ^ 2)) < 0 :=
    div_neg_of_neg_of_pos hdot hden_pos
  have hpos : 0 < Real.sqrt 2 / 2 := by positivity
  exact hdiv_neg.trans hpos

private theorem binary_left_witness_angle_gt
    {u v : Real} (hu : 0 < u) (hv : 0 < v) (huv : u < v) :
    let t : Real := (v - u) / (2 * (v + u))
    forall x : Fin 2 -> Real,
      (∀ i, x i ∈ ({-u, v} : Finset Real)) ->
      OptimalAlphabets.AsymmetricProduct.tupleVector x ≠ 0 ->
      Real.pi / 4 <
        InnerProductGeometry.angle
          (vec2 (-1) t)
          (OptimalAlphabets.AsymmetricProduct.tupleVector x) := by
  intro t x hxmem _hxne
  have ht_pos : 0 < t := by
    dsimp [t]
    exact div_pos (sub_pos.2 huv) (by nlinarith [hu, hv])
  have hx0 := hxmem 0
  have hx1 := hxmem 1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx0 hx1
  rw [tupleVector_eq_vec2]
  rcases hx0 with hx0 | hx0 <;> rcases hx1 with hx1 | hx1
  · rw [hx0, hx1]
    apply pi_div_four_lt_angle_vec2_of_sq
    · positivity
    · nlinarith [sq_pos_of_pos hu]
    · have hden : (2 * (v + u)) ≠ 0 := by nlinarith [hu, hv]
      dsimp [t]
      field_simp [hden]
      ring_nf
      nlinarith [hu, hv, huv]
  · rw [hx0, hx1]
    apply pi_div_four_lt_angle_vec2_of_sq
    · positivity
    · nlinarith [sq_pos_of_pos hu, sq_pos_of_pos hv]
    · dsimp [t]
      have hden : (2 * (v + u)) ≠ 0 := by nlinarith [hu, hv]
      field_simp [hden]
      ring_nf
      have hfactor :
          0 < (v - u) *
            (3 * v ^ 3 + 5 * u * v ^ 2 + 5 * u ^ 2 * v + 3 * u ^ 3) := by
        have hpoly :
            0 < 3 * v ^ 3 + 5 * u * v ^ 2 + 5 * u ^ 2 * v + 3 * u ^ 3 := by
          positivity
        exact mul_pos (sub_pos.2 huv) hpoly
      nlinarith
  · rw [hx0, hx1]
    apply pi_div_four_lt_angle_vec2_of_inner_neg
    · positivity
    · nlinarith [sq_pos_of_pos hu, sq_pos_of_pos hv]
    · nlinarith [hu, hv, ht_pos]
  · rw [hx0, hx1]
    apply pi_div_four_lt_angle_vec2_of_sq
    · positivity
    · nlinarith [sq_pos_of_pos hv]
    · dsimp [t]
      have hden : (2 * (v + u)) ≠ 0 := by nlinarith [hu, hv]
      field_simp [hden]
      ring_nf
      nlinarith [hu, hv, huv]

private theorem binary_right_witness_angle_gt
    {u v : Real} (hu : 0 < u) (hv : 0 < v) (hvu : v < u) :
    let t : Real := (u - v) / (2 * (u + v))
    forall x : Fin 2 -> Real,
      (∀ i, x i ∈ ({-u, v} : Finset Real)) ->
      OptimalAlphabets.AsymmetricProduct.tupleVector x ≠ 0 ->
      Real.pi / 4 <
        InnerProductGeometry.angle
          (vec2 (-t) 1)
          (OptimalAlphabets.AsymmetricProduct.tupleVector x) := by
  intro t x hxmem _hxne
  have ht_pos : 0 < t := by
    dsimp [t]
    exact div_pos (sub_pos.2 hvu) (by nlinarith [hu, hv])
  have ht_lt_one : t < 1 := by
    dsimp [t]
    rw [div_lt_one₀ (by nlinarith [hu, hv])]
    nlinarith [hu, hv]
  have hx0 := hxmem 0
  have hx1 := hxmem 1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx0 hx1
  rw [tupleVector_eq_vec2]
  rcases hx0 with hx0 | hx0 <;> rcases hx1 with hx1 | hx1
  · rw [hx0, hx1]
    apply pi_div_four_lt_angle_vec2_of_inner_neg
    · positivity
    · nlinarith [sq_pos_of_pos hu]
    · nlinarith [hu, ht_lt_one]
  · rw [hx0, hx1]
    apply pi_div_four_lt_angle_vec2_of_sq
    · positivity
    · nlinarith [sq_pos_of_pos hu, sq_pos_of_pos hv]
    · dsimp [t]
      have hden : (2 * (u + v)) ≠ 0 := by nlinarith [hu, hv]
      field_simp [hden]
      ring_nf
      have hfactor :
          0 < (u - v) *
            (3 * u ^ 3 + 5 * u ^ 2 * v + 5 * u * v ^ 2 + 3 * v ^ 3) := by
        have hpoly :
            0 < 3 * u ^ 3 + 5 * u ^ 2 * v + 5 * u * v ^ 2 + 3 * v ^ 3 := by
          positivity
        exact mul_pos (sub_pos.2 hvu) hpoly
      nlinarith
  · rw [hx0, hx1]
    apply pi_div_four_lt_angle_vec2_of_inner_neg
    · positivity
    · nlinarith [sq_pos_of_pos hu, sq_pos_of_pos hv]
    · nlinarith [hu, hv, ht_pos]
  · rw [hx0, hx1]
    apply pi_div_four_lt_angle_vec2_of_sq
    · positivity
    · nlinarith [sq_pos_of_pos hv]
    · dsimp [t]
      have hden : (2 * (u + v)) ≠ 0 := by nlinarith [hu, hv]
      field_simp [hden]
      ring_nf
      nlinarith [hu, hv, hvu]

private theorem P_nonempty_of_Pdir_nonempty
    {n : Nat} {A : Finset Real} (h : (Pdir n A).Nonempty) :
    (P n A).Nonempty := by
  classical
  rcases h with ⟨v, hv⟩
  refine
    ⟨⟨v, OptimalAlphabets.AsymmetricProduct.mem_sphere_of_mem_asymProdDirections hv⟩,
      ?_⟩
  unfold P OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode
  rw [Finset.mem_map]
  refine ⟨⟨v, hv⟩, Finset.mem_attach _ _, rfl⟩

private theorem binary_left_strict_F
    {u v : Real} (hu : 0 < u) (hv : 0 < v) (huv : u < v) :
    Real.pi / 4 < F 2 ({-u, v} : Finset Real) := by
  classical
  let t : Real := (v - u) / (2 * (v + u))
  let y : EuclideanSpace Real (Fin 2) := vec2 (-1) t
  have hy_ne : y ≠ 0 := by
    intro h
    have h0 := congrArg (fun z : EuclideanSpace Real (Fin 2) => z 0) h
    simp [y] at h0
  let w : OptimalAlphabets.SpherePoint 2 :=
    ⟨NormedSpace.normalize y, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact NormedSpace.norm_normalize (x := y) hy_ne⟩
  let A : Finset Real := ({-u, v} : Finset Real)
  let C : Finset (OptimalAlphabets.SpherePoint 2) := P 2 A
  have hAcard : 1 < A.card := by
    have hne : -u ≠ v := by linarith
    simp [A, hne]
  have hC_nonempty : C.Nonempty :=
    P_nonempty_of_Pdir_nonempty (Pdir_two_nonempty_of_one_lt_card hAcard)
  have hpoint (c : OptimalAlphabets.SpherePoint 2) (hc : c ∈ C) :
      Real.pi / 4 < InnerProductGeometry.angle w.1 c.1 := by
    rcases
        OptimalAlphabets.AsymmetricProduct.exists_tuple_of_mem_asymProdSphericalCode
          (n := 2) (A := A) (by simpa [C] using hc) with
      ⟨x, hx, hcval⟩
    have hxmem : ∀ i, x i ∈ A :=
      (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1 hx).1
    have hxne : OptimalAlphabets.AsymmetricProduct.tupleVector x ≠ 0 :=
      (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1 hx).2
    rw [← hcval]
    change
      Real.pi / 4 <
        InnerProductGeometry.angle
          (NormedSpace.normalize y)
          (NormedSpace.normalize
            (OptimalAlphabets.AsymmetricProduct.tupleVector x))
    simpa [A, y, t] using
      (binary_left_witness_angle_gt hu hv huv x hxmem hxne)
  have hmin :
      Real.pi / 4 < OptimalAlphabets.minAngleToSphericalCode C w := by
    unfold OptimalAlphabets.minAngleToSphericalCode
    rw [dif_pos hC_nonempty]
    exact
      (Finset.lt_inf'_iff
        (s := C) (H := hC_nonempty)
        (f := fun c => InnerProductGeometry.angle w.1 c.1)).2 hpoint
  unfold F OptimalAlphabets.AsymmetricProduct.F_asym
    OptimalAlphabets.covrad_sph
  exact lt_of_lt_of_le hmin
    (le_csSup (OptimalAlphabets.bddAbove_range_minAngleToSphericalCode C)
      (Set.mem_range_self w))

private theorem binary_right_strict_F
    {u v : Real} (hu : 0 < u) (hv : 0 < v) (hvu : v < u) :
    Real.pi / 4 < F 2 ({-u, v} : Finset Real) := by
  classical
  let t : Real := (u - v) / (2 * (u + v))
  let y : EuclideanSpace Real (Fin 2) := vec2 (-t) 1
  have hy_ne : y ≠ 0 := by
    intro h
    have h1 := congrArg (fun z : EuclideanSpace Real (Fin 2) => z 1) h
    simp [y] at h1
  let w : OptimalAlphabets.SpherePoint 2 :=
    ⟨NormedSpace.normalize y, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact NormedSpace.norm_normalize (x := y) hy_ne⟩
  let A : Finset Real := ({-u, v} : Finset Real)
  let C : Finset (OptimalAlphabets.SpherePoint 2) := P 2 A
  have hAcard : 1 < A.card := by
    have hne : -u ≠ v := by linarith
    simp [A, hne]
  have hC_nonempty : C.Nonempty :=
    P_nonempty_of_Pdir_nonempty (Pdir_two_nonempty_of_one_lt_card hAcard)
  have hpoint (c : OptimalAlphabets.SpherePoint 2) (hc : c ∈ C) :
      Real.pi / 4 < InnerProductGeometry.angle w.1 c.1 := by
    rcases
        OptimalAlphabets.AsymmetricProduct.exists_tuple_of_mem_asymProdSphericalCode
          (n := 2) (A := A) (by simpa [C] using hc) with
      ⟨x, hx, hcval⟩
    have hxmem : ∀ i, x i ∈ A :=
      (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1 hx).1
    have hxne : OptimalAlphabets.AsymmetricProduct.tupleVector x ≠ 0 :=
      (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1 hx).2
    rw [← hcval]
    change
      Real.pi / 4 <
        InnerProductGeometry.angle
          (NormedSpace.normalize y)
          (NormedSpace.normalize
            (OptimalAlphabets.AsymmetricProduct.tupleVector x))
    simpa [A, y, t] using
      (binary_right_witness_angle_gt hu hv hvu x hxmem hxne)
  have hmin :
      Real.pi / 4 < OptimalAlphabets.minAngleToSphericalCode C w := by
    unfold OptimalAlphabets.minAngleToSphericalCode
    rw [dif_pos hC_nonempty]
    exact
      (Finset.lt_inf'_iff
        (s := C) (H := hC_nonempty)
        (f := fun c => InnerProductGeometry.angle w.1 c.1)).2 hpoint
  unfold F OptimalAlphabets.AsymmetricProduct.F_asym
    OptimalAlphabets.covrad_sph
  exact lt_of_lt_of_le hmin
    (le_csSup (OptimalAlphabets.bddAbove_range_minAngleToSphericalCode C)
      (Set.mem_range_self w))

/-- Unequal binary alphabets are strictly worse than the antipodal binary
case in dimension two. -/
theorem binary_unequal_strict_F
    {u v : Real} (hu : 0 < u) (hv : 0 < v) (hne : u ≠ v) :
    Real.pi / 4 < F 2 ({-u, v} : Finset Real) := by
  rcases lt_or_gt_of_ne hne with huv | hvu
  · exact binary_left_strict_F hu hv huv
  · exact binary_right_strict_F hu hv hvu

private theorem pi_div_four_le_antipodal_binary_F
    {u : Real} (hu : 0 < u) :
    Real.pi / 4 <= F 2 ({-u, u} : Finset Real) := by
  classical
  let A : Finset Real := ({-u, u} : Finset Real)
  have hAcard : A.card = 2 := by
    have hne : -u ≠ u := by linarith
    simp [A, hne]
  have hP_nonempty : (Pdir 2 A).Nonempty :=
    Pdir_two_nonempty_of_one_lt_card (by simp [hAcard])
  have hP_pos_nat : 0 < (Pdir 2 A).card :=
    Finset.card_pos.2 hP_nonempty
  have hP_card_le_four : (Pdir 2 A).card <= 4 := by
    have hle : (Pdir 2 A).card <= A.card ^ 2 := by
      calc
        (Pdir 2 A).card <= (nonzeroProductTuples 2 A).card :=
          Pdir_card_le_nonzeroProductTuples_card 2 A
        _ <= (productTuples 2 A).card :=
          Finset.card_le_card (nonzeroProductTuples_subset_productTuples 2 A)
        _ = A.card ^ 2 := productTuples_card_two A
    simpa [hAcard] using hle
  have hrho_four :
      rhoSph 2 4 = Real.pi / 4 := by
    simpa using
      (lemma1_exact_spherical_optimum_on_circle 4 (by norm_num : 1 <= 4))
  calc
    Real.pi / 4 = rhoSph 2 4 := hrho_four.symm
    _ <= rhoSph 2 (Pdir 2 A).card := by
      exact appendix_lemma4_antitonicity_in_code_size
        (n := 2) (m1 := (Pdir 2 A).card) (m2 := 4)
        (by norm_num) (Nat.succ_le_of_lt hP_pos_nat) hP_card_le_four
    _ <= F 2 A := appendix_lemma3_pointwise_comparison 2 A

private theorem antipodal_binary_F_le_pi_div_four
    {u : Real} (hu : 0 < u) :
    F 2 ({-u, u} : Finset Real) <= Real.pi / 4 := by
  classical
  let A : Finset Real := ({-u, u} : Finset Real)
  let C : Finset (OptimalAlphabets.SpherePoint 2) := P 2 A
  have hupper (w : OptimalAlphabets.SpherePoint 2) :
      OptimalAlphabets.minAngleToSphericalCode C w <= Real.pi / 4 := by
    let x : Fin 2 -> Real := fun i =>
      if 0 <= w.1 i then u else -u
    have hxmem : ∀ i, x i ∈ A := by
      intro i
      by_cases hi : 0 <= w.1 i
      · simp [x, A, hi]
      · simp [x, A, hi]
    have hxne :
        OptimalAlphabets.AsymmetricProduct.tupleVector x ≠ 0 := by
      rw [OptimalAlphabets.AsymmetricProduct.tupleVector_ne_zero_iff]
      refine ⟨0, ?_⟩
      by_cases h0 : 0 <= w.1 0
      · simp [x, h0, ne_of_gt hu]
      · have hneg_ne : -u ≠ 0 := by linarith
        simp [x, h0, hneg_ne]
    have hx : x ∈ nonzeroProductTuples 2 A :=
      OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.2
        ⟨hxmem, hxne⟩
    let y : EuclideanSpace Real (Fin 2) :=
      OptimalAlphabets.AsymmetricProduct.tupleVector x
    have hydir : NormedSpace.normalize y ∈ Pdir 2 A := by
      rw [Pdir, OptimalAlphabets.AsymmetricProduct.mem_asymProdDirections]
      exact ⟨x, hx, rfl⟩
    let c : OptimalAlphabets.SpherePoint 2 :=
      ⟨NormedSpace.normalize y,
        OptimalAlphabets.AsymmetricProduct.mem_sphere_of_mem_asymProdDirections
          hydir⟩
    have hc : c ∈ C := by
      unfold C P OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode
      rw [Finset.mem_map]
      refine ⟨⟨NormedSpace.normalize y, hydir⟩, Finset.mem_attach _ _, rfl⟩
    let a : Real := w.1 0
    let b : Real := w.1 1
    have hw_eq : w.1 = vec2 a b := by
      simpa [a, b] using euclidean2_eq_vec2_coords w.1
    have hsq : a ^ 2 + b ^ 2 = 1 := by
      have hw_norm : ‖w.1‖ = 1 :=
        OptimalAlphabets.AsymmetricProduct.norm_spherePoint w
      have hnorm_sq : ‖w.1‖ ^ 2 = 1 := by
        rw [hw_norm]
        norm_num
      rw [hw_eq, norm_sq_vec2] at hnorm_sq
      exact hnorm_sq
    have hraw :
        InnerProductGeometry.angle w.1 y <= Real.pi / 4 := by
      by_cases ha : 0 <= a <;> by_cases hb : 0 <= b
      · rw [hw_eq]
        change
          InnerProductGeometry.angle (vec2 a b)
            (OptimalAlphabets.AsymmetricProduct.tupleVector x) <=
              Real.pi / 4
        rw [tupleVector_eq_vec2]
        simp [x, a, b, ha, hb]
        rw [show vec2 u u = u • vec2 1 1 by
          simpa using (vec2_smul u 1 1)]
        rw [InnerProductGeometry.angle_smul_right_of_pos _ _ hu]
        exact angle_vec2_corner_le_pi_div_four hsq
          (by norm_num) (by norm_num)
          (by simpa [a] using ha) (by simpa [b] using hb)
      · have hb' : b <= 0 := le_of_not_ge hb
        rw [hw_eq]
        change
          InnerProductGeometry.angle (vec2 a b)
            (OptimalAlphabets.AsymmetricProduct.tupleVector x) <=
              Real.pi / 4
        rw [tupleVector_eq_vec2]
        simp [x, a, b, ha, hb]
        rw [show vec2 u (-u) = u • vec2 1 (-1) by
          simpa using (vec2_smul u 1 (-1))]
        rw [InnerProductGeometry.angle_smul_right_of_pos _ _ hu]
        exact angle_vec2_corner_le_pi_div_four hsq
          (by norm_num) (by norm_num)
          (by simpa [a] using ha) (by nlinarith [hb'])
      · have ha' : a <= 0 := le_of_not_ge ha
        rw [hw_eq]
        change
          InnerProductGeometry.angle (vec2 a b)
            (OptimalAlphabets.AsymmetricProduct.tupleVector x) <=
              Real.pi / 4
        rw [tupleVector_eq_vec2]
        simp [x, a, b, ha, hb]
        rw [show vec2 (-u) u = u • vec2 (-1) 1 by
          simpa using (vec2_smul u (-1) 1)]
        rw [InnerProductGeometry.angle_smul_right_of_pos _ _ hu]
        exact angle_vec2_corner_le_pi_div_four hsq
          (by norm_num) (by norm_num)
          (by nlinarith [ha']) (by simpa [b] using hb)
      · have ha' : a <= 0 := le_of_not_ge ha
        have hb' : b <= 0 := le_of_not_ge hb
        rw [hw_eq]
        change
          InnerProductGeometry.angle (vec2 a b)
            (OptimalAlphabets.AsymmetricProduct.tupleVector x) <=
              Real.pi / 4
        rw [tupleVector_eq_vec2]
        simp [x, a, b, ha, hb]
        rw [show vec2 (-u) (-u) = u • vec2 (-1) (-1) by
          simpa using (vec2_smul u (-1) (-1))]
        rw [InnerProductGeometry.angle_smul_right_of_pos _ _ hu]
        exact angle_vec2_corner_le_pi_div_four hsq
          (by norm_num) (by norm_num) (by nlinarith) (by nlinarith)
    have hangle :
        InnerProductGeometry.angle w.1 c.1 <= Real.pi / 4 := by
      simpa [c, y] using hraw
    unfold OptimalAlphabets.minAngleToSphericalCode
    rw [dif_pos ⟨c, hc⟩]
    exact
      (Finset.inf'_le
        (s := C) (f := fun c => InnerProductGeometry.angle w.1 c.1)
        hc).trans hangle
  unfold F OptimalAlphabets.AsymmetricProduct.F_asym
    OptimalAlphabets.covrad_sph
  change
    sSup (Set.range (OptimalAlphabets.minAngleToSphericalCode C)) <=
      Real.pi / 4
  refine csSup_le ?_ ?_
  · exact ⟨_, Set.mem_range_self (angleToSphere2 0)⟩
  · rintro r ⟨w, rfl⟩
    exact hupper w

/-- Antipodal binary alphabets have product covering radius exactly `pi / 4`
in dimension two. -/
theorem antipodal_binary_F_eq_pi_div_four
    {u : Real} (hu : 0 < u) :
    F 2 ({-u, u} : Finset Real) = Real.pi / 4 :=
  le_antisymm
    (antipodal_binary_F_le_pi_div_four hu)
    (pi_div_four_le_antipodal_binary_F hu)

/-- Appendix Lemma 7: binary no-collision case. -/
def appendix_lemma7_binary_no_collision_case_statement : Prop :=
  forall u v : Real, 0 < u -> 0 < v ->
    let A : Finset Real := ({-u, v} : Finset Real)
    (F 2 A = Real.pi / 4 ↔ u = v) ∧
      (u ≠ v -> Real.pi / 4 < F 2 A)

/-- Appendix Lemma 7, theorem-backed binary no-collision case. -/
theorem appendix_lemma7_binary_no_collision_case :
    appendix_lemma7_binary_no_collision_case_statement := by
  intro u v hu hv
  dsimp
  constructor
  · constructor
    · intro hF
      by_contra hne
      have hstrict := binary_unequal_strict_F hu hv hne
      change
        Real.pi / 4 <
          OptimalAlphabets.covrad_sph
            (OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode 2
              ({-u, v} : Finset Real))
        at hstrict
      rw [hF] at hstrict
      linarith
    · intro huv
      subst v
      exact antipodal_binary_F_eq_pi_div_four hu
  · intro hne
    exact binary_unequal_strict_F hu hv hne

/-- Theorem 1, theorem-backed complete dimension-2 classification. -/
theorem theorem1_complete_dimension2_classification :
    theorem1_complete_dimension2_classification_statement := by
  intro A hcard
  by_cases hanti : IsAntipodalBinary A
  · left
    refine ⟨hanti, ?_⟩
    rcases hanti with ⟨a, ha_pos, hmem⟩
    have hAeq : A = ({-a, a} : Finset Real) := by
      ext x
      simpa [Finset.mem_insert, Finset.mem_singleton] using hmem x
    have hcard_two : A.card = 2 :=
      IsAntipodalBinary.card_eq_two ⟨a, ha_pos, hmem⟩
    have hF : F 2 A = Real.pi / 4 := by
      rw [hAeq]
      exact antipodal_binary_F_eq_pi_div_four ha_pos
    have hrho :
        rhoSph 2 (A.card ^ 2) = Real.pi / 4 := by
      have hrho_four :
          rhoSph 2 4 = Real.pi / 4 := by
        simpa using
          (lemma1_exact_spherical_optimum_on_circle 4
            (by norm_num : 1 <= 4))
      simpa [hcard_two] using hrho_four
    rw [hF, hrho]
  · right
    refine ⟨hanti, ?_⟩
    let collision : Prop :=
      (0 : Real) ∈ A ∨
        (∃ a : Real, ∃ b : Real,
          a ∈ A ∧ b ∈ A ∧ 0 < a ∧ 0 < b ∧ a ≠ b) ∨
        (∃ a : Real, ∃ b : Real,
          a ∈ A ∧ b ∈ A ∧ a < 0 ∧ b < 0 ∧ a ≠ b)
    by_cases hcollision : collision
    · have hfull :=
        appendix_lemma5_collisions_in_dimension2
          A hcard hcollision
      have hstrict :
          Real.pi / ((A.card ^ 2 : Nat) : Real) < F 2 A :=
        hfull.2
      have hsq_one : 1 <= A.card ^ 2 := by
        have hcard_pos : 0 < A.card := by omega
        exact Nat.succ_le_of_lt (Nat.pow_pos hcard_pos)
      have hrho :
          rhoSph 2 (A.card ^ 2) =
            Real.pi / ((A.card ^ 2 : Nat) : Real) :=
        lemma1_exact_spherical_optimum_on_circle
          (A.card ^ 2) hsq_one
      rw [hrho]
      exact hstrict
    · have hzero : ¬ (0 : Real) ∈ A := by
        intro hz
        exact hcollision (Or.inl hz)
      have hposPair :
          ¬ (∃ a : Real, ∃ b : Real,
            a ∈ A ∧ b ∈ A ∧ 0 < a ∧ 0 < b ∧ a ≠ b) := by
        intro hp
        exact hcollision (Or.inr (Or.inl hp))
      have hnegPair :
          ¬ (∃ a : Real, ∃ b : Real,
            a ∈ A ∧ b ∈ A ∧ a < 0 ∧ b < 0 ∧ a ≠ b) := by
        intro hn
        exact hcollision (Or.inr (Or.inr hn))
      rcases
          appendix_lemma6_no_collision_case A hcard hzero hposPair hnegPair with
        ⟨u, v, hu_pos, hv_pos, hmem⟩
      have hAeq : A = ({-u, v} : Finset Real) := by
        ext x
        simpa [Finset.mem_insert, Finset.mem_singleton] using hmem x
      have hcard_two : A.card = 2 := by
        have hne : -u ≠ v := by linarith
        rw [hAeq]
        simp [hne]
      have huv_ne : u ≠ v := by
        intro huv
        apply hanti
        refine ⟨u, hu_pos, ?_⟩
        intro x
        simpa [huv] using hmem x
      have hstrict_binary :
          Real.pi / 4 < F 2 ({-u, v} : Finset Real) :=
        binary_unequal_strict_F hu_pos hv_pos huv_ne
      have hstrict_A : Real.pi / 4 < F 2 A := by
        simpa [hAeq] using hstrict_binary
      have hrho :
          rhoSph 2 (A.card ^ 2) = Real.pi / 4 := by
        have hrho_four :
            rhoSph 2 4 = Real.pi / 4 := by
          simpa using
            (lemma1_exact_spherical_optimum_on_circle 4
              (by norm_num : 1 <= 4))
        simpa [hcard_two] using hrho_four
      rw [hrho]
      exact hstrict_A

/-- Corollary 5: uniform dimension-2 strict separation for `q >= 3`. -/
def corollary5_uniform_dimension2_strict_separation_statement : Prop :=
  forall q : Nat, 3 <= q -> forall A : Finset Real, A ∈ Aq q ->
    rhoSph 2 (q ^ 2) < F 2 A

/-- Corollary 5, theorem-backed strict separation for every `q >= 3`. -/
theorem corollary5_uniform_dimension2_strict_separation :
    corollary5_uniform_dimension2_strict_separation_statement := by
  intro q hq A hA
  have hcard : A.card = q := by
    simpa [Aq] using hA
  have hdir_q := corollary5_direction_count_bound (q := q) hq hA
  have hdir_A : (Pdir 2 A).card <= A.card ^ 2 - 1 := by
    simpa [hcard] using hdir_q
  have hstrict :
      Real.pi / ((A.card ^ 2 : Nat) : Real) < F 2 A :=
    dimension2_strict_lower_bound_of_direction_count
      (A := A) (by omega) hdir_A
  have hq_pos : 0 < q := by omega
  have hq_sq_one : 1 <= q ^ 2 :=
    Nat.succ_le_of_lt (Nat.pow_pos hq_pos)
  have hrho :
      rhoSph 2 (q ^ 2) = Real.pi / ((q ^ 2 : Nat) : Real) :=
    lemma1_exact_spherical_optimum_on_circle (q ^ 2) hq_sq_one
  rw [hrho]
  simpa [hcard] using hstrict

end PaperProofs
