import PaperProofs.Definitions

/-!
# Nearest-neighbor scaling theorem

This file defines the paper-facing quantizer interface for Theorem 6 and records
the exact statement as inventory.  It also proves the finite separable
optimization step used in the paper proof.
-/

noncomputable section

open Set Filter Topology Real Metric
open scoped BigOperators

namespace PaperProofs

/-- An elementwise nearest-neighbor quantizer onto a finite scalar alphabet.

The function is allowed to choose any nearest neighbor when there are ties.
-/
def IsElementwiseNearestNeighborQuantizer
    {n : Nat} (A : Finset Real) (Q : (Fin n -> Real) -> (Fin n -> Real)) : Prop :=
  forall y : Fin n -> Real, forall i : Fin n,
    Q y i ∈ A ∧ forall a : Real, a ∈ A -> |y i - Q y i| <= |y i - a|

/-- The scaled query vector used in Theorem 6. -/
def scaledQuery {n : Nat} (s : Real) (u : OptimalAlphabets.SpherePoint n) :
    Fin n -> Real :=
  fun i => s * u.1 i

/-- Angle from a sphere point to a nonzero raw vector. -/
def angleToRaw {n : Nat} (u : OptimalAlphabets.SpherePoint n)
    (x : Fin n -> Real) : Real :=
  InnerProductGeometry.angle u.1
    (OptimalAlphabets.AsymmetricProduct.tupleVector x)

/-- The bundled sphere point represented by a nonzero raw product tuple. -/
def rawTupleSpherePoint {n : Nat} {A : Finset Real}
    (x : Fin n -> Real) (hx : x ∈ nonzeroProductTuples n A) :
    OptimalAlphabets.SpherePoint n :=
  ⟨NormedSpace.normalize (OptimalAlphabets.AsymmetricProduct.tupleVector x), by
    have hxne : OptimalAlphabets.AsymmetricProduct.tupleVector x ≠ 0 :=
      (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1
        (by simpa [nonzeroProductTuples] using hx)).2
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact NormedSpace.norm_normalize (x :=
      OptimalAlphabets.AsymmetricProduct.tupleVector x) hxne⟩

/-- The sphere point represented by a raw nonzero tuple is a member of the
paper product code. -/
theorem rawTupleSpherePoint_mem_P {n : Nat} {A : Finset Real}
    {x : Fin n -> Real} (hx : x ∈ nonzeroProductTuples n A) :
    rawTupleSpherePoint x hx ∈ P n A := by
  classical
  unfold rawTupleSpherePoint P
  unfold OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode
  rw [Finset.mem_map]
  have hdir :
      NormedSpace.normalize (OptimalAlphabets.AsymmetricProduct.tupleVector x) ∈
        OptimalAlphabets.AsymmetricProduct.asymProdDirections n A := by
    rw [OptimalAlphabets.AsymmetricProduct.mem_asymProdDirections]
    exact ⟨x, by simpa [nonzeroProductTuples] using hx, rfl⟩
  refine ⟨⟨_, hdir⟩, Finset.mem_attach _ _, ?_⟩
  exact Subtype.ext rfl

/-- Normalizing a nonzero raw tuple does not change its angle to a sphere
witness. -/
theorem angle_rawTupleSpherePoint_eq_angleToRaw
    {n : Nat} {A : Finset Real} (u : OptimalAlphabets.SpherePoint n)
    {x : Fin n -> Real} (hx : x ∈ nonzeroProductTuples n A) :
    InnerProductGeometry.angle u.1 (rawTupleSpherePoint x hx).1 =
      angleToRaw u x := by
  have hxne : OptimalAlphabets.AsymmetricProduct.tupleVector x ≠ 0 :=
    (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1
      (by simpa [nonzeroProductTuples] using hx)).2
  calc
    InnerProductGeometry.angle u.1 (rawTupleSpherePoint x hx).1 =
        InnerProductGeometry.angle u.1
          (NormedSpace.normalize
            (OptimalAlphabets.AsymmetricProduct.tupleVector x)) := rfl
    _ = InnerProductGeometry.angle u.1
          (‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ •
            NormedSpace.normalize
              (OptimalAlphabets.AsymmetricProduct.tupleVector x)) := by
          rw [InnerProductGeometry.angle_smul_right_of_pos
            _ _ (norm_pos_iff.mpr hxne)]
    _ = angleToRaw u x := by
          rw [NormedSpace.norm_smul_normalize]
          rfl

/-- Raw tuple angle, written as arccosine of the tuple correlation. -/
theorem angleToRaw_eq_arccos_tupleCorr
    {n : Nat} (u : OptimalAlphabets.SpherePoint n)
    (x : Fin n -> Real) :
    angleToRaw u x =
      Real.arccos (OptimalAlphabets.AsymmetricProduct.tupleCorr u x) := by
  simp [angleToRaw, InnerProductGeometry.angle,
    OptimalAlphabets.AsymmetricProduct.tupleCorr,
    OptimalAlphabets.AsymmetricProduct.norm_spherePoint u]

/-- Maximizing tuple correlation minimizes raw tuple angle. -/
theorem angleToRaw_le_angleToRaw_of_tupleCorr_le
    {n : Nat} (u : OptimalAlphabets.SpherePoint n)
    {x y : Fin n -> Real}
    (hxy :
      OptimalAlphabets.AsymmetricProduct.tupleCorr u x <=
        OptimalAlphabets.AsymmetricProduct.tupleCorr u y) :
    angleToRaw u y <= angleToRaw u x := by
  rw [angleToRaw_eq_arccos_tupleCorr, angleToRaw_eq_arccos_tupleCorr]
  exact Real.arccos_le_arccos hxy

/-- With zero and both signs available, every sphere witness has a nonzero
product tuple with positive raw correlation. -/
theorem exists_nonzeroProductTuple_positive_tupleCorr
    {n : Nat} {A : Finset Real}
    (hzero : (0 : Real) ∈ A)
    (hpos : ∃ a : Real, a ∈ A ∧ 0 < a)
    (hneg : ∃ a : Real, a ∈ A ∧ a < 0)
    (u : OptimalAlphabets.SpherePoint n) :
    ∃ x : Fin n -> Real,
      x ∈ nonzeroProductTuples n A ∧
        0 < OptimalAlphabets.AsymmetricProduct.tupleCorr u x := by
  have hu_ne : u.1 ≠ 0 := by
    intro hzero_vec
    have hunorm : ‖u.1‖ = 1 :=
      OptimalAlphabets.AsymmetricProduct.norm_spherePoint u
    simp [hzero_vec] at hunorm
  have hcoord : ∃ i : Fin n, u.1 i ≠ 0 := by
    by_contra hnone
    apply hu_ne
    ext i
    exact not_not.mp (not_exists.mp hnone i)
  rcases hcoord with ⟨i, hui_ne⟩
  rcases lt_or_gt_of_ne hui_ne.symm with hui_pos | hui_neg
  · rcases hpos with ⟨a, ha_mem, ha_pos⟩
    let x : Fin n -> Real := fun j => if j = i then a else 0
    have hxmem : forall j : Fin n, x j ∈ A := by
      intro j
      by_cases hji : j = i
      · simp [x, hji, ha_mem]
      · simp [x, hji, hzero]
    have hxne : OptimalAlphabets.AsymmetricProduct.tupleVector x ≠ 0 := by
      rw [OptimalAlphabets.AsymmetricProduct.tupleVector_ne_zero_iff]
      refine ⟨i, ?_⟩
      simp [x, ha_pos.ne']
    have hx : x ∈ nonzeroProductTuples n A := by
      rw [nonzeroProductTuples,
        OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples]
      exact ⟨hxmem, hxne⟩
    have hinner :
        inner Real u.1 (OptimalAlphabets.AsymmetricProduct.tupleVector x) =
          u.1 i * a := by
      rw [PiLp.inner_apply]
      rw [Finset.sum_eq_single i]
      · simp [OptimalAlphabets.AsymmetricProduct.tupleVector, x, mul_comm]
      · intro j _hj hji
        simp [OptimalAlphabets.AsymmetricProduct.tupleVector, x, hji]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    have hinner_pos :
        0 < inner Real u.1 (OptimalAlphabets.AsymmetricProduct.tupleVector x) := by
      rw [hinner]
      exact mul_pos hui_pos ha_pos
    refine ⟨x, hx, ?_⟩
    unfold OptimalAlphabets.AsymmetricProduct.tupleCorr
    exact div_pos hinner_pos (norm_pos_iff.mpr hxne)
  · rcases hneg with ⟨a, ha_mem, ha_neg⟩
    let x : Fin n -> Real := fun j => if j = i then a else 0
    have hxmem : forall j : Fin n, x j ∈ A := by
      intro j
      by_cases hji : j = i
      · simp [x, hji, ha_mem]
      · simp [x, hji, hzero]
    have hxne : OptimalAlphabets.AsymmetricProduct.tupleVector x ≠ 0 := by
      rw [OptimalAlphabets.AsymmetricProduct.tupleVector_ne_zero_iff]
      refine ⟨i, ?_⟩
      simp [x, ha_neg.ne]
    have hx : x ∈ nonzeroProductTuples n A := by
      rw [nonzeroProductTuples,
        OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples]
      exact ⟨hxmem, hxne⟩
    have hinner :
        inner Real u.1 (OptimalAlphabets.AsymmetricProduct.tupleVector x) =
          u.1 i * a := by
      rw [PiLp.inner_apply]
      rw [Finset.sum_eq_single i]
      · simp [OptimalAlphabets.AsymmetricProduct.tupleVector, x, mul_comm]
      · intro j _hj hji
        simp [OptimalAlphabets.AsymmetricProduct.tupleVector, x, hji]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    have hinner_pos :
        0 < inner Real u.1 (OptimalAlphabets.AsymmetricProduct.tupleVector x) := by
      rw [hinner]
      exact mul_pos_of_neg_of_neg hui_neg ha_neg
    refine ⟨x, hx, ?_⟩
    unfold OptimalAlphabets.AsymmetricProduct.tupleCorr
    exact div_pos hinner_pos (norm_pos_iff.mpr hxne)

/-- The finite product alphabet has an angular maximizer with positive raw
correlation under the hypotheses of Theorem 6. -/
theorem exists_angularMaximizer_positive_tupleCorr
    {n : Nat} {A : Finset Real}
    (hzero : (0 : Real) ∈ A)
    (hpos : ∃ a : Real, a ∈ A ∧ 0 < a)
    (hneg : ∃ a : Real, a ∈ A ∧ a < 0)
    (u : OptimalAlphabets.SpherePoint n) :
    ∃ xstar : Fin n -> Real,
      xstar ∈ nonzeroProductTuples n A ∧
      (forall z : Fin n -> Real, z ∈ nonzeroProductTuples n A ->
        OptimalAlphabets.AsymmetricProduct.tupleCorr u z <=
          OptimalAlphabets.AsymmetricProduct.tupleCorr u xstar) ∧
      0 < OptimalAlphabets.AsymmetricProduct.tupleCorr u xstar := by
  classical
  rcases exists_nonzeroProductTuple_positive_tupleCorr
      (A := A) hzero hpos hneg u with
    ⟨x0, hx0, hx0_pos⟩
  have htuples : (nonzeroProductTuples n A).Nonempty := ⟨x0, hx0⟩
  rcases Finset.exists_mem_eq_sup' htuples
      (fun x => OptimalAlphabets.AsymmetricProduct.tupleCorr u x) with
    ⟨xstar, hxstar, hxstar_eq⟩
  refine ⟨xstar, hxstar, ?_, ?_⟩
  · intro z hz
    have hz_le :=
      Finset.le_sup' (s := nonzeroProductTuples n A)
        (f := fun x => OptimalAlphabets.AsymmetricProduct.tupleCorr u x) hz
    simpa [hxstar_eq] using hz_le
  · have hx0_le :=
      Finset.le_sup' (s := nonzeroProductTuples n A)
        (f := fun x => OptimalAlphabets.AsymmetricProduct.tupleCorr u x) hx0
    exact lt_of_lt_of_le hx0_pos (by simpa [hxstar_eq] using hx0_le)

/-- A tuple-correlation maximizer exactly realizes the finite product-code
minimum angle. -/
theorem minAngleToSphericalCode_eq_angleToRaw_of_angularMaximizer
    {n : Nat} {A : Finset Real} (u : OptimalAlphabets.SpherePoint n)
    {xstar : Fin n -> Real}
    (hxstar : xstar ∈ nonzeroProductTuples n A)
    (hopt : forall z : Fin n -> Real, z ∈ nonzeroProductTuples n A ->
      OptimalAlphabets.AsymmetricProduct.tupleCorr u z <=
        OptimalAlphabets.AsymmetricProduct.tupleCorr u xstar) :
    OptimalAlphabets.minAngleToSphericalCode (P n A) u =
      angleToRaw u xstar := by
  have hstar_mem : rawTupleSpherePoint xstar hxstar ∈ P n A :=
    rawTupleSpherePoint_mem_P hxstar
  apply le_antisymm
  · unfold OptimalAlphabets.minAngleToSphericalCode
    split_ifs with hP
    · calc
        (P n A).inf' hP
            (fun c => InnerProductGeometry.angle u.1 c.1) <=
            InnerProductGeometry.angle u.1 (rawTupleSpherePoint xstar hxstar).1 :=
              Finset.inf'_le _ hstar_mem
        _ = angleToRaw u xstar :=
              angle_rawTupleSpherePoint_eq_angleToRaw u hxstar
    · exact False.elim (hP ⟨rawTupleSpherePoint xstar hxstar, hstar_mem⟩)
  · unfold OptimalAlphabets.minAngleToSphericalCode
    split_ifs with hP
    · refine Finset.le_inf' hP _ ?_
      intro c hc
      rcases OptimalAlphabets.AsymmetricProduct.exists_tuple_of_mem_asymProdSphericalCode
          (n := n) (A := A) hc with
        ⟨y, hy, hcval⟩
      have hy' : y ∈ nonzeroProductTuples n A := by
        simpa [nonzeroProductTuples] using hy
      have hangle_c :
          InnerProductGeometry.angle u.1 c.1 = angleToRaw u y := by
        rw [← hcval]
        simpa [rawTupleSpherePoint] using
          (angle_rawTupleSpherePoint_eq_angleToRaw (A := A) u hy').symm
      calc
        angleToRaw u xstar <= angleToRaw u y :=
          angleToRaw_le_angleToRaw_of_tupleCorr_le u (hopt y hy')
        _ = InnerProductGeometry.angle u.1 c.1 := hangle_c.symm
    · exact False.elim (hP ⟨rawTupleSpherePoint xstar hxstar, hstar_mem⟩)

/-- The separable scale objective from the proof of Theorem 6. -/
def scaleObjective {n : Nat} (s : Real) (u : OptimalAlphabets.SpherePoint n)
    (x : Fin n -> Real) : Real :=
  ∑ i : Fin n, (2 * s * u.1 i * x i - (x i) ^ 2)

/-- The nonseparable quadratic objective used in the paper proof of
Theorem 6. -/
def globalScaleObjective {n : Nat} (s : Real)
    (u : OptimalAlphabets.SpherePoint n) (x : Fin n -> Real) : Real :=
  (2 * s) * inner Real u.1
    (OptimalAlphabets.AsymmetricProduct.tupleVector x) -
      ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ ^ 2

/-- The scale chosen in the proof of Theorem 6 from a reference raw tuple. -/
def optimalScaleFromRaw {n : Nat} (u : OptimalAlphabets.SpherePoint n)
    (x : Fin n -> Real) : Real :=
  ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ ^ 2 /
    inner Real u.1 (OptimalAlphabets.AsymmetricProduct.tupleVector x)

/-- The separable objective is exactly the paper's global quadratic objective
`2s<u,x> - ||x||^2`. -/
theorem scaleObjective_eq_globalScaleObjective
    {n : Nat} (s : Real) (u : OptimalAlphabets.SpherePoint n)
    (x : Fin n -> Real) :
    scaleObjective s u x = globalScaleObjective s u x := by
  unfold scaleObjective globalScaleObjective
  rw [PiLp.inner_apply, EuclideanSpace.norm_sq_eq]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib
    (s := (Finset.univ : Finset (Fin n)))
    (f := fun i : Fin n => (2 * s) *
      inner Real (u.1 i)
        ((OptimalAlphabets.AsymmetricProduct.tupleVector x) i))
    (g := fun i : Fin n =>
      ‖(OptimalAlphabets.AsymmetricProduct.tupleVector x) i‖ ^ 2)]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp [OptimalAlphabets.AsymmetricProduct.tupleVector]
  ring
/-- At the proof-selected scale, the reference tuple has quadratic value
`||x||^2`. -/
theorem globalScaleObjective_self_optimalScaleFromRaw
    {n : Nat} (u : OptimalAlphabets.SpherePoint n) {x : Fin n -> Real}
    (hinner : inner Real u.1
      (OptimalAlphabets.AsymmetricProduct.tupleVector x) ≠ 0) :
    globalScaleObjective (optimalScaleFromRaw u x) u x =
      ‖OptimalAlphabets.AsymmetricProduct.tupleVector x‖ ^ 2 := by
  unfold globalScaleObjective optimalScaleFromRaw
  field_simp [hinner]
  ring
/-- Conversely, if a tuple reaches at least the angular maximizer's quadratic
value at the proof-selected scale, then its raw correlation is at least that
of the maximizer. -/
theorem tupleCorr_le_of_norm_sq_le_globalScaleObjective_optimalScale
    {n : Nat} (u : OptimalAlphabets.SpherePoint n)
    {xstar y : Fin n -> Real}
    (hxstar_ne :
      OptimalAlphabets.AsymmetricProduct.tupleVector xstar ≠ 0)
    (hy_ne : OptimalAlphabets.AsymmetricProduct.tupleVector y ≠ 0)
    (hpos : 0 < OptimalAlphabets.AsymmetricProduct.tupleCorr u xstar)
    (hge :
      ‖OptimalAlphabets.AsymmetricProduct.tupleVector xstar‖ ^ 2 <=
        globalScaleObjective (optimalScaleFromRaw u xstar) u y) :
    OptimalAlphabets.AsymmetricProduct.tupleCorr u xstar <=
      OptimalAlphabets.AsymmetricProduct.tupleCorr u y := by
  let vx := OptimalAlphabets.AsymmetricProduct.tupleVector xstar
  let vy := OptimalAlphabets.AsymmetricProduct.tupleVector y
  have hnormx_pos : 0 < ‖vx‖ := norm_pos_iff.mpr (by simpa [vx] using hxstar_ne)
  have hnormy_pos : 0 < ‖vy‖ := norm_pos_iff.mpr (by simpa [vy] using hy_ne)
  have hinnerx_pos : 0 < inner Real u.1 vx := by
    have hmul := mul_lt_mul_of_pos_right hpos hnormx_pos
    unfold OptimalAlphabets.AsymmetricProduct.tupleCorr at hmul
    simpa [vx, div_eq_mul_inv, mul_assoc, hnormx_pos.ne'] using hmul
  have hglobal :
      globalScaleObjective (optimalScaleFromRaw u xstar) u y =
        2 * ‖vx‖ ^ 2 * inner Real u.1 vy / inner Real u.1 vx -
          ‖vy‖ ^ 2 := by
    unfold globalScaleObjective optimalScaleFromRaw
    field_simp [vx, vy, hinnerx_pos.ne']
    ring
  have hge_expand :
      ‖vx‖ ^ 2 + ‖vy‖ ^ 2 <=
        2 * ‖vx‖ ^ 2 * inner Real u.1 vy / inner Real u.1 vx := by
    have hge' :
        ‖vx‖ ^ 2 <=
          2 * ‖vx‖ ^ 2 * inner Real u.1 vy / inner Real u.1 vx -
            ‖vy‖ ^ 2 := by
      simpa [vx, vy, hglobal] using hge
    linarith
  have hge_mul :
      (‖vx‖ ^ 2 + ‖vy‖ ^ 2) * inner Real u.1 vx <=
        2 * ‖vx‖ ^ 2 * inner Real u.1 vy := by
    have hmul := mul_le_mul_of_nonneg_right hge_expand hinnerx_pos.le
    calc
      (‖vx‖ ^ 2 + ‖vy‖ ^ 2) * inner Real u.1 vx <=
          (2 * ‖vx‖ ^ 2 * inner Real u.1 vy /
              inner Real u.1 vx) * inner Real u.1 vx := hmul
      _ = 2 * ‖vx‖ ^ 2 * inner Real u.1 vy := by
          field_simp [hinnerx_pos.ne']
  have hamgm : 2 * ‖vx‖ * ‖vy‖ <= ‖vx‖ ^ 2 + ‖vy‖ ^ 2 := by
    nlinarith [sq_nonneg (‖vx‖ - ‖vy‖)]
  have hleft := mul_le_mul_of_nonneg_right hamgm hinnerx_pos.le
  have hcomb :
      2 * ‖vx‖ * ‖vy‖ * inner Real u.1 vx <=
        2 * ‖vx‖ ^ 2 * inner Real u.1 vy := by
    exact le_trans (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hleft) hge_mul
  have htarget_inner :
      inner Real u.1 vx * ‖vy‖ <= inner Real u.1 vy * ‖vx‖ := by
    have hcomb' :
        (2 * ‖vx‖) * (inner Real u.1 vx * ‖vy‖) <=
          (2 * ‖vx‖) * (inner Real u.1 vy * ‖vx‖) := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hcomb
    exact le_of_mul_le_mul_left hcomb'
      (mul_pos (by norm_num : (0 : Real) < 2) hnormx_pos)
  unfold OptimalAlphabets.AsymmetricProduct.tupleCorr
  rw [div_le_iff₀ hnormx_pos]
  have hrewrite :
      (inner Real u.1 vy / ‖vy‖) * ‖vx‖ =
        (inner Real u.1 vy * ‖vx‖) / ‖vy‖ := by
    field_simp [hnormy_pos.ne']
  rw [hrewrite, le_div_iff₀ hnormy_pos]
  simpa [vx, vy, mul_assoc, mul_left_comm, mul_comm] using htarget_inner
/-- One-coordinate algebraic equivalence used by nearest-neighbor quantization:
minimizing distance to `s u_i` maximizes `2 s u_i a - a^2`. -/
theorem nearestCoordinate_maximizes_quadratic
    {s ui q a : Real}
    (hnear : |s * ui - q| <= |s * ui - a|) :
    2 * s * ui * a - a ^ 2 <= 2 * s * ui * q - q ^ 2 := by
  have hsq : (s * ui - q) ^ 2 <= (s * ui - a) ^ 2 := by
    rw [sq_le_sq]
    exact hnear
  nlinarith

/-- The coordinatewise nearest-neighbor output maximizes the separable scale
objective over all product tuples with entries in `A`. -/
theorem nearestQuantizer_maximizes_scaleObjective
    {n : Nat} {A : Finset Real} {Q : (Fin n -> Real) -> (Fin n -> Real)}
    (hQ : IsElementwiseNearestNeighborQuantizer A Q)
    (s : Real) (u : OptimalAlphabets.SpherePoint n)
    {y : Fin n -> Real} (hy : forall i : Fin n, y i ∈ A) :
    scaleObjective s u y <= scaleObjective s u (Q (scaledQuery s u)) := by
  unfold scaleObjective
  refine Finset.sum_le_sum ?_
  intro i _hi
  have hnear := (hQ (scaledQuery s u) i).2 (y i) (hy i)
  simpa [scaledQuery, mul_assoc] using
    nearestCoordinate_maximizes_quadratic
      (s := s) (ui := u.1 i) (q := Q (scaledQuery s u) i) (a := y i) hnear
/-- If the quantizer output is nonzero, it is a nonzero product tuple over the
target alphabet. -/
theorem nearestQuantizer_mem_nonzeroProductTuples_of_ne
    {n : Nat} {A : Finset Real} {Q : (Fin n -> Real) -> (Fin n -> Real)}
    (hQ : IsElementwiseNearestNeighborQuantizer A Q)
    {s : Real} {u : OptimalAlphabets.SpherePoint n}
    (hne :
      OptimalAlphabets.AsymmetricProduct.tupleVector (Q (scaledQuery s u)) ≠ 0) :
    Q (scaledQuery s u) ∈ nonzeroProductTuples n A := by
  rw [nonzeroProductTuples,
    OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples]
  exact ⟨fun i => (hQ (scaledQuery s u) i).1, hne⟩

/-- The nearest-neighbor quantizer maximizes the paper's global quadratic
objective over all product tuples with entries in `A`. -/
theorem nearestQuantizer_maximizes_globalScaleObjective
    {n : Nat} {A : Finset Real} {Q : (Fin n -> Real) -> (Fin n -> Real)}
    (hQ : IsElementwiseNearestNeighborQuantizer A Q)
    (s : Real) (u : OptimalAlphabets.SpherePoint n)
    {y : Fin n -> Real} (hy : forall i : Fin n, y i ∈ A) :
    globalScaleObjective s u y <=
      globalScaleObjective s u (Q (scaledQuery s u)) := by
  have h := nearestQuantizer_maximizes_scaleObjective
    (A := A) (Q := Q) hQ s u hy
  rwa [scaleObjective_eq_globalScaleObjective,
    scaleObjective_eq_globalScaleObjective] at h

/-- Scale-search angle set appearing in Theorem 6. -/
def scaleSearchAngles {n : Nat} (_A : Finset Real)
    (Q : (Fin n -> Real) -> (Fin n -> Real))
    (u : OptimalAlphabets.SpherePoint n) : Set Real :=
  {theta : Real |
    ∃ s : Real,
      0 < s ∧
      OptimalAlphabets.AsymmetricProduct.tupleVector (Q (scaledQuery s u)) ≠ 0 ∧
      theta = angleToRaw u (Q (scaledQuery s u))}

/-- The angle produced by any positive nonzero quantized scale is a member of
the scale-search angle set. -/
theorem angleToRaw_mem_scaleSearchAngles
    {n : Nat} {A : Finset Real} {Q : (Fin n -> Real) -> (Fin n -> Real)}
    {s : Real} (hs : 0 < s) {u : OptimalAlphabets.SpherePoint n}
    (hne :
      OptimalAlphabets.AsymmetricProduct.tupleVector (Q (scaledQuery s u)) ≠ 0) :
    angleToRaw u (Q (scaledQuery s u)) ∈ scaleSearchAngles A Q u := by
  exact ⟨s, hs, hne, rfl⟩

/-- A nonzero raw product tuple gives an upper bound on the finite product-code
minimum angle. -/
theorem minAngleToSphericalCode_le_angleToRaw_of_mem_nonzeroProductTuples
    {n : Nat} {A : Finset Real} (u : OptimalAlphabets.SpherePoint n)
    {x : Fin n -> Real} (hx : x ∈ nonzeroProductTuples n A) :
    OptimalAlphabets.minAngleToSphericalCode (P n A) u <= angleToRaw u x := by
  have hmem : rawTupleSpherePoint x hx ∈ P n A :=
    rawTupleSpherePoint_mem_P hx
  unfold OptimalAlphabets.minAngleToSphericalCode
  split_ifs with hP
  · calc
      (P n A).inf' hP
          (fun c => InnerProductGeometry.angle u.1 c.1) <=
          InnerProductGeometry.angle u.1 (rawTupleSpherePoint x hx).1 :=
            Finset.inf'_le _ hmem
      _ = angleToRaw u x := angle_rawTupleSpherePoint_eq_angleToRaw u hx
  · exact False.elim (hP ⟨rawTupleSpherePoint x hx, hmem⟩)

/-- Under the paper's both-sign hypothesis, some positive scale quantizes to a
nonzero raw tuple. -/
theorem exists_positive_scale_nearestQuantizer_ne_zero
    {n : Nat} {A : Finset Real} {Q : (Fin n -> Real) -> (Fin n -> Real)}
    (hpos : ∃ a : Real, a ∈ A ∧ 0 < a)
    (hneg : ∃ a : Real, a ∈ A ∧ a < 0)
    (hQ : IsElementwiseNearestNeighborQuantizer A Q)
    (u : OptimalAlphabets.SpherePoint n) :
    ∃ s : Real, 0 < s ∧
      OptimalAlphabets.AsymmetricProduct.tupleVector (Q (scaledQuery s u)) ≠ 0 := by
  have hu_ne : u.1 ≠ 0 := by
    intro hzero
    have hunorm : ‖u.1‖ = 1 :=
      OptimalAlphabets.AsymmetricProduct.norm_spherePoint u
    simp [hzero] at hunorm
  have hcoord : ∃ i : Fin n, u.1 i ≠ 0 := by
    by_contra hnone
    apply hu_ne
    ext i
    exact not_not.mp (not_exists.mp hnone i)
  rcases hcoord with ⟨i, hui_ne⟩
  rcases lt_or_gt_of_ne hui_ne.symm with hui_pos | hui_neg
  · rcases hpos with ⟨a, ha_mem, ha_pos⟩
    let s : Real := 2 * a / u.1 i
    have hs : 0 < s := by
      exact div_pos (mul_pos (by norm_num : (0 : Real) < 2) ha_pos) hui_pos
    refine ⟨s, hs, ?_⟩
    rw [OptimalAlphabets.AsymmetricProduct.tupleVector_ne_zero_iff]
    refine ⟨i, ?_⟩
    intro hqi
    have hnear := (hQ (scaledQuery s u) i).2 a ha_mem
    have hsui : s * u.1 i = 2 * a := by
      unfold s
      field_simp [hui_ne]
    have hnear' : |s * u.1 i - 0| <= |s * u.1 i - a| := by
      simpa [scaledQuery, hqi] using hnear
    have habs_left : |s * u.1 i - 0| = 2 * a := by
      rw [hsui, sub_zero]
      exact abs_of_pos (mul_pos (by norm_num : (0 : Real) < 2) ha_pos)
    have habs_right : |s * u.1 i - a| = a := by
      rw [hsui]
      have hdiff : 2 * a - a = a := by ring
      rw [hdiff]
      exact abs_of_pos ha_pos
    linarith
  · rcases hneg with ⟨a, ha_mem, ha_neg⟩
    let s : Real := 2 * a / u.1 i
    have hs : 0 < s := by
      exact div_pos_of_neg_of_neg
        (mul_neg_of_pos_of_neg (by norm_num : (0 : Real) < 2) ha_neg)
        hui_neg
    refine ⟨s, hs, ?_⟩
    rw [OptimalAlphabets.AsymmetricProduct.tupleVector_ne_zero_iff]
    refine ⟨i, ?_⟩
    intro hqi
    have hnear := (hQ (scaledQuery s u) i).2 a ha_mem
    have hsui : s * u.1 i = 2 * a := by
      unfold s
      field_simp [hui_ne]
    have hnear' : |s * u.1 i - 0| <= |s * u.1 i - a| := by
      simpa [scaledQuery, hqi] using hnear
    have habs_left : |s * u.1 i - 0| = -(2 * a) := by
      rw [hsui, sub_zero]
      exact abs_of_neg (mul_neg_of_pos_of_neg (by norm_num : (0 : Real) < 2) ha_neg)
    have habs_right : |s * u.1 i - a| = -a := by
      rw [hsui]
      have hdiff : 2 * a - a = a := by ring
      rw [hdiff]
      exact abs_of_neg ha_neg
    linarith

/-- The scale-search set in Theorem 6 is nonempty under the paper's both-sign
hypothesis. -/
theorem scaleSearchAngles_nonempty
    {n : Nat} {A : Finset Real} {Q : (Fin n -> Real) -> (Fin n -> Real)}
    (hpos : ∃ a : Real, a ∈ A ∧ 0 < a)
    (hneg : ∃ a : Real, a ∈ A ∧ a < 0)
    (hQ : IsElementwiseNearestNeighborQuantizer A Q)
    (u : OptimalAlphabets.SpherePoint n) :
    (scaleSearchAngles A Q u).Nonempty := by
  rcases exists_positive_scale_nearestQuantizer_ne_zero
      (A := A) (Q := Q) hpos hneg hQ u with
    ⟨s, hs, hne⟩
  exact ⟨angleToRaw u (Q (scaledQuery s u)),
    angleToRaw_mem_scaleSearchAngles (A := A) (Q := Q) hs hne⟩

/-- One theorem-backed inequality in Theorem 6: the finite product-code
minimum angle is bounded by the infimum over positive nonzero quantized
scales. -/
theorem theorem6_minAngle_le_scaleSearch_sInf
    {n : Nat} {A : Finset Real} {Q : (Fin n -> Real) -> (Fin n -> Real)}
    (hpos : ∃ a : Real, a ∈ A ∧ 0 < a)
    (hneg : ∃ a : Real, a ∈ A ∧ a < 0)
    (hQ : IsElementwiseNearestNeighborQuantizer A Q)
    (u : OptimalAlphabets.SpherePoint n) :
    OptimalAlphabets.minAngleToSphericalCode (P n A) u <=
      sInf (scaleSearchAngles A Q u) := by
  refine le_csInf (scaleSearchAngles_nonempty (A := A) (Q := Q) hpos hneg hQ u) ?_
  rintro theta ⟨s, _hs, hne, rfl⟩
  exact minAngleToSphericalCode_le_angleToRaw_of_mem_nonzeroProductTuples
    (A := A) u
    (nearestQuantizer_mem_nonzeroProductTuples_of_ne
      (A := A) (Q := Q) hQ (s := s) (u := u) hne)

/-- Theorem 6: scaling to find a minimum codeword. -/
def theorem6_scaling_to_find_minimum_codeword_statement : Prop :=
  forall n : Nat, 2 <= n -> forall A : Finset Real,
    (0 : Real) ∈ A ->
    (∃ a : Real, a ∈ A ∧ 0 < a) ->
    (∃ a : Real, a ∈ A ∧ a < 0) ->
    forall Q : (Fin n -> Real) -> (Fin n -> Real),
      IsElementwiseNearestNeighborQuantizer A Q ->
      forall u : OptimalAlphabets.SpherePoint n,
        OptimalAlphabets.minAngleToSphericalCode (P n A) u =
          sInf (scaleSearchAngles A Q u)

/-- The reverse theorem-backed inequality in Theorem 6: evaluating the
nearest-neighbor quantizer at the proof-selected scale of an angular maximizer
produces a scale-search angle no larger than the finite product-code minimum. -/
theorem theorem6_scaleSearch_sInf_le_minAngle
    {n : Nat} {A : Finset Real} {Q : (Fin n -> Real) -> (Fin n -> Real)}
    (hzero : (0 : Real) ∈ A)
    (hpos : ∃ a : Real, a ∈ A ∧ 0 < a)
    (hneg : ∃ a : Real, a ∈ A ∧ a < 0)
    (hQ : IsElementwiseNearestNeighborQuantizer A Q)
    (u : OptimalAlphabets.SpherePoint n) :
    sInf (scaleSearchAngles A Q u) <=
      OptimalAlphabets.minAngleToSphericalCode (P n A) u := by
  classical
  rcases exists_angularMaximizer_positive_tupleCorr
      (A := A) hzero hpos hneg u with
    ⟨xstar, hxstar, hopt, hxstar_pos⟩
  let s : Real := optimalScaleFromRaw u xstar
  let q : Fin n -> Real := Q (scaledQuery s u)
  have hxstar_mem :
      forall i : Fin n, xstar i ∈ A :=
    (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1
      (by simpa [nonzeroProductTuples] using hxstar)).1
  have hxstar_ne :
      OptimalAlphabets.AsymmetricProduct.tupleVector xstar ≠ 0 :=
    (OptimalAlphabets.AsymmetricProduct.mem_nonzeroAsymProductTuples.1
      (by simpa [nonzeroProductTuples] using hxstar)).2
  have hnormx_pos :
      0 < ‖OptimalAlphabets.AsymmetricProduct.tupleVector xstar‖ :=
    norm_pos_iff.mpr hxstar_ne
  have hinnerx_pos :
      0 < inner Real u.1
        (OptimalAlphabets.AsymmetricProduct.tupleVector xstar) := by
    have hmul := mul_lt_mul_of_pos_right hxstar_pos hnormx_pos
    unfold OptimalAlphabets.AsymmetricProduct.tupleCorr at hmul
    simpa [div_eq_mul_inv, mul_assoc, hnormx_pos.ne'] using hmul
  have hs_pos : 0 < s := by
    unfold s optimalScaleFromRaw
    exact div_pos (sq_pos_of_pos hnormx_pos) hinnerx_pos
  have hq_ge :
      globalScaleObjective s u xstar <= globalScaleObjective s u q := by
    simpa [q] using
      nearestQuantizer_maximizes_globalScaleObjective
        (A := A) (Q := Q) hQ s u (y := xstar) hxstar_mem
  have hself :
      globalScaleObjective s u xstar =
        ‖OptimalAlphabets.AsymmetricProduct.tupleVector xstar‖ ^ 2 := by
    simpa [s] using
      globalScaleObjective_self_optimalScaleFromRaw
        (u := u) (x := xstar) hinnerx_pos.ne'
  have hq_ne :
      OptimalAlphabets.AsymmetricProduct.tupleVector q ≠ 0 := by
    intro hq_zero
    have hnorm_sq_pos :
        0 < ‖OptimalAlphabets.AsymmetricProduct.tupleVector xstar‖ ^ 2 :=
      sq_pos_of_pos hnormx_pos
    have hle_zero :
        ‖OptimalAlphabets.AsymmetricProduct.tupleVector xstar‖ ^ 2 <= 0 := by
      calc
        ‖OptimalAlphabets.AsymmetricProduct.tupleVector xstar‖ ^ 2 =
            globalScaleObjective s u xstar := hself.symm
        _ <= globalScaleObjective s u q := hq_ge
        _ = 0 := by
            simp [globalScaleObjective, hq_zero]
    exact (not_lt_of_ge hle_zero) hnorm_sq_pos
  have hnorm_le_gq :
      ‖OptimalAlphabets.AsymmetricProduct.tupleVector xstar‖ ^ 2 <=
        globalScaleObjective (optimalScaleFromRaw u xstar) u q := by
    calc
      ‖OptimalAlphabets.AsymmetricProduct.tupleVector xstar‖ ^ 2 =
          globalScaleObjective s u xstar := hself.symm
      _ <= globalScaleObjective s u q := hq_ge
      _ = globalScaleObjective (optimalScaleFromRaw u xstar) u q := by rfl
  have hcorr_x_le_q :
      OptimalAlphabets.AsymmetricProduct.tupleCorr u xstar <=
        OptimalAlphabets.AsymmetricProduct.tupleCorr u q :=
    tupleCorr_le_of_norm_sq_le_globalScaleObjective_optimalScale
      (u := u) (xstar := xstar) (y := q) hxstar_ne hq_ne hxstar_pos
      hnorm_le_gq
  have hangle_q_le_xstar :
      angleToRaw u q <= angleToRaw u xstar :=
    angleToRaw_le_angleToRaw_of_tupleCorr_le u hcorr_x_le_q
  have hmin_eq :
      OptimalAlphabets.minAngleToSphericalCode (P n A) u =
        angleToRaw u xstar :=
    minAngleToSphericalCode_eq_angleToRaw_of_angularMaximizer
      (A := A) u hxstar hopt
  have hbdd : BddBelow (scaleSearchAngles A Q u) := by
    refine ⟨0, ?_⟩
    rintro theta ⟨s', _hs', _hne', rfl⟩
    exact InnerProductGeometry.angle_nonneg _ _
  have hmem : angleToRaw u q ∈ scaleSearchAngles A Q u := by
    simpa [q, s] using
      angleToRaw_mem_scaleSearchAngles
        (A := A) (Q := Q) (s := s) (u := u) hs_pos
        (by simpa [q] using hq_ne)
  exact le_trans (csInf_le hbdd hmem)
    (by simpa [hmin_eq] using hangle_q_le_xstar)

/-- Theorem 6, theorem-backed literal statement. -/
theorem theorem6_scaling_to_find_minimum_codeword :
    theorem6_scaling_to_find_minimum_codeword_statement := by
  intro n _hn A hzero hpos hneg Q hQ u
  exact le_antisymm
    (theorem6_minAngle_le_scaleSearch_sInf
      (A := A) (Q := Q) hpos hneg hQ u)
    (theorem6_scaleSearch_sInf_le_minAngle
      (A := A) (Q := Q) hzero hpos hneg hQ u)

end PaperProofs
