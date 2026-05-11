import Mathlib
import PaperProofs.Internal.OptimalAlphabets.SphericalCodes

/-!
# OptimalAlphabets.SphericalCapMeasure.Defs

Basic definitions for normalized spherical cap measure on `S^(n-1)`.
-/

noncomputable section

open Set Filter Topology Real Metric MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace OptimalAlphabets

/-- Surface measure on the unit sphere in `ℝ^n`, realized via `Measure.toSphere`. -/
def sphereSurfaceMeasure (n : ℕ) :
    Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

/-- Surface area of the unit sphere `S^m`, viewed as a real number. -/
def sphereArea (m : ℕ) : ℝ :=
  (sphereSurfaceMeasure (m + 1)).real Set.univ

/-- The first standard basis vector in `ℝ^n`, totalized by returning `0` when `n = 0`. -/
def e1Vec (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  if hn : 0 < n then EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ) else 0

/-- The spherical cap cut out by the angle bound `a` around `e₁`. -/
def capSet (n : ℕ) (a : ℝ) : Set (SpherePoint n) :=
  {x | InnerProductGeometry.angle x.1 (e1Vec n) ≤ a}

/-- The normalized spherical cap measure. For `n = 0` we set it to `0`. -/
def capMeasure (n : ℕ) (a : ℝ) : ℝ :=
  if 0 < n then
    (sphereSurfaceMeasure n).real (capSet n a) / sphereArea (n - 1)
  else
    0

@[simp]
theorem sphereArea_def (m : ℕ) :
    sphereArea m = (sphereSurfaceMeasure (m + 1)).real Set.univ := rfl

@[simp]
theorem e1Vec_eq_zero {n : ℕ} (hn : ¬ 0 < n) : e1Vec n = 0 := by
  simp [e1Vec, hn]

@[simp]
theorem e1Vec_eq_single {n : ℕ} (hn : 0 < n) :
    e1Vec n = EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ) := by
  simp [e1Vec, hn]

@[simp]
theorem norm_e1Vec {n : ℕ} (hn : 0 < n) : ‖e1Vec n‖ = 1 := by
  simp [e1Vec, hn]

theorem inner_e1Vec {n : ℕ} (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x (e1Vec n) = x ⟨0, hn⟩ := by
  simpa [e1Vec, hn] using
    (EuclideanSpace.inner_single_right (i := ⟨0, hn⟩) (a := (1 : ℝ)) (v := x))

theorem sphereArea_eq_finrank_mul_volume_ball (m : ℕ) :
    sphereArea m =
      (m + 1) * (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).real (Metric.ball 0 1) := by
  rw [sphereArea, sphereSurfaceMeasure, Measure.toSphere_real_apply_univ]
  simp

theorem sphereArea_pos (m : ℕ) : 0 < sphereArea m := by
  have hne : sphereSurfaceMeasure (m + 1) ≠ 0 := by
    change ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere) ≠ 0
    exact Measure.toSphere_ne_zero
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))))
  letI : NeZero (sphereSurfaceMeasure (m + 1)) := ⟨hne⟩
  letI : IsFiniteMeasure (sphereSurfaceMeasure (m + 1)) := by
    dsimp [sphereSurfaceMeasure]
    infer_instance
  rw [sphereArea]
  exact measureReal_univ_pos (μ := sphereSurfaceMeasure (m + 1))

theorem sphereArea_nonneg (m : ℕ) : 0 ≤ sphereArea m :=
  (sphereArea_pos m).le

theorem capMeasure_eq_div_surfaceMeasure {n : ℕ} (hn : 0 < n) (a : ℝ) :
    capMeasure n a = (sphereSurfaceMeasure n).real (capSet n a) / sphereArea (n - 1) := by
  simp [capMeasure, hn]

theorem mem_capSet_iff_cos_le_coord0 {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) (x : SpherePoint n) :
    x ∈ capSet n a ↔ Real.cos a ≤ (x : EuclideanSpace ℝ (Fin n)) ⟨0, hn⟩ := by
  have hapi' : a ≤ Real.pi := by linarith [hapi]
  have hxnorm : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    have hx' := x.2
    rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx'
  have he1norm : ‖e1Vec n‖ = 1 := norm_e1Vec hn
  constructor
  · intro hx
    have hcos :
        Real.cos a ≤ Real.cos (InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin n)) (e1Vec n)) :=
      Real.cos_le_cos_of_nonneg_of_le_pi
        (InnerProductGeometry.angle_nonneg _ _) hapi' hx
    calc
      Real.cos a
          ≤ Real.cos (InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin n)) (e1Vec n)) := hcos
      _ = (x : EuclideanSpace ℝ (Fin n)) ⟨0, hn⟩ := by
        rw [InnerProductGeometry.cos_angle, hxnorm, he1norm, inner_e1Vec hn]
        norm_num
  · intro hx
    have h_arccos :
        Real.arccos ((x : EuclideanSpace ℝ (Fin n)) ⟨0, hn⟩) ≤ Real.arccos (Real.cos a) :=
      Real.arccos_le_arccos hx
    have hacos : Real.arccos (Real.cos a) = a :=
      Real.arccos_cos ha0 hapi'
    have hangle :
        InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin n)) (e1Vec n) =
          Real.arccos ((x : EuclideanSpace ℝ (Fin n)) ⟨0, hn⟩) := by
      simp [InnerProductGeometry.angle, hxnorm, he1norm, inner_e1Vec hn]
    change InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin n)) (e1Vec n) ≤ a
    rw [hangle]
    exact le_trans h_arccos hacos.le

theorem measurableSet_capSet {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    MeasurableSet (capSet n a) := by
  let i0 : Fin n := ⟨0, hn⟩
  have hcap :
      capSet n a = {x : SpherePoint n | Real.cos a ≤ (x : EuclideanSpace ℝ (Fin n)) i0} := by
    ext x
    simpa [i0] using mem_capSet_iff_cos_le_coord0 hn ha0 hapi x
  rw [hcap]
  have hcont :
      Continuous fun x : SpherePoint n => (x : EuclideanSpace ℝ (Fin n)) i0 := by
    simpa using
      ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) i0).comp continuous_subtype_val)
  exact (isClosed_le continuous_const hcont).measurableSet

end OptimalAlphabets
