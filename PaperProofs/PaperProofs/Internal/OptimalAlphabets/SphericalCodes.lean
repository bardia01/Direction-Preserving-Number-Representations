import Mathlib

/-!
# OptimalAlphabets.SphericalCodes

Basic definitions for unconstrained spherical codes in `S^{n-1}`.
-/

noncomputable section

open Set Filter Topology Real Metric
open NormedSpace

namespace OptimalAlphabets

/-- A point on the unit sphere in `ℝ^n`. -/
abbrev SpherePoint (n : ℕ) :=
  {u : EuclideanSpace ℝ (Fin n) // u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1}

/-- The minimum angular distance from a sphere point to a finite spherical code. -/
def minAngleToSphericalCode {n : ℕ} (C : Finset (SpherePoint n)) (u : SpherePoint n) : ℝ :=
  if h : C.Nonempty then
    C.inf' h (fun c => InnerProductGeometry.angle u.1 c.1)
  else
    π

/-- The covering radius of a finite spherical code. -/
def covrad_sph {n : ℕ} (C : Finset (SpherePoint n)) : ℝ :=
  sSup (Set.range (minAngleToSphericalCode C))

/-- The set of finite spherical codes in `S^{n-1}` with exactly `m` points. -/
def sphericalCodesOfCard (n m : ℕ) : Set (Finset (SpherePoint n)) :=
  {C | C.card = m}

/-- The optimal covering radius among all `m`-point spherical codes in `S^{n-1}`. -/
def rho_sph (n m : ℕ) : ℝ :=
  sInf (covrad_sph '' sphericalCodesOfCard n m)

theorem minAngleToSphericalCode_nonneg {n : ℕ} (C : Finset (SpherePoint n)) (u : SpherePoint n) :
    0 ≤ minAngleToSphericalCode C u := by
  unfold minAngleToSphericalCode
  split_ifs with h
  · exact le_trans (by norm_num) (Finset.le_inf' _ _ fun c _ => InnerProductGeometry.angle_nonneg _ _)
  · exact Real.pi_pos.le

theorem minAngleToSphericalCode_le_pi {n : ℕ} (C : Finset (SpherePoint n)) (u : SpherePoint n) :
    minAngleToSphericalCode C u ≤ π := by
  unfold minAngleToSphericalCode
  split_ifs with h
  · exact le_trans (Finset.inf'_le _ (Classical.choose_spec h)) (InnerProductGeometry.angle_le_pi _ _)
  · exact le_rfl

theorem covrad_sph_nonneg {n : ℕ} (C : Finset (SpherePoint n)) :
    0 ≤ covrad_sph C := by
  unfold covrad_sph
  refine Real.sSup_nonneg ?_
  rintro x ⟨u, rfl⟩
  exact minAngleToSphericalCode_nonneg C u

/-- A simple explicit family of nonzero vectors in `ℝ^(n+2)` used to show that
the unit sphere is infinite. -/
def sphereFamilyVec (n t : ℕ) : EuclideanSpace ℝ (Fin (n + 2)) :=
  EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) +
    EuclideanSpace.single ⟨1, by omega⟩ ((t : ℝ) + 1)

@[simp] theorem sphereFamilyVec_zero (n t : ℕ) :
    sphereFamilyVec n t 0 = 1 := by
  simp [sphereFamilyVec]

@[simp] theorem sphereFamilyVec_one (n t : ℕ) :
    sphereFamilyVec n t 1 = (t : ℝ) + 1 := by
  simp [sphereFamilyVec]

lemma sphereFamilyVec_ne_zero (n t : ℕ) :
    sphereFamilyVec n t ≠ 0 := by
  intro hzero
  have h0 : sphereFamilyVec n t 0 = 0 := by
    simpa using congrArg (fun z => z 0) hzero
  rw [sphereFamilyVec_zero] at h0
  norm_num at h0

/-- An explicit infinite family of points on `S^(n+1)`. -/
def sphereFamilyPoint (n t : ℕ) : SpherePoint (n + 2) :=
  ⟨NormedSpace.normalize (sphereFamilyVec n t), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact NormedSpace.norm_normalize (x := sphereFamilyVec n t) (sphereFamilyVec_ne_zero n t)⟩

theorem spherePoint_nonempty (n : ℕ) : Nonempty (SpherePoint (n + 2)) :=
  ⟨sphereFamilyPoint n 0⟩

theorem sphereFamilyPoint_injective (n : ℕ) :
    Function.Injective (sphereFamilyPoint n) := by
  intro t t' hpoint
  have hne : sphereFamilyVec n t ≠ 0 := sphereFamilyVec_ne_zero n t
  have hne' : sphereFamilyVec n t' ≠ 0 := sphereFamilyVec_ne_zero n t'
  have hsame :
      SameRay ℝ (sphereFamilyVec n t) (sphereFamilyVec n t') := by
    rw [sameRay_iff_inv_norm_smul_eq_of_ne hne hne']
    simpa [sphereFamilyPoint, NormedSpace.normalize] using congrArg Subtype.val hpoint
  have hnorm_eq :
      ‖sphereFamilyVec n t‖ = ‖sphereFamilyVec n t'‖ := by
    have hsmul := SameRay.norm_smul_eq hsame
    have hcoord := congrArg (fun z => z 0) hsmul
    change
      ‖sphereFamilyVec n t‖ * sphereFamilyVec n t' 0 =
        ‖sphereFamilyVec n t'‖ * sphereFamilyVec n t 0 at hcoord
    rw [sphereFamilyVec_zero, sphereFamilyVec_zero] at hcoord
    nlinarith
  have hvec : sphereFamilyVec n t = sphereFamilyVec n t' :=
    hsame.eq_of_norm_eq hnorm_eq
  have hcoord : (t : ℝ) + 1 = (t' : ℝ) + 1 := by
    have hcoord' := congrArg (fun z => z 1) hvec
    simpa [sphereFamilyVec] using hcoord'
  have hreal : (t : ℝ) = t' := by
    linarith
  exact_mod_cast hreal

theorem spherePoint_infinite (n : ℕ) : Infinite (SpherePoint (n + 2)) := by
  rw [← not_finite_iff_infinite]
  intro hfin
  letI := hfin
  have hnat : Finite ℕ := Finite.of_injective (sphereFamilyPoint n) (sphereFamilyPoint_injective n)
  exact (not_finite_iff_infinite.mpr (inferInstance : Infinite ℕ)) hnat

theorem bddAbove_range_minAngleToSphericalCode {n : ℕ} (C : Finset (SpherePoint n)) :
    BddAbove (Set.range (minAngleToSphericalCode C)) := by
  refine ⟨π, ?_⟩
  rintro y ⟨u, rfl⟩
  exact minAngleToSphericalCode_le_pi C u

theorem minAngleToSphericalCode_anti {n : ℕ} {C D : Finset (SpherePoint n)}
    (hCD : C ⊆ D) (u : SpherePoint n) :
    minAngleToSphericalCode D u ≤ minAngleToSphericalCode C u := by
  unfold minAngleToSphericalCode
  by_cases hD : D.Nonempty
  · by_cases hC : C.Nonempty
    · simpa [hD, hC] using
        (Finset.inf'_mono (f := fun c : SpherePoint n => InnerProductGeometry.angle u.1 c.1) hCD hC)
    · have hchoose :
          D.inf' hD (fun c : SpherePoint n => InnerProductGeometry.angle u.1 c.1) ≤
            InnerProductGeometry.angle u.1 (Classical.choose hD).1 := by
        exact Finset.inf'_le _ (Classical.choose_spec hD)
      simpa [hD, hC] using
        (le_trans hchoose
          (InnerProductGeometry.angle_le_pi u.1 (Classical.choose hD).1))
  · have hC : ¬ C.Nonempty := by
      intro hC
      rcases hC with ⟨c, hc⟩
      exact hD ⟨c, hCD hc⟩
    simp [hD, hC]

theorem covrad_sph_anti {n : ℕ} (hsp : Nonempty (SpherePoint n)) {C D : Finset (SpherePoint n)}
    (hCD : C ⊆ D) :
    covrad_sph D ≤ covrad_sph C := by
  unfold covrad_sph
  refine csSup_le ?_ ?_
  · rcases hsp with ⟨u⟩
    exact ⟨_, ⟨u, rfl⟩⟩
  rintro y ⟨u, rfl⟩
  exact le_trans (minAngleToSphericalCode_anti hCD u)
    (le_csSup (bddAbove_range_minAngleToSphericalCode C) (Set.mem_range_self u))

theorem exists_sphericalCode_of_card_eq (n m : ℕ) :
    ∃ C : Finset (SpherePoint (n + 2)), C.card = m := by
  letI : Infinite (SpherePoint (n + 2)) := spherePoint_infinite n
  exact Infinite.exists_subset_card_eq (SpherePoint (n + 2)) m

theorem exists_sphericalCode_superset_of_card_eq (n : ℕ) {m₁ m₂ : ℕ}
    (hm : m₁ ≤ m₂) (C : Finset (SpherePoint (n + 2))) (hC : C.card = m₁) :
    ∃ D : Finset (SpherePoint (n + 2)), C ⊆ D ∧ D.card = m₂ := by
  letI : Infinite (SpherePoint (n + 2)) := spherePoint_infinite n
  simpa [hC] using Infinite.exists_superset_card_eq C m₂ (hC ▸ hm)

theorem rho_sph_antitone_succ_succ (n : ℕ) :
    Antitone (rho_sph (n + 2)) := by
  intro m₁ m₂ hm
  unfold rho_sph
  let S₁ : Set ℝ := covrad_sph '' sphericalCodesOfCard (n + 2) m₁
  let S₂ : Set ℝ := covrad_sph '' sphericalCodesOfCard (n + 2) m₂
  have hS₁_nonempty : Set.Nonempty S₁ := by
    rcases exists_sphericalCode_of_card_eq n m₁ with ⟨C, hC⟩
    exact ⟨covrad_sph C, ⟨C, hC, rfl⟩⟩
  have hS₂_bddBelow : BddBelow S₂ := by
    refine ⟨0, ?_⟩
    rintro y ⟨C, hC, rfl⟩
    exact covrad_sph_nonneg C
  refine le_csInf hS₁_nonempty ?_
  intro y hy
  rcases hy with ⟨C, hC, rfl⟩
  rcases exists_sphericalCode_superset_of_card_eq n hm C hC with ⟨D, hCD, hD⟩
  exact le_trans (csInf_le hS₂_bddBelow ⟨D, hD, rfl⟩)
    (covrad_sph_anti (spherePoint_nonempty n) hCD)

theorem rho_sph_antitone_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    Antitone (rho_sph n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm] using rho_sph_antitone_succ_succ m

theorem rho_sph_monotone_points {n m₁ m₂ : ℕ} (hn : 2 ≤ n) (hm : m₁ ≤ m₂) :
    rho_sph n m₂ ≤ rho_sph n m₁ :=
  rho_sph_antitone_of_two_le hn hm

end OptimalAlphabets
