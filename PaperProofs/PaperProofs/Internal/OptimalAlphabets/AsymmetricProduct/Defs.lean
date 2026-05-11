import PaperProofs.Internal.OptimalAlphabets.SphericalCodes
import Mathlib.Data.Fintype.BigOperators

/-!
# OptimalAlphabets.AsymmetricProduct.Defs

Definitions for product-direction codes built from an arbitrary finite scalar
alphabet `A : Finset ℝ`.

This file is deliberately independent of the normalized/signed product-code
machinery used elsewhere in the repository.  The only geometric dependency is
the generic spherical-code layer.
-/

noncomputable section

open Set Filter Topology Real Metric
open NormedSpace

namespace OptimalAlphabets
namespace AsymmetricProduct

/-- Raw product tuples over a finite scalar alphabet. -/
def asymProductTuples (n : ℕ) (A : Finset ℝ) : Finset (Fin n → ℝ) :=
  Fintype.piFinset fun _ : Fin n => A

theorem mem_asymProductTuples {n : ℕ} {A : Finset ℝ} {x : Fin n → ℝ} :
    x ∈ asymProductTuples n A ↔ ∀ i, x i ∈ A := by
  simp [asymProductTuples, Fintype.mem_piFinset]

/-- The raw product tuple count is exactly `A.card ^ n`. -/
theorem asymProductTuples_card (n : ℕ) (A : Finset ℝ) :
    (asymProductTuples n A).card = A.card ^ n := by
  simp [asymProductTuples]

/-- Interpret a raw tuple as a vector in Euclidean space. -/
def tupleVector {n : ℕ} (x : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm x

@[simp] theorem tupleVector_apply {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    tupleVector x i = x i := by
  simp [tupleVector]

theorem tupleVector_eq_zero_iff {n : ℕ} (x : Fin n → ℝ) :
    tupleVector x = 0 ↔ ∀ i, x i = 0 := by
  constructor
  · intro h i
    have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) h
    simpa using hcoord
  · intro h
    ext i
    simp [h i]

theorem tupleVector_ne_zero_iff {n : ℕ} (x : Fin n → ℝ) :
    tupleVector x ≠ 0 ↔ ∃ i, x i ≠ 0 := by
  constructor
  · intro hx
    by_contra hnone
    apply hx
    exact (tupleVector_eq_zero_iff x).2 fun i =>
      not_not.mp (not_exists.mp hnone i)
  · rintro ⟨i, hi⟩ hzero
    exact hi ((tupleVector_eq_zero_iff x).1 hzero i)

/-- Raw product tuples whose associated vector is nonzero. -/
def nonzeroAsymProductTuples (n : ℕ) (A : Finset ℝ) : Finset (Fin n → ℝ) := by
  classical
  exact (asymProductTuples n A).filter fun x => tupleVector x ≠ 0

theorem mem_nonzeroAsymProductTuples {n : ℕ} {A : Finset ℝ} {x : Fin n → ℝ} :
    x ∈ nonzeroAsymProductTuples n A ↔ (∀ i, x i ∈ A) ∧ tupleVector x ≠ 0 := by
  classical
  simp [nonzeroAsymProductTuples, mem_asymProductTuples]

/-- Product directions induced by nonzero raw product tuples. -/
def asymProdDirections (n : ℕ) (A : Finset ℝ) :
    Finset (EuclideanSpace ℝ (Fin n)) := by
  classical
  exact (nonzeroAsymProductTuples n A).image fun x => NormedSpace.normalize (tupleVector x)

theorem mem_asymProdDirections {n : ℕ} {A : Finset ℝ}
    {v : EuclideanSpace ℝ (Fin n)} :
    v ∈ asymProdDirections n A ↔
      ∃ x, x ∈ nonzeroAsymProductTuples n A ∧
        NormedSpace.normalize (tupleVector x) = v := by
  classical
  simp [asymProdDirections, eq_comm]

/-- Every induced product direction lies on the unit sphere. -/
theorem mem_sphere_of_mem_asymProdDirections {n : ℕ} {A : Finset ℝ}
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ asymProdDirections n A) :
    v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  classical
  rcases mem_asymProdDirections.1 hv with ⟨x, hx, rfl⟩
  have hx_ne : tupleVector x ≠ 0 := (mem_nonzeroAsymProductTuples.1 hx).2
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  exact NormedSpace.norm_normalize (x := tupleVector x) hx_ne

/-- Embed the finite set of Euclidean product directions into the sphere subtype. -/
def asymProdDirectionsEmbedding (n : ℕ) (A : Finset ℝ) :
    {v : EuclideanSpace ℝ (Fin n) // v ∈ asymProdDirections n A} ↪ SpherePoint n where
  toFun v := ⟨v.1, mem_sphere_of_mem_asymProdDirections v.2⟩
  inj' := by
    intro v w h
    have hvw : v.1 = w.1 := by
      exact congrArg (fun p : SpherePoint n => p.1) h
    exact Subtype.ext hvw

/-- The asymmetric product spherical code. -/
def asymProdSphericalCode (n : ℕ) (A : Finset ℝ) : Finset (SpherePoint n) :=
  (asymProdDirections n A).attach.map (asymProdDirectionsEmbedding n A)

/-- Product-code covering objective for an arbitrary finite scalar alphabet. -/
def F_asym (n : ℕ) (A : Finset ℝ) : ℝ :=
  covrad_sph (asymProdSphericalCode n A)

@[simp] theorem F_asym_def (n : ℕ) (A : Finset ℝ) :
    F_asym n A = covrad_sph (asymProdSphericalCode n A) :=
  rfl

/-- Positive entries of a finite scalar alphabet. -/
def posPart (A : Finset ℝ) : Finset ℝ := by
  classical
  exact A.filter fun a => 0 < a

/-- Negative entries of a finite scalar alphabet. -/
def negPart (A : Finset ℝ) : Finset ℝ := by
  classical
  exact A.filter fun a => a < 0

/-- Number of positive alphabet entries. -/
def posCount (A : Finset ℝ) : ℕ :=
  (posPart A).card

/-- Number of negative alphabet entries. -/
def negCount (A : Finset ℝ) : ℕ :=
  (negPart A).card

/-- The smaller of the two nonzero sign counts. -/
def signMinCount (A : Finset ℝ) : ℕ :=
  min (posCount A) (negCount A)

theorem posCount_le_card (A : Finset ℝ) :
    posCount A ≤ A.card := by
  classical
  simpa [posCount, posPart] using Finset.card_filter_le A (fun a : ℝ => 0 < a)

theorem posPart_subset (A : Finset ℝ) :
    posPart A ⊆ A := by
  classical
  intro a ha
  have hmem : a ∈ A ∧ 0 < a := by
    simpa [posPart] using ha
  exact hmem.1

theorem negPart_subset (A : Finset ℝ) :
    negPart A ⊆ A := by
  classical
  intro a ha
  have hmem : a ∈ A ∧ a < 0 := by
    simpa [negPart] using ha
  exact hmem.1

theorem disjoint_posPart_negPart (A : Finset ℝ) :
    Disjoint (posPart A) (negPart A) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hneg
  have hpos_mem : a ∈ A ∧ 0 < a := by
    simpa [posPart] using ha
  have hneg_mem : a ∈ A ∧ a < 0 := by
    simpa [negPart] using hneg
  have hpos' : 0 < a := hpos_mem.2
  have hneg' : a < 0 := hneg_mem.2
  linarith

theorem posCount_add_negCount_le_card (A : Finset ℝ) :
    posCount A + negCount A ≤ A.card := by
  classical
  have hsub : posPart A ∪ negPart A ⊆ A := by
    intro a ha
    rcases Finset.mem_union.1 ha with hpos | hneg
    · exact posPart_subset A hpos
    · exact negPart_subset A hneg
  have hcard := Finset.card_le_card hsub
  have hcard_union :
      (posPart A ∪ negPart A).card = posCount A + negCount A := by
    simpa [posCount, negCount] using
      Finset.card_union_of_disjoint (disjoint_posPart_negPart A)
  simpa [hcard_union] using hcard

theorem signMinCount_le_posCount (A : Finset ℝ) :
    signMinCount A ≤ posCount A := by
  simp [signMinCount]

theorem signMinCount_le_negCount (A : Finset ℝ) :
    signMinCount A ≤ negCount A := by
  simp [signMinCount]

theorem signMinCount_le_card_div_two (A : Finset ℝ) :
    signMinCount A ≤ A.card / 2 := by
  have hsum := posCount_add_negCount_le_card A
  have hmin_pos := signMinCount_le_posCount A
  have hmin_neg := signMinCount_le_negCount A
  omega

end AsymmetricProduct
end OptimalAlphabets
