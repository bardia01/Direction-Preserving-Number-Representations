import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct

/-!
# Paper-facing definitions

This file fixes notation for the paper artifact.  The underlying formalization
uses the clean asymmetric-product layer over `Finset Real`; these wrappers give
paper-style names for the same objects.
-/

noncomputable section

open Set Filter Topology Real Metric

namespace PaperProofs

/-- Definition 1: finite scalar alphabets of cardinality `q`. -/
abbrev Aq (q : Nat) : Set (Finset Real) :=
  {A : Finset Real | A.card = q}

/-- Raw product tuples over the scalar alphabet. -/
abbrev productTuples (n : Nat) (A : Finset Real) : Finset (Fin n -> Real) :=
  OptimalAlphabets.AsymmetricProduct.asymProductTuples n A

/-- Nonzero raw product tuples over the scalar alphabet. -/
abbrev nonzeroProductTuples (n : Nat) (A : Finset Real) :
    Finset (Fin n -> Real) :=
  OptimalAlphabets.AsymmetricProduct.nonzeroAsymProductTuples n A

/-- Product directions as Euclidean unit vectors. -/
abbrev Pdir (n : Nat) (A : Finset Real) :
    Finset (EuclideanSpace Real (Fin n)) :=
  OptimalAlphabets.AsymmetricProduct.asymProdDirections n A

/-- Definition 2: product code direction set, as a finite spherical code. -/
abbrev P (n : Nat) (A : Finset Real) :
    Finset (OptimalAlphabets.SpherePoint n) :=
  OptimalAlphabets.AsymmetricProduct.asymProdSphericalCode n A

/-- Definition 3: product code covering objective. -/
abbrev F (n : Nat) (A : Finset Real) : Real :=
  OptimalAlphabets.AsymmetricProduct.F_asym n A

/-- Definition 4: best achievable value at fixed alphabet size. -/
def w (n q : Nat) : Real :=
  sInf ((fun A : Finset Real => F n A) '' Aq q)

/-- Definition 5: optimal spherical covering radius. -/
abbrev rhoSph (n m : Nat) : Real :=
  OptimalAlphabets.rho_sph n m

/-- Definition 6: harmonic number used by the harmonic witness. -/
abbrev H (n : Nat) : Real :=
  OptimalAlphabets.AsymmetricProduct.H n

/-- Definition 6: normalized harmonic witness. -/
abbrev harmonicWitness (n : Nat) (hn : 0 < n) :
    OptimalAlphabets.SpherePoint n :=
  OptimalAlphabets.AsymmetricProduct.harmonicWitness n hn

/-- Definition 7: number of positive alphabet entries. -/
abbrev pPos (A : Finset Real) : Nat :=
  OptimalAlphabets.AsymmetricProduct.posCount A

/-- Definition 7: number of negative alphabet entries. -/
abbrev pNeg (A : Finset Real) : Nat :=
  OptimalAlphabets.AsymmetricProduct.negCount A

/-- Definition 7: smaller nonzero sign count. -/
abbrev mSign (A : Finset Real) : Nat :=
  OptimalAlphabets.AsymmetricProduct.signMinCount A

/-- Complementary cosine objective used in Section VII. -/
abbrev alpha (n : Nat) (A : Finset Real) : Real :=
  OptimalAlphabets.AsymmetricProduct.alpha_asym n A

/-- Harmonic-normalized best arbitrary-alphabet cosine objective. -/
abbrev normBestAlpha (n q : Nat) : Real :=
  OptimalAlphabets.AsymmetricProduct.normBestAsymCos n q

/-- Definition 9: positive decoded floating-point levels. -/
abbrev PhiPlus (e t : Nat) : Finset Real :=
  OptimalAlphabets.AsymmetricProduct.fpPositiveFinset e t

/-- Definition 9: full decoded real floating-point alphabet. -/
abbrev Phi (e t : Nat) : Finset Real :=
  OptimalAlphabets.AsymmetricProduct.fpAlphabet e t

/-- Valid floating-point mantissa-bit choices at total bit-width `b`. -/
abbrev fpSplits (b : Nat) : Finset Nat :=
  OptimalAlphabets.AsymmetricProduct.fpSplitIndices b

/-- Exponent bits associated with a floating-point split. -/
abbrev fpExponentBits (b t : Nat) : Nat :=
  OptimalAlphabets.AsymmetricProduct.fpExponentBits b t

/-- Floating-point cosine objective optimized over valid total-bit splits. -/
abbrev bestFpCos (n b : Nat) : Real :=
  OptimalAlphabets.AsymmetricProduct.bestFpCos n b

/-- Harmonic-normalized floating-point cosine objective. -/
abbrev normBestFpCos (n b : Nat) : Real :=
  OptimalAlphabets.AsymmetricProduct.normBestFpCos n b

/-- Paper constant for arbitrary alphabets in Theorem 5. -/
abbrev arbConst (b : Nat) : Real :=
  OptimalAlphabets.AsymmetricProduct.arbConst b

/-- Paper constant for floating-point alphabets in Theorem 5. -/
abbrev fpConst (b : Nat) : Real :=
  OptimalAlphabets.AsymmetricProduct.fpConst b

/-- Antipodal binary alphabet predicate used in the dimension-2 statements. -/
def IsAntipodalBinary (A : Finset Real) : Prop :=
  ∃ a : Real, 0 < a ∧ forall x : Real, x ∈ A ↔ x = -a ∨ x = a

end PaperProofs
