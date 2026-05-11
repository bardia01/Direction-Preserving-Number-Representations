import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.Correlation

/-!
# OptimalAlphabets.AsymmetricProduct.NormalizedObjective

Best arbitrary-alphabet correlation objectives and their harmonic
normalization.
-/

noncomputable section

open Set Filter Topology Real Metric

namespace OptimalAlphabets
namespace AsymmetricProduct

/-- The canonical `q`-point real finset `{0, 1, ..., q-1}`. -/
def natCastEmbedding : ℕ ↪ ℝ where
  toFun n := (n : ℝ)
  inj' := by
    intro a b h
    exact Nat.cast_injective h

/-- A concrete real finset of cardinality `q`, used to witness nonemptiness of
the index set for `bestAsymCos`. -/
def canonicalRealFinset (q : ℕ) : Finset ℝ :=
  (Finset.range q).map natCastEmbedding

@[simp] theorem canonicalRealFinset_card (q : ℕ) :
    (canonicalRealFinset q).card = q := by
  simp [canonicalRealFinset]

/-- Best correlation among arbitrary scalar alphabets of exact cardinality
`q`. -/
def bestAsymCos (n q : ℕ) : ℝ :=
  sSup (alpha_asym n '' {A : Finset ℝ | A.card = q})

/-- Harmonic-normalized best arbitrary-alphabet correlation. -/
def normBestAsymCos (n q : ℕ) : ℝ :=
  Real.sqrt (H n) * bestAsymCos n q
/-- The image set defining `bestAsymCos` is bounded above by `1`. -/
theorem bestAsymCos_index_bddAbove {n q : ℕ} (hn : 0 < n) :
    BddAbove (alpha_asym n '' {A : Finset ℝ | A.card = q}) := by
  refine ⟨1, ?_⟩
  rintro y ⟨A, _hA, rfl⟩
  exact alpha_asym_le_one hn A

/-- Any explicit alphabet of cardinality `q` contributes to `bestAsymCos`. -/
theorem le_bestAsymCos_of_card {n q : ℕ} (hn : 0 < n)
    {A : Finset ℝ} (hA : A.card = q) :
    alpha_asym n A ≤ bestAsymCos n q := by
  unfold bestAsymCos
  exact le_csSup (bestAsymCos_index_bddAbove (n := n) (q := q) hn)
    ⟨A, hA, rfl⟩

end AsymmetricProduct
end OptimalAlphabets
