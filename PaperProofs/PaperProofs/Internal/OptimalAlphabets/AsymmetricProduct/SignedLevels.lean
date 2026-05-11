import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.NormalizedObjective

/-!
# OptimalAlphabets.AsymmetricProduct.SignedLevels

Small finite-set helpers for alphabets of the form `{0} ∪ S ∪ (-S)`.
-/

noncomputable section

open Set Filter Topology Real Metric

namespace OptimalAlphabets
namespace AsymmetricProduct

/-- Negation as an embedding of real finite sets. -/
def negEmbedding : ℝ ↪ ℝ where
  toFun x := -x
  inj' := by
    intro a b h
    exact neg_inj.mp h

/-- The signed alphabet `{0} ∪ S ∪ (-S)`. -/
def signedFinset (S : Finset ℝ) : Finset ℝ :=
  insert 0 (S ∪ S.map negEmbedding)

@[simp] theorem mem_signedFinset {S : Finset ℝ} {x : ℝ} :
    x ∈ signedFinset S ↔ x = 0 ∨ x ∈ S ∨ -x ∈ S := by
  classical
  simp [signedFinset, negEmbedding]
  constructor
  · rintro (hzero | hS | ⟨a, ha, hax⟩)
    · exact Or.inl hzero
    · exact Or.inr (Or.inl hS)
    · have hxS : -x ∈ S := by
        have hxa : -x = a := by linarith
        simpa [hxa] using ha
      exact Or.inr (Or.inr hxS)
  · rintro (hzero | hS | hxS)
    · exact Or.inl hzero
    · exact Or.inr (Or.inl hS)
    · exact Or.inr (Or.inr ⟨-x, hxS, by ring⟩)

/-- Cardinality of `{0} ∪ S ∪ (-S)` when `S` consists of positive values. -/
theorem signedFinset_card_of_pos {S : Finset ℝ}
    (hpos : ∀ x ∈ S, 0 < x) :
    (signedFinset S).card = 2 * S.card + 1 := by
  classical
  have hdisj : Disjoint S (S.map negEmbedding) := by
    rw [Finset.disjoint_left]
    intro x hx hxneg
    rcases Finset.mem_map.1 hxneg with ⟨y, hy, hyx⟩
    have hxpos : 0 < x := hpos x hx
    have hypos : 0 < y := hpos y hy
    have hxy : x = -y := by simpa [negEmbedding] using hyx.symm
    linarith
  have hzero_not : 0 ∉ S ∪ S.map negEmbedding := by
    intro h0
    rcases Finset.mem_union.1 h0 with hS | hN
    · have := hpos 0 hS
      linarith
    · rcases Finset.mem_map.1 hN with ⟨y, hy, hy0⟩
      have hypos : 0 < y := hpos y hy
      have : (0 : ℝ) = -y := by simpa [negEmbedding] using hy0
      linarith
  calc
    (signedFinset S).card
        = (S ∪ S.map negEmbedding).card + 1 := by
          simp [signedFinset, hzero_not, add_comm]
    _ = S.card + (S.map negEmbedding).card + 1 := by
          rw [Finset.card_union_of_disjoint hdisj]
    _ = 2 * S.card + 1 := by
          simp [Nat.two_mul, add_assoc]

end AsymmetricProduct
end OptimalAlphabets
