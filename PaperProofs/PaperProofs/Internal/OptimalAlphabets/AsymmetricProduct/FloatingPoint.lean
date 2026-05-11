import PaperProofs.Internal.OptimalAlphabets.ScalarBaselines
import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.SignedLevels

/-!
# OptimalAlphabets.AsymmetricProduct.FloatingPoint

Canonical total-bit floating-point alphabets for the direct correlation
objective.  The convention in this file is the paper convention:

* total bit-width is `b`;
* one bit is a sign bit;
* exponent bits `e` satisfy `1 ≤ e`;
* trailing mantissa bits `t` satisfy `0 ≤ t`;
* valid splits satisfy `e + t = b - 1`.
-/

noncomputable section

open Set Filter Topology Real Metric

namespace OptimalAlphabets
namespace AsymmetricProduct

/-- Positive floating-point levels as a finite set. -/
def fpPositiveEmbedding (e t : ℕ) : Fin (floatPositiveCard e t) ↪ ℝ where
  toFun i := floatingPositiveLevels e t i
  inj' := (strictMono_floatingPositiveLevels e t).injective

/-- Positive decoded floating-point levels. -/
def fpPositiveFinset (e t : ℕ) : Finset ℝ :=
  Finset.univ.map (fpPositiveEmbedding e t)

@[simp] theorem fpPositiveFinset_card (e t : ℕ) :
    (fpPositiveFinset e t).card = floatPositiveCard e t := by
  simp [fpPositiveFinset]

/-- Full decoded real floating-point alphabet: zero plus signed positive
levels.  Signed zero has already collapsed to the single scalar value `0`. -/
def fpAlphabet (e t : ℕ) : Finset ℝ :=
  signedFinset (fpPositiveFinset e t)

/-- Positive decoded floating-point levels in decreasing order. -/
def fpDescendingPositiveLevels (e t : ℕ) :
    Fin (floatPositiveCard e t) → ℝ :=
  fun i =>
    floatingPositiveLevels e t
      ⟨floatPositiveCard e t - 1 - (i : ℕ), by
        have hi := i.2
        omega⟩

/-- The decreasing floating-point levels are positive. -/
theorem fpDescendingPositiveLevels_pos (e t : ℕ)
    (i : Fin (floatPositiveCard e t)) :
    0 < fpDescendingPositiveLevels e t i := by
  unfold fpDescendingPositiveLevels
  exact floatingPositiveLevels_pos e t _

/-- The decreasing floating-point level sequence is strictly decreasing. -/
theorem fpDescendingPositiveLevels_desc (e t : ℕ) :
    ∀ {i j : Fin (floatPositiveCard e t)}, i < j →
      fpDescendingPositiveLevels e t j <
        fpDescendingPositiveLevels e t i := by
  intro i j hij
  unfold fpDescendingPositiveLevels
  apply strictMono_floatingPositiveLevels e t
  have hi := i.2
  have hj := j.2
  have hij_nat : (i : ℕ) < (j : ℕ) := hij
  change floatPositiveCard e t - 1 - (j : ℕ) <
    floatPositiveCard e t - 1 - (i : ℕ)
  omega

/-- Positive decoded count for a total-bit split. -/
theorem fpPositiveCard_total {e t b : ℕ} (h : e + t = b - 1) :
    floatPositiveCard e t = 2 ^ (b - 1) - 1 := by
  rw [floatPositiveCard, h]

/-- Consecutive decoded positive floating-point values grow by at most a
factor of two. -/
lemma floatValueCode_succ_le_two_mul (p : ℕ) {u : ℕ} (hu : 0 < u) :
    floatValueCode p (u + 1) ≤ 2 * floatValueCode p u := by
  set B : ℕ := 2 ^ p
  have hB_pos : 0 < B := by
    subst B
    exact pow_pos (by norm_num : 0 < 2) p
  have hB_pos_real : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast hB_pos
  have hB_ne : (B : ℝ) ≠ 0 := hB_pos_real.ne'
  set e : ℕ := u / B
  set m : ℕ := u % B
  have hu_repr : u = e * B + m := by
    dsimp [m, e]
    calc
      u = u % B + B * (u / B) := by
        simpa using (Nat.mod_add_div u B).symm
      _ = (u / B) * B + u % B := by ac_rfl
  have hm_lt : m < B := by
    dsimp [m]
    exact Nat.mod_lt _ hB_pos
  have hrepr : floatValueCode p u = floatValueCodeCore B e m := by
    simp [floatValueCode, B, e, m]
  by_cases hcarry : m + 1 < B
  · have hu1_repr : u + 1 = e * B + (m + 1) := by
      rw [hu_repr]
      omega
    have hdiv1 : (u + 1) / B = e := by
      calc
        (u + 1) / B = (e * B + (m + 1)) / B := by rw [hu1_repr]
        _ = (B * e + (m + 1)) / B := by rw [Nat.mul_comm e B]
        _ = e + (m + 1) / B := by rw [Nat.mul_add_div hB_pos]
        _ = e := by simp [Nat.div_eq_of_lt hcarry]
    have hmod1 : (u + 1) % B = m + 1 := by
      rw [hu1_repr, Nat.mul_add_mod_of_lt hcarry]
    have hrepr1 : floatValueCode p (u + 1) =
        floatValueCodeCore B e (m + 1) := by
      simp [floatValueCode, B, hdiv1, hmod1]
    by_cases he0 : e = 0
    · have hdiv0 : u / B = 0 := by simpa [e] using he0
      have hu_lt_B : u < B := (Nat.div_eq_zero_iff_lt hB_pos).mp hdiv0
      have hm_eq : m = u := by
        dsimp [m]
        exact Nat.mod_eq_of_lt hu_lt_B
      have hm_pos : 0 < m := by
        simpa [hm_eq] using hu
      rw [hrepr, hrepr1]
      simp [floatValueCodeCore, he0]
      have hnum : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by
        have hm_ge_one : (1 : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast hm_pos
        nlinarith
      calc
        ((m : ℝ) + 1) / (B : ℝ)
            ≤ (2 * (m : ℝ)) / (B : ℝ) := by
              exact div_le_div_of_nonneg_right hnum hB_pos_real.le
        _ = 2 * ((m : ℝ) / (B : ℝ)) := by ring
    · rw [hrepr, hrepr1]
      simp [floatValueCodeCore, he0]
      have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (e - 1) := by positivity
      have hfac :
          1 + ((m : ℝ) + 1) / (B : ℝ) ≤
            2 * (1 + (m : ℝ) / (B : ℝ)) := by
        have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast Nat.zero_le m
        have hB_ge_one : (1 : ℝ) ≤ (B : ℝ) := by
          exact_mod_cast hB_pos
        have hfrac :
            ((m : ℝ) + 1) / (B : ℝ) ≤
              1 + 2 * ((m : ℝ) / (B : ℝ)) := by
          have hnum : (m : ℝ) + 1 ≤ (B : ℝ) + 2 * (m : ℝ) := by
            nlinarith
          calc
            ((m : ℝ) + 1) / (B : ℝ)
                ≤ ((B : ℝ) + 2 * (m : ℝ)) / (B : ℝ) := by
                  exact div_le_div_of_nonneg_right hnum hB_pos_real.le
            _ = 1 + 2 * ((m : ℝ) / (B : ℝ)) := by
                  field_simp [hB_ne]
        nlinarith
      calc
        (2 : ℝ) ^ (e - 1) *
            (1 + ((m : ℝ) + 1) / (B : ℝ))
            ≤ (2 : ℝ) ^ (e - 1) *
                (2 * (1 + (m : ℝ) / (B : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hfac hpow_nonneg
        _ = 2 * ((2 : ℝ) ^ (e - 1) *
              (1 + (m : ℝ) / (B : ℝ))) := by
              ring
  · have hm_last : m + 1 = B := by omega
    have hu1_repr : u + 1 = (e + 1) * B + 0 := by
      calc
        u + 1 = e * B + (m + 1) := by
          rw [hu_repr]
          omega
        _ = e * B + B := by rw [hm_last]
        _ = (e + 1) * B := by rw [Nat.add_mul, Nat.one_mul]
        _ = (e + 1) * B + 0 := by simp
    have hdiv1 : (u + 1) / B = e + 1 := by
      calc
        (u + 1) / B = ((e + 1) * B + 0) / B := by rw [hu1_repr]
        _ = (B * (e + 1) + 0) / B := by rw [Nat.mul_comm (e + 1) B]
        _ = e + 1 + 0 / B := by rw [Nat.mul_add_div hB_pos]
        _ = e + 1 := by simp
    have hmod1 : (u + 1) % B = 0 := by
      calc
        (u + 1) % B = ((e + 1) * B + 0) % B := by rw [hu1_repr]
        _ = 0 := by rw [Nat.mul_add_mod_of_lt hB_pos]
    have hrepr1 : floatValueCode p (u + 1) =
        floatValueCodeCore B (e + 1) 0 := by
      simp [floatValueCode, B, hdiv1, hmod1]
    by_cases he0 : e = 0
    · rw [hrepr, hrepr1]
      simp [floatValueCodeCore, he0]
      have hB_eq : ((B : ℕ) : ℝ) = (m : ℝ) + 1 := by
        exact_mod_cast hm_last.symm
      have hm_pos : 0 < m := by
        have hu_eq_m : u = m := by
          rw [hu_repr, he0]
          simp
        simpa [hu_eq_m] using hu
      have hm_ge_one : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hm_pos
      have hnum : (B : ℝ) ≤ 2 * (m : ℝ) := by
        nlinarith
      calc
        (1 : ℝ) = (B : ℝ) / (B : ℝ) := by
          field_simp [hB_ne]
        _ ≤ (2 * (m : ℝ)) / (B : ℝ) := by
          exact div_le_div_of_nonneg_right hnum hB_pos_real.le
        _ = 2 * ((m : ℝ) / (B : ℝ)) := by ring
    · rw [hrepr, hrepr1]
      have he_pos : 0 < e := Nat.pos_iff_ne_zero.mpr he0
      have hpow_pos : 0 < (2 : ℝ) ^ (e - 1) := by positivity
      have hfrac_nonneg : 0 ≤ (m : ℝ) / (B : ℝ) := by positivity
      have hpow_step : (2 : ℝ) ^ (e - 1) * 2 = (2 : ℝ) ^ e := by
        calc
          (2 : ℝ) ^ (e - 1) * 2 = (2 : ℝ) ^ (e - 1) * (2 : ℝ) ^ 1 := by simp
          _ = (2 : ℝ) ^ ((e - 1) + 1) := by rw [← pow_add]
          _ = (2 : ℝ) ^ e := by rw [Nat.sub_add_cancel (Nat.succ_le_of_lt he_pos)]
      have hcurrent_ge :
          (2 : ℝ) ^ (e - 1) ≤
            (2 : ℝ) ^ (e - 1) * (1 + (m : ℝ) / (B : ℝ)) := by
        nlinarith
      have hmain :
          (2 : ℝ) ^ e ≤
            2 * ((2 : ℝ) ^ (e - 1) * (1 + (m : ℝ) / (B : ℝ))) := by
        calc
          (2 : ℝ) ^ e = 2 * (2 : ℝ) ^ (e - 1) := by
            linarith
          _ ≤ 2 * ((2 : ℝ) ^ (e - 1) *
                (1 + (m : ℝ) / (B : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hcurrent_ge (by norm_num)
      simp [floatValueCodeCore, he0]
      exact hmain

/-- Consecutive positive decoded floating-point levels have ratio at most `2`.
This is the Lean-facing form of the paper's ratio lemma. -/
theorem fp_consecutive_ratio_le_two (e t : ℕ) {j : ℕ}
    (hj : j + 1 < floatPositiveCard e t) :
    floatingPositiveLevels e t ⟨j + 1, hj⟩ ≤
      2 * floatingPositiveLevels e t ⟨j, Nat.lt_of_succ_lt hj⟩ := by
  simpa [floatingPositiveLevels, Nat.add_assoc, Nat.succ_eq_add_one] using
    (floatValueCode_succ_le_two_mul (p := t) (u := j + 1) (Nat.succ_pos j))

/-- Adjacent decreasing floating-point levels differ by at most a factor of
two. -/
theorem fpDescendingPositiveLevels_step_le_two (e t : ℕ) {j : ℕ}
    (hj : j + 1 < floatPositiveCard e t) :
    fpDescendingPositiveLevels e t ⟨j, Nat.lt_of_succ_lt hj⟩ ≤
      2 * fpDescendingPositiveLevels e t ⟨j + 1, hj⟩ := by
  unfold fpDescendingPositiveLevels
  let k : ℕ := floatPositiveCard e t - 1 - (j + 1)
  have hk_succ :
      k + 1 = floatPositiveCard e t - 1 - j := by
    dsimp [k]
    omega
  have hk_succ_lt : k + 1 < floatPositiveCard e t := by
    dsimp [k]
    omega
  have hratio := fp_consecutive_ratio_le_two (e := e) (t := t)
    (j := k) hk_succ_lt
  simpa [k, hk_succ] using hratio

/-- Valid mantissa-bit indices for a total-bit width `b`: `t = 0, ..., b-2`. -/
def fpSplitIndices (b : ℕ) : Finset ℕ :=
  Finset.range (b - 1)

/-- For `b ≥ 2`, the total-bit split index set is nonempty. -/
theorem fpSplitIndices_nonempty {b : ℕ} (hb : 2 ≤ b) :
    (fpSplitIndices b).Nonempty := by
  refine ⟨0, ?_⟩
  simp [fpSplitIndices]
  omega

/-- Exponent bits associated to a total-bit split indexed by `t`. -/
def fpExponentBits (b t : ℕ) : ℕ :=
  b - 1 - t

/-- Valid split indices always have at least one exponent bit. -/
theorem fpExponentBits_pos {b t : ℕ} (hb : 2 ≤ b)
    (ht : t ∈ fpSplitIndices b) :
    1 ≤ fpExponentBits b t := by
  have htlt : t < b - 1 := by
    simpa [fpSplitIndices] using ht
  dsimp [fpExponentBits]
  omega

/-- The split indexed by `t` has total non-sign bits `b - 1`. -/
theorem fpExponentBits_add_t {b t : ℕ}
    (ht : t ∈ fpSplitIndices b) :
    fpExponentBits b t + t = b - 1 := by
  have htlt : t < b - 1 := by
    simpa [fpSplitIndices] using ht
  dsimp [fpExponentBits]
  omega

/-- Best floating-point correlation among valid total-bit splits.  If `b < 2`
there are no valid splits and the harmless sentinel value `-1` is used. -/
def bestFpCos (n b : ℕ) : ℝ :=
  if h : (fpSplitIndices b).Nonempty then
    (fpSplitIndices b).sup' h fun t =>
      alpha_asym n (fpAlphabet (fpExponentBits b t) t)
  else
    -1

/-- Harmonic-normalized best floating-point correlation. -/
def normBestFpCos (n b : ℕ) : ℝ :=
  Real.sqrt (H n) * bestFpCos n b

end AsymmetricProduct
end OptimalAlphabets
