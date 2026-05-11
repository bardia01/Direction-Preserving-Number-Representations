import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.BlockHardy

/-!
# OptimalAlphabets.AsymmetricProduct.NormalizedSeparation

Assembly layer for the normalized asymptotic separation between arbitrary
scalar alphabets and canonical total-bit floating-point alphabets.

The proof is staged so the conditional theorem from `BlockHardyLowerBound`
remains available, and the final theorem supplies the standalone
`blockHardy_lower` proof.

The final public theorem is
`eventually_normBestFpCos_lt_normBestAsymCos`.  For every bit-width `b >= 3`,
it states that, for all sufficiently large dimensions `n`,

`normBestFpCos n b < normBestAsymCos n (2 ^ b)`.

The assembly has four named parts:

* `normBestAsymCos_ge_arbConst_sub_eps_of_blockHardy`: the arbitrary side.
  It uses the explicit exact-cardinality alphabet `blockExactAlphabet`, the
  monotonicity of `alpha_asym`, and `le_bestAsymCos_of_card` for the `sSup`
  defining `bestAsymCos`.
* `normBestFpCos_le_fpConst`: the floating-point side.  It applies the
  sign-symmetric layer-cake obstruction to each valid total-bit split
  `e + t = b - 1`, with `e >= 1`.
* `fpConst_lt_arbConst`: the closed-form constant gap for `b >= 3`.
* `eventually_normBestFpCos_lt_normBestAsymCos_of_blockHardy`: the conditional
  comparison theorem.  The unconditional theorem is obtained from it by
  supplying `blockHardy_lower`.

See `NormalizedSeparationProof.md` in this directory for a human-readable
map from the paper proof to the Lean API names.
-/

noncomputable section

open Set Filter Topology Real Metric

namespace OptimalAlphabets
namespace AsymmetricProduct

/-- Arbitrary-alphabet normalized constant at total bit-width `b`. -/
def arbConst (b : ℕ) : ℝ :=
  2 * Real.sqrt (((2 ^ (b - 1) - 1 : ℕ) : ℝ))

/-- Floating-point normalized obstruction constant at total bit-width `b`. -/
def fpConst (b : ℕ) : ℝ :=
  2 * Real.sqrt ((((2 ^ (b - 1) + 1 : ℕ) : ℝ) / 3))

/-- Conditional arbitrary-side lower bound, obtained from the block-Hardy
construction and the explicit `2^b`-cardinality alphabet
`blockExactAlphabet`. -/
theorem normBestAsymCos_ge_arbConst_sub_eps_of_blockHardy
    (hBlock : BlockHardyLowerBound) {b : ℕ} (hb : 2 ≤ b)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      arbConst b - ε ≤ normBestAsymCos n (2 ^ b) := by
  let m : ℕ := 2 ^ (b - 1) - 1
  have hm : 1 ≤ m := by
    have hb1 : 1 ≤ b - 1 := by omega
    have hpow_ge : 2 ^ 1 ≤ 2 ^ (b - 1) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hb1
    dsimp [m]
    omega
  have hBlock_m := hBlock m hm ε hε
  filter_upwards [hBlock_m, Filter.eventually_ge_atTop (1 : ℕ)] with n hblock hn1
  have hnpos : 0 < n := Nat.succ_le_iff.mp hn1
  have hsubset :
      blockSymmAlphabet n m ⊆ blockExactAlphabet n b := by
    simpa [m] using blockSymmAlphabet_subset_blockExactAlphabet n b
  have halpha_mono :
      alpha_asym n (blockSymmAlphabet n m) ≤
        alpha_asym n (blockExactAlphabet n b) :=
    alpha_asym_mono_of_pos hnpos hsubset
  have hcard : (blockExactAlphabet n b).card = 2 ^ b :=
    blockExactAlphabet_card (n := n) (b := b) (by omega)
  have hbest :
      alpha_asym n (blockExactAlphabet n b) ≤ bestAsymCos n (2 ^ b) :=
    le_bestAsymCos_of_card hnpos hcard
  have hsqrt_nonneg : 0 ≤ Real.sqrt (H n) := Real.sqrt_nonneg _
  have hmul :
      Real.sqrt (H n) * alpha_asym n (blockSymmAlphabet n m) ≤
        Real.sqrt (H n) * bestAsymCos n (2 ^ b) :=
    mul_le_mul_of_nonneg_left (le_trans halpha_mono hbest) hsqrt_nonneg
  have hmain :
      2 * Real.sqrt (m : ℝ) - ε ≤
        Real.sqrt (H n) * bestAsymCos n (2 ^ b) :=
    le_trans hblock hmul
  simpa [arbConst, normBestAsymCos, m] using hmain

/-- The finite layer-cake constant for any valid total-bit FP split is bounded
by the closed-form FP constant. -/
theorem layerCakeConstant_fpDescending_le_fpConst {b t : ℕ}
    (hb : 2 ≤ b) (ht : t ∈ fpSplitIndices b) :
    layerCakeConstant
        (fpDescendingPositiveLevels (fpExponentBits b t) t) ≤
      fpConst b := by
  let e : ℕ := fpExponentBits b t
  have hsplit : e + t = b - 1 := by
    simpa [e] using fpExponentBits_add_t (b := b) (t := t) ht
  have hcard :
      floatPositiveCard e t = 2 ^ (b - 1) - 1 :=
    fpPositiveCard_total hsplit
  have hm : 1 ≤ floatPositiveCard e t := by
    rw [hcard]
    have hb1 : 1 ≤ b - 1 := by omega
    have hpow_ge : 2 ^ 1 ≤ 2 ^ (b - 1) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hb1
    omega
  have hconst :=
    layerCakeConstant_le_of_adjacent_ratio_two
      (m := floatPositiveCard e t) hm
      (c := fpDescendingPositiveLevels e t)
      (fpDescendingPositiveLevels_pos e t)
      (by
        intro j hj
        exact fpDescendingPositiveLevels_step_le_two e t hj)
  have hcard_plus :
      floatPositiveCard e t + 2 = 2 ^ (b - 1) + 1 := by
    omega
  calc
    layerCakeConstant (fpDescendingPositiveLevels (fpExponentBits b t) t)
        = layerCakeConstant (fpDescendingPositiveLevels e t) := by rfl
    _ ≤ 2 * Real.sqrt ((((floatPositiveCard e t + 2 : ℕ) : ℝ) / 3)) :=
        hconst
    _ = fpConst b := by
        simp [fpConst, hcard_plus]

/-- Per-split floating-point obstruction from layer-cake. -/
theorem normAlpha_fpSplit_le_fpConst {n b t : ℕ}
    (hn : 0 < n) (hb : 2 ≤ b) (ht : t ∈ fpSplitIndices b) :
    Real.sqrt (H n) *
        alpha_asym n (fpAlphabet (fpExponentBits b t) t) ≤
      fpConst b := by
  let e : ℕ := fpExponentBits b t
  have hsplit : e + t = b - 1 := by
    simpa [e] using fpExponentBits_add_t (b := b) (t := t) ht
  have hcard :
      floatPositiveCard e t = 2 ^ (b - 1) - 1 :=
    fpPositiveCard_total hsplit
  have hm : 1 ≤ floatPositiveCard e t := by
    rw [hcard]
    have hb1 : 1 ≤ b - 1 := by omega
    have hpow_ge : 2 ^ 1 ≤ 2 ^ (b - 1) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hb1
    omega
  have hLayer :=
    signSymmetricLayerCake_obstruction
      (n := n) (m := floatPositiveCard e t) hn hm
      (c := fpDescendingPositiveLevels e t)
      (fpDescendingPositiveLevels_pos e t)
      (fpDescendingPositiveLevels_desc e t)
  have hLayerFp :
      Real.sqrt (H n) * alpha_asym n (fpAlphabet e t) ≤
        layerCakeConstant (fpDescendingPositiveLevels e t) := by
    simpa [signedLevelsOfSeq_fpDescending_eq e t] using hLayer
  have hConst :=
    layerCakeConstant_fpDescending_le_fpConst (b := b) (t := t) hb ht
  simpa [e] using le_trans hLayerFp hConst

/-- Floating-point obstruction from the explicit layer-cake estimate and the
consecutive-ratio bound for total-bit splits with `e ≥ 1`. -/
theorem normBestFpCos_le_fpConst {n b : ℕ} (hn : 0 < n) (hb : 2 ≤ b) :
    normBestFpCos n b ≤ fpConst b := by
  have hsplit_nonempty : (fpSplitIndices b).Nonempty :=
    fpSplitIndices_nonempty hb
  have hHpos : 0 < H n := H_pos hn
  have hsqrtH_pos : 0 < Real.sqrt (H n) :=
    Real.sqrt_pos_of_pos hHpos
  unfold normBestFpCos bestFpCos
  rw [dif_pos hsplit_nonempty]
  have hsup_le :
      (fpSplitIndices b).sup' hsplit_nonempty
          (fun t => alpha_asym n (fpAlphabet (fpExponentBits b t) t)) ≤
        fpConst b / Real.sqrt (H n) := by
    rw [Finset.sup'_le_iff]
    intro t ht
    have hper := normAlpha_fpSplit_le_fpConst
      (n := n) (b := b) (t := t) hn hb ht
    exact (le_div_iff₀ hsqrtH_pos).2 (by simpa [mul_comm] using hper)
  calc
    Real.sqrt (H n) *
        (fpSplitIndices b).sup' hsplit_nonempty
          (fun t => alpha_asym n (fpAlphabet (fpExponentBits b t) t))
        ≤ Real.sqrt (H n) * (fpConst b / Real.sqrt (H n)) := by
          exact mul_le_mul_of_nonneg_left hsup_le hsqrtH_pos.le
    _ = fpConst b := by
          field_simp [hsqrtH_pos.ne']

/-- The two normalized constants are strictly separated for total bit-width
`b ≥ 3`. -/
theorem fpConst_lt_arbConst {b : ℕ} (hb : 3 ≤ b) :
    fpConst b < arbConst b := by
  have hb_exp : 2 ≤ b - 1 := by omega
  have hpow_ge : 2 ^ 2 ≤ 2 ^ (b - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hb_exp
  have hpow_ge4 : 4 ≤ 2 ^ (b - 1) := by
    simpa using hpow_ge
  have hpow_ge1 : 1 ≤ 2 ^ (b - 1) := by omega
  have hpow_ge4_real : (4 : ℝ) ≤ (2 ^ (b - 1) : ℕ) := by
    exact_mod_cast hpow_ge4
  have harg :
      (((2 ^ (b - 1) + 1 : ℕ) : ℝ) / 3) <
        ((2 ^ (b - 1) - 1 : ℕ) : ℝ) := by
    calc
      (((2 ^ (b - 1) + 1 : ℕ) : ℝ) / 3)
          = (((2 ^ (b - 1) : ℕ) : ℝ) + 1) / 3 := by norm_num
      _ < ((2 ^ (b - 1) : ℕ) : ℝ) - 1 := by
            nlinarith
      _ = ((2 ^ (b - 1) - 1 : ℕ) : ℝ) := by
            simp [Nat.cast_sub hpow_ge1]
  have hsqrt :
      Real.sqrt ((((2 ^ (b - 1) + 1 : ℕ) : ℝ) / 3)) <
        Real.sqrt (((2 ^ (b - 1) - 1 : ℕ) : ℝ)) :=
    Real.sqrt_lt_sqrt (by positivity) harg
  unfold fpConst arbConst
  exact mul_lt_mul_of_pos_left hsqrt (by norm_num)

/-- Conditional final normalized separation.  Once `BlockHardyLowerBound` is
proved, this immediately yields the unconditional theorem with the same
conclusion. -/
theorem eventually_normBestFpCos_lt_normBestAsymCos_of_blockHardy
    (hBlock : BlockHardyLowerBound) {b : ℕ} (hb : 3 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      normBestFpCos n b < normBestAsymCos n (2 ^ b) := by
  have hb2 : 2 ≤ b := le_trans (by norm_num : 2 ≤ 3) hb
  have hgap : fpConst b < arbConst b := fpConst_lt_arbConst hb
  let ε : ℝ := (arbConst b - fpConst b) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hAsym :=
    normBestAsymCos_ge_arbConst_sub_eps_of_blockHardy
      hBlock hb2 hε
  filter_upwards [hAsym, Filter.eventually_ge_atTop (1 : ℕ)] with n hAsymn hn1
  have hnpos : 0 < n := Nat.succ_le_iff.mp hn1
  have hFp := normBestFpCos_le_fpConst (n := n) (b := b) hnpos hb2
  have hmid : fpConst b < arbConst b - ε := by
    dsimp [ε]
    linarith
  exact lt_of_lt_of_le (lt_of_le_of_lt hFp hmid) hAsymn

/-- Final normalized separation between canonical floating-point alphabets and
arbitrary scalar alphabets with the same total bit budget. -/
theorem eventually_normBestFpCos_lt_normBestAsymCos
    {b : ℕ} (hb : 3 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      normBestFpCos n b < normBestAsymCos n (2 ^ b) :=
  eventually_normBestFpCos_lt_normBestAsymCos_of_blockHardy
    blockHardy_lower hb

end AsymmetricProduct
end OptimalAlphabets
