import Mathlib

/-!
# OptimalAlphabets.ScalarBaselines

Block-size-`1` scalar baselines, expressed inside the normalized log-shape
parameterization `SigmaBar k`.

Given any strictly increasing positive list of scalar magnitudes
`s₀ < s₁ < ... < s_{k-1}`, the product-code formalization only depends on the
corresponding normalized log alphabet

`Aᵢ = (log sᵢ - log s₀) / (log s_{k-1} - log s₀)`.

Important modeling note:
this module records only the normalized log-shape. The subtraction
`log sᵢ - log s₀` corresponds to removing a removable tensor-wide scale, but the
subsequent division by `log s_{k-1} - log s₀` also quotients out the total
log-span. That second step is not geometrically neutral. The span-aware
correction is formalized separately in `ScalarShapeSpan`.
-/

noncomputable section

namespace OptimalAlphabets

/-- The first index in `Fin k`, packaged using the standing hypothesis `2 ≤ k`. -/
def firstFin {k : ℕ} (hk : 2 ≤ k) : Fin k :=
  ⟨0, lt_of_lt_of_le (by norm_num) hk⟩

/-- The last index in `Fin k`, packaged using the standing hypothesis `2 ≤ k`. -/
def lastFin {k : ℕ} (hk : 2 ≤ k) : Fin k :=
  ⟨k - 1, Nat.sub_lt (by omega) (by norm_num)⟩

/-- The normalized log alphabet attached to a strictly increasing positive
sequence of scalar magnitudes. -/
def normalizedLogAlphabet {k : ℕ} (s : Fin k → ℝ) : Fin k → ℝ :=
  if hk : 2 ≤ k then
    fun i =>
      (Real.log (s i) - Real.log (s (firstFin hk))) /
        (Real.log (s (lastFin hk)) - Real.log (s (firstFin hk)))
  else
    0

@[simp] theorem normalizedLogAlphabet_apply {k : ℕ} (s : Fin k → ℝ)
    (hk : 2 ≤ k) (i : Fin k) :
    normalizedLogAlphabet s i =
      (Real.log (s i) - Real.log (s (firstFin hk))) /
        (Real.log (s (lastFin hk)) - Real.log (s (firstFin hk))) := by
  simp [normalizedLogAlphabet, hk]

/-- Number of positive finite values in a sign/exponent/mantissa format with
`q` exponent bits and `p` mantissa bits, assuming all nonzero signless codes are
finite. -/
def floatPositiveCard (q p : ℕ) : ℕ :=
  2 ^ (q + p) - 1

/-- Canonical positive finite values for a `q`/`p` binary float family.

We use a bias-`1` normalization:

* subnormals (`e = 0`) are `m / 2^p`, with `1 ≤ m < 2^p`;
* normals (`e > 0`) are `2^(e-1) * (1 + m / 2^p)`.

Changing the exponent bias would multiply every value by the same global
constant, so after `normalizedLogAlphabet` this canonical choice is equivalent
to the usual biased formats. In particular, `q = 2`, `p = 1` gives the project
baseline `NVFP4 = {0.5, 1, 1.5, 2, 3, 4, 6}`.
-/
def floatValueCodeCore (B e m : ℕ) : ℝ :=
  if e = 0 then
    (m : ℝ) / (B : ℝ)
  else
    (2 : ℝ) ^ (e - 1) * (1 + (m : ℝ) / (B : ℝ))

def floatValueCode (p : ℕ) (u : ℕ) : ℝ :=
  let B := 2 ^ p
  let e := u / B
  let m := u % B
  floatValueCodeCore B e m

@[simp] lemma floatValueCodeCore_zero (B m : ℕ) :
    floatValueCodeCore B 0 m = (m : ℝ) / (B : ℝ) := by
  simp [floatValueCodeCore]

lemma floatValueCodeCore_ne_zero (B e m : ℕ) (h : e ≠ 0) :
    floatValueCodeCore B e m =
      (2 : ℝ) ^ (e - 1) * (1 + (m : ℝ) / (B : ℝ)) := by
  simp [floatValueCodeCore, h]

/-- Increasing list of positive finite values for the `q`/`p` family. -/
def floatingPositiveLevels (q p : ℕ) : Fin (floatPositiveCard q p) → ℝ :=
  fun i => floatValueCode p (i.1 + 1)

lemma floatValueCode_pos (p : ℕ) {u : ℕ} (hu : 0 < u) :
    0 < floatValueCode p u := by
  set B : ℕ := 2 ^ p
  have hB_pos : 0 < B := by
    subst B
    exact pow_pos (by norm_num : 0 < 2) p
  set e : ℕ := u / B
  set m : ℕ := u % B
  have hrepr : floatValueCode p u = floatValueCodeCore B e m := by
    simp [floatValueCode, B, e, m]
  by_cases he0 : e = 0
  · have hdiv0 : u / B = 0 := by simpa [e] using he0
    have hu_lt_B : u < B := by
      exact (Nat.div_eq_zero_iff_lt hB_pos).mp hdiv0
    have hm_eq : m = u := by
      dsimp [m]
      exact Nat.mod_eq_of_lt hu_lt_B
    have hm_pos : 0 < m := by
      simpa [hm_eq] using hu
    have hcore : floatValueCodeCore B e m = (m : ℝ) / (B : ℝ) := by
      rw [he0]
      simp
    rw [hrepr, hcore]
    exact div_pos (by exact_mod_cast hm_pos) (by exact_mod_cast hB_pos)
  · rw [hrepr, floatValueCodeCore_ne_zero B e m he0]
    have hpow_pos : 0 < (2 : ℝ) ^ (e - 1) := by positivity
    have hfrac_nonneg : 0 ≤ (m : ℝ) / (B : ℝ) := by
      apply div_nonneg <;> positivity
    have hfac_pos : 0 < 1 + (m : ℝ) / (B : ℝ) := by
      linarith
    exact mul_pos hpow_pos hfac_pos

lemma floatValueCode_lt_succ (p : ℕ) {u : ℕ} (_hu : 0 < u) :
    floatValueCode p u < floatValueCode p (u + 1) := by
  set B : ℕ := 2 ^ p
  have hB_pos : 0 < B := by
    subst B
    exact pow_pos (by norm_num : 0 < 2) p
  have hB_pos_real : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast hB_pos
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
    have hrepr1 : floatValueCode p (u + 1) = floatValueCodeCore B e (m + 1) := by
      simp [floatValueCode, B, hdiv1, hmod1]
    by_cases he0 : e = 0
    · have hfrac :
          (m : ℝ) / (B : ℝ) < ((m + 1 : ℕ) : ℝ) / (B : ℝ) := by
        apply div_lt_div_of_pos_right
        · exact_mod_cast Nat.lt_succ_self m
        · exact hB_pos_real
      have hleft : floatValueCodeCore B e m = (m : ℝ) / (B : ℝ) := by
        rw [he0]
        simp
      have hright : floatValueCodeCore B e (m + 1) = ((m + 1 : ℕ) : ℝ) / (B : ℝ) := by
        rw [he0]
        simp
      rw [hrepr, hrepr1, hleft, hright]
      exact hfrac
    · have hpow_pos : 0 < (2 : ℝ) ^ (e - 1) := by positivity
      have hfrac :
          (m : ℝ) / (B : ℝ) < ((m + 1 : ℕ) : ℝ) / (B : ℝ) := by
        apply div_lt_div_of_pos_right
        · exact_mod_cast Nat.lt_succ_self m
        · exact hB_pos_real
      have hfac :
          1 + (m : ℝ) / (B : ℝ) < 1 + ((m + 1 : ℕ) : ℝ) / (B : ℝ) := by
        linarith
      have hmul :
          (2 : ℝ) ^ (e - 1) * (1 + (m : ℝ) / (B : ℝ)) <
            (2 : ℝ) ^ (e - 1) * (1 + ((m + 1 : ℕ) : ℝ) / (B : ℝ)) := by
        exact mul_lt_mul_of_pos_left hfac hpow_pos
      have hleft :
          floatValueCodeCore B e m =
            (2 : ℝ) ^ (e - 1) * (1 + (m : ℝ) / (B : ℝ)) := by
        exact floatValueCodeCore_ne_zero B e m he0
      have hright :
          floatValueCodeCore B e (m + 1) =
            (2 : ℝ) ^ (e - 1) * (1 + ((m + 1 : ℕ) : ℝ) / (B : ℝ)) := by
        exact floatValueCodeCore_ne_zero B e (m + 1) he0
      rw [hrepr, hrepr1, hleft, hright]
      exact hmul
  · have hm_last : m + 1 = B := by omega
    have hu1_repr : u + 1 = (e + 1) * B + 0 := by
      calc
        u + 1 = e * B + (m + 1) := by
          rw [hu_repr]
          omega
        _ = e * B + B := by rw [hm_last]
        _ = (e + 1) * B := by
          rw [Nat.add_mul, Nat.one_mul]
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
    have hrepr1 : floatValueCode p (u + 1) = floatValueCodeCore B (e + 1) 0 := by
      simp [floatValueCode, B, hdiv1, hmod1]
    by_cases he0 : e = 0
    · have hfrac_lt_one : (m : ℝ) / (B : ℝ) < 1 := by
        have hm_lt_real : (m : ℝ) < (B : ℝ) := by
          exact_mod_cast hm_lt
        have hm_lt_real' : (m : ℝ) < 1 * (B : ℝ) := by simpa using hm_lt_real
        exact (div_lt_iff₀ hB_pos_real).2 hm_lt_real'
      rw [hrepr, hrepr1]
      simp [floatValueCodeCore, he0]
      exact hfrac_lt_one
    · have hpow_pos : 0 < (2 : ℝ) ^ (e - 1) := by positivity
      have hfrac_lt_one : (m : ℝ) / (B : ℝ) < 1 := by
        have hm_lt_real : (m : ℝ) < (B : ℝ) := by
          exact_mod_cast hm_lt
        have hm_lt_real' : (m : ℝ) < 1 * (B : ℝ) := by simpa using hm_lt_real
        exact (div_lt_iff₀ hB_pos_real).2 hm_lt_real'
      have hfac : 1 + (m : ℝ) / (B : ℝ) < 2 := by
        linarith
      have hmul :
          (2 : ℝ) ^ (e - 1) * (1 + (m : ℝ) / (B : ℝ)) <
            (2 : ℝ) ^ (e - 1) * 2 := by
        exact mul_lt_mul_of_pos_left hfac hpow_pos
      have he_pos : 0 < e := Nat.pos_iff_ne_zero.mpr he0
      have hpow_step : (2 : ℝ) ^ (e - 1) * 2 = (2 : ℝ) ^ e := by
        calc
          (2 : ℝ) ^ (e - 1) * 2 = (2 : ℝ) ^ (e - 1) * (2 : ℝ) ^ 1 := by simp
          _ = (2 : ℝ) ^ ((e - 1) + 1) := by rw [← pow_add]
          _ = (2 : ℝ) ^ e := by rw [Nat.sub_add_cancel (Nat.succ_le_of_lt he_pos)]
      rw [hrepr, hrepr1]
      have hleft :
          floatValueCodeCore B e m =
            (2 : ℝ) ^ (e - 1) * (1 + (m : ℝ) / (B : ℝ)) := by
        simp [floatValueCodeCore, he0]
      have hright : floatValueCodeCore B (e + 1) 0 = (2 : ℝ) ^ e := by
        simp [floatValueCodeCore, he0]
      rw [hleft, hright]
      calc
        (2 : ℝ) ^ (e - 1) * (1 + (m : ℝ) / (B : ℝ)) < (2 : ℝ) ^ (e - 1) * 2 := hmul
        _ = (2 : ℝ) ^ e := hpow_step

lemma floatingPositiveLevels_pos (q p : ℕ) (i : Fin (floatPositiveCard q p)) :
    0 < floatingPositiveLevels q p i := by
  exact floatValueCode_pos p (Nat.succ_pos _)

lemma strictMono_floatingPositiveLevels (q p : ℕ) :
    StrictMono (floatingPositiveLevels q p) := by
  have hnat : StrictMono (fun n : ℕ => floatValueCode p (n + 1)) := by
    exact strictMono_nat_of_lt_succ (fun n => floatValueCode_lt_succ p (Nat.succ_pos _))
  intro i j hij
  have hij' : (i : ℕ) < (j : ℕ) := hij
  simpa [floatingPositiveLevels] using hnat hij'
end OptimalAlphabets
