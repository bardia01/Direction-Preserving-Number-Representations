import PaperProofs.Internal.OptimalAlphabets.SphericalRandomCovering
import PaperProofs.Internal.OptimalAlphabets.SphericalCapCovering
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# OptimalAlphabets.Wyner

Wyner's full spherical-cap covering asymptotic for the true covering number.

The main theorem is stated for the tail `n = k + 2`, matching the rest of the
project's convention for nonempty spheres and avoiding low-dimensional
edge cases in the asymptotic statement.
-/

noncomputable section

open Filter Topology Real Asymptotics
open scoped Topology

namespace OptimalAlphabets

private theorem sin_pos_of_theta
    {theta : ℝ} (htheta0 : 0 < theta) (htheta_pi2 : theta < Real.pi / 2) :
    0 < Real.sin theta := by
  exact Real.sin_pos_of_pos_of_lt_pi htheta0 (by linarith [htheta_pi2, Real.pi_pos])

private theorem sin_lt_one_of_theta
    {theta : ℝ} (htheta0 : 0 < theta) (htheta_pi2 : theta < Real.pi / 2) :
    Real.sin theta < 1 := by
  have hsin_lt :
      Real.sin theta < Real.sin (Real.pi / 2) := by
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [htheta0, Real.pi_pos])
      (by linarith) htheta_pi2
  simpa using hsin_lt

theorem coveringExponent_pos
    {theta : ℝ} (htheta0 : 0 < theta) (htheta_pi2 : theta < Real.pi / 2) :
    0 < coveringExponent theta := by
  have hsin0 := sin_pos_of_theta htheta0 htheta_pi2
  have hsin1 := sin_lt_one_of_theta htheta0 htheta_pi2
  have hlog_neg : Real.log (Real.sin theta) < 0 :=
    Real.log_neg hsin0 hsin1
  dsimp [coveringExponent]
  linarith

private def wynerLowerLogBound (theta : ℝ) (k : ℕ) : ℝ :=
  - (Real.log (((k + 1 : ℕ) : ℝ)) + Real.log theta +
      (k : ℝ) * Real.log (Real.sin theta)) / (((k + 2 : ℕ) : ℝ))

private theorem tendsto_log_nat_succ_div_nat_add_two :
    Tendsto
      (fun k : ℕ => Real.log (((k + 1 : ℕ) : ℝ)) / (((k + 2 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 1)) atTop (𝓝 0) := by
    simpa [pow_one, one_mul] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 1 1 one_ne_zero)
  have hsucc :
      Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  refine (hreal.comp hsucc).congr' ?_
  filter_upwards with k
  simp [pow_one, one_mul, Nat.cast_add, add_assoc]
  ring

private theorem tendsto_const_div_nat_add_two (A : ℝ) :
    Tendsto (fun k : ℕ => A / (((k + 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
  refine ((tendsto_const_div_atTop_nhds_zero_nat A).comp
      (tendsto_add_atTop_nat 2)).congr' ?_
  filter_upwards with k
  simp [Nat.cast_add]

private theorem wynerLowerLogBound_tendsto
    {theta : ℝ} (_htheta0 : 0 < theta) (_htheta_pi2 : theta < Real.pi / 2) :
    Tendsto (fun k : ℕ => wynerLowerLogBound theta k) atTop
      (𝓝 (coveringExponent theta)) := by
  let L : ℝ := Real.log (Real.sin theta)
  have hlog :
      Tendsto
        (fun k : ℕ =>
          Real.log (((k + 1 : ℕ) : ℝ)) / (((k + 2 : ℕ) : ℝ)))
        atTop (𝓝 0) :=
    tendsto_log_nat_succ_div_nat_add_two
  have htheta :
      Tendsto
        (fun k : ℕ => Real.log theta / (((k + 2 : ℕ) : ℝ)))
        atTop (𝓝 0) :=
    tendsto_const_div_nat_add_two _
  have hkdiv :
      Tendsto (fun k : ℕ => (k : ℝ) / (((k + 2 : ℕ) : ℝ))) atTop (𝓝 1) := by
    refine (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 2).congr' ?_
    filter_upwards with k
    simp [Nat.cast_add]
  have hmain :
      Tendsto
        (fun k : ℕ => ((k : ℝ) / (((k + 2 : ℕ) : ℝ))) * L)
        atTop (𝓝 L) := by
    simpa using hkdiv.mul (tendsto_const_nhds (x := L))
  have hsplit :
      Tendsto
        (fun k : ℕ =>
          - (Real.log (((k + 1 : ℕ) : ℝ)) / (((k + 2 : ℕ) : ℝ))) -
            Real.log theta / (((k + 2 : ℕ) : ℝ)) -
              ((k : ℝ) / (((k + 2 : ℕ) : ℝ))) * L)
        atTop (𝓝 (-L)) := by
    simpa using (hlog.neg.sub htheta).sub hmain
  have hsplit' :
      Tendsto (fun k : ℕ => wynerLowerLogBound theta k) atTop (𝓝 (-L)) := by
    refine hsplit.congr' ?_
    filter_upwards with k
    have hden : (((k + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
    dsimp [wynerLowerLogBound, L]
    field_simp [hden]
    ring
  simpa [coveringExponent, L] using hsplit'

private theorem wynerLowerLogBound_le_log_coveringNumber
    {theta : ℝ} (htheta0 : 0 < theta) (htheta_pi2 : theta < Real.pi / 2)
    (k : ℕ) :
    wynerLowerLogBound theta k ≤
      Real.log ((sphericalCapCoveringNumber (k + 2) theta : ℝ)) /
        (((k + 2 : ℕ) : ℝ)) := by
  let s : ℝ := Real.sin theta
  let M : ℕ := sphericalCapCoveringNumber (k + 2) theta
  let U : ℝ := ((k + 1 : ℕ) : ℝ) * theta * s ^ k
  have hn : 2 ≤ k + 2 := by omega
  have htheta_pi : theta < Real.pi := by linarith [htheta_pi2, Real.pi_pos]
  have hMpos_nat : 0 < M :=
    sphericalCapCoveringNumber_pos (n := k + 2) hn htheta0 htheta_pi
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hMpos_nat
  have hs0 : 0 < s := by
    dsimp [s]
    exact sin_pos_of_theta htheta0 htheta_pi2
  have hUpos : 0 < U := by
    dsimp [U]
    positivity
  have hcap_upper :
      capMeasure (k + 2) theta ≤ U := by
    have h := capMeasure_upper_bound (n := k + 2) hn htheta0 htheta_pi2
    have hk1 : k + 2 - 1 = k + 1 := by omega
    have hk2 : k + 2 - 2 = k := by omega
    have hcoef : ((k : ℝ) + 2 - 1) = (((k + 1 : ℕ) : ℝ)) := by
      norm_num [Nat.cast_add]
      ring
    simpa [U, s, hk1, hk2, Nat.cast_add, hcoef] using h
  have hmeasure :
      1 ≤ (M : ℝ) * capMeasure (k + 2) theta := by
    simpa [M] using
      one_le_sphericalCapCoveringNumber_mul_capMeasure
        (n := k + 2) hn htheta0 htheta_pi2.le
  have hMU : 1 ≤ (M : ℝ) * U := by
    exact hmeasure.trans
      (mul_le_mul_of_nonneg_left hcap_upper (show 0 ≤ (M : ℝ) by positivity))
  have hinv_le_M : U⁻¹ ≤ (M : ℝ) := by
    exact (inv_le_iff_one_le_mul₀ hUpos).2 hMU
  have hlog_lower : Real.log U⁻¹ ≤ Real.log (M : ℝ) :=
    Real.log_le_log (inv_pos.mpr hUpos) hinv_le_M
  have hlogU :
      Real.log U =
        Real.log (((k + 1 : ℕ) : ℝ)) + Real.log theta +
          (k : ℝ) * Real.log s := by
    have hk1_ne : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have htheta_ne : theta ≠ 0 := htheta0.ne'
    have hs_ne : s ≠ 0 := hs0.ne'
    have hleft_ne : (((k + 1 : ℕ) : ℝ) * theta) ≠ 0 :=
      mul_ne_zero hk1_ne htheta_ne
    dsimp [U]
    rw [Real.log_mul hleft_ne (pow_ne_zero k hs_ne),
      Real.log_mul hk1_ne htheta_ne, Real.log_pow]
  have hden_pos : 0 < (((k + 2 : ℕ) : ℝ)) := by positivity
  have hbound :
      - Real.log U / (((k + 2 : ℕ) : ℝ)) ≤
        Real.log (M : ℝ) / (((k + 2 : ℕ) : ℝ)) := by
    have hlog_lower' : - Real.log U ≤ Real.log (M : ℝ) := by
      simpa [Real.log_inv] using hlog_lower
    exact div_le_div_of_nonneg_right hlog_lower' hden_pos.le
  have hrewrite :
      - Real.log U / (((k + 2 : ℕ) : ℝ)) = wynerLowerLogBound theta k := by
    rw [hlogU]
    dsimp [wynerLowerLogBound, s]
  have hbound' := hbound
  rw [hrewrite] at hbound'
  simpa [M] using hbound'

theorem eventually_sphericalCapCoveringNumber_le_floor_exp_of_gt
    {theta p : ℝ} (htheta0 : 0 < theta) (htheta_pi2 : theta < Real.pi / 2)
    (hp : coveringExponent theta < p) :
    ∀ᶠ n : ℕ in atTop,
      sphericalCapCoveringNumber n theta ≤ ⌊(Real.exp p) ^ n⌋₊ := by
  have hRc_pos := coveringExponent_pos htheta0 htheta_pi2
  have hp_pos : 0 < p := lt_trans hRc_pos hp
  have hsin0 := sin_pos_of_theta htheta0 htheta_pi2
  have hmul : 1 < Real.exp p * Real.sin theta := by
    have harg : 0 < p + Real.log (Real.sin theta) := by
      dsimp [coveringExponent] at hp
      linarith
    calc
      1 = Real.exp 0 := by rw [Real.exp_zero]
      _ < Real.exp (p + Real.log (Real.sin theta)) := by
            exact Real.exp_strictMono harg
      _ = Real.exp p * Real.sin theta := by
            rw [Real.exp_add, Real.exp_log hsin0]
  rcases eventual_sphericalCapCover_card_le_floor_of_mul_sin_gt_one
      (lam := Real.exp p) (theta := theta)
      (by simpa [Real.one_lt_exp_iff] using hp_pos)
      htheta0 htheta_pi2 hmul with ⟨N, -, hN⟩
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  rcases hN n hn with ⟨C, hCcard, hCcover⟩
  exact (sphericalCapCoveringNumber_le_of_cover hCcover).trans hCcard

private theorem eventually_log_coveringNumber_div_le_of_gt
    {theta p : ℝ} (htheta0 : 0 < theta) (htheta_pi2 : theta < Real.pi / 2)
    (hp : coveringExponent theta < p) :
    ∀ᶠ k : ℕ in atTop,
      Real.log ((sphericalCapCoveringNumber (k + 2) theta : ℝ)) /
          (((k + 2 : ℕ) : ℝ)) ≤ p := by
  have hupper :=
    eventually_sphericalCapCoveringNumber_le_floor_exp_of_gt htheta0 htheta_pi2 hp
  have hupper_shift :
      ∀ᶠ k : ℕ in atTop,
        sphericalCapCoveringNumber (k + 2) theta ≤
          ⌊(Real.exp p) ^ (k + 2)⌋₊ :=
    (tendsto_add_atTop_nat 2).eventually hupper
  filter_upwards [hupper_shift] with k hk
  let M : ℕ := sphericalCapCoveringNumber (k + 2) theta
  have hn : 2 ≤ k + 2 := by omega
  have htheta_pi : theta < Real.pi := by linarith [htheta_pi2, Real.pi_pos]
  have hMpos_nat : 0 < M :=
    sphericalCapCoveringNumber_pos (n := k + 2) hn htheta0 htheta_pi
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hMpos_nat
  have hfloor_le :
      ((⌊(Real.exp p) ^ (k + 2)⌋₊ : ℕ) : ℝ) ≤ (Real.exp p) ^ (k + 2) :=
    Nat.floor_le (pow_nonneg (Real.exp_pos p).le (k + 2))
  have hM_le_exp : (M : ℝ) ≤ (Real.exp p) ^ (k + 2) := by
    exact (show (M : ℝ) ≤ ((⌊(Real.exp p) ^ (k + 2)⌋₊ : ℕ) : ℝ) by
      exact_mod_cast hk).trans hfloor_le
  have hlog_le :
      Real.log (M : ℝ) ≤ Real.log ((Real.exp p) ^ (k + 2)) :=
    Real.log_le_log hMpos hM_le_exp
  have hlog_exp :
      Real.log ((Real.exp p) ^ (k + 2)) = (((k + 2 : ℕ) : ℝ)) * p := by
    rw [← Real.exp_nat_mul, Real.log_exp]
  have hden_pos : 0 < (((k + 2 : ℕ) : ℝ)) := by positivity
  calc
    Real.log (M : ℝ) / (((k + 2 : ℕ) : ℝ))
      ≤ Real.log ((Real.exp p) ^ (k + 2)) / (((k + 2 : ℕ) : ℝ)) := by
          exact div_le_div_of_nonneg_right hlog_le hden_pos.le
    _ = p := by
          rw [hlog_exp]
          field_simp [hden_pos.ne']

/-- Wyner's full asymptotic theorem for the normalized logarithm of the true
spherical-cap covering number. -/
theorem wyner_sphericalCapCoveringNumber_log_limit
    {theta : ℝ} (htheta0 : 0 < theta) (htheta_pi2 : theta < Real.pi / 2) :
    Tendsto
      (fun k : ℕ =>
        Real.log ((sphericalCapCoveringNumber (k + 2) theta : ℝ)) /
          (((k + 2 : ℕ) : ℝ)))
      atTop (𝓝 (coveringExponent theta)) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hlow_tendsto := wynerLowerLogBound_tendsto htheta0 htheta_pi2
  have hlow_event :
      ∀ᶠ k : ℕ in atTop,
        coveringExponent theta - ε / 2 ≤ wynerLowerLogBound theta k := by
    exact (hlow_tendsto.eventually
      (Ici_mem_nhds (by linarith : coveringExponent theta - ε / 2 <
        coveringExponent theta)))
  have hlow_bound :
      ∀ᶠ k : ℕ in atTop,
        wynerLowerLogBound theta k ≤
          Real.log ((sphericalCapCoveringNumber (k + 2) theta : ℝ)) /
            (((k + 2 : ℕ) : ℝ)) :=
    Eventually.of_forall
      (wynerLowerLogBound_le_log_coveringNumber htheta0 htheta_pi2)
  have hupper_event :=
    eventually_log_coveringNumber_div_le_of_gt
      htheta0 htheta_pi2
      (by linarith : coveringExponent theta < coveringExponent theta + ε / 2)
  have hevent :
      ∀ᶠ k : ℕ in atTop,
        dist
          (Real.log ((sphericalCapCoveringNumber (k + 2) theta : ℝ)) /
            (((k + 2 : ℕ) : ℝ)))
          (coveringExponent theta) < ε := by
    filter_upwards [hlow_event, hlow_bound, hupper_event] with k hlow hlowb hup
    rw [Real.dist_eq]
    have hleft :
        coveringExponent theta - ε <
          Real.log ((sphericalCapCoveringNumber (k + 2) theta : ℝ)) /
            (((k + 2 : ℕ) : ℝ)) := by
      linarith
    have hright :
        Real.log ((sphericalCapCoveringNumber (k + 2) theta : ℝ)) /
            (((k + 2 : ℕ) : ℝ)) <
          coveringExponent theta + ε := by
      linarith
    exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  exact Filter.eventually_atTop.1 hevent

/-- Little-o restatement of Wyner's theorem on the logarithmic scale. -/
theorem wyner_sphericalCapCoveringNumber_log_error_isLittleO
    {theta : ℝ} (htheta0 : 0 < theta) (htheta_pi2 : theta < Real.pi / 2) :
    (fun k : ℕ =>
        Real.log ((sphericalCapCoveringNumber (k + 2) theta : ℝ)) -
          (((k + 2 : ℕ) : ℝ) * coveringExponent theta))
      =o[atTop] (fun k : ℕ => (((k + 2 : ℕ) : ℝ))) := by
  have hlim := wyner_sphericalCapCoveringNumber_log_limit htheta0 htheta_pi2
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have hsub :
        Tendsto
          (fun k : ℕ =>
            Real.log ((sphericalCapCoveringNumber (k + 2) theta : ℝ)) /
                (((k + 2 : ℕ) : ℝ)) -
              coveringExponent theta)
          atTop (𝓝 0) :=
        tendsto_sub_nhds_zero_iff.mpr hlim
    refine (tendsto_congr' ?_).mpr hsub
    filter_upwards with k
    have hden : (((k + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hden, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  · filter_upwards with k
    intro hk
    have hden : (((k + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
    exact (hden hk).elim

end OptimalAlphabets
