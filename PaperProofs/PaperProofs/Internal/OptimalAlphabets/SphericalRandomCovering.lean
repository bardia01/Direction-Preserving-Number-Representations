import PaperProofs.Internal.OptimalAlphabets.SphericalAsymptotic
import PaperProofs.Internal.OptimalAlphabets.SphericalNets
import PaperProofs.Internal.OptimalAlphabets.SphericalCapCovering
import PaperProofs.Internal.OptimalAlphabets.SphericalCapMeasure.UniformLowerBound
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# OptimalAlphabets.SphericalRandomCovering

An asymptotic random-covering upper bound for unconstrained spherical codes.
-/

noncomputable section

open Set Filter Topology Real Metric MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace OptimalAlphabets

private theorem capMeasure_le_one
    (n : ℕ) (hn : 2 ≤ n) (v : SpherePoint n) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    capMeasure n a ≤ 1 := by
  have hn0 : 0 < n := by omega
  calc
    capMeasure n a
      = ((sphereProbabilityMeasure n hn0 : Measure (SpherePoint n)).real (capAround v a)) := by
          symm
          exact sphereProbabilityMeasure_real_capAround_eq_capMeasure hn v ha0 hapi
    _ ≤ ((sphereProbabilityMeasure n hn0 : Measure (SpherePoint n)).real Set.univ) := by
          exact MeasureTheory.measureReal_mono (by simp)
    _ = 1 := by simp [Measure.real_def]

private theorem badEvent_real_eq_pow
    {n M : ℕ} (hn : 2 ≤ n) (v : SpherePoint n) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    let μ := sphereProbabilityMeasure n (show 0 < n by omega)
    let Ωμ : ProbabilityMeasure (Fin M → SpherePoint n) := ProbabilityMeasure.pi (fun _ : Fin M => μ)
    let bad : Set (Fin M → SpherePoint n) := Set.pi Set.univ (fun _ : Fin M => (capAround v a)ᶜ)
    ((Ωμ : Measure (Fin M → SpherePoint n)).real bad) = (1 - capMeasure n a) ^ M := by
  have hn0 : 0 < n := by omega
  let μ := sphereProbabilityMeasure n hn0
  let Ωμ : ProbabilityMeasure (Fin M → SpherePoint n) := ProbabilityMeasure.pi (fun _ : Fin M => μ)
  let bad : Set (Fin M → SpherePoint n) := Set.pi Set.univ (fun _ : Fin M => (capAround v a)ᶜ)
  have hfactor :
      ((μ : Measure (SpherePoint n)).real ((capAround v a)ᶜ)) = 1 - capMeasure n a := by
    rw [MeasureTheory.probReal_compl_eq_one_sub
      (μ := (μ : Measure (SpherePoint n))) (measurableSet_capAround v ha0 hapi)]
    rw [sphereProbabilityMeasure_real_capAround_eq_capMeasure hn v ha0 hapi]
  have hpi :
      Ωμ bad = ∏ i : Fin M, μ ((capAround v a)ᶜ) := by
    exact (ProbabilityMeasure.pi_pi (μ := fun _ : Fin M => μ)
      (s := fun _ : Fin M => (capAround v a)ᶜ))
  calc
    ((Ωμ : Measure (Fin M → SpherePoint n)).real bad)
      = (Ωμ bad : ℝ) := by simp
    _ = ((∏ i : Fin M, μ ((capAround v a)ᶜ)) : ℝ) := by
          simpa using congrArg (fun t : ℝ≥0 => (t : ℝ)) hpi
    _ = ∏ i : Fin M, (μ ((capAround v a)ᶜ) : ℝ) := by
          simp
    _ = ∏ i : Fin M, ((μ : Measure (SpherePoint n)).real ((capAround v a)ᶜ)) := by
          simp
    _ = (1 - capMeasure n a) ^ M := by
          have hfactor' :
              ((μ : Measure (SpherePoint n)).real ((capAround v a)ᶜ)) = 1 - capMeasure n a := hfactor
          simpa [Finset.prod_const] using congrArg (fun x : ℝ => x ^ M) hfactor'

private theorem badEvent_real_le_exp_neg
    {n M : ℕ} (hn : 2 ≤ n) (hM : 0 < M) (v : SpherePoint n) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    let μ := sphereProbabilityMeasure n (show 0 < n by omega)
    let Ωμ : ProbabilityMeasure (Fin M → SpherePoint n) := ProbabilityMeasure.pi (fun _ : Fin M => μ)
    let bad : Set (Fin M → SpherePoint n) := Set.pi Set.univ (fun _ : Fin M => (capAround v a)ᶜ)
    ((Ωμ : Measure (Fin M → SpherePoint n)).real bad) ≤
      Real.exp (-(M : ℝ) * capMeasure n a) := by
  have hp_nonneg : 0 ≤ capMeasure n a := by
    have hn0 : 0 < n := by omega
    calc
      0 ≤ ((sphereProbabilityMeasure n hn0 : Measure (SpherePoint n)).real (capAround v a)) := by
            positivity
      _ = capMeasure n a := by
            exact sphereProbabilityMeasure_real_capAround_eq_capMeasure hn v ha0 hapi
  have hp_le_one : capMeasure n a ≤ 1 := capMeasure_le_one n hn v ha0 hapi
  have hpow :
      (1 - capMeasure n a) ^ M ≤ Real.exp (-(M : ℝ) * capMeasure n a) := by
    have ht : capMeasure n a * M ≤ M := by
      have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
      nlinarith
    have hM0 : (M : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hM
    calc
      (1 - capMeasure n a) ^ M
        = (1 - (capMeasure n a * M) / M) ^ M := by
            congr 1
            field_simp [hM0]
      _ ≤ Real.exp (-(capMeasure n a * M)) :=
            Real.one_sub_div_pow_le_exp_neg (n := M) (t := capMeasure n a * M) ht
      _ = Real.exp (-(M : ℝ) * capMeasure n a) := by ring_nf
  simpa using (badEvent_real_eq_pow (n := n) (M := M) hn v ha0 hapi).trans_le hpow

private theorem eventually_pow_mul_exp_neg_pow_lt_one
    {A c γ : ℝ} (hA : 1 < A) (hc : 0 < c) (hγ : 1 < γ) :
    ∃ N : ℕ, ∀ n, N ≤ n → A ^ n * Real.exp (-c * γ ^ n) < 1 := by
  have hlogA : 0 < Real.log A := Real.log_pos hA
  have hdiv_tendsto :
      Tendsto (fun n : ℕ => (n : ℝ) / γ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 1 hγ)
  have hsmall :
      ∀ᶠ n : ℕ in atTop, (n : ℝ) / γ ^ n < c / Real.log A := by
    exact hdiv_tendsto.eventually (gt_mem_nhds (show 0 < c / Real.log A by positivity))
  rcases Filter.eventually_atTop.1 hsmall with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hratio : (n : ℝ) / γ ^ n < c / Real.log A := hN n hn
  have hγpow_pos : 0 < γ ^ n := pow_pos (lt_trans zero_lt_one hγ) n
  have hn_lt : (n : ℝ) < (c / Real.log A) * γ ^ n := by
    exact (div_lt_iff₀ hγpow_pos).1 hratio
  have hnlog_lt :
      (n : ℝ) * Real.log A < c * γ ^ n := by
    have hmul := mul_lt_mul_of_pos_right hn_lt hlogA
    have hright :
        ((c / Real.log A) * γ ^ n) * Real.log A = c * γ ^ n := by
      field_simp [hlogA.ne']
    rwa [hright] at hmul
  have hexponent_lt : (n : ℝ) * Real.log A - c * γ ^ n < 0 := by
    linarith
  have hAexp : A ^ n = Real.exp ((n : ℝ) * Real.log A) := by
    calc
      A ^ n = (Real.exp (Real.log A)) ^ n := by rw [Real.exp_log (lt_trans zero_lt_one hA)]
      _ = Real.exp ((n : ℝ) * Real.log A) := by rw [← Real.exp_nat_mul]
  calc
    A ^ n * Real.exp (-c * γ ^ n)
      = Real.exp ((n : ℝ) * Real.log A) * Real.exp (-c * γ ^ n) := by rw [hAexp]
    _ = Real.exp ((n : ℝ) * Real.log A + -(c * γ ^ n)) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ = Real.exp ((n : ℝ) * Real.log A - c * γ ^ n) := by rw [sub_eq_add_neg]
    _ < 1 := by exact Real.exp_lt_one_iff.mpr hexponent_lt

/-- Random-covering upper bound, returning the finite cap cover constructed by the
probabilistic argument.

This is the witness-bearing version of
`eventualSphericalUpperBoundAt_of_mul_sin_gt_one`; the older theorem below is
kept unchanged as the downstream `rho_sph` API. -/
theorem eventual_sphericalCapCover_card_le_floor_of_mul_sin_gt_one
    {lam theta : ℝ}
    (hlam1 : 1 < lam)
    (htheta0 : 0 < theta)
    (htheta_pi2 : theta < Real.pi / 2)
    (hmul : 1 < lam * Real.sin theta) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n, N ≤ n →
      ∃ C : Finset (SpherePoint n),
        C.card ≤ ⌊lam ^ n⌋₊ ∧ SphericalCapCover n theta C := by
  let f : ℝ → ℝ := fun t => lam * Real.sin (theta - t)
  have hfcont : Continuous f := by
    fun_prop
  have hnhds : {t : ℝ | 1 < f t} ∈ 𝓝 (0 : ℝ) := by
    apply (isOpen_lt continuous_const hfcont).mem_nhds
    simpa [f] using hmul
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr_pos, hr_sub⟩
  let η : ℝ := min (r / 2) (theta / 2)
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hη_lt_theta : η < theta := by
    have : η ≤ theta / 2 := by
      dsimp [η]
      exact min_le_right _ _
    linarith
  have hη_mem : η ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hη_pos.le]
    dsimp [η]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hmargin : 1 < lam * Real.sin (theta - η) := by
    exact hr_sub hη_mem

  let ε : ℝ := η / 2
  let a : ℝ := theta - ε
  let γ : ℝ := lam * Real.sin (a - ε)

  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  have hε_lt_theta : ε < theta := by
    dsimp [ε]
    linarith
  have hε_le_one : ε ≤ 1 := by
    have : ε < 1 := by
      dsimp [ε]
      linarith [hη_lt_theta, htheta_pi2, Real.pi_lt_four]
    linarith
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have ha_pi2 : a < Real.pi / 2 := by
    dsimp [a]
    linarith
  have hε_lt_a : ε < a := by
    dsimp [a, ε]
    linarith
  have hgamma : 1 < γ := by
    have hrewrite : a - ε = theta - η := by
      dsimp [a, ε]
      ring
    simpa [γ, hrewrite] using hmargin

  have hA : 1 < 5 / ε := by
    have hfive : ε < 5 := by linarith
    exact (one_lt_div hε_pos).2 hfive
  have hd : 0 < ε / (2 * Real.pi) := by
    positivity
  obtain ⟨Nexp, hNexp⟩ :=
    eventually_pow_mul_exp_neg_pow_lt_one hA hd hgamma

  have hpow_lam : Tendsto (fun n : ℕ => lam ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hlam1
  have hlarge :
      ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ lam ^ n := hpow_lam.eventually_ge_atTop 2
  rcases Filter.eventually_atTop.1 hlarge with ⟨Nfloor, hNfloor⟩

  refine ⟨max (max Nexp Nfloor) 2, by omega, ?_⟩
  intro n hn
  have hn_exp : Nexp ≤ n := by omega
  have hn_floor : Nfloor ≤ n := by omega
  have hn_two : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega

  let Nnet : Finset (SpherePoint n) :=
    Classical.choose (exists_finset_card_le_and_angle_cover n hε_pos hε_le_one)
  have hNnet_cover :
      ∀ u : SpherePoint n, ∃ v ∈ Nnet, InnerProductGeometry.angle u.1 v.1 ≤ ε := by
    exact (Classical.choose_spec (exists_finset_card_le_and_angle_cover n hε_pos hε_le_one)).1
  have hNnet_card : (Nnet.card : ℝ) ≤ (5 / ε) ^ n := by
    exact (Classical.choose_spec (exists_finset_card_le_and_angle_cover n hε_pos hε_le_one)).2

  let M : ℕ := ⌊lam ^ n⌋₊
  have hpow_ge_two : (2 : ℝ) ≤ lam ^ n := hNfloor n hn_floor
  have hM_half : lam ^ n / 2 ≤ (M : ℝ) := by
    have hfloor : lam ^ n - 1 < (M : ℝ) := by
      exact Nat.sub_one_lt_floor (a := lam ^ n)
    nlinarith
  have hM_pos : 0 < M := by
    have : (0 : ℝ) < (M : ℝ) := by
      nlinarith [hM_half, hpow_ge_two]
    exact_mod_cast this

  let μn : ProbabilityMeasure (SpherePoint n) := sphereProbabilityMeasure n hn0
  let Ωμ : ProbabilityMeasure (Fin M → SpherePoint n) := ProbabilityMeasure.pi (fun _ : Fin M => μn)
  let bad : SpherePoint n → Set (Fin M → SpherePoint n) :=
    fun v => Set.pi Set.univ (fun _ : Fin M => (capAround v a)ᶜ)
  let badUnion : Set (Fin M → SpherePoint n) := ⋃ v ∈ Nnet, bad v

  have hcap_lb :
      (ε / Real.pi) * Real.sin (a - ε) ^ n ≤ capMeasure n a :=
    capMeasure_uniform_lower_bound n hn_two a ε ha_pos ha_pi2 hε_pos hε_lt_a
  have hs_nonneg : 0 ≤ Real.sin (a - ε) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor
    · linarith
    · linarith [Real.pi_pos, ha_pi2]
  have hfac_nonneg : 0 ≤ (ε / Real.pi) * Real.sin (a - ε) ^ n := by
    refine mul_nonneg (div_nonneg hε_pos.le Real.pi_pos.le) ?_
    exact pow_nonneg hs_nonneg n
  have hMcap :
      (ε / (2 * Real.pi)) * γ ^ n ≤ (M : ℝ) * capMeasure n a := by
    calc
      (ε / (2 * Real.pi)) * γ ^ n
        = (lam ^ n / 2) * ((ε / Real.pi) * Real.sin (a - ε) ^ n) := by
            dsimp [γ]
            rw [mul_pow]
            field_simp [Real.pi_ne_zero]
      _ ≤ (M : ℝ) * ((ε / Real.pi) * Real.sin (a - ε) ^ n) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_right hM_half hfac_nonneg
      _ ≤ (M : ℝ) * capMeasure n a := by
            exact mul_le_mul_of_nonneg_left hcap_lb (by positivity)

  have hbad_each :
      ∀ v : SpherePoint n,
        ((Ωμ : Measure (Fin M → SpherePoint n)).real (bad v)) ≤
          Real.exp (-(ε / (2 * Real.pi)) * γ ^ n) := by
    intro v
    have hbad0 :
        ((Ωμ : Measure (Fin M → SpherePoint n)).real (bad v)) ≤
          Real.exp (-(M : ℝ) * capMeasure n a) := by
      simpa [Ωμ, bad] using
        badEvent_real_le_exp_neg (n := n) (M := M) hn_two hM_pos v ha_pos.le ha_pi2.le
    refine le_trans hbad0 ?_
    have hexp_arg :
        -(M : ℝ) * capMeasure n a ≤ -(ε / (2 * Real.pi)) * γ ^ n := by
      linarith
    exact Real.exp_le_exp.mpr hexp_arg

  have hunion :
      ((Ωμ : Measure (Fin M → SpherePoint n)).real badUnion) ≤
        (Nnet.card : ℝ) * Real.exp (-(ε / (2 * Real.pi)) * γ ^ n) := by
    calc
      ((Ωμ : Measure (Fin M → SpherePoint n)).real badUnion)
        ≤ ∑ v ∈ Nnet, ((Ωμ : Measure (Fin M → SpherePoint n)).real (bad v)) := by
            simpa [badUnion] using
              MeasureTheory.measureReal_biUnion_finset_le
                (μ := (Ωμ : Measure (Fin M → SpherePoint n))) Nnet bad
      _ ≤ ∑ v ∈ Nnet, Real.exp (-(ε / (2 * Real.pi)) * γ ^ n) := by
            exact Finset.sum_le_sum (fun v hv => hbad_each v)
      _ = (Nnet.card : ℝ) * Real.exp (-(ε / (2 * Real.pi)) * γ ^ n) := by
            simp [Finset.sum_const, nsmul_eq_mul]

  have hbad_lt_one :
      ((Ωμ : Measure (Fin M → SpherePoint n)).real badUnion) < 1 := by
    have hmul_le :
        (Nnet.card : ℝ) * Real.exp (-(ε / (2 * Real.pi)) * γ ^ n) ≤
          (5 / ε) ^ n * Real.exp (-(ε / (2 * Real.pi)) * γ ^ n) := by
      exact mul_le_mul_of_nonneg_right hNnet_card (by positivity)
    exact lt_of_le_of_lt (le_trans hunion hmul_le) (by simpa [γ] using hNexp n hn_exp)

  have hnotall : ¬ ∀ ω : Fin M → SpherePoint n, ω ∈ badUnion := by
    intro hall
    have hEq : badUnion = Set.univ := Set.eq_univ_iff_forall.mpr hall
    have hreal_univ :
        ((Ωμ : Measure (Fin M → SpherePoint n)).real Set.univ) = 1 := by
      simp [Measure.real_def]
    have hbad_eq_one :
        ((Ωμ : Measure (Fin M → SpherePoint n)).real badUnion) = 1 := by
      rw [hEq]
      exact hreal_univ
    linarith
  rcases not_forall.mp hnotall with ⟨ω, hω⟩

  let C : Finset (SpherePoint n) := Finset.univ.image ω
  have hCcard : C.card ≤ M := by
    simpa [C] using (Finset.card_image_le (s := Finset.univ) (f := ω))
  have hnet_hit :
      ∀ v ∈ Nnet, ∃ i : Fin M, ω i ∈ capAround v a := by
    intro v hv
    have hnotbad : ω ∉ bad v := by
      intro hbad
      exact hω <| by
        exact mem_iUnion.2 ⟨v, mem_iUnion.2 ⟨hv, hbad⟩⟩
    have hnotforall : ¬ ∀ i : Fin M, ω i ∈ (capAround v a)ᶜ := by
      simpa [bad, Set.mem_pi, Set.mem_univ] using hnotbad
    push_neg at hnotforall
    simpa using hnotforall

  have hcover : SphericalCapCover n theta C := by
    intro u
    rcases hNnet_cover u with ⟨v, hv, huv⟩
    rcases hnet_hit v hv with ⟨i, hi⟩
    have hci : ω i ∈ C := by
      exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
    have hvu : InnerProductGeometry.angle v.1 (ω i).1 ≤ a := by
      simpa [InnerProductGeometry.angle_comm] using hi
    have huc : InnerProductGeometry.angle u.1 (ω i).1 ≤ theta := by
      calc
        InnerProductGeometry.angle u.1 (ω i).1
          ≤ InnerProductGeometry.angle u.1 v.1 + InnerProductGeometry.angle v.1 (ω i).1 := by
              exact InnerProductGeometry.angle_le_angle_add_angle u.1 v.1 (ω i).1
        _ ≤ ε + a := by gcongr
        _ = theta := by
              dsimp [a]
              ring
    exact ⟨ω i, hci, huc⟩

  exact ⟨C, hCcard, hcover⟩

/-- Random-covering upper bound, packaged in the exact form needed by the
product-vs-spherical comparison.

If `1 < λ * sin θ`, then eventually `⌊λ^n⌋` unconstrained spherical code
points suffice to achieve covering radius at most `θ`. -/
theorem eventualSphericalUpperBoundAt_of_mul_sin_gt_one
    {lam theta : ℝ}
    (hlam1 : 1 < lam)
    (htheta0 : 0 < theta)
    (htheta_pi2 : theta < Real.pi / 2)
    (hmul : 1 < lam * Real.sin theta) :
    EventualSphericalUpperBoundAt lam theta := by
  let f : ℝ → ℝ := fun t => lam * Real.sin (theta - t)
  have hfcont : Continuous f := by
    fun_prop
  have hnhds : {t : ℝ | 1 < f t} ∈ 𝓝 (0 : ℝ) := by
    apply (isOpen_lt continuous_const hfcont).mem_nhds
    simpa [f] using hmul
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr_pos, hr_sub⟩
  let η : ℝ := min (r / 2) (theta / 2)
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hη_lt_theta : η < theta := by
    have : η ≤ theta / 2 := by
      dsimp [η]
      exact min_le_right _ _
    linarith
  have hη_mem : η ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hη_pos.le]
    dsimp [η]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hmargin : 1 < lam * Real.sin (theta - η) := by
    exact hr_sub hη_mem

  let ε : ℝ := η / 2
  let a : ℝ := theta - ε
  let γ : ℝ := lam * Real.sin (a - ε)

  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  have hε_lt_theta : ε < theta := by
    dsimp [ε]
    linarith
  have hε_le_one : ε ≤ 1 := by
    have : ε < 1 := by
      dsimp [ε]
      linarith [hη_lt_theta, htheta_pi2, Real.pi_lt_four]
    linarith
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have ha_pi2 : a < Real.pi / 2 := by
    dsimp [a]
    linarith
  have hε_lt_a : ε < a := by
    dsimp [a, ε]
    linarith
  have hgamma : 1 < γ := by
    have hrewrite : a - ε = theta - η := by
      dsimp [a, ε]
      ring
    simpa [γ, hrewrite] using hmargin

  have hA : 1 < 5 / ε := by
    have hfive : ε < 5 := by linarith
    exact (one_lt_div hε_pos).2 hfive
  have hd : 0 < ε / (2 * Real.pi) := by
    positivity
  obtain ⟨Nexp, hNexp⟩ :=
    eventually_pow_mul_exp_neg_pow_lt_one hA hd hgamma

  have hpow_lam : Tendsto (fun n : ℕ => lam ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hlam1
  have hlarge :
      ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ lam ^ n := hpow_lam.eventually_ge_atTop 2
  rcases Filter.eventually_atTop.1 hlarge with ⟨Nfloor, hNfloor⟩

  refine ⟨max (max Nexp Nfloor) 2, ?_⟩
  intro n hn
  have hn_exp : Nexp ≤ n := by omega
  have hn_floor : Nfloor ≤ n := by omega
  have hn_two : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega

  let Nnet : Finset (SpherePoint n) :=
    Classical.choose (exists_finset_card_le_and_angle_cover n hε_pos hε_le_one)
  have hNnet_cover :
      ∀ u : SpherePoint n, ∃ v ∈ Nnet, InnerProductGeometry.angle u.1 v.1 ≤ ε := by
    exact (Classical.choose_spec (exists_finset_card_le_and_angle_cover n hε_pos hε_le_one)).1
  have hNnet_card : (Nnet.card : ℝ) ≤ (5 / ε) ^ n := by
    exact (Classical.choose_spec (exists_finset_card_le_and_angle_cover n hε_pos hε_le_one)).2

  let M : ℕ := ⌊lam ^ n⌋₊
  have hpow_ge_two : (2 : ℝ) ≤ lam ^ n := hNfloor n hn_floor
  have hM_half : lam ^ n / 2 ≤ (M : ℝ) := by
    have hfloor : lam ^ n - 1 < (M : ℝ) := by
      exact Nat.sub_one_lt_floor (a := lam ^ n)
    nlinarith
  have hM_pos : 0 < M := by
    have : (0 : ℝ) < (M : ℝ) := by
      nlinarith [hM_half, hpow_ge_two]
    exact_mod_cast this

  let μn : ProbabilityMeasure (SpherePoint n) := sphereProbabilityMeasure n hn0
  let Ωμ : ProbabilityMeasure (Fin M → SpherePoint n) := ProbabilityMeasure.pi (fun _ : Fin M => μn)
  let bad : SpherePoint n → Set (Fin M → SpherePoint n) :=
    fun v => Set.pi Set.univ (fun _ : Fin M => (capAround v a)ᶜ)
  let badUnion : Set (Fin M → SpherePoint n) := ⋃ v ∈ Nnet, bad v

  have hcap_lb :
      (ε / Real.pi) * Real.sin (a - ε) ^ n ≤ capMeasure n a :=
    capMeasure_uniform_lower_bound n hn_two a ε ha_pos ha_pi2 hε_pos hε_lt_a
  have hs_nonneg : 0 ≤ Real.sin (a - ε) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor
    · linarith
    · linarith [Real.pi_pos, ha_pi2]
  have hfac_nonneg : 0 ≤ (ε / Real.pi) * Real.sin (a - ε) ^ n := by
    refine mul_nonneg (div_nonneg hε_pos.le Real.pi_pos.le) ?_
    exact pow_nonneg hs_nonneg n
  have hMcap :
      (ε / (2 * Real.pi)) * γ ^ n ≤ (M : ℝ) * capMeasure n a := by
    calc
      (ε / (2 * Real.pi)) * γ ^ n
        = (lam ^ n / 2) * ((ε / Real.pi) * Real.sin (a - ε) ^ n) := by
            dsimp [γ]
            rw [mul_pow]
            field_simp [Real.pi_ne_zero]
      _ ≤ (M : ℝ) * ((ε / Real.pi) * Real.sin (a - ε) ^ n) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_right hM_half hfac_nonneg
      _ ≤ (M : ℝ) * capMeasure n a := by
            exact mul_le_mul_of_nonneg_left hcap_lb (by positivity)

  have hbad_each :
      ∀ v : SpherePoint n,
        ((Ωμ : Measure (Fin M → SpherePoint n)).real (bad v)) ≤
          Real.exp (-(ε / (2 * Real.pi)) * γ ^ n) := by
    intro v
    have hbad0 :
        ((Ωμ : Measure (Fin M → SpherePoint n)).real (bad v)) ≤
          Real.exp (-(M : ℝ) * capMeasure n a) := by
      simpa [Ωμ, bad] using
        badEvent_real_le_exp_neg (n := n) (M := M) hn_two hM_pos v ha_pos.le ha_pi2.le
    refine le_trans hbad0 ?_
    have hexp_arg :
        -(M : ℝ) * capMeasure n a ≤ -(ε / (2 * Real.pi)) * γ ^ n := by
      linarith
    exact Real.exp_le_exp.mpr hexp_arg

  have hunion :
      ((Ωμ : Measure (Fin M → SpherePoint n)).real badUnion) ≤
        (Nnet.card : ℝ) * Real.exp (-(ε / (2 * Real.pi)) * γ ^ n) := by
    calc
      ((Ωμ : Measure (Fin M → SpherePoint n)).real badUnion)
        ≤ ∑ v ∈ Nnet, ((Ωμ : Measure (Fin M → SpherePoint n)).real (bad v)) := by
            simpa [badUnion] using
              MeasureTheory.measureReal_biUnion_finset_le
                (μ := (Ωμ : Measure (Fin M → SpherePoint n))) Nnet bad
      _ ≤ ∑ v ∈ Nnet, Real.exp (-(ε / (2 * Real.pi)) * γ ^ n) := by
            exact Finset.sum_le_sum (fun v hv => hbad_each v)
      _ = (Nnet.card : ℝ) * Real.exp (-(ε / (2 * Real.pi)) * γ ^ n) := by
            simp [Finset.sum_const, nsmul_eq_mul]

  have hbad_lt_one :
      ((Ωμ : Measure (Fin M → SpherePoint n)).real badUnion) < 1 := by
    have hmul_le :
        (Nnet.card : ℝ) * Real.exp (-(ε / (2 * Real.pi)) * γ ^ n) ≤
          (5 / ε) ^ n * Real.exp (-(ε / (2 * Real.pi)) * γ ^ n) := by
      exact mul_le_mul_of_nonneg_right hNnet_card (by positivity)
    exact lt_of_le_of_lt (le_trans hunion hmul_le) (by simpa [γ] using hNexp n hn_exp)

  have hnotall : ¬ ∀ ω : Fin M → SpherePoint n, ω ∈ badUnion := by
    intro hall
    have hEq : badUnion = Set.univ := Set.eq_univ_iff_forall.mpr hall
    have hreal_univ :
        ((Ωμ : Measure (Fin M → SpherePoint n)).real Set.univ) = 1 := by
      simp [Measure.real_def]
    have hbad_eq_one :
        ((Ωμ : Measure (Fin M → SpherePoint n)).real badUnion) = 1 := by
      rw [hEq]
      exact hreal_univ
    linarith
  rcases not_forall.mp hnotall with ⟨ω, hω⟩

  let C : Finset (SpherePoint n) := Finset.univ.image ω
  have hCcard : C.card ≤ M := by
    simpa [C] using (Finset.card_image_le (s := Finset.univ) (f := ω))
  have hnet_hit :
      ∀ v ∈ Nnet, ∃ i : Fin M, ω i ∈ capAround v a := by
    intro v hv
    have hnotbad : ω ∉ bad v := by
      intro hbad
      exact hω <| by
        exact mem_iUnion.2 ⟨v, mem_iUnion.2 ⟨hv, hbad⟩⟩
    have hnotforall : ¬ ∀ i : Fin M, ω i ∈ (capAround v a)ᶜ := by
      simpa [bad, Set.mem_pi, Set.mem_univ] using hnotbad
    push_neg at hnotforall
    simpa using hnotforall

  have hcov : covrad_sph C ≤ theta := by
    unfold covrad_sph
    refine csSup_le ?_ ?_
    · have hn_eq : (n - 2) + 2 = n := by omega
      rcases (show Nonempty (SpherePoint n) by
        simpa [hn_eq] using spherePoint_nonempty (n - 2)) with ⟨u⟩
      exact ⟨_, Set.mem_range_self u⟩
    · rintro y ⟨u, rfl⟩
      rcases hNnet_cover u with ⟨v, hv, huv⟩
      rcases hnet_hit v hv with ⟨i, hi⟩
      have hci : ω i ∈ C := by
        exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
      have hvu : InnerProductGeometry.angle v.1 (ω i).1 ≤ a := by
        simpa [InnerProductGeometry.angle_comm] using hi
      have huc : InnerProductGeometry.angle u.1 (ω i).1 ≤ theta := by
        calc
          InnerProductGeometry.angle u.1 (ω i).1
            ≤ InnerProductGeometry.angle u.1 v.1 + InnerProductGeometry.angle v.1 (ω i).1 := by
                exact InnerProductGeometry.angle_le_angle_add_angle u.1 v.1 (ω i).1
          _ ≤ ε + a := by gcongr
          _ = theta := by
                dsimp [a]
                ring
      have hCnonempty : C.Nonempty := ⟨ω i, hci⟩
      unfold minAngleToSphericalCode
      rw [dif_pos hCnonempty]
      exact le_trans (Finset.inf'_le (s := C) (f := fun c : SpherePoint n =>
        InnerProductGeometry.angle u.1 c.1) hci) huc

  have hrhoC : rho_sph n C.card ≤ covrad_sph C := by
    unfold rho_sph
    refine csInf_le ?_ ?_
    · refine ⟨0, ?_⟩
      rintro x ⟨D, hD, rfl⟩
      exact covrad_sph_nonneg D
    · exact ⟨C, by simp [sphericalCodesOfCard], rfl⟩

  have hrhoM : rho_sph n M ≤ theta := by
    exact le_trans (rho_sph_monotone_points hn_two hCcard) (le_trans hrhoC hcov)

  simpa [M] using hrhoM

end OptimalAlphabets
