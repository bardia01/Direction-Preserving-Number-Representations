import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.LayerCake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# OptimalAlphabets.AsymmetricProduct.BlockHardy

Block-Hardy alphabets and the standalone lower-bound theorem interface.

The proof of `BlockHardyLowerBound` is intentionally staged separately from
the final normalized-separation assembly.

The main public theorem in this file is
`blockHardy_lower : BlockHardyLowerBound`.  It proves the arbitrary-alphabet
lower-bound input used by `NormalizedSeparation.lean`.

The proof has three layers.

1. Sign alignment.  A nonnegative block tuple for `absSphereTuple u` is turned
   into a signed tuple for the original witness `u`.  The key bridge lemmas are
   `le_alpha_blockSymmAlphabet_of_nonnegative_unit_maxCorr` and
   `BlockHardyLowerBound_of_finite_core`.

2. Finite scale integration.  The core finite estimate is
   `blockHardy_finite_sandwich`.  It uses the coordinatewise payoff `blockPsi`,
   the geometric lower contribution
   `integral_blockPsi_ge_geometric_total_contribution`, and the variational
   upper bound `integral_sum_blockPsi_scale_le_log_mul_maxCorr_sq`.

3. Asymptotic simplification.  The finite sandwich is normalized by `sqrt (H n)`
   in `blockHardy_finite_core_lower`.  The support lemmas are
   `tendsto_blockHardySandwichLeft`, `eventually_log_blockScaleR_le_mul_H`, and
   `eventually_blockHardyLogDenom_le`.

The exact-cardinality alphabet for the arbitrary side is
`blockExactAlphabet`: it adds the explicit extra scalar `R_n^m` to the symmetric
block alphabet.  Its cardinality is proved by `blockExactAlphabet_card`.
-/

noncomputable section

open Set Filter Topology Real Metric MeasureTheory
open intervalIntegral
open scoped BigOperators

namespace OptimalAlphabets
namespace AsymmetricProduct

/-- The slowly growing geometric ratio used by the block-Hardy construction. -/
def blockScaleR (n : ℕ) : ℝ :=
  Real.exp (Real.sqrt (Real.log ((n : ℝ) + 2)))

/-- The block-Hardy ratio is strictly larger than `1`. -/
theorem one_lt_blockScaleR (n : ℕ) :
    1 < blockScaleR n := by
  have harg : 1 < ((n : ℝ) + 2) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    linarith
  have hlog : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos harg
  have hsqrt : 0 < Real.sqrt (Real.log ((n : ℝ) + 2)) :=
    Real.sqrt_pos_of_pos hlog
  have hexp : Real.exp 0 < Real.exp (Real.sqrt (Real.log ((n : ℝ) + 2))) :=
    Real.exp_strictMono hsqrt
  simpa [blockScaleR] using hexp

/-- Our real harmonic sum is the real coercion of mathlib's rational
`harmonic` number. -/
theorem H_eq_harmonic_cast (n : ℕ) :
    H n = (harmonic n : ℝ) := by
  simp [H, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- Standard lower bound `log(n+1) ≤ H_n`, in the local real-valued notation. -/
theorem log_nat_add_one_le_H (n : ℕ) :
    Real.log ((n : ℝ) + 1) ≤ H n := by
  have h := log_add_one_le_harmonic n
  rw [H_eq_harmonic_cast]
  simpa [Nat.cast_add, Nat.cast_one] using h

/-- A convenient exponential form of `log(n+1) ≤ H_n`. -/
theorem nat_cast_le_exp_H (n : ℕ) :
    (n : ℝ) ≤ Real.exp (H n) := by
  have hlog := log_nat_add_one_le_H n
  have hexp : Real.exp (Real.log ((n : ℝ) + 1)) ≤ Real.exp (H n) :=
    Real.exp_monotone hlog
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  have hle : (n : ℝ) + 1 ≤ Real.exp (H n) := by
    simpa [Real.exp_log hpos] using hexp
  linarith

/-- The block-Hardy ratio tends to infinity. -/
theorem blockScaleR_tendsto_atTop :
    Tendsto blockScaleR atTop atTop := by
  unfold blockScaleR
  have harg : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add
      (tendsto_const_nhds (x := (2 : ℝ)))
  exact Real.tendsto_exp_atTop.comp
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp harg))

/-- Exact logarithm of the chosen block-Hardy ratio. -/
@[simp] theorem log_blockScaleR (n : ℕ) :
    Real.log (blockScaleR n) =
      Real.sqrt (Real.log ((n : ℝ) + 2)) := by
  simp [blockScaleR]

/-- Powers of `blockScaleR n` as an embedding of natural exponents. -/
def blockPowEmbedding (n : ℕ) : ℕ ↪ ℝ where
  toFun j := blockScaleR n ^ j
  inj' := by
    intro a b h
    by_cases hab : a = b
    · exact hab
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · have hpow : blockScaleR n ^ a < blockScaleR n ^ b :=
        pow_lt_pow_right₀ (one_lt_blockScaleR n) hlt
      linarith
    · have hpow : blockScaleR n ^ b < blockScaleR n ^ a :=
        pow_lt_pow_right₀ (one_lt_blockScaleR n) hgt
      linarith

/-- Positive block-Hardy levels `{1, R, ..., R^(m-1)}`. -/
def blockPositiveFinset (n m : ℕ) : Finset ℝ :=
  (Finset.range m).map (blockPowEmbedding n)

@[simp] theorem blockPositiveFinset_card (n m : ℕ) :
    (blockPositiveFinset n m).card = m := by
  simp [blockPositiveFinset]

/-- Every block-Hardy positive level is strictly positive. -/
theorem blockPositiveFinset_pos {n m : ℕ} {x : ℝ}
    (hx : x ∈ blockPositiveFinset n m) :
    0 < x := by
  rcases Finset.mem_map.1 hx with ⟨j, _hj, rfl⟩
  exact pow_pos (lt_trans zero_lt_one (one_lt_blockScaleR n)) j

/-- Every positive block level is at least `1`. -/
theorem one_le_blockScaleR_pow (n j : ℕ) :
    1 ≤ blockScaleR n ^ j :=
  one_le_pow₀ (le_of_lt (one_lt_blockScaleR n))

/-- The nonnegative block alphabet `{0, 1, R, ..., R^(m-1)}` used before
signs are aligned with an arbitrary witness vector. -/
def nonnegativeBlockAlphabet (n m : ℕ) : Finset ℝ :=
  insert 0 (blockPositiveFinset n m)

@[simp] theorem mem_nonnegativeBlockAlphabet {n m : ℕ} {x : ℝ} :
    x ∈ nonnegativeBlockAlphabet n m ↔
      x = 0 ∨ x ∈ blockPositiveFinset n m := by
  simp [nonnegativeBlockAlphabet]

/-- Elements of the nonnegative block alphabet are nonnegative. -/
theorem nonnegativeBlockAlphabet_nonneg {n m : ℕ} {x : ℝ}
    (hx : x ∈ nonnegativeBlockAlphabet n m) :
    0 ≤ x := by
  rw [mem_nonnegativeBlockAlphabet] at hx
  rcases hx with rfl | hx
  · exact le_rfl
  · exact (blockPositiveFinset_pos hx).le
/-- Symmetric block-Hardy alphabet `{0} ∪ ±{1, R, ..., R^(m-1)}`. -/
def blockSymmAlphabet (n m : ℕ) : Finset ℝ :=
  signedFinset (blockPositiveFinset n m)

@[simp] theorem blockSymmAlphabet_card (n m : ℕ) :
    (blockSymmAlphabet n m).card = 2 * m + 1 := by
  rw [blockSymmAlphabet, signedFinset_card_of_pos]
  · simp
  · intro x hx
    exact blockPositiveFinset_pos hx

/-- Coordinatewise absolute value of a sphere witness, as a raw tuple. -/
def absSphereTuple {n : ℕ} (u : SpherePoint n) : Fin n → ℝ :=
  fun i => |u.1 i|

@[simp] theorem absSphereTuple_nonneg {n : ℕ} (u : SpherePoint n) (i : Fin n) :
    0 ≤ absSphereTuple u i := by
  simp [absSphereTuple]

/-- Taking coordinatewise absolute values preserves the Euclidean norm of a
sphere witness. -/
theorem norm_tupleVector_absSphereTuple {n : ℕ} (u : SpherePoint n) :
    ‖tupleVector (absSphereTuple u)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hunorm : ‖u.1‖ = 1 := norm_spherePoint u
  rw [EuclideanSpace.norm_eq] at hunorm
  rw [← hunorm]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp [tupleVector, absSphereTuple, sq_abs]

/-- Align a nonnegative tuple with the signs of the witness `u`. -/
def alignToWitness {n : ℕ} (u : SpherePoint n) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => if 0 ≤ u.1 i then x i else -x i

/-- Sign alignment sends nonnegative block tuples into the signed block
alphabet. -/
theorem alignToWitness_mem_blockSymmAlphabet {n m : ℕ}
    (u : SpherePoint n) {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ nonnegativeBlockAlphabet n m) :
    ∀ i, alignToWitness u x i ∈ blockSymmAlphabet n m := by
  intro i
  have hxi := hx i
  rw [mem_nonnegativeBlockAlphabet] at hxi
  rw [blockSymmAlphabet, mem_signedFinset]
  by_cases hsign : 0 ≤ u.1 i
  · rcases hxi with hzero | hpos
    · exact Or.inl (by simp [alignToWitness, hsign, hzero])
    · exact Or.inr (Or.inl (by simpa [alignToWitness, hsign] using hpos))
  · rcases hxi with hzero | hpos
    · exact Or.inl (by simp [alignToWitness, hsign, hzero])
    · exact Or.inr (Or.inr (by simpa [alignToWitness, hsign] using hpos))

/-- Sign alignment preserves nonzeroness. -/
theorem tupleVector_alignToWitness_ne_zero {n : ℕ}
    (u : SpherePoint n) {x : Fin n → ℝ}
    (hx : tupleVector x ≠ 0) :
    tupleVector (alignToWitness u x) ≠ 0 := by
  rw [tupleVector_ne_zero_iff] at hx ⊢
  rcases hx with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  by_cases hsign : 0 ≤ u.1 i
  · simpa [alignToWitness, hsign] using hi
  · simpa [alignToWitness, hsign] using (neg_ne_zero.mpr hi)

/-- Sign alignment preserves Euclidean norm. -/
theorem norm_tupleVector_alignToWitness {n : ℕ}
    (u : SpherePoint n) (x : Fin n → ℝ) :
    ‖tupleVector (alignToWitness u x)‖ = ‖tupleVector x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases hsign : 0 ≤ u.1 i <;>
    simp [tupleVector, alignToWitness, hsign]

/-- After sign alignment, the witness dot product becomes the dot product with
the coordinatewise absolute value of the witness. -/
theorem inner_alignToWitness_eq_absSphereTuple {n : ℕ}
    (u : SpherePoint n) (x : Fin n → ℝ) :
    inner ℝ u.1 (tupleVector (alignToWitness u x)) =
      inner ℝ (tupleVector (absSphereTuple u)) (tupleVector x) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases hsign : 0 ≤ u.1 i
  · have habs : |u.1 i| = u.1 i := abs_of_nonneg hsign
    simp [tupleVector, alignToWitness, absSphereTuple, hsign, habs]
  · have hle : u.1 i ≤ 0 := le_of_not_ge hsign
    have habs : |u.1 i| = -u.1 i := abs_of_nonpos hle
    simp [tupleVector, alignToWitness, absSphereTuple, hsign, habs]

/-- Correlation after sign alignment is exactly the nonnegative correlation
against `|u|`. -/
theorem tupleCorr_alignToWitness_eq_absSphereTuple {n : ℕ}
    (u : SpherePoint n) (x : Fin n → ℝ) :
    tupleCorr u (alignToWitness u x) =
      inner ℝ (tupleVector (absSphereTuple u)) (tupleVector x) /
        ‖tupleVector x‖ := by
  unfold tupleCorr
  rw [inner_alignToWitness_eq_absSphereTuple u x,
    norm_tupleVector_alignToWitness]

/-- A nonnegative block tuple with good absolute-witness correlation
lower-bounds the signed block maximum for the original witness. -/
theorem le_maxCorr_blockSymmAlphabet_of_nonnegative_tuple {n m : ℕ}
    {u : SpherePoint n} {C : ℝ} {x : Fin n → ℝ}
    (hxmem : ∀ i, x i ∈ nonnegativeBlockAlphabet n m)
    (hxne : tupleVector x ≠ 0)
    (hC :
      C ≤ inner ℝ (tupleVector (absSphereTuple u)) (tupleVector x) /
        ‖tupleVector x‖) :
    C ≤ maxCorr_asym n (blockSymmAlphabet n m) u := by
  let y : Fin n → ℝ := alignToWitness u x
  have hy_mem : ∀ i, y i ∈ blockSymmAlphabet n m := by
    simpa [y] using alignToWitness_mem_blockSymmAlphabet u hxmem
  have hy_ne : tupleVector y ≠ 0 := by
    simpa [y] using tupleVector_alignToWitness_ne_zero u hxne
  have hy_tuple : y ∈ nonzeroAsymProductTuples n (blockSymmAlphabet n m) :=
    mem_nonzeroAsymProductTuples.2 ⟨hy_mem, hy_ne⟩
  refine le_maxCorr_asym_of_exists_tuple ?_
  refine ⟨y, hy_tuple, ?_⟩
  simpa [y, tupleCorr_alignToWitness_eq_absSphereTuple u x] using hC

/-- Lower-bound `alpha_asym` for signed block alphabets by constructing, for
every witness, one good nonnegative block tuple. -/
theorem le_alpha_blockSymmAlphabet_of_forall_nonnegative_tuple {n m : ℕ}
    (hn : 0 < n) {C : ℝ}
    (hbound : ∀ u : SpherePoint n,
      ∃ x : Fin n → ℝ,
        (∀ i, x i ∈ nonnegativeBlockAlphabet n m) ∧
        tupleVector x ≠ 0 ∧
        C ≤ inner ℝ (tupleVector (absSphereTuple u)) (tupleVector x) /
          ‖tupleVector x‖) :
    C ≤ alpha_asym n (blockSymmAlphabet n m) := by
  refine le_alpha_asym_of_forall_le_maxCorr hn ?_
  intro u
  rcases hbound u with ⟨x, hxmem, hxne, hC⟩
  exact le_maxCorr_blockSymmAlphabet_of_nonnegative_tuple hxmem hxne hC

/-- Maximum nonnegative correlation against the nonnegative block alphabet.
This is the `M_B(s)` quantity from the proof note. -/
def nonnegativeBlockMaxCorr (n m : ℕ) (s : Fin n → ℝ) : ℝ :=
  let T := nonzeroAsymProductTuples n (nonnegativeBlockAlphabet n m)
  if h : T.Nonempty then
    T.sup' h fun x =>
      inner ℝ (tupleVector s) (tupleVector x) / ‖tupleVector x‖
  else
    0

/-- If the nonnegative product set is nonempty, `nonnegativeBlockMaxCorr` is
attained by one of its tuples. -/
theorem exists_tuple_attains_nonnegativeBlockMaxCorr {n m : ℕ}
    {s : Fin n → ℝ}
    (hT :
      (nonzeroAsymProductTuples n (nonnegativeBlockAlphabet n m)).Nonempty) :
    ∃ x,
      x ∈ nonzeroAsymProductTuples n (nonnegativeBlockAlphabet n m) ∧
      nonnegativeBlockMaxCorr n m s =
        inner ℝ (tupleVector s) (tupleVector x) / ‖tupleVector x‖ := by
  unfold nonnegativeBlockMaxCorr
  rw [dif_pos hT]
  obtain ⟨x, hx, hxmax⟩ :=
    Finset.exists_mem_eq_sup' hT fun x =>
      inner ℝ (tupleVector s) (tupleVector x) / ‖tupleVector x‖
  exact ⟨x, hx, hxmax⟩

/-- Any nonzero nonnegative block tuple is bounded by the maximum
`nonnegativeBlockMaxCorr`. -/
theorem tupleCorr_le_nonnegativeBlockMaxCorr {n m : ℕ}
    {s x : Fin n → ℝ}
    (hx : x ∈ nonzeroAsymProductTuples n (nonnegativeBlockAlphabet n m)) :
    inner ℝ (tupleVector s) (tupleVector x) / ‖tupleVector x‖ ≤
      nonnegativeBlockMaxCorr n m s := by
  unfold nonnegativeBlockMaxCorr
  have hT :
      (nonzeroAsymProductTuples n (nonnegativeBlockAlphabet n m)).Nonempty :=
    ⟨x, hx⟩
  rw [dif_pos hT]
  exact Finset.le_sup'
    (s := nonzeroAsymProductTuples n (nonnegativeBlockAlphabet n m))
    (f := fun x =>
      inner ℝ (tupleVector s) (tupleVector x) / ‖tupleVector x‖) hx

/-- A positive block level belongs to the nonnegative block alphabet. -/
theorem blockScaleR_pow_mem_nonnegativeBlockAlphabet {n m j : ℕ}
    (hj : j < m) :
    blockScaleR n ^ j ∈ nonnegativeBlockAlphabet n m := by
  rw [mem_nonnegativeBlockAlphabet]
  exact Or.inr (Finset.mem_map.2 ⟨j, Finset.mem_range.2 hj, rfl⟩)

/-- For `0 < n` and `1 ≤ m`, the nonnegative block product has a concrete
nonzero tuple. -/
theorem nonzero_nonnegativeBlockTuples_nonempty {n m : ℕ}
    (hn : 0 < n) (hm : 1 ≤ m) :
    (nonzeroAsymProductTuples n (nonnegativeBlockAlphabet n m)).Nonempty := by
  let x : Fin n → ℝ := fun i => if i = ⟨0, hn⟩ then (1 : ℝ) else 0
  refine ⟨x, ?_⟩
  rw [mem_nonzeroAsymProductTuples]
  constructor
  · intro i
    by_cases hi : i = ⟨0, hn⟩
    · have h0 : (0 : ℕ) < m := by omega
      simpa [x, hi] using
        blockScaleR_pow_mem_nonnegativeBlockAlphabet (n := n) (m := m) h0
    · simp [x, hi]
  · rw [tupleVector_ne_zero_iff]
    refine ⟨⟨0, hn⟩, ?_⟩
    simp [x]

/-- The nonnegative block maximum is attained by a nonzero tuple when the
ambient dimension and number of levels are nonzero. -/
theorem exists_tuple_attains_nonnegativeBlockMaxCorr_of_pos {n m : ℕ}
    (hn : 0 < n) (hm : 1 ≤ m) {s : Fin n → ℝ} :
    ∃ x,
      x ∈ nonzeroAsymProductTuples n (nonnegativeBlockAlphabet n m) ∧
      nonnegativeBlockMaxCorr n m s =
        inner ℝ (tupleVector s) (tupleVector x) / ‖tupleVector x‖ :=
  exists_tuple_attains_nonnegativeBlockMaxCorr
    (nonzero_nonnegativeBlockTuples_nonempty hn hm)

/-- A lower bound on `nonnegativeBlockMaxCorr` provides the explicit tuple
needed for the signed-alphabet `alpha_asym` lower bound. -/
theorem le_alpha_blockSymmAlphabet_of_nonnegativeBlockMaxCorr
    {n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m) {C : ℝ}
    (hbound : ∀ u : SpherePoint n,
      C ≤ nonnegativeBlockMaxCorr n m (absSphereTuple u)) :
    C ≤ alpha_asym n (blockSymmAlphabet n m) := by
  refine le_alpha_blockSymmAlphabet_of_forall_nonnegative_tuple hn ?_
  intro u
  rcases exists_tuple_attains_nonnegativeBlockMaxCorr_of_pos
      (n := n) (m := m) hn hm (s := absSphereTuple u) with
    ⟨x, hx, hxmax⟩
  rcases mem_nonzeroAsymProductTuples.1 hx with ⟨hxmem, hxne⟩
  refine ⟨x, hxmem, hxne, ?_⟩
  exact le_trans (hbound u) (by rw [hxmax])

/-- It is enough to prove the block-Hardy lower bound for arbitrary
nonnegative unit vectors; sign alignment and the sphere objective are handled
by the preceding infrastructure. -/
theorem le_alpha_blockSymmAlphabet_of_nonnegative_unit_maxCorr
    {n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m) {C : ℝ}
    (hbound : ∀ s : Fin n → ℝ,
      (∀ i, 0 ≤ s i) → ‖tupleVector s‖ = 1 →
        C ≤ nonnegativeBlockMaxCorr n m s) :
    C ≤ alpha_asym n (blockSymmAlphabet n m) := by
  refine le_alpha_blockSymmAlphabet_of_nonnegativeBlockMaxCorr hn hm ?_
  intro u
  exact hbound (absSphereTuple u)
    (fun i => absSphereTuple_nonneg u i)
    (norm_tupleVector_absSphereTuple u)

/-- Finite-dimensional nonnegative-unit lower-bound statement for a fixed
`n,m,C`.  This is the remaining analytic core of the Block-Hardy proof. -/
def NonnegativeUnitMaxCorrLowerBound (n m : ℕ) (C : ℝ) : Prop :=
  ∀ s : Fin n → ℝ,
    (∀ i, 0 ≤ s i) → ‖tupleVector s‖ = 1 →
      C ≤ nonnegativeBlockMaxCorr n m s

/-- The finite analytic core implies the corresponding `alpha_asym` lower
bound for the signed block alphabet. -/
theorem le_alpha_blockSymmAlphabet_of_finite_core
    {n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m) {C : ℝ}
    (hcore : NonnegativeUnitMaxCorrLowerBound n m C) :
    C ≤ alpha_asym n (blockSymmAlphabet n m) :=
  le_alpha_blockSymmAlphabet_of_nonnegative_unit_maxCorr hn hm hcore

/-- The coordinatewise convex-dual payoff
`ψ_B(y) = max_{b ∈ {0,1,R,...}} (2 b y - b^2)`.  Including `0` in the
nonnegative alphabet builds in the positive part from the paper definition. -/
def blockPsi (n m : ℕ) (y : ℝ) : ℝ :=
  (nonnegativeBlockAlphabet n m).sup'
    (by simp [nonnegativeBlockAlphabet] : (nonnegativeBlockAlphabet n m).Nonempty)
    fun b => 2 * b * y - b ^ 2

/-- `ψ_B` is continuous as a finite supremum of affine functions. -/
theorem continuous_blockPsi (n m : ℕ) :
    Continuous (blockPsi n m) := by
  let S : Finset ℝ := nonnegativeBlockAlphabet n m
  have hS : S.Nonempty := by
    simp [S, nonnegativeBlockAlphabet]
  change Continuous
    (fun y : ℝ => S.sup' hS (fun b : ℝ => 2 * b * y - b ^ 2))
  refine Continuous.finset_sup'_apply
    (s := S)
    (f := fun b : ℝ => fun y : ℝ => 2 * b * y - b ^ 2)
    hS ?_
  intro b _hb
  fun_prop

/-- On a positive interval, `ψ_B(y) * y^(-3)` is interval-integrable. -/
theorem intervalIntegrable_blockPsi_mul_zpow_neg_three_of_pos
    {n m : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun y : ℝ => blockPsi n m y * y ^ (-3 : ℤ))
      volume a b := by
  have hnot : (0 : ℝ) ∉ Set.uIcc a b := Set.notMem_uIcc_of_lt ha hb
  exact (intervalIntegrable_zpow
    (μ := volume) (a := a) (b := b) (n := (-3 : ℤ))
    (Or.inr hnot)).continuousOn_mul
      (continuous_blockPsi n m).continuousOn

/-- `ψ_B` is nonnegative, because the level `0` is available. -/
theorem blockPsi_nonneg (n m : ℕ) (y : ℝ) :
    0 ≤ blockPsi n m y := by
  unfold blockPsi
  have hzero : (0 : ℝ) ∈ nonnegativeBlockAlphabet n m := by
    simp [nonnegativeBlockAlphabet]
  have hle :=
    Finset.le_sup' (s := nonnegativeBlockAlphabet n m)
      (f := fun b : ℝ => 2 * b * y - b ^ 2) hzero
  calc
    (0 : ℝ) = 2 * 0 * y - 0 ^ 2 := by norm_num
    _ ≤ (nonnegativeBlockAlphabet n m).sup'
        (by simp [nonnegativeBlockAlphabet] :
          (nonnegativeBlockAlphabet n m).Nonempty)
        (fun b : ℝ => 2 * b * y - b ^ 2) := hle

/-- `ψ_B` dominates the quadratic payoff obtained by using any available
positive block level. -/
theorem blockPsi_ge_level {n m j : ℕ} (hj : j < m) (y : ℝ) :
    2 * (blockScaleR n ^ j) * y - (blockScaleR n ^ j) ^ 2 ≤
      blockPsi n m y := by
  unfold blockPsi
  have hmem :
      blockScaleR n ^ j ∈ nonnegativeBlockAlphabet n m :=
    blockScaleR_pow_mem_nonnegativeBlockAlphabet (n := n) (m := m) hj
  exact Finset.le_sup' (s := nonnegativeBlockAlphabet n m)
    (f := fun b : ℝ => 2 * b * y - b ^ 2) hmem
/-- Pointwise lower bound for the integrand `ψ_B(y) y^{-3}` using one
available block level. -/
theorem levelProduct_mul_zpow_neg_three_le_blockPsi {n m j : ℕ}
    (hj : j < m) {y : ℝ} (hy : 0 < y) :
    (2 * (blockScaleR n ^ j) * y - (blockScaleR n ^ j) ^ 2) *
        y ^ (-3 : ℤ) ≤
      blockPsi n m y * y ^ (-3 : ℤ) := by
  have hlevel := blockPsi_ge_level (n := n) (m := m) hj y
  have hzpow_nonneg : 0 ≤ y ^ (-3 : ℤ) := by positivity
  exact mul_le_mul_of_nonneg_right hlevel hzpow_nonneg

/-- Integral of `y^(-2)` over a positive interval. -/
theorem integral_zpow_neg_two_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ y in a..b, y ^ (-2 : ℤ)) = a⁻¹ - b⁻¹ := by
  have hnot : (0 : ℝ) ∉ Set.uIcc a b := Set.notMem_uIcc_of_lt ha hb
  have h :=
    integral_zpow (a := a) (b := b) (n := (-2 : ℤ))
      (Or.inr ⟨by norm_num, hnot⟩)
  calc
    (∫ y in a..b, y ^ (-2 : ℤ)) = (b⁻¹ - a⁻¹) / ((-2 : ℝ) + 1) := by
      simpa using h
    _ = a⁻¹ - b⁻¹ := by ring

/-- Integral of `y^(-3)` over a positive interval. -/
theorem integral_zpow_neg_three_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ y in a..b, y ^ (-3 : ℤ)) = (a⁻¹ ^ 2 - b⁻¹ ^ 2) / 2 := by
  have hnot : (0 : ℝ) ∉ Set.uIcc a b := Set.notMem_uIcc_of_lt ha hb
  have h :=
    integral_zpow (a := a) (b := b) (n := (-3 : ℤ))
      (Or.inr ⟨by norm_num, hnot⟩)
  calc
    (∫ y in a..b, y ^ (-3 : ℤ)) =
        ((b ^ 2)⁻¹ - (a ^ 2)⁻¹) / ((-3 : ℝ) + 1) := by
      simpa using h
    _ = (a⁻¹ ^ 2 - b⁻¹ ^ 2) / 2 := by
      simp
      ring_nf

/-- Integral of the block-Hardy lower kernel associated with one level `B`. -/
theorem integral_blockLevel_kernel_of_pos {a b B : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    (∫ y in a..b,
        (2 * B) * y ^ (-2 : ℤ) - B ^ 2 * y ^ (-3 : ℤ)) =
      (2 * B) * (a⁻¹ - b⁻¹) -
        B ^ 2 * ((a⁻¹ ^ 2 - b⁻¹ ^ 2) / 2) := by
  have hnot : (0 : ℝ) ∉ Set.uIcc a b := Set.notMem_uIcc_of_lt ha hb
  have h2 :
      IntervalIntegrable (fun y : ℝ => (2 * B) * y ^ (-2 : ℤ))
        volume a b := by
    exact (intervalIntegrable_zpow
      (μ := volume) (a := a) (b := b) (n := (-2 : ℤ))
      (Or.inr hnot)).const_mul _
  have h3 :
      IntervalIntegrable (fun y : ℝ => B ^ 2 * y ^ (-3 : ℤ))
        volume a b := by
    exact (intervalIntegrable_zpow
      (μ := volume) (a := a) (b := b) (n := (-3 : ℤ))
      (Or.inr hnot)).const_mul _
  rw [intervalIntegral.integral_sub h2 h3,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_zpow_neg_two_of_pos ha hb, integral_zpow_neg_three_of_pos ha hb]

/-- The exact integral contribution over one geometric half-block
`[B/2, R*B/2]`. -/
theorem integral_blockLevel_kernel_half_to_ratio {B R : ℝ}
    (hB : 0 < B) (hR : 0 < R) :
    (∫ y in (B / 2)..(R * B / 2),
        (2 * B) * y ^ (-2 : ℤ) - B ^ 2 * y ^ (-3 : ℤ)) =
      2 - 4 / R + 2 / R ^ 2 := by
  have ha : 0 < B / 2 := by positivity
  have hb : 0 < R * B / 2 := by positivity
  rw [integral_blockLevel_kernel_of_pos ha hb]
  field_simp [hB.ne', hR.ne']
  ring

/-- The final block contribution over `[B/2, R*B]`, matching the paper's
last-level interval. -/
theorem integral_blockLevel_kernel_half_to_ratio_full {B R : ℝ}
    (hB : 0 < B) (hR : 0 < R) :
    (∫ y in (B / 2)..(R * B),
        (2 * B) * y ^ (-2 : ℤ) - B ^ 2 * y ^ (-3 : ℤ)) =
      2 - 2 / R + 1 / (2 * R ^ 2) := by
  have ha : 0 < B / 2 := by positivity
  have hb : 0 < R * B := by positivity
  rw [integral_blockLevel_kernel_of_pos ha hb]
  field_simp [hB.ne', hR.ne']
  ring

/-- Away from zero, the zpow kernel and the product-form kernel are the same
algebraic expression. -/
theorem blockLevel_kernel_eq_product_kernel_of_ne {B y : ℝ} (hy : y ≠ 0) :
    (2 * B) * y ^ (-2 : ℤ) - B ^ 2 * y ^ (-3 : ℤ) =
      (2 * B * y - B ^ 2) * y ^ (-3 : ℤ) := by
  field_simp [hy]

/-- The product-form level kernel is interval-integrable on positive
intervals. -/
theorem intervalIntegrable_levelProduct_mul_zpow_neg_three_of_pos
    {a b B : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable
      (fun y : ℝ => (2 * B * y - B ^ 2) * y ^ (-3 : ℤ))
      volume a b := by
  have hnot : (0 : ℝ) ∉ Set.uIcc a b := Set.notMem_uIcc_of_lt ha hb
  exact (intervalIntegrable_zpow
    (μ := volume) (a := a) (b := b) (n := (-3 : ℤ))
    (Or.inr hnot)).continuousOn_mul (by fun_prop)

/-- Integral comparison between one level product kernel and
`ψ_B(y) y^{-3}` on a positive interval. -/
theorem integral_levelProduct_le_blockPsi_mul_zpow_neg_three
    {n m j : ℕ} {a b : ℝ}
    (hj : j < m) (hab : a ≤ b) (ha : 0 < a) (hb : 0 < b) :
    (∫ y in a..b,
        (2 * (blockScaleR n ^ j) * y - (blockScaleR n ^ j) ^ 2) *
          y ^ (-3 : ℤ)) ≤
      ∫ y in a..b, blockPsi n m y * y ^ (-3 : ℤ) := by
  have hkernel :
      IntervalIntegrable
        (fun y : ℝ =>
          (2 * (blockScaleR n ^ j) * y -
              (blockScaleR n ^ j) ^ 2) * y ^ (-3 : ℤ))
        volume a b :=
    intervalIntegrable_levelProduct_mul_zpow_neg_three_of_pos
      (B := blockScaleR n ^ j) ha hb
  have hpsi :
      IntervalIntegrable
        (fun y : ℝ => blockPsi n m y * y ^ (-3 : ℤ))
        volume a b :=
    intervalIntegrable_blockPsi_mul_zpow_neg_three_of_pos
      (n := n) (m := m) ha hb
  refine intervalIntegral.integral_mono_on
    (μ := volume) hab hkernel hpsi ?_
  intro y hy
  have hy_pos : 0 < y := lt_of_lt_of_le ha hy.1
  exact levelProduct_mul_zpow_neg_three_le_blockPsi
    (n := n) (m := m) (j := j) hj hy_pos

/-- One non-final geometric half-block contributes at least
`2 - 4/R + 2/R^2` to the `ψ_B(y)y^{-3}` integral. -/
theorem integral_blockPsi_ge_geometric_half_contribution
    {n m j : ℕ} (hj : j < m) :
    2 - 4 / blockScaleR n + 2 / (blockScaleR n) ^ 2 ≤
      ∫ y in (blockScaleR n ^ j / 2)..(blockScaleR n * blockScaleR n ^ j / 2),
        blockPsi n m y * y ^ (-3 : ℤ) := by
  let B : ℝ := blockScaleR n ^ j
  let R : ℝ := blockScaleR n
  have hB : 0 < B := by
    dsimp [B]
    exact pow_pos (lt_trans zero_lt_one (one_lt_blockScaleR n)) j
  have hR : 0 < R := by
    dsimp [R]
    exact lt_trans zero_lt_one (one_lt_blockScaleR n)
  have ha : 0 < B / 2 := by positivity
  have hb : 0 < R * B / 2 := by positivity
  have hab : B / 2 ≤ R * B / 2 := by
    nlinarith [hB, one_lt_blockScaleR n]
  have hmono :=
    integral_levelProduct_le_blockPsi_mul_zpow_neg_three
      (n := n) (m := m) (j := j) hj hab ha hb
  have hkernel :=
    integral_blockLevel_kernel_half_to_ratio (B := B) (R := R) hB hR
  calc
    2 - 4 / blockScaleR n + 2 / (blockScaleR n) ^ 2
        = ∫ y in (B / 2)..(R * B / 2),
            (2 * B) * y ^ (-2 : ℤ) - B ^ 2 * y ^ (-3 : ℤ) := by
          rw [hkernel]
    _ = ∫ y in (B / 2)..(R * B / 2),
            (2 * B * y - B ^ 2) * y ^ (-3 : ℤ) := by
          refine intervalIntegral.integral_congr ?_
          intro y hy_mem
          have hnot : (0 : ℝ) ∉ Set.uIcc (B / 2) (R * B / 2) :=
            Set.notMem_uIcc_of_lt ha hb
          by_cases hy : y = 0
          · exfalso
            exact hnot (by simpa [hy] using hy_mem)
          · exact blockLevel_kernel_eq_product_kernel_of_ne (B := B) (y := y) hy
    _ ≤ ∫ y in (B / 2)..(R * B / 2),
          blockPsi n m y * y ^ (-3 : ℤ) := by
          simpa [B, R, mul_assoc] using hmono

/-- The final geometric block contributes at least
`2 - 2/R + 1/(2R^2)` to the `ψ_B(y)y^{-3}` integral. -/
theorem integral_blockPsi_ge_final_geometric_contribution
    {n m : ℕ} (hm : 1 ≤ m) :
    2 - 2 / blockScaleR n + 1 / (2 * (blockScaleR n) ^ 2) ≤
      ∫ y in (blockScaleR n ^ (m - 1) / 2)..(blockScaleR n * blockScaleR n ^ (m - 1)),
        blockPsi n m y * y ^ (-3 : ℤ) := by
  let j : ℕ := m - 1
  have hj : j < m := by
    dsimp [j]
    omega
  let B : ℝ := blockScaleR n ^ j
  let R : ℝ := blockScaleR n
  have hB : 0 < B := by
    dsimp [B]
    exact pow_pos (lt_trans zero_lt_one (one_lt_blockScaleR n)) j
  have hR : 0 < R := by
    dsimp [R]
    exact lt_trans zero_lt_one (one_lt_blockScaleR n)
  have ha : 0 < B / 2 := by positivity
  have hb : 0 < R * B := by positivity
  have hab : B / 2 ≤ R * B := by
    nlinarith [hB, one_lt_blockScaleR n]
  have hmono :=
    integral_levelProduct_le_blockPsi_mul_zpow_neg_three
      (n := n) (m := m) (j := j) hj hab ha hb
  have hkernel :=
    integral_blockLevel_kernel_half_to_ratio_full (B := B) (R := R) hB hR
  calc
    2 - 2 / blockScaleR n + 1 / (2 * (blockScaleR n) ^ 2)
        = ∫ y in (B / 2)..(R * B),
            (2 * B) * y ^ (-2 : ℤ) - B ^ 2 * y ^ (-3 : ℤ) := by
          rw [hkernel]
    _ = ∫ y in (B / 2)..(R * B),
            (2 * B * y - B ^ 2) * y ^ (-3 : ℤ) := by
          refine intervalIntegral.integral_congr ?_
          intro y hy_mem
          have hnot : (0 : ℝ) ∉ Set.uIcc (B / 2) (R * B) :=
            Set.notMem_uIcc_of_lt ha hb
          by_cases hy : y = 0
          · exfalso
            exact hnot (by simpa [hy] using hy_mem)
          · exact blockLevel_kernel_eq_product_kernel_of_ne (B := B) (y := y) hy
    _ ≤ ∫ y in (B / 2)..(R * B),
          blockPsi n m y * y ^ (-3 : ℤ) := by
          simpa [B, R, j, mul_assoc] using hmono

/-- Endpoints for the block-Hardy geometric integration chain.  The last
endpoint is `R^m`, while the earlier endpoints are `R^k/2`. -/
def blockIntegralEndpoint (n m k : ℕ) : ℝ :=
  if k < m then blockScaleR n ^ k / 2 else blockScaleR n ^ m

/-- All block-Hardy integration-chain endpoints are positive. -/
theorem blockIntegralEndpoint_pos (n m k : ℕ) :
    0 < blockIntegralEndpoint n m k := by
  unfold blockIntegralEndpoint
  have hR : 0 < blockScaleR n := lt_trans zero_lt_one (one_lt_blockScaleR n)
  by_cases hk : k < m
  · simp [hk, div_pos (pow_pos hR k) (by norm_num : (0 : ℝ) < 2)]
  · simp [hk, pow_pos hR m]

@[simp] theorem blockIntegralEndpoint_zero {n m : ℕ} (hm : 0 < m) :
    blockIntegralEndpoint n m 0 = (1 : ℝ) / 2 := by
  simp [blockIntegralEndpoint, hm]

@[simp] theorem blockIntegralEndpoint_last (n m : ℕ) :
    blockIntegralEndpoint n m m = blockScaleR n ^ m := by
  simp [blockIntegralEndpoint]

/-- The sum of the non-final geometric half-block contributions plus the final
block contribution lower-bounds the full scale integral from `1/2` to `R^m`. -/
theorem integral_blockPsi_ge_geometric_total_contribution
    {n m : ℕ} (hm : 1 ≤ m) :
    (∑ _j ∈ Finset.range (m - 1),
        (2 - 4 / blockScaleR n + 2 / (blockScaleR n) ^ 2)) +
      (2 - 2 / blockScaleR n + 1 / (2 * (blockScaleR n) ^ 2)) ≤
        ∫ y in (1 / 2 : ℝ)..(blockScaleR n ^ m),
          blockPsi n m y * y ^ (-3 : ℤ) := by
  let f : ℝ → ℝ := fun y => blockPsi n m y * y ^ (-3 : ℤ)
  let a : ℕ → ℝ := blockIntegralEndpoint n m
  have hsum_eq :
      (∑ k ∈ Finset.range m, ∫ y in a k..a (k + 1), f y) =
        ∫ y in a 0..a m, f y := by
    have h :=
      intervalIntegral.sum_integral_adjacent_intervals_Ico
        (μ := volume) (f := f) (a := a) (m := 0) (n := m)
        (Nat.zero_le m) ?_
    · simpa using h
    · intro k _hk
      exact intervalIntegrable_blockPsi_mul_zpow_neg_three_of_pos
        (n := n) (m := m)
        (blockIntegralEndpoint_pos n m k)
        (blockIntegralEndpoint_pos n m (k + 1))
  have hnonfinal :
      (∑ _j ∈ Finset.range (m - 1),
        (2 - 4 / blockScaleR n + 2 / (blockScaleR n) ^ 2)) ≤
        ∑ j ∈ Finset.range (m - 1), ∫ y in a j..a (j + 1), f y := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hjlt : j < m - 1 := Finset.mem_range.1 hj
    have hjm : j < m := by omega
    have hjsucc : j + 1 < m := by omega
    have hcontrib :=
      integral_blockPsi_ge_geometric_half_contribution
        (n := n) (m := m) (j := j) hjm
    simpa [a, f, blockIntegralEndpoint, hjm, hjsucc, pow_succ,
      mul_assoc, mul_comm, mul_left_comm] using hcontrib
  have hfinal :
      2 - 2 / blockScaleR n + 1 / (2 * (blockScaleR n) ^ 2) ≤
        ∫ y in a (m - 1)..a m, f y := by
    have hpred : m - 1 < m := by omega
    have hm_eq : m = (m - 1) + 1 := (Nat.sub_add_cancel hm).symm
    have hcontrib :=
      integral_blockPsi_ge_final_geometric_contribution (n := n) (m := m) hm
    have hleft :
        a (m - 1) = blockScaleR n ^ (m - 1) / 2 := by
      dsimp [a]
      unfold blockIntegralEndpoint
      rw [if_pos hpred]
    have hright :
        a m = blockScaleR n * blockScaleR n ^ (m - 1) := by
      calc
        a m = blockScaleR n ^ m := by
          simp [a]
        _ = blockScaleR n ^ ((m - 1) + 1) := by
          conv_lhs => rw [hm_eq]
        _ = blockScaleR n ^ (m - 1) * blockScaleR n := by
          rw [pow_succ]
        _ = blockScaleR n * blockScaleR n ^ (m - 1) := by
          ring
    calc
      2 - 2 / blockScaleR n + 1 / (2 * (blockScaleR n) ^ 2) ≤
          ∫ y in (blockScaleR n ^ (m - 1) / 2)..
              (blockScaleR n * blockScaleR n ^ (m - 1)),
            blockPsi n m y * y ^ (-3 : ℤ) := hcontrib
      _ = ∫ y in a (m - 1)..a m, f y := by
          rw [hleft, hright]
  have hsum_bound :
      (∑ _j ∈ Finset.range (m - 1),
          (2 - 4 / blockScaleR n + 2 / (blockScaleR n) ^ 2)) +
        (2 - 2 / blockScaleR n + 1 / (2 * (blockScaleR n) ^ 2)) ≤
          ∑ k ∈ Finset.range m, ∫ y in a k..a (k + 1), f y := by
    have hm_eq : m = (m - 1) + 1 := (Nat.sub_add_cancel hm).symm
    rw [hm_eq, Finset.sum_range_succ]
    have hfinal' :
        2 - 2 / blockScaleR n + 1 / (2 * (blockScaleR n) ^ 2) ≤
          ∫ y in a (m - 1)..a (m - 1 + 1), f y := by
      simpa [← hm_eq] using hfinal
    exact add_le_add hnonfinal hfinal'
  calc
    (∑ _j ∈ Finset.range (m - 1),
        (2 - 4 / blockScaleR n + 2 / (blockScaleR n) ^ 2)) +
      (2 - 2 / blockScaleR n + 1 / (2 * (blockScaleR n) ^ 2))
        ≤ ∑ k ∈ Finset.range m, ∫ y in a k..a (k + 1), f y := hsum_bound
    _ = ∫ y in a 0..a m, f y := hsum_eq
    _ = ∫ y in (1 / 2 : ℝ)..(blockScaleR n ^ m),
          blockPsi n m y * y ^ (-3 : ℤ) := by
          have hm_pos : 0 < m := by omega
          simp [a, f, hm_pos]

/-- Coordinatewise scale change for the integrated `ψ_B` expression. -/
theorem blockPsi_scale_integral_change_of_variables
    {n m : ℕ} {lam0 lam1 s : ℝ}
    (hlam0 : 0 < lam0) (hlam1 : 0 < lam1) (hs : 0 < s) :
    (∫ lam in lam0..lam1,
        blockPsi n m (lam * s) * lam ^ (-3 : ℤ)) =
      s ^ 2 * ∫ y in (lam0 * s)..(lam1 * s),
        blockPsi n m y * y ^ (-3 : ℤ) := by
  let f : ℝ → ℝ := fun y => blockPsi n m y * y ^ (-3 : ℤ)
  have hnot : (0 : ℝ) ∉ Set.uIcc lam0 lam1 :=
    Set.notMem_uIcc_of_lt hlam0 hlam1
  calc
    (∫ lam in lam0..lam1,
        blockPsi n m (lam * s) * lam ^ (-3 : ℤ))
        = ∫ lam in lam0..lam1, s ^ 3 * f (lam * s) := by
          refine intervalIntegral.integral_congr ?_
          intro lam hlam_mem
          by_cases hlam : lam = 0
          · exfalso
            exact hnot (by simpa [hlam] using hlam_mem)
          · dsimp [f]
            field_simp [hlam, hs.ne']
    _ = s ^ 3 * ∫ lam in lam0..lam1, f (lam * s) := by
          rw [intervalIntegral.integral_const_mul]
    _ = s ^ 2 * ∫ y in (lam0 * s)..(lam1 * s), f y := by
          have hchange :=
            intervalIntegral.mul_integral_comp_mul_right
              (a := lam0) (b := lam1) (f := f) (c := s)
          calc
            s ^ 3 * ∫ lam in lam0..lam1, f (lam * s)
                = s ^ 2 * (s * ∫ lam in lam0..lam1, f (lam * s)) := by
                  ring
            _ = s ^ 2 * ∫ y in (lam0 * s)..(lam1 * s), f y := by
                  rw [hchange]

/-- Integrability of the scale-integrated coordinatewise `ψ_B` sum on a
positive interval. -/
theorem intervalIntegrable_sum_blockPsi_scale_mul_zpow_neg_three_of_pos
    {n m : ℕ} {lam0 lam1 : ℝ} (hlam0 : 0 < lam0) (hlam1 : 0 < lam1)
    (s : Fin n → ℝ) :
    IntervalIntegrable
      (fun lam : ℝ =>
        (∑ i : Fin n, blockPsi n m (lam * s i)) * lam ^ (-3 : ℤ))
      volume lam0 lam1 := by
  have hnot : (0 : ℝ) ∉ Set.uIcc lam0 lam1 :=
    Set.notMem_uIcc_of_lt hlam0 hlam1
  have hterms :
      IntervalIntegrable
        (fun lam : ℝ =>
          ∑ i : Fin n, blockPsi n m (lam * s i) * lam ^ (-3 : ℤ))
        volume lam0 lam1 := by
    have hsum_fun :
        IntervalIntegrable
          (∑ i : Fin n, fun lam : ℝ =>
            blockPsi n m (lam * s i) * lam ^ (-3 : ℤ))
          volume lam0 lam1 :=
      IntervalIntegrable.sum
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => fun lam : ℝ =>
          blockPsi n m (lam * s i) * lam ^ (-3 : ℤ))
        (μ := volume) (a := lam0) (b := lam1)
        (by
          intro i _hi
          have hz :
              IntervalIntegrable (fun lam : ℝ => lam ^ (-3 : ℤ))
                volume lam0 lam1 :=
            intervalIntegrable_zpow (μ := volume) (a := lam0) (b := lam1)
              (n := (-3 : ℤ)) (Or.inr hnot)
          have hcont :
              ContinuousOn (fun lam : ℝ => blockPsi n m (lam * s i))
                (Set.uIcc lam0 lam1) := by
            exact (continuous_blockPsi n m).continuousOn.comp
              (continuousOn_id.mul continuousOn_const)
              (by intro lam hlam; exact Set.mem_univ _)
          simpa [mul_comm] using hz.continuousOn_mul hcont)
    convert hsum_fun using 1
    ext lam
    simp [Finset.sum_apply]
  simpa [Finset.sum_mul] using hterms

/-- At each coordinate, the finite maximum defining `ψ_B` is attained. -/
theorem exists_blockPsi_arg (n m : ℕ) (y : ℝ) :
    ∃ b ∈ nonnegativeBlockAlphabet n m,
      blockPsi n m y = 2 * b * y - b ^ 2 := by
  unfold blockPsi
  obtain ⟨b, hb, hbmax⟩ :=
    Finset.exists_mem_eq_sup'
      (by simp [nonnegativeBlockAlphabet] :
        (nonnegativeBlockAlphabet n m).Nonempty)
      (fun b : ℝ => 2 * b * y - b ^ 2)
  exact ⟨b, hb, hbmax⟩

/-- A product tuple that simultaneously attains every coordinatewise
`ψ_B(lam * s_i)` maximum. -/
theorem exists_tuple_sum_blockPsi_eq {n m : ℕ} (lam : ℝ) (s : Fin n → ℝ) :
    ∃ x : Fin n → ℝ,
      (∀ i, x i ∈ nonnegativeBlockAlphabet n m) ∧
      (∑ i : Fin n, blockPsi n m (lam * s i)) =
        ∑ i : Fin n, (2 * x i * (lam * s i) - (x i) ^ 2) := by
  classical
  let x : Fin n → ℝ := fun i =>
    Classical.choose (exists_blockPsi_arg n m (lam * s i))
  have hxmem : ∀ i, x i ∈ nonnegativeBlockAlphabet n m := by
    intro i
    exact (Classical.choose_spec
      (exists_blockPsi_arg n m (lam * s i))).1
  have hxval : ∀ i,
      blockPsi n m (lam * s i) = 2 * x i * (lam * s i) - (x i) ^ 2 := by
    intro i
    exact (Classical.choose_spec
      (exists_blockPsi_arg n m (lam * s i))).2
  refine ⟨x, hxmem, ?_⟩
  exact Finset.sum_congr rfl fun i _hi => hxval i

/-- Squared norm of a raw tuple as a coordinate sum. -/
theorem norm_tupleVector_sq_eq_sum {n : ℕ} (x : Fin n → ℝ) :
    ‖tupleVector x‖ ^ 2 = ∑ i : Fin n, (x i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [tupleVector, Real.norm_eq_abs, sq_abs]

/-- Inner product of two raw tuples as a coordinate sum. -/
theorem inner_tupleVector_eq_sum {n : ℕ} (s x : Fin n → ℝ) :
    inner ℝ (tupleVector s) (tupleVector x) =
      ∑ i : Fin n, s i * x i := by
  simp [PiLp.inner_apply, tupleVector, mul_comm]

/-- For a nonnegative unit witness, the nonnegative block maximum is
nonnegative: take any concrete nonzero nonnegative block tuple. -/
theorem nonnegativeBlockMaxCorr_nonneg {n m : ℕ}
    (hn : 0 < n) (hm : 1 ≤ m) {s : Fin n → ℝ}
    (hs_nonneg : ∀ i, 0 ≤ s i) :
    0 ≤ nonnegativeBlockMaxCorr n m s := by
  rcases nonzero_nonnegativeBlockTuples_nonempty (n := n) (m := m) hn hm with
    ⟨x, hx⟩
  rcases mem_nonzeroAsymProductTuples.1 hx with ⟨hxmem, _hxne⟩
  have hinner_nonneg :
      0 ≤ inner ℝ (tupleVector s) (tupleVector x) := by
    rw [inner_tupleVector_eq_sum]
    exact Finset.sum_nonneg fun i _hi =>
      mul_nonneg (hs_nonneg i) (nonnegativeBlockAlphabet_nonneg (hxmem i))
  have hcorr_nonneg :
      0 ≤ inner ℝ (tupleVector s) (tupleVector x) / ‖tupleVector x‖ :=
    div_nonneg hinner_nonneg (norm_nonneg _)
  exact le_trans hcorr_nonneg (tupleCorr_le_nonnegativeBlockMaxCorr hx)

/-- Unit Euclidean norm is equivalent here to unit squared-coordinate sum. -/
theorem sum_sq_eq_one_of_norm_tupleVector_eq_one {n : ℕ} {s : Fin n → ℝ}
    (hs_norm : ‖tupleVector s‖ = 1) :
    (∑ i : Fin n, (s i) ^ 2) = 1 := by
  rw [← norm_tupleVector_sq_eq_sum, hs_norm]
  norm_num

/-- A nonnegative coordinate of a unit vector is at most `1`. -/
theorem coord_le_one_of_nonneg_norm_one {n : ℕ} {s : Fin n → ℝ}
    (_hs_nonneg : ∀ i, 0 ≤ s i) (hs_norm : ‖tupleVector s‖ = 1) (i : Fin n) :
    s i ≤ 1 := by
  have hsum := sum_sq_eq_one_of_norm_tupleVector_eq_one (s := s) hs_norm
  have hterm_le :
      (s i) ^ 2 ≤ ∑ j : Fin n, (s j) ^ 2 := by
    exact Finset.single_le_sum
      (fun j _hj => sq_nonneg (s j))
      (Finset.mem_univ i)
  have hsq_le : (s i) ^ 2 ≤ 1 := by
    simpa [hsum] using hterm_le
  have hsquare : 0 ≤ (s i - 1) ^ 2 := sq_nonneg (s i - 1)
  nlinarith

/-- The cutoff used in the finite Block-Hardy proof.  Coordinates above this
threshold see the whole geometric scale range after dilation. -/
def blockHardyCutoff (n : ℕ) : ℝ :=
  (blockScaleR n * Real.exp (H n / 2))⁻¹

/-- The cutoff is positive. -/
theorem blockHardyCutoff_pos (n : ℕ) :
    0 < blockHardyCutoff n := by
  unfold blockHardyCutoff
  exact inv_pos.mpr (mul_pos
    (lt_trans zero_lt_one (one_lt_blockScaleR n))
    (Real.exp_pos _))

/-- Coordinates below the cutoff carry at most `R_n^{-2}` total squared mass. -/
theorem bad_blockHardyCutoff_sq_mass_le {n : ℕ} {s : Fin n → ℝ}
    (hs_nonneg : ∀ i, 0 ≤ s i) :
    (∑ i ∈ (Finset.univ : Finset (Fin n)).filter
        (fun i => s i < blockHardyCutoff n), (s i) ^ 2) ≤
      (blockScaleR n)⁻¹ ^ 2 := by
  let bad : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter (fun i => s i < blockHardyCutoff n)
  have hcut_pos : 0 < blockHardyCutoff n := blockHardyCutoff_pos n
  have hterm :
      ∀ i ∈ bad, (s i) ^ 2 ≤ (blockHardyCutoff n) ^ 2 := by
    intro i hi
    have hlt : s i < blockHardyCutoff n := by
      simpa [bad] using (Finset.mem_filter.1 hi).2
    have habs : |s i| ≤ |blockHardyCutoff n| := by
      rw [abs_of_nonneg (hs_nonneg i), abs_of_pos hcut_pos]
      exact hlt.le
    exact sq_le_sq.mpr habs
  have hsum_le :
      (∑ i ∈ bad, (s i) ^ 2) ≤ bad.card * (blockHardyCutoff n) ^ 2 := by
    simpa using Finset.sum_le_card_nsmul bad (fun i => (s i) ^ 2)
      ((blockHardyCutoff n) ^ 2) hterm
  have hcard : (bad.card : ℝ) ≤ (n : ℝ) := by
    have hcard_nat : bad.card ≤ n := by
      simpa using (Finset.card_le_univ bad)
    exact_mod_cast hcard_nat
  have hn_exp : (n : ℝ) ≤ Real.exp (H n) := nat_cast_le_exp_H n
  have hcut_sq :
      (blockHardyCutoff n) ^ 2 =
        (blockScaleR n)⁻¹ ^ 2 * (Real.exp (H n))⁻¹ := by
    unfold blockHardyCutoff
    have hhalf :
        Real.exp (H n / 2) ^ 2 = Real.exp (H n) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have hEinv_sq :
        (Real.exp (H n / 2))⁻¹ ^ 2 = (Real.exp (H n))⁻¹ := by
      rw [inv_pow, hhalf]
    calc
      (blockScaleR n * Real.exp (H n / 2))⁻¹ ^ 2
          = ((Real.exp (H n / 2))⁻¹ * (blockScaleR n)⁻¹) ^ 2 := by
            rw [mul_inv_rev]
      _ = (Real.exp (H n / 2))⁻¹ ^ 2 * (blockScaleR n)⁻¹ ^ 2 := by
            rw [mul_pow]
      _ = (blockScaleR n)⁻¹ ^ 2 * (Real.exp (H n))⁻¹ := by
            rw [hEinv_sq]
            ring
  have hnonneg_cut_sq : 0 ≤ (blockHardyCutoff n) ^ 2 := sq_nonneg _
  have hbad_card_bound :
      bad.card * (blockHardyCutoff n) ^ 2 ≤
        (n : ℝ) * (blockHardyCutoff n) ^ 2 := by
    exact mul_le_mul_of_nonneg_right hcard hnonneg_cut_sq
  have hn_cut_bound :
      (n : ℝ) * (blockHardyCutoff n) ^ 2 ≤ (blockScaleR n)⁻¹ ^ 2 := by
    rw [hcut_sq]
    have hexp_pos : 0 < Real.exp (H n) := Real.exp_pos _
    calc
      (n : ℝ) * ((blockScaleR n)⁻¹ ^ 2 * (Real.exp (H n))⁻¹)
          ≤ Real.exp (H n) *
              ((blockScaleR n)⁻¹ ^ 2 * (Real.exp (H n))⁻¹) := by
            exact mul_le_mul_of_nonneg_right hn_exp (by positivity)
      _ = (blockScaleR n)⁻¹ ^ 2 := by
            field_simp [hexp_pos.ne']
  exact le_trans hsum_le (le_trans hbad_card_bound hn_cut_bound)

/-- The coordinatewise `ψ_B` sum is the quadratic payoff of its maximizing
product tuple. -/
theorem exists_tuple_sum_blockPsi_eq_quadratic {n m : ℕ}
    (lam : ℝ) (s : Fin n → ℝ) :
    ∃ x : Fin n → ℝ,
      (∀ i, x i ∈ nonnegativeBlockAlphabet n m) ∧
      (∑ i : Fin n, blockPsi n m (lam * s i)) =
        2 * lam * inner ℝ (tupleVector s) (tupleVector x) -
          ‖tupleVector x‖ ^ 2 := by
  rcases exists_tuple_sum_blockPsi_eq (n := n) (m := m) lam s with
    ⟨x, hxmem, hxsum⟩
  refine ⟨x, hxmem, ?_⟩
  calc
    (∑ i : Fin n, blockPsi n m (lam * s i))
        = ∑ i : Fin n, (2 * x i * (lam * s i) - (x i) ^ 2) := hxsum
    _ = 2 * lam * (∑ i : Fin n, s i * x i) -
          ∑ i : Fin n, (x i) ^ 2 := by
          rw [Finset.sum_sub_distrib]
          congr 1
          calc
            (∑ i : Fin n, 2 * x i * (lam * s i))
                = ∑ i : Fin n, 2 * lam * (s i * x i) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _hi
                  ring
            _ = 2 * lam * (∑ i : Fin n, s i * x i) := by
                  rw [Finset.mul_sum]
    _ = 2 * lam * inner ℝ (tupleVector s) (tupleVector x) -
          ‖tupleVector x‖ ^ 2 := by
          rw [inner_tupleVector_eq_sum, norm_tupleVector_sq_eq_sum]

/-- A coordinatewise `ψ` maximizer is nonzero whenever the `ψ` sum is
positive. -/
theorem tuple_ne_zero_of_sum_blockPsi_pos {n m : ℕ} {lam : ℝ}
    {s x : Fin n → ℝ}
    (hxsum :
      (∑ i : Fin n, blockPsi n m (lam * s i)) =
        2 * lam * inner ℝ (tupleVector s) (tupleVector x) -
          ‖tupleVector x‖ ^ 2)
    (hsum_pos : 0 < ∑ i : Fin n, blockPsi n m (lam * s i)) :
    tupleVector x ≠ 0 := by
  intro hxzero
  have hnorm_zero : ‖tupleVector x‖ = 0 := by simp [hxzero]
  have hinner_zero : inner ℝ (tupleVector s) (tupleVector x) = 0 := by
    simp [hxzero]
  have hsum_eq_zero :
      (∑ i : Fin n, blockPsi n m (lam * s i)) = 0 := by
    rw [hxsum, hinner_zero, hnorm_zero]
    ring
  linarith

/-- The finite variational inequality behind the Block-Hardy proof:
coordinatewise maximization is controlled by the squared global maximum
correlation. -/
theorem sum_blockPsi_le_lam_sq_mul_maxCorr_sq {n m : ℕ}
    {lam : ℝ} (hlam : 0 ≤ lam) (s : Fin n → ℝ) :
    (∑ i : Fin n, blockPsi n m (lam * s i)) ≤
      lam ^ 2 * (nonnegativeBlockMaxCorr n m s) ^ 2 := by
  rcases exists_tuple_sum_blockPsi_eq_quadratic (n := n) (m := m) lam s with
    ⟨x, hxmem, hxsum⟩
  by_cases hsum_pos : 0 < ∑ i : Fin n, blockPsi n m (lam * s i)
  · have hxne : tupleVector x ≠ 0 :=
      tuple_ne_zero_of_sum_blockPsi_pos hxsum hsum_pos
    have hx_tuple : x ∈ nonzeroAsymProductTuples n (nonnegativeBlockAlphabet n m) :=
      mem_nonzeroAsymProductTuples.2 ⟨hxmem, hxne⟩
    have hxnorm_pos : 0 < ‖tupleVector x‖ := norm_pos_iff.mpr hxne
    have hcorr_le :
        inner ℝ (tupleVector s) (tupleVector x) / ‖tupleVector x‖ ≤
          nonnegativeBlockMaxCorr n m s :=
      tupleCorr_le_nonnegativeBlockMaxCorr hx_tuple
    have hinner_le :
        inner ℝ (tupleVector s) (tupleVector x) ≤
          nonnegativeBlockMaxCorr n m s * ‖tupleVector x‖ := by
      exact (div_le_iff₀ hxnorm_pos).1 hcorr_le
    let r : ℝ := ‖tupleVector x‖
    let M : ℝ := nonnegativeBlockMaxCorr n m s
    have hpayoff_le :
        (∑ i : Fin n, blockPsi n m (lam * s i)) ≤
          2 * lam * (M * r) - r ^ 2 := by
      rw [hxsum]
      dsimp [M, r] at hinner_le ⊢
      have hmul :=
        mul_le_mul_of_nonneg_left hinner_le (by positivity : 0 ≤ 2 * lam)
      linarith
    have hquad :
        2 * lam * (M * r) - r ^ 2 ≤ lam ^ 2 * M ^ 2 := by
      have hsquare : 0 ≤ (r - lam * M) ^ 2 := sq_nonneg (r - lam * M)
      nlinarith
    exact le_trans hpayoff_le hquad
  · have hsum_nonpos :
        (∑ i : Fin n, blockPsi n m (lam * s i)) ≤ 0 := le_of_not_gt hsum_pos
    have hrhs_nonneg :
        0 ≤ lam ^ 2 * (nonnegativeBlockMaxCorr n m s) ^ 2 := by
      positivity
    exact le_trans hsum_nonpos hrhs_nonneg

/-- Integrated version of the finite variational inequality:
`∫ Σ ψ(λs_i) λ^{-3} ≤ M_B(s)^2 log(λ₁/λ₀)`. -/
theorem integral_sum_blockPsi_scale_le_log_mul_maxCorr_sq
    {n m : ℕ} {lam0 lam1 : ℝ}
    (hlam0 : 0 < lam0) (hlam1 : 0 < lam1) (hle : lam0 ≤ lam1)
    (s : Fin n → ℝ) :
    (∫ lam in lam0..lam1,
        (∑ i : Fin n, blockPsi n m (lam * s i)) * lam ^ (-3 : ℤ)) ≤
      (nonnegativeBlockMaxCorr n m s) ^ 2 * Real.log (lam1 / lam0) := by
  let M : ℝ := nonnegativeBlockMaxCorr n m s
  have hnot : (0 : ℝ) ∉ Set.uIcc lam0 lam1 :=
    Set.notMem_uIcc_of_lt hlam0 hlam1
  have hleft :
      IntervalIntegrable
        (fun lam : ℝ =>
          (∑ i : Fin n, blockPsi n m (lam * s i)) * lam ^ (-3 : ℤ))
        volume lam0 lam1 :=
    intervalIntegrable_sum_blockPsi_scale_mul_zpow_neg_three_of_pos
      (n := n) (m := m) hlam0 hlam1 s
  have hright :
      IntervalIntegrable (fun lam : ℝ => M ^ 2 * lam⁻¹)
        volume lam0 lam1 := by
    simpa using
      ((intervalIntegrable_zpow
        (μ := volume) (a := lam0) (b := lam1) (n := (-1 : ℤ))
        (Or.inr hnot)).const_mul (M ^ 2))
  have hmono :
      (∫ lam in lam0..lam1,
          (∑ i : Fin n, blockPsi n m (lam * s i)) * lam ^ (-3 : ℤ)) ≤
        ∫ lam in lam0..lam1, M ^ 2 * lam⁻¹ := by
    refine intervalIntegral.integral_mono_on
      (μ := volume) hle hleft hright ?_
    intro lam hlam_mem
    have hlam_pos : 0 < lam := lt_of_lt_of_le hlam0 hlam_mem.1
    have hsum := sum_blockPsi_le_lam_sq_mul_maxCorr_sq
      (n := n) (m := m) (lam := lam) hlam_pos.le s
    have hzpow_nonneg : 0 ≤ lam ^ (-3 : ℤ) := by positivity
    calc
      (∑ i : Fin n, blockPsi n m (lam * s i)) * lam ^ (-3 : ℤ)
          ≤ (lam ^ 2 * M ^ 2) * lam ^ (-3 : ℤ) := by
            exact mul_le_mul_of_nonneg_right hsum hzpow_nonneg
      _ = M ^ 2 * lam⁻¹ := by
            dsimp [M]
            field_simp [hlam_pos.ne']
  calc
    (∫ lam in lam0..lam1,
        (∑ i : Fin n, blockPsi n m (lam * s i)) * lam ^ (-3 : ℤ))
        ≤ ∫ lam in lam0..lam1, M ^ 2 * lam⁻¹ := hmono
    _ = M ^ 2 * Real.log (lam1 / lam0) := by
          rw [intervalIntegral.integral_const_mul,
            integral_inv_of_pos hlam0 hlam1]

/-- The explicit scale contribution appearing on the left of the finite
Block-Hardy sandwich. -/
def blockHardyGeometricContribution (n m : ℕ) : ℝ :=
  (∑ _j ∈ Finset.range (m - 1),
    (2 - 4 / blockScaleR n + 2 / (blockScaleR n) ^ 2)) +
  (2 - 2 / blockScaleR n + 1 / (2 * (blockScaleR n) ^ 2))

/-- The full left side of the finite Block-Hardy sandwich. -/
def blockHardySandwichLeft (n m : ℕ) : ℝ :=
  (1 - (blockScaleR n)⁻¹ ^ 2) *
    blockHardyGeometricContribution n m

/-- The logarithmic denominator used in the finite Block-Hardy sandwich. -/
def blockHardyLogDenom (n m : ℕ) : ℝ :=
  Real.log (2 * blockScaleR n ^ (m + 1) * Real.exp (H n / 2))

/-- Concrete finite Block-Hardy sandwich before asymptotic simplification. -/
theorem blockHardy_finite_sandwich {n m : ℕ} (hm : 1 ≤ m)
    {s : Fin n → ℝ} (hs_nonneg : ∀ i, 0 ≤ s i)
    (hs_norm : ‖tupleVector s‖ = 1) :
    (1 - (blockScaleR n)⁻¹ ^ 2) *
        ((∑ _j ∈ Finset.range (m - 1),
            (2 - 4 / blockScaleR n + 2 / (blockScaleR n) ^ 2)) +
          (2 - 2 / blockScaleR n + 1 / (2 * (blockScaleR n) ^ 2))) ≤
      (nonnegativeBlockMaxCorr n m s) ^ 2 *
        Real.log (2 * blockScaleR n ^ (m + 1) * Real.exp (H n / 2)) := by
  let good : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter
      (fun i => blockHardyCutoff n ≤ s i)
  let bad : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter
      (fun i => s i < blockHardyCutoff n)
  let G : ℝ :=
    (∑ _j ∈ Finset.range (m - 1),
      (2 - 4 / blockScaleR n + 2 / (blockScaleR n) ^ 2)) +
    (2 - 2 / blockScaleR n + 1 / (2 * (blockScaleR n) ^ 2))
  let lam0 : ℝ := 1 / 2
  let lam1 : ℝ := blockScaleR n ^ (m + 1) * Real.exp (H n / 2)
  have hR_pos : 0 < blockScaleR n := lt_trans zero_lt_one (one_lt_blockScaleR n)
  have hcut_pos : 0 < blockHardyCutoff n := blockHardyCutoff_pos n
  have hlam0_pos : 0 < lam0 := by norm_num [lam0]
  have hlam1_pos : 0 < lam1 := by
    dsimp [lam1]
    positivity
  have hlam_le : lam0 ≤ lam1 := by
    dsimp [lam0, lam1]
    have hRpow : 1 ≤ blockScaleR n ^ (m + 1) :=
      one_le_blockScaleR_pow n (m + 1)
    have hexp_ge : 1 ≤ Real.exp (H n / 2) := by
      have hH_nonneg : 0 ≤ H n := by
        by_cases hn : n = 0
        · simp [hn, H]
        · exact (H_pos (Nat.pos_of_ne_zero hn)).le
      have hnonneg : 0 ≤ H n / 2 := by positivity
      simpa using Real.one_le_exp_iff.mpr hnonneg
    have hone : (1 : ℝ) ≤ blockScaleR n ^ (m + 1) * Real.exp (H n / 2) := by
      nlinarith
    nlinarith
  have hsum_sq_one :
      (∑ i : Fin n, (s i) ^ 2) = 1 :=
    sum_sq_eq_one_of_norm_tupleVector_eq_one (s := s) hs_norm
  have hbad_mass :
      (∑ i ∈ bad, (s i) ^ 2) ≤ (blockScaleR n)⁻¹ ^ 2 := by
    simpa [bad, blockHardyCutoff] using
      bad_blockHardyCutoff_sq_mass_le (n := n) (s := s) hs_nonneg
  have hsplit :
      (∑ i ∈ good, (s i) ^ 2) +
        (∑ i ∈ bad, (s i) ^ 2) =
          ∑ i : Fin n, (s i) ^ 2 := by
    have h :=
      Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin n)))
        (p := fun i : Fin n => blockHardyCutoff n ≤ s i)
        (f := fun i : Fin n => (s i) ^ 2)
    simpa [good, bad, not_le] using h
  have hgood_mass :
      1 - (blockScaleR n)⁻¹ ^ 2 ≤ ∑ i ∈ good, (s i) ^ 2 := by
    nlinarith [hsplit, hsum_sq_one, hbad_mass]
  have hG_nonneg : 0 ≤ G := by
    let a : ℝ := (blockScaleR n)⁻¹
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      positivity
    have ha_le_one : a ≤ 1 := by
      dsimp [a]
      exact inv_le_one_of_one_le₀ (one_lt_blockScaleR n).le
    have hnonfinal :
        0 ≤ 2 - 4 / blockScaleR n + 2 / (blockScaleR n) ^ 2 := by
      have heq :
          2 - 4 / blockScaleR n + 2 / (blockScaleR n) ^ 2 =
            2 * (1 - a) ^ 2 := by
        dsimp [a]
        field_simp [hR_pos.ne']
        ring
      rw [heq]
      positivity
    have hfinal :
        0 ≤ 2 - 2 / blockScaleR n + 1 / (2 * (blockScaleR n) ^ 2) := by
      have heq :
          2 - 2 / blockScaleR n + 1 / (2 * (blockScaleR n) ^ 2) =
            2 - 2 * a + a ^ 2 / 2 := by
        dsimp [a]
        field_simp [hR_pos.ne']
      rw [heq]
      nlinarith [sq_nonneg a]
    dsimp [G]
    exact add_nonneg
      (Finset.sum_nonneg (fun _j _hj => hnonfinal))
      hfinal
  have hlower_terms :
      G * (∑ i ∈ good, (s i) ^ 2) ≤
        ∑ i ∈ good,
          s i ^ 2 * ∫ y in (1 / 2 : ℝ)..(blockScaleR n ^ m),
            blockPsi n m y * y ^ (-3 : ℤ) := by
    have htotal :=
      integral_blockPsi_ge_geometric_total_contribution (n := n) (m := m) hm
    calc
      G * (∑ i ∈ good, (s i) ^ 2)
          = (∑ i ∈ good, (s i) ^ 2) * G := by ring
      _ = ∑ i ∈ good, (s i) ^ 2 * G := by
            rw [Finset.sum_mul]
      _ ≤ ∑ i ∈ good,
          s i ^ 2 * ∫ y in (1 / 2 : ℝ)..(blockScaleR n ^ m),
            blockPsi n m y * y ^ (-3 : ℤ) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hs_sq_nonneg : 0 ≤ (s i) ^ 2 := sq_nonneg _
            exact mul_le_mul_of_nonneg_left (by simpa [G] using htotal) hs_sq_nonneg
  have hgood_to_lam :
      ∀ i ∈ good,
        s i ^ 2 * ∫ y in (1 / 2 : ℝ)..(blockScaleR n ^ m),
            blockPsi n m y * y ^ (-3 : ℤ) ≤
          ∫ lam in lam0..lam1,
            blockPsi n m (lam * s i) * lam ^ (-3 : ℤ) := by
    intro i hi
    have hgood_i : blockHardyCutoff n ≤ s i := by
      simpa [good] using (Finset.mem_filter.1 hi).2
    have hs_pos : 0 < s i := lt_of_lt_of_le hcut_pos hgood_i
    have hchange :=
      blockPsi_scale_integral_change_of_variables
        (n := n) (m := m) (lam0 := lam0) (lam1 := lam1)
        (s := s i) hlam0_pos hlam1_pos hs_pos
    have hleft_endpoint :
        lam0 * s i ≤ (1 / 2 : ℝ) := by
      dsimp [lam0]
      have hsi_le : s i ≤ 1 :=
        coord_le_one_of_nonneg_norm_one hs_nonneg hs_norm i
      nlinarith
    have hright_endpoint :
        blockScaleR n ^ m ≤ lam1 * s i := by
      dsimp [lam1, blockHardyCutoff] at hgood_i ⊢
      have hprod_pos :
          0 < blockScaleR n * Real.exp (H n / 2) := by positivity
      have hmul :=
        mul_le_mul_of_nonneg_left hgood_i
          (by positivity : 0 ≤ blockScaleR n ^ (m + 1) * Real.exp (H n / 2))
      have hleft_eq :
          blockScaleR n ^ m =
            (blockScaleR n ^ (m + 1) * Real.exp (H n / 2)) *
              (blockScaleR n * Real.exp (H n / 2))⁻¹ := by
        field_simp [hR_pos.ne', (Real.exp_pos (H n / 2)).ne']
        rw [pow_succ]
      calc
        blockScaleR n ^ m
            = (blockScaleR n ^ (m + 1) * Real.exp (H n / 2)) *
                (blockScaleR n * Real.exp (H n / 2))⁻¹ := hleft_eq
        _ ≤ (blockScaleR n ^ (m + 1) * Real.exp (H n / 2)) * s i := hmul
    have hnonneg :
        0 ≤ᵐ[volume.restrict (Set.Ioc (lam0 * s i) (lam1 * s i))]
          fun y : ℝ => blockPsi n m y * y ^ (-3 : ℤ) := by
      rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine ae_of_all _ ?_
      intro y hy
      have hy_pos : 0 < y := lt_trans (by positivity : 0 < lam0 * s i) hy.1
      exact mul_nonneg (blockPsi_nonneg n m y) (by positivity)
    have hint :
        IntervalIntegrable
          (fun y : ℝ => blockPsi n m y * y ^ (-3 : ℤ))
          volume (lam0 * s i) (lam1 * s i) :=
      intervalIntegrable_blockPsi_mul_zpow_neg_three_of_pos
        (by positivity) (by positivity)
    have hmono :=
      intervalIntegral.integral_mono_interval
        (μ := volume)
        (f := fun y : ℝ => blockPsi n m y * y ^ (-3 : ℤ))
        hleft_endpoint (by
          have hpow_ge : (1 / 2 : ℝ) ≤ blockScaleR n ^ m := by
            have hone : (1 : ℝ) ≤ blockScaleR n ^ m :=
              one_le_blockScaleR_pow n m
            nlinarith
          exact hpow_ge) hright_endpoint hnonneg hint
    calc
      s i ^ 2 * ∫ y in (1 / 2 : ℝ)..(blockScaleR n ^ m),
          blockPsi n m y * y ^ (-3 : ℤ)
          ≤ s i ^ 2 *
              ∫ y in (lam0 * s i)..(lam1 * s i),
                blockPsi n m y * y ^ (-3 : ℤ) := by
            exact mul_le_mul_of_nonneg_left hmono (sq_nonneg _)
      _ = ∫ lam in lam0..lam1,
            blockPsi n m (lam * s i) * lam ^ (-3 : ℤ) := by
            rw [hchange]
  have hsum_good_le_all :
      (∑ i ∈ good,
          ∫ lam in lam0..lam1,
            blockPsi n m (lam * s i) * lam ^ (-3 : ℤ)) ≤
        ∫ lam in lam0..lam1,
          (∑ i : Fin n, blockPsi n m (lam * s i)) * lam ^ (-3 : ℤ) := by
    have hterm_int :
        ∀ i ∈ good,
          IntervalIntegrable
            (fun lam : ℝ => blockPsi n m (lam * s i) * lam ^ (-3 : ℤ))
            volume lam0 lam1 := by
      intro i _hi
      have hz :
          IntervalIntegrable (fun lam : ℝ => lam ^ (-3 : ℤ))
            volume lam0 lam1 :=
        intervalIntegrable_zpow (μ := volume) (a := lam0) (b := lam1)
          (n := (-3 : ℤ))
          (Or.inr (Set.notMem_uIcc_of_lt hlam0_pos hlam1_pos))
      have hcont :
          ContinuousOn (fun lam : ℝ => blockPsi n m (lam * s i))
            (Set.uIcc lam0 lam1) := by
        exact (continuous_blockPsi n m).continuousOn.comp
          (continuousOn_id.mul continuousOn_const)
          (by intro lam hlam; exact Set.mem_univ _)
      simpa [mul_comm] using hz.continuousOn_mul hcont
    have hgood_int :
        IntervalIntegrable
          (fun lam : ℝ =>
            (∑ i ∈ good, blockPsi n m (lam * s i)) * lam ^ (-3 : ℤ))
          volume lam0 lam1 := by
      have hsum_fun :
          IntervalIntegrable
            (∑ i ∈ good, fun lam : ℝ =>
              blockPsi n m (lam * s i) * lam ^ (-3 : ℤ))
            volume lam0 lam1 :=
        IntervalIntegrable.sum
          (s := good)
          (f := fun i : Fin n => fun lam : ℝ =>
            blockPsi n m (lam * s i) * lam ^ (-3 : ℤ))
          (μ := volume) (a := lam0) (b := lam1) hterm_int
      convert hsum_fun using 1
      ext lam
      simp [Finset.sum_apply, Finset.sum_mul]
    have hfull_int :
        IntervalIntegrable
          (fun lam : ℝ =>
            (∑ i : Fin n, blockPsi n m (lam * s i)) * lam ^ (-3 : ℤ))
          volume lam0 lam1 :=
      intervalIntegrable_sum_blockPsi_scale_mul_zpow_neg_three_of_pos
        (n := n) (m := m) hlam0_pos hlam1_pos s
    have hgood_integral_eq :
        (∑ i ∈ good,
          ∫ lam in lam0..lam1,
            blockPsi n m (lam * s i) * lam ^ (-3 : ℤ)) =
          ∫ lam in lam0..lam1,
            (∑ i ∈ good, blockPsi n m (lam * s i)) * lam ^ (-3 : ℤ) := by
      have hsum :=
        intervalIntegral.integral_finset_sum
          (μ := volume) (a := lam0) (b := lam1)
          (s := good)
          (f := fun i : Fin n => fun lam : ℝ =>
            blockPsi n m (lam * s i) * lam ^ (-3 : ℤ))
          hterm_int
      rw [← hsum]
      congr 1
      ext lam
      simp [Finset.sum_mul]
    have hmono :
        (∫ lam in lam0..lam1,
            (∑ i ∈ good, blockPsi n m (lam * s i)) * lam ^ (-3 : ℤ)) ≤
          ∫ lam in lam0..lam1,
            (∑ i : Fin n, blockPsi n m (lam * s i)) * lam ^ (-3 : ℤ) := by
      refine intervalIntegral.integral_mono_on
        (μ := volume) hlam_le hgood_int hfull_int ?_
      intro lam hlam_mem
      have hlam_pos : 0 < lam := lt_of_lt_of_le hlam0_pos hlam_mem.1
      have hzpow_nonneg : 0 ≤ lam ^ (-3 : ℤ) := by positivity
      have hsum_le :
          (∑ i ∈ good, blockPsi n m (lam * s i)) ≤
            ∑ i : Fin n, blockPsi n m (lam * s i) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by intro i hi; simp)
          (by
            intro i hi_univ hinot
            exact blockPsi_nonneg n m (lam * s i))
      exact mul_le_mul_of_nonneg_right hsum_le hzpow_nonneg
    rw [hgood_integral_eq]
    exact hmono
  have hupper :=
    integral_sum_blockPsi_scale_le_log_mul_maxCorr_sq
      (n := n) (m := m) (lam0 := lam0) (lam1 := lam1)
      hlam0_pos hlam1_pos hlam_le s
  have hleft_le_upper :
      G * (∑ i ∈ good, (s i) ^ 2) ≤
        (nonnegativeBlockMaxCorr n m s) ^ 2 * Real.log (lam1 / lam0) := by
    calc
      G * (∑ i ∈ good, (s i) ^ 2)
          ≤ ∑ i ∈ good,
              s i ^ 2 * ∫ y in (1 / 2 : ℝ)..(blockScaleR n ^ m),
                blockPsi n m y * y ^ (-3 : ℤ) := hlower_terms
      _ ≤ ∑ i ∈ good,
          ∫ lam in lam0..lam1,
            blockPsi n m (lam * s i) * lam ^ (-3 : ℤ) := by
            exact Finset.sum_le_sum hgood_to_lam
      _ ≤ ∫ lam in lam0..lam1,
          (∑ i : Fin n, blockPsi n m (lam * s i)) * lam ^ (-3 : ℤ) :=
            hsum_good_le_all
      _ ≤ (nonnegativeBlockMaxCorr n m s) ^ 2 * Real.log (lam1 / lam0) := hupper
  have hmass_times :
      (1 - (blockScaleR n)⁻¹ ^ 2) * G ≤
        G * (∑ i ∈ good, (s i) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hgood_mass hG_nonneg]
  have hlog_eq :
      Real.log (lam1 / lam0) =
        Real.log (2 * blockScaleR n ^ (m + 1) * Real.exp (H n / 2)) := by
    dsimp [lam0, lam1]
    ring_nf
  calc
    (1 - (blockScaleR n)⁻¹ ^ 2) * G
        ≤ G * (∑ i ∈ good, (s i) ^ 2) := hmass_times
    _ ≤ (nonnegativeBlockMaxCorr n m s) ^ 2 * Real.log (lam1 / lam0) :=
        hleft_le_upper
    _ = (nonnegativeBlockMaxCorr n m s) ^ 2 *
        Real.log (2 * blockScaleR n ^ (m + 1) * Real.exp (H n / 2)) := by
          rw [hlog_eq]

/-- The finite sandwich contribution tends to its ideal value `2m`. -/
theorem tendsto_blockHardySandwichLeft {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => blockHardySandwichLeft n m) atTop
      (𝓝 (2 * (m : ℝ))) := by
  have hinv :
      Tendsto (fun n : ℕ => (blockScaleR n)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_inv_atTop_zero.comp blockScaleR_tendsto_atTop
  have hinv_sq :
      Tendsto (fun n : ℕ => (blockScaleR n)⁻¹ ^ 2) atTop
        (𝓝 (0 : ℝ)) := by
    simpa using hinv.pow 2
  have hnonfinal :
      Tendsto
        (fun n : ℕ =>
          2 - 4 / blockScaleR n + 2 / (blockScaleR n) ^ 2)
        atTop (𝓝 (2 : ℝ)) := by
    have h4 :
        Tendsto (fun n : ℕ => 4 * (blockScaleR n)⁻¹) atTop
          (𝓝 (0 : ℝ)) := by
      simpa using hinv.const_mul (4 : ℝ)
    have h2sq :
        Tendsto (fun n : ℕ => 2 * (blockScaleR n)⁻¹ ^ 2) atTop
          (𝓝 (0 : ℝ)) := by
      simpa using hinv_sq.const_mul (2 : ℝ)
    have hconst2 :
        Tendsto (fun _n : ℕ => (2 : ℝ)) atTop (𝓝 (2 : ℝ)) :=
      tendsto_const_nhds
    have hlim :
        Tendsto
          (fun n : ℕ =>
            (2 : ℝ) - 4 * (blockScaleR n)⁻¹ +
              2 * (blockScaleR n)⁻¹ ^ 2)
          atTop (𝓝 (2 - 0 + 0 : ℝ)) :=
      (hconst2.sub h4).add h2sq
    simpa [div_eq_mul_inv, inv_pow, pow_two, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm, mul_comm, mul_left_comm,
      mul_assoc] using hlim
  have hfinal :
      Tendsto
        (fun n : ℕ =>
          2 - 2 / blockScaleR n + 1 / (2 * (blockScaleR n) ^ 2))
        atTop (𝓝 (2 : ℝ)) := by
    have h2 :
        Tendsto (fun n : ℕ => 2 * (blockScaleR n)⁻¹) atTop
          (𝓝 (0 : ℝ)) := by
      simpa using hinv.const_mul (2 : ℝ)
    have hhalf_sq :
        Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ * (blockScaleR n)⁻¹ ^ 2)
          atTop (𝓝 (0 : ℝ)) := by
      simpa using hinv_sq.const_mul ((2 : ℝ)⁻¹)
    have hconst2 :
        Tendsto (fun _n : ℕ => (2 : ℝ)) atTop (𝓝 (2 : ℝ)) :=
      tendsto_const_nhds
    have hlim :
        Tendsto
          (fun n : ℕ =>
            (2 : ℝ) - 2 * (blockScaleR n)⁻¹ +
              (2 : ℝ)⁻¹ * (blockScaleR n)⁻¹ ^ 2)
          atTop (𝓝 (2 - 0 + 0 : ℝ)) :=
      (hconst2.sub h2).add hhalf_sq
    simpa [div_eq_mul_inv, inv_pow, pow_two, one_div, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm, mul_comm, mul_left_comm,
      mul_assoc] using hlim
  have hgeom :
      Tendsto (fun n : ℕ => blockHardyGeometricContribution n m) atTop
        (𝓝 (2 * (m : ℝ))) := by
    have hsum :
        Tendsto
          (fun n : ℕ =>
            ∑ _j ∈ Finset.range (m - 1),
              (2 - 4 / blockScaleR n + 2 / (blockScaleR n) ^ 2))
          atTop (𝓝 (((m - 1 : ℕ) : ℝ) * 2)) := by
      have hmul := hnonfinal.const_mul (((m - 1 : ℕ) : ℝ))
      convert hmul using 1
      ext n
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    have hlim :
        Tendsto (fun n : ℕ => blockHardyGeometricContribution n m) atTop
          (𝓝 ((((m - 1 : ℕ) : ℝ) * 2) + 2)) := by
      simpa [blockHardyGeometricContribution] using hsum.add hfinal
    have hm_cast :
        (((m - 1 : ℕ) : ℝ) * 2 + 2) = 2 * (m : ℝ) := by
      have hm' : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
        exact_mod_cast (Nat.sub_add_cancel hm)
      nlinarith
    simpa [hm_cast] using hlim
  have hfactor :
      Tendsto (fun n : ℕ => 1 - (blockScaleR n)⁻¹ ^ 2) atTop
        (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hinv_sq
  have hlim := hfactor.mul hgeom
  simpa [blockHardySandwichLeft, one_mul] using hlim

/-- Eventual lower estimate for the finite sandwich contribution. -/
theorem eventually_blockHardySandwichLeft_ge {m : ℕ} (hm : 1 ≤ m)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      2 * (m : ℝ) - η ≤ blockHardySandwichLeft n m := by
  have hlim := tendsto_blockHardySandwichLeft (m := m) hm
  have hnhds : Set.Ioi (2 * (m : ℝ) - η) ∈ 𝓝 (2 * (m : ℝ)) :=
    Ioi_mem_nhds (by linarith)
  exact (hlim.eventually hnhds).mono fun n hn => hn.le

/-- The logarithm of the block ratio is negligible against the harmonic
scale. -/
theorem eventually_log_blockScaleR_le_mul_H {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (blockScaleR n) ≤ η * H n := by
  let C : ℝ := Real.log 2 + 1
  have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hC_pos : 0 < C := by
    dsimp [C]
    linarith
  have hηsq_pos : 0 < η ^ 2 := sq_pos_of_pos hη
  have hlarge :
      ∀ᶠ n : ℕ in atTop, max (1 : ℝ) (C / η ^ 2) ≤ H n :=
    H_tendsto_atTop.eventually_ge_atTop (max (1 : ℝ) (C / η ^ 2))
  filter_upwards [hlarge, Filter.eventually_ge_atTop (1 : ℕ)] with n hHlarge hn1
  have hnpos : 0 < n := Nat.succ_le_iff.mp hn1
  have hHpos : 0 < H n := H_pos hnpos
  have hHge1 : (1 : ℝ) ≤ H n := le_trans (le_max_left _ _) hHlarge
  have hHgeC : C / η ^ 2 ≤ H n := le_trans (le_max_right _ _) hHlarge
  have hlog_arg :
      Real.log ((n : ℝ) + 2) ≤ Real.log 2 + H n := by
    have harg_pos : 0 < (n : ℝ) + 2 := by positivity
    have hn1_pos : 0 < (n : ℝ) + 1 := by positivity
    have hle_arg : (n : ℝ) + 2 ≤ 2 * ((n : ℝ) + 1) := by
      have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      nlinarith
    have hlog_le :
        Real.log ((n : ℝ) + 2) ≤ Real.log (2 * ((n : ℝ) + 1)) :=
      Real.log_le_log harg_pos hle_arg
    calc
      Real.log ((n : ℝ) + 2)
          ≤ Real.log (2 * ((n : ℝ) + 1)) := hlog_le
      _ = Real.log 2 + Real.log ((n : ℝ) + 1) := by
            rw [Real.log_mul (by norm_num) hn1_pos.ne']
      _ ≤ Real.log 2 + H n := by
            exact add_le_add le_rfl (log_nat_add_one_le_H n)
  have hsqrt_le :
      Real.sqrt (Real.log ((n : ℝ) + 2)) ≤
        Real.sqrt (Real.log 2 + H n) :=
    Real.sqrt_le_sqrt hlog_arg
  have hsqrt_bound :
      Real.sqrt (Real.log 2 + H n) ≤ η * H n := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hC_bound : Real.log 2 + H n ≤ C * H n := by
        dsimp [C]
        nlinarith [hlog2_nonneg, hHge1]
      have hC_le : C ≤ η ^ 2 * H n := by
        have h := (div_le_iff₀ hηsq_pos).1 hHgeC
        simpa [mul_comm] using h
      have hCH_le : C * H n ≤ (η * H n) ^ 2 := by
        nlinarith [hC_le, hHpos.le]
      exact le_trans hC_bound hCH_le
  exact le_trans (by simpa using hsqrt_le) hsqrt_bound

/-- The logarithmic denominator is asymptotically at most `(1/2 + η) H_n`. -/
theorem eventually_blockHardyLogDenom_le {m : ℕ} {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      blockHardyLogDenom n m ≤ ((1 : ℝ) / 2 + η) * H n := by
  let η₁ : ℝ := η / (2 * ((m + 1 : ℕ) : ℝ))
  have hm1_pos : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hη₁ : 0 < η₁ := by
    dsimp [η₁]
    positivity
  have hlogR_event := eventually_log_blockScaleR_le_mul_H hη₁
  have hlog2_event :
      ∀ᶠ n : ℕ in atTop, (2 * Real.log 2 / η) ≤ H n :=
    H_tendsto_atTop.eventually_ge_atTop (2 * Real.log 2 / η)
  filter_upwards [hlogR_event, hlog2_event, Filter.eventually_ge_atTop (1 : ℕ)] with
    n hlogR hHlog2 hn1
  have hnpos : 0 < n := Nat.succ_le_iff.mp hn1
  have hHpos : 0 < H n := H_pos hnpos
  have hR_pos : 0 < blockScaleR n := lt_trans zero_lt_one (one_lt_blockScaleR n)
  have hlog_eq :
      blockHardyLogDenom n m =
        Real.log 2 + ((m + 1 : ℕ) : ℝ) * Real.log (blockScaleR n) +
          H n / 2 := by
    unfold blockHardyLogDenom
    have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
    have hpow_ne : blockScaleR n ^ (m + 1) ≠ 0 :=
      pow_ne_zero _ hR_pos.ne'
    have hexp_ne : Real.exp (H n / 2) ≠ 0 :=
      (Real.exp_pos (H n / 2)).ne'
    rw [mul_assoc]
    rw [Real.log_mul h2_ne (mul_ne_zero hpow_ne hexp_ne)]
    rw [Real.log_mul hpow_ne hexp_ne, Real.log_pow, Real.log_exp]
    ring
  have hlog2_le : Real.log 2 ≤ (η / 2) * H n := by
    have hmul := mul_le_mul_of_nonneg_left hHlog2 (by positivity : 0 ≤ η / 2)
    have hleft :
        (η / 2) * (2 * Real.log 2 / η) = Real.log 2 := by
      field_simp [hη.ne']
    calc
      Real.log 2 = (η / 2) * (2 * Real.log 2 / η) := hleft.symm
      _ ≤ (η / 2) * H n := hmul
  have hscale_le :
      ((m + 1 : ℕ) : ℝ) * Real.log (blockScaleR n) ≤
        (η / 2) * H n := by
    have hmul := mul_le_mul_of_nonneg_left hlogR hm1_pos.le
    dsimp [η₁] at hmul
    field_simp [hm1_pos.ne'] at hmul
    nlinarith
  calc
    blockHardyLogDenom n m
        = Real.log 2 + ((m + 1 : ℕ) : ℝ) * Real.log (blockScaleR n) +
            H n / 2 := hlog_eq
    _ ≤ (η / 2) * H n + (η / 2) * H n + H n / 2 := by
          nlinarith
    _ = ((1 : ℝ) / 2 + η) * H n := by ring

/-- The logarithmic denominator is positive. -/
theorem blockHardyLogDenom_pos (n m : ℕ) :
    0 < blockHardyLogDenom n m := by
  unfold blockHardyLogDenom
  have hRpow : 1 ≤ blockScaleR n ^ (m + 1) :=
    one_le_blockScaleR_pow n (m + 1)
  have hH_nonneg : 0 ≤ H n := by
    by_cases hn : n = 0
    · simp [hn, H]
    · exact (H_pos (Nat.pos_of_ne_zero hn)).le
  have hexp_ge : 1 ≤ Real.exp (H n / 2) := by
    have hnonneg : 0 ≤ H n / 2 := by positivity
    simpa using Real.one_le_exp_iff.mpr hnonneg
  have harg_gt :
      1 < 2 * blockScaleR n ^ (m + 1) * Real.exp (H n / 2) := by
    nlinarith
  exact Real.log_pos harg_gt

/-- The exact-cardinality asymmetric alphabet used on the arbitrary side:
add the explicit extra scalar `R_n^m`. -/
def blockExactAlphabet (n b : ℕ) : Finset ℝ :=
  let m := 2 ^ (b - 1) - 1
  insert (blockScaleR n ^ m) (blockSymmAlphabet n m)

/-- The symmetric block alphabet is a subset of the exact-cardinality alphabet. -/
theorem blockSymmAlphabet_subset_blockExactAlphabet (n b : ℕ) :
    blockSymmAlphabet n (2 ^ (b - 1) - 1) ⊆ blockExactAlphabet n b := by
  intro x hx
  simp [blockExactAlphabet, hx]

/-- The extra scalar `R_n^m` is genuinely new. -/
theorem blockScaleR_pow_not_mem_blockSymmAlphabet (n m : ℕ) :
    blockScaleR n ^ m ∉ blockSymmAlphabet n m := by
  intro hmem
  have hpow_pos : 0 < blockScaleR n ^ m :=
    pow_pos (lt_trans zero_lt_one (one_lt_blockScaleR n)) m
  rw [blockSymmAlphabet, mem_signedFinset] at hmem
  rcases hmem with hzero | hpos | hneg
  · linarith
  · rcases Finset.mem_map.1 hpos with ⟨j, hj, hjval⟩
    have hj_eq : j = m := (blockPowEmbedding n).injective hjval
    have hj_lt : j < m := Finset.mem_range.1 hj
    omega
  · have hneg_pos : 0 < -(blockScaleR n ^ m) :=
      blockPositiveFinset_pos hneg
    linarith

/-- Exact cardinality of the arbitrary comparison alphabet. -/
theorem blockExactAlphabet_card {n b : ℕ} (hb : 1 ≤ b) :
    (blockExactAlphabet n b).card = 2 ^ b := by
  let m := 2 ^ (b - 1) - 1
  have hnot : blockScaleR n ^ m ∉ blockSymmAlphabet n m :=
    blockScaleR_pow_not_mem_blockSymmAlphabet n m
  calc
    (blockExactAlphabet n b).card
        = (blockSymmAlphabet n m).card + 1 := by
          simp [blockExactAlphabet, m, hnot, add_comm]
    _ = 2 * m + 2 := by
          simp [m, Nat.add_assoc]
    _ = 2 ^ b := by
          dsimp [m]
          have hpow : 2 * 2 ^ (b - 1) = 2 ^ b := by
            calc
              2 * 2 ^ (b - 1) = 2 ^ (b - 1) * 2 := by rw [Nat.mul_comm]
              _ = 2 ^ ((b - 1) + 1) := by rw [pow_succ]
              _ = 2 ^ b := by rw [Nat.sub_add_cancel hb]
          have hpow_pos : 0 < 2 ^ (b - 1) :=
            pow_pos (by norm_num : 0 < 2) _
          have hsub :
              2 * (2 ^ (b - 1) - 1) + 2 = 2 * 2 ^ (b - 1) := by
            omega
          rw [hsub, hpow]

/-- Standalone statement of the block-Hardy lower bound. -/
def BlockHardyLowerBound : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      2 * Real.sqrt (m : ℝ) - ε ≤
        Real.sqrt (H n) * alpha_asym n (blockSymmAlphabet n m)

/-- Finite analytic core, in the normalized form needed by
`BlockHardyLowerBound`.  This is the only remaining scale-sum estimate: it is
purely about nonnegative unit vectors and the finite maximum `M_B(s)`. -/
def BlockHardyFiniteCoreLowerBound : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      ∀ s : Fin n → ℝ,
        (∀ i, 0 ≤ s i) → ‖tupleVector s‖ = 1 →
          2 * Real.sqrt (m : ℝ) - ε ≤
            Real.sqrt (H n) * nonnegativeBlockMaxCorr n m s

/-- The finite sandwich implies the normalized nonnegative-unit Block-Hardy
core. -/
theorem blockHardy_finite_core_lower :
    BlockHardyFiniteCoreLowerBound := by
  intro m hm ε hε
  let K : ℝ := 2 * Real.sqrt (m : ℝ) - ε
  by_cases hKpos : 0 < K
  · let gap : ℝ := 2 * (m : ℝ) - K ^ 2 / 2
    have hm_pos_real : 0 < (m : ℝ) := by
      exact_mod_cast (show 0 < m by omega)
    have hgap_pos : 0 < gap := by
      have hsqrt_sq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) :=
        Real.sq_sqrt hm_pos_real.le
      dsimp [gap, K]
      nlinarith [hsqrt_sq, hε, hKpos]
    have hK_sq_le : K ^ 2 ≤ 4 * (m : ℝ) := by
      have hsqrt_sq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) :=
        Real.sq_sqrt hm_pos_real.le
      dsimp [K]
      nlinarith [hsqrt_sq, hε, hKpos]
    let η : ℝ := gap / (2 * (K ^ 2 + 1))
    have hη : 0 < η := by
      dsimp [η]
      positivity
    have hbudget :
        K ^ 2 * ((1 : ℝ) / 2 + η) + η ≤ 2 * (m : ℝ) := by
      have hden_pos : 0 < 2 * (K ^ 2 + 1) := by positivity
      dsimp [η, gap]
      field_simp [hden_pos.ne']
      ring_nf
      nlinarith [hK_sq_le]
    have hleft_event := eventually_blockHardySandwichLeft_ge (m := m) hm hη
    have hlog_event := eventually_blockHardyLogDenom_le (m := m) hη
    filter_upwards [hleft_event, hlog_event,
      Filter.eventually_ge_atTop (1 : ℕ)] with n hleft hlog hn1
    intro s hs_nonneg hs_norm
    have hn : 0 < n := Nat.succ_le_iff.mp hn1
    have hHpos : 0 < H n := H_pos hn
    have hH_nonneg : 0 ≤ H n := hHpos.le
    let M : ℝ := nonnegativeBlockMaxCorr n m s
    have hM_nonneg : 0 ≤ M := by
      dsimp [M]
      exact nonnegativeBlockMaxCorr_nonneg hn hm hs_nonneg
    have hsand_raw := blockHardy_finite_sandwich
      (n := n) (m := m) hm (s := s) hs_nonneg hs_norm
    have hsand :
        blockHardySandwichLeft n m ≤
          M ^ 2 * blockHardyLogDenom n m := by
      dsimp [M]
      simpa [blockHardySandwichLeft, blockHardyGeometricContribution,
        blockHardyLogDenom] using hsand_raw
    have hlog_pos : 0 < blockHardyLogDenom n m :=
      blockHardyLogDenom_pos n m
    have hbudget' :
        K ^ 2 * ((1 : ℝ) / 2 + η) ≤ 2 * (m : ℝ) - η := by
      linarith
    have hKsq_log_le_H_left :
        K ^ 2 * blockHardyLogDenom n m ≤
          H n * blockHardySandwichLeft n m := by
      calc
        K ^ 2 * blockHardyLogDenom n m
            ≤ K ^ 2 * (((1 : ℝ) / 2 + η) * H n) := by
              exact mul_le_mul_of_nonneg_left hlog (sq_nonneg K)
        _ = (K ^ 2 * ((1 : ℝ) / 2 + η)) * H n := by ring
        _ ≤ (2 * (m : ℝ) - η) * H n := by
              exact mul_le_mul_of_nonneg_right hbudget' hH_nonneg
        _ ≤ blockHardySandwichLeft n m * H n := by
              exact mul_le_mul_of_nonneg_right hleft hH_nonneg
        _ = H n * blockHardySandwichLeft n m := by ring
    have hKsq_log_le_HM_log :
        K ^ 2 * blockHardyLogDenom n m ≤
          (H n * M ^ 2) * blockHardyLogDenom n m := by
      calc
        K ^ 2 * blockHardyLogDenom n m
            ≤ H n * blockHardySandwichLeft n m := hKsq_log_le_H_left
        _ ≤ H n * (M ^ 2 * blockHardyLogDenom n m) := by
              exact mul_le_mul_of_nonneg_left hsand hH_nonneg
        _ = (H n * M ^ 2) * blockHardyLogDenom n m := by ring
    have hKsq_le_HM :
        K ^ 2 ≤ H n * M ^ 2 :=
      (mul_le_mul_iff_left₀ hlog_pos).1 hKsq_log_le_HM_log
    have hsqrtH_nonneg : 0 ≤ Real.sqrt (H n) := Real.sqrt_nonneg _
    have hrhs_nonneg : 0 ≤ Real.sqrt (H n) * M :=
      mul_nonneg hsqrtH_nonneg hM_nonneg
    have hsq_rhs :
        (Real.sqrt (H n) * M) ^ 2 = H n * M ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hH_nonneg]
    have hsq :
        K ^ 2 ≤ (Real.sqrt (H n) * M) ^ 2 := by
      simpa [hsq_rhs] using hKsq_le_HM
    have habs := (sq_le_sq).1 hsq
    have hK_le : K ≤ Real.sqrt (H n) * M := by
      rwa [abs_of_pos hKpos, abs_of_nonneg hrhs_nonneg] at habs
    simpa [K, M] using hK_le
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn1
    intro s hs_nonneg _hs_norm
    have hn : 0 < n := Nat.succ_le_iff.mp hn1
    have hM_nonneg :
        0 ≤ nonnegativeBlockMaxCorr n m s :=
      nonnegativeBlockMaxCorr_nonneg hn hm hs_nonneg
    have hrhs_nonneg :
        0 ≤ Real.sqrt (H n) * nonnegativeBlockMaxCorr n m s := by
      exact mul_nonneg (Real.sqrt_nonneg _) hM_nonneg
    have hK_nonpos : K ≤ 0 := le_of_not_gt hKpos
    exact le_trans (by simpa [K] using hK_nonpos) hrhs_nonneg

/-- The nonnegative-unit finite analytic core implies the public block-Hardy
lower bound for `alpha_asym`. -/
theorem BlockHardyLowerBound_of_finite_core
    (hcore : BlockHardyFiniteCoreLowerBound) :
    BlockHardyLowerBound := by
  intro m hm ε hε
  filter_upwards [hcore m hm ε hε, Filter.eventually_ge_atTop (1 : ℕ)] with
    n hcore_n hn1
  have hn : 0 < n := Nat.succ_le_iff.mp hn1
  have hHpos : 0 < H n := H_pos hn
  have hsqrtH_pos : 0 < Real.sqrt (H n) := Real.sqrt_pos_of_pos hHpos
  let K : ℝ := 2 * Real.sqrt (m : ℝ) - ε
  let C : ℝ := K / Real.sqrt (H n)
  have hfinite : NonnegativeUnitMaxCorrLowerBound n m C := by
    intro s hs_nonneg hs_norm
    have hnormalized := hcore_n s hs_nonneg hs_norm
    dsimp [K, C] at hnormalized ⊢
    exact (div_le_iff₀ hsqrtH_pos).2 (by
      simpa [mul_comm] using hnormalized)
  have halpha : C ≤ alpha_asym n (blockSymmAlphabet n m) :=
    le_alpha_blockSymmAlphabet_of_finite_core hn hm hfinite
  have hmul :
      Real.sqrt (H n) * C ≤
        Real.sqrt (H n) * alpha_asym n (blockSymmAlphabet n m) :=
    mul_le_mul_of_nonneg_left halpha hsqrtH_pos.le
  have hK_eq : K = Real.sqrt (H n) * C := by
    dsimp [C]
    field_simp [hsqrtH_pos.ne']
  calc
    2 * Real.sqrt (m : ℝ) - ε = K := rfl
    _ = Real.sqrt (H n) * C := hK_eq
    _ ≤ Real.sqrt (H n) * alpha_asym n (blockSymmAlphabet n m) := hmul

/-- Standalone Block-Hardy lower bound for the symmetric block alphabets. -/
theorem blockHardy_lower : BlockHardyLowerBound :=
  BlockHardyLowerBound_of_finite_core blockHardy_finite_core_lower

end AsymmetricProduct
end OptimalAlphabets
