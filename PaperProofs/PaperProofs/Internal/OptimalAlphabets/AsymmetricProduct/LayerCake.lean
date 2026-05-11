import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.FloatingPoint

/-!
# OptimalAlphabets.AsymmetricProduct.LayerCake

The sign-symmetric layer-cake obstruction used for floating-point alphabets.

The index convention is explicit: for descending positive levels
`c 0 > ... > c (m-1) > 0`, the bottom layer contributes the final `1`, and the
sum runs over `j = 0, ..., m-2`.
-/

noncomputable section

open Set Filter Topology Real Metric

namespace OptimalAlphabets
namespace AsymmetricProduct

/-- Positive levels indexed by `Fin m`, converted into a finite scalar set. -/
def positiveLevelsFinset {m : ℕ} (c : Fin m → ℝ) : Finset ℝ :=
  Finset.univ.image c

/-- Signed alphabet associated to positive levels `c`. -/
def signedLevelsOfSeq {m : ℕ} (c : Fin m → ℝ) : Finset ℝ :=
  signedFinset (positiveLevelsFinset c)

/-- The decreasing floating-point presentation has the same positive level set
as the canonical increasing presentation. -/
theorem positiveLevelsFinset_fpDescending_eq (e t : ℕ) :
    positiveLevelsFinset (fpDescendingPositiveLevels e t) =
      fpPositiveFinset e t := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.1 hx with ⟨i, _hi, rfl⟩
    exact Finset.mem_map.2
      ⟨⟨floatPositiveCard e t - 1 - (i : ℕ), by
          have hi := i.2
          omega⟩, by simp, by
        simp [fpPositiveEmbedding, fpDescendingPositiveLevels]⟩
  · intro hx
    rcases Finset.mem_map.1 hx with ⟨k, _hk, hkx⟩
    let i : Fin (floatPositiveCard e t) :=
      ⟨floatPositiveCard e t - 1 - (k : ℕ), by
        have hklt := k.2
        omega⟩
    have hrev :
        floatPositiveCard e t - 1 - (i : ℕ) = (k : ℕ) := by
      dsimp [i]
      have hklt := k.2
      omega
    refine Finset.mem_image.2 ⟨i, by simp, ?_⟩
    simpa [fpPositiveEmbedding, fpDescendingPositiveLevels, i, hrev] using hkx

/-- The decreasing floating-point presentation gives the same signed alphabet
as `fpAlphabet`. -/
theorem signedLevelsOfSeq_fpDescending_eq (e t : ℕ) :
    signedLevelsOfSeq (fpDescendingPositiveLevels e t) =
      fpAlphabet e t := by
  simp [signedLevelsOfSeq, fpAlphabet, positiveLevelsFinset_fpDescending_eq]

/-- The explicit layer-cake summand.  The fallback value is only used outside
the intended range; in the main sum `j ∈ range (m - 1)`, the index proof is
available from the range membership. -/
def layerCakeStepTerm {m : ℕ} (c : Fin m → ℝ) (j : ℕ) : ℝ :=
  if hj : j + 1 < m then
    (c ⟨j, Nat.lt_of_succ_lt hj⟩ - c ⟨j + 1, hj⟩) /
      (c ⟨j, Nat.lt_of_succ_lt hj⟩ + c ⟨j + 1, hj⟩)
  else
    0

/-- The normalized obstruction constant
`2 * sqrt (1 + sum_j (c_j-c_{j+1})/(c_j+c_{j+1}))`. -/
def layerCakeConstant {m : ℕ} (c : Fin m → ℝ) : ℝ :=
  2 * Real.sqrt
    (1 + ∑ j ∈ Finset.range (m - 1), layerCakeStepTerm c j)

def layerDiff {m : ℕ} (c : Fin m → ℝ) (j : Fin m) : ℝ :=
  if hj : (j : ℕ) + 1 < m then
    c j - c ⟨(j : ℕ) + 1, hj⟩
  else
    c j

def layerWidth {m : ℕ} (c : Fin m → ℝ) (j : Fin m) : ℝ :=
  if hj : (j : ℕ) + 1 < m then
    c j + c ⟨(j : ℕ) + 1, hj⟩
  else
    c j

def layerEnergyCoeff {m : ℕ} (c : Fin m → ℝ) (j : Fin m) : ℝ :=
  layerDiff c j * layerWidth c j

def layerRatioCoeff {m : ℕ} (c : Fin m → ℝ) (j : Fin m) : ℝ :=
  layerDiff c j / layerWidth c j

def levelValueNat {m : ℕ} (c : Fin m → ℝ) (j : ℕ) : ℝ :=
  if hj : j < m then c ⟨j, hj⟩ else 0

def layerDiffNat {m : ℕ} (c : Fin m → ℝ) (j : ℕ) : ℝ :=
  if hj : j < m then layerDiff c ⟨j, hj⟩ else 0

def layerEnergyCoeffNat {m : ℕ} (c : Fin m → ℝ) (j : ℕ) : ℝ :=
  if hj : j < m then layerEnergyCoeff c ⟨j, hj⟩ else 0

def positiveThresholdSet {n m : ℕ} (c : Fin m → ℝ)
    (x : Fin n → ℝ) (j : Fin m) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => c j ≤ x i

/-- The total layer mass active below a scalar `a`. -/
def activeLayerSum {m : ℕ} (c : Fin m → ℝ) (a : ℝ) : ℝ :=
  ∑ j : Fin m, if c j ≤ a then layerDiff c j else 0

/-- The total layer energy active below a scalar `a`. -/
def activeEnergySum {m : ℕ} (c : Fin m → ℝ) (a : ℝ) : ℝ :=
  ∑ j : Fin m, if c j ≤ a then layerEnergyCoeff c j else 0

@[simp] theorem mem_positiveThresholdSet {n m : ℕ} {c : Fin m → ℝ}
    {x : Fin n → ℝ} {j : Fin m} {i : Fin n} :
    i ∈ positiveThresholdSet c x j ↔ c j ≤ x i := by
  classical
  simp [positiveThresholdSet]

theorem layerCakeConstant_nonneg {m : ℕ} (c : Fin m → ℝ) :
    0 ≤ layerCakeConstant c := by
  unfold layerCakeConstant
  positivity

theorem layerDiff_pos {m : ℕ} {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    (j : Fin m) :
    0 < layerDiff c j := by
  unfold layerDiff
  by_cases hj : (j : ℕ) + 1 < m
  · rw [dif_pos hj]
    exact sub_pos.mpr (hdesc (by simp [Fin.lt_def]))
  · rw [dif_neg hj]
    exact hpos j

theorem layerWidth_pos {m : ℕ} {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j) (j : Fin m) :
    0 < layerWidth c j := by
  unfold layerWidth
  by_cases hj : (j : ℕ) + 1 < m
  · rw [dif_pos hj]
    exact add_pos (hpos j) (hpos ⟨(j : ℕ) + 1, hj⟩)
  · rw [dif_neg hj]
    exact hpos j

theorem layerEnergyCoeff_nonneg {m : ℕ} {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    (j : Fin m) :
    0 ≤ layerEnergyCoeff c j := by
  unfold layerEnergyCoeff
  exact mul_nonneg (layerDiff_pos hpos hdesc j).le (layerWidth_pos hpos j).le

theorem layerRatioCoeff_nonneg {m : ℕ} {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    (j : Fin m) :
    0 ≤ layerRatioCoeff c j := by
  unfold layerRatioCoeff
  exact div_nonneg (layerDiff_pos hpos hdesc j).le (layerWidth_pos hpos j).le

theorem layerDiffNat_nonneg {m : ℕ} {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    (j : ℕ) :
    0 ≤ layerDiffNat c j := by
  unfold layerDiffNat
  by_cases hj : j < m
  · rw [dif_pos hj]
    exact (layerDiff_pos hpos hdesc ⟨j, hj⟩).le
  · rw [dif_neg hj]

theorem activeLayerSum_nonneg {m : ℕ} {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    (a : ℝ) :
    0 ≤ activeLayerSum c a := by
  classical
  unfold activeLayerSum
  refine Finset.sum_nonneg ?_
  intro j _hj
  by_cases hactive : c j ≤ a
  · rw [if_pos hactive]
    exact (layerDiff_pos hpos hdesc j).le
  · rw [if_neg hactive]

theorem layerDiffNat_eq_levelValueNat_sub_succ {m : ℕ}
    (c : Fin m → ℝ) (j : ℕ) :
    layerDiffNat c j = levelValueNat c j - levelValueNat c (j + 1) := by
  unfold layerDiffNat levelValueNat layerDiff
  by_cases hj : j < m
  · rw [dif_pos hj]
    by_cases hsucc : j + 1 < m
    · simp [hj, hsucc]
    · simp [hj, hsucc]
  · have hsucc_not : ¬ j + 1 < m := by omega
    simp [hj, hsucc_not]

theorem layerRatioCoeff_eq_step {m : ℕ} {c : Fin m → ℝ}
    {j : ℕ} (hj : j + 1 < m) :
    layerRatioCoeff c ⟨j, Nat.lt_of_succ_lt hj⟩ =
      layerCakeStepTerm c j := by
  unfold layerRatioCoeff layerDiff layerWidth layerCakeStepTerm
  simp [hj]

theorem layerEnergyCoeff_eq_sq_sub {m : ℕ} {c : Fin m → ℝ}
    {j : ℕ} (hj : j + 1 < m) :
    layerEnergyCoeff c ⟨j, Nat.lt_of_succ_lt hj⟩ =
      (c ⟨j, Nat.lt_of_succ_lt hj⟩) ^ 2 - (c ⟨j + 1, hj⟩) ^ 2 := by
  unfold layerEnergyCoeff layerDiff layerWidth
  simp [hj]
  ring

theorem layerEnergyCoeff_bottom_eq_sq {m : ℕ} {c : Fin m → ℝ}
    (hm : 1 ≤ m) :
    layerEnergyCoeff c ⟨m - 1, Nat.sub_lt (by omega) (by norm_num)⟩ =
      (c ⟨m - 1, Nat.sub_lt (by omega) (by norm_num)⟩) ^ 2 := by
  have hnot : ¬ (m - 1 : ℕ) + 1 < m := by omega
  unfold layerEnergyCoeff layerDiff layerWidth
  simp [hnot]
  ring

theorem layerEnergyCoeffNat_eq_levelValueNat_sq_sub_succ {m : ℕ}
    (c : Fin m → ℝ) (j : ℕ) :
    layerEnergyCoeffNat c j =
      (levelValueNat c j) ^ 2 - (levelValueNat c (j + 1)) ^ 2 := by
  unfold layerEnergyCoeffNat levelValueNat
  by_cases hj : j < m
  · rw [dif_pos hj]
    by_cases hsucc : j + 1 < m
    · rw [dif_pos hj, dif_pos hsucc]
      exact layerEnergyCoeff_eq_sq_sub (c := c) hsucc
    · rw [dif_pos hj, dif_neg hsucc]
      have hbottom : j = m - 1 := by omega
      subst hbottom
      simpa using layerEnergyCoeff_bottom_eq_sq (m := m) (c := c) (by omega)
  · have hsucc_not : ¬ j + 1 < m := by omega
    simp [hj, hsucc_not]

theorem layerEnergyCoeffNat_nonneg {m : ℕ} {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    (j : ℕ) :
    0 ≤ layerEnergyCoeffNat c j := by
  unfold layerEnergyCoeffNat
  by_cases hj : j < m
  · rw [dif_pos hj]
    exact layerEnergyCoeff_nonneg hpos hdesc ⟨j, hj⟩
  · rw [dif_neg hj]

theorem sum_Ico_sub_succ_eq_sub (F : ℕ → ℝ) {l m : ℕ} (hlm : l ≤ m) :
    (∑ j ∈ Finset.Ico l m, (F j - F (j + 1))) = F l - F m := by
  induction m generalizing l with
  | zero =>
      have hl0 : l = 0 := by omega
      subst l
      simp
  | succ m ih =>
      by_cases hle : l ≤ m
      · rw [Finset.sum_Ico_succ_top hle, ih hle]
        ring
      · have hl : l = m + 1 := by omega
        subst l
        simp

theorem sum_Ico_layerDiffNat_eq_levelValueNat {m : ℕ}
    (c : Fin m → ℝ) {l : ℕ} (hl : l < m) :
    (∑ j ∈ Finset.Ico l m, layerDiffNat c j) = levelValueNat c l := by
  have htel :
      (∑ j ∈ Finset.Ico l m,
          (levelValueNat c j - levelValueNat c (j + 1))) =
        levelValueNat c l - levelValueNat c m := by
    simpa using
      (sum_Ico_sub_succ_eq_sub (fun j => levelValueNat c j) (Nat.le_of_lt hl))
  have hdiff :
      (∑ j ∈ Finset.Ico l m, layerDiffNat c j) =
        ∑ j ∈ Finset.Ico l m,
          (levelValueNat c j - levelValueNat c (j + 1)) := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    exact layerDiffNat_eq_levelValueNat_sub_succ c j
  have hzero : levelValueNat c m = 0 := by
    unfold levelValueNat
    simp
  rw [hdiff, htel, hzero, sub_zero]

theorem sum_Ico_layerEnergyCoeffNat_eq_levelValueNat_sq {m : ℕ}
    (c : Fin m → ℝ) {l : ℕ} (hl : l < m) :
    (∑ j ∈ Finset.Ico l m, layerEnergyCoeffNat c j) =
      (levelValueNat c l) ^ 2 := by
  have htel :
      (∑ j ∈ Finset.Ico l m,
          ((levelValueNat c j) ^ 2 - (levelValueNat c (j + 1)) ^ 2)) =
        (levelValueNat c l) ^ 2 - (levelValueNat c m) ^ 2 := by
    simpa using
      (sum_Ico_sub_succ_eq_sub (fun j => (levelValueNat c j) ^ 2) (Nat.le_of_lt hl))
  have hdiff :
      (∑ j ∈ Finset.Ico l m, layerEnergyCoeffNat c j) =
        ∑ j ∈ Finset.Ico l m,
          ((levelValueNat c j) ^ 2 - (levelValueNat c (j + 1)) ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    exact layerEnergyCoeffNat_eq_levelValueNat_sq_sub_succ c j
  have hzero : levelValueNat c m = 0 := by
    unfold levelValueNat
    simp
  rw [hdiff, htel, hzero]
  ring

theorem levelValueNat_le_of_le {m : ℕ} {c : Fin m → ℝ}
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    {l j : ℕ} (hl : l < m) (hj : j < m) (hlj : l ≤ j) :
    levelValueNat c j ≤ levelValueNat c l := by
  unfold levelValueNat
  rw [dif_pos hj, dif_pos hl]
  by_cases hlj_eq : l = j
  · subst j
    rfl
  · have hlt : l < j := lt_of_le_of_ne hlj hlj_eq
    exact (hdesc (i := ⟨l, hl⟩) (j := ⟨j, hj⟩)
      (by simpa [Fin.lt_def] using hlt)).le

theorem tail_layerDiffNat_le_activeLayerSum {m : ℕ}
    {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    {l : ℕ} (hl : l < m) :
    (∑ j ∈ Finset.Ico l m, layerDiffNat c j) ≤
      activeLayerSum c (levelValueNat c l) := by
  classical
  let f : ℕ → ℝ := fun j =>
    if levelValueNat c j ≤ levelValueNat c l then layerDiffNat c j else 0
  have htail_eq :
      (∑ j ∈ Finset.Ico l m, layerDiffNat c j) =
        ∑ j ∈ Finset.Ico l m, f j := by
    refine Finset.sum_congr rfl ?_
    intro j hjmem
    have hj : j < m := by
      have hjmem' : l ≤ j ∧ j < m := by simpa using hjmem
      exact hjmem'.2
    have hlj : l ≤ j := by
      have hjmem' : l ≤ j ∧ j < m := by simpa using hjmem
      exact hjmem'.1
    have hle := levelValueNat_le_of_le (c := c) hdesc hl hj hlj
    simp [f, hle]
  have hsubset : Finset.Ico l m ⊆ Finset.range m := by
    intro j hjmem
    have hjmem' : l ≤ j ∧ j < m := by simpa using hjmem
    simpa using hjmem'.2
  have htail_le_range :
      (∑ j ∈ Finset.Ico l m, f j) ≤
        ∑ j ∈ Finset.range m, f j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro j hjrange hjnot
    by_cases hactive : levelValueNat c j ≤ levelValueNat c l
    · simp [f, hactive, layerDiffNat_nonneg hpos hdesc j]
    · simp [f, hactive]
  have hrange_eq :
      (∑ j ∈ Finset.range m, f j) =
        activeLayerSum c (levelValueNat c l) := by
    unfold activeLayerSum
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro j hjmem
    have hj : j < m := by simpa using hjmem
    simp [f, levelValueNat, layerDiffNat, hj]
  calc
    (∑ j ∈ Finset.Ico l m, layerDiffNat c j)
        = ∑ j ∈ Finset.Ico l m, f j := htail_eq
    _ ≤ ∑ j ∈ Finset.range m, f j := htail_le_range
    _ = activeLayerSum c (levelValueNat c l) := hrange_eq

theorem exists_level_eq_of_pos_mem_signedLevels {m : ℕ}
    {c : Fin m → ℝ} (hpos : ∀ j, 0 < c j)
    {a : ℝ} (ha : a ∈ signedLevelsOfSeq c) (ha_pos : 0 < a) :
    ∃ j : Fin m, c j = a := by
  rcases (mem_signedFinset.1 ha) with hzero | hposmem | hnegmem
  · linarith
  · rcases Finset.mem_image.1 hposmem with ⟨j, _hj, hj⟩
    exact ⟨j, hj⟩
  · rcases Finset.mem_image.1 hnegmem with ⟨j, _hj, hj⟩
    have hcpos : 0 < c j := hpos j
    linarith

theorem scalar_le_activeLayerSum_of_mem_signedLevels {m : ℕ}
    {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    {a : ℝ} (ha : a ∈ signedLevelsOfSeq c) :
    a ≤ activeLayerSum c a := by
  by_cases ha_pos : 0 < a
  · rcases exists_level_eq_of_pos_mem_signedLevels hpos ha ha_pos with ⟨l, hl⟩
    have hsum :
        (∑ j ∈ Finset.Ico (l : ℕ) m, layerDiffNat c j) =
          levelValueNat c (l : ℕ) :=
      sum_Ico_layerDiffNat_eq_levelValueNat c l.2
    have hlevel : levelValueNat c (l : ℕ) = a := by
      unfold levelValueNat
      simp [l.2, hl]
    calc
      a = levelValueNat c (l : ℕ) := hlevel.symm
      _ = ∑ j ∈ Finset.Ico (l : ℕ) m, layerDiffNat c j := hsum.symm
      _ ≤ activeLayerSum c (levelValueNat c (l : ℕ)) :=
          tail_layerDiffNat_le_activeLayerSum hpos hdesc l.2
      _ = activeLayerSum c a := by rw [hlevel]
  · have ha_nonpos : a ≤ 0 := le_of_not_gt ha_pos
    have hsum_nonneg := activeLayerSum_nonneg hpos hdesc a
    linarith

theorem activeEnergySum_eq_range {m : ℕ} (c : Fin m → ℝ) (a : ℝ) :
    activeEnergySum c a =
      ∑ j ∈ Finset.range m,
        if levelValueNat c j ≤ a then layerEnergyCoeffNat c j else 0 := by
  unfold activeEnergySum
  rw [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro j hjmem
  have hj : j < m := by simpa using hjmem
  simp [levelValueNat, layerEnergyCoeffNat, hj]

theorem activeEnergySum_level_le_tail_layerEnergyCoeffNat {m : ℕ}
    {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    {l : ℕ} (hl : l < m) :
    activeEnergySum c (levelValueNat c l) ≤
      ∑ j ∈ Finset.Ico l m, layerEnergyCoeffNat c j := by
  classical
  rw [activeEnergySum_eq_range]
  have hpoint :
      ∀ j ∈ Finset.range m,
        (if levelValueNat c j ≤ levelValueNat c l then
            layerEnergyCoeffNat c j else 0) ≤
          if l ≤ j then layerEnergyCoeffNat c j else 0 := by
    intro j hjmem
    have hj : j < m := by simpa using hjmem
    by_cases hlj : l ≤ j
    · by_cases hactive : levelValueNat c j ≤ levelValueNat c l
      · simp [hactive, hlj]
      · have hE := layerEnergyCoeffNat_nonneg hpos hdesc j
        simp [hactive, hlj, hE]
    · have hjl : j < l := Nat.lt_of_not_ge hlj
      have hgt : levelValueNat c l < levelValueNat c j := by
        unfold levelValueNat
        rw [dif_pos hl, dif_pos hj]
        exact hdesc (i := ⟨j, hj⟩) (j := ⟨l, hl⟩)
          (by simpa [Fin.lt_def] using hjl)
      have hnot : ¬ levelValueNat c j ≤ levelValueNat c l := not_le.mpr hgt
      simp [hnot, hlj]
  calc
    (∑ j ∈ Finset.range m,
        if levelValueNat c j ≤ levelValueNat c l then
          layerEnergyCoeffNat c j else 0)
        ≤ ∑ j ∈ Finset.range m,
            if l ≤ j then layerEnergyCoeffNat c j else 0 := by
          exact Finset.sum_le_sum hpoint
    _ = ∑ j ∈ Finset.Ico l m, layerEnergyCoeffNat c j := by
          rw [← Finset.sum_filter]
          congr 1
          ext j
          simp [Finset.mem_Ico, and_comm]

theorem activeEnergySum_le_sq_of_mem_signedLevels {m : ℕ}
    {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    {a : ℝ} (ha : a ∈ signedLevelsOfSeq c) :
    activeEnergySum c a ≤ a ^ 2 := by
  by_cases ha_pos : 0 < a
  · rcases exists_level_eq_of_pos_mem_signedLevels hpos ha ha_pos with ⟨l, hl⟩
    have hlevel : levelValueNat c (l : ℕ) = a := by
      unfold levelValueNat
      simp [l.2, hl]
    have htail :=
      activeEnergySum_level_le_tail_layerEnergyCoeffNat
        (c := c) hpos hdesc l.2
    have hsum :
        (∑ j ∈ Finset.Ico (l : ℕ) m, layerEnergyCoeffNat c j) =
          (levelValueNat c (l : ℕ)) ^ 2 :=
      sum_Ico_layerEnergyCoeffNat_eq_levelValueNat_sq c l.2
    calc
      activeEnergySum c a
          = activeEnergySum c (levelValueNat c (l : ℕ)) := by rw [hlevel]
      _ ≤ ∑ j ∈ Finset.Ico (l : ℕ) m, layerEnergyCoeffNat c j := htail
      _ = (levelValueNat c (l : ℕ)) ^ 2 := hsum
      _ = a ^ 2 := by rw [hlevel]
  · have ha_nonpos : a ≤ 0 := le_of_not_gt ha_pos
    have hzero : activeEnergySum c a = 0 := by
      unfold activeEnergySum
      refine Finset.sum_eq_zero ?_
      intro j _hj
      have hnot : ¬ c j ≤ a := by
        linarith [hpos j]
      simp [hnot]
    rw [hzero]
    positivity

theorem harmonic_activeLayerSum_eq_layer_contributions {n m : ℕ}
    (c : Fin m → ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin n, harmonicWeightNat (i : ℕ) * activeLayerSum c (x i)) =
      ∑ j : Fin m, layerDiff c j *
        (∑ i ∈ positiveThresholdSet c x j, harmonicWeightNat (i : ℕ)) := by
  classical
  unfold activeLayerSum
  calc
    (∑ i : Fin n,
        harmonicWeightNat (i : ℕ) *
          (∑ j : Fin m, if c j ≤ x i then layerDiff c j else 0))
        = ∑ i : Fin n, ∑ j : Fin m,
            harmonicWeightNat (i : ℕ) *
              (if c j ≤ x i then layerDiff c j else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Finset.mul_sum]
    _ = ∑ j : Fin m, ∑ i : Fin n,
            harmonicWeightNat (i : ℕ) *
              (if c j ≤ x i then layerDiff c j else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin m, layerDiff c j *
          (∑ i ∈ positiveThresholdSet c x j, harmonicWeightNat (i : ℕ)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          calc
            (∑ i : Fin n,
                harmonicWeightNat (i : ℕ) *
                  (if c j ≤ x i then layerDiff c j else 0))
                = ∑ i : Fin n,
                    if c j ≤ x i then
                      harmonicWeightNat (i : ℕ) * layerDiff c j else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro i _hi
                  by_cases hactive : c j ≤ x i
                  · simp [hactive]
                  · simp [hactive]
            _ = ∑ i ∈ positiveThresholdSet c x j,
                    harmonicWeightNat (i : ℕ) * layerDiff c j := by
                  rw [← Finset.sum_filter]
                  simp [positiveThresholdSet]
            _ = layerDiff c j *
                  (∑ i ∈ positiveThresholdSet c x j,
                    harmonicWeightNat (i : ℕ)) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro i _hi
                  ring

theorem inner_harmonicWeights_tupleVector_le_layer_contributions {n m : ℕ}
    {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    {x : Fin n → ℝ}
    (hxA : ∀ i, x i ∈ signedLevelsOfSeq c) :
    inner ℝ (harmonicWeights n) (tupleVector x) ≤
      ∑ j : Fin m, layerDiff c j *
        (∑ i ∈ positiveThresholdSet c x j, harmonicWeightNat (i : ℕ)) := by
  rw [inner_harmonicWeights_tupleVector]
  calc
    (∑ i : Fin n, harmonicWeightNat (i : ℕ) * x i)
        ≤ ∑ i : Fin n, harmonicWeightNat (i : ℕ) *
            activeLayerSum c (x i) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          exact mul_le_mul_of_nonneg_left
            (scalar_le_activeLayerSum_of_mem_signedLevels hpos hdesc (hxA i))
            (harmonicWeightNat_nonneg (i : ℕ))
    _ = ∑ j : Fin m, layerDiff c j *
          (∑ i ∈ positiveThresholdSet c x j,
            harmonicWeightNat (i : ℕ)) :=
          harmonic_activeLayerSum_eq_layer_contributions c x

theorem layerRatioCoeff_bottom_eq_one {m : ℕ} {c : Fin m → ℝ}
    (hm : 1 ≤ m) (hpos : ∀ j, 0 < c j) :
    layerRatioCoeff c ⟨m - 1, Nat.sub_lt (by omega) (by norm_num)⟩ = 1 := by
  have hnot : ¬ (m - 1 : ℕ) + 1 < m := by omega
  unfold layerRatioCoeff layerDiff layerWidth
  simp [hnot, (hpos ⟨m - 1, Nat.sub_lt (by omega) (by norm_num)⟩).ne']

theorem sum_layerRatioCoeff_eq_layerCakeArg {m : ℕ} (hm : 1 ≤ m)
    {c : Fin m → ℝ} (hpos : ∀ j, 0 < c j) :
    (∑ j : Fin m, layerRatioCoeff c j) =
      1 + ∑ j ∈ Finset.range (m - 1), layerCakeStepTerm c j := by
  cases m with
  | zero =>
      omega
  | succ k =>
      rw [Fin.sum_univ_castSucc]
      have hlast :
          layerRatioCoeff c (Fin.last k) = 1 := by
        simpa [Fin.last] using
          layerRatioCoeff_bottom_eq_one (m := k + 1) (c := c) (by omega) hpos
      rw [hlast]
      simp only [Nat.add_sub_cancel_right]
      rw [add_comm 1 (∑ x ∈ Finset.range k, layerCakeStepTerm c x)]
      congr 1
      rw [Finset.sum_fin_eq_sum_range]
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxlt : x < k := by simpa using hx
      have hxsucc : x + 1 < k + 1 := Nat.succ_lt_succ hxlt
      rw [dif_pos hxlt]
      simpa [Fin.castSucc] using layerRatioCoeff_eq_step (c := c) hxsucc

/-- A bridge from tuplewise harmonic-witness bounds to the direct correlation
objective. -/
theorem sqrtH_mul_alpha_le_of_harmonic_tuple_bound {n : ℕ} (hn : 0 < n)
    (A : Finset ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound :
      ∀ x, x ∈ nonzeroAsymProductTuples n A →
        Real.sqrt (H n) * tupleCorr (harmonicWitness n hn) x ≤ C) :
    Real.sqrt (H n) * alpha_asym n A ≤ C := by
  have hHpos : 0 < H n := H_pos hn
  have hsqrtH_pos : 0 < Real.sqrt (H n) := Real.sqrt_pos_of_pos hHpos
  have hsentinel : -1 ≤ C / Real.sqrt (H n) := by
    have hdiv_nonneg : 0 ≤ C / Real.sqrt (H n) :=
      div_nonneg hC hsqrtH_pos.le
    linarith
  have hmax :
      maxCorr_asym n A (harmonicWitness n hn) ≤ C / Real.sqrt (H n) :=
    maxCorr_asym_le_of_forall hsentinel (by
      intro x hx
      exact (le_div_iff₀ hsqrtH_pos).2 (by
        simpa [mul_comm] using hbound x hx))
  have halpha :
      alpha_asym n A ≤ maxCorr_asym n A (harmonicWitness n hn) :=
    alpha_asym_le_maxCorr A (harmonicWitness n hn)
  calc
    Real.sqrt (H n) * alpha_asym n A
        ≤ Real.sqrt (H n) * maxCorr_asym n A (harmonicWitness n hn) := by
          exact mul_le_mul_of_nonneg_left halpha hsqrtH_pos.le
    _ ≤ Real.sqrt (H n) * (C / Real.sqrt (H n)) := by
          exact mul_le_mul_of_nonneg_left hmax hsqrtH_pos.le
    _ = C := by
          field_simp [hsqrtH_pos.ne']

theorem sqrtH_mul_tupleCorr_harmonicWitness_le_of_inner_le
    {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ} (hxne : tupleVector x ≠ 0)
    {C : ℝ}
    (hinner :
      inner ℝ (harmonicWeights n) (tupleVector x) ≤ C * ‖tupleVector x‖) :
    Real.sqrt (H n) * tupleCorr (harmonicWitness n hn) x ≤ C := by
  have hHpos : 0 < H n := H_pos hn
  have hsqrtH_pos : 0 < Real.sqrt (H n) := Real.sqrt_pos_of_pos hHpos
  have hxnorm_pos : 0 < ‖tupleVector x‖ := norm_pos_iff.mpr hxne
  have hnorm_hw : ‖harmonicWeights n‖ = Real.sqrt (H n) :=
    harmonicWeights_norm n
  have hinner_norm :
      inner ℝ (harmonicWitness n hn).1 (tupleVector x) =
        (‖harmonicWeights n‖)⁻¹ *
          inner ℝ (harmonicWeights n) (tupleVector x) := by
    simp [harmonicWitness, NormedSpace.normalize, real_inner_smul_left]
  have hcorr :
      Real.sqrt (H n) * tupleCorr (harmonicWitness n hn) x =
        inner ℝ (harmonicWeights n) (tupleVector x) / ‖tupleVector x‖ := by
    unfold tupleCorr
    rw [hinner_norm, hnorm_hw]
    field_simp [hsqrtH_pos.ne', hxnorm_pos.ne']
  rw [hcorr]
  exact (div_le_iff₀ hxnorm_pos).2 hinner

theorem harmonic_threshold_sum_le {n m : ℕ} (c : Fin m → ℝ)
    (x : Fin n → ℝ) (j : Fin m) :
    ∑ i ∈ positiveThresholdSet c x j, harmonicWeightNat (i : ℕ) ≤
      2 * Real.sqrt ((positiveThresholdSet c x j).card : ℝ) := by
  exact sum_harmonicWeight_subset_le (positiveThresholdSet c x j)

theorem layer_threshold_contribution_le {n m : ℕ} {c : Fin m → ℝ}
    (x : Fin n → ℝ) (j : Fin m) (hdiff : 0 ≤ layerDiff c j) :
    layerDiff c j *
        (∑ i ∈ positiveThresholdSet c x j,
          harmonicWeightNat (i : ℕ)) ≤
      2 * layerDiff c j *
        Real.sqrt ((positiveThresholdSet c x j).card : ℝ) := by
  have hbase := harmonic_threshold_sum_le c x j
  nlinarith

theorem layerDiff_mul_sqrt_card_eq_sqrt_energy_mul_sqrt_ratio {n m : ℕ}
    {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    (x : Fin n → ℝ) (j : Fin m) :
    layerDiff c j *
        Real.sqrt ((positiveThresholdSet c x j).card : ℝ) =
      Real.sqrt
          (layerEnergyCoeff c j *
            ((positiveThresholdSet c x j).card : ℝ)) *
        Real.sqrt (layerRatioCoeff c j) := by
  let d : ℝ := layerDiff c j
  let w : ℝ := layerWidth c j
  let k : ℝ := ((positiveThresholdSet c x j).card : ℝ)
  have hd_pos : 0 < d := by
    dsimp [d]
    exact layerDiff_pos hpos hdesc j
  have hd_nonneg : 0 ≤ d := hd_pos.le
  have hw_pos : 0 < w := by
    dsimp [w]
    exact layerWidth_pos hpos j
  have hk_nonneg : 0 ≤ k := by
    dsimp [k]
    positivity
  have henergy_nonneg :
      0 ≤ layerEnergyCoeff c j * k := by
    exact mul_nonneg (layerEnergyCoeff_nonneg hpos hdesc j) hk_nonneg
  symm
  calc
    Real.sqrt
          (layerEnergyCoeff c j *
            ((positiveThresholdSet c x j).card : ℝ)) *
        Real.sqrt (layerRatioCoeff c j)
        = Real.sqrt
            ((layerEnergyCoeff c j * k) * layerRatioCoeff c j) := by
          rw [← Real.sqrt_mul henergy_nonneg]
    _ = Real.sqrt (d ^ 2 * k) := by
          congr 1
          dsimp [d, w, k]
          unfold layerEnergyCoeff layerRatioCoeff
          field_simp [(layerWidth_pos hpos j).ne']
    _ = Real.sqrt (d ^ 2) * Real.sqrt k := by
          rw [Real.sqrt_mul (sq_nonneg d)]
    _ = d * Real.sqrt k := by
          rw [Real.sqrt_sq hd_nonneg]
    _ = layerDiff c j *
          Real.sqrt ((positiveThresholdSet c x j).card : ℝ) := by
          rfl

theorem layer_energy_card_sum_le_norm_sq {n m : ℕ}
    {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    {x : Fin n → ℝ}
    (hxA : ∀ i, x i ∈ signedLevelsOfSeq c) :
    (∑ j : Fin m,
        layerEnergyCoeff c j *
          ((positiveThresholdSet c x j).card : ℝ)) ≤
      ‖tupleVector x‖ ^ 2 := by
  classical
  have henergy_reindex :
      (∑ j : Fin m,
          layerEnergyCoeff c j *
            ((positiveThresholdSet c x j).card : ℝ)) =
        ∑ i : Fin n, activeEnergySum c (x i) := by
    calc
      (∑ j : Fin m,
          layerEnergyCoeff c j *
            ((positiveThresholdSet c x j).card : ℝ))
          = ∑ j : Fin m, ∑ i ∈ positiveThresholdSet c x j,
              layerEnergyCoeff c j := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            simp [mul_comm]
      _ = ∑ j : Fin m, ∑ i : Fin n,
              if c j ≤ x i then layerEnergyCoeff c j else 0 := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [← Finset.sum_filter]
            simp [positiveThresholdSet]
      _ = ∑ i : Fin n, ∑ j : Fin m,
              if c j ≤ x i then layerEnergyCoeff c j else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ i : Fin n, activeEnergySum c (x i) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simp [activeEnergySum]
  calc
    (∑ j : Fin m,
        layerEnergyCoeff c j *
          ((positiveThresholdSet c x j).card : ℝ))
        = ∑ i : Fin n, activeEnergySum c (x i) := henergy_reindex
    _ ≤ ∑ i : Fin n, (x i) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          exact activeEnergySum_le_sq_of_mem_signedLevels hpos hdesc (hxA i)
    _ = ‖tupleVector x‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]
          simp [tupleVector, Real.norm_eq_abs, sq_abs]

theorem layer_contributions_le_layerCakeConstant_mul_norm {n m : ℕ}
    (hm : 1 ≤ m) {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    {x : Fin n → ℝ}
    (hxA : ∀ i, x i ∈ signedLevelsOfSeq c) :
    (∑ j : Fin m, layerDiff c j *
        (∑ i ∈ positiveThresholdSet c x j,
          harmonicWeightNat (i : ℕ))) ≤
      layerCakeConstant c * ‖tupleVector x‖ := by
  let E : Fin m → ℝ := fun j =>
    layerEnergyCoeff c j * ((positiveThresholdSet c x j).card : ℝ)
  let R : Fin m → ℝ := fun j => layerRatioCoeff c j
  have hthreshold :
      (∑ j : Fin m, layerDiff c j *
          (∑ i ∈ positiveThresholdSet c x j,
            harmonicWeightNat (i : ℕ))) ≤
        ∑ j : Fin m,
          2 * layerDiff c j *
            Real.sqrt ((positiveThresholdSet c x j).card : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    exact layer_threshold_contribution_le x j
      (layerDiff_pos hpos hdesc j).le
  have htwo_sum :
      (∑ j : Fin m,
          2 * layerDiff c j *
            Real.sqrt ((positiveThresholdSet c x j).card : ℝ)) =
        2 * ∑ j : Fin m,
          layerDiff c j *
            Real.sqrt ((positiveThresholdSet c x j).card : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    ring
  have hsqrt_terms :
      (∑ j : Fin m,
          layerDiff c j *
            Real.sqrt ((positiveThresholdSet c x j).card : ℝ)) =
        ∑ j : Fin m, Real.sqrt (E j) * Real.sqrt (R j) := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    dsimp [E, R]
    exact layerDiff_mul_sqrt_card_eq_sqrt_energy_mul_sqrt_ratio
      hpos hdesc x j
  have hE_sq :
      (∑ j : Fin m, (Real.sqrt (E j)) ^ 2) =
        ∑ j : Fin m, E j := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    rw [Real.sq_sqrt]
    dsimp [E]
    exact mul_nonneg (layerEnergyCoeff_nonneg hpos hdesc j) (by positivity)
  have hR_sq :
      (∑ j : Fin m, (Real.sqrt (R j)) ^ 2) =
        ∑ j : Fin m, R j := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    rw [Real.sq_sqrt]
    dsimp [R]
    exact layerRatioCoeff_nonneg hpos hdesc j
  have hcauchy :
      (∑ j : Fin m, Real.sqrt (E j) * Real.sqrt (R j)) ≤
        Real.sqrt (∑ j : Fin m, E j) *
          Real.sqrt (∑ j : Fin m, R j) := by
    calc
      (∑ j : Fin m, Real.sqrt (E j) * Real.sqrt (R j))
          ≤ Real.sqrt (∑ j : Fin m, (Real.sqrt (E j)) ^ 2) *
              Real.sqrt (∑ j : Fin m, (Real.sqrt (R j)) ^ 2) := by
            simpa using
              Real.sum_mul_le_sqrt_mul_sqrt
                (Finset.univ : Finset (Fin m))
                (fun j => Real.sqrt (E j)) (fun j => Real.sqrt (R j))
      _ = Real.sqrt (∑ j : Fin m, E j) *
            Real.sqrt (∑ j : Fin m, R j) := by
            rw [hE_sq, hR_sq]
  have hsqrt_energy_le_norm :
      Real.sqrt (∑ j : Fin m, E j) ≤ ‖tupleVector x‖ := by
    calc
      Real.sqrt (∑ j : Fin m, E j)
          ≤ Real.sqrt (‖tupleVector x‖ ^ 2) := by
            exact Real.sqrt_le_sqrt
              (by
                dsimp [E]
                exact layer_energy_card_sum_le_norm_sq hpos hdesc hxA)
      _ = ‖tupleVector x‖ := Real.sqrt_sq (norm_nonneg _)
  have hsqrt_sum_le :
      (∑ j : Fin m,
          layerDiff c j *
            Real.sqrt ((positiveThresholdSet c x j).card : ℝ)) ≤
        ‖tupleVector x‖ * Real.sqrt (∑ j : Fin m, R j) := by
    calc
      (∑ j : Fin m,
          layerDiff c j *
            Real.sqrt ((positiveThresholdSet c x j).card : ℝ))
          = ∑ j : Fin m, Real.sqrt (E j) * Real.sqrt (R j) := hsqrt_terms
      _ ≤ Real.sqrt (∑ j : Fin m, E j) *
            Real.sqrt (∑ j : Fin m, R j) := hcauchy
      _ ≤ ‖tupleVector x‖ * Real.sqrt (∑ j : Fin m, R j) := by
            exact mul_le_mul_of_nonneg_right hsqrt_energy_le_norm
              (Real.sqrt_nonneg _)
  have hratio_arg :
      (∑ j : Fin m, R j) =
        1 + ∑ j ∈ Finset.range (m - 1), layerCakeStepTerm c j := by
    dsimp [R]
    exact sum_layerRatioCoeff_eq_layerCakeArg hm hpos
  calc
    (∑ j : Fin m, layerDiff c j *
        (∑ i ∈ positiveThresholdSet c x j,
          harmonicWeightNat (i : ℕ)))
        ≤ ∑ j : Fin m,
            2 * layerDiff c j *
              Real.sqrt ((positiveThresholdSet c x j).card : ℝ) := hthreshold
    _ = 2 * ∑ j : Fin m,
          layerDiff c j *
            Real.sqrt ((positiveThresholdSet c x j).card : ℝ) := htwo_sum
    _ ≤ 2 * (‖tupleVector x‖ * Real.sqrt (∑ j : Fin m, R j)) := by
          exact mul_le_mul_of_nonneg_left hsqrt_sum_le (by norm_num)
    _ = layerCakeConstant c * ‖tupleVector x‖ := by
          unfold layerCakeConstant
          rw [hratio_arg]
          ring

theorem inner_harmonicWeights_tupleVector_le_layerCakeConstant_mul_norm
    {n m : ℕ} (hm : 1 ≤ m) {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i)
    {x : Fin n → ℝ}
    (hxA : ∀ i, x i ∈ signedLevelsOfSeq c) :
    inner ℝ (harmonicWeights n) (tupleVector x) ≤
      layerCakeConstant c * ‖tupleVector x‖ := by
  calc
    inner ℝ (harmonicWeights n) (tupleVector x)
        ≤ ∑ j : Fin m, layerDiff c j *
            (∑ i ∈ positiveThresholdSet c x j,
              harmonicWeightNat (i : ℕ)) :=
          inner_harmonicWeights_tupleVector_le_layer_contributions
            hpos hdesc hxA
    _ ≤ layerCakeConstant c * ‖tupleVector x‖ :=
          layer_contributions_le_layerCakeConstant_mul_norm
            hm hpos hdesc hxA

/-- If adjacent descending levels have ratio at most two, the corresponding
layer-cake summand is at most `1/3`. -/
theorem layerCakeStepTerm_le_one_third {m : ℕ} {c : Fin m → ℝ} {j : ℕ}
    (hj : j + 1 < m) (hpos : ∀ i, 0 < c i)
    (hratio :
      c ⟨j, Nat.lt_of_succ_lt hj⟩ ≤ 2 * c ⟨j + 1, hj⟩) :
    layerCakeStepTerm c j ≤ (1 : ℝ) / 3 := by
  unfold layerCakeStepTerm
  rw [dif_pos hj]
  let a : ℝ := c ⟨j, Nat.lt_of_succ_lt hj⟩
  let d : ℝ := c ⟨j + 1, hj⟩
  have ha : 0 < a := by
    dsimp [a]
    exact hpos _
  have hd : 0 < d := by
    dsimp [d]
    exact hpos _
  have hratio' : a ≤ 2 * d := by
    simpa [a, d] using hratio
  have hden_pos : 0 < a + d := by linarith
  rw [div_le_iff₀ hden_pos]
  nlinarith

/-- A finite layer-cake constant bound from adjacent ratio control. -/
theorem layerCakeConstant_le_of_adjacent_ratio_two {m : ℕ}
    (hm : 1 ≤ m) {c : Fin m → ℝ} (hpos : ∀ i, 0 < c i)
    (hratio : ∀ {j : ℕ} (hj : j + 1 < m),
      c ⟨j, Nat.lt_of_succ_lt hj⟩ ≤ 2 * c ⟨j + 1, hj⟩) :
    layerCakeConstant c ≤
      2 * Real.sqrt ((((m + 2 : ℕ) : ℝ) / 3)) := by
  have hsum_le :
      (∑ j ∈ Finset.range (m - 1), layerCakeStepTerm c j) ≤
        ∑ _j ∈ Finset.range (m - 1), ((1 : ℝ) / 3) := by
    refine Finset.sum_le_sum ?_
    intro j hjmem
    have hj : j + 1 < m := by
      have hjlt : j < m - 1 := by
        simpa using hjmem
      omega
    exact layerCakeStepTerm_le_one_third hj hpos (hratio hj)
  have hsum_const :
      (∑ _j ∈ Finset.range (m - 1), ((1 : ℝ) / 3)) =
        ((m - 1 : ℕ) : ℝ) / 3 := by
    simp [div_eq_mul_inv]
  have hsum_bound :
      (∑ j ∈ Finset.range (m - 1), layerCakeStepTerm c j) ≤
        ((m - 1 : ℕ) : ℝ) / 3 := by
    calc
      (∑ j ∈ Finset.range (m - 1), layerCakeStepTerm c j)
          ≤ ∑ _j ∈ Finset.range (m - 1), ((1 : ℝ) / 3) := hsum_le
      _ = ((m - 1 : ℕ) : ℝ) / 3 := hsum_const
  have harg :
      1 + (∑ j ∈ Finset.range (m - 1), layerCakeStepTerm c j) ≤
        (((m + 2 : ℕ) : ℝ) / 3) := by
    calc
      1 + (∑ j ∈ Finset.range (m - 1), layerCakeStepTerm c j)
          ≤ 1 + ((m - 1 : ℕ) : ℝ) / 3 := by
            exact add_le_add_right hsum_bound 1
      _ = (((m + 2 : ℕ) : ℝ) / 3) := by
            rw [Nat.cast_sub hm, Nat.cast_add]
            norm_num
            ring
  unfold layerCakeConstant
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt harg) (by norm_num)

/-- Layer-cake obstruction for sign-symmetric alphabets. -/
theorem signSymmetricLayerCake_obstruction {n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    {c : Fin m → ℝ}
    (hpos : ∀ j, 0 < c j)
    (hdesc : ∀ {i j : Fin m}, i < j → c j < c i) :
    Real.sqrt (H n) * alpha_asym n (signedLevelsOfSeq c) ≤
      layerCakeConstant c := by
  refine sqrtH_mul_alpha_le_of_harmonic_tuple_bound
    hn (signedLevelsOfSeq c) (layerCakeConstant_nonneg c) ?_
  intro x hx
  have hxA : ∀ i, x i ∈ signedLevelsOfSeq c :=
    (mem_nonzeroAsymProductTuples.1 hx).1
  have hxne : tupleVector x ≠ 0 :=
    (mem_nonzeroAsymProductTuples.1 hx).2
  exact sqrtH_mul_tupleCorr_harmonicWitness_le_of_inner_le
    hn hxne
    (inner_harmonicWeights_tupleVector_le_layerCakeConstant_mul_norm
      hm hpos hdesc hxA)

end AsymmetricProduct
end OptimalAlphabets
