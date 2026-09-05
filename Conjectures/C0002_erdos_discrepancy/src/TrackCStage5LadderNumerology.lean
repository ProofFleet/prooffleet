import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandScheduleSharpNumerology

/-!
# Track R L3: the exceptional-cell share margin

The Phase-4 exceptional fit proposes the uniform per-cell share

`1 / (2^(J+4) * cellCount^2)`.

Its stated prime-term reduction would require

`DeltaU^2 <= share * c3 * eps^2 * logP / (24*1024)`.

For the exceptional power interval the e-adic cover has at least a constant
multiple of `logP` cells.  The following algebraic lemmas record the resulting
necessary upper bound on `logP`.  In particular increasing the exceptional
prime scale makes this margin worse, not better.
-/

namespace MoltResearch

namespace Tao2015

/-- The lower/upper e-adic index convention used for a prime interval whose
logarithmic endpoints, after multiplication by the cell density, are `a,b`. -/
noncomputable def phase4EadicIndexRange (a b : ℝ) : Finset ℕ :=
  Finset.Ico (⌈a⌉₊ - 1) (⌊b⌋₊ + 1)

/-- The chosen contiguous e-adic index range has at least its real
logarithmic width.  Applied with `a = 2*Nu*log P` and
`b = 2*Nu*log Q`, this is the cell-count lower bound used below. -/
theorem phase4EadicIndexRange_width_le_card
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    b - a ≤ ((phase4EadicIndexRange a b).card : ℝ) := by
  have ha0 : 0 ≤ a := ha.le
  have hb0 : 0 ≤ b := ha0.trans hab
  have hceil1 : 1 ≤ ⌈a⌉₊ := Nat.one_le_ceil_iff.mpr ha
  have hceil : ((⌈a⌉₊ : ℕ) : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
  have hfloor : b < ((⌊b⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one b
  have hindex : ⌈a⌉₊ - 1 ≤ ⌊b⌋₊ + 1 := by
    have hcast : ((⌈a⌉₊ : ℕ) : ℝ) < ((⌊b⌋₊ + 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hnat : ⌈a⌉₊ < ⌊b⌋₊ + 2 := by exact_mod_cast hcast
    omega
  rw [phase4EadicIndexRange, Nat.card_Ico, Nat.cast_sub hindex,
    Nat.cast_add, Nat.cast_one, Nat.cast_sub hceil1, Nat.cast_one]
  linarith

/-- Any exceptional interval with `log Q >= 2*log P` has at least `log P`
cells under the Phase-4 index convention, already at the coarsest admissible
cell density `Nu = 1`. -/
theorem phase4EadicIndexRange_log_lower
    (Nu : ℕ) (logP logQ : ℝ) (hNu : 0 < Nu) (hlogP : 0 < logP)
    (hlogQ : 2 * logP ≤ logQ) :
    logP ≤
      ((phase4EadicIndexRange (2 * (Nu : ℝ) * logP)
        (2 * (Nu : ℝ) * logQ)).card : ℝ) := by
  have hNuR : (1 : ℝ) ≤ Nu := by exact_mod_cast hNu
  have hleft : 0 < 2 * (Nu : ℝ) * logP := by positivity
  have horder : 2 * (Nu : ℝ) * logP ≤ 2 * (Nu : ℝ) * logQ := by
    gcongr
    linarith
  have hwidth := phase4EadicIndexRange_width_le_card
    (2 * (Nu : ℝ) * logP) (2 * (Nu : ℝ) * logQ) hleft horder
  calc
    logP ≤
        2 * (Nu : ℝ) * logQ - 2 * (Nu : ℝ) * logP := by
      nlinarith
    _ ≤ _ := hwidth

/-- The uniform exceptional-cell share prescribed by the Phase-4 schedule. -/
noncomputable def ladderExceptionalCellShare
    (J : ℕ) (cellCount : ℝ) : ℝ :=
  1 / ((2 : ℝ) ^ (J + 4) * cellCount ^ 2)

/-- **L3-5 obstruction.**  If the number of exceptional cells is at least
`logP`, the proposed sufficient prime fit forces

`384 * 2^(J+4) * epsilon'^2 * logP <= c3 * eps^2`.

The factor `384` is exact: `24*1024 / 8^2 = 384`. -/
theorem ladderExceptionalCellShare_prime_fit_forces_log_upper
    (J : ℕ) (cellCount logP c3 eps epsilon' : ℝ)
    (hlogP : 0 < logP) (hcellCount : logP ≤ cellCount)
    (hepsilon' : 0 < epsilon')
    (hfit : (epsilon' / 8) ^ 2 ≤
      ladderExceptionalCellShare J cellCount * c3 * eps ^ 2 * logP /
        (24 * 1024)) :
    384 * (2 : ℝ) ^ (J + 4) * epsilon' ^ 2 * logP ≤ c3 * eps ^ 2 := by
  have hcellCount0 : 0 < cellCount := hlogP.trans_le hcellCount
  have hpow0 : 0 < (2 : ℝ) ^ (J + 4) := by positivity
  have hcountSq : logP ^ 2 ≤ cellCount ^ 2 :=
    pow_le_pow_left₀ hlogP.le hcellCount 2
  have hden : 0 < 24576 * (2 : ℝ) ^ (J + 4) * cellCount ^ 2 := by
    positivity
  have hshape :
      ladderExceptionalCellShare J cellCount * c3 * eps ^ 2 * logP /
          (24 * 1024) =
        (c3 * eps ^ 2 * logP) /
          (24576 * (2 : ℝ) ^ (J + 4) * cellCount ^ 2) := by
    unfold ladderExceptionalCellShare
    ring
  rw [hshape] at hfit
  have hcross :
      (epsilon' / 8) ^ 2 *
          (24576 * (2 : ℝ) ^ (J + 4) * cellCount ^ 2) ≤
        c3 * eps ^ 2 * logP :=
    (le_div_iff₀ hden).mp hfit
  have hlower :
      384 * (2 : ℝ) ^ (J + 4) * epsilon' ^ 2 * logP ^ 2 ≤
        c3 * eps ^ 2 * logP := by
    calc
      384 * (2 : ℝ) ^ (J + 4) * epsilon' ^ 2 * logP ^ 2 =
          (epsilon' / 8) ^ 2 *
            (24576 * (2 : ℝ) ^ (J + 4) * logP ^ 2) := by ring
      _ ≤ (epsilon' / 8) ^ 2 *
            (24576 * (2 : ℝ) ^ (J + 4) * cellCount ^ 2) := by
        gcongr
      _ ≤ c3 * eps ^ 2 * logP := hcross
  apply le_of_mul_le_mul_right _ hlogP
  convert hlower using 1
  all_goals ring

/-- Once `logP` exceeds the forced upper bound, the proposed uniform
exceptional prime fit is impossible.  The failed margin grows at least
linearly in `2^J * logP`. -/
theorem ladderExceptionalCellShare_prime_fit_fails_of_large_log
    (J : ℕ) (cellCount logP c3 eps epsilon' : ℝ)
    (hlogP : 0 < logP) (hcellCount : logP ≤ cellCount)
    (hepsilon' : 0 < epsilon')
    (hlarge : c3 * eps ^ 2 <
      384 * (2 : ℝ) ^ (J + 4) * epsilon' ^ 2 * logP) :
    ¬ ((epsilon' / 8) ^ 2 ≤
      ladderExceptionalCellShare J cellCount * c3 * eps ^ 2 * logP /
        (24 * 1024)) := by
  intro hfit
  exact (not_le_of_gt hlarge)
    (ladderExceptionalCellShare_prime_fit_forces_log_upper J cellCount logP
      c3 eps epsilon' hlogP hcellCount hepsilon' hfit)

/-- **Share-independent form of the L3-5 obstruction.**  Suppose the summed
prime parts of the exceptional cell fits cost at least
`64*d^2*E/logQ`, as they do for unit-modulus prime coefficients, and the
e-adic cover has at least `logQ` cells.  The aggregate exceptional share then
forces `1024*2^(J+1)*d^2*E <= c3*eps^2`.

Thus redistributing the cell shares cannot repair the geometric loss. -/
theorem ladderExceptionalAggregate_prime_fit_forces_level_upper
    (J : ℕ) (cellCount logQ totalShareCost budget d E c3 eps : ℝ)
    (hlogQ : 0 < logQ) (hcellCount : logQ ≤ cellCount)
    (hd : 0 < d) (hE : 0 < E)
    (hprime : 64 * d ^ 2 * E / logQ ≤ totalShareCost)
    (haggregate : 2 * cellCount * totalShareCost ≤
      (1 / (2 : ℝ) ^ (J + 1)) * budget)
    (hbudget : budget ≤ c3 * eps ^ 2 / 8) :
    1024 * (2 : ℝ) ^ (J + 1) * d ^ 2 * E ≤ c3 * eps ^ 2 := by
  have htotal0 : 0 ≤ totalShareCost := by
    exact le_trans (by positivity : 0 ≤ 64 * d ^ 2 * E / logQ) hprime
  have hcost : 128 * d ^ 2 * E ≤ 2 * cellCount * totalShareCost := by
    calc
      128 * d ^ 2 * E =
          2 * logQ * (64 * d ^ 2 * E / logQ) := by field_simp; ring
      _ ≤ 2 * logQ * totalShareCost :=
        mul_le_mul_of_nonneg_left hprime (by positivity)
      _ ≤ 2 * cellCount * totalShareCost := by gcongr
  have hpow0 : 0 < (2 : ℝ) ^ (J + 1) := by positivity
  have hscaled : 128 * d ^ 2 * E ≤
      c3 * eps ^ 2 / (8 * (2 : ℝ) ^ (J + 1)) := by
    calc
      128 * d ^ 2 * E ≤ 2 * cellCount * totalShareCost := hcost
      _ ≤ (1 / (2 : ℝ) ^ (J + 1)) * budget := haggregate
      _ ≤ (1 / (2 : ℝ) ^ (J + 1)) * (c3 * eps ^ 2 / 8) := by
        gcongr
      _ = c3 * eps ^ 2 / (8 * (2 : ℝ) ^ (J + 1)) := by ring
  have hden : 0 < 8 * (2 : ℝ) ^ (J + 1) := by positivity
  have := (le_div_iff₀ hden).mp hscaled
  nlinarith

/-- With the sharp envelope's fixed floor `d = epsilon'/8`, the preceding
necessary condition has the simpler exact coefficient `16`. -/
theorem ladderExceptionalAggregate_fixed_floor_forces_level_upper
    (J : ℕ) (cellCount logQ totalShareCost budget E c3 eps epsilon' : ℝ)
    (hlogQ : 0 < logQ) (hcellCount : logQ ≤ cellCount)
    (hE : 0 < E) (hepsilon' : 0 < epsilon')
    (hprime : 64 * (epsilon' / 8) ^ 2 * E / logQ ≤ totalShareCost)
    (haggregate : 2 * cellCount * totalShareCost ≤
      (1 / (2 : ℝ) ^ (J + 1)) * budget)
    (hbudget : budget ≤ c3 * eps ^ 2 / 8) :
    16 * (2 : ℝ) ^ (J + 1) * epsilon' ^ 2 * E ≤ c3 * eps ^ 2 := by
  have hraw := ladderExceptionalAggregate_prime_fit_forces_level_upper
    J cellCount logQ totalShareCost budget (epsilon' / 8) E c3 eps
    hlogQ hcellCount (by positivity) hE hprime haggregate hbudget
  nlinarith

end Tao2015

end MoltResearch
