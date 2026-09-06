import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2BrunMain

/-!
# Track R A2-V'-27: geometric Brun saving along the positive ladder

The positive-level ratios start at `2 eta` and double thereafter.  Once
`epsc * eta` pays `64 exp(12)`, the sum of all Euler-product and canonical-tail
terms uses only one eighth of the density budget.  The remainder is an
explicit finite sum, ready for the cutoff estimate.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The finite Brun error for the prime interval `(P, P^R]`. -/
noncomputable def brunPowerIntervalFiniteError (a P R : ℕ) : ℝ :=
  let L := (Ioc P (P ^ R)).filter Nat.Prime
  let E := ∑ p ∈ L, (1 : ℝ) / p
  let k := ⌈Real.exp 1 * E⌉₊
  2 * ((L.card : ℝ) + 1) ^ (2 * k) / a

/-- At a positive level, the scheduled ratio dominates `2^j eta`. -/
theorem sliceA2LadderRatio_geometric
    (ratio0 eta j : ℕ) (hj : 0 < j) :
    2 ^ j * eta ≤ sliceA2LadderRatio ratio0 eta j := by
  rw [sliceA2LadderRatio_of_pos ratio0 eta j hj]
  exact le_max_right _ _

/-- The chosen initial later-level ratio gives each main Brun term its
geometric density share. -/
theorem sliceA2BrunMainCoefficient_le
    (ratio0 eta j : ℕ) (epsc : ℝ) (hj : 0 < j)
    (heta : 64 * Real.exp 12 ≤ epsc * eta) :
    8 * Real.exp 12 / sliceA2LadderRatio ratio0 eta j ≤
      epsc / (8 * 2 ^ j) := by
  let q : ℕ := 2 ^ j
  let R := sliceA2LadderRatio ratio0 eta j
  have hq0 : (0 : ℝ) < q := by positivity
  have heta0 : (0 : ℝ) < eta := by
    have hetaNat : 0 < eta := by
      by_contra h
      have hz : eta = 0 := Nat.eq_zero_of_not_pos h
      subst eta
      norm_num at heta
      nlinarith [Real.exp_pos 12]
    exact_mod_cast hetaNat
  have hqeta : (0 : ℝ) < q * eta := mul_pos hq0 heta0
  have hratio : (q : ℝ) * eta ≤ R := by
    exact_mod_cast sliceA2LadderRatio_geometric ratio0 eta j hj
  have hfirst : 8 * Real.exp 12 / (R : ℝ) ≤
      8 * Real.exp 12 / ((q : ℝ) * eta) := by
    exact div_le_div_of_nonneg_left (by positivity) hqeta hratio
  have hbudget : 8 * Real.exp 12 / ((q : ℝ) * eta) ≤
      epsc / (8 * q) := by
    rw [div_le_div_iff₀ hqeta (mul_pos (by norm_num) hq0)]
    have hqnonneg : (0 : ℝ) ≤ q := hq0.le
    calc
      8 * Real.exp 12 * (8 * q) = q * (64 * Real.exp 12) := by ring
      _ ≤ q * (epsc * eta) :=
        mul_le_mul_of_nonneg_left heta hqnonneg
      _ = epsc * (q * eta) := by ring
  simpa [q, R] using hfirst.trans hbudget

set_option maxHeartbeats 800000 in
/-- All positive-ladder main Brun terms together occupy at most one eighth
of the logarithmic mass. -/
theorem sliceA2PositiveLadder_brun_le_main_add_errors
    (P0 ratio0 eta n a : ℕ) (epsc : ℝ)
    (ha : 1 ≤ a) (hP0 : 3 ≤ P0) (hepsc : 0 < epsc)
    (heta : 64 * Real.exp 12 ≤ epsc * eta) :
    ladderSiftedLogMass a (2 * a)
        ((List.range n).map
          (fun i ↦ sliceA2LadderPrimes P0 ratio0 eta (i + 1))) ≤
      (epsc / 8) * (∑ m ∈ Ioc a (2 * a), (1 : ℝ) / m) +
        ∑ i ∈ range n,
          brunPowerIntervalFiniteError a
            (sliceA2LadderP P0 ratio0 eta (i + 1))
            (sliceA2LadderRatio ratio0 eta (i + 1)) := by
  classical
  let H : ℝ := ∑ m ∈ Ioc a (2 * a), (1 : ℝ) / m
  let err : ℕ → ℝ := fun i ↦
    brunPowerIntervalFiniteError a
      (sliceA2LadderP P0 ratio0 eta (i + 1))
      (sliceA2LadderRatio ratio0 eta (i + 1))
  let c : ℕ → ℝ := fun i ↦
    8 * Real.exp 12 / sliceA2LadderRatio ratio0 eta (i + 1)
  have hsum : ladderSiftedLogMass a (2 * a)
      ((List.range n).map
        (fun i ↦ sliceA2LadderPrimes P0 ratio0 eta (i + 1))) ≤
      ∑ i ∈ range n, (c i * H + err i) := by
    refine ladderSiftedLogMass_map_le a (2 * a) n
      (fun i ↦ sliceA2LadderPrimes P0 ratio0 eta (i + 1))
      (fun i ↦ c i * H + err i) ?_
    intro i hi
    have hPi : 3 ≤ sliceA2LadderP P0 ratio0 eta (i + 1) :=
      hP0.trans (sliceA2LadderP_mono P0 ratio0 eta (by omega)
        (Nat.zero_le (i + 1)))
    have hRi := sliceA2LadderRatio_two_le ratio0 eta (i + 1)
    simpa [sliceA2LadderPrimes, c, H, err,
      brunPowerIntervalFiniteError] using
      no_factor_density_prime_power_le a
        (sliceA2LadderP P0 ratio0 eta (i + 1))
        (sliceA2LadderRatio ratio0 eta (i + 1)) ha hPi hRi
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hcpoint : ∀ i, c i ≤ epsc / (8 * 2 ^ (i + 1)) := by
    intro i
    exact sliceA2BrunMainCoefficient_le ratio0 eta (i + 1) epsc
      (by omega) heta
  have hcsum : ∑ i ∈ range n, c i ≤ epsc / 8 := by
    calc
      ∑ i ∈ range n, c i ≤
          ∑ i ∈ range n, epsc / (8 * 2 ^ (i + 1)) :=
        sum_le_sum fun i hi ↦ hcpoint i
      _ = (epsc / 8) *
          ∑ i ∈ range n, (1 : ℝ) / 2 ^ (i + 1) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        ring
      _ ≤ (epsc / 8) * 1 :=
        mul_le_mul_of_nonneg_left (geometric_shares_le_one n)
          (by positivity)
      _ = epsc / 8 := by ring
  calc
    ladderSiftedLogMass a (2 * a)
        ((List.range n).map
          (fun i ↦ sliceA2LadderPrimes P0 ratio0 eta (i + 1))) ≤
        ∑ i ∈ range n, (c i * H + err i) := hsum
    _ = (∑ i ∈ range n, c i) * H + ∑ i ∈ range n, err i := by
      rw [sum_add_distrib, sum_mul]
    _ ≤ (epsc / 8) * H + ∑ i ∈ range n, err i := by
      gcongr
    _ = _ := rfl

end Tao2015

end MoltResearch
