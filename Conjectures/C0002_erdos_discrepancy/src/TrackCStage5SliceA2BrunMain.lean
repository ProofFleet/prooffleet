import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2DensityWindow

/-!
# Track R A2-V'-26: the main Brun saving along the positive ladder

The canonical Brun truncation tail is no larger than its Euler-product term.
For a prime interval `(P, P^R]`, lower Mertens then prices both terms by
`2 exp(12) / R`.  This leaf also records the duplicate-safe passage from
levelwise estimates to the list-valued ladder remainder.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The tail at the canonical Brun depth is bounded by the exponential of
the negative reciprocal-prime mass. -/
theorem brunCanonicalTail_le_exp_neg (E : ℝ) (hE : 0 ≤ E) :
    let k := ⌈Real.exp 1 * E⌉₊
    (2 : ℝ) ^ (-(↑(2 * k + 1) : ℤ)) ≤ Real.exp (-E) := by
  let k := ⌈Real.exp 1 * E⌉₊
  have hkceil : Real.exp 1 * E ≤ (k : ℝ) := Nat.le_ceil _
  have hexpone : (1 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hEk : E ≤ (k : ℝ) := by
    calc
      E = 1 * E := by ring
      _ ≤ Real.exp 1 * E :=
        mul_le_mul_of_nonneg_right hexpone hE
      _ ≤ (k : ℝ) := hkceil
  have hlog : E ≤ (2 * (k : ℝ) + 1) * Real.log 2 := by
    have hlogtwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    have hk0 : (0 : ℝ) ≤ k := by positivity
    calc
      E ≤ (k : ℝ) := hEk
      _ ≤ (2 * (k : ℝ) + 1) * Real.log 2 := by
        nlinarith
  have htailpos : (0 : ℝ) < (2 : ℝ) ^ (-(↑(2 * k + 1) : ℤ)) :=
    zpow_pos (by norm_num) _
  rw [← Real.log_le_log_iff htailpos (Real.exp_pos (-E))]
  rw [Real.log_zpow, Real.log_exp]
  push_cast
  linarith

/-- Lower Mertens on `(P, P^R]` turns the Euler-product exponential into
the reciprocal interval ratio. -/
theorem exp_neg_prime_power_mass_le
    (P R : ℕ) (hP : 3 ≤ P) (hR : 2 ≤ R)
    (E : ℝ)
    (hmass : E = ∑ p ∈ (Ioc P (P ^ R)).filter Nat.Prime,
      (1 : ℝ) / p) :
    Real.exp (-E) ≤ 2 * Real.exp 12 / R := by
  have hlow := prime_power_Ioc_mass_lower P R hP hR
  rw [← hmass] at hlow
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  calc
    Real.exp (-E) ≤
        Real.exp (-(Real.log (R : ℝ) - Real.log 2 - 12)) :=
      Real.exp_le_exp.mpr (neg_le_neg hlow)
    _ = 2 * Real.exp 12 / R := by
      rw [show -(Real.log (R : ℝ) - Real.log 2 - 12) =
        Real.log 2 + 12 - Real.log (R : ℝ) by ring]
      rw [Real.exp_sub, Real.exp_add, Real.exp_log (by norm_num),
        Real.exp_log hRpos]

/-- A single power-interval level has geometric main cost, plus the explicit
finite Brun error. -/
theorem no_factor_density_prime_power_le
    (a P R : ℕ) (ha : 1 ≤ a) (hP : 3 ≤ P) (hR : 2 ≤ R) :
    let L := (Ioc P (P ^ R)).filter Nat.Prime
    let E := ∑ p ∈ L, (1 : ℝ) / p
    let k := ⌈Real.exp 1 * E⌉₊
    (∑ m ∈ (Ioc a (2 * a)).filter (fun m ↦ ∀ p ∈ L, ¬ p ∣ m),
        (1 : ℝ) / m) ≤
      (8 * Real.exp 12 / R) *
          (∑ m ∈ Ioc a (2 * a), (1 : ℝ) / m) +
        2 * ((L.card : ℝ) + 1) ^ (2 * k) / a := by
  let L := (Ioc P (P ^ R)).filter Nat.Prime
  let E := ∑ p ∈ L, (1 : ℝ) / p
  let k := ⌈Real.exp 1 * E⌉₊
  have hprime : ∀ p ∈ L, p.Prime := by
    intro p hp
    exact (mem_filter.mp hp).2
  have hE : 0 ≤ E := by
    dsimp [E, L]
    positivity
  have hraw := no_factor_density_le_of_ratio a ha L hprime E hE rfl
  have htail := brunCanonicalTail_le_exp_neg E hE
  have hexp := exp_neg_prime_power_mass_le P R hP hR E rfl
  dsimp only at hraw
  have hH : 0 ≤ ∑ m ∈ Ioc a (2 * a), (1 : ℝ) / m := by positivity
  have hcoef : 2 * (Real.exp (-E) +
      (2 : ℝ) ^ (-(↑(2 * k + 1) : ℤ))) ≤
      8 * Real.exp 12 / R := by
    calc
      2 * (Real.exp (-E) +
          (2 : ℝ) ^ (-(↑(2 * k + 1) : ℤ))) ≤
          4 * Real.exp (-E) := by nlinarith
      _ ≤ 4 * (2 * Real.exp 12 / R) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 8 * Real.exp 12 / R := by ring
  calc
    _ ≤ 2 * (Real.exp (-E) +
          (2 : ℝ) ^ (-(↑(2 * k + 1) : ℤ))) *
          (∑ m ∈ Ioc a (2 * a), (1 : ℝ) / m) +
        2 * ((L.card : ℝ) + 1) ^ (2 * k) / a := hraw
    _ ≤ (8 * Real.exp 12 / R) *
          (∑ m ∈ Ioc a (2 * a), (1 : ℝ) / m) +
        2 * ((L.card : ℝ) + 1) ^ (2 * k) / a := by
      gcongr

/-- Levelwise upper bounds may be summed over a mapped list even if two
levels happen to coincide. -/
theorem ladderSiftedLogMass_map_le
    (a b n : ℕ) (L : ℕ → Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ i < n,
      ∑ m ∈ (Ioc a b).filter (fun m ↦ ∀ p ∈ L i, ¬ p ∣ m),
        (1 : ℝ) / m ≤ w i) :
    ladderSiftedLogMass a b ((List.range n).map L) ≤
      ∑ i ∈ range n, w i := by
  classical
  unfold ladderSiftedLogMass
  have hset : ((List.range n).map L).toFinset = (range n).image L := by
    ext Q
    simp
  rw [hset]
  refine (sum_image_le_of_nonneg (fun i hi ↦ ?_)).trans ?_
  · exact Finset.sum_nonneg fun m hm ↦ by positivity
  · exact sum_le_sum fun i hi ↦ hw i (mem_range.mp hi)

end Tao2015

end MoltResearch
