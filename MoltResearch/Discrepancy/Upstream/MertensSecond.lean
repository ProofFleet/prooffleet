import MoltResearch.Discrepancy.MertensFloor
import MoltResearch.Discrepancy.PrimeMassCell
import MoltResearch.Discrepancy.BrunIntervalSieve

/-!
# Upstreaming slot UP-2: Mertens' second theorem

Pre-allocated leaf for card item UP-2 of `Problems/nucleus_upstreaming.md`. The claimant of UP-2 fills this file with
the Mathlib-style restatement, proved from the imported tree lemmas; no other file is to be edited.
-/

namespace MoltResearch

namespace Upstream

open Finset

/-- The prime harmonic sum up to `x` lies between `log log x - 1` and
`log log x + 12`.  This is the explicit-constant form of Mertens' second
theorem, first proved in F. Mertens, *Ein Beitrag zur analytischen
Zahlentheorie*, J. Reine Angew. Math. 78 (1874), 46--62. -/
theorem mertens_second_bounds (x : ℕ) (hx : 3 ≤ x) :
    Real.log (Real.log (x : ℝ)) - 1 ≤
        ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ∧
      ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
        Real.log (Real.log (x : ℝ)) + 12 := by
  classical
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hx3 : (3 : ℝ) ≤ x := by exact_mod_cast hx
  have hlogx0 : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hcast : ((x + 1 : ℕ) : ℝ) = (x : ℝ) + 1 := by push_cast; ring
  have hprime_set :
      (Finset.Icc 1 x).filter Nat.Prime = (x + 1).primesBelow := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hp1, hpx⟩, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpx, hp⟩
      exact ⟨⟨hp.one_lt.le, by omega⟩, hp⟩
  have hIoc_set :
      (Finset.Ioc 1 x).filter Nat.Prime =
        (Finset.Icc 1 x).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp1, hpx⟩, hp⟩
      exact ⟨⟨hp1.le, hpx⟩, hp⟩
    · rintro ⟨⟨_, hpx⟩, hp⟩
      exact ⟨⟨hp.one_lt, hpx⟩, hp⟩
  constructor
  · have hfloor := log_log_le_sum_one_div_primesBelow
        (y := x + 1) (by omega : 2 ≤ x + 1)
    rw [← hprime_set, hcast] at hfloor
    have hlog_mono : Real.log (x : ℝ) ≤ Real.log ((x : ℝ) + 1) :=
      Real.log_le_log hx0 (by linarith)
    have hloglog_mono :
        Real.log (Real.log (x : ℝ)) ≤
          Real.log (Real.log ((x : ℝ) + 1)) :=
      Real.log_le_log hlogx0 hlog_mono
    linarith
  · have hupp := sum_one_div_prime_Ioc_le_mertens 1 x hx
    rw [hIoc_set] at hupp
    have hxp1_pos : (0 : ℝ) < (x : ℝ) + 1 := by positivity
    have hxp1_one : (1 : ℝ) < (x : ℝ) + 1 := by linarith
    have hsq : (x : ℝ) + 1 ≤ (x : ℝ) ^ 2 := by
      nlinarith
    have hlog_sq :
        Real.log ((x : ℝ) + 1) ≤ 2 * Real.log (x : ℝ) := by
      calc
        Real.log ((x : ℝ) + 1) ≤ Real.log ((x : ℝ) ^ 2) :=
          Real.log_le_log hxp1_pos hsq
        _ = 2 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_num
    have houter :
        Real.log (Real.log ((x : ℝ) + 1)) ≤
          Real.log (2 * Real.log (x : ℝ)) :=
      Real.log_le_log (Real.log_pos hxp1_one) hlog_sq
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hlogx0)] at houter
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith

/-- The usual absolute-value formulation of Mertens' second theorem, with
the explicit constant `12`. -/
theorem mertens_second_theorem (x : ℕ) (hx : 3 ≤ x) :
    |∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime, (1 : ℝ) / (p : ℝ) -
        Real.log (Real.log (x : ℝ))| ≤ 12 := by
  rw [abs_le]
  rcases mertens_second_bounds x hx with ⟨hlow, hupp⟩
  constructor <;> linarith

/-- The interval form of the lower half of Mertens' second theorem. -/
theorem mertens_second_Ioc_lower (lo hi : ℕ) (hlo : 3 ≤ lo) (hlohi : lo ≤ hi) :
    Real.log (Real.log ((hi : ℝ) + 1)) -
        Real.log (Real.log ((lo : ℝ) + 1)) - 12 ≤
      ∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
  exact prime_Ioc_mass_lower_mertens lo hi hlo hlohi

example (x : ℕ) (hx : 3 ≤ x) :
    |∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime, (1 : ℝ) / (p : ℝ) -
        Real.log (Real.log (x : ℝ))| ≤ 12 :=
  mertens_second_theorem x hx

end Upstream

end MoltResearch
