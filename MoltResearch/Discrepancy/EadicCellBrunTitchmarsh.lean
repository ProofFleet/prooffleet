import MoltResearch.Discrepancy.BrunTitchmarsh
import MoltResearch.Discrepancy.TypicalFactorization

/-!
# Brun--Titchmarsh for a fine e-adic cell

This leaf keeps the cell-width saving which is lost when an e-adic cell is
enlarged to the dyadic interval `(P, 2P]`.  At resolution `2N`, a cell above
its integer lower anchor has length `O(P/N)`, so Brun--Titchmarsh gives
`#cell ≪ P/(N log P)`.
-/

namespace MoltResearch

open Finset

/-- Lower endpoint of the contiguous index range covering `(Plo,Qhi]`. -/
noncomputable def eadicCoverIndexLower (N Plo : ℕ) : ℕ :=
  ⌈(N : ℝ) * Real.log Plo⌉₊ - 1

/-- Upper endpoint of the contiguous index range covering `(Plo,Qhi]`. -/
noncomputable def eadicCoverIndexUpper (N Qhi : ℕ) : ℕ :=
  ⌊(N : ℝ) * Real.log Qhi⌋₊

/-- Every finite set contained in `(Plo,Qhi]` is covered by the expected
contiguous e-adic index range.  The lower index is shifted by one because the
left endpoint of the prime interval is strict. -/
theorem eadicCell_biUnion_Ico_eq
    (P : Finset ℕ) (N Plo Qhi : ℕ) (hN : 0 < N) (hPlo : 1 ≤ Plo)
    (hlo : ∀ p ∈ P, Plo < p) (hhi : ∀ p ∈ P, p ≤ Qhi) :
    (Finset.Ico (eadicCoverIndexLower N Plo)
        (eadicCoverIndexUpper N Qhi + 1)).biUnion (eadicCell P N) = P := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_Ico, mem_eadicCell]
  constructor
  · rintro ⟨v, -, hp, -⟩
    exact hp
  · intro hp
    let v : ℕ := ⌊(N : ℝ) * Real.log p⌋₊
    refine ⟨v, ?_, hp, rfl⟩
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hPloR : (0 : ℝ) < Plo := by exact_mod_cast (show 0 < Plo by omega)
    have hpR : (0 : ℝ) < p := by
      exact_mod_cast (lt_trans (show 0 < Plo by omega) (hlo p hp))
    have hlogp : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hPlo.trans (Nat.le_of_lt (hlo p hp)))
    have halow :
        (N : ℝ) * Real.log Plo < (N : ℝ) * Real.log p := by
      exact mul_lt_mul_of_pos_left
        (Real.log_lt_log hPloR (by exact_mod_cast hlo p hp)) hNR
    have hvfloor :
        (v : ℝ) ≤ (N : ℝ) * Real.log p := by
      dsimp [v]
      exact Nat.floor_le (mul_nonneg hNR.le hlogp)
    have hlowerCeil :
        ⌈(N : ℝ) * Real.log Plo⌉₊ ≤ v + 1 := by
      apply Nat.ceil_le.mpr
      have hvnext : (N : ℝ) * Real.log p < (v : ℝ) + 1 := by
        dsimp [v]
        exact Nat.lt_floor_add_one _
      simpa only [Nat.cast_add, Nat.cast_one] using (halow.trans hvnext).le
    have hlower : eadicCoverIndexLower N Plo ≤ v := by
      unfold eadicCoverIndexLower
      omega
    have hlogupper : Real.log (p : ℝ) ≤ Real.log Qhi := by
      exact Real.log_le_log hpR (by exact_mod_cast hhi p hp)
    have hvupperR : (v : ℝ) ≤ (N : ℝ) * Real.log Qhi := by
      calc
        (v : ℝ) ≤ (N : ℝ) * Real.log p := hvfloor
        _ ≤ (N : ℝ) * Real.log Qhi :=
          mul_le_mul_of_nonneg_left hlogupper hNR.le
    have hvupper : v ≤ eadicCoverIndexUpper N Qhi := by
      unfold eadicCoverIndexUpper
      exact Nat.le_floor hvupperR
    exact ⟨hlower, Nat.lt_succ_of_le hvupper⟩

/-- The greatest integer which is certainly strictly below every integer in
the e-adic cell.  The `ceil - 1` form also handles an integral lower endpoint. -/
noncomputable def eadicCellLowerAnchor (N v : ℕ) : ℕ :=
  ⌈Real.exp ((v : ℝ) / (2 * (N : ℝ)))⌉₊ - 1

/-- A convenient integral envelope for the cell's additive width. -/
noncomputable def eadicCellBrunLength (N v : ℕ) : ℕ :=
  eadicCellLowerAnchor N v / N + 3

/-- The lower anchor is one below the lower-endpoint ceiling. -/
theorem eadicCellLowerAnchor_add_one (N v : ℕ)
    (hceil : 1 ≤ ⌈Real.exp ((v : ℝ) / (2 * (N : ℝ)))⌉₊) :
    eadicCellLowerAnchor N v + 1 =
      ⌈Real.exp ((v : ℝ) / (2 * (N : ℝ)))⌉₊ := by
  unfold eadicCellLowerAnchor
  exact Nat.sub_add_cancel hceil

/-- Once the integral anchor is positive, twice the anchor dominates the
real lower endpoint. -/
theorem exp_cell_lower_le_two_anchor (N v : ℕ)
    (hPc : 1 ≤ eadicCellLowerAnchor N v) :
    Real.exp ((v : ℝ) / (2 * (N : ℝ))) ≤
      2 * (eadicCellLowerAnchor N v : ℝ) := by
  let x : ℝ := Real.exp ((v : ℝ) / (2 * (N : ℝ)))
  let Pc : ℕ := eadicCellLowerAnchor N v
  have hceil1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
  have hx : x ≤ (Pc : ℝ) + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add,
      eadicCellLowerAnchor_add_one N v (by simpa [x] using hceil1)]
    exact Nat.le_ceil x
  have hPcR : (1 : ℝ) ≤ Pc := by exact_mod_cast hPc
  dsimp [x, Pc] at hx ⊢
  linarith

/-- A cell at resolution `2N` lies in the short interval beginning at its
lower anchor and having length `anchor / N + 3`. -/
theorem eadicCell_subset_brun_interval
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N v : ℕ) (hN : 0 < N) :
    eadicCell P (2 * N) v ⊆
      (Finset.Ioc (eadicCellLowerAnchor N v)
        (eadicCellLowerAnchor N v + eadicCellBrunLength N v)).filter Nat.Prime := by
  intro p hp
  rw [Finset.mem_filter, Finset.mem_Ioc]
  have hpP := (mem_eadicCell.mp hp).1
  have hp1 : 1 ≤ p := (hP p hpP).one_le
  have hbounds := eadicCell_bounds (by omega : 0 < 2 * N) hp hp1
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  rw [hcast] at hbounds
  let x : ℝ := Real.exp ((v : ℝ) / (2 * (N : ℝ)))
  let Pc : ℕ := eadicCellLowerAnchor N v
  let K : ℕ := eadicCellBrunLength N v
  have hx0 : 0 < x := Real.exp_pos _
  have hceil1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx0
  have hPcCeil : Pc + 1 = ⌈x⌉₊ := by
    dsimp [Pc, eadicCellLowerAnchor, x]
    exact Nat.sub_add_cancel hceil1
  have hxPc : x ≤ (Pc : ℝ) + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, hPcCeil]
    exact Nat.le_ceil x
  have hceilp : ⌈x⌉₊ ≤ p := Nat.ceil_le.mpr (by simpa [x] using hbounds.1)
  have hPclt : Pc < p := by omega
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hstep0 : 0 < 1 / (2 * (N : ℝ)) := by positivity
  have hstep1 : |1 / (2 * (N : ℝ))| ≤ 1 := by
    rw [abs_of_pos hstep0, div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 2 * N by omega)
  have hexp : Real.exp (1 / (2 * (N : ℝ))) ≤ 1 + 1 / (N : ℝ) := by
    have habs := Real.abs_exp_sub_one_le hstep1
    have hright := (abs_le.mp habs).2
    rw [abs_of_pos hstep0] at hright
    have : (2 : ℝ) * (1 / (2 * (N : ℝ))) = 1 / (N : ℝ) := by field_simp
    linarith
  have hsplit : ((v : ℝ) + 1) / (2 * (N : ℝ)) =
      (v : ℝ) / (2 * (N : ℝ)) + 1 / (2 * (N : ℝ)) := by
    field_simp
  have hpupper : (p : ℝ) < ((Pc : ℝ) + 1) * (1 + 1 / (N : ℝ)) := by
    calc
      (p : ℝ) < Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) := hbounds.2
      _ = x * Real.exp (1 / (2 * (N : ℝ))) := by
        rw [hsplit, Real.exp_add]
      _ ≤ ((Pc : ℝ) + 1) * (1 + 1 / (N : ℝ)) := by
        exact mul_le_mul hxPc hexp (Real.exp_pos _).le (by positivity)
  have hdivNat : Pc < (Pc / N + 1) * N :=
    (Nat.div_lt_iff_lt_mul hN).mp (Nat.lt_succ_self (Pc / N))
  have hdiv : (Pc : ℝ) / (N : ℝ) < (Pc / N : ℕ) + 1 := by
    rw [div_lt_iff₀ hN0]
    exact_mod_cast hdivNat
  have hNinv : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hN0]
    exact_mod_cast hN
  have hexpand : ((Pc : ℝ) + 1) * (1 + 1 / (N : ℝ)) =
      (Pc : ℝ) + 1 + (Pc : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by
    field_simp
    ring
  have hpK : (p : ℝ) < (Pc + K : ℕ) := by
    calc
      (p : ℝ) < ((Pc : ℝ) + 1) * (1 + 1 / (N : ℝ)) := hpupper
      _ < (Pc : ℝ) + (Pc / N : ℕ) + 3 := by
        rw [hexpand]
        linarith
      _ = (Pc + K : ℕ) := by
        push_cast
        simp only [K, eadicCellBrunLength, Pc, Nat.cast_add, Nat.cast_ofNat]
        ring
  have hpKnat : p < Pc + K := by exact_mod_cast hpK
  exact ⟨⟨hPclt, hpKnat.le⟩, hP p hpP⟩

/-- At resolution at least four, a cell lies in the dyadic interval above
the strict lower anchor.  The harmless anchor threshold `6` absorbs integer
rounding. -/
theorem eadicCell_mem_lowerAnchor_dyadic
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N v : ℕ)
    (hN : 2 ≤ N) (hPc : 6 ≤ eadicCellLowerAnchor N v) :
    ∀ p ∈ eadicCell P (2 * N) v,
      eadicCellLowerAnchor N v < p ∧
        p ≤ 2 * eadicCellLowerAnchor N v := by
  intro p hp
  let Pc := eadicCellLowerAnchor N v
  let K := eadicCellBrunLength N v
  have hsub := eadicCell_subset_brun_interval P hP N v (by omega : 0 < N)
  have hpI := (Finset.mem_filter.mp (hsub hp)).1
  rw [Finset.mem_Ioc] at hpI
  change Pc < p ∧ p ≤ Pc + K at hpI
  have hdiv : Pc / N ≤ Pc / 2 := Nat.div_le_div_left hN (by omega)
  have hK : K ≤ Pc := by
    change Pc / N + 3 ≤ Pc
    have : Pc / 2 + 3 ≤ Pc := by
      dsimp [Pc] at hPc ⊢
      omega
    omega
  change Pc < p ∧ p ≤ 2 * Pc
  constructor
  · exact hpI.1
  · exact hpI.2.trans (by
      omega)

/-- Brun--Titchmarsh with the fine-cell width retained.  The scale hypothesis
`4N² ≤ P` is harmless in the intended polylogarithmic prime ranges and gives
the explicit constant `1024`. -/
theorem card_eadicCell_le_brun
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N v : ℕ) (hN : 0 < N)
    (hscale : 4 * N ^ 2 ≤ eadicCellLowerAnchor N v) :
    ((eadicCell P (2 * N) v).card : ℝ) ≤
      1024 * (eadicCellLowerAnchor N v : ℝ) /
        ((N : ℝ) * Real.log (eadicCellLowerAnchor N v)) := by
  let Pc : ℕ := eadicCellLowerAnchor N v
  let K : ℕ := eadicCellBrunLength N v
  have hN1 : 1 ≤ N := hN
  have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow 2 N hN
  have hPc4 : 4 ≤ Pc := by
    dsimp [Pc] at hscale ⊢
    omega
  have hPc1 : 1 < Pc := by omega
  have hPc0 : (0 : ℝ) < Pc := by positivity
  have hlogPc : 0 < Real.log (Pc : ℝ) := Real.log_pos (by exact_mod_cast hPc1)
  have hK3 : 3 ≤ K := by simp [K, eadicCellBrunLength]
  have hK2 : 2 ≤ K := by omega
  have hK0 : (0 : ℝ) < K := by positivity
  have hlogK : 0 < Real.log (K : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < K by omega))
  have hsub := eadicCell_subset_brun_interval P hP N v hN
  have hcard : ((eadicCell P (2 * N) v).card : ℝ) ≤
      (((Finset.Ioc Pc (Pc + K)).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hbt := card_primes_Ioc_le Pc K hK2
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdivNat : Pc < (Pc / N + 1) * N :=
    (Nat.div_lt_iff_lt_mul hN).mp (Nat.lt_succ_self (Pc / N))
  have hdivLower : (Pc : ℝ) / (2 * (N : ℝ)) ≤ (Pc / N : ℕ) := by
    have hdiv : (Pc : ℝ) / (N : ℝ) < (Pc / N : ℕ) + 1 := by
      rw [div_lt_iff₀ hN0]
      exact_mod_cast hdivNat
    have hx4 : 4 ≤ (Pc : ℝ) / (N : ℝ) := by
      rw [le_div_iff₀ hN0]
      have hscaleR : (4 : ℝ) * (N : ℝ) ^ 2 ≤ Pc := by exact_mod_cast hscale
      nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast hN1]
    have hhalf : (Pc : ℝ) / (2 * (N : ℝ)) =
        ((Pc : ℝ) / (N : ℝ)) / 2 := by field_simp
    rw [hhalf]
    linarith
  have hKLower : (Pc : ℝ) / (2 * (N : ℝ)) ≤ (K : ℝ) := by
    exact hdivLower.trans (by
      exact_mod_cast (Nat.le_add_right (Pc / N) 3))
  have hx4 : 4 ≤ (Pc : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ hN0]
    have hscaleR : (4 : ℝ) * (N : ℝ) ^ 2 ≤ Pc := by exact_mod_cast hscale
    nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast hN1]
  have hKUpper : (K : ℝ) ≤ 2 * (Pc : ℝ) / (N : ℝ) := by
    have hq : ((Pc / N : ℕ) : ℝ) ≤ (Pc : ℝ) / (N : ℝ) := Nat.cast_div_le
    have hKdef : K = Pc / N + 3 := by
      simp only [K, eadicCellBrunLength, Pc]
    calc
      (K : ℝ) = ((Pc / N : ℕ) : ℝ) + 3 := by exact_mod_cast hKdef
      _ ≤ (Pc : ℝ) / (N : ℝ) + 3 := by linarith
      _ ≤ 2 * ((Pc : ℝ) / (N : ℝ)) := by linarith
      _ = 2 * (Pc : ℝ) / (N : ℝ) := by ring
  have hscaleR : (4 : ℝ) * (N : ℝ) ^ 2 ≤ Pc := by exact_mod_cast hscale
  have hPcKsq : (Pc : ℝ) ≤ (K : ℝ) ^ 2 := by
    have hbase : (Pc : ℝ) ≤ ((Pc : ℝ) / (2 * (N : ℝ))) ^ 2 := by
      have hPcNonneg : (0 : ℝ) ≤ Pc := by positivity
      field_simp
      nlinarith
    exact hbase.trans (pow_le_pow_left₀ (by positivity) hKLower 2)
  have hlogRel : Real.log (Pc : ℝ) / 2 ≤ Real.log (K : ℝ) := by
    have hlog := Real.log_le_log hPc0 hPcKsq
    rw [Real.log_pow] at hlog
    norm_num at hlog
    nlinarith
  calc
    ((eadicCell P (2 * N) v).card : ℝ)
        ≤ (((Finset.Ioc Pc (Pc + K)).filter Nat.Prime).card : ℝ) := hcard
    _ ≤ 256 * (K : ℝ) / Real.log K := hbt
    _ ≤ 256 * (2 * (Pc : ℝ) / (N : ℝ)) / (Real.log Pc / 2) := by
      gcongr
    _ = 1024 * (Pc : ℝ) / ((N : ℝ) * Real.log Pc) := by
      field_simp
      norm_num

/-- The complementary sharp Mertens estimate on a prime interval.  Together
with `prime_Ioc_mass_lower_mertens`, it traps the interval mass to an absolute
additive constant. -/
theorem prime_Ioc_mass_upper_mertens (lo hi : ℕ)
    (hlo : 3 ≤ lo) (hlohi : lo ≤ hi) :
    ∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, (1 : ℝ) / p ≤
      Real.log (Real.log ((hi : ℝ) + 1)) -
        Real.log (Real.log ((lo : ℝ) + 1)) + 12 := by
  have hsub : (lo + 1).primesBelow ⊆ (hi + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hdiff :
      ∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, (1 : ℝ) / p =
        (∑ p ∈ (hi + 1).primesBelow, (1 : ℝ) / p) -
          ∑ p ∈ (lo + 1).primesBelow, (1 : ℝ) / p := by
    rw [← Finset.sum_sdiff_eq_sub hsub]
    apply Finset.sum_congr
    · ext p
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
        Nat.mem_primesBelow]
      constructor
      · rintro ⟨⟨hlop, hphi⟩, hpprime⟩
        exact ⟨⟨by omega, hpprime⟩, fun hp => by omega⟩
      · rintro ⟨⟨hphi, hpprime⟩, hnlo⟩
        exact ⟨⟨by
          by_contra h
          apply hnlo
          exact ⟨by omega, hpprime⟩, by omega⟩, hpprime⟩
    · intro p hp
      rfl
  have hupp := sum_one_div_primesBelow_le_sharp (hi + 1) (by omega)
  have hlow := log_log_le_sum_one_div_primesBelow (y := lo + 1) (by omega)
  have hcastlo : ((lo + 1 : ℕ) : ℝ) = (lo : ℝ) + 1 := by push_cast; ring
  have hcasthi : ((hi + 1 : ℕ) : ℝ) = (hi : ℝ) + 1 := by push_cast; ring
  rw [hcastlo] at hlow
  rw [hcasthi] at hupp
  rw [hdiff]
  linarith

end MoltResearch
