import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2LowBand

/-!
# Track R A2-V'-2: the final two-ratio ladder

The bottom interval and the later ladder have different jobs.  Its logarithmic
length is fixed by the density parameter `epsc`; making it depend on the
mean-square accuracy would turn the lower bound `P0 > C (log h)^B` into a
super-polynomial condition on `h`.  Only the levels after zero need the
`1/eps` ratios which pay the growing-ladder sieve remainder.

This leaf records the resulting sequence without changing the earlier L3
lemmas.  The jump remains exactly `P_(j+1) = Q_j^(100 (j+1)^2)`, so all of the
per-cell numerology applies unchanged.
-/

namespace MoltResearch

namespace Tao2015

/-- The bottom ratio is `ratio0`; from level one onward the ratios grow
geometrically from `eta`. -/
def sliceA2LadderRatio (ratio0 eta j : ℕ) : ℕ :=
  if j = 0 then max 2 ratio0 else max 2 (2 ^ j * eta)

@[simp] theorem sliceA2LadderRatio_zero (ratio0 eta : ℕ) :
    sliceA2LadderRatio ratio0 eta 0 = max 2 ratio0 := by
  simp [sliceA2LadderRatio]

theorem sliceA2LadderRatio_of_pos (ratio0 eta j : ℕ) (hj : 0 < j) :
    sliceA2LadderRatio ratio0 eta j = max 2 (2 ^ j * eta) := by
  simp [sliceA2LadderRatio, Nat.ne_of_gt hj]

theorem sliceA2LadderRatio_two_le (ratio0 eta j : ℕ) :
    2 ≤ sliceA2LadderRatio ratio0 eta j := by
  unfold sliceA2LadderRatio
  split_ifs <;> exact le_max_left _ _

/-- Lower endpoints of the final ordinary ladder. -/
def sliceA2LadderP (P0 ratio0 eta : ℕ) : ℕ → ℕ
  | 0 => P0
  | j + 1 =>
      (sliceA2LadderP P0 ratio0 eta j ^
          sliceA2LadderRatio ratio0 eta j) ^ (100 * (j + 1) ^ 2)

/-- Upper endpoints of the final ordinary ladder. -/
def sliceA2LadderQ (P0 ratio0 eta j : ℕ) : ℕ :=
  sliceA2LadderP P0 ratio0 eta j ^ sliceA2LadderRatio ratio0 eta j

@[simp] theorem sliceA2LadderP_zero (P0 ratio0 eta : ℕ) :
    sliceA2LadderP P0 ratio0 eta 0 = P0 := rfl

@[simp] theorem sliceA2LadderQ_eq (P0 ratio0 eta j : ℕ) :
    sliceA2LadderQ P0 ratio0 eta j =
      sliceA2LadderP P0 ratio0 eta j ^
        sliceA2LadderRatio ratio0 eta j := rfl

@[simp] theorem sliceA2LadderP_succ (P0 ratio0 eta j : ℕ) :
    sliceA2LadderP P0 ratio0 eta (j + 1) =
      sliceA2LadderQ P0 ratio0 eta j ^ (100 * (j + 1) ^ 2) := rfl

theorem sliceA2LadderP_two_le
    (P0 ratio0 eta j : ℕ) (hP0 : 2 ≤ P0) :
    2 ≤ sliceA2LadderP P0 ratio0 eta j := by
  induction j with
  | zero => simpa using hP0
  | succ j ih =>
      rw [sliceA2LadderP_succ]
      have hQ : 2 ≤ sliceA2LadderQ P0 ratio0 eta j := by
        rw [sliceA2LadderQ_eq]
        exact ih.trans (Nat.le_pow (by
          have := sliceA2LadderRatio_two_le ratio0 eta j
          omega))
      exact hQ.trans (Nat.le_pow (by positivity : 0 < 100 * (j + 1) ^ 2))

theorem sliceA2LadderP_le_Q (P0 ratio0 eta j : ℕ) :
    sliceA2LadderP P0 ratio0 eta j ≤
      sliceA2LadderQ P0 ratio0 eta j := by
  rw [sliceA2LadderQ_eq]
  exact Nat.le_pow (by
    have := sliceA2LadderRatio_two_le ratio0 eta j
    omega)

theorem sliceA2LadderQ_lt_P_succ
    (P0 ratio0 eta j : ℕ) (hP0 : 2 ≤ P0) :
    sliceA2LadderQ P0 ratio0 eta j <
      sliceA2LadderP P0 ratio0 eta (j + 1) := by
  rw [sliceA2LadderP_succ]
  let Q := sliceA2LadderQ P0 ratio0 eta j
  have hQ : 2 ≤ Q :=
    (sliceA2LadderP_two_le P0 ratio0 eta j hP0).trans
      (sliceA2LadderP_le_Q P0 ratio0 eta j)
  have hQ2 : Q < Q ^ 2 := by rw [pow_two]; nlinarith
  have hjpow : 1 ≤ (j + 1) ^ 2 := by rw [pow_two]; nlinarith
  have hexp : 2 ≤ 100 * (j + 1) ^ 2 := by omega
  exact hQ2.trans_le (pow_le_pow_right' (by omega : 1 ≤ Q) hexp)

theorem sliceA2LadderP_mono (P0 ratio0 eta : ℕ) (hP0 : 2 ≤ P0) :
    Monotone (sliceA2LadderP P0 ratio0 eta) := by
  apply monotone_nat_of_le_succ
  intro j
  exact (sliceA2LadderP_le_Q P0 ratio0 eta j).trans
    (sliceA2LadderQ_lt_P_succ P0 ratio0 eta j hP0).le

theorem sliceA2LadderQ_lt_P_of_lt
    (P0 ratio0 eta i j : ℕ) (hP0 : 2 ≤ P0) (hij : i < j) :
    sliceA2LadderQ P0 ratio0 eta i <
      sliceA2LadderP P0 ratio0 eta j := by
  exact (sliceA2LadderQ_lt_P_succ P0 ratio0 eta i hP0).trans_le
    (sliceA2LadderP_mono P0 ratio0 eta hP0 (Nat.succ_le_iff.mpr hij))

/-- Prime set at a final ordinary level. -/
def sliceA2LadderPrimes (P0 ratio0 eta j : ℕ) : Finset ℕ :=
  (Finset.Ioc (sliceA2LadderP P0 ratio0 eta j)
    (sliceA2LadderQ P0 ratio0 eta j)).filter Nat.Prime

theorem sliceA2LadderPrimes_prime
    (P0 ratio0 eta j p : ℕ) (hp : p ∈ sliceA2LadderPrimes P0 ratio0 eta j) :
    p.Prime := (Finset.mem_filter.mp hp).2

theorem sliceA2LadderPrimes_bounds
    (P0 ratio0 eta j p : ℕ) (hp : p ∈ sliceA2LadderPrimes P0 ratio0 eta j) :
    sliceA2LadderP P0 ratio0 eta j < p ∧
      p ≤ sliceA2LadderQ P0 ratio0 eta j :=
  Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1

theorem sliceA2LadderPrimes_disjoint
    (P0 ratio0 eta i j : ℕ) (hP0 : 2 ≤ P0) (hij : i ≠ j) :
    Disjoint (sliceA2LadderPrimes P0 ratio0 eta i)
      (sliceA2LadderPrimes P0 ratio0 eta j) := by
  have hforward : ∀ {a b : ℕ}, a < b →
      Disjoint (sliceA2LadderPrimes P0 ratio0 eta a)
        (sliceA2LadderPrimes P0 ratio0 eta b) := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro p hpa hpb
    have ha := sliceA2LadderPrimes_bounds P0 ratio0 eta a p hpa
    have hb := sliceA2LadderPrimes_bounds P0 ratio0 eta b p hpb
    have hsep := sliceA2LadderQ_lt_P_of_lt P0 ratio0 eta a b hP0 hab
    omega
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact hforward hij
  · exact (hforward hij).symm

theorem sliceA2LadderPrimes_disjoint_interval
    (P0 ratio0 eta j lo hi : ℕ)
    (hsep : sliceA2LadderQ P0 ratio0 eta j ≤ lo) :
    Disjoint (sliceA2LadderPrimes P0 ratio0 eta j)
      ((Finset.Ioc lo hi).filter Nat.Prime) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  have hp' := (sliceA2LadderPrimes_bounds P0 ratio0 eta j p hp).2
  have hq' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
  omega

/-! ## The scale-dependent cutoff -/

theorem sliceA2LadderP_sq_le_succ
    (P0 ratio0 eta j : ℕ) (hP0 : 2 ≤ P0) :
    sliceA2LadderP P0 ratio0 eta j ^ 2 ≤
      sliceA2LadderP P0 ratio0 eta (j + 1) := by
  have hP1 : 1 ≤ sliceA2LadderP P0 ratio0 eta j :=
    (sliceA2LadderP_two_le P0 ratio0 eta j hP0).trans' (by norm_num)
  have hfirst : sliceA2LadderP P0 ratio0 eta j ^ 2 ≤
      sliceA2LadderQ P0 ratio0 eta j := by
    rw [sliceA2LadderQ_eq]
    exact pow_le_pow_right' hP1
      (sliceA2LadderRatio_two_le ratio0 eta j)
  rw [sliceA2LadderP_succ]
  exact hfirst.trans (Nat.le_pow (by positivity : 0 < 100 * (j + 1) ^ 2))

theorem two_pow_two_pow_le_sliceA2LadderP
    (P0 ratio0 eta j : ℕ) (hP0 : 2 ≤ P0) :
    2 ^ (2 ^ j) ≤ sliceA2LadderP P0 ratio0 eta j := by
  induction j with
  | zero => simpa using hP0
  | succ j ih =>
      calc
        2 ^ (2 ^ (j + 1)) = (2 ^ (2 ^ j)) ^ 2 := by
          rw [pow_succ, pow_mul]
        _ ≤ sliceA2LadderP P0 ratio0 eta j ^ 2 := pow_le_pow_left' ih 2
        _ ≤ sliceA2LadderP P0 ratio0 eta (j + 1) :=
          sliceA2LadderP_sq_le_succ P0 ratio0 eta j hP0

theorem sliceA2Ladder_reaches_cutoff
    (P0 ratio0 eta A1 : ℕ) (hP0 : 2 ≤ P0) :
    ∃ j : ℕ, ordinaryLadderCutoff A1 ≤
      (sliceA2LadderP P0 ratio0 eta j : ℝ) := by
  let x := ordinaryLadderCutoff A1
  let j : ℕ := ⌈x⌉₊
  refine ⟨j, ?_⟩
  have hxj : x ≤ (j : ℝ) := Nat.le_ceil x
  have hjpow : j ≤ 2 ^ j := Nat.lt_two_pow_self.le
  have hpowpow : 2 ^ j ≤ 2 ^ (2 ^ j) :=
    pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) hjpow
  have hgrowth := two_pow_two_pow_le_sliceA2LadderP
    P0 ratio0 eta j hP0
  exact hxj.trans (by exact_mod_cast hjpow.trans hpowpow |>.trans hgrowth)

/-- One plus the least index reaching `(log A1)^40`. -/
noncomputable def sliceA2LadderJ
    (P0 ratio0 eta A1 : ℕ) (hP0 : 2 ≤ P0) : ℕ :=
  Nat.find (sliceA2Ladder_reaches_cutoff P0 ratio0 eta A1 hP0) + 1

theorem sliceA2LadderJ_pos
    (P0 ratio0 eta A1 : ℕ) (hP0 : 2 ≤ P0) :
    0 < sliceA2LadderJ P0 ratio0 eta A1 hP0 := by
  unfold sliceA2LadderJ
  omega

theorem sliceA2LadderJ_last_reaches
    (P0 ratio0 eta A1 : ℕ) (hP0 : 2 ≤ P0) :
    ordinaryLadderCutoff A1 ≤
      (sliceA2LadderP P0 ratio0 eta
        (sliceA2LadderJ P0 ratio0 eta A1 hP0 - 1) : ℝ) := by
  unfold sliceA2LadderJ
  simpa using Nat.find_spec
    (sliceA2Ladder_reaches_cutoff P0 ratio0 eta A1 hP0)

theorem sliceA2LadderJ_two_le_of_bottom_lt
    (P0 ratio0 eta A1 : ℕ) (hP0 : 2 ≤ P0)
    (hbottom : (P0 : ℝ) < ordinaryLadderCutoff A1) :
    2 ≤ sliceA2LadderJ P0 ratio0 eta A1 hP0 := by
  let hex := sliceA2Ladder_reaches_cutoff P0 ratio0 eta A1 hP0
  have hfind : 0 < Nat.find hex := by
    by_contra hzero
    have hz : Nat.find hex = 0 := Nat.eq_zero_of_not_pos hzero
    have hspec := Nat.find_spec hex
    rw [hz, sliceA2LadderP_zero] at hspec
    exact (not_le_of_gt hbottom) hspec
  unfold sliceA2LadderJ
  omega

theorem sliceA2LadderJ_prev_lt
    (P0 ratio0 eta A1 : ℕ) (hP0 : 2 ≤ P0)
    (hJ2 : 2 ≤ sliceA2LadderJ P0 ratio0 eta A1 hP0) :
    (sliceA2LadderP P0 ratio0 eta
        (sliceA2LadderJ P0 ratio0 eta A1 hP0 - 2) : ℝ) <
      ordinaryLadderCutoff A1 := by
  let hex := sliceA2Ladder_reaches_cutoff P0 ratio0 eta A1 hP0
  let n := Nat.find hex
  have hn : 0 < n := by
    dsimp [sliceA2LadderJ] at hJ2
    omega
  have hnot : ¬ ordinaryLadderCutoff A1 ≤
      (sliceA2LadderP P0 ratio0 eta (n - 1) : ℝ) :=
    Nat.find_min hex (by omega : n - 1 < n)
  have hshape : sliceA2LadderJ P0 ratio0 eta A1 hP0 - 2 = n - 1 := by
    dsimp [sliceA2LadderJ, n, hex]
    omega
  rw [hshape]
  exact lt_of_not_ge hnot

end Tao2015

end MoltResearch
