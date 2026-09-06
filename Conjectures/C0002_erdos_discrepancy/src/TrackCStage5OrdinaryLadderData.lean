import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5OrdinaryLadderNumerology

/-!
# Track R L3-2: ordinary ladder data

This file packages the purely finite data used by every ordinary level.  The
integer `eta` is the already-chosen ceiling of the analytic ratio constant;
putting `ratio j = max 2 (2^j eta)` keeps all subsequent arithmetic integral.
The prime intervals are separated by the exact jump
`P_(j+1) = Q_j^(100*(j+1)^2)`.
-/

namespace MoltResearch

namespace Tao2015

/-- Integral version of the geometric ratio schedule. -/
def ordinaryLadderRatio (eta j : ℕ) : ℕ := max 2 (2 ^ j * eta)

theorem ordinaryLadderRatio_two_le (eta j : ℕ) :
    2 ≤ ordinaryLadderRatio eta j := by
  unfold ordinaryLadderRatio
  exact le_max_left _ _

/-- Lower endpoints of the fixed ordinary ladder. -/
def ordinaryLadderP (P0 eta : ℕ) : ℕ → ℕ
  | 0 => P0
  | j + 1 =>
      (ordinaryLadderP P0 eta j ^ ordinaryLadderRatio eta j) ^
        (100 * (j + 1) ^ 2)

/-- Upper endpoints of the fixed ordinary ladder. -/
def ordinaryLadderQ (P0 eta j : ℕ) : ℕ :=
  ordinaryLadderP P0 eta j ^ ordinaryLadderRatio eta j

@[simp] theorem ordinaryLadderP_zero (P0 eta : ℕ) :
    ordinaryLadderP P0 eta 0 = P0 := rfl

@[simp] theorem ordinaryLadderQ_eq (P0 eta j : ℕ) :
    ordinaryLadderQ P0 eta j =
      ordinaryLadderP P0 eta j ^ ordinaryLadderRatio eta j := rfl

@[simp] theorem ordinaryLadderP_succ (P0 eta j : ℕ) :
    ordinaryLadderP P0 eta (j + 1) =
      ordinaryLadderQ P0 eta j ^ (100 * (j + 1) ^ 2) := rfl

theorem ordinaryLadderP_two_le (P0 eta j : ℕ) (hP0 : 2 ≤ P0) :
    2 ≤ ordinaryLadderP P0 eta j := by
  induction j with
  | zero => simpa using hP0
  | succ j ih =>
      rw [ordinaryLadderP_succ]
      have hQ : 2 ≤ ordinaryLadderQ P0 eta j := by
        rw [ordinaryLadderQ_eq]
        have hratio0 : 0 < ordinaryLadderRatio eta j :=
          lt_of_lt_of_le (by norm_num) (ordinaryLadderRatio_two_le eta j)
        exact le_trans ih
          (Nat.le_pow hratio0)
      have hexp0 : 0 < 100 * (j + 1) ^ 2 := by
        exact Nat.mul_pos (by norm_num) (pow_pos (Nat.succ_pos j) 2)
      exact le_trans hQ
        (Nat.le_pow hexp0)

theorem ordinaryLadderP_le_Q (P0 eta j : ℕ) :
    ordinaryLadderP P0 eta j ≤ ordinaryLadderQ P0 eta j := by
  rw [ordinaryLadderQ_eq]
  exact Nat.le_pow
    (lt_of_lt_of_le (by norm_num) (ordinaryLadderRatio_two_le eta j))

theorem ordinaryLadderQ_lt_P_succ (P0 eta j : ℕ) (hP0 : 2 ≤ P0) :
    ordinaryLadderQ P0 eta j < ordinaryLadderP P0 eta (j + 1) := by
  rw [ordinaryLadderP_succ]
  let Q := ordinaryLadderQ P0 eta j
  have hQ : 2 ≤ Q :=
    (ordinaryLadderP_two_le P0 eta j hP0).trans
      (ordinaryLadderP_le_Q P0 eta j)
  have htwo : Q < Q ^ 2 := by
    rw [pow_two]
    nlinarith
  have hjpow : 1 ≤ (j + 1) ^ 2 := by
    rw [pow_two]
    nlinarith
  have hexp : 2 ≤ 100 * (j + 1) ^ 2 := by omega
  exact htwo.trans_le (pow_le_pow_right' (by omega : 1 ≤ Q) hexp)

theorem ordinaryLadderP_mono (P0 eta : ℕ) (hP0 : 2 ≤ P0) :
    Monotone (ordinaryLadderP P0 eta) := by
  apply monotone_nat_of_le_succ
  intro j
  exact (ordinaryLadderP_le_Q P0 eta j).trans
    (ordinaryLadderQ_lt_P_succ P0 eta j hP0).le

theorem ordinaryLadderQ_lt_P_of_lt
    (P0 eta i k : ℕ) (hP0 : 2 ≤ P0) (hik : i < k) :
    ordinaryLadderQ P0 eta i < ordinaryLadderP P0 eta k := by
  have hs : i + 1 ≤ k := Nat.succ_le_iff.mpr hik
  exact (ordinaryLadderQ_lt_P_succ P0 eta i hP0).trans_le
    (ordinaryLadderP_mono P0 eta hP0 hs)

/-- Prime set at an ordinary ladder level. -/
def ordinaryLadderPrimes (P0 eta j : ℕ) : Finset ℕ :=
  (Finset.Ioc (ordinaryLadderP P0 eta j)
    (ordinaryLadderQ P0 eta j)).filter Nat.Prime

theorem ordinaryLadderPrimes_prime
    (P0 eta j p : ℕ) (hp : p ∈ ordinaryLadderPrimes P0 eta j) : p.Prime := by
  exact (Finset.mem_filter.mp hp).2

theorem ordinaryLadderPrimes_bounds
    (P0 eta j p : ℕ) (hp : p ∈ ordinaryLadderPrimes P0 eta j) :
    ordinaryLadderP P0 eta j < p ∧ p ≤ ordinaryLadderQ P0 eta j := by
  exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1)

theorem ordinaryLadderPrimes_mass_le_mertens
    (P0 eta j : ℕ) (hQ : 3 ≤ ordinaryLadderQ P0 eta j) :
    ∑ p ∈ ordinaryLadderPrimes P0 eta j, (1 : ℝ) / p ≤
      Real.log (Real.log ((ordinaryLadderQ P0 eta j : ℝ) + 1)) + 11 := by
  exact sum_one_div_prime_Ioc_le_mertens
    (ordinaryLadderP P0 eta j) (ordinaryLadderQ P0 eta j) hQ

theorem ordinaryLadderPrimes_card_le_Q (P0 eta j : ℕ) :
    (ordinaryLadderPrimes P0 eta j).card ≤ ordinaryLadderQ P0 eta j := by
  calc
    (ordinaryLadderPrimes P0 eta j).card ≤
      (Finset.Ioc (ordinaryLadderP P0 eta j)
          (ordinaryLadderQ P0 eta j)).card :=
      Finset.card_le_card (by
        intro p hp
        exact (Finset.mem_filter.mp hp).1)
    _ ≤ ordinaryLadderQ P0 eta j := by
      rw [Nat.card_Ioc]
      omega

/-- The collision mass has the elementary `#P/Plo²` bound. -/
theorem ordinaryLadderPrimes_sq_mass_le_card
    (P0 eta j : ℕ) (hP0 : 2 ≤ P0) :
    ∑ p ∈ ordinaryLadderPrimes P0 eta j,
        (1 : ℝ) / (p : ℝ) ^ 2 ≤
      ((ordinaryLadderPrimes P0 eta j).card : ℝ) /
        (ordinaryLadderP P0 eta j : ℝ) ^ 2 := by
  have hPj : (0 : ℝ) < ordinaryLadderP P0 eta j := by
    exact_mod_cast (show 0 < ordinaryLadderP P0 eta j by
      have := ordinaryLadderP_two_le P0 eta j hP0
      omega)
  calc
    ∑ p ∈ ordinaryLadderPrimes P0 eta j,
        (1 : ℝ) / (p : ℝ) ^ 2 ≤
      ∑ _p ∈ ordinaryLadderPrimes P0 eta j,
        (1 : ℝ) / (ordinaryLadderP P0 eta j : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro p hp
          apply one_div_le_one_div_of_le (by positivity)
          have hpP : (ordinaryLadderP P0 eta j : ℝ) ≤ p := by
            exact_mod_cast (ordinaryLadderPrimes_bounds P0 eta j p hp).1.le
          nlinarith
    _ = ((ordinaryLadderPrimes P0 eta j).card : ℝ) /
        (ordinaryLadderP P0 eta j : ℝ) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Separated endpoint intervals give disjoint prime levels. -/
theorem ordinaryLadderPrimes_disjoint
    (P0 eta i k : ℕ) (hP0 : 2 ≤ P0) (hik : i ≠ k) :
    Disjoint (ordinaryLadderPrimes P0 eta i)
      (ordinaryLadderPrimes P0 eta k) := by
  have hforward : ∀ {a b : ℕ}, a < b →
      Disjoint (ordinaryLadderPrimes P0 eta a)
        (ordinaryLadderPrimes P0 eta b) := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro p hpa hpb
    have ha := ordinaryLadderPrimes_bounds P0 eta a p hpa
    have hb := ordinaryLadderPrimes_bounds P0 eta b p hpb
    have hsep := ordinaryLadderQ_lt_P_of_lt P0 eta a b hP0 hab
    omega
  rcases lt_or_gt_of_ne hik with hlt | hgt
  · exact hforward hlt
  · exact (hforward hgt).symm

/-- An ordinary level is disjoint from any later interval beginning above
its upper endpoint. -/
theorem ordinaryLadderPrimes_disjoint_interval
    (P0 eta j Ulo Uhi : ℕ)
    (hsep : ordinaryLadderQ P0 eta j ≤ Ulo) :
    Disjoint (ordinaryLadderPrimes P0 eta j)
      ((Finset.Ioc Ulo Uhi).filter Nat.Prime) := by
  rw [Finset.disjoint_left]
  intro p hp hpu
  have hpq := (ordinaryLadderPrimes_bounds P0 eta j p hp).2
  have hpl := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpu).1).1
  omega

/-- Main, replacement and collision shares used at an ordinary level. -/
noncomputable def ordinaryKappaMain (j : ℕ) : ℝ := ordinaryLegShare j / 2

noncomputable def ordinaryKappaReplacement (j : ℕ) : ℝ := ordinaryLegShare j / 8

noncomputable def ordinaryKappaCollision (j : ℕ) : ℝ := ordinaryLegShare j / 8

theorem ordinaryKappa_share_fit (j : ℕ) :
    2 * ordinaryKappaMain j + 2 * ordinaryKappaReplacement j +
        2 * ordinaryKappaCollision j ≤ (1 : ℝ) / 2 ^ (j + 2) := by
  have hleg0 : 0 ≤ ordinaryLegShare j := by
    unfold ordinaryLegShare
    positivity
  have hwide := ordinaryLegShares_fit_shifted j
  unfold ordinaryKappaMain ordinaryKappaReplacement ordinaryKappaCollision
  nlinarith

/-- Cell resolution large enough to pay half of the wide replacement share.
The coefficient is `48 * 64 * 9 = 27648`. -/
noncomputable def ordinaryLevelN (E kappa c3 eps : ℝ) : ℕ :=
  max 2 ⌈27648 * Real.exp Real.pi * E / (kappa * c3 * eps ^ 2)⌉₊

theorem ordinaryLevelN_two_le (E kappa c3 eps : ℝ) :
    2 ≤ ordinaryLevelN E kappa c3 eps := by
  unfold ordinaryLevelN
  exact le_max_left _ _

theorem ordinaryLevelN_replacement_mass_fit
    (E kappa c3 eps : ℝ) (hE : 0 ≤ E) (hkappa : 0 < kappa)
    (hc3 : 0 < c3) (heps : 0 < eps) :
    64 * 9 * Real.exp Real.pi *
        (E / (ordinaryLevelN E kappa c3 eps : ℝ)) ≤
      kappa * c3 * eps ^ 2 / 48 := by
  let b : ℝ := kappa * c3 * eps ^ 2
  let C : ℝ := 27648 * Real.exp Real.pi
  have hb : 0 < b := by dsimp [b]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hratio0 : 0 ≤ C * E / b := by positivity
  have hceil : C * E / b ≤
      (⌈C * E / b⌉₊ : ℕ) := Nat.le_ceil _
  have hNlower : C * E / b ≤
      (ordinaryLevelN E kappa c3 eps : ℝ) := by
    refine hceil.trans ?_
    exact_mod_cast (le_max_right 2 ⌈C * E / b⌉₊)
  have hcross : C * E ≤
      b * (ordinaryLevelN E kappa c3 eps : ℝ) := by
    calc
      C * E = b * (C * E / b) := by field_simp
      _ ≤ b * (ordinaryLevelN E kappa c3 eps : ℝ) :=
        mul_le_mul_of_nonneg_left hNlower hb.le
  have hN0 : (0 : ℝ) < ordinaryLevelN E kappa c3 eps := by
    exact_mod_cast (show 0 < ordinaryLevelN E kappa c3 eps by
      have := ordinaryLevelN_two_le E kappa c3 eps
      omega)
  have hdiv : C * E / (ordinaryLevelN E kappa c3 eps : ℝ) ≤ b :=
    (div_le_iff₀ hN0).2 hcross
  dsimp [C, b] at hdiv
  calc
    64 * 9 * Real.exp Real.pi *
          (E / (ordinaryLevelN E kappa c3 eps : ℝ)) =
        (27648 * Real.exp Real.pi * E /
          (ordinaryLevelN E kappa c3 eps : ℝ)) / 48 := by ring
    _ ≤ (kappa * c3 * eps ^ 2) / 48 :=
      div_le_div_of_nonneg_right hdiv (by norm_num)

/-- Cell-index endpoints for an interval at resolution `2N`. -/
noncomputable def ordinaryLevelV0 (P N : ℕ) : ℕ :=
  eadicCoverIndexLower (2 * N) P

noncomputable def ordinaryLevelV1 (Q N : ℕ) : ℕ :=
  eadicCoverIndexUpper (2 * N) Q

/-- The number of scheduled cells is at most its logarithmic width plus two. -/
theorem ordinaryLevel_cell_card_le
    (P Q N : ℕ) (hP : 2 ≤ P) (hPQ : P ≤ Q) (hN : 0 < N) :
    ((Finset.Ico (ordinaryLevelV0 P N)
        (ordinaryLevelV1 Q N + 1)).card : ℝ) ≤
      2 * (N : ℝ) * (Real.log Q - Real.log P) + 2 := by
  have hP0 : (0 : ℝ) < P := by positivity
  have hQ0 : (0 : ℝ) < Q := hP0.trans_le (by exact_mod_cast hPQ)
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast hP)
  have hQ1 : (1 : ℝ) ≤ Q := by
    exact_mod_cast (show 1 ≤ Q from (by omega))
  have hlogQ0 : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg hQ1
  have hlogPQ : Real.log (P : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log hP0 (by exact_mod_cast hPQ)
  let a : ℝ := ((2 * N : ℕ) : ℝ) * Real.log P
  let b : ℝ := ((2 * N : ℕ) : ℝ) * Real.log Q
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hceil1 : 1 ≤ ⌈a⌉₊ := Nat.one_le_ceil_iff.mpr ha
  have hceil : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
  have hfloor : ((⌊b⌋₊ : ℕ) : ℝ) ≤ b := Nat.floor_le hb
  by_cases hidx : ⌈a⌉₊ - 1 ≤ ⌊b⌋₊ + 1
  · rw [ordinaryLevelV0, ordinaryLevelV1, eadicCoverIndexLower,
      eadicCoverIndexUpper, Nat.card_Ico, Nat.cast_sub hidx,
      Nat.cast_add, Nat.cast_one, Nat.cast_sub hceil1, Nat.cast_one]
    dsimp [a, b] at hceil hfloor ⊢
    push_cast at hceil hfloor ⊢
    linarith
  · have hzero : (Finset.Ico (ordinaryLevelV0 P N)
        (ordinaryLevelV1 Q N + 1)).card = 0 := by
      rw [Nat.card_Ico]
      apply Nat.sub_eq_zero_of_le
      have hrev : ⌊b⌋₊ + 1 ≤ ⌈a⌉₊ - 1 :=
        (Nat.lt_of_not_ge hidx).le
      dsimp [a, b] at hrev
      simpa only [ordinaryLevelV0, ordinaryLevelV1, eadicCoverIndexLower,
        eadicCoverIndexUpper] using hrev
    rw [hzero]
    norm_num only [Nat.cast_zero]
    have hnonneg : 0 ≤ 2 * (N : ℝ) * (Real.log Q - Real.log P) := by
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hlogPQ)
    linarith

/-- The empty-cell-safe representative used at every ordinary level. -/
noncomputable def ordinaryLevelRepresentative
    (P0 eta j N v : ℕ) : ℕ :=
  scaleCellRepresentative (ordinaryLadderPrimes P0 eta j) N v

/-- All cell and representative hypotheses of the shifted wide capstone are
automatic for one ordinary prime interval. -/
theorem ordinaryLevel_cell_data
    (P0 eta j N : ℕ) (hP0 : 2 ≤ P0) (hN : 0 < N) :
    ((Finset.Ico
        (ordinaryLevelV0 (ordinaryLadderP P0 eta j) N)
        (ordinaryLevelV1 (ordinaryLadderQ P0 eta j) N + 1)).biUnion
      (eadicCell (ordinaryLadderPrimes P0 eta j) (2 * N)) =
        ordinaryLadderPrimes P0 eta j) ∧
    (∀ v ∈ Finset.Ico
        (ordinaryLevelV0 (ordinaryLadderP P0 eta j) N)
        (ordinaryLevelV1 (ordinaryLadderQ P0 eta j) N + 1),
      (ordinaryLevelRepresentative P0 eta j N v : ℝ) ≤
        Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ)))) ∧
    (∀ v, 1 ≤ ordinaryLevelRepresentative P0 eta j N v) ∧
    (∀ v ∈ Finset.Ico
        (ordinaryLevelV0 (ordinaryLadderP P0 eta j) N)
        (ordinaryLevelV1 (ordinaryLadderQ P0 eta j) N + 1),
      ∀ p ∈ eadicCell (ordinaryLadderPrimes P0 eta j) (2 * N) v,
        ordinaryLevelRepresentative P0 eta j N v ≤ p) ∧
    (∀ v ∈ Finset.Ico
        (ordinaryLevelV0 (ordinaryLadderP P0 eta j) N)
        (ordinaryLevelV1 (ordinaryLadderQ P0 eta j) N + 1),
      ∀ p ∈ eadicCell (ordinaryLadderPrimes P0 eta j) (2 * N) v,
        N * p ≤ (N + 1) * ordinaryLevelRepresentative P0 eta j N v) := by
  have hPj : 1 ≤ ordinaryLadderP P0 eta j :=
    (ordinaryLadderP_two_le P0 eta j hP0).trans' (by norm_num)
  have hprime : ∀ p ∈ ordinaryLadderPrimes P0 eta j, p.Prime :=
    fun p hp => ordinaryLadderPrimes_prime P0 eta j p hp
  have hone : ∀ p ∈ ordinaryLadderPrimes P0 eta j, 1 ≤ p :=
    fun p hp => (hprime p hp).one_le
  constructor
  · simpa [ordinaryLevelV0, ordinaryLevelV1] using
      eadicCell_biUnion_Ico_eq (ordinaryLadderPrimes P0 eta j) (2 * N)
        (ordinaryLadderP P0 eta j) (ordinaryLadderQ P0 eta j)
        (by omega : 0 < 2 * N) hPj
        (fun p hp => (ordinaryLadderPrimes_bounds P0 eta j p hp).1)
        (fun p hp => (ordinaryLadderPrimes_bounds P0 eta j p hp).2)
  constructor
  · intro v hv
    exact qup_of_ceil_or_one (ordinaryLadderPrimes P0 eta j) N v hN hone
  constructor
  · intro v
    exact one_le_scaleCellRepresentative (ordinaryLadderPrimes P0 eta j) N v
  constructor
  · intro v hv p hp
    exact scaleCellRepresentative_le_mem hN hp (hprime p (mem_eadicCell.mp hp).1).one_le
  · intro v hv p hp
    exact scaleCellRepresentative_ratio_le hN hp
      (hprime p (mem_eadicCell.mp hp).1).one_le

/-- Natural quotient data used by `innerBand_later_level_main_cells`. -/
noncomputable def ordinaryQuotientA (A q : ℕ) : ℕ := A / q

noncomputable def ordinaryQuotientDelta (A Delta q : ℕ) : ℕ :=
  (A + Delta) / q - A / q

/-- The convenient guard `Delta + q ≤ A` makes the quotient increment no
larger than its starting point. -/
theorem ordinaryQuotientDelta_le
    (A Delta q : ℕ) (hq : 0 < q) (hguard : Delta + q ≤ A) :
    ordinaryQuotientDelta A Delta q ≤ ordinaryQuotientA A q := by
  have hr := Nat.mod_lt A hq
  have hdecomp := Nat.div_add_mod A q
  have hDelta : Delta ≤ q * (A / q) := by omega
  have hmono := Nat.div_le_div_right (c := q) (Nat.add_le_add_left hDelta A)
  have hsplit : (A + q * (A / q)) / q = A / q + A / q := by
    rw [Nat.add_mul_div_left A (A / q) hq]
  rw [hsplit] at hmono
  unfold ordinaryQuotientDelta ordinaryQuotientA
  exact Nat.sub_le_iff_le_add.mpr hmono

/-- The quotient interval is literally recovered from its start and
increment, while the same guard supplies positivity and the half-width
condition required by the later-level mean-value theorem. -/
theorem ordinaryQuotient_data
    (A Delta q : ℕ) (hq : 0 < q) (hguard : Delta + q ≤ A) :
    1 ≤ ordinaryQuotientA A q ∧
      ordinaryQuotientDelta A Delta q ≤ ordinaryQuotientA A q ∧
      Finset.Ioc (A / q) ((A + Delta) / q) ⊆
        Finset.Ioc (ordinaryQuotientA A q)
          (ordinaryQuotientA A q + ordinaryQuotientDelta A Delta q) := by
  have hqA : q ≤ A := by omega
  have hstart : 1 ≤ ordinaryQuotientA A q := by
    unfold ordinaryQuotientA
    exact (Nat.one_le_div_iff hq).mpr hqA
  have hmono : A / q ≤ (A + Delta) / q := Nat.div_le_div_right (by omega)
  have hend : ordinaryQuotientA A q + ordinaryQuotientDelta A Delta q =
      (A + Delta) / q := by
    unfold ordinaryQuotientA ordinaryQuotientDelta
    omega
  refine ⟨hstart, ordinaryQuotientDelta_le A Delta q hq hguard, ?_⟩
  rw [hend]
  simp [ordinaryQuotientA]

/-- The borrowed moment reaches its prescribed positive real scale. -/
theorem le_pow_ordinaryBorrowMoment
    (P : ℕ) (hP : 2 ≤ P) (x : ℝ) (hx : 0 < x) :
    x ≤ ((P ^ ordinaryBorrowMoment P x : ℕ) : ℝ) := by
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hratio : Real.log x / Real.log P ≤
      (ordinaryBorrowMoment P x : ℝ) := by
    calc
      Real.log x / Real.log P ≤
          (⌈Real.log x / Real.log P⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (ordinaryBorrowMoment P x : ℝ) := by
        exact_mod_cast (show ⌈Real.log x / Real.log P⌉₊ ≤
          ordinaryBorrowMoment P x by unfold ordinaryBorrowMoment; omega)
  have hlog : Real.log x ≤
      (ordinaryBorrowMoment P x : ℝ) * Real.log P :=
    (div_le_iff₀ hlogP).mp hratio
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hx] at hexp
  rw [show (ordinaryBorrowMoment P x : ℝ) * Real.log P =
      (ordinaryBorrowMoment P x : ℕ) * Real.log P by norm_cast,
    Real.exp_nat_mul, Real.exp_log (by exact_mod_cast (show 0 < P by omega))] at hexp
  norm_cast at hexp ⊢

/-- A scale `t ≥ q` controls the quotient rounding loss. -/
theorem time_div_quotient_le_two_mul_scale
    (A q t : ℕ) (T : ℝ) (hq : 1 ≤ q) (hqt : q ≤ t)
    (h2qA : 2 * q ≤ A) (hT : 0 ≤ T) :
    T / ((A / q : ℕ) : ℝ) ≤ 2 * T * (t : ℝ) / (A : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hmod : ((A % q : ℕ) : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.mod_lt A (by omega : 0 < q)
  have hdm : (q : ℝ) * ((A / q : ℕ) : ℝ) + ((A % q : ℕ) : ℝ) = A := by
    exact_mod_cast Nat.div_add_mod A q
  have hfloor : (A : ℝ) / (2 * (q : ℝ)) ≤ ((A / q : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have h2qR : 2 * (q : ℝ) ≤ A := by exact_mod_cast h2qA
    nlinarith
  calc
    T / ((A / q : ℕ) : ℝ) ≤ T / ((A : ℝ) / (2 * (q : ℝ))) := by gcongr
    _ = 2 * T * (q : ℝ) / (A : ℝ) := by field_simp
    _ ≤ 2 * T * (t : ℝ) / (A : ℝ) := by gcongr

/-- The moment chosen at scale `t*(2T/A)` makes the exact time quotient in
the later-level cell summand at most one. -/
theorem ordinaryBorrowMoment_time_term_le_one
    (P A q t : ℕ) (T : ℝ) (hP : 2 ≤ P) (hq : 1 ≤ q)
    (hqt : q ≤ t) (h2qA : 2 * q ≤ A) (hT : 0 < T) :
    T / (((P ^ ordinaryBorrowMoment P ((t : ℝ) * (2 * T / A)) : ℕ) *
        (A / q) : ℕ) : ℝ) ≤ 1 := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hAq : 1 ≤ A / q := (Nat.one_le_div_iff (by omega : 0 < q)).mpr (by omega)
  have hquot := time_div_quotient_le_two_mul_scale A q t T hq hqt h2qA hT.le
  have hxpos : 0 < (t : ℝ) * (2 * T / (A : ℝ)) := by
    have ht : 0 < t := lt_of_lt_of_le (by omega : 0 < q) hqt
    positivity
  have hpow := le_pow_ordinaryBorrowMoment P hP
    ((t : ℝ) * (2 * T / (A : ℝ))) hxpos
  have hshape : 2 * T * (t : ℝ) / (A : ℝ) =
      (t : ℝ) * (2 * T / (A : ℝ)) := by ring
  rw [hshape] at hquot
  have hquotPow := hquot.trans hpow
  have hAq0 : (0 : ℝ) < (A / q : ℕ) := by exact_mod_cast hAq
  have hcross : T ≤
      ((P ^ ordinaryBorrowMoment P ((t : ℝ) * (2 * T / A)) : ℕ) : ℝ) *
        (A / q : ℕ) := by
    exact (div_le_iff₀ hAq0).mp hquotPow
  have hden : (0 : ℝ) <
      ((P ^ ordinaryBorrowMoment P ((t : ℝ) * (2 * T / A)) : ℕ) *
        (A / q) : ℕ) := by positivity
  apply (div_le_iff₀ hden).2
  push_cast
  simpa only [one_mul, Nat.cast_mul, Nat.cast_pow] using hcross

/-- A convenient sufficient condition for the wide replacement fit.  The
constant `64*9*exp(pi)` is the exact factor after `T/A ≤ 1`. -/
theorem replacementEnergyBoundWide_fit_of_mass_card
    (A N : ℕ) (P : Finset ℕ) (T E kappa c3 eps : ℝ)
    (hA : 2 ≤ A) (hN : 0 < N) (hTA : T ≤ A)
    (hmass : ∑ p ∈ P, (1 : ℝ) / p ≤ E)
    (hfit : 64 * 9 * Real.exp Real.pi *
        (E / (N : ℝ) + (P.card : ℝ) / A) ≤
      kappa * c3 * eps ^ 2 / 24)
    (hc3 : 0 ≤ c3) (hkappa : 0 ≤ kappa)
    (Delta : ℕ) (hhalf : A / 2 ≤ Delta) :
    2 * replacementEnergyBoundWide A P N T ≤
      kappa * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hratio : T / (A : ℝ) ≤ 1 := (div_le_one hA0).2 (by exact_mod_cast hTA)
  have hinner0 : 0 ≤
      (∑ p ∈ P, (1 : ℝ) / p) / (N : ℝ) + (P.card : ℝ) / A := by positivity
  have hEinner :
      (∑ p ∈ P, (1 : ℝ) / p) / (N : ℝ) + (P.card : ℝ) / A ≤
        E / (N : ℝ) + (P.card : ℝ) / A := by gcongr
  have hraw : 2 * replacementEnergyBoundWide A P N T ≤
      64 * 9 * Real.exp Real.pi * (E / (N : ℝ) + (P.card : ℝ) / A) := by
    unfold replacementEnergyBoundWide
    calc
      2 * (Real.exp Real.pi * (T / (A : ℝ) + 8) *
          (32 * ((∑ p ∈ P, (1 : ℝ) / p) / (N : ℝ) +
            (P.card : ℝ) / (A : ℝ)))) =
        64 * Real.exp Real.pi * (T / (A : ℝ) + 8) *
          ((∑ p ∈ P, (1 : ℝ) / p) / (N : ℝ) +
            (P.card : ℝ) / A) := by ring
      _ ≤ 64 * Real.exp Real.pi * 9 *
          ((∑ p ∈ P, (1 : ℝ) / p) / (N : ℝ) +
            (P.card : ℝ) / A) := by gcongr; linarith
      _ = 64 * 9 * Real.exp Real.pi *
          ((∑ p ∈ P, (1 : ℝ) / p) / (N : ℝ) +
            (P.card : ℝ) / A) := by ring
      _ ≤ _ := by gcongr
  have hbudget := bandBudget_one_twenty_four_le_of_nat_half_le
    c3 eps hc3 A Delta hA hhalf
  calc
    2 * replacementEnergyBoundWide A P N T ≤ _ := hraw
    _ ≤ kappa * c3 * eps ^ 2 / 24 := hfit
    _ = kappa * (c3 * eps ^ 2 / 24) := by ring
    _ ≤ kappa * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) :=
      mul_le_mul_of_nonneg_left hbudget hkappa

/-- A convenient sufficient condition for the wide collision fit.  The
constant `40*exp(pi)` is the exact factor after `T/A ≤ 1`. -/
theorem collisionEnergyBoundWide_fit_of_mass_card
    (A : ℕ) (P : Finset ℕ) (T E2 kappa c3 eps : ℝ)
    (hA : 2 ≤ A) (hTA : T ≤ A)
    (hmass2 : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 ≤ E2)
    (hfit : 40 * Real.exp Real.pi *
        (2 * E2 + (P.card : ℝ) / A) ≤ kappa * c3 * eps ^ 2 / 24)
    (hc3 : 0 ≤ c3) (hkappa : 0 ≤ kappa)
    (Delta : ℕ) (hhalf : A / 2 ≤ Delta) :
    8 * collisionEnergyBoundWide A P T ≤
      kappa * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hratio : T / (A : ℝ) ≤ 1 := (div_le_one hA0).2 (by exact_mod_cast hTA)
  have hinner0 : 0 ≤
      2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) + (P.card : ℝ) / A := by positivity
  have hEinner :
      2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) + (P.card : ℝ) / A ≤
        2 * E2 + (P.card : ℝ) / A := by gcongr
  have hraw : 8 * collisionEnergyBoundWide A P T ≤
      40 * Real.exp Real.pi * (2 * E2 + (P.card : ℝ) / A) := by
    unfold collisionEnergyBoundWide
    calc
      8 * (Real.exp Real.pi * (T / (A : ℝ) + 4) *
          (2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
            (P.card : ℝ) / (A : ℝ))) =
        8 * Real.exp Real.pi * (T / (A : ℝ) + 4) *
          (2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
            (P.card : ℝ) / A) := by ring
      _ ≤ 8 * Real.exp Real.pi * 5 *
          (2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
            (P.card : ℝ) / A) := by gcongr; linarith
      _ = 40 * Real.exp Real.pi *
          (2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
            (P.card : ℝ) / A) := by ring
      _ ≤ _ := by gcongr
  have hbudget := bandBudget_one_twenty_four_le_of_nat_half_le
    c3 eps hc3 A Delta hA hhalf
  calc
    8 * collisionEnergyBoundWide A P T ≤ _ := hraw
    _ ≤ kappa * c3 * eps ^ 2 / 24 := hfit
    _ = kappa * (c3 * eps ^ 2 / 24) := by ring
    _ ≤ kappa * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) :=
      mul_le_mul_of_nonneg_left hbudget hkappa

end Tao2015

end MoltResearch
