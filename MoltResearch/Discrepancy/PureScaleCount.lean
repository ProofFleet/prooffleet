import MoltResearch.Discrepancy.AlmostOrthogonality
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Totient

/-!
# Discrepancy: pure-scale diagonal count for cutoff windows

Endgame step for the Tao 2015 §4 analysis (arXiv:1509.05363,
`Problems/tao2015_derivation_c.md`, issue #2871): the per-scale lower bound on the
diagonal terms `d = qⁱ` surviving the almost-orthogonality expansion.

* `totient_mul_le_sum_normSq_dirichletChar_Ico`: the windowed character second moment
  grows linearly **from any offset**: `φ(q)·⌊L/q⌋ ≤ ∑_{b ∈ [c, c+L)} ‖χ(b)‖²`
  (the `Icc 1 N` version is `totient_mul_le_sum_normSq_dirichletChar`).
* `sum_Ioc_charCutoff_eq_char`: a length-`d` window `(H', H'+d]` contains exactly one
  multiple of `d`, so the cutoff window sum evaluates to the single character value
  `χ(⌊(a+H')/d⌋ + 1)`.
* `sum_normSq_window_pure_scale_ge`: combining the two over a full period `a ∈ [0, q^k)`,

  `φ(q)·⌊(q^{k−i}−1)/q⌋·qⁱ ≤ ∑_a ‖∑_{m ∈ (H', H'+qⁱ]} charCutoff χ qⁱ (a+m)‖²`

  — the "`b ↦ |χ(b)|²` is periodic with mean `≫ 1`" step of the paper's endgame, in
  explicit form: each of the `q^{k−i}−1` complete `qⁱ`-blocks of the shifted period
  contributes its own character value `qⁱ` times.
-/

namespace MoltResearch

open Finset

variable {q : ℕ} {χ : DirichletCharacter ℂ q}

/-- Offset version of the coprime indicator block count: any window `[c, c + q·T)`
carries indicator mass exactly `φ(q)·T`. -/
private lemma sum_coprime_indicator_Ico_eq (q c T : ℕ) :
    ∑ b ∈ Finset.Ico c (c + q * T), (if q.Coprime b then (1 : ℝ) else 0)
      = (q.totient : ℝ) * (T : ℝ) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h1 : c ≤ c + q * T := Nat.le_add_right _ _
    have h2 : c + q * T ≤ c + q * (T + 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left q (Nat.le_succ T)) c
    rw [← Finset.sum_Ico_consecutive _ h1 h2, ih]
    have hblock : ∑ b ∈ Finset.Ico (c + q * T) (c + q * (T + 1)),
        (if q.Coprime b then (1 : ℝ) else 0) = (q.totient : ℝ) := by
      have harg : c + q * (T + 1) = (c + q * T) + q := by ring
      rw [harg, Finset.sum_boole]
      exact_mod_cast Nat.filter_coprime_Ico_eq_totient q (c + q * T)
    rw [hblock]
    push_cast
    ring

/-- **Linear growth of the windowed character second moment, from any offset**
(Tao 2015 §4 endgame): `φ(q)·⌊L/q⌋ ≤ ∑_{b ∈ [c, c+L)} ‖χ(b)‖²`. -/
theorem totient_mul_le_sum_normSq_dirichletChar_Ico (χ : DirichletCharacter ℂ q)
    (c L : ℕ) :
    (q.totient : ℝ) * ((L / q : ℕ) : ℝ)
      ≤ ∑ b ∈ Finset.Ico c (c + L), ‖χ ((b : ℕ) : ZMod q)‖ ^ 2 := by
  have hpoint : ∀ b : ℕ, (if q.Coprime b then (1 : ℝ) else 0)
      ≤ ‖χ ((b : ℕ) : ZMod q)‖ ^ 2 := by
    intro b
    by_cases h : q.Coprime b
    · rw [if_pos h]
      have hu : IsUnit ((b : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime b q).mpr h.symm
      rw [← hu.unit_spec, DirichletCharacter.unit_norm_eq_one χ hu.unit, one_pow]
    · rw [if_neg h]
      positivity
  have hsubset : Finset.Ico c (c + q * (L / q)) ⊆ Finset.Ico c (c + L) := by
    intro b hb
    rw [Finset.mem_Ico] at hb ⊢
    have hdiv : L / q * q ≤ L := Nat.div_mul_le_self L q
    have hcomm : q * (L / q) = L / q * q := Nat.mul_comm _ _
    omega
  calc (q.totient : ℝ) * ((L / q : ℕ) : ℝ)
      = ∑ b ∈ Finset.Ico c (c + q * (L / q)), (if q.Coprime b then (1 : ℝ) else 0) :=
        (sum_coprime_indicator_Ico_eq q c (L / q)).symm
    _ ≤ ∑ b ∈ Finset.Ico c (c + L), (if q.Coprime b then (1 : ℝ) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun b _ _ => by split <;> norm_num)
    _ ≤ ∑ b ∈ Finset.Ico c (c + L), ‖χ ((b : ℕ) : ZMod q)‖ ^ 2 :=
        Finset.sum_le_sum fun b _ => hpoint b

/-- **The unique multiple in a length-`d` window** (Tao 2015 §4 endgame): the cutoff
window sum over `m ∈ (H', H'+d]` has exactly one surviving term, at the unique multiple
of `d` in `(a+H', a+H'+d]`, whose cofactor is `⌊(a+H')/d⌋ + 1`. -/
theorem sum_Ioc_charCutoff_eq_char {d : ℕ} (hd : d ≠ 0) (a H' : ℕ) :
    ∑ m ∈ Finset.Ioc H' (H' + d), charCutoff χ d (a + m)
      = χ ((((a + H') / d + 1 : ℕ)) : ZMod q) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd
  -- generalize the division data so all arithmetic below is linear in the atoms
  have key : ∀ s r : ℕ, d * s + r = a + H' → r < d →
      ∑ m ∈ Finset.Ioc H' (H' + d), charCutoff χ d (a + m)
        = χ (((s + 1 : ℕ)) : ZMod q) := by
    intro s r hsr hrd
    have hmem : d * s + d - a ∈ Finset.Ioc H' (H' + d) := by
      rw [Finset.mem_Ioc]
      omega
    have huniq : ∀ m ∈ Finset.Ioc H' (H' + d), m ≠ d * s + d - a →
        charCutoff χ d (a + m) = 0 := by
      intro m hm hne
      rw [Finset.mem_Ioc] at hm
      refine charCutoff_of_not_dvd fun hdvd => hne ?_
      obtain ⟨j, hj⟩ := hdvd
      have hjlow : s < j := by
        refine Nat.lt_of_mul_lt_mul_left (a := d) ?_
        omega
      have hjhigh : j < s + 2 := by
        refine Nat.lt_of_mul_lt_mul_left (a := d) ?_
        have hexp : d * (s + 2) = d * s + d + d := by ring
        omega
      have hjeq : j = s + 1 := by omega
      rw [hjeq, Nat.mul_succ] at hj
      omega
    rw [Finset.sum_eq_single_of_mem _ hmem huniq]
    have ham₀ : a + (d * s + d - a) = d * (s + 1) := by
      rw [Nat.mul_succ]
      omega
    have hdvd : d ∣ a + (d * s + d - a) := ⟨s + 1, ham₀⟩
    rw [charCutoff_of_dvd hdvd, ham₀, Nat.mul_div_cancel_left _ hd0]
  exact key ((a + H') / d) ((a + H') % d) (Nat.div_add_mod _ _) (Nat.mod_lt _ hd0)

/-- On each complete block `[d·b, d·b + d)` the cofactor `⌊j/d⌋` is constant, so the
block sums collapse with weight `d`. -/
private lemma sum_Ico_blocks_char_eq {d : ℕ} (hd : 0 < d) (c₀ L : ℕ) :
    ∑ j ∈ Finset.Ico (d * c₀) (d * c₀ + d * L), ‖χ (((j / d + 1 : ℕ)) : ZMod q)‖ ^ 2
      = (d : ℝ) * ∑ b ∈ Finset.Ico c₀ (c₀ + L), ‖χ (((b + 1 : ℕ)) : ZMod q)‖ ^ 2 := by
  induction L with
  | zero => simp
  | succ L ih =>
    have h1 : d * c₀ ≤ d * c₀ + d * L := Nat.le_add_right _ _
    have h2 : d * c₀ + d * L ≤ d * c₀ + d * (L + 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left d (Nat.le_succ L)) _
    rw [← Finset.sum_Ico_consecutive _ h1 h2, ih]
    have hblock : ∑ j ∈ Finset.Ico (d * c₀ + d * L) (d * c₀ + d * (L + 1)),
        ‖χ (((j / d + 1 : ℕ)) : ZMod q)‖ ^ 2
          = (d : ℝ) * ‖χ (((c₀ + L + 1 : ℕ)) : ZMod q)‖ ^ 2 := by
      have hconst : ∀ j ∈ Finset.Ico (d * c₀ + d * L) (d * c₀ + d * (L + 1)),
          ‖χ (((j / d + 1 : ℕ)) : ZMod q)‖ ^ 2
            = ‖χ (((c₀ + L + 1 : ℕ)) : ZMod q)‖ ^ 2 := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        have hjd : j / d = c₀ + L := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · have hexp : (c₀ + L) * d = d * c₀ + d * L := by ring
            omega
          · have hexp : (c₀ + L + 1) * d = d * c₀ + d * (L + 1) := by ring
            omega
        rw [hjd]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico]
      have hcard : d * c₀ + d * (L + 1) - (d * c₀ + d * L) = d := by
        have hexp : d * (L + 1) = d * L + d := by ring
        omega
      rw [hcard, nsmul_eq_mul]
    rw [hblock, show c₀ + (L + 1) = (c₀ + L) + 1 by omega,
      Finset.sum_Ico_succ_top (Nat.le_add_right c₀ L)]
    push_cast
    ring

/-- Shift the character argument by one to align with the offset second-moment count. -/
private lemma sum_Ico_shift_one_char (c₀ L : ℕ) :
    ∑ b ∈ Finset.Ico c₀ (c₀ + L), ‖χ (((b + 1 : ℕ)) : ZMod q)‖ ^ 2
      = ∑ b ∈ Finset.Ico (c₀ + 1) (c₀ + 1 + L), ‖χ ((b : ℕ) : ZMod q)‖ ^ 2 := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  have harg : c₀ + i + 1 = c₀ + 1 + i := by omega
  rw [harg]

/-- **Pure-scale diagonal lower bound** (Tao 2015 §4 endgame): over a full period
`a ∈ [0, q^k)`, the `d = qⁱ` cutoff windows of length `qⁱ` each evaluate to a single
character value, and the values sweep `q^{k−i}−1` complete blocks, giving

`φ(q)·⌊(q^{k−i}−1)/q⌋·qⁱ ≤ ∑_a ‖∑_{m ∈ (H', H'+qⁱ]} charCutoff χ qⁱ (a+m)‖²`. -/
theorem sum_normSq_window_pure_scale_ge (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    {i k : ℕ} (hik : i ≤ k) (H' : ℕ) :
    (q.totient : ℝ) * (((q ^ (k - i) - 1) / q : ℕ) : ℝ) * ((q ^ i : ℕ) : ℝ)
      ≤ ∑ a ∈ Finset.range (q ^ k),
          ‖∑ m ∈ Finset.Ioc H' (H' + q ^ i), charCutoff χ (q ^ i) (a + m)‖ ^ 2 := by
  have hq0 : 0 < q := hq
  -- opaque block data: `d = qⁱ`, `M = q^{k−i}`, `N = q^k` with `d·M = N`, so that all
  -- subsequent arithmetic is linear in the atoms
  obtain ⟨d, M, N, hd, hM, hN, hd0, hM1, hdM⟩ :
      ∃ d M N : ℕ, q ^ i = d ∧ q ^ (k - i) = M ∧ q ^ k = N ∧ 0 < d ∧ 1 ≤ M ∧ d * M = N :=
    ⟨q ^ i, q ^ (k - i), q ^ k, rfl, rfl, rfl, pow_pos hq0 i, Nat.one_le_pow _ _ hq0,
      by rw [← pow_add, Nat.add_sub_cancel' hik]⟩
  rw [hd, hM, hN]
  -- evaluate each window to a single character value
  have heval : ∀ a ∈ Finset.range N,
      ‖∑ m ∈ Finset.Ioc H' (H' + d), charCutoff χ d (a + m)‖ ^ 2
        = ‖χ ((((a + H') / d + 1 : ℕ)) : ZMod q)‖ ^ 2 := fun a _ => by
    rw [sum_Ioc_charCutoff_eq_char hd0.ne' a H']
  rw [Finset.sum_congr rfl heval]
  -- reindex `a ↦ H' + a`
  have hreindex : ∑ a ∈ Finset.range N,
      ‖χ ((((a + H') / d + 1 : ℕ)) : ZMod q)‖ ^ 2
        = ∑ j ∈ Finset.Ico H' (H' + N), ‖χ (((j / d + 1 : ℕ)) : ZMod q)‖ ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    exact Finset.sum_congr rfl fun a _ => by rw [Nat.add_comm H' a]
  rw [hreindex]
  -- restrict to the `M − 1` complete blocks starting at the first multiple of `d`
  -- past `H'`
  obtain ⟨c₀, hc₀low, hc₀high⟩ : ∃ c₀ : ℕ, H' < d * c₀ ∧ d * c₀ ≤ H' + d := by
    refine ⟨H' / d + 1, ?_, ?_⟩
    · have hdm := Nat.div_add_mod H' d
      have hmod := Nat.mod_lt H' hd0
      have hexp : d * (H' / d + 1) = d * (H' / d) + d := Nat.mul_succ d _
      omega
    · have hdm := Nat.div_add_mod H' d
      have hexp : d * (H' / d + 1) = d * (H' / d) + d := Nat.mul_succ d _
      omega
  have hmM : d * (M - 1) + d = d * M := by
    have hexp : d * (M - 1 + 1) = d * (M - 1) + d := Nat.mul_succ d _
    rw [← hexp, Nat.sub_add_cancel hM1]
  have hsub : Finset.Ico (d * c₀) (d * c₀ + d * (M - 1))
      ⊆ Finset.Ico H' (H' + N) := by
    intro j hj
    rw [Finset.mem_Ico] at hj ⊢
    omega
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun j _ _ => by positivity))
  rw [sum_Ico_blocks_char_eq hd0 c₀ (M - 1), sum_Ico_shift_one_char c₀ (M - 1)]
  have hcount := totient_mul_le_sum_normSq_dirichletChar_Ico χ (c₀ + 1) (M - 1)
  have hd0' : (0 : ℝ) ≤ ((d : ℕ) : ℝ) := by positivity
  calc (q.totient : ℝ) * (((M - 1) / q : ℕ) : ℝ) * ((d : ℕ) : ℝ)
      = ((d : ℕ) : ℝ) * ((q.totient : ℝ) * (((M - 1) / q : ℕ) : ℝ)) := by ring
    _ ≤ ((d : ℕ) : ℝ) * ∑ b ∈ Finset.Ico (c₀ + 1) (c₀ + 1 + (M - 1)),
          ‖χ ((b : ℕ) : ZMod q)‖ ^ 2 := mul_le_mul_of_nonneg_left hcount hd0'

end MoltResearch
