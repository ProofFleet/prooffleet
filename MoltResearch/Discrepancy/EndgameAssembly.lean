import MoltResearch.Discrepancy.ChiTildeCutoff
import MoltResearch.Discrepancy.PureScaleCount
import MoltResearch.Discrepancy.GoodResidues

/-!
# Discrepancy: the §4 endgame assembly

Deterministic core of the Tao 2015 §4 endgame (arXiv:1509.05363,
`Problems/tao2015_derivation_c.md`, issue #2871): the lower bound that contradicts
eq. (contra) for large `H`.

`mul_sum_scales_le_good_window_moment`: for a primitive `χ` mod `q > 1`, a unimodular
`g`, and any set `S` of scales with `i ≤ k−1` and `2·qⁱ ≤ H`,

`⌊H/2⌋ · ∑_{i ∈ S} φ(q)·⌊(q^{k−i}−1)/q⌋·qⁱ
   ≤ 4·∑_{H' ∈ (H,2H]} ∑_{a ∈ [1,q^k] good} ‖∑_{m ≤ H'} χ̃(a+m)‖²
     + 16·H³·(2H·ω(q)·(q^k/2^k + 1))`.

Route (the paper's eq. (contra) → `∑_{i : qⁱ<√H} 1 ≪ 1` chain, run backwards as one
lower bound — no pigeonhole needed, the `H'`-average is kept throughout):

* each scale `i ∈ S` and window start `H' ∈ (H, H+⌊H/2⌋]` carries mass
  `φ(q)·⌊(q^{k−i}−1)/q⌋·qⁱ` (`sum_normSq_window_pure_scale_ge`);
* a `(H', H'+qⁱ]` window is the difference of two initial windows with endpoints in
  `(H, 2H]` (`‖x−y‖² ≤ 2‖x‖² + 2‖y‖²` plus an index shift), costing the factor `4`;
* the scale windows are among the diagonal terms of the divisor-cutoff expansion
  (`sum_normSq_window_charCutoff_comb`, weights `‖χ̃(d)‖² = 1`);
* the cutoff combination equals `χ̃` on good residues, is `1`-bounded on bad ones
  (`sum_divisors_chiTilde_charCutoff_of_good`, `norm_sum_divisors_chiTilde_charCutoff_le`),
  and is periodic mod `q^k`, aligning the full period `[0, q^k)` with `[1, q^k]`;
* the bad residues are counted by `card_not_goodResidue_le`.

The stochastic wrapper feeds eq. (contra) into the right side and picks `H`, then `k`,
making the left side larger — the paper's contradiction.
-/

namespace MoltResearch

open Finset

variable {g : ℕ → ℂ} {q : ℕ} {χ : DirichletCharacter ℂ q} {t : ℝ}

/-- Quadratic triangle inequality: `‖x − y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
private lemma norm_sub_sq_le (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_sub_le x y
  have h0 : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y]

/-- The divisor cutoffs are periodic mod `q^k` (for divisors of `q^{k−1}`): the indicator
is `q^k`-periodic and the cofactor shifts by a multiple of `q`. -/
private lemma charCutoff_add_pow (hq : q ≠ 0) {k d : ℕ} (hk : 1 ≤ k)
    (hd : d ∣ q ^ (k - 1)) (n : ℕ) :
    charCutoff χ d (n + q ^ k) = charCutoff χ d n := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (pow_ne_zero _ hq) hd
  have hdk : d ∣ q ^ k := hd.trans (pow_dvd_pow q (Nat.sub_le k 1))
  by_cases hdn : d ∣ n
  · rw [charCutoff_of_dvd (hdn.add hdk), charCutoff_of_dvd hdn,
      Nat.add_div_of_dvd_right hdn]
    -- the shift `q^k/d` is a multiple of `q`
    obtain ⟨e, he⟩ := hd
    have hqk : q ^ k = d * (e * q) := by
      have hsplit : q ^ k = q ^ (k - 1) * q := by
        rw [← pow_succ, Nat.sub_add_cancel hk]
      rw [hsplit, he]
      ring
    have hqdvd : q ^ k / d = e * q := by
      rw [hqk, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
    rw [hqdvd]
    congr 1
    push_cast
    rw [ZMod.natCast_self]
    ring
  · rw [charCutoff_of_not_dvd hdn,
      charCutoff_of_not_dvd fun hcon => hdn ((Nat.dvd_add_left hdk).mp hcon)]

/-- A sum over the full period `[0, P)` equals the sum over `[1, P]` when the summand
agrees at `0` and `P`. -/
private lemma sum_range_eq_sum_Icc_of_periodic {P : ℕ} (hP : 1 ≤ P) (G : ℕ → ℝ)
    (hper : G 0 = G P) :
    ∑ a ∈ Finset.range P, G a = ∑ a ∈ Finset.Icc 1 P, G a := by
  obtain ⟨P', rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_Icc_succ_top (by omega : 1 ≤ P' + 1)]
  have hIcc : ∑ a ∈ Finset.Icc 1 P', G a = ∑ i ∈ Finset.range P', G (i + 1) := by
    rw [show Finset.Icc 1 P' = Finset.Ico 1 (P' + 1) from Finset.val_inj.mp rfl,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm 1 i]
  rw [hIcc, hper]

/-- Reinstating the bad residues: the full-period window moment of the divisor-cutoff
combination is at most the good-residue `χ̃` moment plus `4H²` per bad residue. -/
private lemma sum_range_normSq_comb_le {k H H' : ℕ} (hq : 1 < q) (hk : 1 ≤ k)
    (hH' : H' ≤ 2 * H) (hu : Unimodular g) :
    ∑ a ∈ Finset.range (q ^ k),
        ‖∑ m ∈ Finset.Icc 1 H',
            ∑ d ∈ (q ^ (k - 1)).divisors, chiTilde g q χ t d * charCutoff χ d (a + m)‖ ^ 2
      ≤ (∑ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a => IsGoodResidue q k H a),
            ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2)
        + 4 * (H : ℝ) ^ 2
            * (((Finset.Icc 1 (q ^ k)).filter fun a => ¬ IsGoodResidue q k H a).card : ℝ) := by
  have hq0 : q ≠ 0 := by omega
  have hP1 : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
  -- shift the full period `[0, q^k)` to `[1, q^k]` using periodicity of the combination
  have hper : ∀ n : ℕ, ∑ d ∈ (q ^ (k - 1)).divisors,
      chiTilde g q χ t d * charCutoff χ d (n + q ^ k)
        = ∑ d ∈ (q ^ (k - 1)).divisors, chiTilde g q χ t d * charCutoff χ d n :=
    fun n => Finset.sum_congr rfl fun d hd => by
      rw [charCutoff_add_pow hq0 hk (Nat.mem_divisors.mp hd).1 n]
  have hshift : ∑ a ∈ Finset.range (q ^ k),
      ‖∑ m ∈ Finset.Icc 1 H',
          ∑ d ∈ (q ^ (k - 1)).divisors, chiTilde g q χ t d * charCutoff χ d (a + m)‖ ^ 2
        = ∑ a ∈ Finset.Icc 1 (q ^ k),
            ‖∑ m ∈ Finset.Icc 1 H',
              ∑ d ∈ (q ^ (k - 1)).divisors,
                chiTilde g q χ t d * charCutoff χ d (a + m)‖ ^ 2 := by
    refine sum_range_eq_sum_Icc_of_periodic hP1 _ ?_
    have harg : ∀ m : ℕ, ∑ d ∈ (q ^ (k - 1)).divisors,
        chiTilde g q χ t d * charCutoff χ d (0 + m)
          = ∑ d ∈ (q ^ (k - 1)).divisors,
              chiTilde g q χ t d * charCutoff χ d (q ^ k + m) := by
      intro m
      rw [Nat.zero_add, Nat.add_comm (q ^ k) m, hper m]
    rw [Finset.sum_congr rfl fun m _ => harg m]
  rw [hshift, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (q ^ k))
    (fun a => IsGoodResidue q k H a)]
  -- good residues: the combination is `χ̃`
  have hgood : ∀ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a => IsGoodResidue q k H a),
      ‖∑ m ∈ Finset.Icc 1 H',
          ∑ d ∈ (q ^ (k - 1)).divisors, chiTilde g q χ t d * charCutoff χ d (a + m)‖ ^ 2
        = ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2 := by
    intro a ha
    have hga := (Finset.mem_filter.mp ha).2
    have hterm : ∀ m ∈ Finset.Icc 1 H',
        ∑ d ∈ (q ^ (k - 1)).divisors, chiTilde g q χ t d * charCutoff χ d (a + m)
          = chiTilde g q χ t (a + m) := by
      intro m hm
      have hm' : m ∈ Finset.Icc 1 (2 * H) := by
        rw [Finset.mem_Icc] at hm ⊢
        omega
      exact sum_divisors_chiTilde_charCutoff_of_good hq0 hga hm'
    rw [Finset.sum_congr rfl hterm]
  -- bad residues: the combination window is bounded by `H' ≤ 2H`
  have hbad : ∀ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a => ¬ IsGoodResidue q k H a),
      ‖∑ m ∈ Finset.Icc 1 H',
          ∑ d ∈ (q ^ (k - 1)).divisors, chiTilde g q χ t d * charCutoff χ d (a + m)‖ ^ 2
        ≤ 4 * (H : ℝ) ^ 2 := by
    intro a _
    have hnorm : ‖∑ m ∈ Finset.Icc 1 H',
        ∑ d ∈ (q ^ (k - 1)).divisors, chiTilde g q χ t d * charCutoff χ d (a + m)‖
          ≤ 2 * (H : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ m ∈ Finset.Icc 1 H',
            ‖∑ d ∈ (q ^ (k - 1)).divisors, chiTilde g q χ t d * charCutoff χ d (a + m)‖
          ≤ ∑ _m ∈ Finset.Icc 1 H', (1 : ℝ) :=
            Finset.sum_le_sum fun m _ =>
              norm_sum_divisors_chiTilde_charCutoff_le hu hq0 (k - 1) (a + m)
        _ = (H' : ℝ) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
            norm_num
        _ ≤ 2 * (H : ℝ) := by exact_mod_cast hH'
    have h0 : (0 : ℝ) ≤ ‖∑ m ∈ Finset.Icc 1 H',
        ∑ d ∈ (q ^ (k - 1)).divisors, chiTilde g q χ t d * charCutoff χ d (a + m)‖ :=
      norm_nonneg _
    nlinarith
  refine le_trans (add_le_add (le_of_eq (Finset.sum_congr rfl hgood))
    (Finset.sum_le_sum hbad)) (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- **The §4 endgame lower bound** (Tao 2015): the good-residue window moment of `χ̃`
dominates the pure-scale mass.  With eq. (contra) bounding the right side, choosing many
scales (i.e. `H` and then `k` large) yields the paper's contradiction. -/
theorem mul_sum_scales_le_good_window_moment (hq : 1 < q) {k : ℕ} (hk : 1 ≤ k)
    (hχ : χ.IsPrimitive) (hu : Unimodular g) {H : ℕ} (hH : 1 ≤ H) (S : Finset ℕ)
    (hSk : ∀ i ∈ S, i ≤ k - 1) (hSH : ∀ i ∈ S, 2 * q ^ i ≤ H) :
    ((H / 2 : ℕ) : ℝ)
        * ∑ i ∈ S, (q.totient : ℝ) * (((q ^ (k - i) - 1) / q : ℕ) : ℝ) * ((q ^ i : ℕ) : ℝ)
      ≤ 4 * ∑ H' ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a => IsGoodResidue q k H a),
              ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2
        + 16 * (H : ℝ) ^ 3
            * ((2 * H * q.primeFactors.card * (q ^ k / 2 ^ k + 1) : ℕ) : ℝ) := by
  have hq1 : 1 ≤ q := by omega
  -- Step 1: the scale mass is dominated by the `(H', H'+qⁱ]` window moments over
  -- `H' ∈ (H, H + ⌊H/2⌋]`.
  have hstep1 : ((H / 2 : ℕ) : ℝ)
      * ∑ i ∈ S, (q.totient : ℝ) * (((q ^ (k - i) - 1) / q : ℕ) : ℝ) * ((q ^ i : ℕ) : ℝ)
        ≤ ∑ i ∈ S, ∑ H' ∈ Finset.Ioc H (H + H / 2),
            ∑ a ∈ Finset.range (q ^ k),
              ‖∑ m ∈ Finset.Ioc H' (H' + q ^ i), charCutoff χ (q ^ i) (a + m)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hik : i ≤ k := le_trans (hSk i hi) (Nat.sub_le k 1)
    have hcardT : (Finset.Ioc H (H + H / 2)).card = H / 2 := by
      rw [Nat.card_Ioc]
      omega
    calc ((H / 2 : ℕ) : ℝ)
          * ((q.totient : ℝ) * (((q ^ (k - i) - 1) / q : ℕ) : ℝ) * ((q ^ i : ℕ) : ℝ))
        = ∑ _H' ∈ Finset.Ioc H (H + H / 2),
            (q.totient : ℝ) * (((q ^ (k - i) - 1) / q : ℕ) : ℝ) * ((q ^ i : ℕ) : ℝ) := by
          rw [Finset.sum_const, hcardT, nsmul_eq_mul]
      _ ≤ ∑ H' ∈ Finset.Ioc H (H + H / 2),
            ∑ a ∈ Finset.range (q ^ k),
              ‖∑ m ∈ Finset.Ioc H' (H' + q ^ i), charCutoff χ (q ^ i) (a + m)‖ ^ 2 :=
          Finset.sum_le_sum fun H' _ => sum_normSq_window_pure_scale_ge hq1 χ hik H'
  -- Step 2: each `(H', H'+qⁱ]` window is a difference of two initial windows in `(H, 2H]`.
  have hstep2 : ∀ i ∈ S, ∑ H' ∈ Finset.Ioc H (H + H / 2),
      ∑ a ∈ Finset.range (q ^ k),
        ‖∑ m ∈ Finset.Ioc H' (H' + q ^ i), charCutoff χ (q ^ i) (a + m)‖ ^ 2
        ≤ 4 * ∑ H' ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ Finset.range (q ^ k),
              ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ (q ^ i) (a + m)‖ ^ 2 := by
    intro i hi
    -- opaque scale so the interval arithmetic below is linear
    obtain ⟨Q, hQ, hQH⟩ : ∃ Q : ℕ, q ^ i = Q ∧ 2 * Q ≤ H := ⟨q ^ i, rfl, hSH i hi⟩
    rw [hQ]
    have hpt : ∀ H' a : ℕ,
        ‖∑ m ∈ Finset.Ioc H' (H' + Q), charCutoff χ Q (a + m)‖ ^ 2
          ≤ 2 * ‖∑ m ∈ Finset.Icc 1 (H' + Q), charCutoff χ Q (a + m)‖ ^ 2
            + 2 * ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ Q (a + m)‖ ^ 2 := by
      intro H' a
      have hIcc1 : Finset.Icc 1 H' = Finset.Ioc 0 H' := Finset.val_inj.mp rfl
      have hIcc2 : Finset.Icc 1 (H' + Q) = Finset.Ioc 0 (H' + Q) := Finset.val_inj.mp rfl
      have hdecomp : ∑ m ∈ Finset.Ioc H' (H' + Q), charCutoff χ Q (a + m)
          = (∑ m ∈ Finset.Icc 1 (H' + Q), charCutoff χ Q (a + m))
            - ∑ m ∈ Finset.Icc 1 H', charCutoff χ Q (a + m) := by
        rw [hIcc1, hIcc2]
        exact eq_sub_of_add_eq' (Finset.sum_Ioc_consecutive
          (fun m => charCutoff χ Q (a + m)) (Nat.zero_le H') (Nat.le_add_right H' Q))
      rw [hdecomp]
      exact norm_sub_sq_le _ _
    calc ∑ H' ∈ Finset.Ioc H (H + H / 2),
          ∑ a ∈ Finset.range (q ^ k),
            ‖∑ m ∈ Finset.Ioc H' (H' + Q), charCutoff χ Q (a + m)‖ ^ 2
        ≤ ∑ H' ∈ Finset.Ioc H (H + H / 2),
            (2 * ∑ a ∈ Finset.range (q ^ k),
                ‖∑ m ∈ Finset.Icc 1 (H' + Q), charCutoff χ Q (a + m)‖ ^ 2
              + 2 * ∑ a ∈ Finset.range (q ^ k),
                  ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ Q (a + m)‖ ^ 2) := by
          refine Finset.sum_le_sum fun H' _ => ?_
          calc ∑ a ∈ Finset.range (q ^ k),
                ‖∑ m ∈ Finset.Ioc H' (H' + Q), charCutoff χ Q (a + m)‖ ^ 2
              ≤ ∑ a ∈ Finset.range (q ^ k),
                  (2 * ‖∑ m ∈ Finset.Icc 1 (H' + Q), charCutoff χ Q (a + m)‖ ^ 2
                    + 2 * ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ Q (a + m)‖ ^ 2) :=
                Finset.sum_le_sum fun a _ => hpt H' a
            _ = 2 * ∑ a ∈ Finset.range (q ^ k),
                  ‖∑ m ∈ Finset.Icc 1 (H' + Q), charCutoff χ Q (a + m)‖ ^ 2
                + 2 * ∑ a ∈ Finset.range (q ^ k),
                    ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ Q (a + m)‖ ^ 2 := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 2 * ∑ H' ∈ Finset.Ioc H (H + H / 2),
            ∑ a ∈ Finset.range (q ^ k),
              ‖∑ m ∈ Finset.Icc 1 (H' + Q), charCutoff χ Q (a + m)‖ ^ 2
          + 2 * ∑ H' ∈ Finset.Ioc H (H + H / 2),
              ∑ a ∈ Finset.range (q ^ k),
                ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ Q (a + m)‖ ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * ∑ H' ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ Finset.range (q ^ k),
              ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ Q (a + m)‖ ^ 2
          + 2 * ∑ H' ∈ Finset.Ioc H (2 * H),
              ∑ a ∈ Finset.range (q ^ k),
                ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ Q (a + m)‖ ^ 2 := by
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num))
            (mul_le_mul_of_nonneg_left ?_ (by norm_num))
          · -- shift the window endpoint by `Q`
            have himg : ∑ H' ∈ Finset.Ioc H (H + H / 2),
                ∑ a ∈ Finset.range (q ^ k),
                  ‖∑ m ∈ Finset.Icc 1 (H' + Q), charCutoff χ Q (a + m)‖ ^ 2
                  = ∑ y ∈ Finset.Ioc (H + Q) (H + H / 2 + Q),
                      ∑ a ∈ Finset.range (q ^ k),
                        ‖∑ m ∈ Finset.Icc 1 y, charCutoff χ Q (a + m)‖ ^ 2 := by
              rw [← Finset.image_add_right_Ioc]
              exact (Finset.sum_image (g := fun x => x + Q)
                (f := fun y => ∑ a ∈ Finset.range (q ^ k),
                  ‖∑ m ∈ Finset.Icc 1 y, charCutoff χ Q (a + m)‖ ^ 2)
                ((add_left_injective Q).injOn)).symm
            rw [himg]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ => by positivity
            intro y hy
            rw [Finset.mem_Ioc] at hy ⊢
            omega
          · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ => by positivity
            intro y hy
            rw [Finset.mem_Ioc] at hy ⊢
            omega
      _ = 4 * ∑ H' ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ Finset.range (q ^ k),
              ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ Q (a + m)‖ ^ 2 := by ring
  -- Step 3: per `H'`, the scale windows are diagonal terms of the cutoff expansion.
  have hstep3 : ∀ H' ∈ Finset.Ioc H (2 * H),
      ∑ i ∈ S, ∑ a ∈ Finset.range (q ^ k),
          ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ (q ^ i) (a + m)‖ ^ 2
        ≤ ∑ a ∈ Finset.range (q ^ k),
            ‖∑ m ∈ Finset.Icc 1 H',
              ∑ d ∈ (q ^ (k - 1)).divisors,
                chiTilde g q χ t d * charCutoff χ d (a + m)‖ ^ 2 := by
    intro H' _
    rw [sum_normSq_window_charCutoff_comb hq hk hχ (chiTilde g q χ t) H']
    have hw : ∀ d ∈ (q ^ (k - 1)).divisors,
        ‖chiTilde g q χ t d‖ ^ 2 * ∑ a ∈ Finset.range (q ^ k),
            ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ d (a + m)‖ ^ 2
          = ∑ a ∈ Finset.range (q ^ k),
              ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ d (a + m)‖ ^ 2 := by
      intro d _
      rw [chiTilde_unimodular hu d, one_pow, one_mul]
    rw [Finset.sum_congr rfl hw]
    have himg : ∑ i ∈ S, ∑ a ∈ Finset.range (q ^ k),
        ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ (q ^ i) (a + m)‖ ^ 2
          = ∑ d ∈ S.image (q ^ ·), ∑ a ∈ Finset.range (q ^ k),
              ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ d (a + m)‖ ^ 2 := by
      exact (Finset.sum_image (g := fun i => q ^ i)
        (f := fun d => ∑ a ∈ Finset.range (q ^ k),
          ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ d (a + m)‖ ^ 2)
        fun x _ y _ h => (Nat.pow_right_inj hq).mp h).symm
    rw [himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => by positivity
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨i, hiS, rfl⟩ := hd
    exact Nat.mem_divisors.mpr ⟨pow_dvd_pow q (hSk i hiS), pow_ne_zero _ (by omega)⟩
  -- Step 4: reinstate the bad residues across the `(H, 2H]` average.
  have hstep4 : ∑ H' ∈ Finset.Ioc H (2 * H),
      ∑ a ∈ Finset.range (q ^ k),
        ‖∑ m ∈ Finset.Icc 1 H',
            ∑ d ∈ (q ^ (k - 1)).divisors,
              chiTilde g q χ t d * charCutoff χ d (a + m)‖ ^ 2
        ≤ (∑ H' ∈ Finset.Ioc H (2 * H),
              ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a => IsGoodResidue q k H a),
                ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2)
          + (H : ℝ) * (4 * (H : ℝ) ^ 2
              * (((Finset.Icc 1 (q ^ k)).filter fun a => ¬ IsGoodResidue q k H a).card : ℝ)) := by
    calc ∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ Finset.range (q ^ k),
            ‖∑ m ∈ Finset.Icc 1 H',
                ∑ d ∈ (q ^ (k - 1)).divisors,
                  chiTilde g q χ t d * charCutoff χ d (a + m)‖ ^ 2
        ≤ ∑ H' ∈ Finset.Ioc H (2 * H),
            ((∑ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a => IsGoodResidue q k H a),
                ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2)
              + 4 * (H : ℝ) ^ 2
                  * (((Finset.Icc 1 (q ^ k)).filter
                      fun a => ¬ IsGoodResidue q k H a).card : ℝ)) := by
          refine Finset.sum_le_sum fun H' hH' => ?_
          rw [Finset.mem_Ioc] at hH'
          exact sum_range_normSq_comb_le hq hk hH'.2 hu
      _ = (∑ H' ∈ Finset.Ioc H (2 * H),
              ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a => IsGoodResidue q k H a),
                ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2)
          + ((Finset.Ioc H (2 * H)).card : ℝ) * (4 * (H : ℝ) ^ 2
              * (((Finset.Icc 1 (q ^ k)).filter
                  fun a => ¬ IsGoodResidue q k H a).card : ℝ)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      _ = _ := by
          have hcard : (Finset.Ioc H (2 * H)).card = H := by
            rw [Nat.card_Ioc]
            omega
          rw [hcard]
  -- Combine.
  have hbadcount : (((Finset.Icc 1 (q ^ k)).filter
      fun a => ¬ IsGoodResidue q k H a).card : ℝ)
        ≤ ((2 * H * q.primeFactors.card * (q ^ k / 2 ^ k + 1) : ℕ) : ℝ) := by
    exact_mod_cast card_not_goodResidue_le q k H (by omega)
  calc ((H / 2 : ℕ) : ℝ)
        * ∑ i ∈ S, (q.totient : ℝ) * (((q ^ (k - i) - 1) / q : ℕ) : ℝ) * ((q ^ i : ℕ) : ℝ)
      ≤ ∑ i ∈ S, ∑ H' ∈ Finset.Ioc H (H + H / 2),
          ∑ a ∈ Finset.range (q ^ k),
            ‖∑ m ∈ Finset.Ioc H' (H' + q ^ i), charCutoff χ (q ^ i) (a + m)‖ ^ 2 := hstep1
    _ ≤ ∑ i ∈ S, 4 * ∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ Finset.range (q ^ k),
            ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ (q ^ i) (a + m)‖ ^ 2 :=
        Finset.sum_le_sum hstep2
    _ = 4 * ∑ H' ∈ Finset.Ioc H (2 * H), ∑ i ∈ S,
          ∑ a ∈ Finset.range (q ^ k),
            ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ (q ^ i) (a + m)‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 4 * ∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ Finset.range (q ^ k),
            ‖∑ m ∈ Finset.Icc 1 H',
                ∑ d ∈ (q ^ (k - 1)).divisors,
                  chiTilde g q χ t d * charCutoff χ d (a + m)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep3) (by norm_num)
    _ ≤ 4 * ((∑ H' ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a => IsGoodResidue q k H a),
              ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2)
          + (H : ℝ) * (4 * (H : ℝ) ^ 2
              * (((Finset.Icc 1 (q ^ k)).filter
                  fun a => ¬ IsGoodResidue q k H a).card : ℝ))) :=
        mul_le_mul_of_nonneg_left hstep4 (by norm_num)
    _ ≤ 4 * ∑ H' ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a => IsGoodResidue q k H a),
              ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2
        + 16 * (H : ℝ) ^ 3
            * ((2 * H * q.primeFactors.card * (q ^ k / 2 ^ k + 1) : ℕ) : ℝ) := by
        have key : (H : ℝ) ^ 3 * (((Finset.Icc 1 (q ^ k)).filter
              fun a => ¬ IsGoodResidue q k H a).card : ℝ)
            ≤ (H : ℝ) ^ 3
              * ((2 * H * q.primeFactors.card * (q ^ k / 2 ^ k + 1) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hbadcount (by positivity)
        linarith [key]

end MoltResearch
