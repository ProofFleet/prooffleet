import MoltResearch.Discrepancy.EndgameAssembly

/-!
# Discrepancy: the §4 endgame contradiction extractor

Final deterministic step of the Tao 2015 §4 endgame (arXiv:1509.05363,
`Problems/tao2015_derivation_c.md`, issue #2871): for every primitive character and
every candidate constant `E ≥ 0`, there are explicit `H` and `k` for which the
eq. (contra) bound `≤ E` is **false for every unimodular sample**
(`exists_H_k_refuting_contra`).

* `q = 1`: `χ̃ ≡ 1` (`chiTilde_apply_level_one`), the lone residue `a = 1` is good, and
  each window sums to `H' > H`, so the left side is `≥ H²`; take `H² > E`.
* `q ≥ 2`: with `s` scales, `H = 2·q^s` and `k` huge, the endgame assembly
  (`mul_sum_scales_le_good_window_moment`) is contradicted: choosing
  `s·φ(q) ≥ 32·q·E + 8` covers the main term `8·q^{k+s}·E` twice over, and
  `2^k ≥ 512·q^{4s+1}·(ω(q)+1)`, `q^{k−1} ≥ 512·q^{4s}·(ω(q)+1)` reduce the bad-residue
  errors below the surplus — the paper's "`∑_{i : qⁱ<√H} 1 ≪_ε 1`, contradiction for `H`
  large" in explicit form.

Consumer: the stochastic wrapper
`[LogElliottNonasymptoticAssumption] → [VinogradovKorobovAssumption] →
BorweinChoiCoonsAssumption` picks `H, k` from this lemma *before* the chain threshold,
then feeds `contra_of_pretentious_window` at scale `X`.
-/

namespace MoltResearch

open Finset

/-- At level `1` the completion `χ̃` is identically `1` on positive integers. -/
theorem chiTilde_apply_level_one (g : ℕ → ℂ) (χ : DirichletCharacter ℂ 1) (t : ℝ)
    {u : ℕ} (hu : u ≠ 0) : chiTilde g 1 χ t u = 1 := by
  rw [chiTilde_apply_of_coprime hu (Nat.coprime_one_right u),
    Subsingleton.elim ((u : ℕ) : ZMod 1) 1, map_one]

/-- The `q = 1` branch: the (contra) left side is at least `H²`. -/
private lemma level_one_lower (χ : DirichletCharacter ℂ 1) (g : ℕ → ℂ) (t : ℝ)
    {H k : ℕ} (hH : 1 ≤ H) :
    (H : ℝ) ^ 2 ≤ (1 / ((1 : ℝ) ^ k))
        * ∑ a ∈ (Finset.Icc 1 (1 ^ k)).filter (fun a => IsGoodResidue 1 k H a),
            ((1 : ℝ) / H) * ∑ H' ∈ Finset.Ioc H (2 * H),
              ‖∑ m ∈ Finset.Icc 1 H', chiTilde g 1 χ t (a + m)‖ ^ 2 := by
  have hgood1 : IsGoodResidue 1 k H 1 := by
    intro m _ p hp hpq
    exact absurd (Nat.eq_one_of_dvd_one hpq) hp.ne_one
  have hfilter : (Finset.Icc 1 (1 ^ k)).filter (fun a => IsGoodResidue 1 k H a)
      = {1} := by
    rw [one_pow, Finset.Icc_self]
    refine Finset.filter_true_of_mem fun a ha => ?_
    rw [Finset.mem_singleton] at ha
    rw [ha]
    exact hgood1
  rw [hfilter, Finset.sum_singleton, one_pow, div_one, one_mul]
  have hwin : ∀ H' ∈ Finset.Ioc H (2 * H),
      ‖∑ m ∈ Finset.Icc 1 H', chiTilde g 1 χ t (1 + m)‖ ^ 2 = ((H' : ℝ)) ^ 2 := by
    intro H' _
    have hterm : ∀ m ∈ Finset.Icc 1 H', chiTilde g 1 χ t (1 + m) = 1 := fun m _ =>
      chiTilde_apply_level_one g χ t (by omega)
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
      mul_one, show H' + 1 - 1 = H' from by omega, Complex.norm_natCast]
  rw [Finset.sum_congr rfl hwin]
  have hbound : ∀ H' ∈ Finset.Ioc H (2 * H), (H : ℝ) ^ 2 ≤ ((H' : ℝ)) ^ 2 := by
    intro H' hH'
    rw [Finset.mem_Ioc] at hH'
    have h1 : (H : ℝ) ≤ (H' : ℝ) := by exact_mod_cast hH'.1.le
    have h0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    nlinarith
  have hsum : (H : ℝ) * (H : ℝ) ^ 2 ≤ ∑ H' ∈ Finset.Ioc H (2 * H), ((H' : ℝ)) ^ 2 := by
    have hcard : (Finset.Ioc H (2 * H)).card = H := by
      rw [Nat.card_Ioc]
      omega
    calc (H : ℝ) * (H : ℝ) ^ 2
        = (Finset.Ioc H (2 * H)).card • ((H : ℝ) ^ 2) := by rw [hcard, nsmul_eq_mul]
      _ ≤ ∑ H' ∈ Finset.Ioc H (2 * H), ((H' : ℝ)) ^ 2 :=
          Finset.card_nsmul_le_sum _ _ _ hbound
  have hH0 : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hkey : (1 : ℝ) / H * ((H : ℝ) * (H : ℝ) ^ 2) = (H : ℝ) ^ 2 := by
    field_simp
  calc (H : ℝ) ^ 2 = (1 : ℝ) / H * ((H : ℝ) * (H : ℝ) ^ 2) := hkey.symm
    _ ≤ (1 : ℝ) / H * ∑ H' ∈ Finset.Ioc H (2 * H), ((H' : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)

/-- The `q ≥ 2` branch, parametric in the scale count `s` and depth `k`: the endgame
assembly refutes eq. (contra) once `s·φ(q) ≥ 32qE + 8` and `k` is deep enough. -/
private lemma not_contra_of_params {g : ℕ → ℂ} {q : ℕ} {χ : DirichletCharacter ℂ q}
    {t : ℝ} (hq2 : 2 ≤ q) (hχ : χ.IsPrimitive) {E : ℝ} (hE : 0 ≤ E) {s k : ℕ}
    (hs1 : 1 ≤ s) (hks : s + 1 ≤ k)
    (hsφ : 32 * (q : ℝ) * E + 8 ≤ (s : ℝ) * (q.totient : ℝ))
    (hbig1 : 512 * q ^ (4 * s) * (q.primeFactors.card + 1) * q ≤ 2 ^ k)
    (hbig2 : 512 * q ^ (4 * s) * (q.primeFactors.card + 1) ≤ q ^ (k - 1))
    (hu : Unimodular g) :
    ¬ ((1 / ((q : ℝ) ^ k))
        * ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter
            (fun a => IsGoodResidue q k (2 * q ^ s) a),
            ((1 : ℝ) / (2 * q ^ s : ℕ)) * ∑ H' ∈ Finset.Ioc (2 * q ^ s) (2 * (2 * q ^ s)),
              ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2
      ≤ E) := by
  intro hcon
  have hq1 : 1 < q := hq2
  have hk1 : 1 ≤ k := by omega
  have hqs1 : 1 ≤ q ^ s := Nat.one_le_pow _ _ (by omega)
  have hH1 : 1 ≤ 2 * q ^ s := le_trans hqs1 (Nat.le_mul_of_pos_left _ (by omega))
  -- convert (contra ≤ E) into the good-window moment bound
  have hpull : ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter
      (fun a => IsGoodResidue q k (2 * q ^ s) a),
      ((1 : ℝ) / (2 * q ^ s : ℕ)) * ∑ H' ∈ Finset.Ioc (2 * q ^ s) (2 * (2 * q ^ s)),
        ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2
      = ((1 : ℝ) / (2 * q ^ s : ℕ))
          * ∑ H' ∈ Finset.Ioc (2 * q ^ s) (2 * (2 * q ^ s)),
              ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter
                  (fun a => IsGoodResidue q k (2 * q ^ s) a),
                ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2 := by
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_comm
  rw [hpull] at hcon
  have hqk0 : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have hH0 : (0 : ℝ) < ((2 * q ^ s : ℕ) : ℝ) := by exact_mod_cast hH1
  have hGT : ∑ H' ∈ Finset.Ioc (2 * q ^ s) (2 * (2 * q ^ s)),
      ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a => IsGoodResidue q k (2 * q ^ s) a),
        ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2
      ≤ (q : ℝ) ^ k * ((2 * q ^ s : ℕ) : ℝ) * E := by
    have h := mul_le_mul_of_nonneg_left hcon (mul_pos hqk0 hH0).le
    calc ∑ H' ∈ Finset.Ioc (2 * q ^ s) (2 * (2 * q ^ s)),
          ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter
              (fun a => IsGoodResidue q k (2 * q ^ s) a),
            ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2
        = ((q : ℝ) ^ k * ((2 * q ^ s : ℕ) : ℝ))
            * (1 / ((q : ℝ) ^ k) * (((1 : ℝ) / (2 * q ^ s : ℕ))
              * ∑ H' ∈ Finset.Ioc (2 * q ^ s) (2 * (2 * q ^ s)),
                  ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter
                      (fun a => IsGoodResidue q k (2 * q ^ s) a),
                    ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2)) := by
          field_simp
      _ ≤ ((q : ℝ) ^ k * ((2 * q ^ s : ℕ) : ℝ)) * E := h
      _ = (q : ℝ) ^ k * ((2 * q ^ s : ℕ) : ℝ) * E := by ring
  -- the endgame assembly at scales `S = range s`
  have hSk : ∀ i ∈ Finset.range s, i ≤ k - 1 := fun i hi => by
    have := Finset.mem_range.mp hi
    omega
  have hSH : ∀ i ∈ Finset.range s, 2 * q ^ i ≤ 2 * q ^ s := fun i hi =>
    Nat.mul_le_mul_left 2
      (Nat.pow_le_pow_right (by omega) (Finset.mem_range.mp hi).le)
  have hE4 := mul_sum_scales_le_good_window_moment (g := g) (t := t) hq1 hk1 hχ hu
    hH1 (Finset.range s) hSk hSH
  -- the per-scale mass in explicit form
  have hβ : ∀ i ∈ Finset.range s,
      (q.totient : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ) / 2
        ≤ (q.totient : ℝ) * (((q ^ (k - i) - 1) / q : ℕ) : ℝ) * ((q ^ i : ℕ) : ℝ) := by
    intro i hi
    have hik2 : i + 2 ≤ k := by
      have := Finset.mem_range.mp hi
      omega
    have hdiv : (q ^ (k - i) - 1) / q = q ^ (k - i - 1) - 1 := by
      obtain ⟨A, hA⟩ : ∃ A, q ^ (k - i - 1) = A := ⟨_, rfl⟩
      have hA1 : 1 ≤ A := hA ▸ Nat.one_le_pow _ _ (by omega)
      have hpow : q ^ (k - i) = A * q := by
        rw [← hA, ← pow_succ]
        congr 1
        omega
      rw [hpow, hA]
      have hqA : q ≤ A * q := Nat.le_mul_of_pos_left q (by omega)
      refine Nat.div_eq_of_lt_le ?_ ?_
      · have hsub : (A - 1) * q = A * q - q := by rw [Nat.sub_mul, one_mul]
        omega
      · have hA1' : A - 1 + 1 = A := by omega
        rw [hA1']
        omega
    rw [hdiv]
    have hone : 1 ≤ q ^ (k - i - 1) := Nat.one_le_pow _ _ (by omega)
    rw [Nat.cast_sub hone, Nat.cast_one]
    have hmul : q ^ (k - i - 1) * q ^ i = q ^ (k - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hmulR : ((q ^ (k - i - 1) : ℕ) : ℝ) * ((q ^ i : ℕ) : ℝ)
        = ((q ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast hmul
    have h2i : 2 * q ^ i ≤ q ^ (k - 1) := by
      calc 2 * q ^ i ≤ q * q ^ i := Nat.mul_le_mul_right _ (by omega)
        _ = q ^ (i + 1) := by rw [pow_succ, Nat.mul_comm]
        _ ≤ q ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2iR : 2 * ((q ^ i : ℕ) : ℝ) ≤ ((q ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast h2i
    have hφ0 : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
    have hexpand : (q.totient : ℝ) * (((q ^ (k - i - 1) : ℕ) : ℝ) - 1)
          * ((q ^ i : ℕ) : ℝ)
        = (q.totient : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ)
          - (q.totient : ℝ) * ((q ^ i : ℕ) : ℝ) := by
      rw [← hmulR]
      ring
    rw [hexpand]
    have hprod := mul_le_mul_of_nonneg_left h2iR hφ0
    linarith
  have hSsum : (s : ℝ) * ((q.totient : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ) / 2)
      ≤ ∑ i ∈ Finset.range s,
          (q.totient : ℝ) * (((q ^ (k - i) - 1) / q : ℕ) : ℝ) * ((q ^ i : ℕ) : ℝ) := by
    calc (s : ℝ) * ((q.totient : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ) / 2)
        = (Finset.range s).card • ((q.totient : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ) / 2) := by
          rw [Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := Finset.card_nsmul_le_sum _ _ _ hβ
  -- `⌊H/2⌋ = q^s` exactly
  have hH2 : 2 * q ^ s / 2 = q ^ s := Nat.mul_div_cancel_left _ (by omega)
  rw [hH2] at hE4
  -- real-atom bookkeeping
  have hX1 : (1 : ℝ) ≤ ((q ^ (k - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow (k - 1) q (by omega)
  have hY1 : (1 : ℝ) ≤ ((q ^ s : ℕ) : ℝ) := by exact_mod_cast hqs1
  have hKX : ((q ^ k : ℕ) : ℝ) = (q : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ) := by
    have : q ^ k = q * q ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    exact_mod_cast this
  -- bad-term bound: `16H³·BC ≤ 512·q^{4s}·ω·(q^k/2^k + 1) ≤ 2·q^{k−1}`
  have hbadN : 512 * q ^ (4 * s) * q.primeFactors.card * (q ^ k)
      ≤ 2 ^ k * q ^ (k - 1) := by
    calc 512 * q ^ (4 * s) * q.primeFactors.card * q ^ k
        = 512 * q ^ (4 * s) * q.primeFactors.card * q * q ^ (k - 1) := by
          have : q ^ k = q * q ^ (k - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          rw [this]
          ring
      _ ≤ 512 * q ^ (4 * s) * (q.primeFactors.card + 1) * q * q ^ (k - 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left _ (by omega)))
      _ ≤ 2 ^ k * q ^ (k - 1) := Nat.mul_le_mul_right _ hbig1
  have h2k0 : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hbad1R : 512 * ((q ^ (4 * s) : ℕ) : ℝ) * (q.primeFactors.card : ℝ)
      * (((q ^ k : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ)) ≤ ((q ^ (k - 1) : ℕ) : ℝ) := by
    rw [mul_div_assoc', div_le_iff₀ h2k0]
    calc 512 * ((q ^ (4 * s) : ℕ) : ℝ) * (q.primeFactors.card : ℝ) * ((q ^ k : ℕ) : ℝ)
        = ((512 * q ^ (4 * s) * q.primeFactors.card * q ^ k : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ k * q ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast hbadN
      _ = ((q ^ (k - 1) : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
  have hbad2R : 512 * ((q ^ (4 * s) : ℕ) : ℝ) * (q.primeFactors.card : ℝ)
      ≤ ((q ^ (k - 1) : ℕ) : ℝ) := by
    calc 512 * ((q ^ (4 * s) : ℕ) : ℝ) * (q.primeFactors.card : ℝ)
        = ((512 * q ^ (4 * s) * q.primeFactors.card : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((512 * q ^ (4 * s) * (q.primeFactors.card + 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_le_mul_left _ (by omega)
      _ ≤ ((q ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast hbig2
  -- cast the bad count of E4 and bound it
  have hbadE4 : 16 * (((2 * q ^ s : ℕ)) : ℝ) ^ 3
      * ((2 * (2 * q ^ s) * q.primeFactors.card * (q ^ k / 2 ^ k + 1) : ℕ) : ℝ)
      ≤ 2 * ((q ^ (k - 1) : ℕ) : ℝ) := by
    have hW : ((q ^ k / 2 ^ k : ℕ) : ℝ) ≤ ((q ^ k : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ) :=
      Nat.cast_div_le
    have hcube : (((2 * q ^ s : ℕ)) : ℝ) ^ 3 * (2 * ((2 * q ^ s : ℕ) : ℝ))
        = 32 * ((q ^ (4 * s) : ℕ) : ℝ) := by
      have h4 : ((q ^ s : ℕ) : ℝ) ^ 4 = ((q ^ (4 * s) : ℕ) : ℝ) := by
        rw [← Nat.cast_pow, ← pow_mul, Nat.mul_comm s 4]
      push_cast at h4 ⊢
      linear_combination 32 * h4
    calc 16 * (((2 * q ^ s : ℕ)) : ℝ) ^ 3
          * ((2 * (2 * q ^ s) * q.primeFactors.card * (q ^ k / 2 ^ k + 1) : ℕ) : ℝ)
        = (((2 * q ^ s : ℕ)) : ℝ) ^ 3 * (2 * ((2 * q ^ s : ℕ) : ℝ)) * 16
            * (q.primeFactors.card : ℝ) * (((q ^ k / 2 ^ k : ℕ) : ℝ) + 1) := by
          push_cast
          ring
      _ = 512 * ((q ^ (4 * s) : ℕ) : ℝ) * (q.primeFactors.card : ℝ)
            * (((q ^ k / 2 ^ k : ℕ) : ℝ) + 1) := by
          rw [hcube]
          ring
      _ ≤ 512 * ((q ^ (4 * s) : ℕ) : ℝ) * (q.primeFactors.card : ℝ)
            * (((q ^ k : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ) + 1) := by
          refine mul_le_mul_of_nonneg_left (by linarith) ?_
          positivity
      _ = 512 * ((q ^ (4 * s) : ℕ) : ℝ) * (q.primeFactors.card : ℝ)
            * (((q ^ k : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ))
          + 512 * ((q ^ (4 * s) : ℕ) : ℝ) * (q.primeFactors.card : ℝ) := by ring
      _ ≤ ((q ^ (k - 1) : ℕ) : ℝ) + ((q ^ (k - 1) : ℕ) : ℝ) := add_le_add hbad1R hbad2R
      _ = 2 * ((q ^ (k - 1) : ℕ) : ℝ) := by ring
  -- put the chain together and contradict
  have hlow : ((q ^ s : ℕ) : ℝ)
      * ((s : ℝ) * ((q.totient : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ) / 2))
      ≤ ((q ^ s : ℕ) : ℝ)
        * ∑ i ∈ Finset.range s,
            (q.totient : ℝ) * (((q ^ (k - i) - 1) / q : ℕ) : ℝ) * ((q ^ i : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hSsum (by positivity)
  have hGT4 : 4 * ∑ H' ∈ Finset.Ioc (2 * q ^ s) (2 * (2 * q ^ s)),
      ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a => IsGoodResidue q k (2 * q ^ s) a),
        ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2
      ≤ 4 * ((q : ℝ) ^ k * ((2 * q ^ s : ℕ) : ℝ) * E) :=
    mul_le_mul_of_nonneg_left hGT (by norm_num)
  -- numeric endgame: `16EYK + 4YX ≤ 8EYK + 2X` is absurd
  have hqkcast : ((q ^ k : ℕ) : ℝ) = (q : ℝ) ^ k := by push_cast; ring
  have hsφY : ((q ^ s : ℕ) : ℝ) * ((32 * (q : ℝ) * E + 8)
        * ((q ^ (k - 1) : ℕ) : ℝ) / 2)
      ≤ ((q ^ s : ℕ) : ℝ)
        * ((s : ℝ) * ((q.totient : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ) / 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := mul_le_mul_of_nonneg_right hsφ
      (by positivity : (0 : ℝ) ≤ ((q ^ (k - 1) : ℕ) : ℝ) / 2)
    calc (32 * (q : ℝ) * E + 8) * ((q ^ (k - 1) : ℕ) : ℝ) / 2
        = (32 * (q : ℝ) * E + 8) * (((q ^ (k - 1) : ℕ) : ℝ) / 2) := by ring
      _ ≤ (s : ℝ) * (q.totient : ℝ) * (((q ^ (k - 1) : ℕ) : ℝ) / 2) := this
      _ = (s : ℝ) * ((q.totient : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ) / 2) := by ring
  -- assemble everything with `nlinarith`
  have hEY : (0 : ℝ) ≤ E * ((q ^ s : ℕ) : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ) * (q : ℝ) := by
    positivity
  have hYX : ((q ^ (k - 1) : ℕ) : ℝ)
      ≤ ((q ^ s : ℕ) : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ) :=
    le_mul_of_one_le_left (by positivity) hY1
  -- chain: lower ≤ E4-LHS ≤ E4-RHS ≤ upper
  have hchain := le_trans (le_trans hsφY hlow) (le_trans hE4 (by
    refine add_le_add (le_trans ?_ hGT4) hbadE4
    exact le_of_eq rfl))
  -- expand `(2·q^s : ℕ)` and finish
  have hHcast : ((2 * q ^ s : ℕ) : ℝ) = 2 * ((q ^ s : ℕ) : ℝ) := by push_cast; ring
  rw [hHcast, hqkcast.symm, hKX] at hchain
  nlinarith [hchain, hEY, hYX, hX1, hY1, hE]

/-- **The endgame contradiction extractor** (Tao 2015 §4): for a primitive `χ` and any
candidate bound `E ≥ 0`, explicit `H` and `k` refute eq. (contra) for **every**
unimodular sample `g` and frequency `t`. -/
theorem exists_H_k_refuting_contra {q : ℕ} (hq : 1 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {E : ℝ} (hE : 0 ≤ E) :
    ∃ H k : ℕ, 1 ≤ H ∧ 1 ≤ k ∧
      ∀ (g : ℕ → ℂ) (t : ℝ), Unimodular g →
        ¬ ((1 / ((q : ℝ) ^ k))
            * ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a => IsGoodResidue q k H a),
                ((1 : ℝ) / H) * ∑ H' ∈ Finset.Ioc H (2 * H),
                  ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2
          ≤ E) := by
  rcases eq_or_lt_of_le hq with hq1 | hq2
  · -- `q = 1`
    subst hq1
    refine ⟨⌈E⌉₊ + 1, 1, by omega, le_refl 1, fun g t _ hcon => ?_⟩
    simp only [Nat.cast_one] at hcon
    have hlow := level_one_lower χ g t (H := ⌈E⌉₊ + 1) (k := 1) (by omega)
    have hEH : E < ((⌈E⌉₊ + 1 : ℕ) : ℝ) ^ 2 := by
      have h1 : E ≤ (⌈E⌉₊ : ℝ) := Nat.le_ceil E
      have h0 : (0 : ℝ) ≤ (⌈E⌉₊ : ℝ) := Nat.cast_nonneg _
      push_cast
      nlinarith
    exact absurd (le_trans hlow hcon) (not_le.mpr hEH)
  · -- `q ≥ 2`
    have hq2' : 2 ≤ q := hq2
    obtain ⟨s, hs1, hsφ⟩ : ∃ s : ℕ, 1 ≤ s ∧
        32 * (q : ℝ) * E + 8 ≤ (s : ℝ) * (q.totient : ℝ) := by
      refine ⟨⌈(32 * (q : ℝ) * E + 8) / (q.totient : ℝ)⌉₊, ?_, ?_⟩
      · have hφ0 : (0 : ℝ) < (q.totient : ℝ) := by
          exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
        exact Nat.one_le_ceil_iff.mpr (by positivity)
      · have hφ0 : (0 : ℝ) < (q.totient : ℝ) := by
          exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
        have hle := Nat.le_ceil ((32 * (q : ℝ) * E + 8) / (q.totient : ℝ))
        rw [div_le_iff₀ hφ0] at hle
        exact hle
    obtain ⟨k, hks, hbig1, hbig2⟩ : ∃ k : ℕ, s + 1 ≤ k ∧
        512 * q ^ (4 * s) * (q.primeFactors.card + 1) * q ≤ 2 ^ k ∧
        512 * q ^ (4 * s) * (q.primeFactors.card + 1) ≤ q ^ (k - 1) := by
      obtain ⟨R, hR⟩ : ∃ R, 512 * q ^ (4 * s) * (q.primeFactors.card + 1) = R :=
        ⟨_, rfl⟩
      rw [hR]
      refine ⟨max (s + 1) (R * q + 1), le_max_left _ _, ?_, ?_⟩
      · have h1 : R * q < 2 ^ (R * q) := Nat.lt_two_pow_self
        have h2 : 2 ^ (R * q) ≤ 2 ^ max (s + 1) (R * q + 1) :=
          Nat.pow_le_pow_right (by omega)
            (le_trans (by omega) (le_max_right (s + 1) (R * q + 1)))
        exact le_trans h1.le h2
      · have h0 : R * q < 2 ^ (R * q) := Nat.lt_two_pow_self
        have h1 : R ≤ R * q := Nat.le_mul_of_pos_right R (by omega)
        have h2 : 2 ^ (R * q) ≤ 2 ^ (max (s + 1) (R * q + 1) - 1) := by
          refine Nat.pow_le_pow_right (by omega) ?_
          have := le_max_right (s + 1) (R * q + 1)
          omega
        have h3 : 2 ^ (max (s + 1) (R * q + 1) - 1)
            ≤ q ^ (max (s + 1) (R * q + 1) - 1) :=
          Nat.pow_le_pow_left (by omega) _
        exact le_trans (le_trans h1 (le_trans h0.le h2)) h3
    refine ⟨2 * q ^ s, k, ?_, by omega, fun g t hu => ?_⟩
    · exact le_trans (Nat.one_le_pow _ _ (by omega))
        (Nat.le_mul_of_pos_left _ (by omega))
    · exact not_contra_of_params hq2' hχ hE hs1 hks hsφ hbig1 hbig2 hu

end MoltResearch
