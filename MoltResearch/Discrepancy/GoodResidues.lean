import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Push

/-!
# Discrepancy: good residue classes for the Maier-style decoupling (Tao 2015 §4)

Pure `ℕ`-arithmetic substrate for the Maier-style decoupling step in Tao's resolution of
the Erdős discrepancy problem (arXiv:1509.05363, §4; issue #2871, PR H prep).

Following the paper: *"Call a residue class `a (q^k)` bad if `a + m` is divisible by
`p^k` for some `p ∣ q` and `1 ≤ m ≤ 2H`, and good otherwise."*  This file formalises
that notion (`IsGoodResidue`) and the elementary facts the §4 argument consumes:

- `gcd_add_eq_of_modEq`: the gcd `(n + m, q^k)` only depends on the residue class of
  `n (mod q^k)` — so goodness data transfers from `a` to every `n ≡ a (q^k)`.
- `gcd_dvd_pow_pred_of_good`: for a good class, `(a + m, q^k) ∣ q^{k-1}` for all
  `1 ≤ m ≤ 2H` (the paper's gcd rigidity chain, first display after the definition).
- `coprime_div_gcd_of_good`: moreover `(a + m)/(a + m, q^k)` is coprime to `q`.
- `card_not_goodResidue_le`: the bad-count.  The paper bounds the number of bad `a` by
  `2H ∑_{p ∣ q} q^k p^{-k}`; we prove the explicit crude form
  `#bad ≤ 2H · ω(q) · (q^k/2^k + 1)`, which is `o(q^k)` as `k → ∞` for fixed `q, H` —
  all the consumer needs.  `le_card_goodResidue` is the complementary lower bound.

No complex numbers and no characters here: everything is gcd/factorization/counting.
-/

namespace MoltResearch

/-- Tao 2015 §4: the residue class `a (mod q^k)` is **good** (for shift range `H`) if
`a + m` is *not* divisible by `p^k` for any prime `p ∣ q` and any `1 ≤ m ≤ 2H`. -/
def IsGoodResidue (q k H a : ℕ) : Prop :=
  ∀ m ∈ Finset.Icc 1 (2 * H), ∀ p : ℕ, p.Prime → p ∣ q → ¬ p ^ k ∣ (a + m)

/-- Goodness only involves primes `p < q + a + 2H + 2`: a prime divisor of `q ≠ 0` is at
most `q`; if `q = 0` (where every prime divides `q`) a huge prime power `p^k` with
`k ≥ 1` cannot divide `a + m ≥ 1`, and for `k = 0` the small witness `p = 2` already
decides the matter.  This bounded form makes `IsGoodResidue` decidable. -/
theorem isGoodResidue_iff_bounded (q k H a : ℕ) :
    IsGoodResidue q k H a ↔
      ∀ m ∈ Finset.Icc 1 (2 * H), ∀ p ∈ Finset.range (q + a + 2 * H + 2),
        p.Prime → p ∣ q → ¬ p ^ k ∣ (a + m) := by
  constructor
  · intro h m hm p _ hp hpq
    exact h m hm p hp hpq
  · intro h m hm p hp hpq hdvd
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    by_cases hlt : p < q + a + 2 * H + 2
    · exact h m hm p (Finset.mem_range.mpr hlt) hp hpq hdvd
    · -- a huge prime divisor forces `q = 0`, and then `p ^ k ∣ a + m` forces `k = 0`
      have hq0 : q = 0 := by
        rcases Nat.eq_zero_or_pos q with h0 | hqpos
        · exact h0
        · have := Nat.le_of_dvd hqpos hpq
          omega
      have hk0 : k = 0 := by
        rcases Nat.eq_zero_or_pos k with h0 | hkpos
        · exact h0
        · have h1 : p ≤ p ^ k := Nat.le_self_pow hkpos.ne' p
          have h2 : p ^ k ≤ a + m := Nat.le_of_dvd (by omega) hdvd
          omega
      have h2 := h m hm 2 (Finset.mem_range.mpr (by omega)) Nat.prime_two
        (by rw [hq0]; exact dvd_zero 2)
      rw [hk0, pow_zero] at h2
      exact h2 (one_dvd _)

instance instDecidableIsGoodResidue (q k H a : ℕ) : Decidable (IsGoodResidue q k H a) :=
  decidable_of_iff' _ (isGoodResidue_iff_bounded q k H a)

/-- Tao 2015 §4 (gcd rigidity): `gcd (n + m) (q ^ k)` only depends on the residue class
of `n` modulo `q ^ k`.  Hence gcd facts proved for a good representative `a` transfer to
every `n ≡ a (q^k)`. -/
theorem gcd_add_eq_of_modEq {q k n a : ℕ} (h : n ≡ a [MOD q ^ k]) (m : ℕ) :
    Nat.gcd (n + m) (q ^ k) = Nat.gcd (a + m) (q ^ k) :=
  (h.add_right m).gcd_eq

/-- The `p`-adic valuation of a `k`-th power, pointwise form of `Nat.factorization_pow`. -/
private lemma factorization_pow_apply (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  simp [Nat.factorization_pow]

/-- Tao 2015 §4, gcd rigidity chain, step 1: for a good residue class `a (q^k)` and any
shift `1 ≤ m ≤ 2H`, the gcd `(a + m, q^k)` divides `q^{k-1}`.  (Paper: since `a + m` is
not divisible by `p^k` for any `p ∣ q`, every prime in the gcd appears with exponent at
most `k - 1 ≤ (k-1)·v_p(q)`.) -/
theorem gcd_dvd_pow_pred_of_good {q k H a : ℕ} (hq : q ≠ 0)
    (hgood : IsGoodResidue q k H a) {m : ℕ} (hm : m ∈ Finset.Icc 1 (2 * H)) :
    Nat.gcd (a + m) (q ^ k) ∣ q ^ (k - 1) := by
  obtain ⟨hm1, -⟩ := Finset.mem_Icc.mp hm
  have ham : a + m ≠ 0 := by omega
  have hqk : q ^ k ≠ 0 := pow_ne_zero k hq
  have hgcd0 : Nat.gcd (a + m) (q ^ k) ≠ 0 := Nat.gcd_ne_zero_left ham
  rw [← Nat.factorization_le_iff_dvd hgcd0 (pow_ne_zero _ hq), Finsupp.le_def]
  intro p
  rw [Nat.factorization_gcd ham hqk, Finsupp.inf_apply, factorization_pow_apply,
    factorization_pow_apply]
  rcases eq_or_ne (q.factorization p) 0 with h0 | h0
  · rw [h0, mul_zero, mul_zero]
    exact inf_le_right
  · -- here `p` is a prime divisor of `q`, so goodness caps the valuation of `a + m`
    have hmem : p ∈ q.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr h0
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hmem
    have hpq : p ∣ q := Nat.dvd_of_mem_primeFactors hmem
    have hlt : (a + m).factorization p < k := by
      by_contra hle
      exact hgood m hm p hp hpq ((hp.pow_dvd_iff_le_factorization ham).mpr (by omega))
    calc (a + m).factorization p ⊓ (k * q.factorization p)
        ≤ (a + m).factorization p := inf_le_left
      _ ≤ k - 1 := by omega
      _ ≤ (k - 1) * q.factorization p := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h0)

/-- Tao 2015 §4, gcd rigidity chain, step 2: for a good residue class the cofactor
`(a + m) / (a + m, q^k)` is coprime to `q`.  (For a prime `p ∣ q` the valuation
`v_p(a+m) ≤ k - 1 < k·v_p(q^k)` is *fully* absorbed into the gcd, so none of it survives
in the quotient.) -/
theorem coprime_div_gcd_of_good {q k H a : ℕ} (hq : q ≠ 0)
    (hgood : IsGoodResidue q k H a) {m : ℕ} (hm : m ∈ Finset.Icc 1 (2 * H)) :
    Nat.Coprime ((a + m) / Nat.gcd (a + m) (q ^ k)) q := by
  obtain ⟨hm1, -⟩ := Finset.mem_Icc.mp hm
  have ham : a + m ≠ 0 := by omega
  have hqk : q ^ k ≠ 0 := pow_ne_zero k hq
  have hgdvd : Nat.gcd (a + m) (q ^ k) ∣ a + m := Nat.gcd_dvd_left _ _
  have hgpos : 0 < Nat.gcd (a + m) (q ^ k) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hquot : (a + m) / Nat.gcd (a + m) (q ^ k) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (by omega) hgdvd) hgpos).ne'
  by_contra hcop
  obtain ⟨p, hp, hpdvd, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hppos : 0 < ((a + m) / Nat.gcd (a + m) (q ^ k)).factorization p :=
    hp.factorization_pos_of_dvd hquot hpdvd
  rw [Nat.factorization_div hgdvd, Finsupp.tsub_apply, Nat.factorization_gcd ham hqk,
    Finsupp.inf_apply, factorization_pow_apply] at hppos
  -- `v_p(a+m) < k ≤ k·v_p(q)`, so the inf is `v_p(a+m)` and the quotient valuation is `0`
  have hlt : (a + m).factorization p < k := by
    by_contra hle
    exact hgood m hm p hp hpq ((hp.pow_dvd_iff_le_factorization ham).mpr (by omega))
  have hkB : k ≤ k * q.factorization p :=
    Nat.le_mul_of_pos_right k (hp.factorization_pos_of_dvd hq hpq)
  rw [inf_eq_left.mpr (le_trans hlt.le hkB)] at hppos
  omega

/-- Counting helper: at most `M / d + 1` integers `a ∈ [1, M]` satisfy `d ∣ a + m`
(the multiples of `d` in the shifted window `(m, M + m]`). -/
lemma card_Icc_filter_dvd_add_le (M m d : ℕ) (hd : d ≠ 0) :
    ((Finset.Icc 1 M).filter fun a => d ∣ a + m).card ≤ M / d + 1 := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  -- inject `a ↦ a + m` into the multiples of `d` in `(m, M + m]`
  have hcard1 : ((Finset.Icc 1 M).filter fun a => d ∣ a + m).card
      ≤ ((Finset.Ioc m (M + m)).filter (d ∣ ·)).card := by
    rw [← Finset.card_image_of_injective ((Finset.Icc 1 M).filter fun a => d ∣ a + m)
      (add_left_injective m)]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨b, ⟨⟨hb1, hb2⟩, hdvd⟩, rfl⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, hdvd⟩
  -- count multiples of `d` in `(m, M + m]` by splitting `(0, M + m]` at `m`
  have hsplit : ((Finset.Ioc 0 m).filter (d ∣ ·)).card
      + ((Finset.Ioc m (M + m)).filter (d ∣ ·)).card
      = ((Finset.Ioc 0 (M + m)).filter (d ∣ ·)).card := by
    rw [← Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)),
      ← Finset.filter_union,
      Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le m) (Nat.le_add_left m M)]
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at hsplit
  -- so the count is `(M+m)/d - m/d ≤ M/d + 1`
  have harith : (M + m) / d ≤ M / d + m / d + 1 := by
    rw [Nat.add_div hdpos]
    split_ifs <;> omega
  omega

/-- Tao 2015 §4, the bad-count: *"The number of such `a` is at most
`H ∑_{p ∣ q} q^k p^{-k}`"*.  Explicit crude form: the number of **bad** residues
`a ∈ [1, q^k]` is at most `2H · ω(q) · (q^k/2^k + 1)`, since each bad `a` is caught by
one of the `2H · ω(q)` congruences `a ≡ -m (mod p^k)` and `p ≥ 2` for every prime
`p ∣ q`.  This is `o(q^k)` as `k → ∞` for fixed `q, H`. -/
theorem card_not_goodResidue_le (q k H : ℕ) (hq : q ≠ 0) :
    ((Finset.Icc 1 (q ^ k)).filter fun a => ¬ IsGoodResidue q k H a).card
      ≤ 2 * H * q.primeFactors.card * (q ^ k / 2 ^ k + 1) := by
  have hsub : ((Finset.Icc 1 (q ^ k)).filter fun a => ¬ IsGoodResidue q k H a)
      ⊆ (Finset.Icc 1 (2 * H) ×ˢ q.primeFactors).biUnion
        fun mp => (Finset.Icc 1 (q ^ k)).filter fun a => mp.2 ^ k ∣ a + mp.1 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨haIcc, hbad⟩ := ha
    unfold IsGoodResidue at hbad
    push_neg at hbad
    obtain ⟨m, hm, p, hp, hpq, hdvd⟩ := hbad
    rw [Finset.mem_biUnion]
    exact ⟨(m, p), Finset.mem_product.mpr ⟨hm, Nat.mem_primeFactors.mpr ⟨hp, hpq, hq⟩⟩,
      Finset.mem_filter.mpr ⟨haIcc, hdvd⟩⟩
  calc ((Finset.Icc 1 (q ^ k)).filter fun a => ¬ IsGoodResidue q k H a).card
      ≤ ((Finset.Icc 1 (2 * H) ×ˢ q.primeFactors).biUnion
          fun mp => (Finset.Icc 1 (q ^ k)).filter fun a => mp.2 ^ k ∣ a + mp.1).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ mp ∈ Finset.Icc 1 (2 * H) ×ˢ q.primeFactors,
          ((Finset.Icc 1 (q ^ k)).filter fun a => mp.2 ^ k ∣ a + mp.1).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _mp ∈ Finset.Icc 1 (2 * H) ×ˢ q.primeFactors, (q ^ k / 2 ^ k + 1) := by
        apply Finset.sum_le_sum
        intro mp hmp
        rw [Finset.mem_product] at hmp
        have hp : mp.2.Prime := Nat.prime_of_mem_primeFactors hmp.2
        have h1 : ((Finset.Icc 1 (q ^ k)).filter fun a => mp.2 ^ k ∣ a + mp.1).card
            ≤ q ^ k / mp.2 ^ k + 1 :=
          card_Icc_filter_dvd_add_le _ _ _ (pow_ne_zero k hp.pos.ne')
        have h2 : q ^ k / mp.2 ^ k ≤ q ^ k / 2 ^ k :=
          Nat.div_le_div_left (Nat.pow_le_pow_left hp.two_le k) (Nat.two_pow_pos k)
        omega
    _ = 2 * H * q.primeFactors.card * (q ^ k / 2 ^ k + 1) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_product, Nat.card_Icc,
          Nat.add_sub_cancel]

/-- Complementary count: at least `q^k - 2H·ω(q)·(q^k/2^k + 1)` residues in `[1, q^k]`
are good (Tao 2015 §4: "most" residue classes are good once `k` is large). -/
theorem le_card_goodResidue (q k H : ℕ) (hq : q ≠ 0) :
    q ^ k - 2 * H * q.primeFactors.card * (q ^ k / 2 ^ k + 1)
      ≤ ((Finset.Icc 1 (q ^ k)).filter fun a => IsGoodResidue q k H a).card := by
  have hpart : ((Finset.Icc 1 (q ^ k)).filter fun a => IsGoodResidue q k H a).card
      + ((Finset.Icc 1 (q ^ k)).filter fun a => ¬ IsGoodResidue q k H a).card
      = (Finset.Icc 1 (q ^ k)).card :=
    Finset.card_filter_add_card_filter_not fun a => IsGoodResidue q k H a
  have hbad := card_not_goodResidue_le q k H hq
  have hcard : (Finset.Icc 1 (q ^ k)).card = q ^ k := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
  omega

end MoltResearch
