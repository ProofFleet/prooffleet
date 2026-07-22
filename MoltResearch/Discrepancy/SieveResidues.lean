import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Real.Basic

/-!
# Discrepancy: sieve residue counts

Track S of the EDP-unconditional campaign (`Problems/tao2015_derivation_c.md`,
issue #3004): the local data of the twin-type sift `n ↦ n(s−n)`.

`sieveRootCard s d` counts the residues `x ∈ [0, d)` with `d ∣ x(s−x)` (as
integers) — the residue classes the Selberg sieve removes. This unit gives the
local theory: congruence invariance of the sift condition, the value at primes
(`1` if `p ∣ s`, else `2`), multiplicativity across coprime moduli (CRT), and
the product formula over the prime factors of a squarefree modulus.

The count is `Finset.range`-based with an integer divisibility condition, so
no `ZMod`-`Fintype` instances are ever needed — moduli can range over bound
variables in sums and products.
-/

namespace MoltResearch

open Finset

/-- The sieve's local root count: residues `x ∈ [0,d)` with `d ∣ x(s−x)`. -/
def sieveRootCard (s d : ℕ) : ℕ :=
  ((Finset.range d).filter
    (fun x : ℕ => (d : ℤ) ∣ (x : ℤ) * ((s : ℤ) - (x : ℤ)))).card

/-- The sift condition only depends on the residue class. -/
theorem sieve_dvd_congr {d : ℕ} {x y : ℤ} (h : x ≡ y [ZMOD (d : ℤ)])
    (s : ℕ) : (d : ℤ) ∣ x * ((s : ℤ) - x) ↔ (d : ℤ) ∣ y * ((s : ℤ) - y) := by
  have hcong : x * ((s : ℤ) - x) ≡ y * ((s : ℤ) - y) [ZMOD (d : ℤ)] :=
    Int.ModEq.mul h ((Int.ModEq.refl (s : ℤ)).sub h)
  constructor
  · intro hdvd
    exact (Int.modEq_zero_iff_dvd).mp
      ((hcong.symm.trans ((Int.modEq_zero_iff_dvd).mpr hdvd)))
  · intro hdvd
    exact (Int.modEq_zero_iff_dvd).mp
      (hcong.trans ((Int.modEq_zero_iff_dvd).mpr hdvd))

/-- Modulus 1 admits exactly one residue. -/
theorem sieveRootCard_one (s : ℕ) : sieveRootCard s 1 = 1 := by
  have h : (Finset.range 1).filter
      (fun x : ℕ => ((1 : ℕ) : ℤ) ∣ (x : ℤ) * ((s : ℤ) - (x : ℤ)))
      = Finset.range 1 :=
    Finset.filter_true_of_mem fun x _ => by
      exact_mod_cast one_dvd ((x : ℤ) * ((s : ℤ) - (x : ℤ)))
  rw [sieveRootCard, h, Finset.card_range]

/-- **The prime value**: at a prime `p`, the sift removes one residue class if
`p ∣ s` (only `x ≡ 0`) and two otherwise (`x ≡ 0` and `x ≡ s`). -/
theorem sieveRootCard_prime {p : ℕ} (hp : p.Prime) (s : ℕ) :
    sieveRootCard s p = if p ∣ s then 1 else 2 := by
  classical
  have hp0 : 0 < p := hp.pos
  have hset : (Finset.range p).filter
      (fun x : ℕ => (p : ℤ) ∣ (x : ℤ) * ((s : ℤ) - (x : ℤ)))
      = {0, s % p} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hxlt, hdvd⟩
      rcases (Int.Prime.dvd_mul' hp hdvd) with hx | hsx
      · left
        have hx' : p ∣ x := by exact_mod_cast hx
        exact Nat.eq_zero_of_dvd_of_lt hx' hxlt
      · right
        have hmod : (x : ℤ) ≡ (s : ℤ) [ZMOD (p : ℤ)] :=
          Int.modEq_iff_dvd.mpr hsx
        have hmod' : x ≡ s [MOD p] := Int.natCast_modEq_iff.mp hmod
        have h1 : x % p = s % p := hmod'
        rw [Nat.mod_eq_of_lt hxlt] at h1
        exact h1
    · intro hx
      rcases hx with h0 | hsp
      · subst h0
        refine ⟨hp0, ?_⟩
        simp only [Nat.cast_zero, zero_mul, dvd_zero]
      · subst hsp
        refine ⟨Nat.mod_lt s hp0, ?_⟩
        have h2 : ((s % p : ℕ) : ℤ) ≡ (s : ℤ) [ZMOD (p : ℤ)] :=
          Int.natCast_modEq_iff.mpr (Nat.mod_modEq s p)
        have hsx : (p : ℤ) ∣ (s : ℤ) - ((s % p : ℕ) : ℤ) :=
          Int.modEq_iff_dvd.mp h2
        exact Dvd.dvd.mul_left hsx _
  rw [sieveRootCard, hset]
  by_cases hps : p ∣ s
  · rw [if_pos hps]
    have h0 : s % p = 0 := Nat.mod_eq_zero_of_dvd hps
    rw [h0, Finset.insert_eq_self.mpr (Finset.mem_singleton_self 0),
      Finset.card_singleton]
  · rw [if_neg hps]
    have h0 : s % p ≠ 0 := fun hc => hps (Nat.dvd_of_mod_eq_zero hc)
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact fun hc => h0 hc.symm), Finset.card_singleton]

/-- **CRT multiplicativity** of the root count across coprime moduli. -/
theorem sieveRootCard_mul {d₁ d₂ : ℕ} (hcop : Nat.Coprime d₁ d₂) (s : ℕ) :
    sieveRootCard s (d₁ * d₂) = sieveRootCard s d₁ * sieveRootCard s d₂ := by
  classical
  rcases Nat.eq_zero_or_pos d₁ with h1 | h1
  · subst h1
    rw [zero_mul, sieveRootCard, Finset.range_zero,
      Finset.filter_empty, Finset.card_empty, zero_mul]
  rcases Nat.eq_zero_or_pos d₂ with h2 | h2
  · subst h2
    rw [mul_zero, sieveRootCard, Finset.range_zero,
      Finset.filter_empty, Finset.card_empty, mul_zero]
  have hd12 : 0 < d₁ * d₂ := Nat.mul_pos h1 h2
  have hsplit : ∀ z : ℤ, ((d₁ * d₂ : ℕ) : ℤ) ∣ z ↔ (d₁ : ℤ) ∣ z ∧ (d₂ : ℤ) ∣ z := by
    intro z
    constructor
    · intro h
      rw [Nat.cast_mul] at h
      exact ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩
    · rintro ⟨ha, hb⟩
      rw [Nat.cast_mul]
      exact (Nat.isCoprime_iff_coprime.mpr hcop).mul_dvd ha hb
  -- the congruence-transfer helper
  have htrans : ∀ (d : ℕ) (x : ℕ), (d : ℤ) ∣ (x : ℤ) * ((s : ℤ) - x)
      ↔ (d : ℤ) ∣ ((x % d : ℕ) : ℤ) * ((s : ℤ) - ((x % d : ℕ) : ℤ)) := by
    intro d x
    refine sieve_dvd_congr ?_ s
    rw [Int.natCast_modEq_iff]
    exact (Nat.mod_modEq x d).symm
  rw [sieveRootCard, sieveRootCard, sieveRootCard, ← Finset.card_product]
  refine Finset.card_bij (fun x _ => (x % d₁, x % d₂)) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨hxlt, hdvd⟩ := hx
    rw [hsplit] at hdvd
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_range, Finset.mem_range]
    exact ⟨⟨Nat.mod_lt x h1, ((htrans d₁ x).mp hdvd.1)⟩,
      ⟨Nat.mod_lt x h2, ((htrans d₂ x).mp hdvd.2)⟩⟩
  · intro x hx y hy heq
    rw [Finset.mem_filter, Finset.mem_range] at hx hy
    have he1 : x % d₁ = y % d₁ := congrArg Prod.fst heq
    have he2 : x % d₂ = y % d₂ := congrArg Prod.snd heq
    have hmod : x ≡ y [MOD d₁ * d₂] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨he1, he2⟩
    rw [Nat.ModEq, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at hmod
    exact hmod
  · intro y hy
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_range, Finset.mem_range] at hy
    obtain ⟨⟨hy1lt, hy1⟩, ⟨hy2lt, hy2⟩⟩ := hy
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop y.1 y.2
    refine ⟨k % (d₁ * d₂), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt k hd12, ?_⟩
      rw [← htrans (d₁ * d₂) k, hsplit]
      constructor
      · rw [htrans d₁ k]
        have hkk : k % d₁ = y.1 := by
          have := hk1
          rw [Nat.ModEq, Nat.mod_eq_of_lt hy1lt] at this
          exact this
        rw [hkk]
        exact hy1
      · rw [htrans d₂ k]
        have hkk : k % d₂ = y.2 := by
          have := hk2
          rw [Nat.ModEq, Nat.mod_eq_of_lt hy2lt] at this
          exact this
        rw [hkk]
        exact hy2
    · have hm1 : k % (d₁ * d₂) % d₁ = y.1 := by
        rw [Nat.mod_mod_of_dvd k (dvd_mul_right d₁ d₂)]
        have := hk1
        rw [Nat.ModEq, Nat.mod_eq_of_lt hy1lt] at this
        exact this
      have hm2 : k % (d₁ * d₂) % d₂ = y.2 := by
        rw [Nat.mod_mod_of_dvd k (dvd_mul_left d₂ d₁)]
        have := hk2
        rw [Nat.ModEq, Nat.mod_eq_of_lt hy2lt] at this
        exact this
      show (k % (d₁ * d₂) % d₁, k % (d₁ * d₂) % d₂) = y
      rw [hm1, hm2]

/-- **The product formula** over the prime factors of a squarefree modulus. -/
theorem sieveRootCard_squarefree (s : ℕ) :
    ∀ d : ℕ, Squarefree d →
      sieveRootCard s d = ∏ p ∈ d.primeFactors, sieveRootCard s p := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    rcases eq_or_ne d 1 with h1 | h1
    · subst h1
      rw [sieveRootCard_one, Nat.primeFactors_one, Finset.prod_empty]
    · have hd0 : d ≠ 0 := hd.ne_zero
      have hp := Nat.minFac_prime h1
      set q := d.minFac with hq_def
      obtain ⟨d', hd'⟩ := d.minFac_dvd
      rw [← hq_def] at hd'
      have hd'0 : d' ≠ 0 := by
        intro hc
        rw [hc, mul_zero] at hd'
        exact hd0 hd'
      have hd'lt : d' < d := by
        rw [hd']
        have h2 := hp.two_le
        have h3 : 0 < d' := Nat.pos_of_ne_zero hd'0
        calc d' = 1 * d' := (one_mul d').symm
          _ < q * d' := Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl h3
      have hsq' : Squarefree d' :=
        Squarefree.squarefree_of_dvd ⟨q, by rw [hd']; ring⟩ hd
      have hpd' : ¬ q ∣ d' := by
        intro hc
        obtain ⟨e, he⟩ := hc
        have hpp : q * q ∣ d := ⟨e, by rw [hd', he]; ring⟩
        have hunit := hd q hpp
        rw [Nat.isUnit_iff] at hunit
        exact hp.one_lt.ne' hunit
      have hcop : Nat.Coprime q d' :=
        (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd'
      have hmem : q ∉ d'.primeFactors := fun hc =>
        hpd' (Nat.dvd_of_mem_primeFactors hc)
      have hpf' : (q * d').primeFactors = insert q d'.primeFactors := by
        rw [Nat.primeFactors_mul (hp.pos.ne') hd'0,
          Nat.Prime.primeFactors hp, Finset.singleton_union]
      rw [hd', sieveRootCard_mul hcop, ih d' hd'lt hsq', hpf',
        Finset.prod_insert hmem]

/-- Single residue class in `(a, b]`, two-sided: within 1 of `(b−a)/d`. -/
theorem abs_card_Ioc_modEq_sub_le {d a b : ℕ} (hd : 0 < d) (hab : a ≤ b)
    (v : ℕ) :
    |(({x ∈ Finset.Ioc a b | x ≡ v [MOD d]}).card : ℝ)
      - ((b : ℝ) - a) / d| ≤ 1 := by
  have hcard := Nat.Ioc_filter_modEq_card a b hd v
  have hdQ : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hQ : |((({x ∈ Finset.Ioc a b | x ≡ v [MOD d]}).card : ℚ))
      - ((b : ℚ) - a) / d| ≤ 1 := by
    have hcardQ : ((({x ∈ Finset.Ioc a b | x ≡ v [MOD d]}).card : ℚ))
        = ((max (⌊((b : ℚ) - v) / d⌋ - ⌊((a : ℚ) - v) / d⌋) 0 : ℤ) : ℚ) := by
      exact_mod_cast hcard
    have hb1 : ((b : ℚ) - v) / d - 1 < (⌊((b : ℚ) - v) / d⌋ : ℚ) :=
      Int.sub_one_lt_floor _
    have hb2 : ((⌊((b : ℚ) - v) / d⌋ : ℚ)) ≤ ((b : ℚ) - v) / d :=
      Int.floor_le _
    have ha1 : ((a : ℚ) - v) / d - 1 < (⌊((a : ℚ) - v) / d⌋ : ℚ) :=
      Int.sub_one_lt_floor _
    have ha2 : ((⌊((a : ℚ) - v) / d⌋ : ℚ)) ≤ ((a : ℚ) - v) / d :=
      Int.floor_le _
    have hlen : ((b : ℚ) - v) / d - ((a : ℚ) - v) / d = ((b : ℚ) - a) / d := by
      field_simp
      ring
    rw [hcardQ]
    rcases le_or_gt (⌊((b : ℚ) - v) / d⌋ - ⌊((a : ℚ) - v) / d⌋) 0 with hle | hgt
    · rw [max_eq_right hle]
      have hfl0 : ⌊((b : ℚ) - v) / d⌋ ≤ ⌊((a : ℚ) - v) / d⌋ := by omega
      have hfl : ((⌊((b : ℚ) - v) / d⌋ : ℚ))
          ≤ ((⌊((a : ℚ) - v) / d⌋ : ℚ)) := by exact_mod_cast hfl0
      have hnn : (0 : ℚ) ≤ ((b : ℚ) - a) / d := by
        have hab' : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hab
        have h2 : (0 : ℚ) ≤ (b : ℚ) - a := by linarith
        positivity
      have hsmall : ((b : ℚ) - a) / d ≤ 1 := by
        linarith [hlen]
      rw [Int.cast_zero, abs_le]
      constructor <;> linarith
    · rw [max_eq_left hgt.le, abs_le]
      have hcast : ((⌊((b : ℚ) - v) / d⌋ - ⌊((a : ℚ) - v) / d⌋ : ℤ) : ℚ)
          = ((⌊((b : ℚ) - v) / d⌋ : ℚ)) - ((⌊((a : ℚ) - v) / d⌋ : ℚ)) := by
        push_cast
        ring
      rw [hcast]
      constructor <;> linarith [hlen]
  have hcastR : ((({x ∈ Finset.Ioc a b | x ≡ v [MOD d]}).card : ℝ))
      - ((b : ℝ) - a) / d
      = ((((({x ∈ Finset.Ioc a b | x ≡ v [MOD d]}).card : ℚ))
        - ((b : ℚ) - a) / d : ℚ) : ℝ) := by
    push_cast
    ring
  rw [hcastR, ← Rat.cast_abs]
  exact_mod_cast hQ

/-- **The sifted interval count, two-sided**: the number of `n ∈ (a, b]` with
`d ∣ n(s−n)` is `sieveRootCard s d · (b−a)/d` up to `sieveRootCard s d`. -/
theorem abs_card_sift_sub_le {d a b : ℕ} (hd : 0 < d) (hab : a ≤ b) (s : ℕ) :
    |((((Finset.Ioc a b).filter
        (fun n : ℕ => (d : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)))).card : ℝ)
      - (sieveRootCard s d : ℝ) * (((b : ℝ) - a) / d))|
      ≤ sieveRootCard s d := by
  classical
  set RootF : Finset ℕ := (Finset.range d).filter
    (fun x : ℕ => (d : ℤ) ∣ (x : ℤ) * ((s : ℤ) - (x : ℤ))) with hRootF_def
  have hRcard : RootF.card = sieveRootCard s d := rfl
  -- fiber the sifted set over the residue class
  have hmaps : ∀ n ∈ (Finset.Ioc a b).filter
      (fun n : ℕ => (d : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ))), n % d ∈ RootF := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [hRootF_def, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt n hd, ?_⟩
    have hcong : ((n : ℤ)) ≡ ((n % d : ℕ) : ℤ) [ZMOD (d : ℤ)] :=
      Int.natCast_modEq_iff.mpr (Nat.mod_modEq n d).symm
    exact (sieve_dvd_congr hcong s).mp hn.2
  have hmaps' : Set.MapsTo (fun n => n % d)
      ↑((Finset.Ioc a b).filter
        (fun n : ℕ => (d : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)))) ↑RootF :=
    fun n hn => hmaps n hn
  have hfiber := Finset.card_eq_sum_card_fiberwise hmaps'
  -- each fiber is a single residue class
  have hfibeq : ∀ x ∈ RootF,
      (((Finset.Ioc a b).filter
          (fun n : ℕ => (d : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)))).filter
        (fun n => n % d = x)).card
        = ({n ∈ Finset.Ioc a b | n ≡ x [MOD d]}).card := by
    intro x hx
    rw [hRootF_def, Finset.mem_filter, Finset.mem_range] at hx
    congr 1
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun n _ => ?_
    constructor
    · rintro ⟨hdvd, hmod⟩
      show n % d = x % d
      rw [Nat.mod_eq_of_lt hx.1]
      exact hmod
    · intro hmod
      have hmod' : n % d = x := by
        have h1 : n % d = x % d := hmod
        rwa [Nat.mod_eq_of_lt hx.1] at h1
      refine ⟨?_, hmod'⟩
      have hcong : ((x : ℕ) : ℤ) ≡ ((n : ℕ) : ℤ) [ZMOD (d : ℤ)] :=
        Int.natCast_modEq_iff.mpr (Nat.ModEq.symm hmod)
      exact (sieve_dvd_congr hcong s).mp hx.2
  -- pass to reals and apply the per-class bound
  have hsum : ((((Finset.Ioc a b).filter
      (fun n : ℕ => (d : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)))).card : ℝ))
      = ∑ x ∈ RootF,
        ((({n ∈ Finset.Ioc a b | n ≡ x [MOD d]}).card : ℝ)) := by
    rw [hfiber]
    push_cast
    exact Finset.sum_congr rfl fun x hx => by rw [hfibeq x hx]
  have hconst : (sieveRootCard s d : ℝ) * (((b : ℝ) - a) / d)
      = ∑ _x ∈ RootF, (((b : ℝ) - a) / d) := by
    rw [Finset.sum_const, ← hRcard, nsmul_eq_mul]
  rw [hsum, hconst, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ x ∈ RootF,
      |((({n ∈ Finset.Ioc a b | n ≡ x [MOD d]}).card : ℝ))
        - (((b : ℝ) - a) / d)|
      ≤ ∑ _x ∈ RootF, (1 : ℝ) :=
        Finset.sum_le_sum fun x _ => abs_card_Ioc_modEq_sub_le hd hab x
    _ = (RootF.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (sieveRootCard s d : ℝ) := by rw [hRcard]

end MoltResearch
