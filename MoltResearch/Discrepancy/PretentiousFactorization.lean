import MoltResearch.Discrepancy.CMOfPrimes
import MoltResearch.Discrepancy.PretentiousDist
import MoltResearch.Discrepancy.GoodResidues
import MoltResearch.Discrepancy.ArchimedeanTaylor
import MoltResearch.Discrepancy.CharTwistCompose
import MoltResearch.Discrepancy.CharTwistedSingularSeries
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Discrepancy: the pretentious factorization `g = χ̃ · n^{i𝐭} · h` (Tao 2015 §4)

Language-layer module for the generalized Borwein–Choi–Coons analysis of Tao 2015
(arXiv:1509.05363, §4; issue #2871).  The pretense bound (paper eq. `(gh)`) says a
completely multiplicative unimodular sample `g` pretends to be the character twist
`n ↦ χ(n)·n^{i𝐭}`; §4 formalises this with the factorisation (paper eq. `(dos)`)

`g(n) = χ̃(n) · n^{i𝐭} · h(n)`,

where both factors are the completely multiplicative unimodular extensions
(`cmOfPrimes`) of the prime data

* `χ̃(p) = χ(p)` for `p ∤ q` and `χ̃(p) = g(p)·p^{−i𝐭}` for `p ∣ q` (`chiTilde`), and
* `h(p) = g(p)·conj(χ(p))·p^{−i𝐭}` for `p ∤ q` and `h(p) = 1` for `p ∣ q` (`hPart`).

Contents:

* `CompletelyMultiplicativeC.eq_prod_factorization` /
  `CompletelyMultiplicativeC.eq_of_forall_prime` — a guarded completely multiplicative
  sequence with value `1` at `1` is determined by its prime values (via
  `Nat.multiplicative_factorization`); the substrate for every identity below.
* `chiTilde`, `hPart` and their basic API (completely multiplicative, value `1` at `1`,
  prime evaluation, unimodularity given `Unimodular g`).
* `chiTilde_mul_cpow_mul_hPart` — the factorisation identity `(dos)` itself, checked at
  primes and propagated by complete multiplicativity.
* `pretentiousDistSq_hPart_le` — the pretense transfer `(gh) ⇒ (gap)`: the distance from
  `h` to the constant `1` is at most the distance from `g` to the twist
  `charTwist q χ 𝐭`, prime by prime.
* `hPart_eq_one_of_primes_dvd` — `h ≡ 1` on `q`-smooth numbers (used for the principal
  character in the equidistribution step).
* `chiTilde_apply_of_coprime` and `chiTilde_congr_of_good` — the χ̃-rigidity chain: on a
  good residue class `a (q^k)` (`IsGoodResidue`), the value `χ̃(n+m)` for
  `n ≡ a (q^k)` and `1 ≤ m ≤ 2H` depends only on `a + m`, via the paper's gcd splitting
  `χ̃(n+m) = χ̃((a+m, q^k)) · χ((n+m)/(a+m, q^k))` and periodicity of `χ`.

Conventions: the archimedean factor `p^{−i𝐭}` is spelled
`(p : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ))` so that `norm_natCast_cpow_I_mul` and
`conj_natCast_cpow_I_mul` apply verbatim; junk values follow Mathlib (`(0:ℂ)^s = 0` for
`s ≠ 0`, `cmOfPrimes F 0 = 1`), and all identities carry the `n ≠ 0` guards of the
guarded `CompletelyMultiplicativeC`.
-/

namespace MoltResearch

/-! ### Completely multiplicative sequences are determined by their prime values -/

namespace CompletelyMultiplicativeC

variable {g h : ℕ → ℂ}

/-- Prime-power (indeed any-base) evaluation of a guarded completely multiplicative
sequence with `g 1 = 1`: iterating the guarded law gives `g (p^k) = g(p)^k` for `p ≠ 0`. -/
theorem map_pow (hg : CompletelyMultiplicativeC g) (hg1 : g 1 = 1) {p : ℕ} (hp : p ≠ 0)
    (k : ℕ) : g (p ^ k) = g p ^ k := by
  induction k with
  | zero => simpa using hg1
  | succ k ih => rw [pow_succ, hg (p ^ k) p (pow_ne_zero k hp) hp, ih, pow_succ]

/-- **A completely multiplicative sequence is determined by its prime values**
(Tao 2015 §4 substrate): for `n ≠ 0`,

`g n = ∏_{p^k ∥ n} g(p)^k`.

The guarded law upgrades to multiplicativity on coprime pairs (the zero cases force the
other factor to be `1`), and `Nat.multiplicative_factorization` plus `map_pow` finish. -/
theorem eq_prod_factorization (hg : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    {n : ℕ} (hn : n ≠ 0) :
    g n = n.factorization.prod fun p k => g p ^ k := by
  have h_mult : ∀ x y : ℕ, Nat.Coprime x y → g (x * y) = g x * g y := by
    intro x y hxy
    rcases eq_or_ne x 0 with rfl | hx
    · have hy1 : y = 1 := (Nat.coprime_zero_left y).mp hxy
      subst hy1
      simp [hg1]
    rcases eq_or_ne y 0 with rfl | hy
    · have hx1 : x = 1 := (Nat.coprime_zero_right x).mp hxy
      subst hx1
      simp [hg1]
    · exact hg x y hx hy
  rw [Nat.multiplicative_factorization g h_mult hg1 hn]
  refine Finsupp.prod_congr fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [← Nat.support_factorization])
  exact hg.map_pow hg1 hpp.pos.ne' _

/-- Two guarded completely multiplicative sequences with value `1` at `1` that agree at
all primes agree at every `n ≠ 0`. -/
theorem eq_of_forall_prime (hg : CompletelyMultiplicativeC g)
    (hh : CompletelyMultiplicativeC h) (hg1 : g 1 = 1) (hh1 : h 1 = 1)
    (hgh : ∀ p : ℕ, p.Prime → g p = h p) {n : ℕ} (hn : n ≠ 0) : g n = h n := by
  rw [hg.eq_prod_factorization hg1 hn, hh.eq_prod_factorization hh1 hn]
  refine Finsupp.prod_congr fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [← Nat.support_factorization])
  rw [hgh p hpp]

end CompletelyMultiplicativeC

/-! ### The archimedean factor `n ↦ n^{s}` -/

/-- The archimedean power `n ↦ (n : ℂ)^s` is guarded completely multiplicative (indeed
the guards are not even needed: `Complex.mul_cpow_ofReal_nonneg` covers `0`). -/
theorem completelyMultiplicativeC_natCast_cpow (s : ℂ) :
    CompletelyMultiplicativeC fun n : ℕ => (n : ℂ) ^ s := by
  intro a b _ _
  show ((a * b : ℕ) : ℂ) ^ s = ((a : ℕ) : ℂ) ^ s * ((b : ℕ) : ℂ) ^ s
  have h := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ (a : ℝ))
    (Nat.cast_nonneg b : (0 : ℝ) ≤ (b : ℝ)) s
  push_cast at h ⊢
  exact h

/-- Conjugating the archimedean twist flips the frequency: for `n ≠ 0`,

`conj (n^{i𝐭}) = n^{i(−𝐭)}`.

Companion to `natCast_cpow_mul_conj_cpow`; stated with the exponent normal form
`Complex.I * ((-t : ℝ) : ℂ)` used by `chiTilde`/`hPart`. -/
theorem conj_natCast_cpow_I_mul {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (starRingEnd ℂ) (((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)))
      = ((n : ℕ) : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ)) := by
  have hn0 : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hlog : (starRingEnd ℂ) (Complex.log ((n : ℕ) : ℂ)) = Complex.log ((n : ℕ) : ℂ) := by
    rw [← Complex.natCast_log, Complex.conj_ofReal]
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_conj,
    map_mul, hlog, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

/-! ### The §4 factorization `g = χ̃ · n^{i𝐭} · h` (paper eq. (dos)) -/

/-- Tao 2015 §4, eq. `(dos)`: the character-like factor `χ̃` — the completely
multiplicative extension of `χ̃(p) = χ(p)` for `p ∤ q`, `χ̃(p) = g(p)·p^{−i𝐭}` for
`p ∣ q`.  This is the generalized Borwein–Choi–Coons object whose medium-length sums
§4 bounds from below. -/
noncomputable def chiTilde (g : ℕ → ℂ) (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ℕ → ℂ :=
  cmOfPrimes fun p =>
    if p ∣ q then g p * (p : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ)) else χ (p : ZMod q)

/-- Tao 2015 §4, eq. `(dos)`: the pretending-to-`1` factor `h` — the completely
multiplicative extension of `h(p) = g(p)·conj(χ(p))·p^{−i𝐭}` for `p ∤ q`, `h(p) = 1`
for `p ∣ q`. -/
noncomputable def hPart (g : ℕ → ℂ) (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ℕ → ℂ :=
  cmOfPrimes fun p =>
    if p ∣ q then 1
    else g p * (starRingEnd ℂ) (χ (p : ZMod q)) * (p : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ))

variable {g : ℕ → ℂ} {q : ℕ} {χ : DirichletCharacter ℂ q} {t : ℝ}

/-- `χ̃` is (guarded) completely multiplicative. -/
theorem chiTilde_completelyMultiplicativeC :
    CompletelyMultiplicativeC (chiTilde g q χ t) :=
  cmOfPrimes_completelyMultiplicativeC _

/-- `h` is (guarded) completely multiplicative. -/
theorem hPart_completelyMultiplicativeC :
    CompletelyMultiplicativeC (hPart g q χ t) :=
  cmOfPrimes_completelyMultiplicativeC _

/-- `χ̃(1) = 1`. -/
@[simp] theorem chiTilde_one : chiTilde g q χ t 1 = 1 :=
  cmOfPrimes_one _

/-- `h(1) = 1`. -/
@[simp] theorem hPart_one : hPart g q χ t 1 = 1 :=
  cmOfPrimes_one _

/-- Prime evaluation of `χ̃` (the defining prime data). -/
theorem chiTilde_apply_prime {p : ℕ} (hp : p.Prime) :
    chiTilde g q χ t p
      = if p ∣ q then g p * (p : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ)) else χ (p : ZMod q) :=
  cmOfPrimes_apply_prime _ hp

/-- Prime evaluation of `h` (the defining prime data). -/
theorem hPart_apply_prime {p : ℕ} (hp : p.Prime) :
    hPart g q χ t p
      = if p ∣ q then 1
        else g p * (starRingEnd ℂ) (χ (p : ZMod q))
          * (p : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ)) :=
  cmOfPrimes_apply_prime _ hp

/-- `χ̃` has magnitude `1` (Tao 2015 §4): at `p ∣ q` this is unimodularity of `g` and of
the archimedean twist; at `p ∤ q` the prime is a unit mod `q`, where Dirichlet-character
values have norm `1`. -/
theorem chiTilde_unimodular (hu : Unimodular g) : Unimodular (chiTilde g q χ t) := by
  have hF : ∀ p : ℕ, p.Prime →
      ‖if p ∣ q then g p * (p : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ)) else χ (p : ZMod q)‖
        = 1 := by
    intro p hp
    by_cases hpq : p ∣ q
    · rw [if_pos hpq, norm_mul, hu p, one_mul]
      exact norm_natCast_cpow_I_mul hp.pos.ne' (-t)
    · rw [if_neg hpq]
      have hunit : IsUnit ((p : ℕ) : ZMod q) := ZMod.isUnit_prime_of_not_dvd hp hpq
      have h := χ.unit_norm_eq_one hunit.unit
      rwa [hunit.unit_spec] at h
  exact cmOfPrimes_unimodular hF

/-- `h` has magnitude `1` (Tao 2015 §4). -/
theorem hPart_unimodular (hu : Unimodular g) : Unimodular (hPart g q χ t) := by
  have hF : ∀ p : ℕ, p.Prime →
      ‖if p ∣ q then (1 : ℂ)
        else g p * (starRingEnd ℂ) (χ (p : ZMod q))
          * (p : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ))‖ = 1 := by
    intro p hp
    by_cases hpq : p ∣ q
    · rw [if_pos hpq, norm_one]
    · rw [if_neg hpq]
      have hunit : IsUnit ((p : ℕ) : ZMod q) := ZMod.isUnit_prime_of_not_dvd hp hpq
      have hχ : ‖χ ((p : ℕ) : ZMod q)‖ = 1 := by
        have h := χ.unit_norm_eq_one hunit.unit
        rwa [hunit.unit_spec] at h
      rw [norm_mul, norm_mul, hu p, RCLike.norm_conj, hχ,
        norm_natCast_cpow_I_mul hp.pos.ne' (-t)]
      norm_num
  exact cmOfPrimes_unimodular hF

/-- **The factorization identity** (Tao 2015 §4, eq. `(dos)`): for a completely
multiplicative unimodular `g` and every `n ≠ 0`,

`χ̃(n) · n^{i𝐭} · h(n) = g(n)`.

All three factors are completely multiplicative with value `1` at `1`, so it suffices to
check at primes: for `p ∤ q` the character values cancel (`χ(p)·conj(χ(p)) = 1` on
units) and the archimedean twists cancel (`p^{−i𝐭}·p^{i𝐭} = 1`); for `p ∣ q` only the
archimedean cancellation is needed. -/
theorem chiTilde_mul_cpow_mul_hPart (hg : CompletelyMultiplicativeC g)
    (hu : Unimodular g) {n : ℕ} (hn : n ≠ 0) :
    chiTilde g q χ t n * (n : ℂ) ^ (Complex.I * (t : ℂ)) * hPart g q χ t n = g n := by
  have hg1 : g 1 = 1 := hg.map_one_of_unimodular hu
  have hcm : CompletelyMultiplicativeC
      fun n : ℕ => chiTilde g q χ t n * (n : ℂ) ^ (Complex.I * (t : ℂ)) * hPart g q χ t n :=
    (chiTilde_completelyMultiplicativeC.mul
      (completelyMultiplicativeC_natCast_cpow (Complex.I * (t : ℂ)))).mul
      hPart_completelyMultiplicativeC
  have hF1 : chiTilde g q χ t 1 * ((1 : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))
      * hPart g q χ t 1 = 1 := by
    rw [chiTilde_one, hPart_one, mul_one, one_mul, Nat.cast_one, Complex.one_cpow]
  have hprime : ∀ p : ℕ, p.Prime →
      chiTilde g q χ t p * (p : ℂ) ^ (Complex.I * (t : ℂ)) * hPart g q χ t p = g p := by
    intro p hp
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
    have hsum : Complex.I * ((-t : ℝ) : ℂ) + Complex.I * (t : ℂ) = 0 := by
      push_cast
      ring
    have hcpow : (p : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ)) * (p : ℂ) ^ (Complex.I * (t : ℂ))
        = 1 := by
      rw [← Complex.cpow_add _ _ hp0, hsum, Complex.cpow_zero]
    rw [chiTilde_apply_prime hp, hPart_apply_prime hp]
    by_cases hpq : p ∣ q
    · rw [if_pos hpq, if_pos hpq, mul_one, mul_assoc, hcpow, mul_one]
    · rw [if_neg hpq, if_neg hpq]
      have hunit : IsUnit ((p : ℕ) : ZMod q) := ZMod.isUnit_prime_of_not_dvd hp hpq
      have hχ : ‖χ ((p : ℕ) : ZMod q)‖ = 1 := by
        have h := χ.unit_norm_eq_one hunit.unit
        rwa [hunit.unit_spec] at h
      have hχconj : χ ((p : ℕ) : ZMod q) * (starRingEnd ℂ) (χ ((p : ℕ) : ZMod q)) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ, one_pow, Complex.ofReal_one]
      calc χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (Complex.I * (t : ℂ))
            * (g p * (starRingEnd ℂ) (χ ((p : ℕ) : ZMod q))
              * (p : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ)))
          = χ ((p : ℕ) : ZMod q) * (starRingEnd ℂ) (χ ((p : ℕ) : ZMod q))
            * ((p : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ)) * (p : ℂ) ^ (Complex.I * (t : ℂ)))
            * g p := by ring
        _ = g p := by rw [hχconj, hcpow, one_mul, one_mul]
  exact hcm.eq_of_forall_prime hg hF1 hg1 hprime hn

/-! ### Pretense transfer: (gh) implies (gap) -/

/-- Off the divisors of `q`, the prime value of `h` is exactly the pretense comparison
`g(p)·conj(χ(p)·p^{i𝐭})` — the per-prime bridge between eq. `(gh)` and eq. `(gap)`. -/
theorem hPart_eq_mul_conj_charTwist {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) :
    hPart g q χ t p = g p * (starRingEnd ℂ) (charTwist q χ t p) := by
  rw [hPart_apply_prime hp, if_neg hpq]
  simp only [charTwist]
  rw [map_mul, conj_natCast_cpow_I_mul hp.pos.ne' t]
  ring

/-- **Pretense transfer** (Tao 2015 §4, eq. `(gh)` ⇒ eq. `(gap)`): the pretentious
distance from `h` to the constant `1` is bounded by the distance from `g` to the twist
`n ↦ χ(n)·n^{i𝐭}`:

`𝔻(h, 1; N)² ≤ 𝔻(g, χ·(·)^{i𝐭}; N)²`.

Prime by prime: for `p ∤ q` the summands agree (`hPart_eq_mul_conj_charTwist`); for
`p ∣ q` the left summand vanishes (`h(p) = 1`) while the right one is nonnegative. -/
theorem pretentiousDistSq_hPart_le (hu : Unimodular g) (N : ℕ) :
    pretentiousDistSq (hPart g q χ t) (fun _ => 1) N
      ≤ pretentiousDistSq g (charTwist q χ t) N := by
  unfold pretentiousDistSq
  refine Finset.sum_le_sum fun p hp => ?_
  have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
  by_cases hpq : p ∣ q
  · have h1 : hPart g q χ t p = 1 := by rw [hPart_apply_prime hpp, if_pos hpq]
    simp only [h1, map_one, mul_one, Complex.one_re, sub_self, zero_div]
    exact pretentiousDistSq_summand_nonneg_of_norm_le_one hu (charTwist_norm_le_one q χ t) p
  · have h2 : hPart g q χ t p = g p * (starRingEnd ℂ) (charTwist q χ t p) :=
      hPart_eq_mul_conj_charTwist hpp hpq
    simp only [h2, map_one, mul_one]
    exact le_rfl

/-! ### `h ≡ 1` on `q`-smooth numbers -/

/-- `h(d) = 1` whenever every prime factor of `d` divides `q` (Tao 2015 §4: used with
`d ∣ q^k`, e.g. for the principal-character term of the equidistribution computation and
for `h((b,r)) = 1` in the non-primitive residue classes).  The hypothesis also covers
`d = 0` and `d = 1` thanks to the junk value `cmOfPrimes F 0 = 1`. -/
theorem hPart_eq_one_of_primes_dvd {d : ℕ} (hdq : ∀ p : ℕ, p.Prime → p ∣ d → p ∣ q) :
    hPart g q χ t d = 1 := by
  unfold hPart cmOfPrimes
  rw [Finsupp.prod]
  refine Finset.prod_eq_one fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [← Nat.support_factorization])
  have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors (by rwa [← Nat.support_factorization])
  simp only [if_pos (hdq p hpp hpd), one_pow]

/-! ### χ̃-rigidity on good residue classes -/

/-- On arguments coprime to `q`, the completion `χ̃` is just the character: every prime
factor of `u` avoids `q`, so each prime datum takes the `χ` branch, and `χ` is completely
multiplicative on casts. -/
theorem chiTilde_apply_of_coprime {u : ℕ} (hu0 : u ≠ 0) (hcop : Nat.Coprime u q) :
    chiTilde g q χ t u = χ (u : ZMod q) := by
  have hχcm : CompletelyMultiplicativeC fun n : ℕ => χ (n : ZMod q) := by
    intro a b _ _
    show χ ((a * b : ℕ) : ZMod q) = χ ((a : ℕ) : ZMod q) * χ ((b : ℕ) : ZMod q)
    rw [Nat.cast_mul, map_mul]
  have hχ1 : χ ((1 : ℕ) : ZMod q) = 1 := by rw [Nat.cast_one, map_one]
  have hlhs : chiTilde g q χ t u = u.factorization.prod fun p k => χ (p : ZMod q) ^ k := by
    unfold chiTilde cmOfPrimes
    refine Finsupp.prod_congr fun p hp => ?_
    have hpp : p.Prime :=
      Nat.prime_of_mem_primeFactors (by rwa [← Nat.support_factorization])
    have hpu : p ∣ u := Nat.dvd_of_mem_primeFactors (by rwa [← Nat.support_factorization])
    have hpq : ¬ p ∣ q :=
      (Nat.Prime.coprime_iff_not_dvd hpp).mp (Nat.Coprime.coprime_dvd_left hpu hcop)
    simp only [if_neg hpq]
  rw [hlhs]
  exact (hχcm.eq_prod_factorization hχ1 hu0).symm

/-- Goodness of a residue class transfers along the congruence: if `n ≡ a (q^k)`, then
divisibility of `n + m` by `p^k` (for `p ∣ q`, so `p^k ∣ q^k`) is the same as for
`a + m`. -/
theorem IsGoodResidue.of_modEq {q k H a n : ℕ} (hgood : IsGoodResidue q k H a)
    (hcong : n ≡ a [MOD q ^ k]) : IsGoodResidue q k H n := by
  intro m hm p hp hpq hdvd
  refine hgood m hm p hp hpq ?_
  have hmod : n + m ≡ a + m [MOD p ^ k] :=
    (hcong.add_right m).of_dvd (pow_dvd_pow_of_dvd hpq k)
  exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))

/-- **χ̃-rigidity on good residue classes** (Tao 2015 §4, the display after eq. `(jock)`
setup): for a good class `a (q^k)`, `n ≡ a (q^k)`, and `1 ≤ m ≤ 2H`,

`χ̃(n + m) = χ̃(a + m)`.

Paper route: with `d = (a+m, q^k) = (n+m, q^k)` (gcd rigidity), split
`χ̃(n+m) = χ̃(d)·χ̃((n+m)/d)`; the cofactor is coprime to `q`, where `χ̃ = χ ∘ cast`, and
`(n+m)/d ≡ (a+m)/d (mod q)` because `d ∣ q^{k−1}` makes `q^k/d` a multiple of `q`. -/
theorem chiTilde_congr_of_good {k H a n : ℕ} (hq : 1 < q) (hk : 1 ≤ k)
    (hgood : IsGoodResidue q k H a) (hcong : n ≡ a [MOD q ^ k])
    {m : ℕ} (hm : m ∈ Finset.Icc 1 (2 * H)) :
    chiTilde g q χ t (n + m) = chiTilde g q χ t (a + m) := by
  have hq0 : q ≠ 0 := by omega
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hnm0 : n + m ≠ 0 := by omega
  have ham0 : a + m ≠ 0 := by omega
  set d := Nat.gcd (a + m) (q ^ k) with hd_def
  have hgcd_n : Nat.gcd (n + m) (q ^ k) = d := gcd_add_eq_of_modEq hcong m
  have hd0 : d ≠ 0 := Nat.gcd_ne_zero_left ham0
  have hd_dvd_pred : d ∣ q ^ (k - 1) := gcd_dvd_pow_pred_of_good hq0 hgood hm
  have hd_dvd_am : d ∣ a + m := Nat.gcd_dvd_left _ _
  have hd_dvd_nm : d ∣ n + m := by
    rw [← hgcd_n]
    exact Nat.gcd_dvd_left _ _
  have hd_dvd_qk : d ∣ q ^ k := Nat.gcd_dvd_right _ _
  -- goodness (hence coprimality of the cofactor) transfers from `a` to `n`
  have hgood_n : IsGoodResidue q k H n := hgood.of_modEq hcong
  have hcop_a : Nat.Coprime ((a + m) / d) q := coprime_div_gcd_of_good hq0 hgood hm
  have hcop_n : Nat.Coprime ((n + m) / d) q := by
    have h := coprime_div_gcd_of_good hq0 hgood_n hm
    rwa [hgcd_n] at h
  have hquot_n0 : (n + m) / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hnm0) hd_dvd_nm)
      (Nat.pos_of_ne_zero hd0)).ne'
  have hquot_a0 : (a + m) / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ham0) hd_dvd_am)
      (Nat.pos_of_ne_zero hd0)).ne'
  -- cofactor congruence mod `q`: divide `n + m ≡ a + m (q^k)` by `d`, then use
  -- `q ∣ q^k / d` (from `d ∣ q^{k−1}`)
  have hdivmod : (n + m) / d ≡ (a + m) / d [MOD q] := by
    have hqk_pos : 0 < q ^ k := pow_pos (by omega) k
    have h1 : d * ((n + m) / d) ≡ d * ((a + m) / d) [MOD q ^ k] := by
      rw [Nat.mul_div_cancel' hd_dvd_nm, Nat.mul_div_cancel' hd_dvd_am]
      exact hcong.add_right m
    have h2 := Nat.ModEq.cancel_left_div_gcd hqk_pos h1
    rw [Nat.gcd_eq_right hd_dvd_qk] at h2
    have hqk_eq : q ^ k = q * q ^ (k - 1) := by
      have hkk : k - 1 + 1 = k := Nat.sub_add_cancel hk
      calc q ^ k = q ^ (k - 1 + 1) := by rw [hkk]
        _ = q ^ (k - 1) * q := pow_succ q (k - 1)
        _ = q * q ^ (k - 1) := mul_comm _ _
    have hq_dvd : q ∣ q ^ k / d := by
      rw [hqk_eq, Nat.mul_div_assoc q hd_dvd_pred]
      exact dvd_mul_right q _
    exact h2.of_dvd hq_dvd
  have hcast : (((n + m) / d : ℕ) : ZMod q) = (((a + m) / d : ℕ) : ZMod q) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hdivmod
  calc chiTilde g q χ t (n + m)
      = chiTilde g q χ t (d * ((n + m) / d)) := by rw [Nat.mul_div_cancel' hd_dvd_nm]
    _ = chiTilde g q χ t d * chiTilde g q χ t ((n + m) / d) :=
        chiTilde_completelyMultiplicativeC d ((n + m) / d) hd0 hquot_n0
    _ = chiTilde g q χ t d * χ (((n + m) / d : ℕ) : ZMod q) := by
        rw [chiTilde_apply_of_coprime hquot_n0 hcop_n]
    _ = chiTilde g q χ t d * χ (((a + m) / d : ℕ) : ZMod q) := by rw [hcast]
    _ = chiTilde g q χ t d * chiTilde g q χ t ((a + m) / d) := by
        rw [chiTilde_apply_of_coprime hquot_a0 hcop_a]
    _ = chiTilde g q χ t (d * ((a + m) / d)) :=
        (chiTilde_completelyMultiplicativeC d ((a + m) / d) hd0 hquot_a0).symm
    _ = chiTilde g q χ t (a + m) := by rw [Nat.mul_div_cancel' hd_dvd_am]

end MoltResearch
