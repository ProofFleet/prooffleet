import MoltResearch.Discrepancy.MultiplicativeC
import Mathlib.Data.Nat.Factorization.Defs

/-!
# Discrepancy: completely multiplicative functions from prime data

Language-layer constructor for the Tao 2015 §4 analysis (`Problems/tao2015_derivation_c.md`,
issue #2871): the unique completely multiplicative extension `n ↦ ∏_{p^k ∥ n} F(p)^k` of a
prescribed function on the primes.

§4 uses it twice, to split a pretentious sample `g = χ̃ · n^{i𝐭} · h`:
- `χ̃`, the *character-like* completion of a Dirichlet character `χ` mod `q`: `χ(p)` at
  `p ∤ q`, but the (unimodular) `g(p)·p^{−i𝐭}` at `p | q` — the generalized
  Borwein–Choi–Coons object whose medium-length sums §4 bounds below;
- `h`, the *pretentious-to-1* part: `g(p)·conj(χ(p))·p^{−i𝐭}` at `p ∤ q`, `1` at `p | q`.

Conventions:
- Junk values: `cmOfPrimes F 0 = 1` (empty factorization), consistent with the guarded
  `CompletelyMultiplicativeC` (issue #2879), which never constrains the value at `0`.
- Only the values of `F` **at primes** matter (`cmOfPrimes_apply_prime`); unimodularity of
  the extension needs `‖F p‖ = 1` at primes only (`cmOfPrimes_unimodular`).
-/

namespace MoltResearch

/-- The completely multiplicative extension of prime data: `n ↦ ∏_{p^k ∥ n} F(p)^k`.

Values of `F` off the primes are ignored; `cmOfPrimes F 0 = 1` (junk, empty product). -/
noncomputable def cmOfPrimes (F : ℕ → ℂ) : ℕ → ℂ :=
  fun n => n.factorization.prod fun p k => F p ^ k

/-- Degenerate input: the empty factorization of `0` gives the junk value `1`. -/
@[simp] theorem cmOfPrimes_zero (F : ℕ → ℂ) : cmOfPrimes F 0 = 1 := by
  simp [cmOfPrimes]

/-- The empty factorization of `1` gives `1`. -/
@[simp] theorem cmOfPrimes_one (F : ℕ → ℂ) : cmOfPrimes F 1 = 1 := by
  simp [cmOfPrimes]

/-- The extension is completely multiplicative (in the guarded, literature sense). -/
theorem cmOfPrimes_completelyMultiplicativeC (F : ℕ → ℂ) :
    CompletelyMultiplicativeC (cmOfPrimes F) := by
  intro a b ha hb
  unfold cmOfPrimes
  rw [Nat.factorization_mul ha hb]
  exact Finsupp.prod_add_index' (fun p => pow_zero (F p)) fun p k l => pow_add (F p) k l

/-- The extension restricts to `F` on the primes. -/
theorem cmOfPrimes_apply_prime (F : ℕ → ℂ) {p : ℕ} (hp : p.Prime) :
    cmOfPrimes F p = F p := by
  unfold cmOfPrimes
  have h : (Finsupp.single p 1).prod (fun p k => F p ^ k) = F p ^ 1 :=
    Finsupp.prod_single_index (pow_zero (F p))
  rw [Nat.Prime.factorization hp, h, pow_one]

/-- Prime-power evaluation: `cmOfPrimes F (p^k) = F(p)^k`. -/
theorem cmOfPrimes_apply_prime_pow (F : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    cmOfPrimes F (p ^ k) = F p ^ k := by
  unfold cmOfPrimes
  rw [Nat.Prime.factorization_pow hp]
  exact Finsupp.prod_single_index (pow_zero (F p))

/-- Unimodularity transfers from the prime data to the extension (all `n`, including the
junk `‖cmOfPrimes F 0‖ = ‖1‖ = 1`). -/
theorem cmOfPrimes_unimodular {F : ℕ → ℂ} (hF : ∀ p : ℕ, p.Prime → ‖F p‖ = 1) :
    Unimodular (cmOfPrimes F) := by
  intro n
  unfold cmOfPrimes
  rw [Finsupp.prod, norm_prod]
  refine Finset.prod_eq_one fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by
    rwa [← Nat.support_factorization])
  rw [norm_pow, hF p hpp, one_pow]

end MoltResearch
