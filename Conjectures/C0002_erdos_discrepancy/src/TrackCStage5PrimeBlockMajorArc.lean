import MoltResearch.Discrepancy
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5QuadrupleSieve

/-!
# Track C: Stage 5 — the prime-block major-arc classification interface (R1 of issue #3044)

The **Vinogradov classification**: a dyadic prime-block exponential sum that is
within a constant-times-`ε` factor of its trivial (Mertens) size can only occur at
major-arc frequencies — rationals `a/q` with `q` polylogarithmic in the block scale,
up to a polylogarithmic-over-`n₀` width.

This is the bridge between the consumer's frequency filter (the `θ`-large set of
`elliott_master`, whose size `card_major_le` bounds via the quadruple sieve) and the
major-arc Matomäki–Radziwiłł interface: composed, they replace the all-`α`
`MatomakiRadziwillAssumption` on the whole Erdős-discrepancy chain.

Mathematically this is Vinogradov's estimate for exponential sums over primes
(Vaughan's identity + Type I/II bilinear sums; see [ik, §13.5]), in contrapositive
form: on minor arcs — `q ∈ [C·(log n₀)^B, n₀/(C·(log n₀)^B)]` after Dirichlet
approximation — the block sum `∑_{n₀<p≤2n₀} e(pβ)/p` is `o(1/log n₀)`, below any
fixed fraction of the trivial size.  Frequency-aspect only: no zero-free regions,
no `t`-heights — fully elementary (campaign phase R4v).

Design notes (Track R, issue #3044):

- The classification constants `B, C` and the threshold scale `N₀` depend only on
  the fraction-of-trivial coefficient `c`; the consumer's threshold
  `θs = ε·ms/256 ≥ c(ε)/log n₀` (via `hms_lb`) supplies exactly this shape.
- The conclusion's arc data is formatted to feed
  `MatomakiRadziwillMajorArcAssumption` after the frequency substitution
  `β = h·α` (lemma `majorArc_of_mul` below): denominators multiply by `h`, widths
  divide by `h`.
- Discharged unconditionally by `instPrimeBlockMajorArcAssumption`
  (`TrackCStage5PrimeBlockMajorArcProof.lean`, R4v of issue #3044), which supplies the
  Vinogradov Type I/II classification with `B = 20`, `C = 1`.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- **Prime-block major-arc classification assumption** (Vinogradov; [ik, §13.5],
used as in the remarks of arXiv:1509.05422 following Proposition `mrp`): if a dyadic
prime-block exponential sum at frequency `β` is at least `c/log n₀` — a fixed
fraction of its trivial Mertens size — then `β` lies in a major arc of
polylogarithmic denominator and polylogarithmic-over-`n₀` width, with constants
depending only on `c`. -/
class PrimeBlockMajorArcAssumption : Prop where
  bound :
    ∀ c : ℝ, 0 < c →
      ∃ N₀ : ℕ, ∃ B : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ n₀ : ℕ, N₀ ≤ n₀ →
          ∀ β θ : ℝ, c / Real.log n₀ ≤ θ →
            θ ≤ ‖∑ p ∈ primeBlock n₀, ((1 / (p : ℝ) : ℝ) : ℂ) * e ((p : ℝ) * β)‖ →
            ∃ a : ℤ, ∃ q : ℕ, 1 ≤ q ∧
              (q : ℝ) ≤ C * Real.log n₀ ^ B ∧
              |β - (a : ℝ) / (q : ℝ)| ≤ C * Real.log n₀ ^ B / ((n₀ : ℝ) * (q : ℝ))

/-- Consumer-facing restatement. -/
theorem primeBlockMajorArc_bound [inst : PrimeBlockMajorArcAssumption]
    {c : ℝ} (hc : 0 < c) :
    ∃ N₀ : ℕ, ∃ B : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n₀ : ℕ, N₀ ≤ n₀ →
        ∀ β θ : ℝ, c / Real.log n₀ ≤ θ →
          θ ≤ ‖∑ p ∈ primeBlock n₀, ((1 / (p : ℝ) : ℝ) : ℂ) * e ((p : ℝ) * β)‖ →
          ∃ a : ℤ, ∃ q : ℕ, 1 ≤ q ∧
            (q : ℝ) ≤ C * Real.log n₀ ^ B ∧
            |β - (a : ℝ) / (q : ℝ)| ≤ C * Real.log n₀ ^ B / ((n₀ : ℝ) * (q : ℝ)) :=
  inst.bound c hc

/-- **Arc transport under frequency division**: major-arc data for `h·α` yields
major-arc data for `α`, with the denominator multiplied by `h` and the width divided
by `h`.  This is the substitution the consumer performs between the classification
(applied at the prime-block frequency `h·α`) and the major-arc Matomäki–Radziwiłł
interface (applied at the modulation frequency `α`). -/
theorem majorArc_of_mul {α w : ℝ} {a : ℤ} {q h : ℕ} (hq : 1 ≤ q) (hh : 1 ≤ h)
    (harc : |(h : ℝ) * α - (a : ℝ) / (q : ℝ)| ≤ w) :
    ∃ a' : ℤ, ∃ q' : ℕ, 1 ≤ q' ∧ q' = q * h ∧
      |α - (a' : ℝ) / (q' : ℝ)| ≤ w / (h : ℝ) := by
  refine ⟨a, q * h, Nat.one_le_iff_ne_zero.mpr (by positivity), rfl, ?_⟩
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hcast : ((q * h : ℕ) : ℝ) = (q : ℝ) * (h : ℝ) := by push_cast; ring
  have hkey : α - (a : ℝ) / ((q * h : ℕ) : ℝ)
      = ((h : ℝ) * α - (a : ℝ) / (q : ℝ)) / (h : ℝ) := by
    rw [hcast]
    field_simp
  rw [hkey, abs_div, abs_of_pos hh0]
  gcongr

-- Consumer example (compile-only): the classification composes with the arc
-- transport to produce data in exactly the format
-- `MatomakiRadziwillMajorArcAssumption` consumes (denominator bound `C·h·log^B n₀`,
-- width `C·log^B n₀/(n₀·q')·1`), for any shift `1 ≤ h`.
example [PrimeBlockMajorArcAssumption] {c : ℝ} (hc : 0 < c) (h : ℕ) (hh : 1 ≤ h) :
    ∃ N₀ : ℕ, ∃ B : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n₀ : ℕ, N₀ ≤ n₀ →
        ∀ α θ : ℝ, c / Real.log n₀ ≤ θ →
          θ ≤ ‖∑ p ∈ primeBlock n₀, ((1 / (p : ℝ) : ℝ) : ℂ)
              * e ((p : ℝ) * ((h : ℝ) * α))‖ →
          ∃ a' : ℤ, ∃ q' : ℕ, 1 ≤ q' ∧
            (q' : ℝ) ≤ C * (h : ℝ) * Real.log n₀ ^ B ∧
            |α - (a' : ℝ) / (q' : ℝ)|
              ≤ C * Real.log n₀ ^ B / ((n₀ : ℝ) * (h : ℝ)) := by
  obtain ⟨N₀, B, C, hC0, hbound⟩ := primeBlockMajorArc_bound hc
  refine ⟨N₀, B, C, hC0, fun n₀ hn₀ α θ hθlo hθ => ?_⟩
  obtain ⟨a, q, hq1, hqB, harc⟩ := hbound n₀ hn₀ ((h : ℝ) * α) θ hθlo hθ
  obtain ⟨a', q', hq'1, hq'eq, harc'⟩ := majorArc_of_mul hq1 hh harc
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  refine ⟨a', q', hq'1, ?_, ?_⟩
  · have : ((q' : ℕ) : ℝ) = (q : ℝ) * (h : ℝ) := by
      rw [hq'eq]; push_cast; ring
    rw [this]
    calc (q : ℝ) * (h : ℝ) ≤ (C * Real.log n₀ ^ B) * (h : ℝ) :=
          mul_le_mul_of_nonneg_right hqB hh0.le
      _ = C * (h : ℝ) * Real.log n₀ ^ B := by ring
  · refine harc'.trans ?_
    have hn₀0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
    have hstep : C * Real.log n₀ ^ B / ((n₀ : ℝ) * (q : ℝ)) / (h : ℝ)
        ≤ C * Real.log n₀ ^ B / ((n₀ : ℝ) * (h : ℝ)) := by
      rw [div_div]
      rcases eq_or_lt_of_le hn₀0 with h0 | hn₀pos
      · simp [← h0]
      · refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        calc (n₀ : ℝ) * (h : ℝ) = (n₀ : ℝ) * 1 * (h : ℝ) := by ring
          _ ≤ (n₀ : ℝ) * (q : ℝ) * (h : ℝ) := by
              have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left this hn₀0) hh0.le
    exact hstep

end Tao2015

end MoltResearch
