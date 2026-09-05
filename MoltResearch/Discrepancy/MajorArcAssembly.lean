import MoltResearch.Discrepancy.MajorArcFreeze
import MoltResearch.Discrepancy.TypicalFactorization

/-!
# Track R: the major-arc assembly — opening lemmas (R6-1, R6-2a)

The major-arc Matomäki–Radziwiłł interface bounds
`∑_{n} ‖∑_{j=1}^{H} g(n+j)·e(jα)‖/(Hn)` on major arcs `α = a/q + δ`.  The
assembly (`Problems/tao2015_a1_r6r7_design_report.md`, §1.3 and §8 Phase R6)
follows `[mrt]`'s major-arc section: rewrite the window sum as a sum over
`m ∈ (n, n+H]` of `g(m)e(mα)`, split it into the `𝒮`-restricted part and the
complement, split the restricted part by residue classes `m ≡ b (mod q)`,
extract `d₀ = gcd(b, q)` by complete multiplicativity, expand the class in
Dirichlet characters, freeze the slowly varying phase, and apply the
`𝒮`-restricted A.2 per twist.  This module holds the two elementary facts the
first steps rest on.

* `window_twisted_sum_eq` / `norm_window_twisted_sum_eq` — the shift `j ↦ n + j`
  turns the interface's window into a block of `g(m)e(mα)`, at the cost of a
  unimodular factor `e(−nα)` which the norm forgets.  Everything downstream is
  stated for blocks `Finset.Ioc n (n+H)`, the shape of the slice harness.
* `norm_block_le_restricted_add_card` — the block sum is the `𝒮`-restricted sum
  plus at most the number of non-typical integers in the block.  This is the
  **once-paid** removal of the complement (report §7.3): the arcs are assembled
  on the restricted sum, and the complement is priced by its density only at
  the top, exactly as Tao's proof of Proposition 2.4 uses `[mrt, Lemma 2.2]`.
* `hasFactorInAll_mul_left_iff` — `𝒮`-membership is invariant under
  multiplication by an integer with no prime in any level.  It is what lets the
  residue-class extraction `m = d₀·m'` (with `d₀ ∣ q ≤ (log H)^{20} < P₁`) stay
  inside the restricted sums, so that A.2 is applied to the same `𝒮` at every
  class.
-/

open Finset

namespace MoltResearch

/-- **`𝒮`-membership is invariant under coprime dilation** (Track R, R6-2a).

If no prime of any level divides `d`, then `d·m` has a factor in every level iff
`m` does: a level prime dividing `d·m` must divide `m`.  The hypothesis is the
one the residue-class step supplies — `d₀ ∣ q` and `q` is below every level. -/
theorem hasFactorInAll_mul_left_iff (levels : List (Finset ℕ))
    (hlv : ∀ P ∈ levels, ∀ p ∈ P, p.Prime) (d m : ℕ)
    (hd : ∀ P ∈ levels, ∀ p ∈ P, ¬ p ∣ d) :
    HasFactorInAll levels (d * m) ↔ HasFactorInAll levels m := by
  have hfilter : ∀ P ∈ levels,
      P.filter (· ∣ d * m) = P.filter (· ∣ m) := by
    intro P hP
    refine Finset.filter_congr fun p hp => ?_
    have hpp := hlv P hP p hp
    have hpd := hd P hP p hp
    constructor
    · intro h
      rcases (Nat.Prime.dvd_mul hpp).mp h with h1 | h1
      · exact absurd h1 hpd
      · exact h1
    · intro h
      exact Dvd.dvd.mul_left h d
  constructor
  · intro h P hP
    rw [← hfilter P hP]
    exact h P hP
  · intro h P hP
    rw [hfilter P hP]
    exact h P hP

/-- **The window as a block** (Track R, R6-1): shifting the summation index by
`n` turns the interface's window sum into a block sum of `g(m)e(mα)` over
`(n, n+H]`, times the unimodular phase `e(−nα)`. -/
theorem window_twisted_sum_eq (g : ℕ → ℂ) (n H : ℕ) (α : ℝ) :
    ∑ j ∈ Finset.Icc 1 H,
        g (n + j) * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (α : ℂ))
      = Complex.exp (-(2 * Real.pi * Complex.I * (n : ℂ) * (α : ℂ)))
        * ∑ m ∈ Finset.Ioc n (n + H),
            g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ)) := by
  have hmap : (Finset.Icc 1 H).map (addLeftEmbedding n) = Finset.Ioc n (n + H) := by
    rw [Finset.map_add_left_Icc, Finset.Icc_add_one_left_eq_Ioc]
  rw [← hmap, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [addLeftEmbedding_apply]
  have hexp : Complex.exp (2 * Real.pi * Complex.I * ((n + j : ℕ) : ℂ) * (α : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (α : ℂ))
        * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (α : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp, ← mul_assoc, ← mul_assoc, mul_comm (Complex.exp (-_)) (g (n + j)),
    mul_assoc (g (n + j)), ← Complex.exp_add]
  have hzero : -(2 * Real.pi * Complex.I * (n : ℂ) * (α : ℂ))
      + 2 * Real.pi * Complex.I * (n : ℂ) * (α : ℂ) = 0 := by ring
  rw [hzero, Complex.exp_zero, mul_one]

/-- **The window's norm is the block's norm** (Track R, R6-1). -/
theorem norm_window_twisted_sum_eq (g : ℕ → ℂ) (n H : ℕ) (α : ℝ) :
    ‖∑ j ∈ Finset.Icc 1 H,
        g (n + j) * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (α : ℂ))‖
      = ‖∑ m ∈ Finset.Ioc n (n + H),
            g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ := by
  rw [window_twisted_sum_eq, norm_mul, Complex.norm_exp]
  have hre : (-(2 * Real.pi * Complex.I * (n : ℂ) * (α : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero, one_mul]

/-- **The once-paid `𝒮`-removal on a block** (Track R, R6-1 / R7-3): a
`1`-bounded twisted block sum is at most its `𝒮`-restricted part plus the number
of non-typical integers in the block.  The phase is any unimodular `φ`. -/
theorem norm_block_le_restricted_add_card (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (φ : ℕ → ℂ) (hφ : ∀ m, ‖φ m‖ ≤ 1)
    (levels : List (Finset ℕ)) (n H : ℕ) :
    ‖∑ m ∈ Finset.Ioc n (n + H), g m * φ m‖
      ≤ ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels), g m * φ m‖
        + (((Finset.Ioc n (n + H)).filter
            (fun m => ¬ HasFactorInAll levels m)).card : ℝ) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc n (n + H))
    (HasFactorInAll levels)]
  refine le_trans (norm_add_le _ _) (add_le_add le_rfl ?_)
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ m ∈ (Finset.Ioc n (n + H)).filter (fun m => ¬ HasFactorInAll levels m),
          ‖g m * φ m‖
      ≤ ∑ m ∈ (Finset.Ioc n (n + H)).filter (fun m => ¬ HasFactorInAll levels m),
          (1 : ℝ) := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [norm_mul]
        exact mul_le_one₀ (hg m) (norm_nonneg _) (hφ m)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end MoltResearch
