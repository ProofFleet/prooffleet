import MoltResearch.Discrepancy.MajorArcFreeze
import MoltResearch.Discrepancy.TypicalFactorization

/-!
# Track R: the major-arc assembly — opening lemmas (R6-1, R6-2a, R6-2b)

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
* `sum_mul_exp_ratl_eq_sum_residues` / `sum_restricted_residue_eq_gcd_dilate`
  (R6-2b) — the residue split.  The rational phase `e(m·a/q)` depends only on
  `m mod q`, so the restricted block sum is a sum over the `q` classes; inside
  the class `m ≡ b`, every `m` is a multiple of `d₀ = gcd(b, q)`, and writing
  `m = d₀·m'` (complete multiplicativity, `𝒮`-invariance of the dilation) turns
  the class sum into `g(d₀)` times a sum over the dilated block
  `(⌊lo/d₀⌋, ⌊hi/d₀⌋]` in the **unit** class `m' ≡ b/d₀ (mod q/d₀)` — the shape the
  character expansion (`sum_filter_residue_eq_char_avg`) consumes.
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

/-- **The residue split of a rational phase sum** (Track R, R6-2b).

The phase `e(m·a/q)` depends only on `m mod q` (`m = q·⌊m/q⌋ + (m mod q)` and
`e(integer) = 1`), so a phase sum over any finite set of integers is the sum over
the `q` residue classes of the class phase times the untwisted class sum.  This is
the step that removes the rational part of the major-arc frequency: what is left
in each class is a plain (frozen) sum of `g`. -/
theorem sum_mul_exp_ratl_eq_sum_residues (S : Finset ℕ) (F : ℕ → ℂ) (a : ℤ) (q : ℕ)
    (hq : 0 < q) :
    ∑ m ∈ S, F m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)
        * (((a : ℝ) / (q : ℝ) : ℝ) : ℂ))
      = ∑ b ∈ Finset.range q,
          Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) * (((a : ℝ) / (q : ℝ) : ℝ) : ℂ))
            * ∑ m ∈ S.filter (fun m => m % q = b), F m := by
  classical
  have hmaps : ∀ m ∈ S, m % q ∈ Finset.range q := fun m _ =>
    Finset.mem_range.mpr (Nat.mod_lt m hq)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmb : m % q = b := (Finset.mem_filter.mp hm).2
  subst hmb
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hsplit : (m : ℂ) = (q : ℂ) * ((m / q : ℕ) : ℂ) + ((m % q : ℕ) : ℂ) := by
    exact_mod_cast (Nat.div_add_mod m q).symm
  have hint : Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (((a : ℝ) / (q : ℝ) : ℝ) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * ((m % q : ℕ) : ℂ)
            * (((a : ℝ) / (q : ℝ) : ℝ) : ℂ))
        * Complex.exp ((((m / q : ℕ) : ℤ) * a : ℤ) * (2 * Real.pi * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hsplit]
    simp only [Int.cast_mul, Int.cast_natCast, Complex.ofReal_div, Complex.ofReal_intCast,
      Complex.ofReal_natCast]
    field_simp
    ring
  rw [hint, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  ring

/-- **The gcd extraction inside a residue class** (Track R, R6-2b).

In the class `m ≡ b (mod q)` every `m` is a multiple of `d₀ = gcd(b, q)`, and
`m = d₀·m'` runs over the dilated block `(⌊lo/d₀⌋, ⌊hi/d₀⌋]` in the class
`m' ≡ b/d₀ (mod q/d₀)`, which is a **unit** class.  Complete multiplicativity
factors `g(m) = g(d₀)·g(m')`, and `𝒮`-membership is unchanged by the dilation
when no level prime divides `q` (`hasFactorInAll_mul_left_iff`).  The hypothesis
`hql` is the one the arcs supply: `q ≤ (log H)^{20}` lies below every level.

The block bounds are `Nat` floors: `lo < d₀·m' ↔ ⌊lo/d₀⌋ < m'` and
`d₀·m' ≤ hi ↔ m' ≤ ⌊hi/d₀⌋`, so the dilated block is exactly an `Ioc` again — the
shape A.2 is stated for. -/
theorem sum_restricted_residue_eq_gcd_dilate (g : ℕ → ℂ) (hg : CompletelyMultiplicativeC g)
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ p ∈ P, p.Prime)
    (q : ℕ) (hq : 0 < q) (hql : ∀ P ∈ levels, ∀ p ∈ P, ¬ p ∣ q)
    (b lo hi : ℕ) :
    ∑ m ∈ (Finset.Ioc lo hi).filter
        (fun m => HasFactorInAll levels m ∧ m % q = b), g m
      = g (Nat.gcd b q)
        * ∑ m' ∈ (Finset.Ioc (lo / Nat.gcd b q) (hi / Nat.gcd b q)).filter
            (fun m' => HasFactorInAll levels m'
              ∧ m' % (q / Nat.gcd b q) = b / Nat.gcd b q), g m' := by
  classical
  have hdq : Nat.gcd b q ∣ q := Nat.gcd_dvd_right b q
  have hdb : Nat.gcd b q ∣ b := Nat.gcd_dvd_left b q
  have hd0 : 0 < Nat.gcd b q := Nat.gcd_pos_of_pos_right b hq
  generalize hd : Nat.gcd b q = d at hdq hdb hd0 ⊢
  obtain ⟨q₀, hq₀⟩ := hdq
  obtain ⟨b₀, hb₀⟩ := hdb
  have hqd : q / d = q₀ := by rw [hq₀]; exact Nat.mul_div_cancel_left q₀ hd0
  have hbd : b / d = b₀ := by rw [hb₀]; exact Nat.mul_div_cancel_left b₀ hd0
  have hdl : ∀ P ∈ levels, ∀ p ∈ P, ¬ p ∣ d := fun P hP p hp hpd =>
    hql P hP p hp (dvd_trans hpd ⟨q₀, hq₀⟩)
  rw [hqd, hbd, Finset.mul_sum]
  have hterm : ∀ m' ∈ (Finset.Ioc (lo / d) (hi / d)).filter
      (fun m' => HasFactorInAll levels m' ∧ m' % q₀ = b₀),
      g d * g m' = g (d * m') := by
    intro m' hm'
    have hm'0 : m' ≠ 0 :=
      (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm').1).1).ne'
    rw [hg d m' hd0.ne' hm'0]
  rw [Finset.sum_congr rfl hterm]
  have hinj : Set.InjOn (fun m' : ℕ => d * m')
      ↑((Finset.Ioc (lo / d) (hi / d)).filter
        (fun m' => HasFactorInAll levels m' ∧ m' % q₀ = b₀)) := by
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left hd0 hxy
  rw [← Finset.sum_image hinj]
  congr 1
  ext m
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hS, hres⟩
    have hdm : d ∣ m := by
      have h := Nat.div_add_mod m q
      rw [← h]
      refine dvd_add (dvd_mul_of_dvd_left ⟨q₀, hq₀⟩ _) ?_
      rw [hres, hb₀]
      exact dvd_mul_right d b₀
    obtain ⟨m', rfl⟩ := hdm
    refine ⟨m', ⟨⟨?_, ?_⟩, ?_, ?_⟩, rfl⟩
    · refine (Nat.div_lt_iff_lt_mul hd0).mpr ?_
      rw [mul_comm]
      exact hlo
    · refine (Nat.le_div_iff_mul_le hd0).mpr ?_
      rw [mul_comm]
      exact hhi
    · exact (hasFactorInAll_mul_left_iff levels hlv d m' hdl).mp hS
    · rw [hq₀, hb₀, Nat.mul_mod_mul_left] at hres
      exact Nat.eq_of_mul_eq_mul_left hd0 hres
  · rintro ⟨m', ⟨⟨hlo, hhi⟩, hS, hres⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have h := (Nat.div_lt_iff_lt_mul hd0).mp hlo
      rw [mul_comm] at h
      exact h
    · have h := (Nat.le_div_iff_mul_le hd0).mp hhi
      rw [mul_comm] at h
      exact h
    · exact (hasFactorInAll_mul_left_iff levels hlv d m' hdl).mpr hS
    · rw [hq₀, hb₀, Nat.mul_mod_mul_left, hres]

end MoltResearch
