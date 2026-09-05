import MoltResearch.Discrepancy.MajorArcFreeze
import MoltResearch.Discrepancy.TypicalFactorization
import MoltResearch.Discrepancy.CharTwistCompose

/-!
# Track R: the major-arc assembly — opening lemmas (R6-1 … R6-7)

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
* `sum_restricted_unit_class_eq_char_avg` / `norm_restricted_block_ratl_le_char_sum`
  (R6-3) — the character expansion of the unit class, and the per-block capstone: the
  `𝒮`-restricted block sum at the rational frequency `a/q` is at most the sum over the
  `q` classes of the `1/φ(q₀)`-weighted character sums of `‖∑_{dilated block ∩ 𝒮} χ·g‖`.
  The rational frequency is gone; each term is a plain `𝒮`-restricted block sum of the
  twist `χ·g`, which is what A.2 bounds.
* `completelyMultiplicativeC_charMul`, `norm_charMul_le_one`, `charMul_one`,
  `nonPretentiousAt_charMul` (R6-3) — the twist `χ·g` satisfies every hypothesis A.2
  places on its function: completely multiplicative, `1`-bounded, `1` at `1`, and
  non-pretentious at strength `A/q₀` whenever `g` is at strength `A` (the distance to a
  twist mod `q'` is the distance of `g` to the composite twist mod `q'·q₀`, which the
  predicate already covers).
* `norm_filter_block_twisted_le_subblocks_add` (R6-4) — the phase freeze on a filtered
  block: at `α = β + δ`, the `δ`-phase is frozen on sub-blocks of length `ℓ`
  (`norm_sum_mul_exp_freeze_sub_le`), so the twisted `𝒮`-restricted block sum is at most
  the sum of the `⌊H/ℓ⌋ + 1` sub-block sums at the frequency `β` alone, plus the freeze
  cost `H·2π|δ|ℓ`.  With `β = a/q`, each sub-block is exactly the object of
  `norm_restricted_block_ratl_le_char_sum`.
* `logavg_le_of_meanSquare_dyadic`, `sum_div_comp_div_le`, `norm_filter_block_le_card`
  (R6-5) — the three bookkeeping facts that turn A.2 into the per-`(k, b, χ)` average:
  the mean-square bound on dyadic blocks gives the log-averaged `L¹` bound on blocks of
  ratio `≤ 3` (Cauchy–Schwarz, one split at `2a`); the `d`-to-one reindexing
  `n ↦ (n + c)/d` of a log-averaged sum costs the factor `4/3` (each fibre has `≤ d`
  points and `d·n' ≤ n + c ≤ (4/3)n`); and a `1`-bounded filtered block sum is at most
  the block length (the partial last sub-block).
* `norm_twisted_filter_block_le_windows_add`, `sum_restricted_residue_mul_eq_gcd_dilate`
  (R6-6a) — the two shapes the per-`n` assembly composes: the freeze on a block of
  length `L` trimmed to `h₀·⌊L/h₀⌋`, so that every sub-block is a **full** window
  `(n + kh₀, n + kh₀ + h₀]` or empty (cost `h₀` for the trimmed tail, `L·2π|δ|h₀` for the
  freeze, range extended to any `K > L/h₀`); and the gcd dilation with a phase factor
  carried along, `∑_{m ≡ b} g(m)F(m) = g(d₀)·∑_{m'} g(m')F(d₀m')` — the residue split is
  done **before** the freeze, so that one window length `h₀` serves every class and the
  A.2 input is taken at a single `(ε', h₀)` (one `𝒮` for all twists).
* `norm_restricted_window_le_char_windows` (R6-6b) — the per-`n` composition of all of
  the above: the `𝒮`-restricted window at `n`, twisted by `e(m(a/q + δ))`, is at most
  `∑_{b<q} (1/φ(q/d₀)) ∑_{χ} [∑_{k<K} ‖∑_{(⌊n/d₀⌋ + kh₀, ⌊n/d₀⌋ + kh₀ + h₀] ∩ 𝒮} χ·g‖
  + h₀ + L_b·2π|d₀δ|h₀]`.  Every window on the right has the same length `h₀`; the
  rational frequency, the classes and the arc phase are all gone.
* `sum_div_comp_div_le_of_meanSquare` (R6-6c) — the reindexed A.2 average over one
  dyadic block, in absolute form: `∑_{n∈(A,2A]} W((n+c)/d)/n ≤ 4·εh` from the mean-square
  input on dyadic blocks above `A₁`, once `4d ≤ A`, `3c ≤ A`, `A₁ + 1 ≤ ⌊(A+c)/d⌋`.  The
  reindexed range has ratio just above `2` and harmonic mass at most `3`.
* `sum_restricted_window_logavg_le_of_meanSquare` (R6-6d) — **the restricted major-arc
  bound on one dyadic block**: given the mean-square input for every twist `χ·g`
  (`χ` mod `q/d₀`, `d₀ ∣ q`) at the one window length `h₀`, the log average over
  `(A, 2A]` of the `𝒮`-restricted window sums at `a/q + δ` is at most
  `(16qε' + qh₀/H + 4πq²|δ|h₀)·∑_{(A,2A]} 1/n`.  This is R6-6 of the report, with the
  three costs (A.2 main term, trimmed tails, freeze) explicit.
* `nonPretentiousAt_scale_up`, `sum_card_filter_window_div_le` (R6-7 / R7-3a) — the two
  facts the wrapper needs around the block bound: non-pretentiousness at scale `x`
  transfers **up** to any scale `z ≤ c·x` at strength `A/c` (the distance only grows, the
  frequency range `|t| ≤ (A/c)·z ≤ A·x` is covered), so the twisted block scale `2A'+1`,
  which may exceed `x` for the top dyadic blocks, is reached without a Mertens cost; and
  the harmonic-weighted sliding count `∑_{n∈(A,B]} #((n,n+H] ∩ {p})/n ≤ 2H·∑_{m∈(A,B+H]∩{p}} 1/m`
  (each `m` is met by at most `H` windows, all starting at `n ≥ m − H ≥ m/2`), which prices
  the once-paid `𝒮ᶜ` removal by the block's `𝒮ᶜ` log-density.
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

/-- **The gcd extraction inside a residue class** (Track R, R6-2b; phase-carrying form, R6-6a).

In the class `m ≡ b (mod q)` every `m` is a multiple of `d₀ = gcd(b, q)`, and
`m = d₀·m'` runs over the dilated block `(⌊lo/d₀⌋, ⌊hi/d₀⌋]` in the class
`m' ≡ b/d₀ (mod q/d₀)`, which is a **unit** class.  Complete multiplicativity
factors `g(m) = g(d₀)·g(m')`, and `𝒮`-membership is unchanged by the dilation
when no level prime divides `q` (`hasFactorInAll_mul_left_iff`).  The hypothesis
`hql` is the one the arcs supply: `q ≤ (log H)^{20}` lies below every level.

The block bounds are `Nat` floors: `lo < d₀·m' ↔ ⌊lo/d₀⌋ < m'` and
`d₀·m' ≤ hi ↔ m' ≤ ⌊hi/d₀⌋`, so the dilated block is exactly an `Ioc` again — the
shape A.2 is stated for.  An arbitrary factor `F` rides along (`F(m) = F(d₀·m')`), so the
slowly varying arc phase `e(mδ)` can be split into classes **before** it is frozen. -/
theorem sum_restricted_residue_mul_eq_gcd_dilate (g : ℕ → ℂ)
    (hg : CompletelyMultiplicativeC g)
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ p ∈ P, p.Prime)
    (q : ℕ) (hq : 0 < q) (hql : ∀ P ∈ levels, ∀ p ∈ P, ¬ p ∣ q)
    (F : ℕ → ℂ) (b lo hi : ℕ) :
    ∑ m ∈ (Finset.Ioc lo hi).filter
        (fun m => HasFactorInAll levels m ∧ m % q = b), g m * F m
      = g (Nat.gcd b q)
        * ∑ m' ∈ (Finset.Ioc (lo / Nat.gcd b q) (hi / Nat.gcd b q)).filter
            (fun m' => HasFactorInAll levels m'
              ∧ m' % (q / Nat.gcd b q) = b / Nat.gcd b q), g m' * F (Nat.gcd b q * m') := by
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
      g d * (g m' * F (d * m')) = g (d * m') * F (d * m') := by
    intro m' hm'
    have hm'0 : m' ≠ 0 :=
      (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm').1).1).ne'
    rw [hg d m' hd0.ne' hm'0, mul_assoc]
  rw [Finset.sum_congr rfl hterm]
  have hinj : Set.InjOn (fun m' : ℕ => d * m')
      ↑((Finset.Ioc (lo / d) (hi / d)).filter
        (fun m' => HasFactorInAll levels m' ∧ m' % q₀ = b₀)) := by
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left hd0 hxy
  rw [← Finset.sum_image (f := fun y => g y * F y) hinj]
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

/-- **The gcd extraction inside a residue class** (Track R, R6-2b), phase-free form:
the case `F = 1` of `sum_restricted_residue_mul_eq_gcd_dilate`. -/
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
  have := sum_restricted_residue_mul_eq_gcd_dilate g hg levels hlv q hq hql
    (fun _ => (1 : ℂ)) b lo hi
  simpa only [mul_one] using this

/-! ### R6-3: the character expansion of a unit class, and the `χ·g` twist -/

/-- **The unit class in characters** (Track R, R6-3): the `𝒮`-restricted sum over
the class `m ≡ b₀ (mod q₀)`, `gcd(b₀, q₀) = 1`, is the `1/φ(q₀)`-weighted character
average of the twisted `𝒮`-restricted block sums — `sum_filter_residue_eq_char_avg`
on the block `(lo, hi] ∩ 𝒮`, with the residue predicate read in `ZMod q₀`. -/
theorem sum_restricted_unit_class_eq_char_avg (g : ℕ → ℂ) (levels : List (Finset ℕ))
    (q₀ b₀ lo hi : ℕ) (hq₀ : 0 < q₀) (hb₀ : b₀ < q₀) (hcop : Nat.Coprime b₀ q₀) :
    ∑ m ∈ (Finset.Ioc lo hi).filter
        (fun m => HasFactorInAll levels m ∧ m % q₀ = b₀), g m
      = (1 / (q₀.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q₀,
          χ ((b₀ : ZMod q₀))⁻¹
            * ∑ m ∈ (Finset.Ioc lo hi).filter (HasFactorInAll levels), χ m * g m := by
  classical
  haveI : NeZero q₀ := ⟨hq₀.ne'⟩
  have hunit : IsUnit ((b₀ : ℕ) : ZMod q₀) := (ZMod.isUnit_iff_coprime b₀ q₀).mpr hcop
  have hfilter : (Finset.Ioc lo hi).filter
      (fun m => HasFactorInAll levels m ∧ m % q₀ = b₀)
      = ((Finset.Ioc lo hi).filter (HasFactorInAll levels)).filter
          (fun m : ℕ => ((m : ZMod q₀)) = ((b₀ : ℕ) : ZMod q₀)) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun m _ => ?_
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hb₀]
  rw [hfilter]
  exact sum_filter_residue_eq_char_avg q₀ _ g ((b₀ : ℕ) : ZMod q₀) hunit

/-- **The unit class, bounded by the twisted block sums** (Track R, R6-3): the
character values at the unit `b₀⁻¹` have norm at most one. -/
theorem norm_sum_restricted_unit_class_le (g : ℕ → ℂ) (levels : List (Finset ℕ))
    (q₀ b₀ lo hi : ℕ) (hq₀ : 0 < q₀) (hb₀ : b₀ < q₀) (hcop : Nat.Coprime b₀ q₀) :
    ‖∑ m ∈ (Finset.Ioc lo hi).filter
        (fun m => HasFactorInAll levels m ∧ m % q₀ = b₀), g m‖
      ≤ (1 / (q₀.totient : ℝ)) * ∑ χ : DirichletCharacter ℂ q₀,
          ‖∑ m ∈ (Finset.Ioc lo hi).filter (HasFactorInAll levels), χ m * g m‖ := by
  classical
  rw [sum_restricted_unit_class_eq_char_avg g levels q₀ b₀ lo hi hq₀ hb₀ hcop, norm_mul]
  have hφ : ‖(1 / (q₀.totient : ℂ))‖ = 1 / (q₀.totient : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [hφ]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun χ _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)

/-- **The `𝒮`-restricted block at a rational frequency, in classes and characters**
(Track R, R6-3; the composite of R6-2b and the unit-class expansion).

For a `1`-bounded completely multiplicative `g` and a modulus `q` below every level,
the restricted block sum twisted by `e(m·a/q)` is at most the sum over the `q`
residue classes `b` of the `1/φ(q/d₀)`-weighted character sums of the twisted
restricted sums over the dilated block `(⌊lo/d₀⌋, ⌊hi/d₀⌋]`, `d₀ = gcd(b, q)`.  The
factor `g(d₀)` has been bounded by `1` and the class phases by `1`.  Nothing on the
right-hand side remembers `a`: each term is the plain `𝒮`-restricted block sum of the
twist `χ·g`, the object A.2 bounds in mean square. -/
theorem norm_restricted_block_ratl_le_char_sum (g : ℕ → ℂ)
    (hg : CompletelyMultiplicativeC g) (hb : ∀ m, ‖g m‖ ≤ 1)
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ p ∈ P, p.Prime)
    (q : ℕ) (hq : 0 < q) (hql : ∀ P ∈ levels, ∀ p ∈ P, ¬ p ∣ q) (a : ℤ) (lo hi : ℕ) :
    ‖∑ m ∈ (Finset.Ioc lo hi).filter (HasFactorInAll levels),
        g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)
          * (((a : ℝ) / (q : ℝ) : ℝ) : ℂ))‖
      ≤ ∑ b ∈ Finset.range q, (1 / ((q / Nat.gcd b q).totient : ℝ))
          * ∑ χ : DirichletCharacter ℂ (q / Nat.gcd b q),
              ‖∑ m' ∈ (Finset.Ioc (lo / Nat.gcd b q) (hi / Nat.gcd b q)).filter
                  (HasFactorInAll levels), χ m' * g m'‖ := by
  classical
  rw [sum_mul_exp_ratl_eq_sum_residues _ _ a q hq]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun b hbq => ?_)
  have hbq' : b < q := Finset.mem_range.mp hbq
  have hunit : ‖Complex.exp (2 * Real.pi * Complex.I * (b : ℂ)
      * (((a : ℝ) / (q : ℝ) : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * (b : ℂ)
        * (((a : ℝ) / (q : ℝ) : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  rw [norm_mul, hunit, one_mul, Finset.filter_filter,
    sum_restricted_residue_eq_gcd_dilate g hg levels hlv q hq hql b lo hi, norm_mul]
  have hd0 : 0 < Nat.gcd b q := Nat.gcd_pos_of_pos_right b hq
  have hq₀ : 0 < q / Nat.gcd b q :=
    Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right b q)) hd0
  have hb₀ : b / Nat.gcd b q < q / Nat.gcd b q :=
    Nat.div_lt_div_of_lt_of_dvd (Nat.gcd_dvd_right b q) hbq'
  have hcop : Nat.Coprime (b / Nat.gcd b q) (q / Nat.gcd b q) :=
    Nat.coprime_div_gcd_div_gcd hd0
  refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (hb _)) ?_
  exact norm_sum_restricted_unit_class_le g levels _ _ _ _ hq₀ hb₀ hcop

/-- The character twist `n ↦ χ(n)·g(n)` of a completely multiplicative function is
completely multiplicative (Track R, R6-3). -/
theorem completelyMultiplicativeC_charMul (g : ℕ → ℂ) (hg : CompletelyMultiplicativeC g)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    CompletelyMultiplicativeC (fun n => χ n * g n) := by
  intro a b ha hb
  dsimp only
  rw [hg a b ha hb, Nat.cast_mul, map_mul]
  ring

/-- The character twist of a `1`-bounded function is `1`-bounded (Track R, R6-3). -/
theorem norm_charMul_le_one (g : ℕ → ℂ) (hb : ∀ m, ‖g m‖ ≤ 1) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (m : ℕ) : ‖χ m * g m‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (DirichletCharacter.norm_le_one χ _) (norm_nonneg _) (hb m)

/-- The character twist takes the value `1` at `1` (Track R, R6-3). -/
theorem charMul_one (g : ℕ → ℂ) (hg1 : g 1 = 1) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    χ ((1 : ℕ) : ZMod q) * g 1 = 1 := by
  rw [hg1, Nat.cast_one, map_one, one_mul]

/-- **The twisted distance is a distance of `g`** (Track R, R6-3): the pretentious
distance from `χ·g` to the twist `ψ(n)·n^{it}` mod `q'` equals the distance from `g`
to the composite twist `(ψ·χ̄)(n)·n^{it}` mod `q'·q₀`, prime by prime
(`changeLevel_mul_changeLevel_inv_apply_natCast`). -/
theorem pretentiousDistSq_charMul_eq (g : ℕ → ℂ) {q₀ q' : ℕ}
    (χ : DirichletCharacter ℂ q₀) (ψ : DirichletCharacter ℂ q') (t : ℝ) (N : ℕ) :
    pretentiousDistSq (fun n : ℕ => χ n * g n) (charTwist q' ψ t) N
      = pretentiousDistSq g (charTwist (q' * q₀)
          (DirichletCharacter.changeLevel (dvd_mul_right q' q₀) ψ
            * (DirichletCharacter.changeLevel (dvd_mul_left q₀ q') χ)⁻¹) t) N := by
  unfold pretentiousDistSq
  refine Finset.sum_congr rfl fun p _ => ?_
  have hkey : (fun n : ℕ => χ n * g n) p * (starRingEnd ℂ) (charTwist q' ψ t p)
      = g p * (starRingEnd ℂ) (charTwist (q' * q₀)
          (DirichletCharacter.changeLevel (dvd_mul_right q' q₀) ψ
            * (DirichletCharacter.changeLevel (dvd_mul_left q₀ q') χ)⁻¹) t p) := by
    simp only [charTwist]
    rw [changeLevel_mul_changeLevel_inv_apply_natCast]
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [hkey]

/-- **Non-pretentiousness passes to the twist `χ·g`** (Track R, R6-3): if `g` is
non-pretentious at strength `A`, then `χ·g` (for `χ` mod `q₀`) is non-pretentious at
any strength `A'` with `A'·q₀ ≤ A` — a twist mod `q' ≤ A'` of `χ·g` is a twist mod
`q'·q₀ ≤ A` of `g`, and the frequency range `|t| ≤ A'x ≤ Ax` shrinks.  In the assembly
`q₀ ∣ q ≤ C(log H)^B` and `A₀` is chosen after `H`, so the loss is absorbed. -/
theorem nonPretentiousAt_charMul (g : ℕ → ℂ) {A A' : ℝ} {x : ℕ} (h : NonPretentiousAt g A x)
    {q₀ : ℕ} (hq₀ : 0 < q₀) (χ : DirichletCharacter ℂ q₀) (hA'0 : 0 ≤ A')
    (hA' : A' * q₀ ≤ A) :
    NonPretentiousAt (fun n => χ n * g n) A' x := by
  intro q' ψ t hq' ht
  have hq₀1 : (1 : ℝ) ≤ q₀ := by exact_mod_cast hq₀
  have hAA' : A' ≤ A := le_trans (le_mul_of_one_le_right hA'0 hq₀1) hA'
  have hqq : ((q' * q₀ : ℕ) : ℝ) ≤ A := by
    push_cast
    calc (q' : ℝ) * q₀ ≤ A' * q₀ := mul_le_mul_of_nonneg_right hq' (by positivity)
      _ ≤ A := hA'
  have ht' : |t| ≤ A * x :=
    le_trans ht (mul_le_mul_of_nonneg_right hAA' (Nat.cast_nonneg x))
  rw [pretentiousDistSq_charMul_eq]
  exact le_trans hAA' (h (q' * q₀) _ t hqq ht')

/-! ### R6-4: the phase freeze on a filtered block -/

/-- **The phase freeze on a filtered block** (Track R, R6-4).

At `α = β + δ` the twisted sum over `(n, n+H] ∩ {p}` is cut into the sub-blocks
`(n + kℓ, n + min((k+1)ℓ, H)] ∩ {p}`, `k ≤ ⌊H/ℓ⌋`, on each of which the slowly varying
phase `e(mδ)` is frozen at the anchor `n + kℓ + 1` at cost `2π|δ|ℓ` per term
(`norm_sum_mul_exp_freeze_sub_le`).  The frozen phases are unimodular and the
sub-blocks partition the block, so the total cost is `#(block ∩ {p})·2π|δ|ℓ ≤ H·2π|δ|ℓ`.
On the major arcs `|δ| ≤ C(log H)^B/(Hq)`, so with `ℓ ≍ εHq/(C(log H)^B)` this is
`O(εH)` per `n` (report §8 R6-4). -/
theorem norm_filter_block_twisted_le_subblocks_add (p : ℕ → Prop) [DecidablePred p]
    (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1) (n H ℓ : ℕ) (hℓ : 0 < ℓ) (β δ : ℝ) :
    ‖∑ m ∈ (Finset.Ioc n (n + H)).filter p,
        h m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * ((β + δ : ℝ) : ℂ))‖
      ≤ (∑ k ∈ Finset.range (H / ℓ + 1),
          ‖∑ m ∈ (Finset.Ioc (n + k * ℓ) (n + min ((k + 1) * ℓ) H)).filter p,
              h m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (β : ℂ))‖)
        + (H : ℝ) * (2 * Real.pi * |δ| * ℓ) := by
  classical
  set S := (Finset.Ioc n (n + H)).filter p with hS
  set h' : ℕ → ℂ := fun m => h m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (β : ℂ))
    with hh'
  have hunit : ∀ x : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ) * (β : ℂ))‖ = 1 := by
    intro x
    rw [Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * (x : ℂ) * (β : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  have hb' : ∀ m, ‖h' m‖ ≤ 1 := by
    intro m
    simp only [hh']
    rw [norm_mul]
    have := hunit (m : ℝ)
    rw [Complex.ofReal_natCast] at this
    rw [this, mul_one]
    exact hb m
  -- split the phase `e(m(β+δ)) = e(mβ)·e(mδ)`
  have hsplit : ∀ m : ℕ,
      h m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * ((β + δ : ℝ) : ℂ))
        = h' m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ)) := by
    intro m
    have hexp : Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * ((β + δ : ℝ) : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (β : ℂ))
          * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp, hh']
    ring
  simp_rw [hsplit]
  -- the fibre partition by `k = (m − n − 1)/ℓ`
  have hmaps : ∀ m ∈ S, (m - n - 1) / ℓ ∈ Finset.range (H / ℓ + 1) := by
    intro m hm
    have hm' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1
    rw [Finset.mem_range]
    have : (m - n - 1) / ℓ ≤ H / ℓ := Nat.div_le_div_right (by omega)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- the fibres are the sub-blocks
  have hfib : ∀ k, S.filter (fun m => (m - n - 1) / ℓ = k)
      = (Finset.Ioc (n + k * ℓ) (n + min ((k + 1) * ℓ) H)).filter p := by
    intro k
    ext m
    simp only [hS, Finset.mem_filter, Finset.mem_Ioc]
    have hK1 : (k + 1) * ℓ = k * ℓ + ℓ := Nat.succ_mul k ℓ
    have hlow : ∀ m, (m - n - 1) / ℓ = k → k * ℓ ≤ m - n - 1 := fun m hd => by
      rw [← hd]; exact Nat.div_mul_le_self _ _
    have hhigh : ∀ m, (m - n - 1) / ℓ = k → m - n - 1 < k * ℓ + ℓ := fun m hd => by
      rw [← hd]; exact Nat.lt_div_mul_add hℓ
    have hdiv : ∀ m, k * ℓ ≤ m - n - 1 → m - n - 1 < k * ℓ + ℓ → (m - n - 1) / ℓ = k :=
      fun m h1 h2 => Nat.div_eq_of_lt_le h1 (by rw [Nat.succ_mul]; exact h2)
    generalize k * ℓ = K at hK1 hlow hhigh hdiv ⊢
    rw [hK1]
    constructor
    · rintro ⟨⟨⟨hn, hH⟩, hp⟩, hd⟩
      have h1 := hlow m hd
      have h2 := hhigh m hd
      exact ⟨⟨by omega, by omega⟩, hp⟩
    · rintro ⟨⟨hlo, hhi⟩, hp⟩
      exact ⟨⟨⟨by omega, by omega⟩, hp⟩, hdiv m (by omega) (by omega)⟩
  -- the per-fibre freeze
  have hfibbound : ∀ k ∈ Finset.range (H / ℓ + 1),
      ‖∑ m ∈ S.filter (fun m => (m - n - 1) / ℓ = k),
          h' m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ))‖
        ≤ ‖∑ m ∈ (Finset.Ioc (n + k * ℓ) (n + min ((k + 1) * ℓ) H)).filter p, h' m‖
          + ((S.filter (fun m => (m - n - 1) / ℓ = k)).card : ℝ)
              * (2 * Real.pi * |δ| * ℓ) := by
    intro k _
    have hB : ∀ m ∈ S.filter (fun m => (m - n - 1) / ℓ = k),
        (n + k * ℓ + 1) ≤ m ∧ m < (n + k * ℓ + 1) + ℓ := by
      intro m hm
      rw [hfib k, Finset.mem_filter, Finset.mem_Ioc] at hm
      have hK1 : (k + 1) * ℓ = k * ℓ + ℓ := Nat.succ_mul k ℓ
      have hm1 := hm.1
      generalize k * ℓ = K at hK1 hm1 ⊢
      rw [hK1] at hm1
      omega
    have hfreeze := norm_sum_mul_exp_freeze_sub_le
      (S.filter (fun m => (m - n - 1) / ℓ = k)) (n + k * ℓ + 1) ℓ hB h' hb' δ
    have hanchor : ‖Complex.exp (2 * Real.pi * Complex.I * ((n + k * ℓ + 1 : ℕ) : ℂ)
        * (δ : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (2 * Real.pi * Complex.I * ((n + k * ℓ + 1 : ℕ) : ℂ) * (δ : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, Real.exp_zero]
    calc ‖∑ m ∈ S.filter (fun m => (m - n - 1) / ℓ = k),
            h' m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ))‖
        ≤ ‖Complex.exp (2 * Real.pi * Complex.I * ((n + k * ℓ + 1 : ℕ) : ℂ) * (δ : ℂ))
              * ∑ m ∈ S.filter (fun m => (m - n - 1) / ℓ = k), h' m‖
          + ‖(∑ m ∈ S.filter (fun m => (m - n - 1) / ℓ = k),
                h' m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ)))
              - Complex.exp (2 * Real.pi * Complex.I * ((n + k * ℓ + 1 : ℕ) : ℂ) * (δ : ℂ))
                * ∑ m ∈ S.filter (fun m => (m - n - 1) / ℓ = k), h' m‖ :=
          norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖∑ m ∈ (Finset.Ioc (n + k * ℓ) (n + min ((k + 1) * ℓ) H)).filter p, h' m‖
          + ((S.filter (fun m => (m - n - 1) / ℓ = k)).card : ℝ)
              * (2 * Real.pi * |δ| * ℓ) := by
          rw [norm_mul, hanchor, one_mul, hfib k]
          rw [hfib k] at hfreeze
          exact add_le_add le_rfl hfreeze
  -- the fibre cardinalities sum to `#S ≤ H`
  have hcount : ∑ k ∈ Finset.range (H / ℓ + 1),
      ((S.filter (fun m => (m - n - 1) / ℓ = k)).card : ℝ) ≤ H := by
    have hmapsTo : Set.MapsTo (fun m => (m - n - 1) / ℓ) ↑S ↑(Finset.range (H / ℓ + 1)) :=
      fun m hm => hmaps m hm
    have hcard := Finset.card_eq_sum_card_fiberwise hmapsTo
    have hSH : S.card ≤ H := by
      calc S.card ≤ (Finset.Ioc n (n + H)).card := Finset.card_filter_le _ _
        _ = H := by rw [Nat.card_Ioc]; omega
    rw [hcard] at hSH
    exact_mod_cast hSH
  calc ‖∑ k ∈ Finset.range (H / ℓ + 1), ∑ m ∈ S.filter (fun m => (m - n - 1) / ℓ = k),
          h' m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ))‖
      ≤ ∑ k ∈ Finset.range (H / ℓ + 1), ‖∑ m ∈ S.filter (fun m => (m - n - 1) / ℓ = k),
          h' m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (H / ℓ + 1),
          (‖∑ m ∈ (Finset.Ioc (n + k * ℓ) (n + min ((k + 1) * ℓ) H)).filter p, h' m‖
            + ((S.filter (fun m => (m - n - 1) / ℓ = k)).card : ℝ)
                * (2 * Real.pi * |δ| * ℓ)) := Finset.sum_le_sum hfibbound
    _ = (∑ k ∈ Finset.range (H / ℓ + 1),
          ‖∑ m ∈ (Finset.Ioc (n + k * ℓ) (n + min ((k + 1) * ℓ) H)).filter p, h' m‖)
        + (∑ k ∈ Finset.range (H / ℓ + 1),
            ((S.filter (fun m => (m - n - 1) / ℓ = k)).card : ℝ)) * (2 * Real.pi * |δ| * ℓ) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (∑ k ∈ Finset.range (H / ℓ + 1),
          ‖∑ m ∈ (Finset.Ioc (n + k * ℓ) (n + min ((k + 1) * ℓ) H)).filter p, h' m‖)
        + (H : ℝ) * (2 * Real.pi * |δ| * ℓ) := by
        gcongr

/-! ### R6-5: the `L¹` form of A.2 on a block, and the `d`-to-one reindexing -/

/-- **A.2 in log-averaged `L¹` form on blocks of ratio at most `3`** (Track R, R6-5).

If the mean square `∑_{(A, A+J]} W(n)²/n ≤ ε²h²∑_{(A, A+J]} 1/n` holds on every
dyadic block `A₀ ≤ A`, `J ≤ A` (the shape of `SliceMeanSquareA2` at `s = 1`), then on
any block `(a, b]` with `A₀ ≤ a` and `b ≤ 3a` the log-averaged `L¹` sum is at most
`εh·∑ 1/n` — Cauchy–Schwarz (`sum_div_le_sqrt_mul_sqrt`) on each of the at most two
dyadic pieces `(a, 2a]`, `(2a, b]`.  The reindexed ranges of `sum_div_comp_div_le` have
ratio just above `2`, which is why the block is allowed ratio `3`. -/
theorem logavg_le_of_meanSquare_dyadic (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n)
    (ε h : ℝ) (hε : 0 ≤ ε) (hh : 0 ≤ h) (A₀ : ℕ)
    (hA2 : ∀ A J : ℕ, A₀ ≤ A → J ≤ A →
      ∑ n ∈ Finset.Ioc A (A + J), (W n)^2 / n
        ≤ ε^2 * h^2 * ∑ n ∈ Finset.Ioc A (A + J), (1:ℝ)/n)
    (a b : ℕ) (ha : A₀ ≤ a) (hb : b ≤ 3 * a) :
    ∑ n ∈ Finset.Ioc a b, W n / n ≤ ε * h * ∑ n ∈ Finset.Ioc a b, (1:ℝ)/n := by
  classical
  -- one dyadic block
  have hsingle : ∀ a b : ℕ, A₀ ≤ a → a ≤ b → b ≤ 2 * a →
      ∑ n ∈ Finset.Ioc a b, W n / n ≤ ε * h * ∑ n ∈ Finset.Ioc a b, (1:ℝ)/n := by
    intro a b ha hab hb2
    have hsq : ∑ n ∈ Finset.Ioc a b, (W n)^2 / n
        ≤ ε^2 * h^2 * ∑ n ∈ Finset.Ioc a b, (1:ℝ)/n := by
      have := hA2 a (b - a) ha (by omega)
      rwa [Nat.add_sub_of_le hab] at this
    have h1 : (0:ℝ) ≤ ∑ n ∈ Finset.Ioc a b, (1:ℝ)/n :=
      Finset.sum_nonneg fun n _ => by positivity
    have hL : (0:ℝ) ≤ ∑ n ∈ Finset.Ioc a b, W n / n :=
      Finset.sum_nonneg fun n _ => div_nonneg (hW n) (Nat.cast_nonneg n)
    have hεh : (0:ℝ) ≤ ε * h := mul_nonneg hε hh
    -- Cauchy–Schwarz with the weights `1/√n`, `W n/√n`
    have hcs : (∑ n ∈ Finset.Ioc a b, W n / n)^2
        ≤ (∑ n ∈ Finset.Ioc a b, (1:ℝ)/n) * ∑ n ∈ Finset.Ioc a b, (W n)^2 / n := by
      have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ioc a b)
        (fun n => 1 / Real.sqrt n) (fun n => W n / Real.sqrt n)
      have hn0 : ∀ n ∈ Finset.Ioc a b, (0:ℝ) < n := fun n hn => by
        have := (Finset.mem_Ioc.mp hn).1
        exact_mod_cast (by omega : 0 < n)
      have hprod : ∀ n ∈ Finset.Ioc a b,
          1 / Real.sqrt n * (W n / Real.sqrt n) = W n / n := fun n hn => by
        rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (hn0 n hn).le]
      have hfsq : ∀ n ∈ Finset.Ioc a b, (1 / Real.sqrt n)^2 = (1:ℝ)/n := fun n hn => by
        rw [div_pow, one_pow, Real.sq_sqrt (hn0 n hn).le]
      have hgsq : ∀ n ∈ Finset.Ioc a b, (W n / Real.sqrt n)^2 = (W n)^2 / n := fun n hn => by
        rw [div_pow, Real.sq_sqrt (hn0 n hn).le]
      rwa [Finset.sum_congr rfl hprod, Finset.sum_congr rfl hfsq,
        Finset.sum_congr rfl hgsq] at hcs0
    have hsq' : (∑ n ∈ Finset.Ioc a b, W n / n)^2
        ≤ (ε * h * ∑ n ∈ Finset.Ioc a b, (1:ℝ)/n)^2 := by
      calc (∑ n ∈ Finset.Ioc a b, W n / n)^2
          ≤ (∑ n ∈ Finset.Ioc a b, (1:ℝ)/n) * ∑ n ∈ Finset.Ioc a b, (W n)^2 / n := hcs
        _ ≤ (∑ n ∈ Finset.Ioc a b, (1:ℝ)/n)
              * (ε^2 * h^2 * ∑ n ∈ Finset.Ioc a b, (1:ℝ)/n) :=
            mul_le_mul_of_nonneg_left hsq h1
        _ = (ε * h * ∑ n ∈ Finset.Ioc a b, (1:ℝ)/n)^2 := by ring
    exact (pow_le_pow_iff_left₀ hL (mul_nonneg hεh h1) two_ne_zero).mp hsq'
  rcases le_or_gt b a with hba | hab
  · -- empty block
    rw [Finset.Ioc_eq_empty (not_lt.mpr hba)]
    simp
  rcases le_or_gt b (2 * a) with hb2 | hb2
  · exact hsingle a b ha hab.le hb2
  · have h1 : a ≤ 2 * a := by omega
    have h2 : 2 * a ≤ b := hb2.le
    rw [← Finset.sum_Ioc_consecutive (fun n => W n / (n:ℝ)) h1 h2,
      ← Finset.sum_Ioc_consecutive (fun n => (1:ℝ) / (n:ℝ)) h1 h2, mul_add]
    exact add_le_add (hsingle a (2 * a) ha h1 le_rfl)
      (hsingle (2 * a) b (by omega) h2 (by omega))

/-- **A `1`-bounded filtered block sum is at most the block length** (Track R, R6-5):
the trivial bound, used for the partial last sub-block of the freeze. -/
theorem norm_filter_block_le_card (p : ℕ → Prop) [DecidablePred p] (h : ℕ → ℂ)
    (hb : ∀ m, ‖h m‖ ≤ 1) (lo hi : ℕ) :
    ‖∑ m ∈ (Finset.Ioc lo hi).filter p, h m‖ ≤ ((hi - lo : ℕ) : ℝ) := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ m ∈ (Finset.Ioc lo hi).filter p, ‖h m‖
      ≤ ∑ m ∈ (Finset.Ioc lo hi).filter p, (1:ℝ) := Finset.sum_le_sum fun m _ => hb m
    _ = (((Finset.Ioc lo hi).filter p).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ((Finset.Ioc lo hi).card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
    _ = ((hi - lo : ℕ) : ℝ) := by rw [Nat.card_Ioc]

/-- **The `d`-to-one reindexing of a log-averaged sum** (Track R, R6-5).

Under `n ↦ n' = (n + c)/d` the block `(A, B]` maps into `[⌊(A+c)/d⌋, ⌊(B+c)/d⌋]`, each
`n'` has at most `d` preimages (they are distinguished by `(n + c) mod d`), and
`d·n' ≤ n + c ≤ (4/3)·n` once `3c ≤ A`; hence

  `∑_{n ∈ (A, B]} f((n+c)/d)/n ≤ (4/3)·∑_{n' ∈ (⌊(A+c)/d⌋ − 1, ⌊(B+c)/d⌋]} f(n')/n'`

for nonnegative `f`.  In the assembly `c = kℓ ≤ H ≤ A/3`, `d = gcd(b, q) ≤ q ≤ A`, and
`f(n')` is the `𝒮`-restricted window sum of the twist at `n'`, so the right-hand side
is the log average A.2 bounds. -/
theorem sum_div_comp_div_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (A B c d : ℕ) (hd : 0 < d)
    (hdA : d ≤ A) (hcA : 3 * c ≤ A) :
    ∑ n ∈ Finset.Ioc A B, f ((n + c) / d) / n
      ≤ (4/3) * ∑ n' ∈ Finset.Ioc ((A + c) / d - 1) ((B + c) / d), f n' / n' := by
  classical
  have hAd1 : 1 ≤ (A + c) / d := by
    rw [Nat.one_le_div_iff hd]
    omega
  have hmaps : ∀ n ∈ Finset.Ioc A B,
      (n + c) / d ∈ Finset.Ioc ((A + c) / d - 1) ((B + c) / d) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    have h1 : (A + c) / d ≤ (n + c) / d := Nat.div_le_div_right (by omega)
    have h2 : (n + c) / d ≤ (B + c) / d := Nat.div_le_div_right (by omega)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_le_sum fun n' hn' => ?_
  have hn'1 : 1 ≤ n' := by
    rw [Finset.mem_Ioc] at hn'
    omega
  have hn'pos : (0:ℝ) < n' := by exact_mod_cast hn'1
  -- on the fibre the summand is `f n' / n`, and `1/n ≤ (4/3)/(d n')`
  have hterm : ∀ n ∈ (Finset.Ioc A B).filter (fun n => (n + c) / d = n'),
      f ((n + c) / d) / n ≤ f n' * ((4/3) / ((d:ℝ) * n')) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hAn, _⟩, hdiv⟩ := hn
    rw [hdiv]
    have hdn : d * n' ≤ n + c := by
      rw [← hdiv, mul_comm]
      exact Nat.div_mul_le_self _ _
    have hnpos : (0:ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hkey : (d:ℝ) * n' ≤ (4/3) * n := by
      have h1 : ((d * n' : ℕ) : ℝ) ≤ ((n + c : ℕ) : ℝ) := by exact_mod_cast hdn
      have h2 : ((c : ℕ) : ℝ) * 3 ≤ (n : ℝ) := by
        have : c * 3 ≤ n := by omega
        exact_mod_cast this
      push_cast at h1
      linarith
    have hdn'pos : (0:ℝ) < (d:ℝ) * n' := by positivity
    rw [div_eq_mul_one_div (f n') (n:ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ (hf n')
    rw [div_le_div_iff₀ hnpos hdn'pos]
    linarith
  have hcard : (((Finset.Ioc A B).filter (fun n => (n + c) / d = n')).card : ℝ) ≤ d := by
    have hinj : Set.InjOn (fun n => (n + c) % d)
        ↑((Finset.Ioc A B).filter (fun n => (n + c) / d = n')) := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      have hx' := Nat.div_add_mod (x + c) d
      have hy' := Nat.div_add_mod (y + c) d
      simp only at hxy
      rw [hx.2] at hx'
      rw [hy.2] at hy'
      omega
    have hmaps' : Set.MapsTo (fun n => (n + c) % d)
        ↑((Finset.Ioc A B).filter (fun n => (n + c) / d = n')) ↑(Finset.range d) :=
      fun n _ => Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ hd))
    have := Finset.card_le_card_of_injOn _ hmaps' hinj
    rw [Finset.card_range] at this
    exact_mod_cast this
  calc ∑ n ∈ (Finset.Ioc A B).filter (fun n => (n + c) / d = n'), f ((n + c) / d) / n
      ≤ ∑ n ∈ (Finset.Ioc A B).filter (fun n => (n + c) / d = n'),
          f n' * ((4/3) / ((d:ℝ) * n')) := Finset.sum_le_sum hterm
    _ = (((Finset.Ioc A B).filter (fun n => (n + c) / d = n')).card : ℝ)
          * (f n' * ((4/3) / ((d:ℝ) * n'))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d : ℝ) * (f n' * ((4/3) / ((d:ℝ) * n'))) := by
        refine mul_le_mul_of_nonneg_right hcard ?_
        have := hf n'
        positivity
    _ = (4/3) * (f n' / n') := by
        field_simp

/-! ### R6-6a: the freeze trimmed to full windows -/

/-- **The freeze, trimmed to full windows** (Track R, R6-6a).

On a filtered block `(n, n+L]` twisted by `e(mδ)`, cut off the tail
`(n + h₀⌊L/h₀⌋, n + L]` (fewer than `h₀` terms, `norm_filter_block_le_card`), then freeze
the phase on the remaining block of length `h₀⌊L/h₀⌋` in sub-blocks of length `h₀`
(`norm_filter_block_twisted_le_subblocks_add`).  Because the trimmed length is a multiple
of `h₀`, every sub-block is either the **full** window `(n + kh₀, n + kh₀ + h₀]` or
empty, and the sum may be extended to any range `K > L/h₀`.  The result is the shape the
A.2 input is stated for: plain filtered sums over windows of one fixed length `h₀`. -/
theorem norm_twisted_filter_block_le_windows_add (p : ℕ → Prop) [DecidablePred p]
    (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1) (n L h₀ K : ℕ) (hh₀ : 0 < h₀) (hK : L / h₀ < K)
    (δ : ℝ) :
    ‖∑ m ∈ (Finset.Ioc n (n + L)).filter p,
        h m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ))‖
      ≤ (∑ k ∈ Finset.range K,
          ‖∑ m ∈ (Finset.Ioc (n + k * h₀) (n + k * h₀ + h₀)).filter p, h m‖)
        + (h₀ : ℝ) + (L : ℝ) * (2 * Real.pi * |δ| * h₀) := by
  classical
  set H' := h₀ * (L / h₀) with hH'
  have hH'L : H' ≤ L := Nat.mul_div_le L h₀
  have hLH' : L - H' < h₀ := by
    have := Nat.div_add_mod L h₀
    have := Nat.mod_lt L hh₀
    omega
  have hH'div : H' / h₀ = L / h₀ := by
    rw [hH']; exact Nat.mul_div_cancel_left _ hh₀
  -- split off the tail
  have hsplit : ∑ m ∈ (Finset.Ioc n (n + L)).filter p,
      h m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ))
      = (∑ m ∈ (Finset.Ioc n (n + H')).filter p,
          h m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ)))
        + ∑ m ∈ (Finset.Ioc (n + H') (n + L)).filter p,
          h m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ)) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
    exact (Finset.sum_Ioc_consecutive _ (Nat.le_add_right n H') (by omega)).symm
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  -- the tail, trivially
  have hb' : ∀ m, ‖h m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ))‖ ≤ 1 := by
    intro m
    rw [norm_mul, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero, mul_one]
    exact hb m
  have htail : ‖∑ m ∈ (Finset.Ioc (n + H') (n + L)).filter p,
      h m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ))‖ ≤ (h₀ : ℝ) := by
    refine le_trans (norm_filter_block_le_card p _ hb' (n + H') (n + L)) ?_
    have : n + L - (n + H') < h₀ := by omega
    exact_mod_cast this.le
  -- the freeze on the trimmed block, at `β = 0`
  have hfreeze := norm_filter_block_twisted_le_subblocks_add p h hb n H' h₀ hh₀ 0 δ
  simp only [zero_add, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hfreeze
  -- every sub-block is a full window or empty
  have hsub : ∀ k ∈ Finset.range (H' / h₀ + 1),
      ‖∑ m ∈ (Finset.Ioc (n + k * h₀) (n + min ((k + 1) * h₀) H')).filter p, h m‖
        ≤ ‖∑ m ∈ (Finset.Ioc (n + k * h₀) (n + k * h₀ + h₀)).filter p, h m‖ := by
    intro k _
    rcases le_or_gt ((k + 1) * h₀) H' with hk | hk
    · rw [min_eq_left hk]
      have : n + (k + 1) * h₀ = n + k * h₀ + h₀ := by ring
      rw [this]
    · rw [min_eq_right hk.le]
      have hkH' : H' ≤ k * h₀ := by
        have h1 : L / h₀ < k + 1 := by
          by_contra hcon
          push_neg at hcon
          have : (k + 1) * h₀ ≤ h₀ * (L / h₀) := by
            rw [mul_comm]
            exact Nat.mul_le_mul_left h₀ hcon
          omega
        rw [hH', mul_comm k h₀]
        exact Nat.mul_le_mul_left h₀ (by omega : L / h₀ ≤ k)
      have hempty : Finset.Ioc (n + k * h₀) (n + H') = ∅ :=
        Finset.Ioc_eq_empty (by omega)
      rw [hempty, Finset.filter_empty, Finset.sum_empty, norm_zero]
      exact norm_nonneg _
  have hrange : Finset.range (H' / h₀ + 1) ⊆ Finset.range K := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  calc ‖∑ m ∈ (Finset.Ioc n (n + H')).filter p,
          h m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ))‖
        + ‖∑ m ∈ (Finset.Ioc (n + H') (n + L)).filter p,
          h m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ))‖
      ≤ ((∑ k ∈ Finset.range (H' / h₀ + 1),
            ‖∑ m ∈ (Finset.Ioc (n + k * h₀) (n + min ((k + 1) * h₀) H')).filter p, h m‖)
          + (H' : ℝ) * (2 * Real.pi * |δ| * h₀)) + (h₀ : ℝ) := add_le_add hfreeze htail
    _ ≤ ((∑ k ∈ Finset.range K,
            ‖∑ m ∈ (Finset.Ioc (n + k * h₀) (n + k * h₀ + h₀)).filter p, h m‖)
          + (L : ℝ) * (2 * Real.pi * |δ| * h₀)) + (h₀ : ℝ) := by
        gcongr ?_ + ?_ + _
        · refine le_trans (Finset.sum_le_sum hsub) ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg hrange
            (fun k _ _ => norm_nonneg _)
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hH'L) (by positivity)
    _ = _ := by ring

/-! ### R6-6b: the window at `n`, in classes, characters and full windows -/

/-- **The `𝒮`-restricted window at `n`, in classes, characters and full `h₀`-windows**
(Track R, R6-6b).

For a `1`-bounded completely multiplicative `g`, a modulus `q` below every level and
the arc frequency `a/q + δ`: the window sum over `(n, n+H] ∩ 𝒮` is split into the `q`
classes (`sum_mul_exp_ratl_eq_sum_residues`, the arc phase riding along), each class
is dilated by `d₀ = gcd(b, q)` (`sum_restricted_residue_mul_eq_gcd_dilate`, the phase
becoming `e(m'·d₀δ)`), expanded in characters mod `q/d₀`
(`norm_sum_restricted_unit_class_le`), and the phase is frozen on the dilated block
`(⌊n/d₀⌋, ⌊(n+H)/d₀⌋]` in full windows of length `h₀`
(`norm_twisted_filter_block_le_windows_add`, range `K ≥ ⌊H/h₀⌋ + 2`, uniform in `n`
and in the class).  What remains is `∑_b (1/φ) ∑_χ` of: the `K` window sums
`‖∑_{(⌊n/d₀⌋ + kh₀, ⌊n/d₀⌋ + kh₀ + h₀] ∩ 𝒮} χ(m')g(m')‖`, the trimmed tail `h₀`, and the
freeze cost `L_b·2π|d₀δ|h₀` with `L_b = ⌊(n+H)/d₀⌋ − ⌊n/d₀⌋ ≤ H + 1`. -/
theorem norm_restricted_window_le_char_windows (g : ℕ → ℂ)
    (hg : CompletelyMultiplicativeC g) (hb : ∀ m, ‖g m‖ ≤ 1)
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ p ∈ P, p.Prime)
    (q : ℕ) (hq : 0 < q) (hql : ∀ P ∈ levels, ∀ p ∈ P, ¬ p ∣ q) (a : ℤ) (δ : ℝ)
    (n H h₀ K : ℕ) (hh₀ : 0 < h₀) (hK : H / h₀ + 2 ≤ K) :
    ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
        g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)
          * (((a : ℝ) / (q : ℝ) + δ : ℝ) : ℂ))‖
      ≤ ∑ b ∈ Finset.range q, (1 / ((q / Nat.gcd b q).totient : ℝ))
          * ∑ χ : DirichletCharacter ℂ (q / Nat.gcd b q),
              ((∑ k ∈ Finset.range K,
                ‖∑ m' ∈ (Finset.Ioc (n / Nat.gcd b q + k * h₀)
                    (n / Nat.gcd b q + k * h₀ + h₀)).filter (HasFactorInAll levels),
                  χ m' * g m'‖)
              + (h₀ : ℝ)
              + (((n + H) / Nat.gcd b q - n / Nat.gcd b q : ℕ) : ℝ)
                  * (2 * Real.pi * |(Nat.gcd b q : ℝ) * δ| * h₀)) := by
  classical
  set S := (Finset.Ioc n (n + H)).filter (HasFactorInAll levels) with hS
  -- split the phase into the rational part and the arc part
  have hphase : ∀ m : ℕ,
      g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)
          * (((a : ℝ) / (q : ℝ) + δ : ℝ) : ℂ))
        = (g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ)))
          * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (((a : ℝ) / (q : ℝ) : ℝ) : ℂ)) := by
    intro m
    have hexp : Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)
        * (((a : ℝ) / (q : ℝ) + δ : ℝ) : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (δ : ℂ))
          * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (((a : ℝ) / (q : ℝ) : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  simp_rw [hphase]
  rw [sum_mul_exp_ratl_eq_sum_residues S _ a q hq]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun b hbq => ?_)
  have hbq' : b < q := Finset.mem_range.mp hbq
  have hunit : ‖Complex.exp (2 * Real.pi * Complex.I * (b : ℂ)
      * (((a : ℝ) / (q : ℝ) : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * (b : ℂ)
        * (((a : ℝ) / (q : ℝ) : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  rw [norm_mul, hunit, one_mul, hS, Finset.filter_filter,
    sum_restricted_residue_mul_eq_gcd_dilate g hg levels hlv q hq hql _ b n (n + H), norm_mul]
  -- the class data
  set d := Nat.gcd b q with hd
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right b hq
  have hdq : d ∣ q := Nat.gcd_dvd_right b q
  have hq₀ : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
  have hb₀ : b / d < q / d := Nat.div_lt_div_of_lt_of_dvd hdq hbq'
  have hcop : Nat.Coprime (b / d) (q / d) := Nat.coprime_div_gcd_div_gcd hd0
  refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (hb _)) ?_
  refine le_trans (norm_sum_restricted_unit_class_le _ levels (q / d) (b / d)
    (n / d) ((n + H) / d) hq₀ hb₀ hcop) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => ?_) (by positivity)
  -- per character: the dilated phase, then the trimmed freeze
  have hdil : ∀ m' : ℕ,
      χ m' * (g m' * Complex.exp (2 * Real.pi * Complex.I * ((d * m' : ℕ) : ℂ) * (δ : ℂ)))
        = (χ m' * g m')
          * Complex.exp (2 * Real.pi * Complex.I * (m' : ℂ) * (((d : ℝ) * δ : ℝ) : ℂ)) := by
    intro m'
    have hexp : 2 * Real.pi * Complex.I * ((d * m' : ℕ) : ℂ) * (δ : ℂ)
        = 2 * Real.pi * Complex.I * (m' : ℂ) * (((d : ℝ) * δ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hexp]
    ring
  simp only [hdil]
  have hL : n / d ≤ (n + H) / d := Nat.div_le_div_right (Nat.le_add_right n H)
  have hblock : Finset.Ioc (n / d) ((n + H) / d)
      = Finset.Ioc (n / d) (n / d + ((n + H) / d - n / d)) := by
    rw [Nat.add_sub_cancel' hL]
  rw [hblock]
  refine norm_twisted_filter_block_le_windows_add (HasFactorInAll levels)
    (fun m' => χ m' * g m') (norm_charMul_le_one g hb χ) (n / d) _ h₀ K hh₀ ?_ ((d : ℝ) * δ)
  -- `L / h₀ < K` uniformly: `L ≤ H + 1`
  have hL1 : (n + H) / d - n / d ≤ H + 1 := by
    have hadd := Nat.add_div (a := n) (b := H) hd0
    have hHd : H / d ≤ H := Nat.div_le_self H d
    split_ifs at hadd <;> omega
  calc ((n + H) / d - n / d) / h₀ ≤ (H + h₀) / h₀ := Nat.div_le_div_right (by omega)
    _ = H / h₀ + 1 := Nat.add_div_right H hh₀
    _ < K := by omega

/-! ### R6-6c: the reindexed A.2 average over a dyadic block -/

/-- **The reindexed A.2 average over one dyadic block** (Track R, R6-6c).

For a nonnegative window function `W` obeying the mean-square bound on every dyadic
block above `A₁` (the shape of `SliceMeanSquareA2` at `s = 1`, `εh` its per-window
scale), the log average of `W((n+c)/d)` over `(A, 2A]` is at most `4·εh`: the
`d`-to-one reindexing (`sum_div_comp_div_le`, factor `4/3`) lands in the block
`(⌊(A+c)/d⌋ − 1, ⌊(2A+c)/d⌋]`, which has ratio at most `3` once `⌊(A+c)/d⌋ ≥ 4`
(`logavg_le_of_meanSquare_dyadic`) and harmonic mass at most `3`.  In the assembly `W`
is the `𝒮`-restricted `h₀`-window sum of a twist `χ·g`, `d = gcd(b, q)` and `c = d·kh₀`;
the hypotheses `4d ≤ A`, `3c ≤ A` hold for `A ≥ 6qH`, and `A₁ + 1 ≤ ⌊A/q⌋` gives the
last one. -/
theorem sum_div_comp_div_le_of_meanSquare (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n)
    (ε h : ℝ) (hε : 0 ≤ ε) (hh : 0 ≤ h) (A₁ : ℕ)
    (hA2 : ∀ A' J : ℕ, A₁ ≤ A' → J ≤ A' →
      ∑ n ∈ Finset.Ioc A' (A' + J), (W n)^2 / n
        ≤ ε^2 * h^2 * ∑ n ∈ Finset.Ioc A' (A' + J), (1:ℝ)/n)
    (A c d : ℕ) (hd : 0 < d) (h4dA : 4 * d ≤ A) (hcA : 3 * c ≤ A)
    (hA₁ : A₁ + 1 ≤ (A + c) / d) :
    ∑ n ∈ Finset.Ioc A (2 * A), W ((n + c) / d) / n ≤ 4 * (ε * h) := by
  classical
  have hdA : d ≤ A := by omega
  have hre := sum_div_comp_div_le W hW A (2 * A) c d hd hdA hcA
  -- the reindexed block has ratio at most `3`
  have hu4 : 4 ≤ (A + c) / d := by
    calc 4 ≤ A / d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
      _ ≤ (A + c) / d := Nat.div_le_div_right (Nat.le_add_right A c)
  have hb3 : (2 * A + c) / d ≤ 3 * ((A + c) / d - 1) := by
    have h2 : 2 * A + c = A + (A + c) := by ring
    have hadd := Nat.add_div (a := A) (b := A + c) hd
    have hAd : A / d ≤ (A + c) / d := Nat.div_le_div_right (Nat.le_add_right A c)
    rw [h2]
    split_ifs at hadd <;> omega
  have ha : A₁ ≤ (A + c) / d - 1 := by omega
  have hlog := logavg_le_of_meanSquare_dyadic W hW ε h hε hh A₁ hA2
    ((A + c) / d - 1) ((2 * A + c) / d) ha hb3
  -- harmonic mass of the reindexed block
  have hharm : ∑ n' ∈ Finset.Ioc ((A + c) / d - 1) ((2 * A + c) / d), (1:ℝ) / n' ≤ 3 := by
    have hpt : ∀ n' ∈ Finset.Ioc ((A + c) / d - 1) ((2 * A + c) / d),
        (1:ℝ) / n' ≤ 1 / (((A + c) / d : ℕ) : ℝ) := by
      intro n' hn'
      rw [Finset.mem_Ioc] at hn'
      have h1 : ((A + c) / d : ℕ) ≤ n' := by omega
      have hpos : (0:ℝ) < (((A + c) / d : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < (A + c) / d)
      exact one_div_le_one_div_of_le hpos (by exact_mod_cast h1)
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
    have hcard : (2 * A + c) / d - ((A + c) / d - 1) ≤ 3 * ((A + c) / d) := by omega
    have hpos : (0:ℝ) < (((A + c) / d : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < (A + c) / d)
    calc (((2 * A + c) / d - ((A + c) / d - 1) : ℕ) : ℝ) * (1 / (((A + c) / d : ℕ) : ℝ))
        ≤ ((3 * ((A + c) / d) : ℕ) : ℝ) * (1 / (((A + c) / d : ℕ) : ℝ)) := by
          gcongr
      _ = 3 := by
          push_cast
          field_simp
  have hεh : (0:ℝ) ≤ ε * h := mul_nonneg hε hh
  calc ∑ n ∈ Finset.Ioc A (2 * A), W ((n + c) / d) / n
      ≤ (4/3) * ∑ n' ∈ Finset.Ioc ((A + c) / d - 1) ((2 * A + c) / d), W n' / n' := hre
    _ ≤ (4/3) * (ε * h * ∑ n' ∈ Finset.Ioc ((A + c) / d - 1) ((2 * A + c) / d), (1:ℝ) / n') :=
        mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ ≤ (4/3) * (ε * h * 3) := by gcongr
    _ = 4 * (ε * h) := by ring

/-! ### R6-6d: the restricted major-arc bound on one dyadic block -/

/-- **The `𝒮`-restricted major-arc bound on one dyadic block** (Track R, R6-6d).

Assume `g` is `1`-bounded and completely multiplicative, `q ≥ 1` lies below every level,
`2h₀ ≤ H`, `6qH ≤ A`, and the mean-square input holds for every twist `χ·g` (`χ` mod
`q/d`, `d ∣ q`) at the window length `h₀` on all dyadic blocks above `A₁` with
`A₁ + 1 ≤ ⌊A/q⌋`.  Then

  `∑_{n∈(A,2A]} ‖∑_{(n,n+H]∩𝒮} g(m)e(m(a/q+δ))‖/(Hn)
      ≤ (16qε' + qh₀/H + 4πq²|δ|h₀)·∑_{(A,2A]} 1/n`.

Per `n` the window is expanded by `norm_restricted_window_le_char_windows` (range
`K = ⌊H/h₀⌋ + 2`); the `n`-average is swapped inside the `∑_b (1/φ) ∑_χ`, and for each
class and character the `K` window terms are averaged by
`sum_div_comp_div_le_of_meanSquare` (`≤ 4ε'h₀/H` each, `K·h₀ ≤ 2H`), the tails give
`(h₀/H)·∑1/n`, and the freeze costs give `4πq|δ|h₀·∑1/n` (`L_b ≤ 2H`, `d ≤ q`).  The
`φ(q/d)` characters cancel the `1/φ(q/d)`, the `q` classes contribute the factor `q`, and
`∑_{(A,2A]} 1/n ≥ 1/2` absorbs the absolute main term. -/
theorem sum_restricted_window_logavg_le_of_meanSquare (g : ℕ → ℂ)
    (hg : CompletelyMultiplicativeC g) (hb : ∀ m, ‖g m‖ ≤ 1)
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ p ∈ P, p.Prime)
    (q : ℕ) (hq : 0 < q) (hql : ∀ P ∈ levels, ∀ p ∈ P, ¬ p ∣ q) (a : ℤ) (δ : ℝ)
    (A H h₀ : ℕ) (hh₀ : 0 < h₀) (h2h₀ : 2 * h₀ ≤ H) (hA : 6 * q * H ≤ A)
    (ε' : ℝ) (hε' : 0 ≤ ε') (A₁ : ℕ) (hA₁ : A₁ + 1 ≤ A / q)
    (hA2 : ∀ d : ℕ, 0 < d → d ∣ q → ∀ χ : DirichletCharacter ℂ (q / d),
      ∀ A' J : ℕ, A₁ ≤ A' → J ≤ A' →
        ∑ n' ∈ Finset.Ioc A' (A' + J),
          ‖∑ m' ∈ (Finset.Ioc n' (n' + h₀)).filter (HasFactorInAll levels),
            χ m' * g m'‖^2 / n'
          ≤ ε'^2 * (h₀ : ℝ)^2 * ∑ n' ∈ Finset.Ioc A' (A' + J), (1:ℝ)/n') :
    ∑ n ∈ Finset.Ioc A (2 * A),
        ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
          g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)
            * (((a : ℝ) / (q : ℝ) + δ : ℝ) : ℂ))‖ / ((H : ℝ) * n)
      ≤ (16 * q * ε' + q * h₀ / H + 4 * Real.pi * q^2 * |δ| * h₀)
          * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n := by
  classical
  have hH1 : 1 ≤ H := by omega
  have hA1 : 1 ≤ A := by nlinarith
  have hqA : q ≤ A := by nlinarith
  have hH0 : (0:ℝ) < H := by exact_mod_cast hH1
  have hh₀R : (0:ℝ) < h₀ := by exact_mod_cast hh₀
  set K := H / h₀ + 2 with hK
  set S := ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => by positivity
  -- the harmonic mass of a dyadic block is at least `1/2`
  have hShalf : (1:ℝ)/2 ≤ S := by
    have hpt : ∀ n ∈ Finset.Ioc A (2 * A), (1:ℝ) / ((2 * A : ℕ) : ℝ) ≤ (1:ℝ)/n := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      exact one_div_le_one_div_of_le hn0 (by exact_mod_cast hn.2)
    have := Finset.card_nsmul_le_sum _ _ _ hpt
    rw [Nat.card_Ioc, nsmul_eq_mul] at this
    have hA0 : (0:ℝ) < A := by exact_mod_cast hA1
    calc (1:ℝ)/2 = ((2 * A - A : ℕ) : ℝ) * (1 / ((2 * A : ℕ) : ℝ)) := by
          have : (2 * A - A : ℕ) = A := by omega
          rw [this]
          push_cast
          field_simp
      _ ≤ S := this
  -- the window function of a twist
  set W : ∀ d : ℕ, DirichletCharacter ℂ (q / d) → ℕ → ℝ := fun d χ n' =>
    ‖∑ m' ∈ (Finset.Ioc n' (n' + h₀)).filter (HasFactorInAll levels), χ m' * g m'‖ with hW
  -- per class and character: the `n`-average of the expanded window is at most `M`
  set M : ℝ := 8 * ε' + (h₀ / H) * S + 4 * Real.pi * q * |δ| * h₀ * S with hM
  have hclass : ∀ b ∈ Finset.range q, ∀ χ : DirichletCharacter ℂ (q / Nat.gcd b q),
      ∑ n ∈ Finset.Ioc A (2 * A),
        ((∑ k ∈ Finset.range K, W (Nat.gcd b q) χ (n / Nat.gcd b q + k * h₀))
          + (h₀ : ℝ)
          + (((n + H) / Nat.gcd b q - n / Nat.gcd b q : ℕ) : ℝ)
              * (2 * Real.pi * |(Nat.gcd b q : ℝ) * δ| * h₀)) / ((H : ℝ) * n) ≤ M := by
    intro b _
    have hd0 : 0 < Nat.gcd b q := Nat.gcd_pos_of_pos_right b hq
    have hdq : Nat.gcd b q ∣ q := Nat.gcd_dvd_right b q
    generalize hd : Nat.gcd b q = d at hd0 hdq ⊢
    intro χ
    have hdle : d ≤ q := Nat.le_of_dvd hq hdq
    have hdR : (d : ℝ) ≤ q := by exact_mod_cast hdle
    -- (I) the window terms
    have hI : ∑ n ∈ Finset.Ioc A (2 * A),
        (∑ k ∈ Finset.range K, W d χ (n / d + k * h₀)) / ((H : ℝ) * n) ≤ 8 * ε' := by
      simp_rw [Finset.sum_div]
      rw [Finset.sum_comm]
      have hk : ∀ k ∈ Finset.range K,
          ∑ n ∈ Finset.Ioc A (2 * A), W d χ (n / d + k * h₀) / ((H : ℝ) * n)
            ≤ (1 / (H : ℝ)) * (4 * (ε' * h₀)) := by
        intro k hk
        have hkK : k < K := Finset.mem_range.mp hk
        have hkh : k * h₀ ≤ 2 * H := by
          have h1 : k ≤ H / h₀ + 1 := by omega
          have h2 : (H / h₀ + 1) * h₀ ≤ H + h₀ := by
            rw [Nat.add_mul, one_mul]
            exact Nat.add_le_add_right (Nat.div_mul_le_self H h₀) h₀
          calc k * h₀ ≤ (H / h₀ + 1) * h₀ := Nat.mul_le_mul_right h₀ h1
            _ ≤ H + h₀ := h2
            _ ≤ 2 * H := by omega
        have hc : 3 * (d * (k * h₀)) ≤ A := by
          calc 3 * (d * (k * h₀)) ≤ 3 * (d * (2 * H)) :=
                Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left d hkh)
            _ = 6 * d * H := by ring
            _ ≤ 6 * q * H := by
                exact Nat.mul_le_mul_right H (Nat.mul_le_mul_left 6 hdle)
            _ ≤ A := hA
        have h4d : 4 * d ≤ A := by nlinarith
        have hA₁' : A₁ + 1 ≤ (A + d * (k * h₀)) / d := by
          calc A₁ + 1 ≤ A / q := hA₁
            _ ≤ A / d := Nat.div_le_div_left hdle hd0
            _ ≤ (A + d * (k * h₀)) / d := Nat.div_le_div_right (Nat.le_add_right _ _)
        have hre := sum_div_comp_div_le_of_meanSquare (W d χ) (fun _ => norm_nonneg _) ε' h₀
          hε' hh₀R.le A₁ (hA2 d hd0 hdq χ) A (d * (k * h₀)) d hd0 h4d hc hA₁'
        have hshift : ∀ n : ℕ, n / d + k * h₀ = (n + d * (k * h₀)) / d := fun n =>
          (Nat.add_mul_div_left n (k * h₀) hd0).symm
        simp_rw [hshift]
        calc ∑ n ∈ Finset.Ioc A (2 * A), W d χ ((n + d * (k * h₀)) / d) / ((H : ℝ) * n)
            = (1 / (H : ℝ)) * ∑ n ∈ Finset.Ioc A (2 * A), W d χ ((n + d * (k * h₀)) / d) / n := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun n _ => ?_
              rw [div_mul_eq_div_div_swap, one_div_mul_eq_div]
          _ ≤ (1 / (H : ℝ)) * (4 * (ε' * h₀)) :=
              mul_le_mul_of_nonneg_left hre (by positivity)
      refine le_trans (Finset.sum_le_sum hk) ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      -- `K·h₀ ≤ 2H`
      have hKh : ((K : ℕ) : ℝ) * h₀ ≤ 2 * H := by
        have : K * h₀ ≤ 2 * H := by
          rw [hK, Nat.add_mul]
          have := Nat.div_mul_le_self H h₀
          omega
        exact_mod_cast this
      calc ((K : ℕ) : ℝ) * (1 / (H : ℝ) * (4 * (ε' * h₀)))
          = 4 * ε' * (((K : ℕ) : ℝ) * h₀) / H := by
            field_simp
        _ ≤ 4 * ε' * (2 * H) / H := by gcongr
        _ = 8 * ε' := by
            field_simp
            ring
    -- (II) the trimmed tails
    have hII : ∑ n ∈ Finset.Ioc A (2 * A), (h₀ : ℝ) / ((H : ℝ) * n) = (h₀ / H) * S := by
      rw [hSdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [div_mul_div_comm, mul_one]
    -- (III) the freeze costs
    have hIII : ∑ n ∈ Finset.Ioc A (2 * A),
        (((n + H) / d - n / d : ℕ) : ℝ) * (2 * Real.pi * |(d : ℝ) * δ| * h₀) / ((H : ℝ) * n)
          ≤ 4 * Real.pi * q * |δ| * h₀ * S := by
      rw [hSdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn0 : (0:ℝ) < n := by
        rw [Finset.mem_Ioc] at hn
        exact_mod_cast (by omega : 0 < n)
      have hL : (((n + H) / d - n / d : ℕ) : ℝ) ≤ 2 * H := by
        have hadd := Nat.add_div (a := n) (b := H) hd0
        have hHd : H / d ≤ H := Nat.div_le_self H d
        have : (n + H) / d - n / d ≤ 2 * H := by split_ifs at hadd <;> omega
        exact_mod_cast this
      have habs : |(d : ℝ) * δ| ≤ q * |δ| := by
        rw [abs_mul, Nat.abs_cast]
        exact mul_le_mul_of_nonneg_right hdR (abs_nonneg δ)
      have hnum : (((n + H) / d - n / d : ℕ) : ℝ) * (2 * Real.pi * |(d : ℝ) * δ| * h₀)
          ≤ (H : ℝ) * (4 * Real.pi * q * |δ| * h₀) := by
        calc (((n + H) / d - n / d : ℕ) : ℝ) * (2 * Real.pi * |(d : ℝ) * δ| * h₀)
            ≤ (2 * H) * (2 * Real.pi * (q * |δ|) * h₀) := by
              gcongr
            _ = (H : ℝ) * (4 * Real.pi * q * |δ| * h₀) := by ring
      calc (((n + H) / d - n / d : ℕ) : ℝ) * (2 * Real.pi * |(d : ℝ) * δ| * h₀) / ((H : ℝ) * n)
          ≤ (H : ℝ) * (4 * Real.pi * q * |δ| * h₀) / ((H : ℝ) * n) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ = (4 * Real.pi * q * |δ| * h₀) / n := mul_div_mul_left _ _ hH0.ne'
        _ = 4 * Real.pi * q * |δ| * h₀ * (1 / n) := by rw [mul_one_div]
    -- assemble the three
    calc ∑ n ∈ Finset.Ioc A (2 * A),
          ((∑ k ∈ Finset.range K, W d χ (n / d + k * h₀)) + (h₀ : ℝ)
            + (((n + H) / d - n / d : ℕ) : ℝ) * (2 * Real.pi * |(d : ℝ) * δ| * h₀))
            / ((H : ℝ) * n)
        = (∑ n ∈ Finset.Ioc A (2 * A),
            (∑ k ∈ Finset.range K, W d χ (n / d + k * h₀)) / ((H : ℝ) * n))
          + (∑ n ∈ Finset.Ioc A (2 * A), (h₀ : ℝ) / ((H : ℝ) * n))
          + ∑ n ∈ Finset.Ioc A (2 * A),
            (((n + H) / d - n / d : ℕ) : ℝ) * (2 * Real.pi * |(d : ℝ) * δ| * h₀)
              / ((H : ℝ) * n) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [add_div, add_div]
      _ ≤ 8 * ε' + (h₀ / H) * S + 4 * Real.pi * q * |δ| * h₀ * S := by
          rw [hII]
          exact add_le_add (add_le_add hI le_rfl) hIII
  -- the per-`n` expansion, summed
  have hpern : ∀ n ∈ Finset.Ioc A (2 * A),
      ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
          g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)
            * (((a : ℝ) / (q : ℝ) + δ : ℝ) : ℂ))‖ / ((H : ℝ) * n)
        ≤ ∑ b ∈ Finset.range q, (1 / ((q / Nat.gcd b q).totient : ℝ))
            * ∑ χ : DirichletCharacter ℂ (q / Nat.gcd b q),
              ((∑ k ∈ Finset.range K, W (Nat.gcd b q) χ (n / Nat.gcd b q + k * h₀))
                + (h₀ : ℝ)
                + (((n + H) / Nat.gcd b q - n / Nat.gcd b q : ℕ) : ℝ)
                    * (2 * Real.pi * |(Nat.gcd b q : ℝ) * δ| * h₀)) / ((H : ℝ) * n) := by
    intro n hn
    have hn0 : (0:ℝ) < n := by
      rw [Finset.mem_Ioc] at hn
      exact_mod_cast (by omega : 0 < n)
    have h := norm_restricted_window_le_char_windows g hg hb levels hlv q hq hql a δ n H h₀ K
      hh₀ le_rfl
    calc ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
            g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)
              * (((a : ℝ) / (q : ℝ) + δ : ℝ) : ℂ))‖ / ((H : ℝ) * n)
        ≤ (∑ b ∈ Finset.range q, (1 / ((q / Nat.gcd b q).totient : ℝ))
            * ∑ χ : DirichletCharacter ℂ (q / Nat.gcd b q),
              ((∑ k ∈ Finset.range K,
                ‖∑ m' ∈ (Finset.Ioc (n / Nat.gcd b q + k * h₀)
                    (n / Nat.gcd b q + k * h₀ + h₀)).filter (HasFactorInAll levels),
                  χ m' * g m'‖)
              + (h₀ : ℝ)
              + (((n + H) / Nat.gcd b q - n / Nat.gcd b q : ℕ) : ℝ)
                  * (2 * Real.pi * |(Nat.gcd b q : ℝ) * δ| * h₀))) / ((H : ℝ) * n) :=
          div_le_div_of_nonneg_right h (by positivity)
      _ = _ := by
          simp only [Finset.sum_div, mul_div_assoc, hW]
  refine le_trans (Finset.sum_le_sum hpern) ?_
  -- swap the `n`-sum inside, use `hclass`, count the characters
  rw [Finset.sum_comm]
  have hb : ∀ b ∈ Finset.range q,
      ∑ n ∈ Finset.Ioc A (2 * A), (1 / ((q / Nat.gcd b q).totient : ℝ))
          * ∑ χ : DirichletCharacter ℂ (q / Nat.gcd b q),
            ((∑ k ∈ Finset.range K, W (Nat.gcd b q) χ (n / Nat.gcd b q + k * h₀))
              + (h₀ : ℝ)
              + (((n + H) / Nat.gcd b q - n / Nat.gcd b q : ℕ) : ℝ)
                  * (2 * Real.pi * |(Nat.gcd b q : ℝ) * δ| * h₀)) / ((H : ℝ) * n)
        ≤ M := by
    intro b hbq
    have hd0 : 0 < Nat.gcd b q := Nat.gcd_pos_of_pos_right b hq
    have hq₀ : 0 < q / Nat.gcd b q :=
      Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right b q)) hd0
    haveI : NeZero (q / Nat.gcd b q) := ⟨hq₀.ne'⟩
    have hφ : (0:ℝ) < ((q / Nat.gcd b q).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq₀
    have hcard : (Fintype.card (DirichletCharacter ℂ (q / Nat.gcd b q)) : ℝ)
        = ((q / Nat.gcd b q).totient : ℝ) := by
      rw [← Nat.card_eq_fintype_card]
      exact_mod_cast DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ _
    rw [← Finset.mul_sum, Finset.sum_comm]
    calc (1 / ((q / Nat.gcd b q).totient : ℝ))
          * ∑ χ : DirichletCharacter ℂ (q / Nat.gcd b q), ∑ n ∈ Finset.Ioc A (2 * A),
            ((∑ k ∈ Finset.range K, W (Nat.gcd b q) χ (n / Nat.gcd b q + k * h₀))
              + (h₀ : ℝ)
              + (((n + H) / Nat.gcd b q - n / Nat.gcd b q : ℕ) : ℝ)
                  * (2 * Real.pi * |(Nat.gcd b q : ℝ) * δ| * h₀)) / ((H : ℝ) * n)
        ≤ (1 / ((q / Nat.gcd b q).totient : ℝ))
          * ∑ _χ : DirichletCharacter ℂ (q / Nat.gcd b q), M := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => ?_) (by positivity)
          exact hclass b hbq χ
      _ = M := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
          field_simp
  refine le_trans (Finset.sum_le_sum hb) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hM]
  -- absorb the absolute main term with `S ≥ 1/2`
  have h8 : 8 * (q : ℝ) * ε' ≤ 16 * q * ε' * S := by
    have := mul_le_mul_of_nonneg_left hShalf (by positivity : (0:ℝ) ≤ 16 * q * ε')
    linarith
  have hexp : (q : ℝ) * (8 * ε' + (h₀ / H) * S + 4 * Real.pi * q * |δ| * h₀ * S)
      = 8 * q * ε' + (q * h₀ / H + 4 * Real.pi * q^2 * |δ| * h₀) * S := by ring
  rw [hexp]
  linarith

/-! ### R6-7: the upward scale transfer, and the harmonic sliding count -/

/-- **Non-pretentiousness transfers up in scale at a bounded cost in strength** (Track R,
R6-7).  If `g` is unimodular and non-pretentious at strength `A` and truncation `x`, then
for any truncation `z` with `x ≤ z ≤ c·x` it is non-pretentious at strength `A/c` (more
precisely any `A'` with `A'·c ≤ A`): the distance to every twist only grows with the
truncation (`pretentiousDistSq_mono_of_norm_le_one`), the moduli `q ≤ A' ≤ A` are covered,
and the frequency range `|t| ≤ A'·z ≤ A'·c·x ≤ A·x` is covered.  In the wrapper the top
dyadic blocks of `(x/w, x]` have twisted block scale `2A'+1` up to `≈ 4x`, so the
interface's `NonPretentiousAt g A ⌈x⌉₊` is first moved up to scale `8⌈x⌉₊` at strength
`A/8` and only then transferred down (`nonPretentiousAt_scale_transfer`) to each block. -/
theorem nonPretentiousAt_scale_up {g : ℕ → ℂ} (hg : Unimodular g) {A A' c : ℝ} {x z : ℕ}
    (h : NonPretentiousAt g A x) (hxz : x ≤ z) (hzc : (z : ℝ) ≤ c * x)
    (hA'0 : 0 ≤ A') (hc1 : 1 ≤ c) (hA' : A' * c ≤ A) :
    NonPretentiousAt g A' z := by
  intro q χ t hq ht
  have hAA' : A' ≤ A := le_trans (le_mul_of_one_le_right hA'0 hc1) hA'
  have hq' : (q : ℝ) ≤ A := le_trans hq hAA'
  have ht' : |t| ≤ A * x := by
    calc |t| ≤ A' * z := ht
      _ ≤ A' * (c * x) := mul_le_mul_of_nonneg_left hzc hA'0
      _ = (A' * c) * x := by ring
      _ ≤ A * x := mul_le_mul_of_nonneg_right hA' (Nat.cast_nonneg x)
  calc A' ≤ A := hAA'
    _ ≤ pretentiousDistSq g (charTwist q χ t) x := h q χ t hq' ht'
    _ ≤ pretentiousDistSq g (charTwist q χ t) z :=
        pretentiousDistSq_mono_of_norm_le_one hg (charTwist_norm_le_one q χ t) hxz

/-- **The harmonic-weighted sliding count** (Track R, R7-3a).

Summing over `n ∈ (A, B]` the number of `m ∈ (n, n+H]` with property `p`, weighted by
`1/n`, costs at most `2H` times the harmonic mass of the `p`-integers in `(A, B+H]`: each
such `m` is met by the windows with `m − H ≤ n < m`, at most `H` of them, and each has
`n ≥ m − H ≥ m/2` once `2H ≤ A`.  With `p = 𝒮ᶜ` this is the once-paid `𝒮ᶜ` removal of
report §7.3, priced by the block's `𝒮ᶜ` log-density. -/
theorem sum_card_filter_window_div_le (p : ℕ → Prop) [DecidablePred p] (A B H : ℕ)
    (hHA : 2 * H ≤ A) :
    ∑ n ∈ Finset.Ioc A B, (((Finset.Ioc n (n + H)).filter p).card : ℝ) / n
      ≤ 2 * H * ∑ m ∈ (Finset.Ioc A (B + H)).filter p, (1:ℝ) / m := by
  classical
  -- the window count as an indicator sum over the enclosing range
  have hcard : ∀ n ∈ Finset.Ioc A B, (((Finset.Ioc n (n + H)).filter p).card : ℝ) / n
      = ∑ m ∈ (Finset.Ioc A (B + H)).filter p,
          if n < m ∧ m ≤ n + H then (1:ℝ) / n else 0 := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hset : (Finset.Ioc n (n + H)).filter p
        = ((Finset.Ioc A (B + H)).filter p).filter (fun m => n < m ∧ m ≤ n + H) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, h2⟩, hp⟩
        exact ⟨⟨⟨by omega, by omega⟩, hp⟩, h1, h2⟩
      · rintro ⟨⟨_, hp⟩, h1, h2⟩
        exact ⟨⟨h1, h2⟩, hp⟩
    rw [hset, Finset.card_filter, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hcard, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [Finset.mem_filter, Finset.mem_Ioc] at hm
  obtain ⟨⟨hAm, _⟩, _⟩ := hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  -- the windows meeting `m`
  rw [← Finset.sum_filter]
  have hsub : (Finset.Ioc A B).filter (fun n => n < m ∧ m ≤ n + H) ⊆ Finset.Ico (m - H) m := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    rw [Finset.mem_Ico]
    omega
  have hcardle : (((Finset.Ioc A B).filter (fun n => n < m ∧ m ≤ n + H)).card : ℝ) ≤ H := by
    have h1 := Finset.card_le_card hsub
    rw [Nat.card_Ico] at h1
    have h2 : m - (m - H) ≤ H := by omega
    exact_mod_cast le_trans h1 h2
  have hpt : ∀ n ∈ (Finset.Ioc A B).filter (fun n => n < m ∧ m ≤ n + H),
      (1:ℝ) / n ≤ 2 / m := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [div_le_div_iff₀ hn0 hm0]
    have : (m : ℝ) ≤ 2 * n := by exact_mod_cast (by omega : m ≤ 2 * n)
    linarith
  calc ∑ n ∈ (Finset.Ioc A B).filter (fun n => n < m ∧ m ≤ n + H), (1:ℝ) / n
      ≤ ∑ n ∈ (Finset.Ioc A B).filter (fun n => n < m ∧ m ≤ n + H), (2:ℝ) / m :=
        Finset.sum_le_sum hpt
    _ = (((Finset.Ioc A B).filter (fun n => n < m ∧ m ≤ n + H)).card : ℝ) * (2 / m) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (H : ℝ) * (2 / m) := mul_le_mul_of_nonneg_right hcardle (by positivity)
    _ = 2 * H * (1 / m) := by ring

end MoltResearch
