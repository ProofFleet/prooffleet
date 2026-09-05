import MoltResearch.Discrepancy.MajorArcFreeze
import MoltResearch.Discrepancy.TypicalFactorization
import MoltResearch.Discrepancy.CharTwistCompose

/-!
# Track R: the major-arc assembly — opening lemmas (R6-1 … R6-4)

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

end MoltResearch
