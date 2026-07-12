import MoltResearch.Discrepancy.PrincipalAndEquidistribution

/-!
# Discrepancy: reduction of non-primitive residue classes to primitive ones

Nucleus-track module for the Tao 2015 §4 analysis (arXiv:1509.05363, issue #2871): the
reduction step for **non-primitive** residue classes.  The paper: "For non-primitive
residue classes `b (r)`, we write `r = (b,r) r'` and `b = (b,r) b'`.  The previous
arguments then give `∑_{n = b' (r')} h(n)/n^{1+1/log X} = 𝔖/r' + O(...)`, which since
`h((b,r)) = 1` gives `∑_{n = b (r)} h(n)/n^{1+1/log X} = 𝔖/r + O(...)`."

Contents:
* `natResidueZetaSum` — the ℕ-congruence form `∑_{n % r = b % r} h(n)/n^σ` of
  `residueZetaSum`, with bridge `natResidueZetaSum_eq_residueZetaSum` (pointwise
  `(n : ZMod r) = (b : ZMod r) ↔ n % r = b % r`, `ZMod.natCast_eq_natCast_iff'`).
* `natResidueZetaSum_mul_left` — the dilation identity
  `∑_{n ≡ d·b' (d·r')} h(n)/n^σ = (1/d^σ) · ∑_{u ≡ b' (r')} h(u)/u^σ` for completely
  multiplicative `h` with `h d = 1`: every `n ≡ d·b' (mod d·r')` is a multiple `d·u`
  with `u ≡ b' (mod r')`, and per term `h(d·u)/(d·u)^σ = (1/d^σ)·(h(u)/u^σ)`.
* `natResidueZetaSum_eq_of_gcd` — the paper's reduction: specialize the dilation
  identity at `d = gcd(b, r)` using `r = d·(r/d)`, `b = d·(b/d)`.
* `isUnit_div_gcd_cast` — the reduced class `b/d mod r/d` is a *unit* (Mathlib's
  `Nat.coprime_div_gcd_div_gcd`), which is exactly the hypothesis that
  `residueZetaSum_eq_char_average` needs at the reduced modulus; the closing `example`
  chains all three pieces with the character-average expansion.

Junk conventions keep the statements hypothesis-light: the `n = 0` term of every series
vanishes on its own, since `(0:ℂ)^σ = 0` for `σ ≠ 0` and `z / 0 = 0`.
-/

namespace MoltResearch

/-- ℕ-congruence form of the residue-class zeta sum, `∑_{n % r = b % r} h(n)/n^σ`
(Tao 2015 §4, arXiv:1509.05363: the sums `∑_{n = b (r)} h(n)/n^{1+1/log X}`).

Compare `residueZetaSum`, which indexes the class by `b : ZMod r`; the bridge is
`natResidueZetaSum_eq_residueZetaSum`.  The ℕ-indexed form is the convenient one for the
non-primitive-class reduction, where `b` and `r` are divided by their gcd. -/
noncomputable def natResidueZetaSum (h : ℕ → ℂ) (r b : ℕ) (σ : ℝ) : ℂ :=
  ∑' n : ℕ, if n % r = b % r then h n / (n : ℂ) ^ (σ : ℂ) else 0

/-- The ℕ-congruence residue-class zeta sum agrees with the `ZMod`-indexed one:
pointwise, `(n : ZMod r) = (b : ZMod r) ↔ n % r = b % r`. -/
theorem natResidueZetaSum_eq_residueZetaSum {r : ℕ} [NeZero r] (h : ℕ → ℂ) (b : ℕ)
    (σ : ℝ) : natResidueZetaSum h r b σ = residueZetaSum h r (b : ZMod r) σ := by
  rw [natResidueZetaSum, residueZetaSum]
  refine tsum_congr fun n => ?_
  by_cases hc : n % r = b % r
  · rw [if_pos hc, if_pos ((ZMod.natCast_eq_natCast_iff' n b r).mpr hc)]
  · rw [if_neg hc, if_neg fun hz => hc ((ZMod.natCast_eq_natCast_iff' n b r).mp hz)]

/-- **Dilation identity for residue-class zeta sums** (Tao 2015 §4, arXiv:1509.05363,
the identity behind "which since `h((b,r)) = 1` gives ..."): for completely
multiplicative `h` with `h d = 1` (`d ≠ 0`) and exponent `σ ≠ 0`,

`∑_{n ≡ d·b' (d·r')} h(n)/n^σ = (1/d^σ) · ∑_{u ≡ b' (r')} h(u)/u^σ`.

Every `n` with `n ≡ d·b' (mod d·r')` is divisible by `d` (reduce the congruence mod
`d`), so the left series reindexes along the injection `u ↦ d·u`
(`Function.Injective.tsum_eq`); per term the congruence transfers by
`Nat.mul_mod_mul_left`, and `h(d·u)/(d·u)^σ = (1/d^σ)·(h(u)/u^σ)` since
`h(d·u) = h(d)·h(u) = h(u)` and `(d·u)^σ = d^σ·u^σ`.  The `u = 0` term is junk-zero on
both sides (`(0:ℂ)^σ = 0`, `z/0 = 0`), so no guard beyond `σ ≠ 0` is needed. -/
theorem natResidueZetaSum_mul_left {h : ℕ → ℂ} (hmul : CompletelyMultiplicativeC h)
    {d : ℕ} (hd0 : d ≠ 0) (hd1 : h d = 1) (r' b' : ℕ) {σ : ℝ} (hσ : σ ≠ 0) :
    natResidueZetaSum h (d * r') (d * b') σ
      = (1 / (d : ℂ) ^ (σ : ℂ)) * natResidueZetaSum h r' b' σ := by
  have hσC : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ
  have hinj : Function.Injective fun u : ℕ => d * u := fun u v huv =>
    (mul_right_inj' hd0).mp huv
  -- the support of the `(d·r')`-summand consists of multiples of `d`
  have hsupp : (Function.support fun n : ℕ =>
      if n % (d * r') = (d * b') % (d * r') then h n / (n : ℂ) ^ (σ : ℂ) else 0)
      ⊆ Set.range fun u : ℕ => d * u := by
    intro n hn
    have hn' : ¬(if n % (d * r') = (d * b') % (d * r')
        then h n / (n : ℂ) ^ (σ : ℂ) else 0) = 0 := hn
    have hcong : n % (d * r') = (d * b') % (d * r') := by
      by_contra hcon
      exact hn' (if_neg hcon)
    -- reduce the congruence mod `d`: `n % d = (d·b') % d = 0`
    have hdn : d ∣ n := by
      refine Nat.dvd_of_mod_eq_zero ?_
      calc n % d = n % (d * r') % d := (Nat.mod_mod_of_dvd n (dvd_mul_right d r')).symm
        _ = (d * b') % (d * r') % d := by rw [hcong]
        _ = (d * b') % d := Nat.mod_mod_of_dvd _ (dvd_mul_right d r')
        _ = 0 := Nat.mul_mod_right d b'
    exact Set.mem_range.mpr ⟨n / d, Nat.mul_div_cancel' hdn⟩
  -- per-term identity along the reindexing `n = d·u`
  have hterm : ∀ u : ℕ,
      (if (d * u) % (d * r') = (d * b') % (d * r')
        then h (d * u) / ((d * u : ℕ) : ℂ) ^ (σ : ℂ) else 0)
      = (1 / (d : ℂ) ^ (σ : ℂ))
          * (if u % r' = b' % r' then h u / (u : ℂ) ^ (σ : ℂ) else 0) := by
    intro u
    have hcond : (d * u) % (d * r') = (d * b') % (d * r') ↔ u % r' = b' % r' := by
      rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
      exact mul_right_inj' hd0
    by_cases hc : u % r' = b' % r'
    · rw [if_pos (hcond.mpr hc), if_pos hc]
      rcases eq_or_ne u 0 with rfl | hu0
      · -- junk term: both sides vanish since `(0:ℂ)^σ = 0` and `z/0 = 0`
        rw [mul_zero, Nat.cast_zero, Complex.zero_cpow hσC, div_zero, mul_zero]
      · rw [hmul d u hd0 hu0, hd1, one_mul, Nat.cast_mul,
          Complex.natCast_mul_natCast_cpow]
        ring
    · rw [if_neg fun hcc => hc (hcond.mp hcc), if_neg hc, mul_zero]
  calc natResidueZetaSum h (d * r') (d * b') σ
      = ∑' u : ℕ, (if (d * u) % (d * r') = (d * b') % (d * r')
          then h (d * u) / ((d * u : ℕ) : ℂ) ^ (σ : ℂ) else 0) := by
        rw [natResidueZetaSum]
        exact (hinj.tsum_eq hsupp).symm
    _ = ∑' u : ℕ, (1 / (d : ℂ) ^ (σ : ℂ))
          * (if u % r' = b' % r' then h u / (u : ℂ) ^ (σ : ℂ) else 0) :=
        tsum_congr hterm
    _ = (1 / (d : ℂ) ^ (σ : ℂ)) * natResidueZetaSum h r' b' σ := by
        rw [natResidueZetaSum]
        exact tsum_mul_left

/-- **Non-primitive residue classes reduce to a smaller modulus** (Tao 2015 §4,
arXiv:1509.05363: "we write `r = (b,r) r'` and `b = (b,r) b'` ... which since
`h((b,r)) = 1` gives `∑_{n = b (r)} h(n)/n^{1+1/log X} = 𝔖/r + O(...)`"): for
completely multiplicative `h` with `h(gcd(b,r)) = 1`, `b ≠ 0`, and `σ ≠ 0`,

`∑_{n ≡ b (r)} h(n)/n^σ = (1/gcd(b,r)^σ) · ∑_{u ≡ b/gcd (r/gcd)} h(u)/u^σ`.

This is `natResidueZetaSum_mul_left` at `d = gcd(b,r)`, via `r = d·(r/d)` and
`b = d·(b/d)`.  The reduced class is primitive (`isUnit_div_gcd_cast`), so the
character-average expansion applies at the reduced modulus. -/
theorem natResidueZetaSum_eq_of_gcd {h : ℕ → ℂ} (hmul : CompletelyMultiplicativeC h)
    {r b : ℕ} (hb : b ≠ 0) {σ : ℝ} (hσ : σ ≠ 0) (hd1 : h (Nat.gcd b r) = 1) :
    natResidueZetaSum h r b σ
      = (1 / (Nat.gcd b r : ℂ) ^ (σ : ℂ))
          * natResidueZetaSum h (r / Nat.gcd b r) (b / Nat.gcd b r) σ := by
  have hd0 : Nat.gcd b r ≠ 0 := fun h0 => hb (Nat.gcd_eq_zero_iff.mp h0).1
  have hkey := natResidueZetaSum_mul_left hmul hd0 hd1
    (r / Nat.gcd b r) (b / Nat.gcd b r) hσ
  rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_right b r),
    Nat.mul_div_cancel' (Nat.gcd_dvd_left b r)] at hkey

/-- **The reduced residue class is primitive** (Tao 2015 §4: the class `b' (r')` is a
unit class, so the previous — primitive — arguments apply to it): for `b ≠ 0`, the
residue `b/gcd(b,r) mod r/gcd(b,r)` is a unit, by Mathlib's
`Nat.coprime_div_gcd_div_gcd` and `ZMod.isUnit_iff_coprime`.  This is exactly the
`IsUnit` hypothesis that `residueZetaSum_eq_char_average` needs at the reduced
modulus. -/
theorem isUnit_div_gcd_cast {r b : ℕ} (hb : b ≠ 0) :
    IsUnit ((b / Nat.gcd b r : ℕ) : ZMod (r / Nat.gcd b r)) := by
  have hpos : 0 < Nat.gcd b r := Nat.gcd_pos_of_pos_left r (Nat.pos_of_ne_zero hb)
  exact (ZMod.isUnit_iff_coprime _ _).mpr (Nat.coprime_div_gcd_div_gcd hpos)

/-- Compile-only regression: chaining the gcd reduction, the `ZMod` bridge, and the
character-average expansion (`residueZetaSum_eq_char_average`) expresses a
*non-primitive* residue-class zeta sum through the `φ(r/d)` twisted singular series at
the reduced modulus `r/d`, `d = gcd(b,r)`. -/
example {h : ℕ → ℂ} (hmul : CompletelyMultiplicativeC h) {r b : ℕ} (hb : b ≠ 0)
    (hr' : r / Nat.gcd b r ≠ 0) {σ : ℝ} (hσ : 1 < σ) (hb1 : ∀ n, ‖h n‖ ≤ 1)
    (hd1 : h (Nat.gcd b r) = 1) :
    natResidueZetaSum h r b σ
      = (1 / (Nat.gcd b r : ℂ) ^ (σ : ℂ))
          * (((r / Nat.gcd b r).totient : ℂ)⁻¹
              * ∑ χ : DirichletCharacter ℂ (r / Nat.gcd b r),
                  (starRingEnd ℂ) (χ ((b / Nat.gcd b r : ℕ) : ZMod (r / Nat.gcd b r)))
                    * zetaWeightedSum
                        (fun n : ℕ => χ (n : ZMod (r / Nat.gcd b r)) * h n) σ) := by
  haveI : NeZero (r / Nat.gcd b r) := ⟨hr'⟩
  rw [natResidueZetaSum_eq_of_gcd hmul hb (ne_of_gt (lt_trans one_pos hσ)) hd1,
    natResidueZetaSum_eq_residueZetaSum,
    residueZetaSum_eq_char_average hb1 hσ (isUnit_div_gcd_cast (r := r) hb)]

end MoltResearch
