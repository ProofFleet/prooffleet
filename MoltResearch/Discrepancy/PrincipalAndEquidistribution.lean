import MoltResearch.Discrepancy.SingularSeries
import MoltResearch.Discrepancy.CharTwistCompose
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Discrepancy: principal-character series and residue-class equidistribution

Nucleus-track module for the Tao 2015 §4 analysis (arXiv:1509.05363,
`Problems/tao2015_derivation_c.md`, issue #2871, PR E3): the two remaining pieces of the
character decomposition of the singular series over residue classes mod `r`.

**(a) Principal character = untwisted series up to modulus-only factors**
(`norm_zetaWeightedSum_principal_mul_bounds`): the paper computes
`∑_n χ₀(n)h(n)/n^{1+1/log X} = (φ(r)/r)·𝔖 + O_ε(1)`; our modulus-only form says the
principal twist changes `‖𝔖‖` by at most `exp(±ω(r))` (`ω(r) = r.primeFactors.card`):

`exp(−ω(r))·‖𝔖‖ ≤ ‖𝔖_{χ₀}‖ ≤ exp(ω(r))·‖𝔖‖`.

Proof (Mertens-free, mirroring `SingularSeries.lean`): both series are Euler products, so
`‖𝔖_{χ₀}‖ = exp(Re T₀)` and `‖𝔖‖ = exp(Re T)` with `T, T₀` the log-sums over primes
(`EulerProduct.exp_tsum_primes_log_eq_tsum`).  Since `χ₀(p) = 1` for `p ∤ r` and `= 0` for
`p ∣ r`, the two log-sums agree except at the finitely many primes dividing `r`
(`primeFactorsLift` lifts `r.primeFactors` into `Nat.Primes`; `tsum_eq_sum` collapses the
difference), where each term is `‖log(1 − h(p)/p^σ)‖ ≤ (3/2)·(1/2) ≤ 1`
(`Complex.norm_log_one_add_half_le_self`).  Hence `|Re T − Re T₀| ≤ ω(r)`.

**(b) Character-orthogonality expansion into residue classes**
(`residueZetaSum_eq_char_average`): for a unit residue `b mod r`,

`∑_{n ≡ b (r)} h(n)/n^σ = φ(r)⁻¹ · ∑_χ conj(χ(b)) · ∑_n χ(n)h(n)/n^σ`,

the paper's expansion of the residue-class sum into the `φ(r)` twisted singular series.
The pointwise input is the second orthogonality relation
`∑_χ conj(χ(b))·χ(a) = φ(r)·1_{a=b}` (`sum_conj_char_mul_char`, from Mathlib's
`DirichletCharacter.sum_char_inv_mul_char_eq` via `conj(χ(b)) = χ(b⁻¹)` on the unit
circle); the finite character sum is interchanged with the absolutely convergent `tsum`
by `Summable.tsum_finsetSum`.
-/

namespace MoltResearch

open Finset

private lemma one_lt_log_of_three_le {X : ℝ} (hX : 3 ≤ X) : 1 < Real.log X := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    _ ≤ Real.log X := Real.log_le_log (by norm_num) hX

/-- The zeta weight of a 1-bounded sequence lies in the half-disc at primes:
`‖g(p)/p^σ‖ ≤ 1/p ≤ 1/2` for `σ ≥ 1`. -/
private lemma norm_prime_zetaWeight_le {g : ℕ → ℂ} (hb : ∀ n, ‖g n‖ ≤ 1) {σ : ℝ}
    (hσ : 1 < σ) (p : Nat.Primes) :
    ‖g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)‖ ≤ 1 / ((p : ℕ) : ℝ) := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  refine (norm_zetaWeight_le hb (by linarith) (p : ℕ)).trans ?_
  refine one_div_le_one_div_of_le hp0 ?_
  calc ((p : ℕ) : ℝ) = ((p : ℕ) : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ ((p : ℕ) : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le (by linarith) hσ.le

/-- Per-prime crude bound on the Euler log-factor: `‖log(1 − g(p)/p^σ)‖ ≤ 1` for
1-bounded `g` and `σ > 1`, via `‖log(1+z)‖ ≤ (3/2)‖z‖` on the half-disc. -/
private lemma norm_log_one_sub_zetaWeight_le_one {g : ℕ → ℂ} (hb : ∀ n, ‖g n‖ ≤ 1) {σ : ℝ}
    (hσ : 1 < σ) (p : Nat.Primes) :
    ‖Complex.log (1 - g p / ((p : ℕ) : ℂ) ^ (σ : ℂ))‖ ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hhalf : ‖g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)‖ ≤ 1 / 2 :=
    (norm_prime_zetaWeight_le hb hσ p).trans (one_div_le_one_div_of_le (by norm_num) hp2)
  have hlog := Complex.norm_log_one_add_half_le_self
    (z := -(g p / ((p : ℕ) : ℂ) ^ (σ : ℂ))) (by rwa [norm_neg])
  rw [← sub_eq_add_neg] at hlog
  calc ‖Complex.log (1 - g p / ((p : ℕ) : ℂ) ^ (σ : ℂ))‖
      ≤ 3 / 2 * ‖-(g p / ((p : ℕ) : ℂ) ^ (σ : ℂ))‖ := hlog
    _ = 3 / 2 * ‖g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)‖ := by rw [norm_neg]
    _ ≤ 3 / 2 * (1 / 2) := mul_le_mul_of_nonneg_left hhalf (by norm_num)
    _ ≤ 1 := by norm_num

/-- The prime factors of `r`, lifted from `Finset ℕ` into `Finset Nat.Primes` (the index
type of Euler-product prime sums). -/
private def primeFactorsLift (r : ℕ) : Finset Nat.Primes :=
  r.primeFactors.attach.map
    ⟨fun p => ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩, by
      intro p q hpq
      have h1 : (p : ℕ) = (q : ℕ) := congrArg (fun t : Nat.Primes => (t : ℕ)) hpq
      exact Subtype.ext h1⟩

private lemma mem_primeFactorsLift {r : ℕ} {p : Nat.Primes} :
    p ∈ primeFactorsLift r ↔ (p : ℕ) ∈ r.primeFactors := by
  constructor
  · intro hp
    rw [primeFactorsLift, Finset.mem_map] at hp
    obtain ⟨x, _, rfl⟩ := hp
    exact x.2
  · intro hp
    rw [primeFactorsLift, Finset.mem_map]
    exact ⟨⟨(p : ℕ), hp⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

private lemma card_primeFactorsLift (r : ℕ) :
    (primeFactorsLift r).card = r.primeFactors.card := by
  rw [primeFactorsLift, Finset.card_map, Finset.card_attach]

/-- **Principal-character singular series, modulus-only bounds** (Tao 2015 §4,
arXiv:1509.05363, the principal-character computation
`∑_n χ₀(n)h(n)/n^{1+1/log X} = (φ(r)/r)·𝔖 + O_ε(1)`): for completely multiplicative
unimodular `h` with `h(1) = 1` and `X ≥ 3`, the `χ₀`-twisted singular series at the zeta
weight `σ = 1 + 1/log X` has the same magnitude as the untwisted one up to the explicit
modulus-only factor `exp(±ω(r))`, `ω(r) = r.primeFactors.card`:

`exp(−ω(r))·‖𝔖‖ ≤ ‖𝔖_{χ₀}‖ ≤ exp(ω(r))·‖𝔖‖`.

Both series are Euler products, `‖𝔖‖ = exp(Re T)`; the two prime log-sums agree off the
primes dividing `r` (`χ₀(p) = 1` there) and differ by `‖log(1 − h(p)/p^σ)‖ ≤ 1` at each of
the `ω(r)` primes dividing `r` (`χ₀(p) = 0` there). -/
theorem norm_zetaWeightedSum_principal_mul_bounds {r : ℕ} [NeZero r]
    {h : ℕ → ℂ} (hmul : CompletelyMultiplicativeC h) (h1 : h 1 = 1) (hu : Unimodular h)
    {X : ℝ} (hX : 3 ≤ X) :
    Real.exp (-(1 * (r.primeFactors.card : ℝ)))
        * ‖zetaWeightedSum h (1 + 1 / Real.log X)‖
      ≤ ‖zetaWeightedSum (fun n : ℕ => (1 : DirichletCharacter ℂ r) (n : ZMod r) * h n)
          (1 + 1 / Real.log X)‖
    ∧ ‖zetaWeightedSum (fun n : ℕ => (1 : DirichletCharacter ℂ r) (n : ZMod r) * h n)
          (1 + 1 / Real.log X)‖
      ≤ Real.exp (1 * (r.primeFactors.card : ℝ))
        * ‖zetaWeightedSum h (1 + 1 / Real.log X)‖ := by
  have hlog1 : 1 < Real.log X := one_lt_log_of_three_le hX
  have hσ : 1 < 1 + 1 / Real.log X := by
    have h0 : 0 < 1 / Real.log X := by positivity
    linarith
  have hbh : ∀ n, ‖h n‖ ≤ 1 := fun n => (hu n).le
  set g₀ : ℕ → ℂ := fun n : ℕ => (1 : DirichletCharacter ℂ r) (n : ZMod r) * h n
    with hg₀def
  -- the principal twist is completely multiplicative, normalized, 1-bounded
  have hg₀mul : CompletelyMultiplicativeC g₀ := by
    intro a b ha hb'
    rw [hg₀def]
    dsimp only
    rw [Nat.cast_mul, map_mul, hmul a b ha hb']
    ring
  have hg₀1 : g₀ 1 = 1 := by
    rw [hg₀def]
    dsimp only
    rw [Nat.cast_one, map_one, h1, mul_one]
  have hg₀b : ∀ n, ‖g₀ n‖ ≤ 1 := by
    intro n
    rw [hg₀def]
    dsimp only
    rw [norm_mul, hu n, mul_one]
    exact DirichletCharacter.norm_le_one _ _
  -- Euler products: both norms are exponentials of prime log-sums
  have hnormh := summable_norm_zetaWeight hbh hσ
  have hnormg := summable_norm_zetaWeight hg₀b hσ
  have hEh := EulerProduct.exp_tsum_primes_log_eq_tsum
    (f := hmul.zetaWeightHom h1 (by linarith)) hnormh
  have hEg := EulerProduct.exp_tsum_primes_log_eq_tsum
    (f := hg₀mul.zetaWeightHom hg₀1 (by linarith)) hnormg
  set Th : ℂ := ∑' p : Nat.Primes,
    -Complex.log (1 - h p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)) with hThdef
  set T₀ : ℂ := ∑' p : Nat.Primes,
    -Complex.log (1 - g₀ p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)) with hT₀def
  have hexpTh : Real.exp Th.re = ‖zetaWeightedSum h (1 + 1 / Real.log X)‖ := by
    rw [← Complex.norm_exp, hThdef]
    exact congrArg norm hEh
  have hexpT₀ : Real.exp T₀.re = ‖zetaWeightedSum g₀ (1 + 1 / Real.log X)‖ := by
    rw [← Complex.norm_exp, hT₀def]
    exact congrArg norm hEg
  have hsumlogh : Summable fun p : Nat.Primes =>
      -Complex.log (1 - h p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)) :=
    ((hnormh.of_norm.subtype {p | Nat.Prime p}).clog_one_sub).neg
  have hsumlogg : Summable fun p : Nat.Primes =>
      -Complex.log (1 - g₀ p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)) :=
    ((hnormg.of_norm.subtype {p | Nat.Prime p}).clog_one_sub).neg
  -- the two log-sums differ exactly at the primes dividing `r`
  have hdiff : Th - T₀ = ∑ p ∈ primeFactorsLift r,
      (-Complex.log (1 - h p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ))
        - -Complex.log (1 - g₀ p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ))) := by
    rw [hThdef, hT₀def, ← Summable.tsum_sub hsumlogh hsumlogg]
    refine tsum_eq_sum fun p hp => ?_
    have hpnot : (p : ℕ) ∉ r.primeFactors := fun hmem =>
      hp (mem_primeFactorsLift.mpr hmem)
    have hcop : Nat.Coprime (p : ℕ) r :=
      (Nat.Prime.coprime_iff_not_dvd p.prop).mpr fun hdvd =>
        hpnot (Nat.mem_primeFactors.mpr ⟨p.prop, hdvd, NeZero.ne r⟩)
    have hunit : IsUnit (((p : ℕ) : ZMod r)) := (ZMod.isUnit_iff_coprime (p : ℕ) r).mpr hcop
    have hg₀p : g₀ (p : ℕ) = h (p : ℕ) := by
      rw [hg₀def]
      dsimp only
      rw [MulChar.one_apply hunit, one_mul]
    rw [hg₀p, sub_self]
  -- at each prime dividing `r` the discrepancy is a single log-factor of norm `≤ 1`
  have hnormD : ∀ p ∈ primeFactorsLift r,
      ‖-Complex.log (1 - h p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ))
        - -Complex.log (1 - g₀ p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ))‖ ≤ 1 := by
    intro p hp
    have hmem : (p : ℕ) ∈ r.primeFactors := mem_primeFactorsLift.mp hp
    have hnunit : ¬IsUnit (((p : ℕ) : ZMod r)) := by
      rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd p.prop]
      exact not_not_intro (Nat.dvd_of_mem_primeFactors hmem)
    have hg₀p : g₀ (p : ℕ) = 0 := by
      rw [hg₀def]
      dsimp only
      rw [MulChar.map_nonunit _ hnunit, zero_mul]
    rw [hg₀p, zero_div, sub_zero, Complex.log_one, neg_zero, sub_zero, norm_neg]
    exact norm_log_one_sub_zetaWeight_le_one hbh hσ p
  have habsdiff : |Th.re - T₀.re| ≤ 1 * (r.primeFactors.card : ℝ) := by
    have hnorm_le : ‖Th - T₀‖ ≤ 1 * (r.primeFactors.card : ℝ) := by
      rw [hdiff]
      calc ‖∑ p ∈ primeFactorsLift r,
            (-Complex.log (1 - h p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ))
              - -Complex.log (1 - g₀ p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)))‖
          ≤ ∑ p ∈ primeFactorsLift r,
              ‖-Complex.log (1 - h p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ))
                - -Complex.log (1 - g₀ p / ((p : ℕ) : ℂ)
                    ^ ((1 + 1 / Real.log X : ℝ) : ℂ))‖ := norm_sum_le _ _
        _ ≤ ∑ _p ∈ primeFactorsLift r, (1 : ℝ) := sum_le_sum hnormD
        _ = ((primeFactorsLift r).card : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one]
        _ = 1 * (r.primeFactors.card : ℝ) := by rw [card_primeFactorsLift, one_mul]
    calc |Th.re - T₀.re| = |(Th - T₀).re| := by rw [Complex.sub_re]
      _ ≤ ‖Th - T₀‖ := Complex.abs_re_le_norm _
      _ ≤ 1 * (r.primeFactors.card : ℝ) := hnorm_le
  have habs := abs_le.mp habsdiff
  constructor
  · calc Real.exp (-(1 * (r.primeFactors.card : ℝ)))
          * ‖zetaWeightedSum h (1 + 1 / Real.log X)‖
        = Real.exp (-(1 * (r.primeFactors.card : ℝ))) * Real.exp Th.re := by rw [hexpTh]
      _ = Real.exp (Th.re - 1 * (r.primeFactors.card : ℝ)) := by
          rw [← Real.exp_add]
          ring_nf
      _ ≤ Real.exp T₀.re := Real.exp_le_exp.mpr (by linarith [habs.2])
      _ = ‖zetaWeightedSum g₀ (1 + 1 / Real.log X)‖ := hexpT₀
  · calc ‖zetaWeightedSum g₀ (1 + 1 / Real.log X)‖
        = Real.exp T₀.re := hexpT₀.symm
      _ ≤ Real.exp (Th.re + 1 * (r.primeFactors.card : ℝ)) :=
          Real.exp_le_exp.mpr (by linarith [habs.1])
      _ = Real.exp (1 * (r.primeFactors.card : ℝ)) * Real.exp Th.re := by
          rw [← Real.exp_add]
          ring_nf
      _ = Real.exp (1 * (r.primeFactors.card : ℝ))
          * ‖zetaWeightedSum h (1 + 1 / Real.log X)‖ := by rw [hexpTh]

/-- The zeta-weighted sum restricted to the residue class `b mod r`:
`∑_{n ≡ b (r)} h(n)/n^σ` (Tao 2015 §4: the residue-class average whose equidistribution
over good residues drives the Borwein–Choi–Coons analysis). -/
noncomputable def residueZetaSum (h : ℕ → ℂ) (r : ℕ) (b : ZMod r) (σ : ℝ) : ℂ :=
  ∑' n : ℕ, if (n : ZMod r) = b then h n / (n : ℂ) ^ (σ : ℂ) else 0

/-- **Second orthogonality relation, conjugate form** (Tao 2015 §4 input): for a unit
residue `b mod r`,

`∑_χ conj(χ(b))·χ(a) = φ(r)·1_{a = b}`.

Bridge from Mathlib's `DirichletCharacter.sum_char_inv_mul_char_eq` via
`conj(χ(b)) = χ(b⁻¹)` (character values at units lie on the unit circle). -/
theorem sum_conj_char_mul_char {r : ℕ} [NeZero r] {b : ZMod r} (hbu : IsUnit b)
    (a : ZMod r) :
    ∑ χ : DirichletCharacter ℂ r, (starRingEnd ℂ) (χ b) * χ a
      = if a = b then (r.totient : ℂ) else 0 := by
  have hconj : ∀ χ : DirichletCharacter ℂ r, (starRingEnd ℂ) (χ b) = χ b⁻¹ := by
    intro χ
    have hnorm : ‖χ b‖ = 1 := by
      have hb1 := χ.unit_norm_eq_one hbu.unit
      rwa [hbu.unit_spec] at hb1
    have hinv : χ b⁻¹ = (χ b)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_mul, ZMod.inv_mul_of_unit b hbu, map_one])
    rw [hinv, ← Complex.inv_eq_conj hnorm]
  calc ∑ χ : DirichletCharacter ℂ r, (starRingEnd ℂ) (χ b) * χ a
      = ∑ χ : DirichletCharacter ℂ r, χ b⁻¹ * χ a :=
        Finset.sum_congr rfl fun χ _ => by rw [hconj χ]
    _ = if b = a then (r.totient : ℂ) else 0 :=
        DirichletCharacter.sum_char_inv_mul_char_eq ℂ hbu a
    _ = if a = b then (r.totient : ℂ) else 0 := by
        by_cases hab : a = b
        · rw [if_pos hab.symm, if_pos hab]
        · rw [if_neg fun hba => hab hba.symm, if_neg hab]

/-- **Residue-class sum as a character average** (Tao 2015 §4, arXiv:1509.05363, the
orthogonality expansion of the singular series over residue classes): for 1-bounded `h`,
`σ > 1`, and a unit residue `b mod r`,

`∑_{n ≡ b (r)} h(n)/n^σ = φ(r)⁻¹ · ∑_χ conj(χ(b)) · ∑_n χ(n)h(n)/n^σ`.

The finite character sum interchanges with the absolutely convergent series
(`Summable.tsum_finsetSum`), and per `n` the orthogonality relation
`sum_conj_char_mul_char` collapses the character sum to `φ(r)·1_{n ≡ b}`. -/
theorem residueZetaSum_eq_char_average {r : ℕ} [NeZero r] {h : ℕ → ℂ}
    (hb : ∀ n, ‖h n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {b : ZMod r} (hbu : IsUnit b) :
    residueZetaSum h r b σ
      = (r.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ r,
          (starRingEnd ℂ) (χ b) * zetaWeightedSum (fun n : ℕ => χ (n : ZMod r) * h n) σ := by
  have hsummand : ∀ χ : DirichletCharacter ℂ r,
      Summable fun n : ℕ =>
        (starRingEnd ℂ) (χ b) * (χ (n : ZMod r) * h n / (n : ℂ) ^ (σ : ℂ)) := by
    intro χ
    have hb' : ∀ n : ℕ, ‖χ (n : ZMod r) * h n‖ ≤ 1 := by
      intro n
      rw [norm_mul]
      calc ‖χ ((n : ℕ) : ZMod r)‖ * ‖h n‖
          ≤ 1 * 1 := mul_le_mul (DirichletCharacter.norm_le_one _ _) (hb n)
            (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    exact ((summable_norm_zetaWeight hb' hσ).of_norm).mul_left _
  have key : ∑ χ : DirichletCharacter ℂ r,
      (starRingEnd ℂ) (χ b) * zetaWeightedSum (fun n : ℕ => χ (n : ZMod r) * h n) σ
      = (r.totient : ℂ) * residueZetaSum h r b σ := by
    calc ∑ χ : DirichletCharacter ℂ r,
        (starRingEnd ℂ) (χ b) * zetaWeightedSum (fun n : ℕ => χ (n : ZMod r) * h n) σ
        = ∑ χ : DirichletCharacter ℂ r,
            ∑' n : ℕ, (starRingEnd ℂ) (χ b)
              * (χ (n : ZMod r) * h n / (n : ℂ) ^ (σ : ℂ)) := by
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [show zetaWeightedSum (fun n : ℕ => χ (n : ZMod r) * h n) σ
              = ∑' n : ℕ, χ (n : ZMod r) * h n / (n : ℂ) ^ (σ : ℂ) from rfl]
          exact tsum_mul_left.symm
      _ = ∑' n : ℕ, ∑ χ : DirichletCharacter ℂ r,
            (starRingEnd ℂ) (χ b) * (χ (n : ZMod r) * h n / (n : ℂ) ^ (σ : ℂ)) :=
          (Summable.tsum_finsetSum fun χ _ => hsummand χ).symm
      _ = ∑' n : ℕ, (if (n : ZMod r) = b
            then (r.totient : ℂ) * (h n / (n : ℂ) ^ (σ : ℂ)) else 0) := by
          refine tsum_congr fun n => ?_
          calc ∑ χ : DirichletCharacter ℂ r,
              (starRingEnd ℂ) (χ b) * (χ (n : ZMod r) * h n / (n : ℂ) ^ (σ : ℂ))
              = ∑ χ : DirichletCharacter ℂ r,
                  (starRingEnd ℂ) (χ b) * χ (n : ZMod r) * (h n / (n : ℂ) ^ (σ : ℂ)) :=
                Finset.sum_congr rfl fun χ _ => by ring
            _ = (∑ χ : DirichletCharacter ℂ r, (starRingEnd ℂ) (χ b) * χ (n : ZMod r))
                  * (h n / (n : ℂ) ^ (σ : ℂ)) := by rw [Finset.sum_mul]
            _ = (if ((n : ℕ) : ZMod r) = b then (r.totient : ℂ) else 0)
                  * (h n / (n : ℂ) ^ (σ : ℂ)) := by rw [sum_conj_char_mul_char hbu]
            _ = if ((n : ℕ) : ZMod r) = b
                  then (r.totient : ℂ) * (h n / (n : ℂ) ^ (σ : ℂ)) else 0 := by
                rw [ite_mul, zero_mul]
      _ = ∑' n : ℕ, (r.totient : ℂ)
            * (if (n : ZMod r) = b then h n / (n : ℂ) ^ (σ : ℂ) else 0) := by
          refine tsum_congr fun n => ?_
          rw [mul_ite, mul_zero]
      _ = (r.totient : ℂ) * residueZetaSum h r b σ := by
          rw [residueZetaSum]
          exact tsum_mul_left
  have htot : ((r.totient : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr r.pos_of_neZero).ne'
  rw [key, inv_mul_cancel_left₀ htot]

end MoltResearch
