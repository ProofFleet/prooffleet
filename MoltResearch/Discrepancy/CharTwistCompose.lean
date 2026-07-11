import MoltResearch.Discrepancy.PretentiousDist

/-!
# Discrepancy: composing two character twists into one composite twist

Support for the `𝐭`-cutting lemma of Tao 2015 (arXiv:1509.05363, §4, proof of the generalized
Borwein–Choi–Coons theorem). There, two applications of Proposition 1.11 produce twists
`n ↦ χ(n)·n^{i𝐭}` and `n ↦ χ'(n)·n^{i𝐭'}` both pretending to be the multiplicative function,
and "applying the pretentious triangle inequality, we conclude that

`∑_{p ≤ X^δ} (1 − Re χ(p) conj(χ'(p)) p^{−i(𝐭'−𝐭)})/p ≪_ε 1`."

The left-hand side is `pretentiousDistSq (charTwist q χ 𝐭) (charTwist q' χ' 𝐭')`, but the
Vinogradov–Korobov interface (Track C Stage 5) consumes bounds of the shape
`M ≤ pretentiousDistSq (fun _ => 1) (charTwist Q χ'' s) N` for an honest Dirichlet character
`χ''`. This module supplies the bridge (`pretentiousDistSq_one_charTwist_mul`): the distance
between the two twists **equals** the distance from the constant `1` to the single composite
twist at modulus `Q = q·q'`, character `χ'' = changeLevel χ · (changeLevel χ')⁻¹`, and
frequency `s = 𝐭 − 𝐭'` (the paper's `p^{−i(𝐭'−𝐭)} = p^{i(𝐭−𝐭')}`).

The per-prime content is `charTwist_mul_conj_charTwist`: for `0 < n`,

`χ''(n)·n^{i(t−t')} = (χ(n)·n^{it}) · conj(χ'(n)·n^{it'})`,

split into a character part (`changeLevel_mul_changeLevel_inv_apply_natCast`; the inverse of a
`ℂ`-valued Dirichlet character is its pointwise conjugate since values on units have norm one,
and off the common coprime locus both sides vanish) and an archimedean part
(`natCast_cpow_mul_conj_cpow`: `n^{it}·conj(n^{it'}) = n^{i(t−t')}`).

Also included: `natCast_mul_le_mul`, the trivial composite-modulus bound `q·q' ≤ Q·Q'` feeding
the interface's `(q : ℝ) ≤ Q` quantifier.
-/

namespace MoltResearch

/-- Evaluation of `DirichletCharacter.changeLevel` at a natural number that is a unit at the
larger level: raising the level does not change the value. (At naturals that are units mod `Q`
but not mod `q` — impossible — or non-units mod `Q`, the two sides can differ, so the unit
hypothesis is essential.) -/
theorem changeLevel_apply_natCast_of_isUnit {R : Type*} [CommMonoidWithZero R] {q Q : ℕ}
    (h : q ∣ Q) (χ : DirichletCharacter R q) (n : ℕ) (hu : IsUnit ((n : ℕ) : ZMod Q)) :
    DirichletCharacter.changeLevel h χ ((n : ℕ) : ZMod Q) = χ ((n : ℕ) : ZMod q) := by
  rw [← hu.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd χ h hu.unit,
    hu.unit_spec, ZMod.cast_natCast h]

/-- The inverse of a `ℂ`-valued Dirichlet character is its pointwise complex conjugate:
on units the values have norm one (`z⁻¹ = conj z` there), and off units both sides vanish. -/
theorem dirichletCharacter_inv_apply_conj {Q : ℕ} (ψ : DirichletCharacter ℂ Q) (a : ZMod Q) :
    ψ⁻¹ a = (starRingEnd ℂ) (ψ a) := by
  rw [MulChar.inv_apply_eq_inv']
  by_cases ha : IsUnit a
  · have hnorm : ‖ψ a‖ = 1 := by
      have h := ψ.unit_norm_eq_one ha.unit
      rwa [ha.unit_spec] at h
    exact Complex.inv_eq_conj hnorm
  · rw [MulChar.map_nonunit ψ ha, inv_zero, map_zero]

/-- Character part of the composite-twist identity: at every natural `n`,

`(changeLevel χ · (changeLevel χ')⁻¹)(n mod q·q') = χ(n mod q) · conj(χ'(n mod q'))`.

If `n` is a unit mod `q·q'` this is `changeLevel` evaluation plus inverse-equals-conjugate;
otherwise `n` shares a factor with `q` or with `q'` and both sides vanish. -/
theorem changeLevel_mul_changeLevel_inv_apply_natCast {q q' : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q') (n : ℕ) :
    (DirichletCharacter.changeLevel (dvd_mul_right q q') χ
        * (DirichletCharacter.changeLevel (dvd_mul_left q' q) χ')⁻¹) ((n : ℕ) : ZMod (q * q'))
      = χ ((n : ℕ) : ZMod q) * (starRingEnd ℂ) (χ' ((n : ℕ) : ZMod q')) := by
  rw [MulChar.mul_apply, dirichletCharacter_inv_apply_conj]
  by_cases hu : IsUnit ((n : ℕ) : ZMod (q * q'))
  · rw [changeLevel_apply_natCast_of_isUnit (dvd_mul_right q q') χ n hu,
      changeLevel_apply_natCast_of_isUnit (dvd_mul_left q' q) χ' n hu]
  · have hncop : ¬n.Coprime (q * q') := fun hcop =>
      hu ((ZMod.isUnit_iff_coprime n (q * q')).mpr hcop)
    rw [MulChar.map_nonunit _ hu, zero_mul]
    by_cases hcq : n.Coprime q
    · have hcq' : ¬n.Coprime q' := fun hc => hncop (Nat.Coprime.mul_right hcq hc)
      rw [MulChar.map_nonunit χ' (fun hun => hcq' ((ZMod.isUnit_iff_coprime n q').mp hun)),
        map_zero, mul_zero]
    · rw [MulChar.map_nonunit χ (fun hun => hcq ((ZMod.isUnit_iff_coprime n q).mp hun)),
        zero_mul]

/-- Archimedean part of the composite-twist identity: for `0 < n`,

`n^{it} · conj(n^{it'}) = n^{i(t−t')}`.

Proved through `exp`/`log` at the positive real base `n`, where `log n` is real (conjugation
fixes it) and `conj(i·t') = −i·t'`. -/
theorem natCast_cpow_mul_conj_cpow {n : ℕ} (hn : 0 < n) (t t' : ℝ) :
    (n : ℂ) ^ (Complex.I * (t : ℂ)) * (starRingEnd ℂ) ((n : ℂ) ^ (Complex.I * (t' : ℂ)))
      = (n : ℂ) ^ (Complex.I * ((t - t' : ℝ) : ℂ)) := by
  have hn0 : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hlog : (starRingEnd ℂ) (Complex.log ((n : ℕ) : ℂ)) = Complex.log ((n : ℕ) : ℂ) := by
    rw [← Complex.natCast_log, Complex.conj_ofReal]
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0,
    Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_conj, map_mul, hlog, map_mul,
    Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Composite-twist identity** (Tao 2015 §4, `𝐭`-cutting lemma bookkeeping): for `0 < n`,
the single twist at modulus `q·q'`, character `changeLevel χ · (changeLevel χ')⁻¹`, and
frequency `t − t'` is the product of the `χ`-twist with the conjugated `χ'`-twist:

`charTwist (q·q') (χ·conj χ') (t − t') n = charTwist q χ t n · conj (charTwist q' χ' t' n)`. -/
theorem charTwist_mul_conj_charTwist {q q' : ℕ} (χ : DirichletCharacter ℂ q)
    (χ' : DirichletCharacter ℂ q') (t t' : ℝ) {n : ℕ} (hn : 0 < n) :
    charTwist (q * q')
        (DirichletCharacter.changeLevel (dvd_mul_right q q') χ
          * (DirichletCharacter.changeLevel (dvd_mul_left q' q) χ')⁻¹) (t - t') n
      = charTwist q χ t n * (starRingEnd ℂ) (charTwist q' χ' t' n) := by
  simp only [charTwist]
  rw [map_mul, changeLevel_mul_changeLevel_inv_apply_natCast,
    ← natCast_cpow_mul_conj_cpow hn t t']
  ring

/-- **Pair-of-twists distance as a single composite-twist distance** (Tao 2015 §4, proof of
the `𝐭`-cutting lemma): the pretentious distance between the two character twists produced by
Proposition 1.11 equals the distance from the constant `1` to the composite twist at modulus
`q·q'`, character `changeLevel χ · (changeLevel χ')⁻¹`, and frequency `t − t'` — the exact
left-hand-side shape consumed by the Vinogradov–Korobov interface. In the paper's notation:

`∑_{p ≤ X^δ} (1 − Re χ(p) conj(χ'(p)) p^{−i(𝐭'−𝐭)})/p = 𝔻(1, χ''(·)·(·)^{i(𝐭−𝐭')}; X^δ)²`.

The summands agree prime by prime (`charTwist_mul_conj_charTwist`; primes are positive, so no
junk case arises). The hypotheses `q ≠ 0`, `q' ≠ 0` are not needed for the identity but are
kept for the Lemma-"tb" call-site shape (its interface has `1 ≤ q`). -/
theorem pretentiousDistSq_one_charTwist_mul {q q' : ℕ} (hq : q ≠ 0) (hq' : q' ≠ 0)
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q') (t t' : ℝ) (N : ℕ) :
    pretentiousDistSq (fun _ => 1)
        (charTwist (q * q')
          (DirichletCharacter.changeLevel (dvd_mul_right q q') χ
            * (DirichletCharacter.changeLevel (dvd_mul_left q' q) χ')⁻¹)
          (t - t')) N
      = pretentiousDistSq (charTwist q χ t) (charTwist q' χ' t') N := by
  unfold pretentiousDistSq
  refine Finset.sum_congr rfl fun p hp => ?_
  have hppos : 0 < p := (Nat.mem_primesBelow.mp hp).2.pos
  have hD := charTwist_mul_conj_charTwist χ χ' t t' hppos
  simp only [hD, one_mul, Complex.conj_re]

/-- Composite-modulus bound for feeding the Vinogradov–Korobov quantifier `(q : ℝ) ≤ Q`:
if `q ≤ Q` and `q' ≤ Q'` (with `0 ≤ Q`), then `q·q' ≤ Q·Q'`. -/
theorem natCast_mul_le_mul {q q' : ℕ} {Q Q' : ℝ} (hqQ : (q : ℝ) ≤ Q)
    (hq'Q' : (q' : ℝ) ≤ Q') (hQ : 0 ≤ Q) : ((q * q' : ℕ) : ℝ) ≤ Q * Q' := by
  push_cast
  exact mul_le_mul hqQ hq'Q' (Nat.cast_nonneg q') hQ

end MoltResearch
