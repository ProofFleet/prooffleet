import MoltResearch.Discrepancy.ArchimedeanTaylor
import MoltResearch.Discrepancy.PrimeSumBounds
import MoltResearch.Discrepancy.ZetaWeighted

/-!
# Discrepancy: zeta-weighted window transfer across the twist `n ↦ n^{i𝐭}`

Deterministic Taylor-transfer step of Tao 2015 (arXiv:1509.05363, §4): if `g(n) = w(n)·n^{i𝐭}`
with `1`-bounded `w` and the zeta-weighted squared windows of `g` satisfy

`∑_n |∑_{m=1}^{H'} g(n+m)|² / n^{1+1/log X} ≤ D·log X`,

then the same holds for `w` with an explicit additive loss. Following the paper:

> "For `n ≥ X^{2δ}`, we can use \eqref{t-bound} and Taylor expansion to conclude that
> `(n+m)^{i𝐭} = n^{i𝐭} + O(X^{−δ})`. The contribution of the error term is negligible …
> For `n < X^{2δ}` we can crudely bound the left-hand side by `H²`."

Here `δ = 1/4` is fixed: the twist bound is `|𝐭| ≤ T·X^{1/4}`, the crude-region cutoff is
`X^{1/2}` (as literal exponents `(1:ℝ)/4`, `(1:ℝ)/2`). All constants are crude and explicit;
the final loss in `sum_div_normSq_window_twisted_le` is `(H')²·(2 + 18·T·H')·log X`
(crude region ≤ `2(H')²·log X` via the harmonic sum; Taylor tail ≤ `18T(H')³·log X` via
`∑ n⁻¹⁻¹ᐟˡᵒᵍ ˣ ≤ 2 + log X` and `log X ≤ 4X^{1/4}`).

Junk conventions: all `tsum`s run over all of `ℕ`; the `n = 0` term vanishes because
`(0:ℝ)^{1+1/log X} = 0` and `x/0 = 0`.
-/

namespace MoltResearch

open Finset

/-- `1 < log X` for `X ≥ 3` (the same crude bound as in `PrimeSumBounds`). -/
private lemma one_lt_log_aux {X : ℝ} (hX : 3 ≤ X) : 1 < Real.log X := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    _ ≤ Real.log X := Real.log_le_log (by norm_num) hX

/-- Crude calculus bound `log X ≤ 4·X^{1/4}` for `X ≥ 1`, via `log y ≤ y − 1` at
`y = X^{1/4}`. -/
private lemma log_le_four_mul_rpow {X : ℝ} (hX : 1 ≤ X) :
    Real.log X ≤ 4 * X ^ ((1 : ℝ)/4) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have h1 : Real.log (X ^ ((1 : ℝ)/4)) = (1/4) * Real.log X := Real.log_rpow hX0 _
  have h2 : Real.log (X ^ ((1 : ℝ)/4)) ≤ X ^ ((1 : ℝ)/4) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hX0 _)
  linarith

/-- Same-denominator division monotonicity with a merely nonnegative denominator
(the `c = 0` case is `0 ≤ 0` by junk conventions). -/
private lemma div_le_div_of_nonneg_denom {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) :
    a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hc)

private lemma sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith

/-- Windows of weights that are `1`-bounded away from `0` are bounded by the window
length: `‖∑_{m=1}^{H'} u(n+m)‖ ≤ H'` (every argument `n + m` is `≥ 1`). -/
private lemma norm_window_sum_le {u : ℕ → ℂ} (hu : ∀ k : ℕ, k ≠ 0 → ‖u k‖ ≤ 1)
    (n H' : ℕ) : ‖∑ m ∈ Finset.Icc 1 H', u (n + m)‖ ≤ (H' : ℝ) := by
  calc ‖∑ m ∈ Finset.Icc 1 H', u (n + m)‖
      ≤ ∑ m ∈ Finset.Icc 1 H', ‖u (n + m)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 H', (1 : ℝ) := by
        refine Finset.sum_le_sum fun m hm => hu (n + m) ?_
        have := (Finset.mem_Icc.mp hm).1
        omega
    _ = (H' : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]

/-- Quadratic transfer inequality: if `0 ≤ s ≤ a + e`, `s ≤ Hr`, `a ≤ Hr` then
`s² ≤ a² + 3·Hr·e`. Both regimes (`e ≤ Hr`: genuine Taylor gain; `e > Hr`: the trivial
window bound already wins) land in the same right-hand side. -/
private lemma sq_le_sq_add_three_mul {s a e Hr : ℝ} (hs0 : 0 ≤ s) (hsae : s ≤ a + e)
    (hsH : s ≤ Hr) (haH : a ≤ Hr) (ha0 : 0 ≤ a) (he0 : 0 ≤ e) :
    s ^ 2 ≤ a ^ 2 + 3 * Hr * e := by
  have hH0 : 0 ≤ Hr := le_trans ha0 haH
  rcases le_or_gt e Hr with hc | hc
  · have h1 : s ^ 2 ≤ (a + e) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right haH he0, mul_le_mul_of_nonneg_right hc he0]
  · have h1 : s ^ 2 ≤ Hr ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hc.le hH0, sq_nonneg a, mul_nonneg hH0 he0]

/-- If `g = w·n^{i𝐭}` away from `0` and `w` is `1`-bounded, then `g` is `1`-bounded away
from `0` (unimodularity of the twist). -/
private lemma norm_g_le_one {g w : ℕ → ℂ} {t : ℝ}
    (hfac : ∀ n : ℕ, n ≠ 0 → g n = w n * (n : ℂ) ^ (Complex.I * (t : ℂ)))
    (hwb : ∀ n, ‖w n‖ ≤ 1) {k : ℕ} (hk : k ≠ 0) : ‖g k‖ ≤ 1 := by
  rw [hfac k hk, norm_mul, norm_natCast_cpow_I_mul hk t, mul_one]
  exact hwb k

/-- **Pointwise window comparison** (Tao 2015 §4, Taylor step in comparison form): for
`n ≠ 0`, the untwisted window of `w` is controlled by the window of `g = w·(·)^{i𝐭}` plus
the Taylor error `H'·(|𝐭|·H'/n)`. -/
private lemma norm_window_le_add {g w : ℕ → ℂ} {t : ℝ}
    (hfac : ∀ n : ℕ, n ≠ 0 → g n = w n * (n : ℂ) ^ (Complex.I * (t : ℂ)))
    (hwb : ∀ n, ‖w n‖ ≤ 1) {n : ℕ} (hn : n ≠ 0) (H' : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖
      ≤ ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ + H' * (|t| * H' / n) := by
  -- the Taylor engine, beta-reduced by a defeq `have`
  have hsub : ‖(∑ m ∈ Finset.Icc 1 H', w (n + m) * ((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)))
        - ((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) * ∑ m ∈ Finset.Icc 1 H', w (n + m)‖
      ≤ H' * (|t| * H' / n) :=
    norm_windowTwistSum_sub_le (u := fun k => w (n + k)) (fun k => hwb (n + k)) hn H' t
  -- rewrite the `g`-window as a twisted `w`-window
  have hG : ∑ m ∈ Finset.Icc 1 H', g (n + m)
      = ∑ m ∈ Finset.Icc 1 H', w (n + m) * ((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    refine hfac (n + m) ?_
    have := (Finset.mem_Icc.mp hm).1
    omega
  -- unimodularity + triangle inequality
  have h1 : ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖
      = ‖((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) * ∑ m ∈ Finset.Icc 1 H', w (n + m)‖ := by
    rw [norm_mul, norm_natCast_cpow_I_mul hn t, one_mul]
  have h2 : ‖((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) * ∑ m ∈ Finset.Icc 1 H', w (n + m)‖
      ≤ ‖∑ m ∈ Finset.Icc 1 H', w (n + m) * ((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))‖
        + ‖(∑ m ∈ Finset.Icc 1 H', w (n + m) * ((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)))
            - ((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) * ∑ m ∈ Finset.Icc 1 H', w (n + m)‖ := by
    calc ‖((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) * ∑ m ∈ Finset.Icc 1 H', w (n + m)‖
        = ‖(∑ m ∈ Finset.Icc 1 H', w (n + m) * ((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)))
            - ((∑ m ∈ Finset.Icc 1 H', w (n + m) * ((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)))
              - ((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) * ∑ m ∈ Finset.Icc 1 H', w (n + m))‖ := by
          rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  rw [hG]
  calc ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖
      ≤ ‖∑ m ∈ Finset.Icc 1 H', w (n + m) * ((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))‖
        + ‖(∑ m ∈ Finset.Icc 1 H', w (n + m) * ((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)))
            - ((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) * ∑ m ∈ Finset.Icc 1 H', w (n + m)‖ :=
        h1 ▸ h2
    _ ≤ _ := by linarith [hsub]

/-- **Pointwise squared window comparison**: for `n ≠ 0`,
`‖∑_m w(n+m)‖² ≤ ‖∑_m g(n+m)‖² + 3·(H')³·|𝐭|/n`. -/
private lemma normSq_window_le_add {g w : ℕ → ℂ} {t : ℝ}
    (hfac : ∀ n : ℕ, n ≠ 0 → g n = w n * (n : ℂ) ^ (Complex.I * (t : ℂ)))
    (hwb : ∀ n, ‖w n‖ ≤ 1) {n : ℕ} (hn : n ≠ 0) (H' : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖ ^ 2
      ≤ ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 + 3 * (H' : ℝ) ^ 3 * |t| / n := by
  have hW : ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖ ≤ (H' : ℝ) :=
    norm_window_sum_le (fun k _ => hwb k) n H'
  have hG : ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ≤ (H' : ℝ) :=
    norm_window_sum_le (fun k hk => norm_g_le_one hfac hwb hk) n H'
  have he0 : 0 ≤ (H' : ℝ) * (|t| * H' / n) := by positivity
  have h := sq_le_sq_add_three_mul (norm_nonneg _)
    (norm_window_le_add hfac hwb hn H') hW hG (norm_nonneg _) he0
  refine h.trans (le_of_eq ?_)
  ring

/-- Zeta-weighted squared windows of `1`-bounded (away from `0`) weights are summable
at any exponent `σ > 1` (domination by `(H')²/n^σ`, mirroring `summable_norm_zetaWeight`). -/
private lemma summable_normSq_window_div {u : ℕ → ℂ} (hu : ∀ k : ℕ, k ≠ 0 → ‖u k‖ ≤ 1)
    (H' : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => ‖∑ m ∈ Finset.Icc 1 H', u (n + m)‖ ^ 2 / (n : ℝ) ^ σ := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((Real.summable_one_div_nat_rpow.mpr hσ).mul_left ((H' : ℝ) ^ 2))
  rw [mul_one_div]
  exact div_le_div_of_nonneg_denom
    (sq_le_sq_of_nonneg (norm_nonneg _) (norm_window_sum_le hu n H'))
    (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

/-- **Crude-region bound** (Tao 2015 §4: "for `n < X^{2δ}` we can crudely bound … by `H²`"):
the finite sum of `(H')²/n^{1+1/log X}` over `1 ≤ n ≤ ⌊X^{1/2}⌋` costs at most
`2·(H')²·log X` — harmonic sum plus `log⌊X^{1/2}⌋ ≤ ½·log X`. -/
private lemma sum_crude_region_le {X : ℝ} (hX : 3 ≤ X) (H' : ℕ) :
    ∑ n ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊,
        (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X))
      ≤ 2 * (H' : ℝ) ^ 2 * Real.log X := by
  have hlog1 : 1 < Real.log X := one_lt_log_aux hX
  have hX0 : (0 : ℝ) < X := by linarith
  -- each zeta weight is dominated by the harmonic weight
  have hstep : ∀ n ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊,
      (1 : ℝ) / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ 1 / (n : ℝ) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have h0 : (0 : ℝ) ≤ 1 / Real.log X := one_div_nonneg.mpr (by linarith)
    have h2 : (n : ℝ) ^ (1 : ℝ) ≤ (n : ℝ) ^ (1 + 1 / Real.log X) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [Real.rpow_one] at h2
    exact one_div_le_one_div_of_le (by linarith) h2
  -- harmonic sum bound
  have hharm : ∑ n ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊, (1 : ℝ) / (n : ℝ)
      ≤ 1 + Real.log ⌊X ^ ((1 : ℝ)/2)⌋₊ := by
    have h1 : (harmonic ⌊X ^ ((1 : ℝ)/2)⌋₊ : ℝ)
        = ∑ n ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊, (1 : ℝ) / (n : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    rw [← h1]
    exact harmonic_le_one_add_log _
  -- the floor is between `1` and `X^{1/2}`
  have hB1 : 1 ≤ ⌊X ^ ((1 : ℝ)/2)⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_one]
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hlogB : Real.log ⌊X ^ ((1 : ℝ)/2)⌋₊ ≤ Real.log X / 2 := by
    have hB0 : (0 : ℝ) < (⌊X ^ ((1 : ℝ)/2)⌋₊ : ℝ) := by exact_mod_cast hB1
    calc Real.log ⌊X ^ ((1 : ℝ)/2)⌋₊
        ≤ Real.log (X ^ ((1 : ℝ)/2)) :=
          Real.log_le_log hB0 (Nat.floor_le (Real.rpow_nonneg hX0.le _))
      _ = (1/2) * Real.log X := Real.log_rpow hX0 _
      _ = Real.log X / 2 := by ring
  calc ∑ n ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊,
        (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X))
      = (H' : ℝ) ^ 2 * ∑ n ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊,
          (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by rw [← Finset.mul_sum]
    _ ≤ (H' : ℝ) ^ 2 * (2 * Real.log X) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := Finset.sum_le_sum hstep
        linarith
    _ = 2 * (H' : ℝ) ^ 2 * Real.log X := by ring

/-- **Taylor-tail constant**: with `|𝐭| ≤ T·X^{1/4}` the total tail error constant
`(3(H')³|𝐭|/X^{1/2})·(2 + log X)` is at most `18·(H')³·T` (using `log X ≤ 4X^{1/4}`,
so `2 + log X ≤ 6X^{1/4}`, and `X^{1/2} = X^{1/4}·X^{1/4}`). -/
private lemma tail_const_le {X T t : ℝ} (hX : 3 ≤ X) (hT : 1 ≤ T)
    (ht : |t| ≤ T * X ^ ((1 : ℝ)/4)) (H' : ℕ) :
    3 * (H' : ℝ) ^ 3 * |t| / X ^ ((1 : ℝ)/2) * (2 + Real.log X)
      ≤ 18 * (H' : ℝ) ^ 3 * T := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog1 : 1 < Real.log X := one_lt_log_aux hX
  have ha0 : (0 : ℝ) < X ^ ((1 : ℝ)/4) := Real.rpow_pos_of_pos hX0 _
  have ha1 : (1 : ℝ) ≤ X ^ ((1 : ℝ)/4) := Real.one_le_rpow (by linarith) (by norm_num)
  have hhalf : X ^ ((1 : ℝ)/2) = X ^ ((1 : ℝ)/4) * X ^ ((1 : ℝ)/4) := by
    rw [← Real.rpow_add hX0]
    norm_num
  have h6 : 2 + Real.log X ≤ 6 * X ^ ((1 : ℝ)/4) := by
    have h4 := log_le_four_mul_rpow (by linarith : (1 : ℝ) ≤ X)
    linarith
  have hprod : |t| * (2 + Real.log X) ≤ T * X ^ ((1 : ℝ)/4) * (6 * X ^ ((1 : ℝ)/4)) :=
    mul_le_mul ht h6 (by linarith) (mul_nonneg (by linarith) ha0.le)
  have hnum : 3 * (H' : ℝ) ^ 3 * |t| * (2 + Real.log X)
      ≤ 18 * (H' : ℝ) ^ 3 * T * (X ^ ((1 : ℝ)/4) * X ^ ((1 : ℝ)/4)) := by
    calc 3 * (H' : ℝ) ^ 3 * |t| * (2 + Real.log X)
        = 3 * (H' : ℝ) ^ 3 * (|t| * (2 + Real.log X)) := by ring
      _ ≤ 3 * (H' : ℝ) ^ 3 * (T * X ^ ((1 : ℝ)/4) * (6 * X ^ ((1 : ℝ)/4))) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 18 * (H' : ℝ) ^ 3 * T * (X ^ ((1 : ℝ)/4) * X ^ ((1 : ℝ)/4)) := by ring
  rw [hhalf, div_mul_eq_mul_div, div_le_iff₀ (mul_pos ha0 ha0)]
  exact hnum

/-- **Zeta-weighted window transfer across the archimedean twist** (Tao 2015,
arXiv:1509.05363, §4, "the first step is to eliminate the role of `n^{i𝐭}`"):

if `g(n) = w(n)·n^{i𝐭}` for `n ≠ 0` with `‖w‖ ≤ 1`, `|𝐭| ≤ T·X^{1/4}` (the paper's
`𝐭 = O(X^δ)` at `δ = 1/4`), and the zeta-weighted squared windows of `g` are
`≤ D·log X`, then those of `w` are `≤ (D + (H')²·(2 + 18·T·H'))·log X`.

Shape of the explicit loss: the crude region `n ≤ X^{1/2}` contributes `≤ 2(H')²·log X`
(harmonic sum), and the Taylor error `3(H')³|𝐭|/n` on `n > X^{1/2}` contributes
`≤ 18T(H')³ ≤ 18T(H')³·log X` (via `∑_n n^{-1-1/log X} ≤ 2 + log X` and
`log X ≤ 4X^{1/4}`). Junk conventions make the `n = 0` terms vanish on both sides. -/
theorem sum_div_normSq_window_twisted_le
    {g w : ℕ → ℂ} {t : ℝ}
    (hfac : ∀ n : ℕ, n ≠ 0 → g n = w n * (n : ℂ) ^ (Complex.I * (t : ℂ)))
    (hwb : ∀ n, ‖w n‖ ≤ 1)
    {X T : ℝ} (hX : 3 ≤ X) (hT : 1 ≤ T) (ht : |t| ≤ T * X ^ ((1 : ℝ)/4))
    {H' : ℕ} (hH' : 1 ≤ H')
    {D : ℝ}
    (hg : ∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
      ≤ D * Real.log X) :
    ∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
      ≤ (D + (H' : ℝ) ^ 2 * (2 + 18 * T * (H' : ℝ))) * Real.log X := by
  have hlog1 : 1 < Real.log X := one_lt_log_aux hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hσ1 : 1 < 1 + 1 / Real.log X := by
    have h0 : (0 : ℝ) < 1 / Real.log X := by
      rw [one_div]
      exact inv_pos.mpr (by linarith)
    linarith
  have hgb : ∀ k : ℕ, k ≠ 0 → ‖g k‖ ≤ 1 := fun k hk => norm_g_le_one hfac hwb hk
  have hc0 : (0 : ℝ) ≤ 3 * (H' : ℝ) ^ 3 * |t| / X ^ ((1 : ℝ)/2) :=
    div_nonneg (by positivity) (Real.rpow_nonneg hX0.le _)
  -- summability of all four pieces
  have hsummZ : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + 1 / Real.log X) :=
    Real.summable_one_div_nat_rpow.mpr hσ1
  have hsummW : Summable fun n : ℕ =>
      ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X) :=
    summable_normSq_window_div (fun k _ => hwb k) H' hσ1
  have hsummG : Summable fun n : ℕ =>
      ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X) :=
    summable_normSq_window_div hgb H' hσ1
  have hsummE : Summable fun n : ℕ =>
      3 * (H' : ℝ) ^ 3 * |t| / X ^ ((1 : ℝ)/2) * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) :=
    hsummZ.mul_left _
  have hsummI : Summable fun n : ℕ =>
      if n ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊ then
        (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) else 0 :=
    summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊)
      fun n hn => if_neg hn
  -- pointwise majorization: `w`-window ≤ `g`-window + Taylor tail + crude region
  have hpt : ∀ n : ℕ,
      ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
        ≤ ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
            + 3 * (H' : ℝ) ^ 3 * |t| / X ^ ((1 : ℝ)/2)
              * (1 / (n : ℝ) ^ (1 + 1 / Real.log X))
            + (if n ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊ then
                (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) else 0) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · -- junk row: everything vanishes
      have hz : ((0 : ℕ) : ℝ) ^ (1 + 1 / Real.log X) = 0 := by
        rw [Nat.cast_zero]
        exact Real.zero_rpow (by linarith : (0 : ℝ) < 1 + 1 / Real.log X).ne'
      simp only [hz, div_zero, mul_zero, ite_self, add_zero, zero_add, le_refl]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hnp : (0 : ℝ) ≤ (n : ℝ) ^ (1 + 1 / Real.log X) :=
        Real.rpow_nonneg (by linarith) _
      by_cases hmem : n ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊
      · -- crude region: charge everything to the `(H')²` column
        rw [if_pos hmem]
        have hWH : ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
            ≤ (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_denom
            (sq_le_sq_of_nonneg (norm_nonneg _)
              (norm_window_sum_le (fun k _ => hwb k) n H')) hnp
        have hg0 : (0 : ℝ)
            ≤ ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X) := by
          positivity
        have he0 : (0 : ℝ) ≤ 3 * (H' : ℝ) ^ 3 * |t| / X ^ ((1 : ℝ)/2)
            * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) :=
          mul_nonneg hc0 (by positivity)
        linarith
      · -- Taylor region `n > X^{1/2}`: the pointwise squared comparison
        rw [if_neg hmem, add_zero]
        have hBn : ⌊X ^ ((1 : ℝ)/2)⌋₊ < n :=
          not_le.mp fun hle => hmem (Finset.mem_Icc.mpr ⟨hn1, hle⟩)
        have hXn : X ^ ((1 : ℝ)/2) ≤ (n : ℝ) := by
          have hlt : X ^ ((1 : ℝ)/2) < (⌊X ^ ((1 : ℝ)/2)⌋₊ : ℝ) + 1 :=
            Nat.lt_floor_add_one _
          have hle : (⌊X ^ ((1 : ℝ)/2)⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt hBn
          linarith
        have hdiv : ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
            ≤ (‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 + 3 * (H' : ℝ) ^ 3 * |t| / n)
              / (n : ℝ) ^ (1 + 1 / Real.log X) :=
          div_le_div_of_nonneg_denom (normSq_window_le_add hfac hwb hn0 H') hnp
        have hsplit : (‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2
              + 3 * (H' : ℝ) ^ 3 * |t| / n) / (n : ℝ) ^ (1 + 1 / Real.log X)
            = ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
              + 3 * (H' : ℝ) ^ 3 * |t| / n * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by
          rw [add_div, div_eq_mul_one_div (3 * (H' : ℝ) ^ 3 * |t| / n)
            ((n : ℝ) ^ (1 + 1 / Real.log X))]
        rw [hsplit] at hdiv
        have herr : 3 * (H' : ℝ) ^ 3 * |t| / n * (1 / (n : ℝ) ^ (1 + 1 / Real.log X))
            ≤ 3 * (H' : ℝ) ^ 3 * |t| / X ^ ((1 : ℝ)/2)
              * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hx2 : (0 : ℝ) < X ^ ((1 : ℝ)/2) := Real.rpow_pos_of_pos hX0 _
          have hinv : 1 / (n : ℝ) ≤ 1 / X ^ ((1 : ℝ)/2) :=
            one_div_le_one_div_of_le hx2 hXn
          calc 3 * (H' : ℝ) ^ 3 * |t| / n
              = 3 * (H' : ℝ) ^ 3 * |t| * (1 / (n : ℝ)) := div_eq_mul_one_div _ _
            _ ≤ 3 * (H' : ℝ) ^ 3 * |t| * (1 / X ^ ((1 : ℝ)/2)) :=
                mul_le_mul_of_nonneg_left hinv (by positivity)
            _ = 3 * (H' : ℝ) ^ 3 * |t| / X ^ ((1 : ℝ)/2) := mul_one_div _ _
        linarith
  -- convert the indicator tsum into the finite crude-region sum
  have hIsum : (∑ n ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊,
        if n ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊ then
          (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) else 0)
      = ∑ n ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊,
          (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) :=
    Finset.sum_congr rfl fun n hn => if_pos hn
  -- the three budget lines
  have h2 : 3 * (H' : ℝ) ^ 3 * |t| / X ^ ((1 : ℝ)/2)
        * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / Real.log X)
      ≤ 18 * (H' : ℝ) ^ 3 * T :=
    (mul_le_mul_of_nonneg_left (tsum_one_div_rpow_le_two_add_log hX) hc0).trans
      (tail_const_le hX hT ht H')
  have h3 := sum_crude_region_le hX H'
  have hc18 : (0 : ℝ) ≤ 18 * (H' : ℝ) ^ 3 * T :=
    mul_nonneg (by positivity) (by linarith)
  have h4 : 18 * (H' : ℝ) ^ 3 * T ≤ 18 * (H' : ℝ) ^ 3 * T * Real.log X := by
    nlinarith [mul_nonneg hc18 (by linarith : (0 : ℝ) ≤ Real.log X - 1)]
  -- assemble
  calc ∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
      ≤ ∑' n : ℕ,
          (‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
            + 3 * (H' : ℝ) ^ 3 * |t| / X ^ ((1 : ℝ)/2)
              * (1 / (n : ℝ) ^ (1 + 1 / Real.log X))
            + (if n ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊ then
                (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) else 0)) :=
        Summable.tsum_le_tsum hpt hsummW ((hsummG.add hsummE).add hsummI)
    _ = (∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X))
          + 3 * (H' : ℝ) ^ 3 * |t| / X ^ ((1 : ℝ)/2)
            * (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / Real.log X))
          + ∑ n ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊,
              (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by
        rw [Summable.tsum_add (hsummG.add hsummE) hsummI,
          Summable.tsum_add hsummG hsummE, tsum_mul_left,
          tsum_eq_sum (s := Finset.Icc 1 ⌊X ^ ((1 : ℝ)/2)⌋₊) (fun n hn => if_neg hn),
          hIsum]
    _ ≤ D * Real.log X + 18 * (H' : ℝ) ^ 3 * T + 2 * (H' : ℝ) ^ 2 * Real.log X := by
        linarith
    _ ≤ D * Real.log X + 18 * (H' : ℝ) ^ 3 * T * Real.log X
          + 2 * (H' : ℝ) ^ 2 * Real.log X := by linarith
    _ = (D + (H' : ℝ) ^ 2 * (2 + 18 * T * (H' : ℝ))) * Real.log X := by ring

/-- **Parametric crude-region bound** (Tao 2015 §4: "for `n < X^{2δ}` we can crudely bound
… by `H²`", with the exponent `δ` a parameter): the finite sum of `(H')²/n^{1+1/log X}` over
`1 ≤ n ≤ ⌊X^{2δ}⌋` costs at most `(H')²·(1 + 2δ·log X)` — harmonic sum plus
`log⌊X^{2δ}⌋ ≤ 2δ·log X`, kept exact (not absorbed into the log term) so the caller can take
`δ` small depending on `H'`. -/
private lemma sum_crude_region_le_param {X δ : ℝ} (hX : 3 ≤ X) (hδ0 : 0 < δ) (H' : ℕ) :
    ∑ n ∈ Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊,
        (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X))
      ≤ (H' : ℝ) ^ 2 * (1 + 2 * δ * Real.log X) := by
  have hlog1 : 1 < Real.log X := one_lt_log_aux hX
  have hX0 : (0 : ℝ) < X := by linarith
  -- each zeta weight is dominated by the harmonic weight
  have hstep : ∀ n ∈ Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊,
      (1 : ℝ) / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ 1 / (n : ℝ) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have h0 : (0 : ℝ) ≤ 1 / Real.log X := one_div_nonneg.mpr (by linarith)
    have h2 : (n : ℝ) ^ (1 : ℝ) ≤ (n : ℝ) ^ (1 + 1 / Real.log X) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [Real.rpow_one] at h2
    exact one_div_le_one_div_of_le (by linarith) h2
  -- harmonic sum bound
  have hharm : ∑ n ∈ Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊, (1 : ℝ) / (n : ℝ)
      ≤ 1 + Real.log ⌊X ^ (2 * δ)⌋₊ := by
    have h1 : (harmonic ⌊X ^ (2 * δ)⌋₊ : ℝ)
        = ∑ n ∈ Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊, (1 : ℝ) / (n : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    rw [← h1]
    exact harmonic_le_one_add_log _
  -- the floor is between `1` and `X^{2δ}`
  have hB1 : 1 ≤ ⌊X ^ (2 * δ)⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_one]
    exact Real.one_le_rpow (by linarith) (by linarith)
  have hlogB : Real.log ⌊X ^ (2 * δ)⌋₊ ≤ 2 * δ * Real.log X := by
    have hB0 : (0 : ℝ) < (⌊X ^ (2 * δ)⌋₊ : ℝ) := by exact_mod_cast hB1
    calc Real.log ⌊X ^ (2 * δ)⌋₊
        ≤ Real.log (X ^ (2 * δ)) :=
          Real.log_le_log hB0 (Nat.floor_le (Real.rpow_nonneg hX0.le _))
      _ = 2 * δ * Real.log X := Real.log_rpow hX0 _
  calc ∑ n ∈ Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊,
        (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X))
      = (H' : ℝ) ^ 2 * ∑ n ∈ Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊,
          (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by rw [← Finset.mul_sum]
    _ ≤ (H' : ℝ) ^ 2 * (1 + 2 * δ * Real.log X) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := Finset.sum_le_sum hstep
        linarith

/-- **Parametric Taylor-tail constant**: with `|𝐭| ≤ T·X^δ`, the total tail-error constant
`(3(H')³|𝐭|/X^{2δ})·(2 + log X)` is at most `3(H')³·T·(2 + log X)/X^δ`
(since `X^{2δ} = X^δ·X^δ`, the twist budget `T·X^δ` cancels one factor). -/
private lemma tail_const_le_param {X T δ t : ℝ} (hX : 3 ≤ X)
    (ht : |t| ≤ T * X ^ δ) (H' : ℕ) :
    3 * (H' : ℝ) ^ 3 * |t| / X ^ (2 * δ) * (2 + Real.log X)
      ≤ 3 * (H' : ℝ) ^ 3 * T * (2 + Real.log X) / X ^ δ := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog1 : 1 < Real.log X := one_lt_log_aux hX
  have hδpos : (0 : ℝ) < X ^ δ := Real.rpow_pos_of_pos hX0 _
  have h2δ : X ^ (2 * δ) = X ^ δ * X ^ δ := by
    rw [← Real.rpow_add hX0]
    congr 1
    ring
  have hq : |t| / X ^ (2 * δ) ≤ T / X ^ δ := by
    have h1 : |t| / X ^ δ ≤ T := by
      rw [div_le_iff₀ hδpos]
      exact ht
    calc |t| / X ^ (2 * δ) = |t| / X ^ δ / X ^ δ := by rw [h2δ, div_div]
      _ ≤ T / X ^ δ := div_le_div_of_nonneg_denom h1 hδpos.le
  calc 3 * (H' : ℝ) ^ 3 * |t| / X ^ (2 * δ) * (2 + Real.log X)
      = |t| / X ^ (2 * δ) * (3 * (H' : ℝ) ^ 3 * (2 + Real.log X)) := by ring
    _ ≤ T / X ^ δ * (3 * (H' : ℝ) ^ 3 * (2 + Real.log X)) :=
        mul_le_mul_of_nonneg_right hq (mul_nonneg (by positivity) (by linarith))
    _ = 3 * (H' : ℝ) ^ 3 * T * (2 + Real.log X) / X ^ δ := by ring

/-- **δ-parametric zeta-weighted window transfer across the archimedean twist**
(Tao 2015, arXiv:1509.05363, §4): additive form of `sum_div_normSq_window_twisted_le`
with the exponent `δ` a parameter — the paper's "for `n ≥ X^{2δ}` … Taylor expansion …
for `n < X^{2δ}` crude bound", quantified so the caller can take `δ` small depending on
`H'` (the loss coefficient of `log X` is `2δ(H')²`, plus an `X`-independent `(H')²` and an
`X^{−δ}`-decaying tail). No hypothesis on the `g`-side sum is needed: the comparison is
termwise. -/
theorem sum_div_normSq_window_twisted_le_add
    {g w : ℕ → ℂ} {t : ℝ}
    (hfac : ∀ n : ℕ, n ≠ 0 → g n = w n * (n : ℂ) ^ (Complex.I * (t : ℂ)))
    (hwb : ∀ n, ‖w n‖ ≤ 1)
    {X T δ : ℝ} (hX : 3 ≤ X) (hT : 1 ≤ T) (hδ0 : 0 < δ) (ht : |t| ≤ T * X ^ δ)
    {H' : ℕ} (hH' : 1 ≤ H') :
    ∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
      ≤ (∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X))
        + (H' : ℝ) ^ 2 * (1 + 2 * δ * Real.log X)
        + 3 * (H' : ℝ) ^ 3 * T * (2 + Real.log X) / X ^ δ := by
  have hlog1 : 1 < Real.log X := one_lt_log_aux hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hσ1 : 1 < 1 + 1 / Real.log X := by
    have h0 : (0 : ℝ) < 1 / Real.log X := by
      rw [one_div]
      exact inv_pos.mpr (by linarith)
    linarith
  have hgb : ∀ k : ℕ, k ≠ 0 → ‖g k‖ ≤ 1 := fun k hk => norm_g_le_one hfac hwb hk
  have hc0 : (0 : ℝ) ≤ 3 * (H' : ℝ) ^ 3 * |t| / X ^ (2 * δ) :=
    div_nonneg (by positivity) (Real.rpow_nonneg hX0.le _)
  -- summability of all four pieces
  have hsummZ : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + 1 / Real.log X) :=
    Real.summable_one_div_nat_rpow.mpr hσ1
  have hsummW : Summable fun n : ℕ =>
      ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X) :=
    summable_normSq_window_div (fun k _ => hwb k) H' hσ1
  have hsummG : Summable fun n : ℕ =>
      ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X) :=
    summable_normSq_window_div hgb H' hσ1
  have hsummE : Summable fun n : ℕ =>
      3 * (H' : ℝ) ^ 3 * |t| / X ^ (2 * δ) * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) :=
    hsummZ.mul_left _
  have hsummI : Summable fun n : ℕ =>
      if n ∈ Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊ then
        (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) else 0 :=
    summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊)
      fun n hn => if_neg hn
  -- pointwise majorization: `w`-window ≤ `g`-window + Taylor tail + crude region
  have hpt : ∀ n : ℕ,
      ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
        ≤ ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
            + 3 * (H' : ℝ) ^ 3 * |t| / X ^ (2 * δ)
              * (1 / (n : ℝ) ^ (1 + 1 / Real.log X))
            + (if n ∈ Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊ then
                (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) else 0) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · -- junk row: everything vanishes
      have hz : ((0 : ℕ) : ℝ) ^ (1 + 1 / Real.log X) = 0 := by
        rw [Nat.cast_zero]
        exact Real.zero_rpow (by linarith : (0 : ℝ) < 1 + 1 / Real.log X).ne'
      simp only [hz, div_zero, mul_zero, ite_self, add_zero, zero_add, le_refl]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hnp : (0 : ℝ) ≤ (n : ℝ) ^ (1 + 1 / Real.log X) :=
        Real.rpow_nonneg (by linarith) _
      by_cases hmem : n ∈ Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊
      · -- crude region: charge everything to the `(H')²` column
        rw [if_pos hmem]
        have hWH : ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
            ≤ (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_denom
            (sq_le_sq_of_nonneg (norm_nonneg _)
              (norm_window_sum_le (fun k _ => hwb k) n H')) hnp
        have hg0 : (0 : ℝ)
            ≤ ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X) := by
          positivity
        have he0 : (0 : ℝ) ≤ 3 * (H' : ℝ) ^ 3 * |t| / X ^ (2 * δ)
            * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) :=
          mul_nonneg hc0 (by positivity)
        linarith
      · -- Taylor region `n > X^{2δ}`: the pointwise squared comparison
        rw [if_neg hmem, add_zero]
        have hBn : ⌊X ^ (2 * δ)⌋₊ < n :=
          not_le.mp fun hle => hmem (Finset.mem_Icc.mpr ⟨hn1, hle⟩)
        have hXn : X ^ (2 * δ) ≤ (n : ℝ) := by
          have hlt : X ^ (2 * δ) < (⌊X ^ (2 * δ)⌋₊ : ℝ) + 1 :=
            Nat.lt_floor_add_one _
          have hle : (⌊X ^ (2 * δ)⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt hBn
          linarith
        have hdiv : ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
            ≤ (‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 + 3 * (H' : ℝ) ^ 3 * |t| / n)
              / (n : ℝ) ^ (1 + 1 / Real.log X) :=
          div_le_div_of_nonneg_denom (normSq_window_le_add hfac hwb hn0 H') hnp
        have hsplit : (‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2
              + 3 * (H' : ℝ) ^ 3 * |t| / n) / (n : ℝ) ^ (1 + 1 / Real.log X)
            = ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
              + 3 * (H' : ℝ) ^ 3 * |t| / n * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by
          rw [add_div, div_eq_mul_one_div (3 * (H' : ℝ) ^ 3 * |t| / n)
            ((n : ℝ) ^ (1 + 1 / Real.log X))]
        rw [hsplit] at hdiv
        have herr : 3 * (H' : ℝ) ^ 3 * |t| / n * (1 / (n : ℝ) ^ (1 + 1 / Real.log X))
            ≤ 3 * (H' : ℝ) ^ 3 * |t| / X ^ (2 * δ)
              * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hx2 : (0 : ℝ) < X ^ (2 * δ) := Real.rpow_pos_of_pos hX0 _
          have hinv : 1 / (n : ℝ) ≤ 1 / X ^ (2 * δ) :=
            one_div_le_one_div_of_le hx2 hXn
          calc 3 * (H' : ℝ) ^ 3 * |t| / n
              = 3 * (H' : ℝ) ^ 3 * |t| * (1 / (n : ℝ)) := div_eq_mul_one_div _ _
            _ ≤ 3 * (H' : ℝ) ^ 3 * |t| * (1 / X ^ (2 * δ)) :=
                mul_le_mul_of_nonneg_left hinv (by positivity)
            _ = 3 * (H' : ℝ) ^ 3 * |t| / X ^ (2 * δ) := mul_one_div _ _
        linarith
  -- convert the indicator tsum into the finite crude-region sum
  have hIsum : (∑ n ∈ Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊,
        if n ∈ Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊ then
          (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) else 0)
      = ∑ n ∈ Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊,
          (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) :=
    Finset.sum_congr rfl fun n hn => if_pos hn
  -- the two budget lines: Taylor tail and crude region
  have h2 : 3 * (H' : ℝ) ^ 3 * |t| / X ^ (2 * δ)
        * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / Real.log X)
      ≤ 3 * (H' : ℝ) ^ 3 * T * (2 + Real.log X) / X ^ δ :=
    (mul_le_mul_of_nonneg_left (tsum_one_div_rpow_le_two_add_log hX) hc0).trans
      (tail_const_le_param hX ht H')
  have h3 := sum_crude_region_le_param hX hδ0 H'
  -- assemble
  calc ∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', w (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
      ≤ ∑' n : ℕ,
          (‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
            + 3 * (H' : ℝ) ^ 3 * |t| / X ^ (2 * δ)
              * (1 / (n : ℝ) ^ (1 + 1 / Real.log X))
            + (if n ∈ Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊ then
                (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) else 0)) :=
        Summable.tsum_le_tsum hpt hsummW ((hsummG.add hsummE).add hsummI)
    _ = (∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X))
          + 3 * (H' : ℝ) ^ 3 * |t| / X ^ (2 * δ)
            * (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / Real.log X))
          + ∑ n ∈ Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊,
              (H' : ℝ) ^ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by
        rw [Summable.tsum_add (hsummG.add hsummE) hsummI,
          Summable.tsum_add hsummG hsummE, tsum_mul_left,
          tsum_eq_sum (s := Finset.Icc 1 ⌊X ^ (2 * δ)⌋₊) (fun n hn => if_neg hn),
          hIsum]
    _ ≤ (∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X))
          + (H' : ℝ) ^ 2 * (1 + 2 * δ * Real.log X)
          + 3 * (H' : ℝ) ^ 3 * T * (2 + Real.log X) / X ^ δ := by linarith

end MoltResearch
