import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Discrepancy: archimedean Taylor step for the twist `n ↦ n^{i𝐭}`

Deterministic engine for removing the archimedean character from window sums, following
Tao 2015 (arXiv:1509.05363, §4, proof of the generalized Borwein–Choi–Coons theorem):

> "For `n ≥ X^{2δ}`, we can use the bound `𝐭 = O(X^δ)` and Taylor expansion to conclude
> that `(n+m)^{i𝐭} = n^{i𝐭} + O(X^{−δ})`."

Three layers, with crude explicit constants throughout:

* `norm_exp_I_mul_sub_one_le`: the circle-arc (chord) bound `‖e^{iθ} − 1‖ ≤ |θ|`
  (the chord is shorter than the arc; via `‖e^{iθ} − 1‖ = |2 sin(θ/2)|` and `|sin| ≤ |·|`).
* `norm_natCast_cpow_I_mul_sub_le`: the Taylor step at natural points,
  `‖(n+m)^{i𝐭} − n^{i𝐭}‖ ≤ |𝐭|·m/n` for `n ≠ 0`, from `log(n+m) − log n = log(1 + m/n)
  ≤ m/n` and the chord bound. No lower bound on `n` is needed: the estimate is trivial
  unless `n` is much larger than `|𝐭|·m`.
* `norm_windowTwistSum_sub_le`: the consumer shape — over a window `m ∈ [1, H']` of
  `1`-bounded weights `u`, replacing every `(n+m)^{i𝐭}` by the single constant `n^{i𝐭}`
  costs at most `H'·(|𝐭|·H'/n)` (in the paper: `O(H² X^{δ} / X^{2δ}) = O(H² X^{−δ})`).
  Corollary `norm_windowTwistSum_le` gives the `‖A‖ ≤ ‖B‖ + err` comparison form.

Also included: `norm_natCast_cpow_I_mul`, unimodularity `‖n^{i𝐭}‖ = 1` for `n ≠ 0`
(for `n = 0` the junk value `(0:ℂ)^{i𝐭} = 0` would fail this, hence the hypothesis).

This module is deliberately dependency-light: it imports only Mathlib (no MoltResearch
modules), and is intended to be added to the stable surface `MoltResearch.Discrepancy`.
-/

namespace MoltResearch

/-- **Chord-versus-arc bound** on the unit circle: `‖e^{iθ} − 1‖ ≤ |θ|`.

This is the elementary estimate behind the Taylor expansion step of Tao 2015, §4: the
distance between two points on the unit circle is at most the angle between them. -/
theorem norm_exp_I_mul_sub_one_le (θ : ℝ) :
    ‖Complex.exp (Complex.I * θ) - 1‖ ≤ |θ| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  have h := mul_le_mul_of_nonneg_left
    (Real.abs_sin_le_abs : |Real.sin (θ / 2)| ≤ |θ / 2|) (by norm_num : (0 : ℝ) ≤ 2)
  refine h.trans (le_of_eq ?_)
  rw [abs_div, abs_two]
  ring

/-- The archimedean twist is unimodular at nonzero naturals: `‖n^{i𝐭}‖ = 1` for `n ≠ 0`.
(At `n = 0` the junk value `(0:ℂ)^{i𝐭} = 0` has norm `0`.) -/
theorem norm_natCast_cpow_I_mul {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    ‖((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))‖ = 1 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [← Complex.ofReal_natCast n, Complex.norm_cpow_eq_rpow_re_of_pos hn']
  simp [Complex.mul_re]

/-- **Taylor expansion step** (Tao 2015, §4): for `n ≠ 0`,

`‖(n+m)^{i𝐭} − n^{i𝐭}‖ ≤ |𝐭| · m / n`.

Proof: `(n+m)^{i𝐭} = n^{i𝐭} · e^{i𝐭(log(n+m) − log n)}`, the first factor is unimodular,
and the chord bound together with `log(n+m) − log n = log((n+m)/n) ≤ (n+m)/n − 1 = m/n`
finishes. In the paper this is applied with `|𝐭| = O(X^δ)`, `m ≤ H`, `n ≥ X^{2δ}`,
giving the error `O(X^{−δ})` per term. -/
theorem norm_natCast_cpow_I_mul_sub_le {n m : ℕ} (hn : n ≠ 0) (t : ℝ) :
    ‖((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) - ((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))‖
      ≤ |t| * m / n := by
  have hnm : n + m ≠ 0 := by omega
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnm' : (0 : ℝ) < ((n + m : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hnm
  have hlog_le : Real.log ((n : ℕ) : ℝ) ≤ Real.log ((n + m : ℕ) : ℝ) :=
    Real.log_le_log hn' (by exact_mod_cast Nat.le_add_right n m)
  -- both powers are exponentials of purely imaginary multiples of real logarithms
  have hcpow : ∀ k : ℕ, k ≠ 0 → ((k : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))
      = Complex.exp (Complex.I * (t : ℂ) * (Real.log ((k : ℕ) : ℝ) : ℂ)) := by
    intro k hk
    have hk0 : ((k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    rw [Complex.cpow_def_of_ne_zero hk0, ← Complex.natCast_log]
    congr 1
    ring
  -- split off the unimodular factor `n^{i𝐭}`
  have harg : Complex.I * (t : ℂ) * (Real.log ((n + m : ℕ) : ℝ) : ℂ)
      = Complex.I * (t : ℂ) * (Real.log ((n : ℕ) : ℝ) : ℂ)
        + Complex.I * ((t * (Real.log ((n + m : ℕ) : ℝ) - Real.log ((n : ℕ) : ℝ)) : ℝ) : ℂ) := by
    push_cast
    ring
  have hnorm1 : ‖Complex.exp (Complex.I * (t : ℂ) * (Real.log ((n : ℕ) : ℝ) : ℂ))‖ = 1 := by
    rw [show Complex.I * (t : ℂ) * (Real.log ((n : ℕ) : ℝ) : ℂ)
        = ((t * Real.log ((n : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hcpow (n + m) hnm, hcpow n hn, harg, Complex.exp_add, ← mul_sub_one, norm_mul,
    hnorm1, one_mul]
  refine (norm_exp_I_mul_sub_one_le _).trans ?_
  rw [abs_mul]
  -- the logarithmic increment is at most `m/n`
  have hL : |Real.log ((n + m : ℕ) : ℝ) - Real.log ((n : ℕ) : ℝ)| ≤ (m : ℝ) / (n : ℝ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hlog_le),
      ← Real.log_div (ne_of_gt hnm') (ne_of_gt hn')]
    calc Real.log (((n + m : ℕ) : ℝ) / ((n : ℕ) : ℝ))
        ≤ ((n + m : ℕ) : ℝ) / ((n : ℕ) : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hnm' hn')
      _ = (m : ℝ) / (n : ℝ) := by
          push_cast
          rw [add_div, div_self (ne_of_gt hn')]
          ring
  calc |t| * |Real.log ((n + m : ℕ) : ℝ) - Real.log ((n : ℕ) : ℝ)|
      ≤ |t| * ((m : ℝ) / (n : ℝ)) := mul_le_mul_of_nonneg_left hL (abs_nonneg t)
    _ = |t| * (m : ℝ) / (n : ℝ) := by ring

/-- **Window-sum twist removal** (Tao 2015, §4): for `1`-bounded weights `u` and `n ≠ 0`,
replacing every twist `(n+m)^{i𝐭}` in the window `m ∈ [1, H']` by the single constant
`n^{i𝐭}` costs at most `H' · (|𝐭| · H' / n)`:

`‖∑_{m=1}^{H'} u(m)(n+m)^{i𝐭} − n^{i𝐭} ∑_{m=1}^{H'} u(m)‖ ≤ H'·(|𝐭|·H'/n)`.

In the paper this is applied with `u(m) = 𝐠(n)⁻¹·𝐠(n+m)·χ̄(n+m)`-type weights, `|𝐭| ≤ X^δ`
and `n ≥ X^{2δ}`, making the right-hand side `O(H² X^{−δ})`. -/
theorem norm_windowTwistSum_sub_le {u : ℕ → ℂ} (hu : ∀ k, ‖u k‖ ≤ 1)
    {n : ℕ} (hn : n ≠ 0) (H' : ℕ) (t : ℝ) :
    ‖(∑ m ∈ Finset.Icc 1 H', u m * ((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)))
        - ((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) * ∑ m ∈ Finset.Icc 1 H', u m‖
      ≤ H' * (|t| * H' / n) := by
  have hterm : ∀ m ∈ Finset.Icc 1 H',
      ‖u m * ((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))
          - ((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) * u m‖
        ≤ |t| * (H' : ℝ) / (n : ℝ) := by
    intro m hm
    have hmH : (m : ℝ) ≤ (H' : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    rw [mul_comm (((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))) (u m), ← mul_sub, norm_mul]
    calc ‖u m‖ * ‖((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))
            - ((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))‖
        ≤ 1 * (|t| * (m : ℝ) / (n : ℝ)) :=
          mul_le_mul (hu m) (norm_natCast_cpow_I_mul_sub_le hn t) (norm_nonneg _)
            zero_le_one
      _ = |t| * (m : ℝ) / (n : ℝ) := one_mul _
      _ ≤ |t| * (H' : ℝ) / (n : ℝ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmH (abs_nonneg t)) (by positivity)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc ‖∑ m ∈ Finset.Icc 1 H',
        (u m * ((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))
          - ((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) * u m)‖
      ≤ ∑ m ∈ Finset.Icc 1 H',
          ‖u m * ((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))
            - ((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) * u m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 H', (|t| * (H' : ℝ) / (n : ℝ)) := Finset.sum_le_sum hterm
    _ = (H' : ℝ) * (|t| * (H' : ℝ) / (n : ℝ)) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

/-- Comparison form of `norm_windowTwistSum_sub_le`: the twisted window sum is bounded by
the untwisted one plus the Taylor error,

`‖∑_{m=1}^{H'} u(m)(n+m)^{i𝐭}‖ ≤ ‖∑_{m=1}^{H'} u(m)‖ + H'·(|𝐭|·H'/n)`. -/
theorem norm_windowTwistSum_le {u : ℕ → ℂ} (hu : ∀ k, ‖u k‖ ≤ 1)
    {n : ℕ} (hn : n ≠ 0) (H' : ℕ) (t : ℝ) :
    ‖∑ m ∈ Finset.Icc 1 H', u m * ((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))‖
      ≤ ‖∑ m ∈ Finset.Icc 1 H', u m‖ + H' * (|t| * H' / n) := by
  have hsub := norm_windowTwistSum_sub_le hu hn H' t
  have htri := norm_sub_norm_le
    (∑ m ∈ Finset.Icc 1 H', u m * ((n + m : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)))
    (((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) * ∑ m ∈ Finset.Icc 1 H', u m)
  have hone : ‖((n : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) * ∑ m ∈ Finset.Icc 1 H', u m‖
      = ‖∑ m ∈ Finset.Icc 1 H', u m‖ := by
    rw [norm_mul, norm_natCast_cpow_I_mul hn t, one_mul]
  rw [hone] at htri
  linarith

end MoltResearch
