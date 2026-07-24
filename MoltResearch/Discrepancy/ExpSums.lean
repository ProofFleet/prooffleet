import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Chebyshev

/-!
# Discrete exponential sums, layer 1: the Kusmin–Landau inequality (Track L of #3020)

The additive character `e(x) = exp(2πix)`, the nearest-integer distance
`nint`, and the first cancellation estimate for discrete exponential sums:

* `four_nint_le_norm_e_sub_one` — the geometric floor `4·‖x‖ ≤ ‖e(x) − 1‖`
  (Euler split `e(x) − 1 = e(x/2)·2i·sin(πx)` + Jordan's inequality);
* `inv_e_sub_one_eq` — the increment inverses live on a vertical line:
  `(e(δ) − 1)⁻¹ = −1/2 − (i/2)·cot(πδ)` on `(0,1)`;
* `cotpi_sub_cotpi` — the cotangent difference is a sine quotient
  (`cot(πa) − cot(πb) = sin(π(b−a))/(sin(πa)sin(πb))`), giving antitonicity
  with no calculus;
* `sum_diff_mul_eq` — the Abel rearrangement for difference-weighted sums;
* `kusmin_landau` — **the Kusmin–Landau inequality** with explicit constant
  `1`: if the phase increments `φ(n+1) − φ(n)` are monotone and confined to
  `[θ, 1−θ]`, then `‖∑_{M ≤ n ≤ N} e(φ(n))‖ ≤ 1/θ`, uniformly in the length.

Layer 2 (same campaign): the **discrete van der Corput second-derivative
test** `vdc2` — convex phases with second differences `≥ r` and total
increment variation `≤ D` satisfy
`‖∑ e(φ(n))‖ ≤ (D + 2)·(2θ/r + 1/θ + 1)` for every separation `θ`. The
proof is calculus-free: `sum_level_le` charges each unit of increment
growth one short bad prefix (the `delta_climb` through an integer's
`θ`-neighborhood) plus one Kusmin–Landau block (`kusmin_landau_shift` —
the character cannot see the integer part of the slope, `e_intCast`), and
`vdc2_aux` runs the level-budget recursion.

Layer 3 (same campaign): **Weyl differencing** (`weyl_differencing`, the
van der Corput A-process) — `‖∑ e(φ(n))‖² ≤ ((L+H)/H)·(L + 2∑_{g<H} ‖T_g‖)`
with `T_g` the difference-phase sums `∑ e(φ(m+g) − φ(m))`: the `H`-fold
shifted-window average, discrete Cauchy–Schwarz, the conjugate-pair
expansion, and the three-way diagonal/upper/lower split with the
off-diagonal fibering (each difference `g` occurs at most `H` times).
-/

namespace MoltResearch

namespace ExpSums

open Complex

/-- The normalized additive character `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * x * Complex.I)

/-- The distance to the nearest integer. -/
noncomputable def nint (x : ℝ) : ℝ := |x - round x|

theorem nint_nonneg (x : ℝ) : 0 ≤ nint x := abs_nonneg _

theorem nint_le_half (x : ℝ) : nint x ≤ 1 / 2 := abs_sub_round x

/-- The character has unit modulus. -/
theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  rw [e]
  rw [Complex.norm_exp]
  simp

/-- Euler split: `e(x) − 1 = e(x/2)·2i·sin(πx)`. -/
theorem e_sub_one (x : ℝ) :
    e x - 1 = Complex.exp (Real.pi * x * Complex.I)
      * (2 * Complex.I * Real.sin (Real.pi * x)) := by
  have h1 : (2 : ℂ) * Real.pi * x * Complex.I
      = Real.pi * x * Complex.I + Real.pi * x * Complex.I := by ring
  rw [e, h1, Complex.exp_add]
  have h2 : Complex.exp (Real.pi * x * Complex.I)
      = Real.cos (Real.pi * x) + Real.sin (Real.pi * x) * Complex.I := by
    have h3 := Complex.exp_mul_I (x := ((Real.pi * x : ℝ) : ℂ))
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    push_cast at h3 ⊢
    exact h3
  rw [h2]
  have hcs := Real.sin_sq_add_cos_sq (Real.pi * x)
  have hcast : ((Real.sin (Real.pi * x) : ℝ) : ℂ) ^ 2
      + ((Real.cos (Real.pi * x) : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hcs
  have hI : (Complex.I) ^ 2 = -1 := Complex.I_sq
  linear_combination hcast - ((Real.sin (Real.pi * x) : ℝ) : ℂ) ^ 2 * hI

/-- The modulus of the character increment: `‖e(x) − 1‖ = 2·|sin(πx)|`. -/
theorem norm_e_sub_one (x : ℝ) :
    ‖e x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  rw [e_sub_one, norm_mul]
  have h1 : ‖Complex.exp (Real.pi * x * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [h1, one_mul, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs]
  simp

/-- Integer shifts only flip the sign of `sin(π·)`. -/
theorem abs_sin_pi_sub_round (x : ℝ) :
    |Real.sin (Real.pi * (x - round x))| = |Real.sin (Real.pi * x)| := by
  have hexp : Real.pi * (x - round x) = Real.pi * x - (round x : ℝ) * Real.pi := by
    ring
  rw [hexp, Real.sin_sub]
  have hs0 : Real.sin ((round x : ℝ) * Real.pi) = 0 := by
    have := Real.sin_int_mul_pi (round x)
    exact_mod_cast this
  have hc1 : |Real.cos ((round x : ℝ) * Real.pi)| = 1 := by
    have h1 := Real.sin_sq_add_cos_sq ((round x : ℝ) * Real.pi)
    rw [hs0] at h1
    have h2 : Real.cos ((round x : ℝ) * Real.pi) ^ 2 = 1 := by nlinarith
    calc |Real.cos ((round x : ℝ) * Real.pi)|
        = Real.sqrt (Real.cos ((round x : ℝ) * Real.pi) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ = 1 := by rw [h2, Real.sqrt_one]
  rw [hs0, mul_zero, sub_zero, abs_mul, hc1, mul_one]

/-- Fold into the absolute value: `|sin(πu)| = sin(π·|u|)` for `|u| ≤ 1`. -/
theorem abs_sin_pi_eq_sin_abs {u : ℝ} (hu : |u| ≤ 1) :
    |Real.sin (Real.pi * u)| = Real.sin (Real.pi * |u|) := by
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h]
    refine abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_)
    · positivity
    · rw [abs_of_nonneg h] at hu
      nlinarith [Real.pi_pos]
  · rw [abs_of_neg h]
    have h1 : Real.pi * u = -(Real.pi * -u) := by ring
    rw [h1, Real.sin_neg, abs_neg]
    refine abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_)
    · nlinarith [Real.pi_pos]
    · rw [abs_of_neg h] at hu
      nlinarith [Real.pi_pos]

/-- **The geometric floor**: `4·‖x‖ ≤ ‖e(x) − 1‖`, with `‖x‖` the distance to
the nearest integer — the engine of the Kusmin–Landau inequality. -/
theorem four_nint_le_norm_e_sub_one (x : ℝ) :
    4 * nint x ≤ ‖e x - 1‖ := by
  have habs : |x - round x| ≤ 1 := le_trans (abs_sub_round x) (by norm_num)
  have h1 : ‖e x - 1‖ = 2 * Real.sin (Real.pi * nint x) := by
    rw [norm_e_sub_one, ← abs_sin_pi_sub_round, abs_sin_pi_eq_sin_abs habs,
      nint]
  rw [h1]
  have h2 : Real.pi * nint x ≤ Real.pi / 2 := by
    have := nint_le_half x
    nlinarith [Real.pi_pos]
  have h3 := Real.mul_le_sin (x := Real.pi * nint x)
    (by positivity [nint_nonneg x]) h2
  have h4 : 2 / Real.pi * (Real.pi * nint x) = 2 * nint x := by
    field_simp
  rw [h4] at h3
  linarith

/-- The character is additive. -/
theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  rw [e, e, e, ← Complex.exp_add]
  push_cast
  ring_nf

/-- Integers are in the kernel. -/
theorem e_intCast (k : ℤ) : e (k : ℝ) = 1 := by
  rw [e]
  have h1 : 2 * (Real.pi : ℂ) * ((k : ℝ) : ℂ) * Complex.I
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h1]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- Away from the integers, quantitatively: `θ ≤ x ≤ 1 − θ` forces
`θ ≤ ‖x‖`. -/
theorem le_nint {θ x : ℝ} (hθ : 0 < θ) (hlo : θ ≤ x) (hhi : x ≤ 1 - θ) :
    θ ≤ nint x := by
  rw [nint, round_eq]
  rcases lt_or_ge x (1 / 2) with h | h
  · have h0 : ⌊x + 1 / 2⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]
      constructor
      · linarith
      · norm_num
        linarith
    rw [h0]
    push_cast
    rw [sub_zero, abs_of_nonneg (by linarith)]
    exact hlo
  · have h1 : ⌊x + 1 / 2⌋ = 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor
      · linarith
      · linarith
    rw [h1]
    push_cast
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- The increment-inverse bound: `‖(e(x) − 1)⁻¹‖ ≤ 1/(4θ)` away from the
integers. -/
theorem norm_inv_e_sub_one_le {θ x : ℝ} (hθ : 0 < θ) (hn : θ ≤ nint x) :
    ‖(e x - 1)⁻¹‖ ≤ 1 / (4 * θ) := by
  rw [norm_inv, one_div]
  have h1 : 4 * θ ≤ ‖e x - 1‖ := by
    have h2 := four_nint_le_norm_e_sub_one x
    linarith
  have h2 : (0 : ℝ) < 4 * θ := by linarith
  exact inv_anti₀ h2 h1

/-- **The Abel rearrangement** for difference-weighted sums: pure algebra,
no analysis. -/
theorem sum_diff_mul_eq (A u : ℕ → ℂ) {M N : ℕ} (h : M ≤ N) :
    ∑ n ∈ Finset.Ico M (N + 1), (A (n + 1) - A n) * u n
      = A (N + 1) * u N - A M * u M
        + ∑ n ∈ Finset.Ico M N, A (n + 1) * (u n - u (n + 1)) := by
  induction N, h using Nat.le_induction with
  | base =>
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, Finset.Ico_self,
      Finset.sum_empty]
    ring
  | succ N hMN ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ih,
      Finset.sum_Ico_succ_top hMN]
    ring

/-- The half-period cotangent `cot(πx)`, defined bare — no `Real.cot` API
dependence. -/
noncomputable def cotpi (x : ℝ) : ℝ :=
  Real.cos (Real.pi * x) / Real.sin (Real.pi * x)

theorem sin_pi_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    0 < Real.sin (Real.pi * x) := by
  refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
  nlinarith [Real.pi_pos]

/-- The cotangent difference is a sine quotient: no calculus needed. -/
theorem cotpi_sub_cotpi {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    cotpi a - cotpi b
      = Real.sin (Real.pi * (b - a))
        / (Real.sin (Real.pi * a) * Real.sin (Real.pi * b)) := by
  have hsa := sin_pi_pos ha (lt_of_le_of_lt hab hb)
  have hsb := sin_pi_pos (lt_of_lt_of_le ha hab) hb
  rw [cotpi, cotpi, div_sub_div _ _ hsa.ne' hsb.ne',
    show Real.pi * (b - a) = Real.pi * b - Real.pi * a by ring,
    Real.sin_sub]
  ring_nf

/-- `cot(π·)` is antitone on `(0, 1)`. -/
theorem cotpi_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    cotpi b ≤ cotpi a := by
  rw [← sub_nonneg, cotpi_sub_cotpi ha hab hb]
  have hsa := sin_pi_pos ha (lt_of_le_of_lt hab hb)
  have hsb := sin_pi_pos (lt_of_lt_of_le ha hab) hb
  have hnum : 0 ≤ Real.sin (Real.pi * (b - a)) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) ?_
    nlinarith [Real.pi_pos]
  exact div_nonneg hnum (mul_pos hsa hsb).le

/-- The endpoint bound: `cot(πθ) ≤ 1/(2θ)` on `(0, 1/2]`. -/
theorem cotpi_le {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) :
    cotpi θ ≤ 1 / (2 * θ) := by
  have hs : (0 : ℝ) < Real.sin (Real.pi * θ) :=
    sin_pi_pos hθ (by linarith)
  have hjordan : 2 * θ ≤ Real.sin (Real.pi * θ) := by
    have h2 : Real.pi * θ ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
    have h3 := Real.mul_le_sin (x := Real.pi * θ) (by positivity) h2
    have h4 : 2 / Real.pi * (Real.pi * θ) = 2 * θ := by
      field_simp
    linarith [h4 ▸ h3]
  rw [cotpi, div_le_div_iff₀ hs (by linarith)]
  have hcos : Real.cos (Real.pi * θ) ≤ 1 := Real.cos_le_one _
  nlinarith [hjordan, hcos, hθ]

/-- The reflection `cot(π(1−θ)) = −cot(πθ)`. -/
theorem cotpi_one_sub (θ : ℝ) : cotpi (1 - θ) = -cotpi θ := by
  rw [cotpi, cotpi,
    show Real.pi * (1 - θ) = Real.pi - Real.pi * θ by ring,
    Real.sin_pi_sub, Real.cos_pi_sub]
  ring

/-- **The inverse identity**: `(e(δ) − 1)⁻¹ = −1/2 − (i/2)·cot(πδ)` on
`(0, 1)` — the increments' inverses live on a vertical line. -/
theorem inv_e_sub_one_eq {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    (e δ - 1)⁻¹
      = -(1 / 2 : ℂ) - Complex.I / 2 * (cotpi δ : ℝ) := by
  have hs := sin_pi_pos h0 h1
  have hexp : Complex.exp (Real.pi * δ * Complex.I)
      = Real.cos (Real.pi * δ) + Real.sin (Real.pi * δ) * Complex.I := by
    have h3 := Complex.exp_mul_I (x := ((Real.pi * δ : ℝ) : ℂ))
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    push_cast at h3 ⊢
    exact h3
  have hcs : ((Real.sin (Real.pi * δ) : ℝ) : ℂ) ^ 2
      + ((Real.cos (Real.pi * δ) : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ))
      (Real.sin_sq_add_cos_sq (Real.pi * δ))
  have hI : (Complex.I) ^ 2 = -1 := Complex.I_sq
  have hsC : ((Real.sin (Real.pi * δ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hs.ne'
  have key2 : (-((Real.sin (Real.pi * δ) : ℝ) : ℂ)
        - Complex.I * ((Real.cos (Real.pi * δ) : ℝ) : ℂ))
      * ((((Real.cos (Real.pi * δ) : ℝ) : ℂ)
          + ((Real.sin (Real.pi * δ) : ℝ) : ℂ) * Complex.I)
        * (2 * Complex.I * ((Real.sin (Real.pi * δ) : ℝ) : ℂ)))
      = 2 * ((Real.sin (Real.pi * δ) : ℝ) : ℂ) := by
    linear_combination (2 * ((Real.sin (Real.pi * δ) : ℝ) : ℂ)) * hcs
      + (-(2 * ((Real.sin (Real.pi * δ) : ℝ) : ℂ) ^ 2
            * ((Real.cos (Real.pi * δ) : ℝ) : ℂ) * Complex.I)
        - 2 * ((Real.sin (Real.pi * δ) : ℝ) : ℂ) ^ 3
        - 2 * ((Real.sin (Real.pi * δ) : ℝ) : ℂ)
          * ((Real.cos (Real.pi * δ) : ℝ) : ℂ) ^ 2) * hI
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [e_sub_one, hexp, cotpi, Complex.ofReal_div]
  have h2S : (2 * ((Real.sin (Real.pi * δ) : ℝ) : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero hsC
  have hfactor : (-(1 / 2 : ℂ)
        - Complex.I / 2 * (((Real.cos (Real.pi * δ) : ℝ) : ℂ)
          / ((Real.sin (Real.pi * δ) : ℝ) : ℂ)))
      = (-((Real.sin (Real.pi * δ) : ℝ) : ℂ)
          - Complex.I * ((Real.cos (Real.pi * δ) : ℝ) : ℂ))
        / (2 * ((Real.sin (Real.pi * δ) : ℝ) : ℂ)) := by
    field_simp
  rw [hfactor, div_mul_eq_mul_div, div_eq_iff h2S, one_mul]
  exact key2

/-- Telescoping over `Ico`. -/
theorem sum_Ico_sub_telescope (g : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (g n - g (n + 1)) = g a - g b := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    ring

/-- **The Kusmin–Landau inequality** (monotone form, explicit constant `1`):
if the phase increments are monotone and stay `θ`-separated from the
integers inside `[θ, 1 − θ]`, the exponential sum is bounded by `1/θ`,
uniformly in the length. -/
theorem kusmin_landau {φ : ℕ → ℝ} {θ : ℝ} {M N : ℕ}
    (hθ : 0 < θ) (hMN : M ≤ N)
    (hlo : ∀ n, M ≤ n → n ≤ N → θ ≤ φ (n + 1) - φ n)
    (hhi : ∀ n, M ≤ n → n ≤ N → φ (n + 1) - φ n ≤ 1 - θ)
    (hmono : ∀ n, M ≤ n → n < N →
      φ (n + 1) - φ n ≤ φ (n + 2) - φ (n + 1)) :
    ‖∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖ ≤ 1 / θ := by
  have hθ2 : θ ≤ 1 / 2 := by
    have h1 := hlo M le_rfl hMN
    have h2 := hhi M le_rfl hMN
    linarith
  -- the pointwise increment identity
  have hnz : ∀ n, M ≤ n → n ≤ N → e (φ (n + 1) - φ n) - 1 ≠ 0 := by
    intro n h1 h2 hc
    have h4 := four_nint_le_norm_e_sub_one (φ (n + 1) - φ n)
    have h5 := le_nint hθ (hlo n h1 h2) (hhi n h1 h2)
    rw [hc, norm_zero] at h4
    nlinarith
  have hsummand : ∀ n ∈ Finset.Ico M (N + 1),
      e (φ n) = (e (φ (n + 1)) - e (φ n))
        * (e (φ (n + 1) - φ n) - 1)⁻¹ := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hsplit : e (φ (n + 1)) = e (φ n) * e (φ (n + 1) - φ n) := by
      rw [← e_add]
      congr 1
      ring
    rw [hsplit,
      show e (φ n) * e (φ (n + 1) - φ n) - e (φ n)
        = e (φ n) * (e (φ (n + 1) - φ n) - 1) by ring,
      mul_assoc, mul_inv_cancel₀ (hnz n hn.1 (by omega)), mul_one]
  -- Abel rearrangement
  have habel := sum_diff_mul_eq (fun n => e (φ n))
    (fun n => (e (φ (n + 1) - φ n) - 1)⁻¹) hMN
  beta_reduce at habel
  rw [Finset.sum_congr rfl hsummand, habel]
  -- endpoint bounds
  have hendN : ‖(e (φ (N + 1) - φ N) - 1)⁻¹‖ ≤ 1 / (4 * θ) :=
    norm_inv_e_sub_one_le hθ (le_nint hθ (hlo N hMN le_rfl) (hhi N hMN le_rfl))
  have hendM : ‖(e (φ (M + 1) - φ M) - 1)⁻¹‖ ≤ 1 / (4 * θ) :=
    norm_inv_e_sub_one_le hθ (le_nint hθ (hlo M le_rfl hMN) (hhi M le_rfl hMN))
  -- the variation is a cotangent difference
  have hvar : ∀ n, M ≤ n → n < N →
      ‖(e (φ (n + 1) - φ n) - 1)⁻¹ - (e (φ (n + 2) - φ (n + 1)) - 1)⁻¹‖
        = 1 / 2 * (cotpi (φ (n + 1) - φ n)
            - cotpi (φ (n + 2) - φ (n + 1))) := by
    intro n h1 h2
    have hd1lo := hlo n h1 (by omega)
    have hd1hi := hhi n h1 (by omega)
    have hd2lo := hlo (n + 1) (by omega) (by omega)
    have hd2hi := hhi (n + 1) (by omega) (by omega)
    rw [inv_e_sub_one_eq (by linarith) (by linarith),
      inv_e_sub_one_eq (by linarith) (by linarith)]
    have heq : (-(1 / 2 : ℂ)
          - Complex.I / 2 * ((cotpi (φ (n + 1) - φ n) : ℝ) : ℂ))
        - (-(1 / 2 : ℂ)
          - Complex.I / 2 * ((cotpi (φ (n + 2) - φ (n + 1)) : ℝ) : ℂ))
        = Complex.I / 2 * (((cotpi (φ (n + 2) - φ (n + 1))
            - cotpi (φ (n + 1) - φ n) : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hmono' := hmono n h1 h2
    have hcot : cotpi (φ (n + 2) - φ (n + 1))
        ≤ cotpi (φ (n + 1) - φ n) :=
      cotpi_anti (by linarith) hmono' (by linarith)
    rw [abs_of_nonpos (by linarith), norm_div, Complex.norm_I]
    simp
  -- assemble
  have htel : ∑ n ∈ Finset.Ico M N,
      (1 / 2 * (cotpi (φ (n + 1) - φ n)
        - cotpi (φ (n + 2) - φ (n + 1))))
      = 1 / 2 * (cotpi (φ (M + 1) - φ M) - cotpi (φ (N + 1) - φ N)) := by
    rw [← Finset.mul_sum,
      sum_Ico_sub_telescope (fun n => cotpi (φ (n + 1) - φ n)) hMN]
  have hcotM : cotpi (φ (M + 1) - φ M) ≤ cotpi θ := by
    have h1 := hlo M le_rfl hMN
    have h2 := hhi M le_rfl hMN
    exact cotpi_anti hθ h1 (by linarith)
  have hcotN : -cotpi θ ≤ cotpi (φ (N + 1) - φ N) := by
    have h1 := hlo N hMN le_rfl
    have h2 := hhi N hMN le_rfl
    have h3 := cotpi_anti (by linarith : (0:ℝ) < φ (N + 1) - φ N) h2
      (by linarith : 1 - θ < 1)
    rw [cotpi_one_sub] at h3
    linarith
  have hcotθ := cotpi_le hθ hθ2
  calc ‖e (φ (N + 1)) * (e (φ (N + 1) - φ N) - 1)⁻¹
        - e (φ M) * (e (φ (M + 1) - φ M) - 1)⁻¹
        + ∑ n ∈ Finset.Ico M N, e (φ (n + 1))
            * ((e (φ (n + 1) - φ n) - 1)⁻¹
              - (e (φ (n + 2) - φ (n + 1)) - 1)⁻¹)‖
      ≤ ‖e (φ (N + 1)) * (e (φ (N + 1) - φ N) - 1)⁻¹
          - e (φ M) * (e (φ (M + 1) - φ M) - 1)⁻¹‖
        + ‖∑ n ∈ Finset.Ico M N, e (φ (n + 1))
            * ((e (φ (n + 1) - φ n) - 1)⁻¹
              - (e (φ (n + 2) - φ (n + 1)) - 1)⁻¹)‖ := norm_add_le _ _
    _ ≤ (‖e (φ (N + 1)) * (e (φ (N + 1) - φ N) - 1)⁻¹‖
          + ‖e (φ M) * (e (φ (M + 1) - φ M) - 1)⁻¹‖)
        + ∑ n ∈ Finset.Ico M N, ‖e (φ (n + 1))
            * ((e (φ (n + 1) - φ n) - 1)⁻¹
              - (e (φ (n + 2) - φ (n + 1)) - 1)⁻¹)‖ :=
        add_le_add (norm_sub_le _ _) (norm_sum_le _ _)
    _ = (‖(e (φ (N + 1) - φ N) - 1)⁻¹‖ + ‖(e (φ (M + 1) - φ M) - 1)⁻¹‖)
        + ∑ n ∈ Finset.Ico M N, ‖(e (φ (n + 1) - φ n) - 1)⁻¹
              - (e (φ (n + 2) - φ (n + 1)) - 1)⁻¹‖ := by
        congr 1
        · rw [norm_mul, norm_mul, norm_e, norm_e, one_mul, one_mul]
        · exact Finset.sum_congr rfl fun n _ => by
            rw [norm_mul, norm_e, one_mul]
    _ ≤ (1 / (4 * θ) + 1 / (4 * θ))
        + (1 / 2 * (cotpi (φ (M + 1) - φ M) - cotpi (φ (N + 1) - φ N))) := by
        refine add_le_add (add_le_add hendN hendM) ?_
        rw [← htel]
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_Ico] at hn
        exact le_of_eq (hvar n hn.1 hn.2)
    _ ≤ 1 / (4 * θ) + 1 / (4 * θ) + cotpi θ := by
        have h1 : 1 / 2 * (cotpi (φ (M + 1) - φ M)
            - cotpi (φ (N + 1) - φ N)) ≤ cotpi θ := by
          linarith
        linarith
    _ ≤ 1 / θ := by
        have h2 : cotpi θ ≤ 1 / (2 * θ) := hcotθ
        have h3 : 1 / (4 * θ) + 1 / (4 * θ) = 1 / (2 * θ) := by
          field_simp
          ring
        have h4 : 1 / (2 * θ) + 1 / (2 * θ) = 1 / θ := by
          field_simp
          ring
        linarith

/-- Increment monotonicity, transitively (`d`-form: no ℕ-subtraction). -/
theorem delta_mono {φ : ℕ → ℝ} {M N : ℕ}
    (hmono : ∀ n, M ≤ n → n < N →
      φ (n + 1) - φ n ≤ φ (n + 2) - φ (n + 1))
    {i d : ℕ} (hMi : M ≤ i) (hdN : i + d ≤ N) :
    φ (i + 1) - φ i ≤ φ (i + d + 1) - φ (i + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := hmono (i + d) (by omega) (by omega)
    have h2 := ih (by omega)
    have h3 : i + (d + 1) = i + d + 1 := by omega
    rw [h3]
    calc φ (i + 1) - φ i ≤ φ (i + d + 1) - φ (i + d) := h2
      _ ≤ φ (i + d + 1 + 1) - φ (i + d + 1) := by
          have h4 : i + d + 2 = i + d + 1 + 1 := by omega
          rw [← h4]
          exact h1

/-- The second-difference climb (`d`-form): increments rise linearly. -/
theorem delta_climb {φ : ℕ → ℝ} {r : ℝ} {M N : ℕ}
    (hsec : ∀ n, M ≤ n → n < N →
      r ≤ (φ (n + 2) - φ (n + 1)) - (φ (n + 1) - φ n))
    {i d : ℕ} (hMi : M ≤ i) (hdN : i + d ≤ N) :
    (d : ℝ) * r ≤ (φ (i + d + 1) - φ (i + d)) - (φ (i + 1) - φ i) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := hsec (i + d) (by omega) (by omega)
    have h2 := ih (by omega)
    have h3 : i + (d + 1) = i + d + 1 := by omega
    rw [h3]
    have h4 : i + d + 2 = i + d + 1 + 1 := by omega
    rw [h4] at h1
    push_cast
    linarith

/-- Kusmin–Landau after an integer shift: the character cannot see `k·n`. -/
theorem kusmin_landau_shift {φ : ℕ → ℝ} {θ : ℝ} {M N : ℕ} (k : ℤ)
    (hθ : 0 < θ) (hMN : M ≤ N)
    (hlo : ∀ n, M ≤ n → n ≤ N → (k : ℝ) + θ ≤ φ (n + 1) - φ n)
    (hhi : ∀ n, M ≤ n → n ≤ N → φ (n + 1) - φ n ≤ (k : ℝ) + 1 - θ)
    (hmono : ∀ n, M ≤ n → n < N →
      φ (n + 1) - φ n ≤ φ (n + 2) - φ (n + 1)) :
    ‖∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖ ≤ 1 / θ := by
  have hcongr : ∀ n ∈ Finset.Ico M (N + 1),
      e (φ n) = e (φ n - (k : ℝ) * n) := by
    intro n _
    rw [show φ n - (k : ℝ) * n = φ n + ((-(k * n) : ℤ) : ℝ) by
        push_cast
        ring,
      e_add, e_intCast, mul_one]
  rw [Finset.sum_congr rfl hcongr]
  refine kusmin_landau hθ hMN ?_ ?_ ?_
  · intro n h1 h2
    show θ ≤ (φ (n + 1) - (k : ℝ) * ((n + 1 : ℕ) : ℝ)) - (φ n - (k : ℝ) * n)
    have hb : (φ (n + 1) - (k : ℝ) * ((n + 1 : ℕ) : ℝ)) - (φ n - (k : ℝ) * n)
        = φ (n + 1) - φ n - (k : ℝ) := by
      push_cast
      ring
    have h3 := hlo n h1 h2
    linarith [hb]
  · intro n h1 h2
    show (φ (n + 1) - (k : ℝ) * ((n + 1 : ℕ) : ℝ)) - (φ n - (k : ℝ) * n)
      ≤ 1 - θ
    have hb : (φ (n + 1) - (k : ℝ) * ((n + 1 : ℕ) : ℝ)) - (φ n - (k : ℝ) * n)
        = φ (n + 1) - φ n - (k : ℝ) := by
      push_cast
      ring
    have h3 := hhi n h1 h2
    linarith [hb]
  · intro n h1 h2
    show (φ (n + 1) - (k : ℝ) * ((n + 1 : ℕ) : ℝ)) - (φ n - (k : ℝ) * n)
      ≤ (φ (n + 2) - (k : ℝ) * ((n + 2 : ℕ) : ℝ))
        - (φ (n + 1) - (k : ℝ) * ((n + 1 : ℕ) : ℝ))
    have hb1 : (φ (n + 1) - (k : ℝ) * ((n + 1 : ℕ) : ℝ))
          - (φ n - (k : ℝ) * n)
        = φ (n + 1) - φ n - (k : ℝ) := by
      push_cast
      ring
    have hb2 : (φ (n + 2) - (k : ℝ) * ((n + 2 : ℕ) : ℝ))
          - (φ (n + 1) - (k : ℝ) * ((n + 1 : ℕ) : ℝ))
        = φ (n + 2) - φ (n + 1) - (k : ℝ) := by
      push_cast
      ring
    have h3 := hmono n h1 h2
    linarith [hb1, hb2]

/-- **The single-level bound**: increments confined to `[k − θ, k + 1 − θ]`
cost one short bad prefix (the climb through the integer's `θ`-neighborhood)
plus one Kusmin–Landau block. -/
theorem sum_level_le {φ : ℕ → ℝ} {θ r : ℝ} {M N : ℕ} (k : ℤ)
    (hθ : 0 < θ) (hr : 0 < r) (hMN : M ≤ N)
    (hlo : (k : ℝ) - θ ≤ φ (M + 1) - φ M)
    (hhi : ∀ n, M ≤ n → n ≤ N → φ (n + 1) - φ n ≤ (k : ℝ) + 1 - θ)
    (hmono : ∀ n, M ≤ n → n < N →
      φ (n + 1) - φ n ≤ φ (n + 2) - φ (n + 1))
    (hsec : ∀ n, M ≤ n → n < N →
      r ≤ (φ (n + 2) - φ (n + 1)) - (φ (n + 1) - φ n)) :
    ‖∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖
      ≤ (2 * θ / r + 1) + 1 / θ := by
  classical
  have hex : ∃ n, N + 1 ≤ n
      ∨ (M ≤ n ∧ n ≤ N ∧ (k : ℝ) + θ ≤ φ (n + 1) - φ n) :=
    ⟨N + 1, Or.inl le_rfl⟩
  set P := Nat.find hex with hPdef
  have hQP := Nat.find_spec hex
  have hPle : P ≤ N + 1 := Nat.find_le (Or.inl le_rfl)
  have hMP : M ≤ P := by
    rcases hQP with h | h
    · omega
    · exact h.1
  rw [← Finset.sum_Ico_consecutive _ hMP hPle]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · -- the bad prefix: at most 2θ/r + 1 terms, bounded trivially
    refine le_trans (norm_sum_le _ _) ?_
    have h1 : ∑ n ∈ Finset.Ico M P, ‖e (φ n)‖ = ((P - M : ℕ) : ℝ) := by
      rw [Finset.sum_congr rfl (fun n _ => norm_e (φ n)),
        Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico]
    rw [h1]
    rcases Nat.eq_or_lt_of_le hMP with hPM | hPM
    · rw [← hPM]
      simp
      positivity
    · -- P ≥ M + 1: look at the last prefix index P − 1 = M + d
      obtain ⟨d, hd⟩ : ∃ d, P - 1 = M + d := ⟨P - 1 - M, by omega⟩
      have hdN : M + d ≤ N := by omega
      have hnotQ : ¬ (N + 1 ≤ P - 1
          ∨ (M ≤ P - 1 ∧ P - 1 ≤ N
            ∧ (k : ℝ) + θ ≤ φ (P - 1 + 1) - φ (P - 1))) := by
        rw [hPdef]
        exact Nat.find_min hex (by omega)
      push_neg at hnotQ
      have hbad : φ (P - 1 + 1) - φ (P - 1) < (k : ℝ) + θ := by
        have := hnotQ.2 (by omega) (by omega)
        linarith
      have hclimb := delta_climb hsec (i := M) (d := d) le_rfl hdN
      rw [← hd] at hclimb
      have hcount : ((d : ℝ)) * r < 2 * θ := by
        have h2 : φ (P - 1 + 1) - φ (P - 1) - (φ (M + 1) - φ M)
            < ((k : ℝ) + θ) - ((k : ℝ) - θ) := by
          linarith
        linarith
      have hdle : (d : ℝ) < 2 * θ / r := by
        rw [lt_div_iff₀ hr]
        linarith
      have hcast : ((P - M : ℕ) : ℝ) = (d : ℝ) + 1 := by
        have : P - M = d + 1 := by omega
        rw [this]
        push_cast
        ring
      rw [hcast]
      linarith
  · -- the good suffix: Kusmin–Landau at level k
    rcases Nat.eq_or_lt_of_le hPle with hPN | hPN
    · rw [hPN, Finset.Ico_self, Finset.sum_empty, norm_zero]
      positivity
    · have hQ : M ≤ P ∧ P ≤ N ∧ (k : ℝ) + θ ≤ φ (P + 1) - φ P := by
        rcases hQP with h | h
        · omega
        · exact h
      refine kusmin_landau_shift k hθ hQ.2.1 ?_ ?_ ?_
      · intro n h1 h2
        obtain ⟨d, hd⟩ : ∃ d, n = P + d := ⟨n - P, by omega⟩
        have h3 := delta_mono hmono (i := P) (d := d) hMP (by omega)
        rw [← hd] at h3
        have h4 := hQ.2.2
        linarith
      · intro n h1 h2
        exact hhi n (by omega) h2
      · intro n h1 h2
        exact hmono n (by omega) h2

/-- The level-budget recursion behind the second-derivative test: each unit
of increment-growth costs one single-level block. -/
theorem vdc2_aux (φ : ℕ → ℝ) {θ r : ℝ} (hθ : 0 < θ) (hr : 0 < r) :
    ∀ d : ℕ, ∀ M N : ℕ, M ≤ N →
      (∀ n, M ≤ n → n < N →
        φ (n + 1) - φ n ≤ φ (n + 2) - φ (n + 1)) →
      (∀ n, M ≤ n → n < N →
        r ≤ (φ (n + 2) - φ (n + 1)) - (φ (n + 1) - φ n)) →
      ⌊(φ (N + 1) - φ N) + θ⌋ ≤ ⌊(φ (M + 1) - φ M) + θ⌋ + d →
      ‖∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖
        ≤ (d + 1) * ((2 * θ / r + 1) + 1 / θ) := by
  intro d
  induction d with
  | zero =>
    intro M N hMN hmono hsec hbudget
    have hB : ‖∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖
        ≤ (2 * θ / r + 1) + 1 / θ := by
      refine sum_level_le ⌊(φ (M + 1) - φ M) + θ⌋ hθ hr hMN ?_ ?_ hmono hsec
      · have h1 := Int.floor_le ((φ (M + 1) - φ M) + θ)
        linarith
      · intro n h1 h2
        have h3 : φ (n + 1) - φ n ≤ φ (N + 1) - φ N := by
          obtain ⟨dd, hdd⟩ : ∃ dd, N = n + dd := ⟨N - n, by omega⟩
          have h4 := delta_mono hmono (i := n) (d := dd) h1 (by omega)
          rw [← hdd] at h4
          exact h4
        have h5 := Int.lt_floor_add_one ((φ (N + 1) - φ N) + θ)
        have h6 : (⌊(φ (N + 1) - φ N) + θ⌋ : ℝ)
            ≤ (⌊(φ (M + 1) - φ M) + θ⌋ : ℝ) := by
          have h7 : ⌊(φ (N + 1) - φ N) + θ⌋
              ≤ ⌊(φ (M + 1) - φ M) + θ⌋ := by omega
          exact_mod_cast h7
        push_cast at h5
        linarith
    have hpos : (0 : ℝ) ≤ (2 * θ / r + 1) + 1 / θ := by positivity
    calc ‖∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖
        ≤ (2 * θ / r + 1) + 1 / θ := hB
      _ ≤ ((0 : ℕ) + 1) * ((2 * θ / r + 1) + 1 / θ) := by
          push_cast
          linarith
  | succ d ih =>
    intro M N hMN hmono hsec hbudget
    classical
    have hex : ∃ n, N + 1 ≤ n
        ∨ (M ≤ n ∧ n ≤ N
          ∧ (⌊(φ (M + 1) - φ M) + θ⌋ : ℝ) + 1 - θ ≤ φ (n + 1) - φ n) :=
      ⟨N + 1, Or.inl le_rfl⟩
    set P := Nat.find hex with hPdef
    have hQP := Nat.find_spec hex
    have hPle : P ≤ N + 1 := Nat.find_le (Or.inl le_rfl)
    have hδM : φ (M + 1) - φ M
        < (⌊(φ (M + 1) - φ M) + θ⌋ : ℝ) + 1 - θ := by
      have h1 := Int.lt_floor_add_one ((φ (M + 1) - φ M) + θ)
      push_cast at h1
      linarith
    have hMP : M + 1 ≤ P := by
      rcases Nat.lt_or_ge M P with h | h
      · omega
      · exfalso
        have hnQ := Nat.find_spec hex
        rw [← hPdef] at hnQ
        rcases hnQ with h1 | h1
        · omega
        · have h2 : P = M ∨ P < M := by omega
          rcases h2 with h2 | h2
          · rw [h2] at h1
            linarith [h1.2.2]
          · omega
    rcases Nat.eq_or_lt_of_le hPle with hPN | hPN
    · -- no crossing: single level on the whole range
      have hB : ‖∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖
          ≤ (2 * θ / r + 1) + 1 / θ := by
        refine sum_level_le ⌊(φ (M + 1) - φ M) + θ⌋ hθ hr hMN ?_ ?_
          hmono hsec
        · have h1 := Int.floor_le ((φ (M + 1) - φ M) + θ)
          linarith
        · intro n h1 h2
          have h3 : ¬ (N + 1 ≤ n
              ∨ (M ≤ n ∧ n ≤ N
                ∧ (⌊(φ (M + 1) - φ M) + θ⌋ : ℝ) + 1 - θ
                  ≤ φ (n + 1) - φ n)) := by
            rw [hPdef] at hPN
            exact Nat.find_min hex (by omega)
          push_neg at h3
          have h4 := h3.2 h1 h2
          linarith
      have hpos : (0 : ℝ) ≤ (2 * θ / r + 1) + 1 / θ := by positivity
      calc ‖∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖
          ≤ (2 * θ / r + 1) + 1 / θ := hB
        _ ≤ ((d : ℝ) + 1 + 1) * ((2 * θ / r + 1) + 1 / θ) := by
            nlinarith
        _ = (((d + 1 : ℕ) : ℝ) + 1) * ((2 * θ / r + 1) + 1 / θ) := by
            push_cast
            ring
    · -- crossing at P ≤ N: split, single level left, recurse right
      have hPN' : P ≤ N := by omega
      have hQ : M ≤ P ∧ P ≤ N
          ∧ (⌊(φ (M + 1) - φ M) + θ⌋ : ℝ) + 1 - θ ≤ φ (P + 1) - φ P := by
        rcases hQP with h | h
        · omega
        · exact h
      rw [← Finset.sum_Ico_consecutive _ (by omega : M ≤ P)
        (by omega : P ≤ N + 1)]
      refine le_trans (norm_add_le _ _) ?_
      have hleft : ‖∑ n ∈ Finset.Ico M P, e (φ n)‖
          ≤ (2 * θ / r + 1) + 1 / θ := by
        have hP1 : P - 1 + 1 = P := by omega
        rw [← hP1]
        refine sum_level_le ⌊(φ (M + 1) - φ M) + θ⌋ hθ hr
          (by omega : M ≤ P - 1) ?_ ?_
          (fun n h1 h2 => hmono n h1 (by omega))
          (fun n h1 h2 => hsec n h1 (by omega))
        · have h1 := Int.floor_le ((φ (M + 1) - φ M) + θ)
          linarith
        · intro n h1 h2
          have h3 : ¬ (N + 1 ≤ n
              ∨ (M ≤ n ∧ n ≤ N
                ∧ (⌊(φ (M + 1) - φ M) + θ⌋ : ℝ) + 1 - θ
                  ≤ φ (n + 1) - φ n)) := by
            rw [hPdef] at hPN'
            exact Nat.find_min hex (by omega)
          push_neg at h3
          have h4 := h3.2 h1 (by omega)
          linarith
      have hright : ‖∑ n ∈ Finset.Ico P (N + 1), e (φ n)‖
          ≤ ((d : ℝ) + 1) * ((2 * θ / r + 1) + 1 / θ) := by
        have hbud' : ⌊(φ (N + 1) - φ N) + θ⌋
            ≤ ⌊(φ (P + 1) - φ P) + θ⌋ + d := by
          have h1 : (⌊(φ (M + 1) - φ M) + θ⌋ + 1 : ℤ)
              ≤ ⌊(φ (P + 1) - φ P) + θ⌋ := by
            rw [Int.le_floor]
            push_cast
            linarith [hQ.2.2]
          omega
        have h2 := ih P N hPN'
          (fun n h1 h2 => hmono n (by omega) h2)
          (fun n h1 h2 => hsec n (by omega) h2)
          hbud'
        calc ‖∑ n ∈ Finset.Ico P (N + 1), e (φ n)‖
            ≤ ((d : ℕ) + 1) * ((2 * θ / r + 1) + 1 / θ) := h2
          _ = ((d : ℝ) + 1) * ((2 * θ / r + 1) + 1 / θ) := by
              push_cast
              ring
      calc ‖∑ n ∈ Finset.Ico M P, e (φ n)‖
            + ‖∑ n ∈ Finset.Ico P (N + 1), e (φ n)‖
          ≤ ((2 * θ / r + 1) + 1 / θ)
            + ((d : ℝ) + 1) * ((2 * θ / r + 1) + 1 / θ) :=
            add_le_add hleft hright
        _ = (((d + 1 : ℕ) : ℝ) + 1) * ((2 * θ / r + 1) + 1 / θ) := by
            push_cast
            ring

/-- **The discrete van der Corput second-derivative test**: convex phases
with second differences at least `r` and total increment variation at most
`D` have exponential sums bounded by `(D + 2)·(2θ/r + 1/θ + 1)`, for every
separation parameter `θ`. -/
theorem vdc2 {φ : ℕ → ℝ} {θ r D : ℝ} {M N : ℕ}
    (hθ : 0 < θ) (hr : 0 < r) (hMN : M ≤ N)
    (hmono : ∀ n, M ≤ n → n < N →
      φ (n + 1) - φ n ≤ φ (n + 2) - φ (n + 1))
    (hsec : ∀ n, M ≤ n → n < N →
      r ≤ (φ (n + 2) - φ (n + 1)) - (φ (n + 1) - φ n))
    (hD : (φ (N + 1) - φ N) - (φ (M + 1) - φ M) ≤ D) :
    ‖∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖
      ≤ (D + 2) * ((2 * θ / r + 1) + 1 / θ) := by
  have hD0 : (0 : ℝ) ≤ D := by
    obtain ⟨dd, hdd⟩ : ∃ dd, N = M + dd := ⟨N - M, by omega⟩
    have h1 := delta_mono hmono (i := M) (d := dd) le_rfl (by omega)
    rw [← hdd] at h1
    linarith
  set d : ℕ := (⌊(φ (N + 1) - φ N) + θ⌋
    - ⌊(φ (M + 1) - φ M) + θ⌋).toNat with hd
  have hbudget : ⌊(φ (N + 1) - φ N) + θ⌋
      ≤ ⌊(φ (M + 1) - φ M) + θ⌋ + d := by
    rw [hd]
    omega
  have h1 := vdc2_aux φ hθ hr d M N hMN hmono hsec hbudget
  have hdD : ((d : ℕ) : ℝ) ≤ D + 1 := by
    have h2 : (⌊(φ (N + 1) - φ N) + θ⌋ : ℝ)
        ≤ (φ (N + 1) - φ N) + θ := Int.floor_le _
    have h3 : (φ (M + 1) - φ M) + θ - 1
        < (⌊(φ (M + 1) - φ M) + θ⌋ : ℝ) := by
      have := Int.lt_floor_add_one ((φ (M + 1) - φ M) + θ)
      linarith
    rcases le_or_gt (⌊(φ (N + 1) - φ N) + θ⌋)
        (⌊(φ (M + 1) - φ M) + θ⌋) with h4 | h4
    · have h5 : d = 0 := by
        rw [hd]
        omega
      rw [h5]
      push_cast
      linarith
    · have h6 : (0 : ℤ) ≤ ⌊(φ (N + 1) - φ N) + θ⌋
          - ⌊(φ (M + 1) - φ M) + θ⌋ := by omega
      have h5 : ((d : ℕ) : ℝ) = (⌊(φ (N + 1) - φ N) + θ⌋ : ℝ)
          - (⌊(φ (M + 1) - φ M) + θ⌋ : ℝ) := by
        rw [hd]
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ))
          (Int.toNat_of_nonneg h6)
      rw [h5]
      linarith
  have hpos : (0 : ℝ) ≤ (2 * θ / r + 1) + 1 / θ := by positivity
  calc ‖∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖
      ≤ ((d : ℕ) + 1) * ((2 * θ / r + 1) + 1 / θ) := h1
    _ ≤ (D + 2) * ((2 * θ / r + 1) + 1 / θ) := by
        have h7 : ((d : ℕ) : ℝ) + 1 ≤ D + 2 := by linarith
        nlinarith

/-- Conjugation negates the phase. -/
theorem e_conj (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  rw [e, e, ← Complex.exp_conj]
  have h0 : (2 : ℂ) * (Real.pi : ℂ) * (x : ℂ) * Complex.I
      = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h0, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- Products against conjugates subtract phases. -/
theorem e_mul_conj (x y : ℝ) :
    e x * (starRingEnd ℂ) (e y) = e (x - y) := by
  rw [e_conj, ← e_add]
  congr 1

/-- The shift identity: summing a shifted phase over a shifted window. -/
theorem sum_shift (φ : ℕ → ℝ) {M N : ℕ} (h : ℕ) (hhM : h ≤ M)
    (hMN : M ≤ N + 1) :
    ∑ n ∈ Finset.Ico M (N + 1), e (φ n)
      = ∑ n ∈ Finset.Ico (M - h) (N + 1 - h), e (φ (n + h)) := by
  have hmap : Finset.Ico M (N + 1)
      = (Finset.Ico (M - h) (N + 1 - h)).map
          (addRightEmbedding h) := by
    rw [Finset.map_add_right_Ico]
    congr 1 <;> omega
  rw [hmap, Finset.sum_map]
  simp only [addRightEmbedding_apply]

/-- Discrete Cauchy–Schwarz for complex sums. -/
theorem norm_sum_sq_le_card_mul (W : Finset ℕ) (f : ℕ → ℂ) :
    ‖∑ n ∈ W, f n‖ ^ 2 ≤ (W.card : ℝ) * ∑ n ∈ W, ‖f n‖ ^ 2 := by
  have h1 : ‖∑ n ∈ W, f n‖ ≤ ∑ n ∈ W, ‖f n‖ := norm_sum_le _ _
  have h2 : (∑ n ∈ W, ‖f n‖) ^ 2 ≤ (W.card : ℝ) * ∑ n ∈ W, ‖f n‖ ^ 2 := by
    exact_mod_cast sq_sum_le_card_mul_sum_sq (s := W) (f := fun n => ‖f n‖)
  calc ‖∑ n ∈ W, f n‖ ^ 2
      ≤ (∑ n ∈ W, ‖f n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (W.card : ℝ) * ∑ n ∈ W, ‖f n‖ ^ 2 := h2

/-- Expanding the square of an inner sum into conjugate pairs. -/
theorem sum_norm_sq_expand (W K : Finset ℕ) (c : ℕ → ℕ → ℂ) :
    ∑ n ∈ W, ‖∑ h ∈ K, c n h‖ ^ 2
      ≤ ∑ p ∈ K ×ˢ K, ‖∑ n ∈ W, c n p.1 * (starRingEnd ℂ) (c n p.2)‖ := by
  have hsq : ∀ z : ℂ, (‖z‖ : ℝ) ^ 2 = (z * (starRingEnd ℂ) z).re := by
    intro z
    rw [Complex.mul_conj]
    simp [Complex.sq_norm]
  have hexp : ∀ n, (∑ h ∈ K, c n h) * (starRingEnd ℂ) (∑ h ∈ K, c n h)
      = ∑ p ∈ K ×ˢ K, c n p.1 * (starRingEnd ℂ) (c n p.2) := by
    intro n
    rw [map_sum, Finset.sum_mul_sum, ← Finset.sum_product']
  calc ∑ n ∈ W, ‖∑ h ∈ K, c n h‖ ^ 2
      = ∑ n ∈ W, ((∑ h ∈ K, c n h)
          * (starRingEnd ℂ) (∑ h ∈ K, c n h)).re := by
        refine Finset.sum_congr rfl fun n _ => hsq _
    _ = (∑ n ∈ W, ∑ p ∈ K ×ˢ K,
          c n p.1 * (starRingEnd ℂ) (c n p.2)).re := by
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hexp]
    _ = (∑ p ∈ K ×ˢ K, ∑ n ∈ W,
          c n p.1 * (starRingEnd ℂ) (c n p.2)).re := by
        rw [Finset.sum_comm]
    _ ≤ ‖∑ p ∈ K ×ˢ K, ∑ n ∈ W,
          c n p.1 * (starRingEnd ℂ) (c n p.2)‖ := Complex.re_le_norm _
    _ ≤ ∑ p ∈ K ×ˢ K, ‖∑ n ∈ W,
          c n p.1 * (starRingEnd ℂ) (c n p.2)‖ := norm_sum_le _ _

/-- The off-diagonal fibering: pairs at difference `g` number at most `H`. -/
theorem sum_offdiag_le {H : ℕ} (F : ℕ → ℝ) (hF : ∀ g, 0 ≤ F g) :
    ∑ p ∈ ((Finset.range H) ×ˢ (Finset.range H)).filter
        (fun p => p.2 < p.1), F (p.1 - p.2)
      ≤ (H : ℝ) * ∑ g ∈ Finset.Ico 1 H, F g := by
  classical
  have hmaps : ∀ p ∈ ((Finset.range H) ×ˢ (Finset.range H)).filter
      (fun p => p.2 < p.1), p.1 - p.2 ∈ Finset.Ico 1 H := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_range] at hp
    rw [Finset.mem_Ico]
    omega
  have hfib := Finset.sum_fiberwise_of_maps_to
    (g := fun p : ℕ × ℕ => p.1 - p.2) (t := Finset.Ico 1 H) hmaps
    (fun p : ℕ × ℕ => F (p.1 - p.2))
  rw [← hfib]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun g hg => ?_
  have hcong : ∀ p ∈ (((Finset.range H) ×ˢ (Finset.range H)).filter
      (fun p => p.2 < p.1)).filter (fun p => p.1 - p.2 = g),
      F (p.1 - p.2) = F g := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [hp.2]
  rw [Finset.sum_congr rfl hcong, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hF g)
  have hcard : ((((Finset.range H) ×ˢ (Finset.range H)).filter
      (fun p => p.2 < p.1)).filter (fun p => p.1 - p.2 = g)).card
      ≤ H := by
    have hinj : Set.MapsTo Prod.snd
        (↑((((Finset.range H) ×ˢ (Finset.range H)).filter
          (fun p => p.2 < p.1)).filter (fun p => p.1 - p.2 = g))
          : Set (ℕ × ℕ))
        ((Finset.range H : Finset ℕ) : Set ℕ) := by
      intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter,
        Finset.mem_product] at hp
      rw [Finset.mem_coe]
      exact hp.1.1.2
    have h2 := Finset.card_le_card_of_injOn Prod.snd hinj ?_
    · rw [Finset.card_range] at h2
      exact h2
    · intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter] at hp hq
      have h3 := hp.2
      have h4 := hq.2
      have h5 := hp.1.2
      have h6 := hq.1.2
      refine Prod.ext ?_ hpq
      omega
  exact_mod_cast hcard

/-- The trivial character value. -/
theorem e_zero : e 0 = 1 := by
  rw [e]
  norm_num

/-- The off-diagonal pair sum collapses to a difference-phase sum. -/
theorem weyl_offdiag {φ : ℕ → ℝ} {M N H : ℕ} (hHM : H ≤ M) (hMN : M ≤ N)
    {h h' : ℕ} (hh' : h' < h) (hhH : h < H) :
    ∑ n ∈ Finset.Ico (M - H + 1) (N + 1),
      (if n ∈ Finset.Ico (M - h) (N + 1 - h) then e (φ (n + h)) else 0)
        * (starRingEnd ℂ) (if n ∈ Finset.Ico (M - h') (N + 1 - h')
            then e (φ (n + h')) else 0)
      = ∑ m ∈ Finset.Ico M (N + 1 - (h - h')),
          e (φ (m + (h - h')) - φ m) := by
  classical
  have h1 : ∀ n, (if n ∈ Finset.Ico (M - h) (N + 1 - h)
        then e (φ (n + h)) else 0)
      * (starRingEnd ℂ) (if n ∈ Finset.Ico (M - h') (N + 1 - h')
          then e (φ (n + h')) else 0)
      = if n ∈ Finset.Ico (M - h') (N + 1 - h)
          then e (φ (n + h) - φ (n + h')) else 0 := by
    intro n
    by_cases hn1 : n ∈ Finset.Ico (M - h) (N + 1 - h)
    · by_cases hn2 : n ∈ Finset.Ico (M - h') (N + 1 - h')
      · rw [if_pos hn1, if_pos hn2, e_mul_conj, if_pos ?_]
        rw [Finset.mem_Ico] at hn1 hn2 ⊢
        omega
      · rw [if_pos hn1, if_neg hn2, map_zero, mul_zero, if_neg ?_]
        rw [Finset.mem_Ico] at hn1 hn2 ⊢
        omega
    · rw [if_neg hn1, zero_mul, if_neg ?_]
      rw [Finset.mem_Ico] at hn1 ⊢
      omega
  rw [Finset.sum_congr rfl (fun n _ => h1 n), Finset.sum_ite_mem]
  have h2 : Finset.Ico (M - H + 1) (N + 1)
      ∩ Finset.Ico (M - h') (N + 1 - h)
      = Finset.Ico (M - h') (N + 1 - h) := by
    rw [Finset.inter_eq_right]
    intro n hn
    rw [Finset.mem_Ico] at hn ⊢
    omega
  rw [h2]
  have h4 : ∑ m ∈ Finset.Ico M (N + 1 - (h - h')),
      e (φ (m + (h - h')) - φ m)
      = ∑ n ∈ Finset.Ico (M - h') (N + 1 - h),
          e (φ (n + h) - φ (n + h')) := by
    have h5 : Finset.Ico M (N + 1 - (h - h'))
        = (Finset.Ico (M - h') (N + 1 - h)).map
            (addRightEmbedding h') := by
      rw [Finset.map_add_right_Ico]
      congr 1 <;> omega
    rw [h5, Finset.sum_map]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h6 : (addRightEmbedding h') n = n + h' := rfl
    rw [h6]
    have h7 : n + h' + (h - h') = n + h := by omega
    rw [h7]
  exact h4.symm

/-- The diagonal pair sums are bounded by the window length. -/
theorem weyl_diag {φ : ℕ → ℝ} {M N H : ℕ} (hHM : H ≤ M) (hMN : M ≤ N)
    {h : ℕ} (hhH : h < H) :
    ‖∑ n ∈ Finset.Ico (M - H + 1) (N + 1),
      (if n ∈ Finset.Ico (M - h) (N + 1 - h) then e (φ (n + h)) else 0)
        * (starRingEnd ℂ) (if n ∈ Finset.Ico (M - h) (N + 1 - h)
            then e (φ (n + h)) else 0)‖
      ≤ ((N + 1 - M : ℕ) : ℝ) := by
  classical
  have h1 : ∀ n, (if n ∈ Finset.Ico (M - h) (N + 1 - h)
        then e (φ (n + h)) else 0)
      * (starRingEnd ℂ) (if n ∈ Finset.Ico (M - h) (N + 1 - h)
          then e (φ (n + h)) else 0)
      = if n ∈ Finset.Ico (M - h) (N + 1 - h) then 1 else 0 := by
    intro n
    by_cases hn : n ∈ Finset.Ico (M - h) (N + 1 - h)
    · rw [if_pos hn, if_pos hn, e_mul_conj, sub_self, e_zero]
    · rw [if_neg hn, zero_mul, if_neg hn]
  rw [Finset.sum_congr rfl (fun n _ => h1 n), Finset.sum_ite_mem,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : Finset.Ico (M - H + 1) (N + 1)
      ∩ Finset.Ico (M - h) (N + 1 - h)
      = Finset.Ico (M - h) (N + 1 - h) := by
    rw [Finset.inter_eq_right]
    intro n hn
    rw [Finset.mem_Ico] at hn ⊢
    omega
  rw [h2, Nat.card_Ico, Complex.norm_natCast]
  have h3 : N + 1 - h - (M - h) ≤ N + 1 - M := by omega
  exact_mod_cast h3

/-- Swapping the roles in a conjugate-pair sum preserves the norm. -/
theorem norm_sum_mul_conj_comm (W : Finset ℕ) (A B : ℕ → ℂ) :
    ‖∑ n ∈ W, A n * (starRingEnd ℂ) (B n)‖
      = ‖∑ n ∈ W, B n * (starRingEnd ℂ) (A n)‖ := by
  have h1 : ∑ n ∈ W, B n * (starRingEnd ℂ) (A n)
      = (starRingEnd ℂ) (∑ n ∈ W, A n * (starRingEnd ℂ) (B n)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, Complex.conj_conj, mul_comm]
  rw [h1, RCLike.norm_conj]

/-- **Weyl differencing** (the van der Corput A-process): the square of an
exponential sum is controlled by the difference-phase sums. -/
theorem weyl_differencing {φ : ℕ → ℝ} {M N H : ℕ}
    (hH : 1 ≤ H) (hHM : H ≤ M) (hMN : M ≤ N) :
    ‖∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖ ^ 2
      ≤ (((N + 1 - M : ℕ) : ℝ) + H) / H
        * (((N + 1 - M : ℕ) : ℝ)
          + 2 * ∑ g ∈ Finset.Ico 1 H,
              ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (φ (m + g) - φ m)‖) := by
  classical
  have hHS : (H : ℂ) * ∑ n ∈ Finset.Ico M (N + 1), e (φ n)
      = ∑ n ∈ Finset.Ico (M - H + 1) (N + 1), ∑ h ∈ Finset.range H,
          (if n ∈ Finset.Ico (M - h) (N + 1 - h)
            then e (φ (n + h)) else 0) := by
    rw [Finset.sum_comm]
    have h1 : ∀ h ∈ Finset.range H,
        ∑ n ∈ Finset.Ico (M - H + 1) (N + 1),
          (if n ∈ Finset.Ico (M - h) (N + 1 - h)
            then e (φ (n + h)) else 0)
        = ∑ n ∈ Finset.Ico M (N + 1), e (φ n) := by
      intro h hh
      rw [Finset.mem_range] at hh
      rw [Finset.sum_ite_mem]
      have h2 : Finset.Ico (M - H + 1) (N + 1)
          ∩ Finset.Ico (M - h) (N + 1 - h)
          = Finset.Ico (M - h) (N + 1 - h) := by
        rw [Finset.inter_eq_right]
        intro n hn
        rw [Finset.mem_Ico] at hn ⊢
        omega
      rw [h2, ← sum_shift φ h (by omega) (by omega)]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  -- the pair-sum bound
  have hpairs : ∑ p ∈ (Finset.range H) ×ˢ (Finset.range H),
      ‖∑ n ∈ Finset.Ico (M - H + 1) (N + 1),
        (if n ∈ Finset.Ico (M - p.1) (N + 1 - p.1)
          then e (φ (n + p.1)) else 0)
        * (starRingEnd ℂ) (if n ∈ Finset.Ico (M - p.2) (N + 1 - p.2)
            then e (φ (n + p.2)) else 0)‖
      ≤ (H : ℝ) * ((N + 1 - M : ℕ) : ℝ)
        + 2 * ((H : ℝ) * ∑ g ∈ Finset.Ico 1 H,
            ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (φ (m + g) - φ m)‖) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      ((Finset.range H) ×ˢ (Finset.range H)) (fun p => p.2 < p.1),
      ← Finset.sum_filter_add_sum_filter_not
      (((Finset.range H) ×ˢ (Finset.range H)).filter
        (fun p => ¬ p.2 < p.1)) (fun p => p.1 < p.2)]
    have hS1 : ∑ p ∈ ((Finset.range H) ×ˢ (Finset.range H)).filter
        (fun p => p.2 < p.1),
        ‖∑ n ∈ Finset.Ico (M - H + 1) (N + 1),
          (if n ∈ Finset.Ico (M - p.1) (N + 1 - p.1)
            then e (φ (n + p.1)) else 0)
          * (starRingEnd ℂ) (if n ∈ Finset.Ico (M - p.2) (N + 1 - p.2)
              then e (φ (n + p.2)) else 0)‖
        ≤ (H : ℝ) * ∑ g ∈ Finset.Ico 1 H,
            ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (φ (m + g) - φ m)‖ := by
      have he : ∀ p ∈ ((Finset.range H) ×ˢ (Finset.range H)).filter
          (fun p => p.2 < p.1),
          ‖∑ n ∈ Finset.Ico (M - H + 1) (N + 1),
            (if n ∈ Finset.Ico (M - p.1) (N + 1 - p.1)
              then e (φ (n + p.1)) else 0)
            * (starRingEnd ℂ) (if n ∈ Finset.Ico (M - p.2) (N + 1 - p.2)
                then e (φ (n + p.2)) else 0)‖
          = ‖∑ m ∈ Finset.Ico M (N + 1 - (p.1 - p.2)),
              e (φ (m + (p.1 - p.2)) - φ m)‖ := by
        intro p hp
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_range] at hp
        rw [weyl_offdiag hHM hMN hp.2 hp.1.1]
      rw [Finset.sum_congr rfl he]
      exact sum_offdiag_le (fun g => ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (φ (m + g) - φ m)‖) (fun g => norm_nonneg _)
    have hS2 : ∑ p ∈ ((((Finset.range H) ×ˢ (Finset.range H)).filter
        (fun p => ¬ p.2 < p.1)).filter (fun p => p.1 < p.2)),
        ‖∑ n ∈ Finset.Ico (M - H + 1) (N + 1),
          (if n ∈ Finset.Ico (M - p.1) (N + 1 - p.1)
            then e (φ (n + p.1)) else 0)
          * (starRingEnd ℂ) (if n ∈ Finset.Ico (M - p.2) (N + 1 - p.2)
              then e (φ (n + p.2)) else 0)‖
        ≤ (H : ℝ) * ∑ g ∈ Finset.Ico 1 H,
            ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (φ (m + g) - φ m)‖ := by
      have he : ∀ p ∈ (((Finset.range H) ×ˢ (Finset.range H)).filter
          (fun p => ¬ p.2 < p.1)).filter (fun p => p.1 < p.2),
          ‖∑ n ∈ Finset.Ico (M - H + 1) (N + 1),
            (if n ∈ Finset.Ico (M - p.1) (N + 1 - p.1)
              then e (φ (n + p.1)) else 0)
            * (starRingEnd ℂ) (if n ∈ Finset.Ico (M - p.2) (N + 1 - p.2)
                then e (φ (n + p.2)) else 0)‖
          = ‖∑ m ∈ Finset.Ico M (N + 1 - (p.2 - p.1)),
              e (φ (m + (p.2 - p.1)) - φ m)‖ := by
        intro p hp
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product,
          Finset.mem_range, Finset.mem_range] at hp
        rw [norm_sum_mul_conj_comm, weyl_offdiag hHM hMN hp.2 hp.1.1.2]
      rw [Finset.sum_congr rfl he]
      have hswap : ∑ p ∈ (((Finset.range H) ×ˢ (Finset.range H)).filter
          (fun p => ¬ p.2 < p.1)).filter (fun p => p.1 < p.2),
          ‖∑ m ∈ Finset.Ico M (N + 1 - (p.2 - p.1)),
            e (φ (m + (p.2 - p.1)) - φ m)‖
          = ∑ p ∈ ((Finset.range H) ×ˢ (Finset.range H)).filter
            (fun p => p.2 < p.1),
            ‖∑ m ∈ Finset.Ico M (N + 1 - (p.1 - p.2)),
              e (φ (m + (p.1 - p.2)) - φ m)‖ := by
        refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
        · intro p hp
          rw [Finset.mem_filter, Finset.mem_filter,
            Finset.mem_product] at hp
          rw [Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.2⟩
        · intro p hp
          rw [Finset.mem_filter, Finset.mem_product] at hp
          rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product]
          simp only [Prod.fst_swap, Prod.snd_swap]
          have h21 := hp.2
          exact ⟨⟨⟨hp.1.2, hp.1.1⟩, by omega⟩, hp.2⟩
        · intro p _
          exact Prod.swap_swap p
        · intro p _
          exact Prod.swap_swap p
        · intro p _
          rfl
      rw [hswap]
      exact sum_offdiag_le (fun g => ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (φ (m + g) - φ m)‖) (fun g => norm_nonneg _)
    have hS3 : ∑ p ∈ ((((Finset.range H) ×ˢ (Finset.range H)).filter
        (fun p => ¬ p.2 < p.1)).filter (fun p => ¬ p.1 < p.2)),
        ‖∑ n ∈ Finset.Ico (M - H + 1) (N + 1),
          (if n ∈ Finset.Ico (M - p.1) (N + 1 - p.1)
            then e (φ (n + p.1)) else 0)
          * (starRingEnd ℂ) (if n ∈ Finset.Ico (M - p.2) (N + 1 - p.2)
              then e (φ (n + p.2)) else 0)‖
        ≤ (H : ℝ) * ((N + 1 - M : ℕ) : ℝ) := by
      have hbound : ∀ p ∈ (((Finset.range H) ×ˢ (Finset.range H)).filter
          (fun p => ¬ p.2 < p.1)).filter (fun p => ¬ p.1 < p.2),
          ‖∑ n ∈ Finset.Ico (M - H + 1) (N + 1),
            (if n ∈ Finset.Ico (M - p.1) (N + 1 - p.1)
              then e (φ (n + p.1)) else 0)
            * (starRingEnd ℂ) (if n ∈ Finset.Ico (M - p.2) (N + 1 - p.2)
                then e (φ (n + p.2)) else 0)‖
          ≤ ((N + 1 - M : ℕ) : ℝ) := by
        intro p hp
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product,
          Finset.mem_range, Finset.mem_range] at hp
        have hpe : p.2 = p.1 := by omega
        rw [hpe]
        exact weyl_diag hHM hMN hp.1.1.1
      refine le_trans (Finset.sum_le_sum hbound) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      have hcard : ((((Finset.range H) ×ˢ (Finset.range H)).filter
          (fun p => ¬ p.2 < p.1)).filter (fun p => ¬ p.1 < p.2)).card
          ≤ H := by
        have hinj := Finset.card_le_card_of_injOn Prod.fst
          (s := (((Finset.range H) ×ˢ (Finset.range H)).filter
            (fun p => ¬ p.2 < p.1)).filter (fun p => ¬ p.1 < p.2))
          (t := Finset.range H) ?_ ?_
        · rw [Finset.card_range] at hinj
          exact hinj
        · intro p hp
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter,
            Finset.mem_product] at hp
          rw [Finset.mem_coe]
          exact hp.1.1.1
        · intro p hp q hq hpq
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter] at hp hq
          have h5 : p.2 = p.1 := by omega
          have h6 : q.2 = q.1 := by omega
          refine Prod.ext hpq ?_
          rw [h5, h6, hpq]
      exact_mod_cast hcard
    linarith [hS1, hS2, hS3]
  -- assemble
  have hcs := norm_sum_sq_le_card_mul (Finset.Ico (M - H + 1) (N + 1))
    (fun n => ∑ h ∈ Finset.range H,
      (if n ∈ Finset.Ico (M - h) (N + 1 - h) then e (φ (n + h)) else 0))
  have hex := sum_norm_sq_expand (Finset.Ico (M - H + 1) (N + 1))
    (Finset.range H)
    (fun n h => if n ∈ Finset.Ico (M - h) (N + 1 - h)
      then e (φ (n + h)) else 0)
  beta_reduce at hcs hex
  have hWcard : ((Finset.Ico (M - H + 1) (N + 1)).card : ℝ)
      = ((N + 1 - M : ℕ) : ℝ) + (H : ℝ) - 1 := by
    rw [Nat.card_Ico]
    have h8 : N + 1 - (M - H + 1) = (N + 1 - M) + H - 1 := by omega
    rw [h8]
    have h9 : (N + 1 - M) + H - 1 + 1 = (N + 1 - M) + H := by omega
    have h10 := congrArg (fun k : ℕ => (k : ℝ)) h9
    push_cast at h10
    linarith
  have hchain : (H : ℝ) ^ 2
      * ‖∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖ ^ 2
      ≤ (((N + 1 - M : ℕ) : ℝ) + (H : ℝ) - 1)
        * ((H : ℝ) * ((N + 1 - M : ℕ) : ℝ)
          + 2 * ((H : ℝ) * ∑ g ∈ Finset.Ico 1 H,
              ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (φ (m + g) - φ m)‖)) := by
    have h11 : (H : ℝ) ^ 2
        * ‖∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖ ^ 2
        = ‖(H : ℂ) * ∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖ ^ 2 := by
      rw [norm_mul, Complex.norm_natCast, mul_pow]
    rw [h11, hHS]
    calc ‖∑ n ∈ Finset.Ico (M - H + 1) (N + 1), ∑ h ∈ Finset.range H,
          (if n ∈ Finset.Ico (M - h) (N + 1 - h)
            then e (φ (n + h)) else 0)‖ ^ 2
        ≤ ((Finset.Ico (M - H + 1) (N + 1)).card : ℝ)
          * ∑ n ∈ Finset.Ico (M - H + 1) (N + 1),
            ‖∑ h ∈ Finset.range H,
              (if n ∈ Finset.Ico (M - h) (N + 1 - h)
                then e (φ (n + h)) else 0)‖ ^ 2 := hcs
      _ ≤ ((Finset.Ico (M - H + 1) (N + 1)).card : ℝ)
          * ((H : ℝ) * ((N + 1 - M : ℕ) : ℝ)
            + 2 * ((H : ℝ) * ∑ g ∈ Finset.Ico 1 H,
                ‖∑ m ∈ Finset.Ico M (N + 1 - g),
                  e (φ (m + g) - φ m)‖)) := by
          refine mul_le_mul_of_nonneg_left (le_trans hex hpairs)
            (Nat.cast_nonneg _)
      _ = (((N + 1 - M : ℕ) : ℝ) + (H : ℝ) - 1)
          * ((H : ℝ) * ((N + 1 - M : ℕ) : ℝ)
            + 2 * ((H : ℝ) * ∑ g ∈ Finset.Ico 1 H,
                ‖∑ m ∈ Finset.Ico M (N + 1 - g),
                  e (φ (m + g) - φ m)‖)) := by
          rw [hWcard]
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hFpos : (0 : ℝ) ≤ ∑ g ∈ Finset.Ico 1 H,
      ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (φ (m + g) - φ m)‖ :=
    Finset.sum_nonneg fun g _ => norm_nonneg _
  have hLpos : (0 : ℝ) ≤ ((N + 1 - M : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [div_mul_eq_mul_div, le_div_iff₀ hHpos]
  have hs0 : (0 : ℝ) ≤ ‖∑ n ∈ Finset.Ico M (N + 1), e (φ n)‖ ^ 2 := by
    positivity
  nlinarith [hchain, hHpos, hFpos, hLpos, hs0]

/-- **The weighted Abel bound**: a decreasing nonnegative weight against
uniformly bounded partial sums costs only the leading weight. -/
theorem abel_weight_bound {w : ℕ → ℝ} {a : ℕ → ℂ} {M N : ℕ} {E : ℝ}
    (hMN : M ≤ N)
    (hw0 : ∀ n, M ≤ n → n ≤ N → 0 ≤ w n)
    (hwd : ∀ n, M ≤ n → n < N → w (n + 1) ≤ w n)
    (hE : ∀ P, M ≤ P → P ≤ N + 1 →
      ‖∑ n ∈ Finset.Ico M P, a n‖ ≤ E) :
    ‖∑ n ∈ Finset.Ico M (N + 1), w n • a n‖ ≤ w M * E := by
  classical
  have hE0 : 0 ≤ E := by
    have := hE M le_rfl (by omega)
    rw [Finset.Ico_self, Finset.sum_empty, norm_zero] at this
    exact this
  -- partial sums
  set A : ℕ → ℂ := fun P => ∑ n ∈ Finset.Ico M P, a n with hA
  have hstep : ∀ n, M ≤ n → A (n + 1) - A n = a n := by
    intro n hn
    show (∑ m ∈ Finset.Ico M (n + 1), a m)
      - (∑ m ∈ Finset.Ico M n, a m) = a n
    rw [Finset.sum_Ico_succ_top hn]
    ring
  have hsummand : ∀ n ∈ Finset.Ico M (N + 1),
      w n • a n = (A (n + 1) - A n) * (w n : ℂ) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    rw [hstep n hn.1]
    rw [Complex.real_smul]
    ring
  rw [Finset.sum_congr rfl hsummand,
    sum_diff_mul_eq A (fun n => (w n : ℂ)) hMN]
  have hAM : A M = 0 := by
    show (∑ m ∈ Finset.Ico M M, a m) = 0
    rw [Finset.Ico_self, Finset.sum_empty]
  rw [hAM, zero_mul, sub_zero]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖A (N + 1) * ((w N : ℝ) : ℂ)‖ ≤ E * w N := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hw0 N hMN le_rfl)]
    exact mul_le_mul_of_nonneg_right (hE (N + 1) (by omega) le_rfl)
      (hw0 N hMN le_rfl)
  have h2 : ‖∑ n ∈ Finset.Ico M N,
      A (n + 1) * (((w n : ℝ) : ℂ) - ((w (n + 1) : ℝ) : ℂ))‖
      ≤ (w M - w N) * E := by
    refine le_trans (norm_sum_le _ _) ?_
    have h3 : ∀ n ∈ Finset.Ico M N,
        ‖A (n + 1) * (((w n : ℝ) : ℂ) - ((w (n + 1) : ℝ) : ℂ))‖
        ≤ (w n - w (n + 1)) * E := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      rw [norm_mul]
      have h4 : (((w n : ℝ) : ℂ) - ((w (n + 1) : ℝ) : ℂ))
          = ((w n - w (n + 1) : ℝ) : ℂ) := by push_cast; ring
      rw [h4, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hwd n hn.1 hn.2])]
      rw [mul_comm ((w n - w (n + 1))) E]
      exact mul_le_mul_of_nonneg_right
        (hE (n + 1) (by omega) (by omega))
        (by linarith [hwd n hn.1 hn.2])
    refine le_trans (Finset.sum_le_sum h3) ?_
    have h5 : ∑ n ∈ Finset.Ico M N, (w n - w (n + 1)) * E
        = (∑ n ∈ Finset.Ico M N, (w n - w (n + 1))) * E := by
      rw [Finset.sum_mul]
    rw [h5]
    have h6 : ∑ n ∈ Finset.Ico M N, (w n - w (n + 1)) = w M - w N := by
      have h7 := sum_Ico_sub_telescope w hMN
      exact h7
    rw [h6]
  have h8 : E * w N + (w M - w N) * E = w M * E := by ring
  linarith [h1, h2]


end ExpSums

end MoltResearch
