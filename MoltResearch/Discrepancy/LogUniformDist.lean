import MoltResearch.Discrepancy.LogUniform

/-!
# Discrepancy: the finite log-uniform distribution

Track C, Elliott campaign (`Problems/tao2015_derivation_c.md`, issue #2946, E6a): the
probability packaging of the paper's random variable `𝐧` — `P(𝐧 = n) ∝ 1/n` on a
window `(A, B]` — as a plain weight function, so the E1 entropy layer applies to its
pushforwards.

* `logWeight A B` — the normalized weights; nonnegative, summing to `1` on a
  nonempty window.
* `pushWeight` — the pushforward of a finite weighted set along a map into a
  `Fintype` (the law of `f(𝐧)`); total mass is preserved.
* `abs_sum_one_div_residue_sub_le` — **near-uniformity mod `q`** at the unnormalized
  level: the log-mass of a residue class is `(1/q)`-th of the window's within
  `2r/q² + (2 log q + 4)/q` — the finitary (hayah): `𝐧 mod q` is almost uniform.
-/

namespace MoltResearch

open Finset

/-- The normalized log-uniform weight on the window `(A, B]`. -/
noncomputable def logWeight (A B : ℕ) : ℕ → ℝ :=
  fun n => (1 / n) / ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m

theorem logWeight_nonneg (A B n : ℕ) : 0 ≤ logWeight A B n := by
  rw [logWeight]
  have h1 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m :=
    Finset.sum_nonneg fun m _ => by positivity
  positivity

theorem sum_logWeight {A B : ℕ} (hA : 1 ≤ A) (hAB : A < B) :
    ∑ n ∈ Finset.Ioc A B, logWeight A B n = 1 := by
  have hSpos : (0 : ℝ) < ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m := by
    refine Finset.sum_pos (fun m hm => ?_) ⟨A + 1, by
      rw [Finset.mem_Ioc]
      omega⟩
    rw [Finset.mem_Ioc] at hm
    have : (0 : ℝ) < (m : ℝ) := by
      have : 1 ≤ m := by omega
      exact_mod_cast this
    positivity
  have hrw : ∑ n ∈ Finset.Ioc A B, logWeight A B n
      = (∑ n ∈ Finset.Ioc A B, (1 : ℝ) / n)
        * (∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m)⁻¹ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [logWeight, div_eq_mul_inv]
  rw [hrw, mul_inv_cancel₀ (ne_of_gt hSpos)]

/-- The expectation dictionary: log-weighted averages against the unnormalized
`1/n`-sums. -/
theorem sum_logWeight_mul (A B : ℕ) (F : ℕ → ℂ) :
    ∑ n ∈ Finset.Ioc A B, ((logWeight A B n : ℝ) : ℂ) * F n
      = (1 / ((∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m : ℝ) : ℂ))
        * ∑ n ∈ Finset.Ioc A B, F n / (n : ℂ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [logWeight]
  push_cast
  field_simp

/-- The pushforward of a finite weighted set along a map into a `Fintype` — the law
of `f(𝐧)`. -/
noncomputable def pushWeight (s : Finset ℕ) (w : ℕ → ℝ) {β : Type*} [Fintype β]
    [DecidableEq β] (f : ℕ → β) : β → ℝ :=
  fun b => ∑ n ∈ s.filter (fun n => f n = b), w n

theorem pushWeight_nonneg {s : Finset ℕ} {w : ℕ → ℝ} (hw : ∀ n ∈ s, 0 ≤ w n)
    {β : Type*} [Fintype β] [DecidableEq β] (f : ℕ → β) (b : β) :
    0 ≤ pushWeight s w f b :=
  Finset.sum_nonneg fun n hn => hw n (Finset.mem_filter.mp hn).1

theorem sum_pushWeight (s : Finset ℕ) (w : ℕ → ℝ) {β : Type*} [Fintype β]
    [DecidableEq β] (f : ℕ → β) :
    ∑ b, pushWeight s w f b = ∑ n ∈ s, w n :=
  Finset.sum_fiberwise_of_maps_to (fun n _ => Finset.mem_univ (f n)) w

/-- **Pushforward expectation dictionary** (`ℂ`-valued): integrating an
observable against the pushed law is integrating its pullback. -/
theorem sum_pushWeight_mul_complex (s : Finset ℕ) (w : ℕ → ℝ) {β : Type*}
    [Fintype β] [DecidableEq β] (f : ℕ → β) (F : β → ℂ) :
    ∑ b, ((pushWeight s w f b : ℝ) : ℂ) * F b
      = ∑ n ∈ s, ((w n : ℝ) : ℂ) * F (f n) := by
  classical
  rw [show (∑ b, ((pushWeight s w f b : ℝ) : ℂ) * F b)
      = ∑ b, ∑ n ∈ s.filter (fun n => f n = b), ((w n : ℝ) : ℂ) * F b from
    Finset.sum_congr rfl fun b _ => by
      rw [pushWeight, Complex.ofReal_sum, Finset.sum_mul]]
  rw [← Finset.sum_fiberwise_of_maps_to (g := f)
    (fun n _ => Finset.mem_univ (f n)) (fun n => ((w n : ℝ) : ℂ) * F (f n))]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_filter] at hn
  rw [hn.2]

/-- Window-quotient log bound, `r`-shifted form. -/
theorem log_div_window_le' {q r A : ℕ} (hq : 2 ≤ q) (hr : r < q) (h4q : 4 * q ≤ A) :
    Real.log A - Real.log ((A - r) / q : ℕ) ≤ Real.log (2 * q) := by
  have hq0 : 0 < q := by omega
  have hA0 : (0 : ℝ) < (A : ℝ) := by
    have : (8 : ℝ) ≤ (A : ℝ) := by exact_mod_cast le_trans (by omega) h4q
    linarith
  have hq1 : 1 ≤ (A - r) / q := by
    rw [Nat.one_le_div_iff hq0]
    omega
  have hq0R : (0 : ℝ) < (((A - r) / q : ℕ) : ℝ) := by exact_mod_cast hq1
  rw [← Real.log_div (ne_of_gt hA0) (ne_of_gt hq0R)]
  refine Real.log_le_log (by positivity) ?_
  -- A ≤ 2q·((A−r)/q)
  have hkey : A ≤ 2 * q * ((A - r) / q) := by
    have hmod := Nat.div_add_mod (A - r) q
    have hlt : (A - r) % q < q := Nat.mod_lt _ hq0
    have hsub : A - r + r = A := Nat.sub_add_cancel (by omega)
    have h3 : 2 * q * ((A - r) / q) = 2 * (q * ((A - r) / q)) := by ring
    omega
  have hkeyR : (A : ℝ) ≤ 2 * (q : ℝ) * (((A - r) / q : ℕ) : ℝ) := by
    exact_mod_cast hkey
  rw [div_le_iff₀ hq0R]
  nlinarith [hkeyR]

set_option maxHeartbeats 800000 in
/-- **Near-uniformity of `𝐧 mod q`** (the finitary (hayah)): the unnormalized
log-mass of the class `r (q)` in `(A, B]` is `(1/q)`-th of the window's, within
`2r/q² + (2 log(2q) + 2)/q`. -/
theorem abs_sum_one_div_residue_sub_le {q r A B : ℕ} (hq : 2 ≤ q) (hr : r < q)
    (h4q : 4 * q ≤ A) (hqB : q * (A + 1) ≤ B) :
    |(∑ n ∈ (Finset.Ioc A B).filter (fun n => n % q = r), (1 : ℝ) / n)
        - (1 / q) * ∑ n ∈ Finset.Ioc A B, (1 : ℝ) / n|
      ≤ 2 * r / q ^ 2 + (2 * Real.log (2 * q) + 2) / q := by
  classical
  have hq0 : 0 < q := by omega
  have hA1 : 1 ≤ A := by omega
  -- run the ℂ-machinery at F ≡ 1 and take real parts
  set Fc : ℕ → ℂ := fun _ => 1 with hFc
  have hFc1 : ∀ n, ‖Fc n‖ ≤ 1 := fun n => by rw [hFc]; simp
  -- dictionary: the real sums are the real parts of the ℂ-sums
  have hdict : ∀ s : Finset ℕ, (∑ n ∈ s, (1 : ℝ) / n)
      = (∑ n ∈ s, Fc n / (n : ℂ)).re := by
    intro s
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hFc]
    rw [show (1 : ℂ) / (n : ℂ) = (((1 : ℝ) / (n : ℝ) : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.ofReal_re]
  -- the ℂ-chain: class ↔ (1/q)·window
  -- step 1: exact reindex to the divided window
  have hreindex : ∑ n ∈ (Finset.Ioc A B).filter (fun n => n % q = r), Fc n / (n : ℂ)
      = ∑ n' ∈ Finset.Ioc ((A - r) / q) ((B - r) / q),
          Fc (q * n' + r) / ((q * n' + r : ℕ) : ℂ) := by
    have h1 := sum_filter_residue_eq_sum_image hq0 hr
      (fun n => Fc n / (n : ℂ)) (Finset.Ioc A B)
    rw [h1, image_div_filter_eq hq0 hr A B (by omega)]
  -- step 2: weight comparison and pull-out of 1/q
  have hAq : q ≤ A := by omega
  have hweight := norm_sum_div_residue_sub_le hq0 hr hFc1 (a := A) (b := B) hAq
  have hdivcomp : ∀ n' : ℕ, (q * n' + r) / q = n' := by
    intro n'
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hq0]
    have h0 := Nat.div_eq_of_lt hr
    omega
  have hsecond : ∑ n ∈ (Finset.Ioc A B).filter (fun n => n % q = r),
        Fc n / (q : ℂ) / ((n / q : ℕ) : ℂ)
      = (1 / (q : ℂ)) * ∑ n' ∈ Finset.Ioc ((A - r) / q) ((B - r) / q),
          Fc (q * n' + r) / ((n' : ℕ) : ℂ) := by
    rw [Finset.mul_sum]
    have h1 := sum_filter_residue_eq_sum_image hq0 hr
      (fun n => Fc n / (q : ℂ) / ((n / q : ℕ) : ℂ)) (Finset.Ioc A B)
    rw [h1, image_div_filter_eq hq0 hr A B (by omega)]
    refine Finset.sum_congr rfl fun n' _ => ?_
    rw [hdivcomp n']
    rw [hFc]
    push_cast
    ring
  -- step 3: window restoration inside the 1/q prefactor
  have hADq : (A - r) / q ≤ A := le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
  have hABq : A ≤ (B - r) / q := by
    rw [Nat.le_div_iff_mul_le hq0]
    have hcomm : A * q = q * A := Nat.mul_comm A q
    have hd : q * (A + 1) = q * A + q := by ring
    omega
  have hBqB : (B - r) / q ≤ B := le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
  have hone : ∀ m : ℕ, 1 ≤ m → ‖Fc (q * m + r) / ((m : ℕ) : ℂ)‖ = 1 / (m : ℝ) := by
    intro m hm
    rw [hFc, norm_div, norm_one, Complex.norm_natCast]
  have h4qB : 4 * q ≤ B := by omega
  have hwin : ‖(∑ n' ∈ Finset.Ioc ((A - r) / q) ((B - r) / q),
        Fc (q * n' + r) / ((n' : ℕ) : ℂ))
      - ∑ n' ∈ Finset.Ioc A B, Fc (q * n' + r) / ((n' : ℕ) : ℂ)‖
      ≤ 2 * Real.log (2 * q) + 2 := by
    have hsplit1 : Finset.Ioc ((A - r) / q) ((B - r) / q)
        = Finset.Ioc ((A - r) / q) A ∪ Finset.Ioc A ((B - r) / q) :=
      (Finset.Ioc_union_Ioc_eq_Ioc hADq hABq).symm
    have hsplit2 : Finset.Ioc A B
        = Finset.Ioc A ((B - r) / q) ∪ Finset.Ioc ((B - r) / q) B :=
      (Finset.Ioc_union_Ioc_eq_Ioc hABq hBqB).symm
    have hdisj1 : Disjoint (Finset.Ioc ((A - r) / q) A)
        (Finset.Ioc A ((B - r) / q)) := by
      refine Finset.disjoint_left.mpr fun m hm1 hm2 => ?_
      rw [Finset.mem_Ioc] at hm1 hm2
      omega
    have hdisj2 : Disjoint (Finset.Ioc A ((B - r) / q))
        (Finset.Ioc ((B - r) / q) B) := by
      refine Finset.disjoint_left.mpr fun m hm1 hm2 => ?_
      rw [Finset.mem_Ioc] at hm1 hm2
      omega
    rw [hsplit1, hsplit2, Finset.sum_union hdisj1, Finset.sum_union hdisj2]
    rw [show ∀ x y z : ℂ, (x + y) - (y + z) = x - z from fun x y z => by ring]
    refine le_trans (norm_sub_le _ _) ?_
    have hq1' : 1 ≤ (A - r) / q := by
      rw [Nat.one_le_div_iff hq0]
      omega
    have hmass1 : ‖∑ m ∈ Finset.Ioc ((A - r) / q) A,
        Fc (q * m + r) / ((m : ℕ) : ℂ)‖ ≤ Real.log (2 * q) := by
      refine le_trans (norm_sum_le _ _) ?_
      have hle : ∀ m ∈ Finset.Ioc ((A - r) / q) A,
          ‖Fc (q * m + r) / ((m : ℕ) : ℂ)‖ = 1 / (m : ℝ) := by
        intro m hm
        rw [Finset.mem_Ioc] at hm
        exact hone m (by omega)
      rw [Finset.sum_congr rfl hle]
      refine le_trans (sum_one_div_Ioc_le hq1' hADq) ?_
      exact log_div_window_le' hq hr h4q
    have hmass2 : ‖∑ m ∈ Finset.Ioc ((B - r) / q) B,
        Fc (q * m + r) / ((m : ℕ) : ℂ)‖ ≤ Real.log (2 * q) := by
      refine le_trans (norm_sum_le _ _) ?_
      have hq1'' : 1 ≤ (B - r) / q := by
        rw [Nat.one_le_div_iff hq0]
        omega
      have hle : ∀ m ∈ Finset.Ioc ((B - r) / q) B,
          ‖Fc (q * m + r) / ((m : ℕ) : ℂ)‖ = 1 / (m : ℝ) := by
        intro m hm
        rw [Finset.mem_Ioc] at hm
        exact hone m (by omega)
      rw [Finset.sum_congr rfl hle]
      refine le_trans (sum_one_div_Ioc_le hq1'' hBqB) ?_
      exact log_div_window_le' hq hr h4qB
    have hlog2q : (0 : ℝ) ≤ Real.log (2 * q) := by
      refine Real.log_nonneg ?_
      have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      push_cast
      linarith
    linarith
  -- assemble in ℂ, then take real parts
  have hq0R : (0 : ℝ) < (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hpnorm : ‖(1 / (q : ℂ))‖ = 1 / (q : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  have hCtotal : ‖(∑ n ∈ (Finset.Ioc A B).filter (fun n => n % q = r),
        Fc n / (n : ℂ))
      - (1 / (q : ℂ)) * ∑ n' ∈ Finset.Ioc A B,
          Fc (q * n' + r) / ((n' : ℕ) : ℂ)‖
      ≤ 2 * r / q ^ 2 + (2 * Real.log (2 * q) + 2) / q := by
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (∑ n ∈ (Finset.Ioc A B).filter (fun n => n % q = r), Fc n / (n : ℂ))
      (∑ n ∈ (Finset.Ioc A B).filter (fun n => n % q = r),
        Fc n / (q : ℂ) / ((n / q : ℕ) : ℂ))
      ((1 / (q : ℂ)) * ∑ n' ∈ Finset.Ioc A B,
        Fc (q * n' + r) / ((n' : ℕ) : ℂ))
    have h2 : ‖(∑ n ∈ (Finset.Ioc A B).filter (fun n => n % q = r),
          Fc n / (q : ℂ) / ((n / q : ℕ) : ℂ))
        - (1 / (q : ℂ)) * ∑ n' ∈ Finset.Ioc A B,
            Fc (q * n' + r) / ((n' : ℕ) : ℂ)‖
        ≤ (2 * Real.log (2 * q) + 2) / q := by
      rw [hsecond, ← mul_sub, norm_mul, hpnorm]
      rw [div_eq_mul_inv (2 * Real.log (2 * q) + 2), mul_comm (2 * Real.log (2 * q) + 2),
        one_div]
      exact mul_le_mul_of_nonneg_left hwin (by positivity)
    linarith [hweight, h2, htri]
  -- the target sum on the right is the plain window mass
  have hplain : (∑ n' ∈ Finset.Ioc A B, Fc (q * n' + r) / ((n' : ℕ) : ℂ)).re
      = ∑ n ∈ Finset.Ioc A B, (1 : ℝ) / n := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hFc]
    rw [show (1 : ℂ) / (n : ℂ) = (((1 : ℝ) / (n : ℝ) : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.ofReal_re]
  -- real parts close it
  have hreal : (∑ n ∈ (Finset.Ioc A B).filter (fun n => n % q = r), (1 : ℝ) / n)
      - (1 / q) * ∑ n ∈ Finset.Ioc A B, (1 : ℝ) / n
      = ((∑ n ∈ (Finset.Ioc A B).filter (fun n => n % q = r), Fc n / (n : ℂ))
        - (1 / (q : ℂ)) * ∑ n' ∈ Finset.Ioc A B,
            Fc (q * n' + r) / ((n' : ℕ) : ℂ)).re := by
    rw [Complex.sub_re, ← hdict, Complex.mul_re]
    rw [show ((1 : ℂ) / (q : ℂ)).re = 1 / (q : ℝ) from by
      rw [show (1 : ℂ) / (q : ℂ) = (((1 : ℝ) / (q : ℝ) : ℝ) : ℂ) from by
        push_cast; ring, Complex.ofReal_re]]
    rw [show ((1 : ℂ) / (q : ℂ)).im = 0 from by
      rw [show (1 : ℂ) / (q : ℂ) = (((1 : ℝ) / (q : ℝ) : ℝ) : ℂ) from by
        push_cast; ring, Complex.ofReal_im]]
    rw [hplain]
    ring
  rw [hreal]
  exact le_trans (Complex.abs_re_le_norm _) hCtotal

end MoltResearch
