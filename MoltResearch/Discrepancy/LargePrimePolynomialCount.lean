import MoltResearch.Discrepancy.WindowTK

/-!
# High-moment counts for prime Dirichlet polynomials

This is the cardinality form of the high-moment estimate used in the
exceptional-frequency argument.  The power of the prime polynomial is collapsed
onto products of primes, and the existing separated-sample inequality is applied
to that Dirichlet polynomial.  All constants, including the derivative cost from
unit-cell sampling, remain explicit.
-/

namespace MoltResearch

open Finset MeasureTheory ExpSums

-- Expanding the power and its derivative gives a large but bounded elaboration.
set_option maxHeartbeats 800000 in
/-- **Phase 0 VI-9b — a high-moment count at separated large values.**

For a prime polynomial `Q` supported on `(P, 2P]`, a `1`-separated family in
`[-T,T]` on which `‖Q‖ ≥ V` has cardinality controlled by the `2ℓ`-moment
scale.  The final parenthesis is the explicit Gallagher derivative cost for the
collapsed polynomial `Q^ℓ`; its support is contained in `(P^ℓ,(2P)^ℓ]`. -/
theorem card_large_prime_poly_pow_le (Y : Finset ℕ)
    (hY : ∀ p ∈ Y, p.Prime) (P : ℕ) (hP : 1 ≤ P)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2 * P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1) (ell : ℕ) (hell : 1 ≤ ell)
    (points : Finset ℝ) (T V lam : ℝ) (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hlam : 0 < lam)
    (hmem : ∀ t ∈ points, t ∈ Set.Icc (-T) T)
    (hsep : ∀ t ∈ points, ∀ u ∈ points, t ≠ u → 1 ≤ |t - u|)
    (hlarge : ∀ t ∈ points,
      V ≤ ‖∑ p ∈ Y, (b p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖) :
    (points.card : ℝ) * V ^ (2 * ell)
      ≤ Real.exp Real.pi
          * ((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ))
        * ((Nat.factorial ell : ℝ) ^ 2
            * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell)
        * ((1 + lam) + (1 / lam)
            * (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2) := by
  classical
  set tuples : Finset (Fin ell → ℕ) := Fintype.piFinset (fun _ : Fin ell => Y)
    with htuples
  set support : Finset ℕ := tuples.image (fun v => ∏ i, v i) with hsupport
  set c : ℕ → ℂ := fun n =>
    ∑ v ∈ tuples.filter (fun v => ∏ i, v i = n), ∏ i, b (v i) with hc
  have hppos : ∀ p ∈ Y, 0 < p := fun p hp => (hY p hp).pos
  have hpow : ∀ t : ℝ,
      (∑ p ∈ Y, (b p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)) ^ ell =
        ∑ n ∈ support, (c n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) := by
    intro t
    rw [phase_poly_pow Y b hppos ell t]
    exact phase_poly_fiberwise' tuples (fun v => ∏ i, v i) support
      (fun v hv => by
        rw [hsupport, Finset.mem_image]
        exact ⟨v, hv, rfl⟩)
      (fun v => ∏ i, b (v i)) t
  have hPpow : 1 ≤ P ^ ell := Nat.one_le_pow _ _ hP
  have hsupp : support ⊆ Finset.Ioc (P ^ ell) (2 ^ ell * P ^ ell) := by
    intro n hn
    rw [hsupport, Finset.mem_image] at hn
    obtain ⟨v, hv, rfl⟩ := hn
    rw [htuples, Fintype.mem_piFinset] at hv
    have hcard : (Finset.univ : Finset (Fin ell)).card = ell := by simp
    rw [Finset.mem_Ioc]
    constructor
    · have hstep : (P + 1) ^ ell ≤ ∏ i, v i := by
        calc
          (P + 1) ^ ell = ∏ _i : Fin ell, (P + 1) := by
            rw [Finset.prod_const, hcard]
          _ ≤ ∏ i, v i := Finset.prod_le_prod' fun i _ => hlo _ (hv i)
      have : P ^ ell < (P + 1) ^ ell := Nat.pow_lt_pow_left (by omega) (by omega)
      omega
    · calc
        ∏ i, v i ≤ ∏ _i : Fin ell, (2 * P) :=
          Finset.prod_le_prod' fun i _ => hhi _ (hv i)
        _ = (2 * P) ^ ell := by rw [Finset.prod_const, hcard]
        _ = 2 ^ ell * P ^ ell := by rw [mul_pow]
  have hcbd : ∀ n, ‖c n‖ ≤ (Nat.factorial ell : ℝ) := by
    intro n
    have hfiber := card_prime_tuple_fiber_le (ℓ := ell) Y hY n
    calc
      ‖c n‖ ≤ ∑ _v ∈ tuples.filter (fun v => ∏ i, v i = n), (1 : ℝ) := by
        rw [hc]
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun v _ => ?_)
        rw [norm_prod]
        exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hb _)
      _ = ((tuples.filter (fun v => ∏ i, v i = n)).card : ℝ) := by simp
      _ ≤ (Nat.factorial ell : ℝ) := by exact_mod_cast hfiber
  have hmass : ∑ n ∈ support, ‖c n‖ ^ 2 / (n : ℝ)
      ≤ (Nat.factorial ell : ℝ) ^ 2
          * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell := by
    calc
      ∑ n ∈ support, ‖c n‖ ^ 2 / (n : ℝ)
          ≤ (Nat.factorial ell : ℝ) ^ 2
              * ∑ n ∈ support, (1 : ℝ) / (n : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun n hn => ?_
        have hn0 : (0 : ℝ) < n := by
          exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_succ _) (Finset.mem_Ioc.mp (hsupp hn)).1)
        rw [div_le_iff₀ hn0]
        have hsq := pow_le_pow_left₀ (norm_nonneg _) (hcbd n) 2
        convert hsq using 1 <;> field_simp
      _ ≤ (Nat.factorial ell : ℝ) ^ 2
              * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell := by
        gcongr
        rw [hsupport, htuples]
        exact sum_one_div_image_prod_le Y ell
  have hlogmass :
      ∑ n ∈ support, (2 * Real.pi * Real.log n) ^ 2 * ‖c n‖ ^ 2 / (n : ℝ)
        ≤ (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2
            * ((Nat.factorial ell : ℝ) ^ 2
              * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell) := by
    have hlogfac : 0 ≤ (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2 := sq_nonneg _
    calc
      ∑ n ∈ support, (2 * Real.pi * Real.log n) ^ 2 * ‖c n‖ ^ 2 / (n : ℝ)
          ≤ ∑ n ∈ support, (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2
              * (‖c n‖ ^ 2 / (n : ℝ)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hnNat : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ _)
          (Finset.mem_Ioc.mp (hsupp hn)).1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
        have hnUpper : n ≤ (2 * P) ^ ell := by
          rw [mul_pow]
          exact (Finset.mem_Ioc.mp (hsupp hn)).2
        have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hnNat)
        have hlogle : Real.log n ≤ Real.log ((2 * P) ^ ell) := by
          exact Real.log_le_log hn0 (by exact_mod_cast hnUpper)
        have hphase : 0 ≤ 2 * Real.pi * Real.log n := by positivity
        have hphaseLe : 2 * Real.pi * Real.log n
            ≤ 2 * Real.pi * Real.log ((2 * P) ^ ell) := by gcongr
        have hsq := pow_le_pow_left₀ hphase hphaseLe 2
        have hcoef0 : 0 ≤ ‖c n‖ ^ 2 / (n : ℝ) := by positivity
        calc
          (2 * Real.pi * Real.log n) ^ 2 * ‖c n‖ ^ 2 / (n : ℝ)
              = (2 * Real.pi * Real.log n) ^ 2 * (‖c n‖ ^ 2 / (n : ℝ)) := by ring
          _ ≤ (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2
              * (‖c n‖ ^ 2 / (n : ℝ)) := mul_le_mul_of_nonneg_right hsq hcoef0
      _ = (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2
              * ∑ n ∈ support, ‖c n‖ ^ 2 / (n : ℝ) := by rw [Finset.mul_sum]
      _ ≤ (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2
            * ((Nat.factorial ell : ℝ) ^ 2
              * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell) :=
        mul_le_mul_of_nonneg_left hmass hlogfac
  have hlargePow : ∀ t ∈ points, V ^ ell ≤ ‖∑ n ∈ support,
      (c n / (n : ℂ))
        * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ := by
    intro t ht
    rw [← hpow t, norm_pow]
    exact pow_le_pow_left₀ hV (hlarge t ht) ell
  have hcount := card_large_poly_le support (P ^ ell) (2 ^ ell) hPpow
    Nat.one_le_two_pow hsupp c points T (V ^ ell) lam hT (pow_nonneg hV ell)
    hlam hmem hsep hlargePow
  have hE0 : 0 ≤ Real.exp Real.pi
      * ((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ)) := by
    positivity
  have hlam0 : 0 ≤ 1 / lam := by positivity
  calc
    (points.card : ℝ) * V ^ (2 * ell) = (points.card : ℝ) * (V ^ ell) ^ 2 := by
      rw [Nat.mul_comm 2 ell, pow_mul]
    _ ≤ (1 + lam) * (Real.exp Real.pi
            * ((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ))
            * ∑ n ∈ support, ‖c n‖ ^ 2 / (n : ℝ))
        + (1 / lam) * (Real.exp Real.pi
            * ((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ))
            * ∑ n ∈ support,
              (2 * Real.pi * Real.log n) ^ 2 * ‖c n‖ ^ 2 / (n : ℝ)) := hcount
    _ ≤ (1 + lam) * (Real.exp Real.pi
            * ((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ))
            * ((Nat.factorial ell : ℝ) ^ 2
              * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell))
        + (1 / lam) * (Real.exp Real.pi
            * ((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ))
            * ((2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2
              * ((Nat.factorial ell : ℝ) ^ 2
                * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell))) := by
      gcongr
    _ = Real.exp Real.pi
          * ((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ))
        * ((Nat.factorial ell : ℝ) ^ 2
            * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell)
        * ((1 + lam) + (1 / lam)
            * (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2) := by ring

end MoltResearch
