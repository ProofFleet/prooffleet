import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Field

/-!
# Discrepancy: Chebyshev bound and the prime tail estimate

Track C, VK/Littlewood campaign (`Problems/tao2015_derivation_c.md`, issue #2935, W2c):

* `sum_log_primesBelow_le` — Chebyshev's bound `θ(y) = ∑_{p<y} log p ≤ y log 4`, from
  Mathlib's primorial estimate `primorial_le_4_pow`.
* `tsum_primes_tail_rpow_le` — **the prime tail estimate**: at `σ = 1 + 1/log y`,
  `∑_{p ≥ y} p^{−σ} ≤ 8`. Dyadic decomposition: the block `[2^k y, 2^{k+1} y)` holds at
  most `2^{k+1} y log 4 / log y` primes by Chebyshev, each contributing at most
  `(2^k y)^{−σ}`, and the geometric series `∑_k 2^{−k/log y}` sums to at most
  `2 log y / log 2`. The prime-counting saving is essential — over all integers the
  tail diverges like `log y`.

This is the last analytic ingredient for the truncation step: it lets the Euler-product
log bridge (W2a) be cut at `y` with `O(1)` loss.
-/

namespace MoltResearch

open Finset

/-- **Chebyshev's θ-bound**: `∑_{p < y} log p ≤ y log 4`, from `primorial ≤ 4^n`. -/
theorem sum_log_primesBelow_le (y : ℕ) :
    ∑ p ∈ y.primesBelow, Real.log p ≤ y * Real.log 4 := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [Nat.primesBelow_zero]
  have hprimes : y.primesBelow = {p ∈ Finset.range ((y - 1) + 1) | p.Prime} := by
    rw [Nat.primesBelow, Nat.sub_add_cancel hy]
  have hprod : ∑ p ∈ y.primesBelow, Real.log p = Real.log (primorial (y - 1)) := by
    rw [hprimes, primorial]
    rw [← Real.log_prod (fun p hp => by
      have hpp := (Finset.mem_filter.mp hp).2
      have : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      positivity)]
    congr 1
    push_cast
    rfl
  rw [hprod]
  calc Real.log (primorial (y - 1))
      ≤ Real.log ((4 : ℕ) ^ (y - 1) : ℕ) := by
        refine Real.log_le_log (by exact_mod_cast primorial_pos (y - 1)) ?_
        exact_mod_cast primorial_le_4_pow (y - 1)
    _ = (y - 1 : ℕ) * Real.log 4 := by
        push_cast
        rw [Real.log_pow]
    _ ≤ y * Real.log 4 := by
        have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        have : ((y - 1 : ℕ) : ℝ) ≤ y := by exact_mod_cast Nat.sub_le y 1
        nlinarith

/-- Dyadic block count: at most `2a log 4 / log a` primes in `[a, 2a)`. -/
private theorem card_primes_Ico_le {a : ℕ} (ha : 2 ≤ a) :
    (((2 * a).primesBelow.filter (fun p => a ≤ p)).card : ℝ) * Real.log a
      ≤ 2 * a * Real.log 4 := by
  set B := (2 * a).primesBelow.filter (fun p => a ≤ p) with hB
  have hloga : (0 : ℝ) ≤ Real.log a := Real.log_nonneg (by exact_mod_cast by omega)
  calc (B.card : ℝ) * Real.log a
      = ∑ _p ∈ B, Real.log a := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ B, Real.log p := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [hB, Finset.mem_filter] at hp
        refine Real.log_le_log (by exact_mod_cast by omega) ?_
        exact_mod_cast hp.2
    _ ≤ ∑ p ∈ (2 * a).primesBelow, Real.log p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun p hp _ => ?_
        have hpp := Nat.prime_of_mem_primesBelow hp
        exact Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    _ ≤ (2 * a : ℕ) * Real.log 4 := sum_log_primesBelow_le (2 * a)
    _ = 2 * a * Real.log 4 := by push_cast; ring

/-- Finite geometric bound (local copy): `∑_{k∈s} r^k ≤ 1/(1−r)` on `[0,1)`. -/
private theorem sum_pow_le_one_div {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : Finset ℕ) : ∑ k ∈ s, r ^ k ≤ 1 / (1 - r) := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  obtain ⟨K, hK⟩ : ∃ K, ∀ k ∈ s, k < K :=
    ⟨s.sup id + 1, fun k hk => Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)⟩
  calc ∑ k ∈ s, r ^ k
      ≤ ∑ k ∈ Finset.range K, r ^ k := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (fun k hk => Finset.mem_range.mpr (hK k hk)) fun k _ _ => by positivity
    _ ≤ 1 / (1 - r) := by
        have h := geom_sum_mul r K
        have hpow : (0 : ℝ) ≤ r ^ K := by positivity
        rw [le_div_iff₀ h1r]
        nlinarith

/-- **The prime tail estimate**: at `σ = 1 + 1/log y`, the tail `∑_{p ≥ y} p^{−σ}`
is at most `8` — the prime-counting saving via Chebyshev makes it `O(1)` where the
integer tail would diverge. -/
theorem tsum_primes_tail_rpow_le {y : ℕ} (hy : 3 ≤ y) :
    ∑' p : Nat.Primes,
        (if y ≤ (p : ℕ) then ((p : ℕ) : ℝ) ^ (-(1 + 1 / Real.log y)) else 0) ≤ 8 := by
  classical
  set ε : ℝ := 1 / Real.log y with hε
  have hlogy : (1 : ℝ) < Real.log y := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have h3 : (3 : ℝ) ≤ y := by exact_mod_cast hy
    linarith [Real.exp_one_lt_d9]
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε1 : ε < 1 := by
    rw [hε, div_lt_one (by linarith)]
    exact hlogy
  -- the per-finite-set bound
  refine Real.tsum_le_of_sum_le (fun p => by positivity) fun S => ?_
  -- restrict to the support and group by dyadic block
  set f : Nat.Primes → ℝ :=
    fun p => if y ≤ (p : ℕ) then ((p : ℕ) : ℝ) ^ (-(1 + ε)) else 0 with hf
  set T := S.filter (fun p : Nat.Primes => y ≤ (p : ℕ)) with hT
  have hsplit : ∑ p ∈ S, f p = ∑ p ∈ T, f p := by
    rw [hT]
    rw [← Finset.sum_filter_add_sum_filter_not S (fun p : Nat.Primes => y ≤ (p : ℕ)) f]
    have hz : ∑ p ∈ S.filter (fun p : Nat.Primes => ¬ y ≤ (p : ℕ)), f p = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [Finset.mem_filter] at hp
      rw [hf]
      simp only [if_neg hp.2]
    rw [hz, add_zero]
  rw [hsplit]
  -- the dyadic index
  set κ : Nat.Primes → ℕ := fun p => Nat.log 2 ((p : ℕ) / y) with hκ
  -- fiberwise decomposition
  have hgroup : ∑ k ∈ T.image κ, ∑ p ∈ T.filter (fun p => κ p = k), f p
      = ∑ p ∈ T, f p :=
    Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem κ hp) f
  rw [← hgroup]
  -- per-fiber facts
  have hy0 : (0 : ℕ) < y := by omega
  have hblockmem : ∀ k, ∀ p ∈ T.filter (fun p => κ p = k),
      2 ^ k * y ≤ (p : ℕ) ∧ (p : ℕ) < 2 * (2 ^ k * y) := by
    intro k p hp
    rw [Finset.mem_filter, hT, Finset.mem_filter] at hp
    obtain ⟨⟨-, hyp⟩, hkp⟩ := hp
    have hdiv1 : 1 ≤ (p : ℕ) / y := (Nat.one_le_div_iff hy0).mpr hyp
    constructor
    · have hpow : 2 ^ k ≤ (p : ℕ) / y := by
        rw [← hkp]
        exact Nat.pow_log_le_self 2 (by omega)
      calc 2 ^ k * y ≤ ((p : ℕ) / y) * y := Nat.mul_le_mul_right y hpow
        _ ≤ (p : ℕ) := Nat.div_mul_le_self _ y
    · have hlt : (p : ℕ) / y < 2 ^ (k + 1) := by
        rw [← hkp]
        exact Nat.lt_pow_succ_log_self (by norm_num) _
      have hmod := Nat.div_add_mod (p : ℕ) y
      have hmlt : (p : ℕ) % y < y := Nat.mod_lt _ hy0
      calc (p : ℕ) = y * ((p : ℕ) / y) + (p : ℕ) % y := hmod.symm
        _ = ((p : ℕ) / y) * y + (p : ℕ) % y := by ring
        _ < ((p : ℕ) / y) * y + y := by omega
        _ = ((p : ℕ) / y + 1) * y := by ring
        _ ≤ 2 ^ (k + 1) * y := Nat.mul_le_mul_right y (by omega)
        _ = 2 * (2 ^ k * y) := by ring
  -- the fiber sums against the block counts
  have hfiber : ∀ k, ∑ p ∈ T.filter (fun p => κ p = k), f p
      ≤ (2 * Real.log 4 / Real.log y) * ((2 : ℝ) ^ (-ε)) ^ k := by
    intro k
    set a : ℕ := 2 ^ k * y with ha
    have ha2 : (2 : ℕ) ≤ a := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      calc (2 : ℕ) ≤ y := by omega
        _ = 1 * y := (one_mul y).symm
        _ ≤ 2 ^ k * y := Nat.mul_le_mul_right y this
    have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
    have ha0 : (0 : ℝ) < a := by linarith
    -- the fiber injects into the ℕ-block
    set B := (2 * a).primesBelow.filter (fun q => a ≤ q) with hBdef
    have hcard : (T.filter (fun p => κ p = k)).card ≤ B.card := by
      refine Finset.card_le_card_of_injOn (fun p => (p : ℕ)) ?_ ?_
      · intro p hp
        have hp' : p ∈ T.filter (fun p => κ p = k) := hp
        obtain ⟨hge, hlt⟩ := hblockmem k p hp'
        refine Finset.mem_coe.mpr ?_
        rw [hBdef, Finset.mem_filter, Nat.mem_primesBelow]
        exact ⟨⟨hlt, p.prop⟩, hge⟩
      · intro p _ q _ h
        exact Subtype.ext h
    -- each fiber term is at most a^{-(1+ε)}
    have hterm : ∀ p ∈ T.filter (fun p => κ p = k),
        f p ≤ (a : ℝ) ^ (-(1 + ε)) := by
      intro p hp
      obtain ⟨hge, -⟩ := hblockmem k p hp
      have hgeR : (a : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hge
      have hyp : y ≤ (p : ℕ) := by
        rw [Finset.mem_filter, hT, Finset.mem_filter] at hp
        exact hp.1.2
      rw [hf]
      simp only [if_pos hyp]
      -- antitone base at negative exponent, via reciprocals
      have h1 : (a : ℝ) ^ (-(1 + ε)) = 1 / (a : ℝ) ^ (1 + ε) := by
        rw [Real.rpow_neg ha0.le, one_div]
      have h2 : ((p : ℕ) : ℝ) ^ (-(1 + ε)) = 1 / ((p : ℕ) : ℝ) ^ (1 + ε) := by
        rw [Real.rpow_neg (by linarith), one_div]
      rw [h1, h2]
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact Real.rpow_le_rpow ha0.le hgeR (by linarith)
    have hsumfiber : ∑ p ∈ T.filter (fun p => κ p = k), f p
        ≤ (B.card : ℝ) * (a : ℝ) ^ (-(1 + ε)) := by
      calc ∑ p ∈ T.filter (fun p => κ p = k), f p
          ≤ ((T.filter (fun p => κ p = k)).card : ℝ) * (a : ℝ) ^ (-(1 + ε)) := by
            have := Finset.sum_le_card_nsmul _ _ _ hterm
            rwa [nsmul_eq_mul] at this
        _ ≤ (B.card : ℝ) * (a : ℝ) ^ (-(1 + ε)) := by
            have : ((T.filter (fun p => κ p = k)).card : ℝ) ≤ (B.card : ℝ) := by
              exact_mod_cast hcard
            have hpos : (0 : ℝ) ≤ (a : ℝ) ^ (-(1 + ε)) := by positivity
            nlinarith
    -- Chebyshev block count
    have hya : (y : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_left y (Nat.two_pow_pos k)
    have hloga : (1 : ℝ) < Real.log a := by
      calc (1 : ℝ) < Real.log y := hlogy
        _ ≤ Real.log a := Real.log_le_log (by exact_mod_cast hy0) hya
    have hcount := card_primes_Ico_le (a := a) ha2
    have hcardB : (B.card : ℝ) ≤ 2 * a * Real.log 4 / Real.log y := by
      rw [← hBdef] at hcount
      have h1 : (B.card : ℝ) ≤ 2 * a * Real.log 4 / Real.log a := by
        rw [le_div_iff₀ (by linarith)]
        exact hcount
      refine le_trans h1 ?_
      have hlog4 : (0 : ℝ) ≤ 2 * a * Real.log 4 := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
        positivity
      exact div_le_div_of_nonneg_left hlog4 (by linarith)
        (Real.log_le_log (by exact_mod_cast hy0) hya)
    -- combine: card · a^{-(1+ε)} ≤ (2 log4 / log y) · a^{-ε}
    have hrpow_split : (a : ℝ) * (a : ℝ) ^ (-(1 + ε)) = (a : ℝ) ^ (-ε) := by
      rw [show (a : ℝ) * (a : ℝ) ^ (-(1 + ε))
          = (a : ℝ) ^ (1 : ℝ) * (a : ℝ) ^ (-(1 + ε)) from by rw [Real.rpow_one],
        ← Real.rpow_add ha0]
      ring_nf
    have hstep : (B.card : ℝ) * (a : ℝ) ^ (-(1 + ε))
        ≤ (2 * Real.log 4 / Real.log y) * (a : ℝ) ^ (-ε) := by
      have hpos : (0 : ℝ) ≤ (a : ℝ) ^ (-(1 + ε)) := by positivity
      calc (B.card : ℝ) * (a : ℝ) ^ (-(1 + ε))
          ≤ (2 * a * Real.log 4 / Real.log y) * (a : ℝ) ^ (-(1 + ε)) := by nlinarith
        _ = (2 * Real.log 4 / Real.log y) * ((a : ℝ) * (a : ℝ) ^ (-(1 + ε))) := by ring
        _ = (2 * Real.log 4 / Real.log y) * (a : ℝ) ^ (-ε) := by rw [hrpow_split]
    -- a^{-ε} ≤ (2^{-ε})^k (dropping y^{-ε} ≤ 1)
    have hgeo : (a : ℝ) ^ (-ε) ≤ ((2 : ℝ) ^ (-ε)) ^ k := by
      have hcast : (a : ℝ) = (2 : ℝ) ^ (k : ℕ) * (y : ℝ) := by
        rw [ha]; push_cast; ring
      rw [hcast, Real.mul_rpow (by positivity) (by exact_mod_cast hy0.le)]
      have hyfac : (y : ℝ) ^ (-ε) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hy0) (by linarith)
      have h2fac : ((2 : ℝ) ^ (k : ℕ)) ^ (-ε) = ((2 : ℝ) ^ (-ε)) ^ k := by
        rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num),
          mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
      have hpos2 : (0 : ℝ) ≤ ((2 : ℝ) ^ (k : ℕ)) ^ (-ε) := by positivity
      calc ((2 : ℝ) ^ (k : ℕ)) ^ (-ε) * (y : ℝ) ^ (-ε)
          ≤ ((2 : ℝ) ^ (k : ℕ)) ^ (-ε) * 1 := by
            have hy0R : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy0.le
            nlinarith [Real.rpow_nonneg hy0R (-ε)]
        _ = ((2 : ℝ) ^ (-ε)) ^ k := by rw [mul_one, h2fac]
    have hcoef : (0 : ℝ) ≤ 2 * Real.log 4 / Real.log y := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      positivity
    calc ∑ p ∈ T.filter (fun p => κ p = k), f p
        ≤ (B.card : ℝ) * (a : ℝ) ^ (-(1 + ε)) := hsumfiber
      _ ≤ (2 * Real.log 4 / Real.log y) * (a : ℝ) ^ (-ε) := hstep
      _ ≤ (2 * Real.log 4 / Real.log y) * ((2 : ℝ) ^ (-ε)) ^ k := by
          have hpos : (0 : ℝ) ≤ (a : ℝ) ^ (-ε) := by positivity
          nlinarith
  -- geometric series over the dyadic indices
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-ε) := by positivity
  have hr1 : (2 : ℝ) ^ (-ε) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeosum : ∑ k ∈ T.image κ, ((2 : ℝ) ^ (-ε)) ^ k
      ≤ 1 / (1 - (2 : ℝ) ^ (-ε)) := sum_pow_le_one_div hr0 hr1 _
  -- 1/(1 − 2^{-ε}) ≤ 2 log y / log 2
  have hlb : ε * Real.log 2 / 2 ≤ 1 - (2 : ℝ) ^ (-ε) := by
    have hx : (0 : ℝ) < ε * Real.log 2 := by
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      positivity
    have hx1 : ε * Real.log 2 ≤ 1 := by
      have hl2 : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        linarith [Real.exp_one_gt_d9]
      nlinarith
    have hexp : (2 : ℝ) ^ (-ε) = Real.exp (-(ε * Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
      ring_nf
    have hexple : Real.exp (-(ε * Real.log 2)) ≤ 1 / (1 + ε * Real.log 2) := by
      rw [Real.exp_neg, inv_eq_one_div]
      refine one_div_le_one_div_of_le (by linarith) ?_
      linarith [Real.add_one_le_exp (ε * Real.log 2)]
    rw [hexp]
    have h2 : 1 / (1 + ε * Real.log 2) ≤ 1 - ε * Real.log 2 / 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hfin : 1 / (1 - (2 : ℝ) ^ (-ε)) ≤ 2 * Real.log y / Real.log 2 := by
    have hd : (0 : ℝ) < ε * Real.log 2 / 2 := by
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      positivity
    calc 1 / (1 - (2 : ℝ) ^ (-ε))
        ≤ 1 / (ε * Real.log 2 / 2) := one_div_le_one_div_of_le hd hlb
      _ = 2 / (ε * Real.log 2) := by ring
      _ = 2 * Real.log y / Real.log 2 := by
          rw [hε]
          have : Real.log y ≠ 0 := by linarith
          field_simp
  -- assemble
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
    push_cast
    ring
  calc ∑ k ∈ T.image κ, ∑ p ∈ T.filter (fun p => κ p = k), f p
      ≤ ∑ k ∈ T.image κ, (2 * Real.log 4 / Real.log y) * ((2 : ℝ) ^ (-ε)) ^ k :=
        Finset.sum_le_sum fun k _ => hfiber k
    _ = (2 * Real.log 4 / Real.log y) * ∑ k ∈ T.image κ, ((2 : ℝ) ^ (-ε)) ^ k := by
        rw [Finset.mul_sum]
    _ ≤ (2 * Real.log 4 / Real.log y) * (2 * Real.log y / Real.log 2) := by
        have hcoef : (0 : ℝ) ≤ 2 * Real.log 4 / Real.log y := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
          positivity
        have hle := le_trans hgeosum hfin
        have hsum0 : (0 : ℝ) ≤ ∑ k ∈ T.image κ, ((2 : ℝ) ^ (-ε)) ^ k :=
          Finset.sum_nonneg fun k _ => pow_nonneg hr0 k
        nlinarith
    _ = 8 := by
        rw [hlog4]
        have hly : Real.log y ≠ 0 := by linarith
        field_simp
        ring

/-- Per-block prime mass: `∑_{T ≤ p < 2T} 1/p ≤ 3/log T` for `T ≥ 2`
— Chebyshev's θ-bound spent once per dyadic block. -/
theorem sum_one_div_primes_block_le (T : ℕ) (hT : 2 ≤ T) :
    ∑ p ∈ (2*T).primesBelow \ T.primesBelow, (1:ℝ)/p
      ≤ 3 / Real.log T := by
  classical
  have hT0 : (0:ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hlogT : (0:ℝ) < Real.log T := by
    refine Real.log_pos ?_
    exact_mod_cast (by omega : 1 < T)
  have hpt : ∀ p ∈ (2*T).primesBelow \ T.primesBelow,
      (1:ℝ)/p ≤ (Real.log p / p) / Real.log T := by
    intro p hp
    rw [Finset.mem_sdiff, Nat.mem_primesBelow] at hp
    have hpT : T ≤ p := by
      by_contra h
      exact hp.2 (Nat.mem_primesBelow.mpr ⟨by omega, hp.1.2⟩)
    have hp0 : (0:ℝ) < p := by
      exact_mod_cast hp.1.2.pos
    have hlogp : Real.log T ≤ Real.log p :=
      Real.log_le_log hT0 (by exact_mod_cast hpT)
    rw [div_div, div_le_div_iff₀ hp0 (by positivity)]
    calc (1:ℝ) * (p * Real.log T) = p * Real.log T := by ring
      _ ≤ p * Real.log p := mul_le_mul_of_nonneg_left hlogp hp0.le
      _ = Real.log p * p := by ring
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [← Finset.sum_div]
  gcongr
  have hpt2 : ∀ p ∈ (2*T).primesBelow \ T.primesBelow,
      Real.log p / p ≤ Real.log p / T := by
    intro p hp
    rw [Finset.mem_sdiff, Nat.mem_primesBelow] at hp
    have hpT : T ≤ p := by
      by_contra h
      exact hp.2 (Nat.mem_primesBelow.mpr ⟨by omega, hp.1.2⟩)
    have hlogp0 : 0 ≤ Real.log p :=
      Real.log_nonneg (by exact_mod_cast hp.1.2.one_lt.le)
    exact div_le_div_of_nonneg_left hlogp0 hT0 (by exact_mod_cast hpT)
  refine le_trans (Finset.sum_le_sum hpt2) ?_
  rw [← Finset.sum_div]
  have hθ : ∑ p ∈ (2*T).primesBelow \ T.primesBelow, Real.log p
      ≤ (2*T : ℕ) * Real.log 4 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.sdiff_subset) ?_) ?_
    · intro p hp _
      have hpp := Nat.prime_of_mem_primesBelow hp
      exact Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    · exact sum_log_primesBelow_le (2*T)
  rw [div_le_iff₀ hT0]
  calc ∑ p ∈ (2*T).primesBelow \ T.primesBelow, Real.log p
      ≤ (2*T : ℕ) * Real.log 4 := hθ
    _ ≤ 3 * T := by
        push_cast
        have h4 : Real.log 4 ≤ 1.4 := by
          rw [show (4:ℝ) = 2^2 from by norm_num, Real.log_pow]
          have := Real.log_two_lt_d9
          push_cast
          linarith
        nlinarith

/-- The harmonic telescope: `∑_{j<J} 1/(c+j) ≤ log(c+J−1) − log(c−1)`
for real `c ≥ 2` — each term is a log increment. -/
theorem sum_one_div_add_le_log (c : ℝ) (hc : 2 ≤ c) (J : ℕ) :
    ∑ j ∈ Finset.range J, 1/(c + j)
      ≤ Real.log (c + J - 1) - Real.log (c - 1) := by
  induction J with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have ht : (0:ℝ) < c + k := by positivity
    have ht1 : (0:ℝ) < c + k - 1 := by
      have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      linarith
    have hstep : 1/(c + k) ≤ Real.log (c + k) - Real.log (c + k - 1) := by
      have hfact : c + k - 1 = (c + k) * (1 - 1/(c + k)) := by
        field_simp
      have hin0 : (0:ℝ) < 1 - 1/(c + k) := by
        have h1 : 1/(c + k) < 1 := by
          rw [div_lt_one ht]
          have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
          linarith
        linarith
      have hlogm : Real.log (c + k - 1)
          = Real.log (c + k) + Real.log (1 - 1/(c + k)) := by
        rw [hfact, Real.log_mul (by positivity) (by linarith)]
      have hsmall : Real.log (1 - 1/(c + k)) ≤ -(1/(c + k)) := by
        have := Real.log_le_sub_one_of_pos hin0
        linarith
      rw [hlogm]
      linarith
    push_cast
    push_cast at ih
    rw [show c + ((k:ℝ) + 1) - 1 = c + k from by ring]
    linarith [hstep, ih]


/-- **The Mertens mass difference** (Track R, M2-h3): the prime
harmonic mass between truncations `4 ≤ y ≤ x` is at most
`5·(loglog x − loglog y) + 15` — dyadic Chebyshev blocks against the
harmonic telescope. The loglog-quality transfer that makes the
distance-floor scale change affordable. -/
theorem mass_diff_le (y x : ℕ) (hy : 4 ≤ y) (hyx : y ≤ x) :
    (∑ p ∈ x.primesBelow, (1:ℝ)/p) - (∑ p ∈ y.primesBelow, (1:ℝ)/p)
      ≤ 5 * (Real.log (Real.log x) - Real.log (Real.log y)) + 15 := by
  classical
  set J : ℕ := Nat.log 2 x + 1 with hJ_def
  have hysub : y.primesBelow ⊆ x.primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hdiff_eq : (∑ p ∈ x.primesBelow, (1:ℝ)/p)
        - (∑ p ∈ y.primesBelow, (1:ℝ)/p)
      = ∑ p ∈ x.primesBelow \ y.primesBelow, (1:ℝ)/(p:ℝ) :=
    (Finset.sum_sdiff_eq_sub hysub).symm
  rw [hdiff_eq]
  have hcover : x.primesBelow \ y.primesBelow
      ⊆ (Finset.range J).biUnion
          (fun j => (y*2^(j+1)).primesBelow \ (y*2^j).primesBelow) := by
    intro p hp
    rw [Finset.mem_sdiff, Nat.mem_primesBelow] at hp
    have hpy : y ≤ p := by
      by_contra h
      exact hp.2 (Nat.mem_primesBelow.mpr ⟨by omega, hp.1.2⟩)
    have hp0 : 0 < p := hp.1.2.pos
    set j : ℕ := Nat.log 2 (p/y) with hj_def
    have hy0 : 0 < y := by omega
    have hlow : y*2^j ≤ p := by
      have h1 : 2^j ≤ p/y := Nat.pow_log_le_self 2 (by
        have : 1 ≤ p/y := (Nat.one_le_div_iff hy0).mpr hpy
        omega)
      calc y*2^j ≤ y*(p/y) := Nat.mul_le_mul_left y h1
        _ ≤ p := Nat.mul_div_le p y
    have hhigh : p < y*2^(j+1) := by
      have h1 : p/y < 2^(j+1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have h2 : p < y*(p/y) + y := by
        have := Nat.div_add_mod p y
        have hmod := Nat.mod_lt p hy0
        omega
      have h3 : y*(p/y) + y = y*(p/y + 1) := by ring
      calc p < y*(p/y) + y := h2
        _ = y*(p/y + 1) := h3
        _ ≤ y*2^(j+1) := Nat.mul_le_mul_left y (by omega)
    have hjJ : j < J := by
      rw [hJ_def, hj_def]
      have h1 : Nat.log 2 (p/y) ≤ Nat.log 2 p :=
        Nat.log_mono_right (Nat.div_le_self p y)
      have h2 : Nat.log 2 p ≤ Nat.log 2 x :=
        Nat.log_mono_right (by omega)
      omega
    rw [Finset.mem_biUnion]
    refine ⟨j, Finset.mem_range.mpr hjJ, ?_⟩
    rw [Finset.mem_sdiff, Nat.mem_primesBelow]
    refine ⟨⟨hhigh, hp.1.2⟩, ?_⟩
    intro hmem
    rw [Nat.mem_primesBelow] at hmem
    omega
  have hdisj_aux : ∀ j k : ℕ, j < k →
      Disjoint ((y*2^(j+1)).primesBelow \ (y*2^j).primesBelow)
        ((y*2^(k+1)).primesBelow \ (y*2^k).primesBelow) := by
    intro j k hjk
    refine Finset.disjoint_left.mpr fun p hpj hpk => ?_
    rw [Finset.mem_sdiff, Nat.mem_primesBelow] at hpj hpk
    have h1 : p < y*2^(j+1) := hpj.1.1
    have h2 : y*2^k ≤ p := by
      by_contra h
      exact hpk.2 (Nat.mem_primesBelow.mpr ⟨by omega, hpk.1.2⟩)
    have h3 : y*2^(j+1) ≤ y*2^k :=
      Nat.mul_le_mul_left y (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  have hdisj : Set.PairwiseDisjoint ↑(Finset.range J)
      (fun j => (y*2^(j+1)).primesBelow \ (y*2^j).primesBelow) := by
    intro j _ k _ hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact hdisj_aux j k h
    · exact (hdisj_aux k j h).symm
  have hnonneg : ∀ p : ℕ, (0:ℝ) ≤ 1/(p:ℝ) := fun p => by positivity
  have hblocks : ∑ p ∈ x.primesBelow \ y.primesBelow, (1:ℝ)/(p:ℝ)
      ≤ ∑ j ∈ Finset.range J,
          ∑ p ∈ (y*2^(j+1)).primesBelow \ (y*2^j).primesBelow,
            (1:ℝ)/(p:ℝ) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hcover
      (fun p _ _ => hnonneg p)) ?_
    rw [Finset.sum_biUnion hdisj]
  refine le_trans hblocks ?_
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lb : (0.6:ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog2_ub : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  set c : ℝ := Real.log y / Real.log 2 with hc_def
  have hlogy_lb : 2 * Real.log 2 ≤ Real.log y := by
    have h4 : Real.log 4 ≤ Real.log y :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hy)
    rw [show (4:ℝ) = 2^2 from by norm_num, Real.log_pow] at h4
    push_cast at h4
    linarith
  have hc2 : 2 ≤ c := by
    rw [hc_def, le_div_iff₀ hlog2pos]
    linarith
  have hperblock : ∀ j ∈ Finset.range J,
      ∑ p ∈ (y*2^(j+1)).primesBelow \ (y*2^j).primesBelow, (1:ℝ)/(p:ℝ)
        ≤ (3/Real.log 2) * (1/(c + j)) := by
    intro j _
    have h2j : (1:ℕ) ≤ 2^j := Nat.one_le_pow j 2 (by norm_num)
    have hT4 : 2 ≤ y*2^j := by nlinarith
    have hblock := sum_one_div_primes_block_le (y*2^j) hT4
    have heq : 2*(y*2^j) = y*2^(j+1) := by ring
    rw [heq] at hblock
    refine le_trans hblock ?_
    have hcj0 : (0:ℝ) < c + j := by
      have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      linarith
    have hlogT : Real.log ((y*2^j : ℕ):ℝ) = Real.log 2 * (c + j) := by
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
        hc_def]
      field_simp
    rw [hlogT]
    rw [show (3:ℝ)/(Real.log 2 * (c+j)) = (3/Real.log 2)*(1/(c+j)) from by
      rw [div_mul_div_comm, mul_one]]
  refine le_trans (Finset.sum_le_sum hperblock) ?_
  rw [← Finset.mul_sum]
  have htel := sum_one_div_add_le_log c hc2 J
  -- endpoints
  have hlogx_pos : (0:ℝ) < Real.log x := by
    refine Real.log_pos ?_
    have : (4:ℝ) ≤ x := by exact_mod_cast (by omega : 4 ≤ x)
    linarith
  have hlogy_pos : (0:ℝ) < Real.log y := by linarith
  have hJlog : ((J:ℝ) - 1) * Real.log 2 ≤ Real.log x := by
    rw [hJ_def]
    push_cast
    have h1 : (2:ℕ)^(Nat.log 2 x) ≤ x := Nat.pow_log_le_self 2 (by omega)
    have h2 : Real.log ((2:ℕ)^(Nat.log 2 x) : ℕ) ≤ Real.log x :=
      Real.log_le_log (by positivity) (by exact_mod_cast h1)
    rw [show (((2:ℕ)^(Nat.log 2 x) : ℕ):ℝ) = (2:ℝ)^(Nat.log 2 x) from by
      push_cast; ring] at h2
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hupper : c + J - 1 ≤ 4 * Real.log x := by
    have h1 : c ≤ Real.log x / Real.log 2 := by
      rw [hc_def, div_le_div_iff₀ hlog2pos hlog2pos]
      have := Real.log_le_log (by positivity : (0:ℝ) < y)
        (by exact_mod_cast hyx : (y:ℝ) ≤ x)
      nlinarith
    have h2 : (J:ℝ) - 1 ≤ Real.log x / Real.log 2 := by
      rw [le_div_iff₀ hlog2pos]
      linarith
    have h3 : Real.log x / Real.log 2 ≤ 2 * Real.log x := by
      rw [div_le_iff₀ hlog2pos]
      nlinarith
    linarith
  have hlower : Real.log y / 2 ≤ c - 1 := by
    rw [hc_def, le_sub_iff_add_le, le_div_iff₀ hlog2pos]
    nlinarith [hlogy_lb, hlog2_ub, hlog2pos]
  have hcJ1_pos : (0:ℝ) < c + J - 1 := by
    have hJ1 : (1:ℝ) ≤ (J:ℝ) := by
      rw [hJ_def]
      push_cast
      have : (0:ℝ) ≤ (Nat.log 2 x : ℝ) := Nat.cast_nonneg _
      linarith
    linarith
  have hsum_nonneg : (0:ℝ) ≤ ∑ j ∈ Finset.range J, 1/(c + (j:ℝ)) := by
    refine Finset.sum_nonneg fun j _ => ?_
    have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    positivity
  have h35 : 3/Real.log 2 ≤ 5 := by
    rw [div_le_iff₀ hlog2pos]
    linarith
  have hlog_up : Real.log (c + J - 1) ≤ Real.log (Real.log x) + 2 := by
    have h1 : Real.log (c + J - 1) ≤ Real.log (4 * Real.log x) :=
      Real.log_le_log hcJ1_pos hupper
    rw [Real.log_mul (by norm_num) (ne_of_gt hlogx_pos)] at h1
    have h4 : Real.log 4 ≤ 2 := by
      rw [show (4:ℝ) = 2^2 from by norm_num, Real.log_pow]
      push_cast
      linarith
    linarith
  have hlog_low : Real.log (Real.log y) - 1 ≤ Real.log (c - 1) := by
    have h1 : Real.log (Real.log y / 2) ≤ Real.log (c - 1) :=
      Real.log_le_log (by positivity) hlower
    rw [Real.log_div (ne_of_gt hlogy_pos) (by norm_num)] at h1
    linarith
  have hΔ : ∑ j ∈ Finset.range J, 1/(c + (j:ℝ))
      ≤ (Real.log (Real.log x) - Real.log (Real.log y)) + 3 := by
    calc ∑ j ∈ Finset.range J, 1/(c + (j:ℝ))
        ≤ Real.log (c + J - 1) - Real.log (c - 1) := htel
      _ ≤ (Real.log (Real.log x) + 2) - (Real.log (Real.log y) - 1) := by
          linarith
      _ = (Real.log (Real.log x) - Real.log (Real.log y)) + 3 := by ring
  calc (3/Real.log 2) * ∑ j ∈ Finset.range J, 1/(c + (j:ℝ))
      ≤ 5 * ∑ j ∈ Finset.range J, 1/(c + (j:ℝ)) :=
        mul_le_mul_of_nonneg_right h35 hsum_nonneg
    _ ≤ 5 * ((Real.log (Real.log x) - Real.log (Real.log y)) + 3) := by
        refine mul_le_mul_of_nonneg_left hΔ (by norm_num)
    _ = 5 * (Real.log (Real.log x) - Real.log (Real.log y)) + 15 := by
        ring


end MoltResearch
