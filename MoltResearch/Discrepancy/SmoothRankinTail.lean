import MoltResearch.Discrepancy.ExceptionalHalaszSharp
import MoltResearch.Discrepancy.HalaszSharpEps

/-!
# The `P`-smooth Rankin tail, and the sharp Ramaré cost in `ε`-form

The exceptional-cell recut (`ExceptionalHalaszSharp`) charges a Ramaré
quotient `((A/n₁), (B/n₁)]` by the windowed sharp Halász cost when
`A/n₁ ≥ x₀` and by its harmonic mass otherwise.  The window is transferred
from the top scale `N` with the loss `2(loglog N − loglog u + 12)`, bounded
only for quotient scales `u ≥ N^{c}`; so the cutoff `x₀` is a power of `N`, and
the short quotients — `P`-smooth `n₁ > A/x₀` — must be shown negligible.
That is Rankin's trick for an arbitrary finite prime set `P`:

* `sum_pSmooth_rpow_le_prod` — `∑_{n ≤ B, P-smooth} n^{−s} ≤ ∏_{p∈P}(1 − p^{−s})^{−1}`
  for `s > 0` (the box-product argument of `pSmoothHarmonicMass_le_exp_primeMass`
  with the weight `n^{−s} = ∏ (p^{−s})^{e_p}`);
* `pSmooth_harmonic_tail_le` — `∑_{n ≤ B, P-smooth, n > y} 1/n ≤ y^{−s}·∏_{p∈P}(1 − p^{−(1−s)})^{−1}`
  for `0 < s < 1`, from `1/n = n^{−s}·n^{−(1−s)} ≤ y^{−s}·n^{−(1−s)}`;
* `prod_inv_one_sub_le_exp` — `∏(1 − r_p)^{−1} ≤ exp(2∑ r_p)` when every `r_p ≤ 1/2`;
* `sharpRamareCost_le_split`, `sharpRamareCost_le_eps` — the sharp Ramaré cost is at
  most `2ε·(P-smooth harmonic mass) + (log B + 1)·(A/x₀)^{−s}·∏(1 − p^{−(1−s)})^{−1}`
  once the block `ε`-form holds at the cutoff, with `D₀(ε), x₀(ε)` from
  `sharpTwistedDirichletCost_le_eps`.  With `s = 1/log Q` (all `p ∈ P` below `Q`) the
  product is `≤ exp(2e·∑_{p∈P} 1/p)` and the tail is `exp(−(1−c)·log A/log Q + 2e·E_P)·log B`,
  negligible whenever `log A ≫ log Q`.
-/

namespace MoltResearch

open Finset ExpSums

/-- **Rankin's majorization for an arbitrary prime set** (Track R, T0-7b): for
`s > 0`, `∑_{n ≤ B, P-smooth} n^{−s} ≤ ∏_{p ∈ P} (1 − p^{−s})^{−1}`. -/
theorem sum_pSmooth_rpow_le_prod (B : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (s : ℝ) (hs : 0 < s) :
    ∑ n ∈ (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P), (n:ℝ) ^ (-s)
      ≤ ∏ p ∈ P, (1 - (p:ℝ) ^ (-s))⁻¹ := by
  classical
  let S := (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P)
  let E := Nat.log 2 B + 1
  let F : ℕ → ({p // p ∈ P} → ℕ) := fun n p => n.factorization p.1
  have hrecon : ∀ n ∈ S, n = ∏ p : {p // p ∈ P}, p.1 ^ F n p := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hattach : (∏ p : {p // p ∈ P}, p.1 ^ F n p) =
        ∏ p ∈ P, p ^ n.factorization p := by
      change (∏ p ∈ (Finset.univ : Finset {p // p ∈ P}),
        p.1 ^ n.factorization p.1) = _
      rw [Finset.univ_eq_attach]
      exact Finset.prod_attach P (fun p => p ^ n.factorization p)
    rw [hattach]
    rw [show ∏ p ∈ P, p ^ n.factorization p =
        ∏ p ∈ n.primeFactors, p ^ n.factorization p from
      (Finset.prod_subset hn.2 fun p hpP hp => by
        have hfac0 : n.factorization p = 0 := by
          rw [← Finsupp.notMem_support_iff]
          simpa only [Nat.support_factorization] using hp
        rw [hfac0, pow_zero]).symm]
    exact (Nat.factorization_prod_pow_eq_self hn0).symm
  have hpow : ∀ (x : ℝ) (e : ℕ), 0 ≤ x → (x ^ e) ^ (-s) = (x ^ (-s)) ^ e := by
    intro x e hx
    rw [← Real.rpow_natCast x e, ← Real.rpow_mul hx, mul_comm, Real.rpow_mul hx,
      Real.rpow_natCast]
  have hval : ∀ n ∈ S, (n:ℝ) ^ (-s) = ∏ p : {p // p ∈ P}, ((p.1:ℝ) ^ (-s)) ^ F n p := by
    intro n hn
    have hcast : (n:ℝ) = ∏ p : {p // p ∈ P}, ((p.1:ℝ)) ^ F n p := by
      conv_lhs => rw [hrecon n hn]
      push_cast
      rfl
    rw [hcast, ← Real.finset_prod_rpow _ _ (fun p _ => by positivity)]
    exact Finset.prod_congr rfl fun p _ => hpow _ _ (by positivity)
  have hinj : Set.InjOn F S := by
    intro n hn m hm hnm
    rw [hrecon n hn, hrecon m hm]
    exact Finset.prod_congr rfl fun p hp => by rw [hnm]
  have himg : S.image F ⊆ Fintype.piFinset
      (fun _ : {p // p ∈ P} => Finset.range E) := by
    intro f hf
    rw [Finset.mem_image] at hf
    obtain ⟨n, hn, rfl⟩ := hf
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range]
    change n.factorization p.1 < Nat.log 2 B + 1
    rw [Nat.lt_succ_iff]
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    exact factorization_le_log hn.1.1 hn.1.2 p.1
  have hbox : ∑ n ∈ S, (n:ℝ) ^ (-s)
      ≤ ∏ p ∈ P, ∑ e ∈ Finset.range E, ((p:ℝ) ^ (-s)) ^ e := by
    calc
      ∑ n ∈ S, (n:ℝ) ^ (-s) =
          ∑ n ∈ S, ∏ p : {p // p ∈ P}, ((p.1:ℝ) ^ (-s)) ^ F n p :=
        Finset.sum_congr rfl hval
      _ = ∑ f ∈ S.image F, ∏ p : {p // p ∈ P}, ((p.1:ℝ) ^ (-s)) ^ f p := by
          rw [Finset.sum_image fun n hn m hm hnm => hinj hn hm hnm]
      _ ≤ ∑ f ∈ Fintype.piFinset (fun _ : {p // p ∈ P} => Finset.range E),
            ∏ p : {p // p ∈ P}, ((p.1:ℝ) ^ (-s)) ^ f p :=
          Finset.sum_le_sum_of_subset_of_nonneg himg
            (fun f hf hnf => Finset.prod_nonneg fun p hp => by positivity)
      _ = ∏ p ∈ P, ∑ e ∈ Finset.range E, ((p:ℝ) ^ (-s)) ^ e := by
          rw [← Finset.prod_attach P
            (fun p => ∑ e ∈ Finset.range E, ((p:ℝ) ^ (-s)) ^ e),
            show P.attach = Finset.univ from (Finset.univ_eq_attach P).symm,
            Finset.prod_univ_sum]
  refine hbox.trans ?_
  apply Finset.prod_le_prod₀
  · intro p hp
    exact Finset.sum_nonneg fun e he => by positivity
  · intro p hp
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hp0 : (0:ℝ) < p := by linarith
    have hr0 : (0:ℝ) ≤ (p:ℝ) ^ (-s) := by positivity
    have hr1 : (p:ℝ) ^ (-s) < 1 := by
      rw [Real.rpow_neg hp0.le, inv_lt_one₀ (Real.rpow_pos_of_pos hp0 s)]
      exact Real.one_lt_rpow (by linarith) hs
    have := sum_pow_le_one_div ((p:ℝ) ^ (-s)) hr0 hr1 E
    rwa [one_div] at this

/-- **The `P`-smooth harmonic tail** (Track R, T0-7b): for `0 < s < 1` and
`y > 0`, `∑_{n ≤ B, P-smooth, n > y} 1/n ≤ y^{−s} · ∏_{p ∈ P} (1 − p^{−(1−s)})^{−1}`. -/
theorem pSmooth_harmonic_tail_le (B : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (y : ℝ) (hy : 0 < y) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∑ n ∈ ((Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P)).filter
        (fun n : ℕ => y < (n:ℝ)), (1:ℝ) / n
      ≤ y ^ (-s) * ∏ p ∈ P, (1 - (p:ℝ) ^ (-(1 - s)))⁻¹ := by
  classical
  set S := (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P) with hS
  have hterm : ∀ n ∈ S.filter (fun n : ℕ => y < (n:ℝ)),
      (1:ℝ) / n ≤ y ^ (-s) * (n:ℝ) ^ (-(1 - s)) := by
    intro n hn
    obtain ⟨_, hyn⟩ := Finset.mem_filter.mp hn
    have hn0 : (0:ℝ) < n := lt_trans hy hyn
    have h1 : (1:ℝ) / n = (n:ℝ) ^ (-s) * (n:ℝ) ^ (-(1 - s)) := by
      rw [← Real.rpow_add hn0, show -s + -(1 - s) = (-1:ℝ) by ring, Real.rpow_neg_one,
        one_div]
    rw [h1]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [Real.rpow_neg hy.le, Real.rpow_neg hn0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hy s) (Real.rpow_le_rpow hy.le hyn.le hs0.le)
  calc ∑ n ∈ S.filter (fun n : ℕ => y < (n:ℝ)), (1:ℝ) / n
      ≤ ∑ n ∈ S.filter (fun n : ℕ => y < (n:ℝ)), y ^ (-s) * (n:ℝ) ^ (-(1 - s)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ S, y ^ (-s) * (n:ℝ) ^ (-(1 - s)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n _ _ => by positivity)
    _ = y ^ (-s) * ∑ n ∈ S, (n:ℝ) ^ (-(1 - s)) := by rw [Finset.mul_sum]
    _ ≤ y ^ (-s) * ∏ p ∈ P, (1 - (p:ℝ) ^ (-(1 - s)))⁻¹ :=
        mul_le_mul_of_nonneg_left (sum_pSmooth_rpow_le_prod B P hP (1 - s) (by linarith))
          (by positivity)

/-- **The finite Euler product against the exponential** (Track R, T0-7b):
`∏ (1 − r_p)^{−1} ≤ exp(2·∑ r_p)` when `0 ≤ r_p ≤ 1/2` for every `p`. -/
theorem prod_inv_one_sub_le_exp (P : Finset ℕ) (r : ℕ → ℝ)
    (hr0 : ∀ p ∈ P, 0 ≤ r p) (hr : ∀ p ∈ P, r p ≤ 1 / 2) :
    ∏ p ∈ P, (1 - r p)⁻¹ ≤ Real.exp (2 * ∑ p ∈ P, r p) := by
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p hp
    have := hr p hp
    have : 0 < 1 - r p := by linarith
    positivity
  · intro p hp
    have h0 := hr0 p hp
    have hh := hr p hp
    have h1 : 0 < 1 - r p := by linarith
    have hinv : (1 - r p)⁻¹ ≤ 1 + 2 * r p := by
      rw [inv_le_iff_one_le_mul₀ h1]
      nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ 1 - 2 * r p)]
    exact hinv.trans (by simpa only [add_comm] using Real.add_one_le_exp (2 * r p))

set_option maxHeartbeats 800000 in
/-- **The sharp Ramaré cost, split** (Track R, T0-7b): if every long block
(`x₀ ≤ a ≤ b ≤ 3a`) costs at most `ε·b/(a+1)`, then for `1 ≤ A ≤ B ≤ 2A+1`,

  `sharpRamareCost x₀ D δ₀ A B P ≤ 2ε·(P-smooth harmonic mass up to B)
     + (log B + 1)·(A/x₀)^{−s}·∏_{p∈P}(1 − p^{−(1−s)})^{−1}`

— the long quotients `x₀ ≤ A/n₁` have `B/n₁ ≤ 2(A/n₁)+1`, so each costs `≤ 2ε/n₁`;
the short quotients have `n₁ > A/x₀` and are charged `(log B + 1)/n₁`, whose
sum is the `P`-smooth Rankin tail. -/
theorem sharpRamareCost_le_split (x0 : ℕ) (hx0 : 1 ≤ x0) (D δ₀ : ℝ)
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) (hB : B ≤ 2 * A + 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (ε : ℝ) (hε : 0 ≤ ε)
    (hlong : ∀ a b : ℕ, x0 ≤ a → a ≤ b → b ≤ 3 * a →
      sharpTwistedDirichletCost D δ₀ a b ≤ ε * (b:ℝ) / ((a + 1 : ℕ):ℝ))
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    sharpRamareCost x0 D δ₀ A B P
      ≤ 2 * ε * pSmoothHarmonicMass B P
        + (Real.log (B:ℝ) + 1)
          * (((A:ℝ) / x0) ^ (-s) * ∏ p ∈ P, (1 - (p:ℝ) ^ (-(1 - s)))⁻¹) := by
  classical
  set S := (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P) with hS
  have hB1 : 1 ≤ B := le_trans hA hAB
  have hlogB : (0:ℝ) ≤ Real.log (B:ℝ) := Real.log_nonneg (by exact_mod_cast hB1)
  have hx0R : (0:ℝ) < (x0:ℝ) := by exact_mod_cast hx0
  have hAR : (0:ℝ) < (A:ℝ) := by exact_mod_cast hA
  have hy : (0:ℝ) < (A:ℝ) / x0 := by positivity
  -- membership facts
  have hmemS : ∀ n1 ∈ S, 1 ≤ n1 := by
    intro n1 hn1
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hn1
    exact hn1.1.1
  unfold sharpRamareCost
  rw [← Finset.sum_filter_add_sum_filter_not S (fun n1 => x0 ≤ A / n1)]
  -- the long quotients
  have hlongsum : ∑ n1 ∈ S.filter (fun n1 => x0 ≤ A / n1),
      (1 : ℝ) / n1 * sharpQuotientCost x0 D δ₀ (A / n1) (B / n1)
      ≤ 2 * ε * pSmoothHarmonicMass B P := by
    have hterm : ∀ n1 ∈ S.filter (fun n1 => x0 ≤ A / n1),
        (1 : ℝ) / n1 * sharpQuotientCost x0 D δ₀ (A / n1) (B / n1)
          ≤ (1 : ℝ) / n1 * (2 * ε) := by
      intro n1 hn1
      obtain ⟨hn1S, hcut⟩ := Finset.mem_filter.mp hn1
      have hn1pos : 0 < n1 := hmemS n1 hn1S
      have ha1 : 1 ≤ A / n1 := le_trans hx0 hcut
      have hab : A / n1 ≤ B / n1 := Nat.div_le_div_right hAB
      have hb2 : B / n1 ≤ 2 * (A / n1) + 1 := div_le_two_mul_div_add_one A B n1 hn1pos hB
      have hb3 : B / n1 ≤ 3 * (A / n1) := by
        generalize hd : A / n1 = d at ha1 hb2 ⊢
        omega
      have hcost := hlong (A / n1) (B / n1) hcut hab hb3
      have hratio : ε * ((B / n1 : ℕ):ℝ) / ((A / n1 + 1 : ℕ):ℝ) ≤ 2 * ε := by
        have hden : (0:ℝ) < ((A / n1 + 1 : ℕ):ℝ) := by positivity
        rw [div_le_iff₀ hden]
        have hb2R : ((B / n1 : ℕ):ℝ) ≤ 2 * ((A / n1 + 1 : ℕ):ℝ) := by
          have : ((B / n1 : ℕ):ℝ) ≤ ((2 * (A / n1) + 1 : ℕ):ℝ) := by exact_mod_cast hb2
          push_cast at this ⊢
          linarith
        nlinarith [mul_le_mul_of_nonneg_left hb2R hε]
      rw [sharpQuotientCost, if_pos hcut]
      exact mul_le_mul_of_nonneg_left (hcost.trans hratio) (by positivity)
    calc ∑ n1 ∈ S.filter (fun n1 => x0 ≤ A / n1),
          (1 : ℝ) / n1 * sharpQuotientCost x0 D δ₀ (A / n1) (B / n1)
        ≤ ∑ n1 ∈ S.filter (fun n1 => x0 ≤ A / n1), (1 : ℝ) / n1 * (2 * ε) :=
          Finset.sum_le_sum hterm
      _ = 2 * ε * ∑ n1 ∈ S.filter (fun n1 => x0 ≤ A / n1), (1 : ℝ) / n1 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n1 _ => by ring
      _ ≤ 2 * ε * ∑ n1 ∈ S, (1 : ℝ) / n1 :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun n _ _ => by positivity)) (by positivity)
      _ = 2 * ε * pSmoothHarmonicMass B P := by
          unfold pSmoothHarmonicMass
          rfl
  -- the short quotients
  have hshortsum : ∑ n1 ∈ S.filter (fun n1 => ¬ x0 ≤ A / n1),
      (1 : ℝ) / n1 * sharpQuotientCost x0 D δ₀ (A / n1) (B / n1)
      ≤ (Real.log (B:ℝ) + 1)
          * (((A:ℝ) / x0) ^ (-s) * ∏ p ∈ P, (1 - (p:ℝ) ^ (-(1 - s)))⁻¹) := by
    have hterm : ∀ n1 ∈ S.filter (fun n1 => ¬ x0 ≤ A / n1),
        (1 : ℝ) / n1 * sharpQuotientCost x0 D δ₀ (A / n1) (B / n1)
          ≤ (1 : ℝ) / n1 * (Real.log (B:ℝ) + 1) := by
      intro n1 hn1
      obtain ⟨hn1S, hcut⟩ := Finset.mem_filter.mp hn1
      rw [sharpQuotientCost, if_neg hcut]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      unfold cellHalaszTrivialCost
      -- `∑_{(A/n₁, B/n₁]} 1/n ≤ ∑_{n ≤ B/n₁} 1/n ≤ log(B/n₁) + 1 ≤ log B + 1`
      have hsub : Finset.Ioc (A / n1) (B / n1) ⊆ Finset.Icc 1 (B / n1) := by
        intro n hn
        rw [Finset.mem_Ioc] at hn
        rw [Finset.mem_Icc]
        generalize A / n1 = d at hn ⊢
        generalize B / n1 = f at hn ⊢
        omega
      have hmono : ∑ n ∈ Finset.Ioc (A / n1) (B / n1), (1 : ℝ) / n
          ≤ ∑ n ∈ Finset.Icc 1 (B / n1), (1 : ℝ) / n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
      rcases Nat.eq_zero_or_pos (B / n1) with hzero | hpos
      · rw [Finset.Ioc_eq_empty (by rw [hzero]; exact Nat.not_lt_zero _), Finset.sum_empty]
        linarith
      · have hlog := ExpSums.sum_one_div_Icc_le_log (B / n1) hpos
        have hdivB : ((B / n1 : ℕ):ℝ) ≤ (B:ℝ) := by exact_mod_cast Nat.div_le_self B n1
        have hlogmono : Real.log ((B / n1 : ℕ):ℝ) ≤ Real.log (B:ℝ) :=
          Real.log_le_log (by exact_mod_cast hpos) hdivB
        linarith
    have hsubset : S.filter (fun n1 => ¬ x0 ≤ A / n1)
        ⊆ S.filter (fun n : ℕ => (A:ℝ) / x0 < (n:ℝ)) := by
      intro n1 hn1
      obtain ⟨hn1S, hcut⟩ := Finset.mem_filter.mp hn1
      rw [Finset.mem_filter]
      refine ⟨hn1S, ?_⟩
      have hn1pos : 0 < n1 := hmemS n1 hn1S
      have hlt : A / n1 < x0 := Nat.lt_of_not_le hcut
      have hAx : A < x0 * n1 := (Nat.div_lt_iff_lt_mul hn1pos).mp hlt
      have hAxR : (A:ℝ) < (x0:ℝ) * n1 := by exact_mod_cast hAx
      rw [div_lt_iff₀ hx0R]
      linarith
    calc ∑ n1 ∈ S.filter (fun n1 => ¬ x0 ≤ A / n1),
          (1 : ℝ) / n1 * sharpQuotientCost x0 D δ₀ (A / n1) (B / n1)
        ≤ ∑ n1 ∈ S.filter (fun n1 => ¬ x0 ≤ A / n1),
            (1 : ℝ) / n1 * (Real.log (B:ℝ) + 1) := Finset.sum_le_sum hterm
      _ = (Real.log (B:ℝ) + 1) * ∑ n1 ∈ S.filter (fun n1 => ¬ x0 ≤ A / n1), (1 : ℝ) / n1 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n1 _ => by ring
      _ ≤ (Real.log (B:ℝ) + 1) * ∑ n1 ∈ S.filter (fun n : ℕ => (A:ℝ) / x0 < (n:ℝ)), (1 : ℝ) / n1 :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _ => by positivity))
            (by linarith)
      _ ≤ (Real.log (B:ℝ) + 1)
          * (((A:ℝ) / x0) ^ (-s) * ∏ p ∈ P, (1 - (p:ℝ) ^ (-(1 - s)))⁻¹) :=
          mul_le_mul_of_nonneg_left
            (pSmooth_harmonic_tail_le B P hP ((A:ℝ) / x0) hy s hs0 hs1) (by linarith)
  linarith [hlongsum, hshortsum]

/-- **The sharp Ramaré cost in `ε`-form** (Track R, T0-7b): for every `ε > 0`
there are a strength `D₀ ≥ 1` and a cutoff floor `x₀ ≥ 10¹⁶` such that, at
`δ₀ := ε/(8e)`, for every `D ≥ D₀`, every cutoff `x₀' ≥ x₀`, every
`1 ≤ A ≤ B ≤ 2A+1`, every finite prime set `P` and every `0 < s < 1`,

  `sharpRamareCost x₀' D (ε/(8e)) A B P ≤ 2ε·(P-smooth mass up to B)
     + (log B + 1)·(A/x₀')^{−s}·∏_{p∈P}(1 − p^{−(1−s)})^{−1}`. -/
theorem sharpRamareCost_le_eps (ε : ℝ) (hε : 0 < ε) :
    ∃ (D₀ : ℝ) (x₀ : ℕ), 1 ≤ D₀ ∧ 10^16 ≤ x₀ ∧
      ∀ D : ℝ, D₀ ≤ D → ∀ x0 : ℕ, x₀ ≤ x0 →
      ∀ A B : ℕ, 1 ≤ A → A ≤ B → B ≤ 2 * A + 1 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ s : ℝ, 0 < s → s < 1 →
        sharpRamareCost x0 D (ε / (8 * Real.exp 1)) A B P
          ≤ 2 * ε * pSmoothHarmonicMass B P
            + (Real.log (B:ℝ) + 1)
              * (((A:ℝ) / x0) ^ (-s) * ∏ p ∈ P, (1 - (p:ℝ) ^ (-(1 - s)))⁻¹) := by
  obtain ⟨D₀, x₀, hD₀, hx₀, hcost⟩ := sharpTwistedDirichletCost_le_eps ε hε
  refine ⟨D₀, x₀, hD₀, hx₀, ?_⟩
  intro D hD x0 hx0 A B hA hAB hB P hP s hs0 hs1
  have hx01 : 1 ≤ x0 := le_trans (le_trans (by norm_num) hx₀) hx0
  exact sharpRamareCost_le_split x0 hx01 D (ε / (8 * Real.exp 1)) A B hA hAB hB P hP ε hε.le
    (fun a b ha hab hb3 => hcost D hD a b (le_trans hx0 ha) hab hb3) s hs0 hs1

end MoltResearch
