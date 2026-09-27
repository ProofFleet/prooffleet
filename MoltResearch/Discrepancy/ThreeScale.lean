import MoltResearch.Discrepancy.SmoothRankin
import MoltResearch.Discrepancy.SelbergLinear

/-!
# Track R: the three-scale factorization substrate

The smooth/rough class split of the cheap Halász argument (campaign
#3044, M2-a): every `n` factors as its `y`-smooth part times its
`y`-rough part, and the numbers whose rough part at the lower cut is
nontrivial yet free of medium primes — the `E₂`-class of the
three-scale factorization — number at most
`(2x/log y₁)·e¹²·log y₂ + Ψ(x,y₂)·y₁⁸`.
-/

namespace MoltResearch

open Finset

/-- The `y`-smooth part of `n`: the prime powers below the cut. -/
noncomputable def smoothPart (y n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (· < y), p ^ n.factorization p

/-- The `y`-rough part of `n`: the prime powers at or above the cut. -/
noncomputable def roughPart (y n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (¬ · < y), p ^ n.factorization p

/-- **The class split** (Track R, M2-a1): every nonzero `n` factors as
its smooth part times its rough part. -/
theorem smoothPart_mul_roughPart (y n : ℕ) (hn : n ≠ 0) :
    smoothPart y n * roughPart y n = n := by
  classical
  unfold smoothPart roughPart
  rw [Finset.prod_filter_mul_prod_filter_not]
  have h := Nat.factorization_prod_pow_eq_self hn
  rw [Nat.prod_factorization_eq_prod_primeFactors] at h
  exact h

/-- The smooth part is smooth. -/
theorem smoothPart_mem_smoothNumbers (y n : ℕ) (hn : n ≠ 0) (hy : 1 ≤ y) :
    smoothPart y n ∈ Nat.smoothNumbers y := by
  classical
  rw [Nat.mem_smoothNumbers']
  intro q hq hqdvd
  unfold smoothPart at hqdvd
  obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finset_prod_iff hq.prime _).mp hqdvd
  rw [Finset.mem_filter] at hp
  have hqp' : q ∣ p := hq.dvd_of_dvd_pow hqp
  have hpp := Nat.prime_of_mem_primeFactors hp.1
  have : q = p := (Nat.prime_dvd_prime_iff_eq hq hpp).mp hqp'
  omega

/-- The rough part is coprime to the primorial below the cut. -/
theorem roughPart_coprime_primorial (y n : ℕ) (hn : n ≠ 0) (hy : 1 ≤ y) :
    Nat.Coprime (roughPart y n) (primorial (y-1)) := by
  classical
  by_contra hnc
  obtain ⟨q, hq, hq1, hq2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  unfold roughPart at hq1
  obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finset_prod_iff hq.prime _).mp hq1
  rw [Finset.mem_filter] at hp
  have hqp' : q ∣ p := hq.dvd_of_dvd_pow hqp
  have hpp := Nat.prime_of_mem_primeFactors hp.1
  have hqep : q = p := (Nat.prime_dvd_prime_iff_eq hq hpp).mp hqp'
  have hqy : q ≤ y - 1 := by
    have := mem_primeFactors_primorial.mp
      (Nat.mem_primeFactors.mpr ⟨hq, hq2, (squarefree_primorial _).ne_zero⟩)
    exact this.2
  omega


/-- The parts divide and are positive. -/
theorem smoothPart_dvd (y n : ℕ) (hn : n ≠ 0) : smoothPart y n ∣ n :=
  ⟨roughPart y n, (smoothPart_mul_roughPart y n hn).symm⟩

theorem roughPart_dvd (y n : ℕ) (hn : n ≠ 0) : roughPart y n ∣ n :=
  ⟨smoothPart y n, by
    rw [mul_comm]
    exact (smoothPart_mul_roughPart y n hn).symm⟩

theorem smoothPart_pos (y n : ℕ) (hn : n ≠ 0) : 0 < smoothPart y n := by
  rcases Nat.eq_zero_or_pos (smoothPart y n) with h | h
  · exfalso
    have := smoothPart_mul_roughPart y n hn
    rw [h, zero_mul] at this
    exact hn this.symm
  · exact h

theorem roughPart_pos (y n : ℕ) (hn : n ≠ 0) : 0 < roughPart y n := by
  rcases Nat.eq_zero_or_pos (roughPart y n) with h | h
  · exfalso
    have := smoothPart_mul_roughPart y n hn
    rw [h, mul_zero] at this
    exact hn this.symm
  · exact h

/-- **The medium-free large-part count** (Track R, E2-iv): the numbers
up to `x` whose rough part at cut `y₂` is nontrivial yet free of
primes below `y₁` number at most
`(2x/log y₁)·e¹²·log y₂ + Ψ(x,y₂)·y₁⁸` — the fibered rough count over
smooth parts, with the Mertens product bound on the outer sum. The
`E₂`-error of the cheap-Halász three-scale factorization. -/
theorem card_medfree_large_le (y₂ y₁ x : ℕ) (h2 : 4 ≤ y₂)
    (h12 : y₂ ≤ y₁) :
    ((((Finset.Icc 1 x).filter (fun n =>
        roughPart y₂ n ≠ 1
          ∧ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1)))).card : ℝ))
      ≤ (2*(x:ℝ)/Real.log y₁) * (Real.exp 12 * Real.log y₂)
        + ((Nat.smoothNumbersUpTo x y₂).card : ℝ) * ((y₁:ℝ)^4)^2 := by
  classical
  set E := (Finset.Icc 1 x).filter (fun n =>
    roughPart y₂ n ≠ 1
      ∧ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))) with hE_def
  -- fiber over the smooth part
  have hmap : ∀ n ∈ E, smoothPart y₂ n ∈ Nat.smoothNumbersUpTo x y₂ := by
    intro n hn
    rw [hE_def, Finset.mem_filter, Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    rw [Nat.mem_smoothNumbersUpTo]
    refine ⟨le_trans (Nat.le_of_dvd (by omega) (smoothPart_dvd y₂ n hn0))
      hn.1.2, ?_⟩
    exact smoothPart_mem_smoothNumbers y₂ n hn0 (by omega)
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := smoothPart y₂) (s := E) (t := Nat.smoothNumbersUpTo x y₂)
    (fun n hn => Finset.mem_coe.mpr (hmap n (Finset.mem_coe.mp hn)))
  -- each fiber injects into the rough interval
  have hfiber : ∀ n₁ ∈ Nat.smoothNumbersUpTo x y₂,
      ((E.filter (fun n => smoothPart y₂ n = n₁)).card : ℝ)
        ≤ 2*((x/n₁ : ℕ):ℝ)/Real.log ((y₁-1:ℕ)+1) + (((y₁-1:ℕ):ℝ)^4)^2 := by
    intro n₁ hn₁
    rw [Nat.mem_smoothNumbersUpTo] at hn₁
    have hn₁0 : n₁ ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hn₁.2
    have hinj : Set.InjOn (roughPart y₂)
        ↑(E.filter (fun n => smoothPart y₂ n = n₁)) := by
      intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter, hE_def, Finset.mem_filter,
        Finset.mem_Icc] at ha hb
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      calc a = smoothPart y₂ a * roughPart y₂ a :=
            (smoothPart_mul_roughPart y₂ a ha0).symm
        _ = n₁ * roughPart y₂ b := by rw [ha.2, hab]
        _ = smoothPart y₂ b * roughPart y₂ b := by rw [hb.2]
        _ = b := smoothPart_mul_roughPart y₂ b hb0
    have hsub : (E.filter (fun n => smoothPart y₂ n = n₁)).image
        (roughPart y₂)
        ⊆ (Finset.Ioc 1 (1 + (x/n₁ - 1))).filter (fun m =>
            Nat.Coprime m (primorial (y₁-1))) := by
      intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨n, hn, rfl⟩ := hm
      rw [Finset.mem_filter, hE_def, Finset.mem_filter, Finset.mem_Icc] at hn
      have hn0 : n ≠ 0 := by omega
      have hr1 : 1 < roughPart y₂ n := by
        have := roughPart_pos y₂ n hn0
        have := hn.1.2.1
        omega
      have hrle : roughPart y₂ n ≤ x/n₁ := by
        have hprod := smoothPart_mul_roughPart y₂ n hn0
        rw [hn.2] at hprod
        rw [Nat.le_div_iff_mul_le (by omega : 0 < n₁), mul_comm]
        rw [hprod]
        exact hn.1.1.2
      have hxn₁ : 1 ≤ x/n₁ := le_trans (by omega) hrle
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hr1, by omega⟩, hn.1.2.2⟩
    have hcount := card_rough_interval_le (y₁-1) (x/n₁ - 1) 1 (by omega)
    calc ((E.filter (fun n => smoothPart y₂ n = n₁)).card : ℝ)
        = (((E.filter (fun n => smoothPart y₂ n = n₁)).image
            (roughPart y₂)).card : ℝ) := by
          rw [Finset.card_image_of_injOn hinj]
      _ ≤ (((Finset.Ioc 1 (1 + (x/n₁ - 1))).filter (fun m =>
            Nat.Coprime m (primorial (y₁-1)))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ 2*((x/n₁ - 1 : ℕ):ℝ)/Real.log (((y₁-1:ℕ):ℝ)+1) + (((y₁-1:ℕ):ℝ)^4)^2 :=
          hcount
      _ ≤ 2*((x/n₁ : ℕ):ℝ)/Real.log ((y₁-1:ℕ)+1) + (((y₁-1:ℕ):ℝ)^4)^2 := by
          have hlogpos : (0:ℝ) < Real.log (((y₁-1:ℕ):ℝ)+1) := by
            refine Real.log_pos ?_
            have : (4:ℝ) ≤ ((y₁-1:ℕ):ℝ) + 1 := by
              have : 4 ≤ y₁ := by omega
              have h1 : ((y₁-1:ℕ):ℝ) = (y₁:ℝ) - 1 := by
                push_cast [Nat.cast_sub (by omega : 1 ≤ y₁)]
                ring
              rw [h1]
              push_cast
              linarith [show (4:ℝ) ≤ (y₁:ℝ) from by exact_mod_cast this]
            linarith
          have hmono : ((x/n₁ - 1 : ℕ):ℝ) ≤ ((x/n₁ : ℕ):ℝ) := by
            exact_mod_cast Nat.sub_le _ _
          gcongr
  -- outer sum
  have hy₁4 : 4 ≤ y₁ := by omega
  have hlogy₁ : (0:ℝ) < Real.log y₁ := by
    refine Real.log_pos ?_
    exact_mod_cast (by omega : 1 < y₁)
  have hcast_y₁ : ((y₁-1:ℕ):ℝ) + 1 = (y₁:ℝ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ y₁)]
    ring
  have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg x
  calc ((E.card : ℕ):ℝ)
      = ∑ n₁ ∈ Nat.smoothNumbersUpTo x y₂,
          ((E.filter (fun n => smoothPart y₂ n = n₁)).card : ℝ) := by
        rw [hcard]
        push_cast
        rfl
    _ ≤ ∑ n₁ ∈ Nat.smoothNumbersUpTo x y₂,
          (2*((x/n₁ : ℕ):ℝ)/Real.log ((y₁-1:ℕ)+1) + (((y₁-1:ℕ):ℝ)^4)^2) :=
        Finset.sum_le_sum hfiber
    _ = (∑ n₁ ∈ Nat.smoothNumbersUpTo x y₂,
          2*((x/n₁ : ℕ):ℝ)/Real.log ((y₁-1:ℕ)+1))
        + ((Nat.smoothNumbersUpTo x y₂).card : ℝ) * (((y₁-1:ℕ):ℝ)^4)^2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2*(x:ℝ)/Real.log y₁) * (Real.exp 12 * Real.log y₂)
        + ((Nat.smoothNumbersUpTo x y₂).card : ℝ) * ((y₁:ℝ)^4)^2 := by
        refine add_le_add ?_ ?_
        · have hterm : ∀ n₁ ∈ Nat.smoothNumbersUpTo x y₂,
              2*((x/n₁ : ℕ):ℝ)/Real.log ((y₁-1:ℕ)+1)
                ≤ (2*(x:ℝ)/Real.log y₁) * (1/(n₁:ℝ)) := by
            intro n₁ hn₁
            rw [Nat.mem_smoothNumbersUpTo] at hn₁
            have hn₁0 : 0 < n₁ := Nat.pos_of_ne_zero
              (Nat.ne_zero_of_mem_smoothNumbers hn₁.2)
            have hn₁r : (0:ℝ) < n₁ := by exact_mod_cast hn₁0
            rw [show ((y₁-1:ℕ):ℝ)+1 = (y₁:ℝ) from hcast_y₁]
            have hdiv : ((x/n₁ : ℕ):ℝ) ≤ (x:ℝ)/n₁ := Nat.cast_div_le
            calc 2*((x/n₁ : ℕ):ℝ)/Real.log y₁
                ≤ 2*((x:ℝ)/n₁)/Real.log y₁ := by gcongr
              _ = (2*(x:ℝ)/Real.log y₁) * (1/(n₁:ℝ)) := by
                  field_simp
          calc ∑ n₁ ∈ Nat.smoothNumbersUpTo x y₂,
              2*((x/n₁ : ℕ):ℝ)/Real.log ((y₁-1:ℕ)+1)
              ≤ ∑ n₁ ∈ Nat.smoothNumbersUpTo x y₂,
                  (2*(x:ℝ)/Real.log y₁) * (1/(n₁:ℝ)) :=
                Finset.sum_le_sum hterm
            _ = (2*(x:ℝ)/Real.log y₁) * ∑ n₁ ∈ Nat.smoothNumbersUpTo x y₂,
                  (1:ℝ)/n₁ := by
                rw [Finset.mul_sum]
            _ ≤ (2*(x:ℝ)/Real.log y₁) * (Real.exp 12 * Real.log y₂) := by
                refine mul_le_mul_of_nonneg_left
                  (sum_smooth_one_div_le y₂ x h2) ?_
                positivity
        · refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have hb : ((y₁-1:ℕ):ℝ) ≤ (y₁:ℝ) := by
            exact_mod_cast Nat.sub_le y₁ 1
          have h0 : (0:ℝ) ≤ ((y₁-1:ℕ):ℝ) := Nat.cast_nonneg _
          calc (((y₁-1:ℕ):ℝ)^4)^2 = ((y₁-1:ℕ):ℝ)^8 := by ring
            _ ≤ (y₁:ℝ)^8 := by gcongr
            _ = ((y₁:ℝ)^4)^2 := by ring



/-- Trivial rough part persists under raising the cut. -/
theorem roughPart_eq_one_of_le {y y' n : ℕ} (hn : n ≠ 0) (h : y ≤ y')
    (h1 : roughPart y n = 1) : roughPart y' n = 1 := by
  classical
  unfold roughPart at h1 ⊢
  have hempty : n.primeFactors.filter (fun p => ¬ p < y) = ∅ := by
    by_contra hne
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hdvd : p ^ n.factorization p
        ∣ ∏ q ∈ n.primeFactors.filter (fun q => ¬ q < y),
            q ^ n.factorization q :=
      Finset.dvd_prod_of_mem _ hp
    rw [h1] at hdvd
    have hone := Nat.dvd_one.mp hdvd
    rw [Finset.mem_filter] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp.1
    have hν : 0 < n.factorization p :=
      Nat.Prime.factorization_pos_of_dvd hpp hn
        (Nat.dvd_of_mem_primeFactors hp.1)
    have h2 : 2 ≤ p ^ n.factorization p :=
      le_trans hpp.two_le (Nat.le_self_pow (by omega) p)
    omega
  have hsub : n.primeFactors.filter (fun p => ¬ p < y')
      ⊆ n.primeFactors.filter (fun p => ¬ p < y) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, by omega⟩
  have : n.primeFactors.filter (fun p => ¬ p < y') = ∅ :=
    Finset.subset_empty.mp (hempty ▸ hsub)
  rw [this, Finset.prod_empty]

/-- Numbers with trivial rough part are smooth. -/
theorem mem_smoothNumbersUpTo_of_roughPart_eq_one {y x n : ℕ}
    (hn : n ∈ Finset.Icc 1 x) (hr : roughPart y n = 1) (hy : 1 ≤ y) :
    n ∈ Nat.smoothNumbersUpTo x y := by
  rw [Finset.mem_Icc] at hn
  have hn0 : n ≠ 0 := by omega
  rw [Nat.mem_smoothNumbersUpTo]
  refine ⟨hn.2, ?_⟩
  have h := smoothPart_mul_roughPart y n hn0
  rw [hr, mul_one] at h
  rw [← h]
  exact smoothPart_mem_smoothNumbers y n hn0 hy

/-- **The three-scale split** (Track R, M2-a3): the Cesàro sum differs
from its main term — the numbers with both a medium and a large prime
part — by at most the `y₁`-smooth count plus the medium-free large
count. -/
theorem norm_cesaro_sub_main_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1)
    (y₂ y₁ x : ℕ) (hy₁ : 1 ≤ y₁) (h12 : y₂ ≤ y₁) :
    ‖(∑ n ∈ Finset.Icc 1 x, f n)
        - ∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
            roughPart y₁ n ≠ 1
              ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))), f n‖
      ≤ ((Nat.smoothNumbersUpTo x y₁).card : ℝ)
        + (((Finset.Icc 1 x).filter (fun n =>
            roughPart y₂ n ≠ 1
              ∧ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1)))).card : ℝ) := by
  classical
  set MAIN := (Finset.Icc 1 x).filter (fun n =>
    roughPart y₁ n ≠ 1
      ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))) with hM_def
  have hdiff : (∑ n ∈ Finset.Icc 1 x, f n) - ∑ n ∈ MAIN, f n
      = ∑ n ∈ (Finset.Icc 1 x).filter (fun n => ¬(
          roughPart y₁ n ≠ 1
            ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1)))), f n := by
    rw [hM_def, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 x)
      (fun n => roughPart y₁ n ≠ 1
        ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1)))]
    ring
  rw [hdiff]
  -- the complement splits into smooth and medium-free-large
  have hcompl : ∀ n ∈ (Finset.Icc 1 x).filter (fun n => ¬(
      roughPart y₁ n ≠ 1
        ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1)))),
      n ∈ Nat.smoothNumbersUpTo x y₁
        ∨ n ∈ (Finset.Icc 1 x).filter (fun n =>
            roughPart y₂ n ≠ 1
              ∧ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnI, hnc⟩ := hn
    push_neg at hnc
    by_cases hr : roughPart y₁ n = 1
    · exact Or.inl (mem_smoothNumbersUpTo_of_roughPart_eq_one hnI hr hy₁)
    · right
      have hcop := hnc hr
      rw [Finset.mem_filter]
      refine ⟨hnI, ?_, hcop⟩
      rw [Finset.mem_Icc] at hnI
      have hn0 : n ≠ 0 := by omega
      intro hr2
      exact hr (roughPart_eq_one_of_le hn0 h12 hr2)
  -- bound by the two cardinalities
  set S := (Finset.Icc 1 x).filter (fun n => ¬(
    roughPart y₁ n ≠ 1
      ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1)))) with hS_def
  have hsub : S ⊆ Nat.smoothNumbersUpTo x y₁
      ∪ (Finset.Icc 1 x).filter (fun n =>
          roughPart y₂ n ≠ 1
            ∧ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))) := by
    intro n hn
    rw [Finset.mem_union]
    exact hcompl n hn
  calc ‖∑ n ∈ S, f n‖
      ≤ ∑ n ∈ S, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, 1 := Finset.sum_le_sum (fun n _ => hb n)
    _ = (S.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ((Nat.smoothNumbersUpTo x y₁
          ∪ (Finset.Icc 1 x).filter (fun n =>
              roughPart y₂ n ≠ 1
                ∧ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1)))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((Nat.smoothNumbersUpTo x y₁).card : ℝ)
        + (((Finset.Icc 1 x).filter (fun n =>
            roughPart y₂ n ≠ 1
              ∧ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1)))).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _



/-- Additive frequencies split the character. -/
theorem char_add_mul (a b ξ : ℝ) :
    ((Real.fourierChar (-((a + b) * ξ)) : Circle) : ℂ)
      = ((Real.fourierChar (-(a * ξ)) : Circle) : ℂ)
        * ((Real.fourierChar (-(b * ξ)) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The box-polynomial factorization, binary form** (Track R, M2-a4):
the phase polynomial of a product box with additive log-frequencies
splits into the product of the factor polynomials. -/
theorem sum_box_char_eq_mul {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (w : ι → ℂ) (v : κ → ℂ) (s : ι → ℝ) (r : κ → ℝ) (ξ : ℝ) :
    ∑ p ∈ S ×ˢ T, (w p.1 * v p.2)
        * ((Real.fourierChar (-((s p.1 + r p.2) * ξ)) : Circle) : ℂ)
      = (∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ))
        * (∑ j ∈ T, v j * ((Real.fourierChar (-(r j * ξ)) : Circle) : ℂ)) := by
  classical
  rw [Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [char_add_mul]
  ring

/-- **The box-polynomial factorization, triple form** (M2-a4): three
factors. -/
theorem sum_triple_char_eq_mul (S₁ S₂ S₃ : Finset ℕ)
    (w₁ w₂ w₃ : ℕ → ℂ) (ξ : ℝ) :
    ∑ t ∈ S₁ ×ˢ (S₂ ×ˢ S₃),
        (w₁ t.1 * (w₂ t.2.1 * w₃ t.2.2))
          * ((Real.fourierChar
              (-((Real.log t.1 + (Real.log t.2.1 + Real.log t.2.2)) * ξ))
              : Circle) : ℂ)
      = (∑ i ∈ S₁, w₁ i * ((Real.fourierChar (-(Real.log i * ξ)) : Circle) : ℂ))
        * ((∑ j ∈ S₂, w₂ j * ((Real.fourierChar (-(Real.log j * ξ)) : Circle) : ℂ))
          * (∑ k ∈ S₃, w₃ k * ((Real.fourierChar (-(Real.log k * ξ)) : Circle) : ℂ))) := by
  classical
  have hinner := sum_box_char_eq_mul S₂ S₃ w₂ w₃
    (fun j => Real.log j) (fun k => Real.log k) ξ
  have houter := sum_box_char_eq_mul S₁ (S₂ ×ˢ S₃) w₁
    (fun p : ℕ × ℕ => w₂ p.1 * w₃ p.2)
    (fun i => Real.log i)
    (fun p : ℕ × ℕ => Real.log p.1 + Real.log p.2) ξ
  rw [houter, hinner]


/-- **Factorization uniqueness, smooth side** (Track R, M2-i4c0a): the
smooth part of a smooth × rough product is the smooth factor. -/
theorem smoothPart_mul_eq_left (y : ℕ) (hy : 1 ≤ y) (a r : ℕ)
    (ha : a ∈ Nat.smoothNumbers y) (hr0 : r ≠ 0)
    (hr : Nat.Coprime r (primorial (y-1))) :
    smoothPart y (a * r) = a := by
  classical
  have ha0 : a ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers ha
  have hprimes_a : ∀ p ∈ a.primeFactors, p < y := by
    intro p hp
    exact Nat.mem_smoothNumbers'.mp ha p
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hprimes_r : ∀ p ∈ r.primeFactors, ¬ p < y := by
    intro p hp hlt
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hple : p ≤ y - 1 := by
      have := hpp.two_le
      omega
    have hdvd_prim : p ∣ primorial (y-1) :=
      Nat.dvd_of_mem_primeFactors
        (mem_primeFactors_primorial.mpr ⟨hpp, hple⟩)
    exact Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p, hpp, Nat.dvd_of_mem_primeFactors hp, hdvd_prim⟩ hr
  unfold smoothPart
  have hpf : (a * r).primeFactors = a.primeFactors ∪ r.primeFactors :=
    Nat.primeFactors_mul ha0 hr0
  have hfilter : ((a * r).primeFactors).filter (· < y) = a.primeFactors := by
    rw [hpf]
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hpa | hpr, hlt⟩
      · exact hpa
      · exact absurd hlt (hprimes_r p hpr)
    · intro hpa
      exact ⟨Or.inl hpa, hprimes_a p hpa⟩
  rw [hfilter]
  have hfact : ∀ p ∈ a.primeFactors,
      (a * r).factorization p = a.factorization p := by
    intro p hp
    rw [Nat.factorization_mul ha0 hr0]
    have hnot : p ∉ r.primeFactors := fun hpr =>
      (hprimes_r p hpr) (hprimes_a p hp)
    rw [← Nat.support_factorization] at hnot
    have hz : r.factorization p = 0 := Finsupp.notMem_support_iff.mp hnot
    simp [hz]
  rw [Finset.prod_congr rfl fun p hp => by rw [hfact p hp]]
  have h := Nat.factorization_prod_pow_eq_self ha0
  rw [Nat.prod_factorization_eq_prod_primeFactors] at h
  exact h

/-- **Factorization uniqueness, rough side** (Track R, M2-i4c0a): the
rough part of a smooth × rough product is the rough factor. -/
theorem roughPart_mul_eq_right (y : ℕ) (hy : 1 ≤ y) (a r : ℕ)
    (ha : a ∈ Nat.smoothNumbers y) (hr0 : r ≠ 0)
    (hr : Nat.Coprime r (primorial (y-1))) :
    roughPart y (a * r) = r := by
  have ha0 : a ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers ha
  have h := smoothPart_mul_roughPart y (a * r) (mul_ne_zero ha0 hr0)
  rw [smoothPart_mul_eq_left y hy a r ha hr0 hr] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha0) h

/-- Smooth numbers are closed under multiplication. -/
theorem mul_mem_smoothNumbers {y a b : ℕ} (ha : a ∈ Nat.smoothNumbers y)
    (hb : b ∈ Nat.smoothNumbers y) : a * b ∈ Nat.smoothNumbers y := by
  rw [Nat.mem_smoothNumbers'] at ha hb ⊢
  intro p hp hpdvd
  rcases (Nat.Prime.dvd_mul hp).mp hpdvd with h | h
  · exact ha p hp h
  · exact hb p hp h

/-- **Rough-part idempotence across cuts** (Track R, M2-i4c0a): the
`y₁`-rough part of the `y₂`-rough part is the `y₁`-rough part, for
`y₂ ≤ y₁`. -/
theorem roughPart_roughPart (y₂ y₁ n : ℕ) (hy₂ : 1 ≤ y₂)
    (h12 : y₂ ≤ y₁) (hn : n ≠ 0) :
    roughPart y₁ (roughPart y₂ n) = roughPart y₁ n := by
  have hy₁ : 1 ≤ y₁ := le_trans hy₂ h12
  have hr0 : roughPart y₂ n ≠ 0 := (roughPart_pos y₂ n hn).ne'
  have hrr0 : roughPart y₁ (roughPart y₂ n) ≠ 0 :=
    (roughPart_pos y₁ _ hr0).ne'
  -- n = (smoothPart y₂ n * smoothPart y₁ (roughPart y₂ n)) * large
  have hsplit1 := smoothPart_mul_roughPart y₂ n hn
  have hsplit2 := smoothPart_mul_roughPart y₁ (roughPart y₂ n) hr0
  have hsmooth : smoothPart y₂ n * smoothPart y₁ (roughPart y₂ n)
      ∈ Nat.smoothNumbers y₁ :=
    mul_mem_smoothNumbers
      (Nat.smoothNumbers_mono h12 (smoothPart_mem_smoothNumbers y₂ n hn hy₂))
      (smoothPart_mem_smoothNumbers y₁ _ hr0 hy₁)
  have hrough : Nat.Coprime (roughPart y₁ (roughPart y₂ n))
      (primorial (y₁-1)) :=
    roughPart_coprime_primorial y₁ _ hr0 hy₁
  have hn_eq : n = (smoothPart y₂ n * smoothPart y₁ (roughPart y₂ n))
      * roughPart y₁ (roughPart y₂ n) := by
    rw [mul_assoc, hsplit2, hsplit1]
  calc roughPart y₁ (roughPart y₂ n)
      = roughPart y₁ ((smoothPart y₂ n * smoothPart y₁ (roughPart y₂ n))
          * roughPart y₁ (roughPart y₂ n)) :=
        (roughPart_mul_eq_right y₁ hy₁ _ _ hsmooth hrr0 hrough).symm
    _ = roughPart y₁ n := by rw [← hn_eq]

/-- The primorial divides the primorial at a larger cut. -/
theorem primorial_dvd_primorial {m m' : ℕ} (h : m ≤ m') :
    primorial m ∣ primorial m' := by
  refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

set_option maxHeartbeats 3200000 in
/-- **The box bridge** (Track R, M2-i4c0b): the window-weighted main
term of the three-scale split equals the window-weighted sum over the
full product box small-smooth × medium-class × large-class. Tuples
whose product exceeds `x` are killed by the window; tuples with
product at most `x` biject with the main set via the canonical
three-part factorization. This puts the main term in the exact shape
of the translate pairing at the triple index. -/
theorem sum_main_eq_sum_box (f : ℕ → ℂ)
    (hcm : ∀ a b, a ≠ 0 → b ≠ 0 → f (a * b) = f a * f b)
    (y₂ y₁ x : ℕ) (hy₂ : 1 ≤ y₂) (h12 : y₂ ≤ y₁) (hx : 1 ≤ x)
    (V : ℝ → ℝ) (hV0 : ∀ v, v ≤ 0 → V v = 0) :
    ∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
        roughPart y₁ n ≠ 1
          ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
      (f n/(n:ℂ)) * ((V (Real.log x - Real.log n) : ℝ) : ℂ)
    = ∑ t ∈ ((Finset.Icc 1 x).filter (· ∈ Nat.smoothNumbers y₂)) ×ˢ
        (((Finset.Icc 1 x).filter (fun b => b ≠ 1
            ∧ b ∈ Nat.smoothNumbers y₁
            ∧ Nat.Coprime b (primorial (y₂-1)))) ×ˢ
         ((Finset.Icc 1 x).filter (fun c => c ≠ 1
            ∧ Nat.Coprime c (primorial (y₁-1))))),
      (f t.1/(t.1:ℂ) * (f t.2.1/(t.2.1:ℂ) * (f t.2.2/(t.2.2:ℂ))))
        * ((V (Real.log x
            - (Real.log t.1 + (Real.log t.2.1 + Real.log t.2.2))) : ℝ) : ℂ) := by
  classical
  have hy₁ : 1 ≤ y₁ := le_trans hy₂ h12
  refine Eq.trans ?_ (Finset.sum_filter_of_ne
    (p := fun t : ℕ × ℕ × ℕ => t.1 * (t.2.1 * t.2.2) ≤ x) ?_)
  swap
  · -- tuples with product beyond x are killed by the window
    intro t ht hne
    rw [Finset.mem_product, Finset.mem_product] at ht
    obtain ⟨ht1, ht2, ht3⟩ := ht
    rw [Finset.mem_filter, Finset.mem_Icc] at ht1 ht2 ht3
    by_contra hgt
    push_neg at hgt
    refine hne ?_
    have ha1 : 1 ≤ t.1 := ht1.1.1
    have hb1 : 1 ≤ t.2.1 := ht2.1.1
    have hc1 : 1 ≤ t.2.2 := ht3.1.1
    have hxm : (x:ℝ) ≤ (t.1:ℝ) * ((t.2.1:ℝ) * (t.2.2:ℝ)) := by
      exact_mod_cast le_of_lt hgt
    have hlogsum : Real.log t.1 + (Real.log t.2.1 + Real.log t.2.2)
        = Real.log ((t.1:ℝ) * ((t.2.1:ℝ) * (t.2.2:ℝ))) := by
      rw [Real.log_mul (by exact_mod_cast (by omega : t.1 ≠ 0))
          (by positivity),
        Real.log_mul (by exact_mod_cast (by omega : t.2.1 ≠ 0))
          (by exact_mod_cast (by omega : t.2.2 ≠ 0))]
    have hVz : V (Real.log x
        - (Real.log t.1 + (Real.log t.2.1 + Real.log t.2.2))) = 0 := by
      refine hV0 _ ?_
      rw [hlogsum]
      have hxpos : (0:ℝ) < x := by exact_mod_cast (by omega : 0 < x)
      have := Real.log_le_log hxpos hxm
      linarith
    rw [hVz]
    simp
  -- the bijection between the main set and the truncated box
  refine Finset.sum_bij'
    (fun n _ => (smoothPart y₂ n,
      (smoothPart y₁ (roughPart y₂ n), roughPart y₁ n)))
    (fun t _ => t.1 * (t.2.1 * t.2.2)) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnx⟩, hlarge, hmed⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hnpos : 0 < n := by omega
    have hr0 : roughPart y₂ n ≠ 0 := (roughPart_pos y₂ n hn0).ne'
    have hrr := roughPart_roughPart y₂ y₁ n hy₂ h12 hn0
    have hprod : smoothPart y₂ n
        * (smoothPart y₁ (roughPart y₂ n) * roughPart y₁ n) = n := by
      rw [← hrr, smoothPart_mul_roughPart y₁ _ hr0,
        smoothPart_mul_roughPart y₂ n hn0]
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    dsimp only
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · -- smooth part in B₁
      rw [Finset.mem_filter, Finset.mem_Icc]
      have hdvd := smoothPart_dvd y₂ n hn0
      exact ⟨⟨Nat.pos_of_ne_zero (smoothPart_pos y₂ n hn0).ne',
        le_trans (Nat.le_of_dvd hnpos hdvd) hnx⟩,
        smoothPart_mem_smoothNumbers y₂ n hn0 hy₂⟩
    · -- medium part in B₂
      rw [Finset.mem_filter, Finset.mem_Icc]
      have hdvd : smoothPart y₁ (roughPart y₂ n) ∣ n :=
        dvd_trans (smoothPart_dvd y₁ _ hr0) (roughPart_dvd y₂ n hn0)
      refine ⟨⟨Nat.pos_of_ne_zero (smoothPart_pos y₁ _ hr0).ne',
        le_trans (Nat.le_of_dvd hnpos hdvd) hnx⟩, ?_, ?_, ?_⟩
      · -- medium part nontrivial: the medium prime witness
        obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hmed
        have hsplit := smoothPart_mul_roughPart y₁ (roughPart y₂ n) hr0
        have hpmed : p ∣ smoothPart y₁ (roughPart y₂ n) := by
          rcases (Nat.Prime.dvd_mul hp).mp (hsplit ▸ hp1) with h | h
          · exact h
          · exfalso
            rw [hrr] at h
            exact Nat.Prime.not_coprime_iff_dvd.mpr
              ⟨p, hp, h, hp2⟩ (roughPart_coprime_primorial y₁ n hn0 hy₁)
        intro heq
        rw [heq] at hpmed
        have h1 := Nat.dvd_one.mp hpmed
        have h2 := hp.two_le
        omega
      · exact smoothPart_mem_smoothNumbers y₁ _ hr0 hy₁
      · exact Nat.Coprime.coprime_dvd_left (smoothPart_dvd y₁ _ hr0)
          (roughPart_coprime_primorial y₂ n hn0 hy₂)
    · -- large part in B₃
      rw [Finset.mem_filter, Finset.mem_Icc]
      have hdvd := roughPart_dvd y₁ n hn0
      exact ⟨⟨Nat.pos_of_ne_zero (roughPart_pos y₁ n hn0).ne',
        le_trans (Nat.le_of_dvd hnpos hdvd) hnx⟩, hlarge,
        roughPart_coprime_primorial y₁ n hn0 hy₁⟩
    · -- the product is back within range
      rw [hprod]
      exact hnx
  · -- backward membership
    intro t ht
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
    obtain ⟨⟨ht1, ht2, ht3⟩, hprodx⟩ := ht
    rw [Finset.mem_filter, Finset.mem_Icc] at ht1 ht2 ht3
    obtain ⟨⟨ha1, hax⟩, hasm⟩ := ht1
    obtain ⟨⟨hb1, hbx⟩, hbne, hbsm, hbcop⟩ := ht2
    obtain ⟨⟨hc1, hcx⟩, hcne, hccop⟩ := ht3
    have hb0 : t.2.1 ≠ 0 := by omega
    have hc0 : t.2.2 ≠ 0 := by omega
    have hbc0 : t.2.1 * t.2.2 ≠ 0 := mul_ne_zero hb0 hc0
    have hccop₂ : Nat.Coprime t.2.2 (primorial (y₂-1)) :=
      Nat.Coprime.coprime_dvd_right
        (primorial_dvd_primorial (by omega : y₂-1 ≤ y₁-1)) hccop
    have hbccop : Nat.Coprime (t.2.1 * t.2.2) (primorial (y₂-1)) :=
      Nat.Coprime.mul_left hbcop hccop₂
    have hr2 : roughPart y₂ (t.1 * (t.2.1 * t.2.2)) = t.2.1 * t.2.2 :=
      roughPart_mul_eq_right y₂ hy₂ _ _ hasm hbc0 hbccop
    have habsm : t.1 * t.2.1 ∈ Nat.smoothNumbers y₁ :=
      mul_mem_smoothNumbers (Nat.smoothNumbers_mono h12 hasm) hbsm
    have hr3 : roughPart y₁ (t.1 * (t.2.1 * t.2.2)) = t.2.2 := by
      rw [← mul_assoc]
      exact roughPart_mul_eq_right y₁ hy₁ _ _ habsm hc0 hccop
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, hprodx⟩, ?_, ?_⟩
    · have h0 : 0 < t.1 * (t.2.1 * t.2.2) := by positivity
      exact Nat.one_le_iff_ne_zero.mpr h0.ne'
    · rw [hr3]
      exact hcne
    · rw [hr2]
      intro hcop
      obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd hbne
      have hpy₁ : p < y₁ := Nat.mem_smoothNumbers'.mp hbsm p hp hpb
      have hple : p ≤ y₁ - 1 := by
        have := hp.two_le
        omega
      have hpprim : p ∣ primorial (y₁-1) :=
        Nat.dvd_of_mem_primeFactors
          (mem_primeFactors_primorial.mpr ⟨hp, hple⟩)
      exact Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p, hp, dvd_mul_of_dvd_left hpb _, hpprim⟩ hcop
  · -- left inverse
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnx⟩, _, _⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hr0 : roughPart y₂ n ≠ 0 := (roughPart_pos y₂ n hn0).ne'
    have hrr := roughPart_roughPart y₂ y₁ n hy₂ h12 hn0
    dsimp only
    rw [← hrr, smoothPart_mul_roughPart y₁ _ hr0,
      smoothPart_mul_roughPart y₂ n hn0]
  · -- right inverse
    intro t ht
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
    obtain ⟨⟨ht1, ht2, ht3⟩, hprodx⟩ := ht
    rw [Finset.mem_filter, Finset.mem_Icc] at ht1 ht2 ht3
    obtain ⟨⟨ha1, hax⟩, hasm⟩ := ht1
    obtain ⟨⟨hb1, hbx⟩, hbne, hbsm, hbcop⟩ := ht2
    obtain ⟨⟨hc1, hcx⟩, hcne, hccop⟩ := ht3
    have hb0 : t.2.1 ≠ 0 := by omega
    have hc0 : t.2.2 ≠ 0 := by omega
    have hbc0 : t.2.1 * t.2.2 ≠ 0 := mul_ne_zero hb0 hc0
    have hccop₂ : Nat.Coprime t.2.2 (primorial (y₂-1)) :=
      Nat.Coprime.coprime_dvd_right
        (primorial_dvd_primorial (by omega : y₂-1 ≤ y₁-1)) hccop
    have hbccop : Nat.Coprime (t.2.1 * t.2.2) (primorial (y₂-1)) :=
      Nat.Coprime.mul_left hbcop hccop₂
    have h1 : smoothPart y₂ (t.1 * (t.2.1 * t.2.2)) = t.1 :=
      smoothPart_mul_eq_left y₂ hy₂ _ _ hasm hbc0 hbccop
    have hr2 : roughPart y₂ (t.1 * (t.2.1 * t.2.2)) = t.2.1 * t.2.2 :=
      roughPart_mul_eq_right y₂ hy₂ _ _ hasm hbc0 hbccop
    have h2 : smoothPart y₁ (roughPart y₂ (t.1 * (t.2.1 * t.2.2)))
        = t.2.1 := by
      rw [hr2]
      exact smoothPart_mul_eq_left y₁ hy₁ _ _ hbsm hc0 hccop
    have habsm : t.1 * t.2.1 ∈ Nat.smoothNumbers y₁ :=
      mul_mem_smoothNumbers (Nat.smoothNumbers_mono h12 hasm) hbsm
    have h3 : roughPart y₁ (t.1 * (t.2.1 * t.2.2)) = t.2.2 := by
      rw [← mul_assoc]
      exact roughPart_mul_eq_right y₁ hy₁ _ _ habsm hc0 hccop
    exact Prod.ext_iff.mpr ⟨h1, Prod.ext_iff.mpr ⟨h2, h3⟩⟩
  · -- the summands agree
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnx⟩, _, _⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hr0 : roughPart y₂ n ≠ 0 := (roughPart_pos y₂ n hn0).ne'
    have hrr := roughPart_roughPart y₂ y₁ n hy₂ h12 hn0
    have hprod : smoothPart y₂ n
        * (smoothPart y₁ (roughPart y₂ n) * roughPart y₁ n) = n := by
      rw [← hrr, smoothPart_mul_roughPart y₁ _ hr0,
        smoothPart_mul_roughPart y₂ n hn0]
    have ha0 : smoothPart y₂ n ≠ 0 := (smoothPart_pos y₂ n hn0).ne'
    have hb0 : smoothPart y₁ (roughPart y₂ n) ≠ 0 :=
      (smoothPart_pos y₁ _ hr0).ne'
    have hc0 : roughPart y₁ n ≠ 0 := (roughPart_pos y₁ n hn0).ne'
    have hf : f n = f (smoothPart y₂ n)
        * (f (smoothPart y₁ (roughPart y₂ n)) * f (roughPart y₁ n)) := by
      conv_lhs => rw [← hprod]
      rw [hcm _ _ ha0 (mul_ne_zero hb0 hc0), hcm _ _ hb0 hc0]
    have hcast : (n:ℂ) = (smoothPart y₂ n : ℂ)
        * ((smoothPart y₁ (roughPart y₂ n) : ℂ) * (roughPart y₁ n : ℂ)) := by
      exact_mod_cast congrArg (fun k : ℕ => (k:ℂ)) hprod.symm
    have hlogn : Real.log n = Real.log (smoothPart y₂ n)
        + (Real.log (smoothPart y₁ (roughPart y₂ n))
          + Real.log (roughPart y₁ n)) := by
      have hcastR : (n:ℝ) = (smoothPart y₂ n : ℝ)
          * ((smoothPart y₁ (roughPart y₂ n) : ℝ)
            * (roughPart y₁ n : ℝ)) := by
        exact_mod_cast congrArg (fun k : ℕ => (k:ℝ)) hprod.symm
      rw [hcastR,
        Real.log_mul (by exact_mod_cast ha0) (by
          refine mul_ne_zero ?_ ?_ <;> exact_mod_cast ‹_›),
        Real.log_mul (by exact_mod_cast hb0) (by exact_mod_cast hc0)]
    dsimp only
    rw [hf, hcast, hlogn, mul_div_mul_comm, mul_div_mul_comm]

end MoltResearch
