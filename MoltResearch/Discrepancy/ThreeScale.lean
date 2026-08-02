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


end MoltResearch
