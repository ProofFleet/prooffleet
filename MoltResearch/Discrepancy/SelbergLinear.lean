import MoltResearch.Discrepancy.SelbergPrimorial
import MoltResearch.Discrepancy.ZetaBound

/-!
# Track R: the linear Selberg sieve and the short-interval rough count

The `s = 0` specialization of the Track S Selberg machinery (campaign
#3044, M2-f): at the linear sift the squarefree root count is `1`, the
truncated `G`-sum dominates half the harmonic mass, and the primorial
master yields the short-interval rough count
`#{n ∈ (a, a+N] : (n, primorial z) = 1} ≤ 2N/log(z+1) + z⁸` — the
close-pair density input of the cheap Halász `L²` factors.
-/

namespace MoltResearch

open Finset

/-- **The linear sieve density** (Track R, M2-f1): at sift target
`s = 0` the residue condition `d ∣ n(0−n)` is `d ∣ n²`, so a
squarefree modulus removes exactly one residue class — the Selberg
machinery specializes from the quadratic to the linear sieve. -/
theorem sieveRootCard_zero_eq_one {d : ℕ} (hd : Squarefree d)
    (hd0 : 0 < d) :
    sieveRootCard 0 d = 1 := by
  classical
  unfold sieveRootCard
  have hset : (Finset.range d).filter
      (fun x : ℕ => (d : ℤ) ∣ (x : ℤ) * (((0:ℕ) : ℤ) - (x : ℤ))) = {0} := by
    ext x
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hxd, hdvd⟩
      have h1 : (d : ℤ) ∣ (x : ℤ)^2 := by
        have h2 : (x : ℤ) * (((0:ℕ) : ℤ) - (x : ℤ)) = -((x:ℤ)^2) := by
          push_cast
          ring
        rw [h2, dvd_neg] at hdvd
        exact hdvd
      have h2 : d ∣ x^2 := by
        have : ((x:ℤ))^2 = ((x^2 : ℕ) : ℤ) := by push_cast; ring
        rw [this] at h1
        exact_mod_cast h1
      have h4 : d ∣ x := (hd.dvd_pow_iff_dvd (by norm_num)).mp h2
      rcases Nat.eq_zero_or_pos x with hx | hx
      · exact hx
      · exact absurd (Nat.le_of_dvd hx h4) (by omega)
    · rintro rfl
      refine ⟨hd0, ?_⟩
      push_cast
      ring_nf
      exact dvd_zero _
  rw [hset, Finset.card_singleton]


/-- Square-reciprocal mass on `[1, z]`: at most `2`. -/
theorem sum_inv_sq_Icc_le_two (z : ℕ) :
    ∑ b ∈ Finset.Icc 1 z, (1:ℝ)/(b:ℝ)^2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos z with hz | hz
  · subst hz
    norm_num
  · have hsplit : Finset.Icc 1 z = insert 1 (Finset.Ico 2 (z+1)) := by
      ext n
      rw [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hsplit, Finset.sum_insert (by rw [Finset.mem_Ico]; omega)]
    have h2 := ExpSums.sum_inv_sq_Ico_le 2 (z+1) (le_refl 2)
    norm_num at h2 ⊢
    linarith

/-- **The harmonic floor** (M2-f2): `log(z+1) ≤ ∑_{n≤z} 1/n`. -/
theorem log_le_sum_one_div (z : ℕ) :
    Real.log ((z:ℝ)+1) ≤ ∑ n ∈ Finset.Icc 1 z, (1:ℝ)/n := by
  induction z with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1)]
    have hstep : Real.log ((k:ℝ)+1+1) - Real.log ((k:ℝ)+1) ≤ 1/((k:ℝ)+1) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have hdiv : ((k:ℝ)+1+1) / ((k:ℝ)+1) = 1 + 1/((k:ℝ)+1) := by
        field_simp
      rw [hdiv]
      have := Real.log_le_sub_one_of_pos
        (by positivity : (0:ℝ) < 1 + 1/((k:ℝ)+1))
      linarith
    push_cast
    linarith

/-- **The squarefree harmonic comparison** (M2-f2): the harmonic sum is
at most twice its squarefree part — `n = b²·a` with `a` squarefree, and
the square part carries mass `≤ 2`. -/
theorem sum_one_div_le_two_mul_squarefree (z : ℕ) :
    ∑ n ∈ Finset.Icc 1 z, (1:ℝ)/n
      ≤ 2 * ∑ k ∈ (Finset.Icc 1 z).filter Squarefree, (1:ℝ)/k := by
  classical
  have hex := fun n : ℕ => Nat.sq_mul_squarefree n
  choose a b hab hsf using hex
  have hmap : ∀ n ∈ Finset.Icc 1 z,
      (a n, b n) ∈ ((Finset.Icc 1 z).filter Squarefree) ×ˢ Finset.Icc 1 z := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have ha0 : a n ≠ 0 := by
      intro h
      rw [← hab n, h, mul_zero] at hn0
      exact hn0 rfl
    have hb0 : b n ≠ 0 := by
      intro h
      rw [← hab n, h] at hn0
      norm_num at hn0
    have hadvd : a n ∣ n := ⟨(b n)^2, by rw [mul_comm]; exact (hab n).symm⟩
    have haz : a n ≤ z := le_trans (Nat.le_of_dvd (by omega) hadvd) hn.2
    have hbz : b n ≤ z := by
      have hb2 : (b n)^2 ≤ n := by
        calc (b n)^2 ≤ (b n)^2 * a n := Nat.le_mul_of_pos_right _ (by omega)
          _ = n := hab n
      have h1 : 1 ≤ b n := by omega
      have : b n ≤ (b n)^2 := by nlinarith
      omega
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨by omega, haz⟩, hsf n⟩, by omega, hbz⟩
  have hinj : Set.InjOn (fun n => (a n, b n))
      ((Finset.Icc 1 z : Finset ℕ) : Set ℕ) := by
    intro m hm n hn h
    have h1 : a m = a n := congrArg Prod.fst h
    have h2 : b m = b n := congrArg Prod.snd h
    calc m = b m ^ 2 * a m := (hab m).symm
      _ = b n ^ 2 * a n := by rw [h1, h2]
      _ = n := hab n
  have hval : ∀ n ∈ Finset.Icc 1 z,
      (1:ℝ)/n = (1/((a n : ℕ) : ℝ)) * (1/((b n : ℕ) : ℝ)^2) := by
    intro n hn
    have h := hab n
    have hcast : (a n : ℝ) * (b n : ℝ)^2 = (n:ℝ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℝ))
        (by rw [mul_comm]; exact h : a n * (b n)^2 = n)
    rw [← hcast, div_mul_div_comm, one_mul]
  calc ∑ n ∈ Finset.Icc 1 z, (1:ℝ)/n
      = ∑ n ∈ Finset.Icc 1 z,
          (1/((a n : ℕ) : ℝ)) * (1/((b n : ℕ) : ℝ)^2) :=
        Finset.sum_congr rfl hval
    _ = ∑ y ∈ (Finset.Icc 1 z).image (fun n => (a n, b n)),
          (1/(y.1 : ℝ)) * (1/(y.2 : ℝ)^2) := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ y ∈ ((Finset.Icc 1 z).filter Squarefree) ×ˢ Finset.Icc 1 z,
          (1/(y.1 : ℝ)) * (1/(y.2 : ℝ)^2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun y _ _ => by positivity)
        intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨n, hn, rfl⟩ := hy
        exact hmap n hn
    _ = (∑ k ∈ (Finset.Icc 1 z).filter Squarefree, (1:ℝ)/k)
          * ∑ bb ∈ Finset.Icc 1 z, (1:ℝ)/(bb:ℝ)^2 := by
        rw [Finset.sum_product]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ ≤ (∑ k ∈ (Finset.Icc 1 z).filter Squarefree, (1:ℝ)/k) * 2 := by
        refine mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le_two z) ?_
        refine Finset.sum_nonneg fun k _ => by positivity
    _ = 2 * ∑ k ∈ (Finset.Icc 1 z).filter Squarefree, (1:ℝ)/k := by ring

/-- **The `s = 0` Selberg `G`-floor** (Track R, M2-f2): at the linear
sift the truncated `G`-sum dominates half the harmonic mass —
`log(z+1) ≤ 2·G(0, primorial z, R)` for `z ≤ R`. With the primorial
master this gives the short-interval rough-number count
`≤ 2N/log z + z⁸`. -/
theorem log_le_two_mul_selbergG_zero (z R : ℕ) (hz : 1 ≤ z)
    (hzR : z ≤ R) :
    Real.log ((z:ℝ)+1) ≤ 2 * selbergG 0 (primorial z) R := by
  classical
  have hPsf := squarefree_primorial z
  have hP0 : primorial z ≠ 0 := hPsf.ne_zero
  -- squarefree k ≤ z sit inside the G-index set
  have hsubset : (Finset.Icc 1 z).filter Squarefree
      ⊆ ((primorial z).divisors).filter (· ≤ R) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hkz⟩, hksf⟩ := hk
    have hkfac : ∀ p ∈ k.primeFactors, p ∈ (primorial z).primeFactors := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      rw [mem_primeFactors_primorial]
      exact ⟨hp.1, le_trans (Nat.le_of_dvd (by omega) hp.2.1) hkz⟩
    have hkdvd : k ∣ primorial z := by
      have h1 : ∏ p ∈ k.primeFactors, p = k :=
        Nat.prod_primeFactors_of_squarefree hksf
      have h2 : ∏ p ∈ (primorial z).primeFactors, p = primorial z :=
        Nat.prod_primeFactors_of_squarefree hPsf
      rw [← h1, ← h2]
      exact Finset.prod_dvd_prod_of_subset _ _ _ hkfac
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hkdvd, hP0⟩, by omega⟩
  -- each G-summand is ∏ 1/(p−1) and dominates 1/k on squarefree k
  have hpoint : ∀ k ∈ (Finset.Icc 1 z).filter Squarefree,
      (1:ℝ)/k ≤ ∏ p ∈ k.primeFactors,
        ((sieveRootCard 0 p : ℝ) / ((p : ℝ) - sieveRootCard 0 p)) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hkz⟩, hksf⟩ := hk
    have hprod : ∏ p ∈ k.primeFactors, p = k :=
      Nat.prod_primeFactors_of_squarefree hksf
    have hcongr : ∀ p ∈ k.primeFactors,
        ((sieveRootCard 0 p : ℝ) / ((p : ℝ) - sieveRootCard 0 p))
          = 1 / ((p:ℝ) - 1) := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      rw [sieveRootCard_zero_eq_one hp.1.squarefree hp.1.pos]
      norm_num
    rw [Finset.prod_congr rfl hcongr]
    have hk_cast : ((k:ℕ):ℝ) = ∏ p ∈ k.primeFactors, (p:ℝ) := by
      conv_lhs => rw [← hprod]
      push_cast
      rfl
    rw [one_div, hk_cast, ← Finset.prod_inv_distrib]
    refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
    rw [Nat.mem_primeFactors] at hp
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.1.two_le
    simp only [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hchain : ∑ k ∈ (Finset.Icc 1 z).filter Squarefree, (1:ℝ)/k
      ≤ selbergG 0 (primorial z) R := by
    unfold selbergG
    calc ∑ k ∈ (Finset.Icc 1 z).filter Squarefree, (1:ℝ)/k
        ≤ ∑ k ∈ (Finset.Icc 1 z).filter Squarefree,
            ∏ p ∈ k.primeFactors,
              ((sieveRootCard 0 p : ℝ) / ((p : ℝ) - sieveRootCard 0 p)) :=
          Finset.sum_le_sum hpoint
      _ ≤ ∑ k ∈ ((primorial z).divisors).filter (· ≤ R),
            ∏ p ∈ k.primeFactors,
              ((sieveRootCard 0 p : ℝ) / ((p : ℝ) - sieveRootCard 0 p)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset
            fun k hk _ => ?_
          refine Finset.prod_nonneg fun p hp => ?_
          rw [Nat.mem_primeFactors] at hp
          rw [sieveRootCard_zero_eq_one hp.1.squarefree hp.1.pos]
          have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.1.two_le
          push_cast
          exact div_nonneg zero_le_one (by linarith)
  have hδ := sum_one_div_le_two_mul_squarefree z
  have hε := log_le_sum_one_div z
  linarith

/-- **The short-interval rough count** (Track R, M2-f3): the numbers in
`(a, a+N]` coprime to the `z`-primorial (no prime factor `≤ z`) number
at most `2N/log(z+1) + z⁸` — the primorial Selberg master at the
linear sift `s = 0` with the harmonic `G`-floor. The close-pair
density input of the cheap Halász `L²` factors. -/
theorem card_rough_interval_le (z N a : ℕ) (hz : 1 ≤ z) :
    (((Finset.Ioc a (a + N)).filter (fun n : ℕ =>
        Nat.Coprime n (primorial z))).card : ℝ)
      ≤ 2 * (N:ℝ) / Real.log ((z:ℝ)+1) + ((z:ℝ)^4)^2 := by
  classical
  have hP0 : primorial z ≠ 0 := (squarefree_primorial z).ne_zero
  have hmaster := card_sift_le_primorial_master (s := 0) (z := z)
    (N := N) (a := a) (dvd_zero 2) hz
  have hfilter_eq : (Finset.Ioc a (a + N)).filter (fun n : ℕ =>
        ∀ p ∈ (primorial z).primeFactors,
          ¬ ((p : ℤ) ∣ (n : ℤ) * (((0:ℕ) : ℤ) - (n : ℤ))))
      = (Finset.Ioc a (a + N)).filter (fun n : ℕ =>
        Nat.Coprime n (primorial z)) := by
    refine Finset.filter_congr fun n hn => ?_
    constructor
    · intro h
      by_contra hnc
      obtain ⟨p, hp, hpn, hpP⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      refine h p (Nat.mem_primeFactors.mpr ⟨hp, hpP, hP0⟩) ?_
      have h2 : (n : ℤ) * (((0:ℕ) : ℤ) - (n : ℤ)) = -((n:ℤ)^2) := by
        push_cast
        ring
      rw [h2, dvd_neg]
      have h3 : (p:ℤ) ∣ (n:ℤ) := by exact_mod_cast hpn
      exact Dvd.dvd.trans h3 (dvd_pow_self _ (by norm_num))
    · intro hcop p hp hpdvd
      rw [Nat.mem_primeFactors] at hp
      have h2 : (n : ℤ) * (((0:ℕ) : ℤ) - (n : ℤ)) = -((n:ℤ)^2) := by
        push_cast
        ring
      rw [h2, dvd_neg] at hpdvd
      have h3 : p ∣ n^2 := by
        have h4 : ((n:ℤ))^2 = ((n^2 : ℕ) : ℤ) := by push_cast; ring
        rw [h4] at hpdvd
        exact_mod_cast hpdvd
      have h5 : p ∣ n := hp.1.dvd_of_dvd_pow h3
      exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.1, h5, hp.2.1⟩ hcop
  rw [hfilter_eq] at hmaster
  have hG := log_le_two_mul_selbergG_zero z z hz (le_refl z)
  have hlogpos : (0:ℝ) < Real.log ((z:ℝ)+1) := by
    refine Real.log_pos ?_
    have : (1:ℝ) ≤ z := by exact_mod_cast hz
    linarith
  have hGpos : (0:ℝ) < selbergG 0 (primorial z) z := by linarith
  have hNG : (N:ℝ) / selbergG 0 (primorial z) z
      ≤ 2 * (N:ℝ) / Real.log ((z:ℝ)+1) := by
    rw [div_le_div_iff₀ hGpos hlogpos]
    have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  linarith

end MoltResearch
