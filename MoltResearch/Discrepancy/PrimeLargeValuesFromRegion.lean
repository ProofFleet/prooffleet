import MoltResearch.Discrepancy.PrimeSumZeroFree
import MoltResearch.Discrepancy.HalaszMontgomeryLargeValues
import MoltResearch.Discrepancy.LogUniform
import MoltResearch.Discrepancy.CharTwistCompose

/-!
# Prime large values from a zero-free region

This leaf contains the finite-dimensional part of `[MR]` Lemma 8.  The
analytic kernel estimate is supplied by `PrimeSumZeroFree`; here the two
remaining ingredients are square-reciprocal packing and weighted duality.
-/

namespace MoltResearch

open Complex ExpSums Finset MeasureTheory
open scoped ContDiff

/-- A one-separated positive family has square-reciprocal mass at most two. -/
theorem sum_inv_sq_le_two_of_one_separated {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (d : ι → ℝ)
    (hd1 : ∀ i ∈ S, 1 ≤ d i)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |d i - d j|) :
    ∑ i ∈ S, (1 : ℝ) / d i ^ 2 ≤ 2 := by
  classical
  let k : ι → ℕ := fun i => ⌊d i⌋₊
  have hk1 : ∀ i ∈ S, 1 ≤ k i := by
    intro i hi
    exact Nat.le_floor (by exact_mod_cast hd1 i hi)
  have hkinj : Set.InjOn k ↑S := by
    intro i hi j hj hij
    have hiS := Finset.mem_coe.mp hi
    have hjS := Finset.mem_coe.mp hj
    have hdi0 : 0 ≤ d i := le_trans (by norm_num) (hd1 i hiS)
    have hdj0 : 0 ≤ d j := le_trans (by norm_num) (hd1 j hjS)
    have hki : ((k i : ℕ) : ℝ) ≤ d i := Nat.floor_le hdi0
    have hkj : ((k j : ℕ) : ℝ) ≤ d j := Nat.floor_le hdj0
    have hik : d i < (k i : ℕ) + 1 := Nat.lt_floor_add_one _
    have hjk : d j < (k j : ℕ) + 1 := Nat.lt_floor_add_one _
    have hfloor : ((k i : ℕ) : ℝ) = (k j : ℕ) := by exact_mod_cast hij
    have habs : |d i - d j| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    by_contra hne
    exact (not_lt_of_ge (hsep i hiS j hjS hne)) habs
  have hpoint : ∀ i ∈ S, (1 : ℝ) / d i ^ 2 ≤ 1 / (k i : ℝ) ^ 2 := by
    intro i hi
    have hkpos : (0 : ℝ) < k i := by exact_mod_cast hk1 i hi
    have hkd : (k i : ℝ) ≤ d i :=
      Nat.floor_le (le_trans (by norm_num) (hd1 i hi))
    exact one_div_le_one_div_of_le (sq_pos_of_pos hkpos)
      (sq_le_sq₀ hkpos.le (le_trans (by norm_num) (hd1 i hi)) |>.mpr hkd)
  calc
    ∑ i ∈ S, (1 : ℝ) / d i ^ 2
        ≤ ∑ i ∈ S, (1 : ℝ) / (k i : ℝ) ^ 2 := Finset.sum_le_sum hpoint
    _ = ∑ m ∈ S.image k, (1 : ℝ) / (m : ℝ) ^ 2 :=
      (Finset.sum_image (f := fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) hkinj).symm
    _ ≤ 2 := sum_one_div_sq_le_two (S.image k)

/-- The square-reciprocal gaps about one point in a `1`-separated family
have uniformly bounded mass. -/
theorem sum_inv_sq_abs_sub_erase_le_four {ι : Type*} [DecidableEq ι]
    (𝒯 : Finset ι) (position : ι → ℝ) (t : ι) (ht : t ∈ 𝒯)
    (hsep : ∀ s ∈ 𝒯, ∀ v ∈ 𝒯, s ≠ v →
      1 ≤ |position s - position v|) :
    ∑ s ∈ 𝒯.erase t, (1 : ℝ) /
      |position t - position s| ^ 2 ≤ 4 := by
  classical
  let L := 𝒯.filter (fun s => position s < position t)
  let R := 𝒯.filter (fun s => position t < position s)
  have hleft : ∑ s ∈ L, (1 : ℝ) /
      (position t - position s) ^ 2 ≤ 2 := by
    apply sum_inv_sq_le_two_of_one_separated L
      (fun s => position t - position s)
    · intro s hs
      dsimp [L] at hs
      rw [Finset.mem_filter] at hs
      have hne : t ≠ s := by
        intro hts
        rw [hts] at hs
        exact (lt_irrefl _ hs.2).elim
      have h := hsep t ht s hs.1 hne
      rwa [abs_of_pos (sub_pos.mpr hs.2)] at h
    · intro s hs v hv hsv
      dsimp [L] at hs hv
      rw [Finset.mem_filter] at hs hv
      have h := hsep v hv.1 s hs.1 hsv.symm
      simpa [sub_sub_sub_cancel_left, abs_sub_comm] using h
  have hright : ∑ s ∈ R, (1 : ℝ) /
      (position s - position t) ^ 2 ≤ 2 := by
    apply sum_inv_sq_le_two_of_one_separated R
      (fun s => position s - position t)
    · intro s hs
      dsimp [R] at hs
      rw [Finset.mem_filter] at hs
      have hne : s ≠ t := by
        intro hst
        rw [hst] at hs
        exact (lt_irrefl _ hs.2).elim
      have h := hsep s hs.1 t ht hne
      rwa [abs_of_pos (sub_pos.mpr hs.2)] at h
    · intro s hs v hv hsv
      dsimp [R] at hs hv
      rw [Finset.mem_filter] at hs hv
      have h := hsep s hs.1 v hv.1 hsv
      simpa [sub_sub_sub_cancel_right] using h
  have hsplit : 𝒯.erase t = L ∪ R := by
    ext s
    simp only [L, R, Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hs
      have hposne : position s ≠ position t := by
        intro heq
        have h := hsep s hs.2 t ht hs.1
        rw [heq, sub_self, abs_zero] at h
        norm_num at h
      rcases lt_or_gt_of_ne hposne with hlt | hgt
      · exact Or.inl ⟨hs.2, hlt⟩
      · exact Or.inr ⟨hs.2, hgt⟩
    · rintro (⟨hs, hlt⟩ | ⟨hs, hgt⟩)
      · refine ⟨?_, hs⟩
        intro hst
        rw [hst] at hlt
        exact (lt_irrefl _ hlt).elim
      · refine ⟨?_, hs⟩
        intro hst
        rw [hst] at hgt
        exact (lt_irrefl _ hgt).elim
  have hdis : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro s hs hv
    dsimp [L] at hs
    dsimp [R] at hv
    rw [Finset.mem_filter] at hs hv
    linarith
  rw [hsplit, Finset.sum_union hdis]
  have hleftEq : ∑ s ∈ L, (1 : ℝ) /
      |position t - position s| ^ 2 =
      ∑ s ∈ L, (1 : ℝ) / (position t - position s) ^ 2 := by
    apply Finset.sum_congr rfl
    intro s hs
    dsimp [L] at hs
    rw [Finset.mem_filter] at hs
    rw [abs_of_pos (sub_pos.mpr hs.2)]
  have hrightEq : ∑ s ∈ R, (1 : ℝ) /
      |position t - position s| ^ 2 =
      ∑ s ∈ R, (1 : ℝ) / (position s - position t) ^ 2 := by
    apply Finset.sum_congr rfl
    intro s hs
    dsimp [R] at hs
    rw [Finset.mem_filter] at hs
    rw [abs_of_neg (sub_neg.mpr hs.2), neg_sub]
  rw [hleftEq, hrightEq]
  linarith

/-- Weighted finite-dimensional duality in the exact form used by `[MR]`:
an `ℓ²` bound for the adjoint synthesis map gives the same bound for the
original map, with reciprocal weights on its coefficients. -/
theorem weighted_synthesis_sq_le_of_adjoint_sq_le {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (weight : ι → ℝ)
    (b : ι → ℂ) (χ : ι → κ → ℂ) (B : ℝ)
    (hw : ∀ i ∈ I, 0 < weight i) (hB : 0 ≤ B)
    (hadj : ∀ η : κ → ℂ,
      ∑ i ∈ I, weight i *
          ‖∑ t ∈ J, η t * (starRingEnd ℂ) (χ i t)‖ ^ 2 ≤
        B * ∑ t ∈ J, ‖η t‖ ^ 2) :
    ∑ t ∈ J, ‖∑ i ∈ I, b i * χ i t‖ ^ 2 ≤
      B * ∑ i ∈ I, ‖b i‖ ^ 2 / weight i := by
  classical
  let S : κ → ℂ := fun t => ∑ i ∈ I, b i * χ i t
  let A : ι → ℂ := fun i =>
    ∑ t ∈ J, S t * (starRingEnd ℂ) (χ i t)
  let L : ℝ := ∑ t ∈ J, ‖S t‖ ^ 2
  let Q : ℝ := ∑ i ∈ I, weight i * ‖A i‖ ^ 2
  let R : ℝ := ∑ i ∈ I, ‖b i‖ ^ 2 / weight i
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun t _ => sq_nonneg _
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i hi =>
    div_nonneg (sq_nonneg _) (hw i hi).le
  have hQ : Q ≤ B * L := by
    simpa only [Q, A, L] using hadj S
  have henergy : ((L : ℝ) : ℂ) =
      ∑ i ∈ I, (starRingEnd ℂ) (b i) * A i := by
    calc
      ((L : ℝ) : ℂ) = ∑ t ∈ J, (((‖S t‖ ^ 2 : ℝ) : ℂ)) := by
        simp only [L, Complex.ofReal_sum]
      _ = ∑ t ∈ J, ∑ i ∈ I,
          (starRingEnd ℂ) (b i) *
            (S t * (starRingEnd ℂ) (χ i t)) := by
        apply Finset.sum_congr rfl
        intro t ht
        calc
          (((‖S t‖ ^ 2 : ℝ) : ℂ)) =
              S t * (starRingEnd ℂ) (S t) := by
            rw [← Complex.normSq_eq_norm_sq]
            exact (Complex.mul_conj _).symm
          _ = S t * (starRingEnd ℂ) (∑ i ∈ I, b i * χ i t) := by rfl
          _ = S t * ∑ i ∈ I,
              (starRingEnd ℂ) (b i * χ i t) := by rw [map_sum]
          _ = ∑ i ∈ I, (starRingEnd ℂ) (b i) *
              (S t * (starRingEnd ℂ) (χ i t)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [map_mul]
            ring
      _ = ∑ i ∈ I, ∑ t ∈ J,
          (starRingEnd ℂ) (b i) *
            (S t * (starRingEnd ℂ) (χ i t)) := by rw [Finset.sum_comm]
      _ = ∑ i ∈ I, (starRingEnd ℂ) (b i) * A i := by
        apply Finset.sum_congr rfl
        intro i hi
        change (∑ t ∈ J, (starRingEnd ℂ) (b i) *
            (S t * (starRingEnd ℂ) (χ i t))) =
          (starRingEnd ℂ) (b i) *
            (∑ t ∈ J, S t * (starRingEnd ℂ) (χ i t))
        rw [Finset.mul_sum]
  have htri : L ≤ ∑ i ∈ I, ‖b i‖ * ‖A i‖ := by
    have hnorm : L = ‖∑ i ∈ I, (starRingEnd ℂ) (b i) * A i‖ := by
      rw [← henergy, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
    rw [hnorm]
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun i _ => by rw [norm_mul, RCLike.norm_conj]
  have hfactor (i : ι) (hi : i ∈ I) :
      ‖b i‖ * ‖A i‖ =
        (‖b i‖ / Real.sqrt (weight i)) *
          (Real.sqrt (weight i) * ‖A i‖) := by
    have hs : Real.sqrt (weight i) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (hw i hi))
    field_simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I
    (fun i => ‖b i‖ / Real.sqrt (weight i))
    (fun i => Real.sqrt (weight i) * ‖A i‖)
  have hfirst : ∑ i ∈ I, (‖b i‖ / Real.sqrt (weight i)) ^ 2 = R := by
    apply Finset.sum_congr rfl
    intro i hi
    have hs : Real.sqrt (weight i) ^ 2 = weight i :=
      Real.sq_sqrt (hw i hi).le
    change (‖b i‖ / Real.sqrt (weight i)) ^ 2 = ‖b i‖ ^ 2 / weight i
    rw [div_pow, hs]
  have hsecond : ∑ i ∈ I, (Real.sqrt (weight i) * ‖A i‖) ^ 2 = Q := by
    apply Finset.sum_congr rfl
    intro i hi
    change (Real.sqrt (weight i) * ‖A i‖) ^ 2 = weight i * ‖A i‖ ^ 2
    rw [mul_pow, Real.sq_sqrt (hw i hi).le]
  have hquad : L ^ 2 ≤ R * Q := by
    calc
      L ^ 2 ≤ (∑ i ∈ I, ‖b i‖ * ‖A i‖) ^ 2 :=
        (sq_le_sq₀ hL0 (Finset.sum_nonneg fun i _ =>
          mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htri
      _ = (∑ i ∈ I,
          (‖b i‖ / Real.sqrt (weight i)) *
            (Real.sqrt (weight i) * ‖A i‖)) ^ 2 := by
        rw [Finset.sum_congr rfl hfactor]
      _ ≤ (∑ i ∈ I, (‖b i‖ / Real.sqrt (weight i)) ^ 2) *
          ∑ i ∈ I, (Real.sqrt (weight i) * ‖A i‖) ^ 2 := hcs
      _ = R * Q := by rw [hfirst, hsecond]
  have hquad' : L ^ 2 ≤ (B * R) * L := by
    calc
      L ^ 2 ≤ R * Q := hquad
      _ ≤ R * (B * L) := mul_le_mul_of_nonneg_left hQ hR0
      _ = (B * R) * L := by ring
  change L ≤ B * R
  rcases hL0.eq_or_lt with hL | hL
  · rw [← hL]
    exact mul_nonneg hB hR0
  · nlinarith

/-- **V-B-1, finite-dimensional core.**  A positive weighted kernel with
quadratic off-diagonal decay gives the corresponding synthesis estimate.
The constant `4` is the one-dimensional packing cost. -/
theorem weighted_large_values_of_kernel_decay {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (position : κ → ℝ)
    (weight : ι → ℝ) (b : ι → ℂ) (χ : ι → κ → ℂ)
    (D A E : ℝ)
    (hw : ∀ i ∈ I, 0 < weight i)
    (hχ : ∀ i ∈ I, ∀ t ∈ J, ‖χ i t‖ = 1)
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hdiag : ∑ i ∈ I, weight i ≤ D)
    (hkernel : ∀ t ∈ J, ∀ s ∈ J, t ≠ s →
      ‖∑ i ∈ I, (weight i : ℂ) * χ i t *
          (starRingEnd ℂ) (χ i s)‖ ≤
        A / |position t - position s| ^ 2 + E)
    (hsep : ∀ t ∈ J, ∀ s ∈ J, t ≠ s →
      1 ≤ |position t - position s|) :
    ∑ t ∈ J, ‖∑ i ∈ I, b i * χ i t‖ ^ 2 ≤
      (D + 4 * A + (J.card : ℝ) * E) *
        ∑ i ∈ I, ‖b i‖ ^ 2 / weight i := by
  classical
  let B : ℝ := D + 4 * A + (J.card : ℝ) * E
  have hB : 0 ≤ B := by positivity
  let φ : ι → κ → ℂ := fun i t =>
    (Real.sqrt (weight i) : ℂ) * χ i t
  let β : ι → ℂ := fun i => b i / (Real.sqrt (weight i) : ℂ)
  have hrow : ∀ t ∈ J,
      ∑ s ∈ J,
          ‖∑ i ∈ I, φ i t * (starRingEnd ℂ) (φ i s)‖ ≤ B := by
    intro t ht
    have hgram (s : κ) (hs : s ∈ J) :
        (∑ i ∈ I, φ i t * (starRingEnd ℂ) (φ i s)) =
          ∑ i ∈ I, (weight i : ℂ) *
            χ i t * (starRingEnd ℂ) (χ i s) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hsqrt : Real.sqrt (weight i) ^ 2 = weight i :=
        Real.sq_sqrt (hw i hi).le
      simp only [φ, map_mul, Complex.conj_ofReal]
      rw [show ((Real.sqrt (weight i) : ℂ) * χ i t) *
          ((Real.sqrt (weight i) : ℂ) * (starRingEnd ℂ) (χ i s)) =
          ((Real.sqrt (weight i) ^ 2 : ℝ) : ℂ) * χ i t *
            (starRingEnd ℂ) (χ i s) by push_cast; ring, hsqrt]
    have hdiagEq :
        ‖∑ i ∈ I, (weight i : ℂ) *
            χ i t * (starRingEnd ℂ) (χ i t)‖ =
          ∑ i ∈ I, weight i := by
      have hsum :
          (∑ i ∈ I, (weight i : ℂ) *
              χ i t * (starRingEnd ℂ) (χ i t)) =
            ((∑ i ∈ I, weight i : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hnormsq : Complex.normSq (χ i t) = 1 := by
          rw [Complex.normSq_eq_norm_sq, hχ i hi t ht]
          norm_num
        calc
          (weight i : ℂ) * χ i t * (starRingEnd ℂ) (χ i t) =
              (weight i : ℂ) *
                (χ i t * (starRingEnd ℂ) (χ i t)) := by ring
          _ = (weight i : ℂ) * Complex.normSq (χ i t) := by
                rw [Complex.mul_conj]
          _ = (weight i : ℂ) := by rw [hnormsq]; norm_num
      rw [hsum, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun i hi => (hw i hi).le)]
    have hoff :
        ∑ s ∈ J.erase t,
            ‖∑ i ∈ I, φ i t * (starRingEnd ℂ) (φ i s)‖ ≤
          4 * A + (J.card : ℝ) * E := by
      calc
        _ = ∑ s ∈ J.erase t,
            ‖∑ i ∈ I, (weight i : ℂ) *
              χ i t * (starRingEnd ℂ) (χ i s)‖ := by
                apply Finset.sum_congr rfl
                intro s hs
                rw [hgram s (Finset.mem_of_mem_erase hs)]
        _ ≤ ∑ s ∈ J.erase t,
            (A / |position t - position s| ^ 2 + E) := by
              apply Finset.sum_le_sum
              intro s hs
              exact hkernel t ht s (Finset.mem_of_mem_erase hs)
                (Finset.ne_of_mem_erase hs).symm
        _ = A * (∑ s ∈ J.erase t,
              (1 : ℝ) / |position t - position s| ^ 2) +
            ((J.erase t).card : ℝ) * E := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
              simp only [Finset.sum_const, nsmul_eq_mul]
              congr 1
              · apply Finset.sum_congr rfl
                intro s hs
                ring
        _ ≤ A * 4 + (J.card : ℝ) * E := by
              have hpack := sum_inv_sq_abs_sub_erase_le_four
                J position t ht hsep
              have hcard : ((J.erase t).card : ℝ) ≤ (J.card : ℝ) := by
                exact_mod_cast (Finset.card_erase_le (s := J) (a := t))
              exact add_le_add
                (mul_le_mul_of_nonneg_left hpack hA)
                (mul_le_mul_of_nonneg_right hcard hE)
        _ = 4 * A + (J.card : ℝ) * E := by ring
    rw [← Finset.sum_erase_add _ _ ht]
    rw [hgram t ht, hdiagEq]
    calc
      _ ≤ (4 * A + (J.card : ℝ) * E) + D := add_le_add hoff hdiag
      _ = B := by dsimp [B]; ring
  have hsynthesis := sum_norm_sq_le_norm_sq_mul_sup_kernel
    I J β φ B hB hrow
  have hinner (t : κ) :
      (∑ i ∈ I, β i * φ i t) = ∑ i ∈ I, b i * χ i t := by
    apply Finset.sum_congr rfl
    intro i hi
    have hsqrt : (Real.sqrt (weight i) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (hw i hi))
    simp only [β, φ]
    field_simp
  have hmass :
      (∑ i ∈ I, ‖β i‖ ^ 2) =
        ∑ i ∈ I, ‖b i‖ ^ 2 / weight i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hsqrt : Real.sqrt (weight i) ^ 2 = weight i :=
      Real.sq_sqrt (hw i hi).le
    simp only [β, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, hsqrt]
  simpa only [hinner, hmass, B, mul_comm] using hsynthesis

/-- **V-B-1, plateau specialization.**  A quadratic bound for the complete
plateau-weighted prime kernel implies the large-values estimate for every
subset of primes in `[P,2P]`.  The subset is put into the coefficients, while
duality is run over all positive-weight primes. -/
theorem prime_large_values_of_mellin_kernel
    (S : ℝ → ℝ) (P : ℕ) (Y : Finset ℕ) (a : ℕ → ℂ)
    (𝒯 : Finset ℝ) (position : ℝ → ℝ) (A E : ℝ)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hP : 2 ≤ P)
    (hYprime : ∀ p ∈ Y, p.Prime)
    (hYrange : ∀ p ∈ Y, P ≤ p ∧ p ≤ 2 * P)
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hsep : ∀ t ∈ 𝒯, ∀ s ∈ 𝒯, t ≠ s →
      1 ≤ |position t - position s|)
    (hkernel : ∀ t ∈ 𝒯, ∀ s ∈ 𝒯, t ≠ s →
      ‖∑ p ∈ (Finset.Ioc 0 ⌊4 * (P : ℝ)⌋₊).filter Nat.Prime,
          ((primeMellinWindow S P p * Real.log p : ℝ) : ℂ) *
            (p : ℂ) ^ (I * ((position t - position s : ℝ) : ℂ))‖ ≤
        A / |position t - position s| ^ 2 + E) :
    ∑ t ∈ 𝒯,
        ‖∑ p ∈ Y, (a p / (p : ℂ)) *
          (p : ℂ) ^ (I * (position t : ℂ))‖ ^ 2 ≤
      (16 * (P : ℝ) + 4 * A + (𝒯.card : ℝ) * E) *
        (∑ p ∈ Y, ‖a p / (p : ℂ)‖ ^ 2) / Real.log P := by
  classical
  let I₀ : Finset ℕ :=
    (Finset.Ioc 0 ⌊4 * (P : ℝ)⌋₊).filter Nat.Prime
  let Ipos : Finset ℕ := I₀.filter fun p => primeMellinWindow S P p ≠ 0
  let weight : ℕ → ℝ := fun p =>
    primeMellinWindow S P p * Real.log p
  let b : ℕ → ℂ := fun p => if p ∈ Y then a p / (p : ℂ) else 0
  let χ : ℕ → ℝ → ℂ := fun p t =>
    (p : ℂ) ^ (I * (position t : ℂ))
  have hwindow (n : ℕ) : 0 ≤ primeMellinWindow S P n ∧
      primeMellinWindow S P n ≤ 1 := by
    unfold primeMellinWindow primeMellinProfile
    have hL := hS01 (2 * (Real.log (↑n / (P : ℝ)) / Real.log 2) + 1)
    have hR := hS01 (3 - 2 * (Real.log (↑n / (P : ℝ)) / Real.log 2))
    constructor
    · exact mul_nonneg hL.1 hR.1
    · nlinarith [mul_nonneg hL.1 hR.1,
        mul_nonneg (sub_nonneg.mpr hL.2) hR.1]
  have hYI : Y ⊆ Ipos := by
    intro p hp
    have hpprime := hYprime p hp
    have hpRange := hYrange p hp
    have hpFloor : p ≤ ⌊4 * (P : ℝ)⌋₊ := by
      apply Nat.le_floor
      exact_mod_cast (show p ≤ 4 * P by omega)
    have hpI₀ : p ∈ I₀ := by
      simp only [I₀, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hpprime.pos, hpFloor⟩, hpprime⟩
    have hwOne : primeMellinWindow S P p = 1 := by
      apply primeMellinWindow_eq_one S (P : ℝ) p hS1
      · exact_mod_cast (show 0 < P by omega)
      · exact_mod_cast hpRange.1
      · exact_mod_cast hpRange.2
    simp only [Ipos, Finset.mem_filter]
    exact ⟨hpI₀, by rw [hwOne]; norm_num⟩
  have hw : ∀ p ∈ Ipos, 0 < weight p := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpPrime : p.Prime := (Finset.mem_filter.mp hpData.1).2
    have hwp : 0 < primeMellinWindow S P p :=
      lt_of_le_of_ne (hwindow p).1 (Ne.symm hpData.2)
    exact mul_pos hwp (Real.log_pos (by exact_mod_cast hpPrime.one_lt))
  have hχ : ∀ p ∈ Ipos, ∀ t ∈ 𝒯, ‖χ p t‖ = 1 := by
    intro p hp t ht
    have hpPrime : p.Prime :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    simp only [χ]
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    simp
  have hdiag : ∑ p ∈ Ipos, weight p ≤ 16 * (P : ℝ) := by
    have hpoint : ∀ p ∈ Ipos, weight p ≤ Real.log p := by
      intro p hp
      have hpPrime : p.Prime :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      dsimp only [weight]
      exact mul_le_of_le_one_left
        (Real.log_nonneg (by exact_mod_cast hpPrime.one_lt.le)) (hwindow p).2
    have hsubset : Ipos ⊆ I₀ := Finset.filter_subset _ _
    have hnonneg : ∀ p ∈ I₀, p ∉ Ipos → 0 ≤ Real.log p := by
      intro p hp hpn
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      exact Real.log_nonneg (by exact_mod_cast hpPrime.one_lt.le)
    have htheta : ∑ p ∈ I₀, Real.log p = Chebyshev.theta (4 * (P : ℝ)) := by
      rfl
    have hlog4 : Real.log 4 ≤ 3 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
    calc
      ∑ p ∈ Ipos, weight p ≤ ∑ p ∈ Ipos, Real.log p :=
        Finset.sum_le_sum hpoint
      _ ≤ ∑ p ∈ I₀, Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
      _ = Chebyshev.theta (4 * (P : ℝ)) := htheta
      _ ≤ Real.log 4 * (4 * (P : ℝ)) :=
        Chebyshev.theta_le_log4_mul_x (by positivity)
      _ ≤ 16 * (P : ℝ) := by
        have hPR : (0 : ℝ) ≤ P := by positivity
        nlinarith
  have hkernelPos : ∀ t ∈ 𝒯, ∀ s ∈ 𝒯, t ≠ s →
      ‖∑ p ∈ Ipos, (weight p : ℂ) * χ p t *
          (starRingEnd ℂ) (χ p s)‖ ≤
        A / |position t - position s| ^ 2 + E := by
    intro t ht s hs hts
    have hphase (p : ℕ) (hp : p ∈ Ipos) :
        χ p t * (starRingEnd ℂ) (χ p s) =
          (p : ℂ) ^ (I * ((position t - position s : ℝ) : ℂ)) := by
      have hpPrime : p.Prime :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      simpa only [χ] using
        natCast_cpow_mul_conj_cpow hpPrime.pos (position t) (position s)
    have hsum :
        (∑ p ∈ Ipos, (weight p : ℂ) * χ p t *
            (starRingEnd ℂ) (χ p s)) =
          ∑ p ∈ I₀, ((primeMellinWindow S P p * Real.log p : ℝ) : ℂ) *
            (p : ℂ) ^ (I * ((position t - position s : ℝ) : ℂ)) := by
      calc
        _ = ∑ p ∈ Ipos,
            ((primeMellinWindow S P p * Real.log p : ℝ) : ℂ) *
              (p : ℂ) ^ (I * ((position t - position s : ℝ) : ℂ)) := by
              apply Finset.sum_congr rfl
              intro p hp
              rw [mul_assoc, hphase p hp]
        _ = _ := Finset.sum_subset (Finset.filter_subset _ _)
          (fun p hpI₀ hpnot => by
            have hwzero : primeMellinWindow S P p = 0 := by
              by_contra hn
              exact hpnot (Finset.mem_filter.mpr ⟨hpI₀, hn⟩)
            simp [hwzero])
    rw [hsum]
    exact hkernel t ht s hs hts
  have hmain := weighted_large_values_of_kernel_decay
    Ipos 𝒯 position weight b χ (16 * (P : ℝ)) A E hw hχ
    (by positivity) hA hE hdiag hkernelPos hsep
  have hleft :
      (∑ t ∈ 𝒯, ‖∑ p ∈ Ipos, b p * χ p t‖ ^ 2) =
        ∑ t ∈ 𝒯, ‖∑ p ∈ Y, (a p / (p : ℂ)) *
          (p : ℂ) ^ (I * (position t : ℂ))‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro t ht
    apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
    calc
      (∑ p ∈ Ipos, b p * χ p t) = ∑ p ∈ Y, b p * χ p t :=
        (Finset.sum_subset hYI
          (fun p hpI hpnot => by simp [b, hpnot])).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [b, χ, if_pos hp]
  have hmass :
      (∑ p ∈ Ipos, ‖b p‖ ^ 2 / weight p) ≤
        (∑ p ∈ Y, ‖a p / (p : ℂ)‖ ^ 2) / Real.log P := by
    have hlogP : 0 < Real.log P :=
      Real.log_pos (by exact_mod_cast (show 1 < P by omega))
    calc
      _ ≤ ∑ p ∈ Ipos, if p ∈ Y then
            ‖a p / (p : ℂ)‖ ^ 2 / Real.log P else 0 := by
        apply Finset.sum_le_sum
        intro p hp
        by_cases hpY : p ∈ Y
        · have hpRange := hYrange p hpY
          have hwOne : primeMellinWindow S P p = 1 := by
            apply primeMellinWindow_eq_one S (P : ℝ) p hS1
            · exact_mod_cast (show 0 < P by omega)
            · exact_mod_cast hpRange.1
            · exact_mod_cast hpRange.2
          have hlogp : Real.log P ≤ Real.log p := by
            exact Real.log_le_log (by exact_mod_cast (show 0 < P by omega))
              (by exact_mod_cast hpRange.1)
          have hnum : 0 ≤ ‖a p / (p : ℂ)‖ ^ 2 := sq_nonneg _
          simp only [b, if_pos hpY, weight, hwOne, one_mul]
          exact div_le_div_of_nonneg_left hnum hlogP hlogp
        · simp [b, hpY]
      _ = ∑ p ∈ Y, ‖a p / (p : ℂ)‖ ^ 2 / Real.log P := by
        rw [← Finset.sum_subset hYI]
        · apply Finset.sum_congr rfl
          intro p hp
          simp [hp]
        · intro p hpI hpnot
          simp [hpnot]
      _ = (∑ p ∈ Y, ‖a p / (p : ℂ)‖ ^ 2) / Real.log P := by
        rw [Finset.sum_div]
  rw [← hleft]
  calc
    _ ≤ (16 * (P : ℝ) + 4 * A + (𝒯.card : ℝ) * E) *
        ((∑ p ∈ Y, ‖a p / (p : ℂ)‖ ^ 2) / Real.log P) :=
      hmain.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
    _ = _ := by ring

/-! ## The analytic kernel supplied by the zero-free rectangle -/

/-- The zero-free rectangle identity after the zeta pole has been removed.
Unlike the full contour identity, its boundary integral is zero. -/
theorem primeMellin_regular_rectangle (W : ℂ → ℂ)
    (hW : Differentiable ℂ W) (η c Z u : ℝ)
    (hη : 0 < η) (hc1 : 1 < c) (hc2 : c ≤ 2) (hZ : 0 < Z)
    (hzero : ∀ s : ℂ, 1 - η ≤ s.re → s.re ≤ 2 → |s.im| ≤ Z →
      s ≠ 1 → riemannZeta s ≠ 0) :
    let s₀ : ℂ := 1 - (u : ℂ) * I
    let A : ℝ := c - 1
    let B : ℝ := η / 2
    (∫ x : ℝ in -B..A,
        W (s₀ + ((x : ℂ) - (Z : ℂ) * I)) *
          (-deriv riemannZeta (1 + (x : ℂ) - (Z : ℂ) * I) /
              riemannZeta (1 + (x : ℂ) - (Z : ℂ) * I) -
            1 / ((x : ℂ) - (Z : ℂ) * I))) -
      (∫ x : ℝ in -B..A,
        W (s₀ + ((x : ℂ) + (Z : ℂ) * I)) *
          (-deriv riemannZeta (1 + (x : ℂ) + (Z : ℂ) * I) /
              riemannZeta (1 + (x : ℂ) + (Z : ℂ) * I) -
            1 / ((x : ℂ) + (Z : ℂ) * I))) +
      I * (∫ y : ℝ in -Z..Z,
        W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
          (-deriv riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) /
              riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) -
            1 / ((A : ℂ) + (y : ℂ) * I))) -
      I * (∫ y : ℝ in -Z..Z,
        W (s₀ + (-(B : ℂ) + (y : ℂ) * I)) *
          (-deriv riemannZeta (1 - (B : ℂ) + (y : ℂ) * I) /
              riemannZeta (1 - (B : ℂ) + (y : ℂ) * I) -
            1 / (-(B : ℂ) + (y : ℂ) * I))) = 0 := by
  dsimp only
  let s₀ : ℂ := 1 - (u : ℂ) * I
  let A : ℝ := c - 1
  let B : ℝ := η / 2
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := by dsimp [B]; linarith
  obtain ⟨G, hG, hGval⟩ := exists_zeta_pole_reg
  let R : Set ℂ := Set.uIcc (-B) A ×ℂ Set.uIcc (-Z) Z
  have hcoord (z : ℂ) (hz : z ∈ R) :
      -B ≤ z.re ∧ z.re ≤ A ∧ -Z ≤ z.im ∧ z.im ≤ Z := by
    rcases hz with ⟨hzre, hzim⟩
    rw [Set.uIcc_of_le (by linarith : -B ≤ A)] at hzre
    rw [Set.uIcc_of_le (by linarith : -Z ≤ Z)] at hzim
    exact ⟨hzre.1, hzre.2, hzim.1, hzim.2⟩
  have hremoved (z : ℂ) (hz : z ∈ R) :
      zetaPoleRemoved G (1 + z) ≠ 0 := by
    rcases eq_or_ne z 0 with rfl | hz0
    · simp [zetaPoleRemoved]
    · have hone : (1 : ℂ) + z ≠ 1 := by
        intro h
        apply hz0
        linear_combination h
      have hcz := hcoord z hz
      rw [zetaPoleRemoved_eq G hGval (1 + z) hone]
      apply mul_ne_zero
      · simpa only [add_sub_cancel_left] using hz0
      · apply hzero (1 + z)
        · simp only [Complex.add_re, Complex.one_re]
          dsimp [B] at hcz
          linarith
        · simp only [Complex.add_re, Complex.one_re]
          dsimp [A] at hcz
          linarith
        · simp only [Complex.add_im, Complex.one_im, zero_add]
          rw [abs_le]
          exact ⟨hcz.2.2.1, hcz.2.2.2⟩
        · exact hone
  let q : ℂ → ℂ := fun z =>
    W (s₀ + z) * zetaLogDerivRegular G (1 + z)
  have hqAt (z : ℂ) (hz : z ∈ R) : DifferentiableAt ℂ q z := by
    exact ((hW (s₀ + z)).comp z (by fun_prop)).mul
      ((zetaLogDerivRegular_differentiableAt G hG (1 + z)
        (hremoved z hz)).comp z (by fun_prop))
  have hq : DifferentiableOn ℂ q R :=
    fun z hz => (hqAt z hz).differentiableWithinAt
  have hqrect : DifferentiableOn ℂ q
      (Set.uIcc ((-B : ℂ) - (Z : ℂ) * I).re
          ((A : ℂ) + (Z : ℂ) * I).re ×ℂ
        Set.uIcc ((-B : ℂ) - (Z : ℂ) * I).im
          ((A : ℂ) + (Z : ℂ) * I).im) := by
    simpa [R, Set.uIcc_of_le (by linarith : -B ≤ A),
      Set.uIcc_of_le (by linarith : -Z ≤ Z)] using hq
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn q
    ((-B : ℂ) - (Z : ℂ) * I) ((A : ℂ) + (Z : ℂ) * I) hqrect
  have hrect' :
      (∫ x : ℝ in -B..A,
          W (s₀ + ((x : ℂ) - (Z : ℂ) * I)) *
            zetaLogDerivRegular G (1 + (x : ℂ) - (Z : ℂ) * I)) -
        (∫ x : ℝ in -B..A,
          W (s₀ + ((x : ℂ) + (Z : ℂ) * I)) *
            zetaLogDerivRegular G (1 + (x : ℂ) + (Z : ℂ) * I)) +
        I * (∫ y : ℝ in -Z..Z,
          W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
            zetaLogDerivRegular G (1 + (A : ℂ) + (y : ℂ) * I)) -
        I * (∫ y : ℝ in -Z..Z,
          W (s₀ + (-(B : ℂ) + (y : ℂ) * I)) *
            zetaLogDerivRegular G (1 - (B : ℂ) + (y : ℂ) * I)) = 0 := by
    simpa [q, smul_eq_mul, sub_eq_add_neg, add_assoc] using hrect
  have hregEq (z : ℂ) (hz : z ∈ R) (hz0 : z ≠ 0) :
      zetaLogDerivRegular G (1 + z) =
        -deriv riemannZeta (1 + z) / riemannZeta (1 + z) - 1 / z := by
    have hone : (1 : ℂ) + z ≠ 1 := by
      intro h
      apply hz0
      linear_combination h
    have hcz := hcoord z hz
    have hζ : riemannZeta (1 + z) ≠ 0 := by
      apply hzero (1 + z)
      · simp only [Complex.add_re, Complex.one_re]
        dsimp [B] at hcz
        linarith
      · simp only [Complex.add_re, Complex.one_re]
        dsimp [A] at hcz
        linarith
      · simp only [Complex.add_im, Complex.one_im, zero_add]
        rw [abs_le]
        exact ⟨hcz.2.2.1, hcz.2.2.2⟩
      · exact hone
    rw [zetaLogDerivRegular_eq G hG hGval (1 + z) hone hζ]
    rw [show (1 : ℂ) + z - 1 = z by ring]
  have hmemH (x : ℝ) (hx : x ∈ Set.uIcc (-B) A) (sgn : ℝ) (hsgn : |sgn| = Z) :
      (x : ℂ) + (sgn : ℂ) * I ∈ R := by
    rw [show R = Set.uIcc (-B) A ×ℂ Set.uIcc (-Z) Z from rfl, mem_reProdIm]
    constructor
    · simpa using hx
    · rw [Set.uIcc_of_le (by linarith : -Z ≤ Z)]
      have habs : |sgn| ≤ Z := by rw [hsgn]
      rw [abs_le] at habs
      simpa only [Set.mem_Icc, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, zero_mul,
        mul_one, zero_add, add_zero] using habs
  have hmemV (y : ℝ) (hy : y ∈ Set.uIcc (-Z) Z) (x : ℝ)
      (hx : x = A ∨ x = -B) : (x : ℂ) + (y : ℂ) * I ∈ R := by
    rw [show R = Set.uIcc (-B) A ×ℂ Set.uIcc (-Z) Z from rfl, mem_reProdIm]
    constructor
    · rw [Set.uIcc_of_le (by linarith : -B ≤ A)]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
      rcases hx with rfl | rfl <;> constructor <;> linarith
    · simpa using hy
  have hbot :
      (∫ x : ℝ in -B..A,
        W (s₀ + ((x : ℂ) - (Z : ℂ) * I)) *
          (-deriv riemannZeta (1 + (x : ℂ) - (Z : ℂ) * I) /
              riemannZeta (1 + (x : ℂ) - (Z : ℂ) * I) -
            1 / ((x : ℂ) - (Z : ℂ) * I))) =
      ∫ x : ℝ in -B..A,
        W (s₀ + ((x : ℂ) - (Z : ℂ) * I)) *
          zetaLogDerivRegular G (1 + (x : ℂ) - (Z : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hmem : (x : ℂ) - (Z : ℂ) * I ∈ R := by
      simpa [mul_comm] using hmemH x hx (-Z) (by simp [abs_of_pos hZ])
    have heq := hregEq ((x : ℂ) - (Z : ℂ) * I)
      hmem (by
        intro h; have := congrArg Complex.im h; simp [hZ.ne'] at this)
    rw [show (1 : ℂ) + ((x : ℂ) - (Z : ℂ) * I) =
      1 + (x : ℂ) - (Z : ℂ) * I by ring] at heq
    exact congrArg (fun q : ℂ => W (s₀ + ((x : ℂ) - (Z : ℂ) * I)) * q) heq.symm
  have htop :
      (∫ x : ℝ in -B..A,
        W (s₀ + ((x : ℂ) + (Z : ℂ) * I)) *
          (-deriv riemannZeta (1 + (x : ℂ) + (Z : ℂ) * I) /
              riemannZeta (1 + (x : ℂ) + (Z : ℂ) * I) -
            1 / ((x : ℂ) + (Z : ℂ) * I))) =
      ∫ x : ℝ in -B..A,
        W (s₀ + ((x : ℂ) + (Z : ℂ) * I)) *
          zetaLogDerivRegular G (1 + (x : ℂ) + (Z : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have heq := hregEq ((x : ℂ) + (Z : ℂ) * I)
      (hmemH x hx Z (abs_of_pos hZ)) (by
        intro h; have := congrArg Complex.im h; simp [hZ.ne'] at this)
    rw [show (1 : ℂ) + ((x : ℂ) + (Z : ℂ) * I) =
      1 + (x : ℂ) + (Z : ℂ) * I by ring] at heq
    exact congrArg
      (fun q : ℂ => W (s₀ + ((x : ℂ) + (Z : ℂ) * I)) * q) heq.symm
  have hright :
      (∫ y : ℝ in -Z..Z,
        W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
          (-deriv riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) /
              riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) -
            1 / ((A : ℂ) + (y : ℂ) * I))) =
      ∫ y : ℝ in -Z..Z,
        W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
          zetaLogDerivRegular G (1 + (A : ℂ) + (y : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have heq := hregEq ((A : ℂ) + (y : ℂ) * I) (hmemV y hy A (Or.inl rfl)) (by
      intro h; have := congrArg Complex.re h; simp [hA.ne'] at this)
    rw [show (1 : ℂ) + ((A : ℂ) + (y : ℂ) * I) =
      1 + (A : ℂ) + (y : ℂ) * I by ring] at heq
    exact congrArg
      (fun q : ℂ => W (s₀ + ((A : ℂ) + (y : ℂ) * I)) * q) heq.symm
  have hleft :
      (∫ y : ℝ in -Z..Z,
        W (s₀ + (-(B : ℂ) + (y : ℂ) * I)) *
          (-deriv riemannZeta (1 - (B : ℂ) + (y : ℂ) * I) /
              riemannZeta (1 - (B : ℂ) + (y : ℂ) * I) -
            1 / (-(B : ℂ) + (y : ℂ) * I))) =
      ∫ y : ℝ in -Z..Z,
        W (s₀ + (-(B : ℂ) + (y : ℂ) * I)) *
          zetaLogDerivRegular G (1 - (B : ℂ) + (y : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have heq := hregEq (-(B : ℂ) + (y : ℂ) * I)
      (by simpa using hmemV y hy (-B) (Or.inr rfl)) (by
        intro h; have := congrArg Complex.re h; simp [hB.ne'] at this)
    rw [show (1 : ℂ) + (-(B : ℂ) + (y : ℂ) * I) =
      1 - (B : ℂ) + (y : ℂ) * I by ring] at heq
    exact congrArg
      (fun q : ℂ => W (s₀ + (-(B : ℂ) + (y : ℂ) * I)) * q) heq.symm
  rw [hbot, htop, hright, hleft]
  exact hrect'

/-- On the auxiliary line `Re s = 1/2`, the rational pole integral has
absolute size `O(P^{1/2})`, uniformly in its vertical translate. -/
theorem primeMellin_rational_half_line_bound
    (S : ℝ → ℝ) (C P Z u : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) (hZ : 0 < Z) :
    ‖∫ y : ℝ in -Z..Z,
        primeMellinTransform S P
            ((1 - (u : ℂ) * I) +
              (-((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) /
          (-((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      2000000 * (C + 1) ^ 2 * P ^ (1 / 2 : ℝ) := by
  let D : ℝ := 500000 * (C + 1) ^ 2 * P ^ (1 / 2 : ℝ)
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hmajor : IntervalIntegrable
      (fun y : ℝ => D * (1 + (y - u) ^ 2)⁻¹) volume (-Z) Z := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      ((continuous_const.add ((continuous_id.sub continuous_const).pow 2)).inv₀
        fun y => by positivity)
  have hpoint : ∀ y ∈ Set.Ioc (-Z) Z,
      ‖primeMellinTransform S P
            ((1 - (u : ℂ) * I) +
              (-((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) /
          (-((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        D * (1 + (y - u) ^ 2)⁻¹ := by
    intro y hy
    have hw0 := primeMellinTransform_vertical_decay S C P (1 / 2) (y - u)
      hSs hS01 hS0 hS1 hC0 hC1 hC2 hP (by norm_num) (by norm_num)
    have hw :
        ‖primeMellinTransform S P
            ((1 - (u : ℂ) * I) +
              (-((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I))‖ ≤
          250000 * (C + 1) ^ 2 * P ^ (1 / 2 : ℝ) /
            (1 + (y - u) ^ 2) := by
      convert hw0 using 1 <;> push_cast <;> ring
    have hden : (1 / 2 : ℝ) ≤
        ‖-((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I‖ := by
      have hre := Complex.abs_re_le_norm
        (-((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)
      norm_num at hre ⊢
      exact hre
    have hden0 : 0 < ‖-((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I‖ :=
      lt_of_lt_of_le (by norm_num) hden
    rw [norm_div]
    calc
      _ ≤ (250000 * (C + 1) ^ 2 * P ^ (1 / 2 : ℝ) /
            (1 + (y - u) ^ 2)) /
          ‖-((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I‖ :=
        div_le_div_of_nonneg_right hw hden0.le
      _ ≤ (250000 * (C + 1) ^ 2 * P ^ (1 / 2 : ℝ) /
            (1 + (y - u) ^ 2)) / (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
      _ = D * (1 + (y - u) ^ 2)⁻¹ := by
        dsimp [D]
        rw [div_eq_mul_inv]
        ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le
    (by linarith : -Z ≤ Z) (ae_of_all _ fun y => fun hy => hpoint y hy) hmajor
  calc
    _ ≤ ∫ y : ℝ in -Z..Z, D * (1 + (y - u) ^ 2)⁻¹ := hint
    _ = D * ∫ y : ℝ in -Z..Z, (1 + (y - u) ^ 2)⁻¹ := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ D * 4 := mul_le_mul_of_nonneg_left
      (integral_inv_one_add_sq_sub_le_four (-Z) Z u (by linarith)) hD0
    _ = 2000000 * (C + 1) ^ 2 * P ^ (1 / 2 : ℝ) := by
      dsimp [D]
      ring

/-- The two rational horizontal sides have quadratic height decay. -/
theorem primeMellin_rational_horizontal_sides_bound
    (S : ℝ → ℝ) (C P c Z u : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) (hc1 : 1 < c) (hc2 : c ≤ 2)
    (hZ : 1 ≤ Z) (hu : |u| ≤ Z / 2) :
    ‖∫ x : ℝ in -(1 / 2)..(c - 1),
        primeMellinTransform S P
            ((1 - (u : ℂ) * I) + ((x : ℂ) - (Z : ℂ) * I)) /
          ((x : ℂ) - (Z : ℂ) * I)‖ +
      ‖∫ x : ℝ in -(1 / 2)..(c - 1),
        primeMellinTransform S P
            ((1 - (u : ℂ) * I) + ((x : ℂ) + (Z : ℂ) * I)) /
          ((x : ℂ) + (Z : ℂ) * I)‖ ≤
      4000000 * (C + 1) ^ 2 * P ^ c / Z ^ 2 := by
  have hτbot : Z / 2 ≤ |-Z - u| := by
    have htri := abs_add_le (-Z - u) u
    rw [show -Z - u + u = -Z by ring, abs_neg, abs_of_pos (by linarith : 0 < Z)] at htri
    linarith
  have hτtop : Z / 2 ≤ |Z - u| := by
    have htri := abs_add_le (Z - u) u
    rw [show Z - u + u = Z by ring, abs_of_pos (by linarith : 0 < Z)] at htri
    linarith
  have hside (sgn : ℝ) (hτ : Z / 2 ≤ |sgn - u|) (hsgn : |sgn| = Z) :
      ‖∫ x : ℝ in -(1 / 2)..(c - 1),
          primeMellinTransform S P
              ((1 - (u : ℂ) * I) + ((x : ℂ) + (sgn : ℂ) * I)) /
            ((x : ℂ) + (sgn : ℂ) * I)‖ ≤
        2000000 * (C + 1) ^ 2 * P ^ c / Z ^ 2 := by
    let D : ℝ := 1000000 * (C + 1) ^ 2 * P ^ c / Z ^ 2
    have hD0 : 0 ≤ D := by dsimp [D]; positivity
    have hBA : -(1 / 2 : ℝ) ≤ c - 1 := by linarith
    have hpoint : ∀ x ∈ Set.uIoc (-(1 / 2 : ℝ)) (c - 1),
        ‖primeMellinTransform S P
              ((1 - (u : ℂ) * I) + ((x : ℂ) + (sgn : ℂ) * I)) /
            ((x : ℂ) + (sgn : ℂ) * I)‖ ≤ D := by
      intro x hx
      rw [Set.uIoc_of_le hBA] at hx
      have hα0 : (1 / 2 : ℝ) ≤ 1 + x := by linarith [hx.1]
      have hα2 : 1 + x ≤ 2 := by linarith [hx.2]
      have hw0 := primeMellinTransform_vertical_decay S C P (1 + x) (sgn - u)
        hSs hS01 hS0 hS1 hC0 hC1 hC2 hP hα0 hα2
      have hw :
          ‖primeMellinTransform S P
              ((1 - (u : ℂ) * I) + ((x : ℂ) + (sgn : ℂ) * I))‖ ≤
            250000 * (C + 1) ^ 2 * P ^ (1 + x) /
              (1 + (sgn - u) ^ 2) := by
        convert hw0 using 1 <;> push_cast <;> ring
      have hp : P ^ (1 + x) ≤ P ^ c :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hx.2])
      have hinv := inv_one_add_sq_le_four_div_sq Z (sgn - u) (by linarith) hτ
      have hden : 1 ≤ ‖(x : ℂ) + (sgn : ℂ) * I‖ := by
        have him := Complex.abs_im_le_norm ((x : ℂ) + (sgn : ℂ) * I)
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, zero_mul, mul_one, zero_add] at him
        calc
          1 ≤ Z := hZ
          _ = |sgn| := hsgn.symm
          _ ≤ ‖(x : ℂ) + (sgn : ℂ) * I‖ := by simpa only [add_zero] using him
      rw [norm_div]
      calc
        _ ≤ (250000 * (C + 1) ^ 2 * P ^ (1 + x) /
              (1 + (sgn - u) ^ 2)) /
            ‖(x : ℂ) + (sgn : ℂ) * I‖ :=
          div_le_div_of_nonneg_right hw (norm_nonneg _)
        _ ≤ (250000 * (C + 1) ^ 2 * P ^ (1 + x) /
              (1 + (sgn - u) ^ 2)) / 1 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
        _ ≤ 250000 * (C + 1) ^ 2 * P ^ c * (4 / Z ^ 2) := by
          rw [div_one, div_eq_mul_inv]
          gcongr
        _ = D := by dsimp [D]; ring
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    calc
      _ ≤ D * |(c - 1) - -(1 / 2 : ℝ)| := hb
      _ ≤ D * 2 := by
        gcongr
        rw [abs_of_nonneg (by linarith : 0 ≤ (c - 1) - -(1 / 2 : ℝ))]
        linarith
      _ = 2000000 * (C + 1) ^ 2 * P ^ c / Z ^ 2 := by
        dsimp [D]
        ring
  have hb :
      ‖∫ x : ℝ in -(1 / 2)..(c - 1),
          primeMellinTransform S P
              ((1 - (u : ℂ) * I) + ((x : ℂ) - (Z : ℂ) * I)) /
            ((x : ℂ) - (Z : ℂ) * I)‖ ≤
        2000000 * (C + 1) ^ 2 * P ^ c / Z ^ 2 := by
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using
      hside (-Z) (by simpa only [sub_eq_add_neg] using hτbot)
        (by simp [abs_of_pos (by linarith : 0 < Z)])
  have ht := hside Z hτtop (abs_of_pos (by linarith : 0 < Z))
  convert add_le_add hb ht using 1 <;> ring

/-- Shifting the rational pole factor to `Re s = 1/2` extracts its residue;
the remaining vertical side is `O(P^{1/2})`. -/
theorem primeMellin_rational_truncated_bound
    (S : ℝ → ℝ) (C P c Z u : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) (hc1 : 1 < c) (hc2 : c ≤ 2)
    (hZ : 1 ≤ Z) (hu : |u| ≤ Z / 2) :
    ‖(1 / (2 * Real.pi) : ℂ) *
          (∫ y : ℝ in -Z..Z,
            primeMellinTransform S P
                ((1 - (u : ℂ) * I) +
                  (((c - 1 : ℝ) : ℂ) + (y : ℂ) * I)) /
              (((c - 1 : ℝ) : ℂ) + (y : ℂ) * I)) -
        primeMellinTransform S P (1 - (u : ℂ) * I)‖ ≤
      6000000 * (C + 1) ^ 2 *
        (P ^ (1 / 2 : ℝ) + P ^ c / Z ^ 2) := by
  let W : ℂ → ℂ := primeMellinTransform S P
  let s₀ : ℂ := 1 - (u : ℂ) * I
  let A : ℝ := c - 1
  let Hb : ℂ := ∫ x : ℝ in -(1 / 2)..A,
    W (s₀ + ((x : ℂ) - (Z : ℂ) * I)) / ((x : ℂ) - (Z : ℂ) * I)
  let Ht : ℂ := ∫ x : ℝ in -(1 / 2)..A,
    W (s₀ + ((x : ℂ) + (Z : ℂ) * I)) / ((x : ℂ) + (Z : ℂ) * I)
  let R : ℂ := ∫ y : ℝ in -Z..Z,
    W (s₀ + ((A : ℂ) + (y : ℂ) * I)) / ((A : ℂ) + (y : ℂ) * I)
  let L : ℂ := ∫ y : ℝ in -Z..Z,
    W (s₀ + (-((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) /
      (-((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)
  have hW : Differentiable ℂ W :=
    primeMellinTransform_differentiable S P hSs hS0 (by linarith)
  have hpole := primeMellin_pole_rectangle W hW s₀ A (1 / 2) Z
    (by dsimp [A]; linarith) (by norm_num) (by linarith)
  change Hb - Ht + I * R - I * L = 2 * Real.pi * I * W s₀ at hpole
  have hpole' := congrArg (fun z : ℂ ↦ (-I) * z) hpole
  simp only [mul_sub, mul_add, neg_mul, ← mul_assoc, Complex.I_mul_I,
    neg_neg, neg_one_mul, one_mul] at hpole'
  have hscalar :
      -(I * 2 * Real.pi * I * W s₀) = 2 * Real.pi * W s₀ := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hscalar] at hpole'
  have hrelation : R - 2 * Real.pi * W s₀ = L + I * Hb - I * Ht := by
    linear_combination hpole'
  have hleft : ‖L‖ ≤ 2000000 * (C + 1) ^ 2 * P ^ (1 / 2 : ℝ) := by
    simpa only [L, W, s₀] using
      primeMellin_rational_half_line_bound S C P Z u hSs hS01
        hS0 hS1 hC0 hC1 hC2 hP (by linarith)
  have hhoriz : ‖Hb‖ + ‖Ht‖ ≤
      4000000 * (C + 1) ^ 2 * P ^ c / Z ^ 2 := by
    simpa only [Hb, Ht, W, s₀, A] using
      primeMellin_rational_horizontal_sides_bound S C P c Z u
        hSs hS01 hS0 hS1 hC0 hC1 hC2 hP hc1 hc2 hZ hu
  have hcoef : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [div_le_one (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith [Real.two_le_pi]
  have hraw : ‖R - 2 * Real.pi * W s₀‖ ≤
      6000000 * (C + 1) ^ 2 *
        (P ^ (1 / 2 : ℝ) + P ^ c / Z ^ 2) := by
    rw [hrelation]
    calc
      _ ≤ (‖L‖ + ‖Hb‖) + ‖Ht‖ := by
        calc
          _ ≤ ‖L + I * Hb‖ + ‖I * Ht‖ := norm_sub_le _ _
          _ ≤ (‖L‖ + ‖I * Hb‖) + ‖I * Ht‖ :=
            add_le_add (norm_add_le _ _) (le_refl _)
          _ = (‖L‖ + ‖Hb‖) + ‖Ht‖ := by simp
      _ = ‖L‖ + (‖Hb‖ + ‖Ht‖) := by ring
      _ ≤ 2000000 * (C + 1) ^ 2 * P ^ (1 / 2 : ℝ) +
          4000000 * (C + 1) ^ 2 * P ^ c / Z ^ 2 := add_le_add hleft hhoriz
      _ ≤ 6000000 * (C + 1) ^ 2 * P ^ (1 / 2 : ℝ) +
          6000000 * (C + 1) ^ 2 * (P ^ c / Z ^ 2) := by
            have ha : 0 ≤ (C + 1) ^ 2 * P ^ (1 / 2 : ℝ) := by positivity
            have hb : 0 ≤ (C + 1) ^ 2 * P ^ c / Z ^ 2 := by positivity
            calc
              _ = 2000000 * ((C + 1) ^ 2 * P ^ (1 / 2 : ℝ)) +
                  4000000 * ((C + 1) ^ 2 * P ^ c / Z ^ 2) := by ring
              _ ≤ 6000000 * ((C + 1) ^ 2 * P ^ (1 / 2 : ℝ)) +
                  6000000 * ((C + 1) ^ 2 * P ^ c / Z ^ 2) :=
                add_le_add
                  (mul_le_mul_of_nonneg_right (by norm_num) ha)
                  (mul_le_mul_of_nonneg_right (by norm_num) hb)
              _ = _ := by ring
      _ = 6000000 * (C + 1) ^ 2 *
          (P ^ (1 / 2 : ℝ) + P ^ c / Z ^ 2) := by ring
  have hfactor :
      (1 / (2 * Real.pi) : ℂ) *
          (∫ y : ℝ in -Z..Z,
            primeMellinTransform S P
                ((1 - (u : ℂ) * I) +
                  (((c - 1 : ℝ) : ℂ) + (y : ℂ) * I)) /
              (((c - 1 : ℝ) : ℂ) + (y : ℂ) * I)) -
        primeMellinTransform S P (1 - (u : ℂ) * I) =
      (1 / (2 * Real.pi) : ℂ) * (R - 2 * Real.pi * W s₀) := by
    change (1 / (2 * Real.pi) : ℂ) * R - W s₀ = _
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [hfactor, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hcoef).trans hraw

/-- The right-line tail outside the asymmetric contour heights
`[-Z-u, Z-u]` is controlled by the smaller distance `Z-|u|`. -/
theorem exists_primeMellin_asymmetric_right_tail_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀
      (S : ℝ → ℝ) (C P u Z : ℝ),
      ContDiff ℝ ∞ S →
      (∀ v, 0 ≤ S v ∧ S v ≤ 1) →
      (∀ v, v ≤ 0 → S v = 0) →
      (∀ v, 1 ≤ v → S v = 1) →
      0 ≤ C → (∀ v, |deriv S v| ≤ C) →
      (∀ v, |deriv (deriv S) v| ≤ C) →
      2 ≤ P → |u| < Z →
      let c := 1 + 1 / Real.log (2 * P)
      ‖(1 / (2 * Real.pi) : ℂ) *
          ∫ τ : ℝ in Set.Iic (-Z - u) ∪ Set.Ioi (Z - u),
            primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I) *
              (-deriv riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) /
                riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I))‖ ≤
        B * (C + 1) ^ 2 * P ^ c * Real.log (2 * P) / (Z - |u|) := by
  obtain ⟨A, hA1, hALS⟩ := exists_norm_LSeries_vonMangoldt_le_log
  refine ⟨500000 * A, by nlinarith, ?_⟩
  intro S C P u Z hSs hS01 hS0 hS1 hC0 hC1 hC2 hP huZ
  let c : ℝ := 1 + 1 / Real.log (2 * P)
  let H : ℝ := Z - |u|
  have hH : 0 < H := by dsimp [H]; linarith
  have hlog1 : 1 < Real.log (2 * P) := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      _ ≤ Real.log (2 * P) := Real.strictMonoOn_log.monotoneOn
        (show 3 ∈ Set.Ioi (0 : ℝ) by norm_num)
        (show 2 * P ∈ Set.Ioi (0 : ℝ) by
          change 0 < 2 * P
          nlinarith)
        (by linarith)
  have hc1 : 1 < c := by
    dsimp [c]
    have : 0 < 1 / Real.log (2 * P) := one_div_pos.mpr (by linarith)
    linarith
  have hc2 : c ≤ 2 := by
    dsimp [c]
    have hinv : 1 / Real.log (2 * P) ≤ 1 := by
      rw [div_le_iff₀ (by linarith : 0 < Real.log (2 * P))]
      linarith
    linarith
  let D : ℝ := 250000 * (C + 1) ^ 2 * P ^ c * (A * Real.log (2 * P))
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hmajorant : Integrable (fun τ : ℝ ↦ D * (1 + τ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul D
  let f : ℝ → ℂ := fun τ ↦
    primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I) *
      (-deriv riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) /
        riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I))
  have hfbound (τ : ℝ) : ‖f τ‖ ≤ D * (1 + τ ^ 2)⁻¹ := by
    have hdecay := primeMellinTransform_vertical_decay S C P c τ hSs hS01
      hS0 hS1 hC0 hC1 hC2 hP (by linarith) hc2
    have hzeta :
        ‖-deriv riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) /
            riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I)‖ ≤
          A * Real.log (2 * P) := by
      rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
          mul_one, add_zero]
        exact hc1)]
      simpa only [c] using hALS P (τ + u) hP
    simp only [f, norm_mul]
    calc
      _ ≤ (250000 * (C + 1) ^ 2 * P ^ c / (1 + τ ^ 2)) *
          (A * Real.log (2 * P)) :=
        mul_le_mul hdecay hzeta (norm_nonneg _) (by positivity)
      _ = D * (1 + τ ^ 2)⁻¹ := by
        dsimp [D]
        rw [div_eq_mul_inv]
        ring
  let U : Set ℝ := Set.Iic (-Z - u) ∪ Set.Ioi (Z - u)
  let V : Set ℝ := Set.Iic (-H) ∪ Set.Ioi H
  have hUV : U ⊆ V := by
    intro τ hτ
    rcases hτ with hτ | hτ
    · left
      change τ ≤ -Z - u at hτ
      change τ ≤ -(Z - |u|)
      linarith [neg_le_abs u]
    · right
      change Z - u < τ at hτ
      change Z - |u| < τ
      linarith [le_abs_self u]
  have hint : ‖∫ τ : ℝ in U, f τ‖ ≤
      ∫ τ : ℝ in U, D * (1 + τ ^ 2)⁻¹ :=
    norm_integral_le_of_norm_le hmajorant.integrableOn (ae_of_all _ hfbound)
  have hmono : (∫ τ : ℝ in U, D * (1 + τ ^ 2)⁻¹) ≤
      ∫ τ : ℝ in V, D * (1 + τ ^ 2)⁻¹ := by
    apply MeasureTheory.setIntegral_mono_set hmajorant.integrableOn
    · filter_upwards with τ
      positivity
    · exact Filter.Eventually.of_forall hUV
  have htail := integral_inv_one_add_sq_tail_le H hH
  have htailD : (∫ τ : ℝ in V, D * (1 + τ ^ 2)⁻¹) ≤
      D * (2 / H) := by
    dsimp only [V]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left htail hD0
  have hcoef : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [div_le_one (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith [Real.two_le_pi]
  change ‖(1 / (2 * Real.pi) : ℂ) * ∫ τ : ℝ in U, f τ‖ ≤ _
  calc
    _ = ‖(1 / (2 * Real.pi) : ℂ)‖ * ‖∫ τ : ℝ in U, f τ‖ := norm_mul _ _
    _ ≤ ‖∫ τ : ℝ in U, f τ‖ := by
      nlinarith [norm_nonneg (∫ τ : ℝ in U, f τ)]
    _ ≤ ∫ τ : ℝ in U, D * (1 + τ ^ 2)⁻¹ := hint
    _ ≤ ∫ τ : ℝ in V, D * (1 + τ ^ 2)⁻¹ := hmono
    _ ≤ D * (2 / H) := htailD
    _ = (500000 * A) * (C + 1) ^ 2 * P ^ c *
        Real.log (2 * P) / (Z - |u|) := by
      dsimp [D, H]
      ring

/-- The regular part of the truncated right line is bounded by the shifted
side and the two horizontal sides of the zero-free rectangle. -/
theorem primeMellin_regular_truncated_bound
    (S : ℝ → ℝ) (C P η c Z u M : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hc1 : 1 < c) (hc2 : c ≤ 2) (hZ : 1 ≤ Z) (hM : 0 ≤ M)
    (hu : |u| ≤ Z / 2)
    (hzero : ∀ z : ℂ, 1 - η ≤ z.re → z.re ≤ 2 → |z.im| ≤ Z →
      z ≠ 1 → riemannZeta z ≠ 0)
    (hreg : ∀ z : ℂ, 1 - η ≤ z.re → z.re ≤ 2 → |z.im| ≤ Z →
      z ≠ 1 →
        ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤ M) :
    ‖(1 / (2 * Real.pi) : ℂ) *
        ∫ y : ℝ in -Z..Z,
          primeMellinTransform S P
              ((1 - (u : ℂ) * I) +
                (((c - 1 : ℝ) : ℂ) + (y : ℂ) * I)) *
            (-deriv riemannZeta
                  (1 + ((c - 1 : ℝ) : ℂ) + (y : ℂ) * I) /
                riemannZeta
                  (1 + ((c - 1 : ℝ) : ℂ) + (y : ℂ) * I) -
              1 / (((c - 1 : ℝ) : ℂ) + (y : ℂ) * I))‖ ≤
      5000000 * (C + 1) ^ 2 * M *
        (P ^ (1 - η / 2) + P ^ c / Z ^ 2) := by
  let W : ℂ → ℂ := primeMellinTransform S P
  let s₀ : ℂ := 1 - (u : ℂ) * I
  let A : ℝ := c - 1
  let B : ℝ := η / 2
  let Hb : ℂ := ∫ x : ℝ in -B..A,
    W (s₀ + ((x : ℂ) - (Z : ℂ) * I)) *
      (-deriv riemannZeta (1 + (x : ℂ) - (Z : ℂ) * I) /
          riemannZeta (1 + (x : ℂ) - (Z : ℂ) * I) -
        1 / ((x : ℂ) - (Z : ℂ) * I))
  let Ht : ℂ := ∫ x : ℝ in -B..A,
    W (s₀ + ((x : ℂ) + (Z : ℂ) * I)) *
      (-deriv riemannZeta (1 + (x : ℂ) + (Z : ℂ) * I) /
          riemannZeta (1 + (x : ℂ) + (Z : ℂ) * I) -
        1 / ((x : ℂ) + (Z : ℂ) * I))
  let R : ℂ := ∫ y : ℝ in -Z..Z,
    W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
      (-deriv riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) /
          riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) -
        1 / ((A : ℂ) + (y : ℂ) * I))
  let L : ℂ := ∫ y : ℝ in -Z..Z,
    W (s₀ + (-(B : ℂ) + (y : ℂ) * I)) *
      (-deriv riemannZeta (1 - (B : ℂ) + (y : ℂ) * I) /
          riemannZeta (1 - (B : ℂ) + (y : ℂ) * I) -
        1 / (-(B : ℂ) + (y : ℂ) * I))
  have hW : Differentiable ℂ W :=
    primeMellinTransform_differentiable S P hSs hS0 (by linarith)
  have hrect := primeMellin_regular_rectangle W hW η c Z u hη hc1 hc2
    (by linarith) hzero
  change Hb - Ht + I * R - I * L = 0 at hrect
  have hrect' := congrArg (fun z : ℂ ↦ (-I) * z) hrect
  simp only [mul_sub, mul_add, neg_mul, ← mul_assoc, Complex.I_mul_I,
    neg_neg, one_mul, mul_zero] at hrect'
  have hrelation : R = L + I * Hb - I * Ht := by
    linear_combination hrect'
  have hleft : ‖L‖ ≤
      1000000 * (C + 1) ^ 2 * M * P ^ (1 - η / 2) := by
    have hl := primeMellin_shifted_side_bound S C P η Z u M
      hSs hS01 hS0 hS1 hC0 hC1 hC2 hP hη hη1 (by linarith) hM hreg
    dsimp only [L, W, s₀, B]
    convert hl using 1 <;> push_cast <;> ring
  have hhoriz : ‖Hb‖ + ‖Ht‖ ≤
      4000000 * (C + 1) ^ 2 * M * P ^ c / Z ^ 2 := by
    have hh := primeMellin_horizontal_sides_bound S C P η c Z u M
      hSs hS01 hS0 hS1 hC0 hC1 hC2 hP hη hη1 hc1 hc2 (by linarith) hM hu hreg
    dsimp only [Hb, Ht, W, s₀, A, B]
    convert hh using 1 <;> push_cast <;> ring
  have hcoef : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [div_le_one (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith [Real.two_le_pi]
  change ‖(1 / (2 * Real.pi) : ℂ) * R‖ ≤ _
  calc
    _ = ‖(1 / (2 * Real.pi) : ℂ)‖ * ‖R‖ := norm_mul _ _
    _ ≤ ‖R‖ := mul_le_of_le_one_left (norm_nonneg _) hcoef
    _ = ‖L + I * Hb - I * Ht‖ := by rw [hrelation]
    _ ≤ ‖L‖ + (‖Hb‖ + ‖Ht‖) := by
      calc
        _ ≤ ‖L + I * Hb‖ + ‖I * Ht‖ := norm_sub_le _ _
        _ ≤ (‖L‖ + ‖I * Hb‖) + ‖I * Ht‖ :=
          add_le_add (norm_add_le _ _) (le_refl _)
        _ = _ := by simp [add_assoc]
    _ ≤ 1000000 * (C + 1) ^ 2 * M * P ^ (1 - η / 2) +
        4000000 * (C + 1) ^ 2 * M * P ^ c / Z ^ 2 :=
      add_le_add hleft hhoriz
    _ ≤ 5000000 * (C + 1) ^ 2 * M * P ^ (1 - η / 2) +
        5000000 * (C + 1) ^ 2 * M * (P ^ c / Z ^ 2) := by
      have ha : 0 ≤ (C + 1) ^ 2 * M * P ^ (1 - η / 2) := by positivity
      have hb : 0 ≤ (C + 1) ^ 2 * M * P ^ c / Z ^ 2 := by positivity
      calc
        _ = 1000000 * ((C + 1) ^ 2 * M * P ^ (1 - η / 2)) +
            4000000 * ((C + 1) ^ 2 * M * P ^ c / Z ^ 2) := by ring
        _ ≤ 5000000 * ((C + 1) ^ 2 * M * P ^ (1 - η / 2)) +
            5000000 * ((C + 1) ^ 2 * M * P ^ c / Z ^ 2) :=
          add_le_add
            (mul_le_mul_of_nonneg_right (by norm_num) ha)
            (mul_le_mul_of_nonneg_right (by norm_num) hb)
        _ = _ := by ring
    _ = 5000000 * (C + 1) ^ 2 * M *
        (P ^ (1 - η / 2) + P ^ c / Z ^ 2) := by ring

/-- On the right edge, the full logarithmic derivative splits exactly into
the analytic regular part and the rational pole part. -/
theorem primeMellin_right_line_decomposition
    (W : ℂ → ℂ) (hW : Differentiable ℂ W)
    (c Z u : ℝ) (hc1 : 1 < c) :
    let s₀ : ℂ := 1 - (u : ℂ) * I
    let A : ℝ := c - 1
    (∫ y : ℝ in -Z..Z,
        W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
          (-deriv riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) /
            riemannZeta (1 + (A : ℂ) + (y : ℂ) * I))) =
      (∫ y : ℝ in -Z..Z,
        W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
          (-deriv riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) /
              riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) -
            1 / ((A : ℂ) + (y : ℂ) * I))) +
      ∫ y : ℝ in -Z..Z,
        W (s₀ + ((A : ℂ) + (y : ℂ) * I)) /
          ((A : ℂ) + (y : ℂ) * I) := by
  dsimp only
  let s₀ : ℂ := 1 - (u : ℂ) * I
  let A : ℝ := c - 1
  have hA : 0 < A := by dsimp [A]; linarith
  obtain ⟨G, hG, hGval⟩ := exists_zeta_pole_reg
  let q : ℂ → ℂ := fun z ↦
    W (s₀ + z) * zetaLogDerivRegular G (1 + z)
  have hremoved (y : ℝ) :
      zetaPoleRemoved G (1 + ((A : ℂ) + (y : ℂ) * I)) ≠ 0 := by
    have hz0 : (A : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro hz
      have := congrArg Complex.re hz
      simp [hA.ne'] at this
    have hone : (1 : ℂ) + ((A : ℂ) + (y : ℂ) * I) ≠ 1 := by
      intro hz
      apply hz0
      linear_combination hz
    rw [zetaPoleRemoved_eq G hGval _ hone]
    rw [show (1 : ℂ) + ((A : ℂ) + (y : ℂ) * I) - 1 =
      (A : ℂ) + (y : ℂ) * I by ring]
    apply mul_ne_zero hz0
    apply riemannZeta_ne_zero_of_one_le_re
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    dsimp [A]
    linarith
  have hqAt (y : ℝ) :
      DifferentiableAt ℂ q ((A : ℂ) + (y : ℂ) * I) := by
    exact ((hW _).comp _ (by fun_prop)).mul
      ((zetaLogDerivRegular_differentiableAt G hG _ (hremoved y)).comp _
        (by fun_prop))
  have hqInt : IntervalIntegrable
      (fun y : ℝ ↦ q ((A : ℂ) + (y : ℂ) * I)) volume (-Z) Z := by
    apply Continuous.intervalIntegrable
    apply continuous_iff_continuousAt.2
    intro y
    have hp : ContinuousAt (fun y : ℝ ↦ (A : ℂ) + (y : ℂ) * I) y := by
      fun_prop
    have hc := ContinuousAt.comp
      (f := fun y : ℝ ↦ (A : ℂ) + (y : ℂ) * I) (g := q)
      (hqAt y).continuousAt hp
    simpa only [Function.comp_apply] using hc
  have hpoleInt : IntervalIntegrable
      (fun y : ℝ ↦ W (s₀ + ((A : ℂ) + (y : ℂ) * I)) /
        ((A : ℂ) + (y : ℂ) * I)) volume (-Z) Z := by
    apply Continuous.intervalIntegrable
    apply Continuous.div (hW.continuous.comp (by fun_prop)) (by fun_prop)
    intro y
    intro hy
    have := congrArg Complex.re hy
    simp [hA.ne'] at this
  have hqEq (y : ℝ) :
      q ((A : ℂ) + (y : ℂ) * I) =
        W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
          (-deriv riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) /
              riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) -
            1 / ((A : ℂ) + (y : ℂ) * I)) := by
    have hz0 : (A : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro hz
      have := congrArg Complex.re hz
      simp [hA.ne'] at this
    have hone : (1 : ℂ) + ((A : ℂ) + (y : ℂ) * I) ≠ 1 := by
      intro hz
      apply hz0
      linear_combination hz
    have hζ : riemannZeta (1 + ((A : ℂ) + (y : ℂ) * I)) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
      dsimp [A]
      linarith
    dsimp only [q]
    have hr := zetaLogDerivRegular_eq G hG hGval
      (1 + ((A : ℂ) + (y : ℂ) * I)) hone hζ
    rw [show (1 : ℂ) + ((A : ℂ) + (y : ℂ) * I) - 1 =
      (A : ℂ) + (y : ℂ) * I by ring] at hr
    rw [hr]
    congr 2 <;> ring
  have hregInt : IntervalIntegrable
      (fun y : ℝ ↦
        W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
          (-deriv riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) /
              riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) -
            1 / ((A : ℂ) + (y : ℂ) * I))) volume (-Z) Z := by
    exact IntervalIntegrable.congr (fun y hy ↦ hqEq y) hqInt
  rw [← intervalIntegral.integral_add hregInt hpoleInt]
  apply intervalIntegral.integral_congr
  intro y hy
  dsimp only [s₀, A]
  ring

/-- The normalized truncated right-line integral differs from the pole
residue by the regular zero-free contribution plus square-root and
horizontal errors. -/
theorem primeMellin_truncated_shift_bound
    (S : ℝ → ℝ) (C P η c Z u M : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hc1 : 1 < c) (hc2 : c ≤ 2) (hZ : 1 ≤ Z) (hM : 0 ≤ M)
    (hu : |u| ≤ Z / 2)
    (hzero : ∀ z : ℂ, 1 - η ≤ z.re → z.re ≤ 2 → |z.im| ≤ Z →
      z ≠ 1 → riemannZeta z ≠ 0)
    (hreg : ∀ z : ℂ, 1 - η ≤ z.re → z.re ≤ 2 → |z.im| ≤ Z →
      z ≠ 1 →
        ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤ M) :
    ‖(1 / (2 * Real.pi) : ℂ) *
          (∫ y : ℝ in -Z..Z,
            primeMellinTransform S P
                ((1 - (u : ℂ) * I) +
                  (((c - 1 : ℝ) : ℂ) + (y : ℂ) * I)) *
              (-deriv riemannZeta
                    (1 + ((c - 1 : ℝ) : ℂ) + (y : ℂ) * I) /
                riemannZeta
                  (1 + ((c - 1 : ℝ) : ℂ) + (y : ℂ) * I))) -
        primeMellinTransform S P (1 - (u : ℂ) * I)‖ ≤
      12000000 * (C + 1) ^ 2 * (M + 1) *
        (P ^ (1 - η / 2) + P ^ c / Z ^ 2) := by
  let W : ℂ → ℂ := primeMellinTransform S P
  let s₀ : ℂ := 1 - (u : ℂ) * I
  let A : ℝ := c - 1
  let R : ℂ := ∫ y : ℝ in -Z..Z,
    W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
      (-deriv riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) /
        riemannZeta (1 + (A : ℂ) + (y : ℂ) * I))
  let Rreg : ℂ := ∫ y : ℝ in -Z..Z,
    W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
      (-deriv riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) /
          riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) -
        1 / ((A : ℂ) + (y : ℂ) * I))
  let Rrat : ℂ := ∫ y : ℝ in -Z..Z,
    W (s₀ + ((A : ℂ) + (y : ℂ) * I)) /
      ((A : ℂ) + (y : ℂ) * I)
  have hW : Differentiable ℂ W :=
    primeMellinTransform_differentiable S P hSs hS0 (by linarith)
  have hdecomp : R = Rreg + Rrat := by
    simpa only [R, Rreg, Rrat, W, s₀, A] using
      primeMellin_right_line_decomposition W hW c Z u hc1
  have hregular :
      ‖(1 / (2 * Real.pi) : ℂ) * Rreg‖ ≤
        5000000 * (C + 1) ^ 2 * M *
          (P ^ (1 - η / 2) + P ^ c / Z ^ 2) := by
    simpa only [Rreg, W, s₀, A] using
      primeMellin_regular_truncated_bound S C P η c Z u M hSs hS01 hS0 hS1
        hC0 hC1 hC2 hP hη hη1 hc1 hc2 hZ hM hu hzero hreg
  have hrational :
      ‖(1 / (2 * Real.pi) : ℂ) * Rrat - W s₀‖ ≤
        6000000 * (C + 1) ^ 2 *
          (P ^ (1 / 2 : ℝ) + P ^ c / Z ^ 2) := by
    simpa only [Rrat, W, s₀, A] using
      primeMellin_rational_truncated_bound S C P c Z u hSs hS01 hS0 hS1
        hC0 hC1 hC2 hP hc1 hc2 hZ hu
  have hsqrt : P ^ (1 / 2 : ℝ) ≤ P ^ (1 - η / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  change ‖(1 / (2 * Real.pi) : ℂ) * R - W s₀‖ ≤ _
  rw [hdecomp]
  have hrearrange :
      (1 / (2 * Real.pi) : ℂ) * (Rreg + Rrat) - W s₀ =
        (1 / (2 * Real.pi) : ℂ) * Rreg +
          ((1 / (2 * Real.pi) : ℂ) * Rrat - W s₀) := by ring
  rw [hrearrange]
  calc
    _ ≤ ‖(1 / (2 * Real.pi) : ℂ) * Rreg‖ +
        ‖(1 / (2 * Real.pi) : ℂ) * Rrat - W s₀‖ := norm_add_le _ _
    _ ≤ 5000000 * (C + 1) ^ 2 * M *
          (P ^ (1 - η / 2) + P ^ c / Z ^ 2) +
        6000000 * (C + 1) ^ 2 *
          (P ^ (1 / 2 : ℝ) + P ^ c / Z ^ 2) :=
      add_le_add hregular hrational
    _ ≤ 5000000 * (C + 1) ^ 2 * M *
          (P ^ (1 - η / 2) + P ^ c / Z ^ 2) +
        6000000 * (C + 1) ^ 2 *
          (P ^ (1 - η / 2) + P ^ c / Z ^ 2) := by
      gcongr
    _ ≤ 12000000 * (C + 1) ^ 2 * (M + 1) *
          (P ^ (1 - η / 2) + P ^ c / Z ^ 2) := by
      have hbase : 0 ≤ (C + 1) ^ 2 *
          (P ^ (1 - η / 2) + P ^ c / Z ^ 2) := by positivity
      have hM1 : 1 ≤ M + 1 := by linarith
      nlinarith

/-- The full right-line integrand is integrable.  This packages the
measurability fact needed to split it into the asymmetric compact interval
and its two tails. -/
theorem primeMellin_right_line_integrable
    (S : ℝ → ℝ) (C P c u : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) (hc1 : 1 < c) (hc2 : c ≤ 2)
    (hcstandard : c = 1 + 1 / Real.log (2 * P)) :
    Integrable (fun τ : ℝ ↦
      primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I) *
        (-deriv riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) /
          riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I))) := by
  obtain ⟨A₀, hA₀, hALS⟩ := exists_norm_LSeries_vonMangoldt_le_log
  let D : ℝ := 250000 * (C + 1) ^ 2 * P ^ c * (A₀ * Real.log (2 * P))
  let f : ℝ → ℂ := fun τ ↦
    primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I) *
      (-deriv riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) /
        riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I))
  let W : ℂ → ℂ := primeMellinTransform S P
  let s₀ : ℂ := 1 - (u : ℂ) * I
  let A : ℝ := c - 1
  have hA : 0 < A := by dsimp [A]; linarith
  obtain ⟨G, hG, hGval⟩ := exists_zeta_pole_reg
  let q : ℂ → ℂ := fun z ↦
    W (s₀ + z) * zetaLogDerivRegular G (1 + z)
  let p : ℝ → ℂ := fun y ↦
    W (s₀ + ((A : ℂ) + (y : ℂ) * I)) /
      ((A : ℂ) + (y : ℂ) * I)
  have hremoved (y : ℝ) :
      zetaPoleRemoved G (1 + ((A : ℂ) + (y : ℂ) * I)) ≠ 0 := by
    have hz0 : (A : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro hz
      have := congrArg Complex.re hz
      simp [hA.ne'] at this
    have hone : (1 : ℂ) + ((A : ℂ) + (y : ℂ) * I) ≠ 1 := by
      intro hz
      apply hz0
      linear_combination hz
    rw [zetaPoleRemoved_eq G hGval _ hone]
    rw [show (1 : ℂ) + ((A : ℂ) + (y : ℂ) * I) - 1 =
      (A : ℂ) + (y : ℂ) * I by ring]
    exact mul_ne_zero hz0 (riemannZeta_ne_zero_of_one_le_re (by
      simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
      dsimp [A]
      linarith))
  have hqCont : Continuous (fun y : ℝ ↦
      q ((A : ℂ) + (y : ℂ) * I)) := by
    apply continuous_iff_continuousAt.2
    intro y
    have hqAt : DifferentiableAt ℂ q ((A : ℂ) + (y : ℂ) * I) :=
      ((primeMellinTransform_differentiable S P hSs hS0 (by linarith) _).comp _
          (by fun_prop)).mul
        ((zetaLogDerivRegular_differentiableAt G hG _ (hremoved y)).comp _
          (by fun_prop))
    have hp : ContinuousAt (fun y : ℝ ↦ (A : ℂ) + (y : ℂ) * I) y := by
      fun_prop
    have hc := ContinuousAt.comp
      (f := fun y : ℝ ↦ (A : ℂ) + (y : ℂ) * I) (g := q)
      hqAt.continuousAt hp
    simpa only [Function.comp_apply] using hc
  have hpCont : Continuous p := by
    apply Continuous.div
    · exact (primeMellinTransform_differentiable S P hSs hS0
          (by linarith)).continuous.comp (by fun_prop)
    · fun_prop
    · intro y hy
      have := congrArg Complex.re hy
      simp [p, hA.ne'] at this
  have hsplit (y : ℝ) :
      f (y - u) = q ((A : ℂ) + (y : ℂ) * I) + p y := by
    have hz0 : (A : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro hz
      have := congrArg Complex.re hz
      simp [hA.ne'] at this
    have hone : (1 : ℂ) + ((A : ℂ) + (y : ℂ) * I) ≠ 1 := by
      intro hz
      apply hz0
      linear_combination hz
    have hζ : riemannZeta (1 + ((A : ℂ) + (y : ℂ) * I)) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by
        simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
        dsimp [A]
        linarith)
    have hr := zetaLogDerivRegular_eq G hG hGval
      (1 + ((A : ℂ) + (y : ℂ) * I)) hone hζ
    rw [show (1 : ℂ) + ((A : ℂ) + (y : ℂ) * I) - 1 =
      (A : ℂ) + (y : ℂ) * I by ring] at hr
    have hcA : (c : ℂ) = 1 + (A : ℂ) := by
      dsimp [A]
      push_cast
      ring
    dsimp only [f, q, p, W, s₀]
    rw [hcA]
    rw [hr]
    push_cast
    ring
  have hfMeas : AEStronglyMeasurable f := by
    have hcomp : Continuous (fun τ : ℝ ↦
        q ((A : ℂ) + ((τ + u : ℝ) : ℂ) * I) + p (τ + u)) :=
      hqCont.comp (by fun_prop) |>.add (hpCont.comp (by fun_prop))
    refine hcomp.aestronglyMeasurable.congr (ae_of_all _ fun τ ↦ ?_)
    simpa only [add_sub_cancel_right] using (hsplit (τ + u)).symm
  have hmajorant : Integrable (fun τ : ℝ ↦ D * (1 + τ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul D
  have hfbound (τ : ℝ) : ‖f τ‖ ≤ D * (1 + τ ^ 2)⁻¹ := by
    have hdecay := primeMellinTransform_vertical_decay S C P c τ hSs hS01
      hS0 hS1 hC0 hC1 hC2 hP (by linarith) hc2
    have hzeta :
        ‖-deriv riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) /
            riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I)‖ ≤
          A₀ * Real.log (2 * P) := by
      rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
          mul_one, add_zero]
        exact hc1)]
      rw [hcstandard]
      exact hALS P (τ + u) hP
    simp only [f, norm_mul]
    calc
      _ ≤ (250000 * (C + 1) ^ 2 * P ^ c / (1 + τ ^ 2)) *
          (A₀ * Real.log (2 * P)) :=
        mul_le_mul hdecay hzeta (norm_nonneg _) (by positivity)
      _ = D * (1 + τ ^ 2)⁻¹ := by
        dsimp [D]
        rw [div_eq_mul_inv]
        ring
  change Integrable f
  exact hmajorant.mono' hfMeas (ae_of_all _ hfbound)

/-- The completed Mellin shift for the plateau-weighted von Mangoldt sum.
The asymmetric truncation contributes `1 / (Z-|u|)`, while the regular part
has no loss in `η`. -/
theorem exists_primeMellin_vonMangoldt_shift_bound :
    ∃ K : ℝ, 1 ≤ K ∧ ∀
      (S : ℝ → ℝ) (C P η Z u M : ℝ),
      ContDiff ℝ ∞ S →
      (∀ v, 0 ≤ S v ∧ S v ≤ 1) →
      (∀ v, v ≤ 0 → S v = 0) →
      (∀ v, 1 ≤ v → S v = 1) →
      0 ≤ C → (∀ v, |deriv S v| ≤ C) →
      (∀ v, |deriv (deriv S) v| ≤ C) →
      2 ≤ P → 0 < η → η ≤ 1 / 2 → 1 ≤ Z → 0 ≤ M →
      |u| ≤ Z / 2 →
      (∀ z : ℂ, 1 - η ≤ z.re → z.re ≤ 2 → |z.im| ≤ Z →
        z ≠ 1 → riemannZeta z ≠ 0) →
      (∀ z : ℂ, 1 - η ≤ z.re → z.re ≤ 2 → |z.im| ≤ Z →
        z ≠ 1 →
          ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤ M) →
      let c := 1 + 1 / Real.log (2 * P)
      ‖(∑' n : ℕ,
          (((ArithmeticFunction.vonMangoldt n * primeMellinWindow S P n : ℝ) : ℂ) *
            (n : ℂ) ^ (-((u : ℂ) * I)))) -
          primeMellinTransform S P (1 - (u : ℂ) * I)‖ ≤
        K * (C + 1) ^ 2 * (M + 1) *
          (P ^ (1 - η / 2) +
            P ^ c * Real.log (2 * P) / (Z - |u|) + P ^ c / Z ^ 2) := by
  obtain ⟨B, hB1, htail⟩ := exists_primeMellin_asymmetric_right_tail_bound
  let K : ℝ := 12000000 + B
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  intro S C P η Z u M hSs hS01 hS0 hS1 hC0 hC1 hC2 hP hη hη1 hZ hM hu
    hzero hreg
  let c : ℝ := 1 + 1 / Real.log (2 * P)
  have hlog1 : 1 < Real.log (2 * P) := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      _ ≤ Real.log (2 * P) := Real.strictMonoOn_log.monotoneOn
        (show 3 ∈ Set.Ioi (0 : ℝ) by norm_num)
        (show 2 * P ∈ Set.Ioi (0 : ℝ) by
          change 0 < 2 * P
          nlinarith)
        (by linarith)
  have hc1 : 1 < c := by
    dsimp [c]
    have : 0 < 1 / Real.log (2 * P) := one_div_pos.mpr (by linarith)
    linarith
  have hc2 : c ≤ 2 := by
    dsimp [c]
    have hinv : 1 / Real.log (2 * P) ≤ 1 := by
      rw [div_le_iff₀ (by linarith : 0 < Real.log (2 * P))]
      linarith
    linarith
  let f : ℝ → ℂ := fun τ ↦
    primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I) *
      (-deriv riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) /
        riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I))
  let a : ℝ := -Z - u
  let b : ℝ := Z - u
  let Mid : ℂ := ∫ τ : ℝ in a..b, f τ
  let Tail : ℂ := ∫ τ : ℝ in Set.Iic a ∪ Set.Ioi b, f τ
  let Full : ℂ := ∫ τ : ℝ, f τ
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hfInt : Integrable f := by
    exact primeMellin_right_line_integrable S C P c u hSs hS01 hS0 hS1
      hC0 hC1 hC2 hP hc1 hc2 rfl
  have hpartition : Mid + Tail = Full := by
    have hsplit := MeasureTheory.integral_add_compl (f := f)
      (s := Set.Ioc a b) measurableSet_Ioc hfInt
    rw [← intervalIntegral.integral_of_le hab] at hsplit
    have hcompl : (Set.Ioc a b)ᶜ = Set.Iic a ∪ Set.Ioi b := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_Ioc, Set.mem_union,
        Set.mem_Iic, Set.mem_Ioi]
      constructor
      · intro hx
        by_cases hxa : x ≤ a
        · exact Or.inl hxa
        · right
          have hax : a < x := lt_of_not_ge hxa
          by_contra hxb
          exact hx ⟨hax, le_of_not_gt hxb⟩
      · intro hx hmem
        rcases hx with hxa | hxb
        · exact (not_lt_of_ge hxa) hmem.1
        · exact (not_lt_of_ge hmem.2) hxb
    rw [hcompl] at hsplit
    exact hsplit
  have hmid :
      ‖(1 / (2 * Real.pi) : ℂ) * Mid -
          primeMellinTransform S P (1 - (u : ℂ) * I)‖ ≤
        12000000 * (C + 1) ^ 2 * (M + 1) *
          (P ^ (1 - η / 2) + P ^ c / Z ^ 2) := by
    have hs := primeMellin_truncated_shift_bound S C P η c Z u M
      hSs hS01 hS0 hS1 hC0 hC1 hC2 hP hη hη1 hc1 hc2 hZ hM hu hzero hreg
    have htranslate := intervalIntegral.integral_comp_sub_right f u
      (a := -Z) (b := Z)
    have hmidEq : Mid = ∫ y : ℝ in -Z..Z, f (y - u) := by
      dsimp only [Mid, a, b]
      exact htranslate.symm
    rw [hmidEq]
    let g : ℝ → ℂ := fun y ↦
      primeMellinTransform S P
          ((1 - (u : ℂ) * I) + (((c - 1 : ℝ) : ℂ) + (y : ℂ) * I)) *
        (-deriv riemannZeta
              (1 + ((c - 1 : ℝ) : ℂ) + (y : ℂ) * I) /
          riemannZeta (1 + ((c - 1 : ℝ) : ℂ) + (y : ℂ) * I))
    have hfg (y : ℝ) : f (y - u) = g y := by
      dsimp only [f, g]
      push_cast
      congr 2 <;> ring
    have hint : (∫ y : ℝ in -Z..Z, f (y - u)) = ∫ y : ℝ in -Z..Z, g y := by
      apply intervalIntegral.integral_congr
      intro y hy
      exact hfg y
    rw [hint]
    change ‖(1 / (2 * Real.pi) : ℂ) * (∫ y : ℝ in -Z..Z, g y) -
        primeMellinTransform S P (1 - (u : ℂ) * I)‖ ≤ _ at hs
    exact hs
  have htailBound :
      ‖(1 / (2 * Real.pi) : ℂ) * Tail‖ ≤
        B * (C + 1) ^ 2 * P ^ c * Real.log (2 * P) / (Z - |u|) := by
    dsimp only [Tail, a, b, f]
    simpa only [c] using htail S C P u Z hSs hS01 hS0 hS1 hC0 hC1 hC2 hP
      (by nlinarith [abs_nonneg u])
  have hrep := primeMellin_vonMangoldt_zeta_representation S C P u hSs hS01
    hS0 hS1 hC0 hC1 hC2 hP
  change _ = (1 / (2 * Real.pi) : ℂ) * Full at hrep
  rw [hrep]
  rw [← hpartition]
  have hrearrange :
      (1 / (2 * Real.pi) : ℂ) * (Mid + Tail) -
          primeMellinTransform S P (1 - (u : ℂ) * I) =
        ((1 / (2 * Real.pi) : ℂ) * Mid -
          primeMellinTransform S P (1 - (u : ℂ) * I)) +
        (1 / (2 * Real.pi) : ℂ) * Tail := by ring
  rw [hrearrange]
  calc
    _ ≤ ‖(1 / (2 * Real.pi) : ℂ) * Mid -
          primeMellinTransform S P (1 - (u : ℂ) * I)‖ +
        ‖(1 / (2 * Real.pi) : ℂ) * Tail‖ := norm_add_le _ _
    _ ≤ 12000000 * (C + 1) ^ 2 * (M + 1) *
          (P ^ (1 - η / 2) + P ^ c / Z ^ 2) +
        B * (C + 1) ^ 2 * P ^ c * Real.log (2 * P) / (Z - |u|) :=
      add_le_add hmid htailBound
    _ ≤ K * (C + 1) ^ 2 * (M + 1) *
          (P ^ (1 - η / 2) +
            P ^ c * Real.log (2 * P) / (Z - |u|) + P ^ c / Z ^ 2) := by
      dsimp [K]
      have hq : 0 ≤ (C + 1) ^ 2 := sq_nonneg _
      have hM1 : 1 ≤ M + 1 := by linarith
      let X : ℝ := P ^ (1 - η / 2) + P ^ c / Z ^ 2
      let Q : ℝ := P ^ c * Real.log (2 * P) / (Z - |u|)
      have hX : 0 ≤ X := by dsimp [X]; positivity
      have hden : 0 < Z - |u| := by
        have : |u| ≤ Z / 2 := hu
        linarith
      have hQ : 0 ≤ Q := by dsimp [Q]; positivity
      have hB0 : 0 ≤ B := by linarith
      have hrest : 0 ≤ (C + 1) ^ 2 * (M + 1) * X := by positivity
      have hfirst :
          12000000 * (C + 1) ^ 2 * (M + 1) * X ≤
            (12000000 + B) * (C + 1) ^ 2 * (M + 1) * X := by
        apply mul_le_mul_of_nonneg_right _ hX
        gcongr
        linarith
      have hBq : 0 ≤ B * (C + 1) ^ 2 := mul_nonneg hB0 hq
      have htailM : B * (C + 1) ^ 2 * Q ≤
          B * (C + 1) ^ 2 * (M + 1) * Q := by
        calc
          _ = (B * (C + 1) ^ 2) * Q := by ring
          _ ≤ ((B * (C + 1) ^ 2) * (M + 1)) * Q :=
            mul_le_mul_of_nonneg_right
              (le_mul_of_one_le_right hBq hM1) hQ
          _ = _ := by ring
      have htailCoeff : B * (C + 1) ^ 2 * (M + 1) * Q ≤
          (12000000 + B) * (C + 1) ^ 2 * (M + 1) * Q := by
        have hrestQ : 0 ≤ (C + 1) ^ 2 * (M + 1) * Q := by positivity
        apply mul_le_mul_of_nonneg_right _ hQ
        gcongr
        linarith
      calc
        12000000 * (C + 1) ^ 2 * (M + 1) *
              (P ^ (1 - η / 2) + P ^ c / Z ^ 2) +
            B * (C + 1) ^ 2 * P ^ c * Real.log (2 * P) / (Z - |u|) =
          12000000 * (C + 1) ^ 2 * (M + 1) * X +
            B * (C + 1) ^ 2 * Q := by dsimp [X, Q]; ring
        _ ≤ (12000000 + B) * (C + 1) ^ 2 * (M + 1) * X +
            (12000000 + B) * (C + 1) ^ 2 * (M + 1) * Q := by
          exact add_le_add hfirst (htailM.trans htailCoeff)
        _ = (12000000 + B) * (C + 1) ^ 2 * (M + 1) *
            (P ^ (1 - η / 2) +
              P ^ c * Real.log (2 * P) / (Z - |u|) + P ^ c / Z ^ 2) := by
          dsimp [X, Q]
          ring

/-- Compact support turns the von Mangoldt `tsum` into the finite campaign
sum used by the prime-power estimate. -/
theorem primeMellin_vonMangoldt_tsum_eq_sum
    (S : ℝ → ℝ) (P u : ℝ)
    (hS0 : ∀ v, v ≤ 0 → S v = 0) (hP : 2 ≤ P) :
    (∑' n : ℕ,
        (((ArithmeticFunction.vonMangoldt n * primeMellinWindow S P n : ℝ) : ℂ) *
          (n : ℂ) ^ (-((u : ℂ) * I)))) =
      ∑ n ∈ Finset.Ioc 0 ⌊4 * P⌋₊,
        (((ArithmeticFunction.vonMangoldt n * primeMellinWindow S P n : ℝ) : ℂ) *
          (n : ℂ) ^ (-((u : ℂ) * I))) := by
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnlarge : ⌊4 * P⌋₊ < n := by
      by_contra hle
      exact hn (Finset.mem_Ioc.mpr ⟨hnpos, le_of_not_gt hle⟩)
    have h4P0 : 0 ≤ 4 * P := by positivity
    have hfloor : 4 * P < (⌊4 * P⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hsucc : ⌊4 * P⌋₊ + 1 ≤ n := Nat.succ_le_iff.mpr hnlarge
    have hnR : ((⌊4 * P⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hsucc
    have h4Pn : 4 * P ≤ (n : ℝ) := le_trans hfloor.le hnR
    rw [primeMellinWindow_eq_zero_of_two_mul_le S P n hS0 (by linarith) h4Pn]
    simp

/-- **V-A capstone.**  The plateau-weighted prime sum equals the Mellin pole
term up to the zero-free shift error and the prime-power remainder. -/
theorem exists_primeMellin_prime_shift_bound :
    ∃ K : ℝ, 1 ≤ K ∧ ∀
      (S : ℝ → ℝ) (C P η Z u M : ℝ),
      ContDiff ℝ ∞ S →
      (∀ v, 0 ≤ S v ∧ S v ≤ 1) →
      (∀ v, v ≤ 0 → S v = 0) →
      (∀ v, 1 ≤ v → S v = 1) →
      0 ≤ C → (∀ v, |deriv S v| ≤ C) →
      (∀ v, |deriv (deriv S) v| ≤ C) →
      2 ≤ P → 0 < η → η ≤ 1 / 2 → 1 ≤ Z → 0 ≤ M →
      |u| ≤ Z / 2 →
      (∀ z : ℂ, 1 - η ≤ z.re → z.re ≤ 2 → |z.im| ≤ Z →
        z ≠ 1 → riemannZeta z ≠ 0) →
      (∀ z : ℂ, 1 - η ≤ z.re → z.re ≤ 2 → |z.im| ≤ Z →
        z ≠ 1 →
          ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤ M) →
      let c := 1 + 1 / Real.log (2 * P)
      ‖(∑ p ∈ (Finset.Ioc 0 ⌊4 * P⌋₊).filter Nat.Prime,
          ((primeMellinWindow S P p * Real.log p : ℝ) : ℂ) *
            (p : ℂ) ^ (-((u : ℂ) * I))) -
          primeMellinTransform S P (1 - (u : ℂ) * I)‖ ≤
        K * (C + 1) ^ 2 * (M + 1) *
          (P ^ (1 - η / 2) +
            P ^ c * Real.log (2 * P) / (Z - |u|) +
            P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)) := by
  obtain ⟨K₀, hK₀, hshift⟩ := exists_primeMellin_vonMangoldt_shift_bound
  let K : ℝ := K₀ + 6
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  intro S C P η Z u M hSs hS01 hS0 hS1 hC0 hC1 hC2 hP hη hη1 hZ hM hu
    hzero hreg
  let c : ℝ := 1 + 1 / Real.log (2 * P)
  let I₀ : Finset ℕ := Finset.Ioc 0 ⌊4 * P⌋₊
  let F : ℕ → ℂ := fun n ↦
    (((ArithmeticFunction.vonMangoldt n * primeMellinWindow S P n : ℝ) : ℂ) *
      (n : ℂ) ^ (-((u : ℂ) * I)))
  let PrimePart : ℂ := ∑ p ∈ I₀.filter Nat.Prime,
    ((primeMellinWindow S P p * Real.log p : ℝ) : ℂ) *
      (p : ℂ) ^ (-((u : ℂ) * I))
  let Nonprime : ℂ := ∑ n ∈ I₀.filter (fun n ↦ ¬n.Prime), F n
  let Finite : ℂ := ∑ n ∈ I₀, F n
  have hprimeEq : (∑ p ∈ I₀.filter Nat.Prime, F p) = PrimePart := by
    dsimp only [PrimePart]
    apply Finset.sum_congr rfl
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    dsimp only [F]
    rw [ArithmeticFunction.vonMangoldt_apply_prime hpp]
    push_cast
    ring
  have hfiniteSplit : PrimePart + Nonprime = Finite := by
    rw [← hprimeEq]
    dsimp only [Nonprime, Finite]
    exact Finset.sum_filter_add_sum_filter_not I₀ Nat.Prime F
  have hfiniteTsum : (∑' n : ℕ, F n) = Finite := by
    dsimp only [F, Finite, I₀]
    exact primeMellin_vonMangoldt_tsum_eq_sum S P u hS0 hP
  have hmain :
      ‖Finite - primeMellinTransform S P (1 - (u : ℂ) * I)‖ ≤
        K₀ * (C + 1) ^ 2 * (M + 1) *
          (P ^ (1 - η / 2) +
            P ^ c * Real.log (2 * P) / (Z - |u|) + P ^ c / Z ^ 2) := by
    have hs := hshift S C P η Z u M hSs hS01 hS0 hS1 hC0 hC1 hC2 hP
      hη hη1 hZ hM hu hzero hreg
    rw [hfiniteTsum] at hs
    simpa only [c] using hs
  have hnonprime : ‖Nonprime‖ ≤ 6 * Real.sqrt P * Real.log (4 * P) := by
    have hp := primeMellin_prime_powers_bound S P u hS01 hP
    dsimp only [Nonprime, I₀, F]
    convert hp using 1
    apply congrArg norm
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring
  have hrearrange :
      PrimePart - primeMellinTransform S P (1 - (u : ℂ) * I) =
        (Finite - primeMellinTransform S P (1 - (u : ℂ) * I)) - Nonprime := by
    linear_combination hfiniteSplit
  change ‖PrimePart - primeMellinTransform S P (1 - (u : ℂ) * I)‖ ≤ _
  rw [hrearrange]
  calc
    _ ≤ ‖Finite - primeMellinTransform S P (1 - (u : ℂ) * I)‖ +
        ‖Nonprime‖ := norm_sub_le _ _
    _ ≤ K₀ * (C + 1) ^ 2 * (M + 1) *
          (P ^ (1 - η / 2) +
            P ^ c * Real.log (2 * P) / (Z - |u|) + P ^ c / Z ^ 2) +
        6 * Real.sqrt P * Real.log (4 * P) := add_le_add hmain hnonprime
    _ ≤ K * (C + 1) ^ 2 * (M + 1) *
          (P ^ (1 - η / 2) +
            P ^ c * Real.log (2 * P) / (Z - |u|) +
            P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)) := by
      dsimp [K]
      let X : ℝ := P ^ (1 - η / 2) +
        P ^ c * Real.log (2 * P) / (Z - |u|) + P ^ c / Z ^ 2
      let Q : ℝ := Real.sqrt P * Real.log (4 * P)
      have hden : 0 < Z - |u| := by linarith [abs_nonneg u]
      have hlog2 : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by linarith)
      have hlog4 : 0 ≤ Real.log (4 * P) := Real.log_nonneg (by linarith)
      have hX : 0 ≤ X := by dsimp [X]; positivity
      have hQ : 0 ≤ Q := by dsimp [Q]; positivity
      have hfac : 1 ≤ (C + 1) ^ 2 * (M + 1) := by
        have hC1 : 1 ≤ C + 1 := by linarith
        nlinarith [sq_nonneg (C + 1)]
      have hK0 : 0 ≤ K₀ := by linarith
      have hfirst : K₀ * (C + 1) ^ 2 * (M + 1) * X ≤
          (K₀ + 6) * (C + 1) ^ 2 * (M + 1) * X := by
        apply mul_le_mul_of_nonneg_right _ hX
        gcongr
        linarith
      have hsecond : 6 * Q ≤
          (K₀ + 6) * (C + 1) ^ 2 * (M + 1) * Q := by
        apply mul_le_mul_of_nonneg_right _ hQ
        have : 6 ≤ (K₀ + 6) * ((C + 1) ^ 2 * (M + 1)) := by
          nlinarith [mul_nonneg (show 0 ≤ K₀ + 6 by linarith)
            (show 0 ≤ (C + 1) ^ 2 * (M + 1) by positivity)]
        nlinarith
      calc
        K₀ * (C + 1) ^ 2 * (M + 1) *
              (P ^ (1 - η / 2) +
                P ^ c * Real.log (2 * P) / (Z - |u|) + P ^ c / Z ^ 2) +
            6 * Real.sqrt P * Real.log (4 * P) =
          K₀ * (C + 1) ^ 2 * (M + 1) * X + 6 * Q := by
            dsimp [X, Q]
            ring
        _ ≤ (K₀ + 6) * (C + 1) ^ 2 * (M + 1) * X +
            (K₀ + 6) * (C + 1) ^ 2 * (M + 1) * Q :=
          add_le_add hfirst hsecond
        _ = _ := by dsimp [X, Q]; ring

/-- The V-A estimate in the positive-phase form consumed by the weighted
large-values lemma.  The Mellin residue supplies the summable `1/u²` term. -/
theorem exists_primeMellin_kernel_bound :
    ∃ K : ℝ, 1 ≤ K ∧ ∀
      (S : ℝ → ℝ) (C P η Z u M : ℝ),
      ContDiff ℝ ∞ S →
      (∀ v, 0 ≤ S v ∧ S v ≤ 1) →
      (∀ v, v ≤ 0 → S v = 0) →
      (∀ v, 1 ≤ v → S v = 1) →
      0 ≤ C → (∀ v, |deriv S v| ≤ C) →
      (∀ v, |deriv (deriv S) v| ≤ C) →
      2 ≤ P → 0 < η → η ≤ 1 / 2 → 1 ≤ Z → 0 ≤ M →
      1 ≤ |u| → |u| ≤ Z / 2 →
      (∀ z : ℂ, 1 - η ≤ z.re → z.re ≤ 2 → |z.im| ≤ Z →
        z ≠ 1 → riemannZeta z ≠ 0) →
      (∀ z : ℂ, 1 - η ≤ z.re → z.re ≤ 2 → |z.im| ≤ Z →
        z ≠ 1 →
          ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤ M) →
      let c := 1 + 1 / Real.log (2 * P)
      ‖∑ p ∈ (Finset.Ioc 0 ⌊4 * P⌋₊).filter Nat.Prime,
          ((primeMellinWindow S P p * Real.log p : ℝ) : ℂ) *
            (p : ℂ) ^ (I * (u : ℂ))‖ ≤
        (250000 * (C + 1) ^ 2 * P) / |u| ^ 2 +
          K * (C + 1) ^ 2 * (M + 1) *
            (P ^ (1 - η / 2) +
              P ^ c * Real.log (2 * P) / (Z - |u|) +
              P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)) := by
  obtain ⟨K, hK, hshift⟩ := exists_primeMellin_prime_shift_bound
  refine ⟨K, hK, ?_⟩
  intro S C P η Z u M hSs hS01 hS0 hS1 hC0 hC1 hC2 hP hη hη1 hZ hM hu1 huZ
    hzero hreg
  let c : ℝ := 1 + 1 / Real.log (2 * P)
  let Q : ℂ := ∑ p ∈ (Finset.Ioc 0 ⌊4 * P⌋₊).filter Nat.Prime,
    ((primeMellinWindow S P p * Real.log p : ℝ) : ℂ) *
      (p : ℂ) ^ ((u : ℂ) * I)
  let W₀ : ℂ := primeMellinTransform S P (1 + (u : ℂ) * I)
  have hs : ‖Q - W₀‖ ≤
      K * (C + 1) ^ 2 * (M + 1) *
        (P ^ (1 - η / 2) +
          P ^ c * Real.log (2 * P) / (Z - |u|) +
          P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)) := by
    have hs₀ := hshift S C P η Z (-u) M hSs hS01 hS0 hS1 hC0 hC1 hC2 hP
      hη hη1 hZ hM (by simpa only [abs_neg] using huZ) hzero hreg
    dsimp only [Q, W₀]
    simpa only [c, Complex.ofReal_neg, neg_mul, neg_neg, abs_neg,
      sub_neg_eq_add] using hs₀
  have hpole₀ := primeMellinTransform_vertical_decay S C P 1 u hSs hS01 hS0 hS1
    hC0 hC1 hC2 hP (by norm_num) (by norm_num)
  have hinv : (1 + u ^ 2)⁻¹ ≤ 1 / |u| ^ 2 := by
    have hu0 : 0 < |u| ^ 2 := sq_pos_of_pos (lt_of_lt_of_le (by norm_num) hu1)
    rw [show u ^ 2 = |u| ^ 2 by exact (sq_abs u).symm]
    simpa only [one_div] using
      (inv_le_inv₀ (by positivity : 0 < 1 + |u| ^ 2) hu0).2 (by linarith)
  have hpole : ‖W₀‖ ≤ (250000 * (C + 1) ^ 2 * P) / |u| ^ 2 := by
    have hpole₁ : ‖W₀‖ ≤
        250000 * (C + 1) ^ 2 * P / (1 + u ^ 2) := by
      dsimp only [W₀]
      convert hpole₀ using 1 <;> norm_num
    calc
      _ ≤ 250000 * (C + 1) ^ 2 * P * (1 + u ^ 2)⁻¹ := by
        simpa only [div_eq_mul_inv] using hpole₁
      _ ≤ 250000 * (C + 1) ^ 2 * P * (1 / |u| ^ 2) := by
        gcongr
      _ = (250000 * (C + 1) ^ 2 * P) / |u| ^ 2 := by ring
  have hQphase :
      (∑ p ∈ (Finset.Ioc 0 ⌊4 * P⌋₊).filter Nat.Prime,
          ((primeMellinWindow S P p * Real.log p : ℝ) : ℂ) *
            (p : ℂ) ^ (I * (u : ℂ))) = Q := by
    dsimp only [Q]
    apply Finset.sum_congr rfl
    intro p hp
    congr 1
    ring
  rw [hQphase]
  calc
    ‖Q‖ = ‖(Q - W₀) + W₀‖ := by ring
    _ ≤ ‖Q - W₀‖ + ‖W₀‖ := norm_add_le _ _
    _ ≤ K * (C + 1) ^ 2 * (M + 1) *
          (P ^ (1 - η / 2) +
            P ^ c * Real.log (2 * P) / (Z - |u|) +
            P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)) +
        (250000 * (C + 1) ^ 2 * P) / |u| ^ 2 := add_le_add hs hpole
    _ = _ := by ring

end MoltResearch
