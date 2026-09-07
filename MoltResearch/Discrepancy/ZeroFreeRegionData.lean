import MoltResearch.Discrepancy.PrimeLargeValuesFromRegion

/-!
# Prime large values from quantitative zero-free data

This leaf packages the final two-region bookkeeping in the Mellin-shift
argument.  The height includes the factor `2 * pi` forced by Mathlib's
normalisation of `Real.fourierChar`: points in `[-T,T]` become Mellin
frequencies in `[-2*pi*T,2*pi*T]`, and their differences have size at most
`4*pi*T`.

The `envelope` field is purely real-variable bookkeeping.  It records the
standard split between the trivial estimate at short prime length and the
zero-free saving at long prime length.  In particular, it contains no
additional statement about zeta.  The exponent pair used by Track R is
`theta = 31/40 < 4/5`; every fixed logarithmic loss `m` is absorbed in this
field.
-/

namespace MoltResearch

open Complex ExpSums Finset
open scoped ContDiff

/-- Width used when a zero-free region with logarithmic exponent `theta` is
fed to the contour shift.  The cap supplies the `eta <= 1/2` normalisation. -/
noncomputable def zeroFreeRegionEta (theta T : ℝ) : ℝ :=
  min (1 / 2) ((Real.log (2 * T)) ^ (-theta))

/-- Rectangle height compatible with Mathlib's `2*pi` Fourier convention. -/
noncomputable def zeroFreeRegionHeight (T P : ℝ) : ℝ :=
  8 * Real.pi * T + P ^ 2

/-- Polynomial logarithmic bound for the regular part of `-zeta'/zeta`. -/
noncomputable def zeroFreeRegionRegularBound (m T : ℝ) : ℝ :=
  (Real.log (2 * T)) ^ m

/-- The saving required by the prime large-values interface at exponent
`beta`. -/
noncomputable def primeLargeValuesDecay (beta P T : ℝ) : ℝ :=
  Real.exp (-(Real.log P / (Real.log (2 * T)) ^ beta)) *
    (Real.log (2 * T)) ^ 2

/-- Quantitative zero-free-region data in the form used by the Mellin shift.

`region` is the number-theoretic input: nonvanishing and a bound for the
regular part on the full closed rectangle.  `envelope` records the elementary
two-region comparison which turns the raw contour error into the fixed
`4/5` saving, with `1/(2*T+1)` paying for the bounded-height regime. -/
structure ZeroFreeRegionData (theta m : ℝ) : Prop where
  theta_pos : 0 < theta
  region : ∀ (P : ℕ) (T : ℝ), 2 ≤ P → 1 ≤ T →
    let eta := zeroFreeRegionEta theta T
    let Z := zeroFreeRegionHeight T P
    let M := zeroFreeRegionRegularBound m T
    (∀ z : ℂ, 1 - eta ≤ z.re → z.re ≤ 2 → |z.im| ≤ Z →
        z ≠ 1 → riemannZeta z ≠ 0) ∧
      (∀ z : ℂ, 1 - eta ≤ z.re → z.re ≤ 2 → |z.im| ≤ Z →
        z ≠ 1 →
          ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤ M)
  envelope : ∃ D : ℝ, 1 ≤ D ∧ ∀ (P : ℕ) (T u : ℝ),
    2 ≤ P → 1 ≤ T → 1 ≤ |u| → |u| ≤ 4 * Real.pi * T →
    let eta := zeroFreeRegionEta theta T
    let Z := zeroFreeRegionHeight T P
    let M := zeroFreeRegionRegularBound m T
    let c := 1 + 1 / Real.log (2 * P)
    (M + 1) *
        (P ^ (1 - eta / 2) +
          P ^ c * Real.log (2 * P) / (Z - |u|) +
          P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)) ≤
      D * P *
        (1 / (2 * T + 1) + primeLargeValuesDecay (4 / 5) P T)

/-- A finite one-separated subset of `[-T,T]` has at most `2*T+1` points. -/
theorem card_le_two_mul_add_one_of_one_separated
    (T : ℝ) (𝒯 : Finset ℝ) (hT : 0 ≤ T)
    (hrange : ∀ t ∈ 𝒯, |t| ≤ T)
    (hsep : ∀ t ∈ 𝒯, ∀ s ∈ 𝒯, t ≠ s → 1 ≤ |t - s|) :
    (𝒯.card : ℝ) ≤ 2 * T + 1 := by
  classical
  let k : ℝ → ℕ := fun t => ⌊t + T⌋₊
  have hk_nonneg : ∀ t ∈ 𝒯, 0 ≤ t + T := by
    intro t ht
    have h := hrange t ht
    rw [abs_le] at h
    linarith
  have hkinj : Set.InjOn k (↑𝒯 : Set ℝ) := by
    intro t ht s hs hks
    have htmem : t ∈ 𝒯 := Finset.mem_coe.mp ht
    have hsmem : s ∈ 𝒯 := Finset.mem_coe.mp hs
    have hkt : ((k t : ℕ) : ℝ) ≤ t + T := Nat.floor_le (hk_nonneg t htmem)
    have hks' : ((k s : ℕ) : ℝ) ≤ s + T := Nat.floor_le (hk_nonneg s hsmem)
    have htk : t + T < (k t : ℕ) + 1 := Nat.lt_floor_add_one _
    have hsk : s + T < (k s : ℕ) + 1 := Nat.lt_floor_add_one _
    have hfloor : ((k t : ℕ) : ℝ) = (k s : ℕ) := by exact_mod_cast hks
    by_contra hne
    have habs : |t - s| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    exact (not_lt_of_ge (hsep t htmem s hsmem hne)) habs
  have hcardImage : 𝒯.card = (𝒯.image k).card := by
    exact (Finset.card_image_iff.mpr hkinj).symm
  have himage : 𝒯.image k ⊆ Finset.range (⌊2 * T⌋₊ + 1) := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨t, ht, rfl⟩ := hn
    rw [Finset.mem_range]
    have htupper := (abs_le.mp (hrange t ht)).2
    have hfloor : k t ≤ ⌊2 * T⌋₊ := by
      dsimp only [k]
      exact Nat.floor_mono (by linarith)
    omega
  have hcardNat : 𝒯.card ≤ ⌊2 * T⌋₊ + 1 := by
    rw [hcardImage]
    simpa using Finset.card_le_card himage
  have hfloorR : ((⌊2 * T⌋₊ : ℕ) : ℝ) ≤ 2 * T :=
    Nat.floor_le (by positivity)
  have hcardR : (𝒯.card : ℝ) ≤ ((⌊2 * T⌋₊ : ℕ) : ℝ) + 1 := by
    exact_mod_cast hcardNat
  linarith

/-- Mathlib's additive Fourier character equals the Mellin phase at frequency
`-2*pi*t`. -/
theorem fourierChar_neg_log_eq_primeMellin_phase
    (p : ℕ) (hp : p ≠ 0) (t : ℝ) :
    ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ) =
      (p : ℂ) ^ (I * ((-2 * Real.pi * t : ℝ) : ℂ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp
  have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
    rw [show (p : ℂ) = (((p : ℝ) : ℝ) : ℂ) by push_cast; rfl]
    exact (Complex.ofReal_log hp0.le).symm
  rw [Real.fourierChar_apply, Complex.cpow_def_of_ne_zero hpc, hlog]
  congr 1
  push_cast
  ring

set_option maxHeartbeats 800000

/-- **V-B-2, nucleus form.**  Quantitative zero-free data implies the prime
large-values estimate with exponent `4/5`, in the exact Fourier
normalisation used by the conjecture interface. -/
theorem prime_large_values_bound_of_zeroFreeRegionData
    {theta m : ℝ} (h : ZeroFreeRegionData theta m) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : ℕ) (Y : Finset ℕ),
      (∀ p ∈ Y, p.Prime) →
      (∀ p ∈ Y, P ≤ p ∧ p ≤ 2 * P) →
      ∀ (a : ℕ → ℂ) (T : ℝ) (𝒯 : Finset ℝ),
      2 ≤ P → 1 ≤ T → (∀ t ∈ 𝒯, |t| ≤ T) →
      (∀ t ∈ 𝒯, ∀ u ∈ 𝒯, t ≠ u → 1 ≤ |t - u|) →
      ∑ t ∈ 𝒯, ‖∑ p ∈ Y, (a p / (p : ℂ)) *
          ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ ^ 2 ≤
        C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay (4 / 5) P T) *
          (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) *
          (P : ℝ) / Real.log P := by
  classical
  obtain ⟨S, Cw, hSs, hS01, hS0, hS1, hCw0, hCw1, hCw2⟩ :=
    ExpSums.exists_master_transition
  obtain ⟨K, hK, hkernel⟩ := exists_primeMellin_kernel_bound
  obtain ⟨D, hD, henvelope⟩ := h.envelope
  let F : ℝ := K * (Cw + 1) ^ 2 * D
  let C : ℝ := 16 + 1000000 * (Cw + 1) ^ 2 + F
  have hF0 : 0 ≤ F := by
    dsimp [F]
    positivity
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith [sq_nonneg (Cw + 1), hF0]
  refine ⟨C, hC, ?_⟩
  intro P Y hYprime hYrange a T 𝒯 hP hT hrange hsep
  let eta := zeroFreeRegionEta theta T
  let Z := zeroFreeRegionHeight T P
  let M := zeroFreeRegionRegularBound m T
  let c := 1 + 1 / Real.log (2 * P)
  let position : ℝ → ℝ := fun t => -2 * Real.pi * t
  let A : ℝ := 250000 * (Cw + 1) ^ 2 * P
  let Raw : ℝ := P ^ (1 - eta / 2) +
    P ^ c * Real.log (2 * P) / (Z - 4 * Real.pi * T) +
    P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)
  let E : ℝ := K * (Cw + 1) ^ 2 * (M + 1) * Raw
  have hlogT : 0 < Real.log (2 * T) :=
    Real.log_pos (by linarith)
  have heta0 : 0 < eta := by
    dsimp only [eta, zeroFreeRegionEta]
    exact lt_min (by norm_num) (Real.rpow_pos_of_pos hlogT _)
  have heta1 : eta ≤ 1 / 2 := by
    dsimp only [eta, zeroFreeRegionEta]
    exact min_le_left _ _
  have hZ : 1 ≤ Z := by
    dsimp only [Z, zeroFreeRegionHeight]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
    nlinarith [sq_nonneg (P : ℝ)]
  have hM : 0 ≤ M := by
    dsimp only [M, zeroFreeRegionRegularBound]
    exact Real.rpow_nonneg hlogT.le _
  obtain ⟨hzero, hreg⟩ := h.region P T hP hT
  have hpositionRange : ∀ t ∈ 𝒯, |position t| ≤ 2 * Real.pi * T := by
    intro t ht
    have habscoeff : |(-2 * Real.pi : ℝ)| = 2 * Real.pi := by
      rw [abs_of_neg (by linarith [Real.pi_pos] : (-2 * Real.pi : ℝ) < 0)]
      ring
    dsimp only [position]
    rw [abs_mul, habscoeff]
    have := hrange t ht
    nlinarith [Real.pi_pos.le]
  have hpositionSep : ∀ t ∈ 𝒯, ∀ s ∈ 𝒯, t ≠ s →
      1 ≤ |position t - position s| := by
    intro t ht s hs hts
    have hgap := hsep t ht s hs hts
    have hpi2 : 1 ≤ 2 * Real.pi := by
      linarith [Real.pi_gt_three]
    have habscoeff : |(-2 * Real.pi : ℝ)| = 2 * Real.pi := by
      rw [abs_of_neg (by linarith [Real.pi_pos] : (-2 * Real.pi : ℝ) < 0)]
      ring
    dsimp only [position]
    rw [show -2 * Real.pi * t - -2 * Real.pi * s =
      (-2 * Real.pi) * (t - s) by ring, abs_mul, habscoeff]
    nlinarith [abs_nonneg (t - s)]
  have hdiffUpper : ∀ t ∈ 𝒯, ∀ s ∈ 𝒯,
      |position t - position s| ≤ 4 * Real.pi * T := by
    intro t ht s hs
    calc
      |position t - position s| ≤ |position t| + |position s| := abs_sub _ _
      _ ≤ 4 * Real.pi * T := by
        have ht' := hpositionRange t ht
        have hs' := hpositionRange s hs
        linarith
  have hdiffZ : ∀ t ∈ 𝒯, ∀ s ∈ 𝒯,
      |position t - position s| ≤ Z / 2 := by
    intro t ht s hs
    have hd := hdiffUpper t ht s hs
    dsimp only [Z, zeroFreeRegionHeight]
    have hP2 : (0 : ℝ) ≤ (P : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hRaw0 : 0 ≤ Raw := by
    have hden : 0 < Z - 4 * Real.pi * T := by
      have hPR : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
      have hpiT : 0 ≤ 4 * Real.pi * T := by positivity
      dsimp only [Z, zeroFreeRegionHeight]
      nlinarith [sq_pos_of_pos hPR]
    have hlog2P : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by
      have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
      linarith)
    have hlog4P : 0 ≤ Real.log (4 * P) := Real.log_nonneg (by
      have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
      linarith)
    dsimp only [Raw]
    positivity
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hkernelDiff : ∀ t ∈ 𝒯, ∀ s ∈ 𝒯, t ≠ s →
      ‖∑ p ∈ (Finset.Ioc 0 ⌊4 * (P : ℝ)⌋₊).filter Nat.Prime,
          ((primeMellinWindow S P p * Real.log p : ℝ) : ℂ) *
            (p : ℂ) ^ (I * ((position t - position s : ℝ) : ℂ))‖ ≤
        A / |position t - position s| ^ 2 + E := by
    intro t ht s hs hts
    let u := position t - position s
    have hu1 := hpositionSep t ht s hs hts
    have hu4 := hdiffUpper t ht s hs
    have huZ := hdiffZ t ht s hs
    have hk := hkernel S Cw P eta Z u M hSs hS01 hS0 hS1 hCw0 hCw1 hCw2
      (by exact_mod_cast hP) heta0 heta1 hZ hM hu1 huZ hzero hreg
    have hrawMono :
        P ^ (1 - eta / 2) +
              P ^ c * Real.log (2 * P) / (Z - |u|) +
              P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P) ≤ Raw := by
      have hdenU : 0 < Z - |u| := by linarith
      have hdenT : 0 < Z - 4 * Real.pi * T := by
        have hPR : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
        have hpiT : 0 ≤ 4 * Real.pi * T := by positivity
        dsimp only [Z, zeroFreeRegionHeight]
        nlinarith [sq_pos_of_pos hPR]
      have hnum : 0 ≤ P ^ c * Real.log (2 * P) := by
        have : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by
          have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
          linarith)
        positivity
      dsimp only [Raw]
      gcongr
    have hfac : 0 ≤ K * (Cw + 1) ^ 2 * (M + 1) := by positivity
    calc
      _ ≤ (250000 * (Cw + 1) ^ 2 * P) / |u| ^ 2 +
          K * (Cw + 1) ^ 2 * (M + 1) *
            (P ^ (1 - eta / 2) +
              P ^ c * Real.log (2 * P) / (Z - |u|) +
              P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)) := by
        simpa only [u, c] using hk
      _ ≤ (250000 * (Cw + 1) ^ 2 * P) / |u| ^ 2 +
          K * (Cw + 1) ^ 2 * (M + 1) * Raw :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hrawMono hfac)
      _ = A / |position t - position s| ^ 2 + E := by
        dsimp only [A, E, u]
  have hlv := prime_large_values_of_mellin_kernel S P Y a 𝒯 position A E
    hS01 hS1 hP hYprime hYrange hA0 hE0 hpositionSep hkernelDiff
  have hphase : ∀ t ∈ 𝒯,
      (∑ p ∈ Y, (a p / (p : ℂ)) *
          ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)) =
        ∑ p ∈ Y, (a p / (p : ℂ)) *
          (p : ℂ) ^ (I * (position t : ℂ)) := by
    intro t ht
    apply Finset.sum_congr rfl
    intro p hp
    rw [fourierChar_neg_log_eq_primeMellin_phase p
      (hYprime p hp).ne_zero t]
  have hmass : (∑ p ∈ Y, ‖a p / (p : ℂ)‖ ^ 2) =
      ∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [norm_div, Complex.norm_natCast, div_pow]
  have habsu : |4 * Real.pi * T| = 4 * Real.pi * T := by
    rw [abs_of_nonneg]
    positivity
  have henv := henvelope P T (4 * Real.pi * T) hP hT
    (by
      rw [abs_of_nonneg]
      · have hpi2 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
        nlinarith
      · positivity)
    (by rw [abs_of_nonneg (by positivity)])
  have hEnvRaw : (M + 1) * Raw ≤
      D * P * (1 / (2 * T + 1) + primeLargeValuesDecay (4 / 5) P T) := by
    simpa only [eta, Z, M, c, Raw, habsu] using henv
  have hcard := card_le_two_mul_add_one_of_one_separated T 𝒯 (by linarith)
    hrange hsep
  have hdenT : 0 < 2 * T + 1 := by linarith
  have hcardDiv : (𝒯.card : ℝ) * (1 / (2 * T + 1)) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one hdenT).2 hcard
  have hdecay0 : 0 ≤ primeLargeValuesDecay (4 / 5) P T := by
    dsimp only [primeLargeValuesDecay]
    positivity
  have hEbound : (𝒯.card : ℝ) * E ≤
      F * P * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay (4 / 5) P T) := by
    have hcard0 : 0 ≤ (𝒯.card : ℝ) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hEnvRaw hcard0
    have hinner : (𝒯.card : ℝ) *
        (1 / (2 * T + 1) + primeLargeValuesDecay (4 / 5) P T) ≤
      1 + (𝒯.card : ℝ) * primeLargeValuesDecay (4 / 5) P T := by
      nlinarith
    have hDP0 : 0 ≤ D * P := by positivity
    have hscaled' := mul_le_mul_of_nonneg_left hinner hDP0
    have hKF0 : 0 ≤ K * (Cw + 1) ^ 2 := by positivity
    dsimp only [E, F]
    calc
      (𝒯.card : ℝ) *
          (K * (Cw + 1) ^ 2 * (M + 1) * Raw) =
        K * (Cw + 1) ^ 2 *
          ((𝒯.card : ℝ) * ((M + 1) * Raw)) := by ring
      _ ≤ K * (Cw + 1) ^ 2 *
          ((𝒯.card : ℝ) *
            (D * P * (1 / (2 * T + 1) +
              primeLargeValuesDecay (4 / 5) P T))) :=
        mul_le_mul_of_nonneg_left hscaled hKF0
      _ = K * (Cw + 1) ^ 2 *
          (D * P * ((𝒯.card : ℝ) *
            (1 / (2 * T + 1) + primeLargeValuesDecay (4 / 5) P T))) := by ring
      _ ≤ K * (Cw + 1) ^ 2 *
          (D * P * (1 + (𝒯.card : ℝ) *
            primeLargeValuesDecay (4 / 5) P T)) :=
        mul_le_mul_of_nonneg_left hscaled' hKF0
      _ = (K * (Cw + 1) ^ 2 * D) * P *
          (1 + (𝒯.card : ℝ) * primeLargeValuesDecay (4 / 5) P T) := by ring
  have hcoeff : 16 * (P : ℝ) + 4 * A + (𝒯.card : ℝ) * E ≤
      C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay (4 / 5) P T) * P := by
    let Q : ℝ := 1 + (𝒯.card : ℝ) * primeLargeValuesDecay (4 / 5) P T
    have hQ1 : 1 ≤ Q := by
      dsimp only [Q]
      exact le_add_of_nonneg_right (mul_nonneg (by positivity) hdecay0)
    have hPR : 0 ≤ (P : ℝ) := by positivity
    have hbase : 16 * (P : ℝ) + 4 * A ≤
        (16 + 1000000 * (Cw + 1) ^ 2) * Q * P := by
      have hcoef0 : 0 ≤ 16 + 1000000 * (Cw + 1) ^ 2 := by positivity
      calc
        16 * (P : ℝ) + 4 * A =
            (16 + 1000000 * (Cw + 1) ^ 2) * P := by
          dsimp only [A]
          ring
        _ ≤ ((16 + 1000000 * (Cw + 1) ^ 2) * Q) * P :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hcoef0 hQ1) hPR
        _ = _ := by ring
    calc
      _ ≤ (16 + 1000000 * (Cw + 1) ^ 2) * Q * P + F * P * Q :=
        add_le_add hbase (by simpa only [Q, mul_assoc] using hEbound)
      _ = C * Q * P := by dsimp only [C]; ring
      _ = _ := rfl
  have hleftEq :
      (∑ t ∈ 𝒯, ‖∑ p ∈ Y, (a p / (p : ℂ)) *
          ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ ^ 2) =
        ∑ t ∈ 𝒯, ‖∑ p ∈ Y, (a p / (p : ℂ)) *
          (p : ℂ) ^ (I * (position t : ℂ))‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [hphase t ht]
  rw [hleftEq]
  calc
    _ ≤ (16 * (P : ℝ) + 4 * A + (𝒯.card : ℝ) * E) *
        (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) / Real.log P := by
      rw [← hmass]
      exact hlv
    _ ≤ (C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay (4 / 5) P T) * P) *
        (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) / Real.log P := by
      have hmass0 : 0 ≤ ∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2 := by positivity
      have hlogP : 0 < Real.log P :=
        Real.log_pos (by exact_mod_cast (show 1 < P by omega))
      gcongr
    _ = C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay (4 / 5) P T) *
          (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) * P / Real.log P := by ring

end MoltResearch
