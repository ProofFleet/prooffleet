import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryScaleClose

/-!
# Track R A2-V': close the explicit Fourier window

For fixed accuracy and interval length, all scale-dependent window
inequalities follow from one explicit base threshold.  The only hypotheses
left here concern the interval length itself; they will become the polynomial
`h` threshold in the final theorem.
-/

namespace MoltResearch

namespace Tao2015

open ExpSums

set_option maxHeartbeats 1200000

/-- Exact collection of window inequalities used by the one-slice and inner
schedule closures. -/
def SliceA2WindowClosed (eps : ℝ) (A1 A X H : ℕ) : Prop :=
  100 ≤ sliceA2GeomEps eps * H ∧
  2000 ≤ sliceA2EffectiveEps eps * H ∧
  3072000 * (sliceA2Parts eps : ℝ) *
      explicitSliceWindowDerivBound (sliceA2GeomEps eps) ≤
    sliceA2EffectiveEps eps ^ 2 * H ∧
  sliceA2Parts eps ≤ A ∧
  3 * H ≤ A ∧
  2 * H + 4 * sliceA2Collar (sliceA2GeomEps eps) H ≤
    A / sliceA2Parts eps ∧
  32 * (H : ℝ) ^ 2 ≤
    sliceA2EffectiveEps eps ^ 2 * (X : ℝ) ^ 2 ∧
  sliceA2OuterCutoff eps X H ≤ X ∧
  sliceA2OuterCutoff eps X H ≤ sliceA2TailCutoff X ∧
  sliceA2LowCutoff eps ≤ sliceA2OuterCutoff eps X H ∧
  3840 * (sliceA2Parts eps : ℝ) *
      (A / sliceA2Parts eps + 2 * H +
        4 * sliceA2Collar (sliceA2GeomEps eps) H : ℕ) ^ 2 *
      (X : ℝ) *
      explicitSliceWindowDerivBound (sliceA2GeomEps eps) ^ 2 ≤
    sliceA2EffectiveEps eps ^ 2 * (H : ℝ) ^ 3 * Real.pi ^ 2 *
      sliceA2TailCutoff X ^ 2 ∧
  2 * (sliceA2OuterCutoff eps X H + 2) ≤ X ∧
  Real.log (A1 : ℝ) / 2 ≤
    Real.log (2 * (sliceA2OuterCutoff eps X H + 2)) ∧
  Real.log (2 * (sliceA2OuterCutoff eps X H + 2)) ≤
    3 * Real.log (A1 : ℝ) ∧
  15 * (A / sliceA2Parts eps + 2 * H +
    4 * sliceA2Collar (sliceA2GeomEps eps) H) ≤ X

/-- The real threshold whose ceiling pays all scale-dependent window
margins. -/
noncomputable def sliceA2WindowScaleThreshold (eps : ℝ) (H : ℕ) : ℝ :=
  let e := sliceA2EffectiveEps eps
  let M := sliceA2Parts eps
  let B := explicitSliceWindowDerivBound (sliceA2GeomEps eps)
  let c := sliceA2OuterConstant * B / (e * H)
  max (32 * (H : ℝ) ^ 2 / e ^ 2)
    (max (1 / c)
      (max (3840 * (M : ℝ) * B ^ 2 /
          (e ^ 2 * (H : ℝ) ^ 3 * Real.pi ^ 2))
        (1 / (4 * c ^ 2))))

/-- A fixed collection of polynomial interval-length margins closes every
explicit-window condition uniformly for `A1 <= A <= A1^2` and
`A <= X <= 2A`. -/
theorem exists_sliceA2WindowClosed
    (eps : ℝ) (H : ℕ) (heps : 0 < eps)
    (hgeom : 100 ≤ sliceA2GeomEps eps * H)
    (hround : 2000 ≤ sliceA2EffectiveEps eps * H)
    (hlipschitz :
      3072000 * (sliceA2Parts eps : ℝ) *
          explicitSliceWindowDerivBound (sliceA2GeomEps eps) ≤
        sliceA2EffectiveEps eps ^ 2 * H)
    (houter :
      4 * sliceA2OuterConstant *
          explicitSliceWindowDerivBound (sliceA2GeomEps eps) ≤
        sliceA2EffectiveEps eps * H) :
    ∃ A0 : ℕ, ∀ A1 A X : ℕ, A0 ≤ A1 → A1 ≤ A → A ≤ A1 ^ 2 →
      A ≤ X → X ≤ 2 * A → SliceA2WindowClosed eps A1 A X H := by
  let e := sliceA2EffectiveEps eps
  let eg := sliceA2GeomEps eps
  let M := sliceA2Parts eps
  let B := explicitSliceWindowDerivBound eg
  let c := sliceA2OuterConstant * B / (e * H)
  let R := sliceA2WindowScaleThreshold eps H
  let A0 := max (3 * M * H) (max 10 (⌈R⌉₊ + 1))
  obtain ⟨he, he1, heps0⟩ := sliceA2EffectiveEps_bounds eps heps
  obtain ⟨hM0, hM30, hMbound⟩ := sliceA2Parts_bounds eps heps
  have heg : 0 < eg := by dsimp [eg]; exact (sliceA2GeomEps_bounds eps heps).1
  have hB : 0 < B := by
    dsimp [B]
    unfold explicitSliceWindowDerivBound
    positivity [one_le_explicitSliceWindowConstant]
  have hH : 0 < H := by
    by_contra! hz
    have hHzero : H = 0 := by omega
    rw [hHzero] at hround
    norm_num at hround
  have hc : 0 < c := by dsimp [c]; positivity [sliceA2OuterConstant_pos]
  have hR0 : 0 ≤ R := by
    dsimp [R, sliceA2WindowScaleThreshold]
    positivity
  refine ⟨A0, fun A1 A X hA1 hAA1 hAupper hAX hX2A ↦ ?_⟩
  have hbase : 3 * M * H ≤ A1 :=
    (le_max_left (3 * M * H) (max 10 (⌈R⌉₊ + 1))).trans hA1
  have hten : 10 ≤ A1 := (le_max_left 10 (⌈R⌉₊ + 1)).trans
    ((le_max_right (3 * M * H) (max 10 (⌈R⌉₊ + 1))).trans hA1)
  have hceil : ⌈R⌉₊ + 1 ≤ A1 :=
    (le_max_right 10 (⌈R⌉₊ + 1)).trans
      ((le_max_right (3 * M * H) (max 10 (⌈R⌉₊ + 1))).trans hA1)
  have hR : R ≤ (A1 : ℝ) := by
    calc
      R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
      _ ≤ (A1 : ℝ) := by exact_mod_cast (Nat.le_succ ⌈R⌉₊ |>.trans hceil)
  have hA1one : 1 ≤ A1 := by omega
  have hA1pos : (0 : ℝ) < A1 := by exact_mod_cast hA1one
  have hAone : 1 ≤ A := hA1one.trans hAA1
  have hXone : 1 ≤ X := hAone.trans hAX
  have hApos : (0 : ℝ) < A := by exact_mod_cast hAone
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hXone
  have hMA : M ≤ A := by
    have hMH : M ≤ 3 * M * H := by
      have : 1 ≤ H := hH
      nlinarith
    exact hMH.trans (hbase.trans hAA1)
  have h3H : 3 * H ≤ A := by
    have : 3 * H ≤ 3 * M * H := by
      have : 1 ≤ M := hM0
      nlinarith
    exact this.trans (hbase.trans hAA1)
  obtain ⟨hU, hU100, hU50, h50U, h2U1⟩ :=
    sliceA2Collar_bounds eg H (sliceA2GeomEps_bounds eps heps).2
      (by simpa [eg] using hgeom)
  let U := sliceA2Collar eg H
  have hcollarNat : 2 * H + 4 * U ≤ 3 * H := by
    dsimp [U] at h50U ⊢
    omega
  have hcollar : 2 * H + 4 * U ≤ A / M := by
    apply (Nat.le_div_iff_mul_le hM0).2
    have hscale : M * (3 * H) ≤ A := by
      have : 3 * M * H ≤ A := hbase.trans hAA1
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
    simpa [Nat.mul_comm] using
      (Nat.mul_le_mul_left M hcollarNat).trans hscale
  obtain ⟨hs, hsX, hs30, h3HX, hU', h2UH, hplat, hDeltaX, hrho⟩ :=
    sliceA2_floor_width_geometry A X H M U hM0 hM30 hMA hAX hX2A h3H
      hU h50U h2U1
  have hDeltaSmall : 15 * (A / M + 2 * H + 4 * U) ≤ X := by
    have hDeltaTwo : A / M + 2 * H + 4 * U ≤ 2 * (A / M) := by omega
    calc
      15 * (A / M + 2 * H + 4 * U) ≤ 15 * (2 * (A / M)) :=
        Nat.mul_le_mul_left 15 hDeltaTwo
      _ = 30 * (A / M) := by ring
      _ ≤ X := hs30
  have hconvR : 32 * (H : ℝ) ^ 2 / e ^ 2 ≤ (A1 : ℝ) :=
    (le_max_left _ _).trans hR
  have hconv : 32 * (H : ℝ) ^ 2 ≤ e ^ 2 * (X : ℝ) ^ 2 := by
    have hA1X : (A1 : ℝ) ≤ X := by exact_mod_cast hAA1.trans hAX
    have hXoneR : (1 : ℝ) ≤ X := by exact_mod_cast hXone
    have hXX : (X : ℝ) ≤ X ^ 2 := by
      simpa [pow_two] using mul_le_mul_of_nonneg_left hXoneR hXpos.le
    have := hconvR.trans (hA1X.trans hXX)
    have hmul := (div_le_iff₀ (sq_pos_of_pos he)).mp this
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hcQuarter : c ≤ 1 / 4 := by
    apply (div_le_iff₀ (mul_pos he (by exact_mod_cast hH))).2
    dsimp [c, e, B] at ⊢
    have hout := houter
    change 4 * sliceA2OuterConstant * B ≤ e * H at hout
    nlinarith
  have hKform : sliceA2OuterCutoff eps X H = c * X := by
    dsimp [c, e, B, eg]
    unfold sliceA2OuterCutoff
    ring
  have hKquarter : sliceA2OuterCutoff eps X H ≤ (X : ℝ) / 4 := by
    rw [hKform]
    exact (mul_le_mul_of_nonneg_right hcQuarter hXpos.le).trans_eq (by ring)
  have hKX : sliceA2OuterCutoff eps X H ≤ X :=
    hKquarter.trans (by linarith)
  have hKtail : sliceA2OuterCutoff eps X H ≤ sliceA2TailCutoff X := by
    unfold sliceA2TailCutoff
    have hXoneR : (1 : ℝ) ≤ X := by exact_mod_cast hXone
    exact hKX.trans (by
      simpa [pow_two] using mul_le_mul_of_nonneg_left hXoneR hXpos.le)
  have hlowR : 1 / c ≤ (A1 : ℝ) :=
    (le_max_left (1 / c) _).trans ((le_max_right _ _).trans hR)
  have hcX : 1 ≤ c * (X : ℝ) := by
    have hcA1 : 1 ≤ c * (A1 : ℝ) := by
      simpa [mul_comm] using (div_le_iff₀ hc).mp hlowR
    exact hcA1.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast hAA1.trans hAX) hc.le)
  have hlowK : sliceA2LowCutoff eps ≤ sliceA2OuterCutoff eps X H := by
    rw [hKform]
    exact (sliceA2LowCutoff_le_one eps heps).trans hcX
  have htwoT : 2 * (sliceA2OuterCutoff eps X H + 2) ≤ X := by
    have hX8nat : 8 ≤ X := (by norm_num : 8 ≤ 10).trans
      (hten.trans (hAA1.trans hAX))
    have hX8 : (8 : ℝ) ≤ X := by exact_mod_cast hX8nat
    nlinarith
  have htailR : 3840 * (M : ℝ) * B ^ 2 /
      (e ^ 2 * (H : ℝ) ^ 3 * Real.pi ^ 2) ≤ (A1 : ℝ) :=
    (le_max_left _ _).trans ((le_max_right (1 / c) _).trans
      ((le_max_right _ _).trans hR))
  have htailCoefficient : 3840 * (M : ℝ) * B ^ 2 ≤
      e ^ 2 * (H : ℝ) ^ 3 * Real.pi ^ 2 * X := by
    have hden : 0 < e ^ 2 * (H : ℝ) ^ 3 * Real.pi ^ 2 := by positivity
    have hA1X : (A1 : ℝ) ≤ X := by exact_mod_cast hAA1.trans hAX
    have hraw := htailR.trans hA1X
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (div_le_iff₀ hden).mp hraw
  have htail : 3840 * (M : ℝ) *
      (A / M + 2 * H + 4 * U : ℕ) ^ 2 * (X : ℝ) * B ^ 2 ≤
    e ^ 2 * (H : ℝ) ^ 3 * Real.pi ^ 2 *
      sliceA2TailCutoff X ^ 2 := by
    have hDeltaR : ((A / M + 2 * H + 4 * U : ℕ) : ℝ) ≤ X := by
      exact_mod_cast hDeltaX
    have hDeltaSq := pow_le_pow_left₀ (by positivity) hDeltaR 2
    unfold sliceA2TailCutoff
    calc
      _ = (3840 * (M : ℝ) * B ^ 2) *
          (((A / M + 2 * H + 4 * U : ℕ) : ℝ) ^ 2 * X) := by ring
      _ ≤ (3840 * (M : ℝ) * B ^ 2) * (X ^ 2 * X) := by
        gcongr
      _ = (3840 * (M : ℝ) * B ^ 2) * (X : ℝ) ^ 3 := by ring
      _ ≤ (e ^ 2 * (H : ℝ) ^ 3 * Real.pi ^ 2 * X) * X ^ 3 := by
        gcongr
      _ = e ^ 2 * (H : ℝ) ^ 3 * Real.pi ^ 2 * (X ^ 2) ^ 2 := by ring
  have hlogR : 1 / (4 * c ^ 2) ≤ (A1 : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hR))
  have hlogLower : Real.log (A1 : ℝ) / 2 ≤
      Real.log (2 * (sliceA2OuterCutoff eps X H + 2)) := by
    have hc2 : 0 < 4 * c ^ 2 := by positivity
    have hone : 1 ≤ 4 * c ^ 2 * (A1 : ℝ) := by
      simpa [mul_comm] using (div_le_iff₀ hc2).mp hlogR
    have hA1Xreal : (A1 : ℝ) ≤ X := by exact_mod_cast hAA1.trans hAX
    have hsq : (A1 : ℝ) ≤ (2 * c * X) ^ 2 := by
      have hA1nonneg : (0 : ℝ) ≤ A1 := by positivity
      calc
        (A1 : ℝ) = 1 * A1 := by ring
        _ ≤ (4 * c ^ 2 * A1) * A1 :=
          mul_le_mul_of_nonneg_right hone hA1nonneg
        _ ≤ (4 * c ^ 2 * X) * X := by gcongr
        _ = (2 * c * X) ^ 2 := by ring
    have hTpos : 0 < 2 * (sliceA2OuterCutoff eps X H + 2) := by
      have hKpos := sliceA2OuterCutoff_pos eps X H heps (by omega) hH
      positivity
    have htwocX : 2 * c * X ≤
        2 * (sliceA2OuterCutoff eps X H + 2) := by
      rw [hKform]
      nlinarith
    have hsqT : (A1 : ℝ) ≤
        (2 * (sliceA2OuterCutoff eps X H + 2)) ^ 2 :=
      hsq.trans (pow_le_pow_left₀ (by positivity) htwocX 2)
    have hlogs := Real.log_le_log hA1pos hsqT
    rw [Real.log_pow] at hlogs
    norm_num at hlogs
    linarith
  have hlogUpper : Real.log (2 * (sliceA2OuterCutoff eps X H + 2)) ≤
      3 * Real.log (A1 : ℝ) := by
    have htwoTpos : 0 < 2 * (sliceA2OuterCutoff eps X H + 2) := by
      have hKpos := sliceA2OuterCutoff_pos eps X H heps (by omega) hH
      positivity
    have htopNat : X ≤ 2 * A1 ^ 2 := hX2A.trans (Nat.mul_le_mul_left 2 hAupper)
    have htop : 2 * (sliceA2OuterCutoff eps X H + 2) ≤ (A1 : ℝ) ^ 3 := by
      calc
        _ ≤ (X : ℝ) := htwoT
        _ ≤ 2 * (A1 : ℝ) ^ 2 := by exact_mod_cast htopNat
        _ ≤ (A1 : ℝ) ^ 3 := by
          have hA1two : (2 : ℝ) ≤ A1 := by exact_mod_cast (show 2 ≤ A1 by omega)
          nlinarith [sq_nonneg (A1 : ℝ)]
    calc
      _ ≤ Real.log ((A1 : ℝ) ^ 3) := Real.log_le_log htwoTpos htop
      _ = 3 * Real.log (A1 : ℝ) := by rw [Real.log_pow]; norm_num
  exact ⟨hgeom, hround, hlipschitz, hMA, h3H,
    by simpa [M, eg, U] using hcollar,
    by simpa [e] using hconv, hKX, hKtail, hlowK,
    by simpa [M, e, eg, B, U] using htail, htwoT, hlogLower, hlogUpper,
    by simpa [M, eg, U] using hDeltaSmall⟩

end Tao2015

end MoltResearch
