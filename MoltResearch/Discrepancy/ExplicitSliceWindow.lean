import MoltResearch.Discrepancy.ExplicitBumpWindow

/-!
# Explicit short-slice windows

This leaf inserts `explicitBumpWindow` into the existing collar comparison.
Unlike the abstract `ContDiffBump` constructor, it exports a derivative bound
whose dependence on the geometric accuracy is explicitly linear.
-/

namespace MoltResearch

namespace ExpSums

open Real Finset Metric
open scoped ContDiff

set_option maxHeartbeats 800000 in
/-- One absolute constant controls explicit windows at every accuracy.  The
window has the same plateau and support as `exists_slice_window'`, the same
collar estimate, and derivative bound `3600*B/epsGeom`. -/
theorem exists_explicit_slice_window_constant :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ epsGeom : ℝ, 0 < epsGeom → epsGeom ≤ 1 →
      ∀ h : ℕ → ℂ, (∀ m, ‖h m‖ ≤ 1) →
      ∀ A s U H : ℕ, 1 ≤ A → 1 ≤ s → s ≤ A → 0 < U →
        2 * U ≤ H → ((U : ℝ) + 1) * ((A : ℝ) + s) ≤ (A : ℝ) * H →
        30 * s ≤ A → 3 * H ≤ A →
        epsGeom * (H : ℝ) ≤ 100 * U → 50 * (U : ℝ) ≤ epsGeom * H →
      ∃ eta : ℝ → ℝ,
        ContDiff ℝ ∞ eta ∧
        (∀ u, 0 ≤ eta u ∧ eta u ≤ 1) ∧
        (∀ u, eta u ≠ 0 → |u| ≤ 2) ∧
        (∀ u, |deriv eta u| ≤ 3600 * B / epsGeom) ∧
        ∀ n ∈ Finset.Ioc A (A + s),
          ‖((1 / (U : ℂ)) * ∑ u ∈ Finset.range U,
                ∑ m ∈ Finset.Ioc (n + u) (n + u + H), h m) -
              ∑ m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
                h m * ((eta (((A : ℝ) / H) *
                  (Real.log n - Real.log m)) : ℝ) : ℂ)‖
            ≤ 6 * (U : ℝ) + (H : ℝ) * s / A + 2 := by
  obtain ⟨B, hB, hBderiv⟩ := exists_explicitBumpWindow_deriv_bound
  refine ⟨B, hB, ?_⟩
  intro epsGeom heps heps1 h hb A s U H hA hs hsA hU hUH hplat
    hs30 h3H hU100 hU50
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hH0 : (0 : ℝ) < H := by
    have : 0 < H := by omega
    exact_mod_cast this
  have hAs0 : (0 : ℝ) < (A : ℝ) + s := by
    have : (0 : ℝ) < s := by exact_mod_cast hs
    linarith
  let T : ℝ := (A : ℝ) / H
  let t0 : ℝ := Real.log (1 + (U : ℝ) / (4 * ((A : ℝ) + s)))
  let t1 : ℝ := Real.log (1 + (U : ℝ) / A)
  let t2 : ℝ := Real.log (1 + (H : ℝ) / ((A : ℝ) + s))
  let t3 : ℝ := Real.log (1 + ((H : ℝ) + 2 * U) / A)
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨ht0, ht01, ht12, ht23, ht3⟩ :=
    slice_edge_geometry A s U H hA hs hsA hU hUH hplat
  have ht0' : 0 < t0 := by simpa [t0] using ht0
  have ht01' : t0 < t1 := by simpa [t0, t1] using ht01
  have ht12' : t1 < t2 := by simpa [t1, t2] using ht12
  have ht23' : t2 < t3 := by simpa [t2, t3] using ht23
  have ht3' : T * t3 ≤ 2 := by simpa [T, t3] using ht3
  let c : ℝ := -(T * (t1 + t2) / 2)
  let rIn : ℝ := T * (t2 - t1) / 2
  let gap : ℝ := T * min (t1 - t0) (t3 - t2)
  let rOut : ℝ := rIn + gap
  let eta : ℝ → ℝ := explicitBumpWindow c rIn rOut
  have hrIn : 0 < rIn := by
    change 0 < T * (t2 - t1) / 2
    exact div_pos (mul_pos hT (sub_pos.mpr ht12')) (by norm_num)
  have hgap : 0 < gap := by
    dsimp [gap]
    exact mul_pos hT (lt_min (sub_pos.mpr ht01') (sub_pos.mpr ht23'))
  have hrOut : rIn < rOut := by dsimp [rOut]; linarith
  obtain ⟨hetaSmooth, heta01, hetaPlateau, hetaSupport⟩ :=
    explicitBumpWindow_properties c rIn rOut hrIn hrOut
  have hrelative : epsGeom * rIn / 600 ≤ rOut - rIn := by
    have hratio := slice_ratio_lower A s U H epsGeom hA
      (by omega) hs30 h3H heps.le heps1 hU100 hU50
    dsimp [rOut, gap, rIn, T, t0, t1, t2, t3]
    convert hratio using 1 <;> ring
  have hetaDerivRaw : ∀ u, |deriv eta u| ≤
      1200 * B / (epsGeom * rIn) := by
    intro u
    simpa [eta] using hBderiv epsGeom c rIn rOut heps hrIn hrOut
      hrelative u
  have hrInLower : (1 : ℝ) / 3 ≤ rIn := by
    simpa [rIn, T, t1, t2] using
      slice_rIn_lower A s U H epsGeom hA (by omega) hs30 h3H heps1 hU50
  have hetaDeriv : ∀ u, |deriv eta u| ≤ 3600 * B / epsGeom := by
    intro u
    have hden : 0 < epsGeom * rIn := mul_pos heps hrIn
    have hB0 : 0 ≤ B := zero_le_one.trans hB
    apply (hetaDerivRaw u).trans
    rw [div_le_div_iff₀ hden heps]
    have hthree : 1 ≤ 3 * rIn := by linarith
    calc
      1200 * B * epsGeom = (1200 * B * epsGeom) * 1 := by ring
      _ ≤ (1200 * B * epsGeom) * (3 * rIn) :=
        mul_le_mul_of_nonneg_left hthree
          (mul_nonneg (mul_nonneg (by norm_num) hB0) heps.le)
      _ = 3600 * B * (epsGeom * rIn) := by ring
  have hetaPlatEdges : ∀ u, -(T * t2) ≤ u → u ≤ -(T * t1) → eta u = 1 := by
    intro u hu1 hu2
    apply hetaPlateau
    rw [abs_le]
    dsimp [c, rIn]
    constructor <;> nlinarith
  have hetaSuppEdges : ∀ u, eta u ≠ 0 → -(T * t3) < u ∧ u < -(T * t0) := by
    intro u hu
    obtain ⟨hlo, hhi⟩ := hetaSupport u hu
    have hmin1 : min (t1 - t0) (t3 - t2) ≤ t1 - t0 := min_le_left _ _
    have hmin2 : min (t1 - t0) (t3 - t2) ≤ t3 - t2 := min_le_right _ _
    dsimp [c, rOut, rIn, gap] at hlo hhi
    constructor <;> nlinarith
  have heta2 : ∀ u, eta u ≠ 0 → |u| ≤ 2 := by
    intro u hu
    obtain ⟨hlo, hhi⟩ := hetaSuppEdges u hu
    rw [abs_le]
    constructor
    · nlinarith [ht3']
    · have hTt0 : 0 < T * t0 := mul_pos hT ht0'
      linarith
  refine ⟨eta, hetaSmooth, heta01, heta2, hetaDeriv, ?_⟩
  intro n hn
  rw [Finset.mem_Ioc] at hn
  obtain ⟨hn1, hn2⟩ := hn
  have hr00 : (0 : ℝ) < (U : ℝ) / (4 * ((A : ℝ) + s)) := by positivity
  have hr01 : (U : ℝ) / (4 * ((A : ℝ) + s)) ≤ (U : ℝ) / A := by
    refine div_le_div_of_nonneg_left (by positivity) hA0 ?_
    linarith
  have hr12 : (U : ℝ) / A ≤ (H : ℝ) / ((A : ℝ) + s) := by
    rw [div_le_div_iff₀ hA0 hAs0]
    have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
    have hUH' : 2 * (U : ℝ) ≤ H := by exact_mod_cast hUH
    have hsA' : (s : ℝ) ≤ A := by exact_mod_cast hsA
    nlinarith
  have hr23 : (H : ℝ) / ((A : ℝ) + s) ≤ ((H : ℝ) + 2 * U) / A := by
    rw [div_le_div_iff₀ hAs0 hA0]
    have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
    have hsA' : (s : ℝ) ≤ A := by exact_mod_cast hsA
    nlinarith
  obtain ⟨hpsiPlat, hpsiSupp⟩ := psi_transfer A n hA hn1 ((A : ℝ) / H)
    (by positivity) ((U : ℝ) / (4 * ((A : ℝ) + s))) ((U : ℝ) / A)
    ((H : ℝ) / ((A : ℝ) + s)) (((H : ℝ) + 2 * U) / A)
    hr00 hr01 hr12 hr23 eta (by simpa [T, t1, t2] using hetaPlatEdges)
      (by simpa [T, t0, t3] using hetaSuppEdges)
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩ :=
    slice_cut_points A s U H n hA hs hsA hU hUH hplat hn1 hn2
  have hMsub : Finset.Ioc n
      (max ⌊(n : ℝ) * (1 + ((H : ℝ) + 2 * U) / A)⌋₊ (n + U + H)) ⊆
        Finset.Ioc A (A + s + 2 * H + 4 * U) := by
    intro k hk
    rw [Finset.mem_Ioc] at hk ⊢
    have hfl : ⌊(n : ℝ) * (1 + ((H : ℝ) + 2 * U) / A)⌋₊ ≤
        A + s + 2 * H + 4 * U := by
      refine Nat.floor_le_of_le ?_
      have hn2' : (n : ℝ) ≤ (A : ℝ) + s := by exact_mod_cast hn2
      have hx : (n : ℝ) * (1 + ((H : ℝ) + 2 * U) / A) ≤
          ((A : ℝ) + s) * (1 + ((H : ℝ) + 2 * U) / A) := by
        refine mul_le_mul_of_nonneg_right hn2' ?_
        positivity
      have hy : ((A : ℝ) + s) * (((H : ℝ) + 2 * U) / A) ≤
          2 * ((H : ℝ) + 2 * U) := by
        rw [mul_div_assoc', div_le_iff₀ hA0]
        have hsA' : (s : ℝ) ≤ A := by exact_mod_cast hsA
        nlinarith
      push_cast
      nlinarith [hx, hy]
    constructor
    · omega
    · have htop : max ⌊(n : ℝ) * (1 + ((H : ℝ) + 2 * U) / A)⌋₊
          (n + U + H) ≤ A + s + 2 * H + 4 * U := by
        rw [max_le_iff]
        constructor
        · exact hfl
        · omega
      omega
  have hmain := norm_shift_avg_sub_smooth_le_of_cuts h hb n U H hU
    ((n : ℝ) * (1 + (U : ℝ) / (4 * ((A : ℝ) + s))))
    ((n : ℝ) * (1 + (U : ℝ) / A))
    ((n : ℝ) * (1 + (H : ℝ) / ((A : ℝ) + s)))
    ((n : ℝ) * (1 + ((H : ℝ) + 2 * U) / A))
    hc1 hc2 hc3 hc4 hc5 hc0
    (Finset.Ioc A (A + s + 2 * H + 4 * U)) hMsub
    (fun m => eta (((A : ℝ) / H) * (Real.log n - Real.log m)))
    (fun m => heta01 _)
    hpsiPlat hpsiSupp
  exact le_trans hmain hc6

/-- A fixed choice of the absolute derivative constant. -/
noncomputable def explicitSliceWindowConstant : ℝ :=
  Classical.choose exists_explicit_slice_window_constant

theorem one_le_explicitSliceWindowConstant :
    1 ≤ explicitSliceWindowConstant :=
  (Classical.choose_spec exists_explicit_slice_window_constant).1

/-- The concrete polynomial derivative envelope used in the A.2 window. -/
noncomputable def explicitSliceWindowDerivBound (epsGeom : ℝ) : ℝ :=
  3600 * explicitSliceWindowConstant / epsGeom

/-- Fixed-constant form of `exists_explicit_slice_window_constant`. -/
theorem exists_explicit_slice_window
    (epsGeom : ℝ) (heps : 0 < epsGeom) (heps1 : epsGeom ≤ 1)
    (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1)
    (A s U H : ℕ) (hA : 1 ≤ A) (hs : 1 ≤ s) (hsA : s ≤ A)
    (hU : 0 < U) (hUH : 2 * U ≤ H)
    (hplat : ((U : ℝ) + 1) * ((A : ℝ) + s) ≤ (A : ℝ) * H)
    (hs30 : 30 * s ≤ A) (h3H : 3 * H ≤ A)
    (hU100 : epsGeom * (H : ℝ) ≤ 100 * U)
    (hU50 : 50 * (U : ℝ) ≤ epsGeom * H) :
    ∃ eta : ℝ → ℝ,
      ContDiff ℝ ∞ eta ∧
      (∀ u, 0 ≤ eta u ∧ eta u ≤ 1) ∧
      (∀ u, eta u ≠ 0 → |u| ≤ 2) ∧
      (∀ u, |deriv eta u| ≤ explicitSliceWindowDerivBound epsGeom) ∧
      ∀ n ∈ Finset.Ioc A (A + s),
        ‖((1 / (U : ℂ)) * ∑ u ∈ Finset.range U,
              ∑ m ∈ Finset.Ioc (n + u) (n + u + H), h m) -
            ∑ m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
              h m * ((eta (((A : ℝ) / H) *
                (Real.log n - Real.log m)) : ℝ) : ℂ)‖
          ≤ 6 * (U : ℝ) + (H : ℝ) * s / A + 2 := by
  have hspec := (Classical.choose_spec exists_explicit_slice_window_constant).2
    epsGeom heps heps1 h hb A s U H hA hs hsA hU hUH hplat hs30 h3H
      hU100 hU50
  simpa [explicitSliceWindowConstant, explicitSliceWindowDerivBound] using hspec

end ExpSums

end MoltResearch
