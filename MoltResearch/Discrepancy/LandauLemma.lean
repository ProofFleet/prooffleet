import MoltResearch.Discrepancy.ZetaBound
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville

/-!
# Track C: the Landau lemma substrate (Track R, campaign #3044, phase P3)

The road to the zero-free region: dividing analytic functions by their roots,
counting roots by the max-modulus principle (the Jensen-free quarter-ball
argument: roots confined to `B(s₀, R/4)` with the boundary at `R` cost a
modulus factor `≥ 3` each, so the count is `≤ M/log 3` outright), and the
Borel–Carathéodory bound on the root-free part — culminating in Landau's
inequality `-Re f'/f(s₀) ≤ C·M/R - ∑ Re 1/(s₀-ρ)`.

This file works with `ℂ → ℂ` throughout; `•` is `*`.
-/

namespace MoltResearch

namespace ExpSums

open Complex

/-- A point where an analytic function vanishes to finite positive order splits
off one linear factor **globally on any open set**: `f = (· - ρ) * g` with `g`
analytic on all of `U`.  (The local factorization from `analyticOrderAt` is
patched together with `f/(· - ρ)` away from `ρ`.) -/
theorem exists_analyticOnNhd_factor_of_zero {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) {ρ : ℂ} (hρ : ρ ∈ U)
    (h0 : f ρ = 0) (hord : analyticOrderAt f ρ ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ ∀ z ∈ U, f z = (z - ρ) * g z := by
  classical
  have hfρ : AnalyticAt ℂ f ρ := hf ρ hρ
  -- the finite order and its local factorization
  obtain ⟨n, hn⟩ : ∃ n : ℕ, analyticOrderAt f ρ = n :=
    ⟨(analyticOrderAt f ρ).toNat, (ENat.coe_toNat hord).symm⟩
  obtain ⟨g₀, hg₀an, hg₀ne, hg₀ev⟩ := (hfρ.analyticOrderAt_eq_natCast).mp hn
  have hn1 : 1 ≤ n := by
    by_contra h
    push_neg at h
    interval_cases n
    have h1 : f ρ = (ρ - ρ) ^ 0 • g₀ ρ := hg₀ev.self_of_nhds
    rw [h0] at h1
    simp at h1
    exact hg₀ne h1.symm
  -- the global quotient, patched at `ρ`
  set g : ℂ → ℂ := fun z =>
    if z = ρ then (0 : ℂ) ^ (n - 1) * g₀ ρ else f z / (z - ρ) with hg_def
  refine ⟨g, ?_, ?_⟩
  · -- analyticity: away from `ρ` by division, at `ρ` by congruence with the
    -- local factor `(· - ρ)^{n-1} * g₀`
    intro w hw
    rcases eq_or_ne w ρ with hwρ | hwρ
    · subst hwρ
      have hloc : AnalyticAt ℂ (fun z => (z - w) ^ (n - 1) * g₀ z) w := by
        exact ((analyticAt_id.sub analyticAt_const).pow _).mul hg₀an
      refine hloc.congr ?_
      have hev : ∀ᶠ z in nhds w, f z = (z - w) ^ n • g₀ z := hg₀ev
      filter_upwards [hev] with z hz
      rcases eq_or_ne z w with hzw | hzw
      · subst hzw
        simp only [hg_def, if_pos rfl, sub_self, smul_eq_mul]
      · simp only [hg_def, if_neg hzw]
        rw [hz, smul_eq_mul]
        have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
        have hsplit : (z - w) ^ n = (z - w) * (z - w) ^ (n - 1) := by
          conv_lhs => rw [show n = 1 + (n - 1) from by omega]
          rw [pow_add, pow_one]
        rw [hsplit]
        field_simp
    · have hden : AnalyticAt ℂ (fun z => z - ρ) w :=
        analyticAt_id.sub analyticAt_const
      have hdiv : AnalyticAt ℂ (fun z => f z / (z - ρ)) w :=
        (hf w hw).div hden (sub_ne_zero.mpr hwρ)
      refine hdiv.congr ?_
      have hopen : IsOpen {z : ℂ | z ≠ ρ} := isOpen_ne
      filter_upwards [hopen.mem_nhds hwρ] with z hz
      simp only [hg_def, if_neg hz]
  · -- the factorization identity on `U`
    intro z _
    rcases eq_or_ne z ρ with hzρ | hzρ
    · subst hzρ
      rw [h0, sub_self, zero_mul]
    · simp only [hg_def, if_neg hzρ]
      have hzρ' : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
      field_simp

/-- **Fuel-inducted root extraction**: either `f` factors as at most `fuel`
linear factors rooted in `S` times a quotient nonvanishing on `S`, or as
exactly `fuel` such factors times an analytic quotient.  Pure structural
induction — the second branch is refuted downstream by the max-modulus root
count, which is what terminates the extraction in applications. -/
theorem exists_prod_factor_of_zeros (f : ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (S : Set ℂ) (hSU : S ⊆ U)
    (hne : ∀ ρ ∈ S, ¬ (∀ᶠ z in nhds ρ, f z = 0)) (fuel : ℕ) :
    ∃ (L : List ℂ) (g : ℂ → ℂ), (∀ ρ ∈ L, ρ ∈ S) ∧ AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ U, f z = (L.map (fun ρ => z - ρ)).prod * g z) ∧
      L.length ≤ fuel ∧
      (L.length = fuel ∨ ∀ ρ ∈ S, g ρ ≠ 0) := by
  classical
  induction fuel with
  | zero =>
    exact ⟨[], f, by simp, hf, fun z _ => by simp, le_refl 0, Or.inl rfl⟩
  | succ m ih =>
    obtain ⟨L, g, hLS, hg, hfac, hlen, hdisj⟩ := ih
    rcases hdisj with hfull | hnv
    · -- the quotient may still vanish somewhere on `S`: extract one more root
      by_cases hz : ∃ ρ ∈ S, g ρ = 0
      · obtain ⟨ρ, hρS, hgρ⟩ := hz
        -- the quotient inherits non-local-vanishing from `f`
        have hgord : analyticOrderAt g ρ ≠ ⊤ := by
          intro htop
          have hgev : ∀ᶠ z in nhds ρ, g z = 0 :=
            analyticOrderAt_eq_top.mp htop
          refine hne ρ hρS ?_
          have hUnhds : ∀ᶠ z in nhds ρ, z ∈ U :=
            hU.mem_nhds (hSU hρS)
          filter_upwards [hgev, hUnhds] with z hz1 hz2
          rw [hfac z hz2, hz1, mul_zero]
        obtain ⟨g', hg', hfac'⟩ :=
          exists_analyticOnNhd_factor_of_zero hU hg (hSU hρS) hgρ hgord
        refine ⟨ρ :: L, g', fun τ hτ => ?_, hg', fun z hz => ?_, ?_, Or.inl ?_⟩
        · rcases List.mem_cons.mp hτ with h | h
          · exact h ▸ hρS
          · exact hLS τ h
        · rw [hfac z hz, hfac' z hz]
          simp only [List.map_cons, List.prod_cons]
          ring
        · simpa using Nat.succ_le_succ (le_of_eq hfull)
        · simpa using hfull
      · -- no zeros left: the quotient is nonvanishing on `S`
        push_neg at hz
        exact ⟨L, g, hLS, hg, hfac, le_trans hlen (Nat.le_succ m),
          Or.inr hz⟩
    · exact ⟨L, g, hLS, hg, hfac, le_trans hlen (Nat.le_succ m), Or.inr hnv⟩

/-- Lower bound for a product of linear factors, all of size `≥ r`. -/
theorem le_norm_list_prod_sub {z : ℂ} {L : List ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hL : ∀ ρ ∈ L, r ≤ ‖z - ρ‖) :
    r ^ L.length ≤ ‖(L.map (fun ρ => z - ρ)).prod‖ := by
  induction L with
  | nil => simp
  | cons ρ L ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, norm_mul]
    have h1 : r ≤ ‖z - ρ‖ := hL ρ (List.mem_cons_self ..)
    have h2 : r ^ L.length ≤ ‖(L.map (fun ρ => z - ρ)).prod‖ :=
      ih fun τ hτ => hL τ (List.mem_cons_of_mem _ hτ)
    calc r ^ (L.length + 1) = r * r ^ L.length := by ring
      _ ≤ ‖z - ρ‖ * ‖(L.map (fun ρ => z - ρ)).prod‖ :=
        mul_le_mul h1 h2 (by positivity) (norm_nonneg _)

/-- Upper bound for a product of linear factors, all of size `≤ r`. -/
theorem norm_list_prod_sub_le {z : ℂ} {L : List ℂ} {r : ℝ}
    (hL : ∀ ρ ∈ L, ‖z - ρ‖ ≤ r) :
    ‖(L.map (fun ρ => z - ρ)).prod‖ ≤ r ^ L.length := by
  induction L with
  | nil => simp
  | cons ρ L ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, norm_mul]
    have h1 : ‖z - ρ‖ ≤ r := hL ρ (List.mem_cons_self ..)
    have h2 : ‖(L.map (fun ρ => z - ρ)).prod‖ ≤ r ^ L.length :=
      ih fun τ hτ => hL τ (List.mem_cons_of_mem _ hτ)
    calc ‖z - ρ‖ * ‖(L.map (fun ρ => z - ρ)).prod‖
        ≤ r * r ^ L.length :=
        mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = r ^ (L.length + 1) := by ring

/-- **The quarter-ball root count** (Jensen-free): a factorization
`f = ∏(·-ρ_j)·g` on a neighborhood of `closedBall c R` with all roots in the
quarter-ball `closedBall c (R/4)` forces `3^k·‖f c‖ ≤ B` where `B` bounds
`‖f‖` on the sphere — each root costs a modulus factor `(3R/4)/(R/4) = 3` by
the maximum principle applied to `g`. -/
theorem three_pow_mul_le_of_prod_factor {f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall c R ⊆ U)
    (hg : AnalyticOnNhd ℂ g U) {L : List ℂ}
    (hLball : ∀ ρ ∈ L, ρ ∈ Metric.closedBall c (R/4))
    (hfac : ∀ z ∈ U, f z = (L.map (fun ρ => z - ρ)).prod * g z)
    {B : ℝ} (hB : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ B) :
    3 ^ L.length * ‖f c‖ ≤ B := by
  set k : ℕ := L.length with hk_def
  -- the maximum principle for `g` on the ball
  have hgc : ‖g c‖ ≤ B / ((3/4) * R) ^ k := by
    have hbd : Bornology.IsBounded (Metric.ball c R) := Metric.isBounded_ball
    have hdiff : DiffContOnCl ℂ g (Metric.ball c R) := by
      have h1 : DifferentiableOn ℂ g (Metric.closedBall c R) := by
        intro z hz
        exact (hg z (hball hz)).differentiableAt.differentiableWithinAt
      rw [← closure_ball c hR.ne'] at h1
      exact h1.diffContOnCl
    have hfr : ∀ z ∈ frontier (Metric.ball c R), ‖g z‖ ≤ B / ((3/4) * R) ^ k := by
      rw [frontier_ball c hR.ne']
      intro z hz
      have hzU : z ∈ U := hball (Metric.sphere_subset_closedBall hz)
      have hzc : dist z c = R := Metric.mem_sphere.mp hz
      have hroots : ∀ ρ ∈ L, (3/4) * R ≤ ‖z - ρ‖ := by
        intro ρ hρ
        have h1 : dist ρ c ≤ R/4 := Metric.mem_closedBall.mp (hLball ρ hρ)
        have h2 : ‖z - ρ‖ = dist z ρ := by rw [dist_eq_norm]
        rw [h2]
        calc (3/4) * R = R - R/4 := by ring
          _ ≤ dist z c - dist ρ c := by linarith
          _ ≤ dist z ρ := by
              have := dist_triangle z ρ c
              have h3 : dist ρ c = dist ρ c := rfl
              linarith [dist_triangle z ρ c]
      have hprod : ((3/4) * R) ^ k ≤ ‖(L.map (fun ρ => z - ρ)).prod‖ :=
        le_norm_list_prod_sub (by positivity) hroots
      have hfz := hfac z hzU
      have hfB := hB z hz
      rw [hfz, norm_mul] at hfB
      have hpos : (0:ℝ) < ((3/4) * R) ^ k := by positivity
      rw [le_div_iff₀ hpos]
      calc ‖g z‖ * ((3/4) * R) ^ k
          ≤ ‖g z‖ * ‖(L.map (fun ρ => z - ρ)).prod‖ :=
            mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = ‖(L.map (fun ρ => z - ρ)).prod‖ * ‖g z‖ := by ring
        _ ≤ B := hfB
    have hcc : c ∈ closure (Metric.ball c R) := by
      rw [closure_ball c hR.ne']
      exact Metric.mem_closedBall_self hR.le
    exact Complex.norm_le_of_forall_mem_frontier_norm_le hbd hdiff hfr hcc
  -- the center factorization and the quarter-ball upper bound
  have hcU : c ∈ U := hball (Metric.mem_closedBall_self hR.le)
  have hfc : ‖f c‖ ≤ (R/4) ^ k * ‖g c‖ := by
    rw [hfac c hcU, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine norm_list_prod_sub_le fun ρ hρ => ?_
    have h1 : dist ρ c ≤ R/4 := Metric.mem_closedBall.mp (hLball ρ hρ)
    rw [show ‖c - ρ‖ = dist ρ c from by rw [dist_eq_norm, norm_sub_rev]]
    exact h1
  -- combine: `3^k·‖f c‖ ≤ 3^k·(R/4)^k·‖g c‖ = ((3/4)R)^k·‖g c‖ ≤ B`
  have hkey : (3:ℝ) ^ k * ((R/4) ^ k * ‖g c‖) ≤ B := by
    have h1 : (3:ℝ) ^ k * (R/4) ^ k = ((3/4) * R) ^ k := by
      rw [← mul_pow]
      congr 1
      ring
    calc (3:ℝ) ^ k * ((R/4) ^ k * ‖g c‖)
        = ((3/4) * R) ^ k * ‖g c‖ := by rw [← h1]; ring
      _ ≤ ((3/4) * R) ^ k * (B / ((3/4) * R) ^ k) :=
          mul_le_mul_of_nonneg_left hgc (by positivity)
      _ = B := by
          field_simp
  calc (3:ℝ) ^ k * ‖f c‖ ≤ (3:ℝ) ^ k * ((R/4) ^ k * ‖g c‖) :=
        mul_le_mul_of_nonneg_left hfc (by positivity)
    _ ≤ B := hkey

/-- **The normalized logarithm of a nonvanishing function on a disk**: a branch
`φ` with `φ c = 0`, `exp ∘ φ = g/g c`, and `deriv`-witness `g'/g` — built as
the Morera primitive of the logarithmic derivative, with `exp (-φ) * g`
constant on the (convex) ball. -/
theorem exists_log_branch {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.ball c R ⊆ U)
    (hne : ∀ z ∈ Metric.ball c R, g z ≠ 0) :
    ∃ φ : ℂ → ℂ, φ c = 0 ∧
      (∀ z ∈ Metric.ball c R, Complex.exp (φ z) = g z / g c) ∧
      (∀ z ∈ Metric.ball c R, HasDerivAt φ (deriv g z / g z) z) := by
  have hcball : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hgc : g c ≠ 0 := hne c hcball
  -- the logarithmic derivative is holomorphic on the ball
  have hld : DifferentiableOn ℂ (fun z => deriv g z / g z) (Metric.ball c R) := by
    intro z hz
    have h1 : AnalyticAt ℂ (deriv g) z := (hg z (hball hz)).deriv
    have h2 : AnalyticAt ℂ g z := hg z (hball hz)
    exact ((h1.div h2 (hne z hz)).differentiableAt).differentiableWithinAt
  -- its Morera primitive, normalized at the center
  obtain ⟨Φ, hΦ⟩ := hld.isExactOn_ball
  set φ : ℂ → ℂ := fun z => Φ z - Φ c with hφ_def
  have hφc : φ c = 0 := by simp [hφ_def]
  have hφd : ∀ z ∈ Metric.ball c R, HasDerivAt φ (deriv g z / g z) z := by
    intro z hz
    simpa [hφ_def] using (hΦ z hz).sub_const (Φ c)
  refine ⟨φ, hφc, ?_, hφd⟩
  -- `exp (-φ) * g` has zero derivative, hence is constant on the convex ball
  set E : ℂ → ℂ := fun z => Complex.exp (-φ z) * g z with hE_def
  have hEd : ∀ z ∈ Metric.ball c R, HasDerivAt E 0 z := by
    intro z hz
    have h1 : HasDerivAt (fun w => Complex.exp (-φ w))
        (Complex.exp (-φ z) * (-(deriv g z / g z))) z := by
      have h2 : HasDerivAt (fun w => -φ w) (-(deriv g z / g z)) z :=
        (hφd z hz).neg
      simpa using (Complex.hasDerivAt_exp (-φ z)).comp z h2
    have h3 : HasDerivAt g (deriv g z) z :=
      ((hg z (hball hz)).differentiableAt).hasDerivAt
    have h4 := h1.mul h3
    have hEeq : E = (fun w => Complex.exp (-φ w)) * g := by
      funext w
      simp [hE_def]
    rw [hEeq]
    convert h4 using 1
    field_simp [hne z hz]
    ring
  have hEconst : ∀ z ∈ Metric.ball c R, E z = E c := by
    intro z hz
    have hconv : Convex ℝ (Metric.ball c R) := convex_ball c R
    have hEdiff : DifferentiableOn ℂ E (Metric.ball c R) := fun w hw =>
      ((hEd w hw).differentiableAt).differentiableWithinAt
    have hfz : ∀ w ∈ Metric.ball c R,
        fderivWithin ℂ E (Metric.ball c R) w = 0 := by
      intro w hw
      have h1 : HasFDerivAt E
          ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (0:ℂ))) w :=
        (hEd w hw).hasFDerivAt
      have h2 := h1.hasFDerivWithinAt.fderivWithin
        ((Metric.isOpen_ball).uniqueDiffWithinAt hw)
      rw [h2]
      exact ContinuousLinearMap.ext fun v => by simp
    exact hconv.is_const_of_fderivWithin_eq_zero hEdiff hfz hz hcball
  intro z hz
  have h1 := hEconst z hz
  have h2 : E c = g c := by
    simp [hE_def, hφc]
  rw [h2] at h1
  have h1' : Complex.exp (-φ z) * g z = g c := by
    simpa [hE_def] using h1
  -- from `exp (-φ z) * g z = g c` conclude `exp (φ z) = g z / g c`
  have h3 : Complex.exp (-φ z) ≠ 0 := Complex.exp_ne_zero _
  have h4 : Complex.exp (φ z) * Complex.exp (-φ z) = 1 := by
    rw [← Complex.exp_add]
    simp
  field_simp [hgc]
  calc Complex.exp (φ z) * g c
      = Complex.exp (φ z) * (Complex.exp (-φ z) * g z) := by rw [h1']
    _ = (Complex.exp (φ z) * Complex.exp (-φ z)) * g z := by ring
    _ = g z := by rw [h4]; ring

/-- **The Borel–Carathéodory bound on the logarithmic derivative**: if `g` is
analytic and nonvanishing on `ball c R` with `‖g‖ ≤ e^M·‖g c‖` throughout,
then `‖g'/g(c)‖ ≤ 4(M+1)/R` — via the normalized log branch, the
Borel–Carathéodory theorem at strictness pad `M+1`, and the Cauchy derivative
estimate at radius `R/2`. -/
theorem norm_logDeriv_le_of_ratio_le {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.ball c R ⊆ U)
    (hne : ∀ z ∈ Metric.ball c R, g z ≠ 0) {M : ℝ}
    (hratio : ∀ z ∈ Metric.ball c R, ‖g z‖ ≤ Real.exp M * ‖g c‖) :
    ‖deriv g c / g c‖ ≤ 4 * (M + 1) / R := by
  have hcball : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hgc : g c ≠ 0 := hne c hcball
  have hgc0 : (0:ℝ) < ‖g c‖ := norm_pos_iff.mpr hgc
  -- `M ≥ 0` from the ratio bound at the center
  have hM0 : 0 ≤ M := by
    have h1 := hratio c hcball
    by_contra h
    push_neg at h
    have h2 : Real.exp M < 1 := Real.exp_lt_one_iff.mpr h
    nlinarith [mul_lt_mul_of_pos_right h2 hgc0]
  -- the log branch and its real-part bound
  obtain ⟨φ, hφc, hφexp, hφd⟩ := exists_log_branch hU hg hR hball hne
  have hφre : ∀ z ∈ Metric.ball c R, (φ z).re ≤ M := by
    intro z hz
    have h1 : ‖Complex.exp (φ z)‖ = ‖g z‖ / ‖g c‖ := by
      rw [hφexp z hz, norm_div]
    have h2 : Real.exp ((φ z).re) ≤ Real.exp M := by
      rw [← Complex.norm_exp, h1]
      rw [div_le_iff₀ hgc0]
      exact hratio z hz
    exact (Real.exp_le_exp).mp h2
  -- recenter at the origin
  set ψ : ℂ → ℂ := fun w => φ (c + w) with hψ_def
  have htrans : ∀ w : ℂ, w ∈ Metric.ball (0:ℂ) R → c + w ∈ Metric.ball c R := by
    intro w hw
    rw [Metric.mem_ball] at hw ⊢
    simpa [dist_eq_norm] using hw
  have hψd : ∀ w ∈ Metric.ball (0:ℂ) R,
      HasDerivAt ψ (deriv g (c + w) / g (c + w)) w := by
    intro w hw
    have h1 := hφd (c + w) (htrans w hw)
    have h2 : HasDerivAt (fun v : ℂ => c + v) 1 w :=
      (hasDerivAt_id w).const_add c
    simpa [hψ_def] using (h1.comp w h2)
  have hψdiff : DifferentiableOn ℂ ψ (Metric.ball (0:ℂ) R) := fun w hw =>
    ((hψd w hw).differentiableAt).differentiableWithinAt
  have hψ0 : ψ 0 = 0 := by
    simp [hψ_def, hφc]
  -- Borel–Carathéodory at strictness pad `M+1`, evaluated on the `R/2` sphere
  have hBC : ∀ z ∈ Metric.sphere (0:ℂ) (R/2), ‖ψ z‖ ≤ 2 * (M + 1) := by
    intro z hz
    have hz' : z ∈ Metric.ball (0:ℂ) R := by
      rw [Metric.mem_sphere] at hz
      rw [Metric.mem_ball]
      rw [hz]
      linarith
    have hmaps : Set.MapsTo ψ (Metric.ball (0:ℂ) R) {w : ℂ | w.re < M + 1} := by
      intro w hw
      have h1 : (ψ w).re ≤ M := hφre (c + w) (htrans w hw)
      simp only [Set.mem_setOf_eq]
      linarith
    have hball0 : Metric.ball (0:ℂ) R = Metric.ball 0 R := rfl
    have h2 := Complex.borelCaratheodory (M := M + 1) (by linarith) hψdiff
      hmaps hR hz'
    rw [hψ0] at h2
    simp only [norm_zero, zero_mul, zero_div, add_zero] at h2
    have hznorm : ‖z‖ = R/2 := by
      rw [Metric.mem_sphere] at hz
      simpa [dist_eq_norm] using hz
    rw [hznorm] at h2
    have h3 : R - R/2 = R/2 := by ring
    rw [h3] at h2
    calc ‖ψ z‖ ≤ 2 * (M + 1) * (R/2) / (R/2) := h2
      _ = 2 * (M + 1) := by field_simp
  -- the Cauchy derivative estimate at radius `R/2`
  have hR2 : (0:ℝ) < R/2 := by linarith
  have hdiff2 : DiffContOnCl ℂ ψ (Metric.ball (0:ℂ) (R/2)) := by
    have h1 : DifferentiableOn ℂ ψ (Metric.closedBall (0:ℂ) (R/2)) := by
      refine hψdiff.mono ?_
      intro w hw
      rw [Metric.mem_closedBall] at hw
      rw [Metric.mem_ball]
      linarith
    rw [← closure_ball (0:ℂ) hR2.ne'] at h1
    exact h1.diffContOnCl
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR2
    hdiff2 hBC
  -- identify the derivative at the origin
  have hψ0d : HasDerivAt ψ (deriv g c / g c) 0 := by
    have h1 := hψd 0 (Metric.mem_ball_self hR)
    simpa using h1
  rw [hψ0d.deriv] at hcauchy
  calc ‖deriv g c / g c‖ ≤ 2 * (M + 1) / (R/2) := hcauchy
    _ = 4 * (M + 1) / R := by
        field_simp
        ring

/-- The derivative of a product of linear factors, in logarithmic form, at a
point avoiding all roots. -/
theorem hasDerivAt_list_prod_sub {L : List ℂ} {z : ℂ} (hz : ∀ ρ ∈ L, z ≠ ρ) :
    HasDerivAt (fun w => (L.map (fun ρ => w - ρ)).prod)
      ((L.map (fun ρ => z - ρ)).prod * (L.map (fun ρ => 1/(z - ρ))).sum) z := by
  induction L with
  | nil =>
    simpa using hasDerivAt_const z (1:ℂ)
  | cons ρ L ih =>
    have hzρ : z - ρ ≠ 0 :=
      sub_ne_zero.mpr (hz ρ (List.mem_cons_self ..))
    have hL := ih fun τ hτ => hz τ (List.mem_cons_of_mem _ hτ)
    have hlin : HasDerivAt (fun w : ℂ => w - ρ) 1 z := by
      simpa using (hasDerivAt_id z).sub_const ρ
    have hmul := hlin.mul hL
    have heq : ((fun w : ℂ => w - ρ) * fun w => (L.map (fun τ => w - τ)).prod)
        = (fun w => (((ρ :: L).map (fun τ => w - τ)).prod)) := by
      funext w
      simp [List.map_cons, List.prod_cons]
    rw [heq] at hmul
    have hval : 1 * (L.map (fun τ => z - τ)).prod
        + (z - ρ) * ((L.map (fun τ => z - τ)).prod
          * (L.map (fun τ => 1/(z - τ))).sum)
        = ((ρ :: L).map (fun τ => z - τ)).prod
          * ((ρ :: L).map (fun τ => 1/(z - τ))).sum := by
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      field_simp
    rw [hval] at hmul
    exact hmul

/-- **The logarithmic derivative of a factorization**: at a point where the
quotient and all linear factors are nonvanishing,
`f'/f = ∑ 1/(c-ρ) + g'/g`. -/
theorem deriv_div_of_prod_factor {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) {L : List ℂ}
    (hfac : ∀ z ∈ U, f z = (L.map (fun ρ => z - ρ)).prod * g z)
    {c : ℂ} (hc : c ∈ U) (hLc : ∀ ρ ∈ L, c ≠ ρ) (hgc : g c ≠ 0) :
    deriv f c / f c = (L.map (fun ρ => 1/(c - ρ))).sum + deriv g c / g c := by
  have hP := hasDerivAt_list_prod_sub hLc
  have hgd : HasDerivAt g (deriv g c) c :=
    ((hg c hc).differentiableAt).hasDerivAt
  have hprod := hP.mul hgd
  -- transfer to `f` via the eventual factorization
  have hev : (fun z => (L.map (fun ρ => z - ρ)).prod * g z) =ᶠ[nhds c] f := by
    filter_upwards [hU.mem_nhds hc] with z hz
    exact (hfac z hz).symm
  have hfd := hprod.congr_of_eventuallyEq hev.symm
  have hPc : (L.map (fun ρ => c - ρ)).prod ≠ 0 := by
    rw [Ne, List.prod_eq_zero_iff]
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨ρ, hρL, hρ0⟩ := hmem
    exact (sub_ne_zero.mpr (hLc ρ hρL)) hρ0
  have hfc : f c ≠ 0 := by
    rw [hfac c hc]
    exact mul_ne_zero hPc hgc
  rw [hfd.deriv, hfac c hc]
  field_simp

/-- **Landau's inequality** (Jensen-free form): if `f` is analytic on a
neighborhood of `closedBall c R`, `f c ≠ 0`, `‖f‖ ≤ e^M·‖f c‖` on the ball,
all zeros in the quarter-ball have real part `≤ re c`, and `ρ₀` is such a
zero, then `-Re (f'/f)(c) ≤ 4(M+1)/R − Re (1/(c-ρ₀))`. -/
theorem landau_inequality {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall c R ⊆ U) (hfc : f c ≠ 0) {M : ℝ}
    (hratio : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ Real.exp M * ‖f c‖)
    (hre : ∀ z ∈ Metric.closedBall c (R/4), f z = 0 → z.re ≤ c.re)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Metric.closedBall c (R/4)) (hfρ₀ : f ρ₀ = 0) :
    -(deriv f c / f c).re ≤ 16 * (M + 1) / R - (1/(c - ρ₀)).re := by
  classical
  have hfc0 : (0:ℝ) < ‖f c‖ := norm_pos_iff.mpr hfc
  have hM0 : 0 ≤ M := by
    have h1 := hratio c (Metric.mem_closedBall_self hR.le)
    by_contra h
    push_neg at h
    have h2 : Real.exp M < 1 := Real.exp_lt_one_iff.mpr h
    nlinarith [mul_lt_mul_of_pos_right h2 hfc0]
  -- the zero set of the quarter-ball, inside the open ball
  set S : Set ℂ := {z ∈ Metric.closedBall c (R/4) | f z = 0} with hS_def
  have hSball : S ⊆ Metric.ball c R := by
    intro z hz
    have h1 : dist z c ≤ R/4 := Metric.mem_closedBall.mp hz.1
    rw [Metric.mem_ball]
    linarith
  have hSU : S ⊆ U := fun z hz =>
    hball (Metric.ball_subset_closedBall (hSball hz))
  -- no zero is a local identical vanishing point (else `f c = 0`)
  have hne : ∀ ρ ∈ S, ¬ (∀ᶠ z in nhds ρ, f z = 0) := by
    intro ρ hρ hev
    have hball_conn : IsPreconnected (Metric.ball c R) :=
      (convex_ball c R).isPreconnected
    have hfball : AnalyticOnNhd ℂ f (Metric.ball c R) := fun z hz =>
      hf z (hball (Metric.ball_subset_closedBall hz))
    have hzero := hfball.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hball_conn (hSball hρ) hev
    exact hfc (hzero (Metric.mem_ball_self hR))
  -- extraction with fuel one beyond the count bound, on the ambient open set
  set fuel : ℕ := ⌈M / Real.log 3⌉₊ + 1 with hfuel_def
  obtain ⟨L, g, hLS, hg, hfac, hlen, hdisj⟩ :=
    exists_prod_factor_of_zeros f hU hf S hSU hne fuel
  have hlog3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  -- refute the exactly-fuel branch by the quarter-ball count
  have hnv : ∀ ρ ∈ S, g ρ ≠ 0 := by
    rcases hdisj with hfull | hnv
    · exfalso
      have hcount := three_pow_mul_le_of_prod_factor hU hR hball hg
        (fun ρ hρ => (hLS ρ hρ).1) hfac
        (B := Real.exp M * ‖f c‖)
        (fun z hz => hratio z (Metric.sphere_subset_closedBall hz))
      rw [hfull] at hcount
      have h1 : (3:ℝ) ^ fuel ≤ Real.exp M :=
        le_of_mul_le_mul_right hcount hfc0
      have h4 : (fuel:ℝ) * Real.log 3 ≤ M := by
        have h5 := Real.log_le_log (by positivity) h1
        rw [Real.log_pow, Real.log_exp] at h5
        exact h5
      have h6 : (fuel:ℝ) ≤ M / Real.log 3 := by
        rw [le_div_iff₀ hlog3]
        exact h4
      have h7 : M / Real.log 3 ≤ (⌈M / Real.log 3⌉₊ : ℝ) := Nat.le_ceil _
      have h8 : (fuel:ℝ) = (⌈M / Real.log 3⌉₊ : ℝ) + 1 := by
        rw [hfuel_def]
        push_cast
        ring
      linarith
    · exact hnv
  -- the offending zero was extracted
  have hρ₀S : ρ₀ ∈ S := ⟨hρ₀, hfρ₀⟩
  have hρ₀L : ρ₀ ∈ L := by
    have h1 := hfac ρ₀ (hSU hρ₀S)
    rw [hfρ₀] at h1
    have h2 : (L.map (fun ρ => ρ₀ - ρ)).prod = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h (hnv ρ₀ hρ₀S)
    have h4 : (0:ℂ) ∈ L.map (fun ρ => ρ₀ - ρ) := List.prod_eq_zero_iff.mp h2
    rw [List.mem_map] at h4
    obtain ⟨ρ, hρL, hρ0⟩ := h4
    have h3 : ρ₀ = ρ := sub_eq_zero.mp hρ0
    exact h3 ▸ hρL
  -- the center avoids all roots
  have hLc : ∀ ρ ∈ L, c ≠ ρ := by
    intro ρ hρL hcρ
    exact hfc (hcρ ▸ (hLS ρ hρL).2)
  -- `g` is nonvanishing on the whole quarter-ball
  have hgq : ∀ z ∈ Metric.ball c (R/4), g z ≠ 0 := by
    intro z hz hg0
    by_cases hfz : f z = 0
    · exact hnv z ⟨Metric.ball_subset_closedBall hz, hfz⟩ hg0
    · refine hfz ?_
      rw [hfac z (hball (Metric.ball_subset_closedBall (by
          rw [Metric.mem_ball] at hz ⊢
          linarith))), hg0, mul_zero]
  -- the `g`-ratio bound on the quarter-ball, via the maximum principle at `R`
  set k : ℕ := L.length with hk_def
  have hgcl : ‖f c‖ ≤ (R/4) ^ k * ‖g c‖ := by
    rw [hfac c (hball (Metric.mem_closedBall_self hR.le)), norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine norm_list_prod_sub_le fun ρ hρ => ?_
    have h1 : dist ρ c ≤ R/4 := Metric.mem_closedBall.mp (hLS ρ hρ).1
    rw [show ‖c - ρ‖ = dist ρ c from by rw [dist_eq_norm, norm_sub_rev]]
    exact h1
  have hgball : ∀ z ∈ Metric.ball c R,
      ‖g z‖ ≤ Real.exp M * ‖f c‖ / ((3/4) * R) ^ k := by
    intro z hz
    have hbd : Bornology.IsBounded (Metric.ball c R) := Metric.isBounded_ball
    have hdiff : DiffContOnCl ℂ g (Metric.ball c R) := by
      have h1 : DifferentiableOn ℂ g (Metric.closedBall c R) := by
        intro w hw
        exact (hg w (hball hw)).differentiableAt.differentiableWithinAt
      rw [← closure_ball c hR.ne'] at h1
      exact h1.diffContOnCl
    have hfr : ∀ w ∈ frontier (Metric.ball c R),
        ‖g w‖ ≤ Real.exp M * ‖f c‖ / ((3/4) * R) ^ k := by
      rw [frontier_ball c hR.ne']
      intro w hw
      have hwU : w ∈ U := hball (Metric.sphere_subset_closedBall hw)
      have hwc : dist w c = R := Metric.mem_sphere.mp hw
      have hroots : ∀ ρ ∈ L, (3/4) * R ≤ ‖w - ρ‖ := by
        intro ρ hρ
        have h1 : dist ρ c ≤ R/4 := Metric.mem_closedBall.mp (hLS ρ hρ).1
        rw [show ‖w - ρ‖ = dist w ρ from by rw [dist_eq_norm]]
        calc (3/4) * R = R - R/4 := by ring
          _ ≤ dist w c - dist ρ c := by linarith
          _ ≤ dist w ρ := by linarith [dist_triangle w ρ c]
      have hprod : ((3/4) * R) ^ k ≤ ‖(L.map (fun ρ => w - ρ)).prod‖ :=
        le_norm_list_prod_sub (by positivity) hroots
      have hfw := hfac w hwU
      have hfB := hratio w (Metric.sphere_subset_closedBall hw)
      rw [hfw, norm_mul] at hfB
      have hpos : (0:ℝ) < ((3/4) * R) ^ k := by positivity
      rw [le_div_iff₀ hpos]
      calc ‖g w‖ * ((3/4) * R) ^ k
          ≤ ‖g w‖ * ‖(L.map (fun ρ => w - ρ)).prod‖ :=
            mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = ‖(L.map (fun ρ => w - ρ)).prod‖ * ‖g w‖ := by ring
        _ ≤ Real.exp M * ‖f c‖ := hfB
    have hcc : z ∈ closure (Metric.ball c R) := by
      rw [closure_ball c hR.ne']
      exact Metric.ball_subset_closedBall hz
    exact Complex.norm_le_of_forall_mem_frontier_norm_le hbd hdiff hfr hcc
  have hgratio : ∀ z ∈ Metric.ball c (R/4),
      ‖g z‖ ≤ Real.exp M * ‖g c‖ := by
    intro z hz
    have hz' : z ∈ Metric.ball c R := by
      rw [Metric.mem_ball] at hz ⊢
      linarith
    have h1 := hgball z hz'
    have h2 : Real.exp M * ‖f c‖ / ((3/4) * R) ^ k
        ≤ Real.exp M * ‖g c‖ := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : ((3:ℝ)/4 * R) ^ k = 3 ^ k * (R/4) ^ k := by
        rw [← mul_pow]
        congr 1
        ring
      rw [h3]
      calc Real.exp M * ‖f c‖
          ≤ Real.exp M * ((R/4) ^ k * ‖g c‖) :=
            mul_le_mul_of_nonneg_left hgcl (Real.exp_pos M).le
        _ = (Real.exp M * ‖g c‖) * ((R/4) ^ k * 1) := by ring
        _ ≤ (Real.exp M * ‖g c‖) * ((R/4) ^ k * 3 ^ k) := by
            have h4 : (1:ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
            have h5 : (0:ℝ) ≤ (R/4) ^ k := by positivity
            have h6 : (0:ℝ) ≤ Real.exp M * ‖g c‖ :=
              mul_nonneg (Real.exp_pos M).le (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h4 h5) h6
        _ = Real.exp M * ‖g c‖ * (3 ^ k * (R/4) ^ k) := by ring
    exact le_trans h1 h2
  -- the Borel–Carathéodory bound on `g'/g` at radius `R/4`
  have hR4 : (0:ℝ) < R/4 := by linarith
  have hball4 : Metric.ball c (R/4) ⊆ U := by
    intro z hz
    refine hball (Metric.ball_subset_closedBall ?_)
    rw [Metric.mem_ball] at hz ⊢
    linarith
  have hlogd := norm_logDeriv_le_of_ratio_le hU hg hR4 hball4 hgq hgratio
  have hlogd4 : ‖deriv g c / g c‖ ≤ 16 * (M + 1) / R := by
    refine le_trans hlogd ?_
    rw [show 4 * (M + 1) / (R/4) = 16 * (M + 1) / R from by field_simp; ring]
  -- assemble through the factorization logarithmic derivative
  have hgc : g c ≠ 0 := hgq c (Metric.mem_ball_self hR4)
  have hsplit := deriv_div_of_prod_factor hU hg hfac
    (hball (Metric.mem_closedBall_self hR.le)) hLc hgc
  -- split the root sum at `ρ₀` and drop the nonnegative rest
  have hperm : L.Perm (ρ₀ :: L.erase ρ₀) := List.perm_cons_erase hρ₀L
  have hsum_split : ((L.map (fun ρ => 1/(c - ρ))).sum : ℂ)
      = 1/(c - ρ₀) + ((L.erase ρ₀).map (fun ρ => 1/(c - ρ))).sum := by
    have h1 := (hperm.map (fun ρ => 1/(c - ρ))).sum_eq
    rw [h1, List.map_cons, List.sum_cons]
  have hrest : (0:ℝ) ≤ (((L.erase ρ₀).map (fun ρ => 1/(c - ρ))).sum).re := by
    rw [show (((L.erase ρ₀).map (fun ρ => 1/(c - ρ))).sum).re
        = (((L.erase ρ₀).map (fun ρ => 1/(c - ρ))).map Complex.re).sum from by
        rw [← Complex.coe_reAddGroupHom]
        exact map_list_sum Complex.reAddGroupHom _]
    refine List.sum_nonneg ?_
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [List.mem_map] at hy
    obtain ⟨ρ, hρe, hρy⟩ := hy
    have hρL : ρ ∈ L := List.mem_of_mem_erase hρe
    have hρS : ρ ∈ S := hLS ρ hρL
    have hρre : ρ.re ≤ c.re := hre ρ hρS.1 hρS.2
    have hcρ : c - ρ ≠ 0 := sub_ne_zero.mpr (hLc ρ hρL)
    rw [← hyx, ← hρy]
    rw [one_div, Complex.inv_re]
    refine div_nonneg ?_ (Complex.normSq_nonneg _)
    rw [Complex.sub_re]
    linarith
  rw [hsplit, hsum_split]
  have hgre : -(deriv g c / g c).re ≤ 16 * (M + 1) / R := by
    have h1 : -(deriv g c / g c).re ≤ ‖deriv g c / g c‖ := by
      have h2 := Complex.abs_re_le_norm (deriv g c / g c)
      have h3 := neg_abs_le (deriv g c / g c).re
      linarith
    linarith [hlogd4]
  have hfinal : -((1/(c - ρ₀) + ((L.erase ρ₀).map (fun ρ => 1/(c - ρ))).sum
      + deriv g c / g c).re)
      = -(1/(c - ρ₀)).re - (((L.erase ρ₀).map (fun ρ => 1/(c - ρ))).sum).re
        - (deriv g c / g c).re := by
    simp [Complex.add_re]
    ring
  rw [hfinal]
  linarith

end ExpSums

end MoltResearch
