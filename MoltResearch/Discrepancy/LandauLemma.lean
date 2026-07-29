import MoltResearch.Discrepancy.ZetaBound
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives

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

end ExpSums

end MoltResearch
