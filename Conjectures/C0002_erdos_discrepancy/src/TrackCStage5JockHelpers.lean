import MoltResearch.Discrepancy
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5VanDerCorput

/-!
# Track C: Stage 5 — analytic helpers for the (jock) → (contra) chain (Tao 2015 §4)

Conjectures-layer scaffolding for issue #2871 (`Problems/tao2015_derivation_c.md`): three
small deterministic tools consumed by the (jock) → (contra) assembly.

* `norm_tsum_sq_le_tsum_mul_tsum` — Cauchy–Schwarz for absolutely dominated ℂ-series.
* `tsum_indicator_class_zeta_le` — the zeta mass `∑_{n ≡ b (r)} 1/n^σ ≤ 1 + (2 + log X)/r`.
* `norm_tsum_indicator_shift_sub_le` — the `n ↦ n + m` shift costs `O(m)` in a residue-class
  zeta sum (constant `2m + 2`).

All at the zeta weight `σ = 1 + 1/log X`; constants explicit and crude.

The fourth tool of the chain — the `φ(r')`-normalized principal Euler factor being
`1 + O(log(dr')/log X)` (the "κ-calculus") — is tracked separately as issue #2907.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-! ### Cauchy–Schwarz for dominated complex series -/

/-- **Cauchy–Schwarz for absolutely dominated series**: if `‖u n‖² ≤ v n · w n` pointwise
with `v, w ≥ 0` summable, then `‖∑' u‖² ≤ (∑' v)·(∑' w)`. -/
theorem norm_tsum_sq_le_tsum_mul_tsum {u : ℕ → ℂ} {v w : ℕ → ℝ}
    (hv : ∀ n, 0 ≤ v n) (hw : ∀ n, 0 ≤ w n) (huvw : ∀ n, ‖u n‖ ^ 2 ≤ v n * w n)
    (hv' : Summable v) (hw' : Summable w) :
    ‖∑' n : ℕ, u n‖ ^ 2 ≤ (∑' n : ℕ, v n) * (∑' n : ℕ, w n) := by
  have hsqrt : ∀ n, ‖u n‖ ≤ Real.sqrt (v n) * Real.sqrt (w n) := by
    intro n
    rw [← Real.sqrt_mul (hv n)]
    calc ‖u n‖ = Real.sqrt (‖u n‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (v n * w n) := Real.sqrt_le_sqrt (huvw n)
  have hAMGM : ∀ n, Real.sqrt (v n) * Real.sqrt (w n) ≤ (v n + w n) / 2 := by
    intro n
    nlinarith [Real.sq_sqrt (hv n), Real.sq_sqrt (hw n), Real.sqrt_nonneg (v n),
      Real.sqrt_nonneg (w n), sq_nonneg (Real.sqrt (v n) - Real.sqrt (w n))]
  have hsummU : Summable (fun n => ‖u n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => (hsqrt n).trans (hAMGM n)) ((hv'.add hw').div_const 2)
  have hCSfin : ∀ F : Finset ℕ,
      ∑ n ∈ F, ‖u n‖ ≤ Real.sqrt (∑' n, v n) * Real.sqrt (∑' n, w n) := by
    intro F
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq F (fun n => Real.sqrt (v n))
      (fun n => Real.sqrt (w n))
    rw [Finset.sum_congr rfl (fun n _ => Real.sq_sqrt (hv n)),
      Finset.sum_congr rfl (fun n _ => Real.sq_sqrt (hw n))] at hcs
    have hnn : 0 ≤ ∑ n ∈ F, Real.sqrt (v n) * Real.sqrt (w n) :=
      Finset.sum_nonneg fun n _ => by positivity
    calc ∑ n ∈ F, ‖u n‖
        ≤ ∑ n ∈ F, Real.sqrt (v n) * Real.sqrt (w n) :=
          Finset.sum_le_sum fun n _ => hsqrt n
      _ = Real.sqrt ((∑ n ∈ F, Real.sqrt (v n) * Real.sqrt (w n)) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((∑ n ∈ F, v n) * (∑ n ∈ F, w n)) := Real.sqrt_le_sqrt hcs
      _ = Real.sqrt (∑ n ∈ F, v n) * Real.sqrt (∑ n ∈ F, w n) :=
          Real.sqrt_mul (Finset.sum_nonneg fun n _ => hv n) _
      _ ≤ Real.sqrt (∑' n, v n) * Real.sqrt (∑' n, w n) := by
          gcongr
          · exact hv'.sum_le_tsum F (fun n _ => hv n)
          · exact hw'.sum_le_tsum F (fun n _ => hw n)
  have hUb : ∑' n, ‖u n‖ ≤ Real.sqrt (∑' n, v n) * Real.sqrt (∑' n, w n) :=
    hsummU.tsum_le_of_sum_le hCSfin
  calc ‖∑' n : ℕ, u n‖ ^ 2
      ≤ (∑' n, ‖u n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_tsum_le_tsum_norm hsummU) 2
    _ ≤ (Real.sqrt (∑' n, v n) * Real.sqrt (∑' n, w n)) ^ 2 :=
        pow_le_pow_left₀ (tsum_nonneg fun n => norm_nonneg _) hUb 2
    _ = (∑' n, v n) * (∑' n, w n) := by
        rw [mul_pow, Real.sq_sqrt (tsum_nonneg hv), Real.sq_sqrt (tsum_nonneg hw)]

/-! ### The zeta mass of a residue class -/

private lemma one_lt_log_three_le {X : ℝ} (hX : 3 ≤ X) : 1 < Real.log X := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    _ ≤ Real.log X := Real.log_le_log (by norm_num) hX

/-- **Residue-class zeta mass** (Tao 2015 §4): the total zeta weight of a single residue
class mod `r` at `σ = 1 + 1/log X` is `≤ 1 + (2 + log X)/r` — a single small term below `r`
plus an `r`-dilated copy of the full zeta tail. -/
theorem tsum_indicator_class_zeta_le {r b : ℕ} (hr : 1 ≤ r) {X : ℝ} (hX : 3 ≤ X) :
    ∑' n : ℕ, (if n % r = b % r then (1 : ℝ) / (n : ℝ) ^ (1 + 1 / Real.log X) else 0)
      ≤ 1 + (2 + Real.log X) / r := by
  have hlog1 : 1 < Real.log X := one_lt_log_three_le hX
  set σ : ℝ := 1 + 1 / Real.log X with hσdef
  have hσ1 : 1 ≤ σ := by
    have : 0 ≤ 1 / Real.log X := by positivity
    rw [hσdef]; linarith
  have hσ0 : 0 < σ := by linarith
  have hrR0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  set b₀ : ℕ := b % r with hb₀def
  have hb₀lt : b₀ < r := Nat.mod_lt _ (by omega)
  set f : ℕ → ℝ := fun n => if n % r = b % r then (1 : ℝ) / (n : ℝ) ^ σ else 0 with hfdef
  set e : ℕ → ℕ := fun j => b₀ + j * r with hedef
  -- `e` is injective
  have hinj : Function.Injective e := by
    intro j₁ j₂ h
    have : j₁ * r = j₂ * r := by
      simp only [hedef] at h
      omega
    exact Nat.eq_of_mul_eq_mul_right (by omega) this
  -- the support of `f` lies in the range of `e`
  have hsupp : Function.support f ⊆ Set.range e := by
    intro n hn
    have hn' : f n ≠ 0 := hn
    have hcond : n % r = b % r := by
      by_contra hcon
      exact hn' (by simp only [hfdef]; rw [if_neg hcon])
    refine Set.mem_range.mpr ⟨n / r, ?_⟩
    simp only [hedef, hb₀def]
    rw [← hcond]
    conv_rhs => rw [← Nat.mod_add_div n r]
    ring
  -- `f (e j) = 1 / (b₀ + j r)^σ`
  have hfe : ∀ j, f (e j) = 1 / ((b₀ : ℝ) + j * r) ^ σ := by
    intro j
    have hmod : e j % r = b % r := by
      simp only [hedef, hb₀def]
      rw [Nat.add_mul_mod_self_right, Nat.mod_mod]
    simp only [hfdef]
    rw [if_pos hmod]
    congr 2
    simp only [hedef]
    push_cast
    ring
  -- dominating sequence
  set G : ℕ → ℝ := fun j =>
    (if j = 0 then (1 : ℝ) else 0) + (1 / (r : ℝ)) * (1 / (j : ℝ) ^ σ) with hGdef
  have hσstrict : (1 : ℝ) < σ := by
    have : (0 : ℝ) < 1 / Real.log X := by positivity
    rw [hσdef]; linarith
  have hsummZeta : Summable fun n : ℕ => 1 / (n : ℝ) ^ σ :=
    Real.summable_one_div_nat_rpow.mpr hσstrict
  have hsumm_ite : Summable (fun j : ℕ => if j = 0 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun j hj => if_neg (by simpa using hj)
  have hsummG : Summable G := by
    simp only [hGdef]
    exact hsumm_ite.add (hsummZeta.mul_left (1 / (r : ℝ)))
  -- termwise domination `f (e j) ≤ G j`
  have hdom : ∀ j, f (e j) ≤ G j := by
    intro j
    rw [hfe j]
    rcases eq_or_ne j 0 with rfl | hj0
    · have hG0 : G 0 = 1 := by
        simp [hGdef, Real.zero_rpow (ne_of_gt hσ0)]
      have hlhs : (1 : ℝ) / ((b₀ : ℝ) + ((0 : ℕ) : ℝ) * (r : ℝ)) ^ σ = 1 / (b₀ : ℝ) ^ σ := by
        norm_num
      rw [hlhs, hG0]
      rcases eq_or_ne b₀ 0 with hb0 | hb0
      · rw [hb0, Nat.cast_zero, Real.zero_rpow (ne_of_gt hσ0), div_zero]
        exact zero_le_one
      · have hb0R : (1 : ℝ) ≤ (b₀ : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hb0
        rw [div_le_one (by positivity)]
        exact Real.one_le_rpow hb0R hσ0.le
    · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
        have : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
        exact_mod_cast this
      have hjR0 : (0 : ℝ) < (j : ℝ) := by linarith
      simp only [hGdef, if_neg hj0, zero_add]
      -- `(b₀ + jr)^σ ≥ (jr)^σ = j^σ r^σ ≥ j^σ r`
      have hjr0 : (0 : ℝ) < (j : ℝ) * r := by positivity
      have hbase : (j : ℝ) * r ≤ (b₀ : ℝ) + j * r := by
        have : (0 : ℝ) ≤ (b₀ : ℝ) := by positivity
        linarith
      have h1 : ((j : ℝ) * r) ^ σ ≤ ((b₀ : ℝ) + j * r) ^ σ :=
        Real.rpow_le_rpow hjr0.le hbase hσ0.le
      have h2 : ((j : ℝ) * r) ^ σ = (j : ℝ) ^ σ * (r : ℝ) ^ σ :=
        Real.mul_rpow hjR0.le hrR0.le
      have h3 : (r : ℝ) ≤ (r : ℝ) ^ σ := by
        calc (r : ℝ) = (r : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (r : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le hr1R hσ1
      have h4 : (j : ℝ) ^ σ * (r : ℝ) ≤ (j : ℝ) ^ σ * (r : ℝ) ^ σ :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have hden : (j : ℝ) ^ σ * (r : ℝ) ≤ ((b₀ : ℝ) + j * r) ^ σ := by
        calc (j : ℝ) ^ σ * (r : ℝ) ≤ (j : ℝ) ^ σ * (r : ℝ) ^ σ := h4
          _ = ((j : ℝ) * r) ^ σ := h2.symm
          _ ≤ ((b₀ : ℝ) + j * r) ^ σ := h1
      have hjσ0 : (0 : ℝ) < (j : ℝ) ^ σ := Real.rpow_pos_of_pos hjR0 σ
      calc 1 / ((b₀ : ℝ) + j * r) ^ σ
          ≤ 1 / ((j : ℝ) ^ σ * (r : ℝ)) := by
            apply one_div_le_one_div_of_le (by positivity) hden
        _ = 1 / (r : ℝ) * (1 / (j : ℝ) ^ σ) := by
            rw [div_mul_div_comm, one_mul, mul_comm]
  -- assemble
  have hsummFe : Summable fun j => f (e j) :=
    Summable.of_nonneg_of_le (fun j => by rw [hfe j]; positivity) hdom hsummG
  calc ∑' n : ℕ, f n
      = ∑' j : ℕ, f (e j) := (hinj.tsum_eq hsupp).symm
    _ ≤ ∑' j : ℕ, G j := hsummFe.tsum_le_tsum hdom hsummG
    _ ≤ 1 + (2 + Real.log X) / r := by
        rw [hGdef]
        rw [Summable.tsum_add (summable_of_ne_finset_zero (s := {0}) fun j hj => by
              rw [if_neg (by simpa using hj)]) (hsummZeta.mul_left (1 / (r : ℝ)))]
        rw [tsum_mul_left]
        have hite : ∑' j : ℕ, (if j = 0 then (1 : ℝ) else 0) = 1 := by
          rw [tsum_eq_single 0 (fun j hj => if_neg hj)]
          rw [if_pos rfl]
        rw [hite]
        have hmass : ∑' j : ℕ, 1 / (j : ℝ) ^ σ ≤ 2 + Real.log X := by
          rw [hσdef]; exact tsum_one_div_rpow_le_two_add_log hX
        rw [div_eq_mul_one_div (2 + Real.log X) (r : ℝ), mul_comm (2 + Real.log X)]
        have : (1 / (r : ℝ)) * (∑' j : ℕ, 1 / (j : ℝ) ^ σ)
            ≤ (1 / (r : ℝ)) * (2 + Real.log X) :=
          mul_le_mul_of_nonneg_left hmass (by positivity)
        linarith

/-! ### The shift `n ↦ n + m` in a residue-class zeta sum -/

/-- `1 / (n:ℂ)^σ` is the real embedding of `1 / (n:ℝ)^σ`, for every `n` (junk at `n = 0`). -/
private lemma one_div_natCast_cpow_ofReal {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    (1 : ℂ) / (n : ℂ) ^ ((σ : ℝ) : ℂ) = ((1 / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.cast_zero, Complex.zero_cpow (by exact_mod_cast Complex.ofReal_ne_zero.mpr hσ),
      div_zero]
    rw [Nat.cast_zero, Real.zero_rpow hσ, div_zero, Complex.ofReal_zero]
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow hn0]
    norm_num

/-- A `1`-bounded numerator over `n^σ` (as a masked complex term) has norm `≤ 1/n^σ`. -/
private lemma norm_ite_div_le {h : ℕ → ℂ} (hb : ∀ n, ‖h n‖ ≤ 1) {σ : ℝ} (hσ : σ ≠ 0)
    (c : Prop) [Decidable c] (k n : ℕ) :
    ‖if c then h k / (n : ℂ) ^ ((σ : ℝ) : ℂ) else 0‖ ≤ 1 / (n : ℝ) ^ σ := by
  by_cases hc : c
  · rw [if_pos hc, norm_div]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hσ), Real.zero_rpow hσ]
    · have hnorm : ‖(n : ℂ) ^ ((σ : ℝ) : ℂ)‖ = (n : ℝ) ^ σ := by
        simpa using Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn0) ((σ : ℝ) : ℂ)
      rw [hnorm]
      gcongr
      exact hb k
  · rw [if_neg hc, norm_zero]; positivity

/-- **Shift comparison** (Tao 2015 §4, `∑_{n≡a} h(n+m)/n^σ = ∑_{n≡a+m} h(n)/n^σ + O_H(1)`):
shifting the summation variable by `m` in a residue-class zeta sum costs at most `2m + 2`. -/
theorem norm_tsum_indicator_shift_sub_le {h : ℕ → ℂ} (hb : ∀ n, ‖h n‖ ≤ 1)
    {r : ℕ} (hr : 1 ≤ r) (a m : ℕ) {X : ℝ} (hX : 3 ≤ X) :
    ‖(∑' n : ℕ, if n % r = a % r
          then h (n + m) / (n : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ) else 0)
        - natResidueZetaSum h r (a + m) (1 + 1 / Real.log X)‖
      ≤ 2 * m + 2 := by
  have hlog1 : 1 < Real.log X := one_lt_log_three_le hX
  set σ : ℝ := 1 + 1 / Real.log X with hσdef
  have hσ1 : 1 ≤ σ := by
    have : 0 ≤ 1 / Real.log X := by positivity
    rw [hσdef]; linarith
  have hσstrict : (1 : ℝ) < σ := by
    have : (0 : ℝ) < 1 / Real.log X := by positivity
    rw [hσdef]; linarith
  have hσ0 : σ ≠ 0 := by positivity
  have hσnn : (0 : ℝ) ≤ σ := by linarith
  set d : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ σ with hddef
  have hd_eq : ∀ n, d n = 1 / (n : ℝ) ^ σ := fun _ => rfl
  have hd0 : ∀ n, 0 ≤ d n := fun n => by rw [hd_eq]; positivity
  have hdmono : ∀ n, n ≠ 0 → d (n + m) ≤ d n := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [hd_eq, hd_eq]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnpos σ)
      (Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_add_right n m) hσnn)
  have hsummd : Summable d := Real.summable_one_div_nat_rpow.mpr hσstrict
  have hsummd_shift : Summable fun n => d (n + m) := (summable_nat_add_iff m).mpr hsummd
  -- rewrite `natResidueZetaSum` via the shift `Summable.sum_add_tsum_nat_add`
  set g : ℕ → ℂ := fun n => if n % r = (a + m) % r then h n / (n : ℂ) ^ ((σ : ℝ) : ℂ) else 0
    with hgdef
  have hg_norm : ∀ n, ‖g n‖ ≤ d n := by
    intro n
    rw [hd_eq]
    simp only [hgdef]
    exact norm_ite_div_le hb hσ0 _ n n
  have hsummg : Summable g :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hg_norm hsummd)
  -- `natResidueZetaSum = ∑_{i<m} g i + ∑'_n g (n+m)`
  have hNat : natResidueZetaSum h r (a + m) σ
      = (∑ i ∈ Finset.range m, g i) + ∑' n : ℕ, g (n + m) := by
    rw [natResidueZetaSum]
    exact (hsummg.sum_add_tsum_nat_add m).symm
  -- `g (n + m) = if n % r = a % r then h (n+m)/(n+m)^σ else 0`
  have hgshift : ∀ n : ℕ, g (n + m)
      = if n % r = a % r then h (n + m) / ((n + m : ℕ) : ℂ) ^ ((σ : ℝ) : ℂ) else 0 := by
    intro n
    simp only [hgdef]
    by_cases hc : n % r = a % r
    · have hcm : (n + m) % r = (a + m) % r := by
        have := Nat.ModEq.add_right m hc
        simpa [Nat.ModEq] using this
      rw [if_pos hcm, if_pos hc]
    · have hcm : ¬ (n + m) % r = (a + m) % r := by
        intro hcon
        exact hc (by simpa [Nat.ModEq] using (Nat.ModEq.add_right_cancel' m hcon))
      rw [if_neg hcm, if_neg hc]
  set A : ℕ → ℂ := fun n => if n % r = a % r
      then h (n + m) / (n : ℂ) ^ ((σ : ℝ) : ℂ) else 0 with hAdef
  set A' : ℕ → ℂ := fun n => if n % r = a % r
      then h (n + m) / ((n + m : ℕ) : ℂ) ^ ((σ : ℝ) : ℂ) else 0 with hA'def
  have hA_norm : ∀ n, ‖A n‖ ≤ d n := by
    intro n
    rw [hd_eq]
    simp only [hAdef]
    exact norm_ite_div_le hb hσ0 _ (n + m) n
  have hsummA : Summable A :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hA_norm hsummd)
  have hsummA' : Summable A' := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hsummd_shift)
    rw [hd_eq]
    simp only [hA'def]
    exact norm_ite_div_le hb hσ0 _ (n + m) (n + m)
  -- the main difference decomposition
  have hAeq : (∑' n : ℕ, A n) - natResidueZetaSum h r (a + m) σ
      = (∑' n : ℕ, (A n - A' n)) - ∑ i ∈ Finset.range m, g i := by
    have hshift_tsum : ∑' n : ℕ, g (n + m) = ∑' n : ℕ, A' n :=
      tsum_congr hgshift
    rw [hNat, hshift_tsum, Summable.tsum_sub hsummA hsummA']
    ring
  rw [hAeq]
  -- bound the two pieces
  have hbound1 : ‖∑' n : ℕ, (A n - A' n)‖ ≤ (m : ℝ) + 2 := by
    have hsummAA' : Summable fun n => A n - A' n := hsummA.sub hsummA'
    -- pointwise: ‖A n - A' n‖ ≤ (d n - d (n+m)) + 2·(if n = 0 then d m else 0)
    have habs : ∀ n : ℕ,
        |d n - d (n + m)| ≤ (d n - d (n + m)) + 2 * (if n = 0 then d m else 0) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn0
      · have hd00 : d 0 = 0 := by rw [hd_eq]; simp [Real.zero_rpow hσ0]
        have hzm : (0 : ℕ) + m = m := Nat.zero_add m
        rw [hzm, hd00, if_pos rfl, zero_sub, abs_neg, abs_of_nonneg (hd0 m)]
        linarith [hd0 m]
      · rw [if_neg hn0, mul_zero, add_zero, abs_of_nonneg (by linarith [hdmono n hn0])]
    have hpt : ∀ n : ℕ, ‖A n - A' n‖
        ≤ (d n - d (n + m)) + 2 * (if n = 0 then d m else 0) := by
      intro n
      by_cases hc : n % r = a % r
      · have hAn : A n = ((h (n + m)) : ℂ) * ((d n : ℝ) : ℂ) := by
          simp only [hAdef, if_pos hc]
          rw [div_eq_mul_one_div, one_div_natCast_cpow_ofReal hσ0, hd_eq n]
        have hA'n : A' n = ((h (n + m)) : ℂ) * ((d (n + m) : ℝ) : ℂ) := by
          simp only [hA'def, if_pos hc]
          rw [div_eq_mul_one_div, one_div_natCast_cpow_ofReal hσ0, hd_eq (n + m)]
        rw [hAn, hA'n, ← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs]
        calc ‖h (n + m)‖ * |d n - d (n + m)|
            ≤ 1 * |d n - d (n + m)| :=
              mul_le_mul_of_nonneg_right (hb _) (abs_nonneg _)
          _ = |d n - d (n + m)| := one_mul _
          _ ≤ (d n - d (n + m)) + 2 * (if n = 0 then d m else 0) := habs n
      · simp only [hAdef, hA'def, if_neg hc, sub_zero, norm_zero]
        have h1 : 0 ≤ (d n - d (n + m)) + 2 * (if n = 0 then d m else 0) := by
          have hite2 : 0 ≤ 2 * (if n = 0 then d m else 0) := by
            by_cases h0 : n = 0
            · rw [if_pos h0]; positivity
            · rw [if_neg h0, mul_zero]
          have := abs_nonneg (d n - d (n + m))
          linarith [habs n]
        linarith
    -- telescoping: `∑'_n (d n - d(n+m)) = ∑_{i<m} d i ≤ m`
    have htel : (∑' n : ℕ, (d n - d (n + m))) = ∑ i ∈ Finset.range m, d i := by
      rw [Summable.tsum_sub hsummd hsummd_shift]
      have := hsummd.sum_add_tsum_nat_add m
      linarith [this]
    have hteltsum : ∑ i ∈ Finset.range m, d i ≤ (m : ℝ) := by
      calc ∑ i ∈ Finset.range m, d i ≤ ∑ _i ∈ Finset.range m, (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [hd_eq]
            rcases eq_or_ne i 0 with rfl | hi0
            · simp only [Nat.cast_zero, Real.zero_rpow hσ0, div_zero]; norm_num
            · rw [div_le_one (by positivity)]
              exact Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi0) hσnn
        _ = (m : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hite_tsum : (∑' n : ℕ, (if n = 0 then d m else 0)) = d m := by
      rw [tsum_eq_single 0 (fun n hn => if_neg hn), if_pos rfl]
    have hdm1 : d m ≤ 1 := by
      rw [hd_eq]
      rcases eq_or_ne m 0 with rfl | hm0
      · simp only [Nat.cast_zero, Real.zero_rpow hσ0, div_zero]; norm_num
      · rw [div_le_one (by positivity)]
        exact Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0) hσnn
    calc ‖∑' n : ℕ, (A n - A' n)‖
        ≤ ∑' n : ℕ, ‖A n - A' n‖ := norm_tsum_le_tsum_norm (by
          refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpt ?_
          exact (hsummd.sub hsummd_shift).add
            ((summable_of_ne_finset_zero (s := {0}) fun n hn => by
              rw [if_neg (by simpa using hn)]).mul_left 2))
      _ ≤ ∑' n : ℕ, ((d n - d (n + m)) + 2 * (if n = 0 then d m else 0)) :=
          (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpt
            ((hsummd.sub hsummd_shift).add
              ((summable_of_ne_finset_zero (s := {0}) fun n hn => by
                rw [if_neg (by simpa using hn)]).mul_left 2))).tsum_le_tsum hpt
            ((hsummd.sub hsummd_shift).add
              ((summable_of_ne_finset_zero (s := {0}) fun n hn => by
                rw [if_neg (by simpa using hn)]).mul_left 2))
      _ = (∑' n : ℕ, (d n - d (n + m))) + 2 * (∑' n : ℕ, (if n = 0 then d m else 0)) := by
          rw [Summable.tsum_add (hsummd.sub hsummd_shift)
            ((summable_of_ne_finset_zero (s := {0}) fun n hn => by
              rw [if_neg (by simpa using hn)]).mul_left 2), tsum_mul_left]
      _ = (∑ i ∈ Finset.range m, d i) + 2 * d m := by rw [htel, hite_tsum]
      _ ≤ (m : ℝ) + 2 := by linarith
  have hbound2 : ‖∑ i ∈ Finset.range m, g i‖ ≤ (m : ℝ) := by
    calc ‖∑ i ∈ Finset.range m, g i‖ ≤ ∑ i ∈ Finset.range m, ‖g i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range m, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => (hg_norm i).trans ?_
          rw [hd_eq]
          rcases eq_or_ne i 0 with rfl | hi0
          · simp only [Nat.cast_zero, Real.zero_rpow hσ0, div_zero]; norm_num
          · rw [div_le_one (by positivity)]
            exact Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi0) hσnn
      _ = (m : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  calc ‖(∑' n : ℕ, (A n - A' n)) - ∑ i ∈ Finset.range m, g i‖
      ≤ ‖∑' n : ℕ, (A n - A' n)‖ + ‖∑ i ∈ Finset.range m, g i‖ := norm_sub_le _ _
    _ ≤ ((m : ℝ) + 2) + (m : ℝ) := add_le_add hbound1 hbound2
    _ = 2 * m + 2 := by ring

end Tao2015

end MoltResearch
