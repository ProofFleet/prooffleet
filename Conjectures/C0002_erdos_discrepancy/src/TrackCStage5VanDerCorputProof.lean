import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Derivation
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Elliott
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Track C: Stage 5 — Proposition 1.11 from the nonasymptotic Elliott interface

This file discharges the derivation card's van der Corput box
(`Problems/tao2015_derivation_c.md`, issue #2870): the instance

`[LogElliottNonasymptoticAssumption] → VanDerCorputAssumption`

i.e. Proposition 1.11 of arXiv:1509.05363 (§3) from the nonasymptotic two-point Elliott
input (Theorem 1.10 there / arXiv:1509.05422, Theorem 1.3).

**Proof shape** (all substrate lemmas are in the verified nucleus, PRs #2874–#2877):
given a uniform second-moment bound `C` and `ε ∈ (0, 1]`, bump `C' = max C 1`, take the
window length `H = ⌈8C'/ε⌉₊` and Elliott strength `ε' = 1/(8H)`. Let `A` dominate the
Elliott thresholds `A₀(ε', (1,1,h,h'))` of the finitely many shift pairs `h ≠ h' ≤ H`
(and `1`), and set `W = max A (exp 2)`. For any truncation `X ≥ ⌈W⌉₊`, over the Elliott
window `s = Ioc ⌊X/W⌋₊ X`:

- the log-mass `S = ∑_{n ∈ s} 1/n` satisfies `S ≥ log W − 1 ≥ (log W)/2 ≥ 1`
  (`Mathlib.NumberTheory.Harmonic` bounds);
- Markov (`prob_sum_div_normSq_windowSumC_le`) puts the sample's log-averaged squared
  window sum below `4C'S/ε ≤ H·S/2` off an event of probability `≤ ε`;
- on the good event, the pigeonhole (`Unimodular.exists_pair_windowCorr_le`) extracts a
  shift pair with `‖windowCorr‖ ≥ S/(2H) ≥ (log W)/(4H) > ε'·log W` — violating the
  Elliott bound at `(a₁, a₂, b₁, b₂) = (1, 1, h, h')`, `g₂ = conj g`;
- so `NonPretentiousAt (g ω) A X` fails, and unpacking the negation is exactly
  membership in `pretentiousEvent G A A A X`.

The interface friction flagged on #2870 (Prop 1.11 truncates at `X : ℕ` while the Elliott
bound lands at `⌈x⌉₊` over `Ioc ⌊x/w⌋₊ ⌊x⌋₊`) dissolves by instantiating the Elliott input
at `x := (X : ℝ)`: then `⌈x⌉₊ = X` and `⌊x⌋₊ = X` on the nose — no interface amendment
needed. The probability constant is `K = 1`, independent of `ε` (the audited quantifier
order), and `Q = T = B = A`.

`theorem18_of_logElliottNonasymptotic` restates the milestone: Theorem 1.8 is now
conditional on exactly the two remaining deep inputs (nonasymptotic Elliott + §4
Borwein–Choi–Coons). Axiom footprints are pinned in `TrackCAxiomAudit.lean`.
-/

namespace MoltResearch

/-- Conjugation preserves complete multiplicativity — the small bridge the Elliott call
site needs for `g₂ = conj g₁` (promotion candidate for the nucleus). -/
theorem CompletelyMultiplicativeC.conj {g : ℕ → ℂ} (hg : CompletelyMultiplicativeC g) :
    CompletelyMultiplicativeC fun n => (starRingEnd ℂ) (g n) := fun a b ha hb => by
  simp only [hg a b ha hb, map_mul]

namespace Tao2015

open MeasureTheory

/-- **Log-mass of the Elliott window**: for `1 ≤ W ≤ X` the window `⌊X/W⌋₊ < n ≤ X`
carries harmonic mass at least `log W − 1` — the lower bound that makes the pigeonhole
payoff `S/(2H)` beat the Elliott bound `ε'·log W`. -/
theorem log_sub_one_le_sum_one_div {W : ℝ} (hW : 1 ≤ W) {X : ℕ} (hWX : W ≤ (X : ℝ)) :
    Real.log W - 1 ≤ ∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n := by
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le one_pos hW
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le hW0 hWX
  set m : ℕ := ⌊(X : ℝ) / W⌋₊ with hm
  have hdiv1 : (1 : ℝ) ≤ (X : ℝ) / W := (one_le_div hW0).mpr hWX
  have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hdiv1)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmle : (m : ℝ) ≤ (X : ℝ) / W := Nat.floor_le (by positivity)
  have hmX : m ≤ X := by
    have h1 : (m : ℝ) ≤ (X : ℝ) := hmle.trans (div_le_self hX0.le hW)
    exact_mod_cast h1
  -- the window sum is a difference of harmonic numbers
  have hIoc : ∀ k : ℕ, ∑ n ∈ Finset.Ioc 0 k, (1 : ℝ) / n = (harmonic k : ℝ) := by
    intro k
    have hset : Finset.Ioc 0 k = Finset.Icc 1 k := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hset, harmonic_eq_sum_Icc]
    push_cast
    simp [one_div]
  have hsplit := Finset.sum_Ioc_consecutive (fun n : ℕ => (1 : ℝ) / n) (Nat.zero_le m) hmX
  have hkey : ∑ n ∈ Finset.Ioc m X, (1 : ℝ) / n = (harmonic X : ℝ) - (harmonic m : ℝ) := by
    rw [← hIoc X, ← hIoc m, ← hsplit]
    ring
  rw [hkey]
  -- harmonic bounds: `log (X+1) ≤ harmonic X` and `harmonic m ≤ 1 + log m`
  have hup : (harmonic m : ℝ) ≤ 1 + Real.log m := harmonic_le_one_add_log m
  have hlo : Real.log (X + 1) ≤ (harmonic X : ℝ) := by
    have h := log_add_one_le_harmonic X
    push_cast at h ⊢
    exact h
  have hlogX : Real.log X ≤ Real.log (X + 1) := Real.log_le_log hX0 (by linarith)
  -- `log m ≤ log (X/W) = log X − log W`
  have hlogm : Real.log m ≤ Real.log X - Real.log W := by
    calc Real.log m ≤ Real.log ((X : ℝ) / W) := Real.log_le_log hm0 hmle
      _ = Real.log X - Real.log W := Real.log_div (ne_of_gt hX0) (ne_of_gt hW0)
  linarith

/-- **Proposition 1.11** (Tao 2015, arXiv:1509.05363 §3), proved from the nonasymptotic
two-point Elliott interface: bounded second moment forces, with probability `1 − ε` at
every large truncation, pretentiousness toward some character twist with controlled
period, frequency, and distance.

The probability constant is `K = 1` (independent of `ε` — the audited quantifier order),
and the constants are `Q = T = B = A` with `A` dominating the Elliott thresholds of the
finitely many shift pairs. -/
instance (priority := 90) vanDerCorputAssumption_of_logElliottNonasymptotic
    [inst : LogElliottNonasymptoticAssumption] : VanDerCorputAssumption where
  pretentious := by
    intro Ω m μ hprob G C hC
    refine ⟨1, ?_⟩
    intro ε hε0 hε1
    have hεne : ε ≠ 0 := ne_of_gt hε0
    -- constants: bump the bound to `C' ≥ 1`, window length `H ≥ 8C'/ε`, strength `ε' = 1/(8H)`
    set C' : ℝ := max C 1 with hC'def
    have hC' : ∀ n : ℕ, sndMomentPartialSum G n ≤ C' := fun n => (hC n).trans (le_max_left C 1)
    have hC'1 : (1 : ℝ) ≤ C' := le_max_right C 1
    have hC'0 : (0 : ℝ) < C' := lt_of_lt_of_le one_pos hC'1
    set H : ℕ := ⌈8 * C' / ε⌉₊ with hHdef
    have hHle : 8 * C' / ε ≤ (H : ℝ) := Nat.le_ceil _
    have hH1 : 1 ≤ H := Nat.ceil_pos.mpr (by positivity)
    have hHr0 : (0 : ℝ) < H := by exact_mod_cast hH1
    have hHne : (H : ℝ) ≠ 0 := ne_of_gt hHr0
    set ε' : ℝ := 1 / (8 * H) with hε'def
    have hε'0 : 0 < ε' := by positivity
    -- Elliott thresholds for each shift pair, totalized so `choose` applies
    have hbound : ∀ p : ℕ × ℕ, ∃ A₀ : ℝ, p.1 ≠ p.2 →
        ∀ A : ℝ, A₀ ≤ A → 1 ≤ A → ∀ x w : ℝ, A ≤ w → w ≤ x →
          ∀ g₁ g₂ : ℕ → ℂ,
            CompletelyMultiplicativeC g₁ → (∀ n, ‖g₁ n‖ ≤ 1) →
            CompletelyMultiplicativeC g₂ → (∀ n, ‖g₂ n‖ ≤ 1) →
            NonPretentiousAt g₁ A ⌈x⌉₊ →
            ‖∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
                g₁ (1 * n + p.1) * g₂ (1 * n + p.2) / (n : ℂ)‖ ≤ ε' * Real.log w := by
      intro p
      by_cases hne : p.1 = p.2
      · exact ⟨0, fun hcon => absurd hne hcon⟩
      · obtain ⟨A₀, hA₀⟩ := inst.bound 1 1 p.1 p.2 one_pos one_pos
          (by simpa using Ne.symm hne) ε' hε'0
        exact ⟨A₀, fun _ => hA₀⟩
    choose A₀f hA₀f using hbound
    -- `A` dominates every pair's threshold; `W` additionally forces `log W ≥ 2`
    have hPne : (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).Nonempty :=
      ⟨(1, 1), Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨le_rfl, hH1⟩, Finset.mem_Icc.mpr ⟨le_rfl, hH1⟩⟩⟩
    set A : ℝ := max 1 ((Finset.Icc 1 H ×ˢ Finset.Icc 1 H).sup' hPne A₀f) with hAdef
    have hA1 : (1 : ℝ) ≤ A := le_max_left _ _
    set W : ℝ := max A (Real.exp 2) with hWdef
    have hAW : A ≤ W := le_max_left _ _
    have hW1 : (1 : ℝ) ≤ W := hA1.trans hAW
    have hW0 : (0 : ℝ) < W := lt_of_lt_of_le one_pos hW1
    have hlogW : 2 ≤ Real.log W := by
      rw [Real.le_log_iff_exp_le hW0]
      exact le_max_right A _
    refine ⟨A, A, A, ⌈W⌉₊, ?_⟩
    intro X hX₀X
    have hWX : W ≤ (X : ℝ) := (Nat.le_ceil W).trans (by exact_mod_cast hX₀X)
    -- log-mass of the Elliott window at truncation `X`
    have hSlog : Real.log W - 1 ≤ ∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n :=
      log_sub_one_le_sum_one_div hW1 hWX
    have hS2 : Real.log W / 2 ≤ ∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n := by
      linarith
    have hSpos : (0 : ℝ) < ∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n := by linarith
    have hCS : 0 < C' * ∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n :=
      mul_pos hC'0 hSpos
    -- Markov event, then a.e. inclusion into the pretentious event
    have hmarkov := prob_sum_div_normSq_windowSumC_le G hC'
      (Finset.Ioc ⌊(X : ℝ) / W⌋₊ X) H hε0 hε1 hCS
    rw [one_mul]
    refine le_trans hmarkov (measure_mono_ae ?_)
    filter_upwards [G.mul_ae, G.unimodular_ae] with ω hgmul hguni hω
    -- pigeonhole: some pair carries a large windowed correlation
    have hB : 4 * C' * (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / ε
        ≤ (H : ℝ) * (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / 2 := by
      calc 4 * C' * (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / ε
          = 8 * C' / ε * ((∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / 2) := by
            field_simp
            ring
        _ ≤ (H : ℝ) * ((∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / 2) :=
            mul_le_mul_of_nonneg_right hHle (by positivity)
        _ = (H : ℝ) * (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / 2 := by ring
    obtain ⟨h, hh, h', hh', hne, hcorr⟩ :=
      hguni.exists_pair_windowCorr_le hH1 hSpos hω hB
    -- the sample and its conjugate are 1-bounded completely multiplicative
    have hb1 : ∀ n, ‖G.g ω n‖ ≤ 1 := fun n => (hguni n).le
    have hmulc : CompletelyMultiplicativeC fun n => (starRingEnd ℂ) (G.g ω n) := hgmul.conj
    have hb1c : ∀ n, ‖(starRingEnd ℂ) (G.g ω n)‖ ≤ 1 := fun n => by
      rw [RCLike.norm_conj]
      exact hb1 n
    have hA₀A : A₀f (h, h') ≤ A :=
      le_trans (Finset.le_sup' A₀f (Finset.mem_product.mpr ⟨hh, hh'⟩)) (le_max_right 1 _)
    -- the extracted correlation violates the Elliott bound, so the sample is pretentious
    have hnot : ¬ NonPretentiousAt (G.g ω) A X := by
      intro hnp
      have hnp' : NonPretentiousAt (G.g ω) A ⌈((X : ℕ) : ℝ)⌉₊ := by
        rwa [Nat.ceil_natCast]
      have hEl := hA₀f (h, h') hne A hA₀A hA1 ((X : ℕ) : ℝ) W hAW hWX
        (G.g ω) (fun n => (starRingEnd ℂ) (G.g ω n)) hgmul hb1 hmulc hb1c hnp'
      have hsum : (∑ n ∈ Finset.Ioc ⌊((X : ℕ) : ℝ) / W⌋₊ ⌊((X : ℕ) : ℝ)⌋₊,
            (G.g ω) (1 * n + h) * (starRingEnd ℂ) ((G.g ω) (1 * n + h')) / (n : ℂ))
          = windowCorr (G.g ω) (Finset.Ioc ⌊(X : ℝ) / W⌋₊ X) h h' := by
        rw [Nat.floor_natCast]
        unfold windowCorr
        exact Finset.sum_congr rfl fun n _ => by rw [one_mul]
      rw [hsum] at hEl
      have hup : (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / (2 * H)
          ≤ ε' * Real.log W := le_trans hcorr hEl
      rw [hε'def] at hup
      have h2H : (0 : ℝ) < 2 * H := by positivity
      have h1 : (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) ≤ Real.log W / 4 := by
        have h0 := (div_le_iff₀ h2H).mp hup
        calc (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n)
            ≤ 1 / (8 * H) * Real.log W * (2 * H) := h0
          _ = Real.log W / 4 := by
              field_simp
              ring
      linarith
    -- unpack the failed non-pretentiousness into the event data
    unfold NonPretentiousAt at hnot
    push_neg at hnot
    obtain ⟨q, χ, t, hq, ht, hdist⟩ := hnot
    exact ⟨q, χ, t, hq, ht, hdist.le⟩

/-- **Milestone restatement** (Theorem 1.8 under the new instance chain): with the van der
Corput leg discharged, Theorem 1.8 is conditional on exactly the two remaining deep inputs
— the nonasymptotic Elliott theorem and the §4 Borwein–Choi–Coons growth statement. -/
theorem theorem18_of_logElliottNonasymptotic
    [LogElliottNonasymptoticAssumption] [BorweinChoiCoonsAssumption]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, sndMomentPartialSum G n ≤ C :=
  theorem18 μ G

-- Consumer example (compile-only): the Prop-1.11 conclusion is now available from the
-- Elliott interface alone — no `VanDerCorputAssumption` hypothesis at the call site.
example [LogElliottNonasymptoticAssumption]
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) (hC : ∀ n : ℕ, sndMomentPartialSum G n ≤ 100) :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ Q T B : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ENNReal.ofReal (1 - K * ε) ≤ μ (pretentiousEvent G Q T B X) :=
  vanDerCorput_pretentious G hC

end Tao2015

end MoltResearch
