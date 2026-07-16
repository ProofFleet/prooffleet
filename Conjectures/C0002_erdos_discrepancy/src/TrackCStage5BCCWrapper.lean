import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5JockChain
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5TCut
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5ZetaMarkov
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5EventMeasurability
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Derivation
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5VanDerCorputProof

/-!
# Track C, Stage 5: the Borwein–Choi–Coons wrapper (§4 closing)

Tao 2015 (arXiv:1509.05363, §4; `Problems/tao2015_derivation_c.md`, issue #2871): the
stochastic wrapper discharging `BorweinChoiCoonsAssumption` from the Vinogradov–Korobov
input alone — Elliott is *not* consumed on this branch, so the derivation's deep-input
set for the §4 box shrinks to `{VinogradovKorobovAssumption}`.

Structure (deterministic core first, probability last):

* `window_transfer` — the per-sample bridge from the zeta-weighted window bound for `g`
  (the Markov event, eq. (jock) input) to the `χ̃·h`-window bound the chain consumes,
  via the δ-parametric archimedean transfer `sum_div_normSq_window_twisted_le_add`
  at a small frequency `|t| ≤ T''·X^δ`; total cost `3·log X` once
  `4H² ≤ log X`, `8δH² ≤ 1`, `72H³T'' ≤ X^δ`.
* `exists_refuting_threshold` — per primitive pair `(q₁, χ₁)`: the chain
  (`contra_of_pretentious_window`) composed with the endgame extractor
  (`exists_H_k_refuting_contra`) at `E = 6·exp(2(20+B₂))·D + 1` yields an `H` and a
  threshold past which no sample with the two chain inputs can exist.

The remaining sections (the `q = 0` pretender kill, the finite character sweep, the
two-scale t-cut, and the probability glue assembling the instance) follow below.
-/

namespace MoltResearch

namespace Tao2015

open MeasureTheory

open scoped ENNReal

/-- **Window transfer** (Tao 2015 §4, removing `n^{i𝐭}` from eq. (jock)): a zeta-weighted
window bound for the sample `g` transfers to the `χ̃·h`-windows at an additive cost of
`3·log X`, provided the frequency obeys `|t| ≤ T''·X^δ` and `H`, `δ`, `X` respect the
hierarchy `4H² ≤ log X`, `8δH² ≤ 1`, `72H³T'' ≤ X^δ`. -/
private lemma window_transfer {g : ℕ → ℂ} (hcm : CompletelyMultiplicativeC g)
    (hu : Unimodular g) {q₁ : ℕ} (χ₁ : DirichletCharacter ℂ q₁) {t : ℝ}
    {X T'' δ : ℝ} (hX : 3 ≤ X) (hT'' : 1 ≤ T'') (hδ0 : 0 < δ)
    (ht : |t| ≤ T'' * X ^ δ) {H : ℕ} (hH : 1 ≤ H)
    (hlogH : 4 * (H : ℝ) ^ 2 ≤ Real.log X)
    (hδH : 8 * δ * (H : ℝ) ^ 2 ≤ 1)
    (hXδ : 72 * (H : ℝ) ^ 3 * T'' ≤ X ^ δ)
    {Cg : ℝ}
    (hg : (1 / (H : ℝ)) * ∑ H' ∈ Finset.Ioc H (2 * H), ∑' n : ℕ,
        ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ Cg) :
    (1 / (H : ℝ)) * ∑ H' ∈ Finset.Ioc H (2 * H), ∑' n : ℕ,
        ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q₁ χ₁ t (n + m)
            * hPart g q₁ χ₁ t (n + m)‖ ^ 2
          / (n : ℝ) ^ (1 + 1 / Real.log X)
      ≤ Cg + 3 * Real.log X := by
  have hH0 : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hHR1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hlog1 : (1 : ℝ) ≤ Real.log X := by nlinarith
  have hT''0 : (0 : ℝ) < T'' := lt_of_lt_of_le one_pos hT''
  have hXδ0 : (0 : ℝ) < X ^ δ := Real.rpow_pos_of_pos (by linarith) δ
  -- per-window transfer with the cost folded into `3·log X`
  have hper : ∀ H' ∈ Finset.Ioc H (2 * H),
      ∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q₁ χ₁ t (n + m)
          * hPart g q₁ χ₁ t (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
        ≤ (∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2
            / (n : ℝ) ^ (1 + 1 / Real.log X)) + 3 * Real.log X := by
    intro H' hH'
    rw [Finset.mem_Ioc] at hH'
    have hH'1 : 1 ≤ H' := by omega
    have hfac : ∀ n : ℕ, n ≠ 0 →
        g n = (chiTilde g q₁ χ₁ t n * hPart g q₁ χ₁ t n)
          * (n : ℂ) ^ (Complex.I * (t : ℂ)) := by
      intro n hn
      rw [← chiTilde_mul_cpow_mul_hPart hcm hu hn]
      ring
    have hwb : ∀ n : ℕ, ‖chiTilde g q₁ χ₁ t n * hPart g q₁ χ₁ t n‖ ≤ 1 := fun n => by
      rw [norm_mul, chiTilde_unimodular hu, hPart_unimodular hu, mul_one]
    have hp5 := sum_div_normSq_window_twisted_le_add (g := g)
      (w := fun u => chiTilde g q₁ χ₁ t u * hPart g q₁ χ₁ t u)
      hfac hwb hX hT'' hδ0 ht hH'1
    have hH'2 : ((H' : ℝ)) ≤ 2 * (H : ℝ) := by exact_mod_cast hH'.2
    have hH'0 : (0 : ℝ) ≤ (H' : ℝ) := Nat.cast_nonneg _
    have h2 : ((H' : ℝ)) ^ 2 ≤ 4 * (H : ℝ) ^ 2 := by nlinarith
    have h3 : ((H' : ℝ)) ^ 3 ≤ 8 * (H : ℝ) ^ 3 := by nlinarith
    -- the archimedean cost is at most `2·log X`, the tail cost at most `log X`
    have hterm1 : ((H' : ℝ)) ^ 2 * (1 + 2 * δ * Real.log X) ≤ 2 * Real.log X := by
      have hδ' : (0 : ℝ) ≤ 2 * δ * Real.log X := by positivity
      have hstep : ((H' : ℝ)) ^ 2 * (1 + 2 * δ * Real.log X)
          ≤ 4 * (H : ℝ) ^ 2 * (1 + 2 * δ * Real.log X) :=
        mul_le_mul_of_nonneg_right h2 (by linarith)
      have hexpand : 4 * (H : ℝ) ^ 2 * (1 + 2 * δ * Real.log X)
          = 4 * (H : ℝ) ^ 2 + (8 * δ * (H : ℝ) ^ 2) * Real.log X := by ring
      have hsecond : (8 * δ * (H : ℝ) ^ 2) * Real.log X ≤ 1 * Real.log X :=
        mul_le_mul_of_nonneg_right hδH (by linarith)
      linarith
    have hterm2 : 3 * ((H' : ℝ)) ^ 3 * T'' * (2 + Real.log X) / (X ^ δ)
        ≤ Real.log X := by
      rw [div_le_iff₀ hXδ0]
      have hstep : 3 * ((H' : ℝ)) ^ 3 * T'' * (2 + Real.log X)
          ≤ 24 * (H : ℝ) ^ 3 * T'' * (3 * Real.log X) := by
        have h23 : 2 + Real.log X ≤ 3 * Real.log X := by linarith
        have hHT : 3 * ((H' : ℝ)) ^ 3 * T'' ≤ 24 * (H : ℝ) ^ 3 * T'' := by
          nlinarith
        have hpos1 : (0 : ℝ) ≤ 3 * ((H' : ℝ)) ^ 3 * T'' := by positivity
        have hpos2 : (0 : ℝ) ≤ 2 + Real.log X := by linarith
        calc 3 * ((H' : ℝ)) ^ 3 * T'' * (2 + Real.log X)
            ≤ 24 * (H : ℝ) ^ 3 * T'' * (2 + Real.log X) :=
              mul_le_mul_of_nonneg_right hHT hpos2
          _ ≤ 24 * (H : ℝ) ^ 3 * T'' * (3 * Real.log X) :=
              mul_le_mul_of_nonneg_left h23 (by positivity)
      have hfinal : 24 * (H : ℝ) ^ 3 * T'' * (3 * Real.log X)
          = (72 * (H : ℝ) ^ 3 * T'') * Real.log X := by ring
      have hlast : (72 * (H : ℝ) ^ 3 * T'') * Real.log X ≤ X ^ δ * Real.log X :=
        mul_le_mul_of_nonneg_right hXδ (by linarith)
      calc 3 * ((H' : ℝ)) ^ 3 * T'' * (2 + Real.log X)
          ≤ 24 * (H : ℝ) ^ 3 * T'' * (3 * Real.log X) := hstep
        _ = (72 * (H : ℝ) ^ 3 * T'') * Real.log X := hfinal
        _ ≤ X ^ δ * Real.log X := hlast
        _ = Real.log X * X ^ δ := by ring
    calc ∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q₁ χ₁ t (n + m)
            * hPart g q₁ χ₁ t (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
        ≤ (∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2
              / (n : ℝ) ^ (1 + 1 / Real.log X))
            + ((H' : ℝ)) ^ 2 * (1 + 2 * δ * Real.log X)
            + 3 * ((H' : ℝ)) ^ 3 * T'' * (2 + Real.log X) / (X ^ δ) := hp5
      _ ≤ (∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2
              / (n : ℝ) ^ (1 + 1 / Real.log X)) + 3 * Real.log X := by
          linarith
  -- average over `H' ∈ (H, 2H]`
  have hsum : ∑ H' ∈ Finset.Ioc H (2 * H), ∑' n : ℕ,
      ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q₁ χ₁ t (n + m)
          * hPart g q₁ χ₁ t (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
        ≤ (∑ H' ∈ Finset.Ioc H (2 * H), ∑' n : ℕ,
            ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X))
          + (H : ℝ) * (3 * Real.log X) := by
    calc ∑ H' ∈ Finset.Ioc H (2 * H), ∑' n : ℕ,
        ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q₁ χ₁ t (n + m)
            * hPart g q₁ χ₁ t (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
        ≤ ∑ H' ∈ Finset.Ioc H (2 * H),
            ((∑' n : ℕ, ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2
                / (n : ℝ) ^ (1 + 1 / Real.log X)) + 3 * Real.log X) :=
          Finset.sum_le_sum hper
      _ = (∑ H' ∈ Finset.Ioc H (2 * H), ∑' n : ℕ,
            ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X))
          + ((Finset.Ioc H (2 * H)).card : ℝ) * (3 * Real.log X) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      _ = _ := by
          have hcard : (Finset.Ioc H (2 * H)).card = H := by
            rw [Nat.card_Ioc]
            omega
          rw [hcard]
  have hmul := mul_le_mul_of_nonneg_left hsum
    (by positivity : (0 : ℝ) ≤ 1 / (H : ℝ))
  have hsplit : (1 / (H : ℝ))
      * ((∑ H' ∈ Finset.Ioc H (2 * H), ∑' n : ℕ,
          ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X))
        + (H : ℝ) * (3 * Real.log X))
      = (1 / (H : ℝ)) * (∑ H' ∈ Finset.Ioc H (2 * H), ∑' n : ℕ,
          ‖∑ m ∈ Finset.Icc 1 H', g (n + m)‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X))
        + 3 * Real.log X := by
    field_simp
  rw [hsplit] at hmul
  linarith

/-- **No pretender at modulus `0`** (interface hygiene): a modulus-`0` character vanishes
at every prime (`p` is not a unit of `ZMod 0 = ℤ`), so the pretentious distance to such a
twist is the full divergent Mertens sum; past an explicit scale no sample is within
distance `B`. -/
private lemma exists_scale_no_zero_modulus_pretender (B : ℝ) :
    ∃ X₂ : ℕ, ∀ X : ℕ, X₂ ≤ X →
      ∀ (g : ℕ → ℂ) (χ : DirichletCharacter ℂ 0) (t : ℝ),
        ¬ (pretentiousDistSq g (charTwist 0 χ t) X ≤ B) := by
  classical
  -- the distance is exactly the Mertens partial sum
  have hval : ∀ (g : ℕ → ℂ) (χ : DirichletCharacter ℂ 0) (t : ℝ) (X : ℕ),
      pretentiousDistSq g (charTwist 0 χ t) X
        = ∑ p ∈ X.primesBelow, 1 / (p : ℝ) := by
    intro g χ t X
    unfold pretentiousDistSq
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have hnu : ¬ IsUnit ((p : ℕ) : ZMod 0) := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_zero_right]
      exact hpp.ne_one
    have hzero : charTwist 0 χ t p = 0 := by
      unfold charTwist
      rw [χ.map_nonunit hnu, zero_mul]
    rw [hzero, map_zero, mul_zero, Complex.zero_re, sub_zero]
  -- the Mertens partial sums tend to infinity
  have hdiv : Filter.Tendsto
      (fun X : ℕ => ∑ i ∈ Finset.range X,
        Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i)
      Filter.atTop Filter.atTop := by
    rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
    · exact not_summable_one_div_on_primes
    · intro n
      rw [Set.indicator_apply]
      split
      · positivity
      · exact le_refl 0
  have hind : ∀ X : ℕ, ∑ i ∈ Finset.range X,
      Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i
        = ∑ p ∈ X.primesBelow, 1 / (p : ℝ) := by
    intro X
    unfold Nat.primesBelow
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  obtain ⟨X₂, hX₂⟩ := Filter.eventually_atTop.mp (hdiv.eventually_gt_atTop B)
  refine ⟨X₂, fun X hX g χ t hcon => ?_⟩
  have hgt := hX₂ X hX
  rw [hind X] at hgt
  rw [hval g χ t X] at hcon
  linarith

/-- Crude but uniform: the number of distinct prime factors is at most the number
itself. -/
private lemma card_primeFactors_le_self (q : ℕ) : q.primeFactors.card ≤ q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have hsub : q.primeFactors ⊆ Finset.Icc 1 q := fun p hp => by
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hdvd := Nat.dvd_of_mem_primeFactors hp
      rw [Finset.mem_Icc]
      exact ⟨hpp.one_lt.le, Nat.le_of_dvd hq hdvd⟩
    have hcard := Finset.card_le_card hsub
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at hcard

/-- Threshold constructor: past an explicit scale, `log X` beats any constant. -/
private lemma exists_nat_forall_log_ge (A : ℝ) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → A ≤ Real.log X := by
  refine ⟨max 1 ⌈Real.exp A⌉₊, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXA : Real.exp A ≤ (X : ℝ) := by
    calc Real.exp A ≤ (⌈Real.exp A⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (X : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hX
  calc A = Real.log (Real.exp A) := (Real.log_exp A).symm
    _ ≤ Real.log X := Real.log_le_log (Real.exp_pos A) hXA

/-- Threshold constructor: past an explicit scale, `X^δ` beats any constant. -/
private lemma exists_nat_forall_rpow_ge (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → A ≤ (X : ℝ) ^ δ := by
  refine ⟨⌈(max A 1) ^ (1 / δ)⌉₊, fun X hX => ?_⟩
  have hB1 : (1 : ℝ) ≤ max A 1 := le_max_right _ _
  have hB0 : (0 : ℝ) ≤ max A 1 := by linarith
  have hXB : (max A 1) ^ (1 / δ) ≤ (X : ℝ) := by
    calc (max A 1) ^ (1 / δ) ≤ (⌈(max A 1) ^ (1 / δ)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (X : ℝ) := by exact_mod_cast hX
  have hrw : ((max A 1) ^ (1 / δ)) ^ δ = max A 1 := by
    rw [← Real.rpow_mul hB0, one_div_mul_cancel hδ.ne', Real.rpow_one]
  calc A ≤ max A 1 := le_max_left _ _
    _ = ((max A 1) ^ (1 / δ)) ^ δ := hrw.symm
    _ ≤ (X : ℝ) ^ δ := Real.rpow_le_rpow (Real.rpow_nonneg hB0 _) hXB hδ.le

/-- **Per-pair refutation threshold** (Tao 2015 §4): for a primitive pair `(q₁, χ₁)` and
chain constants `B₂, D`, the (jock)→(contra) chain composed with the endgame extractor
at `E = 6·exp(2(20+B₂))·D + 1` produces an `H` and a threshold `X₁` past which **no**
completely multiplicative unimodular sample can satisfy both chain inputs. -/
private lemma exists_refuting_threshold {q₁ : ℕ} (hq₁ : 1 ≤ q₁)
    {χ₁ : DirichletCharacter ℂ q₁} (hχ₁ : χ₁.IsPrimitive)
    (B₂ D : ℝ) (hB₂ : 0 ≤ B₂) (hD : 0 ≤ D) :
    ∃ H X₁ : ℕ, 1 ≤ H ∧
      ∀ X : ℕ, X₁ ≤ X →
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g → ∀ t : ℝ,
        pretentiousDistSq (hPart g q₁ χ₁ t) (fun _ => 1) (X + 1) ≤ B₂ →
        ((1 : ℝ) / H) * ∑ H' ∈ Finset.Ioc H (2 * H), ∑' n : ℕ,
            ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q₁ χ₁ t (n + m)
                * hPart g q₁ χ₁ t (n + m)‖ ^ 2
              / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ D * Real.log X →
        False := by
  have hE0 : (0 : ℝ) ≤ 6 * Real.exp (2 * (20 + B₂)) * D + 1 := by positivity
  obtain ⟨H, k, hH1, hk1, href⟩ := exists_H_k_refuting_contra hq₁ hχ₁ hE0
  obtain ⟨X₁, hchain⟩ := contra_of_pretentious_window q₁ k H hq₁ hk1 hH1 D B₂ hD hB₂
  exact ⟨H, X₁, hH1, fun X hX g hcm hu t hpret hwin =>
    href g t hu (hchain X hX g hcm hu χ₁ t hpret hwin)⟩

set_option maxHeartbeats 3200000 in
/-- **The Borwein–Choi–Coons theorem, stochastic form** (Tao 2015, §4), from the
Vinogradov–Korobov input alone: a stochastic completely multiplicative unimodular
function with uniformly bounded second moment cannot be persistently pretentious.

This discharges `BorweinChoiCoonsAssumption` — the last §4 obligation — so
`theorem18`'s deep-input set becomes `{LogElliottNonasymptotic (via vdC), VK, Fourier-§2}`
with the §4 box needing only VK. -/
instance (priority := 100) [VinogradovKorobovAssumption] :
    BorweinChoiCoonsAssumption := by
  refine ⟨?_⟩
  intro Ω m μ hprob G C hC K hK
  classical
  -- the defeating `ε`: probability failure per pretentious event at most `1/4`
  refine ⟨min 1 (1 / (4 * K)), by positivity, min_le_left _ _, ?_⟩
  intro Q T B X₀ hpack
  set ε : ℝ := min 1 (1 / (4 * K)) with hεdef
  have hε0 : 0 < ε := by positivity
  have hKε : K * ε ≤ 1 / 4 := by
    have h1 : ε ≤ 1 / (4 * K) := min_le_right _ _
    have h2 : K * ε ≤ K * (1 / (4 * K)) := mul_le_mul_of_nonneg_left h1 hK.le
    have h3 : K * (1 / (4 * K)) = 1 / 4 := by field_simp
    linarith
  have hKε0 : 0 ≤ K * ε := by positivity
  -- sanitized package constants
  set Tm : ℝ := max T 1 with hTmdef
  have hTm1 : (1 : ℝ) ≤ Tm := le_max_right _ _
  set Bm : ℝ := max B 0 with hBmdef
  have hBm0 : (0 : ℝ) ≤ Bm := le_max_right _ _
  set Qn : ℕ := ⌊Q⌋₊ with hQndef
  set C' : ℝ := max C 1 with hC'def
  have hC'0 : (0 : ℝ) < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC'ub : ∀ n : ℕ, sndMomentPartialSum G n ≤ C' := fun n =>
    le_trans (hC n) (le_max_left _ _)
  -- character-count data
  set nch : ℕ → ℕ := fun q =>
    if hq : 1 ≤ q then
      haveI : NeZero q := ⟨by omega⟩
      Fintype.card (DirichletCharacter ℂ q)
    else 0 with hnchdef
  set nmax : ℕ := (Finset.Icc 1 Qn).sup nch with hnmaxdef
  -- Markov budget and window constant, fixed before any pair is chosen
  set εM : ℝ := 1 / (4 * ((Qn : ℝ) + 1) * ((nmax : ℝ) + 1)) with hεMdef
  have hεM0 : 0 < εM := by positivity
  have hεM1 : εM ≤ 1 := by
    rw [hεMdef]
    rw [div_le_one (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) Qn, Nat.cast_nonneg (α := ℝ) nmax]
  set D : ℝ := 48 * C' * ((Qn : ℝ) + 1) * ((nmax : ℝ) + 1) + 3 with hDdef
  have hD0 : (0 : ℝ) ≤ D := by positivity
  set B₂ : ℝ := Bm + 2 * (Qn : ℝ) with hB₂def
  have hB₂0 : (0 : ℝ) ≤ B₂ := by positivity
  -- Skolemize the per-pair refutation data
  have href : ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q, ∃ HX : ℕ × ℕ, 1 ≤ HX.1 ∧
      (1 ≤ q → ∀ X : ℕ, HX.2 ≤ X →
        ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g → ∀ t : ℝ,
        pretentiousDistSq (hPart g χ.conductor χ.primitiveCharacter t)
            (fun _ => 1) (X + 1) ≤ B₂ →
        ((1 : ℝ) / HX.1) * ∑ H' ∈ Finset.Ioc HX.1 (2 * HX.1), ∑' n : ℕ,
            ‖∑ m ∈ Finset.Icc 1 H',
                chiTilde g χ.conductor χ.primitiveCharacter t (n + m)
                * hPart g χ.conductor χ.primitiveCharacter t (n + m)‖ ^ 2
              / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ D * Real.log X →
        False) := by
    intro q χ
    by_cases hq : 1 ≤ q
    · haveI : NeZero q := ⟨by omega⟩
      have hq₁ : 1 ≤ χ.conductor :=
        Nat.one_le_iff_ne_zero.mpr
          (ne_zero_of_dvd_ne_zero (NeZero.ne q) χ.conductor_dvd_level)
      obtain ⟨H, X₁, hH1, h⟩ := exists_refuting_threshold hq₁
        χ.primitiveCharacter_isPrimitive B₂ D hB₂0 hD0
      exact ⟨(H, X₁), hH1, fun _ => h⟩
    · exact ⟨(1, 0), le_refl 1, fun h => absurd h hq⟩
  choose FHX hFH1 hFref using href
  -- uniform bounds over the finitely many pairs
  set Hmax : ℕ := max 1 ((Finset.Icc 1 Qn).sup fun q =>
    if hq : 1 ≤ q then
      haveI : NeZero q := ⟨by omega⟩
      (Finset.univ : Finset (DirichletCharacter ℂ q)).sup fun χ => (FHX q χ).1
    else 0) with hHmaxdef
  set Xmax : ℕ := (Finset.Icc 1 Qn).sup fun q =>
    if hq : 1 ≤ q then
      haveI : NeZero q := ⟨by omega⟩
      (Finset.univ : Finset (DirichletCharacter ℂ q)).sup fun χ => (FHX q χ).2
    else 0 with hXmaxdef
  have hHmax1 : 1 ≤ Hmax := le_max_left _ _
  have hHpair : ∀ q : ℕ, 1 ≤ q → q ≤ Qn → ∀ χ : DirichletCharacter ℂ q,
      (FHX q χ).1 ≤ Hmax ∧ (FHX q χ).2 ≤ Xmax := by
    intro q hq1 hqQ χ
    haveI : NeZero q := ⟨by omega⟩
    have hmem : q ∈ Finset.Icc 1 Qn := Finset.mem_Icc.mpr ⟨hq1, hqQ⟩
    constructor
    · refine le_trans ?_ (le_max_right 1 _)
      refine le_trans ?_ (Finset.le_sup hmem)
      rw [dif_pos hq1]
      exact Finset.le_sup (f := fun χ => (FHX q χ).1) (Finset.mem_univ χ)
    · refine le_trans ?_ (Finset.le_sup hmem)
      rw [dif_pos hq1]
      exact Finset.le_sup (f := fun χ => (FHX q χ).2) (Finset.mem_univ χ)
  -- the uniform small frequency exponent
  set δ : ℝ := min (1 / 2) (1 / (8 * ((Hmax : ℝ) + 1) ^ 3)) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  -- Vinogradov–Korobov t-cut threshold
  obtain ⟨XF2, hF2⟩ := tcut_of_vinogradovKorobov (max Q 1) (2 * Tm) Bm
    (le_max_right _ _) (by linarith) hBm0 hδ0 hδ1
  -- the `q = 0` pretender kill
  obtain ⟨XW1, hW1⟩ := exists_scale_no_zero_modulus_pretender Bm
  -- log/rpow thresholds
  obtain ⟨N1, hN1⟩ := exists_nat_forall_log_ge 1
  obtain ⟨N2, hN2⟩ := exists_nat_forall_log_ge (4 * ((Hmax : ℝ) + 1) ^ 2)
  obtain ⟨N3, hN3⟩ := exists_nat_forall_rpow_ge
    (72 * ((Hmax : ℝ) + 1) ^ 3 * (Tm + 1)) hδ0
  obtain ⟨N4, hN4⟩ := exists_nat_forall_rpow_ge ((X₀ : ℝ) + 1) hδ0
  obtain ⟨N5, hN5⟩ := exists_nat_forall_rpow_ge ((XW1 : ℝ) + 1) hδ0
  -- the working scale
  set X : ℕ := max (max (max (max X₀ Xmax) (max XW1 N1)) (max (max N2 N3) (max N4 N5)))
    (max 3 ⌈XF2⌉₊) with hXdef
  -- threshold consequences
  have hXX₀ : X₀ ≤ X := by omega
  have hX3 : 3 ≤ X := by omega
  have hXr1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast by omega
  have hXr3 : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX3
  have hlog1 : (1 : ℝ) ≤ Real.log X := hN1 X (by omega)
  have hlogH : 4 * ((Hmax : ℝ) + 1) ^ 2 ≤ Real.log X := hN2 X (by omega)
  have hXδ3 : 72 * ((Hmax : ℝ) + 1) ^ 3 * (Tm + 1) ≤ (X : ℝ) ^ δ := hN3 X (by omega)
  have hXδ4 : ((X₀ : ℝ) + 1) ≤ (X : ℝ) ^ δ := hN4 X (by omega)
  have hXδ5 : ((XW1 : ℝ) + 1) ≤ (X : ℝ) ^ δ := hN5 X (by omega)
  have hXF2le : XF2 ≤ (X : ℝ) := by
    have h1 : ⌈XF2⌉₊ ≤ X := by omega
    calc XF2 ≤ (⌈XF2⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (X : ℝ) := by exact_mod_cast h1
  have hXδnn : (0 : ℝ) ≤ (X : ℝ) ^ δ := Real.rpow_nonneg (by linarith) δ
  have hXδleX : (X : ℝ) ^ δ ≤ (X : ℝ) := by
    calc (X : ℝ) ^ δ ≤ (X : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXr1 hδ1.le
      _ = (X : ℝ) := Real.rpow_one _
  have hfloorX₀ : X₀ ≤ ⌊(X : ℝ) ^ δ⌋₊ :=
    Nat.le_floor (by push_cast; linarith)
  have hfloorW1 : XW1 ≤ ⌊(X : ℝ) ^ δ⌋₊ :=
    Nat.le_floor (by push_cast; linarith)
  have hfloorle : ⌊(X : ℝ) ^ δ⌋₊ ≤ X + 1 := by
    have h1 : ⌊(X : ℝ) ^ δ⌋₊ ≤ ⌊(X : ℝ)⌋₊ := Nat.floor_le_floor hXδleX
    rw [Nat.floor_natCast] at h1
    omega
  -- the two pretentious events and the almost-sure regularity sets
  have hp1 : ENNReal.ofReal (1 - K * ε) ≤ μ (pretentiousEvent G Q T B (X + 1)) :=
    hpack (X + 1) (by omega)
  have hp2 : ENNReal.ofReal (1 - K * ε)
      ≤ μ (pretentiousEvent G Q T B ⌊(X : ℝ) ^ δ⌋₊) :=
    hpack _ hfloorX₀
  have hcompl : ∀ Y : ℕ, ENNReal.ofReal (1 - K * ε) ≤ μ (pretentiousEvent G Q T B Y) →
      μ (pretentiousEvent G Q T B Y)ᶜ ≤ ENNReal.ofReal (K * ε) := by
    intro Y hY
    have hm := measurableSet_pretentiousEvent G Q T B Y
    rw [measure_compl hm (measure_ne_top μ _), measure_univ]
    calc (1 : ℝ≥0∞) - μ (pretentiousEvent G Q T B Y)
        ≤ 1 - ENNReal.ofReal (1 - K * ε) := tsub_le_tsub_left hY 1
      _ = ENNReal.ofReal (K * ε) := by
          rw [← ENNReal.ofReal_one,
            ← ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ 1 - K * ε)]
          congr 1
          ring
  set A : Set Ω := pretentiousEvent G Q T B (X + 1)
      ∩ pretentiousEvent G Q T B ⌊(X : ℝ) ^ δ⌋₊
      ∩ {ω | CompletelyMultiplicativeC (G.g ω)}
      ∩ {ω | Unimodular (G.g ω)} with hAdef
  have hA2 : ENNReal.ofReal (1 / 2) ≤ μ A := by
    have hAc : μ Aᶜ ≤ ENNReal.ofReal (1 / 2) := by
      rw [hAdef]
      rw [Set.compl_inter, Set.compl_inter, Set.compl_inter]
      have hMc : μ {ω | CompletelyMultiplicativeC (G.g ω)}ᶜ = 0 := by
        rw [Set.compl_setOf]
        exact MeasureTheory.ae_iff.mp G.mul_ae
      have hUc : μ {ω | Unimodular (G.g ω)}ᶜ = 0 := by
        rw [Set.compl_setOf]
        exact MeasureTheory.ae_iff.mp G.unimodular_ae
      calc μ ((pretentiousEvent G Q T B (X + 1))ᶜ
            ∪ (pretentiousEvent G Q T B ⌊(X : ℝ) ^ δ⌋₊)ᶜ
            ∪ {ω | CompletelyMultiplicativeC (G.g ω)}ᶜ
            ∪ {ω | Unimodular (G.g ω)}ᶜ)
          ≤ μ ((pretentiousEvent G Q T B (X + 1))ᶜ
              ∪ (pretentiousEvent G Q T B ⌊(X : ℝ) ^ δ⌋₊)ᶜ
              ∪ {ω | CompletelyMultiplicativeC (G.g ω)}ᶜ)
            + μ {ω | Unimodular (G.g ω)}ᶜ := measure_union_le _ _
        _ ≤ (μ ((pretentiousEvent G Q T B (X + 1))ᶜ
              ∪ (pretentiousEvent G Q T B ⌊(X : ℝ) ^ δ⌋₊)ᶜ)
            + μ {ω | CompletelyMultiplicativeC (G.g ω)}ᶜ)
            + μ {ω | Unimodular (G.g ω)}ᶜ :=
            add_le_add (measure_union_le _ _) le_rfl
        _ ≤ ((μ (pretentiousEvent G Q T B (X + 1))ᶜ
              + μ (pretentiousEvent G Q T B ⌊(X : ℝ) ^ δ⌋₊)ᶜ)
            + μ {ω | CompletelyMultiplicativeC (G.g ω)}ᶜ)
            + μ {ω | Unimodular (G.g ω)}ᶜ :=
            add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
        _ ≤ ((ENNReal.ofReal (K * ε) + ENNReal.ofReal (K * ε)) + 0) + 0 := by
            refine add_le_add (add_le_add (add_le_add ?_ ?_) hMc.le) hUc.le
            · exact hcompl _ hp1
            · exact hcompl _ hp2
        _ = ENNReal.ofReal (K * ε) + ENNReal.ofReal (K * ε) := by
            rw [add_zero, add_zero]
        _ ≤ ENNReal.ofReal (1 / 2) := by
            rw [← ENNReal.ofReal_add hKε0 hKε0]
            exact ENNReal.ofReal_le_ofReal (by linarith)
    have hunion : (1 : ℝ≥0∞) ≤ μ A + μ Aᶜ := by
      calc (1 : ℝ≥0∞) = μ Set.univ := measure_univ.symm
        _ = μ (A ∪ Aᶜ) := by rw [Set.union_compl_self]
        _ ≤ μ A + μ Aᶜ := measure_union_le _ _
    have h1 : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 2) ≤ μ A := by
      rw [tsub_le_iff_right]
      exact le_trans hunion (add_le_add le_rfl hAc)
    have heq2 : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 2) = ENNReal.ofReal (1 / 2) := by
      rw [← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
    rwa [heq2] at h1
  -- cover `A` by the finitely many admissible moduli and select a heavy one
  set Aq : ℕ → Set Ω := fun q => {ω | ∃ χ : DirichletCharacter ℂ q, ∃ t : ℝ,
    |t| ≤ Tm * ((X : ℝ) + 1)
      ∧ pretentiousDistSq (G.g ω) (charTwist q χ t) (X + 1) ≤ Bm} with hAqdef
  have hcover : A ⊆ ⋃ q ∈ Finset.Icc 1 Qn, Aq q := by
    intro ω hω
    obtain ⟨q, χ, t, hqQ, ht, hd⟩ := hω.1.1.1
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with rfl | h
      · exact absurd (le_trans hd (le_max_left B 0))
          (hW1 (X + 1) (by omega) (G.g ω) χ t)
      · exact h
    have hqQn : q ≤ Qn := by
      rcases le_total 0 Q with hQ0 | hQ0
      · exact Nat.le_floor hqQ
      · have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
        linarith [le_trans h1 hqQ]
    refine Set.mem_iUnion₂.mpr ⟨q, Finset.mem_Icc.mpr ⟨hq1, hqQn⟩, χ, t, ?_, ?_⟩
    · have hcast : ((X + 1 : ℕ) : ℝ) = (X : ℝ) + 1 := by push_cast; ring
      rw [hcast] at ht
      calc |t| ≤ T * ((X : ℝ) + 1) := ht
        _ ≤ Tm * ((X : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right (le_max_left T 1) (by linarith)
    · exact le_trans hd (le_max_left B 0)
  have hsel1 : ∃ q ∈ Finset.Icc 1 Qn,
      ENNReal.ofReal (1 / (2 * ((Qn : ℝ) + 1))) ≤ μ (A ∩ Aq q) := by
    by_contra hno
    push_neg at hno
    have hAsub : A ⊆ ⋃ q ∈ Finset.Icc 1 Qn, (A ∩ Aq q) := fun ω hω => by
      obtain ⟨q, hq, hmem⟩ := Set.mem_iUnion₂.mp (hcover hω)
      exact Set.mem_iUnion₂.mpr ⟨q, hq, hω, hmem⟩
    have hle : μ A ≤ ∑ q ∈ Finset.Icc 1 Qn, μ (A ∩ Aq q) :=
      le_trans (measure_mono hAsub) (measure_biUnion_finset_le _ _)
    have hsum : ∑ q ∈ Finset.Icc 1 Qn, μ (A ∩ Aq q)
        ≤ (Finset.Icc 1 Qn).card • ENNReal.ofReal (1 / (2 * ((Qn : ℝ) + 1))) :=
      Finset.sum_le_card_nsmul _ _ _ fun q hq => (hno q hq).le
    have hcard : (Finset.Icc 1 Qn).card = Qn := by
      rw [Nat.card_Icc]
      omega
    have hfinal : μ A < ENNReal.ofReal (1 / 2) := by
      calc μ A ≤ (Finset.Icc 1 Qn).card
            • ENNReal.ofReal (1 / (2 * ((Qn : ℝ) + 1))) := le_trans hle hsum
        _ = ENNReal.ofReal ((Qn : ℝ) * (1 / (2 * ((Qn : ℝ) + 1)))) := by
            rw [hcard, nsmul_eq_mul, ← ENNReal.ofReal_natCast Qn,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg Qn)]
        _ < ENNReal.ofReal (1 / 2) := by
            rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
            rw [mul_one_div, div_lt_iff₀ (by positivity)]
            nlinarith [Nat.cast_nonneg (α := ℝ) Qn]
    exact absurd (lt_of_lt_of_le hfinal hA2) (lt_irrefl _)
  obtain ⟨qs, hqsmem, hqsμ⟩ := hsel1
  obtain ⟨hqs1, hqsQ⟩ := Finset.mem_Icc.mp hqsmem
  haveI : NeZero qs := ⟨by omega⟩
  -- select a heavy character mod `qs`
  set Aqχ : DirichletCharacter ℂ qs → Set Ω := fun χ => {ω | ∃ t : ℝ,
    |t| ≤ Tm * ((X : ℝ) + 1)
      ∧ pretentiousDistSq (G.g ω) (charTwist qs χ t) (X + 1) ≤ Bm} with hAqχdef
  have hnchqs : nch qs ≤ nmax := Finset.le_sup hqsmem
  have hsel2 : ∃ χs : DirichletCharacter ℂ qs,
      ENNReal.ofReal (1 / (2 * ((Qn : ℝ) + 1) * ((nmax : ℝ) + 1)))
        ≤ μ ((A ∩ Aq qs) ∩ Aqχ χs) := by
    by_contra hno
    push_neg at hno
    have hsub2 : (A ∩ Aq qs) ⊆ ⋃ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ qs)),
        ((A ∩ Aq qs) ∩ Aqχ χ) := by
      intro ω hω
      obtain ⟨χ, t, ht, hd⟩ := hω.2
      exact Set.mem_iUnion₂.mpr ⟨χ, Finset.mem_univ χ, hω, ⟨t, ht, hd⟩⟩
    have hle2 : μ (A ∩ Aq qs)
        ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ qs)),
            μ ((A ∩ Aq qs) ∩ Aqχ χ) :=
      le_trans (measure_mono hsub2) (measure_biUnion_finset_le _ _)
    have hsum2 : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ qs)),
        μ ((A ∩ Aq qs) ∩ Aqχ χ)
        ≤ (Finset.univ : Finset (DirichletCharacter ℂ qs)).card
          • ENNReal.ofReal (1 / (2 * ((Qn : ℝ) + 1) * ((nmax : ℝ) + 1))) :=
      Finset.sum_le_card_nsmul _ _ _ fun χ _ => (hno χ).le
    have hcard2 : (Finset.univ : Finset (DirichletCharacter ℂ qs)).card ≤ nmax := by
      rw [Finset.card_univ]
      calc Fintype.card (DirichletCharacter ℂ qs) = nch qs := by
            simp only [hnchdef]
            rw [dif_pos hqs1]
        _ ≤ nmax := hnchqs
    have hfinal2 : μ (A ∩ Aq qs)
        < ENNReal.ofReal (1 / (2 * ((Qn : ℝ) + 1))) := by
      calc μ (A ∩ Aq qs)
          ≤ (Finset.univ : Finset (DirichletCharacter ℂ qs)).card
            • ENNReal.ofReal (1 / (2 * ((Qn : ℝ) + 1) * ((nmax : ℝ) + 1))) :=
            le_trans hle2 hsum2
        _ ≤ nmax • ENNReal.ofReal (1 / (2 * ((Qn : ℝ) + 1) * ((nmax : ℝ) + 1))) := by
            exact nsmul_le_nsmul_left (by positivity) hcard2
        _ = ENNReal.ofReal ((nmax : ℝ)
            * (1 / (2 * ((Qn : ℝ) + 1) * ((nmax : ℝ) + 1)))) := by
            rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast nmax,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg nmax)]
        _ < ENNReal.ofReal (1 / (2 * ((Qn : ℝ) + 1))) := by
            rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
            rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
            nlinarith [Nat.cast_nonneg (α := ℝ) nmax, Nat.cast_nonneg (α := ℝ) Qn]
    exact absurd (lt_of_lt_of_le hfinal2 hqsμ) (lt_irrefl _)
  obtain ⟨χs, hχsμ⟩ := hsel2
  -- the Markov event at the selected pair's window length
  obtain ⟨EM, hEMm, hEMp, hEMb⟩ := exists_measurable_zeta_window_event G hC'0 hC'ub
    (hFH1 qs χs) hXr3 hεM0 hεM1
  have hEMc : μ EMᶜ ≤ ENNReal.ofReal εM := by
    rw [measure_compl hEMm (measure_ne_top μ _), measure_univ]
    calc (1 : ℝ≥0∞) - μ EM ≤ 1 - ENNReal.ofReal (1 - εM) := tsub_le_tsub_left hEMp 1
      _ = ENNReal.ofReal εM := by
          rw [← ENNReal.ofReal_one,
            ← ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ 1 - εM)]
          congr 1
          ring
  have hne : (((A ∩ Aq qs) ∩ Aqχ χs) ∩ EM).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hsubc : ((A ∩ Aq qs) ∩ Aqχ χs) ⊆ EMᶜ := by
      intro ω hω hEM
      exact absurd hemp (Set.nonempty_iff_ne_empty.mp ⟨ω, hω, hEM⟩)
    have hlt : ENNReal.ofReal (1 / (2 * ((Qn : ℝ) + 1) * ((nmax : ℝ) + 1)))
        ≤ ENNReal.ofReal εM := le_trans hχsμ (le_trans (measure_mono hsubc) hEMc)
    have : ¬ (ENNReal.ofReal (1 / (2 * ((Qn : ℝ) + 1) * ((nmax : ℝ) + 1)))
        ≤ ENNReal.ofReal εM) := by
      rw [not_le, ENNReal.ofReal_lt_ofReal_iff (by positivity), hεMdef]
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) nmax, Nat.cast_nonneg (α := ℝ) Qn]
    exact this hlt
  obtain ⟨ω, ⟨⟨hωA, _⟩, hωAqχ⟩, hωEM⟩ := hne
  -- unpack the sample data
  have hcm : CompletelyMultiplicativeC (G.g ω) := hωA.1.2
  have huni : Unimodular (G.g ω) := hωA.2
  obtain ⟨t, hts, hds⟩ := hωAqχ
  obtain ⟨q', χ', t', hq'Q, ht', hd'⟩ := hωA.1.1.2
  -- the second certificate has positive modulus
  have hq'1 : 1 ≤ q' := by
    rcases Nat.eq_zero_or_pos q' with rfl | h
    · exact absurd (le_trans hd' (le_max_left B 0))
        (hW1 ⌊(X : ℝ) ^ δ⌋₊ hfloorW1 (G.g ω) χ' t')
    · exact h
  -- both certificates live at the t-cut scale
  have hcert1 : pretentiousDistSq (G.g ω) (charTwist qs χs t) ⌊(X : ℝ) ^ δ⌋₊ ≤ Bm :=
    le_trans (pretentiousDistSq_mono_of_norm_le_one huni
      (charTwist_norm_le_one qs χs t) hfloorle) hds
  have hqsQR : (qs : ℝ) ≤ max Q 1 := by
    rcases le_total 0 Q with hQ0 | hQ0
    · calc (qs : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hqsQ
        _ ≤ Q := Nat.floor_le hQ0
        _ ≤ max Q 1 := le_max_left _ _
    · have hQn0 : Qn = 0 := by
        rw [hQndef]
        exact Nat.floor_of_nonpos hQ0
      omega
  have hq'QR : (q' : ℝ) ≤ max Q 1 := le_trans hq'Q (le_max_left _ _)
  have hfl : ((⌊(X : ℝ) ^ δ⌋₊ : ℕ) : ℝ) ≤ (X : ℝ) ^ δ := Nat.floor_le hXδnn
  -- frequency windows for the t-cut
  have ht2T : |t| ≤ 2 * Tm * (X : ℝ) := by
    calc |t| ≤ Tm * ((X : ℝ) + 1) := hts
      _ ≤ 2 * Tm * (X : ℝ) := by nlinarith
  have ht'Tδ : |t'| ≤ Tm * (X : ℝ) ^ δ := by
    calc |t'| ≤ T * ((⌊(X : ℝ) ^ δ⌋₊ : ℕ) : ℝ) := ht'
      _ ≤ Tm * (X : ℝ) ^ δ :=
          mul_le_mul (le_max_left T 1) hfl (Nat.cast_nonneg _) (by linarith)
  have ht'2T : |t'| ≤ 2 * Tm * (X : ℝ) := by
    calc |t'| ≤ Tm * (X : ℝ) ^ δ := ht'Tδ
      _ ≤ 2 * Tm * (X : ℝ) := by nlinarith [hXδleX]
  -- the Vinogradov–Korobov t-cut
  have htcut := hF2 (X : ℝ) hXF2le (G.g ω) huni qs χs t hqs1 hqsQR ht2T hcert1
    q' χ' t' hq'1 hq'QR ht'2T (le_trans hd' (le_max_left B 0))
  have htsmall : |t| ≤ (Tm + 1) * (X : ℝ) ^ δ := by
    have h1 : |t| ≤ |t'| + |t - t'| := by
      calc |t| = |t' + (t - t')| := by congr 1; ring
        _ ≤ |t'| + |t - t'| := abs_add_le _ _
    nlinarith [htcut.le, ht'Tδ]
  -- pretentious input of the chain, at the conductor pair
  have hpret : pretentiousDistSq
      (hPart (G.g ω) χs.conductor χs.primitiveCharacter t) (fun _ => 1) (X + 1)
      ≤ B₂ := by
    have hP1 := pretentiousDistSq_hPart_le (g := G.g ω) (q := χs.conductor)
      (χ := χs.primitiveCharacter) (t := t) huni (X + 1)
    have hP4 := pretentiousDistSq_primitive_le χs huni t (X + 1)
    have hωq : (qs.primeFactors.card : ℝ) ≤ (Qn : ℝ) := by
      exact_mod_cast le_trans (card_primeFactors_le_self qs) hqsQ
    calc pretentiousDistSq (hPart (G.g ω) χs.conductor χs.primitiveCharacter t)
          (fun _ => 1) (X + 1)
        ≤ pretentiousDistSq (G.g ω)
            (charTwist χs.conductor χs.primitiveCharacter t) (X + 1) := hP1
      _ ≤ pretentiousDistSq (G.g ω) (charTwist qs χs t) (X + 1)
          + 2 * qs.primeFactors.card := hP4
      _ ≤ Bm + 2 * (Qn : ℝ) := by linarith [hds]
      _ = B₂ := by rw [hB₂def]
  -- window input of the chain, via the Markov event and the archimedean transfer
  have hEMω := hEMb ω hωEM
  simp only [windowSumC] at hEMω
  have hHsmax : ((FHX qs χs).1 : ℝ) ≤ (Hmax : ℝ) := by
    exact_mod_cast (hHpair qs hqs1 hqsQ χs).1
  have hHs0 : (0 : ℝ) ≤ ((FHX qs χs).1 : ℝ) := Nat.cast_nonneg _
  have hHm0 : (0 : ℝ) ≤ (Hmax : ℝ) := Nat.cast_nonneg _
  have hlogHs : 4 * (((FHX qs χs).1 : ℝ)) ^ 2 ≤ Real.log X := by
    nlinarith
  have hδHs : 8 * δ * (((FHX qs χs).1 : ℝ)) ^ 2 ≤ 1 := by
    have hδle : δ ≤ 1 / (8 * ((Hmax : ℝ) + 1) ^ 3) := min_le_right _ _
    have hY1 : (1 : ℝ) ≤ (Hmax : ℝ) + 1 := by linarith
    have hY0 : (0 : ℝ) < 8 * ((Hmax : ℝ) + 1) ^ 3 := by positivity
    have h1 : (((FHX qs χs).1 : ℝ)) ^ 2 ≤ ((Hmax : ℝ) + 1) ^ 2 := by nlinarith
    have h2 : 8 * δ * (((FHX qs χs).1 : ℝ)) ^ 2
        ≤ 8 * (1 / (8 * ((Hmax : ℝ) + 1) ^ 3)) * ((Hmax : ℝ) + 1) ^ 2 := by
      have hδnn : (0 : ℝ) ≤ δ := hδ0.le
      nlinarith [mul_le_mul hδle h1 (by positivity) (by positivity)]
    have h3 : 8 * (1 / (8 * ((Hmax : ℝ) + 1) ^ 3)) * ((Hmax : ℝ) + 1) ^ 2
        = 1 / ((Hmax : ℝ) + 1) := by
      field_simp
    have h4 : 1 / ((Hmax : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  have hXδHs : 72 * (((FHX qs χs).1 : ℝ)) ^ 3 * (Tm + 1) ≤ (X : ℝ) ^ δ := by
    refine le_trans ?_ hXδ3
    have h1 : (((FHX qs χs).1 : ℝ)) ^ 3 ≤ ((Hmax : ℝ) + 1) ^ 3 :=
      pow_le_pow_left₀ hHs0 (by linarith) 3
    nlinarith
  have htrans := window_transfer hcm huni χs.primitiveCharacter hXr3
    (by linarith : (1 : ℝ) ≤ Tm + 1) hδ0 htsmall (hFH1 qs χs) hlogHs hδHs hXδHs hEMω
  have hCgD : 4 * C' * (2 + Real.log X) / εM + 3 * Real.log X ≤ D * Real.log X := by
    have hCgeq : 4 * C' * (2 + Real.log X) / εM
        = 16 * C' * ((Qn : ℝ) + 1) * ((nmax : ℝ) + 1) * (2 + Real.log X) := by
      rw [hεMdef]
      field_simp
      ring
    have h23 : 2 + Real.log X ≤ 3 * Real.log X := by linarith
    have hpos : (0 : ℝ) ≤ 16 * C' * ((Qn : ℝ) + 1) * ((nmax : ℝ) + 1) := by positivity
    rw [hCgeq, hDdef]
    nlinarith [mul_le_mul_of_nonneg_left h23 hpos]
  -- the refutation closes the proof
  exact hFref qs χs hqs1 X
    (by have := (hHpair qs hqs1 hqsQ χs).2; omega)
    (G.g ω) hcm huni t hpret (le_trans htrans hCgD)

/-- **Milestone restatement** (Theorem 1.8 with both derivation legs discharged): the van
der Corput leg comes from the nonasymptotic Elliott interface, the Borwein–Choi–Coons leg
from the Vinogradov–Korobov interface, so Theorem 1.8 is now conditional on exactly the
two permanent deep inputs `{LogElliottNonasymptoticAssumption, VinogradovKorobovAssumption}`
(plus the §2 Fourier reduction for EDP itself). -/
theorem theorem18_of_logElliott_vinogradovKorobov
    [LogElliottNonasymptoticAssumption] [VinogradovKorobovAssumption]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, sndMomentPartialSum G n ≤ C :=
  theorem18 μ G

end Tao2015

end MoltResearch
