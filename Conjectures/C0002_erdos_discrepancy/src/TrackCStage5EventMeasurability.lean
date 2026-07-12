import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5VanDerCorput

/-!
# Track C: Stage 5 — the pretentious event is measurable (Tao 2015 §4)

Measure-theoretic hygiene for the §4 endgame of arXiv:1509.05363 (issue #2871, PR M1): the
`pretentiousEvent G Q T B X` of the van der Corput interface is a *measurable* set.

Why this is needed: the §4 stochastic upgrade intersects two Proposition-1.11 events at
different scales with a Markov-inequality event and runs a union/lower bound on the
probabilities. Measure lower bounds only combine through `MeasurableSet` (otherwise `μ` is
merely an outer measure on the intersection), so `MeasurableSet (pretentiousEvent …)` is the
gate through which the Prop-1.11 conclusions enter the endgame.

Proof idea — a countable skeleton for an uncountable existential. The event quantifies over
`q : ℕ`, `χ : DirichletCharacter ℂ q`, and a *real* frequency `t`:
- the period range `(q : ℝ) ≤ Q` is the finite set `Finset.Icc 1 ⌊Q⌋₊` plus the degenerate
  modulus `q = 0` (where every character kills every prime, so the distance collapses to the
  `ω`-free constant `∑_{p<X} 1/p` and the slice is `univ` or `∅`);
- for each fixed `(q, χ)` there are finitely many characters (`DirichletCharacter.fintype`),
  and the frequency slice `{ω | ∃ t, |t| ≤ c ∧ 𝔻²(𝐠(ω), χ·(·)^{it}; X) ≤ B}` is rewritten
  as `⋂_j ⋃_{s : ℚ} {ω | |s| ≤ 1 ∧ 𝔻²(𝐠(ω), χ·(·)^{i·c·s}; X) < B + 1/(j+1)}`: rational
  frequencies suffice because `t ↦ 𝔻²` is continuous (a finite sum of `cpow` twists), and the
  strict-inequality slack `1/(j+1)` is recovered in the limit by compactness of `[-1, 1]`
  (extract a convergent subsequence of rational witnesses and pass to the limit).
Each layer is then a countable union/intersection of sub-level sets of `ω`-measurable maps
(coordinatewise measurability is the `measurable` field of `StochasticMultiplicative`).
-/

namespace MoltResearch

namespace Tao2015

open MeasureTheory

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Continuity of the squared pretentious distance in the frequency of the comparison twist:
`t ↦ 𝔻(g, χ(·)·(·)^{it}; X)²` is a finite sum of compositions of `cpow` (with nonzero prime
base), conjugation, and real parts — all continuous. -/
private lemma continuous_pretentiousDistSq_charTwist (g : ℕ → ℂ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (X : ℕ) :
    Continuous fun t : ℝ => pretentiousDistSq g (charTwist q χ t) X := by
  simp only [pretentiousDistSq, charTwist]
  refine continuous_finset_sum _ fun p hp => ?_
  have hp' : p.Prime := Nat.prime_of_mem_primesBelow hp
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp'.ne_zero
  have hcpow : Continuous fun t : ℝ => ((p : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) :=
    (continuous_const.mul Complex.continuous_ofReal).const_cpow (Or.inl hp0)
  have hinner : Continuous fun t : ℝ =>
      (g p * (starRingEnd ℂ)
        (χ ((p : ℕ) : ZMod q) * ((p : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)))).re :=
    Complex.continuous_re.comp
      (continuous_const.mul (Complex.continuous_conj.comp (continuous_const.mul hcpow)))
  exact (continuous_const.sub hinner).div_const _

/-- Measurability in the sample of the squared pretentious distance to a fixed twist:
per prime, the coordinate map `ω ↦ 𝐠(ω)(p)` is measurable and the rest is a continuous
function of that coordinate. -/
private lemma measurable_pretentiousDistSq_charTwist (G : StochasticMultiplicative μ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) :
    Measurable fun ω : Ω => pretentiousDistSq (G.g ω) (charTwist q χ t) X := by
  simp only [pretentiousDistSq]
  refine Finset.measurable_sum _ fun p _ => ?_
  have hcont : Continuous fun z : ℂ =>
      (1 - (z * (starRingEnd ℂ) (charTwist q χ t p)).re) / (p : ℝ) :=
    (continuous_const.sub
      (Complex.continuous_re.comp (continuous_id.mul continuous_const))).div_const _
  exact hcont.measurable.comp (G.measurable p)

/-- The `(q, χ)`-slice of the pretentious event is measurable: the real-frequency existential
`∃ t, |t| ≤ c ∧ 𝔻² ≤ B` equals the countable skeleton
`⋂_j ⋃_{s : ℚ} {|s| ≤ 1 ∧ 𝔻²(frequency c·s) < B + 1/(j+1)}` — rationals suffice by continuity
in the frequency, and the limit `≤ B` is recovered by compactness of `[-1, 1]`. -/
private lemma measurableSet_frequencySlice (G : StochasticMultiplicative μ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (c B : ℝ) (X : ℕ) :
    MeasurableSet {ω : Ω | ∃ t : ℝ, |t| ≤ c ∧
      pretentiousDistSq (G.g ω) (charTwist q χ t) X ≤ B} := by
  by_cases hc : 0 ≤ c
  · -- the countable rational-frequency skeleton
    have hset : {ω : Ω | ∃ t : ℝ, |t| ≤ c ∧
          pretentiousDistSq (G.g ω) (charTwist q χ t) X ≤ B}
        = ⋂ j : ℕ, ⋃ s : ℚ, {ω : Ω | |(s : ℝ)| ≤ 1 ∧
            pretentiousDistSq (G.g ω) (charTwist q χ (c * (s : ℝ))) X
              < B + 1 / ((j : ℝ) + 1)} := by
      ext ω
      have hFc : Continuous fun s : ℝ =>
          pretentiousDistSq (G.g ω) (charTwist q χ (c * s)) X :=
        (continuous_pretentiousDistSq_charTwist (G.g ω) q χ X).comp
          (continuous_const.mul continuous_id)
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
      constructor
      · rintro ⟨t₀, ht₀, hFt₀⟩ j
        have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
        rcases hc.eq_or_lt with hc0 | hcpos
        · -- `c = 0`: the only admissible frequency is `t₀ = 0`; take `s = 0`
          have ht0 : t₀ = 0 := abs_nonpos_iff.mp (hc0 ▸ ht₀)
          refine ⟨0, by norm_num, ?_⟩
          have heq : c * ((0 : ℚ) : ℝ) = t₀ := by rw [ht0, Rat.cast_zero, mul_zero]
          rw [heq]
          exact lt_of_le_of_lt hFt₀ (lt_add_of_pos_right B hj)
        · -- `c > 0`: rescale to `s₀ = t₀/c ∈ [-1, 1]` and pick a nearby rational
          set s₀ : ℝ := t₀ / c with hs₀def
          have hcs₀ : c * s₀ = t₀ := by rw [hs₀def]; field_simp
          have hs₀le : |s₀| ≤ 1 := by
            rw [hs₀def, abs_div, abs_of_pos hcpos, div_le_one hcpos]
            exact ht₀
          have hs₀U : s₀ ∈ (fun s : ℝ =>
              pretentiousDistSq (G.g ω) (charTwist q χ (c * s)) X) ⁻¹'
              Set.Iio (B + 1 / ((j : ℝ) + 1)) := by
            simp only [Set.mem_preimage, Set.mem_Iio, hcs₀]
            exact lt_of_le_of_lt hFt₀ (lt_add_of_pos_right B hj)
          obtain ⟨δ, hδpos, hball⟩ :=
            Metric.isOpen_iff.mp (isOpen_Iio.preimage hFc) s₀ hs₀U
          have hs₀1 : s₀ ≤ 1 := le_trans (le_abs_self s₀) hs₀le
          have hs₀2 : -1 ≤ s₀ := (abs_le.mp hs₀le).1
          have hlt : max (s₀ - δ) (-1) < min (s₀ + δ) 1 := by
            rw [lt_min_iff, max_lt_iff, max_lt_iff]
            exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
          obtain ⟨s, hsl, hsr⟩ := exists_rat_btwn hlt
          have h1 : s₀ - δ < (s : ℝ) := lt_of_le_of_lt (le_max_left _ _) hsl
          have h2 : (-1 : ℝ) < (s : ℝ) := lt_of_le_of_lt (le_max_right _ _) hsl
          have h3 : (s : ℝ) < s₀ + δ := lt_of_lt_of_le hsr (min_le_left _ _)
          have h4 : (s : ℝ) < 1 := lt_of_lt_of_le hsr (min_le_right _ _)
          refine ⟨s, abs_le.mpr ⟨h2.le, h4.le⟩, ?_⟩
          have hmem := hball (show (s : ℝ) ∈ Metric.ball s₀ δ by
            rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
            constructor <;> linarith)
          simpa using hmem
      · -- limit direction: rational witnesses accumulate in `[-1, 1]`
        intro h
        choose u hu1 hu2 using h
        have humem : ∀ j : ℕ, ((u j : ℝ)) ∈ Set.Icc (-1 : ℝ) 1 :=
          fun j => Set.mem_Icc.mpr (abs_le.mp (hu1 j))
        obtain ⟨sstar, hsstar, φ, hφ, hφt⟩ := isCompact_Icc.tendsto_subseq humem
        have htend2 : Filter.Tendsto (fun j : ℕ => B + 1 / ((j : ℝ) + 1))
            Filter.atTop (nhds B) := by
          simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add B
        have hlim : pretentiousDistSq (G.g ω) (charTwist q χ (c * sstar)) X ≤ B := by
          refine le_of_tendsto_of_tendsto' ((hFc.tendsto sstar).comp hφt) htend2 fun j => ?_
          have hjφ : j ≤ φ j := hφ.le_apply
          have hjcast : ((j : ℝ)) + 1 ≤ ((φ j : ℝ)) + 1 := by
            have : (j : ℝ) ≤ (φ j : ℝ) := Nat.cast_le.mpr hjφ
            linarith
          have hdiv : 1 / ((φ j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
            one_div_le_one_div_of_le (by positivity) hjcast
          have hlt := hu2 (φ j)
          simp only [Function.comp_apply]
          linarith
        refine ⟨c * sstar, ?_, hlim⟩
        rw [abs_mul, abs_of_nonneg hc]
        exact mul_le_of_le_one_right hc (abs_le.mpr (Set.mem_Icc.mp hsstar))
    rw [hset]
    refine MeasurableSet.iInter fun j => MeasurableSet.iUnion fun s => ?_
    by_cases hs : |(s : ℝ)| ≤ 1
    · have heq : {ω : Ω | |(s : ℝ)| ≤ 1 ∧
            pretentiousDistSq (G.g ω) (charTwist q χ (c * (s : ℝ))) X
              < B + 1 / ((j : ℝ) + 1)}
          = {ω : Ω | pretentiousDistSq (G.g ω) (charTwist q χ (c * (s : ℝ))) X
              < B + 1 / ((j : ℝ) + 1)} := by
        ext ω; simp [hs]
      rw [heq]
      exact measurableSet_lt
        (measurable_pretentiousDistSq_charTwist G q χ (c * (s : ℝ)) X) measurable_const
    · have heq : {ω : Ω | |(s : ℝ)| ≤ 1 ∧
            pretentiousDistSq (G.g ω) (charTwist q χ (c * (s : ℝ))) X
              < B + 1 / ((j : ℝ) + 1)} = (∅ : Set Ω) := by
        ext ω; simp [hs]
      rw [heq]
      exact MeasurableSet.empty
  · -- negative frequency budget: no admissible `t` at all
    have hempty : {ω : Ω | ∃ t : ℝ, |t| ≤ c ∧
          pretentiousDistSq (G.g ω) (charTwist q χ t) X ≤ B} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨t, ht, -⟩
      exact hc ((abs_nonneg t).trans ht)
    rw [hempty]
    exact MeasurableSet.empty

/-- At the degenerate modulus `q = 0`, every Dirichlet character kills every prime
(`(p : ZMod 0)` is a non-unit integer), so the squared pretentious distance to any such twist
collapses to the `ω`-, `χ`-, and `t`-free constant `∑_{p < X} 1/p`. -/
private lemma pretentiousDistSq_charTwist_zero_modulus (g : ℕ → ℂ)
    (χ : DirichletCharacter ℂ 0) (t : ℝ) (X : ℕ) :
    pretentiousDistSq g (charTwist 0 χ t) X = ∑ p ∈ X.primesBelow, 1 / (p : ℝ) := by
  unfold pretentiousDistSq
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.Prime := Nat.prime_of_mem_primesBelow hp
  have hnu : ¬IsUnit ((p : ℕ) : ZMod 0) := fun h =>
    (ZMod.isUnit_prime_iff_not_dvd hp').mp h (dvd_zero p)
  have hzero : charTwist 0 χ t p = 0 := by
    unfold charTwist
    rw [MulChar.map_nonunit χ hnu, zero_mul]
  rw [hzero, map_zero, mul_zero, Complex.zero_re, sub_zero]

/-- The `q = 0` slice of the pretentious event is measurable: by the collapse lemma its
defining condition is `ω`-free, so the slice is `univ` or `∅`. -/
private lemma measurableSet_zeroModulusSlice (G : StochasticMultiplicative μ)
    (Q T B : ℝ) (X : ℕ) :
    MeasurableSet {ω : Ω | ∃ (χ : DirichletCharacter ℂ 0) (t : ℝ),
      ((0 : ℕ) : ℝ) ≤ Q ∧ |t| ≤ T * X ∧
      pretentiousDistSq (G.g ω) (charTwist 0 χ t) X ≤ B} := by
  have hset : {ω : Ω | ∃ (χ : DirichletCharacter ℂ 0) (t : ℝ),
        ((0 : ℕ) : ℝ) ≤ Q ∧ |t| ≤ T * X ∧
        pretentiousDistSq (G.g ω) (charTwist 0 χ t) X ≤ B}
      = {_ω : Ω | (0 : ℝ) ≤ Q ∧ 0 ≤ T * (X : ℝ) ∧
          (∑ p ∈ X.primesBelow, 1 / (p : ℝ)) ≤ B} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨χ, t, hQ0, ht, hB⟩
      rw [pretentiousDistSq_charTwist_zero_modulus] at hB
      exact ⟨by simpa using hQ0, (abs_nonneg t).trans ht, hB⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨1, 0, by simpa using h1, by simpa using h2,
        by rw [pretentiousDistSq_charTwist_zero_modulus]; exact h3⟩
  rw [hset]
  exact MeasurableSet.const _

/-- **The pretentious event is measurable** (Tao 2015, arXiv:1509.05363 §4 hygiene): the event
of `pretentiousEvent G Q T B X` — some character twist of period `≤ Q` and frequency
`|t| ≤ T·X` within squared pretentious distance `B` of the sample — is a measurable set, so
the §4 endgame may intersect Prop-1.11 events at two scales with a Markov event and add up
measure lower bounds.

Proof: split the period existential into the degenerate modulus `q = 0` (an `ω`-free slice)
and the finite range `Finset.Icc 1 ⌊Q⌋₊`; for each of the finitely many characters, the
frequency slice is a countable rational-frequency skeleton of sub-level sets of measurable
maps (`measurableSet_frequencySlice`). -/
theorem measurableSet_pretentiousEvent {μ : Measure Ω} (G : StochasticMultiplicative μ)
    (Q T B : ℝ) (X : ℕ) :
    MeasurableSet (pretentiousEvent G Q T B X) := by
  by_cases hQ : 0 ≤ Q
  · have hdecomp : pretentiousEvent G Q T B X =
        {ω : Ω | ∃ (χ : DirichletCharacter ℂ 0) (t : ℝ),
            ((0 : ℕ) : ℝ) ≤ Q ∧ |t| ≤ T * X ∧
            pretentiousDistSq (G.g ω) (charTwist 0 χ t) X ≤ B} ∪
        ⋃ q ∈ Finset.Icc 1 ⌊Q⌋₊, ⋃ χ : DirichletCharacter ℂ q,
          {ω : Ω | ∃ t : ℝ, |t| ≤ T * X ∧
            pretentiousDistSq (G.g ω) (charTwist q χ t) X ≤ B} := by
      ext ω
      simp only [pretentiousEvent, Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion,
        Finset.mem_Icc, exists_prop]
      constructor
      · rintro ⟨q, χ, t, hq, ht, hd⟩
        rcases Nat.eq_zero_or_pos q with rfl | hq1
        · exact Or.inl ⟨χ, t, hq, ht, hd⟩
        · exact Or.inr ⟨q, ⟨hq1, Nat.le_floor hq⟩, χ, t, ht, hd⟩
      · rintro (⟨χ, t, hq, ht, hd⟩ | ⟨q, ⟨-, hq2⟩, χ, t, ht, hd⟩)
        · exact ⟨0, χ, t, hq, ht, hd⟩
        · exact ⟨q, χ, t, (Nat.le_floor_iff hQ).mp hq2, ht, hd⟩
    rw [hdecomp]
    refine (measurableSet_zeroModulusSlice G Q T B X).union ?_
    refine Finset.measurableSet_biUnion _ fun q _ => ?_
    exact MeasurableSet.iUnion fun χ => measurableSet_frequencySlice G q χ (T * X) B X
  · -- `Q < 0`: no admissible period, the event is empty
    have hempty : pretentiousEvent G Q T B X = ∅ := by
      ext ω
      simp only [pretentiousEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨q, χ, t, hq, -, -⟩
      exact hQ ((Nat.cast_nonneg q).trans hq)
    rw [hempty]
    exact MeasurableSet.empty

-- Consumer example (compile-only): the §4 endgame shape — the Prop-1.11 events at two
-- different scales intersect into a measurable set, ready for measure lower bounds.
example {μ : Measure Ω} (G : StochasticMultiplicative μ) (Q T B : ℝ) (X₁ X₂ : ℕ) :
    MeasurableSet (pretentiousEvent G Q T B X₁ ∩ pretentiousEvent G Q T B X₂) :=
  (measurableSet_pretentiousEvent G Q T B X₁).inter
    (measurableSet_pretentiousEvent G Q T B X₂)

end Tao2015

end MoltResearch
