import Conjectures.C0003_edp_rate.src.ElliottThresholds

/-!
# Finite van der Corput package: the endpoint obstruction

The A6 cutoff-local Markov estimate needs the moment-fit inequality `X + H ≤ L`, where
`L` is the last index supplied by `FiniteSecondMomentBound` and `H` is the positive van der
Corput window length.  The A3 target `FinitePersistentPretentious`, however, asks for the
pretentiousness estimate at every `X` through the same endpoint `L`.

**Blocked:** at `X = L` these two requirements give `L + H ≤ L`, while
`one_le_edpVdCWindowLength` proves `1 ≤ H`.  Thus no starting scale `X₀ ≤ L` makes the A6
consumer applicable on the full interval required by the current interface.  This file
formalizes that exact failing inequality and does not install a
`FiniteVanDerCorputRateAssumption` instance.

Possible repairs are the interface changes already identified in
`Problems/edp_rate_elliott_thresholds.md`: supply Fourier moments through `L + H`, shorten
the persistent interval and check the structured consumer against it, or prove a different
scale-transfer/window lemma.  None is among A7's listed deliverables.
-/

namespace MoltResearch

/-- The schedule condition needed to apply A6's cutoff-local Elliott-window estimate at
every scale in the interval required by `FinitePersistentPretentious`. -/
def FiniteVdCWindowScheduleFits (C ε : ℝ) (L : ℕ) : Prop :=
  ∃ X₀ : ℕ, 1 ≤ X₀ ∧ X₀ ≤ L ∧
    ∀ X : ℕ, X₀ ≤ X → X ≤ L → X + edpVdCWindowLength C ε ≤ L

/-- The terminal Elliott window never fits inside a moment cutoff ending at the same scale:
its positive length forces the endpoint moment index strictly past `L`. -/
theorem edpVdC_endpoint_window_does_not_fit (C ε : ℝ) (L : ℕ) :
    ¬ L + edpVdCWindowLength C ε ≤ L := by
  have hH : 1 ≤ edpVdCWindowLength C ε := one_le_edpVdCWindowLength C ε
  omega

/-- No nonempty starting interval through `L` can satisfy the moment-fit premise consumed by
the A6 expectation and Markov estimates at every scale in that interval. -/
theorem finiteVdCWindowScheduleFits_false (C ε : ℝ) (L : ℕ) :
    ¬ FiniteVdCWindowScheduleFits C ε L := by
  rintro ⟨X₀, -, hX₀L, hfit⟩
  exact edpVdC_endpoint_window_does_not_fit C ε L (hfit L hX₀L le_rfl)

end MoltResearch
