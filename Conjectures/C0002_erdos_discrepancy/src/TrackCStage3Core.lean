import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2CoreExtras

/-!
# Track C: Stage 3 core lemmas (Tao 2015 plane)

This file is intentionally tiny.

It contains the minimal proved projections/lemmas about `Tao2015.Stage3Output` needed by
later stages, without importing the large Stage-3 output-lemma library
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Output`.
-/

namespace MoltResearch

namespace Tao2015

namespace Stage3Output

variable {f : ℕ → ℤ}

/-- Alias for the packaged global conclusion, matching Stage-2 naming.

Stage 2 calls this statement `Stage2Output.notBoundedOriginal`; Stage 3 exposes it as the method
`out.notBounded` (derived from the Stage-2 output). This alias lets downstream code use a
consistent name at both boundaries.
-/
abbrev notBoundedOriginal (out : Stage3Output f) : ¬ BoundedDiscrepancy f :=
  out.notBounded

/-!
Note: `Stage3Output.hasDiscrepancyAtLeast` is already defined in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3`.

We avoid re-declaring it here so that `TrackCStage3Core` can be imported alongside
`TrackCStage3` without name clashes.
-/

-- Note: the basic projections `Stage3Output.d` and `Stage3Output.g` live in
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3` so that hard-gate consumers can access
-- them without importing `TrackCStage3Core`.

/-- The reduced sequence packaged in Stage 3 is a sign sequence. -/
theorem hg (out : Stage3Output f) : IsSignSequence out.g := by
  simpa [Stage3Output.g] using (Stage2Output.hg (f := f) out.out2)

/-- Stage 3 retains the Stage-2 reduced-step unboundedness witness.

This is a tiny convenience projection so consumers of `Stage3Output` do not have to reach into the
nested Stage-2 record field `out.out2.unbounded`.
-/
abbrev unboundedReducedAlong (out : Stage3Output f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d :=
  out.out2.unbounded

/-- Equivalent packaging: arbitrarily large reduced-sequence discrepancy witnesses along `out.d`.

This is the `HasDiscrepancyAtLeastAlong` normal form of `unboundedReducedAlong`.
-/
theorem forall_hasDiscrepancyAtLeastAlong (out : Stage3Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C := by
  -- Package the definitional equivalence as a named lemma, avoiding repeated unfolding.
  exact
    (HasDiscrepancyAtLeastAlong.forall_hasDiscrepancyAtLeastAlong_iff_unboundedDiscrepancyAlong
          (g := out.g) (d := out.d)).2
      out.unboundedReducedAlong

/-!
Note: `Stage3Output.notBoundedReducedAlong` is already defined in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3`.

We do not re-declare it here so that `TrackCStage3Core` can be imported alongside `TrackCStage3`
without name clashes.
-/

/-!
Note: `Stage3Output.unboundedDiscrepancyAlong_core` is already defined in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3`.

This file focuses on tiny arithmetic rewrites and start-index lemmas that are
convenient for later stages, without re-declaring boundary lemmas.
-/

-- Note: the basic projection `Stage3Output.m` lives in `TrackCStage3.lean` alongside `d` and `g`.
-- Note: `Stage3Output.unboundedDiscOffset` is defined in `TrackCStage3.lean`.

-- Note: the projection `Stage3Output.start` lives in `TrackCStage3.lean` so hard-gate consumers can
-- access it without importing `TrackCStage3Core`.

/-- Definitional rewrite: the bundled Stage-3 start index is the Stage-2 start index
of the carried Stage-2 output.

This lemma is intentionally tiny (and not marked as a simp lemma): it exists mainly to reduce
`dsimp` noise when shuttling facts between Stage 2 and Stage 3.
-/
theorem start_eq_out2_start (out : Stage3Output f) : out.start = out.out2.start := by
  rfl

/-- The affine-tail start index `out.start` is a multiple of the reduced step size `out.d`. -/
theorem d_dvd_start (out : Stage3Output f) : out.d ∣ out.start := by
  -- Delegate to the Stage-2 core lemma (avoids re-proving arithmetic about the projections).
  simpa [Stage3Output.start, Stage2Output.start] using
    (Stage2Output.d_dvd_start (f := f) out.out2)

/-- The affine-tail start index `out.start` has remainder `0` when reduced modulo `out.d`. -/
theorem start_mod_d (out : Stage3Output f) : out.start % out.d = 0 := by
  simpa [Stage3Output.start, Stage2Output.start] using
    (Stage2Output.start_mod_d (f := f) out.out2)

/-- Adding the start index does not change residues modulo the step size.

Since `out.start` is a multiple of `out.d`, we have
`(n + out.start) % out.d = n % out.d`.
-/
theorem add_start_mod_d (out : Stage3Output f) (n : ℕ) :
    (n + out.start) % out.d = n % out.d := by
  simpa [Stage3Output.start, Stage2Output.start] using
    (Stage2Output.add_start_mod_d (f := f) out.out2 n)

/-- Rewrite for the reduced sequence packaged in Stage 3: it is a shift by `m*d`. -/
theorem g_eq (out : Stage3Output f) (k : ℕ) :
    out.g k = f (k + out.m * out.d) := by
  simpa [Stage3Output.g, Stage3Output.m, Stage3Output.d] using
    (Stage2Output.g_eq (f := f) out.out2 k)

/-- Rewrite for the reduced sequence packaged in Stage 3, phrased using the bundled start index
`out.start = out.m * out.d`. -/
theorem g_eq_start (out : Stage3Output f) (k : ℕ) :
    out.g k = f (k + out.start) := by
  simpa [Stage3Output.start] using (out.g_eq (f := f) k)

/-- Function-level rewrite for the reduced sequence packaged in Stage 3: it is the shifted sequence
`fun k => f (k + out.start)`.
-/
theorem g_eq_fun (out : Stage3Output f) :
    out.g = fun k => f (k + out.start) := by
  funext k
  simpa using out.g_eq_start (f := f) k

/-- Convenience projection: positivity of the reduced step size. -/
@[simp] abbrev hd (out : Stage3Output f) : out.d > 0 := out.out2.hd

/-- Convenience lemma: the reduced step size is nonzero.

We intentionally delegate this to the Stage-2 boundary API lemma (`Stage2Output.d_ne_zero`), so
Stage 3 doesn't re-prove arithmetic facts about its projections.
-/
theorem d_ne_zero (out : Stage3Output f) : out.d ≠ 0 := by
  simpa [Stage3Output.d] using (Stage2Output.d_ne_zero (f := f) out.out2)

/-- Convenience lemma: the reduced step size is at least `1`.

We intentionally delegate this to the Stage-2 boundary API lemma (`Stage2Output.one_le_d`).
-/
theorem one_le_d (out : Stage3Output f) : 1 ≤ out.d := by
  simpa [Stage3Output.d] using (Stage2Output.one_le_d (f := f) out.out2)

end Stage3Output

end Tao2015

end MoltResearch
