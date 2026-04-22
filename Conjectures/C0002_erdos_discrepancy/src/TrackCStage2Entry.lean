import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Stub

/-!
# Track C: Stage 2 entry point (Tao 2015 plane)

This file is **Conjectures-only** glue.

It contains only:
- the lightweight projections `stage2_d`, `stage2_g`, `stage2_m`, `stage2_start`, and
- the tiny projection lemmas `stage2_d_pos`, `stage2_one_le_d`, `stage2_d_ne_zero`,
  `stage2_start_eq_m_mul_d`, `stage2_d_dvd_start`, `stage2_start_mod_d`,
  `stage2_add_start_mod_d`, `stage2_start_add_mod_d`, `stage2_start_div_d`.

The reduced-sequence rewrite lemmas (`stage2_hg`, `stage2_g_eq`, `stage2_g_eq_fun`) live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2ProofCore`.

The conjecture stub itself (`stage2` and the deterministic name `stage2Out`) lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Stub`.

All other proved convenience lemmas about `stage2Out` live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Proof`.

Design goal: keep the Track-C hard-gate build (which imports Stage 3) from compiling additional
wrapper lemmas when it only needs the Stage-2 stub.
-/

namespace MoltResearch

namespace Tao2015

/-- Convenience projection: the reduced step size produced by Stage 2. -/
noncomputable abbrev stage2_d (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2Out (f := f) (hf := hf)).out1.d

/-- Convenience projection lemma: the reduced step size produced by Stage 2 is positive.

We keep this in the entry-point module because most consumers need the side condition `d > 0`,
and it is a zero-cost projection from the Stage-1 reduction output bundled in `stage2Out`.
-/
theorem stage2_d_pos (f : ℕ → ℤ) (hf : IsSignSequence f) : stage2_d (f := f) (hf := hf) > 0 := by
  simpa [stage2_d] using (stage2Out (f := f) (hf := hf)).out1.hd

/-- Convenience lemma: the reduced step size produced by Stage 2 is at least `1`. -/
theorem stage2_one_le_d (f : ℕ → ℤ) (hf : IsSignSequence f) : 1 ≤ stage2_d (f := f) (hf := hf) := by
  exact Nat.succ_le_of_lt (stage2_d_pos (f := f) (hf := hf))

/-- Convenience lemma: the reduced step size produced by Stage 2 is nonzero. -/
theorem stage2_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) : stage2_d (f := f) (hf := hf) ≠ 0 := by
  exact Nat.ne_of_gt (stage2_d_pos (f := f) (hf := hf))

/-- Convenience projection: the reduced sequence produced by Stage 2. -/
noncomputable abbrev stage2_g (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ → ℤ :=
  (stage2Out (f := f) (hf := hf)).out1.g

/-- Convenience projection: the bundled offset parameter produced by Stage 2. -/
noncomputable abbrev stage2_m (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2Out (f := f) (hf := hf)).out1.m

/-- Convenience projection: the affine-tail start index `m*d` bundled in Stage 1 and produced by
Stage 2.

We define this in the entry-point module so hard-gate consumers can use it without importing any
additional wrapper-lemma modules.
-/
noncomputable abbrev stage2_start (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  stage2_m (f := f) (hf := hf) * stage2_d (f := f) (hf := hf)

/-- Definitional rewrite: the Stage-2 start index is `m*d` for the deterministic parameters
produced by Stage 2.

This lemma is intentionally tiny (and not a simp lemma): it exists mainly to reduce `dsimp` noise
in downstream arithmetic rewrites.
-/
theorem stage2_start_eq_m_mul_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_start (f := f) (hf := hf) =
      stage2_m (f := f) (hf := hf) * stage2_d (f := f) (hf := hf) := by
  rfl

/-- The affine-tail start index `stage2_start` is a multiple of the reduced step size `stage2_d`. -/
theorem stage2_d_dvd_start (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_d (f := f) (hf := hf) ∣ stage2_start (f := f) (hf := hf) := by
  -- `stage2_start` is definitionally `m*d`.
  simp [stage2_start]

/-- The affine-tail start index `stage2_start` has remainder `0` when reduced modulo `stage2_d`.

This is often the most convenient form of `stage2_d_dvd_start` for arithmetic rewriting.
-/
theorem stage2_start_mod_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_start (f := f) (hf := hf) % stage2_d (f := f) (hf := hf) = 0 := by
  exact Nat.mod_eq_zero_of_dvd (stage2_d_dvd_start (f := f) (hf := hf))

/-- Adding the start index does not change residues modulo the step size.

Since `stage2_start` is a multiple of `stage2_d`, we have
`(n + stage2_start) % stage2_d = n % stage2_d`.
-/
theorem stage2_add_start_mod_d (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    (n + stage2_start (f := f) (hf := hf)) % stage2_d (f := f) (hf := hf) =
      n % stage2_d (f := f) (hf := hf) := by
  have hstart : stage2_start (f := f) (hf := hf) % stage2_d (f := f) (hf := hf) = 0 :=
    stage2_start_mod_d (f := f) (hf := hf)
  simp [Nat.add_mod, hstart]

/-- Variant of `stage2_add_start_mod_d` with the start index on the left. -/
theorem stage2_start_add_mod_d (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    (stage2_start (f := f) (hf := hf) + n) % stage2_d (f := f) (hf := hf) =
      n % stage2_d (f := f) (hf := hf) := by
  simpa [Nat.add_comm] using stage2_add_start_mod_d (f := f) (hf := hf) (n := n)

/-- Adding the start index increases quotients by the offset parameter.

Since `stage2_start = stage2_m * stage2_d`, we have
`(n + stage2_start) / stage2_d = n / stage2_d + stage2_m`.
-/
theorem stage2_add_start_div_d (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    (n + stage2_start (f := f) (hf := hf)) / stage2_d (f := f) (hf := hf) =
      n / stage2_d (f := f) (hf := hf) + stage2_m (f := f) (hf := hf) := by
  have hd : 0 < stage2_d (f := f) (hf := hf) := stage2_d_pos (f := f) (hf := hf)
  simpa [stage2_start] using
    (Nat.add_mul_div_right (x := n) (y := stage2_m (f := f) (hf := hf))
      (z := stage2_d (f := f) (hf := hf)) hd)

/-- Variant of `stage2_add_start_div_d` with the start index on the left. -/
theorem stage2_start_add_div_d (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    (stage2_start (f := f) (hf := hf) + n) / stage2_d (f := f) (hf := hf) =
      n / stage2_d (f := f) (hf := hf) + stage2_m (f := f) (hf := hf) := by
  simpa [Nat.add_comm] using stage2_add_start_div_d (f := f) (hf := hf) (n := n)

/-- Recover the offset parameter `stage2_m` by dividing the Stage-2 start index `stage2_start`
by the reduced step size `stage2_d`.

This is a tiny arithmetic convenience lemma: `stage2_start = stage2_m * stage2_d` by definition.
-/
theorem stage2_start_div_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_start (f := f) (hf := hf) / stage2_d (f := f) (hf := hf) =
      stage2_m (f := f) (hf := hf) := by
  have hd : 0 < stage2_d (f := f) (hf := hf) := stage2_d_pos (f := f) (hf := hf)
  simpa [stage2_start] using (Nat.mul_div_left (stage2_m (f := f) (hf := hf)) hd)

/-!
The remaining proved projection lemmas about the reduced sequence `stage2_g` live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2ProofCore`.

We keep this entry-point module focused on deterministic parameter/projection definitions and
small arithmetic facts about `stage2_start`.
-/

end Tao2015

end MoltResearch
