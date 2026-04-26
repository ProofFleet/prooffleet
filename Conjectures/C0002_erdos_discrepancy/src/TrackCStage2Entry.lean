import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Stub

/-!
# Track C: Stage 2 entry point (Tao 2015 plane)

This file is **Conjectures-only** glue.

It contains only:
- the lightweight projections `stage2_d`, `stage2_g`, `stage2_m`, `stage2_start`, and
- the tiny projection lemmas `stage2_d_pos`, `stage2_one_le_d`, `stage2_d_ne_zero`,
  `stage2_start_eq_m_mul_d`, `stage2_d_dvd_start`, `stage2_start_mod_d`,
  `stage2_add_start_mod_d`, `stage2_start_add_mod_d`, `stage2_start_div_d`.

The reduced-sequence rewrite lemmas (`stage2_hg`, `stage2_g_eq`, `stage2_g_eq_fun`) are also
provided here (as tiny wrappers over the Stage-1 reduction fields bundled in `stage2Out`).

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
## Reduced sequence projection lemmas

These are tiny proved wrapper lemmas specialized to the deterministic reduced sequence `stage2_g`.
They are logically part of the Stage-1 reduction output bundled inside `stage2Out`, but they are
useful enough that we keep them in the entry-point module so downstream stages can consume them
without importing additional Stage-2 convenience layers.
-/

/-- The reduced sequence produced by Stage 2 is a sign sequence. -/
theorem stage2_hg (f : ℕ → ℤ) (hf : IsSignSequence f) :
    IsSignSequence (stage2_g (f := f) (hf := hf)) := by
  simpa [stage2_g] using (stage2Out (f := f) (hf := hf)).out1.hg

/-- Rewrite for the reduced sequence produced by Stage 2: it is a shift by `m*d`. -/
theorem stage2_g_eq (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    stage2_g (f := f) (hf := hf) k = f (k + stage2_start (f := f) (hf := hf)) := by
  -- This is just the Stage-1 reduction contract carried by the Stage-2 output.
  simpa [stage2_g, stage2_start, stage2_m, stage2_d] using
    (stage2Out (f := f) (hf := hf)).out1.g_eq k

/-- Function-level rewrite for `stage2_g`: it is the shifted sequence `fun k => f (k + m*d)`. -/
theorem stage2_g_eq_fun (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_g (f := f) (hf := hf) =
      fun k => f (k + stage2_start (f := f) (hf := hf)) := by
  funext k
  simpa using stage2_g_eq (f := f) (hf := hf) k

/-!
## Explicit-assumption variants

These are the non-typeclass analogues of the deterministic projections above, specialized to an
explicit `Stage2Assumption` instance `inst`.

They let downstream developments run the Stage-2 pipeline under a verified assumption without
introducing a local typeclass instance via `letI`.
-/

/-- Convenience projection: the reduced step size produced by Stage 2, under an explicit
assumption. -/
noncomputable abbrev stage2_dOf (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2OutOf inst (f := f) (hf := hf)).out1.d

/-- Convenience lemma: the reduced step size produced by Stage 2 (explicit assumption) is
positive. -/
theorem stage2_dOf_pos (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_dOf inst (f := f) (hf := hf) > 0 := by
  simpa [stage2_dOf] using (stage2OutOf inst (f := f) (hf := hf)).out1.hd

/-- Convenience lemma: the reduced step size produced by Stage 2 (explicit assumption) is at least
`1`. -/
theorem stage2_one_le_dOf (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    1 ≤ stage2_dOf inst (f := f) (hf := hf) := by
  exact Nat.succ_le_of_lt (stage2_dOf_pos (inst := inst) (f := f) (hf := hf))

/-- Convenience lemma: the reduced step size produced by Stage 2 (explicit assumption) is
nonzero. -/
theorem stage2_dOf_ne_zero (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_dOf inst (f := f) (hf := hf) ≠ 0 := by
  exact Nat.ne_of_gt (stage2_dOf_pos (inst := inst) (f := f) (hf := hf))

/-- Convenience projection: the reduced sequence produced by Stage 2, under an explicit
assumption. -/
noncomputable abbrev stage2_gOf (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ℕ → ℤ :=
  (stage2OutOf inst (f := f) (hf := hf)).out1.g

/-- Convenience projection: the bundled offset parameter produced by Stage 2, under an explicit
assumption. -/
noncomputable abbrev stage2_mOf (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2OutOf inst (f := f) (hf := hf)).out1.m

/-- Convenience projection: the affine-tail start index `m*d` under an explicit assumption. -/
noncomputable abbrev stage2_startOf (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ℕ :=
  stage2_mOf inst (f := f) (hf := hf) * stage2_dOf inst (f := f) (hf := hf)

/-- The explicit-assumption start index `stage2_startOf` is a multiple of the reduced step size
`stage2_dOf`.

This is the explicit-assumption analogue of `stage2_d_dvd_start`.
-/
theorem stage2_dOf_dvd_startOf (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_dOf inst (f := f) (hf := hf) ∣ stage2_startOf inst (f := f) (hf := hf) := by
  refine ⟨stage2_mOf inst (f := f) (hf := hf), ?_⟩
  -- `stage2_startOf` is definitionally `m*d`.
  simp [stage2_startOf, Nat.mul_comm]

/-- The explicit-assumption start index `stage2_startOf` has remainder `0` modulo `stage2_dOf`.

This is the explicit-assumption analogue of `stage2_start_mod_d`.
-/
theorem stage2_startOf_mod_d (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_startOf inst (f := f) (hf := hf) % stage2_dOf inst (f := f) (hf := hf) = 0 := by
  exact Nat.mod_eq_zero_of_dvd (stage2_dOf_dvd_startOf (inst := inst) (f := f) (hf := hf))

/-- Adding the explicit-assumption start index does not change residues modulo the step size.

Since `stage2_startOf` is a multiple of `stage2_dOf`, we have
`(n + stage2_startOf) % stage2_dOf = n % stage2_dOf`.
-/
theorem stage2_add_startOf_mod_d (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f)
    (n : ℕ) :
    (n + stage2_startOf inst (f := f) (hf := hf)) % stage2_dOf inst (f := f) (hf := hf) =
      n % stage2_dOf inst (f := f) (hf := hf) := by
  have hstart :
      stage2_startOf inst (f := f) (hf := hf) % stage2_dOf inst (f := f) (hf := hf) = 0 :=
    stage2_startOf_mod_d (inst := inst) (f := f) (hf := hf)
  simp [Nat.add_mod, hstart]

/-- Variant of `stage2_add_startOf_mod_d` with the start index on the left. -/
theorem stage2_startOf_add_mod_d (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f)
    (n : ℕ) :
    (stage2_startOf inst (f := f) (hf := hf) + n) % stage2_dOf inst (f := f) (hf := hf) =
      n % stage2_dOf inst (f := f) (hf := hf) := by
  simpa [Nat.add_comm] using
    stage2_add_startOf_mod_d (inst := inst) (f := f) (hf := hf) (n := n)

/-- Adding the explicit-assumption start index increases quotients by the offset parameter.

Since `stage2_startOf = stage2_mOf * stage2_dOf`, we have
`(n + stage2_startOf) / stage2_dOf = n / stage2_dOf + stage2_mOf`.
-/
theorem stage2_add_startOf_div_d (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f)
    (n : ℕ) :
    (n + stage2_startOf inst (f := f) (hf := hf)) / stage2_dOf inst (f := f) (hf := hf) =
      n / stage2_dOf inst (f := f) (hf := hf) + stage2_mOf inst (f := f) (hf := hf) := by
  have hd : 0 < stage2_dOf inst (f := f) (hf := hf) :=
    stage2_dOf_pos (inst := inst) (f := f) (hf := hf)
  simpa [stage2_startOf] using
    (Nat.add_mul_div_right (x := n) (y := stage2_mOf inst (f := f) (hf := hf))
      (z := stage2_dOf inst (f := f) (hf := hf)) hd)

/-- Variant of `stage2_add_startOf_div_d` with the start index on the left. -/
theorem stage2_startOf_add_div_d (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f)
    (n : ℕ) :
    (stage2_startOf inst (f := f) (hf := hf) + n) / stage2_dOf inst (f := f) (hf := hf) =
      n / stage2_dOf inst (f := f) (hf := hf) + stage2_mOf inst (f := f) (hf := hf) := by
  simpa [Nat.add_comm] using
    stage2_add_startOf_div_d (inst := inst) (f := f) (hf := hf) (n := n)

/-- Recover the offset parameter by dividing the explicit-assumption start index by the step size.
-/
theorem stage2_startOf_div_d (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_startOf inst (f := f) (hf := hf) / stage2_dOf inst (f := f) (hf := hf) =
      stage2_mOf inst (f := f) (hf := hf) := by
  have hd : 0 < stage2_dOf inst (f := f) (hf := hf) :=
    stage2_dOf_pos (inst := inst) (f := f) (hf := hf)
  simpa [stage2_startOf] using
    (Nat.mul_div_left (stage2_mOf inst (f := f) (hf := hf)) hd)

/-- The reduced sequence produced by Stage 2 (explicit assumption) is a sign sequence. -/
theorem stage2_hgOf (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    IsSignSequence (stage2_gOf inst (f := f) (hf := hf)) := by
  simpa [stage2_gOf] using (stage2OutOf inst (f := f) (hf := hf)).out1.hg

/-- Pointwise rewrite for the reduced sequence under an explicit assumption. -/
theorem stage2_gOf_eq (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    stage2_gOf inst (f := f) (hf := hf) k =
      f (k + stage2_startOf inst (f := f) (hf := hf)) := by
  simpa [stage2_gOf, stage2_startOf, stage2_mOf, stage2_dOf] using
    (stage2OutOf inst (f := f) (hf := hf)).out1.g_eq k

/-- Function-level rewrite for `stage2_gOf`. -/
theorem stage2_gOf_eq_fun (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_gOf inst (f := f) (hf := hf) =
      fun k => f (k + stage2_startOf inst (f := f) (hf := hf)) := by
  funext k
  simpa using stage2_gOf_eq (inst := inst) (f := f) (hf := hf) k

end Tao2015

end MoltResearch
