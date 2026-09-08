import Conjectures.C0005_erdos177_ap.src.Reduction
import Mathlib.Order.KonigLemma

/-!
# Erdős 177: compactness for residue-prefix witnesses

This file discharges the compactness interface from `Reduction.lean`.  A finite witness is encoded
by a Boolean string.  Restriction makes the valid strings into an inverse system of finite types,
and Kőnig's infinity lemma supplies a coherent string at every horizon.  Reading the coherent
strings coordinatewise gives one infinite sign sequence.  Every residue-prefix constraint is
already decided at its finite endpoint, so the passage introduces no horizon-dependent loss.
-/

namespace MoltResearch

namespace Erdos177Compactness

/-- Interpret a Boolean as one of the two integer signs. -/
private def bitSign (b : Bool) : ℤ :=
  if b then 1 else -1

/-- Extend a finite Boolean string to an integer-valued sequence.  Values beyond the string are
irrelevant to a finite witness and are filled with `1`. -/
private def bitExtension {N : ℕ} (g : Fin N → Bool) (n : ℕ) : ℤ :=
  if hn : n < N then bitSign (g ⟨n, hn⟩) else 1

/-- A witness only depends on the values strictly below its ambient horizon. -/
private theorem finiteResiduePrefixWitness_congr {f g : ℕ → ℤ} {α C : ℝ} {N : ℕ}
    (hfg : ∀ n, n < N → f n = g n)
    (hf : FiniteResiduePrefixWitness f α C N) :
    FiniteResiduePrefixWitness g α C N := by
  constructor
  · intro n hn
    rw [← hfg n hn]
    exact hf.1 n hn
  · intro d r M hd hr hend
    have hsum : residuePrefixSum f d r M = residuePrefixSum g d r M := by
      unfold residuePrefixSum
      apply Finset.sum_congr rfl
      intro j hj
      apply hfg
      exact lt_of_lt_of_le
        (Nat.add_lt_add_left
          (Nat.mul_lt_mul_of_pos_right (Finset.mem_range.mp hj) hd) r)
        hend
    rw [← hsum]
    exact hf.2 d r M hd hr hend

/-- Restricting the ambient horizon preserves validity. -/
private theorem finiteResiduePrefixWitness_mono {f : ℕ → ℤ} {α C : ℝ} {i j : ℕ}
    (hij : i ≤ j) (hf : FiniteResiduePrefixWitness f α C j) :
    FiniteResiduePrefixWitness f α C i := by
  constructor
  · intro n hn
    exact hf.1 n (lt_of_lt_of_le hn hij)
  · intro d r M hd hr hend
    exact hf.2 d r M hd hr (hend.trans hij)

/-- Boolean strings whose canonical extensions are valid finite witnesses. -/
private abbrev ValidBits (α C : ℝ) (N : ℕ) :=
  {g : Fin N → Bool // FiniteResiduePrefixWitness (bitExtension g) α C N}

/-- Restriction of a finite Boolean string along an inequality of horizons. -/
private def restrictBits {i j : ℕ} (hij : i ≤ j) (g : Fin j → Bool) : Fin i → Bool :=
  fun n => g ⟨n, lt_of_lt_of_le n.isLt hij⟩

private theorem bitExtension_restrictBits {i j : ℕ} (hij : i ≤ j) (g : Fin j → Bool)
    {n : ℕ} (hn : n < i) :
    bitExtension (restrictBits hij g) n = bitExtension g n := by
  simp [bitExtension, restrictBits, hn, lt_of_lt_of_le hn hij]

/-- Restrict a valid string, retaining its finite-witness proof. -/
private def validBitsRestrict {α C : ℝ} {i j : ℕ} (hij : i ≤ j)
    (g : ValidBits α C j) : ValidBits α C i :=
  ⟨restrictBits hij g.1,
    finiteResiduePrefixWitness_congr
      (fun _ hn => (bitExtension_restrictBits hij g.1 hn).symm)
      (finiteResiduePrefixWitness_mono hij g.2)⟩

/-- Every finite integer-valued witness has an equivalent Boolean encoding. -/
private theorem validBits_nonempty {α C : ℝ} {N : ℕ}
    (hN : ∃ f : ℕ → ℤ, FiniteResiduePrefixWitness f α C N) :
    Nonempty (ValidBits α C N) := by
  obtain ⟨f, hf⟩ := hN
  let g : Fin N → Bool := fun n => if f n = 1 then true else false
  refine ⟨⟨g, finiteResiduePrefixWitness_congr (g := bitExtension g) ?_ hf⟩⟩
  intro n hn
  rcases hf.1 n hn with h | h
  · simp [bitExtension, bitSign, g, hn, h]
  · simp [bitExtension, bitSign, g, hn, h]

/-- Uniform finite feasibility yields a single infinite sign sequence satisfying every
residue-prefix bound with exactly the same constant. -/
theorem residuePrefixCompactness (α C : ℝ)
    (hwitnesses : ∀ N : ℕ, ∃ f : ℕ → ℤ, FiniteResiduePrefixWitness f α C N) :
    ∃ f : ℕ → ℤ, IsSignSequence f ∧ ResiduePrefixBoundedBy f α C := by
  letI (N : ℕ) : Nonempty (ValidBits α C N) := validBits_nonempty (hwitnesses N)
  let π : {i j : ℕ} → (hij : i ≤ j) → ValidBits α C j → ValidBits α C i :=
    fun {_ _} hij => validBitsRestrict hij
  have hπrefl : ∀ ⦃i⦄ (a : ValidBits α C i), π (le_refl i) a = a := by
    intro i a
    apply Subtype.ext
    funext n
    rfl
  have hπtrans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) (a : ValidBits α C k),
      π hij (π hjk a) = π (hij.trans hjk) a := by
    intro i j k hij hjk a
    apply Subtype.ext
    funext n
    rfl
  have hπfinite : ∀ i (a : ValidBits α C i),
      {b : ValidBits α C (i + 1) | π (Nat.le_add_right i 1) b = a}.Finite := by
    intro i a
    exact Set.toFinite _
  obtain ⟨g, hg⟩ :=
    exists_seq_forall_proj_of_forall_finite π hπrefl hπtrans hπfinite
  let f : ℕ → ℤ := fun n => bitSign ((g (n + 1)).1 ⟨n, Nat.lt_succ_self n⟩)
  have hf_agrees : ∀ N n : ℕ, n < N → f n = bitExtension (g N).1 n := by
    intro N n hn
    have hle : n + 1 ≤ N := Nat.succ_le_iff.mpr hn
    have hcoherent := congr_arg Subtype.val (hg hle)
    have hbit := congr_fun hcoherent ⟨n, Nat.lt_succ_self n⟩
    change bitSign ((g (n + 1)).1 ⟨n, Nat.lt_succ_self n⟩) = _
    rw [← hbit]
    simp [π, validBitsRestrict, restrictBits, bitExtension, hn]
  refine ⟨f, ?_, ?_⟩
  · intro n
    simp only [f, bitSign]
    split <;> simp
  · intro d r M hd hr
    let N := r + M * d
    have hfinite := (g N).2.2 d r M hd hr (le_refl N)
    have hsum : residuePrefixSum f d r M = residuePrefixSum (bitExtension (g N).1) d r M := by
      unfold residuePrefixSum
      apply Finset.sum_congr rfl
      intro j hj
      apply hf_agrees N
      exact Nat.add_lt_add_left
        (Nat.mul_lt_mul_of_pos_right (Finset.mem_range.mp hj) hd) r
    rw [hsum]
    exact hfinite

end Erdos177Compactness

/-- The compactness node in the Erdős 177 reduction is unconditional. -/
instance residuePrefixCompactnessAssumption (α : ℝ) :
    ResiduePrefixCompactnessAssumption α where
  limit C _hC hwitnesses := Erdos177Compactness.residuePrefixCompactness α C hwitnesses

/--
info: 'MoltResearch.residuePrefixCompactnessAssumption' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms residuePrefixCompactnessAssumption

end MoltResearch
