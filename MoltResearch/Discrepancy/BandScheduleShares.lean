import MoltResearch.Discrepancy.BandSchedule

/-!
# Geometric shares for the inner-band schedule (Track R, A2-III, VI-8e)

The inner-band assembly asks for three shares at every ordinary level and for
per-cell shares on every later level.  This file fixes both choices.  Each of
the main, replacement, and collision legs receives `3/64` of the geometric
level share `2^{-(j+1)}`.  Under `S1`'s `3H ≤ A`, the assembly's window
factor `(4H/A)²` then leaves a factor two of slack.

Within a level, the main share is split geometrically by the absolute cell
index.  Summing over any `Ico` costs at most the full geometric series, so no
cell-count denominator or nonemptiness side condition is needed.
-/

namespace MoltResearch

/-- The share assigned to one of the three ordinary legs at level `j`. -/
noncomputable def ordinaryLegShare (j : ℕ) : ℝ :=
  3 / (64 * 2 ^ (j + 1) : ℝ)

/-- A geometric subdivision of a budget `κ` by absolute cell index. -/
noncomputable def geometricCellShare (κ : ℝ) (r : ℕ) : ℝ :=
  κ / 2 ^ (r + 1)

/-- Any interval of geometric cell shares sums to at most its parent share. -/
theorem sum_geometricCellShare_Ico_le (v₀ v₁ : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∑ r ∈ Finset.Ico v₀ (v₁ + 1), geometricCellShare κ r ≤ κ := by
  have hsub : Finset.Ico v₀ (v₁ + 1) ⊆ Finset.range (v₁ + 1) := by
    intro r hr
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hr).2
  have hterm : ∀ r : ℕ, 0 ≤ geometricCellShare κ r := fun r => by
    unfold geometricCellShare
    positivity
  calc
    ∑ r ∈ Finset.Ico v₀ (v₁ + 1), geometricCellShare κ r
        ≤ ∑ r ∈ Finset.range (v₁ + 1), geometricCellShare κ r :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => hterm r)
    _ = κ * ∑ r ∈ Finset.range (v₁ + 1), (1 : ℝ) / 2 ^ (r + 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by
        unfold geometricCellShare
        ring
    _ ≤ κ * 1 := mul_le_mul_of_nonneg_left (geometric_shares_le_one _) hκ
    _ = κ := mul_one _

/-- `S1` makes the three ordinary-leg shares fit the weighted level share. -/
theorem ordinaryLegShares_fit (A H j : ℕ) (hA : 0 < A) (hHA : 3 * H ≤ A) :
    (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (2 * ordinaryLegShare j + 2 * ordinaryLegShare j +
          2 * ordinaryLegShare j)
      ≤ (1 : ℝ) / 2 ^ (j + 1) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hHA' : (3 : ℝ) * (H : ℝ) ≤ (A : ℝ) := by exact_mod_cast hHA
  have hratio : 4 * (H : ℝ) / (A : ℝ) ≤ 4 / 3 := by
    rw [div_le_div_iff₀ hA0 (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  have hratio0 : 0 ≤ 4 * (H : ℝ) / (A : ℝ) := by positivity
  have hsq : (4 * (H : ℝ) / (A : ℝ)) ^ 2 ≤ (4 / 3 : ℝ) ^ 2 := by
    nlinarith
  have hpow : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  unfold ordinaryLegShare
  calc
    (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * (2 * (3 / (64 * 2 ^ (j + 1) : ℝ)) +
            2 * (3 / (64 * 2 ^ (j + 1) : ℝ)) +
            2 * (3 / (64 * 2 ^ (j + 1) : ℝ)))
        ≤ (4 / 3 : ℝ) ^ 2
          * (2 * (3 / (64 * 2 ^ (j + 1) : ℝ)) +
            2 * (3 / (64 * 2 ^ (j + 1) : ℝ)) +
            2 * (3 / (64 * 2 ^ (j + 1) : ℝ))) := by
      gcongr
    _ ≤ (1 : ℝ) / 2 ^ (j + 1) := by
      field_simp
      norm_num

end MoltResearch
