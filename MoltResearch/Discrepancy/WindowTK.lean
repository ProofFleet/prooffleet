/-
# Window Turán–Kubilius substrate (Track R, A2-III, N3-h)

The in-tree Turán–Kubilius and sift bounds (`TuranKubilius.lean`,
`TypicalFactorization.lean`) run on the global range `Ico 1 N`.  The
band-energy schedule prices the atypical complement *per block*
`(A, A+Δ]`, so it needs the first/second prime moments and the sifted
log-average on a window — with errors measured against the window
harmonic mass, not `log N`.

This file builds that substrate from the exact fibre reindex: the
`d`-multiples of a window are the dilated quotient window, so every
moment computation reduces to comparing harmonic masses of quotient
windows.
-/
import MoltResearch.Discrepancy.TuranKubilius
import MoltResearch.Discrepancy.RamareIdentity

namespace MoltResearch

open Finset

/-- **The window divisibility reindex, exactly** (Track R, A2-III,
N3-h0): the harmonic mass of the `d`-multiples in a window is `1/d`
times the harmonic mass of the quotient window — an identity, no
error term.  Every window moment computation reduces to this. -/
theorem sum_one_div_Ioc_dvd_eq (A B d : ℕ) (hd : 0 < d) :
    ∑ n ∈ (Finset.Ioc A B).filter (fun n => d ∣ n), (1:ℝ)/n
      = (1/(d:ℝ)) * ∑ k ∈ Finset.Ioc (A/d) (B/d), (1:ℝ)/k := by
  classical
  rw [sum_filter_dvd_eq_sum_image (Finset.Ioc A B) hd (fun n => (1:ℝ)/n)]
  have himg : ((Finset.Ioc A B).filter (fun n => d ∣ n)).image (· / d)
      = Finset.Ioc (A/d) (B/d) := by
    refine le_antisymm
      (image_div_fibre_subset A B (Finset.Ioc A B)
        (Finset.Subset.refl _) hd) ?_
    intro k hk
    rw [Finset.mem_Ioc] at hk
    rw [Finset.mem_image]
    refine ⟨d*k, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Ioc]
      have h1 : A < k * d := (Nat.div_lt_iff_lt_mul hd).mp hk.1
      have h2 : k * d ≤ B := (Nat.le_div_iff_mul_le hd).mp hk.2
      refine ⟨⟨?_, ?_⟩, ⟨k, rfl⟩⟩
      · rw [mul_comm d k]
        exact h1
      · rw [mul_comm d k]
        exact h2
    · rw [Nat.mul_div_cancel_left k hd]
  rw [himg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Ioc] at hk
  have hk0 : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hk.1
  have hkc : ((k:ℝ)) ≠ 0 := by exact_mod_cast hk0.ne'
  have hdc : ((d:ℝ)) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp

end MoltResearch
