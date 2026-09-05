import MoltResearch.Discrepancy.MajorArcAssembly
import MoltResearch.Discrepancy.WindowAssembly

/-!
# Track R: the twisted non-pretentiousness at every block scale (R6-8a)

The A.2 input of `sum_restricted_window_logavg_le_of_meanSquare` is demanded, for every
divisor `d ∣ q` and every character `χ` mod `q/d`, on dyadic blocks `(A', A'+J]` with
`⌊A/q⌋ ≤ A'+1` and `A' + J ≤ 3A`; each such application needs the twist `χ·g` to be
non-pretentious at truncation `2A'+1`.  This leaf produces all of those from **one**
hypothesis on `g` — strength `q·A₀ + 26`, truncation `6A+1` — by the downward scale
transfer of `WindowAssembly` (`nonPretentiousAt_scale_transfer`, priced by
`mertens_mass_diff_le`) followed by the character twist of `MajorArcAssembly`
(`nonPretentiousAt_charMul`).  It is kept out of `MajorArcAssembly` so that module stays
below the window harness in the import graph.
-/

namespace MoltResearch

open ExpSums

/-- **The twist is non-pretentious at every block scale** (Track R, R6-8a).

Let `g` be unimodular and non-pretentious at strength `q·A₀ + 26` and truncation `6A+1`,
with `7q² ≤ A`.  Then for every `d ∣ q`, every character `χ` mod `q/d`, and every block
start `A'` with `⌊A/q⌋ ≤ A'+1` and `A' ≤ 3A`, the twist `χ·g` is non-pretentious at
strength `A₀` and truncation `2A'+1`.  The truncation is moved down from `6A+1` to
`2A'+1 ≥ ⌊A/q⌋` at the Mertens cost `2·(loglog(6A+1) − loglog(2A'+1) + 12)`
(`nonPretentiousAt_scale_transfer`, `mertens_mass_diff_le`), which is at most `26`
because `(2A'+1)² ≥ ⌊A/q⌋² ≥ 6A+1`; then `nonPretentiousAt_charMul` trades the factor
`q/d ≤ q` in strength.  This is the shape in which the wrapper hands the interface's
single non-pretentiousness hypothesis to the A.2 input of every class and character. -/
theorem nonPretentiousAt_charMul_of_block (g : ℕ → ℂ) (hgu : Unimodular g) {A₀ : ℝ}
    (hA₀ : 0 ≤ A₀) {q : ℕ} (hq : 0 < q) {d : ℕ} (hd0 : 0 < d) (hdq : d ∣ q)
    (χ : DirichletCharacter ℂ (q / d)) (A A' : ℕ) (hA7 : 7 * q ^ 2 ≤ A)
    (hA'lo : A / q ≤ A' + 1) (hA'hi : A' ≤ 3 * A)
    (hnp : NonPretentiousAt g (q * A₀ + 26) (6 * A + 1)) :
    NonPretentiousAt (fun n => χ n * g n) A₀ (2 * A' + 1) := by
  have hq₀ : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
  have hq₀le : q / d ≤ q := Nat.div_le_self q d
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  -- `⌊A/q⌋ ≥ 7q`, hence `2A'+1 ≥ ⌊A/q⌋ ≥ 7q ≥ 7` and `⌊A/q⌋² ≥ 6A+1`
  have hAq7 : 7 * q ≤ A / q := (Nat.le_div_iff_mul_le hq).mpr (by nlinarith)
  have hA'2 : 4 ≤ 2 * A' + 1 := by omega
  have hsq : 6 * A + 1 ≤ (A / q) * (A / q) := by
    have hmod := Nat.div_add_mod A q
    have hlt := Nat.mod_lt A hq
    have h1 : 7 * (q * (A / q)) ≤ (A / q) * (A / q) := by
      have := Nat.mul_le_mul_right (A / q) hAq7
      linarith [this]
    have h2 : A + 1 ≤ q * (A / q) + q := by omega
    nlinarith
  have hu : A / q ≤ 2 * A' + 1 := by omega
  -- the Mertens cost of moving the truncation down is at most `26`
  have hmass : (∑ p ∈ (6 * A + 1).primesBelow, (1:ℝ)/p)
      - (∑ p ∈ (2 * A' + 1).primesBelow, (1:ℝ)/p) ≤ 13 := by
    have hle : 2 * A' + 1 ≤ 6 * A + 1 := by omega
    have hmd := mertens_mass_diff_le (2 * A' + 1) (6 * A + 1) hA'2 hle
    have huR : (4:ℝ) ≤ ((2 * A' + 1 : ℕ) : ℝ) := by exact_mod_cast hA'2
    have h6R : ((6 * A + 1 : ℕ) : ℝ) ≤ ((2 * A' + 1 : ℕ) : ℝ) ^ 2 := by
      have h1 : 6 * A + 1 ≤ (2 * A' + 1) * (2 * A' + 1) :=
        le_trans hsq (Nat.mul_le_mul hu hu)
      have h2 : ((6 * A + 1 : ℕ) : ℝ) ≤ (((2 * A' + 1) * (2 * A' + 1) : ℕ) : ℝ) := by
        exact_mod_cast h1
      rw [sq]
      push_cast at h2 ⊢
      exact h2
    have hlogu : 0 < Real.log ((2 * A' + 1 : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hlog6 : Real.log ((6 * A + 1 : ℕ) : ℝ) ≤ Real.exp 1 * Real.log ((2 * A' + 1 : ℕ) : ℝ) := by
      calc Real.log ((6 * A + 1 : ℕ) : ℝ)
          ≤ Real.log (((2 * A' + 1 : ℕ) : ℝ) ^ 2) := Real.log_le_log (by positivity) h6R
        _ = 2 * Real.log ((2 * A' + 1 : ℕ) : ℝ) := by rw [Real.log_pow]; push_cast; ring
        _ ≤ Real.exp 1 * Real.log ((2 * A' + 1 : ℕ) : ℝ) := by
            have : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
            exact mul_le_mul_of_nonneg_right this hlogu.le
    have hloglog : Real.log (Real.log ((6 * A + 1 : ℕ) : ℝ))
        ≤ 1 + Real.log (Real.log ((2 * A' + 1 : ℕ) : ℝ)) := by
      have hpos6 : 0 < Real.log ((6 * A + 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < 6 * A + 1))
      calc Real.log (Real.log ((6 * A + 1 : ℕ) : ℝ))
          ≤ Real.log (Real.exp 1 * Real.log ((2 * A' + 1 : ℕ) : ℝ)) :=
            Real.log_le_log hpos6 hlog6
        _ = 1 + Real.log (Real.log ((2 * A' + 1 : ℕ) : ℝ)) := by
            rw [Real.log_mul (Real.exp_ne_zero 1) hlogu.ne', Real.log_exp]
    linarith
  -- move the truncation down at strength `q·A₀`
  have hdown : NonPretentiousAt g (q * A₀) (2 * A' + 1) := by
    refine nonPretentiousAt_scale_transfer (fun p => (hgu p).le) hnp (by omega)
      (by positivity) ?_
    linarith
  -- and twist
  refine nonPretentiousAt_charMul g hdown hq₀ χ hA₀ ?_
  have : ((q / d : ℕ) : ℝ) ≤ q := by exact_mod_cast hq₀le
  calc A₀ * ((q / d : ℕ) : ℝ) ≤ A₀ * q := mul_le_mul_of_nonneg_left this hA₀
    _ = q * A₀ := mul_comm _ _

end MoltResearch
