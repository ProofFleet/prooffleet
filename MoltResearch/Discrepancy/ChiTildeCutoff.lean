import MoltResearch.Discrepancy.AlmostOrthogonality
import MoltResearch.Discrepancy.PretentiousFactorization

/-!
# Discrepancy: `χ̃` as a divisor-cutoff combination

Endgame step for the Tao 2015 §4 analysis (arXiv:1509.05363,
`Problems/tao2015_derivation_c.md`, issue #2871): the bridge between the good-residue
window moments of the completion `χ̃ = chiTilde g q χ t` and the divisor-cutoff
combination fed to the almost-orthogonality expansion.

The combination `n ↦ ∑_{d ∣ qʲ} χ̃(d)·charCutoff χ d n` has at most one nonzero term, at
`d = gcd(n, qʲ)`: for any other contributing divisor `d`, a prime `p ∣ q` survives inside
the cofactor `n/d`, where `χ` vanishes (`sum_divisors_chiTilde_charCutoff_eq`).
Consequences (at `j = k − 1`):

* `sum_divisors_chiTilde_charCutoff_of_good`: on a good residue class
  (`IsGoodResidue q k H a`, window `m ∈ [1, 2H]`) the combination **equals** `χ̃(a+m)` —
  the gcd with `q^k` already divides `q^{k−1}` (`gcd_dvd_pow_pred_of_good`), the cofactor
  is coprime to `q` (`coprime_div_gcd_of_good`), and `χ̃ = χ` on coprimes
  (`chiTilde_apply_of_coprime`).
* `norm_sum_divisors_chiTilde_charCutoff_le`: everywhere (bad residues included) the
  combination is `1`-bounded — the price of reinstating the bad residues.
-/

namespace MoltResearch

open Finset

variable {g : ℕ → ℂ} {q : ℕ} {χ : DirichletCharacter ℂ q} {t : ℝ}

/-- If `d ∣ e ∣ qʲ` with `d ≠ e` and `e ∣ n`, a prime of `e/d` divides both `q` and
`n/d`, so `χ(n/d) = 0`.  The uniqueness engine behind the collapse. -/
private lemma char_div_eq_zero_of_proper_dvd {j d e n : ℕ} (hq : q ≠ 0) (hd0 : d ≠ 0)
    (hde : d ∣ e) (hne : d ≠ e) (hej : e ∣ q ^ j) (hen : e ∣ n) :
    χ ((n / d : ℕ) : ZMod q) = 0 := by
  have he0 : e ≠ 0 := ne_zero_of_dvd_ne_zero (pow_ne_zero j hq) hej
  obtain ⟨c, hc⟩ := hde
  have hc0 : c ≠ 0 := by rintro rfl; exact he0 (by simpa using hc)
  have hc1 : c ≠ 1 := by rintro rfl; exact hne (by simpa using hc.symm)
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd hc1
  have hpe : p ∣ e := hpc.trans ⟨d, by rw [hc, Nat.mul_comm]⟩
  have hpq : p ∣ q := hp.dvd_of_dvd_pow (hpe.trans hej)
  obtain ⟨x, hx⟩ := hen
  have hnd : n / d = c * x := by
    rw [hx, hc, mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  have hpnd : p ∣ n / d := hnd ▸ (hpc.mul_right x)
  have hnu : ¬ IsUnit (((n / d : ℕ)) : ZMod q) := by
    intro hunit
    have hcop : Nat.Coprime (n / d) q := (ZMod.isUnit_iff_coprime _ _).mp hunit
    have h1 : p ∣ Nat.gcd (n / d) q := Nat.dvd_gcd hpnd hpq
    rw [Nat.Coprime] at hcop
    rw [hcop] at h1
    exact absurd (Nat.eq_one_of_dvd_one h1) hp.ne_one
  exact χ.map_nonunit hnu

/-- **Collapse of the divisor-cutoff combination** (Tao 2015 §4 endgame): the sum
`∑_{d ∣ qʲ} χ̃(d)·1_{d ∣ n}·χ(n/d)` has at most one nonzero term, at `d = gcd(n, qʲ)`. -/
theorem sum_divisors_chiTilde_charCutoff_eq (hq : q ≠ 0) (j n : ℕ) :
    ∑ d ∈ (q ^ j).divisors, chiTilde g q χ t d * charCutoff χ d n
      = chiTilde g q χ t (Nat.gcd n (q ^ j)) * charCutoff χ (Nat.gcd n (q ^ j)) n := by
  have hqj : q ^ j ≠ 0 := pow_ne_zero j hq
  have hemem : Nat.gcd n (q ^ j) ∈ (q ^ j).divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hqj⟩
  refine Finset.sum_eq_single_of_mem _ hemem fun d hd hne => ?_
  have hdq : d ∣ q ^ j := (Nat.mem_divisors.mp hd).1
  have hd0 : d ≠ 0 := by
    intro h; rw [h] at hdq; exact hqj (Nat.eq_zero_of_zero_dvd hdq)
  by_cases hdn : d ∣ n
  · rw [charCutoff_of_dvd hdn,
      char_div_eq_zero_of_proper_dvd hq hd0 (Nat.dvd_gcd hdn hdq) hne
        (Nat.gcd_dvd_right n (q ^ j)) (Nat.gcd_dvd_left n (q ^ j)), mul_zero]
  · rw [charCutoff_of_not_dvd hdn, mul_zero]

/-- **`χ̃` is its own divisor-cutoff combination on good residue classes** (Tao 2015 §4
endgame, eq. (contra) → (stop)): on a good class the gcd with `q^k` divides `q^{k−1}` and
the cofactor is coprime to `q`, so the collapse reconstructs `χ̃(a+m)` exactly. -/
theorem sum_divisors_chiTilde_charCutoff_of_good {k H a : ℕ} (hq : q ≠ 0)
    (hgood : IsGoodResidue q k H a) {m : ℕ} (hm : m ∈ Finset.Icc 1 (2 * H)) :
    ∑ d ∈ (q ^ (k - 1)).divisors, chiTilde g q χ t d * charCutoff χ d (a + m)
      = chiTilde g q χ t (a + m) := by
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hn0 : a + m ≠ 0 := by omega
  have hs : Nat.gcd (a + m) (q ^ k) ∣ q ^ (k - 1) := gcd_dvd_pow_pred_of_good hq hgood hm
  have hcop : Nat.Coprime ((a + m) / Nat.gcd (a + m) (q ^ k)) q :=
    coprime_div_gcd_of_good hq hgood hm
  have hse : Nat.gcd (a + m) (q ^ (k - 1)) = Nat.gcd (a + m) (q ^ k) := by
    refine Nat.dvd_antisymm ?_ ?_
    · exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
        ((Nat.gcd_dvd_right _ _).trans (pow_dvd_pow q (Nat.sub_le k 1)))
    · exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hs
  rw [sum_divisors_chiTilde_charCutoff_eq hq (k - 1) (a + m), hse]
  have hsn : Nat.gcd (a + m) (q ^ k) ∣ a + m := Nat.gcd_dvd_left _ _
  have hs0 : Nat.gcd (a + m) (q ^ k) ≠ 0 := Nat.gcd_ne_zero_left hn0
  have hdiv0 : (a + m) / Nat.gcd (a + m) (q ^ k) ≠ 0 := by
    have h1 : 1 ≤ (a + m) / Nat.gcd (a + m) (q ^ k) :=
      (Nat.one_le_div_iff (Nat.pos_of_ne_zero hs0)).mpr (Nat.le_of_dvd (by omega) hsn)
    omega
  rw [charCutoff_of_dvd hsn, ← chiTilde_apply_of_coprime hdiv0 hcop,
    ← chiTilde_completelyMultiplicativeC _ _ hs0 hdiv0, Nat.mul_div_cancel' hsn]

/-- The divisor-cutoff combination is `1`-bounded everywhere (Tao 2015 §4 endgame,
"we reinstate the bad `a`"): the unique surviving term is unimodular-times-character. -/
theorem norm_sum_divisors_chiTilde_charCutoff_le (hu : Unimodular g) (hq : q ≠ 0)
    (j n : ℕ) :
    ‖∑ d ∈ (q ^ j).divisors, chiTilde g q χ t d * charCutoff χ d n‖ ≤ 1 := by
  rw [sum_divisors_chiTilde_charCutoff_eq hq j n, norm_mul,
    chiTilde_unimodular hu _, one_mul]
  exact norm_charCutoff_le _ _

end MoltResearch
