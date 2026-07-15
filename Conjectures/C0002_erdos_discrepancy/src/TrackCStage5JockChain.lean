import MoltResearch.Discrepancy
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5VanDerCorput
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5JockHelpers

/-!
# Track C: Stage 5 — the (jock) → (contra) chain (Tao 2015 §4, deterministic core)

Conjectures-layer assembly for issue #2871 (`Problems/tao2015_derivation_c.md`): from the
per-sample data handed over by Proposition 1.11 (after the `𝐭`-cut, conductor reduction and
the eq.-(dos) factorization `g = χ̃·n^{i𝐭}·h`), derive the paper's estimate `(contra)`:

`(1/q^k) ∑_{a good} (1/H) ∑_{H < H' ≤ 2H} |∑_{m ≤ H'} χ̃(a+m)|² ≪_ε 1`.

The route (arXiv:1509.05363 §4, between eq. (jock) and eq. (contra)):
residue-class restriction and Cauchy–Schwarz for the zeta-weighted windows, the Maier
rigidity `χ̃(n+m) = χ̃(a+m)` on good classes, the `n ↦ n+m` shift, the equidistribution of
`h` in residue classes mod `q^k` (character orthogonality: principal term = singular series
times explicit Euler factors, non-principal terms subexponential), and the two-sided
singular-series bound `exp(−(20+B₂))·log X ≤ ‖𝔖‖ ≤ 2 + log X`.

All constants are explicit and, crucially, **`H`-free** in the coefficient of the main
term: the `(1/H)`-averaged window hypothesis produces the `(contra)` constant
`8·exp(2(20+B₂))·D + 1`, with every `H`-dependent error killed by the `X → ∞` threshold
(which is uniform in the sample `g`, the character `χ` and the frequency `𝐭` — only
`(q, k, H, D, B₂)` enter).
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-! ### Small preliminaries -/

/-- Uniform (classical) decidable equality for character types, so that `Finset.erase`
elaborates with one and the same instance in every statement and proof of this file. -/
private noncomputable instance (N : ℕ) : DecidableEq (DirichletCharacter ℂ N) :=
  Classical.decEq _

private lemma one_lt_log_of_three_le' {X : ℝ} (hX : 3 ≤ X) : 1 < Real.log X := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    _ ≤ Real.log X := Real.log_le_log (by norm_num) hX

/-- A guarded completely multiplicative function equal to `1` at every prime divisor of
`q` is `1` at every `d` all of whose prime factors divide `q` (`d ≠ 0`). -/
private lemma cm_eq_one_of_primes_dvd {h : ℕ → ℂ} (hmul : CompletelyMultiplicativeC h)
    (h1 : h 1 = 1) {q : ℕ} (hp1 : ∀ p : ℕ, p.Prime → p ∣ q → h p = 1)
    {d : ℕ} (hd0 : d ≠ 0) (hdq : ∀ p : ℕ, p.Prime → p ∣ d → p ∣ q) : h d = 1 := by
  rw [hmul.eq_prod_factorization h1 hd0]
  rw [Finsupp.prod]
  refine Finset.prod_eq_one fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [← Nat.support_factorization])
  have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors (by rwa [← Nat.support_factorization])
  rw [hp1 p hpp (hdq p hpp hpd), one_pow]

/-- At level `q = 1` the completion `χ̃` is identically `1` away from `0` (the degenerate
Borwein–Choi–Coons case: `ZMod 1` is trivial, every character value is `1`). -/
private lemma chiTilde_eq_one_of_level_one {g : ℕ → ℂ} (χ : DirichletCharacter ℂ 1)
    (t : ℝ) {u : ℕ} (hu : u ≠ 0) : chiTilde g 1 χ t u = 1 := by
  have hcm1 : CompletelyMultiplicativeC (fun _ : ℕ => (1 : ℂ)) := by
    intro a b _ _
    simp
  have hprime : ∀ p : ℕ, p.Prime → chiTilde g 1 χ t p = 1 := by
    intro p hp
    rw [chiTilde_apply_prime hp]
    have hnd : ¬ p ∣ 1 := fun hdvd => hp.one_lt.ne' (Nat.eq_one_of_dvd_one hdvd)
    rw [if_neg hnd]
    have : ((p : ℕ) : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [this, map_one]
  exact chiTilde_completelyMultiplicativeC.eq_of_forall_prime hcm1
    chiTilde_one (by simp) hprime hu

/-! ### The non-principal character sums, aggregated over the finitely many characters

`exists_norm_zetaWeightedSum_char_mul_le` gives, for each non-principal `χ₁ mod N`, a
constant `C(χ₁)` with `‖𝔖_{χ₁·h}‖ ≤ C(χ₁)·exp(√(2B₂)·√(4 log log X + 17))` for every
pretentious-to-`1` unimodular completely multiplicative `h`.  The equidistribution insert
needs this summed over all non-principal characters of all moduli `r' ∣ q^k`, with one
constant.  We aggregate by summing the (choice-extracted) constants. -/

/-- One modulus: the whole non-principal block of the character average is bounded by a
single constant times the subexponential factor. -/
private lemma exists_nonprincipal_sum_bound (N : ℕ) [NeZero N] :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧
      ∀ (h : ℕ → ℂ), CompletelyMultiplicativeC h → h 1 = 1 → Unimodular h →
      ∀ X : ℝ, 3 ≤ X → ∀ B₂ : ℝ,
        pretentiousDistSq h (fun _ => 1) (⌊X⌋₊ + 1) ≤ B₂ →
        ∀ b : ZMod N,
        ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ N),
            (starRingEnd ℂ) (χ b)
              * zetaWeightedSum (fun n : ℕ => χ (n : ZMod N) * h n) (1 + 1 / Real.log X)‖
          ≤ C₃ * Real.exp (Real.sqrt (2 * max B₂ 0)
              * Real.sqrt (4 * Real.log (Real.log X) + 17)) := by
  classical
  -- choice-extract a constant for each character (junk 0 at the principal one)
  have hex : ∀ χ : DirichletCharacter ℂ N, ∃ C : ℝ,
      χ ≠ 1 →
      ∀ (h : ℕ → ℂ), CompletelyMultiplicativeC h → h 1 = 1 → Unimodular h →
      ∀ X : ℝ, 3 ≤ X → ∀ B₀ : ℝ,
        pretentiousDistSq h (fun _ => 1) (⌊X⌋₊ + 1) ≤ B₀ →
        ‖zetaWeightedSum (fun n : ℕ => χ (n : ZMod N) * h n) (1 + 1 / Real.log X)‖
          ≤ C * Real.exp (Real.sqrt (2 * B₀)
              * Real.sqrt (4 * Real.log (Real.log X) + 17)) := by
    intro χ
    by_cases hχ : χ = 1
    · exact ⟨0, fun hcon => absurd hχ hcon⟩
    · obtain ⟨C, hC⟩ := exists_norm_zetaWeightedSum_char_mul_le hχ
      exact ⟨C, fun _ => hC⟩
  choose f hf using hex
  refine ⟨∑ χ : DirichletCharacter ℂ N, max (f χ) 0,
    Finset.sum_nonneg fun χ _ => le_max_right _ _, ?_⟩
  intro h hmul h1 huni X hX B₂ hpret b
  have hB₂ : pretentiousDistSq h (fun _ => 1) (⌊X⌋₊ + 1) ≤ max B₂ 0 :=
    hpret.trans (le_max_left _ _)
  calc ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ N),
        (starRingEnd ℂ) (χ b)
          * zetaWeightedSum (fun n : ℕ => χ (n : ZMod N) * h n) (1 + 1 / Real.log X)‖
      ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ N),
          ‖(starRingEnd ℂ) (χ b)
            * zetaWeightedSum (fun n : ℕ => χ (n : ZMod N) * h n) (1 + 1 / Real.log X)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ N),
          max (f χ) 0 * Real.exp (Real.sqrt (2 * max B₂ 0)
            * Real.sqrt (4 * Real.log (Real.log X) + 17)) := by
        refine Finset.sum_le_sum fun χ hχ => ?_
        have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
        have hb1 : ‖(starRingEnd ℂ) (χ b)‖ ≤ 1 := by
          rw [RCLike.norm_conj]
          exact DirichletCharacter.norm_le_one χ b
        calc ‖(starRingEnd ℂ) (χ b)
              * zetaWeightedSum (fun n : ℕ => χ (n : ZMod N) * h n) (1 + 1 / Real.log X)‖
            = ‖(starRingEnd ℂ) (χ b)‖
              * ‖zetaWeightedSum (fun n : ℕ => χ (n : ZMod N) * h n) (1 + 1 / Real.log X)‖ :=
              norm_mul _ _
          _ ≤ 1 * (f χ * Real.exp (Real.sqrt (2 * max B₂ 0)
                * Real.sqrt (4 * Real.log (Real.log X) + 17))) := by
              refine mul_le_mul hb1
                (hf χ hχ1 h hmul h1 huni X hX (max B₂ 0) hB₂) (norm_nonneg _) zero_le_one
          _ ≤ max (f χ) 0 * Real.exp (Real.sqrt (2 * max B₂ 0)
                * Real.sqrt (4 * Real.log (Real.log X) + 17)) := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ = (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ N), max (f χ) 0)
          * Real.exp (Real.sqrt (2 * max B₂ 0)
            * Real.sqrt (4 * Real.log (Real.log X) + 17)) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ χ : DirichletCharacter ℂ N, max (f χ) 0)
          * Real.exp (Real.sqrt (2 * max B₂ 0)
            * Real.sqrt (4 * Real.log (Real.log X) + 17)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun χ _ _ => le_max_right _ _

/-- All moduli dividing `M` at once: one constant for every non-principal block at every
level `r' ∣ M`. -/
private lemma exists_nonprincipal_sum_bound_divisors (M : ℕ) (hM : M ≠ 0) :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧
      ∀ r' : ℕ, r' ∣ M →
      ∀ (h : ℕ → ℂ), CompletelyMultiplicativeC h → h 1 = 1 → Unimodular h →
      ∀ X : ℝ, 3 ≤ X → ∀ B₂ : ℝ,
        pretentiousDistSq h (fun _ => 1) (⌊X⌋₊ + 1) ≤ B₂ →
        ∀ b : ZMod r',
        ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ r'),
            (starRingEnd ℂ) (χ b)
              * zetaWeightedSum (fun n : ℕ => χ (n : ZMod r') * h n) (1 + 1 / Real.log X)‖
          ≤ C₃ * Real.exp (Real.sqrt (2 * max B₂ 0)
              * Real.sqrt (4 * Real.log (Real.log X) + 17)) := by
  -- choice-extract per divisor (junk 0 off the divisors)
  have hex : ∀ r' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (r' ∣ M →
      ∀ (h : ℕ → ℂ), CompletelyMultiplicativeC h → h 1 = 1 → Unimodular h →
      ∀ X : ℝ, 3 ≤ X → ∀ B₂ : ℝ,
        pretentiousDistSq h (fun _ => 1) (⌊X⌋₊ + 1) ≤ B₂ →
        ∀ b : ZMod r',
        ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ r'),
            (starRingEnd ℂ) (χ b)
              * zetaWeightedSum (fun n : ℕ => χ (n : ZMod r') * h n) (1 + 1 / Real.log X)‖
          ≤ C * Real.exp (Real.sqrt (2 * max B₂ 0)
              * Real.sqrt (4 * Real.log (Real.log X) + 17))) := by
    intro r'
    by_cases hr' : r' ∣ M
    · have hr'0 : r' ≠ 0 := by
        rintro rfl
        exact hM (Nat.eq_zero_of_zero_dvd hr')
      haveI : NeZero r' := ⟨hr'0⟩
      obtain ⟨C, hC0, hC⟩ := exists_nonprincipal_sum_bound r'
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun hcon => absurd hcon hr'⟩
  choose f hf0 hf using hex
  refine ⟨∑ r' ∈ M.divisors, f r', Finset.sum_nonneg fun r' _ => hf0 r', ?_⟩
  intro r' hr' h hmul h1 huni X hX B₂ hpret b
  have hmem : r' ∈ M.divisors := Nat.mem_divisors.mpr ⟨hr', hM⟩
  refine (hf r' hr' h hmul h1 huni X hX B₂ hpret b).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact Finset.single_le_sum (fun s _ => hf0 s) hmem

/-! ### Equidistribution of `h` in residue classes mod `q^k`

Tao 2015 §4: `∑_{n ≡ b (q^k)} h(n)/n^{1+1/log X} = 𝔖/q^k + O_{q,k}(exp(O_ε((log log X)^{1/2})))`,
for all residues `b` (primitive or not).  The reduction to the primitive case goes through
the gcd (P2), the character average (E3), the principal Euler-factor identity, and the
non-principal bounds (E2), with the `φ(r')⁻¹`-normalized principal factor being
`1/r + O(log r/(r·log X))` (the κ-calculus).

The two external inputs (the principal identity and the κ-calculus) are taken as
hypotheses `hprincipal`/`hkappa` here; the public wrapper discharges them. -/

private lemma exists_equidistribution_bound_core (q k : ℕ) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hprincipal : ∀ r' : ℕ, r' ≠ 0 → ∀ h : ℕ → ℂ, CompletelyMultiplicativeC h →
      h 1 = 1 → (∀ n, ‖h n‖ ≤ 1) → ∀ σ : ℝ, 1 < σ →
      zetaWeightedSum (fun n : ℕ => (1 : DirichletCharacter ℂ r') ((n : ℕ) : ZMod r') * h n) σ
        = zetaWeightedSum h σ
          * ∏ p ∈ r'.primeFactors, (1 - h p / ((p : ℕ) : ℂ) ^ ((σ : ℝ) : ℂ)))
    (hkappa : ∀ d r' : ℕ, 1 ≤ d → 1 ≤ r' → ∀ L : ℝ, 2 ≤ L →
      2 * Real.log ((d : ℝ) * (r' : ℝ)) ≤ L →
      |((d : ℝ) * (r' : ℝ)) * ((1 / (d : ℝ) ^ (1 + 1/L)) * (1 / (r'.totient : ℝ))
          * ∏ p ∈ r'.primeFactors, (1 - 1 / (p : ℝ) ^ (1 + 1/L))) - 1|
        ≤ 2 * Real.log ((d : ℝ) * (r' : ℝ)) / L) :
    ∃ C₄ : ℝ, 0 ≤ C₄ ∧
      ∀ h : ℕ → ℂ, CompletelyMultiplicativeC h → h 1 = 1 → Unimodular h →
      (∀ p : ℕ, p.Prime → p ∣ q → h p = 1) →
      ∀ X : ℕ, (3 : ℝ) ≤ (X : ℝ) →
        max 2 (2 * Real.log ((q ^ k : ℕ) : ℝ)) ≤ Real.log X →
      ∀ B₂ : ℝ, 0 ≤ B₂ → pretentiousDistSq h (fun _ => 1) (X + 1) ≤ B₂ →
      ∀ b : ℕ, b ≠ 0 →
        ‖natResidueZetaSum h (q ^ k) b (1 + 1 / Real.log X)
            - zetaWeightedSum h (1 + 1 / Real.log X) / ((q ^ k : ℕ) : ℂ)‖
          ≤ C₄ * (1 + Real.exp (Real.sqrt (2 * B₂)
              * Real.sqrt (4 * Real.log (Real.log X) + 17))) := by
  have hr0 : (q ^ k : ℕ) ≠ 0 := pow_ne_zero _ (by omega)
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_nonprincipal_sum_bound_divisors (q ^ k) hr0
  refine ⟨max (4 * Real.log ((q ^ k : ℕ) : ℝ)) C₃,
    le_max_of_le_right hC₃0, ?_⟩
  intro h hmul h1 huni hp1 X hX3 hLbig B₂ hB₂0 hpret b hb
  set L : ℝ := Real.log X with hLdef
  set σ : ℝ := 1 + 1 / L with hσdef
  have hL2 : 2 ≤ L := le_trans (le_max_left _ _) hLbig
  have hlogr : 2 * Real.log ((q ^ k : ℕ) : ℝ) ≤ L := le_trans (le_max_right _ _) hLbig
  have hL0 : 0 < L := by linarith
  have hσ1 : 1 < σ := by
    have : 0 < 1 / L := by positivity
    rw [hσdef]
    linarith
  have hσ0 : σ ≠ 0 := by positivity
  have hbnorm : ∀ n, ‖h n‖ ≤ 1 := fun n => (huni n).le
  -- gcd data
  set d : ℕ := Nat.gcd b (q ^ k) with hddef
  have hd0 : d ≠ 0 := Nat.gcd_ne_zero_left hb
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
  have hddvd : d ∣ q ^ k := Nat.gcd_dvd_right _ _
  set r' : ℕ := q ^ k / d with hr'def
  have hdr' : d * r' = q ^ k := Nat.mul_div_cancel' hddvd
  have hr'0 : r' ≠ 0 := by
    intro hcon
    rw [hcon, mul_zero] at hdr'
    exact hr0 hdr'.symm
  have hr'1 : 1 ≤ r' := Nat.one_le_iff_ne_zero.mpr hr'0
  haveI : NeZero r' := ⟨hr'0⟩
  have hr'dvd : r' ∣ q ^ k := Nat.div_dvd_of_dvd hddvd
  -- `h` is `1` at the gcd
  have hhd : h d = 1 := by
    refine cm_eq_one_of_primes_dvd hmul h1 hp1 hd0 fun p hp hpd => ?_
    exact hp.dvd_of_dvd_pow (hpd.trans hddvd)
  -- `h` is `1` at every prime factor of `r'`
  have hp1r' : ∀ p ∈ r'.primeFactors, h p = 1 := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ r' := Nat.dvd_of_mem_primeFactors hp
    exact hp1 p hpp (hpp.dvd_of_dvd_pow (hpd.trans hr'dvd))
  -- Step 1: gcd dilation + ZMod bridge + character average
  have hstep1 : natResidueZetaSum h (q ^ k) b σ
      = (1 / (d : ℂ) ^ (σ : ℂ)) * natResidueZetaSum h r' (b / d) σ :=
    natResidueZetaSum_eq_of_gcd hmul hb hσ0 hhd
  have hbu : IsUnit (((b / d : ℕ) : ZMod r')) := isUnit_div_gcd_cast hb
  have hstep2 : natResidueZetaSum h r' (b / d) σ
      = residueZetaSum h r' ((b / d : ℕ) : ZMod r') σ :=
    natResidueZetaSum_eq_residueZetaSum h (b / d) σ
  have hstep3 : residueZetaSum h r' ((b / d : ℕ) : ZMod r') σ
      = (r'.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ r',
          (starRingEnd ℂ) (χ ((b / d : ℕ) : ZMod r'))
            * zetaWeightedSum (fun n : ℕ => χ ((n : ℕ) : ZMod r') * h n) σ :=
    residueZetaSum_eq_char_average hbnorm hσ1 hbu
  -- Step 2: split off the principal character
  set N : ℂ := ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ r'),
      (starRingEnd ℂ) (χ ((b / d : ℕ) : ZMod r'))
        * zetaWeightedSum (fun n : ℕ => χ ((n : ℕ) : ZMod r') * h n) σ with hNdef
  have hone : ((1 : DirichletCharacter ℂ r') ((b / d : ℕ) : ZMod r')) = 1 := by
    have := MulChar.one_apply_coe (R := ZMod r') (R' := ℂ) hbu.unit
    rwa [hbu.unit_spec] at this
  have hsplit : ∑ χ : DirichletCharacter ℂ r',
      (starRingEnd ℂ) (χ ((b / d : ℕ) : ZMod r'))
        * zetaWeightedSum (fun n : ℕ => χ ((n : ℕ) : ZMod r') * h n) σ
      = zetaWeightedSum
          (fun n : ℕ => (1 : DirichletCharacter ℂ r') ((n : ℕ) : ZMod r') * h n) σ + N := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ r'))]
    rw [hone, map_one, one_mul]
  -- Step 3: principal term via the Euler-factor identity (`h(p) = 1` at `p ∣ r'`)
  have hprin : zetaWeightedSum
      (fun n : ℕ => (1 : DirichletCharacter ℂ r') ((n : ℕ) : ZMod r') * h n) σ
      = zetaWeightedSum h σ
        * ∏ p ∈ r'.primeFactors, (1 - 1 / ((p : ℕ) : ℂ) ^ ((σ : ℝ) : ℂ)) := by
    rw [hprincipal r' hr'0 h hmul h1 hbnorm σ hσ1]
    congr 1
    exact Finset.prod_congr rfl fun p hp => by rw [hp1r' p hp]
  -- the complex scalar in front of the main term is a real scalar
  have hφ0 : (0 : ℝ) < (r'.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hr'0)
  set cR : ℝ := 1 / (d : ℝ) ^ σ * (1 / (r'.totient : ℝ))
      * ∏ p ∈ r'.primeFactors, (1 - 1 / (p : ℝ) ^ σ) with hcRdef
  have hdcast : ((d : ℂ) : ℂ) ^ ((σ : ℝ) : ℂ) = (((d : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (d : ℝ))]
    norm_num
  have hpcast : ∀ p ∈ r'.primeFactors,
      (1 - 1 / ((p : ℕ) : ℂ) ^ ((σ : ℝ) : ℂ)) = (((1 - 1 / (p : ℝ) ^ σ : ℝ)) : ℂ) := by
    intro p hp
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
    rw [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_cpow hp0]
    norm_num
  have hcast : (1 / (d : ℂ) ^ (σ : ℂ)) * ((r'.totient : ℂ))⁻¹
      * ∏ p ∈ r'.primeFactors, (1 - 1 / ((p : ℕ) : ℂ) ^ ((σ : ℝ) : ℂ))
      = ((cR : ℝ) : ℂ) := by
    rw [Finset.prod_congr rfl hpcast, ← Complex.ofReal_prod, hcRdef]
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one]
    rw [Complex.ofReal_div, Complex.ofReal_one]
    rw [← hdcast]
    push_cast
    ring
  -- decompose the target difference
  have hdecomp : natResidueZetaSum h (q ^ k) b σ
      - zetaWeightedSum h σ / ((q ^ k : ℕ) : ℂ)
      = (((cR : ℝ) : ℂ) - 1 / ((q ^ k : ℕ) : ℂ)) * zetaWeightedSum h σ
        + (1 / (d : ℂ) ^ (σ : ℂ)) * ((r'.totient : ℂ))⁻¹ * N := by
    rw [hstep1, hstep2, hstep3, hsplit, hprin, ← hcast]
    ring
  -- bound the main-term deviation via the κ-calculus
  have hr'cast : ((q ^ k : ℕ) : ℝ) = (d : ℝ) * (r' : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hdr'.symm
  have hrpos : (0 : ℝ) < ((q ^ k : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hr0
  have hlogr0 : 0 ≤ Real.log ((q ^ k : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr0)
  have hkap : |((q ^ k : ℕ) : ℝ) * cR - 1| ≤ 2 * Real.log ((q ^ k : ℕ) : ℝ) / L := by
    have := hkappa d r' hd1 hr'1 L hL2 (by rw [← hr'cast]; exact hlogr)
    rw [← hr'cast] at this
    calc |((q ^ k : ℕ) : ℝ) * cR - 1|
        = |((q ^ k : ℕ) : ℝ) * ((1 / (d : ℝ) ^ (1 + 1/L)) * (1 / (r'.totient : ℝ))
            * ∏ p ∈ r'.primeFactors, (1 - 1 / (p : ℝ) ^ (1 + 1/L))) - 1| := by
          rw [hcRdef, hσdef]
      _ ≤ 2 * Real.log ((q ^ k : ℕ) : ℝ) / L := this
  have habs : |cR - 1 / ((q ^ k : ℕ) : ℝ)|
      ≤ (1 / ((q ^ k : ℕ) : ℝ)) * (2 * Real.log ((q ^ k : ℕ) : ℝ) / L) := by
    have hexpand : ((q ^ k : ℕ) : ℝ) * cR - 1
        = ((q ^ k : ℕ) : ℝ) * (cR - 1 / ((q ^ k : ℕ) : ℝ)) := by
      field_simp
    have hkey : ((q ^ k : ℕ) : ℝ) * |cR - 1 / ((q ^ k : ℕ) : ℝ)|
        ≤ 2 * Real.log ((q ^ k : ℕ) : ℝ) / L := by
      have := hkap
      rw [hexpand, abs_mul, abs_of_pos hrpos] at this
      exact this
    calc |cR - 1 / ((q ^ k : ℕ) : ℝ)|
        = (1 / ((q ^ k : ℕ) : ℝ))
            * (((q ^ k : ℕ) : ℝ) * |cR - 1 / ((q ^ k : ℕ) : ℝ)|) := by
          field_simp
      _ ≤ (1 / ((q ^ k : ℕ) : ℝ)) * (2 * Real.log ((q ^ k : ℕ) : ℝ) / L) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
  have hSnorm : ‖zetaWeightedSum h σ‖ ≤ 2 + L := by
    have := norm_zetaWeightedSum_le (g := h) hbnorm (X := ((X : ℕ) : ℝ)) hX3
    rwa [hσdef, hLdef]
  have hmainbound : ‖(((cR : ℝ) : ℂ) - 1 / ((q ^ k : ℕ) : ℂ)) * zetaWeightedSum h σ‖
      ≤ 4 * Real.log ((q ^ k : ℕ) : ℝ) := by
    rw [norm_mul]
    have hcnorm : ‖((cR : ℝ) : ℂ) - 1 / ((q ^ k : ℕ) : ℂ)‖
        = |cR - 1 / ((q ^ k : ℕ) : ℝ)| := by
      have : ((cR : ℝ) : ℂ) - 1 / ((q ^ k : ℕ) : ℂ)
          = (((cR - 1 / ((q ^ k : ℕ) : ℝ)) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    rw [hcnorm]
    calc |cR - 1 / ((q ^ k : ℕ) : ℝ)| * ‖zetaWeightedSum h σ‖
        ≤ ((1 / ((q ^ k : ℕ) : ℝ)) * (2 * Real.log ((q ^ k : ℕ) : ℝ) / L)) * (2 + L) := by
          refine mul_le_mul habs hSnorm (norm_nonneg _) ?_
          positivity
      _ ≤ ((1 / ((q ^ k : ℕ) : ℝ)) * (2 * Real.log ((q ^ k : ℕ) : ℝ) / L)) * (2 * L) := by
          refine mul_le_mul_of_nonneg_left (by linarith) ?_
          positivity
      _ = (1 / ((q ^ k : ℕ) : ℝ)) * (4 * Real.log ((q ^ k : ℕ) : ℝ)) := by
          field_simp
          ring
      _ ≤ 1 * (4 * Real.log ((q ^ k : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_one hrpos]
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr0
      _ = 4 * Real.log ((q ^ k : ℕ) : ℝ) := one_mul _
  -- bound the non-principal block
  have hpret' : pretentiousDistSq h (fun _ => 1) (⌊((X : ℕ) : ℝ)⌋₊ + 1) ≤ B₂ := by
    rwa [Nat.floor_natCast]
  have hNbound : ‖N‖ ≤ C₃ * Real.exp (Real.sqrt (2 * B₂)
      * Real.sqrt (4 * Real.log (Real.log X) + 17)) := by
    have := hC₃ r' hr'dvd h hmul h1 huni ((X : ℕ) : ℝ) hX3 B₂ hpret'
      (((b / d : ℕ)) : ZMod r')
    rwa [max_eq_left hB₂0] at this
  have hSCnorm : ‖(1 / (d : ℂ) ^ (σ : ℂ)) * ((r'.totient : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_mul, norm_div, norm_one, norm_inv]
    have hdnorm : ‖(d : ℂ) ^ (σ : ℂ)‖ = (d : ℝ) ^ σ := by
      have := Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hd0) (σ : ℂ)
      simpa using this
    have hφnorm : ‖((r'.totient : ℕ) : ℂ)‖ = (r'.totient : ℝ) := by
      simp
    rw [hdnorm, hφnorm]
    have h1d : (1 : ℝ) ≤ (d : ℝ) ^ σ :=
      Real.one_le_rpow (by exact_mod_cast hd1) (by positivity)
    have h1φ : (1 : ℝ) ≤ (r'.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hr'0)
    calc 1 / (d : ℝ) ^ σ * ((r'.totient : ℝ))⁻¹
        ≤ 1 * 1 := by
          refine mul_le_mul ?_ ?_ (by positivity) zero_le_one
          · rw [div_le_one (by positivity)]
            exact h1d
          · rw [inv_le_one_iff₀]
            right
            exact h1φ
      _ = 1 := one_mul 1
  -- final assembly
  rw [hdecomp]
  calc ‖(((cR : ℝ) : ℂ) - 1 / ((q ^ k : ℕ) : ℂ)) * zetaWeightedSum h σ
      + (1 / (d : ℂ) ^ (σ : ℂ)) * ((r'.totient : ℂ))⁻¹ * N‖
      ≤ ‖(((cR : ℝ) : ℂ) - 1 / ((q ^ k : ℕ) : ℂ)) * zetaWeightedSum h σ‖
        + ‖(1 / (d : ℂ) ^ (σ : ℂ)) * ((r'.totient : ℂ))⁻¹ * N‖ := norm_add_le _ _
    _ ≤ 4 * Real.log ((q ^ k : ℕ) : ℝ)
        + 1 * (C₃ * Real.exp (Real.sqrt (2 * B₂)
            * Real.sqrt (4 * Real.log (Real.log X) + 17))) := by
        refine add_le_add hmainbound ?_
        rw [norm_mul]
        exact mul_le_mul hSCnorm hNbound (norm_nonneg _) zero_le_one
    _ ≤ max (4 * Real.log ((q ^ k : ℕ) : ℝ)) C₃ * 1
        + max (4 * Real.log ((q ^ k : ℕ) : ℝ)) C₃
          * Real.exp (Real.sqrt (2 * B₂)
            * Real.sqrt (4 * Real.log (Real.log X) + 17)) := by
        rw [one_mul, mul_one]
        refine add_le_add (le_max_left _ _) ?_
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
    _ = max (4 * Real.log ((q ^ k : ℕ) : ℝ)) C₃
        * (1 + Real.exp (Real.sqrt (2 * B₂)
            * Real.sqrt (4 * Real.log (Real.log X) + 17))) := by ring

/-! ### The main chain: from the averaged zeta-weighted window bound to eq. (contra)

Tao 2015 §4, from eq. (jock) to eq. (contra).  Inputs (per sample, all deterministic):
the factorization data `χ̃ = chiTilde g q χ t`, `h = hPart g q χ t`, the pretense
`𝔻(h,1;X+1)² ≤ B₂`, and the `(1/H)`-averaged zeta-weighted window bound for `w = χ̃·h`.
Output: `(1/q^k) ∑_{a good} (1/H) ∑_{H'} |∑_{m≤H'} χ̃(a+m)|² ≤ 6·exp(2(20+B₂))·D + 1`
for all `X` past a threshold depending only on `(q, k, H, D, B₂)` — uniform in the
sample `g`, the character `χ` and the frequency `t`. -/

set_option maxHeartbeats 1600000 in
theorem contra_of_pretentious_window (q k H : ℕ) (hq : 1 ≤ q) (hk : 1 ≤ k) (hH : 1 ≤ H)
    (D B₂ : ℝ) (hD : 0 ≤ D) (hB₂ : 0 ≤ B₂) :
    ∃ X₁ : ℕ, ∀ X : ℕ, X₁ ≤ X →
    ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
    ∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
    pretentiousDistSq (hPart g q χ t) (fun _ => 1) (X + 1) ≤ B₂ →
    ((1 : ℝ) / H) * ∑ H' ∈ Finset.Ioc H (2 * H), ∑' n : ℕ,
        ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (n + m) * hPart g q χ t (n + m)‖ ^ 2
          / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ D * Real.log X →
    (1 / ((q : ℝ) ^ k)) * ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter
          (fun a => IsGoodResidue q k H a),
        ((1 : ℝ) / H) * ∑ H' ∈ Finset.Ioc H (2 * H),
          ‖∑ m ∈ Finset.Icc 1 H', chiTilde g q χ t (a + m)‖ ^ 2
      ≤ 6 * Real.exp (2 * (20 + B₂)) * D + 1 := by
  -- the equidistribution constant (depends only on (q,k))
  obtain ⟨C₄, hC₄0, hC₄⟩ := exists_equidistribution_bound_core q k hq hk
    (fun r' hr' h hm h1 hb σ hσ => by
      haveI : NeZero r' := ⟨hr'⟩
      exact zetaWeightedSum_principal_mul_eq hm h1 hb hσ)
    (fun _ _ hd hr' _ hL2 hLr => abs_scaled_euler_prod_sub_one_le hd hr' hL2 hLr)
  -- constants and the threshold
  set s₀ : ℝ := Real.exp (-(20 + B₂)) with hs₀def
  have hs₀0 : 0 < s₀ := Real.exp_pos _
  set A₀ : ℝ := 4 * H + 2 + 2 * C₄ with hA₀def
  have hA₀1 : 1 ≤ A₀ := by
    have : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    rw [hA₀def]
    linarith
  set c₅ : ℝ := 6 * H * (q ^ k : ℕ) * A₀ / s₀ with hc₅def
  have hrn1 : (1 : ℝ) ≤ ((q ^ k : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k (by omega : q ≠ 0))
  have hc₅0 : 0 < c₅ := by
    have : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    rw [hc₅def]
    positivity
  set y₀ : ℝ := max 1 (max (168 * B₂) (2 * Real.log c₅)) with hy₀def
  set M : ℝ := max (max 2 (2 * Real.log ((q ^ k : ℕ) : ℝ)))
      (max ((q ^ k : ℕ) : ℝ) (Real.exp y₀)) with hMdef
  refine ⟨⌈Real.exp M⌉₊, ?_⟩
  intro X hX1 g hgmul hguni χ t hpret hwin
  -- threshold consequences
  have hXM : Real.exp M ≤ (X : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hX1)
  have hX0 : (0 : ℝ) < (X : ℝ) := lt_of_lt_of_le (Real.exp_pos M) hXM
  have hML : M ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    exact hXM
  set L : ℝ := Real.log X with hLdef
  have hL2 : 2 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hML
  have hL0 : 0 < L := by linarith
  have hlogr2 : 2 * Real.log ((q ^ k : ℕ) : ℝ) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hML
  have hrL : ((q ^ k : ℕ) : ℝ) ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hML
  have hyy : y₀ ≤ Real.log L := by
    have h1 : Real.exp y₀ ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hML
    rw [Real.le_log_iff_exp_le hL0]
    exact h1
  have hX3 : (3 : ℝ) ≤ (X : ℝ) := by
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ)
      linarith
    have h2M : (2 : ℝ) ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
    exact h3.trans ((Real.exp_le_exp.mpr h2M).trans hXM)
  set σ : ℝ := 1 + 1 / L with hσdef
  have hσ1 : 1 < σ := by
    have : 0 < 1 / L := by positivity
    rw [hσdef]; linarith
  have hσ0 : (0 : ℝ) < σ := by linarith
  -- the factorization objects
  set r : ℕ := q ^ k with hrdef
  have hr0 : r ≠ 0 := pow_ne_zero k (by omega)
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
  set hh : ℕ → ℂ := hPart g q χ t with hhdef
  set ct : ℕ → ℂ := chiTilde g q χ t with hctdef
  have hhmul : CompletelyMultiplicativeC hh := hPart_completelyMultiplicativeC
  have hh1 : hh 1 = 1 := hPart_one
  have hhuni : Unimodular hh := hPart_unimodular hguni
  have hhb : ∀ n, ‖hh n‖ ≤ 1 := fun n => (hhuni n).le
  have hctuni : Unimodular ct := chiTilde_unimodular hguni
  have hp1 : ∀ p : ℕ, p.Prime → p ∣ q → hh p = 1 := by
    intro p hp hpq
    rw [hhdef, hPart_apply_prime hp, if_pos hpq]
  have hwb : ∀ n, ‖ct n * hh n‖ ≤ 1 := by
    intro n
    rw [norm_mul, hctuni n, hhuni n, one_mul]
  -- the exponential factor and the per-(a,m) error budget
  set Ex : ℝ := Real.exp (Real.sqrt (2 * B₂)
      * Real.sqrt (4 * Real.log (Real.log X) + 17)) with hExdef
  have hEx1 : 1 ≤ Ex := Real.one_le_exp (by positivity)
  set Estar : ℝ := (4 * H + 2) + C₄ * (1 + Ex) with hEstardef
  have hEstar0 : 0 ≤ Estar := by
    have : (0 : ℝ) ≤ (H : ℝ) := by positivity
    rw [hEstardef]
    have : 0 ≤ C₄ * (1 + Ex) := mul_nonneg hC₄0 (by linarith)
    positivity
  have hEstarA : Estar ≤ 2 * A₀ * Ex := by
    have h1 : (1 : ℝ) + Ex ≤ 2 * Ex := by linarith
    have h2 : C₄ * (1 + Ex) ≤ C₄ * (2 * Ex) := mul_le_mul_of_nonneg_left h1 hC₄0
    have h3 : (4 * (H : ℝ) + 2) ≤ (4 * H + 2) * Ex := by
      have h4 : (0 : ℝ) ≤ 4 * (H : ℝ) + 2 := by positivity
      nlinarith
    rw [hEstardef, hA₀def]
    nlinarith [hEx1]
  -- the singular-series bounds
  have hfloorX : (⌊((X : ℕ) : ℝ)⌋₊ : ℕ) = X := Nat.floor_natCast X
  have hpret' : pretentiousDistSq hh (fun _ => 1) (⌊((X : ℕ) : ℝ)⌋₊ + 1) ≤ B₂ := by
    rw [hfloorX]
    exact hpret
  have hSlow : s₀ * L ≤ ‖zetaWeightedSum hh σ‖ := by
    have := exp_neg_mul_log_le_norm_zetaWeightedSum (g := hh) hhmul hh1 hhb
      (X := ((X : ℕ) : ℝ)) hX3 hpret'
    rw [hσdef, hLdef, hs₀def]
    exact this
  -- the threshold controlling the error term: `c₅ · Ex ≤ L`
  have hc₅Ex : c₅ * Ex ≤ L := by
    have hy1 : (1 : ℝ) ≤ Real.log L := le_trans (le_max_left _ _) hyy
    have hy2 : 168 * B₂ ≤ Real.log L :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hyy
    have hy3 : 2 * Real.log c₅ ≤ Real.log L :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hyy
    set y : ℝ := Real.log L with hydef
    have hy0 : 0 < y := by linarith
    -- `√(2B₂)·√(4y+17) ≤ y/2`
    have hsq : Real.sqrt (2 * B₂) * Real.sqrt (4 * y + 17) ≤ y / 2 := by
      have h417 : 4 * y + 17 ≤ 21 * y := by linarith
      have hs1 : Real.sqrt (2 * B₂) * Real.sqrt (4 * y + 17)
          = Real.sqrt (2 * B₂ * (4 * y + 17)) := (Real.sqrt_mul (by linarith) _).symm
      have hs2 : 2 * B₂ * (4 * y + 17) ≤ 42 * B₂ * y := by nlinarith
      have hs3 : 42 * B₂ * y ≤ (y / 2) ^ 2 := by nlinarith
      calc Real.sqrt (2 * B₂) * Real.sqrt (4 * y + 17)
          = Real.sqrt (2 * B₂ * (4 * y + 17)) := hs1
        _ ≤ Real.sqrt ((y / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = y / 2 := Real.sqrt_sq (by linarith)
    have hlogc : Real.log c₅ ≤ y / 2 := by linarith
    calc c₅ * Ex = Real.exp (Real.log c₅ + (Real.sqrt (2 * B₂)
          * Real.sqrt (4 * Real.log (Real.log X) + 17))) := by
          rw [Real.exp_add, Real.exp_log hc₅0, hExdef]
      _ ≤ Real.exp y := by
          refine Real.exp_le_exp.mpr ?_
          have : Real.log (Real.log X) = y := by rw [hydef, hLdef]
          rw [this]
          linarith
      _ = L := by rw [hydef, Real.exp_log hL0]
  -- ================= the chain =================
  -- helper facts (discharged by `TrackCStage5JockHelpers`)
  have hHelper1 : ∀ (u : ℕ → ℂ) (v w : ℕ → ℝ), (∀ n, 0 ≤ v n) → (∀ n, 0 ≤ w n) →
      (∀ n, ‖u n‖ ^ 2 ≤ v n * w n) → Summable v → Summable w →
      ‖∑' n : ℕ, u n‖ ^ 2 ≤ (∑' n : ℕ, v n) * (∑' n : ℕ, w n) :=
    fun u v w hv hw huvw hv' hw' => norm_tsum_sq_le_tsum_mul_tsum hv hw huvw hv' hw'
  have hHelper2 : ∀ b : ℕ,
      ∑' n : ℕ, (if n % r = b % r then (1 : ℝ) / (n : ℝ) ^ σ else 0)
        ≤ 1 + (2 + L) / r :=
    fun b => tsum_indicator_class_zeta_le hr1 hX3
  have hHelper3 : ∀ a m : ℕ,
      ‖(∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0)
          - natResidueZetaSum hh r (a + m) σ‖ ≤ 2 * m + 2 :=
    fun a m => norm_tsum_indicator_shift_sub_le hhb hr1 a m hX3
  -- basic facts
  have hσC0 : ((σ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hsummZeta : Summable fun n : ℕ => 1 / (n : ℝ) ^ σ :=
    Real.summable_one_div_nat_rpow.mpr hσ1
  have hWnorm : ∀ H' n : ℕ,
      ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ≤ (H' : ℝ) := by
    intro H' n
    calc ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖
        ≤ ∑ m ∈ Finset.Icc 1 H', ‖ct (n + m) * hh (n + m)‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Finset.Icc 1 H', (1 : ℝ) := Finset.sum_le_sum fun m _ => hwb _
      _ = (H' : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  have hnormcpow : ∀ n : ℕ, n ≠ 0 → ‖(n : ℂ) ^ (σ : ℂ)‖ = (n : ℝ) ^ σ := by
    intro n hn
    have := Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn) (σ : ℂ)
    simpa using this
  -- the good residues
  set G : Finset ℕ := (Finset.Icc 1 r).filter (fun a => IsGoodResidue q k H a) with hGdef
  have hGsub : G ⊆ Finset.Icc 1 r := Finset.filter_subset _ _
  have hGcard : (G.card : ℝ) ≤ (r : ℝ) := by
    have h1 : G.card ≤ (Finset.Icc 1 r).card := Finset.card_le_card hGsub
    have h2 : (Finset.Icc 1 r).card = r := by
      rw [Nat.card_Icc]
      omega
    exact_mod_cast h1.trans (le_of_eq h2)
  have hmodinj : ∀ a₁ ∈ Finset.Icc 1 r, ∀ a₂ ∈ Finset.Icc 1 r,
      a₁ % r = a₂ % r → a₁ = a₂ := by
    intro a₁ h₁ a₂ h₂ hmod
    rw [Finset.mem_Icc] at h₁ h₂
    have e₁ : a₁ % r = if a₁ = r then 0 else a₁ := by
      by_cases hcase : a₁ = r
      · rw [if_pos hcase, hcase, Nat.mod_self]
      · rw [if_neg hcase]
        exact Nat.mod_eq_of_lt (by omega)
    have e₂ : a₂ % r = if a₂ = r then 0 else a₂ := by
      by_cases hcase : a₂ = r
      · rw [if_pos hcase, hcase, Nat.mod_self]
      · rw [if_neg hcase]
        exact Nat.mod_eq_of_lt (by omega)
    rw [e₁, e₂] at hmod
    by_cases hc₁ : a₁ = r
    · by_cases hc₂ : a₂ = r
      · rw [hc₁, hc₂]
      · rw [if_pos hc₁, if_neg hc₂] at hmod
        omega
    · by_cases hc₂ : a₂ = r
      · rw [if_neg hc₁, if_pos hc₂] at hmod
        omega
      · rw [if_neg hc₁, if_neg hc₂] at hmod
        omega
  -- summability of the pieces (per class, per window)
  have hsummV : ∀ a : ℕ, Summable fun n : ℕ =>
      (if n % r = a % r then (1 : ℝ) / (n : ℝ) ^ σ else 0) := by
    intro a
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsummZeta
    · by_cases hc : n % r = a % r <;> simp [hc] <;> positivity
    · by_cases hc : n % r = a % r
      · rw [if_pos hc]
      · rw [if_neg hc]
        positivity
  have hsummS : ∀ a H' : ℕ, Summable fun n : ℕ =>
      (if n % r = a % r
        then ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ else 0) := by
    intro a H'
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (hsummZeta.mul_left ((H' : ℝ) ^ 2))
    · by_cases hc : n % r = a % r <;> simp [hc] <;> positivity
    · by_cases hc : n % r = a % r
      · rw [if_pos hc, mul_one_div]
        refine div_le_div_of_nonneg_right ?_ ?_ |>.trans_eq rfl
        · exact pow_le_pow_left₀ (norm_nonneg _) (hWnorm H' n) 2
        · positivity
      · rw [if_neg hc]
        positivity
  -- Step CS: Cauchy–Schwarz per good class
  have hCS : ∀ a H' : ℕ,
      ‖∑' n : ℕ, (if n % r = a % r
          then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
          else 0)‖ ^ 2
        ≤ (1 + (2 + L) / r) * ∑' n : ℕ, (if n % r = a % r
            then ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ
            else 0) := by
    intro a H'
    have hv0 : ∀ n : ℕ, 0 ≤ (if n % r = a % r then (1 : ℝ) / (n : ℝ) ^ σ else 0) := by
      intro n
      by_cases hc : n % r = a % r <;> simp [hc] <;> positivity
    have hw0 : ∀ n : ℕ, 0 ≤ (if n % r = a % r
        then ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ else 0) := by
      intro n
      by_cases hc : n % r = a % r <;> simp [hc] <;> positivity
    have huvw : ∀ n : ℕ,
        ‖(if n % r = a % r
            then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
            else 0)‖ ^ 2
          ≤ (if n % r = a % r then (1 : ℝ) / (n : ℝ) ^ σ else 0)
            * (if n % r = a % r
                then ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ
                else 0) := by
      intro n
      by_cases hc : n % r = a % r
      · simp only [if_pos hc]
        rcases eq_or_ne n 0 with rfl | hn0
        · rw [Nat.cast_zero, Complex.zero_cpow hσC0, div_zero, norm_zero]
          rw [Nat.cast_zero, Real.zero_rpow (by positivity : σ ≠ 0)]
          simp
        · rw [norm_div, hnormcpow n hn0, div_pow]
          refine le_of_eq ?_
          rw [pow_two ((n : ℝ) ^ σ), div_mul_div_comm, one_mul]
      · simp [hc]
    exact le_of_le_of_eq
      ((hHelper1 _ _ _ hv0 hw0 huvw (hsummV a) (hsummS a H')).trans
        (mul_le_mul_of_nonneg_right (hHelper2 a)
          (tsum_nonneg fun n => hw0 n)))
      rfl
  -- Step B: each `n` lies in exactly one class `a ∈ [1, r]`
  have hsum_ite_eq : ∀ (n : ℕ) (c : ℝ),
      (∑ a ∈ Finset.Icc 1 r, if n % r = a % r then c else 0) = c := by
    intro n c
    set a₀ : ℕ := if n % r = 0 then r else n % r with ha₀def
    have ha₀mem : a₀ ∈ Finset.Icc 1 r := by
      rw [Finset.mem_Icc, ha₀def]
      by_cases h0 : n % r = 0
      · rw [if_pos h0]
        omega
      · rw [if_neg h0]
        have : n % r < r := Nat.mod_lt n (by omega)
        omega
    have ha₀mod : n % r = a₀ % r := by
      rw [ha₀def]
      by_cases h0 : n % r = 0
      · rw [if_pos h0, Nat.mod_self, h0]
      · rw [if_neg h0]
        have hlt : n % r < r := Nat.mod_lt n (by omega)
        rw [Nat.mod_eq_of_lt hlt]
    rw [Finset.sum_eq_single a₀]
    · rw [if_pos ha₀mod]
    · intro b hb hne
      rw [if_neg]
      intro hcon
      exact hne (hmodinj b hb a₀ ha₀mem (by rw [← hcon, ← ha₀mod]))
    · intro hcon
      exact absurd ha₀mem hcon
  have hBfull : ∀ H' : ℕ,
      (∑ a ∈ G, ∑' n : ℕ, (if n % r = a % r
          then ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ else 0))
        ≤ ∑' n : ℕ,
            ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ := by
    intro H'
    have hstep : (∑ a ∈ G, ∑' n : ℕ, (if n % r = a % r
        then ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ else 0))
        ≤ ∑ a ∈ Finset.Icc 1 r, ∑' n : ℕ, (if n % r = a % r
            then ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ
            else 0) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hGsub fun a _ _ => ?_
      refine tsum_nonneg fun n => ?_
      by_cases hc : n % r = a % r <;> simp [hc] <;> positivity
    refine hstep.trans (le_of_eq ?_)
    rw [← Summable.tsum_finsetSum fun a _ => hsummS a H']
    exact tsum_congr fun n => hsum_ite_eq n _
  -- rigidity of `χ̃` along a residue class (with the `q = 1` degenerate case inline)
  have hrig : ∀ a n m : ℕ, IsGoodResidue q k H a → n % r = a % r →
      m ∈ Finset.Icc 1 (2 * H) → ct (n + m) = ct (a + m) := by
    intro a n m hgood hcong hm
    by_cases hq1 : 1 < q
    · exact chiTilde_congr_of_good hq1 hk hgood hcong hm
    · have hqe : q = 1 := by omega
      subst hqe
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      rw [hctdef, chiTilde_eq_one_of_level_one χ t (by omega : n + m ≠ 0),
        chiTilde_eq_one_of_level_one χ t (by omega : a + m ≠ 0)]
  -- Step C: pull the rigid `χ̃(a+m)` out of the class sum
  have hYeq : ∀ a ∈ G, ∀ H', H' ≤ 2 * H →
      (∑' n : ℕ, (if n % r = a % r
          then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
          else 0))
        = ∑ m ∈ Finset.Icc 1 H', ct (a + m)
            * (∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0) := by
    intro a ha H' hH2
    have hgood : IsGoodResidue q k H a := by
      rw [hGdef] at ha
      exact (Finset.mem_filter.mp ha).2
    have hsummPer : ∀ m : ℕ, Summable fun n : ℕ =>
        (if n % r = a % r then ct (a + m) * (hh (n + m) / (n : ℂ) ^ (σ : ℂ)) else 0) := by
      intro m
      refine Summable.of_norm ?_
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsummZeta
      by_cases hc : n % r = a % r
      · rw [if_pos hc, norm_mul, norm_div]
        rcases eq_or_ne n 0 with rfl | hn0
        · rw [Nat.cast_zero, Complex.zero_cpow hσC0, norm_zero, div_zero, mul_zero]
          positivity
        · rw [hnormcpow n hn0, hctuni (a + m), one_mul]
          gcongr
          exact hhb (n + m)
      · rw [if_neg hc, norm_zero]
        positivity
    have hpt : ∀ n : ℕ, (if n % r = a % r
        then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ) else 0)
        = ∑ m ∈ Finset.Icc 1 H',
            (if n % r = a % r then ct (a + m) * (hh (n + m) / (n : ℂ) ^ (σ : ℂ)) else 0) := by
      intro n
      by_cases hc : n % r = a % r
      · simp only [if_pos hc]
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm' : m ∈ Finset.Icc 1 (2 * H) := by
          rw [Finset.mem_Icc] at hm ⊢
          omega
        rw [hrig a n m hgood hc hm', mul_div_assoc]
      · simp only [if_neg hc, Finset.sum_const_zero]
    calc (∑' n : ℕ, (if n % r = a % r
        then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ) else 0))
        = ∑' n : ℕ, ∑ m ∈ Finset.Icc 1 H',
            (if n % r = a % r then ct (a + m) * (hh (n + m) / (n : ℂ) ^ (σ : ℂ)) else 0) :=
          tsum_congr hpt
      _ = ∑ m ∈ Finset.Icc 1 H', ∑' n : ℕ,
            (if n % r = a % r then ct (a + m) * (hh (n + m) / (n : ℂ) ^ (σ : ℂ)) else 0) :=
          Summable.tsum_finsetSum fun m _ => hsummPer m
      _ = ∑ m ∈ Finset.Icc 1 H', ct (a + m)
            * (∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [← tsum_mul_left]
          exact tsum_congr fun n => by rw [mul_ite, mul_zero]
  -- Step D: the equidistribution insert, per shift
  have hE1inst : ∀ b : ℕ, b ≠ 0 →
      ‖natResidueZetaSum hh r b σ - zetaWeightedSum hh σ / ((r : ℕ) : ℂ)‖
        ≤ C₄ * (1 + Ex) := by
    intro b hb
    have hmax : max 2 (2 * Real.log ((r : ℕ) : ℝ)) ≤ Real.log X :=
      max_le (by rw [← hLdef]; exact hL2) (by rw [← hLdef]; exact hlogr2)
    exact hC₄ hh hhmul hh1 hhuni hp1 X hX3 hmax B₂ hB₂ hpret b hb
  have hinner : ∀ a ∈ G, ∀ m ∈ Finset.Icc 1 (2 * H),
      ‖(∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0)
          - zetaWeightedSum hh σ / ((r : ℕ) : ℂ)‖ ≤ Estar := by
    intro a ha m hm
    have ha1 : 1 ≤ a := by
      rw [hGdef] at ha
      have := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
      omega
    have hm2 : m ≤ 2 * H := (Finset.mem_Icc.mp hm).2
    have hdecomp : (∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0)
        - zetaWeightedSum hh σ / ((r : ℕ) : ℂ)
        = ((∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0)
            - natResidueZetaSum hh r (a + m) σ)
          + (natResidueZetaSum hh r (a + m) σ
            - zetaWeightedSum hh σ / ((r : ℕ) : ℂ)) := by
      ring
    rw [hdecomp]
    calc ‖((∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0)
            - natResidueZetaSum hh r (a + m) σ)
          + (natResidueZetaSum hh r (a + m) σ
            - zetaWeightedSum hh σ / ((r : ℕ) : ℂ))‖
        ≤ ‖(∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0)
            - natResidueZetaSum hh r (a + m) σ‖
          + ‖natResidueZetaSum hh r (a + m) σ
            - zetaWeightedSum hh σ / ((r : ℕ) : ℂ)‖ := norm_add_le _ _
      _ ≤ (2 * m + 2) + C₄ * (1 + Ex) := by
          refine add_le_add (hHelper3 a m) (hE1inst (a + m) (by omega))
      _ ≤ Estar := by
          rw [hEstardef]
          have : (m : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast hm2
          linarith
  -- Step D': the window of `χ̃` against the singular series
  set SS : ℂ := zetaWeightedSum hh σ with hSSdef
  have hYdecomp : ∀ a ∈ G, ∀ H' ∈ Finset.Ioc H (2 * H),
      (‖SS‖ / (r : ℝ)) * ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)‖
        ≤ ‖∑' n : ℕ, (if n % r = a % r
            then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
            else 0)‖ + 2 * H * Estar := by
    intro a ha H' hH'
    obtain ⟨hH'1, hH'2⟩ := Finset.mem_Ioc.mp hH'
    rw [hYeq a ha H' hH'2]
    have hmemlift : ∀ m ∈ Finset.Icc 1 H', m ∈ Finset.Icc 1 (2 * H) := by
      intro m hm
      rw [Finset.mem_Icc] at hm ⊢
      omega
    have hTS : (∑ m ∈ Finset.Icc 1 H', ct (a + m)) * (SS / ((r : ℕ) : ℂ))
        = (∑ m ∈ Finset.Icc 1 H', ct (a + m)
            * (∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0))
          - ∑ m ∈ Finset.Icc 1 H', ct (a + m)
            * ((∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0)
              - SS / ((r : ℕ) : ℂ)) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    have herrsum : ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)
        * ((∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0)
          - SS / ((r : ℕ) : ℂ))‖ ≤ 2 * H * Estar := by
      calc ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)
          * ((∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0)
            - SS / ((r : ℕ) : ℂ))‖
          ≤ ∑ m ∈ Finset.Icc 1 H', ‖ct (a + m)
              * ((∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0)
                - SS / ((r : ℕ) : ℂ))‖ := norm_sum_le _ _
        _ ≤ ∑ _m ∈ Finset.Icc 1 H', Estar := by
            refine Finset.sum_le_sum fun m hm => ?_
            rw [norm_mul, hctuni (a + m), one_mul]
            exact hinner a ha m (hmemlift m hm)
        _ = (H' : ℝ) * Estar := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        _ ≤ 2 * H * Estar := by
            have : (H' : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast hH'2
            exact mul_le_mul_of_nonneg_right (by push_cast; linarith) hEstar0
    calc (‖SS‖ / (r : ℝ)) * ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)‖
        = ‖(∑ m ∈ Finset.Icc 1 H', ct (a + m)) * (SS / ((r : ℕ) : ℂ))‖ := by
          rw [norm_mul, norm_div, Complex.norm_natCast]
          ring
      _ = ‖(∑ m ∈ Finset.Icc 1 H', ct (a + m)
            * (∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0))
          - ∑ m ∈ Finset.Icc 1 H', ct (a + m)
            * ((∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0)
              - SS / ((r : ℕ) : ℂ))‖ := by rw [hTS]
      _ ≤ ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)
            * (∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0)‖
          + ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)
            * ((∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0)
              - SS / ((r : ℕ) : ℂ))‖ := norm_sub_le _ _
      _ ≤ ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)
            * (∑' n : ℕ, if n % r = a % r then hh (n + m) / (n : ℂ) ^ (σ : ℂ) else 0)‖
          + 2 * H * Estar := add_le_add le_rfl herrsum
  -- squared form
  have hsq : ∀ a ∈ G, ∀ H' ∈ Finset.Ioc H (2 * H),
      (‖SS‖ / (r : ℝ)) ^ 2 * ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)‖ ^ 2
        ≤ 2 * ‖∑' n : ℕ, (if n % r = a % r
            then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
            else 0)‖ ^ 2 + 8 * (H : ℝ) ^ 2 * Estar ^ 2 := by
    intro a ha H' hH'
    have hx := hYdecomp a ha H' hH'
    have hx0 : 0 ≤ (‖SS‖ / (r : ℝ)) * ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)‖ := by positivity
    have hy0 : (0 : ℝ) ≤ ‖∑' n : ℕ, (if n % r = a % r
        then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
        else 0)‖ := norm_nonneg _
    have hz0 : (0 : ℝ) ≤ 2 * H * Estar := by positivity
    have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    nlinarith [sq_nonneg ((‖SS‖ / (r : ℝ)) * ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)‖
        - ‖∑' n : ℕ, (if n % r = a % r
          then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
          else 0)‖ - 2 * H * Estar),
      sq_nonneg (‖∑' n : ℕ, (if n % r = a % r
          then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
          else 0)‖ - 2 * H * Estar), mul_pow (‖SS‖ / (r : ℝ))
        ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)‖ 2]
  -- sum everything
  set Q : ℝ := ∑ a ∈ G, ∑ H' ∈ Finset.Ioc H (2 * H),
      ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)‖ ^ 2 with hQdef
  set YQ : ℝ := ∑ H' ∈ Finset.Ioc H (2 * H), ∑ a ∈ G,
      ‖∑' n : ℕ, (if n % r = a % r
          then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
          else 0)‖ ^ 2 with hYQdef
  have hIoccard : (Finset.Ioc H (2 * H)).card = H := by
    rw [Nat.card_Ioc]
    omega
  have hQbound : (‖SS‖ / (r : ℝ)) ^ 2 * Q
      ≤ 2 * YQ + 8 * (H : ℝ) ^ 2 * Estar ^ 2 * ((H : ℝ) * (r : ℝ)) := by
    rw [hQdef, Finset.mul_sum]
    calc ∑ a ∈ G, (‖SS‖ / (r : ℝ)) ^ 2 * ∑ H' ∈ Finset.Ioc H (2 * H),
          ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)‖ ^ 2
        ≤ ∑ a ∈ G, ∑ H' ∈ Finset.Ioc H (2 * H),
            (2 * ‖∑' n : ℕ, (if n % r = a % r
              then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
              else 0)‖ ^ 2 + 8 * (H : ℝ) ^ 2 * Estar ^ 2) := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun H' hH' => hsq a ha H' hH'
      _ = (∑ a ∈ G, ∑ H' ∈ Finset.Ioc H (2 * H),
            2 * ‖∑' n : ℕ, (if n % r = a % r
              then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
              else 0)‖ ^ 2)
          + (G.card : ℝ) * ((H : ℝ) * (8 * (H : ℝ) ^ 2 * Estar ^ 2)) := by
          have hinner2 : ∀ a ∈ G, (∑ H' ∈ Finset.Ioc H (2 * H),
              (2 * ‖∑' n : ℕ, (if n % r = a % r
                then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
                else 0)‖ ^ 2 + 8 * (H : ℝ) ^ 2 * Estar ^ 2))
              = (∑ H' ∈ Finset.Ioc H (2 * H),
                  2 * ‖∑' n : ℕ, (if n % r = a % r
                    then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
                    else 0)‖ ^ 2)
                + (H : ℝ) * (8 * (H : ℝ) ^ 2 * Estar ^ 2) := by
            intro a _
            rw [Finset.sum_add_distrib, Finset.sum_const, hIoccard, nsmul_eq_mul]
          rw [Finset.sum_congr rfl hinner2, Finset.sum_add_distrib, Finset.sum_const,
            nsmul_eq_mul]
      _ ≤ 2 * YQ + 8 * (H : ℝ) ^ 2 * Estar ^ 2 * ((H : ℝ) * (r : ℝ)) := by
          refine add_le_add (le_of_eq ?_) ?_
          · rw [hYQdef, Finset.mul_sum, Finset.sum_comm]
            exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
          · have h8 : (0 : ℝ) ≤ (H : ℝ) * (8 * (H : ℝ) ^ 2 * Estar ^ 2) := by positivity
            calc (G.card : ℝ) * ((H : ℝ) * (8 * (H : ℝ) ^ 2 * Estar ^ 2))
                ≤ (r : ℝ) * ((H : ℝ) * (8 * (H : ℝ) ^ 2 * Estar ^ 2)) :=
                  mul_le_mul_of_nonneg_right hGcard h8
              _ = 8 * (H : ℝ) ^ 2 * Estar ^ 2 * ((H : ℝ) * (r : ℝ)) := by ring
  have hYQbound : YQ ≤ (1 + (2 + L) / r) * ((H : ℝ) * (D * L)) := by
    have hper : ∀ H' ∈ Finset.Ioc H (2 * H), ∑ a ∈ G,
        ‖∑' n : ℕ, (if n % r = a % r
            then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
            else 0)‖ ^ 2
        ≤ (1 + (2 + L) / r) * ∑' n : ℕ,
            ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ := by
      intro H' _
      calc ∑ a ∈ G, ‖∑' n : ℕ, (if n % r = a % r
            then (∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)) / (n : ℂ) ^ (σ : ℂ)
            else 0)‖ ^ 2
          ≤ ∑ a ∈ G, (1 + (2 + L) / r) * ∑' n : ℕ, (if n % r = a % r
              then ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ
              else 0) :=
            Finset.sum_le_sum fun a _ => hCS a H'
        _ = (1 + (2 + L) / r) * ∑ a ∈ G, ∑' n : ℕ, (if n % r = a % r
              then ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ
              else 0) := by rw [Finset.mul_sum]
        _ ≤ (1 + (2 + L) / r) * ∑' n : ℕ,
              ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ := by
            refine mul_le_mul_of_nonneg_left (hBfull H') ?_
            have h2L : 0 ≤ (2 + L) / r := by positivity
            linarith
    have hsumfull : ∑ H' ∈ Finset.Ioc H (2 * H), ∑' n : ℕ,
        ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ
        ≤ (H : ℝ) * (D * L) := by
      have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
      have hthis := hwin
      rw [one_div, inv_mul_eq_div, div_le_iff₀ hHpos] at hthis
      linarith [hthis]
    calc YQ ≤ ∑ H' ∈ Finset.Ioc H (2 * H), (1 + (2 + L) / r) * ∑' n : ℕ,
          ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ := by
          rw [hYQdef]
          exact Finset.sum_le_sum hper
      _ = (1 + (2 + L) / r) * ∑ H' ∈ Finset.Ioc H (2 * H), ∑' n : ℕ,
            ‖∑ m ∈ Finset.Icc 1 H', ct (n + m) * hh (n + m)‖ ^ 2 / (n : ℝ) ^ σ := by
          rw [Finset.mul_sum]
      _ ≤ (1 + (2 + L) / r) * ((H : ℝ) * (D * L)) := by
          refine mul_le_mul_of_nonneg_left hsumfull ?_
          have h2L : 0 ≤ (2 + L) / r := by positivity
          linarith
  -- ================= final arithmetic =================
  have hrR0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr0
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun H' _ => by positivity
  set W : ℝ := 2 * (1 + (2 + L) / r) * (D * L) + 8 * (H : ℝ) ^ 2 * Estar ^ 2 * (r : ℝ)
    with hWdef
  have hW0 : 0 ≤ W := by
    have h1 : (0 : ℝ) ≤ (2 + L) / r := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (1 + (2 + L) / r) * (D * L) := by
      have : (0 : ℝ) ≤ 1 + (2 + L) / r := by linarith
      positivity
    have h3 : (0 : ℝ) ≤ 8 * (H : ℝ) ^ 2 * Estar ^ 2 * (r : ℝ) := by positivity
    linarith
  have hkey2 : s₀ ^ 2 * L ^ 2 * Q ≤ (H : ℝ) * W * (r : ℝ) ^ 2 := by
    have hSSr : (s₀ * L / (r : ℝ)) ^ 2 ≤ (‖SS‖ / (r : ℝ)) ^ 2 := by
      have h1 : s₀ * L / (r : ℝ) ≤ ‖SS‖ / (r : ℝ) := by
        gcongr
      exact pow_le_pow_left₀ (by positivity) h1 2
    have hkey : (s₀ * L / (r : ℝ)) ^ 2 * Q ≤ (H : ℝ) * W := by
      calc (s₀ * L / (r : ℝ)) ^ 2 * Q
          ≤ (‖SS‖ / (r : ℝ)) ^ 2 * Q := mul_le_mul_of_nonneg_right hSSr hQ0
        _ ≤ 2 * YQ + 8 * (H : ℝ) ^ 2 * Estar ^ 2 * ((H : ℝ) * (r : ℝ)) := hQbound
        _ ≤ 2 * ((1 + (2 + L) / r) * ((H : ℝ) * (D * L)))
            + 8 * (H : ℝ) ^ 2 * Estar ^ 2 * ((H : ℝ) * (r : ℝ)) := by
            have := mul_le_mul_of_nonneg_left hYQbound (by norm_num : (0 : ℝ) ≤ 2)
            linarith
        _ = (H : ℝ) * W := by
            rw [hWdef]
            ring
    have := mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ (r : ℝ) ^ 2)
    calc s₀ ^ 2 * L ^ 2 * Q = (s₀ * L / (r : ℝ)) ^ 2 * Q * (r : ℝ) ^ 2 := by
          field_simp
      _ ≤ (H : ℝ) * W * (r : ℝ) ^ 2 := this
  -- exponential bookkeeping
  have hs₀exp : s₀ ^ 2 * Real.exp (2 * (20 + B₂)) = 1 := by
    rw [hs₀def, sq, ← Real.exp_add, ← Real.exp_add,
      show -(20 + B₂) + -(20 + B₂) + 2 * (20 + B₂) = 0 by ring, Real.exp_zero]
  have hPieceA : 2 * (1 + (2 + L) / r) * (D * L) * (r : ℝ) / (s₀ ^ 2 * L ^ 2)
      ≤ 6 * Real.exp (2 * (20 + B₂)) * D := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < s₀ ^ 2 * L ^ 2)]
    have hRHS : 6 * Real.exp (2 * (20 + B₂)) * D * (s₀ ^ 2 * L ^ 2) = 6 * D * L ^ 2 := by
      have hcomm : Real.exp (2 * (20 + B₂)) * s₀ ^ 2 = 1 := by
        rw [mul_comm]
        exact hs₀exp
      calc 6 * Real.exp (2 * (20 + B₂)) * D * (s₀ ^ 2 * L ^ 2)
          = 6 * D * L ^ 2 * (Real.exp (2 * (20 + B₂)) * s₀ ^ 2) := by ring
        _ = 6 * D * L ^ 2 := by rw [hcomm, mul_one]
    rw [hRHS]
    have hLHS : 2 * (1 + (2 + L) / r) * (D * L) * (r : ℝ)
        = 2 * D * L * ((r : ℝ) + 2 + L) := by
      field_simp
      ring
    rw [hLHS]
    have h3L : (r : ℝ) + 2 + L ≤ 3 * L := by linarith [hrL, hL2]
    have h2DL : (0 : ℝ) ≤ 2 * D * L := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3L h2DL]
  have hPieceB : 8 * (H : ℝ) ^ 2 * Estar ^ 2 * (r : ℝ) * (r : ℝ) / (s₀ ^ 2 * L ^ 2)
      ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < s₀ ^ 2 * L ^ 2)]
    have hA₀0 : (0 : ℝ) ≤ A₀ := le_trans zero_le_one hA₀1
    have hEx0 : (0 : ℝ) ≤ Ex := le_trans zero_le_one hEx1
    have hHrA : (0 : ℝ) ≤ 6 * (H : ℝ) * (r : ℝ) * A₀ * Ex := by positivity
    have h2 : 6 * (H : ℝ) * (r : ℝ) * A₀ * Ex ≤ s₀ * L := by
      have h3 := mul_le_mul_of_nonneg_left hc₅Ex hs₀0.le
      have h4 : s₀ * (c₅ * Ex) = 6 * (H : ℝ) * (r : ℝ) * A₀ * Ex := by
        rw [hc₅def]
        field_simp
      linarith [h4 ▸ h3]
    have h2sq : (6 * (H : ℝ) * (r : ℝ) * A₀ * Ex) ^ 2 ≤ (s₀ * L) ^ 2 :=
      pow_le_pow_left₀ hHrA h2 2
    have h1sq : Estar ^ 2 ≤ (2 * A₀ * Ex) ^ 2 :=
      pow_le_pow_left₀ hEstar0 hEstarA 2
    have hXnn : (0 : ℝ) ≤ (H : ℝ) ^ 2 * (r : ℝ) ^ 2 * A₀ ^ 2 * Ex ^ 2 := by positivity
    calc 8 * (H : ℝ) ^ 2 * Estar ^ 2 * (r : ℝ) * (r : ℝ)
        = 8 * (H : ℝ) ^ 2 * (r : ℝ) ^ 2 * Estar ^ 2 := by ring
      _ ≤ 8 * (H : ℝ) ^ 2 * (r : ℝ) ^ 2 * (2 * A₀ * Ex) ^ 2 :=
          mul_le_mul_of_nonneg_left h1sq (by positivity)
      _ = 32 * ((H : ℝ) ^ 2 * (r : ℝ) ^ 2 * A₀ ^ 2 * Ex ^ 2) := by ring
      _ ≤ 36 * ((H : ℝ) ^ 2 * (r : ℝ) ^ 2 * A₀ ^ 2 * Ex ^ 2) := by linarith
      _ = (6 * (H : ℝ) * (r : ℝ) * A₀ * Ex) ^ 2 := by ring
      _ ≤ (s₀ * L) ^ 2 := h2sq
      _ = s₀ ^ 2 * L ^ 2 := by ring
  -- assemble
  have hrcast : ((r : ℕ) : ℝ) = (q : ℝ) ^ k := by
    rw [hrdef]
    push_cast
    ring
  have hgoalform : (1 / ((q : ℝ) ^ k)) * ∑ a ∈ G, ((1 : ℝ) / H)
      * ∑ H' ∈ Finset.Ioc H (2 * H), ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)‖ ^ 2
      = Q / ((r : ℝ) * (H : ℝ)) := by
    have h1 : ∑ a ∈ G, ((1 : ℝ) / H)
        * ∑ H' ∈ Finset.Ioc H (2 * H), ‖∑ m ∈ Finset.Icc 1 H', ct (a + m)‖ ^ 2
        = (1 / (H : ℝ)) * Q := by
      rw [hQdef, Finset.mul_sum]
    rw [h1, ← hrcast]
    field_simp
  rw [hgoalform]
  have hQrH : Q / ((r : ℝ) * (H : ℝ)) ≤ W * (r : ℝ) / (s₀ ^ 2 * L ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkey2]
  refine hQrH.trans ?_
  have hsplit : W * (r : ℝ) / (s₀ ^ 2 * L ^ 2)
      = 2 * (1 + (2 + L) / r) * (D * L) * (r : ℝ) / (s₀ ^ 2 * L ^ 2)
        + 8 * (H : ℝ) ^ 2 * Estar ^ 2 * (r : ℝ) * (r : ℝ) / (s₀ ^ 2 * L ^ 2) := by
    rw [hWdef]
    ring
  rw [hsplit]
  exact add_le_add hPieceA hPieceB

end Tao2015

end MoltResearch
