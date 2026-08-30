import MoltResearch.Discrepancy.RamareIdentity

/-!
# Track C: typical factorization — the [mrt] 𝒮-set (Track R, A.2 leg, A2-I)

The set `𝒮` of integers with at least one prime factor in each of a
family of prime blocks `[P_j, Q_j]` — the typical-factorization
restriction of [MR]/[mrt, Appendix A], in the idiom of the Ramaré
`𝒰`-machinery: a level is a `Finset ℕ` of primes, a family is a
`List (Finset ℕ)` (the slot `RamareIdentity.uBound` recurses over),
and membership at one level is the `𝒰`-filter's
`0 < (P.filter (· ∣ n)).card`.
-/

namespace MoltResearch

/-- `n` has at least one divisor in every level of the family.  (For
prime levels: at least one prime factor in each block — the [mrt]
`𝒮`-membership.) -/
def HasFactorInAll (levels : List (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ P ∈ levels, 0 < (P.filter (· ∣ n)).card

instance (levels : List (Finset ℕ)) (n : ℕ) :
    Decidable (HasFactorInAll levels n) :=
  List.decidableBAll _ levels

@[simp] theorem hasFactorInAll_nil (n : ℕ) : HasFactorInAll [] n := by
  intro P hP
  simp at hP

theorem hasFactorInAll_cons {P : Finset ℕ} {rest : List (Finset ℕ)}
    {n : ℕ} :
    HasFactorInAll (P :: rest) n
      ↔ 0 < (P.filter (· ∣ n)).card ∧ HasFactorInAll rest n := by
  constructor
  · intro h
    exact ⟨h P (List.mem_cons_self ..), fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)⟩
  · rintro ⟨h1, h2⟩ Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ'
    · exact h1
    · exact h2 Q hQ'

/-- Membership is antitone in the family: fewer levels, weaker demand. -/
theorem HasFactorInAll.of_sublist {levels levels' : List (Finset ℕ)}
    (hsub : List.Sublist levels' levels) {n : ℕ}
    (h : HasFactorInAll levels n) :
    HasFactorInAll levels' n :=
  fun P hP => h P (hsub.subset hP)

/-- **The typical set** over a range: the [mrt] `𝒮` as a `Finset`. -/
def typicalS (a b : ℕ) (levels : List (Finset ℕ)) : Finset ℕ :=
  (Finset.Ioc a b).filter (HasFactorInAll levels)

@[simp] theorem mem_typicalS {a b n : ℕ} {levels : List (Finset ℕ)} :
    n ∈ typicalS a b levels
      ↔ (a < n ∧ n ≤ b) ∧ HasFactorInAll levels n := by
  simp [typicalS, Finset.mem_filter, Finset.mem_Ioc]

theorem typicalS_subset_Ioc (a b : ℕ) (levels : List (Finset ℕ)) :
    typicalS a b levels ⊆ Finset.Ioc a b :=
  Finset.filter_subset _ _

/-- Peeling one level: the typical set for `P :: rest` is the
`𝒰`-filter of the typical set for `rest` — the shape the `uBound`
recursion consumes. -/
theorem typicalS_cons (a b : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) :
    typicalS a b (P :: rest)
      = (typicalS a b rest).filter
          (fun n => 0 < (P.filter (· ∣ n)).card) := by
  ext n
  simp only [mem_typicalS, Finset.mem_filter, hasFactorInAll_cons]
  tauto

/-- The complement split at one level: the `rest`-typical numbers
missing a factor in `P` — the per-level exceptional set the density
estimate prices. -/
theorem typicalS_sdiff_cons (a b : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) :
    typicalS a b rest \ typicalS a b (P :: rest)
      = (typicalS a b rest).filter
          (fun n => (P.filter (· ∣ n)).card = 0) := by
  ext n
  simp only [Finset.mem_sdiff, mem_typicalS, Finset.mem_filter,
    hasFactorInAll_cons]
  constructor
  · rintro ⟨⟨hr, hall⟩, hnot⟩
    refine ⟨⟨hr, hall⟩, ?_⟩
    by_contra hne
    exact hnot ⟨⟨hr.1, hr.2⟩, ⟨Nat.pos_of_ne_zero hne, hall⟩⟩
  · rintro ⟨⟨hr, hall⟩, hzero⟩
    exact ⟨⟨hr, hall⟩, fun hcon => by omega⟩


open Real Finset in
/-- **The sifted set is log-thin** (Track R, A2-I): for any `ε > 0`
there is a mass threshold `E₀` such that any prime block `P` of mass
`≥ E₀` (with the Turán–Kubilius side conditions) has

  `∑_{n < N, no factor in P} 1/n ≤ ε·log N`.

An integer with no block factor has `|ω_P/E − 1| = 1`, so the
Turán–Kubilius deviation sum dominates the sifted log-average term by
term — the `[mrt]` Lemma-"excep" analogue in the `ε`-form the EDP
consumer runs on, with no sieve anywhere. -/
theorem sifted_logavg_le (ε : ℝ) (hε : 0 < ε) :
    ∃ E₀ : ℝ, 0 < E₀ ∧ ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ N Pmax : ℕ, (∀ p ∈ P, p ≤ Pmax) → 2*Pmax ≤ N →
      E₀ ≤ ∑ p ∈ P, (1:ℝ)/p →
      (∑ p ∈ P, (1:ℝ)/p) ≤ Real.log N →
      Real.log (Pmax+1) ≤ Real.log N →
      1 ≤ Real.log N →
      ∑ n ∈ (Finset.Ico 1 N).filter
          (fun n => (P.filter (· ∣ n)).card = 0), (1:ℝ)/n
        ≤ ε * Real.log N := by
  obtain ⟨E₀, hE₀0, hTK⟩ := turan_kubilius_block ε hε
  refine ⟨E₀, hE₀0, ?_⟩
  intro P hP N Pmax hPle h2P hE hEA hBA hA1
  have hE0 : (0:ℝ) < ∑ p ∈ P, (1:ℝ)/p := lt_of_lt_of_le hE₀0 hE
  have htk := hTK P hP N Pmax hPle h2P hE hEA hBA hA1
  refine le_trans ?_ htk
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 N)
    (fun n => (P.filter (· ∣ n)).card = 0)
    (fun n => |((P.filter (· ∣ n)).card : ℝ)/(∑ p ∈ P, (1:ℝ)/p) - 1| / n)]
  have hmatch : ∑ n ∈ (Finset.Ico 1 N).filter
      (fun n => (P.filter (· ∣ n)).card = 0), (1:ℝ)/n
      = ∑ n ∈ (Finset.Ico 1 N).filter
          (fun n => (P.filter (· ∣ n)).card = 0),
          |((P.filter (· ∣ n)).card : ℝ)/(∑ p ∈ P, (1:ℝ)/p) - 1| / n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_filter] at hn
    rw [hn.2]
    rw [show ((0:ℕ):ℝ)/(∑ p ∈ P, (1:ℝ)/p) - 1 = -1 by simp]
    norm_num
  rw [hmatch]
  have hrest : (0:ℝ) ≤ ∑ n ∈ (Finset.Ico 1 N).filter
      (fun n => ¬ (P.filter (· ∣ n)).card = 0),
      |((P.filter (· ∣ n)).card : ℝ)/(∑ p ∈ P, (1:ℝ)/p) - 1| / n :=
    Finset.sum_nonneg fun n _ => by positivity
  linarith

open Real Finset in
/-- **The typical set's complement is log-thin** (Track R, A2-I): the
multi-level telescope over `sifted_logavg_le` — for any `ε > 0` there
is a mass threshold `E₀` such that any family of prime blocks, each of
mass `≥ E₀` (with the Turán–Kubilius side conditions), has

  `∑_{n < N, n ∉ 𝒮} 1/n ≤ (#levels)·ε·log N`.

Missing membership means missing some level, and each level's
exceptional set is priced by `sifted_logavg_le`. -/
theorem typicalS_complement_logavg_le (ε : ℝ) (hε : 0 < ε) :
    ∃ E₀ : ℝ, 0 < E₀ ∧ ∀ levels : List (Finset ℕ),
      (∀ P ∈ levels, ∀ p ∈ P, p.Prime) →
      ∀ N Pmax : ℕ, (∀ P ∈ levels, ∀ p ∈ P, p ≤ Pmax) → 2*Pmax ≤ N →
      (∀ P ∈ levels, E₀ ≤ ∑ p ∈ P, (1:ℝ)/p) →
      (∀ P ∈ levels, (∑ p ∈ P, (1:ℝ)/p) ≤ Real.log N) →
      Real.log (Pmax+1) ≤ Real.log N →
      1 ≤ Real.log N →
      ∑ n ∈ (Finset.Ico 1 N).filter
          (fun n => ¬ HasFactorInAll levels n), (1:ℝ)/n
        ≤ (levels.length : ℝ) * ε * Real.log N := by
  obtain ⟨E₀, hE₀0, hsift⟩ := sifted_logavg_le ε hε
  refine ⟨E₀, hE₀0, ?_⟩
  intro levels
  induction levels with
  | nil =>
      intro _ N Pmax _ _ _ _ _ _
      simp
  | cons P rest ih =>
      intro hPr N Pmax hPle h2P hE hEA hBA hA1
      have hPr' : ∀ Q ∈ rest, ∀ p ∈ Q, p.Prime :=
        fun Q hQ => hPr Q (List.mem_cons_of_mem _ hQ)
      have hPle' : ∀ Q ∈ rest, ∀ p ∈ Q, p ≤ Pmax :=
        fun Q hQ => hPle Q (List.mem_cons_of_mem _ hQ)
      have hE' : ∀ Q ∈ rest, E₀ ≤ ∑ p ∈ Q, (1:ℝ)/p :=
        fun Q hQ => hE Q (List.mem_cons_of_mem _ hQ)
      have hEA' : ∀ Q ∈ rest, (∑ p ∈ Q, (1:ℝ)/p) ≤ Real.log N :=
        fun Q hQ => hEA Q (List.mem_cons_of_mem _ hQ)
      have hrest := ih hPr' N Pmax hPle' h2P hE' hEA' hBA hA1
      have hhead := hsift P (hPr P (List.mem_cons_self ..)) N Pmax
        (hPle P (List.mem_cons_self ..)) h2P
        (hE P (List.mem_cons_self ..)) (hEA P (List.mem_cons_self ..))
        hBA hA1
      -- the union bound: missing `P :: rest` means missing `P` or missing `rest`
      have hsub : (Finset.Ico 1 N).filter
          (fun n => ¬ HasFactorInAll (P :: rest) n)
          ⊆ ((Finset.Ico 1 N).filter
              (fun n => (P.filter (· ∣ n)).card = 0))
            ∪ ((Finset.Ico 1 N).filter
              (fun n => ¬ HasFactorInAll rest n)) := by
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        rw [hasFactorInAll_cons, not_and_or] at hn
        rcases hn.2 with h | h
        · exact Or.inl ⟨hn.1, by omega⟩
        · exact Or.inr ⟨hn.1, h⟩
      have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => by positivity :
          ∀ n ∈ ((Finset.Ico 1 N).filter
              (fun n => (P.filter (· ∣ n)).card = 0))
            ∪ ((Finset.Ico 1 N).filter
              (fun n => ¬ HasFactorInAll rest n)),
            n ∉ (Finset.Ico 1 N).filter
              (fun n => ¬ HasFactorInAll (P :: rest) n) → (0:ℝ) ≤ 1/n)
      have hunion : ∑ n ∈ ((Finset.Ico 1 N).filter
            (fun n => (P.filter (· ∣ n)).card = 0))
          ∪ ((Finset.Ico 1 N).filter
            (fun n => ¬ HasFactorInAll rest n)), (1:ℝ)/n
          ≤ (∑ n ∈ (Finset.Ico 1 N).filter
              (fun n => (P.filter (· ∣ n)).card = 0), (1:ℝ)/n)
            + ∑ n ∈ (Finset.Ico 1 N).filter
              (fun n => ¬ HasFactorInAll rest n), (1:ℝ)/n := by
        have hui := Finset.sum_union_inter
          (s₁ := (Finset.Ico 1 N).filter
            (fun n => (P.filter (· ∣ n)).card = 0))
          (s₂ := (Finset.Ico 1 N).filter
            (fun n => ¬ HasFactorInAll rest n))
          (f := fun n => (1:ℝ)/n)
        have hint : (0:ℝ) ≤ ∑ n ∈ ((Finset.Ico 1 N).filter
            (fun n => (P.filter (· ∣ n)).card = 0))
          ∩ ((Finset.Ico 1 N).filter
            (fun n => ¬ HasFactorInAll rest n)), (1:ℝ)/n :=
          Finset.sum_nonneg fun n _ => by positivity
        linarith
      have hlen : ((P :: rest).length : ℝ) = (rest.length : ℝ) + 1 := by
        simp
      rw [hlen]
      calc ∑ n ∈ (Finset.Ico 1 N).filter
            (fun n => ¬ HasFactorInAll (P :: rest) n), (1:ℝ)/n
          ≤ _ := hmono
        _ ≤ _ := hunion
        _ ≤ ε * Real.log N + (rest.length : ℝ) * ε * Real.log N := by
            linarith [hhead, hrest]
        _ = ((rest.length : ℝ) + 1) * ε * Real.log N := by ring

/-- **The log-phase character is completely multiplicative** (Track R,
A2-III, N3-f0): `e(−ξ·log(pm)) = e(−ξ·log p)·e(−ξ·log m)` — the glue
that lets complete multiplicativity of the coefficients factor a
Ramaré fibre through the phase. -/
theorem char_mul (p m : ℕ) (hp : 0 < p) (hm : 0 < m) (ξ : ℝ) :
    ((Real.fourierChar (-(Real.log (p*m : ℕ) * ξ)) : Circle) : ℂ)
      = ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
  have hp0 : ((p:ℝ)) ≠ 0 := by exact_mod_cast hp.ne'
  have hm0 : ((m:ℝ)) ≠ 0 := by exact_mod_cast hm.ne'
  have hlog : Real.log ((p:ℝ)*(m:ℝ)) = Real.log p + Real.log m :=
    Real.log_mul hp0 hm0
  rw [Real.fourierChar_apply, Real.fourierChar_apply,
    Real.fourierChar_apply, ← Complex.exp_add]
  congr 1
  push_cast
  rw [hlog]
  push_cast
  ring

open Finset in
/-- **The typical band polynomial splits main + collision** (Track R,
A2-III, N3-f): peeling one `𝒰`-level, the `1/n`-normalized phase
polynomial over `typicalS (P :: rest)` factors — each main fibre is
the prime phase `(g p/p)·e(−ξ log p)` times the `1/(ω_P+1)`-weighted
quotient polynomial, and the collision term keeps its raw
`1/ω_P`-weight.  `subset_sum_omega_pos_eq_main_add_coll` through
`typicalS_cons`, with complete multiplicativity and `char_mul`
factoring the fibres. -/
theorem typicalS_phase_main_add_coll (g : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC g) (A Δ : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (rest : List (Finset ℕ)) (ξ : ℝ) :
    ∑ m ∈ typicalS A (A+Δ) (P :: rest),
        (g m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
      = (∑ p ∈ P, (g p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)
            * ∑ m' ∈ (((typicalS A (A+Δ) rest).filter
                  (fun n => p ∣ n)).image (· / p)).filter
                (fun m' => ¬ p ∣ m'),
              ((g m'/(m':ℂ))
                  * ((Real.fourierChar (-(Real.log m' * ξ)) : Circle) : ℂ))
                / (((P.filter (· ∣ m')).card : ℂ) + 1))
        + ∑ p ∈ P, ∑ m' ∈ (((typicalS A (A+Δ) rest).filter
              (fun n => p ∣ n)).image (· / p)).filter (fun m' => p ∣ m'),
            ((g (p*m')/((p*m' : ℕ):ℂ))
                * ((Real.fourierChar (-(Real.log (p*m' : ℕ) * ξ))
                  : Circle) : ℂ))
              / (((P.filter (· ∣ (p*m'))).card : ℂ)) := by
  classical
  have hkey := subset_sum_omega_pos_eq_main_add_coll
    (typicalS A (A+Δ) rest) P hP
    (fun m => (g m/(m:ℂ))
      * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
  rw [typicalS_cons, hkey]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp2 : 2 ≤ p := (hP p hp).two_le
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' hm' => ?_
  rw [Finset.mem_filter, Finset.mem_image] at hm'
  obtain ⟨⟨n, hn, rfl⟩, hnd⟩ := hm'
  rw [Finset.mem_filter] at hn
  have hnA : A < n := by
    have := (mem_typicalS.mp hn.1).1
    exact this.1
  have hn0 : 0 < n := by omega
  have hm'0 : 0 < n / p :=
    Nat.div_pos (Nat.le_of_dvd hn0 hn.2) (by omega)
  have hgm : g (p * (n/p)) = g p * g (n/p) :=
    hcm p (n/p) (by omega) hm'0.ne'
  have hcast : ((p * (n/p) : ℕ) : ℂ) = (p:ℂ) * ((n/p : ℕ):ℂ) := by
    push_cast
    ring
  have hchar := char_mul p (n/p) (by omega) hm'0 ξ
  rw [hgm, hcast, hchar]
  ring


/-- **The sifted term vanishes on the typical set** (Track R, A2-III,
II-0): a number typical for `P :: rest` has, by definition, a prime
factor in `P`, so the `P`-sifted part of `typicalS` is empty.

In `[MR]`'s decomposition lemma the analogous term is a genuine error
`∑_{(n, ∏_{P≤p≤Q} p) = 1} |a_n|²/n`; restricting the coefficients to
`𝒮` kills it outright at every level of the ladder.  Only the
exceptional-frequency treatment, whose prime range is unrelated to
`𝒮`, still pays for it. -/
theorem typicalS_filter_card_eq_zero_eq_empty (a b : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) :
    (typicalS a b (P :: rest)).filter
        (fun n => (P.filter (· ∣ n)).card = 0) = ∅ := by
  classical
  ext n
  simp only [Finset.mem_filter, mem_typicalS, hasFactorInAll_cons,
    Finset.notMem_empty, iff_false, not_and]
  rintro ⟨-, hpos, -⟩
  omega

end MoltResearch
