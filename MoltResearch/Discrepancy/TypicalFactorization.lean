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


/-! ## e-adic prime cells (Track R, A2-III) -/

/-- **The e-adic cell** at resolution `N` and index `v`: the primes of
`P` with `⌊N·log p⌋ = v`, i.e. `e^{v/N} ≤ p < e^{(v+1)/N}`.

The cell is defined by the *natural-number* floor equation rather than
by the two real inequalities: membership is then decidable by `rfl`,
distinct cells are disjoint by construction, and the analytic bounds
are recovered on demand by `eadicCell_bounds`.  `[MR]` splits the
prime range into exactly these cells before applying the mean value
theorem, so that every prime in a cell contributes the same scale. -/
noncomputable def eadicCell (P : Finset ℕ) (N v : ℕ) : Finset ℕ :=
  P.filter (fun p => ⌊(N:ℝ) * Real.log p⌋₊ = v)

@[simp] theorem mem_eadicCell {P : Finset ℕ} {N v p : ℕ} :
    p ∈ eadicCell P N v ↔ p ∈ P ∧ ⌊(N:ℝ) * Real.log p⌋₊ = v := by
  simp [eadicCell, Finset.mem_filter]

/-- Distinct cells are disjoint — immediate from the defining
equation. -/
theorem eadicCell_disjoint (P : Finset ℕ) (N : ℕ) {v w : ℕ} (hvw : v ≠ w) :
    Disjoint (eadicCell P N v) (eadicCell P N w) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [mem_eadicCell] at hp hp'
  exact hvw (hp.2.symm.trans hp'.2)

/-- **The cells cover the prime range**: every prime whose index is at
most `V` lies in one of the cells `0, …, V`. -/
theorem eadicCell_biUnion (P : Finset ℕ) (N V : ℕ)
    (hV : ∀ p ∈ P, ⌊(N:ℝ) * Real.log p⌋₊ ≤ V) :
    (Finset.range (V+1)).biUnion (eadicCell P N) = P := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_range, mem_eadicCell]
  constructor
  · rintro ⟨v, -, hp, -⟩
    exact hp
  · intro hp
    exact ⟨⌊(N:ℝ) * Real.log p⌋₊, Nat.lt_succ_of_le (hV p hp), hp, rfl⟩

/-- **The analytic content of a cell**: its primes lie in the
multiplicative window `[e^{v/N}, e^{(v+1)/N})`. -/
theorem eadicCell_bounds {P : Finset ℕ} {N v p : ℕ} (hN : 0 < N)
    (hp : p ∈ eadicCell P N v) (hp1 : 1 ≤ p) :
    Real.exp ((v:ℝ)/N) ≤ (p:ℝ) ∧ (p:ℝ) < Real.exp (((v:ℝ)+1)/N) := by
  rw [mem_eadicCell] at hp
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp1
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp1)
  have hfl : ((v:ℝ)) ≤ (N:ℝ) * Real.log p ∧
      (N:ℝ) * Real.log p < (v:ℝ) + 1 := by
    have hnn : (0:ℝ) ≤ (N:ℝ) * Real.log p := by positivity
    have := Nat.floor_eq_iff hnn |>.mp hp.2
    exact ⟨this.1, this.2⟩
  constructor
  · rw [← Real.exp_log hp0]
    refine Real.exp_le_exp.2 ?_
    rw [div_le_iff₀ hN0]
    linarith [hfl.1]
  · rw [← Real.exp_log hp0]
    refine Real.exp_lt_exp.2 ?_
    rw [lt_div_iff₀ hN0]
    linarith [hfl.2]


/-- **Two primes of one cell give quotient windows within a collar**
(Track R, A2-III, II-2b): if `q ≤ p` and `N·p ≤ (N+1)·q` — the primes
sit within a factor `1 + 1/N` of each other — then the two quotient
windows start within

  `A/q ≤ A/p + A/(N·p) + 1`

of each other.  The `+1` is the cost of the two `ℕ`-division floors; the
main term `A/(N·p)` is the `1/N`-fraction of the window `A/p` that the
`[MR]` telescoping pays as a collar.

Everything here is `ℕ`-division: `A/p` is `⌊A/p⌋`, and the statement is
exactly the input `sum_Ioc_eq_sum_Ioc_add_collars` needs to know its
collars are short. -/
theorem div_le_div_add_div_add_one (A N p q : ℕ) (hN : 0 < N) (hq : 0 < q)
    (hqp : q ≤ p) (hratio : N * p ≤ (N+1) * q) :
    A / q ≤ A / p + A / (N * p) + 1 := by
  have hp : 0 < p := lt_of_lt_of_le hq hqp
  have hQ0 : (0:ℝ) < q := by exact_mod_cast hq
  have hP0 : (0:ℝ) < p := by exact_mod_cast hp
  have hn0 : (0:ℝ) < N := by exact_mod_cast hN
  have hA0 : (0:ℝ) ≤ A := Nat.cast_nonneg A
  have hr : ((N:ℝ)) * p ≤ ((N:ℝ)+1) * q := by exact_mod_cast hratio
  -- the real inequality: `a/q = (a/p)·(p/q) ≤ (a/p)·(1 + 1/N)`
  have hkey : (A:ℝ)/(q:ℝ) ≤ (A:ℝ)/(p:ℝ) + (A:ℝ)/((N:ℝ)*(p:ℝ)) := by
    rw [div_add_div _ _ (ne_of_gt hP0) (by positivity),
      div_le_div_iff₀ hQ0 (by positivity)]
    have hexp : (A:ℝ) * ((p:ℝ) * ((N:ℝ) * (p:ℝ)))
        = ((A:ℝ) * (p:ℝ)) * ((N:ℝ) * (p:ℝ)) := by ring
    nlinarith [mul_nonneg hA0 (le_of_lt hP0), mul_pos hP0 hn0,
      mul_le_mul_of_nonneg_left hr (mul_nonneg hA0 (le_of_lt hP0))]
  -- floor bridges
  have hAq : ((A/q : ℕ):ℝ) ≤ (A:ℝ)/(q:ℝ) := Nat.cast_div_le
  have hfloor : ∀ m : ℕ, 0 < m → (A:ℝ)/(m:ℝ) < ((A/m : ℕ):ℝ) + 1 := by
    intro m hm
    have hM0 : (0:ℝ) < m := by exact_mod_cast hm
    have hmod : A < m * (A/m) + m := by
      have := Nat.div_add_mod A m
      have hlt := Nat.mod_lt A hm
      omega
    have hcast : (A:ℝ) < (m:ℝ) * ((A/m : ℕ):ℝ) + (m:ℝ) := by exact_mod_cast hmod
    rw [div_lt_iff₀ hM0]
    linarith
  have hAp := hfloor p hp
  have hANp := hfloor (N*p) (Nat.mul_pos hN hp)
  have hcastNp : (((N*p : ℕ)):ℝ) = (N:ℝ)*(p:ℝ) := by push_cast; ring
  rw [hcastNp] at hANp
  have hfin : ((A/q : ℕ):ℝ) < ((A/p : ℕ):ℝ) + ((A/(N*p) : ℕ):ℝ) + 2 := by
    linarith
  have : A/q < A/p + A/(N*p) + 2 := by exact_mod_cast hfin
  omega

/-- **Primes of one cell are within a factor `1 + 1/N`** (Track R,
A2-III, II-2b): the e-adic cell at resolution `2N` has multiplicative
width `e^{1/(2N)} ≤ 1 + 1/N`, so any two of its members satisfy the
purely arithmetic ratio bound `N·p ≤ (N+1)·q`.

The doubled resolution is what makes the bound *arithmetic*: at
resolution `N` the cell width is `e^{1/N}`, which exceeds `1 + 1/N`, and
no `ℕ`-inequality of this shape would hold.  Halving the cell buys the
slack, and costs only a factor `2` in the number of cells. -/
theorem eadicCell_ratio_le {P : Finset ℕ} {N v p q : ℕ} (hN : 0 < N)
    (hp : p ∈ eadicCell P (2*N) v) (hq : q ∈ eadicCell P (2*N) v)
    (hp1 : 1 ≤ p) (hq1 : 1 ≤ q) :
    N * p ≤ (N+1) * q := by
  have hN2 : 0 < 2*N := by omega
  obtain ⟨-, hpub⟩ := eadicCell_bounds hN2 hp hp1
  obtain ⟨hqlb, -⟩ := eadicCell_bounds hN2 hq hq1
  have hn0 : (0:ℝ) < N := by exact_mod_cast hN
  have hcast : ((2*N : ℕ):ℝ) = 2*(N:ℝ) := by push_cast; ring
  rw [hcast] at hpub hqlb
  -- `e^{(v+1)/(2N)} = e^{v/(2N)}·e^{1/(2N)}`
  have hsplit : ((v:ℝ)+1)/(2*(N:ℝ)) = (v:ℝ)/(2*(N:ℝ)) + 1/(2*(N:ℝ)) := by
    field_simp
  -- `e^{1/(2N)} ≤ 1 + 1/N`
  have hx0 : (0:ℝ) < 1/(2*(N:ℝ)) := by positivity
  have hx1 : |1/(2*(N:ℝ))| ≤ 1 := by
    rw [abs_of_pos hx0]
    rw [div_le_one (by positivity)]
    have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  have hexp : Real.exp (1/(2*(N:ℝ))) ≤ 1 + 1/(N:ℝ) := by
    have habs := Real.abs_exp_sub_one_le hx1
    have h1 := (abs_le.mp habs).2
    rw [abs_of_pos hx0] at h1
    have : (2:ℝ) * (1/(2*(N:ℝ))) = 1/(N:ℝ) := by field_simp
    linarith
  have hexpq : Real.exp ((v:ℝ)/(2*(N:ℝ))) ≤ (q:ℝ) := hqlb
  have hexppos : (0:ℝ) < Real.exp ((v:ℝ)/(2*(N:ℝ))) := Real.exp_pos _
  have hchain : (p:ℝ) < (q:ℝ) * (1 + 1/(N:ℝ)) := by
    calc (p:ℝ) < Real.exp (((v:ℝ)+1)/(2*(N:ℝ))) := hpub
      _ = Real.exp ((v:ℝ)/(2*(N:ℝ))) * Real.exp (1/(2*(N:ℝ))) := by
          rw [hsplit, Real.exp_add]
      _ ≤ (q:ℝ) * (1 + 1/(N:ℝ)) := by
          refine mul_le_mul hexpq hexp (le_of_lt (by positivity)) ?_
          exact le_trans (le_of_lt hexppos) hexpq
  have hfinal : (N:ℝ) * (p:ℝ) < ((N:ℝ)+1) * (q:ℝ) := by
    have hq0 : (0:ℝ) < q := by exact_mod_cast hq1
    have := mul_lt_mul_of_pos_left hchain hn0
    calc (N:ℝ) * (p:ℝ) < (N:ℝ) * ((q:ℝ) * (1 + 1/(N:ℝ))) := this
      _ = ((N:ℝ)+1) * (q:ℝ) := by field_simp
  have : N * p < (N+1) * q := by exact_mod_cast hfinal
  omega

open Finset in
/-- **The one-step convolution of phase polynomials** (Track R,
A2-III, III-0): the product of two `1/n`-normalised phase polynomials
is the phase polynomial of the product support —

  `(∑_{m∈S} (a m/m)·e(−ξ log m))·(∑_{p∈Y} (b p/p)·e(−ξ log p))
     = ∑_{(m,p) ∈ S ×ˢ Y} (a m·b p/(mp))·e(−ξ log(mp))`.

Iterating this is how the `ℓ`-th power of a prime polynomial becomes a
Dirichlet polynomial supported on `ℓ`-fold products, which is what the
`[MR]` moment computation needs.  Stated over `S ×ˢ Y` rather than
over the image: collapsing the fibres (with their `ℓ!`-multiplicity)
is a separate, purely combinatorial step. -/
theorem phase_poly_mul (S Y : Finset ℕ) (a b : ℕ → ℂ)
    (hS : ∀ m ∈ S, 0 < m) (hY : ∀ p ∈ Y, 0 < p) (ξ : ℝ) :
    (∑ m ∈ S, (a m/(m:ℂ))
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
      * (∑ p ∈ Y, (b p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
      = ∑ q ∈ S ×ˢ Y, ((a q.1 * b q.2)/(((q.1 * q.2 : ℕ)):ℂ))
          * ((Real.fourierChar (-(Real.log ((q.1 * q.2 : ℕ)) * ξ)) : Circle) : ℂ) := by
  classical
  rw [Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_product] at hq
  have hm0 : 0 < q.1 := hS q.1 hq.1
  have hp0 : 0 < q.2 := hY q.2 hq.2
  have hmc : ((q.1 : ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0.ne'
  have hpc : ((q.2 : ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp0.ne'
  rw [char_mul q.1 q.2 hm0 hp0 ξ]
  have hcast : (((q.1 * q.2 : ℕ)):ℂ) = ((q.1 : ℕ):ℂ) * ((q.2 : ℕ):ℂ) := by
    push_cast
    ring
  rw [hcast]
  field_simp


open Finset in
/-- **The log-phase character over a product** (Track R, A2-III,
III-0b): `∏ᵢ e(−ξ·log vᵢ) = e(−ξ·log ∏ᵢ vᵢ)` — `char_mul` iterated over
a `Finset`.

Positivity is required of every `v i`, not only of those in `s`, so that
the induction on `s` needs no side condition; at the call sites `v`
takes its values in a `Finset` of primes, where this is free. -/
theorem char_prod {ι : Type*} (v : ι → ℕ) (hv : ∀ i, 0 < v i) (ξ : ℝ)
    (s : Finset ι) :
    (∏ i ∈ s, ((Real.fourierChar (-(Real.log (v i) * ξ)) : Circle) : ℂ))
      = ((Real.fourierChar (-(Real.log ((∏ i ∈ s, v i : ℕ)) * ξ))
          : Circle) : ℂ) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.prod_cons, ih,
        char_mul (v a) (∏ i ∈ s, v i) (hv a)
          (Finset.prod_pos fun i _ => hv i) ξ]

open Finset in
/-- **The `ℓ`-th power of a prime polynomial** (Track R, A2-III,
III-0b): the `ℓ`-fold iterate of `phase_poly_mul`, in closed form —

  `(∑_{p∈Y} (b p/p)·e(−ξ log p))^ℓ
     = ∑_{v ∈ Y^ℓ} ((∏ᵢ b vᵢ)/∏ᵢ vᵢ)·e(−ξ log ∏ᵢ vᵢ)`.

No induction is needed: the power is a constant product, and
`Finset.prod_univ_sum` — the distributive law over a `piFinset` — expands
it in one step.  `char_prod` then moves the phase onto the product index
and `Finset.prod_div_distrib` collects the `1/n` normalisation.

With `phase_poly_fiberwise` this is the `2ℓ`-th moment's first half: the
power is a Dirichlet polynomial supported on `ℓ`-fold products, whose
coefficients `card_prime_tuple_fiber_le` bounds by `ℓ!` and whose
harmonic mass `sum_one_div_image_prod_le` bounds by `(∑_{p∈Y} 1/p)^ℓ`. -/
theorem phase_poly_pow (Y : Finset ℕ) (b : ℕ → ℂ) (hY : ∀ p ∈ Y, 0 < p)
    (ℓ : ℕ) (ξ : ℝ) :
    (∑ p ∈ Y, (b p/(p:ℂ))
        * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))^ℓ
      = ∑ v ∈ Fintype.piFinset (fun _ : Fin ℓ => Y),
          ((∏ i, b (v i))/(((∏ i, v i : ℕ)):ℂ))
            * ((Real.fourierChar (-(Real.log ((∏ i, v i : ℕ)) * ξ))
                : Circle) : ℂ) := by
  classical
  have hpow : (∑ p ∈ Y, (b p/(p:ℂ))
      * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))^ℓ
      = ∏ _i : Fin ℓ, (∑ p ∈ Y, (b p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Fintype.mem_piFinset] at hv
  -- extend the coordinates to a globally positive function
  have hvpos : ∀ i, 0 < (if h : v i ∈ Y then v i else 1) := by
    intro i
    split_ifs with h
    · exact hY _ h
    · exact Nat.one_pos
  have hveq : ∀ i, (if h : v i ∈ Y then v i else 1) = v i := by
    intro i
    rw [dif_pos (hv i)]
  have hchar := char_prod (fun i => if h : v i ∈ Y then v i else 1) hvpos ξ
    (Finset.univ : Finset (Fin ℓ))
  simp only [hveq] at hchar
  rw [Finset.prod_mul_distrib, hchar, Finset.prod_div_distrib]
  push_cast
  ring

open Finset in
/-- **The fibre collapse** (Track R, A2-III, III-1a): a phase sum
indexed by pairs is the phase polynomial whose coefficient at `n` is
the total weight of the fibre over `n` —

  `∑_{q ∈ s} (a q/(q₁q₂))·e(−ξ log(q₁q₂))
     = ∑_{n ∈ T} ((∑_{q : q₁q₂ = n} a q)/n)·e(−ξ log n)`.

This is the bridge from the convolution form of `phase_poly_mul`,
which is indexed by tuples, to the `∑_{n} (c n/n)·e(−ξ log n)` shape
that the mean value theorem consumes.  All the multiplicity of
representations is now visible in one place: the fibre cardinality. -/
theorem phase_poly_fiberwise (s : Finset (ℕ × ℕ)) (T : Finset ℕ)
    (hmaps : ∀ q ∈ s, q.1 * q.2 ∈ T) (a : ℕ × ℕ → ℂ) (ξ : ℝ) :
    ∑ q ∈ s, (a q/(((q.1 * q.2 : ℕ)):ℂ))
        * ((Real.fourierChar (-(Real.log ((q.1 * q.2 : ℕ)) * ξ)) : Circle) : ℂ)
      = ∑ n ∈ T, ((∑ q ∈ s.filter (fun q => q.1 * q.2 = n), a q)/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun q => (a q/(((q.1 * q.2 : ℕ)):ℂ))
      * ((Real.fourierChar (-(Real.log ((q.1 * q.2 : ℕ)) * ξ)) : Circle) : ℂ))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_filter] at hq
  rw [hq.2]

open Finset in
/-- **The fibre collapse, at a general index** (Track R, A2-III,
III-1e): `phase_poly_fiberwise` with an arbitrary index type and an
arbitrary map to the support —

  `∑_{q∈s} (a q/φ q)·e(−ξ log φ q)
     = ∑_{n∈T} ((∑_{q∈s, φ q = n} a q)/n)·e(−ξ log n)`.

The `ℓ`-fold moment needs the index `Fin ℓ → ℕ` and the map
`v ↦ ∏ᵢ vᵢ`, which the pair version cannot express. -/
theorem phase_poly_fiberwise' {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (φ : ι → ℕ) (T : Finset ℕ) (hmaps : ∀ q ∈ s, φ q ∈ T) (a : ι → ℂ)
    (ξ : ℝ) :
    ∑ q ∈ s, (a q/((φ q : ℕ):ℂ))
        * ((Real.fourierChar (-(Real.log (φ q) * ξ)) : Circle) : ℂ)
      = ∑ n ∈ T, ((∑ q ∈ s.filter (fun q => φ q = n), a q)/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun q => (a q/((φ q : ℕ):ℂ))
      * ((Real.fourierChar (-(Real.log (φ q) * ξ)) : Circle) : ℂ))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [(Finset.mem_filter.mp hq).2]

open Finset in
/-- **The fibre coefficient bound** (Track R, A2-III, III-1b): the
collapsed coefficient at `n` is at most the fibre cardinality times
the pointwise weight bound.  The `[MR]` moment computation supplies
`ℓ!` for that cardinality when the fibres are `ℓ`-fold products of
primes from a dyadic range. -/
theorem norm_sum_fiber_le (s : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (ha : ∀ q, ‖a q‖ ≤ B) (n : ℕ) :
    ‖∑ q ∈ s.filter (fun q => q.1 * q.2 = n), a q‖
      ≤ ((s.filter (fun q => q.1 * q.2 = n)).card : ℝ) * B := by
  classical
  calc ‖∑ q ∈ s.filter (fun q => q.1 * q.2 = n), a q‖
      ≤ ∑ q ∈ s.filter (fun q => q.1 * q.2 = n), ‖a q‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _q ∈ s.filter (fun q => q.1 * q.2 = n), B :=
        Finset.sum_le_sum fun q _ => ha q
    _ = ((s.filter (fun q => q.1 * q.2 = n)).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]


open Finset in
/-- **A product of two primes has at most two ordered factorisations**
(Track R, A2-III, III-1c): the fibre of `(p,q) ↦ pq` over any `n`,
within a product of two prime sets, has at most two elements.

This is the `ℓ = 2` case of the multiplicity bound the moment
computation needs (`ℓ!` ordered representations of an `ℓ`-fold
product).  Unique factorisation does the work: if `pq = ab` with all
four prime then `p ∈ {a, b}`, and the partner is forced by
cancellation. -/
theorem card_prime_pair_fiber_le (Y Z : Finset ℕ)
    (hY : ∀ p ∈ Y, p.Prime) (hZ : ∀ q ∈ Z, q.Prime) (n : ℕ) :
    (((Y ×ˢ Z).filter (fun q => q.1 * q.2 = n)).card) ≤ 2 := by
  classical
  rcases Finset.eq_empty_or_nonempty
    ((Y ×ˢ Z).filter (fun q => q.1 * q.2 = n)) with hempty | ⟨ab, hab⟩
  · rw [hempty]
    simp
  · -- every member of the fibre is `ab` or its swap
    have habmem := hab
    rw [Finset.mem_filter, Finset.mem_product] at habmem
    obtain ⟨⟨haY, hbZ⟩, hprod⟩ := habmem
    have ha := hY _ haY
    have hb := hZ _ hbZ
    have hsub : (Y ×ˢ Z).filter (fun q => q.1 * q.2 = n)
        ⊆ {ab, (ab.2, ab.1)} := by
      intro pq hpq
      rw [Finset.mem_filter, Finset.mem_product] at hpq
      obtain ⟨⟨hpY, hqZ⟩, hpqn⟩ := hpq
      have hp := hY _ hpY
      have heq : pq.1 * pq.2 = ab.1 * ab.2 := by
        rw [hpqn, hprod]
      have hdvd : pq.1 ∣ ab.1 * ab.2 := ⟨pq.2, heq.symm⟩
      have hcase := (Nat.Prime.dvd_mul hp).mp hdvd
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases hcase with h1 | h2
      · -- `pq.1 = ab.1`, so the partners agree
        have h1' : pq.1 = ab.1 := ((Nat.prime_dvd_prime_iff_eq hp ha).mp h1)
        left
        have hpos : 0 < ab.1 := ha.pos
        have : pq.2 = ab.2 := by
          have := heq
          rw [h1'] at this
          exact Nat.eq_of_mul_eq_mul_left hpos this
        exact Prod.ext h1' this
      · -- `pq.1 = ab.2`, so `pq.2 = ab.1`
        have h2' : pq.1 = ab.2 := ((Nat.prime_dvd_prime_iff_eq hp hb).mp h2)
        right
        have hpos : 0 < ab.2 := hb.pos
        have : pq.2 = ab.1 := by
          have hcomm : ab.2 * pq.2 = ab.2 * ab.1 := by
            calc ab.2 * pq.2 = pq.1 * pq.2 := by rw [h2']
              _ = ab.1 * ab.2 := heq
              _ = ab.2 * ab.1 := by ring
          exact Nat.eq_of_mul_eq_mul_left hpos hcomm
        exact Prod.ext h2' this
    refine le_trans (Finset.card_le_card hsub) ?_
    exact le_trans (Finset.card_insert_le _ _) (by simp)


open Finset in
/-- **An `ℓ`-fold product of primes has at most `ℓ!` ordered
factorisations** (Track R, A2-III, III-1d): for a `Finset` of primes `Y`,

  `#{v ∈ Y^ℓ : ∏ᵢ vᵢ = n} ≤ ℓ!`.

The `ℓ`-fold generalisation of `card_prime_pair_fiber_le`, and the
multiplicity input to the `2ℓ`-th moment of a prime polynomial: after
`phase_poly_fiberwise` collapses `Q^ℓ` to a Dirichlet polynomial, this
bounds its coefficients.

The proof is the fundamental theorem of arithmetic packaged as
`Nat.primeFactorsList_unique`: every tuple in the fibre, read as a list,
is a permutation of `n`'s prime factorisation, `List.ofFn` is injective,
and a list of length `ℓ` has exactly `ℓ!` permutations. -/
theorem card_prime_tuple_fiber_le {ℓ : ℕ} (Y : Finset ℕ)
    (hY : ∀ p ∈ Y, p.Prime) (n : ℕ) :
    ((Fintype.piFinset fun _ : Fin ℓ => Y).filter
        (fun v => ∏ i, v i = n)).card ≤ Nat.factorial ℓ := by
  classical
  rcases Finset.eq_empty_or_nonempty
      ((Fintype.piFinset fun _ : Fin ℓ => Y).filter (fun v => ∏ i, v i = n))
    with hemp | ⟨v₀, hv₀⟩
  · rw [hemp]
    exact Nat.zero_le _
  -- every member of the fibre, read as a list, is prime-valued with product `n`
  have hprime : ∀ v ∈ (Fintype.piFinset fun _ : Fin ℓ => Y).filter
      (fun v => ∏ i, v i = n), ∀ p ∈ List.ofFn v, Nat.Prime p := by
    intro v hv p hp
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hv
    rw [List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    exact hY _ (hv.1 i)
  have hperm : ∀ v ∈ (Fintype.piFinset fun _ : Fin ℓ => Y).filter
      (fun v => ∏ i, v i = n),
        List.Perm (List.ofFn v) (Nat.primeFactorsList n) := by
    intro v hv
    refine Nat.primeFactorsList_unique ?_ (hprime v hv)
    rw [List.prod_ofFn]
    exact (Finset.mem_filter.mp hv).2
  -- the fibre is nonempty, so `n` factors into exactly `ℓ` primes
  have hlen : (Nat.primeFactorsList n).length = ℓ := by
    have := (hperm v₀ hv₀).length_eq
    rw [List.length_ofFn] at this
    exact this.symm
  have hcard : ((Fintype.piFinset fun _ : Fin ℓ => Y).filter
      (fun v => ∏ i, v i = n)).card
      ≤ ((Nat.primeFactorsList n).permutations.toFinset).card := by
    refine Finset.card_le_card_of_injOn (fun v => List.ofFn v) ?_
      (fun v _ w _ h => List.ofFn_injective h)
    intro v hv
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_permutations]
    rw [Finset.mem_coe] at hv
    exact hperm v hv
  refine le_trans hcard (le_trans (List.toFinset_card_le _) ?_)
  rw [List.length_permutations, hlen]

/-! ## The harmonic mass of a product set (Track R, A2-III, III-2a) -/

open Finset in
/-- **The harmonic mass of a product set** (Track R, A2-III, III-2a):

  `∑_{n ∈ Y·Z} 1/n ≤ (∑_{p∈Y} 1/p)·(∑_{q∈Z} 1/q)`.

This is the elementary Euler-product substitute for a Shiu-type bound in
the `[MR]` moment estimates: the support of a product of two Dirichlet
polynomials is the product set, and its harmonic mass — the quantity the
sharp mean value theorem charges for — is bounded by the product of the
two prime masses.  Collisions only help, which is why an inequality
suffices and no multiplicity count enters here.

No hypotheses: if `0 ∈ Y` the corresponding terms are `1/0 = 0` on both
sides. -/
theorem sum_one_div_image_mul_le (Y Z : Finset ℕ) :
    ∑ n ∈ (Y ×ˢ Z).image (fun q : ℕ × ℕ => q.1 * q.2), (1:ℝ)/n
      ≤ (∑ p ∈ Y, (1:ℝ)/p) * (∑ q ∈ Z, (1:ℝ)/q) := by
  classical
  refine le_trans (Finset.sum_image_le_of_nonneg (fun q _ => by positivity)) ?_
  rw [Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
  push_cast
  rw [one_div, one_div, one_div, mul_inv]

open Finset in
/-- **The harmonic mass of an `ℓ`-fold product set** (Track R, A2-III,
III-2a): for the image of `Y^ℓ` under the product map,

  `∑_{n ∈ Y^ℓ} 1/n ≤ (∑_{p∈Y} 1/p)^ℓ`.

The `ℓ`-fold version of the same estimate, and the harmonic input to the
`2ℓ`-th moment of a prime polynomial: `Q^ℓ` is supported on this set, so
the sharp mean value theorem at ratio `2^ℓ` charges exactly this mass.

The proof is `Finset.prod_univ_sum` — the distributive law for a product
of sums over a `piFinset` — after inverting the product coordinatewise.
Again no positivity hypothesis is needed: a zero coordinate makes both
sides' terms vanish. -/
theorem sum_one_div_image_prod_le (Y : Finset ℕ) (ℓ : ℕ) :
    ∑ n ∈ (Fintype.piFinset fun _ : Fin ℓ => Y).image (fun v => ∏ i, v i),
        (1:ℝ)/n
      ≤ (∑ p ∈ Y, (1:ℝ)/p)^ℓ := by
  classical
  refine le_trans (Finset.sum_image_le_of_nonneg (fun v _ => by positivity)) ?_
  have hsplit : ∀ v : Fin ℓ → ℕ,
      (1:ℝ)/((∏ i, v i : ℕ):ℝ) = ∏ i : Fin ℓ, (1:ℝ)/((v i : ℕ):ℝ) := by
    intro v
    push_cast
    simp [one_div, ← Finset.prod_inv_distrib]
  have hpow : (∑ p ∈ Y, (1:ℝ)/p)^ℓ
      = ∏ _i : Fin ℓ, (∑ p ∈ Y, (1:ℝ)/p) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow, Finset.prod_univ_sum]
  refine le_of_eq (Finset.sum_congr rfl fun v _ => hsplit v)


/-! ## The `ℓ`-fold product set, graded by `Ω` (Track R, A2-III, III-2d) -/

open Finset in
/-- **The `ℓ`-fold product set is the `Ω`-graded smooth set** (Track R,
A2-III, III-2d): for a `Finset` of primes `Y`,

  `n ∈ Y^ℓ  ↔  n ≠ 0 ∧ Ω(n) = ℓ ∧ (prime factors of n) ⊆ Y`,

with `Ω(n)` the length of `n`'s prime factorisation.  The support of
`Q^ℓ` is described here without reference to tuples, which is what makes
it closed under taking divisors — see `exists_dvd_split_image_prod`.

The `n ≠ 0` clause is not decoration: `Nat.primeFactorsList 0 = []`, so
without it `n = 0` would qualify at `ℓ = 0`, where the product set is
`{1}`.

Both directions are the fundamental theorem of arithmetic as
`Nat.primeFactorsList_unique`: a tuple read through `List.ofFn` is a
prime-valued list with product `n`, hence a permutation of `n`'s
factorisation; conversely that factorisation, read through `List.get`,
is a tuple. -/
theorem mem_image_prod_iff {ℓ : ℕ} (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (n : ℕ) :
    n ∈ (Fintype.piFinset fun _ : Fin ℓ => Y).image (fun v => ∏ i, v i)
      ↔ n ≠ 0 ∧ (Nat.primeFactorsList n).length = ℓ ∧ n.primeFactors ⊆ Y := by
  classical
  constructor
  · intro hn
    rw [Finset.mem_image] at hn
    obtain ⟨v, hv, rfl⟩ := hn
    rw [Fintype.mem_piFinset] at hv
    have hvp : ∀ i, Nat.Prime (v i) := fun i => hY _ (hv i)
    have hne : (∏ i, v i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => (hvp i).pos.ne'
    have hprime : ∀ p ∈ List.ofFn v, Nat.Prime p := by
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨i, rfl⟩ := hp
      exact hvp i
    have hperm : List.Perm (List.ofFn v)
        (Nat.primeFactorsList (∏ i, v i)) := by
      refine Nat.primeFactorsList_unique ?_ hprime
      rw [List.prod_ofFn]
    refine ⟨hne, ?_, ?_⟩
    · have hl := hperm.length_eq
      rw [List.length_ofFn] at hl
      exact hl.symm
    · intro p hp
      have hpl : p ∈ Nat.primeFactorsList (∏ i, v i) :=
        Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp
      have hpo : p ∈ List.ofFn v := (hperm.mem_iff).mpr hpl
      rw [List.mem_ofFn] at hpo
      obtain ⟨i, rfl⟩ := hpo
      exact hv i
  · rintro ⟨hne, hlen, hsub⟩
    rw [Finset.mem_image]
    subst hlen
    refine ⟨fun i => (Nat.primeFactorsList n).get i, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      refine hsub ?_
      refine Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr ?_
      exact List.get_mem _ _
    · rw [← List.prod_ofFn, List.ofFn_get]
      exact Nat.prod_primeFactorsList hne

open Finset in
/-- **The `ℓ`-fold product set splits along divisors** (Track R, A2-III,
III-2d): if `r ∈ Y^ℓ` and `d ∣ r`, then `d ∈ Y^k` and `r/d ∈ Y^{ℓ−k}`
for `k = Ω(d) ≤ ℓ`.

`k` is named, not existentially quantified.  The consumer partitions
`Y^ℓ × Y^ℓ` into the fibres of `(r,r') ↦ Ω(gcd r r')` and needs the
splitting to land in the fibre it is working in, which an existential
cannot say.

This is the structural fact the `[MR]` moment estimate needs and that a
tuple-level description cannot supply directly: a divisor of a product
of `ℓ` primes of `Y` is again such a product, of a shorter length, with
the lengths adding.  It is what lets `∑_{r,r' ∈ Y^ℓ} 1/[r,r']` be
summed against the finite ladder `Y^0, …, Y^ℓ` — writing
`[r,r'] = gcd·(r/gcd)·(r'/gcd)` and pricing each factor by
`sum_one_div_image_prod_le` — instead of by an Euler product over the
infinitely many `Y`-smooth numbers, which is the route the A2-III design
note proposed and where its constant went wrong.

Immediate from `mem_image_prod_iff`: divisibility passes to prime-factor
sets, and `Ω` is additive along `r = (r/d)·d`. -/
theorem dvd_split_image_prod {ℓ : ℕ} (Y : Finset ℕ)
    (hY : ∀ p ∈ Y, p.Prime) {r d : ℕ}
    (hr : r ∈ (Fintype.piFinset fun _ : Fin ℓ => Y).image (fun v => ∏ i, v i))
    (hd : d ∣ r) :
    (Nat.primeFactorsList d).length ≤ ℓ ∧
      d ∈ (Fintype.piFinset fun _ : Fin (Nat.primeFactorsList d).length => Y).image
            (fun v => ∏ i, v i) ∧
      r/d ∈ (Fintype.piFinset
              fun _ : Fin (ℓ - (Nat.primeFactorsList d).length) => Y).image
              (fun v => ∏ i, v i) := by
  classical
  obtain ⟨hr0, hrlen, hrsub⟩ := (mem_image_prod_iff Y hY r).mp hr
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hr0 (Nat.eq_zero_of_zero_dvd hd)
  have hmul : (r/d) * d = r := Nat.div_mul_cancel hd
  have he0 : r/d ≠ 0 := by
    intro h
    rw [← hmul, h, zero_mul] at hr0
    exact hr0 rfl
  have hperm := Nat.perm_primeFactorsList_mul he0 hd0
  rw [hmul] at hperm
  have hlen : (Nat.primeFactorsList (r/d)).length
      + (Nat.primeFactorsList d).length = ℓ := by
    have hl := hperm.length_eq
    rw [List.length_append] at hl
    omega
  refine ⟨by omega, ?_, ?_⟩
  · refine (mem_image_prod_iff Y hY d).mpr ⟨hd0, rfl, ?_⟩
    exact fun p hp => hrsub (Nat.primeFactors_mono hd hr0 hp)
  · refine (mem_image_prod_iff Y hY (r/d)).mpr ⟨he0, by omega, ?_⟩
    exact fun p hp =>
      hrsub (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hd) hr0 hp)


/-! ## The pair-divisor sum over an `ℓ`-fold product set (Track R, A2-III,
III-2e) -/

open Finset in
/-- **The pair-divisor sum over an `ℓ`-fold product set** (Track R,
A2-III, III-2e): for a `Finset` of primes `Y` of harmonic mass
`σ = ∑_{p∈Y} 1/p ≤ 1`,

  `∑_{r, r' ∈ Y^ℓ} 1/[r,r'] ≤ (ℓ+1)·σ^ℓ`.

This is the elementary substitute for Shiu's theorem in the `[MR]`
moment estimate, and it replaces the design note's route: rather than an
Euler product over the infinitely many `Y`-smooth numbers — on which the
note's constant was in any case false (#3532) — the sum is priced
against the **finite** ladder `Y^0, …, Y^ℓ`.

The mechanism.  Partition `Y^ℓ × Y^ℓ` into the fibres of
`(r,r') ↦ Ω(gcd r r')`.  On the fibre over `k`, the map

  `(r,r') ↦ (g, r/g, r'/g)`,  `g = gcd(r,r')`,

is injective — `r = g·(r/g)` recovers the pair — it lands in
`Y^k × Y^{ℓ−k} × Y^{ℓ−k}` by `dvd_split_image_prod`, and it carries
`1/[r,r']` to `1/(g·(r/g)·(r'/g))` because `g·[r,r'] = r·r'`.  So the
fibre is at most `σ^k·σ^{ℓ−k}·σ^{ℓ−k}` by `sum_one_div_image_prod_le`,
and `σ ≤ 1` collapses the exponent `k + 2(ℓ−k) ≥ ℓ` to `σ^ℓ`.  There are
`ℓ+1` fibres.

`σ ≤ 1` is the only hypothesis beyond primality, and it is harmless in
the application: `Y` is a set of primes in `(P, 2P]`, where
`σ ≍ 1/log P`. -/
theorem sum_one_div_lcm_image_prod_le (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (ℓ : ℕ) (hσ : ∑ p ∈ Y, (1:ℝ)/p ≤ 1) :
    ∑ r ∈ (Fintype.piFinset fun _ : Fin ℓ => Y).image (fun v => ∏ i, v i),
      ∑ r' ∈ (Fintype.piFinset fun _ : Fin ℓ => Y).image (fun v => ∏ i, v i),
        (1:ℝ)/(Nat.lcm r r')
      ≤ ((ℓ:ℝ)+1) * (∑ p ∈ Y, (1:ℝ)/p)^ℓ := by
  classical
  set D : ℕ → Finset ℕ :=
    fun k => (Fintype.piFinset fun _ : Fin k => Y).image (fun v => ∏ i, v i)
    with hD_def
  set σ : ℝ := ∑ p ∈ Y, (1:ℝ)/p with hσ_def
  have hσ0 : 0 ≤ σ := by
    rw [hσ_def]
    refine Finset.sum_nonneg fun p _ => by positivity
  have hDmass : ∀ k, ∑ n ∈ D k, (1:ℝ)/n ≤ σ^k := by
    intro k
    rw [hD_def, hσ_def]
    exact sum_one_div_image_prod_le Y k
  have hDne : ∀ k, ∀ n ∈ D k, n ≠ 0 := by
    intro k n hn
    exact ((mem_image_prod_iff Y hY n).mp hn).1
  -- to a sum over the product finset
  rw [← Finset.sum_product' (D ℓ) (D ℓ) (fun r r' => (1:ℝ)/(Nat.lcm r r'))]
  -- partition by `Ω(gcd)`
  set key : ℕ × ℕ → ℕ := fun x => (Nat.primeFactorsList (Nat.gcd x.1 x.2)).length
    with hkey_def
  have hmaps : ∀ x ∈ D ℓ ×ˢ D ℓ, key x ∈ Finset.range (ℓ+1) := by
    intro x hx
    rw [Finset.mem_product] at hx
    have hdvd : Nat.gcd x.1 x.2 ∣ x.1 := Nat.gcd_dvd_left _ _
    have hle := (dvd_split_image_prod Y hY hx.1 hdvd).1
    have hkx : key x = (Nat.primeFactorsList (Nat.gcd x.1 x.2)).length := rfl
    rw [Finset.mem_range, hkx]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- bound each fibre
  have hfibre : ∀ k ∈ Finset.range (ℓ+1),
      ∑ x ∈ (D ℓ ×ˢ D ℓ).filter (fun x => key x = k),
          (1:ℝ)/(Nat.lcm x.1 x.2) ≤ σ^ℓ := by
    intro k hk
    rw [Finset.mem_range] at hk
    set φ : ℕ × ℕ → ℕ × ℕ × ℕ :=
      fun x => (Nat.gcd x.1 x.2, x.1 / Nat.gcd x.1 x.2, x.2 / Nat.gcd x.1 x.2)
      with hφ_def
    set h : ℕ × ℕ × ℕ → ℝ := fun y => (1:ℝ)/((y.1 : ℝ) * y.2.1 * y.2.2) with hh_def
    -- the fibre facts
    have hfacts : ∀ x ∈ (D ℓ ×ˢ D ℓ).filter (fun x => key x = k),
        Nat.gcd x.1 x.2 ∈ D k ∧ x.1 / Nat.gcd x.1 x.2 ∈ D (ℓ - k)
          ∧ x.2 / Nat.gcd x.1 x.2 ∈ D (ℓ - k)
          ∧ (Nat.lcm x.1 x.2 : ℝ)
              = (Nat.gcd x.1 x.2 : ℝ) * (x.1 / Nat.gcd x.1 x.2 : ℕ)
                  * (x.2 / Nat.gcd x.1 x.2 : ℕ) := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_product] at hx
      obtain ⟨⟨h1, h2⟩, hkk⟩ := hx
      have hg1 : Nat.gcd x.1 x.2 ∣ x.1 := Nat.gcd_dvd_left _ _
      have hg2 : Nat.gcd x.1 x.2 ∣ x.2 := Nat.gcd_dvd_right _ _
      have hs1 := dvd_split_image_prod Y hY h1 hg1
      have hs2 := dvd_split_image_prod Y hY h2 hg2
      rw [hkey_def] at hkk
      simp only at hkk
      rw [hkk] at hs1 hs2
      refine ⟨hs1.2.1, hs1.2.2, hs2.2.2, ?_⟩
      -- `lcm = g * (r/g) * (r'/g)`
      have hx10 : x.1 ≠ 0 := hDne ℓ x.1 h1
      have hg0 : Nat.gcd x.1 x.2 ≠ 0 := fun hc => hx10 (Nat.eq_zero_of_gcd_eq_zero_left hc)
      have hprod : Nat.gcd x.1 x.2 * Nat.lcm x.1 x.2 = x.1 * x.2 :=
        Nat.gcd_mul_lcm _ _
      have he1 : Nat.gcd x.1 x.2 * (x.1 / Nat.gcd x.1 x.2) = x.1 :=
        Nat.mul_div_cancel' hg1
      have he2 : Nat.gcd x.1 x.2 * (x.2 / Nat.gcd x.1 x.2) = x.2 :=
        Nat.mul_div_cancel' hg2
      have hnat : Nat.lcm x.1 x.2
          = Nat.gcd x.1 x.2 * (x.1 / Nat.gcd x.1 x.2) * (x.2 / Nat.gcd x.1 x.2) := by
        have : Nat.gcd x.1 x.2 * Nat.lcm x.1 x.2
            = Nat.gcd x.1 x.2 * (Nat.gcd x.1 x.2 * (x.1 / Nat.gcd x.1 x.2)
                * (x.2 / Nat.gcd x.1 x.2)) := by
          rw [hprod]
          calc x.1 * x.2 = (Nat.gcd x.1 x.2 * (x.1 / Nat.gcd x.1 x.2))
                * (Nat.gcd x.1 x.2 * (x.2 / Nat.gcd x.1 x.2)) := by rw [he1, he2]
            _ = Nat.gcd x.1 x.2 * (Nat.gcd x.1 x.2 * (x.1 / Nat.gcd x.1 x.2)
                * (x.2 / Nat.gcd x.1 x.2)) := by ring
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hg0) this
      rw [hnat]
      push_cast
      ring
    -- the map is injective on the fibre
    have hinj : Set.InjOn φ ((D ℓ ×ˢ D ℓ).filter (fun x => key x = k) : Finset (ℕ×ℕ)) := by
      intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at ha hb
      rw [hφ_def] at hab
      simp only [Prod.mk.injEq] at hab
      obtain ⟨hg, h1, h2⟩ := hab
      have ha1 : Nat.gcd a.1 a.2 * (a.1 / Nat.gcd a.1 a.2) = a.1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have ha2 : Nat.gcd a.1 a.2 * (a.2 / Nat.gcd a.1 a.2) = a.2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have hb1 : Nat.gcd b.1 b.2 * (b.1 / Nat.gcd b.1 b.2) = b.1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hb2 : Nat.gcd b.1 b.2 * (b.2 / Nat.gcd b.1 b.2) = b.2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      refine Prod.ext ?_ ?_
      · calc a.1 = Nat.gcd a.1 a.2 * (a.1 / Nat.gcd a.1 a.2) := ha1.symm
          _ = Nat.gcd b.1 b.2 * (b.1 / Nat.gcd b.1 b.2) := by rw [h1, hg]
          _ = b.1 := hb1
      · calc a.2 = Nat.gcd a.1 a.2 * (a.2 / Nat.gcd a.1 a.2) := ha2.symm
          _ = Nat.gcd b.1 b.2 * (b.2 / Nat.gcd b.1 b.2) := by rw [h2, hg]
          _ = b.2 := hb2
    -- image lands in the triple product
    have hsub : ((D ℓ ×ˢ D ℓ).filter (fun x => key x = k)).image φ
        ⊆ D k ×ˢ D (ℓ - k) ×ˢ D (ℓ - k) := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨hg, hs, hs', -⟩ := hfacts x hx
      rw [Finset.mem_product, Finset.mem_product]
      exact ⟨hg, hs, hs'⟩
    calc ∑ x ∈ (D ℓ ×ˢ D ℓ).filter (fun x => key x = k), (1:ℝ)/(Nat.lcm x.1 x.2)
        = ∑ x ∈ (D ℓ ×ˢ D ℓ).filter (fun x => key x = k), h (φ x) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          obtain ⟨-, -, -, hlcm⟩ := hfacts x hx
          rw [hh_def, hφ_def]
          simp only
          rw [hlcm]
      _ = ∑ y ∈ ((D ℓ ×ˢ D ℓ).filter (fun x => key x = k)).image φ, h y :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ y ∈ D k ×ˢ D (ℓ - k) ×ˢ D (ℓ - k), h y := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
          intro y _ _
          rw [hh_def]
          positivity
      _ = ∑ g ∈ D k, ∑ z ∈ D (ℓ - k) ×ˢ D (ℓ - k), h (g, z) :=
          Finset.sum_product (D k) (D (ℓ-k) ×ˢ D (ℓ-k)) h
      _ = ∑ g ∈ D k, ∑ s ∈ D (ℓ - k), ∑ s' ∈ D (ℓ - k),
            ((1:ℝ)/g) * (((1:ℝ)/s) * ((1:ℝ)/s')) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.sum_product (D (ℓ-k)) (D (ℓ-k)) (fun z => h (g, z))]
          refine Finset.sum_congr rfl fun s _ =>
            Finset.sum_congr rfl fun s' _ => ?_
          rw [hh_def]
          simp only
          rw [one_div, one_div, one_div, one_div, mul_inv, mul_inv]
          ring
      _ = (∑ g ∈ D k, (1:ℝ)/g) * ((∑ s ∈ D (ℓ-k), (1:ℝ)/s)
            * (∑ s' ∈ D (ℓ-k), (1:ℝ)/s')) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum]
      _ ≤ σ^k * (σ^(ℓ-k) * σ^(ℓ-k)) := by
          refine mul_le_mul (hDmass k) ?_ ?_ (by positivity)
          · exact mul_le_mul (hDmass (ℓ-k)) (hDmass (ℓ-k))
              (Finset.sum_nonneg fun n _ => by positivity) (by positivity)
          · refine mul_nonneg (Finset.sum_nonneg fun n _ => by positivity)
              (Finset.sum_nonneg fun n _ => by positivity)
      _ = σ^(k + (ℓ-k) + (ℓ-k)) := by rw [pow_add, pow_add]; ring
      _ ≤ σ^ℓ := by
          refine pow_le_pow_of_le_one hσ0 hσ ?_
          omega
  calc ∑ k ∈ Finset.range (ℓ+1),
        ∑ x ∈ (D ℓ ×ˢ D ℓ).filter (fun x => key x = k), (1:ℝ)/(Nat.lcm x.1 x.2)
      ≤ ∑ _k ∈ Finset.range (ℓ+1), σ^ℓ := Finset.sum_le_sum hfibre
    _ = ((ℓ:ℝ)+1) * σ^ℓ := by
        rw [Finset.sum_const, Finset.card_range]
        ring


/-! ## III-2 proper: the mean square of the smooth-divisor count (Track R,
A2-III, III-2f) -/

open Finset in
/-- **The mean square of the `Y^ℓ`-divisor count** (Track R, A2-III,
III-2f — "III-2 proper"): for a `Finset` of primes `Y` of harmonic mass
`σ = ∑_{p∈Y} 1/p ≤ 1` and a window `W ⊆ (M, RM]` of any ratio `R`,

  `∑_{n ∈ W} g(n)²/n ≤ R(ℓ+1)·σ^ℓ`,  `g(n) = #{r ∈ Y^ℓ : r ∣ n}`.

The weight is `1/n`, not `1/n²`, because that is what the in-tree sharp
mean value theorem charges: `intervalIntegral_norm_sq_poly_le_sharp_ratio`
takes a polynomial `∑ (c n/n)·e(−ξ log n)` to `e^π(T/A + 2R)·∑ ‖c n‖²/n`.
The design note's `sum_smooth_divisor_count_sq_div_sq_le` asks for `1/n²`,
which predates that normalisation and no consumer takes.

The ratio is left free because the consumer needs it free: `Q^ℓ·R` is
supported on `(P^ℓA', 2^{ℓ+1}P^ℓA']`, so an `ℓ`-fold prime product spans
a `2^{ℓ+1}`-fold range and no dyadic statement would reach it — the same
reason the sharp mean value theorem had to be re-cut at general ratio.

This is the elementary substitute for **Shiu's theorem** in the `[MR]`
moment estimate, and the last brick the full `III-3` was waiting on: the
coefficient of `Q^ℓ·R` at `n` is bounded by `ℓ!·g(n)`, so this sum is
exactly the coefficient mass the sharp mean value theorem charges.

Three steps, each already in the tree.  On `W ⊆ (M, 2M]` the weight
`1/n` drops to `1/M` (only the lower endpoint is used here; the ratio
enters solely through the fibre count, and the two `M`s then cancel — which
is why no scale survives in the bound).  The square is a pair count,

  `g(n)² = #{(r,r') ∈ Y^ℓ × Y^ℓ : r ∣ n ∧ r' ∣ n}
         = #{(r,r') : [r,r'] ∣ n}`,

so summing over `n` and swapping the order counts, for each pair, the
multiples of `[r,r']` in the window — at most `RM/[r,r']` by
`card_filter_dvd_le_div`.  What is left is `∑_{r,r'} 1/[r,r']`, which is
`sum_one_div_lcm_image_prod_le`.

No Shiu, no Rankin, and no Euler product over the `Y`-smooth numbers. -/
theorem sum_card_dvd_sq_div_le (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (ℓ : ℕ) (hσ : ∑ p ∈ Y, (1:ℝ)/p ≤ 1)
    (M R : ℕ) (hM : 1 ≤ M) (W : Finset ℕ) (hW : W ⊆ Finset.Ioc M (R*M)) :
    ∑ n ∈ W,
        ((((Fintype.piFinset fun _ : Fin ℓ => Y).image
              (fun v => ∏ i, v i)).filter (· ∣ n)).card : ℝ)^2 / (n:ℝ)
      ≤ (R:ℝ) * ((ℓ:ℝ)+1) * (∑ p ∈ Y, (1:ℝ)/p)^ℓ := by
  classical
  set D : Finset ℕ :=
    (Fintype.piFinset fun _ : Fin ℓ => Y).image (fun v => ∏ i, v i) with hD_def
  set σ : ℝ := ∑ p ∈ Y, (1:ℝ)/p with hσ_def
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  have hDne : ∀ n ∈ D, n ≠ 0 := fun n hn => ((mem_image_prod_iff Y hY n).mp hn).1
  -- (1) drop `1/n` to `1/M`
  have hstep1 : ∑ n ∈ W, ((D.filter (· ∣ n)).card : ℝ)^2 / (n:ℝ)
      ≤ (1/(M:ℝ)) * ∑ n ∈ W, ((D.filter (· ∣ n)).card : ℝ)^2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' := Finset.mem_Ioc.mp (hW hn)
    have hMn : (M:ℝ) < (n:ℝ) := by exact_mod_cast hn'.1
    have hn0 : (0:ℝ) < (n:ℝ) := lt_trans hM0 hMn
    have hc : (0:ℝ) ≤ ((D.filter (· ∣ n)).card : ℝ)^2 := sq_nonneg _
    have ht : (0:ℝ) ≤ (1/(M:ℝ)) * ((D.filter (· ∣ n)).card : ℝ)^2 := by
      positivity
    have key : (1/(M:ℝ)) * ((D.filter (· ∣ n)).card : ℝ)^2 * (M:ℝ)
        = ((D.filter (· ∣ n)).card : ℝ)^2 := by field_simp
    rw [div_le_iff₀ hn0]
    nlinarith [hMn, ht, key]
  -- (2) the square is a pair count, and the pair count is an lcm-fibre count
  have hsq : ∀ n : ℕ, ((D ×ˢ D).filter (fun x => Nat.lcm x.1 x.2 ∣ n)).card
      = (D.filter (· ∣ n)).card * (D.filter (· ∣ n)).card := by
    intro n
    have hfil : (D ×ˢ D).filter (fun x => Nat.lcm x.1 x.2 ∣ n)
        = (D.filter (· ∣ n)) ×ˢ (D.filter (· ∣ n)) := by
      rw [← Finset.filter_product (fun a : ℕ => a ∣ n) (fun b : ℕ => b ∣ n)]
      refine Finset.filter_congr fun x _ => ?_
      simp only [Nat.lcm_dvd_iff]
    rw [hfil, Finset.card_product]
  -- (3) the double count
  have hswap : ∑ n ∈ W, ((D.filter (· ∣ n)).card : ℝ)^2
      = ∑ x ∈ D ×ˢ D, ((W.filter (fun n => Nat.lcm x.1 x.2 ∣ n)).card : ℝ) := by
    have hL : ∀ n : ℕ, ((D.filter (· ∣ n)).card : ℝ)^2
        = ((((D ×ˢ D).filter (fun x => Nat.lcm x.1 x.2 ∣ n)).card : ℕ) : ℝ) := by
      intro n
      rw [hsq n]
      push_cast
      ring
    simp only [hL]
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero]
    rw [Finset.sum_comm]
  -- (4) each lcm fibre by the window fibre count
  have hfib : ∀ x ∈ D ×ˢ D,
      ((W.filter (fun n => Nat.lcm x.1 x.2 ∣ n)).card : ℝ)
        ≤ ((R:ℝ)*(M:ℝ))/(Nat.lcm x.1 x.2 : ℝ) := by
    intro x hx
    rw [Finset.mem_product] at hx
    have h1 : x.1 ≠ 0 := hDne _ hx.1
    have h2 : x.2 ≠ 0 := hDne _ hx.2
    have hl : 0 < Nat.lcm x.1 x.2 := Nat.pos_of_ne_zero (Nat.lcm_ne_zero h1 h2)
    have hcnt := card_filter_dvd_le_div M (R*M) W hW hl
    calc ((W.filter (fun n => Nat.lcm x.1 x.2 ∣ n)).card : ℝ)
        ≤ ((R*M : ℕ) : ℝ)/(Nat.lcm x.1 x.2 : ℝ) := hcnt
      _ = ((R:ℝ)*(M:ℝ))/(Nat.lcm x.1 x.2 : ℝ) := by push_cast; ring
  -- (5) assemble against the pair-divisor sum
  have hpair : ∑ x ∈ D ×ˢ D, (1:ℝ)/(Nat.lcm x.1 x.2) ≤ ((ℓ:ℝ)+1) * σ^ℓ := by
    rw [Finset.sum_product]
    exact sum_one_div_lcm_image_prod_le Y hY ℓ hσ
  calc ∑ n ∈ W, ((D.filter (· ∣ n)).card : ℝ)^2 / (n:ℝ)
      ≤ (1/(M:ℝ)) * ∑ n ∈ W, ((D.filter (· ∣ n)).card : ℝ)^2 := hstep1
    _ = (1/(M:ℝ)) * ∑ x ∈ D ×ˢ D,
          ((W.filter (fun n => Nat.lcm x.1 x.2 ∣ n)).card : ℝ) := by rw [hswap]
    _ ≤ (1/(M:ℝ)) * ∑ x ∈ D ×ˢ D, ((R:ℝ)*(M:ℝ))/(Nat.lcm x.1 x.2 : ℝ) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum hfib) (by positivity)
    _ = ((R:ℝ)*(M:ℝ)/(M:ℝ)) * ∑ x ∈ D ×ˢ D, (1:ℝ)/(Nat.lcm x.1 x.2) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        field_simp
    _ ≤ ((R:ℝ)*(M:ℝ)/(M:ℝ)) * (((ℓ:ℝ)+1) * σ^ℓ) := by
        refine mul_le_mul_of_nonneg_left hpair (by positivity)
    _ = (R:ℝ) * ((ℓ:ℝ)+1) * σ^ℓ := by
        field_simp

end MoltResearch
