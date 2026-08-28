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

end MoltResearch
