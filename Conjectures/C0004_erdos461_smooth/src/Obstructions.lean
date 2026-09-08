import Conjectures.C0004_erdos461_smooth.src.Reduction

/-!
# Erdős 461: obstructions to the naive multiple matchings

This file formalizes the finite obstruction at `t = 8`, `n = 1255` and a
parametric highly-divisible-centre construction.  These results obstruct the
prime and upper-half *multiple* matchings discussed in
`Problems/erdos461_obstructions.md`; they do not disprove Erdős 461 or the
lower-half component-matching interface in `Reduction.lean`.
-/

namespace MoltResearch.Erdos461

open Finset

/-- Multiples of `d` represented by the interval `(n, n + t]`. -/
def multipleNeighbors (n t d : ℕ) : Finset ℕ :=
  (Finset.Ioc n (n + t)).filter (fun m => d ∣ m)

/-- The interval start that puts `C` just right of the middle of an interval
of length `t`.  Thus `C` occurs at offset `t / 2 + 1`. -/
def centeredStart (t C : ℕ) : ℕ := C - (t / 2 + 1)

/-- The false dyadic route uses the upper-half divisors
`ceil(t / 2) ≤ d < t`. -/
def upperHalfLeft (t : ℕ) : Finset ℕ :=
  Finset.Ico ((t + 1) / 2) t

/-- The integer neighbors of all divisors in `U`. -/
def multipleNeighborhood (n t : ℕ) (U : Finset ℕ) : Finset ℕ :=
  U.biUnion (multipleNeighbors n t)

/-- The Hall defect of a set of left vertices in the multiple graph. -/
def multipleDefect (n t : ℕ) (U : Finset ℕ) : ℕ :=
  U.card - (multipleNeighborhood n t U).card

private theorem eq_of_common_multiple_of_sub_lt {d x y : ℕ}
    (hdx : d ∣ x) (hdy : d ∣ y)
    (hxy : x < y → y - x < d) (hyx : y < x → x - y < d) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have hdvd : d ∣ y - x := Nat.dvd_sub hdy hdx
    have hle : d ≤ y - x := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdvd
    exact (not_lt_of_ge hle (hxy hlt)).elim
  · exact heq
  · have hdvd : d ∣ x - y := Nat.dvd_sub hdx hdy
    have hle : d ≤ x - y := Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) hdvd
    exact (not_lt_of_ge hle (hyx hgt)).elim

/-- In an odd interval centered at a common multiple `C`, every divisor at
least `k + 1` has the unique represented multiple `C`. -/
theorem multipleNeighbors_centered_odd {k C d : ℕ} (hC : k + 1 ≤ C)
    (hd : k + 1 ≤ d) (hdC : d ∣ C) :
    multipleNeighbors (centeredStart (2 * k + 1) C) (2 * k + 1) d = {C} := by
  ext m
  simp only [multipleNeighbors, Finset.mem_filter, Finset.mem_Ioc,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hm, hdm⟩
    apply eq_of_common_multiple_of_sub_lt hdm hdC
    · intro hlt
      simp [centeredStart] at hm
      omega
    · intro hgt
      simp [centeredStart] at hm
      omega
  · intro hm
    subst m
    refine ⟨?_, hdC⟩
    simp [centeredStart]
    omega

/-- In an even interval centered one place right of the midpoint, every
divisor strictly above `k` again has the unique represented multiple `C`. -/
theorem multipleNeighbors_centered_even_large {k C d : ℕ} (hk : 1 ≤ k)
    (hC : k + 1 ≤ C) (hd : k + 1 ≤ d) (hdC : d ∣ C) :
    multipleNeighbors (centeredStart (2 * k) C) (2 * k) d = {C} := by
  ext m
  simp only [multipleNeighbors, Finset.mem_filter, Finset.mem_Ioc,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hm, hdm⟩
    apply eq_of_common_multiple_of_sub_lt hdm hdC
    · intro hlt
      simp [centeredStart] at hm
      omega
    · intro hgt
      simp [centeredStart] at hm
      omega
  · intro hm
    subst m
    refine ⟨?_, hdC⟩
    simp [centeredStart]
    omega

/-- For an even interval, the boundary divisor `k` sees the center and the
left endpoint.  This is the sole extra neighbor in the family. -/
theorem multipleNeighbors_centered_even_half {k C : ℕ} (hk : 1 ≤ k)
    (hC : k + 1 ≤ C) (hkC : k ∣ C) :
    multipleNeighbors (centeredStart (2 * k) C) (2 * k) k = {C - k, C} := by
  ext m
  simp only [multipleNeighbors, Finset.mem_filter, Finset.mem_Ioc,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hm, hkm⟩
    rcases lt_trichotomy m C with hlt | rfl | hgt
    · left
      have hdvd : k ∣ C - m := Nat.dvd_sub hkC hkm
      have hle : k ≤ C - m := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdvd
      simp [centeredStart] at hm
      omega
    · exact Or.inr rfl
    · have hdvd : k ∣ m - C := Nat.dvd_sub hkm hkC
      have hle : k ≤ m - C := Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) hdvd
      simp [centeredStart] at hm
      omega
  · rintro (rfl | rfl)
    · constructor
      · simp [centeredStart]
        omega
      · exact Nat.dvd_sub hkC (dvd_refl k)
    · constructor
      · simp [centeredStart]
        omega
      · exact hkC

/-- Every upper-half divisor of an odd interval has the same sole neighbor
when the center is divisible by all of them. -/
theorem multipleNeighborhood_centered_odd {k C : ℕ} (hk : 1 ≤ k)
    (hC : k + 1 ≤ C) (hdiv : ∀ d ∈ upperHalfLeft (2 * k + 1), d ∣ C) :
    multipleNeighborhood (centeredStart (2 * k + 1) C) (2 * k + 1)
      (upperHalfLeft (2 * k + 1)) = {C} := by
  ext m
  simp only [multipleNeighborhood, Finset.mem_biUnion, Finset.mem_singleton]
  constructor
  · rintro ⟨d, hd, hm⟩
    have hdlo : k + 1 ≤ d := by
      simp [upperHalfLeft] at hd
      omega
    rw [multipleNeighbors_centered_odd hC hdlo (hdiv d hd)] at hm
    exact Finset.mem_singleton.mp hm
  · intro hm
    subst m
    have hd : k + 1 ∈ upperHalfLeft (2 * k + 1) := by
      simp [upperHalfLeft]
      omega
    refine ⟨k + 1, hd, ?_⟩
    rw [multipleNeighbors_centered_odd hC (le_refl _) (hdiv (k + 1) hd)]
    simp

/-- The upper-half neighborhood of the even family consists of exactly the
center and the left endpoint. -/
theorem multipleNeighborhood_centered_even {k C : ℕ} (hk : 2 ≤ k)
    (hC : k + 1 ≤ C) (hdiv : ∀ d ∈ upperHalfLeft (2 * k), d ∣ C) :
    multipleNeighborhood (centeredStart (2 * k) C) (2 * k)
      (upperHalfLeft (2 * k)) = {C - k, C} := by
  ext m
  simp only [multipleNeighborhood, Finset.mem_biUnion, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨d, hd, hm⟩
    have hdbounds : k ≤ d ∧ d < 2 * k := by
      simp [upperHalfLeft] at hd
      omega
    by_cases hdk : d = k
    · subst d
      rw [multipleNeighbors_centered_even_half (by omega) hC (hdiv k hd)] at hm
      simpa using hm
    · have hdlo : k + 1 ≤ d := by omega
      rw [multipleNeighbors_centered_even_large (by omega) hC hdlo (hdiv d hd)] at hm
      exact Or.inr (Finset.mem_singleton.mp hm)
  · intro hm
    have hd : k ∈ upperHalfLeft (2 * k) := by
      simp [upperHalfLeft]
      omega
    refine ⟨k, hd, ?_⟩
    rw [multipleNeighbors_centered_even_half (by omega) hC (hdiv k hd)]
    simpa using hm

/-- The full upper-half left set has size `k` for odd intervals. -/
theorem upperHalfLeft_odd_card (k : ℕ) :
    (upperHalfLeft (2 * k + 1)).card = k := by
  simp [upperHalfLeft]
  omega

/-- The full upper-half left set has size `k` for even intervals. -/
theorem upperHalfLeft_even_card (k : ℕ) :
    (upperHalfLeft (2 * k)).card = k := by
  simp [upperHalfLeft]
  omega

/-- Exact Hall defect for the odd highly-divisible-center family: `k - 1`.
Thus the maximum multiple matching has size at most one. -/
theorem multipleDefect_centered_odd {k C : ℕ} (hk : 1 ≤ k)
    (hC : k + 1 ≤ C) (hdiv : ∀ d ∈ upperHalfLeft (2 * k + 1), d ∣ C) :
    multipleDefect (centeredStart (2 * k + 1) C) (2 * k + 1)
      (upperHalfLeft (2 * k + 1)) = k - 1 := by
  rw [multipleDefect, multipleNeighborhood_centered_odd hk hC hdiv,
    upperHalfLeft_odd_card]
  simp

/-- Exact Hall defect for the even highly-divisible-center family: `k - 2`.
Thus the maximum multiple matching has size at most two. -/
theorem multipleDefect_centered_even {k C : ℕ} (hk : 2 ≤ k)
    (hC : k + 1 ≤ C) (hdiv : ∀ d ∈ upperHalfLeft (2 * k), d ∣ C) :
    multipleDefect (centeredStart (2 * k) C) (2 * k)
      (upperHalfLeft (2 * k)) = k - 2 := by
  rw [multipleDefect, multipleNeighborhood_centered_even hk hC hdiv,
    upperHalfLeft_even_card]
  have hne : C - k ≠ C := by omega
  simp [hne]

/-- Factorial centers give an explicit infinite odd obstruction family. -/
theorem multipleDefect_factorial_center_odd (k : ℕ) (hk : 1 ≤ k) :
    multipleDefect
      (centeredStart (2 * k + 1) (Nat.factorial (2 * k + 1))) (2 * k + 1)
      (upperHalfLeft (2 * k + 1)) = k - 1 := by
  apply multipleDefect_centered_odd hk
  · exact (by
      calc
        k + 1 ≤ 2 * k + 1 := by omega
        _ ≤ Nat.factorial (2 * k + 1) := Nat.self_le_factorial _)
  · intro d hd
    have hbounds : k + 1 ≤ d ∧ d < 2 * k + 1 := by
      simp [upperHalfLeft] at hd
      omega
    exact Nat.dvd_factorial (by omega) (by omega)

/-- Factorial centers give an explicit infinite even obstruction family. -/
theorem multipleDefect_factorial_center_even (k : ℕ) (hk : 2 ≤ k) :
    multipleDefect
      (centeredStart (2 * k) (Nat.factorial (2 * k))) (2 * k)
      (upperHalfLeft (2 * k)) = k - 2 := by
  apply multipleDefect_centered_even hk
  · exact (by
      calc
        k + 1 ≤ 2 * k := by omega
        _ ≤ Nat.factorial (2 * k) := Nat.self_le_factorial _)
  · intro d hd
    have hbounds : k ≤ d ∧ d < 2 * k := by
      simp [upperHalfLeft] at hd
      omega
    exact Nat.dvd_factorial (by omega) (by omega)

/-- At `t = 8`, the prime `5` has only the multiple `1260` in
`(1255, 1263]`. -/
theorem multipleNeighbors_1255_eight_five :
    multipleNeighbors 1255 8 5 = {1260} := by
  native_decide

/-- At `t = 8`, the prime `7` has the same unique multiple as `5`. -/
theorem multipleNeighbors_1255_eight_seven :
    multipleNeighbors 1255 8 7 = {1260} := by
  native_decide

/-- Consequently, any choices of interval multiples for `5` and `7` agree;
the proposed prime-to-distinct-multiples injection already fails at
`t = 8`, `n = 1255`. -/
theorem prime_pair_choices_coincide {m₅ m₇ : ℕ}
    (h₅ : m₅ ∈ multipleNeighbors 1255 8 5)
    (h₇ : m₇ ∈ multipleNeighbors 1255 8 7) : m₅ = m₇ := by
  rw [multipleNeighbors_1255_eight_five] at h₅
  rw [multipleNeighbors_1255_eight_seven] at h₇
  simp only [Finset.mem_singleton] at h₅ h₇
  exact h₅.trans h₇.symm

/-- The eight pointwise component computations used below. -/
theorem smoothPart_8_1256 : smoothPart 8 1256 = 8 := by
  unfold smoothPart
  rw [show Nat.primeFactors 1256 = {2, 157} by native_decide]
  rw [show ({2, 157} : Finset ℕ).filter (fun p => p < 8) = {2} by native_decide]
  norm_num [show Nat.factorization 1256 2 = 3 by native_decide]
theorem smoothPart_8_1257 : smoothPart 8 1257 = 3 := by
  unfold smoothPart
  rw [show Nat.primeFactors 1257 = {3, 419} by native_decide]
  rw [show ({3, 419} : Finset ℕ).filter (fun p => p < 8) = {3} by native_decide]
  norm_num [show Nat.factorization 1257 3 = 1 by native_decide]
theorem smoothPart_8_1258 : smoothPart 8 1258 = 2 := by
  unfold smoothPart
  rw [show Nat.primeFactors 1258 = {2, 17, 37} by native_decide]
  rw [show ({2, 17, 37} : Finset ℕ).filter (fun p => p < 8) = {2} by native_decide]
  norm_num [show Nat.factorization 1258 2 = 1 by native_decide]
theorem smoothPart_8_1259 : smoothPart 8 1259 = 1 := by
  norm_num [smoothPart,
    show Nat.primeFactors 1259 = {1259} by native_decide]
theorem smoothPart_8_1260 : smoothPart 8 1260 = 1260 := by
  apply smoothPart_eq_self (by norm_num)
  norm_num [show Nat.primeFactors 1260 = {2, 3, 5, 7} by native_decide]
theorem smoothPart_8_1261 : smoothPart 8 1261 = 1 := by
  norm_num [smoothPart,
    show Nat.primeFactors 1261 = {13, 97} by native_decide]
theorem smoothPart_8_1262 : smoothPart 8 1262 = 2 := by
  unfold smoothPart
  rw [show Nat.primeFactors 1262 = {2, 631} by native_decide]
  rw [show ({2, 631} : Finset ℕ).filter (fun p => p < 8) = {2} by native_decide]
  norm_num [show Nat.factorization 1262 2 = 1 by native_decide]
theorem smoothPart_8_1263 : smoothPart 8 1263 = 3 := by
  unfold smoothPart
  rw [show Nat.primeFactors 1263 = {3, 421} by native_decide]
  rw [show ({3, 421} : Finset ℕ).filter (fun p => p < 8) = {3} by native_decide]
  norm_num [show Nat.factorization 1263 3 = 1 by native_decide]

/-- The exact smooth components in the smallest prime-matching
counterexample. -/
theorem smoothParts_1255_eight :
    (Finset.Ioc 1255 1263).image (smoothPart 8) = {1, 2, 3, 8, 1260} := by
  rw [show Finset.Ioc 1255 1263 =
    {1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263} by native_decide]
  simp [smoothPart_8_1256, smoothPart_8_1257, smoothPart_8_1258,
    smoothPart_8_1259, smoothPart_8_1260, smoothPart_8_1261,
    smoothPart_8_1262, smoothPart_8_1263]
  native_decide

/-- Hence the counterexample interval has five distinct smooth components.
This is evidence against the proposed injection, not against a proportional
lower bound. -/
theorem smoothComponentCount_1255_eight :
    smoothComponentCount 1255 8 = 5 := by
  rw [smoothComponentCount, show 1255 + 8 = 1263 by norm_num,
    smoothParts_1255_eight]
  native_decide

end MoltResearch.Erdos461
