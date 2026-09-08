import MoltResearch.Discrepancy.ExpSums

/-!
# Upstreaming slot UP-4: Kusmin–Landau and the second-derivative test

Pre-allocated leaf for card item UP-4 of `Problems/nucleus_upstreaming.md`. The claimant of UP-4 fills this file with
the Mathlib-style restatement, proved from the imported tree lemmas; no other file is to be edited.
-/

namespace MoltResearch

namespace Upstream

/-- The monotone Kusmin--Landau inequality on a half-open natural interval,
in the form of Landau, *Ueber eine trigonometrische Summe* (1928).  The
normalized additive character is expanded in the statement. -/
theorem kusmin_landau_Ico {φ : ℕ → ℝ} {θ : ℝ} {M N : ℕ}
    (hθ : 0 < θ) (hMN : M < N)
    (hlo : ∀ n, M ≤ n → n < N → θ ≤ φ (n + 1) - φ n)
    (hhi : ∀ n, M ≤ n → n < N → φ (n + 1) - φ n ≤ 1 - θ)
    (hmono : ∀ n, M ≤ n → n + 1 < N →
      φ (n + 1) - φ n ≤ φ (n + 2) - φ (n + 1)) :
    ‖∑ n ∈ Finset.Ico M N,
        Complex.exp (2 * Real.pi * φ n * Complex.I)‖ ≤ 1 / θ := by
  have hMN' : M ≤ N - 1 := by omega
  have hN : N - 1 + 1 = N := by omega
  simpa only [ExpSums.e, hN] using
    (ExpSums.kusmin_landau (φ := φ) (θ := θ) (M := M) (N := N - 1)
      hθ hMN'
      (fun n hn hnN => hlo n hn (by omega))
      (fun n hn hnN => hhi n hn (by omega))
      (fun n hn hnN => hmono n hn (by omega)))

/-- A discrete convex-phase version of van der Corput's second-derivative
test, whose classical continuous form dates to van der Corput (1922).
Everything in the statement is standard `Finset` and complex-exponential
notation. -/
theorem van_der_corput_second_derivative_Ico
    {φ : ℕ → ℝ} {θ r D : ℝ} {M N : ℕ}
    (hθ : 0 < θ) (hr : 0 < r) (hMN : M < N)
    (hmono : ∀ n, M ≤ n → n + 1 < N →
      φ (n + 1) - φ n ≤ φ (n + 2) - φ (n + 1))
    (hsec : ∀ n, M ≤ n → n + 1 < N →
      r ≤ (φ (n + 2) - φ (n + 1)) - (φ (n + 1) - φ n))
    (hD : (φ N - φ (N - 1)) - (φ (M + 1) - φ M) ≤ D) :
    ‖∑ n ∈ Finset.Ico M N,
        Complex.exp (2 * Real.pi * φ n * Complex.I)‖
      ≤ (D + 2) * ((2 * θ / r + 1) + 1 / θ) := by
  have hMN' : M ≤ N - 1 := by omega
  have hN : N - 1 + 1 = N := by omega
  simpa only [ExpSums.e, hN] using
    (ExpSums.vdc2 (φ := φ) (θ := θ) (r := r) (D := D)
      (M := M) (N := N - 1) hθ hr hMN'
      (fun n hn hnN => hmono n hn (by omega))
      (fun n hn hnN => hsec n hn (by omega)) (by simpa only [hN] using hD))

/-- Both standalone tests specialize to the same expanded exponential sum. -/
example {φ : ℕ → ℝ} {θ r D : ℝ} {M N : ℕ}
    (hθ : 0 < θ) (hr : 0 < r) (hMN : M < N)
    (hlo : ∀ n, M ≤ n → n < N → θ ≤ φ (n + 1) - φ n)
    (hhi : ∀ n, M ≤ n → n < N → φ (n + 1) - φ n ≤ 1 - θ)
    (hmono : ∀ n, M ≤ n → n + 1 < N →
      φ (n + 1) - φ n ≤ φ (n + 2) - φ (n + 1))
    (hsec : ∀ n, M ≤ n → n + 1 < N →
      r ≤ (φ (n + 2) - φ (n + 1)) - (φ (n + 1) - φ n))
    (hD : (φ N - φ (N - 1)) - (φ (M + 1) - φ M) ≤ D) :
    let S := ∑ n ∈ Finset.Ico M N,
      Complex.exp (2 * Real.pi * φ n * Complex.I)
    ‖S‖ ≤ 1 / θ ∧
      ‖S‖ ≤ (D + 2) * ((2 * θ / r + 1) + 1 / θ) := by
  exact ⟨kusmin_landau_Ico hθ hMN hlo hhi hmono,
    van_der_corput_second_derivative_Ico hθ hr hMN hmono hsec hD⟩

end Upstream

end MoltResearch
