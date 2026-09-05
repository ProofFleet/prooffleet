import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5MajorArcA2
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5MatomakiRadziwillMajorArc

/-!
# Track C: Stage 5 — the `mrp` wrapper: the major-arc interface from `SliceMeanSquareA2` (R7)

The last leg of the Track R chain (`Problems/tao2015_a1_r6r7_design_report.md` §1.4,
§8 Phase R7): from the Prop `SliceMeanSquareA2` (`[mrt]` Theorem A.2 in the tree's shape)
to the major-arc Matomäki–Radziwiłł interface `MatomakiRadziwillMajorArcAssumption`,
following Tao's proof of Proposition 2.4 (arXiv:1509.05422): the range `(x/w, x]` is
covered by dyadic blocks, on each **good** block the once-paid `𝒮ᶜ` removal and the
`𝒮`-restricted major-arc bound of `majorArc_block_bound_restricted` give
`≲ ε·∑_{block} 1/n`, and the few **small** and **bad** blocks are priced trivially.

* `good_block_total_le` (R7-4) — the per-block estimate on a good block, with every
  constant explicit: `(16qε' + qh₀/H + 4πq²|α − a/q|h₀ + 6εc)·∑_{(A,2A]} 1/n`.
* `exists_wrapper_params` (R7-5) — the parameter choice: for `ε ≤ 1` and the arc data
  `(C, B)`, an `H₀` such that every `H ≥ H₀` admits `Q ≥ max(C(log H)^B, 1)`, a window
  `h₀ ≤ εH/(64πQ²)` with `2h₀ ≤ H`, and A.2 data `(levels, A₀)` at `ε' = ε/(128Q)`,
  `εc = ε/48`, with all level primes above `Q`.  The Prop is invoked with the polylog
  constant `2^B·C`, so that `2^B C(log h₀)^B ≥ C(log H)^B` follows from `H ≤ h₀²`; every
  size condition is one instance of `exists_forall_polylog_le`.
-/

namespace MoltResearch

namespace Tao2015

open ExpSums

/-- **The total on a good dyadic block** (Track R, R7-4).

Given the two clauses of `SliceMeanSquareA2` for one `(levels, A₀, h₀, ε', εc)` — the
`𝒮ᶜ` log-density `≤ εc` on dyadic blocks above `A₀`, and the mean square — and a good
block `(A, 2A]` (`6qH ≤ A`, `7q² ≤ A`, `⌈A₀⌉₊ + 1 ≤ ⌊A/q⌋`, `g` non-pretentious at
strength `q·A₀ + 26` and truncation `6A+1`), the log-averaged window sums at any `α`
with rational part `a/q` are at most

  `(16qε' + qh₀/H + 4πq²|α − a/q|h₀ + 6εc)·∑_{(A,2A]} 1/n`.

The window is split into its `𝒮`-part and the complement once
(`sum_window_div_le_restricted_add_complement`); the complement is priced by the density
clause on `(A, 2A]` and `(2A, 4A]` (`sum_complement_Ioc_le_of_density`); the `𝒮`-part by
`majorArc_block_bound_restricted` at `δ = α − a/q`. -/
theorem good_block_total_le
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ p ∈ P, p.Prime)
    (A₀ : ℝ) (hA₀1 : 1 ≤ A₀) (h₀ : ℕ) (ε' εc : ℝ) (hε' : 0 ≤ ε') (hεc : 0 ≤ εc)
    (hdens : ∀ A : ℕ, A₀ ≤ A →
      ∑ n ∈ (Finset.Ioc A (2 * A)).filter (fun n => ¬ HasFactorInAll levels n), (1:ℝ)/n
        ≤ εc * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n)
    (hms : ∀ A : ℕ, A₀ ≤ A →
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
        NonPretentiousAt g A₀ (2 * A + 1) →
        ∀ J : ℕ, J ≤ A →
          ∑ n ∈ Finset.Ioc A (A + J),
            ‖∑ m ∈ (Finset.Ioc n (n + h₀)).filter (HasFactorInAll levels), g m‖^2 / n
            ≤ ε'^2 * (h₀ : ℝ)^2 * ∑ n ∈ Finset.Ioc A (A + J), (1:ℝ)/n)
    (g : ℕ → ℂ) (hg : CompletelyMultiplicativeC g) (hgu : Unimodular g)
    (q : ℕ) (hq : 0 < q) (hql : ∀ P ∈ levels, ∀ p ∈ P, ¬ p ∣ q) (a : ℤ) (α : ℝ)
    (A H : ℕ) (hh₀ : 0 < h₀) (h2h₀ : 2 * h₀ ≤ H) (hA : 6 * q * H ≤ A)
    (hA7 : 7 * q ^ 2 ≤ A) (hA₀q : ⌈A₀⌉₊ + 1 ≤ A / q)
    (hnp : NonPretentiousAt g (q * A₀ + 26) (6 * A + 1)) :
    ∑ n ∈ Finset.Ioc A (2 * A),
        ‖∑ m ∈ Finset.Ioc n (n + H),
          g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ / ((H : ℝ) * n)
      ≤ (16 * q * ε' + q * h₀ / H + 4 * Real.pi * q^2 * |α - (a : ℝ) / q| * h₀ + 6 * εc)
          * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n := by
  have hb : ∀ m, ‖g m‖ ≤ 1 := fun m => (hgu m).le
  have hH : 0 < H := by omega
  have h2H : 2 * H ≤ A := by nlinarith
  have hA1 : 1 ≤ A := by omega
  have hHA : H ≤ 2 * A := by omega
  -- `A₀ ≤ A` and `A₀ ≤ 2A` from `⌈A₀⌉₊ + 1 ≤ ⌊A/q⌋ ≤ A`
  have hA₀A : A₀ ≤ A := by
    have h1 : ⌈A₀⌉₊ ≤ A := le_trans (by omega) (Nat.div_le_self A q)
    exact le_trans (Nat.le_ceil A₀) (by exact_mod_cast h1)
  have hA₀2A : A₀ ≤ ((2 * A : ℕ) : ℝ) := le_trans hA₀A (by exact_mod_cast (by omega : A ≤ 2 * A))
  -- the once-paid removal
  have hsplit := sum_window_div_le_restricted_add_complement g hb levels α A H hH h2H
  -- the complement mass
  have hcompl := sum_complement_Ioc_le_of_density levels εc hεc A H hA1 hHA
    (hdens A hA₀A) (hdens (2 * A) hA₀2A)
  -- the restricted part at `α = a/q + (α − a/q)`
  have hα : ∀ m : ℕ,
      g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))
        = g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)
            * (((a : ℝ) / (q : ℝ) + (α - (a : ℝ) / (q : ℝ)) : ℝ) : ℂ)) := by
    intro m
    congr 3
    push_cast
    ring
  have hres := majorArc_block_bound_restricted levels hlv A₀ hA₀1 h₀ ε' hε' hms g hg hgu q hq hql
    a (α - (a : ℝ) / (q : ℝ)) A H hh₀ h2h₀ hA hA7 hA₀q hnp
  simp_rw [← hα] at hres
  have hS0 : 0 ≤ ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n :=
    Finset.sum_nonneg fun n _ => by positivity
  calc ∑ n ∈ Finset.Ioc A (2 * A),
        ‖∑ m ∈ Finset.Ioc n (n + H),
          g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ / ((H : ℝ) * n)
      ≤ (∑ n ∈ Finset.Ioc A (2 * A),
          ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
            g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ / ((H : ℝ) * n))
        + 2 * ∑ m ∈ (Finset.Ioc A (2 * A + H)).filter (fun m => ¬ HasFactorInAll levels m),
            (1:ℝ) / m := hsplit
    _ ≤ (16 * q * ε' + q * h₀ / H + 4 * Real.pi * q^2 * |α - (a : ℝ) / q| * h₀)
          * (∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n)
        + 2 * (3 * εc * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n) :=
        add_le_add hres (mul_le_mul_of_nonneg_left hcompl (by norm_num))
    _ = _ := by ring

/-- **The parameter choice** (Track R, R7-5).

For `0 < ε ≤ 1`, `C > 0` and `B`, there is `H₀` such that every `H ≥ H₀` admits: a real
`Q ≥ 1` with `C(log H)^B ≤ Q`; a window length `h₀` with `0 < h₀`, `2h₀ ≤ H` and
`h₀ ≤ εH/(64πQ²)`; and a level list with threshold `A₀ ≥ 1` such that the levels are
primes above `Q`, the `𝒮ᶜ` log-density of dyadic blocks above `A₀` is at most `ε/48`, and
the mean-square clause of `SliceMeanSquareA2` holds at `ε' = ε/(128Q)` and window `h₀`.

`Q := max(C(log H)^B, 1)`, `h₀ := ⌊εH/(64πQ²)⌋₊`, and the Prop is invoked at
`(εc, B, 2^B C)`; the requirements `h₁ ≤ h₀`, `C₁/ε'^k ≤ h₀`, `H ≤ h₀²` are all of the
form `T·Q^{2k+4} ≤ H` for one explicit `T`, supplied by `exists_forall_polylog_le`. -/
theorem exists_wrapper_params (hA2 : SliceMeanSquareA2) (ε C : ℝ) (B : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 < C) :
    ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H →
      ∃ (Q : ℝ) (h₀ : ℕ) (levels : List (Finset ℕ)) (A₀ : ℝ),
        1 ≤ Q ∧ C * Real.log H ^ B ≤ Q ∧ 1 ≤ A₀ ∧ 0 < h₀ ∧ 2 * h₀ ≤ H ∧
        (h₀ : ℝ) ≤ ε * H / (64 * Real.pi * Q ^ 2) ∧
        (∀ P ∈ levels, ∀ p ∈ P, p.Prime) ∧
        (∀ P ∈ levels, ∀ p ∈ P, Q < p) ∧
        (∀ A : ℕ, A₀ ≤ A →
          ∑ n ∈ (Finset.Ioc A (2 * A)).filter (fun n => ¬ HasFactorInAll levels n), (1:ℝ)/n
            ≤ (ε / 48) * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n) ∧
        (∀ A : ℕ, A₀ ≤ A →
          ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
            NonPretentiousAt g A₀ (2 * A + 1) →
            ∀ J : ℕ, J ≤ A →
              ∑ n ∈ Finset.Ioc A (A + J),
                ‖∑ m ∈ (Finset.Ioc n (n + h₀)).filter (HasFactorInAll levels), g m‖^2 / n
                ≤ (ε / (128 * Q))^2 * (h₀ : ℝ)^2 * ∑ n ∈ Finset.Ioc A (A + J), (1:ℝ)/n) := by
  obtain ⟨h₁, C₁, k, hC₁, hProp⟩ :=
    hA2 (ε / 48) (by positivity) B (2 ^ B * C) (by positivity)
  have hπ : (1:ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  -- the one size constant
  set T : ℝ := (64 * Real.pi / ε) * ((h₁ : ℝ) + 2 + C₁ * (128 / ε) ^ k)
    + (128 * Real.pi / ε) ^ 2 with hT
  have hT0 : 0 < T := by positivity
  obtain ⟨H₀, hH₀⟩ := exists_forall_polylog_le T C hT0 hC B (2 * k + 4)
  refine ⟨H₀, fun H hH => ?_⟩
  obtain ⟨hH2, hTH⟩ := hH₀ H hH
  set Q : ℝ := max (C * Real.log H ^ B) 1 with hQdef
  have hQ1 : 1 ≤ Q := le_max_right _ _
  have hQQ : C * Real.log H ^ B ≤ Q := le_max_left _ _
  have hQ0 : 0 < Q := by linarith
  have hHpos : (0:ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  -- the window length
  set t : ℝ := ε * H / (64 * Real.pi * Q ^ 2) with htdef
  have ht0 : 0 ≤ t := by positivity
  set h₀ : ℕ := ⌊t⌋₊ with hh₀def
  -- `t ≥ (h₁ + 2 + C₁(128/ε)^k)·Q^{2k+2}` from `T·Q^{2k+4} ≤ H`
  have hQpow : Q ^ (2 * k + 4) = Q ^ (2 * k + 2) * Q ^ 2 := by rw [← pow_add]
  have hQ2k2 : 1 ≤ Q ^ (2 * k + 2) := one_le_pow₀ hQ1
  have hQk : Q ^ k ≤ Q ^ (2 * k + 2) := pow_le_pow_right₀ hQ1 (by omega)
  have hbase : ((h₁ : ℝ) + 2 + C₁ * (128 / ε) ^ k) * Q ^ (2 * k + 2) ≤ t := by
    have h1 : (64 * Real.pi / ε) * ((h₁ : ℝ) + 2 + C₁ * (128 / ε) ^ k) * Q ^ (2 * k + 4)
        ≤ (H : ℝ) := by
      calc (64 * Real.pi / ε) * ((h₁ : ℝ) + 2 + C₁ * (128 / ε) ^ k) * Q ^ (2 * k + 4)
          ≤ T * Q ^ (2 * k + 4) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [hT]
            have : (0:ℝ) ≤ (128 * Real.pi / ε) ^ 2 := by positivity
            linarith
        _ ≤ H := hTH
    rw [htdef, le_div_iff₀ (by positivity)]
    rw [hQpow] at h1
    have hε' : 0 < 64 * Real.pi / ε := by positivity
    calc ((h₁ : ℝ) + 2 + C₁ * (128 / ε) ^ k) * Q ^ (2 * k + 2) * (64 * Real.pi * Q ^ 2)
        = ε * ((64 * Real.pi / ε) * ((h₁ : ℝ) + 2 + C₁ * (128 / ε) ^ k)
            * (Q ^ (2 * k + 2) * Q ^ 2)) := by
          field_simp
      _ ≤ ε * H := mul_le_mul_of_nonneg_left h1 hε.le
  have hCk0 : 0 ≤ C₁ * (128 / ε) ^ k := by positivity
  have ht2 : (h₁ : ℝ) + 2 + C₁ * (128 / ε) ^ k ≤ t := by
    calc (h₁ : ℝ) + 2 + C₁ * (128 / ε) ^ k
        = ((h₁ : ℝ) + 2 + C₁ * (128 / ε) ^ k) * 1 := (mul_one _).symm
      _ ≤ ((h₁ : ℝ) + 2 + C₁ * (128 / ε) ^ k) * Q ^ (2 * k + 2) :=
          mul_le_mul_of_nonneg_left hQ2k2 (by positivity)
      _ ≤ t := hbase
  have hh₀t : (h₀ : ℝ) ≤ t := Nat.floor_le ht0
  have hth₀ : t < (h₀ : ℝ) + 1 := Nat.lt_floor_add_one t
  -- `h₁ ≤ h₀`
  have hh₁ : h₁ ≤ h₀ := Nat.le_floor (by linarith)
  -- `C₁/ε'^k ≤ h₀` at `ε' = ε/(128Q)`
  have hε'0 : 0 < ε / (128 * Q) := by positivity
  have hCε' : C₁ / (ε / (128 * Q)) ^ k ≤ (h₀ : ℝ) := by
    have h1 : C₁ / (ε / (128 * Q)) ^ k = C₁ * (128 / ε) ^ k * Q ^ k := by
      have hε0 : ε ≠ 0 := hε.ne'
      have hQ0' : Q ≠ 0 := hQ0.ne'
      rw [div_pow, div_pow, mul_pow]
      field_simp
      try ring
    rw [h1]
    have h2 : C₁ * (128 / ε) ^ k * Q ^ k ≤ C₁ * (128 / ε) ^ k * Q ^ (2 * k + 2) :=
      mul_le_mul_of_nonneg_left hQk hCk0
    have h3 : C₁ * (128 / ε) ^ k * Q ^ (2 * k + 2) + 1
        ≤ ((h₁ : ℝ) + 2 + C₁ * (128 / ε) ^ k) * Q ^ (2 * k + 2) := by
      have : (1:ℝ) ≤ ((h₁ : ℝ) + 2) * Q ^ (2 * k + 2) := by
        calc (1:ℝ) ≤ 2 := by norm_num
          _ ≤ (h₁ : ℝ) + 2 := by linarith [(Nat.cast_nonneg h₁ : (0:ℝ) ≤ h₁)]
          _ = ((h₁ : ℝ) + 2) * 1 := (mul_one _).symm
          _ ≤ ((h₁ : ℝ) + 2) * Q ^ (2 * k + 2) :=
              mul_le_mul_of_nonneg_left hQ2k2 (by positivity)
      nlinarith
    linarith
  -- `0 < h₀`, `2h₀ ≤ H`
  have hh₀pos : 0 < h₀ := Nat.floor_pos.mpr (by linarith)
  have h2h₀ : 2 * h₀ ≤ H := by
    have hden : (64:ℝ) ≤ 64 * Real.pi * Q ^ 2 := by
      have h1 : (1:ℝ) ≤ Q ^ 2 := one_le_pow₀ hQ1
      nlinarith
    have ht64 : t ≤ (H : ℝ) / 64 := by
      rw [htdef, div_le_div_iff₀ (by positivity) (by norm_num)]
      calc ε * H * 64 ≤ (H : ℝ) * 64 := by nlinarith
        _ ≤ (H : ℝ) * (64 * Real.pi * Q ^ 2) := mul_le_mul_of_nonneg_left hden hHpos.le
    have : (h₀ : ℝ) ≤ (H : ℝ) / 2 := by linarith
    exact_mod_cast (by linarith : (2 * h₀ : ℝ) ≤ H)
  -- `H ≤ h₀²` (for the level-prime bound)
  have hHh₀ : (H : ℝ) ≤ (h₀ : ℝ) ^ 2 := by
    -- `t² ≥ 4H` from `T·Q^{2k+4} ≥ (128πQ²/ε)²·Q^{2k}·...`: use `T ≥ (128π/ε)²`, `Q^{2k+4} ≥ Q⁴`
    have hTQ : (128 * Real.pi / ε) ^ 2 * Q ^ 4 ≤ (H : ℝ) := by
      calc (128 * Real.pi / ε) ^ 2 * Q ^ 4
          ≤ T * Q ^ (2 * k + 4) := by
            refine mul_le_mul ?_ (pow_le_pow_right₀ hQ1 (by omega)) (by positivity) hT0.le
            rw [hT]
            have : (0:ℝ) ≤ (64 * Real.pi / ε) * ((h₁ : ℝ) + 2 + C₁ * (128 / ε) ^ k) := by
              positivity
            linarith
        _ ≤ H := hTH
    have ht4 : 4 * (H : ℝ) ≤ t ^ 2 := by
      rw [htdef, div_pow]
      rw [le_div_iff₀ (by positivity)]
      have : (128 * Real.pi / ε) ^ 2 * Q ^ 4 * ε ^ 2 = 4 * (64 * Real.pi * Q ^ 2) ^ 2 := by
        field_simp
        ring
      calc 4 * (H : ℝ) * (64 * Real.pi * Q ^ 2) ^ 2
          = (H : ℝ) * (4 * (64 * Real.pi * Q ^ 2) ^ 2) := by ring
        _ = (H : ℝ) * ((128 * Real.pi / ε) ^ 2 * Q ^ 4 * ε ^ 2) := by rw [this]
        _ ≤ (H : ℝ) * ((H : ℝ) * ε ^ 2) := by
            gcongr
        _ = (ε * H) ^ 2 := by ring
    -- `h₀ ≥ t/2` since `t ≥ 2`
    have hth : t / 2 ≤ (h₀ : ℝ) := by
      have : (2:ℝ) ≤ t := by linarith
      linarith
    calc (H : ℝ) ≤ t ^ 2 / 4 := by linarith
      _ = (t / 2) ^ 2 := by ring
      _ ≤ (h₀ : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hth 2
  -- invoke the Prop at `(ε', h₀)`
  obtain ⟨levels, A₀, hA₀1, hlv, hbig, hdens, hms⟩ :=
    hProp (ε / (128 * Q)) hε'0 h₀ hh₁ hCε'
  refine ⟨Q, h₀, levels, A₀, hQ1, hQQ, hA₀1, hh₀pos, h2h₀, hh₀t, hlv, ?_, hdens, hms⟩
  -- level primes exceed `Q`: `2^B C (log h₀)^B = C (log h₀²)^B ≥ C (log H)^B`, and `p ≥ 2 > 1`
  intro P hP p hp
  have hpQ := hbig P hP p hp
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (hlv P hP p hp).two_le
  have hh₀R : (1:ℝ) ≤ h₀ := by exact_mod_cast hh₀pos
  have hlogH : Real.log H ≤ 2 * Real.log h₀ := by
    have hsq : Real.log ((h₀ : ℝ) ^ 2) = 2 * Real.log h₀ := by
      rw [Real.log_pow]
      norm_num
    rw [← hsq]
    exact Real.log_le_log hHpos hHh₀
  have hlog0 : 0 ≤ Real.log H := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ H))
  have hCB : C * Real.log H ^ B ≤ 2 ^ B * C * Real.log h₀ ^ B := by
    calc C * Real.log H ^ B ≤ C * (2 * Real.log h₀) ^ B :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlogH B) hC.le
      _ = 2 ^ B * C * Real.log h₀ ^ B := by rw [mul_pow]; ring
  rw [hQdef, max_lt_iff]
  exact ⟨lt_of_le_of_lt hCB hpQ, by linarith⟩

end Tao2015

end MoltResearch
