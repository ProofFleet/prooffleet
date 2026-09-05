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

/-- **The good-block coefficient** (Track R, R7-4): with `q ≤ Q`, `h₀ ≤ εH/(64πQ²)` and
`|δ| ≤ Q/(Hq)`, the four terms of `good_block_total_le`'s coefficient at `ε' = ε/(128Q)`,
`εc = ε/48` are at most `ε/8`, `ε/64`, `ε/16`, `ε/8`: total `(21/64)ε`. -/
theorem good_block_coef_le (Q ε : ℝ) (q h₀ H : ℕ) (δ : ℝ) (hε : 0 < ε) (hQ1 : 1 ≤ Q)
    (hq : 0 < q) (hH : 0 < H) (hqQ : (q : ℝ) ≤ Q)
    (hh₀Q : (h₀ : ℝ) ≤ ε * H / (64 * Real.pi * Q ^ 2)) (harc : |δ| ≤ Q / ((H : ℝ) * q)) :
    16 * q * (ε / (128 * Q)) + q * h₀ / H + 4 * Real.pi * q ^ 2 * |δ| * h₀ + 6 * (ε / 48)
      ≤ (21 / 64) * ε := by
  have hQ0 : 0 < Q := by linarith
  have hHR : (0:ℝ) < H := by exact_mod_cast hH
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hπ1 : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hπQ : (1:ℝ) ≤ Real.pi * Q := one_le_mul_of_one_le_of_one_le hπ1 hQ1
  have hqQ' : (q : ℝ) / Q ≤ 1 := by rw [div_le_one hQ0]; exact hqQ
  have hc1 : 16 * q * (ε / (128 * Q)) ≤ ε / 8 := by
    have : 16 * (q : ℝ) * (ε / (128 * Q)) = (q / Q) * (ε / 8) := by
      field_simp
      ring
    rw [this]
    exact mul_le_of_le_one_left (by positivity) hqQ'
  have hc2 : (q : ℝ) * h₀ / H ≤ ε / 64 := by
    have h1 : (q : ℝ) * h₀ ≤ Q * (ε * H / (64 * Real.pi * Q ^ 2)) :=
      mul_le_mul hqQ hh₀Q (by positivity) hQ0.le
    have h2 : Q * (ε * H / (64 * Real.pi * Q ^ 2)) ≤ ε * H / 64 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      have hεH : (0:ℝ) ≤ ε * H := by positivity
      have hint : 0 ≤ ε * H * Q * (Real.pi * Q - 1) :=
        mul_nonneg (mul_nonneg hεH hQ0.le) (sub_nonneg.mpr hπQ)
      nlinarith [hint]
    rw [div_le_iff₀ hHR]
    linarith
  have hc3 : 4 * Real.pi * q ^ 2 * |δ| * h₀ ≤ ε / 16 := by
    have h1 : |δ| * h₀ ≤ Q / ((H : ℝ) * q) * (ε * H / (64 * Real.pi * Q ^ 2)) :=
      mul_le_mul harc hh₀Q (by positivity) (by positivity)
    have h2 : 4 * Real.pi * (q : ℝ) ^ 2 * (Q / ((H : ℝ) * q) * (ε * H / (64 * Real.pi * Q ^ 2)))
        = (q / Q) * (ε / 16) := by
      field_simp
      ring
    calc 4 * Real.pi * (q : ℝ) ^ 2 * |δ| * h₀
        = 4 * Real.pi * (q : ℝ) ^ 2 * (|δ| * h₀) := by ring
      _ ≤ 4 * Real.pi * (q : ℝ) ^ 2 * (Q / ((H : ℝ) * q) * (ε * H / (64 * Real.pi * Q ^ 2))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (q / Q) * (ε / 16) := h2
      _ ≤ ε / 16 := mul_le_of_le_one_left (by positivity) hqQ'
  linarith

/-- **The size conditions of a good block** (Track R, R7-4): a block start
`Ab ≥ Q(6H + 7Q + A₀ + 2)` with `q ≤ Q` satisfies `6qH ≤ Ab`, `7q² ≤ Ab` and
`⌈A₀⌉₊ + 1 ≤ ⌊Ab/q⌋`. -/
theorem good_block_sizes (Q A₀ : ℝ) (q H Ab : ℕ) (hQ1 : 1 ≤ Q) (hA₀0 : 0 ≤ A₀) (hq : 0 < q)
    (hqQ : (q : ℝ) ≤ Q) (hbase : Q * (6 * H + 7 * Q + A₀ + 2) ≤ Ab) :
    6 * q * H ≤ Ab ∧ 7 * q ^ 2 ≤ Ab ∧ ⌈A₀⌉₊ + 1 ≤ Ab / q := by
  have hQ0 : 0 < Q := by linarith
  have hH0 : (0:ℝ) ≤ H := Nat.cast_nonneg H
  have hrest : 0 ≤ 7 * Q + A₀ + 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have : ((6 * q * H : ℕ) : ℝ) ≤ Ab := by
      push_cast
      calc (6 : ℝ) * q * H ≤ 6 * Q * H := by gcongr
        _ ≤ Q * (6 * H + 7 * Q + A₀ + 2) := by nlinarith
        _ ≤ Ab := hbase
    exact_mod_cast this
  · have : ((7 * q ^ 2 : ℕ) : ℝ) ≤ Ab := by
      push_cast
      calc (7 : ℝ) * q ^ 2 ≤ 7 * Q ^ 2 := by gcongr
        _ ≤ Q * (6 * H + 7 * Q + A₀ + 2) := by nlinarith
        _ ≤ Ab := hbase
    exact_mod_cast this
  · rw [Nat.le_div_iff_mul_le hq]
    have hceil : (⌈A₀⌉₊ : ℝ) < A₀ + 1 := Nat.ceil_lt_add_one hA₀0
    have : (((⌈A₀⌉₊ + 1) * q : ℕ) : ℝ) ≤ Ab := by
      push_cast
      calc ((⌈A₀⌉₊ : ℝ) + 1) * q ≤ (A₀ + 2) * Q :=
            mul_le_mul (by linarith) hqQ (by positivity) (by linarith)
        _ ≤ Q * (6 * H + 7 * Q + A₀ + 2) := by nlinarith
        _ ≤ Ab := hbase
    exact_mod_cast this

/-- **The per-block trichotomy** (Track R, R7-2 / R7-4).

For a dyadic block `(Ab, 2Ab]` of the cover, `1 ≤ Ab ≤ x'`, with the wrapper's data:
either `Ab < L₀` (a **small** block, priced trivially by its harmonic mass), or `Ab < X`
(a **bad** block, `X ≥ (8x')^{ε/64}`, priced trivially), or the block is **good** —
`Ab ≥ L₀ ≥ Q(6H + 7Q + A₀ + 2)` gives the size conditions of the block bound and
`Ab ≥ X` gives `θ·log(8x') ≤ log(6Ab+1)`, so `nonPretentiousAt_block_of_good` and
`good_block_total_le` price it by `(21/64)·ε` times its harmonic mass. -/
theorem block_total_le_trichotomy
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ p ∈ P, p.Prime)
    (A₀ : ℝ) (hA₀1 : 1 ≤ A₀) (h₀ H : ℕ) (Q ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hQ1 : 1 ≤ Q)
    (hh₀ : 0 < h₀) (h2h₀ : 2 * h₀ ≤ H) (hh₀Q : (h₀ : ℝ) ≤ ε * H / (64 * Real.pi * Q ^ 2))
    (hdens : ∀ A : ℕ, A₀ ≤ A →
      ∑ n ∈ (Finset.Ioc A (2 * A)).filter (fun n => ¬ HasFactorInAll levels n), (1:ℝ)/n
        ≤ (ε / 48) * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n)
    (hms : ∀ A : ℕ, A₀ ≤ A →
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
        NonPretentiousAt g A₀ (2 * A + 1) →
        ∀ J : ℕ, J ≤ A →
          ∑ n ∈ Finset.Ioc A (A + J),
            ‖∑ m ∈ (Finset.Ioc n (n + h₀)).filter (HasFactorInAll levels), g m‖^2 / n
            ≤ (ε / (128 * Q))^2 * (h₀ : ℝ)^2 * ∑ n ∈ Finset.Ioc A (A + J), (1:ℝ)/n)
    (g : ℕ → ℂ) (hg : CompletelyMultiplicativeC g) (hgu : Unimodular g)
    (q : ℕ) (hq : 0 < q) (hqQ : (q : ℝ) ≤ Q) (hql : ∀ P ∈ levels, ∀ p ∈ P, ¬ p ∣ q)
    (a : ℤ) (α : ℝ) (harc : |α - (a : ℝ) / q| ≤ Q / ((H : ℝ) * q))
    (x' : ℕ) (hx' : 1 ≤ x') (A : ℝ) (hnp : NonPretentiousAt g A x')
    (hA8 : Q * A₀ + 50 + 2 * Real.log (64 / ε) ≤ A / 8)
    (L₀ X : ℕ) (hL₀ : Q * (6 * H + 7 * Q + A₀ + 2) ≤ L₀)
    (hX : (8 * (x' : ℝ)) ^ (ε / 64) ≤ X)
    (Ab : ℕ) (hAb1 : 1 ≤ Ab) (hAbx : Ab ≤ x') :
    ∑ n ∈ Finset.Ioc Ab (2 * Ab),
        ‖∑ m ∈ Finset.Ioc n (n + H),
          g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ / ((H : ℝ) * n)
      ≤ (if Ab < L₀ then ∑ n ∈ Finset.Ioc Ab (2 * Ab), (1:ℝ)/n else 0)
        + (if Ab < X then ∑ n ∈ Finset.Ioc Ab (2 * Ab), (1:ℝ)/n else 0)
        + (21 / 64) * ε * ∑ n ∈ Finset.Ioc Ab (2 * Ab), (1:ℝ)/n := by
  have hb : ∀ m, ‖g m‖ ≤ 1 := fun m => (hgu m).le
  have hH : 0 < H := by omega
  have hS0 : 0 ≤ ∑ n ∈ Finset.Ioc Ab (2 * Ab), (1:ℝ)/n :=
    Finset.sum_nonneg fun n _ => by positivity
  have htriv := sum_window_div_le_sum_one_div g hb α Ab H hH
  have hε21 : 0 ≤ (21 / 64) * ε * ∑ n ∈ Finset.Ioc Ab (2 * Ab), (1:ℝ)/n := by positivity
  by_cases hsmall : Ab < L₀
  · rw [if_pos hsmall]
    have : 0 ≤ (if Ab < X then ∑ n ∈ Finset.Ioc Ab (2 * Ab), (1:ℝ)/n else 0) := by
      split_ifs <;> linarith
    linarith
  rw [if_neg hsmall]
  by_cases hbad : Ab < X
  · rw [if_pos hbad]
    linarith
  rw [if_neg hbad, zero_add, zero_add]
  -- the good block
  push_neg at hsmall hbad
  have hAbR : (L₀ : ℝ) ≤ Ab := by exact_mod_cast hsmall
  have hA₀0 : 0 ≤ A₀ := by linarith
  have hbaseR : Q * (6 * H + 7 * Q + A₀ + 2) ≤ Ab := le_trans hL₀ hAbR
  obtain ⟨h6, h7, hA₀q⟩ := good_block_sizes Q A₀ q H Ab hQ1 hA₀0 hq hqQ hbaseR
  -- the good-block condition and the block non-pretentiousness
  have hθ0 : 0 < ε / 64 := by positivity
  have hθ1 : ε / 64 ≤ 1 := by linarith
  have hgood : (ε / 64) * Real.log ((8 * x' : ℕ) : ℝ) ≤ Real.log ((6 * Ab + 1 : ℕ) : ℝ) := by
    have hXAb : (X : ℝ) ≤ Ab := by exact_mod_cast hbad
    have h1 : (8 * (x' : ℝ)) ^ (ε / 64) ≤ ((6 * Ab + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h2 : Real.log ((8 * (x' : ℝ)) ^ (ε / 64)) = (ε / 64) * Real.log ((8 * x' : ℕ) : ℝ) := by
      rw [Real.log_rpow (by positivity)]
      push_cast
      ring
    rw [← h2]
    exact Real.log_le_log (by positivity) h1
  have hnp' : NonPretentiousAt g (q * A₀ + 26) (6 * Ab + 1) := by
    refine nonPretentiousAt_block_of_good g hgu x' Ab hx' hAb1 hAbx hnp (ε / 64) hθ0 hθ1 hgood
      (q * A₀ + 26) (by positivity) ?_
    rw [one_div_div]
    have : (q : ℝ) * A₀ ≤ Q * A₀ := mul_le_mul_of_nonneg_right hqQ hA₀0
    linarith
  have hmain := good_block_total_le levels hlv A₀ hA₀1 h₀ (ε / (128 * Q)) (ε / 48)
    (by positivity) (by positivity) hdens hms g hg hgu q hq hql a α Ab H hh₀ h2h₀ h6 h7 hA₀q hnp'
  have hcoef := good_block_coef_le Q ε q h₀ H (α - (a : ℝ) / q) hε hQ1 hq hH hqQ hh₀Q harc
  exact le_trans hmain (mul_le_mul_of_nonneg_right hcoef hS0)

/-- **The cost of the bad blocks** (Track R, R7-2).

The blocks `(2^k, 2^{k+1}]` of the cover of `(lo, hi]` with `2^k < X`, where
`X ≤ (8x')^θ + 1`, `θ ≤ 1/2`, carry harmonic mass at most `2 + 15θ + 2θ·log w`
provided `lo ≥ (x/w)/2` and `x' ≤ 2x`.  Either no such block exists (`lo ≥ 2X`), or
`lo < 2X ≤ 4(8x')^θ` forces `log x ≤ 2log w + 9`, and the trivial cost
`log(2X) ≤ log 4 + θ·log(8x')` is then `≤ 2 + θ(3 + log x)`. -/
theorem bad_blocks_sum_le (lo hi x' : ℕ) (x w θ : ℝ) (hθ0 : 0 < θ)
    (hθ : θ ≤ 1 / 2) (hx1 : 1 ≤ x) (hw1 : 1 ≤ w) (hlo : x / w / 2 ≤ lo)
    (hx'1 : 1 ≤ x') (hx' : (x' : ℝ) ≤ 2 * x) (X : ℕ) (hX1 : 1 ≤ X)
    (hXle : (X : ℝ) ≤ (8 * (x' : ℝ)) ^ θ + 1) :
    ∑ k ∈ (Finset.Icc (Nat.log 2 lo) (Nat.log 2 hi)).filter (fun k => 2 ^ k < X),
        ∑ n ∈ Finset.Ioc (2 ^ k : ℕ) (2 ^ (k + 1)), (1:ℝ)/n
      ≤ 2 + 15 * θ + 2 * θ * Real.log w := by
  classical
  have hlogw : 0 ≤ Real.log w := Real.log_nonneg hw1
  have hlog2 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hlo2 : lo < 2 * X
  · -- bad blocks may exist: their total is `≤ log(2X)`
    have hsum := sum_filter_pow_lt_one_div_le (Nat.log 2 lo) (Nat.log 2 hi) X hX1
    have h8x' : (1:ℝ) ≤ 8 * (x' : ℝ) := by
      have : (1:ℝ) ≤ x' := by exact_mod_cast hx'1
      linarith
    have hr1 : (1:ℝ) ≤ (8 * (x' : ℝ)) ^ θ := Real.one_le_rpow h8x' hθ0.le
    have h2X : 2 * (X : ℝ) ≤ 4 * (8 * (x' : ℝ)) ^ θ := by linarith
    have hlogX : Real.log (2 * (X : ℝ)) ≤ Real.log 4 + θ * Real.log (8 * (x' : ℝ)) := by
      calc Real.log (2 * (X : ℝ)) ≤ Real.log (4 * (8 * (x' : ℝ)) ^ θ) :=
            Real.log_le_log (by positivity) h2X
        _ = Real.log 4 + θ * Real.log (8 * (x' : ℝ)) := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by positivity)]
    have hlog8x' : Real.log (8 * (x' : ℝ)) ≤ Real.log 16 + Real.log x := by
      calc Real.log (8 * (x' : ℝ)) ≤ Real.log (16 * x) :=
            Real.log_le_log (by positivity) (by linarith)
        _ = Real.log 16 + Real.log x := Real.log_mul (by norm_num) (by linarith)
    -- crude numerics: `log 4 ≤ 2`, `log 8 ≤ 3`, `log 16 ≤ 3`
    have hl4 : Real.log 4 ≤ 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    have hl8 : Real.log 8 ≤ 3 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; linarith
    have hl16 : Real.log 16 ≤ 3 := by
      rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith
    -- `lo < 2X` forces `log x ≤ 2 log w + 9`
    have hxw : x / w < 8 * (8 * (x' : ℝ)) ^ θ := by
      have hloR : (lo : ℝ) < 2 * X := by exact_mod_cast hlo2
      linarith
    have hlogx : Real.log x ≤ 2 * Real.log w + 9 := by
      have hxw0 : 0 < x / w := by positivity
      have h1 : Real.log (x / w) ≤ Real.log (8 * (8 * (x' : ℝ)) ^ θ) :=
        Real.log_le_log hxw0 hxw.le
      rw [Real.log_div (by linarith) (by linarith),
        Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by positivity)] at h1
      have h2 : Real.log x - Real.log w ≤ 3 + θ * (3 + Real.log x) := by
        have : θ * Real.log (8 * (x' : ℝ)) ≤ θ * (Real.log 16 + Real.log x) :=
          mul_le_mul_of_nonneg_left hlog8x' hθ0.le
        nlinarith
      have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
      nlinarith
    calc ∑ k ∈ (Finset.Icc (Nat.log 2 lo) (Nat.log 2 hi)).filter (fun k => 2 ^ k < X),
          ∑ n ∈ Finset.Ioc (2 ^ k : ℕ) (2 ^ (k + 1)), (1:ℝ)/n
        ≤ Real.log (2 * (X : ℝ)) := hsum
      _ ≤ Real.log 4 + θ * Real.log (8 * (x' : ℝ)) := hlogX
      _ ≤ 2 + θ * (3 + (2 * Real.log w + 9)) := by
          have : θ * Real.log (8 * (x' : ℝ)) ≤ θ * (3 + (2 * Real.log w + 9)) := by
            apply mul_le_mul_of_nonneg_left _ hθ0.le
            linarith
          linarith
      _ = 2 + 12 * θ + 2 * θ * Real.log w := by ring
      _ ≤ 2 + 15 * θ + 2 * θ * Real.log w := by linarith
  · -- no bad block: every `2^k ≥ 2^{⌊log₂ lo⌋} > lo/2 ≥ X`
    push_neg at hlo2
    have hempty : (Finset.Icc (Nat.log 2 lo) (Nat.log 2 hi)).filter (fun k => 2 ^ k < X) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro k hk
      rw [Finset.mem_Icc] at hk
      have h1 : lo < 2 ^ (Nat.log 2 lo + 1) := Nat.lt_pow_succ_log_self (by norm_num) lo
      have h2 : 2 ^ (Nat.log 2 lo) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk.1
      rw [pow_succ] at h1
      omega
    rw [hempty, Finset.sum_empty]
    positivity

end Tao2015

end MoltResearch
