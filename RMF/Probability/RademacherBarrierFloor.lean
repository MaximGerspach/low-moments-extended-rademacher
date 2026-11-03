/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherBarrierSharp

/-!
# The Rademacher bad sets at the chaining slope `8`

At the chaining slope `Λ₁ = 7` the sharp Lemma B.2 covers the upper level `A + j + b ≤ 6j` only
from `j ≥ 8Δ₁`, which puts the block bad sets at the level `harperBadLevel E₀ = 32Δ`.  At
`Λ₁ = 8`, `6j ≤ 8(j - Δ₁)` already from `j ≥ 4Δ₁`, and the level floor halves:
`RMF.radBlockBadLevel E₀ = 16Δ` (`RMF.measureReal_not_mesoGood_le_rademacher_floor`).
The chaining constant `RMF.radChainConst` does not see `Λ₁`, and the pair tail at `8` is
`≤ 10¹⁵`, so the primes' threshold is `≤ 10¹²⁰ ≤ exp(e^{16})`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-! ### The threshold at `Λ₁ = 8` -/

/-- `radPairTailConst (1/2) 8 ≤ 10¹⁵`. -/
lemma radPairTailConst_eight_le : radPairTailConst (1 / 2) 8 ≤ 1000000000000000 := by
  have hL := radLocalPairConst_le
  have hL0 : (0 : ℝ) ≤ radLocalPairConst ((2 : ℝ) ^ (-(1 / 2 : ℝ))) := by
    have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hθ : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := lt_of_le_of_lt two_rpow_neg_half_le (by norm_num)
    exact (abs_log_local_pair_rademacherLaw_le_explicit hθ0 hθ).1.le
  have hT := tsum_nat_rpow_neg_le (s := 3 * (((1 / 2 + 1 / 3) / 2 + 1 / 3) / 2)) (by norm_num)
  have hT' : ∑' n : ℕ, (n : ℝ) ^ (-3 * (((1 / 2 + 1 / 3) / 2 + 1 / 3) / 2 : ℝ)) ≤ 9 := by
    have he : (-3 * (((1 / 2 + 1 / 3) / 2 + 1 / 3) / 2 : ℝ))
        = -(3 * (((1 / 2 + 1 / 3) / 2 + 1 / 3) / 2)) := by ring
    rw [he]
    refine le_trans hT (le_of_eq ?_)
    norm_num
  have hT0 : (0 : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 * (((1 / 2 + 1 / 3) / 2 + 1 / 3) / 2 : ℝ)) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hK : (1 + (8 : ℝ) / 2 + 8 / 2 / ((1 / 2 - 1 / 3) / 2)) ^ 3 = 148877 := by norm_num
  unfold radPairTailConst
  rw [hK]
  calc radLocalPairConst ((2 : ℝ) ^ (-(1 / 2 : ℝ))) * 148877
        * ∑' n : ℕ, (n : ℝ) ^ (-3 * (((1 / 2 + 1 / 3) / 2 + 1 / 3) / 2 : ℝ))
      ≤ 40000000 * 148877 * 9 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hL (by norm_num)) hT' hT0 (by norm_num)
    _ ≤ 1000000000000000 := by norm_num

/-- **The sharp Rademacher chain threshold, evaluated**: `radChainThreshold (1/2) 8 ≤ 10¹²⁰`. -/
lemma radChainThreshold_eight_le : radChainThreshold (1 / 2) 8 ≤ (10 : ℝ) ^ 120 := by
  have hP := radPairTailConst_eight_le
  have hP0 : (0 : ℝ) ≤ radPairTailConst (1 / 2) 8 :=
    radPairTailConst_nonneg (by norm_num) (by norm_num)
  have e2 : (3 * (((1 / 2 + 1 / 3) / 2 - 1 / 3) / 2 : ℝ))⁻¹ = ((8 : ℕ) : ℝ) := by norm_num
  unfold radChainThreshold
  rw [e2, Real.rpow_natCast]
  refine max_le (by norm_num) ?_
  calc radPairTailConst (1 / 2) 8 ^ 8 ≤ (1000000000000000 : ℝ) ^ 8 :=
        pow_le_pow_left₀ hP0 hP 8
    _ ≤ (10 : ℝ) ^ 120 := by norm_num

/-- **`radChainThreshold (1/2) 8 ≤ exp(e^{16})`**: every block of Harper's scales at an offset
`ϑ ≥ 16` starts past the sharp Rademacher chaining threshold. -/
lemma radChainThreshold_eight_le_exp_exp_sixteen :
    radChainThreshold (1 / 2) 8 ≤ Real.exp (Real.exp 16) :=
  le_trans radChainThreshold_eight_le ten_pow_hundred_twenty_le_exp_exp_sixteen

/-! ### Lemma 2.3 at one index, at the slope `8` -/

/-- **Hamdan's Lemma 2.3 for the Rademacher RMF at one index, at the chaining slope `8`.**  At
`Λ₁ = 8` the index needs only `j ≥ 4Δ₁` (and `j ≥ Δ₂`), since `6j ≤ 8(j - Δ₁)`.  For
`|a - j| ≤ Δ₁`, `∑_p p^{-1-2δ} log p ≤ e^{j+ϑ} + Δ₂`, `A ≤ 4j`, `b ≤ j`, primes from
`⌊blockScale ϑ 0⌋₊ + 1 ≥ radChainThreshold (1/2) 8` and a window of width `w ≥ e^{-(j+ϑ)}`:

`P(∃h ∈ [h₀, h₀+w) : log‖F(1/2+δ+ih)‖ ∉ [-A - cj, A + j + b])`
`≤ radIndexConst Δ₁ · w e^ϑ e^{-2A} e^{-2b}`. -/
theorem IsRademacherRMF.measureReal_index_le_of_le_floor {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ)
    {Δ₁ Δ₂ ϑ A b c δ h₀ w : ℝ} {j : ℕ} (hΔ₁ : 1 ≤ Δ₁) (hϑ : 1 ≤ ϑ)
    (hϑ₀ : radChainThreshold (1 / 2) 8 ≤ ((⌊blockScale ϑ 0⌋₊ + 1 : ℕ) : ℝ))
    (hA0 : 0 ≤ A) (hb0 : 0 ≤ b) (hc : 20 ≤ c) (hδ0 : 0 ≤ δ)
    (hupA : (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ₁)
    (hlowA : (j : ℝ) - Δ₁ ≤ ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)))
    (hP : (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Real.exp ((j : ℝ) + ϑ) + Δ₂)
    (hτC : 4 * Δ₁ ≤ (j : ℝ)) (hτΔ : Δ₂ ≤ (j : ℝ)) (hA : A ≤ 4 * (j : ℝ)) (hb : b ≤ (j : ℝ))
    (hw : Real.exp (-((j : ℝ) + ϑ)) ≤ w) :
    μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w),
        Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
            (heightLine (1 / 2 + δ) h) ω‖
          ∉ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b)}
      ≤ radIndexConst Δ₁ * w * Real.exp ϑ * Real.exp (-(2 * A)) * Real.exp (-(2 * b)) := by
  have hK : radIndexRefine = 1152 := rfl
  have hK0 : (0 : ℝ) < radIndexRefine := by rw [hK]; norm_num
  have hK1 : (1 : ℝ) ≤ radIndexRefine := by rw [hK]; norm_num
  have hΛ₂ : (0 : ℝ) < 2 / radIndexRefine := by positivity
  have hΛ₂576 : 576 * (2 / radIndexRefine) ≤ 1 := by rw [hK]; norm_num
  have hCs := radChainConst_pos hΛ₂
  set Cs := radChainConst (2 / radIndexRefine) with hCs_expl
  set K := radIndexRefine with hK_expl
  have hδσ : (1 : ℝ) / 2 ≤ 1 / 2 + δ := by linarith
  have hσ₀ : (1 : ℝ) / 3 < 1 / 2 := by norm_num
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  haveI := hX.isProbabilityMeasure
  set τ := (j : ℝ) with hτdef
  have hτ8 : 4 * Δ₁ ≤ τ := hτC
  have hτΔ₂ : Δ₂ ≤ τ := hτΔ
  have hτ0 : (0 : ℝ) < τ := by linarith
  set a := ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
    (p : ℝ) ^ (-2 * (1 / 2 + δ)) with hadef
  clear_value τ a
  have hale : a ≤ τ + Δ₁ := by linarith
  have hage : τ - Δ₁ ≤ a := by linarith
  have ha1 : (1 : ℝ) ≤ a := by linarith
  -- the partition of `[h₀, h₀+w)` into intervals of width `(K e^{τ+ϑ})⁻¹`
  obtain ⟨Eτ, hEτdef⟩ : ∃ Eτ : ℝ, Eτ = Real.exp (τ + ϑ) := ⟨_, rfl⟩
  have hEτ0 : (0 : ℝ) < Eτ := by rw [hEτdef]; exact Real.exp_pos _
  have hΔ₂E : Δ₂ ≤ Eτ := by
    have h1 := Real.add_one_le_exp τ
    have h2 : Real.exp τ ≤ Real.exp (τ + ϑ) := Real.exp_le_exp.2 (by linarith)
    rw [hEτdef]
    linarith
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (K * Eτ)⁻¹ := ⟨_, rfl⟩
  have hρ0 : (0 : ℝ) < ρ := by rw [hρdef]; positivity
  have hρinv : K * Eτ * ρ = 1 := by
    rw [hρdef]
    exact mul_inv_cancel₀ (by positivity)
  have hw0 : (0 : ℝ) < w := lt_of_lt_of_le (Real.exp_pos _) hw
  have hwE : (1 : ℝ) ≤ w * Eτ := by
    have h := mul_le_mul_of_nonneg_right hw (Real.exp_pos (τ + ϑ)).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
    rw [hEτdef]
    exact h
  have hKwE : (1 : ℝ) ≤ K * (w * Eτ) := by nlinarith
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈K * (w * Eτ)⌉₊ := ⟨_, rfl⟩
  have hNge : K * (w * Eτ) ≤ (N : ℝ) := by rw [hNdef]; exact Nat.le_ceil _
  have hNle : (N : ℝ) ≤ 2 * (K * (w * Eτ)) := by
    rw [hNdef]
    have hce := Nat.ceil_lt_add_one (by linarith only [hKwE] : (0 : ℝ) ≤ K * (w * Eτ))
    linarith only [hce, hKwE]
  have hNρ : w ≤ (N : ℝ) * ρ := by
    have h := mul_le_mul_of_nonneg_right hNge hρ0.le
    have he : K * (w * Eτ) * ρ = w := by
      calc K * (w * Eτ) * ρ = w * (K * Eτ * ρ) := by ring
        _ = w := by rw [hρinv, mul_one]
    linarith only [h, he]
  -- Lemma B.2's hypotheses, at every interval
  have hrP : ρ * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ 2 / K := by
    have h1 := mul_le_mul_of_nonneg_left hP hρ0.le
    rw [← hEτdef] at h1
    have h2 : ρ * (Eτ + Δ₂) ≤ ρ * (2 * Eτ) := mul_le_mul_of_nonneg_left (by linarith) hρ0.le
    have h3 : ρ * (2 * Eτ) = 2 / K := by
      rw [hρdef]
      field_simp
    linarith
  have h78 : 3 * τ / 4 ≤ a := by linarith
  have hVΛ : A + τ + b ≤ 8 * a := by linarith
  have hWΛ : 6 * τ ≤ 8 * a := by linarith
  have hV0 : (0 : ℝ) ≤ A + τ + b := by linarith
  have hW0 : (0 : ℝ) ≤ 6 * τ := by linarith
  have ha1' : (1 : ℝ) ≤ ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ)) := hadef ▸ ha1
  have hVΛ' : A + τ + b ≤ 8 * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ))) := hadef ▸ hVΛ
  have hWΛ' : 6 * τ ≤ 8 * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ))) := hadef ▸ hWΛ
  -- the two linear exponents, against the entropy of the partition
  have hexpU : Eτ * Real.exp (a - 2 * (A + τ + b))
      ≤ Real.exp ϑ * (Real.exp Δ₁ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))) := by
    have hkey := barrier_upper_exponent_two_le (τ := τ) (A := A) (b := b) (a := a) (C₁ := Δ₁)
      hale
    rw [hEτdef, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hexpL : Eτ * Real.exp (a - 2 * (6 * τ))
      ≤ Real.exp ϑ * (Real.exp Δ₁ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))) := by
    have hkey := barrier_lower_exponent_six_le (τ := τ) (A := A) (b := b) (a := a) (C₀ := Δ₁)
      hale hA hb
    rw [hEτdef, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  -- the two families of events, one per interval, based at `h₀`
  obtain ⟨Eup, hEup⟩ : ∃ E : ℕ → Set Ω, E = fun k : ℕ =>
      {ω | ∃ h ∈ Set.Ico (h₀ + (k : ℝ) * ρ) (h₀ + (k : ℝ) * ρ + ρ),
        A + τ + b < Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (⌊blockScale ϑ 0⌋₊ + 1)
          (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖} := ⟨_, rfl⟩
  obtain ⟨Elo, hElo⟩ : ∃ E : ℕ → Set Ω, E = fun k : ℕ =>
      {ω | ∃ h ∈ Set.Ico (h₀ + (k : ℝ) * ρ) (h₀ + (k : ℝ) * ρ + ρ),
        6 * τ + 4 * a < -Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (⌊blockScale ϑ 0⌋₊ + 1)
          (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖} := ⟨_, rfl⟩
  have hboundU : μ.real (⋃ k ∈ Finset.range N, Eup k)
      ≤ (N : ℝ) * (Cs * Real.exp (a - 2 * (A + τ + b))) := by
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    have hterm : ∀ k ∈ Finset.range N,
        μ.real (Eup k) ≤ Cs * Real.exp (a - 2 * (A + τ + b)) := by
      intro k _
      have h := hf.measure_exists_gt_le_sharp hσ₀ (by norm_num : (2 : ℝ) ≤ 8) hΛ₂ hΛ₂576
        (h₀ := h₀ + (k : ℝ) * ρ) hϑ₀ (⌊blockScale ϑ j⌋₊ + 1) hδσ hρ0 hV0 ha1' hVΛ' hrP
      rw [← hadef] at h
      simp only [hEup]
      exact h
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hboundL : μ.real (⋃ k ∈ Finset.range N, Elo k)
      ≤ (N : ℝ) * (Cs * Real.exp (a - 2 * (6 * τ))) := by
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    have hterm : ∀ k ∈ Finset.range N,
        μ.real (Elo k) ≤ Cs * Real.exp (a - 2 * (6 * τ)) := by
      intro k _
      have h := hf.measure_exists_lt_le_sharp hσ₀ (by norm_num : (2 : ℝ) ≤ 8) hΛ₂ hΛ₂576
        (h₀ := h₀ + (k : ℝ) * ρ) hϑ₀ (⌊blockScale ϑ j⌋₊ + 1) hδσ hρ0 hW0 ha1' hWΛ' hrP
      rw [← hadef] at h
      simp only [hElo]
      exact h
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the failure on this window is covered by the two families
  have hsub : {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w),
      Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖
        ∉ Set.Icc (-A - c * τ) (A + τ + b)}
      ⊆ (⋃ k ∈ Finset.range N, Eup k) ∪ (⋃ k ∈ Finset.range N, Elo k) := by
    rintro ω ⟨h, hh, hnot⟩
    simp only [Set.mem_Ico] at hh
    obtain ⟨k, hkN, hk⟩ := exists_lt_mem_Ico_of_lt (h := h - h₀) hρ0
      (by linarith only [hh.1]) (by linarith only [hh.2]) hNρ
    simp only [Set.mem_Ico] at hk
    have hk' : h ∈ Set.Ico (h₀ + (k : ℝ) * ρ) (h₀ + (k : ℝ) * ρ + ρ) := by
      simp only [Set.mem_Ico]
      exact ⟨by linarith only [hk.1], by linarith only [hk.2]⟩
    simp only [Set.mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with hlt | hgt
    · refine Or.inr (Set.mem_biUnion (Finset.mem_range.2 hkN) ?_)
      simp only [hElo]
      have hct : 20 * τ ≤ c * τ := mul_le_mul_of_nonneg_right hc hτ0.le
      exact ⟨h, hk', by linarith only [hlt, hct, hA0, hale, hτ8, hτ0]⟩
    · refine Or.inl (Set.mem_biUnion (Finset.mem_range.2 hkN) ?_)
      simp only [hEup]
      exact ⟨h, hk', hgt⟩
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_union_le _ _) ?_
  have hR0 : (0 : ℝ) ≤ Real.exp ϑ * (Real.exp Δ₁
      * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))) := by positivity
  have hU : (N : ℝ) * (Cs * Real.exp (a - 2 * (A + τ + b)))
      ≤ 2 * K * Cs * (w * (Real.exp ϑ * (Real.exp Δ₁
        * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))))) := by
    have h1 : (N : ℝ) * Real.exp (a - 2 * (A + τ + b))
        ≤ 2 * K * (w * (Eτ * Real.exp (a - 2 * (A + τ + b)))) := by
      have h := mul_le_mul_of_nonneg_right hNle (Real.exp_pos (a - 2 * (A + τ + b))).le
      linarith only [h]
    have h2 := mul_le_mul_of_nonneg_left hexpU hw0.le
    calc (N : ℝ) * (Cs * Real.exp (a - 2 * (A + τ + b)))
        = Cs * ((N : ℝ) * Real.exp (a - 2 * (A + τ + b))) := by ring
      _ ≤ Cs * (2 * K * (w * (Eτ * Real.exp (a - 2 * (A + τ + b))))) :=
          mul_le_mul_of_nonneg_left h1 hCs.le
      _ ≤ Cs * (2 * K * (w * (Real.exp ϑ * (Real.exp Δ₁
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) hCs.le
      _ = 2 * K * Cs * (w * (Real.exp ϑ * (Real.exp Δ₁
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))))) := by ring
  have hL : (N : ℝ) * (Cs * Real.exp (a - 2 * (6 * τ)))
      ≤ 2 * K * Cs * (w * (Real.exp ϑ * (Real.exp Δ₁
        * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))))) := by
    have h1 : (N : ℝ) * Real.exp (a - 2 * (6 * τ))
        ≤ 2 * K * (w * (Eτ * Real.exp (a - 2 * (6 * τ)))) := by
      have h := mul_le_mul_of_nonneg_right hNle (Real.exp_pos (a - 2 * (6 * τ))).le
      linarith only [h]
    have h2 := mul_le_mul_of_nonneg_left hexpL hw0.le
    calc (N : ℝ) * (Cs * Real.exp (a - 2 * (6 * τ)))
        = Cs * ((N : ℝ) * Real.exp (a - 2 * (6 * τ))) := by ring
      _ ≤ Cs * (2 * K * (w * (Eτ * Real.exp (a - 2 * (6 * τ))))) :=
          mul_le_mul_of_nonneg_left h1 hCs.le
      _ ≤ Cs * (2 * K * (w * (Real.exp ϑ * (Real.exp Δ₁
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) hCs.le
      _ = 2 * K * Cs * (w * (Real.exp ϑ * (Real.exp Δ₁
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))))) := by ring
  have heq : 2 * K * Cs * (w * (Real.exp ϑ * (Real.exp Δ₁
        * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))))
      + 2 * K * Cs * (w * (Real.exp ϑ * (Real.exp Δ₁
        * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))))
      = radIndexConst Δ₁ * w * Real.exp ϑ * Real.exp (-(2 * A)) * Real.exp (-(2 * b)) := by
    rw [radIndexConst]
    ring
  linarith [hboundU, hboundL, hU, hL]

/-! ### Lemma 2.3 over the indices, at the slope `8` -/

/-- **Hamdan's Lemma 2.3 for the Rademacher RMF, at the chaining slope `8`**: the barrier over the
indices `r ≤ j ≤ n` on a window `[h₀, h₀+w)`, `w ≥ e^{-(r+ϑ)}`, at `RMF.radIndexConst Δ₁`, from
`r ≥ 4Δ₁`, `r ≥ Δ₂`.  The union over `j` of
`RMF.IsRademacherRMF.measureReal_index_le_of_le_floor`. -/
theorem IsRademacherRMF.measure_exists_barrier_le_of_le_floor {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ)
    {Δ₁ Δ₂ ϑ A c δ h₀ w : ℝ} {r n : ℕ} {b : ℕ → ℝ} (hΔ₁ : 1 ≤ Δ₁) (hϑ : 1 ≤ ϑ)
    (hϑ₀ : radChainThreshold (1 / 2) 8 ≤ ((⌊blockScale ϑ 0⌋₊ + 1 : ℕ) : ℝ))
    (hA0 : 0 ≤ A) (hc : 20 ≤ c) (hδ0 : 0 ≤ δ) (hCr : 4 * Δ₁ ≤ (r : ℝ)) (hCr₂ : Δ₂ ≤ (r : ℝ))
    (hb0 : ∀ j, r ≤ j → j ≤ n → 0 ≤ b j) (hble : ∀ j, r ≤ j → j ≤ n → b j ≤ (j : ℝ))
    (h4 : ∀ j, r ≤ j → j ≤ n → A ≤ 4 * (j : ℝ))
    (hup : ∀ j, r ≤ j → j ≤ n →
      (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ₁)
    (hlow : ∀ j, r ≤ j → j ≤ n → (j : ℝ) - Δ₁ ≤
      ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)))
    (hlogP : ∀ j, r ≤ j → j ≤ n →
      (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Real.exp ((j : ℝ) + ϑ) + Δ₂)
    (hw : Real.exp (-((r : ℝ) + ϑ)) ≤ w) :
    μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
        Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
            (heightLine (1 / 2 + δ) h) ω‖
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      ≤ radIndexConst Δ₁ * w * Real.exp ϑ * Real.exp (-(2 * A))
        * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  obtain ⟨E, hE⟩ : ∃ E : ℕ → Set Ω, E = fun j : ℕ =>
      {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w),
        Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
            (heightLine (1 / 2 + δ) h) ω‖
          ∉ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)} := ⟨_, rfl⟩
  have hsub : {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
      Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
          (heightLine (1 / 2 + δ) h) ω‖
        ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      ⊆ ⋃ j ∈ Finset.Icc r n, E j := by
    rintro ω ⟨h, hh, hnot⟩
    push Not at hnot
    obtain ⟨j, hjr, hjn, hj⟩ := hnot
    refine Set.mem_biUnion (Finset.mem_Icc.2 ⟨hjr, hjn⟩) ?_
    simp only [hE]
    exact ⟨h, hh, hj⟩
  have hlast : ∑ j ∈ Finset.Icc r n,
        radIndexConst Δ₁ * w * Real.exp ϑ * Real.exp (-(2 * A)) * Real.exp (-(2 * b j))
      = radIndexConst Δ₁ * w * Real.exp ϑ * Real.exp (-(2 * A))
        * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) := by
    rw [Finset.mul_sum]
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun j hj => ?_) (le_of_eq hlast)
  obtain ⟨hjr, hjn⟩ := Finset.mem_Icc.1 hj
  have hjR : (r : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjr
  simp only [hE]
  have hwj : Real.exp (-((j : ℝ) + ϑ)) ≤ w :=
    le_trans (Real.exp_le_exp.2 (by linarith only [hjR])) hw
  exact hf.measureReal_index_le_of_le_floor hΔ₁ hϑ hϑ₀ hA0 (hb0 j hjr hjn) hc hδ0
    (hup j hjr hjn) (hlow j hjr hjn) (hlogP j hjr hjn) (by linarith only [hCr, hjR])
    (by linarith only [hCr₂, hjR])
    (h4 j hjr hjn) (hble j hjr hjn) hwj

/-- **Hamdan's Lemma 2.3 for the squarefree block walk, at the chaining slope `8`**:
`RMF.IsRademacherRMF.measure_exists_barrier_le_of_le_floor` for the walk
`∑_{m<j} ∑_{p ∈ B_m} log‖1 + X_p p^{-s}‖`, which is `log‖F‖` over the block range on the
unimodularity set (`RMF.walk_blockSum_eq_sum_primesIco_of_summand`). -/
theorem IsRademacherPrimeValues.measure_exists_barrier_le_of_le_floor {Ω : Type*}
    [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {Δ₁ Δ₂ ϑ A c δ h₀ w : ℝ} {r n : ℕ} {b : ℕ → ℝ} (hΔ₁ : 1 ≤ Δ₁) (hϑ : 1 ≤ ϑ)
    (hϑ₀ : radChainThreshold (1 / 2) 8 ≤ ((⌊blockScale ϑ 0⌋₊ + 1 : ℕ) : ℝ))
    (hA0 : 0 ≤ A) (hc : 20 ≤ c) (hδ0 : 0 ≤ δ) (hCr : 4 * Δ₁ ≤ (r : ℝ)) (hCr₂ : Δ₂ ≤ (r : ℝ))
    (hb0 : ∀ j, r ≤ j → j ≤ n → 0 ≤ b j) (hble : ∀ j, r ≤ j → j ≤ n → b j ≤ (j : ℝ))
    (h4 : ∀ j, r ≤ j → j ≤ n → A ≤ 4 * (j : ℝ))
    (hup : ∀ j, r ≤ j → j ≤ n →
      (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ₁)
    (hlow : ∀ j, r ≤ j → j ≤ n → (j : ℝ) - Δ₁ ≤
      ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)))
    (hlogP : ∀ j, r ≤ j → j ≤ n →
      (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Real.exp ((j : ℝ) + ϑ) + Δ₂)
    (hw : Real.exp (-((r : ℝ) + ϑ)) ≤ w) :
    μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
        walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      ≤ radIndexConst Δ₁ * w * Real.exp ϑ * Real.exp (-(2 * A))
        * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) := by
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G =
      {ω | ∀ p ∈ Nat.primesBelow (⌊blockScale ϑ n⌋₊ + 1), ‖X p ω‖ ≤ 1} := ⟨_, rfl⟩
  have hGnull : μ Gᶜ = 0 := by
    have h := ae_forall_norm_le_one hX norm_le_one_rademacherLaw (⌊blockScale ϑ n⌋₊ + 1)
    rw [ae_iff] at h
    rw [hGdef, Set.compl_setOf]
    exact h
  have hwalk : ∀ ω ∈ G, ∀ (h : ℝ) (j : ℕ), j ≤ n →
      walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
        = Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
              (heightLine (1 / 2 + δ) h) ω‖ := by
    intro ω hωG h j hjn
    rw [hGdef] at hωG
    have hjm : ⌊blockScale ϑ j⌋₊ ≤ ⌊blockScale ϑ n⌋₊ :=
      Nat.floor_le_floor (blockScale_mono ϑ hjn)
    have hsub : ∀ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        ‖X p ω‖ ≤ 1 := by
      intro p hp
      obtain ⟨hpp, -, hp2⟩ := mem_primesIco.1 hp
      exact hωG p (Nat.mem_primesBelow.2 ⟨by omega, hpp⟩)
    rw [walk_blockSum_eq_sum_primesIco_of_summand ϑ
      (fun p ω => localLogAdd ((p : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X p ω)) j ω]
    exact (log_norm_randomEulerProductIco_sqfree_eq
      (by rw [re_heightLine]; linarith) hsub).symm
  have hset : G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
        walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      = G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
        Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
              (heightLine (1 / 2 + δ) h) ω‖
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)} := by
    ext ω
    constructor
    · rintro ⟨hωG, h, hh, hnot⟩
      exact ⟨hωG, h, hh, fun hall => hnot fun j hjr hjn => by
        rw [hwalk ω hωG h j hjn]; exact hall j hjr hjn⟩
    · rintro ⟨hωG, h, hh, hnot⟩
      exact ⟨hωG, h, hh, fun hall => hnot fun j hjr hjn => by
        rw [← hwalk ω hωG h j hjn]; exact hall j hjr hjn⟩
  calc μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
        walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      = μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
          Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
              (heightLine (1 / 2 + δ) h) ω‖
            ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)} := by
        unfold MeasureTheory.Measure.real
        rw [measure_eq_measure_inter_of_compl_null hGnull _, hset,
          ← measure_eq_measure_inter_of_compl_null hGnull _]
    _ ≤ radIndexConst Δ₁ * w * Real.exp ϑ * Real.exp (-(2 * A))
          * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) :=
        hf.measure_exists_barrier_le_of_le_floor hΔ₁ hϑ hϑ₀ hA0 hc hδ0 hCr hCr₂ hb0 hble h4 hup
          hlow hlogP hw

/-! ### The bad sets, from the level `16Δ` -/

/-- **The level floor of the block bad sets at the chaining slope `8`**: `16(1 + 45√E₀)`, half of
`RMF.harperBadLevel`. -/
noncomputable def radBlockBadLevel (E₀ : ℝ) : ℝ := 16 * harperSharpDeficit E₀

lemma one_le_radBlockBadLevel (E₀ : ℝ) : 1 ≤ radBlockBadLevel E₀ := by
  unfold radBlockBadLevel harperSharpDeficit
  have := Real.sqrt_nonneg E₀
  linarith

set_option maxHeartbeats 400000 in
-- the deficit, the threshold and the barrier, fed to one theorem as in the Steinhaus bad sets
/-- **The bad sets of a mesoscopic block, at the level floor `16Δ`.**  For the walk at offset
`ϑ = harperOffset D x ≥ 16` over `n = harperBlockCount D x` blocks, the good set
`G_a(h) = mesoGood Y ϑ c n ⌈a/4⌉ a (β log) (½ + σ + ih)` (`c = prop5UpperSlope`, `β ∈ (1/2, 2]`)
fails somewhere on the window `[T/e, T]`, `1 ≤ T e^ϑ`, with probability

`≤ radBlockBadConst E₀ β·(T e^ϑ)·e^{-2a}`,  `a ≥ radBlockBadLevel E₀ = 16(1 + 45√E₀)`,

for `0 ≤ σ` with `σ log x ≤ η ≤ E₀`: Lemma 2.3 at the chaining slope `8`
(`RMF.IsRademacherPrimeValues.measure_exists_barrier_le_of_le_floor`), at the deficit
`1 + 45√E₀` (`RMF.abs_sum_primesIco_rpow_sub_le_of_le'`) and no excess
(`RMF.sum_primesIco_rpow_log_le_exp`), on a window of width `T`.  The Rademacher counterpart of
`RMF.measureReal_not_harperGoodSlopeOf_le_of_harperThreshold`. -/
theorem measureReal_not_mesoGood_le_rademacher_floor {Ω : Type*} [MeasurableSpace Ω]
    (E₀ β : ℝ) (hβ : 1 / 2 < β) (hβ2 : β ≤ 2) {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {x σ η a T : ℝ} {D : ℕ} (hx1 : 1 < x)
    (hDlog : (D : ℝ) ≤ Real.log (Real.log x)) (hϑ16 : (16 : ℝ) ≤ harperOffset D x)
    (hσ0 : 0 ≤ σ) (hη0 : 0 ≤ η) (hηE : η ≤ E₀) (hσx : |σ| * Real.log x ≤ η) (hT0 : 0 < T)
    (hTθ : 1 ≤ T * Real.exp (harperOffset D x)) (ha : radBlockBadLevel E₀ ≤ a) :
    ν.real {ω | ∃ h ∈ Set.Icc (T / Real.exp 1) T,
        ω ∉ mesoGood Y (harperOffset D x) prop5UpperSlope (harperBlockCount D x) ⌈a / 4⌉₊ a
          (fun j => β * Real.log j) (shiftLine σ h)}
      ≤ radBlockBadConst E₀ β * (T * Real.exp (harperOffset D x)) * Real.exp (-(2 * a)) := by
  haveI := hY.isProbabilityMeasure
  set ϑ := harperOffset D x with hϑdef
  set n := harperBlockCount D x with hndef
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ, Δ = 1 + 45 * √E₀ := ⟨_, rfl⟩
  have hΔ1 : (1 : ℝ) ≤ Δ := by
    rw [hΔdef]
    linarith [Real.sqrt_nonneg E₀]
  set Lv := 4 * Δ with hLv_expl
  have hWa : radBlockBadLevel E₀ = 4 * Lv := by
    unfold radBlockBadLevel harperSharpDeficit
    rw [← hΔdef]
    ring
  have hWB : radBlockBadConst E₀ β = radIndexConst Δ * ∑' i : ℕ, (i : ℝ) ^ (-(2 * β)) := by
    unfold radBlockBadConst harperSharpDeficit
    rw [← hΔdef]
  rw [hWa] at ha
  rw [hWB]
  have hϑ3 : (3 : ℝ) ≤ ϑ := by linarith
  have hδtop : |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η := by
    rw [hϑdef, hndef, log_blockScale_harperOffset_top hx1 hDlog]
    exact hσx
  have hps : ∀ j, j ≤ n →
      |(∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1)
          (⌊blockScale ϑ j⌋₊ + 1), (p : ℝ) ^ (-2 * (1 / 2 + σ))) - (j : ℝ)|
        ≤ 45 * √η + 120 * Real.exp 2 * Real.exp (-(1 + ϑ)) := fun j hj =>
    abs_sum_primesIco_rpow_sub_le_of_le' hϑ3 (by omega) hη0 hσ0 hδtop
  have hsmall : 120 * Real.exp 2 * Real.exp (-(1 + ϑ)) ≤ 1 := by
    have h1 : Real.exp 2 * Real.exp (-(1 + ϑ)) * Real.exp (ϑ - 1) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      simp only [show 2 + -(1 + ϑ) + (ϑ - 1) = 0 by ring, Real.exp_zero]
    have h2 : (120 : ℝ) ≤ Real.exp (ϑ - 1) := by
      have ht : (15 : ℝ) ≤ ϑ - 1 := by linarith
      have hq := Real.quadratic_le_exp_of_nonneg (x := ϑ - 1) (by linarith)
      have ht2 : (225 : ℝ) ≤ (ϑ - 1) ^ 2 := by
        have h := mul_le_mul ht ht (by norm_num) (by linarith)
        calc (225 : ℝ) = 15 * 15 := by norm_num
          _ ≤ (ϑ - 1) * (ϑ - 1) := h
          _ = (ϑ - 1) ^ 2 := by ring
      linarith
    have h3 : (0 : ℝ) ≤ Real.exp 2 * Real.exp (-(1 + ϑ)) := by positivity
    nlinarith
  have hpsΔ : ∀ j, j ≤ n →
      |(∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1)
          (⌊blockScale ϑ j⌋₊ + 1), (p : ℝ) ^ (-2 * (1 / 2 + σ))) - (j : ℝ)| ≤ Δ := by
    intro j hj
    refine le_trans (hps j hj) ?_
    have hsq : √η ≤ √E₀ := Real.sqrt_le_sqrt hηE
    rw [hΔdef]
    linarith
  have haC₂ : 4 * Lv ≤ a := ha
  have ha1 : (1 : ℝ) ≤ a := by linarith
  have hr1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
  have hrge : a / 4 ≤ (⌈a / 4⌉₊ : ℝ) := Nat.le_ceil _
  have hCr : Lv ≤ ((⌈a / 4⌉₊ : ℕ) : ℝ) := by linarith
  have h4 : ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ n → a ≤ 4 * (j : ℝ) := by
    intro j hj _
    have : ((⌈a / 4⌉₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have hlog : ∀ j, ⌈a / 4⌉₊ ≤ j → (0 : ℝ) ≤ Real.log j := by
    intro j hj
    exact Real.log_nonneg (by exact_mod_cast le_trans hr1 hj)
  have hϑ1 : (1 : ℝ) ≤ ϑ := by linarith
  have hϑ₀ : radChainThreshold (1 / 2) 8 ≤ ((⌊blockScale ϑ 0⌋₊ + 1 : ℕ) : ℝ) := by
    have hbs : Real.exp (Real.exp 16) ≤ blockScale ϑ 0 := by
      unfold blockScale
      exact Real.exp_le_exp.2 (Real.exp_le_exp.2 (by push_cast; linarith))
    have hfl := Nat.lt_floor_add_one (blockScale ϑ 0)
    have ht := radChainThreshold_eight_le_exp_exp_sixteen
    push_cast
    linarith
  -- the window `[T/e, T]` inside `[T/e, T/e + T)`, which is wide enough for the mesh
  have hw : Real.exp (-(((⌈a / 4⌉₊ : ℕ) : ℝ) + ϑ)) ≤ T := by
    have hr0 : (0 : ℝ) ≤ ((⌈a / 4⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hθ0 : (0 : ℝ) < Real.exp ϑ := Real.exp_pos _
    have h1 : Real.exp (-(((⌈a / 4⌉₊ : ℕ) : ℝ) + ϑ)) ≤ Real.exp (-ϑ) :=
      Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-ϑ) ≤ T := by
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hθ0]
      linarith [hTθ]
    linarith
  have hbar := hY.measure_exists_barrier_le_of_le_floor (A := a) (c := prop5UpperSlope)
    (δ := σ) (h₀ := T / Real.exp 1) (w := T)
    (r := ⌈a / 4⌉₊) (n := n) (b := fun j => β * Real.log j) (Δ₂ := 0) hΔ1 hϑ1 hϑ₀
    (by linarith) twenty_le_prop5UpperSlope hσ0 hCr (Nat.cast_nonneg _)
    (fun j hj _ => mul_nonneg (by linarith) (hlog j hj))
    (fun j hj _ => mul_log_le_self (by linarith) hβ2 (le_trans hr1 hj)) h4
    (fun j _ hjn => by linarith [(abs_le.1 (hpsΔ j hjn)).2])
    (fun j _ hjn => by linarith [(abs_le.1 (hpsΔ j hjn)).1])
    (fun j _ _ => by rw [add_zero]; exact sum_primesIco_rpow_log_le_exp hϑ3 hσ0 _) hw
  have hsub : {ω | ∃ h ∈ Set.Icc (T / Real.exp 1) T,
        ω ∉ mesoGood Y ϑ prop5UpperSlope n ⌈a / 4⌉₊ a (fun j => β * Real.log j) (shiftLine σ h)}
      ⊆ {ω | ∃ h ∈ Set.Ico (T / Real.exp 1) (T / Real.exp 1 + T), ¬ ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ n →
          walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
            localLogAdd (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + σ) h))) (Y (p : ℕ) ω)) j ω
            ∈ Set.Icc (-a - prop5UpperSlope * (j : ℝ))
              (a + (j : ℝ) + (fun j => β * Real.log j) j)} := by
    rintro ω ⟨h, hh, hnot⟩
    refine ⟨h, ⟨hh.1, by linarith [hh.2, div_pos hT0 (Real.exp_pos 1)]⟩, ?_⟩
    rw [heightLine_eq_shiftLine]
    exact hnot
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) (le_trans hbar ?_)
  have hsum := sum_exp_neg_envelope_le_of hβ (r := ⌈a / 4⌉₊) (n := n) hr1
  have hC₂ := radIndexConst_pos Δ
  have h2 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc ⌈a / 4⌉₊ n, Real.exp (-(2 * (β * Real.log j))) :=
    Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
  have hfac : (0 : ℝ) ≤ radIndexConst Δ * T * Real.exp ϑ * Real.exp (-(2 * a)) := by positivity
  calc radIndexConst Δ * T * Real.exp ϑ * Real.exp (-(2 * a))
        * ∑ j ∈ Finset.Icc ⌈a / 4⌉₊ n, Real.exp (-(2 * (β * Real.log j)))
      ≤ radIndexConst Δ * T * Real.exp ϑ * Real.exp (-(2 * a))
          * ∑' i : ℕ, (i : ℝ) ^ (-(2 * β)) := mul_le_mul_of_nonneg_left hsum hfac
    _ = (radIndexConst Δ * ∑' i : ℕ, (i : ℝ) ^ (-(2 * β))) * (T * Real.exp ϑ)
          * Real.exp (-(2 * a)) := by ring

end RMF
