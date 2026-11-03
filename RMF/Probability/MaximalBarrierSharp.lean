/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.MaximalBarrierExplicit
import RMF.Probability.ChainingSharp

/-!
# Hamdan's Lemma 2.3 with a sharp constant

`RMF.IsSteinhausRMF.exists_const_measureReal_index_le_of_le` runs the chaining at `Λ = Δ + 40`,
where `Δ` bounds both the variance deficit `|a - τ|` and the excess of `∑ p^{-1} log p` over
`e^{τ+ϑ}`, and pays `e^Δ`.  Only the first needs to be small, and neither needs to enter the
chaining: here

* the deficit `Δ₁` (in `|a - τ| ≤ Δ₁`) and the excess `Δ₂` are separate, and only `e^{Δ₁}` is paid;
* the chaining runs at `V ≤ 7a` (the upper event `A + τ + b ≤ 6τ`, and the lower one at the
  threshold `4τ`, which suffices by `RMF.barrier_lower_exponent_le_four`) and `rP ≤ 2/K`, on a
  partition of `[0,1)` refined by `K = RMF.indexSharpRefine`;
* the primes start at `⌊blockScale ϑ 0⌋₊ + 1`, which must pass `RMF.chainSharpThreshold (1/2) 7`;
* the index only has to pass the level `RMF.indexSharpLevel Δ₁ Δ₂ = max{8Δ₁, Δ₂}`, not the
  constant: `RMF.IsSteinhausRMF.exists_const_measureReal_index_le_of_le` asks for `j ≥ C` only so
  that one number serves as both.

The constant is `RMF.indexSharpConst Δ₁ = 4K·chainSharpConst 7 (2/K)·e^{Δ₁}`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-- The refinement `K` of the partition of `[0,1)` in the sharp Lemma 2.3. -/
noncomputable def indexSharpRefine : ℝ := 10000

/-- **The level of the sharp Lemma 2.3** at deficit `Δ₁` and excess `Δ₂`: `max{8Δ₁, Δ₂}`. -/
noncomputable def indexSharpLevel (Δ₁ Δ₂ : ℝ) : ℝ := max (8 * Δ₁) Δ₂

/-- **The constant of the sharp Lemma 2.3** at deficit `Δ₁`: `4K·chainSharpConst 7 (2/K)·e^{Δ₁}`,
`K = indexSharpRefine`. -/
noncomputable def indexSharpConst (Δ₁ : ℝ) : ℝ :=
  4 * indexSharpRefine * chainSharpConst 7 (2 / indexSharpRefine) * Real.exp Δ₁

lemma indexSharpConst_pos (Δ₁ : ℝ) : 0 < indexSharpConst Δ₁ := by
  have hK0 : (0 : ℝ) < indexSharpRefine := by
    rw [show indexSharpRefine = 10000 from rfl]
    norm_num
  have hΛ₂ : (0 : ℝ) < 2 / indexSharpRefine := by positivity
  have := chainSharpConst_pos (Λ₁ := 7) hΛ₂
  rw [indexSharpConst]
  positivity

/-- **Below the barrier, at the threshold `4τ`**: `(4τ)²/a ≥ τ + 2A + 2b`. -/
lemma barrier_lower_exponent_le_four {τ A b a C₀ : ℝ} (hC₀ : 1 ≤ C₀) (hτ : 8 * C₀ ≤ τ)
    (hA : A ≤ 4 * τ) (hb : b ≤ τ) (hle : a ≤ τ + C₀) (hge : τ - C₀ ≤ a) :
    τ + 2 * A + 2 * b ≤ (4 * τ) ^ 2 / a := by
  have hτ0 : (0 : ℝ) < τ := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  have haup : a ≤ 9 * τ / 8 := by linarith
  have hlhs : τ + 2 * A + 2 * b ≤ 11 * τ := by linarith
  rw [le_div_iff₀ hapos]
  calc (τ + 2 * A + 2 * b) * a ≤ 11 * τ * (9 * τ / 8) :=
        mul_le_mul hlhs haup hapos.le (by linarith)
    _ ≤ (4 * τ) ^ 2 := by nlinarith [sq_nonneg τ]

/-- **Hamdan's Lemma 2.3 at one index, sharp.**  For `|a - j| ≤ Δ₁`, `∑_p p^{-1-2δ} log p ≤
e^{j+ϑ} + Δ₂`, `A ≤ 4j`, `b ≤ j`, `j ≥ indexSharpLevel Δ₁ Δ₂` and primes from
`⌊blockScale ϑ 0⌋₊ + 1 ≥ chainSharpThreshold (1/2) 7`:

`P(∃h ∈ [0,1) : log‖F(1/2+δ+ih)‖ ∉ [-A - cj, A + j + b])`
`≤ indexSharpConst Δ₁ · e^ϑ e^{-2A} e^{-2b}`. -/
theorem IsSteinhausRMF.measureReal_index_le_of_le_sharp {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ)
    {Δ₁ Δ₂ ϑ A b c δ : ℝ} {j : ℕ} (hΔ₁ : 1 ≤ Δ₁) (hϑ : 1 ≤ ϑ)
    (hϑ₀ : chainSharpThreshold (1 / 2) 7 ≤ ((⌊blockScale ϑ 0⌋₊ + 1 : ℕ) : ℝ))
    (hA0 : 0 ≤ A) (hb0 : 0 ≤ b) (hc : 20 ≤ c) (hδ0 : 0 ≤ δ)
    (hupA : (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ₁)
    (hlowA : (j : ℝ) - Δ₁ ≤ ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)))
    (hP : (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Real.exp ((j : ℝ) + ϑ) + Δ₂)
    (hτC : indexSharpLevel Δ₁ Δ₂ ≤ (j : ℝ)) (hA : A ≤ 4 * (j : ℝ)) (hb : b ≤ (j : ℝ)) :
    μ.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
        Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
            (heightLine (1 / 2 + δ) h) ω‖
          ∉ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b)}
      ≤ indexSharpConst Δ₁ * Real.exp ϑ * Real.exp (-(2 * A)) * Real.exp (-(2 * b)) := by
  have hK : indexSharpRefine = 10000 := rfl
  have hK0 : (0 : ℝ) < indexSharpRefine := by rw [hK]; norm_num
  have hK1 : (1 : ℝ) ≤ indexSharpRefine := by rw [hK]; norm_num
  have hΛ₂ : (0 : ℝ) < 2 / indexSharpRefine := by positivity
  have hΛ₂288 : 288 * (2 / indexSharpRefine) ≤ 1 := by rw [hK]; norm_num
  have hCs := chainSharpConst_pos (Λ₁ := 7) hΛ₂
  set Cs := chainSharpConst 7 (2 / indexSharpRefine) with hCs_expl
  set K := indexSharpRefine with hK_expl
  have hδσ : (1 : ℝ) / 2 ≤ 1 / 2 + δ := by linarith
  have hσ₀ : (1 : ℝ) / 3 < 1 / 2 := by norm_num
  haveI := hf.isProbabilityMeasure
  set τ := (j : ℝ) with hτdef
  have hτ8 : 8 * Δ₁ ≤ τ := le_trans (le_max_left _ _) hτC
  have hτΔ₂ : Δ₂ ≤ τ := le_trans (le_max_right _ _) hτC
  have hτ0 : (0 : ℝ) < τ := by linarith
  set a := ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
    (p : ℝ) ^ (-2 * (1 / 2 + δ)) with hadef
  clear_value τ a
  have hale : a ≤ τ + Δ₁ := by linarith
  have hage : τ - Δ₁ ≤ a := by linarith
  have ha1 : (1 : ℝ) ≤ a := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  -- the partition of `[0,1)` into intervals of width `(K e^{τ+ϑ})⁻¹`
  obtain ⟨Eτ, hEτdef⟩ : ∃ Eτ : ℝ, Eτ = Real.exp (τ + ϑ) := ⟨_, rfl⟩
  have hEτ0 : (0 : ℝ) < Eτ := by rw [hEτdef]; exact Real.exp_pos _
  have hEτ1 : (1 : ℝ) ≤ Eτ := by rw [hEτdef]; exact Real.one_le_exp (by linarith)
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
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈K * Eτ⌉₊ := ⟨_, rfl⟩
  have hNge : K * Eτ ≤ (N : ℝ) := by rw [hNdef]; exact Nat.le_ceil _
  have hNle : (N : ℝ) ≤ 2 * (K * Eτ) := by
    rw [hNdef]
    have hce := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ K * Eτ)
    have hone : (1 : ℝ) ≤ K * Eτ := by nlinarith
    linarith
  have hNρ : (1 : ℝ) ≤ (N : ℝ) * ρ := by
    have h := mul_le_mul_of_nonneg_right hNge hρ0.le
    linarith
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
  have h78 : 7 * τ / 8 ≤ a := by linarith
  have hVΛ : A + τ + b ≤ 7 * a := by linarith
  have hWΛ : 4 * τ ≤ 7 * a := by linarith
  have hV0 : (0 : ℝ) ≤ A + τ + b := by linarith
  have hW0 : (0 : ℝ) ≤ 4 * τ := by linarith
  have ha1' : (1 : ℝ) ≤ ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ)) := hadef ▸ ha1
  have hVΛ' : A + τ + b ≤ 7 * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ))) := hadef ▸ hVΛ
  have hWΛ' : 4 * τ ≤ 7 * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ))) := hadef ▸ hWΛ
  -- the two Gaussian exponents, against the entropy of the partition
  have hexpU : Eτ * Real.exp (-((A + τ + b) ^ 2 / a))
      ≤ Real.exp ϑ * (Real.exp Δ₁ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))) := by
    have hkey := barrier_upper_exponent_le (τ := τ) (A := A) (b := b) (a := a) (C₀ := Δ₁)
      hapos hale (by linarith)
    rw [hEτdef, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hexpL : Eτ * Real.exp (-((4 * τ) ^ 2 / a))
      ≤ Real.exp ϑ * (Real.exp Δ₁ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))) := by
    have hkey := barrier_lower_exponent_le_four (τ := τ) (A := A) (b := b) (a := a) (C₀ := Δ₁)
      hΔ₁ hτ8 hA hb hale hage
    rw [hEτdef, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  -- the two families of events, one per interval
  obtain ⟨Eup, hEup⟩ : ∃ E : ℕ → Set Ω, E = fun k : ℕ =>
      {ω | ∃ h ∈ Set.Ico ((k : ℝ) * ρ) ((k : ℝ) * ρ + ρ),
        A + τ + b < Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1)
          (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖} := ⟨_, rfl⟩
  obtain ⟨Elo, hElo⟩ : ∃ E : ℕ → Set Ω, E = fun k : ℕ =>
      {ω | ∃ h ∈ Set.Ico ((k : ℝ) * ρ) ((k : ℝ) * ρ + ρ),
        4 * τ + 4 * a < -Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1)
          (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖} := ⟨_, rfl⟩
  have hboundU : μ.real (⋃ k ∈ Finset.range N, Eup k)
      ≤ (N : ℝ) * (Cs * Real.exp (-((A + τ + b) ^ 2 / a))) := by
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    have hterm : ∀ k ∈ Finset.range N,
        μ.real (Eup k) ≤ Cs * Real.exp (-((A + τ + b) ^ 2 / a)) := by
      intro k _
      have h := hf.measure_exists_gt_le_shift_sharp hσ₀ (by norm_num : (1 : ℝ) ≤ 7) hΛ₂ hΛ₂288
        (h₀ := (k : ℝ) * ρ) hϑ₀ (⌊blockScale ϑ j⌋₊ + 1) hδσ hρ0 hV0 ha1' hVΛ' hrP
      rw [← hadef] at h
      simp only [hEup]
      exact h
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hboundL : μ.real (⋃ k ∈ Finset.range N, Elo k)
      ≤ (N : ℝ) * (Cs * Real.exp (-((4 * τ) ^ 2 / a))) := by
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    have hterm : ∀ k ∈ Finset.range N,
        μ.real (Elo k) ≤ Cs * Real.exp (-((4 * τ) ^ 2 / a)) := by
      intro k _
      have h := hf.measure_exists_lt_le_sharp hσ₀ (by norm_num : (1 : ℝ) ≤ 7) hΛ₂ hΛ₂288
        (h₀ := (k : ℝ) * ρ) hϑ₀ (⌊blockScale ϑ j⌋₊ + 1) hδσ hρ0 hW0 ha1' hWΛ' hrP
      rw [← hadef] at h
      simp only [hElo]
      exact h
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the failure at this index is covered by the two families
  have hsub : {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
      Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
          (heightLine (1 / 2 + δ) h) ω‖
        ∉ Set.Icc (-A - c * τ) (A + τ + b)}
      ⊆ (⋃ k ∈ Finset.range N, Eup k) ∪ (⋃ k ∈ Finset.range N, Elo k) := by
    rintro ω ⟨h, hh, hnot⟩
    obtain ⟨k, hkN, hk⟩ := exists_lt_mem_Ico hρ0 hh.1 hh.2 hNρ
    simp only [Set.mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with hlt | hgt
    · refine Or.inr (Set.mem_biUnion (Finset.mem_range.2 hkN) ?_)
      simp only [hElo]
      have hct : 20 * τ ≤ c * τ := mul_le_mul_of_nonneg_right hc hτ0.le
      exact ⟨h, hk, by linarith⟩
    · refine Or.inl (Set.mem_biUnion (Finset.mem_range.2 hkN) ?_)
      simp only [hEup]
      exact ⟨h, hk, hgt⟩
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_union_le _ _) ?_
  have hR : 0 ≤ Real.exp ϑ * (Real.exp Δ₁ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))) := by
    positivity
  have hU : (N : ℝ) * (Cs * Real.exp (-((A + τ + b) ^ 2 / a)))
      ≤ 2 * K * Cs * (Real.exp ϑ * (Real.exp Δ₁
        * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))) := by
    have h1 : (N : ℝ) * Real.exp (-((A + τ + b) ^ 2 / a))
        ≤ 2 * K * (Eτ * Real.exp (-((A + τ + b) ^ 2 / a))) := by
      have h := mul_le_mul_of_nonneg_right hNle (Real.exp_pos (-((A + τ + b) ^ 2 / a))).le
      linarith
    have h2 := mul_le_mul_of_nonneg_left hexpU (by positivity : (0 : ℝ) ≤ 2 * K)
    calc (N : ℝ) * (Cs * Real.exp (-((A + τ + b) ^ 2 / a)))
        = Cs * ((N : ℝ) * Real.exp (-((A + τ + b) ^ 2 / a))) := by ring
      _ ≤ Cs * (2 * K * (Eτ * Real.exp (-((A + τ + b) ^ 2 / a)))) :=
          mul_le_mul_of_nonneg_left h1 hCs.le
      _ ≤ Cs * (2 * K * (Real.exp ϑ * (Real.exp Δ₁
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))))) :=
          mul_le_mul_of_nonneg_left h2 hCs.le
      _ = 2 * K * Cs * (Real.exp ϑ * (Real.exp Δ₁
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))) := by ring
  have hL : (N : ℝ) * (Cs * Real.exp (-((4 * τ) ^ 2 / a)))
      ≤ 2 * K * Cs * (Real.exp ϑ * (Real.exp Δ₁
        * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))) := by
    have h1 : (N : ℝ) * Real.exp (-((4 * τ) ^ 2 / a))
        ≤ 2 * K * (Eτ * Real.exp (-((4 * τ) ^ 2 / a))) := by
      have h := mul_le_mul_of_nonneg_right hNle (Real.exp_pos (-((4 * τ) ^ 2 / a))).le
      linarith
    have h2 := mul_le_mul_of_nonneg_left hexpL (by positivity : (0 : ℝ) ≤ 2 * K)
    calc (N : ℝ) * (Cs * Real.exp (-((4 * τ) ^ 2 / a)))
        = Cs * ((N : ℝ) * Real.exp (-((4 * τ) ^ 2 / a))) := by ring
      _ ≤ Cs * (2 * K * (Eτ * Real.exp (-((4 * τ) ^ 2 / a)))) :=
          mul_le_mul_of_nonneg_left h1 hCs.le
      _ ≤ Cs * (2 * K * (Real.exp ϑ * (Real.exp Δ₁
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))))) :=
          mul_le_mul_of_nonneg_left h2 hCs.le
      _ = 2 * K * Cs * (Real.exp ϑ * (Real.exp Δ₁
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))) := by ring
  have hmax : 4 * K * Cs * Real.exp Δ₁ ≤ indexSharpConst Δ₁ := le_of_eq rfl
  have hpos : (0 : ℝ) < Real.exp ϑ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))) := by
    positivity
  have hlast := mul_le_mul_of_nonneg_right hmax hpos.le
  have heq : 2 * K * Cs * (Real.exp ϑ * (Real.exp Δ₁
        * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))))
      + 2 * K * Cs * (Real.exp ϑ * (Real.exp Δ₁
        * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))))
      = 4 * K * Cs * Real.exp Δ₁ * (Real.exp ϑ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))) := by
    ring
  have heq2 : indexSharpConst Δ₁ * (Real.exp ϑ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))
      = indexSharpConst Δ₁ * Real.exp ϑ * Real.exp (-(2 * A)) * Real.exp (-(2 * b)) := by ring
  linarith [hboundU, hboundL, hU, hL, hlast]

/-- **Hamdan's Lemma 2.3, sharp**: the barrier over the indices `r ≤ j ≤ n`, at
`RMF.indexSharpConst Δ₁`, from the level `r ≥ RMF.indexSharpLevel Δ₁ Δ₂`. -/
theorem IsSteinhausRMF.measure_exists_barrier_le_of_le_sharp {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ)
    {Δ₁ Δ₂ ϑ A c δ : ℝ} {r n : ℕ} {b : ℕ → ℝ} (hΔ₁ : 1 ≤ Δ₁) (hϑ : 1 ≤ ϑ)
    (hϑ₀ : chainSharpThreshold (1 / 2) 7 ≤ ((⌊blockScale ϑ 0⌋₊ + 1 : ℕ) : ℝ))
    (hA0 : 0 ≤ A) (hc : 20 ≤ c) (hδ0 : 0 ≤ δ) (hCr : indexSharpLevel Δ₁ Δ₂ ≤ (r : ℝ))
    (hb0 : ∀ j, r ≤ j → j ≤ n → 0 ≤ b j)
    (hble : ∀ j, r ≤ j → j ≤ n → b j ≤ (j : ℝ))
    (h4 : ∀ j, r ≤ j → j ≤ n → A ≤ 4 * (j : ℝ))
    (hup : ∀ j, r ≤ j → j ≤ n →
      (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ₁)
    (hlow : ∀ j, r ≤ j → j ≤ n → (j : ℝ) - Δ₁ ≤
      ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)))
    (hlogP : ∀ j, r ≤ j → j ≤ n →
      (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Real.exp ((j : ℝ) + ϑ) + Δ₂) :
    μ.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
        Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
            (heightLine (1 / 2 + δ) h) ω‖
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      ≤ indexSharpConst Δ₁ * Real.exp ϑ * Real.exp (-(2 * A))
        * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) := by
  haveI := hf.isProbabilityMeasure
  obtain ⟨E, hE⟩ : ∃ E : ℕ → Set Ω, E = fun j : ℕ =>
      {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
        Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
            (heightLine (1 / 2 + δ) h) ω‖
          ∉ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)} := ⟨_, rfl⟩
  have hsub : {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
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
        indexSharpConst Δ₁ * Real.exp ϑ * Real.exp (-(2 * A)) * Real.exp (-(2 * b j))
      = indexSharpConst Δ₁ * Real.exp ϑ * Real.exp (-(2 * A))
        * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) := by
    rw [Finset.mul_sum]
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun j hj => ?_) (le_of_eq hlast)
  obtain ⟨hjr, hjn⟩ := Finset.mem_Icc.1 hj
  have hjR : (r : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjr
  simp only [hE]
  exact hf.measureReal_index_le_of_le_sharp hΔ₁ hϑ hϑ₀ hA0 (hb0 j hjr hjn) hc hδ0
    (hup j hjr hjn) (hlow j hjr hjn) (hlogP j hjr hjn) (by linarith) (h4 j hjr hjn)
    (hble j hjr hjn)

/-- **Hamdan's Lemma 2.3, sharp, for the walk**:
`RMF.IsSteinhausRMF.measure_exists_barrier_le_of_le_sharp` restated for `RMF.walk` over the block
sums, as the good set of the chaos moments uses it. -/
theorem IsSteinhausPrimeValues.measure_exists_barrier_le_of_le_sharp {Ω : Type*}
    [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsSteinhausPrimeValues X μ)
    {Δ₁ Δ₂ ϑ A c δ : ℝ} {r n : ℕ} {b : ℕ → ℝ} (hΔ₁ : 1 ≤ Δ₁) (hϑ : 1 ≤ ϑ)
    (hϑ₀ : chainSharpThreshold (1 / 2) 7 ≤ ((⌊blockScale ϑ 0⌋₊ + 1 : ℕ) : ℝ))
    (hA0 : 0 ≤ A) (hc : 20 ≤ c) (hδ0 : 0 ≤ δ) (hCr : indexSharpLevel Δ₁ Δ₂ ≤ (r : ℝ))
    (hb0 : ∀ j, r ≤ j → j ≤ n → 0 ≤ b j)
    (hble : ∀ j, r ≤ j → j ≤ n → b j ≤ (j : ℝ))
    (h4 : ∀ j, r ≤ j → j ≤ n → A ≤ 4 * (j : ℝ))
    (hup : ∀ j, r ≤ j → j ≤ n →
      (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ₁)
    (hlow : ∀ j, r ≤ j → j ≤ n → (j : ℝ) - Δ₁ ≤
      ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)))
    (hlogP : ∀ j, r ≤ j → j ≤ n →
      (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Real.exp ((j : ℝ) + ϑ) + Δ₂) :
    μ.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
        walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLog (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      ≤ indexSharpConst Δ₁ * Real.exp ϑ * Real.exp (-(2 * A))
        * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) := by
  haveI := hX.isProbabilityMeasure
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ := hX.isSteinhausRMF
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G =
      {ω | ∀ p ∈ Nat.primesBelow (⌊blockScale ϑ n⌋₊ + 1), ‖X p ω‖ ≤ 1} := ⟨_, rfl⟩
  have hGnull : μ Gᶜ = 0 := by
    have h := ae_forall_norm_le_one hX norm_le_one_steinhausLaw (⌊blockScale ϑ n⌋₊ + 1)
    rw [ae_iff] at h
    rw [hGdef, Set.compl_setOf]
    exact h
  have hwalk : ∀ ω ∈ G, ∀ (h : ℝ) (j : ℕ), j ≤ n →
      walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLog (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
        = Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω)
              (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖ := by
    intro ω hωG h j hjn
    rw [hGdef] at hωG
    have hjm : ⌊blockScale ϑ j⌋₊ ≤ ⌊blockScale ϑ n⌋₊ :=
      Nat.floor_le_floor (blockScale_mono ϑ hjn)
    have hsub : ∀ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        ‖X p ω‖ ≤ 1 := by
      intro p hp
      obtain ⟨hpp, -, hp2⟩ := mem_primesIco.1 hp
      exact hωG p (Nat.mem_primesBelow.2 ⟨by omega, hpp⟩)
    rw [walk_blockSum_eq_sum_primesIco ϑ
      (fun m => (m : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) j ω]
    exact (log_norm_randomEulerProductIco_eq (by rw [re_heightLine]; linarith) hsub).symm
  have hset : G ∩ {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
        walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLog (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      = G ∩ {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
        Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω)
              (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)} := by
    ext ω
    constructor
    · rintro ⟨hωG, h, hh, hnot⟩
      exact ⟨hωG, h, hh, fun hall => hnot fun j hjr hjn => by
        rw [hwalk ω hωG h j hjn]; exact hall j hjr hjn⟩
    · rintro ⟨hωG, h, hh, hnot⟩
      exact ⟨hωG, h, hh, fun hall => hnot fun j hjr hjn => by
        rw [← hwalk ω hωG h j hjn]; exact hall j hjr hjn⟩
  calc μ.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
        walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLog (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      = μ.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
          Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω)
              (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖
            ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)} := by
        unfold MeasureTheory.Measure.real
        rw [measure_eq_measure_inter_of_compl_null hGnull _, hset,
          ← measure_eq_measure_inter_of_compl_null hGnull _]
    _ ≤ indexSharpConst Δ₁ * Real.exp ϑ * Real.exp (-(2 * A))
          * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) :=
        hf.measure_exists_barrier_le_of_le_sharp hΔ₁ hϑ hϑ₀ hA0 hc hδ0 hCr hb0 hble h4 hup hlow
          hlogP

end RMF
