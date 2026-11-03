/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Conditional Jensen for `t ↦ t^q`

The reduction opens with `E|S_x|^{2q} = E[(|S_x|²)^q] ≤ E[(E[|S_x|² ∣ 𝓕_y])^q]`, which is
conditional Jensen for the concave `t ↦ t^q`, `0 ≤ q ≤ 1`.  This file specialises Mathlib's
general statement to that case, in the two forms the argument uses.

The general result is Mathlib's `ConcaveOn.condExp_map_le`, and `Real.concaveOn_rpow` supplies the
concavity, so no tangent-line argument is needed.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Conditional Jensen for `t ↦ t^q`**, `0 ≤ q ≤ 1`: `E[X^q ∣ m] ≤ (E[X ∣ m])^q` a.e., for
nonnegative integrable `X`.

Nonnegativity is genuinely needed, not a convenience: `t ↦ t^q` is concave on `[0,∞)` and
`Real.rpow` takes junk values to the left of `0`. -/
theorem condExp_rpow_le (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)] {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {X : Ω → ℝ} (hX : 0 ≤ᵐ[μ] X)
    (hint : Integrable X μ) (hint' : Integrable (fun ω => X ω ^ q) μ) :
    μ[fun ω => X ω ^ q | m] ≤ᵐ[μ] fun ω => μ[X | m] ω ^ q :=
  (Real.concaveOn_rpow hq0 hq1).condExp_map_le hm
    ((Real.continuous_rpow_const hq0).upperSemicontinuous.upperSemicontinuousOn _)
    (by filter_upwards [hX] with ω hω using Set.mem_Ici.2 hω) isClosed_Ici hint hint'

/-- The integrated form, which is what the reduction actually consumes: conditioning can only
increase the `q`-th moment of a nonnegative variable.

This is conditional Jensen followed by the tower property, so `X` may be replaced by anything
with the same conditional expectation — which is exactly how it is used, with `X = |S_x|²` and
`m = 𝓕_y`. -/
theorem integral_rpow_le_integral_condExp_rpow (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)] {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {X : Ω → ℝ} (hX : 0 ≤ᵐ[μ] X)
    (hint : Integrable X μ) (hint' : Integrable (fun ω => X ω ^ q) μ)
    (hcond : Integrable (fun ω => μ[X | m] ω ^ q) μ) :
    ∫ ω, X ω ^ q ∂μ ≤ ∫ ω, μ[X | m] ω ^ q ∂μ := by
  calc ∫ ω, X ω ^ q ∂μ = ∫ ω, μ[fun ω => X ω ^ q | m] ω ∂μ := (integral_condExp hm).symm
    _ ≤ ∫ ω, μ[X | m] ω ^ q ∂μ :=
        integral_mono_ae integrable_condExp hcond (condExp_rpow_le hm hq0 hq1 hX hint hint')

/-- **Conditional Jensen for `‖S‖^{2q}`, its side conditions discharged.**  For a measurable `S`
bounded almost surely and `0 ≤ q ≤ 1`, `E‖S‖^{2q} ≤ E[(E[‖S‖² ∣ m])^q]`:
`RMF.integral_rpow_le_integral_condExp_rpow` at `X = ‖S‖²`, the four integrability conditions
following from the bound.  The reductions of `RMF/Reduction/` and `RMF/Weighted/` open with this
step. -/
theorem integral_rpow_norm_le_integral_condExp_rpow [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)] {S : Ω → ℂ} (hS : Measurable S) {K : ℝ}
    (hK : ∀ᵐ ω ∂μ, ‖S ω‖ ≤ K) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ ω, ‖S ω‖ ^ (2 * q) ∂μ ≤ ∫ ω, (μ[fun ω => ‖S ω‖ ^ 2 | m] ω) ^ q ∂μ := by
  have hbdd : ∀ᵐ ω ∂μ, ‖S ω‖ ^ 2 ≤ K ^ 2 := by
    filter_upwards [hK] with ω hω
    exact pow_le_pow_left₀ (norm_nonneg _) hω 2
  have hnn : 0 ≤ᵐ[μ] fun ω => ‖S ω‖ ^ 2 :=
    Filter.Eventually.of_forall fun ω => by positivity
  have hW : Measurable fun ω => ‖S ω‖ ^ 2 := hS.norm.pow_const 2
  have hint2 : Integrable (fun ω => ‖S ω‖ ^ 2) μ := by
    refine (memLp_top_of_bound hW.aestronglyMeasurable (K ^ 2) ?_).integrable le_top
    filter_upwards [hbdd] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hω
  have hintq : Integrable (fun ω => (‖S ω‖ ^ 2) ^ q) μ := by
    refine (memLp_top_of_bound (hW.pow_const q).aestronglyMeasurable ((K ^ 2) ^ q) ?_).integrable
      le_top
    filter_upwards [hbdd] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) q)]
    exact Real.rpow_le_rpow (by positivity) hω hq0
  have hcnn : 0 ≤ᵐ[μ] μ[fun ω => ‖S ω‖ ^ 2 | m] := condExp_nonneg hnn
  have hcle : μ[fun ω => ‖S ω‖ ^ 2 | m] ≤ᵐ[μ] fun _ => K ^ 2 := by
    have h := condExp_mono (m := m) hint2 (integrable_const (K ^ 2)) hbdd
    rwa [condExp_const hm] at h
  have hintc : Integrable (fun ω => (μ[fun ω => ‖S ω‖ ^ 2 | m] ω) ^ q) μ := by
    have hm0 : Measurable (μ[fun ω => ‖S ω‖ ^ 2 | m]) :=
      (stronglyMeasurable_condExp.mono hm).measurable
    refine (memLp_top_of_bound (hm0.pow_const q).aestronglyMeasurable ((K ^ 2) ^ q)
      ?_).integrable le_top
    filter_upwards [hcnn, hcle] with ω h0 h1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 q)]
    exact Real.rpow_le_rpow h0 h1 hq0
  have hpow : ∀ ω : Ω, ‖S ω‖ ^ (2 * q) = (‖S ω‖ ^ 2) ^ q := by
    intro ω
    rw [← Real.rpow_natCast ‖S ω‖ 2, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  simp_rw [hpow]
  exact integral_rpow_le_integral_condExp_rpow hm hq0 hq1 hnn hint2 hintq hintc

/-- **Peeling one term off a `q`-th power**, `0 ≤ q ≤ 1`: for nonnegative `g` and `a ∈ A`,

`E[(∑_{m ∈ A} g_m)^q] ≤ E[g_a^q] + E[(∑_{m ∈ A∖{a}} g_m)^q]`,

by subadditivity of `t ↦ t^q`. -/
theorem integral_rpow_sum_le_add_integral_rpow_erase {g : ℕ → Ω → ℝ} {A : Finset ℕ} {a : ℕ}
    (ha : a ∈ A) (hg0 : ∀ n ω, 0 ≤ g n ω) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hint : Integrable (fun ω => (∑ n ∈ A, g n ω) ^ q) μ)
    (hint1 : Integrable (fun ω => g a ω ^ q) μ)
    (hint2 : Integrable (fun ω => (∑ n ∈ A.erase a, g n ω) ^ q) μ) :
    (∫ ω, (∑ n ∈ A, g n ω) ^ q ∂μ)
      ≤ (∫ ω, g a ω ^ q ∂μ) + ∫ ω, (∑ n ∈ A.erase a, g n ω) ^ q ∂μ := by
  calc ∫ ω, (∑ n ∈ A, g n ω) ^ q ∂μ
      ≤ ∫ ω, (g a ω ^ q + (∑ n ∈ A.erase a, g n ω) ^ q) ∂μ :=
        integral_mono hint (hint1.add hint2) fun ω => by
          dsimp only
          rw [← Finset.add_sum_erase _ _ ha]
          exact Real.rpow_add_le_add_rpow (hg0 a ω) (Finset.sum_nonneg fun n _ => hg0 n ω) hq0 hq1
    _ = (∫ ω, g a ω ^ q ∂μ) + ∫ ω, (∑ n ∈ A.erase a, g n ω) ^ q ∂μ := integral_add hint1 hint2

end RMF
