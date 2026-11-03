/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.FinalRegimesMid
import RMF.Weighted.UniformMomentsExplicit

/-!
# The low moments of the weighted Rademacher sum, uniformly in `q`, explicit

The lower bounds for the low moments, uniformly in `q`, with `c = 10⁻¹⁰` for every
`x ≥ x₀ = exp(exp 2100)` (`RMF.weighted_rademacher_moments_lower_uniform_explicit`).  Below `½`,
for `log log x ≥ 6000` the regimes of `RMF/UniformLower/FinalRegimes.lean` (the floor for
`q log log x ≤ 37/2`, else B1 for `q ≤ 9/20` and B2 above), for `log log x < 6000` those of
`RMF/UniformLower/FinalRegimesMid.lean` (`RMF.le_integral_rpow_belowHalfMid`); at and above `½`
the bounds for every `x ≥ 3` of `RMF/UniformLower/LowerAllX.lean`.  The version for every
`x ≥ 3`, and the two-sided bounds with `RMF.weighted_rademacher_moments_upper_uniform_explicit`
(`C = 25`), are in `RMF/UniformLower/MainExplicitAllX.lean`.
-/

open MeasureTheory

namespace RMF

/-- **Lower bounds for the low moments of the weighted Rademacher sum, uniformly in `q`, with
`c = 10⁻¹⁰`.**  For every Rademacher function `X` on any probability space and every
`x ≥ x₀ = exp(exp 2100)`, with `S(x) = ∑_{n≤x} X(n)/√n`,

* `10⁻¹⁰·min{log log x, 1/(1-2q)}·(log log x)^{-q/2} ≤ E|S(x)|^{2q}` for `0 < q < ½`,
* `10⁻¹⁰·(log log x)^{3/4} ≤ E|S(x)|`,
* `10⁻¹⁰·(log x)^{q(2q-1)}·min{1/(2q-1), log log x}^{3/4} ≤ E|S(x)|^{2q}` for `½ < q ≤ 1`. -/
theorem weighted_rademacher_moments_lower_uniform_explicit :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, Real.exp (Real.exp 2100) ≤ x →
        (∀ q : ℝ, 0 < q → q < 1 / 2 →
          1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
              * Real.log (Real.log x) ^ (-(q / 2)))
            ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                ^ (2 * q) ∂μ) ∧
        1 / 10 ^ 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ)
          ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ ∧
        (∀ q : ℝ, 1 / 2 < q → q ≤ 1 →
          1 / 10 ^ 10 * (Real.log x ^ (q * (2 * q - 1))
              * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
            ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                ^ (2 * q) ∂μ) := by
  intro Ω _ X μ hX x hx
  obtain ⟨hΛ, -, -, h405⟩ := loglog_facts_of_2100 hx
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.2 (Real.exp_pos _)) hx
  have hx3 : 3 ≤ x := by
    have := Real.add_one_le_exp (405 : ℝ)
    linarith
  refine ⟨fun q hq0 hq2 => ?_, ?_,
    fun q hq2 hq1 => integral_rpow_weightedRademacherSum_ge_aboveHalf_explicit hX hx3 hq2 hq1⟩
  · rcases le_or_gt 6000 (Real.log (Real.log x)) with h6 | h6
    · have hx6 := exp_exp_le_of_le_loglog hx1 h6
      rcases le_or_gt (q * Real.log (Real.log x)) (37 / 2) with h | h
      · exact le_integral_rpow_floorRegime hX hx6 hq0 h
      · rcases le_or_gt q (9 / 20) with h' | h'
        · exact le_integral_rpow_mainB1Regime hX hx6 hq0 h' h
        · exact le_integral_rpow_mainB2Regime hX hx6 h'.le hq2
    · exact le_integral_rpow_belowHalfMid hX hx h6.le hq0 hq2
  · have hΛ34 : 0 ≤ Real.log (Real.log x) ^ (3 / 4 : ℝ) :=
      Real.rpow_nonneg (le_trans (by norm_num) hΛ) _
    exact le_trans (mul_le_mul_of_nonneg_right (by norm_num) hΛ34)
      (integral_norm_weightedRademacherSum_ge_half_explicit hX hx3)

end RMF
