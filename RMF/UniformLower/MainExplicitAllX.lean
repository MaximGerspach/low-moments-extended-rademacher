/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.FinalRegimesLow
import RMF.UniformLower.SmallXExplicit

/-!
# The low moments of the weighted Rademacher sum, uniformly in `q`, explicit, for every `x ≥ 3`

`RMF.weighted_rademacher_moments_lower_uniform_explicit` with `3 ≤ x` in place of
`x ≥ exp(exp 2100)`, `c = 10⁻¹⁰` in all three cases
(`RMF.weighted_rademacher_moments_lower_uniform_explicit_every_x`).  Below `½`
(`RMF.le_integral_rpow_belowHalf_of_three_le`): the elementary bound for `log log x ≤ 67.17`
(`RMF.le_integral_rpow_weightedRademacherSum_small_explicit`), the low range for
`67.17 < log log x ≤ 2100` (`RMF.le_integral_rpow_belowHalfLow`), and the first conjunct of
`RMF.weighted_rademacher_moments_lower_uniform_explicit` above; at and above `½` the bounds for
every `x ≥ 3` of `RMF/UniformLower/LowerAllX.lean`.  With
`RMF.weighted_rademacher_moments_upper_uniform_explicit` (`C = 25`, every `x ≥ 3`), the two-sided
`RMF.weighted_rademacher_moments_asymp_uniform_explicit_every_x`.
-/

open MeasureTheory

namespace RMF

/-- **Below `½` with `c = 10⁻¹⁰`, for every `x ≥ 3`**: for every Rademacher `X`, `x ≥ 3` and
`0 < q < ½`, `10⁻¹⁰min{log log x, 1/(1-2q)}(log log x)^{-q/2} ≤ E|S(x)|^{2q}`: the elementary
bound for `log log x ≤ 67.17`, the low range up to `2100`, and
`RMF.weighted_rademacher_moments_lower_uniform_explicit` from `x ≥ exp(exp 2100)`. -/
theorem le_integral_rpow_belowHalf_of_three_le {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 3 ≤ x)
    (hq0 : 0 < q) (hq : q < 1 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  have hx1 : 1 < x := by linarith
  rcases le_or_gt (Real.log (Real.log x)) 67.17 with h1 | h1
  · exact le_integral_rpow_weightedRademacherSum_small_explicit hX hx h1 hq0 hq
  rcases le_or_gt (Real.log (Real.log x)) 2100 with h2 | h2
  · exact le_integral_rpow_belowHalfLow hX (exp_exp_le_of_le_loglog hx1 h1.le) h2 hq0 hq
  · exact (weighted_rademacher_moments_lower_uniform_explicit Ω X μ hX x
      (exp_exp_le_of_le_loglog hx1 h2.le)).1 q hq0 hq

/-- **Lower bounds for the low moments of the weighted Rademacher sum, uniformly in `q`, with
`c = 10⁻¹⁰`, for every `x ≥ 3`.**  For every Rademacher function `X` on any probability space and
every `x ≥ 3`, with `S(x) = ∑_{n≤x} X(n)/√n`,

* `10⁻¹⁰·min{log log x, 1/(1-2q)}·(log log x)^{-q/2} ≤ E|S(x)|^{2q}` for `0 < q < ½`,
* `10⁻¹⁰·(log log x)^{3/4} ≤ E|S(x)|`,
* `10⁻¹⁰·(log x)^{q(2q-1)}·min{1/(2q-1), log log x}^{3/4} ≤ E|S(x)|^{2q}` for `½ < q ≤ 1`. -/
theorem weighted_rademacher_moments_lower_uniform_explicit_every_x :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
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
  have hΛ0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg (one_le_log_of_three_le hx)
  refine ⟨fun q hq0 hq2 => le_integral_rpow_belowHalf_of_three_le hX hx hq0 hq2, ?_,
    fun q hq2 hq1 => integral_rpow_weightedRademacherSum_ge_aboveHalf_explicit hX hx hq2 hq1⟩
  exact le_trans (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hΛ0 _))
    (integral_norm_weightedRademacherSum_ge_half_explicit hX hx)

/-- **The low moments of the weighted Rademacher sum, uniformly in `q`, with `c = 10⁻¹⁰` and
`C = 25`, for every `x ≥ 3`.**  For every Rademacher function `X` on any probability space and
every `x ≥ 3`, with `S(x) = ∑_{n≤x} X(n)/√n` and `Λ = log log x`,

* `10⁻¹⁰·G ≤ E|S(x)|^{2q} ≤ 25·G`, `G = min{Λ, 1/(1-2q)}·Λ^{-q/2}`, for `0 < q < ½`,
* `10⁻¹⁰·Λ^{3/4} ≤ E|S(x)| ≤ 25·Λ^{3/4}`,
* `10⁻¹⁰·G ≤ E|S(x)|^{2q} ≤ 25·G`, `G = (log x)^{q(2q-1)}·min{1/(2q-1), Λ}^{3/4}`, for
  `½ < q ≤ 1`.

`RMF.weighted_rademacher_moments_lower_uniform_explicit_every_x` and
`RMF.weighted_rademacher_moments_upper_uniform_explicit`. -/
theorem weighted_rademacher_moments_asymp_uniform_explicit_every_x :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        (∀ q : ℝ, 0 < q → q < 1 / 2 →
          1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
              * Real.log (Real.log x) ^ (-(q / 2)))
              ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
            ∧ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
              ≤ 25 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
                * Real.log (Real.log x) ^ (-(q / 2)))) ∧
        (1 / 10 ^ 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ)
            ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ
          ∧ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ
            ≤ 25 * Real.log (Real.log x) ^ (3 / 4 : ℝ)) ∧
        (∀ q : ℝ, 1 / 2 < q → q ≤ 1 →
          1 / 10 ^ 10 * (Real.log x ^ (q * (2 * q - 1))
              * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
              ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
            ∧ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
              ≤ 25 * (Real.log x ^ (q * (2 * q - 1))
                * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))) := by
  intro Ω _ X μ hX x hx
  obtain ⟨l1, l2, l3⟩ := weighted_rademacher_moments_lower_uniform_explicit_every_x Ω X μ hX x hx
  obtain ⟨u1, u2, u3⟩ := weighted_rademacher_moments_upper_uniform_explicit Ω X μ hX x hx
  exact ⟨fun q hq0 hq2 => ⟨l1 q hq0 hq2, u1 q hq0 hq2⟩, ⟨l2, u2⟩,
    fun q hq2 hq1 => ⟨l3 q hq2 hq1, u3 q hq2 hq1⟩⟩

end RMF
