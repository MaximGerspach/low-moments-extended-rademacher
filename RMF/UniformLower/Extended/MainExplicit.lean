/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.Extended.AboveHalf
import RMF.UniformLower.Extended.SmallX
import RMF.UniformLower.Extended.RegimesHigh

/-!
# The extended sum's low moments, uniformly in `q`, explicit, for every `x ≥ 3`

For `Y(x) = x^{-1/2}∑_{n≤x} X^e(n)`
(`normalisedSum (fun ω => compMultExtension fun p => X p ω) x`), the three cases of
`RMF.weighted_rademacher_moments_lower_uniform_explicit_every_x` with `c = 10⁻¹⁰` for every
`x ≥ 3` (`RMF.extended_rademacher_moments_lower_uniform_explicit_every_x`).  Below `½`
(`RMF.le_integral_rpow_belowHalf_of_three_le_ext`): E1 for `log log x ≤ 67.17`
(`RMF.le_integral_rpow_normalisedSum_compMultExtension_small_explicit`) and the regimes from
`67.17` on (`RMF.le_integral_rpow_normalisedSum_compMultExtension_large_explicit`); at and above
`½` the bounds of `RMF/UniformLower/Extended/AboveHalf.lean`.  With
`RMF.extended_rademacher_moments_upper_uniform_explicit` (`C = 30`, every `x ≥ 3`), the two-sided
`RMF.extended_rademacher_moments_asymp_uniform_explicit_every_x`.  The statements are those of
`RMF/UniformLower/MainExplicitAllX.lean` with `Y` for `S` and `30` for `25`.
-/

open MeasureTheory

namespace RMF

/-- **Below `½` for `Y` with `c = 10⁻¹⁰`, for every `x ≥ 3`**: for every Rademacher `X`, `x ≥ 3`
and `0 < q < ½`, `10⁻¹⁰min{log log x, 1/(1-2q)}(log log x)^{-q/2} ≤ E|Y(x)|^{2q}`: E1 for
`log log x ≤ 67.17` and the low, mid and high ranges from `67.17` on
(`RMF.le_integral_rpow_belowHalf_of_three_le` for `Y`). -/
theorem le_integral_rpow_belowHalf_of_three_le_ext {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 3 ≤ x)
    (hq0 : 0 < q) (hq : q < 1 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  have hx1 : 1 < x := by linarith
  rcases le_or_gt (Real.log (Real.log x)) 67.17 with h1 | h1
  · exact le_integral_rpow_normalisedSum_compMultExtension_small_explicit hX hx h1 hq0 hq
  · exact le_integral_rpow_normalisedSum_compMultExtension_large_explicit hX
      (exp_exp_le_of_le_loglog hx1 h1.le) hq0 hq

/-- **Lower bounds for the low moments of the extended Rademacher sum, uniformly in `q`, with
`c = 10⁻¹⁰`, for every `x ≥ 3`.**  For every Rademacher function `X` on any probability space and
every `x ≥ 3`, with `Y(x) = x^{-1/2}∑_{n≤x} X^e(n)`,

* `10⁻¹⁰·min{log log x, 1/(1-2q)}·(log log x)^{-q/2} ≤ E|Y(x)|^{2q}` for `0 < q < ½`,
* `10⁻¹⁰·(log log x)^{3/4} ≤ E|Y(x)|`,
* `10⁻¹⁰·(log x)^{q(2q-1)}·min{1/(2q-1), log log x}^{3/4} ≤ E|Y(x)|^{2q}` for `½ < q ≤ 1`.

`RMF.weighted_rademacher_moments_lower_uniform_explicit_every_x` for the extended sum. -/
theorem extended_rademacher_moments_lower_uniform_explicit_every_x :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        (∀ q : ℝ, 0 < q → q < 1 / 2 →
          1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
              * Real.log (Real.log x) ^ (-(q / 2)))
            ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                ^ (2 * q) ∂μ) ∧
        1 / 10 ^ 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ)
          ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ ∧
        (∀ q : ℝ, 1 / 2 < q → q ≤ 1 →
          1 / 10 ^ 10 * (Real.log x ^ (q * (2 * q - 1))
              * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
            ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                ^ (2 * q) ∂μ) := by
  intro Ω _ X μ hX x hx
  have hΛ0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg (one_le_log_of_three_le hx)
  refine ⟨fun q hq0 hq2 => le_integral_rpow_belowHalf_of_three_le_ext hX hx hq0 hq2, ?_,
    fun q hq2 hq1 =>
      integral_rpow_normalisedSum_compMultExtension_ge_aboveHalf_explicit hX hx hq2 hq1⟩
  exact le_trans (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hΛ0 _))
    (integral_norm_normalisedSum_compMultExtension_ge_explicit hX hx)

/-- **The low moments of the extended Rademacher sum, uniformly in `q`, with `c = 10⁻¹⁰` and
`C = 30`, for every `x ≥ 3`.**  For every Rademacher function `X` on any probability space and
every `x ≥ 3`, with `Y(x) = x^{-1/2}∑_{n≤x} X^e(n)` and `Λ = log log x`,

* `10⁻¹⁰·G ≤ E|Y(x)|^{2q} ≤ 30·G`, `G = min{Λ, 1/(1-2q)}·Λ^{-q/2}`, for `0 < q < ½`,
* `10⁻¹⁰·Λ^{3/4} ≤ E|Y(x)| ≤ 30·Λ^{3/4}`,
* `10⁻¹⁰·G ≤ E|Y(x)|^{2q} ≤ 30·G`, `G = (log x)^{q(2q-1)}·min{1/(2q-1), Λ}^{3/4}`, for
  `½ < q ≤ 1`.

`RMF.extended_rademacher_moments_lower_uniform_explicit_every_x` and
`RMF.extended_rademacher_moments_upper_uniform_explicit`. -/
theorem extended_rademacher_moments_asymp_uniform_explicit_every_x :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        (∀ q : ℝ, 0 < q → q < 1 / 2 →
          1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
              * Real.log (Real.log x) ^ (-(q / 2)))
              ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
            ∧ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
              ≤ 30 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
                * Real.log (Real.log x) ^ (-(q / 2)))) ∧
        (1 / 10 ^ 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ)
            ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ
          ∧ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ
            ≤ 30 * Real.log (Real.log x) ^ (3 / 4 : ℝ)) ∧
        (∀ q : ℝ, 1 / 2 < q → q ≤ 1 →
          1 / 10 ^ 10 * (Real.log x ^ (q * (2 * q - 1))
              * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
              ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
            ∧ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
              ≤ 30 * (Real.log x ^ (q * (2 * q - 1))
                * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))) := by
  intro Ω _ X μ hX x hx
  obtain ⟨l1, l2, l3⟩ := extended_rademacher_moments_lower_uniform_explicit_every_x Ω X μ hX x hx
  obtain ⟨u1, u2, u3⟩ := extended_rademacher_moments_upper_uniform_explicit Ω X μ hX x hx
  exact ⟨fun q hq0 hq2 => ⟨l1 q hq0 hq2, u1 q hq0 hq2⟩, ⟨l2, u2⟩,
    fun q hq2 hq1 => ⟨l3 q hq2 hq1, u3 q hq2 hq1⟩⟩

end RMF
