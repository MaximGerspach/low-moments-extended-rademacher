/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.SecondMoment

/-!
# Uniformity as `q → 0`: descending from a fixed exponent

The small-`q` chain is **not** uniform down to `q = 0` as it stands, and the loss is structural,
not an artefact:

* subadditivity of `u ↦ u^q` over the `≍ log log x` mesoscopic windows
  (`RMF.integral_rpow_setIntegral_weight_le_sum_windows_primesIco`) costs a factor equal to the
  *number of windows* as `q → 0`, since every summand tends to `1`;
* the depth sum, read sharply, produces `min{(q(1-2q))^{-1}, log log x}` — and the `1/q` there is
  real.

Both are harmless, because the target
`E|S(x)|^{2q} ≪ (log log x)^{-q/2}·min{(1-2q)^{-1}, log log x}` is proved at a **fixed** `q₀` and
then carried down.  That is what this file does.

## Why the shape survives

Jensen at exponent `r = q/q₀ ≤ 1` applied to `‖S‖^{2q₀}` gives
`E‖S‖^{2q} = E[(‖S‖^{2q₀})^r] ≤ (E‖S‖^{2q₀})^r`, and a right-hand side `K·Λ^{-q₀/2}` becomes
`K^{r}·Λ^{-q/2}` — **the exponent tracks `q` exactly and the constant only shrinks**, because
`K^{r} ≤ max{1,K}` for `0 ≤ r ≤ 1`.  So the descent is lossless in the shape and costs one
`max` in the constant.

At `q₀ = 1/4` the factor `min{(1-2q₀)^{-1}, log log x}` is the constant `2`, which is why that is
the natural place to descend from: below it the `min` carries no information, and above it the
chain is uniform on its own.  And since `min{(1-2q)^{-1}, Λ} ≥ 1` for every `0 ≤ q < 1/2`, the
plain conclusion `≤ C·Λ^{-q/2}` already implies the target shape.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The target shape descends too**, and the exponent tracks `q` exactly.  From
`E‖S‖^{2q₀} ≤ K·Λ^{-q₀/2}` at one `q₀` to `E‖S‖^{2q} ≤ max{1,K}·Λ^{-q/2}` for every `0 < q ≤ q₀`:
the constant does not grow, so the small-`q` end of the range costs nothing, although the chain
that proves the bound at `q₀` is not uniform.  At `Λ = log log x` the conclusion implies the target
`≤ C·Λ^{-q/2}·min{(1-2q)^{-1}, Λ}`, that `min` being at least `1`. -/
theorem integral_rpow_le_rpow_of_le_exponent {S : Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {q q₀ K Λ : ℝ} (hq0 : 0 < q) (hqq₀ : q ≤ q₀) (hK : 0 < K)
    (hΛ : 0 < Λ) (hgi : Integrable (fun ω => ‖S ω‖ ^ (2 * q₀)) μ)
    (h : (∫ ω, ‖S ω‖ ^ (2 * q₀) ∂μ) ≤ K * Λ ^ (-(q₀ / 2))) :
    (∫ ω, ‖S ω‖ ^ (2 * q) ∂μ) ≤ max 1 K * Λ ^ (-(q / 2)) := by
  have hq₀0 : (0 : ℝ) < q₀ := lt_of_lt_of_le hq0 hqq₀
  have hr0 : (0 : ℝ) ≤ q / q₀ := by positivity
  have hr1 : q / q₀ ≤ 1 := by rw [div_le_one hq₀0]; exact hqq₀
  have hpt : ∀ ω : Ω, ‖S ω‖ ^ (2 * q) = (‖S ω‖ ^ (2 * q₀)) ^ (q / q₀) := by
    intro ω
    rw [← Real.rpow_mul (norm_nonneg _)]
    congr 1
    field_simp
  have h0 : ∀ᵐ ω ∂μ, ‖S ω‖ ^ (2 * q₀) ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have h0' : ∀ᵐ ω ∂μ, (0 : ℝ) ≤ ‖S ω‖ ^ (2 * q₀) := h0
  have hI0 : (0 : ℝ) ≤ ∫ ω, ‖S ω‖ ^ (2 * q₀) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  simp only [hpt]
  refine le_trans (integral_rpow_le_rpow_integral hr0 hr1 h0 hgi
    (integrable_rpow_of_integrable hgi h0' hr0 hr1)) ?_
  refine le_trans (Real.rpow_le_rpow hI0 h hr0) ?_
  have hsplit : (K * Λ ^ (-(q₀ / 2))) ^ (q / q₀)
      = K ^ (q / q₀) * (Λ ^ (-(q₀ / 2))) ^ (q / q₀) :=
    Real.mul_rpow hK.le (Real.rpow_nonneg hΛ.le _)
  -- the exponent tracks `q` exactly
  have hexp : (Λ ^ (-(q₀ / 2))) ^ (q / q₀) = Λ ^ (-(q / 2)) := by
    rw [← Real.rpow_mul hΛ.le]
    congr 1
    field_simp
  rw [hsplit, hexp]
  exact mul_le_mul_of_nonneg_right (rpow_le_max_one hK hr0 hr1)
    (Real.rpow_nonneg hΛ.le _)

end RMF
