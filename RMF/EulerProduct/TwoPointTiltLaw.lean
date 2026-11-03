/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import RMF.EulerProduct.LogField
import RMF.EulerProduct.Moments
import RMF.EulerProduct.TiltedLaw

/-!
# The two-fold tilted Steinhaus law

`RMF/EulerProduct/TiltedLaw.lean` computes the mean, variance and third absolute moment of
`RMF.localLog w` under the **one-fold** tilt `‖(1 - z a)⁻¹‖²`; the two-point argument of the
restricted second moment needs the same quantities under the **two-fold** tilt
`‖(1 - z a₁)⁻¹‖² ‖(1 - z a₂)⁻¹‖²`, which is the law of `f(p)` under
`RMF.tiltedMeasure₂` (`RMF.IsSteinhausPrimeValues.map_tiltedMeasure₂`).

## Why the perturbation bound is not enough for the mean

`RMF.abs_integral_tilted_sub_integral_le` says that tilting by a small exponent moves a bounded
expectation by `O(MK)`, and `M = ‖localTilt a₂‖_∞` and `K = ‖localLog w‖_∞` are both `O(δ)` with
`δ = p^{-1/2-σ}`.  So it moves the mean by `O(δ²)` — and the mean **is** `O(δ²)`.  For the second
moment and the third absolute moment the same estimate is fine, because there the main term is
`O(δ²)` and `O(δ³)` against a perturbation of `O(δ³)` and `O(δ⁴)`; for the drift it destroys
exactly what it is meant to measure.

## The route taken instead

Expand pointwise on the circle and integrate against `RMF.steinhausLaw` itself, where the
characters are orthonormal.  Two first-order facts do all the work:

* `RMF.abs_localLog_sub_re_le` — `localLog w z = Re(zw) + O(‖w‖²)`;
* `Real.abs_exp_sub_one_sub_id_le` — `e^u = 1 + u + O(u²)` for `|u| ≤ 1`,

and the exact evaluations `∫ localLog w = 0` (`RMF.integral_localLog_eq_zero`),
`∫ Re(zw) = 0` and `∫ Re(zw₁)Re(zw₂) = Re(w₁ \bar w₂)/2`
(`RMF.integral_re_mul_mul_re_steinhausLaw`).  What comes out is that **the two drifts simply
add**:

`E[localLog w] = Re(w \bar a₁) + Re(w \bar a₂) + O(δ³)`,

third order being the accuracy `RMF.sum_prime_Ioc_rpow_le` pays for once summed over a block.

The hypothesis is `‖a₁‖ + ‖a₂‖ ≤ 1/5` rather than `‖a₁‖, ‖a₂‖ ≤ 1/5`: the exponent of the tilt is
the *sum* of the two local exponents, and it is that sum which has to stay inside the range where
`e^u - 1 - u = O(u²)` is available.
-/

open MeasureTheory

namespace RMF

variable {a₁ a₂ w : ℂ}

/-! ### The two-fold exponent on the circle -/

/-- The two-fold tilt exponent is `O(‖a₁‖ + ‖a₂‖)` on the circle. -/
lemma abs_two_localLog_add_le {z : ℂ} (hz : ‖z‖ = 1) (h₁ : ‖a₁‖ ≤ 1 / 5)
    (h₂ : ‖a₂‖ ≤ 1 / 5) :
    |2 * localLog a₁ z + 2 * localLog a₂ z| ≤ 22 / 5 * (‖a₁‖ + ‖a₂‖) := by
  have hb₁ := abs_le.1 (abs_localLog_le_of_norm_le hz h₁)
  have hb₂ := abs_le.1 (abs_localLog_le_of_norm_le hz h₂)
  exact abs_le.2 ⟨by linarith [hb₁.1, hb₂.1], by linarith [hb₁.2, hb₂.2]⟩

/-- **The two-fold weight, to first order.**  `e^g = 1 + 2Re(za₁) + 2Re(za₂) + O((‖a₁‖+‖a₂‖)²)`
on the circle.  This is the expansion the drift is read off from, and the reason the hypothesis is
on the *sum* of the two moduli: it is the sum that has to stay inside `|u| ≤ 1`. -/
lemma abs_exp_two_localLog_add_sub_le {z : ℂ} (hz : ‖z‖ = 1)
    (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5) :
    |Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z)
        - (1 + 2 * (z * a₁).re + 2 * (z * a₂).re)| ≤ 32 * (‖a₁‖ + ‖a₂‖) ^ 2 := by
  have hn₁ : (0 : ℝ) ≤ ‖a₁‖ := norm_nonneg a₁
  have hn₂ : (0 : ℝ) ≤ ‖a₂‖ := norm_nonneg a₂
  have hg : |2 * localLog a₁ z + 2 * localLog a₂ z| ≤ 22 / 5 * (‖a₁‖ + ‖a₂‖) :=
    abs_two_localLog_add_le hz (by linarith) (by linarith)
  have hg1 : |2 * localLog a₁ z + 2 * localLog a₂ z| ≤ 1 := le_trans hg (by linarith)
  have hexp := abs_le.1 (Real.abs_exp_sub_one_sub_id_le hg1)
  have hr₁ := abs_le.1 (abs_localLog_sub_re_le hz (show ‖a₁‖ ≤ 1 / 5 by linarith))
  have hr₂ := abs_le.1 (abs_localLog_sub_re_le hz (show ‖a₂‖ ≤ 1 / 5 by linarith))
  have hgsq : (2 * localLog a₁ z + 2 * localLog a₂ z) ^ 2
      ≤ (22 / 5) ^ 2 * (‖a₁‖ + ‖a₂‖) ^ 2 := by
    nlinarith [sq_abs (2 * localLog a₁ z + 2 * localLog a₂ z),
      abs_nonneg (2 * localLog a₁ z + 2 * localLog a₂ z)]
  have hsq : ‖a₁‖ ^ 2 + ‖a₂‖ ^ 2 ≤ (‖a₁‖ + ‖a₂‖) ^ 2 := by nlinarith
  refine abs_le.2 ⟨?_, ?_⟩ <;>
    nlinarith [hexp.1, hexp.2, hr₁.1, hr₁.2, hr₂.1, hr₂.2, hgsq, hsq]

/-- The two-fold weight is within `O(‖a₁‖+‖a₂‖)` of `1` on the circle. -/
lemma abs_exp_two_localLog_add_sub_one_le {z : ℂ} (hz : ‖z‖ = 1)
    (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5) :
    |Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) - 1| ≤ 44 / 5 * (‖a₁‖ + ‖a₂‖) := by
  have hn₁ : (0 : ℝ) ≤ ‖a₁‖ := norm_nonneg a₁
  have hn₂ : (0 : ℝ) ≤ ‖a₂‖ := norm_nonneg a₂
  have hg : |2 * localLog a₁ z + 2 * localLog a₂ z| ≤ 22 / 5 * (‖a₁‖ + ‖a₂‖) :=
    abs_two_localLog_add_le hz (by linarith) (by linarith)
  have hgle := abs_le.1 hg
  have hg1 : |2 * localLog a₁ z + 2 * localLog a₂ z| ≤ 1 := le_trans hg (by linarith)
  have hexp := abs_le.1 (Real.abs_exp_sub_one_sub_id_le hg1)
  have hgsq : (2 * localLog a₁ z + 2 * localLog a₂ z) ^ 2 ≤ 22 / 5 * (‖a₁‖ + ‖a₂‖) := by
    nlinarith [sq_abs (2 * localLog a₁ z + 2 * localLog a₂ z),
      abs_nonneg (2 * localLog a₁ z + 2 * localLog a₂ z)]
  exact abs_le.2 ⟨by linarith [hexp.1, hgle.1], by linarith [hexp.2, hgle.2]⟩

/-- The two-fold weight is bounded below on the circle: `e^g ≥ e^{-1} > 1/3`. -/
lemma one_third_le_exp_two_localLog_add {z : ℂ} (hz : ‖z‖ = 1)
    (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5) :
    1 / 3 ≤ Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) := by
  have hn₁ : (0 : ℝ) ≤ ‖a₁‖ := norm_nonneg a₁
  have hn₂ : (0 : ℝ) ≤ ‖a₂‖ := norm_nonneg a₂
  have hg : |2 * localLog a₁ z + 2 * localLog a₂ z| ≤ 22 / 5 * (‖a₁‖ + ‖a₂‖) :=
    abs_two_localLog_add_le hz (by linarith) (by linarith)
  have hg1 : -1 ≤ 2 * localLog a₁ z + 2 * localLog a₂ z :=
    (abs_le.1 (le_trans hg (by linarith : 22 / 5 * (‖a₁‖ + ‖a₂‖) ≤ 1))).1
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h9 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hinv : (1 : ℝ) / 3 ≤ (Real.exp 1)⁻¹ := by
    have hmul : (Real.exp 1)⁻¹ * Real.exp 1 = 1 := inv_mul_cancel₀ hpos.ne'
    nlinarith [inv_pos.2 hpos]
  calc (1 : ℝ) / 3 ≤ (Real.exp 1)⁻¹ := hinv
    _ = Real.exp (-1 : ℝ) := by rw [Real.exp_neg]
    _ ≤ Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) := Real.exp_le_exp.2 hg1

/-- The two-fold weight is at most `3` on the circle. -/
lemma exp_two_localLog_add_le_three {z : ℂ} (hz : ‖z‖ = 1)
    (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5) :
    Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) ≤ 3 := by
  have hn₁ : (0 : ℝ) ≤ ‖a₁‖ := norm_nonneg a₁
  have hn₂ : (0 : ℝ) ≤ ‖a₂‖ := norm_nonneg a₂
  have hg : |2 * localLog a₁ z + 2 * localLog a₂ z| ≤ 22 / 5 * (‖a₁‖ + ‖a₂‖) :=
    abs_two_localLog_add_le hz (by linarith) (by linarith)
  have hg1 : 2 * localLog a₁ z + 2 * localLog a₂ z ≤ 1 :=
    (abs_le.1 (le_trans hg (by linarith : 22 / 5 * (‖a₁‖ + ‖a₂‖) ≤ 1))).2
  have h9 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  linarith [Real.exp_le_exp.2 hg1]

/-- **The integrand of the numerator, to third order.**  `localLog w · (e^g - 1)` differs from
`Re(zw)(2Re(za₁) + 2Re(za₂))` by `O(δ³)` pointwise on the circle.

The `-1` matters: `localLog w · e^g` on its own differs from the cross term by `O(‖w‖)`, first
order.  What removes it is that `∫ localLog w` vanishes exactly. -/
lemma abs_localLog_mul_exp_sub_one_sub_re_le {z : ℂ} (hz : ‖z‖ = 1)
    (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) :
    |localLog w z * (Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) - 1)
        - (z * w).re * (2 * (z * a₁).re + 2 * (z * a₂).re)|
      ≤ 53 * ‖w‖ ^ 2 * (‖a₁‖ + ‖a₂‖) + 32 * ‖w‖ * (‖a₁‖ + ‖a₂‖) ^ 2 := by
  have hn₁ : (0 : ℝ) ≤ ‖a₁‖ := norm_nonneg a₁
  have hn₂ : (0 : ℝ) ≤ ‖a₂‖ := norm_nonneg a₂
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hL := abs_localLog_sub_re_le hz hw
  have hE1 := abs_exp_two_localLog_add_sub_one_le hz hA
  have hE2 := abs_exp_two_localLog_add_sub_le hz hA
  have hre : |(z * w).re| ≤ ‖w‖ :=
    (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul])
  have hsplit : localLog w z * (Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) - 1)
      - (z * w).re * (2 * (z * a₁).re + 2 * (z * a₂).re)
      = (localLog w z - (z * w).re)
          * (Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) - 1)
        + (z * w).re * ((Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z)
            - (1 + 2 * (z * a₁).re + 2 * (z * a₂).re))) := by ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_mul]
  have h1 : |localLog w z - (z * w).re|
      * |Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) - 1|
      ≤ 6 * ‖w‖ ^ 2 * (44 / 5 * (‖a₁‖ + ‖a₂‖)) :=
    mul_le_mul hL hE1 (abs_nonneg _) (by positivity)
  have h2 : |(z * w).re| * |Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z)
        - (1 + 2 * (z * a₁).re + 2 * (z * a₂).re)|
      ≤ ‖w‖ * (32 * (‖a₁‖ + ‖a₂‖) ^ 2) :=
    mul_le_mul hre hE2 (abs_nonneg _) hw0
  nlinarith

/-! ### The two-fold tilted local mean

`∫ localLog w dν = N/Z` with `N = ∫ localLog w · e^g` and `Z = ∫ e^g` taken against
`RMF.steinhausLaw` itself, where the characters are orthonormal.  `Z = 1 + O(A²)` and
`N = Re(w \bar a₁) + Re(w \bar a₂) + O(δ³)`; the quotient is the drift. -/

/-- The two-fold weight is integrable. -/
lemma integrable_exp_two_localLog_add (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5) :
    Integrable (fun z => Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z)) steinhausLaw := by
  refine integrable_of_norm_le_steinhausLaw ?_ 3 ?_
  · exact ((((measurable_localLog a₁).const_mul 2).add
      ((measurable_localLog a₂).const_mul 2)).exp).aestronglyMeasurable
  · filter_upwards [norm_eq_one_steinhausLaw] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact exp_two_localLog_add_le_three hz hA

/-- `RMF.localLog` is integrable against the Steinhaus law: it is bounded on the circle. -/
lemma integrable_localLog_steinhausLaw (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (localLog w) steinhausLaw := by
  refine integrable_of_norm_le_steinhausLaw (measurable_localLog w).aestronglyMeasurable
    (11 / 5 * ‖w‖) ?_
  filter_upwards [norm_eq_one_steinhausLaw] with z hz
  rw [Real.norm_eq_abs]
  exact abs_localLog_le_of_norm_le hz hw

/-- The observable against the centred weight is integrable. -/
lemma integrable_localLog_mul_exp_sub_one (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun z => localLog w z
      * (Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) - 1)) steinhausLaw := by
  refine integrable_of_norm_le_steinhausLaw ?_ (11 / 5 * ‖w‖ * 4) ?_
  · exact ((measurable_localLog w).mul
      (((((measurable_localLog a₁).const_mul 2).add
        ((measurable_localLog a₂).const_mul 2)).exp).sub
          measurable_const)).aestronglyMeasurable
  · filter_upwards [norm_eq_one_steinhausLaw] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := abs_localLog_le_of_norm_le hz hw
    have h2 := exp_two_localLog_add_le_three hz hA
    have h3 : (0 : ℝ) ≤ Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) := Real.exp_nonneg _
    have h4 : |Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) - 1| ≤ 4 :=
      abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg (localLog w z), norm_nonneg w]

/-- **The normaliser.**  `Z = 1 + O((‖a₁‖+‖a₂‖)²)`: the first-order terms integrate to zero. -/
lemma abs_integral_exp_two_localLog_add_sub_one_le (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5) :
    |(∫ z, Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) ∂steinhausLaw) - 1|
      ≤ 32 * (‖a₁‖ + ‖a₂‖) ^ 2 := by
  have hre : ∀ c : ℂ, Integrable (fun z : ℂ => (z * c).re) steinhausLaw := fun c =>
    integrable_of_norm_le_steinhausLaw (by fun_prop) ‖c‖ (by
      filter_upwards [norm_eq_one_steinhausLaw] with z hz
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul]))
  have hE := integrable_exp_two_localLog_add (a₁ := a₁) (a₂ := a₂) hA
  have hzero : ∀ c : ℂ, (∫ z : ℂ, 2 * (z * c).re ∂steinhausLaw) = 0 := by
    intro c
    rw [integral_const_mul, integral_re_mul_steinhausLaw, mul_zero]
  have hi0 : Integrable (fun z : ℂ => (1 : ℝ) + 2 * (z * a₁).re) steinhausLaw :=
    (integrable_const 1).add ((hre a₁).const_mul 2)
  have hi1 : Integrable
      (fun z : ℂ => (1 : ℝ) + 2 * (z * a₁).re + 2 * (z * a₂).re) steinhausLaw :=
    hi0.add ((hre a₂).const_mul 2)
  have e1 : (∫ z : ℂ, ((1 : ℝ) + 2 * (z * a₁).re + 2 * (z * a₂).re) ∂steinhausLaw)
      = (∫ z : ℂ, ((1 : ℝ) + 2 * (z * a₁).re) ∂steinhausLaw)
        + ∫ z : ℂ, 2 * (z * a₂).re ∂steinhausLaw :=
    integral_add hi0 ((hre a₂).const_mul 2)
  have e2 : (∫ z : ℂ, ((1 : ℝ) + 2 * (z * a₁).re) ∂steinhausLaw)
      = (∫ _ : ℂ, (1 : ℝ) ∂steinhausLaw) + ∫ z : ℂ, 2 * (z * a₁).re ∂steinhausLaw :=
    integral_add (integrable_const 1) ((hre a₁).const_mul 2)
  have hint1 : (∫ z : ℂ, ((1 : ℝ) + 2 * (z * a₁).re + 2 * (z * a₂).re) ∂steinhausLaw)
      = 1 := by
    rw [e1, e2, hzero a₁, hzero a₂]
    simp
  have hsplit : (∫ z, (Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z)
        - (1 + 2 * (z * a₁).re + 2 * (z * a₂).re)) ∂steinhausLaw)
      = (∫ z, Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) ∂steinhausLaw) - 1 := by
    rw [integral_sub hE hi1, hint1]
  rw [← hsplit]
  have hbd : ‖∫ z, (Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z)
      - (1 + 2 * (z * a₁).re + 2 * (z * a₂).re)) ∂steinhausLaw‖
      ≤ 32 * (‖a₁‖ + ‖a₂‖) ^ 2 * steinhausLaw.real Set.univ := by
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    rw [Real.norm_eq_abs]
    exact abs_exp_two_localLog_add_sub_le hz hA
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at hbd
  exact hbd

/-- **The normaliser is bounded below**, which is what makes the quotient safe. -/
lemma one_third_le_integral_exp_two_localLog_add (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5) :
    1 / 3 ≤ ∫ z, Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) ∂steinhausLaw := by
  have hE := integrable_exp_two_localLog_add (a₁ := a₁) (a₂ := a₂) hA
  have h : (∫ _ : ℂ, (1 / 3 : ℝ) ∂steinhausLaw)
      ≤ ∫ z, Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) ∂steinhausLaw := by
    refine integral_mono_ae (integrable_const _) hE ?_
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact one_third_le_exp_two_localLog_add hz hA
  simpa using h

/-- **The numerator.**  `N = Re(w \bar a₁) + Re(w \bar a₂) + O(δ³)`. -/
lemma abs_integral_localLog_mul_exp_sub_le (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ z, localLog w z * Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) ∂steinhausLaw)
        - ((w * (starRingEnd ℂ) a₁).re + (w * (starRingEnd ℂ) a₂).re)|
      ≤ 53 * ‖w‖ ^ 2 * (‖a₁‖ + ‖a₂‖) + 32 * ‖w‖ * (‖a₁‖ + ‖a₂‖) ^ 2 := by
  have hprod : ∀ c : ℂ, Integrable (fun z : ℂ => (z * w).re * (z * c).re) steinhausLaw :=
    fun c => integrable_of_norm_le_steinhausLaw (by fun_prop) (‖w‖ * ‖c‖) (by
      filter_upwards [norm_eq_one_steinhausLaw] with z hz
      have e₀ : |(z * w).re| ≤ ‖w‖ :=
        (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul])
      have e₁ : |(z * c).re| ≤ ‖c‖ :=
        (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul])
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul e₀ e₁ (abs_nonneg _) (norm_nonneg w))
  -- the cross term evaluates exactly
  have hcross : Integrable (fun z : ℂ => (z * w).re * (2 * (z * a₁).re + 2 * (z * a₂).re))
      steinhausLaw := by
    have hrw : (fun z : ℂ => (z * w).re * (2 * (z * a₁).re + 2 * (z * a₂).re))
        = fun z : ℂ => 2 * ((z * w).re * (z * a₁).re) + 2 * ((z * w).re * (z * a₂).re) := by
      funext z; ring
    rw [hrw]
    exact ((hprod a₁).const_mul 2).add ((hprod a₂).const_mul 2)
  have hmain : (∫ z, (z * w).re * (2 * (z * a₁).re + 2 * (z * a₂).re) ∂steinhausLaw)
      = (w * (starRingEnd ℂ) a₁).re + (w * (starRingEnd ℂ) a₂).re := by
    have hrw : (fun z : ℂ => (z * w).re * (2 * (z * a₁).re + 2 * (z * a₂).re))
        = fun z : ℂ => 2 * ((z * w).re * (z * a₁).re) + 2 * ((z * w).re * (z * a₂).re) := by
      funext z; ring
    rw [hrw]
    have e1 : (∫ z : ℂ, (2 * ((z * w).re * (z * a₁).re)
          + 2 * ((z * w).re * (z * a₂).re)) ∂steinhausLaw)
        = (∫ z : ℂ, 2 * ((z * w).re * (z * a₁).re) ∂steinhausLaw)
          + ∫ z : ℂ, 2 * ((z * w).re * (z * a₂).re) ∂steinhausLaw :=
      integral_add ((hprod a₁).const_mul 2) ((hprod a₂).const_mul 2)
    rw [e1, integral_const_mul, integral_const_mul, integral_re_mul_mul_re_steinhausLaw,
      integral_re_mul_mul_re_steinhausLaw]
    ring
  -- the exact vanishing of the plain local mean
  have hzero : (∫ z, localLog w z ∂steinhausLaw) = 0 :=
    integral_localLog_eq_zero (by linarith [norm_nonneg w])
  have hcent := integrable_localLog_mul_exp_sub_one (a₁ := a₁) (a₂ := a₂) (w := w) hA hw
  have hL := integrable_localLog_steinhausLaw (w := w) hw
  have hdecomp : (∫ z, localLog w z
        * Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) ∂steinhausLaw)
      = ∫ z, localLog w z
        * (Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) - 1) ∂steinhausLaw := by
    have hrw : (fun z => localLog w z * Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z))
        = fun z => localLog w z
            * (Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) - 1) + localLog w z := by
      funext z; ring
    rw [hrw]
    have e2 : (∫ z : ℂ, (localLog w z
          * (Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) - 1) + localLog w z)
          ∂steinhausLaw)
        = (∫ z : ℂ, localLog w z
            * (Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) - 1) ∂steinhausLaw)
          + ∫ z : ℂ, localLog w z ∂steinhausLaw := integral_add hcent hL
    rw [e2, hzero, add_zero]
  rw [hdecomp, ← hmain, ← integral_sub hcent hcross]
  have hbd : ‖∫ z, (localLog w z
      * (Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) - 1)
      - (z * w).re * (2 * (z * a₁).re + 2 * (z * a₂).re)) ∂steinhausLaw‖
      ≤ (53 * ‖w‖ ^ 2 * (‖a₁‖ + ‖a₂‖) + 32 * ‖w‖ * (‖a₁‖ + ‖a₂‖) ^ 2)
        * steinhausLaw.real Set.univ := by
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    rw [Real.norm_eq_abs]
    exact abs_localLog_mul_exp_sub_one_sub_re_le hz hA hw
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at hbd
  exact hbd

/-- **The two-fold tilted local mean**: `E[localLog w] = Re(w \bar a₁) + Re(w \bar a₂) + O(δ³)`
under the tilt by `‖(1 - za₁)⁻¹‖²‖(1 - za₂)⁻¹‖²`, for `‖a₁‖ + ‖a₂‖ ≤ 1/5` and `‖w‖ ≤ 1/5`: the
two drifts add.  `RMF.abs_integral_tilted_sub_integral_le` cannot give this, its error `O(‖a₂‖‖w‖)`
being the order of the main term.  Third order suffices for the block sums
(`RMF.sum_prime_Ioc_rpow_le`); the one-fold `RMF.abs_integral_localLog_tilted_sub_re_le` has a
fourth-order error, since it reproduces a harmonic function with the Poisson kernel. -/
theorem abs_integral_localLog_tilted_pair_sub_le (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5)
    (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ z, localLog w z
          ∂(steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z))
        - ((w * (starRingEnd ℂ) a₁).re + (w * (starRingEnd ℂ) a₂).re)|
      ≤ 160 * ‖w‖ ^ 2 * (‖a₁‖ + ‖a₂‖) + 120 * ‖w‖ * (‖a₁‖ + ‖a₂‖) ^ 2 := by
  have hn₁ : (0 : ℝ) ≤ ‖a₁‖ := norm_nonneg a₁
  have hn₂ : (0 : ℝ) ≤ ‖a₂‖ := norm_nonneg a₂
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ,
      Z = ∫ z, Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) ∂steinhausLaw := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ∫ z, localLog w z
      * Real.exp (2 * localLog a₁ z + 2 * localLog a₂ z) ∂steinhausLaw := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ,
      M = (w * (starRingEnd ℂ) a₁).re + (w * (starRingEnd ℂ) a₂).re := ⟨_, rfl⟩
  have hZ3 : 1 / 3 ≤ Z := by
    rw [hZdef]; exact one_third_le_integral_exp_two_localLog_add hA
  have hZ1 : |Z - 1| ≤ 32 * (‖a₁‖ + ‖a₂‖) ^ 2 := by
    rw [hZdef]; exact abs_integral_exp_two_localLog_add_sub_one_le hA
  have hN : |N - M| ≤ 53 * ‖w‖ ^ 2 * (‖a₁‖ + ‖a₂‖) + 32 * ‖w‖ * (‖a₁‖ + ‖a₂‖) ^ 2 := by
    rw [hNdef, hMdef]; exact abs_integral_localLog_mul_exp_sub_le hA hw
  have hM : |M| ≤ ‖w‖ * (‖a₁‖ + ‖a₂‖) := by
    have e₁ : |(w * (starRingEnd ℂ) a₁).re| ≤ ‖w‖ * ‖a₁‖ := by
      refine (Complex.abs_re_le_norm _).trans_eq ?_
      rw [norm_mul, Complex.norm_conj]
    have e₂ : |(w * (starRingEnd ℂ) a₂).re| ≤ ‖w‖ * ‖a₂‖ := by
      refine (Complex.abs_re_le_norm _).trans_eq ?_
      rw [norm_mul, Complex.norm_conj]
    have h₁ := abs_le.1 e₁
    have h₂ := abs_le.1 e₂
    rw [hMdef]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  -- the tilted mean is the quotient
  have hquot : (∫ z, localLog w z
        ∂(steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z)) = N / Z := by
    rw [hNdef, hZdef, integral_tilted, ← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [smul_eq_mul]
    ring
  rw [hquot, ← hMdef]
  -- and the quotient is what the three bounds say it is
  have hZpos : (0 : ℝ) < Z := by linarith
  have hrw : N / Z - M = (N - M * Z) / Z := by field_simp
  rw [hrw, abs_div, abs_of_pos hZpos, div_le_iff₀ hZpos]
  have hMZ : |M * (Z - 1)| ≤ ‖w‖ * (‖a₁‖ + ‖a₂‖) * (32 * (‖a₁‖ + ‖a₂‖) ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul hM hZ1 (abs_nonneg _) (by positivity)
  have hB0 : (0 : ℝ)
      ≤ 160 * ‖w‖ ^ 2 * (‖a₁‖ + ‖a₂‖) + 120 * ‖w‖ * (‖a₁‖ + ‖a₂‖) ^ 2 := by positivity
  have hBZ : (160 * ‖w‖ ^ 2 * (‖a₁‖ + ‖a₂‖) + 120 * ‖w‖ * (‖a₁‖ + ‖a₂‖) ^ 2) * (1 / 3)
      ≤ (160 * ‖w‖ ^ 2 * (‖a₁‖ + ‖a₂‖) + 120 * ‖w‖ * (‖a₁‖ + ‖a₂‖) ^ 2) * Z :=
    mul_le_mul_of_nonneg_left hZ3 hB0
  have hA0 : (0 : ℝ) ≤ ‖a₁‖ + ‖a₂‖ := by linarith
  have hprod : (0 : ℝ) ≤ ‖w‖ * ((‖a₁‖ + ‖a₂‖) * (‖a₁‖ + ‖a₂‖)) :=
    mul_nonneg hw0 (mul_nonneg hA0 hA0)
  have hcube : ‖w‖ * (‖a₁‖ + ‖a₂‖) * (32 * (‖a₁‖ + ‖a₂‖) ^ 2)
      ≤ 32 / 5 * (‖w‖ * (‖a₁‖ + ‖a₂‖) ^ 2) := by
    nlinarith [mul_nonneg hprod (sub_nonneg.2 hA)]
  have h1 := abs_le.1 hN
  have h2 := abs_le.1 hMZ
  exact abs_le.2 ⟨by nlinarith [h1.1, h2.2], by nlinarith [h1.2, h2.1]⟩

/-! ### The two-fold tilt as a measure

The two lemmas below are what lets the one-fold work be reused: the two-fold tilt is a probability
measure, and it still lives on the circle.  Both are immediate; they are separated out because the
second and third moments each need them. -/

/-- **The two-fold tilt is a probability measure.** -/
lemma isProbabilityMeasure_tilted_localLog_pair (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5) :
    IsProbabilityMeasure (steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z) :=
  isProbabilityMeasure_tilted (integrable_exp_two_localLog_add hA)

/-- **The two-fold tilt lives on the circle**, being absolutely continuous with respect to
`RMF.steinhausLaw`. -/
lemma ae_norm_eq_one_tilted_pair :
    ∀ᵐ z ∂(steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z), ‖z‖ = 1 :=
  (tilted_absolutelyContinuous steinhausLaw _) norm_eq_one_steinhausLaw

/-! ### The two-fold tilted local second moment

Here the perturbation route works, and it is the one the one-fold second moment was built for.
The main term is `O(δ²)` and tilting by the *second* exponent moves it by `O(δ³)`, so
`RMF.abs_integral_tilted_sub_integral_le` is accurate enough — unlike for the mean, where its
error `O(‖a₂‖‖w‖)` is the same order as the main term and the expansion had to be done by hand. -/

/-- **The two-fold tilted local second moment.**  `E[(localLog w)²] = ‖w‖²/2 + O(δ³)` under the
tilt by `‖(1 - za₁)⁻¹‖²‖(1 - za₂)⁻¹‖²` — **the second tilt does not move it**, to third order.
`RMF.abs_integral_localLog_sq_tilted_sub_le` is the one-fold case. -/
theorem abs_integral_localLog_sq_tilted_pair_sub_le (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5)
    (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ z, localLog w z ^ 2
          ∂(steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z)) - ‖w‖ ^ 2 / 2|
      ≤ 20 * ‖w‖ ^ 3 + 240 * ‖w‖ ^ 2 * (‖a₁‖ + ‖a₂‖) := by
  have hn₁ : ‖a₁‖ ≤ 1 / 5 := by linarith [norm_nonneg a₂]
  have hn₂ : ‖a₂‖ ≤ 1 / 5 := by linarith [norm_nonneg a₁]
  have hlt₁ : ‖a₁‖ < 1 := by linarith
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  -- the two-fold tilt is a tilt of the one-fold tilt
  have hsplit : (steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z)
      = (steinhausLaw.tilted fun z => 2 * localLog a₁ z).tilted
          (fun z => 2 * localLog a₂ z) := by
    rw [tilted_tilted (integrable_exp_two_localLog hlt₁)]
    rfl
  have hprob := isProbabilityMeasure_tilted_localLog hlt₁
  -- the second tilt is small, and the observable is bounded
  have hg : ∀ᵐ z ∂(steinhausLaw.tilted fun z => 2 * localLog a₁ z),
      |2 * localLog a₂ z| ≤ 22 / 5 * ‖a₂‖ := by
    filter_upwards [ae_abs_localLog_le_tilted (a := a₁) hn₂] with z hz
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hf : ∀ᵐ z ∂(steinhausLaw.tilted fun z => 2 * localLog a₁ z),
      |localLog w z ^ 2| ≤ 121 / 25 * ‖w‖ ^ 2 := by
    filter_upwards [ae_abs_localLog_le_tilted (a := a₁) hw] with z hz
    rw [abs_pow]
    nlinarith [abs_nonneg (localLog w z)]
  have hpert := abs_integral_tilted_sub_integral_le (by positivity)
    (by linarith : 22 / 5 * ‖a₂‖ ≤ 1) (by positivity)
    ((measurable_localLog a₂).const_mul 2).aestronglyMeasurable
    ((measurable_localLog w).pow_const 2).aestronglyMeasurable hg hf
  have hone := abs_integral_localLog_sq_tilted_sub_le hlt₁ hw
  -- `4e ≤ 11`, and the rest is arithmetic in `‖w‖` and `‖a₁‖ + ‖a₂‖`
  have he : 4 * Real.exp 1 ≤ 11 := by
    have := Real.exp_one_lt_d9
    linarith
  have hprod : (0 : ℝ) ≤ 22 / 5 * ‖a₂‖ * (121 / 25 * ‖w‖ ^ 2) := by positivity
  have hpert' : |(∫ z, localLog w z ^ 2
        ∂((steinhausLaw.tilted fun z => 2 * localLog a₁ z).tilted
          fun z => 2 * localLog a₂ z))
      - ∫ z, localLog w z ^ 2 ∂(steinhausLaw.tilted fun z => 2 * localLog a₁ z)|
      ≤ 11 * (22 / 5 * ‖a₂‖) * (121 / 25 * ‖w‖ ^ 2) := by
    refine hpert.trans ?_
    nlinarith [hprod]
  rw [hsplit]
  have h1 := abs_le.1 hpert'
  have h2 := abs_le.1 hone
  have hsq₁ : ‖a₁‖ ^ 2 ≤ 1 / 5 * ‖a₁‖ := by nlinarith [norm_nonneg a₁]
  refine abs_le.2 ⟨by nlinarith [h1.1, h2.1, norm_nonneg a₁, norm_nonneg a₂],
    by nlinarith [h1.2, h2.2, norm_nonneg a₁, norm_nonneg a₂]⟩

/-! ### The two-fold tilted third absolute moment

No perturbation is involved: `localLog w` is bounded by `11‖w‖/5` on the circle, the two-fold tilt
lives on the circle, and it is a probability measure.  The bound is therefore the same constant as
in the one-fold case, `RMF.integral_abs_localLog_cube_tilted_le`. -/

/-- **The third absolute moment of a local term under the two-fold tilt**:
`E|localLog w|³ ≤ (11/5)³‖w‖³`.  This is the Lindeberg swap's error term. -/
theorem integral_abs_localLog_cube_tilted_pair_le (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5)
    (hw : ‖w‖ ≤ 1 / 5) :
    (∫ z, |localLog w z| ^ 3 ∂(steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z))
      ≤ (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
  have hprob := isProbabilityMeasure_tilted_localLog_pair hA
  have hm : Measurable fun z : ℂ => |localLog w z| ^ 3 := by
    simp only [← Real.norm_eq_abs]
    exact ((measurable_localLog w).norm).pow_const 3
  have hpt : ∀ᵐ z ∂(steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z),
      |localLog w z| ^ 3 ≤ (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
    filter_upwards [ae_norm_eq_one_tilted_pair (a₁ := a₁) (a₂ := a₂)] with z hz
    calc |localLog w z| ^ 3 ≤ (11 / 5 * ‖w‖) ^ 3 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_localLog_le_of_norm_le hz hw) 3
      _ = (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by ring
  calc (∫ z, |localLog w z| ^ 3
        ∂(steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z))
      ≤ ∫ _z : ℂ, (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3
        ∂(steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z) :=
        integral_mono_of_nonneg (.of_forall fun _ => by positivity) (integrable_const _) hpt
    _ = (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by simp

/-! ### The two-fold tilted local covariance

The cross moment `E[localLog w₁ · localLog w₂]` is the one with no one-point analogue to perturb
from — it only exists once there are two walks.  It does have an *untilted* analogue,
`RMF.abs_integral_localLog_mul_sub_le`, and the two-fold tilt moves that by `O(δ³)`: the observable
is bounded by `(11/5)²‖w₁‖‖w₂‖` on the circle and the exponent by `22(‖a₁‖+‖a₂‖)/5`, so
`RMF.abs_integral_tilted_sub_integral_le` applies in one step — no splitting of the tilt is needed
here, unlike for the mean.

At `w_i = p^{-1/2-σ-it_i}` the main term `Re(w₁ \bar w₂)/2` is `\cos((t₁-t₂)\log p)/2p^{1+2σ}`:
**this is the logarithmic correlation**, and it is why the two walks are not independent. -/

/-- **The two-fold tilted local covariance.**
`E[localLog w₁ · localLog w₂] = Re(w₁ \bar w₂)/2 + O(δ³)` under the tilt by
`‖(1 - za₁)⁻¹‖²‖(1 - za₂)⁻¹‖²`, for `‖a₁‖ + ‖a₂‖ ≤ 1/5` and `‖w₁‖, ‖w₂‖ ≤ 1/5`: the per-prime
form of the moment of `z₁z₂` (`RMF.quadMonomial`) that `RMF.abs_integral_swap_window_le` matches. -/
theorem abs_integral_localLog_mul_tilted_pair_sub_le {w₁ w₂ : ℂ}
    (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5) (h₁ : ‖w₁‖ ≤ 1 / 5) (h₂ : ‖w₂‖ ≤ 1 / 5) :
    |(∫ z, localLog w₁ z * localLog w₂ z
          ∂(steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z))
        - (w₁ * (starRingEnd ℂ) w₂).re / 2|
      ≤ 20 * (‖w₁‖ ^ 3 + ‖w₂‖ ^ 3) + 240 * (‖w₁‖ * ‖w₂‖) * (‖a₁‖ + ‖a₂‖) := by
  have hn₁ : ‖a₁‖ ≤ 1 / 5 := by linarith [norm_nonneg a₂]
  have hn₂ : ‖a₂‖ ≤ 1 / 5 := by linarith [norm_nonneg a₁]
  have hg : ∀ᵐ z ∂steinhausLaw, |2 * localLog a₁ z + 2 * localLog a₂ z|
      ≤ 22 / 5 * (‖a₁‖ + ‖a₂‖) := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact abs_two_localLog_add_le hz hn₁ hn₂
  have hf : ∀ᵐ z ∂steinhausLaw, |localLog w₁ z * localLog w₂ z|
      ≤ 121 / 25 * (‖w₁‖ * ‖w₂‖) := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    rw [abs_mul]
    exact (mul_le_mul (abs_localLog_le_of_norm_le hz h₁) (abs_localLog_le_of_norm_le hz h₂)
      (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hpert := abs_integral_tilted_sub_integral_le (by positivity)
    (by linarith : 22 / 5 * (‖a₁‖ + ‖a₂‖) ≤ 1) (by positivity)
    (((measurable_localLog a₁).const_mul 2).add
      ((measurable_localLog a₂).const_mul 2)).aestronglyMeasurable
    ((measurable_localLog w₁).mul (measurable_localLog w₂)).aestronglyMeasurable hg hf
  -- `4e ≤ 11`, and `11 · 22/5 · 121/25 < 240`
  have he : 4 * Real.exp 1 ≤ 11 := by
    have := Real.exp_one_lt_d9
    linarith
  have hprod : (0 : ℝ) ≤ (‖a₁‖ + ‖a₂‖) * (‖w₁‖ * ‖w₂‖) := by positivity
  have hbound : |(∫ z, localLog w₁ z * localLog w₂ z
        ∂(steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z))
      - ∫ z, localLog w₁ z * localLog w₂ z ∂steinhausLaw|
      ≤ 240 * (‖w₁‖ * ‖w₂‖) * (‖a₁‖ + ‖a₂‖) := by
    refine hpert.trans ?_
    nlinarith [hprod, mul_nonneg (sub_nonneg.2 he) hprod]
  have hone := abs_integral_localLog_mul_sub_le h₁ h₂
  have hb1 := abs_le.1 hbound
  have hb2 := abs_le.1 hone
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- `RMF.localLog` is integrable against the two-fold tilted law: it is a.e. bounded on the
circle, where the tilt lives, and the tilt is a probability measure. -/
lemma integrable_localLog_tilted_pair (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (localLog w)
      (steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z) := by
  have hprob := isProbabilityMeasure_tilted_localLog_pair hA
  refine (integrable_const (11 / 5 * ‖w‖)).mono'
    (measurable_localLog w).aestronglyMeasurable ?_
  filter_upwards [ae_norm_eq_one_tilted_pair (a₁ := a₁) (a₂ := a₂)] with z hz
  rw [Real.norm_eq_abs]
  exact abs_localLog_le_of_norm_le hz hw

end RMF
