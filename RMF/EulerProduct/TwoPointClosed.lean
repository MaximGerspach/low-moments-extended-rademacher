/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import RMF.EulerProduct.TwoPoint

/-!
# The Steinhaus two-point local moment in closed form

For `‖w₁‖, ‖w₂‖ < 1`, under the Steinhaus law,

  `E ‖(1 - z w₁)⁻¹‖² ‖(1 - z w₂)⁻¹‖² = (1 - ‖w₁‖²‖w₂‖²) / ((1 - ‖w₁‖²)(1 - ‖w₂‖²)‖1 - w₁ w̄₂‖²)`.

Like its Rademacher analogue, the Steinhaus local moment is thus an identity, and not only an
expansion with a cubic remainder (`RMF.exists_local_two_point_expansion`).  The closed form makes
the remainder quartic and small: `RMF.abs_log_local_two_point_sub_le_quartic` bounds it by `4.1 δ⁴`.

No series is needed.  The mean value property (`DiffContOnCl.circleAverage`) gives
`E (1 - z w)⁻¹ = 1` and `E (1 - z w₁)⁻¹ (1 - z w₂)⁻¹ = 1`, and on the circle two
partial-fraction identities reduce the integrand to those two:

* `(1 - ‖a‖²) ‖(1 - a)⁻¹‖² = 2 Re (1 - a)⁻¹ - 1`, at `a = z w` with `‖z‖ = 1`;
* `(1 - a)⁻¹ (1 - b)⁻¹ = (1 - a b)⁻¹ ((1 - a)⁻¹ + (1 - b)⁻¹ - 1)`, at `a = z w₁`, `b = conj (z w₂)`,
  where `a b = w₁ w̄₂` does not depend on `z`.
-/

open MeasureTheory Complex ComplexConjugate Metric Real

namespace RMF

/-! ### The Steinhaus law against complex integrands -/

/-- **The Steinhaus law is the circle average**, for complex-valued integrands: the analogue of
`RMF.integral_steinhausLaw_eq_circleAverage`, with the same proof. -/
lemma integral_steinhausLaw_eq_circleAverage_complex {g : ℂ → ℂ} (hg : Measurable g) :
    ∫ z, g z ∂steinhausLaw = circleAverage g 0 1 := by
  have hmap : ∀ θ : ℝ, circleMap 0 1 θ = circleAngle θ := by
    intro θ; simp [circleMap, circleAngle]
  have hper : Function.Periodic (fun θ : ℝ => g (circleAngle θ)) (2 * π) := by
    intro θ
    simp only [circleAngle]
    rw [show ((θ + 2 * π : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I + 2 * π * Complex.I by
      push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hshift := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at hshift
  rw [steinhausLaw, integral_smul_measure,
    integral_map measurable_circleAngle.aemeasurable hg.aestronglyMeasurable,
    toReal_steinhaus_const, ← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π),
    hshift, circleAverage]
  simp only [hmap]

/-- `1 - z w` does not vanish on the closed unit disc when `‖w‖ < 1`. -/
lemma one_sub_mul_ne_zero_of_norm_le {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ < 1) :
    1 - z * w ≠ 0 := by
  intro h
  have h1 : z * w = 1 := by linear_combination -h
  have hlt : ‖z * w‖ < 1 := by
    rw [norm_mul]
    calc ‖z‖ * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ = ‖w‖ := one_mul _
      _ < 1 := hw
  rw [h1, norm_one] at hlt
  exact lt_irrefl 1 hlt

/-- On the unit circle, `‖(1 - z w)⁻¹‖ ≤ (1 - ‖w‖)⁻¹`. -/
lemma norm_inv_one_sub_mul_le {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ < 1) :
    ‖(1 - z * w)⁻¹‖ ≤ (1 - ‖w‖)⁻¹ := by
  have hpos : 0 < 1 - ‖w‖ := by linarith
  have hlow : 1 - ‖w‖ ≤ ‖1 - z * w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (z * w)
    rw [norm_one, norm_mul, hz, one_mul] at h
    exact h
  rw [norm_inv]
  exact inv_anti₀ hpos hlow

/-- `z ↦ (1 - z w)⁻¹` is measurable. -/
lemma measurable_inv_one_sub_mul (w : ℂ) : Measurable fun z : ℂ => (1 - z * w)⁻¹ :=
  (measurable_const.sub (measurable_id.mul measurable_const)).inv

/-- `z ↦ (1 - z w)⁻¹` is integrable against the Steinhaus law when `‖w‖ < 1`. -/
lemma integrable_inv_one_sub_mul {w : ℂ} (hw : ‖w‖ < 1) :
    Integrable (fun z : ℂ => (1 - z * w)⁻¹) steinhausLaw := by
  refine (integrable_const ((1 - ‖w‖)⁻¹)).mono'
    (measurable_inv_one_sub_mul w).aestronglyMeasurable ?_
  filter_upwards [norm_eq_one_steinhausLaw] with z hz
  exact norm_inv_one_sub_mul_le hz hw

/-! ### The mean value property -/

/-- `z ↦ (1 - z w)⁻¹` is complex differentiable on the closed unit disc when `‖w‖ < 1`. -/
lemma differentiableOn_inv_one_sub_mul {w : ℂ} (hw : ‖w‖ < 1) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z * w)⁻¹) (closedBall 0 1) := by
  intro z hz
  have hz1 : ‖z‖ ≤ 1 := by simpa using hz
  have hd : DifferentiableAt ℂ (fun z : ℂ => 1 - z * w) z := by fun_prop
  exact (hd.inv (one_sub_mul_ne_zero_of_norm_le hz1 hw)).differentiableWithinAt

/-- **`E (1 - z w)⁻¹ = 1`** under the Steinhaus law, for `‖w‖ < 1`: the mean value property. -/
lemma integral_inv_one_sub_mul_steinhausLaw {w : ℂ} (hw : ‖w‖ < 1) :
    ∫ z, (1 - z * w)⁻¹ ∂steinhausLaw = 1 := by
  rw [integral_steinhausLaw_eq_circleAverage_complex (measurable_inv_one_sub_mul w)]
  have hcl : DiffContOnCl ℂ (fun z : ℂ => (1 - z * w)⁻¹) (ball (0 : ℂ) |1|) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [abs_one, closure_ball (0 : ℂ) one_ne_zero]
    exact differentiableOn_inv_one_sub_mul hw
  rw [hcl.circleAverage]
  simp

/-- **`E (1 - z w₁)⁻¹ (1 - z w₂)⁻¹ = 1`** under the Steinhaus law, for `‖w₁‖, ‖w₂‖ < 1`: the mean
value property again. -/
lemma integral_inv_mul_inv_steinhausLaw {w₁ w₂ : ℂ} (h₁ : ‖w₁‖ < 1) (h₂ : ‖w₂‖ < 1) :
    ∫ z, (1 - z * w₁)⁻¹ * (1 - z * w₂)⁻¹ ∂steinhausLaw = 1 := by
  rw [integral_steinhausLaw_eq_circleAverage_complex
    (show Measurable fun z : ℂ => (1 - z * w₁)⁻¹ * (1 - z * w₂)⁻¹ from
      (measurable_inv_one_sub_mul w₁).mul (measurable_inv_one_sub_mul w₂))]
  have hcl : DiffContOnCl ℂ (fun z : ℂ => (1 - z * w₁)⁻¹ * (1 - z * w₂)⁻¹)
      (ball (0 : ℂ) |1|) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [abs_one, closure_ball (0 : ℂ) one_ne_zero]
    exact (differentiableOn_inv_one_sub_mul h₁).mul (differentiableOn_inv_one_sub_mul h₂)
  rw [hcl.circleAverage]
  simp

/-! ### Two identities on the circle -/

/-- **`‖(1 - a)⁻¹‖²` through its real part**: `(1 - ‖a‖²) ‖(1 - a)⁻¹‖² = 2 Re (1 - a)⁻¹ - 1`. -/
lemma one_sub_sq_norm_mul_sq_norm_inv {a : ℂ} (ha : a ≠ 1) :
    (1 - ‖a‖ ^ 2) * ‖(1 - a)⁻¹‖ ^ 2 = 2 * ((1 - a)⁻¹).re - 1 := by
  have hu : (1 - a) ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have hN : Complex.normSq (1 - a) ≠ 0 := (Complex.normSq_eq_zero (z := 1 - a)).not.2 hu
  have key : 1 - Complex.normSq a = 2 * (1 - a).re - Complex.normSq (1 - a) := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  rw [norm_inv, inv_pow, Complex.sq_norm, Complex.sq_norm, Complex.inv_re, key]
  field_simp

/-- **Partial fractions**: `(1 - a)⁻¹ (1 - b)⁻¹ = (1 - a b)⁻¹ ((1 - a)⁻¹ + (1 - b)⁻¹ - 1)`. -/
lemma inv_one_sub_mul_inv_one_sub {a b : ℂ} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a * b ≠ 1) :
    (1 - a)⁻¹ * (1 - b)⁻¹ = (1 - a * b)⁻¹ * ((1 - a)⁻¹ + (1 - b)⁻¹ - 1) := by
  have h1 : (1 - a) ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have h2 : (1 - b) ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
  have h3 : (1 - a * b) ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  field_simp
  ring

/-- `a ≠ 1` whenever `‖a‖ < 1`. -/
lemma ne_one_of_norm_lt_one {a : ℂ} (ha : ‖a‖ < 1) : a ≠ 1 := by
  rintro rfl
  simp at ha

/-- **The cross moment**: `E (1 - z w₁)⁻¹ conj (1 - z w₂)⁻¹ = (1 - w₁ w̄₂)⁻¹`. -/
lemma integral_inv_mul_conj_inv_steinhausLaw {w₁ w₂ : ℂ} (h₁ : ‖w₁‖ < 1) (h₂ : ‖w₂‖ < 1) :
    ∫ z, (1 - z * w₁)⁻¹ * conj (1 - z * w₂)⁻¹ ∂steinhausLaw = (1 - w₁ * conj w₂)⁻¹ := by
  have hv : ‖w₁ * conj w₂‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg w₁, norm_nonneg w₂]
  have hae : ∀ᵐ z ∂steinhausLaw, (1 - z * w₁)⁻¹ * conj (1 - z * w₂)⁻¹
      = (1 - w₁ * conj w₂)⁻¹ * ((1 - z * w₁)⁻¹ + conj (1 - z * w₂)⁻¹ - 1) := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    have hzw₁ : ‖z * w₁‖ < 1 := by rw [norm_mul, hz, one_mul]; exact h₁
    have hzw₂ : ‖conj (z * w₂)‖ < 1 := by rw [Complex.norm_conj, norm_mul, hz, one_mul]; exact h₂
    have hprod : z * w₁ * conj (z * w₂) = w₁ * conj w₂ := by
      have hzz : z * conj z = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
        norm_num
      rw [map_mul]
      linear_combination (w₁ * conj w₂) * hzz
    have key := inv_one_sub_mul_inv_one_sub (ne_one_of_norm_lt_one hzw₁)
      (ne_one_of_norm_lt_one hzw₂) (by rw [hprod]; exact ne_one_of_norm_lt_one hv)
    rw [hprod] at key
    rw [map_inv₀, map_sub, map_one]
    exact key
  rw [integral_congr_ae hae, integral_const_mul]
  have hi₁ := integrable_inv_one_sub_mul h₁
  have hi₂ : Integrable (fun z : ℂ => conj (1 - z * w₂)⁻¹) steinhausLaw := by
    refine (integrable_const ((1 - ‖w₂‖)⁻¹)).mono'
      (Complex.continuous_conj.measurable.comp
        (measurable_inv_one_sub_mul w₂)).aestronglyMeasurable ?_
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    rw [Complex.norm_conj]
    exact norm_inv_one_sub_mul_le hz h₂
  have hsum : Integrable (fun z : ℂ => (1 - z * w₁)⁻¹ + conj (1 - z * w₂)⁻¹) steinhausLaw :=
    hi₁.add hi₂
  rw [integral_sub hsum (integrable_const _), integral_add hi₁ hi₂, integral_conj,
    integral_inv_one_sub_mul_steinhausLaw h₁, integral_inv_one_sub_mul_steinhausLaw h₂]
  simp

/-! ### The closed form -/

/-- **The Steinhaus two-point local moment in closed form.** -/
theorem integral_local_two_point_eq {w₁ w₂ : ℂ} (h₁ : ‖w₁‖ < 1) (h₂ : ‖w₂‖ < 1) :
    ∫ z, ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2 ∂steinhausLaw
      = (1 - ‖w₁‖ ^ 2 * ‖w₂‖ ^ 2)
          / ((1 - ‖w₁‖ ^ 2) * (1 - ‖w₂‖ ^ 2) * ‖1 - w₁ * conj w₂‖ ^ 2) := by
  set g₁ : ℂ → ℂ := fun z => (1 - z * w₁)⁻¹ with hg₁
  set g₂ : ℂ → ℂ := fun z => (1 - z * w₂)⁻¹ with hg₂
  set v : ℂ := w₁ * conj w₂ with hvdef
  have hv : ‖v‖ < 1 := by
    rw [hvdef, norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg w₁, norm_nonneg w₂]
  have hc₁ : 0 < 1 - ‖w₁‖ ^ 2 := by nlinarith [norm_nonneg w₁]
  have hc₂ : 0 < 1 - ‖w₂‖ ^ 2 := by nlinarith [norm_nonneg w₂]
  -- the integrand, on the circle, as a combination of real parts
  have hae : ∀ᵐ z ∂steinhausLaw, ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2
      = (1 - ‖w₁‖ ^ 2)⁻¹ * (1 - ‖w₂‖ ^ 2)⁻¹
          * (2 * (g₁ z * g₂ z).re + 2 * (g₁ z * conj (g₂ z)).re
              - 2 * (g₁ z).re - 2 * (g₂ z).re + 1) := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    have hzw₁ : ‖z * w₁‖ < 1 := by rw [norm_mul, hz, one_mul]; exact h₁
    have hzw₂ : ‖z * w₂‖ < 1 := by rw [norm_mul, hz, one_mul]; exact h₂
    have e₁ := one_sub_sq_norm_mul_sq_norm_inv (ne_one_of_norm_lt_one hzw₁)
    have e₂ := one_sub_sq_norm_mul_sq_norm_inv (ne_one_of_norm_lt_one hzw₂)
    rw [norm_mul, hz, one_mul] at e₁ e₂
    have hsq₁ : ‖(1 - z * w₁)⁻¹‖ ^ 2 = (1 - ‖w₁‖ ^ 2)⁻¹ * (2 * (g₁ z).re - 1) := by
      rw [← e₁]; field_simp
    have hsq₂ : ‖(1 - z * w₂)⁻¹‖ ^ 2 = (1 - ‖w₂‖ ^ 2)⁻¹ * (2 * (g₂ z).re - 1) := by
      rw [← e₂]; field_simp
    rw [hsq₁, hsq₂]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  -- the four integrals
  have hi₁ := integrable_inv_one_sub_mul h₁
  have hi₂ := integrable_inv_one_sub_mul h₂
  have hbnd : ∀ {w : ℂ}, ‖w‖ < 1 → ∀ᵐ z ∂steinhausLaw, ‖(1 - z * w)⁻¹‖ ≤ (1 - ‖w‖)⁻¹ :=
    fun hw => by
      filter_upwards [norm_eq_one_steinhausLaw] with z hz
      exact norm_inv_one_sub_mul_le hz hw
  have hi₁₂ : Integrable (fun z => g₁ z * g₂ z) steinhausLaw := by
    refine (integrable_const ((1 - ‖w₁‖)⁻¹ * (1 - ‖w₂‖)⁻¹)).mono'
      ((measurable_inv_one_sub_mul w₁).mul (measurable_inv_one_sub_mul w₂)).aestronglyMeasurable
      ?_
    filter_upwards [hbnd h₁, hbnd h₂] with z hz₁ hz₂
    rw [norm_mul]
    exact mul_le_mul hz₁ hz₂ (norm_nonneg _) (by have := norm_nonneg w₁; positivity)
  have hi₁₂' : Integrable (fun z => g₁ z * conj (g₂ z)) steinhausLaw := by
    refine (integrable_const ((1 - ‖w₁‖)⁻¹ * (1 - ‖w₂‖)⁻¹)).mono'
      ((measurable_inv_one_sub_mul w₁).mul
        (Complex.continuous_conj.measurable.comp
          (measurable_inv_one_sub_mul w₂))).aestronglyMeasurable ?_
    filter_upwards [hbnd h₁, hbnd h₂] with z hz₁ hz₂
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hz₁ hz₂ (norm_nonneg _) (by have := norm_nonneg w₁; positivity)
  have I₁₂ : ∫ z, (g₁ z * g₂ z).re ∂steinhausLaw = 1 := by
    have hre := integral_re hi₁₂
    simp only [RCLike.re_to_complex] at hre
    rw [hre]
    simp only [hg₁, hg₂]
    rw [integral_inv_mul_inv_steinhausLaw h₁ h₂, Complex.one_re]
  have I₁₂' : ∫ z, (g₁ z * conj (g₂ z)).re ∂steinhausLaw = ((1 - v)⁻¹).re := by
    have hre := integral_re hi₁₂'
    simp only [RCLike.re_to_complex] at hre
    rw [hre]
    simp only [hg₁, hg₂]
    rw [integral_inv_mul_conj_inv_steinhausLaw h₁ h₂]
  have I₁ : ∫ z, (g₁ z).re ∂steinhausLaw = 1 := by
    have hre := integral_re hi₁
    simp only [RCLike.re_to_complex] at hre
    rw [hre]
    rw [integral_inv_one_sub_mul_steinhausLaw h₁, Complex.one_re]
  have I₂ : ∫ z, (g₂ z).re ∂steinhausLaw = 1 := by
    have hre := integral_re hi₂
    simp only [RCLike.re_to_complex] at hre
    rw [hre]
    rw [integral_inv_one_sub_mul_steinhausLaw h₂, Complex.one_re]
  have hr₁₂ : Integrable (fun z => (g₁ z * g₂ z).re) steinhausLaw := hi₁₂.re
  have hr₁₂' : Integrable (fun z => (g₁ z * conj (g₂ z)).re) steinhausLaw := hi₁₂'.re
  have hr₁ : Integrable (fun z => (g₁ z).re) steinhausLaw := hi₁.re
  have hr₂ : Integrable (fun z => (g₂ z).re) steinhausLaw := hi₂.re
  rw [integral_congr_ae hae, integral_const_mul]
  have hlin : ∫ z, (2 * (g₁ z * g₂ z).re + 2 * (g₁ z * conj (g₂ z)).re
        - 2 * (g₁ z).re - 2 * (g₂ z).re + 1) ∂steinhausLaw
      = 2 * ((1 - v)⁻¹).re - 1 := by
    rw [integral_add, integral_sub, integral_sub, integral_add, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul, I₁₂, I₁₂', I₁, I₂]
    · simp
      ring
    all_goals first
      | exact (hr₁₂.const_mul 2)
      | exact (hr₁₂'.const_mul 2)
      | exact (hr₁.const_mul 2)
      | exact (hr₂.const_mul 2)
      | exact integrable_const _
      | exact (hr₁₂.const_mul 2).add (hr₁₂'.const_mul 2)
      | exact ((hr₁₂.const_mul 2).add (hr₁₂'.const_mul 2)).sub (hr₁.const_mul 2)
      | exact (((hr₁₂.const_mul 2).add (hr₁₂'.const_mul 2)).sub (hr₁.const_mul 2)).sub
          (hr₂.const_mul 2)
  rw [hlin]
  -- `2 Re (1 - v)⁻¹ - 1 = (1 - ‖v‖²)‖(1 - v)⁻¹‖²`, and `‖v‖ = ‖w₁‖‖w₂‖`
  have ev := one_sub_sq_norm_mul_sq_norm_inv (ne_one_of_norm_lt_one hv)
  rw [← ev]
  have hnv : ‖v‖ ^ 2 = ‖w₁‖ ^ 2 * ‖w₂‖ ^ 2 := by
    rw [hvdef, norm_mul, Complex.norm_conj]; ring
  have h1v : ‖1 - v‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact sub_ne_zero.2 (Ne.symm (ne_one_of_norm_lt_one hv))
  rw [hnv, norm_inv, inv_pow]
  field_simp

/-! ### The remainder is quartic -/

/-- `|log (1 - x)| ≤ 1.021 x` for `0 ≤ x ≤ 1/50`. -/
lemma abs_log_one_sub_le_of_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 50) :
    |Real.log (1 - x)| ≤ 1.021 * x := by
  have h := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx0]; linarith) 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_one, abs_of_nonneg hx0] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `|log (1 - x) + x| ≤ 1.021 x²` for `0 ≤ x ≤ 1/50`. -/
lemma abs_log_one_sub_add_le_of_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 50) :
    |Real.log (1 - x) + x| ≤ 1.021 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx0]; linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, abs_of_nonneg hx0] at h
  rw [add_comm]
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg x]

/-- `|Re log (1 - v) + Re v| ≤ 0.511 ‖v‖²` for `‖v‖ ≤ 1/50`. -/
lemma abs_re_log_one_sub_add_le {v : ℂ} (hv : ‖v‖ ≤ 1 / 50) :
    |(Complex.log (1 - v)).re + v.re| ≤ 0.511 * ‖v‖ ^ 2 := by
  have hv1 : ‖-v‖ < 1 := by rw [norm_neg]; linarith
  have h := Complex.norm_log_one_add_sub_self_le hv1
  rw [norm_neg, ← sub_eq_add_neg, sub_neg_eq_add] at h
  have hre : |(Complex.log (1 - v)).re + v.re| ≤ ‖Complex.log (1 - v) + v‖ := by
    rw [← Complex.add_re]
    exact Complex.abs_re_le_norm _
  refine hre.trans (h.trans ?_)
  have hpos : 0 < 1 - ‖v‖ := by linarith
  have hinv : (1 - ‖v‖)⁻¹ ≤ 50 / 49 := by
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  have hsq : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  calc ‖v‖ ^ 2 * (1 - ‖v‖)⁻¹ / 2 ≤ ‖v‖ ^ 2 * (50 / 49) / 2 := by gcongr
    _ ≤ 0.511 * ‖v‖ ^ 2 := by nlinarith

/-- **The two-point remainder is quartic**: `|log E − ‖w₁ + w₂‖²| ≤ 4.1 δ⁴` when
`‖w₁‖, ‖w₂‖ ≤ δ ≤ 0.136`, `E` the Steinhaus two-point local moment. -/
theorem abs_log_local_two_point_sub_le_quartic {w₁ w₂ : ℂ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 0.136) (h₁ : ‖w₁‖ ≤ δ) (h₂ : ‖w₂‖ ≤ δ) :
    |Real.log (∫ z, ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2 ∂steinhausLaw)
        - ‖w₁ + w₂‖ ^ 2| ≤ 4.1 * δ ^ 4 := by
  have hδ2 : δ ^ 2 ≤ 1 / 50 := by
    calc δ ^ 2 ≤ 0.136 ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
      _ ≤ 1 / 50 := by norm_num
  have hδ4 : δ ^ 4 ≤ 1 / 50 := by
    calc δ ^ 4 = (δ ^ 2) ^ 2 := by ring
      _ ≤ (1 / 50) ^ 2 := pow_le_pow_left₀ (sq_nonneg δ) hδ2 2
      _ ≤ 1 / 50 := by norm_num
  have h4pos : 0 ≤ δ ^ 4 := by positivity
  have hn₁ : ‖w₁‖ < 1 := by linarith
  have hn₂ : ‖w₂‖ < 1 := by linarith
  have hu₁δ : ‖w₁‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  have hu₂δ : ‖w₂‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
  have hvn : ‖w₁ * conj w₂‖ = ‖w₁‖ * ‖w₂‖ := by rw [norm_mul, Complex.norm_conj]
  have hvδ : ‖w₁ * conj w₂‖ ≤ δ ^ 2 := by
    rw [hvn]
    calc ‖w₁‖ * ‖w₂‖ ≤ δ * δ := mul_le_mul h₁ h₂ (norm_nonneg _) hδ0
      _ = δ ^ 2 := by ring
  have hv1 : ‖w₁ * conj w₂‖ < 1 := by linarith
  rw [integral_local_two_point_eq hn₁ hn₂]
  set u₁ := ‖w₁‖ ^ 2 with hu₁
  set u₂ := ‖w₂‖ ^ 2 with hu₂
  set v := w₁ * conj w₂ with hvdef
  have hu₁0 : 0 ≤ u₁ := by positivity
  have hu₂0 : 0 ≤ u₂ := by positivity
  have hs0 : 0 ≤ u₁ * u₂ := mul_nonneg hu₁0 hu₂0
  have hsδ : u₁ * u₂ ≤ δ ^ 4 := by
    calc u₁ * u₂ ≤ δ ^ 2 * δ ^ 2 := mul_le_mul hu₁δ hu₂δ hu₂0 (sq_nonneg δ)
      _ = δ ^ 4 := by ring
  have hs1 : 0 < 1 - u₁ * u₂ := by linarith
  have h1u₁ : 0 < 1 - u₁ := by linarith
  have h1u₂ : 0 < 1 - u₂ := by linarith
  have h1v : 0 < ‖1 - v‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm (ne_one_of_norm_lt_one hv1)))
  -- the logarithm of the closed form, and the main term
  have hlogA : Real.log ((1 - u₁ * u₂) / ((1 - u₁) * (1 - u₂) * ‖1 - v‖ ^ 2))
      = Real.log (1 - u₁ * u₂) - Real.log (1 - u₁) - Real.log (1 - u₂)
          - 2 * (Complex.log (1 - v)).re := by
    rw [Real.log_div hs1.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul h1u₁.ne' h1u₂.ne', Real.log_pow, Complex.log_re]
    push_cast
    ring
  have hM : ‖w₁ + w₂‖ ^ 2 = u₁ + u₂ + 2 * v.re := by
    rw [Complex.sq_norm, Complex.normSq_add, hu₁, hu₂, Complex.sq_norm, Complex.sq_norm]
  rw [hlogA, hM]
  have e1 := abs_log_one_sub_le_of_le hs0 (by linarith)
  have e2 := abs_log_one_sub_add_le_of_le hu₁0 (by linarith)
  have e3 := abs_log_one_sub_add_le_of_le hu₂0 (by linarith)
  have e4 := abs_re_log_one_sub_add_le (v := v) (by linarith)
  have hu₁sq : u₁ ^ 2 ≤ δ ^ 4 := by
    calc u₁ ^ 2 ≤ (δ ^ 2) ^ 2 := pow_le_pow_left₀ hu₁0 hu₁δ 2
      _ = δ ^ 4 := by ring
  have hu₂sq : u₂ ^ 2 ≤ δ ^ 4 := by
    calc u₂ ^ 2 ≤ (δ ^ 2) ^ 2 := pow_le_pow_left₀ hu₂0 hu₂δ 2
      _ = δ ^ 4 := by ring
  have hvsq : ‖v‖ ^ 2 ≤ δ ^ 4 := by
    calc ‖v‖ ^ 2 ≤ (δ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hvδ 2
      _ = δ ^ 4 := by ring
  have hsplit : Real.log (1 - u₁ * u₂) - Real.log (1 - u₁) - Real.log (1 - u₂)
        - 2 * (Complex.log (1 - v)).re - (u₁ + u₂ + 2 * v.re)
      = Real.log (1 - u₁ * u₂) - (Real.log (1 - u₁) + u₁) - (Real.log (1 - u₂) + u₂)
          - 2 * ((Complex.log (1 - v)).re + v.re) := by ring
  rw [hsplit]
  have htri : |Real.log (1 - u₁ * u₂) - (Real.log (1 - u₁) + u₁) - (Real.log (1 - u₂) + u₂)
        - 2 * ((Complex.log (1 - v)).re + v.re)|
      ≤ |Real.log (1 - u₁ * u₂)| + |Real.log (1 - u₁) + u₁| + |Real.log (1 - u₂) + u₂|
          + 2 * |(Complex.log (1 - v)).re + v.re| := by
    have h2 : |2 * ((Complex.log (1 - v)).re + v.re)|
        = 2 * |(Complex.log (1 - v)).re + v.re| := by
      rw [abs_mul, abs_two]
    calc _ ≤ |Real.log (1 - u₁ * u₂) - (Real.log (1 - u₁) + u₁) - (Real.log (1 - u₂) + u₂)|
          + |2 * ((Complex.log (1 - v)).re + v.re)| := abs_sub _ _
      _ ≤ |Real.log (1 - u₁ * u₂) - (Real.log (1 - u₁) + u₁)| + |Real.log (1 - u₂) + u₂|
          + |2 * ((Complex.log (1 - v)).re + v.re)| := by gcongr; exact abs_sub _ _
      _ ≤ |Real.log (1 - u₁ * u₂)| + |Real.log (1 - u₁) + u₁| + |Real.log (1 - u₂) + u₂|
          + |2 * ((Complex.log (1 - v)).re + v.re)| := by gcongr; exact abs_sub _ _
      _ = _ := by rw [h2]
  refine htri.trans ?_
  linarith [e1, e2, e3, e4, hsδ, hu₁sq, hu₂sq, hvsq, h4pos]

/-- **The quartic remainder in the cubic shape** the per-prime estimates consume:
`4.1 δ⁴ ≤ 0.56 δ³` for `δ ≤ 0.136`. -/
theorem abs_log_local_two_point_sub_le_closed {w₁ w₂ : ℂ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 0.136) (h₁ : ‖w₁‖ ≤ δ) (h₂ : ‖w₂‖ ≤ δ) :
    |Real.log (∫ z, ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2 ∂steinhausLaw)
        - ‖w₁ + w₂‖ ^ 2| ≤ 0.56 * δ ^ 3 := by
  refine (abs_log_local_two_point_sub_le_quartic hδ0 hδ h₁ h₂).trans ?_
  have h3 : 0 ≤ δ ^ 3 := by positivity
  calc 4.1 * δ ^ 4 = (4.1 * δ) * δ ^ 3 := by ring
    _ ≤ (4.1 * 0.136) * δ ^ 3 := by gcongr
    _ ≤ 0.56 * δ ^ 3 := by gcongr; norm_num

end RMF
