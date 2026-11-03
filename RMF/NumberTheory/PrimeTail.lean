/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.CosinePrimeSum

/-!
# The prime tail `∑_{p > x} p ^ (-3/2)`

`∑_{x < p ≤ y} p ^ (-3/2) ≤ C / (√x log x)`, uniformly in `y ≥ x ≥ 2`.

This is the "standard Chebyshev-type estimate" inside the proof of Harper's Lemma 1, and it is
what gives that lemma's error term `(1 + |u| ^ 3) / (√x log x)` its saving in `x`.  The saving
matters: the third absolute moments of the local terms over a block of primes are of exactly this
size, so this bound is what makes the Gaussian comparison quantitative.

## The argument

Abel summation, as in `RMF/NumberTheory/CosinePrimeSum.lean`, but over a *tail*: with
`h t = t ^ (-3/2) / log t`, so that `log p · h p = p ^ (-3/2)`, and `θ t = ∑_{p ≤ t} log p`,

`∑_{x < p ≤ y} p ^ (-3/2) = h y · θ y - h x · θ x - ∫_x^y h' t · θ t dt`.

Chebyshev's `θ t ≤ log 4 · t` then bounds all three terms by a multiple of `1 / (√x log x)`: the
two boundary terms directly, and the integral because `|h' t| ≤ 3 · t ^ (-5/2) / log t`, so its
integrand is at most `3 log 4 · t ^ (-3/2) / log t`.

The input is Chebyshev's bound, not the prime number theorem — `Chebyshev.theta_le_log4_mul_x`
is in Mathlib.  The two-endpoint Abel formula `sum_mul_eq_sub_sub_integral_mul` is what the
head-sum file cannot supply: its `RMF.cos_prime_sum_eq` uses the one-endpoint version, which sums
from the origin.

## On the constant

`8 log 4 ≈ 11.09`, against a true value near `1.5`.  Nothing downstream is sensitive to it.
-/

open Filter MeasureTheory

namespace RMF

/-! ### The kernel and its derivative -/

/-- The Abel kernel for the tail: `h t = t ^ (-3/2) / log t`, chosen so that `log p · h p` is
the term `p ^ (-3/2)` of the prime tail. -/
noncomputable def rpowLogDiv (t : ℝ) : ℝ := t ^ (-(3 / 2) : ℝ) / Real.log t

lemma rpowLogDiv_nonneg {t : ℝ} (ht : 2 ≤ t) : 0 ≤ rpowLogDiv t := by
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have h : (0 : ℝ) < t ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  exact div_nonneg h.le hlog.le

/-- `t ^ (-3/2) · t⁻¹ = t ^ (-5/2)`, the `rpow` identity the quotient rule needs. -/
lemma rpow_neg_three_halves_mul_inv {t : ℝ} (ht : 0 < t) :
    t ^ (-(3 / 2) : ℝ) * t⁻¹ = t ^ (-(5 / 2) : ℝ) := by
  rw [← Real.rpow_neg_one t, ← Real.rpow_add ht]
  norm_num

/-- `t ^ (-3/2) · t = (√t)⁻¹`, the identity the boundary terms need. -/
lemma rpow_neg_three_halves_mul_self {t : ℝ} (ht : 0 < t) :
    t ^ (-(3 / 2) : ℝ) * t = (Real.sqrt t)⁻¹ := by
  have h1 : t ^ (-(3 / 2) : ℝ) * t ^ (1 : ℝ) = t ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add ht]; norm_num
  rw [Real.rpow_one] at h1
  rw [h1, Real.rpow_neg ht.le, Real.sqrt_eq_rpow]

/-- The derivative of `h`, by the quotient rule. -/
lemma hasDerivAt_rpowLogDiv {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt rpowLogDiv
      ((-(3 / 2) * t ^ (-(5 / 2) : ℝ) * Real.log t - t ^ (-(5 / 2) : ℝ)) / Real.log t ^ 2) t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hf : HasDerivAt (fun u : ℝ => u ^ (-(3 / 2) : ℝ))
      (-(3 / 2) * t ^ (-(3 / 2) - 1 : ℝ)) t := Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
  have hg : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0.ne'
  refine (hf.div hg hlog).congr_deriv ?_
  rw [show (-(3 / 2) - 1 : ℝ) = -(5 / 2) by norm_num, rpow_neg_three_halves_mul_inv ht0]

lemma differentiableAt_rpowLogDiv {t : ℝ} (ht : 2 ≤ t) :
    DifferentiableAt ℝ rpowLogDiv t := (hasDerivAt_rpowLogDiv ht).differentiableAt

/-- **The derivative bound.**  `|h' t| ≤ 3 · t ^ (-5/2) / log t` for `t ≥ 2`.  The `3` absorbs
`3/2 + 1 / log 2 = 2.943`; concretely it uses `1 ≤ (3/2) log t`, which holds because
`(3/2) log 2 = 1.0397`. -/
lemma abs_deriv_rpowLogDiv_le {t : ℝ} (ht : 2 ≤ t) :
    |deriv rpowLogDiv t| ≤ 3 * t ^ (-(5 / 2) : ℝ) / Real.log t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have hlow : (0.6931471803 : ℝ) < Real.log t :=
    lt_of_lt_of_le Real.log_two_gt_d9 (Real.log_le_log (by norm_num) ht)
  have hr : (0 : ℝ) < t ^ (-(5 / 2) : ℝ) := Real.rpow_pos_of_pos ht0 _
  rw [(hasDerivAt_rpowLogDiv ht).deriv, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < Real.log t ^ 2), div_le_div_iff₀ (by positivity) hlog]
  have hnum : |(-(3 / 2) * t ^ (-(5 / 2) : ℝ) * Real.log t - t ^ (-(5 / 2) : ℝ))|
      = t ^ (-(5 / 2) : ℝ) * (3 / 2 * Real.log t + 1) := by
    rw [abs_of_nonpos (by nlinarith)]
    ring
  rw [hnum]
  nlinarith [mul_pos hr hlog, hr.le]

/-! ### Abel summation over a tail -/

lemma continuousOn_deriv_rpowLogDiv {x y : ℝ} (hx : 2 ≤ x) :
    ContinuousOn (deriv rpowLogDiv) (Set.Icc x y) := by
  have hform : Set.EqOn (deriv rpowLogDiv)
      (fun t => (-(3 / 2) * t ^ (-(5 / 2) : ℝ) * Real.log t - t ^ (-(5 / 2) : ℝ))
        / Real.log t ^ 2) (Set.Icc x y) :=
    fun t ht => (hasDerivAt_rpowLogDiv (hx.trans ht.1)).deriv
  refine ContinuousOn.congr ?_ hform
  have hlog : ContinuousOn Real.log (Set.Icc x y) :=
    continuousOn_log_Icc (a := x) (b := y) (by linarith)
  have hrpow : ContinuousOn (fun t : ℝ => t ^ (-(5 / 2) : ℝ)) (Set.Icc x y) :=
    ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (by linarith [ht.1] : t ≠ 0)
  refine ContinuousOn.div (((continuousOn_const.mul hrpow).mul hlog).sub hrpow) (hlog.pow 2)
    fun t ht => pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne'

lemma integrableOn_deriv_rpowLogDiv {x y : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (deriv rpowLogDiv) (Set.Icc x y) :=
  (continuousOn_deriv_rpowLogDiv hx).integrableOn_Icc

/-- **Abel summation for the prime tail.**  The two-endpoint formula against `RMF.primeLog`,
whose partial sums are `Chebyshev.theta` (`RMF.sum_primeLog_eq_theta`). -/
theorem sum_prime_Ioc_rpow_eq {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (p : ℝ) ^ (-(3 / 2) : ℝ)
      = rpowLogDiv y * Chebyshev.theta y - rpowLogDiv x * Chebyshev.theta x
        - ∫ t in Set.Ioc x y, deriv rpowLogDiv t * Chebyshev.theta t := by
  have habel := sum_mul_eq_sub_sub_integral_mul (c := primeLog) (f := rpowLogDiv)
    (by linarith : (0 : ℝ) ≤ x) hxy (fun t ht => differentiableAt_rpowLogDiv (hx.trans ht.1))
    (integrableOn_deriv_rpowLogDiv hx)
  simp_rw [sum_primeLog_eq_theta] at habel
  rw [← habel, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hp : k.Prime
  · have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hp.two_le
    have hlog : Real.log k ≠ 0 := (Real.log_pos (by linarith)).ne'
    rw [if_pos hp, primeLog, if_pos hp, rpowLogDiv]
    field_simp
  · rw [if_neg hp, primeLog, if_neg hp, mul_zero]

/-! ### The three terms -/

/-- The two boundary terms: `h t · θ t ≤ log 4 / (√t log t)`. -/
lemma rpowLogDiv_mul_theta_le {t : ℝ} (ht : 2 ≤ t) :
    rpowLogDiv t * Chebyshev.theta t ≤ Real.log 4 / (Real.sqrt t * Real.log t) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  calc rpowLogDiv t * Chebyshev.theta t
      ≤ rpowLogDiv t * (Real.log 4 * t) :=
        mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x ht0.le) (rpowLogDiv_nonneg ht)
    _ = Real.log 4 / (Real.sqrt t * Real.log t) := by
        rw [rpowLogDiv, div_mul_eq_mul_div, mul_comm (Real.log 4) t, ← mul_assoc,
          rpow_neg_three_halves_mul_self ht0]
        field_simp

/-- `1 / (√t log t)` is decreasing on `[2, ∞)`. -/
lemma one_div_sqrt_mul_log_antitone {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    Real.log 4 / (Real.sqrt y * Real.log y) ≤ Real.log 4 / (Real.sqrt x * Real.log x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hly : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hsy : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  exact div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) (by positivity)
    (mul_le_mul hsy hly hlx.le (by positivity))

/-- `∫_x^y t ^ (-3/2) dt ≤ 2 / √x`, uniformly in `y`. -/
lemma integral_rpow_neg_three_halves_le {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    (∫ t in x..y, t ^ (-(3 / 2) : ℝ)) ≤ 2 / Real.sqrt x := by
  have hderiv : ∀ t ∈ Set.uIcc x y,
      HasDerivAt (fun u : ℝ => -2 * u ^ (-(1 / 2) : ℝ)) (t ^ (-(3 / 2) : ℝ)) t := by
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    refine ((Real.hasDerivAt_rpow_const (p := (-(1 / 2) : ℝ)) (Or.inl ht0.ne')).const_mul
      (-2 : ℝ)).congr_deriv ?_
    rw [show (-(1 / 2) - 1 : ℝ) = -(3 / 2) by norm_num]
    ring
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (-(3 / 2) : ℝ)) volume x y := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hxy]
    exact ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (by linarith [ht.1] : t ≠ 0)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hxe : x ^ (-(1 / 2) : ℝ) = (Real.sqrt x)⁻¹ := by
    rw [Real.rpow_neg hx0.le, Real.sqrt_eq_rpow]
  have hye : (0 : ℝ) ≤ y ^ (-(1 / 2) : ℝ) := (Real.rpow_pos_of_pos hy0 _).le
  rw [hxe]
  have : (2 : ℝ) / Real.sqrt x = 2 * (Real.sqrt x)⁻¹ := by rw [div_eq_mul_inv]
  linarith [this]

/-! ### The tail bound -/

/-- **The prime tail.**  `∑_{x < p ≤ y} p ^ (-3/2) ≤ 8 log 4 / (√x log x)` for `2 ≤ x ≤ y`, the
bound uniform in `y`.  The input is Chebyshev's `θ x ≤ log 4 · x`, not the prime number
theorem. -/
theorem sum_prime_Ioc_rpow_le {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (p : ℝ) ^ (-(3 / 2) : ℝ)
      ≤ 8 * Real.log 4 / (Real.sqrt x * Real.log x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  -- a uniform bound on the derivative, for integrability
  have hIcc : IntegrableOn (fun t => deriv rpowLogDiv t * Chebyshev.theta t) (Set.Icc x y) := by
    have hmeas : AEStronglyMeasurable (fun t => deriv rpowLogDiv t * Chebyshev.theta t)
        (volume.restrict (Set.Icc x y)) :=
      ((continuousOn_deriv_rpowLogDiv hx).aestronglyMeasurable measurableSet_Icc).mul
        (Chebyshev.theta_mono.measurable.aestronglyMeasurable.restrict)
    refine MeasureTheory.Integrable.mono'
      (g := fun _ : ℝ => 3 * x ^ (-(5 / 2) : ℝ) / Real.log x * (Real.log 4 * y))
      (integrable_const _) hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    have ht2 : 2 ≤ t := hx.trans ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    have hltx : Real.log x ≤ Real.log t := Real.log_le_log hx0 ht.1
    have hrt : t ^ (-(5 / 2) : ℝ) ≤ x ^ (-(5 / 2) : ℝ) := by
      rw [Real.rpow_neg ht0.le, Real.rpow_neg hx0.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hx0 _)
        (Real.rpow_le_rpow hx0.le ht.1 (by norm_num))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Chebyshev.theta_nonneg t)]
    calc |deriv rpowLogDiv t| * Chebyshev.theta t
        ≤ 3 * t ^ (-(5 / 2) : ℝ) / Real.log t * (Real.log 4 * t) :=
          mul_le_mul (abs_deriv_rpowLogDiv_le ht2) (Chebyshev.theta_le_log4_mul_x ht0.le)
            (Chebyshev.theta_nonneg t) (by positivity)
      _ ≤ 3 * x ^ (-(5 / 2) : ℝ) / Real.log x * (Real.log 4 * y) := by
          have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          gcongr
          exact ht.2
  have hint1 : IntervalIntegrable (fun t => deriv rpowLogDiv t * Chebyshev.theta t) volume x y := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxy]
    exact hIcc.mono_set Set.Ioc_subset_Icc_self
  have hint2 : IntervalIntegrable
      (fun t : ℝ => 3 * Real.log 4 / Real.log x * t ^ (-(3 / 2) : ℝ)) volume x y := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hxy]
    exact continuousOn_const.mul
      (ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (by linarith [ht.1] : t ≠ 0))
  -- the integral term
  have hbound : ∀ t ∈ Set.Icc x y, |deriv rpowLogDiv t * Chebyshev.theta t|
      ≤ 3 * Real.log 4 / Real.log x * t ^ (-(3 / 2) : ℝ) := by
    intro t ht
    have ht2 : 2 ≤ t := hx.trans ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    have hltx : Real.log x ≤ Real.log t := Real.log_le_log hx0 ht.1
    rw [abs_mul, abs_of_nonneg (Chebyshev.theta_nonneg t)]
    calc |deriv rpowLogDiv t| * Chebyshev.theta t
        ≤ 3 * t ^ (-(5 / 2) : ℝ) / Real.log t * (Real.log 4 * t) :=
          mul_le_mul (abs_deriv_rpowLogDiv_le ht2) (Chebyshev.theta_le_log4_mul_x ht0.le)
            (Chebyshev.theta_nonneg t) (by positivity)
      _ = 3 * Real.log 4 / Real.log t * t ^ (-(3 / 2) : ℝ) := by
          rw [show (-(3 / 2) : ℝ) = -(5 / 2) + 1 by norm_num, Real.rpow_add ht0, Real.rpow_one]
          field_simp
      _ ≤ 3 * Real.log 4 / Real.log x * t ^ (-(3 / 2) : ℝ) := by
          have : (0 : ℝ) < t ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos ht0 _
          have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          gcongr
  have habs : |∫ t in x..y, deriv rpowLogDiv t * Chebyshev.theta t|
      ≤ 6 * Real.log 4 / (Real.sqrt x * Real.log x) := by
    calc |∫ t in x..y, deriv rpowLogDiv t * Chebyshev.theta t|
        ≤ ∫ t in x..y, |deriv rpowLogDiv t * Chebyshev.theta t| :=
          intervalIntegral.abs_integral_le_integral_abs hxy
      _ ≤ ∫ t in x..y, 3 * Real.log 4 / Real.log x * t ^ (-(3 / 2) : ℝ) :=
          intervalIntegral.integral_mono_on hxy hint1.abs hint2 hbound
      _ = 3 * Real.log 4 / Real.log x * ∫ t in x..y, t ^ (-(3 / 2) : ℝ) :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ 3 * Real.log 4 / Real.log x * (2 / Real.sqrt x) := by
          have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          gcongr
          exact integral_rpow_neg_three_halves_le hx hxy
      _ = 6 * Real.log 4 / (Real.sqrt x * Real.log x) := by field_simp; ring
  -- assemble
  rw [sum_prime_Ioc_rpow_eq hx hxy, ← intervalIntegral.integral_of_le hxy]
  have hby : rpowLogDiv y * Chebyshev.theta y ≤ Real.log 4 / (Real.sqrt x * Real.log x) :=
    (rpowLogDiv_mul_theta_le (hx.trans hxy)).trans (one_div_sqrt_mul_log_antitone hx hxy)
  have hbx : 0 ≤ rpowLogDiv x * Chebyshev.theta x :=
    mul_nonneg (rpowLogDiv_nonneg hx) (Chebyshev.theta_nonneg x)
  have hle := neg_abs_le (∫ t in x..y, deriv rpowLogDiv t * Chebyshev.theta t)
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hkey : (8 : ℝ) * Real.log 4 / (Real.sqrt x * Real.log x)
      = Real.log 4 / (Real.sqrt x * Real.log x) + 6 * Real.log 4 / (Real.sqrt x * Real.log x)
        + Real.log 4 / (Real.sqrt x * Real.log x) := by field_simp; ring
  have hpos : (0 : ℝ) < Real.log 4 / (Real.sqrt x * Real.log x) := by positivity
  rw [hkey]
  linarith [abs_le.1 habs |>.1, abs_le.1 habs |>.2]

/-! ### The tilted third-moment sum

`RMF.sum_prime_Ioc_rpow_le` bounds `∑_{x<p≤y} p^{-3/2}`.  What the numerical condition of Harper's
Lemma 3 actually needs is the *tilted* sum `∑ p^{-3/2-3σ}`, since `‖w_p‖³ = p^{-3/2-3σ}` at
`w_p = p^{-1/2-σ-it}`.  The tilt costs a factor `e³` and nothing else: under Harper's
`|σ| ≤ 1/log y` the weight `p^{-3σ}` never exceeds `e³` on the range.

Unlike the *variance* sum, where the analogous `e^{±2}` are sharp, here the factor is pure slack:
the third-moment sum is doubly-exponentially small in the block index. -/

/-- `t^{-3/2-3σ} ≤ e³ t^{-3/2}` for `1 ≤ t ≤ y` with `|σ| log y ≤ 1`.

This is `RMF.rpow_neg_two_mul_le_of_le` read at `σ' = 3σ/2`, `η = 3/2`. -/
lemma rpow_neg_three_halves_le {t y σ : ℝ} (ht : 1 ≤ t) (hty : t ≤ y)
    (hσ : |σ| * Real.log y ≤ 1) :
    t ^ (-(3 / 2) - 3 * σ) ≤ Real.exp 3 * t ^ (-(3 / 2) : ℝ) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hσt : |σ| * Real.log t ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log ht0 hty) (abs_nonneg σ)) hσ
  have hkey : t ^ (-(3 * σ)) ≤ Real.exp 3 := by
    have habs : |3 * σ / 2| * Real.log t ≤ 3 / 2 := by
      rw [show (3 : ℝ) * σ / 2 = 3 / 2 * σ by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      nlinarith [hσt, abs_nonneg σ, hlog]
    have h := rpow_neg_two_mul_le_of_le (σ := 3 * σ / 2) (η := 3 / 2) ht habs
    rw [show -(2 * (3 * σ / 2)) = -(3 * σ) by ring,
      show (2 : ℝ) * (3 / 2) = 3 by norm_num] at h
    exact h
  have hsplit : t ^ (-(3 / 2) - 3 * σ) = t ^ (-(3 * σ)) * t ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add ht0]
    congr 1
    ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg ht0.le _)

/-- **The tilted third-moment sum over a range.**

`∑_{x<p≤y} p^{-3/2-3σ} ≤ e³ · 8 log 4/(√x log x)` when `|σ| log y ≤ 1`.

This is what discharges the `hTb` hypothesis of the block comparison. -/
theorem sum_prime_Ioc_rpow_cube_le {x y σ : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y)
    (hσ : |σ| * Real.log y ≤ 1) :
    ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (p : ℝ) ^ (-(3 / 2) - 3 * σ)
      ≤ Real.exp 3 * (8 * Real.log 4 / (Real.sqrt x * Real.log x)) := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hkey : ∀ p ∈ {p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ | Nat.Prime p},
      (p : ℝ) ^ (-(3 / 2) - 3 * σ) ≤ Real.exp 3 * (p : ℝ) ^ (-(3 / 2) : ℝ) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
    have hfx : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      have : 1 ≤ q := by omega
      exact_mod_cast this
    have hqy : (q : ℝ) ≤ y := le_trans (by exact_mod_cast hq.1.2) (Nat.floor_le hy0)
    exact rpow_neg_three_halves_le hq1 hqy hσ
  calc ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (p : ℝ) ^ (-(3 / 2) - 3 * σ)
      ≤ ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p,
          Real.exp 3 * (p : ℝ) ^ (-(3 / 2) : ℝ) := Finset.sum_le_sum hkey
    _ = Real.exp 3 * ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p,
          (p : ℝ) ^ (-(3 / 2) : ℝ) := by rw [Finset.mul_sum]
    _ ≤ Real.exp 3 * (8 * Real.log 4 / (Real.sqrt x * Real.log x)) :=
        mul_le_mul_of_nonneg_left (sum_prime_Ioc_rpow_le hx hxy) (Real.exp_pos 3).le

/-- **The per-prime tilt bound at a general scale.**  `t^{-3/2-3σ} ≤ e^{3η} t^{-3/2}` for
`1 ≤ t ≤ y` with `|σ| log y ≤ η`; `RMF.rpow_neg_three_halves_le` is the case `η = 1`. -/
lemma rpow_neg_three_halves_le_of_le {t y σ η : ℝ} (ht : 1 ≤ t) (hty : t ≤ y)
    (hσ : |σ| * Real.log y ≤ η) :
    t ^ (-(3 / 2) - 3 * σ) ≤ Real.exp (3 * η) * t ^ (-(3 / 2) : ℝ) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hσt : |σ| * Real.log t ≤ η :=
    le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log ht0 hty) (abs_nonneg σ)) hσ
  have hkey : t ^ (-(3 * σ)) ≤ Real.exp (3 * η) := by
    have habs : |3 * σ / 2| * Real.log t ≤ 3 / 2 * η := by
      rw [show (3 : ℝ) * σ / 2 = 3 / 2 * σ by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      nlinarith [hσt, abs_nonneg σ, hlog]
    have h := rpow_neg_two_mul_le_of_le (σ := 3 * σ / 2) (η := 3 / 2 * η) ht habs
    rw [show -(2 * (3 * σ / 2)) = -(3 * σ) by ring,
      show (2 : ℝ) * (3 / 2 * η) = 3 * η by ring] at h
    exact h
  have hsplit : t ^ (-(3 / 2) - 3 * σ) = t ^ (-(3 * σ)) * t ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add ht0]
    congr 1
    ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg ht0.le _)

/-- **The tilted third-moment sum over a range, at a general scale.**

`RMF.sum_prime_Ioc_rpow_cube_le` is the case `η = 1`.  The scale enters once, as `e^{3η}`, and
the prime sum itself does not see it. -/
theorem sum_prime_Ioc_rpow_cube_le_of_le {x y σ η : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y)
    (hσ : |σ| * Real.log y ≤ η) :
    ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (p : ℝ) ^ (-(3 / 2) - 3 * σ)
      ≤ Real.exp (3 * η) * (8 * Real.log 4 / (Real.sqrt x * Real.log x)) := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hkey : ∀ p ∈ {p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ | Nat.Prime p},
      (p : ℝ) ^ (-(3 / 2) - 3 * σ) ≤ Real.exp (3 * η) * (p : ℝ) ^ (-(3 / 2) : ℝ) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
    have hfx : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      have : 1 ≤ q := by omega
      exact_mod_cast this
    have hqy : (q : ℝ) ≤ y := le_trans (by exact_mod_cast hq.1.2) (Nat.floor_le hy0)
    exact rpow_neg_three_halves_le_of_le hq1 hqy hσ
  calc ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (p : ℝ) ^ (-(3 / 2) - 3 * σ)
      ≤ ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p,
          Real.exp (3 * η) * (p : ℝ) ^ (-(3 / 2) : ℝ) := Finset.sum_le_sum hkey
    _ = Real.exp (3 * η) * ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p,
          (p : ℝ) ^ (-(3 / 2) : ℝ) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (3 * η) * (8 * Real.log 4 / (Real.sqrt x * Real.log x)) :=
        mul_le_mul_of_nonneg_left (sum_prime_Ioc_rpow_le hx hxy) (Real.exp_pos _).le

/-! ### The one-sided form Harper's Lemma 6 actually assumes

The two lemmas above assume `|σ| log y ≤ 1`, a *two-sided* squeeze.  Harper's Lemma 6 assumes only
`σ ≥ -1/log y`, and large positive `σ` is genuinely allowed there — it only makes the sum smaller —
so the one-sided variants below assume only that.

The argument splits on the sign of `σ`.  For `σ ≥ 0` the tilt factor `t^{-3σ}` is at most `1`; for
`σ < 0` it is `exp(3|σ| log t) ≤ exp(3|σ| log y) ≤ e³`.  Either way the same `e³` comes out. -/

/-- `t^{-3/2-3σ} ≤ e³ t^{-3/2}` for `1 ≤ t ≤ y`, under the one-sided `σ ≥ -1/log y`. -/
lemma rpow_neg_three_halves_le' {t y σ : ℝ} (hy : 1 < y) (ht : 1 ≤ t) (hty : t ≤ y)
    (hσ : -(1 / Real.log y) ≤ σ) :
    t ^ (-(3 / 2) - 3 * σ) ≤ Real.exp 3 * t ^ (-(3 / 2) : ℝ) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hkey : t ^ (-(3 * σ)) ≤ Real.exp 3 := by
    rw [Real.rpow_def_of_pos ht0]
    refine Real.exp_le_exp.2 ?_
    rcases le_or_gt 0 σ with hs | hs
    · nlinarith [mul_nonneg hlog hs]
    · have h1 : Real.log t ≤ Real.log y := Real.log_le_log ht0 hty
      have h2 : -σ * Real.log y ≤ 1 := by
        have h3 := mul_le_mul_of_nonneg_right (neg_le_neg hσ) hlogy.le
        rwa [neg_neg, one_div, inv_mul_cancel₀ hlogy.ne'] at h3
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -σ)
        (by linarith : (0 : ℝ) ≤ Real.log y - Real.log t)]
  have hsplit : t ^ (-(3 / 2) - 3 * σ) = t ^ (-(3 * σ)) * t ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add ht0]
    congr 1
    ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg ht0.le _)

/-- **The tilted third-moment sum, under Harper's own hypothesis on `σ`.**

`∑_{x<p≤y} p^{-3/2-3σ} ≤ e³ · 8 log 4/(√x log x)` whenever `σ ≥ -1/log y`.  This is the error
term of Lemma 6, and the only place the `√x` in `(1+|u|³+|v|³)/(√x log x)` comes from. -/
theorem sum_prime_Ioc_rpow_cube_le' {x y σ : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y)
    (hσ : -(1 / Real.log y) ≤ σ) :
    ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (p : ℝ) ^ (-(3 / 2) - 3 * σ)
      ≤ Real.exp 3 * (8 * Real.log 4 / (Real.sqrt x * Real.log x)) := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hy1 : (1 : ℝ) < y := by linarith
  have hkey : ∀ p ∈ {p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ | Nat.Prime p},
      (p : ℝ) ^ (-(3 / 2) - 3 * σ) ≤ Real.exp 3 * (p : ℝ) ^ (-(3 / 2) : ℝ) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
    have hfx : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      have : 1 ≤ q := by omega
      exact_mod_cast this
    have hqy : (q : ℝ) ≤ y := le_trans (by exact_mod_cast hq.1.2) (Nat.floor_le hy0)
    exact rpow_neg_three_halves_le' hy1 hq1 hqy hσ
  calc ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (p : ℝ) ^ (-(3 / 2) - 3 * σ)
      ≤ ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p,
          Real.exp 3 * (p : ℝ) ^ (-(3 / 2) : ℝ) := Finset.sum_le_sum hkey
    _ = Real.exp 3 * ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p,
          (p : ℝ) ^ (-(3 / 2) : ℝ) := by rw [Finset.mul_sum]
    _ ≤ Real.exp 3 * (8 * Real.log 4 / (Real.sqrt x * Real.log x)) :=
        mul_le_mul_of_nonneg_left (sum_prime_Ioc_rpow_le hx hxy) (Real.exp_pos 3).le

end RMF
