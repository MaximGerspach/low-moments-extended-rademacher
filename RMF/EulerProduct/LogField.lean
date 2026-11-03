/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Probability.Moments.Covariance
import RMF.EulerProduct.LogExpansion
import RMF.EulerProduct.Moments

/-!
# The local log-variable

`log ‖F_y(s)‖` is a sum over the primes of

`log ‖(1 - z w)⁻¹‖ = -log ‖1 - z w‖`,   `w = p ^ (-s)`, `z` the value at `p`,

and this file computes the first two moments of that summand under the Steinhaus law.  The
two estimates it produces are what makes the field log-correlated:

* `RMF.integral_localLog_eq_zero`: the mean is **exactly zero**, not `O(‖w‖ ^ 2)`.  The
  second-order terms cancel exactly, `E W = -‖w‖ ^ 2` against `E W ^ 2 / 2 = ‖w‖ ^ 2 + …`.
  This matters: an `O(‖w‖ ^ 2)` mean would make `E log ‖F_y‖` of size `log log y`, and the
  product of the two means would then swamp the covariance.
* `RMF.abs_integral_localLog_mul_sub_le`: the mixed second moment of two such variables, which is
  their covariance, is `Re (w₁ conj w₂) / 2 + O(‖w₁‖ ^ 3 + ‖w₂‖ ^ 3)`.  The main term is the
  second-moment computation `RMF.integral_re_mul_mul_re_steinhausLaw` already used for the
  covariance of `F_y` itself.

The mean is exact by harmonicity (Jensen's formula).  The covariance needs no power series of the
logarithm: on the circle `‖1 - z w‖ ^ 2 = 1 - W` with `W = 2 Re (z w) - ‖w‖ ^ 2`, so it reduces to
the real expansion of `log (1 - W)` and to the second moment of `Re (z w)`.

At `w = p ^ (-s)` the errors are `O(p ^ (-3 Re s))`, summable exactly when `Re s > 1/3` —
the same threshold as everywhere else in the library.
-/

open Finset MeasureTheory ProbabilityTheory

namespace RMF

/-! ### Definition and pointwise bounds -/

/-- The contribution of one prime to `log ‖F_y(s)‖`: with `w = p ^ (-s)` and `z` the value of
the random multiplicative function at `p`, the local factor contributes
`log ‖(1 - z w)⁻¹‖ = -log ‖1 - z w‖`. -/
noncomputable def localLog (w : ℂ) (z : ℂ) : ℝ := -Real.log ‖1 - z * w‖

lemma measurable_localLog (w : ℂ) : Measurable (localLog w) :=
  (Real.measurable_log.comp (by fun_prop : Measurable fun z : ℂ => ‖1 - z * w‖)).neg

/-- On the unit circle `‖1 - z w‖` lies between `1 - ‖w‖` and `1 + ‖w‖`. -/
lemma norm_one_sub_mul_bounds {w z : ℂ} (hz : ‖z‖ = 1) :
    1 - ‖w‖ ≤ ‖1 - z * w‖ ∧ ‖1 - z * w‖ ≤ 1 + ‖w‖ := by
  have hzw : ‖z * w‖ = ‖w‖ := by rw [norm_mul, hz, one_mul]
  constructor
  · have h := norm_sub_norm_le (1 : ℂ) (z * w)
    rwa [norm_one, hzw] at h
  · have h := norm_sub_le (1 : ℂ) (z * w)
    rwa [norm_one, hzw] at h

/-- On the circle the local log-variable is a function of `W` alone:
`-log ‖1 - z w‖ = -log (1 - W) / 2`, because `‖1 - z w‖ ^ 2 = 1 - W`. -/
lemma localLog_eq_neg_log_one_sub_localW (w : ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    localLog w z = -(Real.log (1 - localW w z) / 2) := by
  have hsq : ‖1 - z * w‖ ^ 2 = 1 - localW w z := norm_one_sub_mul_sq_eq hz
  rw [localLog, ← hsq, Real.log_pow]
  push_cast
  ring

/-- On the circle `|W| ≤ 2 ‖w‖ + ‖w‖ ^ 2`, so `|W| ≤ 11 ‖w‖ / 5` once `‖w‖ ≤ 1/5`. -/
lemma abs_localW_le {w z : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ 1 / 5) :
    |localW w z| ≤ 11 / 5 * ‖w‖ := by
  have ht0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hre : |(z * w).re| ≤ ‖w‖ :=
    (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul])
  have h := abs_sub (2 * (z * w).re) (‖w‖ ^ 2)
  rw [abs_mul, abs_two, abs_pow, abs_of_nonneg ht0] at h
  rw [localW]
  nlinarith

/-- The crude bound: `|localLog| ≤ log ((1 - θ)⁻¹)` throughout `‖w‖ ≤ θ < 1`. -/
lemma abs_localLog_le {w z : ℂ} {θ : ℝ} (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ θ) (hθ : θ < 1) :
    |localLog w z| ≤ Real.log ((1 - θ)⁻¹) := by
  obtain ⟨hlow, hhigh⟩ := norm_one_sub_mul_bounds (w := w) hz
  have ht0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have ht1 : ‖w‖ < 1 := hw.trans_lt hθ
  have hlow' : (1 - ‖w‖) ^ (1 : ℝ) ≤ ‖1 - z * w‖ := by rwa [Real.rpow_one]
  have hhigh' : ‖1 - z * w‖ ≤ ((1 - ‖w‖)⁻¹) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    refine hhigh.trans ?_
    rw [← one_div, le_div_iff₀ (by linarith : (0 : ℝ) < 1 - ‖w‖)]
    nlinarith
  rw [localLog, abs_neg]
  have h := abs_log_le_of_rpow_bounds (R := 1) zero_le_one le_rfl ht0 hw hθ hlow' hhigh'
  rwa [one_mul] at h

/-! ### The transfer layer: `localLog` against its degree-two truncation

Two walks are in play: the one built from `RMF.localLog`, the logarithm of the Euler product, and
Hamdan's `S_t`, built from `RMF.localTaylorTwo`, the degree-two Taylor truncation.  They differ by
an **absolute constant**, deterministically.

At `w = p^{-s}` with `Re s = 1/2 + σ`, the per-prime gap is `O(p^{-3/2-3σ})`, which
`RMF.sum_prime_Ioc_rpow_cube_le'` bounds over `(x, y]` by `e³ · 8 log 4/(√x log x)` for
`2 ≤ x ≤ y` and `σ ≥ -1/log y`.  So the two walks differ by `O(1)` uniformly in `ω`, and a barrier
event for one is a barrier event for the other with `a` moved by that constant. -/

/-- **A product of local factors is the exponential of the weighted local-log sum.**  On the
circle, `∏_a ‖(1 - z w_a)⁻¹‖ ^ (2 q_a) = exp (2 ∑_a q_a · localLog(w_a, z))` for real `q` of either
sign and every `‖w_a‖ < 1`.  So a joint moment of the Euler product is a moment generating function
of the walk: Hamdan's Lemma B.1 bounds `E exp(λ₁ S_j(σ) + λ₂(S_j(σ+ih₁) - S_j(σ+ih₂)))`, the case
`q = (λ₁, λ₂, -λ₂)/2` at three points. -/
lemma prod_norm_inv_one_sub_rpow_eq_exp {ι : Type*} (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ)
    {z : ℂ} (hz : ‖z‖ = 1) (hw : ∀ a ∈ A, ‖w a‖ < 1) :
    (∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a))
      = Real.exp (2 * ∑ a ∈ A, q a * localLog (w a) z) := by
  have hpos : ∀ a ∈ A, (0 : ℝ) < ‖1 - z * w a‖ := by
    intro a ha
    have h1 : ‖z * w a‖ = ‖w a‖ := by rw [norm_mul, hz, one_mul]
    have h2 := norm_sub_norm_le (1 : ℂ) (z * w a)
    rw [norm_one, h1] at h2
    linarith [hw a ha]
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun a ha => ?_
  rw [norm_inv, Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _),
    Real.rpow_def_of_pos (hpos a ha)]
  simp only [localLog]
  congr 1
  ring

/-- **Second order: `|localLog w z - localTaylorTwo w z| ≤ 12 ‖w‖³`** on the circle, for
`‖w‖ ≤ 1/5`.  The constant is `12`, not the `2` of the scalar expansion, because the degree-two
truncation of `-½ log(1-W)` in `W` is not the one in `w`: expanding `W = 2Re(zw) - ‖w‖²` leaves
`-Re(zw)‖w‖² + ‖w‖⁴/4`, which is `O(‖w‖³)` but has to be carried. -/
lemma abs_localLog_sub_localTaylorTwo_le {w z : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ 1 / 5) :
    |localLog w z - localTaylorTwo w z| ≤ 12 * ‖w‖ ^ 3 := by
  have ht0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hW := abs_localW_le hz hw
  have hWhalf : |localW w z| ≤ 1 / 2 := by nlinarith
  have hlog := abs_neg_log_one_sub_sub_le hWhalf
  have hL : localLog w z = -(Real.log (1 - localW w z)) / 2 := by
    rw [localLog_eq_neg_log_one_sub_localW w hz]
    ring
  have hre : |(z * w).re| ≤ ‖w‖ :=
    (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul])
  -- `Re(zw)² = (Re(z²w²) + ‖w‖²)/2`, the polarisation that makes the algebra close
  have e1 : (z * w) * (z * w) = z ^ 2 * w ^ 2 := by ring
  have e2 : ((z * w) * (starRingEnd ℂ) (z * w)).re = ‖w‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, norm_mul, hz, one_mul]
  have hre2 : (z * w).re * (z * w).re = ((z ^ 2 * w ^ 2).re + ‖w‖ ^ 2) / 2 := by
    rw [re_mul_re, e1, e2]
  have hWdef : localW w z = 2 * (z * w).re - ‖w‖ ^ 2 := rfl
  have hid : (localW w z + localW w z ^ 2 / 2) / 2
      = localTaylorTwo w z - (z * w).re * ‖w‖ ^ 2 + ‖w‖ ^ 4 / 4 := by
    rw [hWdef, localTaylorTwo]
    nlinarith [hre2]
  have hsplit : localLog w z - localTaylorTwo w z
      = (-(Real.log (1 - localW w z)) - (localW w z + localW w z ^ 2 / 2)) / 2
        + (-((z * w).re * ‖w‖ ^ 2) + ‖w‖ ^ 4 / 4) := by
    rw [hL]
    linarith [hid]
  have hcube : |localW w z| ^ 3 ≤ (11 / 5 * ‖w‖) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hW 3
  have h1 : |(-(Real.log (1 - localW w z)) - (localW w z + localW w z ^ 2 / 2)) / 2|
      ≤ |localW w z| ^ 3 := by
    rw [abs_div, abs_two]
    linarith [hlog]
  have h2 : |(-((z * w).re * ‖w‖ ^ 2) + ‖w‖ ^ 4 / 4)| ≤ ‖w‖ ^ 3 + ‖w‖ ^ 4 / 4 := by
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w‖ ^ 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w‖ ^ 4 / 4)]
    nlinarith [hre]
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  nlinarith [h1, h2, hcube, pow_nonneg ht0 3]

/-- **The transfer bound for a signed combination of weights.**
`|∑_a q_a localLog(w_a, z) - ∑_a q_a localTaylorTwo(w_a, z)| ≤ 12 Q |A| t³` when every `|q_a| ≤ Q`
and every `‖w_a‖ ≤ t ≤ 1/5`.  Here `A` indexes points, not primes: Hamdan's Lemma B.1 combines the
same prime's local logarithm at three points with the signed coefficients `(λ₁, λ₂, -λ₂)`. -/
lemma abs_sum_smul_localLog_sub_sum_smul_localTaylorTwo_le {ι : Type*} {A : Finset ι}
    {q : ι → ℝ} {w : ι → ℂ} {z : ℂ} {Q t : ℝ} (hz : ‖z‖ = 1)
    (hq : ∀ a ∈ A, |q a| ≤ Q) (hw : ∀ a ∈ A, ‖w a‖ ≤ t) (ht : t ≤ 1 / 5) :
    |(∑ a ∈ A, q a * localLog (w a) z) - ∑ a ∈ A, q a * localTaylorTwo (w a) z|
      ≤ 12 * Q * A.card * t ^ 3 := by
  rcases A.eq_empty_or_nonempty with hA | ⟨a₀, ha₀⟩
  · subst hA
    simp
  have hQ0 : 0 ≤ Q := le_trans (abs_nonneg _) (hq a₀ ha₀)
  have hterm : ∀ a ∈ A, |q a * localLog (w a) z - q a * localTaylorTwo (w a) z|
      ≤ 12 * Q * t ^ 3 := by
    intro a ha
    have hwa : ‖w a‖ ≤ 1 / 5 := le_trans (hw a ha) ht
    have hloc := abs_localLog_sub_localTaylorTwo_le hz hwa
    have hcube : ‖w a‖ ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (norm_nonneg _) (hw a ha) 3
    calc |q a * localLog (w a) z - q a * localTaylorTwo (w a) z|
        = |q a| * |localLog (w a) z - localTaylorTwo (w a) z| := by
          rw [← mul_sub, abs_mul]
      _ ≤ Q * (12 * t ^ 3) := by
          refine mul_le_mul (hq a ha) (le_trans hloc (by linarith)) (abs_nonneg _) hQ0
      _ = 12 * Q * t ^ 3 := by ring
  calc |(∑ a ∈ A, q a * localLog (w a) z) - ∑ a ∈ A, q a * localTaylorTwo (w a) z|
      = |∑ a ∈ A, (q a * localLog (w a) z - q a * localTaylorTwo (w a) z)| := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ a ∈ A, |q a * localLog (w a) z - q a * localTaylorTwo (w a) z| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ A, 12 * Q * t ^ 3 := Finset.sum_le_sum hterm
    _ = 12 * Q * A.card * t ^ 3 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- **First order.**  `localLog w z = Re (z w) + O(‖w‖ ^ 2)`. -/
lemma abs_localLog_sub_re_le {w z : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ 1 / 5) :
    |localLog w z - (z * w).re| ≤ 6 * ‖w‖ ^ 2 := by
  have ht0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hW := abs_localW_le hz hw
  have hWhalf : |(-localW w z)| ≤ 1 / 2 := by rw [abs_neg]; nlinarith
  have hlog := abs_log_one_add_sub_le hWhalf
  rw [show (1 : ℝ) + -localW w z = 1 - localW w z by ring] at hlog
  have hstep : |localLog w z - localW w z / 2| ≤ localW w z ^ 2 := by
    rw [localLog_eq_neg_log_one_sub_localW w hz,
      show -(Real.log (1 - localW w z) / 2) - localW w z / 2
        = -((Real.log (1 - localW w z) - -localW w z) / 2) by ring, abs_neg, abs_div, abs_two]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [sq_abs (localW w z)]
  have hhalf : localW w z / 2 - (z * w).re = -(‖w‖ ^ 2 / 2) := by rw [localW]; ring
  have hWsq : localW w z ^ 2 ≤ (11 / 5 * ‖w‖) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hW 2
  have htri := abs_sub_le (localLog w z) (localW w z / 2) ((z * w).re)
  rw [hhalf, abs_neg, abs_div, abs_two, abs_pow, abs_of_nonneg ht0] at htri
  nlinarith

/-! ### Integrals

Every function here is bounded on the circle, so integrability is never an issue and all the
bounds come from `MeasureTheory.norm_integral_le_of_norm_le_const`.
-/

lemma ae_abs_localLog_le {w : ℂ} {θ : ℝ} (hw : ‖w‖ ≤ θ) (hθ : θ < 1) :
    ∀ᵐ z ∂steinhausLaw, ‖localLog w z‖ ≤ Real.log ((1 - θ)⁻¹) := by
  filter_upwards [norm_eq_one_steinhausLaw] with z hz
  rw [Real.norm_eq_abs]
  exact abs_localLog_le hz hw hθ

lemma integrable_localLog_mul {w₁ w₂ : ℂ} {θ : ℝ} (h₁ : ‖w₁‖ ≤ θ) (h₂ : ‖w₂‖ ≤ θ)
    (hθ : θ < 1) :
    Integrable (fun z => localLog w₁ z * localLog w₂ z) steinhausLaw :=
  integrable_of_norm_le_steinhausLaw
    (((measurable_localLog w₁).mul (measurable_localLog w₂)).aestronglyMeasurable)
    (Real.log ((1 - θ)⁻¹) ^ 2) <| by
      filter_upwards [ae_abs_localLog_le h₁ hθ, ae_abs_localLog_le h₂ hθ] with z hz₁ hz₂
      rw [Real.norm_eq_abs, abs_mul, sq]
      rw [Real.norm_eq_abs] at hz₁ hz₂
      exact mul_le_mul hz₁ hz₂ (abs_nonneg _) ((abs_nonneg _).trans hz₁)

/-- **The local mean vanishes**: `E localLog w = 0` for `‖w‖ < 1`.  The function
`z ↦ log ‖1 - z w‖` is harmonic on a neighbourhood of the closed unit disc, so its circle average is
its value at the centre, `log ‖1‖ = 0` (Jensen's formula in its simplest case).  A mean of size
`‖w‖ ^ 2` would make `E log ‖F_y‖` of size `log log y`, and the product of the means would swamp
the covariance. -/
lemma integral_localLog_eq_zero {w : ℂ} (hw : ‖w‖ < 1) :
    ∫ z, localLog w z ∂steinhausLaw = 0 := by
  have hne : ∀ x : ℂ, ‖x‖ ≤ 1 → (1 : ℂ) - x * w ≠ 0 := by
    intro x hx1 h
    have hlt : ‖x * w‖ < 1 := by
      rw [norm_mul]
      calc ‖x‖ * ‖w‖ ≤ 1 * ‖w‖ := by gcongr
        _ = ‖w‖ := one_mul _
        _ < 1 := hw
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hlt
    exact lt_irrefl 1 hlt
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z : ℂ => Real.log ‖1 - z * w‖)
      (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) := fun x hx =>
    AnalyticAt.harmonicAt_log_norm (f := fun z : ℂ => 1 - z * w) (by fun_prop)
      (hne x (by simpa using mem_closedBall_zero_iff.mp hx))
  have hmeas : Measurable fun z : ℂ => Real.log ‖1 - z * w‖ :=
    Real.measurable_log.comp (by fun_prop)
  simp only [localLog]
  rw [integral_neg, integral_steinhausLaw_eq_circleAverage hmeas,
    HarmonicOnNhd.circleAverage_eq hharm]
  simp

/-! ### The local covariance -/

private lemma sq_mul_le_cube_add_cube {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 * b ≤ a ^ 3 + b ^ 3 := by
  rcases le_total a b with h | h
  · have h1 : a ^ 2 * b ≤ b ^ 2 * b :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha h 2) hb
    nlinarith [pow_nonneg ha 3]
  · have h1 : a ^ 2 * b ≤ a ^ 2 * a := mul_le_mul_of_nonneg_left h (sq_nonneg a)
    nlinarith [pow_nonneg hb 3]

/-- **The product, pointwise.**  `localLog w z = Re (z w) + O(‖w‖ ^ 2)` twice over. -/
lemma abs_localLog_mul_sub_le {w₁ w₂ z : ℂ} (hz : ‖z‖ = 1) (h₁ : ‖w₁‖ ≤ 1 / 5)
    (h₂ : ‖w₂‖ ≤ 1 / 5) :
    |localLog w₁ z * localLog w₂ z - (z * w₁).re * (z * w₂).re|
      ≤ 20 * (‖w₁‖ ^ 3 + ‖w₂‖ ^ 3) := by
  have hn₁ : (0 : ℝ) ≤ ‖w₁‖ := norm_nonneg w₁
  have hn₂ : (0 : ℝ) ≤ ‖w₂‖ := norm_nonneg w₂
  have ha₁ : |(z * w₁).re| ≤ ‖w₁‖ :=
    (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul])
  have ha₂ : |(z * w₂).re| ≤ ‖w₂‖ :=
    (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul])
  have hr₁ := abs_localLog_sub_re_le hz h₁
  have hr₂ := abs_localLog_sub_re_le hz h₂
  have hc₁ : |(localLog w₁ z - (z * w₁).re) * (z * w₂).re| ≤ 6 * (‖w₁‖ ^ 2 * ‖w₂‖) := by
    rw [abs_mul]
    exact (mul_le_mul hr₁ ha₂ (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hc₂ : |(z * w₁).re * (localLog w₂ z - (z * w₂).re)| ≤ 6 * (‖w₂‖ ^ 2 * ‖w₁‖) := by
    rw [abs_mul]
    exact (mul_le_mul ha₁ hr₂ (abs_nonneg _) hn₁).trans_eq (by ring)
  have hc₃ : |(localLog w₁ z - (z * w₁).re) * (localLog w₂ z - (z * w₂).re)|
      ≤ 36 * (‖w₁‖ ^ 2 * ‖w₂‖ ^ 2) := by
    rw [abs_mul]
    exact (mul_le_mul hr₁ hr₂ (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hcube₁ := sq_mul_le_cube_add_cube hn₁ hn₂
  have hcube₂ := sq_mul_le_cube_add_cube hn₂ hn₁
  have hcube₃ : ‖w₁‖ ^ 2 * ‖w₂‖ ^ 2 ≤ (‖w₁‖ ^ 3 + ‖w₂‖ ^ 3) / 5 := by
    have h : ‖w₁‖ ^ 2 * ‖w₂‖ ^ 2 ≤ ‖w₁‖ ^ 2 * ‖w₂‖ * (1 / 5) :=
      calc ‖w₁‖ ^ 2 * ‖w₂‖ ^ 2 = ‖w₁‖ ^ 2 * ‖w₂‖ * ‖w₂‖ := by ring
        _ ≤ ‖w₁‖ ^ 2 * ‖w₂‖ * (1 / 5) := mul_le_mul_of_nonneg_left h₂ (by positivity)
    linarith
  rw [show localLog w₁ z * localLog w₂ z - (z * w₁).re * (z * w₂).re
      = (localLog w₁ z - (z * w₁).re) * (z * w₂).re
        + (z * w₁).re * (localLog w₂ z - (z * w₂).re)
        + (localLog w₁ z - (z * w₁).re) * (localLog w₂ z - (z * w₂).re) by ring]
  refine (abs_add_three _ _ _).trans ?_
  linarith [pow_nonneg hn₁ 3, pow_nonneg hn₂ 3]

/-- **The second mixed moment.**  The main term is the second-moment computation
`RMF.integral_re_mul_mul_re_steinhausLaw`. -/
lemma abs_integral_localLog_mul_sub_le {w₁ w₂ : ℂ} (h₁ : ‖w₁‖ ≤ 1 / 5) (h₂ : ‖w₂‖ ≤ 1 / 5) :
    |(∫ z, localLog w₁ z * localLog w₂ z ∂steinhausLaw)
      - (w₁ * (starRingEnd ℂ) w₂).re / 2| ≤ 20 * (‖w₁‖ ^ 3 + ‖w₂‖ ^ 3) := by
  have hθ : (1 : ℝ) / 5 < 1 := by norm_num
  have hprod := integrable_localLog_mul h₁ h₂ hθ
  have hre : Integrable (fun z : ℂ => (z * w₁).re * (z * w₂).re) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw (by fun_prop) (‖w₁‖ * ‖w₂‖) <| by
      filter_upwards [norm_eq_one_steinhausLaw] with z hz
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul ((Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul]))
        ((Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul]))
        (abs_nonneg _) (norm_nonneg _)
  rw [← integral_re_mul_mul_re_steinhausLaw, ← integral_sub hprod hre]
  have key := norm_integral_le_of_norm_le_const (μ := steinhausLaw)
    (C := 20 * (‖w₁‖ ^ 3 + ‖w₂‖ ^ 3))
    (f := fun z => localLog w₁ z * localLog w₂ z - (z * w₁).re * (z * w₂).re) <| by
      filter_upwards [norm_eq_one_steinhausLaw] with z hz
      rw [Real.norm_eq_abs]
      exact abs_localLog_mul_sub_le hz h₁ h₂
  rw [Real.norm_eq_abs] at key
  simpa using key

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The field `log ‖F_y(s)‖`

The Euler product factorises the field into a sum of independent local terms, one per prime.
Covariance is bilinear and kills the off-diagonal pairs, so the covariance of the field is the
sum over the primes of the local covariances computed above.
-/

/-- The field whose correlation structure is at issue: `log ‖F_y(s)‖`. -/
noncomputable def logNormEuler (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (s : ℂ) (ω : Ω) : ℝ :=
  Real.log ‖randomEulerProduct f y s ω‖

/-- **The field is a sum of independent local terms.**  Each prime contributes
`log ‖(1 - X p ω · p ^ (-s))⁻¹‖ = localLog (p ^ (-s)) (X p ω)`. -/
lemma logNormEuler_ae_eq_sum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    logNormEuler (fun ω => compMultExtension fun p => X p ω) y s
      =ᵐ[μ] fun ω => ∑ p ∈ Nat.primesBelow y, localLog ((p : ℂ) ^ (-s)) (X p ω) := by
  have hrmf : IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ := hX.isSteinhausRMF
  filter_upwards [hrmf.randomEulerProduct_eq y hs,
    ae_forall_norm_le_one hX norm_le_one_steinhausLaw y] with ω hω hnorm
  have hpos : ∀ p ∈ Nat.primesBelow y,
      (0 : ℝ) < ‖1 - (compMultExtension fun q => X q ω) p * (p : ℂ) ^ (-s)‖ := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesBelow hp
    rw [compMultExtension_apply_prime _ hprime]
    have hw : ‖(p : ℂ) ^ (-s)‖ < 1 := norm_prime_cpow_neg_lt_one hprime hs
    have h := norm_sub_norm_le (1 : ℂ) (X p ω * (p : ℂ) ^ (-s))
    rw [norm_one, norm_mul] at h
    nlinarith [hnorm p hp, norm_nonneg (X p ω), norm_nonneg ((p : ℂ) ^ (-s))]
  rw [logNormEuler, hω, norm_prod,
    Real.log_prod fun p hp => by
      rw [norm_inv]
      exact inv_ne_zero (hpos p hp).ne']
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [norm_inv, Real.log_inv, compMultExtension_apply_prime _ (Nat.prime_of_mem_primesBelow hp),
    localLog]

/-! ### Continuity in the abscissa

Hamdan's Lemma B.2 telescopes the increment along an e-adic sequence of heights,

`S(σ+ih) - S(σ) = ∑_{ℓ≥0} (S(σ+ih_{ℓ+1}) - S(σ+ih_ℓ))`,

and that identity is not a summability statement: it is the statement that the partial sums
`S(σ+ih_{L+1}) - S(σ)` converge, which holds **because `h ↦ S(σ+ih)` is continuous** and
`h_L → h`.  So continuity has to come first, and — unlike everything else about the walk — it is
needed *surely* on the set where every `‖X_p‖ ≤ 1`, not almost surely.

`localLog w z = -log‖1 - z w‖` is continuous in `w` wherever `1 - z w ≠ 0`, and on `‖z‖ ≤ 1`,
`‖w‖ < 1` that is automatic: `‖1 - z w‖ ≥ 1 - ‖w‖ > 0`. -/

/-- `‖1 - z w‖ > 0` when `‖z‖ ≤ 1` and `‖w‖ < 1`: the local factor never vanishes inside the
disc.  This is the same bound as `RMF.norm_one_sub_mul_bounds`, stated for a contraction `z`
rather than a point of the circle, which is what a *deterministic* continuity statement needs. -/
lemma norm_one_sub_mul_pos {w z : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ < 1) : 0 < ‖1 - z * w‖ := by
  have h1 : ‖z * w‖ < 1 := by
    rw [norm_mul]
    calc ‖z‖ * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ = ‖w‖ := one_mul _
      _ < 1 := hw
  have h2 := norm_sub_norm_le (1 : ℂ) (z * w)
  rw [norm_one] at h2
  linarith

end RMF
