/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.RademacherLogField
import RMF.EulerProduct.TiltedLaw

/-!
# The tilted Rademacher law

The Rademacher counterpart of `RMF/EulerProduct/TiltedLaw.lean`: the moments of the local variable
under Harper's tilt, which have to be recomputed for the two-point law rather than transferred.

## Why it is cheaper here

Harper's tilt reweights the value at each prime by the square of the local factor.  For Steinhaus
that factor is `(1 - z a)⁻¹` and the tilted law is the **Poisson kernel** at `a`, whose moments
are a Fourier series — `RMF.integral_pow_tilted_steinhausLaw` and the term-by-term integrations
that follow it.  For Rademacher the factor is the polynomial `1 + z a` and the law has **two
atoms**, so the tilted law is again a two-point law, with weights

`P~(z = ±1) = (1 ± 2 Re a + ‖a‖²) / (2 (1 + ‖a‖²))`,

and every moment below is an explicit average of two numbers.  No series, and no integrability
question at any point.

## What the tilt does to the mean, and why the phase survives

Under `rademacherLaw` itself the local mean has no first-order term: it is
`‖w‖²/2 - (Re w)² + O(‖w‖³) = -Re(w²)/2 + O(‖w‖³)` (`RMF.abs_integral_localLogAdd_sub_le`).
Under the tilt, with `a = p^{-1/2-σ-it}` the tilt radius and `w = p^{-1/2-σ-it_j}` the observable,

`E~[localLogAdd w] = 2 (Re a)(Re w) - Re(w²)/2 + O(‖w‖³ + ‖a‖³‖w‖)`,

which at those values is `c(t, t_j - t, p) / p^{1+2σ}` for Harper's

`c(t, u, p) = 2 cos(t log p) cos(t_j log p) - (1/2) cos(2 t_j log p)`

(Harper, *Moments of random multiplicative functions, I*, arXiv:1703.06654, §5).  Both terms are
genuinely there, and the second is what the Steinhaus case does not have: the Rademacher law is
not rotation invariant, so the expansion sees the phase of `w` and not only `Re (w conj a)`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-! ### The tilt weight -/

/-- On the circle the local factor is bounded away from zero, so its logarithm is honest. -/
lemma norm_one_add_mul_pos {a z : ℂ} (hz : ‖z‖ = 1) (ha : ‖a‖ < 1) : 0 < ‖1 + z * a‖ := by
  have hza : ‖z * a‖ = ‖a‖ := by rw [norm_mul, hz, one_mul]
  have h := norm_sub_norm_le (1 : ℂ) (-(z * a))
  rw [norm_one, norm_neg, hza, sub_neg_eq_add] at h
  linarith

/-- The tilt weight, on the circle: `exp (2 localLogAdd a z) = ‖1 + z a‖ ^ 2`. -/
lemma exp_two_localLogAdd_eq {a z : ℂ} (hz : ‖z‖ = 1) (ha : ‖a‖ < 1) :
    Real.exp (2 * localLogAdd a z) = ‖1 + z * a‖ ^ 2 := by
  have h0 : (0 : ℝ) < ‖1 + z * a‖ := norm_one_add_mul_pos hz ha
  rw [localLogAdd, show 2 * Real.log ‖1 + z * a‖ = Real.log (‖1 + z * a‖ ^ 2) by
    rw [Real.log_pow]; push_cast; ring]
  exact Real.exp_log (by positivity)

/-- …and it is at most `(1 + ‖a‖) ^ 2`. -/
lemma exp_two_localLogAdd_le {a z : ℂ} (hz : ‖z‖ = 1) (ha : ‖a‖ < 1) :
    Real.exp (2 * localLogAdd a z) ≤ (1 + ‖a‖) ^ 2 := by
  rw [exp_two_localLogAdd_eq hz ha]
  have h := norm_add_le (1 : ℂ) (z * a)
  rw [norm_one, norm_mul, hz, one_mul] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma exp_two_localLogAdd_ae_eq {a : ℂ} (ha : ‖a‖ < 1) :
    (fun z => Real.exp (2 * localLogAdd a z))
      =ᵐ[rademacherLaw] fun z => ‖1 + z * a‖ ^ 2 := by
  filter_upwards [norm_eq_one_rademacherLaw] with z hz
  exact exp_two_localLogAdd_eq hz ha

/-- The tilt weight is bounded on the circle, so the tilt is a probability measure. -/
lemma integrable_exp_two_localLogAdd {a : ℂ} (ha : ‖a‖ < 1) :
    Integrable (fun z => Real.exp (2 * localLogAdd a z)) rademacherLaw := by
  refine (memLp_top_of_bound ?_ ((1 + ‖a‖) ^ 2) ?_).integrable le_top
  · exact ((measurable_localLogAdd a).const_mul 2).exp.aestronglyMeasurable
  · filter_upwards [norm_eq_one_rademacherLaw] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact exp_two_localLogAdd_le hz ha

/-- **The normalising constant is `1 + ‖a‖ ^ 2`.**  The two atoms contribute
`1 ± 2 Re a + ‖a‖ ^ 2` and the cross terms cancel — which is the whole computation, where the
Steinhaus case needs a geometric series. -/
lemma integral_exp_two_localLogAdd_rademacherLaw {a : ℂ} (ha : ‖a‖ < 1) :
    (∫ z, Real.exp (2 * localLogAdd a z) ∂rademacherLaw) = 1 + ‖a‖ ^ 2 := by
  rw [integral_congr_ae (exp_two_localLogAdd_ae_eq ha), integral_rademacherLaw_eq,
    norm_one_add_mul_sq_eq (z := 1) (by simp), norm_one_add_mul_sq_eq (z := -1) (by simp)]
  simp only [one_mul, smul_eq_mul, neg_one_mul, Complex.neg_re]
  ring

lemma isProbabilityMeasure_tilted_localLogAdd {a : ℂ} (ha : ‖a‖ < 1) :
    IsProbabilityMeasure (rademacherLaw.tilted fun z => 2 * localLogAdd a z) :=
  isProbabilityMeasure_tilted (integrable_exp_two_localLogAdd ha)

/-! ### The tilted law, in closed form

Everything else in this file is this lemma at a particular `g`. -/

/-- **The tilted Rademacher law.**  Two atoms, weights `1 ± 2 Re a + ‖a‖ ^ 2`, normalisation
`2 (1 + ‖a‖ ^ 2)`.

This is the Rademacher stand-in for `RMF.integral_pow_tilted_steinhausLaw`, and it replaces a
Fourier series by a quotient of two numbers. -/
theorem integral_tilted_localLogAdd_rademacherLaw {a : ℂ} (ha : ‖a‖ < 1) (g : ℂ → ℝ) :
    (∫ z, g z ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a z))
      = (g 1 * (1 + 2 * a.re + ‖a‖ ^ 2) + g (-1) * (1 - 2 * a.re + ‖a‖ ^ 2))
          / (2 * (1 + ‖a‖ ^ 2)) := by
  have hZ : (0 : ℝ) < 1 + ‖a‖ ^ 2 := by positivity
  rw [integral_tilted, integral_exp_two_localLogAdd_rademacherLaw ha, integral_rademacherLaw_eq,
    exp_two_localLogAdd_eq (z := 1) (by simp) ha,
    exp_two_localLogAdd_eq (z := -1) (by simp) ha,
    norm_one_add_mul_sq_eq (z := 1) (by simp), norm_one_add_mul_sq_eq (z := -1) (by simp)]
  simp only [one_mul, smul_eq_mul, neg_one_mul, Complex.neg_re]
  field_simp
  ring

/-- **The tilted local mean, exactly.**  No error term: the mean is the weighted average of the
two values `log‖1 ± w‖`. -/
theorem integral_localLogAdd_tilted_rademacherLaw {a w : ℂ} (ha : ‖a‖ < 1) :
    (∫ z, localLogAdd w z ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a z))
      = (Real.log (1 + (2 * w.re + ‖w‖ ^ 2)) / 2 * (1 + 2 * a.re + ‖a‖ ^ 2)
          + Real.log (1 + (-(2 * w.re) + ‖w‖ ^ 2)) / 2 * (1 - 2 * a.re + ‖a‖ ^ 2))
        / (2 * (1 + ‖a‖ ^ 2)) := by
  rw [integral_tilted_localLogAdd_rademacherLaw ha, localLogAdd_one, localLogAdd_neg_one]

/-! ### The tilt shifts the mean by a multiple of the increment -/

/-- **The tilt splits**: for every `g`, `E~[g] = E[g] + (Re a / (1 + ‖a‖ ^ 2)) · (g 1 - g (-1))`.
This stands in for the Poisson kernel: the tilt moves the mean by the same multiple of the increment
for every observable, so each moment below is an untilted moment
(`RMF/EulerProduct/RademacherLogField.lean`) plus one correction. -/
theorem integral_tilted_eq_add_rademacherLaw {a : ℂ} (ha : ‖a‖ < 1) (g : ℂ → ℝ) :
    (∫ z, g z ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a z))
      = (∫ z, g z ∂rademacherLaw) + a.re / (1 + ‖a‖ ^ 2) * (g 1 - g (-1)) := by
  have hZ : (0 : ℝ) < 1 + ‖a‖ ^ 2 := by positivity
  rw [integral_tilted_localLogAdd_rademacherLaw ha, integral_rademacherLaw_eq, smul_eq_mul]
  field_simp
  ring

/-- The tilt multiplier is at most `‖a‖`, is at most `1/2` for **every** `a` — because
`2 t ≤ 1 + t ^ 2` — and differs from `Re a` by at most `‖a‖ ^ 3`.

The unconditional `1/2` is what lets the moments below ask only `‖a‖ < 1`. -/
lemma abs_tiltMultiplier_le (a : ℂ) :
    |a.re / (1 + ‖a‖ ^ 2)| ≤ ‖a‖ ∧ |a.re / (1 + ‖a‖ ^ 2)| ≤ 1 / 2
      ∧ |a.re / (1 + ‖a‖ ^ 2) - a.re| ≤ ‖a‖ ^ 3 := by
  have hZ : (0 : ℝ) < 1 + ‖a‖ ^ 2 := by positivity
  have hre : |a.re| ≤ ‖a‖ := Complex.abs_re_le_norm a
  have hmul : |a.re| * ‖a‖ ^ 2 ≤ ‖a‖ * ‖a‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hre (sq_nonneg ‖a‖)
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    nlinarith [norm_nonneg a, abs_nonneg a.re]
  · rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    nlinarith [sq_nonneg (‖a‖ - 1)]
  · have hid : a.re / (1 + ‖a‖ ^ 2) - a.re = -(a.re * ‖a‖ ^ 2) / (1 + ‖a‖ ^ 2) := by
      field_simp
      ring
    rw [hid, abs_div, abs_of_pos hZ, div_le_iff₀ hZ, abs_neg, abs_mul, abs_pow,
      abs_of_nonneg (norm_nonneg a)]
    nlinarith [mul_nonneg (pow_nonneg (norm_nonneg a) 3) (sq_nonneg ‖a‖)]

/-- `‖w‖ ^ 2 / 2 - (Re w) ^ 2 = -Re(w ^ 2) / 2`: the quadratic term of the mean is Harper's
second term `-(1/2) cos(2 t_j log p)`, written in terms of `w`. -/
lemma norm_sq_div_two_sub_re_sq (w : ℂ) : ‖w‖ ^ 2 / 2 - w.re ^ 2 = -((w ^ 2).re / 2) := by
  have hn : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [hn, show w ^ 2 = w * w from sq w, Complex.mul_re]
  ring

/-- The local variable is `O(‖w‖)` pointwise on the circle, with the same constant as the
Steinhaus one — it *is* the Steinhaus one, at the reflected point. -/
lemma abs_localLogAdd_le_of_norm_le {w z : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ 1 / 5) :
    |localLogAdd w z| ≤ 11 / 5 * ‖w‖ := by
  rw [localLogAdd_eq_neg_localLog, abs_neg]
  have h := abs_localLog_le_of_norm_le hz (by rwa [norm_neg] : ‖-w‖ ≤ 1 / 5)
  rwa [norm_neg] at h

/-! ### The three moments Harper's Gaussian comparison is defined by -/

/-- **The drift**: `E~[localLogAdd w] = 2 (Re a)(Re w) - Re(w ^ 2)/2 + O(‖w‖³ + ‖a‖³‖w‖)`, for
`‖a‖ < 1` and `‖w‖ ≤ 1/5`.  At `a = p^{-1/2-σ-it}` and `w = p^{-1/2-σ-it_j}` the main term is
Harper's `c(t, t_j - t, p) / p^{1+2σ}`, `c = 2 cos(t log p) cos(t_j log p) - (1/2) cos(2 t_j log p)`
(Harper, arXiv:1703.06654, §5); the phases are not combined into `Re (w conj a)`, and the second
term has no Steinhaus counterpart. -/
theorem abs_integral_localLogAdd_tilted_sub_le {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ z, localLogAdd w z ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a z))
        - (2 * a.re * w.re - (w ^ 2).re / 2)|
      ≤ 36 * ‖w‖ ^ 3 + 2 * ‖a‖ ^ 3 * ‖w‖ := by
  obtain ⟨hκ, -, hκre⟩ := abs_tiltMultiplier_le a
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have ha0 : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
  have hre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have hmean := abs_integral_localLogAdd_sub_le hw
  have hdiff := abs_localLogAdd_diff_sub_le hw
  have hmain : 2 * a.re * w.re - (w ^ 2).re / 2
      = 2 * a.re * w.re + (‖w‖ ^ 2 / 2 - w.re ^ 2) := by
    rw [norm_sq_div_two_sub_re_sq]
    ring
  rw [integral_tilted_eq_add_rademacherLaw ha (localLogAdd w), hmain]
  set κ : ℝ := a.re / (1 + ‖a‖ ^ 2) with hκdef
  set Δ : ℝ := localLogAdd w 1 - localLogAdd w (-1) with hΔdef
  -- `κΔ - 2 (Re a)(Re w) = κ(Δ - 2 Re w) + 2 (Re w)(κ - Re a)`
  have h1 : |κ * (Δ - 2 * w.re)| ≤ 24 * ‖a‖ * ‖w‖ ^ 3 := by
    rw [abs_mul]
    linarith [mul_le_mul hκ hdiff (abs_nonneg _) ha0]
  have h2 : |2 * w.re * (κ - a.re)| ≤ 2 * ‖a‖ ^ 3 * ‖w‖ := by
    rw [abs_mul, abs_mul, abs_two]
    have h := mul_le_mul hre hκre (abs_nonneg _) hw0
    nlinarith [abs_nonneg (κ - a.re), abs_nonneg w.re]
  have hfive : 24 * ‖a‖ * ‖w‖ ^ 3 ≤ 24 * ‖w‖ ^ 3 := by
    nlinarith [pow_nonneg hw0 3]
  rw [abs_le] at hmean h1 h2 ⊢
  constructor <;> linarith [hmean.1, hmean.2, h1.1, h1.2, h2.1, h2.2]

/-- The second moment's algebra, in real variables.  With `L_± = S ± Δ/2` the two atoms give
`S ^ 2 + Δ ^ 2 / 4` and the tilt correction is `κ · 2 S Δ`; all three terms past `u ^ 2` are
fourth order.  Extracted so that each `nlinarith` runs against six hypotheses; inside the theorem
below it times out. -/
private lemma abs_sq_moment_sub_le {S Δ κ u r : ℝ} (hr0 : 0 ≤ r) (hr5 : r ≤ 1 / 5)
    (hu : |u| ≤ r) (hS : |S| ≤ 4 * r ^ 2) (hΔ : |Δ - 2 * u| ≤ 24 * r ^ 3)
    (hκ : |κ| ≤ 1 / 2) :
    |S ^ 2 + Δ ^ 2 / 4 + κ * (2 * S * Δ) - u ^ 2| ≤ 22 * r ^ 3 := by
  have hr3 : (0 : ℝ) ≤ r ^ 3 := pow_nonneg hr0 3
  have hΔb : |Δ| ≤ 3 * r := by
    rw [abs_le] at hΔ hu ⊢
    constructor <;> nlinarith [hΔ.1, hΔ.2, hu.1, hu.2]
  have hsum : |Δ + 2 * u| ≤ 5 * r := by
    rw [abs_le] at hΔb hu ⊢
    constructor <;> linarith [hΔb.1, hΔb.2, hu.1, hu.2]
  have h1 : |Δ ^ 2 / 4 - u ^ 2| ≤ 30 * r ^ 4 := by
    have hfac : Δ ^ 2 / 4 - u ^ 2 = (Δ - 2 * u) * (Δ + 2 * u) / 4 := by ring
    rw [hfac, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (4 : ℝ)),
      div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    nlinarith [mul_le_mul hΔ hsum (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 24 * r ^ 3)]
  have h2 : S ^ 2 ≤ 16 * r ^ 4 := by
    nlinarith [sq_abs S, abs_nonneg S, sq_nonneg r]
  have h3 : |κ * (2 * S * Δ)| ≤ 12 * r ^ 3 := by
    have hSΔ : |S| * |Δ| ≤ 12 * r ^ 3 := by
      nlinarith [mul_le_mul hS hΔb (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 4 * r ^ 2)]
    calc |κ * (2 * S * Δ)| = |κ| * (2 * (|S| * |Δ|)) := by
          rw [abs_mul, abs_mul, abs_mul, abs_two]
          ring
      _ ≤ 1 / 2 * (2 * (12 * r ^ 3)) := by gcongr
      _ = 12 * r ^ 3 := by ring
  have hquart : r ^ 4 ≤ r ^ 3 / 5 := by nlinarith
  rw [abs_le] at h1 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h3.1, h3.2, h2, sq_nonneg S]

/-- **The second moment**: `E~[(localLogAdd w) ^ 2] = (Re w) ^ 2 + O(‖w‖ ^ 3)` for `‖a‖ < 1` and
`‖w‖ ≤ 1/5`.  At `w = p^{-1/2-σ-it_j}` the main term is `(1 + cos(2 t_j log p)) / (2 p^{1+2σ})`,
Harper's Rademacher block variance, where the Steinhaus one is `1 / (2 p^{1+2σ})`.  The hypothesis
is `‖a‖ < 1`, not `‖a‖ ≤ 1/5`: the tilt radius `p^{-s}` is `0.707…` at `p = 2`, `Re s = 1/2`. -/
theorem abs_integral_localLogAdd_sq_tilted_sub_le {a w : ℂ} (ha : ‖a‖ < 1)
    (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ z, localLogAdd w z ^ 2 ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a z))
        - w.re ^ 2| ≤ 22 * ‖w‖ ^ 3 := by
  obtain ⟨-, hκ, -⟩ := abs_tiltMultiplier_le a
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have hmean := abs_integral_localLogAdd_sub_le hw
  have hdiff := abs_localLogAdd_diff_sub_le hw
  rw [integral_tilted_eq_add_rademacherLaw ha (fun z => localLogAdd w z ^ 2)]
  set S : ℝ := ∫ z, localLogAdd w z ∂rademacherLaw with hSdef
  set Δ : ℝ := localLogAdd w 1 - localLogAdd w (-1) with hΔdef
  -- the two atoms are `S ± Δ/2`
  have hL : localLogAdd w 1 = S + Δ / 2 ∧ localLogAdd w (-1) = S - Δ / 2 := by
    rw [hSdef, integral_rademacherLaw_eq, smul_eq_mul, hΔdef]
    constructor <;> ring
  have hsq : (∫ z, localLogAdd w z ^ 2 ∂rademacherLaw) = S ^ 2 + Δ ^ 2 / 4 := by
    rw [integral_rademacherLaw_eq, smul_eq_mul, hL.1, hL.2]
    ring
  have hcorr : localLogAdd w 1 ^ 2 - localLogAdd w (-1) ^ 2 = 2 * S * Δ := by
    rw [hL.1, hL.2]
    ring
  have hSb : |S| ≤ 4 * ‖w‖ ^ 2 := by
    rw [abs_le] at hmean hre ⊢
    constructor <;> nlinarith [hmean.1, hmean.2, hre.1, hre.2, pow_nonneg hw0 3]
  rw [hsq, hcorr]
  exact abs_sq_moment_sub_le hw0 hw hre hSb hdiff hκ

/-- **The third absolute moment**, `E~|localLogAdd w| ^ 3 ≤ (11/5) ^ 3 ‖w‖ ^ 3`.  Pointwise on
the circle, hence valid under the tilt exactly as under the plain law. -/
theorem integral_abs_localLogAdd_cube_tilted_le {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1 / 5) :
    (∫ z, |localLogAdd w z| ^ 3 ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a z))
      ≤ (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
  have hprob := isProbabilityMeasure_tilted_localLogAdd ha
  set ν := rademacherLaw.tilted fun z => 2 * localLogAdd a z with hνdef
  have hcirc : ∀ᵐ z ∂ν, ‖z‖ = 1 :=
    (tilted_absolutelyContinuous rademacherLaw _) norm_eq_one_rademacherLaw
  have hpt : ∀ᵐ z ∂ν, |localLogAdd w z| ^ 3 ≤ (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
    filter_upwards [hcirc] with z hz
    calc |localLogAdd w z| ^ 3 ≤ (11 / 5 * ‖w‖) ^ 3 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_localLogAdd_le_of_norm_le hz hw) 3
      _ = (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by ring
  calc (∫ z, |localLogAdd w z| ^ 3 ∂ν) ≤ ∫ _z : ℂ, (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 ∂ν :=
        integral_mono_of_nonneg (.of_forall fun _ => by positivity) (integrable_const _) hpt
    _ = (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by simp

end RMF
