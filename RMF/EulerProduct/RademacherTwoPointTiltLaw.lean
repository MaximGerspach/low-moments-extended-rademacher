/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.RademacherTiltedLaw

/-!
# The two-fold tilted Rademacher law

The Rademacher counterpart of `RMF/EulerProduct/TwoPointTiltLaw.lean`, underlying the Rademacher
restricted second moment.
`RMF/EulerProduct/RademacherTiltedLaw.lean` computes the moments of `RMF.localLogAdd` under the
**one-fold** tilt `‖1 + z a‖²`; the two-point argument needs them under the **two-fold** tilt
`‖1 + z a₁‖² ‖1 + z a₂‖²`, which is the law of `f(p)` under `RMF.tiltedMeasure₂`.

## Why this is much cheaper than the Steinhaus case

For Steinhaus the tilt weight is a product of two Poisson kernels and the two-point moments have
to be obtained by expanding pointwise on the circle and integrating against `RMF.steinhausLaw`,
where the characters are orthonormal, with `O(δ³)` error terms throughout
(`RMF/EulerProduct/TwoPointTiltLaw.lean`).

The Rademacher law has **two atoms**, so the two-fold tilt is again a two-atom law and every
moment is an explicit average of two numbers.  There is no expansion, no orthogonality, and **no
error term at all**: the identities below are exact.

## The two drifts add, exactly

Writing `rᵢ = Re aᵢ` and `nᵢ = ‖aᵢ‖²`, the atom weights are `(1 ± 2r₁ + n₁)(1 ± 2r₂ + n₂)`, so

* the normalisation is `(1 + n₁)(1 + n₂) + 4 r₁ r₂`, and
* `E~[g] = E[g] + m·(g 1 - g (-1))` with
  `m = (r₁(1 + n₂) + r₂(1 + n₁)) / ((1 + n₁)(1 + n₂) + 4 r₁ r₂)`.

`RMF.integral_tilted_eq_add_rademacherLaw` is the `a₂ = 0` case, where `m` is `r₁/(1 + n₁)`, and
the shape is the same: **the tilt moves the mean by a fixed multiple of the increment, the same
multiple for every observable.**  Every two-point moment the block statistics need is therefore an
untilted moment — all of which `RademacherLogField` already has — plus one correction, exactly as
in the one-fold case.
-/

open MeasureTheory

namespace RMF

variable {a₁ a₂ : ℂ}

/-! ### The two-fold tilt weight -/

/-- The two-fold tilt weight, on the circle. -/
lemma exp_two_localLogAdd_pair_eq {z : ℂ} (hz : ‖z‖ = 1) (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1) :
    Real.exp (2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z)
      = ‖1 + z * a₁‖ ^ 2 * ‖1 + z * a₂‖ ^ 2 := by
  rw [Real.exp_add, exp_two_localLogAdd_eq hz h₁, exp_two_localLogAdd_eq hz h₂]

lemma exp_two_localLogAdd_pair_ae_eq (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1) :
    (fun z => Real.exp (2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z))
      =ᵐ[rademacherLaw] fun z => ‖1 + z * a₁‖ ^ 2 * ‖1 + z * a₂‖ ^ 2 := by
  filter_upwards [norm_eq_one_rademacherLaw] with z hz
  exact exp_two_localLogAdd_pair_eq hz h₁ h₂

/-- The two-fold weight is bounded on the circle. -/
lemma integrable_exp_two_localLogAdd_pair (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1) :
    Integrable (fun z => Real.exp (2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z))
      rademacherLaw := by
  refine (memLp_top_of_bound ?_ ((1 + ‖a₁‖) ^ 2 * (1 + ‖a₂‖) ^ 2) ?_).integrable le_top
  · exact ((((measurable_localLogAdd a₁).const_mul 2).add
      ((measurable_localLogAdd a₂).const_mul 2))).exp.aestronglyMeasurable
  · filter_upwards [norm_eq_one_rademacherLaw] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_add]
    exact mul_le_mul (exp_two_localLogAdd_le hz h₁) (exp_two_localLogAdd_le hz h₂)
      (Real.exp_nonneg _) (by positivity)

/-- **The normalising constant.**  `(1 + ‖a₁‖²)(1 + ‖a₂‖²) + 4 Re a₁ Re a₂` — the one-fold
`1 + ‖a‖²` at `a₂ = 0`, plus the one genuinely two-point term. -/
lemma integral_exp_two_localLogAdd_pair_rademacherLaw (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1) :
    (∫ z, Real.exp (2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z) ∂rademacherLaw)
      = (1 + ‖a₁‖ ^ 2) * (1 + ‖a₂‖ ^ 2) + 4 * a₁.re * a₂.re := by
  rw [integral_congr_ae (exp_two_localLogAdd_pair_ae_eq h₁ h₂), integral_rademacherLaw_eq,
    norm_one_add_mul_sq_eq (z := 1) (w := a₁) (by simp),
    norm_one_add_mul_sq_eq (z := 1) (w := a₂) (by simp),
    norm_one_add_mul_sq_eq (z := -1) (w := a₁) (by simp),
    norm_one_add_mul_sq_eq (z := -1) (w := a₂) (by simp)]
  simp only [one_mul, smul_eq_mul, neg_one_mul, Complex.neg_re]
  ring

/-- The normalisation is positive: it is the average of the two atom weights, and each is a
product of two positive numbers. -/
lemma zero_lt_pair_norm (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1) :
    (0 : ℝ) < (1 + ‖a₁‖ ^ 2) * (1 + ‖a₂‖ ^ 2) + 4 * a₁.re * a₂.re := by
  rw [← integral_exp_two_localLogAdd_pair_rademacherLaw h₁ h₂,
    integral_congr_ae (exp_two_localLogAdd_pair_ae_eq h₁ h₂), integral_rademacherLaw_eq,
    smul_eq_mul]
  have hp : ∀ z : ℂ, ‖z‖ = 1 → (0 : ℝ) < ‖1 + z * a₁‖ ^ 2 * ‖1 + z * a₂‖ ^ 2 := by
    intro z hz
    exact mul_pos (pow_pos (norm_one_add_mul_pos hz h₁) 2)
      (pow_pos (norm_one_add_mul_pos hz h₂) 2)
  have hpos1 := hp 1 (by simp)
  have hpos2 := hp (-1) (by simp)
  linarith

lemma isProbabilityMeasure_tilted_localLogAdd_pair (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1) :
    IsProbabilityMeasure
      (rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z) :=
  isProbabilityMeasure_tilted (integrable_exp_two_localLogAdd_pair h₁ h₂)

/-! ### The two-fold tilted law, in closed form

Everything the two-point block statistics need is this lemma at a particular `g`. -/

/-- **The two-fold tilted Rademacher law.**  Two atoms, weights `(1 ± 2r₁ + n₁)(1 ± 2r₂ + n₂)`.

The Rademacher stand-in for the circle expansion of `TwoPointTiltLaw`, and it replaces every
`O(‖w‖³)` error term there by an exact quotient. -/
theorem integral_tilted_localLogAdd_pair_rademacherLaw (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1)
    (g : ℂ → ℝ) :
    (∫ z, g z ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z))
      = (g 1 * ((1 + 2 * a₁.re + ‖a₁‖ ^ 2) * (1 + 2 * a₂.re + ‖a₂‖ ^ 2))
          + g (-1) * ((1 - 2 * a₁.re + ‖a₁‖ ^ 2) * (1 - 2 * a₂.re + ‖a₂‖ ^ 2)))
        / (2 * ((1 + ‖a₁‖ ^ 2) * (1 + ‖a₂‖ ^ 2) + 4 * a₁.re * a₂.re)) := by
  have hZ := zero_lt_pair_norm h₁ h₂
  rw [integral_tilted, integral_exp_two_localLogAdd_pair_rademacherLaw h₁ h₂,
    integral_rademacherLaw_eq,
    exp_two_localLogAdd_pair_eq (z := 1) (by simp) h₁ h₂,
    exp_two_localLogAdd_pair_eq (z := -1) (by simp) h₁ h₂,
    norm_one_add_mul_sq_eq (z := 1) (w := a₁) (by simp),
    norm_one_add_mul_sq_eq (z := 1) (w := a₂) (by simp),
    norm_one_add_mul_sq_eq (z := -1) (w := a₁) (by simp),
    norm_one_add_mul_sq_eq (z := -1) (w := a₂) (by simp)]
  simp only [one_mul, smul_eq_mul, neg_one_mul, Complex.neg_re]
  field_simp
  ring

/-- The atom weights are `Z ± 2N`, and that is the whole of the split below.  `Z` is abstract
here on purpose: with the normalisation written out, `field_simp` normalises the denominator into
a polynomial it cannot discharge. -/
private lemma pair_split_atoms {g₁ gₘ N Z : ℝ} (hZ : Z ≠ 0) :
    (g₁ * (Z + 2 * N) + gₘ * (Z - 2 * N)) / (2 * Z)
      = 2⁻¹ * (g₁ + gₘ) + N / Z * (g₁ - gₘ) := by
  field_simp
  ring

/-- **The multiplier the two-fold tilt moves the mean by**,
`(Re a₁ (1 + ‖a₂‖²) + Re a₂ (1 + ‖a₁‖²)) / ((1 + ‖a₁‖²)(1 + ‖a₂‖²) + 4 Re a₁ Re a₂)`.
`RMF.pairTiltMultiplier a 0` is the one-fold `Re a / (1 + ‖a‖²)`. -/
noncomputable def pairTiltMultiplier (a₁ a₂ : ℂ) : ℝ :=
  (a₁.re * (1 + ‖a₂‖ ^ 2) + a₂.re * (1 + ‖a₁‖ ^ 2))
    / ((1 + ‖a₁‖ ^ 2) * (1 + ‖a₂‖ ^ 2) + 4 * a₁.re * a₂.re)

/-- **The two drifts add, and the tilt still splits**: for every `g`,
`E~[g] = E[g] + RMF.pairTiltMultiplier a₁ a₂ · (g 1 - g (-1))`.  The two-point form of
`RMF.integral_tilted_eq_add_rademacherLaw`: each two-point moment is an untilted moment plus one
correction, the same multiple of the increment for every observable. -/
theorem integral_tilted_pair_eq_add_rademacherLaw (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1) (g : ℂ → ℝ) :
    (∫ z, g z ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z))
      = (∫ z, g z ∂rademacherLaw) + pairTiltMultiplier a₁ a₂ * (g 1 - g (-1)) := by
  have hZ := zero_lt_pair_norm h₁ h₂
  rw [integral_tilted_localLogAdd_pair_rademacherLaw h₁ h₂, integral_rademacherLaw_eq,
    pairTiltMultiplier, smul_eq_mul,
    show (1 + 2 * a₁.re + ‖a₁‖ ^ 2) * (1 + 2 * a₂.re + ‖a₂‖ ^ 2)
        = ((1 + ‖a₁‖ ^ 2) * (1 + ‖a₂‖ ^ 2) + 4 * a₁.re * a₂.re)
          + 2 * (a₁.re * (1 + ‖a₂‖ ^ 2) + a₂.re * (1 + ‖a₁‖ ^ 2)) from by ring,
    show (1 - 2 * a₁.re + ‖a₁‖ ^ 2) * (1 - 2 * a₂.re + ‖a₂‖ ^ 2)
        = ((1 + ‖a₁‖ ^ 2) * (1 + ‖a₂‖ ^ 2) + 4 * a₁.re * a₂.re)
          - 2 * (a₁.re * (1 + ‖a₂‖ ^ 2) + a₂.re * (1 + ‖a₁‖ ^ 2)) from by ring]
  exact pair_split_atoms (ne_of_gt hZ)

/-! ### The multiplier, in usable form

`RMF.pairTiltMultiplier` plays the part the one-fold `Re a / (1 + ‖a‖ ^ 2)` plays in
`RMF.abs_tiltMultiplier_le`, and the three facts wanted of it are the same three: it is at most
`1/2` in absolute value, it is `O(‖a₁‖ + ‖a₂‖)`, and it is `Re a₁ + Re a₂` to third order.

**The last two need a hypothesis and their one-point twins do not.**  Take `a₁ = a`, `a₂ = -b`
with `a`, `b` real: the numerator is `(a - b)(1 - ab)` and the denominator is
`(1 + a ^ 2)(1 + b ^ 2) - 4ab`, which on the diagonal is `(1 - a ^ 2) ^ 2`.  Near the diagonal the
quotient is therefore `≍ (a - b)/(1 - a ^ 2)`, which is not `O(a + b)` as `a → 1`.  So the
two-point multiplier is tame only once the radii are **jointly** small, and `‖a₁‖ + ‖a₂‖ ≤ 1/2` is
where the last two estimates are stated — still weaker than the `≤ 1/5` the Steinhaus twin
`RMF.abs_integral_localLog_tiltedMeasure₂_sub_le` carries. -/

/-- The quotient's distance from a constant, with the denominator abstract — the same precaution
`RMF.pair_split_atoms` takes, and for the same reason. -/
private lemma pair_multiplier_sub (N Z r : ℝ) (hZ : Z ≠ 0) : N / Z - r = (N - r * Z) / Z := by
  field_simp

/-- The numerator's distance from `(Re a₁ + Re a₂)` times the denominator, in real variables.
Extracted so that each `nlinarith` runs against four hypotheses rather than the theorem's
twenty. -/
private lemma pair_multiplier_numer_bound {u v r t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hr : |r| ≤ u) (ht : |t| ≤ v) (hA : u + v ≤ 1 / 2) :
    |(-(r * u ^ 2) - t * v ^ 2 - (r + t) * (u ^ 2 * v ^ 2 + 4 * (r * t)))|
      ≤ 9 / 4 * (u + v) ^ 3 := by
  have hA0 : (0 : ℝ) ≤ u + v := by linarith
  have h1 : |r * u ^ 2| ≤ u ^ 3 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg u)]
    calc |r| * u ^ 2 ≤ u * u ^ 2 := mul_le_mul_of_nonneg_right hr (sq_nonneg u)
      _ = u ^ 3 := by ring
  have h2 : |t * v ^ 2| ≤ v ^ 3 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg v)]
    calc |t| * v ^ 2 ≤ v * v ^ 2 := mul_le_mul_of_nonneg_right ht (sq_nonneg v)
      _ = v ^ 3 := by ring
  have h3 : |r + t| ≤ u + v := (abs_add_le r t).trans (add_le_add hr ht)
  have h4 : |u ^ 2 * v ^ 2 + 4 * (r * t)| ≤ u ^ 2 * v ^ 2 + 4 * (u * v) := by
    have hrt : |4 * (r * t)| ≤ 4 * (u * v) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hr ht (abs_nonneg t) hu) (by norm_num)
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 2 * v ^ 2)]
    linarith
  have h5 : |(r + t) * (u ^ 2 * v ^ 2 + 4 * (r * t))|
      ≤ (u + v) * (u ^ 2 * v ^ 2 + 4 * (u * v)) := by
    rw [abs_mul]
    exact mul_le_mul h3 h4 (abs_nonneg _) hA0
  rw [show -(r * u ^ 2) - t * v ^ 2 - (r + t) * (u ^ 2 * v ^ 2 + 4 * (r * t))
      = -(r * u ^ 2) + -(t * v ^ 2) + -((r + t) * (u ^ 2 * v ^ 2 + 4 * (r * t))) from by ring]
  refine (le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
  simp only [abs_neg]
  have hc1 : u ^ 3 + v ^ 3 ≤ (u + v) ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg hu hv) hA0]
  have hc2 : 4 * (u * v) ≤ (u + v) ^ 2 := by nlinarith [sq_nonneg (u - v)]
  have hc3 : u ^ 2 * v ^ 2 ≤ (u + v) ^ 4 / 16 := by
    nlinarith [hc2, mul_nonneg hu hv, sq_nonneg (u + v)]
  have hc4 : (u + v) * (u ^ 2 * v ^ 2 + 4 * (u * v))
      ≤ (u + v) * ((u + v) ^ 4 / 16 + (u + v) ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hA0
  have hsq : (u + v) ^ 2 ≤ 4 := by nlinarith [hA0, hA]
  have hc5 : (u + v) * ((u + v) ^ 4 / 16 + (u + v) ^ 2) ≤ 5 / 4 * (u + v) ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg hA0 3) (by linarith : (0 : ℝ) ≤ 4 - (u + v) ^ 2)]
  linarith

/-- **The multiplier is `Re a₁ + Re a₂` to third order**, the two-point form of the third clause
of `RMF.abs_tiltMultiplier_le`, whose error is `‖a‖ ^ 3`. -/
lemma abs_pairTiltMultiplier_sub_le (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1)
    (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 2) :
    |pairTiltMultiplier a₁ a₂ - (a₁.re + a₂.re)| ≤ 3 * (‖a₁‖ + ‖a₂‖) ^ 3 := by
  have hZ := zero_lt_pair_norm h₁ h₂
  have hu : (0 : ℝ) ≤ ‖a₁‖ := norm_nonneg a₁
  have hv : (0 : ℝ) ≤ ‖a₂‖ := norm_nonneg a₂
  have hr : |a₁.re| ≤ ‖a₁‖ := Complex.abs_re_le_norm a₁
  have ht : |a₂.re| ≤ ‖a₂‖ := Complex.abs_re_le_norm a₂
  -- the denominator is at least `3/4`: the cross term is at least `-(‖a₁‖ + ‖a₂‖) ^ 2 ≥ -1/4`
  have hZlb : (3 : ℝ) / 4 ≤ (1 + ‖a₁‖ ^ 2) * (1 + ‖a₂‖ ^ 2) + 4 * a₁.re * a₂.re := by
    have hprod : |4 * a₁.re * a₂.re| ≤ 4 * (‖a₁‖ * ‖a₂‖) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      linarith [mul_le_mul hr ht (abs_nonneg _) hu]
    have h4 : 4 * (‖a₁‖ * ‖a₂‖) ≤ (‖a₁‖ + ‖a₂‖) ^ 2 := by nlinarith [sq_nonneg (‖a₁‖ - ‖a₂‖)]
    have hsq : (‖a₁‖ + ‖a₂‖) ^ 2 ≤ 1 / 4 := by nlinarith [hA, hu, hv]
    have hone : (1 : ℝ) ≤ (1 + ‖a₁‖ ^ 2) * (1 + ‖a₂‖ ^ 2) := by
      nlinarith [sq_nonneg ‖a₁‖, sq_nonneg ‖a₂‖]
    have habs := abs_le.1 hprod
    linarith [habs.1]
  have hsplit : pairTiltMultiplier a₁ a₂ - (a₁.re + a₂.re)
      = (-(a₁.re * ‖a₁‖ ^ 2) - a₂.re * ‖a₂‖ ^ 2
            - (a₁.re + a₂.re) * (‖a₁‖ ^ 2 * ‖a₂‖ ^ 2 + 4 * (a₁.re * a₂.re)))
        / ((1 + ‖a₁‖ ^ 2) * (1 + ‖a₂‖ ^ 2) + 4 * a₁.re * a₂.re) := by
    rw [pairTiltMultiplier, pair_multiplier_sub _ _ _ hZ.ne']
    congr 1
    ring
  rw [hsplit, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  have hnum := pair_multiplier_numer_bound hu hv hr ht hA
  have hZmul : 3 * (‖a₁‖ + ‖a₂‖) ^ 3 * ((3 : ℝ) / 4)
      ≤ 3 * (‖a₁‖ + ‖a₂‖) ^ 3 * ((1 + ‖a₁‖ ^ 2) * (1 + ‖a₂‖ ^ 2) + 4 * a₁.re * a₂.re) :=
    mul_le_mul_of_nonneg_left hZlb (by positivity)
  linarith

/-- **The multiplier is `O(‖a₁‖ + ‖a₂‖)`**, the two-point form of the first clause of
`RMF.abs_tiltMultiplier_le`. -/
lemma abs_pairTiltMultiplier_le (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1) (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 2) :
    |pairTiltMultiplier a₁ a₂| ≤ 2 * (‖a₁‖ + ‖a₂‖) := by
  have hA0 : (0 : ℝ) ≤ ‖a₁‖ + ‖a₂‖ := by positivity
  have hsub := abs_pairTiltMultiplier_sub_le h₁ h₂ hA
  have hre : |a₁.re + a₂.re| ≤ ‖a₁‖ + ‖a₂‖ :=
    (abs_add_le _ _).trans (add_le_add (Complex.abs_re_le_norm a₁) (Complex.abs_re_le_norm a₂))
  have hcube : 3 * (‖a₁‖ + ‖a₂‖) ^ 3 ≤ ‖a₁‖ + ‖a₂‖ := by
    nlinarith [mul_nonneg hA0 (by nlinarith [hA0, hA] : (0 : ℝ) ≤ 1 - 3 * (‖a₁‖ + ‖a₂‖) ^ 2)]
  linarith [abs_sub_abs_le_abs_sub (pairTiltMultiplier a₁ a₂) (a₁.re + a₂.re)]

end RMF
