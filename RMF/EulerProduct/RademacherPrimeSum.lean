/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.LogExpansion
import RMF.EulerProduct.Moments

/-!
# Moments of the Rademacher random Euler product

The Rademacher local factor is the polynomial `1 + X p ^ (-s)` with `X = ±1`, so a local
moment is an average of two explicit numbers:

`E ‖1 + X w‖ ^ (2 q) = ½[(1 + 2 Re w + ‖w‖ ^ 2) ^ q + (1 - 2 Re w + ‖w‖ ^ 2) ^ q]`.

No integrability question arises — the law has two atoms — which makes this side lighter than
the Steinhaus one, where the local factor has a pole.

## What is shared with the Steinhaus case

* `RMF.exists_taylor_bound_one_sub_rpow` is stated for a *signed* exponent precisely so that it
  covers both models: `α = q` for `(1 - X w)⁻¹` raised to a power, `α = -q` here.
* `RMF.norm_one_sub_mul_sq_eq` is a pointwise identity on the unit circle, and `±1` lies on it,
  so it serves both laws.
* `RMF.exists_abs_log_sub_poly_le` packages the whole passage from a local expansion to a
  local log-expansion, and `RMF.abs_log_prod_prime_sub_sum_le` the summation over the primes;
  both are model-agnostic and live in `RMF/EulerProduct/LogExpansion.lean`.

## What is different

The Rademacher law is not rotation invariant, so the expansion sees the *phase* of `w`:

`E ‖1 + X w‖ ^ (2 q) = 1 + q ‖w‖ ^ 2 + 2 q (q - 1) (Re w) ^ 2 + O_Q(‖w‖ ^ 3)`.

With `w = p ^ (-σ - it)` this is `1 + p ^ (-2σ)[q ^ 2 + q(q-1)\cos(2 t \log p)]`, so the prime
sum acquires a second, oscillatory piece `∑_p \cos(2 t \log p) p ^ (-2σ)` beside
`∑_p p ^ (-2σ)`.  The coefficient `q(q-1)` vanishes at `q = 1`, which is why the second moment
is a function of `Re s` alone while general moments are not.
-/

open Finset MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The local moment in closed form -/

/-- `‖v‖ ^ (2 q) = (‖v‖ ^ 2) ^ q`. -/
lemma norm_rpow_two_mul (v : ℂ) (q : ℝ) : ‖v‖ ^ (2 * q) = (‖v‖ ^ 2) ^ q := by
  rw [Real.rpow_mul (norm_nonneg v), ← Real.rpow_natCast ‖v‖ 2]
  norm_num

/-- **The Rademacher local moment.**  The law has two atoms, so the moment is an explicit
average and no integrability hypothesis is needed. -/
theorem integral_norm_one_add_mul_rpow_rademacherLaw (q : ℝ) (w : ℂ) :
    (∫ z, ‖1 + z * w‖ ^ (2 * q) ∂rademacherLaw)
      = ((1 + 2 * w.re + ‖w‖ ^ 2) ^ q + (1 - 2 * w.re + ‖w‖ ^ 2) ^ q) / 2 := by
  rw [integral_rademacherLaw_eq]
  have h1 : ‖1 + (1 : ℂ) * w‖ ^ (2 * q) = (1 + 2 * w.re + ‖w‖ ^ 2) ^ q := by
    rw [norm_rpow_two_mul, norm_one_add_mul_sq_eq (by simp)]
    simp
  have h2 : ‖1 + (-1 : ℂ) * w‖ ^ (2 * q) = (1 - 2 * w.re + ‖w‖ ^ 2) ^ q := by
    rw [norm_rpow_two_mul, norm_one_add_mul_sq_eq (by simp)]
    congr 1
    simp [Complex.neg_re]
    ring
  rw [h1, h2, smul_eq_mul]
  ring

/-! ### The multi-point local moment

The bottom of the Rademacher joint Laplace transform, and the counterpart of
`RMF.exists_local_multi_expansion_steinhausLaw`'s starting point.

The Steinhaus multi-point moment is an integral over the circle of a product of `‖1 - z w_a‖`
powers, and expanding it takes much of `RMF/EulerProduct/JointLaplace.lean`.  **The Rademacher one
is a two-term average in closed form**, because the law has two atoms: the product is evaluated at
`z = 1` and at `z = -1` and averaged.

What the closed form does *not* do is make the expansion trivial: as in the one-point case
(`RMF.exists_local_expansion_rademacherLaw`) the answer is not a function of the `‖w_a‖` alone,
because the law is not rotation invariant and the phases survive. -/

/-- **The Rademacher multi-point local moment**, in closed form.  The mirror of the circle integral
that opens the Steinhaus joint Laplace chain; here it is an explicit two-term average, so no
integrability hypothesis is needed and the exponents may have either sign. -/
theorem integral_prod_norm_one_add_mul_rpow_rademacherLaw {ι : Type*} (A : Finset ι)
    (q : ι → ℝ) (w : ι → ℂ) :
    (∫ z, ∏ a ∈ A, ‖1 + z * w a‖ ^ (2 * q a) ∂rademacherLaw)
      = ((∏ a ∈ A, (1 + 2 * (w a).re + ‖w a‖ ^ 2) ^ q a)
          + ∏ a ∈ A, (1 - 2 * (w a).re + ‖w a‖ ^ 2) ^ q a) / 2 := by
  rw [integral_rademacherLaw_eq]
  have hP : (∏ a ∈ A, ‖1 + (1 : ℂ) * w a‖ ^ (2 * q a))
      = ∏ a ∈ A, (1 + 2 * (w a).re + ‖w a‖ ^ 2) ^ q a := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [norm_rpow_two_mul, norm_one_add_mul_sq_eq (by simp)]
    simp
  have hM : (∏ a ∈ A, ‖1 + (-1 : ℂ) * w a‖ ^ (2 * q a))
      = ∏ a ∈ A, (1 - 2 * (w a).re + ‖w a‖ ^ 2) ^ q a := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [norm_rpow_two_mul, norm_one_add_mul_sq_eq (by simp)]
    congr 1
    simp [Complex.neg_re]
    ring
  rw [hP, hM, smul_eq_mul]
  ring

/-! ### The local expansion -/

/-- **The Rademacher local expansion.**  For `|q| ≤ Q` and `‖w‖ ≤ 1/5`,

`E ‖1 + X w‖ ^ (2 q) = 1 + q ‖w‖ ^ 2 + 2 q (q - 1) (Re w) ^ 2 + O_Q(‖w‖ ^ 3)`.

Unlike the Steinhaus expansion this is not a function of `‖w‖` alone: the law is not rotation
invariant, so the phase of `w` survives. -/
theorem exists_local_expansion_rademacherLaw {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C > 0, ∀ q ∈ Set.Icc (-Q) Q, ∀ w : ℂ, ‖w‖ ≤ 1 / 5 →
      |(∫ z, ‖1 + z * w‖ ^ (2 * q) ∂rademacherLaw)
        - (1 + q * ‖w‖ ^ 2 + 2 * q * (q - 1) * w.re ^ 2)| ≤ C * ‖w‖ ^ 3 := by
  obtain ⟨C₀, hC₀, htaylor⟩ := exists_taylor_bound_one_sub_rpow hQ
  refine ⟨11 * C₀ + Q * (Q + 1) / 10, by positivity, ?_⟩
  rintro q ⟨hq0, hqQ⟩ w hw
  have ht0 : (0:ℝ) ≤ ‖w‖ := norm_nonneg w
  have hre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have hsq : ‖w‖ ^ 2 ≤ ‖w‖ / 5 := by nlinarith
  have hcube : (0:ℝ) ≤ ‖w‖ ^ 3 := by positivity
  -- the two arguments of the Taylor bound
  set aP : ℝ := -(2 * w.re + ‖w‖ ^ 2) with haP
  set aM : ℝ := 2 * w.re - ‖w‖ ^ 2 with haM
  have hb : ∀ a : ℝ, |a| ≤ 2 * ‖w‖ + ‖w‖ ^ 2 → |a| ≤ 1 / 2 := by
    intro a h
    nlinarith
  have habP : |aP| ≤ 2 * ‖w‖ + ‖w‖ ^ 2 := by
    rw [haP, abs_neg]
    have := abs_add_le (2 * w.re) (‖w‖ ^ 2)
    rw [abs_mul, abs_two, abs_pow, abs_of_nonneg ht0] at this
    linarith
  have habM : |aM| ≤ 2 * ‖w‖ + ‖w‖ ^ 2 := by
    rw [haM, sub_eq_add_neg]
    have := abs_add_le (2 * w.re) (-(‖w‖ ^ 2))
    rw [abs_mul, abs_two, abs_neg, abs_pow, abs_of_nonneg ht0] at this
    linarith
  have hαmem : (-q) ∈ Set.Icc (-Q) Q := ⟨by linarith, by linarith⟩
  have eP := htaylor (-q) hαmem aP (hb _ habP)
  have eM := htaylor (-q) hαmem aM (hb _ habM)
  -- the closed form, rewritten as the two powers the Taylor bound speaks about
  have hclosed : (∫ z, ‖1 + z * w‖ ^ (2 * q) ∂rademacherLaw)
      = ((1 - aP) ^ (-(-q)) + (1 - aM) ^ (-(-q))) / 2 := by
    rw [integral_norm_one_add_mul_rpow_rademacherLaw, haP, haM, neg_neg,
      show (1 : ℝ) - -(2 * w.re + ‖w‖ ^ 2) = 1 + 2 * w.re + ‖w‖ ^ 2 by ring,
      show (1 : ℝ) - (2 * w.re - ‖w‖ ^ 2) = 1 - 2 * w.re + ‖w‖ ^ 2 by ring]
  -- the average of the two Taylor polynomials is the claimed expansion, up to a quartic term
  have hpoly : ((1 + -q * aP + -q * (-q + 1) / 2 * aP ^ 2)
      + (1 + -q * aM + -q * (-q + 1) / 2 * aM ^ 2)) / 2
      = 1 + q * ‖w‖ ^ 2 + 2 * q * (q - 1) * w.re ^ 2 + q * (q - 1) * ‖w‖ ^ 4 / 2 := by
    rw [haP, haM]; ring
  have hquart : |q * (q - 1) * ‖w‖ ^ 4 / 2| ≤ Q * (Q + 1) / 10 * ‖w‖ ^ 3 := by
    have h1 : |q * (q - 1)| ≤ Q * (Q + 1) := by
      rw [abs_mul]
      have h2 : |q - 1| ≤ Q + 1 := by rw [abs_le]; constructor <;> linarith
      exact mul_le_mul (abs_le.2 ⟨hq0, hqQ⟩) h2 (abs_nonneg _) hQ
    have h3 : ‖w‖ ^ 4 ≤ ‖w‖ ^ 3 / 5 := by nlinarith
    rw [abs_div, abs_two, abs_mul, abs_pow, abs_of_nonneg ht0]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [abs_nonneg (q * (q - 1)), pow_nonneg ht0 4, pow_nonneg ht0 3]
  -- assemble
  have hcube' : (2 * ‖w‖ + ‖w‖ ^ 2) ^ 3 ≤ 11 * ‖w‖ ^ 3 := by
    have h : 2 * ‖w‖ + ‖w‖ ^ 2 ≤ 11 * ‖w‖ / 5 := by linarith
    calc (2 * ‖w‖ + ‖w‖ ^ 2) ^ 3 ≤ (11 * ‖w‖ / 5) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h 3
      _ ≤ 11 * ‖w‖ ^ 3 := by nlinarith [pow_nonneg ht0 3]
  have herr : ∀ a : ℝ, |a| ≤ 2 * ‖w‖ + ‖w‖ ^ 2 → C₀ * |a| ^ 3 ≤ 11 * C₀ * ‖w‖ ^ 3 := by
    intro a h
    have h1 : |a| ^ 3 ≤ (2 * ‖w‖ + ‖w‖ ^ 2) ^ 3 := pow_le_pow_left₀ (abs_nonneg a) h 3
    nlinarith [hC₀.le]
  rw [hclosed]
  have hsplit : ((1 - aP) ^ (-(-q)) + (1 - aM) ^ (-(-q))) / 2
      - (1 + q * ‖w‖ ^ 2 + 2 * q * (q - 1) * w.re ^ 2)
      = (((1 - aP) ^ (-(-q)) - (1 + -q * aP + -q * (-q + 1) / 2 * aP ^ 2))
        + ((1 - aM) ^ (-(-q)) - (1 + -q * aM + -q * (-q + 1) / 2 * aM ^ 2))) / 2
        + q * (q - 1) * ‖w‖ ^ 4 / 2 := by
    linarith [hpoly]
  rw [hsplit]
  have htri : |(((1 - aP) ^ (-(-q)) - (1 + -q * aP + -q * (-q + 1) / 2 * aP ^ 2))
        + ((1 - aM) ^ (-(-q)) - (1 + -q * aM + -q * (-q + 1) / 2 * aM ^ 2))) / 2
        + q * (q - 1) * ‖w‖ ^ 4 / 2|
      ≤ (|(1 - aP) ^ (-(-q)) - (1 + -q * aP + -q * (-q + 1) / 2 * aP ^ 2)|
          + |(1 - aM) ^ (-(-q)) - (1 + -q * aM + -q * (-q + 1) / 2 * aM ^ 2)|) / 2
        + |q * (q - 1) * ‖w‖ ^ 4 / 2| := by
    refine (abs_add_le _ _).trans ?_
    gcongr
    rw [abs_div, abs_two]
    gcongr
    exact abs_add_le _ _
  refine htri.trans ?_
  have hP := (eP.trans (herr aP habP))
  have hM := (eM.trans (herr aM habM))
  linarith [hquart]

/-! ### After taking logarithms -/

/-- **Two-sided bounds on the Rademacher local moment, for either sign of the exponent.**  The
moment is an average of two numbers, each between `1 - ‖w‖` and `1 + ‖w‖ ≤ (1 - ‖w‖)⁻¹`.

Stated with `|r|`: for `r < 0` the map `x ↦ x ^ r` is antitone, so the two sides swap, and the
`|r|` is what absorbs the swap.  That is what lets the negative moments reuse the machinery. -/
lemma localMoment_rademacher_bounds {w : ℂ} (hw : ‖w‖ < 1) (r : ℝ) :
    (1 - ‖w‖) ^ |r| ≤ (∫ z, ‖1 + z * w‖ ^ r ∂rademacherLaw)
      ∧ (∫ z, ‖1 + z * w‖ ^ r ∂rademacherLaw) ≤ ((1 - ‖w‖)⁻¹) ^ |r| := by
  have h0 : (0 : ℝ) < 1 - ‖w‖ := by linarith
  have ht0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hinv : ∀ x y : ℝ, 0 < x → (x⁻¹) ^ y = x ^ (-y) := fun x y hx => by
    rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
  have key : ∀ v : ℂ, ‖v‖ = 1 →
      (1 - ‖w‖) ^ |r| ≤ ‖1 + v * w‖ ^ r ∧ ‖1 + v * w‖ ^ r ≤ ((1 - ‖w‖)⁻¹) ^ |r| := by
    intro v hv
    have hvw : ‖v * w‖ = ‖w‖ := by rw [norm_mul, hv, one_mul]
    have hlow : 1 - ‖w‖ ≤ ‖1 + v * w‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (-(v * w))
      rw [norm_one, norm_neg, hvw, sub_neg_eq_add] at h
      exact h
    have hpos : (0 : ℝ) < ‖1 + v * w‖ := lt_of_lt_of_le h0 hlow
    have hhigh : ‖1 + v * w‖ ≤ (1 - ‖w‖)⁻¹ := by
      have h := norm_add_le (1 : ℂ) (v * w)
      rw [norm_one, hvw] at h
      refine h.trans ?_
      have hmul : (1 + ‖w‖) * (1 - ‖w‖) ≤ 1 := by nlinarith
      calc (1 : ℝ) + ‖w‖ = (1 + ‖w‖) * (1 - ‖w‖) / (1 - ‖w‖) := by field_simp
        _ ≤ 1 / (1 - ‖w‖) := by gcongr
        _ = (1 - ‖w‖)⁻¹ := one_div _
    rcases le_or_gt 0 r with hr | hr
    · rw [abs_of_nonneg hr]
      exact ⟨Real.rpow_le_rpow h0.le hlow hr, Real.rpow_le_rpow hpos.le hhigh hr⟩
    · rw [abs_of_neg hr]
      refine ⟨?_, ?_⟩
      · calc (1 - ‖w‖) ^ (-r) = ((1 - ‖w‖)⁻¹) ^ r := (hinv _ _ h0).symm
          _ ≤ ‖1 + v * w‖ ^ r := Real.rpow_le_rpow_of_nonpos hpos hhigh hr.le
      · calc ‖1 + v * w‖ ^ r ≤ (1 - ‖w‖) ^ r := Real.rpow_le_rpow_of_nonpos h0 hlow hr.le
          _ = ((1 - ‖w‖)⁻¹) ^ (-r) := by rw [hinv _ _ h0, neg_neg]
  obtain ⟨l1, u1⟩ := key 1 (by simp)
  obtain ⟨l2, u2⟩ := key (-1) (by simp)
  rw [integral_rademacherLaw_eq, smul_eq_mul]
  constructor <;> linarith

/-- The crude bound on the logarithm of a Rademacher local moment, valid on the whole range
`‖w‖ ≤ θ < 1`.  The two-sided bound `RMF.localMoment_rademacher_bounds` is the input that
`RMF.abs_log_le_of_rpow_bounds` asks for, once `1 + ‖w‖ ≤ (1 - ‖w‖)⁻¹` is checked. -/
lemma abs_log_localMoment_rademacher_le {w : ℂ} {θ : ℝ} (hθ : θ < 1) (hw : ‖w‖ ≤ θ)
    {q Q : ℝ} (hq0 : -Q ≤ q) (hqQ : q ≤ Q) :
    |Real.log (∫ z, ‖1 + z * w‖ ^ (2 * q) ∂rademacherLaw)|
      ≤ 2 * Q * Real.log ((1 - θ)⁻¹) := by
  have ht0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have ht : ‖w‖ < 1 := hw.trans_lt hθ
  obtain ⟨hlow, hhigh⟩ := localMoment_rademacher_bounds ht (2 * q)
  exact abs_log_le_of_rpow_bounds (abs_nonneg _)
    (abs_le.2 ⟨by linarith, by linarith⟩) ht0 hw hθ hlow hhigh

/-- **The Rademacher local expansion after taking logarithms**, on the whole range
`‖w‖ ≤ θ < 1`.  The three hypotheses of `RMF.exists_abs_log_sub_poly_le` are the local
expansion, the bound `|P| ≤ Q (2Q + 3) ‖w‖ ^ 2` on the polynomial
`P = q ‖w‖ ^ 2 + 2 q (q - 1) (Re w) ^ 2`, and the crude bound
`RMF.abs_log_localMoment_rademacher_le`. -/
theorem exists_local_log_bound_rademacherLaw {Q θ : ℝ} (hQ : 0 ≤ Q) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) :
    ∃ C > 0, ∀ q ∈ Set.Icc (-Q) Q, ∀ w : ℂ, ‖w‖ ≤ θ →
      |Real.log (∫ z, ‖1 + z * w‖ ^ (2 * q) ∂rademacherLaw)
        - (q * ‖w‖ ^ 2 + 2 * q * (q - 1) * w.re ^ 2)| ≤ C * ‖w‖ ^ 3 := by
  obtain ⟨C₀, hC₀, hexp⟩ := exists_local_expansion_rademacherLaw hQ
  have hL0 : 0 ≤ Real.log ((1 - θ)⁻¹) :=
    Real.log_nonneg (one_le_inv_iff₀.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨C, hC, hbound⟩ := exists_abs_log_sub_poly_le (M₀ := 2 * Q * Real.log ((1 - θ)⁻¹))
    hC₀.le (by positivity : (0 : ℝ) ≤ Q * (2 * Q + 3)) (by positivity)
  refine ⟨C, hC, ?_⟩
  rintro q ⟨hq0, hqQ⟩ w hw
  have ht0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hresq : w.re ^ 2 ≤ ‖w‖ ^ 2 := by
    nlinarith [Complex.abs_re_le_norm w, abs_nonneg w.re, sq_abs w.re]
  -- the expansion, reassociated as `1 + P`
  have hfine : ‖w‖ ≤ 1 / 5 →
      |(∫ z, ‖1 + z * w‖ ^ (2 * q) ∂rademacherLaw)
        - (1 + (q * ‖w‖ ^ 2 + 2 * q * (q - 1) * w.re ^ 2))| ≤ C₀ * ‖w‖ ^ 3 := fun h => by
    rw [show (1 : ℝ) + (q * ‖w‖ ^ 2 + 2 * q * (q - 1) * w.re ^ 2)
      = 1 + q * ‖w‖ ^ 2 + 2 * q * (q - 1) * w.re ^ 2 by ring]
    exact hexp q ⟨hq0, hqQ⟩ w h
  -- the polynomial is at most `Q (2Q + 3) ‖w‖ ^ 2`
  have hpoly : |q * ‖w‖ ^ 2 + 2 * q * (q - 1) * w.re ^ 2| ≤ Q * (2 * Q + 3) * ‖w‖ ^ 2 := by
    have hqabs : |q| ≤ Q := abs_le.2 ⟨hq0, hqQ⟩
    have h1 : |q * ‖w‖ ^ 2| ≤ Q * ‖w‖ ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg ‖w‖)]
      exact mul_le_mul_of_nonneg_right hqabs (sq_nonneg _)
    have hq1 : |q - 1| ≤ Q + 1 := by rw [abs_le]; constructor <;> linarith
    have hcoef : 2 * |q| * |q - 1| ≤ 2 * Q * (Q + 1) := by
      nlinarith [abs_nonneg (q - 1), abs_nonneg q]
    have h2 : |2 * q * (q - 1) * w.re ^ 2| ≤ 2 * Q * (Q + 1) * ‖w‖ ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg w.re), abs_mul, abs_mul, abs_two]
      exact mul_le_mul hcoef hresq (sq_nonneg _) (by positivity)
    calc |q * ‖w‖ ^ 2 + 2 * q * (q - 1) * w.re ^ 2|
        ≤ |q * ‖w‖ ^ 2| + |2 * q * (q - 1) * w.re ^ 2| := abs_add_le _ _
      _ ≤ Q * ‖w‖ ^ 2 + 2 * Q * (Q + 1) * ‖w‖ ^ 2 := by linarith
      _ = Q * (2 * Q + 3) * ‖w‖ ^ 2 := by ring
  exact hbound _ _ _ ht0 (by linarith) hfine hpoly
    (abs_log_localMoment_rademacher_le hθ hw hq0 hqQ)

/-! ### The prime sum

Summing the local estimate over `p < y`.  Where the Steinhaus prime sum involves only
`∑_p p ^ (-2σ)`, the Rademacher one also involves the oscillatory `∑_p \cos(2 t \log p) p ^ (-2σ)`,
because the local expansion sees the phase of `p ^ (-s)`.
-/

/-- The local polynomial, in trigonometric form: the coefficient of `p ^ (-2σ)` is
`q ^ 2 + q (q - 1) \cos(2 t \log p)`. -/
lemma local_poly_eq {p : ℕ} (hp : p.Prime) (q : ℝ) (s : ℂ) :
    q * ‖(p : ℂ) ^ (-s)‖ ^ 2 + 2 * q * (q - 1) * (((p : ℂ) ^ (-s)).re) ^ 2
      = (p : ℝ) ^ (-2 * s.re)
        * (q ^ 2 + q * (q - 1) * Real.cos (2 * (s.im * Real.log p))) := by
  have hre := re_natCast_cpow_neg hp.pos s
  have hcos : Real.cos (s.im * Real.log p) ^ 2
      = 1 / 2 + Real.cos (2 * (s.im * Real.log p)) / 2 := Real.cos_sq _
  have hsq : ((p : ℝ) ^ (-s.re)) ^ 2 = (p : ℝ) ^ (-2 * s.re) := by
    rw [rpow_neg_pow (by positivity : (0 : ℝ) ≤ (p : ℝ))]; norm_num
  rw [norm_prime_cpow_neg_sq hp, hre, mul_pow, hsq, hcos]
  ring

/-- **The Rademacher prime sum.**  For `|q| ≤ Q` and `σ₀ ≤ Re s` with `σ₀ > 1/3`,

`log ∏_{p < y} E ‖1 + X p ^ (-s)‖ ^ (2q)`
`  = ∑_{p < y} p ^ (-2 Re s) [q ^ 2 + q (q-1) \cos(2 (Im s) \log p)] + O(1)`,

with a constant depending only on `Q` and `σ₀`. -/
theorem exists_prime_sum_bound_rademacherLaw {Q σ₀ : ℝ} (hQ : 0 ≤ Q) (hσ₀ : 1 / 3 < σ₀) :
    ∃ C > 0, ∀ q ∈ Set.Icc (-Q) Q, ∀ s : ℂ, σ₀ ≤ s.re → ∀ y : ℕ,
      |Real.log (∏ p ∈ Nat.primesBelow y,
          ∫ z, ‖1 + z * (p : ℂ) ^ (-s)‖ ^ (2 * q) ∂rademacherLaw)
        - ∑ p ∈ Nat.primesBelow y, ((p : ℝ) ^ (-2 * s.re)
            * (q ^ 2 + q * (q - 1) * Real.cos (2 * (s.im * Real.log p))))| ≤ C := by
  have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_nonneg (by norm_num) _
  have hθ : (2 : ℝ) ^ (-σ₀) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨C₁, hC₁, hlocal⟩ := exists_local_log_bound_rademacherLaw hQ hθ0 hθ
  have hT0 : (0 : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 * σ₀) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨C₁ * ∑' n : ℕ, (n : ℝ) ^ (-3 * σ₀) + C₁, by positivity, ?_⟩
  rintro q ⟨hq0, hqQ⟩ s hs y
  -- the target sum is `∑ P (p ^ (-s))` for the local polynomial `P`, by `RMF.local_poly_eq`
  have hsum : ∑ p ∈ Nat.primesBelow y,
        (q * ‖(p : ℂ) ^ (-s)‖ ^ 2 + 2 * q * (q - 1) * (((p : ℂ) ^ (-s)).re) ^ 2)
      = ∑ p ∈ Nat.primesBelow y, ((p : ℝ) ^ (-2 * s.re)
          * (q ^ 2 + q * (q - 1) * Real.cos (2 * (s.im * Real.log p)))) :=
    Finset.sum_congr rfl fun p hp => local_poly_eq (Nat.prime_of_mem_primesBelow hp) q s
  rw [← hsum]
  have hbounds : ∀ w : ℂ, ‖w‖ ≤ (2 : ℝ) ^ (-σ₀) →
      0 < ∫ z, ‖1 + z * w‖ ^ (2 * q) ∂rademacherLaw := fun w hw => by
    have hb := (localMoment_rademacher_bounds (hw.trans_lt hθ) (2 * q)).1
    have hpp : (0 : ℝ) < (1 - ‖w‖) ^ |2 * q| :=
      Real.rpow_pos_of_pos (by linarith [hw.trans_lt hθ]) _
    linarith
  have key := abs_log_prod_prime_sub_sum_le hσ₀ hC₁.le
    (I := fun w => ∫ z, ‖1 + z * w‖ ^ (2 * q) ∂rademacherLaw)
    (P := fun w => q * ‖w‖ ^ 2 + 2 * q * (q - 1) * w.re ^ 2)
    hbounds (fun w hw => hlocal q ⟨hq0, hqQ⟩ w hw) hs y
  nlinarith [hC₁.le]

end RMF
