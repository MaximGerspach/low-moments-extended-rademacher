/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.StrongPNT
import RMF.PNTPlus.MediumPNTExplicit
import RMF.NumberTheory.ThetaClassicalBound

/-!
# The effective prime number theorem in the shape the crude range consumes

The block cosine estimates take the prime number theorem as `|θ t - t| ≤ Cθ · t/\log² t`.  The
effective prime number theorem for `θ`, `RMF.abs_theta_sub_le_exp_numeral_explicit`, has numeral
constants, `10⁴⁰` at rate `1/200`, but the shape `x·e^{-(1/200)(\log x)^{1/10}}`.

**The shape converts at no cost in effectivity**: at `u = (\log x)^{1/10}`,
`\log² x · e^{-cu} = u^{20} e^{-cu} ≤ 20!/c^{20}`, one term of the exponential series, so

`|θ x - x| ≤ RMF.thetaMediumConst · x/\log² x`

past the same threshold, with `RMF.thetaMediumConst = 10⁴⁰ · 20! · 200²⁰ ≈ 2.6·10¹⁰⁴` a
**numeral**.  This file proves the inequality and names the constant; the conversion is
`RMF.abs_theta_sub_le_medium_explicit`.
-/

open Real Chebyshev

namespace RMF

/-- **`\log² x · e^{-c(\log x)^{1/10}} ≤ 20!/c^{20}`**, from `y^{20}/20! ≤ e^y` at
`y = c(\log x)^{1/10}`: what the `t/\log² t` shape needs. -/
lemma sq_mul_exp_neg_rpow_tenth_le {c L : ℝ} (hc : 0 < c) (hL : 0 ≤ L) :
    L ^ 2 * Real.exp (-c * L ^ ((1 : ℝ) / 10)) ≤ 2432902008176640000 / c ^ 20 := by
  set u : ℝ := L ^ ((1 : ℝ) / 10) with hudef
  have hu0 : (0 : ℝ) ≤ u := Real.rpow_nonneg hL _
  have hu20 : u ^ (20 : ℕ) = L ^ 2 := by
    rw [hudef, ← Real.rpow_natCast (L ^ ((1 : ℝ) / 10)) 20, ← Real.rpow_mul hL]
    norm_num
  have hcu : (0 : ℝ) ≤ c * u := by positivity
  have h1 : c ^ 20 * u ^ 20 ≤ 2432902008176640000 * Real.exp (c * u) := by
    have h := Real.pow_div_factorial_le_exp (c * u) hcu 20
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Nat.factorial 20 : ℝ))] at h
    rw [mul_pow] at h
    norm_num at h
    linarith
  rw [← hu20, neg_mul, Real.exp_neg, ← div_eq_mul_inv,
    div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  linarith

/-- **The effective prime number theorem's constant in the `t/\log² t` shape**:
`10⁴⁰ · 20! · 200²⁰`. -/
noncomputable def thetaMediumConst : ℝ :=
  10 ^ (40 : ℕ) * (2432902008176640000 * 200 ^ (20 : ℕ))

/-- `RMF.thetaMediumConst` is positive. -/
lemma thetaMediumConst_pos : 0 < thetaMediumConst := by
  rw [thetaMediumConst]
  positivity

end RMF
