/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.MeanInequalities
import RMF.EulerProduct.Block
import RMF.EulerProduct.RademacherPrimeSum
import RMF.NumberTheory.LogPrimeSum
import RMF.Probability.RademacherFirstMoment
import RMF.Probability.RestrictedSecondMoment.Ranges
import RMF.Weighted.LineTail

/-!
# The central window: the two inputs

`Z = (log y)⁻¹∫_ℝ|F_y(½+σ+it)|²|σ+it|^{-2}dt` splits at `|t| ≤ 1/log y`, and the central piece
`Z_c` rests on the central-window bound

`E[(∫_{|t|≤c}|F_y(½+σ+it)|²dt)^q] ≪ c^q·E|F_y(½+σ)|^{2q}`  for `0 < c ≤ 2/log y`.

Plain Jensen in `ω` is **not** enough: it gives `(∫E|F|²)^q ≍ (c·log y)^q`, and since
`q(2q-1) < q` that overshoots `E|F_y(½+σ)|^{2q} ≍ (log y)^{q(2q-1)}` by `(log y)^{q(2-2q)}`.  This
is also why the `2/3` route of `RMF/Reduction/WindowDescent.lean` must be kept off the central
window — `E Z_c^{2/3}` is a power of `log x`.  This file proves the bound in the weighted form
`Z_c` needs (`RMF.integral_rpow_setIntegral_normSq_div_shiftLine_le`), and for a block of primes
to the left of `½` (`RMF.integral_rpow_setIntegral_normSq_div_shiftLine_primesIco_le`).

## The balanced Hölder

`RMF.integral_mul_rpow_le` is `E[A·B^q] ≤ (E A)^{1-q}(E[A·B])^q`, applied with `A = |F(0)|^{2q}`
and `B = (∫_{|t|≤c}|F(t)|²dt)/|F(0)|²`: Jensen under the `|F|^{2q}`-tilt, with no tilted measure,
since the tilt is Hölder at the conjugate pair `(1/(1-q), 1/q)`.

## The two-point ratio

The other input is `E[|F(0)|^{2q-2}|F(t)|²] ≪ E|F(0)|^{2q}` for `|t| ≤ 2/log y`.  Both sides
factor over the primes (`RMF.integral_prod_norm_one_add_mul_rpow_rademacherLaw`, exponents of
either sign), and with `a = p^{-½-σ}`, `v = a·cos(t log p)` the per-prime ratio is the identity
`N = D + (a-v)·[(1-a)^{2q-2} - (1+a)^{2q-2}]`, so no Taylor expansion is needed
(`RMF.two_point_local_ratio_le`).

## No dyadic split

The tilt lives in `ω`, so a weight `ρ(t) ≥ 0` rides through Fubini
(`RMF.integral_rpow_setIntegral_weight_normSq_shiftLine_primesIco_le`), and
`∫_{|t|≤w}(σ²+t²)^{-1} ≤ π/σ` (`RMF.setIntegral_inv_sq_add_sq_le`) gives the factor `1/σ` of
`Z_c`'s `|σ+it|^{-2}` directly, for every `0 ≤ q ≤ 1`, with no dyadic split of `|t| ≤ 1/log y`.
The constants are explicit and far from sharp: the `8192` of `RMF.two_point_local_ratio_le` gives
the `e^{143800}` of the two-point ratio.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The balanced Hölder -/

/-- **`E[A·B^q] ≤ (E A)^{1-q}·(E[A·B])^q`** for nonnegative `A`, `B` and `0 ≤ q ≤ 1`.

Hölder at the conjugate pair `(1/(1-q), 1/q)`, which is the `A`-tilt of Jensen written without a
tilted measure: pointwise it is the weighted AM–GM
`(A/α)^{1-q}·(AB/β)^q ≤ (1-q)(A/α) + q(AB/β)`, and the right-hand side integrates to `1` at
`α = E A`, `β = E[A·B]`. -/
theorem integral_mul_rpow_le {μ : Measure Ω} {A B : Ω → ℝ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hA : ∀ᵐ ω ∂μ, 0 ≤ A ω) (hB : ∀ᵐ ω ∂μ, 0 ≤ B ω)
    (hAi : Integrable A μ) (hABi : Integrable (fun ω => A ω * B ω) μ)
    (hi : Integrable (fun ω => A ω * B ω ^ q) μ)
    (hα : 0 < ∫ ω, A ω ∂μ) (hβ : 0 < ∫ ω, A ω * B ω ∂μ) :
    (∫ ω, A ω * B ω ^ q ∂μ)
      ≤ (∫ ω, A ω ∂μ) ^ (1 - q) * (∫ ω, A ω * B ω ∂μ) ^ q := by
  set α : ℝ := ∫ ω, A ω ∂μ with hαdef
  set β : ℝ := ∫ ω, A ω * B ω ∂μ with hβdef
  have hcoef : (0 : ℝ) ≤ α ^ (1 - q) * β ^ q :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (Real.rpow_nonneg hβ.le _)
  -- the pointwise weighted AM–GM
  have key : ∀ᵐ ω ∂μ, A ω * B ω ^ q
      ≤ α ^ (1 - q) * β ^ q * ((1 - q) * (A ω / α) + q * (A ω * B ω / β)) := by
    filter_upwards [hA, hB] with ω hAω hBω
    have hgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - q) (w₂ := q)
      (p₁ := A ω / α) (p₂ := A ω * B ω / β) (by linarith) hq0
      (div_nonneg hAω hα.le) (div_nonneg (mul_nonneg hAω hBω) hβ.le) (by ring)
    have hAsum : A ω ^ (1 - q) * A ω ^ q = A ω := by
      rw [← Real.rpow_add' hAω (by simp)]
      norm_num
    have hsplit : (A ω / α) ^ (1 - q) * (A ω * B ω / β) ^ q
        = (α ^ (1 - q) * β ^ q)⁻¹ * (A ω * B ω ^ q) := by
      rw [Real.div_rpow hAω hα.le,
        Real.div_rpow (mul_nonneg hAω hBω) hβ.le,
        Real.mul_rpow hAω hBω, div_mul_div_comm, ← mul_assoc, hAsum,
        div_eq_inv_mul]
    rw [hsplit] at hgm
    have := mul_le_mul_of_nonneg_left hgm hcoef
    rwa [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this
  -- integrate, and the right-hand side is `α^{1-q}β^q`
  have hrhs : Integrable (fun ω => α ^ (1 - q) * β ^ q
      * ((1 - q) * (A ω / α) + q * (A ω * B ω / β))) μ := by
    refine Integrable.const_mul ?_ _
    exact ((hAi.div_const α).const_mul _).add ((hABi.div_const β).const_mul _)
  refine le_trans (integral_mono_ae hi hrhs key) (le_of_eq ?_)
  rw [integral_const_mul, integral_add ((hAi.div_const α).const_mul _)
    ((hABi.div_const β).const_mul _), integral_const_mul, integral_const_mul,
    integral_div, integral_div, ← hαdef, ← hβdef]
  field_simp
  ring

/-! ### The two-point local ratio -/

/-- **The bracket.**  `(1-a)^{2q-2} - (1+a)^{2q-2} ≤ 2(2-2q)·a/(1-a)³` for `0 ≤ a ≤ 3/4`,
`0 ≤ q ≤ 1`.

`e^{mL₁} - e^{-mL₂}` with `L₁ = -log(1-a)`, `L₂ = log(1+a)`, split as
`(e^{mL₁} - 1) + (1 - e^{-mL₂})` and bounded by `mL₁e^{mL₁}` and `mL₂`; then `L₁ ≤ a/(1-a)`,
`L₂ ≤ a` and `e^{mL₁} = (1-a)^{-m} ≤ (1-a)^{-2}`. -/
theorem rpow_sub_rpow_le {a q : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 3 / 4)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - a) ^ (2 * q - 2) - (1 + a) ^ (2 * q - 2)
      ≤ 2 * (2 - 2 * q) * a / (1 - a) ^ 3 := by
  have hB : (0 : ℝ) < 1 - a := by linarith
  have hB1 : (1 - a) ≤ 1 := by linarith
  have hA : (0 : ℝ) < 1 + a := by linarith
  set m : ℝ := 2 - 2 * q with hmdef
  have hm0 : (0 : ℝ) ≤ m := by simp only [hmdef]; linarith
  have hm2 : m ≤ 2 := by simp only [hmdef]; linarith
  -- the two logarithms
  have hL2 : Real.log (1 + a) ≤ a := by
    have := Real.log_le_sub_one_of_pos hA
    linarith
  have hL20 : (0 : ℝ) ≤ Real.log (1 + a) := Real.log_nonneg (by linarith)
  have hL1 : -Real.log (1 - a) ≤ a / (1 - a) := by
    have h := Real.log_le_sub_one_of_pos (x := (1 - a)⁻¹) (by positivity)
    rw [Real.log_inv] at h
    have hid : (1 - a)⁻¹ - 1 = a / (1 - a) := by
      rw [eq_div_iff hB.ne', sub_mul, inv_mul_cancel₀ hB.ne']
      ring
    linarith [hid.le, hid.ge]
  have hL10 : (0 : ℝ) ≤ -Real.log (1 - a) := by
    have := Real.log_nonpos (by linarith) hB1
    linarith
  -- the two exponentials
  have hexpB : (1 - a) ^ (2 * q - 2) = Real.exp (m * (-Real.log (1 - a))) := by
    rw [Real.rpow_def_of_pos hB]
    congr 1
    simp only [hmdef]
    ring
  have hexpA : (1 + a) ^ (2 * q - 2) = Real.exp (-(m * Real.log (1 + a))) := by
    rw [Real.rpow_def_of_pos hA]
    congr 1
    simp only [hmdef]
    ring
  -- `e^{mL₁} ≤ (1-a)^{-2}`
  have hcap : Real.exp (m * (-Real.log (1 - a))) ≤ ((1 - a) ^ 2)⁻¹ := by
    rw [← hexpB]
    have hstep : (1 - a) ^ (2 * q - 2) ≤ (1 - a) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hB hB1 (by linarith)
    have hid : (1 - a) ^ (-2 : ℝ) = ((1 - a) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hB.le, ← Real.rpow_natCast (1 - a) 2]
      norm_num
    linarith [hid.le, hid.ge]
  -- `e^x - 1 ≤ x e^x` and `1 - e^{-y} ≤ y`
  have hup : Real.exp (m * (-Real.log (1 - a))) - 1
      ≤ (m * (-Real.log (1 - a))) * Real.exp (m * (-Real.log (1 - a))) := by
    have h := Real.add_one_le_exp (-(m * (-Real.log (1 - a))))
    rw [Real.exp_neg] at h
    have hp : (0 : ℝ) < Real.exp (m * (-Real.log (1 - a))) := Real.exp_pos _
    have := mul_le_mul_of_nonneg_right h hp.le
    rw [inv_mul_cancel₀ hp.ne'] at this
    nlinarith [this]
  have hdown : 1 - Real.exp (-(m * Real.log (1 + a))) ≤ m * Real.log (1 + a) := by
    have h := Real.add_one_le_exp (-(m * Real.log (1 + a)))
    linarith
  -- assemble
  have hprod : (m * (-Real.log (1 - a))) * Real.exp (m * (-Real.log (1 - a)))
      ≤ m * (a / (1 - a)) * ((1 - a) ^ 2)⁻¹ := by
    have h1 : (0 : ℝ) ≤ m * (-Real.log (1 - a)) := mul_nonneg hm0 hL10
    have h2 : m * (-Real.log (1 - a)) ≤ m * (a / (1 - a)) :=
      mul_le_mul_of_nonneg_left hL1 hm0
    have h3 : (0 : ℝ) ≤ m * (a / (1 - a)) := mul_nonneg hm0 (by positivity)
    nlinarith [hcap, Real.exp_pos (m * (-Real.log (1 - a)))]
  have hsmall : m * Real.log (1 + a) ≤ m * (a / (1 - a)) * ((1 - a) ^ 2)⁻¹ := by
    have h1 : m * Real.log (1 + a) ≤ m * a := mul_le_mul_of_nonneg_left hL2 hm0
    have h2 : m * a ≤ m * (a / (1 - a)) * ((1 - a) ^ 2)⁻¹ := by
      have hpow : (1 - a) ^ 3 ≤ 1 := by nlinarith
      have hid : m * (a / (1 - a)) * ((1 - a) ^ 2)⁻¹ = m * a / (1 - a) ^ 3 := by
        field_simp
      rw [hid, le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg hm0 ha0]
    linarith
  rw [hexpB, hexpA]
  have hkey : Real.exp (m * (-Real.log (1 - a))) - Real.exp (-(m * Real.log (1 + a)))
      ≤ 2 * (m * (a / (1 - a)) * ((1 - a) ^ 2)⁻¹) := by linarith
  refine hkey.trans (le_of_eq ?_)
  field_simp

/-- **The two-point local ratio.**  For `0 ≤ a ≤ 3/4`, `v ≤ a` and `0 ≤ q ≤ 1`, in closed form:
the mixed moment `E[|1+Xa|^{2q-2}|1+Xw|²]`, `Re w = v`, `|w| = a`, is at most `(1 + 8192·a(a-v))`
times the plain moment `E|1+Xa|^{2q}` (with `a = p^{-½-σ}`, `w = p^{-(½+σ+it)}` in mind).
`N = D + (a-v)·[(1-a)^{2q-2}-(1+a)^{2q-2}]` is an identity, `1±2v+a² = (1±a)² ∓ 2(a-v)`, and the
bracket is `RMF.rpow_sub_rpow_le`.  Summed over `p ≤ y`, `a(a-v) = a²(1-cos(t log p))` costs
`∑_p (log p)²/p`, which confines the estimate to `|t| ≪ 1/log y`. -/
theorem two_point_local_ratio_le {a v q : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 3 / 4)
    (hav : v ≤ a) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ((1 + a) ^ (2 * q - 2) * (1 + 2 * v + a ^ 2)
        + (1 - a) ^ (2 * q - 2) * (1 - 2 * v + a ^ 2)) / 2
      ≤ ((1 + a) ^ (2 * q) + (1 - a) ^ (2 * q)) / 2 * (1 + 8192 * (a * (a - v))) := by
  have hB : (0 : ℝ) < 1 - a := by linarith
  have hB1 : (1 - a) ≤ 1 := by linarith
  have hA : (0 : ℝ) < 1 + a := by linarith
  have hav0 : (0 : ℝ) ≤ a - v := by linarith
  -- `x^{2q-2}·x² = x^{2q}`
  have e1 : (1 + a) ^ (2 * q - 2) * ((1 + a) ^ 2) = (1 + a) ^ (2 * q) := by
    rw [← Real.rpow_natCast (1 + a) 2, ← Real.rpow_add hA]
    norm_num
  have e2 : (1 - a) ^ (2 * q - 2) * ((1 - a) ^ 2) = (1 - a) ^ (2 * q) := by
    rw [← Real.rpow_natCast (1 - a) 2, ← Real.rpow_add hB]
    norm_num
  -- the identity
  have hid : ((1 + a) ^ (2 * q - 2) * (1 + 2 * v + a ^ 2)
        + (1 - a) ^ (2 * q - 2) * (1 - 2 * v + a ^ 2)) / 2
      = ((1 + a) ^ (2 * q) + (1 - a) ^ (2 * q)) / 2
        + (a - v) * ((1 - a) ^ (2 * q - 2) - (1 + a) ^ (2 * q - 2)) := by
    rw [← e1, ← e2]
    ring
  -- the plain moment is at least `(1-a)²`
  have hDlow : (1 - a) ^ 2 ≤ ((1 + a) ^ (2 * q) + (1 - a) ^ (2 * q)) / 2 := by
    have h1 : (1 - a) ^ (2 * q) ≤ (1 + a) ^ (2 * q) :=
      Real.rpow_le_rpow hB.le (by linarith) (by linarith)
    have h2 : (1 - a) ^ 2 ≤ (1 - a) ^ (2 * q) := by
      have := Real.rpow_le_rpow_of_exponent_ge hB hB1 (show 2 * q ≤ (2 : ℝ) by linarith)
      rw [← Real.rpow_natCast (1 - a) 2]
      push_cast
      linarith
    linarith
  -- the bracket
  have hbr := rpow_sub_rpow_le ha0 ha hq0 hq1
  have hstep : (a - v) * ((1 - a) ^ (2 * q - 2) - (1 + a) ^ (2 * q - 2))
      ≤ (a - v) * (4 * a / (1 - a) ^ 3) := by
    refine mul_le_mul_of_nonneg_left (le_trans hbr ?_) hav0
    have hnum : 2 * (2 - 2 * q) * a ≤ 4 * a := by nlinarith
    exact div_le_div_of_nonneg_right hnum (by positivity) |>.trans_eq rfl
  have hprod0 : (0 : ℝ) ≤ a * (a - v) := mul_nonneg ha0 hav0
  have h5' : ((1 : ℝ) / 4) ^ 5 ≤ (1 - a) ^ 5 :=
    pow_le_pow_left₀ (by norm_num) (by linarith : (1 : ℝ) / 4 ≤ 1 - a) 5
  have h5 : (4 : ℝ) ≤ 8192 * (1 - a) ^ 5 := by
    have hv : ((1 : ℝ) / 4) ^ 5 = 1 / 1024 := by norm_num
    rw [hv] at h5'
    linarith
  have hfin : (a - v) * (4 * a / (1 - a) ^ 3)
      ≤ ((1 + a) ^ (2 * q) + (1 - a) ^ (2 * q)) / 2 * (8192 * (a * (a - v))) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hDlow (by linarith))
    rw [show (a - v) * (4 * a / (1 - a) ^ 3) = 4 * (a * (a - v)) / (1 - a) ^ 3 by ring,
      div_le_iff₀ (by positivity : (0 : ℝ) < (1 - a) ^ 3)]
    nlinarith [mul_le_mul_of_nonneg_right h5 hprod0]
  rw [hid]
  nlinarith [hstep, hfin]

/-! ### The local ratio, at the law -/

/-- **The two-point Rademacher local moment**, in closed form: the `Fin 2` case of
`RMF.integral_prod_norm_one_add_mul_rpow_rademacherLaw`.  Both exponents are free and may have
either sign, which is what a *ratio* of Euler products costs. -/
lemma integral_norm_one_add_mul_rpow_mul_rademacherLaw (q r : ℝ) (w w' : ℂ) :
    (∫ z, ‖1 + z * w‖ ^ (2 * q) * ‖1 + z * w'‖ ^ (2 * r) ∂rademacherLaw)
      = ((1 + 2 * w.re + ‖w‖ ^ 2) ^ q * (1 + 2 * w'.re + ‖w'‖ ^ 2) ^ r
          + (1 - 2 * w.re + ‖w‖ ^ 2) ^ q * (1 - 2 * w'.re + ‖w'‖ ^ 2) ^ r) / 2 := by
  have h := integral_prod_norm_one_add_mul_rpow_rademacherLaw
    (Finset.univ : Finset (Fin 2)) ![q, r] ![w, w']
  simpa [Fin.prod_univ_two] using h

/-- **The local ratio at one prime.**  For `w` a nonnegative real of size at most `3/4`, `w'` of
the same modulus and `0 ≤ q ≤ 1`,
`E[‖1+Xw‖^{2q-2}‖1+Xw'‖²] ≤ (1 + 8192·‖w‖(‖w‖ - Re w'))·E‖1+Xw‖^{2q}`:
`RMF.two_point_local_ratio_le` read through the closed forms; `‖w‖(‖w‖-Re w') = ‖w‖²(1-cos θ)`
is the quantity that sums to `t²∑_p(log p)²/p` over the primes. -/
lemma integral_two_point_rademacherLaw_le {w w' : ℂ} {q : ℝ}
    (hre : w.re = ‖w‖) (hw : ‖w‖ ≤ 3 / 4) (hw' : ‖w'‖ = ‖w‖)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ z, ‖1 + z * w‖ ^ (2 * (q - 1)) * ‖1 + z * w'‖ ^ (2 * (1 : ℝ)) ∂rademacherLaw)
      ≤ (1 + 8192 * (‖w‖ * (‖w‖ - w'.re)))
          * ∫ z, ‖1 + z * w‖ ^ (2 * q) ∂rademacherLaw := by
  set a : ℝ := ‖w‖ with hadef
  have ha0 : (0 : ℝ) ≤ a := norm_nonneg w
  have hav : w'.re ≤ a := hw' ▸ Complex.re_le_norm w'
  have hpos : (0 : ℝ) < 1 + a := by linarith
  have hneg : (0 : ℝ) < 1 - a := by linarith
  -- `(1 ± a)²` raised to a real power
  have hp1 : ∀ c : ℝ, ((1 + a) ^ 2 : ℝ) ^ c = (1 + a) ^ (2 * c) := fun c => by
    rw [← Real.rpow_natCast (1 + a) 2, ← Real.rpow_mul hpos.le]
    norm_num
  have hp2 : ∀ c : ℝ, ((1 - a) ^ 2 : ℝ) ^ c = (1 - a) ^ (2 * c) := fun c => by
    rw [← Real.rpow_natCast (1 - a) 2, ← Real.rpow_mul hneg.le]
    norm_num
  have hsq1 : (1 : ℝ) + 2 * a + a ^ 2 = (1 + a) ^ 2 := by ring
  have hsq2 : (1 : ℝ) - 2 * a + a ^ 2 = (1 - a) ^ 2 := by ring
  have he1 : (2 : ℝ) * (q - 1) = 2 * q - 2 := by ring
  rw [integral_norm_one_add_mul_rpow_mul_rademacherLaw,
    integral_norm_one_add_mul_rpow_rademacherLaw, hre, hw', hsq1, hsq2, hp1, hp2, hp1, hp2,
    Real.rpow_one, Real.rpow_one, he1]
  have hkey := two_point_local_ratio_le (a := a) (v := w'.re) (q := q) ha0 hw hav hq0 hq1
  linarith

/-! ### The ratio over the primes -/

/-- `p^{-c}` at a real `c` is a positive real. -/
lemma natCast_cpow_neg_ofReal (n : ℕ) (c : ℝ) :
    ((n : ℂ) ^ (-(c : ℂ))) = (((n : ℝ) ^ (-c) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]

lemma re_natCast_cpow_neg_ofReal (n : ℕ) (c : ℝ) :
    ((n : ℂ) ^ (-(c : ℂ))).re = (n : ℝ) ^ (-c) := by
  rw [natCast_cpow_neg_ofReal, Complex.ofReal_re]

/-- **`p^{-c} ≤ 3/4` at every prime, already for `c ≥ 5/12`.**  The bound is `2^{-5/12} = 0.7492…`,
so the smallest prime still decides it, with the margin `(4/3)^{12} = 31.57… ≤ 32 = 2^5`.  This is
the widening that lets the two-point ratio run to the left of `½`: at the shift `½ - 1/(2 log z)`
of a band's central window it needs only `log z ≥ 6`. -/
lemma prime_rpow_neg_le_three_quarters_of_five_twelfths {p : ℕ} (hp : p.Prime) {c : ℝ}
    (hc : 5 / 12 ≤ c) : (p : ℝ) ^ (-c) ≤ 3 / 4 := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h1 : ((p : ℝ)) ^ (-c) ≤ (2 : ℝ) ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by linarith)
  have h3 : (2 : ℝ) ^ (-c) ≤ (2 : ℝ) ^ (-(5 / 12) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  -- `4/3 ≤ 2^{5/12}`, from `(4/3)^12 ≤ 32 = (2^{5/12})^12`
  have hpow : ((2 : ℝ) ^ ((5 : ℝ) / 12)) ^ (12 : ℕ) = 32 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h5 : (5 : ℝ) / 12 * ((12 : ℕ) : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
    rw [h5, Real.rpow_natCast]
    norm_num
  have h43 : (4 : ℝ) / 3 ≤ (2 : ℝ) ^ ((5 : ℝ) / 12) := by
    refine le_of_pow_le_pow_left₀ (n := 12) (by norm_num) (by positivity) ?_
    rw [hpow]
    norm_num
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((5 : ℝ) / 12) := by positivity
  have h4 : (2 : ℝ) ^ (-(5 / 12) : ℝ) ≤ 3 / 4 := by
    rw [Real.rpow_neg (by norm_num), inv_eq_one_div, div_le_iff₀ hpos]
    linarith
  linarith

/-- **The mixed moment against the plain one, for a block of primes.**  For a real `c ≥ 5/12`, any
`s₁` with `Re s₁ = c` and `0 ≤ q ≤ 1`, with `F` the product over the block `y₀ ≤ p < y₁`,
`E[‖F(c)‖^{2q-2}‖F(s₁)‖²] ≤ ∏_{y₀≤p<y₁}(1 + 8192·p^{-c}(p^{-c} - Re p^{-s₁}))·E‖F(c)‖^{2q}`.
Both sides factor over the primes (`RMF.integral_prod_norm_randomEulerProductIco_rpow_sqfree`), and
each prime is `RMF.integral_two_point_rademacherLaw_le`, whose size hypothesis `p^{-c} ≤ 3/4` is
`RMF.prime_rpow_neg_le_three_quarters_of_five_twelfths`. -/
theorem integral_mixed_norm_randomEulerProductIco_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {c q : ℝ} {s₁ : ℂ}
    (hc : 5 / 12 ≤ c) (hre : s₁.re = c) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ (c : ℂ) ω‖
          ^ (2 * (q - 1))
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₁ ω‖
          ^ (2 * (1 : ℝ)) ∂μ)
      ≤ (∏ p ∈ primesIco y₀ y₁,
            (1 + 8192 * ((p : ℝ) ^ (-c) * ((p : ℝ) ^ (-c) - ((p : ℂ) ^ (-s₁)).re))))
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (c : ℂ) ω‖ ^ (2 * q) ∂μ := by
  have hsvec : ∀ j ∈ (Finset.univ : Finset (Fin 2)), 0 < (![(c : ℂ), s₁] j).re := by
    intro j _
    fin_cases j <;> simp [hre] <;> linarith
  have hL : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (c : ℂ) ω‖ ^ (2 * (q - 1))
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₁ ω‖
          ^ (2 * (1 : ℝ)) ∂μ)
      = ∏ p ∈ primesIco y₀ y₁, ∫ z, ‖1 + z * (p : ℂ) ^ (-(c : ℂ))‖ ^ (2 * (q - 1))
          * ‖1 + z * (p : ℂ) ^ (-s₁)‖ ^ (2 * (1 : ℝ)) ∂rademacherLaw := by
    have h := integral_prod_norm_randomEulerProductIco_rpow_sqfree hX norm_le_one_rademacherLaw
      y₀ y₁ (Finset.univ : Finset (Fin 2)) hsvec (q := ![q - 1, 1])
    simpa [Fin.prod_univ_two] using h
  have hR : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        (c : ℂ) ω‖ ^ (2 * q) ∂μ)
      = ∏ p ∈ primesIco y₀ y₁,
          ∫ z, ‖1 + z * (p : ℂ) ^ (-(c : ℂ))‖ ^ (2 * q) ∂rademacherLaw := by
    have h := integral_prod_norm_randomEulerProductIco_rpow_sqfree hX norm_le_one_rademacherLaw
      y₀ y₁ (Finset.univ : Finset (Fin 1)) (s := ![(c : ℂ)])
      (fun j _ => by fin_cases j; simp; linarith) (q := ![q])
    simpa [Fin.prod_univ_one] using h
  rw [hL, hR, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p _ => integral_nonneg fun z => ?_) ?_
  · exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)
  intro p hp
  have hp2 := prime_of_mem_primesIco hp
  have hnorm : ‖(p : ℂ) ^ (-(c : ℂ))‖ = (p : ℝ) ^ (-c) := by
    rw [Complex.norm_natCast_cpow_of_pos hp2.pos]
    norm_num
  have hnorm' : ‖(p : ℂ) ^ (-s₁)‖ = (p : ℝ) ^ (-c) := by
    rw [Complex.norm_natCast_cpow_of_pos hp2.pos, Complex.neg_re, hre]
  have hb := integral_two_point_rademacherLaw_le (w := (p : ℂ) ^ (-(c : ℂ)))
    (w' := (p : ℂ) ^ (-s₁)) (q := q) (by rw [hnorm, re_natCast_cpow_neg_ofReal])
    (by rw [hnorm]; exact prime_rpow_neg_le_three_quarters_of_five_twelfths hp2 hc)
    (by rw [hnorm, hnorm']) hq0 hq1
  rwa [hnorm] at hb

/-! ### The prime sum that confines the window -/

/-- **`∑_{p<y}(log p)²/p ≤ log y·(log y + log 4 + 4)`.**  `log p ≤ log y` pulls one logarithm
out and `RMF.sum_log_div_prime_le` — Mertens' first theorem, one-sided — bounds the rest.
This `∑_{p≤y}(log p)²/p ≪ (log y)²` confines the central window to `|t| ≪ 1/log y`. -/
lemma sum_log_sq_div_primesBelow_le {y : ℕ} (hy : 1 ≤ y) :
    ∑ p ∈ Nat.primesBelow y, Real.log p ^ 2 / p
      ≤ Real.log y * (Real.log y + Real.log 4 + 4) := by
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy1
  have hfloor : ⌊(y : ℝ)⌋₊ = y := Nat.floor_natCast y
  -- pull one logarithm out
  have hstep : ∀ p ∈ Nat.primesBelow y,
      Real.log p ^ 2 / p ≤ Real.log y * (Real.log p / p) := by
    intro p hp
    have hp2 := Nat.prime_of_mem_primesBelow hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp2.pos
    have hple : (p : ℝ) ≤ (y : ℝ) := by exact_mod_cast (Nat.lt_of_mem_primesBelow hp).le
    have hml : Real.log p ≤ Real.log y := Real.log_le_log hp0 hple
    have hid : Real.log p ^ 2 / (p : ℝ) = Real.log p * (Real.log p / p) := by ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right hml
      (div_nonneg (Real.log_natCast_nonneg p) hp0.le)
  have hsum1 : ∑ p ∈ Nat.primesBelow y, Real.log p ^ 2 / p
      ≤ Real.log y * ∑ p ∈ Nat.primesBelow y, Real.log p / p := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hstep
  -- Mertens
  have hmert := sum_log_div_prime_le hy1
  rw [hfloor] at hmert
  have hsub : Nat.primesBelow y ⊆ {p ∈ Finset.Ioc 0 y | p.Prime} := by
    intro p hp
    have hp2 := Nat.prime_of_mem_primesBelow hp
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hp2.pos, (Nat.lt_of_mem_primesBelow hp).le⟩, hp2⟩
  have hsum2 : ∑ p ∈ Nat.primesBelow y, Real.log p / p
      ≤ Real.log y + Real.log 4 + 4 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))) hmert
  calc ∑ p ∈ Nat.primesBelow y, Real.log p ^ 2 / p
      ≤ Real.log y * ∑ p ∈ Nat.primesBelow y, Real.log p / p := hsum1
    _ ≤ Real.log y * (Real.log y + Real.log 4 + 4) :=
        mul_le_mul_of_nonneg_left hsum2 hlogy

/-- The block form of `RMF.sum_log_sq_div_primesBelow_le`: a block below `y₁` sits inside the
primes below `y₁`. -/
lemma sum_log_sq_div_primesIco_le {y₀ y₁ : ℕ} (hy : 1 ≤ y₁) :
    ∑ p ∈ primesIco y₀ y₁, Real.log p ^ 2 / p
      ≤ Real.log y₁ * (Real.log y₁ + Real.log 4 + 4) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => ?_)
    (sum_log_sq_div_primesBelow_le hy)
  · intro p hp
    obtain ⟨hprime, -, hlt⟩ := mem_primesIco.1 hp
    exact Nat.mem_primesBelow.2 ⟨hlt, hprime⟩
  · exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg p)

/-! ### The product of the local ratios -/

/-- **The product of the local ratios, over any set of primes.**  If `p^{-c}·p^{-c} ≤ K/p` on `S`
and `Re s₁ = c`, then
`∏_{p∈S}(1 + 8192·p^{-c}(p^{-c} - Re p^{-s₁})) ≤ exp(4096·K·t²∑_{p∈S}(log p)²/p)`,  `t = Im s₁`,
by `1 - cos θ ≤ θ²/2` and `1 + u ≤ e^u`.  At `c ≥ ½` the hypothesis holds with `K = 1`
(`RMF.prime_rpow_neg_mul_self_le_inv`); to the left of `½` it is where the shift is paid for. -/
theorem prod_one_add_two_point_le_of_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {c K : ℝ}
    {s₁ : ℂ} (hre : s₁.re = c)
    (hK : ∀ p ∈ S, (p : ℝ) ^ (-c) * (p : ℝ) ^ (-c) ≤ K * ((p : ℝ))⁻¹) :
    (∏ p ∈ S, (1 + 8192 * ((p : ℝ) ^ (-c) * ((p : ℝ) ^ (-c) - ((p : ℂ) ^ (-s₁)).re))))
      ≤ Real.exp (4096 * K * s₁.im ^ 2 * ∑ p ∈ S, Real.log p ^ 2 / p) := by
  set f : ℕ → ℝ := fun p =>
    8192 * ((p : ℝ) ^ (-c) * ((p : ℝ) ^ (-c) - ((p : ℂ) ^ (-s₁)).re)) with hfdef
  -- each factor, rewritten
  have hkey : ∀ p ∈ S, 0 ≤ f p ∧ f p ≤ 4096 * K * s₁.im ^ 2 * (Real.log p ^ 2 / p) := by
    intro p hp
    have hp2 := hS p hp
    have hA0 : (0 : ℝ) ≤ (p : ℝ) ^ (-c) * (p : ℝ) ^ (-c) := by positivity
    have hA1 := hK p hp
    -- `1 - cos θ ∈ [0, θ²/2]`
    have hC0 : (0 : ℝ) ≤ 1 - Real.cos (s₁.im * Real.log p) := by
      linarith [Real.cos_le_one (s₁.im * Real.log p)]
    have hC1 : 1 - Real.cos (s₁.im * Real.log p) ≤ (s₁.im * Real.log p) ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := s₁.im * Real.log p)]
    have hfeq : f p
        = 8192 * (((p : ℝ) ^ (-c) * (p : ℝ) ^ (-c))
            * (1 - Real.cos (s₁.im * Real.log p))) := by
      rw [hfdef]
      simp only
      rw [re_natCast_cpow_neg hp2.pos, hre]
      ring
    have hmul : ((p : ℝ) ^ (-c) * (p : ℝ) ^ (-c)) * (1 - Real.cos (s₁.im * Real.log p))
        ≤ (K * ((p : ℝ))⁻¹) * ((s₁.im * Real.log p) ^ 2 / 2) :=
      mul_le_mul hA1 hC1 hC0 (le_trans hA0 hA1)
    refine ⟨by rw [hfeq]; positivity, ?_⟩
    rw [hfeq, div_eq_mul_inv]
    nlinarith [hmul]
  -- `∏(1+f) ≤ exp(∑ f) ≤ exp(4096 K t²∑(log p)²/p)`
  have hsum : ∑ p ∈ S, f p ≤ 4096 * K * s₁.im ^ 2 * ∑ p ∈ S, Real.log p ^ 2 / p := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => (hkey p hp).2
  calc ∏ p ∈ S, (1 + f p)
      ≤ ∏ p ∈ S, Real.exp (f p) :=
        Finset.prod_le_prod (fun p hp => by linarith [(hkey p hp).1])
          (fun p _ => (add_comm 1 (f p)).le.trans (Real.add_one_le_exp _))
    _ = Real.exp (∑ p ∈ S, f p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (4096 * K * s₁.im ^ 2 * ∑ p ∈ S, Real.log p ^ 2 / p) := Real.exp_le_exp.2 hsum

/-- At `c ≥ ½`, `p^{-c}·p^{-c} ≤ 1/p`: the hypothesis of `RMF.prod_one_add_two_point_le_of_le` at
`K = 1`. -/
lemma prime_rpow_neg_mul_self_le_inv {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : 1 / 2 ≤ c) :
    (p : ℝ) ^ (-c) * (p : ℝ) ^ (-c) ≤ 1 * ((p : ℝ))⁻¹ := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  rw [one_mul, ← Real.rpow_add hp0]
  have h2 : (p : ℝ) ^ (-c + -c) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  rwa [Real.rpow_neg_one] at h2

/-! ### The ratio is bounded on the central window -/

/-- **The two-point ratio on the central window, for a block of primes.**  For `y₁ ≥ 2`,
`|Im s₁|·log y₁ ≤ 2`, `c = Re s₁ ≥ 5/12`, `p^{-c}·p^{-c} ≤ K/p` on the block, `K ≥ 0`, `0 ≤ q ≤ 1`,
`E[‖F(c)‖^{2q-2}‖F(s₁)‖²] ≤ e^{143800·K}·E‖F(c)‖^{2q}`, `F` the product over `y₀ ≤ p < y₁`:
`RMF.integral_mixed_norm_randomEulerProductIco_le` and `RMF.prod_one_add_two_point_le_of_le`,
the prime sum over the block bounded by the sum below `y₁` (`RMF.sum_log_sq_div_primesIco_le`),
and `4096·t²·log y₁·(log y₁ + log 4 + 4) ≤ 143800` for `|t|·log y₁ ≤ 2`. -/
theorem integral_mixed_norm_randomEulerProductIco_le_exp {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y₀ y₁ : ℕ} (hy : 2 ≤ y₁) {c q K : ℝ} {s₁ : ℂ}
    (hc : 5 / 12 ≤ c) (hre : s₁.re = c) (ht : |s₁.im| * Real.log y₁ ≤ 2)
    (hK : ∀ p ∈ primesIco y₀ y₁, (p : ℝ) ^ (-c) * (p : ℝ) ^ (-c) ≤ K * ((p : ℝ))⁻¹)
    (hK0 : 0 ≤ K) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ (c : ℂ) ω‖
          ^ (2 * (q - 1))
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₁ ω‖
          ^ (2 * (1 : ℝ)) ∂μ)
      ≤ Real.exp (143800 * K)
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (c : ℂ) ω‖ ^ (2 * q) ∂μ := by
  -- the two logarithms
  have hL2 : (6931 : ℝ) / 10000 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hL2' : Real.log 2 ≤ (6932 : ℝ) / 10000 := by
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hLy : Real.log 2 ≤ Real.log y₁ :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hy)
  have hLpos : (0 : ℝ) < Real.log y₁ := by linarith
  -- `t²(log y₁)² ≤ 4` and `t² log y₁ ≤ 4/log 2`
  have hnn : (0 : ℝ) ≤ |s₁.im| * Real.log y₁ := mul_nonneg (abs_nonneg _) hLpos.le
  have hTL : s₁.im ^ 2 * Real.log y₁ ^ 2 ≤ 4 := by
    nlinarith [sq_abs s₁.im, mul_self_le_mul_self hnn ht]
  have h1 : (0 : ℝ) ≤ s₁.im ^ 2 * Real.log y₁ := mul_nonneg (sq_nonneg _) hLpos.le
  have h4 : s₁.im ^ 2 * Real.log y₁ ≤ 57712 / 10000 := by
    nlinarith [hTL, hLy, hL2, hLpos, sq_nonneg s₁.im,
      mul_nonneg (mul_nonneg (sq_nonneg s₁.im) hLpos.le) (sub_nonneg.2 hLy)]
  -- the numeric bound on the exponent
  have hnum : 4096 * s₁.im ^ 2 * (Real.log y₁ * (Real.log y₁ + Real.log 4 + 4)) ≤ 143800 := by
    have hexp : 4096 * s₁.im ^ 2 * (Real.log y₁ * (Real.log y₁ + Real.log 4 + 4))
        = 4096 * (s₁.im ^ 2 * Real.log y₁ ^ 2)
          + 4096 * (Real.log 4 + 4) * (s₁.im ^ 2 * Real.log y₁) := by ring
    rw [hexp, hlog4]
    nlinarith [hTL, h4, h1,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 53864 / 10000 - (2 * Real.log 2 + 4)) h1]
  -- assemble
  have hmix := integral_mixed_norm_randomEulerProductIco_le hX y₀ y₁ hc hre hq0 hq1
  have hprod := prod_one_add_two_point_le_of_le (S := primesIco y₀ y₁)
    (fun p hp => prime_of_mem_primesIco hp) hre hK
  have hsum := sum_log_sq_div_primesIco_le (y₀ := y₀) (y₁ := y₁) (by omega)
  have hR0 : (0 : ℝ)
      ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (c : ℂ) ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hstep : Real.exp (4096 * K * s₁.im ^ 2 * ∑ p ∈ primesIco y₀ y₁, Real.log p ^ 2 / p)
      ≤ Real.exp (143800 * K) := by
    refine Real.exp_le_exp.2 ?_
    have hc0 : (0 : ℝ) ≤ 4096 * s₁.im ^ 2 := by positivity
    have hA := mul_le_mul_of_nonneg_left hsum hc0
    have hB := mul_le_mul_of_nonneg_left (le_trans hA hnum) hK0
    nlinarith [hB]
  exact hmix.trans (mul_le_mul_of_nonneg_right (hprod.trans hstep) hR0)

/-! ### The envelope of the Euler product on a vertical line

The central-window bound applies the balanced Hölder to `A = ‖F_y(c)‖^{2q}` and
`B = (∫_{|t|≤w}‖F_y(c+it)‖²dt)/‖F_y(c)‖²`, and every side condition it carries — the three
integrabilities and the two positivities — comes from the *same* two-sided bound: on the line
`Re s = c ≥ 1/2` the squarefree product sits between `∏(1 - p^{-c})` and `∏(1 + p^{-c})`, with
both bounds independent of `Im s` and the lower one positive because `p^{-c} ≤ 3/4`. -/

/-- The Rademacher squarefree block product is measurable — the closed form is pointwise, so
this needs no hypothesis on `s`. -/
lemma measurable_norm_randomEulerProductIco_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) (s : ℂ) :
    Measurable fun ω =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖ := by
  simp only [randomEulerProductIco_sqfree_eq]
  exact (Finset.measurable_prod _ fun p hp =>
    ((hX.measurable p (prime_of_mem_primesIco hp)).mul_const _).const_add 1).norm

/-- **The two-sided envelope of a block product**, uniform along the line `Re s = c`, for every
`c > 0`.  Both bounds depend on `s` only through `c`; the lower one is positive because every
`p^{-c} < 1` (`RMF.prod_one_sub_prime_rpow_primesIco_pos_of_pos`). -/
lemma ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ ω ∂μ, ∀ s : ℂ, s.re = c →
      (∏ p ∈ primesIco y₀ y₁, (1 - (p : ℝ) ^ (-c)))
          ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖
        ∧ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖
          ≤ ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-c)) := by
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw y₀ y₁] with ω hω
  intro s hs
  have hw : ∀ p ∈ primesIco y₀ y₁, ‖((p : ℕ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-c) := by
    intro p hp
    rw [Complex.norm_natCast_cpow_of_pos (prime_of_mem_primesIco hp).pos, Complex.neg_re, hs]
  have hup := norm_randomEulerProductIco_sqfree_le (X := X) y₀ y₁ s hω
  have hlow := le_norm_randomEulerProductIco_sqfree (X := X) y₀ y₁
    (show (0 : ℝ) < s.re by rw [hs]; exact hc) hω
  rw [Finset.prod_congr rfl fun p hp => by rw [hw p hp]] at hup
  rw [Finset.prod_congr rfl fun p hp => by rw [hw p hp]] at hlow
  exact ⟨hlow, hup⟩

/-- **The two-sided envelope**, uniform along the line `Re s = c`.  Both bounds depend on `s` only
through `c`.  The block `[0, y)` of `RMF.ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos`. -/
lemma ae_forall_norm_randomEulerProduct_mem_Icc {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {c : ℝ} (hc : 1 / 2 ≤ c) :
    ∀ᵐ ω ∂μ, ∀ s : ℂ, s.re = c →
      (∏ p ∈ Nat.primesBelow y, (1 - (p : ℝ) ^ (-c)))
          ≤ ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω‖
        ∧ ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω‖
          ≤ ∏ p ∈ Nat.primesBelow y, (1 + (p : ℝ) ^ (-c)) := by
  simpa only [randomEulerProductIco_zero, primesIco_zero] using
    ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX 0 y (by linarith : (0 : ℝ) < c)

/-- The lower envelope of a block product is positive as soon as `c > 0`: every factor is
`1 - p^{-c} > 0`.  (The bound `p^{-c} ≤ 3/4` is needed only by the two-point ratio.) -/
lemma prod_one_sub_prime_rpow_primesIco_pos_of_pos {y₀ y₁ : ℕ} {c : ℝ} (hc : 0 < c) :
    (0 : ℝ) < ∏ p ∈ primesIco y₀ y₁, (1 - (p : ℝ) ^ (-c)) :=
  Finset.prod_pos fun p hp => by
    have := Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast (prime_of_mem_primesIco hp).one_lt : (1 : ℝ) < (p : ℝ))
      (by linarith : -c < 0)
    linarith

/-- The lower envelope is positive: every factor is `1 - p^{-c} ≥ 1/4`.  The block `[0, y)` of
`RMF.prod_one_sub_prime_rpow_primesIco_pos_of_pos`. -/
lemma prod_one_sub_prime_rpow_pos {y : ℕ} {c : ℝ} (hc : 1 / 2 ≤ c) :
    (0 : ℝ) < ∏ p ∈ Nat.primesBelow y, (1 - (p : ℝ) ^ (-c)) := by
  simpa only [primesIco_zero] using
    prod_one_sub_prime_rpow_primesIco_pos_of_pos (y₀ := 0) (y₁ := y) (by linarith : (0 : ℝ) < c)

/-- **Every real power of a block product is integrable**, at a *negative* exponent too, on any
line `Re s = c > 0`: the lower envelope keeps `‖F(s)‖` away from zero, so `x ↦ x^r` is continuous
where it matters and the bound is `max{U^r, V^r}`. -/
lemma integrable_norm_randomEulerProductIco_rpow {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : s.re = c)
    (r : ℝ) :
    Integrable (fun ω =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖ ^ r) μ := by
  haveI := hX.isProbabilityMeasure
  have henv := (ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y₁ hc).mono
    fun _ h => h s hs
  set V : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 - (p : ℝ) ^ (-c)) with hVdef
  set U : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-c)) with hUdef
  have hV : (0 : ℝ) < V := prod_one_sub_prime_rpow_primesIco_pos_of_pos hc
  -- measurability, through the truncation `max · V`
  have hcont : Continuous fun x : ℝ => (max x V) ^ r :=
    (continuous_id.max continuous_const).rpow_const fun x =>
      Or.inl (lt_of_lt_of_le hV (le_max_right x V)).ne'
  have hmeas : AEStronglyMeasurable (fun ω =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖ ^ r) μ := by
    refine (hcont.measurable.comp
      (measurable_norm_randomEulerProductIco_sqfree hX y₀ y₁ s)).aestronglyMeasurable.congr ?_
    filter_upwards [henv] with ω hω
    simp only [Function.comp_apply, max_eq_left hω.1]
  refine (memLp_top_of_bound hmeas (max (U ^ r) (V ^ r)) ?_).integrable le_top
  filter_upwards [henv] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rcases le_total 0 r with hr | hr
  · exact le_trans (Real.rpow_le_rpow (norm_nonneg _) hω.2 hr) (le_max_left _ _)
  · exact le_trans (Real.rpow_le_rpow_of_nonpos hV hω.1 hr) (le_max_right _ _)

/-- The plain moment of a block product is positive on any line `Re s = c > 0`:
`‖F(s)‖^r ≥ min{V^r, U^r} > 0` almost surely. -/
lemma integral_norm_randomEulerProductIco_rpow_pos {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : s.re = c)
    (r : ℝ) :
    (0 : ℝ) < ∫ ω,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖ ^ r ∂μ := by
  haveI := hX.isProbabilityMeasure
  have henv := (ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y₁ hc).mono
    fun _ h => h s hs
  set V : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 - (p : ℝ) ^ (-c)) with hVdef
  set U : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-c)) with hUdef
  have hV : (0 : ℝ) < V := prod_one_sub_prime_rpow_primesIco_pos_of_pos hc
  have hlow : ∀ᵐ ω ∂μ, min (V ^ r) (U ^ r)
      ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖ ^ r := by
    filter_upwards [henv] with ω hω
    rcases le_total 0 r with hr | hr
    · exact le_trans (min_le_left _ _) (Real.rpow_le_rpow hV.le hω.1 hr)
    · exact le_trans (min_le_right _ _)
        (Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hV hω.1) hω.2 hr)
  have hU : (0 : ℝ) < U := Finset.prod_pos fun p _ => by positivity
  have hmin : (0 : ℝ) < min (V ^ r) (U ^ r) :=
    lt_min (Real.rpow_pos_of_pos hV r) (Real.rpow_pos_of_pos hU r)
  calc (0 : ℝ) < min (V ^ r) (U ^ r) := hmin
    _ = ∫ _ω, min (V ^ r) (U ^ r) ∂μ := by simp
    _ ≤ _ := integral_mono_ae (integrable_const _)
        (integrable_norm_randomEulerProductIco_rpow hX y₀ y₁ hc hs r) hlow

/-! ### The window integral, and Fubini -/

/-- **The Tonelli slice for a block product**, on any set of finite measure and any line
`Re s = ½ + σ > 0`.  The closed form `RMF.randomEulerProductIco_sqfree_eq` makes the integrand
jointly measurable, and the upper envelope, which does not move along the line, bounds it. -/
lemma integrable_uncurry_normSq_shiftLine_primesIco {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {σ : ℝ} (hσ : 0 < 1 / 2 + σ) {I : Set ℝ}
    (hI : volume I ≠ ⊤) :
    Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ t) ω‖ ^ 2)
      (μ.prod (volume.restrict I)) := by
  haveI := hX.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict I) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hI⟩
  have henv := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y₁ hσ
  have hmeas0 : Measurable fun w : Ω × ℝ =>
      ‖∏ p ∈ primesIco y₀ y₁, (1 + X p w.1 * (p : ℂ) ^ (-(shiftLine σ w.2)))‖ ^ 2 := by
    refine (Finset.measurable_prod _ fun p hp => ?_).norm.pow_const 2
    have h1 : Measurable fun w : Ω × ℝ => X p w.1 :=
      (hX.measurable p (prime_of_mem_primesIco hp)).comp measurable_fst
    have h2 : Measurable fun w : Ω × ℝ => (p : ℂ) ^ (-(shiftLine σ w.2)) :=
      ((continuous_cpow_neg_shiftLine (prime_of_mem_primesIco hp).pos σ).measurable).comp
        measurable_snd
    exact (h1.mul h2).const_add 1
  have heq : (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        (shiftLine σ t) ω‖ ^ 2)
      = fun w : Ω × ℝ =>
        ‖∏ p ∈ primesIco y₀ y₁, (1 + X p w.1 * (p : ℂ) ^ (-(shiftLine σ w.2)))‖ ^ 2 := by
    funext w
    exact congrArg (fun v : ℂ => ‖v‖ ^ 2) (randomEulerProductIco_sqfree_eq y₀ y₁ _ w.1)
  have hmeas : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        (shiftLine σ t) ω‖ ^ 2) := by
    rw [heq]
    exact hmeas0
  refine (memLp_top_of_bound hmeas.aestronglyMeasurable
    ((∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2) ?_).integrable le_top
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae henv] with w hw
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hw (shiftLine σ w.2) (re_shiftLine σ w.2)).2 2

/-! ### A weight in `t`

`Z_c` carries `|σ+it|^{-2}`, and the balanced Hölder does not care: the tilt is in `ω` and the
weight rides through Fubini untouched.  **That is why no dyadic split is needed**: the weight
supplies the factor `1/σ` directly, `∫_ℝ dt/(σ²+t²) = π/σ`.

Everything below therefore carries a nonnegative bounded measurable `ρ : ℝ → ℝ`, and the
unweighted statements are its `ρ = 1` case. -/

/-- `∫_{|t|≤w} dt/(σ²+t²) ≤ π/σ`, by the antiderivative `σ⁻¹·arctan(t/σ)` and
`|arctan| < π/2`. -/
lemma setIntegral_inv_sq_add_sq_le {σ w : ℝ} (hσ : 0 < σ) (hw : 0 ≤ w) :
    (∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹) ≤ Real.pi / σ := by
  have hpos : ∀ t : ℝ, (0 : ℝ) < σ ^ 2 + t ^ 2 := fun t => by positivity
  have hcont : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ := by
    refine Continuous.inv₀ (by fun_prop) fun t => (hpos t).ne'
  -- the antiderivative
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => σ⁻¹ * Real.arctan (u / σ)) ((σ ^ 2 + t ^ 2)⁻¹) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => u / σ) σ⁻¹ t := by
      simpa using (hasDerivAt_id t).div_const σ
    have h2 := (Real.hasDerivAt_arctan (t / σ)).comp t h1
    have h3 := h2.const_mul σ⁻¹
    have hne : σ ≠ 0 := hσ.ne'
    have hne2 : σ ^ 2 + t ^ 2 ≠ 0 := (hpos t).ne'
    have hd : (1 : ℝ) + (t / σ) ^ 2 = (σ ^ 2 + t ^ 2) / σ ^ 2 := by field_simp
    have heq : σ⁻¹ * (1 / (1 + (t / σ) ^ 2) * σ⁻¹) = (σ ^ 2 + t ^ 2)⁻¹ := by
      rw [hd, one_div, inv_div]
      field_simp
    rw [heq] at h3
    exact h3
  have hint : (∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹)
      = σ⁻¹ * Real.arctan (w / σ) - σ⁻¹ * Real.arctan (-w / σ) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -w ≤ w)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable _ _)
  rw [hint]
  have h1 : Real.arctan (w / σ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have h2 : -(Real.pi / 2) < Real.arctan (-w / σ) := Real.neg_pi_div_two_lt_arctan _
  have hσ' : (0 : ℝ) < σ⁻¹ := inv_pos.2 hσ
  have : σ⁻¹ * Real.arctan (w / σ) - σ⁻¹ * Real.arctan (-w / σ) < σ⁻¹ * Real.pi := by
    nlinarith [hσ']
  have hpi : Real.pi / σ = σ⁻¹ * Real.pi := by rw [div_eq_inv_mul]
  linarith [hpi.le, hpi.ge]

/-- The weighted Tonelli slice for a block product: a bounded measurable `ρ` in `t` keeps the
product integrable. -/
lemma integrable_uncurry_weight_normSq_shiftLine_primesIco {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {σ w Bd : ℝ} {ρ : ℝ → ℝ}
    (hσ : 0 < 1 / 2 + σ) (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρb : ∀ t, ρ t ≤ Bd) :
    Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
        ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ t) ω‖ ^ 2)
      (μ.prod (volume.restrict (Set.Icc (-w) w))) := by
  haveI := hX.isProbabilityMeasure
  refine Integrable.bdd_mul (c := Bd)
    (integrable_uncurry_normSq_shiftLine_primesIco hX y₀ y₁ hσ (I := Set.Icc (-w) w)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    (hρm.comp measurable_snd).aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 _)]
  exact hρb _

/-- The weighted slice times a power of the block product at the base point, still integrable:
the power is bounded by the envelope, which holds on any line `Re s = ½ + σ > 0`. -/
lemma integrable_uncurry_rpow_mul_weight_normSq_primesIco {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {σ r w Bd : ℝ} {ρ : ℝ → ℝ}
    (hσ : 0 < 1 / 2 + σ) (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρb : ∀ t, ρ t ≤ Bd) :
    Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ 0) ω‖ ^ r
          * (ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ t) ω‖ ^ 2))
      (μ.prod (volume.restrict (Set.Icc (-w) w))) := by
  haveI := hX.isProbabilityMeasure
  have h0 := integrable_uncurry_weight_normSq_shiftLine_primesIco hX y₀ y₁ (w := w) hσ hρm hρ0 hρb
  have henv := (ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y₁ hσ).mono
    fun _ h => h (shiftLine σ 0) (re_shiftLine σ 0)
  set V : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) with hVdef
  set U : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) with hUdef
  have hV : (0 : ℝ) < V := prod_one_sub_prime_rpow_primesIco_pos_of_pos hσ
  have hbound : ∀ᵐ ω ∂μ,
      ‖‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        (shiftLine σ 0) ω‖ ^ r‖ ≤ max (U ^ r) (V ^ r) := by
    filter_upwards [henv] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    rcases le_total 0 r with hr | hr
    · exact le_trans (Real.rpow_le_rpow (norm_nonneg _) hω.2 hr) (le_max_left _ _)
    · exact le_trans (Real.rpow_le_rpow_of_nonpos hV hω.1 hr) (le_max_right _ _)
  exact Integrable.bdd_mul h0
    ((integrable_norm_randomEulerProductIco_rpow hX y₀ y₁ hσ (re_shiftLine σ 0) r).1.comp_fst)
    (Measure.quasiMeasurePreserving_fst.ae hbound)

/-- The weighted window integral of a block product, swapped by Fubini. -/
lemma integral_rpow_mul_setIntegral_weight_normSq_swap_primesIco {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {σ r w Bd : ℝ} {ρ : ℝ → ℝ}
    (hσ : 0 < 1 / 2 + σ) (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρb : ∀ t, ρ t ≤ Bd) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ r
        * (∫ t in Set.Icc (-w) w, ρ t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2) ∂μ)
      = ∫ t in Set.Icc (-w) w, ∫ ω,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ r
            * (ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hint := integrable_uncurry_rpow_mul_weight_normSq_primesIco hX y₀ y₁ (r := r) (w := w)
    hσ hρm hρ0 hρb
  calc (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ r
        * (∫ t in Set.Icc (-w) w, ρ t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2) ∂μ)
      = ∫ ω, (∫ t in Set.Icc (-w) w,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ r
            * (ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2)) ∂μ := by
        simp_rw [integral_const_mul]
    _ = _ := integral_integral_swap hint

/-! ### The central-window bound -/

/-- **The balanced Hölder, in the shape the central window uses it.**  With `N > 0` the "plain"
observable and `W ≥ 0` the window integral, `E[W^q] ≤ κ^q·E[N^q]` whenever
`E[N^{q-1}W] ≤ κ·E[N^q]`, for `0 ≤ q ≤ 1` and `κ ≥ 0`:
`RMF.integral_mul_rpow_le` at `A = N^q`, `B = W/N`, where `A·B^q = W^q`, `A·B = N^{q-1}W` and
`(EA)^{1-q}(κ·EA)^q = κ^q·EA`.  Every hypothesis is what the envelope supplies. -/
theorem integral_rpow_le_of_mixed_le {μ : Measure Ω} {N W : Ω → ℝ} {q κ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hN : ∀ᵐ ω ∂μ, 0 < N ω) (hW : ∀ᵐ ω ∂μ, 0 ≤ W ω)
    (hNi : Integrable (fun ω => N ω ^ q) μ)
    (hABi : Integrable (fun ω => N ω ^ (q - 1) * W ω) μ)
    (hi : Integrable (fun ω => W ω ^ q) μ)
    (hα : 0 < ∫ ω, N ω ^ q ∂μ) (hβ : 0 < ∫ ω, N ω ^ (q - 1) * W ω ∂μ) (hκ : 0 ≤ κ)
    (hbd : (∫ ω, N ω ^ (q - 1) * W ω ∂μ) ≤ κ * ∫ ω, N ω ^ q ∂μ) :
    (∫ ω, W ω ^ q ∂μ) ≤ κ ^ q * ∫ ω, N ω ^ q ∂μ := by
  -- the two pointwise identities
  have hAB : ∀ᵐ ω ∂μ, N ω ^ q * (W ω / N ω) = N ω ^ (q - 1) * W ω := by
    filter_upwards [hN] with ω hNω
    rw [Real.rpow_sub hNω, Real.rpow_one]
    field_simp
  have hABq : ∀ᵐ ω ∂μ, N ω ^ q * (W ω / N ω) ^ q = W ω ^ q := by
    filter_upwards [hN, hW] with ω hNω hWω
    have hne : N ω ^ q ≠ 0 := (Real.rpow_pos_of_pos hNω q).ne'
    rw [Real.div_rpow hWω hNω.le]
    field_simp
  have e1 : (∫ ω, N ω ^ q * (W ω / N ω) ^ q ∂μ) = ∫ ω, W ω ^ q ∂μ := integral_congr_ae hABq
  have e2 : (∫ ω, N ω ^ q * (W ω / N ω) ∂μ) = ∫ ω, N ω ^ (q - 1) * W ω ∂μ :=
    integral_congr_ae hAB
  -- the balanced Hölder
  have hmain := integral_mul_rpow_le (μ := μ) (A := fun ω => N ω ^ q)
    (B := fun ω => W ω / N ω) hq0 hq1
    (hN.mono fun ω h => (Real.rpow_pos_of_pos h q).le)
    ((hN.and hW).mono fun ω h => div_nonneg h.2 h.1.le)
    hNi (hABi.congr (hAB.mono fun ω h => h.symm)) (hi.congr (hABq.mono fun ω h => h.symm))
    hα (by rw [e2]; exact hβ)
  rw [e1, e2] at hmain
  refine hmain.trans ?_
  have hstep : (∫ ω, N ω ^ (q - 1) * W ω ∂μ) ^ q ≤ (κ * ∫ ω, N ω ^ q ∂μ) ^ q :=
    Real.rpow_le_rpow hβ.le hbd hq0
  have h1 : (κ * ∫ ω, N ω ^ q ∂μ) ^ q = κ ^ q * (∫ ω, N ω ^ q ∂μ) ^ q :=
    Real.mul_rpow hκ hα.le
  have h2 : (∫ ω, N ω ^ q ∂μ) ^ (1 - q) * (∫ ω, N ω ^ q ∂μ) ^ q = ∫ ω, N ω ^ q ∂μ := by
    rw [← Real.rpow_add hα]
    norm_num
  calc (∫ ω, N ω ^ q ∂μ) ^ (1 - q) * (∫ ω, N ω ^ (q - 1) * W ω ∂μ) ^ q
      ≤ (∫ ω, N ω ^ q ∂μ) ^ (1 - q) * (κ * ∫ ω, N ω ^ q ∂μ) ^ q :=
        mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hα.le _)
    _ = κ ^ q * ((∫ ω, N ω ^ q ∂μ) ^ (1 - q) * (∫ ω, N ω ^ q ∂μ) ^ q) := by rw [h1]; ring
    _ = κ ^ q * ∫ ω, N ω ^ q ∂μ := by rw [h2]

/-- **The central window for a block of primes, with a weight in `t`, to the left of `½`.**  For
`0 ≤ q ≤ 1`, `y₁ ≥ 2`, `σ ≥ -1/12` with `p^{-(½+σ)}·p^{-(½+σ)} ≤ K/p` on the block (`K ≥ 0`),
`w·log y₁ ≤ 2`, and a nonnegative bounded measurable `ρ` with `0 < ∫_{|t|≤w}ρ ≤ R`,
`E[(∫_{|t|≤w}ρ(t)‖F(½+σ+it)‖²dt)^q] ≤ (R·e^{143800·K})^q·E‖F(½+σ)‖^{2q}`, `F` over `y₀ ≤ p < y₁`.
The two hypotheses on `σ` replace `σ ≥ 0`: `½ + σ ≥ 5/12` keeps every `p^{-(½+σ)} ≤ 3/4`, as the
two-point ratio needs, and `K` is what `p^{-2(½+σ)} ≤ 1/p` becomes. -/
theorem integral_rpow_setIntegral_weight_normSq_shiftLine_primesIco_le {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {y₀ y₁ : ℕ} (hy : 2 ≤ y₁)
    {σ w q R Bd K : ℝ} {ρ : ℝ → ℝ} (hσ : -(1 / 12) ≤ σ)
    (hK : ∀ p ∈ primesIco y₀ y₁,
      (p : ℝ) ^ (-(1 / 2 + σ)) * (p : ℝ) ^ (-(1 / 2 + σ)) ≤ K * ((p : ℝ))⁻¹)
    (hK0 : 0 ≤ K) (hwy : w * Real.log y₁ ≤ 2) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρb : ∀ t, ρ t ≤ Bd)
    (hρpos : 0 < ∫ t in Set.Icc (-w) w, ρ t)
    (hρR : (∫ t in Set.Icc (-w) w, ρ t) ≤ R) :
    (∫ ω, (∫ t in Set.Icc (-w) w, ρ t *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ (R * Real.exp (143800 * K)) ^ q
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (-w) w)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hc : (5 : ℝ) / 12 ≤ 1 / 2 + σ := by linarith
  have hc0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hlogy : (0 : ℝ) ≤ Real.log y₁ :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y₁))
  have hbase : shiftLine σ 0 = (((1 / 2 + σ : ℝ)) : ℂ) := by simp [shiftLine]
  have henvall := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y₁ hc0
  set V : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) with hVdef
  set U : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) with hUdef
  have hV : (0 : ℝ) < V := prod_one_sub_prime_rpow_primesIco_pos_of_pos hc0
  have hUpos : (0 : ℝ) < U := Finset.prod_pos fun p _ => by positivity
  -- the weight is integrable on the window
  have hρint : Integrable ρ (volume.restrict (Set.Icc (-w) w)) := by
    refine (memLp_top_of_bound hρm.aestronglyMeasurable Bd ?_).integrable le_top
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
    exact hρb t
  -- the window integral, and its two-sided bound
  have hslice := integrable_uncurry_weight_normSq_shiftLine_primesIco hX y₀ y₁ (w := w) hc0 hρm
    hρ0 hρb
  have hWint : Integrable (fun ω => ∫ t in Set.Icc (-w) w, ρ t *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        (shiftLine σ t) ω‖ ^ 2) μ := hslice.integral_prod_left
  have hWnn : ∀ ω : Ω, (0 : ℝ) ≤ ∫ t in Set.Icc (-w) w, ρ t *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        (shiftLine σ t) ω‖ ^ 2 :=
    fun ω => integral_nonneg fun t => mul_nonneg (hρ0 t) (by positivity)
  have hcm : ∀ C : ℝ, (∫ t in Set.Icc (-w) w, ρ t * C)
      = (∫ t in Set.Icc (-w) w, ρ t) * C := fun C => integral_mul_const C ρ
  have hWbd : ∀ᵐ ω ∂μ, (V ^ 2 * (∫ t in Set.Icc (-w) w, ρ t)
        ≤ ∫ t in Set.Icc (-w) w, ρ t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2)
      ∧ (∫ t in Set.Icc (-w) w, ρ t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2) ≤ U ^ 2 * (∫ t in Set.Icc (-w) w, ρ t) := by
    filter_upwards [henvall, hslice.prod_right_ae] with ω hω hint
    constructor
    · rw [show V ^ 2 * (∫ t in Set.Icc (-w) w, ρ t)
          = (∫ t in Set.Icc (-w) w, ρ t) * V ^ 2 by ring, ← hcm]
      refine integral_mono (hρint.mul_const _) hint fun t => ?_
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hV.le (hω (shiftLine σ t) (re_shiftLine σ t)).1 2) (hρ0 t)
    · rw [show U ^ 2 * (∫ t in Set.Icc (-w) w, ρ t)
          = (∫ t in Set.Icc (-w) w, ρ t) * U ^ 2 by ring, ← hcm]
      refine integral_mono hint (hρint.mul_const _) fun t => ?_
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hω (shiftLine σ t) (re_shiftLine σ t)).2 2) (hρ0 t)
  -- the plain moment, read as `N^q`
  have hnorm : ∀ (r : ℝ) (ω : Ω),
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ (2 * r)
        = (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ 2) ^ r := fun r ω => norm_rpow_two_mul _ r
  rw [integral_congr_ae (Filter.Eventually.of_forall (hnorm q))]
  refine integral_rpow_le_of_mixed_le hq0 hq1 ?_ (.of_forall hWnn) ?_ ?_ ?_ ?_ ?_
    (mul_nonneg (by linarith) (Real.exp_pos _).le) ?_
  -- `0 < N`
  · filter_upwards [henvall] with ω hω
    exact pow_pos (lt_of_lt_of_le hV (hω (shiftLine σ 0) (re_shiftLine σ 0)).1) 2
  -- `N^q` integrable
  · exact (integrable_norm_randomEulerProductIco_rpow hX y₀ y₁ hc0 (re_shiftLine σ 0) (2 * q)).congr
      (Filter.Eventually.of_forall (hnorm q))
  -- `N^{q-1}·W` integrable
  · refine Integrable.bdd_mul (c := (V ^ 2) ^ (q - 1)) hWint
      (((integrable_norm_randomEulerProductIco_rpow hX y₀ y₁ hc0 (re_shiftLine σ 0)
        (2 * (q - 1))).congr (Filter.Eventually.of_forall (hnorm (q - 1)))).1) ?_
    filter_upwards [henvall] with ω hω
    have h1 := (hω (shiftLine σ 0) (re_shiftLine σ 0)).1
    have h2 : (0 : ℝ) < V ^ 2 := by positivity
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (le_of_lt (pow_pos (lt_of_lt_of_le hV h1) 2)) _)]
    exact Real.rpow_le_rpow_of_nonpos h2 (pow_le_pow_left₀ hV.le h1 2) (by linarith)
  -- `W^q` integrable
  · refine (memLp_top_of_bound
      ((Real.continuous_rpow_const hq0).comp_aestronglyMeasurable hWint.1)
      ((U ^ 2 * (∫ t in Set.Icc (-w) w, ρ t)) ^ q) ?_).integrable le_top
    filter_upwards [hWbd] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hWnn ω) _)]
    exact Real.rpow_le_rpow (hWnn ω) hω.2 hq0
  -- `0 < ∫ N^q`
  · have h := integral_norm_randomEulerProductIco_rpow_pos hX y₀ y₁ hc0 (re_shiftLine σ 0) (2 * q)
    rwa [integral_congr_ae (Filter.Eventually.of_forall (hnorm q))] at h
  -- `0 < ∫ N^{q-1}·W`
  · have hlow : ∀ᵐ ω ∂μ, (U ^ 2) ^ (q - 1) * (V ^ 2 * (∫ t in Set.Icc (-w) w, ρ t))
        ≤ (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
          * ∫ t in Set.Icc (-w) w, ρ t *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
                (shiftLine σ t) ω‖ ^ 2 := by
      filter_upwards [henvall, hWbd] with ω hω hWω
      have h1 := (hω (shiftLine σ 0) (re_shiftLine σ 0)).1
      have h2 := (hω (shiftLine σ 0) (re_shiftLine σ 0)).2
      have hpos : (0 : ℝ) < ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          y₀ y₁ (shiftLine σ 0) ω‖ ^ 2 := pow_pos (lt_of_lt_of_le hV h1) 2
      refine mul_le_mul (Real.rpow_le_rpow_of_nonpos hpos
        (pow_le_pow_left₀ (norm_nonneg _) h2 2) (by linarith)) hWω.1
        (by positivity) (Real.rpow_nonneg (le_of_lt hpos) _)
    have hcpos : (0 : ℝ) < (U ^ 2) ^ (q - 1) * (V ^ 2 * (∫ t in Set.Icc (-w) w, ρ t)) :=
      mul_pos (Real.rpow_pos_of_pos (pow_pos hUpos 2) (q - 1)) (mul_pos (pow_pos hV 2) hρpos)
    refine lt_of_lt_of_le hcpos ?_
    calc (U ^ 2) ^ (q - 1) * (V ^ 2 * (∫ t in Set.Icc (-w) w, ρ t))
        = ∫ _ω, (U ^ 2) ^ (q - 1) * (V ^ 2 * (∫ t in Set.Icc (-w) w, ρ t)) ∂μ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _)
          (by
            refine Integrable.bdd_mul (c := (V ^ 2) ^ (q - 1)) hWint
              (((integrable_norm_randomEulerProductIco_rpow hX y₀ y₁ hc0 (re_shiftLine σ 0)
                (2 * (q - 1))).congr (Filter.Eventually.of_forall (hnorm (q - 1)))).1) ?_
            filter_upwards [henvall] with ω hω
            have h1 := (hω (shiftLine σ 0) (re_shiftLine σ 0)).1
            have h2 : (0 : ℝ) < V ^ 2 := by positivity
            rw [Real.norm_eq_abs,
              abs_of_nonneg
                (Real.rpow_nonneg (le_of_lt (pow_pos (lt_of_lt_of_le hV h1) 2)) _)]
            exact Real.rpow_le_rpow_of_nonpos h2 (pow_le_pow_left₀ hV.le h1 2) (by linarith))
          hlow
  -- the mixed bound, via Fubini
  · have hswap := integral_rpow_mul_setIntegral_weight_normSq_swap_primesIco hX y₀ y₁
      (r := 2 * (q - 1)) (w := w) hc0 hρm hρ0 hρb
    have he : (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
        * (∫ t in Set.Icc (-w) w, ρ t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2) ∂μ)
        = ∫ t in Set.Icc (-w) w, ∫ ω,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
                (shiftLine σ 0) ω‖ ^ (2 * (q - 1))
              * (ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
                (shiftLine σ t) ω‖ ^ 2) ∂μ := by
      rw [← hswap]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      dsimp only
      rw [hnorm (q - 1) ω]
    rw [he]
    have hMnn : (0 : ℝ) ≤ ∫ ω,
        (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ 2) ^ q ∂μ :=
      integral_nonneg fun ω => Real.rpow_nonneg (by positivity) _
    have hpt : ∀ t ∈ Set.Icc (-w) w,
        (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ (2 * (q - 1))
            * (ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2) ∂μ)
          ≤ ρ t * (Real.exp (143800 * K) * ∫ ω,
              (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
                (shiftLine σ 0) ω‖ ^ 2) ^ q ∂μ) := by
      intro t ht
      have habs : |t| ≤ w := abs_le.2 ⟨ht.1, ht.2⟩
      have hthr : |(shiftLine σ t).im| * Real.log y₁ ≤ 2 := by
        rw [im_shiftLine]
        have := mul_le_mul_of_nonneg_right habs hlogy
        linarith
      have hmix := integral_mixed_norm_randomEulerProductIco_le_exp hX hy hc
        (re_shiftLine σ t) hthr hK hK0 hq0 hq1
      rw [← hbase] at hmix
      have hone : ∀ v : ℂ, ‖v‖ ^ (2 * (1 : ℝ)) = ‖v‖ ^ 2 := fun v => by
        rw [norm_rpow_two_mul v 1, Real.rpow_one]
      simp only [hone] at hmix
      rw [integral_congr_ae (Filter.Eventually.of_forall (hnorm q))] at hmix
      have hpull : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ (2 * (q - 1))
            * (ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2) ∂μ)
          = ρ t * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ (2 * (q - 1))
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2 ∂μ := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
      rw [hpull]
      exact mul_le_mul_of_nonneg_left hmix (hρ0 t)
    have hIint : Integrable (fun t => ∫ ω,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ 0) ω‖ ^ (2 * (q - 1))
          * (ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ t) ω‖ ^ 2) ∂μ) (volume.restrict (Set.Icc (-w) w)) :=
      (integrable_uncurry_rpow_mul_weight_normSq_primesIco hX y₀ y₁
        (r := 2 * (q - 1)) (w := w) hc0 hρm hρ0 hρb).integral_prod_right
    calc (∫ t in Set.Icc (-w) w, ∫ ω,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ (2 * (q - 1))
            * (ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2) ∂μ)
        ≤ ∫ t in Set.Icc (-w) w, ρ t * (Real.exp (143800 * K) * ∫ ω,
            (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ 2) ^ q ∂μ) :=
          setIntegral_mono_on hIint (by exact hρint.mul_const _) measurableSet_Icc hpt
      _ = (∫ t in Set.Icc (-w) w, ρ t) * (Real.exp (143800 * K) * ∫ ω,
            (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ 2) ^ q ∂μ) := hcm _
      _ ≤ R * Real.exp (143800 * K) * ∫ ω,
            (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ 2) ^ q ∂μ := by
          linarith [mul_le_mul_of_nonneg_right hρR
            (mul_nonneg (Real.exp_pos (143800 * K)).le hMnn)]

/-- **`Z_c`'s window for a block, with the weight's abscissa decoupled from the product's.**  For
`c > 0`, `σ ≥ -1/12` with `p^{-(½+σ)}·p^{-(½+σ)} ≤ K/p` on the block (`K ≥ 0`), `0 < w` with
`w·log y₁ ≤ 2`, `y₁ ≥ 2` and `0 ≤ q ≤ 1`, `F` the product over `y₀ ≤ p < y₁`,
`E[(∫_{|t|≤w}‖F(½+σ+it)/(c+it)‖²dt)^q] ≤ (π e^{143800·K}/c)^q·E‖F(½+σ)‖^{2q}`: the weight
`ρ(t) = (c²+t²)^{-1}` integrates to at most `π/c`.  A band's central window
(`RMF.integral_rpow_centralWindow_primesIco_le`) takes the product at `½ - c` and the weight at
`c`. -/
theorem integral_rpow_setIntegral_normSq_div_shiftLine_primesIco_le {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {y₀ y₁ : ℕ} (hy : 2 ≤ y₁)
    {σ c w q K : ℝ} (hσ : -(1 / 12) ≤ σ)
    (hK : ∀ p ∈ primesIco y₀ y₁,
      (p : ℝ) ^ (-(1 / 2 + σ)) * (p : ℝ) ^ (-(1 / 2 + σ)) ≤ K * ((p : ℝ))⁻¹)
    (hK0 : 0 ≤ K) (hc : 0 < c) (hw : 0 < w) (hwy : w * Real.log y₁ ≤ 2)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, (∫ t in Set.Icc (-w) w,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ t) ω / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ (Real.pi / c * Real.exp (143800 * K)) ^ q
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (-w) w)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hpos : ∀ t : ℝ, (0 : ℝ) < c ^ 2 + t ^ 2 := fun t => by positivity
  have hcont : Continuous fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun t => (hpos t).ne'
  -- `‖z/(c+it)‖² = (c²+t²)⁻¹‖z‖²`
  have hden : ∀ t : ℝ, ‖((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = c ^ 2 + t ^ 2 := by
    intro t
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hpt : ∀ (t : ℝ) (ω : Ω),
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ t) ω / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        = (c ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ t) ω‖ ^ 2 := by
    intro t ω
    rw [norm_div, div_pow, hden t]
    ring
  simp only [hpt]
  refine integral_rpow_setIntegral_weight_normSq_shiftLine_primesIco_le (Bd := (c ^ 2)⁻¹)
    (R := Real.pi / c) hX hy hσ hK hK0 hwy hq0 hq1 hcont.measurable
    (fun t => by positivity) (fun t => ?_) ?_ (setIntegral_inv_sq_add_sq_le hc hw.le)
  · exact (inv_le_inv₀ (hpos t) (by positivity)).2 (by nlinarith [sq_nonneg t])
  · have hb : ∀ t ∈ Set.Icc (-w) w, (c ^ 2 + w ^ 2)⁻¹ ≤ (c ^ 2 + t ^ 2)⁻¹ := by
      intro t ht
      have habs : |t| ≤ w := abs_le.2 ⟨ht.1, ht.2⟩
      have : t ^ 2 ≤ w ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
      exact (inv_le_inv₀ (by positivity) (hpos t)).2 (by linarith)
    calc (0 : ℝ) < 2 * w * (c ^ 2 + w ^ 2)⁻¹ := by positivity
      _ = ∫ _t in Set.Icc (-w) w, (c ^ 2 + w ^ 2)⁻¹ := by
          rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
          ring
      _ ≤ _ := setIntegral_mono_on (by exact integrable_const _)
          (hcont.integrableOn_Icc) measurableSet_Icc hb

/-- **`Z_c`, with its own weight.**  For `0 ≤ q ≤ 1`, `y ≥ 2`, `σ > 0` and `0 < w` with
`w·log y ≤ 2`, `E[(∫_{|t|≤w}‖F_y(½+σ+it)/(σ+it)‖²dt)^q] ≤ (π e^{143800}/σ)^q·E‖F_y(½+σ)‖^{2q}`.
Divided by `(log y)^q` it is `E Z_c^q ≪ E‖F_y(½+σ)‖^{2q}/(σ log y)^q`, with no dyadic split: the
`1/σ` is the integral of the weight.  The block `[0, y)`, `c = σ`, `K = 1` case of
`RMF.integral_rpow_setIntegral_normSq_div_shiftLine_primesIco_le`. -/
theorem integral_rpow_setIntegral_normSq_div_shiftLine_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y : ℕ} (hy : 2 ≤ y) {σ w q : ℝ}
    (hσ : 0 < σ) (hw : 0 < w) (hwy : w * Real.log y ≤ 2) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, (∫ t in Set.Icc (-w) w,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
            (shiftLine σ t) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ (Real.pi / σ * Real.exp 143800) ^ q
        * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ := by
  have h := integral_rpow_setIntegral_normSq_div_shiftLine_primesIco_le hX (y₀ := 0) hy
    (σ := σ) (c := σ) (K := 1) (by linarith)
    (fun p hp => prime_rpow_neg_mul_self_le_inv (prime_of_mem_primesIco hp) (by linarith))
    zero_le_one hσ hw hwy hq0 hq1
  simpa only [randomEulerProductIco_zero, mul_one] using h

end RMF
