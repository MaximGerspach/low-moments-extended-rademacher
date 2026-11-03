/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.FracReductionExplicit.Line
import RMF.Weighted.FracWindowsExplicit.Assembly

/-!
# The remainder for every `x ≥ 3`, explicit

For the fractional-part sum `R(x) = x^{-1/2}∑_{m≤x} X(m){√(x/m)}`, every `x ≥ 3` and
`Λ = log log x`:

* `E|R(x)| ≤ 20Λ^{-1/4}` (`RMF.integral_norm_fracPartSum_le_twenty_of_three_le`): for `Λ ≤ 20⁴`
  from `E|R| ≤ 1`; beyond, the reduction to the line at `c = 1/100`
  (`RMF.integral_norm_fracPartSum_le_lineFrac`) and the bound for the line integral
  (`RMF.integral_rpow_fracLine_le_explicit`) give
  `E|R| ≤ (0.0895e^{1/100})^{1/2}·55Λ^{-1/4} + 3/log x ≤ 16.56Λ^{-1/4} + 3e^{-Λ}`;
* `E|R(x)|^{2q} ≤ min(1, 20Λ^{-1/4})^{2q}` for `0 ≤ q ≤ ½`
  (`RMF.integral_rpow_norm_fracPartSum_le_min_of_three_le`), by Jensen.
-/

open MeasureTheory

namespace RMF

/-! ### Numerals -/

/-- `1 ≤ 20Λ^{-1/4}` for `0 < Λ ≤ 20⁴`. -/
lemma one_le_twenty_mul_rpow_neg_quarter {Λ : ℝ} (hΛ0 : 0 < Λ) (hΛ : Λ ≤ 160000) :
    1 ≤ 20 * Λ ^ (-(1 / 4 : ℝ)) := by
  have h := Real.rpow_le_rpow_of_nonpos hΛ0 hΛ (by norm_num : -(1 / 4 : ℝ) ≤ 0)
  have e : (160000 : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / 20 := by
    rw [show (160000 : ℝ) = 20 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), show ((4 : ℕ) : ℝ) * -(1 / 4 : ℝ) = -1 by norm_num,
      Real.rpow_neg_one]
    norm_num
  linarith

/-- `(0.0895e^{1/100})^{1/2} ≤ 0.301`. -/
lemma fracLineConst_le : (0.0895 * Real.exp (1 / 100)) ^ (1 / 2 : ℝ) ≤ 0.301 := by
  refine rpow_half_le_of_le (by norm_num) ?_
  have h : Real.exp (1 / 100) ≤ 1.0101 := by interval_decide (trust := kernel)
  norm_num
  linarith

section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The first moment -/

/-- **The remainder for every `x ≥ 3`, explicit**: `E|R(x)| ≤ 20Λ^{-1/4}`, `Λ = log log x`.
For `Λ ≤ 20⁴`, `E|R| ≤ 1` (`RMF.integral_rpow_norm_fracPartSum_le_one`); beyond,
`E|R| ≤ 0.301·55Λ^{-1/4} + 3/log x` (`RMF.integral_norm_fracPartSum_le_lineFrac` at `c = 1/100`
and `RMF.integral_rpow_fracLine_le_explicit`), and `3/log x ≤ 3Λ⁻¹ ≤ 3Λ^{-1/4}/8000`. -/
theorem integral_norm_fracPartSum_le_twenty_of_three_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 3 ≤ x) :
    (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
      ≤ 20 * Real.log (Real.log x) ^ (-(1 / 4 : ℝ)) := by
  have hx1 : 1 ≤ x := by linarith
  have hΛ0 : 0 < Real.log (Real.log x) := by linarith [loglog_ge_of_three_le hx]
  rcases le_or_gt (Real.log (Real.log x)) 160000 with hs | hb
  · -- `Λ ≤ 20⁴`: `E|R| ≤ 1 ≤ 20Λ^{-1/4}`
    have hR := integral_rpow_norm_fracPartSum_le_one hX hx1 (q := 1 / 2) (by norm_num)
      (by norm_num)
    simp only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at hR
    linarith [one_le_twenty_mul_rpow_neg_quarter hΛ0 hs]
  -- `Λ > 20⁴`: `x ≥ exp(e^{20})`, as in `RMF.integral_rpow_fracLine_le_explicit`
  have hx0 : 0 < x := by linarith
  have hL1 : 1 < Real.log x := by
    rw [Real.lt_log_iff_exp_lt hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hexpΛ : Real.exp (Real.log (Real.log x)) = Real.log x := Real.exp_log (by linarith)
  have hx20 : Real.exp (Real.exp 20) ≤ x := by
    have h1 : Real.exp 20 ≤ Real.log x := by
      rw [← hexpΛ]
      exact Real.exp_le_exp.2 (by linarith)
    calc Real.exp (Real.exp 20) ≤ Real.exp (Real.log x) := Real.exp_le_exp.2 h1
      _ = x := Real.exp_log hx0
  -- the reduction to the line at `c = 1/100`, and the bound for the line integral
  have h4 := integral_norm_fracPartSum_le_lineFrac hX hx20 (c := 1 / 100) (by norm_num)
  have h5 := integral_rpow_fracLine_le_explicit hX hx hb.le (c := 1 / 100) (by norm_num)
    (by norm_num)
  obtain ⟨hM0, hM4, -, hM20⟩ := rpow_neg_quarter_facts hb.le
  have hA0 : 0 ≤ (0.0895 * Real.exp (1 / 100)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hAZ := mul_le_mul_of_nonneg_left h5 hA0
  have hA55 := mul_le_mul_of_nonneg_right fracLineConst_le
    (by positivity : (0 : ℝ) ≤ 55 * Real.log (Real.log x) ^ (-(1 / 4 : ℝ)))
  -- `3/log x ≤ 3Λ⁻¹ ≤ 3Λ^{-1/4}/8000`
  have hΛL : Real.log (Real.log x) ≤ Real.log x := by
    have := Real.add_one_le_exp (Real.log (Real.log x))
    linarith
  have h3 : 3 / Real.log x ≤ 3 * (Real.log (Real.log x))⁻¹ := by
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by norm_num) hΛ0 hΛL
  have hM3 : (Real.log (Real.log x) ^ (-(1 / 4 : ℝ))) ^ 3 ≤ (1 / 20) ^ 3 :=
    pow_le_pow_left₀ hM0.le hM20 3
  have hinv : (Real.log (Real.log x))⁻¹ ≤ Real.log (Real.log x) ^ (-(1 / 4 : ℝ)) / 8000 := by
    rw [← hM4]
    have e : (Real.log (Real.log x) ^ (-(1 / 4 : ℝ))) ^ 4
        = Real.log (Real.log x) ^ (-(1 / 4 : ℝ))
          * (Real.log (Real.log x) ^ (-(1 / 4 : ℝ))) ^ 3 := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hM3 hM0.le
    linarith
  linarith

/-! ### The moments below `q = ½` -/

/-- **Jensen**: `E|R(x)|^{2q} ≤ min(1, 20Λ^{-1/4})^{2q}` for `x ≥ 3` and `0 ≤ q ≤ ½`, from
`E|R|^{2q} ≤ 1` (`RMF.integral_rpow_norm_fracPartSum_le_one`) and
`E|R|^{2q} ≤ (E|R|)^{2q}` (`RMF.integral_rpow_le_rpow_of_integral_le`) with
`RMF.integral_norm_fracPartSum_le_twenty_of_three_le`. -/
theorem integral_rpow_norm_fracPartSum_le_min_of_three_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 3 ≤ x) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ min 1 (20 * Real.log (Real.log x) ^ (-(1 / 4 : ℝ))) ^ (2 * q) := by
  haveI := hX.isProbabilityMeasure
  have h1 := integral_rpow_norm_fracPartSum_le_one hX (by linarith : (1 : ℝ) ≤ x) hq0
    (by linarith)
  have hint : Integrable (fun ω =>
      ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖) μ :=
    (integrable_rpow_norm_fracPartSum hX x zero_le_one).congr
      (Filter.Eventually.of_forall fun ω => Real.rpow_one _)
  have h2 := integral_rpow_le_rpow_of_integral_le (by linarith : (0 : ℝ) ≤ 2 * q)
    (by linarith) (Filter.Eventually.of_forall fun ω => norm_nonneg _) hint
    (integral_norm_fracPartSum_le_twenty_of_three_le hX hx)
  rcases min_cases (1 : ℝ) (20 * Real.log (Real.log x) ^ (-(1 / 4 : ℝ))) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h, Real.one_rpow]
    exact h1
  · rw [h]
    exact h2

end

end RMF
