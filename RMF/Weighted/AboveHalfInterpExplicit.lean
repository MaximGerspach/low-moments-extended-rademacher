/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ULowQExplicit

/-!
# Above `q = ½`, explicit: interpolation between the first and the second moment

For `½ ≤ q ≤ 1` and `x ≥ 3`, Hölder with weights `2 - 2q` and `2q - 1` between (H),
`E|S(x)| ≤ 10(log log x)^{3/4}`, and `E|S(x)|² ≤ 1 + log x` gives
`E|S(x)|^{2q} ≤ (10(log log x)^{3/4})^{2-2q}(1 + log x)^{2q-1}`
(`RMF.integral_rpow_weightedRademacherSum_le_interp`).  Against the target `C(log x)^{q(2q-1)}`
it loses `e^{(2q-1)(1-q)log log x}` up to powers of `log log x`, so it covers small `log log x`
and the two ends `q → ½`, `q → 1` of the range.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Interpolation above `q = ½`**: for `x ≥ 3` and `½ ≤ q ≤ 1`,
`E|S(x)|^{2q} ≤ (10(log log x)^{3/4})^{2-2q}(1 + log x)^{2q-1}`, by Hölder
(`RMF.integral_rpow_le_mul_rpow`, exponents `1` and `2` with weights `2 - 2q` and `2q - 1`)
from (H) (`RMF.integral_norm_weightedRademacherSum_le_ten_of_three_le`) and the second moment
(`RMF.integral_normSq_weightedRademacherSum_le_one_add_log`). -/
theorem integral_rpow_weightedRademacherSum_le_interp {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 3 ≤ x) (hq1 : 1 / 2 ≤ q) (hq2 : q ≤ 1) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ (10 * Real.log (Real.log x) ^ (3 / 4 : ℝ)) ^ (2 - 2 * q)
        * (1 + Real.log x) ^ (2 * q - 1) := by
  haveI := hX.isProbabilityMeasure
  set S := weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x with hS
  have hI : ∀ r : ℝ, 0 < r → Integrable (fun ω => ‖S ω‖ ^ r) μ := by
    intro r hr
    have h := (memLp_weightedRademacherSum hX x (ENNReal.ofReal r)).integrable_norm_rpow
      (by simpa using hr) ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hr.le] at h
  have hcore := integral_rpow_le_mul_rpow (S := S) (μ := μ) (a := 1) (b := 2) (c := 2 * q)
    (α := 2 - 2 * q) (β := 2 * q - 1) (by linarith) (by linarith) (by ring) (by ring)
    (ne_of_gt (by linarith)) (hI 1 one_pos) (hI 2 two_pos) (hI (2 * q) (by linarith))
  have h1 : (∫ ω, ‖S ω‖ ^ (1 : ℝ) ∂μ) ≤ 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
    simp only [Real.rpow_one]
    exact integral_norm_weightedRademacherSum_le_ten_of_three_le hX hx
  have h2 : (∫ ω, ‖S ω‖ ^ (2 : ℝ) ∂μ) ≤ 1 + Real.log x := by
    simp only [Real.rpow_two]
    exact integral_normSq_weightedRademacherSum_le_one_add_log hX.isRademacherRMF (by linarith)
  have h10 : (0 : ℝ) ≤ ∫ ω, ‖S ω‖ ^ (1 : ℝ) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have h20 : (0 : ℝ) ≤ ∫ ω, ‖S ω‖ ^ (2 : ℝ) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  exact hcore.trans (mul_le_mul (Real.rpow_le_rpow h10 h1 (by linarith))
    (Real.rpow_le_rpow h20 h2 (by linarith)) (Real.rpow_nonneg h20 _)
    (Real.rpow_nonneg (h10.trans h1) _))

end RMF
