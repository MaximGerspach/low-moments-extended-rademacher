/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ULowQExplicit
import RMF.Weighted.UCellsHalfJensenExplicit
import RMF.Weighted.UHalfChaosRegimeExplicit

/-!
# The first moment below `q = ½`: (U) for every `0 < q ≤ ½` and `x ≥ 3`

The bound (U), `E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` for `S(x) = ∑_{n≤x} f(n)/√n` and
`Λ = log log x`, for every `0 < q ≤ ½` and every `x ≥ 3`
(`RMF.integral_rpow_weightedRademacherSum_le_u`).  Below `q = 0.49` it is
`RMF.integral_rpow_weightedRademacherSum_le_u_of_le_049`.  On `[0.49, ½]`, in `w = (1 - 2q)Λ`:
`w ≤ 3/2` by (H) (`E|S(x)| ≤ 10Λ^{3/4}`) and Lyapunov (`RMF.u_small_w`), and `w > 3/2`, which
forces `Λ > 75`, by the cells of the middle range (`Λ ≤ 110`, `RMF.u_cell_half_mid`), the Jensen
range (`Λ ≤ 6000`, `RMF.u_half_jensen_regime`) and the chaos range (`RMF.u_half_chaos_regime`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **(U) for `w = (1 - 2q)Λ ≤ 3/2`**: for `x ≥ 3` and `0 < q ≤ ½`, by
`RMF.integral_rpow_le_of_ten`, `(10Λ^{3/4})^{2q} = (10Λ)^{2q}Λ^{-q/2}`, and
`(10Λ)^{2q}(Λ⁻¹ + 1 - 2q)` is at most `Λ⁻¹ + 1 ≤ 11.7` for `10Λ ≤ 1` and at most
`10ΛV = 10 + 10w ≤ 25` otherwise. -/
theorem u_small_w {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : 3 ≤ x) (hq0 : 0 < q) (hq2 : q ≤ 1 / 2)
    (hw : (1 - 2 * q) * Real.log (Real.log x) ≤ 3 / 2) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  refine le_trans (integral_rpow_le_of_ten hX hx hq0 hq2) ?_
  have hΛ0 := loglog_ge_of_three_le hx
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛp : 0 < Λ := by linarith
  -- `(10Λ^{3/4})^{2q} = (10Λ)^{2q}·Λ^{-q/2}`
  have e : (10 * Λ ^ (3 / 4 : ℝ)) ^ (2 * q) = (10 * Λ) ^ (2 * q) * Λ ^ (-(q / 2)) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hΛp.le _),
      Real.mul_rpow (by norm_num) hΛp.le, ← Real.rpow_mul hΛp.le, mul_assoc,
      ← Real.rpow_add hΛp]
    congr 2
    ring
  rw [e]
  set V := Λ⁻¹ + (1 - 2 * q) with hVdef
  have hV0 : 0 < V := by have := inv_pos.2 hΛp; linarith
  have hΛq : 0 < Λ ^ (-(q / 2)) := Real.rpow_pos_of_pos hΛp _
  -- `(10Λ)^{2q}V ≤ 25`
  have hkey : (10 * Λ) ^ (2 * q) * V ≤ 25 := by
    have hΛi : Λ⁻¹ ≤ 1000 / 94 := by
      rw [inv_le_comm₀ hΛp (by norm_num)]
      rw [inv_div]
      exact hΛ0
    rcases le_total (10 * Λ) 1 with h1 | h1
    · have ha : (10 * Λ) ^ (2 * q) ≤ 1 := Real.rpow_le_one (by positivity) h1 (by linarith)
      have hV : V ≤ 1000 / 94 + 1 := by rw [hVdef]; linarith
      calc (10 * Λ) ^ (2 * q) * V ≤ 1 * V :=
            mul_le_mul_of_nonneg_right ha hV0.le
        _ ≤ 25 := by linarith
    · have ha : (10 * Λ) ^ (2 * q) ≤ 10 * Λ := by
        calc (10 * Λ) ^ (2 * q) ≤ (10 * Λ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
          _ = 10 * Λ := Real.rpow_one _
      have e2 : 10 * Λ * V = 10 + 10 * ((1 - 2 * q) * Λ) := by
        rw [hVdef]; field_simp
      calc (10 * Λ) ^ (2 * q) * V ≤ 10 * Λ * V := mul_le_mul_of_nonneg_right ha hV0.le
        _ ≤ 25 := by rw [e2]; linarith
  calc (10 * Λ) ^ (2 * q) * Λ ^ (-(q / 2)) = (10 * Λ) ^ (2 * q) * V * (V⁻¹ * Λ ^ (-(q / 2))) := by
        field_simp
    _ ≤ 25 * (V⁻¹ * Λ ^ (-(q / 2))) :=
        mul_le_mul_of_nonneg_right hkey (mul_nonneg (inv_pos.2 hV0).le hΛq.le)
    _ = 25 * V⁻¹ * Λ ^ (-(q / 2)) := by ring

/-- **(U) on `q ∈ [0.49, ½]`** for every `x ≥ 3`: `w = (1 - 2q)Λ ≤ 3/2` by `RMF.u_small_w`;
otherwise `q < ½` and `Λ > 75` (as `w ≤ Λ/50`), and the cells of the middle, Jensen and chaos
ranges cover `Λ ∈ [75, 110]`, `[110, 6000]` and `[6000, ∞)`. -/
theorem u_half_strip {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : 3 ≤ x) (hq49 : 49 / 100 ≤ q) (hq : q ≤ 1 / 2) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (3 / 2) with hw | hw
  · exact u_small_w hX hx (by linarith) hq hw
  have hq' : q < 1 / 2 := by
    rcases lt_or_eq_of_le hq with h | h
    · exact h
    · rw [h] at hw
      norm_num at hw
  have hΛ0 := loglog_ge_of_three_le hx
  have hwtop : (1 - 2 * q) * Real.log (Real.log x) ≤ Real.log (Real.log x) / 50 := by
    have := mul_le_mul_of_nonneg_right (by linarith : 1 - 2 * q ≤ 1 / 50)
      (by linarith : (0 : ℝ) ≤ Real.log (Real.log x))
    linarith
  have hΛ75 : 75 < Real.log (Real.log x) := by linarith
  have hx7 := exp_exp_seven_le_of hx (by linarith)
  rcases le_or_gt (Real.log (Real.log x)) 110 with h110 | h110
  · exact u_cell_half_mid hX hx7 hΛ75.le h110 hq49 hq hw.le (by linarith)
  have hx110 := exp_exp_le_of_loglog hx7 h110.le
  rcases le_or_gt (Real.log (Real.log x)) 6000 with h6 | h6
  · exact u_half_jensen_regime hX hx110 h6 hq49 hq hw.le
  · exact u_half_chaos_regime hX hx110 h6.le hq49 hq' hw.le

/-- **(U)**: for every `0 < q ≤ ½` and every `x ≥ 3`,
`E|∑_{n≤x} f(n)/√n|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`, `Λ = log log x`
(`RMF.integral_rpow_weightedRademacherSum_le_u_of_le_049` below `q = 0.49`,
`RMF.u_half_strip` above). -/
theorem integral_rpow_weightedRademacherSum_le_u {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 3 ≤ x) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  rcases le_or_gt q (49 / 100) with h | h
  · exact integral_rpow_weightedRademacherSum_le_u_of_le_049 hX hx hq0 h
  · exact u_half_strip hX hx h.le hq

end RMF
