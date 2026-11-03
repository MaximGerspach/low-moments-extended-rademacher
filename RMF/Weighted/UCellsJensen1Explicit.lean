/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UJensenCellExplicit

/-!
# The Jensen regime's cells, part 1

`RMF.u_cell_jensen` at the numerals of the cells `q ∈ [0.43, 0.45]`, `Λ ∈ [110, 330]`,
`[330, 1100]` and `[1100, 4000]`; their certificate totals are `12.68`, `15.63` and `20.50`
(of `25`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The Jensen regime's cell `q ∈ [0.43, 0.45]`, `Λ ∈ [110, 330]`**: `RMF.u_cell_jensen` at its
numerals (certificate total `12.68`). -/
theorem u_cell_jensen_1 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛl : 110 ≤ Real.log (Real.log x))
    (hΛu : Real.log (Real.log x) ≤ 330) (hq1 : 43 / 100 ≤ q) (hq2 : q ≤ 9 / 20) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hwl, hwu⟩ := w_bounds_of_cell hq1 hq2 (by norm_num) hΛl hΛu (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 9 / 20) (b := 22077 / 12500)
    (c := 13803 / 125000) (Gb := 1093 / 500) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 9 / 20) (b := 18217 / 12500)
    (c := 408739 / 10000000) (Gb := 491 / 250) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 9 / 20) (b := 134641 / 100000)
    (c := 152939 / 10000000) (Gb := 1893 / 1000) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 9 / 20) (b := 32649 / 25000)
    (c := 588533 / 100000000) (Gb := 467 / 250) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  exact u_cell_jensen hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The Jensen regime's cell `q ∈ [0.43, 0.45]`, `Λ ∈ [330, 1100]`**: `RMF.u_cell_jensen` at its
numerals (certificate total `15.63`). -/
theorem u_cell_jensen_2 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛl : 330 ≤ Real.log (Real.log x))
    (hΛu : Real.log (Real.log x) ≤ 1100) (hq1 : 43 / 100 ≤ q) (hq2 : q ≤ 9 / 20) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hwl, hwu⟩ := w_bounds_of_cell hq1 hq2 (by norm_num) hΛl hΛu (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 9 / 20) (b := 22077 / 12500)
    (c := 13803 / 125000) (Gb := 1093 / 500) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 9 / 20) (b := 18217 / 12500)
    (c := 408739 / 10000000) (Gb := 491 / 250) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 9 / 20) (b := 134641 / 100000)
    (c := 152939 / 10000000) (Gb := 1893 / 1000) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 9 / 20) (b := 32649 / 25000)
    (c := 588533 / 100000000) (Gb := 467 / 250) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  exact u_cell_jensen hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The Jensen regime's cell `q ∈ [0.43, 0.45]`, `Λ ∈ [1100, 4000]`**: `RMF.u_cell_jensen` at its
numerals (certificate total `20.50`). -/
theorem u_cell_jensen_3 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛl : 1100 ≤ Real.log (Real.log x))
    (hΛu : Real.log (Real.log x) ≤ 4000) (hq1 : 43 / 100 ≤ q) (hq2 : q ≤ 9 / 20) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hwl, hwu⟩ := w_bounds_of_cell hq1 hq2 (by norm_num) hΛl hΛu (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 9 / 20) (b := 22077 / 12500)
    (c := 13803 / 125000) (Gb := 1093 / 500) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 9 / 20) (b := 18217 / 12500)
    (c := 408739 / 10000000) (Gb := 491 / 250) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 9 / 20) (b := 134641 / 100000)
    (c := 152939 / 10000000) (Gb := 1893 / 1000) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 9 / 20) (b := 32649 / 25000)
    (c := 588533 / 100000000) (Gb := 467 / 250) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  exact u_cell_jensen hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

end RMF
