/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UJensenCellExplicit

/-!
# The Jensen regime's cells, part 2

`RMF.u_cell_jensen` at the numerals of the cells `q ∈ [0.45, 0.47]`, `Λ ∈ [110, 330]`,
`[330, 1100]` and `[1100, 4000]`; their certificate totals are `13.82`, `16.27` and `21.35`
(of `25`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The Jensen regime's cell `q ∈ [0.45, 0.47]`, `Λ ∈ [110, 330]`**: `RMF.u_cell_jensen` at its
numerals (certificate total `13.82`). -/
theorem u_cell_jensen_4 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛl : 110 ≤ Real.log (Real.log x))
    (hΛu : Real.log (Real.log x) ≤ 330) (hq1 : 9 / 20 ≤ q) (hq2 : q ≤ 47 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hwl, hwu⟩ := w_bounds_of_cell hq1 hq2 (by norm_num) hΛl hΛu (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 47 / 100) (b := 170419 / 100000)
    (c := 13803 / 125000) (Gb := 1113 / 500) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 47 / 100) (b := 70311 / 50000)
    (c := 408739 / 10000000) (Gb := 1999 / 1000) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 47 / 100) (b := 129917 / 100000)
    (c := 152939 / 10000000) (Gb := 77 / 40) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 47 / 100) (b := 63007 / 50000)
    (c := 588533 / 100000000) (Gb := 19 / 10) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  exact u_cell_jensen hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The Jensen regime's cell `q ∈ [0.45, 0.47]`, `Λ ∈ [330, 1100]`**: `RMF.u_cell_jensen` at its
numerals (certificate total `16.27`). -/
theorem u_cell_jensen_5 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛl : 330 ≤ Real.log (Real.log x))
    (hΛu : Real.log (Real.log x) ≤ 1100) (hq1 : 9 / 20 ≤ q) (hq2 : q ≤ 47 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hwl, hwu⟩ := w_bounds_of_cell hq1 hq2 (by norm_num) hΛl hΛu (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 47 / 100) (b := 170419 / 100000)
    (c := 13803 / 125000) (Gb := 1113 / 500) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 47 / 100) (b := 70311 / 50000)
    (c := 408739 / 10000000) (Gb := 1999 / 1000) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 47 / 100) (b := 129917 / 100000)
    (c := 152939 / 10000000) (Gb := 77 / 40) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 47 / 100) (b := 63007 / 50000)
    (c := 588533 / 100000000) (Gb := 19 / 10) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  exact u_cell_jensen hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The Jensen regime's cell `q ∈ [0.45, 0.47]`, `Λ ∈ [1100, 4000]`**: `RMF.u_cell_jensen` at its
numerals (certificate total `21.35`). -/
theorem u_cell_jensen_6 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛl : 1100 ≤ Real.log (Real.log x))
    (hΛu : Real.log (Real.log x) ≤ 4000) (hq1 : 9 / 20 ≤ q) (hq2 : q ≤ 47 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hwl, hwu⟩ := w_bounds_of_cell hq1 hq2 (by norm_num) hΛl hΛu (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 47 / 100) (b := 170419 / 100000)
    (c := 13803 / 125000) (Gb := 1113 / 500) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 47 / 100) (b := 70311 / 50000)
    (c := 408739 / 10000000) (Gb := 1999 / 1000) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 47 / 100) (b := 129917 / 100000)
    (c := 152939 / 10000000) (Gb := 77 / 40) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 47 / 100) (b := 63007 / 50000)
    (c := 588533 / 100000000) (Gb := 19 / 10) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  exact u_cell_jensen hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

end RMF
