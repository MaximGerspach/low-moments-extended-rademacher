/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UMidCellExplicit

/-!
# The middle range's cells, part 3

`RMF.u_cell_mid` at the numerals of the cells `q ∈ [0.47, 0.48]`, `Λ ∈ [7, 12]`, `[12, 20]`,
`[20, 35]`, `[35, 60]` and `[60, 110]`; their certificate totals are `16.22`, `15.99`, `16.94`,
`17.47`, `17.98` (of `25`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The middle range's cell `q ∈ [0.47, 0.48]`, `Λ ∈ [7, 12]`**: `RMF.u_cell_mid` at its
numerals (certificate total `16.22`). -/
theorem u_cell_mid_11 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) (hΛl : 7 ≤ Real.log (Real.log x))
    (hΛu : Real.log (Real.log x) ≤ 12) (hq1 : 47 / 100 ≤ q) (hq2 : q ≤ 12 / 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hwl, hwu⟩ := w_bounds_of_cell hq1 hq2 (by norm_num) hΛl hΛu (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 82111 / 50000) (c := 86267 / 500000) (Gb := 459 / 200) (by norm_num) (by norm_num)
    (by norm_num) 4 uChaosEps_4 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 135509 / 100000) (c := 20597 / 200000) (Gb := 258 / 125) (by norm_num) (by norm_num)
    (by norm_num) 5 uChaosEps_5 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 125193 / 100000) (c := 774041 / 10000000) (Gb := 1989 / 1000) (by norm_num) (by norm_num)
    (by norm_num) 6 uChaosEps_6 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 121431 / 100000) (c := 169989 / 2500000) (Gb := 1963 / 1000) (by norm_num) (by norm_num)
    (by norm_num) 7 uChaosEps_7 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  exact u_cell_mid hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu (fun w _ => one_add_mul_exp_neg_le_max (by norm_num))
    hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The middle range's cell `q ∈ [0.47, 0.48]`, `Λ ∈ [12, 20]`**: `RMF.u_cell_mid` at its
numerals (certificate total `15.99`). -/
theorem u_cell_mid_12 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) (hΛl : 12 ≤ Real.log (Real.log x))
    (hΛu : Real.log (Real.log x) ≤ 20) (hq1 : 47 / 100 ≤ q) (hq2 : q ≤ 12 / 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hwl, hwu⟩ := w_bounds_of_cell hq1 hq2 (by norm_num) hΛl hΛu (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 82111 / 50000) (c := 86267 / 500000) (Gb := 459 / 200) (by norm_num) (by norm_num)
    (by norm_num) 4 uChaosEps_4 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 135509 / 100000) (c := 20597 / 200000) (Gb := 258 / 125) (by norm_num) (by norm_num)
    (by norm_num) 5 uChaosEps_5 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 125193 / 100000) (c := 774041 / 10000000) (Gb := 1989 / 1000) (by norm_num) (by norm_num)
    (by norm_num) 6 uChaosEps_6 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 121431 / 100000) (c := 169989 / 2500000) (Gb := 1963 / 1000) (by norm_num) (by norm_num)
    (by norm_num) 7 uChaosEps_7 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  exact u_cell_mid hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu (fun w _ => one_add_mul_exp_neg_le_max (by norm_num))
    hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The middle range's cell `q ∈ [0.47, 0.48]`, `Λ ∈ [20, 35]`**: `RMF.u_cell_mid` at its
numerals (certificate total `16.94`). -/
theorem u_cell_mid_13 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) (hΛl : 20 ≤ Real.log (Real.log x))
    (hΛu : Real.log (Real.log x) ≤ 35) (hq1 : 47 / 100 ≤ q) (hq2 : q ≤ 12 / 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hwl, hwu⟩ := w_bounds_of_cell hq1 hq2 (by norm_num) hΛl hΛu (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 82111 / 50000) (c := 86267 / 500000) (Gb := 459 / 200) (by norm_num) (by norm_num)
    (by norm_num) 4 uChaosEps_4 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 135509 / 100000) (c := 20597 / 200000) (Gb := 258 / 125) (by norm_num) (by norm_num)
    (by norm_num) 5 uChaosEps_5 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 125193 / 100000) (c := 774041 / 10000000) (Gb := 1989 / 1000) (by norm_num) (by norm_num)
    (by norm_num) 6 uChaosEps_6 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 121431 / 100000) (c := 169989 / 2500000) (Gb := 1963 / 1000) (by norm_num) (by norm_num)
    (by norm_num) 7 uChaosEps_7 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  exact u_cell_mid hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu (fun w _ => one_add_mul_exp_neg_le_max (by norm_num))
    hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The middle range's cell `q ∈ [0.47, 0.48]`, `Λ ∈ [35, 60]`**: `RMF.u_cell_mid` at its
numerals (certificate total `17.47`). -/
theorem u_cell_mid_14 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) (hΛl : 35 ≤ Real.log (Real.log x))
    (hΛu : Real.log (Real.log x) ≤ 60) (hq1 : 47 / 100 ≤ q) (hq2 : q ≤ 12 / 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hwl, hwu⟩ := w_bounds_of_cell hq1 hq2 (by norm_num) hΛl hΛu (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 82111 / 50000) (c := 86267 / 500000) (Gb := 459 / 200) (by norm_num) (by norm_num)
    (by norm_num) 4 uChaosEps_4 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 135509 / 100000) (c := 20597 / 200000) (Gb := 258 / 125) (by norm_num) (by norm_num)
    (by norm_num) 5 uChaosEps_5 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 125193 / 100000) (c := 774041 / 10000000) (Gb := 1989 / 1000) (by norm_num) (by norm_num)
    (by norm_num) 6 uChaosEps_6 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 121431 / 100000) (c := 169989 / 2500000) (Gb := 1963 / 1000) (by norm_num) (by norm_num)
    (by norm_num) 7 uChaosEps_7 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  exact u_cell_mid hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu (fun w hw => one_add_mul_exp_neg_anti (by norm_num) (by norm_num) hw)
    hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The middle range's cell `q ∈ [0.47, 0.48]`, `Λ ∈ [60, 110]`**: `RMF.u_cell_mid` at its
numerals (certificate total `17.98`). -/
theorem u_cell_mid_15 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) (hΛl : 60 ≤ Real.log (Real.log x))
    (hΛu : Real.log (Real.log x) ≤ 110) (hq1 : 47 / 100 ≤ q) (hq2 : q ≤ 12 / 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hwl, hwu⟩ := w_bounds_of_cell hq1 hq2 (by norm_num) hΛl hΛu (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 82111 / 50000) (c := 86267 / 500000) (Gb := 459 / 200) (by norm_num) (by norm_num)
    (by norm_num) 4 uChaosEps_4 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 135509 / 100000) (c := 20597 / 200000) (Gb := 258 / 125) (by norm_num) (by norm_num)
    (by norm_num) 5 uChaosEps_5 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 125193 / 100000) (c := 774041 / 10000000) (Gb := 1989 / 1000) (by norm_num) (by norm_num)
    (by norm_num) 6 uChaosEps_6 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of_log (ql := 47 / 100) (qu := 12 / 25) (Ly := 144)
    (b := 121431 / 100000) (c := 169989 / 2500000) (Gb := 1963 / 1000) (by norm_num) (by norm_num)
    (by norm_num) 7 uChaosEps_7 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  exact u_cell_mid hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu (fun w hw => one_add_mul_exp_neg_anti (by norm_num) (by norm_num) hw)
    hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

end RMF
