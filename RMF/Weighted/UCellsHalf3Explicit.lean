/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UHalfLeavesExplicit

/-!
# The first moment near `q = ½`: the cells, part 3

`RMF.u_cell_half` and `RMF.u_cell_half_large` at the numerals of the cells covering
`w ≥ 159 / 20`; their certificate totals are at most `24.85` (of `25`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ∈ [7.95, 10.3]` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half`; certificate
total `24.76`). -/
theorem u_cell_half_11 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hwl : 159 / 20 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 103 / 10) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half (ql := 499141 / 1000000) (a₁ := 67 / 78125) (Vb := 471 / 250000)
    hX hx hΛ hq49 hq (by norm_num) hwl hwu
    (by norm_num) (Or.inr (by norm_num)) (Or.inr (by norm_num)) (by norm_num) (Or.inl (by norm_num))
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ∈ [10.3, 14.9]` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half`; certificate
total `24.78`). -/
theorem u_cell_half_12 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hwl : 103 / 10 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 149 / 10) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half (ql := 249379 / 500000) (a₁ := 1239 / 1000000) (Vb := 53 / 20000)
    hX hx hΛ hq49 hq (by norm_num) hwl hwu
    (by norm_num) (Or.inr (by norm_num)) (Or.inr (by norm_num)) (by norm_num) (Or.inl (by norm_num))
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ∈ [14.9, 28.4]` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half`; certificate
total `24.85`). -/
theorem u_cell_half_13 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hwl : 149 / 10 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 142 / 5) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half (ql := 497633 / 1000000) (a₁ := 589 / 250000) (Vb := 49 / 10000)
    hX hx hΛ hq49 hq (by norm_num) hwl hwu
    (by norm_num) (Or.inr (by norm_num)) (Or.inr (by norm_num)) (by norm_num) (Or.inl (by norm_num))
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ∈ [28.4, 85.2]` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half`; certificate
total `23.37`). -/
theorem u_cell_half_14 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hwl : 142 / 5 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 426 / 5) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half (ql := 4929 / 10000) (a₁ := 7 / 1000) (Vb := 1437 / 100000)
    hX hx hΛ hq49 hq (by norm_num) hwl hwu
    (by norm_num) (Or.inr (by norm_num)) (Or.inr (by norm_num)) (by norm_num) (Or.inl (by norm_num))
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ≥ 85.2` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half_large`; certificate
total `22.67`). -/
theorem u_cell_half_top {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hw : 426 / 5 ≤ (1 - 2 * q) * Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half_large (W := 426 / 5) hX hx hΛ hq49 hq (by norm_num) hw
    (by interval_decide (trust := kernel))

end RMF
