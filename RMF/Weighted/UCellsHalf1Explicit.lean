/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UHalfLeavesExplicit

/-!
# The first moment near `q = ½`: the cells, part 1

`RMF.u_cell_half` at the numerals of the cells covering `w ∈ [3 / 2, 371 / 100]`; their
certificate totals are at most `24.83` (of `25`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ∈ [1.5, 2.0]` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half`; certificate
total `24.79`). -/
theorem u_cell_half_1 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hwl : 3 / 2 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 2) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half (ql := 499833 / 1000000) (a₁ := 1667 / 10000000) (Vb := 1 / 2000)
    hX hx hΛ hq49 hq (by norm_num) hwl hwu
    (by norm_num) (Or.inr (by norm_num)) (Or.inl (by norm_num)) (by norm_num) (Or.inl (by norm_num))
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ∈ [2.0, 2.45]` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half`; certificate
total `24.83`). -/
theorem u_cell_half_2 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hwl : 2 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 49 / 20) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half (ql := 99959 / 200000) (a₁ := 1021 / 5000000) (Vb := 23 / 40000)
    hX hx hΛ hq49 hq (by norm_num) hwl hwu
    (by norm_num) (Or.inr (by norm_num)) (Or.inl (by norm_num)) (by norm_num) (Or.inl (by norm_num))
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ∈ [2.45, 2.87]` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half`; certificate
total `24.79`). -/
theorem u_cell_half_3 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hwl : 49 / 20 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 287 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half (ql := 6247 / 12500) (a₁ := 299 / 1250000) (Vb := 129 / 200000)
    hX hx hΛ hq49 hq (by norm_num) hwl hwu
    (by norm_num) (Or.inr (by norm_num)) (Or.inl (by norm_num)) (by norm_num) (Or.inl (by norm_num))
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ∈ [2.87, 3.28]` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half`; certificate
total `24.72`). -/
theorem u_cell_half_4 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hwl : 287 / 100 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 82 / 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half (ql := 249863 / 500000) (a₁ := 1367 / 5000000) (Vb := 3567 / 5000000)
    hX hx hΛ hq49 hq (by norm_num) hwl hwu
    (by norm_num) (Or.inr (by norm_num)) (Or.inl (by norm_num)) (by norm_num) (Or.inl (by norm_num))
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ∈ [3.28, 3.71]` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half`; certificate
total `24.70`). -/
theorem u_cell_half_5 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hwl : 82 / 25 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 371 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half (ql := 49969 / 100000) (a₁ := 773 / 2500000) (Vb := 157 / 200000)
    hX hx hΛ hq49 hq (by norm_num) hwl hwu
    (by norm_num) (Or.inr (by norm_num)) (Or.inl (by norm_num)) (by norm_num) (Or.inl (by norm_num))
    (by interval_decide (trust := kernel))

end RMF
