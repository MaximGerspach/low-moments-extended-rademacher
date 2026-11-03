/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UHalfLeavesExplicit

/-!
# The first moment near `q = ½`: the cells, part 2

`RMF.u_cell_half` at the numerals of the cells covering `w ∈ [371 / 100, 159 / 20]`; their
certificate totals are at most `24.82` (of `25`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ∈ [3.71, 4.2]` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half`; certificate
total `24.75`). -/
theorem u_cell_half_6 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hwl : 371 / 100 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 21 / 5) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half (ql := 9993 / 20000) (a₁ := 1749 / 5000000) (Vb := 8667 / 10000000)
    hX hx hΛ hq49 hq (by norm_num) hwl hwu
    (by norm_num) (Or.inr (by norm_num)) (Or.inr (by norm_num)) (by norm_num) (Or.inl (by norm_num))
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ∈ [4.2, 4.79]` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half`; certificate
total `24.80`). -/
theorem u_cell_half_7 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hwl : 21 / 5 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 479 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half (ql := 1249 / 2500) (a₁ := 499 / 1250000) (Vb := 193 / 200000)
    hX hx hΛ hq49 hq (by norm_num) hwl hwu
    (by norm_num) (Or.inr (by norm_num)) (Or.inl (by norm_num)) (by norm_num) (Or.inl (by norm_num))
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ∈ [4.79, 5.51]` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half`; certificate
total `24.72`). -/
theorem u_cell_half_8 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hwl : 479 / 100 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 551 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half (ql := 24977 / 50000) (a₁ := 287 / 625000) (Vb := 217 / 200000)
    hX hx hΛ hq49 hq (by norm_num) hwl hwu
    (by norm_num) (Or.inr (by norm_num)) (Or.inl (by norm_num)) (by norm_num) (Or.inl (by norm_num))
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ∈ [5.51, 6.51]` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half`; certificate
total `24.82`). -/
theorem u_cell_half_9 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hwl : 551 / 100 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 651 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half (ql := 499457 / 1000000) (a₁ := 217 / 400000) (Vb := 313 / 250000)
    hX hx hΛ hq49 hq (by norm_num) hwl hwu
    (by norm_num) (Or.inr (by norm_num)) (Or.inr (by norm_num)) (by norm_num) (Or.inl (by norm_num))
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **The cell `w ∈ [6.51, 7.95]` near `q = ½`** for `Λ ≥ 6000` (`RMF.u_cell_half`; certificate
total `24.76`). -/
theorem u_cell_half_10 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hwl : 651 / 100 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 159 / 20) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  u_cell_half (ql := 499337 / 1000000) (a₁ := 3311 / 5000000) (Vb := 373 / 250000)
    hX hx hΛ hq49 hq (by norm_num) hwl hwu
    (by norm_num) (Or.inr (by norm_num)) (Or.inr (by norm_num)) (by norm_num) (Or.inl (by norm_num))
    (by interval_decide (trust := kernel))

end RMF
