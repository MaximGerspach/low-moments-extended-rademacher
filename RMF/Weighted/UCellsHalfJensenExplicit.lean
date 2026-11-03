/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UMidCellExplicit

/-!
# The first moment near `q = ½`: the Jensen and middle ranges

For `q ∈ [0.49, ½)` with `w = (1 - 2q)Λ ≥ 3/2`: the cells of `RMF.u_cell_jensen` covering
`110 ≤ Λ ≤ 6000` (`RMF.u_half_jensen_regime`, 6 cells in `(Λ, w)`, certificate totals at most
`24.84`) and the one cell of `RMF.u_cell_mid` covering `75 ≤ Λ ≤ 110` (total `14.90`), with `q`'s
range from `w` and `Λ` (`RMF.q_bounds_of_w`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`q` from `w`**: for `q ≤ ½`, `Λ ∈ [Λ_l, Λ_u]` and `w = (1 - 2q)Λ ∈ [w_l, w_u]`,
`½ - w_u/(2Λ_l) ≤ q ≤ ½ - w_l/(2Λ_u)`. -/
lemma q_bounds_of_w {q Λ Λl Λu wl wu ql qu : ℝ} (hΛl : Λl ≤ Λ) (hΛu : Λ ≤ Λu) (hΛl0 : 0 < Λl)
    (hq : q ≤ 1 / 2) (hwl : wl ≤ (1 - 2 * q) * Λ) (hwu : (1 - 2 * q) * Λ ≤ wu)
    (hql : ql ≤ 49 / 100 ∨ ql ≤ 1 / 2 - wu / (2 * Λl)) (hq49 : 49 / 100 ≤ q)
    (hqu : 1 / 2 - wl / (2 * Λu) ≤ qu) : ql ≤ q ∧ q ≤ qu := by
  have hv : 0 ≤ 1 - 2 * q := by linarith
  have h1 : (1 - 2 * q) * Λl ≤ (1 - 2 * q) * Λ := mul_le_mul_of_nonneg_left hΛl hv
  have h2 : (1 - 2 * q) * Λ ≤ (1 - 2 * q) * Λu := mul_le_mul_of_nonneg_left hΛu hv
  have hΛu0 : 0 < Λu := by linarith
  constructor
  · rcases hql with h | h
    · linarith
    · have h3 : 1 - 2 * q ≤ wu / Λl := by rw [le_div_iff₀ hΛl0]; linarith
      have e : wu / (2 * Λl) = wu / Λl / 2 := by ring
      linarith
  · have h3 : wl / Λu ≤ 1 - 2 * q := by rw [div_le_iff₀ hΛu0]; linarith
    have e : wl / (2 * Λu) = wl / Λu / 2 := by ring
    linarith

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The cell `Λ ∈ [110, 898]`, `w ∈ [3 / 2, 449 / 25]` near `q = ½`**: `RMF.u_cell_jensen`
at its numerals, `q ∈ [49 / 100, 99833 / 200000]` from `w = (1 - 2q)Λ`
(certificate total `24.05`). -/
theorem u_cell_half_jensen_1 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛl : 110 ≤ Real.log (Real.log x)) (hΛu : Real.log (Real.log x) ≤ 898)
    (hq49 : 49 / 100 ≤ q) (hq : q ≤ 1 / 2) (hwl : 3 / 2 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 449 / 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hq1, hq2⟩ := q_bounds_of_w (ql := 49 / 100) (qu := 99833 / 200000)
    hΛl hΛu (by norm_num) hq hwl hwu (Or.inl (by norm_num)) hq49 (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 99833 / 200000)
    (b := 6321 / 4000) (c := 13803 / 125000) (Gb := 283 / 125)
    (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 99833 / 200000)
    (b := 26079 / 20000) (c := 408739 / 10000000) (Gb := 509 / 250)
    (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 99833 / 200000)
    (b := 30117 / 25000) (c := 152939 / 10000000) (Gb := 981 / 500)
    (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 99833 / 200000)
    (b := 116849 / 100000) (c := 588533 / 100000000) (Gb := 242 / 125)
    (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  exact u_cell_jensen hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The cell `Λ ∈ [898, 6000]`, `w ∈ [3 / 2, 249 / 100]` near `q = ½`**: `RMF.u_cell_jensen`
at its numerals, `q ∈ [498613 / 1000000, 3999 / 8000]` from `w = (1 - 2q)Λ`
(certificate total `24.82`). -/
theorem u_cell_half_jensen_2 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛl : 898 ≤ Real.log (Real.log x)) (hΛu : Real.log (Real.log x) ≤ 6000)
    (hq49 : 49 / 100 ≤ q) (hq : q ≤ 1 / 2) (hwl : 3 / 2 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 249 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hq1, hq2⟩ := q_bounds_of_w (ql := 498613 / 1000000) (qu := 3999 / 8000)
    hΛl hΛu (by norm_num) hq hwl hwu (Or.inr (by norm_num)) hq49 (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 498613 / 1000000) (qu := 3999 / 8000)
    (b := 6321 / 4000) (c := 13803 / 125000) (Gb := 283 / 125)
    (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 498613 / 1000000) (qu := 3999 / 8000)
    (b := 26079 / 20000) (c := 408739 / 10000000) (Gb := 509 / 250)
    (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 498613 / 1000000) (qu := 3999 / 8000)
    (b := 30117 / 25000) (c := 152939 / 10000000) (Gb := 981 / 500)
    (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 498613 / 1000000) (qu := 3999 / 8000)
    (b := 116849 / 100000) (c := 588533 / 100000000) (Gb := 242 / 125)
    (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  exact u_cell_jensen hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The cell `Λ ∈ [898, 6000]`, `w ∈ [249 / 100, 187 / 50]` near `q = ½`**: `RMF.u_cell_jensen`
at its numerals, `q ∈ [497917 / 1000000, 499793 / 1000000]` from `w = (1 - 2q)Λ`
(certificate total `24.79`). -/
theorem u_cell_half_jensen_3 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛl : 898 ≤ Real.log (Real.log x)) (hΛu : Real.log (Real.log x) ≤ 6000)
    (hq49 : 49 / 100 ≤ q) (hq : q ≤ 1 / 2) (hwl : 249 / 100 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 187 / 50) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hq1, hq2⟩ := q_bounds_of_w (ql := 497917 / 1000000) (qu := 499793 / 1000000)
    hΛl hΛu (by norm_num) hq hwl hwu (Or.inr (by norm_num)) hq49 (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 497917 / 1000000) (qu := 499793 / 1000000)
    (b := 6321 / 4000) (c := 13803 / 125000) (Gb := 283 / 125)
    (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 497917 / 1000000) (qu := 499793 / 1000000)
    (b := 26079 / 20000) (c := 408739 / 10000000) (Gb := 509 / 250)
    (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 497917 / 1000000) (qu := 499793 / 1000000)
    (b := 30117 / 25000) (c := 152939 / 10000000) (Gb := 981 / 500)
    (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 497917 / 1000000) (qu := 499793 / 1000000)
    (b := 116849 / 100000) (c := 588533 / 100000000) (Gb := 242 / 125)
    (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  exact u_cell_jensen hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The cell `Λ ∈ [898, 6000]`, `w ∈ [187 / 50, 551 / 100]` near `q = ½`**: `RMF.u_cell_jensen`
at its numerals, `q ∈ [124233 / 250000, 499689 / 1000000]` from `w = (1 - 2q)Λ`
(certificate total `24.80`). -/
theorem u_cell_half_jensen_4 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛl : 898 ≤ Real.log (Real.log x)) (hΛu : Real.log (Real.log x) ≤ 6000)
    (hq49 : 49 / 100 ≤ q) (hq : q ≤ 1 / 2) (hwl : 187 / 50 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 551 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hq1, hq2⟩ := q_bounds_of_w (ql := 124233 / 250000) (qu := 499689 / 1000000)
    hΛl hΛu (by norm_num) hq hwl hwu (Or.inr (by norm_num)) hq49 (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 124233 / 250000) (qu := 499689 / 1000000)
    (b := 6321 / 4000) (c := 13803 / 125000) (Gb := 283 / 125)
    (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 124233 / 250000) (qu := 499689 / 1000000)
    (b := 26079 / 20000) (c := 408739 / 10000000) (Gb := 509 / 250)
    (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 124233 / 250000) (qu := 499689 / 1000000)
    (b := 30117 / 25000) (c := 152939 / 10000000) (Gb := 981 / 500)
    (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 124233 / 250000) (qu := 499689 / 1000000)
    (b := 116849 / 100000) (c := 588533 / 100000000) (Gb := 242 / 125)
    (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  exact u_cell_jensen hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The cell `Λ ∈ [898, 6000]`, `w ∈ [551 / 100, 101 / 10]` near `q = ½`**: `RMF.u_cell_jensen`
at its numerals, `q ∈ [61797 / 125000, 499541 / 1000000]` from `w = (1 - 2q)Λ`
(certificate total `24.84`). -/
theorem u_cell_half_jensen_5 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛl : 898 ≤ Real.log (Real.log x)) (hΛu : Real.log (Real.log x) ≤ 6000)
    (hq49 : 49 / 100 ≤ q) (hq : q ≤ 1 / 2) (hwl : 551 / 100 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 101 / 10) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hq1, hq2⟩ := q_bounds_of_w (ql := 61797 / 125000) (qu := 499541 / 1000000)
    hΛl hΛu (by norm_num) hq hwl hwu (Or.inr (by norm_num)) hq49 (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 61797 / 125000) (qu := 499541 / 1000000)
    (b := 6321 / 4000) (c := 13803 / 125000) (Gb := 283 / 125)
    (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 61797 / 125000) (qu := 499541 / 1000000)
    (b := 26079 / 20000) (c := 408739 / 10000000) (Gb := 509 / 250)
    (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 61797 / 125000) (qu := 499541 / 1000000)
    (b := 30117 / 25000) (c := 152939 / 10000000) (Gb := 981 / 500)
    (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 61797 / 125000) (qu := 499541 / 1000000)
    (b := 116849 / 100000) (c := 588533 / 100000000) (Gb := 242 / 125)
    (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  exact u_cell_jensen hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The cell `Λ ∈ [898, 6000]`, `w ∈ [101 / 10, 120]` near `q = ½`**: `RMF.u_cell_jensen`
at its numerals, `q ∈ [49 / 100, 499159 / 1000000]` from `w = (1 - 2q)Λ`
(certificate total `23.92`). -/
theorem u_cell_half_jensen_6 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛl : 898 ≤ Real.log (Real.log x)) (hΛu : Real.log (Real.log x) ≤ 6000)
    (hq49 : 49 / 100 ≤ q) (hq : q ≤ 1 / 2) (hwl : 101 / 10 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 120) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hq1, hq2⟩ := q_bounds_of_w (ql := 49 / 100) (qu := 499159 / 1000000)
    hΛl hΛu (by norm_num) hq hwl hwu (Or.inl (by norm_num)) hq49 (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 499159 / 1000000)
    (b := 6321 / 4000) (c := 13803 / 125000) (Gb := 283 / 125)
    (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 499159 / 1000000)
    (b := 26079 / 20000) (c := 408739 / 10000000) (Gb := 509 / 250)
    (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 499159 / 1000000)
    (b := 30117 / 25000) (c := 152939 / 10000000) (Gb := 981 / 500)
    (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 499159 / 1000000)
    (b := 116849 / 100000) (c := 588533 / 100000000) (Gb := 242 / 125)
    (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  exact u_cell_jensen hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 2000000 in
-- five kernel-checked numerals
/-- **The cell `Λ ∈ [75, 110]`, `w ∈ [3 / 2, 11 / 5]` near `q = ½`**: `RMF.u_cell_mid`
at its numerals, `q ∈ [49 / 100, 246591 / 500000]` from `w = (1 - 2q)Λ`
(certificate total `14.90`). -/
theorem u_cell_half_mid {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp (Real.exp 7) ≤ x)
    (hΛl : 75 ≤ Real.log (Real.log x)) (hΛu : Real.log (Real.log x) ≤ 110)
    (hq49 : 49 / 100 ≤ q) (hq : q ≤ 1 / 2) (hwl : 3 / 2 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ 11 / 5) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hq1, hq2⟩ := q_bounds_of_w (ql := 49 / 100) (qu := 246591 / 500000)
    hΛl hΛu (by norm_num) hq hwl hwu (Or.inl (by norm_num)) hq49 (by norm_num)
  have hG1 := thetaWindowConstQ_rpow_le_of_log (ql := 49 / 100) (qu := 246591 / 500000)
    (Ly := 144) (b := 6321 / 4000) (c := 86267 / 500000) (Gb := 292 / 125)
    (by norm_num) (by norm_num) (by norm_num) 4 uChaosEps_4 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG2 := thetaWindowConstQ_rpow_le_of_log (ql := 49 / 100) (qu := 246591 / 500000)
    (Ly := 144) (b := 26079 / 20000) (c := 20597 / 200000) (Gb := 21 / 10)
    (by norm_num) (by norm_num) (by norm_num) 5 uChaosEps_5 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG3 := thetaWindowConstQ_rpow_le_of_log (ql := 49 / 100) (qu := 246591 / 500000)
    (Ly := 144) (b := 30117 / 25000) (c := 774041 / 10000000) (Gb := 253 / 125)
    (by norm_num) (by norm_num) (by norm_num) 6 uChaosEps_6 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  have hG4 := thetaWindowConstQ_rpow_le_of_log (ql := 49 / 100) (qu := 246591 / 500000)
    (Ly := 144) (b := 116849 / 100000) (c := 169989 / 2500000) (Gb := 1997 / 1000)
    (by norm_num) (by norm_num) (by norm_num) 7 uChaosEps_7 (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  exact u_cell_mid hX hx hΛl hΛu (by norm_num) (by norm_num) hq1 hq2 (by norm_num) hwl
    (by norm_num) hwu (fun w hw => one_add_mul_exp_neg_anti (by norm_num) (by norm_num) hw)
    hG1 hG2 hG3 hG4 (by norm_num) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))

/-- **(U) near `q = ½` for `110 ≤ Λ ≤ 6000`**: for `q ∈ [0.49, ½)` and `w = (1 - 2q)Λ ≥ 3/2`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (the cells `RMF.u_cell_half_jensen_1`, …, `_6`). -/
theorem u_half_jensen_regime {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : Real.log (Real.log x) ≤ 6000)
    (hq49 : 49 / 100 ≤ q) (hq : q ≤ 1 / 2) (hw : 3 / 2 ≤ (1 - 2 * q) * Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨-, -, hΛ110, -, -, -⟩ := half_params hx
  have hwtop : (1 - 2 * q) * Real.log (Real.log x) ≤ Real.log (Real.log x) / 50 := by
    have := mul_le_mul_of_nonneg_right (by linarith : 1 - 2 * q ≤ 1 / 50)
      (by linarith : (0 : ℝ) ≤ Real.log (Real.log x))
    linarith
  rcases le_or_gt (Real.log (Real.log x)) 898 with hb0 | hb0
  · exact u_cell_half_jensen_1 hX hx (by linarith) hb0 hq49 hq hw (by linarith)
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (249 / 100) with h2 | h2
  · exact u_cell_half_jensen_2 hX hx (by linarith) hΛ hq49 hq hw h2
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (187 / 50) with h3 | h3
  · exact u_cell_half_jensen_3 hX hx (by linarith) hΛ hq49 hq h2.le h3
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (551 / 100) with h4 | h4
  · exact u_cell_half_jensen_4 hX hx (by linarith) hΛ hq49 hq h3.le h4
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (101 / 10) with h5 | h5
  · exact u_cell_half_jensen_5 hX hx (by linarith) hΛ hq49 hq h4.le h5
  exact u_cell_half_jensen_6 hX hx (by linarith) hΛ hq49 hq h5.le (by linarith)

end RMF
