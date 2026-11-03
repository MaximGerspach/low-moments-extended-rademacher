/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UCellsHalf1Explicit
import RMF.Weighted.UCellsHalf2Explicit
import RMF.Weighted.UCellsHalf3Explicit

/-!
# The first moment near `q = ½` past `Λ = 6000`

For `Λ = log log x ≥ 6000`, `q ∈ [0.49, ½)` and `w = (1 - 2q)Λ ≥ 3/2`, the bound (U),
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (`RMF.u_half_chaos_regime`), from the 15 cells
`RMF.u_cell_half_1`, …, `RMF.u_cell_half_14` and `RMF.u_cell_half_top` (certificate totals at
most `24.85`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **(U) near `q = ½` past `Λ = 6000`**: for `Λ = log log x ≥ 6000`, `q ∈ [0.49, ½)` and
`w = (1 - 2q)Λ ≥ 3/2`, `E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (the cells
`RMF.u_cell_half_1`, …, `_14` and `RMF.u_cell_half_top`). -/
theorem u_half_chaos_regime {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hw : 3 / 2 ≤ (1 - 2 * q) * Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) 2 with h1 | h1
  · exact u_cell_half_1 hX hx hΛ hq49 hq hw h1
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (49 / 20) with h2 | h2
  · exact u_cell_half_2 hX hx hΛ hq49 hq h1.le h2
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (287 / 100) with h3 | h3
  · exact u_cell_half_3 hX hx hΛ hq49 hq h2.le h3
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (82 / 25) with h4 | h4
  · exact u_cell_half_4 hX hx hΛ hq49 hq h3.le h4
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (371 / 100) with h5 | h5
  · exact u_cell_half_5 hX hx hΛ hq49 hq h4.le h5
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (21 / 5) with h6 | h6
  · exact u_cell_half_6 hX hx hΛ hq49 hq h5.le h6
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (479 / 100) with h7 | h7
  · exact u_cell_half_7 hX hx hΛ hq49 hq h6.le h7
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (551 / 100) with h8 | h8
  · exact u_cell_half_8 hX hx hΛ hq49 hq h7.le h8
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (651 / 100) with h9 | h9
  · exact u_cell_half_9 hX hx hΛ hq49 hq h8.le h9
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (159 / 20) with h10 | h10
  · exact u_cell_half_10 hX hx hΛ hq49 hq h9.le h10
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (103 / 10) with h11 | h11
  · exact u_cell_half_11 hX hx hΛ hq49 hq h10.le h11
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (149 / 10) with h12 | h12
  · exact u_cell_half_12 hX hx hΛ hq49 hq h11.le h12
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (142 / 5) with h13 | h13
  · exact u_cell_half_13 hX hx hΛ hq49 hq h12.le h13
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (426 / 5) with h14 | h14
  · exact u_cell_half_14 hX hx hΛ hq49 hq h13.le h14
  exact u_cell_half_top hX hx hΛ hq49 hq h14.le

end RMF
