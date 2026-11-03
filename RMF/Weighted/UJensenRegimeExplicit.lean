/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UChaosRegimeExplicit
import RMF.Weighted.UCellsJensen1Explicit
import RMF.Weighted.UCellsJensen2Explicit
import RMF.Weighted.UCellsJensen3Explicit
import RMF.Weighted.UCellsJensen4Explicit

/-!
# The first moment below `q = ½`: `q ∈ [0.41, 0.49]` past `x = exp(e^{110})`

`RMF.u_jensen_regime` (`110 ≤ Λ ≤ 4000`, from the twelve cells of
`RMF/Weighted/UCellsJensen*Explicit.lean`, certificate totals at most `22.53`) and
`RMF.u_large_regime`: with the chaos regime `RMF.u_chaos_regime`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` for every `x ≥ exp(e^{110})` and `q ∈ [0.41, 0.49]`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Jensen regime of (U)**: for `x ≥ exp(e^{110})` with `Λ = log log x ≤ 4000` and
`q ∈ [0.41, 0.49]`, `E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (the cells
`RMF.u_cell_jensen_1`, …, `_12`). -/
theorem u_jensen_regime {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛu : Real.log (Real.log x) ≤ 4000)
    (hq1 : 41 / 100 ≤ q) (hq2 : q ≤ 49 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨-, -, hΛ110, -, -, -⟩ := half_params hx
  rcases le_or_gt q (43 / 100) with hq0 | hq0
  · rcases le_or_gt (Real.log (Real.log x)) 330 with hL1 | hL1
    · exact u_cell_jensen_10 hX hx hΛ110 hL1 hq1 hq0
    rcases le_or_gt (Real.log (Real.log x)) 1100 with hL2 | hL2
    · exact u_cell_jensen_11 hX hx hL1.le hL2 hq1 hq0
    · exact u_cell_jensen_12 hX hx hL2.le hΛu hq1 hq0
  rcases le_or_gt q (9 / 20) with hqa | hqa
  · rcases le_or_gt (Real.log (Real.log x)) 330 with hL1 | hL1
    · exact u_cell_jensen_1 hX hx hΛ110 hL1 hq0.le hqa
    rcases le_or_gt (Real.log (Real.log x)) 1100 with hL2 | hL2
    · exact u_cell_jensen_2 hX hx hL1.le hL2 hq0.le hqa
    · exact u_cell_jensen_3 hX hx hL2.le hΛu hq0.le hqa
  rcases le_or_gt q (47 / 100) with hqb | hqb
  · rcases le_or_gt (Real.log (Real.log x)) 330 with hL1 | hL1
    · exact u_cell_jensen_4 hX hx hΛ110 hL1 hqa.le hqb
    rcases le_or_gt (Real.log (Real.log x)) 1100 with hL2 | hL2
    · exact u_cell_jensen_5 hX hx hL1.le hL2 hqa.le hqb
    · exact u_cell_jensen_6 hX hx hL2.le hΛu hqa.le hqb
  · rcases le_or_gt (Real.log (Real.log x)) 330 with hL1 | hL1
    · exact u_cell_jensen_7 hX hx hΛ110 hL1 hqb.le hq2
    rcases le_or_gt (Real.log (Real.log x)) 1100 with hL2 | hL2
    · exact u_cell_jensen_8 hX hx hL1.le hL2 hqb.le hq2
    · exact u_cell_jensen_9 hX hx hL2.le hΛu hqb.le hq2

/-- **(U) for `q ∈ [0.41, 0.49]` past `x = exp(e^{110})`**:
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`, by the Jensen regime up to `Λ = 4000`
(`RMF.u_jensen_regime`) and the chaos regime beyond (`RMF.u_chaos_regime`). -/
theorem u_large_regime {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hq1 : 41 / 100 ≤ q) (hq2 : q ≤ 49 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  rcases le_or_gt (Real.log (Real.log x)) 4000 with h | h
  · exact u_jensen_regime hX hx h hq1 hq2
  · exact u_chaos_regime hX hx h.le hq1 hq2

end RMF
