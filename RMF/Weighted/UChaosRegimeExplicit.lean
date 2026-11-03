/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UCellsChaos1Explicit
import RMF.Weighted.UCellsChaos2Explicit
import RMF.Weighted.UCellsChaos3Explicit
import RMF.Weighted.UCellsChaos4Explicit

/-!
# The first moment below `q = ½`: the chaos regime

For `Λ = log log x ≥ 4000` and `0.41 ≤ q ≤ 0.49`, the bound (U),
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (`RMF.u_chaos_regime`), from the eight cells of
`RMF/Weighted/UCellsChaos*Explicit.lean` (certificate totals at most `24.42`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The chaos regime of (U)**: for `Λ = log log x ≥ 4000` and `q ∈ [0.41, 0.49]`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (the cells `RMF.u_cell_chaos_1`, …, `_8`). -/
theorem u_chaos_regime {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 4000 ≤ Real.log (Real.log x))
    (hq1 : 41 / 100 ≤ q) (hq2 : q ≤ 49 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  rcases le_or_gt q (21 / 50) with h7 | h7
  · exact u_cell_chaos_7 hX hx hΛ hq1 h7
  rcases le_or_gt q (43 / 100) with h0 | h0
  · exact u_cell_chaos_8 hX hx hΛ h7.le h0
  rcases le_or_gt q (11 / 25) with h1 | h1
  · exact u_cell_chaos_1 hX hx hΛ h0.le h1
  rcases le_or_gt q (9 / 20) with h2 | h2
  · exact u_cell_chaos_2 hX hx hΛ h1.le h2
  rcases le_or_gt q (23 / 50) with h3 | h3
  · exact u_cell_chaos_3 hX hx hΛ h2.le h3
  rcases le_or_gt q (47 / 100) with h4 | h4
  · exact u_cell_chaos_4 hX hx hΛ h3.le h4
  rcases le_or_gt q (12 / 25) with h5 | h5
  · exact u_cell_chaos_5 hX hx hΛ h4.le h5
  exact u_cell_chaos_6 hX hx hΛ h5.le hq2

end RMF
