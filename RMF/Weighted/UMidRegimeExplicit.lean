/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UJensenRegimeExplicit
import RMF.Weighted.UCellsMid1Explicit
import RMF.Weighted.UCellsMid2Explicit
import RMF.Weighted.UCellsMid3Explicit
import RMF.Weighted.UCellsMid4Explicit
import RMF.Weighted.UCellsMid5Explicit

/-!
# The first moment below `q = ½`: `q ∈ [0.41, 0.49]` past `x = exp(e⁷)`

`RMF.u_mid_regime` (`7 ≤ Λ ≤ 110`, from the twenty-five cells of
`RMF/Weighted/UCellsMid*Explicit.lean`, certificate totals at most `21.14`) and
`RMF.u_regime_mid_large`: with `RMF.u_large_regime`, `E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`
for every `x ≥ exp(e⁷)` and `q ∈ [0.41, 0.49]`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The middle range of (U)**: for `x ≥ exp(e⁷)` with `Λ = log log x ≤ 110` and
`q ∈ [0.41, 0.49]`, `E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (the cells
`RMF.u_cell_mid_1`, …, `_25`). -/
theorem u_mid_regime {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) (hΛu : Real.log (Real.log x) ≤ 110)
    (hq1 : 41 / 100 ≤ q) (hq2 : q ≤ 49 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨-, -, hΛ7, -, -, -⟩ := mid_params hx
  rcases le_or_gt q (43 / 100) with hq0 | hq0
  · rcases le_or_gt (Real.log (Real.log x)) 12 with hL1 | hL1
    · exact u_cell_mid_21 hX hx hΛ7 hL1 hq1 hq0
    rcases le_or_gt (Real.log (Real.log x)) 20 with hL2 | hL2
    · exact u_cell_mid_22 hX hx hL1.le hL2 hq1 hq0
    rcases le_or_gt (Real.log (Real.log x)) 35 with hL3 | hL3
    · exact u_cell_mid_23 hX hx hL2.le hL3 hq1 hq0
    rcases le_or_gt (Real.log (Real.log x)) 60 with hL4 | hL4
    · exact u_cell_mid_24 hX hx hL3.le hL4 hq1 hq0
    exact u_cell_mid_25 hX hx hL4.le hΛu hq1 hq0
  rcases le_or_gt q (9 / 20) with hqa | hqa
  · rcases le_or_gt (Real.log (Real.log x)) 12 with hL1 | hL1
    · exact u_cell_mid_1 hX hx hΛ7 hL1 hq0.le hqa
    rcases le_or_gt (Real.log (Real.log x)) 20 with hL2 | hL2
    · exact u_cell_mid_2 hX hx hL1.le hL2 hq0.le hqa
    rcases le_or_gt (Real.log (Real.log x)) 35 with hL3 | hL3
    · exact u_cell_mid_3 hX hx hL2.le hL3 hq0.le hqa
    rcases le_or_gt (Real.log (Real.log x)) 60 with hL4 | hL4
    · exact u_cell_mid_4 hX hx hL3.le hL4 hq0.le hqa
    exact u_cell_mid_5 hX hx hL4.le hΛu hq0.le hqa
  rcases le_or_gt q (47 / 100) with hqb | hqb
  · rcases le_or_gt (Real.log (Real.log x)) 12 with hL1 | hL1
    · exact u_cell_mid_6 hX hx hΛ7 hL1 hqa.le hqb
    rcases le_or_gt (Real.log (Real.log x)) 20 with hL2 | hL2
    · exact u_cell_mid_7 hX hx hL1.le hL2 hqa.le hqb
    rcases le_or_gt (Real.log (Real.log x)) 35 with hL3 | hL3
    · exact u_cell_mid_8 hX hx hL2.le hL3 hqa.le hqb
    rcases le_or_gt (Real.log (Real.log x)) 60 with hL4 | hL4
    · exact u_cell_mid_9 hX hx hL3.le hL4 hqa.le hqb
    exact u_cell_mid_10 hX hx hL4.le hΛu hqa.le hqb
  rcases le_or_gt q (12 / 25) with hqc | hqc
  · rcases le_or_gt (Real.log (Real.log x)) 12 with hL1 | hL1
    · exact u_cell_mid_11 hX hx hΛ7 hL1 hqb.le hqc
    rcases le_or_gt (Real.log (Real.log x)) 20 with hL2 | hL2
    · exact u_cell_mid_12 hX hx hL1.le hL2 hqb.le hqc
    rcases le_or_gt (Real.log (Real.log x)) 35 with hL3 | hL3
    · exact u_cell_mid_13 hX hx hL2.le hL3 hqb.le hqc
    rcases le_or_gt (Real.log (Real.log x)) 60 with hL4 | hL4
    · exact u_cell_mid_14 hX hx hL3.le hL4 hqb.le hqc
    exact u_cell_mid_15 hX hx hL4.le hΛu hqb.le hqc
  rcases le_or_gt (Real.log (Real.log x)) 12 with hL1 | hL1
  · exact u_cell_mid_16 hX hx hΛ7 hL1 hqc.le hq2
  rcases le_or_gt (Real.log (Real.log x)) 20 with hL2 | hL2
  · exact u_cell_mid_17 hX hx hL1.le hL2 hqc.le hq2
  rcases le_or_gt (Real.log (Real.log x)) 35 with hL3 | hL3
  · exact u_cell_mid_18 hX hx hL2.le hL3 hqc.le hq2
  rcases le_or_gt (Real.log (Real.log x)) 60 with hL4 | hL4
  · exact u_cell_mid_19 hX hx hL3.le hL4 hqc.le hq2
  exact u_cell_mid_20 hX hx hL4.le hΛu hqc.le hq2

/-- `x ≥ exp(e^{110})` from `log log x ≥ 110` past `exp(e⁷)`. -/
lemma exp_exp_le_of_loglog {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x)
    (hΛ : 110 ≤ Real.log (Real.log x)) : Real.exp (Real.exp 110) ≤ x := by
  obtain ⟨hx0, hL, -, -, -, -⟩ := mid_params hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have h1 : Real.exp 110 ≤ Real.log x := (Real.le_log_iff_exp_le hLpos).1 hΛ
  exact (Real.le_log_iff_exp_le hx0).1 h1

/-- **(U) for `q ∈ [0.41, 0.49]` past `x = exp(e⁷)`**: `E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`,
by the middle range up to `Λ = 110` (`RMF.u_mid_regime`) and `RMF.u_large_regime` beyond. -/
theorem u_regime_mid_large {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) (hq1 : 41 / 100 ≤ q) (hq2 : q ≤ 49 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  rcases le_or_gt (Real.log (Real.log x)) 110 with h | h
  · exact u_mid_regime hX hx h hq1 hq2
  · exact u_large_regime hX (exp_exp_le_of_loglog hx h.le) hq1 hq2

end RMF
