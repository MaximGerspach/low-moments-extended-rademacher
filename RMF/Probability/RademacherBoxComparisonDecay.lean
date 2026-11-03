/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherComparisonGeneric

/-!
# A third-moment bound for the box comparisons on summable windows

One numerical fact for the two-dimensional box comparisons on per-block windows: after the fourth
root, the two-fold third-moment bound `RMF.blockTAdd₂` is at most twice the one-point pair's
`2·RMF.blockTAdd` (`RMF.blockTAdd₂_rpow_le`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The numerical conditions -/

/-- **The two-fold third-moment bound, after the fourth root, is at most twice the one-point
pair's `2·RMF.blockTAdd`**: `RMF.blockThirdConstAdd₂ ≤ 32·RMF.blockThirdConstAdd` (`≈ 530`
against `≈ 154`), so `RMF.blockTAdd₂ ≤ 16·(2·RMF.blockTAdd)`, and `16^{1/4} = 2`. -/
lemma blockTAdd₂_rpow_le (θ : ℝ) (m : ℕ) :
    blockTAdd₂ θ m ^ (1 / 4 : ℝ) ≤ 2 * (2 * blockTAdd θ m) ^ (1 / 4 : ℝ) := by
  have hlogpos : (0 : ℝ) < Real.log (blockScale θ m) := by
    rw [log_blockScale]; exact Real.exp_pos _
  have hT₂0 : 0 ≤ blockTAdd₂ θ m := (blockTAdd₂_pos hlogpos).le
  have hT0 : 0 ≤ 2 * blockTAdd θ m := by have := blockTAdd_pos hlogpos; linarith
  have hc : blockThirdConstAdd₂ ≤ 32 * blockThirdConstAdd := by
    have h := absMomentConst_nonneg 3
    rw [blockThirdConstAdd₂, blockThirdConstAdd]
    nlinarith [h]
  have hle : blockTAdd₂ θ m ≤ 16 * (2 * blockTAdd θ m) := by
    have hs : (0 : ℝ) < Real.sqrt (blockScale θ m) := Real.sqrt_pos.2 (blockScale_pos θ m)
    have hl4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hX0 : (0 : ℝ) ≤ Real.exp 3 * (8 * Real.log 4
        / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m))) := by positivity
    rw [blockTAdd₂, blockTAdd]
    nlinarith [mul_le_mul_of_nonneg_right hc hX0]
  have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by rw [Real.rpow_ofNat]; norm_num,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  calc blockTAdd₂ θ m ^ (1 / 4 : ℝ) ≤ (16 * (2 * blockTAdd θ m)) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hT₂0 hle (by norm_num)
    _ = 2 * (2 * blockTAdd θ m) ^ (1 / 4 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hT0, h16]

end RMF
