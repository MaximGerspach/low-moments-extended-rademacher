/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.LowerBlockNumeral

/-!
# The lower reduction's window threshold, bounded by a numeral

`RMF.windowThreshold_le`: the threshold `RMF.windowThreshold` of the lower reduction's mean-square
leg is at most `exp(e^{1621})`.  It rests on `RMF.pntAllConst_le`, `pntAllConst ≤ 10¹⁴⁷`, from
`thetaMediumConst ≤ 2.6·10¹⁰⁴` and `log thetaExpThreshold ≤ 10⁷³`.
-/

open MeasureTheory ProbabilityTheory Real

namespace RMF

/-! ### The prime number theorem's constant and the window threshold -/

lemma four_le_exp_two : (4 : ℝ) ≤ Real.exp 2 := by
  have h := pow_le_exp_nat_of_le (n := 2) (by norm_num : (0 : ℝ) ≤ 2.718) exp_one_gt_2718.le
  have h2 : (4 : ℝ) ≤ 2.718 ^ 2 := by norm_num
  push_cast at h
  linarith

lemma thetaExpThreshold_log_le : Real.log thetaExpThreshold ≤ 10 ^ 73 := by
  have hT : thetaExpThreshold ≤ Real.exp (10 ^ 73) :=
    le_trans (le_max_left _ _) blockCosineThreshold_le
  have hT0 : 0 < thetaExpThreshold := lt_of_lt_of_le (Real.exp_pos 100) (le_max_right _ _)
  exact (Real.log_le_iff_le_exp hT0).2 hT

lemma pntAllConst_le : pntAllConst ≤ 10 ^ 147 := by
  unfold pntAllConst
  have hC := thetaMediumConst_le
  have hL := thetaExpThreshold_log_le
  have hL0 : 0 ≤ Real.log thetaExpThreshold := by
    have h : Real.exp 100 ≤ thetaExpThreshold := le_max_right _ _
    have := (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 100) h)).2 h
    linarith
  have hl4 : Real.log 4 ≤ 1.4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
    linarith [Real.log_two_lt_d9]
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsq : Real.log thetaExpThreshold ^ 2 ≤ (10 ^ 73) ^ 2 := pow_le_pow_left₀ hL0 hL 2
  refine max_le (le_trans hC (by norm_num)) ?_
  calc Real.log 4 * Real.log thetaExpThreshold ^ 2 ≤ 1.4 * (10 ^ 73) ^ 2 :=
        mul_le_mul hl4 hsq (by positivity) (by norm_num)
    _ ≤ 10 ^ 147 := by norm_num

lemma windowThreshold_le : windowThreshold ≤ Real.exp (Real.exp 1621) := by
  unfold windowThreshold
  have hp := pntAllConst_le
  have h150 : (10 ^ 150 : ℝ) ≤ Real.exp 1621 :=
    le_trans (ten_pow_le_exp 150) (Real.exp_le_exp.2 (by norm_num))
  refine max_le (Real.exp_le_exp.2 (by linarith)) ?_
  exact le_trans four_le_exp_two (Real.exp_le_exp.2 (by linarith))

end RMF
