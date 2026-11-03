/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.BlockComparisonExplicit
import RMF.Probability.SharpNumerals
import Mathlib.NumberTheory.ZetaValues

/-!
# Elementary numerals

Numerical bounds on `e`: `2.718 < e < 2.719`, `e^n ≤ b^n` for `b ≥ e` and `b^n ≤ e^n` for
`0 ≤ b ≤ e`, and `e² ≤ 8`.
-/

open MeasureTheory ProbabilityTheory
open scoped Real

namespace RMF

/-! ### Elementary numerals -/

lemma exp_one_gt_2718 : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9

lemma exp_one_lt_2719 : Real.exp 1 < 2.719 := lt_trans Real.exp_one_lt_d9 (by norm_num)

lemma exp_nat_le_pow_of_le {n : ℕ} {b : ℝ} (hb : Real.exp 1 ≤ b) :
    Real.exp (n : ℝ) ≤ b ^ n := by
  rw [show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le hb n

lemma pow_le_exp_nat_of_le {n : ℕ} {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ Real.exp 1) :
    b ^ n ≤ Real.exp (n : ℝ) := by
  rw [show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ hb0 hb n

lemma exp_two_le_eight : Real.exp 2 ≤ 8 := by
  have h := exp_nat_le_pow_of_le (n := 2) exp_one_lt_2719.le
  norm_num at h ⊢
  linarith

end RMF
