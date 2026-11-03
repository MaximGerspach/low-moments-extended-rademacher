/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.HarperMoment
import RMF.Probability.GaussianNumerals
import RMF.Probability.RestrictedSecondMoment
import RMF.Probability.RestrictedSecondMoment.RangeNumerals
import RMF.NumberTheory.MertensProductExplicit
import RMF.NumberTheory.CosinePrimeSum
import RMF.Probability.RestrictedSecondMoment.Assembly
import RMF.Probability.RestrictedSecondMoment.Drift
import RMF.NumberTheory.StrongPNT
import RMF.PNTPlus.MediumPNTExplicit
import RMF.NumberTheory.ThetaClassicalBound
import RMF.Harper
import RMF.NumberTheory.ThetaMedium
import RMF.NumberTheory.ThetaFar
import RMF.NumberTheory.PNTThresholdExplicit
import RMF.Probability.BlockComparisonExplicit
import RMF.Probability.ChaosMoment
import RMF.Probability.ChaosFirstMomentExplicit
import RMF.Probability.MaximalBarrierExplicit
import RMF.Probability.MaximalBarrierSharp
import RMF.Probability.SharpNumerals
import RMF.Probability.HarperScalesExplicit
import RMF.Reduction.LowerReductionExplicit
import RMF.Reduction.UpperNumerals
import RMF.Reduction.LowerAssembly

/-!
# Numeral bounds on two thresholds

`RMF.blockCosineThreshold_le`: `blockCosineThreshold ≤ exp(10⁷³)`, and
`RMF.thetaMediumConst_le`: `thetaMediumConst ≤ 2.6·10¹⁰⁴`, the constant of the effective prime
number theorem past `RMF.thetaExpThreshold`; with `10 ≤ e³` and `10ⁿ ≤ e^{3n}`.  They feed the
bound on the lower reduction's window threshold in `RMF/Reduction/LowerConstNumeral.lean`.
-/

open MeasureTheory ProbabilityTheory Real

namespace RMF

/-! ### The threshold `blockCosineThreshold` -/

lemma blockCosineThreshold_le : blockCosineThreshold ≤ Real.exp (10 ^ 73) := by
  unfold blockCosineThreshold thetaExpThreshold
  have hL := mediumPNTThresholdL_le
  exact max_le (max_le (Real.exp_le_exp.2 hL) (Real.exp_le_exp.2 (by norm_num)))
    (Real.exp_le_exp.2 (by norm_num))

/-! ### The constant `thetaMediumConst` -/

lemma thetaMediumConst_le : thetaMediumConst ≤ 2.6 * 10 ^ 104 := by
  unfold thetaMediumConst
  norm_num

/-! ### Powers of ten against the exponential -/

lemma exp_three_ge_ten : (10 : ℝ) ≤ Real.exp 3 := by
  have h := pow_le_exp_nat_of_le (n := 3) (by norm_num : (0 : ℝ) ≤ 2.718) exp_one_gt_2718.le
  have h2 : (10 : ℝ) ≤ 2.718 ^ 3 := by norm_num
  push_cast at h
  linarith

lemma ten_pow_le_exp (n : ℕ) : (10 : ℝ) ^ n ≤ Real.exp (3 * n) := by
  rw [mul_comm, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) exp_three_ge_ten n

end RMF
