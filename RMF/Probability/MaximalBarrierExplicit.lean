/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.MaximalBarrier
import RMF.Probability.Chaining
import RMF.EulerProduct.JointLaplaceExplicit
import RMF.NumberTheory.CosinePrimeSumExplicit

/-!
# The maximal barrier bound with its constants named

The constants of the two prime sums at the block scales of
`RMF/Probability/MaximalBarrier.lean`, as Harper's upper bound uses them:
`RMF.blockScaleSumConst = primesBelowInvLogLogConst + log 4 + log 2 + 5` for the sums up to `x_j`,
and `RMF.blockRangeSumConst = 2·blockScaleSumConst` for the sums over `x_0 < p ≤ x_j`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-- The constant of `RMF.exists_const_sum_primesBelow_blockScale_le`. -/
noncomputable def blockScaleSumConst : ℝ := primesBelowInvLogLogConst + Real.log 4 + Real.log 2 + 5

/-- The constant of `RMF.exists_const_sum_primesIco_blockScale_le`. -/
noncomputable def blockRangeSumConst : ℝ := 2 * blockScaleSumConst

end RMF
