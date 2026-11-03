/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ChaosFirstMoment
import RMF.NumberTheory.MertensProductExplicit
import RMF.Probability.RestrictedFirstMoment
import RMF.Probability.HarperScalesExplicit

/-!
# The chaos first moment with its constants named

The explicit level of `RMF.exists_const_integral_restrictedChaosUnitShift_le_of_le`
(`RMF/Probability/ChaosFirstMoment.lean`), Hamdan's Proposition 2.1 (Hamdan, arXiv:2604.05563) on
the unit window, as Harper's upper bound uses it: `RMF.restrictedChaosLevel E₀`.
-/

open MeasureTheory

namespace RMF

/-- The level of `RMF.exists_const_integral_restrictedChaosUnitShift_le_of_le`: that of
Proposition 5's upper half, which does not depend on `E₀`. -/
noncomputable def restrictedChaosLevel (_E₀ : ℝ) : ℝ := max prop5UpperLevel 0

end RMF
