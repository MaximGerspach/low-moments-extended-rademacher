/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.Steps
import RMF.Reduction.SuppliersExplicit

/-!
# The upper reduction with its constants named

The constants of `RMF.reduction_upper_of_core`, named in terms of Rankin's constants `A`, `c_R`,
`C_R` and the sieve constant `C_s` (`RMF/Reduction/SuppliersExplicit.lean`):
`C = max{1, C_R + C_R/c_R, C_s/π}`, `K = A + 1`, `c = c_R/4` and `y₀ = max{4, ⌈e^{c_R}⌉}`.
`RMF.reduction_upper_window` is stated with them.
-/

open MeasureTheory Filter Set
open scoped Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The constant `C` of `RMF.reduction_upper_of_core`, `max{1, C_R + C_R/c_R, C_s/π}`. -/
noncomputable def reductionUpperConst : ℝ :=
  max 1 (max (smoothCountConst + smoothCountConst / smoothCountDecay) (roughCountConst / π))

/-- The exponent `K` of `RMF.reduction_upper_of_core`, Rankin's `A` plus one. -/
noncomputable def reductionUpperExponent : ℝ := smoothCountExponent + 1

/-- The decay constant `c` of `RMF.reduction_upper_of_core`, a quarter of Rankin's. -/
noncomputable def reductionUpperDecay : ℝ := smoothCountDecay / 4

/-- The smallest `y` of `RMF.reduction_upper_of_core`, `max{4, ⌈e^{c_R}⌉}`. -/
noncomputable def reductionUpperStart : ℕ := max 4 ⌈Real.exp smoothCountDecay⌉₊

end RMF
