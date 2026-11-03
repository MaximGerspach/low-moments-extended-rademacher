/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Order.Lattice
import RMF.Probability.GaussianEstimates
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The second moment of a centred Gaussian

`∫ z² ∂N(0,V) = V` (`RMF.integral_sq_gaussianReal_eq`), read off Mathlib's variance of
`gaussianReal`.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `∫ z² ∂N(0,V) = V`, from Mathlib's variance computation. -/
lemma integral_sq_gaussianReal_eq (V : ℝ≥0) :
    ∫ z, z ^ 2 ∂(gaussianReal 0 V) = (V : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := V)
  rw [variance_eq_integral (measurable_id'.aemeasurable)] at h
  simpa using h

end RMF
