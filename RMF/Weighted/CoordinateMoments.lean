/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.CoordinateModel
import RMF.Weighted.Defs

/-!
# The weighted moments on the coordinate model

`E|∑_{n ≤ x} f(n)/√n|^r`, for `f` the extension over the squarefree integers of iid values at the
primes, is the same on every probability space as on the coordinate model
(`RMF.IsIIDPrimeValues.integral_comp_primeExtend`).  This makes the constants of the weighted
theorems independent of the probability space (`RMF.weighted_rademacher_moments`,
`RMF.exists_integral_rpow_norm_weightedRademacherSum_le_sharp`).
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`E|∑_{n ≤ x} f(n)/√n|^r` is the coordinate model's**, for `f` the extension of iid values at
the primes over the squarefree integers. -/
theorem IsIIDPrimeValues.integral_rpow_weightedRademacherSum_squarefreeExtension_eq
    {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (x r : ℝ) :
    ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ r ∂μ
      = ∫ v, ‖weightedRademacherSum (fun v => squarefreeExtension (primeExtend v)) x v‖ ^ r
          ∂(Measure.infinitePi fun _ : Nat.Primes => ν) := by
  have hm : Measurable fun v : Nat.Primes → ℂ =>
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, squarefreeExtension (primeExtend v) n / (Real.sqrt n : ℂ)‖ ^ r :=
    (Finset.measurable_sum _ fun n _ =>
      (measurable_squarefreeExtension_primeExtend n).div_const (Real.sqrt n : ℂ)).norm.pow_const r
  exact hX.integral_comp_primeExtend
    (Ψ := fun g => ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, squarefreeExtension g n / (Real.sqrt n : ℂ)‖ ^ r)
    (fun h => congrArg
      (fun F : ArithmeticFunction ℂ => ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F n / (Real.sqrt n : ℂ)‖ ^ r)
      (squarefreeExtension_congr_primes h))
    hm.aestronglyMeasurable

end RMF
