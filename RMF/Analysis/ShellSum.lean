/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A partial sum of `k^{-1/2}`

`∑_{k=1}^{m} k^{-1/2} ≤ 2√m` (`RMF.sum_one_div_sqrt_le`), by induction on `m`: the step is
`1/√(m+1) ≤ 2√(m+1) - 2√m`.
-/

open scoped Real

namespace RMF

section ShellSum

/-- `∑_{k=1}^{m} k^{-1/2} ≤ 2√m`. -/
lemma sum_one_div_sqrt_le (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, 1 / Real.sqrt k ≤ 2 * Real.sqrt m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    set s : ℝ := Real.sqrt m with hsdef
    set t : ℝ := Real.sqrt ((m : ℝ) + 1) with htdef
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have ht0 : 0 < t := Real.sqrt_pos.2 (by positivity)
    have hs2 : s ^ 2 = (m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg m)
    have ht2 : t ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hstep : 1 / t ≤ 2 * t - 2 * s := by
      rw [div_le_iff₀ ht0]
      nlinarith [sq_nonneg (t - s)]
    rw [hcast]
    linarith

end ShellSum

end RMF
