/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.HarperScales
import RMF.Probability.BlockShift
import RMF.Probability.BlockComparisonSharp

/-!
# Harper's scales with their constants named

The explicit twin of `RMF.exists_harperThreshold_of_blockCount`, at the threshold
`RMF.harperThreshold D n₀ = exp(exp(D + n₀))`, and the block offset
`RMF.freeStartHarperD E₀ = ⌈prop5UpperThreshold E₀⌉₊ + 1` at which the averaged free start is read
at Harper's scales (`RMF.freeStart_barrier_harper_le_averaged_steinhaus`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

/-- **The threshold on `x`** for a block offset `D` and a block count `n₀`: `exp(exp(D + n₀))`. -/
noncomputable def harperThreshold (D n₀ : ℕ) : ℝ := Real.exp (Real.exp ((D : ℝ) + (n₀ : ℝ)))

/-- **`RMF.exists_harperThreshold_of_blockCount` at its threshold**
`RMF.harperThreshold D n₀ = exp(exp(D + n₀))`. -/
theorem exists_harperThreshold_of_blockCount_explicit (D n₀ : ℕ) :
    ∀ x : ℝ, (harperThreshold D n₀) ≤ x →
      1 < x ∧ (D : ℝ) ≤ Real.log (Real.log x) ∧ n₀ ≤ harperBlockCount D x := by
  rw [show harperThreshold D n₀ = Real.exp (Real.exp ((D : ℝ) + (n₀ : ℝ))) from rfl]
  refine fun x hx => ?_
  have hn₀0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg n₀
  have hinner : (0 : ℝ) < Real.exp ((D : ℝ) + (n₀ : ℝ)) := Real.exp_pos _
  have hx1 : 1 < x := by
    have hone : (1 : ℝ) < Real.exp (Real.exp ((D : ℝ) + (n₀ : ℝ))) := by
      linarith [Real.add_one_le_exp (Real.exp ((D : ℝ) + (n₀ : ℝ)))]
    linarith
  -- `log x ≥ e^{D+n₀}`, then `log log x ≥ D + n₀`
  have hlx : Real.exp ((D : ℝ) + (n₀ : ℝ)) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos (Real.exp ((D : ℝ) + (n₀ : ℝ)))) hx
    rwa [Real.log_exp] at this
  have hllx : (D : ℝ) + (n₀ : ℝ) ≤ Real.log (Real.log x) := by
    have := Real.log_le_log hinner hlx
    rwa [Real.log_exp] at this
  have hDlog : (D : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hfloor : D + n₀ ≤ ⌊Real.log (Real.log x)⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    linarith
  have hcount : n₀ ≤ harperBlockCount D x := by
    rw [harperBlockCount]
    omega
  exact ⟨hx1, hDlog, hcount⟩

/-- `RMF.harperThreshold D n` is monotone in the block count `n`. -/
lemma harperThreshold_mono (D : ℕ) {n m : ℕ} (h : n ≤ m) :
    harperThreshold D n ≤ harperThreshold D m := by
  unfold harperThreshold
  have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
  exact Real.exp_le_exp.2 (Real.exp_le_exp.2 (by linarith))

/-- `RMF.harperThreshold D n ≥ 2`. -/
lemma two_le_harperThreshold (D n : ℕ) : 2 ≤ harperThreshold D n := by
  unfold harperThreshold
  have h0 : (0 : ℝ) ≤ (D : ℝ) + (n : ℝ) := by positivity
  linarith [Real.add_one_le_exp ((D : ℝ) + (n : ℝ)),
    Real.add_one_le_exp (Real.exp ((D : ℝ) + (n : ℝ)))]

/-- The block offset of the averaged free start at Harper's scales
(`RMF.freeStart_barrier_harper_le_averaged_steinhaus`), `⌈prop5UpperThreshold E₀⌉₊ + 1`: Harper's
offset `ϑ ≥ D - 1` is then past the threshold, and `D ≥ 17` since the threshold is at least `16`. -/
noncomputable def freeStartHarperD (E₀ : ℝ) : ℕ := ⌈prop5UpperThreshold E₀⌉₊ + 1

end RMF
