/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.BlockComparisonPair
import RMF.Probability.BlockComparisonSharp

/-!
# The `ε`-windows of the two-point comparison

The windows `ε_w/(m+1)²` in place of `1/(m+1)²`.  Lemma 4 widens both tubes by the window sum, so
the windows `1/(m+1)²` cost the two-point bound a level shift of `2`, and these cost `2ε_w`:
`RMF.sum_mul_blockWindow_le` bounds their sum by `2ε_w` from any restart `k`, the slack at which
`RMF/Probability/HarperChainSlack.lean` states Lemma 4.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The `ε`-windows sum to at most `2ε_w`**, from any restart `k`.  This is the slack at which
Lemma 4 is applied (`RMF.measure_barrierEventPair_le_slack`). -/
lemma sum_mul_blockWindow_le {εw : ℝ} (hεw : 0 ≤ εw) (k j : ℕ) :
    ∑ m ∈ Finset.range j, εw * blockWindow (m + k) ≤ 2 * εw := by
  have h := sum_inv_sq_range_le_two (k + j)
  rw [sum_range_add_shift] at h
  have h0 : (0 : ℝ) ≤ ∑ m ∈ Finset.range k, (1 : ℝ) / ((m : ℝ) + 1) ^ 2 :=
    Finset.sum_nonneg fun m _ => by positivity
  have hsh : ∑ m ∈ Finset.range j, blockWindow (m + k) ≤ 2 := by
    simp only [blockWindow]
    linarith
  rw [← Finset.mul_sum]
  calc εw * ∑ m ∈ Finset.range j, blockWindow (m + k) ≤ εw * 2 :=
        mul_le_mul_of_nonneg_left hsh hεw
    _ = 2 * εw := by ring

end RMF
