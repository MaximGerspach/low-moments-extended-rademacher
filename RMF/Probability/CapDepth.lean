/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.FloorDepth

/-!
# The linear ballot, from below on an interval

`RMF.le_ballotLinear_of_mem`: for `0 ≤ b_L ≤ c ≤ b_U` with `b_U² ≤ 2nv₋`, the linear ballot
`RMF.ballotLinear c` is at least `2b_L(1 - b_U²/(2nv₋))/√(2πnv₊)`, uniformly in `c`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

namespace RMF

/-- **`RMF.ballotLinear` from below on an interval**: for `0 ≤ b_L ≤ c ≤ b_U` with
`b_U² ≤ 2nv₋`, `2b_L(1 - b_U²/(2nv₋))/√(2πnv₊) ≤ ballotLinear c`. -/
lemma le_ballotLinear_of_mem {vmin vmax : ℝ} (hvmin : 0 < vmin) {n : ℕ} (hn : 1 ≤ n)
    {c bL bU : ℝ} (hbL : 0 ≤ bL) (hL : bL ≤ c) (hU : c ≤ bU)
    (hb : bU ^ 2 ≤ 2 * ((n : ℝ) * vmin)) :
    2 * bL * (1 - bU ^ 2 / (2 * ((n : ℝ) * vmin))) / √(2 * π * ((n : ℝ) * vmax))
      ≤ ballotLinear vmin vmax n c := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnv : 0 < 2 * ((n : ℝ) * vmin) := by positivity
  have hc0 : 0 ≤ c := le_trans hbL hL
  have h1 : 0 ≤ 1 - bU ^ 2 / (2 * ((n : ℝ) * vmin)) := by
    rw [sub_nonneg, div_le_one hnv]
    exact hb
  have hsq : c ^ 2 ≤ bU ^ 2 := pow_le_pow_left₀ hc0 hU 2
  have h2 : 1 - bU ^ 2 / (2 * ((n : ℝ) * vmin)) ≤ 1 - c ^ 2 / (2 * ((n : ℝ) * vmin)) := by
    have := div_le_div_of_nonneg_right hsq hnv.le
    linarith
  have h3 : 2 * bL * (1 - bU ^ 2 / (2 * ((n : ℝ) * vmin)))
      ≤ 2 * c * (1 - c ^ 2 / (2 * ((n : ℝ) * vmin))) :=
    mul_le_mul (by linarith) h2 h1 (mul_nonneg (by norm_num) hc0)
  unfold ballotLinear
  rw [max_eq_left hc0]
  exact div_le_div_of_nonneg_right h3 (Real.sqrt_nonneg _)

end RMF
