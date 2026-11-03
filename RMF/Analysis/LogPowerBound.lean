/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Powers of the logarithm against powers of `x`, with literal constants

`(log x)⁴ ≪ x^{9/10}` is the one analytic input of the short-interval sieve bound
`RMF.exists_roughCount_sub_le_short`.  An `IsBigO` would leave the sieve's constant and its
threshold ineffective; here everything is elementary and every constant is a literal.

The engine is Mathlib's `Real.log_le_rpow_div`: `log x ≤ x^ε/ε` for every `ε > 0`, itself just
`log t ≤ t - 1` at `t = x^ε`.  At `ε = 1/8` it gives `(log x)⁴ ≤ 8⁴·x^{1/2}` for every `x ≥ 1`,
and past `x = e^21` the leftover `x^{2/5}` absorbs the constant, because `8⁴ = 2^12` while
`x^{2/5} ≥ e^{8.4}` — so all that is needed is `log 2 ≤ 0.7`.

## Main results

* `RMF.log_pow_four_le_rpow_half`: `(log x)⁴ ≤ 4096·x^{1/2}` for `x ≥ 1`, unconditional;
* `RMF.log_pow_four_le_rpow`: `(log x)⁴ ≤ x^{9/10}` for `x ≥ e^21`;
* `RMF.rpow_mul_log_pow_three_le`: `x^{1/10}·(log x)³ ≤ x / log x` for `x ≥ e^21` — the form the
  sieve consumes, and an explicit stand-in for
  `BrunTitchmarsh.rpow_mul_rpow_log_isBigO_id_div_log 3 (1/10)`.
-/

namespace RMF

/-- **`log x ≤ 8·x^{1/8}`, hence `(log x)⁴ ≤ 4096·x^{1/2}`, for every `x ≥ 1`.**  This is
`Real.log_le_rpow_div` at `ε = 1/8`, raised to the fourth power; `x ≥ 1` is needed only so that
`log x ≥ 0` and the fourth power is monotone. -/
theorem log_pow_four_le_rpow_half {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 4 ≤ 4096 * x ^ (1 / 2 : ℝ) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hlog0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hstep : Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := by
    have h := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 8 by norm_num)
    calc Real.log x ≤ x ^ (1 / 8 : ℝ) / (1 / 8) := h
      _ = 8 * x ^ (1 / 8 : ℝ) := by ring
  have hfour : (x ^ (1 / 8 : ℝ)) ^ (4 : ℕ) = x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (x ^ (1 / 8 : ℝ)) 4, ← Real.rpow_mul hx0.le]
    norm_num
  calc Real.log x ^ 4 ≤ (8 * x ^ (1 / 8 : ℝ)) ^ (4 : ℕ) := pow_le_pow_left₀ hlog0 hstep 4
    _ = 4096 * (x ^ (1 / 8 : ℝ)) ^ (4 : ℕ) := by ring
    _ = 4096 * x ^ (1 / 2 : ℝ) := by rw [hfour]

/-- **`(log x)⁴ ≤ x^{9/10}` for `x ≥ e^21`.**  The unconditional bound leaves a factor
`4096 = 2^12`, and `x^{2/5} ≥ e^{8.4} ≥ 2^{12}` swallows it, which needs `log 2 ≤ 0.7`
(`Real.log_two_lt_d9`).  The proof of `RMF.exists_roughCount_sub_le_short` takes `H₀ = e^21`. -/
theorem log_pow_four_le_rpow {x : ℝ} (hx : Real.exp 21 ≤ x) :
    Real.log x ^ 4 ≤ x ^ (9 / 10 : ℝ) := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hlogx : (21 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 21]
    exact Real.log_le_log (Real.exp_pos 21) hx
  have hl2 : Real.log 2 ≤ 0.6932 := by linarith [Real.log_two_lt_d9]
  -- `4096 = 2^12 ≤ e^{8.4} ≤ x^{2/5}`, read off logarithms
  have habs : (4096 : ℝ) ≤ x ^ (2 / 5 : ℝ) := by
    refine (Real.log_le_log_iff (by norm_num) (Real.rpow_pos_of_pos hx0 _)).1 ?_
    have hlhs : Real.log 4096 = 12 * Real.log 2 := by
      rw [show (4096 : ℝ) = 2 ^ (12 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [hlhs, Real.log_rpow hx0]
    linarith
  have hadd : x ^ (2 / 5 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  calc Real.log x ^ 4 ≤ 4096 * x ^ (1 / 2 : ℝ) := log_pow_four_le_rpow_half hx1
    _ ≤ x ^ (2 / 5 : ℝ) * x ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right habs (Real.rpow_nonneg hx0.le _)
    _ = x ^ (9 / 10 : ℝ) := hadd

/-- **`x^{1/10}·(log x)³ ≤ x / log x` for `x ≥ e^21`.**  Multiplying through by `log x > 0` this
is `x^{1/10}·(log x)⁴ ≤ x`, which is `RMF.log_pow_four_le_rpow` together with
`x^{1/10}·x^{9/10} = x`.

This is the explicit form of `BrunTitchmarsh.rpow_mul_rpow_log_isBigO_id_div_log 3 (1/10)`, with
the implied constant equal to `1`. -/
theorem rpow_mul_log_pow_three_le {x : ℝ} (hx : Real.exp 21 ≤ x) :
    x ^ (1 / 10 : ℝ) * Real.log x ^ 3 ≤ x / Real.log x := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hlogx : (21 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 21]
    exact Real.log_le_log (Real.exp_pos 21) hx
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  rw [le_div_iff₀ hlog0, show x ^ (1 / 10 : ℝ) * Real.log x ^ 3 * Real.log x
      = x ^ (1 / 10 : ℝ) * Real.log x ^ 4 by ring]
  calc x ^ (1 / 10 : ℝ) * Real.log x ^ 4 ≤ x ^ (1 / 10 : ℝ) * x ^ (9 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left (log_pow_four_le_rpow hx) (Real.rpow_nonneg hx0.le _)
    _ = x := by rw [← Real.rpow_add hx0]; norm_num

end RMF
