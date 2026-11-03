/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Truncated powers

`x₊ ^ n`, the classical spline building block: `x ^ n` for `x ≥ 0` and `0` for `x ≤ 0`.  It is
exactly `C^(n-1)`, and differentiating lowers the exponent by one *globally*, including at the
kink.

## Why this file exists

The Lindeberg replacement argument needs a `C³` approximation to the indicator of an interval,
built from the degree-`7` smoothstep extended by `0` and `1` outside `[0,1]`.  Establishing that
the extension is `C³` by a piecewise definition is painful: Mathlib's `ContMDiff.piecewise` wants
the two branches to agree on a *neighbourhood* of the seam, which is false here — they agree at
one point — and there is no `ContDiff` analogue at all.

Truncated powers avoid the seam entirely.  The extended smoothstep is a fixed linear combination
of `truncPow k x` and `truncPow k (x - 1)` for `4 ≤ k ≤ 7`, so its regularity and all of its
derivatives follow from ordinary calculus applied to this one family, with no gluing anywhere.

## The exponent convention

`RMF.truncPow (n + 2)` is differentiable and `RMF.truncPow (n + 1)` is `Cⁿ`; both offsets are
sharp.  `truncPow 1 x = max x 0` is continuous but *not* differentiable at `0`, so the derivative
lemma cannot be stated for `truncPow (n + 1)` — a natural-looking statement that is false at
`n = 0`.
-/

namespace RMF

/-- The truncated power `x ↦ (max x 0) ^ n`, written `x₊ ^ n` in the spline literature. -/
noncomputable def truncPow (n : ℕ) (x : ℝ) : ℝ := max x 0 ^ n

@[simp]
lemma truncPow_zero (x : ℝ) : truncPow 0 x = 1 := pow_zero _

/-- On the positive half-line a truncated power is the honest power. -/
lemma truncPow_of_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : truncPow n x = x ^ n := by
  rw [truncPow, max_eq_left hx]

/-- A truncated power of positive exponent vanishes on the negative half-line. -/
lemma truncPow_of_nonpos {x : ℝ} (hx : x ≤ 0) {n : ℕ} (hn : n ≠ 0) : truncPow n x = 0 := by
  rw [truncPow, max_eq_right hx, zero_pow hn]

lemma truncPow_nonneg (n : ℕ) (x : ℝ) : 0 ≤ truncPow n x := pow_nonneg (le_max_right x 0) n

/-- A truncated power is dominated by the corresponding power of the absolute value.  This is
what makes the kink a zero of order `n`. -/
lemma truncPow_le_abs_pow (n : ℕ) (x : ℝ) : truncPow n x ≤ |x| ^ n :=
  pow_le_pow_left₀ (le_max_right x 0) (max_le (le_abs_self x) (abs_nonneg x)) n

lemma continuous_truncPow (n : ℕ) : Continuous (truncPow n) :=
  (continuous_id.max continuous_const).pow n

/-- **Differentiating a truncated power lowers the exponent**, at every point including the
kink.  The exponent `n + 2` is sharp: `truncPow 1 = max · 0` is not differentiable at `0`. -/
lemma hasDerivAt_truncPow (n : ℕ) (x : ℝ) :
    HasDerivAt (truncPow (n + 2)) ((n + 2 : ℝ) * truncPow (n + 1) x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hev : truncPow (n + 2) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      exact truncPow_of_nonpos hy.le (by omega)
    rw [truncPow_of_nonpos hx.le (by omega), mul_zero]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  · rw [truncPow_of_nonpos le_rfl (by omega), mul_zero, hasDerivAt_iff_tendsto_slope]
    have hbound : ∀ y : ℝ, ‖slope (truncPow (n + 2)) 0 y‖ ≤ |y| ^ (n + 1) := by
      intro y
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      · rw [slope_def_field, truncPow_of_nonpos le_rfl (by omega), sub_zero, sub_zero,
          Real.norm_eq_abs, abs_div]
        rw [div_le_iff₀ (abs_pos.2 hy)]
        calc |truncPow (n + 2) y| = truncPow (n + 2) y := abs_of_nonneg (truncPow_nonneg _ _)
          _ ≤ |y| ^ (n + 2) := truncPow_le_abs_pow _ _
          _ = |y| ^ (n + 1) * |y| := by ring
    refine squeeze_zero_norm (fun y => hbound y) ?_
    have : Filter.Tendsto (fun y : ℝ => |y| ^ (n + 1)) (nhds 0) (nhds 0) := by
      have hc : Continuous fun y : ℝ => |y| ^ (n + 1) := (continuous_abs.pow _)
      simpa using hc.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  · have hev : truncPow (n + 2) =ᶠ[nhds x] fun y => y ^ (n + 2) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact truncPow_of_nonneg hy.le _
    rw [truncPow_of_nonneg hx.le]
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    simpa using hasDerivAt_pow (n + 2) x

lemma differentiable_truncPow (n : ℕ) : Differentiable ℝ (truncPow (n + 2)) :=
  fun x => (hasDerivAt_truncPow n x).differentiableAt

/-- The derivative in closed form, valid on all of `ℝ`. -/
lemma deriv_truncPow (n : ℕ) :
    deriv (truncPow (n + 2)) = fun x => (n + 2 : ℝ) * truncPow (n + 1) x :=
  funext fun x => (hasDerivAt_truncPow n x).deriv

/-- **`x₊ ^ (n+1)` is `Cⁿ`.**  The one induction the smoothstep development rests on; everything
else is assembled from it by ring operations and composition with affine maps. -/
lemma contDiff_truncPow (n : ℕ) : ContDiff ℝ n (truncPow (n + 1)) := by
  induction n with
  | zero => simpa [contDiff_zero] using continuous_truncPow 1
  | succ n ih =>
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; ring
      rw [hcast, contDiff_succ_iff_deriv]
      refine ⟨differentiable_truncPow n, by simp, ?_⟩
      rw [deriv_truncPow n]
      have hconst : ContDiff ℝ (n : WithTop ℕ∞) (fun _ : ℝ => (n : ℝ) + 2) := contDiff_const
      exact ContDiff.mul hconst ih

end RMF
