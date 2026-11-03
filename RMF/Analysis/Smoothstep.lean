/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import RMF.Analysis.TruncPow

/-!
# The degree-`7` smoothstep

`S x = 35 x ^ 4 - 84 x ^ 5 + 70 x ^ 6 - 20 x ^ 7` on `[0,1]`, extended by `0` below and `1` above:
the unique polynomial with `S 0 = 0`, `S 1 = 1` and `S' = S'' = S''' = 0` at both endpoints, so
that the extension is `C³`.

This is the profile of the smoothed indicator that a Lindeberg replacement argument needs.
Mathlib's two candidates are both unusable: `ContDiffBump` carries no derivative bound of any
kind — its own docstring names that as future work — and `Real.smoothTransition` has an essential
singularity at the ends, so its derivatives grow without bound in the order.  Here everything is
polynomial, and the derivative bounds are `nlinarith` certificates.

## Defined by its truncated-power expansion

`RMF.smoothstep` is *defined* as

`35 x₊⁴ - 84 x₊⁵ + 70 x₊⁶ - 20 x₊⁷ + 35 (x-1)₊⁴ + 84 (x-1)₊⁵ + 70 (x-1)₊⁶ + 20 (x-1)₊⁷`,

not by a three-way `if`.  The first group is the Taylor polynomial of `S` at `0`, the second is
minus the Taylor polynomial of `S - 1` at `1`; both start at order `4` because that is where the
interpolation conditions stop.  Defining it this way makes `RMF.contDiff_smoothstep` immediate
from `RMF.contDiff_truncPow`, with no gluing argument anywhere, and turns the three region
formulas into `ring` identities.

`S 1 = 1` is `35 - 84 + 70 - 20 = 1`, and the `x ≥ 1` branch is the polynomial identity
`S (1 + t) = 1 - (35 t⁴ + 84 t⁵ + 70 t⁶ + 20 t⁷)`.

## The reflection

`RMF.smoothstep_add_smoothstep_one_sub` says `S x + S (1 - x) = 1` for *every* real `x`, not just
on `[0,1]`.  It is what makes the upper bound `S ≤ 1` follow from the lower bound `0 ≤ S` with no
second calculation, and it is the symmetry the two-sided window is built on.
-/

namespace RMF

/-- The degree-`7` smoothstep: `0` below `0`, `1` above `1`, and the unique interpolant matching
value and first three derivatives at both endpoints in between.  Given by its truncated-power
expansion, so that smoothness needs no gluing. -/
noncomputable def smoothstep (x : ℝ) : ℝ :=
  35 * truncPow 4 x - 84 * truncPow 5 x + 70 * truncPow 6 x - 20 * truncPow 7 x
    + 35 * truncPow 4 (x - 1) + 84 * truncPow 5 (x - 1) + 70 * truncPow 6 (x - 1)
    + 20 * truncPow 7 (x - 1)

/-- **The smoothstep is `C³`.**  Every summand is a truncated power of exponent at least `4`,
hence `C³` by `RMF.contDiff_truncPow`, composed with a translation. -/
lemma contDiff_smoothstep : ContDiff ℝ 3 smoothstep := by
  have key : ∀ n : ℕ, ContDiff ℝ 3 (truncPow (n + 4)) := by
    intro n
    refine (contDiff_truncPow (n + 3)).of_le ?_
    exact_mod_cast (by omega : (3 : ℕ) ≤ n + 3)
  have shift : ∀ n : ℕ, ContDiff ℝ 3 fun x : ℝ => truncPow (n + 4) (x - 1) := fun n =>
    (key n).comp (contDiff_id.sub contDiff_const)
  have h4 := key 0
  have h5 := key 1
  have h6 := key 2
  have h7 := key 3
  have s4 := shift 0
  have s5 := shift 1
  have s6 := shift 2
  have s7 := shift 3
  norm_num at h4 h5 h6 h7 s4 s5 s6 s7
  exact ((((((((contDiff_const.mul h4).sub (contDiff_const.mul h5)).add
    (contDiff_const.mul h6)).sub (contDiff_const.mul h7)).add
    (contDiff_const.mul s4)).add (contDiff_const.mul s5)).add
    (contDiff_const.mul s6)).add (contDiff_const.mul s7))

/-! ### The three regions -/

/-- The smoothstep vanishes below `0`. -/
lemma smoothstep_of_nonpos {x : ℝ} (hx : x ≤ 0) : smoothstep x = 0 := by
  have h1 : x - 1 ≤ 0 := by linarith
  have h : ∀ n : ℕ, n ≠ 0 → truncPow n x = 0 := fun n hn => truncPow_of_nonpos hx hn
  have h' : ∀ n : ℕ, n ≠ 0 → truncPow n (x - 1) = 0 := fun n hn => truncPow_of_nonpos h1 hn
  rw [smoothstep, h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num),
    h' 4 (by norm_num), h' 5 (by norm_num), h' 6 (by norm_num), h' 7 (by norm_num)]
  ring

/-- On the transition interval the smoothstep is its defining polynomial. -/
lemma smoothstep_of_mem_Icc {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    smoothstep x = 35 * x ^ 4 - 84 * x ^ 5 + 70 * x ^ 6 - 20 * x ^ 7 := by
  have hx1 : x - 1 ≤ 0 := by linarith
  have h' : ∀ n : ℕ, n ≠ 0 → truncPow n (x - 1) = 0 := fun n hn => truncPow_of_nonpos hx1 hn
  rw [smoothstep, truncPow_of_nonneg h0 4, truncPow_of_nonneg h0 5, truncPow_of_nonneg h0 6,
    truncPow_of_nonneg h0 7, h' 4 (by norm_num), h' 5 (by norm_num), h' 6 (by norm_num),
    h' 7 (by norm_num)]
  ring

/-- The smoothstep is `1` above `1`.  The content is the polynomial identity
`S (1 + t) = 1 - (35 t⁴ + 84 t⁵ + 70 t⁶ + 20 t⁷)`. -/
lemma smoothstep_of_one_le {x : ℝ} (hx : 1 ≤ x) : smoothstep x = 1 := by
  have h0 : (0 : ℝ) ≤ x := by linarith
  have h1 : (0 : ℝ) ≤ x - 1 := by linarith
  rw [smoothstep, truncPow_of_nonneg h0 4, truncPow_of_nonneg h0 5, truncPow_of_nonneg h0 6,
    truncPow_of_nonneg h0 7, truncPow_of_nonneg h1 4, truncPow_of_nonneg h1 5,
    truncPow_of_nonneg h1 6, truncPow_of_nonneg h1 7]
  ring

@[simp] lemma smoothstep_zero : smoothstep 0 = 0 := smoothstep_of_nonpos le_rfl

@[simp] lemma smoothstep_one : smoothstep 1 = 1 := smoothstep_of_one_le le_rfl

/-! ### The reflection, and the bounds it gives -/

/-- **The smoothstep is symmetric about `(1/2, 1/2)`**, on all of `ℝ`. -/
lemma smoothstep_add_smoothstep_one_sub (x : ℝ) : smoothstep x + smoothstep (1 - x) = 1 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [smoothstep_of_nonpos hx, smoothstep_of_one_le (by linarith), zero_add]
  · rcases le_or_gt x 1 with hx1 | hx1
    · rw [smoothstep_of_mem_Icc hx.le hx1,
        smoothstep_of_mem_Icc (by linarith) (by linarith)]
      ring
    · rw [smoothstep_of_one_le hx1.le, smoothstep_of_nonpos (by linarith), add_zero]

/-- The smoothstep is nonnegative.  On the transition interval this is
`x⁴ (35 - 84x + 70x² - 20x³) ≥ 0`, the second factor decreasing from `35` to `1`. -/
lemma smoothstep_nonneg (x : ℝ) : 0 ≤ smoothstep x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [smoothstep_of_nonpos hx]
  · rcases le_or_gt x 1 with hx1 | hx1
    · rw [smoothstep_of_mem_Icc hx.le hx1]
      nlinarith [pow_nonneg hx.le 4, sq_nonneg (x - 1), sq_nonneg x, hx.le, hx1,
        mul_nonneg (pow_nonneg hx.le 4) (sub_nonneg.2 hx1)]
    · rw [smoothstep_of_one_le hx1.le]
      norm_num

/-- The smoothstep never exceeds `1`, by reflection. -/
lemma smoothstep_le_one (x : ℝ) : smoothstep x ≤ 1 := by
  have h := smoothstep_add_smoothstep_one_sub x
  have h' := smoothstep_nonneg (1 - x)
  linarith

/-! ### The derivative

`S' = 140 x₊³ (1-x)₊³`, and the truncated-power form of that is what differentiating the
definition gives directly — one application of `RMF.hasDerivAt_truncPow` per summand, with the
shifted ones composed with `x ↦ x - 1`.  Outside `[0,1]` one of the two truncated factors
vanishes, which is exactly the statement that the extension is `C¹`. -/

/-- **The derivative of the smoothstep**, in the same truncated-power form as the definition. -/
lemma hasDerivAt_smoothstep (x : ℝ) :
    HasDerivAt smoothstep
      (140 * truncPow 3 x - 420 * truncPow 4 x + 420 * truncPow 5 x - 140 * truncPow 6 x
        + 140 * truncPow 3 (x - 1) + 420 * truncPow 4 (x - 1) + 420 * truncPow 5 (x - 1)
        + 140 * truncPow 6 (x - 1)) x := by
  have hshift : HasDerivAt (fun y : ℝ => y - 1) 1 x := (hasDerivAt_id x).sub_const 1
  have sh : ∀ n : ℕ, HasDerivAt (fun y : ℝ => truncPow (n + 2) (y - 1))
      (((n : ℝ) + 2) * truncPow (n + 1) (x - 1) * 1) x := fun n => by
    simpa [Function.comp_def] using HasDerivAt.comp x (hasDerivAt_truncPow n (x - 1)) hshift
  have h4 := (hasDerivAt_truncPow 2 x).const_mul (35 : ℝ)
  have h5 := (hasDerivAt_truncPow 3 x).const_mul (84 : ℝ)
  have h6 := (hasDerivAt_truncPow 4 x).const_mul (70 : ℝ)
  have h7 := (hasDerivAt_truncPow 5 x).const_mul (20 : ℝ)
  have s4 := (sh 2).const_mul (35 : ℝ)
  have s5 := (sh 3).const_mul (84 : ℝ)
  have s6 := (sh 4).const_mul (70 : ℝ)
  have s7 := (sh 5).const_mul (20 : ℝ)
  have hall := HasDerivAt.add (HasDerivAt.add (HasDerivAt.add (HasDerivAt.add
    (HasDerivAt.sub (HasDerivAt.add (HasDerivAt.sub h4 h5) h6) h7) s4) s5) s6) s7
  refine hall.congr_deriv ?_
  norm_num
  ring

lemma deriv_smoothstep (x : ℝ) :
    deriv smoothstep x
      = 140 * truncPow 3 x - 420 * truncPow 4 x + 420 * truncPow 5 x - 140 * truncPow 6 x
        + 140 * truncPow 3 (x - 1) + 420 * truncPow 4 (x - 1) + 420 * truncPow 5 (x - 1)
        + 140 * truncPow 6 (x - 1) :=
  (hasDerivAt_smoothstep x).deriv

/-- On the transition interval the derivative is `140 x³ (1-x)³`. -/
lemma deriv_smoothstep_of_mem_Icc {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    deriv smoothstep x = 140 * (x * (1 - x)) ^ 3 := by
  have hx1 : x - 1 ≤ 0 := by linarith
  have hq : ∀ n : ℕ, n ≠ 0 → truncPow n (x - 1) = 0 := fun n hn => truncPow_of_nonpos hx1 hn
  rw [deriv_smoothstep, truncPow_of_nonneg h0 3, truncPow_of_nonneg h0 4,
    truncPow_of_nonneg h0 5, truncPow_of_nonneg h0 6, hq 3 (by norm_num), hq 4 (by norm_num),
    hq 5 (by norm_num), hq 6 (by norm_num)]
  ring

/-- The derivative vanishes below `0`. -/
lemma deriv_smoothstep_of_nonpos {x : ℝ} (hx : x ≤ 0) : deriv smoothstep x = 0 := by
  have h1 : x - 1 ≤ 0 := by linarith
  have hp : ∀ n : ℕ, n ≠ 0 → truncPow n x = 0 := fun n hn => truncPow_of_nonpos hx hn
  have hq : ∀ n : ℕ, n ≠ 0 → truncPow n (x - 1) = 0 := fun n hn => truncPow_of_nonpos h1 hn
  rw [deriv_smoothstep, hp 3 (by norm_num), hp 4 (by norm_num), hp 5 (by norm_num),
    hp 6 (by norm_num), hq 3 (by norm_num), hq 4 (by norm_num), hq 5 (by norm_num),
    hq 6 (by norm_num)]
  ring

/-- The derivative vanishes above `1`; the smoothstep is constant there. -/
lemma deriv_smoothstep_of_one_le {x : ℝ} (hx : 1 ≤ x) : deriv smoothstep x = 0 := by
  have h0 : (0 : ℝ) ≤ x := by linarith
  have h1 : (0 : ℝ) ≤ x - 1 := by linarith
  rw [deriv_smoothstep, truncPow_of_nonneg h0 3, truncPow_of_nonneg h0 4,
    truncPow_of_nonneg h0 5, truncPow_of_nonneg h0 6, truncPow_of_nonneg h1 3,
    truncPow_of_nonneg h1 4, truncPow_of_nonneg h1 5, truncPow_of_nonneg h1 6]
  ring

/-- **The bound on the first derivative**, `‖S′‖ ≤ 35/16`.  On the transition interval
`S′ = 140 u³` with `u = x(1-x) ≤ 1/4`, and `140/64 = 35/16`. -/
lemma abs_deriv_smoothstep_le (x : ℝ) : |deriv smoothstep x| ≤ 35 / 16 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [deriv_smoothstep_of_nonpos hx]
    norm_num
  · rcases le_or_gt x 1 with hx1 | hx1
    · rw [deriv_smoothstep_of_mem_Icc hx.le hx1]
      have hu0 : 0 ≤ x * (1 - x) := mul_nonneg hx.le (by linarith)
      have hu4 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
      have hcube : (x * (1 - x)) ^ 3 ≤ (1 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hu0 hu4 3
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    · rw [deriv_smoothstep_of_one_le hx1.le]
      norm_num

/-! ### The second and third derivatives

Same pattern: differentiate the truncated-power form again.  On `[0,1]`, with `u = x(1-x)`,

`S′′ = 420 u² (1 - 2x)`  and  `S′′′ = 840 u (1 - 5u)`,

and outside `[0,1]` both vanish.  The bound on `S′′′` is the one Lindeberg consumes; the sharp value
is `105/2`, attained at `x = 1/2` where `S′′′ = -105/2`.  Note that the maximum is at an *endpoint*
of the range of `u`: the interior critical point `u = 1/10` gives only `42`. -/

/-- The second derivative, in truncated-power form. -/
lemma hasDerivAt_deriv_smoothstep (x : ℝ) :
    HasDerivAt (deriv smoothstep)
      (420 * truncPow 2 x - 1680 * truncPow 3 x + 2100 * truncPow 4 x - 840 * truncPow 5 x
        + 420 * truncPow 2 (x - 1) + 1680 * truncPow 3 (x - 1) + 2100 * truncPow 4 (x - 1)
        + 840 * truncPow 5 (x - 1)) x := by
  rw [funext deriv_smoothstep]
  have hshift : HasDerivAt (fun y : ℝ => y - 1) 1 x := (hasDerivAt_id x).sub_const 1
  have sh : ∀ n : ℕ, HasDerivAt (fun y : ℝ => truncPow (n + 2) (y - 1))
      (((n : ℝ) + 2) * truncPow (n + 1) (x - 1) * 1) x := fun n => by
    simpa [Function.comp_def] using HasDerivAt.comp x (hasDerivAt_truncPow n (x - 1)) hshift
  have h3 := (hasDerivAt_truncPow 1 x).const_mul (140 : ℝ)
  have h4 := (hasDerivAt_truncPow 2 x).const_mul (420 : ℝ)
  have h5 := (hasDerivAt_truncPow 3 x).const_mul (420 : ℝ)
  have h6 := (hasDerivAt_truncPow 4 x).const_mul (140 : ℝ)
  have s3 := (sh 1).const_mul (140 : ℝ)
  have s4 := (sh 2).const_mul (420 : ℝ)
  have s5 := (sh 3).const_mul (420 : ℝ)
  have s6 := (sh 4).const_mul (140 : ℝ)
  have hall := ((((((h3.sub h4).add h5).sub h6).add s3).add s4).add s5).add s6
  refine hall.congr_deriv ?_
  norm_num
  ring

lemma deriv2_smoothstep (x : ℝ) :
    deriv (deriv smoothstep) x
      = 420 * truncPow 2 x - 1680 * truncPow 3 x + 2100 * truncPow 4 x - 840 * truncPow 5 x
        + 420 * truncPow 2 (x - 1) + 1680 * truncPow 3 (x - 1) + 2100 * truncPow 4 (x - 1)
        + 840 * truncPow 5 (x - 1) :=
  (hasDerivAt_deriv_smoothstep x).deriv

/-- The third derivative, in truncated-power form. -/
lemma hasDerivAt_deriv2_smoothstep (x : ℝ) :
    HasDerivAt (deriv (deriv smoothstep))
      (840 * truncPow 1 x - 5040 * truncPow 2 x + 8400 * truncPow 3 x - 4200 * truncPow 4 x
        + 840 * truncPow 1 (x - 1) + 5040 * truncPow 2 (x - 1) + 8400 * truncPow 3 (x - 1)
        + 4200 * truncPow 4 (x - 1)) x := by
  rw [funext deriv2_smoothstep]
  have hshift : HasDerivAt (fun y : ℝ => y - 1) 1 x := (hasDerivAt_id x).sub_const 1
  have sh : ∀ n : ℕ, HasDerivAt (fun y : ℝ => truncPow (n + 2) (y - 1))
      (((n : ℝ) + 2) * truncPow (n + 1) (x - 1) * 1) x := fun n => by
    simpa [Function.comp_def] using HasDerivAt.comp x (hasDerivAt_truncPow n (x - 1)) hshift
  have h2 := (hasDerivAt_truncPow 0 x).const_mul (420 : ℝ)
  have h3 := (hasDerivAt_truncPow 1 x).const_mul (1680 : ℝ)
  have h4 := (hasDerivAt_truncPow 2 x).const_mul (2100 : ℝ)
  have h5 := (hasDerivAt_truncPow 3 x).const_mul (840 : ℝ)
  have s2 := (sh 0).const_mul (420 : ℝ)
  have s3 := (sh 1).const_mul (1680 : ℝ)
  have s4 := (sh 2).const_mul (2100 : ℝ)
  have s5 := (sh 3).const_mul (840 : ℝ)
  have hall := ((((((h2.sub h3).add h4).sub h5).add s2).add s3).add s4).add s5
  refine hall.congr_deriv ?_
  norm_num
  ring

lemma deriv3_smoothstep (x : ℝ) :
    deriv (deriv (deriv smoothstep)) x
      = 840 * truncPow 1 x - 5040 * truncPow 2 x + 8400 * truncPow 3 x - 4200 * truncPow 4 x
        + 840 * truncPow 1 (x - 1) + 5040 * truncPow 2 (x - 1) + 8400 * truncPow 3 (x - 1)
        + 4200 * truncPow 4 (x - 1) :=
  (hasDerivAt_deriv2_smoothstep x).deriv

/-! ### Region values and the sup bounds -/

/-- `S′′ = 420 u² (1 - 2x)` with `u = x(1-x)`, on the transition interval. -/
lemma deriv2_smoothstep_of_mem_Icc {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    deriv (deriv smoothstep) x = 420 * (x * (1 - x)) ^ 2 * (1 - 2 * x) := by
  have hx1 : x - 1 ≤ 0 := by linarith
  have hq : ∀ n : ℕ, n ≠ 0 → truncPow n (x - 1) = 0 := fun n hn => truncPow_of_nonpos hx1 hn
  rw [deriv2_smoothstep, truncPow_of_nonneg h0 2, truncPow_of_nonneg h0 3,
    truncPow_of_nonneg h0 4, truncPow_of_nonneg h0 5, hq 2 (by norm_num), hq 3 (by norm_num),
    hq 4 (by norm_num), hq 5 (by norm_num)]
  ring

lemma deriv2_smoothstep_of_nonpos {x : ℝ} (hx : x ≤ 0) : deriv (deriv smoothstep) x = 0 := by
  have h1 : x - 1 ≤ 0 := by linarith
  have hp : ∀ n : ℕ, n ≠ 0 → truncPow n x = 0 := fun n hn => truncPow_of_nonpos hx hn
  have hq : ∀ n : ℕ, n ≠ 0 → truncPow n (x - 1) = 0 := fun n hn => truncPow_of_nonpos h1 hn
  rw [deriv2_smoothstep, hp 2 (by norm_num), hp 3 (by norm_num), hp 4 (by norm_num),
    hp 5 (by norm_num), hq 2 (by norm_num), hq 3 (by norm_num), hq 4 (by norm_num),
    hq 5 (by norm_num)]
  ring

lemma deriv2_smoothstep_of_one_le {x : ℝ} (hx : 1 ≤ x) : deriv (deriv smoothstep) x = 0 := by
  have h0 : (0 : ℝ) ≤ x := by linarith
  have h1 : (0 : ℝ) ≤ x - 1 := by linarith
  rw [deriv2_smoothstep, truncPow_of_nonneg h0 2, truncPow_of_nonneg h0 3,
    truncPow_of_nonneg h0 4, truncPow_of_nonneg h0 5, truncPow_of_nonneg h1 2,
    truncPow_of_nonneg h1 3, truncPow_of_nonneg h1 4, truncPow_of_nonneg h1 5]
  ring

/-- `‖S′′‖ ≤ 105/4`.  Crude: `|1 - 2x| ≤ 1` and `u ≤ 1/4` give `420/16`.  The sharp value is
`84√5/25 = 7.513…`, attained at `u = 1/5`. -/
lemma abs_deriv2_smoothstep_le (x : ℝ) : |deriv (deriv smoothstep) x| ≤ 105 / 4 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [deriv2_smoothstep_of_nonpos hx]; norm_num
  · rcases le_or_gt x 1 with hx1 | hx1
    · rw [deriv2_smoothstep_of_mem_Icc hx.le hx1]
      have hu0 : 0 ≤ x * (1 - x) := mul_nonneg hx.le (by linarith)
      have hu4 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
      have hsq : (x * (1 - x)) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ hu0 hu4 2
      have habs : |1 - 2 * x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      rw [abs_mul, abs_of_nonneg (by positivity)]
      nlinarith [abs_nonneg (1 - 2 * x)]
    · rw [deriv2_smoothstep_of_one_le hx1.le]; norm_num

/-- `S′′′ = 840 u (1 - 5u)` with `u = x(1-x)`, on the transition interval. -/
lemma deriv3_smoothstep_of_mem_Icc {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    deriv (deriv (deriv smoothstep)) x
      = 840 * (x * (1 - x)) * (1 - 5 * (x * (1 - x))) := by
  have hx1 : x - 1 ≤ 0 := by linarith
  have hq : ∀ n : ℕ, n ≠ 0 → truncPow n (x - 1) = 0 := fun n hn => truncPow_of_nonpos hx1 hn
  rw [deriv3_smoothstep, truncPow_of_nonneg h0 1, truncPow_of_nonneg h0 2,
    truncPow_of_nonneg h0 3, truncPow_of_nonneg h0 4, hq 1 (by norm_num), hq 2 (by norm_num),
    hq 3 (by norm_num), hq 4 (by norm_num)]
  ring

lemma deriv3_smoothstep_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv (deriv (deriv smoothstep)) x = 0 := by
  have h1 : x - 1 ≤ 0 := by linarith
  have hp : ∀ n : ℕ, n ≠ 0 → truncPow n x = 0 := fun n hn => truncPow_of_nonpos hx hn
  have hq : ∀ n : ℕ, n ≠ 0 → truncPow n (x - 1) = 0 := fun n hn => truncPow_of_nonpos h1 hn
  rw [deriv3_smoothstep, hp 1 (by norm_num), hp 2 (by norm_num), hp 3 (by norm_num),
    hp 4 (by norm_num), hq 1 (by norm_num), hq 2 (by norm_num), hq 3 (by norm_num),
    hq 4 (by norm_num)]
  ring

lemma deriv3_smoothstep_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv (deriv (deriv smoothstep)) x = 0 := by
  have h0 : (0 : ℝ) ≤ x := by linarith
  have h1 : (0 : ℝ) ≤ x - 1 := by linarith
  rw [deriv3_smoothstep, truncPow_of_nonneg h0 1, truncPow_of_nonneg h0 2,
    truncPow_of_nonneg h0 3, truncPow_of_nonneg h0 4, truncPow_of_nonneg h1 1,
    truncPow_of_nonneg h1 2, truncPow_of_nonneg h1 3, truncPow_of_nonneg h1 4]
  ring

/-- **The bound on the third derivative**, `‖S′′′‖ ≤ 105/2`.  Both directions have exact
certificates: above, `42 - 840u + 4200u² = 4200 (u - 1/10)²`; below,
`840u - 4200u² + 105/2 = 4200 (1/4 - u)(u + 1/20)`.  This is the bound a Lindeberg replacement
argument consumes. -/
lemma abs_deriv3_smoothstep_le (x : ℝ) : |deriv (deriv (deriv smoothstep)) x| ≤ 105 / 2 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [deriv3_smoothstep_of_nonpos hx]; norm_num
  · rcases le_or_gt x 1 with hx1 | hx1
    · rw [deriv3_smoothstep_of_mem_Icc hx.le hx1, abs_le]
      have hu0 : 0 ≤ x * (1 - x) := mul_nonneg hx.le (by linarith)
      have hu4 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.2 hu4) (by linarith : (0 : ℝ) ≤ x * (1 - x) + 1 / 20)]
      · nlinarith [sq_nonneg (x * (1 - x) - 1 / 10)]
    · rw [deriv3_smoothstep_of_one_le hx1.le]; norm_num

end RMF
