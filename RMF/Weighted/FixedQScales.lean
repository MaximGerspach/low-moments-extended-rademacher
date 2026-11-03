/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.FixedQ

/-!
# The scales of the fixed-`q` upper bound

The upper bound for fixed `½ < q < 1` takes `y_k = x^{e^{-(k-1)}}` for `1 ≤ k ≤ K` with
`K = ⌈2(1-q) log log x⌉ + 1`, so that `y_1 = x` and `log y_K ≍ (log x)^{2q-1}`.

Here they are the **integers** `Y k = ⌊x^{e^{1-k}}⌋₊`, and that is not a cosmetic difference: the
floor is what forces the block tail bound to be stated at `log z ≤ Λ·log y` rather than at
`z = y^e` (see `RMF.exists_integral_normSq_blockTruncationTail_le`).  This file collects what the
layers satisfy.

## The one quantity everything is measured against

Write `u k = e^{1-k}·log x`, the logarithm of the *unfloored* scale.  Then

* `log (Y k) ≤ u k`, always (for `x ≥ 1`);
* `log (Y k) ≥ u k − log 2`, as soon as `u k ≥ log 2` — because `⌊t⌋₊ > t − 1 ≥ t/2` for `t ≥ 2`.

So the floor costs `log 2` per layer, once, and every estimate below is `u k` up to that.  In
particular `log (Y k) ≤ 2e·log (Y (k+1))` needs `u (k+1) ≥ log 4`, which is why `log 4` rather
than `log 2` is the threshold carried throughout.

`u` is decreasing in `k`, so all of these follow from the single condition `log 4 ≤ u K` at the
bottom layer — and `u K ≥ e^{-1}(log x)^{2q-1}`, so that condition is a lower bound on `x` alone.
-/

open Finset MeasureTheory

namespace RMF

/-- `Y k = ⌊x^{e^{1-k}}⌋₊`, the `k`-th layer.  At `k = 1` this is `⌊x⌋₊`. -/
noncomputable def fixedQScale (x : ℝ) (k : ℕ) : ℕ := ⌊x ^ Real.exp (1 - (k : ℝ))⌋₊

/-- `u k = e^{1-k}·log x`, the logarithm of the unfloored `k`-th scale. -/
noncomputable def fixedQLogScale (x : ℝ) (k : ℕ) : ℝ := Real.exp (1 - (k : ℝ)) * Real.log x

/-- `K = ⌈2(1-q)·log log x⌉₊ + 1`, the number of layers. -/
noncomputable def fixedQLayers (q x : ℝ) : ℕ := ⌈2 * (1 - q) * Real.log (Real.log x)⌉₊ + 1

/-! ### The unfloored scales -/

/-- `u (k+1) = e^{-1}·u k`, which is the whole point of the scales. -/
lemma fixedQLogScale_succ (x : ℝ) (k : ℕ) :
    fixedQLogScale x k = Real.exp 1 * fixedQLogScale x (k + 1) := by
  rw [fixedQLogScale, fixedQLogScale, ← mul_assoc, ← Real.exp_add]
  push_cast
  ring_nf

/-! ### The floored scales -/

@[simp]
lemma fixedQScale_one (x : ℝ) : fixedQScale x 1 = ⌊x⌋₊ := by
  rw [fixedQScale]
  norm_num

/-- The unfloored scale is at least `1`, for `x ≥ 1`. -/
lemma one_le_rpow_exp {x : ℝ} (hx : 1 ≤ x) (k : ℕ) :
    (1 : ℝ) ≤ x ^ Real.exp (1 - (k : ℝ)) := by
  have h := Real.rpow_le_rpow_of_exponent_le hx (le_of_lt (Real.exp_pos (1 - (k : ℝ))))
  rwa [Real.rpow_zero] at h

/-- The layers are nonincreasing, for `x ≥ 1`. -/
lemma fixedQScale_antitone {x : ℝ} (hx : 1 ≤ x) (k : ℕ) :
    fixedQScale x (k + 1) ≤ fixedQScale x k := by
  refine Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hx (Real.exp_le_exp.2 ?_))
  push_cast
  linarith

/-- The layers lie below `x`, for `x ≥ 1` and `k ≥ 1`. -/
lemma fixedQScale_le {x : ℝ} (hx : 1 ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    (fixedQScale x k : ℝ) ≤ x := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hexp : Real.exp (1 - (k : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  refine le_trans (Nat.floor_le (by positivity)) ?_
  calc x ^ Real.exp (1 - (k : ℝ)) ≤ x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx hexp
    _ = x := Real.rpow_one x

/-- `log (Y k) ≤ u k`. -/
lemma log_fixedQScale_le {x : ℝ} (hx : 1 ≤ x) (k : ℕ) :
    Real.log (fixedQScale x k) ≤ fixedQLogScale x k := by
  have h1 : (1 : ℝ) ≤ x ^ Real.exp (1 - (k : ℝ)) := one_le_rpow_exp hx k
  have hfl : 1 ≤ fixedQScale x k := Nat.one_le_floor_iff _ |>.2 h1
  have hflR : (1 : ℝ) ≤ (fixedQScale x k : ℝ) := by exact_mod_cast hfl
  have hle : (fixedQScale x k : ℝ) ≤ x ^ Real.exp (1 - (k : ℝ)) :=
    Nat.floor_le (by linarith)
  rw [fixedQLogScale, ← Real.log_rpow (by linarith : (0 : ℝ) < x)]
  exact Real.log_le_log (by linarith) hle

/-- **The floor costs `log 2`, once.**  `log (Y k) ≥ u k − log 2`, as soon as `u k ≥ log 2`. -/
lemma le_log_fixedQScale {x : ℝ} (hx : 1 ≤ x) {k : ℕ} (hu : Real.log 2 ≤ fixedQLogScale x k) :
    fixedQLogScale x k - Real.log 2 ≤ Real.log (fixedQScale x k) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : Real.log (x ^ Real.exp (1 - (k : ℝ))) = fixedQLogScale x k := Real.log_rpow hx0 _
  have h2 : (2 : ℝ) ≤ x ^ Real.exp (1 - (k : ℝ)) := by
    have := Real.exp_le_exp.2 hu
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2), ← hlog,
      Real.exp_log (by positivity : (0 : ℝ) < x ^ Real.exp (1 - (k : ℝ)))] at this
  have hhalf : x ^ Real.exp (1 - (k : ℝ)) / 2 ≤ (fixedQScale x k : ℝ) := by
    have hfl := Nat.lt_floor_add_one (x ^ Real.exp (1 - (k : ℝ)))
    have : x ^ Real.exp (1 - (k : ℝ)) - 1 ≤ (fixedQScale x k : ℝ) := by
      rw [fixedQScale]; linarith
    linarith
  have hpos : (0 : ℝ) < x ^ Real.exp (1 - (k : ℝ)) / 2 := by linarith
  have := Real.log_le_log hpos hhalf
  rwa [Real.log_div (by linarith) (by norm_num), hlog] at this

/-- `2 ≤ Y k`, as soon as `u k ≥ log 4`. -/
lemma two_le_fixedQScale {x : ℝ} (hx : 1 ≤ x) {k : ℕ}
    (hu : Real.log 4 ≤ fixedQLogScale x k) : 2 ≤ fixedQScale x k := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : Real.log (x ^ Real.exp (1 - (k : ℝ))) = fixedQLogScale x k := Real.log_rpow hx0 _
  have h4 : (4 : ℝ) ≤ x ^ Real.exp (1 - (k : ℝ)) := by
    have := Real.exp_le_exp.2 hu
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 4), ← hlog,
      Real.exp_log (by positivity : (0 : ℝ) < x ^ Real.exp (1 - (k : ℝ)))] at this
  have hcast : ((2 : ℕ) : ℝ) ≤ x ^ Real.exp (1 - (k : ℝ)) := by
    push_cast
    linarith
  exact Nat.le_floor hcast

/-- **The layer ratio, at `Λ = 2e`.**  `log (Y k) ≤ 2e·log (Y (k+1))`, as soon as
`u (k+1) ≥ log 4`.  This is the hypothesis of the block tail bound, and `2e` rather than `e` is
exactly the price of the two floors: `log Y k ≤ u k = e·u (k+1)` while
`log Y (k+1) ≥ u (k+1) − log 2`, and `e·u ≤ 2e·(u − log 2)` precisely when
`u ≥ 2 log 2 = log 4`. -/
lemma log_fixedQScale_le_two_mul_exp_mul {x : ℝ} (hx : 1 ≤ x) {k : ℕ}
    (hu : Real.log 4 ≤ fixedQLogScale x (k + 1)) :
    Real.log (fixedQScale x k) ≤ 2 * Real.exp 1 * Real.log (fixedQScale x (k + 1)) := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlow := le_log_fixedQScale hx (k := k + 1) (by rw [hlog4] at hu; linarith)
  have hup := log_fixedQScale_le hx k
  have hstep := fixedQLogScale_succ x k
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hu2 : 2 * Real.log 2 ≤ fixedQLogScale x (k + 1) := by rw [hlog4] at hu; linarith
  nlinarith [he, hu2, hlow, hup, hstep]

/-! ### The bottom layer

`u K` is where the whole choice of `K` is felt: it is `(log x)^{2q-1}` up to a factor `e`, and
that is what makes the last term of the structural inequality the same size as the first. -/

/-- The bottom layer's unfloored logarithm is at most `(log x)^{2q-1}`.

`K = ⌈a⌉₊ + 1` with `a = 2(1-q)·log log x`, so `u K = e^{-⌈a⌉₊}·log x ≤ e^{-a}·log x`, and
`e^{-a} = (log x)^{-2(1-q)}`. -/
lemma fixedQLogScale_layers_le {q x : ℝ} (hq : q ≤ 1) (hx : Real.exp 1 ≤ x) :
    fixedQLogScale x (fixedQLayers q x) ≤ (Real.log x) ^ (2 * q - 1) := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hx
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at this
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hb : (0 : ℝ) ≤ 2 * (1 - q) := by linarith
  have ha : (0 : ℝ) ≤ 2 * (1 - q) * Real.log (Real.log x) :=
    mul_nonneg hb (Real.log_nonneg hL1)
  have hcast : (1 : ℝ) - (fixedQLayers q x : ℕ)
      = -(⌈2 * (1 - q) * Real.log (Real.log x)⌉₊ : ℕ) := by
    rw [fixedQLayers]
    push_cast
    ring
  have hceil : 2 * (1 - q) * Real.log (Real.log x)
      ≤ (⌈2 * (1 - q) * Real.log (Real.log x)⌉₊ : ℕ) := Nat.le_ceil _
  have hexp : Real.exp (-(⌈2 * (1 - q) * Real.log (Real.log x)⌉₊ : ℕ))
      ≤ (Real.log x) ^ (-(2 * (1 - q))) := by
    rw [Real.rpow_def_of_pos hL0]
    exact Real.exp_le_exp.2 (by nlinarith [hceil])
  have hmul : (Real.log x) ^ (-(2 * (1 - q))) * Real.log x = (Real.log x) ^ (2 * q - 1) := by
    nth_rewrite 2 [show Real.log x = (Real.log x) ^ (1 : ℝ) from (Real.rpow_one _).symm]
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  calc fixedQLogScale x (fixedQLayers q x)
      = Real.exp (-(⌈2 * (1 - q) * Real.log (Real.log x)⌉₊ : ℕ)) * Real.log x := by
        rw [fixedQLogScale, hcast]
    _ ≤ (Real.log x) ^ (-(2 * (1 - q))) * Real.log x :=
        mul_le_mul_of_nonneg_right hexp hL0.le
    _ = (Real.log x) ^ (2 * q - 1) := hmul

/-! ### Capping the depth

At `q` close to `½` the layer count `⌈2(1-q) log log x⌉₊ + 1` runs past the point where the scales
are still meaningful: `u K ≍ (log x)^{2q-1} → 1`, so `Y K` drops below `2` and the estimates have
nothing to stand on.

`fixedQCap x` is the last layer whose unfloored logarithm is still `≥ log 4`, and capping the
depth there costs nothing: where the cap binds, `u K < e·log 4` is bounded, so the bottom tail is
`O(1)` and the target `(log x)^{(2q-1)/2}` is at least `1`.  The cap depends on `x` alone, and
`fixedQCap x ≥ 1` needs only `x ≥ 4`. -/

/-- `fixedQCap x`, the deepest layer with `u k ≥ log 4`: `⌊1 + log(log x / log 4)⌋₊`. -/
noncomputable def fixedQCap (x : ℝ) : ℕ := ⌊1 + Real.log (Real.log x / Real.log 4)⌋₊

/-- The cap is at least the first layer, for `x ≥ 4`. -/
lemma one_le_fixedQCap {x : ℝ} (hx : 4 ≤ x) : 1 ≤ fixedQCap x := by
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hL : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  refine Nat.one_le_floor_iff _ |>.2 ?_
  have : (0 : ℝ) ≤ Real.log (Real.log x / Real.log 4) :=
    Real.log_nonneg ((one_le_div hlog4).2 hL)
  linarith

/-- **Every layer at or above the cap clears the threshold.**  `log 4 ≤ u k` for `k ≤ fixedQCap x`
— which is what the tail bounds need at every layer, through `RMF.two_le_fixedQScale` and
`RMF.log_fixedQScale_le_two_mul_exp_mul`. -/
lemma log_four_le_fixedQLogScale_of_le_cap {x : ℝ} (hx : 4 ≤ x) {k : ℕ} (hk : k ≤ fixedQCap x) :
    Real.log 4 ≤ fixedQLogScale x k := by
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hLx : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hdiv : (0 : ℝ) < Real.log 4 / Real.log x := div_pos hlog4 hL0
  have hcap : (k : ℝ) ≤ 1 + Real.log (Real.log x / Real.log 4) := by
    have h1 : (k : ℝ) ≤ (fixedQCap x : ℝ) := by exact_mod_cast hk
    have h2 : ((fixedQCap x : ℕ) : ℝ) ≤ 1 + Real.log (Real.log x / Real.log 4) := by
      rw [fixedQCap]
      refine Nat.floor_le ?_
      have : (0 : ℝ) ≤ Real.log (Real.log x / Real.log 4) :=
        Real.log_nonneg ((one_le_div hlog4).2 hLx)
      linarith
    linarith
  have hneg : Real.log (Real.log 4 / Real.log x) ≤ 1 - (k : ℝ) := by
    rw [Real.log_div (ne_of_gt hlog4) (ne_of_gt hL0),
      Real.log_div (ne_of_gt hL0) (ne_of_gt hlog4)] at *
    linarith
  have hexp := Real.exp_le_exp.2 hneg
  rw [Real.exp_log hdiv] at hexp
  rw [fixedQLogScale]
  calc Real.log 4 = Real.log 4 / Real.log x * Real.log x := by field_simp
    _ ≤ Real.exp (1 - (k : ℝ)) * Real.log x := mul_le_mul_of_nonneg_right hexp hL0.le

/-- **The cap is not deeper than it needs to be.**  `u (fixedQCap x) < e·log 4`: the next layer
already fails the threshold, and consecutive layers differ by exactly `e`.  So where the cap binds
the bottom layer is `O(1)`, which is all the upper bound asks of it there. -/
lemma fixedQLogScale_cap_le {x : ℝ} (hx : 4 ≤ x) :
    fixedQLogScale x (fixedQCap x) ≤ Real.exp 1 * Real.log 4 := by
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hLx : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hfl := Nat.lt_floor_add_one (1 + Real.log (Real.log x / Real.log 4))
  have hgt : Real.log (Real.log x / Real.log 4) < (fixedQCap x : ℝ) := by
    rw [fixedQCap]
    linarith
  have hexp := Real.exp_lt_exp.2 (neg_lt_neg hgt)
  have hval : Real.exp (-Real.log (Real.log x / Real.log 4)) = (Real.log x / Real.log 4)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (div_pos hL0 hlog4)]
  rw [hval] at hexp
  have hnext : fixedQLogScale x (fixedQCap x + 1) ≤ Real.log 4 := by
    rw [fixedQLogScale]
    have hcast : (1 : ℝ) - ((fixedQCap x + 1 : ℕ) : ℝ) = -(fixedQCap x : ℝ) := by
      push_cast; ring
    rw [hcast]
    have hmul := mul_le_mul_of_nonneg_right hexp.le hL0.le
    calc Real.exp (-(fixedQCap x : ℝ)) * Real.log x
        ≤ (Real.log x / Real.log 4)⁻¹ * Real.log x := hmul
      _ = Real.log 4 := by field_simp
  rw [fixedQLogScale_succ x (fixedQCap x)]
  exact mul_le_mul_of_nonneg_left hnext (Real.exp_pos 1).le

/-- **The layer count is at most `log log x + 2`.**  `K = ⌈2(1-q) log log x⌉₊ + 1` and
`2(1-q) ≤ 1` for `q ≥ ½`; this is the factor the uniform-in-`q` bound pays for summing the layers
trivially rather than geometrically. -/
lemma fixedQLayers_le {q x : ℝ} (hq : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hx : Real.exp 1 ≤ x) :
    ((fixedQLayers q x : ℕ) : ℝ) ≤ Real.log (Real.log x) + 2 := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hx
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at this
  have hll : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hL1
  have ha : (0 : ℝ) ≤ 2 * (1 - q) * Real.log (Real.log x) := by nlinarith
  have hceil := Nat.ceil_lt_add_one ha
  have hle : 2 * (1 - q) * Real.log (Real.log x) ≤ Real.log (Real.log x) := by nlinarith
  rw [fixedQLayers]
  push_cast
  linarith

end RMF
