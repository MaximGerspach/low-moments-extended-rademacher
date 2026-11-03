/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.SmoothSums
import RMF.NumberTheory.MertensExplicit

/-!
# The Euler product `∏_{p ≤ y}(1 + 1/p)` with a literal constant

`RMF.exists_sum_smoothSquarefree_inv_le` (`RMF/Weighted/SmoothSums.lean`) bounds
`∑_{P(m) ≤ y, m sqfree} 1/m = ∏_{p ≤ y}(1 + 1/p)` by `C·log y`, with `C` unspecified.  This file
proves `∏_{p ≤ y}(1 + 1/p) ≤ 1.195·log y` for `y ≥ e^99` (`RMF.prod_one_add_inv_primesBelow_le`),
and the same with the threshold left free (`RMF.prod_one_add_inv_primesBelow_le_exp`).

## The constant

The true size of the product is `(6e^γ/π²)·log y ≈ 1.0828·log y`, the floor for the constant.
Its logarithm is `∑_{p ≤ y} 1/p` minus `∑_{p ≤ y} (1/p − log(1+1/p))`:

1. **Mertens' second theorem**, `RMF.sum_primesBelow_inv_le`:
   `∑_{p<y} 1/p ≤ log log y + 0.2641 + 9.003/log y`, whose error is `≤ 0.0910` at `log y ≥ 99`.
2. **The head of `K = ∑_p (1/p − log(1+1/p)) ≈ 0.18198`**: `RMF.sum_head_inv_sub_log_one_add_ge`
   recovers `0.1792` from the primes below `48`, `p = 2, 3, 5` off Mathlib's decimal bounds for
   `log 2, log 3, log 5` and `7 ≤ p < 48` off the cubic Taylor bound `RMF.log_one_add_le_cubic`.

So `1.195 ≥ 1.0002·e^{0.2641 − 0.1792 + 0.0910}`, `1.0002` being the passage from `log (y+1)` to
`log y`.
-/

open Finset

namespace RMF

/-! ### Two elementary bounds -/

/-- **The cubic Taylor bound for `log (1 + u)`**, with Mathlib's remainder:
`log (1+u) ≤ u - u²/2 + u³/3 + u⁴/(1-u)` for `0 < u < 1`.

`Real.abs_log_sub_add_sum_range_le` at `x = -u` and `n = 3`.  The true remainder after the cubic
term is `≤ 0`; the `u⁴/(1-u)` here is what Mathlib's crude two-sided estimate leaves, and at
`u ≤ 1/7` it costs `< 0.0005`, which is all this file needs. -/
theorem log_one_add_le_cubic {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Real.log (1 + u) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 + u ^ 4 / (1 - u) := by
  have habs : |(-u)| = u := by rw [abs_neg, abs_of_pos hu0]
  have hlt : |(-u)| < 1 := by rw [habs]; exact hu1
  have key := Real.abs_log_sub_add_sum_range_le hlt 3
  rw [habs, show (1 : ℝ) - -u = 1 + u by ring] at key
  have hup := (abs_le.mp key).2
  norm_num [Finset.sum_range_succ] at hup
  linarith

/-- Every term of `K = ∑_p (1/p - log (1 + 1/p))` is nonnegative, since `log (1+u) ≤ u`.
Stated for every natural `p`, including `0` and `1`, so that it can be fed to
`Finset.sum_le_sum_of_subset_of_nonneg` without a primality side condition. -/
theorem inv_sub_log_one_add_nonneg (p : ℕ) : 0 ≤ (p : ℝ)⁻¹ - Real.log (1 + (p : ℝ)⁻¹) := by
  have h : Real.log (1 + (p : ℝ)⁻¹) ≤ 1 + (p : ℝ)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  linarith

/-- `RMF.log_one_add_le_cubic` at `u = 1/p`, packaged so that a single `norm_num` discharges the
arithmetic at a fixed prime: `1/p - log (1 + 1/p) ≥ 1/(2p²) - 1/(3p³) - 1/(p³(p-1))`. -/
theorem inv_sub_log_one_add_ge (p : ℕ) (hp : 2 ≤ p) (c : ℝ)
    (hc : c ≤ (p : ℝ)⁻¹ ^ 2 / 2 - (p : ℝ)⁻¹ ^ 3 / 3 - (p : ℝ)⁻¹ ^ 4 / (1 - (p : ℝ)⁻¹)) :
    c ≤ (p : ℝ)⁻¹ - Real.log (1 + (p : ℝ)⁻¹) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hu0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by linarith)
  have hu1 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hp2
  linarith [log_one_add_le_cubic hu0 (by linarith : (p : ℝ)⁻¹ < 1)]

/-- `e^{0.17584} ≤ 1.1947`, from `exp t = (exp (t/8))⁸` and Mathlib's
`Real.exp_bound_div_one_sub_of_interval`, `exp s ≤ (1-s)⁻¹`.  The true value is `1.19225`;
splitting `t` into eighths keeps the overhead of the `(1-s)⁻¹` bound down to `e^{t²/16} ≈ 1.002`. -/
theorem exp_mertens_residue_le : Real.exp (0.17584 : ℝ) ≤ 1.1947 := by
  have hb : Real.exp (0.17584 / 8) ≤ 1 / (1 - 0.17584 / 8) :=
    Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
  have h8 : Real.exp (0.17584 : ℝ) = Real.exp (0.17584 / 8) ^ 8 := by
    rw [← Real.exp_nsmul]
    norm_num
  rw [h8]
  calc Real.exp (0.17584 / 8) ^ 8 ≤ (1 / (1 - 0.17584 / 8)) ^ 8 := by gcongr
    _ ≤ 1.1947 := by norm_num

/-! ### The head of `K = ∑_p (1/p - log (1 + 1/p))` -/

/-- **The primes below `48` already carry `0.1792` of `K = ∑_p (1/p - log(1+1/p))`.**  The true
value of `K` is `0.181982 = M - log (6e^γ/π²)`, and of the partial sum `0.180057`.

`p = 2, 3, 5` are exact, off Mathlib's `Real.log_two_lt_d9` and friends; the remaining twelve use
the cubic Taylor bound `RMF.inv_sub_log_one_add_ge`, good to five decimal places at `p ≥ 7`. -/
theorem sum_head_inv_sub_log_one_add_ge :
    (0.1792 : ℝ) ≤ ∑ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ),
      ((p : ℝ)⁻¹ - Real.log (1 + (p : ℝ)⁻¹)) := by
  have h2 : (0.0945348 : ℝ) ≤ ((2 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((2 : ℕ) : ℝ)⁻¹) := by
    rw [show (1 : ℝ) + ((2 : ℕ) : ℝ)⁻¹ = 3 / 2 by norm_num,
      Real.log_div (by norm_num) (by norm_num), show ((2 : ℕ) : ℝ)⁻¹ = 1 / 2 by norm_num]
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  have h3 : (0.0456512 : ℝ) ≤ ((3 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((3 : ℕ) : ℝ)⁻¹) := by
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [show (1 : ℝ) + ((3 : ℕ) : ℝ)⁻¹ = 4 / 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num), hl4,
      show ((3 : ℕ) : ℝ)⁻¹ = 1 / 3 by norm_num]
    linarith [Real.log_two_lt_d9, Real.log_three_gt_d9]
  have h5 : (0.0176784 : ℝ) ≤ ((5 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((5 : ℕ) : ℝ)⁻¹) := by
    have hl6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [show (1 : ℝ) + ((5 : ℕ) : ℝ)⁻¹ = 6 / 5 by norm_num,
      Real.log_div (by norm_num) (by norm_num), hl6,
      show ((5 : ℕ) : ℝ)⁻¹ = 1 / 5 by norm_num]
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_gt_d9]
  have h7 : (0.0087463 : ℝ) ≤ ((7 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((7 : ℕ) : ℝ)⁻¹) :=
    inv_sub_log_one_add_ge 7 (by norm_num) _ (by norm_num)
  have h11 : (0.0038066 : ℝ) ≤ ((11 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((11 : ℕ) : ℝ)⁻¹) :=
    inv_sub_log_one_add_ge 11 (by norm_num) _ (by norm_num)
  have h13 : (0.0027689 : ℝ) ≤ ((13 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((13 : ℕ) : ℝ)⁻¹) :=
    inv_sub_log_one_add_ge 13 (by norm_num) _ (by norm_num)
  have h17 : (0.0016495 : ℝ) ≤ ((17 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((17 : ℕ) : ℝ)⁻¹) :=
    inv_sub_log_one_add_ge 17 (by norm_num) _ (by norm_num)
  have h19 : (0.0013283 : ℝ) ≤ ((19 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((19 : ℕ) : ℝ)⁻¹) :=
    inv_sub_log_one_add_ge 19 (by norm_num) _ (by norm_num)
  have h23 : (0.0009140 : ℝ) ≤ ((23 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((23 : ℕ) : ℝ)⁻¹) :=
    inv_sub_log_one_add_ge 23 (by norm_num) _ (by norm_num)
  have h29 : (0.0005793 : ℝ) ≤ ((29 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((29 : ℕ) : ℝ)⁻¹) :=
    inv_sub_log_one_add_ge 29 (by norm_num) _ (by norm_num)
  have h31 : (0.0005079 : ℝ) ≤ ((31 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((31 : ℕ) : ℝ)⁻¹) :=
    inv_sub_log_one_add_ge 31 (by norm_num) _ (by norm_num)
  have h37 : (0.0003581 : ℝ) ≤ ((37 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((37 : ℕ) : ℝ)⁻¹) :=
    inv_sub_log_one_add_ge 37 (by norm_num) _ (by norm_num)
  have h41 : (0.0002922 : ℝ) ≤ ((41 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((41 : ℕ) : ℝ)⁻¹) :=
    inv_sub_log_one_add_ge 41 (by norm_num) _ (by norm_num)
  have h43 : (0.0002659 : ℝ) ≤ ((43 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((43 : ℕ) : ℝ)⁻¹) :=
    inv_sub_log_one_add_ge 43 (by norm_num) _ (by norm_num)
  have h47 : (0.0002229 : ℝ) ≤ ((47 : ℕ) : ℝ)⁻¹ - Real.log (1 + ((47 : ℕ) : ℝ)⁻¹) :=
    inv_sub_log_one_add_ge 47 (by norm_num) _ (by norm_num)
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  linarith

/-! ### The Euler product -/

/-- **The Euler product, with the threshold left free.**  For `L ≥ 99` and `y ≥ e^L`,
`∏_{p ≤ y}(1 + 1/p) ≤ 1.0002·e^{0.0849 + 9.003/L}·log y`.

The logarithm of the product is `∑_{p ≤ y} 1/p` (Mertens, `RMF.sum_primesBelow_inv_le`) minus the
head of `K` (`RMF.sum_head_inv_sub_log_one_add_ge`): `0.0849 = 0.2641 − 0.1792` is the residue of
Mertens' constant, `9.003/L` is Mertens' error, and `1.0002` passes from `log (y+1)` to `log y`. -/
theorem prod_one_add_inv_primesBelow_le_exp {y : ℕ} {L : ℝ} (hL : 99 ≤ L)
    (hy : Real.exp L ≤ (y : ℝ)) :
    ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ)⁻¹)
      ≤ 1.0002 * Real.exp (0.0849 + 9.003 / L) * Real.log y := by
  have hLpos' : (0 : ℝ) < L := by linarith
  have hy1 : L + 1 ≤ (y : ℝ) := le_trans (Real.add_one_le_exp L) hy
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith
  have hyn : 47 ≤ y := by
    have h : (47 : ℝ) ≤ (y : ℝ) := by linarith
    exact_mod_cast h
  have hL' : L ≤ Real.log y := (Real.le_log_iff_exp_le hypos).2 hy
  have hLpos : (0 : ℝ) < Real.log y := by linarith
  have hLy1 : L ≤ Real.log ((y : ℝ) + 1) :=
    le_trans hL' (Real.log_le_log hypos (by linarith))
  have hLy1pos : (0 : ℝ) < Real.log ((y : ℝ) + 1) := by linarith
  -- Mertens' second theorem, at `y + 1`
  have hmert : ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹
      ≤ Real.log (Real.log ((y : ℝ) + 1)) + 0.2641 + 9.003 / Real.log ((y : ℝ) + 1) := by
    have h := sum_primesBelow_inv_le (y := y + 1) (by omega)
    push_cast at h
    exact h
  -- the head of `K`, transported to the primes below `y + 1`
  have hsub : ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ)
      ⊆ Nat.primesBelow (y + 1) := by
    intro p hp
    rw [Nat.mem_primesBelow]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> exact ⟨by omega, by norm_num⟩
  have hhead : (0.1792 : ℝ)
      ≤ ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ)⁻¹ - Real.log (1 + (p : ℝ)⁻¹)) :=
    le_trans sum_head_inv_sub_log_one_add_ge
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => inv_sub_log_one_add_nonneg p)
  have hsplit : ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ)⁻¹ - Real.log (1 + (p : ℝ)⁻¹))
      = (∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹)
        - ∑ p ∈ Nat.primesBelow (y + 1), Real.log (1 + (p : ℝ)⁻¹) := Finset.sum_sub_distrib _ _
  have herr : 9.003 / Real.log ((y : ℝ) + 1) ≤ 9.003 / L :=
    div_le_div_of_nonneg_left (by norm_num) hLpos' hLy1
  have hbound : ∑ p ∈ Nat.primesBelow (y + 1), Real.log (1 + (p : ℝ)⁻¹)
      ≤ Real.log (Real.log ((y : ℝ) + 1)) + (0.0849 + 9.003 / L) := by
    linarith only [hhead, hsplit, hmert, herr]
  -- `log (y+1) ≤ 1.0002 · log y`, from `log (1 + 1/y) ≤ 1/y ≤ 1/(L+1)` and `L ≥ 99`
  have hshift : Real.log ((y : ℝ) + 1) ≤ 1.0002 * Real.log y := by
    have h1 : Real.log ((y : ℝ) + 1) - Real.log y = Real.log (((y : ℝ) + 1) / (y : ℝ)) := by
      rw [Real.log_div (by linarith) (by linarith)]
    have h2 : Real.log (((y : ℝ) + 1) / (y : ℝ)) ≤ ((y : ℝ) + 1) / (y : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : ((y : ℝ) + 1) / (y : ℝ) - 1 = 1 / (y : ℝ) := by
      field_simp
      ring
    have h4 : 1 / (y : ℝ) ≤ 1 / (L + 1) := one_div_le_one_div_of_le (by linarith) hy1
    have h5 : (99 : ℝ) * 100 ≤ Real.log y * (L + 1) :=
      mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
    have h6 : 1 / (L + 1) ≤ 0.0002 * Real.log y := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < L + 1)]
      linarith only [h5]
    linarith
  -- the product is the exponential of the sum
  have hprodeq : Real.exp (∑ p ∈ Nat.primesBelow (y + 1), Real.log (1 + (p : ℝ)⁻¹))
      = ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ)⁻¹) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun p _ => Real.exp_log (by positivity)
  rw [← hprodeq]
  calc Real.exp (∑ p ∈ Nat.primesBelow (y + 1), Real.log (1 + (p : ℝ)⁻¹))
      ≤ Real.exp (Real.log (Real.log ((y : ℝ) + 1)) + (0.0849 + 9.003 / L)) :=
        Real.exp_le_exp.2 hbound
    _ = Real.log ((y : ℝ) + 1) * Real.exp (0.0849 + 9.003 / L) := by
        rw [Real.exp_add, Real.exp_log hLy1pos]
    _ ≤ (1.0002 * Real.log y) * Real.exp (0.0849 + 9.003 / L) :=
        mul_le_mul_of_nonneg_right hshift (Real.exp_pos _).le
    _ = 1.0002 * Real.exp (0.0849 + 9.003 / L) * Real.log y := by ring

/-- **`∏_{p ≤ y}(1 + 1/p) ≤ 1.195·log y` for `y ≥ e^99`.**  The truth is `1.0828·log y`.

`RMF.prod_one_add_inv_primesBelow_le_exp` at `L = 99`, where the residual exponent is
`0.0849 + 9.003/99 ≤ 0.17584`. -/
theorem prod_one_add_inv_primesBelow_le {y : ℕ} (hy : Real.exp 99 ≤ (y : ℝ)) :
    ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ)⁻¹) ≤ 1.195 * Real.log y := by
  have hy1 : (100 : ℝ) ≤ (y : ℝ) := le_trans (by linarith [Real.add_one_le_exp (99 : ℝ)]) hy
  have hLpos : (0 : ℝ) ≤ Real.log y := (Real.log_pos (by linarith)).le
  -- `0.0849 + 9.003/99 = 0.1758394 ≤ 0.17584`
  have hexp : Real.exp ((0.0849 : ℝ) + 9.003 / 99) ≤ 1.1947 :=
    le_trans (Real.exp_le_exp.2 (by norm_num)) exp_mertens_residue_le
  refine le_trans (prod_one_add_inv_primesBelow_le_exp (by norm_num) hy) ?_
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 1.0002)) hLpos
  linarith only [h, hLpos]

end RMF
