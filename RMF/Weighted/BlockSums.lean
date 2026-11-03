/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Factorisation
import RMF.Weighted.SmoothSums
import RMF.NumberTheory.MertensBlock
import RMF.NumberTheory.MertensBlockUniform

/-!
# Sums over the squarefree integers composed of primes in a block

The layered proof of the upper bound `E|S(x)|^{2q} ≪ (log x)^{q(2q-1)}` for fixed `½ < q < 1`
needs, on each layer `(y, z]` with `z = y^e`, the two sums

`∑_{m ∈ M} 1/m ≪ 1`  and  `∑_{m ∈ M} (1 + log m)/m ≪ log z`,

where `M` is the set of squarefree integers all of whose prime factors lie in `(y, z]`, with
implied constants **not depending on `y` or `z`**, for every block with `log z ≤ Λ·log y`.  The
layered argument applies them `K ≍ log log x` times, so a constant growing with `y` would be
useless.

This is the block form of `RMF.exists_sum_smoothSquarefree_one_add_log_div_le`, proved the same
way on the powerset of the block (`RMF.sum_blockSquarefree_eq_sum_powerset`).  Under
`m ↦ m.primeFactors` the two summands split as

`1/m = ∏_{p ∈ t} 1/p`,  `(1 + log m)/m = ∏_{p ∈ t} 1/p + (∑_{p ∈ t} log p) ∏_{p ∈ t} 1/p`,

so `Finset.prod_one_add` and `RMF.sum_powerset_sum_mul_prod_le` reduce both to sums over the
primes of the block.

## The one arithmetic input

Everything rests on `∑_{y < p ≤ z} 1/p ≤ A := log Λ + 1.86`, Mertens over a block of bounded
log-log length (`RMF.sum_prime_Ioc_inv_le_of_log_le'`, `RMF/NumberTheory/MertensBlockUniform.lean`):

* `∏_{y < p ≤ z}(1 + 1/p) ≤ e^A` — `Real.prod_one_add_le_exp_sum`, no further input;
* `∑_{y < p ≤ z} (log p)/p ≤ A·log z` — crudely, `log p ≤ log z` on the block.

Mertens' first theorem is not needed for the second, and Rankin is not needed either: the full
sum `∑_{m ∈ M} 1/m` is already bounded, so a restriction to `m > x` is free.

## Why `Λ` rather than `e`

The layers are **integers**: at `y_k = ⌊x^{e^{-(k-1)}}⌋₊` the floor costs
`log(t/(t-1)) ≤ log 2` at each end, so `log y_k ≤ e·log y_{k+1}` is false, while
`log y_k ≤ 2e·log y_{k+1}` holds as soon as `y_{k+1} ≥ 4`.  Carrying `Λ` costs one `log Λ` in
every constant and nothing else.
-/

open Finset

namespace RMF

/-! ### Over the primes of the block -/

/-- **The block's harmonic prime sum.**  `∑_{y < p ≤ z} 1/p ≤ log Λ + 1.86` for `2 ≤ y ≤ z`
and `1 ≤ Λ` with `log z ≤ Λ·log y`; `RMF.sum_prime_Ioc_inv_le_of_log_le'` transported to
`RMF.primesIco`. -/
theorem sum_inv_primesIco_le {y z : ℕ} {Λ : ℝ} (hy : 2 ≤ y) (hyz : y ≤ z)
    (hΛ : 1 ≤ Λ) (hlog : Real.log z ≤ Λ * Real.log y) :
    ∑ p ∈ primesIco (y + 1) (z + 1), ((p : ℝ))⁻¹ ≤ Real.log Λ + 1.86 := by
  calc ∑ p ∈ primesIco (y + 1) (z + 1), ((p : ℝ))⁻¹
      = ∑ p ∈ Finset.Ioc y z with Nat.Prime p, (1 : ℝ) / p := by
        rw [filter_prime_Ioc_eq_primesIco]
        exact Finset.sum_congr rfl fun p _ => (one_div _).symm
    _ ≤ Real.log Λ + 1.86 := sum_prime_Ioc_inv_le_of_log_le' hy hyz hΛ hlog

/-- **The block's Euler product is bounded.**  `∏_{y < p ≤ z}(1 + 1/p) ≤ e^{log Λ + 1.86}`.

Contrast the whole-range bound `∏_{p ≤ z}(1 + 1/p) ≍ log z`
(`RMF.exists_prod_one_add_le_rpow_log`): over a block of bounded log-log length there is no
logarithm left. -/
theorem prod_one_add_inv_primesIco_le {y z : ℕ} {Λ : ℝ} (hy : 2 ≤ y) (hyz : y ≤ z)
    (hΛ : 1 ≤ Λ) (hlog : Real.log z ≤ Λ * Real.log y) :
    ∏ p ∈ primesIco (y + 1) (z + 1), (1 + ((p : ℝ))⁻¹)
      ≤ Real.exp (Real.log Λ + 1.86) :=
  le_trans (Real.prod_one_add_le_exp_sum _ fun p => inv_nonneg.2 (Nat.cast_nonneg p))
    (Real.exp_le_exp.2 (sum_inv_primesIco_le hy hyz hΛ hlog))

/-- **The block's logarithmically weighted prime sum.**  `∑_{y < p ≤ z} (log p)/p ≤ A·log z` with
`A = log Λ + 1.86`.

Mertens' first theorem is *not* used: `log p ≤ log z` throughout the block, so the harmonic bound
already carries it. -/
theorem sum_log_div_primesIco_le {y z : ℕ} {Λ : ℝ} (hy : 2 ≤ y) (hyz : y ≤ z)
    (hΛ : 1 ≤ Λ) (hlog : Real.log z ≤ Λ * Real.log y) :
    ∑ p ∈ primesIco (y + 1) (z + 1), Real.log p * ((p : ℝ))⁻¹
      ≤ (Real.log Λ + 1.86) * Real.log z := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  have hlz : (0 : ℝ) ≤ Real.log z :=
    Real.log_nonneg (by linarith)
  calc ∑ p ∈ primesIco (y + 1) (z + 1), Real.log p * ((p : ℝ))⁻¹
      ≤ ∑ p ∈ primesIco (y + 1) (z + 1), Real.log z * ((p : ℝ))⁻¹ := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hpp, -, hpz⟩ := mem_primesIco.1 hp
        have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
        have hpzR : (p : ℝ) ≤ (z : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 hpz
        exact mul_le_mul_of_nonneg_right (Real.log_le_log hp0 hpzR) (inv_nonneg.2 hp0.le)
    _ = Real.log z * ∑ p ∈ primesIco (y + 1) (z + 1), ((p : ℝ))⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log z * (Real.log Λ + 1.86) :=
        mul_le_mul_of_nonneg_left (sum_inv_primesIco_le hy hyz hΛ hlog) hlz
    _ = (Real.log Λ + 1.86) * Real.log z := mul_comm _ _

/-! ### Over the squarefree integers of the block -/

/-- **The block's harmonic mass is bounded.**  `∑_{m ∈ M} 1/m ≤ e^{log Λ + 1.86}`, where `M`
is the set of squarefree integers composed of primes in `(y, z]`.

At the block scale this replaces Rankin's trick: the *whole* sum is bounded, so restricting it
to `m > x` costs nothing. -/
theorem sum_blockSquarefree_inv_le {y z : ℕ} {Λ : ℝ} (hy : 2 ≤ y) (hyz : y ≤ z)
    (hΛ : 1 ≤ Λ) (hlog : Real.log z ≤ Λ * Real.log y) :
    ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) |
        m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m ∧ Squarefree m}, ((m : ℝ))⁻¹
      ≤ Real.exp (Real.log Λ + 1.86) := by
  have hterm : ∀ t ∈ (primesIco (y + 1) (z + 1)).powerset,
      (((∏ p ∈ t, p : ℕ) : ℝ))⁻¹ = ∏ p ∈ t, ((p : ℝ))⁻¹ := fun t _ => by
    rw [Nat.cast_prod, Finset.prod_inv_distrib]
  have hGeq : ∑ t ∈ (primesIco (y + 1) (z + 1)).powerset, ∏ p ∈ t, ((p : ℝ))⁻¹
      = ∏ p ∈ primesIco (y + 1) (z + 1), (1 + ((p : ℝ))⁻¹) := (Finset.prod_one_add _).symm
  rw [sum_blockSquarefree_eq_sum_powerset y z fun m => ((m : ℝ))⁻¹,
    Finset.sum_congr rfl hterm, hGeq]
  exact prod_one_add_inv_primesIco_le hy hyz hΛ hlog

/-- **The block's logarithmically weighted mass.**  `∑_{m ∈ M} (1 + log m)/m ≤ e^A·(1 + A·log z)`
with `A = log Λ + 1.86`, i.e. `≪ log z` with a constant free of `y` and `z`.

The reindexing of `RMF.exists_sum_smoothSquarefree_one_add_log_div_le`, its two inputs replaced by
the block forms `RMF.prod_one_add_inv_primesIco_le` and `RMF.sum_log_div_primesIco_le`; of the two
logarithms of the whole-range bound `(log z)²`, one is gone over a block. -/
theorem sum_blockSquarefree_one_add_log_div_le {y z : ℕ} {Λ : ℝ} (hy : 2 ≤ y) (hyz : y ≤ z)
    (hΛ : 1 ≤ Λ) (hlog : Real.log z ≤ Λ * Real.log y) :
    ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) |
        m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m ∧ Squarefree m}, (1 + Real.log m) / m
      ≤ Real.exp (Real.log Λ + 1.86)
          * (1 + (Real.log Λ + 1.86) * Real.log z) := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  have hlz : (0 : ℝ) ≤ Real.log z := Real.log_nonneg (by linarith)
  have hlΛ : (0 : ℝ) ≤ Real.log Λ := Real.log_nonneg hΛ
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hA : (0 : ℝ) ≤ Real.log Λ + 1.86 := by
    have : (0 : ℝ) < 1.86 := by norm_num
    linarith
  -- the summand, transported to the powerset of the block
  have hterm : ∀ t ∈ (primesIco (y + 1) (z + 1)).powerset,
      (1 + Real.log ((∏ p ∈ t, p : ℕ) : ℝ)) / ((∏ p ∈ t, p : ℕ) : ℝ)
        = (∏ p ∈ t, ((p : ℝ))⁻¹) + (∑ p ∈ t, Real.log p) * ∏ p ∈ t, ((p : ℝ))⁻¹ := by
    intro t ht
    have hne : ∀ p ∈ t, ((p : ℝ)) ≠ 0 := fun p hp =>
      Nat.cast_ne_zero.2 (prime_of_mem_primesIco (Finset.mem_powerset.1 ht hp)).ne_zero
    rw [Nat.cast_prod, Real.log_prod hne, Finset.prod_inv_distrib, add_div, one_div,
      div_eq_mul_inv]
  have hstep : ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) |
        m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m ∧ Squarefree m}, (1 + Real.log m) / m
      = ∑ t ∈ (primesIco (y + 1) (z + 1)).powerset,
          ((∏ p ∈ t, ((p : ℝ))⁻¹) + (∑ p ∈ t, Real.log p) * ∏ p ∈ t, ((p : ℝ))⁻¹) :=
    (sum_blockSquarefree_eq_sum_powerset y z _).trans (Finset.sum_congr rfl hterm)
  have hwt := sum_powerset_sum_mul_prod_le (a := fun p : ℕ => Real.log p)
    (b := fun p : ℕ => ((p : ℝ))⁻¹) (fun p => Real.log_natCast_nonneg p)
    (fun p => inv_nonneg.2 (Nat.cast_nonneg p)) (primesIco (y + 1) (z + 1))
  have hGeq : ∑ t ∈ (primesIco (y + 1) (z + 1)).powerset, ∏ p ∈ t, ((p : ℝ))⁻¹
      = ∏ p ∈ primesIco (y + 1) (z + 1), (1 + ((p : ℝ))⁻¹) := (Finset.prod_one_add _).symm
  have hGnn : (0 : ℝ) ≤ ∏ p ∈ primesIco (y + 1) (z + 1), (1 + ((p : ℝ))⁻¹) :=
    Finset.prod_nonneg fun p _ => add_nonneg zero_le_one (inv_nonneg.2 (Nat.cast_nonneg p))
  have hlogdiv := sum_log_div_primesIco_le hy hyz hΛ hlog
  have hprodle := prod_one_add_inv_primesIco_le hy hyz hΛ hlog
  rw [hstep, Finset.sum_add_distrib, hGeq]
  calc ∏ p ∈ primesIco (y + 1) (z + 1), (1 + ((p : ℝ))⁻¹)
        + ∑ t ∈ (primesIco (y + 1) (z + 1)).powerset,
            (∑ p ∈ t, Real.log p) * ∏ p ∈ t, ((p : ℝ))⁻¹
      ≤ (1 + ∑ p ∈ primesIco (y + 1) (z + 1), Real.log p * ((p : ℝ))⁻¹)
          * ∏ p ∈ primesIco (y + 1) (z + 1), (1 + ((p : ℝ))⁻¹) := by linarith only [hwt]
    _ ≤ (1 + (Real.log Λ + 1.86) * Real.log z)
          * Real.exp (Real.log Λ + 1.86) := by
        refine mul_le_mul (by linarith only [hlogdiv]) hprodle hGnn ?_
        have : (0 : ℝ) ≤ (Real.log Λ + 1.86) * Real.log z := mul_nonneg hA hlz
        linarith
    _ = Real.exp (Real.log Λ + 1.86)
          * (1 + (Real.log Λ + 1.86) * Real.log z) := mul_comm _ _

end RMF
