/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Reduction
import RMF.Weighted.Factorisation
import RMF.NumberTheory.CosinePrimeSum

/-!
# Rankin's bound on the smooth tail

The third term of `RMF.exists_integral_rpow_weightedRademacherSum_le` is

`T = ∑_{x < m ≤ y#, m y-smooth and squarefree} 1/m`.

The squarefree `y`-smooth numbers are exactly the divisors of `y#`, so `T` is a tail of a
**finite** sum whose full value is `∏_{p ≤ y}(1 + 1/p) ≍ log y`.  Rankin's trick bounds the tail:
on it `(m/x)^δ ≥ 1` for any `δ > 0`, so

`T ≤ x^{-δ} ∑_m m^{δ-1} = x^{-δ} ∏_{p ≤ y} (1 + p^{δ-1})`.

At `δ = c/log y` the product is `≪ (log y)^{e^c}` and `x^{-δ} = e^{-c log x / log y}`; at the
reduction's parameters, where `log x / log y = 4 log log x`, that is `(log x)^{e^c - 4c}`, best at
`c = log 4`, giving `T ≪ (log x)^{-1.55}`.  Since the error term of the same theorem is only
`≈ (log y)^{-1}`, the smooth tail is **dominated by an error already present**.

Both halves are proved here: the sum-to-product identity
`RMF.sum_smoothSquarefree_rpow_eq_prod`, and Rankin's step `RMF.smoothTailSum_le_rankin` on top
of it.

Both are the block `(0, y]` of their forms over a block of primes,
`RMF.sum_blockSquarefree_rpow_eq_prod` and `RMF.blockTailSum_le_rankin`; the truncation bound for a
band (`RMF/Weighted/LemmaT.lean`) reads the latter on a band `(y, z]`.
-/

open Finset

namespace RMF

/-- **The Dirichlet series of the squarefrees of a block, at trivial coefficients.**  The sum over
the squarefree `y`-rough `z`-smooth `m` of `m^r` is `∏_{y<p≤z} (1 + p^r)`, for every real `r`: the
case `f m = m ^ r` of `RMF.sum_blockSquarefree_eq_sum_powerset`, then `Finset.prod_one_add`. -/
theorem sum_blockSquarefree_rpow_eq_prod (y z : ℕ) (r : ℝ) :
    ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z)
        | m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m ∧ Squarefree m}, (m : ℝ) ^ r
      = ∏ p ∈ primesIco (y + 1) (z + 1), (1 + (p : ℝ) ^ r) := by
  rw [Finset.prod_one_add, sum_blockSquarefree_eq_sum_powerset]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.cast_prod]
  exact (Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p) r).symm

/-- **The squarefree `y`-smooth numbers are the subset products of the primes up to `y`.**
Any sum over the range of `RMF.sum_smoothSquarefree_rpow_eq_prod` is a sum over
`(Nat.primesBelow (y+1)).powerset`, via `m ↦ m.primeFactors` and `t ↦ ∏ p ∈ t, p`: the block
`(0, y]` of `RMF.sum_blockSquarefree_eq_sum_powerset`, every integer being `0`-rough.  The
logarithmically weighted sum of `Weighted/SmoothSums.lean` is one of its cases. -/
theorem sum_smoothSquarefree_eq_sum_powerset {M : Type*} [AddCommMonoid M] (y : ℕ) (f : ℕ → M) :
    ∑ m ∈ {m ∈ Finset.Icc 1 (primorial y)
        | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m}, f m
      = ∑ t ∈ (Nat.primesBelow (y + 1)).powerset, f (∏ p ∈ t, p) := by
  have h0 : ∀ n : ℕ, IsRough 0 n := fun n => isRough_iff.2 fun p hp _ => hp.pos
  have key := sum_blockSquarefree_eq_sum_powerset (M := M) 0 y f
  rw [zero_add, primesIco_one] at key
  rw [← key]
  exact Finset.sum_congr (Finset.filter_congr fun m _ => by simp [h0 m]) fun _ _ => rfl

/-- **The Dirichlet series of the smooth squarefrees, at trivial coefficients.**  The sum over
squarefree `y`-smooth `m` of `m^r` is the Euler product `∏_{p ≤ y} (1 + p^r)`, for every real `r`.

The block `(0, y]` of `RMF.sum_blockSquarefree_rpow_eq_prod`. -/
theorem sum_smoothSquarefree_rpow_eq_prod (y : ℕ) (r : ℝ) :
    ∑ m ∈ {m ∈ Finset.Icc 1 (primorial y)
        | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m}, (m : ℝ) ^ r
      = ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ r) := by
  have h0 : ∀ n : ℕ, IsRough 0 n := fun n => isRough_iff.2 fun p hp _ => hp.pos
  have key := sum_blockSquarefree_rpow_eq_prod 0 y r
  rw [zero_add, primesIco_one] at key
  rw [← key]
  exact Finset.sum_congr (Finset.filter_congr fun m _ => by simp [h0 m]) fun _ _ => rfl

/-- **Rankin's bound on the tail of a block of primes.**  Over the squarefree `y`-rough `z`-smooth
`m > x`, `∑ 1/m ≤ x^{-δ} ∏_{y<p≤z} (1 + p^{δ-1})`: on the tail `(m/x)^δ ≥ 1`, and the whole sum of
`m^{δ-1}` is `RMF.sum_blockSquarefree_rpow_eq_prod`. -/
theorem blockTailSum_le_rankin (y z : ℕ) {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    ∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial z)
        | m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m ∧ Squarefree m}, ((m : ℝ))⁻¹
      ≤ x ^ (-δ) * ∏ p ∈ primesIco (y + 1) (z + 1), (1 + (p : ℝ) ^ (δ - 1)) := by
  classical
  rw [← sum_blockSquarefree_rpow_eq_prod y z (δ - 1), Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum (g := fun m : ℕ => x ^ (-δ) * (m : ℝ) ^ (δ - 1)) ?_) ?_
  · -- on the tail `m > x`, so `1/m ≤ x^{-δ} m^{δ-1}`
    intro m hm
    have hmx : x < (m : ℝ) := by
      have h := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hm).1).1
      have h' : (⌊x⌋₊ : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h
      exact lt_of_lt_of_le (Nat.lt_floor_add_one x) h'
    have hm0 : (0 : ℝ) < m := lt_trans hx hmx
    have hpow : x ^ δ ≤ (m : ℝ) ^ δ := Real.rpow_le_rpow hx.le hmx.le hδ.le
    have h1 : (1 : ℝ) ≤ (x ^ δ)⁻¹ * (m : ℝ) ^ δ := by
      rw [← div_eq_inv_mul, le_div_iff₀ (Real.rpow_pos_of_pos hx δ), one_mul]
      exact hpow
    have h2 : x ^ (-δ) * (m : ℝ) ^ (δ - 1) = ((x ^ δ)⁻¹ * (m : ℝ) ^ δ) * ((m : ℝ))⁻¹ := by
      rw [Real.rpow_neg hx.le, Real.rpow_sub hm0, Real.rpow_one]
      ring
    rw [h2]
    calc ((m : ℝ))⁻¹ = 1 * ((m : ℝ))⁻¹ := (one_mul _).symm
      _ ≤ ((x ^ δ)⁻¹ * (m : ℝ) ^ δ) * ((m : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hm0.le)
  · -- the tail is a subset of the whole block
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro m hm
      rw [Finset.mem_filter, Finset.mem_Ioc] at hm
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.one_le_iff_ne_zero.2 (by omega), hm.1.2⟩, hm.2⟩
    · intro m _ _
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg (Nat.cast_nonneg m) _)

/-- **Rankin's bound on the smooth tail.**  The block `(0, y]` of `RMF.blockTailSum_le_rankin`. -/
theorem smoothTailSum_le_rankin (y : ℕ) {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    ∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial y)
        | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m}, ((m : ℝ))⁻¹
      ≤ x ^ (-δ) * ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (δ - 1)) := by
  have h0 : ∀ n : ℕ, IsRough 0 n := fun n => isRough_iff.2 fun p hp _ => hp.pos
  have key := blockTailSum_le_rankin 0 y hx hδ
  rw [zero_add, primesIco_one] at key
  exact (Finset.sum_congr (Finset.filter_congr fun m _ => by simp [h0 m])
    fun _ _ => rfl).trans_le key

/-- **Mertens with a shifted exponent.**  When `δ·log y ≤ 1`, every `p ≤ y` has
`p^{δ-1} = p^δ/p ≤ e/p`, so Rankin's Euler product is `≪ (log y)^e`.

`e < 3` is what ultimately makes the tail beat `1/log y` at the reduction's parameters. -/
theorem exists_prod_one_add_rpow_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y → ∀ δ : ℝ, 0 < δ → δ * Real.log y ≤ 1 →
      ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (δ - 1))
        ≤ C * (Real.log y) ^ (Real.exp 1) := by
  obtain ⟨C₂, hC₂, hprod⟩ := exists_prod_one_add_le_rpow_log
  refine ⟨Real.exp (Real.exp 1 * C₂), Real.exp_pos _, ?_⟩
  intro y hy δ hδ hδy
  refine hprod y hy (Real.exp 1) (Real.exp_pos 1).le (fun p => (p : ℝ) ^ (δ - 1))
    (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _) ?_
  -- the only content: `p^δ ≤ e` when `δ log p ≤ δ log y ≤ 1`
  intro p hp
  obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.1 hp
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hple : (p : ℝ) ≤ (y : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 hplt
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hpd : (p : ℝ) ^ δ ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hp0]
    refine Real.exp_le_exp.2 ?_
    have hlp : Real.log p ≤ Real.log y := Real.log_le_log hp0 hple
    calc Real.log p * δ ≤ Real.log y * δ := mul_le_mul_of_nonneg_right hlp hδ.le
      _ = δ * Real.log y := mul_comm _ _
      _ ≤ 1 := hδy
  rw [Real.rpow_sub hp0, Real.rpow_one, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hpd (inv_nonneg.2 hp0.le)

end RMF
