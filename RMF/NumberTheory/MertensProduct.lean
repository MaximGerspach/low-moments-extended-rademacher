/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.PSeries
import RMF.NumberTheory.CosinePrimeSum

/-!
# Mertens' third theorem

`∏_{p ≤ y} (1 - 1/p)⁻¹ ≍ log y`, in the additive form

`|log ∏_{p ≤ y} (1 - 1/p)⁻¹ - log log y| ≤ C`.

This is the second moment of a Steinhaus random Euler product on the critical line:
`RMF.IsSteinhausRMF.integral_norm_randomEulerProduct_sq` evaluates
`E‖F_y(1/2 + ih)‖²` as exactly this product, so the estimate here turns that identity into the
bound `≍ log y` that the Laplace transform estimate needs.

The proof is Mertens' *second* theorem, already available as
`RMF.exists_abs_sum_primesBelow_inv_sub_log_log_le`, plus the observation that

`0 ≤ -log(1 - 1/p) - 1/p ≤ 2/p²`,

so that the two differ by an absolutely convergent sum over the primes.  No numerical value for
that sum is needed: it is bounded by a `tsum` and absorbed into the constant.
-/

namespace RMF

open Finset

/-- The logarithm of one Euler factor differs from `1/p` by `O(1/p²)`.  This is the `n = 1` case
of the Taylor estimate `Real.abs_log_sub_add_sum_range_le`. -/
theorem abs_log_one_sub_inv_inv_sub_inv_le {p : ℕ} (hp : 2 ≤ p) :
    |Real.log ((1 - ((p : ℝ))⁻¹)⁻¹) - ((p : ℝ))⁻¹| ≤ 2 / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  set t : ℝ := ((p : ℝ))⁻¹ with ht
  have ht0 : 0 < t := by positivity
  have ht2 : t ≤ 1 / 2 := by
    rw [ht, inv_le_comm₀ hp0 (by norm_num)]
    linarith
  have htabs : |t| < 1 := by
    rw [abs_of_pos ht0]
    linarith
  have hkey := Real.abs_log_sub_add_sum_range_le htabs 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one] at hkey
  have habs : |t| = t := abs_of_pos ht0
  rw [habs] at hkey
  have hlog : Real.log ((1 - t)⁻¹) = -Real.log (1 - t) := Real.log_inv _
  rw [hlog, show -Real.log (1 - t) - t = -(t + Real.log (1 - t)) by ring, abs_neg]
  refine hkey.trans ?_
  have hden : (1 : ℝ) / 2 ≤ 1 - t := by linarith
  have hsq : t ^ 2 = 1 / (p : ℝ) ^ 2 := by
    rw [ht, inv_pow, one_div]
  calc t ^ 2 / (1 - t) ≤ t ^ 2 / (1 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = 2 / (p : ℝ) ^ 2 := by rw [hsq]; ring

/-- The primes contribute an absolutely convergent sum of `1/p²`, bounded independently of the
range.  No numerical value is needed. -/
theorem exists_sum_primesBelow_inv_sq_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∑ p ∈ Nat.primesBelow N, 1 / ((p : ℝ)) ^ 2 ≤ B := by
  classical
  have hf0 : ∀ n : ℕ, 0 ≤ (if n.Prime then 1 / ((n : ℝ)) ^ 2 else 0) := by
    intro n
    split <;> positivity
  have hle : ∀ n : ℕ, (if n.Prime then 1 / ((n : ℝ)) ^ 2 else 0) ≤ 1 / ((n : ℝ)) ^ 2 := by
    intro n
    split
    · exact le_rfl
    · positivity
  have hsum : Summable (fun n : ℕ => if n.Prime then 1 / ((n : ℝ)) ^ 2 else 0) :=
    Summable.of_nonneg_of_le hf0 hle (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine ⟨∑' n : ℕ, (if n.Prime then 1 / ((n : ℝ)) ^ 2 else 0), tsum_nonneg hf0, fun N => ?_⟩
  calc ∑ p ∈ Nat.primesBelow N, 1 / ((p : ℝ)) ^ 2
      = ∑ p ∈ Nat.primesBelow N, (if p.Prime then 1 / ((p : ℝ)) ^ 2 else 0) :=
        Finset.sum_congr rfl fun p hp => by rw [if_pos (Nat.prime_of_mem_primesBelow hp)]
    _ ≤ ∑' n : ℕ, (if n.Prime then 1 / ((n : ℝ)) ^ 2 else 0) :=
        hsum.sum_le_tsum _ (fun n _ => hf0 n)

/-- **Mertens' third theorem.**  `∏_{p ≤ y} (1 - 1/p)⁻¹ ≍ log y`. -/
theorem exists_abs_log_prod_primesBelow_sub_log_log_le :
    ∃ C > 0, ∀ N : ℕ, 2 ≤ N →
      |Real.log (∏ p ∈ Nat.primesBelow (N + 1), (1 - ((p : ℝ))⁻¹)⁻¹)
        - Real.log (Real.log N)| ≤ C := by
  obtain ⟨C₀, hC₀, hmertens⟩ := exists_abs_sum_primesBelow_inv_sub_log_log_le
  obtain ⟨B, hB0, hB⟩ := exists_sum_primesBelow_inv_sq_le
  refine ⟨C₀ + 2 * B, by positivity, fun N hN => ?_⟩
  -- the logarithm of the product is the sum of the logarithms
  have hne : ∀ p ∈ Nat.primesBelow (N + 1), (1 - ((p : ℝ))⁻¹)⁻¹ ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    exact inv_ne_zero (ne_of_gt (by linarith : (0 : ℝ) < 1 - ((p : ℝ))⁻¹))
  rw [Real.log_prod hne]
  -- and it differs from Mertens' second sum by a convergent tail
  have htail : |∑ p ∈ Nat.primesBelow (N + 1), Real.log ((1 - ((p : ℝ))⁻¹)⁻¹)
      - ∑ p ∈ Nat.primesBelow (N + 1), ((p : ℝ))⁻¹| ≤ 2 * B := by
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ p ∈ Nat.primesBelow (N + 1),
          |Real.log ((1 - ((p : ℝ))⁻¹)⁻¹) - ((p : ℝ))⁻¹|
        ≤ ∑ p ∈ Nat.primesBelow (N + 1), 2 / ((p : ℝ)) ^ 2 :=
          Finset.sum_le_sum fun p hp =>
            abs_log_one_sub_inv_inv_sub_inv_le (Nat.prime_of_mem_primesBelow hp).two_le
      _ = 2 * ∑ p ∈ Nat.primesBelow (N + 1), 1 / ((p : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ 2 * B := by
          have := hB (N + 1)
          linarith
  have := hmertens N hN
  calc |∑ p ∈ Nat.primesBelow (N + 1), Real.log ((1 - ((p : ℝ))⁻¹)⁻¹) - Real.log (Real.log N)|
      ≤ |∑ p ∈ Nat.primesBelow (N + 1), Real.log ((1 - ((p : ℝ))⁻¹)⁻¹)
          - ∑ p ∈ Nat.primesBelow (N + 1), ((p : ℝ))⁻¹|
        + |∑ p ∈ Nat.primesBelow (N + 1), ((p : ℝ))⁻¹ - Real.log (Real.log N)| := by
        exact abs_sub_le _ _ _
    _ ≤ 2 * B + C₀ := by gcongr
    _ = C₀ + 2 * B := by ring

end RMF
