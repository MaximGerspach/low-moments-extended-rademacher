/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.RademacherExplicit
import RMF.NumberTheory.MertensBlock
import RMF.NumberTheory.MertensExplicit
import RMF.Weighted.EulerMomentHalf
import RMF.NumberTheory.MertensUniform

/-!
# The Euler product moment at `s = ½`, with a literal constant

`RMF.exists_moment_half_le` gives `E‖F_y(½)‖^{2q} ≤ C·(log y)^{q(2q-1)}` with `C` unspecified.  For
`½ ≤ q ≤ 1` this file gives `C = exp(3/5 + 1.42) ≈ 7.54` for every `y ≥ 2`
(`RMF.exists_moment_half_le_uniform`), the product of two literal bounds:

* `RMF.IsRademacherRMF.integral_norm_randomEulerProduct_half_rpow_le` gives
  `E‖F_y(½)‖^{2q} ≤ exp(q(2q-1)·∑_{p<y}1/p + 3/5)`, the `3/5` being the whole local cost;
* `RMF.sum_primesBelow_inv_le_log_log_add` gives `∑_{p≤y} 1/p ≤ log log y + 1.42` for every
  `y ≥ 2`.

It also proves Mertens' second theorem from below, `∑_{p≤y} 1/p ≥ log log y - 29`
(`RMF.log_log_sub_le_sum_primesBelow_inv`), which the range `q ≤ ½` needs.
-/

open MeasureTheory

namespace RMF

/-! ### The constant for every `y ≥ 2`

`RMF.exists_moment_half_le` routes the local moment through
`RMF.exists_local_expansion_rademacherLaw` and `RMF.exists_abs_log_sub_poly_le`, whose `δ^{-3}` is
the price of one statement covering *every* prime, including `p = 2`.
`RMF.prod_integral_norm_one_add_prime_le` avoids that — it splits the primes at `31` and uses the
chord below — and it carries **no hypothesis on `y`**.

Mertens enters as `RMF.sum_primesBelow_inv_le_log_log_add`, `∑_{p≤y} 1/p ≤ log log y + 1.42` for
every `y ≥ 2`; the truth is `½ − log log 2 = 0.8665`, attained at `y = 2`. -/

/-- **The Euler product moment at `s = ½`, uniformly in `y`.**  For `½ ≤ q ≤ 1` and every `y ≥ 2`,
`E‖F_{y+1}(½)‖^{2q} ≤ C·(log y)^{q(2q-1)}`, with the witness `C = exp(3/5 + 1.42) ≈ 7.54`: the
statement of `RMF.exists_moment_half_le` at `Q = 1`, restricted to the `q ≥ ½` the chord bound
needs.  `3/5` is the local cost and `1.42` is `RMF.sum_primesBelow_inv_le_log_log_add`, Mertens
without a threshold. -/
theorem exists_moment_half_le_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω),
        IsRademacherRMF f μ →
      ∀ q : ℝ, 1 / 2 ≤ q → q ≤ 1 → ∀ y : ℕ, 2 ≤ y →
        (∫ ω, ‖randomEulerProduct f (y + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ)
          ≤ C * (Real.log y) ^ (q * (2 * q - 1)) := by
  refine ⟨Real.exp (3 / 5 + 1.42), Real.exp_pos _, ?_⟩
  intro Ω _ f μ hf q hq0 hq1 y hy
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL0 : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hloc := hf.integral_norm_randomEulerProduct_half_rpow_le hq0 hq1 (y + 1)
  have hS := sum_primesBelow_inv_le_log_log_add hy
  have hc0 : (0 : ℝ) ≤ q * (2 * q - 1) := by nlinarith
  have hc1 : q * (2 * q - 1) ≤ 1 := by nlinarith
  have hstep : q * (2 * q - 1) * (∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹) + 3 / 5
      ≤ q * (2 * q - 1) * Real.log (Real.log y) + (3 / 5 + 1.42) := by
    have h := mul_le_mul_of_nonneg_left
      (by linarith : (∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹)
        ≤ Real.log (Real.log y) + 1.42) hc0
    nlinarith [h, hc0, hc1]
  refine le_trans hloc (le_trans (Real.exp_le_exp.2 hstep) (le_of_eq ?_))
  rw [Real.exp_add, mul_comm]
  congr 1
  rw [Real.rpow_def_of_pos hL0, mul_comm]

/-! ### Below the critical exponent: Mertens from below

For `q ≤ ½` the coefficient `q(2q-1)` is **negative**, so turning `∑_{p≤y}1/p` into
`(log y)^{q(2q-1)}` needs Mertens' second theorem in the opposite direction to the one
`RMF.sum_primesBelow_inv_le` supplies: a *lower* bound on the prime sum.

`RMF.abs_sum_prime_Ioc_inv_sub_log_log_sub_le` gives it with Mertens' constant already cancelled,
at the price of a crude `20/log 2`. -/

/-- **Mertens' second theorem from below.**  `∑_{p ≤ y} 1/p ≥ log log y - 29` for `y ≥ 2`. -/
theorem log_log_sub_le_sum_primesBelow_inv {y : ℕ} (hy : 2 ≤ y) :
    Real.log (Real.log y) - 29 ≤ ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹ := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hblock := abs_sum_prime_Ioc_inv_sub_log_log_sub_le 2 (y : ℝ) le_rfl hy2
  rw [show ⌊(2 : ℝ)⌋₊ = 2 by norm_num, Nat.floor_natCast] at hblock
  have hlow := (abs_le.1 hblock).1
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hll2 : Real.log (Real.log 2) ≤ 0 :=
    Real.log_nonpos hl2.le (by linarith [Real.log_two_lt_d9])
  have h29 : (20 : ℝ) / Real.log 2 ≤ 29 := by
    rw [div_le_iff₀ hl2]
    linarith [Real.log_two_gt_d9]
  have hsub : {p ∈ Finset.Ioc 2 y | p.Prime} ⊆ Nat.primesBelow (y + 1) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    exact Nat.mem_primesBelow.2 ⟨by omega, hp.2⟩
  have hmono : ∑ p ∈ {p ∈ Finset.Ioc 2 y | p.Prime}, (1 : ℝ) / p
      ≤ ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹ := by
    rw [show (∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹)
        = ∑ p ∈ Nat.primesBelow (y + 1), (1 : ℝ) / p from
      Finset.sum_congr rfl fun p _ => (one_div _).symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
  linarith

end RMF
