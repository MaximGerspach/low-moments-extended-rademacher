/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.RademacherPrimeSum
import RMF.NumberTheory.CosinePrimeSum

/-!
# The Euler product moment on the real critical point

`RMF.exists_integral_rpow_weightedRademacherSum_le` carries `E‖F_y(½)‖^{2q}` symbolically.  This
file evaluates it.

`RMF.exists_prime_sum_bound_rademacherLaw` gives, for `Re s ≥ σ₀ > 1/3`,

`log E‖F_y(s)‖^{2q} = ∑_{p<y} p^{-2 Re s} (q² + q(q-1) cos(2 Im s log p)) + O(1)`.

At the **real** point `s = ½` the cosine is `1`, the bracket collapses to `q(2q-1)`, and Mertens
(`RMF.exists_abs_sum_primesBelow_inv_sub_log_log_le`) turns the prime sum into `log log y`.  So

`E‖F_y(½)‖^{2q} ≍ (log y)^{q(2q-1)}`,

which for `0 < q ≤ ½` is bounded, and decays for `q < ½`.

The `O(1)` constant is obtained **before** the probability space is introduced, so it is uniform in
it — the shape the reduction needs.
-/

open Finset MeasureTheory

namespace RMF

/-- **The Rademacher Euler product moment at `s = ½`.**  `E‖F_y(½)‖^{2q} ≤ C (log y)^{q(2q-1)}`
for `|q| ≤ Q` and `y ≥ 2`, with `C` depending only on `Q`. -/
theorem exists_moment_half_le {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω),
        IsRademacherRMF f μ →
      ∀ q ∈ Set.Icc (-Q) Q, ∀ y : ℕ, 2 ≤ y →
        (∫ ω, ‖randomEulerProduct f (y + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ)
          ≤ C * (Real.log y) ^ (q * (2 * q - 1)) := by
  obtain ⟨C₁, hC₁, hps⟩ :=
    exists_prime_sum_bound_rademacherLaw hQ (by norm_num : (1 : ℝ) / 3 < 1 / 2)
  obtain ⟨C₂, hC₂, hmert⟩ := exists_abs_sum_primesBelow_inv_sub_log_log_le
  refine ⟨Real.exp (C₁ + Q * (2 * Q + 1) * C₂), Real.exp_pos _, ?_⟩
  intro Ω _ f μ hf q hq y hy
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hrhs : (0 : ℝ) < Real.exp (C₁ + Q * (2 * Q + 1) * C₂) * (Real.log y) ^ (q * (2 * q - 1)) :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hlogy _)
  rcases le_or_gt (∫ ω, ‖randomEulerProduct f (y + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ) 0 with hI | hI
  · exact le_trans hI hrhs.le
  -- the moment factorises into the local moments, and the prime sum evaluates
  have hre : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have him : ((1 / 2 : ℂ)).im = 0 := by norm_num
  have hfact := hf.integral_norm_randomEulerProduct_rpow_of_pos (y + 1)
    (by rw [hre]; norm_num : (0 : ℝ) < ((1 / 2 : ℂ)).re) (2 * q)
  have hbound := hps q hq (1 / 2 : ℂ) (by rw [hre]) (y + 1)
  rw [← hfact] at hbound
  -- the bracket collapses at the real point
  have hS : (∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ) ^ (-2 * ((1 / 2 : ℂ)).re)
        * (q ^ 2 + q * (q - 1) * Real.cos (2 * (((1 / 2 : ℂ)).im * Real.log p)))))
      = q * (2 * q - 1) * ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hre, him]
    norm_num [Real.rpow_neg_one]
    ring
  rw [hS] at hbound
  -- Mertens, with the sign of `q(2q-1)` handled by the absolute value
  have hm := hmert y hy
  have hcoef : |q * (2 * q - 1)| ≤ Q * (2 * Q + 1) := by
    rw [abs_mul]
    have h1 : |q| ≤ Q := abs_le.2 ⟨hq.1, hq.2⟩
    have h2 : |2 * q - 1| ≤ 2 * Q + 1 := by
      rw [abs_le]
      constructor <;> [linarith [hq.1]; linarith [hq.2]]
    exact mul_le_mul h1 h2 (abs_nonneg _) hQ
  have hkey : Real.log (∫ ω, ‖randomEulerProduct f (y + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ q * (2 * q - 1) * Real.log (Real.log y) + (C₁ + Q * (2 * Q + 1) * C₂) := by
    have h3 := (abs_le.1 hbound).2
    have h4 : q * (2 * q - 1) * (∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹)
        ≤ q * (2 * q - 1) * Real.log (Real.log y) + Q * (2 * Q + 1) * C₂ := by
      have h5 : |q * (2 * q - 1)
          * ((∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹) - Real.log (Real.log y))|
          ≤ Q * (2 * Q + 1) * C₂ := by
        rw [abs_mul]
        exact mul_le_mul hcoef hm (abs_nonneg _) (by positivity)
      have h6 := (abs_le.1 h5).2
      nlinarith [h6]
    linarith
  -- exponentiate
  have hexp : (∫ ω, ‖randomEulerProduct f (y + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
      = Real.exp (Real.log (∫ ω, ‖randomEulerProduct f (y + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)) :=
    (Real.exp_log hI).symm
  rw [hexp]
  refine le_trans (Real.exp_le_exp.2 hkey) (le_of_eq ?_)
  rw [Real.exp_add, Real.rpow_def_of_pos hlogy]
  ring_nf

end RMF
