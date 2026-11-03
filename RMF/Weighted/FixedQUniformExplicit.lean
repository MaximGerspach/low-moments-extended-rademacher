/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.FixedQTerms
import RMF.Weighted.FixedQScales
import RMF.Weighted.Fluctuations
import RMF.Weighted.Sieve
import RMF.Weighted.SmoothSumsExplicit
import RMF.Weighted.BlockSums
import RMF.Weighted.EulerMomentHalfExplicit

/-!
# The second moment of the weighted sum at every scale

Two elementary bounds: the harmonic sum `∑_{n ≤ N} 1/n ≤ 1 + log N`
(`RMF.sum_inv_Icc_le_one_add_log`), and `E|S(x)|² ≤ 1 + log x` for every `x ≥ 1`
(`RMF.integral_normSq_weightedRademacherSum_le_one_add_log`).  With Jensen the second gives
`E|S(x)|^{2q} ≤ (1 + log x)^q` for `0 < q ≤ 1`, which bounds the moments by a constant on any
bounded range of `x`.
-/

open MeasureTheory

namespace RMF

/-- **The harmonic sum**: `∑_{n ≤ N} 1/n ≤ 1 + log N`.

`1/(n+1) ≤ log(n+1) − log n` is `log t ≤ t − 1` at `t = n/(n+1)`; telescoping leaves the `n = 1`
term. -/
theorem sum_inv_Icc_le_one_add_log (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ ≤ 1 + Real.log N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · norm_num
    · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      have hstep : ((N : ℝ) + 1)⁻¹ ≤ Real.log ((N : ℝ) + 1) - Real.log N := by
        have h := Real.log_le_sub_one_of_pos
          (x := (N : ℝ) / ((N : ℝ) + 1)) (by positivity)
        rw [Real.log_div (ne_of_gt hN0) (by positivity)] at h
        have hid : (N : ℝ) / ((N : ℝ) + 1) - 1 = -(((N : ℝ) + 1)⁻¹) := by
          field_simp
          ring
        rw [hid] at h
        linarith
      push_cast
      linarith

/-- **The second moment at every scale**: `E|S(x)|² ≤ 1 + log x` for `x ≥ 1`.

Orthogonality (`RMF.integral_normSq_weightedRademacherSum`) makes it `∑_{n ≤ x} μ²(n)/n`, and
dropping the squarefree filter leaves the harmonic sum. -/
theorem integral_normSq_weightedRademacherSum_le_one_add_log {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ) {x : ℝ}
    (hx : 1 ≤ x) :
    (∫ ω, ‖weightedRademacherSum f x ω‖ ^ 2 ∂μ) ≤ 1 + Real.log x := by
  classical
  rw [integral_normSq_weightedRademacherSum hf x]
  have hfl : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfl0 : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast (hfl : 0 < ⌊x⌋₊)
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun i _ _ => by positivity) ?_
  refine le_trans (sum_inv_Icc_le_one_add_log ⌊x⌋₊) ?_
  have hlog : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log hfl0 (Nat.floor_le (by linarith))
  linarith

end RMF
