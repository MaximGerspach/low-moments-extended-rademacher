/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherChainingSharp
import RMF.Probability.RademacherBarrier
import RMF.Probability.ChaosMomentExplicit
import RMF.Weighted.MesoscopicChaos

/-!
# Lemma 2.3 and the block bad sets for the Rademacher RMF: the sharp constants

The constants of the sharp Rademacher Lemma 2.3, the twin of
`RMF/Probability/MaximalBarrierSharp.lean`; the barrier bounds that use them, at the chaining
slope `8`, are in `RMF/Probability/RademacherBarrierFloor.lean`.

* `RMF.radLocalPairConst_le` and `RMF.ten_pow_hundred_twenty_le_exp_exp_sixteen`: the chain
  threshold, evaluated.
* `RMF.radIndexRefine`, `RMF.radIndexConst`: the window is partitioned at `(K e^{τ+ϑ})⁻¹`,
  `K = radIndexRefine = 1152`, so that the sharp Lemma B.2
  (`RMF.IsRademacherRMF.measure_exists_gt_le_sharp`) runs at `Λ₂ = 2/K = 1/576`.
* `RMF.barrier_lower_exponent_six_le`: the exponents are linear (tilt `2`), so the lower event is
  taken at `6τ` rather than the Steinhaus `4τ`.
* `RMF.radBlockBadConst`: the constant of the bad sets of a mesoscopic block.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-! ### The chain threshold, evaluated -/

/-- `radLocalPairConst 2^{-1/2} ≤ 4·10⁷`. -/
lemma radLocalPairConst_le : radLocalPairConst ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 40000000 := by
  have hθ := two_rpow_neg_half_le
  have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  set θ := (2 : ℝ) ^ (-(1 / 2 : ℝ)) with hθdef
  have h1θ : (1 : ℝ) / 4 ≤ 1 - θ := by linarith
  have h1θ1 : 1 - θ ≤ 1 := by linarith
  have hu0 : (0 : ℝ) < 1 - θ := by linarith
  have hCf : radLocalPairFine θ ≤ 530 := by
    unfold radLocalPairFine
    have h3 : ((1 : ℝ) / 4) ^ 3 ≤ (1 - θ) ^ 3 := pow_le_pow_left₀ (by norm_num) h1θ 3
    have ha : 8 / (1 - θ) ^ 3 ≤ 8 / ((1 : ℝ) / 4) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
    have hb : 4 / (1 - θ) ≤ 4 / ((1 : ℝ) / 4) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1θ
    have hc : (8 : ℝ) / ((1 : ℝ) / 4) ^ 3 + 4 / ((1 : ℝ) / 4) + 2 = 530 := by norm_num
    linarith
  have hCf0 : (0 : ℝ) ≤ radLocalPairFine θ := by
    unfold radLocalPairFine
    positivity
  have hd : (1 : ℝ) / 2124 ≤ radLocalPairScale θ := by
    unfold radLocalPairScale
    refine le_min (by linarith) ?_
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  have hd0 : (0 : ℝ) < radLocalPairScale θ := lt_of_lt_of_le (by norm_num) hd
  have htail : radLocalPairTail θ ≤ 36103752 := by
    unfold radLocalPairTail
    have hsq : ((1 : ℝ) / 2124) ^ 2 ≤ radLocalPairScale θ ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hd 2
    have h1 : 2 / ((1 - θ) * radLocalPairScale θ ^ 2) ≤ 2 / ((1 / 4) * (1 / 2124) ^ 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul h1θ hsq (by positivity) (by linarith)
    have h2 : 6 / radLocalPairScale θ ≤ 6 / (1 / 2124) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
    have h3 : (2 : ℝ) / ((1 / 4) * (1 / 2124) ^ 2) + 6 / (1 / 2124) = 36103752 := by norm_num
    linarith
  unfold radLocalPairConst
  have hsq : 2 * (6 + radLocalPairFine θ) ^ 2 ≤ 2 * 536 ^ 2 := by
    have h0 : (0 : ℝ) ≤ 6 + radLocalPairFine θ := by linarith
    have h1 : 6 + radLocalPairFine θ ≤ 536 := by linarith
    nlinarith
  linarith

/-- `10¹²⁰ ≤ exp(e^{16})`: `e^{16} ≥ 1681` and `exp(y/120) ≥ 1 + y/120 ≥ 10`. -/
lemma ten_pow_hundred_twenty_le_exp_exp_sixteen : (10 : ℝ) ^ 120 ≤ Real.exp (Real.exp 16) := by
  have h8 : (41 : ℝ) ≤ Real.exp 8 := by
    have h := Real.quadratic_le_exp_of_nonneg (x := (8 : ℝ)) (by norm_num)
    norm_num at h
    linarith
  have hy : (1681 : ℝ) ≤ Real.exp 16 := by
    have hsq : Real.exp 16 = Real.exp 8 * Real.exp 8 := by
      rw [← Real.exp_add]
      norm_num
    have h := mul_le_mul h8 h8 (by norm_num) (Real.exp_pos 8).le
    rw [hsq]
    linarith
  have h1 : (1 : ℝ) + Real.exp 16 / 120 ≤ Real.exp (Real.exp 16 / 120) := by
    linarith [Real.add_one_le_exp (Real.exp 16 / 120)]
  have h2 : (10 : ℝ) ≤ 1 + Real.exp 16 / 120 := by
    have : (1681 : ℝ) / 120 ≤ Real.exp 16 / 120 := div_le_div_of_nonneg_right hy (by norm_num)
    have h3 : (9 : ℝ) ≤ 1681 / 120 := by norm_num
    linarith
  have h4 : (10 : ℝ) ^ 120 ≤ Real.exp (Real.exp 16 / 120) ^ 120 :=
    pow_le_pow_left₀ (by norm_num) (le_trans h2 h1) 120
  have h5 : Real.exp (Real.exp 16 / 120) ^ 120 = Real.exp (Real.exp 16) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  linarith

/-! ### The constants of Lemma 2.3 at one index -/

/-- The refinement `K` of the window's partition in the sharp Rademacher Lemma 2.3: `2/K = 1/576`
is the sharp Lemma B.2's largest `Λ₂`. -/
noncomputable def radIndexRefine : ℝ := 1152

/-- **The constant of the sharp Rademacher Lemma 2.3** at deficit `Δ₁`:
`4K·radChainConst (2/K)·e^{Δ₁}`, `K = radIndexRefine`. -/
noncomputable def radIndexConst (Δ₁ : ℝ) : ℝ :=
  4 * radIndexRefine * radChainConst (2 / radIndexRefine) * Real.exp Δ₁

lemma radIndexConst_pos (Δ₁ : ℝ) : 0 < radIndexConst Δ₁ := by
  have hK0 : (0 : ℝ) < radIndexRefine := by
    rw [show radIndexRefine = 1152 from rfl]
    norm_num
  have := radChainConst_pos (show (0 : ℝ) < 2 / radIndexRefine by positivity)
  rw [radIndexConst]
  positivity

/-- **Below the barrier, at the threshold `6τ` and the linear exponent**:
`τ + (a - 2·6τ) ≤ C₀ - 2A - 2b` for `a ≤ τ + C₀`, `A ≤ 4τ`, `b ≤ τ`. -/
lemma barrier_lower_exponent_six_le {a τ A b C₀ : ℝ} (hale : a ≤ τ + C₀) (hA : A ≤ 4 * τ)
    (hb : b ≤ τ) : τ + (a - 2 * (6 * τ)) ≤ C₀ - 2 * A - 2 * b := by
  linarith

/-! ### The constant of the bad sets of a mesoscopic block -/

/-- **The constant of the block bad sets at log-slope `β`**:
`radIndexConst (1 + 45√E₀)·∑_i i^{-2β}`; the factor `T e^ϑ` of the window is kept outside. -/
noncomputable def radBlockBadConst (E₀ β : ℝ) : ℝ :=
  radIndexConst (harperSharpDeficit E₀) * ∑' i : ℕ, (i : ℝ) ^ (-(2 * β))

lemma radBlockBadConst_pos (E₀ : ℝ) {β : ℝ} (hβ : 1 / 2 < β) : 0 < radBlockBadConst E₀ β := by
  have hs : Summable fun i : ℕ => (i : ℝ) ^ (-(2 * β)) :=
    Real.summable_nat_rpow.2 (by linarith)
  have h1 : (1 : ℝ) ≤ ∑' i : ℕ, (i : ℝ) ^ (-(2 * β)) := by
    have h := hs.le_tsum 1 (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
    simpa using h
  have := radIndexConst_pos (harperSharpDeficit E₀)
  unfold radBlockBadConst
  positivity

end RMF
