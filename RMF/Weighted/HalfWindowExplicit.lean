/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.BlockFamilyExplicit

/-!
# The windows of `Z` at `q = ½`

At `q = ½` the Euler product's moment factor at a window's split point is at most `1`:
`E‖F_{z+1}(½+σ)‖ ≤ 1` for `σ ≥ 0` (`RMF.integral_norm_randomEulerProduct_shiftLine_half_le_one`).
Also here: the offset of the Rademacher free start is at most `104` for `0 ≤ E₀ ≤ 1`
(`RMF.radFreeStartThreshold_le_104`), and the mesoscopic range of `Z` at `q = ½` is at most the
sum of any bounds on its windows (`RMF.mesoRange_half_le_sum`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

lemma one_sub_exp_one_inv_pos : (0 : ℝ) < 1 - (Real.exp 1)⁻¹ := by
  have h : (Real.exp 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith [Real.exp_one_gt_d9])
  linarith

/-! ### One window at `q = ½` -/

/-- **The Euler product's moment at `q = ½` is at most `1`**: `E‖F_{z+1}(½+σ)‖ ≤ 1` for `σ ≥ 0`,
`z ≥ 2`. -/
lemma integral_norm_randomEulerProduct_shiftLine_half_le_one {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {z : ℕ} (hz : 2 ≤ z) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (z + 1)
        (shiftLine σ 0) ω‖ ^ (2 * (1 / 2 : ℝ)) ∂ν) ≤ 1 := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have h1 := hRa.integral_norm_randomEulerProduct_shift_rpow_le_log_sharp hσ (q := 1 / 2)
    (by norm_num) le_rfl hz
  have hs : shiftLine σ 0 = (((1 / 2 + σ : ℝ)) : ℂ) := by simp [shiftLine]
  rw [hs]
  refine le_trans h1 (le_of_eq ?_)
  norm_num

/-! ### The chaos windows -/

/-- `log a ≤ 104` for `0 < a ≤ 10⁹`. -/
lemma log_le_104_of_le {a : ℝ} (ha : 0 < a) (h : a ≤ 1000000000) : Real.log a ≤ 104 := by
  rw [Real.log_le_iff_le_exp ha]
  have h2 : (2 : ℝ) ^ 104 ≤ Real.exp 104 := by
    rw [show (104 : ℝ) = ((104 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) 104
  linarith [show (1000000000 : ℝ) ≤ 2 ^ 104 by norm_num]

/-- **The Rademacher free start's offset is below `104`** for `0 ≤ E₀ ≤ 1`: its three logarithms
have arguments below `10⁹` (the largest is `≈ 10⁸`). -/
lemma radFreeStartThreshold_le_104 {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1) :
    radFreeStartThreshold E₀ ≤ 104 := by
  have he2 : Real.exp (2 * E₀) ≤ 8 := by
    have h1 : Real.exp (2 * E₀) ≤ Real.exp 2 := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [Real.exp_one_pow]; norm_num
    have h3 := Real.exp_one_lt_d9
    have h4 : Real.exp 1 ^ 2 ≤ (2.72 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 2
    nlinarith
  have hee : Real.exp 2 ≤ 8 := by
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [Real.exp_one_pow]; norm_num
    have h3 := Real.exp_one_lt_d9
    have h4 : Real.exp 1 ^ 2 ≤ (2.72 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 2
    nlinarith
  unfold radFreeStartThreshold radUpperThreshold thrDirectThreshold blockNumThreshold
  rw [prop5UpperSlope_eq]
  refine max_le (max_le ?_ ?_) (max_le (by norm_num) ?_)
  · have hpos : 0 < 5 * (2 * Real.exp (2 * E₀)) * (25 + 2 * 20 + (48 + 4 * 20) + Real.exp 2 + 1) ^ 2
        / (3 / 100) := by positivity
    refine log_le_104_of_le hpos ?_
    have hb : (25 + 2 * 20 + (48 + 4 * 20) + Real.exp 2 + 1 : ℝ) ≤ 202 := by linarith
    have hb0 : (0 : ℝ) ≤ 25 + 2 * 20 + (48 + 4 * 20) + Real.exp 2 + 1 := by positivity
    have hsq : (25 + 2 * 20 + (48 + 4 * 20) + Real.exp 2 + 1 : ℝ) ^ 2 ≤ 202 ^ 2 :=
      pow_le_pow_left₀ hb0 hb 2
    rw [div_le_iff₀ (by norm_num)]
    have he0 : 0 ≤ Real.exp (2 * E₀) := (Real.exp_pos _).le
    nlinarith
  · refine log_le_104_of_le (by positivity) ?_
    nlinarith
  · exact log_le_104_of_le (by positivity) (by linarith)

/-- `e^{1/5} ≤ 5/4`. -/
lemma exp_one_fifth_le : Real.exp (1 / 5) ≤ 5 / 4 := by
  have h := Real.exp_bound_div_one_sub_of_interval (x := 1 / 5) (by norm_num) (by norm_num)
  have : (1 : ℝ) / (1 - 1 / 5) = 5 / 4 := by norm_num
  linarith

/-! ### The mesoscopic range at `q = ½` -/

/-- **The mesoscopic range of `Z` at `q = ½`, window by window**: for `k₀ ≤ J` and any bounds
`b k` on the windows' contributions `(2/log y)^{1/2}·E[W_k^{1/2}]`,
`E[((log y)⁻¹∫_{e^{-J}<|t|≤e^{-k₀}}‖F_{y+1}/(σ+it)‖²)^{1/2}] ≤ ∑_{k₀≤k<J} b k`. -/
theorem mesoRange_half_le_sum {Y : ℕ → Ω → ℂ} {ν : Measure Ω} (hY : IsRademacherPrimeValues Y ν)
    {σ : ℝ} {y k₀ J : ℕ} (hy2 : 2 ≤ y) (hσ : 0 < σ) (hk₀J : k₀ ≤ J) {b : ℕ → ℝ}
    (hb : ∀ k ∈ Finset.Ico k₀ J,
      (2 / Real.log y) ^ (1 / 2 : ℝ) * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
        (Real.exp (-(k : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂ν ≤ b k) :
    (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-(J : ℝ)) < |t|
          ∧ |t| ≤ Real.exp (-(k₀ : ℝ))},
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ (1 / 2 : ℝ) ∂ν)
      ≤ ∑ k ∈ Finset.Ico k₀ J, b k := by
  refine le_trans (integral_rpow_mesoRange_le_sum_windows hY hy2 hσ (by norm_num) (by norm_num)
    hk₀J) ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum hb

end RMF
