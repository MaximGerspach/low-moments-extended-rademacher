/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UCellsChaosLeavesExplicit

/-!
# The chaos regime's cells, part 3

`RMF.u_cell_chaos` at the numerals of the cells `q ∈ [0.47, 0.48]` and `[0.48, 0.49]`; their
certificate totals are `24.38` and `23.98` (of `25`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 4000000 in
-- seventeen kernel-checked numerals
/-- **The chaos regime's cell `q ∈ [47 / 100, 12 / 25]`**: for `Λ = log log x ≥ 4000`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (`RMF.u_cell_chaos`; certificate total `24.38`). -/
theorem u_cell_chaos_5 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 4000 ≤ Real.log (Real.log x))
    (hq1 : 47 / 100 ≤ q) (hq2 : q ≤ 12 / 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  have hq0 : 0 ≤ q := by linarith
  have ho : (1 - (12 / 25 : ℝ)) ^ (-(12 / 25 : ℝ)) ≤ 137 / 100 :=
    one_sub_rpow_neg_le_of (by norm_num) (by interval_decide (trust := kernel))
  have hA1 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 101 →
      (⟨65, 105 / 2, 60, 20, 2873⟩ : WinChaos).const E₀ q K ≤ (6759 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 47 / 100) (b := 12 / 25)
      (ℓK := 101) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 42239 / 1000)
      (cb := 2457 / 2000) (e := 12 / 25) (j := 6759 / 1000) (d := 6693 / 1000)
      ⟨65, 105 / 2, 60, 20, 2873⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 47 / 100) (qu := 12 / 25) (b := 82111 / 50000)
    (c := 13803 / 125000) (Gb := 2227 / 1000) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb1 : (2227 / 1000) * (6759 / 1000)
      * (1 - (12 / 25 : ℝ)) ^ (-(12 / 25 : ℝ)) * (10075 / 10000) ≤ 20777 / 1000 :=
    calc _ ≤ (2227 / 1000 : ℝ) * (6759 / 1000) * (137 / 100) * (10075 / 10000) := by gcongr
      _ ≤ 20777 / 1000 := by norm_num
  have hA2 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 100 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (841 / 125) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 47 / 100) (b := 12 / 25)
      (ℓK := 100) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 41709 / 1000)
      (cb := 12287 / 10000) (e := 12 / 25) (j := 841 / 125) (d := 1669 / 250)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 47 / 100) (qu := 12 / 25) (b := 135509 / 100000)
    (c := 408739 / 10000000) (Gb := 2003 / 1000) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb2 : (2003 / 1000) * (841 / 125)
      * (1 - (12 / 25 : ℝ)) ^ (-(12 / 25 : ℝ)) * (10075 / 10000) ≤ 18601 / 1000 :=
    calc _ ≤ (2003 / 1000 : ℝ) * (841 / 125) * (137 / 100) * (10075 / 10000) := by gcongr
      _ ≤ 18601 / 1000 := by norm_num
  have hA3 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 99 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (841 / 125) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 47 / 100) (b := 12 / 25)
      (ℓK := 99) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 41709 / 1000)
      (cb := 12287 / 10000) (e := 12 / 25) (j := 841 / 125) (d := 3327 / 500)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 47 / 100) (qu := 12 / 25) (b := 125193 / 100000)
    (c := 152939 / 10000000) (Gb := 1931 / 1000) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb3 : (1931 / 1000) * (841 / 125)
      * (1 - (12 / 25 : ℝ)) ^ (-(12 / 25 : ℝ)) * (10075 / 10000) ≤ 17933 / 1000 :=
    calc _ ≤ (1931 / 1000 : ℝ) * (841 / 125) * (137 / 100) * (10075 / 10000) := by gcongr
      _ ≤ 17933 / 1000 := by norm_num
  have hA4 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 98 →
      (⟨63, 103 / 2, 60, 20, 2834⟩ : WinChaos).const E₀ q K ≤ (3349 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 47 / 100) (b := 12 / 25)
      (ℓK := 98) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 41179 / 1000)
      (cb := 12289 / 10000) (e := 12 / 25) (j := 3349 / 500) (d := 1659 / 250)
      ⟨63, 103 / 2, 60, 20, 2834⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 47 / 100) (qu := 12 / 25) (b := 121431 / 100000)
    (c := 588533 / 100000000) (Gb := 381 / 200) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb4 : (381 / 200) * (3349 / 500)
      * (1 - (12 / 25 : ℝ)) ^ (-(12 / 25 : ℝ)) * (10075 / 10000) ≤ 4403 / 250 :=
    calc _ ≤ (381 / 200 : ℝ) * (3349 / 500) * (137 / 100) * (10075 / 10000) := by gcongr
      _ ≤ 4403 / 250 := by norm_num
  have hA5 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 74 →
      (⟨51, 87 / 2, 60, 16, 2600⟩ : WinChaos).const E₀ q K ≤ (6187 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 47 / 100) (b := 12 / 25)
      (ℓK := 74) (Ci' := 5977 / 5000) (s' := 729 / 50) (U := 17379 / 500)
      (cb := 6177 / 5000) (e := 12 / 25) (j := 6187 / 1000) (d := 6133 / 1000)
      ⟨51, 87 / 2, 60, 16, 2600⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_16 h0 h1)
      (uChaosRadS_60_16 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG5 := thetaWindowConstQ_rpow_le_of (ql := 47 / 100) (qu := 12 / 25) (b := 119251 / 100000)
    (c := 409219 / 1000000000) (Gb := 1891 / 1000) (by norm_num) (by norm_num) 31 uChaosEps_31
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb5 : (1891 / 1000) * (6187 / 1000)
      * (1 - (12 / 25 : ℝ)) ^ (-(12 / 25 : ℝ)) * (10075 / 10000) ≤ 16149 / 1000 :=
    calc _ ≤ (1891 / 1000 : ℝ) * (6187 / 1000) * (137 / 100) * (10075 / 10000) := by gcongr
      _ ≤ 16149 / 1000 := by norm_num
  have hA6 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 44 →
      (⟨36, 67 / 2, 50, 12, 2298⟩ : WinChaos).const E₀ q K ≤ (219 / 40) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 47 / 100) (b := 12 / 25)
      (ℓK := 44) (Ci' := 12033 / 10000) (s' := 14233 / 1000) (U := 3328 / 125)
      (cb := 12519 / 10000) (e := 12 / 25) (j := 219 / 40) (d := 5431 / 1000)
      ⟨36, 67 / 2, 50, 12, 2298⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_50_12 h0 h1)
      (uChaosRadS_50_12 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG6 := thetaWindowConstQ_rpow_le_of (ql := 47 / 100) (qu := 12 / 25) (b := 119251 / 100000)
    (c := 409219 / 1000000000) (Gb := 1891 / 1000) (by norm_num) (by norm_num) 61 uChaosEps_61
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb6 : (1891 / 1000) * (219 / 40)
      * (1 - (12 / 25 : ℝ)) ^ (-(12 / 25 : ℝ)) * (10075 / 10000) ≤ 14291 / 1000 :=
    calc _ ≤ (1891 / 1000 : ℝ) * (219 / 40) * (137 / 100) * (10075 / 10000) := by gcongr
      _ ≤ 14291 / 1000 := by norm_num
  have hA7 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      (⟨20, 45 / 2, 35, 10, 2000⟩ : WinChaos).const E₀ q K ≤ (2277 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 47 / 100) (b := 12 / 25)
      (ℓK := 8) (Ci' := 12177 / 10000) (s' := 13749 / 1000) (U := 17887 / 1000)
      (cb := 803 / 625) (e := 12 / 25) (j := 2277 / 500) (d := 451 / 100)
      ⟨20, 45 / 2, 35, 10, 2000⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_35_10 h0 h1)
      (uChaosRadS_35_10 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG7 := thetaWindowConstQ_rpow_le_of (ql := 47 / 100) (qu := 12 / 25) (b := 119251 / 100000)
    (c := 409219 / 1000000000) (Gb := 1891 / 1000) (by norm_num) (by norm_num) 97 uChaosEps_97
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb7 : (1891 / 1000) * (2277 / 500)
      * (1 - (12 / 25 : ℝ)) ^ (-(12 / 25 : ℝ)) * (10763 / 10000) ≤ 12699 / 1000 :=
    calc _ ≤ (1891 / 1000 : ℝ) * (2277 / 500) * (137 / 100) * (10763 / 10000) := by gcongr
      _ ≤ 12699 / 1000 := by norm_num
  exact u_cell_chaos hX hx hΛ (by norm_num) hq1 hq2 (by norm_num) uChaosW_valid_1
    uChaosW_valid_2 uChaosW_valid_3 uChaosW_valid_4 uChaosW_valid_5 uChaosW_valid_6
    uChaosW_valid_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hA1 hA2 hA3 hA4 hA5 hA6 hA7 hG1 hG2 hG3 hG4 hG5 hG6 hG7 hb1 hb2
    hb3 hb4 hb5 hb6 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by interval_decide (trust := kernel))
    (by rw [rpow_eq_exp_mul_log (by norm_num), rpow_eq_exp_mul_log (by norm_num)]
        interval_decide (trust := kernel))

set_option maxHeartbeats 4000000 in
-- seventeen kernel-checked numerals
/-- **The chaos regime's cell `q ∈ [12 / 25, 49 / 100]`**: for `Λ = log log x ≥ 4000`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (`RMF.u_cell_chaos`; certificate total `23.98`). -/
theorem u_cell_chaos_6 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 4000 ≤ Real.log (Real.log x))
    (hq1 : 12 / 25 ≤ q) (hq2 : q ≤ 49 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  have hq0 : 0 ≤ q := by linarith
  have ho : (1 - (49 / 100 : ℝ)) ^ (-(49 / 100 : ℝ)) ≤ 174 / 125 :=
    one_sub_rpow_neg_le_of (by norm_num) (by interval_decide (trust := kernel))
  have hA1 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 101 →
      (⟨65, 105 / 2, 60, 20, 2873⟩ : WinChaos).const E₀ q K ≤ (7033 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 12 / 25) (b := 49 / 100)
      (ℓK := 101) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 20721 / 500)
      (cb := 2457 / 2000) (e := 49 / 100) (j := 7033 / 1000) (d := 3451 / 500)
      ⟨65, 105 / 2, 60, 20, 2873⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 12 / 25) (qu := 49 / 100) (b := 161123 / 100000)
    (c := 13803 / 125000) (Gb := 1123 / 500) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb1 : (1123 / 500) * (7033 / 1000)
      * (1 - (49 / 100 : ℝ)) ^ (-(49 / 100 : ℝ)) * (10075 / 10000) ≤ 11077 / 500 :=
    calc _ ≤ (1123 / 500 : ℝ) * (7033 / 1000) * (174 / 125) * (10075 / 10000) := by gcongr
      _ ≤ 11077 / 500 := by norm_num
  have hA2 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 100 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (7001 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 12 / 25) (b := 49 / 100)
      (ℓK := 100) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 20461 / 500)
      (cb := 12287 / 10000) (e := 49 / 100) (j := 7001 / 1000) (d := 1377 / 200)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 12 / 25) (qu := 49 / 100) (b := 16619 / 12500)
    (c := 408739 / 10000000) (Gb := 101 / 50) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb2 : (101 / 50) * (7001 / 1000)
      * (1 - (49 / 100 : ℝ)) ^ (-(49 / 100 : ℝ)) * (10075 / 10000) ≤ 9917 / 500 :=
    calc _ ≤ (101 / 50 : ℝ) * (7001 / 1000) * (174 / 125) * (10075 / 10000) := by gcongr
      _ ≤ 9917 / 500 := by norm_num
  have hA3 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 99 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (7001 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 12 / 25) (b := 49 / 100)
      (ℓK := 99) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 20461 / 500)
      (cb := 12287 / 10000) (e := 49 / 100) (j := 7001 / 1000) (d := 343 / 50)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 12 / 25) (qu := 49 / 100) (b := 122831 / 100000)
    (c := 152939 / 10000000) (Gb := 973 / 500) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb3 : (973 / 500) * (7001 / 1000)
      * (1 - (49 / 100 : ℝ)) ^ (-(49 / 100 : ℝ)) * (10075 / 10000) ≤ 19107 / 1000 :=
    calc _ ≤ (973 / 500 : ℝ) * (7001 / 1000) * (174 / 125) * (10075 / 10000) := by gcongr
      _ ≤ 19107 / 1000 := by norm_num
  have hA4 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 98 →
      (⟨63, 103 / 2, 60, 20, 2834⟩ : WinChaos).const E₀ q K ≤ (871 / 125) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 12 / 25) (b := 49 / 100)
      (ℓK := 98) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 20201 / 500)
      (cb := 12289 / 10000) (e := 49 / 100) (j := 871 / 125) (d := 6843 / 1000)
      ⟨63, 103 / 2, 60, 20, 2834⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 12 / 25) (qu := 49 / 100) (b := 5957 / 5000)
    (c := 588533 / 100000000) (Gb := 1921 / 1000) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb4 : (1921 / 1000) * (871 / 125)
      * (1 - (49 / 100 : ℝ)) ^ (-(49 / 100 : ℝ)) * (10075 / 10000) ≤ 18773 / 1000 :=
    calc _ ≤ (1921 / 1000 : ℝ) * (871 / 125) * (174 / 125) * (10075 / 10000) := by gcongr
      _ ≤ 18773 / 1000 := by norm_num
  have hA5 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 74 →
      (⟨51, 87 / 2, 60, 16, 2600⟩ : WinChaos).const E₀ q K ≤ (3213 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 12 / 25) (b := 49 / 100)
      (ℓK := 74) (Ci' := 5977 / 5000) (s' := 729 / 50) (U := 17051 / 500)
      (cb := 6177 / 5000) (e := 49 / 100) (j := 3213 / 500) (d := 3157 / 500)
      ⟨51, 87 / 2, 60, 16, 2600⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_16 h0 h1)
      (uChaosRadS_60_16 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG5 := thetaWindowConstQ_rpow_le_of (ql := 12 / 25) (qu := 49 / 100) (b := 117001 / 100000)
    (c := 409219 / 1000000000) (Gb := 953 / 500) (by norm_num) (by norm_num) 31 uChaosEps_31
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb5 : (953 / 500) * (3213 / 500)
      * (1 - (49 / 100 : ℝ)) ^ (-(49 / 100 : ℝ)) * (10075 / 10000) ≤ 8589 / 500 :=
    calc _ ≤ (953 / 500 : ℝ) * (3213 / 500) * (174 / 125) * (10075 / 10000) := by gcongr
      _ ≤ 8589 / 500 := by norm_num
  have hA6 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 44 →
      (⟨36, 67 / 2, 50, 12, 2298⟩ : WinChaos).const E₀ q K ≤ (5673 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 12 / 25) (b := 49 / 100)
      (ℓK := 44) (Ci' := 12033 / 10000) (s' := 14233 / 1000) (U := 13061 / 500)
      (cb := 12519 / 10000) (e := 49 / 100) (j := 5673 / 1000) (d := 2789 / 500)
      ⟨36, 67 / 2, 50, 12, 2298⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_50_12 h0 h1)
      (uChaosRadS_50_12 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG6 := thetaWindowConstQ_rpow_le_of (ql := 12 / 25) (qu := 49 / 100) (b := 117001 / 100000)
    (c := 409219 / 1000000000) (Gb := 953 / 500) (by norm_num) (by norm_num) 61 uChaosEps_61
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb6 : (953 / 500) * (5673 / 1000)
      * (1 - (49 / 100 : ℝ)) ^ (-(49 / 100 : ℝ)) * (10075 / 10000) ≤ 3033 / 200 :=
    calc _ ≤ (953 / 500 : ℝ) * (5673 / 1000) * (174 / 125) * (10075 / 10000) := by gcongr
      _ ≤ 3033 / 200 := by norm_num
  have hA7 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      (⟨20, 45 / 2, 35, 10, 2000⟩ : WinChaos).const E₀ q K ≤ (47 / 10) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 12 / 25) (b := 49 / 100)
      (ℓK := 8) (Ci' := 12177 / 10000) (s' := 13749 / 1000) (U := 351 / 20)
      (cb := 803 / 625) (e := 49 / 100) (j := 47 / 10) (d := 4611 / 1000)
      ⟨20, 45 / 2, 35, 10, 2000⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_35_10 h0 h1)
      (uChaosRadS_35_10 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG7 := thetaWindowConstQ_rpow_le_of (ql := 12 / 25) (qu := 49 / 100) (b := 117001 / 100000)
    (c := 409219 / 1000000000) (Gb := 953 / 500) (by norm_num) (by norm_num) 97 uChaosEps_97
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb7 : (953 / 500) * (47 / 10)
      * (1 - (49 / 100 : ℝ)) ^ (-(49 / 100 : ℝ)) * (10763 / 10000) ≤ 6711 / 500 :=
    calc _ ≤ (953 / 500 : ℝ) * (47 / 10) * (174 / 125) * (10763 / 10000) := by gcongr
      _ ≤ 6711 / 500 := by norm_num
  exact u_cell_chaos hX hx hΛ (by norm_num) hq1 hq2 (by norm_num) uChaosW_valid_1
    uChaosW_valid_2 uChaosW_valid_3 uChaosW_valid_4 uChaosW_valid_5 uChaosW_valid_6
    uChaosW_valid_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hA1 hA2 hA3 hA4 hA5 hA6 hA7 hG1 hG2 hG3 hG4 hG5 hG6 hG7 hb1 hb2
    hb3 hb4 hb5 hb6 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by interval_decide (trust := kernel))
    (by rw [rpow_eq_exp_mul_log (by norm_num), rpow_eq_exp_mul_log (by norm_num)]
        interval_decide (trust := kernel))

end RMF
