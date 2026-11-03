/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UCellsChaosLeavesExplicit

/-!
# The chaos regime's cells, part 2

`RMF.u_cell_chaos` at the numerals of the cells `q ∈ [0.45, 0.46]` and `[0.46, 0.47]`; their
certificate totals are `24.34` and `24.42` (of `25`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 4000000 in
-- seventeen kernel-checked numerals
/-- **The chaos regime's cell `q ∈ [9 / 20, 23 / 50]`**: for `Λ = log log x ≥ 4000`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (`RMF.u_cell_chaos`; certificate total `24.34`). -/
theorem u_cell_chaos_3 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 4000 ≤ Real.log (Real.log x))
    (hq1 : 9 / 20 ≤ q) (hq2 : q ≤ 23 / 50) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  have hq0 : 0 ≤ q := by linarith
  have ho : (1 - (23 / 50 : ℝ)) ^ (-(23 / 50 : ℝ)) ≤ 1329 / 1000 :=
    one_sub_rpow_neg_le_of (by norm_num) (by interval_decide (trust := kernel))
  have hA1 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 101 →
      (⟨65, 105 / 2, 60, 20, 2873⟩ : WinChaos).const E₀ q K ≤ (3143 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 9 / 20) (b := 23 / 50)
      (ℓK := 101) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 43833 / 1000)
      (cb := 2457 / 2000) (e := 23 / 50) (j := 3121 / 500) (d := 3143 / 500)
      ⟨65, 105 / 2, 60, 20, 2873⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 23 / 50) (b := 170419 / 100000)
    (c := 13803 / 125000) (Gb := 547 / 250) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb1 : (547 / 250) * (3143 / 500)
      * (1 - (23 / 50 : ℝ)) ^ (-(23 / 50 : ℝ)) * (10075 / 10000) ≤ 2302 / 125 :=
    calc _ ≤ (547 / 250 : ℝ) * (3143 / 500) * (1329 / 1000) * (10075 / 10000) := by gcongr
      _ ≤ 2302 / 125 := by norm_num
  have hA2 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 100 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (1567 / 250) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 9 / 20) (b := 23 / 50)
      (ℓK := 100) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 43283 / 1000)
      (cb := 12287 / 10000) (e := 23 / 50) (j := 1243 / 200) (d := 1567 / 250)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 23 / 50) (b := 70311 / 50000)
    (c := 408739 / 10000000) (Gb := 197 / 100) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb2 : (197 / 100) * (1567 / 250)
      * (1 - (23 / 50 : ℝ)) ^ (-(23 / 50 : ℝ)) * (10075 / 10000) ≤ 8267 / 500 :=
    calc _ ≤ (197 / 100 : ℝ) * (1567 / 250) * (1329 / 1000) * (10075 / 10000) := by gcongr
      _ ≤ 8267 / 500 := by norm_num
  have hA3 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 99 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (25 / 4) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 9 / 20) (b := 23 / 50)
      (ℓK := 99) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 43283 / 1000)
      (cb := 12287 / 10000) (e := 23 / 50) (j := 1243 / 200) (d := 25 / 4)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 23 / 50) (b := 129917 / 100000)
    (c := 152939 / 10000000) (Gb := 1899 / 1000) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb3 : (1899 / 1000) * (25 / 4)
      * (1 - (23 / 50 : ℝ)) ^ (-(23 / 50 : ℝ)) * (10075 / 10000) ≤ 3973 / 250 :=
    calc _ ≤ (1899 / 1000 : ℝ) * (25 / 4) * (1329 / 1000) * (10075 / 10000) := by gcongr
      _ ≤ 3973 / 250 := by norm_num
  have hA4 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 98 →
      (⟨63, 103 / 2, 60, 20, 2834⟩ : WinChaos).const E₀ q K ≤ (6231 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 9 / 20) (b := 23 / 50)
      (ℓK := 98) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 42733 / 1000)
      (cb := 12289 / 10000) (e := 23 / 50) (j := 1547 / 250) (d := 6231 / 1000)
      ⟨63, 103 / 2, 60, 20, 2834⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 23 / 50) (b := 63007 / 50000)
    (c := 588533 / 100000000) (Gb := 937 / 500) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb4 : (937 / 500) * (6231 / 1000)
      * (1 - (23 / 50 : ℝ)) ^ (-(23 / 50 : ℝ)) * (10075 / 10000) ≤ 3127 / 200 :=
    calc _ ≤ (937 / 500 : ℝ) * (6231 / 1000) * (1329 / 1000) * (10075 / 10000) := by gcongr
      _ ≤ 3127 / 200 := by norm_num
  have hA5 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 74 →
      (⟨51, 87 / 2, 60, 16, 2600⟩ : WinChaos).const E₀ q K ≤ (2889 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 9 / 20) (b := 23 / 50)
      (ℓK := 74) (Ci' := 5977 / 5000) (s' := 729 / 50) (U := 36069 / 1000)
      (cb := 6177 / 5000) (e := 23 / 50) (j := 1147 / 200) (d := 2889 / 500)
      ⟨51, 87 / 2, 60, 16, 2600⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_16 h0 h1)
      (uChaosRadS_60_16 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG5 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 23 / 50) (b := 123751 / 100000)
    (c := 409219 / 1000000000) (Gb := 93 / 50) (by norm_num) (by norm_num) 31 uChaosEps_31
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb5 : (93 / 50) * (2889 / 500)
      * (1 - (23 / 50 : ℝ)) ^ (-(23 / 50 : ℝ)) * (10075 / 10000) ≤ 1439 / 100 :=
    calc _ ≤ (93 / 50 : ℝ) * (2889 / 500) * (1329 / 1000) * (10075 / 10000) := by gcongr
      _ ≤ 1439 / 100 := by norm_num
  have hA6 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 44 →
      (⟨36, 67 / 2, 50, 12, 2298⟩ : WinChaos).const E₀ q K ≤ (5143 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 9 / 20) (b := 23 / 50)
      (ℓK := 44) (Ci' := 12033 / 10000) (s' := 14233 / 1000) (U := 27629 / 1000)
      (cb := 12519 / 10000) (e := 23 / 50) (j := 5101 / 1000) (d := 5143 / 1000)
      ⟨36, 67 / 2, 50, 12, 2298⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_50_12 h0 h1)
      (uChaosRadS_50_12 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG6 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 23 / 50) (b := 123751 / 100000)
    (c := 409219 / 1000000000) (Gb := 93 / 50) (by norm_num) (by norm_num) 61 uChaosEps_61
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb6 : (93 / 50) * (5143 / 1000)
      * (1 - (23 / 50 : ℝ)) ^ (-(23 / 50 : ℝ)) * (10075 / 10000) ≤ 12809 / 1000 :=
    calc _ ≤ (93 / 50 : ℝ) * (5143 / 1000) * (1329 / 1000) * (10075 / 10000) := by gcongr
      _ ≤ 12809 / 1000 := by norm_num
  have hA7 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      (⟨20, 45 / 2, 35, 10, 2000⟩ : WinChaos).const E₀ q K ≤ (1077 / 250) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 9 / 20) (b := 23 / 50)
      (ℓK := 8) (Ci' := 12177 / 10000) (s' := 13749 / 1000) (U := 9281 / 500)
      (cb := 803 / 625) (e := 23 / 50) (j := 171 / 40) (d := 1077 / 250)
      ⟨20, 45 / 2, 35, 10, 2000⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_35_10 h0 h1)
      (uChaosRadS_35_10 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG7 := thetaWindowConstQ_rpow_le_of (ql := 9 / 20) (qu := 23 / 50) (b := 123751 / 100000)
    (c := 409219 / 1000000000) (Gb := 93 / 50) (by norm_num) (by norm_num) 97 uChaosEps_97
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb7 : (93 / 50) * (1077 / 250)
      * (1 - (23 / 50 : ℝ)) ^ (-(23 / 50 : ℝ)) * (10763 / 10000) ≤ 5731 / 500 :=
    calc _ ≤ (93 / 50 : ℝ) * (1077 / 250) * (1329 / 1000) * (10763 / 10000) := by gcongr
      _ ≤ 5731 / 500 := by norm_num
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
/-- **The chaos regime's cell `q ∈ [23 / 50, 47 / 100]`**: for `Λ = log log x ≥ 4000`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (`RMF.u_cell_chaos`; certificate total `24.42`). -/
theorem u_cell_chaos_4 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 4000 ≤ Real.log (Real.log x))
    (hq1 : 23 / 50 ≤ q) (hq2 : q ≤ 47 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  have hq0 : 0 ≤ q := by linarith
  have ho : (1 - (47 / 100 : ℝ)) ^ (-(47 / 100 : ℝ)) ≤ 1349 / 1000 :=
    one_sub_rpow_neg_le_of (by norm_num) (by interval_decide (trust := kernel))
  have hA1 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 101 →
      (⟨65, 105 / 2, 60, 20, 2873⟩ : WinChaos).const E₀ q K ≤ (1299 / 200) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 23 / 50) (b := 47 / 100)
      (ℓK := 101) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 10759 / 250)
      (cb := 2457 / 2000) (e := 47 / 100) (j := 1299 / 200) (d := 811 / 125)
      ⟨65, 105 / 2, 60, 20, 2873⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 23 / 50) (qu := 47 / 100) (b := 4183 / 2500)
    (c := 13803 / 125000) (Gb := 276 / 125) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb1 : (276 / 125) * (1299 / 200)
      * (1 - (47 / 100 : ℝ)) ^ (-(47 / 100 : ℝ)) * (10075 / 10000) ≤ 4873 / 250 :=
    calc _ ≤ (276 / 125 : ℝ) * (1299 / 200) * (1349 / 1000) * (10075 / 10000) := by gcongr
      _ ≤ 4873 / 250 := by norm_num
  have hA2 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 100 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (647 / 100) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 23 / 50) (b := 47 / 100)
      (ℓK := 100) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 5312 / 125)
      (cb := 12287 / 10000) (e := 47 / 100) (j := 3233 / 500) (d := 647 / 100)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 23 / 50) (qu := 47 / 100) (b := 27613 / 20000)
    (c := 408739 / 10000000) (Gb := 1987 / 1000) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb2 : (1987 / 1000) * (647 / 100)
      * (1 - (47 / 100 : ℝ)) ^ (-(47 / 100 : ℝ)) * (10075 / 10000) ≤ 17473 / 1000 :=
    calc _ ≤ (1987 / 1000 : ℝ) * (647 / 100) * (1349 / 1000) * (10075 / 10000) := by gcongr
      _ ≤ 17473 / 1000 := by norm_num
  have hA3 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 99 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (3233 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 23 / 50) (b := 47 / 100)
      (ℓK := 99) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 5312 / 125)
      (cb := 12287 / 10000) (e := 47 / 100) (j := 3233 / 500) (d := 129 / 20)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 23 / 50) (qu := 47 / 100) (b := 25511 / 20000)
    (c := 152939 / 10000000) (Gb := 383 / 200) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb3 : (383 / 200) * (3233 / 500)
      * (1 - (47 / 100 : ℝ)) ^ (-(47 / 100 : ℝ)) * (10075 / 10000) ≤ 1683 / 100 :=
    calc _ ≤ (383 / 200 : ℝ) * (3233 / 500) * (1349 / 1000) * (10075 / 10000) := by gcongr
      _ ≤ 1683 / 100 := by norm_num
  have hA4 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 98 →
      (⟨63, 103 / 2, 60, 20, 2834⟩ : WinChaos).const E₀ q K ≤ (3219 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 23 / 50) (b := 47 / 100)
      (ℓK := 98) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 10489 / 250)
      (cb := 12289 / 10000) (e := 47 / 100) (j := 3219 / 500) (d := 804 / 125)
      ⟨63, 103 / 2, 60, 20, 2834⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 23 / 50) (qu := 47 / 100) (b := 123723 / 100000)
    (c := 588533 / 100000000) (Gb := 189 / 100) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb4 : (189 / 100) * (3219 / 500)
      * (1 - (47 / 100 : ℝ)) ^ (-(47 / 100 : ℝ)) * (10075 / 10000) ≤ 8269 / 500 :=
    calc _ ≤ (189 / 100 : ℝ) * (3219 / 500) * (1349 / 1000) * (10075 / 10000) := by gcongr
      _ ≤ 8269 / 500 := by norm_num
  have hA5 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 74 →
      (⟨51, 87 / 2, 60, 16, 2600⟩ : WinChaos).const E₀ q K ≤ (1489 / 250) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 23 / 50) (b := 47 / 100)
      (ℓK := 74) (Ci' := 5977 / 5000) (s' := 729 / 50) (U := 17707 / 500)
      (cb := 6177 / 5000) (e := 47 / 100) (j := 1489 / 250) (d := 2977 / 500)
      ⟨51, 87 / 2, 60, 16, 2600⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_16 h0 h1)
      (uChaosRadS_60_16 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG5 := thetaWindowConstQ_rpow_le_of (ql := 23 / 50) (qu := 47 / 100) (b := 121501 / 100000)
    (c := 409219 / 1000000000) (Gb := 15 / 8) (by norm_num) (by norm_num) 31 uChaosEps_31
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb5 : (15 / 8) * (1489 / 250)
      * (1 - (47 / 100 : ℝ)) ^ (-(47 / 100 : ℝ)) * (10075 / 10000) ≤ 7589 / 500 :=
    calc _ ≤ (15 / 8 : ℝ) * (1489 / 250) * (1349 / 1000) * (10075 / 10000) := by gcongr
      _ ≤ 7589 / 500 := by norm_num
  have hA6 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 44 →
      (⟨36, 67 / 2, 50, 12, 2298⟩ : WinChaos).const E₀ q K ≤ (2643 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 23 / 50) (b := 47 / 100)
      (ℓK := 44) (Ci' := 12033 / 10000) (s' := 14233 / 1000) (U := 13563 / 500)
      (cb := 12519 / 10000) (e := 47 / 100) (j := 1057 / 200) (d := 2643 / 500)
      ⟨36, 67 / 2, 50, 12, 2298⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_50_12 h0 h1)
      (uChaosRadS_50_12 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG6 := thetaWindowConstQ_rpow_le_of (ql := 23 / 50) (qu := 47 / 100) (b := 121501 / 100000)
    (c := 409219 / 1000000000) (Gb := 15 / 8) (by norm_num) (by norm_num) 61 uChaosEps_61
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb6 : (15 / 8) * (2643 / 500)
      * (1 - (47 / 100 : ℝ)) ^ (-(47 / 100 : ℝ)) * (10075 / 10000) ≤ 13471 / 1000 :=
    calc _ ≤ (15 / 8 : ℝ) * (2643 / 500) * (1349 / 1000) * (10075 / 10000) := by gcongr
      _ ≤ 13471 / 1000 := by norm_num
  have hA7 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      (⟨20, 45 / 2, 35, 10, 2000⟩ : WinChaos).const E₀ q K ≤ (1103 / 250) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 23 / 50) (b := 47 / 100)
      (ℓK := 8) (Ci' := 12177 / 10000) (s' := 13749 / 1000) (U := 729 / 40)
      (cb := 803 / 625) (e := 47 / 100) (j := 1103 / 250) (d := 4409 / 1000)
      ⟨20, 45 / 2, 35, 10, 2000⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_35_10 h0 h1)
      (uChaosRadS_35_10 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG7 := thetaWindowConstQ_rpow_le_of (ql := 23 / 50) (qu := 47 / 100) (b := 121501 / 100000)
    (c := 409219 / 1000000000) (Gb := 15 / 8) (by norm_num) (by norm_num) 97 uChaosEps_97
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb7 : (15 / 8) * (1103 / 250)
      * (1 - (47 / 100 : ℝ)) ^ (-(47 / 100 : ℝ)) * (10763 / 10000) ≤ 3003 / 250 :=
    calc _ ≤ (15 / 8 : ℝ) * (1103 / 250) * (1349 / 1000) * (10763 / 10000) := by gcongr
      _ ≤ 3003 / 250 := by norm_num
  exact u_cell_chaos hX hx hΛ (by norm_num) hq1 hq2 (by norm_num) uChaosW_valid_1
    uChaosW_valid_2 uChaosW_valid_3 uChaosW_valid_4 uChaosW_valid_5 uChaosW_valid_6
    uChaosW_valid_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hA1 hA2 hA3 hA4 hA5 hA6 hA7 hG1 hG2 hG3 hG4 hG5 hG6 hG7 hb1 hb2
    hb3 hb4 hb5 hb6 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by interval_decide (trust := kernel))
    (by rw [rpow_eq_exp_mul_log (by norm_num), rpow_eq_exp_mul_log (by norm_num)]
        interval_decide (trust := kernel))

end RMF
