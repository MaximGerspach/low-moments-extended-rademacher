/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UCellsChaosLeavesExplicit

/-!
# The chaos regime's cells, part 1

`RMF.u_cell_chaos` at the numerals of the cells `q ∈ [0.43, 0.44]` and `[0.44, 0.45]`; their
certificate totals are `23.75` and `24.10` (of `25`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 4000000 in
-- seventeen kernel-checked numerals
/-- **The chaos regime's cell `q ∈ [43 / 100, 11 / 25]`**: for `Λ = log log x ≥ 4000`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (`RMF.u_cell_chaos`; certificate total `23.75`). -/
theorem u_cell_chaos_1 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 4000 ≤ Real.log (Real.log x))
    (hq1 : 43 / 100 ≤ q) (hq2 : q ≤ 11 / 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  have hq0 : 0 ≤ q := by linarith
  have ho : (1 - (11 / 25 : ℝ)) ^ (-(11 / 25 : ℝ)) ≤ 323 / 250 :=
    one_sub_rpow_neg_le_of (by norm_num) (by interval_decide (trust := kernel))
  have hA1 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 101 →
      (⟨65, 105 / 2, 60, 20, 2873⟩ : WinChaos).const E₀ q K ≤ (5891 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 43 / 100) (b := 11 / 25)
      (ℓK := 101) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 45427 / 1000)
      (cb := 2457 / 2000) (e := 11 / 25) (j := 1441 / 250) (d := 5891 / 1000)
      ⟨65, 105 / 2, 60, 20, 2873⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 11 / 25) (b := 22077 / 12500)
    (c := 13803 / 125000) (Gb := 537 / 250) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb1 : (537 / 250) * (5891 / 1000)
      * (1 - (11 / 25 : ℝ)) ^ (-(11 / 25 : ℝ)) * (10075 / 10000) ≤ 2059 / 125 :=
    calc _ ≤ (537 / 250 : ℝ) * (5891 / 1000) * (323 / 250) * (10075 / 10000) := by gcongr
      _ ≤ 2059 / 125 := by norm_num
  have hA2 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 100 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (2937 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 43 / 100) (b := 11 / 25)
      (ℓK := 100) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 44857 / 1000)
      (cb := 12287 / 10000) (e := 11 / 25) (j := 287 / 50) (d := 2937 / 500)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 11 / 25) (b := 18217 / 12500)
    (c := 408739 / 10000000) (Gb := 387 / 200) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb2 : (387 / 200) * (2937 / 500)
      * (1 - (11 / 25 : ℝ)) ^ (-(11 / 25 : ℝ)) * (10075 / 10000) ≤ 3699 / 250 :=
    calc _ ≤ (387 / 200 : ℝ) * (2937 / 500) * (323 / 250) * (10075 / 10000) := by gcongr
      _ ≤ 3699 / 250 := by norm_num
  have hA3 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 99 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (5859 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 43 / 100) (b := 11 / 25)
      (ℓK := 99) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 44857 / 1000)
      (cb := 12287 / 10000) (e := 11 / 25) (j := 287 / 50) (d := 5859 / 1000)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 11 / 25) (b := 134641 / 100000)
    (c := 152939 / 10000000) (Gb := 933 / 500) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb3 : (933 / 500) * (5859 / 1000)
      * (1 - (11 / 25 : ℝ)) ^ (-(11 / 25 : ℝ)) * (10075 / 10000) ≤ 1779 / 125 :=
    calc _ ≤ (933 / 500 : ℝ) * (5859 / 1000) * (323 / 250) * (10075 / 10000) := by gcongr
      _ ≤ 1779 / 125 := by norm_num
  have hA4 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 98 →
      (⟨63, 103 / 2, 60, 20, 2834⟩ : WinChaos).const E₀ q K ≤ (5841 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 43 / 100) (b := 11 / 25)
      (ℓK := 98) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 44287 / 1000)
      (cb := 12289 / 10000) (e := 11 / 25) (j := 1429 / 250) (d := 5841 / 1000)
      ⟨63, 103 / 2, 60, 20, 2834⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 11 / 25) (b := 32649 / 25000)
    (c := 588533 / 100000000) (Gb := 921 / 500) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb4 : (921 / 500) * (5841 / 1000)
      * (1 - (11 / 25 : ℝ)) ^ (-(11 / 25 : ℝ)) * (10075 / 10000) ≤ 7003 / 500 :=
    calc _ ≤ (921 / 500 : ℝ) * (5841 / 1000) * (323 / 250) * (10075 / 10000) := by gcongr
      _ ≤ 7003 / 500 := by norm_num
  have hA5 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 74 →
      (⟨51, 87 / 2, 60, 16, 2600⟩ : WinChaos).const E₀ q K ≤ (2717 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 43 / 100) (b := 11 / 25)
      (ℓK := 74) (Ci' := 5977 / 5000) (s' := 729 / 50) (U := 37381 / 1000)
      (cb := 6177 / 5000) (e := 11 / 25) (j := 1063 / 200) (d := 2717 / 500)
      ⟨51, 87 / 2, 60, 16, 2600⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_16 h0 h1)
      (uChaosRadS_60_16 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG5 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 11 / 25) (b := 128251 / 100000)
    (c := 409219 / 1000000000) (Gb := 457 / 250) (by norm_num) (by norm_num) 31 uChaosEps_31
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb5 : (457 / 250) * (2717 / 500)
      * (1 - (11 / 25 : ℝ)) ^ (-(11 / 25 : ℝ)) * (10075 / 10000) ≤ 12931 / 1000 :=
    calc _ ≤ (457 / 250 : ℝ) * (2717 / 500) * (323 / 250) * (10075 / 10000) := by gcongr
      _ ≤ 12931 / 1000 := by norm_num
  have hA6 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 44 →
      (⟨36, 67 / 2, 50, 12, 2298⟩ : WinChaos).const E₀ q K ≤ (4861 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 43 / 100) (b := 11 / 25)
      (ℓK := 44) (Ci' := 12033 / 10000) (s' := 14233 / 1000) (U := 28633 / 1000)
      (cb := 12519 / 10000) (e := 11 / 25) (j := 594 / 125) (d := 4861 / 1000)
      ⟨36, 67 / 2, 50, 12, 2298⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_50_12 h0 h1)
      (uChaosRadS_50_12 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG6 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 11 / 25) (b := 128251 / 100000)
    (c := 409219 / 1000000000) (Gb := 457 / 250) (by norm_num) (by norm_num) 61 uChaosEps_61
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb6 : (457 / 250) * (4861 / 1000)
      * (1 - (11 / 25 : ℝ)) ^ (-(11 / 25 : ℝ)) * (10075 / 10000) ≤ 11567 / 1000 :=
    calc _ ≤ (457 / 250 : ℝ) * (4861 / 1000) * (323 / 250) * (10075 / 10000) := by gcongr
      _ ≤ 11567 / 1000 := by norm_num
  have hA7 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      (⟨20, 45 / 2, 35, 10, 2000⟩ : WinChaos).const E₀ q K ≤ (2053 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 43 / 100) (b := 11 / 25)
      (ℓK := 8) (Ci' := 12177 / 10000) (s' := 13749 / 1000) (U := 19237 / 1000)
      (cb := 803 / 625) (e := 11 / 25) (j := 2007 / 500) (d := 2053 / 500)
      ⟨20, 45 / 2, 35, 10, 2000⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_35_10 h0 h1)
      (uChaosRadS_35_10 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG7 := thetaWindowConstQ_rpow_le_of (ql := 43 / 100) (qu := 11 / 25) (b := 128251 / 100000)
    (c := 409219 / 1000000000) (Gb := 457 / 250) (by norm_num) (by norm_num) 97 uChaosEps_97
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb7 : (457 / 250) * (2053 / 500)
      * (1 - (11 / 25 : ℝ)) ^ (-(11 / 25 : ℝ)) * (10763 / 10000) ≤ 5219 / 500 :=
    calc _ ≤ (457 / 250 : ℝ) * (2053 / 500) * (323 / 250) * (10763 / 10000) := by gcongr
      _ ≤ 5219 / 500 := by norm_num
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
/-- **The chaos regime's cell `q ∈ [11 / 25, 9 / 20]`**: for `Λ = log log x ≥ 4000`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (`RMF.u_cell_chaos`; certificate total `24.10`). -/
theorem u_cell_chaos_2 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 4000 ≤ Real.log (Real.log x))
    (hq1 : 11 / 25 ≤ q) (hq2 : q ≤ 9 / 20) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  have hq0 : 0 ≤ q := by linarith
  have ho : (1 - (9 / 20 : ℝ)) ^ (-(9 / 20 : ℝ)) ≤ 131 / 100 :=
    one_sub_rpow_neg_le_of (by norm_num) (by interval_decide (trust := kernel))
  have hA1 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 101 →
      (⟨65, 105 / 2, 60, 20, 2873⟩ : WinChaos).const E₀ q K ≤ (6087 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 11 / 25) (b := 9 / 20)
      (ℓK := 101) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 4463 / 100)
      (cb := 2457 / 2000) (e := 9 / 20) (j := 2999 / 500) (d := 6087 / 1000)
      ⟨65, 105 / 2, 60, 20, 2873⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 11 / 25) (qu := 9 / 20) (b := 173517 / 100000)
    (c := 13803 / 125000) (Gb := 271 / 125) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb1 : (271 / 125) * (6087 / 1000)
      * (1 - (9 / 20 : ℝ)) ^ (-(9 / 20 : ℝ)) * (10075 / 10000) ≤ 8709 / 500 :=
    calc _ ≤ (271 / 125 : ℝ) * (6087 / 1000) * (131 / 100) * (10075 / 10000) := by gcongr
      _ ≤ 8709 / 500 := by norm_num
  have hA2 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 100 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (6069 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 11 / 25) (b := 9 / 20)
      (ℓK := 100) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 4407 / 100)
      (cb := 12287 / 10000) (e := 9 / 20) (j := 5973 / 1000) (d := 6069 / 1000)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 11 / 25) (qu := 9 / 20) (b := 143179 / 100000)
    (c := 408739 / 10000000) (Gb := 244 / 125) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb2 : (244 / 125) * (6069 / 1000)
      * (1 - (9 / 20 : ℝ)) ^ (-(9 / 20 : ℝ)) * (10075 / 10000) ≤ 3909 / 250 :=
    calc _ ≤ (244 / 125 : ℝ) * (6069 / 1000) * (131 / 100) * (10075 / 10000) := by gcongr
      _ ≤ 3909 / 250 := by norm_num
  have hA3 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 99 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (6053 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 11 / 25) (b := 9 / 20)
      (ℓK := 99) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 4407 / 100)
      (cb := 12287 / 10000) (e := 9 / 20) (j := 5973 / 1000) (d := 6053 / 1000)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 11 / 25) (qu := 9 / 20) (b := 132279 / 100000)
    (c := 152939 / 10000000) (Gb := 1883 / 1000) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb3 : (1883 / 1000) * (6053 / 1000)
      * (1 - (9 / 20 : ℝ)) ^ (-(9 / 20 : ℝ)) * (10075 / 10000) ≤ 3761 / 250 :=
    calc _ ≤ (1883 / 1000 : ℝ) * (6053 / 1000) * (131 / 100) * (10075 / 10000) := by gcongr
      _ ≤ 3761 / 250 := by norm_num
  have hA4 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 98 →
      (⟨63, 103 / 2, 60, 20, 2834⟩ : WinChaos).const E₀ q K ≤ (3017 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 11 / 25) (b := 9 / 20)
      (ℓK := 98) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 4351 / 100)
      (cb := 12289 / 10000) (e := 9 / 20) (j := 5947 / 1000) (d := 3017 / 500)
      ⟨63, 103 / 2, 60, 20, 2834⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 11 / 25) (qu := 9 / 20) (b := 25661 / 20000)
    (c := 588533 / 100000000) (Gb := 929 / 500) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb4 : (929 / 500) * (3017 / 500)
      * (1 - (9 / 20 : ℝ)) ^ (-(9 / 20 : ℝ)) * (10075 / 10000) ≤ 14797 / 1000 :=
    calc _ ≤ (929 / 500 : ℝ) * (3017 / 500) * (131 / 100) * (10075 / 10000) := by gcongr
      _ ≤ 14797 / 1000 := by norm_num
  have hA5 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 74 →
      (⟨51, 87 / 2, 60, 16, 2600⟩ : WinChaos).const E₀ q K ≤ (1121 / 200) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 11 / 25) (b := 9 / 20)
      (ℓK := 74) (Ci' := 5977 / 5000) (s' := 729 / 50) (U := 1469 / 40)
      (cb := 6177 / 5000) (e := 9 / 20) (j := 5521 / 1000) (d := 1121 / 200)
      ⟨51, 87 / 2, 60, 16, 2600⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_16 h0 h1)
      (uChaosRadS_60_16 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG5 := thetaWindowConstQ_rpow_le_of (ql := 11 / 25) (qu := 9 / 20) (b := 126001 / 100000)
    (c := 409219 / 1000000000) (Gb := 461 / 250) (by norm_num) (by norm_num) 31 uChaosEps_31
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb5 : (461 / 250) * (1121 / 200)
      * (1 - (9 / 20 : ℝ)) ^ (-(9 / 20 : ℝ)) * (10075 / 10000) ≤ 6821 / 500 :=
    calc _ ≤ (461 / 250 : ℝ) * (1121 / 200) * (131 / 100) * (10075 / 10000) := by gcongr
      _ ≤ 6821 / 500 := by norm_num
  have hA6 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 44 →
      (⟨36, 67 / 2, 50, 12, 2298⟩ : WinChaos).const E₀ q K ≤ (5001 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 11 / 25) (b := 9 / 20)
      (ℓK := 44) (Ci' := 12033 / 10000) (s' := 14233 / 1000) (U := 28131 / 1000)
      (cb := 12519 / 10000) (e := 9 / 20) (j := 1231 / 250) (d := 5001 / 1000)
      ⟨36, 67 / 2, 50, 12, 2298⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_50_12 h0 h1)
      (uChaosRadS_50_12 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG6 := thetaWindowConstQ_rpow_le_of (ql := 11 / 25) (qu := 9 / 20) (b := 126001 / 100000)
    (c := 409219 / 1000000000) (Gb := 461 / 250) (by norm_num) (by norm_num) 61 uChaosEps_61
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb6 : (461 / 250) * (5001 / 1000)
      * (1 - (9 / 20 : ℝ)) ^ (-(9 / 20 : ℝ)) * (10075 / 10000) ≤ 3043 / 250 :=
    calc _ ≤ (461 / 250 : ℝ) * (5001 / 1000) * (131 / 100) * (10075 / 10000) := by gcongr
      _ ≤ 3043 / 250 := by norm_num
  have hA7 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      (⟨20, 45 / 2, 35, 10, 2000⟩ : WinChaos).const E₀ q K ≤ (4207 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 11 / 25) (b := 9 / 20)
      (ℓK := 8) (Ci' := 12177 / 10000) (s' := 13749 / 1000) (U := 189 / 10)
      (cb := 803 / 625) (e := 9 / 20) (j := 2071 / 500) (d := 4207 / 1000)
      ⟨20, 45 / 2, 35, 10, 2000⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_35_10 h0 h1)
      (uChaosRadS_35_10 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG7 := thetaWindowConstQ_rpow_le_of (ql := 11 / 25) (qu := 9 / 20) (b := 126001 / 100000)
    (c := 409219 / 1000000000) (Gb := 461 / 250) (by norm_num) (by norm_num) 97 uChaosEps_97
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb7 : (461 / 250) * (4207 / 1000)
      * (1 - (9 / 20 : ℝ)) ^ (-(9 / 20 : ℝ)) * (10763 / 10000) ≤ 10939 / 1000 :=
    calc _ ≤ (461 / 250 : ℝ) * (4207 / 1000) * (131 / 100) * (10763 / 10000) := by gcongr
      _ ≤ 10939 / 1000 := by norm_num
  exact u_cell_chaos hX hx hΛ (by norm_num) hq1 hq2 (by norm_num) uChaosW_valid_1
    uChaosW_valid_2 uChaosW_valid_3 uChaosW_valid_4 uChaosW_valid_5 uChaosW_valid_6
    uChaosW_valid_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hA1 hA2 hA3 hA4 hA5 hA6 hA7 hG1 hG2 hG3 hG4 hG5 hG6 hG7 hb1 hb2
    hb3 hb4 hb5 hb6 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by interval_decide (trust := kernel))
    (by rw [rpow_eq_exp_mul_log (by norm_num), rpow_eq_exp_mul_log (by norm_num)]
        interval_decide (trust := kernel))

end RMF
