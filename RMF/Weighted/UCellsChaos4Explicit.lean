/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UCellsChaosLeavesExplicit

/-!
# The chaos regime's cells, part 4

`RMF.u_cell_chaos` at the numerals of the cells `q ∈ [0.41, 0.42]` and `[0.42, 0.43]`; their
certificate totals are `22.80` and `23.30` (of `25`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 4000000 in
-- seventeen kernel-checked numerals
/-- **The chaos regime's cell `q ∈ [41 / 100, 21 / 50]`**: for `Λ = log log x ≥ 4000`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (`RMF.u_cell_chaos`; certificate total `22.80`). -/
theorem u_cell_chaos_7 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 4000 ≤ Real.log (Real.log x))
    (hq1 : 41 / 100 ≤ q) (hq2 : q ≤ 21 / 50) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  have hq0 : 0 ≤ q := by linarith
  have ho : (1 - (21 / 50 : ℝ)) ^ (-(21 / 50 : ℝ)) ≤ 629 / 500 :=
    one_sub_rpow_neg_le_of (by norm_num) (by interval_decide (trust := kernel))
  have hA1 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 101 →
      (⟨65, 105 / 2, 60, 20, 2873⟩ : WinChaos).const E₀ q K ≤ (689 / 125) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 41 / 100) (b := 21 / 50)
      (ℓK := 101) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 47021 / 1000)
      (cb := 2457 / 2000) (e := 21 / 50) (j := 5323 / 1000) (d := 689 / 125)
      ⟨65, 105 / 2, 60, 20, 2873⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 41 / 100) (qu := 21 / 50) (b := 182813 / 100000)
    (c := 13803 / 125000) (Gb := 1053 / 500) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb1 : (1053 / 500) * (689 / 125)
      * (1 - (21 / 50 : ℝ)) ^ (-(21 / 50 : ℝ)) * (10075 / 10000) ≤ 14713 / 1000 :=
    calc _ ≤ (1053 / 500 : ℝ) * (689 / 125) * (629 / 500) * (10075 / 10000) := by gcongr
      _ ≤ 14713 / 1000 := by norm_num
  have hA2 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 100 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (1099 / 200) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 41 / 100) (b := 21 / 50)
      (ℓK := 100) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 46431 / 1000)
      (cb := 12287 / 10000) (e := 21 / 50) (j := 2651 / 500) (d := 1099 / 200)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 41 / 100) (qu := 21 / 50) (b := 150849 / 100000)
    (c := 408739 / 10000000) (Gb := 1899 / 1000) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb2 : (1899 / 1000) * (1099 / 200)
      * (1 - (21 / 50 : ℝ)) ^ (-(21 / 50 : ℝ)) * (10075 / 10000) ≤ 6613 / 500 :=
    calc _ ≤ (1899 / 1000 : ℝ) * (1099 / 200) * (629 / 500) * (10075 / 10000) := by gcongr
      _ ≤ 6613 / 500 := by norm_num
  have hA3 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 99 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (5483 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 41 / 100) (b := 21 / 50)
      (ℓK := 99) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 46431 / 1000)
      (cb := 12287 / 10000) (e := 21 / 50) (j := 2651 / 500) (d := 5483 / 1000)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 41 / 100) (qu := 21 / 50) (b := 27873 / 20000)
    (c := 152939 / 10000000) (Gb := 229 / 125) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb3 : (229 / 125) * (5483 / 1000)
      * (1 - (21 / 50 : ℝ)) ^ (-(21 / 50 : ℝ)) * (10075 / 10000) ≤ 3183 / 250 :=
    calc _ ≤ (229 / 125 : ℝ) * (5483 / 1000) * (629 / 500) * (10075 / 10000) := by gcongr
      _ ≤ 3183 / 250 := by norm_num
  have hA4 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 98 →
      (⟨63, 103 / 2, 60, 20, 2834⟩ : WinChaos).const E₀ q K ≤ (2733 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 41 / 100) (b := 21 / 50)
      (ℓK := 98) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 45841 / 1000)
      (cb := 12289 / 10000) (e := 21 / 50) (j := 5281 / 1000) (d := 2733 / 500)
      ⟨63, 103 / 2, 60, 20, 2834⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 41 / 100) (qu := 21 / 50) (b := 67589 / 50000)
    (c := 588533 / 100000000) (Gb := 1809 / 1000) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb4 : (1809 / 1000) * (2733 / 500)
      * (1 - (21 / 50 : ℝ)) ^ (-(21 / 50 : ℝ)) * (10075 / 10000) ≤ 12533 / 1000 :=
    calc _ ≤ (1809 / 1000 : ℝ) * (2733 / 500) * (629 / 500) * (10075 / 10000) := by gcongr
      _ ≤ 12533 / 1000 := by norm_num
  have hA5 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 74 →
      (⟨51, 87 / 2, 60, 16, 2600⟩ : WinChaos).const E₀ q K ≤ (5101 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 41 / 100) (b := 21 / 50)
      (ℓK := 74) (Ci' := 5977 / 5000) (s' := 729 / 50) (U := 38693 / 1000)
      (cb := 6177 / 5000) (e := 21 / 50) (j := 4927 / 1000) (d := 5101 / 1000)
      ⟨51, 87 / 2, 60, 16, 2600⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_16 h0 h1)
      (uChaosRadS_60_16 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG5 := thetaWindowConstQ_rpow_le_of (ql := 41 / 100) (qu := 21 / 50) (b := 132751 / 100000)
    (c := 409219 / 1000000000) (Gb := 359 / 200) (by norm_num) (by norm_num) 31 uChaosEps_31
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb5 : (359 / 200) * (5101 / 1000)
      * (1 - (21 / 50 : ℝ)) ^ (-(21 / 50 : ℝ)) * (10075 / 10000) ≤ 5803 / 500 :=
    calc _ ≤ (359 / 200 : ℝ) * (5101 / 1000) * (629 / 500) * (10075 / 10000) := by gcongr
      _ ≤ 5803 / 500 := by norm_num
  have hA6 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 44 →
      (⟨36, 67 / 2, 50, 12, 2298⟩ : WinChaos).const E₀ q K ≤ (4587 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 41 / 100) (b := 21 / 50)
      (ℓK := 44) (Ci' := 12033 / 10000) (s' := 14233 / 1000) (U := 14819 / 500)
      (cb := 12519 / 10000) (e := 21 / 50) (j := 4427 / 1000) (d := 4587 / 1000)
      ⟨36, 67 / 2, 50, 12, 2298⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_50_12 h0 h1)
      (uChaosRadS_50_12 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG6 := thetaWindowConstQ_rpow_le_of (ql := 41 / 100) (qu := 21 / 50) (b := 132751 / 100000)
    (c := 409219 / 1000000000) (Gb := 359 / 200) (by norm_num) (by norm_num) 61 uChaosEps_61
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb6 : (359 / 200) * (4587 / 1000)
      * (1 - (21 / 50 : ℝ)) ^ (-(21 / 50 : ℝ)) * (10075 / 10000) ≤ 2609 / 250 :=
    calc _ ≤ (359 / 200 : ℝ) * (4587 / 1000) * (629 / 500) * (10075 / 10000) := by gcongr
      _ ≤ 2609 / 250 := by norm_num
  have hA7 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      (⟨20, 45 / 2, 35, 10, 2000⟩ : WinChaos).const E₀ q K ≤ (3907 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 41 / 100) (b := 21 / 50)
      (ℓK := 8) (Ci' := 12177 / 10000) (s' := 13749 / 1000) (U := 2489 / 125)
      (cb := 803 / 625) (e := 21 / 50) (j := 471 / 125) (d := 3907 / 1000)
      ⟨20, 45 / 2, 35, 10, 2000⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_35_10 h0 h1)
      (uChaosRadS_35_10 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG7 := thetaWindowConstQ_rpow_le_of (ql := 41 / 100) (qu := 21 / 50) (b := 132751 / 100000)
    (c := 409219 / 1000000000) (Gb := 359 / 200) (by norm_num) (by norm_num) 97 uChaosEps_97
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb7 : (359 / 200) * (3907 / 1000)
      * (1 - (21 / 50 : ℝ)) ^ (-(21 / 50 : ℝ)) * (10763 / 10000) ≤ 23739 / 2500 :=
    calc _ ≤ (359 / 200 : ℝ) * (3907 / 1000) * (629 / 500) * (10763 / 10000) := by gcongr
      _ ≤ 23739 / 2500 := by norm_num
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
/-- **The chaos regime's cell `q ∈ [21 / 50, 43 / 100]`**: for `Λ = log log x ≥ 4000`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (`RMF.u_cell_chaos`; certificate total `23.30`). -/
theorem u_cell_chaos_8 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 4000 ≤ Real.log (Real.log x))
    (hq1 : 21 / 50 ≤ q) (hq2 : q ≤ 43 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  have hq0 : 0 ≤ q := by linarith
  have ho : (1 - (43 / 100 : ℝ)) ^ (-(43 / 100 : ℝ)) ≤ 51 / 40 :=
    one_sub_rpow_neg_le_of (by norm_num) (by interval_decide (trust := kernel))
  have hA1 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 101 →
      (⟨65, 105 / 2, 60, 20, 2873⟩ : WinChaos).const E₀ q K ≤ (57 / 10) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 21 / 50) (b := 43 / 100)
      (ℓK := 101) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 5778 / 125)
      (cb := 2457 / 2000) (e := 43 / 100) (j := 5539 / 1000) (d := 57 / 10)
      ⟨65, 105 / 2, 60, 20, 2873⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 21 / 50) (qu := 43 / 100) (b := 89857 / 50000)
    (c := 13803 / 125000) (Gb := 2127 / 1000) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb1 : (2127 / 1000) * (57 / 10)
      * (1 - (43 / 100 : ℝ)) ^ (-(43 / 100 : ℝ)) * (10075 / 10000) ≤ 7787 / 500 :=
    calc _ ≤ (2127 / 1000 : ℝ) * (57 / 10) * (51 / 40) * (10075 / 10000) := by gcongr
      _ ≤ 7787 / 500 := by norm_num
  have hA2 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 100 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (2841 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 21 / 50) (b := 43 / 100)
      (ℓK := 100) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 11411 / 250)
      (cb := 12287 / 10000) (e := 43 / 100) (j := 5517 / 1000) (d := 2841 / 500)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 21 / 50) (qu := 43 / 100) (b := 37073 / 25000)
    (c := 408739 / 10000000) (Gb := 1917 / 1000) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb2 : (1917 / 1000) * (2841 / 500)
      * (1 - (43 / 100 : ℝ)) ^ (-(43 / 100 : ℝ)) * (10075 / 10000) ≤ 1749 / 125 :=
    calc _ ≤ (1917 / 1000 : ℝ) * (2841 / 500) * (51 / 40) * (10075 / 10000) := by gcongr
      _ ≤ 1749 / 125 := by norm_num
  have hA3 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 99 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (5669 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 21 / 50) (b := 43 / 100)
      (ℓK := 99) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 11411 / 250)
      (cb := 12287 / 10000) (e := 43 / 100) (j := 5517 / 1000) (d := 5669 / 1000)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 21 / 50) (qu := 43 / 100) (b := 137003 / 100000)
    (c := 152939 / 10000000) (Gb := 1849 / 1000) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb3 : (1849 / 1000) * (5669 / 1000)
      * (1 - (43 / 100 : ℝ)) ^ (-(43 / 100 : ℝ)) * (10075 / 10000) ≤ 2693 / 200 :=
    calc _ ≤ (1849 / 1000 : ℝ) * (5669 / 1000) * (51 / 40) * (10075 / 10000) := by gcongr
      _ ≤ 2693 / 200 := by norm_num
  have hA4 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 98 →
      (⟨63, 103 / 2, 60, 20, 2834⟩ : WinChaos).const E₀ q K ≤ (5651 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 21 / 50) (b := 43 / 100)
      (ℓK := 98) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 5633 / 125)
      (cb := 12289 / 10000) (e := 43 / 100) (j := 2747 / 500) (d := 5651 / 1000)
      ⟨63, 103 / 2, 60, 20, 2834⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 21 / 50) (qu := 43 / 100) (b := 132887 / 100000)
    (c := 588533 / 100000000) (Gb := 73 / 40) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb4 : (73 / 40) * (5651 / 1000)
      * (1 - (43 / 100 : ℝ)) ^ (-(43 / 100 : ℝ)) * (10075 / 10000) ≤ 1656 / 125 :=
    calc _ ≤ (73 / 40 : ℝ) * (5651 / 1000) * (51 / 40) * (10075 / 10000) := by gcongr
      _ ≤ 1656 / 125 := by norm_num
  have hA5 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 74 →
      (⟨51, 87 / 2, 60, 16, 2600⟩ : WinChaos).const E₀ q K ≤ (2633 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 21 / 50) (b := 43 / 100)
      (ℓK := 74) (Ci' := 5977 / 5000) (s' := 729 / 50) (U := 38037 / 1000)
      (cb := 6177 / 5000) (e := 43 / 100) (j := 5117 / 1000) (d := 2633 / 500)
      ⟨51, 87 / 2, 60, 16, 2600⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_16 h0 h1)
      (uChaosRadS_60_16 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG5 := thetaWindowConstQ_rpow_le_of (ql := 21 / 50) (qu := 43 / 100) (b := 130501 / 100000)
    (c := 409219 / 1000000000) (Gb := 453 / 250) (by norm_num) (by norm_num) 31 uChaosEps_31
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb5 : (453 / 250) * (2633 / 500)
      * (1 - (43 / 100 : ℝ)) ^ (-(43 / 100 : ℝ)) * (10075 / 10000) ≤ 6129 / 500 :=
    calc _ ≤ (453 / 250 : ℝ) * (2633 / 500) * (51 / 40) * (10075 / 10000) := by gcongr
      _ ≤ 6129 / 500 := by norm_num
  have hA6 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 44 →
      (⟨36, 67 / 2, 50, 12, 2298⟩ : WinChaos).const E₀ q K ≤ (4723 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 21 / 50) (b := 43 / 100)
      (ℓK := 44) (Ci' := 12033 / 10000) (s' := 14233 / 1000) (U := 3642 / 125)
      (cb := 12519 / 10000) (e := 43 / 100) (j := 4587 / 1000) (d := 4723 / 1000)
      ⟨36, 67 / 2, 50, 12, 2298⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_50_12 h0 h1)
      (uChaosRadS_50_12 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG6 := thetaWindowConstQ_rpow_le_of (ql := 21 / 50) (qu := 43 / 100) (b := 130501 / 100000)
    (c := 409219 / 1000000000) (Gb := 453 / 250) (by norm_num) (by norm_num) 61 uChaosEps_61
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb6 : (453 / 250) * (4723 / 1000)
      * (1 - (43 / 100 : ℝ)) ^ (-(43 / 100 : ℝ)) * (10075 / 10000) ≤ 5497 / 500 :=
    calc _ ≤ (453 / 250 : ℝ) * (4723 / 1000) * (51 / 40) * (10075 / 10000) := by gcongr
      _ ≤ 5497 / 500 := by norm_num
  have hA7 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      (⟨20, 45 / 2, 35, 10, 2000⟩ : WinChaos).const E₀ q K ≤ (2003 / 500) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 21 / 50) (b := 43 / 100)
      (ℓK := 8) (Ci' := 12177 / 10000) (s' := 13749 / 1000) (U := 783 / 40)
      (cb := 803 / 625) (e := 43 / 100) (j := 3889 / 1000) (d := 2003 / 500)
      ⟨20, 45 / 2, 35, 10, 2000⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_35_10 h0 h1)
      (uChaosRadS_35_10 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG7 := thetaWindowConstQ_rpow_le_of (ql := 21 / 50) (qu := 43 / 100) (b := 130501 / 100000)
    (c := 409219 / 1000000000) (Gb := 453 / 250) (by norm_num) (by norm_num) 97 uChaosEps_97
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb7 : (453 / 250) * (2003 / 500)
      * (1 - (43 / 100 : ℝ)) ^ (-(43 / 100 : ℝ)) * (10763 / 10000) ≤ 99613 / 10000 :=
    calc _ ≤ (453 / 250 : ℝ) * (2003 / 500) * (51 / 40) * (10763 / 10000) := by gcongr
      _ ≤ 99613 / 10000 := by norm_num
  exact u_cell_chaos hX hx hΛ (by norm_num) hq1 hq2 (by norm_num) uChaosW_valid_1
    uChaosW_valid_2 uChaosW_valid_3 uChaosW_valid_4 uChaosW_valid_5 uChaosW_valid_6
    uChaosW_valid_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hA1 hA2 hA3 hA4 hA5 hA6 hA7 hG1 hG2 hG3 hG4 hG5 hG6 hG7 hb1 hb2
    hb3 hb4 hb5 hb6 hb7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by interval_decide (trust := kernel))
    (by rw [rpow_eq_exp_mul_log (by norm_num), rpow_eq_exp_mul_log (by norm_num)]
        interval_decide (trust := kernel))

end RMF
