/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UChaosCellExplicit

/-!
# The chaos regime's certificate: the shared leaves

Numerals shared by the cells of `RMF/Weighted/UCellsChaos*Explicit.lean`: the windows' parameters
(one per group of `RMF.u_cell_chaos`) and their validity, the chaos constant's leaves at their
`(T, κ)`, `e^{-k}` at the groups' first windows, and the windows' constants from rational bounds
(`RMF.thetaWindowConstQ_rpow_le_of`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

/-- A window's chaos parameters are valid from their numerals (`√N ≤ r`). -/
lemma winChaos_valid_of {A lam Tr kap r : ℝ} {N : ℕ} (hTr : 4 < Tr) (hkap : 1 ≤ kap)
    (hA : 20 ≤ A) (hlam : 1 ≤ lam) (hN : 2000 ≤ N) (hr : 0 ≤ r) (hsq : (N : ℝ) ≤ r ^ 2)
    (hroom : A / 4 + 3 * r / 4 + 1 ≤ 1 / 50 * N) : (⟨A, lam, Tr, kap, N⟩ : WinChaos).Valid where
  Tr := hTr
  kap := hkap
  A := hA
  lam := hlam
  N := hN
  room := by
    have hs : Real.sqrt (N : ℝ) ≤ r := by
      rw [show r = Real.sqrt (r ^ 2) from (Real.sqrt_sq hr).symm]
      exact Real.sqrt_le_sqrt hsq
    change A / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ 1 / 50 * N
    linarith

/-- **A window's constant at `log y ≥ 22000` from rational bounds**: with `e^{-k} ≤ ε`, `b` above
`2(1 - q_l)` times `RMF.thetaWindowExp` at `ε`, and `c ≥ 9.0028/22000 + 9.0028ε/(3/2)`,
`G_k(q_l)^{q_u} ≤ e^{q_u log((4/3)W(b)e^c)}` (`W = RMF.taylorWindowW`, written out). -/
lemma thetaWindowConstQ_rpow_le_of {ql qu ε b c Gb : ℝ} (hql1 : ql ≤ 1) (hqu : 0 ≤ qu) (k : ℕ)
    (hε : Real.exp (-(k : ℝ)) ≤ ε)
    (hb : 2 * (1 - ql) * ((3 / 2 + ε / 100) ^ 2 / 2 + 15.003 * (3 / 2 * ε + ε ^ 2 / 100)
      + 34 * ε ^ 2) ≤ b)
    (hc : 9.0028 / 22000 + 9.0028 * ε / (3 / 2) ≤ c)
    (hG : Real.exp (qu * Real.log (4 / 3 * ((Real.exp 1 - 1) + b * (1 - Real.exp (-1))
      + (Real.exp b - 1 - b) * (1 - Real.exp (-3)) * (1 / 3)) * Real.exp c)) ≤ Gb) :
    ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql k y ^ qu ≤ Gb := by
  intro y hy
  have hw : thetaWindowExp (3 / 2) k
      ≤ (3 / 2 + ε / 100) ^ 2 / 2 + 15.003 * (3 / 2 * ε + ε ^ 2 / 100) + 34 * ε ^ 2 := by
    unfold thetaWindowExp
    gcongr
  have hb0 : 0 ≤ 2 * (1 - ql) * thetaWindowExp (3 / 2) k :=
    mul_nonneg (by linarith) (thetaWindowExp_nonneg (by norm_num) k)
  have hbb : 2 * (1 - ql) * thetaWindowExp (3 / 2) k ≤ b :=
    le_trans (mul_le_mul_of_nonneg_left hw (by linarith)) hb
  have hW := taylorWindowW_mono hbb
  have hWb0 : 0 ≤ taylorWindowW b := le_trans (taylorWindowW_nonneg hb0) hW
  have e1 : (Real.exp 1)⁻¹ = Real.exp (-1) := (Real.exp_neg 1).symm
  have e3 : (Real.exp 1)⁻¹ ^ 3 = Real.exp (-3) := by
    rw [e1, ← Real.exp_nat_mul]
    norm_num
  have hWb : taylorWindowW b = (Real.exp 1 - 1) + b * (1 - Real.exp (-1))
      + (Real.exp b - 1 - b) * (1 - Real.exp (-3)) * (1 / 3) := by
    unfold taylorWindowW
    rw [e3, e1]
    ring
  have hl : 9.0028 / Real.log y ≤ 9.0028 / 22000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hy
  have hk : 9.0028 * Real.exp (-(k : ℝ)) / (3 / 2) ≤ 9.0028 * ε / (3 / 2) := by gcongr
  have h1 : thetaWindowConstQ (3 / 2) ql k y ≤ 4 / 3 * taylorWindowW b * Real.exp c := by
    unfold thetaWindowConstQ
    rw [show (2 : ℝ) / (3 / 2) = 4 / 3 by norm_num]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hW (by norm_num))
      (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (mul_nonneg (by norm_num) hWb0)
  have h0 : 0 ≤ thetaWindowConstQ (3 / 2) ql k y := thetaWindowConstQ_nonneg (by norm_num) hql1 k y
  refine le_trans (Real.rpow_le_rpow h0 h1 hqu) (le_trans (rpow_le_exp_mul_log
    (mul_nonneg (mul_nonneg (by norm_num) hWb0) (Real.exp_pos _).le) qu) ?_)
  rw [hWb]
  exact hG

/-- `(1 - q)^{-q}` from its exponential form. -/
lemma one_sub_rpow_neg_le_of {q o : ℝ} (hq : q < 1) (h : Real.exp (-q * Real.log (1 - q)) ≤ o) :
    (1 - q) ^ (-q) ≤ o := by
  rw [rpow_eq_exp_mul_log (by linarith)]
  exact h

lemma uChaosRadC_35_10 {E₀ : ℝ} (h0 : 0 ≤ E₀) (h1 : E₀ ≤ 1 / 33680) :
    radAveragedConst E₀ (11 / 20) 35 10 ≤ 12177 / 10000 :=
  le_trans (radAveragedConst_le_of h0 h1 (by norm_num) (by norm_num)) (by norm_num)

lemma uChaosRadS_35_10 {E₀ : ℝ} (h0 : 0 ≤ E₀) (h1 : E₀ ≤ 1 / 33680) :
    radAveragedShift E₀ (11 / 20) 35 10 ≤ 13749 / 1000 := by
  have hk : Real.log 10 ≤ 288 / 125 := by interval_decide (trust := kernel)
  have hkt : Real.log (116341 / 100000 * 35) ≤ 3709 / 1000 := by interval_decide (trust := kernel)
  exact le_trans (radAveragedShift_le_of h0 h1 (by norm_num) hk hkt) (by norm_num)

lemma uChaosRadC_50_12 {E₀ : ℝ} (h0 : 0 ≤ E₀) (h1 : E₀ ≤ 1 / 33680) :
    radAveragedConst E₀ (11 / 20) 50 12 ≤ 12033 / 10000 :=
  le_trans (radAveragedConst_le_of h0 h1 (by norm_num) (by norm_num)) (by norm_num)

lemma uChaosRadS_50_12 {E₀ : ℝ} (h0 : 0 ≤ E₀) (h1 : E₀ ≤ 1 / 33680) :
    radAveragedShift E₀ (11 / 20) 50 12 ≤ 14233 / 1000 := by
  have hk : Real.log 12 ≤ 2487 / 1000 := by interval_decide (trust := kernel)
  have hkt : Real.log (116341 / 100000 * 50) ≤ 2033 / 500 := by interval_decide (trust := kernel)
  exact le_trans (radAveragedShift_le_of h0 h1 (by norm_num) hk hkt) (by norm_num)

lemma uChaosRadC_60_16 {E₀ : ℝ} (h0 : 0 ≤ E₀) (h1 : E₀ ≤ 1 / 33680) :
    radAveragedConst E₀ (11 / 20) 60 16 ≤ 5977 / 5000 :=
  le_trans (radAveragedConst_le_of h0 h1 (by norm_num) (by norm_num)) (by norm_num)

lemma uChaosRadS_60_16 {E₀ : ℝ} (h0 : 0 ≤ E₀) (h1 : E₀ ≤ 1 / 33680) :
    radAveragedShift E₀ (11 / 20) 60 16 ≤ 729 / 50 := by
  have hk : Real.log 16 ≤ 1387 / 500 := by interval_decide (trust := kernel)
  have hkt : Real.log (116341 / 100000 * 60) ≤ 531 / 125 := by interval_decide (trust := kernel)
  exact le_trans (radAveragedShift_le_of h0 h1 (by norm_num) hk hkt) (by norm_num)

lemma uChaosRadC_60_20 {E₀ : ℝ} (h0 : 0 ≤ E₀) (h1 : E₀ ≤ 1 / 33680) :
    radAveragedConst E₀ (11 / 20) 60 20 ≤ 11933 / 10000 :=
  le_trans (radAveragedConst_le_of h0 h1 (by norm_num) (by norm_num)) (by norm_num)

lemma uChaosRadS_60_20 {E₀ : ℝ} (h0 : 0 ≤ E₀) (h1 : E₀ ≤ 1 / 33680) :
    radAveragedShift E₀ (11 / 20) 60 20 ≤ 1837 / 125 := by
  have hk : Real.log 20 ≤ 1499 / 500 := by interval_decide (trust := kernel)
  have hkt : Real.log (116341 / 100000 * 60) ≤ 531 / 125 := by interval_decide (trust := kernel)
  exact le_trans (radAveragedShift_le_of h0 h1 (by norm_num) hk hkt) (by norm_num)

lemma uChaosEps_4 : Real.exp (-((4 : ℕ) : ℝ)) ≤ 1833 / 100000 := by
  simp only [Nat.cast_ofNat]
  interval_decide (trust := kernel)

lemma uChaosEps_5 : Real.exp (-((5 : ℕ) : ℝ)) ≤ 3371 / 500000 := by
  simp only [Nat.cast_ofNat]
  interval_decide (trust := kernel)

lemma uChaosEps_6 : Real.exp (-((6 : ℕ) : ℝ)) ≤ 31 / 12500 := by
  simp only [Nat.cast_ofNat]
  interval_decide (trust := kernel)

lemma uChaosEps_7 : Real.exp (-((7 : ℕ) : ℝ)) ≤ 2281 / 2500000 := by
  simp only [Nat.cast_ofNat]
  interval_decide (trust := kernel)

lemma uChaosEps_31 : Real.exp (-((31 : ℕ) : ℝ)) ≤ 1 / 1000000000000 := by
  simp only [Nat.cast_ofNat]
  interval_decide (trust := kernel)

lemma uChaosEps_61 : Real.exp (-((61 : ℕ) : ℝ)) ≤ 1 / 1000000000000 := by
  simp only [Nat.cast_ofNat]
  interval_decide (trust := kernel)

lemma uChaosEps_97 : Real.exp (-((97 : ℕ) : ℝ)) ≤ 1 / 1000000000000 := by
  simp only [Nat.cast_ofNat]
  interval_decide (trust := kernel)

/-- The chaos regime's windows of group 1: `A = 65`, `λ = 105 / 2`, `T = 60`, `κ = 20`,
`N = 2873`. -/
lemma uChaosW_valid_1 : (⟨65, 105 / 2, 60, 20, 2873⟩ : WinChaos).Valid :=
  winChaos_valid_of (r := 5361 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The chaos regime's windows of group 2: `A = 64`, `λ = 52`, `T = 60`, `κ = 20`,
`N = 2854`. -/
lemma uChaosW_valid_2 : (⟨64, 52, 60, 20, 2854⟩ : WinChaos).Valid :=
  winChaos_valid_of (r := 5343 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The chaos regime's windows of group 3: `A = 64`, `λ = 52`, `T = 60`, `κ = 20`,
`N = 2854`. -/
lemma uChaosW_valid_3 : (⟨64, 52, 60, 20, 2854⟩ : WinChaos).Valid :=
  winChaos_valid_of (r := 5343 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The chaos regime's windows of group 4: `A = 63`, `λ = 103 / 2`, `T = 60`, `κ = 20`,
`N = 2834`. -/
lemma uChaosW_valid_4 : (⟨63, 103 / 2, 60, 20, 2834⟩ : WinChaos).Valid :=
  winChaos_valid_of (r := 1331 / 25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The chaos regime's windows of group 5: `A = 51`, `λ = 87 / 2`, `T = 60`, `κ = 16`,
`N = 2600`. -/
lemma uChaosW_valid_5 : (⟨51, 87 / 2, 60, 16, 2600⟩ : WinChaos).Valid :=
  winChaos_valid_of (r := 51) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The chaos regime's windows of group 6: `A = 36`, `λ = 67 / 2`, `T = 50`, `κ = 12`,
`N = 2298`. -/
lemma uChaosW_valid_6 : (⟨36, 67 / 2, 50, 12, 2298⟩ : WinChaos).Valid :=
  winChaos_valid_of (r := 2397 / 50) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The chaos regime's windows of group 7: `A = 20`, `λ = 45 / 2`, `T = 35`, `κ = 10`,
`N = 2000`. -/
lemma uChaosW_valid_7 : (⟨20, 45 / 2, 35, 10, 2000⟩ : WinChaos).Valid :=
  winChaos_valid_of (r := 4473 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end RMF
