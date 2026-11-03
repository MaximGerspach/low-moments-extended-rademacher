/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.SubtractedBelowHalf.Basic

/-!
# The subtracted term below `½`: the cell near `½`

`RMF.z_half_core` at the chaos regime's window parameters with their constants at `q ∈ [0.49, ½]`
(`RMF.z_half_numerals`, the numerals of `RMF.u_half_numerals`), the unbounded cell in
`w = (1 - 2q)Λ` (`RMF.z_cell_half_large`) and its two instances: `w ≥ 23/2` with `K = 215`
(`RMF.z_cell_half_top`) and `w ≥ 120` with `K = 40` (`RMF.z_cell_half_anchor`, the descent's anchor
at `q = 0.49`, where `w = Λ/50 ≥ 120`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 4000000 in
-- the windows' numerals, each kernel-checked
/-- **`RMF.z_half_core` at the windows' numerals**: the chaos regime's window parameters with
their constants at `q ∈ [0.49, ½]`, as in `RMF.u_half_numerals`. -/
theorem z_half_numerals {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q ql a₁ wl Vb Et Hb Tb E0b K : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hql : 49 / 100 ≤ ql) (hqlq : ql ≤ q) (hq : q < 1 / 2)
    (hwl0 : 0 < wl) (hwl : wl ≤ (1 - 2 * q) * Real.log (Real.log x)) (hwl1 : 1 / ql - 1 ≤ wl)
    (ha₁ : q * (1 - 2 * q) ≤ a₁) (ha₁8 : a₁ ≤ 1 / 8)
    (hEt : Et ≤ Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) / 4)))
    (hVb : (Real.log (Real.log x))⁻¹ + (1 - 2 * q) ≤ Vb)
    (hHb : ∑ g ∈ Finset.range 8, halfRho (g + 1)
        * ((1 + (1 - 2 * q) * Real.log (Real.log x))
          * ((Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigLo g))
            - Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigHi (g + 1))))
            / (q * ((1 - 2 * q) * Real.log (Real.log x))))) ≤ Hb)
    (hTb : (1 + (1 - 2 * q) * Real.log (Real.log x))
        * Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigLo 8)) ≤ Tb)
    (hE0 : Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigLo 0)) ≤ E0b)
    (hfin : (1 + wl) * Real.exp (-(ql * wl))
        * (Real.exp (1 / 2 * Real.log 51) * Real.exp ((a₁ - 1 / 4) * Real.log 6000))
      + Vb * Real.exp (3 / 4 * Real.log 880)
      + (1 / ql + 1 / (ql * wl) + Vb * (1 / 2 + a₁ / 10))
        * ((23623 / 1000) - ((23623 / 1000) - (21143 / 1000)) * Real.exp (-(5 * a₁))
          - ((21143 / 1000) - (10187 / 500)) * Real.exp (-(6 * a₁))
          - ((10187 / 500) - (2001 / 100)) * Real.exp (-(7 * a₁))
          - ((2001 / 100) - (18281 / 1000)) * Real.exp (-(31 * a₁))
          - ((18281 / 1000) - (3219 / 200)) * Real.exp (-(61 * a₁))
          - ((3219 / 200) - (14193 / 1000)) * Real.exp (-(97 * a₁))
          - (14193 / 1000) * Et)
      + (13187 / 1000)
        * (Hb
          + Vb * (1 / 2 + a₁ / 10) * (1497 / 500)
            * E0b
          + Tb * (797 / 10000)) ≤ K) :
    (∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
            ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
          / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ K * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  have hq1 : 49 / 100 ≤ q := le_trans hql hqlq
  have hq2 : q ≤ 1 / 2 := hq.le
  have hq0 : 0 ≤ q := by linarith
  have ho : (1 - (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ 283 / 200 :=
    one_sub_rpow_neg_le_of (by norm_num) (by interval_decide (trust := kernel))
  have hA1 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 101 →
      (⟨65, 105 / 2, 60, 20, 2873⟩ : WinChaos).const E₀ q K ≤ (7319 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 49 / 100) (b := 1 / 2)
      (ℓK := 101) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 8129 / 200)
      (cb := 2457 / 2000) (e := 1 / 2) (j := 7319 / 1000) (d := 3557 / 500)
      ⟨65, 105 / 2, 60, 20, 2873⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG1 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 1 / 2) (b := 6321 / 4000)
    (c := 13803 / 125000) (Gb := 283 / 125) (by norm_num) (by norm_num) 4 uChaosEps_4
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb1 : (283 / 125) * (7319 / 1000)
      * (1 - (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ 23623 / 1000 :=
    calc _ ≤ (283 / 125 : ℝ) * (7319 / 1000) * (283 / 200) * (10075 / 10000) := by gcongr
      _ ≤ 23623 / 1000 := by norm_num
  have hA2 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 100 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (1821 / 250) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 49 / 100) (b := 1 / 2)
      (ℓK := 100) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 8027 / 200)
      (cb := 12287 / 10000) (e := 1 / 2) (j := 1821 / 250) (d := 3549 / 500)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG2 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 1 / 2) (b := 26079 / 20000)
    (c := 408739 / 10000000) (Gb := 509 / 250) (by norm_num) (by norm_num) 5 uChaosEps_5
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb2 : (509 / 250) * (1821 / 250)
      * (1 - (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ 21143 / 1000 :=
    calc _ ≤ (509 / 250 : ℝ) * (1821 / 250) * (283 / 200) * (10075 / 10000) := by gcongr
      _ ≤ 21143 / 1000 := by norm_num
  have hA3 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 99 →
      (⟨64, 52, 60, 20, 2854⟩ : WinChaos).const E₀ q K ≤ (1821 / 250) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 49 / 100) (b := 1 / 2)
      (ℓK := 99) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 8027 / 200)
      (cb := 12287 / 10000) (e := 1 / 2) (j := 1821 / 250) (d := 707 / 100)
      ⟨64, 52, 60, 20, 2854⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG3 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 1 / 2) (b := 30117 / 25000)
    (c := 152939 / 10000000) (Gb := 981 / 500) (by norm_num) (by norm_num) 6 uChaosEps_6
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb3 : (981 / 500) * (1821 / 250)
      * (1 - (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ 10187 / 500 :=
    calc _ ≤ (981 / 500 : ℝ) * (1821 / 250) * (283 / 200) * (10075 / 10000) := by gcongr
      _ ≤ 10187 / 500 := by norm_num
  have hA4 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 98 →
      (⟨63, 103 / 2, 60, 20, 2834⟩ : WinChaos).const E₀ q K ≤ (29 / 4) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 49 / 100) (b := 1 / 2)
      (ℓK := 98) (Ci' := 11933 / 10000) (s' := 1837 / 125) (U := 317 / 8)
      (cb := 12289 / 10000) (e := 1 / 2) (j := 29 / 4) (d := 7053 / 1000)
      ⟨63, 103 / 2, 60, 20, 2834⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_20 h0 h1)
      (uChaosRadS_60_20 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG4 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 1 / 2) (b := 116849 / 100000)
    (c := 588533 / 100000000) (Gb := 242 / 125) (by norm_num) (by norm_num) 7 uChaosEps_7
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb4 : (242 / 125) * (29 / 4)
      * (1 - (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ 2001 / 100 :=
    calc _ ≤ (242 / 125 : ℝ) * (29 / 4) * (283 / 200) * (10075 / 10000) := by gcongr
      _ ≤ 2001 / 100 := by norm_num
  have hA5 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 74 →
      (⟨51, 87 / 2, 60, 16, 2600⟩ : WinChaos).const E₀ q K ≤ (267 / 40) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 49 / 100) (b := 1 / 2)
      (ℓK := 74) (Ci' := 5977 / 5000) (s' := 729 / 50) (U := 16723 / 500)
      (cb := 6177 / 5000) (e := 1 / 2) (j := 267 / 40) (d := 6497 / 1000)
      ⟨51, 87 / 2, 60, 16, 2600⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_60_16 h0 h1)
      (uChaosRadS_60_16 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG5 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 1 / 2) (b := 114751 / 100000)
    (c := 409219 / 1000000000) (Gb := 1921 / 1000) (by norm_num) (by norm_num) 31 uChaosEps_31
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb5 : (1921 / 1000) * (267 / 40)
      * (1 - (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ 18281 / 1000 :=
    calc _ ≤ (1921 / 1000 : ℝ) * (267 / 40) * (283 / 200) * (10075 / 10000) := by gcongr
      _ ≤ 18281 / 1000 := by norm_num
  have hA6 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 44 →
      (⟨36, 67 / 2, 50, 12, 2298⟩ : WinChaos).const E₀ q K ≤ (5877 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 49 / 100) (b := 1 / 2)
      (ℓK := 44) (Ci' := 12033 / 10000) (s' := 14233 / 1000) (U := 25619 / 1000)
      (cb := 12519 / 10000) (e := 1 / 2) (j := 5877 / 1000) (d := 229 / 40)
      ⟨36, 67 / 2, 50, 12, 2298⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_50_12 h0 h1)
      (uChaosRadS_50_12 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG6 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 1 / 2) (b := 114751 / 100000)
    (c := 409219 / 1000000000) (Gb := 1921 / 1000) (by norm_num) (by norm_num) 61 uChaosEps_61
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb6 : (1921 / 1000) * (5877 / 1000)
      * (1 - (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ 3219 / 200 :=
    calc _ ≤ (1921 / 1000 : ℝ) * (5877 / 1000) * (283 / 200) * (10075 / 10000) := by gcongr
      _ ≤ 3219 / 200 := by norm_num
  have hA7 : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      (⟨20, 45 / 2, 35, 10, 2000⟩ : WinChaos).const E₀ q K ≤ (4851 / 1000) :=
    fun E₀ h0 h1 K hK0 hK => le_trans (winChaosConst_le_cell (a := 49 / 100) (b := 1 / 2)
      (ℓK := 8) (Ci' := 12177 / 10000) (s' := 13749 / 1000) (U := 4303 / 250)
      (cb := 803 / 625) (e := 1 / 2) (j := 4851 / 1000) (d := 589 / 125)
      ⟨20, 45 / 2, 35, 10, 2000⟩ hq0 hq1 hq2 (by norm_num) h0 h1 hK0 hK (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (uChaosRadC_35_10 h0 h1)
      (uChaosRadS_35_10 h0 h1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl ⟨by norm_num, rfl⟩) (by dsimp only; interval_decide (trust := kernel))
      (by dsimp only; interval_decide (trust := kernel))) (max_le (by norm_num) (by norm_num))
  have hG7 := thetaWindowConstQ_rpow_le_of (ql := 49 / 100) (qu := 1 / 2) (b := 114751 / 100000)
    (c := 409219 / 1000000000) (Gb := 1921 / 1000) (by norm_num) (by norm_num) 97 uChaosEps_97
    (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
  have hb7 : (1921 / 1000) * (4851 / 1000)
      * (1 - (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) * (10763 / 10000) ≤ 14193 / 1000 :=
    calc _ ≤ (1921 / 1000 : ℝ) * (4851 / 1000) * (283 / 200) * (10763 / 10000) := by gcongr
      _ ≤ 14193 / 1000 := by norm_num
  have hN : ((⟨20, 45 / 2, 35, 10, 2000⟩ : WinChaos).N : ℝ)
      ≤ ((4851 / 1000) * (1 - (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ))) ^ 4 := by
    rw [mul_pow, half_rpow_pow_four]
    norm_num
  have hbH : (1921 / 1000) * (4851 / 1000) * (1 - (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ 13187 / 1000 :=
    calc _ ≤ (1921 / 1000 : ℝ) * (4851 / 1000) * (283 / 200) := by gcongr
      _ ≤ 13187 / 1000 := by norm_num
  exact z_half_core hX hx hΛ hql hqlq hq hwl0 hwl hwl1 ha₁ ha₁8 uChaosW_valid_1 uChaosW_valid_2
    uChaosW_valid_3 uChaosW_valid_4 uChaosW_valid_5 uChaosW_valid_6 uChaosW_valid_7 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA1 hA2
    hA3 hA4 hA5 hA6 hA7 hG1 hG2 hG3 hG4 hG5 hG6 hG7 hb1 hb2 hb3 hb4 hb5 hb6 hb7 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hN hbH hEt hVb hHb hTb
    hE0 hfin

set_option maxHeartbeats 1000000 in
-- the cell's hypotheses from `w ≥ W`
/-- **`Z`'s unbounded cell near `q = ½`**: for `Λ ≥ 6000`, `q ∈ [0.49, ½)` and
`w = (1 - 2q)Λ ≥ W ≥ 3/2`, with the certificate `hfin` at `q_l = 0.49`, `a₁ = 0.0098`,
`V_b = 1/6000 + 1/50`, `E[Z^q] ≤ K(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` (`RMF.z_half_numerals`,
`RMF.halfHb_large_le`; the twin of `RMF.u_cell_half_large`). -/
theorem z_cell_half_large {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q W K : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2)
    (hW : 3 / 2 ≤ W) (hWw : W ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hfin : (1 + W) * Real.exp (-((49 / 100) * W))
        * (Real.exp (1 / 2 * Real.log 51) * Real.exp (((49 / 5000) - 1 / 4) * Real.log 6000))
      + (121 / 6000) * Real.exp (3 / 4 * Real.log 880)
      + (1 / (49 / 100) + 1 / ((49 / 100) * W) + (121 / 6000) * (1 / 2 + (49 / 5000) / 10))
        * ((23623 / 1000) - ((23623 / 1000) - (21143 / 1000)) * Real.exp (-(5 * (49 / 5000)))
          - ((21143 / 1000) - (10187 / 500)) * Real.exp (-(6 * (49 / 5000)))
          - ((10187 / 500) - (2001 / 100)) * Real.exp (-(7 * (49 / 5000)))
          - ((2001 / 100) - (18281 / 1000)) * Real.exp (-(31 * (49 / 5000)))
          - ((18281 / 1000) - (3219 / 200)) * Real.exp (-(61 * (49 / 5000)))
          - ((3219 / 200) - (14193 / 1000)) * Real.exp (-(97 * (49 / 5000)))
          - (14193 / 1000) * 0)
      + (13187 / 1000)
        * (8 * (1497 / 500 * ((1 + 1 / W) / (49 / 100)
            * Real.exp (-(49 / 100 * W * (1499 / 6000)))))
          + (121 / 6000) * (1 / 2 + (49 / 5000) / 10) * (1497 / 500)
            * Real.exp (-(49 / 100 * W * (1499 / 6000)))
          + (1 + W) * Real.exp (-(49 / 100 * W * (114534631 / 117187500))) * (797 / 10000)) ≤ K) :
    (∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
            ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
          / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ K * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  have hΛ0 : 0 < Real.log (Real.log x) := by linarith
  have hwl1 : 1 / (49 / 100 : ℝ) - 1 ≤ W := by
    have : 1 / (49 / 100 : ℝ) - 1 ≤ 3 / 2 := by norm_num
    linarith
  have ha₁ : q * (1 - 2 * q) ≤ 49 / 5000 := by
    have := mul_one_sub_two_mul_anti (by norm_num : (1 : ℝ) / 4 ≤ 49 / 100) hq49
    linarith
  have hEt : (0 : ℝ) ≤ Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) / 4)) :=
    (Real.exp_pos _).le
  have hVb : (Real.log (Real.log x))⁻¹ + (1 - 2 * q) ≤ 121 / 6000 := by
    have hi : (Real.log (Real.log x))⁻¹ ≤ 1 / 6000 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hΛ
    linarith
  have hHb := halfHb_large_le (by norm_num : (0 : ℝ) < 49 / 100) hq49 (by linarith) hWw
  have hTb := halfTb_le le_rfl hq49 hW hWw
  have hE0 := halfE0_le (by norm_num) hq49 (by linarith) hWw
  exact z_half_numerals hX hx hΛ le_rfl hq49 hq (by linarith) hWw hwl1 ha₁ (by norm_num) hEt hVb
    hHb hTb hE0 hfin

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **`Z`'s cell `w ≥ 23 / 2` near `q = ½`** for `Λ ≥ 6000`: `E[Z^q] ≤ 215(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`
(`RMF.z_cell_half_large`; certificate total `212.73`). -/
theorem z_cell_half_top {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hw : 23 / 2 ≤ (1 - 2 * q) * Real.log (Real.log x)) :
    (∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
            ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
          / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ 215 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  z_cell_half_large (W := 23 / 2) hX hx hΛ hq49 hq (by norm_num) hw
    (by interval_decide (trust := kernel))

set_option maxHeartbeats 4000000 in
-- one kernel-checked certificate
/-- **`Z`'s cell `w ≥ 120` near `q = ½`** for `Λ ≥ 6000`: `E[Z^q] ≤ 40(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`
(`RMF.z_cell_half_large`; certificate total `38.38`). -/
theorem z_cell_half_anchor {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 6000 ≤ Real.log (Real.log x))
    (hq49 : 49 / 100 ≤ q) (hq : q < 1 / 2) (hw : 120 ≤ (1 - 2 * q) * Real.log (Real.log x)) :
    (∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
            ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
          / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ 40 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
  z_cell_half_large (W := 120) hX hx hΛ hq49 hq (by norm_num) hw
    (by interval_decide (trust := kernel))

end RMF
