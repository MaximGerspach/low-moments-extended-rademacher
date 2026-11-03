/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfCellsTSExplicit

/-!
# The Jensen regime's cells above `q = ½`, part 1

`RMF.above_cell_jensen_split` at the numerals of the cells 1–11,
`q ∈ [0.8154885, 1.0000000]`; their certificate totals are at most `24.73` (of `25`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The Jensen regime's cell `q ∈ [0.9672897, 1.0000000]`** (certificate total `24.18`). -/
theorem above_cell_1 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 9672897 / 10000000 ≤ q)
    (hq2 : q ≤ 1)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 9672897 / 10000000) (qu := 1) (L0 := 23 / 2) (TS := 42421 / 25) (nCen := 64527 / 50000)
    (Nc := 129093 / 100000) (nC1 := 67177 / 50000) (nC2 := 34209 / 25000) (nK := 230113 / 100000)
    (nCoh := 137977 / 100000) (nTiny := 5697 / 2500000000000000) (nKE := 149573 / 50000)
    (nJF := 226067 / 250000) (nE := 152119 / 10000000) (nB := 105361 / 100000)
    (nF := 110103 / 500000) (nOm := 10063 / 25000) (n15 := 30009 / 20000)
    (nBand0 := 61447 / 50000) (nBand1 := 414461 / 1000000) (nBand2 := 182339 / 100000000)
    (nBot := 491461 / 1000000) (Ntop := 129961 / 100000) (Nb0 := 111279 / 100000)
    (Nb1 := 32199 / 50000) (Nb2 := 21357 / 500000) (Nbot := 350627 / 500000)
    (Nw := 107427 / 100000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_11 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC2Hat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold botHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The Jensen regime's cell `q ∈ [0.9450378, 0.9672897]`** (certificate total `23.53`). -/
theorem above_cell_2 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 4725189 / 5000000 ≤ q)
    (hq2 : q ≤ 9672897 / 10000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 4725189 / 5000000) (qu := 9672897 / 10000000) (L0 := 23 / 2) (TS := 42421 / 25)
    (nCen := 112739 / 100000) (Nc := 28083 / 25000) (nC1 := 66183 / 50000) (nC2 := 67287 / 50000)
    (nK := 111963 / 50000) (nCoh := 136533 / 100000) (nTiny := 422213 / 100000000000000000)
    (nKE := 288617 / 100000) (nJF := 230063 / 250000) (nE := 33499 / 2000000)
    (nB := 52591 / 50000) (nF := 28501 / 125000) (nOm := 208993 / 500000) (n15 := 72159 / 50000)
    (nBand0 := 16199 / 12500) (nBand1 := 114059 / 250000) (nBand2 := 292343 / 100000000)
    (nBot := 136747 / 200000) (Ntop := 13959 / 10000) (Nb0 := 22947 / 20000) (Nb1 := 2667 / 4000)
    (Nb2 := 245019 / 5000000) (Nbot := 821831 / 1000000) (Nw := 28079 / 25000)
    (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_11 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC2Hat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold botHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The Jensen regime's cell `q ∈ [0.9300000, 0.9450378]`** (certificate total `23.17`). -/
theorem above_cell_3 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 93 / 100 ≤ q)
    (hq2 : q ≤ 4725189 / 5000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 93 / 100) (qu := 4725189 / 5000000) (L0 := 23 / 2) (TS := 42421 / 25)
    (nCen := 51179 / 50000) (Nc := 51129 / 50000) (nC1 := 130913 / 100000) (nC2 := 8309 / 6250)
    (nK := 109907 / 50000) (nCoh := 135559 / 100000) (nTiny := 320257 / 50000000000000000)
    (nKE := 140833 / 50000) (nJF := 29101 / 31250) (nE := 89379 / 5000000) (nB := 105061 / 100000)
    (nF := 233437 / 1000000) (nOm := 214307 / 500000) (n15 := 70343 / 50000)
    (nBand0 := 134287 / 100000) (nBand1 := 19431 / 40000) (nBand2 := 99629 / 25000000)
    (nBot := 887383 / 1000000) (Ntop := 146411 / 100000) (Nb0 := 117211 / 100000)
    (Nb1 := 6827 / 10000) (Nb2 := 107549 / 2000000) (Nbot := 37561 / 40000) (Nw := 57909 / 50000)
    (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_11 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC2Hat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold botHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The Jensen regime's cell `q ∈ [0.9095238, 0.9300000]`** (certificate total `23.64`). -/
theorem above_cell_4 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 4547619 / 5000000 ≤ q)
    (hq2 : q ≤ 93 / 100)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 4547619 / 5000000) (qu := 93 / 100) (L0 := 23 / 2) (TS := 586081 / 1000)
    (nCen := 191511 / 200000) (Nc := 961609 / 1000000) (nC1 := 130611 / 100000)
    (nC2 := 16567 / 12500) (nK := 217077 / 100000) (nCoh := 26981 / 20000)
    (nTiny := 7061 / 625000000000000) (nKE := 34633 / 12500) (nJF := 946417 / 1000000)
    (nE := 195321 / 10000000) (nB := 104979 / 100000) (nF := 241037 / 1000000)
    (nOm := 221889 / 500000) (n15 := 138347 / 100000) (nBand0 := 37117 / 25000)
    (nBand1 := 558901 / 1000000) (nBand2 := 19877 / 3125000) (nBot := 777931 / 1000000)
    (Ntop := 78461 / 50000) (Nb0 := 7769 / 6250) (Nb1 := 365813 / 500000)
    (Nb2 := 659503 / 10000000) (Nbot := 87397 / 100000) (Nw := 25413 / 20000)
    (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_10 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC2Hat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold botHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The Jensen regime's cell `q ∈ [0.8900227, 0.9095238]`** (certificate total `24.50`). -/
theorem above_cell_5 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 8900227 / 10000000 ≤ q)
    (hq2 : q ≤ 4547619 / 5000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 8900227 / 10000000) (qu := 4547619 / 5000000) (L0 := 23 / 2) (TS := 586081 / 1000)
    (nCen := 217969 / 250000) (Nc := 221347 / 250000) (nC1 := 129491 / 100000)
    (nC2 := 32817 / 25000) (nK := 42681 / 20000) (nCoh := 6701 / 5000)
    (nTiny := 38791 / 2000000000000000) (nKE := 270919 / 100000) (nJF := 192227 / 200000)
    (nE := 5313 / 250000) (nB := 104867 / 100000) (nF := 49701 / 200000) (nOm := 114569 / 250000)
    (n15 := 16913 / 12500) (nBand0 := 39931 / 25000) (nBand1 := 622149 / 1000000)
    (nBand2 := 478659 / 50000000) (nBot := 106813 / 100000) (Ntop := 167213 / 100000)
    (Nb0 := 130131 / 100000) (Nb1 := 154119 / 200000) (Nb2 := 194169 / 2500000)
    (Nbot := 25951 / 25000) (Nw := 13637 / 10000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_10 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC2Hat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold botHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The Jensen regime's cell `q ∈ [0.8768335, 0.8900227]`** (certificate total `23.97`). -/
theorem above_cell_6 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 1753667 / 2000000 ≤ q)
    (hq2 : q ≤ 8900227 / 10000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 1753667 / 2000000) (qu := 8900227 / 10000000) (L0 := 23 / 2) (TS := 586081 / 1000)
    (nCen := 795113 / 1000000) (Nc := 204533 / 250000) (nC1 := 8001 / 6250) (nC2 := 32413 / 25000)
    (nK := 104983 / 50000) (nCoh := 66591 / 50000) (nTiny := 279543 / 10000000000000000)
    (nKE := 265193 / 100000) (nJF := 971233 / 1000000) (nE := 225003 / 10000000)
    (nB := 104761 / 100000) (nF := 126843 / 500000) (nOm := 117009 / 250000)
    (n15 := 16569 / 12500) (nBand0 := 164623 / 100000) (nBand1 := 327167 / 500000)
    (nBand2 := 61379 / 5000000) (nBot := 2671 / 2000) (Ntop := 3483 / 2000)
    (Nb0 := 132917 / 100000) (Nb1 := 12316 / 15625) (Nb2 := 422241 / 5000000)
    (Nbot := 29493 / 25000) (Nw := 140711 / 100000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_10 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC2Hat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold botHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The Jensen regime's cell `q ∈ [0.8640903, 0.8768335]`** (certificate total `24.73`). -/
theorem above_cell_7 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 8640903 / 10000000 ≤ q)
    (hq2 : q ≤ 1753667 / 2000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 8640903 / 10000000) (qu := 1753667 / 2000000) (L0 := 23 / 2) (TS := 586081 / 1000)
    (nCen := 149269 / 200000) (Nc := 776853 / 1000000) (nC1 := 127217 / 100000)
    (nC2 := 25753 / 20000) (nK := 25959 / 12500) (nCoh := 66309 / 50000)
    (nTiny := 99487 / 2500000000000000) (nKE := 261389 / 100000) (nJF := 490551 / 500000)
    (nE := 237759 / 10000000) (nB := 104689 / 100000) (nF := 51759 / 200000)
    (nOm := 59717 / 125000) (n15 := 8173 / 6250) (nBand0 := 172583 / 100000)
    (nBand1 := 175109 / 250000) (nBand2 := 158453 / 10000000) (nBot := 85149 / 50000)
    (Ntop := 181439 / 100000) (Nb0 := 137173 / 100000) (Nb1 := 816497 / 1000000)
    (Nb2 := 470569 / 5000000) (Nbot := 136119 / 100000) (Nw := 36959 / 25000)
    (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_10 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC2Hat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold botHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The Jensen regime's cell `q ∈ [0.8600000, 0.8640903]`** (certificate total `23.17`). -/
theorem above_cell_8 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 43 / 50 ≤ q)
    (hq2 : q ≤ 8640903 / 10000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 43 / 50) (qu := 8640903 / 10000000) (L0 := 23 / 2) (TS := 586081 / 1000)
    (nCen := 10952 / 15625) (Nc := 368451 / 500000) (nC1 := 125977 / 100000)
    (nC2 := 31859 / 25000) (nK := 205479 / 100000) (nCoh := 33019 / 25000)
    (nTiny := 111429 / 2500000000000000) (nKE := 51553 / 20000) (nJF := 984293 / 1000000)
    (nE := 48401 / 2000000) (nB := 5231 / 5000) (nF := 260457 / 1000000) (nOm := 240303 / 500000)
    (n15 := 129101 / 100000) (nBand0 := 170537 / 100000) (nBand1 := 173663 / 250000)
    (nBand2 := 83343 / 5000000) (nBot := 181653 / 100000) (Ntop := 91631 / 50000)
    (Nb0 := 13643 / 10000) (Nb1 := 810159 / 1000000) (Nb2 := 233983 / 2500000)
    (Nbot := 35383 / 25000) (Nw := 146241 / 100000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_10 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC2Hat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold botHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The Jensen regime's cell `q ∈ [0.8428571, 0.8600000]`** (certificate total `24.10`). -/
theorem above_cell_9 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 8428571 / 10000000 ≤ q)
    (hq2 : q ≤ 43 / 50)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 8428571 / 10000000) (qu := 43 / 50) (L0 := 23 / 2) (TS := 196483 / 1000)
    (nCen := 687859 / 1000000) (Nc := 91217 / 125000) (nC1 := 126407 / 100000)
    (nC2 := 15981 / 12500) (nK := 10239 / 5000) (nCoh := 65951 / 50000)
    (nTiny := 71679 / 1000000000000000) (nKE := 256613 / 100000) (nJF := 498897 / 500000)
    (nE := 260641 / 10000000) (nB := 52299 / 50000) (nF := 133769 / 500000)
    (nOm := 494263 / 1000000) (n15 := 64289 / 50000) (nBand0 := 189471 / 100000)
    (nBand1 := 199213 / 250000) (nBand2 := 243831 / 10000000) (nBot := 26823 / 20000)
    (Ntop := 194551 / 100000) (Nb0 := 73071 / 50000) (Nb1 := 876581 / 1000000)
    (Nb2 := 2309 / 20000) (Nbot := 119057 / 100000) (Nw := 163567 / 100000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_9 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC2Hat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold botHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The Jensen regime's cell `q ∈ [0.8265306, 0.8428571]`** (certificate total `24.60`). -/
theorem above_cell_10 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 4132653 / 5000000 ≤ q)
    (hq2 : q ≤ 8428571 / 10000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 4132653 / 5000000) (qu := 8428571 / 10000000) (L0 := 23 / 2) (TS := 196483 / 1000)
    (nCen := 19747 / 31250) (Nc := 684483 / 1000000) (nC1 := 125237 / 100000)
    (nC2 := 126569 / 100000) (nK := 50469 / 25000) (nCoh := 131177 / 100000)
    (nTiny := 56347 / 500000000000000) (nKE := 251839 / 100000) (nJF := 20217 / 20000)
    (nE := 279723 / 10000000) (nB := 20901 / 20000) (nF := 13723 / 50000) (nOm := 253503 / 500000)
    (n15 := 63223 / 50000) (nBand0 := 100309 / 50000) (nBand1 := 865453 / 1000000)
    (nBand2 := 331137 / 10000000) (nBot := 87257 / 50000) (Ntop := 204871 / 100000)
    (Nb0 := 76211 / 50000) (Nb1 := 459063 / 500000) (Nb2 := 66243 / 500000) (Nbot := 4378 / 3125)
    (Nw := 174963 / 100000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_9 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC2Hat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold botHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The Jensen regime's cell `q ∈ [0.8154885, 0.8265306]`** (certificate total `23.90`). -/
theorem above_cell_11 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 1630977 / 2000000 ≤ q)
    (hq2 : q ≤ 4132653 / 5000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 1630977 / 2000000) (qu := 4132653 / 5000000) (L0 := 23 / 2) (TS := 196483 / 1000)
    (nCen := 581989 / 1000000) (Nc := 643311 / 1000000) (nC1 := 123883 / 100000)
    (nC2 := 125113 / 100000) (nK := 199149 / 100000) (nCoh := 13049 / 10000)
    (nTiny := 1913 / 12500000000000) (nKE := 1979 / 800) (nJF := 50989 / 50000)
    (nE := 146707 / 5000000) (nB := 3263 / 3125) (nF := 279243 / 1000000)
    (nOm := 515551 / 1000000) (n15 := 15563 / 12500) (nBand0 := 205457 / 100000)
    (nBand1 := 900151 / 1000000) (nBand2 := 199383 / 5000000) (nBot := 104417 / 50000)
    (Ntop := 105859 / 50000) (Nb0 := 3111 / 2000) (Nb1 := 938629 / 1000000)
    (Nb2 := 142447 / 1000000) (Nbot := 157113 / 100000) (Nw := 90391 / 50000)
    (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_9 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC2Hat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by unfold bandHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by unfold botHatN; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

end RMF
