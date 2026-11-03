/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfCellsTSExplicit

/-!
# The Jensen regime's cells above `q = ½`, part 2

`RMF.above_cell_jensen_split` at the numerals of the cells 12–22,
`q ∈ [0.6851696, 0.8154885]`; their certificate totals are at most `24.80` (of `25`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The Jensen regime's cell `q ∈ [0.8048198, 0.8154885]`** (certificate total `24.33`). -/
theorem above_cell_12 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 4024099 / 5000000 ≤ q)
    (hq2 : q ≤ 1630977 / 2000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 4024099 / 5000000) (qu := 1630977 / 2000000) (L0 := 23 / 2) (TS := 196483 / 1000)
    (nCen := 550463 / 1000000) (Nc := 154669 / 250000) (nC1 := 123101 / 100000)
    (nC2 := 62133 / 50000) (nK := 7893 / 4000) (nCoh := 130027 / 100000)
    (nTiny := 205691 / 1000000000000000) (nKE := 611 / 250) (nJF := 102849 / 100000)
    (nE := 153639 / 5000000) (nB := 104357 / 100000) (nF := 35493 / 125000)
    (nOm := 262007 / 500000) (n15 := 123237 / 100000) (nBand0 := 26651 / 12500)
    (nBand1 := 189961 / 200000) (nBand2 := 483153 / 10000000) (nBot := 31569 / 12500)
    (Ntop := 109459 / 50000) (Nb0 := 20013 / 12500) (Nb1 := 969209 / 1000000)
    (Nb2 := 31213 / 200000) (Nbot := 177867 / 100000) (Nw := 237 / 125) (Nt := 1 / 1000000000)
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
/-- **The Jensen regime's cell `q ∈ [0.7945119, 0.8048198]`** (certificate total `24.80`). -/
theorem above_cell_13 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 7945119 / 10000000 ≤ q)
    (hq2 : q ≤ 4024099 / 5000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 7945119 / 10000000) (qu := 4024099 / 5000000) (L0 := 23 / 2) (TS := 196483 / 1000)
    (nCen := 521531 / 1000000) (Nc := 596357 / 1000000) (nC1 := 30583 / 25000)
    (nC2 := 24687 / 20000) (nK := 195579 / 100000) (nCoh := 64791 / 50000)
    (nTiny := 34213 / 125000000000000) (nKE := 241561 / 100000) (nJF := 103699 / 100000)
    (nE := 64259 / 2000000) (nB := 104299 / 100000) (nF := 288561 / 1000000)
    (nOm := 266121 / 500000) (n15 := 3814 / 3125) (nBand0 := 220879 / 100000)
    (nBand1 := 10001 / 10000) (nBand2 := 289759 / 5000000) (nBot := 305051 / 100000)
    (Ntop := 226073 / 100000) (Nb0 := 41177 / 25000) (Nb1 := 100037 / 100000)
    (Nb2 := 85241 / 500000) (Nbot := 25227 / 12500) (Nw := 99451 / 50000) (Nt := 1 / 1000000000)
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
/-- **The Jensen regime's cell `q ∈ [0.7900000, 0.7945119]`** (certificate total `23.69`). -/
theorem above_cell_14 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 79 / 100 ≤ q)
    (hq2 : q ≤ 7945119 / 10000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 79 / 100) (qu := 7945119 / 10000000) (L0 := 23 / 2) (TS := 196483 / 1000)
    (nCen := 98921 / 200000) (Nc := 573581 / 1000000) (nC1 := 12137 / 10000)
    (nC2 := 61207 / 50000) (nK := 193907 / 100000) (nCoh := 129153 / 100000)
    (nTiny := 310161 / 1000000000000000) (nKE := 7464 / 3125) (nJF := 52037 / 50000)
    (nE := 327631 / 10000000) (nB := 104243 / 100000) (nF := 58121 / 200000) (nOm := 1674 / 3125)
    (n15 := 30233 / 25000) (nBand0 := 220671 / 100000) (nBand1 := 100447 / 100000)
    (nBand2 := 307687 / 5000000) (nBot := 164341 / 50000) (Ntop := 114367 / 50000)
    (Nb0 := 165079 / 100000) (Nb1 := 100313 / 100000) (Nb2 := 43257 / 250000)
    (Nbot := 8497 / 4000) (Nw := 199647 / 100000) (Nt := 1 / 1000000000)
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
/-- **The Jensen regime's cell `q ∈ [0.7761905, 0.7900000]`** (certificate total `23.54`). -/
theorem above_cell_15 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 1552381 / 2000000 ≤ q)
    (hq2 : q ≤ 79 / 100)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 1552381 / 2000000) (qu := 79 / 100) (L0 := 23 / 2) (TS := 814603 / 10000)
    (nCen := 121021 / 250000) (Nc := 569599 / 1000000) (nC1 := 121391 / 100000)
    (nC2 := 61207 / 50000) (nK := 193179 / 100000) (nCoh := 64483 / 50000)
    (nTiny := 454779 / 1000000000000000) (nKE := 237671 / 100000) (nJF := 105229 / 100000)
    (nE := 347807 / 10000000) (nB := 104219 / 100000) (nF := 37119 / 125000)
    (nOm := 136779 / 250000) (n15 := 120453 / 100000) (nBand0 := 118867 / 50000)
    (nBand1 := 55509 / 50000) (nBand2 := 402219 / 5000000) (nBot := 47191 / 20000)
    (Ntop := 119853 / 50000) (Nb0 := 174743 / 100000) (Nb1 := 106997 / 100000)
    (Nb2 := 101479 / 500000) (Nbot := 173899 / 100000) (Nw := 220227 / 100000)
    (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_8 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.7630386, 0.7761905]`** (certificate total `23.75`). -/
theorem above_cell_16 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 3815193 / 5000000 ≤ q)
    (hq2 : q ≤ 1552381 / 2000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 3815193 / 5000000) (qu := 1552381 / 2000000) (L0 := 23 / 2) (TS := 814603 / 10000)
    (nCen := 451441 / 1000000) (Nc := 136307 / 250000) (nC1 := 60171 / 50000)
    (nC2 := 12129 / 10000) (nK := 19097 / 10000) (nCoh := 64197 / 50000)
    (nTiny := 10231 / 15625000000000) (nKE := 117051 / 50000) (nJF := 106343 / 100000)
    (nE := 368177 / 10000000) (nB := 6509 / 6250) (nF := 303127 / 1000000)
    (nOm := 557779 / 1000000) (n15 := 119023 / 100000) (nBand0 := 49619 / 20000)
    (nBand1 := 118417 / 100000) (nBand2 := 50023 / 500000) (nBot := 72721 / 25000)
    (Ntop := 124799 / 50000) (Nb0 := 22679 / 12500) (Nb1 := 27937 / 25000)
    (Nb2 := 227033 / 1000000) (Nbot := 20137 / 10000) (Nw := 117667 / 50000)
    (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_8 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.7505130, 0.7630386]`** (certificate total `23.98`). -/
theorem above_cell_17 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 750513 / 1000000 ≤ q)
    (hq2 : q ≤ 3815193 / 5000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 750513 / 1000000) (qu := 3815193 / 5000000) (L0 := 23 / 2) (TS := 814603 / 10000)
    (nCen := 422567 / 1000000) (Nc := 104807 / 200000) (nC1 := 29833 / 25000)
    (nC2 := 30053 / 25000) (nK := 188889 / 100000) (nCoh := 31963 / 25000)
    (nTiny := 463263 / 500000000000000) (nKE := 115377 / 50000) (nJF := 21483 / 20000)
    (nE := 97171 / 2500000) (nB := 104073 / 100000) (nF := 154563 / 500000)
    (nOm := 567997 / 1000000) (n15 := 117711 / 100000) (nBand0 := 258209 / 100000)
    (nBand1 := 6297 / 5000) (nBand2 := 122493 / 1000000) (nBot := 35733 / 10000)
    (Ntop := 259341 / 100000) (Nb0 := 47047 / 25000) (Nb1 := 29161 / 25000)
    (Nb2 := 252693 / 1000000) (Nbot := 7302 / 3125) (Nw := 31421 / 12500) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_8 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.7385838, 0.7505130]`** (certificate total `24.24`). -/
theorem above_cell_18 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 3692919 / 5000000 ≤ q)
    (hq2 : q ≤ 750513 / 1000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 3692919 / 5000000) (qu := 750513 / 1000000) (L0 := 23 / 2) (TS := 814603 / 10000)
    (nCen := 99257 / 250000) (Nc := 505623 / 1000000) (nC1 := 118361 / 100000)
    (nC2 := 59589 / 50000) (nK := 11683 / 6250) (nCoh := 63669 / 50000)
    (nTiny := 32239 / 25000000000000) (nKE := 227609 / 100000) (nJF := 3389 / 3125)
    (nE := 409277 / 10000000) (nB := 20801 / 20000) (nF := 6299 / 20000) (nOm := 577781 / 1000000)
    (n15 := 58253 / 50000) (nBand0 := 268053 / 100000) (nBand1 := 133583 / 100000)
    (nBand2 := 147829 / 1000000) (nBot := 436537 / 100000) (Ntop := 134459 / 50000)
    (Nb0 := 38999 / 20000) (Nb1 := 30423 / 25000) (Nb2 := 69977 / 250000)
    (Nbot := 271273 / 100000) (Nw := 268387 / 100000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_8 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.7272227, 0.7385838]`** (certificate total `24.52`). -/
theorem above_cell_19 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 7272227 / 10000000 ≤ q)
    (hq2 : q ≤ 3692919 / 5000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 7272227 / 10000000) (qu := 3692919 / 5000000) (L0 := 23 / 2) (TS := 814603 / 10000)
    (nCen := 374439 / 1000000) (Nc := 30603 / 62500) (nC1 := 117431 / 100000)
    (nC2 := 11819 / 10000) (nK := 185079 / 100000) (nCoh := 126851 / 100000)
    (nTiny := 176679 / 100000000000000) (nKE := 112327 / 50000) (nJF := 54721 / 50000)
    (nE := 214951 / 5000000) (nB := 103941 / 100000) (nF := 320599 / 1000000)
    (nOm := 587143 / 1000000) (n15 := 28849 / 25000) (nBand0 := 17351 / 6250)
    (nBand1 := 28269 / 20000) (nBand2 := 176057 / 1000000) (nBot := 529603 / 100000)
    (Ntop := 69579 / 25000) (Nb0 := 100923 / 50000) (Nb1 := 126899 / 100000)
    (Nb2 := 61729 / 200000) (Nbot := 314689 / 100000) (Nw := 143229 / 50000)
    (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_8 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.7200000, 0.7272227]`** (certificate total `23.70`). -/
theorem above_cell_20 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 18 / 25 ≤ q)
    (hq2 : q ≤ 7272227 / 10000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 18 / 25) (qu := 7272227 / 10000000) (L0 := 23 / 2) (TS := 814603 / 10000)
    (nCen := 177093 / 500000) (Nc := 473781 / 1000000) (nC1 := 116449 / 100000)
    (nC2 := 23431 / 20000) (nK := 22917 / 12500) (nCoh := 31597 / 25000)
    (nTiny := 215833 / 100000000000000) (nKE := 71 / 32) (nJF := 110079 / 100000)
    (nE := 443551 / 10000000) (nB := 103879 / 100000) (nF := 324243 / 1000000)
    (nOm := 296497 / 500000) (n15 := 57187 / 50000) (nBand0 := 17563 / 6250)
    (nBand1 := 144971 / 100000) (nBand2 := 194129 / 1000000) (nBot := 23839 / 4000)
    (Ntop := 14197 / 5000) (Nb0 := 102497 / 50000) (Nb1 := 129459 / 100000)
    (Nb2 := 64817 / 200000) (Nbot := 43191 / 12500) (Nw := 295147 / 100000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_8 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.7018349, 0.7200000]`** (certificate total `24.16`). -/
theorem above_cell_21 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 7018349 / 10000000 ≤ q)
    (hq2 : q ≤ 18 / 25)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 7018349 / 10000000) (qu := 18 / 25) (L0 := 23 / 2) (TS := 416889 / 10000)
    (nCen := 343101 / 1000000) (Nc := 472143 / 1000000) (nC1 := 116163 / 100000)
    (nC2 := 116839 / 100000) (nK := 45559 / 25000) (nCoh := 25219 / 20000)
    (nTiny := 357071 / 100000000000000) (nKE := 220127 / 100000) (nJF := 111699 / 100000)
    (nE := 239913 / 5000000) (nB := 649 / 625) (nF := 333591 / 1000000) (nOm := 608459 / 1000000)
    (n15 := 113741 / 100000) (nBand0 := 305837 / 100000) (nBand1 := 16431 / 10000)
    (nBand2 := 262361 / 1000000) (nBot := 61333 / 12500) (Ntop := 301471 / 100000)
    (Nb0 := 221821 / 100000) (Nb1 := 142487 / 100000) (Nb2 := 24687 / 62500)
    (Nbot := 310641 / 100000) (Nw := 344907 / 100000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_7 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.6851696, 0.7018349]`** (certificate total `24.05`). -/
theorem above_cell_22 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 428231 / 625000 ≤ q)
    (hq2 : q ≤ 7018349 / 10000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 428231 / 625000) (qu := 7018349 / 10000000) (L0 := 23 / 2) (TS := 416889 / 10000)
    (nCen := 63109 / 200000) (Nc := 5673 / 12500) (nC1 := 57351 / 50000) (nC2 := 57649 / 50000)
    (nK := 179499 / 100000) (nCoh := 1567 / 1250) (nTiny := 283341 / 50000000000000)
    (nKE := 21579 / 10000) (nJF := 113209 / 100000) (nE := 515709 / 10000000)
    (nB := 103743 / 100000) (nF := 85601 / 250000) (nOm := 124469 / 200000)
    (n15 := 112207 / 100000) (nBand0 := 8007 / 2500) (nBand1 := 178563 / 100000)
    (nBand2 := 331063 / 1000000) (nBot := 158433 / 25000) (Ntop := 158343 / 50000)
    (Nb0 := 46781 / 20000) (Nb1 := 152713 / 100000) (Nb2 := 455099 / 1000000)
    (Nbot := 192437 / 50000) (Nw := 9641 / 2500) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_7 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
