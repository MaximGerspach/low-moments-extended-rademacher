/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfCellsTSExplicit

/-!
# The Jensen regime's cells above `q = ½`, part 4

`RMF.above_cell_jensen_split` at the numerals of the cells 33–42,
`q ∈ [0.5001500, 0.5200000]`; their certificate totals are at most `24.67` (of `25`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The Jensen regime's cell `q ∈ [0.5100000, 0.5200000]`** (certificate total `18.35`). -/
theorem above_cell_33 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 51 / 100 ≤ q)
    (hq2 : q ≤ 13 / 25)
    (hx3 : 3 ≤ x) (hΛ : 25 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 51 / 100) (qu := 13 / 25) (L0 := 25) (TS := 33377 / 2500) (nCen := 201233 / 1000000)
    (Nc := 110397 / 250000) (nC1 := 50643 / 50000) (nC2 := 4053 / 4000) (nK := 154267 / 100000)
    (nCoh := 739 / 625) (nTiny := 181821 / 250000000000) (nKE := 11051 / 6250)
    (nJF := 130527 / 100000) (nE := 110059 / 1000000) (nB := 6423 / 6250) (nF := 112593 / 250000)
    (nOm := 76873 / 100000) (n15 := 50439 / 50000) (nBand0 := 487383 / 100000)
    (nBand1 := 234209 / 50000) (nBand2 := 230867 / 100000) (nBot := 214301 / 10000)
    (Ntop := 521379 / 100000) (Nb0 := 472621 / 100000) (Nb1 := 90917 / 20000)
    (Nb2 := 227179 / 100000) (Nbot := 201863 / 10000) (Nw := 15994 / 125) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_2 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.5050000, 0.5100000]`** (certificate total `17.89`). -/
theorem above_cell_34 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 101 / 200 ≤ q)
    (hq2 : q ≤ 51 / 100)
    (hx3 : 3 ≤ x) (hΛ : 50 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 101 / 200) (qu := 51 / 100) (L0 := 50) (TS := 129289 / 10000) (nCen := 50247 / 250000)
    (Nc := 444869 / 1000000) (nC1 := 12581 / 12500) (nC2 := 100667 / 100000)
    (nK := 152987 / 100000) (nCoh := 5893 / 5000) (nTiny := 835381 / 1000000000000)
    (nKE := 17489 / 10000) (nJF := 65531 / 50000) (nE := 56233 / 500000) (nB := 51357 / 50000)
    (nF := 453909 / 1000000) (nOm := 386329 / 500000) (n15 := 20089 / 20000)
    (nBand0 := 60993 / 12500) (nBand1 := 59643 / 12500) (nBand2 := 59647 / 25000)
    (nBot := 103567 / 5000) (Ntop := 526991 / 100000) (Nb0 := 480491 / 100000)
    (Nb1 := 11749 / 2500) (Nb2 := 118307 / 50000) (Nbot := 12567 / 625) (Nw := 52107 / 200)
    (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_1 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.5025000, 0.5050000]`** (certificate total `19.13`). -/
theorem above_cell_35 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 201 / 400 ≤ q)
    (hq2 : q ≤ 101 / 200)
    (hx3 : 3 ≤ x) (hΛ : 100 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 201 / 400) (qu := 101 / 200) (L0 := 100) (TS := 129289 / 10000)
    (nCen := 25131 / 125000) (Nc := 111681 / 250000) (nC1 := 100337 / 100000)
    (nC2 := 50173 / 50000) (nK := 152351 / 100000) (nCoh := 117671 / 100000)
    (nTiny := 895313 / 1000000000000) (nKE := 34787 / 20000) (nJF := 131331 / 100000)
    (nE := 11369 / 100000) (nB := 3209 / 3125) (nF := 56961 / 125000) (nOm := 387309 / 500000)
    (n15 := 25059 / 25000) (nBand0 := 61031 / 12500) (nBand1 := 240789 / 50000)
    (nBand2 := 7579 / 3125) (nBot := 51623 / 2500) (Ntop := 529807 / 100000)
    (Nb0 := 484557 / 100000) (Nb1 := 47797 / 10000) (Nb2 := 120767 / 50000)
    (Nbot := 101733 / 5000) (Nw := 527559 / 1000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_1 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.5012500, 0.5025000]`** (certificate total `21.50`). -/
theorem above_cell_36 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 401 / 800 ≤ q)
    (hq2 : q ≤ 201 / 400)
    (hx3 : 3 ≤ x) (hΛ : 200 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 401 / 800) (qu := 201 / 400) (L0 := 200) (TS := 129289 / 10000)
    (nCen := 100561 / 500000) (Nc := 447703 / 1000000) (nC1 := 100183 / 100000)
    (nC2 := 100187 / 100000) (nK := 76017 / 50000) (nCoh := 14697 / 12500)
    (nTiny := 115859 / 125000000000) (nKE := 173459 / 100000) (nJF := 26293 / 20000)
    (nE := 57153 / 500000) (nB := 51337 / 50000) (nF := 22829 / 50000) (nOm := 775597 / 1000000)
    (n15 := 25033 / 25000) (nBand0 := 488401 / 100000) (nBand1 := 241903 / 50000)
    (nBand2 := 246621 / 100000) (nBot := 206193 / 10000) (Ntop := 531217 / 100000)
    (Nb0 := 24331 / 5000) (Nb1 := 482053 / 100000) (Nb2 := 246141 / 100000) (Nbot := 40941 / 2000)
    (Nw := 106349 / 100) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_1 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.5007812, 0.5012500]`** (certificate total `19.87`). -/
theorem above_cell_37 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 1251953 / 2500000 ≤ q)
    (hq2 : q ≤ 401 / 800)
    (hx3 : 3 ≤ x) (hΛ : 400 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 1251953 / 2500000) (qu := 401 / 800) (L0 := 400) (TS := 129289 / 10000)
    (nCen := 50289 / 250000) (Nc := 224039 / 500000) (nC1 := 50053 / 50000)
    (nC2 := 100109 / 100000) (nK := 37969 / 25000) (nCoh := 117529 / 100000)
    (nTiny := 938993 / 1000000000000) (nKE := 86611 / 50000) (nJF := 32879 / 25000)
    (nE := 57269 / 500000) (nB := 25667 / 25000) (nF := 91383 / 200000) (nOm := 155191 / 200000)
    (n15 := 100081 / 100000) (nBand0 := 30513 / 6250) (nBand1 := 96879 / 20000)
    (nBand2 := 128837 / 50000) (nBot := 195003 / 10000) (Ntop := 106329 / 20000)
    (Nb0 := 487149 / 100000) (Nb1 := 9667 / 2000) (Nb2 := 64343 / 25000) (Nbot := 2427 / 125)
    (Nw := 34097 / 20) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_1 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.5004882, 0.5007812]`** (certificate total `22.09`). -/
theorem above_cell_38 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 2502441 / 5000000 ≤ q)
    (hq2 : q ≤ 1251953 / 2500000)
    (hx3 : 3 ≤ x) (hΛ : 1250000 / 1953 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 2502441 / 5000000) (qu := 1251953 / 2500000) (L0 := 1250000 / 1953)
    (TS := 129289 / 10000) (nCen := 201181 / 1000000) (Nc := 112079 / 250000)
    (nC1 := 50039 / 50000) (nC2 := 100079 / 100000) (nK := 18977 / 12500)
    (nCoh := 117511 / 100000) (nTiny := 946649 / 1000000000000) (nKE := 173133 / 100000)
    (nJF := 32887 / 25000) (nE := 28671 / 250000) (nB := 20533 / 20000) (nF := 114281 / 250000)
    (nOm := 194047 / 250000) (n15 := 50031 / 50000) (nBand0 := 24417 / 5000)
    (nBand1 := 97003 / 20000) (nBand2 := 8863 / 3125) (nBot := 97491 / 5000)
    (Ntop := 266007 / 50000) (Nb0 := 121933 / 25000) (Nb1 := 242207 / 50000)
    (Nb2 := 283413 / 100000) (Nbot := 194477 / 10000) (Nw := 68414 / 25) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_1 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.5003051, 0.5004882]`** (certificate total `24.67`). -/
theorem above_cell_39 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 5003051 / 10000000 ≤ q)
    (hq2 : q ≤ 2502441 / 5000000)
    (hx3 : 3 ≤ x) (hΛ : 2500000 / 2441 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 5003051 / 10000000) (qu := 2502441 / 5000000) (L0 := 2500000 / 2441)
    (TS := 129289 / 10000) (nCen := 100599 / 500000) (Nc := 448467 / 1000000) (nC1 := 5003 / 5000)
    (nC2 := 100061 / 100000) (nK := 151779 / 100000) (nCoh := 47 / 40)
    (nTiny := 190293 / 200000000000) (nKE := 173077 / 100000) (nJF := 131567 / 100000)
    (nE := 4591 / 40000) (nB := 12833 / 12500) (nF := 91451 / 200000) (nOm := 776333 / 1000000)
    (n15 := 2001 / 2000) (nBand0 := 488423 / 100000) (nBand1 := 242701 / 50000)
    (nBand2 := 321743 / 100000) (nBot := 194969 / 10000) (Ntop := 133061 / 25000)
    (Nb0 := 244049 / 50000) (Nb1 := 485081 / 100000) (Nb2 := 321611 / 100000) (Nbot := 7787 / 400)
    (Nw := 43881 / 10) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_1 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.5002179, 0.5003051]`** (certificate total `24.16`). -/
theorem above_cell_40 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 5002179 / 10000000 ≤ q)
    (hq2 : q ≤ 5003051 / 10000000)
    (hx3 : 3 ≤ x) (hΛ : 5000000 / 3051 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 5002179 / 10000000) (qu := 5003051 / 10000000) (L0 := 5000000 / 3051)
    (TS := 129289 / 10000) (nCen := 100603 / 500000) (Nc := 224269 / 500000)
    (nC1 := 100049 / 100000) (nC2 := 2001 / 2000) (nK := 37939 / 25000) (nCoh := 117493 / 100000)
    (nTiny := 953767 / 1000000000000) (nKE := 173043 / 100000) (nJF := 131577 / 100000)
    (nE := 57409 / 500000) (nB := 102663 / 100000) (nF := 228659 / 500000)
    (nOm := 776401 / 1000000) (n15 := 100043 / 100000) (nBand0 := 48843 / 10000)
    (nBand1 := 97111 / 20000) (nBand2 := 35137 / 10000) (nBot := 187517 / 10000)
    (Ntop := 26617 / 5000) (Nb0 := 6103 / 1250) (Nb1 := 485367 / 100000) (Nb2 := 87821 / 25000)
    (Nbot := 93667 / 5000) (Nw := 614941 / 100) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_1 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.5001676, 0.5002179]`** (certificate total `24.35`). -/
theorem above_cell_41 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 1250419 / 2500000 ≤ q)
    (hq2 : q ≤ 5002179 / 10000000)
    (hx3 : 3 ≤ x) (hΛ : 5000000 / 2179 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 1250419 / 2500000) (qu := 5002179 / 10000000) (L0 := 5000000 / 2179)
    (TS := 129289 / 10000) (nCen := 201211 / 1000000) (Nc := 22429 / 50000) (nC1 := 25011 / 25000)
    (nC2 := 25011 / 25000) (nK := 30349 / 20000) (nCoh := 11749 / 10000)
    (nTiny := 477549 / 500000000000) (nKE := 86513 / 50000) (nJF := 65791 / 50000)
    (nE := 114843 / 1000000) (nB := 51331 / 50000) (nF := 228677 / 500000)
    (nOm := 776441 / 1000000) (n15 := 100039 / 100000) (nBand0 := 244223 / 50000)
    (nBand1 := 97131 / 20000) (nBand2 := 373427 / 100000) (nBot := 183097 / 10000)
    (Ntop := 532401 / 100000) (Nb0 := 488333 / 100000) (Nb1 := 60693 / 12500) (Nb2 := 2987 / 800)
    (Nbot := 91487 / 5000) (Nw := 199997 / 25) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_1 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.5001500, 0.5001676]`** (certificate total `22.31`). -/
theorem above_cell_42 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 10003 / 20000 ≤ q)
    (hq2 : q ≤ 1250419 / 2500000)
    (hx3 : 3 ≤ x) (hΛ : 1250000 / 419 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 10003 / 20000) (qu := 1250419 / 2500000) (L0 := 1250000 / 419) (TS := 129289 / 10000)
    (nCen := 50303 / 250000) (Nc := 224297 / 500000) (nC1 := 100041 / 100000)
    (nC2 := 100041 / 100000) (nK := 151739 / 100000) (nCoh := 7343 / 6250)
    (nTiny := 238891 / 250000000000) (nKE := 21627 / 12500) (nJF := 4112 / 3125)
    (nE := 28713 / 250000) (nB := 51331 / 50000) (nF := 228683 / 500000) (nOm := 388227 / 500000)
    (n15 := 100037 / 100000) (nBand0 := 488437 / 100000) (nBand1 := 19427 / 4000)
    (nBand2 := 38217 / 10000) (nBot := 6937 / 400) (Ntop := 16638 / 3125) (Nb0 := 15261 / 3125)
    (Nb1 := 485591 / 100000) (Nb2 := 382131 / 100000) (Nbot := 173329 / 10000) (Nw := 223489 / 25)
    (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_1 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
