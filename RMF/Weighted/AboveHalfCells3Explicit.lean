/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfCellsTSExplicit

/-!
# The Jensen regime's cells above `q = ½`, part 3

`RMF.above_cell_jensen_split` at the numerals of the cells 23–32,
`q ∈ [0.5200000, 0.6851696]`; their certificate totals are at most `24.22` (of `25`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The Jensen regime's cell `q ∈ [0.6698804, 0.6851696]`** (certificate total `23.95`). -/
theorem above_cell_23 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 1674701 / 2500000 ≤ q)
    (hq2 : q ≤ 428231 / 625000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 1674701 / 2500000) (qu := 428231 / 625000) (L0 := 23 / 2) (TS := 416889 / 10000)
    (nCen := 293321 / 1000000) (Nc := 21993 / 50000) (nC1 := 14171 / 12500) (nC2 := 14237 / 12500)
    (nK := 5532 / 3125) (nCoh := 12469 / 10000) (nTiny := 86569 / 10000000000000)
    (nKE := 105943 / 50000) (nJF := 22923 / 20000) (nE := 110197 / 2000000)
    (nB := 103653 / 100000) (nF := 350693 / 1000000) (nOm := 635131 / 1000000)
    (n15 := 11087 / 10000) (nBand0 := 41721 / 12500) (nBand1 := 193019 / 100000)
    (nBand2 := 16267 / 40000) (nBot := 401023 / 50000) (Ntop := 165601 / 50000)
    (Nb0 := 245941 / 100000) (Nb1 := 8171 / 5000) (Nb2 := 518777 / 1000000) (Nbot := 23659 / 5000)
    (Nw := 215463 / 50000) (Nt := 1 / 1000000000)
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
/-- **The Jensen regime's cell `q ∈ [0.6600000, 0.6698804]`** (certificate total `22.54`). -/
theorem above_cell_24 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 33 / 50 ≤ q)
    (hq2 : q ≤ 1674701 / 2500000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 33 / 50) (qu := 1674701 / 2500000) (L0 := 23 / 2) (TS := 416889 / 10000)
    (nCen := 275047 / 1000000) (Nc := 106679 / 250000) (nC1 := 112083 / 100000)
    (nC2 := 112551 / 100000) (nK := 174783 / 100000) (nCoh := 124079 / 100000)
    (nTiny := 56919 / 5000000000000) (nKE := 208367 / 100000) (nJF := 115533 / 100000)
    (nE := 115011 / 2000000) (nB := 103571 / 100000) (nF := 356157 / 1000000)
    (nOm := 643267 / 1000000) (n15 := 109701 / 100000) (nBand0 := 67789 / 20000)
    (nBand1 := 200833 / 100000) (nBand2 := 457127 / 1000000) (nBot := 927627 / 100000)
    (Ntop := 340103 / 100000) (Nb0 := 252199 / 100000) (Nb1 := 169649 / 100000)
    (Nb2 := 22307 / 40000) (Nbot := 540741 / 100000) (Nw := 57179 / 12500) (Nt := 1 / 1000000000)
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
/-- **The Jensen regime's cell `q ∈ [0.6379310, 0.6600000]`** (certificate total `24.22`). -/
theorem above_cell_25 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 637931 / 1000000 ≤ q)
    (hq2 : q ≤ 33 / 50)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 637931 / 1000000) (qu := 33 / 50) (L0 := 23 / 2) (TS := 273113 / 10000)
    (nCen := 33213 / 125000) (Nc := 214737 / 500000) (nC1 := 55757 / 50000) (nC2 := 55973 / 50000)
    (nK := 173351 / 100000) (nCoh := 24737 / 20000) (nTiny := 209851 / 10000000000000)
    (nKE := 51531 / 25000) (nJF := 58807 / 50000) (nE := 632683 / 10000000) (nB := 51759 / 50000)
    (nF := 36867 / 100000) (nOm := 165563 / 250000) (n15 := 54487 / 50000)
    (nBand0 := 11584 / 3125) (nBand1 := 29207 / 12500) (nBand2 := 31299 / 50000)
    (nBot := 92787 / 10000) (Ntop := 45641 / 12500) (Nb0 := 139663 / 50000)
    (Nb1 := 194543 / 100000) (Nb2 := 701471 / 1000000) (Nbot := 114673 / 20000)
    (Nw := 584267 / 100000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_6 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.6189060, 0.6379310]`** (certificate total `23.31`). -/
theorem above_cell_26 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 309453 / 500000 ≤ q)
    (hq2 : q ≤ 637931 / 1000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 309453 / 500000) (qu := 637931 / 1000000) (L0 := 23 / 2) (TS := 273113 / 10000)
    (nCen := 49119 / 200000) (Nc := 209751 / 500000) (nC1 := 27439 / 25000) (nC2 := 11011 / 10000)
    (nK := 170193 / 100000) (nCoh := 12281 / 10000) (nTiny := 355547 / 10000000000000)
    (nKE := 503 / 250) (nJF := 119441 / 100000) (nE := 343489 / 5000000) (nB := 103399 / 100000)
    (nF := 37981 / 100000) (nOm := 678199 / 1000000) (n15 := 107429 / 100000)
    (nBand0 := 96759 / 25000) (nBand1 := 257853 / 100000) (nBand2 := 781999 / 1000000)
    (nBot := 120977 / 10000) (Ntop := 192661 / 50000) (Nb0 := 18657 / 6250) (Nb1 := 43003 / 20000)
    (Nb2 := 824949 / 1000000) (Nbot := 374793 / 50000) (Nw := 175591 / 25000)
    (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_6 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.6100000, 0.6189060]`** (certificate total `20.00`). -/
theorem above_cell_27 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 61 / 100 ≤ q)
    (hq2 : q ≤ 309453 / 500000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 61 / 100) (qu := 309453 / 500000) (L0 := 23 / 2) (TS := 273113 / 10000)
    (nCen := 57743 / 250000) (Nc := 25573 / 62500) (nC1 := 108197 / 100000)
    (nC2 := 108489 / 100000) (nK := 41879 / 25000) (nCoh := 122061 / 100000)
    (nTiny := 455083 / 10000000000000) (nKE := 3941 / 2000) (nJF := 30077 / 25000)
    (nE := 713971 / 10000000) (nB := 103297 / 100000) (nF := 19257 / 50000)
    (nOm := 685387 / 1000000) (n15 := 53091 / 50000) (nBand0 := 48423 / 12500)
    (nBand1 := 16563 / 6250) (nBand2 := 423397 / 500000) (nBot := 16897 / 1250)
    (Ntop := 393251 / 100000) (Nb0 := 303539 / 100000) (Nb1 := 55591 / 25000)
    (Nb2 := 218637 / 250000) (Nbot := 211367 / 25000) (Nw := 745817 / 100000)
    (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_6 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.5846154, 0.6100000]`** (certificate total `23.77`). -/
theorem above_cell_28 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 2923077 / 5000000 ≤ q)
    (hq2 : q ≤ 61 / 100)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 2923077 / 5000000) (qu := 61 / 100) (L0 := 23 / 2) (TS := 50459 / 2500)
    (nCen := 11347 / 50000) (Nc := 210163 / 500000) (nC1 := 21539 / 20000) (nC2 := 2699 / 2500)
    (nK := 83139 / 50000) (nCoh := 7607 / 6250) (nTiny := 919651 / 10000000000000)
    (nKE := 195137 / 100000) (nJF := 24563 / 20000) (nE := 796873 / 10000000)
    (nB := 103249 / 100000) (nF := 80149 / 200000) (nOm := 707273 / 1000000)
    (n15 := 13203 / 12500) (nBand0 := 53393 / 12500) (nBand1 := 158727 / 50000)
    (nBand2 := 11679 / 10000) (nBot := 149713 / 10000) (Ntop := 13336 / 3125)
    (Nb0 := 21643 / 6250) (Nb1 := 134329 / 50000) (Nb2 := 11423 / 10000) (Nbot := 4049 / 400)
    (Nw := 22461 / 2000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_5 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.5700000, 0.5846154]`** (certificate total `19.48`). -/
theorem above_cell_29 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 57 / 100 ≤ q)
    (hq2 : q ≤ 2923077 / 5000000)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 57 / 100) (qu := 2923077 / 5000000) (L0 := 23 / 2) (TS := 50459 / 2500)
    (nCen := 213769 / 1000000) (Nc := 51893 / 125000) (nC1 := 3304 / 3125)
    (nC2 := 105919 / 100000) (nK := 162799 / 100000) (nCoh := 60361 / 50000)
    (nTiny := 137891 / 1000000000000) (nKE := 94893 / 50000) (nJF := 24857 / 20000)
    (nE := 424451 / 5000000) (nB := 103113 / 100000) (nF := 205007 / 500000)
    (nOm := 71919 / 100000) (n15 := 833 / 800) (nBand0 := 17293 / 4000) (nBand1 := 168639 / 50000)
    (nBand2 := 132883 / 100000) (nBot := 177563 / 10000) (Ntop := 221107 / 50000)
    (Nb0 := 361293 / 100000) (Nb1 := 72647 / 25000) (Nb2 := 128363 / 100000)
    (Nbot := 62377 / 5000) (Nw := 136359 / 10000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_5 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.5437500, 0.5700000]`** (certificate total `23.37`). -/
theorem above_cell_30 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 87 / 160 ≤ q)
    (hq2 : q ≤ 57 / 100)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 87 / 160) (qu := 57 / 100) (L0 := 23 / 2) (TS := 165283 / 10000)
    (nCen := 209821 / 1000000) (Nc := 427943 / 1000000) (nC1 := 104747 / 100000)
    (nC2 := 1049 / 1000) (nK := 40207 / 25000) (nCoh := 30039 / 25000)
    (nTiny := 14271 / 50000000000) (nKE := 186771 / 100000) (nJF := 63487 / 50000)
    (nE := 475513 / 5000000) (nB := 20607 / 20000) (nF := 85441 / 200000)
    (nOm := 741437 / 1000000) (n15 := 2583 / 2500) (nBand0 := 468843 / 100000)
    (nBand1 := 100143 / 25000) (nBand2 := 35279 / 20000) (nBot := 103523 / 5000)
    (Ntop := 479317 / 100000) (Nb0 := 414159 / 100000) (Nb1 := 8959 / 2500) (Nb2 := 42143 / 25000)
    (Nbot := 20287 / 1250) (Nw := 257383 / 10000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_4 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.5400000, 0.5437500]`** (certificate total `13.38`). -/
theorem above_cell_31 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 27 / 50 ≤ q)
    (hq2 : q ≤ 87 / 160)
    (hx3 : 3 ≤ x) (hΛ : 23 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 27 / 50) (qu := 87 / 160) (L0 := 23 / 2) (TS := 165283 / 10000)
    (nCen := 202243 / 1000000) (Nc := 42199 / 100000) (nC1 := 102829 / 100000)
    (nC2 := 51459 / 50000) (nK := 157349 / 100000) (nCoh := 59573 / 50000)
    (nTiny := 7917 / 25000000000) (nKE := 181477 / 100000) (nJF := 127363 / 100000)
    (nE := 483293 / 5000000) (nB := 20579 / 20000) (nF := 10743 / 25000) (nOm := 743859 / 1000000)
    (n15 := 101979 / 100000) (nBand0 := 452963 / 100000) (nBand1 := 391949 / 100000)
    (nBand2 := 87321 / 50000) (nBot := 210321 / 10000) (Ntop := 4781 / 1000)
    (Nb0 := 101283 / 25000) (Nb1 := 177169 / 50000) (Nb2 := 167627 / 100000)
    (Nbot := 167889 / 10000) (Nw := 128809 / 5000) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_4 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
/-- **The Jensen regime's cell `q ∈ [0.5200000, 0.5400000]`** (certificate total `22.06`). -/
theorem above_cell_32 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hq1 : 13 / 25 ≤ q)
    (hq2 : q ≤ 27 / 50)
    (hx3 : 3 ≤ x) (hΛ : 25 / 2 ≤ Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_jensen_split hX
    (ql := 13 / 25) (qu := 27 / 50) (L0 := 25 / 2) (TS := 36241 / 2500) (nCen := 101639 / 500000)
    (Nc := 87371 / 200000) (nC1 := 102627 / 100000) (nC2 := 25677 / 25000) (nK := 156859 / 100000)
    (nCoh := 119003 / 100000) (nTiny := 275621 / 500000000000) (nKE := 180733 / 100000)
    (nJF := 129463 / 100000) (nE := 52699 / 500000) (nB := 823 / 800) (nF := 22169 / 50000)
    (nOm := 380423 / 500000) (n15 := 50899 / 50000) (nBand0 := 486461 / 100000)
    (nBand1 := 14111 / 3125) (nBand2 := 215923 / 100000) (nBot := 116687 / 5000)
    (Ntop := 63779 / 12500) (Nb0 := 228941 / 50000) (Nb1 := 426243 / 100000)
    (Nb2 := 26211 / 12500) (Nbot := 25851 / 1250) (Nw := 31267 / 500) (Nt := 1 / 1000000000)
    (by norm_num) hq1 hq2 (by norm_num) (by norm_num) hx3 hΛ (by norm_num)
    (fun z hz => aboveTS_3 (le_trans (by norm_num) hq1) (le_trans hq2 (by norm_num)) z hz)
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
