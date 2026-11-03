/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfCellExplicit

/-!
# The bottom's top windows over q-ranges

The bottom's nine top windows (`RMF.botTopSum`) bounded over each of the eleven q-ranges of the
Jensen regime's cells: each window without a split (`RMF.botWin_le_ns`) or with one
(`RMF.botWin_le_sp`), whichever is smaller, every numeral an `interval_decide` check.
-/

open MeasureTheory

namespace RMF

set_option maxHeartbeats 4000000 in
-- nine windows, each a short numeral check
/-- The bottom's nine top windows for `q ∈ [1/2, 51/100]`: at most `12.929`. -/
lemma aboveTS_1 {q : ℝ} (hqa : 1 / 2 ≤ q) (hqb : q ≤ 51 / 100) (z : ℕ)
    (hz : 2300 ≤ Real.log z) : botTopSum q z ≤ 129289 / 10000 := by
  refine le_trans (botTopSum_le_nine
    (botWin_le_ns 0 (kr := 0) (by norm_num) (ql := 1 / 2) (qu := 51 / 100)
      (Tl := 199999 / 100000) (Tinv := 100000 / 199999) (N := 599673 / 1000000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 1 (kr := 1) (by norm_num) (ql := 1 / 2) (qu := 51 / 100)
      (Tl := 367879 / 500000) (Tinv := 500000 / 367879) (N := 988691 / 1000000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 2 (kr := 2) (by norm_num) (ql := 1 / 2) (qu := 51 / 100)
      (Tl := 27067 / 100000) (Tinv := 100000 / 27067) (N := 5144 / 3125)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 3 (kr := 3) (by norm_num) (ql := 1 / 2) (qu := 51 / 100)
      (Tl := 49787 / 500000) (Tinv := 500000 / 49787) (N := 6853 / 2500)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_sp 4 (kr := 4) (by norm_num) (ql := 1 / 2) (qu := 51 / 100)
      (ulo := 150641 / 10000) (uhi := 409487 / 10000) (Np := 296627 / 100000) (B := 156019 / 50000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 5 (kr := 5) (by norm_num) (ql := 1 / 2) (qu := 51 / 100)
      (ulo := 81897 / 2000) (uhi := 11131 / 100) (Np := 13977 / 12500) (B := 14793 / 12500)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 6 (kr := 6) (by norm_num) (ql := 1 / 2) (qu := 51 / 100)
      (ulo := 111309 / 1000) (uhi := 75643 / 250) (Np := 868069 / 1000000) (B := 463411 / 500000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 7 (kr := 7) (by norm_num) (ql := 1 / 2) (qu := 51 / 100)
      (ulo := 302571 / 1000) (uhi := 205619 / 250) (Np := 200073 / 250000) (B := 215691 / 250000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 8 (kr := 8) (by norm_num) (ql := 1 / 2) (qu := 51 / 100)
      (ulo := 411237 / 500) (uhi := 223573 / 100) (Np := 388861 / 500000) (B := 169373 / 200000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))) (by norm_num)

set_option maxHeartbeats 4000000 in
-- nine windows, each a short numeral check
/-- The bottom's nine top windows for `q ∈ [51/100, 13/25]`: at most `13.351`. -/
lemma aboveTS_2 {q : ℝ} (hqa : 51 / 100 ≤ q) (hqb : q ≤ 13 / 25) (z : ℕ)
    (hz : 2300 ≤ Real.log z) : botTopSum q z ≤ 33377 / 2500 := by
  refine le_trans (botTopSum_le_nine
    (botWin_le_ns 0 (kr := 0) (by norm_num) (ql := 51 / 100) (qu := 13 / 25)
      (Tl := 199999 / 100000) (Tinv := 100000 / 199999) (N := 593567 / 1000000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 1 (kr := 1) (by norm_num) (ql := 51 / 100) (qu := 13 / 25)
      (Tl := 367879 / 500000) (Tinv := 500000 / 367879) (N := 49423 / 50000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 2 (kr := 2) (by norm_num) (ql := 51 / 100) (qu := 13 / 25)
      (Tl := 27067 / 100000) (Tinv := 100000 / 27067) (N := 166223 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 3 (kr := 3) (by norm_num) (ql := 51 / 100) (qu := 13 / 25)
      (Tl := 49787 / 500000) (Tinv := 500000 / 49787) (N := 34949 / 12500)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_sp 4 (kr := 4) (by norm_num) (ql := 51 / 100) (qu := 13 / 25)
      (ulo := 150641 / 10000) (uhi := 409487 / 10000) (Np := 73029 / 25000) (B := 64751 / 20000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 5 (kr := 5) (by norm_num) (ql := 51 / 100) (qu := 13 / 25)
      (ulo := 81897 / 2000) (uhi := 11131 / 100) (Np := 13823 / 12500) (B := 62047 / 50000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 6 (kr := 6) (by norm_num) (ql := 51 / 100) (qu := 13 / 25)
      (ulo := 111309 / 1000) (uhi := 75643 / 250) (Np := 858971 / 1000000) (B := 196251 / 200000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 7 (kr := 7) (by norm_num) (ql := 51 / 100) (qu := 13 / 25)
      (ulo := 302571 / 1000) (uhi := 205619 / 250) (Np := 395907 / 500000) (B := 922559 / 1000000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 8 (kr := 8) (by norm_num) (ql := 51 / 100) (qu := 13 / 25)
      (ulo := 411237 / 500) (uhi := 223573 / 100) (Np := 769429 / 1000000) (B := 914961 / 1000000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))) (by norm_num)

set_option maxHeartbeats 4000000 in
-- nine windows, each a short numeral check
/-- The bottom's nine top windows for `q ∈ [13/25, 27/50]`: at most `14.496`. -/
lemma aboveTS_3 {q : ℝ} (hqa : 13 / 25 ≤ q) (hqb : q ≤ 27 / 50) (z : ℕ)
    (hz : 2300 ≤ Real.log z) : botTopSum q z ≤ 36241 / 2500 := by
  refine le_trans (botTopSum_le_nine
    (botWin_le_ns 0 (kr := 0) (by norm_num) (ql := 13 / 25) (qu := 27 / 50)
      (Tl := 199999 / 100000) (Tinv := 100000 / 199999) (N := 146881 / 250000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 1 (kr := 1) (by norm_num) (ql := 13 / 25) (qu := 27 / 50)
      (Tl := 367879 / 500000) (Tinv := 500000 / 367879) (N := 98823 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 2 (kr := 2) (by norm_num) (ql := 13 / 25) (qu := 27 / 50)
      (Tl := 27067 / 100000) (Tinv := 100000 / 27067) (N := 84751 / 50000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 3 (kr := 3) (by norm_num) (ql := 13 / 25) (qu := 27 / 50)
      (Tl := 49787 / 500000) (Tinv := 500000 / 49787) (N := 145433 / 50000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_sp 4 (kr := 4) (by norm_num) (ql := 13 / 25) (qu := 27 / 50)
      (ulo := 150641 / 10000) (uhi := 409487 / 10000) (Np := 293139 / 100000) (B := 72543 / 20000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 5 (kr := 5) (by norm_num) (ql := 13 / 25) (qu := 27 / 50)
      (ulo := 81897 / 2000) (uhi := 11131 / 100) (Np := 109511 / 100000) (B := 27809 / 20000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 6 (kr := 6) (by norm_num) (ql := 13 / 25) (qu := 27 / 50)
      (ulo := 111309 / 1000) (uhi := 75643 / 250) (Np := 106221 / 125000) (B := 111967 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 7 (kr := 7) (by norm_num) (ql := 13 / 25) (qu := 27 / 50)
      (ulo := 302571 / 1000) (uhi := 205619 / 250) (Np := 78327 / 100000) (B := 107521 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 8 (kr := 8) (by norm_num) (ql := 13 / 25) (qu := 27 / 50)
      (ulo := 411237 / 500) (uhi := 223573 / 100) (Np := 190271 / 250000) (B := 108999 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))) (by norm_num)

set_option maxHeartbeats 4000000 in
-- nine windows, each a short numeral check
/-- The bottom's nine top windows for `q ∈ [27/50, 57/100]`: at most `16.528`. -/
lemma aboveTS_4 {q : ℝ} (hqa : 27 / 50 ≤ q) (hqb : q ≤ 57 / 100) (z : ℕ)
    (hz : 2300 ≤ Real.log z) : botTopSum q z ≤ 165283 / 10000 := by
  refine le_trans (botTopSum_le_nine
    (botWin_le_ns 0 (kr := 0) (by norm_num) (ql := 27 / 50) (qu := 57 / 100)
      (Tl := 199999 / 100000) (Tinv := 100000 / 199999) (N := 287811 / 500000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 1 (kr := 1) (by norm_num) (ql := 27 / 50) (qu := 57 / 100)
      (Tl := 367879 / 500000) (Tinv := 500000 / 367879) (N := 123471 / 125000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 2 (kr := 2) (by norm_num) (ql := 27 / 50) (qu := 57 / 100)
      (Tl := 27067 / 100000) (Tinv := 100000 / 27067) (N := 87271 / 50000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 3 (kr := 3) (by norm_num) (ql := 27 / 50) (qu := 57 / 100)
      (Tl := 49787 / 500000) (Tinv := 500000 / 49787) (N := 77159 / 25000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_sp 4 (kr := 4) (by norm_num) (ql := 27 / 50) (qu := 57 / 100)
      (ulo := 150641 / 10000) (uhi := 409487 / 10000) (Np := 287669 / 100000) (B := 53221 / 12500)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 5 (kr := 5) (by norm_num) (ql := 27 / 50) (qu := 57 / 100)
      (ulo := 81897 / 2000) (uhi := 11131 / 100) (Np := 26749 / 25000) (B := 16609 / 10000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 6 (kr := 6) (by norm_num) (ql := 27 / 50) (qu := 57 / 100)
      (ulo := 111309 / 1000) (uhi := 75643 / 250) (Np := 20777 / 25000) (B := 138149 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 7 (kr := 7) (by norm_num) (ql := 27 / 50) (qu := 57 / 100)
      (ulo := 302571 / 1000) (uhi := 205619 / 250) (Np := 766009 / 1000000) (B := 137343 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 8 (kr := 8) (by norm_num) (ql := 27 / 50) (qu := 57 / 100)
      (ulo := 411237 / 500) (uhi := 223573 / 100) (Np := 744259 / 1000000) (B := 144311 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))) (by norm_num)

set_option maxHeartbeats 4000000 in
-- nine windows, each a short numeral check
/-- The bottom's nine top windows for `q ∈ [57/100, 61/100]`: at most `20.184`. -/
lemma aboveTS_5 {q : ℝ} (hqa : 57 / 100 ≤ q) (hqb : q ≤ 61 / 100) (z : ℕ)
    (hz : 2300 ≤ Real.log z) : botTopSum q z ≤ 50459 / 2500 := by
  refine le_trans (botTopSum_le_nine
    (botWin_le_ns 0 (kr := 0) (by norm_num) (ql := 57 / 100) (qu := 61 / 100)
      (Tl := 199999 / 100000) (Tinv := 100000 / 199999) (N := 279109 / 500000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 1 (kr := 1) (by norm_num) (ql := 57 / 100) (qu := 61 / 100)
      (Tl := 367879 / 500000) (Tinv := 500000 / 367879) (N := 987077 / 1000000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 2 (kr := 2) (by norm_num) (ql := 57 / 100) (qu := 61 / 100)
      (Tl := 27067 / 100000) (Tinv := 100000 / 27067) (N := 22687 / 12500)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 3 (kr := 3) (by norm_num) (ql := 57 / 100) (qu := 61 / 100)
      (Tl := 49787 / 500000) (Tinv := 500000 / 49787) (N := 33403 / 10000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_sp 4 (kr := 4) (by norm_num) (ql := 57 / 100) (qu := 61 / 100)
      (ulo := 150641 / 10000) (uhi := 409487 / 10000) (Np := 8561 / 3125) (B := 528177 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 5 (kr := 5) (by norm_num) (ql := 57 / 100) (qu := 61 / 100)
      (ulo := 81897 / 2000) (uhi := 11131 / 100) (Np := 102869 / 100000) (B := 1343 / 625)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 6 (kr := 6) (by norm_num) (ql := 57 / 100) (qu := 61 / 100)
      (ulo := 111309 / 1000) (uhi := 75643 / 250) (Np := 802461 / 1000000) (B := 188073 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 7 (kr := 7) (by norm_num) (ql := 57 / 100) (qu := 61 / 100)
      (ulo := 302571 / 1000) (uhi := 205619 / 250) (Np := 73977 / 100000) (B := 98457 / 50000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 8 (kr := 8) (by norm_num) (ql := 57 / 100) (qu := 61 / 100)
      (ulo := 411237 / 500) (uhi := 223573 / 100) (Np := 23 / 32) (B := 218243 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))) (by norm_num)

set_option maxHeartbeats 4000000 in
-- nine windows, each a short numeral check
/-- The bottom's nine top windows for `q ∈ [61/100, 33/50]`: at most `27.311`. -/
lemma aboveTS_6 {q : ℝ} (hqa : 61 / 100 ≤ q) (hqb : q ≤ 33 / 50) (z : ℕ)
    (hz : 2300 ≤ Real.log z) : botTopSum q z ≤ 273113 / 10000 := by
  refine le_trans (botTopSum_le_nine
    (botWin_le_ns 0 (kr := 0) (by norm_num) (ql := 61 / 100) (qu := 33 / 50)
      (Tl := 199999 / 100000) (Tinv := 100000 / 199999) (N := 53583 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 1 (kr := 1) (by norm_num) (ql := 61 / 100) (qu := 33 / 50)
      (Tl := 367879 / 500000) (Tinv := 500000 / 367879) (N := 197231 / 200000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 2 (kr := 2) (by norm_num) (ql := 61 / 100) (qu := 33 / 50)
      (Tl := 27067 / 100000) (Tinv := 100000 / 27067) (N := 95289 / 50000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 3 (kr := 3) (by norm_num) (ql := 61 / 100) (qu := 33 / 50)
      (Tl := 49787 / 500000) (Tinv := 500000 / 49787) (N := 368729 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_sp 4 (kr := 4) (by norm_num) (ql := 61 / 100) (qu := 33 / 50)
      (ulo := 150641 / 10000) (uhi := 409487 / 10000) (Np := 250951 / 100000) (B := 87633 / 12500)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 5 (kr := 5) (by norm_num) (ql := 61 / 100) (qu := 33 / 50)
      (ulo := 81897 / 2000) (uhi := 11131 / 100) (Np := 972301 / 1000000) (B := 154069 / 50000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 6 (kr := 6) (by norm_num) (ql := 61 / 100) (qu := 33 / 50)
      (ulo := 111309 / 1000) (uhi := 75643 / 250) (Np := 763511 / 1000000) (B := 36253 / 12500)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 7 (kr := 7) (by norm_num) (ql := 61 / 100) (qu := 33 / 50)
      (ulo := 302571 / 1000) (uhi := 205619 / 250) (Np := 176087 / 250000) (B := 326889 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 8 (kr := 8) (by norm_num) (ql := 61 / 100) (qu := 33 / 50)
      (ulo := 411237 / 500) (uhi := 223573 / 100) (Np := 342213 / 500000) (B := 390779 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))) (by norm_num)

set_option maxHeartbeats 4000000 in
-- nine windows, each a short numeral check
/-- The bottom's nine top windows for `q ∈ [33/50, 18/25]`: at most `41.689`. -/
lemma aboveTS_7 {q : ℝ} (hqa : 33 / 50 ≤ q) (hqb : q ≤ 18 / 25) (z : ℕ)
    (hz : 2300 ≤ Real.log z) : botTopSum q z ≤ 416889 / 10000 := by
  refine le_trans (botTopSum_le_nine
    (botWin_le_ns 0 (kr := 0) (by norm_num) (ql := 33 / 50) (qu := 18 / 25)
      (Tl := 199999 / 100000) (Tinv := 100000 / 199999) (N := 254551 / 500000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 1 (kr := 1) (by norm_num) (ql := 33 / 50) (qu := 18 / 25)
      (Tl := 367879 / 500000) (Tinv := 500000 / 367879) (N := 197001 / 200000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 2 (kr := 2) (by norm_num) (ql := 33 / 50) (qu := 18 / 25)
      (Tl := 27067 / 100000) (Tinv := 100000 / 27067) (N := 1263 / 625)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 3 (kr := 3) (by norm_num) (ql := 33 / 50) (qu := 18 / 25)
      (Tl := 49787 / 500000) (Tinv := 500000 / 49787) (N := 415159 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 4 (kr := 4) (by norm_num) (ql := 33 / 50) (qu := 18 / 25)
      (Tl := 45789 / 1250000) (Tinv := 1250000 / 45789) (N := 213229 / 25000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_sp 5 (kr := 5) (by norm_num) (ql := 33 / 50) (qu := 18 / 25)
      (ulo := 81897 / 2000) (uhi := 11131 / 100) (Np := 902443 / 1000000) (B := 251857 / 50000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 6 (kr := 6) (by norm_num) (ql := 33 / 50) (qu := 18 / 25)
      (ulo := 111309 / 1000) (uhi := 75643 / 250) (Np := 357077 / 500000) (B := 523081 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 7 (kr := 7) (by norm_num) (ql := 33 / 50) (qu := 18 / 25)
      (ulo := 302571 / 1000) (uhi := 205619 / 250) (Np := 164949 / 250000) (B := 163161 / 25000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 8 (kr := 8) (by norm_num) (ql := 33 / 50) (qu := 18 / 25)
      (ulo := 411237 / 500) (uhi := 223573 / 100) (Np := 641387 / 1000000) (B := 865717 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))) (by norm_num)

set_option maxHeartbeats 4000000 in
-- nine windows, each a short numeral check
/-- The bottom's nine top windows for `q ∈ [18/25, 79/100]`: at most `81.460`. -/
lemma aboveTS_8 {q : ℝ} (hqa : 18 / 25 ≤ q) (hqb : q ≤ 79 / 100) (z : ℕ)
    (hz : 2300 ≤ Real.log z) : botTopSum q z ≤ 814603 / 10000 := by
  refine le_trans (botTopSum_le_nine
    (botWin_le_ns 0 (kr := 0) (by norm_num) (ql := 18 / 25) (qu := 79 / 100)
      (Tl := 199999 / 100000) (Tinv := 100000 / 199999) (N := 7481 / 15625)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 1 (kr := 1) (by norm_num) (ql := 18 / 25) (qu := 79 / 100)
      (Tl := 367879 / 500000) (Tinv := 500000 / 367879) (N := 491813 / 500000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 2 (kr := 2) (by norm_num) (ql := 18 / 25) (qu := 79 / 100)
      (Tl := 27067 / 100000) (Tinv := 100000 / 27067) (N := 108189 / 50000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 3 (kr := 3) (by norm_num) (ql := 18 / 25) (qu := 79 / 100)
      (Tl := 49787 / 500000) (Tinv := 500000 / 49787) (N := 238383 / 50000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 4 (kr := 4) (by norm_num) (ql := 18 / 25) (qu := 79 / 100)
      (Tl := 45789 / 1250000) (Tinv := 1250000 / 45789) (N := 105051 / 10000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_sp 5 (kr := 5) (by norm_num) (ql := 18 / 25) (qu := 79 / 100)
      (ulo := 81897 / 2000) (uhi := 11131 / 100) (Np := 204577 / 250000) (B := 96599 / 10000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 6 (kr := 6) (by norm_num) (ql := 18 / 25) (qu := 79 / 100)
      (ulo := 111309 / 1000) (uhi := 75643 / 250) (Np := 654897 / 1000000) (B := 114529 / 10000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 7 (kr := 7) (by norm_num) (ql := 18 / 25) (qu := 79 / 100)
      (ulo := 302571 / 1000) (uhi := 205619 / 250) (Np := 151653 / 250000) (B := 163827 / 10000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 8 (kr := 8) (by norm_num) (ql := 18 / 25) (qu := 79 / 100)
      (ulo := 411237 / 500) (uhi := 223573 / 100) (Np := 9221 / 15625) (B := 124923 / 5000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))) (by norm_num)

set_option maxHeartbeats 4000000 in
-- nine windows, each a short numeral check
/-- The bottom's nine top windows for `q ∈ [79/100, 43/50]`: at most `196.483`. -/
lemma aboveTS_9 {q : ℝ} (hqa : 79 / 100 ≤ q) (hqb : q ≤ 43 / 50) (z : ℕ)
    (hz : 2300 ≤ Real.log z) : botTopSum q z ≤ 196483 / 1000 := by
  refine le_trans (botTopSum_le_nine
    (botWin_le_ns 0 (kr := 0) (by norm_num) (ql := 79 / 100) (qu := 43 / 50)
      (Tl := 199999 / 100000) (Tinv := 100000 / 199999) (N := 222843 / 500000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 1 (kr := 1) (by norm_num) (ql := 79 / 100) (qu := 43 / 50)
      (Tl := 367879 / 500000) (Tinv := 500000 / 367879) (N := 49101 / 50000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 2 (kr := 2) (by norm_num) (ql := 79 / 100) (qu := 43 / 50)
      (Tl := 27067 / 100000) (Tinv := 100000 / 27067) (N := 231689 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 3 (kr := 3) (by norm_num) (ql := 79 / 100) (qu := 43 / 50)
      (Tl := 49787 / 500000) (Tinv := 500000 / 49787) (N := 136879 / 25000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 4 (kr := 4) (by norm_num) (ql := 79 / 100) (qu := 43 / 50)
      (Tl := 45789 / 1250000) (Tinv := 1250000 / 45789) (N := 129387 / 10000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_sp 5 (kr := 5) (by norm_num) (ql := 79 / 100) (qu := 43 / 50)
      (ulo := 81897 / 2000) (uhi := 11131 / 100) (Np := 722507 / 1000000) (B := 197241 / 10000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 6 (kr := 6) (by norm_num) (ql := 79 / 100) (qu := 43 / 50)
      (ulo := 111309 / 1000) (uhi := 75643 / 250) (Np := 73377 / 125000) (B := 136281 / 5000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 7 (kr := 7) (by norm_num) (ql := 79 / 100) (qu := 43 / 50)
      (ulo := 302571 / 1000) (uhi := 205619 / 250) (Np := 17059 / 31250) (B := 228001 / 5000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 8 (kr := 8) (by norm_num) (ql := 79 / 100) (qu := 43 / 50)
      (ulo := 411237 / 500) (uhi := 223573 / 100) (Np := 16617 / 31250) (B := 81547 / 1000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))) (by norm_num)

set_option maxHeartbeats 4000000 in
-- nine windows, each a short numeral check
/-- The bottom's nine top windows for `q ∈ [43/50, 93/100]`: at most `586.081`. -/
lemma aboveTS_10 {q : ℝ} (hqa : 43 / 50 ≤ q) (hqb : q ≤ 93 / 100) (z : ℕ)
    (hz : 2300 ≤ Real.log z) : botTopSum q z ≤ 586081 / 1000 := by
  refine le_trans (botTopSum_le_nine
    (botWin_le_ns 0 (kr := 0) (by norm_num) (ql := 43 / 50) (qu := 93 / 100)
      (Tl := 199999 / 100000) (Tinv := 100000 / 199999) (N := 103719 / 250000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 1 (kr := 1) (by norm_num) (ql := 43 / 50) (qu := 93 / 100)
      (Tl := 367879 / 500000) (Tinv := 500000 / 367879) (N := 15319 / 15625)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 2 (kr := 2) (by norm_num) (ql := 43 / 50) (qu := 93 / 100)
      (Tl := 27067 / 100000) (Tinv := 100000 / 27067) (N := 124041 / 50000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 3 (kr := 3) (by norm_num) (ql := 43 / 50) (qu := 93 / 100)
      (Tl := 49787 / 500000) (Tinv := 500000 / 49787) (N := 125753 / 20000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 4 (kr := 4) (by norm_num) (ql := 43 / 50) (qu := 93 / 100)
      (Tl := 45789 / 1250000) (Tinv := 1250000 / 45789) (N := 79681 / 5000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 5 (kr := 5) (by norm_num) (ql := 43 / 50) (qu := 93 / 100)
      (Tl := 67379 / 5000000) (Tinv := 5000000 / 67379) (N := 80781 / 2000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_sp 6 (kr := 6) (by norm_num) (ql := 43 / 50) (qu := 93 / 100)
      (ulo := 111309 / 1000) (uhi := 75643 / 250) (Np := 104333 / 200000) (B := 357341 / 5000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 7 (kr := 7) (by norm_num) (ql := 43 / 50) (qu := 93 / 100)
      (ulo := 302571 / 1000) (uhi := 205619 / 250) (Np := 487473 / 1000000) (B := 142597 / 1000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))
    (botWin_le_sp 8 (kr := 8) (by norm_num) (ql := 43 / 50) (qu := 93 / 100)
      (ulo := 411237 / 500) (uhi := 223573 / 100) (Np := 475619 / 1000000) (B := 15247 / 50)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by interval_decide (trust := kernel))
      (by norm_num) (by norm_num) hz
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by unfold windowWHatB splitST2; interval_decide (trust := kernel))
      (by interval_decide (trust := kernel)))) (by norm_num)

set_option maxHeartbeats 4000000 in
-- nine windows, each a short numeral check
/-- The bottom's nine top windows for `q ∈ [93/100, 1]`: at most `1696.840`. -/
lemma aboveTS_11 {q : ℝ} (hqa : 93 / 100 ≤ q) (hqb : q ≤ 1) (z : ℕ)
    (hz : 2300 ≤ Real.log z) : botTopSum q z ≤ 42421 / 25 := by
  refine le_trans (botTopSum_le_nine
    (botWin_le_ns 0 (kr := 0) (by norm_num) (ql := 93 / 100) (qu := 1)
      (Tl := 199999 / 100000) (Tinv := 100000 / 199999) (N := 386197 / 1000000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 1 (kr := 1) (by norm_num) (ql := 93 / 100) (qu := 1)
      (Tl := 367879 / 500000) (Tinv := 500000 / 367879) (N := 195763 / 200000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 2 (kr := 2) (by norm_num) (ql := 93 / 100) (qu := 1)
      (Tl := 27067 / 100000) (Tinv := 100000 / 27067) (N := 66409 / 25000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 3 (kr := 3) (by norm_num) (ql := 93 / 100) (qu := 1)
      (Tl := 49787 / 500000) (Tinv := 500000 / 49787) (N := 722071 / 100000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 4 (kr := 4) (by norm_num) (ql := 93 / 100) (qu := 1)
      (Tl := 45789 / 1250000) (Tinv := 1250000 / 45789) (N := 4907 / 250)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 5 (kr := 5) (by norm_num) (ql := 93 / 100) (qu := 1)
      (Tl := 67379 / 5000000) (Tinv := 5000000 / 67379) (N := 106709 / 2000)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 6 (kr := 6) (by norm_num) (ql := 93 / 100) (qu := 1)
      (Tl := 495749 / 100000000) (Tinv := 100000000 / 495749) (N := 18129 / 125)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 7 (kr := 7) (by norm_num) (ql := 93 / 100) (qu := 1)
      (Tl := 22797 / 12500000) (Tinv := 12500000 / 22797) (N := 197119 / 500)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))
    (botWin_le_ns 8 (kr := 8) (by norm_num) (ql := 93 / 100) (qu := 1)
      (Tl := 167731 / 250000000) (Tinv := 250000000 / 167731) (N := 21433 / 20)
      (by norm_num) hqa hqb (by norm_num) (by interval_decide (trust := kernel))
      (by norm_num) hz
      (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel)))) (by norm_num)

end RMF
