/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfChaosCellExplicit

/-!
# The chaos regime's cells above `q = ½`

Six cells of `δ = 2q - 1` in `[2·10⁻⁸, 3·10⁻⁴]` (`RMF.above_cell_chaos`) and the lowest cell
(`RMF.above_cell_chaos_low`) give the chaos regime
`RMF.integral_rpow_weightedRademacherSum_le_aboveChaos`: for `½ < q ≤ 0.50015` and
`(2q - 1)log log x ≥ 1`, `E|S(x)|^{2q} ≤ 25(2q - 1)^{-3/4}(log x)^{q(2q-1)}`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The chaos regime's cell `δ ∈ [2·10⁻⁸, 1·10⁻⁶]`** (certificate total `22.79`). -/
theorem above_cell_chaos_1 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hq1 : 50000001 / 100000000 ≤ q) (hq2 : q ≤ 1000001 / 2000000) (hx3 : 3 ≤ x)
    (hδΛ : 1 ≤ (2 * q - 1) * Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_chaos hX
    (ql := 50000001 / 100000000) (qu := 1000001 / 2000000) (L0 := 10000) (Xc := 60)
    (Nc := 8973 / 20000) (Nql := 16823 / 10000) (Ntop := 532629 / 100000) (NCb := 293993 / 50000)
    (NBot := 257313 / 10000) (NK := 16787 / 12500) (N12 := 100031 / 100000)
    (Nd := 316323 / 10000000000) (NMin := 200761 / 100) (NX := 8627 / 400000)
    (NW := 169499 / 10000) (Nsupp := 263301 / 100000000000000000000000) (Ntl := 87327 / 50000000)
    (NP := 158209 / 2500000000000000) (Ndd := 3126 / 3125) (n₀ := 3) (k := 25)
    (by norm_num) hq1 hq2 (by norm_num) hx3 hδΛ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by rw [mul_div_assoc', le_div_iff₀ (by norm_num)]; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by unfold cenHat; interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandConstHat pfC2Hat pfC1Hat; interval_decide (trust := kernel))
    (by unfold botHat pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC1Hat windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (min_le_of_right_le (by norm_num))
    (by interval_decide (trust := kernel))
    (by rw [div_le_iff₀ (by positivity)]; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The chaos regime's cell `δ ∈ [1·10⁻⁶, 1·10⁻⁵]`** (certificate total `23.22`). -/
theorem above_cell_chaos_2 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hq1 : 1000001 / 2000000 ≤ q) (hq2 : q ≤ 100001 / 200000) (hx3 : 3 ≤ x)
    (hδΛ : 1 ≤ (2 * q - 1) * Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_chaos hX
    (ql := 1000001 / 2000000) (qu := 100001 / 200000) (L0 := 10000) (Xc := 60)
    (Nc := 448649 / 1000000) (Nql := 16823 / 10000) (Ntop := 532629 / 100000)
    (NCb := 58799 / 10000) (NBot := 256177 / 10000) (NK := 134297 / 100000)
    (N12 := 100033 / 100000) (Nd := 88941 / 500000000) (NMin := 200761 / 100)
    (NX := 215917 / 10000000) (NW := 86231 / 5000) (Nsupp := 526601 / 10000000000000000000000000)
    (Ntl := 491289 / 50000000) (NP := 88967 / 25000000000000) (Ndd := 100041 / 100000) (n₀ := 2)
    (k := 20)
    (by norm_num) hq1 hq2 (by norm_num) hx3 hδΛ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by rw [mul_div_assoc', le_div_iff₀ (by norm_num)]; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by unfold cenHat; interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandConstHat pfC2Hat pfC1Hat; interval_decide (trust := kernel))
    (by unfold botHat pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC1Hat windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (min_le_of_right_le (by norm_num))
    (by interval_decide (trust := kernel))
    (by rw [div_le_iff₀ (by positivity)]; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The chaos regime's cell `δ ∈ [1·10⁻⁵, 5·10⁻⁵]`** (certificate total `23.33`). -/
theorem above_cell_chaos_3 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hq1 : 100001 / 200000 ≤ q) (hq2 : q ≤ 20001 / 40000) (hx3 : 3 ≤ x)
    (hδΛ : 1 ≤ (2 * q - 1) * Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_chaos hX
    (ql := 100001 / 200000) (qu := 20001 / 40000) (L0 := 10000) (Xc := 60) (Nc := 224323 / 500000)
    (Nql := 168229 / 100000) (Ntop := 133157 / 25000) (NCb := 294003 / 50000)
    (NBot := 30749 / 1250) (NK := 67151 / 50000) (N12 := 100043 / 100000)
    (Nd := 297391 / 500000000) (NMin := 75147 / 125) (NX := 108497 / 5000000) (NW := 86269 / 5000)
    (Nsupp := 526597 / 100000000000000000000000000) (Ntl := 16459 / 500000)
    (NP := 594931 / 10000000000000) (Ndd := 50037 / 50000) (n₀ := 2) (k := 16)
    (by norm_num) hq1 hq2 (by norm_num) hx3 hδΛ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by rw [mul_div_assoc', le_div_iff₀ (by norm_num)]; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by unfold cenHat; interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandConstHat pfC2Hat pfC1Hat; interval_decide (trust := kernel))
    (by unfold botHat pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC1Hat windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (min_le_of_left_le (by norm_num))
    (by interval_decide (trust := kernel))
    (by rw [div_le_iff₀ (by positivity)]; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The chaos regime's cell `δ ∈ [5·10⁻⁵, 1·10⁻⁴]`** (certificate total `23.09`). -/
theorem above_cell_chaos_4 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hq1 : 20001 / 40000 ≤ q) (hq2 : q ≤ 10001 / 20000) (hx3 : 3 ≤ x)
    (hδΛ : 1 ≤ (2 * q - 1) * Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_chaos hX
    (ql := 20001 / 40000) (qu := 10001 / 20000) (L0 := 10000) (Xc := 59) (Nc := 448629 / 1000000)
    (Nql := 5257 / 3125) (Ntop := 2663 / 500) (NCb := 29401 / 5000) (NBot := 205863 / 10000)
    (NK := 67153 / 50000) (N12 := 20011 / 20000) (Nd := 10003 / 10000000) (NMin := 15129 / 125)
    (NX := 54583 / 2500000) (NW := 85073 / 5000) (Nsupp := 71569 / 25000000000000000000000000)
    (Ntl := 277473 / 5000000) (NP := 200101 / 1000000000000) (Ndd := 20021 / 20000) (n₀ := 1)
    (k := 14)
    (by norm_num) hq1 hq2 (by norm_num) hx3 hδΛ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by rw [mul_div_assoc', le_div_iff₀ (by norm_num)]; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by unfold cenHat; interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandConstHat pfC2Hat pfC1Hat; interval_decide (trust := kernel))
    (by unfold botHat pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC1Hat windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (min_le_of_left_le (by norm_num))
    (by interval_decide (trust := kernel))
    (by rw [div_le_iff₀ (by positivity)]; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The chaos regime's cell `δ ∈ [1·10⁻⁴, 2·10⁻⁴]`** (certificate total `23.23`). -/
theorem above_cell_chaos_5 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hq1 : 10001 / 20000 ≤ q) (hq2 : q ≤ 5001 / 10000) (hx3 : 3 ≤ x)
    (hδΛ : 1 ≤ (2 * q - 1) * Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_chaos hX
    (ql := 10001 / 20000) (qu := 5001 / 10000) (L0 := 5000) (Xc := 29) (Nc := 448609 / 1000000)
    (Nql := 84109 / 50000) (Ntop := 133143 / 25000) (NCb := 117611 / 20000)
    (NBot := 205867 / 10000) (NK := 134317 / 100000) (N12 := 1251 / 1250) (Nd := 16823 / 10000000)
    (NMin := 610133 / 10000) (NX := 110503 / 5000000) (NW := 85007 / 5000)
    (Nsupp := 152957 / 10000000000000) (Ntl := 937821 / 10000000) (NP := 168247 / 250000000000)
    (Ndd := 100169 / 100000) (n₀ := 1) (k := 13)
    (by norm_num) hq1 hq2 (by norm_num) hx3 hδΛ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by rw [mul_div_assoc', le_div_iff₀ (by norm_num)]; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by unfold cenHat; interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandConstHat pfC2Hat pfC1Hat; interval_decide (trust := kernel))
    (by unfold botHat pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC1Hat windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (min_le_of_left_le (by norm_num))
    (by interval_decide (trust := kernel))
    (by rw [div_le_iff₀ (by positivity)]; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 8000000 in
-- the cell's numerals, each a short check
/-- **The chaos regime's cell `δ ∈ [2·10⁻⁴, 3·10⁻⁴]`** (certificate total `23.32`). -/
theorem above_cell_chaos_6 {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hq1 : 5001 / 10000 ≤ q) (hq2 : q ≤ 10003 / 20000) (hx3 : 3 ≤ x)
    (hδΛ : 1 ≤ (2 * q - 1) * Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) :=
  above_cell_chaos hX
    (ql := 5001 / 10000) (qu := 10003 / 20000) (L0 := 10000 / 3) (Xc := 19)
    (Nc := 448567 / 1000000) (Nql := 33641 / 20000) (Ntop := 532499 / 100000)
    (NCb := 588081 / 100000) (NBot := 191367 / 10000) (NK := 33581 / 25000) (N12 := 20021 / 20000)
    (Nd := 11401 / 5000000) (NMin := 310043 / 10000) (NX := 223661 / 10000000) (NW := 42443 / 2500)
    (Nsupp := 84219 / 500000000) (Ntl := 5109 / 40000) (NP := 136813 / 100000000000)
    (Ndd := 50111 / 50000) (n₀ := 1) (k := 12)
    (by norm_num) hq1 hq2 (by norm_num) hx3 hδΛ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by rw [mul_div_assoc', le_div_iff₀ (by norm_num)]; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)
    (by unfold cenHat; interval_decide (trust := kernel))
    (by unfold cenHat; interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandConstHat pfC2Hat pfC1Hat; interval_decide (trust := kernel))
    (by unfold botHat pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC1Hat windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (min_le_of_left_le (by norm_num))
    (by interval_decide (trust := kernel))
    (by rw [div_le_iff₀ (by positivity)]; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel))

set_option maxHeartbeats 1000000 in
-- seven cells, found by comparing q with their lower ends
/-- **The chaos regime above `½`.**  For `½ < q ≤ 0.50015` and `x ≥ 3` with
`(2q - 1)log log x ≥ 1`:

`E|S(x)|^{2q} ≤ 25(2q - 1)^{-3/4}(log x)^{q(2q-1)}`,

the cell of `q` among `RMF.above_cell_chaos_1`–`RMF.above_cell_chaos_6` and
`RMF.above_cell_chaos_low`. -/
theorem integral_rpow_weightedRademacherSum_le_aboveChaos {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hq0 : 1 / 2 < q) (hq1 : q ≤ 50015 / 100000) (hx3 : 3 ≤ x)
    (hδΛ : 1 ≤ (2 * q - 1) * Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) := by
  rcases le_or_gt (5001 / 10000) q with h6 | h6
  · exact above_cell_chaos_6 hX h6 (le_trans hq1 (by norm_num)) hx3 hδΛ
  rcases le_or_gt (10001 / 20000) q with h5 | h5
  · exact above_cell_chaos_5 hX h5 (le_trans (h6.le) (by norm_num)) hx3 hδΛ
  rcases le_or_gt (20001 / 40000) q with h4 | h4
  · exact above_cell_chaos_4 hX h4 (le_trans (h5.le) (by norm_num)) hx3 hδΛ
  rcases le_or_gt (100001 / 200000) q with h3 | h3
  · exact above_cell_chaos_3 hX h3 (le_trans (h4.le) (by norm_num)) hx3 hδΛ
  rcases le_or_gt (1000001 / 2000000) q with h2 | h2
  · exact above_cell_chaos_2 hX h2 (le_trans (h3.le) (by norm_num)) hx3 hδΛ
  rcases le_or_gt (50000001 / 100000000) q with h1 | h1
  · exact above_cell_chaos_1 hX h1 (le_trans (h2.le) (by norm_num)) hx3 hδΛ
  exact above_cell_chaos_low hX hq0 (le_trans (h1.le) (by norm_num)) hx3 hδΛ

end RMF
