/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfCells1Explicit
import RMF.Weighted.AboveHalfCells2Explicit
import RMF.Weighted.AboveHalfCells3Explicit
import RMF.Weighted.AboveHalfCells4Explicit

/-!
# The Jensen regime above `q = ½`

Every `q ∈ [0.50015, 1]` lies in one of the forty-two cells of
`RMF/Weighted/AboveHalfCells*Explicit.lean`, so `E|S(x)|^{2q} ≤ 25(2q - 1)^{-3/4}(log x)^{q(2q-1)}`
wherever `Λ ≥ 11.5` and `(2q-1)Λ ≥ 1`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
-- forty-two cells, found by comparing q with their lower ends
/-- **The Jensen regime above `½`.**  For `0.50015 ≤ q ≤ 1` and `x ≥ 3` with
`Λ = log log x ≥ 11.5` and `(2q - 1)Λ ≥ 1`:

`E|S(x)|^{2q} ≤ 25(2q - 1)^{-3/4}(log x)^{q(2q-1)}`,

the cell of `q` among `RMF.above_cell_1`–`RMF.above_cell_42`. -/
theorem integral_rpow_weightedRademacherSum_le_aboveJensen {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hq0 : 50015 / 100000 ≤ q) (hq1 : q ≤ 1) (hx3 : 3 ≤ x)
    (hΛ : 23 / 2 ≤ Real.log (Real.log x))
    (hδΛ : 1 ≤ (2 * q - 1) * Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) := by
  have hΛu : ∀ qu : ℝ, q ≤ qu → 1 / 2 < q →
      1 / (2 * qu - 1) ≤ Real.log (Real.log x) := by
    intro qu hqu hq
    have hd : 0 < 2 * q - 1 := by linarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hq12 : 1 / 2 < q := by linarith
  rcases le_or_gt (9672897 / 10000000) q with h0 | h0
  · exact above_cell_1 hX h0 hq1 hx3 hΛ
  have hqu1 : q ≤ 9672897 / 10000000 := h0.le
  rcases le_or_gt (4725189 / 5000000) q with h1 | h1
  · exact above_cell_2 hX h1 hqu1 hx3 hΛ
  have hqu2 : q ≤ 4725189 / 5000000 := h1.le
  rcases le_or_gt (93 / 100) q with h2 | h2
  · exact above_cell_3 hX h2 hqu2 hx3 hΛ
  have hqu3 : q ≤ 93 / 100 := h2.le
  rcases le_or_gt (4547619 / 5000000) q with h3 | h3
  · exact above_cell_4 hX h3 hqu3 hx3 hΛ
  have hqu4 : q ≤ 4547619 / 5000000 := h3.le
  rcases le_or_gt (8900227 / 10000000) q with h4 | h4
  · exact above_cell_5 hX h4 hqu4 hx3 hΛ
  have hqu5 : q ≤ 8900227 / 10000000 := h4.le
  rcases le_or_gt (1753667 / 2000000) q with h5 | h5
  · exact above_cell_6 hX h5 hqu5 hx3 hΛ
  have hqu6 : q ≤ 1753667 / 2000000 := h5.le
  rcases le_or_gt (8640903 / 10000000) q with h6 | h6
  · exact above_cell_7 hX h6 hqu6 hx3 hΛ
  have hqu7 : q ≤ 8640903 / 10000000 := h6.le
  rcases le_or_gt (43 / 50) q with h7 | h7
  · exact above_cell_8 hX h7 hqu7 hx3 hΛ
  have hqu8 : q ≤ 43 / 50 := h7.le
  rcases le_or_gt (8428571 / 10000000) q with h8 | h8
  · exact above_cell_9 hX h8 hqu8 hx3 hΛ
  have hqu9 : q ≤ 8428571 / 10000000 := h8.le
  rcases le_or_gt (4132653 / 5000000) q with h9 | h9
  · exact above_cell_10 hX h9 hqu9 hx3 hΛ
  have hqu10 : q ≤ 4132653 / 5000000 := h9.le
  rcases le_or_gt (1630977 / 2000000) q with h10 | h10
  · exact above_cell_11 hX h10 hqu10 hx3 hΛ
  have hqu11 : q ≤ 1630977 / 2000000 := h10.le
  rcases le_or_gt (4024099 / 5000000) q with h11 | h11
  · exact above_cell_12 hX h11 hqu11 hx3 hΛ
  have hqu12 : q ≤ 4024099 / 5000000 := h11.le
  rcases le_or_gt (7945119 / 10000000) q with h12 | h12
  · exact above_cell_13 hX h12 hqu12 hx3 hΛ
  have hqu13 : q ≤ 7945119 / 10000000 := h12.le
  rcases le_or_gt (79 / 100) q with h13 | h13
  · exact above_cell_14 hX h13 hqu13 hx3 hΛ
  have hqu14 : q ≤ 79 / 100 := h13.le
  rcases le_or_gt (1552381 / 2000000) q with h14 | h14
  · exact above_cell_15 hX h14 hqu14 hx3 hΛ
  have hqu15 : q ≤ 1552381 / 2000000 := h14.le
  rcases le_or_gt (3815193 / 5000000) q with h15 | h15
  · exact above_cell_16 hX h15 hqu15 hx3 hΛ
  have hqu16 : q ≤ 3815193 / 5000000 := h15.le
  rcases le_or_gt (750513 / 1000000) q with h16 | h16
  · exact above_cell_17 hX h16 hqu16 hx3 hΛ
  have hqu17 : q ≤ 750513 / 1000000 := h16.le
  rcases le_or_gt (3692919 / 5000000) q with h17 | h17
  · exact above_cell_18 hX h17 hqu17 hx3 hΛ
  have hqu18 : q ≤ 3692919 / 5000000 := h17.le
  rcases le_or_gt (7272227 / 10000000) q with h18 | h18
  · exact above_cell_19 hX h18 hqu18 hx3 hΛ
  have hqu19 : q ≤ 7272227 / 10000000 := h18.le
  rcases le_or_gt (18 / 25) q with h19 | h19
  · exact above_cell_20 hX h19 hqu19 hx3 hΛ
  have hqu20 : q ≤ 18 / 25 := h19.le
  rcases le_or_gt (7018349 / 10000000) q with h20 | h20
  · exact above_cell_21 hX h20 hqu20 hx3 hΛ
  have hqu21 : q ≤ 7018349 / 10000000 := h20.le
  rcases le_or_gt (428231 / 625000) q with h21 | h21
  · exact above_cell_22 hX h21 hqu21 hx3 hΛ
  have hqu22 : q ≤ 428231 / 625000 := h21.le
  rcases le_or_gt (1674701 / 2500000) q with h22 | h22
  · exact above_cell_23 hX h22 hqu22 hx3 hΛ
  have hqu23 : q ≤ 1674701 / 2500000 := h22.le
  rcases le_or_gt (33 / 50) q with h23 | h23
  · exact above_cell_24 hX h23 hqu23 hx3 hΛ
  have hqu24 : q ≤ 33 / 50 := h23.le
  rcases le_or_gt (637931 / 1000000) q with h24 | h24
  · exact above_cell_25 hX h24 hqu24 hx3 hΛ
  have hqu25 : q ≤ 637931 / 1000000 := h24.le
  rcases le_or_gt (309453 / 500000) q with h25 | h25
  · exact above_cell_26 hX h25 hqu25 hx3 hΛ
  have hqu26 : q ≤ 309453 / 500000 := h25.le
  rcases le_or_gt (61 / 100) q with h26 | h26
  · exact above_cell_27 hX h26 hqu26 hx3 hΛ
  have hqu27 : q ≤ 61 / 100 := h26.le
  rcases le_or_gt (2923077 / 5000000) q with h27 | h27
  · exact above_cell_28 hX h27 hqu27 hx3 hΛ
  have hqu28 : q ≤ 2923077 / 5000000 := h27.le
  rcases le_or_gt (57 / 100) q with h28 | h28
  · exact above_cell_29 hX h28 hqu28 hx3 hΛ
  have hqu29 : q ≤ 57 / 100 := h28.le
  rcases le_or_gt (87 / 160) q with h29 | h29
  · exact above_cell_30 hX h29 hqu29 hx3 hΛ
  have hqu30 : q ≤ 87 / 160 := h29.le
  rcases le_or_gt (27 / 50) q with h30 | h30
  · exact above_cell_31 hX h30 hqu30 hx3 hΛ
  have hqu31 : q ≤ 27 / 50 := h30.le
  rcases le_or_gt (13 / 25) q with h31 | h31
  · exact above_cell_32 hX h31 hqu31 hx3
      (le_trans (by norm_num : (25 / 2 : ℝ) ≤ 1 / (2 * (27 / 50) - 1))
      (hΛu _ hqu31 hq12))
  have hqu32 : q ≤ 13 / 25 := h31.le
  rcases le_or_gt (51 / 100) q with h32 | h32
  · exact above_cell_33 hX h32 hqu32 hx3
      (le_trans (by norm_num : (25 : ℝ) ≤ 1 / (2 * (13 / 25) - 1))
      (hΛu _ hqu32 hq12))
  have hqu33 : q ≤ 51 / 100 := h32.le
  rcases le_or_gt (101 / 200) q with h33 | h33
  · exact above_cell_34 hX h33 hqu33 hx3
      (le_trans (by norm_num : (50 : ℝ) ≤ 1 / (2 * (51 / 100) - 1))
      (hΛu _ hqu33 hq12))
  have hqu34 : q ≤ 101 / 200 := h33.le
  rcases le_or_gt (201 / 400) q with h34 | h34
  · exact above_cell_35 hX h34 hqu34 hx3
      (le_trans (by norm_num : (100 : ℝ) ≤ 1 / (2 * (101 / 200) - 1))
      (hΛu _ hqu34 hq12))
  have hqu35 : q ≤ 201 / 400 := h34.le
  rcases le_or_gt (401 / 800) q with h35 | h35
  · exact above_cell_36 hX h35 hqu35 hx3
      (le_trans (by norm_num : (200 : ℝ) ≤ 1 / (2 * (201 / 400) - 1))
      (hΛu _ hqu35 hq12))
  have hqu36 : q ≤ 401 / 800 := h35.le
  rcases le_or_gt (1251953 / 2500000) q with h36 | h36
  · exact above_cell_37 hX h36 hqu36 hx3
      (le_trans (by norm_num : (400 : ℝ) ≤ 1 / (2 * (401 / 800) - 1))
      (hΛu _ hqu36 hq12))
  have hqu37 : q ≤ 1251953 / 2500000 := h36.le
  rcases le_or_gt (2502441 / 5000000) q with h37 | h37
  · exact above_cell_38 hX h37 hqu37 hx3
      (le_trans (by norm_num : (1250000 / 1953 : ℝ) ≤ 1 / (2 * (1251953 / 2500000) - 1))
      (hΛu _ hqu37 hq12))
  have hqu38 : q ≤ 2502441 / 5000000 := h37.le
  rcases le_or_gt (5003051 / 10000000) q with h38 | h38
  · exact above_cell_39 hX h38 hqu38 hx3
      (le_trans (by norm_num : (2500000 / 2441 : ℝ) ≤ 1 / (2 * (2502441 / 5000000) - 1))
      (hΛu _ hqu38 hq12))
  have hqu39 : q ≤ 5003051 / 10000000 := h38.le
  rcases le_or_gt (5002179 / 10000000) q with h39 | h39
  · exact above_cell_40 hX h39 hqu39 hx3
      (le_trans (by norm_num : (5000000 / 3051 : ℝ) ≤ 1 / (2 * (5003051 / 10000000) - 1))
      (hΛu _ hqu39 hq12))
  have hqu40 : q ≤ 5002179 / 10000000 := h39.le
  rcases le_or_gt (1250419 / 2500000) q with h40 | h40
  · exact above_cell_41 hX h40 hqu40 hx3
      (le_trans (by norm_num : (5000000 / 2179 : ℝ) ≤ 1 / (2 * (5002179 / 10000000) - 1))
      (hΛu _ hqu40 hq12))
  have hqu41 : q ≤ 1250419 / 2500000 := h40.le
  exact above_cell_42 hX (le_trans (by norm_num) hq0) hqu41 hx3
      (le_trans (by norm_num : (1250000 / 419 : ℝ) ≤ 1 / (2 * (1250419 / 2500000) - 1))
      (hΛu _ hqu41 hq12))

end RMF
