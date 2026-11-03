/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.Extended.Basics
import RMF.UniformLower.SmallXExplicit

/-!
# The extended sum below `½` for small `x`, elementary (E1)

`RMF.le_integral_rpow_normalisedSum_compMultExtension_small_explicit`: for a Rademacher family,
`x ≥ 3` with `Λ = log log x ≤ 67.17` and `0 < q < ½`,
`10⁻¹⁰min{Λ, 1/(1-2q)}Λ^{-q/2} ≤ E|Y(x)|^{2q}`, `Y(x) = x^{-1/2}∑_{n≤x} X^e(n)`.  The weighted
sum's E1 lemmas (`RMF/UniformLower/SmallXExplicit.lean`) give `2T ≤` their bound for `S`, `T` the
target; the bounds for `Y` (`RMF/UniformLower/Extended/Basics.lean`) lose less than that `2`, and
each loss is bounded in the statement of the lemma that pays it, so the margins are certified:

* `x < 9`: there `Λ ≤ 1`, so `T ≤ 10⁻¹⁰`, and `E|Y|^{2q} ≥ ¼(1 + log x)^{-1} ≥ 1/36`;
* NH, `(1-2q)Λ ≤ 17`: Hölder at `½(1 + log x)^{-(1-2q)}`, `×1`;
* otherwise the cell of `RMF.smallCellsY_spec`.  F for `1 - 2q ≥ u_F`: the floor with
  `∑ 1/p ≤ 2#/x`, a loss `2^{-q} ≥ 7/10`, `×1.4` (`RMF.smallTarget_le_floor_extended`).  I below:
  interpolation against `C = 30`, a loss `r^{1+w}(5/6)^w ≥ 33/40`, `w = (1-2q)/(2b-1) ≤ 21/20`,
  `r = ⌊√x⌋/√x ≥ 1 - 10⁻⁸`: `×1.65` (`RMF.smallTarget_le_interp_extended`), the binding margin.
-/

open MeasureTheory

namespace RMF

/-! ### The cells, with `u_F ≤ (21/20)(2b - 1)` -/

/-- **Every cell, for the extended sum**: `RMF.smallCells_spec`, the same four cells by name, with
also `u_F ≤ (21/20)(2b - 1)` (the cells have `u_F/(2b - 1) ≤ 1.0368`), which bounds the loss of
interpolating against `C = 30`. -/
theorem smallCellsY_spec {Λ : ℝ} (h17 : 17 ≤ Λ) (hΛ : Λ ≤ 67.17) :
    ∃ Λ₀ Λ₁ uF b : ℝ, 1 ≤ Λ₀ ∧ Λ₀ ≤ Λ ∧ Λ ≤ Λ₁ ∧ 8 ≤ Λ₁ ∧ 0 < uF ∧ 1 / 2 < b ∧ b ≤ 1
      ∧ 0 ≤ smallPhiF uF Λ₀ Λ₁ ∧ (uF * Λ₁ ≤ 17 ∨ 0 ≤ smallPhiI uF Λ₀ Λ₁ b)
      ∧ uF ≤ 21 / 20 * (2 * b - 1) := by
  rcases le_or_gt Λ 40 with h0 | h0
  · exact ⟨17, 40, 0.425, 1, by norm_num, h17, h0, by norm_num, by norm_num, by norm_num,
      by norm_num, le_trans (by norm_num) smallCellF_0, Or.inl (by norm_num), by norm_num⟩
  rcases le_or_gt Λ 64 with h1 | h1
  · exact ⟨40, 64, 0.38675, 0.6915, by norm_num, h0.le, h1, by norm_num, by norm_num,
      by norm_num, by norm_num, le_trans (by norm_num) smallCellF_1,
      Or.inr (le_trans (by norm_num) smallCellI_1), by norm_num⟩
  rcases le_or_gt Λ 67 with h2 | h2
  · exact ⟨64, 67, 0.38825, 0.6875, by norm_num, h1.le, h2, by norm_num, by norm_num,
      by norm_num, by norm_num, le_trans (by norm_num) smallCellF_2,
      Or.inr (le_trans (by norm_num) smallCellI_2), by norm_num⟩
  exact ⟨67, 67.17, 0.38825, 0.68725, by norm_num, h2.le, hΛ, by norm_num, by norm_num,
    by norm_num, by norm_num, le_trans (by norm_num) smallCellF_3,
    Or.inr (le_trans (by norm_num) smallCellI_3), by norm_num⟩

/-! ### The regimes' losses -/

/-- **F for the extended sum, certified `×1.4`**: for `L > 0` and `q ≤ ½`, if
`2T ≤ 2^{-(1-2q)}3^{-(1-q)}(0.23/L)^q` (the weighted sum's F) then
`(7/5)T ≤ 2^{-(1-2q)}3^{-(1-q)}(0.23/(2L))^q`: the second is `2^{-q} ≥ 2^{-1/2} ≥ 7/10` times
the first. -/
lemma smallTarget_le_floor_extended {T q L : ℝ} (hL : 0 < L) (hq : q ≤ 1 / 2)
    (hT : 2 * T ≤ (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (23 / (100 * L)) ^ q) :
    7 / 5 * T ≤ (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (23 / (200 * L)) ^ q := by
  have hA : 0 < 23 / (100 * L) := by positivity
  have e : (23 / (200 * L)) ^ q = (1 / 2 : ℝ) ^ q * (23 / (100 * L)) ^ q := by
    rw [← Real.mul_rpow (by norm_num) hA.le]
    congr 1
    field_simp
    ring
  have hhalf : 7 / 10 ≤ (1 / 2 : ℝ) ^ q := by
    have h1 : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ q :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hq
    have h2 : (7 / 10 : ℝ) ≤ (1 / 2 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    linarith
  have hF0 : 0 ≤ (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (23 / (100 * L)) ^ q := by
    positivity
  have hmul := mul_le_mul_of_nonneg_right hhalf hF0
  rw [e]
  nlinarith

/-- **I for the extended sum, certified `×1.65`**: for `U > 0`, `½ < b`,
`1 - 2q ≤ (21/20)(2b - 1)` and `1 - 10⁻⁸ ≤ r ≤ 1`, if `2T ≤ (25U)^{-w}`, `w = (1-2q)/(2b-1)` (the
weighted sum's I) then `(33/20)T ≤ r^{(2b-2q)/(2b-1)}(30U)^{-w}`: the second is
`r^{1+w}(5/6)^w ≥ r³(5/6)^{21/20} ≥ 33/40` times the first. -/
lemma smallTarget_le_interp_extended {T U r q b : ℝ} (hU : 0 < U)
    (hb : 1 / 2 < b) (hw : 1 - 2 * q ≤ 21 / 20 * (2 * b - 1)) (hr : 1 - 1 / 10 ^ 8 ≤ r)
    (hr1 : r ≤ 1) (hT : 2 * T ≤ (25 * U) ^ (-((1 - 2 * q) / (2 * b - 1)))) :
    33 / 20 * T
      ≤ r ^ ((2 * b - 2 * q) / (2 * b - 1)) * (30 * U) ^ (-((1 - 2 * q) / (2 * b - 1))) := by
  have hδ : 0 < 2 * b - 1 := by linarith
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have he : (2 * b - 2 * q) / (2 * b - 1) = 1 + (1 - 2 * q) / (2 * b - 1) := by
    field_simp
    ring
  set w := (1 - 2 * q) / (2 * b - 1) with hwdef
  have hw1 : w ≤ 21 / 20 := by
    rw [hwdef, div_le_iff₀ hδ]
    linarith
  -- `(30U)^{-w} = (6/5)^{-w}(25U)^{-w}`
  have hsplit : (30 * U) ^ (-w) = (6 / 5 : ℝ) ^ (-w) * (25 * U) ^ (-w) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    ring
  -- `(6/5)^{-w} ≥ (6/5)^{-21/20} ≥ 0.8257`
  have h65 : (0.8257 : ℝ) ≤ (6 / 5 : ℝ) ^ (-w) := by
    have h1 : (6 / 5 : ℝ) ^ (-(21 / 20 : ℝ)) ≤ (6 / 5 : ℝ) ^ (-w) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (0.8257 : ℝ) ≤ (6 / 5 : ℝ) ^ (-(21 / 20 : ℝ)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      interval_decide (trust := kernel)
    linarith
  -- `r^{1+w} ≥ r³ ≥ (1 - 10⁻⁸)³`
  have hr3 : (1 - 1 / 10 ^ 8 : ℝ) ^ 3 ≤ r ^ (1 + w) := by
    have h1 : r ^ (3 : ℝ) ≤ r ^ (1 + w) :=
      Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
    have h2 : (1 - 1 / 10 ^ 8 : ℝ) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ (by norm_num) hr 3
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
    linarith
  have hloss : 33 / 40 ≤ r ^ (1 + w) * (6 / 5 : ℝ) ^ (-w) :=
    calc (33 / 40 : ℝ) ≤ (1 - 1 / 10 ^ 8 : ℝ) ^ 3 * 0.8257 := by norm_num
      _ ≤ r ^ (1 + w) * (6 / 5 : ℝ) ^ (-w) :=
          mul_le_mul hr3 h65 (by norm_num) (Real.rpow_nonneg hr0.le _)
  have hI0 : 0 ≤ (25 * U) ^ (-w) := Real.rpow_nonneg (by positivity) _
  have hmul := mul_le_mul_of_nonneg_right hloss hI0
  rw [he, hsplit]
  nlinarith

/-! ### The theorem -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Below `½` with `c = 10⁻¹⁰` for `3 ≤ x` with `log log x ≤ 67.17`, for the extended sum
(E1)**: for every Rademacher `X`, every such `x` and every `0 < q < ½`,
`10⁻¹⁰min{log log x, 1/(1-2q)}(log log x)^{-q/2} ≤ E|Y(x)|^{2q}`: directly for `x < 9`, Hölder
where `(1-2q)log log x ≤ 17`, else the cell of `RMF.smallCellsY_spec`, F for `1 - 2q ≥ u_F` and I
at the cell's `b` below; margins `×1`, `×1.4` and `×1.65`. -/
theorem le_integral_rpow_normalisedSum_compMultExtension_small_explicit {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 3 ≤ x)
    (hΛ : Real.log (Real.log x) ≤ 67.17) (hq0 : 0 < q) (hq : q < 1 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  have hx0 : 0 < x := by linarith
  have hL1 : 1 < Real.log x :=
    (Real.lt_log_iff_exp_lt (by linarith)).2 (by linarith [Real.exp_one_lt_d9])
  have hΛ0 : 0 < Real.log (Real.log x) := Real.log_pos hL1
  have hT0 : 0 ≤ 1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
      * Real.log (Real.log x) ^ (-(q / 2))) :=
    mul_nonneg (by norm_num) (mul_nonneg (le_min hΛ0.le (inv_nonneg.2 (by linarith)))
      (Real.rpow_nonneg hΛ0.le _))
  have hr1 := floor_sqrt_div_sqrt_le_one hx0
  rcases lt_or_ge x 9 with h9 | h9
  · -- `x < 9`: `log log x ≤ 1`, so `T ≤ 10⁻¹⁰`; and `E|Y|^{2q} ≥ ¼·(1/9)`
    have hΛ1 : Real.log (Real.log x) ≤ 1 := by
      have he : (9 : ℝ) ≤ Real.exp (Real.exp 1) := by interval_decide (trust := kernel)
      rw [Real.log_le_iff_le_exp (by linarith), Real.log_le_iff_le_exp hx0]
      linarith
    have hT : min (Real.log (Real.log x)) (1 - 2 * q)⁻¹ * Real.log (Real.log x) ^ (-(q / 2))
        ≤ 1 :=
      calc min (Real.log (Real.log x)) (1 - 2 * q)⁻¹ * Real.log (Real.log x) ^ (-(q / 2))
          ≤ Real.log (Real.log x) * Real.log (Real.log x) ^ (-(q / 2)) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hΛ0.le _)
        _ = Real.log (Real.log x) ^ (1 + -(q / 2)) := by rw [Real.rpow_add hΛ0, Real.rpow_one]
        _ ≤ 1 := Real.rpow_le_one hΛ0.le hΛ1 (by linarith)
    have hr2 : 1 / 4 ≤ ((⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x) ^ (2 - 2 * q) := by
      have hr12 := half_le_floor_sqrt_div_sqrt (by linarith : (1 : ℝ) ≤ x)
      have hr0 : 0 < (⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x := by linarith
      have h := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith : 2 - 2 * q ≤ 2)
      rw [Real.rpow_two] at h
      nlinarith [mul_le_mul hr12 hr12 (by norm_num) hr0.le]
    have hpow : 1 / 9 ≤ (1 + Real.log x) ^ (-(1 - 2 * q)) := by
      have hL8 : Real.log x ≤ 8 := by
        have := Real.log_le_sub_one_of_pos hx0
        linarith
      have h1 : (1 + Real.log x) ^ (-1 : ℝ) ≤ (1 + Real.log x) ^ (-(1 - 2 * q)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have h2 : (1 / 9 : ℝ) ≤ (1 + Real.log x)⁻¹ := by
        rw [one_div]
        exact inv_anti₀ (by linarith) (by linarith)
      rw [Real.rpow_neg_one] at h1
      linarith
    have hY := le_integral_rpow_normalisedSum_compMultExtension_holder_floor hX
      (by linarith : (1 : ℝ) ≤ x) hq0 hq
    have hprod := mul_le_mul hr2 hpow (by norm_num) (le_trans (by norm_num) hr2)
    have hT' := mul_le_mul_of_nonneg_left hT (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 10)
    linarith
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) 17 with hNH | hNH
  · -- NH: Hölder, at half the weighted sum's bound
    have hS := two_mul_smallTarget_le_holder hq0 hq hL1 (by linarith) hNH
    have hY := le_integral_rpow_normalisedSum_compMultExtension_holder hX h9 hq0 hq
    linarith
  have hΛ17 : 17 < Real.log (Real.log x) := by
    have : (1 - 2 * q) * Real.log (Real.log x) ≤ 1 * Real.log (Real.log x) :=
      mul_le_mul_of_nonneg_right (by linarith) hΛ0.le
    linarith
  obtain ⟨Λ₀, Λ₁, uF, b, hΛ₀1, hΛ₀, hΛ₁, hΛ₁8, huF0, hb, hb1, hF, hI, huFb⟩ :=
    smallCellsY_spec hΛ17.le hΛ
  -- `x ≥ exp(e^{17}) ≥ 10^{16}`
  have h1 : Real.exp 17 < Real.log x := (Real.lt_log_iff_exp_lt (by linarith)).1 hΛ17
  have h2 : (40 : ℝ) ≤ Real.exp 17 := by interval_decide (trust := kernel)
  have h3 : Real.exp 40 < x := (Real.lt_log_iff_exp_lt (by linarith)).1 (by linarith)
  have h4 : (10 : ℝ) ^ 16 ≤ Real.exp 40 := by interval_decide (trust := kernel)
  have hx16 : (10 : ℝ) ^ 16 ≤ x := by linarith
  rcases le_or_gt uF (1 - 2 * q) with hu | hu
  · -- F: the floor with the bridge `∑ 1/p ≤ 2#/x`
    have hS := two_mul_smallTarget_le_floor hq0 hq (by linarith) hΛ₀1 hΛ₀ hΛ₁ hΛ₁8 huF0 hu hF
    have hY := smallTarget_le_floor_extended (by linarith) hq.le hS
    have hE := le_integral_rpow_normalisedSum_compMultExtension_floor_small hX hx16 hq0 hq.le
    linarith
  · rcases hI with hI | hI
    · -- no I in this cell: `u_FΛ₁ ≤ 17 < uΛ`
      have h1 : (1 - 2 * q) * Real.log (Real.log x) ≤ uF * Λ₁ :=
        mul_le_mul hu.le hΛ₁ hΛ0.le huF0.le
      linarith
    · -- I: interpolation against `C = 30` at the cell's `b`, with `r ≥ 1 - 10⁻⁸`
      have hS := two_mul_smallTarget_le_interp hq0 hq hL1 hΛ₀1 hΛ₀ hΛ₁ hb hb1 hNH hu.le hI
      have hr : 1 - 1 / 10 ^ 8 ≤ (⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x := by
        have hs : (10 : ℝ) ^ 8 ≤ Real.sqrt x := by
          have h := Real.sqrt_le_sqrt hx16
          rwa [show (10 : ℝ) ^ 16 = (10 ^ 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
        have hinv : (Real.sqrt x)⁻¹ ≤ 1 / 10 ^ 8 := by
          rw [inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) hs
        linarith [one_sub_inv_sqrt_le_floor_sqrt_div_sqrt hx0]
      have hδ : 0 < 2 * b - 1 := by linarith
      have hU0 : 0 < Real.log x ^ (b * (2 * b - 1))
          * min (2 * b - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ) :=
        mul_pos (Real.rpow_pos_of_pos (by linarith) _)
          (Real.rpow_pos_of_pos (lt_min (inv_pos.2 hδ) hΛ0) _)
      have hY := smallTarget_le_interp_extended hU0 hb (by linarith) hr hr1 hS
      have hE := le_integral_rpow_normalisedSum_compMultExtension_interp hX hx hq0 hq hb hb1
      linarith

end RMF
