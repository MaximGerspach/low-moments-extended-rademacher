/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.PNTFixedContour
import RMF.NumberTheory.ThetaFar

/-!
# The prime number theorem at constant `1` from `log t = 10²⁰`

`RMF.abs_psi_sub_le_fixedContour` at `ε = 10⁻¹⁹⁰` bounds `|ψ X - X|` by five terms, and for
`10²⁰/2 ≤ log X ≤ 10⁶⁰` they total at most `2.1·10⁻⁹·X/log²X`
(`RMF.abs_psi_sub_le_classical_range`): `30 log 2·εX log X` is at most `2.08·10⁻⁹·X/log²X`, the
other four at most `10⁻⁵⁰·X/log²X` each, through `10⁴²⁶ ≤ e^{1000}` (from `10³ ≤ e⁷`) and, for
the term in `X^{1-10⁻¹⁶}`, `log X ≥ 10²⁰/2`.  Mathlib's `|ψ - θ| ≤ 2√X log X` passes to `θ`, and
past `e^{10⁶⁰}` the effective prime number theorem `RMF.abs_theta_sub_le_far` takes over, since
`RMF.thetaFarThreshold ≤ e^{10⁶⁰}`.

## Main results

* `RMF.abs_theta_sub_le_classical`: `|θ t - t| ≤ t/log²t` for every `t ≥ exp(10²⁰)`.
* `RMF.abs_theta_sub_le_classical_of_exp_half_le`: the same for every `t ≥ exp(10²⁰/2)`.
-/

namespace RMF

open scoped Chebyshev

/-! ### Numerals -/

/-- `10³ ≤ e⁷`, from `e > 2.7182818283`. -/
lemma thousand_le_exp_seven : (1000 : ℝ) ≤ Real.exp 7 := by
  have h := Real.exp_one_gt_d9
  have h7 : Real.exp 7 = Real.exp 1 ^ 7 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h7]
  calc (1000 : ℝ) ≤ 2.7182818283 ^ 7 := by norm_num
    _ ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) h.le 7

/-- `10^{3n} ≤ e^{7n}`, from `RMF.thousand_le_exp_seven`. -/
lemma ten_pow_three_mul_le_exp (n : ℕ) : (10 : ℝ) ^ (3 * n) ≤ Real.exp (7 * n) := by
  rw [pow_mul, show (7 : ℝ) * n = n * 7 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num; exact thousand_le_exp_seven) n

/-- `10⁴²⁶ ≤ e^{1000}`. -/
lemma ten_pow_le_exp_thousand : (10 : ℝ) ^ 426 ≤ Real.exp 1000 := by
  have h : (10 : ℝ) ^ (3 * 142) ≤ Real.exp (7 * (142 : ℕ)) := ten_pow_three_mul_le_exp 142
  calc (10 : ℝ) ^ 426 = 10 ^ (3 * 142) := by norm_num
    _ ≤ Real.exp (7 * (142 : ℕ)) := h
    _ ≤ Real.exp 1000 := Real.exp_le_exp.2 (by norm_num)

/-- The term in `X^{1-10⁻¹⁶}`, against `X/log²X`: `e^{1000}e^{-L/10¹⁶}L² ≤ 8·10³²e^{-1500}` for
`L ≥ 10²⁰/2`, from `y²/2 ≤ e^y` at `y = L/(2·10¹⁶)`. -/
lemma exp_mul_exp_neg_mul_sq_le {L : ℝ} (hL : 10 ^ 20 / 2 ≤ L) :
    Real.exp 1000 * Real.exp (-(L / 10 ^ 16)) * L ^ 2 ≤ 8 * 10 ^ 32 * Real.exp (-1500) := by
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  set y : ℝ := L / (2 * 10 ^ 16) with hy
  have hy0 : 0 ≤ y := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hy0
  have hL2 : L ^ 2 ≤ 8 * 10 ^ 32 * Real.exp y := by
    have hLy : L ^ 2 = 8 * 10 ^ 32 * (y ^ 2 / 2) := by
      rw [hy]
      ring
    have hy2 : y ^ 2 / 2 ≤ Real.exp y := by linarith
    rw [hLy]
    exact mul_le_mul_of_nonneg_left hy2 (by norm_num)
  have hy2500 : 2500 ≤ y := by
    rw [hy, le_div_iff₀ (by norm_num)]
    linarith
  have hexp : Real.exp 1000 * Real.exp (-(L / 10 ^ 16)) * Real.exp y ≤ Real.exp (-1500) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hLy : L / 10 ^ 16 = 2 * y := by
      rw [hy]
      ring
    rw [hLy]
    linarith
  calc Real.exp 1000 * Real.exp (-(L / 10 ^ 16)) * L ^ 2
      ≤ Real.exp 1000 * Real.exp (-(L / 10 ^ 16)) * (8 * 10 ^ 32 * Real.exp y) :=
        mul_le_mul_of_nonneg_left hL2 (by positivity)
    _ = 8 * 10 ^ 32 * (Real.exp 1000 * Real.exp (-(L / 10 ^ 16)) * Real.exp y) := by ring
    _ ≤ 8 * 10 ^ 32 * Real.exp (-1500) := mul_le_mul_of_nonneg_left hexp (by norm_num)

/-- `ψ` against `θ`: `2√X log X ≤ 10⁻¹⁶·X/log²X` once `log X ≥ 10²⁰/2`, since
`√X = e^{L/2} ≥ L⁴/384`. -/
lemma two_mul_sqrt_mul_log_le {X : ℝ} (hX0 : 0 < X) (hL : 10 ^ 20 / 2 ≤ Real.log X) :
    2 * Real.sqrt X * Real.log X ≤ 1 / 10 ^ 16 * X / Real.log X ^ 2 := by
  set L := Real.log X with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  set e : ℝ := Real.exp (L / 2) with hedef
  have he0 : 0 < e := Real.exp_pos _
  have hsqrt : Real.sqrt X = e := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX0, hedef, ← hLdef]
    congr 1
    ring
  have hX : X = e * e := by
    rw [hedef, ← Real.exp_add, add_halves, hLdef, Real.exp_log hX0]
  have h4 : L ^ 4 ≤ 384 * e := by
    have h := Real.pow_div_factorial_le_exp (x := L / 2) (by positivity) 4
    have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hf, div_pow, ← hedef] at h
    linarith
  have h3 : 2 * 10 ^ 16 * L ^ 3 ≤ e := by
    calc 2 * 10 ^ 16 * L ^ 3 = 768 * 10 ^ 16 * L ^ 3 / 384 := by ring
      _ ≤ L * L ^ 3 / 384 := by
          gcongr
          linarith
      _ = L ^ 4 / 384 := by ring
      _ ≤ e := by linarith
  rw [hsqrt, le_div_iff₀ (by positivity), hX]
  calc 2 * e * L * L ^ 2 = (2 * 10 ^ 16 * L ^ 3) * e / 10 ^ 16 := by ring
    _ ≤ e * e / 10 ^ 16 := by gcongr
    _ = 1 / 10 ^ 16 * (e * e) := by ring

/-! ### `ψ` and `θ` on `10²⁰/2 ≤ log X ≤ 10⁶⁰` -/

set_option exponentiation.threshold 500 in
/-- **`|ψ X - X| ≤ 2.1·10⁻⁹·X/log²X` for `10²⁰/2 ≤ log X ≤ 10⁶⁰`**:
`RMF.abs_psi_sub_le_fixedContour` at `ε = 10⁻¹⁹⁰`.  Against `X/log²X` its first term is at most
`30 log 2·10⁻¹⁹⁰·10¹⁸⁰ ≤ 2.08·10⁻⁹`, and the other four are below `10⁻⁵⁰`
(`RMF.ten_pow_le_exp_thousand`, `RMF.exp_mul_exp_neg_mul_sq_le`). -/
theorem abs_psi_sub_le_classical_range {X : ℝ} (hX : Real.exp (10 ^ 20 / 2) ≤ X)
    (hXu : Real.log X ≤ 10 ^ 60) :
    |ψ X - X| ≤ 21 / 10 ^ 10 * X / Real.log X ^ 2 := by
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  set L := Real.log X with hLdef
  have hL : 10 ^ 20 / 2 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hX0]
    exact hX
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hXL : Real.exp L = X := Real.exp_log hX0
  -- `X ≥ 10¹⁹²`, so `Xε > 2` at `ε = 10⁻¹⁹⁰`
  have hXbig : (10 : ℝ) ^ 192 ≤ X := by
    have h : (10 : ℝ) ^ (3 * 64) ≤ Real.exp (7 * (64 : ℕ)) := ten_pow_three_mul_le_exp 64
    calc (10 : ℝ) ^ 192 = 10 ^ (3 * 64) := by norm_num
      _ ≤ Real.exp (7 * (64 : ℕ)) := h
      _ ≤ Real.exp (10 ^ 20 / 2) := Real.exp_le_exp.2 (by norm_num)
      _ ≤ X := hX
  set ε : ℝ := 1 / 10 ^ 190 with hεdef
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := by
    rw [hεdef]
    norm_num
  have hXε : 2 < X * ε := by
    have h1 : (10 : ℝ) ^ 192 * ε ≤ X * ε := mul_le_mul_of_nonneg_right hXbig hε0.le
    have h2 : (10 : ℝ) ^ 192 * ε = 100 := by
      rw [hεdef]
      norm_num
    linarith
  have hX3 : 3 < X := lt_of_lt_of_le (by norm_num) hXbig
  have h := abs_psi_sub_le_fixedContour X ε hX3 hε0 hε1 hXε
  -- the five terms, against `Y = X/L²`
  set Y : ℝ := X / L ^ 2 with hYdef
  have hL2 : 0 < L ^ 2 := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hXY : X = Y * L ^ 2 := by
    rw [hYdef]
    field_simp
  have hE := ten_pow_le_exp_thousand
  have hE0 : 0 < Real.exp 1000 := Real.exp_pos _
  have hL3 : L ^ 3 ≤ 10 ^ 180 := by
    calc L ^ 3 ≤ (10 ^ 60) ^ 3 := pow_le_pow_left₀ hL0.le hXu 3
      _ = 10 ^ 180 := by norm_num
  have hLsq : L ^ 2 ≤ 10 ^ 120 := by
    calc L ^ 2 ≤ (10 ^ 60) ^ 2 := pow_le_pow_left₀ hL0.le hXu 2
      _ = 10 ^ 120 := by norm_num
  have hlog2 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
  have hlog20 : 0 ≤ Real.log 2 := by positivity
  have t1 : 30 * Real.log 2 * ε * X * L ≤ 208 / 10 ^ 11 * Y := by
    have hc : 30 * Real.log 2 * ε * L ^ 3 ≤ 208 / 10 ^ 11 := by
      calc 30 * Real.log 2 * ε * L ^ 3 ≤ 30 * 0.6931471808 * ε * 10 ^ 180 := by gcongr
        _ ≤ 208 / 10 ^ 11 := by
            rw [hεdef]
            norm_num
    calc 30 * Real.log 2 * ε * X * L = (30 * Real.log 2 * ε * L ^ 3) * Y := by
          rw [hXY]
          ring
      _ ≤ 208 / 10 ^ 11 * Y := mul_le_mul_of_nonneg_right hc hY0
  have t2 : 2 * Real.log 2 * ε * X ≤ 1 / 10 ^ 50 * Y := by
    have hc : 2 * Real.log 2 * ε * L ^ 2 ≤ 1 / 10 ^ 50 := by
      calc 2 * Real.log 2 * ε * L ^ 2 ≤ 2 * 0.6931471808 * ε * 10 ^ 120 := by gcongr
        _ ≤ 1 / 10 ^ 50 := by
            rw [hεdef]
            norm_num
    calc 2 * Real.log 2 * ε * X = (2 * Real.log 2 * ε * L ^ 2) * Y := by
          rw [hXY]
          ring
      _ ≤ 1 / 10 ^ 50 * Y := mul_le_mul_of_nonneg_right hc hY0
  have t3 : 2088 * X * L / (ε * Real.exp 1000) ≤ 1 / 10 ^ 50 * Y := by
    have hc : 2088 * L ^ 3 / (ε * Real.exp 1000) ≤ 1 / 10 ^ 50 := by
      rw [div_le_iff₀ (by positivity)]
      calc 2088 * L ^ 3 ≤ 2088 * 10 ^ 180 := by gcongr
        _ ≤ 1 / 10 ^ 50 * (ε * 10 ^ 426) := by
            rw [hεdef]
            norm_num
        _ ≤ 1 / 10 ^ 50 * (ε * Real.exp 1000) := by gcongr
    calc 2088 * X * L / (ε * Real.exp 1000)
        = (2088 * L ^ 3 / (ε * Real.exp 1000)) * Y := by
          rw [hXY]
          ring
      _ ≤ 1 / 10 ^ 50 * Y := mul_le_mul_of_nonneg_right hc hY0
  have t4 : 33 * 10 ^ 15 * X / (ε * Real.exp 1000 ^ 2) ≤ 1 / 10 ^ 50 * Y := by
    have hE1 : Real.exp 1000 ≤ Real.exp 1000 ^ 2 :=
      le_self_pow₀ (Real.one_le_exp (by norm_num)) (by norm_num)
    have hc : 33 * 10 ^ 15 * L ^ 2 / (ε * Real.exp 1000 ^ 2) ≤ 1 / 10 ^ 50 := by
      rw [div_le_iff₀ (by positivity)]
      calc 33 * 10 ^ 15 * L ^ 2 ≤ 33 * 10 ^ 15 * 10 ^ 120 := by gcongr
        _ ≤ 1 / 10 ^ 50 * (ε * 10 ^ 426) := by
            rw [hεdef]
            norm_num
        _ ≤ 1 / 10 ^ 50 * (ε * Real.exp 1000 ^ 2) := by gcongr; linarith
    calc 33 * 10 ^ 15 * X / (ε * Real.exp 1000 ^ 2)
        = (33 * 10 ^ 15 * L ^ 2 / (ε * Real.exp 1000 ^ 2)) * Y := by
          rw [hXY]
          ring
      _ ≤ 1 / 10 ^ 50 * Y := mul_le_mul_of_nonneg_right hc hY0
  have t5 : 181 * 10 ^ 32 * Real.exp 1000 * X ^ zetaSmallTσ / ε ≤ 1 / 10 ^ 50 * Y := by
    have hσv : zetaSmallTσ = 1 - (1 / 10 : ℝ) ^ (16 : ℕ) := rfl
    have hXσ : X ^ zetaSmallTσ = X * Real.exp (-(L / 10 ^ 16)) := by
      have hLσ : L * zetaSmallTσ = L + -(L / 10 ^ 16) := by
        rw [hσv]
        ring
      rw [Real.rpow_def_of_pos hX0, ← hLdef, hLσ, Real.exp_add, hXL]
    have hk := exp_mul_exp_neg_mul_sq_le hL
    have hE15 : Real.exp (-1500) ≤ 1 / 10 ^ 426 := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by positivity) (le_trans hE (Real.exp_le_exp.2 (by norm_num)))
    have hc : 181 * 10 ^ 32 * (Real.exp 1000 * Real.exp (-(L / 10 ^ 16)) * L ^ 2) / ε
        ≤ 1 / 10 ^ 50 := by
      rw [div_le_iff₀ hε0]
      calc 181 * 10 ^ 32 * (Real.exp 1000 * Real.exp (-(L / 10 ^ 16)) * L ^ 2)
          ≤ 181 * 10 ^ 32 * (8 * 10 ^ 32 * Real.exp (-1500)) := by gcongr
        _ ≤ 181 * 10 ^ 32 * (8 * 10 ^ 32 * (1 / 10 ^ 426)) := by gcongr
        _ ≤ 1 / 10 ^ 50 * ε := by
            rw [hεdef]
            norm_num
    calc 181 * 10 ^ 32 * Real.exp 1000 * X ^ zetaSmallTσ / ε
        = 181 * 10 ^ 32 * (Real.exp 1000 * Real.exp (-(L / 10 ^ 16)) * L ^ 2) / ε * Y := by
          rw [hXσ, hXY]
          ring
      _ ≤ 1 / 10 ^ 50 * Y := mul_le_mul_of_nonneg_right hc hY0
  have hgoal : 21 / 10 ^ 10 * X / L ^ 2 = 21 / 10 ^ 10 * Y := by
    rw [hYdef]
    ring
  rw [hgoal]
  linarith

/-- **`|θ t - t| ≤ 2.2·10⁻⁹·t/log²t` for `10²⁰/2 ≤ log t ≤ 10⁶⁰`**:
`RMF.abs_psi_sub_le_classical_range`, and `|ψ - θ| ≤ 2√t log t`
(`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`), which is at most `10⁻¹⁶·t/log²t`
(`RMF.two_mul_sqrt_mul_log_le`). -/
theorem abs_theta_sub_le_classical_range {t : ℝ} (ht : Real.exp (10 ^ 20 / 2) ≤ t)
    (htu : Real.log t ≤ 10 ^ 60) :
    |θ t - t| ≤ 22 / 10 ^ 10 * t / Real.log t ^ 2 := by
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht
  have hL : 10 ^ 20 / 2 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le ht0]
    exact ht
  have ht1 : 1 ≤ t := le_trans (Real.one_le_exp (by norm_num)) ht
  have h1 := abs_psi_sub_le_classical_range ht htu
  have h2 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log ht1
  have h3 := two_mul_sqrt_mul_log_le ht0 hL
  have h4 := abs_sub_le (θ t) (ψ t) t
  rw [abs_sub_comm (θ t) (ψ t)] at h4
  have hsum : 21 / 10 ^ 10 * t / Real.log t ^ 2 + 1 / 10 ^ 16 * t / Real.log t ^ 2
      ≤ 22 / 10 ^ 10 * t / Real.log t ^ 2 := by
    rw [← add_div]
    gcongr
    linarith
  linarith

/-! ### `|θ t - t| ≤ t/log²t` from `exp(10²⁰)` -/

/-- `RMF.thetaFarThreshold ≤ e^{10⁶⁰}`: it is `max(e^{mediumPNTThresholdL}, e^{100}, e^{10⁶⁰})`,
and `mediumPNTThresholdL ≤ 10⁴⁵` (`RMF.mediumPNTThresholdL_le_sharp`). -/
lemma thetaFarThreshold_le_sharp : thetaFarThreshold ≤ Real.exp (10 ^ 60) := by
  unfold thetaFarThreshold thetaExpThreshold
  refine max_le (max_le (Real.exp_le_exp.2 ?_) (Real.exp_le_exp.2 (by norm_num))) le_rfl
  exact le_trans mediumPNTThresholdL_le_sharp (by norm_num)

/-- **The prime number theorem at constant `1` from `exp(10²⁰/2)`**: `|θ t - t| ≤ t/log²t` for
every `t ≥ exp(10²⁰/2)`.  `RMF.abs_theta_sub_le_classical_range` up to `log t = 10⁶⁰`, and
`RMF.abs_theta_sub_le_far` past it (`RMF.thetaFarThreshold_le_sharp`). -/
theorem abs_theta_sub_le_classical_of_exp_half_le :
    ∀ t : ℝ, Real.exp (10 ^ 20 / 2) ≤ t → |θ t - t| ≤ t / Real.log t ^ 2 := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht
  rcases le_or_gt (Real.log t) (10 ^ 60) with hu | hu
  · have h := abs_theta_sub_le_classical_range ht hu
    have hle : 22 / 10 ^ 10 * t / Real.log t ^ 2 ≤ t / Real.log t ^ 2 := by
      gcongr
      linarith
    linarith
  · have hfar : thetaFarThreshold ≤ t := by
      refine le_trans thetaFarThreshold_le_sharp ?_
      rw [← Real.exp_log ht0]
      exact Real.exp_le_exp.2 hu.le
    have h := abs_theta_sub_le_far.2 t hfar
    rwa [one_mul] at h

/-- **The prime number theorem at constant `1` from `exp(10²⁰)`**: `|θ t - t| ≤ t/log²t` for every
`t ≥ exp(10²⁰)`.  `RMF.abs_theta_sub_le_classical_of_exp_half_le`. -/
theorem abs_theta_sub_le_classical :
    ∀ t : ℝ, Real.exp (10 ^ 20) ≤ t → |θ t - t| ≤ t / Real.log t ^ 2 := fun t ht =>
  abs_theta_sub_le_classical_of_exp_half_le t (le_trans (Real.exp_le_exp.2 (by norm_num)) ht)

end RMF

