/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.LowerAllX
import RMF.UniformLower.Extended.Basics

/-!
# The extended sum's explicit lower bounds from `q = ½` up, for every `x ≥ 3`

The twin of `RMF/UniformLower/LowerAllX.lean` for `Y(x) = x^{-1/2}∑_{n≤x} X^e(n)`
(`normalisedSum (fun ω => compMultExtension fun p => X p ω) x`).  No chain for `Y` is needed
here: with `R(x)` the fractional-part sum, `S = Y + R` almost surely
(`RMF.ae_normalisedSum_compMultExtension_eq`), and `E|Y| ≥ ⌊√x⌋/√x ≥ ½`.  With `Λ = log log x`
and `δ = 2q - 1`:

* `q = ½`: `10⁻⁸Λ^{3/4} ≤ E|Y(x)|` for every `x ≥ 3`
  (`RMF.integral_norm_normalisedSum_compMultExtension_ge_explicit`), from `E|Y| ≥ ½` for
  `Λ ≤ 10⁹` and beyond from `E|Y| ≥ E|S| - E|R| ≥ 10⁻⁷Λ^{3/4} - 20Λ^{-1/4}`;
* Bonami–Beckner: `Y(x)` is a Rademacher chaos with the coefficients `⌊√(x/n_A)⌋/√x`
  (`RMF.ae_normalisedSum_compMultExtension_eq_chaosSum`), at least `0.99n_A^{-1/2}` where
  `n_A ≤ x/100²`, so `(9/100)(log x)^{q(2q-1)} ≤ E|Y(x)|^{2q}` for `x ≥ e^{415}`
  (`RMF.le_integral_rpow_normalisedSum_compMultExtension_bb_explicit`);
* the sliver, `δ < 10⁻¹¹` and `δΛ ≥ 1`: the weighted sum's sliver at `10⁻⁸`
  (`RMF.le_integral_rpow_sliverRegime_eight`, with the numeral `RMF.finalSErr8`) and Minkowski,
  `‖Y‖_{2q} ≥ ‖S‖_{2q} - ‖R‖_{2q}` with `E|R|^{2q} ≤ 1`;
* Lyapunov from `q = ½` where `δΛ ≤ 1`, and `E|Y|^{2q} ≥ ¼` where the target is at most `¼`.

Together, `RMF.integral_rpow_normalisedSum_compMultExtension_ge_aboveHalf_explicit`:
`10⁻¹⁰(log x)^{q(2q-1)}min{1/(2q-1), Λ}^{3/4} ≤ E|Y(x)|^{2q}` for `½ < q ≤ 1` and every `x ≥ 3`.
-/

open MeasureTheory

namespace RMF

/-! ### The weighted sum's sliver at `10⁻⁸`: the numerals -/

/-- S, the rest at `10⁻⁸`: `RMF.finalSErr` with `10⁻⁸` for `10⁻¹⁰` (certified
`PhiSl ≥ 12.2·10⁻⁸`). -/
theorem finalSErr8 : 1 / 10 ^ 8 + 33 * Real.exp (-32) + 16 * Real.exp (-3000)
    ≤ Real.exp (-15.917) := by
  interval_decide (trust := kernel)

/-- **S from its certificate, at `10⁻⁸`**: `RMF.PhiSl_ge_of_cert` with `10⁻⁸` for `10⁻¹⁰`,
`PhiSl(q) ≥ 10⁻⁸` on `(½, ½ + 1/(2·10⁸)]`. -/
theorem PhiSl_ge_eight_of_cert {lam : ℝ}
    (hlam : lam ≤ cellLogHalfCore (1 / 2) (1 / 2 + 1 / (2 * 10 ^ 8)) 0.23292 + Real.log (1 / 2)
      - (1 / 2 + 1 / (2 * 10 ^ 8)) / 2 - 1 / 10 ^ 4)
    (hcert : 1 / 10 ^ 8 + 33 * Real.exp (-32) + 16 * Real.exp (-3000) ≤ Real.exp lam)
    {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1 / 2 + 1 / (2 * 10 ^ 8)) : 1 / 10 ^ 8 ≤ PhiSl q := by
  have hC := c3FloorK_eq_of_half_le hq0.le (by linarith) 2
  have hcore := exp_cellLogHalfCore_le (c := 0.23292) (C := c3FloorK q 2) le_rfl hq0.le hq1
    (by norm_num) (by norm_num) (by norm_num) hC.ge
  have hN : Real.exp (-((1 / 2 + 1 / (2 * 10 ^ 8)) / 2)) ≤ Real.exp (-(q / 2)) :=
    Real.exp_le_exp.2 (by linarith)
  have e1 : Real.exp (cellLogHalfCore (1 / 2) (1 / 2 + 1 / (2 * 10 ^ 8)) 0.23292 + Real.log (1 / 2)
      - (1 / 2 + 1 / (2 * 10 ^ 8)) / 2 - 1 / 10 ^ 4)
      = Real.exp (cellLogHalfCore (1 / 2) (1 / 2 + 1 / (2 * 10 ^ 8)) 0.23292) * (1 / 2)
        * Real.exp (-((1 / 2 + 1 / (2 * 10 ^ 8)) / 2)) * Real.exp (-(1 / 10 ^ 4)) := by
    rw [show cellLogHalfCore (1 / 2) (1 / 2 + 1 / (2 * 10 ^ 8)) 0.23292 + Real.log (1 / 2)
        - (1 / 2 + 1 / (2 * 10 ^ 8)) / 2 - 1 / 10 ^ 4
        = cellLogHalfCore (1 / 2) (1 / 2 + 1 / (2 * 10 ^ 8)) 0.23292 + Real.log (1 / 2)
          + -((1 / 2 + 1 / (2 * 10 ^ 8)) / 2) + -(1 / 10 ^ 4) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
  have hX0 := le_trans (Real.exp_pos _).le hcore
  have hmain : Real.exp lam ≤ mainSl q := by
    calc Real.exp lam ≤ _ := Real.exp_le_exp.2 hlam
      _ = _ := e1
      _ ≤ _ := by
        rw [mainSl, perScaleConst]
        exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_right hcore
          (by norm_num)) hN (Real.exp_pos _).le (mul_nonneg hX0 (by norm_num)))
          (Real.exp_pos _).le
  have hJ := cJ_le_one (q := q) (by linarith) (by linarith)
  have hE := cErr_le_sixteen (q := q) (by linarith)
  have h64 : Real.exp (-(64 * q)) ≤ Real.exp (-32) := Real.exp_le_exp.2 (by linarith)
  have hsub : 33 * cJ q * Real.exp (-(64 * q)) ≤ 33 * Real.exp (-32) := by
    have := Real.exp_pos (-(64 * q))
    have hJ0 := cJ_pos q
    nlinarith
  have herr : cErr q * Real.exp (-3000) ≤ 16 * Real.exp (-3000) := by
    have := Real.exp_pos (-3000)
    nlinarith
  unfold PhiSl
  linarith

/-- **S at `10⁻⁸`**: `PhiSl(q) ≥ 10⁻⁸` for `½ < q ≤ ½ + 1/(2·10⁸)` (`RMF.finalSMain`,
`RMF.finalSErr8`; certified margin `×12.2`). -/
theorem PhiSl_ge_eight {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1 / 2 + 1 / (2 * 10 ^ 8)) :
    1 / 10 ^ 8 ≤ PhiSl q :=
  PhiSl_ge_eight_of_cert finalSMain finalSErr8 hq0 hq1

/-- **S's arithmetic at `10⁻⁸`**: `RMF.sliver_regime_arith` with `10⁻⁸` for `10⁻¹⁰`
(`RMF.PhiSl_ge_eight`). -/
lemma sliver_regime_arith_eight {E S Is L q : ℝ} (hL : 0 < L) (hΛ : 6000 ≤ Real.log L)
    (hq0 : 1 / 2 < q) (hq1 : q ≤ 1 / 2 + 1 / (2 * 10 ^ 8)) (hu : 1 ≤ (2 * q - 1) * Real.log L)
    (h : cRed q * (2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * 64)) ^ q * S)
        - cJ q * Real.exp (-(64 * q)) * L ^ (-q) * Is - cErr q * L ^ (-q) ≤ E)
    (hS : perScaleConst q 2 * (1 / 2 * Real.exp (-(q / 2)) * Real.exp (-(1 / 10 ^ 4))
        * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.exp (q * (2 * q - 1) * Real.log L)) ≤ S)
    (hR : Is ≤ 33 * L ^ q * L ^ (q * (2 * q - 1)) * (2 * q - 1) ^ (-(3 / 4 : ℝ))) :
    1 / 10 ^ 8 * (L ^ (q * (2 * q - 1)) * min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ))
      ≤ E := by
  have hδ0 : 0 < 2 * q - 1 := by linarith
  have hδ1 : 2 * q - 1 ≤ 1 := by linarith
  have hΛ0 : 0 < Real.log L := by linarith
  have hmin : min (2 * q - 1)⁻¹ (Real.log L) = (2 * q - 1)⁻¹ :=
    min_eq_left ((inv_le_iff_one_le_mul₀ hδ0).2 (by linarith))
  have hδpow : ((2 * q - 1)⁻¹) ^ (3 / 4 : ℝ) = (2 * q - 1) ^ (-(3 / 4 : ℝ)) := by
    rw [Real.inv_rpow hδ0.le, Real.rpow_neg hδ0.le]
  have hLq : L ^ (q * (2 * q - 1)) = Real.exp (q * (2 * q - 1) * Real.log L) := by
    rw [Real.rpow_def_of_pos hL]
    congr 1
    ring
  rw [hmin, hδpow, hLq]
  rw [hLq] at hR
  rw [show (2 : ℝ) * 64 = 128 by norm_num] at h
  have hP0 : 0 ≤ Real.exp (q * (2 * q - 1) * Real.log L) := (Real.exp_pos _).le
  have hD0 : 0 ≤ (2 * q - 1) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hδ0.le _
  have hG1 : 1 ≤ Real.exp (q * (2 * q - 1) * Real.log L) * (2 * q - 1) ^ (-(3 / 4 : ℝ)) := by
    have h1 : 1 ≤ Real.exp (q * (2 * q - 1) * Real.log L) :=
      Real.one_le_exp (mul_nonneg (mul_nonneg (by linarith) hδ0.le) hΛ0.le)
    have h2 : 1 ≤ (2 * q - 1) ^ (-(3 / 4 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 hδ1 (by norm_num)
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hA0 : 0 ≤ 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / 128) ^ q := by positivity
  have hcR := (cRed_pos q).le
  have hcJ := (cJ_pos q).le
  have hcE := (cErr_pos q).le
  have hLm0 : 0 ≤ L ^ (-q) := Real.rpow_nonneg hL.le _
  have hLL : L ^ (-q) * L ^ q = 1 := by
    rw [← Real.rpow_add hL, neg_add_cancel, Real.rpow_zero]
  have hLe : L ^ (-q) ≤ Real.exp (-3000) := by
    rw [Real.rpow_def_of_pos hL]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul hΛ hq0.le (by norm_num) hΛ0.le
    linarith
  have s1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS hA0) hcR
  have s2 : cRed q * (2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / 128) ^ q
        * (perScaleConst q 2 * (1 / 2 * Real.exp (-(q / 2)) * Real.exp (-(1 / 10 ^ 4))
          * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.exp (q * (2 * q - 1) * Real.log L))))
      = mainSl q * (Real.exp (q * (2 * q - 1) * Real.log L) * (2 * q - 1) ^ (-(3 / 4 : ℝ))) := by
    unfold mainSl
    ring
  have s3 := mul_le_mul_of_nonneg_left hR
    (mul_nonneg (mul_nonneg hcJ (Real.exp_pos (-(64 * q))).le) hLm0)
  have s4 : cJ q * Real.exp (-(64 * q)) * L ^ (-q)
        * (33 * L ^ q * Real.exp (q * (2 * q - 1) * Real.log L) * (2 * q - 1) ^ (-(3 / 4 : ℝ)))
      = 33 * cJ q * Real.exp (-(64 * q))
        * (Real.exp (q * (2 * q - 1) * Real.log L) * (2 * q - 1) ^ (-(3 / 4 : ℝ))) := by
    calc cJ q * Real.exp (-(64 * q)) * L ^ (-q)
          * (33 * L ^ q * Real.exp (q * (2 * q - 1) * Real.log L) * (2 * q - 1) ^ (-(3 / 4 : ℝ)))
        = 33 * cJ q * Real.exp (-(64 * q))
          * (Real.exp (q * (2 * q - 1) * Real.log L) * (2 * q - 1) ^ (-(3 / 4 : ℝ)))
          * (L ^ (-q) * L ^ q) := by ring
      _ = _ := by rw [hLL, mul_one]
  have s5 : cErr q * L ^ (-q) ≤ cErr q * Real.exp (-3000)
      * (Real.exp (q * (2 * q - 1) * Real.log L) * (2 * q - 1) ^ (-(3 / 4 : ℝ))) := by
    calc cErr q * L ^ (-q) ≤ cErr q * Real.exp (-3000) * 1 := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left hLe hcE
      _ ≤ _ := mul_le_mul_of_nonneg_left hG1 (mul_nonneg hcE (Real.exp_pos _).le)
  have s6 : PhiSl q * (Real.exp (q * (2 * q - 1) * Real.log L) * (2 * q - 1) ^ (-(3 / 4 : ℝ)))
      = mainSl q * (Real.exp (q * (2 * q - 1) * Real.log L) * (2 * q - 1) ^ (-(3 / 4 : ℝ)))
        - 33 * cJ q * Real.exp (-(64 * q))
          * (Real.exp (q * (2 * q - 1) * Real.log L) * (2 * q - 1) ^ (-(3 / 4 : ℝ)))
        - cErr q * Real.exp (-3000)
          * (Real.exp (q * (2 * q - 1) * Real.log L) * (2 * q - 1) ^ (-(3 / 4 : ℝ))) := by
    unfold PhiSl
    ring
  have s7 := mul_le_mul_of_nonneg_right (PhiSl_ge_eight hq0 hq1) (mul_nonneg hP0 hD0)
  linarith

/-! ### The numerals for `Y` -/

/-- `Λ^{3/4} ≤ 10⁷` for `0 ≤ Λ ≤ 10⁹`: `(10⁹)^{3/4} = 10^{27/4} ≤ 10⁷`. -/
lemma rpow_three_quarters_le_ten_pow_seven {Λ : ℝ} (h0 : 0 ≤ Λ) (h : Λ ≤ 10 ^ 9) :
    Λ ^ (3 / 4 : ℝ) ≤ 10 ^ 7 := by
  have e9 : ((10 : ℝ) ^ 9) = (10 : ℝ) ^ ((9 : ℕ) : ℝ) := (Real.rpow_natCast 10 9).symm
  have e7 : ((10 : ℝ) ^ 7) = (10 : ℝ) ^ ((7 : ℕ) : ℝ) := (Real.rpow_natCast 10 7).symm
  calc Λ ^ (3 / 4 : ℝ) ≤ ((10 : ℝ) ^ 9) ^ (3 / 4 : ℝ) := Real.rpow_le_rpow h0 h (by norm_num)
    _ = (10 : ℝ) ^ (((9 : ℕ) : ℝ) * (3 / 4)) := by rw [e9, ← Real.rpow_mul (by norm_num)]
    _ ≤ (10 : ℝ) ^ ((7 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 10 ^ 7 := e7.symm

/-- `(100/9)·10⁻¹⁰ ≤ δ^{3/4}` for `δ ≥ 10⁻¹¹`: `(10⁻¹¹)^{3/4} ≥ 5.6·10⁻⁹`. -/
lemma hundred_ninths_mul_le_rpow {δ : ℝ} (hδ : 1 / 10 ^ 11 ≤ δ) :
    100 / 9 * (1 / 10 ^ 10 : ℝ) ≤ δ ^ (3 / 4 : ℝ) := by
  have h0 : (0 : ℝ) < 1 / 10 ^ 11 := by norm_num
  have h1 := Real.rpow_le_rpow h0.le hδ (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have h2 : 100 / 9 * (1 / 10 ^ 10 : ℝ) ≤ (1 / 10 ^ 11 : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos h0]
    interval_decide (trust := kernel)
  linarith

/-- `2^{2q} ≤ 2.1` for `2q - 1 < 10⁻¹¹`. -/
lemma two_rpow_le_of_sliver {q : ℝ} (hq : 2 * q - 1 < 1 / 10 ^ 11) :
    (2 : ℝ) ^ (2 * q) ≤ 21 / 10 := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 : Real.log 2 * (2 * q) ≤ Real.log 2 * (1 + 1 / 10 ^ 11) :=
    mul_le_mul_of_nonneg_left (by linarith) hl
  have h2 : Real.exp (Real.log 2 * (1 + 1 / 10 ^ 11)) ≤ 21 / 10 := by
    interval_decide (trust := kernel)
  rw [Real.rpow_def_of_pos two_pos]
  exact (Real.exp_le_exp.2 h1).trans h2

/-- **The sliver's target is large**: for `½ < q`, `δ = 2q - 1 < 10⁻¹¹`, `L > 0` and
`δ log L ≥ 1`, `2.1 ≤ 10⁻⁸L^{qδ}min{1/δ, log L}^{3/4}`: the `min` is `1/δ`, `L^{qδ} ≥ e^{1/2}`
and `δ^{-3/4} ≥ 10^{33/4}`. -/
lemma sliver_target_ge {q L : ℝ} (hq0 : 1 / 2 < q) (hδ : 2 * q - 1 < 1 / 10 ^ 11) (hL : 0 < L)
    (hu : 1 ≤ (2 * q - 1) * Real.log L) :
    21 / 10 ≤ 1 / 10 ^ 8 * (L ^ (q * (2 * q - 1))
      * min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ)) := by
  have hδ0 : 0 < 2 * q - 1 := by linarith
  have hmin : min (2 * q - 1)⁻¹ (Real.log L) = (2 * q - 1)⁻¹ :=
    min_eq_left ((inv_le_iff_one_le_mul₀ hδ0).2 (by linarith))
  rw [hmin]
  have hLq : Real.exp (1 / 2) ≤ L ^ (q * (2 * q - 1)) := by
    rw [Real.rpow_def_of_pos hL]
    refine Real.exp_le_exp.2 ?_
    have h1 : q * 1 ≤ q * ((2 * q - 1) * Real.log L) := mul_le_mul_of_nonneg_left hu (by linarith)
    have e : Real.log L * (q * (2 * q - 1)) = q * ((2 * q - 1) * Real.log L) := by ring
    linarith
  have hinv : (10 : ℝ) ^ 11 ≤ (2 * q - 1)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hδ0]
    have e : ((10 : ℝ) ^ 11)⁻¹ = 1 / 10 ^ 11 := by norm_num
    linarith
  have hD : Real.exp (Real.log (10 ^ 11) * (3 / 4)) ≤ ((2 * q - 1)⁻¹) ^ (3 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos (inv_pos.2 hδ0)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
      (Real.log_le_log (by norm_num) hinv) (by norm_num))
  have hnum : (21 / 10 : ℝ)
      ≤ 1 / 10 ^ 8 * (Real.exp (1 / 2) * Real.exp (Real.log (10 ^ 11) * (3 / 4))) := by
    interval_decide (trust := kernel)
  exact hnum.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hLq hD (Real.exp_pos _).le (Real.rpow_nonneg hL.le _)) (by norm_num))

/-- **The sliver for `Y`, the arithmetic**: from Minkowski
`IS^{1/(2q)} ≤ IY^{1/(2q)} + IR^{1/(2q)}`, `IS ≥ 10⁻⁸T`, `IR ≤ 1` and `2^{2q} ≤ 2.1 ≤ 10⁻⁸T`:
`IY ≥ 10⁻⁸T/2^{2q} ≥ 10⁻¹⁰T` (`RMF.le_of_rpow_inv_le_add`). -/
lemma sliver_ext_arith {IS IY IR T q : ℝ} (hq0 : 1 / 2 < q) (hq2 : (2 : ℝ) ^ (2 * q) ≤ 21 / 10)
    (hT : 21 / 10 ≤ 1 / 10 ^ 8 * T) (hS : 1 / 10 ^ 8 * T ≤ IS) (hR : IR ≤ 1) (hY0 : 0 ≤ IY)
    (hR0 : 0 ≤ IR) (hmink : IS ^ (2 * q)⁻¹ ≤ IY ^ (2 * q)⁻¹ + IR ^ (2 * q)⁻¹) :
    1 / 10 ^ 10 * T ≤ IY := by
  have h2 : (0 : ℝ) < 2 ^ (2 * q) := Real.rpow_pos_of_pos two_pos _
  have hT0 : 0 ≤ T := by linarith
  have hRM : IR ≤ 1 / 10 ^ 8 * T / 2 ^ (2 * q) := by
    rw [le_div_iff₀ h2]
    calc IR * 2 ^ (2 * q) ≤ 1 * 2 ^ (2 * q) := mul_le_mul_of_nonneg_right hR h2.le
      _ ≤ 1 / 10 ^ 8 * T := by linarith
  have key := le_of_rpow_inv_le_add (by linarith : (0 : ℝ) < 2 * q) hY0 hR0
    (by linarith : (0 : ℝ) ≤ 1 / 10 ^ 8 * T) hmink hS hRM
  have hfin : 1 / 10 ^ 10 * T ≤ 1 / 10 ^ 8 * T / 2 ^ (2 * q) := by
    rw [le_div_iff₀ h2]
    calc 1 / 10 ^ 10 * T * 2 ^ (2 * q) ≤ 1 / 10 ^ 10 * T * (21 / 10) :=
          mul_le_mul_of_nonneg_left hq2 (mul_nonneg (by norm_num) hT0)
      _ ≤ 1 / 10 ^ 8 * T := by linarith
  linarith

/-- **The target above `½` is at most `¼` for `log x ≤ 415`**: for `1 ≤ L ≤ 415` and
`½ < q ≤ 1`, `10⁻¹⁰L^{q(2q-1)}min{1/(2q-1), log L}^{3/4} ≤ 10⁻¹⁰L² ≤ ¼`
(`RMF.aboveHalf_target_le_one_of_le_405` with `415` and `¼`). -/
lemma aboveHalf_target_le_quarter_of_le_415 {q L : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1)
    (hL1 : 1 ≤ L) (hL : L ≤ 415) :
    1 / 10 ^ 10 * (L ^ (q * (2 * q - 1)) * min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ))
      ≤ 1 / 4 := by
  have hδ0 : 0 < 2 * q - 1 := by linarith
  have hmin0 : 0 ≤ min (2 * q - 1)⁻¹ (Real.log L) :=
    le_min (inv_nonneg.2 hδ0.le) (Real.log_nonneg hL1)
  have hmL : min (2 * q - 1)⁻¹ (Real.log L) ≤ L :=
    (min_le_right _ _).trans (Real.log_le_self (by linarith))
  have hA : L ^ (q * (2 * q - 1)) ≤ L := by
    calc L ^ (q * (2 * q - 1)) ≤ L ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (mul_le_one₀ hq1 hδ0.le (by linarith))
      _ = L := Real.rpow_one L
  have hB : min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ) ≤ L := by
    calc min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ) ≤ L ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow hmin0 hmL (by norm_num)
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := Real.rpow_one L
  have hAB : L ^ (q * (2 * q - 1)) * min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ) ≤ 415 * 415 :=
    mul_le_mul (hA.trans hL) (hB.trans hL) (Real.rpow_nonneg hmin0 _) (by norm_num)
  linarith

/-- **The target just above `½` is at most `¼` for `log log x < 6000`**: for `L > 0`,
`0 ≤ log L < 6000`, `½ < q ≤ 1` and `2q - 1 < 10⁻⁸`,
`10⁻¹⁰L^{q(2q-1)}min{1/(2q-1), log L}^{3/4} ≤ 10⁻¹⁰·3·6000 ≤ ¼`
(`RMF.aboveHalf_target_le_one_of_small` with `¼`). -/
lemma aboveHalf_target_le_quarter_of_small {q L : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1)
    (hδ : 2 * q - 1 < 1 / 10 ^ 8) (hL : 0 < L) (hΛ0 : 0 ≤ Real.log L)
    (hΛ : Real.log L < 6000) :
    1 / 10 ^ 10 * (L ^ (q * (2 * q - 1)) * min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ))
      ≤ 1 / 4 := by
  have hδ0 : 0 < 2 * q - 1 := by linarith
  have hβ0 : 0 ≤ q * (2 * q - 1) := mul_nonneg (by linarith) hδ0.le
  have hβ : q * (2 * q - 1) ≤ 1 * (1 / 10 ^ 8) := mul_le_mul hq1 hδ.le hδ0.le zero_le_one
  have hA : L ^ (q * (2 * q - 1)) ≤ 3 := by
    rw [Real.rpow_def_of_pos hL]
    have h1 : Real.log L * (q * (2 * q - 1)) ≤ 6000 * (1 * (1 / 10 ^ 8)) :=
      mul_le_mul hΛ.le hβ hβ0 (by norm_num)
    have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h2 : Real.exp (Real.log L * (q * (2 * q - 1))) ≤ Real.exp 1 :=
      Real.exp_le_exp.2 (by linarith)
    linarith
  have hmin0 : 0 ≤ min (2 * q - 1)⁻¹ (Real.log L) := le_min (inv_nonneg.2 hδ0.le) hΛ0
  have hB : min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ) ≤ 6000 :=
    rpow_three_quarters_le_six_thousand hmin0 ((min_le_right _ _).trans hΛ.le)
  have hAB : L ^ (q * (2 * q - 1)) * min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ) ≤ 3 * 6000 :=
    mul_le_mul hA hB (Real.rpow_nonneg hmin0 _) (by norm_num)
  linarith

/-! ### `Y(x)` as a Rademacher chaos -/

/-- The coefficient of `∏_{p ∈ A} X_p` in `Y(x)`: `⌊√(x/n_A)⌋/√x` if `n_A ≤ ⌊x⌋`, else `0`. -/
noncomputable def compMultCoeff (x : ℝ) (A : Finset Nat.Primes) : ℂ :=
  if ∏ p ∈ A, (p : ℕ) ≤ ⌊x⌋₊ then
    (⌊Real.sqrt (x / ((∏ p ∈ A, (p : ℕ) : ℕ) : ℝ))⌋₊ : ℂ) / (Real.sqrt x : ℂ)
  else 0

/-- **A sum over the squarefree `n ≤ N` is a chaos**: for every `g : ℕ → ℂ`,
`∑_{n≤N} v^{sf}(n)g(n) = ∑_{A ⊆ {p ≤ N}} [n_A ≤ N]g(n_A)∏_{p∈A} v(p)`: the bijection of
`RMF.weightedRademacherSum_eq_chaosSum`, for any coefficients. -/
lemma sum_squarefreeExtension_mul_eq_chaosSum (v : ℕ → ℂ) (g : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, squarefreeExtension v n * g n
      = ∑ A ∈ (primesUpTo N).powerset,
          (if ∏ p ∈ A, (p : ℕ) ≤ N then g (∏ p ∈ A, (p : ℕ)) else 0) * ∏ p ∈ A, v p := by
  classical
  -- only squarefree `n` contribute
  have h1 : ∑ n ∈ Finset.Icc 1 N, squarefreeExtension v n * g n
      = ∑ n ∈ Finset.Icc 1 N with Squarefree n, g n * ∏ p ∈ n.primeFactors, v p := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with hn
    · rw [squarefreeExtension_apply_of_squarefree _ hn, mul_comm]
    · rw [squarefreeExtension_apply_of_not_squarefree _ hn, zero_mul]
  -- and only the sets `A` with `n_A ≤ N`
  have h2 : ∑ A ∈ (primesUpTo N).powerset,
        (if ∏ p ∈ A, (p : ℕ) ≤ N then g (∏ p ∈ A, (p : ℕ)) else 0) * ∏ p ∈ A, v p
      = ∑ A ∈ (primesUpTo N).powerset.filter (fun A : Finset Nat.Primes => ∏ p ∈ A, (p : ℕ) ≤ N),
          g (∏ p ∈ A, (p : ℕ)) * ∏ p ∈ A, v p := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun A _ => ?_
    split_ifs <;> simp
  rw [h1, h2]
  symm
  refine Finset.sum_nbij' (fun A => ∏ p ∈ A, (p : ℕ))
    (fun n => (n.primeFactors.subtype Nat.Prime : Finset Nat.Primes))
    (fun A hA => ?_) (fun n hn => ?_) (fun A _ => ?_) (fun n hn => ?_) (fun A _ => ?_)
  · obtain ⟨-, hAN⟩ := Finset.mem_filter.1 hA
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2
      ⟨Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun p _ => p.2.ne_zero), hAN⟩,
      squarefree_prod_primes A⟩
  · obtain ⟨hnI, hsq⟩ := Finset.mem_filter.1 hn
    have hnN := (Finset.mem_Icc.1 hnI).2
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 fun p hp => ?_, ?_⟩
    · have hp' : (p : ℕ) ∈ n.primeFactors := Finset.mem_subtype.1 hp
      exact mem_primesUpTo.2 (le_trans (Nat.le_of_mem_primeFactors hp') hnN)
    · exact (prod_primeFactors_subtype hsq).trans_le hnN
  · rw [primeFactors_prod_primes, subtype_map_primes]
  · exact prod_primeFactors_subtype (Finset.mem_filter.1 hn).2
  · rw [primeFactors_prod_primes, Finset.prod_map]
    rfl

/-- **The coefficients of `Y(x)` against those of `S(x/100²)`**: for `n_A ≤ x/10⁴`,
`⌊√(x/n_A)⌋ ≥ √(x/n_A) - 1 ≥ (99/100)√(x/n_A)`, so `(98/100)n_A⁻¹ ≤ (⌊√(x/n_A)⌋/√x)²`. -/
lemma sq_norm_cutCoeff_le_compMultCoeff {x : ℝ} (hx : 0 < x) (A : Finset Nat.Primes) :
    98 / 100 * ‖cutCoeff ⌊x / 10 ^ 4⌋₊ A‖ ^ 2 ≤ ‖compMultCoeff x A‖ ^ 2 := by
  unfold cutCoeff
  split_ifs with h
  · have hxx : x / 10 ^ 4 ≤ x := div_le_self hx.le (by norm_num)
    have hnx : ∏ p ∈ A, (p : ℕ) ≤ ⌊x⌋₊ := le_trans h (Nat.floor_le_floor hxx)
    rw [compMultCoeff, if_pos hnx, sq_norm_sqrtInv, norm_div, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
      Real.sq_sqrt hx.le]
    set n := ∏ p ∈ A, (p : ℕ) with hn
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun p _ => p.2.ne_zero)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnx' : (n : ℝ) ≤ x / 10 ^ 4 :=
      le_trans (by exact_mod_cast h) (Nat.floor_le (by positivity))
    have hxn : (10 : ℝ) ^ 4 ≤ x / n := by
      rw [le_div_iff₀ hn0]
      rw [le_div_iff₀ (by norm_num)] at hnx'
      linarith
    set s := Real.sqrt (x / n) with hs
    have hs100 : 100 ≤ s := by
      have h := Real.sqrt_le_sqrt hxn
      rwa [show (10 : ℝ) ^ 4 = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
    have hfl : 99 / 100 * s ≤ (⌊s⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one s
      linarith
    have hs2 : s ^ 2 = x / n := Real.sq_sqrt (by positivity)
    have hsq : (99 / 100 * s) ^ 2 ≤ (⌊s⌋₊ : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hfl 2
    rw [le_div_iff₀ hx]
    have e : 98 / 100 * (n : ℝ)⁻¹ * x = 98 / 100 * (x / n) := by
      field_simp
    rw [e, ← hs2]
    nlinarith
  · rw [norm_zero, zero_pow two_ne_zero, mul_zero]
    positivity

/-- **`∑_A t^{|A|}|c_A|² ≥ (9/100)(log x)^t`** for the coefficients `c_A` of `Y(x)`, `x ≥ e^{415}`
and `0 ≤ t ≤ 1`: on the sets with `n_A ≤ x/10⁴`, `|c_A|²` is at least `98/100` times the
square of `S(x/10⁴)`'s coefficient `n_A^{-1/2}`, whose sum is at least `(1/10)(log(x/10⁴))^t`
(`RMF.chaosNormSq_cutCoeff_ge_explicit`), and `log(x/10⁴) ≥ (97/100)log x`. -/
theorem chaosNormSq_compMultCoeff_ge_explicit {t x : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : Real.exp 415 ≤ x) :
    9 / 100 * Real.log x ^ t ≤ chaosNormSq (primesUpTo ⌊x⌋₊) (compMultCoeff x) t := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : 415 ≤ Real.log x := by
    rw [← Real.log_exp 415]; exact Real.log_le_log (Real.exp_pos _) hx
  have he : (10 : ℝ) ^ 4 ≤ Real.exp 10 := by interval_decide (trust := kernel)
  have hx' : Real.exp 405 ≤ x / 10 ^ 4 := by
    rw [le_div_iff₀ (by norm_num)]
    calc Real.exp 405 * 10 ^ 4 ≤ Real.exp 405 * Real.exp 10 :=
          mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
      _ = Real.exp 415 := by rw [← Real.exp_add]; norm_num
      _ ≤ x := hx
  have hbase := chaosNormSq_cutCoeff_ge_explicit ht0 ht1 hx'
  -- `log(x/10⁴) ≥ (97/100) log x`
  have hl4 : Real.log ((10 : ℝ) ^ 4) ≤ 9.22 := by interval_decide (trust := kernel)
  have hlog : 97 / 100 * Real.log x ≤ Real.log (x / 10 ^ 4) := by
    rw [Real.log_div hx0.ne' (by norm_num)]
    linarith
  have hpow : 97 / 100 * Real.log x ^ t ≤ Real.log (x / 10 ^ 4) ^ t := by
    have h1 : (97 / 100 * Real.log x) ^ t ≤ Real.log (x / 10 ^ 4) ^ t :=
      Real.rpow_le_rpow (mul_nonneg (by norm_num) (by linarith)) hlog ht0
    rw [Real.mul_rpow (by norm_num) (by linarith)] at h1
    have h2 : (97 / 100 : ℝ) ≤ (97 / 100) ^ t := by
      calc (97 / 100 : ℝ) = (97 / 100) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (97 / 100) ^ t := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ht1
    exact le_trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by linarith) _)) h1
  -- the coefficients, compared
  have hcmp : 98 / 100 * chaosNormSq (primesUpTo ⌊x / 10 ^ 4⌋₊) (cutCoeff ⌊x / 10 ^ 4⌋₊) t
      ≤ chaosNormSq (primesUpTo ⌊x / 10 ^ 4⌋₊) (compMultCoeff x) t := by
    unfold chaosNormSq
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun A _ => ?_
    have hA := sq_norm_cutCoeff_le_compMultCoeff hx0 A
    have ht := pow_nonneg ht0 A.card
    calc 98 / 100 * (t ^ A.card * ‖cutCoeff ⌊x / 10 ^ 4⌋₊ A‖ ^ 2)
        = t ^ A.card * (98 / 100 * ‖cutCoeff ⌊x / 10 ^ 4⌋₊ A‖ ^ 2) := by ring
      _ ≤ t ^ A.card * ‖compMultCoeff x A‖ ^ 2 := mul_le_mul_of_nonneg_left hA ht
  have hmono := chaosNormSq_mono
    (primesUpTo_mono (Nat.floor_le_floor (div_le_self hx0.le (by norm_num) : x / 10 ^ 4 ≤ x)))
    (compMultCoeff x) ht0
  have hlx : 0 ≤ Real.log x ^ t := Real.rpow_nonneg (by linarith) _
  calc 9 / 100 * Real.log x ^ t ≤ 98 / 100 * (1 / 10 * (97 / 100 * Real.log x ^ t)) := by
        linarith
    _ ≤ 98 / 100 * (1 / 10 * Real.log (x / 10 ^ 4) ^ t) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by norm_num)
    _ ≤ 98 / 100 * chaosNormSq (primesUpTo ⌊x / 10 ^ 4⌋₊) (cutCoeff ⌊x / 10 ^ 4⌋₊) t :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ ≤ chaosNormSq (primesUpTo ⌊x / 10 ^ 4⌋₊) (compMultCoeff x) t := hcmp
    _ ≤ chaosNormSq (primesUpTo ⌊x⌋₊) (compMultCoeff x) t := hmono

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- **`Y(x)` is a chaos where `X(p)² = 1`** at the primes `p ≤ x`: by the square classes
(`RMF.sum_compMultExtension_eq_sum_squarefreeExtension_mul`)
`Y(x) = ∑_{m≤x} X^{sf}(m)⌊√(x/m)⌋/√x`, a sum over the squarefree `m ≤ x`. -/
lemma normalisedSum_compMultExtension_eq_chaosSum {X : ℕ → Ω → ℂ} {x : ℝ} (hx : 0 ≤ x) {ω : Ω}
    (hv : ∀ p, p.Prime → p ≤ ⌊x⌋₊ → X p ω ^ 2 = 1) :
    normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω
      = chaosSum (fun p : Nat.Primes => X p) (primesUpTo ⌊x⌋₊) (compMultCoeff x) ω := by
  have h := sum_squarefreeExtension_mul_eq_chaosSum (fun p => X p ω)
    (fun n => (⌊Real.sqrt (x / n)⌋₊ : ℂ) / (Real.sqrt x : ℂ)) ⌊x⌋₊
  rw [normalisedSum, randomSum, sum_compMultExtension_eq_sum_squarefreeExtension_mul hx hv,
    Finset.sum_div]
  simp only [mul_div_assoc]
  rw [h, chaosSum]
  rfl

/-- **`Y(x)` is a Rademacher chaos**, almost surely: over the primes up to `⌊x⌋`, with the
coefficients `RMF.compMultCoeff x`. -/
lemma ae_normalisedSum_compMultExtension_eq_chaosSum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 0 ≤ x) :
    ∀ᵐ ω ∂μ, normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω
      = chaosSum (fun p : Nat.Primes => X p) (primesUpTo ⌊x⌋₊) (compMultCoeff x) ω := by
  have hsq : ∀ᵐ ω ∂μ, ∀ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), X p ω ^ 2 = 1 :=
    (Filter.eventually_all_finset _).2 fun p hp =>
      ae_sq_X_eq_one hX (Nat.prime_of_mem_primesBelow hp)
  filter_upwards [hsq] with ω hω
  exact normalisedSum_compMultExtension_eq_chaosSum hx fun p hp hpx =>
    hω p (Nat.mem_primesBelow.2 ⟨by omega, hp⟩)

/-! ### Bonami–Beckner -/

/-- **Bonami–Beckner from below for `Y`, explicit**: for every Rademacher `X`, `x ≥ e^{415}` and
`½ ≤ q ≤ 1`, `(9/100)(log x)^{q(2q-1)} ≤ E|Y(x)|^{2q}`
(`RMF.chaosNormSq_rpow_le_integral`, `RMF.chaosNormSq_compMultCoeff_ge_explicit`). -/
theorem le_integral_rpow_normalisedSum_compMultExtension_bb_explicit {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp 415 ≤ x)
    (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) :
    9 / 100 * Real.log x ^ (q * (2 * q - 1))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : 0 < Real.log x := by
    have : (415 : ℝ) ≤ Real.log x := by
      rw [← Real.log_exp 415]; exact Real.log_le_log (Real.exp_pos _) hx
    linarith
  have hhyp := chaosNormSq_rpow_le_integral (μ := μ) (Y := fun p : Nat.Primes => X p)
    (fun p => hX.measurable p p.2) hX.iIndep (fun p => hX.hasLaw p p.2)
    (p := 2 * q) (by linarith) (by linarith) (primesUpTo ⌊x⌋₊) (compMultCoeff x)
  have hae : (fun ω => ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q))
      =ᵐ[μ] fun ω =>
        ‖chaosSum (fun p : Nat.Primes => X p) (primesUpTo ⌊x⌋₊) (compMultCoeff x) ω‖ ^ (2 * q) := by
    filter_upwards [ae_normalisedSum_compMultExtension_eq_chaosSum hX hx0.le] with ω hω
    rw [hω]
  rw [integral_congr_ae hae]
  refine le_trans ?_ hhyp
  have hbase := chaosNormSq_compMultCoeff_ge_explicit (t := 2 * q - 1) (by linarith)
    (by linarith) hx
  have hmin : (9 / 100 : ℝ) ≤ (9 / 100) ^ q := by
    calc (9 / 100 : ℝ) = (9 / 100) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (9 / 100) ^ q := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hq1
  calc 9 / 100 * Real.log x ^ (q * (2 * q - 1))
      ≤ (9 / 100) ^ q * Real.log x ^ (q * (2 * q - 1)) :=
        mul_le_mul_of_nonneg_right hmin (Real.rpow_nonneg hlogx.le _)
    _ = (9 / 100 * Real.log x ^ (2 * q - 1)) ^ q := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hlogx.le _), ← Real.rpow_mul hlogx.le,
          mul_comm (2 * q - 1) q]
    _ ≤ chaosNormSq (primesUpTo ⌊x⌋₊) (compMultCoeff x) (2 * q - 1) ^ q :=
        Real.rpow_le_rpow (mul_nonneg (by norm_num) (Real.rpow_nonneg hlogx.le _)) hbase
          (by linarith)
    _ = chaosNormSq (primesUpTo ⌊x⌋₊) (compMultCoeff x) (2 * q - 1) ^ (2 * q / 2) := by
        rw [mul_div_cancel_left₀ q two_ne_zero]

/-- **The large-`q` target by Bonami–Beckner, for `Y`**: for `½ < q ≤ 1`, `x ≥ e^{415}` and
`(100/9)c ≤ (2q-1)^{3/4}`, `c(log x)^{q(2q-1)}min{1/(2q-1), log log x}^{3/4} ≤ E|Y(x)|^{2q}`
(`RMF.le_integral_rpow_weightedRademacherSum_largeQ_bb` with `9/100` for `1/10`). -/
theorem le_integral_rpow_normalisedSum_compMultExtension_largeQ_bb {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q c : ℝ} (hx : Real.exp 415 ≤ x)
    (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) (hc0 : 0 ≤ c) (hc : 100 / 9 * c ≤ (2 * q - 1) ^ (3 / 4 : ℝ)) :
    c * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  have hδ : 0 < 2 * q - 1 := by linarith
  have hlogx : 0 < Real.log x := by
    have : (415 : ℝ) ≤ Real.log x := by
      rw [← Real.log_exp 415]; exact Real.log_le_log (Real.exp_pos _) hx
    linarith
  have hΛ : 0 < Real.log (Real.log x) := Real.log_pos (by
    have : (415 : ℝ) ≤ Real.log x := by
      rw [← Real.log_exp 415]; exact Real.log_le_log (Real.exp_pos _) hx
    linarith)
  have hmin0 : 0 ≤ min (2 * q - 1)⁻¹ (Real.log (Real.log x)) := le_min (inv_nonneg.2 hδ.le) hΛ.le
  have hm : min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ)
      ≤ ((2 * q - 1) ^ (3 / 4 : ℝ))⁻¹ := by
    rw [← Real.inv_rpow hδ.le]
    exact Real.rpow_le_rpow hmin0 (min_le_left _ _) (by norm_num)
  have hd0 : 0 < (2 * q - 1) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hδ _
  have hcm : c * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ) ≤ 9 / 100 := by
    calc c * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ)
        ≤ c * ((2 * q - 1) ^ (3 / 4 : ℝ))⁻¹ := mul_le_mul_of_nonneg_left hm hc0
      _ ≤ 9 / 100 := by
          rw [← div_eq_mul_inv, div_le_iff₀ hd0]; linarith
  have hL : 0 ≤ Real.log x ^ (q * (2 * q - 1)) := Real.rpow_nonneg hlogx.le _
  calc c * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
      = c * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ)
          * Real.log x ^ (q * (2 * q - 1)) := by ring
    _ ≤ 9 / 100 * Real.log x ^ (q * (2 * q - 1)) := mul_le_mul_of_nonneg_right hcm hL
    _ ≤ _ := le_integral_rpow_normalisedSum_compMultExtension_bb_explicit hX hx hq0.le hq1

/-! ### `q = ½` -/

/-- **Minkowski for `S = Y + R`**: for `x ≥ 1` and `r ≥ 1`,
`(E|S(x)|^r)^{1/r} ≤ (E|Y(x)|^r)^{1/r} + (E|R(x)|^r)^{1/r}`, `R` the fractional-part sum, as
`S = Y + R` almost surely (`RMF.ae_normalisedSum_compMultExtension_eq`). -/
lemma rpow_inv_integral_rpow_weightedRademacherSum_le_add {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x r : ℝ} (hx : 1 ≤ x) (hr : 1 ≤ r) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ r ∂μ)
        ^ r⁻¹
      ≤ (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ r ∂μ) ^ r⁻¹
        + (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ r ∂μ)
          ^ r⁻¹ := by
  have hae : (fun ω =>
        ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ r)
      =ᵐ[μ] fun ω => ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω
          + fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ r := by
    filter_upwards [ae_normalisedSum_compMultExtension_eq hX hx] with ω hω
    rw [hω, sub_add_cancel]
  rw [integral_congr_ae hae]
  exact rpow_inv_integral_rpow_norm_add_le hr (memLp_normalisedSum_compMultExtension hX x _)
    (memLp_fracPartSum hX x _)

/-- **`E|Y(x)| ≥ 10⁻⁸(log log x)^{3/4}` for every `x ≥ 3`**: for `Λ = log log x ≤ 10⁹`,
`E|Y| ≥ ⌊√x⌋/√x ≥ ½ ≥ 10⁻⁸·10⁷`; beyond, `E|Y| ≥ E|S| - E|R|` with
`E|S| ≥ 10⁻⁷Λ^{3/4}` (`RMF.integral_norm_weightedRademacherSum_ge_half_explicit`) and
`E|R| ≤ 20Λ^{-1/4} ≤ 2·10⁻⁸Λ^{3/4}` (`RMF.integral_norm_fracPartSum_le_twenty_of_three_le`). -/
theorem integral_norm_normalisedSum_compMultExtension_ge_explicit {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 3 ≤ x) :
    1 / 10 ^ 8 * Real.log (Real.log x) ^ (3 / 4 : ℝ)
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hΛ0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg (one_le_log_of_three_le hx)
  have hp0 : 0 ≤ Real.log (Real.log x) ^ (3 / 4 : ℝ) := Real.rpow_nonneg hΛ0 _
  rcases le_or_gt (Real.log (Real.log x)) (10 ^ 9) with hs | hb
  · have h34 := rpow_three_quarters_le_ten_pow_seven hΛ0 hs
    have hr := floor_sqrt_div_sqrt_le_integral_norm_normalisedSum_compMultExtension hX hx1
    have hh := half_le_floor_sqrt_div_sqrt hx1
    linarith
  · have hS := integral_norm_weightedRademacherSum_ge_half_explicit hX hx
    have hR := integral_norm_fracPartSum_le_twenty_of_three_le hX hx
    have hM := rpow_inv_integral_rpow_weightedRademacherSum_le_add hX hx1 (r := 1) le_rfl
    simp only [Real.rpow_one, inv_one] at hM
    have hΛp : 0 < Real.log (Real.log x) := by linarith
    have e : Real.log (Real.log x) ^ (-(1 / 4 : ℝ))
        = Real.log (Real.log x) ^ (3 / 4 : ℝ) / Real.log (Real.log x) := by
      rw [eq_div_iff hΛp.ne', ← Real.rpow_add_one hΛp.ne']
      norm_num
    have hq : Real.log (Real.log x) ^ (-(1 / 4 : ℝ))
        ≤ Real.log (Real.log x) ^ (3 / 4 : ℝ) / 10 ^ 9 := by
      rw [e]
      exact div_le_div_of_nonneg_left hp0 (by norm_num) hb.le
    linarith

/-- `¼ ≤ E|Y(x)|^{2q}` for every Rademacher `X`, `x ≥ 1` and `½ ≤ q ≤ 1`:
`E|Y(x)| ≥ ⌊√x⌋/√x ≥ ½` and `E|Y| ≤ (E|Y|^{2q})^{1/(2q)}`
(`RMF.integral_rpow_le_rpow_integral_of_le`), so `E|Y|^{2q} ≥ (½)^{2q} ≥ ¼`. -/
theorem quarter_le_integral_rpow_normalisedSum_compMultExtension {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 1 ≤ x) (hq : 1 / 2 ≤ q)
    (hq1 : q ≤ 1) :
    1 / 4 ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have h1 : 1 / 2 ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ :=
    (half_le_floor_sqrt_div_sqrt hx).trans
      (floor_sqrt_div_sqrt_le_integral_norm_normalisedSum_compMultExtension hX hx)
  have hJ := integral_rpow_le_rpow_integral_of_le (μ := μ) (p := q) (q := 1 / 2) (by norm_num) hq
    (memLp_normalisedSum_compMultExtension hX x _)
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at hJ
  simp only [Real.rpow_one] at hJ
  have hE0 : 0 ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have h2 : (1 / 2 : ℝ) ^ (2 * q)
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
    calc (1 / 2 : ℝ) ^ (2 * q)
        ≤ ((∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ) ^ (1 / 2 / q)) ^ (2 * q) :=
          Real.rpow_le_rpow (by norm_num) (h1.trans hJ) (by linarith)
      _ = _ := by
          rw [← Real.rpow_mul hE0, show 1 / 2 / q * (2 * q) = 1 by field_simp, Real.rpow_one]
  have h3 : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 * q) := by
    have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      (by linarith : 2 * q ≤ 2)
    rw [Real.rpow_two] at h
    norm_num at h ⊢
    linarith
  linarith

/-! ### The regimes from `x ≥ exp(e^{6000})` -/

section

variable {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **S at `10⁻⁸`**: for `x ≥ exp(e^{6000})`, `½ < q`, `δ = 2q - 1 < 10⁻⁸` and `δΛ ≥ 1`,
`10⁻⁸(log x)^{qδ}min{1/δ, Λ}^{3/4} ≤ E|S(x)|^{2q}`: `RMF.le_integral_rpow_sliverRegime` with
`RMF.sliver_regime_arith_eight`. -/
theorem le_integral_rpow_sliverRegime_eight (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 1 / 2 < q) (hδ : 2 * q - 1 < 1 / 10 ^ 8)
    (hu : 1 ≤ (2 * q - 1) * Real.log (Real.log x)) :
    1 / 10 ^ 8 * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, -, -⟩ := loglog_facts_of_six_thousand hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.2 (Real.exp_pos _)) hx
  have hδ0 : 0 < 2 * q - 1 := by linarith
  have hq1 : q ≤ 1 / 2 + 1 / (2 * 10 ^ 8) := by linarith
  obtain ⟨T, hT1, hT2, H⟩ := exists_level_aboveHalf hX hx hq0.le (by linarith)
  -- the cap `J = ⌊1/(2δ)⌋ ≤ Λ/2`
  have hJ1 : 1 / (2 * (2 * q - 1)) < (⌊1 / (2 * (2 * q - 1))⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hJ2 : (⌊1 / (2 * (2 * q - 1))⌋₊ : ℝ) ≤ 1 / (2 * (2 * q - 1)) :=
    Nat.floor_le (by positivity)
  have hJΛ : 1 / (2 * (2 * q - 1)) ≤ Real.log (Real.log x) / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]
    linarith
  have hTJ : 2021 + ⌊1 / (2 * (2 * q - 1))⌋₊ ≤ T := by
    have : ((2021 + ⌊1 / (2 * (2 * q - 1))⌋₊ : ℕ) : ℝ) ≤ T := by
      push_cast
      linarith
    exact_mod_cast this
  have h := H (Finset.Icc (T - 2000 - ⌊1 / (2 * (2 * q - 1))⌋₊) (T - 2000)) fun k hk => by
    rw [Finset.mem_Icc] at hk
    exact ⟨by omega, by omega⟩
  have hS := le_trans
    (mul_le_mul_of_nonneg_left
      (sliver_count_arith rfl hδ0 hδ (Nat.cast_nonneg _) hJ1.le hJ2 hT1)
      (perScaleConst_nonneg (q := q) (by linarith) (by linarith) 2))
    (sliver_sum_ge hq0 (by linarith) hTJ)
  have hR := integral_rpow_lineDiv_le_subtracted_sliver hX hx1 (by linarith) (V := 64)
    (by norm_num) hq0 (by linarith)
  exact sliver_regime_arith_eight hL0 hΛ hq0 hq1 hu h hS hR

/-- **BB for `Y`**: for `x ≥ exp(e^{6000})`, `q ≤ 1` and `δ = 2q - 1 ≥ 10⁻¹¹`,
`10⁻¹⁰(log x)^{qδ}min{1/δ, Λ}^{3/4} ≤ E|Y(x)|^{2q}`
(`RMF.le_integral_rpow_normalisedSum_compMultExtension_largeQ_bb`,
`δ^{3/4} ≥ (10⁻¹¹)^{3/4} ≥ (100/9)·10⁻¹⁰`). -/
theorem le_integral_rpow_bbRegime_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq1 : q ≤ 1) (hδ : 1 / 10 ^ 11 ≤ 2 * q - 1) :
    1 / 10 ^ 10 * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  have h415 : Real.exp 415 ≤ x :=
    le_trans (Real.exp_le_exp.2 (by linarith [Real.add_one_le_exp (6000 : ℝ)])) hx
  have hδ0 : 0 < 2 * q - 1 := lt_of_lt_of_le (by norm_num) hδ
  exact le_integral_rpow_normalisedSum_compMultExtension_largeQ_bb hX h415 (by linarith) hq1
    (by norm_num) (hundred_ninths_mul_le_rpow hδ)

/-- **L for `Y`, Lyapunov from `q = ½`**: for `x ≥ exp(e^{6000})`, `½ < q`, `δ = 2q - 1 < 10⁻⁸` and
`δΛ ≤ 1`, `10⁻¹⁰(log x)^{qδ}min{1/δ, Λ}^{3/4} ≤ E|Y(x)|^{2q}`:
`E|Y|^{2q} ≥ (E|Y|)^{2q} ≥ (10⁻⁸Λ^{3/4})^{2q}`
(`RMF.integral_norm_normalisedSum_compMultExtension_ge_explicit`) and `RMF.lyap_num`. -/
theorem le_integral_rpow_lyapunovRegime_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 1 / 2 < q) (hδ : 2 * q - 1 < 1 / 10 ^ 8)
    (hu : (2 * q - 1) * Real.log (Real.log x) ≤ 1) :
    1 / 10 ^ 10 * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  obtain ⟨hΛ, hL, -, -⟩ := loglog_facts_of_six_thousand hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx3 : 3 ≤ x := by
    have h1 := Real.add_one_le_exp (Real.exp 6000)
    have h2 := Real.add_one_le_exp (6000 : ℝ)
    linarith
  have hH : 1 / 10 ^ 8 * Real.log (Real.log x) ^ (3 / 4 : ℝ)
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ :=
    integral_norm_normalisedSum_compMultExtension_ge_explicit hX hx3
  have hLy := integral_rpow_le_rpow_integral_of_le (μ := μ) (p := q) (q := 1 / 2) (by norm_num)
    hq0.le (memLp_normalisedSum_compMultExtension hX x _)
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at hLy
  simp only [Real.rpow_one] at hLy
  have hE0 : 0 ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hE10 : 0 ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ :=
    integral_nonneg fun ω => norm_nonneg _
  have hpow : (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ)
        ^ (2 * q)
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
    calc (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ) ^ (2 * q)
        ≤ ((∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ) ^ (1 / 2 / q)) ^ (2 * q) :=
          Real.rpow_le_rpow hE10 hLy (by linarith)
      _ = _ := by
          rw [← Real.rpow_mul hE0, show 1 / 2 / q * (2 * q) = 1 by field_simp, Real.rpow_one]
  have h1 : (1 / 10 ^ 8 * Real.log (Real.log x) ^ (3 / 4 : ℝ)) ^ (2 * q)
      ≤ (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ)
          ^ (2 * q) :=
    Real.rpow_le_rpow (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)) hH
      (by linarith)
  exact le_trans (lyapunov_regime_arith hq0 hδ hL0 (by linarith) hu) (h1.trans hpow)

/-- **S for `Y`, the sliver**: for `x ≥ exp(e^{6000})`, `½ < q`, `δ = 2q - 1 < 10⁻¹¹` and
`δΛ ≥ 1`, `10⁻¹⁰(log x)^{qδ}min{1/δ, Λ}^{3/4} ≤ E|Y(x)|^{2q}`: S at `10⁻⁸`
(`RMF.le_integral_rpow_sliverRegime_eight`), Minkowski with `E|R|^{2q} ≤ 1`, and
`RMF.sliver_ext_arith`. -/
theorem le_integral_rpow_sliverRegime_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 1 / 2 < q) (hδ : 2 * q - 1 < 1 / 10 ^ 11)
    (hu : 1 ≤ (2 * q - 1) * Real.log (Real.log x)) :
    1 / 10 ^ 10 * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨-, hL, -, -⟩ := loglog_facts_of_six_thousand hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx1 : (1 : ℝ) ≤ x := (Real.one_lt_exp_iff.2 (Real.exp_pos _)).le.trans hx
  have hS := le_integral_rpow_sliverRegime_eight hX hx hq0 (by linarith) hu
  have hR := integral_rpow_norm_fracPartSum_le_one hX hx1 (q := q) (by linarith) (by linarith)
  have hM := rpow_inv_integral_rpow_weightedRademacherSum_le_add hX hx1 (r := 2 * q)
    (by linarith)
  exact sliver_ext_arith hq0 (two_rpow_le_of_sliver hδ) (sliver_target_ge hq0 hδ hL0 hu) hS hR
    (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _)
    (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) hM

end

/-! ### Every `x ≥ 3` -/

/-- **Above `½` with `c = 10⁻¹⁰`, for `Y` and every `x ≥ 3`**: for every Rademacher `X`, `x ≥ 3`
and `½ < q ≤ 1`, `10⁻¹⁰(log x)^{q(2q-1)}min{1/(2q-1), log log x}^{3/4} ≤ E|Y(x)|^{2q}`: for
`x ≥ exp(e^{6000})` BB (`2q - 1 ≥ 10⁻¹¹`), L and S; below it BB for `x ≥ e^{415}` and
`2q - 1 ≥ 10⁻¹¹`, and `E|Y(x)|^{2q} ≥ ¼` otherwise, where the target is at most `¼`
(`RMF.integral_rpow_weightedRademacherSum_ge_aboveHalf_explicit`'s case split). -/
theorem integral_rpow_normalisedSum_compMultExtension_ge_aboveHalf_explicit {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 3 ≤ x) (hq0 : 1 / 2 < q)
    (hq1 : q ≤ 1) :
    1 / 10 ^ 10 * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  rcases le_or_gt (Real.exp (Real.exp 6000)) x with hbig | hsmall
  · rcases le_or_gt (1 / 10 ^ 11) (2 * q - 1) with h | h
    · exact le_integral_rpow_bbRegime_ext hX hbig hq1 h
    · rcases le_or_gt ((2 * q - 1) * Real.log (Real.log x)) 1 with h' | h'
      · exact le_integral_rpow_lyapunovRegime_ext hX hbig hq0 (h.trans (by norm_num)) h'
      · exact le_integral_rpow_sliverRegime_ext hX hbig hq0 h h'.le
  have hL1 := one_le_log_of_three_le hx
  have hE := quarter_le_integral_rpow_normalisedSum_compMultExtension hX
    (by linarith : (1 : ℝ) ≤ x) hq0.le hq1
  rcases le_or_gt (1 / 10 ^ 11) (2 * q - 1) with hδ | hδ
  · rcases le_or_gt (Real.exp 415) x with h415 | h415
    · exact le_integral_rpow_normalisedSum_compMultExtension_largeQ_bb hX h415 hq0 hq1
        (by norm_num) (hundred_ninths_mul_le_rpow hδ)
    · have hL415 : Real.log x ≤ 415 := ((Real.log_lt_iff_lt_exp (by linarith)).2 h415).le
      exact (aboveHalf_target_le_quarter_of_le_415 hq0 hq1 hL1 hL415).trans hE
  · exact (aboveHalf_target_le_quarter_of_small hq0 hq1 (hδ.trans (by norm_num)) (by linarith)
      (Real.log_nonneg hL1) (loglog_lt_six_thousand (by linarith) hsmall)).trans hE

end RMF
