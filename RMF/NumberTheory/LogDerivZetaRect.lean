/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import PrimeNumberTheoremAnd.StrongPNT
import RMF.PNTPlus.MediumPNTExplicit
import RMF.NumberTheory.ZeroFreeExplicit

/-!
# `ζ'/ζ` on a fixed rectangle

Bounds for `ζ'/ζ`, and its holomorphy, on the rectangle `[1 - 10⁻¹⁶, 2] × [-e^{1000}, e^{1000}]`
minus `{1}`: the fixed contour of `RMF/NumberTheory/PNTFixedContour.lean`.

For `8 ≤ |t| ≤ e^{1000}` the closed disk of radius `R = 5·10⁻¹¹` about `s₀ = 1 + 10⁻¹² + it` is
zero-free by `RMF.zeta_zeroFree_explicit` (`10⁻⁷/log |Im ρ| ≥ 10⁻⁷/1001 > 4.9·10⁻¹¹` there).  So
`LogOfAnalyticFunction` (PNT+'s `PrimeNumberTheoremAnd.StrongPNT`) gives a logarithm `J` of
`z ↦ ζ(s₀ + z)` with `J' = ζ'/ζ` and `Re J = log ‖ζ(s₀ + z)‖ - log ‖ζ(s₀)‖ ≤ M = 47`, the last by
`ZetaUpperBndExplicit` on the disk and `ZetaInvBound2Explicit` at `s₀`
(`RMF/PNTPlus/MediumPNTExplicit.lean`).  `BorelCaratheodoryDeriv` (from the same PNT+ module)
then bounds `J'` by `16MR²/(R - r)³ ≈ 1.598·10¹³` on the disk of radius `r = 10⁻¹² + 10⁻¹⁶`, which
contains `[1 - 10⁻¹⁶, 1 + 10⁻¹²] + it`; to its right `triv_bound_zeta_explicit` applies.  For
`|t| < 8` the bounds are `logDeriv_zeta_le_smallT` and `LogDerivZetaBndUnifExplicit`, both from
`RMF/PNTPlus/MediumPNTExplicit.lean`.  Holomorphy is `LogDerivZetaHoloOn` (`ZetaBounds.lean`), with
`ζ ≠ 0` from `ZetaNoZerosInBoxThree` for `|t| ≤ 3` and `RMF.zeta_zeroFree_explicit` above.

## Main results

* `RMF.norm_logDeriv_zeta_le_of_disk`: Borel–Carathéodory for `ζ'/ζ` on a zero-free disk.
* `RMF.norm_logDeriv_zeta_le_disk`: `‖ζ'/ζ(s)‖ ≤ 1.6·10¹³` within `10⁻¹² + 10⁻¹⁶` of
  `1 + 10⁻¹² + it`, for `8 ≤ |t| ≤ e^{1000}`.
* `RMF.logDeriv_zeta_le_rect`: `‖ζ'/ζ(σ + it)‖ ≤ 10¹⁴` for `σ ≥ 1 - 10⁻¹⁶`, `8 ≤ |t| ≤ e^{1000}`;
  `RMF.logDeriv_zeta_le_horizontal`: the same on the horizontal sides `t = ∓e^{1000}`.
* `RMF.logDeriv_zeta_le_contourV`: `‖ζ'/ζ‖ ≤ 3·10³²` on `{1 - 10⁻¹⁶} × [-e^{1000}, e^{1000}]`.
* `RMF.holo_rect`: `ζ'/ζ` is holomorphic on `[1 - 10⁻¹⁶, 2] × [-e^{1000}, e^{1000}]` minus `{1}`.
-/

namespace RMF

open Complex Set Metric

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

/-! ### Numerals -/

/-- `e^{1000} + 1 ≤ e^{1001}`. -/
theorem exp_thousand_add_one_le : Real.exp 1000 + 1 ≤ Real.exp 1001 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h0 : (1 : ℝ) ≤ Real.exp 1000 := Real.one_le_exp (by norm_num)
  have he : Real.exp 1001 = Real.exp 1000 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos 1000).le
  rw [he]
  linarith

/-- `(34.65 · 1001) · (6 · 10¹⁵) ≤ e^{47}`, from `e ≥ 2.718`. -/
theorem le_exp_fortySeven : (3465 / 100 * 1001) * (6 * 10 ^ 15) ≤ Real.exp 47 := by
  have h1 : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    norm_num at this
    linarith
  have he : Real.exp 47 = Real.exp 1 ^ 47 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he]
  calc (3465 / 100 * 1001) * (6 * 10 ^ 15 : ℝ) ≤ (2718 / 1000) ^ 47 := by norm_num
    _ ≤ Real.exp 1 ^ 47 := pow_le_pow_left₀ (by norm_num) h1 47

/-! ### The zero-free region at bounded height -/

/-- `ζ` has no zeros with `2 ≤ |Im s| ≤ e^{1001}` and `Re s > 1 - 10⁻⁷/1001`:
`zeta_zeroFree_explicit`, with `log |Im s| ≤ 1001`. -/
theorem riemannZeta_ne_zero_of_le_exp {s : ℂ} (h2 : 2 ≤ |s.im|) (hT : |s.im| ≤ Real.exp 1001)
    (hσ : 1 - 1 / 10 ^ 7 / 1001 < s.re) : ζ s ≠ 0 := by
  intro hs
  have h := zeta_zeroFree_explicit s hs h2
  have hlog0 : 0 < Real.log |s.im| := Real.log_pos (by linarith)
  have hlog : Real.log |s.im| ≤ 1001 := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    exact hT
  have hd : (1 : ℝ) / 10 ^ 7 / 1001 ≤ 1 / 10 ^ 7 / Real.log |s.im| :=
    div_le_div_of_nonneg_left (by norm_num) hlog0 hlog
  linarith

/-! ### Borel–Carathéodory on a zero-free disk -/

/-- **Borel–Carathéodory for `ζ'/ζ`**: if `ζ` has neither zeros nor the pole on the closed disk of
radius `R` about `c`, and `‖ζ‖ ≤ e^M ‖ζ c‖` on the open disk, then `‖ζ'/ζ‖ ≤ 16MR²/(R - r)³` on
the closed disk of radius `r < R`.  `LogOfAnalyticFunction` gives a logarithm `J` of
`z ↦ ζ(c + z)` with `J 0 = 0`, `J' = ζ'/ζ` and `Re J ≤ M`, and `BorelCaratheodoryDeriv` bounds
`J'`. -/
theorem norm_logDeriv_zeta_le_of_disk {c : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hM : 0 < M) (hpole : ∀ z ∈ closedBall (0 : ℂ) R, c + z ≠ 1)
    (hzero : ∀ z ∈ closedBall (0 : ℂ) R, ζ (c + z) ≠ 0)
    (hbound : ∀ z ∈ ball (0 : ℂ) R, ‖ζ (c + z)‖ ≤ Real.exp M * ‖ζ c‖) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) r) :
    ‖ζ' (c + z) / ζ (c + z)‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  have hBan : AnalyticOnNhd ℂ (fun w ↦ ζ (c + w)) (closedBall (0 : ℂ) R) := fun w hw ↦
    (analyticAt_riemannZeta (hpole w hw)).comp (by fun_prop : AnalyticAt ℂ (fun w ↦ c + w) w)
  obtain ⟨J, hJan, hJ0, hJd, hJre⟩ := LogOfAnalyticFunction hr hrR hBan hzero
  have hc0 : ζ c ≠ 0 := by
    have := hzero 0 (mem_closedBall_self (hr.trans hrR).le)
    rwa [add_zero] at this
  have hre : ∀ w ∈ ball (0 : ℂ) R, (J w).re ≤ M := by
    intro w hw
    have h := hJre w hw
    simp only [add_zero] at h
    have hw0 : ζ (c + w) ≠ 0 := hzero w (ball_subset_closedBall hw)
    rw [← h, ← Real.log_div (norm_ne_zero_iff.mpr hw0) (norm_ne_zero_iff.mpr hc0),
      Real.log_le_iff_le_exp (div_pos (norm_pos_iff.mpr hw0) (norm_pos_iff.mpr hc0)),
      div_le_iff₀ (norm_pos_iff.mpr hc0)]
    exact hbound w hw
  have hBC := BorelCaratheodoryDeriv hM hr hrR hJan.analyticOn hJ0 hre hz
  rw [hJd z hz, deriv_comp_const_add riemannZeta c z] at hBC
  exact hBC

/-! ### The disks at `8 ≤ |t| ≤ e^{1000}` -/

/-- `‖ζ(s)‖ ≤ 34.65 · 1001` for `3 < |Im s| ≤ e^{1001}` and `1 - 1/2002 ≤ Re s ≤ 2`:
`ZetaUpperBndExplicit`, with `log |Im s| ≤ 1001`. -/
theorem norm_zeta_le_of_le_exp {s : ℂ} (h3 : 3 < |s.im|) (hT : |s.im| ≤ Real.exp 1001)
    (hσ : 1 - 1 / 2002 ≤ s.re) (hσ2 : s.re ≤ 2) : ‖ζ s‖ ≤ 3465 / 100 * 1001 := by
  have hlog0 : 0 < Real.log |s.im| := Real.log_pos (by linarith)
  have hlog : Real.log |s.im| ≤ 1001 := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    exact hT
  have hA : zetaStripA = 1 / 2 := rfl
  have hmem : s.re ∈ Icc (1 - zetaStripA / Real.log |s.im|) 2 := by
    refine ⟨?_, hσ2⟩
    have : (1 : ℝ) / 2002 ≤ zetaStripA / Real.log |s.im| := by
      rw [hA, le_div_iff₀ hlog0]
      linarith
    linarith
  have h := ZetaUpperBndExplicit s.re s.im h3 hmem
  rw [Complex.re_add_im] at h
  have hC : zetaUpperC ≤ 3465 / 100 := by
    have := zetaUpperC_le
    norm_num at this ⊢
    linarith
  exact h.trans (mul_le_mul hC hlog hlog0.le (by norm_num))

/-- `1 ≤ 6 · 10¹⁵ ‖ζ(1 + 10⁻¹² + it)‖` for `8 ≤ |t| ≤ e^{1000}`: `ZetaInvBound2Explicit`, with
`(10⁻¹²)^{-3/4} ≤ 10¹²` and `(log |t|)^{1/4} ≤ log |t| ≤ 1000`. -/
theorem one_le_norm_zeta_centre {t : ℝ} (h8 : 8 ≤ |t|) (hT : |t| ≤ Real.exp 1000) :
    1 ≤ 6 * 10 ^ 15 * ‖ζ (((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I)‖ := by
  have hσ : (1 + (1 / 10 : ℝ) ^ 12) ∈ Ioc 1 2 := ⟨by norm_num, by norm_num⟩
  have h := ZetaInvBound2Explicit hσ t (by linarith)
  have hsub : (1 + (1 / 10 : ℝ) ^ 12) - 1 = (1 / 10 : ℝ) ^ 12 := by ring
  rw [hsub] at h
  have hpow : ((1 / 10 : ℝ) ^ 12) ^ (-(3 : ℝ) / 4) ≤ 10 ^ 12 := by
    calc ((1 / 10 : ℝ) ^ 12) ^ (-(3 : ℝ) / 4) ≤ ((1 / 10 : ℝ) ^ 12) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      _ = 10 ^ 12 := by
          rw [Real.rpow_neg_one]
          norm_num
  have hlog1 : 1 ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  have hlogT : Real.log |t| ≤ 1000 := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    exact hT
  have hq : Real.log |t| ^ ((1 : ℝ) / 4) ≤ 1000 := by
    calc Real.log |t| ^ ((1 : ℝ) / 4) ≤ Real.log |t| ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
      _ = Real.log |t| := Real.rpow_one _
      _ ≤ 1000 := hlogT
  have hC := zetaInvBound2C_le
  have hp0 : 0 ≤ ((1 / 10 : ℝ) ^ 12) ^ (-(3 : ℝ) / 4) := Real.rpow_nonneg (by norm_num) _
  have hq0 : 0 ≤ Real.log |t| ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  have hb : 1 / ‖ζ (((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I)‖ ≤ 6 * 10 ^ 12 * 1000 :=
    h.trans (mul_le_mul (mul_le_mul hC hpow hp0 (by norm_num)) hq hq0 (by norm_num))
  have hne : ζ (((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
    norm_num
  rw [div_le_iff₀ (norm_pos_iff.mpr hne)] at hb
  linarith

/-- The points of the closed disk of radius `5·10⁻¹¹` about `1 + 10⁻¹² + it`, for
`8 ≤ |t| ≤ e^{1000}`, have `1 - 4.9·10⁻¹¹ ≤ Re ≤ 2` and `8 - 5·10⁻¹¹ ≤ |Im| ≤ e^{1001}`. -/
theorem disk_re_im_bounds {t : ℝ} (h8 : 8 ≤ |t|) (hT : |t| ≤ Real.exp 1000) {z : ℂ}
    (hz : ‖z‖ ≤ 5 * (1 / 10 : ℝ) ^ 11) :
    1 - 49 * (1 / 10 : ℝ) ^ 12 ≤ ((((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I) + z).re ∧
      ((((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I) + z).re ≤ 2 ∧
      8 - 5 * (1 / 10 : ℝ) ^ 11 ≤ |((((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I) + z).im| ∧
      |((((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I) + z).im| ≤ Real.exp 1001 := by
  have hre := abs_le.mp ((Complex.abs_re_le_norm z).trans hz)
  have him := (Complex.abs_im_le_norm z).trans hz
  have hcre : ((((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I) + z).re =
      1 + (1 / 10 : ℝ) ^ 12 + z.re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
  have hcim : ((((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I) + z).im = t + z.im := by
    simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, add_zero, zero_add]
  rw [hcre, hcim]
  have h1 := abs_add_le t z.im
  have h2 := abs_add_le (t + z.im) (-z.im)
  rw [abs_neg, add_neg_cancel_right] at h2
  have hT1 := exp_thousand_add_one_le
  have n1 : (1 : ℝ) + (1 / 10) ^ 12 - 5 * (1 / 10) ^ 11 = 1 - 49 * (1 / 10) ^ 12 := by norm_num
  have n2 : (1 : ℝ) + (1 / 10) ^ 12 + 5 * (1 / 10) ^ 11 ≤ 2 := by norm_num
  have n3 : (5 : ℝ) * (1 / 10) ^ 11 ≤ 1 := by norm_num
  refine ⟨by linarith [hre.1], by linarith [hre.2], by linarith, by linarith⟩

/-- **The disk lemma**: `‖ζ'/ζ(s)‖ ≤ 1.6·10¹³` for `‖s - (1 + 10⁻¹² + it)‖ ≤ 10⁻¹² + 10⁻¹⁶` and
`8 ≤ |t| ≤ e^{1000}`.  `norm_logDeriv_zeta_le_of_disk` with `R = 5·10⁻¹¹`, `M = 47`: the disk of
radius `R` is zero-free by `riemannZeta_ne_zero_of_le_exp`, `‖ζ‖ ≤ 34.65 · 1001` on it, and
`‖ζ‖ ≥ 1/(6·10¹⁵)` at its centre; `16MR²/(R - r)³ ≈ 1.598·10¹³`. -/
theorem norm_logDeriv_zeta_le_disk {t : ℝ} (h8 : 8 ≤ |t|) (hT : |t| ≤ Real.exp 1000) {s : ℂ}
    (hs : ‖s - (((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I)‖ ≤
      (1 / 10 : ℝ) ^ 12 + (1 / 10 : ℝ) ^ 16) :
    ‖ζ' s / ζ s‖ ≤ 16 * 10 ^ 12 := by
  have hpole : ∀ z ∈ closedBall (0 : ℂ) (5 * (1 / 10 : ℝ) ^ 11),
      (((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I) + z ≠ 1 := by
    intro z hz h1
    rw [mem_closedBall_zero_iff] at hz
    have := (disk_re_im_bounds h8 hT hz).2.2.1
    rw [h1] at this
    norm_num at this
  have hzero : ∀ z ∈ closedBall (0 : ℂ) (5 * (1 / 10 : ℝ) ^ 11),
      ζ ((((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I) + z) ≠ 0 := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    obtain ⟨h1, -, h3, h4⟩ := disk_re_im_bounds h8 hT hz
    have n1 : (2 : ℝ) ≤ 8 - 5 * (1 / 10) ^ 11 := by norm_num
    have n2 : (1 : ℝ) - 1 / 10 ^ 7 / 1001 < 1 - 49 * (1 / 10) ^ 12 := by norm_num
    exact riemannZeta_ne_zero_of_le_exp (by linarith) h4 (by linarith)
  have hbound : ∀ z ∈ ball (0 : ℂ) (5 * (1 / 10 : ℝ) ^ 11),
      ‖ζ ((((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I) + z)‖ ≤
        Real.exp 47 * ‖ζ (((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I)‖ := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    obtain ⟨h1, h2, h3, h4⟩ := disk_re_im_bounds h8 hT hz.le
    have n1 : (3 : ℝ) < 8 - 5 * (1 / 10) ^ 11 := by norm_num
    have n2 : (1 : ℝ) - 1 / 2002 ≤ 1 - 49 * (1 / 10) ^ 12 := by norm_num
    have hup := norm_zeta_le_of_le_exp (by linarith) h4 (by linarith) h2
    have hlow := one_le_norm_zeta_centre h8 hT
    have hn := norm_nonneg (ζ (((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I))
    calc ‖ζ ((((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I) + z)‖ ≤ 3465 / 100 * 1001 := hup
      _ ≤ 3465 / 100 * 1001 *
          (6 * 10 ^ 15 * ‖ζ (((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I)‖) :=
          le_mul_of_one_le_right (by norm_num) hlow
      _ = (3465 / 100 * 1001) * (6 * 10 ^ 15) *
          ‖ζ (((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I)‖ := by ring
      _ ≤ Real.exp 47 * ‖ζ (((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I)‖ :=
          mul_le_mul_of_nonneg_right le_exp_fortySeven hn
  have hr : (0 : ℝ) < (1 / 10) ^ 12 + (1 / 10) ^ 16 := by norm_num
  have hrR : (1 / 10 : ℝ) ^ 12 + (1 / 10) ^ 16 < 5 * (1 / 10) ^ 11 := by norm_num
  have hmem : s - (((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I) ∈
      closedBall (0 : ℂ) ((1 / 10 : ℝ) ^ 12 + (1 / 10) ^ 16) := by
    rw [mem_closedBall_zero_iff]
    exact hs
  have key := norm_logDeriv_zeta_le_of_disk hr hrR (by norm_num : (0 : ℝ) < 47) hpole hzero
    hbound hmem
  rw [add_sub_cancel] at key
  refine key.trans ?_
  norm_num

/-! ### The targets -/

/-- **`‖ζ'/ζ‖ ≤ 10¹⁴` on `[1 - 10⁻¹⁶, ∞) × {8 ≤ |t| ≤ e^{1000}}`**: the disk lemma
`norm_logDeriv_zeta_le_disk` for `σ ≤ 1 + 10⁻¹²`, and `triv_bound_zeta_explicit`
(`≤ 1/(σ - 1) + log 4 + 4`) to its right. -/
theorem logDeriv_zeta_le_rect : ∀ σ t : ℝ, 8 ≤ |t| → |t| ≤ Real.exp 1000 →
    1 - (1 / 10 : ℝ) ^ 16 ≤ σ → ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ 10 ^ 14 := by
  intro σ t h8 hT hσ
  rcases le_or_gt σ (1 + (1 / 10 : ℝ) ^ 12) with h | h
  · have hs : ‖((σ : ℂ) + t * I) - (((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I)‖ ≤
        (1 / 10 : ℝ) ^ 12 + (1 / 10 : ℝ) ^ 16 := by
      have e : ((σ : ℂ) + t * I) - (((1 + (1 / 10 : ℝ) ^ 12 : ℝ) : ℂ) + t * I) =
          ((σ - (1 + (1 / 10 : ℝ) ^ 12) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    exact (norm_logDeriv_zeta_le_disk h8 hT hs).trans (by norm_num)
  · have hδ : (0 : ℝ) < (1 / 10) ^ 12 := by norm_num
    have hσ1 : 1 < σ := by linarith
    have hb := triv_bound_zeta_explicit σ t hσ1
    rw [neg_div, norm_neg] at hb
    have hinv : (σ - 1)⁻¹ ≤ 10 ^ 12 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      have : ((10 : ℝ) ^ 12)⁻¹ = (1 / 10) ^ 12 := by norm_num
      linarith
    have hlog4 : Real.log 4 + 4 ≤ 6 := zetaTrivC_le
    have n : (10 : ℝ) ^ 12 + 6 ≤ 10 ^ 14 := by norm_num
    linarith

/-- `‖ζ'/ζ‖ ≤ 10¹⁴` on the horizontal sides `[1 - 10⁻¹⁶, ∞) × {∓e^{1000}}`, in the spelling of
the integrands of `I₂` and `I₈`. -/
theorem logDeriv_zeta_le_horizontal (σ : ℝ) (hσ : zetaSmallTσ ≤ σ) :
    ‖ζ' (σ - Real.exp 1000 * I) / ζ (σ - Real.exp 1000 * I)‖ ≤ 10 ^ 14 ∧
      ‖ζ' (σ + Real.exp 1000 * I) / ζ (σ + Real.exp 1000 * I)‖ ≤ 10 ^ 14 := by
  have h8 : (8 : ℝ) ≤ Real.exp 1000 := by
    have := Real.add_one_le_exp (1000 : ℝ)
    linarith
  have hE : |Real.exp 1000| = Real.exp 1000 := abs_of_pos (Real.exp_pos 1000)
  have hσ' : 1 - (1 / 10 : ℝ) ^ 16 ≤ σ := hσ
  constructor
  · have e : (σ : ℂ) - (Real.exp 1000 : ℝ) * I = σ + ((-Real.exp 1000 : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [e]
    exact logDeriv_zeta_le_rect σ (-Real.exp 1000) (by rw [abs_neg, hE]; exact h8)
      (by rw [abs_neg, hE]) hσ'
  · exact logDeriv_zeta_le_rect σ (Real.exp 1000) (by rw [hE]; exact h8) (by rw [hE]) hσ'

/-- **`‖ζ'/ζ‖ ≤ 3·10³²` on the vertical side `{1 - 10⁻¹⁶} × [-e^{1000}, e^{1000}]`**:
`logDeriv_zeta_le_smallT` for `|t| ≤ 3`, `LogDerivZetaBndUnifExplicit` for `3 < |t| < 8` (its
region `σ ≥ 1 - A/(log |t|)⁹`, `A ≥ 10⁻¹³`, `(log 8)⁹ ≤ 2.1⁹ < 1000`, contains `1 - 10⁻¹⁶`;
`≤ 10²⁸ · 1000`), and `logDeriv_zeta_le_rect` for `8 ≤ |t|`. -/
theorem logDeriv_zeta_le_contourV : ∀ t : ℝ, |t| ≤ Real.exp 1000 →
    ‖ζ' ((zetaSmallTσ : ℂ) + t * I) / ζ ((zetaSmallTσ : ℂ) + t * I)‖ ≤ 3 * 10 ^ 32 := by
  intro t hT
  have hσv : zetaSmallTσ = 1 - (1 / 10 : ℝ) ^ 16 := rfl
  rcases le_or_gt |t| 3 with h3 | h3
  · exact logDeriv_zeta_le_smallT h3
  rcases lt_or_ge |t| 8 with h8 | h8
  · have hlog0 : 0 < Real.log |t| := Real.log_pos (by linarith)
    have hlog8 : Real.log |t| ≤ 21 / 10 := by
      have h28 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      have hl2 := Real.log_two_lt_d9
      norm_num at hl2
      have := Real.log_le_log (by linarith) h8.le
      linarith
    have hpow : Real.log |t| ^ 9 ≤ 1000 := by
      calc Real.log |t| ^ 9 ≤ (21 / 10) ^ 9 := pow_le_pow_left₀ hlog0.le hlog8 9
        _ ≤ 1000 := by norm_num
    have hA := zetaLogDerivA_ge
    have hpos9 : 0 < Real.log |t| ^ 9 := pow_pos hlog0 9
    have hmem : zetaSmallTσ ∈ Ici (1 - zetaLogDerivA / Real.log |t| ^ 9) := by
      rw [mem_Ici, hσv]
      have h16 : (1 / 10 : ℝ) ^ 16 ≤ zetaLogDerivA / Real.log |t| ^ 9 := by
        rw [le_div_iff₀ hpos9]
        have := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ (1 / 10) ^ 16)
        have n : (1 / 10 : ℝ) ^ 16 * 1000 = (1 / 10) ^ 13 := by norm_num
        linarith
      linarith
    have h := LogDerivZetaBndUnifExplicit zetaSmallTσ t h3 hmem
    have hC := zetaLogDerivUnifC_le
    calc _ ≤ zetaLogDerivUnifC * Real.log |t| ^ 9 := h
      _ ≤ 10 ^ 28 * 1000 := mul_le_mul hC hpow hpos9.le (by norm_num)
      _ ≤ 3 * 10 ^ 32 := by norm_num
  · exact (logDeriv_zeta_le_rect zetaSmallTσ t h8 hT hσv.ge).trans (by norm_num)

/-- **`ζ'/ζ` is holomorphic on `[1 - 10⁻¹⁶, 2] × [-e^{1000}, e^{1000}]` minus `{1}`**, in the
spelling of `SmoothedChebyshevPull1`'s hypothesis: `ζ ≠ 0` there by `ZetaNoZerosInBoxThree` for
`|t| ≤ 3` and `riemannZeta_ne_zero_of_le_exp` (`zeta_zeroFree_explicit`) for `|t| > 3`. -/
theorem holo_rect : HolomorphicOn (ζ' / ζ)
    ((Icc zetaSmallTσ 2) ×ℂ (Icc (-Real.exp 1000) (Real.exp 1000)) \ {1}) := by
  have hσv : zetaSmallTσ = 1 - (1 / 10 : ℝ) ^ 16 := rfl
  apply LogDerivZetaHoloOn
  · exact Set.notMem_sdiff_of_mem rfl
  · intro s hs
    obtain ⟨⟨hre1, -⟩, him1, him2⟩ := Complex.mem_reProdIm.mp hs.1
    rcases le_or_gt 1 s.re with h1 | h1
    · exact riemannZeta_ne_zero_of_one_le_re h1
    rcases le_or_gt |s.im| 3 with h3 | h3
    · rw [← Complex.re_add_im s]
      exact ZetaNoZerosInBoxThree s.im h3 s.re hre1
    · have hT : |s.im| ≤ Real.exp 1000 := abs_le.mpr ⟨him1, him2⟩
      have hT1 := exp_thousand_add_one_le
      have n : (1 : ℝ) - 1 / 10 ^ 7 / 1001 < 1 - (1 / 10) ^ 16 := by norm_num
      exact riemannZeta_ne_zero_of_le_exp (by linarith) (by linarith) (by linarith)

end RMF
