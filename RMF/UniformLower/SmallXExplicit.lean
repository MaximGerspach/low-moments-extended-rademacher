/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.SmallXBounds
import RMF.UniformLower.SmallXCells

/-!
# Below `½` for small `x`, elementary

`RMF.le_integral_rpow_weightedRademacherSum_small_explicit`: for a Rademacher family, `x ≥ 3`
with `Λ = log log x ≤ 67.17` and `0 < q < ½`, `10⁻¹⁰min{Λ, 1/(1-2q)}Λ^{-q/2} ≤ E|S(x)|^{2q}`, by
the three bounds of `RMF/UniformLower/SmallXBounds.lean`, each at least twice the target:

* NH, `(1-2q)Λ ≤ 17`: H, `(1 + log x)^{-(1-2q)} ≥ e^{-log 2 - 17} ≥ 2·10⁻¹⁰·70`
  (`RMF.two_mul_smallTarget_le_holder`);
* otherwise `Λ > 17`, and the cell of `RMF.smallCells_spec`: F for `1 - 2q ≥ u_F`
  (`RMF.two_mul_smallTarget_le_floor`), I at the cell's `b` below
  (`RMF.two_mul_smallTarget_le_interp`); the certificates' functions `RMF.smallPhiF`,
  `RMF.smallPhiI` are monotone in `u = 1 - 2q` with their minimum at `u_F`.
-/

open MeasureTheory

namespace RMF

/-! ### The target -/

/-- `T ≤ E` from `2T ≤ B ≤ E` and `T ≥ 0`. -/
lemma le_of_two_mul_le {T B E : ℝ} (hT : 0 ≤ T) (h1 : 2 * T ≤ B) (h2 : B ≤ E) : T ≤ E := by
  linarith

/-- **The target, in exponential form**: for `0 ≤ q < ½` and `0 < Λ₀ ≤ Λ`,
`2·10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ exp(log 2 - 10 log 10 - log(1-2q) - (q/2)log Λ₀)`. -/
lemma two_mul_smallTarget_le {q Λ Λ₀ : ℝ} (hq0 : 0 ≤ q) (hq : q < 1 / 2) (hΛ₀ : 0 < Λ₀)
    (hΛ : Λ₀ ≤ Λ) :
    2 * (1 / 10 ^ 10 * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2))))
      ≤ Real.exp (Real.log 2 - 10 * Real.log 10 - Real.log (1 - 2 * q)
          - q / 2 * Real.log Λ₀) := by
  have hu : 0 < 1 - 2 * q := by linarith
  have hΛ0 : 0 < Λ := lt_of_lt_of_le hΛ₀ hΛ
  have hp : Λ ^ (-(q / 2)) ≤ Λ₀ ^ (-(q / 2)) :=
    Real.rpow_le_rpow_of_nonpos hΛ₀ hΛ (by linarith)
  have hm : min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)) ≤ (1 - 2 * q)⁻¹ * Λ₀ ^ (-(q / 2)) :=
    mul_le_mul (min_le_right _ _) hp (Real.rpow_nonneg hΛ0.le _) (inv_nonneg.2 hu.le)
  have h10 : 10 * Real.log 10 = Real.log (10 ^ 10) := by
    rw [Real.log_pow]
    norm_num
  have e : Real.exp (Real.log 2 - 10 * Real.log 10 - Real.log (1 - 2 * q)
        - q / 2 * Real.log Λ₀)
      = 2 * (1 / 10 ^ 10 * ((1 - 2 * q)⁻¹ * Λ₀ ^ (-(q / 2)))) := by
    rw [Real.exp_sub, Real.exp_sub, Real.exp_sub, Real.exp_log two_pos, Real.exp_log hu, h10,
      Real.exp_log (by norm_num), Real.rpow_def_of_pos hΛ₀,
      show Real.log Λ₀ * -(q / 2) = -(q / 2 * Real.log Λ₀) by ring, Real.exp_neg]
    field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 10)
  linarith

/-! ### The three regimes' arithmetic -/

/-- **NH, Hölder near `½`**: for `0 < q < ½`, `L > 1` with `log L ≤ 70` and
`(1-2q)log L ≤ 17`, `2·10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ (1 + L)^{-(1-2q)}`, `Λ = log L`: the
target is at most `10⁻¹⁰·70`, and `(1 + L)^{-u} ≥ (2L)^{-u} ≥ e^{-log 2 - 17}`. -/
lemma two_mul_smallTarget_le_holder {q L : ℝ} (hq0 : 0 < q) (hq : q < 1 / 2) (hL : 1 < L)
    (hΛ : Real.log L ≤ 70) (hu : (1 - 2 * q) * Real.log L ≤ 17) :
    2 * (1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))))
      ≤ (1 + L) ^ (-(1 - 2 * q)) := by
  have hΛ0 : 0 < Real.log L := Real.log_pos hL
  have hT : min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)) ≤ 70 := by
    rcases le_or_gt 1 (Real.log L) with h1 | h1
    · calc min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)) ≤ Real.log L * 1 :=
            mul_le_mul (min_le_left _ _) (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith))
              (Real.rpow_nonneg hΛ0.le _) hΛ0.le
        _ ≤ 70 := by linarith
    · calc min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))
            ≤ Real.log L * Real.log L ^ (-(q / 2)) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hΛ0.le _)
        _ = Real.log L ^ (1 + -(q / 2)) := by rw [Real.rpow_add hΛ0, Real.rpow_one]
        _ ≤ 1 := Real.rpow_le_one hΛ0.le h1.le (by linarith)
        _ ≤ 70 := by norm_num
  have hH : Real.exp (-Real.log 2 - 17) ≤ (1 + L) ^ (-(1 - 2 * q)) := by
    have h2L : (2 * L) ^ (-(1 - 2 * q)) ≤ (1 + L) ^ (-(1 - 2 * q)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    rw [Real.rpow_def_of_pos (by linarith),
      Real.log_mul two_ne_zero (by linarith : (0 : ℝ) < L).ne'] at h2L
    refine le_trans (Real.exp_le_exp.2 ?_) h2L
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h1 : (1 - 2 * q) * Real.log 2 ≤ 1 * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hl2
    linarith
  have hnum : (2 : ℝ) * (1 / 10 ^ 10 * 70) ≤ Real.exp (-Real.log 2 - 17) := by
    interval_decide (trust := kernel)
  linarith

/-- **An F cell**: for `0 < q < ½`, `L > 0` with `1 ≤ Λ₀ ≤ log L ≤ Λ₁`, `8 ≤ Λ₁`,
`0 < u_F ≤ 1 - 2q` and `smallPhiF u_F Λ₀ Λ₁ ≥ 0`,
`2·10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ 2^{-(1-2q)}3^{-(1-q)}(0.23/L)^q`, `Λ = log L`: `smallPhiF` is
increasing in `u`, its slope `Λ₁/2 - log 2 - (log 3 + log 0.23)/2 - (log Λ₀)/4` being `≥ 0`. -/
lemma two_mul_smallTarget_le_floor {q L Λ₀ Λ₁ uF : ℝ} (hq0 : 0 < q) (hq : q < 1 / 2)
    (hL : 0 < L) (hΛ₀1 : 1 ≤ Λ₀) (hΛ₀ : Λ₀ ≤ Real.log L) (hΛ₁ : Real.log L ≤ Λ₁)
    (hΛ₁8 : 8 ≤ Λ₁) (huF0 : 0 < uF) (huF : uF ≤ 1 - 2 * q) (hcert : 0 ≤ smallPhiF uF Λ₀ Λ₁) :
    2 * (1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))))
      ≤ (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (23 / (100 * L)) ^ q := by
  -- the slope
  have hl2 := Real.log_two_lt_d9
  have hl3 : Real.log 3 < 2 * Real.log 2 := by
    have h := Real.log_lt_log (by norm_num) (by norm_num : (3 : ℝ) < 2 ^ 2)
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  have hl023 : Real.log (23 / 100) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hlΛ₀ : Real.log Λ₀ ≤ Λ₀ - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hslope : 0 ≤ Λ₁ / 2 - Real.log 2 - Real.log 3 / 2 - Real.log (23 / 100) / 2
      - Real.log Λ₀ / 4 := by
    linarith
  have hmono : smallPhiF uF Λ₀ Λ₁ ≤ smallPhiF (1 - 2 * q) Λ₀ Λ₁ := by
    have key : smallPhiF (1 - 2 * q) Λ₀ Λ₁ - smallPhiF uF Λ₀ Λ₁
        = (1 - 2 * q - uF) * (Λ₁ / 2 - Real.log 2 - Real.log 3 / 2 - Real.log (23 / 100) / 2
          - Real.log Λ₀ / 4) + (Real.log (1 - 2 * q) - Real.log uF) := by
      unfold smallPhiF
      ring
    have hlog : Real.log uF ≤ Real.log (1 - 2 * q) := Real.log_le_log huF0 huF
    have := mul_nonneg (sub_nonneg.2 huF) hslope
    linarith
  -- the floor, in exponential form
  have hF : (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (23 / (100 * L)) ^ q
      = Real.exp (Real.log 2 * -(1 - 2 * q) + Real.log 3 * -(1 - q)
          + q * (Real.log (23 / 100) - Real.log L)) := by
    rw [Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
      Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 23 / (100 * L)), ← Real.exp_add,
      ← Real.exp_add, show (23 : ℝ) / (100 * L) = 23 / 100 / L by ring,
      Real.log_div (by norm_num) hL.ne']
    ring_nf
  rw [hF]
  refine (two_mul_smallTarget_le hq0.le hq (by linarith) hΛ₀).trans (Real.exp_le_exp.2 ?_)
  have hqL : q * Real.log L ≤ q * Λ₁ := mul_le_mul_of_nonneg_left hΛ₁ hq0.le
  unfold smallPhiF at hmono hcert
  linarith

/-- **An I cell**: for `0 < q < ½`, `L > 1` with `1 ≤ Λ₀ ≤ log L ≤ Λ₁`, `½ < b ≤ 1`,
`17 < (1-2q)log L`, `1 - 2q ≤ u_F` and `smallPhiI u_F Λ₀ Λ₁ b ≥ 0`,
`2·10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ (25L^{bδ}min{1/δ, Λ}^{3/4})^{-(1-2q)/δ}`, `δ = 2b - 1`,
`Λ = log L`: `smallPhiI` is decreasing in `u` where `uΛ₁ > 17`, its slope being `1/u - C` with
`C ≥ bΛ₁ ≥ 1/u`. -/
lemma two_mul_smallTarget_le_interp {q L Λ₀ Λ₁ uF b : ℝ} (hq0 : 0 < q) (hq : q < 1 / 2)
    (hL : 1 < L) (hΛ₀1 : 1 ≤ Λ₀) (hΛ₀ : Λ₀ ≤ Real.log L) (hΛ₁ : Real.log L ≤ Λ₁)
    (hb : 1 / 2 < b) (hb1 : b ≤ 1) (hu17 : 17 < (1 - 2 * q) * Real.log L)
    (huF : 1 - 2 * q ≤ uF) (hcert : 0 ≤ smallPhiI uF Λ₀ Λ₁ b) :
    2 * (1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))))
      ≤ (25 * (L ^ (b * (2 * b - 1)) * min (2 * b - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ)))
          ^ (-((1 - 2 * q) / (2 * b - 1))) := by
  have hu : 0 < 1 - 2 * q := by linarith
  have hδ : 0 < 2 * b - 1 := by linarith
  have hδ1 : 2 * b - 1 ≤ 1 := by linarith
  have hΛ0 : 0 < Real.log L := Real.log_pos hL
  have hL0 : 0 < L := by linarith
  -- the slope
  have hA0 : 0 ≤ (Real.log 25 - 3 / 4 * Real.log (2 * b - 1)) / (2 * b - 1) := by
    have h1 : Real.log (2 * b - 1) ≤ 0 := Real.log_nonpos hδ.le hδ1
    have h2 : 0 ≤ Real.log 25 := Real.log_nonneg (by norm_num)
    exact div_nonneg (by linarith) hδ.le
  have hlΛ₀ : 0 ≤ Real.log Λ₀ := Real.log_nonneg hΛ₀1
  have hinv : 1 / (1 - 2 * q) ≤ b * Λ₁ := by
    rw [div_le_iff₀ hu]
    have h1 : 17 < (1 - 2 * q) * Λ₁ :=
      lt_of_lt_of_le hu17 (mul_le_mul_of_nonneg_left hΛ₁ hu.le)
    have h2 : 1 / 2 * ((1 - 2 * q) * Λ₁) ≤ b * Λ₁ * (1 - 2 * q) := by
      have h3 : 0 ≤ (1 - 2 * q) * Λ₁ := by linarith
      nlinarith
    linarith
  have hmono : smallPhiI uF Λ₀ Λ₁ b ≤ smallPhiI (1 - 2 * q) Λ₀ Λ₁ b := by
    have key : smallPhiI (1 - 2 * q) Λ₀ Λ₁ b - smallPhiI uF Λ₀ Λ₁ b
        = (uF - (1 - 2 * q)) * ((Real.log 25 - 3 / 4 * Real.log (2 * b - 1)) / (2 * b - 1)
          + b * Λ₁ + Real.log Λ₀ / 4) - (Real.log uF - Real.log (1 - 2 * q)) := by
      unfold smallPhiI
      ring
    have hlog : Real.log uF - Real.log (1 - 2 * q) ≤ (uF - (1 - 2 * q)) * (1 / (1 - 2 * q)) := by
      rw [← Real.log_div (by linarith) hu.ne']
      have h := Real.log_le_sub_one_of_pos (div_pos (by linarith) hu : 0 < uF / (1 - 2 * q))
      have e : uF / (1 - 2 * q) - 1 = (uF - (1 - 2 * q)) * (1 / (1 - 2 * q)) := by
        field_simp
      linarith
    have hstep : (uF - (1 - 2 * q)) * (1 / (1 - 2 * q))
        ≤ (uF - (1 - 2 * q)) * ((Real.log 25 - 3 / 4 * Real.log (2 * b - 1)) / (2 * b - 1)
          + b * Λ₁ + Real.log Λ₀ / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  -- the interpolation bound, in exponential form, at `min{1/δ, Λ} ≤ 1/δ`
  have hm0 : 0 < min (2 * b - 1)⁻¹ (Real.log L) := lt_min (inv_pos.2 hδ) hΛ0
  have hLb : 0 < L ^ (b * (2 * b - 1)) := Real.rpow_pos_of_pos hL0 _
  have hδ34 : 0 < ((2 * b - 1)⁻¹) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (inv_pos.2 hδ) _
  have hbase0 : 0 < 25 * (L ^ (b * (2 * b - 1))
      * min (2 * b - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ)) :=
    mul_pos (by norm_num) (mul_pos hLb (Real.rpow_pos_of_pos hm0 _))
  have hbaseW : 25 * (L ^ (b * (2 * b - 1)) * min (2 * b - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ))
      ≤ 25 * (L ^ (b * (2 * b - 1)) * ((2 * b - 1)⁻¹) ^ (3 / 4 : ℝ)) := by
    have h1 := Real.rpow_le_rpow hm0.le (min_le_left (2 * b - 1)⁻¹ (Real.log L))
      (by norm_num : (0 : ℝ) ≤ 3 / 4)
    have h2 := mul_le_mul_of_nonneg_left h1 hLb.le
    linarith
  have hexp0 : -((1 - 2 * q) / (2 * b - 1)) ≤ 0 := by
    have := div_pos hu hδ
    linarith
  have hW := Real.rpow_le_rpow_of_nonpos hbase0 hbaseW hexp0
  have hWe : (25 * (L ^ (b * (2 * b - 1)) * ((2 * b - 1)⁻¹) ^ (3 / 4 : ℝ)))
        ^ (-((1 - 2 * q) / (2 * b - 1)))
      = Real.exp (-((1 - 2 * q) / (2 * b - 1) * (Real.log 25 - 3 / 4 * Real.log (2 * b - 1)))
          - (1 - 2 * q) * b * Real.log L) := by
    rw [Real.rpow_def_of_pos (mul_pos (by norm_num) (mul_pos hLb hδ34)),
      Real.log_mul (by norm_num) (mul_pos hLb hδ34).ne', Real.log_mul hLb.ne' hδ34.ne',
      Real.log_rpow hL0, Real.log_rpow (inv_pos.2 hδ), Real.log_inv]
    congr 1
    have e1 : b * (2 * b - 1) * Real.log L * ((1 - 2 * q) / (2 * b - 1))
        = (1 - 2 * q) * b * Real.log L := by
      rw [mul_div_assoc']
      exact div_eq_of_eq_mul hδ.ne' (by ring)
    linear_combination (-1 : ℝ) * e1
  rw [hWe] at hW
  refine (two_mul_smallTarget_le hq0.le hq (by linarith) hΛ₀).trans
    (le_trans (Real.exp_le_exp.2 ?_) hW)
  have hqL : (1 - 2 * q) * b * Real.log L ≤ (1 - 2 * q) * b * Λ₁ :=
    mul_le_mul_of_nonneg_left hΛ₁ (by positivity)
  unfold smallPhiI at hmono hcert
  linarith

/-! ### The theorem -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Below `½` with `c = 10⁻¹⁰` for `3 ≤ x` with `log log x ≤ 67.17`, elementary**: for
every Rademacher `X`, every such `x` and every `0 < q < ½`,
`10⁻¹⁰min{log log x, 1/(1-2q)}(log log x)^{-q/2} ≤ E|S(x)|^{2q}`, every margin at least `×2`: H
where `(1-2q)log log x ≤ 17`, else the cell of `RMF.smallCells_spec`, F for `1 - 2q ≥ u_F` and I
at the cell's `b` below. -/
theorem le_integral_rpow_weightedRademacherSum_small_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 3 ≤ x)
    (hΛ : Real.log (Real.log x) ≤ 67.17) (hq0 : 0 < q) (hq : q < 1 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  have hL1 : 1 < Real.log x :=
    (Real.lt_log_iff_exp_lt (by linarith)).2 (by linarith [Real.exp_one_lt_d9])
  have hΛ0 : 0 < Real.log (Real.log x) := Real.log_pos hL1
  have hT0 : 0 ≤ 1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
      * Real.log (Real.log x) ^ (-(q / 2))) :=
    mul_nonneg (by norm_num) (mul_nonneg (le_min hΛ0.le (inv_nonneg.2 (by linarith)))
      (Real.rpow_nonneg hΛ0.le _))
  rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) 17 with hNH | hNH
  · -- NH: Hölder
    exact le_of_two_mul_le hT0 (two_mul_smallTarget_le_holder hq0 hq hL1 (by linarith) hNH)
      (le_integral_rpow_weightedRademacherSum_holder hX (by linarith) hq0 hq)
  have hΛ17 : 17 < Real.log (Real.log x) := by
    have : (1 - 2 * q) * Real.log (Real.log x) ≤ 1 * Real.log (Real.log x) :=
      mul_le_mul_of_nonneg_right (by linarith) hΛ0.le
    linarith
  obtain ⟨Λ₀, Λ₁, uF, b, hΛ₀1, hΛ₀, hΛ₁, hΛ₁8, huF0, hb, hb1, hF, hI⟩ :=
    smallCells_spec hΛ17.le hΛ
  rcases le_or_gt uF (1 - 2 * q) with hu | hu
  · -- F: the floor, at `x ≥ exp(e^{17}) ≥ 10^{16}`
    have h1 : Real.exp 17 < Real.log x := (Real.lt_log_iff_exp_lt (by linarith)).1 hΛ17
    have h2 : (40 : ℝ) ≤ Real.exp 17 := by interval_decide (trust := kernel)
    have h3 : Real.exp 40 < x := (Real.lt_log_iff_exp_lt (by linarith)).1 (by linarith)
    have h4 : (10 : ℝ) ^ 16 ≤ Real.exp 40 := by interval_decide (trust := kernel)
    exact le_of_two_mul_le hT0
      (two_mul_smallTarget_le_floor hq0 hq (by linarith) hΛ₀1 hΛ₀ hΛ₁ hΛ₁8 huF0 hu hF)
      (le_integral_rpow_weightedRademacherSum_floor_small hX (by linarith) hq0 hq.le)
  · rcases hI with hI | hI
    · -- no I in this cell: `u_FΛ₁ ≤ 17 < uΛ`
      have h1 : (1 - 2 * q) * Real.log (Real.log x) ≤ uF * Λ₁ :=
        mul_le_mul hu.le hΛ₁ hΛ0.le huF0.le
      linarith
    · -- I: interpolation at the cell's `b`
      exact le_of_two_mul_le hT0
        (two_mul_smallTarget_le_interp hq0 hq hL1 hΛ₀1 hΛ₀ hΛ₁ hb hb1 hNH hu.le hI)
        (le_integral_rpow_weightedRademacherSum_interp hX hx hq0 hq hb hb1)

end RMF
