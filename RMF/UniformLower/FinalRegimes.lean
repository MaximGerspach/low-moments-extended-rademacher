/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.FinalNumerals
import RMF.UniformLower.LowAboveHalf
import RMF.UniformLower.SubtractedBelowHalf
import RMF.UniformLower.SubtractedSliver
import RMF.Weighted.ULowQExplicit

/-!
# The final assembly: the seven regimes

For a Rademacher family and `x ≥ exp(e^{6000})`, `Λ = log log x`, each regime's conjunct of
`RMF.weighted_rademacher_moments_lower_uniform_explicit`:

* **F**, `qΛ ≤ 37/2` (`RMF.le_integral_rpow_floorRegime`): the floor
  `2^{-(1-2q)}3^{-(1-q)}(0.49/log x)^q` and `RMF.floor_num`;
* **B1**, `37/2 < qΛ`, `q ≤ 9/20`, and **B2**, `9/20 ≤ q < ½` (`RMF.le_integral_rpow_mainB1Regime`,
  `RMF.le_integral_rpow_mainB2Regime`): the reduction at the tilt `V = 32/q`
  (`RMF.exists_level_belowHalf`), the main term at `σ = 2V/log x` on the scale `k = 21` (B1) or
  `21 ≤ k ≤ 20 + min(K_max(q), T - 2020)` (B2), the subtracted term
  (`RMF.integral_rpow_lineDiv_le_subtracted_belowHalf`), `RMF.PhiB1_ge`, `RMF.PhiB2_ge`;
* **H**, `q = ½` (`RMF.le_integral_norm_halfRegime`): `V = 64` (`RMF.exists_level_aboveHalf`), the
  scales `21 ≤ k ≤ T - 2000`, `E|S(x)| ≥ 10⁻⁷Λ^{3/4}` (`RMF.cHalfLB_ge`);
* **L**, `½ < q`, `δ = 2q - 1 < 10⁻⁸`, `δΛ ≤ 1` (`RMF.le_integral_rpow_lyapunovRegime`): Lyapunov
  from H;
* **S**, the same with `δΛ ≥ 1` (`RMF.le_integral_rpow_sliverRegime`): `V = 64`, `N_q(k) ≥ e^{qδk}`,
  the scales `T - 2000 - J ≤ k ≤ T - 2000` with `J = ⌊1/(2δ)⌋`, the subtracted term
  (`RMF.integral_rpow_lineDiv_le_subtracted_sliver`), `RMF.PhiSl_ge`;
* **BB**, `δ ≥ 10⁻⁸` (`RMF.le_integral_rpow_bbRegime`): Bonami–Beckner.

`T` is the damping level of `RMF.exists_damping_level` at `σ = 2V/log x`.  The analysis (the
integrals) and the arithmetic are kept apart: each regime passes its integral bounds to an
arithmetic lemma over plain reals.
-/

open MeasureTheory

namespace RMF

/-! ### The constants -/

/-- `RMF.perScaleConst q K ≥ 0` for `0 ≤ q ≤ 11/20`. -/
lemma perScaleConst_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 11 / 20) (K : ℕ) :
    0 ≤ perScaleConst q K := by
  have hc3 := c3FloorK_pos hq0 hq1 K
  have hP : 0 < 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
  unfold perScaleConst
  positivity

/-- `RMF.perScaleLow2 q ≥ 0`. -/
lemma perScaleLow2_nonneg (q : ℝ) : 0 ≤ perScaleLow2 q := by
  have hP : 0 < 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
  unfold perScaleLow2
  positivity

/-- `K_max(q) ≤ 1/(1 - 2q)` for `0 ≤ q < ½`. -/
lemma c3Kmax_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1 / 2) : (c3Kmax q : ℝ) ≤ 1 / (1 - 2 * q) := by
  have hw : 1 ≤ 1 / (1 - 2 * q) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  unfold c3Kmax
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le hw (Nat.floor_le (by linarith))

/-- `log q + Λ ≥ 2040` for `Λ ≥ 6000` and `qΛ ≥ 37/2`: `log q ≥ log(37/2) - log Λ` and
`log Λ ≤ Λ/10 + log 10 - 1`. -/
lemma log_add_ge_of_mul_ge {q Λ : ℝ} (hΛ : 6000 ≤ Λ) (hqΛ : 37 / 2 ≤ q * Λ) :
    2040 ≤ Real.log q + Λ := by
  have hΛ0 : 0 < Λ := by linarith
  have hq' : 37 / 2 / Λ ≤ q := by
    rw [div_le_iff₀ hΛ0]
    linarith
  have h1 : Real.log (37 / 2 / Λ) ≤ Real.log q := Real.log_le_log (by positivity) hq'
  rw [Real.log_div (by norm_num) hΛ0.ne'] at h1
  have h2 : Real.log (Λ / 10) ≤ Λ / 10 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hΛ0.ne' (by norm_num)] at h2
  have h3 : (29 / 10 : ℝ) ≤ Real.log (37 / 2) := by interval_decide (trust := kernel)
  have h4 : Real.log 10 ≤ 231 / 100 := by interval_decide (trust := kernel)
  linarith

/-! ### Arithmetic -/

/-- **The floor's arithmetic**: for `q > 0`, `Λ = log L ≥ 6000` and `qΛ ≤ 37/2`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ 2^{-(1-2q)}3^{-(1-q)}(0.49/L)^q` (`RMF.floor_num`). -/
lemma floor_regime_arith {q L : ℝ} (hq0 : 0 < q) (hL : 0 < L) (hΛ : 6000 ≤ Real.log L)
    (hqΛ : q * Real.log L ≤ 37 / 2) :
    1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      ≤ (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (49 / (100 * L)) ^ q := by
  have hq6 : q * 6000 ≤ q * Real.log L := mul_le_mul_of_nonneg_left hΛ hq0.le
  have hqs : q ≤ 37 / 12000 := by linarith
  have hb : 1 - 37 / 6000 ≤ 1 - 2 * q := by linarith
  have hmin : min (Real.log L) (1 - 2 * q)⁻¹ ≤ 6000 / 5963 := by
    refine (min_le_right _ _).trans ?_
    calc (1 - 2 * q)⁻¹ ≤ (1 - 37 / 6000)⁻¹ := inv_anti₀ (by norm_num) hb
      _ = 6000 / 5963 := by norm_num
  have hpow : Real.log L ^ (-(q / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hpow0 : 0 ≤ Real.log L ^ (-(q / 2)) := Real.rpow_nonneg (by linarith) _
  have hT : min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)) ≤ 6000 / 5963 := by
    calc _ ≤ 6000 / 5963 * 1 := mul_le_mul hmin hpow hpow0 (by norm_num)
      _ = 6000 / 5963 := mul_one _
  have h2 : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (-(1 - 2 * q)) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : (-1 : ℝ) ≤ -(1 - 2 * q))
    rw [Real.rpow_neg_one] at h
    linarith
  have h3 : (1 : ℝ) / 3 ≤ (3 : ℝ) ^ (-(1 - q)) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by linarith : (-1 : ℝ) ≤ -(1 - q))
    rw [Real.rpow_neg_one] at h
    linarith
  have h49 : Real.exp (37 / 12000 * Real.log (49 / 100)) * Real.exp (-(37 / 2))
      ≤ (49 / (100 * L)) ^ q := by
    rw [show (49 : ℝ) / (100 * L) = 49 / 100 / L by ring, Real.rpow_def_of_pos (by positivity),
      Real.log_div (by norm_num) hL.ne', ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hl : Real.log (49 / 100) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    have h1 := mul_le_mul_of_nonpos_right hqs hl
    linarith
  have hnum := floor_num
  have he0 : 0 ≤ Real.exp (37 / 12000 * Real.log (49 / 100)) * Real.exp (-(37 / 2)) := by
    positivity
  calc 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      ≤ 1 / 10 ^ 10 * (6000 / 5963) := mul_le_mul_of_nonneg_left hT (by norm_num)
    _ ≤ 1 / 2 * (1 / 3)
          * (Real.exp (37 / 12000 * Real.log (49 / 100)) * Real.exp (-(37 / 2))) := by
        linarith
    _ ≤ _ := mul_le_mul (mul_le_mul h2 h3 (by norm_num) (by positivity)) h49 he0 (by positivity)

/-- **Lyapunov's arithmetic**: for `½ < q`, `δ = 2q - 1 < 10⁻⁸`, `Λ = log L ≥ 1` and `δΛ ≤ 1`,
`10⁻¹⁰L^{qδ}min{1/δ, Λ}^{3/4} ≤ (10⁻⁸Λ^{3/4})^{2q}` (`RMF.lyap_num`). -/
lemma lyapunov_regime_arith {q L : ℝ} (hq0 : 1 / 2 < q) (hδ : 2 * q - 1 < 1 / 10 ^ 8)
    (hL : 0 < L) (hΛ : 1 ≤ Real.log L) (hu : (2 * q - 1) * Real.log L ≤ 1) :
    1 / 10 ^ 10 * (L ^ (q * (2 * q - 1)) * min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ))
      ≤ (1 / 10 ^ 8 * Real.log L ^ (3 / 4 : ℝ)) ^ (2 * q) := by
  have hΛ0 : 0 < Real.log L := by linarith
  have hLq : L ^ (q * (2 * q - 1)) ≤ Real.exp (1 / 2 + 1 / (2 * 10 ^ 8)) := by
    rw [Real.rpow_def_of_pos hL]
    refine Real.exp_le_exp.2 ?_
    have h1 : q * ((2 * q - 1) * Real.log L) ≤ q * 1 := mul_le_mul_of_nonneg_left hu (by linarith)
    linarith
  have hmin0 : 0 ≤ min (2 * q - 1)⁻¹ (Real.log L) :=
    le_min (inv_nonneg.2 (by linarith)) hΛ0.le
  have hm : min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ) ≤ Real.log L ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hmin0 (min_le_right _ _) (by norm_num)
  have hΛ34 : 0 ≤ Real.log L ^ (3 / 4 : ℝ) := Real.rpow_nonneg hΛ0.le _
  have hR : Real.exp ((1 + 1 / 10 ^ 8) * Real.log (1 / 10 ^ 8)) * Real.log L ^ (3 / 4 : ℝ)
      ≤ (1 / 10 ^ 8 * Real.log L ^ (3 / 4 : ℝ)) ^ (2 * q) := by
    rw [Real.mul_rpow (by norm_num) hΛ34, ← Real.rpow_mul hΛ0.le]
    refine mul_le_mul ?_ ?_ hΛ34 (Real.rpow_nonneg (by norm_num) _)
    · rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 10 ^ 8)]
      refine Real.exp_le_exp.2 ?_
      have hl : Real.log (1 / 10 ^ 8) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
      have h1 := mul_le_mul_of_nonpos_left (by linarith : 2 * q ≤ 1 + 1 / 10 ^ 8) hl
      linarith
    · exact Real.rpow_le_rpow_of_exponent_le hΛ (by linarith)
  have hnum := lyap_num
  calc 1 / 10 ^ 10 * (L ^ (q * (2 * q - 1)) * min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ))
      ≤ 1 / 10 ^ 10 * (Real.exp (1 / 2 + 1 / (2 * 10 ^ 8)) * Real.log L ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hLq hm (Real.rpow_nonneg hmin0 _) (Real.exp_pos _).le) (by norm_num)
    _ = 1 / 10 ^ 10 * Real.exp (1 / 2 + 1 / (2 * 10 ^ 8)) * Real.log L ^ (3 / 4 : ℝ) := by ring
    _ ≤ Real.exp ((1 + 1 / 10 ^ 8) * Real.log (1 / 10 ^ 8)) * Real.log L ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hnum hΛ34
    _ ≤ _ := hR

/-- **The sliver's count**: for `δ = 2q - 1 ∈ (0, 10⁻⁸)`, `1/(2δ) - 1 ≤ J ≤ 1/(2δ)` and
`T > Λ - 56/5`, `½e^{-q/2}e^{-10⁻⁴}δ^{-3/4}e^{qδΛ} ≤ (J + 1)e^{qδ(T - 2000 - J)}(2000 + J)^{-q/2}`:
`J + 1 ≥ 1/(2δ)`, `2000 + J ≤ 1/δ`, `qδJ ≤ q/2`, and in the exponent
`(q/2 - 1/4)log δ = (δ/4)log δ ≥ -5·10⁻⁸` against `10⁻⁴ - 2011.2qδ`. -/
lemma sliver_count_arith {q δ Λ T J : ℝ} (hqδ : 2 * q - 1 = δ) (hδ0 : 0 < δ)
    (hδ : δ < 1 / 10 ^ 8) (hJ0 : 0 ≤ J) (hJ1 : 1 / (2 * δ) ≤ J + 1) (hJ2 : J ≤ 1 / (2 * δ))
    (hT : Λ - 56 / 5 < T) :
    1 / 2 * Real.exp (-(q / 2)) * Real.exp (-(1 / 10 ^ 4)) * δ ^ (-(3 / 4 : ℝ))
        * Real.exp (q * δ * Λ)
      ≤ (J + 1) * Real.exp (q * δ * (T - 2000 - J)) * (2000 + J) ^ (-(q / 2)) := by
  have hq : q = (1 + δ) / 2 := by linarith
  have hq0 : 0 < q := by linarith
  have hq1 : q ≤ 1 := by linarith
  have hδne : δ ≠ 0 := hδ0.ne'
  have hJ1p : 0 < J + 1 := by linarith
  have hJ2p : 0 < 2000 + J := by linarith
  have h2δ : 0 < 2 * δ := by linarith
  -- `2000 + J ≤ 1/δ`
  have hbig : 2000 ≤ 1 / (2 * δ) := by
    rw [le_div_iff₀ h2δ]
    linarith
  have hJδ : 2000 + J ≤ 1 / δ := by
    have e : 1 / δ = 1 / (2 * δ) + 1 / (2 * δ) := by
      field_simp
      ring
    linarith
  -- the logarithms
  have hl1 : -Real.log 2 - Real.log δ ≤ Real.log (J + 1) := by
    have h := Real.log_le_log (by positivity) hJ1
    rw [one_div, Real.log_inv, Real.log_mul (by norm_num) hδne] at h
    linarith
  have hl2 : Real.log (2000 + J) ≤ -Real.log δ := by
    have h := Real.log_le_log hJ2p hJδ
    rwa [one_div, Real.log_inv] at h
  have hδJ : δ * J ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hJ2 hδ0.le
    have e : δ * (1 / (2 * δ)) = 1 / 2 := by
      field_simp
    linarith
  have hδlog : 1 / 10 ^ 8 * Real.log (1 / 10 ^ 8) ≤ δ * Real.log δ :=
    mul_log_ge_of_le_exp_neg_one hδ0 hδ.le
      (le_trans (by norm_num) Real.exp_neg_one_gt_d9.le)
  have hl8 : -19 ≤ Real.log (1 / 10 ^ 8) := by interval_decide (trust := kernel)
  -- the products
  have hqδ0 : 0 ≤ q * δ := by positivity
  have hqlog2 : q * Real.log (2000 + J) ≤ q * (-Real.log δ) := mul_le_mul_of_nonneg_left hl2 hq0.le
  have hTf : q * δ * (Λ - 56 / 5) ≤ q * δ * T := mul_le_mul_of_nonneg_left hT.le hqδ0
  have hqδJ : q * (δ * J) ≤ q * (1 / 2) := mul_le_mul_of_nonneg_left hδJ hq0.le
  have hqδs : q * δ ≤ 1 * (1 / 10 ^ 8) := mul_le_mul hq1 hδ.le hδ0.le zero_le_one
  have hqlogδ : q * Real.log δ = Real.log δ / 2 + δ * Real.log δ / 2 := by
    rw [hq]
    ring
  -- as exponentials
  have eL : 1 / 2 * Real.exp (-(q / 2)) * Real.exp (-(1 / 10 ^ 4)) * δ ^ (-(3 / 4 : ℝ))
        * Real.exp (q * δ * Λ)
      = Real.exp (-Real.log 2 + -(q / 2) + -(1 / 10 ^ 4) + Real.log δ * (-(3 / 4))
          + q * δ * Λ) := by
    rw [Real.rpow_def_of_pos hδ0, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
      Real.exp_neg (Real.log 2), Real.exp_log two_pos]
    ring
  have eR : (J + 1) * Real.exp (q * δ * (T - 2000 - J)) * (2000 + J) ^ (-(q / 2))
      = Real.exp (Real.log (J + 1) + q * δ * (T - 2000 - J)
          + Real.log (2000 + J) * (-(q / 2))) := by
    rw [Real.rpow_def_of_pos hJ2p, Real.exp_add, Real.exp_add, Real.exp_log hJ1p]
  rw [eL, eR]
  refine Real.exp_le_exp.2 ?_
  linarith

/-! ### Combining the analysis and the arithmetic -/

/-- From `M - DG ≤ E`, `mG ≤ M`, `Φ = m - D` and `c ≤ Φ`: `cG ≤ E` for `G ≥ 0`. -/
lemma le_of_sub_mul_le {E M D G m c Φ : ℝ} (hE : M - D * G ≤ E) (hM : m * G ≤ M)
    (hΦ : Φ = m - D) (hc : c ≤ Φ) (hG : 0 ≤ G) : c * G ≤ E := by
  have h := mul_le_mul_of_nonneg_right hc hG
  rw [hΦ] at h
  linarith

/-- **Below `½`, the three terms combined**: the reduction
`cRed·L^{-q}I - cJ·e·L^{-q}I_J - cErr·L^{-q} ≤ E`, the main term `A·S ≤ L^{-q}I`, the
subtracted term `I_J ≤ 216L^q·m·g` and the error `cErr·L^{-q} ≤ errB·m·g` give
`cRed·A·S - (216cJ·e + errB)·m·g ≤ E`. -/
lemma belowHalf_combine {E Im Is S cR cJ' cE A Lm Lp e m g eB : ℝ}
    (hred : cR * (Lm * Im) - cJ' * e * Lm * Is - cE * Lm ≤ E)
    (hm5 : A * S ≤ Lm * Im) (hcR : 0 ≤ cR)
    (hR3 : Is ≤ 216 * Lp * m * g) (hLL : Lm * Lp = 1) (hcJ : 0 ≤ cJ' * e * Lm)
    (hE : cE * Lm ≤ eB * (m * g)) :
    cR * (A * S) - (216 * cJ' * e + eB) * (m * g) ≤ E := by
  have h1 := mul_le_mul_of_nonneg_left hm5 hcR
  have h2 := mul_le_mul_of_nonneg_left hR3 hcJ
  have h3 : cJ' * e * Lm * (216 * Lp * m * g) = 216 * cJ' * e * (m * g) := by
    calc cJ' * e * Lm * (216 * Lp * m * g) = 216 * cJ' * e * (m * g) * (Lm * Lp) := by ring
      _ = 216 * cJ' * e * (m * g) := by rw [hLL, mul_one]
  linarith

/-- **Above `½`, the main term combined**: from the reduction `cRed·L^{-q}I - R₁ - R₂ ≤ E` and
`A·S' ≤ L^{-q}I`, `cRed·A·S - R₁ - R₂ ≤ E` for every `S ≤ S'`. -/
lemma aboveHalf_combine {E Im S S' cR A Lm R₁ R₂ : ℝ}
    (hred : cR * (Lm * Im) - R₁ - R₂ ≤ E) (hm5 : A * S' ≤ Lm * Im) (hS : S ≤ S')
    (hA : 0 ≤ A) (hcR : 0 ≤ cR) : cR * (A * S) - R₁ - R₂ ≤ E := by
  have h1 := mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left hS hA) hm5) hcR
  linarith

/-- **The error term below `½`**: `cErr(q)L^{-q} ≤ errB(q)·min{Λ, (1-2q)⁻¹}Λ^{-q/2}` for
`Λ = log L ≥ 6000` and `qΛ ≥ 37/2` (`RMF.exp_neg_mul_rpow_le_of_six_thousand`). -/
lemma cErr_mul_rpow_le_errB {q L : ℝ} (hq0 : 0 < q) (hq : q < 1 / 2) (hL : 0 < L)
    (hΛ : 6000 ≤ Real.log L) (hqΛ : 37 / 2 ≤ q * Real.log L) :
    cErr q * L ^ (-q)
      ≤ errB q * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))) := by
  have hΛ0 : 0 < Real.log L := by linarith
  have hkey := exp_neg_mul_rpow_le_of_six_thousand hΛ hq0.le
  have hLq : L ^ (-q) = Real.exp (-(q * Real.log L)) := by
    rw [Real.rpow_def_of_pos hL]
    ring_nf
  have hsplit : Real.log L ^ (q / 2) * Real.log L ^ (-(q / 2)) = 1 := by
    rw [← Real.rpow_add hΛ0, add_neg_cancel, Real.rpow_zero]
  have hg0 : 0 ≤ Real.log L ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  have h1 : Real.exp (-(q * Real.log L))
      ≤ Real.exp (-(1376 / 1377 * (q * Real.log L))) * Real.log L ^ (-(q / 2)) := by
    calc Real.exp (-(q * Real.log L))
        = Real.exp (-(q * Real.log L)) * Real.log L ^ (q / 2) * Real.log L ^ (-(q / 2)) := by
          rw [mul_assoc, hsplit, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hkey hg0
  have hq6 : q * 6000 ≤ q * Real.log L := mul_le_mul_of_nonneg_left hΛ hq0.le
  have hmax : max (37 / 2) (6000 * q) ≤ q * Real.log L := max_le hqΛ (by linarith)
  have h2 : Real.exp (-(1376 / 1377 * (q * Real.log L)))
      ≤ Real.exp (-(1376 / 1377 * max (37 / 2) (6000 * q))) :=
    Real.exp_le_exp.2 (by linarith)
  have hm1 : 1 ≤ min (Real.log L) (1 - 2 * q)⁻¹ :=
    le_min (by linarith) ((one_le_inv₀ (by linarith)).2 (by linarith))
  have hc := (cErr_pos q).le
  unfold errB
  calc cErr q * L ^ (-q) = cErr q * Real.exp (-(q * Real.log L)) := by rw [hLq]
    _ ≤ cErr q * (Real.exp (-(1376 / 1377 * max (37 / 2) (6000 * q)))
          * Real.log L ^ (-(q / 2))) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right h2 hg0)) hc
    _ ≤ cErr q * (Real.exp (-(1376 / 1377 * max (37 / 2) (6000 * q)))
          * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) hc
        exact le_mul_of_one_le_left hg0 hm1
    _ = _ := by ring

/-- **B1's main term**: with the one scale `k = 21`, `2021 ≤ T ≤ Λ` and
`(1-2q)min{Λ, (1-2q)⁻¹} ≤ 1`,
`mainB1(q)·min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ cRed(q)·2^{2q-1}(G/(64/q))^q·∑_{k=21}Γ·N·(T-k)^{-q/2}`. -/
lemma mainB1_mul_le_sum {q Λ : ℝ} {T : ℕ} (hq0 : 0 < q) (hq : q < 1 / 2) (hT : 2021 ≤ T)
    (hTΛ : (T : ℝ) ≤ Λ) :
    mainB1 q * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)))
      ≤ cRed q * (2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
        * ∑ k ∈ ({21} : Finset ℕ), perScaleConst q (k - 20)
          * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
          * ((T - k : ℕ) : ℝ) ^ (-(q / 2))) := by
  rw [Finset.sum_singleton]
  simp only [Nat.cast_ofNat, Nat.reduceSub]
  have hTr : (2021 : ℝ) ≤ T := by exact_mod_cast hT
  have hΛ0 : 0 < Λ := by linarith
  have h21 : ((T - 21 : ℕ) : ℝ) = (T : ℝ) - 21 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have ht : Λ ^ (-(q / 2)) ≤ ((T - 21 : ℕ) : ℝ) ^ (-(q / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by rw [h21]; linarith) (by rw [h21]; linarith) (by linarith)
  have hm : (1 - 2 * q) * min Λ (1 - 2 * q)⁻¹ ≤ 1 := by
    calc (1 - 2 * q) * min Λ (1 - 2 * q)⁻¹ ≤ (1 - 2 * q) * (1 - 2 * q)⁻¹ :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
      _ = 1 := mul_inv_cancel₀ (by linarith)
  have hP0 : 0 ≤ cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
      * perScaleConst q 1
      * Real.exp (-(q * (1 - 2 * q)) * (21 + 0.7866 + 9.003 / Real.exp 21)) := by
    have := cRed_pos q
    have := perScaleConst_nonneg (q := q) hq0.le (by linarith) 1
    positivity
  have hg0 : 0 ≤ Λ ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  calc mainB1 q * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)))
      = (cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
          * perScaleConst q 1
          * Real.exp (-(q * (1 - 2 * q)) * (21 + 0.7866 + 9.003 / Real.exp 21)))
        * ((1 - 2 * q) * min Λ (1 - 2 * q)⁻¹) * Λ ^ (-(q / 2)) := by
        unfold mainB1
        ring
    _ ≤ (cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
          * perScaleConst q 1
          * Real.exp (-(q * (1 - 2 * q)) * (21 + 0.7866 + 9.003 / Real.exp 21))) * 1
        * ((T - 21 : ℕ) : ℝ) ^ (-(q / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hm hP0) ht hg0 (by rw [mul_one]; exact hP0)
    _ = _ := by ring

/-- The exponent of `N_q(k)` on B2's scales: `-20.7867β - q ≤ -β(k + 0.7866 + e)` for `β ≥ 0`,
`k ≤ 20 + n`, `βn ≤ q` and `e ≤ 10⁻⁴`. -/
lemma exp_arg_B2 {β q k n e : ℝ} (hβ : 0 ≤ β) (hk : k ≤ 20 + n) (hn : β * n ≤ q)
    (he : e ≤ 1 / 10 ^ 4) : -β * 20.7867 - q ≤ -β * (k + 0.7866 + e) := by
  have h1 := mul_le_mul_of_nonneg_left hk hβ
  have h2 := mul_le_mul_of_nonneg_left he hβ
  linarith

/-- **B2's main term**: on the scales `21 ≤ k ≤ 20 + n`, `n = min(K_max(q), T - 2020)`, for
`9/20 ≤ q < ½`: drop `k = 21`; on `k ≥ 22`, `Γ ≥ perScaleLow2`, `N ≥ e^{-20.7867β - q}`
(`βn ≤ q`) and `(T - k)^{-q/2} ≥ Λ^{-q/2}`; and `n - 1 ≥ (3/5)min{Λ, (1-2q)⁻¹}`. -/
lemma mainB2_mul_le_sum {q Λ : ℝ} {T : ℕ} (hq0 : 9 / 20 ≤ q) (hq : q < 1 / 2) (hΛ : 6000 ≤ Λ)
    (hT : 2021 ≤ T) (hTΛ : (T : ℝ) ≤ Λ) (hTl : Real.log q + Λ - 21 / 2 < T) :
    mainB2 q * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)))
      ≤ cRed q * (2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
        * ∑ k ∈ Finset.Icc 21 (20 + min (c3Kmax q) (T - 2020)), perScaleConst q (k - 20)
          * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
          * ((T - k : ℕ) : ℝ) ^ (-(q / 2))) := by
  have hqpos : 0 < q := by linarith
  have hb : 0 < 1 - 2 * q := by linarith
  have hbne : 1 - 2 * q ≠ 0 := hb.ne'
  have hΛ0 : 0 < Λ := by linarith
  have hTr : (2021 : ℝ) ≤ T := by exact_mod_cast hT
  have hβ0 : 0 ≤ q * (1 - 2 * q) := mul_nonneg hqpos.le hb.le
  have hg0 : 0 ≤ Λ ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  have hnK : min (c3Kmax q) (T - 2020) ≤ c3Kmax q := min_le_left _ _
  have hnT : min (c3Kmax q) (T - 2020) ≤ T - 2020 := min_le_right _ _
  generalize hn : min (c3Kmax q) (T - 2020) = n at hnK hnT ⊢
  -- `n - 1 ≥ (3/5)min{Λ, (1-2q)⁻¹}`
  have hlog : -81 / 100 ≤ Real.log q :=
    le_trans (by interval_decide (trust := kernel) : (-81 / 100 : ℝ) ≤ Real.log (9 / 20))
      (Real.log_le_log (by norm_num) hq0)
  have hw10 : 10 ≤ 1 / (1 - 2 * q) := by
    rw [le_div_iff₀ hb]
    linarith
  have hmin : min Λ (1 - 2 * q)⁻¹ ≤ 1 / (1 - 2 * q) := by
    rw [one_div]
    exact min_le_right _ _
  have hminΛ : min Λ (1 - 2 * q)⁻¹ ≤ Λ := min_le_left _ _
  have hnA : 3 / 5 * min Λ (1 - 2 * q)⁻¹ + 1 ≤ (c3Kmax q : ℝ) := by
    have h1 : ⌊1 / (1 - 2 * q)⌋₊ ≤ c3Kmax q := le_max_right _ _
    have h2 : 1 / (1 - 2 * q) < (⌊1 / (1 - 2 * q)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : (⌊1 / (1 - 2 * q)⌋₊ : ℝ) ≤ c3Kmax q := by exact_mod_cast h1
    linarith
  have hnB : 3 / 5 * min Λ (1 - 2 * q)⁻¹ + 1 ≤ ((T - 2020 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    linarith
  have hn1 : 3 / 5 * min Λ (1 - 2 * q)⁻¹ + 1 ≤ (n : ℝ) := by
    rw [← hn, Nat.cast_min]
    exact le_min hnA hnB
  have hn1' : 1 ≤ n := by
    have hm0 : 0 ≤ min Λ (1 - 2 * q)⁻¹ := le_min hΛ0.le (inv_nonneg.2 hb.le)
    have : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  -- `βn ≤ q`
  have hβn : q * (1 - 2 * q) * (n : ℝ) ≤ q := by
    have h1 : (n : ℝ) ≤ 1 / (1 - 2 * q) :=
      le_trans (by exact_mod_cast hnK) (c3Kmax_le hqpos.le hq)
    calc q * (1 - 2 * q) * (n : ℝ) ≤ q * (1 - 2 * q) * (1 / (1 - 2 * q)) :=
          mul_le_mul_of_nonneg_left h1 hβ0
      _ = q := by rw [mul_assoc, mul_one_div_cancel hbne, mul_one]
  -- one scale
  have hc0 : 0 ≤ perScaleLow2 q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) * Λ ^ (-(q / 2)) :=
    mul_nonneg (mul_nonneg (perScaleLow2_nonneg q) (Real.exp_pos _).le) hg0
  have he21 : (90030 : ℝ) ≤ Real.exp 21 := by interval_decide (trust := kernel)
  have hterm : ∀ k ∈ Finset.Icc 22 (20 + n),
      perScaleLow2 q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) * Λ ^ (-(q / 2))
        ≤ perScaleConst q (k - 20)
          * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
          * ((T - k : ℕ) : ℝ) ^ (-(q / 2)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hΓ := perScaleLow2_le_perScaleConst hq0 hq (K := k - 20) (by omega)
    have hk20 : (k : ℝ) ≤ 20 + n := by exact_mod_cast hk.2
    have hk21 : (21 : ℝ) ≤ k := by exact_mod_cast (by omega : 21 ≤ k)
    have hek : Real.exp 21 ≤ Real.exp (k : ℝ) := Real.exp_le_exp.2 hk21
    have hs : 9.003 / Real.exp (k : ℝ) ≤ 1 / 10 ^ 4 := by
      rw [div_le_iff₀ (Real.exp_pos _)]
      linarith
    have hN : Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q)
        ≤ Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ))) :=
      Real.exp_le_exp.2 (exp_arg_B2 hβ0 hk20 hβn hs)
    have hTk : (0 : ℝ) < ((T - k : ℕ) : ℝ) := by
      have : 0 < T - k := by omega
      exact_mod_cast this
    have hTkΛ : ((T - k : ℕ) : ℝ) ≤ Λ := le_trans (by exact_mod_cast Nat.sub_le T k) hTΛ
    have ht := Real.rpow_le_rpow_of_nonpos hTk hTkΛ (by linarith : -(q / 2) ≤ 0)
    have hΓ0 := perScaleConst_nonneg (q := q) hqpos.le (by linarith) (k - 20)
    exact mul_le_mul (mul_le_mul hΓ hN (Real.exp_pos _).le hΓ0) ht hg0
      (mul_nonneg hΓ0 (Real.exp_pos _).le)
  have hf0 : ∀ k ∈ Finset.Icc 21 (20 + n), 0 ≤ perScaleConst q (k - 20)
      * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
      * ((T - k : ℕ) : ℝ) ^ (-(q / 2)) := fun k _ =>
    mul_nonneg (mul_nonneg (perScaleConst_nonneg hqpos.le (by linarith) _) (Real.exp_pos _).le)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hcard : ((Finset.Icc 22 (20 + n)).card : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.card_Icc, show 20 + n + 1 - 22 = n - 1 by omega, Nat.cast_sub hn1']
    simp
  have hsum : ((n : ℝ) - 1)
        * (perScaleLow2 q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) * Λ ^ (-(q / 2)))
      ≤ ∑ k ∈ Finset.Icc 21 (20 + n), perScaleConst q (k - 20)
          * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
          * ((T - k : ℕ) : ℝ) ^ (-(q / 2)) := by
    rw [← hcard, ← nsmul_eq_mul]
    refine le_trans (Finset.card_nsmul_le_sum _ _ _ hterm) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by norm_num) le_rfl)
      fun k hk _ => hf0 k hk
  have hP0 : 0 ≤ cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q := by
    have := cRed_pos q
    positivity
  calc mainB2 q * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)))
      = (cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q)
        * (3 / 5 * min Λ (1 - 2 * q)⁻¹
          * (perScaleLow2 q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) * Λ ^ (-(q / 2)))) := by
        unfold mainB2
        ring
    _ ≤ (cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q)
        * (((n : ℝ) - 1)
          * (perScaleLow2 q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) * Λ ^ (-(q / 2)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hc0) hP0
    _ ≤ (cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q)
        * ∑ k ∈ Finset.Icc 21 (20 + n), perScaleConst q (k - 20)
          * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
          * ((T - k : ℕ) : ℝ) ^ (-(q / 2)) := mul_le_mul_of_nonneg_left hsum hP0
    _ = _ := by ring

/-- **H's scales**: for `Λ ≥ 6000`, `Λ - 56/5 < T` and `T + 10 ≤ Λ`, on `21 ≤ k ≤ T - 2000`
every term is `Γ(½, 1)·1·(T - k)^{-1/4} ≥ Γ(½, 1)Λ^{-1/4}`, and there are `T - 2020 ≥ (3/5)Λ`. -/
lemma half_sum_ge {Λ : ℝ} {T : ℕ} (hΛ : 6000 ≤ Λ) (hT1 : Λ - 56 / 5 < T)
    (hT2 : (T : ℝ) + 10 ≤ Λ) :
    3 / 5 * Λ * (perScaleConst (1 / 2) 1 * Λ ^ (-(1 / 2 / 2 : ℝ)))
      ≤ ∑ k ∈ Finset.Icc 21 (T - 2000), perScaleConst (1 / 2) (k - 20)
          * Real.exp (1 / 2 * (2 * (1 / 2) - 1) * k) * ((T - k : ℕ) : ℝ) ^ (-(1 / 2 / 2 : ℝ)) := by
  have hΛ0 : 0 < Λ := by linarith
  have hT2020 : 2020 ≤ T := by
    have : (2020 : ℝ) ≤ T := by linarith
    exact_mod_cast this
  have hΓ0 := perScaleConst_nonneg (q := 1 / 2) (by norm_num) (by norm_num) 1
  have hg0 : 0 ≤ Λ ^ (-(1 / 2 / 2 : ℝ)) := Real.rpow_nonneg hΛ0.le _
  have hterm : ∀ k ∈ Finset.Icc 21 (T - 2000),
      perScaleConst (1 / 2) 1 * Λ ^ (-(1 / 2 / 2 : ℝ))
        ≤ perScaleConst (1 / 2) (k - 20) * Real.exp (1 / 2 * (2 * (1 / 2) - 1) * k)
          * ((T - k : ℕ) : ℝ) ^ (-(1 / 2 / 2 : ℝ)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [perScaleConst_eq_of_half_le le_rfl (by norm_num) (k - 20) 1,
      show (1 / 2 : ℝ) * (2 * (1 / 2) - 1) = 0 by norm_num, zero_mul, Real.exp_zero, mul_one]
    have hTk : (0 : ℝ) < ((T - k : ℕ) : ℝ) := by
      have : 0 < T - k := by omega
      exact_mod_cast this
    have hTkΛ : ((T - k : ℕ) : ℝ) ≤ Λ := by
      have : ((T - k : ℕ) : ℝ) ≤ T := by exact_mod_cast Nat.sub_le T k
      linarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hTk hTkΛ (by norm_num)) hΓ0
  have hcard : ((Finset.Icc 21 (T - 2000)).card : ℝ) = (T : ℝ) - 2020 := by
    rw [Nat.card_Icc, show T - 2000 + 1 - 21 = T - 2020 by omega, Nat.cast_sub hT2020]
    norm_num
  have hcount : 3 / 5 * Λ ≤ (T : ℝ) - 2020 := by linarith
  calc 3 / 5 * Λ * (perScaleConst (1 / 2) 1 * Λ ^ (-(1 / 2 / 2 : ℝ)))
      ≤ ((T : ℝ) - 2020) * (perScaleConst (1 / 2) 1 * Λ ^ (-(1 / 2 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hcount (mul_nonneg hΓ0 hg0)
    _ = (Finset.Icc 21 (T - 2000)).card • (perScaleConst (1 / 2) 1 * Λ ^ (-(1 / 2 / 2 : ℝ))) := by
        rw [nsmul_eq_mul, hcard]
    _ ≤ _ := Finset.card_nsmul_le_sum _ _ _ hterm

/-- **H's arithmetic**: from the reduction and main term at `q = ½`, `V = 64` (`A·S` with
`A = (G/128)^{1/2}`), the scales `S ≥ (3/5)Λ·Γ(½, 1)Λ^{-1/4}`, the subtracted term at `½`
`I_J ≤ 17.3L^{1/2}Λ^{3/4}` and `L^{-1/2} ≤ e^{-3000}`: `E ≥ cHalfLB·Λ^{3/4} ≥ 10⁻⁷Λ^{3/4}`. -/
lemma half_regime_arith {E S Is L : ℝ} (hL : 0 < L) (hΛ : 6000 ≤ Real.log L)
    (h : cRed (1 / 2) * (2 ^ (2 * (1 / 2 : ℝ) - 1)
          * (Real.exp (-0.592) / 2 / (2 * 64)) ^ (1 / 2 : ℝ) * S)
        - cJ (1 / 2) * Real.exp (-(64 * (1 / 2))) * L ^ (-(1 / 2 : ℝ)) * Is
        - cErr (1 / 2) * L ^ (-(1 / 2 : ℝ)) ≤ E)
    (hS : 3 / 5 * Real.log L * (perScaleConst (1 / 2) 1 * Real.log L ^ (-(1 / 2 / 2 : ℝ))) ≤ S)
    (hR : Is ≤ 173 / 10 * L ^ (1 / 2 : ℝ) * Real.log L ^ (3 / 4 : ℝ)) :
    1 / 10 ^ 7 * Real.log L ^ (3 / 4 : ℝ) ≤ E := by
  have hΛ0 : 0 < Real.log L := by linarith
  rw [show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num, Real.rpow_zero, one_mul,
    show (2 : ℝ) * 64 = 128 by norm_num, show -((64 : ℝ) * (1 / 2)) = -32 by norm_num] at h
  have hA0 : 0 ≤ (Real.exp (-0.592) / 2 / 128) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hLL : L ^ (-(1 / 2 : ℝ)) * L ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hL, neg_add_cancel, Real.rpow_zero]
  have hLe : L ^ (-(1 / 2 : ℝ)) ≤ Real.exp (-3000) := by
    rw [Real.rpow_def_of_pos hL]
    exact Real.exp_le_exp.2 (by linarith)
  have hΛ1 : 1 ≤ Real.log L ^ (3 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hΛΛ : Real.log L * Real.log L ^ (-(1 / 2 / 2 : ℝ)) = Real.log L ^ (3 / 4 : ℝ) := by
    rw [show (3 / 4 : ℝ) = 1 + -(1 / 2 / 2) by norm_num, Real.rpow_add hΛ0, Real.rpow_one]
  have hΓ0 := perScaleConst_nonneg (q := 1 / 2) (by norm_num) (by norm_num) 1
  have hcR := (cRed_pos (1 / 2)).le
  have hcJ := (cJ_pos (1 / 2)).le
  have hcE := (cErr_pos (1 / 2)).le
  have hLm0 : 0 ≤ L ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hL.le _
  have s1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS hA0) hcR
  have s2 : cRed (1 / 2) * ((Real.exp (-0.592) / 2 / 128) ^ (1 / 2 : ℝ)
        * (3 / 5 * Real.log L * (perScaleConst (1 / 2) 1 * Real.log L ^ (-(1 / 2 / 2 : ℝ)))))
      = cRed (1 / 2) * (Real.exp (-0.592) / 2 / 128) ^ (1 / 2 : ℝ) * perScaleConst (1 / 2) 1
        * (3 / 5) * Real.log L ^ (3 / 4 : ℝ) := by
    rw [← hΛΛ]
    ring
  have s3 := mul_le_mul_of_nonneg_left hR
    (mul_nonneg (mul_nonneg hcJ (Real.exp_pos (-32)).le) hLm0)
  have s4 : cJ (1 / 2) * Real.exp (-32) * L ^ (-(1 / 2 : ℝ))
        * (173 / 10 * L ^ (1 / 2 : ℝ) * Real.log L ^ (3 / 4 : ℝ))
      = 173 / 10 * cJ (1 / 2) * Real.exp (-32) * Real.log L ^ (3 / 4 : ℝ) := by
    calc cJ (1 / 2) * Real.exp (-32) * L ^ (-(1 / 2 : ℝ))
          * (173 / 10 * L ^ (1 / 2 : ℝ) * Real.log L ^ (3 / 4 : ℝ))
        = 173 / 10 * cJ (1 / 2) * Real.exp (-32) * Real.log L ^ (3 / 4 : ℝ)
          * (L ^ (-(1 / 2 : ℝ)) * L ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [hLL, mul_one]
  have s5 : cErr (1 / 2) * L ^ (-(1 / 2 : ℝ))
      ≤ cErr (1 / 2) * Real.exp (-3000) * Real.log L ^ (3 / 4 : ℝ) := by
    calc cErr (1 / 2) * L ^ (-(1 / 2 : ℝ)) ≤ cErr (1 / 2) * Real.exp (-3000) * 1 := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left hLe hcE
      _ ≤ _ := mul_le_mul_of_nonneg_left hΛ1 (mul_nonneg hcE (Real.exp_pos _).le)
  have s6 : cHalfLB * Real.log L ^ (3 / 4 : ℝ)
      = cRed (1 / 2) * (Real.exp (-0.592) / 2 / 128) ^ (1 / 2 : ℝ) * perScaleConst (1 / 2) 1
          * (3 / 5) * Real.log L ^ (3 / 4 : ℝ)
        - 173 / 10 * cJ (1 / 2) * Real.exp (-32) * Real.log L ^ (3 / 4 : ℝ)
        - cErr (1 / 2) * Real.exp (-3000) * Real.log L ^ (3 / 4 : ℝ) := by
    unfold cHalfLB
    ring
  have s7 := mul_le_mul_of_nonneg_right cHalfLB_ge (by linarith : 0 ≤ Real.log L ^ (3 / 4 : ℝ))
  linarith

/-- **S's scales**: for `½ < q < 201/400` and `T ≥ 2021 + J`, on `T - 2000 - J ≤ k ≤ T - 2000` every
term is at least `Γ(q, 2)e^{qδ(T - 2000 - J)}(2000 + J)^{-q/2}`, and there are `J + 1`. -/
lemma sliver_sum_ge {q : ℝ} {T J : ℕ} (hq0 : 1 / 2 < q) (hq1 : q < 201 / 400)
    (hTJ : 2021 + J ≤ T) :
    perScaleConst q 2 * (((J : ℝ) + 1) * Real.exp (q * (2 * q - 1) * ((T : ℝ) - 2000 - J))
        * (2000 + (J : ℝ)) ^ (-(q / 2)))
      ≤ ∑ k ∈ Finset.Icc (T - 2000 - J) (T - 2000), perScaleConst q (k - 20)
          * Real.exp (q * (2 * q - 1) * k) * ((T - k : ℕ) : ℝ) ^ (-(q / 2)) := by
  have hβ0 : 0 ≤ q * (2 * q - 1) := mul_nonneg (by linarith) (by linarith)
  have hΓ0 := perScaleConst_nonneg (q := q) (by linarith) (by linarith) 2
  have hterm : ∀ k ∈ Finset.Icc (T - 2000 - J) (T - 2000),
      perScaleConst q 2 * Real.exp (q * (2 * q - 1) * ((T : ℝ) - 2000 - J))
          * (2000 + (J : ℝ)) ^ (-(q / 2))
        ≤ perScaleConst q (k - 20) * Real.exp (q * (2 * q - 1) * k)
          * ((T - k : ℕ) : ℝ) ^ (-(q / 2)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [perScaleConst_eq_of_half_le hq0.le hq1 (k - 20) 2]
    have hk1 : (T : ℝ) - 2000 - J ≤ k := by
      have h1 : T ≤ k + 2000 + J := by omega
      have h2 : (T : ℝ) ≤ k + 2000 + J := by exact_mod_cast h1
      linarith
    have hTk1 : ((T - k : ℕ) : ℝ) ≤ 2000 + J := by
      have h1 : T - k ≤ 2000 + J := by omega
      exact_mod_cast h1
    have hTk0 : (0 : ℝ) < ((T - k : ℕ) : ℝ) := by
      have h1 : 0 < T - k := by omega
      exact_mod_cast h1
    have hN := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hk1 hβ0)
    have ht := Real.rpow_le_rpow_of_nonpos hTk0 hTk1 (by linarith : -(q / 2) ≤ 0)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hN hΓ0) ht (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg hΓ0 (Real.exp_pos _).le)
  have hcard : ((Finset.Icc (T - 2000 - J) (T - 2000)).card : ℝ) = (J : ℝ) + 1 := by
    rw [Nat.card_Icc, show T - 2000 + 1 - (T - 2000 - J) = J + 1 by omega, Nat.cast_add,
      Nat.cast_one]
  calc perScaleConst q 2 * (((J : ℝ) + 1) * Real.exp (q * (2 * q - 1) * ((T : ℝ) - 2000 - J))
        * (2000 + (J : ℝ)) ^ (-(q / 2)))
      = (Finset.Icc (T - 2000 - J) (T - 2000)).card
          • (perScaleConst q 2 * Real.exp (q * (2 * q - 1) * ((T : ℝ) - 2000 - J))
            * (2000 + (J : ℝ)) ^ (-(q / 2))) := by
        rw [nsmul_eq_mul, hcard]
        ring
    _ ≤ _ := Finset.card_nsmul_le_sum _ _ _ hterm

/-- **S's arithmetic**: from the reduction and main term at `V = 64`, the scales
`S ≥ Γ(q, 2)·½e^{-q/2}e^{-10⁻⁴}δ^{-3/4}e^{qδΛ}`, the subtracted term `I_J ≤ 33L^qL^{qδ}δ^{-3/4}`
and `L^{-q} ≤ e^{-3000}`: `E ≥ PhiSl(q)·L^{qδ}δ^{-3/4}`, and `min{1/δ, Λ} = 1/δ` for `δΛ ≥ 1`. -/
lemma sliver_regime_arith {E S Is L q : ℝ} (hL : 0 < L) (hΛ : 6000 ≤ Real.log L)
    (hq0 : 1 / 2 < q) (hq1 : q ≤ 1 / 2 + 1 / (2 * 10 ^ 8)) (hu : 1 ≤ (2 * q - 1) * Real.log L)
    (h : cRed q * (2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * 64)) ^ q * S)
        - cJ q * Real.exp (-(64 * q)) * L ^ (-q) * Is - cErr q * L ^ (-q) ≤ E)
    (hS : perScaleConst q 2 * (1 / 2 * Real.exp (-(q / 2)) * Real.exp (-(1 / 10 ^ 4))
        * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.exp (q * (2 * q - 1) * Real.log L)) ≤ S)
    (hR : Is ≤ 33 * L ^ q * L ^ (q * (2 * q - 1)) * (2 * q - 1) ^ (-(3 / 4 : ℝ))) :
    1 / 10 ^ 10 * (L ^ (q * (2 * q - 1)) * min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ))
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
  have s7 := mul_le_mul_of_nonneg_right (PhiSl_ge hq0 hq1) (mul_nonneg hP0 hD0)
  linarith

/-! ### The reduction with the main term, at the damping level -/

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **Below `½`: the reduction at the tilt `V = 32/q`, the main term and the subtracted term.**
For a Rademacher family, `x ≥ exp(e^{6000})`, `0 < q < ½` and `qΛ ≥ 37/2` (`Λ = log log x`), the
damping level `T` at `σ = 2V/log x` has `2021 ≤ T ≤ Λ` and `T > log q + Λ - 21/2`, and for every
set `K` of scales in `(20, T - 2000]` with `k - 20 ≤ K_max(q)`, with `G = e^{-0.592}/2`,
`Γ = RMF.perScaleConst`,

`cRed(q)·2^{2q-1}(G/(64/q))^q∑_{k∈K}Γ(q, k-20)e^{-q(1-2q)(k+0.7866+9.003e^{-k})}(T-k)^{-q/2}`
`  - (216cJ(q)e^{-32} + errB(q))·min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`. -/
theorem exists_level_belowHalf (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 0 < q) (hq : q < 1 / 2)
    (hqΛ : 37 / 2 ≤ q * Real.log (Real.log x)) :
    ∃ T : ℕ, 2021 ≤ T ∧ (T : ℝ) ≤ Real.log (Real.log x)
      ∧ Real.log q + Real.log (Real.log x) - 21 / 2 < T
      ∧ ∀ K : Finset ℕ, (∀ k ∈ K, 20 < k ∧ k + 2000 ≤ T) → (∀ k ∈ K, k - 20 ≤ c3Kmax q) →
        cRed q * (2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
            * ∑ k ∈ K, perScaleConst q (k - 20)
              * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
              * ((T - k : ℕ) : ℝ) ^ (-(q / 2)))
          - (216 * cJ q * Real.exp (-32) + errB q)
            * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹ * Real.log (Real.log x) ^ (-(q / 2)))
        ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, hwt, -⟩ := loglog_facts_of_six_thousand hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.2 (Real.exp_pos _)) hx
  -- `log q + Λ ≥ 2040`, so `q log x ≥ e^{2040}`
  have hlq := log_add_ge_of_mul_ge hΛ hqΛ
  have hqL : Real.exp 2040 ≤ q * Real.log x := by
    rw [← Real.exp_log (mul_pos hq0 hL0), Real.log_mul hq0.ne' hL0.ne']
    exact Real.exp_le_exp.2 hlq
  have he : (12800 : ℝ) ≤ Real.exp 2040 := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2040)
    linarith
  -- the tilt `σ = 2V/log x`, `V = 32/q`
  have hσ : 0 < 2 * (32 / q) / Real.log x := by positivity
  have hσ1 : 2 * (32 / q) / Real.log x ≤ 1 / 200 := by
    rw [show 2 * (32 / q) / Real.log x = 64 / (q * Real.log x) by field_simp; ring,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := exists_damping_level hσ hσ1
  have hℓ : Real.log (1 / (200 * (2 * (32 / q) / Real.log x)))
      = Real.log q + Real.log (Real.log x) - Real.log 12800 := by
    rw [show 1 / (200 * (2 * (32 / q) / Real.log x)) = q * Real.log x / 12800 by
        field_simp; ring,
      Real.log_div (by positivity) (by norm_num), Real.log_mul hq0.ne' hL0.ne']
  rw [hℓ] at hT3 hT4
  have hl1 : Real.log 12800 ≤ 19 / 2 := by interval_decide (trust := kernel)
  have hl2 : 9 ≤ Real.log 12800 := by interval_decide (trust := kernel)
  have hlq0 : Real.log q < 0 := Real.log_neg hq0 (by linarith)
  have hT2021 : 2021 ≤ T := by
    have : (2021 : ℝ) ≤ T := by linarith
    exact_mod_cast this
  refine ⟨T, hT2021, by linarith, by linarith, fun K hK hKq => ?_⟩
  -- the reduction at `V = 32/q`
  have hlogV : 3 * (32 / q) + 3 ≤ Real.log x := by
    have h96 : 96 / q ≤ Real.log x / 2 := by
      rw [div_le_div_iff₀ hq0 two_pos]
      linarith
    have e : 3 * (32 / q) = 96 / q := by ring
    have := Real.add_one_le_exp (6000 : ℝ)
    linarith
  have hred := le_integral_rpow_weightedRademacherSum_euler_full_explicit hX (V := 32 / q)
    (by positivity) hwt hlogV hq0 (by linarith)
  rw [div_mul_cancel₀ (32 : ℝ) hq0.ne'] at hred
  -- the main term at `σ = 2V/log x`
  have hyT := scaleCut_add_seven_le hx1 (T := T) (by linarith)
  have hm5 := le_rpow_mul_integral_rpow_integral_lineDiv_explicit hX hσ hq0 hq.le (k₀ := 20)
    (y := ⌊x⌋₊ + 1) le_rfl hT1 hT2 hyT hK (fun k hk _ => hKq k hk) hL0
    (div_mul_cancel₀ _ hL0.ne')
  -- the subtracted term and the error term
  have hR3 := integral_rpow_lineDiv_le_subtracted_belowHalf hX hx1 hΛ (V := 32 / q)
    (by rw [le_div_iff₀ hq0]; linarith) hq0 hq
  have hE := cErr_mul_rpow_le_errB hq0 hq hL0 hΛ hqΛ
  have hLL : Real.log x ^ (-q) * Real.log x ^ q = 1 := by
    rw [← Real.rpow_add hL0, neg_add_cancel, Real.rpow_zero]
  exact belowHalf_combine hred hm5 (cRed_pos q).le hR3 hLL
    (mul_nonneg (mul_nonneg (cJ_pos q).le (Real.exp_pos _).le) (Real.rpow_nonneg hL0.le _)) hE

/-- **From `½`: the reduction at `V = 64` and the main term with `N_q(k) ≥ e^{q(2q-1)k}`.**  For a
Rademacher family, `x ≥ exp(e^{6000})` and `½ ≤ q ≤ ½ + 1/20`, the damping level `T` at
`σ = 128/log x` has `Λ - 56/5 < T ≤ Λ - 10`, and for every set `K` of scales in `(20, T - 2000]`,

`cRed(q)·2^{2q-1}(G/128)^q∑_{k∈K}Γ(q, k-20)e^{q(2q-1)k}(T-k)^{-q/2}`
`  - cJ(q)e^{-64q}(log x)^{-q}E[J(64/log x)^q] - cErr(q)(log x)^{-q} ≤ E|S(x)|^{2q}`
(`RMF.le_integral_rpow_norm_low_of_half_le`). -/
theorem exists_level_aboveHalf (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1 / 2 + 1 / 20) :
    ∃ T : ℕ, Real.log (Real.log x) - 56 / 5 < T ∧ (T : ℝ) + 10 ≤ Real.log (Real.log x)
      ∧ ∀ K : Finset ℕ, (∀ k ∈ K, 20 < k ∧ k + 2000 ≤ T) →
        cRed q * (2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * 64)) ^ q
            * ∑ k ∈ K, perScaleConst q (k - 20) * Real.exp (q * (2 * q - 1) * k)
              * ((T - k : ℕ) : ℝ) ^ (-(q / 2)))
          - cJ q * Real.exp (-(64 * q)) * Real.log x ^ (-q) * (∫ ω, (∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
                  ((1 / 2 : ℂ) + ((64 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
                / (((64 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
          - cErr q * Real.log x ^ (-q)
        ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, hwt, -⟩ := loglog_facts_of_six_thousand hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.2 (Real.exp_pos _)) hx
  have hL6 : (25600 : ℝ) ≤ Real.log x := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6000)
    linarith
  have hσ : 0 < 2 * 64 / Real.log x := by positivity
  have hσ1 : 2 * 64 / Real.log x ≤ 1 / 200 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    linarith
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := exists_damping_level hσ hσ1
  have hℓ : Real.log (1 / (200 * (2 * 64 / Real.log x)))
      = Real.log (Real.log x) - Real.log 25600 := by
    rw [show 1 / (200 * (2 * 64 / Real.log x)) = Real.log x / 25600 by field_simp; ring,
      Real.log_div hL0.ne' (by norm_num)]
  rw [hℓ] at hT3 hT4
  have hl1 : Real.log 25600 ≤ 51 / 5 := by interval_decide (trust := kernel)
  have hl2 : 10 ≤ Real.log 25600 := by interval_decide (trust := kernel)
  refine ⟨T, by linarith, by linarith, fun K hK => ?_⟩
  -- the reduction at `V = 64`
  have hred := le_integral_rpow_weightedRademacherSum_euler_full_explicit hX (V := 64) (q := q)
    (by norm_num) hwt (by linarith) (by linarith) (by linarith)
  -- the main term at `σ = 128/log x`, `N_q(k)` from below
  have hyT := scaleCut_add_seven_le hx1 (T := T) (by linarith)
  have hm5 := le_rpow_mul_integral_rpow_integral_lineDiv_numeral hX hσ (by linarith) hq1
    (k₀ := 20) (y := ⌊x⌋₊ + 1) le_rfl hT1 hT2 hyT hK (fun k _ h => absurd h (not_lt.2 hq0))
    hL0 (div_mul_cancel₀ _ hL0.ne')
  refine aboveHalf_combine hred hm5 (Finset.sum_le_sum fun k hk => ?_) (by positivity)
    (cRed_pos q).le
  have hkT : k ≤ T := by
    have := (hK k hk).2
    omega
  have hσk : 2 * 64 / Real.log x * Real.exp (k : ℝ) ≤ 1 / 200 :=
    le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by exact_mod_cast hkT)) hσ.le) hT1
  have hN := le_integral_rpow_norm_low_of_half_le hX hσ.le hq0 hq1 (k := k)
    (by have := (hK k hk).1; omega) hσk
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hN (perScaleConst_nonneg (by linarith) (by linarith) _))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-! ### The regimes -/

/-- **F, the floor**: for `x ≥ exp(e^{6000})`, `q > 0` and `qΛ ≤ 37/2`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`
(`RMF.le_integral_rpow_weightedRademacherSum_floor_explicit`, `RMF.floor_num`). -/
theorem le_integral_rpow_floorRegime (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 0 < q)
    (hqΛ : q * Real.log (Real.log x) ≤ 37 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, hwt, -⟩ := loglog_facts_of_six_thousand hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hq12 : q ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hΛ hq0.le
    linarith
  exact le_trans (floor_regime_arith hq0 hL0 hΛ hqΛ)
    (le_integral_rpow_weightedRademacherSum_floor_explicit hX hwt hq0 hq12)

/-- **B1**: for `x ≥ exp(e^{6000})`, `0 < q ≤ 9/20` and `qΛ > 37/2`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`: `RMF.exists_level_belowHalf` on the one scale
`k = 21`, and `RMF.PhiB1_ge`. -/
theorem le_integral_rpow_mainB1Regime (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 0 < q) (hq : q ≤ 9 / 20)
    (hqΛ : 37 / 2 < q * Real.log (Real.log x)) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, -, -, -⟩ := loglog_facts_of_six_thousand hx
  obtain ⟨T, hT, hTΛ, -, H⟩ := exists_level_belowHalf hX hx hq0 (by linarith) hqΛ.le
  have h := H {21}
    (fun k hk => by
      rw [Finset.mem_singleton] at hk
      subst hk
      exact ⟨by norm_num, by omega⟩)
    (fun k hk => by
      rw [Finset.mem_singleton] at hk
      subst hk
      change 1 ≤ c3Kmax q
      exact le_max_left _ _)
  exact le_of_sub_mul_le h (mainB1_mul_le_sum hq0 (by linarith) hT hTΛ)
    (by unfold PhiB1; ring) (PhiB1_ge hq0 hq)
    (mul_nonneg (le_min (by linarith) (inv_nonneg.2 (by linarith)))
      (Real.rpow_nonneg (by linarith) _))

/-- **B2**: for `x ≥ exp(e^{6000})` and `9/20 ≤ q < ½`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`: `RMF.exists_level_belowHalf` on the scales
`21 ≤ k ≤ 20 + min(K_max(q), T - 2020)`, and `RMF.PhiB2_ge`. -/
theorem le_integral_rpow_mainB2Regime (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 9 / 20 ≤ q) (hq : q < 1 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, -, -, -⟩ := loglog_facts_of_six_thousand hx
  have hqΛ : 37 / 2 ≤ q * Real.log (Real.log x) := by
    have := mul_le_mul hq0 hΛ (by norm_num) (by linarith)
    linarith
  obtain ⟨T, hT, hTΛ, hTl, H⟩ := exists_level_belowHalf hX hx (by linarith) hq hqΛ
  have h := H (Finset.Icc 21 (20 + min (c3Kmax q) (T - 2020)))
    (fun k hk => by
      rw [Finset.mem_Icc] at hk
      have := min_le_right (c3Kmax q) (T - 2020)
      exact ⟨by omega, by omega⟩)
    (fun k hk => by
      rw [Finset.mem_Icc] at hk
      have := min_le_left (c3Kmax q) (T - 2020)
      omega)
  exact le_of_sub_mul_le h (mainB2_mul_le_sum hq0 hq hΛ hT hTΛ hTl)
    (by unfold PhiB2; ring) (PhiB2_ge hq0 hq)
    (mul_nonneg (le_min (by linarith) (inv_nonneg.2 (by linarith)))
      (Real.rpow_nonneg (by linarith) _))

/-- **H, `q = ½`**: for `x ≥ exp(e^{6000})`, `10⁻⁷Λ^{3/4} ≤ E|S(x)|`: `RMF.exists_level_aboveHalf`
on the scales `21 ≤ k ≤ T - 2000`, the subtracted term at `½` (`17.3`), and `RMF.cHalfLB_ge`. -/
theorem le_integral_norm_halfRegime (hX : IsRademacherPrimeValues X μ) {x : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) :
    1 / 10 ^ 7 * Real.log (Real.log x) ^ (3 / 4 : ℝ)
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ := by
  obtain ⟨hΛ, hL, -, -⟩ := loglog_facts_of_six_thousand hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.2 (Real.exp_pos _)) hx
  obtain ⟨T, hT1, hT2, H⟩ := exists_level_aboveHalf hX hx (q := 1 / 2) le_rfl (by norm_num)
  have hT2020 : 2020 ≤ T := by
    have : (2020 : ℝ) ≤ T := by linarith
    exact_mod_cast this
  have h := H (Finset.Icc 21 (T - 2000)) fun k hk => by
    rw [Finset.mem_Icc] at hk
    exact ⟨by omega, by omega⟩
  have hR := integral_sqrt_lineDiv_le_subtracted_half hX hx1 hΛ (V := 64) (by norm_num)
  have key := half_regime_arith hL0 hΛ h (half_sum_ge hΛ hT1 hT2) hR
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at key
  simpa only [Real.rpow_one] using key

/-- **L, Lyapunov from H**: for `x ≥ exp(e^{6000})`, `½ < q`, `δ = 2q - 1 < 10⁻⁸` and `δΛ ≤ 1`,
`10⁻¹⁰(log x)^{qδ}min{1/δ, Λ}^{3/4} ≤ E|S(x)|^{2q}`: `E|S|^{2q} ≥ (E|S|)^{2q} ≥ (10⁻⁸Λ^{3/4})^{2q}`
(`RMF.integral_rpow_le_rpow_integral_of_le`) and `RMF.lyap_num`. -/
theorem le_integral_rpow_lyapunovRegime (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 1 / 2 < q) (hδ : 2 * q - 1 < 1 / 10 ^ 8)
    (hu : (2 * q - 1) * Real.log (Real.log x) ≤ 1) :
    1 / 10 ^ 10 * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  obtain ⟨hΛ, hL, -, -⟩ := loglog_facts_of_six_thousand hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hqne : q ≠ 0 := ne_of_gt (by linarith)
  have hH : 1 / 10 ^ 8 * Real.log (Real.log x) ^ (3 / 4 : ℝ)
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ :=
    le_trans (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg (by linarith) _))
      (le_integral_norm_halfRegime hX hx)
  have hLy := integral_rpow_le_rpow_integral_of_le (μ := μ) (p := q) (q := 1 / 2) (by norm_num)
    hq0.le (memLp_weightedRademacherSum hX x _)
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at hLy
  simp only [Real.rpow_one] at hLy
  have hE0 : 0 ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hE10 : 0 ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ∂μ := integral_nonneg fun ω => norm_nonneg _
  have hpow : (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ∂μ) ^ (2 * q)
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
    calc (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ∂μ) ^ (2 * q)
        ≤ ((∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ) ^ (1 / 2 / q)) ^ (2 * q) :=
          Real.rpow_le_rpow hE10 hLy (by linarith)
      _ = _ := by
          rw [← Real.rpow_mul hE0, show 1 / 2 / q * (2 * q) = 1 by field_simp, Real.rpow_one]
  have h1 : (1 / 10 ^ 8 * Real.log (Real.log x) ^ (3 / 4 : ℝ)) ^ (2 * q)
      ≤ (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ∂μ) ^ (2 * q) :=
    Real.rpow_le_rpow (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)) hH
      (by linarith)
  exact le_trans (lyapunov_regime_arith hq0 hδ hL0 (by linarith) hu) (h1.trans hpow)

/-- **S, the sliver**: for `x ≥ exp(e^{6000})`, `½ < q`, `δ = 2q - 1 < 10⁻⁸` and `δΛ ≥ 1`,
`10⁻¹⁰(log x)^{qδ}min{1/δ, Λ}^{3/4} ≤ E|S(x)|^{2q}`: `RMF.exists_level_aboveHalf` on the scales
`T - 2000 - J ≤ k ≤ T - 2000`, `J = ⌊1/(2δ)⌋`, the subtracted term (`33`) and `RMF.PhiSl_ge`. -/
theorem le_integral_rpow_sliverRegime (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 1 / 2 < q) (hδ : 2 * q - 1 < 1 / 10 ^ 8)
    (hu : 1 ≤ (2 * q - 1) * Real.log (Real.log x)) :
    1 / 10 ^ 10 * (Real.log x ^ (q * (2 * q - 1))
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
  exact sliver_regime_arith hL0 hΛ hq0 hq1 hu h hS hR

/-- **BB, Bonami–Beckner**: for `x ≥ exp(e^{6000})`, `q ≤ 1` and `δ = 2q - 1 ≥ 10⁻⁸`,
`10⁻¹⁰(log x)^{qδ}min{1/δ, Λ}^{3/4} ≤ E|S(x)|^{2q}`
(`RMF.le_integral_rpow_weightedRademacherSum_largeQ_bb`, `δ^{3/4} ≥ δ ≥ 10⁻⁸ ≥ 10·10⁻¹⁰`). -/
theorem le_integral_rpow_bbRegime (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq1 : q ≤ 1) (hδ : 1 / 10 ^ 8 ≤ 2 * q - 1) :
    1 / 10 ^ 10 * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  obtain ⟨-, -, -, h405⟩ := loglog_facts_of_six_thousand hx
  have hδ0 : 0 < 2 * q - 1 := lt_of_lt_of_le (by norm_num) hδ
  have hc : 10 * (1 / 10 ^ 10 : ℝ) ≤ (2 * q - 1) ^ (3 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hδ0 (by linarith) (by norm_num : (3 / 4 : ℝ) ≤ 1)
    rw [Real.rpow_one] at h
    linarith
  exact le_integral_rpow_weightedRademacherSum_largeQ_bb hX h405 (by linarith) hq1 (by norm_num) hc

end RMF
