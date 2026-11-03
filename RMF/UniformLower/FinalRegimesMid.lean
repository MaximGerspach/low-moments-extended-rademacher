/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.LowerAllX

/-!
# The final assembly below `½` in the mid range `2100 ≤ log log x ≤ 6000`

For a Rademacher family, `x ≥ exp(e^{2100})` and `Λ = log log x ≤ 6000`, the first conjunct of
`RMF.weighted_rademacher_moments_lower_uniform_explicit` (`RMF.le_integral_rpow_belowHalfMid`),
by four regimes:

* **F″**, `qΛ ≤ 37/2` (`RMF.le_integral_rpow_floorRegimeMid`, every `Λ ≥ 2100`): the floor and
  `RMF.floor_num_mid`;
* **B1″**, `37/2 < qΛ`, `q ≤ 9/20`, and **B2″**, `9/20 ≤ q < ½`, `(1-2q)Λ ≥ 18`
  (`RMF.le_integral_rpow_mainB1RegimeMid`, `RMF.le_integral_rpow_mainB2RegimeMid`): the reduction
  at the tilt `V′ = 32/q + 6000` (`RMF.exists_level_belowHalfMid`), its subtracted term by Jensen
  (`RMF.integral_rpow_lineDiv_le_jensen`) in place of
  `RMF.integral_rpow_lineDiv_le_subtracted_belowHalf`, which needs `Λ ≥ 6000`: with
  `V′q ≥ 32 + qΛ` it is at most `cJ(q)e^{-32}min{Λ, (1-2q)⁻¹}Λ^{-q/2}`.  The main terms are B1's
  and B2's times `(32/(32 + 6000q))^q`, B2″ counting its scales as `min{Λ, (1-2q)⁻¹}/2`;
  `RMF.PhiB1Mid_ge`, `RMF.PhiB2Mid_ge`;
* **NH**, `(1-2q)Λ ≤ 18` (`RMF.le_integral_rpow_nearHalfRegime`): Hölder,
  `E|S|^{2q} ≥ (E|S|)^{2-2q}/(E|S|²)^{1-2q} ≥ (1 + log x)^{-(1-2q)}` (`E|S| ≥ 1`,
  `E|S|² ≤ 1 + log x`), and `RMF.nh_num`.
-/

open MeasureTheory

namespace RMF

/-! ### Arithmetic -/

/-- `log q + Λ ≥ 2090` for `2100 ≤ Λ ≤ 6000` and `qΛ ≥ 37/2`: `log q ≥ log(37/2) - log 6000`. -/
lemma log_add_ge_of_mul_ge_mid {q Λ : ℝ} (hΛ1 : 2100 ≤ Λ) (hΛ2 : Λ ≤ 6000)
    (hqΛ : 37 / 2 ≤ q * Λ) : 2090 ≤ Real.log q + Λ := by
  have hΛ0 : 0 < Λ := by linarith
  have hq' : 37 / 2 / Λ ≤ q := by
    rw [div_le_iff₀ hΛ0]
    linarith
  have h1 : Real.log (37 / 2 / Λ) ≤ Real.log q := Real.log_le_log (by positivity) hq'
  rw [Real.log_div (by norm_num) hΛ0.ne'] at h1
  have h2 : Real.log Λ ≤ Real.log 6000 := Real.log_le_log hΛ0 hΛ2
  have h3 : (29 / 10 : ℝ) ≤ Real.log (37 / 2) := by interval_decide (trust := kernel)
  have h4 : Real.log 6000 ≤ 8.71 := by interval_decide (trust := kernel)
  linarith

/-- **The floor's arithmetic at `Λ ≥ 2100`**: for `q > 0`, `Λ = log L ≥ 2100` and `qΛ ≤ 37/2`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ 2^{-(1-2q)}3^{-(1-q)}(0.49/L)^q` (`RMF.floor_num_mid`). -/
lemma floor_regime_arith_mid {q L : ℝ} (hq0 : 0 < q) (hL : 0 < L) (hΛ : 2100 ≤ Real.log L)
    (hqΛ : q * Real.log L ≤ 37 / 2) :
    1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      ≤ (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (49 / (100 * L)) ^ q := by
  have hq6 : q * 2100 ≤ q * Real.log L := mul_le_mul_of_nonneg_left hΛ hq0.le
  have hqs : q ≤ 37 / 4200 := by linarith
  have hb : 1 - 37 / 2100 ≤ 1 - 2 * q := by linarith
  have hmin : min (Real.log L) (1 - 2 * q)⁻¹ ≤ 2100 / 2063 := by
    refine (min_le_right _ _).trans ?_
    calc (1 - 2 * q)⁻¹ ≤ (1 - 37 / 2100)⁻¹ := inv_anti₀ (by norm_num) hb
      _ = 2100 / 2063 := by norm_num
  have hpow : Real.log L ^ (-(q / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hpow0 : 0 ≤ Real.log L ^ (-(q / 2)) := Real.rpow_nonneg (by linarith) _
  have hT : min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)) ≤ 2100 / 2063 := by
    calc _ ≤ 2100 / 2063 * 1 := mul_le_mul hmin hpow hpow0 (by norm_num)
      _ = 2100 / 2063 := mul_one _
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
  have h49 : Real.exp (37 / 4200 * Real.log (49 / 100)) * Real.exp (-(37 / 2))
      ≤ (49 / (100 * L)) ^ q := by
    rw [show (49 : ℝ) / (100 * L) = 49 / 100 / L by ring, Real.rpow_def_of_pos (by positivity),
      Real.log_div (by norm_num) hL.ne', ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hl : Real.log (49 / 100) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    have h1 := mul_le_mul_of_nonpos_right hqs hl
    linarith
  have hnum := floor_num_mid
  have he0 : 0 ≤ Real.exp (37 / 4200 * Real.log (49 / 100)) * Real.exp (-(37 / 2)) := by
    positivity
  calc 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      ≤ 1 / 10 ^ 10 * (2100 / 2063) := mul_le_mul_of_nonneg_left hT (by norm_num)
    _ ≤ 1 / 2 * (1 / 3)
          * (Real.exp (37 / 4200 * Real.log (49 / 100)) * Real.exp (-(37 / 2))) := by
        linarith
    _ ≤ _ := mul_le_mul (mul_le_mul h2 h3 (by norm_num) (by positivity)) h49 he0 (by positivity)

/-- **The error term below `½`, mid range**: `cErr(q)L^{-q} ≤ errBMid(q)·min{Λ, (1-2q)⁻¹}Λ^{-q/2}`
for `Λ = log L ≥ 2100` and `qΛ ≥ 37/2` (`RMF.exp_neg_mul_rpow_le_of_2100`). -/
lemma cErr_mul_rpow_le_errBMid {q L : ℝ} (hq0 : 0 < q) (hq : q < 1 / 2) (hL : 0 < L)
    (hΛ : 2100 ≤ Real.log L) (hqΛ : 37 / 2 ≤ q * Real.log L) :
    cErr q * L ^ (-q)
      ≤ errBMid q * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))) := by
  have hΛ0 : 0 < Real.log L := by linarith
  have hkey := exp_neg_mul_rpow_le_of_2100 hΛ hq0.le
  have hLq : L ^ (-q) = Real.exp (-(q * Real.log L)) := by
    rw [Real.rpow_def_of_pos hL]
    ring_nf
  have hsplit : Real.log L ^ (q / 2) * Real.log L ^ (-(q / 2)) = 1 := by
    rw [← Real.rpow_add hΛ0, add_neg_cancel, Real.rpow_zero]
  have hg0 : 0 ≤ Real.log L ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  have h1 : Real.exp (-(q * Real.log L))
      ≤ Real.exp (-(545 / 546 * (q * Real.log L))) * Real.log L ^ (-(q / 2)) := by
    calc Real.exp (-(q * Real.log L))
        = Real.exp (-(q * Real.log L)) * Real.log L ^ (q / 2) * Real.log L ^ (-(q / 2)) := by
          rw [mul_assoc, hsplit, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hkey hg0
  have hq6 : q * 2100 ≤ q * Real.log L := mul_le_mul_of_nonneg_left hΛ hq0.le
  have hmax : max (37 / 2) (2100 * q) ≤ q * Real.log L := max_le hqΛ (by linarith)
  have h2 : Real.exp (-(545 / 546 * (q * Real.log L)))
      ≤ Real.exp (-(545 / 546 * max (37 / 2) (2100 * q))) :=
    Real.exp_le_exp.2 (by linarith)
  have hm1 : 1 ≤ min (Real.log L) (1 - 2 * q)⁻¹ :=
    le_min (by linarith) ((one_le_inv₀ (by linarith)).2 (by linarith))
  have hc := (cErr_pos q).le
  unfold errBMid
  calc cErr q * L ^ (-q) = cErr q * Real.exp (-(q * Real.log L)) := by rw [hLq]
    _ ≤ cErr q * (Real.exp (-(545 / 546 * max (37 / 2) (2100 * q)))
          * Real.log L ^ (-(q / 2))) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right h2 hg0)) hc
    _ ≤ cErr q * (Real.exp (-(545 / 546 * max (37 / 2) (2100 * q)))
          * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) hc
        exact le_mul_of_one_le_left hg0 hm1
    _ = _ := by ring

/-- **The subtracted term at the tilt `V′ = 32/q + 6000`, absorbed**: for `0 < q < ½` and `L > 0`
with `2100 ≤ Λ = log L ≤ 6000`,
`e^{-V′q}L^{-q}(1.195πL²/V′)^q ≤ e^{-32}min{Λ, (1-2q)⁻¹}Λ^{-q/2}`: the exponent is
`-32 + q(Λ - 6000) + q(log(1.195π) - log V′)`, and `log(1.195π) + (1/2)log Λ ≤ log V′`. -/
lemma jensen_term_le {q L : ℝ} (hq0 : 0 < q) (hq : q < 1 / 2) (hL : 0 < L)
    (hΛ1 : 2100 ≤ Real.log L) (hΛ2 : Real.log L ≤ 6000) :
    Real.exp (-((32 / q + 6000) * q)) * L ^ (-q)
        * (1.195 * Real.pi * L ^ 2 / (32 / q + 6000)) ^ q
      ≤ Real.exp (-32) * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))) := by
  have hΛ0 : 0 < Real.log L := by linarith
  have h32 : 0 < 32 / q := div_pos (by norm_num) hq0
  have hV : 6000 ≤ 32 / q + 6000 := by linarith
  have hV0 : 0 < 32 / q + 6000 := by linarith
  have hVq : (32 / q + 6000) * q = 32 + 6000 * q := by
    field_simp
  have hB0 : 0 < 1.195 * Real.pi * L ^ 2 / (32 / q + 6000) := by positivity
  have hlogB : Real.log (1.195 * Real.pi * L ^ 2 / (32 / q + 6000))
      = Real.log (1.195 * Real.pi) + 2 * Real.log L - Real.log (32 / q + 6000) := by
    rw [Real.log_div (by positivity) hV0.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    push_cast
    ring
  have hπ : Real.log (1.195 * Real.pi) ≤ 1.33 := by
    have h1 : Real.log (1.195 * Real.pi) ≤ Real.log (1.195 * 3.1416) :=
      Real.log_le_log (by positivity) (by linarith [Real.pi_lt_d4])
    have h2 : Real.log (1.195 * 3.1416) ≤ 1.33 := by interval_decide (trust := kernel)
    linarith
  have h6 : 8.69 ≤ Real.log 6000 := by interval_decide (trust := kernel)
  have hlogV : Real.log 6000 ≤ Real.log (32 / q + 6000) := Real.log_le_log (by norm_num) hV
  have hlogΛ : Real.log (Real.log L) ≤ Real.log 6000 := Real.log_le_log hΛ0 hΛ2
  have hbr : Real.log L - 6000 + Real.log (1.195 * Real.pi) - Real.log (32 / q + 6000)
      + 1 / 2 * Real.log (Real.log L) ≤ 0 := by linarith
  have hqbr := mul_le_mul_of_nonneg_left hbr hq0.le
  have hm1 : 1 ≤ min (Real.log L) (1 - 2 * q)⁻¹ :=
    le_min (by linarith) ((one_le_inv₀ (by linarith)).2 (by linarith))
  have hg0 : 0 ≤ Real.log L ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  rw [Real.rpow_def_of_pos hL, Real.rpow_def_of_pos hB0, hlogB, hVq, ← Real.exp_add,
    ← Real.exp_add]
  calc Real.exp (-(32 + 6000 * q) + Real.log L * -q
        + (Real.log (1.195 * Real.pi) + 2 * Real.log L - Real.log (32 / q + 6000)) * q)
      ≤ Real.exp (-32 + Real.log (Real.log L) * -(q / 2)) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (-32) * Real.log L ^ (-(q / 2)) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hΛ0]
    _ ≤ Real.exp (-32) * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hg0 hm1) (Real.exp_pos _).le

/-- **Below `½` in the mid range, the three terms combined**: the reduction
`cRed·L^{-q}I - cJ·e·L^{-q}I_J - cErr·L^{-q} ≤ E`, the main term `A·S ≤ L^{-q}I`, Jensen
`I_J ≤ B`, the subtracted term `e·L^{-q}B ≤ e^{-32}·m·g` and the error
`cErr·L^{-q} ≤ errB·m·g` give `cRed·A·S - (cJ·e^{-32} + errB)·m·g ≤ E`. -/
lemma belowHalfMid_combine {E Im Is S cR cJ' cE A Lm e B m g eB : ℝ}
    (hred : cR * (Lm * Im) - cJ' * e * Lm * Is - cE * Lm ≤ E)
    (hm5 : A * S ≤ Lm * Im) (hcR : 0 ≤ cR) (hJ : Is ≤ B) (hcJ : 0 ≤ cJ')
    (hcJe : 0 ≤ cJ' * e * Lm) (hsub : e * Lm * B ≤ Real.exp (-32) * (m * g))
    (hE : cE * Lm ≤ eB * (m * g)) :
    cR * (A * S) - (cJ' * Real.exp (-32) + eB) * (m * g) ≤ E := by
  have h1 := mul_le_mul_of_nonneg_left hm5 hcR
  have h2 := mul_le_mul_of_nonneg_left hJ hcJe
  have h3 := mul_le_mul_of_nonneg_left hsub hcJ
  linarith

/-- **The tilt's factor**: `(G/(2V′))^q = (G/(2·32/q))^q(32/(32 + 6000q))^q`, `V′ = 32/q + 6000`. -/
lemma rpow_G_div_tilt {q : ℝ} (hq : 0 < q) :
    (Real.exp (-0.592) / 2 / (2 * (32 / q + 6000))) ^ q
      = (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q * (32 / (32 + 6000 * q)) ^ q := by
  have hq' : q ≠ 0 := hq.ne'
  have h1 : (32 : ℝ) + 6000 * q ≠ 0 := by positivity
  have h2 : (32 : ℝ) / q + 6000 ≠ 0 := by positivity
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

/-- **B1″'s main term**: `RMF.mainB1_mul_le_sum` times the tilt's factor. -/
lemma mainB1Mid_mul_le_sum {q Λ : ℝ} {T : ℕ} (hq0 : 0 < q) (hq : q < 1 / 2) (hT : 2021 ≤ T)
    (hTΛ : (T : ℝ) ≤ Λ) :
    mainB1Mid q * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)))
      ≤ cRed q * (2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q + 6000))) ^ q
        * ∑ k ∈ ({21} : Finset ℕ), perScaleConst q (k - 20)
          * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
          * ((T - k : ℕ) : ℝ) ^ (-(q / 2))) := by
  have h := mul_le_mul_of_nonneg_right (mainB1_mul_le_sum hq0 hq hT hTΛ)
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 32 / (32 + 6000 * q)) q)
  rw [rpow_G_div_tilt hq0]
  calc mainB1Mid q * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)))
      = mainB1 q * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2))) * (32 / (32 + 6000 * q)) ^ q := by
        rw [mainB1Mid]
        ring
    _ ≤ _ := h
    _ = _ := by ring

/-- **B2″'s main term**: on the scales `21 ≤ k ≤ 20 + n`, `n = min(K_max(q), T - 2020)`, for
`9/20 ≤ q < ½`, `Λ ≥ 2100` and `(1-2q)Λ ≥ 18`: as `RMF.mainB2_mul_le_sum`, with
`n - 1 ≥ min{Λ, (1-2q)⁻¹}/2` (`min ≤ (1-2q)⁻¹ ≤ Λ/18`; `⌊w⌋ - 1 ≥ w/2 + 1` for `w ≥ 10`, and
`T - 2021 > Λ - 2038 ≥ Λ/36`) and the tilt's factor. -/
lemma mainB2Mid_mul_le_sum {q Λ : ℝ} {T : ℕ} (hq0 : 9 / 20 ≤ q) (hq : q < 1 / 2)
    (hΛ : 2100 ≤ Λ) (hu : 18 ≤ (1 - 2 * q) * Λ) (hT : 2021 ≤ T) (hTΛ : (T : ℝ) ≤ Λ)
    (hTl : Real.log q + Λ - 16 < T) :
    mainB2Mid q * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)))
      ≤ cRed q * (2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q + 6000))) ^ q
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
  -- `n - 1 ≥ min{Λ, (1-2q)⁻¹}/2`
  have hlog : -81 / 100 ≤ Real.log q :=
    le_trans (by interval_decide (trust := kernel) : (-81 / 100 : ℝ) ≤ Real.log (9 / 20))
      (Real.log_le_log (by norm_num) hq0)
  have hw10 : 10 ≤ 1 / (1 - 2 * q) := by
    rw [le_div_iff₀ hb]
    linarith
  have hmin : min Λ (1 - 2 * q)⁻¹ ≤ 1 / (1 - 2 * q) := by
    rw [one_div]
    exact min_le_right _ _
  have hwΛ : 1 / (1 - 2 * q) ≤ Λ / 18 := by
    rw [div_le_div_iff₀ hb (by norm_num)]
    linarith
  have hnA : 1 / 2 * min Λ (1 - 2 * q)⁻¹ + 1 ≤ (c3Kmax q : ℝ) := by
    have h1 : ⌊1 / (1 - 2 * q)⌋₊ ≤ c3Kmax q := le_max_right _ _
    have h2 : 1 / (1 - 2 * q) < (⌊1 / (1 - 2 * q)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : (⌊1 / (1 - 2 * q)⌋₊ : ℝ) ≤ c3Kmax q := by exact_mod_cast h1
    linarith
  have hnB : 1 / 2 * min Λ (1 - 2 * q)⁻¹ + 1 ≤ ((T - 2020 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    linarith
  have hn1 : 1 / 2 * min Λ (1 - 2 * q)⁻¹ + 1 ≤ (n : ℝ) := by
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
  have hP0 : 0 ≤ cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
      * (32 / (32 + 6000 * q)) ^ q := by
    have := cRed_pos q
    positivity
  rw [rpow_G_div_tilt hqpos]
  calc mainB2Mid q * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)))
      = (cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
          * (32 / (32 + 6000 * q)) ^ q)
        * (1 / 2 * min Λ (1 - 2 * q)⁻¹
          * (perScaleLow2 q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) * Λ ^ (-(q / 2)))) := by
        unfold mainB2Mid
        ring
    _ ≤ (cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
          * (32 / (32 + 6000 * q)) ^ q)
        * (((n : ℝ) - 1)
          * (perScaleLow2 q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) * Λ ^ (-(q / 2)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hc0) hP0
    _ ≤ (cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
          * (32 / (32 + 6000 * q)) ^ q)
        * ∑ k ∈ Finset.Icc 21 (20 + n), perScaleConst q (k - 20)
          * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
          * ((T - k : ℕ) : ℝ) ^ (-(q / 2)) := mul_le_mul_of_nonneg_left hsum hP0
    _ = _ := by ring

/-- `18e^u ≤ ue^{18}` for `1 ≤ u ≤ 18`: `e^{18-u} ≥ 19 - u` and `u(19 - u) ≥ 18`. -/
lemma eighteen_mul_exp_le {u : ℝ} (h1 : 1 ≤ u) (h18 : u ≤ 18) :
    18 * Real.exp u ≤ u * Real.exp 18 := by
  have he : Real.exp 18 = Real.exp u * Real.exp (18 - u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have ht : 19 - u ≤ Real.exp (18 - u) := by linarith [Real.add_one_le_exp (18 - u)]
  have hq : 18 ≤ u * (19 - u) := by nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h18)]
  have hpos := Real.exp_pos u
  rw [he]
  calc 18 * Real.exp u ≤ u * (19 - u) * Real.exp u := mul_le_mul_of_nonneg_right hq hpos.le
    _ ≤ u * Real.exp (18 - u) * Real.exp u :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by linarith)) hpos.le
    _ = u * (Real.exp u * Real.exp (18 - u)) := by ring

/-- **NH's arithmetic**: for `L > 0` with `2100 ≤ Λ = log L ≤ 6000`, `q < ½` and
`u = (1-2q)Λ ≤ 18`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ (1 + L)^{-(1-2q)}`: with `δ = 1 - 2q`,
`Λ·Λ^{-q/2} = Λ^{3/4+δ/4} ≤ 6000^{3/4+3/1400}`, `(1 + L)^{-δ} ≥ (2L)^{-δ} ≥ 2^{-3/350}e^{-u}`,
`min{Λ, 1/δ}e^u ≤ Λe^{18}/18` (`RMF.eighteen_mul_exp_le` for `u ≥ 1`), and `RMF.nh_num`. -/
lemma nearHalf_arith {q L : ℝ} (hL : 0 < L) (hΛ1 : 2100 ≤ Real.log L)
    (hΛ2 : Real.log L ≤ 6000) (hq : q < 1 / 2) (hu : (1 - 2 * q) * Real.log L ≤ 18) :
    1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      ≤ (1 + L) ^ (-(1 - 2 * q)) := by
  have hΛ0 : 0 < Real.log L := by linarith
  have hδ0 : 0 < 1 - 2 * q := by linarith
  have hδ1 : 1 - 2 * q ≤ 3 / 350 := by
    have := mul_le_mul_of_nonneg_left hΛ1 hδ0.le
    linarith
  have hL1 : 1 ≤ L := by
    rw [← Real.exp_log hL]
    exact Real.one_le_exp (by linarith)
  have hg0 : 0 ≤ Real.log L ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  -- `Λ·Λ^{-q/2} ≤ 6000^{3/4+3/1400}`
  have hA : Real.log L * Real.log L ^ (-(q / 2))
      ≤ Real.exp ((3 / 4 + 3 / 1400) * Real.log 6000) := by
    rw [show Real.log L * Real.log L ^ (-(q / 2)) = Real.log L ^ (1 + -(q / 2)) by
        rw [Real.rpow_add hΛ0, Real.rpow_one]]
    calc Real.log L ^ (1 + -(q / 2)) ≤ (6000 : ℝ) ^ (1 + -(q / 2)) :=
          Real.rpow_le_rpow hΛ0.le hΛ2 (by linarith)
      _ ≤ (6000 : ℝ) ^ (3 / 4 + 3 / 1400 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = Real.exp ((3 / 4 + 3 / 1400) * Real.log 6000) := by
          rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  -- `(1 + L)^{-δ} ≥ 2^{-3/350}e^{-u}`
  have hlow : Real.exp (-(3 / 350 * Real.log 2)) * Real.exp (-((1 - 2 * q) * Real.log L))
      ≤ (1 + L) ^ (-(1 - 2 * q)) := by
    have h1 : (2 * L) ^ (-(1 - 2 * q)) ≤ (1 + L) ^ (-(1 - 2 * q)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have h2 : (2 * L) ^ (-(1 - 2 * q))
        = Real.exp (-((1 - 2 * q) * Real.log 2)) * Real.exp (-((1 - 2 * q) * Real.log L)) := by
      rw [Real.rpow_def_of_pos (by linarith), Real.log_mul two_ne_zero hL.ne', ← Real.exp_add]
      congr 1
      ring
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h3 : Real.exp (-(3 / 350 * Real.log 2)) ≤ Real.exp (-((1 - 2 * q) * Real.log 2)) := by
      have := mul_le_mul_of_nonneg_right hδ1 hl2
      exact Real.exp_le_exp.2 (by linarith)
    calc _ ≤ Real.exp (-((1 - 2 * q) * Real.log 2)) * Real.exp (-((1 - 2 * q) * Real.log L)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = (2 * L) ^ (-(1 - 2 * q)) := h2.symm
      _ ≤ _ := h1
  -- `10⁻¹⁰min{Λ, 1/δ}Λ^{-q/2}e^u ≤ 2^{-3/350}`
  have hnum := nh_num
  have hm0 : 0 ≤ min (Real.log L) (1 - 2 * q)⁻¹ := le_min hΛ0.le (inv_nonneg.2 hδ0.le)
  have hkey : 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
        * Real.exp ((1 - 2 * q) * Real.log L)
      ≤ Real.exp (-(3 / 350 * Real.log 2)) := by
    have hA18 : 1 / 10 ^ 10 * (Real.log L * Real.log L ^ (-(q / 2))) * Real.exp 18
        ≤ 18 * Real.exp (-(3 / 350 * Real.log 2)) := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 10)) (Real.exp_pos 18).le
      linarith
    rcases le_or_gt ((1 - 2 * q) * Real.log L) 1 with hu1 | hu1
    · -- `min ≤ Λ`, `e^u ≤ e ≤ e^{18}/18`
      have h17 : (18 : ℝ) ≤ Real.exp 17 := by linarith [Real.add_one_le_exp (17 : ℝ)]
      have he1 : Real.exp ((1 - 2 * q) * Real.log L) ≤ Real.exp 1 := Real.exp_le_exp.2 hu1
      have he18 : 18 * Real.exp 1 ≤ Real.exp 18 := by
        have e : Real.exp 18 = Real.exp 1 * Real.exp 17 := by rw [← Real.exp_add]; norm_num
        rw [e]
        nlinarith [Real.exp_pos 1]
      have hm : min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))
          ≤ Real.log L * Real.log L ^ (-(q / 2)) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hg0
      have hP0 : 0 ≤ 1 / 10 ^ 10 * (Real.log L * Real.log L ^ (-(q / 2))) :=
        mul_nonneg (by norm_num) (mul_nonneg hΛ0.le hg0)
      calc 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
            * Real.exp ((1 - 2 * q) * Real.log L)
          ≤ 1 / 10 ^ 10 * (Real.log L * Real.log L ^ (-(q / 2))) * Real.exp 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num)) he1 (Real.exp_pos _).le hP0
        _ ≤ Real.exp (-(3 / 350 * Real.log 2)) := by
            have := mul_le_mul_of_nonneg_left he18 hP0
            nlinarith
    · -- `min ≤ 1/δ = Λ/u`, `18e^u ≤ ue^{18}`
      have hu18 := eighteen_mul_exp_le hu1.le hu
      have hmu : min (Real.log L) (1 - 2 * q)⁻¹ * ((1 - 2 * q) * Real.log L) ≤ Real.log L := by
        calc min (Real.log L) (1 - 2 * q)⁻¹ * ((1 - 2 * q) * Real.log L)
            ≤ (1 - 2 * q)⁻¹ * ((1 - 2 * q) * Real.log L) :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
          _ = Real.log L := by rw [← mul_assoc, inv_mul_cancel₀ hδ0.ne', one_mul]
      have hQ0 : 0 ≤ 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))) :=
        mul_nonneg (by norm_num) (mul_nonneg hm0 hg0)
      have h1 := mul_le_mul_of_nonneg_left hu18 hQ0
      have h2 : 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
            * ((1 - 2 * q) * Real.log L)
          ≤ 1 / 10 ^ 10 * (Real.log L * Real.log L ^ (-(q / 2))) := by
        have := mul_le_mul_of_nonneg_right hmu hg0
        nlinarith
      have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos 18).le
      nlinarith
  -- conclude
  have hE : Real.exp (-((1 - 2 * q) * Real.log L)) * Real.exp ((1 - 2 * q) * Real.log L) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hT0 : 0 ≤ 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))) :=
    mul_nonneg (by norm_num) (mul_nonneg hm0 hg0)
  have h := mul_le_mul_of_nonneg_right hkey (Real.exp_pos (-((1 - 2 * q) * Real.log L))).le
  calc 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      = 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
        * Real.exp ((1 - 2 * q) * Real.log L) * Real.exp (-((1 - 2 * q) * Real.log L)) := by
        rw [mul_assoc _ (Real.exp _), mul_comm (Real.exp _) (Real.exp _), hE, mul_one]
    _ ≤ Real.exp (-(3 / 350 * Real.log 2)) * Real.exp (-((1 - 2 * q) * Real.log L)) := h
    _ ≤ _ := hlow

/-! ### The subtracted term by Jensen -/

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The subtracted term by Jensen**: for a Rademacher family, `x ≥ e^{100}`, `V > 0` and
`0 ≤ q ≤ 1`, `E[J(V/log x)^q] ≤ (1.195π(log x)²/V)^q`, `J` the reduction's
(`RMF.le_integral_rpow_weightedRademacherSum_of_parseval_explicit`).  Jensen, then Fubini:
`E‖F(½+σ+it)‖² = ∏_{p≤x}(1 + p^{-1-2σ})` at every height, at most `∏_{p≤x}(1 + 1/p) ≤ 1.195 log x`
(`RMF.prod_one_add_inv_primesBelow_le`), and `∫_ℝ dt/(σ²+t²) = π/σ`. -/
theorem integral_rpow_lineDiv_le_jensen (hX : IsRademacherPrimeValues X μ) {x V q : ℝ}
    (hx : Real.exp 100 ≤ x) (hV : 0 < V) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, (∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
            / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ (1.195 * Real.pi * Real.log x ^ 2 / V) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 100 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hL0 : 0 < Real.log x := by linarith
  -- `⌊x⌋ ≥ e^{99}`
  have hfl : Real.exp 99 ≤ (⌊x⌋₊ : ℝ) := by
    have h1 : Real.exp 100 = Real.exp 99 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h3 : (1 : ℝ) ≤ Real.exp 99 := Real.one_le_exp (by norm_num)
    have h4 := Nat.lt_floor_add_one x
    have h5 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos 99).le
    linarith
  have hy2 : 2 ≤ ⌊x⌋₊ := by
    have : (2 : ℝ) ≤ (⌊x⌋₊ : ℝ) :=
      le_trans (by linarith [Real.add_one_le_exp (99 : ℝ)]) hfl
    exact_mod_cast this
  set σ := V / Real.log x with hσdef
  have hσ : 0 < σ := div_pos hV hL0
  have hc : ∀ t : ℝ, (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I := fun t => by push_cast; ring
  have hre : ∀ t : ℝ, ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 + σ :=
    fun t => by rw [← hc]; simp
  -- the height-independent second moment, bounded by Mertens
  have hprod : ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + (p : ℝ) ^ (-2 * (1 / 2 + σ)))
      ≤ 1.195 * Real.log x := by
    have h1 : ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + (p : ℝ) ^ (-2 * (1 / 2 + σ)))
        ≤ ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + (p : ℝ)⁻¹) := by
      refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt.le
      have h := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith : -2 * (1 / 2 + σ) ≤ -1)
      rw [Real.rpow_neg_one] at h
      linarith
    have h2 := prod_one_add_inv_primesBelow_le hfl
    have h3 : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
      Real.log_le_log (by linarith [Real.exp_pos 99]) (Nat.floor_le hx0.le)
    linarith
  have hmeas := measurable_randomEulerProduct_sqfree_uncurry (X := X) hX.measurable
    (1 / 2 + σ) (⌊x⌋₊ + 1)
  simp only [hc] at hmeas
  have henv := ae_forall_norm_randomEulerProduct_mem_Icc hX (⌊x⌋₊ + 1) (c := 1 / 2 + σ)
    (by linarith)
  have hmean := integral_integral_lineDiv_le (μ := μ)
    (F := fun ω t => randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
      (⌊x⌋₊ + 1) ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
    (U := ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + (p : ℝ) ^ (-(1 / 2 + σ))))
    (M := 1.195 * Real.log x) hσ hmeas
    (by
      filter_upwards [henv] with ω hω
      exact fun t => (hω _ (hre t)).2)
    (fun t => by
      rw [hX.isRademacherRMF.integral_norm_randomEulerProduct_sq', hre t]
      exact hprod)
  have hJ1 := integrable_rpow_eulerProductLine_of_two_le hX hy2 hσ zero_le_one
  simp only [Real.rpow_one] at hJ1
  refine le_trans (integral_rpow_le_rpow_integral hq0 hq1
    (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (integral_nonneg fun t => sq_nonneg _))
    hJ1 (integrable_rpow_eulerProductLine_of_two_le hX hy2 hσ hq0)) ?_
  refine Real.rpow_le_rpow (integral_nonneg fun ω => integral_nonneg fun t => sq_nonneg _) ?_ hq0
  calc _ ≤ Real.pi / σ * (1.195 * Real.log x) := hmean
    _ = 1.195 * Real.pi * Real.log x ^ 2 / V := by
        rw [hσdef]
        field_simp

/-! ### The reduction with the main term, at the damping level -/

/-- **Below `½` in the mid range: the reduction at the tilt `V′ = 32/q + 6000`, the main term and
the subtracted term by Jensen.**  For a Rademacher family, `x ≥ exp(e^{2100})` with
`Λ = log log x ≤ 6000`, `0 < q < ½` and `qΛ ≥ 37/2`, the damping level `T` at `σ = 2V′/log x` has
`2021 ≤ T ≤ Λ` and `T > log q + Λ - 16`, and for every set `K` of scales in `(20, T - 2000]` with
`k - 20 ≤ K_max(q)`, with `G = e^{-0.592}/2`, `Γ = RMF.perScaleConst`,

`cRed(q)·2^{2q-1}(G/(2V′))^q∑_{k∈K}Γ(q, k-20)e^{-q(1-2q)(k+0.7866+9.003e^{-k})}(T-k)^{-q/2}`
`  - (cJ(q)e^{-32} + errBMid(q))·min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`. -/
theorem exists_level_belowHalfMid (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 2100) ≤ x) (hΛ6 : Real.log (Real.log x) ≤ 6000) (hq0 : 0 < q)
    (hq : q < 1 / 2) (hqΛ : 37 / 2 ≤ q * Real.log (Real.log x)) :
    ∃ T : ℕ, 2021 ≤ T ∧ (T : ℝ) ≤ Real.log (Real.log x)
      ∧ Real.log q + Real.log (Real.log x) - 16 < T
      ∧ ∀ K : Finset ℕ, (∀ k ∈ K, 20 < k ∧ k + 2000 ≤ T) → (∀ k ∈ K, k - 20 ≤ c3Kmax q) →
        cRed q * (2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q + 6000))) ^ q
            * ∑ k ∈ K, perScaleConst q (k - 20)
              * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
              * ((T - k : ℕ) : ℝ) ^ (-(q / 2)))
          - (cJ q * Real.exp (-32) + errBMid q)
            * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹ * Real.log (Real.log x) ^ (-(q / 2)))
        ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, hwt, -⟩ := loglog_facts_of_2100 hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.2 (Real.exp_pos _)) hx
  -- `log q + Λ ≥ 2090`, so `q log x ≥ e^{2090}`
  have hlq := log_add_ge_of_mul_ge_mid hΛ hΛ6 hqΛ
  have hqL : Real.exp 2090 ≤ q * Real.log x := by
    rw [← Real.exp_log (mul_pos hq0 hL0), Real.log_mul hq0.ne' hL0.ne']
    exact Real.exp_le_exp.2 hlq
  have he : (1212800 : ℝ) ≤ Real.exp 2090 := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2090)
    linarith
  have he' : (36006 : ℝ) ≤ Real.log x := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2100)
    linarith
  -- the tilt `σ = 2V′/log x`, `V′ = 32/q + 6000`
  have hσ : 0 < 2 * (32 / q + 6000) / Real.log x := by positivity
  have hσ1 : 2 * (32 / q + 6000) / Real.log x ≤ 1 / 200 := by
    rw [show 2 * (32 / q + 6000) / Real.log x = 2 * (32 + 6000 * q) / (q * Real.log x) by
        field_simp,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := exists_damping_level hσ hσ1
  have hℓ : Real.log (1 / (200 * (2 * (32 / q + 6000) / Real.log x)))
      = Real.log q + Real.log (Real.log x) - Real.log (400 * (32 + 6000 * q)) := by
    rw [show 1 / (200 * (2 * (32 / q + 6000) / Real.log x))
        = q * Real.log x / (400 * (32 + 6000 * q)) by field_simp; ring,
      Real.log_div (by positivity) (by positivity), Real.log_mul hq0.ne' hL0.ne']
  rw [hℓ] at hT3 hT4
  have hl1 : Real.log (400 * (32 + 6000 * q)) ≤ 15 := by
    have h : Real.log (400 * (32 + 6000 * q)) ≤ Real.log 1212800 :=
      Real.log_le_log (by positivity) (by linarith)
    have h' : Real.log 1212800 ≤ 15 := by interval_decide (trust := kernel)
    linarith
  have hl2 : 9 ≤ Real.log (400 * (32 + 6000 * q)) := by
    have h : Real.log 12800 ≤ Real.log (400 * (32 + 6000 * q)) :=
      Real.log_le_log (by norm_num) (by linarith)
    have h' : 9 ≤ Real.log 12800 := by interval_decide (trust := kernel)
    linarith
  have hlq0 : Real.log q < 0 := Real.log_neg hq0 (by linarith)
  have hT2021 : 2021 ≤ T := by
    have : (2021 : ℝ) ≤ T := by linarith
    exact_mod_cast this
  refine ⟨T, hT2021, by linarith, by linarith, fun K hK hKq => ?_⟩
  -- the reduction at `V′`
  have hV0 : 0 < 32 / q + 6000 := by positivity
  have hlogV : 3 * (32 / q + 6000) + 3 ≤ Real.log x := by
    have h96 : 96 / q ≤ Real.log x / 2 := by
      rw [div_le_div_iff₀ hq0 two_pos]
      linarith
    have e : 3 * (32 / q + 6000) = 96 / q + 18000 := by ring
    linarith
  have hred := le_integral_rpow_weightedRademacherSum_euler_full_explicit hX
    (V := 32 / q + 6000) hV0 hwt hlogV hq0 (by linarith)
  -- the main term at `σ = 2V′/log x`
  have hyT := scaleCut_add_seven_le hx1 (T := T) (by linarith)
  have hm5 := le_rpow_mul_integral_rpow_integral_lineDiv_explicit hX hσ hq0 hq.le (k₀ := 20)
    (y := ⌊x⌋₊ + 1) le_rfl hT1 hT2 hyT hK (fun k hk _ => hKq k hk) hL0
    (div_mul_cancel₀ _ hL0.ne')
  -- the subtracted term by Jensen, and the error term
  have hx100 : Real.exp 100 ≤ x :=
    le_trans (Real.exp_le_exp.2 (le_trans (by norm_num) (Real.add_one_le_exp 2100))) hx
  have hJ := integral_rpow_lineDiv_le_jensen hX hx100 hV0 hq0.le (by linarith)
  have hsub := jensen_term_le hq0 hq hL0 hΛ hΛ6
  have hE := cErr_mul_rpow_le_errBMid hq0 hq hL0 hΛ hqΛ
  exact belowHalfMid_combine hred hm5 (cRed_pos q).le hJ (cJ_pos q).le
    (mul_nonneg (mul_nonneg (cJ_pos q).le (Real.exp_pos _).le) (Real.rpow_nonneg hL0.le _)) hsub hE

/-! ### The regimes -/

/-- **F″, the floor at `Λ ≥ 2100`**: for `x ≥ exp(e^{2100})`, `q > 0` and `qΛ ≤ 37/2`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`
(`RMF.le_integral_rpow_weightedRademacherSum_floor_explicit`, `RMF.floor_num_mid`). -/
theorem le_integral_rpow_floorRegimeMid (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 2100) ≤ x) (hq0 : 0 < q)
    (hqΛ : q * Real.log (Real.log x) ≤ 37 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, hwt, -⟩ := loglog_facts_of_2100 hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hq12 : q ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hΛ hq0.le
    linarith
  exact le_trans (floor_regime_arith_mid hq0 hL0 hΛ hqΛ)
    (le_integral_rpow_weightedRademacherSum_floor_explicit hX hwt hq0 hq12)

/-- **B1″**: for `x ≥ exp(e^{2100})` with `Λ ≤ 6000`, `0 < q ≤ 9/20` and `qΛ > 37/2`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`: `RMF.exists_level_belowHalfMid` on the one scale
`k = 21`, and `RMF.PhiB1Mid_ge`. -/
theorem le_integral_rpow_mainB1RegimeMid (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 2100) ≤ x) (hΛ6 : Real.log (Real.log x) ≤ 6000) (hq0 : 0 < q)
    (hq : q ≤ 9 / 20) (hqΛ : 37 / 2 < q * Real.log (Real.log x)) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, -, -, -⟩ := loglog_facts_of_2100 hx
  obtain ⟨T, hT, hTΛ, -, H⟩ := exists_level_belowHalfMid hX hx hΛ6 hq0 (by linarith) hqΛ.le
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
  exact le_of_sub_mul_le h (mainB1Mid_mul_le_sum hq0 (by linarith) hT hTΛ)
    (by unfold PhiB1Mid; ring) (PhiB1Mid_ge hq0 hq)
    (mul_nonneg (le_min (by linarith) (inv_nonneg.2 (by linarith)))
      (Real.rpow_nonneg (by linarith) _))

/-- **B2″**: for `x ≥ exp(e^{2100})` with `Λ ≤ 6000`, `9/20 ≤ q < ½` and `(1-2q)Λ ≥ 18`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`: `RMF.exists_level_belowHalfMid` on the scales
`21 ≤ k ≤ 20 + min(K_max(q), T - 2020)`, and `RMF.PhiB2Mid_ge`. -/
theorem le_integral_rpow_mainB2RegimeMid (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 2100) ≤ x) (hΛ6 : Real.log (Real.log x) ≤ 6000) (hq0 : 9 / 20 ≤ q)
    (hq : q < 1 / 2) (hu : 18 ≤ (1 - 2 * q) * Real.log (Real.log x)) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, -, -, -⟩ := loglog_facts_of_2100 hx
  have hqΛ : 37 / 2 ≤ q * Real.log (Real.log x) := by
    have := mul_le_mul hq0 hΛ (by norm_num) (by linarith)
    linarith
  obtain ⟨T, hT, hTΛ, hTl, H⟩ := exists_level_belowHalfMid hX hx hΛ6 (by linarith) hq hqΛ
  have h := H (Finset.Icc 21 (20 + min (c3Kmax q) (T - 2020)))
    (fun k hk => by
      rw [Finset.mem_Icc] at hk
      have := min_le_right (c3Kmax q) (T - 2020)
      exact ⟨by omega, by omega⟩)
    (fun k hk => by
      rw [Finset.mem_Icc] at hk
      have := min_le_left (c3Kmax q) (T - 2020)
      omega)
  exact le_of_sub_mul_le h (mainB2Mid_mul_le_sum hq0 hq hΛ hu hT hTΛ hTl)
    (by unfold PhiB2Mid; ring) (PhiB2Mid_ge hq0 hq)
    (mul_nonneg (le_min (by linarith) (inv_nonneg.2 (by linarith)))
      (Real.rpow_nonneg (by linarith) _))

/-- **NH, near `½` by Hölder**: for `x ≥ exp(e^{2100})` with `Λ ≤ 6000`, `q < ½` and
`(1-2q)Λ ≤ 18`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`:
`E|S|^{2q} ≥ (E|S|)^{2-2q}/(E|S|²)^{1-2q}`
(`RMF.rpow_integral_div_rpow_integral_sq_le_integral_rpow` at `2q`), `E|S| ≥ 1`
(`RMF.one_le_integral_norm_weightedRademacherSum`), `E|S|² ≤ 1 + log x`
(`RMF.integral_normSq_weightedRademacherSum_le_one_add_log`) and `RMF.nearHalf_arith`. -/
theorem le_integral_rpow_nearHalfRegime (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 2100) ≤ x) (hΛ6 : Real.log (Real.log x) ≤ 6000) (hq : q < 1 / 2)
    (hu : (1 - 2 * q) * Real.log (Real.log x) ≤ 18) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  obtain ⟨hΛ, hL, -, -⟩ := loglog_facts_of_2100 hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx1 : 1 ≤ x := (lt_of_lt_of_le (Real.one_lt_exp_iff.2 (Real.exp_pos _)) hx).le
  have hq0 : 0 < q := by
    have hb : 0 < 1 - 2 * q := by linarith
    have := mul_le_mul_of_nonneg_left hΛ hb.le
    linarith
  -- integrability: `S` is bounded
  have hint : ∀ r : ℝ, 0 < r → Integrable (fun ω =>
      ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ r) μ :=
    fun r hr => by
      have h := (memLp_weightedRademacherSum hX x (ENNReal.ofReal r)).integrable_norm_rpow
        (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top
      rwa [ENNReal.toReal_ofReal hr.le] at h
  -- the first and second moments
  have h1 := one_le_integral_norm_weightedRademacherSum hX hx1
  have h2 : (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 : ℝ) ∂μ) ≤ 1 + Real.log x := by
    simp only [Real.rpow_two]
    exact integral_normSq_weightedRademacherSum_le_one_add_log hX.isRademacherRMF hx1
  have hpos : 0 < ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 : ℝ) ∂μ := by
    have h := one_le_integral_rpow_weightedRademacherSum hX hx1 (q := 1) (by norm_num)
    rw [show (2 : ℝ) * 1 = 2 by norm_num] at h
    linarith
  -- Hölder at `2q`
  have hPZ := rpow_integral_div_rpow_integral_sq_le_integral_rpow (μ := μ)
    (X := fun ω =>
      ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖)
    (q := 2 * q) (by linarith) (by linarith)
    (Filter.Eventually.of_forall fun ω => norm_nonneg _) (hint _ (by linarith))
    (hint 2 (by norm_num)) hpos
  have hnum1 : 1 ≤ (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ∂μ) ^ (2 - 2 * q) := Real.one_le_rpow h1 (by linarith)
  have hden0 : 0 < (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 : ℝ) ∂μ) ^ (1 - 2 * q) := Real.rpow_pos_of_pos hpos _
  have hden := Real.rpow_le_rpow hpos.le h2 (by linarith : (0 : ℝ) ≤ 1 - 2 * q)
  have hlow : (1 + Real.log x) ^ (-(1 - 2 * q))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
    rw [Real.rpow_neg (by linarith)]
    refine le_trans (inv_anti₀ hden0 hden) (le_trans ?_ hPZ)
    rw [div_eq_mul_inv]
    exact le_mul_of_one_le_left (inv_nonneg.2 hden0.le) hnum1
  exact le_trans (nearHalf_arith hL0 hΛ hΛ6 hq hu) hlow

/-- **Below `½` in the mid range**: for a Rademacher family, `x ≥ exp(e^{2100})` with
`log log x ≤ 6000` and `0 < q < ½`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`: F″ for
`qΛ ≤ 37/2`, else B1″ for `q ≤ 9/20`, else B2″ for `(1-2q)Λ ≥ 18` and NH otherwise. -/
theorem le_integral_rpow_belowHalfMid (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 2100) ≤ x) (hΛ6 : Real.log (Real.log x) ≤ 6000) (hq0 : 0 < q)
    (hq : q < 1 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  rcases le_or_gt (q * Real.log (Real.log x)) (37 / 2) with h | h
  · exact le_integral_rpow_floorRegimeMid hX hx hq0 h
  rcases le_or_gt q (9 / 20) with h' | h'
  · exact le_integral_rpow_mainB1RegimeMid hX hx hΛ6 hq0 h' h
  rcases le_or_gt 18 ((1 - 2 * q) * Real.log (Real.log x)) with h'' | h''
  · exact le_integral_rpow_mainB2RegimeMid hX hx hΛ6 h'.le hq h''
  · exact le_integral_rpow_nearHalfRegime hX hx hΛ6 hq h''.le

end RMF
