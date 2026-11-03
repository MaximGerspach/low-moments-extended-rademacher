/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.Extended.RegimesLow

/-!
# The extended sum below `½` in the mid range `2100 ≤ log log x ≤ 6000`

The twin of `RMF/UniformLower/FinalRegimesMid.lean` for `Y(x) = x^{-1/2}∑_{n≤x} X^e(n)`
(`RMF.le_integral_rpow_belowHalfMid_ext`).  For a Rademacher family, `x ≥ exp(e^{2100})` with
`Λ = log log x ≤ 6000` and `0 < q < ½`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`.

* The analytic input `RMF.exists_level_belowHalfMid_ext` has the weighted sum's conclusion
  verbatim.  The weighted sum's reduction holds from the window threshold, with the error
  constant `cErr`; Y's reduction has the window covering and `cErrD ≤ cErr`
  (`RMF.cErrD_le_cErr`), fed into `RMF.cErr_mul_rpow_le_errBMid`.  F″, B1″ and B2″ use the
  weighted sum's arithmetic and certificates unchanged, F″ with Y's floor from the classical count.
* NH: Y's Hölder bound keeps a factor `½`, paid by `RMF.nh_num_half` (margin `×1.96`).
-/

open MeasureTheory

namespace RMF

/-! ### Arithmetic -/

/-- `cErrD(q) ≤ cErr(q)` for `q ≥ 0`: the factor `2^q` against `16^q`. -/
lemma cErrD_le_cErr {q : ℝ} (hq : 0 ≤ q) : cErrD q ≤ cErr q := by
  unfold cErrD cErr
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by norm_num) (by norm_num) hq)
    (by positivity)

/-- **NH's numeral for `Y`**: `2·10⁻¹⁰·6000^{3/4 + 3/1400}e^{18} ≤ 18·2^{-3/350}`, `RMF.nh_num` with
the factor `2` of Y's Hölder bound (margin `×1.96`). -/
theorem nh_num_half : (2 : ℝ) / 10 ^ 10 * Real.exp ((3 / 4 + 3 / 1400) * Real.log 6000)
      * Real.exp 18
    ≤ 18 * Real.exp (-(3 / 350 * Real.log 2)) := by
  interval_decide (trust := kernel)

/-- **NH's arithmetic for `Y`**: `RMF.nearHalf_arith` against `½(1 + L)^{-(1-2q)}`, for `L > 0`
with `2100 ≤ Λ = log L ≤ 6000`, `q < ½` and `(1-2q)Λ ≤ 18`: its proof with `2·10⁻¹⁰` for `10⁻¹⁰`
and `RMF.nh_num_half`. -/
lemma nearHalf_arith_half {q L : ℝ} (hL : 0 < L) (hΛ1 : 2100 ≤ Real.log L)
    (hΛ2 : Real.log L ≤ 6000) (hq : q < 1 / 2) (hu : (1 - 2 * q) * Real.log L ≤ 18) :
    1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      ≤ 1 / 2 * (1 + L) ^ (-(1 - 2 * q)) := by
  suffices h : 2 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      ≤ (1 + L) ^ (-(1 - 2 * q)) by linarith
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
  have hnum := nh_num_half
  have hm0 : 0 ≤ min (Real.log L) (1 - 2 * q)⁻¹ := le_min hΛ0.le (inv_nonneg.2 hδ0.le)
  have hkey : 2 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
        * Real.exp ((1 - 2 * q) * Real.log L)
      ≤ Real.exp (-(3 / 350 * Real.log 2)) := by
    have hA18 : 2 / 10 ^ 10 * (Real.log L * Real.log L ^ (-(q / 2))) * Real.exp 18
        ≤ 18 * Real.exp (-(3 / 350 * Real.log 2)) := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2 / 10 ^ 10)) (Real.exp_pos 18).le
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
      have hP0 : 0 ≤ 2 / 10 ^ 10 * (Real.log L * Real.log L ^ (-(q / 2))) :=
        mul_nonneg (by norm_num) (mul_nonneg hΛ0.le hg0)
      calc 2 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
            * Real.exp ((1 - 2 * q) * Real.log L)
          ≤ 2 / 10 ^ 10 * (Real.log L * Real.log L ^ (-(q / 2))) * Real.exp 1 :=
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
      have hQ0 : 0 ≤ 2 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))) :=
        mul_nonneg (by norm_num) (mul_nonneg hm0 hg0)
      have h1 := mul_le_mul_of_nonneg_left hu18 hQ0
      have h2 : 2 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
            * ((1 - 2 * q) * Real.log L)
          ≤ 2 / 10 ^ 10 * (Real.log L * Real.log L ^ (-(q / 2))) := by
        have := mul_le_mul_of_nonneg_right hmu hg0
        nlinarith
      have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos 18).le
      nlinarith
  -- conclude
  have hE : Real.exp (-((1 - 2 * q) * Real.log L)) * Real.exp ((1 - 2 * q) * Real.log L) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hT0 : 0 ≤ 2 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))) :=
    mul_nonneg (by norm_num) (mul_nonneg hm0 hg0)
  have h := mul_le_mul_of_nonneg_right hkey (Real.exp_pos (-((1 - 2 * q) * Real.log L))).le
  calc 2 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      = 2 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
        * Real.exp ((1 - 2 * q) * Real.log L) * Real.exp (-((1 - 2 * q) * Real.log L)) := by
        rw [mul_assoc _ (Real.exp _), mul_comm (Real.exp _) (Real.exp _), hE, mul_one]
    _ ≤ Real.exp (-(3 / 350 * Real.log 2)) * Real.exp (-((1 - 2 * q) * Real.log L)) := h
    _ ≤ _ := hlow

/-! ### The reduction with the main term, at the damping level -/

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **Below `½` in the mid range, for `Y`: the reduction at the tilt `V′ = 32/q + 6000`, the
main term and the subtracted term by Jensen.**  `RMF.exists_level_belowHalfMid` with
`E|Y(x)|^{2q}` for `E|S(x)|^{2q}`, its conclusion verbatim: Y's reduction with the window
covering of `RMF.isWindowCovering_of_classical` and the error constant `cErrD ≤ cErr`, Y's main
term (`RMF.le_rpow_mul_integral_rpow_lineDivSq_explicit`) and Jensen bound
(`RMF.integral_rpow_lineDivSq_le_jensen`). -/
theorem exists_level_belowHalfMid_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
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
        ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, -, -⟩ := loglog_facts_of_2100 hx
  obtain ⟨-, -, hx100, hx20, hwin⟩ :=
    loglog_facts_of_low (le_trans (Real.exp_le_exp.2 (Real.exp_le_exp.2 (by norm_num))) hx)
  have hx300 : Real.exp 300 ≤ x := le_trans (Real.exp_le_exp.2 (by norm_num)) hx20
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
  have hred := le_integral_rpow_normalisedSum_compMultExtension_of_windowCovering hX
    (V := 32 / q + 6000) hV0 hx300 hwin hlogV hq0 hq.le
  -- the main term at `σ = 2V′/log x`
  have hyT := scaleCut_add_seven_le hx1 (T := T) (by linarith)
  have h32 : 0 < 32 / q := div_pos (by norm_num) hq0
  have hσy : 16 ≤ 2 * (32 / q + 6000) / Real.log x * Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) :=
    le_trans (by linarith) (two_mul_le_mul_log_floor_add_one hx1 hV0.le)
  have hm5 := le_rpow_mul_integral_rpow_lineDivSq_explicit hX hσ hq0 hq.le (k₀ := 20)
    (y := ⌊x⌋₊ + 1) le_rfl hT1 hT2 hyT hK (fun k hk _ => hKq k hk) hL0
    (div_mul_cancel₀ _ hL0.ne') hσy
  -- the subtracted term by Jensen, and the error term
  have hJ := integral_rpow_lineDivSq_le_jensen hX hx100 hV0 hq0.le (by linarith)
  have hsub := jensen_term_le hq0 hq hL0 hΛ hΛ6
  have hE := le_trans
    (mul_le_mul_of_nonneg_right (cErrD_le_cErr hq0.le) (Real.rpow_nonneg hL0.le _))
    (cErr_mul_rpow_le_errBMid hq0 hq hL0 hΛ hqΛ)
  exact belowHalfMid_combine hred hm5 (cRed_pos q).le hJ (cJ_pos q).le
    (mul_nonneg (mul_nonneg (cJ_pos q).le (Real.exp_pos _).le) (Real.rpow_nonneg hL0.le _)) hsub hE

/-! ### The regimes -/

/-- **F″ for `Y`**: for `x ≥ exp(e^{2100})`, `q > 0` and `qΛ ≤ 37/2`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`: Y's floor
(`RMF.le_integral_rpow_normalisedSum_compMultExtension_floor_classical`) and
`RMF.floor_regime_arith_mid`. -/
theorem le_integral_rpow_floorRegimeMid_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 2100) ≤ x) (hq0 : 0 < q)
    (hqΛ : q * Real.log (Real.log x) ≤ 37 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, -, -⟩ := loglog_facts_of_2100 hx
  obtain ⟨-, -, -, hx20, -⟩ :=
    loglog_facts_of_low (le_trans (Real.exp_le_exp.2 (Real.exp_le_exp.2 (by norm_num))) hx)
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hq12 : q ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hΛ hq0.le
    linarith
  exact le_trans (floor_regime_arith_mid hq0 hL0 hΛ hqΛ)
    (le_integral_rpow_normalisedSum_compMultExtension_floor_classical hX hx20 hq0 hq12)

/-- **B1″ for `Y`**: for `x ≥ exp(e^{2100})` with `Λ ≤ 6000`, `0 < q ≤ 9/20` and `qΛ > 37/2`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`: `RMF.exists_level_belowHalfMid_ext` on the one
scale `k = 21`, and `RMF.PhiB1Mid_ge`. -/
theorem le_integral_rpow_mainB1RegimeMid_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 2100) ≤ x) (hΛ6 : Real.log (Real.log x) ≤ 6000) (hq0 : 0 < q)
    (hq : q ≤ 9 / 20) (hqΛ : 37 / 2 < q * Real.log (Real.log x)) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, -, -, -⟩ := loglog_facts_of_2100 hx
  obtain ⟨T, hT, hTΛ, -, H⟩ := exists_level_belowHalfMid_ext hX hx hΛ6 hq0 (by linarith) hqΛ.le
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

/-- **B2″ for `Y`**: for `x ≥ exp(e^{2100})` with `Λ ≤ 6000`, `9/20 ≤ q < ½` and
`(1-2q)Λ ≥ 18`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`:
`RMF.exists_level_belowHalfMid_ext` on the scales `21 ≤ k ≤ 20 + min(K_max(q), T - 2020)`, and
`RMF.PhiB2Mid_ge`. -/
theorem le_integral_rpow_mainB2RegimeMid_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 2100) ≤ x) (hΛ6 : Real.log (Real.log x) ≤ 6000) (hq0 : 9 / 20 ≤ q)
    (hq : q < 1 / 2) (hu : 18 ≤ (1 - 2 * q) * Real.log (Real.log x)) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, -, -, -⟩ := loglog_facts_of_2100 hx
  have hqΛ : 37 / 2 ≤ q * Real.log (Real.log x) := by
    have := mul_le_mul hq0 hΛ (by norm_num) (by linarith)
    linarith
  obtain ⟨T, hT, hTΛ, hTl, H⟩ := exists_level_belowHalfMid_ext hX hx hΛ6 (by linarith) hq hqΛ
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

/-- **NH for `Y`, near `½` by Hölder**: for `x ≥ exp(e^{2100})` with `Λ ≤ 6000`, `q < ½` and
`(1-2q)Λ ≤ 18`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`:
`½(1 + log x)^{-(1-2q)} ≤ E|Y(x)|^{2q}`
(`RMF.le_integral_rpow_normalisedSum_compMultExtension_holder`) and `RMF.nearHalf_arith_half`. -/
theorem le_integral_rpow_nearHalfRegime_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 2100) ≤ x) (hΛ6 : Real.log (Real.log x) ≤ 6000) (hq : q < 1 / 2)
    (hu : (1 - 2 * q) * Real.log (Real.log x) ≤ 18) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, -, h405⟩ := loglog_facts_of_2100 hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx9 : (9 : ℝ) ≤ x := le_trans (by linarith [Real.add_one_le_exp (405 : ℝ)]) h405
  have hq0 : 0 < q := by
    have hb : 0 < 1 - 2 * q := by linarith
    have := mul_le_mul_of_nonneg_left hΛ hb.le
    linarith
  exact le_trans (nearHalf_arith_half hL0 hΛ hΛ6 hq hu)
    (le_integral_rpow_normalisedSum_compMultExtension_holder hX hx9 hq0 hq)

/-- **Below `½` for `Y` in the mid range**: for a Rademacher family, `x ≥ exp(e^{2100})` with
`log log x ≤ 6000` and `0 < q < ½`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`: F″ for
`qΛ ≤ 37/2`, else B1″ for `q ≤ 9/20`, else B2″ for `(1-2q)Λ ≥ 18` and NH otherwise.
`RMF.le_integral_rpow_belowHalfMid` with `Y` for `S`. -/
theorem le_integral_rpow_belowHalfMid_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 2100) ≤ x) (hΛ6 : Real.log (Real.log x) ≤ 6000) (hq0 : 0 < q)
    (hq : q < 1 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  rcases le_or_gt (q * Real.log (Real.log x)) (37 / 2) with h | h
  · exact le_integral_rpow_floorRegimeMid_ext hX hx hq0 h
  rcases le_or_gt q (9 / 20) with h' | h'
  · exact le_integral_rpow_mainB1RegimeMid_ext hX hx hΛ6 hq0 h' h
  rcases le_or_gt 18 ((1 - 2 * q) * Real.log (Real.log x)) with h'' | h''
  · exact le_integral_rpow_mainB2RegimeMid_ext hX hx hΛ6 h'.le hq h''
  · exact le_integral_rpow_nearHalfRegime_ext hX hx hΛ6 hq h''.le

end RMF
