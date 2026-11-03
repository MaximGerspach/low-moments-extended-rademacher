/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.Extended.RegimesMid

/-!
# The extended sum below `½` for `log log x ≥ 6000`, and from `67.17` on

The twin of the regimes below `½` of `RMF/UniformLower/FinalRegimes.lean` for
`Y(x) = x^{-1/2}∑_{n≤x} X^e(n)` (`RMF.le_integral_rpow_belowHalf_ext`), and the three ranges
together (`RMF.le_integral_rpow_normalisedSum_compMultExtension_large_explicit`): for a
Rademacher family, `x ≥ exp(e^{67.17})` and `0 < q < ½`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`.

* The analytic input `RMF.exists_level_belowHalf_ext` has the weighted sum's conclusion with the
  subtracted constant `400` (`RMF.integral_rpow_lineDivSq_le_subtracted_belowHalf`) in place of
  `216`, and the error constant `cErrD ≤ cErr` fed into `RMF.cErr_mul_rpow_le_errB`.
* B1 and B2: `RMF.PhiB1Ext`, `RMF.PhiB2Ext`, the weighted sum's constants with `400cJ(q)` for
  `216cJ(q)`.  The weighted sum's certificates (`RMF.finalCells_spec`) bound `216e^{-32}`, having
  used `cJ ≤ 1`; here `400cJ(q) ≤ 216` (`cJ ≤ 1/6`, `RMF.four_hundred_mul_cJ_le`), so they
  certify `PhiB1Ext`, `PhiB2Ext` unchanged.  F with Y's floor from the classical count.
-/

open MeasureTheory

namespace RMF

/-! ### The constants and their certificates -/

/-- **B1's constant for `Y`**: `mainB1 - 400cJ(q)e^{-32} - errB`, `RMF.PhiB1` with Y's
subtracted-term constant `400` for `216`. -/
noncomputable def PhiB1Ext (q : ℝ) : ℝ := mainB1 q - 400 * cJ q * Real.exp (-32) - errB q

/-- **B2's constant for `Y`**: `mainB2 - 400cJ(q)e^{-32} - errB`, `RMF.PhiB2` with `400` for
`216`. -/
noncomputable def PhiB2Ext (q : ℝ) : ℝ := mainB2 q - 400 * cJ q * Real.exp (-32) - errB q

/-- `400cJ(q) ≤ 216` for `0 ≤ q ≤ ½`, from `cJ(q) ≤ 1/6` (`RMF.cJ_le_one_sixth`). -/
lemma four_hundred_mul_cJ_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) : 400 * cJ q ≤ 216 := by
  have := cJ_le_one_sixth hq0 hq
  linarith

/-- **B1 for `Y` on a cell**: `PhiB1Ext(q) ≥ 10⁻¹⁰` for `q ∈ [a, b]`, `b ≤ 9/20`, from the
weighted sum's cell certificate (`lam ≤ cellLogMain a b c β ℓ` and
`10⁻¹⁰ + 216e^{-32} + e^{cellLogErr b u} ≤ e^{lam}`) and `400cJ(q) ≤ 216`. -/
theorem PhiB1Ext_ge_of_cell {a b c β ℓ u lam q : ℝ} (haq : a ≤ q) (hqb : q ≤ b) (hb : b ≤ 9 / 20)
    (hq0 : 0 < q) (hc0 : 0 < c) (hc1 : c ≤ 1) (hc : c ≤ c3FloorK q 1)
    (hβ : q * (1 - 2 * q) ≤ β) (hℓ : ℓ ≤ q * Real.log q) (hu : u ≤ max (37 / 2) (6000 * a))
    (hlam : lam ≤ cellLogMain a b c β ℓ)
    (hcert : 1 / 10 ^ 10 + 216 * Real.exp (-32) + Real.exp (cellLogErr b u) ≤ Real.exp lam) :
    1 / 10 ^ 10 ≤ PhiB1Ext q := by
  have hmain := exp_cellLogMain_le_mainB1 haq hqb hb hq0 hc0 hc1 hc hβ hℓ
  have hlam' := Real.exp_le_exp.2 hlam
  have herr := errB_le_exp_cellLogErr haq hqb (by linarith) hu
  have hsub : 400 * cJ q * Real.exp (-32) ≤ 216 * Real.exp (-32) :=
    mul_le_mul_of_nonneg_right (four_hundred_mul_cJ_le hq0.le (by linarith))
      (Real.exp_pos _).le
  unfold PhiB1Ext
  linarith

/-- **B2 for `Y` from its certificate**: `PhiB2Ext(q) ≥ 10⁻¹⁰` on `[9/20, ½)`, from the
weighted sum's B2 certificate and `400cJ(q) ≤ 216`. -/
theorem PhiB2Ext_ge_of_cert {lam : ℝ}
    (hlam : lam ≤ Real.log (3 / 5)
      + cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20))
      - 9 / 20 * (1 - 2 * (9 / 20)) * 20.7867 - 1 / 2)
    (hcert : 1 / 10 ^ 10 + 216 * Real.exp (-32) + Real.exp (cellLogErr (1 / 2) 2700)
      ≤ Real.exp lam)
    {q : ℝ} (hq0 : 9 / 20 ≤ q) (hq1 : q < 1 / 2) : 1 / 10 ^ 10 ≤ PhiB2Ext q := by
  have hqpos : 0 < q := by linarith
  have hℓ := mul_log_ge_of_exp_neg_one_le (by linarith [Real.exp_neg_one_lt_d9]) hq0
  have hcore := exp_cellLogCore_le (c := 0.17784) (C := 0.17784) hq0 hq1.le le_rfl hqpos
    (by norm_num) (by norm_num) le_rfl hℓ
  have hβ := mul_one_sub_two_mul_le_of_ge (by norm_num) hq0
  have hN : Real.exp (-(9 / 20 * (1 - 2 * (9 / 20)) * 20.7867) - 1 / 2)
      ≤ Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) := Real.exp_le_exp.2 (by linarith)
  have e1 : Real.exp (Real.log (3 / 5)
      + cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20))
      - 9 / 20 * (1 - 2 * (9 / 20)) * 20.7867 - 1 / 2)
      = 3 / 5 * Real.exp (cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20)))
        * Real.exp (-(9 / 20 * (1 - 2 * (9 / 20)) * 20.7867) - 1 / 2) := by
    rw [show Real.log (3 / 5) + cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20))
        - 9 / 20 * (1 - 2 * (9 / 20)) * 20.7867 - 1 / 2
        = Real.log (3 / 5) + cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20))
          + (-(9 / 20 * (1 - 2 * (9 / 20)) * 20.7867) - 1 / 2) by ring,
      Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
  have e2 : mainB2 q = 3 / 5 * (cRed q * (2 : ℝ) ^ (2 * q - 1)
      * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
      * ((0.17784 : ℝ) ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
        * ((1 - Real.exp (-100)) * 0.31689) ^ (2 - q) * (6482 : ℝ) ^ (-(1 - q))))
      * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) := by
    rw [mainB2, perScaleLow2]
    ring
  have hX0 := le_trans (Real.exp_pos _).le hcore
  have hmain : Real.exp lam ≤ mainB2 q := by
    calc Real.exp lam ≤ _ := Real.exp_le_exp.2 hlam
      _ = _ := e1
      _ ≤ _ := by
        rw [e2]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hcore (by norm_num)) hN
          (Real.exp_pos _).le (mul_nonneg (by norm_num) hX0)
  have herr := errB_le_exp_cellLogErr (a := 9 / 20) (u := 2700) hq0 hq1.le le_rfl
    (le_max_of_le_right (by norm_num))
  have hsub : 400 * cJ q * Real.exp (-32) ≤ 216 * Real.exp (-32) :=
    mul_le_mul_of_nonneg_right (four_hundred_mul_cJ_le hqpos.le hq1.le)
      (Real.exp_pos _).le
  unfold PhiB2Ext
  linarith

/-- **B1 for `Y`**: `PhiB1Ext(q) ≥ 10⁻¹⁰` for `0 < q ≤ 9/20`, on the weighted sum's 19 cells
(`RMF.finalCells_spec`; certified margin `≥ ×11.97`, as `RMF.PhiB1_ge`). -/
theorem PhiB1Ext_ge {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 9 / 20) : 1 / 10 ^ 10 ≤ PhiB1Ext q := by
  obtain ⟨a, b, c, β, ℓ, u, lam, haq, hqb, hb, hc0, hc1, hc, hβ, hℓ, hu, hlam, hcert⟩ :=
    finalCells_spec.1 q hq0 hq
  exact PhiB1Ext_ge_of_cell haq hqb hb hq0 hc0 hc1 hc hβ hℓ hu hlam hcert

/-- **B2 for `Y`**: `PhiB2Ext(q) ≥ 10⁻¹⁰` for `9/20 ≤ q < ½`, on the weighted sum's certificate
(certified margin `×119`, as `RMF.PhiB2_ge`). -/
theorem PhiB2Ext_ge {q : ℝ} (hq0 : 9 / 20 ≤ q) (hq1 : q < 1 / 2) : 1 / 10 ^ 10 ≤ PhiB2Ext q := by
  obtain ⟨lam, hlam, hcert⟩ := finalCells_spec.2.1
  exact PhiB2Ext_ge_of_cert hlam hcert hq0 hq1

/-! ### Combining the analysis and the arithmetic -/

/-- **Below `½`, the three terms combined, with the subtracted term's constant `K`**:
`RMF.belowHalf_combine` with `K` for `216`: the reduction
`cRed·L^{-q}I - cJ·e·L^{-q}I_J - cE·L^{-q} ≤ E`, the main term `A·S ≤ L^{-q}I`, the subtracted
term `I_J ≤ K·L^q·m·g` and the error `cE·L^{-q} ≤ errB·m·g` give
`cRed·A·S - (K·cJ·e + errB)·m·g ≤ E`. -/
lemma belowHalf_combine_K {E Im Is S cR cJ' cE A Lm Lp e m g eB K : ℝ}
    (hred : cR * (Lm * Im) - cJ' * e * Lm * Is - cE * Lm ≤ E)
    (hm5 : A * S ≤ Lm * Im) (hcR : 0 ≤ cR)
    (hR3 : Is ≤ K * Lp * m * g) (hLL : Lm * Lp = 1) (hcJ : 0 ≤ cJ' * e * Lm)
    (hE : cE * Lm ≤ eB * (m * g)) :
    cR * (A * S) - (K * cJ' * e + eB) * (m * g) ≤ E := by
  have h1 := mul_le_mul_of_nonneg_left hm5 hcR
  have h2 := mul_le_mul_of_nonneg_left hR3 hcJ
  have h3 : cJ' * e * Lm * (K * Lp * m * g) = K * cJ' * e * (m * g) := by
    calc cJ' * e * Lm * (K * Lp * m * g) = K * cJ' * e * (m * g) * (Lm * Lp) := by ring
      _ = K * cJ' * e * (m * g) := by rw [hLL, mul_one]
  linarith

/-! ### The reduction with the main term, at the damping level -/

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **Below `½` for `Y`: the reduction at the tilt `V = 32/q`, the main term and the subtracted
term.**  `RMF.exists_level_belowHalf` with `E|Y(x)|^{2q}` for `E|S(x)|^{2q}` and the subtracted
constant `400` for `216`: Y's reduction with the window covering of
`RMF.isWindowCovering_of_classical` and the error constant `cErrD ≤ cErr`, Y's main term
(`RMF.le_rpow_mul_integral_rpow_lineDivSq_explicit`) and Y's subtracted term
(`RMF.integral_rpow_lineDivSq_le_subtracted_belowHalf`, `V = 32/q ≥ 64`). -/
theorem exists_level_belowHalf_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 0 < q) (hq : q < 1 / 2)
    (hqΛ : 37 / 2 ≤ q * Real.log (Real.log x)) :
    ∃ T : ℕ, 2021 ≤ T ∧ (T : ℝ) ≤ Real.log (Real.log x)
      ∧ Real.log q + Real.log (Real.log x) - 21 / 2 < T
      ∧ ∀ K : Finset ℕ, (∀ k ∈ K, 20 < k ∧ k + 2000 ≤ T) → (∀ k ∈ K, k - 20 ≤ c3Kmax q) →
        cRed q * (2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
            * ∑ k ∈ K, perScaleConst q (k - 20)
              * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
              * ((T - k : ℕ) : ℝ) ^ (-(q / 2)))
          - (400 * cJ q * Real.exp (-32) + errB q)
            * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹ * Real.log (Real.log x) ^ (-(q / 2)))
        ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, -, -⟩ := loglog_facts_of_six_thousand hx
  obtain ⟨-, -, -, hx20, hwin⟩ :=
    loglog_facts_of_low (le_trans (Real.exp_le_exp.2 (Real.exp_le_exp.2 (by norm_num))) hx)
  have hx300 : Real.exp 300 ≤ x := le_trans (Real.exp_le_exp.2 (by norm_num)) hx20
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
  have hred := le_integral_rpow_normalisedSum_compMultExtension_of_windowCovering hX
    (V := 32 / q) (by positivity) hx300 hwin hlogV hq0 hq.le
  rw [div_mul_cancel₀ (32 : ℝ) hq0.ne'] at hred
  -- the main term at `σ = 2V/log x`
  have hyT := scaleCut_add_seven_le hx1 (T := T) (by linarith)
  have h64 : 64 ≤ 32 / q := by
    rw [le_div_iff₀ hq0]
    linarith
  have hσy : 16 ≤ 2 * (32 / q) / Real.log x * Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) :=
    le_trans (by linarith) (two_mul_le_mul_log_floor_add_one hx1 (by linarith))
  have hm5 := le_rpow_mul_integral_rpow_lineDivSq_explicit hX hσ hq0 hq.le (k₀ := 20)
    (y := ⌊x⌋₊ + 1) le_rfl hT1 hT2 hyT hK (fun k hk _ => hKq k hk) hL0
    (div_mul_cancel₀ _ hL0.ne') hσy
  -- the subtracted term and the error term
  have hR3 := integral_rpow_lineDivSq_le_subtracted_belowHalf hX hx1 hΛ (V := 32 / q)
    (by linarith) hq0 hq
  have hE := le_trans
    (mul_le_mul_of_nonneg_right (cErrD_le_cErr hq0.le) (Real.rpow_nonneg hL0.le _))
    (cErr_mul_rpow_le_errB hq0 hq hL0 hΛ hqΛ)
  have hLL : Real.log x ^ (-q) * Real.log x ^ q = 1 := by
    rw [← Real.rpow_add hL0, neg_add_cancel, Real.rpow_zero]
  exact belowHalf_combine_K hred hm5 (cRed_pos q).le hR3 hLL
    (mul_nonneg (mul_nonneg (cJ_pos q).le (Real.exp_pos _).le) (Real.rpow_nonneg hL0.le _)) hE

/-! ### The regimes -/

/-- **F for `Y`**: for `x ≥ exp(e^{6000})`, `q > 0` and `qΛ ≤ 37/2`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`: Y's floor
(`RMF.le_integral_rpow_normalisedSum_compMultExtension_floor_classical`) and
`RMF.floor_regime_arith`. -/
theorem le_integral_rpow_floorRegime_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 0 < q)
    (hqΛ : q * Real.log (Real.log x) ≤ 37 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, -, -⟩ := loglog_facts_of_six_thousand hx
  obtain ⟨-, -, -, hx20, -⟩ :=
    loglog_facts_of_low (le_trans (Real.exp_le_exp.2 (Real.exp_le_exp.2 (by norm_num))) hx)
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hq12 : q ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hΛ hq0.le
    linarith
  exact le_trans (floor_regime_arith hq0 hL0 hΛ hqΛ)
    (le_integral_rpow_normalisedSum_compMultExtension_floor_classical hX hx20 hq0 hq12)

/-- **B1 for `Y`**: for `x ≥ exp(e^{6000})`, `0 < q ≤ 9/20` and `qΛ > 37/2`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`: `RMF.exists_level_belowHalf_ext` on the one scale
`k = 21`, `RMF.mainB1_mul_le_sum` and `RMF.PhiB1Ext_ge`. -/
theorem le_integral_rpow_mainB1Regime_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 0 < q) (hq : q ≤ 9 / 20)
    (hqΛ : 37 / 2 < q * Real.log (Real.log x)) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, -, -, -⟩ := loglog_facts_of_six_thousand hx
  obtain ⟨T, hT, hTΛ, -, H⟩ := exists_level_belowHalf_ext hX hx hq0 (by linarith) hqΛ.le
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
    (by unfold PhiB1Ext; ring) (PhiB1Ext_ge hq0 hq)
    (mul_nonneg (le_min (by linarith) (inv_nonneg.2 (by linarith)))
      (Real.rpow_nonneg (by linarith) _))

/-- **B2 for `Y`**: for `x ≥ exp(e^{6000})` and `9/20 ≤ q < ½`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`: `RMF.exists_level_belowHalf_ext` on the scales
`21 ≤ k ≤ 20 + min(K_max(q), T - 2020)`, `RMF.mainB2_mul_le_sum` and `RMF.PhiB2Ext_ge`. -/
theorem le_integral_rpow_mainB2Regime_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 9 / 20 ≤ q) (hq : q < 1 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, -, -, -⟩ := loglog_facts_of_six_thousand hx
  have hqΛ : 37 / 2 ≤ q * Real.log (Real.log x) := by
    have := mul_le_mul hq0 hΛ (by norm_num) (by linarith)
    linarith
  obtain ⟨T, hT, hTΛ, hTl, H⟩ := exists_level_belowHalf_ext hX hx (by linarith) hq hqΛ
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
    (by unfold PhiB2Ext; ring) (PhiB2Ext_ge hq0 hq)
    (mul_nonneg (le_min (by linarith) (inv_nonneg.2 (by linarith)))
      (Real.rpow_nonneg (by linarith) _))

/-- **Below `½` for `Y`, `log log x ≥ 6000`**: for a Rademacher family, `x ≥ exp(e^{6000})` and
`0 < q < ½`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`: F for `qΛ ≤ 37/2`, else B1 for
`q ≤ 9/20` and B2 above (the weighted sum's case split in
`RMF.weighted_rademacher_moments_lower_uniform_explicit`). -/
theorem le_integral_rpow_belowHalf_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 6000) ≤ x) (hq0 : 0 < q) (hq : q < 1 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  rcases le_or_gt (q * Real.log (Real.log x)) (37 / 2) with h | h
  · exact le_integral_rpow_floorRegime_ext hX hx hq0 h
  · rcases le_or_gt q (9 / 20) with h' | h'
    · exact le_integral_rpow_mainB1Regime_ext hX hx hq0 h' h
    · exact le_integral_rpow_mainB2Regime_ext hX hx h'.le hq

/-! ### From `log log x ≥ 67.17` on -/

/-- **Below `½` for `Y` with `c = 10⁻¹⁰`, for `log log x ≥ 67.17`**: for every Rademacher `X`,
`x ≥ exp(e^{67.17})` and `0 < q < ½`,
`10⁻¹⁰min{log log x, 1/(1-2q)}(log log x)^{-q/2} ≤ E|Y(x)|^{2q}`: the low range up to `2100`
(`RMF.le_integral_rpow_belowHalfLow_ext`), the mid range up to `6000`
(`RMF.le_integral_rpow_belowHalfMid_ext`) and `RMF.le_integral_rpow_belowHalf_ext` above. -/
theorem le_integral_rpow_normalisedSum_compMultExtension_large_explicit
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp (Real.exp 67.17) ≤ x)
    (hq0 : 0 < q) (hq : q < 1 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.2 (Real.exp_pos _)) hx
  rcases le_or_gt (Real.log (Real.log x)) 2100 with h2 | h2
  · exact le_integral_rpow_belowHalfLow_ext hX hx h2 hq0 hq
  rcases le_or_gt (Real.log (Real.log x)) 6000 with h6 | h6
  · exact le_integral_rpow_belowHalfMid_ext hX (exp_exp_le_of_le_loglog hx1 h2.le) h6 hq0 hq
  · exact le_integral_rpow_belowHalf_ext hX (exp_exp_le_of_le_loglog hx1 h6.le) hq0 hq

end RMF
