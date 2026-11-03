/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.Extended.MainTerm
import RMF.UniformLower.Extended.Subtracted
import RMF.UniformLower.FinalRegimesLow

/-!
# The extended sum below `½` in the low range `67.17 ≤ log log x ≤ 2100`

The twin of `RMF/UniformLower/FinalRegimesLow.lean` for `Y(x) = x^{-1/2}∑_{n≤x} X^e(n)`
(`RMF.le_integral_rpow_belowHalfLow_ext`).  For a Rademacher family, `x ≥ exp(e^{67.17})` with
`Λ = log log x ≤ 2100` and `0 < q < ½`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`.

* The analytic input `RMF.exists_level_belowHalfLow_ext` has the weighted sum's conclusion
  verbatim, from Y's reduction, main term and Jensen bound, which carry the weighted sum's
  constants; so F, B1 and B2 use the weighted sum's arithmetic and certificates unchanged.
* F with Y's floor from the classical count
  (`RMF.le_integral_rpow_normalisedSum_compMultExtension_floor_classical`), the same form.
* NH: Y's Hölder bound `½(1 + log x)^{-(1-2q)}` keeps a factor `½` (`E|Y| ≥ ⌊√x⌋/√x`, not `1`),
  paid by the numeral `RMF.nh_num_low_half` (margin `×2.19`).
-/

open MeasureTheory

namespace RMF

/-! ### Arithmetic -/

/-- `2V ≤ (2V/log x)·log(⌊x⌋ + 1)` for `x > 1` and `V ≥ 0`, as `log x ≤ log(⌊x⌋ + 1)`: the
hypothesis `16 ≤ σ log y` of Y's main term at the tilt `σ = 2V/log x`, `y = ⌊x⌋ + 1`. -/
lemma two_mul_le_mul_log_floor_add_one {x V : ℝ} (hx : 1 < x) (hV : 0 ≤ V) :
    2 * V ≤ 2 * V / Real.log x * Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have h1 : Real.log x ≤ Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) :=
    Real.log_le_log hx0 (by push_cast; exact (Nat.lt_floor_add_one x).le)
  calc 2 * V = 2 * V / Real.log x * Real.log x := (div_mul_cancel₀ _ hL.ne').symm
    _ ≤ 2 * V / Real.log x * Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg (by linarith) hL.le)

/-- **NH's numeral for `Y`**: `2·10⁻¹⁰·2100^{3/4 + 67/1000}e^{18} ≤ 18·2^{-268/1000}`,
`RMF.nh_num_low` with the factor `2` of Y's Hölder bound (margin `×2.19`). -/
theorem nh_num_low_half :
    (2 : ℝ) / 10 ^ 10 * Real.exp ((3 / 4 + 67 / 1000) * Real.log 2100) * Real.exp 18
      ≤ 18 * Real.exp (-(268 / 1000 * Real.log 2)) := by
  interval_decide (trust := kernel)

/-- **NH's arithmetic for `Y` in the low range**: `RMF.nearHalf_arith_low` against
`½(1 + L)^{-(1-2q)}`, for `L > 0` with `67.17 ≤ Λ = log L ≤ 2100`, `q < ½` and
`(1-2q)Λ ≤ 18`: its proof with `2·10⁻¹⁰` for `10⁻¹⁰` and `RMF.nh_num_low_half`. -/
lemma nearHalf_arith_low_half {q L : ℝ} (hL : 0 < L) (hΛ1 : 67.17 ≤ Real.log L)
    (hΛ2 : Real.log L ≤ 2100) (hq : q < 1 / 2) (hu : (1 - 2 * q) * Real.log L ≤ 18) :
    1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      ≤ 1 / 2 * (1 + L) ^ (-(1 - 2 * q)) := by
  suffices h : 2 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      ≤ (1 + L) ^ (-(1 - 2 * q)) by linarith
  have hΛ0 : 0 < Real.log L := by linarith
  have hδ0 : 0 < 1 - 2 * q := by linarith
  have hδ1 : 1 - 2 * q ≤ 268 / 1000 := by
    have := mul_le_mul_of_nonneg_left hΛ1 hδ0.le
    linarith
  have hL1 : 1 ≤ L := by
    rw [← Real.exp_log hL]
    exact Real.one_le_exp (by linarith)
  have hg0 : 0 ≤ Real.log L ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  -- `Λ·Λ^{-q/2} ≤ 2100^{3/4+67/1000}`
  have hA : Real.log L * Real.log L ^ (-(q / 2))
      ≤ Real.exp ((3 / 4 + 67 / 1000) * Real.log 2100) := by
    rw [show Real.log L * Real.log L ^ (-(q / 2)) = Real.log L ^ (1 + -(q / 2)) by
        rw [Real.rpow_add hΛ0, Real.rpow_one]]
    calc Real.log L ^ (1 + -(q / 2)) ≤ (2100 : ℝ) ^ (1 + -(q / 2)) :=
          Real.rpow_le_rpow hΛ0.le hΛ2 (by linarith)
      _ ≤ (2100 : ℝ) ^ (3 / 4 + 67 / 1000 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = Real.exp ((3 / 4 + 67 / 1000) * Real.log 2100) := by
          rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  -- `(1 + L)^{-δ} ≥ 2^{-0.268}e^{-u}`
  have hlow : Real.exp (-(268 / 1000 * Real.log 2)) * Real.exp (-((1 - 2 * q) * Real.log L))
      ≤ (1 + L) ^ (-(1 - 2 * q)) := by
    have h1 : (2 * L) ^ (-(1 - 2 * q)) ≤ (1 + L) ^ (-(1 - 2 * q)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have h2 : (2 * L) ^ (-(1 - 2 * q))
        = Real.exp (-((1 - 2 * q) * Real.log 2)) * Real.exp (-((1 - 2 * q) * Real.log L)) := by
      rw [Real.rpow_def_of_pos (by linarith), Real.log_mul two_ne_zero hL.ne', ← Real.exp_add]
      congr 1
      ring
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h3 : Real.exp (-(268 / 1000 * Real.log 2))
        ≤ Real.exp (-((1 - 2 * q) * Real.log 2)) := by
      have := mul_le_mul_of_nonneg_right hδ1 hl2
      exact Real.exp_le_exp.2 (by linarith)
    calc _ ≤ Real.exp (-((1 - 2 * q) * Real.log 2)) * Real.exp (-((1 - 2 * q) * Real.log L)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = (2 * L) ^ (-(1 - 2 * q)) := h2.symm
      _ ≤ _ := h1
  -- `10⁻¹⁰min{Λ, 1/δ}Λ^{-q/2}e^u ≤ 2^{-0.268}`
  have hnum := nh_num_low_half
  have hm0 : 0 ≤ min (Real.log L) (1 - 2 * q)⁻¹ := le_min hΛ0.le (inv_nonneg.2 hδ0.le)
  have hkey : 2 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
        * Real.exp ((1 - 2 * q) * Real.log L)
      ≤ Real.exp (-(268 / 1000 * Real.log 2)) := by
    have hA18 : 2 / 10 ^ 10 * (Real.log L * Real.log L ^ (-(q / 2))) * Real.exp 18
        ≤ 18 * Real.exp (-(268 / 1000 * Real.log 2)) := by
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
        _ ≤ Real.exp (-(268 / 1000 * Real.log 2)) := by
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
  have h := mul_le_mul_of_nonneg_right hkey (Real.exp_pos (-((1 - 2 * q) * Real.log L))).le
  calc 2 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      = 2 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
        * Real.exp ((1 - 2 * q) * Real.log L) * Real.exp (-((1 - 2 * q) * Real.log L)) := by
        rw [mul_assoc _ (Real.exp _), mul_comm (Real.exp _) (Real.exp _), hE, mul_one]
    _ ≤ Real.exp (-(268 / 1000 * Real.log 2)) * Real.exp (-((1 - 2 * q) * Real.log L)) := h
    _ ≤ _ := hlow

/-! ### The reduction with the main term, at the damping level -/

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **Y's floor from the classical count**: for a Rademacher family, `x ≥ exp(10²⁰)` and
`0 < q ≤ ½`, `2^{-(1-2q)}3^{-(1-q)}(0.49/log x)^q ≤ E|Y(x)|^{2q}`, the weighted sum's floor in the
same form (`RMF.le_integral_rpow_normalisedSum_compMultExtension_floor_of_le_card`,
`RMF.le_card_largePrimeSet_half_div_classical`). -/
theorem le_integral_rpow_normalisedSum_compMultExtension_floor_classical
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp (10 ^ 20) ≤ x) (hq0 : 0 < q)
    (hq12 : q ≤ 1 / 2) :
    (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (49 / (100 * Real.log x)) ^ q
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 10 ^ 20 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_trans (by norm_num) (Real.add_one_le_exp (10 ^ 20))) hx
  exact le_integral_rpow_normalisedSum_compMultExtension_floor_of_le_card hX hx4 hq0 hq12
    (div_nonneg (by norm_num) (mul_nonneg (by norm_num) hL0.le))
    (le_card_largePrimeSet_half_div_classical hx)

/-- **Below `½` in the low range, for `Y`: the reduction at the tilt `V′ = Λ + 24/q`, the main
term and the subtracted term by Jensen.**  `RMF.exists_level_belowHalfLow` with `E|Y(x)|^{2q}`
for `E|S(x)|^{2q}`, its conclusion verbatim: Y's reduction
(`RMF.le_integral_rpow_normalisedSum_compMultExtension_of_windowCovering`, the window covering
of `RMF.isWindowCovering_of_classical`), main term
(`RMF.le_rpow_mul_integral_rpow_lineDivSq_explicit_short`, with `σ log(⌊x⌋ + 1) ≥ 2V′ ≥ 16`) and
Jensen bound (`RMF.integral_rpow_lineDivSq_le_jensen`), all with the weighted sum's numbers. -/
theorem exists_level_belowHalfLow_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 67.17) ≤ x) (hq0 : 0 < q) (hq : q < 1 / 2)
    (hδΛ : 1 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hy : 56 ≤ Real.log (Real.log x) - Real.log (400 * (Real.log (Real.log x) + 24 / q))) :
    ∃ T : ℕ, (T : ℝ) ≤ Real.log (Real.log x)
      ∧ Real.log (Real.log x) - Real.log (400 * (Real.log (Real.log x) + 24 / q)) - 1 < T
      ∧ ∀ K : Finset ℕ, (∀ k ∈ K, 20 < k ∧ k + 35 ≤ T) → (∀ k ∈ K, k - 20 ≤ c3Kmax q) →
        cRed q * (2 ^ (2 * q - 1)
            * (Real.exp (-0.592) / 2 / (2 * (Real.log (Real.log x) + 24 / q))) ^ q
            * ∑ k ∈ K, perScaleConstShort q (k - 20) (T - k)
              * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
              * ((T - k : ℕ) : ℝ) ^ (-(q / 2)))
          - ((1 - 2 * q) * cJ q * Real.exp (-24) + errBLow q (Real.log (Real.log x)))
            * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹ * Real.log (Real.log x) ^ (-(q / 2)))
        ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, hx100, hx20, hwin⟩ := loglog_facts_of_low hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.2 (Real.exp_pos _)) hx
  have hx300 : Real.exp 300 ≤ x := le_trans (Real.exp_le_exp.2 (by norm_num)) hx20
  have h24 : 0 < 24 / q := div_pos (by norm_num) hq0
  have hV0 : 0 < Real.log (Real.log x) + 24 / q := by linarith
  have h400 : 0 < 400 * (Real.log (Real.log x) + 24 / q) := by linarith
  -- `400V′ ≤ log x`, from `y ≥ 56`
  have h400L : 400 * (Real.log (Real.log x) + 24 / q) ≤ Real.log x :=
    (Real.log_le_log_iff h400 hL0).1 (by linarith)
  -- the tilt `σ = 2V′/log x` and its damping level
  have hσ : 0 < 2 * (Real.log (Real.log x) + 24 / q) / Real.log x := div_pos (by linarith) hL0
  have hσ1 : 2 * (Real.log (Real.log x) + 24 / q) / Real.log x ≤ 1 / 200 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    linarith
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := exists_damping_level hσ hσ1
  have hℓ : Real.log (1 / (200 * (2 * (Real.log (Real.log x) + 24 / q) / Real.log x)))
      = Real.log (Real.log x) - Real.log (400 * (Real.log (Real.log x) + 24 / q)) := by
    rw [show 200 * (2 * (Real.log (Real.log x) + 24 / q) / Real.log x)
        = 400 * (Real.log (Real.log x) + 24 / q) / Real.log x by ring, one_div_div,
      Real.log_div hL0.ne' h400.ne']
  rw [hℓ] at hT3 hT4
  have hl7 : 7 ≤ Real.log (400 * (Real.log (Real.log x) + 24 / q)) := by
    rw [Real.le_log_iff_exp_le h400]
    have : Real.exp 7 ≤ 1100 := by interval_decide (trust := kernel)
    linarith
  have hyT := scaleCut_add_seven_le hx1 (T := T) (by linarith)
  refine ⟨T, by linarith, hT3, fun K hK hKq => ?_⟩
  -- the reduction at `V′`
  have hlogV : 3 * (Real.log (Real.log x) + 24 / q) + 3 ≤ Real.log x := by linarith
  have hred := le_integral_rpow_normalisedSum_compMultExtension_of_windowCovering hX
    (V := Real.log (Real.log x) + 24 / q) hV0 hx300 hwin hlogV hq0 hq.le
  -- the main term at `σ = 2V′/log x`
  have hσy : 16 ≤ 2 * (Real.log (Real.log x) + 24 / q) / Real.log x
      * Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) :=
    le_trans (by linarith) (two_mul_le_mul_log_floor_add_one hx1 hV0.le)
  have hm5 := le_rpow_mul_integral_rpow_lineDivSq_explicit_short hX hσ hq0 hq.le
    (k₀ := 20) (y := ⌊x⌋₊ + 1) le_rfl hT1 hT2 hyT hK (fun k hk _ => hKq k hk) hL0
    (div_mul_cancel₀ _ hL0.ne') hσy
  -- the subtracted term by Jensen, and the error term
  have hJ := integral_rpow_lineDivSq_le_jensen hX hx100 hV0 hq0.le (by linarith)
  have hsub := jensen_term_le_low hq0 hq hL0 hΛ hδΛ
  have hE := cErrD_mul_rpow_le_errBLow hq hL0 (by linarith) hδΛ
  exact belowHalfLow_combine hred hm5 (cRed_pos q).le hJ (cJ_pos q).le
    (mul_nonneg (mul_nonneg (cJ_pos q).le (Real.exp_pos _).le) (Real.rpow_nonneg hL0.le _)) hsub hE

/-! ### The regimes -/

/-- **F for `Y` in the low range**: for `x ≥ exp(e^{67.17})`, `0 < q < ½` and
`PhiFLow(q, Λ) ≥ 10⁻¹⁰`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`: Y's floor
(`RMF.le_integral_rpow_normalisedSum_compMultExtension_floor_classical`) and
`RMF.floor_regime_arith_low`. -/
theorem le_integral_rpow_floorRegimeLow_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 67.17) ≤ x) (hq0 : 0 < q) (hq : q < 1 / 2)
    (hF : 1 / 10 ^ 10 ≤ PhiFLow q (Real.log (Real.log x))) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, -, hx20, -⟩ := loglog_facts_of_low hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  exact le_trans (floor_regime_arith_low hq hL0 (by linarith) hF)
    (le_integral_rpow_normalisedSum_compMultExtension_floor_classical hX hx20 hq0 hq.le)

/-- **B1 for `Y` in the low range**: for `x ≥ exp(e^{67.17})`, `0 < q ≤ 9/20` and a rung
`r₀ ≥ 35` with `r₀ + 21 ≤ Λ - log(400(Λ + 24/q))` and `PhiB1Low(q, Λ, r₀) ≥ 10⁻¹⁰`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`: `RMF.exists_level_belowHalfLow_ext` on the one
scale `k = 21` and `RMF.mainB1Low_mul_le_sum`, as for the weighted sum. -/
theorem le_integral_rpow_mainB1RegimeLow_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 67.17) ≤ x) (hq0 : 0 < q) (hq : q ≤ 9 / 20) {r₀ : ℕ}
    (hr₀ : 35 ≤ r₀)
    (hrung : (r₀ : ℝ) + 21
      ≤ Real.log (Real.log x) - Real.log (400 * (Real.log (Real.log x) + 24 / q)))
    (hB1 : 1 / 10 ^ 10 ≤ PhiB1Low q (Real.log (Real.log x)) r₀) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, -, -, -, -⟩ := loglog_facts_of_low hx
  have hr₀r : (35 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
  have hδΛ : 1 ≤ (1 - 2 * q) * Real.log (Real.log x) := by
    have := mul_le_mul (by linarith : (1 / 10 : ℝ) ≤ 1 - 2 * q) hΛ (by norm_num) (by linarith)
    linarith
  obtain ⟨T, hTΛ, hTl, H⟩ :=
    exists_level_belowHalfLow_ext hX hx hq0 (by linarith) hδΛ (by linarith)
  have hT : r₀ + 21 ≤ T := by
    have h : (r₀ : ℝ) + 21 < (T : ℝ) + 1 := by linarith
    have h' : r₀ + 21 < T + 1 := by exact_mod_cast h
    omega
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
  exact le_of_sub_mul_le h (mainB1Low_mul_le_sum hq0 (by linarith) hr₀ hT hTΛ)
    (by unfold PhiB1Low; ring) hB1
    (mul_nonneg (le_min (by linarith) (inv_nonneg.2 (by linarith)))
      (Real.rpow_nonneg (by linarith) _))

/-- **B2 for `Y` in the low range**: for `x ≥ exp(e^{67.17})` with `Λ ≤ 2100`, `9/20 ≤ q < ½`
and `(1-2q)Λ ≥ 18`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`:
`RMF.exists_level_belowHalfLow_ext` on the scales `21 ≤ k ≤ 20 + min(K_max(q), T - 55)`,
`RMF.mainB2Low_mul_le_sum` and `RMF.PhiB2Low_ge`, as for the weighted sum. -/
theorem le_integral_rpow_mainB2RegimeLow_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 67.17) ≤ x) (hΛ2 : Real.log (Real.log x) ≤ 2100)
    (hq0 : 9 / 20 ≤ q) (hq : q < 1 / 2) (hu : 18 ≤ (1 - 2 * q) * Real.log (Real.log x)) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, -, -, -, -⟩ := loglog_facts_of_low hx
  have hΛ180 : 180 ≤ Real.log (Real.log x) := by
    have := mul_le_mul_of_nonneg_right (by linarith : 1 - 2 * q ≤ 1 / 10)
      (by linarith : (0 : ℝ) ≤ Real.log (Real.log x))
    linarith
  have hl14 := log_four_hundred_mul_le_fourteen hq0 (by linarith) hΛ2
  obtain ⟨T, hTΛ, hTl, H⟩ :=
    exists_level_belowHalfLow_ext hX hx (by linarith) hq (by linarith) (by linarith)
  have hT15 : Real.log (Real.log x) - 15 < T := by linarith
  have hT55 : 55 ≤ T := by
    have : (55 : ℝ) ≤ T := by linarith
    exact_mod_cast this
  have h := H (Finset.Icc 21 (20 + min (c3Kmax q) (T - 55)))
    (fun k hk => by
      rw [Finset.mem_Icc] at hk
      have := min_le_right (c3Kmax q) (T - 55)
      exact ⟨by omega, by omega⟩)
    (fun k hk => by
      rw [Finset.mem_Icc] at hk
      have := min_le_left (c3Kmax q) (T - 55)
      omega)
  exact le_of_sub_mul_le h (mainB2Low_mul_le_sum hq0 hq hu hTΛ hT15)
    (by unfold PhiB2Low; ring) (PhiB2Low_ge hq0 hq hΛ2 hu)
    (mul_nonneg (le_min (by linarith) (inv_nonneg.2 (by linarith)))
      (Real.rpow_nonneg (by linarith) _))

/-- **NH for `Y` in the low range, near `½` by Hölder**: for `x ≥ exp(e^{67.17})` with
`Λ ≤ 2100`, `q < ½` and `(1-2q)Λ ≤ 18`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`:
`½(1 + log x)^{-(1-2q)} ≤ E|Y(x)|^{2q}`
(`RMF.le_integral_rpow_normalisedSum_compMultExtension_holder`; `q > 0` as `Λ ≥ 67.17`) and
`RMF.nearHalf_arith_low_half`. -/
theorem le_integral_rpow_nearHalfRegimeLow_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 67.17) ≤ x) (hΛ2 : Real.log (Real.log x) ≤ 2100) (hq : q < 1 / 2)
    (hu : (1 - 2 * q) * Real.log (Real.log x) ≤ 18) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, hx100, -, -⟩ := loglog_facts_of_low hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx9 : (9 : ℝ) ≤ x := le_trans (by linarith [Real.add_one_le_exp (100 : ℝ)]) hx100
  have hq0 : 0 < q := by
    have hb : 0 < 1 - 2 * q := by linarith
    have := mul_le_mul_of_nonneg_left hΛ hb.le
    linarith
  exact le_trans (nearHalf_arith_low_half hL0 hΛ hΛ2 hq hu)
    (le_integral_rpow_normalisedSum_compMultExtension_holder hX hx9 hq0 hq)

/-- **Below `½` for `Y` in the low range**: for a Rademacher family, `x ≥ exp(e^{67.17})`
with `log log x ≤ 2100` and `0 < q < ½`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|Y(x)|^{2q}`: for
`q ≤ 9/20`, F or B1 at the rung of `RMF.finalCellsLow_spec`; above, B2 for `(1-2q)Λ ≥ 18` and NH
otherwise.  `RMF.le_integral_rpow_belowHalfLow` with `Y` for `S`. -/
theorem le_integral_rpow_belowHalfLow_ext (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 67.17) ≤ x) (hΛ : Real.log (Real.log x) ≤ 2100) (hq0 : 0 < q)
    (hq : q < 1 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨hΛ0, -, -, -, -⟩ := loglog_facts_of_low hx
  rcases le_or_gt q (9 / 20) with h | h
  · rcases finalCellsLow_spec hq0 h hΛ0 hΛ with hF | ⟨r₀, hr₀, hrung, hB1⟩
    · exact le_integral_rpow_floorRegimeLow_ext hX hx hq0 hq hF
    · exact le_integral_rpow_mainB1RegimeLow_ext hX hx hq0 h hr₀ hrung hB1
  rcases le_or_gt 18 ((1 - 2 * q) * Real.log (Real.log x)) with h' | h'
  · exact le_integral_rpow_mainB2RegimeLow_ext hX hx hΛ h.le hq h'
  · exact le_integral_rpow_nearHalfRegimeLow_ext hX hx hΛ hq h'.le

end RMF
