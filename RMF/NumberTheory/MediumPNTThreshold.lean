/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.PNTPlus.MediumPNTExplicit

/-!
# The effective prime number theorem with an explicit threshold

PNT+'s `MediumPNT` argument, run at the constants named in `RMF/PNTPlus/MediumPNTExplicit.lean`,
gives `|ψ x - x| ≤ 10³⁹ x exp(-(1/200)(log x)^{1/10})` for all large `x`, but only as an
`∀ᶠ x in atTop`: its threshold is the intersection of thirteen eventually-facts.  Each of them is
elementary in `u = (log x)^{1/10}`, and `RMF.mediumPNT_threshold_facts` proves all of them past
one closed-form threshold `exp (RMF.mediumPNTL A σ₂ Tlb₄ Tlb₆ ε_main)`, `mediumPNTL = u₀¹⁰`,
where `a = A^{1/10}` and `u₀` is the largest of

* `log max(3, Tlb₄, Tlb₆)/a + 1`, for the three conditions on `T = e^{a u}`;
* `(a/(1-σ₂))^{1/9} + 1`, for `σ₂ < σ₁` and for the `I₅` term;
* `2|log ε_main|/a + 1`, for `ε < ε_main`;
* `(80/a) log(40/a) + 2`, which gives `log x ≤ e^{(a/4)u}` through `log u ≤ (a/40)u`
  (`RMF.pow_ten_le_exp_div_four_mul`).

`RMF.MediumPNT_bound_explicit` is the bound past that threshold, with the thirteen eventually-facts
supplied by `RMF.mediumPNT_threshold_facts`; `RMF.MediumPNTConstantExplicit` is the numeral form
above for every `x ≥ exp RMF.mediumPNTThresholdL`.
-/

namespace RMF

section MediumPNTThreshold

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)

open scoped Chebyshev

local notation "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

open ComplexConjugate

open MeasureTheory

/-- `log u ≤ (a/40)u` once `u ≥ (80/a) log(40/a)`, for `0 < a ≤ 1`: at `u₁ = (80/a)L₀`,
`L₀ = log(40/a) ≥ log 40`, `log u₁ = log 2 + log L₀ + L₀ ≤ 2L₀ = (a/40)u₁`, and past `u₁ ≥ 40/a`
the slope `1/u` of `log` is below `a/40`. -/
lemma log_le_div_forty_mul {a u : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hu : 80 / a * Real.log (40 / a) ≤ u) : Real.log u ≤ a / 40 * u := by
  set L₀ : ℝ := Real.log (40 / a) with hL₀def
  have h40a : (40 : ℝ) ≤ 40 / a := by
    rw [le_div_iff₀ ha0]
    linarith
  have hlog40 : (3 : ℝ) ≤ Real.log 40 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h := Real.exp_one_lt_d9
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    have : Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le h.le 3
    linarith [show (2.7182818286 : ℝ) ^ 3 ≤ 40 by norm_num]
  have hL₀ : (3 : ℝ) ≤ L₀ := le_trans hlog40 (Real.log_le_log (by norm_num) h40a)
  have hL₀0 : (0 : ℝ) < L₀ := by linarith
  set u₁ : ℝ := 80 / a * L₀ with hu₁def
  have hu₁0 : 0 < u₁ := by positivity
  have hu0 : 0 < u := lt_of_lt_of_le hu₁0 hu
  -- `log u₁ ≤ (a/40)u₁`
  have hlogu₁ : Real.log u₁ = Real.log 2 + Real.log L₀ + L₀ := by
    have h1 : u₁ = 2 * L₀ * (40 / a) := by rw [hu₁def]; field_simp; ring
    rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hL₀0.ne']
  have hlogL₀ : Real.log L₀ ≤ L₀ - 1 := Real.log_le_sub_one_of_pos hL₀0
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hbu₁ : a / 40 * u₁ = 2 * L₀ := by rw [hu₁def]; field_simp; ring
  have hstep1 : Real.log u₁ ≤ a / 40 * u₁ := by linarith
  -- past `u₁`, the slope of `log` is below `a/40`
  have hu₁big : 40 / a ≤ u₁ := by
    rw [hu₁def]
    have : (40 : ℝ) / a * 1 ≤ 80 / a * L₀ := by
      rw [show (80 : ℝ) / a * L₀ = 40 / a * (2 * L₀) by ring]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hratio : Real.log (u / u₁) ≤ u / u₁ - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hdiff : u / u₁ - 1 ≤ a / 40 * (u - u₁) := by
    have h1 : u / u₁ - 1 = (u - u₁) / u₁ := by field_simp
    rw [h1, div_le_iff₀ hu₁0]
    have h2 : 0 ≤ u - u₁ := by linarith
    have h3 : 1 ≤ a / 40 * u₁ := by
      have := mul_le_mul_of_nonneg_left hu₁big (by positivity : (0 : ℝ) ≤ a / 40)
      rw [show a / 40 * (40 / a) = 1 by field_simp] at this
      exact this
    nlinarith
  have hsplit : Real.log u = Real.log u₁ + Real.log (u / u₁) := by
    rw [Real.log_div hu0.ne' hu₁0.ne']
    ring
  rw [hsplit]
  linarith

/-- The `L ≤ e^{(a/4)u}` step: `u¹⁰ ≤ e^{(a/4)u}`. -/
lemma pow_ten_le_exp_div_four_mul {a u : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hu : 80 / a * Real.log (40 / a) ≤ u) : u ^ 10 ≤ Real.exp (a / 4 * u) := by
  have hL₀ : 0 < Real.log (40 / a) := Real.log_pos (by rw [lt_div_iff₀ ha0]; linarith)
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  have h := log_le_div_forty_mul ha0 ha1 hu
  calc u ^ 10 = Real.exp (10 * Real.log u) := by
        rw [show (10 : ℝ) * Real.log u = Real.log (u ^ 10) by rw [Real.log_pow]; norm_num,
          Real.exp_log (by positivity)]
    _ ≤ Real.exp (a / 4 * u) := Real.exp_le_exp.2 (by linarith)

/-- The fourth term at `a ≥ 1/50`: `(80/a) log(40/a) + 2 ≤ 30802`. -/
lemma eighty_div_mul_log_le {a : ℝ} (ha : 1 / 50 ≤ a) (ha1 : a ≤ 1) :
    80 / a * Real.log (40 / a) + 2 ≤ 30802 := by
  have ha0 : 0 < a := by linarith
  have h1 : 80 / a ≤ 4000 := by rw [div_le_iff₀ ha0]; linarith
  have h2 : 40 / a ≤ 2000 := by rw [div_le_iff₀ ha0]; linarith
  have h40 : (40 : ℝ) ≤ 40 / a := by rw [le_div_iff₀ ha0]; linarith
  have hlog : Real.log (40 / a) ≤ Real.log 2000 := Real.log_le_log (by linarith) h2
  have hlog2000 : Real.log 2000 ≤ 7.7 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have h7' : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7182818283 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) h.le 7
    have h07 : (1.945 : ℝ) ≤ Real.exp 0.7 := by
      have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.7 by norm_num)
      linarith
    have hsplit : Real.exp 7.7 = Real.exp 7 * Real.exp 0.7 := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit, h7']
    have h2000 : (2000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 7 * 1.945 := by norm_num
    have hprod : (2.7182818283 : ℝ) ^ 7 * 1.945 ≤ Real.exp 1 ^ 7 * Real.exp 0.7 :=
      mul_le_mul hpow h07 (by norm_num) (by positivity)
    linarith
  have hL0 : 0 ≤ Real.log (40 / a) := Real.log_nonneg (by linarith)
  have : 80 / a * Real.log (40 / a) ≤ 4000 * 7.7 :=
    mul_le_mul h1 (le_trans hlog hlog2000) hL0 (by norm_num)
  linarith

/-- The threshold's `u₀`: the largest of the four lower bounds on `(log x)^{1/10}`. -/
noncomputable def mediumPNTU (A σ₂ Tlb₄ Tlb₆ ε_main : ℝ) : ℝ :=
  max (max 1 (Real.log (max 3 (max Tlb₄ Tlb₆)) / A ^ ((1 : ℝ) / 10) + 1))
    (max ((A ^ ((1 : ℝ) / 10) / (1 - σ₂)) ^ ((1 : ℝ) / 9) + 1)
      (max (2 * |Real.log ε_main| / A ^ ((1 : ℝ) / 10) + 1)
        (80 / A ^ ((1 : ℝ) / 10) * Real.log (40 / A ^ ((1 : ℝ) / 10)) + 2)))

/-- The threshold on `log x`, `u₀¹⁰`. -/
noncomputable def mediumPNTL (A σ₂ Tlb₄ Tlb₆ ε_main : ℝ) : ℝ :=
  mediumPNTU A σ₂ Tlb₄ Tlb₆ ε_main ^ 10

/-- **The thirteen eventually-facts of the effective PNT's proof, past one explicit threshold.** -/
theorem mediumPNT_threshold_facts {A σ₂ Tlb₄ Tlb₆ ε_main : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (hσ₂ : σ₂ < 1) (hε : 0 < ε_main) {X : ℝ}
    (hX : Real.exp (mediumPNTL A σ₂ Tlb₄ Tlb₆ ε_main) ≤ X) :
    3 < X ∧
    Real.exp (-(A ^ ((1 : ℝ) / 10) / 2) * Real.log X ^ ((1 : ℝ) / 10)) < 1 ∧
    2 < X * Real.exp (-(A ^ ((1 : ℝ) / 10) / 2) * Real.log X ^ ((1 : ℝ) / 10)) ∧
    3 < Real.exp (A ^ ((1 : ℝ) / 10) * Real.log X ^ ((1 : ℝ) / 10)) ∧
    Tlb₄ < Real.exp (A ^ ((1 : ℝ) / 10) * Real.log X ^ ((1 : ℝ) / 10)) ∧
    Tlb₆ < Real.exp (A ^ ((1 : ℝ) / 10) * Real.log X ^ ((1 : ℝ) / 10)) ∧
    σ₂ < 1 - A / (Real.log (Real.exp (A ^ ((1 : ℝ) / 10) * Real.log X ^ ((1 : ℝ) / 10)))) ^ 9 ∧
    Real.exp (-(A ^ ((1 : ℝ) / 10) / 2) * Real.log X ^ ((1 : ℝ) / 10)) < ε_main ∧
    1 ≤ Real.log X ∧
    Real.exp (-(A ^ ((1 : ℝ) / 10) / 2) * Real.log X ^ ((1 : ℝ) / 10)) * Real.log X
      ≤ Real.exp (-(A ^ ((1 : ℝ) / 10) / 4) * Real.log X ^ ((1 : ℝ) / 10)) ∧
    Real.log X / (Real.exp (-(A ^ ((1 : ℝ) / 10) / 2) * Real.log X ^ ((1 : ℝ) / 10))
        * Real.exp (A ^ ((1 : ℝ) / 10) * Real.log X ^ ((1 : ℝ) / 10)))
      ≤ Real.exp (-(A ^ ((1 : ℝ) / 10) / 4) * Real.log X ^ ((1 : ℝ) / 10)) ∧
    X ^ (-A / Real.log (Real.exp (A ^ ((1 : ℝ) / 10) * Real.log X ^ ((1 : ℝ) / 10))) ^ 9)
        / Real.exp (-(A ^ ((1 : ℝ) / 10) / 2) * Real.log X ^ ((1 : ℝ) / 10))
      ≤ Real.exp (-(A ^ ((1 : ℝ) / 10) / 4) * Real.log X ^ ((1 : ℝ) / 10)) ∧
    X ^ σ₂ / Real.exp (-(A ^ ((1 : ℝ) / 10) / 2) * Real.log X ^ ((1 : ℝ) / 10))
      ≤ X * Real.exp (-(A ^ ((1 : ℝ) / 10) / 4) * Real.log X ^ ((1 : ℝ) / 10)) := by
  have hexpL := Real.exp_pos (mediumPNTL A σ₂ Tlb₄ Tlb₆ ε_main)
  have hX0 : 0 < X := lt_of_lt_of_le hexpL hX
  have hLge : mediumPNTU A σ₂ Tlb₄ Tlb₆ ε_main ^ 10 ≤ Real.log X := by
    have h := Real.log_le_log hexpL hX
    rwa [Real.log_exp, mediumPNTL] at h
  have hA0 : 0 < A := hA.1
  set a := A ^ ((1 : ℝ) / 10) with ha_def
  set u₀ := mediumPNTU A σ₂ Tlb₄ Tlb₆ ε_main with hu₀_def
  have ha0 : 0 < a := Real.rpow_pos_of_pos hA0 _
  have ha1 : a ≤ 1 := Real.rpow_le_one hA0.le (by linarith [hA.2]) (by norm_num)
  have hA_eq : A = a ^ 10 := by
    rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul hA0.le]
    norm_num
  set M := max 3 (max Tlb₄ Tlb₆) with hM_def
  have hM3 : 3 ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  set ℓ := Real.log M with hℓ_def
  set r := (a / (1 - σ₂)) ^ ((1 : ℝ) / 9) with hr_def
  have h1σ : 0 < 1 - σ₂ := by linarith
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hr9 : r ^ 9 = a / (1 - σ₂) := by
    rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hu₀1 : 1 ≤ u₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hu₀ℓ : ℓ / a + 1 ≤ u₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hu₀σ : r + 1 ≤ u₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hu₀ε : 2 * |Real.log ε_main| / a + 1 ≤ u₀ :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hu₀a : 80 / a * Real.log (40 / a) + 2 ≤ u₀ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hlog40a : 0 ≤ Real.log (40 / a) :=
    Real.log_nonneg (by rw [le_div_iff₀ ha0]; linarith)
  have hu₀0 : 0 ≤ u₀ := by linarith
  set L := Real.log X with hL_def
  have hL0 : 0 ≤ L := le_trans (pow_nonneg hu₀0 10) hLge
  set u := L ^ ((1 : ℝ) / 10) with hu_def
  have hu₀u : u₀ ≤ u := by
    have h := Real.rpow_le_rpow (pow_nonneg hu₀0 10) hLge (by norm_num : (0 : ℝ) ≤ 1 / 10)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hu₀0, show ((10 : ℕ) : ℝ) * (1 / 10) = 1 by
      norm_num, Real.rpow_one] at h
  have hLu : u ^ 10 = L := by
    rw [hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hL0]
    norm_num
  have hu1 : 1 ≤ u := le_trans hu₀1 hu₀u
  have hu0 : 0 < u := by linarith
  have hu₀2 : 2 ≤ u₀ := by
    have : 0 ≤ 80 / a * Real.log (40 / a) := by positivity
    linarith
  have hL1024 : 1024 ≤ L := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hu₀2 10
    norm_num at h
    linarith
  have hL1 : 1 ≤ L := by linarith
  have huL : u ≤ L := by
    have h := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 : ℝ) / 10 ≤ 1)
    rwa [Real.rpow_one] at h
  have hXL : Real.exp L = X := Real.exp_log hX0
  -- `u⁹ > a/(1-σ₂)`, the condition behind `σ₂ < σ₁` and the `I₅` term
  have hu9 : a < (1 - σ₂) * u ^ 9 := by
    have hru : r < u := by linarith
    have h := pow_lt_pow_left₀ hru hr0 (by norm_num : (9 : ℕ) ≠ 0)
    rw [hr9, div_lt_iff₀ h1σ] at h
    linarith
  -- `a u > ℓ`
  have hau : ℓ < a * u := by
    have h := mul_le_mul_of_nonneg_left (le_trans hu₀ℓ hu₀u) ha0.le
    rw [mul_add, mul_div_cancel₀ _ ha0.ne', mul_one] at h
    linarith
  have hexpau : M < Real.exp (a * u) := by
    rw [← Real.exp_log hM0]
    exact Real.exp_lt_exp.2 hau
  -- `log x ≤ e^{(a/4)u}`
  have hcore : L ≤ Real.exp (a / 4 * u) := by
    rw [← hLu]
    exact pow_ten_le_exp_div_four_mul ha0 ha1 (by linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hL1, ?_, ?_, ?_, ?_⟩
  · have h := Real.add_one_le_exp L
    linarith
  · have := mul_pos ha0 hu0
    exact Real.exp_lt_one_iff.2 (by linarith)
  · rw [← hXL, ← Real.exp_add]
    have h := Real.add_one_le_exp (L + -(a / 2) * u)
    have hau' : a * u ≤ u := mul_le_of_le_one_left hu0.le ha1
    linarith
  · linarith
  · exact lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hexpau
  · exact lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hexpau
  · rw [Real.log_exp]
    have h1 : A / (a * u) ^ 9 = a / u ^ 9 := by
      rw [hA_eq, mul_pow]
      field_simp
    rw [h1]
    have h2 : a / u ^ 9 < 1 - σ₂ := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    linarith
  · have hle : -(a / 2) * u < Real.log ε_main := by
      have h1 : 2 * |Real.log ε_main| / a + 1 ≤ u := le_trans hu₀ε hu₀u
      have h2 := mul_le_mul_of_nonneg_left h1 ha0.le
      rw [mul_add, mul_div_cancel₀ _ ha0.ne', mul_one] at h2
      have h3 := neg_abs_le (Real.log ε_main)
      linarith
    rw [← Real.exp_log hε]
    exact Real.exp_lt_exp.2 hle
  · calc Real.exp (-(a / 2) * u) * L ≤ Real.exp (-(a / 2) * u) * Real.exp (a / 4 * u) :=
          mul_le_mul_of_nonneg_left hcore (Real.exp_pos _).le
      _ = Real.exp (-(a / 4) * u) := by
          rw [← Real.exp_add]
          congr 1
          ring
  · rw [← Real.exp_add, div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
    calc L ≤ Real.exp (a / 4 * u) := hcore
      _ = Real.exp (-(a / 4) * u + (-(a / 2) * u + a * u)) := by
          congr 1
          ring
  · rw [Real.log_exp, Real.rpow_def_of_pos hX0, ← Real.exp_sub]
    apply Real.exp_le_exp.2
    have hkey : L * (-A / (a * u) ^ 9) = -(a * u) := by
      rw [hA_eq, ← hLu]
      field_simp
    rw [hkey]
    have := mul_pos ha0 hu0
    linarith
  · have hXσ : X ^ σ₂ = Real.exp (L * σ₂) := Real.rpow_def_of_pos hX0 σ₂
    have hXe : X * Real.exp (-(a / 4) * u) = Real.exp (L + -(a / 4) * u) := by
      rw [Real.exp_add, hXL]
    rw [hXσ, hXe, ← Real.exp_sub]
    apply Real.exp_le_exp.2
    have h1 := mul_lt_mul_of_pos_right hu9 hu0
    have h2 : L = u ^ 9 * u := by rw [← hLu]; ring
    have := mul_pos ha0 hu0
    rw [h2]
    linarith

set_option maxHeartbeats 400000 in
-- Slow
/-- **The effective PNT bound with an explicit threshold**: given the holomorphy of `ζ'/ζ` and
bounds on the smoothing error, on the Mellin factor and on the nine contour pieces `I₁, …, I₉`,
`‖ψ x - x‖` is at most the sum of their constants times `x exp(-(A^{1/10}/4)(log x)^{1/10})`, for
every `x ≥ exp (RMF.mediumPNTL A σ₂ Tlb₄ Tlb₆ ε_main)`.  The thirteen eventually-facts of the
argument are supplied by `RMF.mediumPNT_threshold_facts`. -/
theorem MediumPNT_bound_explicit {A : ℝ} (A_in_Ioc : A ∈ Ioc 0 (1 / 2))
    (holo1 : ∀ (T : ℝ) (_ : 3 ≤ T), HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (((Icc ((1 : ℝ) - A / Real.log T ^ 9) 2) ×ℂ (Icc (-T) T)) \ {1}))
    {σ₂ : ℝ} (σ₂_pos : 0 < σ₂) (σ₂_lt_one : σ₂ < 1)
    (holo2 : HolomorphicOn (fun s ↦ ζ' s / ζ s) (uIcc σ₂ 2 ×ℂ uIcc (-3) 3 \ {1}))
    {c_close : ℝ} (c_close_pos : 0 < c_close)
    (h_close : ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
      ‖SmoothedChebyshev bumpNu ε X - ψ X‖ ≤ c_close * ε * X * Real.log X)
    {ε_main C_main : ℝ} (ε_main_pos : 0 < ε_main) (C_main_pos : 0 < C_main)
    (h_main : ∀ ε ∈ Ioo 0 ε_main, ‖𝓜 (fun x ↦ (Smooth1 bumpNu ε x : ℂ)) 1 - 1‖ ≤ C_main * ε)
    {c₁ : ℝ} (c₁pos : 0 < c₁)
    (hc₁ : ∀ (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (X : ℝ) (_ : 3 < X) {T : ℝ} (_ : 3 < T),
      ‖I₁ bumpNu ε X T‖ ≤ c₁ * X * Real.log X / (ε * T))
    {c₂ : ℝ} (c₂pos : 0 < c₂)
    (hc₂ : ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1) {T : ℝ} (_ : 3 < T),
      let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
      ‖I₂ bumpNu ε T X σ₁‖ ≤ c₂ * X / (ε * T))
    {c₃ : ℝ} (c₃pos : 0 < c₃)
    (hc₃ : ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1) {T : ℝ} (_ : 3 < T),
      let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
      ‖I₃ bumpNu ε T X σ₁‖ ≤ c₃ * X * X ^ (- A / (Real.log T ^ 9)) / ε)
    {c₄ : ℝ} (c₄pos : 0 ≤ c₄) {Tlb₄ : ℝ} (Tlb₄bnd : 3 < Tlb₄)
    (hc₄ : ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1) {T : ℝ} (_ : Tlb₄ < T),
      let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
      ‖I₄ bumpNu ε X σ₁ σ₂‖ ≤ c₄ * X * X ^ (- A / (Real.log T ^ 9)) / ε)
    {c₅ : ℝ} (c₅pos : 0 < c₅)
    (hc₅ : ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1),
      ‖I₅ bumpNu ε X σ₂‖ ≤ c₅ * X ^ σ₂ / ε)
    {c₆ : ℝ} (c₆pos : 0 ≤ c₆) {Tlb₆ : ℝ}
    (hc₆ : ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1) {T : ℝ} (_ : Tlb₆ < T),
      let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
      ‖I₆ bumpNu ε X σ₁ σ₂‖ ≤ c₆ * X * X ^ (- A / (Real.log T ^ 9)) / ε)
    {c₇ : ℝ} (c₇pos : 0 < c₇)
    (hc₇ : ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1) {T : ℝ} (_ : 3 < T),
      let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
      ‖I₇ bumpNu ε T X σ₁‖ ≤ c₇ * X * X ^ (- A / (Real.log T ^ 9)) / ε)
    {c₈ : ℝ} (c₈pos : 0 < c₈)
    (hc₈ : ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1) {T : ℝ} (_ : 3 < T),
      let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
      ‖I₈ bumpNu ε T X σ₁‖ ≤ c₈ * X / (ε * T))
    {c₉ : ℝ} (c₉pos : 0 < c₉)
    (hc₉ : ∀ {ε : ℝ} (_ : 0 < ε) (_ : ε < 1) (X : ℝ) (_ : 3 < X) {T : ℝ} (_ : 3 < T),
      ‖I₉ bumpNu ε X T‖ ≤ c₉ * X * Real.log X / (ε * T)) :
    ∀ x : ℝ, Real.exp (mediumPNTL A σ₂ Tlb₄ Tlb₆ ε_main) ≤ x →
      ‖(ψ - id : ℝ → ℝ) x‖ ≤
        ((c_close + C_main) + (c₁ + c₂ + c₈ + c₉) + (c₃ + c₄ + c₆ + c₇) + c₅) *
        ‖x * Real.exp (-(A ^ ((1 : ℝ) / 10) / 4) * (Real.log x) ^ ((1 : ℝ) / 10))‖ := by
  -- the smoothing function is the explicit `bumpNu`, not an unnamed witness of
  -- `SmoothExistence`; `ContDiff ℝ 1` is all the rest of this proof asks of it
  have ContDiff1ν : ContDiff ℝ 1 bumpNu := bumpNu_contDiff
  have ν_nonneg : ∀ x > 0, 0 ≤ bumpNu x := fun x _ ↦ bumpNu_nonneg x
  have ν_supp : bumpNu.support ⊆ Icc (1 / 2) 2 := bumpNu_support
  have ν_massOne : ∫ x in Ioi 0, bumpNu x / x = 1 := by
    rw [← integral_Ici_eq_integral_Ioi]; exact bumpNu_integral
  set ν := bumpNu with hν
  let C' := c_close + C_main
  let C'' := c₁ + c₂ + c₈ + c₉
  let C''' := c₃ + c₄ + c₆ + c₇
  let c : ℝ := A ^ ((1 : ℝ) / 10) / 4
  have hArp : (0 : ℝ) < A ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos A_in_Ioc.1 _
  have cpos : 0 < c := by change (0 : ℝ) < A ^ ((1 : ℝ) / 10) / 4; linarith
  let C : ℝ := C' + C'' + C''' + c₅
  change ∀ x : ℝ, Real.exp (mediumPNTL A σ₂ Tlb₄ Tlb₆ ε_main) ≤ x →
    ‖(ψ - id : ℝ → ℝ) x‖ ≤ C * ‖x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))‖
  let c_εx : ℝ := A ^ ((1 : ℝ) / 10) / 2
  have c_εx_pos : 0 < c_εx := by change (0 : ℝ) < A ^ ((1 : ℝ) / 10) / 2; linarith
  let c_Tx : ℝ := A ^ ((1 : ℝ) / 10)
  have c_Tx_pos : 0 < c_Tx := by change (0 : ℝ) < A ^ ((1 : ℝ) / 10); linarith
  let εx := (fun x ↦ Real.exp (-c_εx * (Real.log x) ^ ((1 : ℝ) / 10)))
  let Tx := (fun x ↦ Real.exp (c_Tx * (Real.log x) ^ ((1 : ℝ) / 10)))
  intro X hX
  obtain ⟨X_gt_3, f_ε1, f_2, f_T3, f_T4, f_T6, f_σ, f_εm, logX_ge, f_e1, f_e2, f_e3, f_e4⟩ :=
    mediumPNT_threshold_facts A_in_Ioc σ₂_lt_one ε_main_pos hX
  have ε_lt_one : εx X < 1 := f_ε1
  have ε_X : 2 < X * εx X := f_2
  have T_gt_3 : 3 < Tx X := f_T3
  have T_gt_Tlb₄ : Tlb₄ < Tx X := f_T4
  have T_gt_Tlb₆ : Tlb₆ < Tx X := f_T6
  have σ₂_lt_σ₁ : σ₂ < 1 - A / (Real.log (Tx X)) ^ 9 := f_σ
  have ε_lt_ε_main : εx X < ε_main := f_εm
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have C'_nonneg : 0 ≤ C' := by
    change 0 ≤ c_close + C_main
    linarith
  have C''_nonneg : 0 ≤ C'' := by
    change 0 ≤ c₁ + c₂ + c₈ + c₉
    linarith
  have C'''_nonneg : 0 ≤ C''' := by
    change 0 ≤ c₃ + c₄ + c₆ + c₇
    linarith
  have event_1 : C' * (εx X) * X * Real.log X ≤
      C' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10)) := by
    calc C' * (εx X) * X * Real.log X = (C' * X) * (εx X * Real.log X) := by ring
      _ ≤ (C' * X) * rexp (-c * Real.log X ^ ((1 : ℝ) / 10)) :=
          mul_le_mul_of_nonneg_left f_e1 (mul_nonneg C'_nonneg hX0)
      _ = C' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10)) := by ring
  have event_2 : C'' * X * Real.log X / (εx X * Tx X) ≤
      C'' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10)) := by
    calc C'' * X * Real.log X / (εx X * Tx X)
        = (C'' * X) * (Real.log X / (εx X * Tx X)) := by ring
      _ ≤ (C'' * X) * rexp (-c * Real.log X ^ ((1 : ℝ) / 10)) :=
          mul_le_mul_of_nonneg_left f_e2 (mul_nonneg C''_nonneg hX0)
      _ = C'' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10)) := by ring
  have event_3 : C''' * X * X ^ (-A / Real.log (Tx X) ^ 9) / (εx X) ≤
      C''' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10)) := by
    calc C''' * X * X ^ (-A / Real.log (Tx X) ^ 9) / (εx X)
        = (C''' * X) * (X ^ (-A / Real.log (Tx X) ^ 9) / εx X) := by ring
      _ ≤ (C''' * X) * rexp (-c * Real.log X ^ ((1 : ℝ) / 10)) :=
          mul_le_mul_of_nonneg_left f_e3 (mul_nonneg C'''_nonneg hX0)
      _ = C''' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10)) := by ring
  have event_4 : c₅ * X ^ σ₂ / (εx X) ≤
      c₅ * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10)) := by
    calc c₅ * X ^ σ₂ / (εx X) = c₅ * (X ^ σ₂ / εx X) := by ring
      _ ≤ c₅ * (X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10))) :=
          mul_le_mul_of_nonneg_left f_e4 c₅pos.le
      _ = c₅ * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10)) := by ring
  let ε : ℝ := εx X
  have ε_pos : 0 < ε := by positivity
  specialize h_close X X_gt_3 ε ε_pos ε_lt_one ε_X
  let ψ_ε_of_X := SmoothedChebyshev ν ε X
  let T : ℝ := Tx X
  specialize holo1 T T_gt_3.le
  let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
  have σ₁pos : 0 < σ₁ := by calc
    1 - A / (Real.log T)^9 >= 1 - (1/2) / 1 ^ 9:= by
      gcongr
      · exact A_in_Ioc.2
      · exact (logt_gt_one T_gt_3.le).le
    _ > 0 := by norm_num
  have σ₁_lt_one : σ₁ < 1 := by
    apply sub_lt_self
    apply div_pos A_in_Ioc.1
    bound
  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at holo2
  have holo2a : HolomorphicOn (SmoothedChebyshevIntegrand ν ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) := by
    apply DifferentiableOn.mul
    · apply DifferentiableOn.mul
      · rw [(by ext; ring : (fun s ↦ -ζ' s / ζ s) = (fun s ↦ -(ζ' s / ζ s)))]
        apply DifferentiableOn.neg holo2
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        apply Smooth1MellinDifferentiable ContDiff1ν ν_supp ⟨ε_pos, ε_lt_one⟩ ν_nonneg ν_massOne
        linarith[mem_reProdIm.mp hs.1 |>.1.1]
    · intro s hs
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow (by fun_prop)
      left
      norm_cast
      linarith
  have ψ_ε_diff : ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ ≤
      ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖
    + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖
    + ‖I₈ ν ε T X σ₁‖ + ‖I₉ ν ε X T‖ := by
    unfold ψ_ε_of_X
    rw [SmoothedChebyshevPull1 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₁pos σ₁_lt_one holo1 ν_supp ν_nonneg ν_massOne ContDiff1ν]
    rw [SmoothedChebyshevPull2 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₂_pos σ₁_lt_one σ₂_lt_σ₁ holo1 holo2a ν_supp ν_nonneg ν_massOne ContDiff1ν]
    ring_nf
    iterate 5
      apply le_trans (by apply norm_add_le)
      gcongr
    rw [(by ring : I₁ ν ε X T - I₂ ν ε T X σ₁ + I₃ ν ε T X σ₁ - I₄ ν ε X σ₁ σ₂ =
        (I₁ ν ε X T - I₂ ν ε T X σ₁) + (I₃ ν ε T X σ₁ - I₄ ν ε X σ₁ σ₂))]
    apply le_trans (by apply norm_add_le)
    rw [(by ring : ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ =
      (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖) + (‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖))]
    gcongr <;> apply le_trans (by apply norm_sub_le) <;> rfl
  specialize h_main ε ⟨ε_pos, ε_lt_ε_main⟩
  have main : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ ≤ C_main * ε * X := by
    nth_rewrite 2 [← one_mul X]
    push_cast
    rw [← sub_mul, norm_mul]
    gcongr
    rw [norm_real, norm_of_nonneg (by linarith)]
  specialize hc₁ ε ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₂ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₃ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₅ X X_gt_3 ε_pos ε_lt_one
  specialize hc₇ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₈ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₉ ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₄ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₄
  specialize hc₆ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₆
  clear ν_nonneg ν_massOne ContDiff1ν ν_supp holo2
  have C'bnd : c_close * ε * X * Real.log X + C_main * ε * X ≤ C' * ε * X * Real.log X := by
    have : C_main * ε * X * 1 ≤ C_main * ε * X * Real.log X := by
      gcongr
    linarith
  have C''bnd : c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T) + c₈ * X / (ε * T)
    + c₉ * X * Real.log X / (ε * T) ≤ C'' * X * Real.log X / (ε * T) := by
    unfold C''
    rw [(by ring : (c₁ + c₂ + c₈ + c₉) * X * Real.log X / (ε * T)
      = c₁ * X * Real.log X / (ε * T) + c₂ * X * Real.log X / (ε * T)
        + c₈ * X * Real.log X / (ε * T) + c₉ * X * Real.log X / (ε * T))]
    have : c₂ * X / (ε * T) * 1 ≤ c₂ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₂ * X / (ε * T) ≤ c₂ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]
    have : c₈ * X / (ε * T) * 1 ≤ c₈ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₈ * X / (ε * T) ≤ c₈ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]
  have C'''bnd : c₃ * X * X ^ (-A / Real.log T ^ 9) / ε
                    + c₄ * X * X ^ (-A / Real.log T ^ 9) / ε
                    + c₆ * X * X ^ (-A / Real.log T ^ 9) / ε
                    + c₇ * X * X ^ (-A / Real.log T ^ 9) / ε
                  ≤ C''' * X * X ^ (-A / Real.log T ^ 9) / ε := by
    apply le_of_eq
    ring
  calc
    _         = ‖(ψ X - ψ_ε_of_X) + (ψ_ε_of_X - X)‖ := by ring_nf; norm_cast
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - X‖ := norm_add_le _ _
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖(ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X)
                  + (𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X)‖ := by ring_nf
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖
                  + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ := by
                    rw [add_assoc]
                    gcongr
                    apply norm_add_le
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖
                  + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ := by ring
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖
                  + (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖
                  + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖ + ‖I₈ ν ε T X σ₁‖
                  + ‖I₉ ν ε X T‖) := by gcongr
    _         ≤ c_close * ε * X * Real.log X + C_main * ε * X
                  + (c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₃ * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₄ * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₅ * X ^ σ₂ / ε
                  + c₆ * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₇ * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T)) := by
      gcongr
      convert! h_close using 1
      rw [← norm_neg]
      congr
      ring
    _         =  (c_close * ε * X * Real.log X + C_main * ε * X)
                  + ((c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T))
                  + (c₃ * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₄ * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₆ * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₇ * X * X ^ (-A / Real.log T ^ 9) / ε)
                  + c₅ * X ^ σ₂ / ε
                  ) := by ring
    _         ≤ C' * ε * X * Real.log X
                  + (C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₅ * X ^ σ₂ / ε
                  ) := by
      gcongr
    _        = C' * ε * X * Real.log X
                  + C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₅ * X ^ σ₂ / ε
                    := by ring
    _        ≤ C' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10))
                  + C'' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10))
                  + C''' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10))
                  + c₅ * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10))
                    := by
      gcongr
    _        = C * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10))
                    := by ring
    _        = _ := by
      rw [Real.norm_of_nonneg]
      · rw [← mul_assoc]
      · positivity

/-- **The threshold of the effective PNT**, `RMF.mediumPNTL` at the inputs
`RMF.MediumPNTBoundExplicit` uses: the strip `zetaBndHoloA`, `σ₂ = zetaSmallTσ`,
`Tlb₄ = Tlb₆ = I4Tlb`, `ε_main = 1`. -/
noncomputable def mediumPNTThresholdL : ℝ :=
  mediumPNTL zetaBndHoloA zetaSmallTσ (I4Tlb zetaBndHoloA zetaSmallTσ)
    (I4Tlb zetaBndHoloA zetaSmallTσ) 1

lemma mediumPNTThresholdL_nonneg : 0 ≤ mediumPNTThresholdL := by
  unfold mediumPNTThresholdL mediumPNTL
  positivity

/-- **The effective PNT past an explicit threshold**: `‖ψ x − x‖ ≤ mediumPNTConst · x ·
exp(−mediumPNTRate·(log x)^{1/10})` for every `x ≥ exp RMF.mediumPNTThresholdL`. -/
theorem MediumPNTBoundExplicit : ∀ x : ℝ, Real.exp mediumPNTThresholdL ≤ x →
    ‖(ψ - id : ℝ → ℝ) x‖
      ≤ mediumPNTConst * ‖x * Real.exp (-mediumPNTRate * (Real.log x) ^ ((1 : ℝ) / 10))‖ := by
  obtain ⟨hCu, hAmem, hbnd, hholo1⟩ := LogDerivZetaBoundedAndHoloExplicit
  have hσ₂ : zetaSmallTσ ∈ Ioo (0 : ℝ) 1 := ⟨zetaSmallTσ_pos, zetaSmallTσ_lt_one⟩
  have hI4 := I4Bound_of holo2E hσ₂ hAmem bumpMellinC_pos bumpMellin_hyp
  exact MediumPNT_bound_explicit (A := zetaBndHoloA) hAmem hholo1
    zetaSmallTσ_pos zetaSmallTσ_lt_one holo2E
    (c_close := 30 * Real.log 2)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith)
    (SmoothedChebyshevCloseExplicit bumpNu_contDiff bumpNu_support bump_nonneg bump_massOne)
    (ε_main := 1) (C_main := 2 * Real.log 2) (by norm_num)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith)
    (fun ε hε => MellinOfSmooth1cBound bumpNu_contDiff bumpNu_support bump_nonneg bump_massOne
      hε.1 hε.2.le)
    (c₁ := |π|⁻¹ * 2⁻¹ * (Real.exp 1 * (2 * (zetaTrivC + 1)) * bumpMellinC))
    (by have := zetaTrivC_nonneg; have := bumpMellinC_pos
        have hpi : (0:ℝ) < |π| := abs_pos.mpr Real.pi_ne_zero
        positivity)
    (I1Bound_of bumpNu_support bumpNu_contDiff bump_nonneg bump_massOne bumpMellinC_pos
      bumpMellin_hyp zetaTrivK_pos logDeriv_zeta_le_strip)
    (c₂ := ‖1/(2*π*I)‖ * (2 * (bumpMellinC * zetaLogDerivUnifC * 48000 * rexp 1)))
    (by have h1 : (0:ℝ) < ‖(1:ℂ)/(2*(π:ℂ)*I)‖ := by
          rw [norm_pos_iff]; simp [Real.pi_ne_zero]
        have h2 := bumpMellinC_pos
        have h3 := zetaLogDerivUnifC_pos
        have h4 := Real.exp_pos (1:ℝ)
        positivity)
    (I2Bound_of hbnd hCu hAmem bumpMellinC_pos bumpMellin_hyp (by norm_num) IBound_aux1_nine)
    (c₃ := logIntC 9 * bumpMellinC * zetaLogDerivUnifC)
    (by have h1 := (log_pow_over_xsq_integral_bounded_explicit 9).1
        have h2 := bumpMellinC_pos
        have h3 := zetaLogDerivUnifC_pos
        positivity)
    (I3Bound_of hbnd hCu hAmem bumpMellinC_pos bumpMellin_hyp)
    (c₄ := I4C zetaSmallTσ bumpMellinC) hI4.1 (Tlb₄ := I4Tlb zetaBndHoloA zetaSmallTσ) hI4.2.1
    hI4.2.2
    (c₅ := I5const) (by linarith [I5const_pos]) I5BoundNamed
    (c₆ := I4C zetaSmallTσ bumpMellinC) hI4.1 (Tlb₆ := I4Tlb zetaBndHoloA zetaSmallTσ)
    (I6Bound_of holo2E hσ₂ hAmem bumpMellinC_pos bumpMellin_hyp)
    (c₇ := logIntC 9 * bumpMellinC * zetaLogDerivUnifC)
    (by have h1 := (log_pow_over_xsq_integral_bounded_explicit 9).1
        have h2 := bumpMellinC_pos
        have h3 := zetaLogDerivUnifC_pos
        positivity)
    (I7Bound_of hbnd hCu hAmem bumpMellinC_pos bumpMellin_hyp)
    (c₈ := ‖1/(2*π*I)‖ * (2 * (bumpMellinC * zetaLogDerivUnifC * 48000 * rexp 1)))
    (by have h1 : (0:ℝ) < ‖(1:ℂ)/(2*(π:ℂ)*I)‖ := by
          rw [norm_pos_iff]; simp [Real.pi_ne_zero]
        have h2 := bumpMellinC_pos
        have h3 := zetaLogDerivUnifC_pos
        have h4 := Real.exp_pos (1:ℝ)
        positivity)
    (I8Bound_of hbnd hCu hAmem bumpMellinC_pos bumpMellin_hyp (by norm_num) IBound_aux1_nine)
    (c₉ := |π|⁻¹ * 2⁻¹ * (Real.exp 1 * (2 * (zetaTrivC + 1)) * bumpMellinC))
    (by have := zetaTrivC_nonneg; have := bumpMellinC_pos
        have hpi : (0:ℝ) < |π| := abs_pos.mpr Real.pi_ne_zero
        positivity)
    (I9Bound_of bumpNu_support bumpNu_contDiff bump_nonneg bump_massOne bumpMellinC_pos
      bumpMellin_hyp zetaTrivK_pos logDeriv_zeta_le_strip)

/-- **The effective PNT in numerals, past an explicit threshold**:
`‖ψ x − x‖ ≤ 10³⁹ · x · exp(−(1/200)(log x)^{1/10})` for every `x ≥ exp RMF.mediumPNTThresholdL`. -/
theorem MediumPNTConstantExplicit : ∀ x : ℝ, Real.exp mediumPNTThresholdL ≤ x →
    ‖(ψ - id : ℝ → ℝ) x‖
      ≤ 10 ^ (39 : ℕ) * ‖x * Real.exp (-(1 / 200 : ℝ) * (Real.log x) ^ ((1 : ℝ) / 10))‖ := by
  intro x hx0
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp mediumPNTThresholdL_nonneg) hx0
  have hx := MediumPNTBoundExplicit x hx0
  refine le_trans hx (mul_le_mul mediumPNTConst_le ?_ (norm_nonneg _) (by norm_num))
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hLr : 0 ≤ Real.log x ^ ((1 : ℝ) / 10) := Real.rpow_nonneg hlog _
  have hc := mediumPNTRate_ge
  have hx0' : (0 : ℝ) ≤ x := by linarith
  have hexp : Real.exp (-mediumPNTRate * Real.log x ^ ((1 : ℝ) / 10))
      ≤ Real.exp (-(1 / 200 : ℝ) * Real.log x ^ ((1 : ℝ) / 10)) := by
    apply Real.exp_monotone; nlinarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  nlinarith [Real.exp_pos (-(1 / 200 : ℝ) * Real.log x ^ ((1 : ℝ) / 10))]

/-- **`log x₀ ≤ 10⁴⁵`** for the effective PNT's threshold `x₀ = exp RMF.mediumPNTThresholdL`:
`u₀ ≤ 30802`, set by `(80/a) log(40/a) + 2` with `a = zetaBndHoloA^{1/10} ≥ 1/50`
(`RMF.eighty_div_mul_log_le`).  The other terms are small: `I4Tlb ≤ e⁵⁶`, and
`(a/(1-σ₂))^{1/9} ≤ 60` since `1 - σ₂ = 10⁻¹⁶`.  So the block cosine estimates start at
`\log\log x₀ ≤ 103.7`. -/
lemma mediumPNTThresholdL_le_sharp : mediumPNTThresholdL ≤ 10 ^ 45 := by
  obtain ⟨-, hAmem, -, -⟩ := LogDerivZetaBoundedAndHoloExplicit
  have hA0 : 0 < zetaBndHoloA := hAmem.1
  have hA2 : zetaBndHoloA ≤ 1 / 2 := hAmem.2
  have ha : (1 / 50 : ℝ) ≤ zetaBndHoloA ^ ((1 : ℝ) / 10) := by
    have := zetaBndHoloA_rpow_ge
    linarith
  have ha1 : zetaBndHoloA ^ ((1 : ℝ) / 10) ≤ 1 :=
    Real.rpow_le_one hA0.le (by linarith) (by norm_num)
  have hσ : 1 - zetaSmallTσ = (1 / 10 : ℝ) ^ (16 : ℕ) := by
    unfold zetaSmallTσ
    ring
  unfold mediumPNTThresholdL mediumPNTL
  set A := zetaBndHoloA with hAdef
  set a := A ^ ((1 : ℝ) / 10) with hadef
  have ha0 : 0 < a := by linarith
  have h56 : (4 : ℝ) ≤ Real.exp 56 := by
    have := Real.add_one_le_exp (56 : ℝ)
    linarith
  have hT : max 3 (max (I4Tlb A zetaSmallTσ) (I4Tlb A zetaSmallTσ)) ≤ Real.exp 56 := by
    have h1 : A ^ (9 : ℝ)⁻¹ ≤ 56 :=
      le_trans (Real.rpow_le_one hA0.le (by linarith) (by norm_num)) (by norm_num)
    have h2 : (A / (1 - zetaSmallTσ)) ^ (9 : ℝ)⁻¹ ≤ 56 := by
      have hle : A / (1 - zetaSmallTσ) ≤ 56 ^ 9 := by
        rw [hσ, div_le_iff₀ (by positivity)]
        norm_num
        linarith
      calc (A / (1 - zetaSmallTσ)) ^ (9 : ℝ)⁻¹ ≤ ((56 : ℝ) ^ 9) ^ (9 : ℝ)⁻¹ :=
            Real.rpow_le_rpow (div_nonneg hA0.le (by rw [hσ]; positivity)) hle (by norm_num)
        _ = 56 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            norm_num
    have hI : I4Tlb A zetaSmallTσ ≤ Real.exp 56 := by
      unfold I4Tlb
      exact max_le h56 (max_le (Real.exp_le_exp.2 h1) (Real.exp_le_exp.2 h2))
    exact max_le (by linarith) (max_le hI hI)
  have hM3 : (3 : ℝ) ≤ max 3 (max (I4Tlb A zetaSmallTσ) (I4Tlb A zetaSmallTσ)) :=
    le_max_left _ _
  have hℓ : Real.log (max 3 (max (I4Tlb A zetaSmallTσ) (I4Tlb A zetaSmallTσ))) / a + 1
      ≤ 2801 := by
    have hl : Real.log (max 3 (max (I4Tlb A zetaSmallTσ) (I4Tlb A zetaSmallTσ))) ≤ 56 := by
      calc Real.log (max 3 (max (I4Tlb A zetaSmallTσ) (I4Tlb A zetaSmallTσ)))
          ≤ Real.log (Real.exp 56) := Real.log_le_log (by linarith) hT
        _ = 56 := Real.log_exp 56
    have hl0 : 0 ≤ Real.log (max 3 (max (I4Tlb A zetaSmallTσ) (I4Tlb A zetaSmallTσ))) :=
      Real.log_nonneg (by linarith)
    have hdiv : Real.log (max 3 (max (I4Tlb A zetaSmallTσ) (I4Tlb A zetaSmallTσ))) / a
        ≤ 2800 := by
      rw [div_le_iff₀ ha0]
      nlinarith
    linarith
  have hr : (a / (1 - zetaSmallTσ)) ^ ((1 : ℝ) / 9) + 1 ≤ 61 := by
    have hle : a / (1 - zetaSmallTσ) ≤ 60 ^ 9 := by
      rw [hσ, div_le_iff₀ (by positivity)]
      norm_num
      linarith
    have h := Real.rpow_le_rpow (div_nonneg ha0.le (by rw [hσ]; positivity)) hle
      (by norm_num : (0 : ℝ) ≤ 1 / 9)
    rw [← Real.rpow_natCast (60 : ℝ) 9, ← Real.rpow_mul (by norm_num)] at h
    norm_num at h
    linarith
  have hε : 2 * |Real.log 1| / a + 1 ≤ 1 := by simp
  have hq : 80 / a * Real.log (40 / a) + 2 ≤ 30802 := eighty_div_mul_log_le ha ha1
  have hu : mediumPNTU A zetaSmallTσ (I4Tlb A zetaSmallTσ) (I4Tlb A zetaSmallTσ) 1 ≤ 30802 := by
    unfold mediumPNTU
    exact max_le (max_le (by norm_num) (by linarith))
      (max_le (by linarith) (max_le (by linarith) hq))
  have hu0 : 0 ≤ mediumPNTU A zetaSmallTσ (I4Tlb A zetaSmallTσ) (I4Tlb A zetaSmallTσ) 1 := by
    unfold mediumPNTU
    exact le_trans zero_le_one (le_trans (le_max_left _ _) (le_max_left _ _))
  calc mediumPNTU A zetaSmallTσ (I4Tlb A zetaSmallTσ) (I4Tlb A zetaSmallTσ) 1 ^ 10
      ≤ 30802 ^ 10 := pow_le_pow_left₀ hu0 hu 10
    _ ≤ 10 ^ 45 := by norm_num

/-- **`log x₀ ≤ 10⁷³`**, which follows from `RMF.mediumPNTThresholdL_le_sharp`. -/
lemma mediumPNTThresholdL_le : mediumPNTThresholdL ≤ 10 ^ 73 :=
  le_trans mediumPNTThresholdL_le_sharp (by norm_num)

end MediumPNTThreshold

end RMF
