/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.FracReductionExplicit.Parseval
import RMF.Reduction.UpperSieveLeaves

/-!
# The remainder's reduction, IV: the explicit parameters

The headline of the reduction.  With `L = log x`, `Λ = log log x`, the smoothness exponent
`U = 16Λ + 85` (`RMF.fracU`), `y = ⌊x^{1/U}⌋` (`RMF.fracY`), `σ = c/log x`, and internally
`T₀ = √x`, `η = L⁻³`, `ε = L^{-1/2}`, `κ = 1` and the Selberg level `D = x^{1/4}`: for
`x ≥ exp(e^{20})` and `c ≥ 0` (`RMF.integral_norm_fracPartSum_le_lineFrac`),

`E|R(x)| ≤ (0.0895·e^c)^{1/2}·E[Z_R^{1/2}] + 3/log x`,
`Z_R = (log y)⁻¹∫_ℝ|F_{y+1}(½+σ+it)|²|φ̂(½+σ+it)|²dt`.

`0.0895 ≥ 1.0003·1.001e^{-γ}/(2π)` is Selberg's constant with the corrections `(1+ε)` and
`(1+η) + (1+η)²/(ηT₀)`; the error `3/log x = 3e^{-Λ}` collects `fracSmoothErr^{1/2} ≤ 2/L` and
`fracLowErr^{1/2} ≤ 1/L`.  `U ≥ 16Λ + 85` is what makes Selberg's level condition
`D^{1/(2 log y)} ≥ 40000 log² y` hold at `D = x^{1/4}` (`e^{85/8} ≥ 40000`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The parameters -/

/-- The smoothness exponent `U = 16 log log x + 85`. -/
noncomputable def fracU (x : ℝ) : ℝ := 16 * Real.log (Real.log x) + 85

/-- The smoothness level `y = ⌊x^{1/U}⌋`, `U = RMF.fracU x`. -/
noncomputable def fracY (x : ℝ) : ℕ := ⌊x ^ (1 / fracU x)⌋₊

/-! ### Numerals -/

/-- `e^{20} ≥ 4.85·10⁸`. -/
lemma exp_twenty_ge_sharp : (485000000 : ℝ) ≤ Real.exp 20 := by
  interval_decide (trust := kernel)

/-- `e^{85/8} ≥ 40000`. -/
lemma exp_eightyfive_eighths_ge : (40000 : ℝ) ≤ Real.exp (85 / 8) := by
  interval_decide (trust := kernel)

/-- `(10⁶ + 1)(16Λ + 85) ≤ e^Λ` for `Λ ≥ 20`. -/
lemma mul_fracU_le_exp {Λ : ℝ} (hΛ : 20 ≤ Λ) :
    (1000001 : ℝ) * (16 * Λ + 85) ≤ Real.exp Λ := by
  have h20 := exp_twenty_ge_sharp
  have h1 : Real.exp 20 * (1 + (Λ - 20)) ≤ Real.exp Λ := by
    have h := Real.add_one_le_exp (Λ - 20)
    calc Real.exp 20 * (1 + (Λ - 20)) ≤ Real.exp 20 * Real.exp (Λ - 20) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 20).le
      _ = Real.exp Λ := by rw [← Real.exp_add]; ring_nf
  nlinarith [mul_nonneg (sub_nonneg.2 h20) (by linarith : (0 : ℝ) ≤ Λ - 19)]

/-- `2L⁴ ≤ e^{L/2}` for `L ≥ 7680`: `e^{L/2} ≥ (L/2)⁵/5!`. -/
lemma two_mul_pow_four_le_exp_half {L : ℝ} (hL : 7680 ≤ L) :
    2 * L ^ 4 ≤ Real.exp (L / 2) := by
  have h5 := Real.pow_div_factorial_le_exp (x := L / 2) (by linarith) 5
  have hf : ((Nat.factorial 5 : ℕ) : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [hf] at h5
  have hL4 : 0 ≤ L ^ 4 := by positivity
  have key : 2 * L ^ 4 ≤ (L / 2) ^ 5 / 120 := by
    rw [le_div_iff₀ (by norm_num), div_pow]
    have : (2 : ℝ) * L ^ 4 * 120 * 2 ^ 5 ≤ L ^ 4 * L := by nlinarith
    calc 2 * L ^ 4 * 120 = 2 * L ^ 4 * 120 * 2 ^ 5 / 2 ^ 5 := by ring
      _ ≤ L ^ 4 * L / 2 ^ 5 := by gcongr
      _ = L ^ 5 / 2 ^ 5 := by ring
  linarith

/-- `2·10⁵(1 + L/4)³L⁴ ≤ e^{L/4}` for `L ≥ 4.85·10⁸`: `e^{L/4} ≥ (L/4)⁹/9!`. -/
lemma herr_aux {L : ℝ} (hL : 485000000 ≤ L) :
    200000 * (1 + L / 4) ^ 3 * L ^ 4 ≤ Real.exp (L / 4) := by
  have h9 := Real.pow_div_factorial_le_exp (x := L / 4) (by linarith) 9
  have hf : ((Nat.factorial 9 : ℕ) : ℝ) = 362880 := by norm_num [Nat.factorial]
  rw [hf] at h9
  have hL0 : 0 < L := by linarith
  have h1 : (1 + L / 4) ^ 3 ≤ (L / 2) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
  have h2 : 200000 * (1 + L / 4) ^ 3 * L ^ 4 ≤ 200000 * (L / 2) ^ 3 * L ^ 4 := by gcongr
  have h3 : 200000 * (L / 2) ^ 3 * L ^ 4 = 25000 * L ^ 7 := by ring
  have hkey : (25000 : ℝ) * (4 ^ 9 * 362880) ≤ L ^ 2 := by nlinarith
  have h7 : 0 ≤ L ^ 7 := by positivity
  have h4 : 25000 * L ^ 7 ≤ (L / 4) ^ 9 / 362880 := by
    rw [le_div_iff₀ (by norm_num), div_pow]
    calc 25000 * L ^ 7 * 362880 = L ^ 7 * (25000 * (4 ^ 9 * 362880)) / 4 ^ 9 := by ring
      _ ≤ L ^ 7 * L ^ 2 / 4 ^ 9 := by gcongr
      _ = L ^ 9 / 4 ^ 9 := by ring
  linarith

/-! ### The parameters' properties -/

/-- From `x ≥ exp(e^{20})`: `L = log x ≥ 4.85·10⁸`, `Λ = log L ≥ 20` and `L = e^Λ`. -/
lemma log_facts_of_exp_exp_twenty_le {x : ℝ} (hx : Real.exp (Real.exp 20) ≤ x) :
    0 < x ∧ Real.exp 20 ≤ Real.log x ∧ 485000000 ≤ Real.log x
      ∧ 20 ≤ Real.log (Real.log x) ∧ Real.exp (Real.log (Real.log x)) = Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : Real.exp 20 ≤ Real.log x := by
    rw [← Real.log_exp (Real.exp 20)]
    exact Real.log_le_log (Real.exp_pos _) hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛ : 20 ≤ Real.log (Real.log x) := by
    rw [← Real.log_exp 20]
    exact Real.log_le_log (Real.exp_pos _) hL
  exact ⟨hx0, hL, le_trans exp_twenty_ge_sharp hL, hΛ, Real.exp_log hL0⟩

/-- **The smoothness level**: for `x ≥ exp(e^{20})`, `y = ⌊x^{1/U}⌋` has `y ≥ 2`, `log y ≥ 10⁶`
and `log y ≤ log x/U`. -/
lemma fracY_facts {x : ℝ} (hx : Real.exp (Real.exp 20) ≤ x) :
    2 ≤ fracY x ∧ 1000000 ≤ Real.log (fracY x)
      ∧ Real.log (fracY x) ≤ Real.log x / fracU x := by
  obtain ⟨hx0, -, hL, hΛ, hexp⟩ := log_facts_of_exp_exp_twenty_le hx
  set L := Real.log x with hLdef
  set Λ := Real.log L with hΛdef
  have hU : fracU x = 16 * Λ + 85 := rfl
  have hU0 : 0 < fracU x := by rw [hU]; linarith
  set A := L / fracU x with hAdef
  have hA : (1000001 : ℝ) ≤ A := by
    rw [hAdef, le_div_iff₀ hU0, hU]
    have := mul_fracU_le_exp hΛ
    rw [hexp] at this
    linarith
  have hpow : x ^ (1 / fracU x) = Real.exp A := by
    rw [Real.rpow_def_of_pos hx0, ← hLdef, hAdef]
    congr 1
    ring
  have hy : fracY x = ⌊Real.exp A⌋₊ := by rw [fracY, hpow]
  have heA : A + 1 ≤ Real.exp A := Real.add_one_le_exp A
  have hlt : Real.exp A < (fracY x : ℝ) + 1 := by rw [hy]; exact Nat.lt_floor_add_one _
  have hle : (fracY x : ℝ) ≤ Real.exp A := by rw [hy]; exact Nat.floor_le (Real.exp_pos A).le
  have hy2R : (2 : ℝ) ≤ (fracY x : ℝ) := by linarith
  have hy0 : (0 : ℝ) < (fracY x : ℝ) := by linarith
  refine ⟨by exact_mod_cast hy2R, ?_, ?_⟩
  · -- `y ≥ e^A/2`, so `log y ≥ A - log 2`
    have hhalf : Real.exp A / 2 ≤ (fracY x : ℝ) := by linarith
    have hlog := Real.log_le_log (by positivity) hhalf
    rw [Real.log_div (Real.exp_pos A).ne' two_ne_zero, Real.log_exp] at hlog
    have hl2 := Real.log_two_lt_d9
    linarith
  · have := Real.log_le_log hy0 hle
    rwa [Real.log_exp] at this

/-! ### The three terms -/

/-- **The constant**: `(1 + L^{-1/2})·((1+η)²(η/(1+η) + 1/T₀)/η) ≤ 1.0003` for `η = L⁻³`,
`L ≥ 4.85·10⁸` and `T₀ ≥ 2L⁴`. -/
lemma fracReduction_middle_le {L T₀ : ℝ} (hL : 485000000 ≤ L) (hT₀ : 2 * L ^ 4 ≤ T₀) :
    (1 + (Real.sqrt L)⁻¹) * ((1 + (L ^ 3)⁻¹) ^ 2 * ((L ^ 3)⁻¹ / (1 + (L ^ 3)⁻¹) + 1 / T₀)
      / (L ^ 3)⁻¹) ≤ 1.0003 := by
  have hL0 : 0 < L := by linarith
  have hL3 : (0 : ℝ) < L ^ 3 := by positivity
  set η : ℝ := (L ^ 3)⁻¹ with hηdef
  have hη0 : 0 < η := inv_pos.2 hL3
  have hT₀0 : 0 < T₀ := lt_of_lt_of_le (by positivity) hT₀
  -- `η ≤ 10⁻⁸`
  have hη1 : η ≤ 1 / 100000000 := by
    rw [hηdef, inv_le_comm₀ hL3 (by norm_num)]
    have : (100000000 : ℝ) ≤ L := by linarith
    have h1 : L ≤ L ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    norm_num
    linarith
  -- `1/(ηT₀) = L³/T₀ ≤ 1/(2L) ≤ 10⁻⁸`
  have hηT : 1 / (η * T₀) ≤ 1 / 100000000 := by
    have h1 : η * T₀ = T₀ / L ^ 3 := by rw [hηdef]; ring
    rw [h1, one_div_div, div_le_div_iff₀ hT₀0 (by norm_num)]
    have h2 : L ^ 3 * 100000000 ≤ 2 * L ^ 4 := by
      have : (100000000 : ℝ) ≤ 2 * L := by linarith
      nlinarith [pow_pos hL0 3]
    linarith
  have hM : (1 + η) ^ 2 * (η / (1 + η) + 1 / T₀) / η = (1 + η) + (1 + η) ^ 2 * (1 / (η * T₀)) := by
    field_simp
  rw [hM]
  have hsq : (Real.sqrt L)⁻¹ ≤ 1 / 22000 := by
    have h1 : (22000 : ℝ) ≤ Real.sqrt L := by
      rw [Real.le_sqrt (by norm_num) hL0.le]
      linarith
    rw [one_div]
    exact inv_anti₀ (by norm_num) h1
  have hsq0 : 0 ≤ (Real.sqrt L)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hηT0 : 0 ≤ 1 / (η * T₀) := by positivity
  have hsq2 : (1 + η) ^ 2 ≤ 2 := by nlinarith
  have hB : (1 + η) + (1 + η) ^ 2 * (1 / (η * T₀)) ≤ 1 + 3 / 100000000 := by
    have : (1 + η) ^ 2 * (1 / (η * T₀)) ≤ 2 * (1 / 100000000) :=
      mul_le_mul hsq2 hηT hηT0 (by norm_num)
    linarith
  have hB0 : 0 ≤ (1 + η) + (1 + η) ^ 2 * (1 / (η * T₀)) := by positivity
  calc (1 + (Real.sqrt L)⁻¹) * ((1 + η) + (1 + η) ^ 2 * (1 / (η * T₀)))
      ≤ (1 + 1 / 22000) * (1 + 3 / 100000000) :=
        mul_le_mul (by linarith) hB hB0 (by norm_num)
    _ ≤ 1.0003 := by norm_num

/-- **The smoothing error**: `fracSmoothErr x L⁻³ L^{-1/2} ≤ 4/L²` for `L = log x ≥ 4.85·10⁸` and
`√x ≥ 2L⁴`. -/
lemma fracSmoothErr_le_explicit {x : ℝ} (hL : 485000000 ≤ Real.log x)
    (hsx : 2 * Real.log x ^ 4 ≤ Real.sqrt x) :
    fracSmoothErr x (Real.log x ^ 3)⁻¹ (Real.sqrt (Real.log x))⁻¹ ≤ 4 / Real.log x ^ 2 := by
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  have hsx0 : 0 < Real.sqrt x := lt_of_lt_of_le (by positivity) hsx
  rw [fracSmoothErr, one_div, inv_inv]
  set η : ℝ := (L ^ 3)⁻¹ with hηdef
  have hη0 : 0 < η := by positivity
  -- the three terms
  have h1 : η ^ 2 / 4 * (1 + L) ^ 2 ≤ 1 / L ^ 4 := by
    have hL1 : (1 + L) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
    have hη2 : η ^ 2 = 1 / L ^ 6 := by rw [hηdef]; field_simp
    rw [hη2]
    calc 1 / L ^ 6 / 4 * (1 + L) ^ 2 ≤ 1 / L ^ 6 / 4 * (4 * L ^ 2) :=
          mul_le_mul_of_nonneg_left hL1 (by positivity)
      _ = 1 / L ^ 4 := by field_simp
  have h2 : (1 + η) / Real.sqrt x ≤ 1 / L ^ 4 := by
    have hη1 : η ≤ 1 := by
      rw [hηdef]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    rw [div_le_div_iff₀ hsx0 (by positivity)]
    nlinarith
  have h3 : η ≤ 1 / L ^ 3 := by rw [hηdef, one_div]
  have h4 : 2 / L ^ 4 ≤ 1 / L ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hL0 3]
  have hin : η ^ 2 / 4 * (1 + L) ^ 2 + η + (1 + η) / Real.sqrt x ≤ 2 / L ^ 3 := by
    have : 1 / L ^ 4 + 1 / L ^ 4 = 2 / L ^ 4 := by ring
    have : 1 / L ^ 3 + 1 / L ^ 3 = 2 / L ^ 3 := by ring
    linarith
  have hin0 : 0 ≤ η ^ 2 / 4 * (1 + L) ^ 2 + η + (1 + η) / Real.sqrt x := by positivity
  have hs1 : 1 + Real.sqrt L ≤ 2 * Real.sqrt L := by
    have : (1 : ℝ) ≤ Real.sqrt L := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  have hsL2 : Real.sqrt L ≤ L := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  calc (1 + Real.sqrt L) * (η ^ 2 / 4 * (1 + L) ^ 2 + η + (1 + η) / Real.sqrt x)
      ≤ (2 * Real.sqrt L) * (2 / L ^ 3) := mul_le_mul hs1 hin hin0 (by positivity)
    _ ≤ (2 * L) * (2 / L ^ 3) := by gcongr
    _ = 4 / L ^ 2 := by
        field_simp
        ring

/-- **The small rough factors**: `fracLowErr x √x y 1 ≤ 1/L²` for `x ≥ exp(e^{20})`,
`10⁶ ≤ log y ≤ L/U`. -/
lemma fracLowErr_le_explicit {x : ℝ} (hx : Real.exp (Real.exp 20) ≤ x) {y : ℕ}
    (hy1 : 1000000 ≤ Real.log y) (hy2 : Real.log y ≤ Real.log x / fracU x) :
    fracLowErr x (Real.sqrt x) y 1 ≤ 1 / Real.log x ^ 2 := by
  obtain ⟨hx0, -, hL, hΛ, hexp⟩ := log_facts_of_exp_exp_twenty_le hx
  set L := Real.log x with hLdef
  set Λ := Real.log L with hΛdef
  have hL0 : 0 < L := by linarith
  have hU : fracU x = 16 * Λ + 85 := rfl
  have hU0 : 0 < fracU x := by rw [hU]; linarith
  have hly0 : 0 < Real.log y := by linarith
  have hlogs : Real.log (Real.sqrt x) = L / 2 := by rw [Real.log_sqrt hx0.le]
  have hdiv : x / Real.sqrt x = Real.sqrt x := Real.div_sqrt
  rw [fracLowErr, hdiv, hlogs, one_mul]
  -- `(L/2)/log y ≥ U/2`
  have hratio : fracU x / 2 ≤ L / 2 / Real.log y := by
    rw [le_div_iff₀ hly0]
    have : Real.log y * fracU x ≤ L := by
      rw [le_div_iff₀ hU0] at hy2
      linarith
    linarith
  -- the first part of the exponent
  have he1 := Real.exp_one_lt_d9
  have hl4 : Real.log 4 < 1.3863 := by
    have h := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith
  have hfrac : (Real.log 4 + 4) / Real.log y ≤ 6 / 1000000 := by
    rw [div_le_div_iff₀ hly0 (by norm_num)]
    have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith
  have hfrac0 : 0 ≤ (Real.log 4 + 4) / Real.log y :=
    div_nonneg (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]) hly0.le
  have he0 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hexpo : 1.42 + (Real.exp 1 - 1) * (1 + (Real.log 4 + 4) / Real.log y)
      ≤ 3.1385 := by
    have : (Real.exp 1 - 1) * (1 + (Real.log 4 + 4) / Real.log y)
        ≤ 1.7182818286 * (1 + 6 / 1000000) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    norm_num at this ⊢
    linarith
  -- the prefactor
  have hpre : (1 + L / 2) * Real.log y ≤ L ^ 2 := by
    have h1 : Real.log y ≤ L := by
      refine le_trans hy2 ?_
      rw [div_le_iff₀ hU0]
      rw [hU]
      nlinarith
    have h2 : 1 + L / 2 ≤ L := by linarith
    calc (1 + L / 2) * Real.log y ≤ L * L := mul_le_mul h2 h1 hly0.le hL0.le
      _ = L ^ 2 := by ring
  have hpre0 : 0 ≤ (1 + L / 2) * Real.log y := by positivity
  have hE : Real.exp (1.42 + (Real.exp 1 - 1) * (1 + (Real.log 4 + 4) / Real.log y)
      - L / 2 / Real.log y) ≤ Real.exp (3.1385 - (16 * Λ + 85) / 2) := by
    refine Real.exp_le_exp.2 ?_
    rw [hU] at hratio
    linarith
  have hL2 : L ^ 2 = Real.exp (2 * Λ) := by
    rw [← hexp, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  calc (1 + L / 2) * Real.log y * Real.exp (1.42 + (Real.exp 1 - 1)
        * (1 + (Real.log 4 + 4) / Real.log y) - L / 2 / Real.log y)
      ≤ L ^ 2 * Real.exp (3.1385 - (16 * Λ + 85) / 2) :=
        mul_le_mul hpre hE (Real.exp_pos _).le (by positivity)
    _ = Real.exp (2 * Λ + (3.1385 - (16 * Λ + 85) / 2)) := by
        rw [hL2, Real.exp_add]
    _ ≤ Real.exp (-(2 * Λ)) := Real.exp_le_exp.2 (by linarith)
    _ = 1 / L ^ 2 := by
        rw [hL2, Real.exp_neg, one_div]

/-- **Selberg's conditions at `D = x^{1/4}`** for `x ≥ exp(e^{20})`:
`D^{1/(2 log y)} ≥ 40000 log² y` and `5D(1 + log D)³·20000 log y ≤ √x·η/(1+η) + 1`, `η = L⁻³`. -/
lemma fracSelberg_conditions {x : ℝ} (hx : Real.exp (Real.exp 20) ≤ x) :
    40000 * Real.log (fracY x) ^ 2
        ≤ Real.exp (Real.log x / 4) ^ (1 / (2 * Real.log (fracY x)))
      ∧ 5 * Real.exp (Real.log x / 4) * (1 + Real.log (Real.exp (Real.log x / 4))) ^ 3
          * (20000 * Real.log (fracY x))
        ≤ Real.sqrt x * (Real.log x ^ 3)⁻¹ / (1 + (Real.log x ^ 3)⁻¹) + 1 := by
  obtain ⟨hx0, -, hL, hΛ, hexp⟩ := log_facts_of_exp_exp_twenty_le hx
  obtain ⟨-, hy1, hy2⟩ := fracY_facts hx
  set L := Real.log x with hLdef
  set Λ := Real.log L with hΛdef
  set ly := Real.log (fracY x) with hly
  have hL0 : 0 < L := by linarith
  have hU : fracU x = 16 * Λ + 85 := rfl
  have hU0 : 0 < fracU x := by rw [hU]; linarith
  have hly0 : 0 < ly := by linarith
  have hlyL : ly * fracU x ≤ L := by
    rw [le_div_iff₀ hU0] at hy2
    linarith
  have hlyL' : ly ≤ L := by
    have : ly ≤ ly * fracU x := le_mul_of_one_le_right hly0.le (by rw [hU]; linarith)
    linarith
  refine ⟨?_, ?_⟩
  · -- `D^{1/(2 log y)} = e^{L/(8 log y)} ≥ e^{U/8}`
    rw [← Real.exp_mul]
    have hexpo : 2 * Λ + 85 / 8 ≤ L / 4 * (1 / (2 * ly)) := by
      rw [show L / 4 * (1 / (2 * ly)) = L / (8 * ly) by field_simp; ring,
        le_div_iff₀ (by positivity)]
      rw [hU] at hlyL
      nlinarith
    have hsq : ly ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hly0.le hlyL' 2
    have hL2 : L ^ 2 = Real.exp (2 * Λ) := by
      rw [← hexp, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    calc 40000 * ly ^ 2 ≤ Real.exp (85 / 8) * L ^ 2 :=
          mul_le_mul exp_eightyfive_eighths_ge hsq (sq_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * Λ + 85 / 8) := by rw [hL2, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (L / 4 * (1 / (2 * ly))) := Real.exp_le_exp.2 hexpo
  · -- `10⁵e^{L/4}(1 + L/4)³ log y ≤ e^{L/2}/(2L³)`
    rw [Real.log_exp]
    have hsx : Real.sqrt x = Real.exp (L / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, ← hLdef]
      ring_nf
    rw [hsx]
    set η : ℝ := (L ^ 3)⁻¹ with hηdef
    have hη0 : 0 < η := by positivity
    have hη1 : η ≤ 1 := by
      rw [hηdef]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    have hrhs : Real.exp (L / 2) * η / 2 ≤ Real.exp (L / 2) * η / (1 + η) + 1 := by
      have : Real.exp (L / 2) * η / 2 ≤ Real.exp (L / 2) * η / (1 + η) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
      linarith
    refine le_trans ?_ hrhs
    have haux := herr_aux hL
    have hsplit : Real.exp (L / 2) = Real.exp (L / 4) * Real.exp (L / 4) := by
      rw [← Real.exp_add]; ring_nf
    have hE0 : 0 < Real.exp (L / 4) := Real.exp_pos _
    rw [hsplit, hηdef]
    have hL3 : 0 < L ^ 3 := by positivity
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hcube : 0 ≤ (1 + L / 4) ^ 3 := by positivity
    calc 5 * Real.exp (L / 4) * (1 + L / 4) ^ 3 * (20000 * ly) * 2
        ≤ 5 * Real.exp (L / 4) * (1 + L / 4) ^ 3 * (20000 * L) * 2 := by gcongr
      _ = Real.exp (L / 4) * (200000 * (1 + L / 4) ^ 3 * L ^ 4) * (L ^ 3)⁻¹ := by
          field_simp
          ring
      _ ≤ Real.exp (L / 4) * Real.exp (L / 4) * (L ^ 3)⁻¹ := by
          gcongr

/-! ### The headline -/

/-- **The remainder's reduction to the line, explicit.**  For every Rademacher `X`,
`x ≥ exp(e^{20})` and `c ≥ 0`, with `y = ⌊x^{1/U}⌋`, `U = 16 log log x + 85` (`RMF.fracY`) and
`σ = c/log x`:

`E|R(x)| ≤ (0.0895·e^c)^{1/2}·E[Z_R^{1/2}] + 3/log x`,
`Z_R = (log y)⁻¹∫_ℝ|F_{y+1}(½+σ+it)|²|φ̂(½+σ+it)|²dt`.

`RMF.integral_norm_fracPartSum_le_explicit_selberg` at `T₀ = √x`, `η = (log x)⁻³`,
`ε = (log x)^{-1/2}`, `κ = 1`, `D = x^{1/4}`: the constant is
`(1+ε)·((1+η) + (1+η)²/(ηT₀))·1.001e^{-γ}e^c/(2π) ≤ 1.0003·0.08947e^c`
(`RMF.sieveConst_div_two_pi_le`), and the errors are `fracSmoothErr^{1/2} ≤ 2/log x`,
`fracLowErr^{1/2} ≤ 1/log x`. -/
theorem integral_norm_fracPartSum_le_lineFrac {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x c : ℝ} (hx : Real.exp (Real.exp 20) ≤ x)
    (hc : 0 ≤ c) :
    (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
      ≤ (0.0895 * Real.exp c) ^ (1 / 2 : ℝ) * (∫ ω, ((Real.log (fracY x))⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (fracY x + 1)
                ((1 / 2 : ℂ) + ((c / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
              * ‖fracMellin (1 / 2 + ((c / Real.log x : ℝ) : ℂ) + t * Complex.I)‖ ^ 2)
                ^ (1 / 2 : ℝ) ∂μ)
        + 3 / Real.log x := by
  haveI := hX.isProbabilityMeasure
  obtain ⟨hx0, -, hL, hΛ, hexp⟩ := log_facts_of_exp_exp_twenty_le hx
  obtain ⟨hy2, hy1, hyL⟩ := fracY_facts hx
  obtain ⟨hθ, herr⟩ := fracSelberg_conditions hx
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hsx : Real.sqrt x = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, ← hLdef]
    ring_nf
  have hsx4 : 2 * L ^ 4 ≤ Real.sqrt x := by
    rw [hsx]
    exact two_mul_pow_four_le_exp_half (by linarith)
  have hη : 0 < (L ^ 3)⁻¹ := by positivity
  have hε : 0 < (Real.sqrt L)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hL0)
  have hη1 : (L ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hT₀ : 1 + (L ^ 3)⁻¹ < Real.sqrt x := by
    have : L ≤ L ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hT₀x : Real.sqrt x ≤ x := by
    have hx1 : 1 ≤ x := by
      have := Real.add_one_le_exp (Real.exp 20)
      have := Real.exp_pos 20
      linarith
    exact Real.sqrt_le_self_iff.2 (Or.inr hx1)
  have hσ : 0 ≤ c / L := div_nonneg hc hL0.le
  have hσlog : c / L * Real.log (x / Real.sqrt x) ≤ c / 2 := by
    rw [Real.div_sqrt, Real.log_sqrt hx0.le, ← hLdef]
    apply le_of_eq
    field_simp
  have hD : 1 ≤ Real.exp (L / 4) := Real.one_le_exp (by linarith)
  have hκy : (1 : ℝ) ≤ Real.log (fracY x) := by linarith
  have hmain := integral_norm_fracPartSum_le_explicit_selberg hX hy2 hT₀ hT₀x one_pos hκy hσ
    hσlog hη hε hD (by linarith) hθ herr
  -- the constant
  have hconst : fracReductionConst sieveConst (Real.sqrt x) (L ^ 3)⁻¹ (Real.sqrt L)⁻¹ (c / 2)
      ≤ 0.0895 * Real.exp c := by
    rw [fracReductionConst, show 2 * (c / 2) = c by ring]
    have hmid := fracReduction_middle_le hL hsx4
    have hsc := sieveConst_div_two_pi_le
    have hsc0 : 0 ≤ sieveConst / (2 * Real.pi) := div_nonneg sieveConst_pos.le (by positivity)
    have hec : 0 < Real.exp c := Real.exp_pos c
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have heq : (1 + (Real.sqrt L)⁻¹) * sieveConst
        * ((1 + (L ^ 3)⁻¹) ^ 2 * ((L ^ 3)⁻¹ / (1 + (L ^ 3)⁻¹) + 1 / Real.sqrt x) / (L ^ 3)⁻¹)
        * Real.exp c * (2 * Real.pi)⁻¹
        = ((1 + (Real.sqrt L)⁻¹) * ((1 + (L ^ 3)⁻¹) ^ 2 * ((L ^ 3)⁻¹ / (1 + (L ^ 3)⁻¹)
          + 1 / Real.sqrt x) / (L ^ 3)⁻¹)) * (sieveConst / (2 * Real.pi)) * Real.exp c := by
      field_simp
    rw [heq]
    have hmid0 : 0 ≤ (1 + (Real.sqrt L)⁻¹) * ((1 + (L ^ 3)⁻¹) ^ 2 * ((L ^ 3)⁻¹ / (1 + (L ^ 3)⁻¹)
        + 1 / Real.sqrt x) / (L ^ 3)⁻¹) := by positivity
    calc ((1 + (Real.sqrt L)⁻¹) * ((1 + (L ^ 3)⁻¹) ^ 2 * ((L ^ 3)⁻¹ / (1 + (L ^ 3)⁻¹)
          + 1 / Real.sqrt x) / (L ^ 3)⁻¹)) * (sieveConst / (2 * Real.pi)) * Real.exp c
        ≤ 1.0003 * (8947 / 100000) * Real.exp c := by gcongr
      _ ≤ 0.0895 * Real.exp c := by nlinarith
  have hCR0 : 0 ≤ fracReductionConst sieveConst (Real.sqrt x) (L ^ 3)⁻¹ (Real.sqrt L)⁻¹ (c / 2) :=
    fracReductionConst_nonneg sieveConst_pos.le (by positivity) hη hε
  have hZ0 : 0 ≤ ∫ ω, ((Real.log (fracY x))⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (fracY x + 1)
                ((1 / 2 : ℂ) + ((c / L : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
              * ‖fracMellin (1 / 2 + ((c / L : ℝ) : ℂ) + t * Complex.I)‖ ^ 2)
                ^ (1 / 2 : ℝ) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (mul_nonneg (inv_nonneg.2
      (Real.log_natCast_nonneg _)) (integral_nonneg fun t => by positivity)) _
  have hCRle : fracReductionConst sieveConst (Real.sqrt x) (L ^ 3)⁻¹ (Real.sqrt L)⁻¹ (c / 2)
      ^ (1 / 2 : ℝ) ≤ (0.0895 * Real.exp c) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hCR0 hconst (by norm_num)
  -- the errors
  have hS := fracSmoothErr_le_explicit hL hsx4
  have hlow := fracLowErr_le_explicit hx hy1 hyL
  have hS0 : 0 ≤ fracSmoothErr x (L ^ 3)⁻¹ (Real.sqrt L)⁻¹ := by
    rw [fracSmoothErr]
    have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    positivity
  have hlow0 : 0 ≤ fracLowErr x (Real.sqrt x) (fracY x) 1 := by
    rw [fracLowErr]
    have h1 : 0 ≤ 1 + Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt hx0.le, ← hLdef]
      linarith
    have h2 : 0 ≤ Real.log (fracY x) := Real.log_natCast_nonneg _
    positivity
  have hSq : fracSmoothErr x (L ^ 3)⁻¹ (Real.sqrt L)⁻¹ ^ (1 / 2 : ℝ) ≤ 2 / L := by
    calc fracSmoothErr x (L ^ 3)⁻¹ (Real.sqrt L)⁻¹ ^ (1 / 2 : ℝ)
        ≤ (4 / L ^ 2) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hS0 hS (by norm_num)
      _ = 2 / L := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hL0.le,
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hLq : fracLowErr x (Real.sqrt x) (fracY x) 1 ^ (1 / 2 : ℝ) ≤ 1 / L := by
    calc fracLowErr x (Real.sqrt x) (fracY x) 1 ^ (1 / 2 : ℝ)
        ≤ (1 / L ^ 2) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hlow0 hlow (by norm_num)
      _ = 1 / L := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hL0.le,
          Real.sqrt_one]
  have hCE := mul_le_mul_of_nonneg_right hCRle hZ0
  have hfin : 2 / L + 1 / L = 3 / L := by ring
  linarith

end RMF
