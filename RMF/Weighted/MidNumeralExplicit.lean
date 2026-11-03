/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.MidAssemblyExplicit
import RMF.Weighted.TenNumeralExplicit
import RMF.Weighted.FixedQUniformExplicit

/-!
# The first moment with the constant `10` for every `x ≥ 3`

* **The middle range** `exp(e⁷) ≤ x ≤ exp(e^{110})`: the pieces of
  `RMF.integral_norm_weightedRademacherSum_le_mid_assembly` (tail and error `≤ 1`, `C_R ≤ 0.76²`,
  `C_c ≤ 101.02Λ + 4.05`, every window `≤ 2.315`), then a quartic in `Λ^{1/4}`
  (`RMF.integral_norm_weightedRademacherSum_le_ten_mid`).
* **The small range** `3 ≤ x ≤ exp(e⁷)`: `E|S(x)| ≤ (1 + log x)^{1/2}` and
  `1 + L ≤ 100(log L)^{3/2}` on `[log 3, e⁷]`
  (`RMF.integral_norm_weightedRademacherSum_le_ten_small`).

Headline `RMF.integral_norm_weightedRademacherSum_le_ten_of_three_le`:
`E|∑_{n≤x} f(n)/√n| ≤ 10 (log log x)^{3/4}` for every `x ≥ 3`, with
`RMF.integral_norm_weightedRademacherSum_le_ten` beyond `exp(e^{110})`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The middle range's pieces -/

/-- `log 7 ≥ 1.9459`. -/
lemma log_seven_ge : (19459 / 10000 : ℝ) ≤ Real.log 7 := by
  interval_decide (trust := kernel)

/-- `Λ log Λ ≥ 2.9459Λ - 7` and `log Λ ≥ 1.9459` for `Λ ≥ 7`: `log(Λ/7) ≥ 1 - 7/Λ`. -/
lemma mul_log_ge_of_seven_le {Λ : ℝ} (hΛ : 7 ≤ Λ) :
    29459 / 10000 * Λ - 7 ≤ Λ * Real.log Λ ∧ 19459 / 10000 ≤ Real.log Λ := by
  have hΛ0 : 0 < Λ := by linarith
  have h7 := log_seven_ge
  have h1 := Real.one_sub_inv_le_log_of_pos (x := Λ / 7) (by positivity)
  rw [Real.log_div hΛ0.ne' (by norm_num), inv_div] at h1
  have h2 : Λ * (1 - 7 / Λ) = Λ - 7 := by field_simp
  have h3 := mul_le_mul_of_nonneg_left h1 hΛ0.le
  have h4 : Real.log 7 ≤ Real.log Λ := Real.log_le_log (by norm_num) hΛ
  constructor
  · nlinarith
  · linarith

/-- **The middle range's smooth tail is at most `1`**: Rankin at `κ = log Λ`
(`RMF.smoothTailSum_le_rankin_explicit`); `log x/log y ≥ Λ` and `log y ≤ e^{Λ - log Λ}` leave the
exponent `2.0375Λ + 0.3825 - (Λ + 1)log Λ < 0`. -/
lemma midTail_le_one {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) : midTail x ≤ 1 := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, ha, haL⟩ := mid_params hx
  obtain ⟨hy2, -, hlogy_le, hlogy_ge, -, -⟩ := midY_facts hx
  have hA := midA_mul hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hly : 144 ≤ Real.log (midY x) := by linarith
  have hlypos : 0 < Real.log (midY x) := by linarith
  obtain ⟨hlogmul, hlog⟩ := mul_log_ge_of_seven_le hΛ
  set Λ := Real.log (Real.log x) with hΛdef
  set ℓ := Real.log Λ with hℓdef
  have hℓ0 : 0 < ℓ := by linarith
  have h := smoothTailSum_le_rankin_explicit (y := midY x) hy2 hx0 hℓ0
  rw [hℓdef, Real.exp_log hΛpos, ← hℓdef] at h
  unfold midTail
  refine le_trans h ?_
  -- `log x/log y ≥ Λ`
  have hratio : Λ ≤ Real.log x / Real.log (midY x) := by
    rw [le_div_iff₀ hlypos]
    nlinarith
  have hl4 : Real.log 4 + 4 ≤ 54 / 10 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_lt_d9]
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hfrac : (Real.log 4 + 4) / Real.log (midY x) ≤ 375 / 10000 := by
    rw [div_le_iff₀ hlypos]
    linarith
  have hf0 : 0 ≤ (Real.log 4 + 4) / Real.log (midY x) := by positivity
  have e1 : (Λ - 1) * (1 + (Real.log 4 + 4) / Real.log (midY x)) ≤ (Λ - 1) * (1 + 375 / 10000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e2 : ℓ * Λ ≤ ℓ * Real.log x / Real.log (midY x) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hratio hℓ0.le
  -- `log y ≤ a = L/Λ = e^{Λ - ℓ}`
  have hly_le : Real.log (midY x) ≤ Real.exp (Λ - ℓ) := by
    rw [Real.exp_sub, hexpΛ, hℓdef, Real.exp_log hΛpos]
    have : midA x = Real.log x / Λ := by rw [midA]
    linarith
  calc Real.log (midY x) * Real.exp (1.42 + (Λ - 1) * (1 + (Real.log 4 + 4) / Real.log (midY x))
        - ℓ * Real.log x / Real.log (midY x))
      ≤ Real.exp (Λ - ℓ) * Real.exp (1.42 + (Λ - 1) * (1 + 375 / 10000) - ℓ * Λ) :=
        mul_le_mul hly_le (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (Λ - ℓ + (1.42 + (Λ - 1) * (1 + 375 / 10000) - ℓ * Λ)) := (Real.exp_add _ _).symm
    _ ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : Λ * ℓ = ℓ * Λ := mul_comm _ _
        nlinarith

/-- `e^{7/2} ≥ 33`. -/
lemma exp_seven_half_ge : (33 : ℝ) ≤ Real.exp (7 / 2) := by
  interval_decide (trust := kernel)

/-- **`√log x ≥ 4Λ` and `≥ 33`** for `x ≥ exp(e⁷)`: `e^{Λ/2} ≥ 33(1 + (Λ-7)/2)`. -/
lemma mid_sqrt_facts {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    Real.sqrt (Real.log x) = Real.exp (Real.log (Real.log x) / 2)
      ∧ 4 * Real.log (Real.log x) ≤ Real.sqrt (Real.log x) ∧ 33 ≤ Real.sqrt (Real.log x) := by
  obtain ⟨-, -, hΛ, hexpΛ, -, -⟩ := mid_params hx
  have hs : Real.sqrt (Real.log x) = Real.exp (Real.log (Real.log x) / 2) := by
    rw [Real.exp_half, hexpΛ]
  have h33 := exp_seven_half_ge
  have hsplit : Real.exp (Real.log (Real.log x) / 2)
      = Real.exp (7 / 2) * Real.exp ((Real.log (Real.log x) - 7) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hu := Real.add_one_le_exp ((Real.log (Real.log x) - 7) / 2)
  have hu0 : 0 ≤ (Real.log (Real.log x) - 7) / 2 := by linarith
  have hmono : 33 * ((Real.log (Real.log x) - 7) / 2 + 1)
      ≤ Real.exp (7 / 2) * Real.exp ((Real.log (Real.log x) - 7) / 2) :=
    mul_le_mul h33 hu (by linarith) (Real.exp_pos _).le
  refine ⟨hs, ?_, ?_⟩
  · rw [hs, hsplit]
    linarith
  · rw [hs, hsplit]
    linarith

/-- `u⁴e^{-u} ≤ 40320/u⁴` for `u > 0`, from `u⁸/8! ≤ e^u`. -/
lemma pow_four_mul_exp_neg_le {u : ℝ} (hu : 0 < u) :
    u ^ 4 * Real.exp (-u) ≤ 40320 / u ^ 4 := by
  have h := Real.pow_div_factorial_le_exp (x := u) hu.le 8
  have hf : ((Nat.factorial 8 : ℕ) : ℝ) = 40320 := by norm_num [Nat.factorial]
  rw [hf, div_le_iff₀ (by norm_num)] at h
  have he := Real.exp_pos u
  rw [le_div_iff₀ (by positivity), Real.exp_neg]
  rw [show u ^ 4 * (Real.exp u)⁻¹ * u ^ 4 = u ^ 8 / Real.exp u by field_simp,
    div_le_iff₀ he]
  linarith

/-- The `z`-part of the middle range's error: `(1+s)(1+η)·40L³e^{-6L/7} ≤ 10⁻⁴` for `L ≥ 1096`,
`s ≤ L`, `0 ≤ η ≤ 1`. -/
lemma mid_err_z {L s η : ℝ} (hL : 1096 ≤ L) (hsL : s ≤ L) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1) :
    (1 + s) * ((1 + η) * (40 * L ^ 3 * Real.exp (-(6 / 7 * L)))) ≤ 1 / 10000 := by
  have hu : (939 : ℝ) ≤ 6 / 7 * L := by linarith
  have hE := pow_four_mul_exp_neg_le (u := 6 / 7 * L) (by linarith)
  have hu4 : (939 : ℝ) ^ 4 ≤ (6 / 7 * L) ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have hEs : (6 / 7 * L) ^ 4 * Real.exp (-(6 / 7 * L)) ≤ 1 / 10000000 := by
    refine le_trans hE ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hexp0 := Real.exp_pos (-(6 / 7 * L))
  have h1 : (1 + s) * ((1 + η) * (40 * L ^ 3 * Real.exp (-(6 / 7 * L))))
      ≤ (2 * L) * (2 * (40 * L ^ 3 * Real.exp (-(6 / 7 * L)))) :=
    mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
      (by positivity) (by positivity)
  have h2 : (2 * L) * (2 * (40 * L ^ 3 * Real.exp (-(6 / 7 * L))))
      = 160 * (7 / 6) ^ 4 * ((6 / 7 * L) ^ 4 * Real.exp (-(6 / 7 * L))) := by ring
  rw [h2] at h1
  have := mul_le_mul_of_nonneg_left hEs (by norm_num : (0 : ℝ) ≤ 160 * (7 / 6) ^ 4)
  linarith

/-- The main part of the middle range's error: `(1+s)(1+η)·3.2801Λ/L ≤ 0.8449 + 3.2801η` for
`L = s²`, `s ≥ 33`, `0 ≤ 4Λ ≤ s`, `η ≥ 0`. -/
lemma mid_err_main {s L Λ η : ℝ} (hs33 : 33 ≤ s) (hsL : s ^ 2 = L) (hΛ0 : 0 ≤ Λ)
    (hΛs : 4 * Λ ≤ s) (hη0 : 0 ≤ η) :
    (1 + s) * ((1 + η) * (32801 / 10000 * Λ / L)) ≤ 8449 / 10000 + 32801 / 10000 * η := by
  have hs0 : 0 < s := by linarith
  rw [← hsL]
  have hkey : (1 + s) * (Λ / s ^ 2) ≤ 34 / 33 * (1 / 4) := by
    rw [show (1 + s) * (Λ / s ^ 2) = (Λ / s) * (1 + 1 / s) by field_simp; ring]
    have hΛs' : Λ / s ≤ 1 / 4 := by rw [div_le_iff₀ hs0]; linarith
    have h1s : 1 + 1 / s ≤ 34 / 33 := by
      have : 1 / s ≤ 1 / 33 := one_div_le_one_div_of_le (by norm_num) hs33
      linarith
    have hΛs0 : 0 ≤ Λ / s := by positivity
    calc Λ / s * (1 + 1 / s) ≤ 1 / 4 * (34 / 33) :=
          mul_le_mul hΛs' h1s (by positivity) (by norm_num)
      _ = 34 / 33 * (1 / 4) := by ring
  have e : (1 + s) * ((1 + η) * (32801 / 10000 * Λ / s ^ 2))
      = 32801 / 10000 * (1 + η) * ((1 + s) * (Λ / s ^ 2)) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ 32801 / 10000 * (1 + η))
  linarith

/-- `(1+s)·2/L² ≤ 1/5000` for `L = s²`, `s ≥ 33`. -/
lemma mid_err_small {s L : ℝ} (hs33 : 33 ≤ s) (hsL : s ^ 2 = L) :
    (1 + s) * (2 / L ^ 2) ≤ 1 / 5000 := by
  rw [← hsL, mul_div_assoc', div_le_iff₀ (by positivity)]
  have h33 : (33 : ℝ) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) hs33 3
  have h4 := mul_le_mul_of_nonneg_left h33 (by linarith : (0 : ℝ) ≤ s)
  have e : s * s ^ 3 = (s ^ 2) ^ 2 := by ring
  rw [e] at h4
  nlinarith

/-- The error's combination: `(1+s)(E_η + (1+η)(t + z)) ≤ 1` from the three bounds. -/
lemma mid_err_combine {s η Eη A t B zt C : ℝ} (hs0 : 0 ≤ s) (hη0 : 0 ≤ η)
    (hηs : η ≤ 1 / 1000000) (hEη : Eη ≤ A) (ht : t ≤ B) (hz : zt ≤ C)
    (hA : (1 + s) * A ≤ 1 / 5000) (hB : (1 + s) * ((1 + η) * B) ≤ 8449 / 10000 + 32801 / 10000 * η)
    (hC : (1 + s) * ((1 + η) * C) ≤ 1 / 10000) :
    (1 + s) * (Eη + (1 + η) * (t + zt)) ≤ 1 := by
  have h1 : Eη + (1 + η) * (t + zt) ≤ A + (1 + η) * (B + C) :=
    add_le_add hEη (mul_le_mul_of_nonneg_left (add_le_add ht hz) (by linarith))
  have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + s)
  have e : (1 + s) * (A + (1 + η) * (B + C))
      = (1 + s) * A + (1 + s) * ((1 + η) * B) + (1 + s) * ((1 + η) * C) := by ring
  linarith

/-- **The middle range's reduction error is at most `1`**:
`(1 + √L)(η(1 + L) + (1 + η)(2/log z + 5z(1 + log z)³/x))` with `log z ≥ 0.60975a`, `a = L/Λ`,
`Λ ≤ √L/4` and `z ≤ e^{L/7}` (`RMF.mid_err_main`, `RMF.mid_err_z`, `RMF.mid_err_small`). -/
lemma midErr_le_one {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    smallQReductionErr x (midZ x) (halfEta x) (halfEps x) ≤ 1 := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, ha, haL⟩ := mid_params hx
  obtain ⟨hz2, -, hlogz⟩ := midZ_facts hx
  obtain ⟨-, hs4, hs33⟩ := mid_sqrt_facts hx
  have hA := midA_mul hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  have hl2' : Real.log 2 ≤ 6932 / 10000 := by linarith [Real.log_two_lt_d9]
  have hsq : Real.sqrt (Real.log x) ^ 2 = Real.log x := Real.sq_sqrt hLpos.le
  have hε : 1 / halfEps x = Real.sqrt (Real.log x) := by rw [halfEps, one_div, inv_inv]
  have hL1096 : 1096 ≤ Real.log x := le_trans exp_seven_ge_1096 hL
  have hL1 : 1 ≤ Real.log x := by linarith
  -- `η(1 + L) ≤ 2/L²`, `0 ≤ η ≤ 10⁻⁶`
  have hη2 : halfEta x * (1 + Real.log x) ≤ 2 / Real.log x ^ 2 := by
    rw [halfEta, inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ Real.log x ^ 2 := sq_nonneg _
    nlinarith
  have hη0 : 0 ≤ halfEta x := by rw [halfEta]; positivity
  have hηsmall : halfEta x ≤ 1 / 1000000 := by
    rw [halfEta, inv_le_comm₀ (by positivity) (by norm_num)]
    have h3 : (1096 : ℝ) ^ 3 ≤ Real.log x ^ 3 := pow_le_pow_left₀ (by norm_num) hL1096 3
    norm_num at h3 ⊢
    linarith
  -- `2/log z ≤ 3.2801Λ/L`
  have hlogz' : 60975 / 100000 * midA x ≤ Real.log (midZ x) := by linarith
  have hlogz0 : 0 < Real.log (midZ x) := by linarith
  have t1 : 2 / Real.log (midZ x) ≤ 32801 / 10000 * Real.log (Real.log x) / Real.log x := by
    rw [div_le_div_iff₀ hlogz0 hLpos]
    have hm := mul_le_mul_of_nonneg_left hlogz' hΛpos.le
    have e : Real.log (Real.log x) * (60975 / 100000 * midA x) = 60975 / 100000 * Real.log x := by
      calc Real.log (Real.log x) * (60975 / 100000 * midA x)
          = 60975 / 100000 * (midA x * Real.log (Real.log x)) := by ring
        _ = 60975 / 100000 * Real.log x := by rw [hA]
    nlinarith
  -- `5z(1+log z)³/x ≤ 40L³e^{-6L/7}`
  have hzle : (midZ x : ℝ) ≤ Real.exp (midA x) :=
    le_trans (Nat.floor_le (Real.exp_pos _).le) (Real.exp_le_exp.2 (by linarith))
  have hz0 : (0 : ℝ) < (midZ x : ℝ) := by
    have : (2 : ℝ) ≤ (midZ x : ℝ) := by exact_mod_cast hz2
    linarith
  have hlogzle : Real.log (midZ x) ≤ midA x :=
    le_trans (Real.log_le_log hz0 hzle) (le_of_eq (Real.log_exp _))
  have ha7 : midA x ≤ Real.log x / 7 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hcube : (1 + Real.log (midZ x)) ^ 3 ≤ (2 * Real.log x) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hxe : Real.exp (Real.log x) = x := Real.exp_log hx0
  have h2 : Real.exp (midA x) ≤ Real.exp (-(6 / 7 * Real.log x)) * x := by
    calc Real.exp (midA x) ≤ Real.exp (-(6 / 7 * Real.log x) + Real.log x) :=
          Real.exp_le_exp.2 (by linarith)
      _ = Real.exp (-(6 / 7 * Real.log x)) * x := by rw [Real.exp_add, hxe]
  have t2 : 5 * (midZ x : ℝ) * (1 + Real.log (midZ x)) ^ 3 / x
      ≤ 40 * Real.log x ^ 3 * Real.exp (-(6 / 7 * Real.log x)) := by
    rw [div_le_iff₀ hx0]
    calc 5 * (midZ x : ℝ) * (1 + Real.log (midZ x)) ^ 3
        ≤ 5 * (Real.exp (-(6 / 7 * Real.log x)) * x) * (2 * Real.log x) ^ 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (le_trans hzle h2) (by norm_num)) hcube
            (by positivity) (by positivity)
      _ = 40 * Real.log x ^ 3 * Real.exp (-(6 / 7 * Real.log x)) * x := by ring
  have hs0 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hsL : Real.sqrt (Real.log x) ≤ Real.log x := by nlinarith
  have hB := mid_err_main hs33 hsq hΛpos.le hs4 hη0
  have hC := mid_err_z hL1096 hsL hη0 (by linarith)
  have hAs := mid_err_small hs33 hsq
  unfold smallQReductionErr
  rw [hε]
  exact mid_err_combine hs0 hη0 hηsmall hη2 t1 t2 hAs hB hC

/-- `2 log y/log z ≤ 3.2801` in the middle range: `log y ≤ a`, `log z ≥ 0.60975a`. -/
lemma mid_ratio_le {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    2 * Real.log (midY x) / Real.log (midZ x) ≤ 32801 / 10000 := by
  obtain ⟨-, -, hΛ, -, ha, -⟩ := mid_params hx
  obtain ⟨-, -, hlogy_le, -, -, -⟩ := midY_facts hx
  obtain ⟨-, -, hlogz⟩ := midZ_facts hx
  have hl2' : Real.log 2 ≤ 6932 / 10000 := by linarith [Real.log_two_lt_d9]
  have hlogz' : 60975 / 100000 * midA x ≤ Real.log (midZ x) := by linarith
  have hlogz0 : 0 < Real.log (midZ x) := by linarith
  rw [div_le_iff₀ hlogz0]
  linarith

/-- `5z(1+log z)³ log y (1+η)/(yη + 1 + η) ≤ 10⁻⁴` in the middle range: `z e^{8Λ} ≤ 2y`,
`1 + log z ≤ 2a`, `a ≤ L/7`, so the ratio is `≤ 160/(2401 L)`. -/
lemma mid_second_le {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    5 * (midZ x : ℝ) * (1 + Real.log (midZ x)) ^ 3 * Real.log (midY x) * (1 + halfEta x)
      / ((midY x : ℝ) * halfEta x + 1 + halfEta x) ≤ 1 / 10000 := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, ha, haL⟩ := mid_params hx
  obtain ⟨hy2, -, hlogy_le, -, -, hyh⟩ := midY_facts hx
  obtain ⟨hz2, -, -⟩ := midZ_facts hx
  have hA := midA_mul hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hL1096 : 1096 ≤ Real.log x := le_trans exp_seven_ge_1096 hL
  have hy2R : (2 : ℝ) ≤ (midY x : ℝ) := by exact_mod_cast hy2
  have hz2R : (2 : ℝ) ≤ (midZ x : ℝ) := by exact_mod_cast hz2
  have hy0 : (0 : ℝ) < (midY x : ℝ) := by linarith
  have hz0 : (0 : ℝ) < (midZ x : ℝ) := by linarith
  have hly0 : 0 ≤ Real.log (midY x) := Real.log_nonneg (by linarith)
  have hzle : (midZ x : ℝ) ≤ Real.exp (midA x - 8 * Real.log (Real.log x)) :=
    Nat.floor_le (Real.exp_pos _).le
  have hlogzle : Real.log (midZ x) ≤ midA x := by
    have h1 := Real.log_le_log hz0 hzle
    rw [Real.log_exp] at h1
    linarith
  have hlogz0 : 0 ≤ Real.log (midZ x) := Real.log_nonneg (by linarith)
  have hη0 : 0 < halfEta x := by rw [halfEta]; positivity
  have hηL : halfEta x * Real.log x ^ 3 = 1 := by rw [halfEta]; field_simp
  have hη1 : halfEta x ≤ 1 := by
    rw [halfEta]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  -- `z L⁸ ≤ 2y`
  have hL8 : Real.exp (8 * Real.log (Real.log x)) = Real.log x ^ 8 := by
    rw [show (8 : ℝ) * Real.log (Real.log x) = ((8 : ℕ) : ℝ) * Real.log (Real.log x) by norm_num,
      Real.exp_nat_mul, hexpΛ]
  have hzy2 : (midZ x : ℝ) * Real.log x ^ 8 ≤ 2 * (midY x : ℝ) := by
    rw [← hL8]
    calc (midZ x : ℝ) * Real.exp (8 * Real.log (Real.log x))
        ≤ Real.exp (midA x - 8 * Real.log (Real.log x)) * Real.exp (8 * Real.log (Real.log x)) :=
          mul_le_mul_of_nonneg_right hzle (Real.exp_pos _).le
      _ = Real.exp (midA x) := by rw [← Real.exp_add]; ring_nf
      _ ≤ 2 * (midY x : ℝ) := by linarith
  -- numerator `≤ 80 z a⁴ ≤ (80/2401) z L⁴`
  have ha7 : 7 * midA x ≤ Real.log x := by nlinarith
  have ha0 : 0 ≤ midA x := by linarith
  have hnum : 5 * (midZ x : ℝ) * (1 + Real.log (midZ x)) ^ 3 * Real.log (midY x) * (1 + halfEta x)
      ≤ 80 / 2401 * ((midZ x : ℝ) * Real.log x ^ 4) := by
    have h1 : (1 + Real.log (midZ x)) ^ 3 ≤ (2 * midA x) ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 3
    have h2 : 5 * (midZ x : ℝ) * (1 + Real.log (midZ x)) ^ 3 * Real.log (midY x) * (1 + halfEta x)
        ≤ 5 * (midZ x : ℝ) * (2 * midA x) ^ 3 * midA x * 2 :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) hlogy_le hly0
        (by positivity)) (by linarith) (by linarith) (by positivity)
    have h3 : (7 * midA x) ^ 4 ≤ Real.log x ^ 4 := pow_le_pow_left₀ (by positivity) ha7 4
    have e : 5 * (midZ x : ℝ) * (2 * midA x) ^ 3 * midA x * 2
        = 80 / 2401 * ((midZ x : ℝ) * (7 * midA x) ^ 4) := by ring
    rw [e] at h2
    have := mul_le_mul_of_nonneg_left h3 hz0.le
    nlinarith
  -- `(80/2401) z L⁴ ≤ 10⁻⁴ yη`: times `L³`, from `z L⁸ ≤ 2y` and `L ≥ 1096`
  have hden : (midY x : ℝ) * halfEta x ≤ (midY x : ℝ) * halfEta x + 1 + halfEta x := by linarith
  have hB : 80 / 2401 * ((midZ x : ℝ) * Real.log x ^ 4)
      ≤ 1 / 10000 * ((midY x : ℝ) * halfEta x) := by
    have hpos : 0 < Real.log x ^ 3 := by positivity
    refine le_of_mul_le_mul_right ?_ hpos
    have e1 : 80 / 2401 * ((midZ x : ℝ) * Real.log x ^ 4) * Real.log x ^ 3
        = 80 / 2401 * ((midZ x : ℝ) * Real.log x ^ 8) / Real.log x := by
      field_simp
    have e2 : 1 / 10000 * ((midY x : ℝ) * halfEta x) * Real.log x ^ 3
        = 1 / 10000 * (midY x : ℝ) * (halfEta x * Real.log x ^ 3) := by ring
    rw [e1, e2, hηL, div_le_iff₀ hLpos]
    have := mul_le_mul_of_nonneg_left hzy2 (by norm_num : (0 : ℝ) ≤ 80 / 2401)
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- `(1+η)²(η/(1+η) + 1/y)/η ≤ 1 + 2·10⁻⁶` in the middle range: `yη ≥ e^{20}/2`. -/
lemma mid_mid_le {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    (1 + halfEta x) ^ 2 * (halfEta x / (1 + halfEta x) + 1 / (midY x : ℝ)) / halfEta x
      ≤ 1 + 2 / 1000000 := by
  obtain ⟨-, hL, hΛ, hexpΛ, ha, -⟩ := mid_params hx
  obtain ⟨hy2, -, -, -, -, hyh⟩ := midY_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hL1096 : 1096 ≤ Real.log x := le_trans exp_seven_ge_1096 hL
  have hy0 : (0 : ℝ) < (midY x : ℝ) := by
    have : (2 : ℝ) ≤ (midY x : ℝ) := by exact_mod_cast hy2
    linarith
  have hη0 : 0 < halfEta x := by rw [halfEta]; positivity
  have hηL : halfEta x * Real.log x ^ 3 = 1 := by rw [halfEta]; field_simp
  have hη : halfEta x ≤ 1 / 1000000 := by
    rw [halfEta, inv_le_comm₀ (by positivity) (by norm_num)]
    have h3 : (1096 : ℝ) ^ 3 ≤ Real.log x ^ 3 := pow_le_pow_left₀ (by norm_num) hL1096 3
    norm_num at h3 ⊢
    linarith
  have e1 : (1 + halfEta x) ^ 2 * (halfEta x / (1 + halfEta x) + 1 / (midY x : ℝ))
      / halfEta x = (1 + halfEta x) + (1 + halfEta x) ^ 2 / ((midY x : ℝ) * halfEta x) := by
    field_simp
  rw [e1]
  -- `y ≥ e^a/2 ≥ e^{20}L³/2`
  have hL3 : Real.exp (3 * Real.log (Real.log x)) = Real.log x ^ 3 := by
    rw [show (3 : ℝ) * Real.log (Real.log x) = ((3 : ℕ) : ℝ) * Real.log (Real.log x) by norm_num,
      Real.exp_nat_mul, hexpΛ]
  have hyL : 4000000 * Real.log x ^ 3 ≤ (midY x : ℝ) := by
    rw [← hL3]
    have h3 : (8000000 : ℝ) ≤ Real.exp 20 := by interval_decide (trust := kernel)
    have h2 : (8000000 : ℝ) * Real.exp (3 * Real.log (Real.log x)) ≤ Real.exp (midA x) :=
      calc (8000000 : ℝ) * Real.exp (3 * Real.log (Real.log x))
          ≤ Real.exp 20 * Real.exp (3 * Real.log (Real.log x)) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ = Real.exp (20 + 3 * Real.log (Real.log x)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (midA x) := Real.exp_le_exp.2 (by linarith)
    linarith
  have hyη : 4000000 ≤ (midY x : ℝ) * halfEta x := by
    have := mul_le_mul_of_nonneg_right hyL hη0.le
    calc (4000000 : ℝ) = 4000000 * (halfEta x * Real.log x ^ 3) := by rw [hηL]; ring
      _ = 4000000 * Real.log x ^ 3 * halfEta x := by ring
      _ ≤ (midY x : ℝ) * halfEta x := this
  have h1 : (1 + halfEta x) ^ 2 / ((midY x : ℝ) * halfEta x) ≤ 1 / 1000000 := by
    rw [div_le_iff₀ (by positivity)]
    have h4 : (1 + halfEta x) ^ 2 ≤ 4 := by nlinarith
    nlinarith
  linarith

/-- **The middle range's reduction constant**: `C_R ≤ 0.5776 = 0.76²`. -/
lemma midCR_le {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    smallQReductionConst (midY x) (midZ x) (halfEta x) (halfEps x) (1 / 32) ≤ 5776 / 10000 := by
  obtain ⟨-, hL, -, -, -, -⟩ := mid_params hx
  obtain ⟨-, -, hs33⟩ := mid_sqrt_facts hx
  obtain ⟨hz2, hzy, -⟩ := midZ_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hη0 : 0 < halfEta x := by rw [halfEta]; positivity
  have hε0 : 0 < halfEps x := by rw [halfEps]; positivity
  have hε : halfEps x ≤ 1 / 33 := by
    rw [halfEps, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hs33
  have hsieve : smallQSieveConst (midY x) (midZ x) (halfEta x) ≤ 32802 / 10000 := by
    have h1 := mid_ratio_le hx
    have h2 := mid_second_le hx
    rw [smallQSieveConst]
    linarith
  have hmid := mid_mid_le hx
  have hmid0 : 0 ≤ (1 + halfEta x) ^ 2 * (halfEta x / (1 + halfEta x) + 1 / (midY x : ℝ))
      / halfEta x := by positivity
  have hsieve0 : 0 ≤ smallQSieveConst (midY x) (midZ x) (halfEta x) :=
    (smallQSieveConst_pos hz2 hzy hη0).le
  have hpi := Real.pi_gt_d6
  have hinvpi : (2 * Real.pi)⁻¹ ≤ 1 / (2 * 3.141592) := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hexp : Real.exp (2 * (1 / 32)) ≤ 1064495 / 1000000 := by
    interval_decide (trust := kernel)
  unfold smallQReductionConst
  calc (1 + halfEps x) * smallQSieveConst (midY x) (midZ x) (halfEta x)
        * ((1 + halfEta x) ^ 2 * (halfEta x / (1 + halfEta x) + 1 / (midY x : ℝ)) / halfEta x)
        * Real.exp (2 * (1 / 32)) * (2 * Real.pi)⁻¹
      ≤ (1 + 1 / 33) * (32802 / 10000) * (1 + 2 / 1000000) * (1064495 / 1000000)
        * (1 / (2 * 3.141592)) := by
        gcongr
    _ ≤ 5776 / 10000 := by norm_num

/-! ### The middle range's central window and windows -/

/-- **The middle range's central window**: `C_c ≤ 101.02Λ + 4.05`:
`π/(σ log y) ≤ 32πΛ·a/(a - log 2)` and, with `u = w log y ≤ 3/2` and
`S₂(y+1) ≤ 0.62(log y)²`, `2(e^{S₂w²} - 1)/(w log y) ≤ (4/3)(e^{1.395} - 1)`. -/
lemma midCen_le {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    midCen x ≤ 10102 / 100 * Real.log (Real.log x) + 405 / 100 := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, ha, -⟩ := mid_params hx
  obtain ⟨hy2, -, hlogy_le, hlogy_ge, -, -⟩ := midY_facts hx
  have hA := midA_mul hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  have hl2 : Real.log 2 ≤ 6932 / 10000 := by linarith [Real.log_two_lt_d9]
  have hly : 144 ≤ Real.log (midY x) := by linarith
  have hlypos : 0 < Real.log (midY x) := by linarith
  unfold midCen
  rw [add_div]
  -- the first part
  have hp1 : Real.pi / halfSigma x / Real.log (midY x) ≤ 10102 / 100 * Real.log (Real.log x) := by
    have e1 : Real.pi / halfSigma x = 32 * Real.pi * Real.log x := by
      rw [halfSigma]
      field_simp
    rw [e1, div_le_iff₀ hlypos]
    have hpi := Real.pi_lt_d6
    have h1 := mul_le_mul_of_nonneg_left hlogy_ge hΛpos.le
    have e2 : Real.log (Real.log x) * (midA x - Real.log 2)
        = Real.log x - Real.log (Real.log x) * Real.log 2 := by
      calc Real.log (Real.log x) * (midA x - Real.log 2)
          = midA x * Real.log (Real.log x) - Real.log (Real.log x) * Real.log 2 := by ring
        _ = Real.log x - Real.log (Real.log x) * Real.log 2 := by rw [hA]
    rw [e2] at h1
    have hLΛ : 145 * Real.log (Real.log x) ≤ Real.log x := by
      calc 145 * Real.log (Real.log x) ≤ midA x * Real.log (Real.log x) :=
            mul_le_mul_of_nonneg_right (by linarith) hΛpos.le
        _ = Real.log x := hA
    have hl2Λ : Real.log (Real.log x) * Real.log 2 ≤ Real.log (Real.log x) * (6932 / 10000) :=
      mul_le_mul_of_nonneg_left hl2 hΛpos.le
    nlinarith
  -- the second part
  have hw0 : 0 < Real.exp (-((midJ x : ℕ) : ℝ)) := Real.exp_pos _
  have hwly : Real.exp (-((midJ x : ℕ) : ℝ)) * Real.log (midY x) ≤ 3 / 2 := by
    have h23 : 0 < 2 / 3 * Real.log (midY x) := by positivity
    have hJ : Real.log (2 / 3 * Real.log (midY x)) ≤ ((midJ x : ℕ) : ℝ) := by
      rw [midJ]
      push_cast
      exact (Nat.lt_floor_add_one _).le
    calc Real.exp (-((midJ x : ℕ) : ℝ)) * Real.log (midY x)
        ≤ Real.exp (-Real.log (2 / 3 * Real.log (midY x))) * Real.log (midY x) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hlypos.le
      _ = 3 / 2 := by
          rw [Real.exp_neg, Real.exp_log h23]
          field_simp
  have hS : Real.log ((midY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((midY x : ℝ) + 1) + 34
      ≤ 62 / 100 * Real.log (midY x) ^ 2 := by
    have hy0 : (0 : ℝ) < (midY x : ℝ) := by
      have : (2 : ℝ) ≤ (midY x : ℝ) := by exact_mod_cast hy2
      linarith
    have h1 : Real.log ((midY x : ℝ) + 1) ≤ Real.log (midY x) + 1 := by
      have h2 : Real.log ((midY x : ℝ) + 1) ≤ Real.log (2 * (midY x : ℝ)) :=
        Real.log_le_log (by positivity) (by
          have : (1 : ℝ) ≤ (midY x : ℝ) := by exact_mod_cast (by omega : 1 ≤ midY x)
          linarith)
      rw [Real.log_mul (by norm_num) hy0.ne'] at h2
      linarith
    have h0 : 0 ≤ Real.log ((midY x : ℝ) + 1) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ (midY x : ℝ) := hy0.le
      linarith)
    have h3 : Real.log ((midY x : ℝ) + 1) ^ 2 ≤ (Real.log (midY x) + 1) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    nlinarith
  set w := Real.exp (-((midJ x : ℕ) : ℝ)) with hwdef
  set ly := Real.log (midY x) with hlydef
  set S₂ := Real.log ((midY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((midY x : ℝ) + 1) + 34
    with hS₂def
  have hS0 : 0 ≤ S₂ := by
    rw [hS₂def]
    have h0 : 0 ≤ Real.log ((midY x : ℝ) + 1) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ (midY x : ℝ) := Nat.cast_nonneg _
      linarith)
    positivity
  have hκ0 : 0 ≤ 9 / 4 * (S₂ / ly ^ 2) := by positivity
  have hκ : 9 / 4 * (S₂ / ly ^ 2) ≤ 1395 / 1000 := by
    have : S₂ / ly ^ 2 ≤ 62 / 100 := by
      rw [div_le_iff₀ (by positivity)]
      exact hS
    linarith
  have hwl0 : 0 ≤ w * ly := by positivity
  have hs0 : 0 ≤ (w * ly) ^ 2 / (9 / 4) := by positivity
  have hs1 : (w * ly) ^ 2 / (9 / 4) ≤ 1 := by
    rw [div_le_one (by norm_num)]
    have := pow_le_pow_left₀ hwl0 hwly 2
    linarith [show ((3 : ℝ) / 2) ^ 2 = 9 / 4 by norm_num]
  have hconv := exp_mul_le_one_add_mul (x := 9 / 4 * (S₂ / ly ^ 2)) hs0 hs1
  have hexp1 : S₂ * w ^ 2 = (w * ly) ^ 2 / (9 / 4) * (9 / 4 * (S₂ / ly ^ 2)) := by
    field_simp
  have hek : Real.exp (9 / 4 * (S₂ / ly ^ 2)) - 1 ≤ 30351 / 10000 := by
    have : Real.exp (1395 / 1000) ≤ 40351 / 10000 := by interval_decide (trust := kernel)
    linarith [Real.exp_le_exp.2 hκ]
  have hp2 : 2 * (Real.exp (2 * (1 - 1 / 2) * S₂ * w ^ 2) - 1) / w / ly ≤ 405 / 100 := by
    rw [show (2 : ℝ) * (1 - 1 / 2) * S₂ * w ^ 2 = S₂ * w ^ 2 by ring, hexp1, div_div,
      div_le_iff₀ (by positivity)]
    have h1 : Real.exp ((w * ly) ^ 2 / (9 / 4) * (9 / 4 * (S₂ / ly ^ 2))) - 1
        ≤ (w * ly) ^ 2 / (9 / 4) * (Real.exp (9 / 4 * (S₂ / ly ^ 2)) - 1) := by linarith
    have h2 : (w * ly) ^ 2 / (9 / 4) * (Real.exp (9 / 4 * (S₂ / ly ^ 2)) - 1)
        ≤ (w * ly) * (3 / 2) / (9 / 4) * (30351 / 10000) := by
      have hsq : (w * ly) ^ 2 ≤ (w * ly) * (3 / 2) := by
        rw [sq]
        exact mul_le_mul_of_nonneg_left hwly hwl0
      calc (w * ly) ^ 2 / (9 / 4) * (Real.exp (9 / 4 * (S₂ / ly ^ 2)) - 1)
          ≤ (w * ly) ^ 2 / (9 / 4) * (30351 / 10000) :=
            mul_le_mul_of_nonneg_left hek hs0
        _ ≤ (w * ly) * (3 / 2) / (9 / 4) * (30351 / 10000) := by
            have := div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 9 / 4)
            linarith
    linarith
  linarith

/-- `C_c^{1/2} ≤ 10.051√Λ + 0.21` in the middle range. -/
lemma midCen_rpow_le {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    midCen x ^ (1 / 2 : ℝ) ≤ 10051 / 1000 * Real.sqrt (Real.log (Real.log x)) + 21 / 100 := by
  obtain ⟨-, -, hΛ, -, -, -⟩ := mid_params hx
  have hC := midCen_le hx
  have hsq : Real.sqrt (Real.log (Real.log x)) ^ 2 = Real.log (Real.log x) :=
    Real.sq_sqrt (by linarith)
  have hs2 : 2 ≤ Real.sqrt (Real.log (Real.log x)) := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  refine rpow_half_le_of_le (by positivity) ?_
  nlinarith

lemma midCen_nonneg {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) : 0 ≤ midCen x := by
  obtain ⟨-, hL, hΛ, -, ha, -⟩ := mid_params hx
  obtain ⟨-, -, -, hlogy_ge, -, -⟩ := midY_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hσ : 0 < halfSigma x := by rw [halfSigma]; positivity
  have he : 0 ≤ Real.exp (2 * (1 - 1 / 2)
      * (Real.log ((midY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((midY x : ℝ) + 1) + 34)
      * Real.exp (-((midJ x : ℕ) : ℝ)) ^ 2) - 1 := by
    have h0 : 0 ≤ Real.log ((midY x : ℝ) + 1) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ (midY x : ℝ) := Nat.cast_nonneg _
      linarith)
    have : 0 ≤ 2 * (1 - 1 / 2)
        * (Real.log ((midY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((midY x : ℝ) + 1) + 34)
        * Real.exp (-((midJ x : ℕ) : ℝ)) ^ 2 := by positivity
    linarith [Real.one_le_exp this]
  unfold midCen
  have : 0 < Real.log (midY x) := by linarith
  positivity

/-- **`G_k ≤ 2.315` for every window at slope `3/2`**, `k ≥ 4`, `log y ≥ 144`. -/
lemma thetaWindowConst_rpow_le_mid {k y : ℕ} (hk : 4 ≤ k) (hy : 144 ≤ Real.log y) :
    thetaWindowConst (3 / 2) k y ^ (1 / 2 : ℝ) ≤ 2315 / 1000 := by
  have hE := exp_neg_four_le_sharp
  have hE0 := (Real.exp_pos (-4)).le
  have hb : thetaWindowExp (3 / 2) 4 ≤ 1549 / 1000 := by
    unfold thetaWindowExp
    push_cast
    nlinarith [mul_le_mul hE hE hE0 (by norm_num)]
  have hc : 9.0028 / 144 + 9.0028 * Real.exp (-((4 : ℕ) : ℝ)) / (3 / 2) ≤ 1725 / 10000 := by
    push_cast
    nlinarith
  refine rpow_half_le_of_le (by norm_num) ?_
  refine le_trans (thetaWindowConst_le_num hk (by norm_num) hy hb hc) ?_
  interval_decide (trust := kernel)

/-- **The middle range's windows**: `∑_{4≤k<J₀} G_k ≤ 2.315(Λ - 4)`, since
`J₀ ≤ log(log y) + 1 ≤ Λ - log Λ + 1`. -/
lemma midMeso_le {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    ∑ k ∈ Finset.Ico 4 (midJ x), thetaWindowConst (3 / 2) k (midY x) ^ (1 / 2 : ℝ)
      ≤ 2315 / 1000 * (Real.log (Real.log x) - 4) := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, ha, -⟩ := mid_params hx
  obtain ⟨hy2, -, hlogy_le, hlogy_ge, -, -⟩ := midY_facts hx
  obtain ⟨-, hlog⟩ := mul_log_ge_of_seven_le hΛ
  have hA := midA_mul hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hly : 144 ≤ Real.log (midY x) := by linarith
  have h1 : ∑ k ∈ Finset.Ico 4 (midJ x), thetaWindowConst (3 / 2) k (midY x) ^ (1 / 2 : ℝ)
      ≤ ∑ _k ∈ Finset.Ico 4 (midJ x), (2315 / 1000 : ℝ) :=
    Finset.sum_le_sum fun k hk => thetaWindowConst_rpow_le_mid (Finset.mem_Ico.1 hk).1 hly
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h1
  -- `J₀ ≤ log(log y) + 1 ≤ log a + 1 = Λ - log Λ + 1`
  have h23 : 0 < 2 / 3 * Real.log (midY x) := by positivity
  have hJ : ((midJ x : ℕ) : ℝ) ≤ Real.log (Real.log x) - Real.log (Real.log (Real.log x)) + 1 := by
    have hfl : (⌊Real.log (2 / 3 * Real.log (midY x))⌋₊ : ℝ)
        ≤ Real.log (2 / 3 * Real.log (midY x)) :=
      Nat.floor_le (Real.log_nonneg (by nlinarith))
    have hla : Real.log (2 / 3 * Real.log (midY x)) ≤ Real.log (midA x) :=
      Real.log_le_log h23 (by linarith)
    have hlog_a : Real.log (midA x) = Real.log (Real.log x) - Real.log (Real.log (Real.log x)) := by
      rw [midA, Real.log_div hLpos.ne' hΛpos.ne']
    rw [midJ]
    push_cast
    linarith
  have hcnt : ((midJ x - 4 : ℕ) : ℝ) ≤ Real.log (Real.log x) - 4 := by
    rcases le_total (midJ x) 4 with h | h
    · rw [Nat.sub_eq_zero_of_le h]
      push_cast
      linarith
    · rw [Nat.cast_sub h]
      push_cast
      linarith
  calc ∑ k ∈ Finset.Ico 4 (midJ x), thetaWindowConst (3 / 2) k (midY x) ^ (1 / 2 : ℝ)
      ≤ ((midJ x - 4 : ℕ) : ℝ) * (2315 / 1000) := h1
    _ ≤ 2315 / 1000 * (Real.log (Real.log x) - 4) := by nlinarith

/-! ### The theorems -/

/-- **The first moment at `q = ½` with the constant `10` in the middle range**: for
`exp(e⁷) ≤ x ≤ exp(e^{110})`, `E|S(x)| ≤ 10 (log log x)^{3/4}`.
`RMF.integral_norm_weightedRademacherSum_le_mid_assembly` with its pieces evaluated: `T ≤ 1`,
`E_err ≤ 1`, `C_R ≤ 0.76²`, `C_c^{1/2} ≤ 10.051√Λ + 0.21`, the far range `≤ 11.43` and the windows
`≤ 2.315(Λ - 4)`; the final inequality in `s = Λ^{1/4} ∈ [1.62, 3.24]`. -/
theorem integral_norm_weightedRademacherSum_le_ten_mid {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x)
    (hx' : x ≤ Real.exp (Real.exp 110)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
      ≤ 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
  have h := integral_norm_weightedRademacherSum_le_mid_assembly hX hx
  obtain ⟨hx0, hL, hΛ, -, -, -⟩ := mid_params hx
  obtain ⟨hz2, hzy, -⟩ := midZ_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛ110 : Real.log (Real.log x) ≤ 110 := by
    have h1 : Real.log x ≤ Real.exp 110 := by
      rw [Real.log_le_iff_le_exp hx0]
      exact hx'
    rw [Real.log_le_iff_le_exp hLpos]
    exact h1
  have hT : midTail x ^ (1 / 2 : ℝ) ≤ 1 :=
    rpow_half_le_of_le zero_le_one (by linarith [midTail_le_one hx])
  have hE : smallQReductionErr x (midZ x) (halfEta x) (halfEps x) ^ (1 / 2 : ℝ) ≤ 1 :=
    rpow_half_le_of_le zero_le_one (by linarith [midErr_le_one hx])
  have hCR : smallQReductionConst (midY x) (midZ x) (halfEta x) (halfEps x) (1 / 32)
      ^ (1 / 2 : ℝ) ≤ 76 / 100 :=
    rpow_half_le_of_le (by norm_num) (by linarith [midCR_le hx])
  have hCen := midCen_rpow_le hx
  have hCen0 : 0 ≤ midCen x ^ (1 / 2 : ℝ) := Real.rpow_nonneg (midCen_nonneg hx) _
  have hfar := half_far_le
  have hfar0 : 0 ≤ (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hmeso := midMeso_le hx
  have hmeso0 : 0 ≤ ∑ k ∈ Finset.Ico 4 (midJ x), thetaWindowConst (3 / 2) k (midY x)
      ^ (1 / 2 : ℝ) :=
    Finset.sum_nonneg fun k _ => Real.rpow_nonneg (thetaWindowConst_nonneg (by norm_num) k _) _
  obtain ⟨s, hs0, hs4, hs3, hs2⟩ := quarter_facts (Λ := Real.log (Real.log x)) (by linarith)
  rw [← hs3]
  set B := midCen x ^ (1 / 2 : ℝ) + (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ (1 / 2 : ℝ)
    + ∑ k ∈ Finset.Ico 4 (midJ x), thetaWindowConst (3 / 2) k (midY x) ^ (1 / 2 : ℝ) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hprod : smallQReductionConst (midY x) (midZ x) (halfEta x) (halfEps x) (1 / 32)
      ^ (1 / 2 : ℝ) * B ≤ 76 / 100 * B := mul_le_mul_of_nonneg_right hCR hB0
  rw [← hs2] at hCen
  rw [← hs4] at hmeso hΛ hΛ110
  have hBle : B ≤ 10051 / 1000 * s ^ 2 + 21 / 100 + 1143 / 100 + 2315 / 1000 * (s ^ 4 - 4) := by
    rw [hBdef]
    linarith
  have hslo : 162 / 100 ≤ s := by
    by_contra hc
    have : s ^ 4 < (162 / 100) ^ 4 := pow_lt_pow_left₀ (not_le.1 hc) hs0.le (by norm_num)
    linarith [show ((162 : ℝ) / 100) ^ 4 ≤ 7 by norm_num]
  have hshi : s ≤ 324 / 100 := by
    by_contra hc
    have : ((324 : ℝ) / 100) ^ 4 < s ^ 4 :=
      pow_lt_pow_left₀ (not_le.1 hc) (by norm_num) (by norm_num)
    linarith [show (110 : ℝ) ≤ (324 / 100) ^ 4 by norm_num]
  have hpoly : 3 + 76 / 100 * (10051 / 1000 * s ^ 2 + 21 / 100 + 1143 / 100
      + 2315 / 1000 * (s ^ 4 - 4)) ≤ 10 * s ^ 3 := by
    have h1 : 0 ≤ (s - 162 / 100) * (324 / 100 - s) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ (s - 162 / 100) * (324 / 100 - s) * s ^ 2 := mul_nonneg h1 (sq_nonneg s)
    have h3 : 0 ≤ (s - 162 / 100) * s ^ 2 := mul_nonneg (by linarith) (sq_nonneg s)
    nlinarith [sq_nonneg s]
  have := mul_le_mul_of_nonneg_left hBle (by norm_num : (0 : ℝ) ≤ 76 / 100)
  linarith

/-- `d ≤ c^{3/2}` from `d² ≤ c³`, for `c, d ≥ 0`. -/
lemma le_rpow_three_halves {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (h : d ^ 2 ≤ c ^ 3) :
    d ≤ c ^ (3 / 2 : ℝ) := by
  have e : c ^ (3 / 2 : ℝ) = Real.sqrt (c ^ 3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hc]
    norm_num
  rw [e]
  exact (Real.le_sqrt hd (by positivity)).2 h

/-- **`1 + L ≤ 100(log L)^{3/2}` for `log 3 ≤ L ≤ e⁷`**, in four pieces: on each,
`log L ≥ ℓ_i` and `1 + L ≤ 100 d_i` with `d_i² ≤ ℓ_i³`. -/
lemma one_add_le_hundred_mul_log_rpow {L : ℝ} (hL3 : Real.log 3 ≤ L) (hL7 : L ≤ Real.exp 7) :
    1 + L ≤ 100 * Real.log L ^ (3 / 2 : ℝ) := by
  have hl3 : (10986 / 10000 : ℝ) ≤ Real.log 3 := by interval_decide (trust := kernel)
  have he7 : Real.exp 7 ≤ 10967 / 10 := by interval_decide (trust := kernel)
  have key : ∀ {ℓ d : ℝ}, 0 ≤ ℓ → 0 ≤ d → d ^ 2 ≤ ℓ ^ 3 → ℓ ≤ Real.log L → 1 + L ≤ 100 * d →
      1 + L ≤ 100 * Real.log L ^ (3 / 2 : ℝ) := by
    intro ℓ d hℓ hd hdℓ hℓL h
    have h1 := le_rpow_three_halves hℓ hd hdℓ
    have h2 : ℓ ^ (3 / 2 : ℝ) ≤ Real.log L ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hℓ hℓL (by norm_num)
    linarith
  rcases le_or_gt L (185 / 100) with h1 | h1
  · have hl : (94 / 1000 : ℝ) ≤ Real.log L := by
      have h0 : (94 / 1000 : ℝ) ≤ Real.log (10986 / 10000) := by interval_decide (trust := kernel)
      have := Real.log_le_log (by norm_num) (le_trans hl3 hL3)
      linarith
    exact key (ℓ := 94 / 1000) (d := 2881 / 100000) (by norm_num) (by norm_num) (by norm_num) hl
      (by linarith)
  rcases le_or_gt L 47 with h2 | h2
  · have hl : (6151 / 10000 : ℝ) ≤ Real.log L := by
      have h0 : (6151 / 10000 : ℝ) ≤ Real.log (185 / 100) := by interval_decide (trust := kernel)
      have := Real.log_le_log (by norm_num) h1.le
      linarith
    exact key (ℓ := 6151 / 10000) (d := 48 / 100) (by norm_num) (by norm_num) (by norm_num) hl
      (by linarith)
  rcases le_or_gt L 700 with h3 | h3
  · have hl : (385 / 100 : ℝ) ≤ Real.log L := by
      have h0 : (385 / 100 : ℝ) ≤ Real.log 47 := by interval_decide (trust := kernel)
      have := Real.log_le_log (by norm_num) h2.le
      linarith
    exact key (ℓ := 385 / 100) (d := 701 / 100) (by norm_num) (by norm_num) (by norm_num) hl
      (by linarith)
  · have hl : (655 / 100 : ℝ) ≤ Real.log L := by
      have h0 : (655 / 100 : ℝ) ≤ Real.log 700 := by interval_decide (trust := kernel)
      have := Real.log_le_log (by norm_num) h3.le
      linarith
    exact key (ℓ := 655 / 100) (d := 1098 / 100) (by norm_num) (by norm_num) (by norm_num) hl
      (by linarith)

/-- **The first moment for `3 ≤ x ≤ exp(e⁷)`, trivially**:
`E|S(x)| ≤ (E|S(x)|²)^{1/2} ≤ (1 + log x)^{1/2} ≤ 10 (log log x)^{3/4}`
(`RMF.integral_normSq_weightedRademacherSum_le_one_add_log`,
`RMF.one_add_le_hundred_mul_log_rpow`). -/
theorem integral_norm_weightedRademacherSum_le_ten_small {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx3 : 3 ≤ x) (hx : x ≤ Real.exp (Real.exp 7)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
      ≤ 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  have hRa : IsRademacherRMF f μ := hX.isRademacherRMF
  have hx0 : 0 < x := by linarith
  have hWm : Measurable (weightedRademacherSum f x) :=
    Finset.measurable_sum _ fun n _ => (hRa.measurable_apply n).div_const _
  have h1 : (∫ ω, (‖weightedRademacherSum f x ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
      ≤ (∫ ω, ‖weightedRademacherSum f x ω‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) :=
    integral_rpow_le_rpow_integral_of_bound (M := ((⌊x⌋₊ : ℕ) : ℝ) ^ 2)
      (by norm_num) (by norm_num) (by fun_prop)
      (Filter.Eventually.of_forall fun ω => by positivity)
      (by
        filter_upwards [ae_norm_weightedRademacherSum_le hRa x] with ω hω
        exact pow_le_pow_left₀ (norm_nonneg _) hω 2)
  have e : (fun ω => (‖weightedRademacherSum f x ω‖ ^ 2) ^ (1 / 2 : ℝ))
      = fun ω => ‖weightedRademacherSum f x ω‖ := by
    funext ω
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  rw [e] at h1
  have hsm := integral_normSq_weightedRademacherSum_le_one_add_log hRa (by linarith : (1 : ℝ) ≤ x)
  have hsm0 : (0 : ℝ) ≤ ∫ ω, ‖weightedRademacherSum f x ω‖ ^ 2 ∂μ :=
    integral_nonneg fun ω => by positivity
  have h2 : (∫ ω, ‖weightedRademacherSum f x ω‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ)
      ≤ (1 + Real.log x) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hsm0 hsm (by norm_num)
  -- `(1 + L)^{1/2} ≤ 10(log L)^{3/4}`
  have hL3 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3
  have hL7 : Real.log x ≤ Real.exp 7 := by
    rw [Real.log_le_iff_le_exp hx0]
    exact hx
  have hl3 : (1 : ℝ) < Real.log 3 := by
    have : (10986 / 10000 : ℝ) ≤ Real.log 3 := by interval_decide (trust := kernel)
    linarith
  have hlogL0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg (by linarith)
  have hkey := one_add_le_hundred_mul_log_rpow hL3 hL7
  have h3 : (1 + Real.log x) ^ (1 / 2 : ℝ) ≤ 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
    refine rpow_half_le_of_le (by positivity) ?_
    have e2 : (10 * Real.log (Real.log x) ^ (3 / 4 : ℝ)) ^ 2
        = 100 * Real.log (Real.log x) ^ (3 / 2 : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (Real.log (Real.log x) ^ (3 / 4 : ℝ)) 2,
        ← Real.rpow_mul hlogL0]
      norm_num
    rw [e2]
    exact hkey
  exact le_trans h1 (le_trans h2 h3)

/-- **The first moment of the weighted Rademacher sum at `q = ½` with the constant `10`, for
every `x ≥ 3`**: `E|∑_{n≤x} f(n)/√n| ≤ 10 (log log x)^{3/4}`.  Trivially up to `exp(e⁷)`
(`RMF.integral_norm_weightedRademacherSum_le_ten_small`), by the middle range's chain up to
`exp(e^{110})` (`RMF.integral_norm_weightedRademacherSum_le_ten_mid`) and by
`RMF.integral_norm_weightedRademacherSum_le_ten` beyond. -/
theorem integral_norm_weightedRademacherSum_le_ten_of_three_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 3 ≤ x) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
      ≤ 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
  rcases le_or_gt x (Real.exp (Real.exp 7)) with h1 | h1
  · exact integral_norm_weightedRademacherSum_le_ten_small hX hx h1
  rcases le_or_gt x (Real.exp (Real.exp 110)) with h2 | h2
  · exact integral_norm_weightedRademacherSum_le_ten_mid hX h1.le h2
  · exact integral_norm_weightedRademacherSum_le_ten hX h2.le

end RMF
