/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.HalfAssemblyExplicit
import RMF.Reduction.UpperAveragedLeaves

/-!
# The first moment of the weighted Rademacher sum: the numerals

Numerals of the chain at `q = ½`, at the parameters of `RMF/Weighted/HalfAssemblyExplicit.lean`.

* **The chaos constant** `RMF.halfChaosConst E₀ ≤ 4.68` for `E₀ ≤ 1/33680`, i.e. on every chaos
  window (`RMF.halfChaosConst_le`): the leaves of the Rademacher averaged free start at that tilt,
  the level `20 ≥ 16(1 + 45√E₀)`, and `RMF.shiftMomentConst_le_exp`.
-/

open MeasureTheory

namespace RMF

/-! ### The leaves of the chaos constant at `E₀ ≤ 1/33680` -/

lemma sqrt_le_of_le_half_tilt {E₀ : ℝ} (hE₀1 : E₀ ≤ 1 / 33680) :
    Real.sqrt E₀ ≤ 1 / 1835 * 10 := by
  calc Real.sqrt E₀ ≤ Real.sqrt ((1 / 1835 * 10) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = 1 / 1835 * 10 := Real.sqrt_sq (by norm_num)

lemma radAveragedK_le_half {E₀ : ℝ} (hE₀1 : E₀ ≤ 1 / 33680) :
    radAveragedK E₀ ≤ 116341 / 100000 := by
  have hpi := Real.pi_gt_d6
  have he : 1 - 2 * E₀ ≤ Real.exp (-(2 * E₀)) := by
    linarith [Real.add_one_le_exp (-(2 * E₀))]
  have he0 : 0 < Real.exp (-(2 * E₀)) := Real.exp_pos _
  have h : 2 * 25 / (24 * (Real.pi * (0.49 * Real.exp (-(2 * E₀))))) ≤ (116341 / 100000) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  unfold radAveragedK
  calc √(2 * 25 / (24 * (Real.pi * (0.49 * Real.exp (-(2 * E₀))))))
      ≤ √((116341 / 100000) ^ 2) := Real.sqrt_le_sqrt h
    _ = 116341 / 100000 := Real.sqrt_sq (by norm_num)

lemma radAveragedConst_le_half {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 33680) :
    radAveragedConst E₀ (11 / 20) 35 10 ≤ 12177 / 10000 := by
  have hK := radAveragedK_le_half hE₀1
  have hK0 : 0 ≤ radAveragedK E₀ := le_trans zero_le_one (one_le_radAveragedK hE₀)
  have he := exp_neg_hundred_le
  unfold radAveragedConst
  rw [div_le_iff₀ (by norm_num)]
  have h1 : (1 + Real.exp (-100)) * radAveragedK E₀ ≤ (1 + 1 / 10000000) * (116341 / 100000) :=
    mul_le_mul (by linarith) hK hK0 (by norm_num)
  nlinarith

lemma driftRadSharpOf_le_half {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 33680) :
    driftRadSharpOf E₀ 16 (Real.exp (-(2 * E₀)) / 100) ≤ 2553 / 10000 := by
  have hs := sqrt_le_of_le_half_tilt hE₀1
  have h17 := exp_seventeen_ge
  have he2 : Real.exp 2 ≤ 7.4 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h]
    nlinarith [Real.exp_pos 1, Real.exp_one_lt_d9]
  have hu : (Real.exp 17)⁻¹ ≤ 1 / 24000000 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h17
  have hu0 : 0 ≤ (Real.exp 17)⁻¹ := inv_nonneg.2 (Real.exp_pos _).le
  have h1 : Real.exp (-(1 + 16)) = (Real.exp 17)⁻¹ := by rw [← Real.exp_neg]; norm_num
  have h2 : Real.exp E₀ * Real.exp (-16) ≤ Real.exp 2 * (Real.exp 17)⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-(2 * E₀)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  unfold driftRadSharpOf
  rw [h1]
  have t1 : 120 * Real.exp 2 * (Real.exp 17)⁻¹ ≤ 120 * 7.4 * (1 / 24000000) :=
    mul_le_mul (mul_le_mul_of_nonneg_left he2 (by norm_num)) hu hu0 (by norm_num)
  have t2 : Real.exp 2 * (Real.exp 17)⁻¹ ≤ 7.4 * (1 / 24000000) :=
    mul_le_mul he2 hu hu0 (by norm_num)
  have t3 : 76 * Real.exp E₀ * Real.exp (-16) ≤ 76 * (7.4 * (1 / 24000000)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_trans h2 t2) (by norm_num)
  linarith

lemma log_ten_le : Real.log 10 ≤ 2302586 / 1000000 := by
  interval_decide (trust := kernel)

lemma log_KT_rad_le : Real.log (116341 / 100000 * 35) ≤ 3706722 / 1000000 := by
  interval_decide (trust := kernel)

lemma radAveragedShift_le_half {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 33680) :
    radAveragedShift E₀ (11 / 20) 35 10 ≤ 137455 / 10000 := by
  have hd := driftRadSharpOf_le_half hE₀ hE₀1
  have hlog2 : Real.log 2 ≤ 693148 / 1000000 := by linarith [Real.log_two_lt_d9]
  have hlog50 : Real.log (2 * ((25 : ℕ) : ℝ)) ≤ 3912024 / 1000000 := by
    rw [show (2 : ℝ) * ((25 : ℕ) : ℝ) = 50 by norm_num]
    exact log_fifty_le
  have hpi := Real.pi_lt_d6
  have hsq : √(Real.pi * 1 / 2) ≤ 1253315 / 1000000 := by
    have h : Real.pi * 1 / 2 ≤ (1253315 / 1000000) ^ 2 := by nlinarith
    calc √(Real.pi * 1 / 2) ≤ √((1253315 / 1000000) ^ 2) := Real.sqrt_le_sqrt h
      _ = 1253315 / 1000000 := Real.sqrt_sq (by norm_num)
  have hK := radAveragedK_le_half hE₀1
  have hK1 := one_le_radAveragedK hE₀
  have hlogKT : Real.log (radAveragedK E₀ * 35) ≤ 3706722 / 1000000 :=
    le_trans (Real.log_le_log (by positivity) (by linarith)) log_KT_rad_le
  have hl10 := log_ten_le
  unfold radAveragedShift result1SharpShift
  push_cast
  nlinarith

/-- `radChainConst (2/1152) ≤ 561.3`. -/
lemma radChainConst_le_half : radChainConst (2 / 1152) ≤ 5613 / 10 := by
  unfold radChainConst radChainSum
  interval_decide (trust := kernel)

/-- `radBlockBadConst E₀ (11/20)·e⁸ ≤ e^{26.42}` for `E₀ ≤ 1/33680`. -/
lemma radBlockBadConst_mul_le_half {E₀ : ℝ} (hE₀1 : E₀ ≤ 1 / 33680) :
    radBlockBadConst E₀ (11 / 20) * Real.exp 8 ≤ Real.exp (2642 / 100) := by
  have hs := sqrt_le_of_le_half_tilt hE₀1
  have hRC := radChainConst_le_half
  have hRC0 : 0 < radChainConst (2 / 1152) := radChainConst_pos (by norm_num)
  have hζ := tsum_nat_rpow_neg_le (s := 2 * (11 / 20)) (by norm_num)
  have hζ0 : (0 : ℝ) ≤ ∑' i : ℕ, (i : ℝ) ^ (-(2 * (11 / 20 : ℝ))) :=
    tsum_nonneg fun i => Real.rpow_nonneg (Nat.cast_nonneg i) _
  have hD : harperSharpDeficit E₀ ≤ 12453 / 10000 := by
    rw [harperSharpDeficit]
    linarith
  have hexpD : Real.exp (harperSharpDeficit E₀) ≤ Real.exp (12453 / 10000) := Real.exp_le_exp.2 hD
  have hnum : (4 * 1152 * (5613 / 10) * (2 * (11 / 20) / (2 * (11 / 20) - 1)) : ℝ)
      * Real.exp (12453 / 10000) * Real.exp 8 ≤ Real.exp (2642 / 100) := by
    interval_decide (trust := kernel)
  unfold radBlockBadConst radIndexConst
  rw [show radIndexRefine = 1152 from rfl]
  have h1 : 4 * 1152 * radChainConst (2 / 1152) * Real.exp (harperSharpDeficit E₀)
      ≤ 4 * 1152 * (5613 / 10) * Real.exp (12453 / 10000) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hRC (by norm_num)) hexpD (Real.exp_pos _).le
      (by norm_num)
  have h2 := mul_le_mul h1 hζ hζ0 (by positivity)
  have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos 8).le
  refine le_trans (le_of_eq_of_le ?_ h3) ?_
  · ring
  · calc 4 * 1152 * (5613 / 10) * Real.exp (12453 / 10000) * (2 * (11 / 20) / (2 * (11 / 20) - 1))
          * Real.exp 8
        = (4 * 1152 * (5613 / 10) * (2 * (11 / 20) / (2 * (11 / 20) - 1)) : ℝ)
          * Real.exp (12453 / 10000) * Real.exp 8 := by ring
      _ ≤ Real.exp (2642 / 100) := hnum

lemma inv_sqrt_one_sub_fiftieth_le : (Real.sqrt (1 - 1 / 50))⁻¹ ≤ 10102 / 10000 := by
  have h : (10000 / 10102 : ℝ) ≤ Real.sqrt (1 - 1 / 50) := by
    rw [Real.le_sqrt' (by norm_num)]
    norm_num
  calc (Real.sqrt (1 - 1 / 50))⁻¹ ≤ (10000 / 10102 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h
    _ = 10102 / 10000 := by norm_num

/-- **The chaos constant on the chaos windows**: `RMF.halfChaosConst E₀ ≤ 4.68` for
`0 ≤ E₀ ≤ 1/33680`. -/
theorem halfChaosConst_le {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 33680) :
    halfChaosConst E₀ ≤ 468 / 100 := by
  have hCi := radAveragedConst_le_half hE₀ hE₀1
  have hCi0 : 0 ≤ radAveragedConst E₀ (11 / 20) 35 10 := by
    have := one_le_radAveragedConst hE₀ (by norm_num : (0 : ℝ) ≤ 11 / 20) (by norm_num)
      (by norm_num : (4 : ℝ) < 35) (by norm_num : (1 : ℝ) ≤ 10)
    linarith
  have hs := radAveragedShift_le_half hE₀ hE₀1
  have hs0 := radAveragedShift_nonneg hE₀ (by norm_num : (0 : ℝ) ≤ 11 / 20) (by norm_num)
    (by norm_num : (4 : ℝ) < 35) (by norm_num : (1 : ℝ) ≤ 10)
  have hCb := radBlockBadConst_mul_le_half hE₀1
  have hCb0 : 0 ≤ radBlockBadConst E₀ (11 / 20) * Real.exp 8 :=
    mul_nonneg (radBlockBadConst_pos E₀ (by norm_num)).le (Real.exp_pos _).le
  have hAs : (0 : ℝ) ≤ 20 + radAveragedShift E₀ (11 / 20) 35 10 := by linarith
  have hU : (20 + radAveragedShift E₀ (11 / 20) 35 10) * (1 - 1 / 2) ≤ 168728 / 10000 := by
    linarith
  have h := shiftMomentConst_le_exp (C₁ := 1) (N := 1)
    (Ci := radAveragedConst E₀ (11 / 20) 35 10) (Ci' := 12177 / 10000)
    (Cb := radBlockBadConst E₀ (11 / 20) * Real.exp 8) (LB := 2642 / 100)
    (s := radAveragedShift E₀ (11 / 20) 35 10) (U := 168728 / 10000) (IS := 10102 / 10000)
    (S1 := 1156519 / 1000000) (S2 := 181016 / 1000000) (EM2 := 135336 / 1000000) (A := 20)
    (lam := 104 / 5) (δ := 1 / 50) (q := 1 / 2) (by norm_num) (by norm_num) zero_le_one le_rfl
    hCi0 hCi hCb0 hCb hAs hU (by norm_num) (by norm_num) inv_sqrt_one_sub_fiftieth_le
    inv_one_sub_exp_neg_two_le exp_neg_two_mul_inv_sq_le exp_neg_two_le_cert
  rw [halfChaosConst]
  refine le_trans h ?_
  refine max_le ?_ ?_
  · interval_decide (trust := kernel)
  · interval_decide (trust := kernel)

/-! ### The windows' constants -/

lemma rpow_half_le_of_le {a b : ℝ} (hb : 0 ≤ b) (h : a ≤ b ^ 2) :
    a ^ (1 / 2 : ℝ) ≤ b := by
  rw [← Real.sqrt_eq_rpow]
  calc Real.sqrt a ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt h
    _ = b := Real.sqrt_sq hb

lemma exp_neg_four_le_sharp : Real.exp (-4) ≤ 1831564 / 100000000 := by
  interval_decide (trust := kernel)

/-! ### The reduction's pieces -/

/-- `e^{u} ≥ u³/6`, as `u³ ≤ 6e^u`. -/
lemma pow_three_le_six_mul_exp {u : ℝ} (hu : 0 ≤ u) : u ^ 3 ≤ 6 * Real.exp u := by
  have h := Real.pow_div_factorial_le_exp (x := u) hu 3
  have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf] at h
  linarith

/-- `u⁶ ≤ 720e^u`. -/
lemma pow_six_le_exp {u : ℝ} (hu : 0 ≤ u) : u ^ 6 ≤ 720 * Real.exp u := by
  have h := Real.pow_div_factorial_le_exp (x := u) hu 6
  have hf : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hf] at h
  linarith

/-- **The smooth tail is at most `1`**: Rankin at `κ = log U`, `U = Λ/2`
(`RMF.smoothTailSum_le_rankin_explicit`), where the exponent is `≤ 1.42 - 0.4995Λ`. -/
lemma halfTail_le_one {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) : halfTail x ≤ 1 := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, -, -⟩ := half_params hx
  obtain ⟨hy2, -, hlogy_le, hlogy_ge, -, -⟩ := halfY_facts hx
  have ha := halfA_ge hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hly : 22000 ≤ Real.log (halfY x) := by linarith
  have hlypos : 0 < Real.log (halfY x) := by linarith
  have hU : 0 < Real.log (Real.log x) / 2 := by linarith
  have hκ : 4 ≤ Real.log (Real.log (Real.log x) / 2) := by
    rw [Real.le_log_iff_exp_le hU]
    have : Real.exp 4 ≤ 55 := by interval_decide (trust := kernel)
    linarith
  have h := smoothTailSum_le_rankin_explicit (y := halfY x) hy2 hx0
    (κ := Real.log (Real.log (Real.log x) / 2)) (by linarith)
  rw [Real.exp_log hU] at h
  unfold halfTail
  refine le_trans h ?_
  have hratio : Real.log (Real.log x) / 2 ≤ Real.log x / Real.log (halfY x) := by
    rw [le_div_iff₀ hlypos]
    have h1 := hlogy_le
    rw [halfA, le_div_iff₀ hΛpos] at h1
    linarith
  have hl4 : Real.log 4 + 4 ≤ 6 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_lt_d9]
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hfrac : (Real.log 4 + 4) / Real.log (halfY x) ≤ 1 / 1000 := by
    rw [div_le_iff₀ hlypos]
    linarith
  have hf0 : 0 ≤ (Real.log 4 + 4) / Real.log (halfY x) := by positivity
  have e1 : (Real.log (Real.log x) / 2 - 1) * (1 + (Real.log 4 + 4) / Real.log (halfY x))
      ≤ Real.log (Real.log x) / 2 * (1 + 1 / 1000) := by
    have h1 : Real.log (Real.log x) / 2 - 1 ≤ Real.log (Real.log x) / 2 := by linarith
    have h2 : 0 ≤ Real.log (Real.log x) / 2 - 1 := by linarith
    calc (Real.log (Real.log x) / 2 - 1) * (1 + (Real.log 4 + 4) / Real.log (halfY x))
        ≤ Real.log (Real.log x) / 2 * (1 + (Real.log 4 + 4) / Real.log (halfY x)) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ Real.log (Real.log x) / 2 * (1 + 1 / 1000) :=
          mul_le_mul_of_nonneg_left (by linarith) hU.le
  have e2 : 4 * (Real.log (Real.log x) / 2)
      ≤ Real.log (Real.log (Real.log x) / 2) * Real.log x / Real.log (halfY x) := by
    rw [mul_div_assoc]
    exact mul_le_mul hκ hratio hU.le (by linarith)
  have hly_le : Real.log (halfY x) ≤ Real.exp (Real.log (Real.log x)) := by
    rw [hexpΛ]
    obtain ⟨-, -, -, -, -, haL⟩ := half_params hx
    linarith
  calc Real.log (halfY x) * Real.exp (1.42 + (Real.log (Real.log x) / 2 - 1)
        * (1 + (Real.log 4 + 4) / Real.log (halfY x))
        - Real.log (Real.log (Real.log x) / 2) * Real.log x / Real.log (halfY x))
      ≤ Real.exp (Real.log (Real.log x)) * Real.exp (1.42 + Real.log (Real.log x) / 2
          * (1 + 1 / 1000) - 4 * (Real.log (Real.log x) / 2)) :=
        mul_le_mul hly_le (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (Real.log (Real.log x) + (1.42 + Real.log (Real.log x) / 2
          * (1 + 1 / 1000) - 4 * (Real.log (Real.log x) / 2))) := (Real.exp_add _ _).symm
    _ ≤ 1 := Real.exp_le_one_iff.2 (by linarith)

/-- **The large numbers of the parameters**: with `L = log x`, `Λ = log L`, `s = √L`:
`s = e^{Λ/2}`, `100Λ ≤ s` and `10⁶ ≤ s`. -/
lemma half_big {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    Real.sqrt (Real.log x) = Real.exp (Real.log (Real.log x) / 2)
      ∧ 100 * Real.log (Real.log x) ≤ Real.sqrt (Real.log x)
      ∧ 1000000 ≤ Real.sqrt (Real.log x) := by
  obtain ⟨-, -, hΛ, hexpΛ, -, -⟩ := half_params hx
  have hs : Real.sqrt (Real.log x) = Real.exp (Real.log (Real.log x) / 2) := by
    rw [Real.exp_half, hexpΛ]
  have hu : 0 ≤ Real.log (Real.log x) / 2 := by linarith
  have h3 := pow_three_le_six_mul_exp hu
  refine ⟨hs, ?_, ?_⟩
  · rw [hs]
    have h4 : 100 * Real.log (Real.log x) ≤ (Real.log (Real.log x) / 2) ^ 3 / 6 := by
      have h5 : (4800 : ℝ) ≤ Real.log (Real.log x) ^ 2 := by nlinarith
      have h6 : (Real.log (Real.log x) / 2) ^ 3 / 6
          = Real.log (Real.log x) * Real.log (Real.log x) ^ 2 / 48 := by ring
      rw [h6]
      nlinarith
    linarith
  · rw [hs]
    have h7 : (1000000 : ℝ) ≤ Real.exp 55 := by interval_decide (trust := kernel)
    exact le_trans h7 (Real.exp_le_exp.2 (by linarith))

/-- The error's arithmetic: for `s ≥ 10⁶`, `100Λ ≤ s`, `L = s²` and `0 ≤ E`, `E·L⁶ ≤ 46080`,
`(1+s)(2/L² + 2(2Λ/L + 40L³E)) ≤ 1`. -/
lemma half_err_arith {s Λ E : ℝ} (hs6 : 1000000 ≤ s) (hsΛ : 100 * Λ ≤ s)
    (hE0 : 0 ≤ E) (hE : E * (s ^ 2) ^ 6 ≤ 46080) :
    (1 + s) * (2 / (s ^ 2) ^ 2 + 2 * (2 * Λ / s ^ 2 + 40 * (s ^ 2) ^ 3 * E)) ≤ 1 := by
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hs3 : (1000000000000000000 : ℝ) ≤ s ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hs6 3
    norm_num at this
    linarith
  have t1 : (1 + s) * (2 / (s ^ 2) ^ 2) ≤ 1 / 100 := by
    rw [show (1 + s) * (2 / (s ^ 2) ^ 2) = (2 + 2 * s) / (s * s ^ 3) by field_simp,
      div_le_iff₀ (by positivity)]
    nlinarith
  have t2 : (1 + s) * (2 * (2 * Λ / s ^ 2)) ≤ 1 / 10 := by
    rw [show (1 + s) * (2 * (2 * Λ / s ^ 2)) = (4 * Λ + 4 * Λ * s) / (s * s) by field_simp; ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  have t3 : (1 + s) * (2 * (40 * (s ^ 2) ^ 3 * E)) ≤ 1 / 100 := by
    have h1 : (1 + s) * (2 * (40 * (s ^ 2) ^ 3 * E)) ≤ 160 * s * ((s ^ 2) ^ 3 * E) := by
      have : 0 ≤ (s ^ 2) ^ 3 * E := by positivity
      nlinarith
    have h2 : (s ^ 2) ^ 3 * E * (s ^ 2) ^ 3 ≤ 46080 := by
      calc (s ^ 2) ^ 3 * E * (s ^ 2) ^ 3 = E * (s ^ 2) ^ 6 := by ring
        _ ≤ 46080 := hE
    have h3 : (s ^ 2) ^ 3 * E ≤ 46080 / (s ^ 2) ^ 3 := by
      rw [le_div_iff₀ (by positivity)]
      exact h2
    have h4 : 160 * s * (46080 / (s ^ 2) ^ 3) ≤ 1 / 100 := by
      rw [show 160 * s * (46080 / (s ^ 2) ^ 3) = 7372800 / (s ^ 2 * s ^ 3) by field_simp; ring,
        div_le_iff₀ (by positivity)]
      have h5 : (1000000000000 : ℝ) ≤ s ^ 2 := by nlinarith
      nlinarith
    calc (1 + s) * (2 * (40 * (s ^ 2) ^ 3 * E)) ≤ 160 * s * ((s ^ 2) ^ 3 * E) := h1
      _ ≤ 160 * s * (46080 / (s ^ 2) ^ 3) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 1 / 100 := h4
  have hsplit : (1 + s) * (2 / (s ^ 2) ^ 2 + 2 * (2 * Λ / s ^ 2 + 40 * (s ^ 2) ^ 3 * E))
      = (1 + s) * (2 / (s ^ 2) ^ 2) + (1 + s) * (2 * (2 * Λ / s ^ 2))
        + (1 + s) * (2 * (40 * (s ^ 2) ^ 3 * E)) := by ring
  rw [hsplit]
  linarith

/-- **The reduction's error is at most `1`**: `(1+√L)(η(1+L) + (1+η)(2/log z + 5z(1+log z)³/x))`
with `η = L^{-3}`, `log z ≥ L/Λ` and `z ≤ e^{L/2}` (`RMF.half_err_arith`). -/
lemma halfErr_le_one {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ≤ 1 := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, -, haL⟩ := half_params hx
  obtain ⟨hz2, -, hlogz⟩ := halfZ_facts hx
  obtain ⟨-, hsΛ, hs6⟩ := half_big hx
  have ha := halfA_ge hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hsq : Real.sqrt (Real.log x) ^ 2 = Real.log x := Real.sq_sqrt hLpos.le
  have hε : 1 / halfEps x = Real.sqrt (Real.log x) := by rw [halfEps, one_div, inv_inv]
  have hη0 : 0 < halfEta x := by rw [halfEta]; positivity
  have hL1 : 1 ≤ Real.log x := by
    have : (1 : ℝ) ≤ Real.exp 110 := Real.one_le_exp (by norm_num)
    linarith
  -- `η(1 + L) ≤ 2/L²` and `η ≤ 1`
  have hη2 : halfEta x * (1 + Real.log x) ≤ 2 / Real.log x ^ 2 := by
    rw [halfEta, inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ Real.log x ^ 2 := sq_nonneg _
    nlinarith
  have hη1 : halfEta x ≤ 1 := by
    rw [halfEta]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  -- `2/log z ≤ 2Λ/L`
  have hlogz0 : 0 < Real.log (halfZ x) := by linarith
  have hA : halfA x * Real.log (Real.log x) = 2 * Real.log x := by
    rw [halfA]
    field_simp
  have t1 : 2 / Real.log (halfZ x) ≤ 2 * Real.log (Real.log x) / Real.log x := by
    rw [div_le_div_iff₀ hlogz0 hLpos]
    have h1 : halfA x / 2 ≤ Real.log (halfZ x) := by linarith
    nlinarith
  -- `5z(1+log z)³/x ≤ 40L³e^{-L/2}`
  have hzle : (halfZ x : ℝ) ≤ Real.exp (halfA x) :=
    le_trans (Nat.floor_le (Real.exp_pos _).le) (Real.exp_le_exp.2 (by linarith))
  have hz0 : (0 : ℝ) < (halfZ x : ℝ) := by
    have : (2 : ℝ) ≤ (halfZ x : ℝ) := by exact_mod_cast hz2
    linarith
  have hlogzle : Real.log (halfZ x) ≤ halfA x :=
    le_trans (Real.log_le_log hz0 hzle) (le_of_eq (Real.log_exp _))
  have hcube : (1 + Real.log (halfZ x)) ^ 3 ≤ (2 * Real.log x) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have haL2 : halfA x ≤ Real.log x / 2 := by
    rw [halfA, div_le_iff₀ hΛpos]
    nlinarith
  have hxe : Real.exp (Real.log x) = x := Real.exp_log hx0
  have h2 : Real.exp (halfA x) ≤ Real.exp (-(Real.log x / 2)) * x := by
    calc Real.exp (halfA x) ≤ Real.exp (-(Real.log x / 2) + Real.log x) :=
          Real.exp_le_exp.2 (by linarith)
      _ = Real.exp (-(Real.log x / 2)) * x := by rw [Real.exp_add, hxe]
  have t2 : 5 * (halfZ x : ℝ) * (1 + Real.log (halfZ x)) ^ 3 / x
      ≤ 40 * Real.log x ^ 3 * Real.exp (-(Real.log x / 2)) := by
    rw [div_le_iff₀ hx0]
    calc 5 * (halfZ x : ℝ) * (1 + Real.log (halfZ x)) ^ 3
        ≤ 5 * (Real.exp (-(Real.log x / 2)) * x) * (2 * Real.log x) ^ 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (le_trans hzle h2) (by norm_num)) hcube
            (by positivity) (by positivity)
      _ = 40 * Real.log x ^ 3 * Real.exp (-(Real.log x / 2)) * x := by ring
  -- `e^{-L/2}·L⁶ ≤ 46080`
  have hexpneg : Real.exp (-(Real.log x / 2)) * Real.log x ^ 6 ≤ 46080 := by
    have h6 := pow_six_le_exp (u := Real.log x / 2) (by linarith)
    have h1 : Real.exp (-(Real.log x / 2)) * Real.exp (Real.log x / 2) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : (Real.log x / 2) ^ 6 = Real.log x ^ 6 / 64 := by ring
    rw [h3] at h6
    have h4 := Real.exp_pos (-(Real.log x / 2))
    calc Real.exp (-(Real.log x / 2)) * Real.log x ^ 6
        ≤ Real.exp (-(Real.log x / 2)) * (64 * (720 * Real.exp (Real.log x / 2))) :=
          mul_le_mul_of_nonneg_left (by linarith) h4.le
      _ = 46080 * (Real.exp (-(Real.log x / 2)) * Real.exp (Real.log x / 2)) := by ring
      _ = 46080 := by rw [h1, mul_one]
  -- assemble
  have hp : 0 ≤ 2 / Real.log (halfZ x) + 5 * (halfZ x : ℝ) * (1 + Real.log (halfZ x)) ^ 3 / x := by
    positivity
  have hsum : halfEta x * (1 + Real.log x) + (1 + halfEta x) * (2 / Real.log (halfZ x)
      + 5 * (halfZ x : ℝ) * (1 + Real.log (halfZ x)) ^ 3 / x)
      ≤ 2 / Real.log x ^ 2 + 2 * (2 * Real.log (Real.log x) / Real.log x
        + 40 * Real.log x ^ 3 * Real.exp (-(Real.log x / 2))) := by
    have := mul_le_mul (by linarith : 1 + halfEta x ≤ 2) (add_le_add t1 t2) hp (by norm_num)
    linarith
  have hs0 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hfin := mul_le_mul_of_nonneg_left hsum (by linarith : (0 : ℝ) ≤ 1 + Real.sqrt (Real.log x))
  have harith := half_err_arith (s := Real.sqrt (Real.log x)) (Λ := Real.log (Real.log x))
    (E := Real.exp (-(Real.log x / 2))) hs6 hsΛ (Real.exp_pos _).le
    (by rw [hsq]; exact hexpneg)
  rw [hsq] at harith
  unfold smallQReductionErr
  rw [hε]
  linarith

/-- `L^n = e^{nΛ}`. -/
lemma half_log_pow {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (n : ℕ) :
    Real.log x ^ n = Real.exp (n * Real.log (Real.log x)) := by
  obtain ⟨-, -, -, hexpΛ, -, -⟩ := half_params hx
  rw [Real.exp_nat_mul, hexpΛ]

/-- `η = L^{-3}`: `ηL³ = 1` and `0 < η ≤ 10⁻⁶`; `ε ≤ 10⁻⁶`. -/
lemma half_eta_eps {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    0 < halfEta x ∧ halfEta x * Real.log x ^ 3 = 1 ∧ halfEta x ≤ 1 / 1000000
      ∧ 0 ≤ halfEps x ∧ halfEps x ≤ 1 / 1000000 := by
  obtain ⟨-, hL, -, -, -, -⟩ := half_params hx
  obtain ⟨-, -, hs6⟩ := half_big hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hsq : Real.sqrt (Real.log x) ^ 2 = Real.log x := Real.sq_sqrt hLpos.le
  have hL12 : (1000000000000 : ℝ) ≤ Real.log x := by nlinarith
  refine ⟨by rw [halfEta]; positivity, by rw [halfEta]; field_simp, ?_, by rw [halfEps]; positivity,
    ?_⟩
  · rw [halfEta, inv_le_comm₀ (by positivity) (by norm_num)]
    have h3 : (1000000000000 : ℝ) ^ 3 ≤ Real.log x ^ 3 := pow_le_pow_left₀ (by norm_num) hL12 3
    norm_num at h3 ⊢
    linarith
  · rw [halfEps, inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num
    linarith

/-- `2 log y/log z ≤ 2 + 2·10⁻⁶`: `log z ≥ a - 12Λ - log 2` with `a ≥ 200Λ⁹`. -/
lemma half_ratio_le {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    2 * Real.log (halfY x) / Real.log (halfZ x) ≤ 2 + 2 / 1000000 := by
  obtain ⟨-, -, hΛ, -, ha9, -⟩ := half_params hx
  obtain ⟨-, -, hlogy_le, -, -, -⟩ := halfY_facts hx
  obtain ⟨-, -, hlogz⟩ := halfZ_facts hx
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  have h9 : 110 ^ 8 * Real.log (Real.log x) ≤ Real.log (Real.log x) ^ 9 := by
    have h8 : (110 : ℝ) ^ 8 ≤ Real.log (Real.log x) ^ 8 := pow_le_pow_left₀ (by norm_num) hΛ 8
    calc 110 ^ 8 * Real.log (Real.log x) ≤ Real.log (Real.log x) ^ 8 * Real.log (Real.log x) :=
          mul_le_mul_of_nonneg_right h8 hΛpos.le
      _ = Real.log (Real.log x) ^ 9 := by ring
  have h1 : 1000001 * (12 * Real.log (Real.log x) + 1) ≤ halfA x := by nlinarith
  have hlogz0 : 0 < Real.log (halfZ x) := by nlinarith
  rw [div_le_iff₀ hlogz0]
  nlinarith

/-- `5z(1+log z)³ log y (1+η)/(yη + 1 + η) ≤ 10⁻⁶`: `z e^{12Λ} ≤ 2y` and `L⁷ = e^{7Λ}`. -/
lemma half_second_le {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    5 * (halfZ x : ℝ) * (1 + Real.log (halfZ x)) ^ 3 * Real.log (halfY x) * (1 + halfEta x)
      / ((halfY x : ℝ) * halfEta x + 1 + halfEta x) ≤ 1 / 1000000 := by
  obtain ⟨-, hL, hΛ, -, -, haL⟩ := half_params hx
  obtain ⟨hy2, -, hlogy_le, hlogy_ge, -, hyh⟩ := halfY_facts hx
  obtain ⟨hz2, -, hlogz⟩ := halfZ_facts hx
  obtain ⟨hη0, hηL, hη, -, -⟩ := half_eta_eps hx
  have ha := halfA_ge hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hy0 : (0 : ℝ) < (halfY x : ℝ) := by
    have : (2 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast hy2
    linarith
  have hz0 : (0 : ℝ) < (halfZ x : ℝ) := by
    have : (2 : ℝ) ≤ (halfZ x : ℝ) := by exact_mod_cast hz2
    linarith
  have hly0 : 0 ≤ Real.log (halfY x) := by linarith
  have hzle : (halfZ x : ℝ) ≤ Real.exp (halfA x - 12 * Real.log (Real.log x)) :=
    Nat.floor_le (Real.exp_pos _).le
  have hlogzle : Real.log (halfZ x) ≤ halfA x := by
    have h1 := Real.log_le_log hz0 hzle
    rw [Real.log_exp] at h1
    linarith
  have hcube : (1 + Real.log (halfZ x)) ^ 3 ≤ (2 * Real.log x) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hzy2 : (halfZ x : ℝ) * Real.exp (12 * Real.log (Real.log x)) ≤ 2 * (halfY x : ℝ) := by
    calc (halfZ x : ℝ) * Real.exp (12 * Real.log (Real.log x))
        ≤ Real.exp (halfA x - 12 * Real.log (Real.log x))
          * Real.exp (12 * Real.log (Real.log x)) :=
          mul_le_mul_of_nonneg_right hzle (Real.exp_pos _).le
      _ = Real.exp (halfA x) := by rw [← Real.exp_add]; ring_nf
      _ ≤ 2 * (halfY x : ℝ) := by linarith
  have hL7 := half_log_pow hx 7
  push_cast at hL7
  have h5 : (160000000 : ℝ) ≤ Real.exp (5 * Real.log (Real.log x)) := by
    have h3 : (160000000 : ℝ) ≤ Real.exp 550 := by interval_decide (trust := kernel)
    exact le_trans h3 (Real.exp_le_exp.2 (by linarith))
  have h12 : Real.exp (12 * Real.log (Real.log x))
      = Real.exp (7 * Real.log (Real.log x)) * Real.exp (5 * Real.log (Real.log x)) := by
    rw [← Real.exp_add]; ring_nf
  -- `numerator ≤ 80 z L⁴`
  have hA : 5 * (halfZ x : ℝ) * (1 + Real.log (halfZ x)) ^ 3 * Real.log (halfY x)
      * (1 + halfEta x) ≤ 80 * ((halfZ x : ℝ) * Real.log x ^ 4) := by
    have h1 : 5 * (halfZ x : ℝ) * (1 + Real.log (halfZ x)) ^ 3 * Real.log (halfY x)
        ≤ 5 * (halfZ x : ℝ) * (2 * Real.log x) ^ 3 * Real.log x :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcube (by positivity)) (by linarith) hly0
        (by positivity)
    have h2 := mul_le_mul h1 (by linarith : 1 + halfEta x ≤ 2) (by linarith) (by positivity)
    calc _ ≤ 5 * (halfZ x : ℝ) * (2 * Real.log x) ^ 3 * Real.log x * 2 := h2
      _ = 80 * ((halfZ x : ℝ) * Real.log x ^ 4) := by ring
  -- `80 z L⁴ ≤ 10⁻⁶ y η`, multiplied through by `L³ e^{12Λ} > 0`
  have hB : 80 * ((halfZ x : ℝ) * Real.log x ^ 4) ≤ 1 / 1000000 * ((halfY x : ℝ) * halfEta x) := by
    have hpos : 0 < Real.log x ^ 3 * Real.exp (12 * Real.log (Real.log x)) := by positivity
    refine le_of_mul_le_mul_right ?_ hpos
    have e1 : 80 * ((halfZ x : ℝ) * Real.log x ^ 4)
        * (Real.log x ^ 3 * Real.exp (12 * Real.log (Real.log x)))
        = 80 * ((halfZ x : ℝ) * Real.exp (12 * Real.log (Real.log x))) * Real.log x ^ 7 := by
      ring
    have e2 : 1 / 1000000 * ((halfY x : ℝ) * halfEta x)
        * (Real.log x ^ 3 * Real.exp (12 * Real.log (Real.log x)))
        = 1 / 1000000 * (halfY x : ℝ) * (halfEta x * Real.log x ^ 3)
          * Real.exp (12 * Real.log (Real.log x)) := by ring
    rw [e1, e2, hηL, hL7]
    have hE7 := Real.exp_pos (7 * Real.log (Real.log x))
    calc 80 * ((halfZ x : ℝ) * Real.exp (12 * Real.log (Real.log x)))
          * Real.exp (7 * Real.log (Real.log x))
        ≤ 80 * (2 * (halfY x : ℝ)) * Real.exp (7 * Real.log (Real.log x)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzy2 (by norm_num)) hE7.le
      _ ≤ 1 / 1000000 * (halfY x : ℝ) * 1 * Real.exp (12 * Real.log (Real.log x)) := by
          rw [h12]
          have := mul_le_mul_of_nonneg_left h5 (mul_nonneg hy0.le hE7.le)
          nlinarith
  rw [div_le_iff₀ (by positivity)]
  have : (halfY x : ℝ) * halfEta x ≤ (halfY x : ℝ) * halfEta x + 1 + halfEta x := by linarith
  nlinarith

/-- `(1+η)²(η/(1+η) + 1/y)/η = (1+η) + (1+η)²/(yη) ≤ 1 + 2·10⁻⁶`. -/
lemma half_mid_le {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    (1 + halfEta x) ^ 2 * (halfEta x / (1 + halfEta x) + 1 / (halfY x : ℝ)) / halfEta x
      ≤ 1 + 2 / 1000000 := by
  obtain ⟨-, -, hΛ, -, -, -⟩ := half_params hx
  obtain ⟨hy2, -, -, -, -, hyh⟩ := halfY_facts hx
  obtain ⟨hη0, hηL, hη, -, -⟩ := half_eta_eps hx
  have ha := halfA_ge hx
  have hy0 : (0 : ℝ) < (halfY x : ℝ) := by
    have : (2 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast hy2
    linarith
  have e1 : (1 + halfEta x) ^ 2 * (halfEta x / (1 + halfEta x) + 1 / (halfY x : ℝ))
      / halfEta x = (1 + halfEta x) + (1 + halfEta x) ^ 2 / ((halfY x : ℝ) * halfEta x) := by
    field_simp
  rw [e1]
  have hL3 := half_log_pow hx 3
  push_cast at hL3
  have hyL : 4000000 * Real.log x ^ 3 ≤ (halfY x : ℝ) := by
    rw [hL3]
    have h3 : (8000000 : ℝ) ≤ Real.exp 100 := by interval_decide (trust := kernel)
    have h2 : (8000000 : ℝ) * Real.exp (3 * Real.log (Real.log x)) ≤ Real.exp (halfA x) :=
      calc (8000000 : ℝ) * Real.exp (3 * Real.log (Real.log x))
          ≤ Real.exp 100 * Real.exp (3 * Real.log (Real.log x)) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ = Real.exp (100 + 3 * Real.log (Real.log x)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (halfA x) := Real.exp_le_exp.2 (by linarith)
    linarith
  have hyη : 4000000 ≤ (halfY x : ℝ) * halfEta x := by
    have := mul_le_mul_of_nonneg_right hyL hη0.le
    calc (4000000 : ℝ) = 4000000 * (halfEta x * Real.log x ^ 3) := by rw [hηL]; ring
      _ = 4000000 * Real.log x ^ 3 * halfEta x := by ring
      _ ≤ (halfY x : ℝ) * halfEta x := this
  have h1 : (1 + halfEta x) ^ 2 / ((halfY x : ℝ) * halfEta x) ≤ 1 / 1000000 := by
    rw [div_le_iff₀ (by positivity)]
    have h4 : (1 + halfEta x) ^ 2 ≤ 4 := by nlinarith
    nlinarith
  linarith

/-- **The reduction's constant**: `C_R ≤ 0.33885` (the limit is `e^{1/16}/π = 0.338841`). -/
lemma halfCR_le {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32)
      ≤ 33885 / 100000 := by
  obtain ⟨hη0, -, -, hε0, hε⟩ := half_eta_eps hx
  obtain ⟨-, -, -, -, -, -⟩ := half_params hx
  obtain ⟨hz2, hzy, -⟩ := halfZ_facts hx
  have hsieve : smallQSieveConst (halfY x) (halfZ x) (halfEta x) ≤ 2 + 3 / 1000000 := by
    have h1 := half_ratio_le hx
    have h2 := half_second_le hx
    rw [smallQSieveConst]
    linarith
  have hmid := half_mid_le hx
  have hmid0 : 0 ≤ (1 + halfEta x) ^ 2 * (halfEta x / (1 + halfEta x) + 1 / (halfY x : ℝ))
      / halfEta x := by positivity
  have hsieve0 : 0 ≤ smallQSieveConst (halfY x) (halfZ x) (halfEta x) :=
    (smallQSieveConst_pos hz2 hzy hη0).le
  have hpi := Real.pi_gt_d6
  have hinvpi : (2 * Real.pi)⁻¹ ≤ 1 / (2 * 3.141592) := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hexp : Real.exp (2 * (1 / 32)) ≤ 1064495 / 1000000 := by
    interval_decide (trust := kernel)
  unfold smallQReductionConst
  calc (1 + halfEps x) * smallQSieveConst (halfY x) (halfZ x) (halfEta x)
        * ((1 + halfEta x) ^ 2 * (halfEta x / (1 + halfEta x) + 1 / (halfY x : ℝ)) / halfEta x)
        * Real.exp (2 * (1 / 32)) * (2 * Real.pi)⁻¹
      ≤ (1 + 1 / 1000000) * (2 + 3 / 1000000) * (1 + 2 / 1000000) * (1064495 / 1000000)
        * (1 / (2 * 3.141592)) := by
        gcongr
    _ ≤ 33885 / 100000 := by norm_num

/-! ### The central window and the far range -/

/-- `(2·1.195/e^{-4})^{1/2} ≤ 11.43`. -/
lemma half_far_le : (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ (1 / 2 : ℝ) ≤ 1143 / 100 := by
  refine rpow_half_le_of_le (by norm_num) ?_
  push_cast
  rw [div_le_iff₀ (Real.exp_pos _)]
  have : (18294 / 1000000 : ℝ) ≤ Real.exp (-4) := by interval_decide (trust := kernel)
  nlinarith

/-! ### The windows -/

/-- `log log y ≤ Λ`, and `log y ≥ 22000`. -/
lemma halfY_loglog_le {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    Real.log (Real.log (halfY x)) ≤ Real.log (Real.log x) ∧ 22000 ≤ Real.log (halfY x) := by
  obtain ⟨-, -, hΛ, -, -, haL⟩ := half_params hx
  obtain ⟨-, -, hlogy_le, hlogy_ge, -, -⟩ := halfY_facts hx
  have ha := halfA_ge hx
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hly : 22000 ≤ Real.log (halfY x) := by linarith
  exact ⟨Real.log_le_log (by linarith) (by linarith), hly⟩

lemma halfChaosConst_nonneg (E₀ : ℝ) : 0 ≤ halfChaosConst E₀ := by
  rw [halfChaosConst, shiftMomentConst]
  exact le_trans (Real.rpow_nonneg (by norm_num) _) (le_max_left _ _)

/-- `(1 + ½√n)^{-1/2} ≤ 0.2071` for `n ≥ 2000`. -/
lemma chaos_factor_le_small {n : ℝ} (hn : 2000 ≤ n) :
    (1 + (1 - 1 / 2) * Real.sqrt n) ^ (-(1 / 2 : ℝ)) ≤ 2071 / 10000 := by
  have hs : (44676 / 1000 : ℝ) ≤ Real.sqrt n := by
    rw [show (44676 / 1000 : ℝ) = Real.sqrt ((44676 / 1000) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have ht : (23338 / 1000 : ℝ) ≤ 1 + (1 - 1 / 2) * Real.sqrt n := by linarith
  have ht0 : (0 : ℝ) < 1 + (1 - 1 / 2) * Real.sqrt n := by linarith
  rw [Real.rpow_neg ht0.le, ← Real.sqrt_eq_rpow, inv_le_comm₀ (Real.sqrt_pos.2 ht0) (by norm_num)]
  rw [show ((2071 / 10000 : ℝ))⁻¹ = Real.sqrt (((2071 / 10000 : ℝ))⁻¹ ^ 2) from
    (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num; linarith)

/-- `(1 + ½√n)^{-1/2} ≤ 1.4143·n^{-1/4}` for `n > 0`. -/
lemma chaos_factor_le_pow {n : ℝ} (hn : 0 < n) :
    (1 + (1 - 1 / 2) * Real.sqrt n) ^ (-(1 / 2 : ℝ)) ≤ 14143 / 10000 * n ^ (-(1 / 4 : ℝ)) := by
  have hpos : 0 < (1 - 1 / 2) * Real.sqrt n := by
    have := Real.sqrt_pos.2 hn
    positivity
  refine le_trans (Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by norm_num)) ?_
  rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
  have h2 : ((1 : ℝ) - 1 / 2) ^ (-(1 / 2 : ℝ)) ≤ 14143 / 10000 := by
    rw [show ((1 : ℝ) - 1 / 2) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num), Real.rpow_neg
      (by norm_num), inv_inv, ← Real.sqrt_eq_rpow]
    rw [show (14143 / 10000 : ℝ) = Real.sqrt ((14143 / 10000) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h3 : (1 / 2 : ℝ) * -(1 / 2) = -(1 / 4) := by norm_num
  rw [h3]
  exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hn.le _)

/-! ### The sum over the chaos windows -/

/-- **The chaos windows' sum against an integral**: for `m ≥ 2105`,
`∑_{97≤k<m-2007}(m - 8 - k)^{-1/4} ≤ (4/3)((m - 105)^{3/4} - 1999^{3/4})`. -/
lemma sum_chaos_rpow_le {m : ℕ} (hm : 2105 ≤ m) :
    ∑ k ∈ Finset.Ico 97 (m - 2007), ((m : ℝ) - 8 - k) ^ (-(1 / 4 : ℝ))
      ≤ 4 / 3 * (((m : ℝ) - 105) ^ (3 / 4 : ℝ) - 1999 ^ (3 / 4 : ℝ)) := by
  have hab : 97 ≤ m - 2007 := by omega
  have hcast : ((m - 2007 : ℕ) : ℝ) = (m : ℝ) - 2007 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hmR : (2105 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmono : MonotoneOn (fun u : ℝ => ((m : ℝ) - 8 - u) ^ (-(1 / 4 : ℝ)))
      (Set.Icc ((97 : ℕ) : ℝ) ((m - 2007 : ℕ) : ℝ)) := by
    intro u hu v hv huv
    rw [hcast] at hu hv
    simp only [Set.mem_Icc] at hu hv
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  have h := MonotoneOn.sum_le_integral_Ico hab hmono
  refine le_trans h (le_of_eq ?_)
  rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (-(1 / 4 : ℝ))) ((m : ℝ) - 8),
    hcast, integral_rpow (Or.inl (by norm_num))]
  push_cast
  rw [show (m : ℝ) - 8 - ((m : ℝ) - 2007) = 1999 by ring,
    show (m : ℝ) - 8 - 97 = (m : ℝ) - 105 by ring,
    show (-(1 / 4 : ℝ)) + 1 = 3 / 4 by norm_num]
  ring

/-- `1999^{3/4} ≥ 298.9`. -/
lemma rpow_1999_ge : (2989 / 10 : ℝ) ≤ 1999 ^ (3 / 4 : ℝ) := by
  by_contra h
  have h1 : (1999 : ℝ) ^ (3 / 4 : ℝ) < 2989 / 10 := not_le.1 h
  have h0 : 0 ≤ (1999 : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h4 : ((1999 : ℝ) ^ (3 / 4 : ℝ)) ^ 4 < (2989 / 10) ^ 4 :=
    pow_lt_pow_left₀ h1 h0 (by norm_num)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h4
  norm_num at h4

/-! ### The mesoscopic range -/

/-- `log log y ≥ 0.9Λ` for `Λ ≥ 400`. -/
lemma halfY_loglog_ge {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ4 : 400 ≤ Real.log (Real.log x)) :
    9 / 10 * Real.log (Real.log x) ≤ Real.log (Real.log (halfY x)) := by
  obtain ⟨-, hL, hΛ, hexpΛ, -, -⟩ := half_params hx
  obtain ⟨-, -, -, hlogy_ge, -, -⟩ := halfY_facts hx
  have ha := halfA_ge hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  -- `log y ≥ a/2 = L/Λ`
  have hA : halfA x * Real.log (Real.log x) = 2 * Real.log x := by
    rw [halfA]
    field_simp
  have hly : Real.log x / Real.log (Real.log x) ≤ Real.log (halfY x) := by
    rw [div_le_iff₀ hΛpos]
    nlinarith
  have hLΛ : 0 < Real.log x / Real.log (Real.log x) := by positivity
  have h1 : Real.log (Real.log x / Real.log (Real.log x)) ≤ Real.log (Real.log (halfY x)) :=
    Real.log_le_log hLΛ hly
  rw [Real.log_div hLpos.ne' hΛpos.ne'] at h1
  -- `log Λ ≤ 2√Λ ≤ Λ/10`
  have h2 : Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log x) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div hΛpos.le (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h2
  have h3 : 20 ≤ Real.sqrt (Real.log (Real.log x)) := by
    rw [show (20 : ℝ) = Real.sqrt (20 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have h4 : Real.sqrt (Real.log (Real.log x)) ^ 2 = Real.log (Real.log x) := Real.sq_sqrt hΛpos.le
  nlinarith

/-! ### Powers of `Λ^{1/4}` -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `s = Λ^{1/4}`: `s⁴ = Λ`, `s³ = Λ^{3/4}`, `s² = √Λ`. -/
lemma quarter_facts {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ s : ℝ, 0 < s ∧ s ^ 4 = Λ ∧ s ^ 3 = Λ ^ (3 / 4 : ℝ) ∧ s ^ 2 = Real.sqrt Λ := by
  refine ⟨Λ ^ (1 / 4 : ℝ), Real.rpow_pos_of_pos hΛ _, ?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ.le]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ.le]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ.le, Real.sqrt_eq_rpow]
    norm_num

end RMF
