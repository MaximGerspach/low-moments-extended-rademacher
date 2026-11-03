/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.TenAssemblyExplicit
import RMF.Weighted.HalfNumeralExplicit

/-!
# The first moment of the weighted Rademacher sum with the constant `10`

The five pieces of `RMF.integral_norm_weightedRademacherSum_le_ten_assembly`, evaluated:

* **the chaos constant** `≤ 4.68` (`RMF.halfChaosConst_le`) and `≤ 4.55` past `Λ = 10⁴`
  (`RMF.halfChaosConstB_le`: its leaves at `E₀ ≤ 1/160000`, then kernel interval arithmetic);
* **the windows** at slope `3/2`: `G_k ≤ 2.2437` for `k ≥ 4` and `≤ 1.909` for `k ≥ 97`;
* **the central window** `C_c ≤ 50.266Λ + 2.793`;
* the reduction's pieces: `C_R ≤ 0.33885`, the tail and the error `≤ 1`, the far range `≤ 11.43`.

Headline `RMF.integral_norm_weightedRademacherSum_le_ten`:
`E|∑_{n≤x} f(n)/√n| ≤ 10 (log log x)^{3/4}` for `x ≥ exp(e^{110})`.  The certificate peaks at
`≈ 9.68` near `Λ = 10⁵` and tends to `9.53`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The chaos constant at `Λ ≥ 10⁴`, i.e. `E₀ ≤ 1/160000` -/

lemma sqrt_le_of_le_tilt_B {E₀ : ℝ} (hE₀1 : E₀ ≤ 1 / 160000) : Real.sqrt E₀ ≤ 1 / 400 := by
  calc Real.sqrt E₀ ≤ Real.sqrt ((1 / 400) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = 1 / 400 := Real.sqrt_sq (by norm_num)

lemma radAveragedConst_le_B {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 160000) :
    radAveragedConst E₀ (11 / 20) 30 8 ≤ 12285 / 10000 := by
  have hK := radAveragedK_le_half (E₀ := E₀) (by linarith)
  have hK0 : 0 ≤ radAveragedK E₀ := le_trans zero_le_one (one_le_radAveragedK hE₀)
  have he := exp_neg_hundred_le
  unfold radAveragedConst
  rw [div_le_iff₀ (by norm_num)]
  have h1 : (1 + Real.exp (-100)) * radAveragedK E₀ ≤ (1 + 1 / 10000000) * (116341 / 100000) :=
    mul_le_mul (by linarith) hK hK0 (by norm_num)
  nlinarith

lemma driftRadSharpOf_le_B {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 160000) :
    driftRadSharpOf E₀ 16 (Real.exp (-(2 * E₀)) / 100) ≤ 1226 / 10000 := by
  have hs := sqrt_le_of_le_tilt_B hE₀1
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

lemma log_eight_le : Real.log 8 ≤ 2079442 / 1000000 := by
  interval_decide (trust := kernel)

lemma log_KT_rad_le_B : Real.log (116341 / 100000 * 30) ≤ 3552560 / 1000000 := by
  interval_decide (trust := kernel)

lemma radAveragedShift_le_B {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 160000) :
    radAveragedShift E₀ (11 / 20) 30 8 ≤ 13069 / 1000 := by
  have hd := driftRadSharpOf_le_B hE₀ hE₀1
  have hlog2 : Real.log 2 ≤ 693148 / 1000000 := by linarith [Real.log_two_lt_d9]
  have hlog50 : Real.log (2 * ((25 : ℕ) : ℝ)) ≤ 3912024 / 1000000 := by
    rw [show (2 : ℝ) * ((25 : ℕ) : ℝ) = 50 by norm_num]
    exact log_fifty_le
  have hpi := Real.pi_lt_d6
  have hsq : √(Real.pi * 1 / 2) ≤ 1253315 / 1000000 := by
    have h : Real.pi * 1 / 2 ≤ (1253315 / 1000000) ^ 2 := by nlinarith
    calc √(Real.pi * 1 / 2) ≤ √((1253315 / 1000000) ^ 2) := Real.sqrt_le_sqrt h
      _ = 1253315 / 1000000 := Real.sqrt_sq (by norm_num)
  have hK := radAveragedK_le_half (E₀ := E₀) (by linarith)
  have hK1 := one_le_radAveragedK hE₀
  have hlogKT : Real.log (radAveragedK E₀ * 30) ≤ 3552560 / 1000000 :=
    le_trans (Real.log_le_log (by positivity) (by linarith)) log_KT_rad_le_B
  have hl8 := log_eight_le
  unfold radAveragedShift result1SharpShift
  push_cast
  nlinarith

/-- `radBlockBadConst E₀ (11/20)·e⁸ ≤ e^{26.28}` for `E₀ ≤ 1/160000`. -/
lemma radBlockBadConst_mul_le_B {E₀ : ℝ} (hE₀1 : E₀ ≤ 1 / 160000) :
    radBlockBadConst E₀ (11 / 20) * Real.exp 8 ≤ Real.exp (2628 / 100) := by
  have hs := sqrt_le_of_le_tilt_B hE₀1
  have hRC := radChainConst_le_half
  have hRC0 : 0 < radChainConst (2 / 1152) := radChainConst_pos (by norm_num)
  have hζ := tsum_nat_rpow_neg_le (s := 2 * (11 / 20)) (by norm_num)
  have hζ0 : (0 : ℝ) ≤ ∑' i : ℕ, (i : ℝ) ^ (-(2 * (11 / 20 : ℝ))) :=
    tsum_nonneg fun i => Real.rpow_nonneg (Nat.cast_nonneg i) _
  have hD : harperSharpDeficit E₀ ≤ 11125 / 10000 := by
    rw [harperSharpDeficit]
    linarith
  have hexpD : Real.exp (harperSharpDeficit E₀) ≤ Real.exp (11125 / 10000) := Real.exp_le_exp.2 hD
  have hnum : (4 * 1152 * (5613 / 10) * (2 * (11 / 20) / (2 * (11 / 20) - 1)) : ℝ)
      * Real.exp (11125 / 10000) * Real.exp 8 ≤ Real.exp (2628 / 100) := by
    interval_decide (trust := kernel)
  unfold radBlockBadConst radIndexConst
  rw [show radIndexRefine = 1152 from rfl]
  have h1 : 4 * 1152 * radChainConst (2 / 1152) * Real.exp (harperSharpDeficit E₀)
      ≤ 4 * 1152 * (5613 / 10) * Real.exp (11125 / 10000) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hRC (by norm_num)) hexpD (Real.exp_pos _).le
      (by norm_num)
  have h2 := mul_le_mul h1 hζ hζ0 (by positivity)
  have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos 8).le
  refine le_trans (le_of_eq_of_le ?_ h3) ?_
  · ring
  · calc 4 * 1152 * (5613 / 10) * Real.exp (11125 / 10000) * (2 * (11 / 20) / (2 * (11 / 20) - 1))
          * Real.exp 8
        = (4 * 1152 * (5613 / 10) * (2 * (11 / 20) / (2 * (11 / 20) - 1)) : ℝ)
          * Real.exp (11125 / 10000) * Real.exp 8 := by ring
      _ ≤ Real.exp (2628 / 100) := hnum

/-- **The chaos constant past `Λ = 10⁴`**: `RMF.halfChaosConstB E₀ ≤ 4.55` for
`0 ≤ E₀ ≤ 1/160000`. -/
theorem halfChaosConstB_le {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 160000) :
    halfChaosConstB E₀ ≤ 455 / 100 := by
  have hCi := radAveragedConst_le_B hE₀ hE₀1
  have hCi0 : 0 ≤ radAveragedConst E₀ (11 / 20) 30 8 := by
    have := one_le_radAveragedConst hE₀ (by norm_num : (0 : ℝ) ≤ 11 / 20) (by norm_num)
      (by norm_num : (4 : ℝ) < 30) (by norm_num : (1 : ℝ) ≤ 8)
    linarith
  have hs := radAveragedShift_le_B hE₀ hE₀1
  have hs0 := radAveragedShift_nonneg hE₀ (by norm_num : (0 : ℝ) ≤ 11 / 20) (by norm_num)
    (by norm_num : (4 : ℝ) < 30) (by norm_num : (1 : ℝ) ≤ 8)
  have hCb := radBlockBadConst_mul_le_B hE₀1
  have hCb0 : 0 ≤ radBlockBadConst E₀ (11 / 20) * Real.exp 8 :=
    mul_nonneg (radBlockBadConst_pos E₀ (by norm_num)).le (Real.exp_pos _).le
  have hAs : (0 : ℝ) ≤ 18 + radAveragedShift E₀ (11 / 20) 30 8 := by linarith
  have hU : (18 + radAveragedShift E₀ (11 / 20) 30 8) * (1 - 1 / 2) ≤ 155345 / 10000 := by
    linarith
  have h := shiftMomentConst_le_exp (C₁ := 1) (N := 1)
    (Ci := radAveragedConst E₀ (11 / 20) 30 8) (Ci' := 12285 / 10000)
    (Cb := radBlockBadConst E₀ (11 / 20) * Real.exp 8) (LB := 2628 / 100)
    (s := radAveragedShift E₀ (11 / 20) 30 8) (U := 155345 / 10000) (IS := 10102 / 10000)
    (S1 := 1156519 / 1000000) (S2 := 181016 / 1000000) (EM2 := 135336 / 1000000) (A := 18)
    (lam := 98 / 5) (δ := 1 / 50) (q := 1 / 2) (by norm_num) (by norm_num) zero_le_one le_rfl
    hCi0 hCi hCb0 hCb hAs hU (by norm_num) (by norm_num) inv_sqrt_one_sub_fiftieth_le
    inv_one_sub_exp_neg_two_le exp_neg_two_mul_inv_sq_le exp_neg_two_le_cert
  rw [halfChaosConstB]
  refine le_trans h ?_
  refine max_le ?_ ?_
  · interval_decide (trust := kernel)
  · interval_decide (trust := kernel)

/-! ### The windows' constants at slope `3/2` -/

lemma thetaWindowExp_anti {θ : ℝ} (hθ : 0 ≤ θ) {k k' : ℕ} (h : k ≤ k') :
    thetaWindowExp θ k' ≤ thetaWindowExp θ k := by
  have hkk : (k : ℝ) ≤ (k' : ℝ) := by exact_mod_cast h
  have hE : Real.exp (-(k' : ℝ)) ≤ Real.exp (-(k : ℝ)) := Real.exp_le_exp.2 (by linarith)
  have hE0 : 0 ≤ Real.exp (-(k' : ℝ)) := (Real.exp_pos _).le
  unfold thetaWindowExp
  have h1 : (θ + Real.exp (-(k' : ℝ)) / 100) ^ 2 ≤ (θ + Real.exp (-(k : ℝ)) / 100) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h2 : Real.exp (-(k' : ℝ)) ^ 2 ≤ Real.exp (-(k : ℝ)) ^ 2 := pow_le_pow_left₀ hE0 hE 2
  have h3 : θ * Real.exp (-(k' : ℝ)) ≤ θ * Real.exp (-(k : ℝ)) := mul_le_mul_of_nonneg_left hE hθ
  linarith

lemma thetaWindowExp_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (k : ℕ) : 0 ≤ thetaWindowExp θ k := by
  unfold thetaWindowExp
  have := Real.exp_pos (-(k : ℝ))
  positivity

lemma thetaWindowConst_nonneg {θ : ℝ} (hθ : 0 < θ) (k y : ℕ) : 0 ≤ thetaWindowConst θ k y := by
  unfold thetaWindowConst
  have := taylorWindowW_nonneg (thetaWindowExp_nonneg hθ.le k)
  positivity

/-- `1 - e⁻³ ≤ 0.950213`. -/
lemma one_sub_exp_one_inv_cube_le : 1 - (Real.exp 1)⁻¹ ^ 3 ≤ 950213 / 1000000 := by
  have h1 : (10000000000 / 27182818286 : ℝ) ≤ (Real.exp 1)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have h2 : (10000000000 / 27182818286 : ℝ) ^ 3 ≤ (Real.exp 1)⁻¹ ^ 3 :=
    pow_le_pow_left₀ (by norm_num) h1 3
  have h3 : (1 : ℝ) - 950213 / 1000000 ≤ (10000000000 / 27182818286 : ℝ) ^ 3 := by norm_num
  linarith

/-- The window constant at slope `3/2` at numerals: `b ≥ b_{k₀}`,
`c ≥ 9.0028/L₀ + 9.0028e^{-k₀}/(3/2)`. -/
lemma thetaWindowConst_le_num {k₀ k y : ℕ} (hk : k₀ ≤ k) {L₀ b c : ℝ} (hL₀ : 0 < L₀)
    (hy : L₀ ≤ Real.log y) (hb : thetaWindowExp (3 / 2) k₀ ≤ b)
    (hc : 9.0028 / L₀ + 9.0028 * Real.exp (-(k₀ : ℝ)) / (3 / 2) ≤ c) :
    thetaWindowConst (3 / 2) k y
      ≤ 2 / (3 / 2) * (17182818286 / 10000000000 + b * (6321206 / 10000000)
        + (Real.exp b - 1 - b) * (950213 / 3000000)) * Real.exp c := by
  have hbk : thetaWindowExp (3 / 2) k ≤ b :=
    le_trans (thetaWindowExp_anti (by norm_num) hk) hb
  have hb0 : 0 ≤ thetaWindowExp (3 / 2) k := thetaWindowExp_nonneg (by norm_num) k
  have hW := taylorWindowW_mono hbk
  have hWb : taylorWindowW b ≤ 17182818286 / 10000000000 + b * (6321206 / 10000000)
      + (Real.exp b - 1 - b) * (950213 / 3000000) := by
    unfold taylorWindowW
    have he1 : Real.exp 1 - 1 ≤ 17182818286 / 10000000000 := by
      linarith [Real.exp_one_lt_d9]
    have hinv : 1 - (Real.exp 1)⁻¹ ≤ 6321206 / 10000000 := by
      have h1 : (10000000000 / 27182818286 : ℝ) ≤ (Real.exp 1)⁻¹ := by
        rw [le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
        have := Real.exp_one_lt_d9
        norm_num at this ⊢
        linarith
      linarith [show (1 : ℝ) - 10000000000 / 27182818286 ≤ 6321206 / 10000000 by norm_num]
    have hc3 := one_sub_exp_one_inv_cube_le
    have hb0' : 0 ≤ b := le_trans hb0 hbk
    have heb : 0 ≤ Real.exp b - 1 - b := by linarith [Real.add_one_le_exp b]
    have t1 : b * (1 - (Real.exp 1)⁻¹) ≤ b * (6321206 / 10000000) :=
      mul_le_mul_of_nonneg_left hinv hb0'
    have t2 : (Real.exp b - 1 - b) * (1 - (Real.exp 1)⁻¹ ^ 3)
        ≤ (Real.exp b - 1 - b) * (950213 / 1000000) := mul_le_mul_of_nonneg_left hc3 heb
    linarith
  have hk' : (k₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hexp : 9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / (3 / 2) ≤ c := by
    have e1 : 9.0028 / Real.log y ≤ 9.0028 / L₀ := div_le_div_of_nonneg_left (by norm_num) hL₀ hy
    have e2 : Real.exp (-(k : ℝ)) ≤ Real.exp (-(k₀ : ℝ)) := Real.exp_le_exp.2 (by linarith)
    linarith
  have hW0 : 0 ≤ taylorWindowW (thetaWindowExp (3 / 2) k) := taylorWindowW_nonneg hb0
  unfold thetaWindowConst
  exact mul_le_mul (mul_le_mul_of_nonneg_left (le_trans hW hWb) (by norm_num))
    (Real.exp_le_exp.2 hexp) (Real.exp_pos _).le (by linarith)

/-- **`G_k ≤ 2.2437` for every window at slope `3/2`**, `k ≥ 4`, `log y ≥ 22000`. -/
lemma thetaWindowConst_rpow_le_four {k y : ℕ} (hk : 4 ≤ k) (hy : 22000 ≤ Real.log y) :
    thetaWindowConst (3 / 2) k y ^ (1 / 2 : ℝ) ≤ 22437 / 10000 := by
  have hE := exp_neg_four_le_sharp
  have hE0 := (Real.exp_pos (-4)).le
  have hb : thetaWindowExp (3 / 2) 4 ≤ 1549 / 1000 := by
    unfold thetaWindowExp
    push_cast
    nlinarith [mul_le_mul hE hE hE0 (by norm_num)]
  have hc : 9.0028 / 22000 + 9.0028 * Real.exp (-((4 : ℕ) : ℝ)) / (3 / 2) ≤ 1104 / 10000 := by
    push_cast
    nlinarith
  refine rpow_half_le_of_le (by norm_num) ?_
  refine le_trans (thetaWindowConst_le_num hk (by norm_num) hy hb hc) ?_
  interval_decide (trust := kernel)

/-- **`G_k ≤ 1.909` past `k = 97` at slope `3/2`**, `log y ≥ 22000`. -/
lemma thetaWindowConst_rpow_le_hi {k y : ℕ} (hk : 97 ≤ k) (hy : 22000 ≤ Real.log y) :
    thetaWindowConst (3 / 2) k y ^ (1 / 2 : ℝ) ≤ 1909 / 1000 := by
  have hE : Real.exp (-97) ≤ 1 / 10000000000 := by
    interval_decide (trust := kernel)
  have hE0 := (Real.exp_pos (-97)).le
  have hb : thetaWindowExp (3 / 2) 97 ≤ 11250001 / 10000000 := by
    unfold thetaWindowExp
    push_cast
    nlinarith [mul_le_mul hE hE hE0 (by norm_num)]
  have hc : 9.0028 / 22000 + 9.0028 * Real.exp (-((97 : ℕ) : ℝ)) / (3 / 2) ≤ 41 / 100000 := by
    push_cast
    nlinarith
  refine rpow_half_le_of_le (by norm_num) ?_
  refine le_trans (thetaWindowConst_le_num hk (by norm_num) hy hb hc) ?_
  interval_decide (trust := kernel)

/-! ### The central window at slope `3/2` -/

/-- **The central window at slope `3/2`**: `C_c ≤ 50.266Λ + 2.793`: `π/(σ log y) ≤ 16πΛ(1 + 10⁻⁶)`
and, with `u = w log y ≤ 3/2`, `2(e^{S₂w²} - 1)/(w log y) ≤ (4/3)(e^{1.1295} - 1)` (convexity in
`(u/(3/2))²`). -/
lemma tenCen_le {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    tenCen x ≤ 50266 / 1000 * Real.log (Real.log x) + 2793 / 1000 := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, ha9, -⟩ := half_params hx
  obtain ⟨hy2, -, hlogy_le, hlogy_ge, -, -⟩ := halfY_facts hx
  have ha := halfA_ge hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hly : 22000 ≤ Real.log (halfY x) := by linarith
  have hlypos : 0 < Real.log (halfY x) := by linarith
  have hA : halfA x * Real.log (Real.log x) = 2 * Real.log x := by
    rw [halfA]
    field_simp
  have hLbig : 60000 * Real.log (Real.log x) ≤ Real.log x := by
    have h := hundred_mul_pow_ten_le_exp hΛ
    rw [hexpΛ] at h
    have h9 : (110 : ℝ) ^ 9 ≤ Real.log (Real.log x) ^ 9 := pow_le_pow_left₀ (by norm_num) hΛ 9
    have : Real.log (Real.log x) ^ 10 = Real.log (Real.log x) ^ 9 * Real.log (Real.log x) := by
      ring
    nlinarith
  unfold tenCen
  rw [add_div]
  -- the first part
  have hp1 : Real.pi / halfSigma x / Real.log (halfY x) ≤ 50266 / 1000 * Real.log (Real.log x) := by
    have e1 : Real.pi / halfSigma x = 32 * Real.pi * Real.log x := by
      rw [halfSigma]
      field_simp
    rw [e1, div_le_iff₀ hlypos]
    have hpi := Real.pi_lt_d6
    have h1 := mul_le_mul_of_nonneg_left hlogy_ge hΛpos.le
    nlinarith
  -- the second part
  have hw0 : 0 < Real.exp (-((tenJ x : ℕ) : ℝ)) := Real.exp_pos _
  have hwly : Real.exp (-((tenJ x : ℕ) : ℝ)) * Real.log (halfY x) ≤ 3 / 2 := by
    have h23 : 0 < 2 / 3 * Real.log (halfY x) := by positivity
    have hJ : Real.log (2 / 3 * Real.log (halfY x)) ≤ ((tenJ x : ℕ) : ℝ) := by
      rw [tenJ]
      push_cast
      exact (Nat.lt_floor_add_one _).le
    calc Real.exp (-((tenJ x : ℕ) : ℝ)) * Real.log (halfY x)
        ≤ Real.exp (-Real.log (2 / 3 * Real.log (halfY x))) * Real.log (halfY x) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hlypos.le
      _ = 3 / 2 := by
          rw [Real.exp_neg, Real.exp_log h23]
          field_simp
  have hS : Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34
      ≤ 502 / 1000 * Real.log (halfY x) ^ 2 := by
    have hy0 : (0 : ℝ) < (halfY x : ℝ) := by
      have : (2 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast hy2
      linarith
    have h1 : Real.log ((halfY x : ℝ) + 1) ≤ Real.log (halfY x) + 1 := by
      have h2 : Real.log ((halfY x : ℝ) + 1) ≤ Real.log (2 * (halfY x : ℝ)) :=
        Real.log_le_log (by positivity) (by
          have : (1 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast (by omega : 1 ≤ halfY x)
          linarith)
      rw [Real.log_mul (by norm_num) hy0.ne'] at h2
      linarith
    have h0 : 0 ≤ Real.log ((halfY x : ℝ) + 1) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ (halfY x : ℝ) := hy0.le
      linarith)
    have h3 : Real.log ((halfY x : ℝ) + 1) ^ 2 ≤ (Real.log (halfY x) + 1) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    nlinarith
  set w := Real.exp (-((tenJ x : ℕ) : ℝ)) with hwdef
  set ly := Real.log (halfY x) with hlydef
  set S₂ := Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34
    with hS₂def
  have hS0 : 0 ≤ S₂ := by
    rw [hS₂def]
    have h0 : 0 ≤ Real.log ((halfY x : ℝ) + 1) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ (halfY x : ℝ) := Nat.cast_nonneg _
      linarith)
    positivity
  have hκ0 : 0 ≤ 9 / 4 * (S₂ / ly ^ 2) := by positivity
  have hκ : 9 / 4 * (S₂ / ly ^ 2) ≤ 11295 / 10000 := by
    have : S₂ / ly ^ 2 ≤ 502 / 1000 := by
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
  have hek : Real.exp (9 / 4 * (S₂ / ly ^ 2)) - 1 ≤ 20942 / 10000 := by
    have : Real.exp (11295 / 10000) ≤ 30942 / 10000 := by interval_decide (trust := kernel)
    linarith [Real.exp_le_exp.2 hκ]
  have hp2 : 2 * (Real.exp (2 * (1 - 1 / 2) * S₂ * w ^ 2) - 1) / w / ly ≤ 2793 / 1000 := by
    rw [show (2 : ℝ) * (1 - 1 / 2) * S₂ * w ^ 2 = S₂ * w ^ 2 by ring, hexp1, div_div,
      div_le_iff₀ (by positivity)]
    have h1 : Real.exp ((w * ly) ^ 2 / (9 / 4) * (9 / 4 * (S₂ / ly ^ 2))) - 1
        ≤ (w * ly) ^ 2 / (9 / 4) * (Real.exp (9 / 4 * (S₂ / ly ^ 2)) - 1) := by linarith
    have h2 : (w * ly) ^ 2 / (9 / 4) * (Real.exp (9 / 4 * (S₂ / ly ^ 2)) - 1)
        ≤ (w * ly) * (3 / 2) / (9 / 4) * (20942 / 10000) := by
      have hsq : (w * ly) ^ 2 ≤ (w * ly) * (3 / 2) := by
        rw [sq]
        exact mul_le_mul_of_nonneg_left hwly hwl0
      calc (w * ly) ^ 2 / (9 / 4) * (Real.exp (9 / 4 * (S₂ / ly ^ 2)) - 1)
          ≤ (w * ly) ^ 2 / (9 / 4) * (20942 / 10000) :=
            mul_le_mul_of_nonneg_left hek hs0
        _ ≤ (w * ly) * (3 / 2) / (9 / 4) * (20942 / 10000) := by
            have := div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 9 / 4)
            linarith
    linarith
  linarith

/-- `C_c^{1/2} ≤ 7.09√Λ + 0.2` at slope `3/2`. -/
lemma tenCen_rpow_le {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    tenCen x ^ (1 / 2 : ℝ) ≤ 709 / 100 * Real.sqrt (Real.log (Real.log x)) + 2 / 10 := by
  obtain ⟨-, -, hΛ, -, -, -⟩ := half_params hx
  have hC := tenCen_le hx
  have hsq : Real.sqrt (Real.log (Real.log x)) ^ 2 = Real.log (Real.log x) :=
    Real.sq_sqrt (by linarith)
  have hs10 : 10 ≤ Real.sqrt (Real.log (Real.log x)) := by
    rw [show (10 : ℝ) = Real.sqrt (10 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  refine rpow_half_le_of_le (by positivity) ?_
  nlinarith

lemma tenCen_nonneg {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) : 0 ≤ tenCen x := by
  obtain ⟨-, hL, -, -, -, -⟩ := half_params hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hσ : 0 < halfSigma x := by rw [halfSigma]; positivity
  have he : 0 ≤ Real.exp (2 * (1 - 1 / 2)
      * (Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34)
      * Real.exp (-((tenJ x : ℕ) : ℝ)) ^ 2) - 1 := by
    have h0 : 0 ≤ Real.log ((halfY x : ℝ) + 1) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ (halfY x : ℝ) := Nat.cast_nonneg _
      linarith)
    have : 0 ≤ 2 * (1 - 1 / 2)
        * (Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34)
        * Real.exp (-((tenJ x : ℕ) : ℝ)) ^ 2 := by positivity
    linarith [Real.one_le_exp this]
  unfold tenCen
  have : 0 < Real.log (halfY x) := by linarith
  positivity

/-! ### The windows at slope `3/2` -/

lemma tenChaosConst_nonneg (x : ℝ) : 0 ≤ tenChaosConst x := by
  rw [tenChaosConst]
  split_ifs
  · rw [halfChaosConstB, shiftMomentConst]
    exact le_trans (Real.rpow_nonneg (by norm_num) _) (le_max_left _ _)
  · exact halfChaosConst_nonneg _

/-- The chaos constant of the windows, `≤ 4.68` from `Λ = 2105`. -/
lemma tenChaosConst_le {x : ℝ} (hΛ : 2105 ≤ Real.log (Real.log x)) :
    tenChaosConst x ≤ 468 / 100 := by
  have hE₀ : 1 / (16 * Real.log (Real.log x)) ≤ 1 / 33680 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hE₀0 : 0 ≤ 1 / (16 * Real.log (Real.log x)) := by
    have : 0 < Real.log (Real.log x) := by linarith
    positivity
  rw [tenChaosConst]
  split_ifs with hB
  · have hE₀B : 1 / (16 * Real.log (Real.log x)) ≤ 1 / 160000 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith [halfChaosConstB_le hE₀0 hE₀B]
  · exact halfChaosConst_le hE₀0 hE₀

/-- The chaos constant of the windows, `≤ 4.55` from `Λ = 10⁴`. -/
lemma tenChaosConst_le_B {x : ℝ} (hΛ : 10000 ≤ Real.log (Real.log x)) :
    tenChaosConst x ≤ 455 / 100 := by
  have hE₀0 : 0 ≤ 1 / (16 * Real.log (Real.log x)) := by
    have : 0 < Real.log (Real.log x) := by linarith
    positivity
  have hE₀B : 1 / (16 * Real.log (Real.log x)) ≤ 1 / 160000 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  rw [tenChaosConst, if_pos hΛ]
  exact halfChaosConstB_le hE₀0 hE₀B

/-- **A chaos window's factor is below `1`**: `tenChaosConst·(1 + √n/2)^{-1/2} ≤ 4.68·0.2071`. -/
lemma tenChaos_factor_le_one {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) {k : ℕ}
    (hc : 97 ≤ k ∧ k + 8 + 2000 ≤ ⌊Real.log (Real.log (halfY x))⌋₊) :
    tenChaosConst x * (1 + (1 - 1 / 2) * Real.sqrt (harperBlockCount (k + 8) (halfY x) : ℝ))
      ^ (-(1 / 2 : ℝ)) ≤ 1 := by
  obtain ⟨hLL, hly⟩ := halfY_loglog_le hx
  have hm : ((k + 8 + 2000 : ℕ) : ℝ) ≤ Real.log (Real.log (halfY x)) :=
    (Nat.le_floor_iff' (by omega)).1 hc.2
  have hkR : (97 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hc.1
  push_cast at hm
  have hC := tenChaosConst_le (x := x) (by linarith)
  have hC0 := tenChaosConst_nonneg x
  have hn : (2000 : ℝ) ≤ (harperBlockCount (k + 8) (halfY x) : ℝ) := by
    have : 2000 ≤ harperBlockCount (k + 8) (halfY x : ℝ) := by
      rw [harperBlockCount]
      omega
    exact_mod_cast this
  have hF := chaos_factor_le_small hn
  have hF0 : 0 ≤ (1 + (1 - 1 / 2) * Real.sqrt (harperBlockCount (k + 8) (halfY x) : ℝ))
      ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  calc _ ≤ 468 / 100 * (2071 / 10000) := mul_le_mul hC hF hF0 (by norm_num)
    _ ≤ 1 := by norm_num

lemma tenWindowBound_nonneg (x : ℝ) (k : ℕ) : 0 ≤ tenWindowBound x k := by
  have hG0 : 0 ≤ thetaWindowConst (3 / 2) k (halfY x) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (thetaWindowConst_nonneg (by norm_num) k (halfY x)) _
  rw [tenWindowBound]
  split_ifs
  · exact mul_nonneg hG0 (mul_nonneg (tenChaosConst_nonneg _) (Real.rpow_nonneg (by positivity) _))
  · exact hG0

/-- **Every window at slope `3/2` costs at most `2.2437`**, and at most `1.909` past `k = 97`,
chaos window or not. -/
lemma tenWindowBound_le {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) {k : ℕ}
    {G : ℝ} (hG : thetaWindowConst (3 / 2) k (halfY x) ^ (1 / 2 : ℝ) ≤ G) :
    tenWindowBound x k ≤ G := by
  have hG0 : 0 ≤ thetaWindowConst (3 / 2) k (halfY x) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (thetaWindowConst_nonneg (by norm_num) k (halfY x)) _
  rw [tenWindowBound]
  split_ifs with hc
  · have hCF := tenChaos_factor_le_one hx hc
    calc thetaWindowConst (3 / 2) k (halfY x) ^ (1 / 2 : ℝ) * (tenChaosConst x
          * (1 + (1 - 1 / 2) * Real.sqrt (harperBlockCount (k + 8) (halfY x) : ℝ))
            ^ (-(1 / 2 : ℝ)))
        ≤ thetaWindowConst (3 / 2) k (halfY x) ^ (1 / 2 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hCF hG0
      _ ≤ G := by linarith
  · exact hG

lemma tenWindowBound_le_small {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) {k : ℕ} (hk : 4 ≤ k) :
    tenWindowBound x k ≤ 22437 / 10000 :=
  tenWindowBound_le hx (thetaWindowConst_rpow_le_four hk (halfY_loglog_le hx).2)

lemma tenWindowBound_le_hi {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) {k : ℕ} (hk : 97 ≤ k) :
    tenWindowBound x k ≤ 1909 / 1000 :=
  tenWindowBound_le hx (thetaWindowConst_rpow_le_hi hk (halfY_loglog_le hx).2)

/-- **A chaos window at slope `3/2`** costs at most `1.909·A·1.4143·(m - 8 - k)^{-1/4}`,
`m = ⌊log log y⌋`, for any bound `A` on the chaos constant. -/
lemma tenWindowBound_le_chaos {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) {k : ℕ}
    (hk : 97 ≤ k) (hc : k + 8 + 2000 ≤ ⌊Real.log (Real.log (halfY x))⌋₊) {A : ℝ}
    (hA : tenChaosConst x ≤ A) :
    tenWindowBound x k ≤ 1909 / 1000 * A * (14143 / 10000)
      * ((⌊Real.log (Real.log (halfY x))⌋₊ : ℝ) - 8 - k) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨hLL, hly⟩ := halfY_loglog_le hx
  have hG := thetaWindowConst_rpow_le_hi hk hly
  have hG0 : 0 ≤ thetaWindowConst (3 / 2) k (halfY x) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (thetaWindowConst_nonneg (by norm_num) k (halfY x)) _
  rw [tenWindowBound, if_pos ⟨hk, hc⟩]
  have hC0 := tenChaosConst_nonneg x
  have hcast : (harperBlockCount (k + 8) (halfY x : ℝ) : ℝ)
      = (⌊Real.log (Real.log (halfY x))⌋₊ : ℝ) - 8 - k := by
    rw [harperBlockCount, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hn0 : (0 : ℝ) < (⌊Real.log (Real.log (halfY x))⌋₊ : ℝ) - 8 - k := by
    have : ((k + 8 + 2000 : ℕ) : ℝ) ≤ (⌊Real.log (Real.log (halfY x))⌋₊ : ℝ) := by
      exact_mod_cast hc
    push_cast at this
    linarith
  have hF := chaos_factor_le_pow hn0
  rw [hcast]
  have hF0 : 0 ≤ (1 + (1 - 1 / 2) * Real.sqrt ((⌊Real.log (Real.log (halfY x))⌋₊ : ℝ) - 8 - k))
      ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hP0 : 0 ≤ ((⌊Real.log (Real.log (halfY x))⌋₊ : ℝ) - 8 - k) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_nonneg hn0.le _
  calc thetaWindowConst (3 / 2) k (halfY x) ^ (1 / 2 : ℝ) * (tenChaosConst x
        * (1 + (1 - 1 / 2) * Real.sqrt ((⌊Real.log (Real.log (halfY x))⌋₊ : ℝ) - 8 - k))
          ^ (-(1 / 2 : ℝ)))
      ≤ 1909 / 1000 * (A * (14143 / 10000
          * ((⌊Real.log (Real.log (halfY x))⌋₊ : ℝ) - 8 - k) ^ (-(1 / 4 : ℝ)))) :=
        mul_le_mul hG (mul_le_mul hA hF hF0 (le_trans hC0 hA)) (mul_nonneg hC0 hF0) (by norm_num)
    _ = _ := by ring

/-! ### The mesoscopic range at slope `3/2` -/

/-- `J₀ ≤ ⌊log log y⌋ + 1` and `⌊log log y⌋ ≤ J₀`. -/
lemma tenJ_bounds {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    tenJ x ≤ ⌊Real.log (Real.log (halfY x))⌋₊ + 1 ∧ ⌊Real.log (Real.log (halfY x))⌋₊ ≤ tenJ x := by
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  have hly0 : 0 < Real.log (halfY x) := by linarith
  have h23 : 0 < 2 / 3 * Real.log (halfY x) := by positivity
  have hup : Real.log (2 / 3 * Real.log (halfY x)) ≤ Real.log (Real.log (halfY x)) :=
    Real.log_le_log h23 (by linarith)
  have hlo : Real.log (Real.log (halfY x)) - 1 ≤ Real.log (2 / 3 * Real.log (halfY x)) := by
    rw [Real.log_mul (by norm_num) hly0.ne']
    have : -1 ≤ Real.log (2 / 3) := by
      have h := Real.add_one_le_exp (-1 : ℝ)
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have he : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith [Real.exp_one_gt_d9]
      linarith
    linarith
  have hll0 : 0 ≤ Real.log (Real.log (halfY x)) := Real.log_nonneg (by linarith)
  constructor
  · rw [tenJ]
    have := Nat.floor_le_floor hup
    omega
  · rw [tenJ]
    have h1 : (⌊Real.log (Real.log (halfY x))⌋₊ : ℝ) ≤ Real.log (Real.log (halfY x)) :=
      Nat.floor_le hll0
    have h2 : Real.log (2 / 3 * Real.log (halfY x)) < (⌊Real.log (2 / 3 * Real.log (halfY x))⌋₊
        : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : ((⌊Real.log (Real.log (halfY x))⌋₊ : ℕ) : ℝ)
        < ((⌊Real.log (2 / 3 * Real.log (halfY x))⌋₊ + 1 + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have := (Nat.cast_lt (α := ℝ)).1 h3
    omega

/-- **The mesoscopic range at slope `3/2`, without chaos**: the `93` windows below `97` at `2.2437`
and the rest at `1.909`: `≤ 93·2.2437 + 1.909(Λ - 96)`. -/
lemma tenMeso_le_crude {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    ∑ k ∈ Finset.Ico 4 (tenJ x), tenWindowBound x k
      ≤ 93 * (22437 / 10000) + 1909 / 1000 * (Real.log (Real.log x) - 96) := by
  obtain ⟨hLL, hly⟩ := halfY_loglog_le hx
  obtain ⟨-, -, hΛ, -, -, -⟩ := half_params hx
  obtain ⟨hJup, -⟩ := tenJ_bounds hx
  have hll0 : 0 ≤ Real.log (Real.log (halfY x)) := Real.log_nonneg (by linarith)
  have hsub : Finset.Ico 4 (tenJ x) ⊆ Finset.Ico 4 (max (tenJ x) 97) :=
    Finset.Ico_subset_Ico_right (le_max_left _ _)
  have h1 : ∑ k ∈ Finset.Ico 4 (tenJ x), tenWindowBound x k
      ≤ ∑ k ∈ Finset.Ico 4 (max (tenJ x) 97), tenWindowBound x k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => tenWindowBound_nonneg x k
  rw [← Finset.sum_Ico_consecutive _ (show 4 ≤ 97 by norm_num) (le_max_right (tenJ x) 97)] at h1
  have s1 : ∑ k ∈ Finset.Ico 4 97, tenWindowBound x k ≤ 93 * (22437 / 10000) := by
    have h := Finset.sum_le_sum (s := Finset.Ico 4 97) (fun k hk =>
      tenWindowBound_le_small hx (Finset.mem_Ico.1 hk).1)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h
    norm_num at h ⊢
    linarith
  have s2 : ∑ k ∈ Finset.Ico 97 (max (tenJ x) 97), tenWindowBound x k
      ≤ ((max (tenJ x) 97 - 97 : ℕ) : ℝ) * (1909 / 1000) := by
    have h := Finset.sum_le_sum (s := Finset.Ico 97 (max (tenJ x) 97)) (fun k hk =>
      tenWindowBound_le_hi hx (Finset.mem_Ico.1 hk).1)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h
    exact h
  have hcnt : ((max (tenJ x) 97 - 97 : ℕ) : ℝ) ≤ Real.log (Real.log x) - 96 := by
    have hm : (⌊Real.log (Real.log (halfY x))⌋₊ : ℝ) ≤ Real.log (Real.log x) :=
      le_trans (Nat.floor_le hll0) hLL
    rcases le_total (tenJ x) 97 with h | h
    · rw [max_eq_right h, Nat.sub_self]
      push_cast
      linarith
    · rw [max_eq_left h, Nat.cast_sub h]
      have : ((tenJ x : ℕ) : ℝ) ≤ (⌊Real.log (Real.log (halfY x))⌋₊ : ℝ) + 1 := by
        exact_mod_cast hJup
      push_cast
      linarith
  have := mul_le_mul_of_nonneg_right hcnt (by norm_num : (0 : ℝ) ≤ 1909 / 1000)
  linarith

/-- **The mesoscopic range at slope `3/2` past `Λ = 2400`**, for a bound `A` on the chaos
constant: the `93` windows below `97` at `2.2437`, the at most `2008` last ones at `1.909`, and the
chaos windows against the integral `(4/3)(Λ^{3/4} - 1999^{3/4})`. -/
lemma tenMeso_le_large {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ24 : 2400 ≤ Real.log (Real.log x)) {A : ℝ} (hA0 : 0 ≤ A) (hA : tenChaosConst x ≤ A) :
    ∑ k ∈ Finset.Ico 4 (tenJ x), tenWindowBound x k
      ≤ 93 * (22437 / 10000) + 2008 * (1909 / 1000) + 1909 / 1000 * A * (14143 / 10000)
        * (4 / 3 * (Real.log (Real.log x) ^ (3 / 4 : ℝ) - 2989 / 10)) := by
  obtain ⟨hLL, hly⟩ := halfY_loglog_le hx
  have hge := halfY_loglog_ge hx (by linarith)
  have hll0 : 0 ≤ Real.log (Real.log (halfY x)) := by linarith
  obtain ⟨m, hm⟩ : ∃ m, m = ⌊Real.log (Real.log (halfY x))⌋₊ := ⟨_, rfl⟩
  obtain ⟨hJup, hJlo⟩ := tenJ_bounds hx
  rw [← hm] at hJup hJlo
  have hm2105 : 2105 ≤ m := by
    rw [hm]
    exact Nat.le_floor (by push_cast; linarith)
  have hmR : (m : ℝ) ≤ Real.log (Real.log x) := by
    rw [hm]
    linarith [Nat.floor_le hll0]
  rw [← Finset.sum_Ico_consecutive _ (show 4 ≤ 97 by norm_num) (show 97 ≤ tenJ x by omega),
    ← Finset.sum_Ico_consecutive _ (show 97 ≤ m - 2007 by omega)
      (show m - 2007 ≤ tenJ x by omega)]
  -- the first `93` windows
  have s1 : ∑ k ∈ Finset.Ico 4 97, tenWindowBound x k ≤ 93 * (22437 / 10000) := by
    have h := Finset.sum_le_sum (s := Finset.Ico 4 97) (fun k hk =>
      tenWindowBound_le_small hx (Finset.mem_Ico.1 hk).1)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h
    norm_num at h ⊢
    linarith
  -- the last windows, at most `2008`
  have s3 : ∑ k ∈ Finset.Ico (m - 2007) (tenJ x), tenWindowBound x k ≤ 2008 * (1909 / 1000) := by
    have h := Finset.sum_le_sum (s := Finset.Ico (m - 2007) (tenJ x)) (fun k hk => by
      have hk' := Finset.mem_Ico.1 hk
      exact tenWindowBound_le_hi hx (k := k) (by omega))
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h
    have hc : ((tenJ x - (m - 2007) : ℕ) : ℝ) ≤ 2008 := by
      have : tenJ x - (m - 2007) ≤ 2008 := by omega
      exact_mod_cast this
    have := mul_le_mul_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 1909 / 1000)
    linarith
  -- the chaos windows
  have s2 : ∑ k ∈ Finset.Ico 97 (m - 2007), tenWindowBound x k
      ≤ 1909 / 1000 * A * (14143 / 10000)
        * (4 / 3 * (Real.log (Real.log x) ^ (3 / 4 : ℝ) - 2989 / 10)) := by
    have h := Finset.sum_le_sum (s := Finset.Ico 97 (m - 2007)) (fun k hk => by
      have hk' := Finset.mem_Ico.1 hk
      have := tenWindowBound_le_chaos hx (k := k) hk'.1 (by rw [← hm]; omega) hA
      rw [← hm] at this
      exact this)
    rw [← Finset.mul_sum] at h
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine le_trans (sum_chaos_rpow_le hm2105) ?_
    have h1 : ((m : ℝ) - 105) ^ (3 / 4 : ℝ) ≤ Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) - 105 := by
        have : (2105 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2105
        linarith
      exact Real.rpow_le_rpow hm0 (by linarith) (by norm_num)
    have h2 := rpow_1999_ge
    linarith
  linarith

/-! ### The theorem -/

/-- **The first moment of the weighted Rademacher sum at `q = ½`, with the constant `10`**: for
every `x ≥ exp(e^{110})`,

`E|∑_{n≤x} f(n)/√n| ≤ 10 (log log x)^{3/4}`.

`RMF.integral_norm_weightedRademacherSum_le_ten_assembly` with its pieces evaluated: `T ≤ 1`,
`E_err ≤ 1`, `C_R ≤ 0.33885`, `C_c^{1/2} ≤ 7.09√Λ + 0.2`, the far range `≤ 11.43`, and the
mesoscopic range at most `208.7 + 1.909(Λ - 96)` (below `Λ = 2400`) or, with the chaos constant
`4.68` below `Λ = 10⁴` and `4.55` above, `4042 + 1.909·A·1.4143·(4/3)(Λ^{3/4} - 298.9)`. -/
theorem integral_norm_weightedRademacherSum_le_ten {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
      ≤ 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
  have h := integral_norm_weightedRademacherSum_le_ten_assembly hX hx
  obtain ⟨-, -, hΛ, -, -, -⟩ := half_params hx
  have hT : halfTail x ^ (1 / 2 : ℝ) ≤ 1 := by
    have h1 := halfTail_le_one hx
    exact rpow_half_le_of_le zero_le_one (by linarith)
  have hE : smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ (1 / 2 : ℝ) ≤ 1 := by
    have h1 := halfErr_le_one hx
    exact rpow_half_le_of_le zero_le_one (by linarith)
  have hCR : smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32)
      ^ (1 / 2 : ℝ) ≤ 58212 / 100000 := by
    have h1 := halfCR_le hx
    exact rpow_half_le_of_le (by norm_num) (by linarith)
  have hCen := tenCen_rpow_le hx
  have hCen0 : 0 ≤ tenCen x ^ (1 / 2 : ℝ) := Real.rpow_nonneg (tenCen_nonneg hx) _
  have hfar := half_far_le
  have hfar0 : 0 ≤ (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hmeso0 : 0 ≤ ∑ k ∈ Finset.Ico 4 (tenJ x), tenWindowBound x k :=
    Finset.sum_nonneg fun k _ => tenWindowBound_nonneg x k
  obtain ⟨s, hs0, hs4, hs3, hs2⟩ := quarter_facts (Λ := Real.log (Real.log x)) (by linarith)
  rw [← hs3]
  set B := tenCen x ^ (1 / 2 : ℝ) + (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ (1 / 2 : ℝ)
    + ∑ k ∈ Finset.Ico 4 (tenJ x), tenWindowBound x k with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hprod : smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32)
      ^ (1 / 2 : ℝ) * B ≤ 58212 / 100000 * B := mul_le_mul_of_nonneg_right hCR hB0
  rw [← hs2] at hCen
  rcases le_or_gt (Real.log (Real.log x)) 2400 with hsmall | hlarge
  · have hmeso := tenMeso_le_crude hx
    rw [← hs4] at hmeso hsmall hΛ
    have hBle : B ≤ 709 / 100 * s ^ 2 + 2 / 10 + 1143 / 100 + (93 * (22437 / 10000)
        + 1909 / 1000 * (s ^ 4 - 96)) := by
      rw [hBdef]
      linarith
    have hslo : 32 / 10 ≤ s := by
      by_contra hc
      have : s ^ 4 < (32 / 10) ^ 4 := pow_lt_pow_left₀ (not_le.1 hc) hs0.le (by norm_num)
      linarith [show ((32 : ℝ) / 10) ^ 4 ≤ 110 by norm_num]
    have hshi : s ≤ 7 := by
      by_contra hc
      have : (7 : ℝ) ^ 4 < s ^ 4 := pow_lt_pow_left₀ (not_le.1 hc) (by norm_num) (by norm_num)
      linarith [show (2400 : ℝ) ≤ 7 ^ 4 by norm_num]
    have hpoly : 3 + 58212 / 100000 * (709 / 100 * s ^ 2 + 2 / 10 + 1143 / 100
        + (93 * (22437 / 10000) + 1909 / 1000 * (s ^ 4 - 96))) ≤ 10 * s ^ 3 := by
      have h1 : 0 ≤ (s - 32 / 10) * (7 - s) := mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ (s - 32 / 10) * (7 - s) * s ^ 2 := mul_nonneg h1 (sq_nonneg s)
      nlinarith [sq_nonneg s]
    have := mul_le_mul_of_nonneg_left hBle (by norm_num : (0 : ℝ) ≤ 58212 / 100000)
    linarith
  · rcases lt_or_ge (Real.log (Real.log x)) 10000 with hmid | hbig
    · have hmeso := tenMeso_le_large hx hlarge.le (A := 468 / 100) (by norm_num)
        (tenChaosConst_le (by linarith))
      rw [← hs3] at hmeso
      rw [← hs4] at hlarge hmid
      have hBle : B ≤ 709 / 100 * s ^ 2 + 2 / 10 + 1143 / 100 + (93 * (22437 / 10000)
          + 2008 * (1909 / 1000) + 1909 / 1000 * (468 / 100) * (14143 / 10000)
            * (4 / 3 * (s ^ 3 - 2989 / 10))) := by
        rw [hBdef]
        linarith
      have hs6 : 6 ≤ s := by
        by_contra hc
        have : s ^ 4 < 6 ^ 4 := pow_lt_pow_left₀ (not_le.1 hc) hs0.le (by norm_num)
        linarith [show (6 : ℝ) ^ 4 ≤ 2400 by norm_num]
      have hs10 : s ≤ 10 := by
        by_contra hc
        have : (10 : ℝ) ^ 4 < s ^ 4 := pow_lt_pow_left₀ (not_le.1 hc) (by norm_num) (by norm_num)
        linarith [show (10 : ℝ) ^ 4 = 10000 by norm_num]
      have hpoly : 3 + 58212 / 100000 * (709 / 100 * s ^ 2 + 2 / 10 + 1143 / 100
          + (93 * (22437 / 10000) + 2008 * (1909 / 1000) + 1909 / 1000 * (468 / 100)
            * (14143 / 10000) * (4 / 3 * (s ^ 3 - 2989 / 10)))) ≤ 10 * s ^ 3 := by
        have h1 : 0 ≤ s ^ 2 * (10 - s) := mul_nonneg (sq_nonneg s) (by linarith)
        nlinarith [sq_nonneg s]
      have := mul_le_mul_of_nonneg_left hBle (by norm_num : (0 : ℝ) ≤ 58212 / 100000)
      linarith
    · have hmeso := tenMeso_le_large hx hlarge.le (A := 455 / 100) (by norm_num)
        (tenChaosConst_le_B hbig)
      rw [← hs3] at hmeso
      rw [← hs4] at hbig
      have hBle : B ≤ 709 / 100 * s ^ 2 + 2 / 10 + 1143 / 100 + (93 * (22437 / 10000)
          + 2008 * (1909 / 1000) + 1909 / 1000 * (455 / 100) * (14143 / 10000)
            * (4 / 3 * (s ^ 3 - 2989 / 10))) := by
        rw [hBdef]
        linarith
      have hs10 : 10 ≤ s := by
        by_contra hc
        have : s ^ 4 < 10 ^ 4 := pow_lt_pow_left₀ (not_le.1 hc) hs0.le (by norm_num)
        linarith [show (10 : ℝ) ^ 4 = 10000 by norm_num]
      have hpoly : 3 + 58212 / 100000 * (709 / 100 * s ^ 2 + 2 / 10 + 1143 / 100
          + (93 * (22437 / 10000) + 2008 * (1909 / 1000) + 1909 / 1000 * (455 / 100)
            * (14143 / 10000) * (4 / 3 * (s ^ 3 - 2989 / 10)))) ≤ 10 * s ^ 3 := by
        have h1 : 0 ≤ s ^ 2 * (s - 10) := mul_nonneg (sq_nonneg s) (by linarith)
        nlinarith [sq_nonneg s]
      have := mul_le_mul_of_nonneg_left hBle (by norm_num : (0 : ℝ) ≤ 58212 / 100000)
      linarith

end RMF
