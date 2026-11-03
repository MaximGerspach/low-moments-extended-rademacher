/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.TenAssemblyExplicit

/-!
# The first moment at `q = ½` in the middle range: the assembly

The chain of `RMF/Weighted/TenAssemblyExplicit.lean` for `x ≥ exp(e⁷)`, with the parameters chosen
for small `Λ = log log x`: the smoothness level `y = ⌊e^{log x/Λ}⌋` (`U = Λ`), so that the smooth
tail is `≤ 1` already at `Λ = 7`; the sieve level `z = ⌊y e^{-8Λ}⌋`; the same tilt
`σ = (1/32)/log x`, `η = (log x)^{-3}` and `ε = (log x)^{-1/2}`; every window by Jensen at slope
`3/2`, no chaos window existing below `Λ ≈ 2100`.

`RMF.integral_norm_weightedRademacherSum_le_mid_assembly` bounds `E|S(x)|` by the five pieces;
`RMF/Weighted/MidNumeralExplicit.lean` evaluates them.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The parameters of the middle range -/

/-- `log x/log log x = log x/U`, `U = Λ`: the logarithm of the middle range's smoothness level. -/
noncomputable def midA (x : ℝ) : ℝ := Real.log x / Real.log (Real.log x)

/-- The middle range's smoothness level `y = ⌊e^{midA x}⌋`, i.e. `y ≈ x^{1/Λ}`. -/
noncomputable def midY (x : ℝ) : ℕ := ⌊Real.exp (midA x)⌋₊

/-- The middle range's sieve level `z = ⌊e^{midA x - 8Λ}⌋`. -/
noncomputable def midZ (x : ℝ) : ℕ := ⌊Real.exp (midA x - 8 * Real.log (Real.log x))⌋₊

/-- One more than the number of windows in the middle range: `J₀ = ⌊log((2/3)log y)⌋ + 1`. -/
noncomputable def midJ (x : ℝ) : ℕ := ⌊Real.log (2 / 3 * Real.log (midY x))⌋₊ + 1

/-- The middle range's central window constant: `(π/σ + 2(e^{S₂w²} - 1)/w)/log y`,
`w = e^{-J₀}`. -/
noncomputable def midCen (x : ℝ) : ℝ :=
  (Real.pi / halfSigma x + 2 * (Real.exp (2 * (1 - 1 / 2)
      * (Real.log ((midY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((midY x : ℝ) + 1) + 34)
      * Real.exp (-((midJ x : ℕ) : ℝ)) ^ 2) - 1) / Real.exp (-((midJ x : ℕ) : ℝ)))
    / Real.log (midY x)

/-- The middle range's smooth tail. -/
noncomputable def midTail (x : ℝ) : ℝ :=
  ∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial (midY x))
    | m ∈ Nat.smoothNumbers (midY x + 1) ∧ Squarefree m}, (m : ℝ)⁻¹

/-- `e⁷ ≥ 1096`. -/
lemma exp_seven_ge_1096 : (1096 : ℝ) ≤ Real.exp 7 := by
  interval_decide (trust := kernel)

/-- `e^Λ ≥ Λ(20.5Λ + 2)` for `Λ ≥ 7`: `e^Λ ≥ 1096(1 + u + u²/2)`, `u = Λ - 7`. -/
lemma mul_le_exp_of_seven_le {Λ : ℝ} (hΛ : 7 ≤ Λ) : Λ * (41 / 2 * Λ + 2) ≤ Real.exp Λ := by
  have h7 := exp_seven_ge_1096
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Λ - 7 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg hu0
  have he : Real.exp Λ = Real.exp 7 * Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    linarith
  rw [he]
  have h1 : 1096 * (1 + u + u ^ 2 / 2) ≤ Real.exp 7 * Real.exp u :=
    mul_le_mul h7 hq (by positivity) (by positivity)
  have hΛu : Λ = u + 7 := by linarith
  rw [hΛu]
  nlinarith [sq_nonneg u]

/-- The basic facts of the middle range's parameters at `x ≥ exp(e⁷)`. -/
lemma mid_params {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    0 < x ∧ Real.exp 7 ≤ Real.log x ∧ 7 ≤ Real.log (Real.log x)
      ∧ Real.exp (Real.log (Real.log x)) = Real.log x
      ∧ 41 / 2 * Real.log (Real.log x) + 2 ≤ midA x ∧ midA x ≤ Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : Real.exp 7 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛ : 7 ≤ Real.log (Real.log x) := by
    rw [Real.le_log_iff_exp_le hLpos]
    exact hL
  have hexpΛ : Real.exp (Real.log (Real.log x)) = Real.log x := Real.exp_log hLpos
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  refine ⟨hx0, hL, hΛ, hexpΛ, ?_, ?_⟩
  · have h := mul_le_exp_of_seven_le hΛ
    rw [hexpΛ] at h
    rw [midA, le_div_iff₀ hΛpos]
    linarith
  · rw [midA, div_le_iff₀ hΛpos]
    nlinarith

/-- `midA x·Λ = log x`. -/
lemma midA_mul {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    midA x * Real.log (Real.log x) = Real.log x := by
  obtain ⟨-, -, hΛ, -, -, -⟩ := mid_params hx
  rw [midA]
  field_simp

/-- **The middle range's smoothness level**: `e^a/2 ≤ y ≤ e^a`, `a = midA x`, so
`a - log 2 ≤ log y ≤ a`; `y ≤ x` and `y ≥ e^{99}`. -/
lemma midY_facts {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    2 ≤ midY x ∧ (midY x : ℝ) ≤ x ∧ Real.log (midY x) ≤ midA x
      ∧ midA x - Real.log 2 ≤ Real.log (midY x) ∧ Real.exp 99 ≤ (midY x : ℝ)
      ∧ Real.exp (midA x) / 2 ≤ (midY x : ℝ) := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, ha, haL⟩ := mid_params hx
  have ha100 : 100 ≤ midA x := by linarith
  have hfl : Real.exp (midA x) < (midY x : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfl' : (midY x : ℝ) ≤ Real.exp (midA x) := Nat.floor_le (Real.exp_pos _).le
  have hea : 101 ≤ Real.exp (midA x) := by linarith [Real.add_one_le_exp (midA x)]
  have hyh : Real.exp (midA x) / 2 ≤ (midY x : ℝ) := by linarith
  have hypos : 0 < (midY x : ℝ) := lt_of_lt_of_le (by positivity) hyh
  refine ⟨?_, ?_, ?_, ?_, ?_, hyh⟩
  · have h1 : (2 : ℝ) ≤ (midY x : ℝ) := by linarith
    exact_mod_cast h1
  · calc (midY x : ℝ) ≤ Real.exp (midA x) := hfl'
      _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.2 haL
      _ = x := Real.exp_log hx0
  · calc Real.log (midY x) ≤ Real.log (Real.exp (midA x)) := Real.log_le_log hypos hfl'
      _ = midA x := Real.log_exp _
  · calc midA x - Real.log 2 = Real.log (Real.exp (midA x) / 2) := by
          rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
      _ ≤ Real.log (midY x) := Real.log_le_log (by positivity) hyh
  · have h1 : Real.exp 99 * 2 ≤ Real.exp (midA x) := by
      have h2 : Real.exp 99 * Real.exp 1 ≤ Real.exp (midA x) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 (by linarith)
      have h3 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      nlinarith [Real.exp_pos 99]
    linarith

/-- **The middle range's sieve level**: `2 ≤ z ≤ y` and `log z ≥ a - 8Λ - log 2`. -/
lemma midZ_facts {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    2 ≤ midZ x ∧ midZ x ≤ midY x
      ∧ midA x - 8 * Real.log (Real.log x) - Real.log 2 ≤ Real.log (midZ x) := by
  obtain ⟨-, -, hΛ, -, ha, -⟩ := mid_params hx
  obtain ⟨b, hb⟩ : ∃ b, b = midA x - 8 * Real.log (Real.log x) := ⟨_, rfl⟩
  have hb4 : 4 ≤ b := by rw [hb]; linarith
  have heb : 5 ≤ Real.exp b := by linarith [Real.add_one_le_exp b]
  have hfl : Real.exp b < (midZ x : ℝ) + 1 := by rw [midZ, ← hb]; exact Nat.lt_floor_add_one _
  have hzh : Real.exp b / 2 ≤ (midZ x : ℝ) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (2 : ℝ) ≤ (midZ x : ℝ) := by linarith
    exact_mod_cast h1
  · exact Nat.floor_le_floor (Real.exp_le_exp.2 (by linarith))
  · rw [← hb]
    calc b - Real.log 2 = Real.log (Real.exp b / 2) := by
          rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
      _ ≤ Real.log (midZ x) := Real.log_le_log (by positivity) hzh

/-- **`⌊x⌋ ≤ y#`** at the middle range's smoothness level. -/
lemma floor_le_primorial_midY {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    ⌊x⌋₊ ≤ primorial (midY x) := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, ha, -⟩ := mid_params hx
  obtain ⟨-, -, -, -, -, hyh⟩ := midY_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx1 : 1 ≤ x := by
    have : Real.exp 0 ≤ x := le_trans (Real.exp_le_exp.2 (Real.exp_pos _).le) hx
    rwa [Real.exp_zero] at this
  refine floor_le_primorial_of_log_le hx1 ?_
  -- `e^a ≥ e^{Λ+100} = e^{100} log x`, and `≥ 2^{101}`
  have h2 : Real.exp (Real.log (Real.log x) + 100) = Real.log x * Real.exp 100 := by
    rw [Real.exp_add, hexpΛ]
  have h3 : (4 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have h4 : (2 : ℝ) ^ 101 ≤ Real.exp 100 := by
    rw [show (100 : ℝ) = ((100 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
    have := Real.exp_one_gt_d9
    have h5 : (2.7 : ℝ) ^ 100 ≤ Real.exp 1 ^ 100 := pow_le_pow_left₀ (by norm_num) (by linarith) 100
    linarith [show (2 : ℝ) ^ 101 ≤ 2.7 ^ 100 by norm_num]
  have h1 : Real.exp (Real.log (Real.log x) + 100) ≤ Real.exp (midA x) :=
    Real.exp_le_exp.2 (by linarith)
  have hY : (2 : ℝ) ^ 100 ≤ (midY x : ℝ) := by
    have : Real.exp 100 ≤ Real.exp (midA x) := Real.exp_le_exp.2 (by linarith)
    nlinarith
  have hθ := half_le_theta_lower hY
  have hLY : Real.log x ≤ (midY x : ℝ) / 2 := by
    have : Real.log x * 4 ≤ Real.exp (midA x) := by
      have := mul_le_mul_of_nonneg_left h3 hLpos.le
      nlinarith
    linarith
  linarith

/-- `σ log y ≤ 1/32` and `σ log(x/y) ≤ 1/32` for the tilt `σ = (1/32)/log x`. -/
lemma halfSigma_mul_log_div_le {x : ℝ} (hx0 : 0 < x) (hL : 0 < Real.log x) {y : ℕ}
    (hy : 0 < (y : ℝ)) (hly : 0 ≤ Real.log y) :
    halfSigma x * Real.log (x / y) ≤ 1 / 32 := by
  rw [Real.log_div hx0.ne' hy.ne', halfSigma, div_mul_eq_mul_div, div_le_iff₀ hL]
  nlinarith

/-! ### The assembly of the middle range -/

set_option maxHeartbeats 1000000 in
-- the reduction, three ranges and five bounds in one proof
/-- **`E|S(x)|` from its five pieces in the middle range**.  For `x ≥ exp(e⁷)`, with
`y = midY x ≈ x^{1/Λ}`, `z = midZ x`, `σ = (1/32)/log x`, `η = (log x)^{-3}`, `ε = (log x)^{-1/2}`:

`E|S(x)| ≤ 1 + T^{1/2} + C_R^{1/2}·(C_c^{1/2} + (2·1.195·e⁴)^{1/2} + ∑_{4≤k<J₀} G_k) + E_err^{1/2}`,

`T = RMF.midTail`, `C_R = RMF.smallQReductionConst`, `C_c = RMF.midCen`,
`G_k² = RMF.thetaWindowConst (3/2) k y` (every window by Jensen), `J₀ = RMF.midJ`,
`E_err = RMF.smallQReductionErr`. -/
theorem integral_norm_weightedRademacherSum_le_mid_assembly {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
      ≤ 1 + midTail x ^ (1 / 2 : ℝ)
        + smallQReductionConst (midY x) (midZ x) (halfEta x) (halfEps x) (1 / 32) ^ (1 / 2 : ℝ)
          * (midCen x ^ (1 / 2 : ℝ)
            + (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ (1 / 2 : ℝ)
            + ∑ k ∈ Finset.Ico 4 (midJ x), thetaWindowConst (3 / 2) k (midY x) ^ (1 / 2 : ℝ))
        + smallQReductionErr x (midZ x) (halfEta x) (halfEps x) ^ (1 / 2 : ℝ) := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  obtain ⟨hx0, hL, hΛ, hexpΛ, -, haL⟩ := mid_params hx
  obtain ⟨hy2, hyx, hlogy_le, hlogy_ge, hy99, -⟩ := midY_facts hx
  obtain ⟨hz2, hzy, -⟩ := midZ_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  set y := midY x with hydef
  set σ := halfSigma x with hσdef
  have hσ : 0 < σ := by rw [hσdef, halfSigma]; positivity
  have hy2R : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogy_big : 99 ≤ Real.log y := by
    have h := Real.log_le_log (Real.exp_pos 99) hy99
    rwa [Real.log_exp] at h
  -- the reduction's hypotheses
  have hσlog : σ * Real.log (x / y) ≤ 1 / 32 :=
    halfSigma_mul_log_div_le hx0 hLpos (by linarith) hlogy.le
  have hη : 0 < halfEta x := by rw [halfEta]; positivity
  have hyη : 1 + halfEta x < y := by
    have hηle : halfEta x ≤ 1 := by
      rw [halfEta]
      have h1 : (1 : ℝ) ≤ Real.log x ^ 3 := by
        have : (1 : ℝ) ≤ Real.log x := le_trans (by linarith [Real.add_one_le_exp (7 : ℝ)]) hL
        exact one_le_pow₀ this
      exact inv_le_one_of_one_le₀ h1
    have : (100 : ℝ) ≤ Real.exp 99 := by linarith [Real.add_one_le_exp (99 : ℝ)]
    linarith
  have hε : 0 < halfEps x := by rw [halfEps]; positivity
  have hred := integral_rpow_weightedRademacherSum_le_reduction_explicit hX hz2 hzy
    (σ := σ) (x := x) (η := halfEta x) (ε := halfEps x) (c := 1 / 32) (q := 1 / 2)
    hyx (floor_le_primorial_midY hx) hσ hσlog hη hyη hε (by norm_num) (by norm_num)
  have hone : ∀ ω : Ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * (1 / 2 : ℝ)) = ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x
        ω‖ := fun ω => by norm_num
  simp only [hone] at hred
  -- `E‖F_{y+1}(½)‖ ≤ 1`: the sharp moment bound at `q = ½`
  have hPF : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
      (1 / 2) ω‖ ^ (2 * (1 / 2 : ℝ)) ∂μ) ≤ 1 := by
    refine le_trans (hRa.integral_norm_randomEulerProduct_half_rpow_le_log_sharp (q := 1 / 2)
      (by norm_num) le_rfl hy2) (le_of_eq ?_)
    norm_num
  -- `Z` in three ranges
  have hJ4 : 4 ≤ midJ x := by
    rw [midJ, ← hydef]
    have h1 : (3 : ℝ) ≤ Real.log (2 / 3 * Real.log y) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have h2 : Real.exp 3 ≤ 21 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
        have := Real.exp_one_lt_d9
        have h4 : Real.exp 1 ^ 3 ≤ (2.72 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 3
        linarith [show (2.72 : ℝ) ^ 3 ≤ 21 by norm_num]
      linarith
    have : 3 ≤ ⌊Real.log (2 / 3 * Real.log y)⌋₊ := Nat.le_floor (by exact_mod_cast h1)
    omega
  have hJ4R : (4 : ℝ) ≤ ((midJ x : ℕ) : ℝ) := by exact_mod_cast hJ4
  have hwv : Real.exp (-((midJ x : ℕ) : ℝ)) ≤ Real.exp (-((4 : ℕ) : ℝ)) :=
    Real.exp_le_exp.2 (by push_cast; linarith)
  -- the central window
  have hb1 := integral_rpow_centralRange_le_sharp hX (σ := σ) (q := 1 / 2)
    (w := Real.exp (-((midJ x : ℕ) : ℝ))) hy2 hσ (Real.exp_pos _) (by norm_num) le_rfl
  have hPFc : Real.exp (1 / 2 * (1 - 2 * (1 / 2)) * (9.0028 / Real.log y
      + 2 * σ * (Real.log y + Real.log 4 + 4) - 3 / 20))
      * Real.log y ^ (1 / 2 * (2 * (1 / 2) - 1) : ℝ) = 1 := by norm_num
  rw [hPFc, mul_one] at hb1
  -- the windows, every one by Jensen
  have hwin : ∀ k ∈ Finset.Ico 4 (midJ x),
      (2 / Real.log y) ^ (1 / 2 : ℝ) * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
        (Real.exp (-(k : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ
        ≤ thetaWindowConst (3 / 2) k y ^ (1 / 2 : ℝ) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hky := tenJ_window hlogy (by omega : k ≠ 0) (by rw [midJ, ← hydef] at hk; exact hk.2)
    exact window_theta_le_jensen hX (θ := 3 / 2) (by norm_num) hσ (by omega) hky
  have hb2 := mesoRange_half_le_sum hX hy2 hσ (k₀ := 4) (J := midJ x) hJ4 hwin
  -- the far range
  have hb3 := integral_rpow_eulerProductLine_tail_le_explicit hX (q := 1 / 2) (by norm_num)
    (by norm_num) hy99 hσ (T := Real.exp (-((4 : ℕ) : ℝ))) (Real.exp_pos _)
  have hZ := integral_rpow_eulerLineDiv_le_of_three_ranges hX (σ := σ) (q := 1 / 2)
    (w := Real.exp (-((midJ x : ℕ) : ℝ))) (v := Real.exp (-((4 : ℕ) : ℝ))) hy2 hσ (by norm_num)
    (by norm_num) hwv hb1 hb2 hb3
  have hCR0 : 0 ≤ smallQReductionConst y (midZ x) (halfEta x) (halfEps x) (1 / 32) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (smallQReductionConst_pos hz2 hzy hη hε).le _
  have hmul := mul_le_mul_of_nonneg_left hZ hCR0
  have hcen : ((Real.pi / σ + 2 * (Real.exp (2 * (1 - 1 / 2)
      * (Real.log ((y : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((y : ℝ) + 1) + 34)
      * Real.exp (-((midJ x : ℕ) : ℝ)) ^ 2) - 1) / Real.exp (-((midJ x : ℕ) : ℝ)))
      / Real.log y) = midCen x := by
    rw [midCen, ← hydef, ← hσdef]
  rw [hcen] at hmul
  have htail : (∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial y)
      | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m}, (m : ℝ)⁻¹) = midTail x := by
    rw [midTail, ← hydef]
  rw [htail] at hred
  linarith

end RMF
