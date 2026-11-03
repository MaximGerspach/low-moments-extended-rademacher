/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ThetaWindowExplicit
import RMF.Weighted.HalfAssemblyExplicit

/-!
# The first moment at `q = ½`: the assembly at slope `3/2`

The chain at `q = ½` with the parameters of `RMF/Weighted/HalfAssemblyExplicit.lean` (`U = Λ/2`,
`c = 1/32`, `y`, `z`, `η`, `ε`, room `2000`, `δ = 1/50`, `β = 11/20`, `E₀ = 1/(16Λ)`), where

* the windows are split at slope `3/2` (`RMF/Weighted/ThetaWindowExplicit.lean`), so they run up to
  `J₀ = ⌊log((2/3)log y)⌋ + 1` (`RMF.tenJ`) and the central window out to `e^{-J₀} ≤ 3/(2 log y)`;
* past `Λ = 10⁴` the chaos windows take level `18`, `λ = 98/5`, `T = 30`, `κ = 8`
  (`RMF.halfChaosConstB`), below it level `20` (`RMF.halfChaosConst`); `RMF.tenChaosConst` is the
  one or the other.

`RMF.integral_norm_weightedRademacherSum_le_ten_assembly` bounds `E|S(x)|` by the five pieces;
`RMF/Weighted/TenNumeralExplicit.lean` evaluates them.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The parameters at slope `3/2` -/

/-- One more than the number of windows at slope `3/2`: `J₀ = ⌊log((2/3)log y)⌋ + 1`, so every
window `k < J₀` has `(3/2)e^k ≤ log y`. -/
noncomputable def tenJ (x : ℝ) : ℕ := ⌊Real.log (2 / 3 * Real.log (halfY x))⌋₊ + 1

/-- The chaos constant of a window at `q = ½` for `Λ ≥ 10⁴`, at the tilt `E₀`: level `18`,
`λ = 98/5`, `T = 30`, `κ = 8`, `δ = 1/50`, `β = 11/20`. -/
noncomputable def halfChaosConstB (E₀ : ℝ) : ℝ :=
  shiftMomentConst 1 (radAveragedConst E₀ (11 / 20) 30 8)
    (radBlockBadConst E₀ (11 / 20) * Real.exp 8) 18 (radAveragedShift E₀ (11 / 20) 30 8)
    (98 / 5) (1 / 50) (1 / 2)

/-- The chaos constant of a window at `x`, at the tilt `E₀ = 1/(16Λ)`: `RMF.halfChaosConstB` for
`Λ ≥ 10⁴`, `RMF.halfChaosConst` below. -/
noncomputable def tenChaosConst (x : ℝ) : ℝ :=
  if 10000 ≤ Real.log (Real.log x) then halfChaosConstB (1 / (16 * Real.log (Real.log x)))
  else halfChaosConst (1 / (16 * Real.log (Real.log x)))

/-- The bound on the `k`-th window at slope `3/2`: `G_k` times the chaos factor on a chaos window,
`G_k` on the others. -/
noncomputable def tenWindowBound (x : ℝ) (k : ℕ) : ℝ :=
  if 97 ≤ k ∧ k + 8 + 2000 ≤ ⌊Real.log (Real.log (halfY x))⌋₊ then
    thetaWindowConst (3 / 2) k (halfY x) ^ (1 / 2 : ℝ)
      * (tenChaosConst x
        * (1 + (1 - 1 / 2) * Real.sqrt (harperBlockCount (k + 8) (halfY x) : ℝ))
          ^ (-(1 / 2 : ℝ)))
  else thetaWindowConst (3 / 2) k (halfY x) ^ (1 / 2 : ℝ)

/-- The central window's constant at slope `3/2`: `(π/σ + 2(e^{S₂w²} - 1)/w)/log y`,
`w = e^{-J₀}`. -/
noncomputable def tenCen (x : ℝ) : ℝ :=
  (Real.pi / halfSigma x + 2 * (Real.exp (2 * (1 - 1 / 2)
      * (Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34)
      * Real.exp (-((tenJ x : ℕ) : ℝ)) ^ 2) - 1) / Real.exp (-((tenJ x : ℕ) : ℝ)))
    / Real.log (halfY x)

lemma half_level_le_B {Λ : ℝ} (hΛ : 10000 ≤ Λ) : radBlockBadLevel (1 / (16 * Λ)) ≤ 18 := by
  have hE₀le : 1 / (16 * Λ) ≤ (1 / 400) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hsqrt : Real.sqrt (1 / (16 * Λ)) ≤ 1 / 400 := by
    calc Real.sqrt (1 / (16 * Λ)) ≤ Real.sqrt ((1 / 400) ^ 2) := Real.sqrt_le_sqrt hE₀le
      _ = 1 / 400 := Real.sqrt_sq (by norm_num)
  rw [radBlockBadLevel, harperSharpDeficit]
  linarith

/-- The windows below `J₀` satisfy `(3/2)e^k ≤ log y`. -/
lemma tenJ_window {y : ℕ} (hy : 0 < Real.log y) {k : ℕ} (hk0 : k ≠ 0)
    (hk : k < ⌊Real.log (2 / 3 * Real.log y)⌋₊ + 1) : 3 / 2 * Real.exp k ≤ Real.log y := by
  have hk' : k ≤ ⌊Real.log (2 / 3 * Real.log y)⌋₊ := by omega
  have hkR : (k : ℝ) ≤ Real.log (2 / 3 * Real.log y) := (Nat.le_floor_iff' hk0).1 hk'
  have h1 : Real.exp k ≤ 2 / 3 * Real.log y := by
    calc Real.exp k ≤ Real.exp (Real.log (2 / 3 * Real.log y)) := Real.exp_le_exp.2 hkR
      _ = 2 / 3 * Real.log y := Real.exp_log (by positivity)
  linarith

set_option maxHeartbeats 1000000 in
-- the chaos window's thirty hypotheses, discharged one by one, in two regimes
/-- **The `k`-th window's bound at slope `3/2`**: a chaos window by the weighted chaos (level `20`
below `Λ = 10⁴`, level `18` above), every other window by Jensen. -/
lemma tenWindow_le {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x : ℝ}
    (hx : Real.exp (Real.exp 110) ≤ x) {k : ℕ} (hk : k ∈ Finset.Ico 4 (tenJ x)) :
    (2 / Real.log (halfY x)) ^ (1 / 2 : ℝ) * ∫ ω, (∫ t in Set.Icc
        (Real.exp (-(k : ℝ)) / Real.exp 1) (Real.exp (-(k : ℝ))), (halfSigma x ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
          (shiftLine (halfSigma x) t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ ≤ tenWindowBound x k := by
  obtain ⟨-, hL, hΛ, -, -, haL⟩ := half_params hx
  obtain ⟨hy2, -, hlogy_le, -, -, -⟩ := halfY_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hσ : 0 < halfSigma x := by rw [halfSigma]; positivity
  have hy2R : (2 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast hy2
  have hlogy : 0 < Real.log (halfY x) := Real.log_pos (by linarith)
  have hLLy : Real.log (Real.log (halfY x)) ≤ Real.log (Real.log x) :=
    Real.log_le_log hlogy (le_trans hlogy_le haL)
  rw [Finset.mem_Ico] at hk
  rw [tenWindowBound]
  by_cases hc : 97 ≤ k ∧ k + 8 + 2000 ≤ ⌊Real.log (Real.log (halfY x : ℝ))⌋₊
  · rw [if_pos hc, tenChaosConst]
    have hLLy2 : ((k + 8 + 2000 : ℕ) : ℝ) ≤ Real.log (Real.log (halfY x)) :=
      (Nat.le_floor_iff' (by omega)).1 hc.2
    have hkR : (97 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hc.1
    have hΛbig : 2105 ≤ Real.log (Real.log x) := by push_cast at hLLy2; linarith
    have hNn : 2000 ≤ harperBlockCount (k + 8) (halfY x : ℝ) := by
      rw [harperBlockCount]
      omega
    split_ifs with hB
    · rw [halfChaosConstB]
      exact window_theta_le_chaos (1 / (16 * Real.log (Real.log x))) (11 / 20) (by positivity)
        (half_tilt_le hΛ) (by norm_num) (by norm_num) (Tr := 30) (κ := 8) (Amax := 20)
        (δ := 1 / 50) (N := 2000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        half_room half_mono hX (θ := 3 / 2) (by norm_num) (by norm_num) (k := k) (y := halfY x)
        (σ := halfSigma x) (A := 18) (lam := 98 / 5) hσ hc.1 (by omega)
        (halfSigma_mul_log_le hx) hNn (half_level_le_B hB) (by norm_num) (by norm_num)
    · rw [halfChaosConst]
      exact window_theta_le_chaos (1 / (16 * Real.log (Real.log x))) (11 / 20) (by positivity)
        (half_tilt_le hΛ) (by norm_num) (by norm_num) (Tr := 35) (κ := 10) (Amax := 20)
        (δ := 1 / 50) (N := 2000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        half_room half_mono hX (θ := 3 / 2) (by norm_num) (by norm_num) (k := k) (y := halfY x)
        (σ := halfSigma x) (A := 20) (lam := 104 / 5) hσ hc.1 (by omega)
        (halfSigma_mul_log_le hx) hNn (half_level_le hΛbig) le_rfl (by norm_num)
  · rw [if_neg hc]
    have hky := tenJ_window hlogy (by omega : k ≠ 0) (by rw [tenJ] at hk; exact hk.2)
    exact window_theta_le_jensen hX (θ := 3 / 2) (by norm_num) hσ (by omega) hky

/-! ### The assembly at slope `3/2` -/

set_option maxHeartbeats 1000000 in
-- the reduction, three ranges and five bounds in one proof
/-- **`E|S(x)|` from its five pieces, windows at slope `3/2`**.  For `x ≥ exp(e^{110})`:

`E|S(x)| ≤ 1 + T^{1/2} + C_R^{1/2}·(C_c^{1/2} + (2·1.195·e⁴)^{1/2} + ∑_{4≤k<J₀} b_k) + E_err^{1/2}`,

`T = RMF.halfTail`, `C_R = RMF.smallQReductionConst`, `C_c = RMF.tenCen`,
`b_k = RMF.tenWindowBound`, `J₀ = RMF.tenJ`, `E_err = RMF.smallQReductionErr`, with the windows
split at `⌈exp((3/2)e^k)⌉` and the central window out to `e^{-J₀} ≤ 3/(2 log y)`. -/
theorem integral_norm_weightedRademacherSum_le_ten_assembly {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
      ≤ 1 + halfTail x ^ (1 / 2 : ℝ)
        + smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32) ^ (1 / 2 : ℝ)
          * (tenCen x ^ (1 / 2 : ℝ)
            + (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ (1 / 2 : ℝ)
            + ∑ k ∈ Finset.Ico 4 (tenJ x), tenWindowBound x k)
        + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ (1 / 2 : ℝ) := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  obtain ⟨hx0, hL, hΛ, hexpΛ, -, haL⟩ := half_params hx
  obtain ⟨hy2, hyx, hlogy_le, hlogy_ge, hy99, -⟩ := halfY_facts hx
  obtain ⟨hz2, hzy, -⟩ := halfZ_facts hx
  have ha := halfA_ge hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  set y := halfY x with hydef
  set σ := halfSigma x with hσdef
  have hσ : 0 < σ := by rw [hσdef, halfSigma]; positivity
  have hy2R : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hlogy_big : 99 ≤ Real.log y := by linarith
  -- the reduction's hypotheses
  have hσlog : σ * Real.log (x / y) ≤ 1 / 32 := by
    rw [Real.log_div hx0.ne' (by positivity), hσdef, halfSigma]
    rw [div_mul_eq_mul_div, div_le_iff₀ hLpos]
    have : 0 ≤ Real.log y := hlogy.le
    nlinarith
  have hη : 0 < halfEta x := by rw [halfEta]; positivity
  have hyη : 1 + halfEta x < y := by
    have hηle : halfEta x ≤ 1 := by
      rw [halfEta]
      have h1 : (1 : ℝ) ≤ Real.log x ^ 3 := by
        have : (1 : ℝ) ≤ Real.log x := le_trans (by linarith [Real.add_one_le_exp (110 : ℝ)]) hL
        exact one_le_pow₀ this
      exact inv_le_one_of_one_le₀ h1
    have : (100 : ℝ) ≤ Real.exp 99 := by linarith [Real.add_one_le_exp (99 : ℝ)]
    linarith
  have hε : 0 < halfEps x := by rw [halfEps]; positivity
  have hred := integral_rpow_weightedRademacherSum_le_reduction_explicit hX hz2 hzy
    (σ := σ) (x := x) (η := halfEta x) (ε := halfEps x) (c := 1 / 32) (q := 1 / 2)
    hyx (floor_le_primorial_halfY hx) hσ hσlog hη hyη hε (by norm_num) (by norm_num)
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
  have hJ4 : 4 ≤ tenJ x := by
    rw [tenJ, ← hydef]
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
  have hJ4R : (4 : ℝ) ≤ ((tenJ x : ℕ) : ℝ) := by exact_mod_cast hJ4
  have hwv : Real.exp (-((tenJ x : ℕ) : ℝ)) ≤ Real.exp (-((4 : ℕ) : ℝ)) :=
    Real.exp_le_exp.2 (by push_cast; linarith)
  -- the central window
  have hb1 := integral_rpow_centralRange_le_sharp hX (σ := σ) (q := 1 / 2)
    (w := Real.exp (-((tenJ x : ℕ) : ℝ))) hy2 hσ (Real.exp_pos _) (by norm_num) le_rfl
  have hPFc : Real.exp (1 / 2 * (1 - 2 * (1 / 2)) * (9.0028 / Real.log y
      + 2 * σ * (Real.log y + Real.log 4 + 4) - 3 / 20))
      * Real.log y ^ (1 / 2 * (2 * (1 / 2) - 1) : ℝ) = 1 := by norm_num
  rw [hPFc, mul_one] at hb1
  -- the windows
  have hwin : ∀ k ∈ Finset.Ico 4 (tenJ x),
      (2 / Real.log y) ^ (1 / 2 : ℝ) * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
        (Real.exp (-(k : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ ≤ tenWindowBound x k :=
    fun k hk => tenWindow_le hX hx hk
  have hb2 := mesoRange_half_le_sum hX hy2 hσ (k₀ := 4) (J := tenJ x) hJ4 hwin
  -- the far range
  have hb3 := integral_rpow_eulerProductLine_tail_le_explicit hX (q := 1 / 2) (by norm_num)
    (by norm_num) hy99 hσ (T := Real.exp (-((4 : ℕ) : ℝ))) (Real.exp_pos _)
  have hZ := integral_rpow_eulerLineDiv_le_of_three_ranges hX (σ := σ) (q := 1 / 2)
    (w := Real.exp (-((tenJ x : ℕ) : ℝ))) (v := Real.exp (-((4 : ℕ) : ℝ))) hy2 hσ (by norm_num)
    (by norm_num) hwv hb1 hb2 hb3
  have hCR0 : 0 ≤ smallQReductionConst y (halfZ x) (halfEta x) (halfEps x) (1 / 32) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (smallQReductionConst_pos hz2 hzy hη hε).le _
  have hmul := mul_le_mul_of_nonneg_left hZ hCR0
  have hcen : ((Real.pi / σ + 2 * (Real.exp (2 * (1 - 1 / 2)
      * (Real.log ((y : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((y : ℝ) + 1) + 34)
      * Real.exp (-((tenJ x : ℕ) : ℝ)) ^ 2) - 1) / Real.exp (-((tenJ x : ℕ) : ℝ)))
      / Real.log y) = tenCen x := by
    rw [tenCen, ← hydef, ← hσdef]
  rw [hcen] at hmul
  have htail : (∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial y)
      | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m}, (m : ℝ)⁻¹) = halfTail x := by
    rw [halfTail, ← hydef]
  rw [htail] at hred
  linarith

end RMF
