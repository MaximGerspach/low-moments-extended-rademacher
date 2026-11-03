/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.FracWindowsExplicit.Pieces
import RMF.Weighted.FracWindowsExplicit.Numerals

/-!
# The remainder's windows, III: `E[Z_R^{1/2}] ≤ 55(log log x)^{-1/4}`

The headline (`RMF.integral_rpow_fracLine_le_explicit`): for `Λ = log log x ≥ 160000` and
`0 < c ≤ 1`, with the reduction's `y = RMF.fracY x` and `σ = c/log x`,

`E[((log y)⁻¹∫_ℝ‖F_{y+1}(½+σ+it)‖²|φ̂(½+σ+it)|²dt)^{1/2}] ≤ 55Λ^{-1/4}`.

`RMF.integral_rpow_fracLine_le_of_windows` assembles the pieces at cut points
`e^{-K} ≤ e^{-4} ≤ e^{J-4}`, with the windows' room and depth as hypotheses; the headline takes
`K = ⌈log Λ⌉`, `J = K + 26`, the tilt `E₀ = 1/(16Λ)` and `χ = 1.415Λ^{-1/4}`, and discharges them.
The constant is `√2(0.046 + 0.404 + 26.6·1.415 + 0.043) ≤ 53.93`: the fold, the inner piece,
the mesoscopic windows, the far windows and the tail.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A nonnegative factor leaves a power of the integrand. -/
lemma integral_rpow_const_mul {μ : Measure Ω} {a : ℝ} (ha : 0 ≤ a) {g : Ω → ℝ}
    (hg : ∀ ω, 0 ≤ g ω) (r : ℝ) :
    ∫ ω, (a * g ω) ^ r ∂μ = a ^ r * ∫ ω, g ω ^ r ∂μ := by
  rw [← integral_const_mul]
  congr 1
  funext ω
  exact Real.mul_rpow ha (hg ω)

/-! ### The assembly -/

set_option maxHeartbeats 800000 in
-- the four pieces and the two window families in one proof
/-- **`E[Z_R^{1/2}]` from its windows**: for `y ≥ e^{99}`, `log y ≥ 22000`, `σ > 0`,
`σ log y ≤ E₀ ≤ 1/160000` with `radBlockBadLevel E₀ ≤ 65`, cut points `e^{-K} ≤ e^{-4} ≤ e^{J-4}`
(`K ≥ 4`, `J ≥ 13`), and every offset `D ≤ 105 + K + J` below `⌊log log y⌋` with room
(`n = harperBlockCount D y`, levels up to `65 + J`) and `(1 + ½√n)^{-1/2} ≤ χ`:

`E[Z_R^{1/2}] ≤ √2((1.195·0.7151e^{-K})^{1/2} + 0.598(Kσ + 0.03)·2.2437·7.08χ + 26.6χ
  + (1.195·90e^{-(J-4)/2})^{1/2})`.

The fold and the cut (`RMF.integral_rpow_fracLine_le_four`); Jensen inside `e^{-K}` and beyond
`e^{J-4}`; the mesoscopic windows by `RMF.window_frac_meso` (constant `≤ 7.08`, `G_k ≤ 2.2437`)
and the far windows by `RMF.window_far_frac` (constant `≤ 0.81√(78.07 + j)`), summed by
`RMF.sum_fracMeso_weight_le` and `RMF.sum_fracFar_weight_le`. -/
theorem integral_rpow_fracLine_le_of_windows {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y : ℕ} (hy : Real.exp 99 ≤ (y : ℝ))
    (hly : 22000 ≤ Real.log y) {σ E₀ χ : ℝ} (hσ : 0 < σ) (hE₀ : 0 ≤ E₀)
    (hE₀1 : E₀ ≤ 1 / 160000) (hσy : σ * Real.log y ≤ E₀) (hlev : radBlockBadLevel E₀ ≤ 65)
    {K J : ℕ} (hK : 4 ≤ K) (hJ : 13 ≤ J) (hχ : 0 ≤ χ)
    (hwin : ∀ D : ℕ, D ≤ 105 + K + J → D ≤ ⌊Real.log (Real.log y)⌋₊
      ∧ (65 + J : ℝ) / 4 + 3 * Real.sqrt (harperBlockCount D y : ℝ) / 4 + 1
          ≤ 1 / 50 * (harperBlockCount D y : ℝ)
      ∧ 3 ≤ 8 * (1 / 50) * Real.sqrt (harperBlockCount D y : ℝ)
      ∧ (1 + (1 - 1 / 2) * Real.sqrt (harperBlockCount D y : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ χ) :
    (∫ ω, ((Real.log y)⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
          * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
      ≤ Real.sqrt 2 * ((1.195 * (0.7151 * Real.exp (-(K : ℝ)))) ^ (1 / 2 : ℝ)
          + 0.598 * (K * σ + 0.03) * (2.2437 * (7.08 * χ)) + 26.6 * χ
          + (1.195 * (90 * Real.exp ((J : ℝ) - 4) ^ (-(1 / 2 : ℝ)))) ^ (1 / 2 : ℝ)) := by
  haveI := hX.isProbabilityMeasure
  have hy100 : (100 : ℝ) ≤ (y : ℝ) := le_trans (by linarith [Real.add_one_le_exp (99 : ℝ)]) hy
  have hy2 : 2 ≤ y := by exact_mod_cast (by linarith : (2 : ℝ) ≤ y)
  have hlogy : 0 < Real.log y := by linarith
  have hL0 : 0 ≤ (Real.log y)⁻¹ := inv_nonneg.2 hlogy.le
  have hσ0 := hσ.le
  have hE₀10 : E₀ ≤ 1 / 10 := by linarith
  have hKR : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hJR : (13 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hab : Real.exp (-(K : ℝ)) ≤ Real.exp (-4) := Real.exp_le_exp.2 (by linarith)
  have hbc : Real.exp (-4) ≤ Real.exp ((J : ℝ) - 4) := Real.exp_le_exp.2 (by linarith)
  have h4 := integral_rpow_fracLine_le_four hX hy2 hσ0 (Real.exp_pos (-(K : ℝ))).le hab hbc
    (μ := μ)
  have hρi := integrable_normSq_fracMellin (σ := σ) (by linarith)
  have hρ0 : ∀ t : ℝ, 0 ≤ ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := fun t => sq_nonneg _
  have hI0 : ∀ (S : Set ℝ) (ω : Ω), 0 ≤ ∫ t in S, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2 :=
    fun S ω => integral_nonneg fun t => mul_nonneg (hρ0 t) (sq_nonneg _)
  -- the inner piece
  have hin : (∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Ioc 0 (Real.exp (-(K : ℝ))),
      ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
      ≤ (1.195 * (0.7151 * Real.exp (-(K : ℝ)))) ^ (1 / 2 : ℝ) := by
    refine integral_rpow_fracPiece_le_jensen hX hy hσ0 measurableSet_Ioc ?_
    calc (∫ t in Set.Ioc 0 (Real.exp (-(K : ℝ))), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
        ≤ ∫ t in Set.Icc 0 (Real.exp (-(K : ℝ))), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 :=
          setIntegral_mono_set hρi.integrableOn (Filter.Eventually.of_forall hρ0)
            Set.Ioc_subset_Icc_self.eventuallyLE
      _ ≤ 0.7151 * (Real.exp (-(K : ℝ)) - 0) :=
          setIntegral_Icc_normSq_fracMellin_le hσ0 (Real.exp_pos _).le
      _ = 0.7151 * Real.exp (-(K : ℝ)) := by ring
  -- the tail
  have hc1 : 1 ≤ Real.exp ((J : ℝ) - 4) := Real.one_le_exp (by linarith)
  have htl := integral_rpow_fracPiece_le_jensen hX hy hσ0 measurableSet_Ioi
    (setIntegral_Ioi_normSq_fracMellin_le_tail hσ0 hc1) (μ := μ)
  -- the mesoscopic range
  have hme : (∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Ioc (Real.exp (-(K : ℝ))) (Real.exp (-4)),
      ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
      ≤ 0.598 * (K * σ + 0.03) * (2.2437 * (7.08 * χ)) := by
    rw [integral_rpow_const_mul hL0 (hI0 _)]
    have hdec := integral_rpow_fracMeso_le_sum_windows hX (y + 1) hσ0 4 K (μ := μ)
    simp only [Nat.cast_ofNat] at hdec
    have hwk : ∀ k ∈ Finset.Ico 4 K, (Real.log y)⁻¹ ^ (1 / 2 : ℝ)
        * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1) (Real.exp (-(k : ℝ))),
          ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ
        ≤ (0.7151 * (σ ^ 2 + Real.exp (-(k : ℝ)) ^ 2) / 2) ^ (1 / 2 : ℝ)
          * (2.2437 * (7.08 * χ)) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hDle : uOffset k ≤ 105 + K + J := by
        unfold uOffset
        omega
      obtain ⟨hDy, hroom, hmono, hχD⟩ := hwin (uOffset k) hDle
      have hw := window_frac_meso E₀ (11 / 20) hE₀ hE₀10 (by norm_num) (by norm_num)
        (Tr := 30) (κ := 8) (Amax := 65 + J) (δ := 1 / 50)
        (N := harperBlockCount (uOffset k) y) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hroom hmono hX (k := k) (y := y) (D := uOffset k) (σ := σ) (A := 65)
        (lam := 49) hσ (by omega) (le_max_left _ _) (le_max_right _ _) hDy hσy le_rfl hlev
        (by linarith) (by norm_num)
      have hG := thetaWindowConst_rpow_le_four hk.1 hly
      have hG0 : 0 ≤ thetaWindowConst (3 / 2) k y ^ (1 / 2 : ℝ) :=
        Real.rpow_nonneg (thetaWindowConst_nonneg (by norm_num) k y) _
      have hDk : ((uOffset k : ℕ) : ℝ) - k ≤ 101 := by
        have hk4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
        have hD : ((uOffset k : ℕ) : ℝ) ≤ (k : ℝ) + 101 := by
          unfold uOffset
          push_cast
          exact max_le (by linarith) (by linarith)
        linarith
      have hC := fracMesoChaosConst_le hE₀ hE₀1 hDk
      have hC0 : 0 ≤ shiftMomentConst 1 (radAveragedConst E₀ (11 / 20) 30 8)
          (radBlockBadConst E₀ (11 / 20) * Real.exp (((uOffset k : ℕ) : ℝ) - k)) 65
          (radAveragedShift E₀ (11 / 20) 30 8) 49 (1 / 50) (1 / 2) := by
        rw [shiftMomentConst]
        exact le_trans (Real.rpow_nonneg (by positivity) _) (le_max_left _ _)
      have hχ0 : 0 ≤ (1 + (1 - 1 / 2) * Real.sqrt (harperBlockCount (uOffset k) y : ℝ))
          ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
      have hak : 0 ≤ (0.7151 * (σ ^ 2 + Real.exp (-(k : ℝ)) ^ 2) / 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_nonneg (by positivity) _
      refine le_trans hw ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hak
      exact mul_le_mul (le_trans hG (by norm_num)) (mul_le_mul hC hχD hχ0 (by norm_num))
        (mul_nonneg hC0 hχ0) (by norm_num)
    calc (Real.log y)⁻¹ ^ (1 / 2 : ℝ) * ∫ ω, (∫ t in Set.Ioc (Real.exp (-(K : ℝ)))
          (Real.exp (-4)), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ
        ≤ (Real.log y)⁻¹ ^ (1 / 2 : ℝ) * ∑ k ∈ Finset.Ico 4 K, ∫ ω, (∫ t in Set.Icc
          (Real.exp (-(k : ℝ)) / Real.exp 1) (Real.exp (-(k : ℝ))),
          ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ :=
          mul_le_mul_of_nonneg_left hdec (Real.rpow_nonneg hL0 _)
      _ ≤ ∑ k ∈ Finset.Ico 4 K, (0.7151 * (σ ^ 2 + Real.exp (-(k : ℝ)) ^ 2) / 2) ^ (1 / 2 : ℝ)
          * (2.2437 * (7.08 * χ)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum hwk
      _ = (∑ k ∈ Finset.Ico 4 K, (0.7151 * (σ ^ 2 + Real.exp (-(k : ℝ)) ^ 2) / 2) ^ (1 / 2 : ℝ))
          * (2.2437 * (7.08 * χ)) := by rw [Finset.sum_mul]
      _ ≤ 0.598 * (K * σ + 0.03) * (2.2437 * (7.08 * χ)) :=
          mul_le_mul_of_nonneg_right (sum_fracMeso_weight_le hσ0 K) (by positivity)
  -- the far range
  have hfa : (∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Ioc (Real.exp (-4)) (Real.exp ((J : ℝ) - 4)),
      ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ) ≤ 26.6 * χ := by
    rw [integral_rpow_const_mul hL0 (hI0 _)]
    have hdec := integral_rpow_fracFar_le_sum_windows hX (y + 1) hσ0 J (μ := μ)
    have hwj : ∀ j ∈ Finset.range J, (Real.log y)⁻¹ ^ (1 / 2 : ℝ)
        * ∫ ω, (∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1) (Real.exp ((j : ℝ) - 3)),
          ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ
        ≤ 0.81 * Real.sqrt (78.07 + j)
          * (1.195 * ∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1)
            (Real.exp ((j : ℝ) - 3)), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
              ^ (1 / 2 : ℝ) * χ := by
      intro j hj
      have hjJ : j < J := Finset.mem_range.1 hj
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hjJR : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hjJ.le
      obtain ⟨hDy, hroom, hmono, hχD⟩ := hwin (105 + j) (by omega)
      have hw := window_far_frac E₀ (11 / 20) hE₀ hE₀10 (by norm_num) (by norm_num)
        (Tr := 30) (κ := 8) (Amax := 65 + J) (δ := 1 / 50)
        (N := harperBlockCount (105 + j) y) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hroom hmono hX (r := 1 / 2) (by norm_num) (by norm_num) (j := j) (y := y)
        (σ := σ) (A := 65 + j) (lam := 49) hσ0 hy hDy hσy le_rfl (by linarith) (by linarith)
        (by norm_num)
      have hC := fracFarChaosConst_le hE₀ hE₀1 j
      have hm0 : 0 ≤ (1.195 * ∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1)
          (Real.exp ((j : ℝ) - 3)), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
            ^ (1 / 2 : ℝ) :=
        Real.rpow_nonneg (mul_nonneg (by norm_num) (integral_nonneg hρ0)) _
      have hχ0 : 0 ≤ (1 + (1 - 1 / 2) * Real.sqrt (harperBlockCount (105 + j) y : ℝ))
          ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
      refine le_trans hw ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_right hC hm0) hχD hχ0
        (mul_nonneg (by positivity) hm0)
    calc (Real.log y)⁻¹ ^ (1 / 2 : ℝ) * ∫ ω, (∫ t in Set.Ioc (Real.exp (-4))
          (Real.exp ((J : ℝ) - 4)), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ
        ≤ (Real.log y)⁻¹ ^ (1 / 2 : ℝ) * ∑ j ∈ Finset.range J, ∫ ω, (∫ t in Set.Icc
          (Real.exp ((j : ℝ) - 3) / Real.exp 1) (Real.exp ((j : ℝ) - 3)),
          ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ :=
          mul_le_mul_of_nonneg_left hdec (Real.rpow_nonneg hL0 _)
      _ ≤ ∑ j ∈ Finset.range J, 0.81 * Real.sqrt (78.07 + j)
          * (1.195 * ∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1)
            (Real.exp ((j : ℝ) - 3)), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
              ^ (1 / 2 : ℝ) * χ := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum hwj
      _ = (∑ j ∈ Finset.range J, 0.81 * Real.sqrt (78.07 + j)
          * (1.195 * ∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1)
            (Real.exp ((j : ℝ) - 3)), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
              ^ (1 / 2 : ℝ)) * χ := by rw [Finset.sum_mul]
      _ ≤ 26.6 * χ := mul_le_mul_of_nonneg_right (sum_fracFar_weight_le hσ0 hJ) hχ
  refine le_trans h4 (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2))
  linarith [hin, hme, hfa, htl]

/-! ### The parameters at `Λ = log log x` -/

/-- `log Λ ≤ 10.99 + Λ/160000` for `Λ > 0`: `log(Λ/160000) ≤ Λ/160000 - 1`. -/
lemma log_le_frac_linear {Λ : ℝ} (hΛ : 0 < Λ) : Real.log Λ ≤ 10.99 + Λ / 160000 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hΛ (by norm_num : (0 : ℝ) < 160000))
  rw [Real.log_div hΛ.ne' (by norm_num)] at h
  have h2 : Real.log 160000 ≤ 11.99 := by interval_decide (trust := kernel)
  linarith

/-- `y = ⌊x^{1/U}⌋ ≥ x^{1/U}/2`, so `log y ≥ log x/U - 1`, for `x ≥ exp(e^{20})`. -/
lemma log_fracY_ge {x : ℝ} (hx : Real.exp (Real.exp 20) ≤ x) :
    Real.log x / fracU x - 1 ≤ Real.log (fracY x) := by
  obtain ⟨hx0, -, -, hΛ, hexp⟩ := log_facts_of_exp_exp_twenty_le hx
  have hU : fracU x = 16 * Real.log (Real.log x) + 85 := rfl
  have hU0 : 0 < fracU x := by rw [hU]; linarith
  set A := Real.log x / fracU x with hAdef
  have hA : (1000001 : ℝ) ≤ A := by
    rw [hAdef, le_div_iff₀ hU0, hU]
    have := mul_fracU_le_exp hΛ
    rw [hexp] at this
    linarith
  have hpow : x ^ (1 / fracU x) = Real.exp A := by
    rw [Real.rpow_def_of_pos hx0, hAdef]
    congr 1
    ring
  have hy : fracY x = ⌊Real.exp A⌋₊ := by rw [fracY, hpow]
  have heA : A + 1 ≤ Real.exp A := Real.add_one_le_exp A
  have hlt : Real.exp A < (fracY x : ℝ) + 1 := by rw [hy]; exact Nat.lt_floor_add_one _
  have hhalf : Real.exp A / 2 ≤ (fracY x : ℝ) := by linarith
  have hlog := Real.log_le_log (by positivity) hhalf
  rw [Real.log_div (Real.exp_pos A).ne' two_ne_zero, Real.log_exp] at hlog
  have hl2 := Real.log_two_lt_d9
  linarith

/-- **Room for the levels**: for `n ≥ 0.998Λ`, `Λ ≥ 160000` and `J ≤ 38 + Λ/160000`,
`(65 + J)/4 + 3√n/4 + 1 ≤ n/50` and `3 ≤ (8/50)√n` (`√n ≥ 399`). -/
lemma frac_room {n Λ J : ℝ} (hΛ : 160000 ≤ Λ) (hn : 998 / 1000 * Λ ≤ n)
    (hJ : J ≤ 38 + Λ / 160000) :
    (65 + J) / 4 + 3 * Real.sqrt n / 4 + 1 ≤ 1 / 50 * n ∧ 3 ≤ 8 * (1 / 50) * Real.sqrt n := by
  have hn0 : 159680 ≤ n := by linarith
  have hs : 399 ≤ Real.sqrt n := by
    rw [show (399 : ℝ) = Real.sqrt (399 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by linarith)
  have hsn : 399 * Real.sqrt n ≤ n := by nlinarith
  constructor <;> linarith

/-- **The depth factor**: for `n ≥ 0.998Λ`, `(1 + ½√n)^{-1/2} ≤ 1.415Λ^{-1/4}`, since
`(1 + ½√n)² ≥ n/4` and `1.415⁴·0.998/4 ≥ 1`. -/
lemma frac_depth_le {n Λ : ℝ} (hΛ : 0 < Λ) (hn : 998 / 1000 * Λ ≤ n) :
    (1 + (1 - 1 / 2) * Real.sqrt n) ^ (-(1 / 2 : ℝ)) ≤ 1.415 * Λ ^ (-(1 / 4 : ℝ)) := by
  have hn0 : 0 ≤ n := by linarith
  set p := 1 + (1 - 1 / 2) * Real.sqrt n with hp
  have hp0 : 0 < p := by rw [hp]; positivity
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
  have hp2 : n / 4 ≤ p ^ 2 := by
    rw [hp]
    have := Real.sqrt_nonneg n
    nlinarith
  have hM0 : 0 < Λ ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hΛ _
  have hM4 : (Λ ^ (-(1 / 4 : ℝ))) ^ 4 = Λ⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ.le]
    norm_num
    exact Real.rpow_neg_one Λ
  have hP4 : (p ^ (-(1 / 2 : ℝ))) ^ 4 = (p ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
      show (-(1 / 2 : ℝ)) * ((4 : ℕ) : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hp0.le,
      Real.rpow_natCast]
  have hlhs0 : 0 ≤ p ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hp0.le _
  have hrhs0 : 0 ≤ 1.415 * Λ ^ (-(1 / 4 : ℝ)) := by positivity
  refine (pow_le_pow_iff_left₀ hlhs0 hrhs0 (by norm_num : (4 : ℕ) ≠ 0)).1 ?_
  rw [hP4, mul_pow, hM4]
  have hp20 : 0 < p ^ 2 := by positivity
  rw [inv_le_iff_one_le_mul₀ hp20]
  have hkey : Λ ≤ 1.415 ^ 4 * p ^ 2 := by nlinarith
  calc (1 : ℝ) = Λ⁻¹ * Λ := (inv_mul_cancel₀ hΛ.ne').symm
    _ ≤ Λ⁻¹ * (1.415 ^ 4 * p ^ 2) := mul_le_mul_of_nonneg_left hkey (inv_nonneg.2 hΛ.le)
    _ = 1.415 ^ 4 * Λ⁻¹ * p ^ 2 := by ring

/-- **The final arithmetic**: for `M > 0`, `Kσ ≤ 1.25·10⁻⁵`, the inner piece `≤ 0.0463M` and the
tail `≤ 0.0425M`, the assembled bound with `χ = 1.415M` is at most `55M`. -/
lemma frac_final_le {M Kσ inner tail : ℝ} (hM0 : 0 < M) (hKσ : Kσ ≤ 0.0000125)
    (hin : inner ≤ 0.0463 * M) (htl : tail ≤ 0.0425 * M) :
    Real.sqrt 2 * (inner + 0.598 * (Kσ + 0.03) * (2.2437 * (7.08 * (1.415 * M)))
      + 26.6 * (1.415 * M) + tail) ≤ 55 * M := by
  have hs2 : Real.sqrt 2 ≤ 1.41422 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hmeso : 0.598 * (Kσ + 0.03) * (2.2437 * (7.08 * (1.415 * M))) ≤ 0.4035 * M := by
    have h1 : 0.598 * (Kσ + 0.03) ≤ 0.598 * 0.0300125 := by nlinarith
    have h2 : 0 ≤ 2.2437 * (7.08 * (1.415 * M)) := by positivity
    calc 0.598 * (Kσ + 0.03) * (2.2437 * (7.08 * (1.415 * M)))
        ≤ 0.598 * 0.0300125 * (2.2437 * (7.08 * (1.415 * M))) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ ≤ 0.4035 * M := by nlinarith
  have hbr : inner + 0.598 * (Kσ + 0.03) * (2.2437 * (7.08 * (1.415 * M)))
      + 26.6 * (1.415 * M) + tail ≤ 38.132 * M := by nlinarith
  calc Real.sqrt 2 * (inner + 0.598 * (Kσ + 0.03) * (2.2437 * (7.08 * (1.415 * M)))
        + 26.6 * (1.415 * M) + tail)
      ≤ Real.sqrt 2 * (38.132 * M) := mul_le_mul_of_nonneg_left hbr (Real.sqrt_nonneg 2)
    _ ≤ 1.41422 * (38.132 * M) := mul_le_mul_of_nonneg_right hs2 (by positivity)
    _ ≤ 55 * M := by nlinarith

/-- `Λ^{-1/4}` for `Λ ≥ 160000`: positive, `(Λ^{-1/4})⁴ = Λ⁻¹`, `(Λ^{-1/4})² = Λ^{-1/2}`, and
`Λ^{-1/4} ≤ 1/20`. -/
lemma rpow_neg_quarter_facts {Λ : ℝ} (hΛ : 160000 ≤ Λ) :
    0 < Λ ^ (-(1 / 4 : ℝ)) ∧ (Λ ^ (-(1 / 4 : ℝ))) ^ 4 = Λ⁻¹
      ∧ (Λ ^ (-(1 / 4 : ℝ))) ^ 2 = Λ ^ (-(1 / 2 : ℝ)) ∧ Λ ^ (-(1 / 4 : ℝ)) ≤ 1 / 20 := by
  have hΛ0 : 0 < Λ := by linarith
  have hM0 : 0 < Λ ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hΛ0 _
  have hM4 : (Λ ^ (-(1 / 4 : ℝ))) ^ 4 = Λ⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ0.le,
      show (-(1 / 4 : ℝ)) * ((4 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have hM2 : (Λ ^ (-(1 / 4 : ℝ))) ^ 2 = Λ ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ0.le,
      show (-(1 / 4 : ℝ)) * ((2 : ℕ) : ℝ) = -(1 / 2) by norm_num]
  refine ⟨hM0, hM4, hM2, ?_⟩
  refine (pow_le_pow_iff_left₀ hM0.le (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)).1 ?_
  rw [hM4, inv_le_comm₀ hΛ0 (by norm_num)]
  norm_num
  linarith

/-! ### The headline -/

set_option maxHeartbeats 800000 in
-- the parameters at `Λ`, then the assembly
/-- **The remainder's windows, explicit**: for every Rademacher `X`, every `x ≥ 3` with
`Λ = log log x ≥ 160000` and every `0 < c ≤ 1`, with `y = RMF.fracY x` and `σ = c/log x`,

`E[((log y)⁻¹∫_ℝ‖F_{y+1}(½+σ+it)‖²|φ̂(½+σ+it)|²dt)^{1/2}] ≤ 55Λ^{-1/4}`,

in the form `RMF.integral_norm_fracPartSum_le_lineFrac` uses.  It is
`RMF.integral_rpow_fracLine_le_of_windows` at `K = ⌈log Λ⌉`, `J = K + 26`, `E₀ = 1/(16Λ)` and
`χ = 1.415Λ^{-1/4}`: `σ log y ≤ c/U ≤ E₀`, `log log y ≥ Λ - log Λ - 3.53`, so every offset
`D ≤ 131 + 2K` leaves `n ≥ 0.998Λ` blocks. -/
theorem integral_rpow_fracLine_le_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x c : ℝ} (hx : 3 ≤ x)
    (hΛ : 160000 ≤ Real.log (Real.log x)) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (∫ ω, ((Real.log (fracY x))⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (fracY x + 1)
                ((1 / 2 : ℂ) + ((c / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
              * ‖fracMellin (1 / 2 + ((c / Real.log x : ℝ) : ℂ) + t * Complex.I)‖ ^ 2)
                ^ (1 / 2 : ℝ) ∂μ)
      ≤ 55 * Real.log (Real.log x) ^ (-(1 / 4 : ℝ)) := by
  -- the scales
  have hx0 : 0 < x := by linarith
  have hL1 : 1 < Real.log x := by
    rw [Real.lt_log_iff_exp_lt hx0]
    have := Real.exp_one_lt_d9
    linarith
  set L := Real.log x with hLdef
  set Λ := Real.log L with hΛdef
  have hexpΛ : Real.exp Λ = L := Real.exp_log (by linarith)
  have hΛ0 : 0 < Λ := by linarith
  have hx20 : Real.exp (Real.exp 20) ≤ x := by
    have h1 : Real.exp 20 ≤ L := by rw [← hexpΛ]; exact Real.exp_le_exp.2 (by linarith)
    calc Real.exp (Real.exp 20) ≤ Real.exp L := Real.exp_le_exp.2 h1
      _ = x := Real.exp_log hx0
  obtain ⟨hy2, hy6, hyL⟩ := fracY_facts hx20
  have hyge := log_fracY_ge hx20
  have hU : fracU x = 16 * Λ + 85 := rfl
  set y := fracY x with hydef
  set U := fracU x with hUdef
  have hU0 : 0 < U := by rw [hU]; linarith
  have hy99 : Real.exp 99 ≤ (y : ℝ) := by
    have hy0 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
    calc Real.exp 99 ≤ Real.exp (Real.log y) := Real.exp_le_exp.2 (by linarith)
      _ = y := Real.exp_log hy0
  have hly : 22000 ≤ Real.log y := by linarith
  -- the line and the tilt
  set σ := c / L with hσdef
  have hσ : 0 < σ := div_pos hc0 (by linarith)
  have hσ1 : σ ≤ 1 / L := by rw [hσdef]; exact div_le_div_of_nonneg_right hc1 (by linarith)
  set E₀ := 1 / (16 * Λ) with hE₀def
  have hE₀ : 0 ≤ E₀ := by positivity
  have hE₀1 : E₀ ≤ 1 / 160000 := by
    rw [hE₀def, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hσy : σ * Real.log y ≤ E₀ := by
    have h1 : σ * Real.log y ≤ σ * (L / U) := mul_le_mul_of_nonneg_left hyL hσ.le
    have h2 : σ * (L / U) = c / U := by
      rw [hσdef]
      field_simp
    have h3 : c / U ≤ 1 / (16 * Λ) := by
      rw [div_le_div_iff₀ hU0 (by positivity), hU]
      nlinarith
    linarith
  have hlev : radBlockBadLevel E₀ ≤ 65 := le_trans (half_level_le_B (by linarith)) (by norm_num)
  -- the cut points
  have hlogΛ := log_le_frac_linear hΛ0
  have hlogΛ4 : 4 ≤ Real.log Λ := by
    rw [Real.le_log_iff_exp_le hΛ0]
    have : Real.exp 4 ≤ 55 := by interval_decide (trust := kernel)
    linarith
  set K := ⌈Real.log Λ⌉₊ with hKdef
  have hKge : Real.log Λ ≤ (K : ℝ) := Nat.le_ceil _
  have hKle : (K : ℝ) < Real.log Λ + 1 := Nat.ceil_lt_add_one (by linarith)
  have hK4 : 4 ≤ K := by exact_mod_cast (le_trans hlogΛ4 hKge)
  set J := K + 26 with hJdef
  have hJ : 13 ≤ J := by omega
  have hJR : (J : ℝ) = K + 26 := by rw [hJdef]; push_cast; ring
  -- the depth of every window
  set M := Λ ^ (-(1 / 4 : ℝ)) with hMdef
  obtain ⟨hM0, hM4, hM2, hM20⟩ := rpow_neg_quarter_facts hΛ
  have hloglog : Λ - Real.log Λ - 3.53 ≤ Real.log (Real.log y) := by
    have h1 : L / (2 * U) ≤ Real.log y := by
      have : L / (2 * U) = (L / U) / 2 := by field_simp
      rw [this]
      linarith
    have h2 : Real.log (L / (2 * U)) ≤ Real.log (Real.log y) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_div (by positivity) (by positivity)] at h2
    have h3 : Real.log (2 * U) ≤ Real.log (34 * Λ) :=
      Real.log_le_log (by positivity) (by rw [hU]; linarith)
    rw [Real.log_mul (by norm_num) hΛ0.ne'] at h3
    have h34 : Real.log 34 ≤ 3.53 := by interval_decide (trust := kernel)
    linarith
  have hfl : Real.log (Real.log y) - 1 < (⌊Real.log (Real.log y)⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (Real.log (Real.log y))
    linarith
  have hwin : ∀ D : ℕ, D ≤ 105 + K + J → D ≤ ⌊Real.log (Real.log y)⌋₊
      ∧ (65 + J : ℝ) / 4 + 3 * Real.sqrt (harperBlockCount D y : ℝ) / 4 + 1
          ≤ 1 / 50 * (harperBlockCount D y : ℝ)
      ∧ 3 ≤ 8 * (1 / 50) * Real.sqrt (harperBlockCount D y : ℝ)
      ∧ (1 + (1 - 1 / 2) * Real.sqrt (harperBlockCount D y : ℝ)) ^ (-(1 / 2 : ℝ))
          ≤ 1.415 * M := by
    intro D hD
    have hDR : (D : ℝ) ≤ 105 + K + J := by exact_mod_cast hD
    have hbig : (D : ℝ) + 998 / 1000 * Λ ≤ (⌊Real.log (Real.log y)⌋₊ : ℝ) := by linarith
    have hDfl : D ≤ ⌊Real.log (Real.log y)⌋₊ := by
      have : (D : ℝ) ≤ (⌊Real.log (Real.log y)⌋₊ : ℝ) := by linarith
      exact_mod_cast this
    have hn : 998 / 1000 * Λ ≤ (harperBlockCount D y : ℝ) := by
      rw [harperBlockCount, Nat.cast_sub hDfl]
      linarith
    have hJb : (J : ℝ) ≤ 38 + Λ / 160000 := by linarith
    obtain ⟨hroom, hmono⟩ := frac_room hΛ hn hJb
    exact ⟨hDfl, hroom, hmono, frac_depth_le hΛ0 hn⟩
  have hmain := integral_rpow_fracLine_le_of_windows hX hy99 hly hσ hE₀ hE₀1 hσy hlev hK4 hJ
    (χ := 1.415 * M) (by positivity) hwin (μ := μ)
  refine le_trans hmain ?_
  -- the three small terms
  have hKσ : (K : ℝ) * σ ≤ 0.0000125 := by
    have hK1 : (K : ℝ) ≤ Λ := by linarith
    have hLq : Λ ^ 2 / 2 ≤ L := by
      rw [← hexpΛ]
      have := Real.quadratic_le_exp_of_nonneg hΛ0.le
      nlinarith
    have hL0 : 0 < L := by linarith
    calc (K : ℝ) * σ ≤ Λ * (1 / L) := mul_le_mul hK1 hσ1 hσ.le hΛ0.le
      _ ≤ 0.0000125 := by
          rw [mul_one_div, div_le_iff₀ hL0]
          nlinarith
  have hin : (1.195 * (0.7151 * Real.exp (-(K : ℝ)))) ^ (1 / 2 : ℝ) ≤ 0.0463 * M := by
    have heK : Real.exp (-(K : ℝ)) ≤ M ^ 2 * (1 / 400) := by
      have hMsq : M ^ 2 ≤ 1 / 400 := by nlinarith
      calc Real.exp (-(K : ℝ)) ≤ Real.exp (-Real.log Λ) := Real.exp_le_exp.2 (by linarith)
        _ = Λ⁻¹ := by rw [Real.exp_neg, Real.exp_log hΛ0]
        _ = M ^ 2 * M ^ 2 := by rw [← hM4]; ring
        _ ≤ M ^ 2 * (1 / 400) := mul_le_mul_of_nonneg_left hMsq (by positivity)
    refine rpow_half_le_of_le (by positivity) ?_
    rw [mul_pow]
    nlinarith
  have htl : (1.195 * (90 * Real.exp ((J : ℝ) - 4) ^ (-(1 / 2 : ℝ)))) ^ (1 / 2 : ℝ)
      ≤ 0.0425 * M := by
    have he11 : Real.exp (-11) ≤ 0.000016702 := by interval_decide (trust := kernel)
    have hT : Real.exp ((J : ℝ) - 4) ^ (-(1 / 2 : ℝ)) ≤ Real.exp (-11) * M ^ 2 := by
      rw [← Real.exp_mul, hM2, Real.rpow_def_of_pos hΛ0, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by rw [hJR]; linarith)
    have hT0 : 0 ≤ Real.exp ((J : ℝ) - 4) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    refine rpow_half_le_of_le (by positivity) ?_
    rw [mul_pow]
    have hM2' : 0 ≤ M ^ 2 := by positivity
    nlinarith
  exact frac_final_le hM0 hKσ hin htl

end RMF
