/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.BandWindowsExplicit

/-!
# The chaos windows of a band, for `q ≤ 1`

One window of a band `[y₀, y'+1)`, split at `z₁`, with the upper block bounded by the weighted block
chaos (`RMF.integral_rpow_block_weight_le_floor` at `x = y'`, which holds at every `0 ≤ q ≤ 1`):

`E[(∫_{T/e}^{T}(σ²+t²)⁻¹‖F_{[y₀,y'+1)}(½+σ+it)‖²dt)^q]
  ≤ E‖F_{[y₀,z₁)}(½+σ)‖^{2q}·shiftMomentConst 1 C_i (C_b K_ϑ) A s λ δ q·(RM)^q·(1+(1-q)√n)^{-q}`

(`RMF.integral_rpow_window_band_le_split_chaos_of_weight`), `n = harperBlockCount D y'`, `R` a
bound on the window's weight and `M` on the upper block's mean.  The full-product twin is
`RMF.integral_rpow_window_le_split_chaos_of_weight` (`q ≤ ½`, through its split).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **One window of a band by the split and the weighted chaos, for `q ≤ 1`.**  For a band
`[y₀, y'+1)` split at `y₀ ≤ z₁ ≤ y'+1`, `σ > 0`, `0 ≤ q ≤ 1`, `0 < T ≤ 1`,
`β ≥ 2(1-q)S₂(z₁)`, a bound `R` on the window's weight `∫_{T/e}^{T}e^{βt²}dt/(σ²+t²)`, a bound `M`
on the upper block's mean `E‖F_{[z₁,y'+1)}(½+σ)‖²` and the chaos's hypotheses at `x = y'`:

`E[(∫_{T/e}^{T}(σ²+t²)⁻¹‖F_{[y₀,y'+1)}(½+σ+it)‖²dt)^q]
  ≤ E‖F_{[y₀,z₁)}(½+σ)‖^{2q}·(shiftMomentConst 1 C_i (C_b K_ϑ) A s λ δ q·(RM)^q
      ·(1 + (1-q)√n)^{-q})`,

`n = harperBlockCount D y'`: the split at any `q ≤ 1`
(`RMF.integral_rpow_setIntegral_weight_split_primesIco_le_sharp_of_le_one`) and the weighted
block chaos on the upper block (`RMF.integral_rpow_block_weight_le_floor`). -/
theorem integral_rpow_window_band_le_split_chaos_of_weight (E₀ βc : ℝ) (hE₀ : 0 ≤ E₀)
    (hE₀1 : E₀ ≤ 1) (hβc : 1 / 2 < βc) (hβc2 : βc ≤ 2) {Tr κ Kθ Amax δ : ℝ} {N : ℕ}
    (hTr : 4 < Tr) (hκ : 1 ≤ κ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δ * N)
    (hmono : 3 ≤ 8 * δ * Real.sqrt (N : ℝ))
    {Y : ℕ → Ω → ℂ} {ν : Measure Ω} (hY : IsRademacherPrimeValues Y ν) {y₀ z₁ y' D : ℕ}
    (hy₀z₁ : y₀ ≤ z₁) (hz₁y : z₁ ≤ y' + 1) {σ η q T β A lam R M : ℝ}
    (hσ : 0 < σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hT : 0 < T) (hT1 : T ≤ 1) (hβ0 : 0 ≤ β)
    (hβ : 2 * (1 - q) * (Real.log z₁ ^ 2 / 2 + 15.003 * Real.log z₁ + 34) ≤ β)
    (hy1 : (1 : ℝ) < y') (hDlog : (D : ℝ) ≤ Real.log (Real.log y'))
    (hϑ : radFreeStartThreshold E₀ ≤ harperOffset D y')
    (hϑ104 : (104 : ℝ) ≤ harperOffset D y')
    (hη0 : 0 ≤ η) (hηE : η ≤ E₀) (hσx : σ * Real.log y' ≤ η)
    (hlo : 600 * Real.exp (2 * E₀) ≤ 2 * (T / Real.exp 1) * Real.exp (harperOffset D y'))
    (hKθ : T * Real.exp (harperOffset D y') ≤ Kθ)
    (hzb : (z₁ : ℝ) ≤ blockScale (harperOffset D y') 0)
    (hNn : N ≤ harperBlockCount D y')
    (hA : radBlockBadLevel E₀ ≤ A) (hAmax : A ≤ Amax) (hlam : 1 ≤ lam)
    (hR : (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2)) ≤ R)
    (hM : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z₁ (y' + 1)
        (shiftLine σ 0) ω‖ ^ 2 ∂ν) ≤ M) :
    (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ (y' + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ z₁
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂ν)
        * (shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ) (radBlockBadConst E₀ βc * Kθ) A
            (radAveragedShift E₀ βc Tr κ) lam δ q
          * (R * M) ^ q
          * (1 + (1 - q) * Real.sqrt (harperBlockCount D y' : ℝ)) ^ (-q)) := by
  haveI := hY.isProbabilityMeasure
  obtain ⟨hρb, hρb', hρρ', hρpos⟩ := window_weights hσ hT hβ0
  have hρm' : Measurable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)) :=
    by fun_prop
  have hρ0' : ∀ t : ℝ, 0 ≤ (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)) :=
    fun t => by positivity
  -- the split
  have hsplit := integral_rpow_setIntegral_weight_split_primesIco_le_sharp_of_le_one hY
    (y₀ := y₀) (z := z₁) (y := y' + 1) hy₀z₁ hz₁y (σ := σ) (a := T / Real.exp 1)
    (b := T) (q := q) (β := β) (Bd := (σ ^ 2)⁻¹) (Bd' := (σ ^ 2)⁻¹ * Real.exp (β * T ^ 2))
    (ρ := fun t => (σ ^ 2 + t ^ 2)⁻¹)
    (ρ' := fun t => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)))
    hσ.le hq0 hq1 hβ (by fun_prop) (fun t => by positivity) hρb hρm' hρ0' hρb'
    (fun t ht => le_of_eq (hρρ' t ht)) hρpos
  -- the weighted chaos on the upper block, at `x = y'`
  have hρpos' : 0 < ∫ t in Set.Icc (T / Real.exp 1) T,
      (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)) := by
    rw [← setIntegral_congr_fun measurableSet_Icc hρρ']
    haveI : IsFiniteMeasure (volume.restrict (Set.Icc (T / Real.exp 1) T)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
    have hcont : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
      Continuous.inv₀ (by fun_prop) fun t => (by positivity : (0 : ℝ) < σ ^ 2 + t ^ 2).ne'
    refine lt_of_lt_of_le hρpos (setIntegral_mono_on hcont.integrableOn_Icc
      (hcont.mul (by fun_prop)).integrableOn_Icc measurableSet_Icc fun t _ => ?_)
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
  have hfloor : ⌊(y' : ℝ)⌋₊ = y' := Nat.floor_natCast y'
  have hchaos := integral_rpow_block_weight_le_floor E₀ βc hE₀ hE₀1 hβc hβc2 hTr hκ hδ0 hδ hN
    hmono hY (x := (y' : ℝ)) (σ := σ) (η := η) (T := T) (q := q) (A := A) (lam := lam)
    (Bd := (σ ^ 2)⁻¹ * Real.exp (β * T ^ 2)) (z := z₁) (D := D)
    (ρ := fun t => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)))
    hρm' hρ0' hρb' hρpos' hy1 hDlog hϑ hϑ104 hσ.le hη0 hηE
    (by rw [abs_of_pos hσ]; exact hσx) hT hT1 hlo hKθ hzb (by rw [hfloor]; exact hz₁y) hNn hq0
    hq1 hA hAmax hlam
  rw [hfloor] at hchaos
  -- the weight and the mean
  have hW : (∫ t in Set.Icc (T / Real.exp 1) T,
      (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2))) ≤ R := by
    rw [← setIntegral_congr_fun measurableSet_Icc hρρ']
    exact hR
  have hW0 : 0 ≤ ∫ t in Set.Icc (T / Real.exp 1) T,
      (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)) :=
    integral_nonneg fun t => hρ0' t
  have hM0 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
      z₁ (y' + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν := integral_nonneg fun ω => sq_nonneg _
  have hprod := mul_le_mul hW hM hM0 (le_trans hW0 hW)
  have hC0 : 0 ≤ shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ) (radBlockBadConst E₀ βc * Kθ)
      A (radAveragedShift E₀ βc Tr κ) lam δ q := by
    rw [shiftMomentConst]
    exact le_trans (Real.rpow_nonneg (by positivity) _) (le_max_left _ _)
  have h1q : 0 ≤ 1 - q := by linarith
  have hG0 : 0 ≤ (1 + (1 - q) * Real.sqrt (harperBlockCount D y' : ℝ)) ^ (-q) :=
    Real.rpow_nonneg (by positivity) _
  have hupper := le_trans hchaos (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (mul_nonneg hW0 hM0) hprod hq0) hC0) hG0)
  refine le_trans hsplit (mul_le_mul_of_nonneg_left hupper ?_)
  exact integral_nonneg fun ω => by positivity

end RMF
