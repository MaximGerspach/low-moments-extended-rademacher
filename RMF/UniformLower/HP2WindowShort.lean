/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2WindowExt
import RMF.UniformLower.HP2WindowExtNumShort

/-!
# HP2's window integral per tube length

HP2's window integral with the rest (`RMF/UniformLower/HP2WindowExt.lean`) for every tube of
`r ≥ 35` blocks, with the step function `RMF.hp2QShort r` in place of `6482`:
`∫_W∫_W E[1_{H(k,h₁)∩H(k,h₂)}‖F_y(s₁)‖²‖F_y(s₂)‖²] dh₂ dh₁ ≤ (E‖F_y(s_σ)‖²)²·e^{-2k}·hp2QShort r/r`
(`RMF.integral_integral_pair_rest_le_short`), `W = halfWindow k`, `H = RMF.hp1Tube`.

* below `2000`: the window integral on short tubes
  (`RMF.integral_integral_pair_rest_le_hp2ExtSumS`) and the constant at the tube's rung
  (`RMF.hp2ExtSumS_le_hp2QRung`);
* from `2000` on: `RMF.integral_integral_pair_rest_le_two_thousand`.

`RMF.hp2QShort` is `RMF.hp2QRung` below `2000` and `6482` from there, nonincreasing
(`RMF.antitone_hp2QShort`) and at least `6482`.
-/

open MeasureTheory ProbabilityTheory Real

namespace RMF

/-! ### The step function -/

/-- **HP2's constant on tubes of `r` blocks**: the step function `RMF.hp2QRung r` below `2000`,
`6482` from `2000` on. -/
noncomputable def hp2QShort (r : ℕ) : ℝ :=
  if r < 2000 then hp2QRung r else 6482

/-- `RMF.hp2QShort` below `2000`. -/
lemma hp2QShort_of_lt {r : ℕ} (hr : r < 2000) : hp2QShort r = hp2QRung r := by
  unfold hp2QShort
  rw [if_pos hr]

/-- `RMF.hp2QShort` from `2000` on. -/
lemma hp2QShort_of_ge {r : ℕ} (hr : 2000 ≤ r) : hp2QShort r = 6482 := by
  unfold hp2QShort
  rw [if_neg (by omega)]

/-- `RMF.hp2QRung` is at least the rung `160`'s value. -/
lemma hp2QRung_ge (r : ℕ) : 12959 ≤ hp2QRung r := by
  unfold hp2QRung
  split_ifs <;> norm_num

/-- `RMF.hp2QShort` is at least `6482`. -/
lemma hp2QShort_ge (r : ℕ) : 6482 ≤ hp2QShort r := by
  unfold hp2QShort
  split_ifs
  · linarith [hp2QRung_ge r]
  · exact le_rfl

/-- `RMF.hp2QShort` is positive. -/
lemma hp2QShort_pos (r : ℕ) : 0 < hp2QShort r :=
  lt_of_lt_of_le (by norm_num) (hp2QShort_ge r)

/-- `RMF.hp2QShort` is a nonincreasing step function of the tube's length. -/
theorem antitone_hp2QShort : Antitone hp2QShort := by
  intro a b hab
  unfold hp2QShort
  split_ifs with hb ha ha
  · exact hp2QRung_anti hab
  · exact absurd (lt_of_le_of_lt hab hb) ha
  · linarith [hp2QRung_ge a]
  · exact le_rfl

/-! ### The window integral -/

section Pair

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The window's pair integral with the rest from a bound on `r·hp2ExtSumS`**: for `k ≥ 20`,
`σe^{k+r} ≤ 1/200 < σe^{k+r+1}`, `y ≥ c_r`, `r ≥ 35` and `r·hp2ExtSumS r 400 hp2ExtB 5.032 ≤ Q`,
`∫_W∫_W E[1_{H₁∩H₂}‖F_y(s₁)‖²‖F_y(s₂)‖²] dh₂ dh₁ ≤ (E‖F_y(s_σ)‖²)²·e^{-2k}·Q/r`
(`RMF.integral_integral_pair_rest_le_of_hp2ExtSum_le` on short tubes). -/
theorem integral_integral_pair_rest_le_of_hp2ExtSumS_le (hX : IsRademacherPrimeValues X μ)
    {k r y : ℕ} {σ Q : ℝ} (hk : 20 ≤ k) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hσr' : 1 / 200 < σ * Real.exp ((k : ℝ) + r + 1)) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y)
    (hr : 35 ≤ r) (hQ : (r : ℝ) * hp2ExtSumS r 400 hp2ExtB 5.032 ≤ Q) :
    ∫ h₁ in halfWindow k, ∫ h₂ in halfWindow k,
        ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) ^ 2
        * Real.exp (-2 * (k : ℝ)) * Q / r := by
  refine (integral_integral_pair_rest_le_hp2ExtSumS hX hk hσr hσr' hyr hr hp2ExtB_spec
    (isRestCosBound_sat_num (-1) (hp2DeepEnd 400))).trans ?_
  set A : ℝ := (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
    (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) ^ 2
    * Real.exp (-2 * (k : ℝ)) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hS : hp2ExtSumS r 400 hp2ExtB 5.032 ≤ Q / r := by
    rw [le_div_iff₀ hr0]
    linarith
  calc A * hp2ExtSumS r 400 hp2ExtB 5.032 ≤ A * (Q / r) := mul_le_mul_of_nonneg_left hS hA0
    _ = A * Q / r := by ring

/-- **HP2's window integral per tube length**: for `k ≥ 20`, tubes of `r ≥ 35` blocks with
`σe^{k+r} ≤ 1/200 < σe^{k+r+1}` and the tilt cutoff `y ≥ c_r`,
`∫_W∫_W E[1_{H₁∩H₂}‖F_y(s₁)‖²‖F_y(s₂)‖²] dh₂ dh₁ ≤ (E‖F_y(s_σ)‖²)²·e^{-2k}·hp2QShort r/r`:
below `2000` the constant at the tube's rung (`RMF.hp2ExtSumS_le_hp2QRung`), from `2000` on
`RMF.integral_integral_pair_rest_le_two_thousand`. -/
theorem integral_integral_pair_rest_le_short (hX : IsRademacherPrimeValues X μ)
    {k r y : ℕ} {σ : ℝ} (hk : 20 ≤ k) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hσr' : 1 / 200 < σ * Real.exp ((k : ℝ) + r + 1)) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y)
    (hr : 35 ≤ r) :
    ∫ h₁ in halfWindow k, ∫ h₂ in halfWindow k,
        ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) ^ 2
        * Real.exp (-2 * (k : ℝ)) * hp2QShort r / r := by
  rcases lt_or_ge r 2000 with h2 | h2
  · rw [hp2QShort_of_lt h2]
    exact integral_integral_pair_rest_le_of_hp2ExtSumS_le hX hk hσr hσr' hyr hr
      (hp2ExtSumS_le_hp2QRung hr h2)
  · rw [hp2QShort_of_ge h2]
    exact integral_integral_pair_rest_le_two_thousand hX hk hσr hσr' hyr h2

end Pair

end RMF
