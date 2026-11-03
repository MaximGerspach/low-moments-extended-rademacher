/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2WindowExtNum

/-!
# HP2's window integral with the primes above block `r`

For `k ≥ 20`, `r ≥ 2000` maximal for the damping, `σe^{k+r} ≤ 1/200 < σe^{k+r+1}`, a tilt cutoff
`y` above block `r` and `F_y` the Euler product over every prime from the start of block `0` (at
offset `k`) up to `y`:
`∫_W∫_W E[1_{H(k,h₁)∩H(k,h₂)}‖F_y(s₁)‖²‖F_y(s₂)‖²] dh₂ dh₁ ≤ (E‖F_y(s_σ)‖²)²·e^{-2k}·Q₂''/r`,
`W = halfWindow k`, `H = RMF.hp1Tube`, with `Q₂'' = 6482`
(`RMF.integral_integral_pair_rest_le_two_thousand`).  The normalisation
`E‖F_y(s_h)‖² = ∏_{c₀≤p<y}(1 + p^{-1-2σ})` does not depend on `h`
(`RMF.integral_normSq_Ico_eq_prod`).  The primes above block `r` are called the rest.

* `RMF/UniformLower/HP2WindowExt/Taylor.lean`, `Lobe.lean`: the rest's damped cosine integral
  `∫_A^U cos(τu)e^{-2σu}/u du`, uniformly in `U`, and its cells `RMF.IsRestCosBound`;
* `RMF/UniformLower/HP2WindowExt/Rest.lean`: the primes of `[c_r, y)` factor out of the pair
  moment with the exponent `2∫_{e^{k+r}}^U cos(|h₁ - h₂|u)e^{-2σu}/u du + 10⁻¹⁹` (partial top
  block by the PNT);
* `RMF/UniformLower/HP2WindowExt/Step.lean`, `Regions.lean`: the cells and regions of
  `RMF/UniformLower/HP2Window/` with the rest's factor per cell,
  `∫∫ ≤ (E‖F_y(s_σ)‖²)²e^{-2k}·RMF.hp2ExtSum r N B B_sat`;
* `RMF/UniformLower/HP2WindowExt/Cells.lean` and `RMF/UniformLower/HP2WindowExtNum/`: the deep
  cells' bounds.
-/

open MeasureTheory ProbabilityTheory Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The window's pair integral with the rest from a bound on `r·hp2ExtSum`**: for `k ≥ 20`,
`σe^{k+r} ≤ 1/200 < σe^{k+r+1}`, `y ≥ c_r`, `r ≥ 2000` and `r·hp2ExtSum r 400 hp2ExtB 5.032 ≤ Q`,
`∫_W∫_W E[1_{H₁∩H₂}‖F_y(s₁)‖²‖F_y(s₂)‖²] dh₂ dh₁ ≤ (E‖F_y(s_σ)‖²)²·e^{-2k}·Q/r`. -/
theorem integral_integral_pair_rest_le_of_hp2ExtSum_le (hX : IsRademacherPrimeValues X μ)
    {k r y : ℕ} {σ Q : ℝ} (hk : 20 ≤ k) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hσr' : 1 / 200 < σ * Real.exp ((k : ℝ) + r + 1)) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y)
    (hr : 2000 ≤ r) (hQ : (r : ℝ) * hp2ExtSum r 400 hp2ExtB 5.032 ≤ Q) :
    ∫ h₁ in halfWindow k, ∫ h₂ in halfWindow k,
        ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) ^ 2
        * Real.exp (-2 * (k : ℝ)) * Q / r := by
  refine (integral_integral_pair_rest_le_hp2ExtSum hX hk hσr hσr' hyr hr hp2ExtB_spec
    (isRestCosBound_sat_num (-1) (hp2DeepEnd 400))).trans ?_
  set A : ℝ := (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
    (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) ^ 2
    * Real.exp (-2 * (k : ℝ)) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hS : hp2ExtSum r 400 hp2ExtB 5.032 ≤ Q / r := by
    rw [le_div_iff₀ hr0]
    linarith
  calc A * hp2ExtSum r 400 hp2ExtB 5.032 ≤ A * (Q / r) := mul_le_mul_of_nonneg_left hS hA0
    _ = A * Q / r := by ring

/-- **HP2's window integral with the primes above block `r`, `r ≥ 2000`**: for
`k ≥ 20`, `σe^{k+r} ≤ 1/200 < σe^{k+r+1}` and the tilt cutoff `y ≥ c_r`,
`∫_W∫_W E[1_{H₁∩H₂}‖F_y(s₁)‖²‖F_y(s₂)‖²] dh₂ dh₁ ≤ (E‖F_y(s_σ)‖²)²·e^{-2k}·6482/r`. -/
theorem integral_integral_pair_rest_le_two_thousand (hX : IsRademacherPrimeValues X μ)
    {k r y : ℕ} {σ : ℝ} (hk : 20 ≤ k) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hσr' : 1 / 200 < σ * Real.exp ((k : ℝ) + r + 1)) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y)
    (hr : 2000 ≤ r) :
    ∫ h₁ in halfWindow k, ∫ h₂ in halfWindow k,
        ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) ^ 2
        * Real.exp (-2 * (k : ℝ)) * 6482 / r :=
  integral_integral_pair_rest_le_of_hp2ExtSum_le hX hk hσr hσr' hyr hr
    (hp2ExtSum_le_two_thousand hr)

end RMF
