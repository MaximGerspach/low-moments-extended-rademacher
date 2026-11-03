/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.C3Numerals.Table
import RMF.UniformLower.C3LadderOne

/-!
# (C3)*'s numerals for the ladder of length one: the generic rows

What turns `RMF.c3ValOne` (`RMF/UniformLower/C3LadderOne.lean`) into certified numerals at the
damping `η = 1/200` and the smoothing `δ = 10⁻⁴`: one rational side condition per certificate
(`RMF.le_c3ValOne_of_num`), and (C3)* for the ladder of length one from such a bound on a cell
of heights (`RMF.le_setIntegral_halfLadder_twistQ_one_of_le`).
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-- **One row for the ladder of length one**: `c ≤ c3ValOne q_lo (1/200) ϑ_lo 10⁻⁴` from the
cosine anchor `A_lo`, `ml ≤ topMuLo` (`RMF.topMuLo_ge_of`), `z₁ ≤ (ml - δ)/√V` over the
variance's range, `Φ(z₁) ≥ p₁` and `c ≤ p₁ - 10⁻¹⁸`. -/
theorem le_c3ValOne_of_num {q_lo ϑ_lo Alo ml z₁ p₁ c : ℝ}
    (hAlo : Alo ≤ cosExpAnti (-ϑ_lo) - cosExpAnti (-1 - ϑ_lo)) (hp₁ : p₁ ≤ normCDF z₁)
    (hnum : (ml + 2 * ((1 + 1 / 150000) - (Alo - 1 / 10 ^ 6) + 7.43 / 10 ^ 8)
          + 14 * (2 / 10 ^ 40) ≤ (2 * q_lo - 1 / 2) * 0.9900432333
        ∧ ml + 2 * ((1 + 1 / 150000) - (Alo - 1 / 10 ^ 6) + 7.43 / 10 ^ 8)
          + 14 * (2 / 10 ^ 40) ≤ (2 * q_lo - 1 / 2) * (1 + 1 / 150000))
      ∧ ((z₁ ≤ 0 ∧ 0 ≤ ml - 1 / 10 ^ 4)
        ∨ (z₁ ≤ 0 ∧ ml - 1 / 10 ^ 4 ≤ 0 ∧ (ml - 1 / 10 ^ 4) ^ 2 ≤ z₁ ^ 2 * 0.9900432332)
        ∨ (0 ≤ z₁ ∧ 0 ≤ ml - 1 / 10 ^ 4 ∧ z₁ ^ 2 * 1.0000066667 ≤ (ml - 1 / 10 ^ 4) ^ 2))
      ∧ c ≤ p₁ - 1 / 10 ^ 18) :
    c ≤ c3ValOne q_lo (1 / 200) ϑ_lo (1 / 10 ^ 4) := by
  obtain ⟨⟨hml₁, hml₂⟩, hz₁, hc⟩ := hnum
  obtain ⟨hVL1, hVL2⟩ := topVLo_two_hundredth_mem
  obtain ⟨hVH1, hVH2⟩ := topVHi_mem
  have hVL0 : 0 < topVLo (1 / 200) := by linarith
  have hVH0 : 0 < topVHi := by linarith
  have hμlo : ml ≤ topMuLo q_lo (1 / 200) ϑ_lo := topMuLo_ge_of hAlo hml₁ hml₂
  have hm : ml - 1 / 10 ^ 4 ≤ topMuLo q_lo (1 / 200) ϑ_lo - 1 / 10 ^ 4 := by linarith
  have h1 : p₁ ≤ min (normCDF ((topMuLo q_lo (1 / 200) ϑ_lo - 1 / 10 ^ 4) / √(topVLo (1 / 200))))
      (normCDF ((topMuLo q_lo (1 / 200) ϑ_lo - 1 / 10 ^ 4) / √topVHi)) :=
    le_min (hp₁.trans (normCDF_mono (le_div_sqrt_of_cases hVL0 hVL1 (by linarith) hm hz₁)))
      (hp₁.trans (normCDF_mono (le_div_sqrt_of_cases hVH0 (by linarith) hVH2 hm hz₁)))
  have h2 := lindebergErr_le (t := 0) (F := 0) le_rfl (by norm_num) le_rfl (by norm_num)
  rw [c3ValOne]
  linarith

section Window

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **(C3)* for the ladder of length one, from a certified bound**: for `k - k₁ = 1`,
`k₁ ≥ 20`, `σe^k ≤ 1/200`, `0 ≤ q_lo ≤ q ≤ 1`, `c ≤ c3ValOne q_lo (1/200) ϑ_lo 10⁻⁴` and a height
`e^{-(k+ϑ_hi)} ≤ h ≤ e^{-(k+ϑ_lo)}`, `ϑ_lo ≥ 0`:
`c·E‖F_{[a,k)}(σ)‖^{2q} ≤ E[1_{halfLadder X σ k₁ k}‖F_{[a,k)}(s_h)‖²‖F_{[a,k)}(σ)‖^{2q-2}]`. -/
theorem le_setIntegral_halfLadder_twistQ_one_of_le (hX : IsRademacherPrimeValues X μ)
    {a k₁ k : ℕ} (ha : a ≤ scaleCut (k₁ : ℝ)) (hk₁ : 20 ≤ k₁) (hK : k - k₁ = 1) {σ : ℝ}
    (hσ : 0 ≤ σ) (hση : σ * Real.exp k ≤ 1 / 200) {q q_lo c : ℝ} (hqlo : q_lo ≤ q)
    (hq0 : 0 ≤ q_lo) (hq1 : q ≤ 1) {ϑ_lo ϑ_hi : ℝ} (hϑ : 0 ≤ ϑ_lo)
    (hc : c ≤ c3ValOne q_lo (1 / 200) ϑ_lo (1 / 10 ^ 4)) {h : ℝ}
    (hh1 : Real.exp (-((k : ℝ) + ϑ_hi)) ≤ h) (hh2 : h ≤ Real.exp (-((k : ℝ) + ϑ_lo))) :
    c * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
          (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω in halfLadder X σ k₁ k,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ := by
  have hmain := le_setIntegral_halfLadder_twistQ_one hX ha hk₁ hK hσ hση (by norm_num) hqlo hq0
    hq1 (by norm_num : (0 : ℝ) < 1 / 10 ^ 4) hϑ hh1 hh2
  have hE0 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
      (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  exact (mul_le_mul_of_nonneg_right hc hE0).trans hmain

end Window

end RMF
