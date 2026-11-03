/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.PropBDiffExplicit
import RMF.Weighted.BandChaosWindowExplicit

/-!
# One level of the hierarchy above `q = ½`, explicit

The truncation bound in difference form (`RMF.integral_rpow_norm_blockTruncationTail_le_explicit`)
with its line functional split (`RMF.integral_rpow_bandDiffLine_le_split`), the windows' moments
entering through bounds `w k` supplied one window at a time (split and Jensen, no split, or the
chaos):

`E|𝒯_{y,z}(x)|^{2q} ≤ E|T(x)|^{2q} + (Kη/log z)^q P
  + (Ke^{2c_L})^q(Cen^q P + Coh^q P + (1+η′)^q(∑_k w_k + Far^q)) + E_err^q`

(`RMF.integral_rpow_norm_blockTruncationTail_le_split`), `P = E‖F_{y,z}(½)‖^{2q}`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **One level, split.**  For `½ ≤ q ≤ 1` and the hypotheses of the truncation bound in
difference form (`RMF.integral_rpow_norm_blockTruncationTail_le_explicit`), `η′ > 0`, a real `c`,
`k₀ ≤ J`, `M` bounding the band's second moment on the line and bounds `w k` on the windows'
moments:

`E|𝒯_{y,z}(x)|^{2q} ≤ E|T(x)|^{2q} + (Kη/log z)^q P
  + (Ke^{2c_L})^q(Cen^q P + Coh^q P + (1+η′)^q(∑_{k₀≤k<J} w_k + Far^q)) + E_err^q`,

`L = 2π log z`, `τ = e^{c-J}`, `T = e^{c-k₀}`, `Cen = ∫_{-τ}^{τ}L⁻¹(σ²+t²)⁻¹Q`,
`Coh = (1+1/η′)(2/τ)L⁻¹`, `Far = L⁻¹(2/T)M`. -/
theorem integral_rpow_norm_blockTruncationTail_le_split {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y z z' : ℕ} (hyz : y ≤ z) (hz' : 2 ≤ z')
    (hz'z : z' ≤ z) {σ x η ε cL q η' c M : ℝ} {k₀ J : ℕ} {w : ℕ → ℝ} (hzx : (z : ℝ) ≤ x)
    (hσ : 0 < σ) (hσlog : σ * Real.log (x / z) ≤ cL) (hη : 0 < η) (hzη : 1 + η < z)
    (hε : 0 < ε) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hη' : 0 < η') (hk₀J : k₀ ≤ J)
    (hM : ∀ t : ℝ, (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (y + 1) (z + 1) ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ) ≤ M)
    (hw : ∀ k ∈ Finset.Ico k₀ J, (2 / (2 * Real.pi * Real.log z)) ^ q
        * (∫ ω, (∫ t in Set.Icc (Real.exp (c - k) / Real.exp 1) (Real.exp (c - k)),
          (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1) (shiftLine σ t)
              ω‖ ^ 2) ^ q ∂μ) ≤ w k) :
    (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
        ^ (2 * q) ∂μ)
      ≤ (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ (2 * q) ∂μ)
        + (lemmaTConst z z' η ε * (η / Real.log z)) ^ q
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
        + (lemmaTConst z z' η ε * Real.exp (2 * cL)) ^ q
          * ((∫ t in Set.Icc (-Real.exp (c - J)) (Real.exp (c - J)),
                (2 * Real.pi * Real.log z)⁻¹ * (σ ^ 2 + t ^ 2)⁻¹
                  * diffQ (y + 1) (z + 1) q σ t) ^ q
              * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (y + 1) (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
            + ((1 + 1 / η') * (2 / Real.exp (c - J)) * (2 * Real.pi * Real.log z)⁻¹) ^ q
              * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (y + 1) (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
            + (1 + η') ^ q * (∑ k ∈ Finset.Ico k₀ J, w k
              + ((2 * Real.pi * Real.log z)⁻¹ * ((2 / Real.exp (c - k₀)) * M)) ^ q))
        + smallQReductionErr x z' η ε ^ q := by
  have hz2 : (2 : ℕ) ≤ z := le_trans hz' hz'z
  have hLT := integral_rpow_norm_blockTruncationTail_le_explicit hX hyz hz' hz'z hzx hσ hσlog
    hη hzη hε (by linarith) hq1
  have hPB := integral_rpow_bandDiffLine_le_split hX y z hz2 (c := c) hq0 hq1 hσ hη' hk₀J hM
  -- the windows by their bounds
  have hsum : (2 / (2 * Real.pi * Real.log z)) ^ q * ∑ k ∈ Finset.Ico k₀ J,
      ∫ ω, (∫ t in Set.Icc (Real.exp (c - k) / Real.exp 1) (Real.exp (c - k)),
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1) (shiftLine σ t)
            ω‖ ^ 2) ^ q ∂μ
      ≤ ∑ k ∈ Finset.Ico k₀ J, w k := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hw
  have hη'1 : (0 : ℝ) ≤ (1 + η') ^ q := Real.rpow_nonneg (by linarith) _
  have hwin : (1 + η') ^ q * ((2 / (2 * Real.pi * Real.log z)) ^ q * ∑ k ∈ Finset.Ico k₀ J,
      ∫ ω, (∫ t in Set.Icc (Real.exp (c - k) / Real.exp 1) (Real.exp (c - k)),
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1) (shiftLine σ t)
            ω‖ ^ 2) ^ q ∂μ)
      + (1 + η') ^ q * ((2 * Real.pi * Real.log z)⁻¹ * ((2 / Real.exp (c - k₀)) * M)) ^ q
      ≤ (1 + η') ^ q * (∑ k ∈ Finset.Ico k₀ J, w k
        + ((2 * Real.pi * Real.log z)⁻¹ * ((2 / Real.exp (c - k₀)) * M)) ^ q) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (add_le_add hsum le_rfl) hη'1
  have hPB' : (∫ ω, bandDiffLine (fun ω => squarefreeExtension fun p => X p ω) y z σ ω ^ q ∂μ)
      ≤ (∫ t in Set.Icc (-Real.exp (c - J)) (Real.exp (c - J)),
            (2 * Real.pi * Real.log z)⁻¹ * (σ ^ 2 + t ^ 2)⁻¹
              * diffQ (y + 1) (z + 1) q σ t) ^ q
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (y + 1) (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
        + ((1 + 1 / η') * (2 / Real.exp (c - J)) * (2 * Real.pi * Real.log z)⁻¹) ^ q
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (y + 1) (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
        + (1 + η') ^ q * (∑ k ∈ Finset.Ico k₀ J, w k
          + ((2 * Real.pi * Real.log z)⁻¹ * ((2 / Real.exp (c - k₀)) * M)) ^ q) := by
    linarith [hPB, hwin]
  have hK0 : 0 ≤ (lemmaTConst z z' η ε * Real.exp (2 * cL)) ^ q :=
    Real.rpow_nonneg (mul_nonneg (lemmaTConst_pos hz' hz'z hη hε).le (Real.exp_pos _).le) _
  have hmul := mul_le_mul_of_nonneg_left hPB' hK0
  linarith

end RMF
