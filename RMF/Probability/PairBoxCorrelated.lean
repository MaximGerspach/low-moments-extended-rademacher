/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.BlockComparisonPair

/-!
# The two-point box mass at a correlated pair

`RMF.le_toReal_measure_box_gaussianPairLaw_envelope` bounds the Gaussian box from below only at
correlation `|ρ| ≤ 1/4`, and the block comparison built on it asks `|cov| ≤ 1/100`
(`RMF.abs_pairSlope_le_and_cs_of_abs_le`), which at block variances `≈ 1/2` is a correlation of
about `1/50`.  The two-point bound needs the pair before the two heights decorrelate, where the
correlation is `O(1)`.

Here the slope bound `ρ₀` and the first window `h₁` are parameters: at slope `ρ₀` the sheared box
only fits after the first window shrinks by `1 + 4ρ₀`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- **The box mass from below at a correlated pair**, on a product space:
`RMF.le_measure_box_pair` with the first window `h₁` a parameter and the slope bound `ρ₀` in place
of `1/4`.  The shear has to fit inside the box — `RMF.le_measure_box_shifted` asks
`2|ρ|h₁ + s·h' ≤ h₂` — which at `h₂ = h/2`, `h' = h/(4s)` is `hgeo`; the original takes
`h₁ = h/2`, which needs `|ρ| ≤ 1/4`.  At slope `ρ₀` the first window shrinks by `1 + 4ρ₀`. -/
theorem le_measure_box_pair_corr {Ω'' : Type*} [MeasurableSpace Ω'']
    {Q₁ : Measure Ω'} [IsProbabilityMeasure Q₁] {Q₂ : Measure Ω''} [IsProbabilityMeasure Q₂]
    {Z : Ω' → ℝ} {W : Ω'' → ℝ} {V₁ V₂ : ℝ≥0} (hV₁ : V₁ ≠ 0) (hV₂ : V₂ ≠ 0)
    (hZm : Measurable Z) (hWm : Measurable W)
    (hZlaw : Q₁.map Z = gaussianReal 0 V₁) (hWlaw : Q₂.map W = gaussianReal 0 V₂)
    {m₁ m₂ r s : ℝ} {N : Ω' × Ω'' → ℝ × ℝ}
    (hN : ∀ ω, N ω = (m₁ + Z ω.1, m₂ + (r * Z ω.1 + s * W ω.2)))
    (hs : 0 < s) {ρ₀ : ℝ} (hr : |r| ≤ ρ₀)
    {h h₁ C₁ C₂ c₁ c₂ : ℝ} (hh : 0 < h) (hh₁ : 0 < h₁) (hh₁h : h₁ ≤ h / 2)
    (hgeo : 2 * ρ₀ * h₁ + h / 4 ≤ h / 2)
    (hC₁ : |c₁ + h / 4 - m₁| + h₁ ≤ C₁)
    (hC₂ : |c₂ + h / 4 - m₂ + |r| * h₁ - r * (c₁ + h / 4 - m₁)| / s
      + h / (4 * s) ≤ C₂) :
    h₁ * Real.exp (-C₁ ^ 2 / (2 * V₁)) / Real.sqrt (2 * Real.pi * V₁)
        * (h / (4 * s) * Real.exp (-C₂ ^ 2 / (2 * V₂)) / Real.sqrt (2 * Real.pi * V₂))
      ≤ ((Q₁.prod Q₂) (N ⁻¹' (Set.Ioc c₁ (c₁ + h) ×ˢ Set.Ioc c₂ (c₂ + h)))).toReal := by
  -- the two coordinates, read on the product space
  have hZ'law : (Q₁.prod Q₂).map (fun ω : Ω' × Ω'' => Z ω.1) = gaussianReal 0 V₁ := by
    have hcomp : (fun ω : Ω' × Ω'' => Z ω.1) = Z ∘ Prod.fst := rfl
    rw [hcomp, ← Measure.map_map hZm measurable_fst, map_fst_prod_eq, hZlaw]
  have hW'law : (Q₁.prod Q₂).map (fun ω : Ω' × Ω'' => W ω.2) = gaussianReal 0 V₂ := by
    have hcomp : (fun ω : Ω' × Ω'' => W ω.2) = W ∘ Prod.snd := rfl
    rw [hcomp, ← Measure.map_map hWm measurable_snd, map_snd_prod_eq, hWlaw]
  have hind : IndepFun (fun ω : Ω' × Ω'' => Z ω.1) (fun ω : Ω' × Ω'' => W ω.2)
      (Q₁.prod Q₂) := indepFun_comp_fst_snd Z W
  -- the box mass from below, at the shrunken closed box
  have habs₁ := abs_nonneg (c₁ + h / 4 - m₁)
  have habs₂ := abs_nonneg (c₂ + h / 4 - m₂ + |r| * h₁ - r * (c₁ + h / 4 - m₁))
  have hle₁ := neg_abs_le (c₁ + h / 4 - m₁)
  have hle₁' := le_abs_self (c₁ + h / 4 - m₁)
  have hdiv : ∀ x : ℝ, -(|x| / s) ≤ x / s ∧ x / s ≤ |x| / s := by
    intro x
    exact ⟨by rw [← neg_div]; exact div_le_div_of_nonneg_right (neg_abs_le x) hs.le,
      div_le_div_of_nonneg_right (le_abs_self x) hs.le⟩
  obtain ⟨hd₁, hd₂⟩ := hdiv (c₂ + h / 4 - m₂ + |r| * h₁ - r * (c₁ + h / 4 - m₁))
  have hq0 : (0 : ℝ) ≤ h / (4 * s) := div_nonneg hh.le (by linarith)
  have hbox := le_measure_box_shifted (μ := Q₁.prod Q₂)
    (Z := fun ω : Ω' × Ω'' => Z ω.1) (W := fun ω : Ω' × Ω'' => W ω.2)
    hV₁ hV₂ hZ'law hW'law (by fun_prop) (by fun_prop) hind
    (m₁ := m₁) (m₂ := m₂) (ρ := r) (s := s) (u₁ := c₁ + h / 4) (h₁ := h₁)
    (v₁ := c₂ + h / 4) (h₂ := h / 2) (h' := h / (4 * s)) (c₁ := C₁) (c₂ := C₂) hs
    (by
      have hs0 : s ≠ 0 := hs.ne'
      have hsh : s * (h / (4 * s)) = h / 4 := by field_simp
      nlinarith [hr, hh, hsh, hgeo, hh₁.le, mul_le_mul_of_nonneg_right hr hh₁.le])
    (by linarith) (by linarith)
    (by linarith [hd₁, hq0]) (by linarith [hd₂, hq0])
  -- the closed box sits inside the half-open one
  have hsub : {ω : Ω' × Ω'' | m₁ + Z ω.1 ∈ Set.Icc (c₁ + h / 4) (c₁ + h / 4 + h₁)
        ∧ m₂ + (r * Z ω.1 + s * W ω.2) ∈ Set.Icc (c₂ + h / 4) (c₂ + h / 4 + h / 2)}
      ⊆ N ⁻¹' (Set.Ioc c₁ (c₁ + h) ×ˢ Set.Ioc c₂ (c₂ + h)) := by
    rintro ω ⟨h1, h2⟩
    rw [Set.mem_Icc] at h1 h2
    simp only [Set.mem_preimage, hN ω, Set.mem_prod, Set.mem_Ioc]
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩
  -- transport to `ℝ`
  have hnn₁ : (0 : ℝ)
      ≤ h₁ * Real.exp (-C₁ ^ 2 / (2 * V₁)) / Real.sqrt (2 * Real.pi * V₁) :=
    div_nonneg (mul_nonneg hh₁.le (Real.exp_pos _).le) (Real.sqrt_nonneg _)
  have hnn₂ : (0 : ℝ)
      ≤ h / (4 * s) * Real.exp (-C₂ ^ 2 / (2 * V₂)) / Real.sqrt (2 * Real.pi * V₂) :=
    div_nonneg (mul_nonneg hq0 (Real.exp_pos _).le) (Real.sqrt_nonneg _)
  have hfin := le_trans hbox (measure_mono hsub)
  have := ENNReal.toReal_mono (measure_ne_top (Q₁.prod Q₂) _) hfin
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn₁, ENNReal.toReal_ofReal hnn₂] at this

/-- **The box mass from below at a correlated pair, in law form.**
`RMF.le_toReal_measure_box_gaussianPairLaw` at the parametric window and slope. -/
lemma le_toReal_measure_box_gaussianPairLaw_corr {m₁ m₂ V₁ V₂ c ρ₀ : ℝ}
    (hV₁ : V₁.toNNReal ≠ 0)
    (hs : 0 < Real.sqrt (pairResidVar V₁ V₂ c)) (hr : |pairSlope V₁ c| ≤ ρ₀)
    {h h₁ C₁ C₂ c₁ c₂ : ℝ} (hh : 0 < h) (hh₁ : 0 < h₁) (hh₁h : h₁ ≤ h / 2)
    (hgeo : 2 * ρ₀ * h₁ + h / 4 ≤ h / 2)
    (hC₁ : |c₁ + h / 4 - m₁| + h₁ ≤ C₁)
    (hC₂ : |c₂ + h / 4 - m₂ + |pairSlope V₁ c| * h₁
          - pairSlope V₁ c * (c₁ + h / 4 - m₁)| / Real.sqrt (pairResidVar V₁ V₂ c)
        + h / (4 * Real.sqrt (pairResidVar V₁ V₂ c)) ≤ C₂) :
    h₁ * Real.exp (-C₁ ^ 2 / (2 * (V₁.toNNReal : ℝ)))
          / Real.sqrt (2 * Real.pi * (V₁.toNNReal : ℝ))
        * (h / (4 * Real.sqrt (pairResidVar V₁ V₂ c)) * Real.exp (-C₂ ^ 2 / 2)
            / Real.sqrt (2 * Real.pi))
      ≤ (gaussianPairLaw m₁ m₂ V₁ V₂ c
          (Set.Ioc c₁ (c₁ + h) ×ˢ Set.Ioc c₂ (c₂ + h))).toReal := by
  have hlaw : (gaussianPairLaw m₁ m₂ V₁ V₂ c)
        (Set.Ioc c₁ (c₁ + h) ×ˢ Set.Ioc c₂ (c₂ + h))
      = ((gaussianReal 0 V₁.toNNReal).prod (gaussianReal 0 1))
          ((fun z : ℝ × ℝ => (m₁ + z.1, m₂ + pairSlope V₁ c * z.1
              + Real.sqrt (pairResidVar V₁ V₂ c) * z.2))
            ⁻¹' (Set.Ioc c₁ (c₁ + h) ×ˢ Set.Ioc c₂ (c₂ + h))) := by
    rw [gaussianPairLaw, Measure.map_apply (measurable_gaussianPairMap m₁ m₂ V₁ V₂ c)
      (measurableSet_Ioc.prod measurableSet_Ioc)]
  rw [hlaw]
  have hbox := le_measure_box_pair_corr (Q₁ := gaussianReal 0 V₁.toNNReal)
    (Q₂ := gaussianReal 0 1) (Z := id) (W := id) (V₁ := V₁.toNNReal) (V₂ := 1)
    (m₁ := m₁) (m₂ := m₂) (r := pairSlope V₁ c) (s := Real.sqrt (pairResidVar V₁ V₂ c))
    (N := fun z : ℝ × ℝ => (m₁ + z.1, m₂ + pairSlope V₁ c * z.1
      + Real.sqrt (pairResidVar V₁ V₂ c) * z.2))
    (h := h) (h₁ := h₁) (C₁ := C₁) (C₂ := C₂) (c₁ := c₁) (c₂ := c₂)
    hV₁ one_ne_zero measurable_id measurable_id Measure.map_id Measure.map_id
    (fun ω => Prod.ext rfl (by simp only [id_eq]; ring)) hs hr hh hh₁ hh₁h hgeo hC₁ hC₂
  simpa using hbox

end RMF
