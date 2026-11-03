/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.FreeStartAveraged
import RMF.Probability.HarperChain

/-!
# Tonelli through independence

`RMF.lintegral_prod_map_of_indepFun` is the weighted twin of
`RMF.measure_preimage_prod_eq_lintegral`: independence turns the joint law of a pair into the
product of the laws, and Tonelli splits a lower integral of a function of the pair.  It is the
engine of `RMF.lintegral_eq_lintegral_lintegral_of_indepFun`, which freezes one argument by
independence.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

namespace RMF

section StartFibreWeighted

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Tonelli through independence.**  The weighted twin of
`RMF.measure_preimage_prod_eq_lintegral`: for independent `Φ`, `Ψ` the joint law is the product
of the laws, so a lower integral of a function of the pair splits. -/
lemma lintegral_prod_map_of_indepFun {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] {Φ : Ω → α} {Ψ : Ω → β}
    (hΦ : Measurable Φ) (hΨ : Measurable Ψ) (hind : IndepFun Φ Ψ P)
    {F : α × β → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, F (Φ ω, Ψ ω) ∂P) = ∫⁻ x, ∫⁻ y, F (x, y) ∂(P.map Ψ) ∂(P.map Φ) := by
  rw [← lintegral_map hF (hΦ.prodMk hΨ),
    hind.map_prod_eq_prod_map_map hΦ.aemeasurable hΨ.aemeasurable,
    lintegral_prod _ hF.aemeasurable]

end StartFibreWeighted

end RMF
