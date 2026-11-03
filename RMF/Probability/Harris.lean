/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.GaussianHP1

/-!
# Integrals over a finite product of probability measures on `ℝ`

Three helpers for integrals against `Measure.pi μ`, each `μ i` a probability measure on `ℝ`: a
bounded measurable function is integrable (`RMF.integrable_of_measurable_of_abs_le`),
`(t, y) ↦ Fin.cons t y` is measurable (`RMF.measurable_finCons_real`), and the integral splits off
the first coordinate (`RMF.integral_pi_succ_eq`).
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-- A bounded measurable real function is integrable against a finite measure. -/
lemma integrable_of_measurable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {F : α → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- `(t, y) ↦ Fin.cons t y` is measurable. -/
lemma measurable_finCons_real {n : ℕ} :
    Measurable fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ) := by
  refine measurable_pi_iff.2 fun i => ?_
  induction i using Fin.cases with
  | zero => simpa using measurable_fst
  | succ j =>
    simp only [Fin.cons_succ]
    exact (measurable_pi_apply j).comp measurable_snd

/-- **Splitting off the first coordinate** of a finite product of probability measures on `ℝ`. -/
lemma integral_pi_succ_eq {n : ℕ} (μ : Fin (n + 1) → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {F : (Fin (n + 1) → ℝ) → ℝ} (hF : Integrable F (Measure.pi μ)) :
    ∫ x, F x ∂(Measure.pi μ)
      = ∫ t, ∫ y, F (Fin.cons t y) ∂(Measure.pi fun j : Fin n => μ j.succ) ∂(μ 0) := by
  have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
  rw [← hmp.integral_comp', integral_prod]
  · simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
      Fin.zero_succAbove]
    rfl
  · exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF

end RMF
