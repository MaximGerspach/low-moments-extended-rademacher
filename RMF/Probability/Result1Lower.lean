/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.GaussianWalk

/-!
# Probability Result 1, lower half, as a property of its constants

`RMF.Result1Lower v₋ v₊ R α` says that every Gaussian walk with variances in `[v₋, v₊]` satisfies
the lower half of Harper's Probability Result 1 from the level `R` on, with the constant `α`:

`α · min{1, a/√n} ≤ P(S_j ≤ a + h(j) ∀ 1 ≤ j ≤ n)`

for every `a ≥ R`, every `h` with `h(j) ≥ -10 log j`, and every walk length `n ≥ 1` with
`2(log n)²⁰ ≤ n` and `2(log n)⁸ ≤ nv₋`.  `RMF.Result1LowerOn` is the same for one walk.

The iterated-logarithm induction supplies it, `RMF.result1Lower_iteratedLog`, at
`RMF.result1Threshold` and `RMF.result1LowerConst`.  The lower chain takes it as a hypothesis, as
the averaged free start takes `RMF.Result1Affine` for the upper half.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

universe u

section On

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Probability Result 1, lower half, for one walk**, from the level `R` with the constant
`α`. -/
def Result1LowerOn (G : ℕ → Ω → ℝ) (μ : Measure Ω) (vmin R α : ℝ) : Prop :=
  ∀ a : ℝ, R ≤ a → ∀ n : ℕ, 1 ≤ n →
    2 * Real.log n ^ 20 ≤ (n : ℝ) → 2 * Real.log n ^ 8 ≤ (n : ℝ) * vmin →
    ∀ hf : ℕ → ℝ, (∀ j, 1 ≤ j → j ≤ n → -(10 * Real.log j) ≤ hf j) →
      α * min 1 (a / Real.sqrt n)
        ≤ (μ {ω | ∀ j, 1 ≤ j → j ≤ n → walk G j ω ≤ a + hf j}).toReal

end On

/-- **Probability Result 1, lower half, from the level `R` with the constant `α`**, for every
Gaussian walk with variances in `[v₋, v₊]` on a space in the universe `u`. -/
def Result1Lower (vmin vmax R α : ℝ) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (G : ℕ → Ω → ℝ)
    (v : ℕ → ℝ≥0), IsGaussianWalk G v μ → VarBracket v vmin vmax → Result1LowerOn G μ vmin R α

/-- The property at one walk. -/
lemma Result1Lower.on {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {vmin vmax R α : ℝ} (h : Result1Lower.{u} vmin vmax R α)
    (hG : IsGaussianWalk G v μ) (hv : VarBracket v vmin vmax) : Result1LowerOn G μ vmin R α :=
  h Ω μ G v hG hv

end RMF
