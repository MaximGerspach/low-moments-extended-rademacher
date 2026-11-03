/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.HarperChain
import RMF.Probability.CurvedBarrierSharp

/-!
# The two losses of the one-point chaos bound

The one-point chaos bound reads `Γ(s) ≥ P(max W ≤ z) - L_cap - L_low`: the two-sided capped
barrier event is the one-sided event minus the paths that break the ceiling and those that break
the floor.

`RMF.measure_le_barrierEvent_add_breaches` is that decomposition, and it is purely
set-theoretic — a path of the one-sided event that breaks neither barrier lies in the barrier
event, so monotonicity and subadditivity suffice, with no measurability hypothesis.

## Main results

* `RMF.ceilBreach`, `RMF.floorBreach`
* `RMF.measure_le_barrierEvent_add_breaches`
-/

open MeasureTheory ProbabilityTheory
open scoped Real NNReal ENNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}
variable {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}

/-- The paths that break the ceiling somewhere on `[1, n]`. -/
def ceilBreach (X : ℕ → Ω → ℝ) (n : ℕ) (hi : ℕ → ℝ) : Set Ω :=
  {ω | ∃ j, 1 ≤ j ∧ j ≤ n ∧ hi j < walk X j ω}

/-- The paths that break the floor somewhere on `[1, n]`. -/
def floorBreach (X : ℕ → Ω → ℝ) (n : ℕ) (lo : ℕ → ℝ) : Set Ω :=
  {ω | ∃ j, 1 ≤ j ∧ j ≤ n ∧ walk X j ω < lo j}

/-- **Any event is covered by the barrier event and its two breaches.**  This is the shape
`Γ ≥ P(max W ≤ z) - L_cap - L_low` of the one-point chaos bound, with `A` the one-sided event
`{max W ≤ z}`, `L_cap` the cap loss and `L_low` the lower-barrier loss.

Set-theoretic: if a path of `A` breaks neither barrier it lies in the barrier event.  No
measurability is needed — monotonicity and subadditivity suffice. -/
theorem measure_le_barrierEvent_add_breaches (X : ℕ → Ω → ℝ) (n : ℕ) (lo hi : ℕ → ℝ)
    (A : Set Ω) :
    μ A ≤ μ (barrierEvent X n lo hi) + μ (A ∩ ceilBreach X n hi)
      + μ (A ∩ floorBreach X n lo) := by
  have hcover : A ⊆ barrierEvent X n lo hi ∪ (A ∩ ceilBreach X n hi)
      ∪ (A ∩ floorBreach X n lo) := by
    intro ω hω
    by_cases hc : ω ∈ ceilBreach X n hi
    · exact Or.inl (Or.inr ⟨hω, hc⟩)
    by_cases hf : ω ∈ floorBreach X n lo
    · exact Or.inr ⟨hω, hf⟩
    refine Or.inl (Or.inl ?_)
    intro j hj1 hjn
    refine Set.mem_Icc.2 ⟨?_, ?_⟩
    · by_contra hcon
      exact hf ⟨j, hj1, hjn, lt_of_not_ge hcon⟩
    · by_contra hcon
      exact hc ⟨j, hj1, hjn, lt_of_not_ge hcon⟩
  calc μ A ≤ μ (barrierEvent X n lo hi ∪ (A ∩ ceilBreach X n hi)
        ∪ (A ∩ floorBreach X n lo)) := measure_mono hcover
    _ ≤ μ (barrierEvent X n lo hi ∪ (A ∩ ceilBreach X n hi))
        + μ (A ∩ floorBreach X n lo) := measure_union_le _ _
    _ ≤ μ (barrierEvent X n lo hi) + μ (A ∩ ceilBreach X n hi)
        + μ (A ∩ floorBreach X n lo) := by
        gcongr
        exact measure_union_le _ _

end RMF
