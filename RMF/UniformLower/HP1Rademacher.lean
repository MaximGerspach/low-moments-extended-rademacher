/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.GaussianHP1Main
import RMF.UniformLower.WindowBlockData
import RMF.Probability.RademacherBoxComparisonDecay

/-!
# The window's first moment, Rademacher side: the block data

Under the tilt by `|F_y(½+σ+ih)|²`, the blocks at offset `k` of the height walk (at `½+σ+ih`) and
the real walk (at `½+σ`) have named data (`RMF.windowMeanH`, `RMF.windowVarH`, `RMF.windowResid`,
…), whose closed forms are in `RMF/UniformLower/WindowBlockData.lean`; and the height walk is
re-centred by its means (`RMF.barrierEventPair_subset_of_add_fst`).  The window's first moment,
Rademacher side, is `RMF.le_measure_windowEvent_rademacher_floor`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The window's block data, named -/

/-- The height block's tilted mean `μ̃_m(h)`: block `m` at offset `k` of `log|F(½+σ+ih)|`, under the
tilt by `|F_y(½+σ+ih)|²`. -/
noncomputable def windowMeanH (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k : ℕ) (σ h : ℝ) (m : ℕ) : ℝ :=
  blockMeanAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
    (primeBlockSub k m)

/-- The real block's tilted mean `d_m`: block `m` of `log|F(½+σ)|` under the same tilt. -/
noncomputable def windowMeanR (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k : ℕ) (σ h : ℝ) (m : ℕ) : ℝ :=
  blockMeanAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0)))
    (primeBlockSub k m)

/-- The height block's matched variance `V¹_m` under the tilt. -/
noncomputable def windowVarH (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k : ℕ) (σ h : ℝ) (m : ℕ) : ℝ :=
  ((blockMatchedVarAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
    (primeBlockSub k m) : ℝ≥0) : ℝ)

/-- The real block's matched variance `V²_m` under the tilt. -/
noncomputable def windowVarR (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k : ℕ) (σ h : ℝ) (m : ℕ) : ℝ :=
  ((blockMatchedVarAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0)))
    (primeBlockSub k m) : ℝ≥0) : ℝ)

/-- The covariance `κ_m` of the height and the real block under the tilt. -/
noncomputable def windowCov (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k : ℕ) (σ h : ℝ) (m : ℕ) : ℝ :=
  blockMatchedCovAddT X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
    (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m)

/-- The regression slope `β_m = κ_m/V¹_m` of the real block on the height block. -/
noncomputable def windowSlope (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k : ℕ) (σ h : ℝ) (m : ℕ) : ℝ :=
  pairSlope (windowVarH X μ y k σ h m) (windowCov X μ y k σ h m)

/-- The residual variance `R_m = V²_m − κ_m²/V¹_m` of the real block given the height block. -/
noncomputable def windowResid (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k : ℕ) (σ h : ℝ) (m : ℕ) : ℝ :=
  pairResidVar (windowVarH X μ y k σ h m) (windowVarR X μ y k σ h m) (windowCov X μ y k σ h m)

omit [MeasurableSpace Ω] in
/-- **Re-centring the first walk of a pair.**  If below `n` the family `N` is `L` with the
deterministic increments `c m` added to the first coordinate, the pair barrier for `L` lies in the
one for `N` whose first tube is moved by the partial sums of `c` (and whose tubes are wider). -/
lemma barrierEventPair_subset_of_add_fst {L N : ℕ → Ω → ℝ × ℝ} {c : ℕ → ℝ} {n : ℕ}
    {u₁ v₁ u₂ v₂ u₁' v₁' u₂' v₂' : ℕ → ℝ}
    (h₁ : ∀ m, m < n → ∀ ω, (N m ω).1 = c m + (L m ω).1)
    (h₂ : ∀ m, m < n → ∀ ω, (N m ω).2 = (L m ω).2)
    (hu₁ : ∀ j, 1 ≤ j → j ≤ n → u₁' j ≤ ∑ i ∈ Finset.range j, c i + u₁ j)
    (hv₁ : ∀ j, 1 ≤ j → j ≤ n → ∑ i ∈ Finset.range j, c i + v₁ j ≤ v₁' j)
    (hu₂ : ∀ j, 1 ≤ j → j ≤ n → u₂' j ≤ u₂ j) (hv₂ : ∀ j, 1 ≤ j → j ≤ n → v₂ j ≤ v₂' j) :
    barrierEventPair L n u₁ v₁ u₂ v₂ ⊆ barrierEventPair N n u₁' v₁' u₂' v₂' := by
  rintro ω ⟨hL₁, hL₂⟩
  refine ⟨fun j hj1 hjn => ?_, fun j hj1 hjn => ?_⟩
  · have hw : walk (fun m ω => (N m ω).1) j ω
        = ∑ i ∈ Finset.range j, c i + walk (fun m ω => (L m ω).1) j ω := by
      rw [walk_apply, walk_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i hi => h₁ i (by have := Finset.mem_range.1 hi; omega) ω
    have hb := Set.mem_Icc.1 (hL₁ j hj1 hjn)
    rw [Set.mem_Icc, hw]
    exact ⟨by linarith [hu₁ j hj1 hjn, hb.1], by linarith [hv₁ j hj1 hjn, hb.2]⟩
  · have hw : walk (fun m ω => (N m ω).2) j ω = walk (fun m ω => (L m ω).2) j ω := by
      rw [walk_apply, walk_apply]
      exact Finset.sum_congr rfl fun i hi => h₂ i (by have := Finset.mem_range.1 hi; omega) ω
    have hb := Set.mem_Icc.1 (hL₂ j hj1 hjn)
    rw [Set.mem_Icc, hw]
    exact ⟨le_trans (hu₂ j hj1 hjn) hb.1, le_trans hb.2 (hv₂ j hj1 hjn)⟩

variable {X : ℕ → Ω → ℂ} {μ : Measure Ω}

end RMF
