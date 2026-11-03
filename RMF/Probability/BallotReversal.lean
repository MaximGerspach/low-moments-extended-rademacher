/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.CurvedBarrierSharp

/-!
# Time reversal of a Gaussian walk

`RMF.revIdx M` reverses the indices below `M`.  `RMF.walk_reverse`: the walk of the reversed,
negated increments `-G(M-1), -G(M-2), …` is `S_{M-i} - S_M`; and `RMF.IsGaussianWalk.reverse`: it
is again a Gaussian walk.  This lets a barrier estimate be applied to the last steps of a walk,
read backwards.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*}

/-- The reversal of `[0, M)`: `m ↦ M - 1 - m` below `M`, the identity from `M` on. -/
def revIdx (M m : ℕ) : ℕ := if m < M then M - 1 - m else m

lemma revIdx_injective (M : ℕ) : Function.Injective (revIdx M) := by
  intro a b hab
  unfold revIdx at hab
  split_ifs at hab with ha hb hb <;> omega

/-- **The reversed walk**: the walk of the increments `-G(M-1), -G(M-2), …` is `S_{M-i} - S_M`. -/
lemma walk_reverse (G : ℕ → Ω → ℝ) {M i : ℕ} (hi : i ≤ M) (ω : Ω) :
    walk (fun m => -G (revIdx M m)) i ω = walk G (M - i) ω - walk G M ω := by
  simp only [walk_apply, Pi.neg_apply, Finset.sum_neg_distrib]
  have h1 : ∑ m ∈ Finset.range i, G (revIdx M m) ω = ∑ m ∈ Finset.range i, G (M - i + m) ω := by
    rw [← Finset.sum_range_reflect (fun m => G (M - i + m) ω) i]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.1 hm
    have hidx : revIdx M m = M - i + (i - 1 - m) := by
      unfold revIdx
      rw [if_pos (by omega)]
      omega
    simp only [hidx]
  have hsplit : ∑ m ∈ Finset.range M, G m ω
      = ∑ m ∈ Finset.range (M - i), G m ω + ∑ m ∈ Finset.range i, G (M - i + m) ω := by
    rw [← Finset.sum_range_add (fun m => G m ω) (M - i) i, Nat.sub_add_cancel hi]
  rw [h1, hsplit]
  ring

variable [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}

/-- The negated increments of `[0, M)` in reverse order, then the rest, form a Gaussian walk. -/
lemma IsGaussianWalk.reverse (h : IsGaussianWalk G v μ) (M : ℕ) :
    IsGaussianWalk (fun m => -G (revIdx M m)) (fun m => v (revIdx M m)) μ :=
  IsGaussianWalk.neg
    { measurable := fun m => h.measurable (revIdx M m)
      indep := h.indep.precomp (revIdx_injective M)
      map_eq := fun m => h.map_eq (revIdx M m) }

end RMF
