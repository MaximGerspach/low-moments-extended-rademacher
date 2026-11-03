/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.Overshoot

/-!
# The frozen curved barrier

Harper's Probability Lemma 1 moves between barriers of the shape

`a + 10 log (min {j, L})`,

which tracks `a + 10 log j` until time `L` and is constant at `a + 10 log L` afterwards.  The
induction lowers `L` from `n^20` down through `(log_k n)^20`, one iterated-logarithm level at a
time, and the whole content of the lemma is that each such lowering costs little.

This file sets up that barrier and the comparisons the induction consumes.

## Sandwiching by a constant barrier

The single most-used step of Harper's argument is invisible in his write-up: he repeatedly replaces
the curved barrier by a *constant* one so that (A1) becomes applicable — three times in the
inductive step alone, always without comment.  `RMF.curvedBarrierProb_le_barrierProb` is the
comparison above, by `a + 10 log L`, which is what (A1) *upper* is applied to.

## The index `j = 0`

Harper's barrier events run over `1 ≤ j ≤ n`, ours over `j ≤ n`, matching `RMF.barrierProb`.  The
two agree whenever `0 ≤ a`: at `j = 0` the walk is at `0` and the barrier is `a`, since
`min {0, L} = 0` for `L > 0` and Mathlib sets `log 0 = 0`.  So no generality is lost, and no
hypothesis beyond `0 ≤ a` is incurred.
-/

open MeasureTheory ProbabilityTheory Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- **Harper's frozen curved barrier.**  Equal to `a + 10 log j` for `j ≤ L`, and constant at
`a + 10 log L` afterwards. -/
noncomputable def frozenBarrier (a L : ℝ) (j : ℕ) : ℝ := a + 10 * Real.log (min (j : ℝ) L)

@[simp] lemma frozenBarrier_zero (a : ℝ) {L : ℝ} (hL : 0 < L) : frozenBarrier a L 0 = a := by
  simp [frozenBarrier, min_eq_left hL.le]

/-- Before the freeze point the barrier is the unfrozen `a + 10 log j`. -/
lemma frozenBarrier_of_le {a L : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ L) :
    frozenBarrier a L j = a + 10 * Real.log j := by
  rw [frozenBarrier, min_eq_left hj]

/-- **The barrier rises with the freeze point.**  Freezing later is a weaker constraint. -/
lemma frozenBarrier_mono {a L L' : ℝ} (hL : 0 < L) (hLL : L ≤ L') (j : ℕ) :
    frozenBarrier a L j ≤ frozenBarrier a L' j := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    rw [frozenBarrier_zero a hL, frozenBarrier_zero a (lt_of_lt_of_le hL hLL)]
  · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hpos : (0 : ℝ) < min (j : ℝ) L := lt_min (by linarith) hL
    have := Real.log_le_log hpos (min_le_min le_rfl hLL)
    simp only [frozenBarrier]
    linarith

/-- **Above by a constant barrier.**  This is the containment that makes (A1) upper applicable. -/
lemma frozenBarrier_le_const {a L : ℝ} (hL : 1 ≤ L) (j : ℕ) :
    frozenBarrier a L j ≤ a + 10 * Real.log L := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    rw [frozenBarrier_zero a (by linarith)]
    linarith [Real.log_nonneg hL]
  · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hpos : (0 : ℝ) < min (j : ℝ) L := lt_min (by linarith) (by linarith)
    have := Real.log_le_log hpos (min_le_right (j : ℝ) L)
    simp only [frozenBarrier]
    linarith

/-- The probability that the walk stays below the frozen barrier up to time `n`. -/
noncomputable def curvedBarrierProb (μ : Measure Ω) (G : ℕ → Ω → ℝ) (a L : ℝ) (n : ℕ) : ℝ :=
  (μ {ω | ∀ j ≤ n, walk G j ω ≤ frozenBarrier a L j}).toReal

variable [IsProbabilityMeasure μ]

/-- Freezing later can only increase the probability. -/
lemma curvedBarrierProb_mono {a L L' : ℝ} (hL : 0 < L) (hLL : L ≤ L') (n : ℕ) :
    curvedBarrierProb μ G a L n ≤ curvedBarrierProb μ G a L' n :=
  ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun _ hω j hj => (hω j hj).trans (frozenBarrier_mono hL hLL j))

/-- **Sandwich, upper.**  `P(curved) ≤ P(constant barrier at `a + 10 log L`)`. -/
lemma curvedBarrierProb_le_barrierProb {a L : ℝ} (hL : 1 ≤ L) (n : ℕ) :
    curvedBarrierProb μ G a L n ≤ barrierProb μ G (a + 10 * Real.log L) n :=
  ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun _ hω j hj => (hω j hj).trans (frozenBarrier_le_const hL j))

omit [IsProbabilityMeasure μ] in
/-- Up to the freeze point the barrier is unfrozen: for `n ≤ L` the event is Harper's
`S j ≤ a + 10 log j`. -/
lemma curvedBarrierProb_of_le {a L : ℝ} {n : ℕ} (hL : (n : ℝ) ≤ L) :
    curvedBarrierProb μ G a L n
      = (μ {ω | ∀ j ≤ n, walk G j ω ≤ a + 10 * Real.log j}).toReal := by
  refine congrArg ENNReal.toReal (congrArg μ (Set.ext fun ω => ?_))
  simp only [Set.mem_setOf_eq]
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  rw [frozenBarrier_of_le (le_trans (by exact_mod_cast hj) hL)]

end RMF
