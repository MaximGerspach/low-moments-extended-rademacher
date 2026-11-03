/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.CurvedBarrier

/-!
# The frozen curved barrier, downward

Probability Result 1's *lower* bound needs the same induction run with

`a − 10 log (min {j, L})`,

the barrier that *decreases* until time `L` and is constant at `a − 10 log L` afterwards.  Harper
calls the lower bound "very similar" and writes none of it; the structure does mirror, but four
things change, and one of them is not cosmetic.

* **Monotonicity flips.**  `RMF.curvedBarrierProbLower` is *antitone* in the freeze point, where
  `RMF.curvedBarrierProb` is monotone.  In the one-step comparison `L` and the new freeze point `M`
  therefore exchange roles: the estimate reads `Q⁻_M ≤ MID⁻ + (1+ρ)·Q⁻_L`.
* **The sandwich is simpler above.**  `a − 10 log(min{j,L}) ≤ a` outright, so (A1) *upper* applies
  at `a` with no `log L` in it — where the upward barrier needed `a + 10 log L`.
* **The tail floor has to absorb the dip.**  The round trip compares two constant barriers, the
  lower being `a − 10 log L − x_N`, and it needs that to be at least its floor.  The standing
  hypothesis `a ≤ 1000Λ` is an *upper* bound on `a`, so it gives nothing here: `a − 10 log L` may
  well be negative.  The repair is to give the round trip a floor `T₁` **separate from** the split
  threshold `T`.  With `T = Λ⁴` and `T₁ = Λ⁴/2` the requirement becomes `Λ⁴/2 ≤ a − c₀Λ + Λ⁴`,
  which holds as soon as `c₀Λ ≤ Λ⁴/2`; the ratio is still `O(Λ/T₁) = O(1/Λ³)` and the middle
  window is still `O(Λ⁴)`.  See `RMF/Probability/ProbabilityLemma1Lower.lean`.
* **The endgame uses (A1) lower**, at `4a/5`, not (A1) upper.

Everything barrier-agnostic is shared with the upward development: the prefix/suffix split, the
round-trip ratio, the two exponent budgets, the telescope, and the linear growth of the (A1) and
(A2) constants.

## The index `j = 0`

As for the upward barrier: `min {0, L} = 0` and Mathlib sets `log 0 = 0`, so the barrier at `j = 0`
is `a`, and the walk is at `0` there.  The constraint is vacuous exactly when `0 ≤ a`.
-/

open MeasureTheory ProbabilityTheory Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- **The downward frozen barrier.**  Equal to `a − 10 log j` for `j ≤ L`, and constant at
`a − 10 log L` afterwards. -/
noncomputable def frozenBarrierLower (a L : ℝ) (j : ℕ) : ℝ := a - 10 * Real.log (min (j : ℝ) L)

@[simp] lemma frozenBarrierLower_zero (a : ℝ) {L : ℝ} (hL : 0 < L) :
    frozenBarrierLower a L 0 = a := by
  simp [frozenBarrierLower, min_eq_left hL.le]

/-- Before the freeze point the barrier is the unfrozen `a − 10 log j`. -/
lemma frozenBarrierLower_of_le {a L : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ L) :
    frozenBarrierLower a L j = a - 10 * Real.log j := by
  rw [frozenBarrierLower, min_eq_left hj]

/-- **The barrier falls as the freeze point rises** — the mirror of `RMF.frozenBarrier_mono`, and
the reason the one-step comparison runs the other way. -/
lemma frozenBarrierLower_anti {a L L' : ℝ} (hL : 0 < L) (hLL : L ≤ L') (j : ℕ) :
    frozenBarrierLower a L' j ≤ frozenBarrierLower a L j := by
  have hmin : min (j : ℝ) L ≤ min (j : ℝ) L' := min_le_min le_rfl hLL
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [frozenBarrierLower, min_eq_left hL.le, min_eq_left (hL.trans_le hLL).le]
  · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hpos : (0 : ℝ) < min (j : ℝ) L := lt_min (by linarith) hL
    have := Real.log_le_log hpos hmin
    simp only [frozenBarrierLower]
    linarith

/-- **Sandwiched above by the constant `a`.**  This is what (A1) *upper* is applied to; unlike the
upward barrier, no `log L` appears. -/
lemma frozenBarrierLower_le_const {a L : ℝ} (hL : 1 ≤ L) (j : ℕ) :
    frozenBarrierLower a L j ≤ a := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [frozenBarrierLower, min_eq_left (by linarith : (0 : ℝ) ≤ L)]
  · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have : (1 : ℝ) ≤ min (j : ℝ) L := le_min hj1 hL
    simp only [frozenBarrierLower]
    linarith [Real.log_nonneg this]

/-- **Sandwiched below by the constant `a − 10 log L`.**  This is what (A1) *lower* is applied
to. -/
lemma const_le_frozenBarrierLower {a L : ℝ} (hL : 1 ≤ L) (j : ℕ) :
    a - 10 * Real.log L ≤ frozenBarrierLower a L j := by
  have hlogL : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [frozenBarrierLower, Nat.cast_zero, min_eq_left (by linarith : (0 : ℝ) ≤ L),
      Real.log_zero]
    linarith
  · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hpos : (0 : ℝ) < min (j : ℝ) L := lt_min (by linarith) (by linarith)
    have := Real.log_le_log hpos (min_le_right (j : ℝ) L)
    simp only [frozenBarrierLower]
    linarith

/-- The probability that the walk stays below the downward frozen barrier up to time `n`. -/
noncomputable def curvedBarrierProbLower (μ : Measure Ω) (G : ℕ → Ω → ℝ) (a L : ℝ) (n : ℕ) : ℝ :=
  (μ {ω | ∀ j ≤ n, walk G j ω ≤ frozenBarrierLower a L j}).toReal

variable [IsProbabilityMeasure μ]

/-- **Freezing later can only decrease the probability** — the mirror of
`RMF.curvedBarrierProb_mono`. -/
lemma curvedBarrierProbLower_anti {a L L' : ℝ} (hL : 0 < L) (hLL : L ≤ L') (n : ℕ) :
    curvedBarrierProbLower μ G a L' n ≤ curvedBarrierProbLower μ G a L n :=
  ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun _ hω j hj => (hω j hj).trans (frozenBarrierLower_anti hL hLL j))

/-- **Sandwich, lower.**  `P(constant barrier at `a − 10 log L`) ≤ P(curved)`. -/
lemma barrierProb_le_curvedBarrierProbLower {a L : ℝ} (hL : 1 ≤ L) (n : ℕ) :
    barrierProb μ G (a - 10 * Real.log L) n ≤ curvedBarrierProbLower μ G a L n :=
  ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun _ hω j hj => (hω j hj).trans (const_le_frozenBarrierLower hL j))

omit [IsProbabilityMeasure μ] in
/-- Up to the freeze point the barrier is unfrozen: for `n ≤ L` the event is Harper's
`S j ≤ a − 10 log j`. -/
lemma curvedBarrierProbLower_of_le {a L : ℝ} {n : ℕ} (hL : (n : ℝ) ≤ L) :
    curvedBarrierProbLower μ G a L n
      = (μ {ω | ∀ j ≤ n, walk G j ω ≤ a - 10 * Real.log j}).toReal := by
  refine congrArg ENNReal.toReal (congrArg μ (Set.ext fun ω => ?_))
  simp only [Set.mem_setOf_eq]
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  rw [frozenBarrierLower_of_le (le_trans (by exact_mod_cast hj) hL)]

end RMF
