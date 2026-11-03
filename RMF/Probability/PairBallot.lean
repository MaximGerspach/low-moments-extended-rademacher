/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.HarperChainPair
import RMF.Probability.BarrierSupermartingale
import RMF.Analysis.CharFunTaylor

/-!
# The Gaussian pair ballot, decoupled

The far regime of the two-point bound compares the post-offset pair walk with a Gaussian pair walk
in regression form, `N_i = (Z_i, ρ_i Z_i + W_i)` on a product space
(`RMF.exists_gaussianWalk_pair_regression`), and needs the probability that both walks stay below
their ceilings to be `O(1/n)` — the square of the one-point ballot — with a constant that does not
grow with the barrier's envelope.  `RMF.measure_barrierEventPair_shear_le` bounds the shear by the
envelope, which is `≈ A₀ ≈ 10²⁰` here; the decoupled ballot bounds it by the first walk's own
increments.  This file supplies the one-walk ingredients; the decoupled pair ballot itself is
`RMF.measureReal_prod_pairBallot_le_sum` (`RMF/Probability/PairBallotSum.lean`).

* `RMF.IsGaussianWalk.measureReal_forall_le_le_sqrt`: the flat-ceiling ballot bound
  `P(walk ≤ y on [0,n]) ≤ (y + c)√(2/(πnv₋))`.
* `RMF.skipIdx` and `RMF.walk_skipIdx`: the walk without increment `m`, again a Gaussian walk
  (`RMF.IsGaussianWalk.skip`), which on the survival event stays below `y + |G_m|`
  (`RMF.walk_skipIdx_le`).
* `RMF.integral_abs_gaussianReal_le`: `E|Z| ≤ √V` for `Z ~ N(0,V)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

namespace RMF

section OneDim

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {Q : Measure Ω}
  [IsProbabilityMeasure Q]

/-- **The ballot upper bound at a flat ceiling**: `Q(walk_j ≤ y, j ≤ n) ≤ (y + c)√(2/(πn v₋))`
for `y ≥ 0` and `c ≥ √(πv₊/2)`, from `RMF.IsGaussianWalk.measureReal_survival_le_integral_gaussOdd`
at `m = 0`. -/
theorem IsGaussianWalk.measureReal_forall_le_le_sqrt (h : IsGaussianWalk G v Q)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {c : ℝ} (hc0 : 0 < c)
    (hc : √(π * vmax / 2) ≤ c) {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 0 ≤ y) :
    Q.real {ω | ∀ j ≤ n, walk G j ω ≤ y} ≤ (y + c) * √(2 / (π * ((n : ℝ) * vmin))) := by
  have hvmin := hv.pos
  have hv0 : ∀ j, v j ≠ 0 := fun j h0 => by
    have := hv.lo j
    rw [h0, NNReal.coe_zero] at this
    linarith
  have hcj : ∀ j, √(π * v j / 2) ≤ c := fun j =>
    le_trans (Real.sqrt_le_sqrt (by have := hv.hi j; nlinarith [Real.pi_pos])) hc
  have h1 := h.measureReal_survival_le_integral_gaussOdd (g := fun _ => y) (Y := y) (m := 0)
    (n := n) (Nat.zero_le n) (fun j _ _ => le_rfl) hv0 hc0 hcj
  rw [survivalSet_zero G hy, Set.indicator_univ] at h1
  simp only [walk_zero, Pi.zero_apply, sub_zero] at h1
  rw [integral_const, probReal_univ, one_smul, ← Finset.range_eq_Ico] at h1
  set V : ℝ≥0 := ∑ i ∈ Finset.range n, v i with hVdef
  have hVlo : (n : ℝ) * vmin ≤ (V : ℝ) := by
    rw [hVdef, NNReal.coe_sum]
    calc (n : ℝ) * vmin = ∑ _i ∈ Finset.range n, vmin := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range n, (v i : ℝ) := Finset.sum_le_sum fun i _ => hv.lo i
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hVpos : (0 : ℝ) < (V : ℝ) := lt_of_lt_of_le (by positivity) hVlo
  have hVne : V ≠ 0 := fun h0 => by rw [h0, NNReal.coe_zero] at hVpos; linarith
  have hsurv : {ω | ∀ j ≤ n, walk G j ω ≤ y} = survivalSet G (fun _ => y) n := rfl
  rw [hsurv]
  calc Q.real (survivalSet G (fun _ => y) n) ≤ gaussOdd V (y + c) := h1
    _ ≤ (y + c) * √(2 / (π * V)) := gaussOdd_le_mul_sqrt hVne (by linarith)
    _ ≤ (y + c) * √(2 / (π * ((n : ℝ) * vmin))) := by
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by linarith)
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left hVlo Real.pi_pos.le)

end OneDim

section Skip

/-- Skipping index `m`: `0, …, m-1, m+1, m+2, …`. -/
def skipIdx (m i : ℕ) : ℕ := if i < m then i else i + 1

lemma skipIdx_injective (m : ℕ) : Function.Injective (skipIdx m) := by
  intro i j h
  unfold skipIdx at h
  split_ifs at h <;> omega

lemma skipIdx_ne (m i : ℕ) : skipIdx m i ≠ m := by
  unfold skipIdx
  split_ifs <;> omega

lemma skipIdx_le_succ (m i : ℕ) : skipIdx m i ≤ i + 1 := by
  unfold skipIdx
  split_ifs <;> omega

variable {Ω : Type*}

/-- **The walk with increment `m` removed**, in terms of the full walk:
`walk G' j = walk G (skip j) - 1[m < skip j]·G_m`. -/
lemma walk_skipIdx (G : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) (j : ℕ) :
    walk (fun i => G (skipIdx m i)) j ω
      = walk G (skipIdx m j) ω - (if m < skipIdx m j then G m ω else 0) := by
  induction j with
  | zero =>
    unfold skipIdx
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp [walk_apply]
    · simp [walk_apply, hm]
  | succ j ih =>
    rw [walk_apply, Finset.sum_range_succ, ← walk_apply, ih]
    unfold skipIdx
    by_cases h1 : j + 1 < m
    · have h2 : j < m := by omega
      simp only [h1, h2, if_true]
      rw [walk_apply, walk_apply, Finset.sum_range_succ]
      simp only [show ¬ m < j by omega, show ¬ m < j + 1 by omega, if_false]
      ring
    · by_cases h3 : j + 1 = m
      · have h2 : j < m := by omega
        simp only [h1, h2, if_true, if_false]
        subst h3
        rw [walk_apply, walk_apply, Finset.sum_range_succ, Finset.sum_range_succ]
        simp only [show ¬ j + 1 < j by omega, show j + 1 < j + 1 + 1 by omega, if_true, if_false]
        ring
      · have h2 : ¬ j < m := by omega
        simp only [h1, h2, if_false, show m < j + 1 by omega, show m < j + 1 + 1 by omega,
          if_true, walk_apply, Finset.sum_range_succ]
        ring

/-- On the survival event the walk without increment `m` stays below the ceiling raised by
`|G_m|`. -/
lemma walk_skipIdx_le {G : ℕ → Ω → ℝ} {m n : ℕ} {y : ℝ} {ω : Ω}
    (hω : ∀ j ≤ n, walk G j ω ≤ y) {j : ℕ} (hj : j + 1 ≤ n) :
    walk (fun i => G (skipIdx m i)) j ω ≤ y + |G m ω| := by
  rw [walk_skipIdx]
  have hs := hω (skipIdx m j) (le_trans (skipIdx_le_succ m j) hj)
  split_ifs
  · have := neg_abs_le (G m ω)
    linarith
  · have := abs_nonneg (G m ω)
    linarith

variable [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {Q : Measure Ω}

/-- The walk with increment `m` removed is a Gaussian walk. -/
lemma IsGaussianWalk.skip (h : IsGaussianWalk G v Q) (m : ℕ) :
    IsGaussianWalk (fun i => G (skipIdx m i)) (fun i => v (skipIdx m i)) Q where
  measurable i := h.measurable (skipIdx m i)
  indep := h.indep.precomp (skipIdx_injective m)
  map_eq i := h.map_eq (skipIdx m i)

end Skip

section Weighted

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {Q : Measure Ω}
  [IsProbabilityMeasure Q]

/-- `E|Z| ≤ √V` for `Z ~ N(0,V)`, from `|x| ≤ (x²/√V + √V)/2`. -/
lemma integral_abs_gaussianReal_le {V : ℝ≥0} (hV : (0 : ℝ) < V) :
    ∫ x, |x| ∂(gaussianReal 0 V) ≤ √(V : ℝ) := by
  have hs : 0 < √(V : ℝ) := Real.sqrt_pos.2 hV
  have hsq : √(V : ℝ) ^ 2 = V := Real.sq_sqrt hV.le
  have hint2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 V) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hpt : ∀ x : ℝ, |x| ≤ (x ^ 2 / √(V : ℝ) + √(V : ℝ)) / 2 := by
    intro x
    have heq : (x ^ 2 / √(V : ℝ) + √(V : ℝ)) / 2 = (x ^ 2 + √(V : ℝ) ^ 2) / (2 * √(V : ℝ)) := by
      field_simp
    rw [heq, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|x| - √(V : ℝ)), sq_abs x]
  have hint : Integrable (fun x : ℝ => (x ^ 2 / √(V : ℝ) + √(V : ℝ)) / 2) (gaussianReal 0 V) :=
    ((hint2.div_const _).add (integrable_const _)).div_const _
  have hint1 : Integrable (fun x : ℝ => |x|) (gaussianReal 0 V) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).abs
  calc ∫ x, |x| ∂(gaussianReal 0 V)
      ≤ ∫ x, (x ^ 2 / √(V : ℝ) + √(V : ℝ)) / 2 ∂(gaussianReal 0 V) :=
        integral_mono hint1 hint hpt
    _ = (V / √(V : ℝ) + √(V : ℝ)) / 2 := by
        rw [integral_div, integral_add (hint2.div_const _) (integrable_const _), integral_div,
          integral_sq_gaussianReal_eq, integral_const, probReal_univ, one_smul]
    _ = √(V : ℝ) := by
        field_simp
        rw [hsq]
        ring

end Weighted

end RMF
