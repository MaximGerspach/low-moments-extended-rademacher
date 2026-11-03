/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ProbabilityLemma1

/-!
# Probability Result 1, upper bound

Harper's endgame (Harper, arXiv:1703.06654, Appendix A.1), and it is short: choose `k` as large
as possible with `log_k n ≥ a/1000`, apply Probability Lemma 1 at that level, and observe that the
frozen barrier is then a *constant* one, at height `a + 200 log_{k+1} n < a + a/5`, where (A1)
finishes.

Three things have to be supplied that Harper leaves implicit.

* **The terminal level exists.**  `RMF.exists_maximal_iterLog_ge`: inside the good range `n ≥ e^k`,
  so the levels run out and a largest one exists.
* **The whole chain must be good, not just its last level.**  `Real.log` is even, so `log_k n ≥ 1`
  does not propagate downwards.  The maximal `k` is therefore taken over the property "*every*
  iterate down to level `k` is at least `a/1000`", which is exactly what `RMF.IterLogGood` wants.
* **`min{1, a/√n}` comes from two different places.**  For `√n ≤ a` the bound is trivial, a
  probability being at most `1`; only for `a < √n` is there anything to prove, and there the
  minimum is `a/√n`.

The accumulated error of the induction is `≪ 1/(√n log_k² n)`, and at the terminal level
`log_k n ≥ a/1000 ≥ 1`, so it is at most `≪ 1/√n ≤ a/√n`: it is absorbed without needing the
sharper `(1000/a)²`.

The lower bound needs the mirrored induction for `a − 10 log j`, in which the barrier *decreases*
and several comparisons flip: `RMF.IsGaussianWalk.result1_lower`
(`RMF/Probability/ProbabilityLemma1Lower.lean`).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

/-- The constant of Probability Result 1's upper bound,
`max 1 (barrierConstBound v₋ v₊ 2 + (1 - e⁻²)⁻¹ · stepConst v₋ v₊ 200)`: the (A1) constant at the
collapsed barrier `2a`, plus the accumulated error of the induction, and at least `1` so that the
range `√n ≤ a`, where the bound is trivial, is covered by the same constant. -/
noncomputable def result1Const (vmin vmax : ℝ) : ℝ :=
  max 1 (barrierConstBound vmin vmax 2
    + (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ * stepConst vmin vmax 200)

lemma one_le_result1Const (vmin vmax : ℝ) : 1 ≤ result1Const vmin vmax := le_max_left _ _

/-- **Probability Result 1, upper bound.**  For a Gaussian walk with variances in `[v₋, v₊]`,
`a ≥ 1000`, and `n` large enough that `2(log n)²⁰ ≤ n` and `2(log n)⁸ ≤ n v₋`, uniformly over every
perturbation with `h(j) ≤ 10 log j`,

`P( S_j ≤ a + h(j)  ∀ 1 ≤ j ≤ n )  ≤  C(v₋,v₊) · min{1, a/√n}`.

The hypothesis is one-sided — only `h(j) ≤ 10 log j` is used, not `|h(j)| ≤ 10 log j` — since for
the upper bound the barrier is only ever raised; and it is imposed only on `1 ≤ j ≤ n`, the range
Harper imposes it on.  That matters downstream: Probability Result 1 gets applied to a *shifted*
walk, whose perturbation at its own step `j′` is `h(j′+k)`, and `|h(j′+k)| ≤ 10 log(j′+k)` is not
`≤ 10 log j′`. -/
theorem IsGaussianWalk.measure_forall_le_le (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a : ℝ} (ha : 1000 ≤ a) {n : ℕ} (hn : 1 ≤ n)
    (hbig : 2 * Real.log n ^ 20 ≤ (n : ℝ)) (hbig2 : 2 * Real.log n ^ 8 ≤ (n : ℝ) * vmin)
    {hf : ℕ → ℝ} (hhf : ∀ j, 1 ≤ j → j ≤ n → hf j ≤ 10 * Real.log j) :
    (μ {ω | ∀ j, 1 ≤ j → j ≤ n → walk G j ω ≤ a + hf j}).toReal
      ≤ result1Const vmin vmax * min 1 (a / √(n : ℝ)) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  -- the event is monotone in the perturbation, and the index `j = 0` costs nothing
  have hsub : {ω | ∀ j, 1 ≤ j → j ≤ n → walk G j ω ≤ a + hf j}
      ⊆ {ω | ∀ j ≤ n, walk G j ω ≤ a + 10 * Real.log j} := by
    intro ω hω j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · simpa [walk] using ha0
    · exact le_trans (hω j hj1 hj) (by linarith [hhf j hj1 hj])
  refine le_trans (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)) ?_
  rcases lt_or_ge a (√(n : ℝ)) with hcase | hcase
  swap
  · -- trivial range: the minimum is `1` and a probability is at most `1`
    rw [min_eq_left (by rw [le_div_iff₀ hsn]; linarith), mul_one]
    refine le_trans ?_ (one_le_result1Const vmin vmax)
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (by finiteness) prob_le_one
  · -- the substantive range
    rw [min_eq_right (by rw [div_le_one hsn]; linarith)]
    -- the terminal level of the induction
    have han : a / 1000 ≤ (n : ℝ) := by
      have hsq : √(n : ℝ) ≤ (n : ℝ) := Real.sqrt_le_self_iff.2 (Or.inr hnR)
      linarith
    obtain ⟨k, hPk, hk1⟩ := exists_maximal_iterLog_ge (b := a / 1000) (by linarith) han
    have hgood : IterLogGood k (n : ℝ) := fun i hi => le_trans (by linarith) (hPk i hi)
    have haΛ : a ≤ 1000 * iterLog k (n : ℝ) := by linarith [hPk k le_rfl]
    have ht1 : (1 : ℝ) ≤ iterLog k (n : ℝ) := hgood.one_le le_rfl
    -- Probability Lemma 1 at that level
    have hPL := (abs_le.1
      (h.abs_measure_forall_le_sub_iterLog_pow ⟨hvmin, hlo, hhi⟩ ha0 hgood haΛ hbig hbig2)).2
    -- the frozen barrier is constant, at height `a + 200 log_{k+1} n ≤ 2a`
    have hlogL : 10 * Real.log (iterLog k (n : ℝ) ^ 20) = 200 * iterLog (k + 1) (n : ℝ) := by
      rw [Real.log_pow, iterLog_succ]; push_cast; ring
    have hk10 : (0 : ℝ) ≤ iterLog (k + 1) (n : ℝ) := by
      rw [iterLog_succ]; exact Real.log_nonneg ht1
    have hQ : curvedBarrierProb μ G a (iterLog k (n : ℝ) ^ 20) n
        ≤ barrierConstBound vmin vmax 2 * a / √(n : ℝ) := by
      refine le_trans (curvedBarrierProb_le_barrierProb (μ := μ) (one_le_pow₀ ht1) n) ?_
      rw [hlogL]
      refine le_trans (barrierProb_mono (μ := μ) G
        (by linarith : a + 200 * iterLog (k + 1) (n : ℝ) ≤ 2 * a) n) ?_
      refine le_trans (h.barrierProb_le_of_comparable_mgf (by linarith) ⟨hvmin, hlo, hhi⟩ hn) ?_
      exact div_le_div_of_nonneg_right (barrierConst_le_mul hvmin (by linarith) le_rfl) hsn.le
    -- the accumulated error, absorbed into the same `a/√n`
    have hEle : stepConst vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹
          / (√(n : ℝ) * iterLog k (n : ℝ) ^ 2)
        ≤ (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ * stepConst vmin vmax 200 * a / √(n : ℝ) := by
      have hS : (0 : ℝ) ≤ stepConst vmin vmax 200 := stepConst_nonneg hvmin (by norm_num)
      have hC : (0 : ℝ) < (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ := inv_pos.2 one_sub_inv_exp_sq_pos
      have hSC : (0 : ℝ) ≤ stepConst vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ :=
        mul_nonneg hS hC.le
      have ht2 : (1 : ℝ) ≤ iterLog k (n : ℝ) ^ 2 := one_le_pow₀ ht1
      calc stepConst vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹
              / (√(n : ℝ) * iterLog k (n : ℝ) ^ 2)
          = stepConst vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ / iterLog k (n : ℝ) ^ 2
              / √(n : ℝ) := by ring
        _ ≤ stepConst vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ * a / √(n : ℝ) := by
            gcongr
            rw [div_le_iff₀ (by positivity)]
            nlinarith [mul_nonneg hSC (by nlinarith : (0 : ℝ) ≤ a * iterLog k (n : ℝ) ^ 2 - 1)]
        _ = (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ * stepConst vmin vmax 200 * a / √(n : ℝ) := by ring
    -- combine
    have hfin : barrierConstBound vmin vmax 2
        + (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ * stepConst vmin vmax 200 ≤ result1Const vmin vmax :=
      le_max_right _ _
    calc (μ {ω | ∀ j ≤ n, walk G j ω ≤ a + 10 * Real.log j}).toReal
        ≤ curvedBarrierProb μ G a (iterLog k (n : ℝ) ^ 20) n
            + stepConst vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹
              / (√(n : ℝ) * iterLog k (n : ℝ) ^ 2) := by linarith
      _ ≤ barrierConstBound vmin vmax 2 * a / √(n : ℝ)
            + (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ * stepConst vmin vmax 200 * a / √(n : ℝ) := by
          linarith
      _ = (barrierConstBound vmin vmax 2
            + (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ * stepConst vmin vmax 200) * (a / √(n : ℝ)) := by
          ring
      _ ≤ result1Const vmin vmax * (a / √(n : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hfin (by positivity)

/-! ### Arithmetic of `min {1, a/√n}`

The shape both bounds are stated in.  Halving the barrier height costs at most a factor `2` in it,
which is what lets a constant-barrier estimate at height `a/2` serve a curved barrier that never
drops below `a/2`. -/

/-- Halving the argument costs at most a factor `2`: `½·min{1,x} ≤ min{1,x/2}`.  Both sides are
below `1`, and `min{1,x} ≤ x`. -/
lemma half_min_one_le_min_one_half (x : ℝ) : (1 / 2) * min 1 x ≤ min 1 (x / 2) := by
  refine le_min ?_ ?_
  · linarith [min_le_left (1 : ℝ) x]
  · linarith [min_le_right (1 : ℝ) x]

/-- **Scaling inside `min {1, ·}`.**  A factor `≥ 1` can be pulled out for free.  Used twice in
Probability Result 2: to absorb the excess barrier height `(a + |u| + cₖ)/a` of the shifted walk,
and to pass from a suffix of length `m ≥ n/2` back to `n`. -/
lemma min_one_mul_le {lam x : ℝ} (hlam : 1 ≤ lam) :
    min 1 (lam * x) ≤ lam * min 1 x := by
  rcases le_total x 1 with hx1 | hx1
  · rw [min_eq_right hx1]
    exact min_le_right _ _
  · rw [min_eq_left hx1]
    calc min 1 (lam * x) ≤ 1 := min_le_left _ _
      _ ≤ lam * 1 := by linarith

/-- `min {1, ·/√n}` is monotone in the numerator. -/
lemma min_one_div_le_min_one_div {a c s : ℝ} (hac : a ≤ c) (hs : 0 ≤ s) :
    min 1 (a / s) ≤ min 1 (c / s) :=
  min_le_min le_rfl (div_le_div_of_nonneg_right hac hs)

/-- The composite actually invoked: if `c` is at least half of `a`, then `min {1, c/√n}` is at
least half of `min {1, a/√n}`. -/
lemma half_min_one_div_le {a c s : ℝ} (hac : a / 2 ≤ c) (hs : 0 ≤ s) :
    (1 / 2) * min 1 (a / s) ≤ min 1 (c / s) := by
  have h1 := half_min_one_le_min_one_half (a / s)
  rw [show a / s / 2 = a / 2 / s by ring] at h1
  exact le_trans h1 (min_one_div_le_min_one_div hac hs)

/-! ### The lower bound, easy regime

When `a ≥ 20 log n` the barrier `a − 10 log j` never drops below `a/2` on `1 ≤ j ≤ n`, so the event
contains a **constant**-barrier event and (A1) lower finishes.  No induction, and no case split on
the barrier against the standard deviation: `RMF.IsGaussianWalk.barrierConstLow_le_barrierProb`
already carries the `min {1, ·/√n}` shape.

The induction is therefore needed only for `a < 20 log n`, where `min {1, a/√n} = a/√n`. -/

/-- **Probability Result 1, lower bound, for `a ≥ 20 log n`.**  Uniformly over every `h` with
`-(10 log j) ≤ h(j)`: `P(S_j ≤ a + h(j) ∀ 1 ≤ j ≤ n) ≥ (barrierConstLow v₋ v₊/2)·min{1, a/√n}`.
The constant is named, so it visibly depends only on the variance bounds — Harper’s "uniformly",
which Proposition 5 needs since there the walk changes with `x` and `n`.  Only the one-sided
hypothesis is used: for the lower bound the barrier is only ever lowered. -/
theorem IsGaussianWalk.le_measure_forall_le_of_log_le (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 1 ≤ n)
    (halog : 20 * Real.log n ≤ a)
    {hf : ℕ → ℝ} (hhf : ∀ j, 1 ≤ j → j ≤ n → -(10 * Real.log j) ≤ hf j) :
    barrierConstLow vmin vmax / 2 * min 1 (a / √(n : ℝ))
      ≤ (μ {ω | ∀ j, 1 ≤ j → j ≤ n → walk G j ω ≤ a + hf j}).toReal := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hvmax : (0 : ℝ) < vmax := lt_of_lt_of_le hvmin ((hlo 0).trans (hhi 0))
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsub : {ω | ∀ j ≤ n, walk G j ω ≤ a / 2}
      ⊆ {ω | ∀ j, 1 ≤ j → j ≤ n → walk G j ω ≤ a + hf j} := by
    intro ω hω j hj1 hjn
    have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hlogj : Real.log j ≤ Real.log n := Real.log_le_log hj0 (by exact_mod_cast hjn)
    linarith [hω j hjn, hhf j hj1 hjn]
  refine le_trans ?_ (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub))
  have hA1 := h.barrierConstLow_le_barrierProb ⟨hvmin, hlo, hhi⟩ (by linarith : (0 : ℝ) ≤ a / 2) hn
  have hglue := half_min_one_div_le (a := a) (c := a / 2) (s := √(n : ℝ)) le_rfl hsn.le
  have hLpos : (0 : ℝ) ≤ barrierConstLow vmin vmax := (barrierConstLow_pos hvmin hvmax).le
  calc barrierConstLow vmin vmax / 2 * min 1 (a / √(n : ℝ))
      = barrierConstLow vmin vmax * (1 / 2 * min 1 (a / √(n : ℝ))) := by ring
    _ ≤ barrierConstLow vmin vmax * min 1 (a / 2 / √(n : ℝ)) :=
        mul_le_mul_of_nonneg_left hglue hLpos
    _ ≤ barrierProb μ G (a / 2) n := hA1

end RMF
