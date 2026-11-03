/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.Rough
import RMF.Reduction.Suppliers
import RMF.SecondMoment

/-!
# The harmonically weighted sum `S(x) = ∑_{n ≤ x} X(n)/√n`

`RMF.normalisedSum` is `x^{-1/2} ∑_{n ≤ x} f(n)`, normalised so that `E|S_x|² ≍ 1`; that is
Harper's object, and the theorem about it concerns better-than-squareroot cancellation.  Here the
weight `n^{-1/2}` sits *inside* the sum, so

`E|S(x)|² = ∑_{n ≤ x} μ²(n)/n ≍ log x`,

and the moments `E|S(x)|^{2q}` are the pseudomoment-type quantities of Bondarenko–Heap–Seip,
Gerspach and Aymone–Heap–Zhao.  Nothing here is a special case of the other; the two differ in
which power of `x` is removed, and every estimate has to be re-derived.

## Main definitions

* `RMF.weightedRademacherSum`: `S(x) = ∑_{n ≤ x} f(n)/√n`;
* `RMF.roughWeightedRademacherSum`: the same sum restricted to the `y`-rough `n`, `B_y(x)`;
* `RMF.smoothWeightedSum`: its smooth counterpart `A_y(t)`.

## Main results

* `integral_normSq_weightedSum_of_orthogonality'`: the second moment of an arbitrary
  *weighted* sum, given orthogonality — the weighted form of
  `RMF.integral_normSq_sum_of_orthogonality'`, which is stated for `∑ f(n)` with no coefficients
  and so cannot see the `n^{-1/2}`;
* `RMF.integral_normSq_weightedRademacherSum`: `E|S(x)|² = ∑_{n ≤ x} μ²(n)/n`.

Both are stated over a general coefficient sequence rather than for `n^{-1/2}` alone: every
truncation error in the layered argument is a weighted sum over a different index set, and they
all need the same second-moment computation.
-/

open Finset MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The sum -/

/-- The harmonically weighted partial sum `S(x) = ∑_{n ≤ x} f(n)/√n`.

Contrast `RMF.normalisedSum`, which divides the *whole* sum by `√x`. -/
noncomputable def weightedRademacherSum (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f ω n / (Real.sqrt n : ℂ)

/-- `B_y(x) = ∑_{r ≤ x, r `y`-rough} f(r)/√r`, the sum over the `y`-rough part of the range.
The term `r = 1` is included, `1` being `y`-rough for every `y`. -/
noncomputable def roughWeightedRademacherSum (f : Ω → ArithmeticFunction ℂ) (y : ℕ)
    (x : ℝ) (ω : Ω) : ℂ :=
  ∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n}, f ω n / (Real.sqrt n : ℂ)

omit [MeasurableSpace Ω] in
lemma weightedRademacherSum_eq_sum_div (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) :
    weightedRademacherSum f x ω = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Real.sqrt n : ℂ))⁻¹ * f ω n := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_inv_mul]

/-! ### The second moment of a weighted sum

`RMF.integral_normSq_sum_of_orthogonality'` computes `E‖∑_{n ∈ s} f(n)‖²`, which is the case of
all coefficients equal to `1`.  Every sum in the layered argument carries a coefficient, so the
computation is redone here with one. -/

/-- **The second moment of a weighted sum, from orthogonality.**  If the values are orthogonal
with `E[f(m)·conj f(n)] = δ_{mn} d(m)`, then `E‖∑ c(n) f(n)‖² = ∑ ‖c(m)‖² d(m)`.

The law does not appear: orthogonality and integrability are hypotheses, exactly as in
`RMF.integral_normSq_sum_of_orthogonality'`, so both models use this. -/
theorem integral_normSq_weightedSum_of_orthogonality' {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} {c d : ℕ → ℂ} {s : Finset ℕ}
    (hint : ∀ m ∈ s, ∀ n ∈ s, Integrable (fun ω => f ω m * (starRingEnd ℂ) (f ω n)) μ)
    (horth : ∀ m ∈ s, ∀ n ∈ s,
      (∫ ω, f ω m * (starRingEnd ℂ) (f ω n) ∂μ) = if m = n then d m else 0) :
    ((∫ ω, ‖∑ n ∈ s, c n * f ω n‖ ^ 2 ∂μ : ℝ) : ℂ)
      = ∑ m ∈ s, ((‖c m‖ : ℂ) ^ 2) * d m := by
  have hpt : ∀ ω : Ω, ((‖∑ n ∈ s, c n * f ω n‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ s, ∑ n ∈ s, (c m * (starRingEnd ℂ) (c n)) * (f ω m * (starRingEnd ℂ) (f ω n)) := by
    intro ω
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul]
    ring
  have hcast : ((∫ ω, ‖∑ n ∈ s, c n * f ω n‖ ^ 2 ∂μ : ℝ) : ℂ)
      = ∫ ω, ((‖∑ n ∈ s, c n * f ω n‖ ^ 2 : ℝ) : ℂ) ∂μ := integral_complex_ofReal.symm
  have hint' : ∀ m ∈ s, ∀ n ∈ s, Integrable
      (fun ω => (c m * (starRingEnd ℂ) (c n)) * (f ω m * (starRingEnd ℂ) (f ω n))) μ :=
    fun m hm n hn => (hint m hm n hn).const_mul _
  have hrow : ∀ m ∈ s,
      (∫ ω, ∑ n ∈ s, (c m * (starRingEnd ℂ) (c n)) * (f ω m * (starRingEnd ℂ) (f ω n)) ∂μ)
        = ((‖c m‖ : ℂ) ^ 2) * d m := by
    intro m hm
    rw [integral_finsetSum _ fun n hn => hint' m hm n hn]
    have hterm : ∀ n ∈ s,
        (∫ ω, (c m * (starRingEnd ℂ) (c n)) * (f ω m * (starRingEnd ℂ) (f ω n)) ∂μ)
          = if n = m then ((‖c m‖ : ℂ) ^ 2) * d m else 0 := by
      intro n hn
      rw [integral_const_mul, horth m hm n hn]
      by_cases h : m = n
      · subst h
        rw [if_pos rfl, if_pos rfl, ← Complex.mul_conj']
      · rw [if_neg h, if_neg fun hnm => h hnm.symm, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s m]
    simp [hm]
  rw [hcast]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m hm =>
    integrable_finsetSum _ fun n hn => hint' m hm n hn, Finset.sum_congr rfl hrow]

/-- **The second moment of the harmonic sum**: `E|S(x)|² = ∑_{n ≤ x} μ²(n)/n`.

The `q = 1` case of `E|S(x)|^{2q} ≍ (log x)^{q(2q-1)}`, and the base every layer of the argument is
compared against. -/
theorem integral_normSq_weightedRademacherSum {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsRademacherRMF f μ) (x : ℝ) :
    (∫ ω, ‖weightedRademacherSum f x ω‖ ^ 2 ∂μ)
      = ∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | Squarefree n}, (n : ℝ)⁻¹ := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, -⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have hne : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, n ≠ 0 := fun n hn =>
    Nat.one_le_iff_ne_zero.1 (Finset.mem_Icc.1 hn).1
  have key := integral_normSq_weightedSum_of_orthogonality'
    (c := fun n : ℕ => ((Real.sqrt n : ℂ))⁻¹)
    (d := fun m => if Squarefree m then 1 else 0)
    (fun m _ n _ => hf.integrable_mul_conj m n)
    (fun m hm n hn => by
      rw [hf.orthogonality (hne m hm) (hne n hn)]
      by_cases h : m = n
      · subst h; simp
      · simp [h])
  simp_rw [← weightedRademacherSum_eq_sum_div] at key
  rw [← Complex.ofReal_inj]
  rw [key, Complex.ofReal_sum]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero (hne n hn)
  have hnorm : ‖((Real.sqrt n : ℂ))⁻¹‖ = (Real.sqrt n)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  by_cases h : Squarefree n
  · rw [if_pos h, if_pos h, mul_one, hnorm]
    rw [← Complex.ofReal_pow, ← Real.sqrt_inv, Real.sq_sqrt (by positivity)]
  · rw [if_neg h, if_neg h, mul_zero]

/-! ### The smooth factor, and the rough–smooth splitting

`RMF.sum_Icc_eq_sum_rough_smooth` splits `∑_{n ≤ x} f(n)` along `n = r·k` with `r` `y`-rough and
`k` `y`-smooth, for any multiplicative `f`.  The weight `n^{-1/2}` is itself multiplicative, so
that splitting applies verbatim to the pointwise product and there is nothing to re-prove — which
is what `RMF.invSqrt` is for. -/

/-- `n ↦ n^{-1/2}` as an arithmetic function, so that the weighted sum is the sum of a
multiplicative function and the existing rough–smooth splitting applies to it unchanged. -/
noncomputable def invSqrt : ArithmeticFunction ℂ :=
  ⟨fun n => ((Real.sqrt n : ℝ) : ℂ)⁻¹, by simp⟩

@[simp] lemma invSqrt_apply (n : ℕ) : invSqrt n = ((Real.sqrt n : ℝ) : ℂ)⁻¹ := rfl

lemma isMultiplicative_invSqrt : invSqrt.IsMultiplicative := by
  refine ⟨by simp, fun {m n} _ => ?_⟩
  rw [invSqrt_apply, invSqrt_apply, invSqrt_apply, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg m)]
  push_cast
  rw [mul_inv]

omit [MeasurableSpace Ω] in
lemma weightedRademacherSum_eq_sum_pmul (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) :
    weightedRademacherSum f x ω = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((f ω).pmul invSqrt) n := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ArithmeticFunction.pmul_apply, invSqrt_apply, div_eq_mul_inv]

/-- `A_y(t) = ∑_{k ≤ t, k `y`-smooth} f(k)/√k`, the smooth factor of the splitting. -/
noncomputable def smoothWeightedSum (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (t : ℝ) (ω : Ω) :
    ℂ :=
  ∑ k ∈ {k ∈ Finset.Icc 1 ⌊t⌋₊ | k ∈ Nat.smoothNumbers (y + 1)}, f ω k / (Real.sqrt k : ℂ)

omit [MeasurableSpace Ω] in
/-- **The rough–smooth splitting of the weighted sum.**

`S(x) = ∑_{r ≤ x, r `y`-rough} f(r)r^{-1/2} · A_y(x/r)`, which is step 1 of the reduction: the
inner factor is measurable for the smooth `σ`-algebra and the outer coefficients are orthogonal
over it. -/
theorem weightedRademacherSum_eq_sum_rough_smooth (f : Ω → ArithmeticFunction ℂ) (y : ℕ)
    {x : ℝ} (hx : 0 ≤ x) {ω : Ω} (hmul : (f ω).IsMultiplicative) :
    weightedRademacherSum f x ω
      = ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y r},
          f ω r / (Real.sqrt r : ℂ) * smoothWeightedSum f y (x / r) ω := by
  have hpm : ((f ω).pmul invSqrt).IsMultiplicative := hmul.pmul isMultiplicative_invSqrt
  rw [weightedRademacherSum_eq_sum_pmul,
    sum_Icc_eq_sum_rough_smooth (f := fun ω => (f ω).pmul invSqrt) y hx hpm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smoothWeightedSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply, invSqrt_apply, invSqrt_apply,
    div_eq_mul_inv, div_eq_mul_inv]

omit [MeasurableSpace Ω] in
/-- **The smooth factor is measurable for the smooth `σ`-algebra.**  The weighted analogue of
`RMF.measurable_smoothAlgebra_smoothSum_sqfree`: the weights are constants, so the proof is the
same finite sum of measurable terms with a different constant on each. -/
lemma measurable_smoothAlgebra_smoothWeightedSum {X : ℕ → Ω → ℂ} (y : ℕ) (t : ℝ) :
    Measurable[smoothAlgebra X y]
      (smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y t) := by
  refine Finset.measurable_sum _ fun n hn => ?_
  exact (measurable_smoothAlgebra_squarefreeExtension
    (Finset.mem_filter.1 hn).2).div_const _

end RMF
