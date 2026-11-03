/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherPeriodisation
import RMF.Reduction.Steps

/-!
# The reduction for the Rademacher function

Harper's Proposition 2, the Rademacher case, is proved like the Steinhaus Proposition 1: "the only
non-trivial change comes at the very end" (Harper, *Moments of random multiplicative functions, I*,
arXiv:1703.06654, §2.4), where the sum over translates is traded for a maximum.  Everything before
that step transfers.

This file carries the Rademacher reduction: the base facts (measurability, the crude uniform bound
`‖S_x‖ ≤ x`, integrability), the squarefree Euler product on the critical line, conditional
orthogonality, the small range, and the assemblies `RMF.reduction_core_rademacher`,
`RMF.reduction_upper_rademacher` and `RMF.reduction_upper_max_rademacher`.

## Where the two laws differ, and where they do not

The Steinhaus proofs go through `RMF.IsSteinhausRMF.norm_apply`, an **equality** `‖f n‖ = 1`.  The
Rademacher function vanishes off the squarefrees, so only `RMF.IsRademacherRMF.norm_apply_le_one`
is available.  Every use of it in this file sits inside a sum being bounded *above*, so the
inequality suffices — and the proofs are in fact shorter, because `norm_apply_le_one` carries no
`n ≠ 0` side condition where `norm_apply` does.

`RMF.norm_partialSum_le` is law-agnostic: it takes the pointwise bound as a hypothesis rather than
a law, so both cases feed the same lemma.
-/

open MeasureTheory Filter Set
open scoped Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The normalised partial sum is measurable: a finite sum of measurable values over a constant.
Mirrors `RMF.measurable_normalisedSum`. -/
lemma IsRademacherRMF.measurable_normalisedSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (x : ℝ) : Measurable fun ω => normalisedSum f x ω :=
  (Finset.measurable_sum _ fun n _ => hf.measurable_apply n).div_const _

/-- `‖S_x‖ ≤ x` for `x ≥ 1`.  Crude — its `L²` norm is at most `1` — but it holds uniformly in
`ω`, which is all the integrability arguments need.  Mirrors `RMF.norm_normalisedSum_le`.

The Steinhaus proof feeds `RMF.norm_partialSum_le` with `‖f n‖ = 1`; here it is fed with
`RMF.IsRademacherRMF.norm_apply_le_one`, which is what that lemma actually asks for. -/
lemma IsRademacherRMF.norm_normalisedSum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {x : ℝ} (hx : 1 ≤ x) :
    ∀ᵐ ω ∂μ, ‖normalisedSum f x ω‖ ≤ x := by
  have hbdd : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 :=
    fun n _ => hf.norm_apply_le_one n
  have hsx : (1 : ℝ) ≤ Real.sqrt x := one_le_sqrt_of_one_le hx
  filter_upwards [norm_partialSum_le hbdd] with ω hω
  have hnorm : ‖normalisedSum f x ω‖ = ‖partialSum f ⌊x⌋₊ ω‖ / Real.sqrt x := by
    rw [normalisedSum, randomSum_eq_partialSum, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg x)]
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  rw [hnorm, div_le_iff₀ (by linarith : (0 : ℝ) < Real.sqrt x)]
  nlinarith

/-- **The normalised partial sum is bounded**, almost surely, by `⌊x⌋₊/√x`.  Mirrors
`RMF.IsSteinhausRMF.ae_norm_normalisedSum_le`. -/
lemma IsRademacherRMF.ae_norm_normalisedSum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (x : ℝ) :
    ∀ᵐ ω ∂μ, ‖normalisedSum f x ω‖ ≤ (⌊x⌋₊ : ℝ) / Real.sqrt x := by
  have hall : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 :=
    fun n _ => hf.norm_apply_le_one n
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
  have hnum : ‖randomSum f x ω‖ ≤ (⌊x⌋₊ : ℝ) := by
    rw [randomSum]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun n hn => hω n hn) ?_
    simp
  rw [normalisedSum, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg x)]
  exact div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg x)

/-- **The normalised partial sum is in `L^{4/3}`** (it is bounded), the exponent
`RMF.integral_rpow_le_rpow_integral_of_le_two_thirds` asks for.  Mirrors
`RMF.IsSteinhausRMF.memLp_normalisedSum`. -/
lemma IsRademacherRMF.memLp_normalisedSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (x : ℝ) :
    MemLp (normalisedSum f x) (ENNReal.ofReal (4 / 3)) μ := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  exact (memLp_top_of_bound (hf.measurable_normalisedSum x).aestronglyMeasurable _
    (hf.ae_norm_normalisedSum_le x)).mono_exponent le_top

/-! ### The squarefree Euler product obeys the same bound on the critical line

`RMF.eulerBound N = ∏_{p<N}(1 - p^{-1/2})⁻¹` was built for the Steinhaus product
`∏(1 - X_p p^{-s})⁻¹`.  The Rademacher product `∏(1 + X_p p^{-s})` is bounded by the *same*
quantity, because `1 + u ≤ (1 - u)⁻¹` whenever `0 ≤ u < 1`.

That is what lets the periodisation estimates be reused rather than re-derived: every bound in
`RMF/Reduction/Periodisation.lean` that is stated in terms of `eulerBound` is available on the
Rademacher side at the same constant. -/

/-- **Per-factor bound for the squarefree product.**  `‖1 + x·p^{-s}‖ ≤ (1 - p^{-1/2})⁻¹` when
`‖x‖ ≤ 1` and `1/2 ≤ Re s` — the same bound `RMF.norm_inv_one_sub_le` gives the Steinhaus factor.
The triangle inequality bounds `‖1 + x·p^{-s}‖` from above directly, and
`(1+u)(1-u) = 1 - u² ≤ 1` closes it. -/
lemma norm_one_add_le {x : ℂ} (hx : ‖x‖ ≤ 1) {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) :
    ‖1 + x * (p : ℂ) ^ (-s)‖ ≤ (1 - (Real.sqrt p)⁻¹)⁻¹ := by
  have hpos := one_sub_inv_sqrt_pos hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hhalf : (p : ℝ) ^ (-(1 / 2) : ℝ) = (Real.sqrt p)⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg p), Real.sqrt_eq_rpow]
  have hnorm : ‖x * (p : ℂ) ^ (-s)‖ ≤ (Real.sqrt p)⁻¹ := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    have hle : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    calc ‖x‖ * (p : ℝ) ^ (-s.re)
        ≤ 1 * (p : ℝ) ^ (-(1 / 2) : ℝ) :=
          mul_le_mul hx hle (Real.rpow_nonneg (Nat.cast_nonneg p) _) zero_le_one
      _ = (Real.sqrt p)⁻¹ := by rw [one_mul, hhalf]
  have hle : ‖1 + x * (p : ℂ) ^ (-s)‖ ≤ 1 + (Real.sqrt p)⁻¹ := by
    have h2 := norm_add_le (1 : ℂ) (x * (p : ℂ) ^ (-s))
    rw [norm_one] at h2
    linarith
  refine le_trans hle ?_
  have hkey : (1 + (Real.sqrt p)⁻¹) * (1 - (Real.sqrt p)⁻¹)
      ≤ (1 - (Real.sqrt p)⁻¹)⁻¹ * (1 - (Real.sqrt p)⁻¹) := by
    rw [inv_mul_cancel₀ (ne_of_gt hpos)]
    nlinarith [sq_nonneg ((Real.sqrt p)⁻¹)]
  exact le_of_mul_le_mul_right hkey hpos

omit [MeasurableSpace Ω] in
/-- **The squarefree partial Euler product is bounded on the critical line**, uniformly in `t`, by
the same `RMF.eulerBound` as its Steinhaus counterpart `RMF.norm_randomEulerProduct_le`. -/
lemma norm_randomEulerProduct_sqfree_le {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω}
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N s ω‖ ≤ eulerBound N := by
  rw [randomEulerProduct, eulerProduct_squarefreeExtension, eulerBound, norm_prod]
  exact Finset.prod_le_prod (fun p _ => norm_nonneg _)
    fun p hp => norm_one_add_le (hω p hp) (Nat.prime_of_mem_primesBelow hp) hs

/-! ### The periodisation bound, for the Rademacher product

`RMF.integral_lineDivSqOf_le` is stated for a general `F : Ω → ArithmeticFunction ℂ` carrying two
hypotheses — measurability along the vertical line, and a uniform bound there.  Supplying them for
the squarefree product gives the Rademacher periodisation bound *at the same constant* as the
Steinhaus one, with no re-derivation of the folding argument. -/

omit [MeasurableSpace Ω] in
/-- The squarefree product is measurable along the vertical line.  Unlike its Steinhaus
counterpart `RMF.measurable_randomEulerProduct_compMult_line` this needs **no** hypothesis at all:
the closed form `∏_{p<N}(1 + X_p·p^{-s})` is pointwise and unconditional, where the Steinhaus one
holds only where the values are bounded and `Re s > 0`. -/
lemma measurable_randomEulerProduct_sqfree_line {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} (σ : ℝ) :
    Measurable fun t : ℝ =>
      randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
        ((σ : ℂ) + (t : ℂ) * Complex.I) ω := by
  have heq : ∀ t : ℝ,
      randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((σ : ℂ) + (t : ℂ) * Complex.I) ω
        = ∏ p ∈ Nat.primesBelow N,
            (1 + X p ω * (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) := by
    intro t
    rw [randomEulerProduct, eulerProduct_squarefreeExtension]
  simp_rw [heq]
  refine Finset.measurable_prod _ fun p hp => ?_
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.prime_of_mem_primesBelow hp).pos.ne'
  have hcont : Continuous fun t : ℝ => (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl hp0)
  exact (hcont.measurable.const_mul (X p ω)).const_add 1

omit [MeasurableSpace Ω] in
/-- **The periodisation bound for the Rademacher product**, at the same constant as the Steinhaus
`RMF.integral_lineDivSq_le`.  It needs only the two hypotheses of `RMF.integral_lineDivSqOf_le`:
measurability, which is unconditional here, and the uniform bound, which
`RMF.norm_randomEulerProduct_sqfree_le` supplies at `RMF.eulerBound N`. -/
lemma integral_lineDivSqOf_sqfree_le {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    (∫ t : ℝ, lineDivSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N ω t)
      ≤ 8 * eulerBound N ^ 2 * ∑' n : ℤ, shiftWeight 1 n :=
  integral_lineDivSqOf_le σ hσ (measurable_randomEulerProduct_sqfree_line σ)
    (fun t => norm_randomEulerProduct_sqfree_le hω (by simpa using hσ))

/-! ### The line integral is integrable, Rademacher case

This is the first of `RMF.reduction_core`'s five law-dependent inputs.

The Steinhaus proof routes through `RMF.lineFunctional`, a functional of the values at the primes,
because the closed form `∏(1 - X_p p^{-s})⁻¹` is valid only where the values are bounded — so
measurability has to be transported along an almost-everywhere identity.  **The squarefree closed
form needs no such detour**: `∏(1 + X_p p^{-s})` holds pointwise, for every `ω` and every `s`, so
joint measurability in `(ω, t)` is immediate and `StronglyMeasurable.integral_prod_right'` gives
the integral's measurability directly. -/

/-- **Joint measurability of the squarefree line integrand** in `(ω, t)`. -/
lemma measurable_lineDivSqOf_sqfree_uncurry {X : ℕ → Ω → ℂ} (N : ℕ) (σ : ℝ)
    (hX : ∀ p ∈ Nat.primesBelow N, Measurable (X p)) :
    Measurable fun z : Ω × ℝ =>
      lineDivSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N z.1 z.2 := by
  have heq : ∀ z : Ω × ℝ,
      lineDivSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N z.1 z.2
        = ‖(∏ p ∈ Nat.primesBelow N,
              (1 + X p z.1 * (p : ℂ) ^ (-((σ : ℂ) + (z.2 : ℂ) * Complex.I))))
            / ((σ : ℂ) + (z.2 : ℂ) * Complex.I)‖ ^ 2 := by
    intro z
    simp only [lineDivSqOf]
    rw [randomEulerProduct, eulerProduct_squarefreeExtension]
  simp_rw [heq]
  have hden : Measurable fun z : Ω × ℝ => ((σ : ℂ) + (z.2 : ℂ) * Complex.I) := by fun_prop
  have hnum : Measurable fun z : Ω × ℝ =>
      ∏ p ∈ Nat.primesBelow N,
        (1 + X p z.1 * (p : ℂ) ^ (-((σ : ℂ) + (z.2 : ℂ) * Complex.I))) := by
    refine Finset.measurable_prod _ fun p hp => ?_
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.prime_of_mem_primesBelow hp).pos.ne'
    have hcont : Continuous fun t : ℝ => (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) :=
      Continuous.const_cpow (by fun_prop) (Or.inl hp0)
    exact (((hX p hp).comp measurable_fst).mul
      (hcont.measurable.comp measurable_snd)).const_add 1
  exact (hnum.div hden).norm.pow_const 2

/-- **The Rademacher line integral is measurable in `ω`.** -/
lemma measurable_eulerLineIntegral_sqfree {X : ℕ → Ω → ℂ} {y : ℝ}
    (hX : ∀ p ∈ Nat.primesBelow (⌊y⌋₊ + 1), Measurable (X p)) :
    Measurable fun ω =>
      eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω) y ω := by
  have hj := measurable_lineDivSqOf_sqfree_uncurry (X := X) (⌊y⌋₊ + 1) (1 / 2) hX
  have hint : Measurable fun ω : Ω => ∫ t : ℝ,
      lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) (⌊y⌋₊ + 1) ω t :=
    (MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure ℝ)) hj.stronglyMeasurable).measurable
  exact hint.const_mul _

/-- **`(eulerLineIntegral)^q` is integrable**, Rademacher case — the twin of
`RMF.integrable_eulerLineIntegral_rpow`, and the first of `RMF.reduction_core`'s five
law-dependent inputs.

The bound is the same as in the Steinhaus case, `RMF.integral_lineDivSqOf_sqfree_le` supplying
`8·eulerBound²·∑ shiftWeight 1` at the same constant. -/
theorem integrable_eulerLineIntegral_rpow_rademacher {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsRademacherRMF f μ) {y q : ℝ} (hy : 2 ≤ y) (hq : 0 ≤ q) :
    Integrable (fun ω => eulerLineIntegral f y ω ^ q) μ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI := hX.isProbabilityMeasure
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hae := ae_forall_norm_le_one hX norm_le_one_rademacherLaw (⌊y⌋₊ + 1)
  set C : ℝ := (Real.log y)⁻¹ * (8 * eulerBound (⌊y⌋₊ + 1) ^ 2 * ∑' n : ℤ, shiftWeight 1 n)
    with hCdef
  have hm : Measurable fun ω =>
      eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω) y ω :=
    measurable_eulerLineIntegral_sqfree
      (fun p hp => hX.measurable p (Nat.prime_of_mem_primesBelow hp))
  have hmeas : AEStronglyMeasurable
      (fun ω => eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω) y ω ^ q) μ := by
    have hmq : Measurable fun ω =>
        eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω) y ω ^ q := by fun_prop
    exact hmq.aestronglyMeasurable
  have hbd : ∀ᵐ ω ∂μ,
      ‖eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω) y ω ^ q‖ ≤ C ^ q := by
    filter_upwards [hae] with ω hω
    have hnn : 0 ≤ eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω) y ω :=
      eulerLineIntegral_nonneg hy ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnn q)]
    refine Real.rpow_le_rpow hnn ?_ hq
    rw [eulerLineIntegral, hCdef]
    exact mul_le_mul_of_nonneg_left (integral_lineDivSqOf_sqfree_le (by norm_num) hω)
      (inv_nonneg.2 hlog.le)
  exact (memLp_top_of_bound hmeas _ hbd).integrable le_top

/-! ### Conditional orthogonality, Rademacher case

The Steinhaus statement is `E[f(m)·conj f(m') | 𝓕_y] = δ_{m,m'}`.  **The Rademacher one carries a
squarefreeness side condition**: `f` vanishes off the squarefrees, so the diagonal term is `1` only
when `m` is squarefree, and `RMF.IsRademacherRMF.orthogonality` already records exactly that.

Everything else transfers unchanged — the two σ-algebras and their independence
(`RMF.roughAlgebra_le`, `RMF.smoothAlgebra_le`, `RMF.indep_smoothAlgebra_roughAlgebra`) are stated
for `RMF.IsIIDPrimeValues`, which both laws are. -/

/-- **Conditional orthogonality, real part, Rademacher.**  The twin of
`RMF.condExp_rough_mul_conj_re`, with the squarefreeness condition the law forces. -/
lemma condExp_rough_mul_conj_re_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsRademacherPrimeValues X μ) {y m m' : ℕ} (hm : IsRough y m) (hm' : IsRough y m')
    (hm0 : m ≠ 0) (hm'0 : m' ≠ 0) :
    μ[fun ω => (squarefreeExtension (fun p => X p ω) m
        * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m')).re | smoothAlgebra X y]
      =ᵐ[μ] fun _ => if m = m' ∧ Squarefree m then (1 : ℝ) else 0 := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hint := hRa.integrable_mul_conj m m'
  refine (MeasureTheory.condExp_indep_eq (roughAlgebra_le hX y) (smoothAlgebra_le hX y)
    (Complex.continuous_re.measurable.comp
      (measurable_rough_mul_conj_sqfree hm hm')).stronglyMeasurable
    (indep_smoothAlgebra_roughAlgebra hX y).symm).trans
    (Filter.EventuallyEq.of_eq (funext fun _ => ?_))
  have hre : ∫ ω, (squarefreeExtension (fun p => X p ω) m
      * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m')).re ∂μ
      = (∫ ω, squarefreeExtension (fun p => X p ω) m
          * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m') ∂μ).re := by
    simpa using Complex.reCLM.integral_comp_comm hint
  simp only [Function.comp_apply]
  rw [hre, hRa.orthogonality hm0 hm'0]
  split_ifs <;> simp

/-- **Conditional orthogonality, imaginary part, Rademacher.**  It vanishes, as in the Steinhaus
case: the Rademacher values are real, so the integral is real a fortiori. -/
lemma condExp_rough_mul_conj_im_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsRademacherPrimeValues X μ) {y m m' : ℕ} (hm : IsRough y m) (hm' : IsRough y m')
    (hm0 : m ≠ 0) (hm'0 : m' ≠ 0) :
    μ[fun ω => (squarefreeExtension (fun p => X p ω) m
        * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m')).im | smoothAlgebra X y]
      =ᵐ[μ] fun _ => (0 : ℝ) := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hint := hRa.integrable_mul_conj m m'
  refine (MeasureTheory.condExp_indep_eq (roughAlgebra_le hX y) (smoothAlgebra_le hX y)
    (Complex.continuous_im.measurable.comp
      (measurable_rough_mul_conj_sqfree hm hm')).stronglyMeasurable
    (indep_smoothAlgebra_roughAlgebra hX y).symm).trans
    (Filter.EventuallyEq.of_eq (funext fun _ => ?_))
  have him : ∫ ω, (squarefreeExtension (fun p => X p ω) m
      * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m')).im ∂μ
      = (∫ ω, squarefreeExtension (fun p => X p ω) m
          * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m') ∂μ).im := by
    simpa using Complex.imCLM.integral_comp_comm hint
  simp only [Function.comp_apply]
  rw [him, hRa.orthogonality hm0 hm'0]
  split_ifs <;> simp

/-! ### The pieces the conditioning identity assembles -/

/-- The smooth block is bounded, Rademacher case.  Mirrors `RMF.ae_norm_smoothSum_le`, with
`norm_apply_le_one` where the Steinhaus proof has the equality `norm_apply`. -/
lemma ae_norm_smoothSum_le_sqfree {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (y : ℕ) (t : ℝ) :
    ∀ᵐ ω ∂μ, ‖smoothSum f y t ω‖ ≤ (⌊t⌋₊ : ℝ) / Real.sqrt t := by
  have hall : ∀ n ∈ Finset.Icc 1 ⌊t⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 :=
    fun n _ => hf.norm_apply_le_one n
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
  have hnum : ‖∑ n ∈ {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, f ω n‖
      ≤ (⌊t⌋₊ : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ n ∈ {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, ‖f ω n‖
        ≤ ∑ _n ∈ {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, (1 : ℝ) :=
          Finset.sum_le_sum fun n hn => hω n (Finset.mem_filter.1 hn).1
      _ ≤ (⌊t⌋₊ : ℝ) := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact_mod_cast le_trans (Finset.card_filter_le _ _) (by simp)
  rw [smoothSum, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg t)]
  exact div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg t)

/-- Mirrors `RMF.integrable_mul_rough_re`.  Shorter than its model, because
`RMF.IsRademacherRMF.integrable_mul_conj` needs no `m ≠ 0`. -/
lemma integrable_mul_rough_re_sqfree {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hf : IsRademacherRMF f μ) (m m' : ℕ)
    {V : Ω → ℂ} {c : ℝ} (hV : AEStronglyMeasurable V μ) (hVb : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ c) :
    Integrable (fun ω => (V ω * (f ω m * (starRingEnd ℂ) (f ω m'))).re) μ := by
  simpa using ((hf.integrable_mul_conj m m').bdd_mul hV hVb).re

/-- **The pull-out step for one pair `(m, m')`, Rademacher.**  Mirrors
`RMF.condExp_mul_rough_re`; the rough factor contributes its unconditional expectation, which here
is `1` only when `m = m'` *and* `m` is squarefree. -/
lemma condExp_mul_rough_re_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsRademacherPrimeValues X μ) {y m m' : ℕ} (hm : IsRough y m) (hm' : IsRough y m')
    (hm0 : m ≠ 0) (hm'0 : m' ≠ 0) {V : Ω → ℂ} {c : ℝ}
    (hV : Measurable[smoothAlgebra X y] V) (hVb : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ c) :
    μ[fun ω => (V ω * (squarefreeExtension (fun p => X p ω) m
        * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m'))).re | smoothAlgebra X y]
      =ᵐ[μ] fun ω => (if m = m' ∧ Squarefree m then (1 : ℝ) else 0) * (V ω).re := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hZint := hRa.integrable_mul_conj m m'
  have hZre : Integrable (fun ω => (squarefreeExtension (fun p => X p ω) m
      * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m')).re) μ := by
    simpa using hZint.re
  have hZim : Integrable (fun ω => (squarefreeExtension (fun p => X p ω) m
      * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m')).im) μ := by
    simpa using hZint.im
  have hVre : StronglyMeasurable[smoothAlgebra X y] fun ω => (V ω).re :=
    (Complex.continuous_re.measurable.comp hV).stronglyMeasurable
  have hVim : StronglyMeasurable[smoothAlgebra X y] fun ω => (V ω).im :=
    (Complex.continuous_im.measurable.comp hV).stronglyMeasurable
  have hVreb : ∀ᵐ ω ∂μ, ‖(V ω).re‖ ≤ c := by
    filter_upwards [hVb] with ω hω
    exact le_trans (Complex.abs_re_le_norm _) hω
  have hVimb : ∀ᵐ ω ∂μ, ‖(V ω).im‖ ≤ c := by
    filter_upwards [hVb] with ω hω
    exact le_trans (Complex.abs_im_le_norm _) hω
  have hle := smoothAlgebra_le hX y
  have hi1 : Integrable ((fun ω => (V ω).re)
      * fun ω => (squarefreeExtension (fun p => X p ω) m
        * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m')).re) μ :=
    hZre.bdd_mul ((hVre.mono hle).aestronglyMeasurable) hVreb
  have hi2 : Integrable ((fun ω => (V ω).im)
      * fun ω => (squarefreeExtension (fun p => X p ω) m
        * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m')).im) μ :=
    hZim.bdd_mul ((hVim.mono hle).aestronglyMeasurable) hVimb
  have key : (fun ω => (V ω * (squarefreeExtension (fun p => X p ω) m
        * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m'))).re)
      = ((fun ω => (V ω).re) * fun ω => (squarefreeExtension (fun p => X p ω) m
          * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m')).re)
        - ((fun ω => (V ω).im) * fun ω => (squarefreeExtension (fun p => X p ω) m
          * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m')).im) := by
    funext ω
    simp [Complex.mul_re]
  rw [key]
  filter_upwards [condExp_sub hi1 hi2 (smoothAlgebra X y),
    condExp_stronglyMeasurable_mul_of_bound hle hVre hZre c hVreb,
    condExp_stronglyMeasurable_mul_of_bound hle hVim hZim c hVimb,
    condExp_rough_mul_conj_re_sqfree hX hm hm' hm0 hm'0,
    condExp_rough_mul_conj_im_sqfree hX hm hm' hm0 hm'0] with ω e0 e1 e2 e3 e4
  rw [e0]
  simp only [Pi.sub_apply, Pi.mul_apply] at e1 e2 ⊢
  rw [e1, e2, e3, e4]
  ring

/-- **The conditional second moment of a rough–smooth sum, Rademacher case**, an identity, for any
smooth factor `G` that is measurable for the smooth `σ`-algebra and almost surely bounded.

**The index set is where the two laws part company.**  Steinhaus sums over every rough `m`; here
the sum runs over the rough `m` that are *squarefree*, because `f` vanishes off the squarefrees and
so the diagonal term of the conditional orthogonality survives only there. -/
theorem condExp_normSq_roughSmoothSum_sqfree {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ)
    {y : ℕ} {x : ℝ} {G : ℕ → Ω → ℂ} {B : ℕ → ℝ}
    (hGmeas : ∀ m, Measurable[smoothAlgebra X y] (G m))
    (hGb : ∀ m, ∀ᵐ ω ∂μ, ‖G m ω‖ ≤ B m) :
    μ[fun ω => ‖∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
        (((Real.sqrt m)⁻¹ : ℝ) : ℂ)
          * (squarefreeExtension (fun p => X p ω) m * G m ω)‖ ^ 2 | smoothAlgebra X y]
      =ᵐ[μ] fun ω => ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m},
          (m : ℝ)⁻¹ * ‖G m ω‖ ^ 2 := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hle := smoothAlgebra_le hX y
  set A : Finset ℕ := {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m} with hAdef
  have hAmem : ∀ m ∈ A, m ≠ 0 ∧ IsRough y m := by
    intro m hm
    rw [hAdef, Finset.mem_filter, Finset.mem_Icc] at hm
    exact ⟨by omega, hm.2⟩
  set V : ℕ → ℕ → Ω → ℂ := fun m m' ω =>
    (((Real.sqrt m * Real.sqrt m')⁻¹ : ℝ) : ℂ)
      * (G m ω * (starRingEnd ℂ) (G m' ω)) with hVdef
  set T : ℕ → ℕ → Ω → ℝ := fun m m' ω =>
    (V m m' ω * (squarefreeExtension (fun p => X p ω) m
      * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m'))).re with hTdef
  have hVmeas : ∀ m m' : ℕ, Measurable[smoothAlgebra X y] (V m m') := by
    intro m m'
    simp only [hVdef]
    exact Measurable.const_mul ((hGmeas m).mul
      (Complex.continuous_conj.measurable.comp (hGmeas m'))) _
  have hB : ∀ m, 0 ≤ B m := fun m => by
    obtain ⟨ω, hω⟩ := (hGb m).exists
    exact le_trans (norm_nonneg _) hω
  have hVb : ∀ m m' : ℕ, ∀ᵐ ω ∂μ, ‖V m m' ω‖
      ≤ (Real.sqrt m * Real.sqrt m')⁻¹ * (B m * B m') := by
    intro m m'
    filter_upwards [hGb m, hGb m'] with ω h1 h2
    simp only [hVdef]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul,
      Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (hB m))
      (by positivity)
  have hGint : ∀ m ∈ A, ∀ m' ∈ A, Integrable (T m m') μ := fun m _ m' _ =>
    integrable_mul_rough_re_sqfree hRa m m'
      ((hVmeas m m').mono hle le_rfl).aestronglyMeasurable (hVb m m')
  -- each row collapses to its diagonal term, and only when `m` is squarefree
  have hrow : ∀ m ∈ A, μ[fun ω => ∑ m' ∈ A, T m m' ω | smoothAlgebra X y]
      =ᵐ[μ] fun ω => if Squarefree m then
        (m : ℝ)⁻¹ * ‖G m ω‖ ^ 2
      else 0 := by
    intro m hm
    rw [show (fun ω => ∑ m' ∈ A, T m m' ω) = ∑ m' ∈ A, T m m' from
      funext fun ω => by simp [Finset.sum_apply]]
    refine (condExp_finsetSum (fun m' hm' => hGint m hm m' hm') (smoothAlgebra X y)).trans ?_
    have hpairs : ∀ᵐ ω ∂μ, ∀ m' ∈ (A : Set ℕ),
        (μ[T m m' | smoothAlgebra X y]) ω
          = (if m = m' ∧ Squarefree m then (1 : ℝ) else 0) * (V m m' ω).re := by
      rw [MeasureTheory.ae_ball_iff A.countable_toSet]
      intro m' hm'
      have hm'A : m' ∈ A := by simpa using hm'
      exact condExp_mul_rough_re_sqfree hX (hAmem m hm).2 (hAmem m' hm'A).2 (hAmem m hm).1
        (hAmem m' hm'A).1 (hVmeas m m') (hVb m m')
    filter_upwards [hpairs] with ω hω
    simp only [Finset.sum_apply]
    rw [Finset.sum_congr rfl fun m' hm' => hω m' (by simpa using hm'), Finset.sum_eq_single m]
    · by_cases hsf : Squarefree m
      · rw [if_pos ⟨rfl, hsf⟩, if_pos hsf, one_mul]
        simp only [hVdef]
        rw [Real.mul_self_sqrt (Nat.cast_nonneg m), Complex.mul_conj, ← Complex.ofReal_mul,
          Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      · rw [if_neg fun h => hsf h.2, if_neg hsf, zero_mul]
    · intro m' _ hne
      rw [if_neg fun h => hne h.1.symm, zero_mul]
    · intro hnm
      exact absurd hm hnm
  rw [show (fun ω => ‖∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
        (((Real.sqrt m)⁻¹ : ℝ) : ℂ)
          * (squarefreeExtension (fun p => X p ω) m * G m ω)‖ ^ 2)
      = ∑ m ∈ A, fun ω => ∑ m' ∈ A, T m m' ω from
    funext fun ω => by
      simp only [Finset.sum_apply, hTdef, hVdef]
      rw [norm_sq_sum_eq_sum_re]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
      refine congrArg Complex.re ?_
      simp only [map_mul, Complex.conj_ofReal, mul_inv, Complex.ofReal_mul]
      ring]
  refine (condExp_finsetSum (fun m hm =>
    integrable_finsetSum _ fun m' hm' => hGint m hm m' hm') (smoothAlgebra X y)).trans ?_
  have hrows : ∀ᵐ ω ∂μ, ∀ m ∈ (A : Set ℕ),
      (μ[fun ω => ∑ m' ∈ A, T m m' ω | smoothAlgebra X y]) ω
        = if Squarefree m then
            (m : ℝ)⁻¹ * ‖G m ω‖ ^ 2
          else 0 := by
    rw [MeasureTheory.ae_ball_iff A.countable_toSet]
    intro m hm
    exact hrow m (by simpa using hm)
  filter_upwards [hrows] with ω hω
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun m hm => hω m (by simpa using hm), ← Finset.sum_filter]
  simp only [hAdef, Finset.filter_filter]

/-- **The conditional second moment, Rademacher case**: the `RMF.smoothSum` instance of
`RMF.condExp_normSq_roughSmoothSum_sqfree`,
`E[|S_x|² | 𝓕_y] = ∑_{m ≤ x, m rough and squarefree} m⁻¹ |S_{x/m,y}|²`.
Every term is nonnegative, so this is a sub-sum of the Steinhaus shape — which is why the upper
bound downstream is unaffected. -/
theorem condExp_normSq_normalisedSum_sqfree {f : Ω → ArithmeticFunction ℂ} {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ)
    (hf : f = fun ω => squarefreeExtension fun p => X p ω) {y : ℕ}
    {x : ℝ} (hx : 1 ≤ x) :
    μ[fun ω => ‖normalisedSum f x ω‖ ^ 2 | smoothAlgebra X y]
      =ᵐ[μ] fun ω => ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m},
          (m : ℝ)⁻¹ * ‖smoothSum f y (x / m) ω‖ ^ 2 := by
  subst hf
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have key := condExp_normSq_roughSmoothSum_sqfree (x := x) hX
    (G := fun m => smoothSum (fun ω => squarefreeExtension fun p => X p ω) y (x / m))
    (B := fun m => (⌊x / m⌋₊ : ℝ) / Real.sqrt (x / m))
    (fun m => measurable_smoothAlgebra_smoothSum_sqfree y (x / m))
    (fun m => ae_norm_smoothSum_le_sqfree hRa y (x / m))
  refine Filter.EventuallyEq.trans (condExp_congr_ae ?_) key
  filter_upwards with ω
  rw [normalisedSum_eq_sum_rough_smooth (f := fun ω => squarefreeExtension fun p => X p ω)
    (ω := ω) y hx (hRa.isMultiplicative ω)]
  refine congrArg (fun z : ℂ => ‖z‖ ^ 2) (Finset.sum_congr rfl fun m _ => ?_)
  rw [Complex.ofReal_inv]
  ring

/-! ### The small range: the smooth second moment, as an inequality

The Steinhaus reduction uses the *identity* `E|S_{t,y}|² = Ψ(t,y)/t`.  For Rademacher the smooth
second moment counts only the **squarefree** `y`-smooth numbers, so the identity fails — but the
squarefree ones are a subset, so the bound `≤ Ψ(t,y)/t` holds, and that is all the upper bound
needs.  **The same Rankin estimate then applies with no new number theory.** -/

/-- The Rademacher smooth block's second moment is at most the smooth count.  The Steinhaus mirror
`RMF.integral_normSq_smoothSum` is an equality. -/
lemma integral_normSq_smoothSum_le_sqfree {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsRademacherRMF f μ) (y : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ ω, ‖smoothSum f y t ω‖ ^ 2 ∂μ) ≤ (smoothCount y t : ℝ) / t := by
  have hs : ∀ n ∈ {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, n ≠ 0 := by
    intro n hn
    have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
    omega
  have hnorm : ∀ ω : Ω, ‖smoothSum f y t ω‖ ^ 2
      = ‖∑ n ∈ {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, f ω n‖ ^ 2 / t := by
    intro ω
    rw [smoothSum, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg t), div_pow, Real.sq_sqrt ht.le]
  simp_rw [hnorm]
  rw [integral_div, smoothCount]
  exact div_le_div_of_nonneg_right (hf.integral_normSq_sum_le hs) ht.le

/-- The rough sum's expectation is at most the sum of smooth counts.  The Steinhaus mirror
`RMF.integral_sum_roughTerm` is an equality. -/
lemma integral_sum_roughTerm_le_sqfree {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsRademacherRMF f μ) (y : ℕ) {x : ℝ} (hx : 0 < x)
    {s : Finset ℕ} (hs : ∀ m ∈ s, 0 < m ∧ 1 ≤ x / m) :
    (∫ ω, ∑ m ∈ s, roughTerm f y x ω m ∂μ) ≤ ∑ m ∈ s, (smoothCount y (x / m) : ℝ) / x := by
  rw [integral_finsetSum _ fun m hm => integrable_roughTerm hf.isBoundedRMF y (hs m hm).2]
  refine Finset.sum_le_sum fun m hm => ?_
  obtain ⟨hm0, hmt⟩ := hs m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  simp_rw [roughTerm]
  rw [integral_const_mul]
  have hb := integral_normSq_smoothSum_le_sqfree hf y (by positivity : (0 : ℝ) < x / m)
  have hkey : (m : ℝ)⁻¹ * ((smoothCount y (x / m) : ℝ) / (x / m))
      = (smoothCount y (x / m) : ℝ) / x := by
    field_simp
  calc (m : ℝ)⁻¹ * ∫ ω, ‖smoothSum f y (x / m) ω‖ ^ 2 ∂μ
      ≤ (m : ℝ)⁻¹ * ((smoothCount y (x / m) : ℝ) / (x / m)) := by
        exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (smoothCount y (x / m) : ℝ) / x := hkey

/-- **The small range, Rademacher** — the third of `RMF.reduction_core`'s five law-dependent
inputs.  Mirrors `RMF.integral_rpow_sum_small_le`, with the smooth second moment entering as an
inequality rather than an identity.  The Rankin hypothesis `hR` and the resulting bound are
*identical*: the squarefree smooth count is at most the smooth count, so nothing about the
number theory changes. -/
lemma integral_rpow_sum_small_le_sqfree {A cR CR : ℝ}
    (hR : ∀ (y : ℕ) (x : ℝ), 2 ≤ y → 2 ≤ x →
      (smoothCount y x : ℝ)
        ≤ CR * x * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y))
    (hCR : 0 ≤ CR) {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hf : IsRademacherRMF f μ) {y : ℕ} (hy : 2 ≤ y) {x q : ℝ} (hx : 1 ≤ x)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {N : ℕ} {s : Finset ℕ} (hsub : s ⊆ Finset.Icc 1 N)
    (hsm : ∀ m ∈ s, 0 < m ∧ 2 ≤ x / m)
    (hβ0 : 0 < cR / Real.log y) (hβ1 : cR / Real.log y ≤ 1) :
    ∫ ω, (∑ m ∈ s, roughTerm f y x ω m) ^ q ∂μ
      ≤ (CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
          * (1 + (N : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))) ^ q := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsm1 : ∀ m ∈ s, 0 < m ∧ 1 ≤ x / m := fun m hm => ⟨(hsm m hm).1, by linarith [(hsm m hm).2]⟩
  have hnn : ∀ᵐ ω ∂μ, (∑ m ∈ s, roughTerm f y x ω m) ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall fun ω =>
      Set.mem_Ici.2 (Finset.sum_nonneg fun m _ => roughTerm_nonneg _ _ _ _ _)
  have hint : Integrable (fun ω => ∑ m ∈ s, roughTerm f y x ω m) μ :=
    integrable_finsetSum _ fun m hm => integrable_roughTerm hf.isBoundedRMF y (hsm1 m hm).2
  have hintq := integrable_rpow_sum_roughTerm hf.isBoundedRMF y hx hsm1 hq0
  have hnn' : (0 : ℝ) ≤ ∑ m ∈ s, (smoothCount y (x / m) : ℝ) / x :=
    Finset.sum_nonneg fun m _ => by positivity
  calc ∫ ω, (∑ m ∈ s, roughTerm f y x ω m) ^ q ∂μ
      ≤ (∫ ω, ∑ m ∈ s, roughTerm f y x ω m ∂μ) ^ q :=
        integral_rpow_le_rpow_integral hq0 hq1 hnn hint hintq
    _ ≤ (∑ m ∈ s, (smoothCount y (x / m) : ℝ) / x) ^ q :=
        Real.rpow_le_rpow (integral_nonneg fun ω =>
          Finset.sum_nonneg fun m _ => roughTerm_nonneg _ _ _ _ _)
          (integral_sum_roughTerm_le_sqfree hf y hx0 hsm1) hq0
    _ ≤ (CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
          * (1 + (N : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))) ^ q :=
        Real.rpow_le_rpow hnn' (sum_smoothCount_div_le hR hCR hy hx0 hsub hsm hβ0 hβ1) hq0

/-! ### The Dirichlet series over smooth numbers, Rademacher

`RMF.dirichletSeries_smoothCoeff_eq` identifies the Dirichlet series of the smooth coefficients
with the Euler product.  Its Steinhaus proof goes through `RMF.compMultCpowHom`, a `MonoidHom`,
and Mathlib's **geometric** Euler product, which needs `‖f p‖ < 1` at every prime — hence an
almost-everywhere hypothesis on the values, and `0 < Re s`.

The squarefree extension is multiplicative only at *coprime* arguments, so it is not a `MonoidHom`
and the geometric form does not apply.  The **general**
`EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum` does, and its local factor
`∑ₖ f(pᵏ)` collapses to `1 + f(p)` because `p²∤` squarefree kills every higher power.  **So the
identity here needs no hypothesis at all** — not on `s`, not on `ω`, not on the values. -/

/-- `n ↦ f(n)·n^{-s}` for the squarefree extension.  The analogue of `RMF.compMultCpowHom`, which
cannot be a `MonoidHom` here: multiplicativity holds only at coprime arguments. -/
noncomputable def sqfreeCpow (x : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  squarefreeExtension x n * (n : ℂ) ^ (-s)

lemma sqfreeCpow_one (x : ℕ → ℂ) (s : ℂ) : sqfreeCpow x s 1 = 1 := by
  simp [sqfreeCpow]

lemma sqfreeCpow_mul_of_coprime (x : ℕ → ℂ) (s : ℂ) {m n : ℕ} (h : Nat.Coprime m n) :
    sqfreeCpow x s (m * n) = sqfreeCpow x s m * sqfreeCpow x s n := by
  have hcast : ((m * n : ℕ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
    have hh := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg (α := ℝ) m)
      (Nat.cast_nonneg (α := ℝ) n) (-s)
    push_cast at hh ⊢
    exact hh
  rw [sqfreeCpow, sqfreeCpow, sqfreeCpow, hcast,
    (isMultiplicative_squarefreeExtension x).map_mul_of_coprime h]
  ring

/-- **The local factor terminates.**  `∑ₖ f(pᵏ)·p^{-ks} = 1 + f(p)·p^{-s}`: every `k ≥ 2` term
vanishes because `pᵏ` is not squarefree.  This is what removes the convergence hypothesis its
Steinhaus counterpart needs. -/
lemma tsum_sqfreeCpow_prime_pow (x : ℕ → ℂ) (s : ℂ) {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, sqfreeCpow x s (p ^ k)) = 1 + x p * (p : ℂ) ^ (-s) := by
  have hvanish : ∀ k ∉ Finset.range 2, sqfreeCpow x s (p ^ k) = 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [sqfreeCpow, squarefreeExtension_apply_prime_pow x hp (by omega), zero_mul]
  rw [tsum_eq_sum hvanish, Finset.sum_range_succ, Finset.sum_range_one]
  rw [pow_zero, pow_one, sqfreeCpow_one, sqfreeCpow,
    squarefreeExtension_apply_prime x hp]

omit [MeasurableSpace Ω] in
/-- **The Dirichlet series over `y`-smooth numbers is the Euler product over `p ≤ y`**, Rademacher
case.  The twin of `RMF.dirichletSeries_smoothCoeff_eq`, and unlike it an identity for *every* `ω`
and *every* `s`. -/
theorem dirichletSeries_smoothCoeff_eq_sqfree {X : ℕ → Ω → ℂ} (y : ℕ) (ω : Ω) (s : ℂ) :
    dirichletSeries (smoothCoeff (fun ω => squarefreeExtension fun p => X p ω) y ω) s
      = randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1) s ω := by
  classical
  set x : ℕ → ℂ := fun p => X p ω with hxdef
  have hprod := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := sqfreeCpow x s) (sqfreeCpow_one x s)
    (fun {m n} h => sqfreeCpow_mul_of_coprime x s h)
    (fun {p} hp => by
      refine summable_of_ne_finset_zero (s := Finset.range 2) fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [sqfreeCpow, squarefreeExtension_apply_prime_pow x hp (by omega), zero_mul, norm_zero])
    (y + 1)).2
  have hds : dirichletSeries (smoothCoeff (fun ω => squarefreeExtension fun p => X p ω) y ω) s
      = ∑' m : Nat.smoothNumbers (y + 1), sqfreeCpow x s m := by
    rw [tsum_subtype, dirichletSeries]
    refine tsum_congr fun n => ?_
    by_cases hn : n ∈ Nat.smoothNumbers (y + 1)
    · rw [Set.indicator_of_mem hn, smoothCoeff, if_pos hn, sqfreeCpow,
        Complex.cpow_neg, div_eq_mul_inv]
    · rw [Set.indicator_of_notMem hn, smoothCoeff, if_neg hn, zero_div]
  rw [hds, hprod.tsum_eq, randomEulerProduct, eulerProduct_squarefreeExtension]
  exact Finset.prod_congr rfl fun p hp =>
    tsum_sqfreeCpow_prime_pow x s (Nat.prime_of_mem_primesBelow hp)

/-! ### Step (a) for Rademacher: conditional Jensen

The conditioning identity (`RMF.condExp_normSq_normalisedSum_sqfree`) puts the *squarefree* rough
`m` on the right.  Widening back to all rough `m` costs nothing — the terms are nonnegative — so
the conclusion matches its Steinhaus mirror `RMF.integral_rpow_le_integral_rough_sum` exactly, and
`RMF.reduction_core`'s shape is unchanged. -/

/-- **Step (a), Rademacher.**  Conditional Jensen for `t ↦ t^q`, then the conditional second
moment.  The twin of `RMF.integral_rpow_le_integral_rough_sum`. -/
theorem integral_rpow_le_integral_rough_sum_sqfree {f : Ω → ArithmeticFunction ℂ}
    {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ)
    (hf : f = fun ω => squarefreeExtension fun p => X p ω) {y : ℕ}
    {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
          (m : ℝ)⁻¹ * ‖smoothSum f y (x / m) ω‖ ^ 2) ^ q ∂μ := by
  classical
  have hRa : IsRademacherRMF f μ := isRademacherRMF_iff_exists.2 ⟨X, hX, hf⟩
  have hle := smoothAlgebra_le hX y
  haveI : SigmaFinite (μ.trim hle) := (isFiniteMeasure_trim hle).toSigmaFinite
  have hid := condExp_normSq_normalisedSum_sqfree hX hf (y := y) hx
  -- the two index sets, and the integrability of each rough sum's `q`-th power
  have hsub : {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m}
      ⊆ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m} := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, hm.2.1⟩
  have hintS := integrable_rpow_sum_roughTerm hRa.isBoundedRMF y hx
    (fun m hm => rough_mem_facts (P := fun m => IsRough y m ∧ Squarefree m) hx hm) hq0
  have hintA := integrable_rpow_sum_roughTerm hRa.isBoundedRMF y hx
    (fun m hm => rough_mem_facts (P := fun m => IsRough y m) hx hm) hq0
  calc ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω, (μ[fun ω => ‖normalisedSum f x ω‖ ^ 2 | smoothAlgebra X y] ω) ^ q ∂μ :=
        integral_rpow_norm_le_integral_condExp_rpow hle (hRa.measurable_normalisedSum x)
          (hRa.norm_normalisedSum_le hx) hq0 hq1
    _ = ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m},
          (m : ℝ)⁻¹ * ‖smoothSum f y (x / m) ω‖ ^ 2) ^ q ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hid] with ω hω
        rw [hω]
    _ ≤ ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
          (m : ℝ)⁻¹ * ‖smoothSum f y (x / m) ω‖ ^ 2) ^ q ∂μ := by
        refine integral_mono hintS hintA fun ω => ?_
        refine Real.rpow_le_rpow (Finset.sum_nonneg fun m _ => by positivity) ?_ hq0
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity

/-! ### The reduction, assembled

`RMF.reduction_core` and `RMF.reduction_upper` for the Rademacher function.  Both statements are
*verbatim* their Steinhaus mirrors with `RMF.IsSteinhausRMF` replaced by `RMF.IsRademacherRMF` —
same constants, same hypotheses, same conclusion. -/

/-- **The reduction, given the parameters, Rademacher.**  The twin of `RMF.reduction_core`:

`E|S_x|^{2q} ≤ (Rankin bound)^q + (Cs/π)^q E[(eulerLineIntegral)^q]`. -/
theorem reduction_core_rademacher {A cR CR Cs : ℝ}
    (hR : ∀ (y : ℕ) (x : ℝ), 2 ≤ y → 2 ≤ x →
      (smoothCount y x : ℝ)
        ≤ CR * x * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y))
    (hCR : 0 ≤ CR)
    (hS : ∀ (y : ℕ) (x H : ℝ), 2 ≤ y → 0 < x → 0 < H → (y : ℝ) ≤ H →
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ H →
      (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ) ≤ Cs * H / Real.log y)
    (hCs : 0 ≤ Cs)
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ)
    {y : ℕ} (hy : 2 ≤ y) {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {N R : ℕ}
    (hsmall2 : ∀ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N}, 2 ≤ x / m)
    (hsmallsub : {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N} ⊆ Finset.Icc 1 N)
    (hmaps : ∀ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
      ⌊x / (m : ℝ)⌋₊ ∈ Finset.Icc 1 R)
    (hsieveOK : ∀ r ∈ Finset.Icc 1 R, 2 ≤ x / ((r : ℝ) + 1) ∧
      2 ≤ x / r - x / ((r : ℝ) + 1) ∧ (y : ℝ) ≤ x / r - x / ((r : ℝ) + 1) ∧
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ x / r - x / ((r : ℝ) + 1))
    (hfib : ∀ r ∈ Finset.Icc 1 R,
      {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N}.filter
          (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)
        ⊆ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r})
    (hβ0 : 0 < cR / Real.log y) (hβ1 : cR / Real.log y ≤ 1) :
    ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
      ≤ (CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
            * (1 + (N : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))) ^ q
        + (Cs / π) ^ q * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hx0 : (0 : ℝ) < x := by linarith
  have hCsπ : (0 : ℝ) ≤ Cs / π := by positivity
  have hdir : ∀ᵐ ω ∂μ, ∀ z : ℂ, 0 < z.re →
      dirichletSeries (smoothCoeff (fun ω => squarefreeExtension fun p => X p ω) y ω) z
        = randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1) z ω :=
    Filter.Eventually.of_forall fun ω z _ => dirichletSeries_smoothCoeff_eq_sqfree y ω z
  have hlarge : ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
        roughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω m) ^ q ∂μ
      ≤ (Cs / π) ^ q
        * ∫ ω, eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω)
            (y : ℝ) ω ^ q ∂μ := by
    have hfun : (fun ω => ((Cs / π)
          * eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω) (y : ℝ) ω) ^ q)
        = fun ω => (Cs / π) ^ q
          * eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω) (y : ℝ) ω ^ q := by
      funext ω
      exact Real.mul_rpow hCsπ (eulerLineIntegral_nonneg hyR ω)
    have hint : Integrable (fun ω => ((Cs / π)
        * eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω) (y : ℝ) ω) ^ q) μ := by
      rw [hfun]
      exact (integrable_eulerLineIntegral_rpow_rademacher hRa (y := (y : ℝ)) hyR hq0).const_mul _
    have hbd := sum_roughTerm_large_le_euler hCs hS hRa.isBoundedRMF hy hdir hx0
      (fun m hm => (rough_mem_facts (P := fun m => IsRough y m ∧ ¬ m ≤ N) hx hm).1)
      hmaps hsieveOK hfib
    calc ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
            roughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω m) ^ q ∂μ
        ≤ ∫ ω, ((Cs / π)
            * eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω)
              (y : ℝ) ω) ^ q ∂μ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
            Real.rpow_nonneg (Finset.sum_nonneg fun m _ => roughTerm_nonneg _ _ _ _ _) q)
            hint ?_
          filter_upwards [hbd] with ω hω
          exact Real.rpow_le_rpow
            (Finset.sum_nonneg fun m _ => roughTerm_nonneg _ _ _ _ _) hω hq0
      _ = (Cs / π) ^ q
            * ∫ ω, eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω)
              (y : ℝ) ω ^ q ∂μ := by
          rw [hfun, integral_const_mul]
  calc ∫ ω, ‖normalisedSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
          roughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω m) ^ q ∂μ :=
        integral_rpow_le_integral_rough_sum_sqfree hX rfl (y := y) hx hq0 hq1
    _ ≤ (∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N},
            roughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω m) ^ q ∂μ)
          + ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
            roughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω m) ^ q ∂μ :=
        integral_rpow_split hRa.isBoundedRMF y hx hq0 hq1 N
    _ ≤ (CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
            * (1 + (N : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))) ^ q
          + (Cs / π) ^ q
            * ∫ ω, eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω)
              (y : ℝ) ω ^ q ∂μ :=
        add_le_add (integral_rpow_sum_small_le_sqfree hR hCR hRa hy hx hq0 hq1 hsmallsub
          (fun m hm => ⟨(rough_mem_facts (P := fun m => IsRough y m ∧ m ≤ N) hx hm).1,
            hsmall2 m hm⟩) hβ0 hβ1) hlarge

/-! ### The upper reduction

Harper's Proposition 2, up to the periodisation step. -/

/-- **The upper reduction for the Rademacher RMF.**  The `RMF.reduction_upper_of_core`
instance; the mathematics is there, and all this supplies is
`RMF.reduction_core_rademacher`. -/
theorem reduction_upper_rademacher :
    ∃ (C K c : ℝ) (y₀ : ℕ), 0 < C ∧ 0 ≤ K ∧ 0 < c ∧ 2 ≤ y₀ ∧
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
        ∀ (x : ℝ) (y : ℕ) (q : ℝ), y₀ ≤ y →
          5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ Real.sqrt x / 2 → 0 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ C * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ
              + C * (Real.log y ^ K * Real.exp (-c * Real.log x / Real.log y)) ^ q :=
  reduction_upper_of_core (P := IsRademacherRMF) reduction_core_rademacher

/-! ### Harper's sum-to-max periodisation step, for the Rademacher function

`RMF.integral_rpow_line_le_maxOf` needs three inputs.  The a.e. bound is
`RMF.norm_randomEulerProduct_sqfree_le`; the two measurabilities both come from the joint
measurability below, which the squarefree product makes easy because it is a **finite** product,
entire in `s` — the same reason `RMF.measurable_randomEulerProduct_sqfree_line` needs no
hypothesis on `ω` at all. -/

/-- **The squarefree Euler product is jointly measurable in `(ω, t)` along a vertical line.**

The mirror of `RMF.measurable_eulerClosed_uncurry`, and simpler: each factor `1 + X_p ω p^{-s}` is
a product of a measurable function of `ω` and a continuous function of `t`, with no inversion and
so no nonvanishing side condition. -/
lemma measurable_randomEulerProduct_sqfree_uncurry {X : ℕ → Ω → ℂ}
    (hX : ∀ p : ℕ, p.Prime → Measurable (X p)) (σ : ℝ) (N : ℕ) :
    Measurable fun z : Ω × ℝ =>
      randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
        ((σ : ℂ) + (z.2 : ℂ) * Complex.I) z.1 := by
  have heq : ∀ z : Ω × ℝ,
      randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((σ : ℂ) + (z.2 : ℂ) * Complex.I) z.1
        = ∏ p ∈ Nat.primesBelow N,
            (1 + X p z.1 * (p : ℂ) ^ (-((σ : ℂ) + (z.2 : ℂ) * Complex.I))) := by
    intro z
    rw [randomEulerProduct, eulerProduct_squarefreeExtension]
  simp only [heq]
  refine Finset.measurable_prod _ fun p hp => ?_
  have hp0 : (p : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.prime_of_mem_primesBelow hp).pos.ne'
  have hcont : Continuous fun t : ℝ => (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl hp0)
  exact measurable_const.add
    (((hX p (Nat.prime_of_mem_primesBelow hp)).comp measurable_fst).mul
      (hcont.measurable.comp measurable_snd))

/-- **Harper's sum-to-max step for the Rademacher function**: the `RMF.squarefreeExtension`
instance of `RMF.integral_rpow_line_le_maxOf`.

`S` remains a parameter; `RMF.integral_rpow_line_le_max_rademacher_sup` takes it to be the maximum
over the windows, as in Harper's Propositions 2 and 4. -/
theorem integral_rpow_line_le_max_rademacher {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hX : IsIIDPrimeValues X ν μ)
    (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) (N : ℕ) {c : ℝ} (hc : 0 ≤ c)
    {q : ℝ} (hq0 : 5 / 8 < q) (hq1 : q ≤ 1) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ n : ℤ, (∫ ω, (c * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
        lineSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N ω t) ^ q ∂μ)
      ≤ (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) * S) :
    (∫ ω, (c * ∫ t : ℝ,
        lineDivSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N ω t) ^ q ∂μ)
      ≤ 8 * (∑' n : ℤ, shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)) * S := by
  have huncurry := measurable_randomEulerProduct_sqfree_uncurry
    (X := X) (fun p hp => hX.measurable p hp) σ N
  have hSq : StronglyMeasurable fun z : Ω × ℝ =>
      lineSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N z.1 z.2 := by
    simp only [lineSqOf]
    exact (huncurry.norm.pow_const 2).stronglyMeasurable
  have hDivSq : StronglyMeasurable fun z : Ω × ℝ =>
      lineDivSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N z.1 z.2 := by
    simp only [lineDivSqOf]
    refine ((huncurry.div ?_).norm.pow_const 2).stronglyMeasurable
    exact (Complex.measurable_ofReal.comp measurable_snd).mul_const Complex.I |>.const_add _
  refine integral_rpow_line_le_maxOf (C := eulerBound N) σ hσ N ?_ ?_ ?_ hc hq0 hq1 hS0 hS
  · filter_upwards [ae_forall_norm_le_one hX hν N] with ω hω
    exact ⟨measurable_randomEulerProduct_sqfree_line σ,
      fun t => norm_randomEulerProduct_sqfree_le hω (by simpa using hσ)⟩
  · intro n
    have h := hSq.integral_prod_right' (ν := volume.restrict (Set.Ioc ((n : ℝ)) ((n : ℝ) + 1)))
    exact h.aestronglyMeasurable
  · have h := hDivSq.integral_prod_right' (ν := volume)
    exact h.aestronglyMeasurable

/-- **Harper's sum-to-max step for the Rademacher function, with `S` the actual maximum**
`⨆_n (|n|+1)^{-1/4}·E[(c∫_{window n})^q]`, as in Harper's Propositions 2 and 4.  The hypothesis
of `RMF.integral_rpow_line_le_max_rademacher` becomes `le_ciSup`, which needs the family bounded
above: `RMF.integral_rpow_setIntegral_normSq_shiftLine_le_rademacher` bounds every window's moment
by the height-independent `(E‖F(σ)‖²)^q`, so the supremum is a real number rather than junk. -/
theorem integral_rpow_line_le_max_rademacher_sup {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) (N : ℕ)
    {c : ℝ} (hc : 0 ≤ c) {q : ℝ} (hq0 : 5 / 8 < q) (hq1 : q ≤ 1) :
    (∫ ω, (c * ∫ t : ℝ,
        lineDivSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N ω t) ^ q ∂μ)
      ≤ 8 * (∑' n : ℤ, shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
        * ⨆ n : ℤ, (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4)
            * ∫ ω, (c * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
                lineSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N ω t) ^ q ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hq0' : (0 : ℝ) < q := by linarith
  set E : ℤ → ℝ := fun n => ∫ ω, (c * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
    lineSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N ω t) ^ q ∂μ with hEdef
  set A : ℤ → ℝ := fun n => (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) with hAdef
  set g : ℤ → ℝ := fun n => (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4) * E n with hgdef
  have hbase : ∀ n : ℤ, (0 : ℝ) < |(n : ℝ)| + 1 := fun n => by positivity
  have hA0 : ∀ n, (0 : ℝ) < A n := fun n => Real.rpow_pos_of_pos (hbase n) _
  have hcancel : ∀ n : ℤ, A n * (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4) = 1 := by
    intro n
    rw [hAdef]
    simp only
    rw [← Real.rpow_add (hbase n)]
    norm_num
  have hE0 : ∀ n, (0 : ℝ) ≤ E n := fun n =>
    integral_nonneg fun ω => Real.rpow_nonneg
      (mul_nonneg hc (integral_lineSqOf_nonneg σ (n : ℝ) ((n : ℝ) + 1))) q
  -- every window's moment is bounded by the height-independent second moment
  set B : ℝ := (∫ ω, lineSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N ω 0 ∂μ) ^ q
    with hBdef
  have hline : ∀ (ω : Ω) (t : ℝ),
      lineSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N ω t
        = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
            (shiftLine (σ - 1 / 2) t) ω‖ ^ 2 := by
    intro ω t
    simp only [lineSqOf, shiftLine]
    norm_num
  have hEle : ∀ n : ℤ, E n ≤ c ^ q * B := by
    intro n
    have hsplit : E n = c ^ q * ∫ ω, (∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
        lineSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N ω t) ^ q ∂μ := by
      rw [hEdef, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        Real.mul_rpow hc (integral_lineSqOf_nonneg σ (n : ℝ) ((n : ℝ) + 1)))
    have h111 := integral_rpow_setIntegral_normSq_shiftLine_le_rademacher hX N
      (σ := σ - 1 / 2) (by linarith) (n : ℝ) hq0'.le hq1
    simp only [← hline] at h111
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left h111 (Real.rpow_nonneg hc q)
  have hbdd : BddAbove (Set.range g) := by
    refine ⟨c ^ q * B, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 : (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg ((n : ℝ))]) (by norm_num)
    calc g n ≤ 1 * E n :=
          mul_le_mul_of_nonneg_right h1 (hE0 n)
      _ = E n := one_mul _
      _ ≤ c ^ q * B := hEle n
  have hSge : ∀ n : ℤ, E n ≤ A n * ⨆ m : ℤ, g m := by
    intro n
    have h := le_ciSup hbdd n
    have h2 := mul_le_mul_of_nonneg_left h (hA0 n).le
    calc E n = A n * (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4) * E n := by rw [hcancel n, one_mul]
      _ = A n * g n := by rw [hgdef]; ring
      _ ≤ A n * ⨆ m : ℤ, g m := h2
  have hS0 : (0 : ℝ) ≤ ⨆ m : ℤ, g m :=
    le_trans (mul_nonneg (Real.rpow_nonneg (hbase 0).le _) (hE0 0)) (le_ciSup hbdd 0)
  exact integral_rpow_line_le_max_rademacher hσ hX norm_le_one_rademacherLaw N hc hq0 hq1 hS0 hSge

/-! ### The shape of Harper's Proposition 2

`RMF.reduction_upper_rademacher` is the reduction up to the periodisation step, and
`RMF.integral_rpow_line_le_max_rademacher_sup` is the step.  Composing them gives the Rademacher
twin of `RMF.reduction_upper_unitIntegral`, in the shape of Harper's Proposition 2. -/

/-- **Periodisation for the Rademacher function**, the twin of `RMF.periodisation_upper` with the
sum over translates traded for a maximum: rotation invariance fails for this law, so each window
pays the weight `(|n|+1)^{1/4}` (Harper's "only non-trivial change", §2.4).  This is why it needs
`5/8 < q` where `RMF.periodisation_upper` needs only `1/2 < q`.  `RMF.eulerLineIntegral` at `y` is
`(log y)⁻¹·∫_ℝ lineDivSqOf (1/2)` by definition, so the content is the application. -/
theorem periodisation_upper_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y : ℝ} (hy : 2 ≤ y) {q : ℝ} (hq0 : 5 / 8 < q)
    (hq1 : q ≤ 1) :
    ∫ ω, eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω) y ω ^ q ∂μ
      ≤ 8 * (∑' n : ℤ, shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
        * ⨆ n : ℤ, (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4)
            * ∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
                lineSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω)
                  (⌊y⌋₊ + 1) ω t) ^ q ∂μ := by
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hline : ∀ ω, eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω) y ω
      = (Real.log y)⁻¹ * ∫ t : ℝ,
        lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) (⌊y⌋₊ + 1) ω t :=
    fun _ => rfl
  simp_rw [hline]
  exact integral_rpow_line_le_max_rademacher_sup hX le_rfl (⌊y⌋₊ + 1)
    (inv_nonneg.2 hlog.le) hq0 hq1

/-- **The Rademacher reduction, in the shape of Harper's Proposition 2**; the twin of
`RMF.reduction_upper_unitIntegral`.  For `y ≥ y₀` with `5y(1+log y)³ log y ≤ √x/2` and
`q ∈ [2/3,1]`,

`E|S_x|^{2q} ≤ C·max_{N∈ℤ} (|N|+1)^{-1/4}·E[((log y)⁻¹∫_{N}^{N+1}|F(½+it)|²dt)^q]`
`  + C·((log y)^K e^{-c·log x/log y})^q`,

with `C`, `K`, `c`, `y₀` independent of `X`, `μ`, `x`, `y`, `q`.  Harper writes the maximum with
`(1+|N|)^{-1/8}` against `‖·‖_q^{1/2}`, i.e. `(|N|+1)^{-q/4}` against the `q`-th moment; the weight
`(|N|+1)^{-1/4}` here is smaller.  The composition costs only the weight sum
`8·∑_n w_n(|n|+1)^{1/4}`, bounded uniformly in `q` by its value at `q = 2/3`
(`RMF.tsum_shiftWeight_mul_abs_add_one_rpow_le`), and `5/8 < q` is implied by `2/3 ≤ q`. -/
theorem reduction_upper_max_rademacher :
    ∃ (C K c : ℝ) (y₀ : ℕ), 0 < C ∧ 0 ≤ K ∧ 0 < c ∧ 2 ≤ y₀ ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ (x : ℝ) (y : ℕ) (q : ℝ), y₀ ≤ y →
          5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ Real.sqrt x / 2 → 2 / 3 ≤ q →
          q ≤ 1 →
          ∫ ω, ‖normalisedSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ
            ≤ C * (⨆ n : ℤ, (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4)
                  * ∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
                      lineSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω)
                        (⌊(y : ℝ)⌋₊ + 1) ω t) ^ q ∂μ)
              + C * (Real.log y ^ K * Real.exp (-c * Real.log x / Real.log y)) ^ q := by
  obtain ⟨C, K, c, y₀, hC, hK, hc, hy₀, hred⟩ := reduction_upper_rademacher (Ω := Ω)
  set S : ℝ := ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) with hSdef
  have hS0 : 0 ≤ S :=
    tsum_nonneg fun n =>
      mul_nonneg (shiftWeight_nonneg _ _) (Real.rpow_nonneg (by positivity) _)
  refine ⟨C * (1 + 8 * S), K, c, y₀, by positivity, hK, hc, hy₀, ?_⟩
  intro X μ hX x y q hy₀y hyx hq23 hq1
  haveI := hX.isProbabilityMeasure
  have hy0N : (2 : ℕ) ≤ y := le_trans hy₀ hy₀y
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy0N
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  set M : ℝ := ⨆ n : ℤ, (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4)
      * ∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
          lineSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω)
            (⌊(y : ℝ)⌋₊ + 1) ω t) ^ q ∂μ with hMdef
  have hM0 : (0 : ℝ) ≤ M := by
    rw [hMdef]
    refine Real.iSup_nonneg fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _) ?_
    exact integral_nonneg fun ω => Real.rpow_nonneg
      (mul_nonneg (inv_nonneg.2 hlog.le) (integral_lineSqOf_nonneg _ _ _)) q
  have herr : (0 : ℝ) ≤ (Real.log y ^ K * Real.exp (-c * Real.log x / Real.log y)) ^ q :=
    (Real.rpow_pos_of_pos
      (mul_pos (Real.rpow_pos_of_pos hlog _) (Real.exp_pos _)) q).le
  have hw : (∑' n : ℤ, shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)) ≤ S :=
    tsum_shiftWeight_mul_abs_add_one_rpow_le (by norm_num) hq23
  have hline : ∫ ω, eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω)
      (y : ℝ) ω ^ q ∂μ ≤ (1 + 8 * S) * M := by
    refine (periodisation_upper_rademacher hX hy2 (by linarith) hq1).trans ?_
    rw [← hMdef]
    exact mul_le_mul_of_nonneg_right (by linarith) hM0
  have h1 : C * ∫ ω, eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω)
      (y : ℝ) ω ^ q ∂μ ≤ C * (1 + 8 * S) * M := by
    calc C * ∫ ω, eulerLineIntegral (fun ω => squarefreeExtension fun p => X p ω)
          (y : ℝ) ω ^ q ∂μ
        ≤ C * ((1 + 8 * S) * M) := mul_le_mul_of_nonneg_left hline hC.le
      _ = C * (1 + 8 * S) * M := by ring
  have h2 : C * (Real.log y ^ K * Real.exp (-c * Real.log x / Real.log y)) ^ q
      ≤ C * (1 + 8 * S) * (Real.log y ^ K * Real.exp (-c * Real.log x / Real.log y)) ^ q :=
    mul_le_mul_of_nonneg_right (by nlinarith) herr
  linarith [hred (fun ω => squarefreeExtension fun p => X p ω) μ hX.isRademacherRMF x y q hy₀y hyx
    (by linarith) hq1]

end RMF
