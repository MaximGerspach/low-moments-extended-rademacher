/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Defs
import RMF.Reduction.RademacherLower

/-!
# The weighted sum's lower bound, steps L1–L3: from the moment to the prime mean square

The lower-bound reduction for `S(x) = ∑_{n≤x} f(n)/√n` is Gerspach's Proposition 6 (Gerspach,
*Low pseudomoments of the Riemann zeta function and its powers*, arXiv:1909.10224), itself an
adaptation of Harper's Proposition 3 (Harper, *Moments of random multiplicative functions, I*,
arXiv:1703.06654).  It opens the way Harper's does: pass to the numbers with a prime factor above
`√x` (step L1), and apply Khintchine's inequality conditionally on the small primes (steps
L2–L3).  For the weighted sum that gives

`E|S(x)|^{2q} ≥ 2^{2q-1}·3^{-(1-q)}·E[(∑_{y<p≤x} p^{-1}|S(x/p)|²)^q]`,   `0 < q ≤ ½`,

which is `RMF.khintchine_rough_weighted`.

## How the unweighted machinery is reused

`S(x)` is the unweighted partial sum of the multiplicative function `f·n^{-1/2}`
(`RMF.weightedRademacherSum_eq_sum_pmul`).  So
`RMF.weightedExt v = (squarefreeExtension v)·n^{-1/2}` is an extension in the sense of
`RMF.IsCoeffExtension`, and three things carry over unchanged:

* the factorisation `n = p·m` (`RMF.randomSum_sub_smoothPartial_eq`), for any multiplicative
  function;
* the coefficient map and its a.e. identification (`RMF.roughCoeffOf`, `RMF.ae_roughCoeffOf_eq`);
* the symmetrisation, in its `2q ≤ 1` form (`RMF.integral_rough_le_of_le_oneOf`).

The one thing that does not is Khintchine itself: the linear form is in the *unimodular* values
`f(p)`, not in `f(p)/√p`, so the weight goes into the coefficients,
`C_p = p^{-1/2}·S(x/p)` (`RMF.weightedRoughCoeff`), and `‖C_p‖² = p^{-1}|S(x/p)|²` is where the
`p^{-1}` of the statement comes from.

## Why `q ≤ ½`

Only the symmetrisation sees the range: below `2q = 1` it is subadditivity, with constant
`2^{1-2q}`, where Harper's range `2q ≥ 1` has convexity and constant `1`.  Khintchine holds on the
whole range `0 < q ≤ 1` (`RMF.khintchine_lower_indep_of_pos`).
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The weighted extension -/

/-- `v ↦ (squarefreeExtension v)·n^{-1/2}`: the arithmetic function whose partial sums are the
weighted sums, so that the unweighted rough/smooth machinery applies to it. -/
noncomputable def weightedExt (v : ℕ → ℂ) : ArithmeticFunction ℂ :=
  (squarefreeExtension v).pmul invSqrt

lemma weightedExt_apply (v : ℕ → ℂ) (n : ℕ) :
    weightedExt v n = squarefreeExtension v n * ((Real.sqrt n : ℂ))⁻¹ := by
  rw [weightedExt, ArithmeticFunction.pmul_apply, invSqrt_apply]

omit [MeasurableSpace Ω] in
/-- The weighted sum is the unweighted partial sum of the weighted extension. -/
lemma weightedRademacherSum_eq_randomSum (X : ℕ → Ω → ℂ) (x : ℝ) (ω : Ω) :
    weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω
      = randomSum (fun ω => weightedExt fun p => X p ω) x ω := by
  rw [weightedRademacherSum_eq_sum_pmul]
  rfl

/-- `‖n^{-1/2}‖ ≤ 1`, including at `n = 0`, where the inverse is `0`. -/
lemma norm_inv_sqrt_le_one (n : ℕ) : ‖((Real.sqrt n : ℂ))⁻¹‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by exact_mod_cast hn))

lemma isCoeffExtension_weightedExt : IsCoeffExtension weightedExt where
  congr_primeFactors h := by
    rw [weightedExt_apply, weightedExt_apply, squarefreeExtension_congr h]
  norm_unitize_le v n := by
    rw [weightedExt_apply, norm_mul]
    exact mul_le_one₀ (norm_squarefreeExtension_unitize_le v n) (norm_nonneg _)
      (norm_inv_sqrt_le_one n)
  measurable_unitize_apply k := by
    simp_rw [weightedExt_apply]
    exact (measurable_squarefreeExtension_unitize k).mul_const _

lemma weightedExt_flipSign {v : ℕ → ℂ} {y n : ℕ} (hn : n ≠ 0) (hn2 : n < (y + 1) ^ 2) :
    weightedExt (fun p => flipSign y p * v p) n
      = (if n ∈ Nat.smoothNumbers (y + 1) then (1 : ℂ) else -1) * weightedExt v n := by
  rw [weightedExt_apply, weightedExt_apply, squarefreeExtension_flipSign hn hn2]
  ring

lemma measurable_weightedExt_primeExtend (n : ℕ) :
    Measurable fun v : Nat.Primes → ℂ => weightedExt (primeExtend v) n := by
  simp_rw [weightedExt_apply]
  exact (measurable_squarefreeExtension_primeExtend n).mul_const _

lemma weightedExt_congr_primes {v w : ℕ → ℂ} (h : ∀ p, p.Prime → v p = w p) :
    weightedExt v = weightedExt w := by
  rw [weightedExt, weightedExt, squarefreeExtension_congr_primes h]

lemma isMultiplicative_weightedExt (v : ℕ → ℂ) : (weightedExt v).IsMultiplicative :=
  (isMultiplicative_squarefreeExtension v).pmul isMultiplicative_invSqrt

/-- **The mean square of a weighted block.**  Over any finite set `s` of nonzero indices,
`E‖∑_{n∈s} f(n)/√n‖² = ∑_{n∈s squarefree} 1/n` — orthogonality, with the weights squared. -/
theorem integral_normSq_sum_weightedExt {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) :
    (∫ ω, ‖∑ n ∈ s, weightedExt (fun p => X p ω) n‖ ^ 2 ∂μ)
      = ∑ m ∈ s, (if Squarefree m then (m : ℝ)⁻¹ else 0) := by
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have key := integral_normSq_weightedSum_of_orthogonality'
    (c := fun n : ℕ => ((Real.sqrt n : ℂ))⁻¹)
    (d := fun m => if Squarefree m then 1 else 0)
    (fun m _ n _ => hf.integrable_mul_conj m n)
    (fun m hm n hn => by
      rw [hf.orthogonality (hs m hm) (hs n hn)]
      by_cases h : m = n
      · subst h; simp
      · simp [h])
  have hsum : ∀ ω, (∑ n ∈ s, weightedExt (fun p => X p ω) n)
      = ∑ n ∈ s, ((Real.sqrt n : ℂ))⁻¹ * squarefreeExtension (fun p => X p ω) n :=
    fun ω => Finset.sum_congr rfl fun n _ => by rw [weightedExt_apply, mul_comm]
  simp_rw [hsum]
  rw [← Complex.ofReal_inj, key, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (hs m hm)
  have hnorm : ‖((Real.sqrt m : ℂ))⁻¹‖ = (Real.sqrt m)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  by_cases h : Squarefree m
  · rw [if_pos h, if_pos h, mul_one, hnorm, ← Complex.ofReal_pow, ← Real.sqrt_inv,
      Real.sq_sqrt (by positivity)]
  · rw [if_neg h, if_neg h, mul_zero, Complex.ofReal_zero]

/-- The weighted Rademacher function is bounded: `‖f(n)/√n‖ ≤ 1`, and over any finite set of
nonzero indices the second moment `∑_{n squarefree} 1/n` is at most the number of terms. -/
lemma isBoundedRMF_weightedExt {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) :
    IsBoundedRMF (fun ω => weightedExt fun p => X p ω) μ where
  measurable_apply n := by
    simp_rw [weightedExt_apply]
    exact ((IsRademacherRMF.measurable_apply hX.isRademacherRMF) n).mul_const _
  ae_norm_le_one n := by
    filter_upwards [(IsRademacherRMF.norm_apply_le_one hX.isRademacherRMF) n] with ω hω
    rw [weightedExt_apply, norm_mul]
    exact mul_le_one₀ hω (norm_nonneg _) (norm_inv_sqrt_le_one n)
  integral_normSq_sum_le s hs := by
    rw [integral_normSq_sum_weightedExt hX hs]
    calc ∑ m ∈ s, (if Squarefree m then (m : ℝ)⁻¹ else 0) ≤ ∑ _m ∈ s, (1 : ℝ) := by
          refine Finset.sum_le_sum fun m hm => ?_
          split_ifs
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (hs m hm))
          · norm_num
      _ = s.card := by simp

/-! ### Step L1: the rough part -/

/-- **Step L1 for the weighted sum**: the `RMF.weightedExt` instance of
`RMF.integral_rough_le_of_le_oneOf`, for `0 < q ≤ ½`. -/
theorem integral_rough_le_weighted {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} {y : ℕ} (hxy : ⌊x⌋₊ < (y + 1) ^ 2)
    {q : ℝ} (hq0 : 0 < q) (hq1 : 2 * q ≤ 1) :
    (∫ ω, ‖randomSum (fun ω => weightedExt fun p => X p ω) x ω
        - smoothPartial (fun ω => weightedExt fun p => X p ω) y x ω‖ ^ (2 * q) ∂μ)
      ≤ 2 ^ (1 - 2 * q)
          * ∫ ω, ‖randomSum (fun ω => weightedExt fun p => X p ω) x ω‖ ^ (2 * q) ∂μ :=
  integral_rough_le_of_le_oneOf hX
    (fun p _ => map_mul_left_rademacherLaw (flipSign_eq_one_or_neg_one y p))
    (fun _ _ hn hn2 => weightedExt_flipSign hn hn2)
    (fun _ hY => isBoundedRMF_weightedExt hY)
    measurable_weightedExt_primeExtend (fun h => weightedExt_congr_primes h) hxy hq0 hq1

/-! ### Steps L2–L3: Khintchine, with the weight in the coefficients -/

/-- The coefficient of the large prime `p`: `p^{-1/2}` times the weighted partial sum, up to
`x/p`, of the unitised small-prime data. -/
noncomputable def weightedRoughCoeff (x : ℝ) (v : ℕ → ℂ) (p : ℕ) : ℂ :=
  ((Real.sqrt p : ℂ))⁻¹ * roughCoeffOf weightedExt x v p

lemma measurable_weightedRoughCoeff (x : ℝ) (p : ℕ) :
    Measurable fun v : ℕ → ℂ => weightedRoughCoeff x v p :=
  (measurable_roughCoeffOf isCoeffExtension_weightedExt x p).const_mul _

lemma norm_weightedRoughCoeff_le {x : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : 1 ≤ p) (v : ℕ → ℂ) :
    ‖weightedRoughCoeff x v p‖ ≤ (⌊x⌋₊ : ℝ) := by
  rw [weightedRoughCoeff, norm_mul]
  calc ‖((Real.sqrt p : ℂ))⁻¹‖ * ‖roughCoeffOf weightedExt x v p‖
      ≤ 1 * (⌊x⌋₊ : ℝ) :=
        mul_le_mul (norm_inv_sqrt_le_one p)
          (norm_roughCoeffOf_le isCoeffExtension_weightedExt hx hp v) (norm_nonneg _)
          zero_le_one
    _ = (⌊x⌋₊ : ℝ) := one_mul _

/-- **Steps L1–L3 for the weighted sum.**  For `⌊x⌋ < (y+1)²` and `0 < q ≤ ½`,

`3^{-(1-q)}·E[(∑_{y<p≤x} p^{-1}|S(x/p)|²)^q] ≤ 2^{1-2q}·E|S(x)|^{2q}`.

The first two steps of Gerspach's Proposition 6: symmetrisation (with the sign flip in place of
his auxiliary Rademacher variable) and Khintchine conditionally on the primes up to `y`. -/
theorem khintchine_rough_weighted {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} {y : ℕ} (hx : 1 ≤ x)
    (hxy : ⌊x⌋₊ < (y + 1) ^ 2) {q : ℝ} (hq0 : 0 < q) (hq1 : 2 * q ≤ 1) :
    (3 : ℝ) ^ (-(1 - q)) * ∫ ω, (∑ p ∈ largePrimeSet y ⌊x⌋₊, (p : ℝ)⁻¹
        * ‖weightedRademacherSum (fun ω => squarefreeExtension fun r => X r ω) (x / p) ω‖ ^ 2)
          ^ q ∂μ
      ≤ 2 ^ (1 - 2 * q) * ∫ ω, ‖weightedRademacherSum
          (fun ω => squarefreeExtension fun r => X r ω) x ω‖ ^ (2 * q) ∂μ := by
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun r => X r ω with hfdef
  set g : Ω → ArithmeticFunction ℂ := fun ω => weightedExt fun r => X r ω with hgdef
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set s : Finset ℕ := largePrimeSet y ⌊x⌋₊ with hsdef
  have hs : ∀ p ∈ s, Nat.Prime p := fun p hp => (mem_largePrimeSet.1 hp).2
  -- the two data maps
  set W : Ω → (ℕ → ℂ) := fun ω =>
    primeRestrict (smallPrimes y) fun i : smallPrimes y => X ((i : Nat.Primes) : ℕ) ω with hWdef
  have hW : Measurable W :=
    (measurable_primeRestrict _).comp
      (measurable_pi_lambda _ fun i => hX.measurable ((i : Nat.Primes) : ℕ)
        (i : Nat.Primes).2)
  have hZ : (fun ω n => if n ∈ s then f ω n else 0)
      = fun ω => primeRestrict (largePrimes y ⌊x⌋₊)
          fun i : largePrimes y ⌊x⌋₊ => X ((i : Nat.Primes) : ℕ) ω := by
    funext ω
    rw [primeRestrict_largePrimes_eqOf (fun v _ hp => squarefreeExtension_apply_prime v hp)]
  have hind : IndepFun W (fun ω n => if n ∈ s then f ω n else 0) μ := by
    rw [hZ]
    exact indepFun_primeRestrict hX _ _ (disjoint_smallPrimes_largePrimes y ⌊x⌋₊)
  -- Khintchine, on the whole range `0 < q ≤ 1`
  have hkh := khintchine_lower_indep_of_pos hX.isRademacherRMF.isOrthonormalAtPrimes
    hs hW (C := weightedRoughCoeff x) (fun p => measurable_weightedRoughCoeff x p)
    (by norm_num : (0 : ℝ) < 3)
    (fun v => integral_norm_rpow_four_primeLinearForm_le_sqfree hX hs (weightedRoughCoeff x v))
    (B := (⌊x⌋₊ : ℝ))
    (fun v p hp => norm_weightedRoughCoeff_le hx0 (hs p hp).one_lt.le v) hind hq0 (by linarith)
  -- identify the coefficients
  have hae := ae_roughCoeffOf_eq isCoeffExtension_weightedExt hX norm_eq_one_rademacherLaw hx hxy
  have hcoeff : ∀ᵐ ω ∂μ, ∀ p ∈ s,
      weightedRoughCoeff x (W ω) p
        = ((Real.sqrt p : ℂ))⁻¹ * weightedRademacherSum f (x / p) ω := by
    filter_upwards [hae] with ω hω
    intro p hp
    obtain ⟨⟨hy, _⟩, hprime⟩ := mem_largePrimeSet.1 hp
    rw [weightedRoughCoeff, hω p hprime hy, hfdef, weightedRademacherSum_eq_randomSum]
  have hL : (∫ ω, (∑ p ∈ s, ‖weightedRoughCoeff x (W ω) p‖ ^ 2) ^ q ∂μ)
      = ∫ ω, (∑ p ∈ s, (p : ℝ)⁻¹ * ‖weightedRademacherSum f (x / p) ω‖ ^ 2) ^ q ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hcoeff] with ω hω
    refine congrArg (· ^ q) (Finset.sum_congr rfl fun p hp => ?_)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hs p hp).pos
    rw [hω p hp, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hp0.le]
  have hR : (∫ ω, ‖∑ p ∈ s, weightedRoughCoeff x (W ω) p * f ω p‖ ^ (2 * q) ∂μ)
      ≤ 2 ^ (1 - 2 * q) * ∫ ω, ‖weightedRademacherSum f x ω‖ ^ (2 * q) ∂μ := by
    have hS : (∫ ω, ‖weightedRademacherSum f x ω‖ ^ (2 * q) ∂μ)
        = ∫ ω, ‖randomSum g x ω‖ ^ (2 * q) ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [hfdef, hgdef, weightedRademacherSum_eq_randomSum]
    rw [hS]
    refine le_trans (le_of_eq (integral_congr_ae ?_)) (integral_rough_le_weighted hX hxy hq0 hq1)
    filter_upwards [hcoeff] with ω hω
    have hsum : (∑ p ∈ s, weightedRoughCoeff x (W ω) p * f ω p)
        = ∑ p ∈ s, g ω p * randomSum g (x / p) ω := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [hω p hp, hgdef, weightedExt_apply, hfdef, weightedRademacherSum_eq_randomSum,
        squarefreeExtension_apply_prime _ (hs p hp)]
      ring
    have hset : s = {p ∈ Finset.Icc 1 ⌊x⌋₊ | p.Prime ∧ y < p} := by
      ext p
      rw [hsdef, mem_largePrimeSet, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hy, hN⟩, hp⟩
        exact ⟨⟨hp.one_lt.le, hN⟩, hp, hy⟩
      · rintro ⟨⟨_, hN⟩, hp, hy⟩
        exact ⟨⟨hy, hN⟩, hp⟩
    rw [hsum, hset, ← randomSum_sub_smoothPartial_eq (f := g) hx hxy
      (isMultiplicative_weightedExt _)]
  rw [hL] at hkh
  exact le_trans hkh hR

end RMF
