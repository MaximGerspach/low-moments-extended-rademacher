/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import RMF.Basic
import RMF.NumberTheory.SquarefreeCount

/-!
# Second and low moments of a random multiplicative function

For both classical models the partial sum `∑_{n ≤ N} f n` has mean square of order `N`:

* Steinhaus: `∫ ‖∑_{n ≤ N} f n‖ ^ 2 = N` exactly (`IsSteinhausRMF.second_moment`);
* Rademacher: the same integral counts the squarefree integers up to `N`
  (`IsRademacherRMF.second_moment`), hence equals `6/π² · N` up to `3√N`
  (`RMF.abs_squarefreeCount_sub_le`), and is at most `N`.

Both rest on orthogonality of the values, which comes from
`RMF.IsIIDPrimeValues.integral_compMultExtension_mul_conj` — cross moments factor over the
primes dividing `m * n`, using independence alone — together with one computation for the
law at a single prime.  For the Steinhaus law that computation is the orthogonality of the
characters `z ↦ z ^ a` (`integral_pow_mul_conj_steinhausLaw`); for the Rademacher law it is
a parity count (`integral_pow_mul_conj_rademacherLaw`).

The Rademacher function is orthogonal *only* because its exponents are `0` or `1`, where
parity of `a + b` detects `a = b`.  The completely multiplicative variant is not orthogonal:
`f 1 * conj (f 4) = 1`, since `f 4 = f 2 ^ 2 = 1`.

For low moments the file provides Jensen's inequality for the concave map `t ↦ t ^ q`,
`0 ≤ q ≤ 1` (`integral_rpow_le_rpow_integral`), with which the second moment bounds the `2q`-th
moment by `N ^ q`, and Paley–Zygmund (`rpow_integral_div_rpow_integral_sq_le_integral_rpow`).

The `√N` first moment is the trivial bound Harper's theorem improves, showing the Steinhaus
first moment to be of order `√N / (log log N) ^ (1/4)`.
-/

open MeasureTheory ProbabilityTheory Real Complex

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Two nonzero naturals are equal as soon as their factorizations agree at every prime
dividing their product. -/
lemma eq_of_factorization_agree {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : ∀ p ∈ (m * n).primeFactors, m.factorization p = n.factorization p) : m = n := by
  refine Nat.eq_of_factorization_eq hm hn fun q => ?_
  by_cases hq : q ∈ (m * n).primeFactors
  · exact h q hq
  · rw [Nat.primeFactors_mul hm hn, Finset.mem_union] at hq
    have h1 : m.factorization q = 0 :=
      Finsupp.notMem_support_iff.1 (by simp only [Nat.support_factorization]; tauto)
    have h2 : n.factorization q = 0 :=
      Finsupp.notMem_support_iff.1 (by simp only [Nat.support_factorization]; tauto)
    rw [h1, h2]

/-! ### Orthogonality of the random multiplicative function -/

/-- **Orthogonality**: the values of a Steinhaus random multiplicative function at distinct
integers are orthogonal, and each has unit `L²` norm.

The values at the primes are independent, so the expectation factors into one character integral
(`integral_pow_mul_conj_steinhausLaw`) per prime dividing `m * n`, and the factors are all `1`
exactly when the two factorizations agree. -/
theorem IsSteinhausRMF.orthogonality {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (∫ ω, f ω m * (starRingEnd ℂ) (f ω n) ∂μ) = if m = n then 1 else 0 := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  rw [hX.integral_compMultExtension_mul_conj hm hn]
  simp only [integral_pow_mul_conj_steinhausLaw]
  rcases eq_or_ne m n with rfl | hne
  · simp
  · rw [if_neg hne]
    obtain ⟨p, hpS, hp⟩ : ∃ p ∈ (m * n).primeFactors,
        m.factorization p ≠ n.factorization p := by
      by_contra hcon
      exact hne (eq_of_factorization_agree hm hn fun q hq => by
        by_contra hne2; exact hcon ⟨q, hq, hne2⟩)
    exact Finset.prod_eq_zero hpS (by simp [hp])

/-- Each value of a Steinhaus random multiplicative function has modulus one: the value at
`n` is a product of unit-modulus factors, one per prime dividing `n`. -/
theorem IsSteinhausRMF.norm_apply {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) {n : ℕ} (hn : n ≠ 0) : ∀ᵐ ω ∂μ, ‖f ω n‖ = 1 := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have hmeasP : Measurable fun z : ℂ => ‖z‖ = 1 :=
    measurableSet_setOf.1 (measurable_norm (measurableSet_singleton 1))
  have hprimes : ∀ p ∈ n.primeFactors, ∀ᵐ ω ∂μ, ‖X p ω‖ = 1 := fun p hp =>
    ((hX.hasLaw p (Nat.prime_of_mem_primeFactors hp)).ae_iff hmeasP).2 norm_eq_one_steinhausLaw
  filter_upwards [(Filter.eventually_all_finset n.primeFactors).2 hprimes] with ω hω
  rw [compMultExtension_apply_of_ne_zero _ hn, Finsupp.prod, Nat.support_factorization, norm_prod]
  exact Finset.prod_eq_one fun p hp => by rw [norm_pow, hω p hp, one_pow]

/-- Cross terms of the partial sum are integrable: they are unit-modulus on a probability
space. -/
lemma IsSteinhausRMF.integrable_mul_conj {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hf : IsSteinhausRMF f μ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    Integrable (fun ω => f ω m * (starRingEnd ℂ) (f ω n)) μ := by
  have hm1 := hf.measurable_apply m
  have hm2 := hf.measurable_apply n
  have hmeas : AEStronglyMeasurable (fun ω => f ω m * (starRingEnd ℂ) (f ω n)) μ := by fun_prop
  have hb : ∀ᵐ ω ∂μ, ‖f ω m * (starRingEnd ℂ) (f ω n)‖ ≤ 1 := by
    filter_upwards [hf.norm_apply hm, hf.norm_apply hn] with ω h1 h2
    rw [norm_mul, Complex.norm_conj, h1, h2, one_mul]
  exact (memLp_top_of_bound hmeas 1 hb).integrable le_top

/-! ### The second moment -/

/-- The partial sum `∑_{n ≤ N} f(n)` of a random multiplicative function. -/
noncomputable def partialSum (f : Ω → ArithmeticFunction ℂ) (N : ℕ) (ω : Ω) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, f ω n

/-- **The second moment from orthogonality data.**  If the cross moments vanish off the
diagonal and equal `d m` on it, the second moment of the partial sum is `∑_{m ≤ N} d m`.
This is the law-independent half of the second-moment computation. -/
theorem integral_norm_partialSum_sq_of_orthogonality {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} {d : ℕ → ℂ} {N : ℕ}
    (hint : ∀ m ∈ Finset.Icc 1 N, ∀ n ∈ Finset.Icc 1 N,
      Integrable (fun ω => f ω m * (starRingEnd ℂ) (f ω n)) μ)
    (horth : ∀ m ∈ Finset.Icc 1 N, ∀ n ∈ Finset.Icc 1 N,
      (∫ ω, f ω m * (starRingEnd ℂ) (f ω n) ∂μ) = if m = n then d m else 0) :
    ((∫ ω, ‖partialSum f N ω‖ ^ 2 ∂μ : ℝ) : ℂ) = ∑ m ∈ Finset.Icc 1 N, d m := by
  have hpt : ∀ ω, ((‖partialSum f N ω‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, f ω m * (starRingEnd ℂ) (f ω n) := by
    intro ω
    rw [Complex.ofReal_pow, ← Complex.mul_conj', partialSum, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]
  have hcast : ((∫ ω, ‖partialSum f N ω‖ ^ 2 ∂μ : ℝ) : ℂ)
      = ∫ ω, ((‖partialSum f N ω‖ ^ 2 : ℝ) : ℂ) ∂μ := (integral_complex_ofReal).symm
  rw [hcast]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m hm => integrable_finsetSum _ fun n hn => hint m hm n hn]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [integral_finsetSum _ fun n hn => hint m hm n hn,
    Finset.sum_congr rfl fun n hn => horth m hm n hn, Finset.sum_ite_eq]
  simp [hm]

/-- **Exact square-root cancellation in mean square**: the second moment of the partial sum
of a Steinhaus random multiplicative function is exactly the number of terms.  Expand the
square and apply `IsSteinhausRMF.orthogonality` to each of the `N ^ 2` cross terms.

Harper's theorem says the *first* absolute moment is smaller than this suggests: of order
`√N / (log log N) ^ (1/4)` rather than `√N`. -/
theorem IsSteinhausRMF.second_moment {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsSteinhausRMF f μ) (N : ℕ) :
    (∫ ω, ‖partialSum f N ω‖ ^ 2 ∂μ) = N := by
  have hne : ∀ m ∈ Finset.Icc 1 N, m ≠ 0 := fun m hm => by
    have := (Finset.mem_Icc.1 hm).1; omega
  have key := integral_norm_partialSum_sq_of_orthogonality (d := fun _ => (1 : ℂ))
    (fun m hm n hn => hf.integrable_mul_conj (hne m hm) (hne n hn))
    (fun m hm n hn => hf.orthogonality (hne m hm) (hne n hn))
  rw [Finset.sum_const, Nat.card_Icc] at key
  simp only [Nat.add_sub_cancel, nsmul_eq_mul, mul_one] at key
  exact_mod_cast key

/-! ### The Rademacher case

The Rademacher function vanishes off the squarefree integers, so its second moment counts
squarefree numbers rather than all of them.
-/

/-- **The second moment of a sum over a finite index set `s`**, in terms of the diagonal values `d`
of the orthogonality relation: `E‖∑_{n∈s} f n‖² = ∑_{m∈s} d m`.

`RMF.integral_norm_partialSum_sq_of_orthogonality` is the case `s = [1,N]`; the reduction needs
the `y`-smooth subset.  Carrying `d` lets both laws use it: Steinhaus has `d ≡ 1`, Rademacher has
`d m = 1` exactly on the squarefrees. -/
theorem integral_normSq_sum_of_orthogonality' {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    {d : ℕ → ℂ} {s : Finset ℕ}
    (hint : ∀ m ∈ s, ∀ n ∈ s, Integrable (fun ω => f ω m * (starRingEnd ℂ) (f ω n)) μ)
    (horth : ∀ m ∈ s, ∀ n ∈ s,
      (∫ ω, f ω m * (starRingEnd ℂ) (f ω n) ∂μ) = if m = n then d m else 0) :
    ((∫ ω, ‖∑ n ∈ s, f ω n‖ ^ 2 ∂μ : ℝ) : ℂ) = ∑ m ∈ s, d m := by
  have hpt : ∀ ω : Ω, ((‖∑ n ∈ s, f ω n‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ s, ∑ n ∈ s, f ω m * (starRingEnd ℂ) (f ω n) := by
    intro ω
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]
  have hcast : ((∫ ω, ‖∑ n ∈ s, f ω n‖ ^ 2 ∂μ : ℝ) : ℂ)
      = ∫ ω, ((‖∑ n ∈ s, f ω n‖ ^ 2 : ℝ) : ℂ) ∂μ := integral_complex_ofReal.symm
  have hrow : ∀ m ∈ s, (∫ ω, ∑ n ∈ s, f ω m * (starRingEnd ℂ) (f ω n) ∂μ) = d m := by
    intro m hm
    rw [integral_finsetSum _ fun n hn => hint m hm n hn,
      Finset.sum_congr rfl fun n hn => horth m hm n hn, Finset.sum_ite_eq]
    simp [hm]
  rw [hcast]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m hm =>
    integrable_finsetSum _ fun n hn => hint m hm n hn, Finset.sum_congr rfl hrow]

/-- The second moment of a sum over an arbitrary set of nonzero indices is its cardinality.
The `d ≡ 1` instance of `RMF.integral_normSq_sum_of_orthogonality'`. -/
theorem integral_normSq_sum_of_orthogonality {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsSteinhausRMF f μ) {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) :
    (∫ ω, ‖∑ n ∈ s, f ω n‖ ^ 2 ∂μ) = s.card := by
  have key := integral_normSq_sum_of_orthogonality' (d := fun _ => (1 : ℂ))
    (fun m hm n hn => hf.integrable_mul_conj (hs m hm) (hs n hn))
    (fun m hm n hn => hf.orthogonality (hs m hm) (hs n hn))
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at key
  exact_mod_cast key

/-- Moments of the Rademacher law.  It is carried by the reals `±1`, where
`z ^ a * conj (z ^ b) = z ^ (a + b)`, averaging to `1` for an even exponent and `0` for an
odd one. -/
lemma integral_pow_mul_conj_rademacherLaw (a b : ℕ) :
    (∫ z, z ^ a * (starRingEnd ℂ) (z ^ b) ∂rademacherLaw) = if Even (a + b) then 1 else 0 := by
  have h2 : ((-1 : ℂ) ^ a * (starRingEnd ℂ) ((-1 : ℂ) ^ b)) = (-1) ^ (a + b) := by
    rw [map_pow, map_neg, map_one, pow_add]
  rw [rademacherLaw, integral_smul_measure,
    integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
    integral_dirac, integral_dirac, h2]
  rcases Nat.even_or_odd (a + b) with h | h
  · rw [if_pos h, h.neg_one_pow]
    simp
    norm_num
  · rw [if_neg (Nat.not_even_iff_odd.2 h), h.neg_one_pow]
    simp

/-- For exponents that are at most one — the squarefree case — parity of the sum detects
equality. -/
private lemma even_add_iff_eq_of_le_one {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) :
    Even (a + b) ↔ a = b := by
  interval_cases a <;> interval_cases b <;> simp

/-- **Orthogonality for the Rademacher function.**  Values at distinct integers are
orthogonal, and the value at `n` is a unit vector exactly when `n` is squarefree; off the
squarefrees the function vanishes. -/
theorem IsRademacherRMF.orthogonality {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (∫ ω, f ω m * (starRingEnd ℂ) (f ω n) ∂μ) = if m = n ∧ Squarefree m then 1 else 0 := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  by_cases hsm : Squarefree m
  · by_cases hsn : Squarefree n
    · have hconv : ∀ ω : Ω, squarefreeExtension (fun p => X p ω) m
          * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) n)
          = compMultExtension (fun p => X p ω) m
            * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) n) := fun ω => by
        rw [compMultExtension_eq_squarefreeExtension_of_squarefree _ hsm,
          compMultExtension_eq_squarefreeExtension_of_squarefree _ hsn]
      simp_rw [hconv]
      rw [hX.integral_compMultExtension_mul_conj hm hn]
      simp only [integral_pow_mul_conj_rademacherLaw]
      rw [Finset.prod_congr rfl fun p _ => if_congr
        (even_add_iff_eq_of_le_one ((Nat.squarefree_iff_factorization_le_one hm).1 hsm p)
          ((Nat.squarefree_iff_factorization_le_one hn).1 hsn p)) rfl rfl]
      rcases eq_or_ne m n with rfl | hne
      · simp [hsm]
      · rw [if_neg (by tauto)]
        obtain ⟨p, hpS, hp⟩ : ∃ p ∈ (m * n).primeFactors,
            m.factorization p ≠ n.factorization p := by
          by_contra hcon
          exact hne (eq_of_factorization_agree hm hn fun q hq => by
            by_contra hne2; exact hcon ⟨q, hq, hne2⟩)
        exact Finset.prod_eq_zero hpS (by simp [hp])
    · simp only [squarefreeExtension_apply_of_not_squarefree _ hsn, map_zero, mul_zero,
        integral_zero]
      rw [if_neg]
      rintro ⟨rfl, -⟩
      exact hsn hsm
  · simp only [squarefreeExtension_apply_of_not_squarefree _ hsm, zero_mul, integral_zero]
    rw [if_neg (by tauto)]

/-! ### The second moment of the Rademacher function -/

/-- Values of a Rademacher random multiplicative function have modulus at most one: they
are `±1` on the squarefrees and `0` elsewhere. -/
lemma IsRademacherRMF.norm_apply_le_one {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (n : ℕ) : ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  by_cases hn : Squarefree n
  · have hmeasP : Measurable fun z : ℂ => ‖z‖ ≤ 1 :=
      measurableSet_setOf.1 (measurableSet_le measurable_norm measurable_const)
    have hprimes : ∀ p ∈ n.primeFactors, ∀ᵐ ω ∂μ, ‖X p ω‖ ≤ 1 := fun p hp =>
      ((hX.hasLaw p (Nat.prime_of_mem_primeFactors hp)).ae_iff hmeasP).2 norm_le_one_rademacherLaw
    filter_upwards [(Filter.eventually_all_finset n.primeFactors).2 hprimes] with ω hω
    rw [squarefreeExtension_apply_of_squarefree _ hn, norm_prod]
    exact Finset.prod_le_one (fun p _ => norm_nonneg _) fun p hp => hω p hp
  · filter_upwards with ω
    simp [squarefreeExtension_apply_of_not_squarefree _ hn]

lemma IsRademacherRMF.integrable_mul_conj {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hf : IsRademacherRMF f μ) (m n : ℕ) :
    Integrable (fun ω => f ω m * (starRingEnd ℂ) (f ω n)) μ := by
  have hm1 := hf.measurable_apply m
  have hm2 := hf.measurable_apply n
  have hmeas : AEStronglyMeasurable (fun ω => f ω m * (starRingEnd ℂ) (f ω n)) μ := by fun_prop
  have hb : ∀ᵐ ω ∂μ, ‖f ω m * (starRingEnd ℂ) (f ω n)‖ ≤ 1 := by
    filter_upwards [hf.norm_apply_le_one m, hf.norm_apply_le_one n] with ω h1 h2
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ h1 (norm_nonneg _) h2
  exact (memLp_top_of_bound hmeas 1 hb).integrable le_top

/-- **The second moment of the Rademacher function counts squarefree integers.**  Unlike the
Steinhaus case the answer is not `N`: the function vanishes off the squarefrees, so only
those contribute to the diagonal.  The count is `6/π² · N + O(√N)`
(`RMF.abs_squarefreeCount_sub_le`, in `RMF/NumberTheory/SquarefreeCount.lean`). -/
theorem IsRademacherRMF.second_moment {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsRademacherRMF f μ) (N : ℕ) :
    (∫ ω, ‖partialSum f N ω‖ ^ 2 ∂μ) = ((Finset.Icc 1 N).filter Squarefree).card := by
  have hne : ∀ m ∈ Finset.Icc 1 N, m ≠ 0 := fun m hm => by
    have := (Finset.mem_Icc.1 hm).1; omega
  have key := integral_norm_partialSum_sq_of_orthogonality
    (d := fun m => if Squarefree m then (1 : ℂ) else 0)
    (fun m _ n _ => hf.integrable_mul_conj m n)
    (fun m hm n hn => by
      rw [hf.orthogonality (hne m hm) (hne n hn)]
      by_cases h : m = n <;> simp [h])
  rw [Finset.sum_boole] at key
  exact_mod_cast key

/-- **The second moment over an arbitrary set of nonzero indices, Rademacher.**  Only the
squarefree indices contribute, so the count is of those.  The `d m = [m squarefree]` instance of
`RMF.integral_normSq_sum_of_orthogonality'`. -/
theorem IsRademacherRMF.integral_normSq_sum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsRademacherRMF f μ) {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) :
    (∫ ω, ‖∑ n ∈ s, f ω n‖ ^ 2 ∂μ) = (s.filter Squarefree).card := by
  have key := integral_normSq_sum_of_orthogonality'
    (d := fun m => if Squarefree m then (1 : ℂ) else 0)
    (fun m _ n _ => hf.integrable_mul_conj m n)
    (fun m hm n hn => by
      rw [hf.orthogonality (hs m hm) (hs n hn)]
      by_cases h : m = n <;> simp [h])
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] at key
  exact_mod_cast key

/-- **The bound the reduction uses**: the squarefree indices are a subset, so the Rademacher second
moment over any index set is at most the Steinhaus one.  This is why the *upper* bound needs no
new number theory — the same Rankin estimate applies to the smaller count. -/
theorem IsRademacherRMF.integral_normSq_sum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsRademacherRMF f μ) {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) :
    (∫ ω, ‖∑ n ∈ s, f ω n‖ ^ 2 ∂μ) ≤ s.card := by
  rw [hf.integral_normSq_sum hs]
  exact_mod_cast Finset.card_filter_le _ _

/-! ### Low moments

Tools for passing from second moments to `q`-th moments, `0 ≤ q ≤ 1`, on a probability space:
Jensen's inequality for the concave map `t ↦ t ^ q` and its integrability side conditions.  With
the second moments above they give the trivial bound `N ^ q` on the `2q`-th moment of a partial
sum, which Harper's theorem improves.
-/

/-- A partial sum of `N` terms of modulus at most one has norm at most `N`. -/
lemma norm_partialSum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} {N : ℕ}
    (hbdd : ∀ n ∈ Finset.Icc 1 N, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1) :
    ∀ᵐ ω ∂μ, ‖partialSum f N ω‖ ≤ (N : ℝ) := by
  filter_upwards [(Filter.eventually_all_finset (Finset.Icc 1 N)).2 hbdd] with ω hω
  calc ‖partialSum f N ω‖ ≤ ∑ n ∈ Finset.Icc 1 N, ‖f ω n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := Finset.sum_le_sum fun n hn => hω n hn
    _ = (N : ℝ) := by simp

omit [MeasurableSpace Ω] in
/-- `t^q ≤ 1 + t` for `t ≥ 0` and `0 ≤ q ≤ 1` — the crude bound that makes `q`-th powers
integrable on a probability space without any boundedness input. -/
lemma rpow_le_one_add {t q : ℝ} (ht : 0 ≤ t) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : t ^ q ≤ 1 + t := by
  rcases le_or_gt t 1 with h | h
  · have hle : t ^ q ≤ (1 : ℝ) ^ q := Real.rpow_le_rpow ht h hq0
    rw [Real.one_rpow] at hle
    linarith
  · have hle : t ^ q ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le hq1
    rw [Real.rpow_one] at hle
    linarith

omit [MeasurableSpace Ω] in
/-- `a^q ≤ \max\{1, a\}` for `0 ≤ q ≤ 1`: the device that keeps a constant free of `q`.  It is
used wherever a bound of the form `C · M` is raised to the power `q` and the `C^q` has to be
absorbed. -/
lemma rpow_le_max_one {a q : ℝ} (ha : 0 < a) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    a ^ q ≤ max 1 a := by
  rcases le_total a 1 with h | h
  · refine le_trans ?_ (le_max_left 1 a)
    calc a ^ q ≤ a ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ha h hq0
      _ = 1 := Real.rpow_zero a
  · refine le_trans ?_ (le_max_right 1 a)
    calc a ^ q ≤ a ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hq1
      _ = a := Real.rpow_one a

/-- The `q`-th power of a nonnegative integrable function is integrable, `0 ≤ q ≤ 1`.  This is the
side condition the next lemma asks for, and it is why that hypothesis is never an obstacle: on a
probability space no boundedness of `g` is needed. -/
lemma integrable_rpow_of_integrable {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ}
    {q : ℝ} (hg : Integrable g μ) (h0 : 0 ≤ᵐ[μ] g) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Integrable (fun ω => g ω ^ q) μ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hg)
    ((Real.continuous_rpow_const hq0).comp_aestronglyMeasurable hg.aestronglyMeasurable) ?_
  filter_upwards [h0] with ω h1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h1 q)]
  exact rpow_le_one_add h1 hq0 hq1

/-- **Jensen's inequality** for the concave map `t ↦ t ^ q`, `0 ≤ q ≤ 1`: on a probability
space, `∫ g ^ q ≤ (∫ g) ^ q` for nonnegative integrable `g`. -/
lemma integral_rpow_le_rpow_integral {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ}
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hg0 : ∀ᵐ ω ∂μ, g ω ∈ Set.Ici (0 : ℝ))
    (hgi : Integrable g μ) (hgqi : Integrable (fun ω => g ω ^ q) μ) :
    (∫ ω, g ω ^ q ∂μ) ≤ (∫ ω, g ω ∂μ) ^ q :=
  (Real.concaveOn_rpow hq0 hq1).le_map_integral
    (fun x _ => (Real.continuousAt_rpow_const x q (Or.inr hq0)).continuousWithinAt)
    isClosed_Ici hg0 hgi hgqi

/-- **Jensen from a bound**: for measurable `g` with `0 ≤ g ≤ M` almost everywhere and
`0 ≤ q ≤ 1`, `∫ g ^ q ≤ (∫ g) ^ q` on a probability space.  The bound only supplies the two
integrability side conditions of `RMF.integral_rpow_le_rpow_integral`; `M` does not enter the
conclusion. -/
lemma integral_rpow_le_rpow_integral_of_bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {g : Ω → ℝ} {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hmeas : Measurable g)
    (h0 : ∀ᵐ ω ∂μ, 0 ≤ g ω) (hbd : ∀ᵐ ω ∂μ, g ω ≤ M) :
    (∫ ω, g ω ^ q ∂μ) ≤ (∫ ω, g ω ∂μ) ^ q := by
  have hnorm : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ M := by
    filter_upwards [h0, hbd] with ω h1 h2
    rwa [Real.norm_eq_abs, abs_of_nonneg h1]
  have hgi : Integrable g μ :=
    (memLp_top_of_bound hmeas.aestronglyMeasurable M hnorm).integrable le_top
  exact integral_rpow_le_rpow_integral hq0 hq1 h0 hgi
    (integrable_rpow_of_integrable hgi h0 hq0 hq1)

/-- **`∫ g^q ≤ B^q` from `∫ g ≤ B`**, for `0 ≤ q ≤ 1` and `g ≥ 0` integrable.  Jensen, then
monotonicity of `t ↦ t^q`.

A bound on `∫ g` becomes a bound on `∫ g^q`, uniformly in `q` — the shape every use of it takes,
since the quantities it is applied to are controlled only in expectation. -/
theorem integral_rpow_le_rpow_of_integral_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {g : Ω → ℝ} {q B : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h0 : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hgi : Integrable g μ) (hB : (∫ ω, g ω ∂μ) ≤ B) :
    (∫ ω, g ω ^ q ∂μ) ≤ B ^ q := by
  have hint0 : (0 : ℝ) ≤ ∫ ω, g ω ∂μ := integral_nonneg_of_ae h0
  refine le_trans (integral_rpow_le_rpow_integral hq0 hq1 h0 hgi
    (integrable_rpow_of_integrable hgi h0 hq0 hq1)) ?_
  exact Real.rpow_le_rpow hint0 hB hq0

/-! ### Paley–Zygmund

Paley–Zygmund turns a lower bound on `E X` and an upper bound on `E X²` into a lower bound on
`E X^q`.  The mechanism is Hölder run backwards: `X = X^{q/(2-q)}·X^{2(1-q)/(2-q)}`, whose
exponents sum to one, against the conjugate pair `(2-q, (2-q)/(1-q))`.  Nothing here is about
Euler products — `X` is any nonnegative function with `X^q` and `X²` integrable. -/

/-- **An `L^r` membership from an integrable power.**  If `X ≥ 0` and `X^s` is integrable then
`X^{s/r} ∈ L^r`, because `(X^{s/r})^r = X^s`. -/
lemma memLp_rpow_div_of_integrable_rpow {X : Ω → ℝ} {μ : Measure Ω} {s r : ℝ}
    (hr : 0 < r) (hX0 : 0 ≤ᵐ[μ] X) (h : Integrable (fun ω => X ω ^ s) μ) :
    MemLp (fun ω => X ω ^ (s / r)) (ENNReal.ofReal r) μ := by
  have hr' : (0 : ℝ) < 1 / r := by positivity
  have h1 := (memLp_one_iff_integrable.2 h).norm_rpow_div (ENNReal.ofReal (1 / r))
  have hexp : (1 : ENNReal) / ENNReal.ofReal (1 / r) = ENNReal.ofReal r := by
    rw [one_div r, ENNReal.ofReal_inv_of_pos hr, one_div, inv_inv]
  rw [ENNReal.toReal_ofReal hr'.le, hexp] at h1
  refine (memLp_congr_ae ?_).1 h1
  filter_upwards [hX0] with ω hω
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hω s), ← Real.rpow_mul hω, mul_one_div]

/-- **Hölder at the Paley–Zygmund split.**  For `0 < q < 1` and `X ≥ 0`,

`E X ≤ (E X^q)^{1/(2-q)} · (E X²)^{(1-q)/(2-q)}`.

The square is written as an `rpow`; `Real.rpow_natCast` converts to the `npow` form when a
consumer supplies it that way. -/
theorem integral_le_rpow_integral_rpow_mul_rpow_integral_sq
    {X : Ω → ℝ} {μ : Measure Ω} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hX0 : 0 ≤ᵐ[μ] X) (hXq : Integrable (fun ω => X ω ^ q) μ)
    (hX2 : Integrable (fun ω => X ω ^ (2 : ℝ)) μ) :
    (∫ ω, X ω ∂μ)
      ≤ (∫ ω, X ω ^ q ∂μ) ^ (1 / (2 - q))
          * (∫ ω, X ω ^ (2 : ℝ) ∂μ) ^ ((1 - q) / (2 - q)) := by
  have h2q : (0 : ℝ) < 2 - q := by linarith
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hpq : Real.HolderConjugate (2 - q) ((2 - q) / (1 - q)) := by
    have h := Real.holderConjugate_one_div (a := 1 / (2 - q)) (b := (1 - q) / (2 - q))
      (by positivity) (by positivity)
      (by field_simp; ring)
    rwa [one_div_one_div, one_div_div] at h
  have hf0 : 0 ≤ᵐ[μ] fun ω => X ω ^ (q / (2 - q)) := by
    filter_upwards [hX0] with ω hω
    exact Real.rpow_nonneg hω _
  have hg0 : 0 ≤ᵐ[μ] fun ω => X ω ^ (2 * (1 - q) / (2 - q)) := by
    filter_upwards [hX0] with ω hω
    exact Real.rpow_nonneg hω _
  have hfL : MemLp (fun ω => X ω ^ (q / (2 - q))) (ENNReal.ofReal (2 - q)) μ :=
    memLp_rpow_div_of_integrable_rpow h2q hX0 hXq
  have hgL : MemLp (fun ω => X ω ^ (2 * (1 - q) / (2 - q)))
      (ENNReal.ofReal ((2 - q) / (1 - q))) μ := by
    have h := memLp_rpow_div_of_integrable_rpow (r := (2 - q) / (1 - q)) (by positivity) hX0 hX2
    rwa [show (2 : ℝ) / ((2 - q) / (1 - q)) = 2 * (1 - q) / (2 - q) by
      rw [div_div_eq_mul_div]] at h
  have hHold := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf0 hg0 hfL hgL
  rw [one_div_div] at hHold
  -- the three integrands, each a single `rpow` identity
  have hsum : q / (2 - q) + 2 * (1 - q) / (2 - q) = 1 := by
    field_simp
    ring
  have e1 : (∫ ω, X ω ^ (q / (2 - q)) * X ω ^ (2 * (1 - q) / (2 - q)) ∂μ) = ∫ ω, X ω ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hX0] with ω hω
    rw [← Real.rpow_add' hω (by rw [hsum]; norm_num), hsum, Real.rpow_one]
  have e2 : (∫ ω, (X ω ^ (q / (2 - q))) ^ (2 - q) ∂μ) = ∫ ω, X ω ^ q ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hX0] with ω hω
    rw [← Real.rpow_mul hω, div_mul_cancel₀ _ (by linarith : (2 : ℝ) - q ≠ 0)]
  have e3 : (∫ ω, (X ω ^ (2 * (1 - q) / (2 - q))) ^ ((2 - q) / (1 - q)) ∂μ)
      = ∫ ω, X ω ^ (2 : ℝ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hX0] with ω hω
    rw [← Real.rpow_mul hω]
    congr 1
    field_simp
  rw [e1, e2, e3] at hHold
  exact hHold

/-- **Paley–Zygmund.**  For `0 < q < 1`, `X ≥ 0` with `X^q` and `X²` integrable and `E X² > 0`,
`(E X)^{2-q} / (E X²)^{1-q} ≤ E X^q`.

This is `RMF.integral_le_rpow_integral_rpow_mul_rpow_integral_sq` raised to the power `2-q` and
rearranged.  The lower bound applies it at `X = ∫_L |F(1/2+σ+it)|² dt`, with `E X` bounded below
and `E X²` above (Harper's Key Proposition 5). -/
theorem rpow_integral_div_rpow_integral_sq_le_integral_rpow
    {X : Ω → ℝ} {μ : Measure Ω} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hX0 : 0 ≤ᵐ[μ] X) (hXq : Integrable (fun ω => X ω ^ q) μ)
    (hX2 : Integrable (fun ω => X ω ^ (2 : ℝ)) μ)
    (hpos : 0 < ∫ ω, X ω ^ (2 : ℝ) ∂μ) :
    (∫ ω, X ω ∂μ) ^ (2 - q) / (∫ ω, X ω ^ (2 : ℝ) ∂μ) ^ (1 - q)
      ≤ ∫ ω, X ω ^ q ∂μ := by
  have h2q : (0 : ℝ) < 2 - q := by linarith
  have hH := integral_le_rpow_integral_rpow_mul_rpow_integral_sq hq0 hq1 hX0 hXq hX2
  have hX0' : (0 : ℝ) ≤ ∫ ω, X ω ∂μ := integral_nonneg_of_ae hX0
  have hXq0 : (0 : ℝ) ≤ ∫ ω, X ω ^ q ∂μ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hX0] with ω hω
    exact Real.rpow_nonneg hω _
  have hden : (0 : ℝ) < (∫ ω, X ω ^ (2 : ℝ) ∂μ) ^ (1 - q) := Real.rpow_pos_of_pos hpos _
  rw [div_le_iff₀ hden]
  have hraise := Real.rpow_le_rpow hX0' hH h2q.le
  rwa [Real.mul_rpow (Real.rpow_nonneg hXq0 _) (Real.rpow_nonneg hpos.le _),
    ← Real.rpow_mul hXq0, ← Real.rpow_mul hpos.le,
    one_div_mul_cancel (by linarith : (2 : ℝ) - q ≠ 0), Real.rpow_one,
    div_mul_cancel₀ _ (by linarith : (2 : ℝ) - q ≠ 0)] at hraise

/-- **A bounded random multiplicative function**, the part of the law the rough/smooth estimates
use: each value `f n` is measurable, `‖f n‖ ≤ 1` almost surely, and the second moment over any
finite set of nonzero indices is at most its cardinality.  Both models supply it
(`RMF.IsSteinhausRMF.isBoundedRMF`, `RMF.IsRademacherRMF.isBoundedRMF`), so every estimate stated
on it serves both. -/
structure IsBoundedRMF (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω) : Prop where
  /-- Each value is measurable in `ω`. -/
  measurable_apply : ∀ n : ℕ, Measurable fun ω => f ω n
  /-- Each value is bounded by one in modulus, almost surely. -/
  ae_norm_le_one : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1
  /-- **The second moment over any finite index set is at most the number of terms.**  An
  *inequality*, deliberately: Steinhaus attains it, Rademacher does not — its second moment counts
  only the squarefree indices. -/
  integral_normSq_sum_le : ∀ s : Finset ℕ, (∀ n ∈ s, n ≠ 0) →
    (∫ ω, ‖∑ n ∈ s, f ω n‖ ^ 2 ∂μ) ≤ s.card

/-- The Steinhaus function is bounded: `‖f n‖ = 1` for `n ≠ 0`, and `f 0 = 0`. -/
lemma IsSteinhausRMF.isBoundedRMF {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) : IsBoundedRMF f μ where
  measurable_apply := hf.measurable_apply
  ae_norm_le_one n := by
    rcases eq_or_ne n 0 with rfl | hn
    · exact Filter.Eventually.of_forall fun ω => by simp
    · filter_upwards [hf.norm_apply hn] with ω hω
      exact hω.le
  integral_normSq_sum_le s hs := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    haveI := hX.isProbabilityMeasure
    exact le_of_eq (integral_normSq_sum_of_orthogonality hX.isSteinhausRMF hs)

/-- The Rademacher function is bounded, with no side condition at all. -/
lemma IsRademacherRMF.isBoundedRMF {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) : IsBoundedRMF f μ where
  measurable_apply := hf.measurable_apply
  ae_norm_le_one := hf.norm_apply_le_one
  integral_normSq_sum_le s hs := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    haveI := hX.isProbabilityMeasure
    exact IsRademacherRMF.integral_normSq_sum_le hX.isRademacherRMF hs

end RMF
