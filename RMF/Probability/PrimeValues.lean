/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.IdentDistribIndep
import RMF.NumberTheory.Extension
import RMF.Probability.Laws

/-!
# Values at the primes

A random multiplicative function is built from a family `X : ℕ → Ω → ℂ` of random values,
one at each prime.  Two hypotheses on such a family are used:

* `RMF.IsIIDPrimeValues X ν μ` — the values at the primes are independent and each has law
  `ν`.  This is what the classical models specify, and what the theory uses.
* `RMF.IsRMFPrimeValues X μ` — the values are independent, identically distributed,
  centered, with a finite second moment: the hypotheses of the general notion
  `RMF.IsSquarefreeRMF`.

`RMF.IsIIDPrimeValues.isRMFPrimeValues` bridges the two.

The main tool is `RMF.IsIIDPrimeValues.integral_prod`: expectations of products over
distinct primes factor.  Every moment computation downstream is an instance of it.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Hypotheses on the values at the primes -/

/-- The general hypotheses on the values at the primes: independent, identically
distributed, centered, and with a finite second moment. -/
structure IsRMFPrimeValues (X : ℕ → Ω → ℂ) (μ : Measure Ω) : Prop where
  /-- Each value is measurable. -/
  measurable : ∀ p : ℕ, p.Prime → Measurable (X p)
  /-- The values at distinct primes are independent. -/
  iIndep : iIndepFun (fun p : Nat.Primes => X (p : ℕ)) μ
  /-- The values at the primes all have the same law. -/
  identDistrib : ∀ p q : ℕ, p.Prime → q.Prime → IdentDistrib (X p) (X q) μ μ
  /-- The common law is centered. -/
  centered : ∀ p : ℕ, p.Prime → ∫ ω, X p ω ∂μ = 0
  /-- The common law has a finite second moment. -/
  memLp : ∀ p : ℕ, p.Prime → MemLp (X p) 2 μ

/-- Independent values at the primes, each distributed according to `ν`. -/
structure IsIIDPrimeValues (X : ℕ → Ω → ℂ) (ν : Measure ℂ) (μ : Measure Ω) : Prop where
  /-- Each value at a prime is measurable. -/
  measurable : ∀ p : ℕ, p.Prime → Measurable (X p)
  /-- The values at distinct primes are independent. -/
  iIndep : iIndepFun (fun p : Nat.Primes => X (p : ℕ)) μ
  /-- Each value at a prime has law `ν`. -/
  hasLaw : ∀ p : ℕ, p.Prime → HasLaw (X p) ν μ

/-- Independent fair coin flips `±1` at the primes. -/
abbrev IsRademacherPrimeValues (X : ℕ → Ω → ℂ) (μ : Measure Ω) : Prop :=
  IsIIDPrimeValues X rademacherLaw μ

/-- Independent uniform points of the unit circle at the primes. -/
abbrev IsSteinhausPrimeValues (X : ℕ → Ω → ℂ) (μ : Measure Ω) : Prop :=
  IsIIDPrimeValues X steinhausLaw μ

/-! ### Rotation

The Steinhaus hypothesis is closed under multiplying each prime's value by a fixed unimodular
constant.  This is the reusable form of `RMF.map_mul_left_steinhausLaw`: it is what lets a factor
`p^{-it}` be absorbed into the random values themselves, and so what removes Harper's *common*
centre `t`. -/

/-- **iid values survive law-preserving scalings.**  If `z ↦ c p * z` preserves `ν` for every
`p > 0`, then `p ↦ c p * X p` is again iid with law `ν`. -/
theorem IsIIDPrimeValues.mul_const {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) {c : ℕ → ℂ}
    (hc : ∀ p : ℕ, 0 < p → Measure.map (fun z : ℂ => c p * z) ν = ν) :
    IsIIDPrimeValues (fun p ω => c p * X p ω) ν μ := by
  refine ⟨fun p hp => (hX.measurable p hp).const_mul (c p), ?_, fun p hp => ?_⟩
  · exact hX.iIndep.comp (fun p : Nat.Primes => fun z : ℂ => c (p : ℕ) * z)
      (fun _ => measurable_id.const_mul _)
  · refine ⟨((hX.measurable p hp).const_mul (c p)).aemeasurable, ?_⟩
    have hcomp : (fun ω => c p * X p ω) = (fun z : ℂ => c p * z) ∘ X p := rfl
    rw [hcomp, ← Measure.map_map (by fun_prop) (hX.measurable p hp), (hX.hasLaw p hp).map_eq,
      hc p hp.pos]

/-- Multiplying the Steinhaus values by unimodular constants: the `RMF.steinhausLaw` instance of
`RMF.IsIIDPrimeValues.mul_const`. -/
theorem IsSteinhausPrimeValues.mul_unimodular {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {c : ℕ → ℂ} (hc : ∀ p, 0 < p → ‖c p‖ = 1) :
    IsSteinhausPrimeValues (fun p ω => c p * X p ω) μ :=
  hX.mul_const fun p hp => map_mul_left_steinhausLaw (hc p hp)

/-! ### From a named law to the general hypotheses -/

/-- The ambient measure is a probability measure: `μ` and its push-forward under `X p` have
the same total mass, and the law is a probability measure. -/
lemma IsIIDPrimeValues.isProbabilityMeasure {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure ν] (hX : IsIIDPrimeValues X ν μ) : IsProbabilityMeasure μ := by
  have hae := (hX.hasLaw 2 Nat.prime_two).aemeasurable
  have h : μ.map (X 2) Set.univ = 1 := by rw [(hX.hasLaw 2 Nat.prime_two).map_eq]; simp
  rw [Measure.map_apply_of_aemeasurable hae MeasurableSet.univ] at h
  exact ⟨by simpa using h⟩

/-- A centered law with a finite second moment gives values satisfying the general
hypotheses.  This is the weakest hypothesis under which the second-moment theory runs; in
particular it does not require the law to be bounded. -/
theorem IsIIDPrimeValues.isRMFPrimeValues {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hmem : MemLp id 2 ν) (hcent : ∫ z, z ∂ν = 0)
    (hX : IsIIDPrimeValues X ν μ) : IsRMFPrimeValues X μ where
  measurable := hX.measurable
  iIndep := hX.iIndep
  identDistrib p q hp hq :=
    ⟨(hX.hasLaw p hp).aemeasurable, (hX.hasLaw q hq).aemeasurable,
      by rw [(hX.hasLaw p hp).map_eq, (hX.hasLaw q hq).map_eq]⟩
  centered p hp := by rw [(hX.hasLaw p hp).integral_eq, hcent]
  memLp p hp := by
    have hmap : μ.map (X p) = ν := (hX.hasLaw p hp).map_eq
    have := (memLp_map_measure_iff (g := (id : ℂ → ℂ)) (f := X p) (p := 2)
      (by rw [hmap]; exact aestronglyMeasurable_id) (hX.hasLaw p hp).aemeasurable).1
      (by rwa [hmap])
    simpa [Function.comp_def] using this

theorem IsRademacherPrimeValues.isRMFPrimeValues {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) : IsRMFPrimeValues X μ :=
  IsIIDPrimeValues.isRMFPrimeValues memLp_two_rademacherLaw integral_rademacherLaw hX

/-- The completely multiplicative extension of measurable values at the primes is
measurable. -/
lemma IsIIDPrimeValues.measurable_compMultExtension {X : ℕ → Ω → ℂ} {ν : Measure ℂ}
    {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (n : ℕ) :
    Measurable fun ω => compMultExtension (fun p => X p ω) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [compMultExtension_apply_of_ne_zero _ hn, Finsupp.prod, Nat.support_factorization]
    exact Finset.measurable_prod _ fun p hp =>
      (hX.measurable p (Nat.prime_of_mem_primeFactors hp)).pow_const _

/-- **Expectations factor over the primes.**  The expectation of a product of functions of the
values at finitely many distinct primes equals the product of the expectations, each taken against
the law.  Only independence is used; the law enters solely through the individual factors.
Cross moments of a random multiplicative function and moments of its Euler product are instances. -/
theorem IsIIDPrimeValues.integral_prod {𝕜 : Type*} [RCLike 𝕜] {X : ℕ → Ω → ℂ} {ν : Measure ℂ}
    {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (g : ℕ → ℂ → 𝕜) (hg : ∀ p ∈ S, AEStronglyMeasurable (g p) ν) :
    (∫ ω, ∏ p ∈ S, g p (X p ω) ∂μ) = ∏ p ∈ S, ∫ z, g p z ∂ν := by
  have hinj : Function.Injective (fun i : S => (⟨(i : ℕ), hS i i.2⟩ : Nat.Primes)) := by
    intro a b hab
    exact Subtype.ext (congrArg (fun p : Nat.Primes => (p : ℕ)) hab)
  have hindep : iIndepFun (fun i : S => X (i : ℕ)) μ := hX.iIndep.precomp hinj
  have hmeas : ∀ i : S, AEMeasurable (X (i : ℕ)) μ :=
    fun i => (hX.measurable i (hS i i.2)).aemeasurable
  have hgm : ∀ i : S, AEStronglyMeasurable (g i) (μ.map (X (i : ℕ))) := by
    intro i
    rw [(hX.hasLaw i (hS i i.2)).map_eq]
    exact hg i i.2
  calc (∫ ω, ∏ p ∈ S, g p (X p ω) ∂μ)
      = ∫ ω, ∏ i : S, g i (X (i : ℕ) ω) ∂μ := by
        exact integral_congr_ae (.of_forall fun ω => (Finset.prod_coe_sort S _).symm)
    _ = ∏ i : S, ∫ ω, g i (X (i : ℕ) ω) ∂μ := hindep.integral_fun_prod_comp hmeas hgm
    _ = ∏ i : S, ∫ z, g i z ∂ν :=
        Finset.prod_congr rfl fun i _ =>
          (hX.hasLaw i (hS i i.2)).integral_comp (f := g i) (hg i i.2)
    _ = ∏ p ∈ S, ∫ z, g p z ∂ν := Finset.prod_coe_sort _ fun p => ∫ z, g p z ∂ν

/-- **Cross moments factor over the primes.**  A special case of
`IsIIDPrimeValues.integral_prod`: the expectation of `f m * conj (f n)` splits into one
integral against the law per prime dividing `m * n`. -/
theorem IsIIDPrimeValues.integral_compMultExtension_mul_conj {X : ℕ → Ω → ℂ} {ν : Measure ℂ}
    {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (∫ ω, compMultExtension (fun p => X p ω) m
        * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) n) ∂μ)
      = ∏ p ∈ (m * n).primeFactors,
          ∫ z, z ^ m.factorization p * (starRingEnd ℂ) (z ^ n.factorization p) ∂ν := by
  have hSp : ∀ p ∈ (m * n).primeFactors, p.Prime := fun _ hp => Nat.prime_of_mem_primeFactors hp
  have hmS : m.primeFactors ⊆ (m * n).primeFactors := by
    rw [Nat.primeFactors_mul hm hn]; exact Finset.subset_union_left
  have hnS : n.primeFactors ⊆ (m * n).primeFactors := by
    rw [Nat.primeFactors_mul hm hn]; exact Finset.subset_union_right
  have hpt : ∀ ω : Ω, compMultExtension (fun p => X p ω) m
      * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) n)
        = ∏ p ∈ (m * n).primeFactors,
            (X p ω ^ m.factorization p * (starRingEnd ℂ) (X p ω ^ n.factorization p)) := by
    intro ω
    rw [compMultExtension_apply_eq_prod _ hm hmS, compMultExtension_apply_eq_prod _ hn hnS,
      map_prod, ← Finset.prod_mul_distrib]
  simp_rw [hpt]
  exact hX.integral_prod hSp
    (fun p z => z ^ m.factorization p * (starRingEnd ℂ) (z ^ n.factorization p))
    fun p _ => Continuous.aestronglyMeasurable (by fun_prop)

/-- The squarefree-supported extension of measurable values at the primes is measurable. -/
lemma IsIIDPrimeValues.measurable_squarefreeExtension {X : ℕ → Ω → ℂ} {ν : Measure ℂ}
    {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (n : ℕ) :
    Measurable fun ω => squarefreeExtension (fun p => X p ω) n := by
  by_cases hn : Squarefree n
  · simp only [squarefreeExtension_apply_of_squarefree _ hn]
    exact Finset.measurable_prod _ fun p hp => hX.measurable p (Nat.prime_of_mem_primeFactors hp)
  · simp only [squarefreeExtension_apply_of_not_squarefree _ hn]
    exact measurable_const

/-! ### The law of the whole family

Two iid prime-value families with the same one-dimensional law are identically distributed *as
families*, even on different probability spaces.  This is what lets an expectation be transported
between two models of the same random multiplicative function — in particular between a Steinhaus
family and its rotation `p ↦ cₚ Xₚ`, which is the mechanism behind the periodisation step. -/

/-- **The joint law is determined by the one-dimensional law.**  Independence plus equal marginals
gives equality of the laws of the families, by `ProbabilityTheory.IdentDistrib.pi`. -/
theorem IsIIDPrimeValues.identDistrib_family {Ω' : Type*} [MeasurableSpace Ω']
    {X : ℕ → Ω → ℂ} {Y : ℕ → Ω' → ℂ} {ν : Measure ℂ} {μ : Measure Ω} {μ' : Measure Ω'}
    (hX : IsIIDPrimeValues X ν μ) (hY : IsIIDPrimeValues Y ν μ') :
    ProbabilityTheory.IdentDistrib (fun ω (p : Nat.Primes) => X (p : ℕ) ω)
      (fun ω (p : Nat.Primes) => Y (p : ℕ) ω) μ μ' :=
  ProbabilityTheory.IdentDistrib.pi
    (fun p => (hX.hasLaw (p : ℕ) p.2).identDistrib (hY.hasLaw (p : ℕ) p.2))
    hX.iIndep hY.iIndep

/-- **Any measurable functional of the family has the same expectation** under two iid prime-value
families with the same law.  This is the form the reduction consumes. -/
theorem IsIIDPrimeValues.integral_comp_eq {Ω' : Type*} [MeasurableSpace Ω']
    {X : ℕ → Ω → ℂ} {Y : ℕ → Ω' → ℂ} {ν : Measure ℂ} {μ : Measure Ω} {μ' : Measure Ω'}
    (hX : IsIIDPrimeValues X ν μ) (hY : IsIIDPrimeValues Y ν μ')
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Φ : (Nat.Primes → ℂ) → E} (hΦ : Measurable Φ) :
    ∫ ω, Φ (fun p => X (p : ℕ) ω) ∂μ = ∫ ω, Φ (fun p => Y (p : ℕ) ω) ∂μ' :=
  ((hX.identDistrib_family hY).comp hΦ).integral_eq

/-- **Rotation invariance.**  Multiplying the values at the primes by fixed unimodular constants
does not change the expectation of any measurable functional of the family.

This is the whole content of the periodisation step: shifting the critical line by an integer `n`
replaces `f(p)p^{-it}` by `(p^{-in})·f(p)p^{-ih}`, and `p^{-in}` is unimodular. -/
theorem IsIIDPrimeValues.integral_comp_mul_const {X : ℕ → Ω → ℂ} {ν : Measure ℂ}
    {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) {c : ℕ → ℂ}
    (hc : ∀ p : ℕ, 0 < p → Measure.map (fun z : ℂ => c p * z) ν = ν)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Φ : (Nat.Primes → ℂ) → E} (hΦ : Measurable Φ) :
    ∫ ω, Φ (fun p => c (p : ℕ) * X (p : ℕ) ω) ∂μ = ∫ ω, Φ (fun p => X (p : ℕ) ω) ∂μ :=
  (hX.mul_const hc).integral_comp_eq hX hΦ

/-- Rotation invariance: the `RMF.steinhausLaw` instance of
`RMF.IsIIDPrimeValues.integral_comp_mul_const`. -/
theorem IsSteinhausPrimeValues.integral_comp_rotate {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {c : ℕ → ℂ} (hc : ∀ p, 0 < p → ‖c p‖ = 1)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Φ : (Nat.Primes → ℂ) → E} (hΦ : Measurable Φ) :
    ∫ ω, Φ (fun p => c (p : ℕ) * X (p : ℕ) ω) ∂μ = ∫ ω, Φ (fun p => X (p : ℕ) ω) ∂μ :=
  hX.integral_comp_mul_const (fun p hp => map_mul_left_steinhausLaw (hc p hp)) hΦ

end RMF
