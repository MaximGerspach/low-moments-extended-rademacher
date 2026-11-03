/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherChaining

/-!
# The squarefree Euler product is conjugate-symmetric, because the Rademacher law is real

`RMF.rademacherLaw` is the fair coin on `{1, −1}` — a measure on `ℝ ⊆ ℂ`.  So every value is its
own conjugate, and the squarefree Euler product satisfies `F(conj s) = conj F(s)`
**pointwise in `ω`**,
hence `‖F(σ − it)‖ = ‖F(σ + it)‖`.

## Why this matters

`RMF.integral_rpow_window_eq` — *"every unit window contributes the same expectation"* — is proved
for Steinhaus by **rotating** the primes (`RMF.integral_rpow_unitFunctional_rotate`, resting on
`RMF.IsSteinhausPrimeValues.mul_unimodular`).  Rotation is not a Rademacher symmetry.

**What conjugate symmetry does, and what it does not.**  It identifies the window at `-N` with the
window at `N`, so in Harper's sum-to-max step the maximum over `ℤ` may be halved to `N ≥ 0`.  It
does **not** replace the window equality: reflection is `h ↦ -h` and the periodisation step needs
translation `t ↦ t + n`.

**This is strictly stronger than the `X ↦ −X` route.**  `RMF.IsRademacherPrimeValues.neg` is a
statement about the *law*; this is a pointwise identity about a single `ω`, so it survives
conditioning, restriction to the unimodularity set, and anything else done to the sample space.

Nothing here is special to the squarefree product beyond its shape: the same argument gives the
Steinhaus statement for any real-valued family, which is why the hypothesis is stated as realness
of the values rather than as a law.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*}

/-- **The Rademacher law is real**: a.e. `z` is its own conjugate.

The counterpart of `RMF.norm_eq_one_rademacherLaw`, and proved the same way — the law is
`2⁻¹ • (δ₁ + δ₋₁)` and both atoms are real. -/
lemma conj_eq_rademacherLaw : ∀ᵐ z ∂rademacherLaw, (starRingEnd ℂ) z = z := by
  rw [ae_iff]
  simp only [rademacherLaw, Measure.smul_apply, Measure.coe_add, Pi.add_apply, smul_eq_mul]
  simp

/-- **The values are a.e. real over a range of primes.**

The realness counterpart of `RMF.ae_forall_norm_le_one_primesIco`, and like it **generic in the
law** — the law enters only through the `hν` argument, so `RMF.conj_eq_rademacherLaw` slots in
directly. -/
lemma ae_forall_conj_eq_primesIco [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {ν : Measure ℂ}
    {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ)
    (hν : ∀ᵐ z ∂ν, (starRingEnd ℂ) z = z) (y₀ y₁ : ℕ) :
    ∀ᵐ ω ∂μ, ∀ p ∈ primesIco y₀ y₁, (starRingEnd ℂ) (X p ω) = X p ω := by
  refine (Filter.eventually_all_finset _).2 fun p hp => ?_
  have hmeasP : Measurable fun z : ℂ => (starRingEnd ℂ) z = z :=
    measurableSet_setOf.1
      (measurableSet_eq_fun (RCLike.continuous_conj (K := ℂ)).measurable measurable_id)
  exact ((hX.hasLaw p (prime_of_mem_primesIco hp)).ae_iff hmeasP).2 hν

/-- **The squarefree Euler product is conjugate-symmetric at a real-valued sample point.**
`F(conj s) = conj F(s)`, pointwise in `ω`, whenever every value in the range is real: the product
form `RMF.randomEulerProductIco_sqfree_eq` and `RMF.conj_natCast_cpow_neg` on each factor.  No
hypothesis on `s` and none on the law, only that the values at this one `ω` are real. -/
lemma randomEulerProductIco_sqfree_conj {X : ℕ → Ω → ℂ} {y₀ y₁ : ℕ} {s : ℂ} {ω : Ω}
    (hω : ∀ p ∈ primesIco y₀ y₁, (starRingEnd ℂ) (X p ω) = X p ω) :
    randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        ((starRingEnd ℂ) s) ω
      = (starRingEnd ℂ) (randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          y₀ y₁ s ω) := by
  rw [randomEulerProductIco_sqfree_eq, randomEulerProductIco_sqfree_eq, map_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [map_add, map_one, map_mul, hω p hp,
    conj_natCast_cpow_neg (prime_of_mem_primesIco hp).pos s]

/-- **Reflecting the height does not change the norm.**  `‖F(σ − ih)‖ = ‖F(σ + ih)‖`, pointwise in
`ω`, on the realness set, needing no law invariance whatever.  It identifies the window at `-N`
with the window at `N`, so Harper's maximum over `ℤ` may be taken over `N ≥ 0`; it does **not**
replace `RMF.integral_rpow_window_eq`, which needs translation. -/
lemma norm_randomEulerProductIco_sqfree_heightLine_neg {X : ℕ → Ω → ℂ} {y₀ y₁ : ℕ} {σ h : ℝ}
    {ω : Ω} (hω : ∀ p ∈ primesIco y₀ y₁, (starRingEnd ℂ) (X p ω) = X p ω) :
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        (heightLine σ (-h)) ω‖
      = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (heightLine σ h) ω‖ := by
  have hc : heightLine σ (-h) = (starRingEnd ℂ) (heightLine σ h) := by
    rw [heightLine, heightLine]
    apply Complex.ext <;> simp
  rw [hc, randomEulerProductIco_sqfree_conj hω, RCLike.norm_conj]

end RMF
