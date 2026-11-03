/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Probability.Independence.InfinitePi
import RMF.Reduction.RoughLinearForm

/-!
# The coordinate model, and moments that do not depend on the probability space

On `Nat.Primes → ℂ` with the product of copies of a law `ν`, the coordinates extended by zero off
the primes are independent with law `ν` (`RMF.isIIDPrimeValues_primeExtend`).  On any probability
space the values at the primes of an iid family have this product law
(`RMF.IsIIDPrimeValues.hasLaw_infinitePi`), so a functional that only sees them has the coordinate
model's expectation (`RMF.IsIIDPrimeValues.integral_comp_primeExtend`).

For the partial sums of the Steinhaus and the Rademacher random multiplicative function this says
that their moments are those of the coordinate model; it is what makes the constants of Harper's
theorems independent of the probability space (`RMF.harper_low_moments`).
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The coordinate model of iid values at the primes.**  On `Nat.Primes → ℂ` with the product of
copies of a probability law `ν`, the coordinates, extended by zero off the primes
(`RMF.primeExtend`), are independent with law `ν`. -/
theorem isIIDPrimeValues_primeExtend (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    IsIIDPrimeValues (fun n v => primeExtend v n) ν
      (Measure.infinitePi fun _ : Nat.Primes => ν) := by
  have hcoord : ∀ {p : ℕ} (hp : p.Prime),
      (fun v : Nat.Primes → ℂ => primeExtend v p) = fun v => v ⟨p, hp⟩ :=
    fun hp => funext fun v => primeExtend_apply v hp
  refine ⟨fun p _ => measurable_primeExtend p, ?_, fun p hp => ?_⟩
  · have hfun : (fun (p : Nat.Primes) (v : Nat.Primes → ℂ) => primeExtend v p)
        = fun p v => v p :=
      funext fun p => hcoord p.2
    change iIndepFun (fun (p : Nat.Primes) (v : Nat.Primes → ℂ) => primeExtend v p) _
    rw [hfun]
    exact iIndepFun_infinitePi (P := fun _ : Nat.Primes => ν) (X := fun _ (z : ℂ) => z)
      fun _ => measurable_id
  · show HasLaw (fun v : Nat.Primes → ℂ => primeExtend v p) ν _
    rw [hcoord hp]
    exact ⟨(measurable_pi_apply _).aemeasurable, Measure.infinitePi_map_eval _ _⟩

/-- **The values at the primes have the product law**, on any probability space:
`ProbabilityTheory.iIndepFun.hasLaw_infinitePi` for the family `(X p)_{p prime}`. -/
theorem IsIIDPrimeValues.hasLaw_infinitePi {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) :
    HasLaw (fun ω (p : Nat.Primes) => X p ω) (Measure.infinitePi fun _ : Nat.Primes => ν) μ :=
  hX.iIndep.hasLaw_infinitePi (fun p => hX.hasLaw p p.2)
    (measurable_pi_lambda (fun ω (p : Nat.Primes) => X p ω)
      fun p => hX.measurable p p.2).aemeasurable

/-- **Expectations are the coordinate model's.**  A functional `Ψ` of the values that only sees the
values at the primes has, on any probability space, the expectation it has on the coordinate
model. -/
theorem IsIIDPrimeValues.integral_comp_primeExtend {X : ℕ → Ω → ℂ} {ν : Measure ℂ}
    {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Ψ : (ℕ → ℂ) → E}
    (hΨ : ∀ {v w : ℕ → ℂ}, (∀ p, p.Prime → v p = w p) → Ψ v = Ψ w)
    (hΨm : AEStronglyMeasurable (fun v => Ψ (primeExtend v))
      (Measure.infinitePi fun _ : Nat.Primes => ν)) :
    ∫ ω, Ψ (fun n => X n ω) ∂μ
      = ∫ v, Ψ (primeExtend v) ∂(Measure.infinitePi fun _ : Nat.Primes => ν) := by
  have hω : ∀ ω, Ψ (fun n => X n ω) = Ψ (primeExtend fun p : Nat.Primes => X p ω) := fun ω =>
    hΨ (v := fun n => X n ω) (w := primeExtend fun p : Nat.Primes => X p ω)
      fun p hp => (primeExtend_apply (fun p : Nat.Primes => X p ω) hp).symm
  calc ∫ ω, Ψ (fun n => X n ω) ∂μ = ∫ ω, Ψ (primeExtend fun p : Nat.Primes => X p ω) ∂μ :=
        integral_congr_ae (.of_forall hω)
    _ = ∫ v, Ψ (primeExtend v) ∂(Measure.infinitePi fun _ : Nat.Primes => ν) :=
        hX.hasLaw_infinitePi.integral_comp hΨm

/-! ### The moments of the partial sums -/

/-- **`E|x^{-1/2} ∑_{n ≤ x} f(n)|^r` is the coordinate model's**, for `f` the completely
multiplicative extension of iid values at the primes. -/
theorem IsIIDPrimeValues.integral_rpow_normalisedSum_compMultExtension_eq
    {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (x r : ℝ) :
    ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ r ∂μ
      = ∫ v, ‖normalisedSum (fun v => compMultExtension (primeExtend v)) x v‖ ^ r
          ∂(Measure.infinitePi fun _ : Nat.Primes => ν) := by
  have hm : Measurable fun v : Nat.Primes → ℂ =>
      ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, compMultExtension (primeExtend v) n) / (Real.sqrt x : ℂ)‖ ^ r :=
    ((Finset.measurable_sum _ fun n _ => measurable_compMultExtension_primeExtend n).div_const
      (Real.sqrt x : ℂ)).norm.pow_const r
  exact hX.integral_comp_primeExtend
    (Ψ := fun g => ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, compMultExtension g n) / (Real.sqrt x : ℂ)‖ ^ r)
    (fun h => congrArg
      (fun F : ArithmeticFunction ℂ => ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F n) / (Real.sqrt x : ℂ)‖ ^ r)
      (compMultExtension_congr_primes h))
    hm.aestronglyMeasurable

/-- **`E|x^{-1/2} ∑_{n ≤ x} f(n)|^r` is the coordinate model's**, for `f` the extension of iid
values at the primes over the squarefree integers. -/
theorem IsIIDPrimeValues.integral_rpow_normalisedSum_squarefreeExtension_eq
    {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (x r : ℝ) :
    ∫ ω, ‖normalisedSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ r ∂μ
      = ∫ v, ‖normalisedSum (fun v => squarefreeExtension (primeExtend v)) x v‖ ^ r
          ∂(Measure.infinitePi fun _ : Nat.Primes => ν) := by
  have hm : Measurable fun v : Nat.Primes → ℂ =>
      ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, squarefreeExtension (primeExtend v) n) / (Real.sqrt x : ℂ)‖ ^ r :=
    ((Finset.measurable_sum _ fun n _ => measurable_squarefreeExtension_primeExtend n).div_const
      (Real.sqrt x : ℂ)).norm.pow_const r
  exact hX.integral_comp_primeExtend
    (Ψ := fun g => ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, squarefreeExtension g n) / (Real.sqrt x : ℂ)‖ ^ r)
    (fun h => congrArg
      (fun F : ArithmeticFunction ℂ => ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F n) / (Real.sqrt x : ℂ)‖ ^ r)
      (squarefreeExtension_congr_primes h))
    hm.aestronglyMeasurable

end RMF
