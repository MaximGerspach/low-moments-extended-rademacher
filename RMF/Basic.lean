/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.PrimeValues

/-!
# Random multiplicative functions

The classical random multiplicative functions, as properties of a random arithmetic function
`f : Ω → ArithmeticFunction ℂ` under a measure `μ`:

* `RMF.IsRademacherRMF`: the values `f p` at the primes are independent and uniform in `{±1}`,
  and `f n = ∏_{p ∣ n} f p` for squarefree `n`, `f n = 0` otherwise;
* `RMF.IsSteinhausRMF`: the values at the primes are independent and uniform on the unit circle,
  and `f` is completely multiplicative;

together with the general notion the Rademacher one specialises, `RMF.IsSquarefreeRMF`
(supported on the squarefrees), in which the values at the primes need only be independent,
identically distributed, centered and square-integrable.

Each is a structure whose fields say, in order, that every value `f n` is a random variable, how
the values at the primes are distributed, and how they determine `f`.  Each is equivalent to `f`
being the corresponding extension of a family of values at the primes
(`RMF.isRademacherRMF_iff_exists` and its siblings).  That is the form most proofs work with:
`hf.exists_primeValues` unpacks a hypothesis into it, and
`RMF.IsRademacherPrimeValues.isRademacherRMF` and its siblings build one.

Every notion is multiplicative pointwise in `ω`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The named random multiplicative functions -/

/-- A **Rademacher random multiplicative function** `f` on `(Ω, μ)`: the values `f p` at the
primes are independent and uniform in `{±1}`, and `f n = ∏_{p ∣ n} f p` for squarefree `n`,
`f n = 0` otherwise.

`RMF.rademacherLaw` is a law on `ℂ`, so `f p = ±1` holds almost surely, not for every `ω`. -/
structure IsRademacherRMF (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω) : Prop where
  /-- Each value `f n` is a random variable. -/
  measurable_apply : ∀ n, Measurable fun ω => f ω n
  /-- The values at the primes are independent… -/
  iIndepFun_primes : iIndepFun (fun (p : Nat.Primes) ω => f ω p) μ
  /-- …and each is `1` or `-1` with probability `1/2`. -/
  hasLaw_primes : ∀ p : Nat.Primes, HasLaw (fun ω => f ω p) rademacherLaw μ
  /-- `f n = ∏_{p ∣ n} f p` for squarefree `n`… -/
  apply_of_squarefree : ∀ ω n, Squarefree n → f ω n = ∏ p ∈ n.primeFactors, f ω p
  /-- …and `f n = 0` otherwise. -/
  apply_of_not_squarefree : ∀ ω n, ¬ Squarefree n → f ω n = 0

/-- A **Steinhaus random multiplicative function** `f` on `(Ω, μ)`: `f` is completely
multiplicative, and its values `f p` at the primes are independent and uniform on the unit circle.
This is the function in Harper's theorem. -/
structure IsSteinhausRMF (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω) : Prop where
  /-- Each value `f n` is a random variable. -/
  measurable_apply : ∀ n, Measurable fun ω => f ω n
  /-- The values at the primes are independent… -/
  iIndepFun_primes : iIndepFun (fun (p : Nat.Primes) ω => f ω p) μ
  /-- …and each is uniform on the unit circle. -/
  hasLaw_primes : ∀ p : Nat.Primes, HasLaw (fun ω => f ω p) steinhausLaw μ
  /-- `f` is completely multiplicative: `f 1 = 1`… -/
  apply_one : ∀ ω, f ω 1 = 1
  /-- …and `f (m * n) = f m * f n`. -/
  apply_mul : ∀ ω m n, f ω (m * n) = f ω m * f ω n

/-! ### The general notions -/

/-- A **squarefree random multiplicative function** in the general sense: `f n = ∏_{p ∣ n} f p`
for squarefree `n` and `f n = 0` otherwise, and the values `f p` at the primes are independent,
identically distributed, centered, and have a finite second moment. -/
structure IsSquarefreeRMF (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω) : Prop where
  /-- Each value `f n` is a random variable. -/
  measurable_apply : ∀ n, Measurable fun ω => f ω n
  /-- The values at the primes are independent… -/
  iIndepFun_primes : iIndepFun (fun (p : Nat.Primes) ω => f ω p) μ
  /-- …identically distributed… -/
  identDistrib_primes : ∀ p q : Nat.Primes, IdentDistrib (fun ω => f ω p) (fun ω => f ω q) μ μ
  /-- …centered… -/
  centered_primes : ∀ p : Nat.Primes, ∫ ω, f ω p ∂μ = 0
  /-- …and have a finite second moment. -/
  memLp_primes : ∀ p : Nat.Primes, MemLp (fun ω => f ω p) 2 μ
  /-- `f n = ∏_{p ∣ n} f p` for squarefree `n`… -/
  apply_of_squarefree : ∀ ω n, Squarefree n → f ω n = ∏ p ∈ n.primeFactors, f ω p
  /-- …and `f n = 0` otherwise. -/
  apply_of_not_squarefree : ∀ ω n, ¬ Squarefree n → f ω n = 0

/-! ### As extensions of values at the primes

Each notion says exactly that `f` is the corresponding extension of a family of values at the
primes.  That is the form most proofs work with: `hf.exists_primeValues` unpacks a hypothesis into
it, and `hX.isRademacherRMF` and its siblings build one from it. -/

/-- `f` is a Rademacher random multiplicative function exactly when it is the squarefree
extension of a Rademacher family of values at the primes. -/
theorem isRademacherRMF_iff_exists {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} :
    IsRademacherRMF f μ ↔ ∃ X : ℕ → Ω → ℂ,
      IsRademacherPrimeValues X μ ∧ f = fun ω => squarefreeExtension fun p => X p ω := by
  refine ⟨fun hf => ⟨fun n ω => f ω n,
    ⟨fun p _ => hf.measurable_apply p, hf.iIndepFun_primes, fun p hp => hf.hasLaw_primes ⟨p, hp⟩⟩,
    funext fun ω => eq_squarefreeExtension_of_apply (hf.apply_of_squarefree ω)
      (hf.apply_of_not_squarefree ω)⟩, ?_⟩
  rintro ⟨X, hX, rfl⟩
  refine ⟨hX.measurable_squarefreeExtension, ?_, fun p => ?_,
    fun ω n hn => squarefreeExtension_apply_eq_prod_primeFactors _ hn,
    fun ω n hn => squarefreeExtension_apply_of_not_squarefree _ hn⟩
  · convert hX.iIndep using 1
    funext p ω
    exact squarefreeExtension_apply_prime _ p.2
  · convert hX.hasLaw p p.2 using 1
    funext ω
    exact squarefreeExtension_apply_prime _ p.2

/-- `f` is a Steinhaus random multiplicative function exactly when it is the completely
multiplicative extension of a Steinhaus family of values at the primes. -/
theorem isSteinhausRMF_iff_exists {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} :
    IsSteinhausRMF f μ ↔ ∃ X : ℕ → Ω → ℂ,
      IsSteinhausPrimeValues X μ ∧ f = fun ω => compMultExtension fun p => X p ω := by
  refine ⟨fun hf => ⟨fun n ω => f ω n,
    ⟨fun p _ => hf.measurable_apply p, hf.iIndepFun_primes, fun p hp => hf.hasLaw_primes ⟨p, hp⟩⟩,
    funext fun ω => eq_compMultExtension_of_apply_mul (hf.apply_one ω) (hf.apply_mul ω)⟩, ?_⟩
  rintro ⟨X, hX, rfl⟩
  refine ⟨hX.measurable_compMultExtension, ?_, fun p => ?_,
    fun ω => compMultExtension_apply_one _, fun ω m n => compMultExtension_apply_mul' _ m n⟩
  · convert hX.iIndep using 1
    funext p ω
    exact compMultExtension_apply_prime _ p.2
  · convert hX.hasLaw p p.2 using 1
    funext ω
    exact compMultExtension_apply_prime _ p.2

/-- `f` is a squarefree random multiplicative function in the general sense exactly when it is the
squarefree extension of a family of values at the primes satisfying the general hypotheses. -/
theorem isSquarefreeRMF_iff_exists {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} :
    IsSquarefreeRMF f μ ↔ ∃ X : ℕ → Ω → ℂ,
      IsRMFPrimeValues X μ ∧ f = fun ω => squarefreeExtension fun p => X p ω := by
  refine ⟨fun hf => ⟨fun n ω => f ω n,
    ⟨fun p _ => hf.measurable_apply p, hf.iIndepFun_primes,
      fun p q hp hq => hf.identDistrib_primes ⟨p, hp⟩ ⟨q, hq⟩,
      fun p hp => hf.centered_primes ⟨p, hp⟩, fun p hp => hf.memLp_primes ⟨p, hp⟩⟩,
    funext fun ω => eq_squarefreeExtension_of_apply (hf.apply_of_squarefree ω)
      (hf.apply_of_not_squarefree ω)⟩, ?_⟩
  rintro ⟨X, hX, rfl⟩
  have hp : ∀ p : Nat.Primes, (fun ω => squarefreeExtension (fun q => X q ω) p) = X p :=
    fun p => funext fun ω => squarefreeExtension_apply_prime _ p.2
  refine ⟨fun n => ?_, ?_, fun p q => ?_, fun p => ?_, fun p => ?_,
    fun ω n hn => squarefreeExtension_apply_eq_prod_primeFactors _ hn,
    fun ω n hn => squarefreeExtension_apply_of_not_squarefree _ hn⟩
  · by_cases hn : Squarefree n
    · simp only [squarefreeExtension_apply_of_squarefree _ hn]
      exact Finset.measurable_prod _ fun p hp =>
        hX.measurable p (Nat.prime_of_mem_primeFactors hp)
    · simp only [squarefreeExtension_apply_of_not_squarefree _ hn]
      exact measurable_const
  · convert hX.iIndep using 1
    funext p
    exact hp p
  · rw [hp p, hp q]
    exact hX.identDistrib p q p.2 q.2
  · rw [hp p]
    exact hX.centered p p.2
  · rw [hp p]
    exact hX.memLp p p.2

/-- Unpack a Rademacher random multiplicative function into its values at the primes. -/
theorem IsRademacherRMF.exists_primeValues {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) : ∃ X : ℕ → Ω → ℂ,
      IsRademacherPrimeValues X μ ∧ f = fun ω => squarefreeExtension fun p => X p ω :=
  isRademacherRMF_iff_exists.1 hf

/-- Unpack a Steinhaus random multiplicative function into its values at the primes. -/
theorem IsSteinhausRMF.exists_primeValues {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) : ∃ X : ℕ → Ω → ℂ,
      IsSteinhausPrimeValues X μ ∧ f = fun ω => compMultExtension fun p => X p ω :=
  isSteinhausRMF_iff_exists.1 hf

/-- Unpack a squarefree random multiplicative function into its values at the primes. -/
theorem IsSquarefreeRMF.exists_primeValues {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSquarefreeRMF f μ) : ∃ X : ℕ → Ω → ℂ,
      IsRMFPrimeValues X μ ∧ f = fun ω => squarefreeExtension fun p => X p ω :=
  isSquarefreeRMF_iff_exists.1 hf

/-- The squarefree extension of Rademacher values at the primes is a Rademacher random
multiplicative function. -/
theorem IsRademacherPrimeValues.isRademacherRMF {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) :
    IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ :=
  isRademacherRMF_iff_exists.2 ⟨X, hX, rfl⟩

/-- The completely multiplicative extension of Steinhaus values at the primes is a Steinhaus
random multiplicative function. -/
theorem IsSteinhausPrimeValues.isSteinhausRMF {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) :
    IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ :=
  isSteinhausRMF_iff_exists.2 ⟨X, hX, rfl⟩

/-- The squarefree extension of values at the primes satisfying the general hypotheses is a
squarefree random multiplicative function. -/
theorem IsRMFPrimeValues.isSquarefreeRMF {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRMFPrimeValues X μ) :
    IsSquarefreeRMF (fun ω => squarefreeExtension fun p => X p ω) μ :=
  isSquarefreeRMF_iff_exists.2 ⟨X, hX, rfl⟩

theorem IsRademacherRMF.isSquarefreeRMF {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) : IsSquarefreeRMF f μ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  exact hX.isRMFPrimeValues.isSquarefreeRMF

/-! ### Multiplicativity

Whatever the law, a random multiplicative function is multiplicative pointwise in `ω`.
-/

lemma IsSquarefreeRMF.isMultiplicative {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSquarefreeRMF f μ) (ω : Ω) : (f ω).IsMultiplicative := by
  obtain ⟨X, -, rfl⟩ := hf.exists_primeValues
  exact isMultiplicative_squarefreeExtension _

lemma IsSteinhausRMF.isMultiplicative {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) (ω : Ω) : (f ω).IsMultiplicative :=
  ⟨hf.apply_one ω, fun {_ _} _ => hf.apply_mul ω _ _⟩

lemma IsRademacherRMF.isMultiplicative {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (ω : Ω) : (f ω).IsMultiplicative :=
  hf.isSquarefreeRMF.isMultiplicative ω

end RMF
