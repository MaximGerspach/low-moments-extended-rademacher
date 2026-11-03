/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.TiltedLaw

/-!
# The values at the primes under Harper's tilt

The two halves of the tilting development meet here.  `RMF/Probability/Tilting.lean` proves that
an exponential tilt by a sum over a finite subfamily leaves an independent family independent and
tilts each of its laws individually; `RMF/EulerProduct/TiltedLaw.lean` computes every moment of
the tilted circle law.  Neither is of any use until they are instantiated at the actual object —
the values `f(p)` of a Steinhaus random multiplicative function, under the measure tilted by
`2 log‖F_y(s)‖`.  That is what this file does:

* `RMF.IsSteinhausPrimeValues.iIndepFun_tiltedMeasure` — the `f(p)` are still independent under
  `P~`;
* `RMF.IsSteinhausPrimeValues.map_tiltedMeasure` — and for `p < y` the law of `f(p)` under `P~` is
  the tilted circle law `ν_{p^{-s}}`, whose mean, variance and third absolute moment
  `RMF/EulerProduct/TiltedLaw.lean` already supplies.

## The index promotion

`RMF.IsRMFPrimeValues.iIndep` is stated over `Nat.Primes`, while the Euler product sums over
`Nat.primesBelow y : Finset ℕ`.  `RMF.primesBelowSub` promotes the latter to a `Finset Nat.Primes`
and `RMF.sum_primesBelowSub` moves sums across; that is the only friction, and it is confined to
this file.
-/

open Finset MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Promoting the index -/

/-- The primes below `y`, as a `Finset Nat.Primes`. -/
noncomputable def primesBelowSub (y : ℕ) : Finset Nat.Primes :=
  (Nat.primesBelow y).subtype Nat.Prime

@[simp]
lemma mem_primesBelowSub {y : ℕ} {p : Nat.Primes} :
    p ∈ primesBelowSub y ↔ (p : ℕ) ∈ Nat.primesBelow y :=
  Finset.mem_subtype

/-- Sums over the primes below `y` are the same read either way.  Every member of
`Nat.primesBelow y` is prime, so `Finset.subtype` loses nothing. -/
lemma sum_primesBelowSub {M : Type*} [AddCommMonoid M] (y : ℕ) (F : ℕ → M) :
    ∑ p ∈ primesBelowSub y, F (p : ℕ) = ∑ p ∈ Nat.primesBelow y, F p :=
  Finset.sum_subtype_of_mem F fun _ hp => Nat.prime_of_mem_primesBelow hp

/-! ### The tilt exponent, indexed by the primes -/

/-- The local tilt exponent `2 log‖(1 - z p^{-s})⁻¹‖`, as a function of the prime and the value.
Harper's tilt is the sum of these over `p < y`.  Naming it keeps every statement below in the
shape `g i (X i ω)` that the tilt lemmas consume, and keeps the elaborator out of a higher-order
search for `g`. -/
noncomputable def localTilt (s : ℂ) (p : Nat.Primes) (z : ℂ) : ℝ :=
  2 * localLog (((p : ℕ) : ℂ) ^ (-s)) z

lemma measurable_localTilt (s : ℂ) (p : Nat.Primes) : Measurable (localTilt s p) :=
  (measurable_localLog _).const_mul 2

/-- Harper's tilt exponent as a sum over `Nat.Primes`: the shape
`RMF.iIndepFun_tilted_finsetSum` consumes. -/
lemma tiltedMeasure_eq_tilted_finsetSum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ
      = μ.tilted fun ω => ∑ p ∈ primesBelowSub y, localTilt s p (X (p : ℕ) ω) := by
  rw [tiltedMeasure_eq_tilted_sum hX y hs]
  congr 1
  funext ω
  exact (sum_primesBelowSub y fun p => 2 * localLog ((p : ℂ) ^ (-s)) (X p ω)).symm

/-- Each local weight is integrable: it is bounded on the circle by `(1 - p^{-Re s})⁻²`. -/
lemma integrable_exp_localTilt {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun ω => Real.exp (localTilt s p (X (p : ℕ) ω))) μ := by
  have hprob := hX.isProbabilityMeasure
  have hw : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := norm_prime_cpow_neg_lt_one p.2 hs
  have hae : ∀ᵐ ω ∂μ, ‖X (p : ℕ) ω‖ = 1 := by
    refine ((hX.hasLaw (p : ℕ) p.2).ae_iff ?_).2 norm_eq_one_steinhausLaw
    exact measurableSet_setOf.1 (measurableSet_eq_fun measurable_norm measurable_const)
  refine (memLp_top_of_bound
    (((measurable_localTilt s p).comp (hX.measurable (p : ℕ) p.2)).exp.aestronglyMeasurable)
    (((1 - ‖((p : ℕ) : ℂ) ^ (-s)‖)⁻¹) ^ 2) ?_).integrable le_top
  filter_upwards [hae] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact exp_two_localLog_le hω hw

/-! ### The two instantiations -/

/-- **The values at the primes stay independent under Harper's tilt.**  This is
`RMF.iIndepFun_tilted_finsetSum` at the family `f(p)`, the finite set `primesBelow y`, and the
local exponents `RMF.localTilt`. -/
theorem IsSteinhausPrimeValues.iIndepFun_tiltedMeasure {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iIndepFun (fun p : Nat.Primes => X (p : ℕ))
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ) := by
  rw [tiltedMeasure_eq_tilted_finsetSum hX y hs]
  exact iIndepFun_tilted_finsetSum (𝓧 := fun _ : Nat.Primes => ℂ)
    (X := fun p : Nat.Primes => X (p : ℕ)) (g := localTilt s)
    hX.iIndep (fun p => hX.measurable (p : ℕ) p.2) (measurable_localTilt s)
    (fun p _ => integrable_exp_localTilt hX p hs)

/-- **`P~` is a probability measure**, in the `IsSteinhausPrimeValues` phrasing.  The same fact as
`RMF.IsSteinhausRMF.isProbabilityMeasure_tiltedMeasure`, at the family of prime values rather than
the multiplicative function it generates — which is the form every moment statement here needs. -/
theorem IsSteinhausPrimeValues.isProbabilityMeasure_tiltedMeasure {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    IsProbabilityMeasure (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ) :=
  IsSteinhausRMF.isProbabilityMeasure_tiltedMeasure hX.isSteinhausRMF y hs

/-- **The local logarithms stay independent under the tilt.**  This is
`RMF.IsSteinhausPrimeValues.iIndepFun_tiltedMeasure` pushed through `iIndepFun.comp`: the summands
`ξ_p = localLog (w p) (f(p))` of `log‖F_y(s)‖` are an independent family of *real* random variables
under `P~`, which is what the Lindeberg telescope consumes.

The weights `w p` are arbitrary; in the application `w p = p^{-1/2-σ-it}`. -/
theorem IsSteinhausPrimeValues.iIndepFun_localLog_tiltedMeasure {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) (w : Nat.Primes → ℂ) :
    iIndepFun (fun (p : Nat.Primes) (ω : Ω) => localLog (w p) (X (p : ℕ) ω))
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ) :=
  (hX.iIndepFun_tiltedMeasure y hs).comp (fun p => localLog (w p))
    (fun p => measurable_localLog (w p))

/-- **The law of `f(p)` under the tilt is the tilted circle law.**  For `p < y` — the primes the
tilt names — the law of `f(p)` becomes `steinhausLaw` tilted by `2 localLog (p^{-s})`, which is the
Poisson kernel at `conj (p^{-s})`.  Its mean, variance and third absolute moment are
`RMF.integral_localLog_tilted_steinhausLaw`, `RMF.abs_integral_localLog_sq_tilted_sub_le` and
`RMF.integral_abs_localLog_cube_tilted_le`. -/
theorem IsSteinhausPrimeValues.map_tiltedMeasure {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) :
    (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ).map (X (p : ℕ))
      = steinhausLaw.tilted (localTilt s p) := by
  rw [tiltedMeasure_eq_tilted_finsetSum hX y hs,
    map_tilted_finsetSum_of_mem (𝓧 := fun _ : Nat.Primes => ℂ)
      (X := fun q : Nat.Primes => X (q : ℕ)) (g := localTilt s)
      hX.iIndep (fun q => hX.measurable (q : ℕ) q.2) (measurable_localTilt s)
      (fun q _ => integrable_exp_localTilt hX q hs) hp,
    (hX.hasLaw (p : ℕ) p.2).map_eq]

end RMF
