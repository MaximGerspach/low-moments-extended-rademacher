/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.RademacherTiltedLaw
import RMF.EulerProduct.TiltedPrimes

/-!
# The Rademacher tilt, indexed by the primes

The layer between `RMF/EulerProduct/RademacherTiltedLaw.lean` — which computes the tilted law at
a single prime — and the block estimates, which need the primes to stay **independent** under the
tilt and need each one's law to be the tilted local law.

The Steinhaus counterpart is `RMF/EulerProduct/TiltedPrimes.lean`, and the two are line for line
the same argument: rewrite the tilt exponent as a sum of functions of the individual values, and
hand that to the factorisation results of `RMF/Probability/Tilting.lean`, which are generic.  The
model enters at exactly one point: the only thing the tilted layer needs of the law is
`∀ᵐ z ∂ν, ‖z‖ = 1`, here `RMF.norm_eq_one_rademacherLaw`, used once, in
`RMF.integrable_exp_localTiltAdd`.
Everything else is the same generic machinery the Steinhaus side calls.

## The one real difference

`RMF.tiltedMeasure` is generic in the multiplicative function, so `tiltedMeasure` at the
**squarefree** extension is already the Rademacher tilt — no new definition is needed.  But it is
not the same measure as the Steinhaus one at the same `X`: the local factor is `1 + z p^{-s}`
rather than `(1 - z p^{-s})⁻¹`, so the exponent is `+2 log‖1 + z p^{-s}‖` where the Steinhaus one
is `-2 log‖1 - z p^{-s}‖`.  That sign is the whole reason this file exists rather than reusing
`RMF.tiltedMeasure_eq_tilted_finsetSum`.
-/

open Finset MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The local tilt exponent -/

/-- The local tilt exponent `2 log‖1 + z p^{-s}‖`, as a function of the prime and the value.
The Rademacher counterpart of `RMF.localTilt`, and named for the same reason: it keeps every
statement below in the shape `g i (X i ω)` that the tilt lemmas consume. -/
noncomputable def localTiltAdd (s : ℂ) (p : Nat.Primes) (z : ℂ) : ℝ :=
  2 * localLogAdd (((p : ℕ) : ℂ) ^ (-s)) z

lemma measurable_localTiltAdd (s : ℂ) (p : Nat.Primes) : Measurable (localTiltAdd s p) :=
  (measurable_localLogAdd _).const_mul 2

/-- **The single point where the law enters.**  Each local weight is bounded on the circle by
`(1 + ‖p^{-s}‖) ^ 2`, hence integrable.  The only fact used about `rademacherLaw` is that it
lives on the unit circle. -/
lemma integrable_exp_localTiltAdd {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun ω => Real.exp (localTiltAdd s p (X (p : ℕ) ω))) μ := by
  have hprob := hX.isProbabilityMeasure
  have hw : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := norm_prime_cpow_neg_lt_one p.2 hs
  have hae : ∀ᵐ ω ∂μ, ‖X (p : ℕ) ω‖ = 1 := by
    refine ((hX.hasLaw (p : ℕ) p.2).ae_iff ?_).2 norm_eq_one_rademacherLaw
    exact measurableSet_setOf.1 (measurableSet_eq_fun measurable_norm measurable_const)
  refine (memLp_top_of_bound
    (((measurable_localTiltAdd s p).comp (hX.measurable (p : ℕ) p.2)).exp.aestronglyMeasurable)
    ((1 + ‖((p : ℕ) : ℂ) ^ (-s)‖) ^ 2) ?_).integrable le_top
  filter_upwards [hae] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact exp_two_localLogAdd_le hω hw

/-! ### The tilt as a sum over the primes -/

/-- **The tilt exponent is a sum of functions of the individual values.**  This is
`RMF.logNormEuler_ae_eq_sum_rademacher` with the factor `2` distributed. -/
lemma tiltExponent_ae_eq_sum_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    tiltExponent (fun ω => squarefreeExtension fun p => X p ω) y s
      =ᵐ[μ] fun ω => ∑ p ∈ Nat.primesBelow y, 2 * localLogAdd ((p : ℂ) ^ (-s)) (X p ω) := by
  filter_upwards [logNormEuler_ae_eq_sum_rademacher hX y hs] with ω hω
  rw [tiltExponent, hω, Finset.mul_sum]

/-- **The tilted measure in the form the factorisation results consume**, indexed by
`Nat.Primes`. -/
lemma tiltedMeasure_eq_tilted_finsetSum_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ
      = μ.tilted fun ω => ∑ p ∈ primesBelowSub y, localTiltAdd s p (X (p : ℕ) ω) := by
  rw [tiltedMeasure, tilted_congr (tiltExponent_ae_eq_sum_rademacher hX y hs)]
  congr 1
  funext ω
  exact (sum_primesBelowSub y fun p => 2 * localLogAdd ((p : ℂ) ^ (-s)) (X p ω)).symm

/-! ### What the tilt preserves, and what it changes -/

/-- **The values at distinct primes stay independent under the tilt.**  The tilt exponent is a
sum of functions of the individual values, so it factors — `RMF.iIndepFun_tilted_finsetSum` at
the family `X p`, the finite set `primesBelowSub y`, and the local exponents
`RMF.localTiltAdd`. -/
theorem iIndepFun_tiltedMeasure_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iIndepFun (fun p : Nat.Primes => X (p : ℕ))
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) := by
  rw [tiltedMeasure_eq_tilted_finsetSum_rademacher hX y hs]
  exact iIndepFun_tilted_finsetSum (𝓧 := fun _ : Nat.Primes => ℂ)
    (X := fun p : Nat.Primes => X (p : ℕ)) (g := localTiltAdd s)
    hX.iIndep (fun p => hX.measurable (p : ℕ) p.2) (measurable_localTiltAdd s)
    (fun p _ => integrable_exp_localTiltAdd hX p hs)

/-- **The tilt weight is integrable**, so `P~` is a probability measure.  The exponent is a sum
of local weights over `Nat.primesBelow y`, each bounded on the circle. -/
lemma integrable_exp_tiltExponent_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun ω =>
      Real.exp (tiltExponent (fun ω => squarefreeExtension fun p => X p ω) y s ω)) μ := by
  have hprob := hX.isProbabilityMeasure
  have hrmf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hnorm : ∀ᵐ ω ∂μ, ∀ p ∈ Nat.primesBelow y, ‖X p ω‖ = 1 := by
    refine (Filter.eventually_all_finset _).2 fun p hp => ?_
    refine ((hX.hasLaw p (Nat.prime_of_mem_primesBelow hp)).ae_iff ?_).2 norm_eq_one_rademacherLaw
    exact measurableSet_setOf.1 (measurableSet_eq_fun measurable_norm measurable_const)
  have hm : AEStronglyMeasurable (fun ω =>
      Real.exp (tiltExponent (fun ω => squarefreeExtension fun p => X p ω) y s ω)) μ :=
    ((hrmf.aemeasurable_logNormEuler y hs).const_mul 2).exp.aestronglyMeasurable
  refine (memLp_top_of_bound hm
    (∏ p ∈ Nat.primesBelow y, (1 + ‖((p : ℕ) : ℂ) ^ (-s)‖) ^ 2) ?_).integrable le_top
  filter_upwards [tiltExponent_ae_eq_sum_rademacher hX y hs, hnorm] with ω hω hn
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), hω, Real.exp_sum]
  refine Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) fun p hp => ?_
  exact exp_two_localLogAdd_le (hn p hp) (norm_prime_cpow_neg_lt_one
    (Nat.prime_of_mem_primesBelow hp) hs)

/-- **`P~` is a probability measure**, in the `IsRademacherPrimeValues` phrasing. -/
theorem isProbabilityMeasure_tiltedMeasure_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    IsProbabilityMeasure
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) := by
  have hprob := hX.isProbabilityMeasure
  exact isProbabilityMeasure_tilted (integrable_exp_tiltExponent_rademacher hX y hs)

/-- **The local logarithms stay independent under the tilt.**
`RMF.iIndepFun_tiltedMeasure_rademacher` pushed through `iIndepFun.comp`: the summands
`ξ_p = localLogAdd (w p) (f p)` of `log‖F_y(s)‖` are an independent family of *real* random
variables under `P~`, which is what the Lindeberg telescope consumes.  The weights `w p` are
arbitrary. -/
theorem iIndepFun_localLogAdd_tiltedMeasure_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) (w : Nat.Primes → ℂ) :
    iIndepFun (fun (p : Nat.Primes) (ω : Ω) => localLogAdd (w p) (X (p : ℕ) ω))
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) :=
  (iIndepFun_tiltedMeasure_rademacher hX y hs).comp (fun p => localLogAdd (w p))
    (fun p => measurable_localLogAdd (w p))

/-- **The law of `f p` under the tilt is the tilted Rademacher law.**  For `p < y` — the primes
the tilt names — the law of `f p` becomes `rademacherLaw` tilted by `2 localLogAdd (p^{-s})`,
which is the two-point law of `RMF.integral_tilted_localLogAdd_rademacherLaw`.  Its drift, second
moment and third absolute moment are `RMF.abs_integral_localLogAdd_tilted_sub_le`,
`RMF.abs_integral_localLogAdd_sq_tilted_sub_le` and
`RMF.integral_abs_localLogAdd_cube_tilted_le`. -/
theorem map_tiltedMeasure_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) :
    (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ).map (X (p : ℕ))
      = rademacherLaw.tilted (localTiltAdd s p) := by
  rw [tiltedMeasure_eq_tilted_finsetSum_rademacher hX y hs,
    map_tilted_finsetSum_of_mem (𝓧 := fun _ : Nat.Primes => ℂ)
      (X := fun q : Nat.Primes => X (q : ℕ)) (g := localTiltAdd s)
      hX.iIndep (fun q => hX.measurable (q : ℕ) q.2) (measurable_localTiltAdd s)
      (fun q _ => integrable_exp_localTiltAdd hX q hs) hp,
    (hX.hasLaw (p : ℕ) p.2).map_eq]

end RMF
