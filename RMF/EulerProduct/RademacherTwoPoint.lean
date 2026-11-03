/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.TwoPoint
import RMF.EulerProduct.RademacherTwoPointTiltLaw

/-!
# Harper's (5.1) for the Rademacher function — the local two-point moment

For the Steinhaus law, `RMF/EulerProduct/TwoPoint.lean` reaches

`\log ∏_{x<p≤y} A_p = ∑_{x<p≤y} (2 + 2\cos(t\log p))p^{-1-2σ} + O(1/(√x\log x))`

through an expansion: the local factor `E_z|1-zw₁|^{-2}|1-zw₂|^{-2}`, an average over the
**circle**, is expanded with an `O(δ³)` error, controlled by `RMF.localMoment_two_point_bounds`,
`RMF.abs_log_sub_main_le` and `RMF.exists_abs_log_local_two_point_sub_le`.  It also has a closed
form, `RMF.integral_local_two_point_eq` (`RMF/EulerProduct/TwoPointClosed.lean`), whose remainder
is quartic (`RMF.abs_log_local_two_point_sub_le_quartic`).

**The Rademacher local factor is an average over two atoms, and it is exact.**

`E_z ‖1+zw₁‖²‖1+zw₂‖² = (1+‖w₁‖²)(1+‖w₂‖²) + 4(Re w₁)(Re w₂)`

— `RMF.integral_exp_two_localLogAdd_pair_rademacherLaw`, the normaliser of the two-fold tilt.  At
Harper's two points both weights have modulus `ρ = p^{-(1/2+σ)}` and the cross term is
`4ρ²\cos(t\log p)`, so with `n = ρ² = p^{-1-2σ}`

`A_p = (1+n)² + 4n\cos(t\log p) = 1 + (2 + 4\cos(t\log p))·n + n²`,

an **identity**.  There is no expansion and no `O(δ³)`; the only estimate left is
`|\log(1+u) - u| ≤ 2u²`, and the error it leaves is `O(n²) = O(ρ⁴)`, quartic as in the Steinhaus
closed form and *smaller* than the `O(ρ³)` of the Steinhaus expansion.  It is stated at `ρ³`
anyway, because that is what `RMF.sum_prime_Ioc_rpow_cube_le'` sums.

## The main term is different, and the difference is a factor two on the cosine

Steinhaus has `2 + 2\cos(t\log p)`; Rademacher has `2 + 4\cos(t\log p)`.  Both are checked at
`t = 0`: `E|1-zw|^{-4} = ∑_j (j+1)²n^j = 1 + 4n + …` and
`E|1+zw|⁴ = \tfrac12[(1+ρ)⁴+(1-ρ)⁴] = 1 + 6n + n²`.  So the Rademacher two-point moment oscillates
**twice as strongly** in the height, around the same mean — which is the same phenomenon as the
extra `\cos((t₁+t₂)\log p)` in the block covariance, seen at the level of the Euler product.
-/

open MeasureTheory

namespace RMF

/-! ### The local two-point moment, in closed form -/

/-- **The two-atom average of `‖1+zw₁‖²‖1+zw₂‖²`**, in closed form.  This is
`RMF.integral_exp_two_localLogAdd_pair_rademacherLaw` read through the circle identity
`RMF.exp_two_localLogAdd_pair_ae_eq`; no expansion, no error term. -/
lemma integral_normSq_one_add_pair_rademacherLaw {a₁ a₂ : ℂ} (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1) :
    (∫ z, ‖1 + z * a₁‖ ^ 2 * ‖1 + z * a₂‖ ^ 2 ∂rademacherLaw)
      = (1 + ‖a₁‖ ^ 2) * (1 + ‖a₂‖ ^ 2) + 4 * a₁.re * a₂.re := by
  rw [← integral_exp_two_localLogAdd_pair_rademacherLaw h₁ h₂]
  exact (integral_congr_ae (exp_two_localLogAdd_pair_ae_eq h₁ h₂)).symm

/-! ### (5.1)

`∏_p A_p` is what the closed form above estimates, but Harper's left-hand side is an
*expectation*.  Identifying the two is the independence step, and it needs the factorisation over
a **range** of primes: `RMF.IsIIDPrimeValues.integral_prod` on `RMF.primesIco`.

**The squarefree factorisation is unconditional.**  `RMF.randomEulerProductIco_sqfree_eq` is a
pointwise identity, because the squarefree Euler product is a *polynomial*; the Steinhaus twin
`RMF.randomEulerProductIco_compMult_eq` is a product of inverses and needs `0 < Re s` and
unimodularity before it makes sense.  So the Rademacher (5.1) below carries no positivity
hypothesis and never invokes `RMF.half_add_pos` — the hypothesis `400 ≤ x` is used only by the
per-prime estimate, exactly where Harper uses it. -/

/-- **The two-point moment of a squarefree block Euler product factors over the primes of the
block** — the `Ico` sibling of `RMF.integral_norm_randomEulerProductIco_sq_mul_sq_compMult`. -/
theorem integral_norm_randomEulerProductIco_sq_mul_sq_sqfree {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ)
    (y₀ y₁ : ℕ) (s₁ s₂ : ℂ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₂ ω‖ ^ 2
        ∂μ)
      = ∏ p ∈ primesIco y₀ y₁,
          ∫ z, ‖1 + z * (p : ℂ) ^ (-s₁)‖ ^ 2 * ‖1 + z * (p : ℂ) ^ (-s₂)‖ ^ 2 ∂ν := by
  have hae : ∀ ω : Ω,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₂ ω‖ ^ 2
        = ∏ p ∈ primesIco y₀ y₁, ‖1 + X p ω * (p : ℂ) ^ (-s₁)‖ ^ 2
            * ‖1 + X p ω * (p : ℂ) ^ (-s₂)‖ ^ 2 := by
    intro ω
    rw [randomEulerProductIco_sqfree_eq, randomEulerProductIco_sqfree_eq,
      norm_prod, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  have hmeas : ∀ p ∈ primesIco y₀ y₁, AEStronglyMeasurable
      (fun z : ℂ => ‖1 + z * (p : ℂ) ^ (-s₁)‖ ^ 2 * ‖1 + z * (p : ℂ) ^ (-s₂)‖ ^ 2) ν := by
    intro p _
    fun_prop
  rw [integral_congr_ae (Filter.Eventually.of_forall hae),
    hX.integral_prod (fun _ hp => prime_of_mem_primesIco hp)
      (fun p z => ‖1 + z * (p : ℂ) ^ (-s₁)‖ ^ 2 * ‖1 + z * (p : ℂ) ^ (-s₂)‖ ^ 2) hmeas]

/-- The Rademacher case: the left-hand side of Harper's (5.1) is `∏_p Aₚ`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProductIco_sq_mul_sq {Ω : Type*}
    [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ)
    (y₀ y₁ : ℕ) (s₁ s₂ : ℂ) :
    (∫ ω, ‖randomEulerProductIco f y₀ y₁ s₁ ω‖ ^ 2
        * ‖randomEulerProductIco f y₀ y₁ s₂ ω‖ ^ 2 ∂μ)
      = ∏ p ∈ primesIco y₀ y₁,
          ∫ z, ‖1 + z * (p : ℂ) ^ (-s₁)‖ ^ 2 * ‖1 + z * (p : ℂ) ^ (-s₂)‖ ^ 2 ∂rademacherLaw := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  exact integral_norm_randomEulerProductIco_sq_mul_sq_sqfree hX y₀ y₁ s₁ s₂

/-! ### Positivity of the two-point moment

Needed to turn (5.1)'s bound on the *logarithm* of the moment back into a bound on the moment.
The Steinhaus twin `RMF.integral_local_two_point_pos` argues about an integral over the circle;
here the closed form settles it, and the identity that does so is
`(1+a²)(1+b²) - 4ab = (1-ab)² + (a-b)²`. -/

/-- **Each Rademacher local two-point factor is strictly positive**, for `‖w₁‖, ‖w₂‖ < 1`.
From the closed form: `(1+a²)(1+b²) + 4(Re w₁)(Re w₂) ≥ (1-ab)² + (a-b)² > 0` with `a = ‖w₁‖`,
`b = ‖w₂‖`, since `|Re w| ≤ ‖w‖` and `ab < 1`. -/
lemma integral_normSq_one_add_pair_rademacherLaw_pos {a₁ a₂ : ℂ} (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1) :
    0 < ∫ z, ‖1 + z * a₁‖ ^ 2 * ‖1 + z * a₂‖ ^ 2 ∂rademacherLaw := by
  rw [integral_normSq_one_add_pair_rademacherLaw h₁ h₂]
  have hn₁ : (0 : ℝ) ≤ ‖a₁‖ := norm_nonneg _
  have hn₂ : (0 : ℝ) ≤ ‖a₂‖ := norm_nonneg _
  have hcross : -(‖a₁‖ * ‖a₂‖) ≤ a₁.re * a₂.re := by
    have hle : |a₁.re * a₂.re| ≤ ‖a₁‖ * ‖a₂‖ := by
      rw [abs_mul]
      exact mul_le_mul (Complex.abs_re_le_norm a₁) (Complex.abs_re_le_norm a₂)
        (abs_nonneg _) hn₁
    linarith [(abs_le.1 hle).1]
  have hab : (0 : ℝ) < 1 - ‖a₁‖ * ‖a₂‖ := by nlinarith
  nlinarith [hcross, sq_nonneg (‖a₁‖ - ‖a₂‖), mul_pos hab hab]

/-- **The two-point moment over a range of primes is positive.**  Each local factor is positive by
`RMF.integral_normSq_one_add_pair_rademacherLaw_pos`, and the moment is their product. -/
lemma IsRademacherRMF.integral_normSq_mul_normSq_Ico_pos {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ) (y₀ y₁ : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    0 < ∫ ω, ‖randomEulerProductIco f y₀ y₁ s₁ ω‖ ^ 2
        * ‖randomEulerProductIco f y₀ y₁ s₂ ω‖ ^ 2 ∂μ := by
  rw [hf.integral_norm_randomEulerProductIco_sq_mul_sq y₀ y₁ s₁ s₂]
  exact Finset.prod_pos fun p hp => integral_normSq_one_add_pair_rademacherLaw_pos
    (norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs₁)
    (norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs₂)

/-! ### (5.1) at a general pair of heights

The Steinhaus chain reduces a general pair `(1/2+σ+it₁, 1/2+σ+it₂)` to Harper's reduced pair
`1/2+σ`, `1/2+σ+it` by rotating the primes (`RMF.IsSteinhausPrimeValues.integral_comp_rotate`,
from the circle law's invariance under `p ↦ p^{-it}p`), and
`RMF/Probability/RestrictedSecondMoment/Ranges.lean` relies on that rotation.  The Rademacher law
has no such invariance, as Harper remarks (arXiv:1703.06654), so the two-point moment is stated at
a general pair directly.

**The general exponent is `2 + 2\cos((t₁-t₂)\log p) + 2\cos((t₁+t₂)\log p)`**, of which
`2 + 4\cos(t\log p)` is the case `t₁ = 0`, where the two cosines coincide: the same
difference-and-sum pair as in the drift and the covariance.  On Harper's height range both cosine
sums are `O(1)` and the main term is `2` either way. -/

/-- The real-variable content of the general-pair estimate.  With `n = p^{-1-2σ}` the moment is
`1 + u`, `u = (2 + 2c₁ + 2c₂)n + n²`, and `|\log(1+u) - (2+2c₁+2c₂)n| ≤ 2u² + n² ≤ 99n²`, the
weight `2 + 2c₁ + 2c₂` lying in `[-2, 6]`. -/
private lemma abs_log_one_add_local_pair_sub_le {n c₁ c₂ : ℝ} (hn0 : 0 ≤ n) (hn : n ≤ 0.0185)
    (hc₁l : -1 ≤ c₁) (hc₁u : c₁ ≤ 1) (hc₂l : -1 ≤ c₂) (hc₂u : c₂ ≤ 1) :
    |Real.log (1 + ((2 + 2 * c₁ + 2 * c₂) * n + n ^ 2)) - (2 + 2 * c₁ + 2 * c₂) * n|
      ≤ 99 * n ^ 2 := by
  have hlo : -(2 * n) ≤ (2 + 2 * c₁ + 2 * c₂) * n + n ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + c₁) hn0,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + c₂) hn0, sq_nonneg n]
  have hhi : (2 + 2 * c₁ + 2 * c₂) * n + n ^ 2 ≤ 7 * n := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - c₁) hn0,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - c₂) hn0,
      mul_nonneg hn0 (by linarith : (0 : ℝ) ≤ 0.0185 - n)]
  have hu : |(2 + 2 * c₁ + 2 * c₂) * n + n ^ 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hlog := abs_le.1 (abs_log_one_add_sub_le hu)
  have hu2 : ((2 + 2 * c₁ + 2 * c₂) * n + n ^ 2) ^ 2 ≤ 49 * n ^ 2 := by nlinarith [hlo, hhi]
  rw [abs_le]
  constructor <;> nlinarith [hlog.1, hlog.2, hu2, sq_nonneg n]

/-- **The local two-point moment at a general pair of points**,
`E ‖1 + z p^{-s₁}‖² ‖1 + z p^{-s₂}‖²` under `rademacherLaw`. -/
noncomputable def localTwoPointMomentAddAt (p : ℕ) (s₁ s₂ : ℂ) : ℝ :=
  ∫ z, ‖1 + z * (p : ℂ) ^ (-s₁)‖ ^ 2 * ‖1 + z * (p : ℂ) ^ (-s₂)‖ ^ 2 ∂rademacherLaw

/-- **The closed form at a general pair.**
`A_p = (1+n)² + 2n(\cos((t₁-t₂)\log p) + \cos((t₁+t₂)\log p))` — still an identity, and still with
no expansion anywhere. -/
theorem localTwoPointMomentAddAt_eq {p : ℕ} (hp : p.Prime) {σ x y : ℝ} {s₁ s₂ : ℂ}
    (hx : 400 ≤ x) (hxp : x ≤ (p : ℝ)) (hpy : (p : ℝ) ≤ y) (hσ : -(1 / Real.log y) ≤ σ)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ) :
    localTwoPointMomentAddAt p s₁ s₂
      = (1 + (p : ℝ) ^ (-1 - 2 * σ)) ^ 2
        + 2 * ((p : ℝ) ^ (-1 - 2 * σ)
            * (Real.cos ((s₁.im - s₂.im) * Real.log (p : ℝ))
              + Real.cos ((s₁.im + s₂.im) * Real.log (p : ℝ)))) := by
  obtain ⟨-, -, hsmall⟩ := norm_weights_eq (t := (0 : ℝ)) hp hx hxp hpy hσ
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hρ0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2 + σ)) := Real.rpow_nonneg hp0.le _
  have hsq : ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 = (p : ℝ) ^ (-1 - 2 * σ) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 + σ))) 2, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have hnorm : ∀ u : ℂ, u.re = 1 / 2 + σ → ‖(p : ℂ) ^ (-u)‖ = (p : ℝ) ^ (-(1 / 2 + σ)) := by
    intro u hu
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re, hu]
  have hre₁' : ((p : ℂ) ^ (-s₁)).re
      = (p : ℝ) ^ (-(1 / 2 + σ)) * Real.cos (s₁.im * Real.log (p : ℝ)) := by
    rw [re_natCast_cpow_neg hp.pos, hre₁]
  have hre₂' : ((p : ℂ) ^ (-s₂)).re
      = (p : ℝ) ^ (-(1 / 2 + σ)) * Real.cos (s₂.im * Real.log (p : ℝ)) := by
    rw [re_natCast_cpow_neg hp.pos, hre₂]
  rw [localTwoPointMomentAddAt,
    integral_normSq_one_add_pair_rademacherLaw (by rw [hnorm s₁ hre₁]; linarith)
      (by rw [hnorm s₂ hre₂]; linarith),
    hnorm s₁ hre₁, hnorm s₂ hre₂, hre₁', hre₂',
    show (s₁.im - s₂.im) * Real.log (p : ℝ)
        = s₁.im * Real.log (p : ℝ) - s₂.im * Real.log (p : ℝ) by ring,
    show (s₁.im + s₂.im) * Real.log (p : ℝ)
        = s₁.im * Real.log (p : ℝ) + s₂.im * Real.log (p : ℝ) by ring,
    Real.cos_sub, Real.cos_add, ← hsq]
  ring

/-- **Positivity at a general pair.**  `(1+n)² + 4\mathrm{Re}(w₁)\mathrm{Re}(w₂) > 0`, by
`RMF.integral_normSq_one_add_pair_rademacherLaw_pos`. -/
lemma localTwoPointMomentAddAt_pos {p : ℕ} (hp : p.Prime) {σ x y : ℝ} {s₁ s₂ : ℂ}
    (hx : 400 ≤ x) (hxp : x ≤ (p : ℝ)) (hpy : (p : ℝ) ≤ y) (hσ : -(1 / Real.log y) ≤ σ)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ) :
    0 < localTwoPointMomentAddAt p s₁ s₂ := by
  obtain ⟨-, -, hsmall⟩ := norm_weights_eq (t := (0 : ℝ)) hp hx hxp hpy hσ
  have hnorm : ∀ u : ℂ, u.re = 1 / 2 + σ → ‖(p : ℂ) ^ (-u)‖ = (p : ℝ) ^ (-(1 / 2 + σ)) := by
    intro u hu
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re, hu]
  exact integral_normSq_one_add_pair_rademacherLaw_pos
    (by rw [hnorm s₁ hre₁]; linarith) (by rw [hnorm s₂ hre₂]; linarith)

/-- **The per-prime form of (5.1) at a general pair.**  The summand is
`(2 + 2\cos((t₁-t₂)\log p) + 2\cos((t₁+t₂)\log p))p^{-1-2σ}`. -/
theorem exists_abs_log_localTwoPointMomentAddAt_sub_le :
    ∃ C > 0, ∀ (p : ℕ), p.Prime → ∀ (σ x y : ℝ) (s₁ s₂ : ℂ), 400 ≤ x → x ≤ (p : ℝ) →
      (p : ℝ) ≤ y → -(1 / Real.log y) ≤ σ → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
      |Real.log (localTwoPointMomentAddAt p s₁ s₂)
          - (2 + 2 * Real.cos ((s₁.im - s₂.im) * Real.log (p : ℝ))
              + 2 * Real.cos ((s₁.im + s₂.im) * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ)|
        ≤ C * (p : ℝ) ^ (-(3 / 2) - 3 * σ) := by
  refine ⟨100, by norm_num, fun p hp σ x y s₁ s₂ hx hxp hpy hσ hre₁ hre₂ => ?_⟩
  obtain ⟨-, -, hsmall⟩ := norm_weights_eq (t := (0 : ℝ)) hp hx hxp hpy hσ
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hρ0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2 + σ)) := Real.rpow_nonneg hp0.le _
  have hsq : ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 = (p : ℝ) ^ (-1 - 2 * σ) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 + σ))) 2, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have hcube : ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 3 = (p : ℝ) ^ (-(3 / 2) - 3 * σ) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 + σ))) 3, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have hn0 : (0 : ℝ) ≤ (p : ℝ) ^ (-1 - 2 * σ) := by rw [← hsq]; positivity
  have hn : (p : ℝ) ^ (-1 - 2 * σ) ≤ 0.0185 := by
    rw [← hsq]
    nlinarith [hsmall, hρ0]
  have hc₁ := abs_le.1 (Real.abs_cos_le_one ((s₁.im - s₂.im) * Real.log (p : ℝ)))
  have hc₂ := abs_le.1 (Real.abs_cos_le_one ((s₁.im + s₂.im) * Real.log (p : ℝ)))
  have hA : localTwoPointMomentAddAt p s₁ s₂
      = 1 + ((2 + 2 * Real.cos ((s₁.im - s₂.im) * Real.log (p : ℝ))
              + 2 * Real.cos ((s₁.im + s₂.im) * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ)
          + ((p : ℝ) ^ (-1 - 2 * σ)) ^ 2) := by
    rw [localTwoPointMomentAddAt_eq hp hx hxp hpy hσ hre₁ hre₂]
    ring
  have hquart : ((p : ℝ) ^ (-1 - 2 * σ)) ^ 2 ≤ (p : ℝ) ^ (-(3 / 2) - 3 * σ) := by
    rw [← hcube, ← hsq]
    nlinarith [mul_nonneg (pow_nonneg hρ0 3)
      (by linarith : (0 : ℝ) ≤ 1 - (p : ℝ) ^ (-(1 / 2 + σ)))]
  have hL0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(3 / 2) - 3 * σ) := Real.rpow_nonneg hp0.le _
  rw [hA]
  refine le_trans (abs_log_one_add_local_pair_sub_le hn0 hn hc₁.1 hc₁.2 hc₂.1 hc₂.2) ?_
  linarith

/-- **Harper's (5.1) as a product of local moments, at a general pair.**  The law-free and
height-free `RMF.abs_log_prod_sub_sum_le` and `RMF.sum_prime_Ioc_rpow_cube_le'`, fed the two
per-prime inputs `RMF.localTwoPointMomentAddAt_pos` and
`RMF.exists_abs_log_localTwoPointMomentAddAt_sub_le`. -/
theorem exists_abs_log_prod_localTwoPointMomentAddAt_le :
    ∃ C > 0, ∀ (σ x y : ℝ) (s₁ s₂ : ℂ), 400 ≤ x → x ≤ y → -(1 / Real.log y) ≤ σ →
      s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
      |Real.log (∏ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, localTwoPointMomentAddAt p s₁ s₂)
          - ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p,
              (2 + 2 * Real.cos ((s₁.im - s₂.im) * Real.log (p : ℝ))
                  + 2 * Real.cos ((s₁.im + s₂.im) * Real.log (p : ℝ)))
                * (p : ℝ) ^ (-1 - 2 * σ)|
        ≤ C / (Real.sqrt x * Real.log x) := by
  obtain ⟨C₁, hC₁, hloc⟩ := exists_abs_log_localTwoPointMomentAddAt_sub_le
  refine ⟨C₁ * (Real.exp 3 * (8 * Real.log 4)), by positivity,
    fun σ x y s₁ s₂ hx hxy hσ hre₁ hre₂ => ?_⟩
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hrange : ∀ q ∈ {q ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ | Nat.Prime q},
      Nat.Prime q ∧ x ≤ (q : ℝ) ∧ (q : ℝ) ≤ y := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
    refine ⟨hq.2, ?_, ?_⟩
    · have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hq.1.1
      linarith
    · exact le_trans (by exact_mod_cast hq.1.2) (Nat.floor_le hy0)
  refine le_trans (abs_log_prod_sub_sum_le (C := C₁)
    (b := fun q => (q : ℝ) ^ (-(3 / 2) - 3 * σ)) (fun q hq => ?_) (fun q hq => ?_)) ?_
  · obtain ⟨hqp, hxq, hqy⟩ := hrange q hq
    exact localTwoPointMomentAddAt_pos hqp hx hxq hqy hσ hre₁ hre₂
  · obtain ⟨hqp, hxq, hqy⟩ := hrange q hq
    exact hloc q hqp σ x y s₁ s₂ hx hxq hqy hσ hre₁ hre₂
  · calc C₁ * ∑ q ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime q, (q : ℝ) ^ (-(3 / 2) - 3 * σ)
        ≤ C₁ * (Real.exp 3 * (8 * Real.log 4 / (Real.sqrt x * Real.log x))) :=
          mul_le_mul_of_nonneg_left (sum_prime_Ioc_rpow_cube_le' (by linarith) hxy hσ) hC₁.le
      _ = C₁ * (Real.exp 3 * (8 * Real.log 4)) / (Real.sqrt x * Real.log x) := by ring

/-- **Rademacher analogue of Harper's (5.1), general heights.**  For `F` the Euler product over
the primes of `(x, y]`, `400 ≤ x ≤ y`, `σ ≥ -1/\log y`, `Re s_i = 1/2 + σ` and `t_i = Im s_i`,
`\log E[‖F(s₁)‖²‖F(s₂)‖²]` is, up to `O(1/(√x\log x))`,
`∑_{x<p≤y} (2 + 2\cos((t₁-t₂)\log p) + 2\cos((t₁+t₂)\log p))p^{-1-2σ}`.  The Steinhaus proof
reaches a general pair by rotating the primes, which the Rademacher law does not permit. -/
theorem exists_abs_log_integral_two_point_le_rademacher_at {Ω : Type*} [MeasurableSpace Ω] :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (σ x y : ℝ) (s₁ s₂ : ℂ), 400 ≤ x → x ≤ y → -(1 / Real.log y) ≤ σ →
      s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
      |Real.log (∫ ω, ‖randomEulerProductIco f (⌊x⌋₊ + 1) (⌊y⌋₊ + 1) s₁ ω‖ ^ 2
              * ‖randomEulerProductIco f (⌊x⌋₊ + 1) (⌊y⌋₊ + 1) s₂ ω‖ ^ 2 ∂μ)
          - ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p,
              (2 + 2 * Real.cos ((s₁.im - s₂.im) * Real.log (p : ℝ))
                  + 2 * Real.cos ((s₁.im + s₂.im) * Real.log (p : ℝ)))
                * (p : ℝ) ^ (-1 - 2 * σ)|
        ≤ C / (Real.sqrt x * Real.log x) := by
  obtain ⟨C, hC, h⟩ := exists_abs_log_prod_localTwoPointMomentAddAt_le
  refine ⟨C, hC, fun f μ hf σ x y s₁ s₂ hx hxy hσ hre₁ hre₂ => ?_⟩
  rw [hf.integral_norm_randomEulerProductIco_sq_mul_sq, ← filter_prime_Ioc_eq_primesIco]
  simpa only [localTwoPointMomentAddAt] using h σ x y s₁ s₂ hx hxy hσ hre₁ hre₂

end RMF
