/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.RademacherTwoPointTilt
import RMF.EulerProduct.RademacherTiltedMoments

/-!
# The moments of the two-fold Rademacher tilt

`RMF/EulerProduct/RademacherTwoPointTilt.lean` identifies the law of `f p` under
`RMF.tiltedMeasure₂` as `rademacherLaw` tilted by `RMF.localTiltAdd₂`.  This file transports the
integrability and the moments of that law from `ℂ` to `Ω`, exactly as
`RMF/EulerProduct/RademacherTiltedMoments.lean` does at one point.

## One lemma does the integrability, again

The tilted law lives on the unit circle and is a probability measure, so any measurable function
bounded there is integrable: `RMF.integrable_of_ae_bound_tilted_pair_rademacherLaw`.  The
Steinhaus file (`RMF/EulerProduct/TwoPointTiltMoments.lean`) needs one integrability lemma per
moment because its tilt is a product of Poisson kernels and the bound has to be re-derived each
time.

## The one genuinely new object

The one-point file has no analogue of the **cross term** `localLogAdd v · localLogAdd w`, which is
what `RMF.blockMatchedCov` sums.  It is no harder than the square — the same circle bound applied
to each factor — but it has to be stated, so it is here.

Cauchy–Schwarz under this tilt is *not* here: it needs `RMF.sq_integral_le_integral_mul_self` from
`RMF/Probability/MatchingGaussian.lean`, so it sits with the pair block statistics, exactly as its
one-point twin sits in `RMF/Probability/RademacherWindowComparison.lean` rather than in
`RademacherTiltedMoments`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### Integrability under the two-fold tilted law -/

/-- **The whole integrability theory of the two-fold Rademacher tilt.**  The tilted law lives on
the unit circle and is a probability measure, so any measurable function bounded there is
integrable. -/
lemma integrable_of_ae_bound_tilted_pair_rademacherLaw {a₁ a₂ : ℂ} (h₁ : ‖a₁‖ < 1)
    (h₂ : ‖a₂‖ < 1) {g : ℂ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ z : ℂ, ‖z‖ = 1 → |g z| ≤ C) :
    Integrable g
      (rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z) := by
  have hprob := isProbabilityMeasure_tilted_localLogAdd_pair h₁ h₂
  have hcirc : ∀ᵐ z ∂(rademacherLaw.tilted
      fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z), ‖z‖ = 1 :=
    (tilted_absolutelyContinuous rademacherLaw _) norm_eq_one_rademacherLaw
  refine (memLp_top_of_bound hg.aestronglyMeasurable C ?_).integrable le_top
  filter_upwards [hcirc] with z hz
  rw [Real.norm_eq_abs]
  exact hC z hz

lemma integrable_localLogAdd_tilted_pair {a₁ a₂ w : ℂ} (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1)
    (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (localLogAdd w)
      (rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z) :=
  integrable_of_ae_bound_tilted_pair_rademacherLaw h₁ h₂ (measurable_localLogAdd w)
    fun _ hz => abs_localLogAdd_le_of_norm_le hz hw

lemma integrable_localLogAdd_sq_tilted_pair {a₁ a₂ w : ℂ} (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1)
    (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun z => localLogAdd w z ^ 2)
      (rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z) :=
  integrable_of_ae_bound_tilted_pair_rademacherLaw h₁ h₂
    ((measurable_localLogAdd w).pow_const 2) (C := (11 / 5 * ‖w‖) ^ 2) fun _ hz => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_localLogAdd_le_of_norm_le hz hw) 2

/-- **The cross term**, which the one-point file has no analogue of: it is what
`RMF.blockMatchedCov` sums. -/
lemma integrable_localLogAdd_mul_tilted_pair {a₁ a₂ v w : ℂ} (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1)
    (hv : ‖v‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun z => localLogAdd v z * localLogAdd w z)
      (rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z) :=
  integrable_of_ae_bound_tilted_pair_rademacherLaw h₁ h₂
    ((measurable_localLogAdd v).mul (measurable_localLogAdd w))
    (C := (11 / 5 * ‖v‖) * (11 / 5 * ‖w‖)) fun _ hz => by
      rw [abs_mul]
      exact mul_le_mul (abs_localLogAdd_le_of_norm_le hz hv)
        (abs_localLogAdd_le_of_norm_le hz hw) (abs_nonneg _) (by positivity)

lemma integrable_abs_cube_localLogAdd_tilted_pair {a₁ a₂ w : ℂ} (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1)
    (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun z => |localLogAdd w z| ^ 3)
      (rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z) :=
  integrable_of_ae_bound_tilted_pair_rademacherLaw h₁ h₂
    (measurable_abs_cube_localLogAdd w) (C := (11 / 5 * ‖w‖) ^ 3) fun _ hz => by
      rw [abs_pow, abs_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_localLogAdd_le_of_norm_le hz hw) 3

/-! ### Transport to the two-fold `P~` -/

/-- **The transfer.**  A function of the value at one prime has the same two-fold-tilted mean as
it has under the tilted local law, because `RMF.map_tiltedMeasure₂_rademacher` says the law *is*
that one. -/
theorem integral_comp_tiltedMeasure₂_rademacher (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) {g : ℂ → ℝ}
    (hg : Integrable g (rademacherLaw.tilted fun z =>
      2 * localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) z + 2 * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) z)) :
    (∫ ω, g (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
      = ∫ z, g z ∂(rademacherLaw.tilted fun z =>
          2 * localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) z
            + 2 * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) z) := by
  have hmap := map_tiltedMeasure₂_rademacher hX y hs₁ hs₂ hp
  rw [← integral_map (hX.measurable (p : ℕ) p.2).aemeasurable
    (by rw [hmap]; exact hg.aestronglyMeasurable), hmap]
  rfl

/-- **Transport of integrability**, the companion of the transfer. -/
theorem integrable_comp_tiltedMeasure₂_rademacher (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) {g : ℂ → ℝ}
    (hg : Integrable g (rademacherLaw.tilted fun z =>
      2 * localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) z + 2 * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) z)) :
    Integrable (fun ω => g (X (p : ℕ) ω))
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) := by
  refine Integrable.comp_aemeasurable ?_ (hX.measurable (p : ℕ) p.2).aemeasurable
  rw [map_tiltedMeasure₂_rademacher hX y hs₁ hs₂ hp]
  exact hg

theorem integrable_localLogAdd_tiltedMeasure₂ (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun ω => localLogAdd w (X (p : ℕ) ω))
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) :=
  integrable_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ hp
    (integrable_localLogAdd_tilted_pair (norm_prime_cpow_neg_lt_one p.2 hs₁)
      (norm_prime_cpow_neg_lt_one p.2 hs₂) hw)

theorem integrable_localLogAdd_sq_tiltedMeasure₂ (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun ω => localLogAdd w (X (p : ℕ) ω) ^ 2)
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) :=
  integrable_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ hp
    (g := fun z => localLogAdd w z ^ 2)
    (integrable_localLogAdd_sq_tilted_pair (norm_prime_cpow_neg_lt_one p.2 hs₁)
      (norm_prime_cpow_neg_lt_one p.2 hs₂) hw)

/-- The cross term, transported — the summand of `RMF.blockMatchedCov`. -/
theorem integrable_localLogAdd_mul_tiltedMeasure₂ (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) {v w : ℂ} (hv : ‖v‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun ω => localLogAdd v (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω))
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) :=
  integrable_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ hp
    (g := fun z => localLogAdd v z * localLogAdd w z)
    (integrable_localLogAdd_mul_tilted_pair (norm_prime_cpow_neg_lt_one p.2 hs₁)
      (norm_prime_cpow_neg_lt_one p.2 hs₂) hv hw)

theorem integrable_abs_cube_localLogAdd_tiltedMeasure₂ (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun ω => |localLogAdd w (X (p : ℕ) ω)| ^ 3)
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) :=
  integrable_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ hp
    (g := fun z => |localLogAdd w z| ^ 3)
    (integrable_abs_cube_localLogAdd_tilted_pair (norm_prime_cpow_neg_lt_one p.2 hs₁)
      (norm_prime_cpow_neg_lt_one p.2 hs₂) hw)

/-! ### The moments of the two-fold tilted law, at one point of the circle

Each is `RMF.integral_tilted_pair_eq_add_rademacherLaw` at one `g`, so each is an **untilted**
Rademacher moment plus `RMF.pairTiltMultiplier` times an increment.  `RademacherLogField` already
has every untilted moment, so no new integral is computed below — the work is arithmetic on the
multiplier, and that is `RMF.abs_pairTiltMultiplier_le` and
`RMF.abs_pairTiltMultiplier_sub_le`. -/

/-- **The two-fold tilted local mean.**  Main term `2 (Re a₁ + Re a₂)(Re w) - Re(w ^ 2)/2`, the
two-point form of `RMF.abs_integral_localLogAdd_tilted_sub_le`; the second term is the one the
Rademacher law has and the Steinhaus law does not, and is Harper's `-(1/2)\cos(2 t_j \log p)`. -/
theorem abs_integral_localLogAdd_tilted_pair_sub_le {a₁ a₂ : ℂ} (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1)
    (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 2) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ z, localLogAdd w z
          ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z))
        - (2 * (a₁.re + a₂.re) * w.re - (w ^ 2).re / 2)|
      ≤ 36 * ‖w‖ ^ 3 + 6 * (‖a₁‖ + ‖a₂‖) ^ 3 * ‖w‖ := by
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hA0 : (0 : ℝ) ≤ ‖a₁‖ + ‖a₂‖ := by positivity
  have hre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have hmean := abs_integral_localLogAdd_sub_le hw
  have hdiff := abs_localLogAdd_diff_sub_le hw
  have hm := abs_pairTiltMultiplier_le h₁ h₂ hA
  have hmre := abs_pairTiltMultiplier_sub_le h₁ h₂ hA
  have hmain : 2 * (a₁.re + a₂.re) * w.re - (w ^ 2).re / 2
      = 2 * (a₁.re + a₂.re) * w.re + (‖w‖ ^ 2 / 2 - w.re ^ 2) := by
    rw [norm_sq_div_two_sub_re_sq]
    ring
  rw [integral_tilted_pair_eq_add_rademacherLaw h₁ h₂ (localLogAdd w), hmain]
  set m : ℝ := pairTiltMultiplier a₁ a₂ with hmdef
  set Δ : ℝ := localLogAdd w 1 - localLogAdd w (-1) with hΔdef
  -- `mΔ - 2(Re a₁ + Re a₂)(Re w) = m(Δ - 2 Re w) + 2 (Re w)(m - (Re a₁ + Re a₂))`
  have h1 : |m * (Δ - 2 * w.re)| ≤ 24 * ‖w‖ ^ 3 := by
    rw [abs_mul]
    have hmul := mul_le_mul hm hdiff (abs_nonneg _) (by linarith : (0 : ℝ) ≤ 2 * (‖a₁‖ + ‖a₂‖))
    nlinarith [hmul, mul_nonneg (by linarith : (0 : ℝ) ≤ 24 - 48 * (‖a₁‖ + ‖a₂‖))
      (pow_nonneg hw0 3)]
  have h2 : |2 * w.re * (m - (a₁.re + a₂.re))| ≤ 6 * (‖a₁‖ + ‖a₂‖) ^ 3 * ‖w‖ := by
    rw [abs_mul, abs_mul, abs_two]
    have h := mul_le_mul hre hmre (abs_nonneg _) hw0
    nlinarith [h, abs_nonneg (m - (a₁.re + a₂.re)), abs_nonneg w.re]
  rw [abs_le] at hmean h1 h2 ⊢
  constructor <;> linarith [hmean.1, hmean.2, h1.1, h1.2, h2.1, h2.2]

/-- **The two-fold tilted local mean is `O(‖w‖(‖a₁‖ + ‖a₂‖) + ‖w‖ ^ 2)`** — the same two
constants the one-point `RMF.abs_integral_localLogAdd_tiltedMeasure_le` carries, with
`‖a₁‖ + ‖a₂‖` in place of `‖a‖`.  The `‖w‖ ^ 2` term has no Steinhaus counterpart: there the
untilted mean vanishes, and the whole mean is `O(‖w‖ ‖a‖)`. -/
theorem abs_integral_localLogAdd_tilted_pair_le {a₁ a₂ : ℂ} (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1)
    (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 2) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    |∫ z, localLogAdd w z
        ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z)|
      ≤ 4 * (‖a₁‖ + ‖a₂‖) * ‖w‖ + 8 * ‖w‖ ^ 2 := by
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hA0 : (0 : ℝ) ≤ ‖a₁‖ + ‖a₂‖ := by positivity
  have hdrift := abs_integral_localLogAdd_tilted_pair_sub_le h₁ h₂ hA hw
  have hre : |a₁.re + a₂.re| ≤ ‖a₁‖ + ‖a₂‖ :=
    (abs_add_le _ _).trans (add_le_add (Complex.abs_re_le_norm a₁) (Complex.abs_re_le_norm a₂))
  have hwre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have hsq : |(w ^ 2).re| ≤ ‖w‖ ^ 2 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_pow]
  have hmain : |2 * (a₁.re + a₂.re) * w.re - (w ^ 2).re / 2|
      ≤ 2 * (‖a₁‖ + ‖a₂‖) * ‖w‖ + ‖w‖ ^ 2 / 2 := by
    have hp : |2 * (a₁.re + a₂.re) * w.re| ≤ 2 * (‖a₁‖ + ‖a₂‖) * ‖w‖ := by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hre (by norm_num)) hwre (abs_nonneg _)
        (by positivity)
    have hq : |(w ^ 2).re / 2| ≤ ‖w‖ ^ 2 / 2 := by
      rw [abs_div, abs_two]
      linarith
    exact (abs_sub _ _).trans (by linarith)
  -- `36‖w‖³ ≤ (36/5)‖w‖²` and `6A³‖w‖ ≤ (3/2)A‖w‖`
  have herr : 36 * ‖w‖ ^ 3 + 6 * (‖a₁‖ + ‖a₂‖) ^ 3 * ‖w‖
      ≤ 36 / 5 * ‖w‖ ^ 2 + 3 / 2 * (‖a₁‖ + ‖a₂‖) * ‖w‖ := by
    have hcube : 36 * ‖w‖ ^ 3 ≤ 36 / 5 * ‖w‖ ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 5 - ‖w‖) (sq_nonneg ‖w‖)]
    have hacube : 6 * (‖a₁‖ + ‖a₂‖) ^ 3 * ‖w‖ ≤ 3 / 2 * (‖a₁‖ + ‖a₂‖) * ‖w‖ := by
      nlinarith [mul_nonneg (mul_nonneg hA0 hw0)
        (by nlinarith [hA, hA0] : (0 : ℝ) ≤ 1 / 4 - (‖a₁‖ + ‖a₂‖) ^ 2)]
    linarith
  rw [abs_le] at hdrift hmain ⊢
  constructor <;> linarith [hdrift.1, hdrift.2, hmain.1, hmain.2, sq_nonneg ‖w‖,
    mul_nonneg hA0 hw0]

/-! ### The covariance, exactly

The tilted law has atoms `1/2 ± m`, so its covariance is `(1/4 - m ^ 2)` times the product of the
two increments.  That is an **identity**, with no error term and no integrability side condition,
and it is the whole of the two-point argument's off-diagonal.  The Steinhaus route reaches the
same quantity by expanding on the circle, with `O(δ³)` errors from three separate sources
(`RMF.abs_blockMatchedCov_sub_le`). -/

/-- **The two-fold tilted covariance, in closed form.**  `Cov~ = (1 - 4m ^ 2) D_v D_w` with
`D_w = (localLogAdd w 1 - localLogAdd w (-1))/2` the half-increment. -/
theorem cov_localLogAdd_tilted_pair_eq {a₁ a₂ : ℂ} (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1) (v w : ℂ) :
    (∫ z, localLogAdd v z * localLogAdd w z
        ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z))
      - (∫ z, localLogAdd v z
          ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z))
        * (∫ z, localLogAdd w z
          ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z))
      = (1 - 4 * pairTiltMultiplier a₁ a₂ ^ 2)
          * ((localLogAdd v 1 - localLogAdd v (-1)) / 2)
          * ((localLogAdd w 1 - localLogAdd w (-1)) / 2) := by
  rw [integral_tilted_pair_eq_add_rademacherLaw h₁ h₂
      (fun z => localLogAdd v z * localLogAdd w z),
    integral_tilted_pair_eq_add_rademacherLaw h₁ h₂ (localLogAdd v),
    integral_tilted_pair_eq_add_rademacherLaw h₁ h₂ (localLogAdd w),
    integral_rademacherLaw_eq (fun z => localLogAdd v z * localLogAdd w z),
    integral_rademacherLaw_eq (localLogAdd v), integral_rademacherLaw_eq (localLogAdd w)]
  simp only [smul_eq_mul]
  ring

/-- The covariance estimate in real variables.  Extracted so that each step runs against three
hypotheses rather than the theorem's fifteen. -/
private lemma abs_cov_pair_bound {D₁ D₂ r s m nv nw A : ℝ} (hnv : 0 ≤ nv) (hnw : 0 ≤ nw)
    (hv5 : nv ≤ 1 / 5) (hw5 : nw ≤ 1 / 5) (hr : |r| ≤ nv) (hs : |s| ≤ nw)
    (hD₁ : |D₁ - r| ≤ 12 * nv ^ 3) (hD₂ : |D₂ - s| ≤ 12 * nw ^ 3) (hm : |m| ≤ 2 * A)
    (hA0 : 0 ≤ A) :
    |(1 - 4 * m ^ 2) * D₁ * D₂ - r * s|
      ≤ 4 * (nv ^ 3 + nw ^ 3) + 36 * A ^ 2 * (nv * nw) := by
  have hb₁ : |D₁| ≤ 3 / 2 * nv := by
    have h := (abs_sub_abs_le_abs_sub D₁ r).trans hD₁
    nlinarith [h, hr, mul_nonneg hnv (by nlinarith [hnv, hv5] : (0 : ℝ) ≤ 1 - 24 * nv ^ 2)]
  have hb₂ : |D₂| ≤ 3 / 2 * nw := by
    have h := (abs_sub_abs_le_abs_sub D₂ s).trans hD₂
    nlinarith [h, hs, mul_nonneg hnw (by nlinarith [hnw, hw5] : (0 : ℝ) ≤ 1 - 24 * nw ^ 2)]
  have hprod : |D₁ * D₂ - r * s| ≤ 4 * (nv ^ 3 + nw ^ 3) := by
    have t1 : |(D₁ - r) * D₂| ≤ 12 * nv ^ 3 * (3 / 2 * nw) := by
      rw [abs_mul]
      exact mul_le_mul hD₁ hb₂ (abs_nonneg _) (by positivity)
    have t2 : |r * (D₂ - s)| ≤ nv * (12 * nw ^ 3) := by
      rw [abs_mul]
      exact mul_le_mul hr hD₂ (abs_nonneg _) hnv
    have t3 : 12 * nv ^ 3 * (3 / 2 * nw) ≤ 18 / 5 * nv ^ 3 := by
      nlinarith [mul_nonneg (pow_nonneg hnv 3) (by linarith : (0 : ℝ) ≤ 1 / 5 - nw)]
    have t4 : nv * (12 * nw ^ 3) ≤ 12 / 5 * nw ^ 3 := by
      nlinarith [mul_nonneg (pow_nonneg hnw 3) (by linarith : (0 : ℝ) ≤ 1 / 5 - nv)]
    rw [show D₁ * D₂ - r * s = (D₁ - r) * D₂ + r * (D₂ - s) from by ring]
    linarith [abs_add_le ((D₁ - r) * D₂) (r * (D₂ - s)), pow_nonneg hnv 3, pow_nonneg hnw 3]
  have htilt : |4 * m ^ 2 * (D₁ * D₂)| ≤ 36 * A ^ 2 * (nv * nw) := by
    have hm2 : 4 * m ^ 2 ≤ 16 * A ^ 2 := by nlinarith [hm, abs_nonneg m, sq_abs m]
    have hDD : |D₁ * D₂| ≤ 9 / 4 * (nv * nw) := by
      rw [abs_mul]
      have := mul_le_mul hb₁ hb₂ (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 3 / 2 * nv)
      linarith
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * m ^ 2)]
    have := mul_le_mul hm2 hDD (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 16 * A ^ 2)
    linarith
  rw [show (1 - 4 * m ^ 2) * D₁ * D₂ - r * s
      = (D₁ * D₂ - r * s) - 4 * m ^ 2 * (D₁ * D₂) from by ring]
  linarith [abs_sub (D₁ * D₂ - r * s) (4 * m ^ 2 * (D₁ * D₂))]

/-- **The two-fold tilted covariance is `(Re v)(Re w)` up to third order**: the error is
`4(‖v‖³ + ‖w‖³) + 36(‖a₁‖ + ‖a₂‖)²‖v‖‖w‖`.  The Steinhaus main term is `Re(v conj w)/2`; at Harper's
points the two differ by the oscillatory `cos((t₁+t₂) log p)/2`, as the drifts do
(`RMF.rademacherDrift_prime_eq`).  The radii enter only squared, through the factor `1 - 4m²`; the
Steinhaus twin `RMF.abs_blockMatchedCov_sub_le` also carries `240‖v‖‖w‖(‖a₁‖ + ‖a₂‖)`. -/
theorem abs_cov_localLogAdd_tilted_pair_sub_le {a₁ a₂ : ℂ} (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1)
    (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 2) {v w : ℂ} (hv : ‖v‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ z, localLogAdd v z * localLogAdd w z
          ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z))
        - (∫ z, localLogAdd v z
            ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z))
          * (∫ z, localLogAdd w z
            ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z))
        - v.re * w.re|
      ≤ 4 * (‖v‖ ^ 3 + ‖w‖ ^ 3) + 36 * (‖a₁‖ + ‖a₂‖) ^ 2 * (‖v‖ * ‖w‖) := by
  have hhalf : ∀ u : ℂ, ‖u‖ ≤ 1 / 5 →
      |(localLogAdd u 1 - localLogAdd u (-1)) / 2 - u.re| ≤ 12 * ‖u‖ ^ 3 := by
    intro u hu
    have h := abs_localLogAdd_diff_sub_le hu
    rw [show (localLogAdd u 1 - localLogAdd u (-1)) / 2 - u.re
        = ((localLogAdd u 1 - localLogAdd u (-1)) - 2 * u.re) / 2 from by ring, abs_div, abs_two]
    linarith
  rw [cov_localLogAdd_tilted_pair_eq h₁ h₂ v w]
  exact abs_cov_pair_bound (norm_nonneg v) (norm_nonneg w) hv hw (Complex.abs_re_le_norm v)
    (Complex.abs_re_le_norm w) (hhalf v hv) (hhalf w hw) (abs_pairTiltMultiplier_le h₁ h₂ hA)
    (by positivity)

/-! ### The two crude bounds the Lindeberg swap charges

Neither is an expansion.  `RMF.localLogAdd` is bounded by `(11/5)‖w‖` on the circle
(`RMF.abs_localLogAdd_le_of_norm_le`), the two-fold tilted law lives there, and a bounded function
has a bounded mean — the same route, and the same two constants, as the one-fold
`RMF.integral_abs_localLogAdd_cube_tilted_le`.  The tilt radii do not appear at all: the bound is
pointwise, so it cannot see them. -/

/-- **The second moment under the two-fold tilt, crudely.**  In `mul_self` form, which is the form
`RMF.matchingVar` takes. -/
lemma integral_localLogAdd_mul_self_tilted_pair_le {a₁ a₂ w : ℂ} (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1)
    (hw : ‖w‖ ≤ 1 / 5) :
    (∫ z, localLogAdd w z * localLogAdd w z
        ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z))
      ≤ (11 / 5 : ℝ) ^ 2 * ‖w‖ ^ 2 := by
  have hprob := isProbabilityMeasure_tilted_localLogAdd_pair h₁ h₂
  set ν := rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z with hνdef
  have hcirc : ∀ᵐ z ∂ν, ‖z‖ = 1 :=
    (tilted_absolutelyContinuous rademacherLaw _) norm_eq_one_rademacherLaw
  have hpt : ∀ᵐ z ∂ν, localLogAdd w z * localLogAdd w z ≤ (11 / 5 : ℝ) ^ 2 * ‖w‖ ^ 2 := by
    filter_upwards [hcirc] with z hz
    have hb := abs_localLogAdd_le_of_norm_le hz hw
    nlinarith [abs_nonneg (localLogAdd w z), sq_abs (localLogAdd w z), norm_nonneg w]
  refine le_trans (integral_mono_ae (integrable_localLogAdd_mul_tilted_pair h₁ h₂ hw hw)
    (integrable_const _) hpt) ?_
  simp

/-- **The third absolute moment under the two-fold tilt.**  Same constant as the one-fold bound,
for the same reason: it is a pointwise estimate on the circle. -/
lemma integral_abs_localLogAdd_cube_tilted_pair_le {a₁ a₂ w : ℂ} (h₁ : ‖a₁‖ < 1) (h₂ : ‖a₂‖ < 1)
    (hw : ‖w‖ ≤ 1 / 5) :
    (∫ z, |localLogAdd w z| ^ 3
        ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z))
      ≤ (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
  have hprob := isProbabilityMeasure_tilted_localLogAdd_pair h₁ h₂
  set ν := rademacherLaw.tilted fun z => 2 * localLogAdd a₁ z + 2 * localLogAdd a₂ z with hνdef
  have hcirc : ∀ᵐ z ∂ν, ‖z‖ = 1 :=
    (tilted_absolutelyContinuous rademacherLaw _) norm_eq_one_rademacherLaw
  have hpt : ∀ᵐ z ∂ν, |localLogAdd w z| ^ 3 ≤ (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
    filter_upwards [hcirc] with z hz
    calc |localLogAdd w z| ^ 3 ≤ (11 / 5 * ‖w‖) ^ 3 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_localLogAdd_le_of_norm_le hz hw) 3
      _ = (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by ring
  refine le_trans (integral_mono_ae (integrable_abs_cube_localLogAdd_tilted_pair h₁ h₂ hw)
    (integrable_const _) hpt) ?_
  simp

/-- **A bounded observable of one prime is integrable under the two-fold tilt.**  The two-step
composite of `RMF.integrable_of_ae_bound_tilted_pair_rademacherLaw` and
`RMF.integrable_comp_tiltedMeasure₂_rademacher`, named because the comparison's six integrability
inputs are all this lemma at a different bound.  The Steinhaus twin
`RMF.integrable_comp_tiltedMeasure₂_of_bounded` carries `‖a₁‖ + ‖a₂‖ ≤ 1/5`; this one carries
nothing. -/
lemma integrable_comp_tiltedMeasure₂_of_bounded_rademacher (hX : IsRademacherPrimeValues X μ)
    (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) {g : ℂ → ℝ} (hg : Measurable g) {C : ℝ}
    (hbd : ∀ z : ℂ, ‖z‖ = 1 → |g z| ≤ C) :
    Integrable (fun ω => g (X (p : ℕ) ω))
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) :=
  integrable_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ hp
    (integrable_of_ae_bound_tilted_pair_rademacherLaw (norm_prime_cpow_neg_lt_one p.2 hs₁)
      (norm_prime_cpow_neg_lt_one p.2 hs₂) hg hbd)

end RMF
