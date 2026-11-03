/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import RMF.EulerProduct.Defs
import RMF.Main
import RMF.Reduction.Steps
import RMF.Reduction.Smoothing

/-!
# The lower-bound reduction

Harper, *Moments of random multiplicative functions, I* (arXiv:1703.06654), **Proposition 3**
(§2.3).  This is the lower-bound counterpart of `RMF.reduction_upper_unitIntegral`, and it is
**not** the reverse of it: the upper reduction is one-directional (Harper's Proposition 1 is a `≪`
bound with no two-sided version).  The lower bound has its own reduction, so this file consumes
nothing from `RMF/Reduction/Upper.lean`.

## The two bounds

In the first bound of Proposition 3 the `- C√(x/log x)` sits **outside**, subtracted from the
whole product; in the second it sits **inside** the bracket, scaled by `√(x/log x)` along with the
two Euler-product terms.

`F` is Harper's `F₋₁`, the partial Euler product over `x`-smooth numbers,
`F(s) = ∏_{p ≤ x} (1 - f(p)p^{-s})⁻¹ = randomEulerProduct f (⌊x⌋₊ + 1) s`, and
`‖·‖_r := (E|·|^r)^{1/r}`, a genuine norm only for `r ≥ 1`.

## Three features that make this not a mirror image

1. **The error is subtracted, not added**, so the bound is vacuous until the main term beats the
   constant.  The lower bound on the Euler-product moment that does so is
   `RMF.exists_le_integral_rpow_chaosShift`; `RMF.exists_le_integral_rpow_normalisedSum` combines
   the two.
2. **Two shifts, with damping**: a difference of Euler-product moments at `σ = 4V/log x` and
   `σ = 2V/log x`, the second damped by `C e^{-V}`.  Harper takes `V` a large fixed constant so
   that the second term is negligible; here that absorption is
   `RMF.reduction_lower_chaosShift_absorbed`.
3. **Off the critical line**: the integrals are at `1/2 + σ` with `σ > 0`.

## Normalisation

Dividing Harper's bounds by `√x` (passing to `normalisedSum`) and folding `(log x)⁻¹` into
`chaosShift` and `meanSquareIntegral` turns `√(x/log x)·‖J‖_q^{1/2}` into `(E[G^q])^{1/(2q)}`,
leaving the additive constant `C/√(log x)`.  The window is Harper's `[-1/2,1/2]`, not the `[0,1]`
of `chaosUnit`; the two agree in law for Steinhaus `f` (`RMF.integral_rpow_chaosShift_eq`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The two integrals -/

/-- `(1/log y) ∫_{-1/2}^{1/2} |F_y(1/2 + σ + it)|² dt`, the shifted Euler-product integral of
Harper's Proposition 3.

At `σ = 0` this is `RMF.chaosUnit` up to the integration window, which is `[-1/2,1/2]`
here and `[0,1]` there; the two agree in law for Steinhaus `f`. -/
noncomputable def chaosShift (f : Ω → ArithmeticFunction ℂ) (y σ : ℝ) (ω : Ω) : ℝ :=
  (Real.log y)⁻¹ * ∫ t in (-(1 : ℝ) / 2)..(1 / 2 : ℝ),
    ‖randomEulerProduct f (⌊y⌋₊ + 1) (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2

/-- `(1/log x) ∫_1^{√x} |∑_{m ≤ z} f(m)|² dz/z²`, the mean-square average that Proposition 3
passes through on the way to the Euler product. -/
noncomputable def meanSquareIntegral (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) : ℝ :=
  (Real.log x)⁻¹ * ∫ z in (1 : ℝ)..Real.sqrt x, ‖randomSum f z ω‖ ^ 2 / z ^ 2

omit [MeasurableSpace Ω] in
/-- `chaosShift` is the `[-1/2,1/2]` window of `RMF.lineSq` at abscissa `1/2 + δ`, which
is the vocabulary `RMF/Reduction/Periodisation.lean` speaks. -/
lemma chaosShift_eqOf {F : Ω → ArithmeticFunction ℂ} {y δ : ℝ} {ω : Ω} :
    chaosShift F y δ ω
      = (Real.log y)⁻¹ * ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ),
          lineSqOf (1 / 2 + δ) F (⌊y⌋₊ + 1) ω t := by
  rw [chaosShift, intervalIntegral.integral_of_le (by norm_num)]
  rfl

omit [MeasurableSpace Ω] in
/-- The `RMF.compMultExtension` case. -/
lemma chaosShift_eq {X : ℕ → Ω → ℂ} {y δ : ℝ} {ω : Ω} :
    chaosShift (fun ω => compMultExtension fun p => X p ω) y δ ω
      = (Real.log y)⁻¹ * ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ),
          lineSq (1 / 2 + δ) X (⌊y⌋₊ + 1) ω t :=
  chaosShift_eqOf

/-! ### Elementary steps

`RMF.rpow_sub_le_sub_rpow` is what lets a difference of integrals be split without losing more
than the `q`-th powers; both halves of the reduction use it. -/

/-- **`a^q - b^q ≤ (a-b)^q`** for `0 ≤ b ≤ a` and `q ≤ 1`.  Concavity, in the form the chain
needs: subadditivity of `t ↦ t^q` applied to `(a-b) + b = a`. -/
lemma rpow_sub_le_sub_rpow {a b q : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    a ^ q - b ^ q ≤ (a - b) ^ q := by
  have hsub : (0 : ℝ) ≤ a - b := by linarith
  have h := Real.rpow_add_le_add_rpow hsub hb hq0 hq1
  rw [sub_add_cancel] at h
  linarith

/-! ### The shifted tail integral

The object Parseval converts.  The coefficients must be the **`y`-smooth** ones: for a Steinhaus
`f` every `‖f ω n‖` is `1`, so `∑ ‖f ω n‖/n^σ` diverges for `σ ≤ 1`, whereas
`∑_{n y-smooth} n^{-σ} = ∏_{p≤y}(1-p^{-σ})⁻¹` is finite for every `σ > 0`.  That is exactly why
Harper restricts the sum to `x`-smooth `m` — harmlessly, since below `√x` every `m` is
already `x`-smooth, but essentially, once the range is extended to `∞`. -/

/-- Raising the abscissa preserves Parseval's hypothesis: `n^σ ≥ √n` for `n ≥ 1`. -/
lemma summable_coeffWeight_of_half {a : ℕ → ℂ} {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    (ha : Summable fun n : ℕ => ‖a n‖ / Real.sqrt n) :
    Summable (coeffWeight σ a) := by
  refine Summable.of_nonneg_of_le (fun n => coeffWeight_nonneg σ a n) (fun n => ?_) ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coeffWeight, Real.zero_rpow (by linarith : σ ≠ 0)]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hs0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
    have h : Real.sqrt n ≤ (n : ℝ) ^ σ := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hn1 hσ
    rw [coeffWeight]
    gcongr

/-- `∫_0^∞ ‖∑_{m ≤ z, m y-smooth} f(m)‖² dz/z^{1+2σ}`.  The integrand vanishes for `z < 1`, so this
is Harper's `∫_1^∞`; writing it over `(0,∞)` is what lets
`RMF.integral_normSq_partialSum_eq_line` apply verbatim. -/
noncomputable def smoothTailIntegral (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (σ : ℝ) (ω : Ω) :
    ℝ :=
  ∫ z in Set.Ioi (0 : ℝ), ‖smoothPartial f y z ω‖ ^ 2 / z ^ (1 + 2 * σ)

omit [MeasurableSpace Ω] in
lemma smoothTailIntegral_nonneg (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (σ : ℝ) (ω : Ω) :
    0 ≤ smoothTailIntegral f y σ ω :=
  setIntegral_nonneg measurableSet_Ioi fun _z hz =>
    div_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hz) _)

/-- **Parseval at the shifted abscissa**, with the Dirichlet series recognised as the Euler
product: almost surely

`∫_0^∞ ‖∑_{m ≤ z, y-smooth} f(m)‖² dz/z^{1+2σ} = (2π)⁻¹ ∫_ℝ ‖A_y(σ+it)/(σ+it)‖² dt`. -/
theorem smoothTailIntegral_eq_line {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (y : ℕ)
    (hdir : ∀ᵐ ω ∂μ, ∀ z : ℂ, 0 < z.re →
      dirichletSeries (smoothCoeff f y ω) z = randomEulerProduct f (y + 1) z ω)
    {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    ∀ᵐ ω ∂μ, smoothTailIntegral f y σ ω
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
          ‖randomEulerProduct f (y + 1) ((σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  filter_upwards [summable_norm_smoothCoeff_div_sqrt hf y, hdir] with ω hsum heuler
  have hσ0 : (0 : ℝ) < σ := by linarith
  have haw : Summable (coeffWeight σ (smoothCoeff f y ω)) :=
    summable_coeffWeight_of_half hσ hsum
  have hkey := integral_normSq_partialSum_eq_line σ (smoothCoeff f y ω) hσ0 haw
  rw [smoothTailIntegral]
  simp_rw [← sum_smoothCoeff f y]
  rw [hkey]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [← heuler ((σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using hσ0)]
  rfl

/-! ### Restricting, extending, damping

Three pointwise inequalities, per `ω`: restricting the weight and the summands, extending the
range to `(0,∞)` at the cost of a tail, and damping that tail by `e^{-2V}`.  Only the damping uses
the relation between the two shifts. -/

omit [MeasurableSpace Ω] in
/-- The smooth summatory function vanishes below `1`. -/
lemma smoothPartial_eq_zero {f : Ω → ArithmeticFunction ℂ} {y : ℕ} {z : ℝ} (hz : z < 1)
    (ω : Ω) : smoothPartial f y z ω = 0 := by
  rw [smoothPartial, Nat.floor_eq_zero.2 hz]
  simp

omit [MeasurableSpace Ω] in
/-- **The smoothness restriction is vacuous below `√x`.**  Every `m ≤ z ≤ √x` has all its prime
factors below `x`, so the smooth partial sum is the full one — which is why the restriction is
free below `√x`, and used essentially once the range is extended. -/
lemma smoothPartial_eq_randomSum {f : Ω → ArithmeticFunction ℂ} {x z : ℝ} (hx : 1 ≤ x)
    (hz : z ≤ Real.sqrt x) (ω : Ω) :
    smoothPartial f ⌊x⌋₊ z ω = randomSum f z ω := by
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs1 : (1 : ℝ) ≤ Real.sqrt x := by nlinarith
  have hsx : Real.sqrt x ≤ x := by nlinarith
  have hfl : ⌊z⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (le_trans hz hsx)
  rw [smoothPartial, randomSum]
  refine Finset.sum_congr (Finset.filter_true_of_mem fun m hm => ?_) (fun _ _ => rfl)
  rw [Finset.mem_Icc] at hm
  refine Nat.mem_smoothNumbers'.2 (fun p _ hpd => ?_)
  have hpm : p ≤ m := Nat.le_of_dvd (by omega) hpd
  omega

omit [MeasurableSpace Ω] in
/-- **Restricting.**  For `σ ≥ 1/2` and `1 ≤ z ≤ √x`, the shifted integrand is below the
mean-square one: the summands agree and `z^{1+2σ} ≥ z²`. -/
lemma smoothTail_integrand_le {f : Ω → ArithmeticFunction ℂ} {x z σ : ℝ} (hx : 1 ≤ x)
    (hσ : 1 / 2 ≤ σ) (hz1 : 1 ≤ z) (hzx : z ≤ Real.sqrt x) (ω : Ω) :
    ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2 / z ^ (1 + 2 * σ)
      ≤ ‖randomSum f z ω‖ ^ 2 / z ^ 2 := by
  have hz0 : (0 : ℝ) < z := by linarith
  have h2 : z ^ (2 : ℝ) = z ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast z 2]
    norm_num
  rw [smoothPartial_eq_randomSum hx hzx ω, ← h2]
  gcongr
  linarith

omit [MeasurableSpace Ω] in
/-- **Damping.**  Beyond `√x` the heavier weight is smaller than the lighter one by `e^{-2V}`:
`z^{-4V/log x} ≤ (√x)^{-4V/log x} = e^{-2V}`. -/
lemma damping_integrand_le {f : Ω → ArithmeticFunction ℂ} {x z V : ℝ} (hx : Real.exp 1 ≤ x)
    (hV : 0 ≤ V) (hz : Real.sqrt x ≤ z) (ω : Ω) :
    ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2 / z ^ (1 + 2 * (1 / 2 + 4 * V / Real.log x))
      ≤ Real.exp (-(2 * V))
        * (‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2 / z ^ (1 + 2 * (1 / 2 + 2 * V / Real.log x))) := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (1 : ℝ)]) hx
  have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hsx : (1 : ℝ) ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1.le
  have hz1 : (1 : ℝ) ≤ z := le_trans hsx hz
  have hz0 : (0 : ℝ) < z := by linarith
  -- `z^{4V/log x} ≥ (√x)^{4V/log x} = e^{2V}`
  have hsqrt : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith)]
    ring_nf
  have hkey : Real.exp (2 * V) ≤ z ^ (4 * V / Real.log x) := by
    calc Real.exp (2 * V) = Real.sqrt x ^ (4 * V / Real.log x) := by
          rw [hsqrt, ← Real.exp_mul]
          congr 1
          field_simp
          ring
      _ ≤ z ^ (4 * V / Real.log x) :=
          Real.rpow_le_rpow (by linarith) hz (by positivity)
  have hnum : (0 : ℝ) ≤ ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2 := sq_nonneg _
  have hsplit : z ^ (1 + 2 * (1 / 2 + 4 * V / Real.log x))
      = z ^ (1 + 2 * (1 / 2 + 2 * V / Real.log x)) * z ^ (4 * V / Real.log x) := by
    rw [← Real.rpow_add hz0]
    congr 1
    ring
  have hA : (0 : ℝ) < z ^ (1 + 2 * (1 / 2 + 2 * V / Real.log x)) := Real.rpow_pos_of_pos hz0 _
  have hQ : (0 : ℝ) ≤ ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2
      / z ^ (1 + 2 * (1 / 2 + 2 * V / Real.log x)) := div_nonneg hnum hA.le
  rw [hsplit, ← div_div, Real.exp_neg, inv_mul_eq_div]
  gcongr

/-! ### Extending the range, as a genuine split

`∫_0^∞ = ∫_1^b + ∫_b^∞`.  The first equality is the only place the vanishing below `1` is used,
and it is what makes the extension of the range an identity rather than an inequality. -/

/-- The shifted integrand is integrable on `(0,∞)` — `RMF.integrableOn_normSq_partialSum` at the
smooth coefficients. -/
lemma integrableOn_smoothTail {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (y : ℕ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    ∀ᵐ ω ∂μ, IntegrableOn
      (fun z => ‖smoothPartial f y z ω‖ ^ 2 / z ^ (1 + 2 * σ)) (Set.Ioi (0 : ℝ)) := by
  filter_upwards [summable_norm_smoothCoeff_div_sqrt hf y] with ω hsum
  have hσ0 : (0 : ℝ) < σ := by linarith
  have h := integrableOn_normSq_partialSum σ (smoothCoeff f y ω) hσ0
    (summable_coeffWeight_of_half hσ hsum)
  simpa only [sum_smoothCoeff] using h

omit [MeasurableSpace Ω] in
/-- Nothing below `1` contributes: the sum is empty there, and the single point `z = 1` is null. -/
lemma setIntegral_Ioc_zero_one {f : Ω → ArithmeticFunction ℂ} {y : ℕ} {σ : ℝ} {ω : Ω} :
    ∫ z in Set.Ioc (0 : ℝ) 1, ‖smoothPartial f y z ω‖ ^ 2 / z ^ (1 + 2 * σ) = 0 := by
  rw [← setIntegral_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
  rw [smoothPartial_eq_zero hz.2 ω]
  simp

omit [MeasurableSpace Ω] in
/-- **Extending the range.**  `∫_0^∞ = ∫_1^b + ∫_b^∞` for any `b ≥ 1`. -/
lemma smoothTailIntegral_split {f : Ω → ArithmeticFunction ℂ} {y : ℕ} {σ b : ℝ} {ω : Ω}
    (hb : 1 ≤ b)
    (hint : IntegrableOn (fun z => ‖smoothPartial f y z ω‖ ^ 2 / z ^ (1 + 2 * σ))
      (Set.Ioi (0 : ℝ))) :
    smoothTailIntegral f y σ ω
      = (∫ z in Set.Ioc (1 : ℝ) b, ‖smoothPartial f y z ω‖ ^ 2 / z ^ (1 + 2 * σ))
        + ∫ z in Set.Ioi b, ‖smoothPartial f y z ω‖ ^ 2 / z ^ (1 + 2 * σ) := by
  have hI1 : IntegrableOn (fun z => ‖smoothPartial f y z ω‖ ^ 2 / z ^ (1 + 2 * σ))
      (Set.Ioc (0 : ℝ) 1) := hint.mono_set fun z hz => hz.1
  have hI2 : IntegrableOn (fun z => ‖smoothPartial f y z ω‖ ^ 2 / z ^ (1 + 2 * σ))
      (Set.Ioi (1 : ℝ)) := hint.mono_set fun z hz => Set.mem_Ioi.2 (lt_trans zero_lt_one hz)
  have hI3 : IntegrableOn (fun z => ‖smoothPartial f y z ω‖ ^ 2 / z ^ (1 + 2 * σ))
      (Set.Ioc (1 : ℝ) b) := hI2.mono_set fun z hz => hz.1
  have hI4 : IntegrableOn (fun z => ‖smoothPartial f y z ω‖ ^ 2 / z ^ (1 + 2 * σ))
      (Set.Ioi b) := hI2.mono_set fun z hz => lt_of_le_of_lt hb hz
  have h1 : smoothTailIntegral f y σ ω
      = ∫ z in Set.Ioi (1 : ℝ), ‖smoothPartial f y z ω‖ ^ 2 / z ^ (1 + 2 * σ) := by
    rw [smoothTailIntegral, ← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hI1 hI2,
      setIntegral_Ioc_zero_one, zero_add]
  rw [h1, ← Set.Ioc_union_Ioi_eq_Ioi hb,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hI3 hI4]

/-! ### Restricting, extending, damping, combined

Splitting both tails at `√x`, the restriction bounds the `(1,√x]` piece of the heavier one by the
mean-square integrand, and the damping bounds its `(√x,∞)` piece by `e^{-2V}` times the whole
lighter one. -/

/-- The part of the shifted tail beyond `√x`, the piece the damping acts on.  It stays visible
rather than being folded into a difference, because `RMF.rpow_sub_le_sub_rpow` needs to know it is
below the whole tail. -/
noncomputable def farTail (f : Ω → ArithmeticFunction ℂ) (x σ : ℝ) (ω : Ω) : ℝ :=
  ∫ z in Set.Ioi (Real.sqrt x), ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2 / z ^ (1 + 2 * σ)

omit [MeasurableSpace Ω] in
lemma farTail_nonneg (f : Ω → ArithmeticFunction ℂ) (x σ : ℝ) (ω : Ω) :
    0 ≤ farTail f x σ ω :=
  setIntegral_nonneg measurableSet_Ioi fun _z hz =>
    div_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_trans (Real.sqrt_nonneg x) hz.le) _)

omit [MeasurableSpace Ω] in
/-- **The three steps at once.**  With `σ = 1/2 + 4V/log x` and `σ' = 1/2 + 2V/log x`, per `ω`:
the tail is below the whole shifted integral, it is damped by `e^{-2V}` against the lighter shift,
and the remainder is below the mean square. -/
lemma smoothTail_sub_le_meanSquare {f : Ω → ArithmeticFunction ℂ} {x V : ℝ}
    (hx : Real.exp 1 ≤ x) (hV : 0 ≤ V) {ω : Ω}
    (h4 : IntegrableOn (fun z => ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2
      / z ^ (1 + 2 * (1 / 2 + 4 * V / Real.log x))) (Set.Ioi (0 : ℝ)))
    (h2 : IntegrableOn (fun z => ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2
      / z ^ (1 + 2 * (1 / 2 + 2 * V / Real.log x))) (Set.Ioi (0 : ℝ)))
    (hhalf : IntegrableOn (fun z => ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2
      / z ^ (1 + 2 * (1 / 2 : ℝ))) (Set.Ioi (0 : ℝ))) :
    farTail f x (1 / 2 + 4 * V / Real.log x) ω
          ≤ smoothTailIntegral f ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω
        ∧ farTail f x (1 / 2 + 4 * V / Real.log x) ω
          ≤ Real.exp (-(2 * V)) * smoothTailIntegral f ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω
        ∧ smoothTailIntegral f ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω
            - farTail f x (1 / 2 + 4 * V / Real.log x) ω
          ≤ Real.log x * meanSquareIntegral f x ω := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (1 : ℝ)]) hx
  have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsx : (1 : ℝ) ≤ Real.sqrt x := by nlinarith
  have hσ : (1 : ℝ) / 2 ≤ 1 / 2 + 4 * V / Real.log x := by
    have hnn : (0 : ℝ) ≤ 4 * V / Real.log x := by positivity
    linarith
  -- the mean-square integrand is the `σ = 1/2` one on `(1, √x]`
  have hms : IntegrableOn (fun z => ‖randomSum f z ω‖ ^ 2 / z ^ 2)
      (Set.Ioc (1 : ℝ) (Real.sqrt x)) := by
    refine (hhalf.mono_set fun z hz => Set.mem_Ioi.2 (lt_trans zero_lt_one hz.1)).congr_fun
      (fun z hz => ?_) measurableSet_Ioc
    simp only
    rw [smoothPartial_eq_randomSum hx1.le hz.2 ω,
      show (1 : ℝ) + 2 * (1 / 2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  -- the restriction on the near range
  have hM1 : (∫ z in Set.Ioc (1 : ℝ) (Real.sqrt x), ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2
        / z ^ (1 + 2 * (1 / 2 + 4 * V / Real.log x)))
      ≤ ∫ z in Set.Ioc (1 : ℝ) (Real.sqrt x), ‖randomSum f z ω‖ ^ 2 / z ^ 2 :=
    setIntegral_mono_on (h4.mono_set fun z hz => Set.mem_Ioi.2 (lt_trans zero_lt_one hz.1))
      hms measurableSet_Ioc
      fun z hz => smoothTail_integrand_le hx1.le hσ hz.1.le hz.2 ω
  -- the damping on the far range
  have hM3 : (∫ z in Set.Ioi (Real.sqrt x), ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2
        / z ^ (1 + 2 * (1 / 2 + 4 * V / Real.log x)))
      ≤ Real.exp (-(2 * V)) * ∫ z in Set.Ioi (Real.sqrt x), ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2
        / z ^ (1 + 2 * (1 / 2 + 2 * V / Real.log x)) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on
      (h4.mono_set fun z hz => Set.mem_Ioi.2 (lt_of_lt_of_le zero_lt_one (le_trans hsx hz.le)))
      ((h2.mono_set fun z hz =>
        Set.mem_Ioi.2 (lt_of_lt_of_le zero_lt_one (le_trans hsx hz.le))).const_mul _)
      measurableSet_Ioi fun z hz => damping_integrand_le hx hV hz.le ω
  -- the far part of the lighter tail is nonnegative
  have hnear : (0 : ℝ) ≤ ∫ z in Set.Ioc (1 : ℝ) (Real.sqrt x),
      ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2 / z ^ (1 + 2 * (1 / 2 + 2 * V / Real.log x)) :=
    setIntegral_nonneg measurableSet_Ioc fun z hz =>
      div_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hz.1]) _)
  have hE : (0 : ℝ) < Real.exp (-(2 * V)) := Real.exp_pos _
  -- the mean-square integral, unfolded
  have hmean : Real.log x * meanSquareIntegral f x ω
      = ∫ z in Set.Ioc (1 : ℝ) (Real.sqrt x), ‖randomSum f z ω‖ ^ 2 / z ^ 2 := by
    rw [meanSquareIntegral, ← mul_assoc, mul_inv_cancel₀ hlog.ne', one_mul,
      intervalIntegral.integral_of_le hsx]
  have hnear4 : (0 : ℝ) ≤ ∫ z in Set.Ioc (1 : ℝ) (Real.sqrt x),
      ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2 / z ^ (1 + 2 * (1 / 2 + 4 * V / Real.log x)) :=
    setIntegral_nonneg measurableSet_Ioc fun z hz =>
      div_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hz.1]) _)
  rw [hmean, farTail]
  refine ⟨?_, ?_, ?_⟩
  · rw [smoothTailIntegral_split hsx h4]
    linarith
  · rw [smoothTailIntegral_split hsx h2]
    nlinarith [hM3, hnear, hE]
  · rw [smoothTailIntegral_split hsx h4]
    linarith

/-! ### The pointwise input at the `q`-th power

`RMF.rpow_sub_le_sub_rpow` needs the subtracted term below the main one, which is why the tail is
carried explicitly through the three steps. -/

omit [MeasurableSpace Ω] in
/-- **The chain, at the `q`-th power.**  `T_σ^q - e^{-2Vq} T_{σ'}^q ≤ ((log x)·meanSquare)^q`. -/
lemma rpow_smoothTail_sub_le {f : Ω → ArithmeticFunction ℂ} {x V q : ℝ}
    (hx : Real.exp 1 ≤ x) (hV : 0 ≤ V) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {ω : Ω}
    (h4 : IntegrableOn (fun z => ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2
      / z ^ (1 + 2 * (1 / 2 + 4 * V / Real.log x))) (Set.Ioi (0 : ℝ)))
    (h2 : IntegrableOn (fun z => ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2
      / z ^ (1 + 2 * (1 / 2 + 2 * V / Real.log x))) (Set.Ioi (0 : ℝ)))
    (hhalf : IntegrableOn (fun z => ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2
      / z ^ (1 + 2 * (1 / 2 : ℝ))) (Set.Ioi (0 : ℝ))) :
    smoothTailIntegral f ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω ^ q
        - Real.exp (-(2 * V * q))
            * smoothTailIntegral f ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω ^ q
      ≤ (Real.log x * meanSquareIntegral f x ω) ^ q := by
  obtain ⟨hRT, hRD, hAM⟩ := smoothTail_sub_le_meanSquare hx hV h4 h2 hhalf
  have hR0 : 0 ≤ farTail f x (1 / 2 + 4 * V / Real.log x) ω := farTail_nonneg f x _ ω
  have hA0 : (0 : ℝ) ≤ smoothTailIntegral f ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω
      - farTail f x (1 / 2 + 4 * V / Real.log x) ω := by linarith
  have hD0 : (0 : ℝ) ≤ Real.exp (-(2 * V))
      * smoothTailIntegral f ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω := le_trans hR0 hRD
  -- `A^q ≤ ((log x)·meanSquare)^q`
  have hstep1 : (smoothTailIntegral f ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω
        - farTail f x (1 / 2 + 4 * V / Real.log x) ω) ^ q
      ≤ (Real.log x * meanSquareIntegral f x ω) ^ q := Real.rpow_le_rpow hA0 hAM hq0
  -- `T^q - R^q ≤ A^q`
  have hstep2 : smoothTailIntegral f ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω ^ q
        - farTail f x (1 / 2 + 4 * V / Real.log x) ω ^ q
      ≤ (smoothTailIntegral f ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω
          - farTail f x (1 / 2 + 4 * V / Real.log x) ω) ^ q :=
    rpow_sub_le_sub_rpow hR0 hRT hq0 hq1
  -- `R^q ≤ e^{-2Vq} T'^q`
  have hstep3 : farTail f x (1 / 2 + 4 * V / Real.log x) ω ^ q
      ≤ Real.exp (-(2 * V * q))
        * smoothTailIntegral f ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω ^ q := by
    refine le_trans (Real.rpow_le_rpow hR0 hRD hq0) (le_of_eq ?_)
    rw [Real.mul_rpow (Real.exp_pos _).le (smoothTailIntegral_nonneg f ⌊x⌋₊ _ ω),
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    ring_nf
  linarith

/-! ### Measurability

`meanSquareIntegral` is a parameter integral, so `ω ↦ meanSquareIntegral f x ω` is measurable only
once the integrand is *jointly* measurable in `(ω, z)`.  The index set of the sum moves with `z`,
which is why this goes through `measurable_from_prod_countable_left` on `ℕ` rather than the
`measurable_from_top` trick used where the coefficients are fixed. -/

/-- Hence the mean-square integral is measurable. -/
lemma measurable_meanSquareIntegral {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) {x : ℝ} (hx : 1 ≤ x) :
    Measurable fun ω => meanSquareIntegral f x ω := by
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsx : (1 : ℝ) ≤ Real.sqrt x := by nlinarith
  have hjoint : Measurable fun p : Ω × ℝ => ‖randomSum f p.2 p.1‖ ^ 2 / p.2 ^ 2 :=
    (((measurable_randomSum_uncurry hf).norm).pow_const 2).div (measurable_snd.pow_const 2)
  have hset : StronglyMeasurable fun ω =>
      ∫ z in Set.Ioc (1 : ℝ) (Real.sqrt x), ‖randomSum f z ω‖ ^ 2 / z ^ 2 :=
    MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Ioc (1 : ℝ) (Real.sqrt x))) hjoint.stronglyMeasurable
  have heq : (fun ω => ∫ z in (1 : ℝ)..Real.sqrt x, ‖randomSum f z ω‖ ^ 2 / z ^ 2)
      = fun ω => ∫ z in Set.Ioc (1 : ℝ) (Real.sqrt x), ‖randomSum f z ω‖ ^ 2 / z ^ 2 :=
    funext fun ω => intervalIntegral.integral_of_le hsx
  unfold meanSquareIntegral
  refine Measurable.const_mul ?_ _
  rw [heq]
  exact hset.measurable

/-! ### Bounds and integrability

Everything in sight is bounded, uniformly in `ω` on the set where the prime values are unimodular:
the shifted tail by `RMF.integral_lineDivSq_le`, and the mean square because it is the near part
of the `σ = 1/2` tail.  Boundedness plus measurability is what makes the `q`-th powers integrable,
which is what `integral_mono` needs at the end. -/

omit [MeasurableSpace Ω] in
/-- **The mean square is the near part of the `σ = 1/2` tail.** -/
lemma meanSquare_le_smoothTail {f : Ω → ArithmeticFunction ℂ} {x : ℝ} (hx : Real.exp 1 ≤ x)
    {ω : Ω}
    (hhalf : IntegrableOn (fun z => ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2
      / z ^ (1 + 2 * (1 / 2 : ℝ))) (Set.Ioi (0 : ℝ))) :
    Real.log x * meanSquareIntegral f x ω ≤ smoothTailIntegral f ⌊x⌋₊ (1 / 2) ω := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (1 : ℝ)]) hx
  have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsx : (1 : ℝ) ≤ Real.sqrt x := by nlinarith
  have hmean : Real.log x * meanSquareIntegral f x ω
      = ∫ z in Set.Ioc (1 : ℝ) (Real.sqrt x), ‖randomSum f z ω‖ ^ 2 / z ^ 2 := by
    rw [meanSquareIntegral, ← mul_assoc, mul_inv_cancel₀ hlog.ne', one_mul,
      intervalIntegral.integral_of_le hsx]
  have hcongr : (∫ z in Set.Ioc (1 : ℝ) (Real.sqrt x), ‖randomSum f z ω‖ ^ 2 / z ^ 2)
      = ∫ z in Set.Ioc (1 : ℝ) (Real.sqrt x),
          ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2 / z ^ (1 + 2 * (1 / 2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun z hz => ?_
    rw [smoothPartial_eq_randomSum hx1.le hz.2 ω,
      show (1 : ℝ) + 2 * (1 / 2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hfar : (0 : ℝ) ≤ ∫ z in Set.Ioi (Real.sqrt x),
      ‖smoothPartial f ⌊x⌋₊ z ω‖ ^ 2 / z ^ (1 + 2 * (1 / 2 : ℝ)) :=
    setIntegral_nonneg measurableSet_Ioi fun _z hz =>
      div_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_trans hs0 hz.le) _)
  rw [hmean, hcongr, smoothTailIntegral_split hsx hhalf]
  linarith

/-- **The shifted tail is bounded**, by the periodisation bound on the line integral. -/
lemma smoothTailIntegral_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    ∀ᵐ ω ∂μ, smoothTailIntegral (fun ω => compMultExtension fun p => X p ω) y σ ω
      ≤ (2 * Real.pi)⁻¹ * (8 * eulerBound (y + 1) ^ 2 * ∑' n : ℤ, shiftWeight 1 n) := by
  haveI := hX.isProbabilityMeasure
  filter_upwards [smoothTailIntegral_eq_line (IsSteinhausRMF.isBoundedRMF hX.isSteinhausRMF) y
      (dirichletSeries_smoothCoeff_eq hX.isSteinhausRMF y) hσ,
    ae_forall_norm_le_one hX norm_le_one_steinhausLaw (y + 1)] with ω heq hω
  rw [heq]
  exact mul_le_mul_of_nonneg_left (integral_lineDivSq_le σ hσ hω) (by positivity)

/-- **The `q`-th power of the shifted tail is integrable.** -/
lemma integrable_smoothTail_rpow {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {σ q : ℝ} (hσ : 1 / 2 ≤ σ) (hq : 0 ≤ q) :
    Integrable
      (fun ω => smoothTailIntegral (fun ω => compMultExtension fun p => X p ω) y σ ω ^ q) μ := by
  haveI := hX.isProbabilityMeasure
  have hmeas : AEStronglyMeasurable
      (fun ω => smoothTailIntegral (fun ω => compMultExtension fun p => X p ω) y σ ω ^ q) μ := by
    have h1 := (measurable_lineFunctional σ (y + 1)).comp
      (measurable_pi_lambda _ fun p : Nat.Primes => hX.measurable (p : ℕ) p.2)
    have hmap : Measurable fun ω =>
        ((2 * Real.pi)⁻¹ * lineFunctional σ (y + 1)
          (fun p : Nat.Primes => X (p : ℕ) ω)) ^ q := by fun_prop
    refine hmap.aestronglyMeasurable.congr ?_
    filter_upwards [smoothTailIntegral_eq_line (IsSteinhausRMF.isBoundedRMF hX.isSteinhausRMF) y
      (dirichletSeries_smoothCoeff_eq hX.isSteinhausRMF y) hσ,
      ae_forall_norm_le_one hX norm_le_one_steinhausLaw (y + 1)] with ω heq hω
    rw [heq, lineFunctional_eq σ hσ hω]
    rfl
  set B : ℝ := (2 * Real.pi)⁻¹ * (8 * eulerBound (y + 1) ^ 2 * ∑' n : ℤ, shiftWeight 1 n)
    with hBdef
  refine (memLp_top_of_bound hmeas (B ^ q) ?_).integrable le_top
  filter_upwards [smoothTailIntegral_le hX y hσ] with ω hb
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (smoothTailIntegral_nonneg _ _ _ _) q)]
  exact Real.rpow_le_rpow (smoothTailIntegral_nonneg _ _ _ _) hb hq

omit [MeasurableSpace Ω] in
/-- Harper's window is the unit window of a family rotated by a *half*-integer, which
`RMF.window_eq_unitFunctional` allows since its shift is real. -/
lemma chaosShift_window_eq {X : ℕ → Ω → ℂ} {N : ℕ} {δ : ℝ} {ω : Ω} (hδ : 0 ≤ δ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    (∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ), lineSq (1 / 2 + δ) X N ω t)
      = unitFunctional (1 / 2 + δ) N
          (fun p => shiftConst (-(1 : ℝ) / 2) (p : ℕ) * X (p : ℕ) ω) := by
  have h := window_eq_unitFunctional (1 / 2 + δ) (by linarith) (-(1 : ℝ) / 2) hω
  rw [show (-(1 : ℝ) / 2 + 1) = (1 / 2 : ℝ) by norm_num] at h
  exact h

omit [MeasurableSpace Ω] in
/-- The same window, bounded. -/
lemma chaosShift_window_le {X : ℕ → Ω → ℂ} {N : ℕ} {δ : ℝ} {ω : Ω} (hδ : 0 ≤ δ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    (∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ), lineSq (1 / 2 + δ) X N ω t)
      ≤ eulerBound N ^ 2 := by
  have h := window_le (1 / 2 + δ) (by linarith) hω (-(1 : ℝ) / 2)
  rw [show (-(1 : ℝ) / 2 + 1) = (1 / 2 : ℝ) by norm_num] at h
  exact h

omit [MeasurableSpace Ω] in
lemma chaosShift_nonnegOf {F : Ω → ArithmeticFunction ℂ} {y δ : ℝ}
    (hy : 0 ≤ (Real.log y)⁻¹) (ω : Ω) :
    0 ≤ chaosShift F y δ ω := by
  rw [chaosShift_eqOf]
  exact mul_nonneg hy (integral_lineSqOf_nonneg _ _ _)

omit [MeasurableSpace Ω] in
/-- The `RMF.compMultExtension` case. -/
lemma chaosShift_nonneg {X : ℕ → Ω → ℂ} {y δ : ℝ} (hy : 0 ≤ (Real.log y)⁻¹) (ω : Ω) :
    0 ≤ chaosShift (fun ω => compMultExtension fun p => X p ω) y δ ω :=
  chaosShift_nonnegOf hy ω

/-- **The `q`-th power of the shifted Euler-product integral is integrable.** -/
lemma integrable_chaosShift_rpow {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {y δ q : ℝ} (hy : 0 ≤ (Real.log y)⁻¹) (hδ : 0 ≤ δ)
    (hq : 0 ≤ q) :
    Integrable
      (fun ω => chaosShift (fun ω => compMultExtension fun p => X p ω) y δ ω ^ q) μ := by
  haveI := hX.isProbabilityMeasure
  have hae := ae_forall_norm_le_one hX norm_le_one_steinhausLaw (⌊y⌋₊ + 1)
  have hmeas : AEStronglyMeasurable
      (fun ω => chaosShift (fun ω => compMultExtension fun p => X p ω) y δ ω ^ q) μ := by
    have h1 := (measurable_unitFunctional (1 / 2 + δ) (⌊y⌋₊ + 1)).comp
      (measurable_pi_lambda _ fun p : Nat.Primes =>
        (hX.measurable (p : ℕ) p.2).const_mul (shiftConst (-(1 : ℝ) / 2) (p : ℕ)))
    have hmap : Measurable fun ω =>
        ((Real.log y)⁻¹ * unitFunctional (1 / 2 + δ) (⌊y⌋₊ + 1)
          (fun p : Nat.Primes => shiftConst (-(1 : ℝ) / 2) (p : ℕ) * X (p : ℕ) ω)) ^ q := by
      fun_prop
    refine hmap.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with ω hω
    rw [chaosShift_eq, chaosShift_window_eq hδ hω]
  refine (memLp_top_of_bound hmeas
    (((Real.log y)⁻¹ * eulerBound (⌊y⌋₊ + 1) ^ 2) ^ q) ?_).integrable le_top
  filter_upwards [hae] with ω hω
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (chaosShift_nonneg hy ω) q)]
  refine Real.rpow_le_rpow (chaosShift_nonneg hy ω) ?_ hq
  rw [chaosShift_eq]
  exact mul_le_mul_of_nonneg_left (chaosShift_window_le hδ hω) hy

/-- **The `q`-th power of the mean-square integral is integrable.**  It is bounded because it is
the near part of the `σ = 1/2` tail, which `RMF.smoothTailIntegral_le` bounds. -/
lemma integrable_meanSquare_rpow {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {x q : ℝ} (hx : Real.exp 1 ≤ x) (hq : 0 ≤ q) :
    Integrable
      (fun ω => meanSquareIntegral (fun ω => compMultExtension fun p => X p ω) x ω ^ q) μ := by
  haveI := hX.isProbabilityMeasure
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (1 : ℝ)]) hx
  have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsx : (1 : ℝ) ≤ Real.sqrt x := by nlinarith
  set B : ℝ := (2 * Real.pi)⁻¹ * (8 * eulerBound (⌊x⌋₊ + 1) ^ 2 * ∑' n : ℤ, shiftWeight 1 n)
    with hBdef
  have hnn : ∀ ω, 0 ≤ meanSquareIntegral (fun ω => compMultExtension fun p => X p ω) x ω := by
    intro ω
    refine mul_nonneg (by positivity) ?_
    rw [intervalIntegral.integral_of_le hsx]
    exact setIntegral_nonneg measurableSet_Ioc fun _z hz =>
      div_nonneg (sq_nonneg _) (by positivity)
  refine (memLp_top_of_bound
    ((measurable_meanSquareIntegral (IsSteinhausRMF.isBoundedRMF hX.isSteinhausRMF)
      hx1.le).pow_const q).aestronglyMeasurable
    (((Real.log x)⁻¹ * B) ^ q) ?_).integrable le_top
  filter_upwards [integrableOn_smoothTail (IsSteinhausRMF.isBoundedRMF hX.isSteinhausRMF)
      ⌊x⌋₊ (le_refl (1 / 2 : ℝ)),
    smoothTailIntegral_le hX ⌊x⌋₊ (le_refl (1 / 2 : ℝ))] with ω hint hb
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hnn ω) q)]
  refine Real.rpow_le_rpow (hnn ω) ?_ hq
  have hkey := meanSquare_le_smoothTail (f := fun ω => compMultExtension fun p => X p ω) hx hint
  rw [le_inv_mul_iff₀ hlog]
  linarith

/-! ### The two sides of the shifted tail

The lower side keeps only `|t| ≤ 1/2`.  The upper side is the periodisation bound,
followed by the identification of Harper's `[-1/2,1/2]` window with the unit window *in law*;
that identification is an equality of expectations, not a pointwise one, which is why it can only
be applied after the `ω`-integral has been formed. -/

/-- **The lower side.**  `T_σ ≥ (2π)⁻¹(4/5)·log x·chaosShift`. -/
lemma smoothTail_ge_chaosShift {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {x δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (hlog : 0 < Real.log x) :
    ∀ᵐ ω ∂μ, (2 * Real.pi)⁻¹ * (4 / 5) * (Real.log x
        * chaosShift (fun ω => compMultExtension fun p => X p ω) x δ ω)
      ≤ smoothTailIntegral (fun ω => compMultExtension fun p => X p ω) ⌊x⌋₊ (1 / 2 + δ) ω := by
  haveI := hX.isProbabilityMeasure
  filter_upwards [smoothTailIntegral_eq_line (IsSteinhausRMF.isBoundedRMF hX.isSteinhausRMF) ⌊x⌋₊
      (dirichletSeries_smoothCoeff_eq hX.isSteinhausRMF ⌊x⌋₊) (by linarith : 1 / 2 ≤ 1 / 2 + δ),
    ae_forall_norm_le_one hX norm_le_one_steinhausLaw (⌊x⌋₊ + 1)] with ω heq hω
  have hw := integral_lineDivSq_ge (1 / 2 + δ) (by linarith) (by linarith) hω
    (X := X) (N := ⌊x⌋₊ + 1) (ω := ω)
  rw [heq, chaosShift_eq]
  have hcancel : (2 * Real.pi)⁻¹ * (4 / 5) * (Real.log x * ((Real.log x)⁻¹
        * ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ), lineSq (1 / 2 + δ) X (⌊x⌋₊ + 1) ω t))
      = (2 * Real.pi)⁻¹ * ((4 / 5)
          * ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ),
              lineSq (1 / 2 + δ) X (⌊x⌋₊ + 1) ω t) := by
    field_simp
  rw [hcancel]
  exact mul_le_mul_of_nonneg_left hw (by positivity)

/-- **The upper side.**  Periodisation, then the half-integer rotation. -/
lemma integral_rpow_smoothTail_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {x δ q : ℝ} (hδ0 : 0 ≤ δ) (hq0 : 1 / 2 < q)
    (hq1 : q ≤ 1) (hlog : 0 < Real.log x) :
    (∫ ω, smoothTailIntegral (fun ω => compMultExtension fun p => X p ω) ⌊x⌋₊
        (1 / 2 + δ) ω ^ q ∂μ)
      ≤ 8 * (∑' n : ℤ, shiftWeight q n) * ((2 * Real.pi)⁻¹ * Real.log x) ^ q
        * ∫ ω, chaosShift (fun ω => compMultExtension fun p => X p ω) x δ ω ^ q ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hσ : (1 : ℝ) / 2 ≤ 1 / 2 + δ := by linarith
  have hc : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  have hwnn : (0 : ℝ) ≤ 8 * ∑' n : ℤ, shiftWeight q n := by
    have h0 : (0 : ℝ) ≤ ∑' n : ℤ, shiftWeight q n :=
      tsum_nonneg fun n => shiftWeight_nonneg q n
    linarith
  -- the tail *is* the line integral
  have hL : (∫ ω, smoothTailIntegral (fun ω => compMultExtension fun p => X p ω) ⌊x⌋₊
        (1 / 2 + δ) ω ^ q ∂μ)
      = ∫ ω, ((2 * Real.pi)⁻¹
          * ∫ t : ℝ, lineDivSq (1 / 2 + δ) X (⌊x⌋₊ + 1) ω t) ^ q ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [smoothTailIntegral_eq_line (IsSteinhausRMF.isBoundedRMF hX.isSteinhausRMF) ⌊x⌋₊
      (dirichletSeries_smoothCoeff_eq hX.isSteinhausRMF ⌊x⌋₊) hσ] with ω heq
    rw [heq]
    rfl
  -- pull the constant out of the unit-window moment
  have hstep2 : (∫ ω, ((2 * Real.pi)⁻¹
        * ∫ h in Set.Ioc (0 : ℝ) 1, lineSq (1 / 2 + δ) X (⌊x⌋₊ + 1) ω h) ^ q ∂μ)
      = ((2 * Real.pi)⁻¹) ^ q
        * ∫ ω, (∫ h in Set.Ioc (0 : ℝ) 1, lineSq (1 / 2 + δ) X (⌊x⌋₊ + 1) ω h) ^ q ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      Real.mul_rpow hc (integral_lineSq_nonneg _ _ _))
  -- the unit window and Harper's window have the same moment
  have hW := integral_rpow_window_eq (1 / 2 + δ) hσ hX (⌊x⌋₊ + 1) (-(1 : ℝ) / 2) q
  rw [show (-(1 : ℝ) / 2 + 1) = (1 / 2 : ℝ) by norm_num] at hW
  have hstep3 : (∫ ω, (∫ h in Set.Ioc (0 : ℝ) 1, lineSq (1 / 2 + δ) X (⌊x⌋₊ + 1) ω h) ^ q ∂μ)
      = ∫ ω, (∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ),
          lineSq (1 / 2 + δ) X (⌊x⌋₊ + 1) ω t) ^ q ∂μ := by
    simp only [lineSq]
    exact hW.symm
  -- Harper's window is `log x` times `chaosShift`
  have hstep4 : (∫ ω, (∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ),
        lineSq (1 / 2 + δ) X (⌊x⌋₊ + 1) ω t) ^ q ∂μ)
      = (Real.log x) ^ q
        * ∫ ω, chaosShift (fun ω => compMultExtension fun p => X p ω) x δ ω ^ q ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [chaosShift_eq,
      Real.mul_rpow (by positivity) (integral_lineSq_nonneg _ _ _), ← mul_assoc,
      ← Real.mul_rpow hlog.le (by positivity), mul_inv_cancel₀ hlog.ne', Real.one_rpow, one_mul]
  have hP := integral_rpow_line_le (1 / 2 + δ) hσ hX (⌊x⌋₊ + 1) hc hq0 hq1
  rw [hL]
  refine le_trans hP ?_
  rw [hstep2, hstep3, hstep4, Real.mul_rpow hc hlog.le]
  exact le_of_eq (by ring)

/-! ### The second bound, assembled -/

omit [MeasurableSpace Ω] in
lemma meanSquareIntegral_nonneg {f : Ω → ArithmeticFunction ℂ} {x : ℝ} (hx : 1 ≤ x) (ω : Ω) :
    0 ≤ meanSquareIntegral f x ω := by
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsx : (1 : ℝ) ≤ Real.sqrt x := by nlinarith
  refine mul_nonneg (inv_nonneg.2 (Real.log_nonneg hx)) ?_
  rw [intervalIntegral.integral_of_le hsx]
  exact setIntegral_nonneg measurableSet_Ioc fun _z hz =>
    div_nonneg (sq_nonneg _) (by positivity)

/-- **The lower constant of `RMF.meanSquare_ge_chaosShift`**, `(2π)^{-1}·4/5`: the `4/5` is what
survives of the window after the shift, and `(2π)^{-1}` is Parseval's. -/
noncomputable def meanSquareChaosLower : ℝ := (2 * Real.pi)⁻¹ * (4 / 5)

/-- **The upper constant of `RMF.meanSquare_ge_chaosShift`**, `8∑_{n∈ℤ}w_{2/3}(n)`: eight times
the mass of the shift weight at `q = 2/3`, the smallest exponent the bound is stated for. -/
noncomputable def meanSquareChaosUpper : ℝ := 8 * ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n

/-- **`RMF.meanSquare_ge_chaosShift` with its two constants named**, `RMF.meanSquareChaosLower`
and `RMF.meanSquareChaosUpper`, both closed forms: nothing below this step is existential. -/
theorem meanSquare_ge_chaosShift_named :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ x q V : ℝ, Real.exp 1 ≤ x → 2 / 3 ≤ q → q ≤ 1 → 0 ≤ V →
        4 * V / Real.log x ≤ 1 / 2 →
        meanSquareChaosLower * (∫ ω, chaosShift f x (4 * V / Real.log x) ω ^ q ∂μ)
            - meanSquareChaosUpper * Real.exp (-(2 * V * q))
                * ∫ ω, chaosShift f x (2 * V / Real.log x) ω ^ q ∂μ
          ≤ ∫ ω, meanSquareIntegral f x ω ^ q ∂μ := by
  rw [meanSquareChaosLower, meanSquareChaosUpper]
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hbase : (0 : ℝ) < (2 * Real.pi)⁻¹ * (4 / 5) := by positivity
  have hinv1 : (2 * Real.pi)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right; linarith
  have hbase1 : (2 * Real.pi)⁻¹ * (4 / 5) ≤ 1 := by nlinarith [hbase.le]
  have hw23 : (0 : ℝ) < 8 * ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n := by
    have h0 : (0 : ℝ) < ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n :=
      (summable_shiftWeight (by norm_num)).tsum_pos
        (fun n => shiftWeight_nonneg _ n) 0 (shiftWeight_pos _ 0)
    linarith
  intro f μ hf x q V hx hq23 hq1 hV hV1
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI := hX.isProbabilityMeasure
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (1 : ℝ)]) hx
  have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hq0 : (0 : ℝ) < q := by linarith
  have hδ0 : (0 : ℝ) ≤ 4 * V / Real.log x := by positivity
  have hδ'0 : (0 : ℝ) ≤ 2 * V / Real.log x := by positivity
  have hδ'1 : 2 * V / Real.log x ≤ 1 / 2 := by
    have heq : 2 * V / Real.log x = 1 / 2 * (4 * V / Real.log x) := by ring
    rw [heq]; nlinarith
  set F : Ω → ArithmeticFunction ℂ := fun ω => compMultExtension fun p => X p ω with hFdef
  set L4 : ℝ := Real.log x ^ q with hL4def
  set P : ℝ := ∫ ω, chaosShift F x (4 * V / Real.log x) ω ^ q ∂μ with hPdef
  set P' : ℝ := ∫ ω, chaosShift F x (2 * V / Real.log x) ω ^ q ∂μ with hP'def
  set M : ℝ := ∫ ω, meanSquareIntegral F x ω ^ q ∂μ with hMdef
  have hL40 : (0 : ℝ) < L4 := Real.rpow_pos_of_pos hlog q
  have hP0 : (0 : ℝ) ≤ P :=
    integral_nonneg fun ω => Real.rpow_nonneg
      (chaosShift_nonneg (inv_nonneg.2 hlog.le) ω) q
  have hP'0 : (0 : ℝ) ≤ P' :=
    integral_nonneg fun ω => Real.rpow_nonneg
      (chaosShift_nonneg (inv_nonneg.2 hlog.le) ω) q
  -- integrability
  have hIT4 : Integrable
      (fun ω => smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω ^ q) μ :=
    integrable_smoothTail_rpow hX ⌊x⌋₊ (by linarith) hq0.le
  have hIT2 : Integrable
      (fun ω => smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω ^ q) μ :=
    integrable_smoothTail_rpow hX ⌊x⌋₊ (by linarith) hq0.le
  have hIM : Integrable (fun ω => meanSquareIntegral F x ω ^ q) μ :=
    integrable_meanSquare_rpow hX hx hq0.le
  -- the pointwise chain, integrated
  have hchain : (∫ ω, smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω ^ q ∂μ)
        - Real.exp (-(2 * V * q))
            * ∫ ω, smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω ^ q ∂μ
      ≤ L4 * M := by
    have hRHS : (∫ ω, (Real.log x * meanSquareIntegral F x ω) ^ q ∂μ) = L4 * M := by
      rw [hL4def, hMdef, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        Real.mul_rpow hlog.le (meanSquareIntegral_nonneg hx1.le ω))
    have hIR : Integrable (fun ω => (Real.log x * meanSquareIntegral F x ω) ^ q) μ := by
      refine (hIM.const_mul (Real.log x ^ q)).congr ?_
      exact Filter.Eventually.of_forall fun ω =>
        (Real.mul_rpow hlog.le (meanSquareIntegral_nonneg hx1.le ω)).symm
    have hmono : (∫ ω, (smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω ^ q
          - Real.exp (-(2 * V * q))
              * smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω ^ q) ∂μ)
        ≤ ∫ ω, (Real.log x * meanSquareIntegral F x ω) ^ q ∂μ := by
      refine integral_mono_ae (hIT4.sub (hIT2.const_mul _)) hIR ?_
      filter_upwards [integrableOn_smoothTail (IsSteinhausRMF.isBoundedRMF hX.isSteinhausRMF) ⌊x⌋₊
          (show (1 : ℝ) / 2 ≤ 1 / 2 + 4 * V / Real.log x by linarith),
        integrableOn_smoothTail (IsSteinhausRMF.isBoundedRMF hX.isSteinhausRMF) ⌊x⌋₊
          (show (1 : ℝ) / 2 ≤ 1 / 2 + 2 * V / Real.log x by linarith),
        integrableOn_smoothTail (IsSteinhausRMF.isBoundedRMF hX.isSteinhausRMF) ⌊x⌋₊
          (le_refl (1 / 2 : ℝ))]
        with ω i4 i2 ih
      exact rpow_smoothTail_sub_le hx hV hq0.le hq1 i4 i2 ih
    rw [integral_sub hIT4 (hIT2.const_mul _), integral_const_mul, hRHS] at hmono
    exact hmono
  -- the lower side
  have hi : ((2 * Real.pi)⁻¹ * (4 / 5)) ^ q * (L4 * P)
      ≤ ∫ ω, smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω ^ q ∂μ := by
    have hexp : ((2 * Real.pi)⁻¹ * (4 / 5)) ^ q * (L4 * P)
        = ∫ ω, ((2 * Real.pi)⁻¹ * (4 / 5)
            * (Real.log x * chaosShift F x (4 * V / Real.log x) ω)) ^ q ∂μ := by
      rw [hL4def, hPdef, ← integral_const_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only
      rw [Real.mul_rpow hbase.le
          (mul_nonneg hlog.le (chaosShift_nonneg (inv_nonneg.2 hlog.le) ω)),
        Real.mul_rpow hlog.le (chaosShift_nonneg (inv_nonneg.2 hlog.le) ω)]
    rw [hexp]
    refine integral_mono_ae ?_ hIT4 ?_
    · exact ((integrable_chaosShift_rpow hX (inv_nonneg.2 hlog.le) hδ0 hq0.le).const_mul
        (((2 * Real.pi)⁻¹ * (4 / 5)) ^ q * Real.log x ^ q)).congr
        (Filter.Eventually.of_forall fun ω => by
          simp only
          rw [Real.mul_rpow hbase.le
              (mul_nonneg hlog.le (chaosShift_nonneg (inv_nonneg.2 hlog.le) ω)),
            Real.mul_rpow hlog.le (chaosShift_nonneg (inv_nonneg.2 hlog.le) ω)]
          ring)
    · filter_upwards [smoothTail_ge_chaosShift hX hδ0 hV1 hlog] with ω hb
      exact Real.rpow_le_rpow
        (mul_nonneg hbase.le (mul_nonneg hlog.le
          (chaosShift_nonneg (inv_nonneg.2 hlog.le) ω))) hb hq0.le
  -- the upper side
  have hii : (∫ ω, smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω ^ q ∂μ)
      ≤ 8 * (∑' n : ℤ, shiftWeight q n) * ((2 * Real.pi)⁻¹) ^ q * (L4 * P') := by
    have h := integral_rpow_smoothTail_le hX hδ'0 (by linarith) hq1 hlog
    rw [Real.mul_rpow (by positivity) hlog.le] at h
    calc (∫ ω, smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω ^ q ∂μ)
        ≤ 8 * (∑' n : ℤ, shiftWeight q n) * (((2 * Real.pi)⁻¹) ^ q * Real.log x ^ q) * P' := h
      _ = 8 * (∑' n : ℤ, shiftWeight q n) * ((2 * Real.pi)⁻¹) ^ q * (L4 * P') := by
          rw [hL4def]; ring
  -- the constants
  have hcq : (2 * Real.pi)⁻¹ * (4 / 5) ≤ ((2 * Real.pi)⁻¹ * (4 / 5)) ^ q := by
    have h := Real.rpow_le_rpow_of_exponent_ge hbase hbase1 hq1
    rwa [Real.rpow_one] at h
  have hCq : 8 * (∑' n : ℤ, shiftWeight q n) * ((2 * Real.pi)⁻¹) ^ q
      ≤ 8 * ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n := by
    have h1 : (∑' n : ℤ, shiftWeight q n) ≤ ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n :=
      tsum_shiftWeight_le (by norm_num) hq23
    have h2 : ((2 * Real.pi)⁻¹) ^ q ≤ 1 := Real.rpow_le_one (by positivity) hinv1 hq0.le
    have h3 : (0 : ℝ) ≤ ∑' n : ℤ, shiftWeight q n :=
      tsum_nonneg fun n => shiftWeight_nonneg q n
    have h4 : (0 : ℝ) ≤ ((2 * Real.pi)⁻¹) ^ q := Real.rpow_nonneg (by positivity) q
    nlinarith
  -- combine, then divide by `L4`
  have hE : (0 : ℝ) < Real.exp (-(2 * V * q)) := Real.exp_pos _
  have hfinal : L4 * ((2 * Real.pi)⁻¹ * (4 / 5) * P
      - (8 * ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n) * Real.exp (-(2 * V * q)) * P')
      ≤ L4 * M := by
    refine le_trans ?_ hchain
    have hlow : L4 * ((2 * Real.pi)⁻¹ * (4 / 5) * P)
        ≤ ∫ ω, smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω ^ q ∂μ := by
      refine le_trans ?_ hi
      have : L4 * ((2 * Real.pi)⁻¹ * (4 / 5) * P)
          ≤ L4 * (((2 * Real.pi)⁻¹ * (4 / 5)) ^ q * P) := by
        refine mul_le_mul_of_nonneg_left ?_ hL40.le
        exact mul_le_mul_of_nonneg_right hcq hP0
      nlinarith [this]
    have hup : Real.exp (-(2 * V * q))
        * ∫ ω, smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω ^ q ∂μ
        ≤ L4 * ((8 * ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n) * Real.exp (-(2 * V * q)) * P') := by
      have h := mul_le_mul_of_nonneg_left hii hE.le
      have h2 : Real.exp (-(2 * V * q))
          * (8 * (∑' n : ℤ, shiftWeight q n) * ((2 * Real.pi)⁻¹) ^ q * (L4 * P'))
          ≤ L4 * ((8 * ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n)
              * Real.exp (-(2 * V * q)) * P') := by
        have hLP : (0 : ℝ) ≤ L4 * P' := mul_nonneg hL40.le hP'0
        nlinarith [mul_le_mul_of_nonneg_right hCq (mul_nonneg hE.le hLP)]
      linarith
    linarith
  have := le_of_mul_le_mul_left hfinal hL40
  linarith

/-- **Proposition 3's second bound, reduced to the first.**  For `x ≥ e`, `q ∈ [2/3,1]`, `V ≥ 0`
and `4V/log x ≤ 1/2`, `c·E[G_{4V}^q] - C e^{-2Vq}·E[G_{2V}^q] ≤ E[meanSquareIntegral^q]`, where
`G_{kV} = chaosShift f x (kV/log x)`, with `c`, `C` independent of `f`, `μ`, `x`, `q`, `V`.
Composed with `RMF.reduction_lower_meanSquare` it gives `RMF.reduction_lower_chaosShift`. -/
theorem meanSquare_ge_chaosShift :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ x q V : ℝ, Real.exp 1 ≤ x → 2 / 3 ≤ q → q ≤ 1 → 0 ≤ V →
          4 * V / Real.log x ≤ 1 / 2 →
          c * (∫ ω, chaosShift f x (4 * V / Real.log x) ω ^ q ∂μ)
              - C * Real.exp (-(2 * V * q))
                  * ∫ ω, chaosShift f x (2 * V / Real.log x) ω ^ q ∂μ
            ≤ ∫ ω, meanSquareIntegral f x ω ^ q ∂μ := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hbase : (0 : ℝ) < (2 * Real.pi)⁻¹ * (4 / 5) := by positivity
  have hinv1 : (2 * Real.pi)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right; linarith
  have hbase1 : (2 * Real.pi)⁻¹ * (4 / 5) ≤ 1 := by nlinarith [hbase.le]
  have hw23 : (0 : ℝ) < 8 * ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n := by
    have h0 : (0 : ℝ) < ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n :=
      (summable_shiftWeight (by norm_num)).tsum_pos
        (fun n => shiftWeight_nonneg _ n) 0 (shiftWeight_pos _ 0)
    linarith
  exact ⟨meanSquareChaosLower, meanSquareChaosUpper, hbase, hw23,
    meanSquare_ge_chaosShift_named⟩

end RMF
