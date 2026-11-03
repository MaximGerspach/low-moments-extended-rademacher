/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.MatchingGaussian
import Mathlib.Probability.Distributions.Gaussian.Basic
import RMF.Probability.ProductIndependence

/-!
# The bivariate matching Gaussian family

The two-point Gaussian comparison (Harper's Lemma 7) swaps a pair-valued summand against a Gaussian
pair, so it needs the bivariate analogue of `RMF.exists_gaussian_matching_moments`: an independent
family of Gaussian **pairs** whose five raw moments `E N¹`, `E N²`, `E (N¹)²`, `E N¹N²`, `E (N²)²`
match prescribed targets.  Those five are exactly `RMF.quadMonomial`, which is what
`RMF.abs_integral_swap_le` compares.

**The pair is not centred, and must not be.**  `RMF.le_measure_tilted_box` is stated for centred
Gaussians, but the tilted block increments have mean `≈ 1` — that `1` per block is the drift, and
it is the `-j` in Harper's barrier.  So the means are carried explicitly here, and the translation
to the centred form is a separate, visible step.

The construction is the regression form: with `Z ~ N(0, V₁)` and `W ~ N(0,1)` independent,
```
  N¹ = m₁ + Z,        N² = m₂ + ρ·Z + s·W,
```
where `ρ = c/V₁` is the regression slope and `s² = V₂ - c²/V₁` the residual variance.  This section
establishes the three scalar identities that make those come out right, **including at `V₁ = 0`**,
where Cauchy–Schwarz forces `c = 0` and Lean's `c/0 = 0` gives the correct degenerate family.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

universe u

namespace RMF

/-- The regression slope of the second coordinate on the first, `c/V₁`.

At `V₁ = 0` this is `0` by Lean's division convention, which is the right value: Cauchy–Schwarz
then forces `c = 0`, and the second coordinate carries no component of the first. -/
noncomputable def pairSlope (V₁ c : ℝ) : ℝ := c / V₁

/-- The residual variance `V₂ - c²/V₁`: the variance of the second coordinate once its regression
on the first is removed. -/
noncomputable def pairResidVar (V₁ V₂ c : ℝ) : ℝ := V₂ - c ^ 2 / V₁

/-- **The residual variance inherits the second coordinate's bracket**: `1/8 ≤ 2V₂ ≤ 9` and
`cv² ≤ V₁V₂/16` give `1/9 ≤ 2·pairResidVar ≤ 9`, as
`RMF.le_toReal_measure_box_gaussianPairLaw_envelope` asks.  The upper half is free; at correlation
at most `1/4` the residual keeps `15/16` of `V₂`, and `(15/16)·(1/8) = 15/128 ≥ 1/9`.  In the
application the block decorrelation estimate makes the covariance `O(e^{-m})`. -/
lemma pairResidVar_bracket {V₁ V₂ cv : ℝ} (hV₁ : 0 < V₁) (hV₂l : 1 / 8 ≤ 2 * V₂)
    (hV₂u : 2 * V₂ ≤ 9) (hcs : cv ^ 2 ≤ V₁ * V₂ / 16) :
    1 / 9 ≤ 2 * pairResidVar V₁ V₂ cv ∧ 2 * pairResidVar V₁ V₂ cv ≤ 9 := by
  have hdiv : cv ^ 2 / V₁ ≤ V₂ / 16 := by
    rw [div_le_iff₀ hV₁]
    calc cv ^ 2 ≤ V₁ * V₂ / 16 := hcs
      _ = V₂ / 16 * V₁ := by ring
  have hnn : (0 : ℝ) ≤ cv ^ 2 / V₁ := div_nonneg (sq_nonneg cv) hV₁.le
  rw [pairResidVar]
  constructor <;> linarith

/-- **A small covariance discharges both pair conditions at once.**  At `1/16 ≤ V₁, V₂`, the bound
`|cv| ≤ 1/100` gives `|pairSlope V₁ cv| ≤ 1/4` (in fact `4/25`) and `cv² ≤ V₁V₂/16` (in fact
`1/10000` against `1/4096`), the two conditions of
`RMF.le_toReal_measure_box_gaussianPairLaw_envelope`.  `|cv|` is the logarithmic correlation,
`≈ 1/2` when the two heights coincide; Harper's height separation is what makes it small. -/
lemma abs_pairSlope_le_and_cs_of_abs_le {V₁ V₂ cv : ℝ} (hV₁ : 1 / 16 ≤ V₁)
    (hV₂ : 1 / 16 ≤ V₂) (hcv : |cv| ≤ 1 / 100) :
    |pairSlope V₁ cv| ≤ 1 / 4 ∧ cv ^ 2 ≤ V₁ * V₂ / 16 := by
  have hV₁pos : (0 : ℝ) < V₁ := by linarith
  constructor
  · rw [pairSlope, abs_div, abs_of_pos hV₁pos, div_le_iff₀ hV₁pos]
    linarith
  · have hsq : cv ^ 2 ≤ (1 / 100) ^ 2 := by
      have := abs_nonneg cv
      nlinarith [sq_abs cv, hcv]
    nlinarith [hV₁, hV₂, hsq]

/-- Cauchy–Schwarz at a degenerate first coordinate: `V₁ = 0` forces the covariance to vanish. -/
lemma eq_zero_of_cs_of_var_eq_zero {V₁ V₂ c : ℝ} (hV₁ : V₁ = 0) (hCS : c ^ 2 ≤ V₁ * V₂) :
    c = 0 := by
  rw [hV₁, zero_mul] at hCS
  have hsq : c ^ 2 = 0 := le_antisymm hCS (sq_nonneg c)
  exact (pow_eq_zero_iff (n := 2) (by norm_num)).1 hsq

/-- **The residual variance is a variance.**  This is Cauchy–Schwarz, and it is the only place the
hypothesis `c² ≤ V₁V₂` is used. -/
lemma pairResidVar_nonneg {V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂)
    (hCS : c ^ 2 ≤ V₁ * V₂) : 0 ≤ pairResidVar V₁ V₂ c := by
  rcases eq_or_lt_of_le hV₁ with h | h
  · have hc : c = 0 := eq_zero_of_cs_of_var_eq_zero h.symm hCS
    rw [pairResidVar, ← h, hc]
    simpa using hV₂
  · rw [pairResidVar, sub_nonneg, div_le_iff₀ h]
    nlinarith [hCS]

/-- **The covariance comes out right**: `ρ·V₁ = c`.  True at `V₁ = 0` too, because `c` is then
forced to vanish. -/
lemma pairSlope_mul_var {V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁) (hCS : c ^ 2 ≤ V₁ * V₂) :
    pairSlope V₁ c * V₁ = c := by
  rcases eq_or_lt_of_le hV₁ with h | h
  · have hc : c = 0 := eq_zero_of_cs_of_var_eq_zero h.symm hCS
    rw [pairSlope, ← h, hc]
    simp
  · rw [pairSlope, div_mul_cancel₀ _ (ne_of_gt h)]

/-- **The second variance comes out right**: `ρ²V₁ + s² = V₂`.  Again including at `V₁ = 0`, where
both `ρ` and `c²/V₁` are `0` and the identity reads `V₂ = V₂`. -/
lemma pairSlope_sq_mul_var_add_residVar {V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁) :
    pairSlope V₁ c ^ 2 * V₁ + pairResidVar V₁ V₂ c = V₂ := by
  rcases eq_or_lt_of_le hV₁ with h | h
  · rw [pairSlope, pairResidVar, ← h]
    simp
  · rw [pairSlope, pairResidVar, div_pow]
    field_simp
    ring

/-! ### The law, and the family carrying it

The bivariate law is the pushforward of a product of two *independent* one-dimensional Gaussians
under the regression map — which is the only place the pair structure enters.  The independent
family is indexed by pairs: handing `exists_hasLaw_indepFun` the type `ℝ × ℝ` directly gives
`iIndepFun N Q`, each `N i` being a single draw. -/

/-- **The bivariate Gaussian law** with means `m₁, m₂`, variances `V₁, V₂` and covariance `c`: the
image of `N(0,V₁) ⊗ N(0,1)` under `(z, w) ↦ (m₁ + z, m₂ + ρz + sw)`, `ρ = RMF.pairSlope V₁ c`,
`s = √(RMF.pairResidVar V₁ V₂ c)`.  `RMF.pairSlope_mul_var` and
`RMF.pairSlope_sq_mul_var_add_residVar` make the second moments come out. -/
noncomputable def gaussianPairLaw (m₁ m₂ V₁ V₂ c : ℝ) : Measure (ℝ × ℝ) :=
  ((gaussianReal 0 V₁.toNNReal).prod (gaussianReal 0 1)).map
    (fun z => (m₁ + z.1,
      m₂ + pairSlope V₁ c * z.1 + Real.sqrt (pairResidVar V₁ V₂ c) * z.2))

lemma measurable_gaussianPairMap (m₁ m₂ V₁ V₂ c : ℝ) :
    Measurable (fun z : ℝ × ℝ => (m₁ + z.1,
      m₂ + pairSlope V₁ c * z.1 + Real.sqrt (pairResidVar V₁ V₂ c) * z.2)) := by
  fun_prop

instance isProbabilityMeasure_gaussianPairLaw (m₁ m₂ V₁ V₂ c : ℝ) :
    IsProbabilityMeasure (gaussianPairLaw m₁ m₂ V₁ V₂ c) := by
  rw [gaussianPairLaw]
  exact Measure.isProbabilityMeasure_map (measurable_gaussianPairMap m₁ m₂ V₁ V₂ c).aemeasurable

/-! ### The bivariate law is Gaussian in Mathlib's sense

The block Gaussian the two-point comparison swaps against is a **sum** of per-prime pairs, and
identifying that sum with a single `RMF.gaussianPairLaw` is the two-dimensional analogue of the
convolution `ProbabilityTheory.gaussianReal_conv_gaussianReal` that the one-point development uses.
The escape one would like — choosing the per-prime pairs so that the sum is manifestly in
regression form — is not available: the per-prime slope is `ρ_p = c_p/V₁_p = cos(t \log p)`, which
varies with `p`, so `∑ ρ_p Z_p ≠ ρ ∑ Z_p`.

Mathlib's route is `ProbabilityTheory.IsGaussian`, which carries `isGaussian_conv` and determines a
measure by `μ[L]` and `Var[L; μ]` over the dual.  This instance is the first step: the regression
map is a translation of a *continuous linear* map, and both preserve `IsGaussian`. -/

instance isGaussian_gaussianPairLaw (m₁ m₂ V₁ V₂ c : ℝ) :
    IsGaussian (gaussianPairLaw m₁ m₂ V₁ V₂ c) := by
  set ρ := pairSlope V₁ c with hρ
  set sc := Real.sqrt (pairResidVar V₁ V₂ c) with hsc
  set A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ρ • ContinuousLinearMap.fst ℝ ℝ ℝ + sc • ContinuousLinearMap.snd ℝ ℝ ℝ) with hA
  have hfun : (fun z : ℝ × ℝ => (m₁ + z.1, m₂ + ρ * z.1 + sc * z.2))
      = (fun x : ℝ × ℝ => (m₁, m₂) + x) ∘ A := by
    funext z
    simp only [hA, Function.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, Prod.mk_add_mk]
    exact Prod.ext rfl (by ring)
  rw [gaussianPairLaw, hfun, ← Measure.map_map (by fun_prop) A.continuous.measurable]
  infer_instance

/-- **The bivariate Gaussian family.**  An independent family of Gaussian pairs with prescribed laws
`RMF.gaussianPairLaw`.  There is **no hypothesis**: `Real.toNNReal` and `Real.sqrt` clip the
degenerate cases, and the Cauchy–Schwarz condition `c² ≤ V₁V₂` is needed only to identify the
moments (`RMF.exists_gaussian_pair_matching_quadMonomial`). -/
theorem exists_gaussian_pair_matching_moments {ι : Type u} (m₁ m₂ V₁ V₂ c : ι → ℝ) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ι → Ω' → ℝ × ℝ),
      IsProbabilityMeasure Q ∧ (∀ i, Measurable (N i)) ∧ iIndepFun N Q ∧
        (∀ i, Q.map (N i) = gaussianPairLaw (m₁ i) (m₂ i) (V₁ i) (V₂ i) (c i)) := by
  obtain ⟨Ω', mΩ', Q, N, hNm, hNlaw, hNind, hQ⟩ :=
    exists_hasLaw_indepFun (fun _ : ι => ℝ × ℝ)
      (fun i => gaussianPairLaw (m₁ i) (m₂ i) (V₁ i) (V₂ i) (c i))
  exact ⟨Ω', mΩ', Q, N, hQ, hNm, hNind, fun i => (hNlaw i).map_eq⟩

/-! ### The same family, realised in regression form

`RMF.exists_gaussian_pair_matching_moments` builds the family on one space and gets `iIndepFun` for
nothing, because each increment is a single `ℝ × ℝ`-valued draw.  What it does **not** give is a
*realisation*: which parts of the pair are shared and which are independent.  The two-point barrier
argument needs exactly that — the second walk as the first, sheared, plus an independent walk — and
the shear is what makes `ℙ`(both walks in the tube) a **product**, hence the square.

So the same laws are built again, on the two factors of a product space, where the factorisation is
`MeasureTheory.Measure.prod_prod`; the price is `iIndepFun` for the pair family, which
`RMF.iIndepFun_pairProd` pays.  `Z` and `W` carry `RMF.gaussianPairLaw`'s own base laws `N(0, V₁)`
and `N(0, 1)`, so the law below is the definition of `gaussianPairLaw` read from the other side, and
no Cauchy–Schwarz condition appears. -/

/-- **The bivariate Gaussian family in regression form.**  The first coordinate reads the first
factor, the second reads both: `N i = (m₁ + Z i, m₂ + ρ·Z i + s·W i)` with `Z ⊥ W`. -/
theorem exists_gaussian_pair_regression {ι : Type u} (m₁ m₂ V₁ V₂ c : ι → ℝ) :
    ∃ (Ω₁ Ω₂ : Type u) (_ : MeasurableSpace Ω₁) (_ : MeasurableSpace Ω₂)
      (Q₁ : Measure Ω₁) (Q₂ : Measure Ω₂) (Z : ι → Ω₁ → ℝ) (W : ι → Ω₂ → ℝ),
      IsProbabilityMeasure Q₁ ∧ IsProbabilityMeasure Q₂ ∧
        (∀ i, Measurable (Z i)) ∧ (∀ i, Measurable (W i)) ∧
        iIndepFun Z Q₁ ∧ iIndepFun W Q₂ ∧
        (∀ i, Q₁.map (Z i) = gaussianReal 0 (V₁ i).toNNReal) ∧
        (∀ i, Q₂.map (W i) = gaussianReal 0 1) ∧
        iIndepFun (fun i (ω : Ω₁ × Ω₂) => (m₁ i + Z i ω.1,
          m₂ i + pairSlope (V₁ i) (c i) * Z i ω.1
            + Real.sqrt (pairResidVar (V₁ i) (V₂ i) (c i)) * W i ω.2)) (Q₁.prod Q₂) ∧
        (∀ i, (Q₁.prod Q₂).map (fun ω : Ω₁ × Ω₂ => (m₁ i + Z i ω.1,
            m₂ i + pairSlope (V₁ i) (c i) * Z i ω.1
              + Real.sqrt (pairResidVar (V₁ i) (V₂ i) (c i)) * W i ω.2))
          = gaussianPairLaw (m₁ i) (m₂ i) (V₁ i) (V₂ i) (c i)) := by
  obtain ⟨Ω₁, mΩ₁, Q₁, Z, hZm, hZlaw, hZind, hQ₁⟩ :=
    exists_hasLaw_indepFun (fun _ : ι => ℝ) (fun i => gaussianReal 0 (V₁ i).toNNReal)
  obtain ⟨Ω₂, mΩ₂, Q₂, W, hWm, hWlaw, hWind, hQ₂⟩ :=
    exists_hasLaw_indepFun (fun _ : ι => ℝ) (fun _ : ι => gaussianReal 0 1)
  refine ⟨Ω₁, Ω₂, mΩ₁, mΩ₂, Q₁, Q₂, Z, W, hQ₁, hQ₂, hZm, hWm, hZind, hWind,
    fun i => (hZlaw i).map_eq, fun i => (hWlaw i).map_eq, ?_, fun i => ?_⟩
  · exact (iIndepFun_pairProd hZm hWm hZind hWind).comp
      (fun i => fun p : ℝ × ℝ => (m₁ i + p.1, m₂ i + pairSlope (V₁ i) (c i) * p.1
        + Real.sqrt (pairResidVar (V₁ i) (V₂ i) (c i)) * p.2)) fun _ => by fun_prop
  · have hcomp : (fun ω : Ω₁ × Ω₂ => (m₁ i + Z i ω.1,
        m₂ i + pairSlope (V₁ i) (c i) * Z i ω.1
          + Real.sqrt (pairResidVar (V₁ i) (V₂ i) (c i)) * W i ω.2))
      = (fun z : ℝ × ℝ => (m₁ i + z.1, m₂ i + pairSlope (V₁ i) (c i) * z.1
          + Real.sqrt (pairResidVar (V₁ i) (V₂ i) (c i)) * z.2)) ∘ Prod.map (Z i) (W i) := rfl
    rw [hcomp, ← Measure.map_map (measurable_gaussianPairMap _ _ _ _ _) (by fun_prop),
      ← Measure.map_prod_map _ _ (hZm i) (hWm i), (hZlaw i).map_eq, (hWlaw i).map_eq]
    rfl

/-! ### The base moments

Before the regression map is applied, the underlying measure is a product of two centred
Gaussians, and all five second-order moments follow from `integral_prod_mul` — including the
mixed one, which is `0` precisely because the two factors are independent and centred.

Taking `g ≡ 1` in `integral_prod_mul` gives the marginals too, so no separate Fubini step is
needed anywhere in this section. -/

/-- The second moment of a real Gaussian, as a statement about the measure itself. -/
lemma integral_mul_self_gaussianReal (m : ℝ) (v : ℝ≥0) :
    ∫ x, x * x ∂gaussianReal m v = (v : ℝ) + m ^ 2 :=
  integral_sq_of_hasLaw_gaussianReal measurable_id Measure.map_id

/-- The underlying product measure of `RMF.gaussianPairLaw`, named so the moments below can speak
about it. -/
noncomputable def gaussianPairBase (V₁ : ℝ) : Measure (ℝ × ℝ) :=
  (gaussianReal 0 V₁.toNNReal).prod (gaussianReal 0 1)

instance isProbabilityMeasure_gaussianPairBase (V₁ : ℝ) :
    IsProbabilityMeasure (gaussianPairBase V₁) := by
  rw [gaussianPairBase]
  infer_instance

lemma integral_fst_gaussianPairBase (V₁ : ℝ) :
    ∫ z : ℝ × ℝ, z.1 ∂gaussianPairBase V₁ = 0 := by
  have h : ∫ z : ℝ × ℝ, z.1 * (1 : ℝ) ∂gaussianPairBase V₁
      = (∫ x, x ∂gaussianReal 0 V₁.toNNReal) * ∫ _ : ℝ, (1 : ℝ) ∂gaussianReal 0 1 :=
    integral_prod_mul (fun x : ℝ => x) (fun _ : ℝ => (1 : ℝ))
  simpa [integral_id_gaussianReal] using h

lemma integral_snd_gaussianPairBase (V₁ : ℝ) :
    ∫ z : ℝ × ℝ, z.2 ∂gaussianPairBase V₁ = 0 := by
  have h : ∫ z : ℝ × ℝ, (1 : ℝ) * z.2 ∂gaussianPairBase V₁
      = (∫ _ : ℝ, (1 : ℝ) ∂gaussianReal 0 V₁.toNNReal) * ∫ y, y ∂gaussianReal 0 1 :=
    integral_prod_mul (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => y)
  simpa [integral_id_gaussianReal] using h

lemma integral_fst_sq_gaussianPairBase {V₁ : ℝ} (hV₁ : 0 ≤ V₁) :
    ∫ z : ℝ × ℝ, z.1 * z.1 ∂gaussianPairBase V₁ = V₁ := by
  have h : ∫ z : ℝ × ℝ, (z.1 * z.1) * (1 : ℝ) ∂gaussianPairBase V₁
      = (∫ x, x * x ∂gaussianReal 0 V₁.toNNReal) * ∫ _ : ℝ, (1 : ℝ) ∂gaussianReal 0 1 :=
    integral_prod_mul (fun x : ℝ => x * x) (fun _ : ℝ => (1 : ℝ))
  rw [integral_mul_self_gaussianReal] at h
  simpa [Real.coe_toNNReal _ hV₁] using h

lemma integral_snd_sq_gaussianPairBase (V₁ : ℝ) :
    ∫ z : ℝ × ℝ, z.2 * z.2 ∂gaussianPairBase V₁ = 1 := by
  have h : ∫ z : ℝ × ℝ, (1 : ℝ) * (z.2 * z.2) ∂gaussianPairBase V₁
      = (∫ _ : ℝ, (1 : ℝ) ∂gaussianReal 0 V₁.toNNReal) * ∫ y, y * y ∂gaussianReal 0 1 :=
    integral_prod_mul (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => y * y)
  rw [integral_mul_self_gaussianReal] at h
  simpa using h

/-- **The mixed moment vanishes.**  This is the only place independence of the two factors is
used, and it is what makes the covariance of the pair come out as `ρV₁` and nothing else. -/
lemma integral_fst_mul_snd_gaussianPairBase (V₁ : ℝ) :
    ∫ z : ℝ × ℝ, z.1 * z.2 ∂gaussianPairBase V₁ = 0 := by
  have h : ∫ z : ℝ × ℝ, z.1 * z.2 ∂gaussianPairBase V₁
      = (∫ x, x ∂gaussianReal 0 V₁.toNNReal) * ∫ y, y ∂gaussianReal 0 1 :=
    integral_prod_mul (fun x : ℝ => x) (fun y : ℝ => y)
  simpa [integral_id_gaussianReal] using h

/-! ### Integrability, and the transport through the regression map

Splitting `∫ (m₁ + z₁)(m₂ + ρz₁ + sz₂)` into its six terms needs each term integrable, so the
Gaussian's moments are recorded as `Integrable` facts here.  `integral_prod_mul` — Mathlib's —
needed none of this; it is the *expansion* that does. -/

lemma integrable_id_gaussianReal (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => x) (gaussianReal m v) :=
  memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1)

lemma integrable_mul_self_gaussianReal (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => x * x) (gaussianReal m v) := by
  have h := (memLp_id_gaussianReal (μ := m) (v := v) 2).integrable_sq
  simpa [pow_two] using h

lemma integrable_fst_gaussianPairBase (V₁ : ℝ) :
    Integrable (fun z : ℝ × ℝ => z.1) (gaussianPairBase V₁) := by
  rw [gaussianPairBase]
  exact integrable_comp_fst (integrable_id_gaussianReal 0 V₁.toNNReal)

lemma integrable_snd_gaussianPairBase (V₁ : ℝ) :
    Integrable (fun z : ℝ × ℝ => z.2) (gaussianPairBase V₁) := by
  rw [gaussianPairBase]
  exact integrable_comp_snd (integrable_id_gaussianReal 0 1)

lemma integrable_fst_sq_gaussianPairBase (V₁ : ℝ) :
    Integrable (fun z : ℝ × ℝ => z.1 * z.1) (gaussianPairBase V₁) := by
  rw [gaussianPairBase]
  exact integrable_comp_fst (integrable_mul_self_gaussianReal 0 V₁.toNNReal)

lemma integrable_snd_sq_gaussianPairBase (V₁ : ℝ) :
    Integrable (fun z : ℝ × ℝ => z.2 * z.2) (gaussianPairBase V₁) := by
  rw [gaussianPairBase]
  exact integrable_comp_snd (integrable_mul_self_gaussianReal 0 1)

/-- The law is the pushforward of the base under the regression map — by definition, but named so
the transport below can rewrite with it. -/
lemma gaussianPairLaw_eq_map (m₁ m₂ V₁ V₂ c : ℝ) :
    gaussianPairLaw m₁ m₂ V₁ V₂ c
      = (gaussianPairBase V₁).map
          (fun z => (m₁ + z.1,
            m₂ + pairSlope V₁ c * z.1 + Real.sqrt (pairResidVar V₁ V₂ c) * z.2)) := rfl

/-- **Transport.**  Any integral against the pair law is an integral against the base, with the
regression map applied to the integrand.  Every moment below is this plus algebra. -/
lemma integral_gaussianPairLaw {m₁ m₂ V₁ V₂ c : ℝ} {g : ℝ × ℝ → ℝ}
    (hg : AEStronglyMeasurable g (gaussianPairLaw m₁ m₂ V₁ V₂ c)) :
    ∫ w, g w ∂gaussianPairLaw m₁ m₂ V₁ V₂ c
      = ∫ z, g (m₁ + z.1, m₂ + pairSlope V₁ c * z.1
          + Real.sqrt (pairResidVar V₁ V₂ c) * z.2) ∂gaussianPairBase V₁ := by
  rw [gaussianPairLaw_eq_map] at hg ⊢
  exact integral_map (measurable_gaussianPairMap m₁ m₂ V₁ V₂ c).aemeasurable hg

/-! ### The five moments

Each transported integrand is a quadratic in `(z₁, z₂)`, so one lemma covers all five: expand,
integrate term by term, and read off `a + eV₁ + g`.  The rest is algebra, and it is where
`RMF.pairSlope_mul_var` and `RMF.pairSlope_sq_mul_var_add_residVar` do their work.

**Cauchy–Schwarz enters here and only here** — in the covariance and the second variance.  The
means and the first variance need nothing beyond `0 ≤ V₁`. -/

lemma integrable_fst_mul_snd_gaussianPairBase (V₁ : ℝ) :
    Integrable (fun z : ℝ × ℝ => z.1 * z.2) (gaussianPairBase V₁) := by
  rw [gaussianPairBase]
  exact (integrable_id_gaussianReal 0 V₁.toNNReal).mul_prod (integrable_id_gaussianReal 0 1)

/-- **Every quadratic, in one go.**  Only the constant, the `z₁²` and the `z₂²` coefficients
survive: the two linear terms and the cross term integrate to zero. -/
lemma integral_quad_gaussianPairBase {V₁ : ℝ} (hV₁ : 0 ≤ V₁) (a b d e f g : ℝ) :
    ∫ z : ℝ × ℝ, (a + b * z.1 + d * z.2 + e * (z.1 * z.1) + f * (z.1 * z.2)
        + g * (z.2 * z.2)) ∂gaussianPairBase V₁
      = a + e * V₁ + g := by
  have hA : Integrable (fun _ : ℝ × ℝ => a) (gaussianPairBase V₁) := integrable_const a
  have hB : Integrable (fun z : ℝ × ℝ => b * z.1) (gaussianPairBase V₁) :=
    (integrable_fst_gaussianPairBase V₁).const_mul b
  have hD : Integrable (fun z : ℝ × ℝ => d * z.2) (gaussianPairBase V₁) :=
    (integrable_snd_gaussianPairBase V₁).const_mul d
  have hE : Integrable (fun z : ℝ × ℝ => e * (z.1 * z.1)) (gaussianPairBase V₁) :=
    (integrable_fst_sq_gaussianPairBase V₁).const_mul e
  have hF : Integrable (fun z : ℝ × ℝ => f * (z.1 * z.2)) (gaussianPairBase V₁) :=
    (integrable_fst_mul_snd_gaussianPairBase V₁).const_mul f
  have hG : Integrable (fun z : ℝ × ℝ => g * (z.2 * z.2)) (gaussianPairBase V₁) :=
    (integrable_snd_sq_gaussianPairBase V₁).const_mul g
  have j1 : Integrable (fun z : ℝ × ℝ => a + b * z.1) (gaussianPairBase V₁) := hA.add hB
  have j2 : Integrable (fun z : ℝ × ℝ => a + b * z.1 + d * z.2) (gaussianPairBase V₁) :=
    j1.add hD
  have j3 : Integrable (fun z : ℝ × ℝ => a + b * z.1 + d * z.2 + e * (z.1 * z.1))
      (gaussianPairBase V₁) := j2.add hE
  have j4 : Integrable (fun z : ℝ × ℝ => a + b * z.1 + d * z.2 + e * (z.1 * z.1)
      + f * (z.1 * z.2)) (gaussianPairBase V₁) := j3.add hF
  rw [integral_add j4 hG, integral_add j3 hF, integral_add j2 hE, integral_add j1 hD,
    integral_add hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul,
    integral_fst_gaussianPairBase, integral_snd_gaussianPairBase,
    integral_fst_sq_gaussianPairBase hV₁, integral_fst_mul_snd_gaussianPairBase,
    integral_snd_sq_gaussianPairBase, integral_const]
  simp

lemma integral_fst_gaussianPairLaw {m₁ m₂ V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁) :
    ∫ w : ℝ × ℝ, w.1 ∂gaussianPairLaw m₁ m₂ V₁ V₂ c = m₁ := by
  rw [integral_gaussianPairLaw (by fun_prop)]
  have h : ∀ z : ℝ × ℝ, m₁ + z.1
      = m₁ + 1 * z.1 + 0 * z.2 + 0 * (z.1 * z.1) + 0 * (z.1 * z.2) + 0 * (z.2 * z.2) :=
    fun z => by ring
  simp_rw [h]
  rw [integral_quad_gaussianPairBase hV₁]
  ring

lemma integral_snd_gaussianPairLaw {m₁ m₂ V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁) :
    ∫ w : ℝ × ℝ, w.2 ∂gaussianPairLaw m₁ m₂ V₁ V₂ c = m₂ := by
  rw [integral_gaussianPairLaw (by fun_prop)]
  calc ∫ z : ℝ × ℝ, (m₂ + pairSlope V₁ c * z.1
          + Real.sqrt (pairResidVar V₁ V₂ c) * z.2) ∂gaussianPairBase V₁
      = ∫ z : ℝ × ℝ, (m₂ + pairSlope V₁ c * z.1
          + Real.sqrt (pairResidVar V₁ V₂ c) * z.2
          + 0 * (z.1 * z.1) + 0 * (z.1 * z.2) + 0 * (z.2 * z.2)) ∂gaussianPairBase V₁ :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    _ = m₂ := by
        rw [integral_quad_gaussianPairBase hV₁]
        ring

lemma integral_fst_sq_gaussianPairLaw {m₁ m₂ V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁) :
    ∫ w : ℝ × ℝ, w.1 * w.1 ∂gaussianPairLaw m₁ m₂ V₁ V₂ c = V₁ + m₁ ^ 2 := by
  rw [integral_gaussianPairLaw (by fun_prop)]
  have h : ∀ z : ℝ × ℝ, (m₁ + z.1) * (m₁ + z.1)
      = m₁ ^ 2 + (2 * m₁) * z.1 + 0 * z.2 + 1 * (z.1 * z.1) + 0 * (z.1 * z.2)
        + 0 * (z.2 * z.2) := fun z => by ring
  simp_rw [h]
  rw [integral_quad_gaussianPairBase hV₁]
  ring

/-- **The covariance.**  `RMF.pairSlope_mul_var` is what turns `ρV₁` into `c`; Cauchy–Schwarz is
needed for it, and this is the first moment that needs it. -/
lemma integral_fst_mul_snd_gaussianPairLaw {m₁ m₂ V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁)
    (hCS : c ^ 2 ≤ V₁ * V₂) :
    ∫ w : ℝ × ℝ, w.1 * w.2 ∂gaussianPairLaw m₁ m₂ V₁ V₂ c = c + m₁ * m₂ := by
  rw [integral_gaussianPairLaw (by fun_prop)]
  have h : ∀ z : ℝ × ℝ, (m₁ + z.1)
        * (m₂ + pairSlope V₁ c * z.1 + Real.sqrt (pairResidVar V₁ V₂ c) * z.2)
      = m₁ * m₂ + (m₁ * pairSlope V₁ c + m₂) * z.1
        + (m₁ * Real.sqrt (pairResidVar V₁ V₂ c)) * z.2
        + pairSlope V₁ c * (z.1 * z.1)
        + Real.sqrt (pairResidVar V₁ V₂ c) * (z.1 * z.2) + 0 * (z.2 * z.2) :=
    fun z => by ring
  simp_rw [h]
  rw [integral_quad_gaussianPairBase hV₁, pairSlope_mul_var hV₁ hCS]
  ring

/-- **The second variance.**  Here both scalar identities are used, and `Real.sq_sqrt` needs
`RMF.pairResidVar_nonneg`, which is Cauchy–Schwarz again. -/
lemma integral_snd_sq_gaussianPairLaw {m₁ m₂ V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂)
    (hCS : c ^ 2 ≤ V₁ * V₂) :
    ∫ w : ℝ × ℝ, w.2 * w.2 ∂gaussianPairLaw m₁ m₂ V₁ V₂ c = V₂ + m₂ ^ 2 := by
  rw [integral_gaussianPairLaw (by fun_prop)]
  calc ∫ z : ℝ × ℝ, ((m₂ + pairSlope V₁ c * z.1
            + Real.sqrt (pairResidVar V₁ V₂ c) * z.2)
          * (m₂ + pairSlope V₁ c * z.1
            + Real.sqrt (pairResidVar V₁ V₂ c) * z.2)) ∂gaussianPairBase V₁
      = ∫ z : ℝ × ℝ, (m₂ ^ 2 + (2 * m₂ * pairSlope V₁ c) * z.1
          + (2 * m₂ * Real.sqrt (pairResidVar V₁ V₂ c)) * z.2
          + (pairSlope V₁ c ^ 2) * (z.1 * z.1)
          + (2 * pairSlope V₁ c * Real.sqrt (pairResidVar V₁ V₂ c)) * (z.1 * z.2)
          + (Real.sqrt (pairResidVar V₁ V₂ c) * Real.sqrt (pairResidVar V₁ V₂ c))
              * (z.2 * z.2)) ∂gaussianPairBase V₁ :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    _ = V₂ + m₂ ^ 2 := by
        rw [integral_quad_gaussianPairBase hV₁,
          Real.mul_self_sqrt (pairResidVar_nonneg hV₁ hV₂ hCS)]
        linarith [pairSlope_sq_mul_var_add_residVar (V₂ := V₂) (c := c) hV₁]

/-! ### What the dual reads off

`ProbabilityTheory.IsGaussian.charFunDual_eq` determines a Gaussian measure by two numbers per
dual functional, `μ[L]` and `Var[L; μ]`.  For `ℝ × ℝ` every `L` is `t₁x₁ + t₂x₂` with
`t₁ = L(1,0)`, `t₂ = L(0,1)`, so both are quadratic expressions in the five moments — and
`RMF.integral_quad_gaussianPairBase` computes them in one step, without any integrability
bookkeeping, because the transported integrand is already a quadratic in the base coordinates.

The variance comes out as the quadratic form `t₁²V₁ + 2t₁t₂c + t₂²V₂` — the covariance matrix read
against `t`, as it must be.  The two identities that make it so are `RMF.pairSlope_mul_var`
(`ρV₁ = c`) and `RMF.pairSlope_sq_mul_var_add_residVar` (`ρ²V₁ + s² = V₂`), which is where
Cauchy–Schwarz is spent. -/

lemma dual_apply_pair (L : StrongDual ℝ (ℝ × ℝ)) (x : ℝ × ℝ) :
    L x = L (1, 0) * x.1 + L (0, 1) * x.2 := by
  have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm, mul_comm x.2]

lemma integral_lin_gaussianPairLaw {m₁ m₂ V₁ V₂ c t₁ t₂ : ℝ} (hV₁ : 0 ≤ V₁) :
    ∫ w : ℝ × ℝ, (t₁ * w.1 + t₂ * w.2) ∂gaussianPairLaw m₁ m₂ V₁ V₂ c
      = t₁ * m₁ + t₂ * m₂ := by
  rw [integral_gaussianPairLaw (by fun_prop)]
  have h : ∀ z : ℝ × ℝ,
      t₁ * (m₁ + z.1) + t₂ * (m₂ + pairSlope V₁ c * z.1
          + Real.sqrt (pairResidVar V₁ V₂ c) * z.2)
        = (t₁ * m₁ + t₂ * m₂) + (t₁ + t₂ * pairSlope V₁ c) * z.1
          + (t₂ * Real.sqrt (pairResidVar V₁ V₂ c)) * z.2
          + 0 * (z.1 * z.1) + 0 * (z.1 * z.2) + 0 * (z.2 * z.2) := fun z => by ring
  simp_rw [h]
  rw [integral_quad_gaussianPairBase hV₁]
  ring

lemma integral_lin_sq_gaussianPairLaw {m₁ m₂ V₁ V₂ c t₁ t₂ : ℝ} (hV₁ : 0 ≤ V₁)
    (hV₂ : 0 ≤ V₂) (hCS : c ^ 2 ≤ V₁ * V₂) :
    ∫ w : ℝ × ℝ, (t₁ * w.1 + t₂ * w.2) ^ 2 ∂gaussianPairLaw m₁ m₂ V₁ V₂ c
      = t₁ ^ 2 * V₁ + 2 * t₁ * t₂ * c + t₂ ^ 2 * V₂ + (t₁ * m₁ + t₂ * m₂) ^ 2 := by
  rw [integral_gaussianPairLaw (by fun_prop)]
  have hres : Real.sqrt (pairResidVar V₁ V₂ c) ^ 2 = pairResidVar V₁ V₂ c :=
    Real.sq_sqrt (pairResidVar_nonneg hV₁ hV₂ hCS)
  have hc : pairSlope V₁ c * V₁ = c := pairSlope_mul_var hV₁ hCS
  have hv : pairSlope V₁ c ^ 2 * V₁ + pairResidVar V₁ V₂ c = V₂ :=
    pairSlope_sq_mul_var_add_residVar hV₁
  have h : ∀ z : ℝ × ℝ,
      (t₁ * (m₁ + z.1) + t₂ * (m₂ + pairSlope V₁ c * z.1
          + Real.sqrt (pairResidVar V₁ V₂ c) * z.2)) ^ 2
        = (t₁ * m₁ + t₂ * m₂) ^ 2
          + (2 * (t₁ * m₁ + t₂ * m₂) * (t₁ + t₂ * pairSlope V₁ c)) * z.1
          + (2 * (t₁ * m₁ + t₂ * m₂) * (t₂ * Real.sqrt (pairResidVar V₁ V₂ c))) * z.2
          + ((t₁ + t₂ * pairSlope V₁ c) ^ 2) * (z.1 * z.1)
          + (2 * (t₁ + t₂ * pairSlope V₁ c)
              * (t₂ * Real.sqrt (pairResidVar V₁ V₂ c))) * (z.1 * z.2)
          + ((t₂ * Real.sqrt (pairResidVar V₁ V₂ c)) ^ 2) * (z.2 * z.2) := fun z => by ring
  simp_rw [h]
  rw [integral_quad_gaussianPairBase hV₁]
  linear_combination (2 * t₁ * t₂) * hc + t₂ ^ 2 * hv + t₂ ^ 2 * hres

lemma integral_dual_gaussianPairLaw {m₁ m₂ V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁)
    (L : StrongDual ℝ (ℝ × ℝ)) :
    ∫ w, L w ∂gaussianPairLaw m₁ m₂ V₁ V₂ c = L (1, 0) * m₁ + L (0, 1) * m₂ := by
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall (dual_apply_pair L))) ?_
  exact integral_lin_gaussianPairLaw hV₁

lemma variance_dual_gaussianPairLaw {m₁ m₂ V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂)
    (hCS : c ^ 2 ≤ V₁ * V₂) (L : StrongDual ℝ (ℝ × ℝ)) :
    variance (⇑L) (gaussianPairLaw m₁ m₂ V₁ V₂ c)
      = L (1, 0) ^ 2 * V₁ + 2 * L (1, 0) * L (0, 1) * c + L (0, 1) ^ 2 * V₂ := by
  have hmem : MemLp (⇑L) 2 (gaussianPairLaw m₁ m₂ V₁ V₂ c) :=
    IsGaussian.memLp_dual _ L 2 (by simp)
  have hsq : (fun w : ℝ × ℝ => ((⇑L : ℝ × ℝ → ℝ) ^ 2) w)
      =ᵐ[gaussianPairLaw m₁ m₂ V₁ V₂ c]
      fun w : ℝ × ℝ => (L (1, 0) * w.1 + L (0, 1) * w.2) ^ 2 :=
    Filter.Eventually.of_forall fun w => by
      simp only [Pi.pow_apply]
      rw [dual_apply_pair L w]
  have hlin : (⇑L : ℝ × ℝ → ℝ) =ᵐ[gaussianPairLaw m₁ m₂ V₁ V₂ c]
      fun w : ℝ × ℝ => L (1, 0) * w.1 + L (0, 1) * w.2 :=
    Filter.Eventually.of_forall (dual_apply_pair L)
  rw [variance_eq_sub hmem, integral_congr_ae hsq, integral_congr_ae hlin,
    integral_lin_sq_gaussianPairLaw hV₁ hV₂ hCS, integral_lin_gaussianPairLaw hV₁]
  ring

/-- **Cauchy–Schwarz is additive.**  If `c² ≤ V₁V₂` and `c'² ≤ V₁'V₂'` then
`(c+c')² ≤ (V₁+V₁')(V₂+V₂')`: a sum of positive semi-definite covariance matrices is one, which is
why the block parameters inherit the condition from the primes.  The content is
`2cc' ≤ V₁V₂' + V₁'V₂`, certified by `(V₁c' - V₁'c)² ≥ 0` divided by `V₁V₁'`; in the degenerate
cases a vanishing variance forces its covariance to vanish. -/
lemma add_cauchy_schwarz {V₁ V₂ c V₁' V₂' c' : ℝ} (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂)
    (hV₁' : 0 ≤ V₁') (hV₂' : 0 ≤ V₂') (h : c ^ 2 ≤ V₁ * V₂) (h' : c' ^ 2 ≤ V₁' * V₂') :
    (c + c') ^ 2 ≤ (V₁ + V₁') * (V₂ + V₂') := by
  rcases eq_or_lt_of_le hV₁ with h1 | h1
  · have hc2 : c ^ 2 ≤ 0 := by rw [← h1] at h; linarith [h]
    have hc : c = 0 := sq_eq_zero_iff.mp (le_antisymm hc2 (sq_nonneg c))
    rw [hc, ← h1]
    nlinarith [h', mul_nonneg hV₁' hV₂]
  rcases eq_or_lt_of_le hV₁' with h2 | h2
  · have hc2 : c' ^ 2 ≤ 0 := by rw [← h2] at h'; linarith [h']
    have hc : c' = 0 := sq_eq_zero_iff.mp (le_antisymm hc2 (sq_nonneg c'))
    rw [hc, ← h2]
    nlinarith [h, mul_nonneg hV₁ hV₂']
  · have hpos : (0 : ℝ) < V₁ * V₁' := mul_pos h1 h2
    have key : (V₁ * V₁') * (2 * (c * c')) ≤ (V₁ * V₁') * (V₁ * V₂' + V₁' * V₂) := by
      nlinarith [sq_nonneg (V₁ * c' - V₁' * c),
        mul_le_mul_of_nonneg_left h' (sq_nonneg V₁),
        mul_le_mul_of_nonneg_left h (sq_nonneg V₁')]
    have h2cc := le_of_mul_le_mul_left key hpos
    nlinarith [h, h', h2cc]

/-- **Cauchy–Schwarz over a block.**  `RMF.add_cauchy_schwarz` iterated: the summed parameters of a
`Finset` of positive semi-definite pairs are again positive semi-definite. -/
lemma sum_cauchy_schwarz {ι : Type*} {V₁ V₂ cv : ι → ℝ} (hV₁ : ∀ i, 0 ≤ V₁ i)
    (hV₂ : ∀ i, 0 ≤ V₂ i) (hCS : ∀ i, cv i ^ 2 ≤ V₁ i * V₂ i) (t : Finset ι) :
    (∑ i ∈ t, cv i) ^ 2 ≤ (∑ i ∈ t, V₁ i) * ∑ i ∈ t, V₂ i := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
      exact add_cauchy_schwarz (hV₁ a) (hV₂ a) (Finset.sum_nonneg fun i _ => hV₁ i)
        (Finset.sum_nonneg fun i _ => hV₂ i) (hCS a) ih

/-- **The bivariate convolution**, the two-dimensional analogue of
`ProbabilityTheory.gaussianReal_conv_gaussianReal`: two pair laws convolve to the pair law at the
summed parameters.  This names the Gaussian side of the two-point comparison, a sum of per-prime
pairs that cannot be put in one regression form (the slope `ρ_p = cos(t log p)` varies with `p`).
The proof is Mathlib's `ProbabilityTheory.IsGaussian`, where the dual mean and variance add;
Cauchy–Schwarz at the summed parameters is `RMF.add_cauchy_schwarz`. -/
theorem gaussianPairLaw_conv {m₁ m₂ V₁ V₂ c m₁' m₂' V₁' V₂' c' : ℝ}
    (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂) (hCS : c ^ 2 ≤ V₁ * V₂)
    (hV₁' : 0 ≤ V₁') (hV₂' : 0 ≤ V₂') (hCS' : c' ^ 2 ≤ V₁' * V₂') :
    (gaussianPairLaw m₁ m₂ V₁ V₂ c).conv (gaussianPairLaw m₁' m₂' V₁' V₂' c')
      = gaussianPairLaw (m₁ + m₁') (m₂ + m₂') (V₁ + V₁') (V₂ + V₂') (c + c') := by
  have hCSsum : (c + c') ^ 2 ≤ (V₁ + V₁') * (V₂ + V₂') :=
    add_cauchy_schwarz hV₁ hV₂ hV₁' hV₂' hCS hCS'
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_conv, IsGaussian.charFunDual_eq, IsGaussian.charFunDual_eq,
    IsGaussian.charFunDual_eq, ← Complex.exp_add, integral_complex_ofReal,
    integral_complex_ofReal, integral_complex_ofReal,
    integral_dual_gaussianPairLaw hV₁, integral_dual_gaussianPairLaw hV₁',
    integral_dual_gaussianPairLaw (by linarith : (0 : ℝ) ≤ V₁ + V₁'),
    variance_dual_gaussianPairLaw hV₁ hV₂ hCS,
    variance_dual_gaussianPairLaw hV₁' hV₂' hCS',
    variance_dual_gaussianPairLaw (by linarith : (0 : ℝ) ≤ V₁ + V₁')
      (by linarith : (0 : ℝ) ≤ V₂ + V₂') hCSsum]
  push_cast
  ring_nf

/-! ### The block law

`RMF.gaussianPairLaw_conv` iterated over a `Finset`.  This is what names the Gaussian side of the
two-point comparison: the Lindeberg telescope leaves a **sum** of per-prime pairs, and
`RMF.le_measure_box_of_gaussian_pair_of_third_moment` asks for that sum's law.

The empty case needs `gaussianPairLaw 0 0 0 0 0 = δ₀`, which is true for a slightly amusing reason:
at `V₁ = 0` the slope `pairSlope 0 0 = 0/0` is `0` and the residual standard deviation
`√(pairResidVar 0 0 0)` is `0`, so the regression map collapses to `z ↦ (z.1, 0)` and the base's
first factor is already `δ₀`.  Lean's `x/0 = 0` is doing real work here, and the statement would be
false in a convention where it were not. -/

lemma gaussianPairLaw_zero : gaussianPairLaw 0 0 0 0 0 = Measure.dirac 0 := by
  have hslope : pairSlope (0 : ℝ) 0 = 0 := by rw [pairSlope, div_zero]
  have hresid : pairResidVar (0 : ℝ) 0 0 = 0 := by rw [pairResidVar]; norm_num
  rw [gaussianPairLaw, hslope, hresid, Real.sqrt_zero, Real.toNNReal_zero,
    gaussianReal_zero_var, Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : (fun z : ℝ × ℝ => ((0 : ℝ) + z.1,
        (0 : ℝ) + 0 * z.1 + 0 * z.2)) ∘ (Prod.mk (0 : ℝ))
      = fun _ : ℝ => ((0 : ℝ), (0 : ℝ)) := by
    funext y
    simp
  rw [hcomp, Measure.map_const, measure_univ, one_smul]
  rfl

theorem map_sum_eq_gaussianPairLaw {ι Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {G : ι → Ω' → ℝ × ℝ} {m₁ m₂ V₁ V₂ cv : ι → ℝ}
    (hGm : ∀ i, Measurable (G i)) (hGi : iIndepFun G Q)
    (hlaw : ∀ i, Q.map (G i) = gaussianPairLaw (m₁ i) (m₂ i) (V₁ i) (V₂ i) (cv i))
    (hV₁ : ∀ i, 0 ≤ V₁ i) (hV₂ : ∀ i, 0 ≤ V₂ i) (hCS : ∀ i, cv i ^ 2 ≤ V₁ i * V₂ i)
    (t : Finset ι) :
    Q.map (fun ω => ∑ i ∈ t, G i ω)
      = gaussianPairLaw (∑ i ∈ t, m₁ i) (∑ i ∈ t, m₂ i) (∑ i ∈ t, V₁ i) (∑ i ∈ t, V₂ i)
          (∑ i ∈ t, cv i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [gaussianPairLaw_zero, Measure.map_const, measure_univ, one_smul]
  | insert a s ha ih =>
      have hsm : Measurable (fun ω => ∑ i ∈ s, G i ω) :=
        Finset.measurable_sum s fun i _ => hGm i
      have hfs : (fun ω => ∑ i ∈ s, G i ω) = ∑ j ∈ s, G j := by
        funext ω
        simp
      have hind : IndepFun (G a) (fun ω => ∑ i ∈ s, G i ω) Q := by
        rw [hfs]
        exact (hGi.indepFun_finsetSum_of_notMem hGm ha).symm
      have hfun : (fun ω => ∑ i ∈ insert a s, G i ω)
          = (fun ω => G a ω) + fun ω => ∑ i ∈ s, G i ω := by
        funext ω
        simp [Finset.sum_insert ha]
      rw [hfun, hind.map_add_eq_map_conv_map (hGm a) hsm, hlaw a, ih,
        Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
        Finset.sum_insert ha, Finset.sum_insert ha]
      exact gaussianPairLaw_conv (hV₁ a) (hV₂ a) (hCS a)
        (Finset.sum_nonneg fun i _ => hV₁ i) (Finset.sum_nonneg fun i _ => hV₂ i)
        (sum_cauchy_schwarz hV₁ hV₂ hCS s)

/-! ### The marginals, and their third absolute moments

A dividend of the last section.  `ProbabilityTheory.IsGaussian` carries
`map_eq_gaussianReal` as a *field*: the pushforward under any dual functional is the real Gaussian
with the matching mean and variance.  At `L = fst` and `L = snd` that identifies both marginals —
with no convolution argument in sight, even though the second marginal's variance
`ρ²V₁ + s² = V₂` is exactly what a convolution would have had to compute.

The two-point swap charges third absolute moments on the Gaussian side, and with the marginals in
hand those are the one-dimensional `RMF.integral_abs_cube_gaussianReal_le` read twice. -/

lemma map_fst_gaussianPairLaw {m₁ m₂ V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂)
    (hCS : c ^ 2 ≤ V₁ * V₂) :
    (gaussianPairLaw m₁ m₂ V₁ V₂ c).map Prod.fst = gaussianReal m₁ V₁.toNNReal := by
  have h := IsGaussian.map_eq_gaussianReal (μ := gaussianPairLaw m₁ m₂ V₁ V₂ c)
    (ContinuousLinearMap.fst ℝ ℝ ℝ)
  rw [integral_dual_gaussianPairLaw hV₁, variance_dual_gaussianPairLaw hV₁ hV₂ hCS] at h
  simpa using h

lemma map_snd_gaussianPairLaw {m₁ m₂ V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂)
    (hCS : c ^ 2 ≤ V₁ * V₂) :
    (gaussianPairLaw m₁ m₂ V₁ V₂ c).map Prod.snd = gaussianReal m₂ V₂.toNNReal := by
  have h := IsGaussian.map_eq_gaussianReal (μ := gaussianPairLaw m₁ m₂ V₁ V₂ c)
    (ContinuousLinearMap.snd ℝ ℝ ℝ)
  rw [integral_dual_gaussianPairLaw hV₁, variance_dual_gaussianPairLaw hV₁ hV₂ hCS] at h
  simpa using h

lemma integrable_abs_cube_fst_gaussianPairLaw {m₁ m₂ V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁)
    (hV₂ : 0 ≤ V₂) (hCS : c ^ 2 ≤ V₁ * V₂) :
    Integrable (fun w : ℝ × ℝ => |w.1| ^ 3) (gaussianPairLaw m₁ m₂ V₁ V₂ c) :=
  integrable_abs_cube_of_hasLaw_gaussianReal measurable_fst
    (map_fst_gaussianPairLaw hV₁ hV₂ hCS)

lemma integrable_abs_cube_snd_gaussianPairLaw {m₁ m₂ V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁)
    (hV₂ : 0 ≤ V₂) (hCS : c ^ 2 ≤ V₁ * V₂) :
    Integrable (fun w : ℝ × ℝ => |w.2| ^ 3) (gaussianPairLaw m₁ m₂ V₁ V₂ c) :=
  integrable_abs_cube_of_hasLaw_gaussianReal measurable_snd
    (map_snd_gaussianPairLaw hV₁ hV₂ hCS)

/-! ### The collar, in law form

The block Gaussian is a **sum** of per-prime pairs, and `RMF.gaussianPairLaw_conv` names its law
without ever putting it back in regression form.  So the collar is bounded here against the law,
where the marginals of the previous section make it three lines: the collar of a box is a union of
two one-coordinate slabs, and each slab is a one-dimensional Gaussian collar.  This is the form the
block-level comparison uses. -/

lemma toReal_measure_collar_gaussianPairLaw_le {m₁ m₂ V₁ V₂ c : ℝ} (hV₁ : 0 ≤ V₁)
    (hV₂ : 0 ≤ V₂) (hCS : c ^ 2 ≤ V₁ * V₂) (h₁ : V₁.toNNReal ≠ 0) (h₂ : V₂.toNNReal ≠ 0)
    (u₁ v₁ u₂ v₂ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (gaussianPairLaw m₁ m₂ V₁ V₂ c (smoothCollar δ u₁ v₁ ×ˢ (Set.univ : Set ℝ)
        ∪ (Set.univ : Set ℝ) ×ˢ smoothCollar δ u₂ v₂)).toReal
      ≤ 4 * δ / Real.sqrt (2 * Real.pi * V₁) + 4 * δ / Real.sqrt (2 * Real.pi * V₂) := by
  set μ := gaussianPairLaw m₁ m₂ V₁ V₂ c with hμd
  have hCl₁ : MeasurableSet (smoothCollar δ u₁ v₁) := measurableSet_Icc.union measurableSet_Icc
  have hCl₂ : MeasurableSet (smoothCollar δ u₂ v₂) := measurableSet_Icc.union measurableSet_Icc
  have hset : (smoothCollar δ u₁ v₁ ×ˢ (Set.univ : Set ℝ)
      ∪ (Set.univ : Set ℝ) ×ˢ smoothCollar δ u₂ v₂)
      = Prod.fst ⁻¹' smoothCollar δ u₁ v₁ ∪ Prod.snd ⁻¹' smoothCollar δ u₂ v₂ := by
    ext w
    simp
  have hA : μ (Prod.fst ⁻¹' smoothCollar δ u₁ v₁)
      = gaussianReal m₁ V₁.toNNReal (smoothCollar δ u₁ v₁) := by
    rw [← Measure.map_apply measurable_fst hCl₁, hμd, map_fst_gaussianPairLaw hV₁ hV₂ hCS]
  have hB : μ (Prod.snd ⁻¹' smoothCollar δ u₂ v₂)
      = gaussianReal m₂ V₂.toNNReal (smoothCollar δ u₂ v₂) := by
    rw [← Measure.map_apply measurable_snd hCl₂, hμd, map_snd_gaussianPairLaw hV₁ hV₂ hCS]
  have hle := measure_union_le (μ := μ) (Prod.fst ⁻¹' smoothCollar δ u₁ v₁)
    (Prod.snd ⁻¹' smoothCollar δ u₂ v₂)
  rw [hset]
  refine le_trans (ENNReal.toReal_mono (ENNReal.add_ne_top.2
    ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hle) ?_
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hA, hB]
  have h₁' : (gaussianReal m₁ V₁.toNNReal (smoothCollar δ u₁ v₁)).toReal
      ≤ 4 * δ / Real.sqrt (2 * Real.pi * V₁) := by
    have h := measure_collar_gaussianReal_le m₁ h₁ u₁ v₁ hδ
    rw [Real.coe_toNNReal V₁ hV₁] at h
    exact h
  have h₂' : (gaussianReal m₂ V₂.toNNReal (smoothCollar δ u₂ v₂)).toReal
      ≤ 4 * δ / Real.sqrt (2 * Real.pi * V₂) := by
    have h := measure_collar_gaussianReal_le m₂ h₂ u₂ v₂ hδ
    rw [Real.coe_toNNReal V₂ hV₂] at h
    exact h
  linarith

/-! ### The matching, at the raw moments

`RMF.quadMonomial` names the five quantities the bivariate swap matches: both means, both second
moments and the mixed one.  Those are *raw* moments, while `RMF.gaussianPairLaw` is parameterised
by *central* ones, so the matching is a change of variables — `Vᵢ = sᵢ - μᵢ²`, `c = s₁₂ - μ₁μ₂`
— valid exactly when the resulting matrix is positive semidefinite.

**That condition is not a promissory note.**  For a family that really is the moment family of a
random pair it is Cauchy–Schwarz, and `RMF.psd_of_integrable_pair` below proves it, so the
matching is never asked for at a target it cannot meet. -/

/-- The integral of a quadratic form in a pair, term by term.  The analogue of
`RMF.integral_quad_gaussianPairBase` for an arbitrary integrable pair. -/
private lemma integral_quad_pair {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : Ω → ℝ × ℝ}
    (h₁ : Integrable (fun ω => (ξ ω).1) P) (h₂ : Integrable (fun ω => (ξ ω).2) P)
    (h₁₁ : Integrable (fun ω => (ξ ω).1 * (ξ ω).1) P)
    (h₁₂ : Integrable (fun ω => (ξ ω).1 * (ξ ω).2) P)
    (h₂₂ : Integrable (fun ω => (ξ ω).2 * (ξ ω).2) P) (a b d e f g : ℝ) :
    (∫ ω, (a + b * (ξ ω).1 + d * (ξ ω).2 + e * ((ξ ω).1 * (ξ ω).1)
        + f * ((ξ ω).1 * (ξ ω).2) + g * ((ξ ω).2 * (ξ ω).2)) ∂P)
      = a + b * (∫ ω, (ξ ω).1 ∂P) + d * (∫ ω, (ξ ω).2 ∂P)
          + e * (∫ ω, (ξ ω).1 * (ξ ω).1 ∂P) + f * (∫ ω, (ξ ω).1 * (ξ ω).2 ∂P)
          + g * (∫ ω, (ξ ω).2 * (ξ ω).2 ∂P) := by
  have i0 : Integrable (fun _ : Ω => a) P := integrable_const a
  have i1 : Integrable (fun ω => b * (ξ ω).1) P := h₁.const_mul b
  have i2 : Integrable (fun ω => d * (ξ ω).2) P := h₂.const_mul d
  have i3 : Integrable (fun ω => e * ((ξ ω).1 * (ξ ω).1)) P := h₁₁.const_mul e
  have i4 : Integrable (fun ω => f * ((ξ ω).1 * (ξ ω).2)) P := h₁₂.const_mul f
  have i5 : Integrable (fun ω => g * ((ξ ω).2 * (ξ ω).2)) P := h₂₂.const_mul g
  have j1 : Integrable (fun ω => a + b * (ξ ω).1) P := i0.add i1
  have j2 : Integrable (fun ω => a + b * (ξ ω).1 + d * (ξ ω).2) P := j1.add i2
  have j3 : Integrable
      (fun ω => a + b * (ξ ω).1 + d * (ξ ω).2 + e * ((ξ ω).1 * (ξ ω).1)) P := j2.add i3
  have j4 : Integrable (fun ω => a + b * (ξ ω).1 + d * (ξ ω).2
      + e * ((ξ ω).1 * (ξ ω).1) + f * ((ξ ω).1 * (ξ ω).2)) P := j3.add i4
  rw [integral_add j4 i5, integral_add j3 i4, integral_add j2 i3, integral_add j1 i2,
    integral_add i0 i1, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const]
  simp

/-- **Cauchy–Schwarz for the raw moments of a random pair.**  The covariance matrix of an
integrable pair is positive semidefinite.

The second conjunct is the discriminant of `t ↦ E(t(X-μ₁) + (Y-μ₂))²`, a quadratic in `t` that is
nonnegative because it is the integral of a square. -/
theorem psd_of_integrable_pair {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : Ω → ℝ × ℝ}
    (h₁ : Integrable (fun ω => (ξ ω).1) P) (h₂ : Integrable (fun ω => (ξ ω).2) P)
    (h₁₁ : Integrable (fun ω => (ξ ω).1 * (ξ ω).1) P)
    (h₁₂ : Integrable (fun ω => (ξ ω).1 * (ξ ω).2) P)
    (h₂₂ : Integrable (fun ω => (ξ ω).2 * (ξ ω).2) P) :
    0 ≤ (∫ ω, (ξ ω).1 * (ξ ω).1 ∂P) - (∫ ω, (ξ ω).1 ∂P) ^ 2 ∧
      0 ≤ (∫ ω, (ξ ω).2 * (ξ ω).2 ∂P) - (∫ ω, (ξ ω).2 ∂P) ^ 2 ∧
      ((∫ ω, (ξ ω).1 * (ξ ω).2 ∂P) - (∫ ω, (ξ ω).1 ∂P) * (∫ ω, (ξ ω).2 ∂P)) ^ 2
        ≤ ((∫ ω, (ξ ω).1 * (ξ ω).1 ∂P) - (∫ ω, (ξ ω).1 ∂P) ^ 2)
          * ((∫ ω, (ξ ω).2 * (ξ ω).2 ∂P) - (∫ ω, (ξ ω).2 ∂P) ^ 2) := by
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : ℝ, m₁ = ∫ ω, (ξ ω).1 ∂P := ⟨_, rfl⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m₂ : ℝ, m₂ = ∫ ω, (ξ ω).2 ∂P := ⟨_, rfl⟩
  -- the quadratic `t ↦ E(t(X-m₁) + (Y-m₂))²`, evaluated
  have hquad : ∀ t : ℝ,
      ((∫ ω, (ξ ω).1 * (ξ ω).1 ∂P) - m₁ ^ 2) * (t * t)
        + (2 * ((∫ ω, (ξ ω).1 * (ξ ω).2 ∂P) - m₁ * m₂)) * t
        + ((∫ ω, (ξ ω).2 * (ξ ω).2 ∂P) - m₂ ^ 2)
      = ∫ ω, (t * ((ξ ω).1 - m₁) + ((ξ ω).2 - m₂)) ^ 2 ∂P := by
    intro t
    have hpt : ∀ ω, (t * ((ξ ω).1 - m₁) + ((ξ ω).2 - m₂)) ^ 2
        = (t * m₁ + m₂) ^ 2 + (-(2 * (t * m₁ + m₂) * t)) * (ξ ω).1
          + (-(2 * (t * m₁ + m₂))) * (ξ ω).2 + (t * t) * ((ξ ω).1 * (ξ ω).1)
          + (2 * t) * ((ξ ω).1 * (ξ ω).2) + 1 * ((ξ ω).2 * (ξ ω).2) := by
      intro ω; ring
    simp_rw [hpt]
    rw [integral_quad_pair h₁ h₂ h₁₁ h₁₂ h₂₂, ← hm₁, ← hm₂]
    ring
  have hnn : ∀ t : ℝ,
      0 ≤ ((∫ ω, (ξ ω).1 * (ξ ω).1 ∂P) - m₁ ^ 2) * (t * t)
        + (2 * ((∫ ω, (ξ ω).1 * (ξ ω).2 ∂P) - m₁ * m₂)) * t
        + ((∫ ω, (ξ ω).2 * (ξ ω).2 ∂P) - m₂ ^ 2) := by
    intro t
    rw [hquad t]
    exact integral_nonneg fun ω => sq_nonneg _
  -- the two variances are integrals of squares
  have hvar₁ : (∫ ω, ((ξ ω).1 - m₁) ^ 2 ∂P) = (∫ ω, (ξ ω).1 * (ξ ω).1 ∂P) - m₁ ^ 2 := by
    have hpt : ∀ ω, ((ξ ω).1 - m₁) ^ 2
        = m₁ ^ 2 + (-(2 * m₁)) * (ξ ω).1 + 0 * (ξ ω).2 + 1 * ((ξ ω).1 * (ξ ω).1)
          + 0 * ((ξ ω).1 * (ξ ω).2) + 0 * ((ξ ω).2 * (ξ ω).2) := by
      intro ω; ring
    simp_rw [hpt]
    rw [integral_quad_pair h₁ h₂ h₁₁ h₁₂ h₂₂, ← hm₁]
    ring
  have hvar₂ : (∫ ω, ((ξ ω).2 - m₂) ^ 2 ∂P) = (∫ ω, (ξ ω).2 * (ξ ω).2 ∂P) - m₂ ^ 2 := by
    have hpt : ∀ ω, ((ξ ω).2 - m₂) ^ 2
        = m₂ ^ 2 + 0 * (ξ ω).1 + (-(2 * m₂)) * (ξ ω).2 + 0 * ((ξ ω).1 * (ξ ω).1)
          + 0 * ((ξ ω).1 * (ξ ω).2) + 1 * ((ξ ω).2 * (ξ ω).2) := by
      intro ω; ring
    simp_rw [hpt]
    rw [integral_quad_pair h₁ h₂ h₁₁ h₁₂ h₂₂, ← hm₂]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [← hm₁, ← hvar₁]
    exact integral_nonneg fun ω => sq_nonneg _
  · rw [← hm₂, ← hvar₂]
    exact integral_nonneg fun ω => sq_nonneg _
  · have hd := discrim_le_zero hnn
    rw [discrim] at hd
    rw [← hm₁, ← hm₂]
    nlinarith [hd]

/-- **The matched Gaussian pair family, at the raw moments.**  Given target raw moments
`(μ₁, μ₂, s₁, s₁₂, s₂)` whose covariance matrix is positive semidefinite, an independent family of
bivariate Gaussians whose five `RMF.quadMonomial` integrals are exactly those.

This is the form `RMF.abs_integral_swap_le` consumes, which asks for equality of the five raw
moments. -/
theorem exists_gaussian_pair_matching_quadMonomial {ι : Type u} (μ₁ μ₂ s₁ s₁₂ s₂ : ι → ℝ)
    (hV₁ : ∀ i, 0 ≤ s₁ i - μ₁ i ^ 2) (hV₂ : ∀ i, 0 ≤ s₂ i - μ₂ i ^ 2)
    (hCS : ∀ i, (s₁₂ i - μ₁ i * μ₂ i) ^ 2 ≤ (s₁ i - μ₁ i ^ 2) * (s₂ i - μ₂ i ^ 2)) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ι → Ω' → ℝ × ℝ),
      IsProbabilityMeasure Q ∧ (∀ i, Measurable (N i)) ∧ iIndepFun N Q ∧
        (∀ i, Q.map (N i) = gaussianPairLaw (μ₁ i) (μ₂ i) (s₁ i - μ₁ i ^ 2)
          (s₂ i - μ₂ i ^ 2) (s₁₂ i - μ₁ i * μ₂ i)) ∧
        (∀ i, (∫ ω, quadMonomial 0 (N i ω) ∂Q) = μ₁ i) ∧
        (∀ i, (∫ ω, quadMonomial 1 (N i ω) ∂Q) = μ₂ i) ∧
        (∀ i, (∫ ω, quadMonomial 2 (N i ω) ∂Q) = s₁ i) ∧
        (∀ i, (∫ ω, quadMonomial 3 (N i ω) ∂Q) = s₁₂ i) ∧
        (∀ i, (∫ ω, quadMonomial 4 (N i ω) ∂Q) = s₂ i) := by
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw⟩ :=
    exists_gaussian_pair_matching_moments μ₁ μ₂ (fun i => s₁ i - μ₁ i ^ 2)
      (fun i => s₂ i - μ₂ i ^ 2) (fun i => s₁₂ i - μ₁ i * μ₂ i)
  have hmap : ∀ (i : ι) (g : ℝ × ℝ → ℝ), Measurable g →
      (∫ ω, g (N i ω) ∂Q) = ∫ z, g z ∂(Q.map (N i)) := by
    intro i g hg
    rw [integral_map (hNm i).aemeasurable hg.aestronglyMeasurable]
  refine ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [show quadMonomial 0 = fun z : ℝ × ℝ => z.1 from rfl,
      hmap i (fun z : ℝ × ℝ => z.1) measurable_fst, hNlaw i,
      integral_fst_gaussianPairLaw (hV₁ i)]
  · intro i
    rw [show quadMonomial 1 = fun z : ℝ × ℝ => z.2 from rfl,
      hmap i (fun z : ℝ × ℝ => z.2) measurable_snd, hNlaw i,
      integral_snd_gaussianPairLaw (hV₁ i)]
  · intro i
    rw [show quadMonomial 2 = fun z : ℝ × ℝ => z.1 * z.1 from rfl,
      hmap i (fun z : ℝ × ℝ => z.1 * z.1) (measurable_fst.mul measurable_fst), hNlaw i,
      integral_fst_sq_gaussianPairLaw (hV₁ i)]
    ring
  · intro i
    rw [show quadMonomial 3 = fun z : ℝ × ℝ => z.1 * z.2 from rfl,
      hmap i (fun z : ℝ × ℝ => z.1 * z.2) (measurable_fst.mul measurable_snd), hNlaw i,
      integral_fst_mul_snd_gaussianPairLaw (hV₁ i) (hCS i)]
    ring
  · intro i
    rw [show quadMonomial 4 = fun z : ℝ × ℝ => z.2 * z.2 from rfl,
      hmap i (fun z : ℝ × ℝ => z.2 * z.2) (measurable_snd.mul measurable_snd), hNlaw i,
      integral_snd_sq_gaussianPairLaw (hV₁ i) (hV₂ i) (hCS i)]
    ring

end RMF
