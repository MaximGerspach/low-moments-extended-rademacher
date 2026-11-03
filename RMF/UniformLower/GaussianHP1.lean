/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.BarrierSupermartingale

/-!
# Gaussian tools for the window's first moment

Two elementary tools for the Gaussian side of the first moment on the window:

* **Chebyshev's integral inequality** (`RMF.mul_integral_le_integral_mul_of_antitone`): two
  antitone bounded functions are positively correlated under any probability measure on `ℝ`;
* **the exponential potential** `min(1, e^{t(S_k + D_k - z)})` of a drifted walk, frozen at `1`
  once the walk has exceeded `z` (`RMF.frozenPotential`); the exponential maximal bound built on
  it is `RMF.IsGaussianWalk.measureReal_survivalSet_compl_le_exp_sum`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

/-! ### Chebyshev's integral inequality -/

/-- **Chebyshev's integral inequality**: two antitone bounded measurable functions are positively
correlated under any probability measure on `ℝ`.  From `∫∫(f x - f y)(g x - g y) ≥ 0`. -/
theorem mul_integral_le_integral_mul_of_antitone {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f g : ℝ → ℝ} (hf : Antitone f) (hg : Antitone g) (hfm : Measurable f) (hgm : Measurable g)
    {Cf Cg : ℝ} (hfb : ∀ x, |f x| ≤ Cf) (hgb : ∀ x, |g x| ≤ Cg) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  have hCf : 0 ≤ Cf := le_trans (abs_nonneg _) (hfb 0)
  -- the four product integrals
  have h11 : ∫ p : ℝ × ℝ, f p.1 * g p.1 ∂(μ.prod μ) = ∫ x, f x * g x ∂μ := by
    have := integral_prod_mul (μ := μ) (ν := μ) (fun x => f x * g x) (fun _ => (1 : ℝ))
    simpa using this
  have h22 : ∫ p : ℝ × ℝ, f p.2 * g p.2 ∂(μ.prod μ) = ∫ x, f x * g x ∂μ := by
    have := integral_prod_mul (μ := μ) (ν := μ) (fun _ => (1 : ℝ)) (fun x => f x * g x)
    simpa using this
  have h12 : ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂(μ.prod μ) = (∫ x, f x ∂μ) * ∫ x, g x ∂μ :=
    integral_prod_mul f g
  have h21 : ∫ p : ℝ × ℝ, f p.2 * g p.1 ∂(μ.prod μ) = (∫ x, f x ∂μ) * ∫ x, g x ∂μ := by
    have := integral_prod_mul (μ := μ) (ν := μ) g f
    rw [mul_comm (∫ x, g x ∂μ)] at this
    simpa [mul_comm] using this
  -- integrability on the product
  have hi : ∀ (u v : ℝ × ℝ → ℝ), Measurable u → Measurable v →
      Integrable (fun p : ℝ × ℝ => f (u p) * g (v p)) (μ.prod μ) := by
    intro u v hu hv
    refine Integrable.of_bound ((hfm.comp hu).mul (hgm.comp hv)).aestronglyMeasurable (Cf * Cg)
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hfb _) (hgb _) (abs_nonneg _) hCf
  have i11 := hi Prod.fst Prod.fst measurable_fst measurable_fst
  have i12 := hi Prod.fst Prod.snd measurable_fst measurable_snd
  have i21 := hi Prod.snd Prod.fst measurable_snd measurable_fst
  have i22 := hi Prod.snd Prod.snd measurable_snd measurable_snd
  -- the double integral of the nonnegative product
  have hH0 : ∀ p : ℝ × ℝ, 0 ≤ (f p.1 - f p.2) * (g p.1 - g p.2) := by
    intro p
    rcases le_total p.1 p.2 with h | h
    · exact mul_nonneg (sub_nonneg.2 (hf h)) (sub_nonneg.2 (hg h))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hf h)) (sub_nonpos.2 (hg h))
  have hexp : (fun p : ℝ × ℝ => (f p.1 - f p.2) * (g p.1 - g p.2))
      = fun p => f p.1 * g p.1 - f p.1 * g p.2 - f p.2 * g p.1 + f p.2 * g p.2 := by
    funext p
    ring
  have hint := integral_nonneg (μ := μ.prod μ)
    (f := fun p : ℝ × ℝ => (f p.1 - f p.2) * (g p.1 - g p.2)) fun p => hH0 p
  rw [hexp] at hint
  have e1 : ∫ p : ℝ × ℝ, (f p.1 * g p.1 - f p.1 * g p.2 - f p.2 * g p.1 + f p.2 * g p.2)
        ∂(μ.prod μ)
      = ∫ p : ℝ × ℝ, (f p.1 * g p.1 - f p.1 * g p.2 - f p.2 * g p.1) ∂(μ.prod μ)
        + ∫ p : ℝ × ℝ, f p.2 * g p.2 ∂(μ.prod μ) :=
    integral_add ((i11.sub i12).sub i21) i22
  have e2 : ∫ p : ℝ × ℝ, (f p.1 * g p.1 - f p.1 * g p.2 - f p.2 * g p.1) ∂(μ.prod μ)
      = ∫ p : ℝ × ℝ, (f p.1 * g p.1 - f p.1 * g p.2) ∂(μ.prod μ)
        - ∫ p : ℝ × ℝ, f p.2 * g p.1 ∂(μ.prod μ) :=
    integral_sub (i11.sub i12) i21
  have e3 : ∫ p : ℝ × ℝ, (f p.1 * g p.1 - f p.1 * g p.2) ∂(μ.prod μ)
      = ∫ p : ℝ × ℝ, f p.1 * g p.1 ∂(μ.prod μ) - ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂(μ.prod μ) :=
    integral_sub i11 i12
  rw [e1, e2, e3, h11, h12, h21, h22] at hint
  linarith

/-! ### The exponential potential -/

/-- **The exponential potential** `min(1, e^{t(y - z)})`. -/
noncomputable def expPotential (t z y : ℝ) : ℝ := min 1 (Real.exp (t * (y - z)))

lemma expPotential_nonneg (t z y : ℝ) : 0 ≤ expPotential t z y :=
  le_min zero_le_one (Real.exp_pos _).le

lemma expPotential_le_one (t z y : ℝ) : expPotential t z y ≤ 1 := min_le_left _ _

lemma abs_expPotential_le_one (t z y : ℝ) : |expPotential t z y| ≤ 1 := by
  rw [abs_of_nonneg (expPotential_nonneg t z y)]
  exact expPotential_le_one t z y

lemma measurable_expPotential (t z : ℝ) : Measurable (expPotential t z) :=
  measurable_const.min (Real.measurable_exp.comp (measurable_const.mul
    (measurable_id.sub measurable_const)))

/-- Past `z` the potential is `1`. -/
lemma expPotential_eq_one_of_lt {t z y : ℝ} (ht : 0 ≤ t) (h : z < y) :
    expPotential t z y = 1 :=
  min_eq_left (Real.one_le_exp (mul_nonneg ht (by linarith)))

/-! ### The walk -/

section Walk

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The cumulative drift `D_j = ∑_{m<j} d_m`. -/
noncomputable def driftSum (d : ℕ → ℝ) (j : ℕ) : ℝ := ∑ m ∈ Finset.range j, d m

/-- **The frozen potential**: `1` once the drifted walk `S_j + D_j` has exceeded `z`, else
`min(1, e^{t(S_k + D_k - z)})`. -/
noncomputable def frozenPotential (G : ℕ → Ω → ℝ) (d : ℕ → ℝ) (t z : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  (survivalSet G (fun j => z - driftSum d j) k)ᶜ.indicator (fun _ => (1 : ℝ)) ω
    + (survivalSet G (fun j => z - driftSum d j) k).indicator
        (fun ω => expPotential t z (walk G k ω + driftSum d k)) ω

end Walk

end RMF
