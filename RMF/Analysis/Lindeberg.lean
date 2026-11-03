/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Analysis.SmoothIndicator
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Probability.Independence.Integration

/-!
# The Lindeberg swap, analytic core

Every Gaussian comparison in the library — Hamdan's Lemma A.4 (arXiv:2604.05563) for the untilted
block increment, Harper's Lemma 3 (arXiv:1703.06654) for the one-point tilt, and his Lemma 7 for
the two-point tilt — is the same swap: replace one summand by a Gaussian with matching first and
second moments, and pay the third moment against the third derivative of a `C³` test function.

The test function is always a **product** `ψ(y₁, y₂) = f(y₁)·g(y₂)` of two one-dimensional smoothed
windows, and that is what keeps the two-dimensional case cheap.  For such a `ψ`,

`s ↦ ψ(u + s·x) = f(u₁ + s x₁)·g(u₂ + s x₂)`

is a function of **one** real variable — a product of two one-dimensional composites — so its third
derivative is the Leibniz expansion of `RMF/Analysis/SmoothIndicator.lean` all over again, and
ordinary one-variable calculus suffices.  No `iteratedFDeriv`, no multivariate Taylor.
Specialised at `g ≡ 1` this is the one-dimensional swap.

## The constant

`RMF.abs_sub_taylor2_le` carries the constant `K` where Taylor would give `K/6`: its proof is the
mean-value inequality applied three times, not an integral form of the remainder.
-/

open Set

namespace RMF

/-! ### Third-order Taylor, with a crude constant -/

/-- **Third-order Taylor at `0`, evaluated at `1`, with the mean-value constant.**  If `h` carries a
chain of three derivatives and `|h₃| ≤ K`, then `h 1` agrees with its second-order expansion at `0`
to within `K`.

The constant is `K` rather than `K/6` because the proof is three applications of the mean-value
inequality rather than an integral remainder; see the module docstring. -/
lemma abs_sub_taylor2_le {h h₁ h₂ h₃ : ℝ → ℝ} {K : ℝ}
    (hd : ∀ x, HasDerivAt h (h₁ x) x) (hd₁ : ∀ x, HasDerivAt h₁ (h₂ x) x)
    (hd₂ : ∀ x, HasDerivAt h₂ (h₃ x) x) (hK : ∀ x, |h₃ x| ≤ K) :
    |h 1 - h 0 - h₁ 0 - h₂ 0 / 2| ≤ K := by
  have hK0 : (0 : ℝ) ≤ K := le_trans (abs_nonneg _) (hK 0)
  have hdR₁ : ∀ x, HasDerivAt (fun s : ℝ => h₁ s - h₁ 0 - s * h₂ 0) (h₂ x - h₂ 0) x := fun x =>
    (((hd₁ x).sub_const (h₁ 0)).sub ((hasDerivAt_id x).mul_const (h₂ 0))).congr_deriv (by ring)
  have hdR : ∀ x, HasDerivAt (fun s : ℝ => h s - h 0 - s * h₁ 0 - s ^ 2 / 2 * h₂ 0)
      (h₁ x - h₁ 0 - x * h₂ 0) x := fun x => by
    have hx2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2 * h₂ 0) (x * h₂ 0) x :=
      (((hasDerivAt_pow 2 x).div_const 2).mul_const (h₂ 0)).congr_deriv (by push_cast; ring)
    exact ((((hd x).sub_const (h 0)).sub ((hasDerivAt_id x).mul_const (h₁ 0))).sub
      hx2).congr_deriv (by ring)
  -- three mean-value steps, each losing a factor `x ≤ 1`
  have b₂ : ∀ x ∈ Icc (0 : ℝ) 1, |h₂ x - h₂ 0| ≤ K := by
    intro x hx
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := h₂) (f' := h₃) (C := K)
      (fun y _ => (hd₂ y).hasDerivWithinAt) (fun y _ => by simpa using hK y) x hx
    simp only [Real.norm_eq_abs, sub_zero] at hmv
    nlinarith [hx.1, hx.2, abs_nonneg (h₂ x - h₂ 0)]
  have b₁ : ∀ x ∈ Icc (0 : ℝ) 1, |h₁ x - h₁ 0 - x * h₂ 0| ≤ K := by
    intro x hx
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s : ℝ => h₁ s - h₁ 0 - s * h₂ 0) (f' := fun s => h₂ s - h₂ 0) (C := K)
      (fun y _ => (hdR₁ y).hasDerivWithinAt)
      (fun y hy => by simpa using b₂ y (Ico_subset_Icc_self hy)) x hx
    simp only [Real.norm_eq_abs, sub_self, zero_mul, sub_zero] at hmv
    nlinarith [hx.1, hx.2, abs_nonneg (h₁ x - h₁ 0 - x * h₂ 0)]
  have b₀ := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s : ℝ => h s - h 0 - s * h₁ 0 - s ^ 2 / 2 * h₂ 0)
    (f' := fun s => h₁ s - h₁ 0 - s * h₂ 0) (C := K)
    (fun y _ => (hdR y).hasDerivWithinAt)
    (fun y hy => by simpa using b₁ y (Ico_subset_Icc_self hy)) 1 (by norm_num)
  simp only [Real.norm_eq_abs, sub_self, zero_mul, sub_zero, one_mul, one_pow] at b₀
  have hform : |h 1 - h 0 - h₁ 0 - h₂ 0 / 2|
      = |h 1 - h 0 - h₁ 0 - 1 / 2 * h₂ 0 - (0 - 0 ^ 2 / 2 * h₂ 0)| := by congr 1; ring
  rw [hform]
  linarith [b₀]

/-! ### The affine composite -/

/-- Precomposition with `s ↦ a + s·α` multiplies the derivative by `α`. -/
lemma hasDerivAt_affine_comp {F F' : ℝ → ℝ} (hF : ∀ y, HasDerivAt F (F' y) y) (a α s : ℝ) :
    HasDerivAt (fun t : ℝ => F (a + t * α)) (F' (a + s * α) * α) s := by
  have hin : HasDerivAt (fun t : ℝ => a + t * α) α s := by
    simpa using ((hasDerivAt_id s).mul_const α).const_add a
  exact HasDerivAt.comp s (hF (a + s * α)) hin

/-! ### The product test function

`ψ = f ⊗ g` along the ray `s ↦ (a + sα, b + sβ)`.  Three product rules, each combining an affine
composite of `f` with one of `g`; the pattern is `RMF.hasDerivAt_deriv2_window` again. -/

/-- **Third-order Taylor for a product test function.**  With `ψ(y₁,y₂) = f(y₁)·g(y₂)`, the
difference between `ψ(a+α, b+β)` and its second-order expansion at `(a,b)` is controlled by the four
Leibniz terms of the third derivative.  The subtracted terms are `∇ψ(a,b)·(α,β)` and
`½(α,β)ᵀH(a,b)(α,β)`, written out so that a `HasDerivAt` chain is all that is needed; matching
first and second moments matches exactly those two. -/
theorem abs_taylor2_prod_le {f f₁ f₂ f₃ g g₁ g₂ g₃ : ℝ → ℝ} {M₀ M₁ M₂ M₃ N₀ N₁ N₂ N₃ : ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hg : ∀ x, HasDerivAt g (g₁ x) x) (hg₁ : ∀ x, HasDerivAt g₁ (g₂ x) x)
    (hg₂ : ∀ x, HasDerivAt g₂ (g₃ x) x)
    (hM₀ : ∀ x, |f x| ≤ M₀) (hM₁ : ∀ x, |f₁ x| ≤ M₁) (hM₂ : ∀ x, |f₂ x| ≤ M₂)
    (hM₃ : ∀ x, |f₃ x| ≤ M₃)
    (hN₀ : ∀ x, |g x| ≤ N₀) (hN₁ : ∀ x, |g₁ x| ≤ N₁) (hN₂ : ∀ x, |g₂ x| ≤ N₂)
    (hN₃ : ∀ x, |g₃ x| ≤ N₃) (a b α β : ℝ) :
    |f (a + α) * g (b + β) - f a * g b
        - (f₁ a * α * g b + f a * (g₁ b * β))
        - (f₂ a * α * α * g b + 2 * (f₁ a * α * (g₁ b * β)) + f a * (g₂ b * β * β)) / 2|
      ≤ M₃ * N₀ * |α| ^ 3 + 3 * (M₂ * N₁) * (|α| ^ 2 * |β|)
        + 3 * (M₁ * N₂) * (|α| * |β| ^ 2) + M₀ * N₃ * |β| ^ 3 := by
  have hM₀0 : (0 : ℝ) ≤ M₀ := le_trans (abs_nonneg _) (hM₀ 0)
  have hM₁0 : (0 : ℝ) ≤ M₁ := le_trans (abs_nonneg _) (hM₁ 0)
  have hM₂0 : (0 : ℝ) ≤ M₂ := le_trans (abs_nonneg _) (hM₂ 0)
  have hM₃0 : (0 : ℝ) ≤ M₃ := le_trans (abs_nonneg _) (hM₃ 0)
  have hN₀0 : (0 : ℝ) ≤ N₀ := le_trans (abs_nonneg _) (hN₀ 0)
  have hN₁0 : (0 : ℝ) ≤ N₁ := le_trans (abs_nonneg _) (hN₁ 0)
  have hN₂0 : (0 : ℝ) ≤ N₂ := le_trans (abs_nonneg _) (hN₂ 0)
  have hN₃0 : (0 : ℝ) ≤ N₃ := le_trans (abs_nonneg _) (hN₃ 0)
  -- the two affine composites, to three orders
  have hdA₀ : ∀ s : ℝ, HasDerivAt (fun t : ℝ => f (a + t * α))
      (f₁ (a + s * α) * α) s := fun s => hasDerivAt_affine_comp hf a α s
  have hdA₁ : ∀ s : ℝ, HasDerivAt (fun t : ℝ => f₁ (a + t * α) * α)
      (f₂ (a + s * α) * α * α) s := fun s =>
    ((hasDerivAt_affine_comp hf₁ a α s).mul_const α)
  have hdA₂ : ∀ s : ℝ, HasDerivAt (fun t : ℝ => f₂ (a + t * α) * α * α)
      (f₃ (a + s * α) * α * α * α) s := fun s =>
    (((hasDerivAt_affine_comp hf₂ a α s).mul_const α).mul_const α)
  have hdB₀ : ∀ s : ℝ, HasDerivAt (fun t : ℝ => g (b + t * β))
      (g₁ (b + s * β) * β) s := fun s => hasDerivAt_affine_comp hg b β s
  have hdB₁ : ∀ s : ℝ, HasDerivAt (fun t : ℝ => g₁ (b + t * β) * β)
      (g₂ (b + s * β) * β * β) s := fun s =>
    ((hasDerivAt_affine_comp hg₁ b β s).mul_const β)
  have hdB₂ : ∀ s : ℝ, HasDerivAt (fun t : ℝ => g₂ (b + t * β) * β * β)
      (g₃ (b + s * β) * β * β * β) s := fun s =>
    (((hasDerivAt_affine_comp hg₂ b β s).mul_const β).mul_const β)
  -- the ray, and its three derivatives by Leibniz
  have hd : ∀ s : ℝ, HasDerivAt (fun t : ℝ => f (a + t * α) * g (b + t * β))
      (f₁ (a + s * α) * α * g (b + s * β) + f (a + s * α) * (g₁ (b + s * β) * β)) s :=
    fun s => (hdA₀ s).mul (hdB₀ s)
  have hd₁ : ∀ s : ℝ, HasDerivAt
      (fun t : ℝ => f₁ (a + t * α) * α * g (b + t * β) + f (a + t * α) * (g₁ (b + t * β) * β))
      (f₂ (a + s * α) * α * α * g (b + s * β)
        + 2 * (f₁ (a + s * α) * α * (g₁ (b + s * β) * β))
        + f (a + s * α) * (g₂ (b + s * β) * β * β)) s := fun s =>
    (((hdA₁ s).mul (hdB₀ s)).add ((hdA₀ s).mul (hdB₁ s))).congr_deriv (by ring)
  have hd₂ : ∀ s : ℝ, HasDerivAt
      (fun t : ℝ => f₂ (a + t * α) * α * α * g (b + t * β)
        + 2 * (f₁ (a + t * α) * α * (g₁ (b + t * β) * β))
        + f (a + t * α) * (g₂ (b + t * β) * β * β))
      (f₃ (a + s * α) * α * α * α * g (b + s * β)
        + 3 * (f₂ (a + s * α) * α * α * (g₁ (b + s * β) * β))
        + 3 * (f₁ (a + s * α) * α * (g₂ (b + s * β) * β * β))
        + f (a + s * α) * (g₃ (b + s * β) * β * β * β)) s := fun s =>
    ((((hdA₂ s).mul (hdB₀ s)).add (((hdA₁ s).mul (hdB₁ s)).const_mul 2)).add
      ((hdA₀ s).mul (hdB₂ s))).congr_deriv (by ring)
  -- the pointwise bound on the third derivative
  have hK : ∀ s : ℝ, |f₃ (a + s * α) * α * α * α * g (b + s * β)
      + 3 * (f₂ (a + s * α) * α * α * (g₁ (b + s * β) * β))
      + 3 * (f₁ (a + s * α) * α * (g₂ (b + s * β) * β * β))
      + f (a + s * α) * (g₃ (b + s * β) * β * β * β)|
      ≤ M₃ * N₀ * |α| ^ 3 + 3 * (M₂ * N₁) * (|α| ^ 2 * |β|)
        + 3 * (M₁ * N₂) * (|α| * |β| ^ 2) + M₀ * N₃ * |β| ^ 3 := by
    intro s
    have e₁ : |f₃ (a + s * α) * α * α * α * g (b + s * β)| ≤ M₃ * N₀ * |α| ^ 3 := by
      simp only [abs_mul]
      calc |f₃ (a + s * α)| * |α| * |α| * |α| * |g (b + s * β)|
          ≤ M₃ * |α| * |α| * |α| * N₀ := by gcongr <;> [exact hM₃ _; exact hN₀ _]
        _ = M₃ * N₀ * |α| ^ 3 := by ring
    have e₂ : |3 * (f₂ (a + s * α) * α * α * (g₁ (b + s * β) * β))|
        ≤ 3 * (M₂ * N₁) * (|α| ^ 2 * |β|) := by
      simp only [abs_mul]
      calc |(3 : ℝ)| * (|f₂ (a + s * α)| * |α| * |α| * (|g₁ (b + s * β)| * |β|))
          ≤ |(3 : ℝ)| * (M₂ * |α| * |α| * (N₁ * |β|)) := by
            gcongr <;> [exact hM₂ _; exact hN₁ _]
        _ = 3 * (M₂ * N₁) * (|α| ^ 2 * |β|) := by
            rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]; ring
    have e₃ : |3 * (f₁ (a + s * α) * α * (g₂ (b + s * β) * β * β))|
        ≤ 3 * (M₁ * N₂) * (|α| * |β| ^ 2) := by
      simp only [abs_mul]
      calc |(3 : ℝ)| * (|f₁ (a + s * α)| * |α| * (|g₂ (b + s * β)| * |β| * |β|))
          ≤ |(3 : ℝ)| * (M₁ * |α| * (N₂ * |β| * |β|)) := by
            gcongr <;> [exact hM₁ _; exact hN₂ _]
        _ = 3 * (M₁ * N₂) * (|α| * |β| ^ 2) := by
            rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]; ring
    have e₄ : |f (a + s * α) * (g₃ (b + s * β) * β * β * β)| ≤ M₀ * N₃ * |β| ^ 3 := by
      simp only [abs_mul]
      calc |f (a + s * α)| * (|g₃ (b + s * β)| * |β| * |β| * |β|)
          ≤ M₀ * (N₃ * |β| * |β| * |β|) := by gcongr <;> [exact hM₀ _; exact hN₃ _]
        _ = M₀ * N₃ * |β| ^ 3 := by ring
    refine le_trans (abs_add_le _ _) ?_
    refine le_trans (add_le_add (abs_add_le _ _) le_rfl) ?_
    refine le_trans (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) ?_
    linarith
  have key := abs_sub_taylor2_le hd hd₁ hd₂ hK
  simp only [zero_mul, add_zero, one_mul] at key
  convert key using 2

/-! ### The swap

The probabilistic half.  Every term of the second-order Taylor polynomial has the form
`Φ(prefix) · m(summand)` with `Φ` bounded and `m` a monomial of degree at most two, so independence
factors it and the matched moments make the two sides agree.  The cost is the third-order remainder
on each side.
-/

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The prefix factors out.**  A functional of the prefix vector against a monomial in the
summand, when the two are independent.  Only measurability is needed:
`ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral` carries no integrability
hypothesis. -/
lemma integral_prefix_mul_summand {V : Ω → ℝ × ℝ × ℝ} {Z : Ω → ℝ × ℝ}
    (hind : IndepFun V Z μ) {Φ : ℝ × ℝ × ℝ → ℝ} {m : ℝ × ℝ → ℝ}
    (hΦ : Measurable Φ) (hm : Measurable m) (hV : Measurable V) (hZ : Measurable Z) :
    ∫ ω, Φ (V ω) * m (Z ω) ∂μ = (∫ ω, Φ (V ω) ∂μ) * ∫ ω, m (Z ω) ∂μ :=
  (hind.comp hΦ hm).integral_fun_mul_eq_mul_integral
    ((hΦ.comp hV).aestronglyMeasurable) ((hm.comp hZ).aestronglyMeasurable)

/-- **Agreeing to second order.**  If `F` and `G` each stay within `TF`, `TG` of comparison
functionals whose integrals agree, their integrals are within `∫TF + ∫TG`.

This is the shape of every Lindeberg swap: `F` and `G` are the test function against the two
summands, the comparison functionals are their common second-order Taylor polynomials, and the
integrals of those agree because the first and second moments are matched. -/
lemma abs_integral_sub_le_of_integral_eq {F G DF DG TF TG : Ω → ℝ}
    (hF : ∀ ω, |F ω - DF ω| ≤ TF ω) (hG : ∀ ω, |G ω - DG ω| ≤ TG ω)
    (hD : ∫ ω, DF ω ∂μ = ∫ ω, DG ω ∂μ)
    (hFi : Integrable F μ) (hGi : Integrable G μ)
    (hDFi : Integrable DF μ) (hDGi : Integrable DG μ)
    (hTFi : Integrable TF μ) (hTGi : Integrable TG μ) :
    |(∫ ω, F ω ∂μ) - ∫ ω, G ω ∂μ| ≤ (∫ ω, TF ω ∂μ) + ∫ ω, TG ω ∂μ := by
  have e1 : (∫ ω, F ω ∂μ) - ∫ ω, G ω ∂μ
      = (∫ ω, (F ω - DF ω) ∂μ) - ∫ ω, (G ω - DG ω) ∂μ := by
    rw [integral_sub hFi hDFi, integral_sub hGi hDGi, hD]; ring
  have h1 : |∫ ω, (F ω - DF ω) ∂μ| ≤ ∫ ω, TF ω ∂μ :=
    le_trans (abs_integral_le_integral_abs)
      (integral_mono (hFi.sub hDFi).abs hTFi (fun ω => hF ω))
  have h2 : |∫ ω, (G ω - DG ω) ∂μ| ≤ ∫ ω, TG ω ∂μ :=
    le_trans (abs_integral_le_integral_abs)
      (integral_mono (hGi.sub hDGi).abs hTGi (fun ω => hG ω))
  rw [e1]
  have htri := abs_add_le (∫ ω, (F ω - DF ω) ∂μ) (-∫ ω, (G ω - DG ω) ∂μ)
  rw [← sub_eq_add_neg, abs_neg] at htri
  linarith

/-- **Matched moments give matched second-order integrals.**  Coefficients on the prefix, monomials
on the summand: independence factors each term, and the matched moments do the rest. -/
lemma integral_sum_indep_eq {ι : Type*} [Fintype ι]
    {V : Ω → ℝ × ℝ × ℝ} {X Y : Ω → ℝ × ℝ} {Φ : ι → ℝ × ℝ × ℝ → ℝ} {m : ι → ℝ × ℝ → ℝ}
    (hindX : IndepFun V X μ) (hindY : IndepFun V Y μ)
    (hV : Measurable V) (hX : Measurable X) (hY : Measurable Y)
    (hΦ : ∀ i, Measurable (Φ i)) (hm : ∀ i, Measurable (m i))
    (hmom : ∀ i, ∫ ω, m i (X ω) ∂μ = ∫ ω, m i (Y ω) ∂μ)
    (hiX : ∀ i, Integrable (fun ω => Φ i (V ω) * m i (X ω)) μ)
    (hiY : ∀ i, Integrable (fun ω => Φ i (V ω) * m i (Y ω)) μ) :
    ∫ ω, ∑ i, Φ i (V ω) * m i (X ω) ∂μ = ∫ ω, ∑ i, Φ i (V ω) * m i (Y ω) ∂μ := by
  rw [integral_finsetSum _ (fun i _ => hiX i), integral_finsetSum _ (fun i _ => hiY i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_prefix_mul_summand hindX (hΦ i) (hm i) hV hX,
    integral_prefix_mul_summand hindY (hΦ i) (hm i) hV hY, hmom i]

/-! ### The swap, assembled

Three definitions keep the statement short: the five monomials of a quadratic in two variables, the
five coefficients they carry in the second-order Taylor polynomial of `C·(f ⊗ g)`, and the
third-order bound of `RMF.abs_taylor2_prod_le`.  Indexing the first two turns five moment
equalities into one hypothesis and ten integrability hypotheses into two.
-/

/-- The five monomials of a quadratic in two variables. -/
def quadMonomial : Fin 5 → ℝ × ℝ → ℝ
  | 0 => fun z => z.1
  | 1 => fun z => z.2
  | 2 => fun z => z.1 * z.1
  | 3 => fun z => z.1 * z.2
  | 4 => fun z => z.2 * z.2

lemma measurable_quadMonomial (i : Fin 5) : Measurable (quadMonomial i) := by
  fin_cases i <;> simp only [quadMonomial] <;> fun_prop

/-- The coefficients those monomials carry in the second-order Taylor polynomial of
`c·f(u₁)g(u₂)`, as a function of the prefix `(c, u₁, u₂)`. -/
noncomputable def taylorCoeff (f f₁ f₂ g g₁ g₂ : ℝ → ℝ) : Fin 5 → ℝ × ℝ × ℝ → ℝ
  | 0 => fun p => p.1 * (f₁ p.2.1 * g p.2.2)
  | 1 => fun p => p.1 * (f p.2.1 * g₁ p.2.2)
  | 2 => fun p => p.1 * (f₂ p.2.1 * g p.2.2) / 2
  | 3 => fun p => p.1 * (f₁ p.2.1 * g₁ p.2.2)
  | 4 => fun p => p.1 * (f p.2.1 * g₂ p.2.2) / 2

/-- The third-order bound of `RMF.abs_taylor2_prod_le`, as a function of the summand. -/
def lindebergBound (M₀ M₁ M₂ M₃ N₀ N₁ N₂ N₃ : ℝ) (z : ℝ × ℝ) : ℝ :=
  M₃ * N₀ * |z.1| ^ 3 + 3 * (M₂ * N₁) * (|z.1| ^ 2 * |z.2|)
    + 3 * (M₁ * N₂) * (|z.1| * |z.2| ^ 2) + M₀ * N₃ * |z.2| ^ 3

/-- **The one-step swap.**  Replace the summand `X` by `Y` inside the product test function
`ψ = f ⊗ g`, against a weight `C ∈ [0,1]`, where `(C, U₁, U₂)` is independent of `X` and of `Y`.
With the first and second moments matched (`hmom`, one equality per monomial) the cost is the
third-order bound on each side.  The weight lets a telescope run one summand at a time without
grouping coordinates; at `g ≡ 1` this is the one-dimensional swap. -/
theorem abs_integral_swap_le [IsProbabilityMeasure μ]
    {f f₁ f₂ f₃ g g₁ g₂ g₃ : ℝ → ℝ} {M₀ M₁ M₂ M₃ N₀ N₁ N₂ N₃ : ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hg : ∀ x, HasDerivAt g (g₁ x) x) (hg₁ : ∀ x, HasDerivAt g₁ (g₂ x) x)
    (hg₂ : ∀ x, HasDerivAt g₂ (g₃ x) x)
    (hM₀ : ∀ x, |f x| ≤ M₀) (hM₁ : ∀ x, |f₁ x| ≤ M₁) (hM₂ : ∀ x, |f₂ x| ≤ M₂)
    (hM₃ : ∀ x, |f₃ x| ≤ M₃)
    (hN₀ : ∀ x, |g x| ≤ N₀) (hN₁ : ∀ x, |g₁ x| ≤ N₁) (hN₂ : ∀ x, |g₂ x| ≤ N₂)
    (hN₃ : ∀ x, |g₃ x| ≤ N₃)
    {C U₁ U₂ : Ω → ℝ} {X Y : Ω → ℝ × ℝ}
    (hC0 : ∀ ω, 0 ≤ C ω) (hC1 : ∀ ω, C ω ≤ 1)
    (hCm : Measurable C) (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hindX : IndepFun (fun ω => (C ω, U₁ ω, U₂ ω)) X μ)
    (hindY : IndepFun (fun ω => (C ω, U₁ ω, U₂ ω)) Y μ)
    (hmX : ∀ i, Integrable (fun ω => quadMonomial i (X ω)) μ)
    (hmY : ∀ i, Integrable (fun ω => quadMonomial i (Y ω)) μ)
    (hmom : ∀ i, ∫ ω, quadMonomial i (X ω) ∂μ = ∫ ω, quadMonomial i (Y ω) ∂μ)
    (hTX : Integrable (fun ω => lindebergBound M₀ M₁ M₂ M₃ N₀ N₁ N₂ N₃ (X ω)) μ)
    (hTY : Integrable (fun ω => lindebergBound M₀ M₁ M₂ M₃ N₀ N₁ N₂ N₃ (Y ω)) μ) :
    |(∫ ω, C ω * (f (U₁ ω + (X ω).1) * g (U₂ ω + (X ω).2)) ∂μ)
        - ∫ ω, C ω * (f (U₁ ω + (Y ω).1) * g (U₂ ω + (Y ω).2)) ∂μ|
      ≤ (∫ ω, lindebergBound M₀ M₁ M₂ M₃ N₀ N₁ N₂ N₃ (X ω) ∂μ)
        + ∫ ω, lindebergBound M₀ M₁ M₂ M₃ N₀ N₁ N₂ N₃ (Y ω) ∂μ := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hf₁c : Continuous f₁ := continuous_iff_continuousAt.2 fun x => (hf₁ x).continuousAt
  have hf₂c : Continuous f₂ := continuous_iff_continuousAt.2 fun x => (hf₂ x).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have hg₁c : Continuous g₁ := continuous_iff_continuousAt.2 fun x => (hg₁ x).continuousAt
  have hg₂c : Continuous g₂ := continuous_iff_continuousAt.2 fun x => (hg₂ x).continuousAt
  have hV : Measurable (fun ω => (C ω, U₁ ω, U₂ ω)) := hCm.prodMk (hU₁.prodMk hU₂)
  have hM₀₀ : (0 : ℝ) ≤ M₀ := le_trans (abs_nonneg _) (hM₀ 0)
  have hM₁₀ : (0 : ℝ) ≤ M₁ := le_trans (abs_nonneg _) (hM₁ 0)
  have hM₂₀ : (0 : ℝ) ≤ M₂ := le_trans (abs_nonneg _) (hM₂ 0)
  have hN₀₀ : (0 : ℝ) ≤ N₀ := le_trans (abs_nonneg _) (hN₀ 0)
  have hN₁₀ : (0 : ℝ) ≤ N₁ := le_trans (abs_nonneg _) (hN₁ 0)
  have hN₂₀ : (0 : ℝ) ≤ N₂ := le_trans (abs_nonneg _) (hN₂ 0)
  have habsC : ∀ ω, |C ω| ≤ 1 := fun ω => by rw [abs_of_nonneg (hC0 ω)]; exact hC1 ω
  have hcoeffm : ∀ i, Measurable (taylorCoeff f f₁ f₂ g g₁ g₂ i) := by
    intro i; fin_cases i <;> simp only [taylorCoeff] <;> fun_prop
  -- each coefficient is bounded along the prefix, so each Taylor term is integrable
  have hcb : ∀ i, ∃ c : ℝ, ∀ ω, ‖taylorCoeff f f₁ f₂ g g₁ g₂ i (C ω, U₁ ω, U₂ ω)‖ ≤ c := by
    intro i
    fin_cases i
    · exact ⟨M₁ * N₀, fun ω => by
        simp only [taylorCoeff, Real.norm_eq_abs, abs_mul]
        calc |C ω| * (|f₁ (U₁ ω)| * |g (U₂ ω)|) ≤ 1 * (M₁ * N₀) := by
              gcongr <;> first | exact habsC _ | exact hM₁ _ | exact hN₀ _
          _ = M₁ * N₀ := by ring⟩
    · exact ⟨M₀ * N₁, fun ω => by
        simp only [taylorCoeff, Real.norm_eq_abs, abs_mul]
        calc |C ω| * (|f (U₁ ω)| * |g₁ (U₂ ω)|) ≤ 1 * (M₀ * N₁) := by
              gcongr <;> first | exact habsC _ | exact hM₀ _ | exact hN₁ _
          _ = M₀ * N₁ := by ring⟩
    · exact ⟨M₂ * N₀ / 2, fun ω => by
        simp only [taylorCoeff, Real.norm_eq_abs, abs_div, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        calc |C ω| * (|f₂ (U₁ ω)| * |g (U₂ ω)|) / 2 ≤ 1 * (M₂ * N₀) / 2 := by
              gcongr <;> first | exact habsC _ | exact hM₂ _ | exact hN₀ _
          _ = M₂ * N₀ / 2 := by ring⟩
    · exact ⟨M₁ * N₁, fun ω => by
        simp only [taylorCoeff, Real.norm_eq_abs, abs_mul]
        calc |C ω| * (|f₁ (U₁ ω)| * |g₁ (U₂ ω)|) ≤ 1 * (M₁ * N₁) := by
              gcongr <;> first | exact habsC _ | exact hM₁ _ | exact hN₁ _
          _ = M₁ * N₁ := by ring⟩
    · exact ⟨M₀ * N₂ / 2, fun ω => by
        simp only [taylorCoeff, Real.norm_eq_abs, abs_div, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        calc |C ω| * (|f (U₁ ω)| * |g₂ (U₂ ω)|) / 2 ≤ 1 * (M₀ * N₂) / 2 := by
              gcongr <;> first | exact habsC _ | exact hM₀ _ | exact hN₂ _
          _ = M₀ * N₂ / 2 := by ring⟩
  have hiX : ∀ i, Integrable (fun ω => taylorCoeff f f₁ f₂ g g₁ g₂ i (C ω, U₁ ω, U₂ ω)
      * quadMonomial i (X ω)) μ := fun i => by
    obtain ⟨c, hc⟩ := hcb i
    exact (hmX i).bdd_mul (((hcoeffm i).comp hV).aestronglyMeasurable)
      (Filter.Eventually.of_forall hc)
  have hiY : ∀ i, Integrable (fun ω => taylorCoeff f f₁ f₂ g g₁ g₂ i (C ω, U₁ ω, U₂ ω)
      * quadMonomial i (Y ω)) μ := fun i => by
    obtain ⟨c, hc⟩ := hcb i
    exact (hmY i).bdd_mul (((hcoeffm i).comp hV).aestronglyMeasurable)
      (Filter.Eventually.of_forall hc)
  -- the test function against either summand, and at the base point, is bounded
  have hbdd : ∀ (V₁ V₂ : Ω → ℝ), Measurable V₁ → Measurable V₂ →
      Integrable (fun ω => C ω * (f (V₁ ω) * g (V₂ ω))) μ := by
    intro V₁ V₂ h₁ h₂
    refine Integrable.mono' (integrable_const (M₀ * N₀))
      (by fun_prop) (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    calc |C ω| * (|f (V₁ ω)| * |g (V₂ ω)|) ≤ 1 * (M₀ * N₀) := by
          gcongr <;> first | exact habsC _ | exact hM₀ _ | exact hN₀ _
      _ = M₀ * N₀ := by ring
  have hFi := hbdd _ _ (hU₁.add (hXm.fst)) (hU₂.add (hXm.snd))
  have hGi := hbdd _ _ (hU₁.add (hYm.fst)) (hU₂.add (hYm.snd))
  have hbase := hbdd U₁ U₂ hU₁ hU₂
  -- the two comparison functionals
  have hDFi : Integrable (fun ω => C ω * (f (U₁ ω) * g (U₂ ω))
      + ∑ i, taylorCoeff f f₁ f₂ g g₁ g₂ i (C ω, U₁ ω, U₂ ω) * quadMonomial i (X ω)) μ :=
    hbase.add (integrable_finsetSum _ fun i _ => hiX i)
  have hDGi : Integrable (fun ω => C ω * (f (U₁ ω) * g (U₂ ω))
      + ∑ i, taylorCoeff f f₁ f₂ g g₁ g₂ i (C ω, U₁ ω, U₂ ω) * quadMonomial i (Y ω)) μ :=
    hbase.add (integrable_finsetSum _ fun i _ => hiY i)
  have hDeq : ∫ ω, (C ω * (f (U₁ ω) * g (U₂ ω))
        + ∑ i, taylorCoeff f f₁ f₂ g g₁ g₂ i (C ω, U₁ ω, U₂ ω) * quadMonomial i (X ω)) ∂μ
      = ∫ ω, (C ω * (f (U₁ ω) * g (U₂ ω))
        + ∑ i, taylorCoeff f f₁ f₂ g g₁ g₂ i (C ω, U₁ ω, U₂ ω) * quadMonomial i (Y ω)) ∂μ := by
    rw [integral_add hbase (integrable_finsetSum _ fun i _ => hiX i),
      integral_add hbase (integrable_finsetSum _ fun i _ => hiY i)]
    congr 1
    exact integral_sum_indep_eq hindX hindY hV hXm hYm hcoeffm measurable_quadMonomial hmom hiX hiY
  -- the pointwise bound, from the analytic core
  have hpt : ∀ (Z : Ω → ℝ × ℝ) (ω : Ω),
      |C ω * (f (U₁ ω + (Z ω).1) * g (U₂ ω + (Z ω).2))
        - (C ω * (f (U₁ ω) * g (U₂ ω))
          + ∑ i, taylorCoeff f f₁ f₂ g g₁ g₂ i (C ω, U₁ ω, U₂ ω) * quadMonomial i (Z ω))|
        ≤ lindebergBound M₀ M₁ M₂ M₃ N₀ N₁ N₂ N₃ (Z ω) := by
    intro Z ω
    have hcore := abs_taylor2_prod_le hf hf₁ hf₂ hg hg₁ hg₂ hM₀ hM₁ hM₂ hM₃ hN₀ hN₁ hN₂ hN₃
      (U₁ ω) (U₂ ω) (Z ω).1 (Z ω).2
    have hrw : C ω * (f (U₁ ω + (Z ω).1) * g (U₂ ω + (Z ω).2))
        - (C ω * (f (U₁ ω) * g (U₂ ω))
          + ∑ i, taylorCoeff f f₁ f₂ g g₁ g₂ i (C ω, U₁ ω, U₂ ω) * quadMonomial i (Z ω))
        = C ω * (f (U₁ ω + (Z ω).1) * g (U₂ ω + (Z ω).2) - f (U₁ ω) * g (U₂ ω)
            - (f₁ (U₁ ω) * (Z ω).1 * g (U₂ ω) + f (U₁ ω) * (g₁ (U₂ ω) * (Z ω).2))
            - (f₂ (U₁ ω) * (Z ω).1 * (Z ω).1 * g (U₂ ω)
              + 2 * (f₁ (U₁ ω) * (Z ω).1 * (g₁ (U₂ ω) * (Z ω).2))
              + f (U₁ ω) * (g₂ (U₂ ω) * (Z ω).2 * (Z ω).2)) / 2) := by
      simp only [Fin.sum_univ_five, taylorCoeff, quadMonomial]
      ring
    rw [hrw, abs_mul, abs_of_nonneg (hC0 ω)]
    have hb0 : (0 : ℝ) ≤ lindebergBound M₀ M₁ M₂ M₃ N₀ N₁ N₂ N₃ (Z ω) :=
      le_trans (abs_nonneg _) hcore
    calc C ω * |f (U₁ ω + (Z ω).1) * g (U₂ ω + (Z ω).2) - f (U₁ ω) * g (U₂ ω) - _ - _|
        ≤ 1 * lindebergBound M₀ M₁ M₂ M₃ N₀ N₁ N₂ N₃ (Z ω) := by
          gcongr
          · exact hC1 ω
          · exact hcore
      _ = lindebergBound M₀ M₁ M₂ M₃ N₀ N₁ N₂ N₃ (Z ω) := by ring
  exact abs_integral_sub_le_of_integral_eq (hpt X) (hpt Y) hDeq hFi hGi hDFi hDGi hTX hTY

/-- **The one-dimensional swap.**  `|∫ C·f(U + X) - ∫ C·f(U + Y)| ≤ M₃(∫|X|³ + ∫|Y|³)` when `X`
and `Y` have matching first and second moments and `(C, U)` is independent of each: this is
`RMF.abs_integral_swap_le` at `g ≡ 1`.  The classical constant is `M₃/6`; the `6` is given away in
`RMF.abs_sub_taylor2_le`.  `M₀, M₁, M₂` do not appear in the conclusion but make the Taylor
coefficients integrable along the prefix. -/
theorem abs_integral_swap_le_one [IsProbabilityMeasure μ]
    {f f₁ f₂ f₃ : ℝ → ℝ} {M₀ M₁ M₂ M₃ : ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hM₀ : ∀ x, |f x| ≤ M₀) (hM₁ : ∀ x, |f₁ x| ≤ M₁) (hM₂ : ∀ x, |f₂ x| ≤ M₂)
    (hM₃ : ∀ x, |f₃ x| ≤ M₃)
    {C U X Y : Ω → ℝ}
    (hC0 : ∀ ω, 0 ≤ C ω) (hC1 : ∀ ω, C ω ≤ 1)
    (hCm : Measurable C) (hU : Measurable U) (hXm : Measurable X) (hYm : Measurable Y)
    (hindX : IndepFun (fun ω => (C ω, U ω)) X μ)
    (hindY : IndepFun (fun ω => (C ω, U ω)) Y μ)
    (hX₁ : Integrable X μ) (hX₂ : Integrable (fun ω => X ω * X ω) μ)
    (hY₁ : Integrable Y μ) (hY₂ : Integrable (fun ω => Y ω * Y ω) μ)
    (hm₁ : ∫ ω, X ω ∂μ = ∫ ω, Y ω ∂μ)
    (hm₂ : ∫ ω, X ω * X ω ∂μ = ∫ ω, Y ω * Y ω ∂μ)
    (hTX : Integrable (fun ω => |X ω| ^ 3) μ) (hTY : Integrable (fun ω => |Y ω| ^ 3) μ) :
    |(∫ ω, C ω * f (U ω + X ω) ∂μ) - ∫ ω, C ω * f (U ω + Y ω) ∂μ|
      ≤ M₃ * ((∫ ω, |X ω| ^ 3 ∂μ) + ∫ ω, |Y ω| ^ 3 ∂μ) := by
  -- switch the second coordinate off
  have hg : ∀ x : ℝ, HasDerivAt (fun _ : ℝ => (1:ℝ)) ((fun _ : ℝ => (0:ℝ)) x) x :=
    fun x => hasDerivAt_const x 1
  have hg₁ : ∀ x : ℝ, HasDerivAt (fun _ : ℝ => (0:ℝ)) ((fun _ : ℝ => (0:ℝ)) x) x :=
    fun x => hasDerivAt_const x 0
  have hN₀ : ∀ x : ℝ, |(1:ℝ)| ≤ 1 := fun _ => by norm_num
  have hN₁ : ∀ x : ℝ, |(0:ℝ)| ≤ 0 := fun _ => by norm_num
  have hindX' : IndepFun (fun ω => (C ω, U ω, (0:ℝ))) (fun ω => (X ω, (0:ℝ))) μ :=
    hindX.comp (φ := fun q : ℝ × ℝ => (q.1, q.2, (0:ℝ)))
      (ψ := fun x : ℝ => (x, (0:ℝ))) (by fun_prop) (by fun_prop)
  have hindY' : IndepFun (fun ω => (C ω, U ω, (0:ℝ))) (fun ω => (Y ω, (0:ℝ))) μ :=
    hindY.comp (φ := fun q : ℝ × ℝ => (q.1, q.2, (0:ℝ)))
      (ψ := fun x : ℝ => (x, (0:ℝ))) (by fun_prop) (by fun_prop)
  -- the five monomials collapse to `Z`, `0`, `Z²`, `0`, `0`
  have hmon : ∀ (Z : Ω → ℝ), Integrable Z μ → Integrable (fun ω => Z ω * Z ω) μ →
      ∀ i, Integrable (fun ω => quadMonomial i (Z ω, (0:ℝ))) μ := by
    intro Z h₁ h₂ i
    fin_cases i <;> simp only [quadMonomial, mul_zero] <;>
      first | exact h₁ | exact h₂ | exact integrable_zero _ _ _
  have hmom : ∀ i, ∫ ω, quadMonomial i (X ω, (0:ℝ)) ∂μ
      = ∫ ω, quadMonomial i (Y ω, (0:ℝ)) ∂μ := by
    intro i
    fin_cases i <;> simp only [quadMonomial, mul_zero] <;>
      first | exact hm₁ | exact hm₂
  -- the Lindeberg bound collapses to the third absolute moment
  have hcollapse : ∀ (Z : Ω → ℝ),
      (fun ω => lindebergBound M₀ M₁ M₂ M₃ 1 0 0 0 (Z ω, (0:ℝ)))
        = fun ω => M₃ * |Z ω| ^ 3 := by
    intro Z
    funext ω
    simp only [lindebergBound, abs_zero]
    ring
  have hTX' : Integrable (fun ω => lindebergBound M₀ M₁ M₂ M₃ 1 0 0 0 (X ω, (0:ℝ))) μ := by
    rw [hcollapse]; exact hTX.const_mul M₃
  have hTY' : Integrable (fun ω => lindebergBound M₀ M₁ M₂ M₃ 1 0 0 0 (Y ω, (0:ℝ))) μ := by
    rw [hcollapse]; exact hTY.const_mul M₃
  have hIval : ∀ (Z : Ω → ℝ),
      (∫ ω, lindebergBound M₀ M₁ M₂ M₃ 1 0 0 0 (Z ω, (0:ℝ)) ∂μ) = M₃ * ∫ ω, |Z ω| ^ 3 ∂μ := by
    intro Z
    rw [hcollapse, integral_const_mul]
  have hkey := abs_integral_swap_le (μ := μ) hf hf₁ hf₂ hg hg₁ hg₁ hM₀ hM₁ hM₂ hM₃
    hN₀ hN₁ hN₁ hN₁ hC0 hC1 hCm hU measurable_const (hXm.prodMk measurable_const)
    (hYm.prodMk measurable_const) hindX' hindY' (hmon X hX₁ hX₂) (hmon Y hY₁ hY₂) hmom
    hTX' hTY'
  rw [hIval, hIval, ← mul_add] at hkey
  simpa using hkey

/-! ### The telescope

Swap the summands one at a time.  At each step the already-swapped `Y`'s and the not-yet-swapped
`X`'s form the prefix, and `RMF.abs_integral_swap_le_one` charges one third-moment pair.  The
weight `C` rides along untouched, so the only independence used is `(C, prefix) ⟂ X a` and
`(C, prefix) ⟂ Y a`, one coordinate against the rest; coordinates are never grouped.
-/

/-- **The telescope over a finite family.**
`|∫ C·f(U + ∑_s X) - ∫ C·f(U + ∑_s Y)| ≤ M₃ ∑_s (∫|X i|³ + ∫|Y i|³)`, with no dependence on `#s`.
`hind` is the form the induction consumes: when `a` is swapped, the prefix is `U` plus the `Y`'s
over a set `t` and the `X`'s over a set `r`, both avoiding `a`.  It follows from joint independence
of `(C, U)` with the doubled family `{X i, Y i}` (`iIndepFun.indepFun_finset`), which forces the
tilted `X` and the Gaussian `Y` onto one common space. -/
theorem abs_integral_telescope_le [IsProbabilityMeasure μ]
    {ι : Type*} {s : Finset ι}
    {f f₁ f₂ f₃ : ℝ → ℝ} {M₀ M₁ M₂ M₃ : ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hM₀ : ∀ x, |f x| ≤ M₀) (hM₁ : ∀ x, |f₁ x| ≤ M₁) (hM₂ : ∀ x, |f₂ x| ≤ M₂)
    (hM₃ : ∀ x, |f₃ x| ≤ M₃)
    {C U : Ω → ℝ} {X Y : ι → Ω → ℝ}
    (hC0 : ∀ ω, 0 ≤ C ω) (hC1 : ∀ ω, C ω ≤ 1) (hCm : Measurable C) (hUm : Measurable U)
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hX₁ : ∀ i ∈ s, Integrable (X i) μ)
    (hX₂ : ∀ i ∈ s, Integrable (fun ω => X i ω * X i ω) μ)
    (hY₁ : ∀ i ∈ s, Integrable (Y i) μ)
    (hY₂ : ∀ i ∈ s, Integrable (fun ω => Y i ω * Y i ω) μ)
    (hm₁ : ∀ i ∈ s, ∫ ω, X i ω ∂μ = ∫ ω, Y i ω ∂μ)
    (hm₂ : ∀ i ∈ s, ∫ ω, X i ω * X i ω ∂μ = ∫ ω, Y i ω * Y i ω ∂μ)
    (hTX : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ 3) μ)
    (hTY : ∀ i ∈ s, Integrable (fun ω => |Y i ω| ^ 3) μ)
    (hind : ∀ a ∈ s, ∀ t r : Finset ι, a ∉ t → a ∉ r →
      IndepFun (fun ω => (C ω, U ω + ((∑ i ∈ t, Y i ω) + ∑ i ∈ r, X i ω))) (X a) μ ∧
        IndepFun (fun ω => (C ω, U ω + ((∑ i ∈ t, Y i ω) + ∑ i ∈ r, X i ω))) (Y a) μ) :
    |(∫ ω, C ω * f (U ω + ∑ i ∈ s, X i ω) ∂μ)
        - ∫ ω, C ω * f (U ω + ∑ i ∈ s, Y i ω) ∂μ|
      ≤ M₃ * ∑ i ∈ s, ((∫ ω, |X i ω| ^ 3 ∂μ) + ∫ ω, |Y i ω| ^ 3 ∂μ) := by
  classical
  -- induct on the set left to swap; `t` is the set already swapped
  have key : ∀ r : Finset ι, r ⊆ s → ∀ t : Finset ι, Disjoint t r →
      |(∫ ω, C ω * f (U ω + ((∑ i ∈ t, Y i ω) + ∑ i ∈ r, X i ω)) ∂μ)
          - ∫ ω, C ω * f (U ω + ∑ i ∈ t ∪ r, Y i ω) ∂μ|
        ≤ M₃ * ∑ i ∈ r, ((∫ ω, |X i ω| ^ 3 ∂μ) + ∫ ω, |Y i ω| ^ 3 ∂μ) := by
    intro r
    induction r using Finset.induction_on with
    | empty => intro _ t _; simp
    | insert a r' ha ih =>
      intro hsub t hdisj
      have has : a ∈ s := hsub (Finset.mem_insert_self a r')
      have hr's : r' ⊆ s := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hta : a ∉ t := fun hmem =>
        Finset.disjoint_left.mp hdisj hmem (Finset.mem_insert_self a r')
      have htr' : Disjoint t r' := hdisj.mono_right (Finset.subset_insert a r')
      -- the prefix at the moment `a` is swapped
      have hVm : Measurable (fun ω => U ω + ((∑ i ∈ t, Y i ω) + ∑ i ∈ r', X i ω)) :=
        hUm.add ((Finset.measurable_sum t fun i _ => hYm i).add
          (Finset.measurable_sum r' fun i _ => hXm i))
      have h1 := abs_integral_swap_le_one (μ := μ) hf hf₁ hf₂ hM₀ hM₁ hM₂ hM₃ hC0 hC1 hCm hVm
        (hXm a) (hYm a) (hind a has t r' hta ha).1 (hind a has t r' hta ha).2
        (hX₁ a has) (hX₂ a has) (hY₁ a has) (hY₂ a has) (hm₁ a has) (hm₂ a has)
        (hTX a has) (hTY a has)
      have h2 := ih hr's (insert a t) (by
        rw [Finset.disjoint_insert_left]
        exact ⟨ha, htr'⟩)
      -- match the prefixes: `a` moves from the `X` side to the `Y` side
      have e1 : ∀ ω, U ω + ((∑ i ∈ t, Y i ω) + ∑ i ∈ insert a r', X i ω)
          = (U ω + ((∑ i ∈ t, Y i ω) + ∑ i ∈ r', X i ω)) + X a ω := by
        intro ω; rw [Finset.sum_insert ha]; ring
      have e2 : ∀ ω, U ω + ((∑ i ∈ insert a t, Y i ω) + ∑ i ∈ r', X i ω)
          = (U ω + ((∑ i ∈ t, Y i ω) + ∑ i ∈ r', X i ω)) + Y a ω := by
        intro ω; rw [Finset.sum_insert hta]; ring
      have e3 : insert a t ∪ r' = t ∪ insert a r' := by
        rw [Finset.insert_union, Finset.union_insert]
      simp only [e1]
      simp only [e2, e3] at h2
      rw [Finset.sum_insert ha, mul_add]
      exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)
  simpa using key s (subset_refl s) ∅ (Finset.disjoint_empty_left s)

/-- **The telescope, unweighted** — the form Harper's Lemma 3 calls, where there is no weight and
no prefix: the per-coordinate comparison is between two single block sums.

Dropping `C ≡ 1` and `U ≡ 0` reduces `hind` to plain independence of a partial hybrid sum from the
next coordinate, with no pairing against a constant — which is what an `iIndepFun` hypothesis on the
doubled family `{X i, Y i}` delivers through `iIndepFun.indepFun_finset`. -/
theorem abs_integral_telescope_le_of_indep [IsProbabilityMeasure μ]
    {ι : Type*} {s : Finset ι}
    {f f₁ f₂ f₃ : ℝ → ℝ} {M₀ M₁ M₂ M₃ : ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hM₀ : ∀ x, |f x| ≤ M₀) (hM₁ : ∀ x, |f₁ x| ≤ M₁) (hM₂ : ∀ x, |f₂ x| ≤ M₂)
    (hM₃ : ∀ x, |f₃ x| ≤ M₃)
    {X Y : ι → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hX₁ : ∀ i ∈ s, Integrable (X i) μ)
    (hX₂ : ∀ i ∈ s, Integrable (fun ω => X i ω * X i ω) μ)
    (hY₁ : ∀ i ∈ s, Integrable (Y i) μ)
    (hY₂ : ∀ i ∈ s, Integrable (fun ω => Y i ω * Y i ω) μ)
    (hm₁ : ∀ i ∈ s, ∫ ω, X i ω ∂μ = ∫ ω, Y i ω ∂μ)
    (hm₂ : ∀ i ∈ s, ∫ ω, X i ω * X i ω ∂μ = ∫ ω, Y i ω * Y i ω ∂μ)
    (hTX : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ 3) μ)
    (hTY : ∀ i ∈ s, Integrable (fun ω => |Y i ω| ^ 3) μ)
    (hind : ∀ a ∈ s, ∀ t r : Finset ι, a ∉ t → a ∉ r →
      IndepFun (fun ω => (∑ i ∈ t, Y i ω) + ∑ i ∈ r, X i ω) (X a) μ ∧
        IndepFun (fun ω => (∑ i ∈ t, Y i ω) + ∑ i ∈ r, X i ω) (Y a) μ) :
    |(∫ ω, f (∑ i ∈ s, X i ω) ∂μ) - ∫ ω, f (∑ i ∈ s, Y i ω) ∂μ|
      ≤ M₃ * ∑ i ∈ s, ((∫ ω, |X i ω| ^ 3 ∂μ) + ∫ ω, |Y i ω| ^ 3 ∂μ) := by
  have hpair : ∀ (V W : Ω → ℝ), IndepFun V W μ →
      IndepFun (fun ω => ((1 : ℝ), (0 : ℝ) + V ω)) W μ := by
    intro V W h
    exact h.comp (φ := fun v : ℝ => ((1 : ℝ), (0 : ℝ) + v)) (ψ := id) (by fun_prop) measurable_id
  have h := abs_integral_telescope_le (μ := μ) (s := s) (C := fun _ => 1) (U := fun _ => 0)
    hf hf₁ hf₂ hM₀ hM₁ hM₂ hM₃ (fun _ => zero_le_one) (fun _ => le_rfl) measurable_const
    measurable_const hXm hYm hX₁ hX₂ hY₁ hY₂ hm₁ hm₂ hTX hTY
    (fun a has t r hat har =>
      ⟨hpair _ _ (hind a has t r hat har).1, hpair _ _ (hind a has t r hat har).2⟩)
  simpa using h

/-! ### The smoothed window at the two-dimensional swap

`RMF.abs_integral_swap_le` is stated for a product test function `ψ = f ⊗ g` with arbitrary `f`,
`g`; the two-point argument (Harper's Lemma 7) needs that instance at `f = g = RMF.window`,
together with the resulting Lindeberg bound in a usable shape.

The point of the shape is that **every mixed coefficient is `O(δ^{-3})`**, the same order as the
pure ones, so smoothing costs one power of `δ^{-3}` overall and not more. -/

/-- The window is bounded by `1` in absolute value — the `M₀` and `N₀` of the swap. -/
lemma abs_window_le_one (δ a b x : ℝ) : |window δ a b x| ≤ 1 := by
  rw [abs_of_nonneg (window_nonneg δ a b x)]
  exact window_le_one δ a b x

/-! The swap wants its derivatives as *functions*; `RMF.hasDerivAt_window` and friends give them
in explicit closed form.  These three restate them at `deriv`, which is what lets the chain
`f → f₁ → f₂ → f₃` be written as iterated `deriv`. -/

lemma hasDerivAt_window_deriv (δ a b x : ℝ) :
    HasDerivAt (window δ a b) (deriv (window δ a b) x) x := by
  rw [(hasDerivAt_window δ a b x).deriv]
  exact hasDerivAt_window δ a b x

lemma hasDerivAt_window_deriv2 (δ a b x : ℝ) :
    HasDerivAt (deriv (window δ a b)) (deriv (deriv (window δ a b)) x) x := by
  rw [(hasDerivAt_deriv_window δ a b x).deriv]
  exact hasDerivAt_deriv_window δ a b x

lemma hasDerivAt_window_deriv3 (δ a b x : ℝ) :
    HasDerivAt (deriv (deriv (window δ a b)))
      (deriv (deriv (deriv (window δ a b))) x) x := by
  rw [(hasDerivAt_deriv2_window δ a b x).deriv]
  exact hasDerivAt_deriv2_window δ a b x

/-- **The Lindeberg bound at the window, in one order.**

At `Mᵢ = Nᵢ = (1, 35/8δ, 63/δ², 450/δ³)` the four coefficients are `450`, `3·(63·35/8) = 826.875`
twice, and `450`, all over `δ³`.  Against the expansion of `(|z₁|+|z₂|)³`, whose coefficients are
`1, 3, 3, 1`, every one of them fits under `900/δ³` with room — the mixed terms by a factor of
more than three. -/
lemma lindebergBound_window_le {δ : ℝ} (hδ : 0 < δ) (z : ℝ × ℝ) :
    lindebergBound 1 (35 / 8 / δ) (63 / δ ^ 2) (450 / δ ^ 3)
        1 (35 / 8 / δ) (63 / δ ^ 2) (450 / δ ^ 3) z
      ≤ 900 / δ ^ 3 * (|z.1| + |z.2|) ^ 3 := by
  have hd : (0 : ℝ) < δ ^ 3 := by positivity
  have h1 : (0 : ℝ) ≤ |z.1| := abs_nonneg _
  have h2 : (0 : ℝ) ≤ |z.2| := abs_nonneg _
  rw [lindebergBound, ← sub_nonneg]
  have key : 900 / δ ^ 3 * (|z.1| + |z.2|) ^ 3
      - (450 / δ ^ 3 * 1 * |z.1| ^ 3
          + 3 * (63 / δ ^ 2 * (35 / 8 / δ)) * (|z.1| ^ 2 * |z.2|)
          + 3 * (35 / 8 / δ * (63 / δ ^ 2)) * (|z.1| * |z.2| ^ 2)
          + 1 * (450 / δ ^ 3) * |z.2| ^ 3)
      = (450 * |z.1| ^ 3 + 14985 / 8 * (|z.1| ^ 2 * |z.2|)
          + 14985 / 8 * (|z.1| * |z.2| ^ 2) + 450 * |z.2| ^ 3) / δ ^ 3 := by
    field_simp
    ring
  rw [key]
  positivity

/-- **The one-step swap at the smoothed window.**  `RMF.abs_integral_swap_le` at
`f = g = RMF.window`, with its eight derivative and sup-norm hypotheses discharged; the caller
supplies only the probabilistic data.  The bound stays in `RMF.lindebergBound` form, so that no
integrability hypothesis is duplicated; `RMF.lindebergBound_window_le` converts it into
`900δ^{-3}(|z₁|+|z₂|)³`, the form the two-point telescope sums. -/
theorem abs_integral_swap_window_le [IsProbabilityMeasure μ]
    {δ a₁ b₁ a₂ b₂ : ℝ} (hδ : 0 < δ)
    {C U₁ U₂ : Ω → ℝ} {X Y : Ω → ℝ × ℝ}
    (hC0 : ∀ ω, 0 ≤ C ω) (hC1 : ∀ ω, C ω ≤ 1)
    (hCm : Measurable C) (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hindX : IndepFun (fun ω => (C ω, U₁ ω, U₂ ω)) X μ)
    (hindY : IndepFun (fun ω => (C ω, U₁ ω, U₂ ω)) Y μ)
    (hmX : ∀ i, Integrable (fun ω => quadMonomial i (X ω)) μ)
    (hmY : ∀ i, Integrable (fun ω => quadMonomial i (Y ω)) μ)
    (hmom : ∀ i, ∫ ω, quadMonomial i (X ω) ∂μ = ∫ ω, quadMonomial i (Y ω) ∂μ)
    (hTX : Integrable (fun ω => lindebergBound 1 (35 / 8 / δ) (63 / δ ^ 2) (450 / δ ^ 3)
      1 (35 / 8 / δ) (63 / δ ^ 2) (450 / δ ^ 3) (X ω)) μ)
    (hTY : Integrable (fun ω => lindebergBound 1 (35 / 8 / δ) (63 / δ ^ 2) (450 / δ ^ 3)
      1 (35 / 8 / δ) (63 / δ ^ 2) (450 / δ ^ 3) (Y ω)) μ) :
    |(∫ ω, C ω * (window δ a₁ b₁ (U₁ ω + (X ω).1)
          * window δ a₂ b₂ (U₂ ω + (X ω).2)) ∂μ)
        - ∫ ω, C ω * (window δ a₁ b₁ (U₁ ω + (Y ω).1)
            * window δ a₂ b₂ (U₂ ω + (Y ω).2)) ∂μ|
      ≤ (∫ ω, lindebergBound 1 (35 / 8 / δ) (63 / δ ^ 2) (450 / δ ^ 3)
            1 (35 / 8 / δ) (63 / δ ^ 2) (450 / δ ^ 3) (X ω) ∂μ)
        + ∫ ω, lindebergBound 1 (35 / 8 / δ) (63 / δ ^ 2) (450 / δ ^ 3)
            1 (35 / 8 / δ) (63 / δ ^ 2) (450 / δ ^ 3) (Y ω) ∂μ :=
  abs_integral_swap_le
    (hasDerivAt_window_deriv δ a₁ b₁) (hasDerivAt_window_deriv2 δ a₁ b₁)
    (hasDerivAt_window_deriv3 δ a₁ b₁)
    (hasDerivAt_window_deriv δ a₂ b₂) (hasDerivAt_window_deriv2 δ a₂ b₂)
    (hasDerivAt_window_deriv3 δ a₂ b₂)
    (abs_window_le_one δ a₁ b₁) (abs_deriv_window_le hδ a₁ b₁)
    (abs_deriv2_window_le hδ a₁ b₁) (abs_deriv3_window_le hδ a₁ b₁)
    (abs_window_le_one δ a₂ b₂) (abs_deriv_window_le hδ a₂ b₂)
    (abs_deriv2_window_le hδ a₂ b₂) (abs_deriv3_window_le hδ a₂ b₂)
    hC0 hC1 hCm hU₁ hU₂ hXm hYm hindX hindY hmX hmY hmom hTX hTY

/-! ### The two-dimensional telescope

`RMF.abs_integral_swap_window_le` swaps one pair-increment; the two-point argument needs a whole
block chain swapped, by the induction `RMF.abs_integral_telescope_le` runs in one dimension: at
each step the swapped `Y`'s and the unswapped `X`'s form the prefix, the weight `C` rides along,
and one Lindeberg pair is charged.  Only two-group independence is used — the prefix against a
single coordinate — so κ-ary grouping is not needed here either.

**What is new in two dimensions is the fifth moment.**  `RMF.quadMonomial` asks for both means,
both second moments, *and the mixed one*; matching that last is why the comparison Gaussian has to
be bivariate rather than a pair of independent ones, and it is where the logarithmic correlation
between the two heights enters. -/

/-- The Lindeberg bound at the window's own coefficients.  Named so that the telescope can state
its integrability hypotheses and its conclusion without repeating the eight coefficients. -/
noncomputable def windowLindebergBound (δ : ℝ) (z : ℝ × ℝ) : ℝ :=
  lindebergBound 1 (35 / 8 / δ) (63 / δ ^ 2) (450 / δ ^ 3)
    1 (35 / 8 / δ) (63 / δ ^ 2) (450 / δ ^ 3) z

/-- `RMF.lindebergBound_window_le` at the abbreviation: the cube form the telescope sums. -/
lemma windowLindebergBound_le {δ : ℝ} (hδ : 0 < δ) (z : ℝ × ℝ) :
    windowLindebergBound δ z ≤ 900 / δ ^ 3 * (|z.1| + |z.2|) ^ 3 :=
  lindebergBound_window_le hδ z

/-- The window is measurable — it is differentiable, hence continuous. -/
lemma measurable_window (δ a b : ℝ) : Measurable (window δ a b) :=
  (continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_window δ a b x).continuousAt).measurable

/-- `RMF.windowLindebergBound` is measurable: it is a polynomial in `|z₁|` and `|z₂|`. -/
lemma measurable_windowLindebergBound (δ : ℝ) : Measurable (windowLindebergBound δ) := by
  unfold windowLindebergBound lindebergBound
  fun_prop

/-- **The two-dimensional telescope over a finite family**, the pair analogue of
`RMF.abs_integral_telescope_le` at the smoothed window: the cost is
`∑_s (∫ windowLindebergBound δ (X i) + ∫ windowLindebergBound δ (Y i))`.  `hind` is the form the
induction consumes (the prefix is `(U₁, U₂)` plus the `Y`'s over `t` and the `X`'s over `r`, both
avoiding `a`); it follows from joint independence of `(C, U₁, U₂)` with the doubled family. -/
theorem abs_integral_telescope_window_le [IsProbabilityMeasure μ]
    {ι : Type*} {s : Finset ι} {δ a₁ b₁ a₂ b₂ : ℝ} (hδ : 0 < δ)
    {C U₁ U₂ : Ω → ℝ} {X Y : ι → Ω → ℝ × ℝ}
    (hC0 : ∀ ω, 0 ≤ C ω) (hC1 : ∀ ω, C ω ≤ 1) (hCm : Measurable C)
    (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hmX : ∀ i ∈ s, ∀ j, Integrable (fun ω => quadMonomial j (X i ω)) μ)
    (hmY : ∀ i ∈ s, ∀ j, Integrable (fun ω => quadMonomial j (Y i ω)) μ)
    (hmom : ∀ i ∈ s, ∀ j, (∫ ω, quadMonomial j (X i ω) ∂μ)
      = ∫ ω, quadMonomial j (Y i ω) ∂μ)
    (hTX : ∀ i ∈ s, Integrable (fun ω => windowLindebergBound δ (X i ω)) μ)
    (hTY : ∀ i ∈ s, Integrable (fun ω => windowLindebergBound δ (Y i ω)) μ)
    (hind : ∀ a ∈ s, ∀ t r : Finset ι, a ∉ t → a ∉ r →
      IndepFun (fun ω => (C ω,
          U₁ ω + ((∑ i ∈ t, (Y i ω).1) + ∑ i ∈ r, (X i ω).1),
          U₂ ω + ((∑ i ∈ t, (Y i ω).2) + ∑ i ∈ r, (X i ω).2))) (X a) μ ∧
        IndepFun (fun ω => (C ω,
          U₁ ω + ((∑ i ∈ t, (Y i ω).1) + ∑ i ∈ r, (X i ω).1),
          U₂ ω + ((∑ i ∈ t, (Y i ω).2) + ∑ i ∈ r, (X i ω).2))) (Y a) μ) :
    |(∫ ω, C ω * (window δ a₁ b₁ (U₁ ω + ∑ i ∈ s, (X i ω).1)
            * window δ a₂ b₂ (U₂ ω + ∑ i ∈ s, (X i ω).2)) ∂μ)
        - ∫ ω, C ω * (window δ a₁ b₁ (U₁ ω + ∑ i ∈ s, (Y i ω).1)
            * window δ a₂ b₂ (U₂ ω + ∑ i ∈ s, (Y i ω).2)) ∂μ|
      ≤ ∑ i ∈ s, ((∫ ω, windowLindebergBound δ (X i ω) ∂μ)
          + ∫ ω, windowLindebergBound δ (Y i ω) ∂μ) := by
  classical
  have key : ∀ r : Finset ι, r ⊆ s → ∀ t : Finset ι, Disjoint t r →
      |(∫ ω, C ω * (window δ a₁ b₁ (U₁ ω + ((∑ i ∈ t, (Y i ω).1) + ∑ i ∈ r, (X i ω).1))
              * window δ a₂ b₂ (U₂ ω + ((∑ i ∈ t, (Y i ω).2) + ∑ i ∈ r, (X i ω).2))) ∂μ)
          - ∫ ω, C ω * (window δ a₁ b₁ (U₁ ω + ∑ i ∈ t ∪ r, (Y i ω).1)
              * window δ a₂ b₂ (U₂ ω + ∑ i ∈ t ∪ r, (Y i ω).2)) ∂μ|
        ≤ ∑ i ∈ r, ((∫ ω, windowLindebergBound δ (X i ω) ∂μ)
            + ∫ ω, windowLindebergBound δ (Y i ω) ∂μ) := by
    intro r
    induction r using Finset.induction_on with
    | empty => intro _ t _; simp
    | insert a r' ha ih =>
      intro hsub t hdisj
      have has : a ∈ s := hsub (Finset.mem_insert_self a r')
      have hr's : r' ⊆ s := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hta : a ∉ t := fun hmem =>
        Finset.disjoint_left.mp hdisj hmem (Finset.mem_insert_self a r')
      have htr' : Disjoint t r' := hdisj.mono_right (Finset.subset_insert a r')
      have hV₁ : Measurable fun ω => U₁ ω + ((∑ i ∈ t, (Y i ω).1) + ∑ i ∈ r', (X i ω).1) :=
        hU₁.add ((Finset.measurable_sum t fun i _ => (hYm i).fst).add
          (Finset.measurable_sum r' fun i _ => (hXm i).fst))
      have hV₂ : Measurable fun ω => U₂ ω + ((∑ i ∈ t, (Y i ω).2) + ∑ i ∈ r', (X i ω).2) :=
        hU₂.add ((Finset.measurable_sum t fun i _ => (hYm i).snd).add
          (Finset.measurable_sum r' fun i _ => (hXm i).snd))
      have h1 := abs_integral_swap_window_le (μ := μ) (δ := δ) (a₁ := a₁) (b₁ := b₁)
        (a₂ := a₂) (b₂ := b₂) hδ hC0 hC1 hCm hV₁ hV₂ (hXm a) (hYm a)
        (hind a has t r' hta ha).1 (hind a has t r' hta ha).2
        (hmX a has) (hmY a has) (hmom a has) (hTX a has) (hTY a has)
      have h2 := ih hr's (insert a t) (by
        rw [Finset.disjoint_insert_left]
        exact ⟨ha, htr'⟩)
      have e1 : ∀ ω, U₁ ω + ((∑ i ∈ t, (Y i ω).1) + ∑ i ∈ insert a r', (X i ω).1)
          = (U₁ ω + ((∑ i ∈ t, (Y i ω).1) + ∑ i ∈ r', (X i ω).1)) + (X a ω).1 := by
        intro ω; rw [Finset.sum_insert ha]; ring
      have e1' : ∀ ω, U₂ ω + ((∑ i ∈ t, (Y i ω).2) + ∑ i ∈ insert a r', (X i ω).2)
          = (U₂ ω + ((∑ i ∈ t, (Y i ω).2) + ∑ i ∈ r', (X i ω).2)) + (X a ω).2 := by
        intro ω; rw [Finset.sum_insert ha]; ring
      have e2 : ∀ ω, U₁ ω + ((∑ i ∈ insert a t, (Y i ω).1) + ∑ i ∈ r', (X i ω).1)
          = (U₁ ω + ((∑ i ∈ t, (Y i ω).1) + ∑ i ∈ r', (X i ω).1)) + (Y a ω).1 := by
        intro ω; rw [Finset.sum_insert hta]; ring
      have e2' : ∀ ω, U₂ ω + ((∑ i ∈ insert a t, (Y i ω).2) + ∑ i ∈ r', (X i ω).2)
          = (U₂ ω + ((∑ i ∈ t, (Y i ω).2) + ∑ i ∈ r', (X i ω).2)) + (Y a ω).2 := by
        intro ω; rw [Finset.sum_insert hta]; ring
      have e3 : insert a t ∪ r' = t ∪ insert a r' := by
        rw [Finset.insert_union, Finset.union_insert]
      simp only [e1, e1']
      simp only [e2, e2', e3] at h2
      rw [Finset.sum_insert ha]
      exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)
  simpa using key s (subset_refl s) ∅ (Finset.disjoint_empty_left s)

/-- **The two-dimensional telescope, unweighted** — the form the pair window comparison calls,
where there is no weight and no prefix and the comparison is between two block sums.

Dropping `C ≡ 1` and `Uᵢ ≡ 0` reduces `hind` to plain independence of a partial hybrid sum from
the next coordinate, which an `iIndepFun` hypothesis on the doubled family delivers. -/
theorem abs_integral_telescope_window_le_of_indep [IsProbabilityMeasure μ]
    {ι : Type*} {s : Finset ι} {δ a₁ b₁ a₂ b₂ : ℝ} (hδ : 0 < δ)
    {X Y : ι → Ω → ℝ × ℝ}
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hmX : ∀ i ∈ s, ∀ j, Integrable (fun ω => quadMonomial j (X i ω)) μ)
    (hmY : ∀ i ∈ s, ∀ j, Integrable (fun ω => quadMonomial j (Y i ω)) μ)
    (hmom : ∀ i ∈ s, ∀ j, (∫ ω, quadMonomial j (X i ω) ∂μ)
      = ∫ ω, quadMonomial j (Y i ω) ∂μ)
    (hTX : ∀ i ∈ s, Integrable (fun ω => windowLindebergBound δ (X i ω)) μ)
    (hTY : ∀ i ∈ s, Integrable (fun ω => windowLindebergBound δ (Y i ω)) μ)
    (hind : ∀ a ∈ s, ∀ t r : Finset ι, a ∉ t → a ∉ r →
      IndepFun (fun ω => (((∑ i ∈ t, (Y i ω).1) + ∑ i ∈ r, (X i ω).1),
          ((∑ i ∈ t, (Y i ω).2) + ∑ i ∈ r, (X i ω).2))) (X a) μ ∧
        IndepFun (fun ω => (((∑ i ∈ t, (Y i ω).1) + ∑ i ∈ r, (X i ω).1),
          ((∑ i ∈ t, (Y i ω).2) + ∑ i ∈ r, (X i ω).2))) (Y a) μ) :
    |(∫ ω, window δ a₁ b₁ (∑ i ∈ s, (X i ω).1)
            * window δ a₂ b₂ (∑ i ∈ s, (X i ω).2) ∂μ)
        - ∫ ω, window δ a₁ b₁ (∑ i ∈ s, (Y i ω).1)
            * window δ a₂ b₂ (∑ i ∈ s, (Y i ω).2) ∂μ|
      ≤ ∑ i ∈ s, ((∫ ω, windowLindebergBound δ (X i ω) ∂μ)
          + ∫ ω, windowLindebergBound δ (Y i ω) ∂μ) := by
  have htriple : ∀ (V : Ω → ℝ × ℝ) (W : Ω → ℝ × ℝ), IndepFun V W μ →
      IndepFun (fun ω => ((1 : ℝ), (0 : ℝ) + (V ω).1, (0 : ℝ) + (V ω).2)) W μ := by
    intro V W h
    exact h.comp (φ := fun v : ℝ × ℝ => ((1 : ℝ), (0 : ℝ) + v.1, (0 : ℝ) + v.2))
      (ψ := id) (by fun_prop) measurable_id
  have h := abs_integral_telescope_window_le (μ := μ) (s := s) (C := fun _ => 1)
    (U₁ := fun _ => 0) (U₂ := fun _ => 0) (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂)
    hδ (fun _ => zero_le_one) (fun _ => le_rfl)
    measurable_const measurable_const measurable_const hXm hYm hmX hmY hmom hTX hTY
    (fun a has t r hat har =>
      ⟨htriple _ _ (hind a has t r hat har).1, htriple _ _ (hind a has t r hat har).2⟩)
  simpa using h

end RMF
