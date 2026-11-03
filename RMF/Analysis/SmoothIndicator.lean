/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Analysis.Smoothstep

/-!
# A `C³` sandwich for the indicator of an interval

A Lindeberg replacement argument compares `E φ(∑ X_j)` with `E φ(∑ G_j)` for a `C³` test function
`φ`, and then recovers an interval probability by squeezing the indicator of `[u, v]` between two
such `φ`.  This file builds the squeeze.

## The construction

`RMF.window δ a b` rises from `0` to `1` on `[a, a+δ]`, sits at `1` on `[a+δ, b-δ]`, and falls
back to `0` on `[b-δ, b]` — a rising smoothstep at `a` times a falling one at `b`.  From it:

* `RMF.smoothIndicatorLower δ u v = window δ u v`, supported in `[u, v]` and equal to `1` on the
  shrunken `[u+δ, v-δ]`;
* `RMF.smoothIndicatorUpper δ u v = window δ (u-δ) (v+δ)`, equal to `1` on `[u, v]` and supported
  in the enlarged `[u-δ, v+δ]`.

They sandwich the indicator, and — this is what the argument actually consumes — their
*difference* vanishes off the `δ`-neighbourhood of the two endpoints
(`RMF.smoothIndicatorUpper_sub_lower_le_indicator`).  So the cost of smoothing is exactly the
mass the comparison law puts within `δ` of an endpoint, and nothing else.

## Scaling

Everything here is `RMF.smoothstep` composed with an affine map of slope `±1/δ`, so the `k`-th
derivative of the window is bounded by `C_k / δ^k`, with `C_k` built from the constants of
`RMF/Analysis/Smoothstep.lean` (`RMF.abs_deriv_window_le`, `RMF.abs_deriv2_window_le`,
`RMF.abs_deriv3_window_le`).
-/

namespace RMF

/-! ### The window -/

/-- The plateau function on `[a, b]` with transition width `δ`: a rising smoothstep at `a` times
a falling one at `b`. -/
noncomputable def window (δ a b x : ℝ) : ℝ :=
  smoothstep ((x - a) / δ) * smoothstep ((b - x) / δ)

lemma window_nonneg (δ a b x : ℝ) : 0 ≤ window δ a b x :=
  mul_nonneg (smoothstep_nonneg _) (smoothstep_nonneg _)

lemma window_le_one (δ a b x : ℝ) : window δ a b x ≤ 1 := by
  have h₁ := smoothstep_nonneg ((x - a) / δ)
  have h₂ := smoothstep_le_one ((x - a) / δ)
  have h₃ := smoothstep_nonneg ((b - x) / δ)
  have h₄ := smoothstep_le_one ((b - x) / δ)
  rw [window]
  nlinarith

/-- The window vanishes to the left of its support. -/
lemma window_eq_zero_of_le {δ a b x : ℝ} (hδ : 0 < δ) (hx : x ≤ a) : window δ a b x = 0 := by
  rw [window, smoothstep_of_nonpos (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith),
    zero_mul]

/-- The window vanishes to the right of its support. -/
lemma window_eq_zero_of_ge {δ a b x : ℝ} (hδ : 0 < δ) (hx : b ≤ x) : window δ a b x = 0 := by
  have h : smoothstep ((b - x) / δ) = 0 :=
    smoothstep_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  rw [window, h, mul_zero]

/-- On the plateau the window is exactly `1`. -/
lemma window_eq_one_of_mem_Icc {δ a b x : ℝ} (hδ : 0 < δ) (h₁ : a + δ ≤ x) (h₂ : x ≤ b - δ) :
    window δ a b x = 1 := by
  rw [window, smoothstep_of_one_le (by rw [le_div_iff₀ hδ]; linarith),
    smoothstep_of_one_le (by rw [le_div_iff₀ hδ]; linarith), one_mul]

/-- **The window is `C³`**, being a product of two smoothsteps composed with affine maps. -/
lemma contDiff_window (δ a b : ℝ) : ContDiff ℝ 3 (window δ a b) := by
  have h₁ : ContDiff ℝ 3 fun x : ℝ => smoothstep ((x - a) / δ) :=
    contDiff_smoothstep.comp ((contDiff_id.sub contDiff_const).div_const δ)
  have h₂ : ContDiff ℝ 3 fun x : ℝ => smoothstep ((b - x) / δ) :=
    contDiff_smoothstep.comp ((contDiff_const.sub contDiff_id).div_const δ)
  exact ContDiff.mul h₁ h₂

/-! ### The sandwich -/

/-- The inner `C³` minorant of `1_[u,v]`: supported in `[u, v]`, equal to `1` on `[u+δ, v-δ]`. -/
noncomputable def smoothIndicatorLower (δ u v : ℝ) : ℝ → ℝ := window δ u v

/-- The outer `C³` majorant of `1_[u,v]`: equal to `1` on `[u, v]`, supported in
`[u-δ, v+δ]`. -/
noncomputable def smoothIndicatorUpper (δ u v : ℝ) : ℝ → ℝ := window δ (u - δ) (v + δ)

lemma contDiff_smoothIndicatorLower (δ u v : ℝ) : ContDiff ℝ 3 (smoothIndicatorLower δ u v) :=
  contDiff_window δ u v

lemma contDiff_smoothIndicatorUpper (δ u v : ℝ) : ContDiff ℝ 3 (smoothIndicatorUpper δ u v) :=
  contDiff_window δ (u - δ) (v + δ)

lemma smoothIndicatorLower_nonneg (δ u v x : ℝ) : 0 ≤ smoothIndicatorLower δ u v x :=
  window_nonneg _ _ _ _

lemma smoothIndicatorUpper_le_one (δ u v x : ℝ) : smoothIndicatorUpper δ u v x ≤ 1 :=
  window_le_one _ _ _ _

/-- The majorant is `1` on the interval itself. -/
lemma smoothIndicatorUpper_eq_one_of_mem_Icc {δ u v x : ℝ} (hδ : 0 < δ) (h₁ : u ≤ x)
    (h₂ : x ≤ v) : smoothIndicatorUpper δ u v x = 1 :=
  window_eq_one_of_mem_Icc hδ (by linarith) (by linarith)

/-- **Upper half of the sandwich**, `1_[u,v] ≤ φ⁺`. -/
lemma indicator_le_smoothIndicatorUpper {δ u v : ℝ} (hδ : 0 < δ) (x : ℝ) :
    (Set.Icc u v).indicator (1 : ℝ → ℝ) x ≤ smoothIndicatorUpper δ u v x := by
  by_cases hx : x ∈ Set.Icc u v
  · rw [Set.indicator_of_mem hx, smoothIndicatorUpper_eq_one_of_mem_Icc hδ hx.1 hx.2,
      Pi.one_apply]
  · rw [Set.indicator_of_notMem hx]
    exact window_nonneg _ _ _ _

/-! ### The sandwich, half-open

`RMF.sliceEvent` uses `Ioc`, because that is what makes distinct grid points give genuinely
disjoint slices.  The sandwich survives the change untouched: the lower window already *vanishes at
its left endpoint*, `window δ u v u = 0`, so it lies below `1_(u,v]` just as it lies below
`1_[u,v]`.  No atomlessness, and no `δ` of slack, is needed to make the two agree. -/

/-- **Lower half of the sandwich, half-open.**  `φ⁻ ≤ 1_(u,v]`. -/
lemma smoothIndicatorLower_le_indicator_Ioc {δ u v : ℝ} (hδ : 0 < δ) (x : ℝ) :
    smoothIndicatorLower δ u v x ≤ (Set.Ioc u v).indicator (1 : ℝ → ℝ) x := by
  by_cases hx : x ∈ Set.Ioc u v
  · rw [Set.indicator_of_mem hx]
    exact window_le_one _ _ _ _
  · rw [Set.indicator_of_notMem hx]
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with h | h
    · exact le_of_eq (window_eq_zero_of_le hδ h)
    · exact le_of_eq (window_eq_zero_of_ge hδ h.le)

/-- **Upper half of the sandwich, half-open.**  `1_(u,v] ≤ φ⁺`. -/
lemma indicator_Ioc_le_smoothIndicatorUpper {δ u v : ℝ} (hδ : 0 < δ) (x : ℝ) :
    (Set.Ioc u v).indicator (1 : ℝ → ℝ) x ≤ smoothIndicatorUpper δ u v x := by
  refine le_trans ?_ (indicator_le_smoothIndicatorUpper hδ x)
  by_cases hx : x ∈ Set.Ioc u v
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.Ioc_subset_Icc_self hx)]
  · rw [Set.indicator_of_notMem hx]
    by_cases hx' : x ∈ Set.Icc u v
    · rw [Set.indicator_of_mem hx']; exact zero_le_one
    · rw [Set.indicator_of_notMem hx']

/-! ### The smoothing error -/

/-- **The two ends of the sandwich agree off the endpoints.**  On the plateau both are `1`;
outside the enlarged interval both are `0`.  So the whole cost of smoothing is confined to the
`δ`-neighbourhood of `u` and of `v`. -/
lemma smoothIndicatorUpper_eq_lower_of_notMem {δ u v x : ℝ} (hδ : 0 < δ)
    (hx : x ∉ Set.Icc (u - δ) (u + δ) ∪ Set.Icc (v - δ) (v + δ)) :
    smoothIndicatorUpper δ u v x = smoothIndicatorLower δ u v x := by
  simp only [Set.mem_union, Set.mem_Icc, not_or, not_and_or, not_le] at hx
  obtain ⟨h₁, h₂⟩ := hx
  rcases h₁ with h₁ | h₁
  · -- `x < u - δ`: both vanish
    rw [smoothIndicatorUpper, window_eq_zero_of_le hδ h₁.le, smoothIndicatorLower,
      window_eq_zero_of_le hδ (by linarith)]
  · rcases h₂ with h₂ | h₂
    · -- `u + δ < x < v - δ`: both are `1`
      rw [smoothIndicatorUpper, window_eq_one_of_mem_Icc hδ (by linarith) (by linarith),
        smoothIndicatorLower, window_eq_one_of_mem_Icc hδ h₁.le h₂.le]
    · -- `v + δ < x`: both vanish
      rw [smoothIndicatorUpper, window_eq_zero_of_ge hδ h₂.le, smoothIndicatorLower,
        window_eq_zero_of_ge hδ (by linarith)]

/-- **The smoothing estimate.**  `0 ≤ φ⁺ - φ⁻ ≤ 1_N` with `N` the `δ`-neighbourhood of the two
endpoints, so that `∫ (φ⁺ - φ⁻) dμ ≤ μ N`: the cost of smoothing is the mass the law puts within
`δ` of an endpoint. -/
lemma smoothIndicatorUpper_sub_lower_le_indicator {δ u v : ℝ} (hδ : 0 < δ) (x : ℝ) :
    smoothIndicatorUpper δ u v x - smoothIndicatorLower δ u v x
      ≤ (Set.Icc (u - δ) (u + δ) ∪ Set.Icc (v - δ) (v + δ)).indicator (1 : ℝ → ℝ) x := by
  by_cases hx : x ∈ Set.Icc (u - δ) (u + δ) ∪ Set.Icc (v - δ) (v + δ)
  · rw [Set.indicator_of_mem hx, Pi.one_apply]
    have h₁ := smoothIndicatorUpper_le_one δ u v x
    have h₂ := smoothIndicatorLower_nonneg δ u v x
    linarith
  · rw [Set.indicator_of_notMem hx, smoothIndicatorUpper_eq_lower_of_notMem hδ hx, sub_self]

/-! ### Derivative bounds

Each factor of the window is `S` composed with an affine map of slope `±1/δ`, so its `k`-th
derivative is `±S^{(k)}((x∓a)/δ)/δ^k`.  Leibniz for the product then gives

`‖w′‖ ≤ 2C₁/δ`,  `‖w′′‖ ≤ (2C₂ + 2C₁²)/δ²`,  `‖w′′′‖ ≤ (2C₃ + 6C₁C₂)/δ³`,

with `C₁ = 35/16`, `C₂ = 105/4`, `C₃ = 105/2` the constants of `RMF/Analysis/Smoothstep.lean`.
Numerically `35/8`, `≤ 63`, `≤ 450`. -/

/-- `HasDerivAt` for `RMF.smoothstep`, phrased through `deriv` so it composes. -/
lemma hasDerivAt_smoothstep' (x : ℝ) : HasDerivAt smoothstep (deriv smoothstep x) x := by
  rw [deriv_smoothstep]
  exact hasDerivAt_smoothstep x

lemma hasDerivAt_deriv_smoothstep' (x : ℝ) :
    HasDerivAt (deriv smoothstep) (deriv (deriv smoothstep) x) x := by
  rw [deriv2_smoothstep]
  exact hasDerivAt_deriv_smoothstep x

lemma hasDerivAt_deriv2_smoothstep' (x : ℝ) :
    HasDerivAt (deriv (deriv smoothstep)) (deriv (deriv (deriv smoothstep)) x) x := by
  rw [deriv3_smoothstep]
  exact hasDerivAt_deriv2_smoothstep x

/-- The chain rule for the rising factor: precomposition with `y ↦ (y - a)/δ` divides the
derivative by `δ`. -/
lemma hasDerivAt_comp_rise {F Fd : ℝ → ℝ} (hF : ∀ y, HasDerivAt F (Fd y) y) (δ a x : ℝ) :
    HasDerivAt (fun y : ℝ => F ((y - a) / δ)) (Fd ((x - a) / δ) / δ) x := by
  have hin : HasDerivAt (fun y : ℝ => (y - a) / δ) (1 / δ) x :=
    ((hasDerivAt_id x).sub_const a).div_const δ
  exact (HasDerivAt.comp x (hF ((x - a) / δ)) hin).congr_deriv (by ring)

/-- The chain rule for the falling factor; the slope is `-1/δ`, whence the sign. -/
lemma hasDerivAt_comp_fall {F Fd : ℝ → ℝ} (hF : ∀ y, HasDerivAt F (Fd y) y) (δ b x : ℝ) :
    HasDerivAt (fun y : ℝ => F ((b - y) / δ)) (-(Fd ((b - x) / δ) / δ)) x := by
  have hin : HasDerivAt (fun y : ℝ => (b - y) / δ) (-1 / δ) x :=
    (((hasDerivAt_const x b).sub (hasDerivAt_id x)).div_const δ).congr_deriv (by ring)
  exact (HasDerivAt.comp x (hF ((b - x) / δ)) hin).congr_deriv (by ring)

/-! #### The rising and falling factors, to three orders -/

lemma hasDerivAt_rise (δ a x : ℝ) :
    HasDerivAt (fun y : ℝ => smoothstep ((y - a) / δ))
      (deriv smoothstep ((x - a) / δ) / δ) x :=
  hasDerivAt_comp_rise hasDerivAt_smoothstep' δ a x

lemma hasDerivAt_rise₁ (δ a x : ℝ) :
    HasDerivAt (fun y : ℝ => deriv smoothstep ((y - a) / δ) / δ)
      (deriv (deriv smoothstep) ((x - a) / δ) / δ / δ) x :=
  (hasDerivAt_comp_rise hasDerivAt_deriv_smoothstep' δ a x).div_const δ

lemma hasDerivAt_rise₂ (δ a x : ℝ) :
    HasDerivAt (fun y : ℝ => deriv (deriv smoothstep) ((y - a) / δ) / δ / δ)
      (deriv (deriv (deriv smoothstep)) ((x - a) / δ) / δ / δ / δ) x :=
  ((hasDerivAt_comp_rise hasDerivAt_deriv2_smoothstep' δ a x).div_const δ).div_const δ

lemma hasDerivAt_fall (δ b x : ℝ) :
    HasDerivAt (fun y : ℝ => smoothstep ((b - y) / δ))
      (-(deriv smoothstep ((b - x) / δ) / δ)) x :=
  hasDerivAt_comp_fall hasDerivAt_smoothstep' δ b x

lemma hasDerivAt_fall₁ (δ b x : ℝ) :
    HasDerivAt (fun y : ℝ => -(deriv smoothstep ((b - y) / δ) / δ))
      (deriv (deriv smoothstep) ((b - x) / δ) / δ / δ) x :=
  (((hasDerivAt_comp_fall hasDerivAt_deriv_smoothstep' δ b x).div_const δ).neg).congr_deriv
    (by ring)

lemma hasDerivAt_fall₂ (δ b x : ℝ) :
    HasDerivAt (fun y : ℝ => deriv (deriv smoothstep) ((b - y) / δ) / δ / δ)
      (-(deriv (deriv (deriv smoothstep)) ((b - x) / δ) / δ / δ / δ)) x :=
  (((hasDerivAt_comp_fall hasDerivAt_deriv2_smoothstep' δ b x).div_const δ).div_const
    δ).congr_deriv (by ring)

/-! #### The window -/

/-- The first derivative of the window, by the product rule. -/
lemma hasDerivAt_window (δ a b x : ℝ) :
    HasDerivAt (window δ a b)
      (deriv smoothstep ((x - a) / δ) / δ * smoothstep ((b - x) / δ)
        + smoothstep ((x - a) / δ) * -(deriv smoothstep ((b - x) / δ) / δ)) x :=
  (hasDerivAt_rise δ a x).mul (hasDerivAt_fall δ b x)

lemma deriv_window (δ a b x : ℝ) :
    deriv (window δ a b) x
      = deriv smoothstep ((x - a) / δ) / δ * smoothstep ((b - x) / δ)
        + smoothstep ((x - a) / δ) * -(deriv smoothstep ((b - x) / δ) / δ) :=
  (hasDerivAt_window δ a b x).deriv

/-- **The first derivative bound**, `‖w′‖ ≤ (35/8)/δ`. -/
lemma abs_deriv_window_le {δ : ℝ} (hδ : 0 < δ) (a b x : ℝ) :
    |deriv (window δ a b) x| ≤ 35 / 8 / δ := by
  rw [deriv_window]
  have h1 := abs_deriv_smoothstep_le ((x - a) / δ)
  have h2 := abs_deriv_smoothstep_le ((b - x) / δ)
  have h3 : |smoothstep ((b - x) / δ)| ≤ 1 := by
    rw [abs_of_nonneg (smoothstep_nonneg _)]; exact smoothstep_le_one _
  have h4 : |smoothstep ((x - a) / δ)| ≤ 1 := by
    rw [abs_of_nonneg (smoothstep_nonneg _)]; exact smoothstep_le_one _
  calc |deriv smoothstep ((x - a) / δ) / δ * smoothstep ((b - x) / δ)
          + smoothstep ((x - a) / δ) * -(deriv smoothstep ((b - x) / δ) / δ)|
      ≤ |deriv smoothstep ((x - a) / δ) / δ * smoothstep ((b - x) / δ)|
        + |smoothstep ((x - a) / δ) * -(deriv smoothstep ((b - x) / δ) / δ)| := abs_add_le _ _
    _ ≤ 35 / 16 / δ * 1 + 1 * (35 / 16 / δ) := by
        rw [abs_mul, abs_mul, abs_neg, abs_div, abs_div, abs_of_pos hδ]
        gcongr
    _ = 35 / 8 / δ := by ring

/-! #### The window, second and third order

Leibniz on `w = R·F`, with `R y = S((y-a)/δ)` and `F y = S((b-y)/δ)`.  The `HasDerivAt` chains for
`R` and `F` to three orders are `RMF.hasDerivAt_rise`–`₂` and `RMF.hasDerivAt_fall`–`₂` above, so
each order is one product rule and one `ring`.  The constants come out as `7945/128 < 63` and
`14385/32 < 450`; the third order is the last one needed, `M₃` being what the Lindeberg swap
pays. -/

/-- The first derivative of the window, as a function — the form the second derivative
differentiates. -/
lemma deriv_window_eq (δ a b : ℝ) :
    deriv (window δ a b) = fun x =>
      deriv smoothstep ((x - a) / δ) / δ * smoothstep ((b - x) / δ)
        + smoothstep ((x - a) / δ) * -(deriv smoothstep ((b - x) / δ) / δ) :=
  funext (deriv_window δ a b)

/-- **The second derivative**, `w′′ = R′′F + 2R′F′ + RF′′`. -/
lemma hasDerivAt_deriv_window (δ a b x : ℝ) :
    HasDerivAt (deriv (window δ a b))
      (deriv (deriv smoothstep) ((x - a) / δ) / δ / δ * smoothstep ((b - x) / δ)
        + 2 * (deriv smoothstep ((x - a) / δ) / δ
            * -(deriv smoothstep ((b - x) / δ) / δ))
        + smoothstep ((x - a) / δ) * (deriv (deriv smoothstep) ((b - x) / δ) / δ / δ)) x := by
  rw [deriv_window_eq]
  exact (((hasDerivAt_rise₁ δ a x).mul (hasDerivAt_fall δ b x)).add
    ((hasDerivAt_rise δ a x).mul (hasDerivAt_fall₁ δ b x))).congr_deriv (by ring)

lemma deriv2_window (δ a b x : ℝ) :
    deriv (deriv (window δ a b)) x
      = deriv (deriv smoothstep) ((x - a) / δ) / δ / δ * smoothstep ((b - x) / δ)
        + 2 * (deriv smoothstep ((x - a) / δ) / δ
            * -(deriv smoothstep ((b - x) / δ) / δ))
        + smoothstep ((x - a) / δ) * (deriv (deriv smoothstep) ((b - x) / δ) / δ / δ) :=
  (hasDerivAt_deriv_window δ a b x).deriv

lemma deriv2_window_eq (δ a b : ℝ) :
    deriv (deriv (window δ a b)) = fun x =>
      deriv (deriv smoothstep) ((x - a) / δ) / δ / δ * smoothstep ((b - x) / δ)
        + 2 * (deriv smoothstep ((x - a) / δ) / δ
            * -(deriv smoothstep ((b - x) / δ) / δ))
        + smoothstep ((x - a) / δ) * (deriv (deriv smoothstep) ((b - x) / δ) / δ / δ) :=
  funext (deriv2_window δ a b)

/-- **The third derivative**, `w′′′ = R′′′F + 3R′′F′ + 3R′F′′ + RF′′′`. -/
lemma hasDerivAt_deriv2_window (δ a b x : ℝ) :
    HasDerivAt (deriv (deriv (window δ a b)))
      (deriv (deriv (deriv smoothstep)) ((x - a) / δ) / δ / δ / δ
            * smoothstep ((b - x) / δ)
        + 3 * (deriv (deriv smoothstep) ((x - a) / δ) / δ / δ
            * -(deriv smoothstep ((b - x) / δ) / δ))
        + 3 * (deriv smoothstep ((x - a) / δ) / δ
            * (deriv (deriv smoothstep) ((b - x) / δ) / δ / δ))
        + smoothstep ((x - a) / δ)
            * -(deriv (deriv (deriv smoothstep)) ((b - x) / δ) / δ / δ / δ)) x := by
  rw [deriv2_window_eq]
  exact ((((hasDerivAt_rise₂ δ a x).mul (hasDerivAt_fall δ b x)).add
    (((hasDerivAt_rise₁ δ a x).mul (hasDerivAt_fall₁ δ b x)).const_mul 2)).add
    ((hasDerivAt_rise δ a x).mul (hasDerivAt_fall₂ δ b x))).congr_deriv (by ring)

lemma deriv3_window (δ a b x : ℝ) :
    deriv (deriv (deriv (window δ a b))) x
      = deriv (deriv (deriv smoothstep)) ((x - a) / δ) / δ / δ / δ
            * smoothstep ((b - x) / δ)
        + 3 * (deriv (deriv smoothstep) ((x - a) / δ) / δ / δ
            * -(deriv smoothstep ((b - x) / δ) / δ))
        + 3 * (deriv smoothstep ((x - a) / δ) / δ
            * (deriv (deriv smoothstep) ((b - x) / δ) / δ / δ))
        + smoothstep ((x - a) / δ)
            * -(deriv (deriv (deriv smoothstep)) ((b - x) / δ) / δ / δ / δ) :=
  (hasDerivAt_deriv2_window δ a b x).deriv

/-- **The second derivative bound**, `‖w′′‖ ≤ 63/δ²`. -/
lemma abs_deriv2_window_le {δ : ℝ} (hδ : 0 < δ) (a b x : ℝ) :
    |deriv (deriv (window δ a b)) x| ≤ 63 / δ ^ 2 := by
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hs1 : |deriv smoothstep ((x - a) / δ)| ≤ 35 / 16 := abs_deriv_smoothstep_le _
  have hs2 : |deriv smoothstep ((b - x) / δ)| ≤ 35 / 16 := abs_deriv_smoothstep_le _
  have hd1 : |deriv (deriv smoothstep) ((x - a) / δ)| ≤ 105 / 4 := abs_deriv2_smoothstep_le _
  have hd2 : |deriv (deriv smoothstep) ((b - x) / δ)| ≤ 105 / 4 := abs_deriv2_smoothstep_le _
  have hw1 : |smoothstep ((x - a) / δ)| ≤ 1 := by
    rw [abs_of_nonneg (smoothstep_nonneg _)]; exact smoothstep_le_one _
  have hw2 : |smoothstep ((b - x) / δ)| ≤ 1 := by
    rw [abs_of_nonneg (smoothstep_nonneg _)]; exact smoothstep_le_one _
  rw [deriv2_window]
  have hA : |deriv (deriv smoothstep) ((x - a) / δ) / δ / δ * smoothstep ((b - x) / δ)|
      ≤ 105 / 4 / δ ^ 2 := by
    rw [abs_mul, abs_div, abs_div, abs_of_pos hδ, div_div, ← pow_two]
    calc |deriv (deriv smoothstep) ((x - a) / δ)| / δ ^ 2 * |smoothstep ((b - x) / δ)|
        ≤ 105 / 4 / δ ^ 2 * 1 := by gcongr
      _ = 105 / 4 / δ ^ 2 := by ring
  have hB : |2 * (deriv smoothstep ((x - a) / δ) / δ
      * -(deriv smoothstep ((b - x) / δ) / δ))| ≤ 1225 / 128 / δ ^ 2 := by
    rw [abs_mul, abs_mul, abs_neg, abs_div, abs_div, abs_of_pos hδ]
    calc |(2 : ℝ)| * (|deriv smoothstep ((x - a) / δ)| / δ
          * (|deriv smoothstep ((b - x) / δ)| / δ))
        ≤ |(2 : ℝ)| * (35 / 16 / δ * (35 / 16 / δ)) := by gcongr
      _ = 1225 / 128 / δ ^ 2 := by rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; field_simp; ring
  have hC : |smoothstep ((x - a) / δ) * (deriv (deriv smoothstep) ((b - x) / δ) / δ / δ)|
      ≤ 105 / 4 / δ ^ 2 := by
    rw [abs_mul, abs_div, abs_div, abs_of_pos hδ, div_div, ← pow_two]
    calc |smoothstep ((x - a) / δ)| * (|deriv (deriv smoothstep) ((b - x) / δ)| / δ ^ 2)
        ≤ 1 * (105 / 4 / δ ^ 2) := by gcongr
      _ = 105 / 4 / δ ^ 2 := by ring
  have hsum : 105 / 4 / δ ^ 2 + 1225 / 128 / δ ^ 2 + 105 / 4 / δ ^ 2 ≤ 63 / δ ^ 2 := by
    rw [show (105 : ℝ) / 4 / δ ^ 2 + 1225 / 128 / δ ^ 2 + 105 / 4 / δ ^ 2
        = 7945 / 128 / δ ^ 2 from by ring]
    exact div_le_div_of_nonneg_right (by norm_num) hδ2.le
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (abs_add_le _ _) le_rfl) ?_
  linarith

/-- **The third derivative bound**, `‖w′′′‖ ≤ 450/δ³`.  This is the `M₃` of the Lindeberg swap. -/
lemma abs_deriv3_window_le {δ : ℝ} (hδ : 0 < δ) (a b x : ℝ) :
    |deriv (deriv (deriv (window δ a b))) x| ≤ 450 / δ ^ 3 := by
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hδ3 : (0 : ℝ) < δ ^ 3 := by positivity
  have hs1 : |deriv smoothstep ((x - a) / δ)| ≤ 35 / 16 := abs_deriv_smoothstep_le _
  have hs2 : |deriv smoothstep ((b - x) / δ)| ≤ 35 / 16 := abs_deriv_smoothstep_le _
  have hd1 : |deriv (deriv smoothstep) ((x - a) / δ)| ≤ 105 / 4 := abs_deriv2_smoothstep_le _
  have hd2 : |deriv (deriv smoothstep) ((b - x) / δ)| ≤ 105 / 4 := abs_deriv2_smoothstep_le _
  have ht1 : |deriv (deriv (deriv smoothstep)) ((x - a) / δ)| ≤ 105 / 2 :=
    abs_deriv3_smoothstep_le _
  have ht2 : |deriv (deriv (deriv smoothstep)) ((b - x) / δ)| ≤ 105 / 2 :=
    abs_deriv3_smoothstep_le _
  have hw1 : |smoothstep ((x - a) / δ)| ≤ 1 := by
    rw [abs_of_nonneg (smoothstep_nonneg _)]; exact smoothstep_le_one _
  have hw2 : |smoothstep ((b - x) / δ)| ≤ 1 := by
    rw [abs_of_nonneg (smoothstep_nonneg _)]; exact smoothstep_le_one _
  rw [deriv3_window]
  have hA : |deriv (deriv (deriv smoothstep)) ((x - a) / δ) / δ / δ / δ
      * smoothstep ((b - x) / δ)| ≤ 105 / 2 / δ ^ 3 := by
    rw [abs_mul, abs_div, abs_div, abs_div, abs_of_pos hδ, div_div, div_div,
      show δ * (δ * δ) = δ ^ 3 from by ring]
    calc |deriv (deriv (deriv smoothstep)) ((x - a) / δ)| / δ ^ 3
          * |smoothstep ((b - x) / δ)|
        ≤ 105 / 2 / δ ^ 3 * 1 := by gcongr
      _ = 105 / 2 / δ ^ 3 := by ring
  have hB : |3 * (deriv (deriv smoothstep) ((x - a) / δ) / δ / δ
      * -(deriv smoothstep ((b - x) / δ) / δ))| ≤ 11025 / 64 / δ ^ 3 := by
    rw [abs_mul, abs_mul, abs_neg, abs_div, abs_div, abs_div, abs_of_pos hδ]
    calc |(3 : ℝ)| * (|deriv (deriv smoothstep) ((x - a) / δ)| / δ / δ
          * (|deriv smoothstep ((b - x) / δ)| / δ))
        ≤ |(3 : ℝ)| * (105 / 4 / δ / δ * (35 / 16 / δ)) := by gcongr
      _ = 11025 / 64 / δ ^ 3 := by
          rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]; field_simp; ring
  have hC : |3 * (deriv smoothstep ((x - a) / δ) / δ
      * (deriv (deriv smoothstep) ((b - x) / δ) / δ / δ))| ≤ 11025 / 64 / δ ^ 3 := by
    rw [abs_mul, abs_mul, abs_div, abs_div, abs_div, abs_of_pos hδ]
    calc |(3 : ℝ)| * (|deriv smoothstep ((x - a) / δ)| / δ
          * (|deriv (deriv smoothstep) ((b - x) / δ)| / δ / δ))
        ≤ |(3 : ℝ)| * (35 / 16 / δ * (105 / 4 / δ / δ)) := by gcongr
      _ = 11025 / 64 / δ ^ 3 := by
          rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]; field_simp; ring
  have hD : |smoothstep ((x - a) / δ)
      * -(deriv (deriv (deriv smoothstep)) ((b - x) / δ) / δ / δ / δ)| ≤ 105 / 2 / δ ^ 3 := by
    rw [abs_mul, abs_neg, abs_div, abs_div, abs_div, abs_of_pos hδ, div_div, div_div,
      show δ * (δ * δ) = δ ^ 3 from by ring]
    calc |smoothstep ((x - a) / δ)|
          * (|deriv (deriv (deriv smoothstep)) ((b - x) / δ)| / δ ^ 3)
        ≤ 1 * (105 / 2 / δ ^ 3) := by gcongr
      _ = 105 / 2 / δ ^ 3 := by ring
  have hsum : 105 / 2 / δ ^ 3 + 11025 / 64 / δ ^ 3 + 11025 / 64 / δ ^ 3 + 105 / 2 / δ ^ 3
      ≤ 450 / δ ^ 3 := by
    rw [show (105 : ℝ) / 2 / δ ^ 3 + 11025 / 64 / δ ^ 3 + 11025 / 64 / δ ^ 3 + 105 / 2 / δ ^ 3
        = 14385 / 32 / δ ^ 3 from by ring]
    exact div_le_div_of_nonneg_right (by norm_num) hδ3.le
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (abs_add_le _ _) le_rfl) ?_
  refine le_trans (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) ?_
  linarith

/-! ### The sandwich on the plane

The two-point argument compares the law of a *pair* on a box, so it needs the same sandwich for
`φ(z₁)φ(z₂)` against `1_{I₁×I₂}`.  All three parts are the one-dimensional ones multiplied, and
the only step that is not immediate is the collar: the naive bound is
`1_{Cl₁}(z₁) + 1_{Cl₂}(z₂)`, which reaches `2`, but the difference of two things in `[0,1]` never
exceeds `1`, and off the union both factors agree.  So the union is the right collar and the
constant stays `1`. -/

/-- The collar of a window: the two `δ`-neighbourhoods of its endpoints. -/
def smoothCollar (δ u v : ℝ) : Set ℝ :=
  Set.Icc (u - δ) (u + δ) ∪ Set.Icc (v - δ) (v + δ)

/-- **Lower half of the product sandwich.**  `φ⁻⊗φ⁻ ≤ 1_{I₁×I₂}`. -/
lemma prod_smoothIndicatorLower_le_indicator {δ u₁ v₁ u₂ v₂ : ℝ} (hδ : 0 < δ) (z : ℝ × ℝ) :
    smoothIndicatorLower δ u₁ v₁ z.1 * smoothIndicatorLower δ u₂ v₂ z.2
      ≤ (Set.Ioc u₁ v₁ ×ˢ Set.Ioc u₂ v₂).indicator (1 : ℝ × ℝ → ℝ) z := by
  by_cases hz : z ∈ Set.Ioc u₁ v₁ ×ˢ Set.Ioc u₂ v₂
  · rw [Set.indicator_of_mem hz, Pi.one_apply]
    calc smoothIndicatorLower δ u₁ v₁ z.1 * smoothIndicatorLower δ u₂ v₂ z.2 ≤ 1 * 1 :=
          mul_le_mul (window_le_one _ _ _ _) (window_le_one _ _ _ _)
            (smoothIndicatorLower_nonneg _ _ _ _) zero_le_one
      _ = 1 := one_mul 1
  · rw [Set.indicator_of_notMem hz]
    rw [Set.mem_prod, not_and_or] at hz
    rcases hz with h | h
    · have h1 := smoothIndicatorLower_le_indicator_Ioc (δ := δ) (u := u₁) (v := v₁) hδ z.1
      rw [Set.indicator_of_notMem h] at h1
      have h2 := smoothIndicatorLower_nonneg δ u₂ v₂ z.2
      nlinarith [smoothIndicatorLower_nonneg δ u₁ v₁ z.1]
    · have h1 := smoothIndicatorLower_le_indicator_Ioc (δ := δ) (u := u₂) (v := v₂) hδ z.2
      rw [Set.indicator_of_notMem h] at h1
      nlinarith [smoothIndicatorLower_nonneg δ u₁ v₁ z.1,
        smoothIndicatorLower_nonneg δ u₂ v₂ z.2]

/-- **Upper half of the product sandwich.**  `1_{I₁×I₂} ≤ φ⁺⊗φ⁺`. -/
lemma indicator_le_prod_smoothIndicatorUpper {δ u₁ v₁ u₂ v₂ : ℝ} (hδ : 0 < δ) (z : ℝ × ℝ) :
    (Set.Ioc u₁ v₁ ×ˢ Set.Ioc u₂ v₂).indicator (1 : ℝ × ℝ → ℝ) z
      ≤ smoothIndicatorUpper δ u₁ v₁ z.1 * smoothIndicatorUpper δ u₂ v₂ z.2 := by
  by_cases hz : z ∈ Set.Ioc u₁ v₁ ×ˢ Set.Ioc u₂ v₂
  · rw [Set.indicator_of_mem hz, Pi.one_apply]
    rw [Set.mem_prod] at hz
    have h1 := indicator_Ioc_le_smoothIndicatorUpper (δ := δ) (u := u₁) (v := v₁) hδ z.1
    have h2 := indicator_Ioc_le_smoothIndicatorUpper (δ := δ) (u := u₂) (v := v₂) hδ z.2
    rw [Set.indicator_of_mem hz.1, Pi.one_apply] at h1
    rw [Set.indicator_of_mem hz.2, Pi.one_apply] at h2
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ smoothIndicatorUpper δ u₁ v₁ z.1 * smoothIndicatorUpper δ u₂ v₂ z.2 :=
          mul_le_mul h1 h2 zero_le_one (by linarith)
  · rw [Set.indicator_of_notMem hz]
    exact mul_nonneg (window_nonneg _ _ _ _) (window_nonneg _ _ _ _)

/-- **The collar of the product sandwich.**  Off `Cl₁×ℝ ∪ ℝ×Cl₂` the two products agree, and on it
the difference of two things in `[0,1]` is at most `1`. -/
lemma prod_smoothIndicatorUpper_sub_lower_le_indicator {δ u₁ v₁ u₂ v₂ : ℝ} (hδ : 0 < δ)
    (z : ℝ × ℝ) :
    smoothIndicatorUpper δ u₁ v₁ z.1 * smoothIndicatorUpper δ u₂ v₂ z.2
        - smoothIndicatorLower δ u₁ v₁ z.1 * smoothIndicatorLower δ u₂ v₂ z.2
      ≤ (smoothCollar δ u₁ v₁ ×ˢ (Set.univ : Set ℝ)
          ∪ (Set.univ : Set ℝ) ×ˢ smoothCollar δ u₂ v₂).indicator (1 : ℝ × ℝ → ℝ) z := by
  by_cases hz : z ∈ smoothCollar δ u₁ v₁ ×ˢ (Set.univ : Set ℝ)
      ∪ (Set.univ : Set ℝ) ×ˢ smoothCollar δ u₂ v₂
  · rw [Set.indicator_of_mem hz, Pi.one_apply]
    have hu1 := smoothIndicatorUpper_le_one δ u₁ v₁ z.1
    have hu2 := smoothIndicatorUpper_le_one δ u₂ v₂ z.2
    have hl1 := smoothIndicatorLower_nonneg δ u₁ v₁ z.1
    have hl2 := smoothIndicatorLower_nonneg δ u₂ v₂ z.2
    have hup : smoothIndicatorUpper δ u₁ v₁ z.1 * smoothIndicatorUpper δ u₂ v₂ z.2 ≤ 1 := by
      calc smoothIndicatorUpper δ u₁ v₁ z.1 * smoothIndicatorUpper δ u₂ v₂ z.2 ≤ 1 * 1 :=
            mul_le_mul hu1 hu2 (window_nonneg _ _ _ _) zero_le_one
        _ = 1 := one_mul 1
    have hlo : (0 : ℝ)
        ≤ smoothIndicatorLower δ u₁ v₁ z.1 * smoothIndicatorLower δ u₂ v₂ z.2 :=
      mul_nonneg hl1 hl2
    linarith
  · rw [Set.indicator_of_notMem hz]
    rw [Set.mem_union, not_or, Set.mem_prod, Set.mem_prod, not_and_or, not_and_or] at hz
    have h1 : z.1 ∉ smoothCollar δ u₁ v₁ := by
      rcases hz.1 with h | h
      · exact h
      · exact absurd (Set.mem_univ z.2) h
    have h2 : z.2 ∉ smoothCollar δ u₂ v₂ := by
      rcases hz.2 with h | h
      · exact absurd (Set.mem_univ z.1) h
      · exact h
    rw [smoothIndicatorUpper_eq_lower_of_notMem hδ h1,
      smoothIndicatorUpper_eq_lower_of_notMem hδ h2, sub_self]

end RMF
