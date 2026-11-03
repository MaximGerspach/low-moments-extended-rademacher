/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.Khintchine
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Bonami–Beckner hypercontractivity for Rademacher chaos

For independent Rademacher variables `Y_i` and complex coefficients `c_A`, `A` running over the
subsets of a finite index set `S`,

`(∑_A (p-1)^{|A|} |c_A|²)^{p/2} ≤ E|∑_A c_A Y_A|^p`   for `1 ≤ p ≤ 2`,
`E|∑_A c_A Y_A|^r ≤ (∑_A (r-1)^{|A|} |c_A|²)^{r/2}`   for `r ≥ 2`,

`Y_A = ∏_{i∈A} Y_i` (`RMF.chaosNormSq_rpow_le_integral`, `RMF.integral_rpow_le_chaosNormSq`).
These are the `(p → 2)` and `(2 → r)` hypercontractive inequalities of Bonami and Beckner,
O'Donnell, *Analysis of Boolean functions*, Thm. 9.22, written for the coefficients.  The general
`(p → r)` inequality with `2 < p < r` is not proved here.  Also: dropping indices contracts every
`L^r`, `r ≥ 1` (`RMF.integral_rpow_chaosSum_le_of_subset`, conditional expectation).

## The proof

By induction over `S`, at the level of coefficients, so that neither the Fourier–Walsh expansion
nor Minkowski's integral inequality is needed.  Splitting off one index `i`,
`∑_A c_A Y_A = g + Y_i h`, and integrating `Y_i` out (it is independent of `g, h`),

`E|g + Y_i h|^p = ½ (E|g + h|^p + E|g - h|^p)`,

and `g ± h` are again chaos sums over the smaller set.  The induction hypothesis bounds both, and
the step reduces to a **vector two-point inequality** in the weighted `ℓ²` of coefficients
(`RMF.rpow_le_vector_two_point`): with `α² = N(g)`, `β² = N(h)` and `γ = Re⟨g, h⟩`,

`(α² + (p-1)β²)^{p/2} ≤ ½ ((α²+β²+2γ)^{p/2} + (α²+β²-2γ)^{p/2})`.

Concavity of `u ↦ u^{p/2}` moves `γ` out to `±αβ`, and there it is the scalar two-point inequality
`(a² + (p-1)b²)^{p/2} ≤ ½ (|a+b|^p + |a-b|^p)` (`RMF.rpow_le_two_point`), which for `p ≤ 2` is
Bernoulli's inequality on the left against `(1+s)^p + (1-s)^p ≥ 2 + p(p-1)s²` on the right.  The
`r ≥ 2` case is its dual on the two-point space (`RMF.two_point_le_rpow`), with convexity in
place of concavity.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-! ### The scalar two-point inequality, `1 ≤ p ≤ 2` -/

/-- `2αt ≤ (1+t)^α - (1-t)^α` for `α, t ∈ [0,1]`: the derivative of the difference is
`α((1+t)^{α-1} + (1-t)^{α-1} - 2) ≥ 0`, by AM-GM and `(1-t²)^{α-1} ≥ 1`. -/
lemma two_mul_mul_le_one_add_rpow_sub {α t : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    2 * α * t ≤ (1 + t) ^ α - (1 - t) ^ α := by
  have hmono : MonotoneOn (fun s : ℝ => (1 + s) ^ α - (1 - s) ^ α - 2 * α * s)
      (Set.Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · have h1 : Continuous fun s : ℝ => (1 + s) ^ α :=
        (Real.continuous_rpow_const hα0).comp (continuous_const.add continuous_id)
      have h2 : Continuous fun s : ℝ => (1 - s) ^ α :=
        (Real.continuous_rpow_const hα0).comp (continuous_const.sub continuous_id)
      exact ((h1.sub h2).sub (continuous_const.mul continuous_id)).continuousOn
    · rw [interior_Icc]
      intro s hs
      have hs1 : (1 + s) ≠ 0 := by linarith [hs.1]
      have hs2 : (1 - s) ≠ 0 := by linarith [hs.2]
      have d1 := ((hasDerivAt_id s).const_add 1).rpow_const (p := α) (Or.inl hs1)
      have d2 := ((hasDerivAt_id s).const_sub 1).rpow_const (p := α) (Or.inl hs2)
      have d3 := (hasDerivAt_id s).const_mul (2 * α)
      exact ((d1.sub d2).sub d3).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      have hs1 : 0 < 1 + s := by linarith [hs.1]
      have hs2 : 0 < 1 - s := by linarith [hs.2]
      have d1 := ((hasDerivAt_id' s).const_add 1).rpow_const (p := α) (Or.inl hs1.ne')
      have d2 := ((hasDerivAt_id' s).const_sub 1).rpow_const (p := α) (Or.inl hs2.ne')
      have d3 := (hasDerivAt_id' s).const_mul (2 * α)
      have d : HasDerivAt (fun s : ℝ => (1 + s) ^ α - (1 - s) ^ α - 2 * α * s)
          (1 * α * (1 + s) ^ (α - 1) - -1 * α * (1 - s) ^ (α - 1) - 2 * α * 1) s :=
        (d1.sub d2).sub d3
      rw [d.deriv]
      -- `u + v ≥ 2` for `u = (1+s)^{α-1}`, `v = (1-s)^{α-1}`
      have hu : 0 < (1 + s) ^ (α - 1) := Real.rpow_pos_of_pos hs1 _
      have hv : 0 < (1 - s) ^ (α - 1) := Real.rpow_pos_of_pos hs2 _
      have huv : 1 ≤ (1 + s) ^ (α - 1) * (1 - s) ^ (α - 1) := by
        rw [← Real.mul_rpow hs1.le hs2.le]
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (mul_pos hs1 hs2)
          (by nlinarith [sq_nonneg s]) (by linarith)
      have hsum : 2 ≤ (1 + s) ^ (α - 1) + (1 - s) ^ (α - 1) := by
        nlinarith [sq_nonneg ((1 + s) ^ (α - 1) - (1 - s) ^ (α - 1))]
      nlinarith
  have h := hmono ⟨le_refl 0, zero_le_one⟩ ⟨ht0, ht1⟩ ht0
  simp only [add_zero, sub_zero, Real.one_rpow, mul_zero, sub_self] at h
  linarith

/-- `2 + p(p-1)s² ≤ (1+s)^p + (1-s)^p` for `p ∈ [1,2]` and `s ∈ [0,1]`: the derivative of the
difference is `p((1+s)^{p-1} - (1-s)^{p-1} - 2(p-1)s) ≥ 0`. -/
lemma two_add_mul_sq_le_rpow_add_rpow {p s : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    2 + p * (p - 1) * s ^ 2 ≤ (1 + s) ^ p + (1 - s) ^ p := by
  have hmono : MonotoneOn (fun u : ℝ => (1 + u) ^ p + (1 - u) ^ p - 2 - p * (p - 1) * u ^ 2)
      (Set.Icc 0 1) := by
    have d : ∀ u : ℝ, HasDerivAt (fun u : ℝ => (1 + u) ^ p + (1 - u) ^ p - 2 - p * (p - 1) * u ^ 2)
        (1 * p * (1 + u) ^ (p - 1) + (-1) * p * (1 - u) ^ (p - 1) - 0
          - p * (p - 1) * (↑2 * u ^ (2 - 1) * 1)) u := by
      intro u
      have d1 := ((hasDerivAt_id u).const_add 1).rpow_const (p := p) (Or.inr hp1)
      have d2 := ((hasDerivAt_id u).const_sub 1).rpow_const (p := p) (Or.inr hp1)
      have d4 := ((hasDerivAt_id u).pow 2).const_mul (p * (p - 1))
      exact ((d1.add d2).sub (hasDerivAt_const u (2 : ℝ))).sub d4
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun u _ => (d u).continuousAt.continuousWithinAt)
      (fun u _ => (d u).differentiableAt.differentiableWithinAt) ?_
    rw [interior_Icc]
    intro u hu
    rw [(d u).deriv]
    have h := two_mul_mul_le_one_add_rpow_sub (α := p - 1) (by linarith) (by linarith) hu.1.le
      hu.2.le
    have hp' := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ p by linarith)
    norm_num
    nlinarith
  have h := hmono ⟨le_refl 0, zero_le_one⟩ ⟨hs0, hs1⟩ hs0
  simp only [add_zero, sub_zero, Real.one_rpow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero] at h
  linarith

/-- **The scalar two-point inequality at `a = 1`**, `1 ≤ p ≤ 2`, `s ≥ 0`:
`(1 + (p-1)s²)^{p/2} ≤ ½((1+s)^p + |1-s|^p)`.  Bernoulli on the left; for `s > 1` the case
`1/s` after pulling out `s^p`. -/
lemma one_add_mul_sq_rpow_le_two_point {p s : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hs : 0 ≤ s) :
    (1 + (p - 1) * s ^ 2) ^ (p / 2) ≤ ((1 + s) ^ p + |1 - s| ^ p) / 2 := by
  rcases le_total s 1 with hs1 | hs1
  · rw [abs_of_nonneg (by linarith)]
    have hb := rpow_one_add_le_one_add_mul_self (s := (p - 1) * s ^ 2)
      (by nlinarith) (p := p / 2) (by linarith) (by linarith)
    have h2 := two_add_mul_sq_le_rpow_add_rpow hp1 hp2 hs hs1
    nlinarith
  · -- `s ≥ 1`: write everything at `u = 1/s`
    have hs0 : 0 < s := by linarith
    set u : ℝ := s⁻¹ with hudef
    have hu0 : 0 < u := inv_pos.2 hs0
    have hu1 : u ≤ 1 := inv_le_one_of_one_le₀ hs1
    have hsu : s * u = 1 := mul_inv_cancel₀ hs0.ne'
    rw [abs_of_nonpos (by linarith), neg_sub]
    have h1s : 1 + s = s * (1 + u) := by rw [mul_add, hsu, mul_one, add_comm]
    have hs1' : s - 1 = s * (1 - u) := by rw [mul_sub, hsu, mul_one]
    rw [h1s, hs1', Real.mul_rpow hs0.le (by linarith), Real.mul_rpow hs0.le (by linarith)]
    have h2 := two_add_mul_sq_le_rpow_add_rpow hp1 hp2 hu0.le hu1
    -- the left side is `s^p (p - 1 + u²)^{p/2}`
    have hL : 1 + (p - 1) * s ^ 2 = s ^ 2 * (p - 1 + u ^ 2) := by
      have : s ^ 2 * u ^ 2 = 1 := by rw [← mul_pow, hsu, one_pow]
      nlinarith
    have hsp : (s ^ 2) ^ (p / 2) = s ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
      norm_num
      ring_nf
    rw [hL, Real.mul_rpow (by positivity) (by nlinarith), hsp]
    -- Bernoulli at `p - 2 + u² ≥ -1`
    have hb := rpow_one_add_le_one_add_mul_self (s := p - 2 + u ^ 2)
      (by nlinarith) (p := p / 2) (by linarith) (by linarith)
    have hb' : (p - 1 + u ^ 2) ^ (p / 2) ≤ 1 + p / 2 * (p - 1) * u ^ 2 := by
      have e : (1 : ℝ) + (p - 2 + u ^ 2) = p - 1 + u ^ 2 := by ring
      rw [e] at hb
      have hu2 : u ^ 2 ≤ 1 := by nlinarith
      have hk : 0 ≤ p / 2 * (2 - p) * (1 - u ^ 2) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      linarith
    have hsp0 : 0 < s ^ p := Real.rpow_pos_of_pos hs0 _
    have := mul_le_mul_of_nonneg_left hb' hsp0.le
    nlinarith

/-- `{|a+b|, |a-b|} = {|a|+|b|, ||a|-|b||}`, so the two-point sum sees only `|a|` and `|b|`. -/
lemma abs_add_rpow_add_abs_sub_rpow (a b p : ℝ) :
    |a + b| ^ p + |a - b| ^ p = (|a| + |b|) ^ p + |(|a| - |b|)| ^ p := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (add_nonneg ha hb)]
  · have h1 : |a - b| = |a| + |b| := by
      rw [abs_of_nonneg ha, abs_of_nonpos hb, abs_of_nonneg (by linarith : 0 ≤ a - b)]
      ring
    have h2 : |a + b| = |(|a| - |b|)| := by
      rw [abs_of_nonneg ha, abs_of_nonpos hb, sub_neg_eq_add]
    rw [h1, h2, add_comm]
  · have h1 : |a - b| = |a| + |b| := by
      rw [abs_of_nonpos ha, abs_of_nonneg hb, abs_of_nonpos (by linarith : a - b ≤ 0)]
      ring
    have h2 : |a + b| = |(|a| - |b|)| := by
      rw [abs_of_nonpos ha, abs_of_nonneg hb, show -a - b = -(a + b) by ring, abs_neg]
    rw [h1, h2, add_comm]
  · have h1 : |a + b| = |a| + |b| := by
      rw [abs_of_nonpos ha, abs_of_nonpos hb, abs_of_nonpos (by linarith : a + b ≤ 0)]
      ring
    have h2 : |a - b| = |(|a| - |b|)| := by
      rw [abs_of_nonpos ha, abs_of_nonpos hb, show -a - -b = -(a - b) by ring, abs_neg]
    rw [h1, h2]

/-- **The scalar two-point inequality**, `1 ≤ p ≤ 2`:
`(a² + (p-1)b²)^{p/2} ≤ ½(|a+b|^p + |a-b|^p)`, i.e. `‖a + √(p-1)·b·ε‖₂ ≤ ‖a + b·ε‖_p`. -/
theorem rpow_le_two_point {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (a b : ℝ) :
    (a ^ 2 + (p - 1) * b ^ 2) ^ (p / 2) ≤ (|a + b| ^ p + |a - b| ^ p) / 2 := by
  rw [abs_add_rpow_add_abs_sub_rpow, show a ^ 2 = |a| ^ 2 from (sq_abs a).symm,
    show b ^ 2 = |b| ^ 2 from (sq_abs b).symm]
  set a' := |a|
  set b' := |b|
  have ha : 0 ≤ a' := abs_nonneg a
  have hb : 0 ≤ b' := abs_nonneg b
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · -- `a = 0`
    rw [← ha0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, zero_sub,
      abs_neg]
    rw [abs_of_nonneg hb]
    have hp0 : 0 ≤ p - 1 := by linarith
    rw [Real.mul_rpow hp0 (sq_nonneg _), show (b' ^ 2) ^ (p / 2) = b' ^ p by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb]; norm_num; ring_nf]
    have hle : (p - 1) ^ (p / 2) ≤ 1 := Real.rpow_le_one hp0 (by linarith) (by linarith)
    have hbp : 0 ≤ b' ^ p := Real.rpow_nonneg hb _
    nlinarith
  · -- scale by `a`
    set s := b' / a' with hsdef
    have hs0 : 0 ≤ s := div_nonneg hb ha0.le
    have hb' : b' = a' * s := by rw [hsdef]; field_simp
    have h := one_add_mul_sq_rpow_le_two_point hp1 hp2 hs0
    have hL : a' ^ 2 + (p - 1) * b' ^ 2 = a' ^ 2 * (1 + (p - 1) * s ^ 2) := by rw [hb']; ring
    have hap : (a' ^ 2) ^ (p / 2) = a' ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num; ring_nf
    have hR1 : a' + b' = a' * (1 + s) := by rw [hb']; ring
    have hR2 : |a' - b'| = a' * |1 - s| := by
      rw [hb', show a' - a' * s = a' * (1 - s) by ring, abs_mul, abs_of_nonneg ha]
    rw [hL, Real.mul_rpow (sq_nonneg _) (by positivity), hap, hR1, hR2,
      Real.mul_rpow ha (by linarith), Real.mul_rpow ha (abs_nonneg _)]
    have hap0 : 0 ≤ a' ^ p := Real.rpow_nonneg ha _
    have := mul_le_mul_of_nonneg_left h hap0
    linarith

/-! ### The scalar two-point inequality, `r ≥ 2`, by duality on the two-point space -/

/-- `u · (u|u|^{r-2}) = |u|^r`. -/
lemma mul_mul_abs_rpow_sub_two {r : ℝ} (hr : 2 ≤ r) (u : ℝ) :
    u * (u * |u| ^ (r - 2)) = |u| ^ r := by
  rcases eq_or_ne u 0 with hu | hu
  · subst hu
    simp [Real.zero_rpow (by linarith : r ≠ 0)]
  · have hu0 : 0 < |u| := abs_pos.2 hu
    rw [← mul_assoc, ← sq, ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_add hu0]
    norm_num

/-- `|u·|u|^{r-2}|^{r'} = |u|^r` when `(r-1)r' = r`. -/
lemma abs_mul_abs_rpow_sub_two_rpow {r r' : ℝ} (hr : 2 ≤ r) (hr' : 0 < r')
    (hrr' : (r - 1) * r' = r) (u : ℝ) :
    |u * |u| ^ (r - 2)| ^ r' = |u| ^ r := by
  rcases eq_or_ne u 0 with hu | hu
  · subst hu
    simp [Real.zero_rpow hr'.ne', Real.zero_rpow (by linarith : r ≠ 0)]
  · have hu0 : 0 < |u| := abs_pos.2 hu
    have h1 : |u| * |u| ^ (r - 2) = |u| ^ (r - 1) := by
      rw [show r - 1 = 1 + (r - 2) by ring, Real.rpow_add hu0, Real.rpow_one]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _), h1, ← Real.rpow_mul hu0.le, hrr']

/-- **The scalar two-point inequality**, `r ≥ 2`:
`½(|a+s|^r + |a-s|^r) ≤ (a² + (r-1)s²)^{r/2}`, i.e. `‖a + b·ε/√(r-1)‖_r ≤ ‖a + b·ε‖₂`.

The dual of `RMF.rpow_le_two_point` at the conjugate exponent `r' = r/(r-1)`: with
`w = u|u|^{r-2}` at the two points `u = a ± s`, `M = E[uw] = ac + sd` for `w = c ± d`, and
Cauchy–Schwarz against `RMF.rpow_le_two_point` at `r'` gives `M ≤ (a²+(r-1)s²)^{1/2} M^{1/r'}`. -/
theorem two_point_le_rpow {r : ℝ} (hr : 2 ≤ r) (a s : ℝ) :
    (|a + s| ^ r + |a - s| ^ r) / 2 ≤ (a ^ 2 + (r - 1) * s ^ 2) ^ (r / 2) := by
  set M := (|a + s| ^ r + |a - s| ^ r) / 2 with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hr1 : 0 < r - 1 := by linarith
  have hK0 : 0 ≤ a ^ 2 + (r - 1) * s ^ 2 := by positivity
  rcases eq_or_lt_of_le hM0 with hM | hMpos
  · rw [← hM]
    exact Real.rpow_nonneg hK0 _
  set r' : ℝ := r / (r - 1) with hr'def
  have hrr' : (r - 1) * r' = r := by rw [hr'def]; field_simp
  have hr'1 : 1 ≤ r' := by rw [hr'def, le_div_iff₀ hr1]; linarith
  have hr'2 : r' ≤ 2 := by rw [hr'def, div_le_iff₀ hr1]; linarith
  have hr'0 : 0 < r' := by linarith
  have hr'm : r' - 1 = (r - 1)⁻¹ := by rw [hr'def]; field_simp; ring
  set w₁ := (a + s) * |a + s| ^ (r - 2) with hw₁
  set w₂ := (a - s) * |a - s| ^ (r - 2) with hw₂
  set c := (w₁ + w₂) / 2 with hc
  set d := (w₁ - w₂) / 2 with hd
  have hMc : M = a * c + s * d := by
    have e1 := mul_mul_abs_rpow_sub_two hr (a + s)
    have e2 := mul_mul_abs_rpow_sub_two hr (a - s)
    rw [hMdef, ← e1, ← e2, hc, hd, hw₁, hw₂]
    ring
  -- Cauchy–Schwarz with weights `r - 1` and `(r-1)⁻¹`
  have hCS : M ^ 2 ≤ (a ^ 2 + (r - 1) * s ^ 2) * (c ^ 2 + (r' - 1) * d ^ 2) := by
    rw [hMc, hr'm]
    have key : (a ^ 2 + (r - 1) * s ^ 2) * (c ^ 2 + (r - 1)⁻¹ * d ^ 2) - (a * c + s * d) ^ 2
        = (a * d - (r - 1) * s * c) ^ 2 * (r - 1)⁻¹ := by
      field_simp
      ring
    have : 0 ≤ (a * d - (r - 1) * s * c) ^ 2 * (r - 1)⁻¹ := by positivity
    linarith
  -- the two-point inequality at `r'`, read at `w₁ = c + d`, `w₂ = c - d`
  have hTP := rpow_le_two_point hr'1 hr'2 c d
  have hcd1 : c + d = w₁ := by rw [hc, hd]; ring
  have hcd2 : c - d = w₂ := by rw [hc, hd]; ring
  rw [hcd1, hcd2, hw₁, hw₂, abs_mul_abs_rpow_sub_two_rpow hr hr'0 hrr',
    abs_mul_abs_rpow_sub_two_rpow hr hr'0 hrr', ← hMdef] at hTP
  have hX0 : 0 ≤ c ^ 2 + (r' - 1) * d ^ 2 := by
    have : 0 ≤ r' - 1 := by linarith
    positivity
  have hX : c ^ 2 + (r' - 1) * d ^ 2 ≤ M ^ (2 / r') := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) hTP (by positivity : 0 ≤ 2 / r')
    rwa [← Real.rpow_mul hX0, show r' / 2 * (2 / r') = 1 by field_simp, Real.rpow_one] at h
  -- `M^{2/r} ≤ a² + (r-1)s²`
  have h22 : 2 / r + 2 / r' = (2 : ℝ) := by
    rw [hr'def]
    field_simp
    ring
  have hsplit : M ^ 2 = M ^ (2 / r) * M ^ (2 / r') := by
    rw [← Real.rpow_add hMpos, h22, Real.rpow_two]
  have hMr : M ^ (2 / r) ≤ a ^ 2 + (r - 1) * s ^ 2 := by
    have hpos : 0 < M ^ (2 / r') := Real.rpow_pos_of_pos hMpos _
    have h1 : M ^ (2 / r) * M ^ (2 / r') ≤ (a ^ 2 + (r - 1) * s ^ 2) * M ^ (2 / r') := by
      rw [← hsplit]
      exact le_trans hCS (mul_le_mul_of_nonneg_left hX hK0)
    exact le_of_mul_le_mul_right h1 hpos
  calc M = (M ^ (2 / r)) ^ (r / 2) := by
        rw [← Real.rpow_mul hM0, show 2 / r * (r / 2) = 1 by field_simp, Real.rpow_one]
    _ ≤ (a ^ 2 + (r - 1) * s ^ 2) ^ (r / 2) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hMr (by positivity)

/-! ### The vector two-point inequalities -/

/-- `((α ± β)²)^{p/2} = |α ± β|^p`. -/
lemma sq_rpow_half {x p : ℝ} : (x ^ 2) ^ (p / 2) = |x| ^ p := by
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  norm_num
  ring_nf

/-- **The vector two-point inequality**, `1 ≤ p ≤ 2`: for `α, β ≥ 0` and `|γ| ≤ αβ`,
`(α² + (p-1)β²)^{p/2} ≤ ½((α²+β²+2γ)^{p/2} + (α²+β²-2γ)^{p/2})`.  The right side is concave in
`γ` and even, so it is least at `γ = ±αβ`, where it is `RMF.rpow_le_two_point`. -/
theorem rpow_le_vector_two_point {p α β γ : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hγ : |γ| ≤ α * β) :
    (α ^ 2 + (p - 1) * β ^ 2) ^ (p / 2)
      ≤ ((α ^ 2 + β ^ 2 + 2 * γ) ^ (p / 2) + (α ^ 2 + β ^ 2 - 2 * γ) ^ (p / 2)) / 2 := by
  set m := α * β with hmdef
  have hm0 : 0 ≤ m := mul_nonneg hα hβ
  have hcP : α ^ 2 + β ^ 2 + 2 * m = (α + β) ^ 2 := by rw [hmdef]; ring
  have hcM : α ^ 2 + β ^ 2 - 2 * m = (α - β) ^ 2 := by rw [hmdef]; ring
  have hext : (α ^ 2 + (p - 1) * β ^ 2) ^ (p / 2)
      ≤ ((α ^ 2 + β ^ 2 + 2 * m) ^ (p / 2) + (α ^ 2 + β ^ 2 - 2 * m) ^ (p / 2)) / 2 := by
    rw [hcP, hcM, sq_rpow_half, sq_rpow_half]
    exact rpow_le_two_point hp1 hp2 α β
  rcases eq_or_lt_of_le hm0 with hm | hm
  · have hγ0 : γ = 0 := abs_nonpos_iff.1 (by rw [← hm] at hγ; exact hγ)
    rw [hγ0]
    rw [← hm] at hext
    simpa using hext
  · have hconc := Real.concaveOn_rpow (p := p / 2) (by linarith) (by linarith)
    set c := α ^ 2 + β ^ 2 with hcdef
    have hγ' := abs_le.1 hγ
    set l := (m + γ) / (2 * m) with hldef
    have hl0 : 0 ≤ l := div_nonneg (by linarith [hγ'.1]) (by linarith)
    have hl1 : l ≤ 1 := by rw [hldef, div_le_one (by linarith)]; linarith [hγ'.2]
    have hx : l * (c + 2 * m) + (1 - l) * (c - 2 * m) = c + 2 * γ := by
      rw [hldef]; field_simp; ring
    have hy : (1 - l) * (c + 2 * m) + l * (c - 2 * m) = c - 2 * γ := by
      rw [hldef]; field_simp; ring
    have hpP : (0 : ℝ) ≤ c + 2 * m := by rw [hcP]; positivity
    have hpM : (0 : ℝ) ≤ c - 2 * m := by rw [hcM]; positivity
    have h1 := hconc.2 (Set.mem_Ici.2 hpP) (Set.mem_Ici.2 hpM) hl0 (by linarith)
      (by ring : l + (1 - l) = 1)
    have h2 := hconc.2 (Set.mem_Ici.2 hpP) (Set.mem_Ici.2 hpM) (by linarith : 0 ≤ 1 - l) hl0
      (by ring : (1 - l) + l = 1)
    simp only [smul_eq_mul] at h1 h2
    rw [hx] at h1
    rw [hy] at h2
    linarith

/-- **The vector two-point inequality**, `r ≥ 2`: for `α, β ≥ 0` and `|γ| ≤ αβ`,
`½((α²+β²+2γ)^{r/2} + (α²+β²-2γ)^{r/2}) ≤ (α² + (r-1)β²)^{r/2}`.  Convexity in `γ` in place of
concavity, and `RMF.two_point_le_rpow` at `γ = ±αβ`. -/
theorem vector_two_point_le_rpow {r α β γ : ℝ} (hr : 2 ≤ r) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hγ : |γ| ≤ α * β) :
    ((α ^ 2 + β ^ 2 + 2 * γ) ^ (r / 2) + (α ^ 2 + β ^ 2 - 2 * γ) ^ (r / 2)) / 2
      ≤ (α ^ 2 + (r - 1) * β ^ 2) ^ (r / 2) := by
  set m := α * β with hmdef
  have hm0 : 0 ≤ m := mul_nonneg hα hβ
  have hcP : α ^ 2 + β ^ 2 + 2 * m = (α + β) ^ 2 := by rw [hmdef]; ring
  have hcM : α ^ 2 + β ^ 2 - 2 * m = (α - β) ^ 2 := by rw [hmdef]; ring
  have hext : ((α ^ 2 + β ^ 2 + 2 * m) ^ (r / 2) + (α ^ 2 + β ^ 2 - 2 * m) ^ (r / 2)) / 2
      ≤ (α ^ 2 + (r - 1) * β ^ 2) ^ (r / 2) := by
    rw [hcP, hcM, sq_rpow_half, sq_rpow_half]
    exact two_point_le_rpow hr α β
  rcases eq_or_lt_of_le hm0 with hm | hm
  · have hγ0 : γ = 0 := abs_nonpos_iff.1 (by rw [← hm] at hγ; exact hγ)
    rw [hγ0]
    rw [← hm] at hext
    simpa using hext
  · have hconv := convexOn_rpow (p := r / 2) (by linarith)
    set c := α ^ 2 + β ^ 2 with hcdef
    have hγ' := abs_le.1 hγ
    set l := (m + γ) / (2 * m) with hldef
    have hl0 : 0 ≤ l := div_nonneg (by linarith [hγ'.1]) (by linarith)
    have hl1 : l ≤ 1 := by rw [hldef, div_le_one (by linarith)]; linarith [hγ'.2]
    have hx : l * (c + 2 * m) + (1 - l) * (c - 2 * m) = c + 2 * γ := by
      rw [hldef]; field_simp; ring
    have hy : (1 - l) * (c + 2 * m) + l * (c - 2 * m) = c - 2 * γ := by
      rw [hldef]; field_simp; ring
    have hpP : (0 : ℝ) ≤ c + 2 * m := by rw [hcP]; positivity
    have hpM : (0 : ℝ) ≤ c - 2 * m := by rw [hcM]; positivity
    have h1 := hconv.2 (Set.mem_Ici.2 hpP) (Set.mem_Ici.2 hpM) hl0 (by linarith)
      (by ring : l + (1 - l) = 1)
    have h2 := hconv.2 (Set.mem_Ici.2 hpP) (Set.mem_Ici.2 hpM) (by linarith : 0 ≤ 1 - l) hl0
      (by ring : (1 - l) + l = 1)
    simp only [smul_eq_mul] at h1 h2
    rw [hx] at h1
    rw [hy] at h2
    linarith

/-! ### Integrating out one Rademacher variable -/

/-- **Integrating out an independent Rademacher variable**: if `Z` has the Rademacher law and is
independent of `W`, then `E F(W, Z) = ½ (E F(W, 1) + E F(W, -1))`.  Independence makes the joint
law a product, and the Rademacher factor is `½(δ₁ + δ₋₁)`; the argument is
`RMF.integral_le_of_indepFun_fibrewise`'s, with an equality on each fibre. -/
theorem integral_comp_indep_rademacher {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → γ} {Z : Ω → ℂ}
    (hW : Measurable W) (hZ : Measurable Z) (hind : IndepFun W Z μ)
    (hlaw : HasLaw Z rademacherLaw μ) {F : γ → ℂ → ℝ}
    (hFm : StronglyMeasurable fun p : γ × ℂ => F p.1 p.2)
    (hFi : Integrable (fun ω => F (W ω) (Z ω)) μ)
    (hF₁ : Integrable (fun ω => F (W ω) 1) μ) (hF₂ : Integrable (fun ω => F (W ω) (-1)) μ) :
    ∫ ω, F (W ω) (Z ω) ∂μ = (∫ ω, F (W ω) 1 ∂μ + ∫ ω, F (W ω) (-1) ∂μ) / 2 := by
  haveI : IsProbabilityMeasure (μ.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  haveI : IsProbabilityMeasure (μ.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hpair : Measurable fun ω => (W ω, Z ω) := hW.prodMk hZ
  have hmap : μ.map (fun ω => (W ω, Z ω)) = (μ.map W).prod (μ.map Z) :=
    (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hZ.aemeasurable).1 hind
  have hFprod : Integrable (fun p : γ × ℂ => F p.1 p.2) ((μ.map W).prod (μ.map Z)) := by
    rw [← hmap, integrable_map_measure hFm.aestronglyMeasurable hpair.aemeasurable]
    exact hFi
  have hF : (∫ ω, F (W ω) (Z ω) ∂μ) = ∫ y, (∫ z, F y z ∂(μ.map Z)) ∂(μ.map W) := by
    rw [← integral_prod _ hFprod, ← hmap,
      integral_map hpair.aemeasurable hFm.aestronglyMeasurable]
  have hinner : ∀ y, (∫ z, F y z ∂(μ.map Z)) = (F y 1 + F y (-1)) / 2 := by
    intro y
    rw [hlaw.map_eq, integral_rademacherLaw_eq, smul_eq_mul]
    ring
  have hm₁ : AEStronglyMeasurable (fun y => F y 1) (μ.map W) :=
    (hFm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hm₂ : AEStronglyMeasurable (fun y => F y (-1)) (μ.map W) :=
    (hFm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hI₁ : Integrable (fun y => F y 1) (μ.map W) := by
    rw [integrable_map_measure hm₁ hW.aemeasurable]
    exact hF₁
  have hI₂ : Integrable (fun y => F y (-1)) (μ.map W) := by
    rw [integrable_map_measure hm₂ hW.aemeasurable]
    exact hF₂
  rw [hF, integral_congr_ae (Filter.Eventually.of_forall hinner), integral_div,
    integral_add hI₁ hI₂, integral_map hW.aemeasurable hm₁, integral_map hW.aemeasurable hm₂]

/-! ### Rademacher chaos -/

section Chaos

variable {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The Rademacher chaos `∑_{A ⊆ S} c_A ∏_{i ∈ A} Y_i`. -/
noncomputable def chaosSum (Y : ι → Ω → ℂ) (S : Finset ι) (c : Finset ι → ℂ) (ω : Ω) : ℂ :=
  ∑ A ∈ S.powerset, c A * ∏ i ∈ A, Y i ω

/-- The weighted coefficient norm `∑_{A ⊆ S} t^{|A|} |c_A|²`. -/
noncomputable def chaosNormSq (S : Finset ι) (c : Finset ι → ℂ) (t : ℝ) : ℝ :=
  ∑ A ∈ S.powerset, t ^ A.card * ‖c A‖ ^ 2

/-- The weighted real inner product `∑_{A ⊆ S} t^{|A|} Re(c_A \bar d_A)`. -/
noncomputable def chaosInner (S : Finset ι) (c d : Finset ι → ℂ) (t : ℝ) : ℝ :=
  ∑ A ∈ S.powerset, t ^ A.card * (c A * (starRingEnd ℂ) (d A)).re

lemma disjoint_powerset_image_insert [DecidableEq ι] {S : Finset ι} {i : ι} (hi : i ∉ S) :
    Disjoint S.powerset (S.powerset.image (insert i)) := by
  rw [Finset.disjoint_left]
  intro A hA hA'
  obtain ⟨B, -, rfl⟩ := Finset.mem_image.1 hA'
  exact hi (Finset.mem_powerset.1 hA (Finset.mem_insert_self i B))

lemma injOn_insert_powerset [DecidableEq ι] {S : Finset ι} {i : ι} (hi : i ∉ S) :
    Set.InjOn (insert i) (S.powerset : Set (Finset ι)) := by
  intro A hA B hB hAB
  have hiA : i ∉ A := fun h => hi (Finset.mem_powerset.1 hA h)
  have hiB : i ∉ B := fun h => hi (Finset.mem_powerset.1 hB h)
  rw [← Finset.erase_insert hiA, ← Finset.erase_insert hiB]
  exact congrArg (fun C => Finset.erase C i) hAB

omit [MeasurableSpace Ω] in
/-- **Splitting off one variable**: `∑_{A ⊆ S ∪ {i}} c_A Y_A = g + Y_i h`. -/
lemma chaosSum_insert [DecidableEq ι] (Y : ι → Ω → ℂ) {S : Finset ι} {i : ι} (hi : i ∉ S)
    (c : Finset ι → ℂ) (ω : Ω) :
    chaosSum Y (insert i S) c ω
      = chaosSum Y S c ω + Y i ω * chaosSum Y S (fun A => c (insert i A)) ω := by
  rw [chaosSum, Finset.powerset_insert, Finset.sum_union (disjoint_powerset_image_insert hi),
    Finset.sum_image (injOn_insert_powerset hi), chaosSum, chaosSum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun A hA => ?_
  have hiA : i ∉ A := fun h => hi (Finset.mem_powerset.1 hA h)
  rw [Finset.prod_insert hiA]
  ring

lemma chaosNormSq_insert [DecidableEq ι] {S : Finset ι} {i : ι} (hi : i ∉ S)
    (c : Finset ι → ℂ) (t : ℝ) :
    chaosNormSq (insert i S) c t
      = chaosNormSq S c t + t * chaosNormSq S (fun A => c (insert i A)) t := by
  rw [chaosNormSq, Finset.powerset_insert, Finset.sum_union (disjoint_powerset_image_insert hi),
    Finset.sum_image (injOn_insert_powerset hi), chaosNormSq, chaosNormSq, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun A hA => ?_
  have hiA : i ∉ A := fun h => hi (Finset.mem_powerset.1 hA h)
  rw [Finset.card_insert_of_notMem hiA, pow_succ]
  ring

omit [MeasurableSpace Ω] in
lemma chaosSum_add (Y : ι → Ω → ℂ) (S : Finset ι) (c d : Finset ι → ℂ) (ω : Ω) :
    chaosSum Y S (fun A => c A + d A) ω = chaosSum Y S c ω + chaosSum Y S d ω := by
  simp only [chaosSum, add_mul, Finset.sum_add_distrib]

omit [MeasurableSpace Ω] in
lemma chaosSum_sub (Y : ι → Ω → ℂ) (S : Finset ι) (c d : Finset ι → ℂ) (ω : Ω) :
    chaosSum Y S (fun A => c A - d A) ω = chaosSum Y S c ω - chaosSum Y S d ω := by
  simp only [chaosSum, sub_mul, Finset.sum_sub_distrib]

lemma chaosNormSq_add (S : Finset ι) (c d : Finset ι → ℂ) (t : ℝ) :
    chaosNormSq S (fun A => c A + d A) t
      = chaosNormSq S c t + chaosNormSq S d t + 2 * chaosInner S c d t := by
  simp only [chaosNormSq, chaosInner, Complex.sq_norm, Complex.normSq_add, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  ring

lemma chaosNormSq_sub (S : Finset ι) (c d : Finset ι → ℂ) (t : ℝ) :
    chaosNormSq S (fun A => c A - d A) t
      = chaosNormSq S c t + chaosNormSq S d t - 2 * chaosInner S c d t := by
  simp only [chaosNormSq, chaosInner, Complex.sq_norm, Complex.normSq_sub, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  ring

lemma chaosNormSq_nonneg (S : Finset ι) (c : Finset ι → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ chaosNormSq S c t :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg ht _) (sq_nonneg _)

/-- **Cauchy–Schwarz for the weighted inner product.** -/
lemma abs_chaosInner_le (S : Finset ι) (c d : Finset ι → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    |chaosInner S c d t|
      ≤ Real.sqrt (chaosNormSq S c t) * Real.sqrt (chaosNormSq S d t) := by
  set f : Finset ι → ℝ := fun A => Real.sqrt (t ^ A.card) * ‖c A‖ with hf
  set g : Finset ι → ℝ := fun A => Real.sqrt (t ^ A.card) * ‖d A‖ with hg
  have h1 : |chaosInner S c d t| ≤ ∑ A ∈ S.powerset, f A * g A := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun A _ => ?_)
    have htk : 0 ≤ t ^ A.card := pow_nonneg ht _
    have hre : |(c A * (starRingEnd ℂ) (d A)).re| ≤ ‖c A‖ * ‖d A‖ := by
      calc |(c A * (starRingEnd ℂ) (d A)).re| ≤ ‖c A * (starRingEnd ℂ) (d A)‖ :=
            Complex.abs_re_le_norm _
        _ = ‖c A‖ * ‖d A‖ := by rw [norm_mul, Complex.norm_conj]
    rw [abs_mul, abs_of_nonneg htk]
    calc t ^ A.card * |(c A * (starRingEnd ℂ) (d A)).re| ≤ t ^ A.card * (‖c A‖ * ‖d A‖) :=
          mul_le_mul_of_nonneg_left hre htk
      _ = f A * g A := by
          rw [hf, hg]
          have hs := Real.mul_self_sqrt htk
          calc t ^ A.card * (‖c A‖ * ‖d A‖)
              = (Real.sqrt (t ^ A.card) * Real.sqrt (t ^ A.card)) * (‖c A‖ * ‖d A‖) := by
                rw [hs]
            _ = Real.sqrt (t ^ A.card) * ‖c A‖ * (Real.sqrt (t ^ A.card) * ‖d A‖) := by ring
  have hsq : ∀ A, f A ^ 2 = t ^ A.card * ‖c A‖ ^ 2 := fun A => by
    rw [hf, mul_pow, Real.sq_sqrt (pow_nonneg ht _)]
  have hsq' : ∀ A, g A ^ 2 = t ^ A.card * ‖d A‖ ^ 2 := fun A => by
    rw [hg, mul_pow, Real.sq_sqrt (pow_nonneg ht _)]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq S.powerset f g
  simp only [hsq, hsq'] at h2
  have h0 : 0 ≤ ∑ A ∈ S.powerset, f A * g A :=
    Finset.sum_nonneg fun A _ => mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have h3 : ∑ A ∈ S.powerset, f A * g A
      ≤ Real.sqrt (chaosNormSq S c t) * Real.sqrt (chaosNormSq S d t) := by
    rw [← Real.sqrt_mul (chaosNormSq_nonneg S c ht)]
    exact Real.le_sqrt_of_sq_le h2
  linarith

lemma measurable_chaosSum {Y : ι → Ω → ℂ} (hm : ∀ i, Measurable (Y i)) (S : Finset ι)
    (c : Finset ι → ℂ) : Measurable (chaosSum Y S c) :=
  Finset.measurable_sum _ fun _ _ =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => hm i)

omit [MeasurableSpace Ω] in
/-- On the event that every `|Y_i| ≤ 1`, the chaos is at most `∑_A |c_A|`. -/
lemma norm_chaosSum_le {Y : ι → Ω → ℂ} {S : Finset ι} (c : Finset ι → ℂ) {ω : Ω}
    (hω : ∀ i ∈ S, ‖Y i ω‖ ≤ 1) :
    ‖chaosSum Y S c ω‖ ≤ ∑ A ∈ S.powerset, ‖c A‖ := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun A hA => ?_)
  rw [norm_mul, norm_prod]
  have hp : ∏ i ∈ A, ‖Y i ω‖ ≤ 1 :=
    Finset.prod_le_one (fun i _ => norm_nonneg _)
      fun i hi => hω i (Finset.mem_powerset.1 hA hi)
  calc ‖c A‖ * ∏ i ∈ A, ‖Y i ω‖ ≤ ‖c A‖ * 1 := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = ‖c A‖ := mul_one _

/-- Rademacher values are bounded by one, almost surely, on any finite set of indices. -/
lemma ae_forall_norm_le_one_of_hasLaw {Y : ι → Ω → ℂ}
    (hlaw : ∀ i, HasLaw (Y i) rademacherLaw μ) (S : Finset ι) :
    ∀ᵐ ω ∂μ, ∀ i ∈ S, ‖Y i ω‖ ≤ 1 := by
  refine (Filter.eventually_all_finset S).2 fun i _ => ?_
  have hmeasP : Measurable fun z : ℂ => ‖z‖ ≤ 1 :=
    measurableSet_setOf.1 (measurableSet_le measurable_norm measurable_const)
  exact ((hlaw i).ae_iff hmeasP).2 (norm_eq_one_rademacherLaw.mono fun z hz => hz.le)

/-- Every real power of the chaos is integrable: it is bounded almost surely. -/
lemma integrable_norm_chaosSum_rpow [IsProbabilityMeasure μ] {Y : ι → Ω → ℂ}
    (hm : ∀ i, Measurable (Y i)) (hlaw : ∀ i, HasLaw (Y i) rademacherLaw μ) (S : Finset ι)
    (c : Finset ι → ℂ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω => ‖chaosSum Y S c ω‖ ^ p) μ := by
  refine (memLp_top_of_bound
    ((Real.continuous_rpow_const hp).measurable.comp
      (measurable_chaosSum hm S c).norm).aestronglyMeasurable
    ((∑ A ∈ S.powerset, ‖c A‖) ^ p) ?_).integrable le_top
  filter_upwards [ae_forall_norm_le_one_of_hasLaw hlaw S] with ω hω
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_chaosSum_le c hω) hp

/-- **The chaos over `S` is independent of a variable outside `S`.** -/
lemma indepFun_chaosSum_pair {Y : ι → Ω → ℂ} (hm : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) {S : Finset ι} {i : ι} (hi : i ∉ S) (c d : Finset ι → ℂ) :
    IndepFun (fun ω => (chaosSum Y S c ω, chaosSum Y S d ω)) (Y i) μ := by
  classical
  have key := hind.indepFun_finset S {i} (Finset.disjoint_singleton_right.2 hi) hm
  let ext : (S → ℂ) → ι → ℂ := fun v j => if h : j ∈ S then v ⟨j, h⟩ else 0
  have hext : ∀ j, Measurable fun v : S → ℂ => ext v j := by
    intro j
    by_cases h : j ∈ S
    · simp only [ext, h, dif_pos]
      exact measurable_pi_apply _
    · simp only [ext, h, dif_neg, not_false_eq_true]
      exact measurable_const
  let φ : (S → ℂ) → ℂ × ℂ := fun v =>
    (∑ A ∈ S.powerset, c A * ∏ j ∈ A, ext v j, ∑ A ∈ S.powerset, d A * ∏ j ∈ A, ext v j)
  have hφ : Measurable φ :=
    (Finset.measurable_sum _ fun A _ =>
        measurable_const.mul (Finset.measurable_prod _ fun j _ => hext j)).prodMk
      (Finset.measurable_sum _ fun A _ =>
        measurable_const.mul (Finset.measurable_prod _ fun j _ => hext j))
  have hψ : Measurable fun v : ({i} : Finset ι) → ℂ => v ⟨i, Finset.mem_singleton_self i⟩ :=
    measurable_pi_apply _
  refine (key.comp hφ hψ).congr (Filter.Eventually.of_forall fun ω => ?_)
    (Filter.Eventually.of_forall fun ω => rfl)
  have hprod : ∀ A ∈ S.powerset, ∏ j ∈ A, ext (fun j : S => Y j ω) j = ∏ j ∈ A, Y j ω :=
    fun A hA => Finset.prod_congr rfl fun j hj => by
      simp only [ext, Finset.mem_powerset.1 hA hj, dif_pos]
  simp only [Function.comp_apply, φ, chaosSum]
  rw [Prod.mk.injEq]
  exact ⟨Finset.sum_congr rfl fun A hA => by rw [hprod A hA],
    Finset.sum_congr rfl fun A hA => by rw [hprod A hA]⟩

/-- **The averaging identity**: for `i ∉ S`,
`E|g + Y_i h|^p = ½(E|g + h|^p + E|g - h|^p)`, `g, h` chaos sums over `S`. -/
lemma integral_norm_chaosSum_insert_rpow [DecidableEq ι] [IsProbabilityMeasure μ] {Y : ι → Ω → ℂ}
    (hm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hlaw : ∀ i, HasLaw (Y i) rademacherLaw μ) {S : Finset ι} {i : ι} (hi : i ∉ S)
    (c : Finset ι → ℂ) {p : ℝ} (hp : 0 ≤ p) :
    ∫ ω, ‖chaosSum Y (insert i S) c ω‖ ^ p ∂μ
      = (∫ ω, ‖chaosSum Y S (fun A => c A + c (insert i A)) ω‖ ^ p ∂μ
          + ∫ ω, ‖chaosSum Y S (fun A => c A - c (insert i A)) ω‖ ^ p ∂μ) / 2 := by
  set c' : Finset ι → ℂ := fun A => c (insert i A) with hc'
  have hF : StronglyMeasurable fun q : (ℂ × ℂ) × ℂ => ‖q.1.1 + q.2 * q.1.2‖ ^ p :=
    ((Real.continuous_rpow_const hp).comp
      (continuous_norm.comp ((continuous_fst.comp continuous_fst).add
        (continuous_snd.mul (continuous_snd.comp continuous_fst))))).stronglyMeasurable
  have hW : Measurable fun ω => (chaosSum Y S c ω, chaosSum Y S c' ω) :=
    (measurable_chaosSum hm S c).prodMk (measurable_chaosSum hm S c')
  have hsplit : ∀ ω, chaosSum Y (insert i S) c ω
      = chaosSum Y S c ω + Y i ω * chaosSum Y S c' ω := chaosSum_insert Y hi c
  have hplus : ∀ ω, chaosSum Y S (fun A => c A + c (insert i A)) ω
      = chaosSum Y S c ω + 1 * chaosSum Y S c' ω := fun ω => by
    rw [chaosSum_add, one_mul]
  have hminus : ∀ ω, chaosSum Y S (fun A => c A - c (insert i A)) ω
      = chaosSum Y S c ω + (-1) * chaosSum Y S c' ω := fun ω => by
    rw [chaosSum_sub, neg_one_mul, sub_eq_add_neg]
  simp_rw [hsplit, hplus, hminus]
  refine integral_comp_indep_rademacher (W := fun ω => (chaosSum Y S c ω, chaosSum Y S c' ω))
    (F := fun w z => ‖w.1 + z * w.2‖ ^ p) hW (hm i) (indepFun_chaosSum_pair hm hind hi c c')
    (hlaw i) hF ?_ ?_ ?_
  · simpa only [← hsplit] using integrable_norm_chaosSum_rpow hm hlaw (insert i S) c hp
  · simpa only [← hplus] using
      integrable_norm_chaosSum_rpow hm hlaw S (fun A => c A + c (insert i A)) hp
  · simpa only [← hminus] using
      integrable_norm_chaosSum_rpow hm hlaw S (fun A => c A - c (insert i A)) hp

omit [MeasurableSpace Ω] in
lemma chaosSum_empty (Y : ι → Ω → ℂ) (c : Finset ι → ℂ) (ω : Ω) :
    chaosSum Y ∅ c ω = c ∅ := by
  simp [chaosSum]

lemma chaosNormSq_empty (c : Finset ι → ℂ) (t : ℝ) : chaosNormSq ∅ c t = ‖c ∅‖ ^ 2 := by
  simp [chaosNormSq]

/-! ### Hypercontractivity -/

/-- **Bonami–Beckner, `(p → 2)`**: for `1 ≤ p ≤ 2`,
`(∑_{A⊆S} (p-1)^{|A|} |c_A|²)^{p/2} ≤ E|∑_{A⊆S} c_A Y_A|^p`. -/
theorem chaosNormSq_rpow_le_integral [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℂ} (hm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hlaw : ∀ i, HasLaw (Y i) rademacherLaw μ) {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (S : Finset ι) (c : Finset ι → ℂ) :
    chaosNormSq S c (p - 1) ^ (p / 2) ≤ ∫ ω, ‖chaosSum Y S c ω‖ ^ p ∂μ := by
  classical
  induction S using Finset.induction_on generalizing c with
  | empty =>
    simp only [chaosSum_empty, chaosNormSq_empty, integral_const, probReal_univ, one_smul]
    rw [sq_rpow_half, abs_norm]
  | insert i S hi ih =>
    have hp0 : 0 ≤ p - 1 := by linarith
    rw [integral_norm_chaosSum_insert_rpow hm hind hlaw hi c (by linarith), chaosNormSq_insert hi]
    have hP := ih (fun A => c A + c (insert i A))
    have hM := ih (fun A => c A - c (insert i A))
    rw [chaosNormSq_add] at hP
    rw [chaosNormSq_sub] at hM
    have hα2 := Real.sq_sqrt (chaosNormSq_nonneg S c hp0)
    have hβ2 := Real.sq_sqrt (chaosNormSq_nonneg S (fun A => c (insert i A)) hp0)
    have hv := rpow_le_vector_two_point hp1 hp2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (abs_chaosInner_le S c (fun A => c (insert i A)) hp0)
    rw [hα2, hβ2] at hv
    linarith

/-- **Bonami–Beckner, `(2 → r)`**: for `r ≥ 2`,
`E|∑_{A⊆S} c_A Y_A|^r ≤ (∑_{A⊆S} (r-1)^{|A|} |c_A|²)^{r/2}`. -/
theorem integral_rpow_le_chaosNormSq [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℂ} (hm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hlaw : ∀ i, HasLaw (Y i) rademacherLaw μ) {r : ℝ} (hr : 2 ≤ r)
    (S : Finset ι) (c : Finset ι → ℂ) :
    ∫ ω, ‖chaosSum Y S c ω‖ ^ r ∂μ ≤ chaosNormSq S c (r - 1) ^ (r / 2) := by
  classical
  induction S using Finset.induction_on generalizing c with
  | empty =>
    simp only [chaosSum_empty, chaosNormSq_empty, integral_const, probReal_univ, one_smul]
    rw [sq_rpow_half, abs_norm]
  | insert i S hi ih =>
    have hr0 : 0 ≤ r - 1 := by linarith
    rw [integral_norm_chaosSum_insert_rpow hm hind hlaw hi c (by linarith), chaosNormSq_insert hi]
    have hP := ih (fun A => c A + c (insert i A))
    have hM := ih (fun A => c A - c (insert i A))
    rw [chaosNormSq_add] at hP
    rw [chaosNormSq_sub] at hM
    have hα2 := Real.sq_sqrt (chaosNormSq_nonneg S c hr0)
    have hβ2 := Real.sq_sqrt (chaosNormSq_nonneg S (fun A => c (insert i A)) hr0)
    have hv := vector_two_point_le_rpow hr (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (abs_chaosInner_le S c (fun A => c (insert i A)) hr0)
    rw [hα2, hβ2] at hv
    linarith

/-- **Dropping one variable lowers every moment of order `r ≥ 1`**: pointwise
`|g|^r ≤ ½(|g+h|^r + |g-h|^r)`, by the triangle inequality and convexity. -/
lemma integral_rpow_chaosSum_le_insert [DecidableEq ι] [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℂ} (hm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hlaw : ∀ i, HasLaw (Y i) rademacherLaw μ) {r : ℝ} (hr : 1 ≤ r) {S : Finset ι} {i : ι}
    (hi : i ∉ S) (c : Finset ι → ℂ) :
    ∫ ω, ‖chaosSum Y S c ω‖ ^ r ∂μ ≤ ∫ ω, ‖chaosSum Y (insert i S) c ω‖ ^ r ∂μ := by
  have hr0 : 0 ≤ r := by linarith
  rw [integral_norm_chaosSum_insert_rpow hm hind hlaw hi c hr0, ← integral_add
    (integrable_norm_chaosSum_rpow hm hlaw S _ hr0) (integrable_norm_chaosSum_rpow hm hlaw S _ hr0),
    ← integral_div]
  refine integral_mono (integrable_norm_chaosSum_rpow hm hlaw S c hr0)
    (((integrable_norm_chaosSum_rpow hm hlaw S _ hr0).add
      (integrable_norm_chaosSum_rpow hm hlaw S _ hr0)).div_const 2) fun ω => ?_
  simp only [chaosSum_add, chaosSum_sub]
  set g := chaosSum Y S c ω
  set h := chaosSum Y S (fun A => c (insert i A)) ω
  have htri : ‖g‖ ≤ (‖g + h‖ + ‖g - h‖) / 2 := by
    have : (2 : ℝ) * ‖g‖ = ‖(g + h) + (g - h)‖ := by
      rw [show (g + h) + (g - h) = 2 * g by ring, norm_mul, Complex.norm_two]
    have h2 := norm_add_le (g + h) (g - h)
    linarith
  have hconv := (convexOn_rpow hr).2 (Set.mem_Ici.2 (norm_nonneg (g + h)))
    (Set.mem_Ici.2 (norm_nonneg (g - h))) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hconv
  calc ‖g‖ ^ r ≤ ((‖g + h‖ + ‖g - h‖) / 2) ^ r :=
        Real.rpow_le_rpow (norm_nonneg _) htri hr0
    _ = (1 / 2 * ‖g + h‖ + 1 / 2 * ‖g - h‖) ^ r := by ring_nf
    _ ≤ 1 / 2 * ‖g + h‖ ^ r + 1 / 2 * ‖g - h‖ ^ r := hconv
    _ = (‖g + h‖ ^ r + ‖g - h‖ ^ r) / 2 := by ring

/-- **Projection onto fewer variables lowers every moment of order `r ≥ 1`**: for `S ⊆ T`,
`E|∑_{A⊆S} c_A Y_A|^r ≤ E|∑_{A⊆T} c_A Y_A|^r`. -/
theorem integral_rpow_chaosSum_le_of_subset [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℂ} (hm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hlaw : ∀ i, HasLaw (Y i) rademacherLaw μ) {r : ℝ} (hr : 1 ≤ r) {S T : Finset ι}
    (hST : S ⊆ T) (c : Finset ι → ℂ) :
    ∫ ω, ‖chaosSum Y S c ω‖ ^ r ∂μ ≤ ∫ ω, ‖chaosSum Y T c ω‖ ^ r ∂μ := by
  classical
  have key : ∀ D : Finset ι, Disjoint S D →
      ∫ ω, ‖chaosSum Y S c ω‖ ^ r ∂μ ≤ ∫ ω, ‖chaosSum Y (S ∪ D) c ω‖ ^ r ∂μ := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro _; rw [Finset.union_empty]
    | insert i D hi ih =>
      intro hSD
      have hiS : i ∉ S := Finset.disjoint_right.1 hSD (Finset.mem_insert_self i D)
      have hSD' : Disjoint S D := Finset.disjoint_of_subset_right (Finset.subset_insert i D) hSD
      have hiSD : i ∉ S ∪ D := by
        rw [Finset.mem_union]
        rintro (h | h)
        · exact hiS h
        · exact hi h
      rw [Finset.union_insert]
      exact le_trans (ih hSD') (integral_rpow_chaosSum_le_insert hm hind hlaw hr hiSD c)
  have h := key (T \ S) Finset.disjoint_sdiff
  rwa [Finset.union_sdiff_of_subset hST] at h

end Chaos

end RMF
