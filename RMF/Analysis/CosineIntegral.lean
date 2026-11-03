/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The exponential integral `∫ cos (τ u) / u`

The kernel of a joint moment of random Euler products is

`K_y(τ) = ∑_{p < y} cos (τ log p) / p`,

and the estimate that turns it into the covariance of a log-correlated field is

`K_y(τ) = log min (log y) (1/|τ|) + O(1)`  for `|τ| ≤ 1`.

The route to it is partial summation against the prime number theorem, whose main term is the
exponential integral `∫_{log 2}^{log y} cos (τ u) / u du`.  This file proves the estimate for
that integral and nothing else: it is elementary real analysis, depends only on Mathlib, and
no prime numbers appear.  `NumberTheory/CosinePrimeSum.lean` does the summation.

Two regimes, separated by `u = 1/τ`:

* below `1/τ` the cosine is close to `1`, and the integral is `∫ du / u` up to
  `τ ^ 2 b ^ 2 / 4` (`RMF.abs_integral_cos_div_sub_log_le`);
* above `1/τ` the cosine oscillates, and one integration by parts shows the whole tail is at
  most `3` in absolute value, however long it is (`RMF.abs_integral_cos_div_tail_le`).

Splitting at `min b (1/τ)` gives `log (min b (1/τ) / a) + O(1)`
(`RMF.abs_integral_cos_div_sub_log_min_le`).  The point is that the bound does not degrade as
`b → ∞`: the integral saturates at `log (1/τ)`.
-/

open Real intervalIntegral MeasureTheory

namespace RMF

section Integrability

variable {τ a b : ℝ}

/-- Away from the origin the integrand is continuous. -/
lemma continuousOn_cos_div (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun u : ℝ => Real.cos (τ * u) / u) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun u hu => (ha.trans_le hu.1).ne'

lemma intervalIntegrable_cos_div (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => Real.cos (τ * u) / u) volume a b :=
  (continuousOn_cos_div ha hab).intervalIntegrable

lemma intervalIntegrable_one_div (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => 1 / u) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  exact ContinuousOn.div continuousOn_const continuousOn_id fun u hu => (ha.trans_le hu.1).ne'

/-- `x ↦ 1 / x ^ 2` is continuous away from the origin.  It appears four times in the
integration by parts below, once for each integrand built from it. -/
lemma continuousOn_one_div_sq (ha : 0 < a) (b : ℝ) :
    ContinuousOn (fun x : ℝ => 1 / x ^ 2) (Set.Icc a b) :=
  ContinuousOn.div continuousOn_const (by fun_prop)
    fun x hx => pow_ne_zero 2 (ha.trans_le hx.1).ne'

lemma zero_notMem_uIcc (ha : 0 < a) (hab : a ≤ b) : (0 : ℝ) ∉ Set.uIcc a b := by
  rw [Set.uIcc_of_le hab]
  exact fun h => absurd h.1 (not_le.mpr ha)

end Integrability

/-- **Below `1/τ`**: the cosine is close to `1`, so the integral is `log (b/a)` up to
`τ ^ 2 b ^ 2 / 4`.  Applied with `τ b ≤ 1` the error is at most `1/4`. -/
lemma abs_integral_cos_div_sub_log_le {a b τ : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |(∫ u in a..b, Real.cos (τ * u) / u) - Real.log (b / a)| ≤ τ ^ 2 * b ^ 2 / 4 := by
  have hcos := intervalIntegrable_cos_div (τ := τ) ha hab
  have hone := intervalIntegrable_one_div ha hab
  have hquad : IntervalIntegrable (fun u : ℝ => τ ^ 2 * u / 2) volume a b :=
    (by fun_prop : Continuous fun u : ℝ => τ ^ 2 * u / 2).intervalIntegrable _ _
  rw [← integral_one_div (zero_notMem_uIcc ha hab), ← intervalIntegral.integral_sub hcos hone]
  have hpt : ∀ u ∈ Set.Icc a b, |Real.cos (τ * u) / u - 1 / u| ≤ τ ^ 2 * u / 2 := by
    intro u hu
    have hu0 : 0 < u := ha.trans_le hu.1
    rw [div_sub_div_same, abs_div, abs_of_pos hu0,
      abs_of_nonpos (by linarith [Real.cos_le_one (τ * u)])]
    rw [div_le_iff₀ hu0]
    have := Real.one_sub_sq_div_two_le_cos (x := τ * u)
    nlinarith
  calc |∫ u in a..b, (Real.cos (τ * u) / u - 1 / u)|
      ≤ ∫ u in a..b, |Real.cos (τ * u) / u - 1 / u| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ u in a..b, τ ^ 2 * u / 2 :=
        intervalIntegral.integral_mono_on hab (hcos.sub hone).abs hquad hpt
    _ = τ ^ 2 * (b ^ 2 - a ^ 2) / 4 := by
        rw [show (fun u : ℝ => τ ^ 2 * u / 2) = fun u : ℝ => τ ^ 2 / 2 * u by funext; ring,
          intervalIntegral.integral_const_mul, integral_id]
        ring
    _ ≤ τ ^ 2 * b ^ 2 / 4 := by nlinarith [sq_nonneg a, sq_nonneg τ]

/-- **Above `1/τ`**: one integration by parts bounds the tail by `3/(τc)`, however long it is.

The three pieces — the two boundary terms and the remaining integral — are each at most `1/(τc)`,
with no lower bound on `τc`; the `1 ≤ τc` of `RMF.abs_integral_cos_div_tail_le` only weakens
`3/(τc)` to `3`. -/
lemma abs_integral_cos_div_tail_le' {τ c b : ℝ} (hτ : 0 < τ) (hc : 0 < c) (hcb : c ≤ b) :
    |∫ u in c..b, Real.cos (τ * u) / u| ≤ 3 / (τ * c) := by
  have hb : 0 < b := hc.trans_le hcb
  -- integration by parts against an antiderivative of the cosine
  have hderiv1 : ∀ x ∈ Set.uIcc c b, HasDerivAt (fun u : ℝ => 1 / u) (-(1 / x ^ 2)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rw [Set.uIcc_of_le hcb] at hx
      exact (hc.trans_le hx.1).ne'
    simpa [one_div] using (hasDerivAt_inv hx0)
  have hderiv2 : ∀ x ∈ Set.uIcc c b,
      HasDerivAt (fun u : ℝ => Real.sin (τ * u) / τ) (Real.cos (τ * x)) x := by
    intro x _
    have h := ((Real.hasDerivAt_sin (τ * x)).comp x ((hasDerivAt_id x).const_mul τ)).div_const τ
    simpa [mul_comm, hτ.ne'] using h
  have hint1 : IntervalIntegrable (fun x : ℝ => -(1 / x ^ 2)) volume c b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hcb]
    exact (continuousOn_one_div_sq hc b).neg
  have hint2 : IntervalIntegrable (fun x : ℝ => Real.cos (τ * x)) volume c b :=
    (by fun_prop : Continuous fun x : ℝ => Real.cos (τ * x)).intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hderiv1 hderiv2 hint1 hint2
  have hgoal : (∫ u in c..b, Real.cos (τ * u) / u)
      = ∫ x in c..b, (1 / x) * Real.cos (τ * x) :=
    intervalIntegral.integral_congr fun x _ => by rw [one_div, div_eq_inv_mul]
  rw [hgoal, hparts]
  -- the boundary terms, each `≤ 1/(τc)` because `|sin| ≤ 1` and `x ≥ c`
  have hbd : ∀ {x : ℝ}, c ≤ x → |1 / x * (Real.sin (τ * x) / τ)| ≤ 1 / (τ * c) := by
    intro x hx
    have hx0 : 0 < x := hc.trans_le hx
    have hsin : |Real.sin (τ * x)| ≤ 1 := Real.abs_sin_le_one _
    have key : |1 / x * (Real.sin (τ * x) / τ)| = |Real.sin (τ * x)| / (x * τ) := by
      rw [abs_mul, abs_div, abs_div, abs_one, abs_of_pos hx0, abs_of_pos hτ]
      field_simp
    rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hsin (by positivity : (0 : ℝ) ≤ τ * c),
      mul_le_mul_of_nonneg_left hx hτ.le]
  -- the remaining integral, which converges because `1/x ^ 2` does
  have hinvsq : (∫ x in c..b, 1 / x ^ 2) = 1 / c - 1 / b := by
    have hderiv : ∀ x ∈ Set.uIcc c b, HasDerivAt (fun u : ℝ => -(1 / u)) (1 / x ^ 2) x := by
      intro x hx
      have hx0 : x ≠ 0 := by
        rw [Set.uIcc_of_le hcb] at hx
        exact (hc.trans_le hx.1).ne'
      simpa [one_div] using (hasDerivAt_inv hx0).const_mul (-1 : ℝ)
    have hint : IntervalIntegrable (fun x : ℝ => 1 / x ^ 2) volume c b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hcb]
      exact continuousOn_one_div_sq hc b
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    ring
  have hrem : |∫ x in c..b, -(1 / x ^ 2) * (Real.sin (τ * x) / τ)| ≤ 1 / (τ * c) := by
    have habs : IntervalIntegrable
        (fun x : ℝ => |-(1 / x ^ 2) * (Real.sin (τ * x) / τ)|) volume c b := by
      refine ContinuousOn.intervalIntegrable (ContinuousOn.abs ?_)
      rw [Set.uIcc_of_le hcb]
      exact ((continuousOn_one_div_sq hc b).neg).mul (by fun_prop)
    have hmaj : IntervalIntegrable (fun x : ℝ => 1 / τ * (1 / x ^ 2)) volume c b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hcb]
      exact continuousOn_const.mul (continuousOn_one_div_sq hc b)
    have hpt : ∀ x ∈ Set.Icc c b,
        |-(1 / x ^ 2) * (Real.sin (τ * x) / τ)| ≤ 1 / τ * (1 / x ^ 2) := by
      intro x hx
      have hx0 : 0 < x := hc.trans_le hx.1
      have hsin : |Real.sin (τ * x)| ≤ 1 := Real.abs_sin_le_one _
      have key : |-(1 / x ^ 2) * (Real.sin (τ * x) / τ)| = |Real.sin (τ * x)| / (x ^ 2 * τ) := by
        rw [abs_mul, abs_neg, abs_div, abs_div, abs_one,
          abs_of_pos (by positivity : (0:ℝ) < x ^ 2), abs_of_pos hτ]
        field_simp
      rw [key, div_le_iff₀ (by positivity)]
      calc |Real.sin (τ * x)| ≤ 1 := hsin
        _ = 1 / τ * (1 / x ^ 2) * (x ^ 2 * τ) := by field_simp
    calc |∫ x in c..b, -(1 / x ^ 2) * (Real.sin (τ * x) / τ)|
        ≤ ∫ x in c..b, |-(1 / x ^ 2) * (Real.sin (τ * x) / τ)| :=
          intervalIntegral.abs_integral_le_integral_abs hcb
      _ ≤ ∫ x in c..b, 1 / τ * (1 / x ^ 2) :=
          intervalIntegral.integral_mono_on hcb habs hmaj hpt
      _ = 1 / τ * (1 / c - 1 / b) := by rw [intervalIntegral.integral_const_mul, hinvsq]
      _ ≤ 1 / (τ * c) := by
          have h2 : (0:ℝ) ≤ 1 / τ * (1 / b) := by positivity
          have h3 : 1 / τ * (1 / c) = 1 / (τ * c) := by field_simp
          nlinarith
  calc |1 / b * (Real.sin (τ * b) / τ) - 1 / c * (Real.sin (τ * c) / τ)
        - ∫ x in c..b, -(1 / x ^ 2) * (Real.sin (τ * x) / τ)|
      ≤ |1 / b * (Real.sin (τ * b) / τ) - 1 / c * (Real.sin (τ * c) / τ)|
        + |∫ x in c..b, -(1 / x ^ 2) * (Real.sin (τ * x) / τ)| :=
        abs_sub (1 / b * (Real.sin (τ * b) / τ) - 1 / c * (Real.sin (τ * c) / τ))
          (∫ x in c..b, -(1 / x ^ 2) * (Real.sin (τ * x) / τ))
    _ ≤ (|1 / b * (Real.sin (τ * b) / τ)| + |1 / c * (Real.sin (τ * c) / τ)|)
        + |∫ x in c..b, -(1 / x ^ 2) * (Real.sin (τ * x) / τ)| := by
        gcongr
        exact abs_sub (1 / b * (Real.sin (τ * b) / τ)) (1 / c * (Real.sin (τ * c) / τ))
    _ ≤ (1 / (τ * c) + 1 / (τ * c)) + 1 / (τ * c) := by
        linarith [hbd hcb, hbd (le_refl c), hrem]
    _ = 3 / (τ * c) := by ring

/-- **Above `1/τ`**: the tail is at most `3`, however long it is.  This oscillation is what stops
the integral from growing past `log (1/τ)`.  The sharp form is
`RMF.abs_integral_cos_div_tail_le'`. -/
lemma abs_integral_cos_div_tail_le {τ c b : ℝ} (hτ : 0 < τ) (hc : 0 < c) (hcb : c ≤ b)
    (hτc : 1 ≤ τ * c) :
    |∫ u in c..b, Real.cos (τ * u) / u| ≤ 3 := by
  refine le_trans (abs_integral_cos_div_tail_le' hτ hc hcb) ?_
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **The main-term integral.**  For `0 < τ` and `τ a ≤ 1`,

`∫_a^b cos (τ u) / u du = log (min b (1/τ) / a) + O(1)`,

with an absolute constant.  The integral grows like `log b` until `b` reaches `1/τ` and is
flat afterwards. -/
theorem abs_integral_cos_div_sub_log_min_le {a b τ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hτ : 0 < τ) (hτa : τ * a ≤ 1) :
    |(∫ u in a..b, Real.cos (τ * u) / u) - Real.log (min b (1 / τ) / a)| ≤ 4 := by
  by_cases h : τ * b ≤ 1
  · -- the whole range lies below `1/τ`
    have hbτ : b ≤ 1 / τ := by rw [le_div_iff₀ hτ]; linarith [mul_comm τ b]
    rw [min_eq_left hbτ]
    refine (abs_integral_cos_div_sub_log_le ha hab).trans ?_
    have h0 : 0 ≤ τ * b := mul_nonneg hτ.le (ha.trans_le hab).le
    nlinarith
  · -- split at `1/τ`
    rw [not_le] at h
    have hcpos : (0 : ℝ) < 1 / τ := by positivity
    have hac : a ≤ 1 / τ := by rw [le_div_iff₀ hτ]; linarith [mul_comm τ a]
    have hcb : 1 / τ ≤ b := by rw [div_le_iff₀ hτ]; linarith [mul_comm τ b]
    have hτc : 1 ≤ τ * (1 / τ) := by rw [mul_one_div, div_self hτ.ne']
    rw [min_eq_right hcb, ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_cos_div (τ := τ) ha hac)
      (intervalIntegrable_cos_div (τ := τ) hcpos hcb)]
    have h1 : |(∫ u in a..(1 / τ), Real.cos (τ * u) / u) - Real.log (1 / τ / a)| ≤ 1 / 4 := by
      refine (abs_integral_cos_div_sub_log_le ha hac).trans ?_
      rw [show τ ^ 2 * (1 / τ) ^ 2 / 4 = 1 / 4 from by field_simp]
    have h2 : |∫ u in (1 / τ)..b, Real.cos (τ * u) / u| ≤ 3 :=
      abs_integral_cos_div_tail_le hτ hcpos hcb hτc
    calc |(∫ u in a..(1 / τ), Real.cos (τ * u) / u) + (∫ u in (1 / τ)..b, Real.cos (τ * u) / u)
          - Real.log (1 / τ / a)|
        ≤ |(∫ u in a..(1 / τ), Real.cos (τ * u) / u) - Real.log (1 / τ / a)|
          + |∫ u in (1 / τ)..b, Real.cos (τ * u) / u| := by
          calc |(∫ u in a..(1 / τ), Real.cos (τ * u) / u)
                + (∫ u in (1 / τ)..b, Real.cos (τ * u) / u) - Real.log (1 / τ / a)|
              = |((∫ u in a..(1 / τ), Real.cos (τ * u) / u) - Real.log (1 / τ / a))
                + (∫ u in (1 / τ)..b, Real.cos (τ * u) / u)| := by congr 1; ring
            _ ≤ _ := abs_add_le _ _
      _ ≤ 1 / 4 + 3 := by gcongr
      _ ≤ 4 := by norm_num

/-! ### The substitution `u = log t`

Partial summation against the prime counting function produces the main term
`∫_x^y cos (τ log t) / (t log t) dt`, which the substitution `u = log t` turns into the
exponential integral estimated above.
-/

/-- `∫_x^y cos (τ log t) / (t log t) dt = ∫_{log x}^{log y} cos (τ u) / u du`. -/
lemma integral_cos_log_div_eq {τ x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    (∫ t in x..y, Real.cos (τ * Real.log t) / (t * Real.log t))
      = ∫ u in (Real.log x)..(Real.log y), Real.cos (τ * u) / u := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hpos : ∀ t ∈ Set.uIcc x y, 1 < t := by
    rw [Set.uIcc_of_le hxy]
    exact fun t ht => hx.trans_le ht.1
  have hne : ∀ t ∈ Set.uIcc x y, t ≠ 0 := fun t ht => (zero_lt_one.trans (hpos t ht)).ne'
  have hsub : (∫ t in x..y, (1 / t) • ((fun u => Real.cos (τ * u) / u) ∘ Real.log) t)
      = ∫ u in (Real.log x)..(Real.log y), Real.cos (τ * u) / u := by
    refine intervalIntegral.integral_deriv_smul_comp'' ?_ ?_ ?_ ?_
    · exact ContinuousOn.log continuousOn_id hne
    · intro t ht
      rw [Set.uIcc_of_le hxy] at hpos
      have ht0 : t ≠ 0 := by
        rcases Set.mem_Ioo.mp ht with ⟨h1, _⟩
        rw [min_eq_left hxy] at h1
        exact (zero_lt_one.trans (hx.trans h1)).ne'
      have hd := (Real.hasDerivAt_log ht0).hasDerivWithinAt (s := Set.Ioi t)
      rwa [← one_div] at hd
    · exact ContinuousOn.div continuousOn_const continuousOn_id hne
    · rintro u ⟨t, ht, rfl⟩
      refine ContinuousAt.continuousWithinAt ?_
      exact ContinuousAt.div (by fun_prop) (by fun_prop) (Real.log_pos (hpos t ht)).ne'
  rw [← hsub]
  refine intervalIntegral.integral_congr fun t ht => ?_
  have ht1 : 1 < t := hpos t ht
  have : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
  simp only [Function.comp_apply, smul_eq_mul]
  field_simp

/-- **The main term of a block, sharply.**  For `τ > 0` and `1 < y₁ ≤ y₂`,
`|∫_{y₁}^{y₂} cos (τ log t) / (t log t) dt| ≤ 3 / (τ log y₁)`, however long the block and with no
lower bound on `τ log y₁`: `RMF.integral_cos_log_div_eq` followed by
`RMF.abs_integral_cos_div_tail_le'`.  The oscillation of `cos(τu)` against `1/u` gains the factor
`1/(τ log y₁)` of the block decorrelation estimate over the trivial bound. -/
lemma abs_integral_cos_log_div_tail_le {τ y₁ y₂ : ℝ} (hτ : 0 < τ) (hy₁ : 1 < y₁) (hy : y₁ ≤ y₂) :
    |∫ t in y₁..y₂, Real.cos (τ * Real.log t) / (t * Real.log t)|
      ≤ 3 / (τ * Real.log y₁) := by
  rw [integral_cos_log_div_eq hy₁ hy]
  exact abs_integral_cos_div_tail_le' hτ (Real.log_pos hy₁)
    (Real.log_le_log (by linarith) hy)

/-- **The main term of the cosine prime sum.**  For `0 < τ ≤ 1` and `y ≥ 2`,
`|∫_2^y cos (τ log t) / (t log t) dt - log (min (log y) (1/τ) / log 2)| ≤ 4`.

This is `RMF.abs_integral_cos_div_sub_log_min_le` after the substitution `u = log t`. -/
theorem abs_integral_cos_log_div_sub_log_min_le {τ y : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hy : 2 ≤ y) :
    |(∫ t in (2 : ℝ)..y, Real.cos (τ * Real.log t) / (t * Real.log t))
      - Real.log (min (Real.log y) (1 / τ) / Real.log 2)| ≤ 4 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hly : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  rw [integral_cos_log_div_eq (by norm_num) hy]
  exact abs_integral_cos_div_sub_log_min_le hlog2 hly hτ (by nlinarith)

end RMF
