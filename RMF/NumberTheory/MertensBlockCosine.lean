/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.CosinePrimeSum

/-!
# The block cosine sum against explicit Mertens

For `2 ≤ y₁ ≤ y₂` and every `τ`,

`|∑_{y₁ < p ≤ y₂} cos(τ log p)/p - ∫_{y₁}^{y₂} cos(τ log t)/(t log t) dt|
  ≤ K/log y₁ + K/log y₂ + |τ|K(log log y₂ - log log y₁)`,

with `K = log 4 + 6 + (5 log 2 + 3)/4 ≤ 9.0028` (`RMF.mertensErrConst`), the constant of
`Mertens.E₂p.abs_le` with `Mertens.E₁` replaced by its bound `Mertens.E₁.le`.

## The argument

Abel summation of `f(t) = cos(τ log t)` against `S(t) = ∑_{p ≤ t} 1/p = log log t + M + E(t)`.  The
main part `log log t` integrates by parts to `∫ f(t)/(t log t) dt`, the constant `M` cancels, and
what is left is `f(y₂)E(y₂) - f(y₁)E(y₁) - ∫ f'(t)E(t) dt`.  The error `|E(t)| ≤ K/log t` is used
*pointwise* inside the integral, against `|f'(t)| ≤ |τ|/t`, so the integral costs
`|τ|K ∫ dt/(t log t) = |τ|K(log log y₂ - log log y₁)`: one unit of `|τ|K` per unit of `log log`,
however far out the block is.
-/

namespace RMF

/-- **The error constant of Mertens' second theorem**, `log 4 + 6 + (5 log 2 + 3)/4`: the
numerator of `Mertens.E₂p.abs_le` with `Mertens.E₁` replaced by its bound `Mertens.E₁.le`. -/
noncomputable def mertensErrConst : ℝ := Real.log 4 + 6 + (5 * Real.log 2 + 3) / 4

lemma mertensErrConst_nonneg : 0 ≤ mertensErrConst := by
  unfold mertensErrConst
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  positivity

/-- `mertensErrConst ≤ 9.0028`: it is `3.25 log 2 + 6.75 ≈ 9.00273`. -/
lemma mertensErrConst_le : mertensErrConst ≤ 9.0028 := by
  unfold mertensErrConst
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  linarith [Real.log_two_lt_d9]

/-- **Mertens' second theorem with its error constant named**: for `x ≥ 2`,
`|∑_{p ≤ x} 1/p - log log x - M| ≤ mertensErrConst / log x`. -/
theorem abs_sum_prime_div_sub_log_log_sub_mertens_le {x : ℝ} (hx : 2 ≤ x) :
    |(∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p) - Real.log (Real.log x) - Mertens.M|
      ≤ mertensErrConst / Real.log x := by
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  refine (Mertens.E₂p.abs_le hx).trans (div_le_div_of_nonneg_right ?_ hlog.le)
  unfold mertensErrConst
  linarith [Mertens.E₁.le]

/-- **The block cosine sum against Mertens' second theorem.**  For `2 ≤ y₁ ≤ y₂` and every `τ`,
`∑_{y₁ < p ≤ y₂} cos(τ log p)/p` is within
`K/log y₁ + K/log y₂ + |τ|K(log log y₂ - log log y₁)` of `∫_{y₁}^{y₂} cosLogDiv τ`,
`K = mertensErrConst`: Abel summation against `∑_{p ≤ t} 1/p`, with Mertens' error used
pointwise inside the integral. -/
theorem abs_cos_prime_sum_block_sub_integral_le_mertens (τ : ℝ) {y₁ y₂ : ℝ} (hy₁ : 2 ≤ y₁)
    (hy : y₁ ≤ y₂) :
    |(∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p)
        - ∫ t in y₁..y₂, cosLogDiv τ t|
      ≤ mertensErrConst / Real.log y₁ + mertensErrConst / Real.log y₂
        + |τ| * mertensErrConst * (Real.log (Real.log y₂) - Real.log (Real.log y₁)) := by
  have hy₁0 : (0 : ℝ) < y₁ := by linarith
  have hpos : ∀ t ∈ Set.Icc y₁ y₂, 0 < t := fun t ht => hy₁0.trans_le ht.1
  have hone : ∀ t ∈ Set.Icc y₁ y₂, 1 < t := fun t ht => by linarith [ht.1]
  have hIcc : ∀ t ∈ Set.uIcc y₁ y₂, t ∈ Set.Icc y₁ y₂ := fun t ht => by
    rwa [Set.uIcc_of_le hy] at ht
  -- the coefficients, the weight `f` and the main term `L = log log`
  set c : ℕ → ℝ := fun k => if k.Prime then 1 / (k : ℝ) else 0 with hc
  set f : ℝ → ℝ := fun t => Real.cos (τ * Real.log t) with hf
  set f' : ℝ → ℝ := fun t => -Real.sin (τ * Real.log t) * (τ * t⁻¹) with hf'
  set L : ℝ → ℝ := fun t => Real.log (Real.log t) with hL
  set L' : ℝ → ℝ := fun t => t⁻¹ / Real.log t with hL'
  have hfd : ∀ t : ℝ, 0 < t → HasDerivAt f (f' t) t := fun t ht =>
    ((Real.hasDerivAt_log ht.ne').const_mul τ).cos
  have hLd : ∀ t : ℝ, 1 < t → HasDerivAt L (L' t) t := fun t ht =>
    (Real.hasDerivAt_log (zero_lt_one.trans ht).ne').log (Real.log_pos ht).ne'
  have hlogc : ContinuousOn Real.log (Set.Icc y₁ y₂) := continuousOn_log_Icc hy₁0
  have hf'c : ContinuousOn f' (Set.Icc y₁ y₂) :=
    ((Real.continuous_sin.comp_continuousOn (hlogc.const_mul τ)).neg).mul
      (continuousOn_const.mul (continuousOn_id.inv₀ fun t ht => (hpos t ht).ne'))
  have hL'c : ContinuousOn L' (Set.Icc y₁ y₂) :=
    (continuousOn_id.inv₀ fun t ht => (hpos t ht).ne').div hlogc
      fun t ht => (Real.log_pos (hone t ht)).ne'
  have hLc : ContinuousOn L (Set.Icc y₁ y₂) := fun t ht =>
    (hLd t (hone t ht)).continuousAt.continuousWithinAt
  have hf'i : IntervalIntegrable f' MeasureTheory.volume y₁ y₂ :=
    hf'c.intervalIntegrable_of_Icc hy
  have hL'i : IntervalIntegrable L' MeasureTheory.volume y₁ y₂ :=
    hL'c.intervalIntegrable_of_Icc hy
  have hf'L : IntervalIntegrable (fun t => f' t * L t) MeasureTheory.volume y₁ y₂ :=
    (hf'c.mul hLc).intervalIntegrable_of_Icc hy
  -- the partial sums of `c` are Mertens' main term plus its error
  have hT : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k = L t + Mertens.M + Mertens.E₂p t := by
    intro t
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
    have h0 : c 0 = 0 := by simp [hc, Nat.not_prime_zero]
    rw [h0, zero_add]
    have h := Mertens.sum_prime_div_eq t
    rw [Finset.sum_filter] at h
    exact h
  have hTi : IntervalIntegrable (fun t => f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
      MeasureTheory.volume y₁ y₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr
      (integrableOn_mul_sum_Icc c hy₁0.le hf'c.integrableOn_Icc)
  have hEeq : (fun t => f' t * Mertens.E₂p t)
      = fun t => f' t * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) - f' t * L t - Mertens.M * f' t := by
    funext t
    rw [hT t]
    ring
  have hEi : IntervalIntegrable (fun t => f' t * Mertens.E₂p t) MeasureTheory.volume y₁ y₂ := by
    rw [hEeq]
    exact (hTi.sub hf'L).sub (hf'i.const_mul _)
  -- Abel summation
  have hderiv : ∀ t ∈ Set.Icc y₁ y₂, deriv f t = f' t := fun t ht => (hfd t (hpos t ht)).deriv
  have hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc y₁ y₂) :=
    (hf'c.congr hderiv).integrableOn_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul c hy₁0.le hy
    (fun t ht => (hfd t (hpos t ht)).differentiableAt) hf_int
  rw [← intervalIntegral.integral_of_le hy] at habel
  have hcongr : (∫ t in y₁..y₂, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
      = ∫ t in y₁..y₂, f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k :=
    intervalIntegral.integral_congr fun t ht => by rw [hderiv t (hIcc t ht)]
  rw [hcongr] at habel
  have hLHS : (∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p)
      = ∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊, f k * c k := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k.Prime
    · simp only [hc, hf, if_pos hk]
      ring
    · simp only [hc, if_neg hk, mul_zero]
  -- the split of the Abel integral
  have hsplit : (∫ t in y₁..y₂, f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
      = (∫ t in y₁..y₂, f' t * L t) + Mertens.M * (∫ t in y₁..y₂, f' t)
        + ∫ t in y₁..y₂, f' t * Mertens.E₂p t := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hf'L (hf'i.const_mul _),
      ← intervalIntegral.integral_add (hf'L.add (hf'i.const_mul _)) hEi]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hT t]
    ring
  -- the main term, by parts
  have hmain : (∫ t in y₁..y₂, cosLogDiv τ t)
      = f y₂ * L y₂ - f y₁ * L y₁ - ∫ t in y₁..y₂, f' t * L t := by
    rw [← intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun t ht => hfd t (hpos t (hIcc t ht))) (fun t ht => hLd t (hone t (hIcc t ht)))
      hf'i hL'i]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [cosLogDiv, hf, hL']
    ring
  have hFTC : (∫ t in y₁..y₂, f' t) = f y₂ - f y₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hfd t (hpos t (hIcc t ht))) hf'i
  have hFTCL : (∫ t in y₁..y₂, L' t) = L y₂ - L y₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hLd t (hone t (hIcc t ht))) hL'i
  -- the difference is Mertens' error, weighted
  have hD : (∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p)
        - ∫ t in y₁..y₂, cosLogDiv τ t
      = f y₂ * Mertens.E₂p y₂ - f y₁ * Mertens.E₂p y₁
        - ∫ t in y₁..y₂, f' t * Mertens.E₂p t := by
    rw [hLHS, habel, hT y₂, hT y₁, hsplit, hmain, hFTC]
    ring
  -- the three error terms
  have hE : ∀ t : ℝ, 2 ≤ t → |Mertens.E₂p t| ≤ mertensErrConst / Real.log t := fun t ht =>
    abs_sum_prime_div_sub_log_log_sub_mertens_le ht
  have hb : ∀ t : ℝ, 2 ≤ t → |f t * Mertens.E₂p t| ≤ mertensErrConst / Real.log t := by
    intro t ht
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans (hE t ht)
  have hpt : ∀ t ∈ Set.Icc y₁ y₂,
      |f' t * Mertens.E₂p t| ≤ |τ| * mertensErrConst * L' t := by
    intro t ht
    have ht0 : 0 < t := hpos t ht
    have h1 : |f' t| ≤ |τ| * t⁻¹ := by
      simp only [hf']
      rw [abs_mul, abs_neg, abs_mul, abs_of_pos (inv_pos.2 ht0)]
      exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (inv_nonneg.2 ht0.le))
        (Real.abs_sin_le_one _)
    rw [abs_mul]
    calc |f' t| * |Mertens.E₂p t|
        ≤ (|τ| * t⁻¹) * (mertensErrConst / Real.log t) :=
          mul_le_mul h1 (hE t (hy₁.trans ht.1)) (abs_nonneg _)
            (mul_nonneg (abs_nonneg _) (inv_nonneg.2 ht0.le))
      _ = |τ| * mertensErrConst * L' t := by
          simp only [hL']
          ring
  have hint : |∫ t in y₁..y₂, f' t * Mertens.E₂p t|
      ≤ |τ| * mertensErrConst * (L y₂ - L y₁) := by
    calc |∫ t in y₁..y₂, f' t * Mertens.E₂p t|
        ≤ ∫ t in y₁..y₂, |f' t * Mertens.E₂p t| :=
          intervalIntegral.abs_integral_le_integral_abs hy
      _ ≤ ∫ t in y₁..y₂, |τ| * mertensErrConst * L' t :=
          intervalIntegral.integral_mono_on hy hEi.abs (hL'i.const_mul _) hpt
      _ = |τ| * mertensErrConst * (L y₂ - L y₁) := by
          rw [intervalIntegral.integral_const_mul, hFTCL]
  rw [hD]
  have h2 := hb y₂ (hy₁.trans hy)
  have h1 := hb y₁ hy₁
  calc |f y₂ * Mertens.E₂p y₂ - f y₁ * Mertens.E₂p y₁ - ∫ t in y₁..y₂, f' t * Mertens.E₂p t|
      ≤ |f y₂ * Mertens.E₂p y₂| + |f y₁ * Mertens.E₂p y₁|
        + |∫ t in y₁..y₂, f' t * Mertens.E₂p t| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ mertensErrConst / Real.log y₂ + mertensErrConst / Real.log y₁
        + |τ| * mertensErrConst * (L y₂ - L y₁) := add_le_add (add_le_add h2 h1) hint
    _ = _ := by
        simp only [hL]
        ring

end RMF
