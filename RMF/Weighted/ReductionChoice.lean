/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Reduction
import RMF.Weighted.PrimorialBound
import RMF.Weighted.SmoothTail
import RMF.Weighted.EulerMomentHalf
import PrimeNumberTheoremAnd.Consequences

/-!
# The reduction's choice of parameters

`RMF.exists_integral_rpow_weightedRademacherSum_le` leaves `y` and `σ` free.  The application
fixes them, with `U = 4 log log x`:

`y = x^(1/(4 log log x))`,  `σ = 1/log x`,

and this file discharges the reduction's six hypotheses at that choice, for all large `x`.

Five of the six are routine growth statements.  The sixth, `⌊x⌋₊ ≤ primorial y`, is the one with
content: it needs a **lower** bound on the primorial, which by
`Chebyshev.theta_eq_log_primorial` is a lower bound on `θ`.  That comes from
`chebyshev_asymptotic` in `PrimeNumberTheoremAnd` — which is `sorryAx`-free, so the corollary
inherits nothing.

`σ·log(x/y) ≤ 1` is free at this `σ`: it says `1 - log y/log x ≤ 1`, i.e. `y ≥ 1`.

The growth estimates are proved here.  The one with content is that this `y` outgrows
`log x`: writing `L = log x` it says `exp(L/(4 log L)) ≥ 2L + 1`, which reduces to
`L ≥ 8 (log L)²`, and that follows from `log u ≤ 2√u` applied **twice** — once to `L` and once to
`√L` — giving `log L ≤ 4 L^{1/4}` and hence `(log L)² ≤ 16 √L`.  The threshold that makes the
arithmetic close is `x ≥ e^16384`.
-/

open Finset MeasureTheory

namespace RMF

/-- The reduction's smoothness parameter, `y = x^(1/U)` with `U = 4 log log x`.

**Not** Harper's own parameter: he uses a *family* of scales, the `x^(e^{-(k+1)})`-smooth partial
products for `0 ≤ k ≤ log log x`.  The single-parameter reduction here follows Harper's method
and Gorodetsky–Wong (Lemma 1.2). -/
noncomputable def reductionY (x : ℝ) : ℕ := ⌊x ^ (1 / (4 * Real.log (Real.log x)))⌋₊

/-- The reduction's abscissa offset, `σ = 1/log x`. -/
noncomputable def reductionSigma (x : ℝ) : ℝ := 1 / Real.log x

/-- The standing facts at `x ≥ e^16384`: `log x ≥ 16384` and `log log x ≥ 1`. -/
theorem reduction_log_bounds {x : ℝ} (hx : Real.exp 16384 ≤ x) :
    (1 : ℝ) ≤ x ∧ (16384 : ℝ) ≤ Real.log x ∧ (1 : ℝ) ≤ Real.log (Real.log x) := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  have hL : (16384 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 16384) hx
    rwa [Real.log_exp] at h
  refine ⟨hx1, hL, ?_⟩
  have hlx : (0 : ℝ) < Real.log x := by linarith
  refine (Real.le_log_iff_exp_le hlx).2 ?_
  linarith [Real.exp_one_lt_d9]

/-- The parameter `y` is below `x`. -/
theorem eventually_reductionY_le : ∀ᶠ x : ℝ in Filter.atTop, ((reductionY x : ℕ) : ℝ) ≤ x := by
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 16384)] with x hx
  obtain ⟨hx1, hL, hLL⟩ := reduction_log_bounds hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hu1 : 1 / (4 * Real.log (Real.log x)) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  calc ((reductionY x : ℕ) : ℝ) ≤ x ^ (1 / (4 * Real.log (Real.log x))) := by
        exact Nat.floor_le (Real.rpow_nonneg hx0.le _)
    _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hu1
    _ = x := Real.rpow_one x

/-- The parameter `y` outgrows `log x`.  This is what makes `x ≤ primorial y` possible: writing
`L = log x`, it says `exp(L/(4 log L)) ≥ 2L`, i.e. `L ≥ 4(log L)² + 4 log 2 · log L`. -/
theorem eventually_two_log_le_reductionY :
    ∀ᶠ x : ℝ in Filter.atTop, 2 * Real.log x ≤ ((reductionY x : ℕ) : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 16384)] with x hx
  obtain ⟨hx1, hL, hLL⟩ := reduction_log_bounds hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  -- `(log L)² ≤ 16 √L`, from `log ≤ 2√·` applied twice
  have hsq : (Real.log (Real.log x)) ^ 2 ≤ 16 * Real.sqrt (Real.log x) := by
    have h1 : Real.log (Real.log x) ≤ 4 * Real.sqrt (Real.sqrt (Real.log x)) := by
      have h2 := log_le_two_mul_sqrt (y := Real.sqrt (Real.log x)) (Real.sqrt_pos.2 hL0)
      rw [Real.log_sqrt hL0.le] at h2
      linarith
    have h4 : (Real.log (Real.log x)) ^ 2 ≤ (4 * Real.sqrt (Real.sqrt (Real.log x))) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h1 2
    have h5 : (4 * Real.sqrt (Real.sqrt (Real.log x))) ^ 2 = 16 * Real.sqrt (Real.log x) := by
      rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
      ring
    linarith
  -- `√L ≥ 128`, hence `8 (log L)² ≤ 128 √L ≤ L`
  have hs128 : (128 : ℝ) ≤ Real.sqrt (Real.log x) := by
    rw [show (128 : ℝ) = Real.sqrt 16384 by
      rw [show (16384 : ℝ) = 128 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hL
  have hkey : 8 * (Real.log (Real.log x)) ^ 2 ≤ Real.log x := by
    have h6 : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
      Real.mul_self_sqrt hL0.le
    have h7 : (128 : ℝ) * Real.sqrt (Real.log x)
        ≤ Real.sqrt (Real.log x) * Real.sqrt (Real.log x) :=
      mul_le_mul_of_nonneg_right hs128 (Real.sqrt_nonneg _)
    linarith
  -- `log(2L+1) ≤ 2 log L ≤ L/(4 log L)`
  have hcmp : 2 * Real.log x + 1 ≤ (Real.log x) ^ 2 := by
    have h8 : (16384 : ℝ) * Real.log x ≤ Real.log x * Real.log x :=
      mul_le_mul_of_nonneg_right hL hL0.le
    have h9 : (Real.log x) ^ 2 = Real.log x * Real.log x := pow_two _
    linarith
  have hlog2L : Real.log (2 * Real.log x + 1) ≤ 2 * Real.log (Real.log x) := by
    have h10 := Real.log_le_log (by linarith) hcmp
    rwa [Real.log_pow] at h10
  have hmid : 2 * Real.log (Real.log x)
      ≤ Real.log x / (4 * Real.log (Real.log x)) := by
    rw [le_div_iff₀ (by linarith)]
    have h11 : 2 * Real.log (Real.log x) * (4 * Real.log (Real.log x))
        = 8 * (Real.log (Real.log x)) ^ 2 := by ring
    linarith
  -- so `x^u ≥ 2L + 1`, and the floor loses less than 1
  have hxu : 2 * Real.log x + 1 ≤ x ^ (1 / (4 * Real.log (Real.log x))) := by
    rw [Real.rpow_def_of_pos hx0]
    have h12 : Real.log (2 * Real.log x + 1)
        ≤ Real.log x * (1 / (4 * Real.log (Real.log x))) := by
      rw [mul_one_div]
      linarith
    have h13 := Real.exp_le_exp.2 h12
    rwa [Real.exp_log (by linarith)] at h13
  have hfl : x ^ (1 / (4 * Real.log (Real.log x))) < ((reductionY x : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  linarith

/-- The parameter `y` tends to infinity — immediate from outgrowing `2 log x`. -/
theorem tendsto_reductionY_atTop :
    Filter.Tendsto (fun x : ℝ => ((reductionY x : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun B => ?_
  filter_upwards [eventually_two_log_le_reductionY,
    (Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2)).eventually_ge_atTop B]
    with x h1 h2
  linarith

/-- **The reduction at its own parameters.**  For all large `x`, with `y = x^(1/(4 log log x))`
and `σ = 1/log x`. -/
theorem exists_integral_rpow_weightedRademacherSum_le_reduction :
    ∃ C x₀ : ℝ, 0 < C ∧ 0 < x₀ ∧
      ∀ q : ℝ, 0 < q → 2 * q ≤ 1 →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
      ∀ x : ℝ, x₀ ≤ x →
        (∫ ω, ‖weightedRademacherSum
            (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
          ≤ C * ((∫ ω, ((Real.log (reductionY x : ℕ))⁻¹ * ∫ t : ℝ,
                    ‖randomEulerProduct
                        (fun ω => squarefreeExtension fun p => X p ω) (reductionY x + 1)
                        ((1 / 2 : ℂ) + ((reductionSigma x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
                      / (((reductionSigma x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
                + (∫ ω, ‖randomEulerProduct
                    (fun ω => squarefreeExtension fun p => X p ω) (reductionY x + 1) (1 / 2) ω‖
                      ^ (2 * q) ∂μ)
                + (∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial (reductionY x))
                    | m ∈ Nat.smoothNumbers ((reductionY x) + 1) ∧ Squarefree m}, (m : ℝ)⁻¹) ^ q
                + (Real.log x / Real.sqrt (reductionY x) + (Real.log (reductionY x))⁻¹) ^ q) := by
  obtain ⟨C, y₀, hC, hy₀, hprop⟩ := exists_integral_rpow_weightedRademacherSum_le
  obtain ⟨Y, hprim⟩ := exists_floor_le_primorial
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      (2 : ℝ) ≤ ((reductionY x : ℕ) : ℝ) ∧ y₀ ≤ ((reductionY x : ℕ) : ℝ)
        ∧ Y ≤ ((reductionY x : ℕ) : ℝ) ∧ ((reductionY x : ℕ) : ℝ) ≤ x
        ∧ 2 * Real.log x ≤ ((reductionY x : ℕ) : ℝ) ∧ (1 : ℝ) < x := by
    filter_upwards [tendsto_reductionY_atTop.eventually_ge_atTop 2,
      tendsto_reductionY_atTop.eventually_ge_atTop y₀,
      tendsto_reductionY_atTop.eventually_ge_atTop Y, eventually_reductionY_le,
      eventually_two_log_le_reductionY, Filter.eventually_gt_atTop 1] with x a b c d e f
    exact ⟨a, b, c, d, e, f⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨C, max x₀ 1, hC, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro q hq0 hq2 Ω' _ X μ hX x hx
  obtain ⟨h2, hy0, hY, hyx, hlog, hx1⟩ := hx₀ x (le_trans (le_max_left _ _) hx)
  have h2n : 2 ≤ reductionY x := by exact_mod_cast h2
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hlogy : (0 : ℝ) ≤ Real.log (reductionY x) := Real.log_nonneg (by linarith)
  refine hprop q hq0 hq2 Ω' X μ hX (reductionY x) (reductionSigma x) x hy0 hyx
    (hprim (reductionY x) hY x hx1.le hlog) ?_ ?_
  · exact div_pos one_pos hlogx
  · have hne : ((reductionY x : ℕ) : ℝ) ≠ 0 := by positivity
    rw [reductionSigma, Real.log_div (by linarith) hne]
    rw [div_mul_eq_mul_div, one_mul, div_le_one hlogx]
    linarith

/-! ### The smooth tail is dominated by the error term

Rankin at `δ = 1/log y` gives `T ≤ x^{-1/log y} ∏_{p≤y}(1+p^{δ-1}) ≪ (log y)^e · e^{-log x/log y}`.
At this `y` one has `log x/log y ≥ 4 log log x`, so that is `≪ (log x)^{e-4}`, and `e - 4 < -1`
is exactly what makes the tail smaller than the `(log y)^{-1}` already present in the error. -/

/-- The parameter `y` has `log y ≤ log x/(4 log log x)` — the floor only helps. -/
theorem eventually_log_reductionY_le :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.log (reductionY x) ≤ Real.log x / (4 * Real.log (Real.log x)) := by
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 16384)] with x hx
  obtain ⟨hx1, hL, hLL⟩ := reduction_log_bounds hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hfl : ((reductionY x : ℕ) : ℝ) ≤ x ^ (1 / (4 * Real.log (Real.log x))) :=
    Nat.floor_le (Real.rpow_nonneg hx0.le _)
  have h1 : Real.log (reductionY x) ≤ Real.log (x ^ (1 / (4 * Real.log (Real.log x)))) := by
    rcases le_or_gt ((reductionY x : ℕ) : ℝ) 0 with h | h
    · have : Real.log (reductionY x) = 0 := by
        have : ((reductionY x : ℕ) : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
        rw [this, Real.log_zero]
      rw [this]
      exact Real.log_nonneg (Real.one_le_rpow hx1 (by positivity))
    · exact Real.log_le_log h hfl
  rwa [Real.log_rpow hx0, one_div, inv_mul_eq_div] at h1

/-- **The smooth tail is at most a constant times the error term already present.** -/
theorem exists_smoothTail_le_error :
    ∃ C x₀ : ℝ, 0 < C ∧ 0 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial (reductionY x))
          | m ∈ Nat.smoothNumbers (reductionY x + 1) ∧ Squarefree m}, ((m : ℝ))⁻¹
        ≤ C * (Real.log x / Real.sqrt (reductionY x) + (Real.log (reductionY x))⁻¹) := by
  obtain ⟨C₁, hC₁, hprod⟩ := exists_prod_one_add_rpow_le
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_ge_atTop (Real.exp 16384)).and
      (eventually_log_reductionY_le.and (tendsto_reductionY_atTop.eventually_ge_atTop 2)))
  refine ⟨C₁, max x₁ (Real.exp 16384), hC₁, by positivity, ?_⟩
  intro x hx
  obtain ⟨hxe, hlogle, hy2⟩ := hx₁ x (le_trans (le_max_left _ _) hx)
  obtain ⟨hx1, hL, hLL⟩ := reduction_log_bounds hxe
  have hx0 : (0 : ℝ) < x := by linarith
  have hy2n : 2 ≤ reductionY x := by exact_mod_cast hy2
  have hyR : (2 : ℝ) ≤ ((reductionY x : ℕ) : ℝ) := hy2
  have hlogy : (0 : ℝ) < Real.log (reductionY x) := Real.log_pos (by linarith)
  -- Rankin at `δ = 1/log y`
  have hδ : (0 : ℝ) < 1 / Real.log (reductionY x) := by positivity
  have hδy : (1 / Real.log (reductionY x)) * Real.log (reductionY x) ≤ 1 := by
    rw [one_div, inv_mul_cancel₀ hlogy.ne']
  have hrank := smoothTailSum_le_rankin (reductionY x) hx0 hδ
  have hpr := hprod (reductionY x) hy2n (1 / Real.log (reductionY x)) hδ hδy
  -- `x^{-1/log y} ≤ (log x)^{-4}`, since `log x / log y ≥ 4 log log x`
  have hlogx : (0 : ℝ) < Real.log x := by linarith
  have hLL0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  have h1 : Real.log (reductionY x) * (4 * Real.log (Real.log x)) ≤ Real.log x := by
    rwa [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Real.log (Real.log x))] at hlogle
  have h2 : 4 * Real.log (Real.log x) ≤ Real.log x / Real.log (reductionY x) := by
    rw [le_div_iff₀ hlogy]
    linarith
  have hyx : Real.log (reductionY x) ≤ Real.log x := by
    have : Real.log (reductionY x) * 1 ≤ Real.log (reductionY x) * (4 * Real.log (Real.log x)) :=
      mul_le_mul_of_nonneg_left (by linarith) hlogy.le
    linarith
  have hpow : x ^ (-(1 / Real.log (reductionY x))) ≤ (Real.log x) ^ (-(4 : ℝ)) := by
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hlogx]
    refine Real.exp_le_exp.2 ?_
    have h3 : Real.log x * -(1 / Real.log (reductionY x))
        = -(Real.log x / Real.log (reductionY x)) := by field_simp
    rw [h3]
    linarith
  -- assemble: `T ≤ (log x)^{-4} · C₁ (log y)^e ≤ C₁ (log x)^{e-4} ≤ C₁ (log x)^{-1}`
  have hprod0 : (0 : ℝ) ≤ ∏ p ∈ Nat.primesBelow (reductionY x + 1),
      (1 + (p : ℝ) ^ ((1 / Real.log (reductionY x)) - 1)) :=
    Finset.prod_nonneg fun p _ => by positivity
  have hle : (Real.log (reductionY x)) ^ (Real.exp 1) ≤ (Real.log x) ^ (Real.exp 1) :=
    Real.rpow_le_rpow hlogy.le hyx (Real.exp_pos 1).le
  have hcomb : x ^ (-(1 / Real.log (reductionY x)))
      * ∏ p ∈ Nat.primesBelow (reductionY x + 1), (1 + (p : ℝ) ^ ((1 / Real.log (reductionY x)) -
        1))
      ≤ (Real.log x) ^ (-(4 : ℝ)) * (C₁ * (Real.log x) ^ (Real.exp 1)) := by
    refine mul_le_mul hpow (le_trans hpr ?_) hprod0 (Real.rpow_nonneg hlogx.le _)
    exact mul_le_mul_of_nonneg_left hle hC₁.le
  have hx1' : (1 : ℝ) ≤ Real.log x := by linarith
  have hexp : (Real.log x) ^ (-(4 : ℝ)) * (Real.log x) ^ (Real.exp 1)
      = (Real.log x) ^ (Real.exp 1 - 4) := by
    rw [← Real.rpow_add hlogx]
    ring_nf
  have hmono : (Real.log x) ^ (Real.exp 1 - 4) ≤ (Real.log x) ^ (-(1 : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le hx1' ?_
    linarith [Real.exp_one_lt_d9]
  have hinv : (Real.log x) ^ (-(1 : ℝ)) = (Real.log x)⁻¹ := Real.rpow_neg_one _
  have hfinal : (Real.log x)⁻¹ ≤ (Real.log (reductionY x))⁻¹ := by
    exact inv_anti₀ hlogy hyx
  have hsqrt : (0 : ℝ) ≤ Real.log x / Real.sqrt (reductionY x) := by positivity
  calc ∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial (reductionY x))
        | m ∈ Nat.smoothNumbers (reductionY x + 1) ∧ Squarefree m}, ((m : ℝ))⁻¹
      ≤ x ^ (-(1 / Real.log (reductionY x)))
          * ∏ p ∈ Nat.primesBelow (reductionY x + 1),
            (1 + (p : ℝ) ^ ((1 / Real.log (reductionY x)) - 1)) := hrank
    _ ≤ (Real.log x) ^ (-(4 : ℝ)) * (C₁ * (Real.log x) ^ (Real.exp 1)) := hcomb
    _ = C₁ * ((Real.log x) ^ (-(4 : ℝ)) * (Real.log x) ^ (Real.exp 1)) := by ring
    _ = C₁ * (Real.log x) ^ (Real.exp 1 - 4) := by rw [hexp]
    _ ≤ C₁ * (Real.log (reductionY x))⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ hC₁.le
        calc (Real.log x) ^ (Real.exp 1 - 4) ≤ (Real.log x) ^ (-(1 : ℝ)) := hmono
          _ = (Real.log x)⁻¹ := hinv
          _ ≤ (Real.log (reductionY x))⁻¹ := hfinal
    _ ≤ C₁ * (Real.log x / Real.sqrt (reductionY x) + (Real.log (reductionY x))⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ hC₁.le
        linarith

end RMF
