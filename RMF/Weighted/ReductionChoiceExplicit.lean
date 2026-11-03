/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ReductionChoice

/-!
# The reduction at the chosen scales, explicit in `x`

`RMF.exists_integral_rpow_weightedRademacherSum_le_reduction` leaves four terms and an
eventually-quantifier.  This file collapses them to two and makes the `x`-dependence explicit.

## Main results

* `RMF.exists_integral_rpow_weightedRademacherSum_le_reduction_explicit`
-/

open MeasureTheory
open scoped Real

namespace RMF

/-! ### The two-term form, explicit in `x`

Two absorptions collapse the four terms to two.  The smooth tail is below the smoothing error
(`exists_smoothTail_le_error`), and the smoothing error is in turn below the Euler moment: on
`0 < q ≤ ½` one has `q(2q-1) - (-q) = 2q² > 0`, so `(log y)^{-q} ≤ (log y)^{q(2q-1)}`.

Then `E‖F_y(½)‖^{2q} ≪ (log y)^{q(2q-1)}` (`exists_moment_half_le`) and, since `q(1-2q) ≥ 0`,
`(log y)^{q(2q-1)} = ((log y)⁻¹)^{q(1-2q)}`, so a **lower** bound on `log y` makes it explicit:
`log y ≥ log x/(8 log log x)` gives `(8 log log x/log x)^{q(1-2q)}`.

The fourth term `(log x/√y + (log y)⁻¹)^q` collapses to `(2 (log y)⁻¹)^q` because
`eventually_pow_log_le_reductionY` gives `√y ≥ (log x)² ≥ log x · log y`. -/

/-- The smoothing error is dominated by the Euler moment: `q(2q-1) - (-q) = 2q² ≥ 0`, any `q`. -/
theorem rpow_neg_le_rpow_moment {t q : ℝ} (ht : 1 ≤ t) :
    t ^ (-q) ≤ t ^ (q * (2 * q - 1)) := by
  refine Real.rpow_le_rpow_of_exponent_le ht ?_
  nlinarith [sq_nonneg q]

/-- `log y ≥ log x/(8 log log x)` at this `y`: the floor costs at most a factor two.

Writing `u = 1/(4 log log x)`, the floor satisfies `⌊x^u⌋₊ > x^u - 1 ≥ x^u/2` once `x^u ≥ 2`, so
`log y ≥ u log x - log 2`, and `u log x ≥ 2 > 2 log 2` turns that into `u log x/2`. -/
theorem eventually_log_reductionY_ge :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x / (8 * Real.log (Real.log x)) ≤ Real.log (reductionY x) := by
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 16384)] with x hx
  obtain ⟨hx1, hL, hLL⟩ := reduction_log_bounds hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hLL0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  -- `8 log log x ≤ log x`, from `log u ≤ 2√u` and `√(log x) ≥ 128`
  have hs128 : (128 : ℝ) ≤ Real.sqrt (Real.log x) := by
    rw [show (128 : ℝ) = Real.sqrt 16384 by
      rw [show (16384 : ℝ) = 128 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hL
  have hsl : Real.log (Real.log x) ≤ 2 * Real.sqrt (Real.log x) := log_le_two_mul_sqrt hL0
  have hmul : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
    Real.mul_self_sqrt hL0.le
  have hlin : (16 : ℝ) * Real.sqrt (Real.log x)
      ≤ Real.sqrt (Real.log x) * Real.sqrt (Real.log x) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have h8 : 8 * Real.log (Real.log x) ≤ Real.log x := by linarith
  -- hence `u log x = log x/(4 log log x) ≥ 2`, and in particular `x^u ≥ 2`
  have huL : (2 : ℝ) ≤ Real.log x / (4 * Real.log (Real.log x)) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * Real.log (Real.log x))]
    linarith
  have hxu2 : (2 : ℝ) ≤ x ^ (1 / (4 * Real.log (Real.log x))) := by
    rw [Real.rpow_def_of_pos hx0, mul_one_div]
    have h1 := Real.exp_le_exp.2 huL
    have h2 := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hxupos : (0 : ℝ) < x ^ (1 / (4 * Real.log (Real.log x))) := by linarith
  have hfl : x ^ (1 / (4 * Real.log (Real.log x))) < ((reductionY x : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hhalf : x ^ (1 / (4 * Real.log (Real.log x))) / 2 ≤ ((reductionY x : ℕ) : ℝ) := by
    linarith
  have hpos2 : (0 : ℝ) < x ^ (1 / (4 * Real.log (Real.log x))) / 2 := by linarith
  have hlog := Real.log_le_log hpos2 hhalf
  rw [Real.log_div (ne_of_gt hxupos) (by norm_num : (2 : ℝ) ≠ 0), Real.log_rpow hx0, one_div,
    inv_mul_eq_div] at hlog
  have htwo : 2 * (Real.log x / (8 * Real.log (Real.log x)))
      = Real.log x / (4 * Real.log (Real.log x)) := by
    rw [show (8 : ℝ) * Real.log (Real.log x) = 4 * Real.log (Real.log x) * 2 by ring, ← div_div]
    ring
  linarith [Real.log_two_lt_d9]

/-- The parameter `y` outgrows `(log x)^4`.  This is what makes the smoothing error's `log x/√y`
smaller than the `(log y)⁻¹` beside it: `√y ≥ (log x)^2 ≥ log x · log y`.

Writing `L = log x` it says `exp(L/(4 log L)) ≥ L^4 + 1`, which reduces to `L ≥ 20 (log L)^2`, and
the same `(log L)^2 ≤ 16 √L` used for `eventually_two_log_le_reductionY` closes it at
`x ≥ e^262144`. -/
theorem eventually_pow_log_le_reductionY :
    ∀ᶠ x : ℝ in Filter.atTop, (Real.log x) ^ (4 : ℕ) ≤ ((reductionY x : ℕ) : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 262144)] with x hx
  have hxe : Real.exp 16384 ≤ x := le_trans (Real.exp_le_exp.2 (by norm_num)) hx
  obtain ⟨hx1, -, hLL⟩ := reduction_log_bounds hxe
  have hL : (262144 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 262144) hx
    rwa [Real.log_exp] at h
  have hx0 : (0 : ℝ) < x := by linarith
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hLL0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  -- `(log L)^2 ≤ 16 √L`, from `log ≤ 2√·` applied twice
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
  -- `√L ≥ 512`, hence `20 (log L)^2 ≤ 320 √L ≤ L`
  have hs512 : (512 : ℝ) ≤ Real.sqrt (Real.log x) := by
    rw [show (512 : ℝ) = Real.sqrt 262144 by
      rw [show (262144 : ℝ) = 512 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hL
  have hkey : 20 * (Real.log (Real.log x)) ^ 2 ≤ Real.log x := by
    have h6 : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
      Real.mul_self_sqrt hL0.le
    have h7 : (512 : ℝ) * Real.sqrt (Real.log x)
        ≤ Real.sqrt (Real.log x) * Real.sqrt (Real.log x) :=
      mul_le_mul_of_nonneg_right hs512 (Real.sqrt_nonneg _)
    linarith
  -- `log(L^4 + 1) ≤ 5 log L ≤ L/(4 log L)`
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hp4 : (1 : ℝ) ≤ (Real.log x) ^ (4 : ℕ) := one_le_pow₀ hL1
  have hcmp : (Real.log x) ^ (4 : ℕ) + 1 ≤ (Real.log x) ^ (5 : ℕ) := by
    have h8 : (Real.log x) ^ (5 : ℕ) = (Real.log x) ^ (4 : ℕ) * Real.log x := by ring
    have h9 : (Real.log x) ^ (4 : ℕ) * 2 ≤ (Real.log x) ^ (4 : ℕ) * Real.log x :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hlog5 : Real.log ((Real.log x) ^ (5 : ℕ)) = 5 * Real.log (Real.log x) := by
    rw [Real.log_pow]
    norm_num
  have hlogcmp : Real.log ((Real.log x) ^ (4 : ℕ) + 1) ≤ 5 * Real.log (Real.log x) := by
    have h10 := Real.log_le_log (by linarith) hcmp
    rwa [hlog5] at h10
  have hmid : 5 * Real.log (Real.log x) ≤ Real.log x / (4 * Real.log (Real.log x)) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * Real.log (Real.log x))]
    have h11 : 5 * Real.log (Real.log x) * (4 * Real.log (Real.log x))
        = 20 * (Real.log (Real.log x)) ^ 2 := by ring
    linarith
  -- so `x^u ≥ L^4 + 1`, and the floor loses less than 1
  have hxu : (Real.log x) ^ (4 : ℕ) + 1 ≤ x ^ (1 / (4 * Real.log (Real.log x))) := by
    rw [Real.rpow_def_of_pos hx0, mul_one_div]
    have h12 : Real.log ((Real.log x) ^ (4 : ℕ) + 1)
        ≤ Real.log x / (4 * Real.log (Real.log x)) := by linarith
    have h13 := Real.exp_le_exp.2 h12
    rwa [Real.exp_log (by linarith)] at h13
  have hfl : x ^ (1 / (4 * Real.log (Real.log x))) < ((reductionY x : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  linarith

/-- **The reduction at its own parameters, in two terms and explicit in `x`.**

`E‖S(x)‖^{2q} ≤ C ( E[Z^q] + (8 log log x / log x)^{q(1-2q)} )`

with `y = x^{1/(4 log log x)}`, `σ = 1/log x`.  Only `E[Z^q]` is left symbolic — that is where the
chaos estimates enter. -/
theorem exists_integral_rpow_weightedRademacherSum_le_reduction_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ 0 < x₀ ∧
      ∀ q : ℝ, 0 < q → 2 * q ≤ 1 →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
      ∀ x : ℝ, x₀ ≤ x →
        (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
          ∂μ)
          ≤ C * ((∫ ω, ((Real.log (reductionY x))⁻¹ * ∫ t : ℝ,
                    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (reductionY x
                      + 1)
                        ((1 / 2 : ℂ) + ((reductionSigma x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
                      / (((reductionSigma x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
              + (8 * Real.log (Real.log x) / Real.log x) ^ (q * (1 - 2 * q))) := by
  obtain ⟨C₁, x₁, hC₁, hx₁, hfour⟩ := exists_integral_rpow_weightedRademacherSum_le_reduction
  obtain ⟨C₃, x₃, hC₃, hx₃, htail⟩ := exists_smoothTail_le_error
  obtain ⟨C₂, hC₂, hmom⟩ := exists_moment_half_le (Q := 1) zero_le_one
  obtain ⟨x₄, hx₄⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_ge_atTop (Real.exp 16384)).and
      (eventually_log_reductionY_ge.and
        (eventually_log_reductionY_le.and
          (eventually_pow_log_le_reductionY.and
            (tendsto_reductionY_atTop.eventually_ge_atTop (max 2 (Real.exp 1)))))))
  have hM1 : (1 : ℝ) ≤ max 1 C₃ := le_max_left 1 C₃
  refine ⟨C₁ * (1 + (C₂ + 2 * max 1 C₃ + 2)), max x₁ (max x₃ (max x₄ 1)),
    mul_pos hC₁ (by linarith), ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ max x₁ (max x₃ (max x₄ 1)) :=
      le_trans (le_max_right x₄ 1) (le_trans (le_max_right x₃ _) (le_max_right x₁ _))
    linarith
  intro q hq0 hq2 Ω' _ X μ hX x hx
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxx₃ : x₃ ≤ x := le_trans (le_trans (le_max_left x₃ _) (le_max_right x₁ _)) hx
  have hxx₄ : x₄ ≤ x :=
    le_trans (le_trans (le_max_left x₄ 1) (le_trans (le_max_right x₃ _) (le_max_right x₁ _))) hx
  obtain ⟨hxe, hge, hlogle, hy4, hylarge⟩ := hx₄ x hxx₄
  obtain ⟨hx1, hL16, hLL1⟩ := reduction_log_bounds hxe
  have hq1 : q ≤ 1 := by linarith
  have hlogx : (0 : ℝ) < Real.log x := by linarith
  have hLL0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  have hy2R : (2 : ℝ) ≤ ((reductionY x : ℕ) : ℝ) := le_trans (le_max_left _ _) hylarge
  have hyE : Real.exp 1 ≤ ((reductionY x : ℕ) : ℝ) := le_trans (le_max_right _ _) hylarge
  have hy2n : 2 ≤ reductionY x := by exact_mod_cast hy2R
  have hy0 : (0 : ℝ) < ((reductionY x : ℕ) : ℝ) := by linarith
  have hlogy1 : (1 : ℝ) ≤ Real.log (reductionY x) := (Real.le_log_iff_exp_le hy0).2 hyE
  have hlogy0 : (0 : ℝ) < Real.log (reductionY x) := by linarith
  have hW0 : (0 : ℝ) ≤ (Real.log (reductionY x))⁻¹ := inv_nonneg.2 hlogy0.le
  have hexp0 : (0 : ℝ) ≤ q * (1 - 2 * q) := mul_nonneg hq0.le (by linarith)
  have hR0 : (0 : ℝ) ≤ (8 * Real.log (Real.log x) / Real.log x) ^ (q * (1 - 2 * q)) :=
    Real.rpow_nonneg (div_nonneg (by linarith) hlogx.le) _
  -- `(log y)⁻¹ ≤ 8 log log x/log x`, which is what makes the bound explicit in `x`
  have hWle : (Real.log (reductionY x))⁻¹ ≤ 8 * Real.log (Real.log x) / Real.log x := by
    have hd0 : (0 : ℝ) < Real.log x / (8 * Real.log (Real.log x)) :=
      div_pos hlogx (by linarith)
    have h := inv_anti₀ hd0 hge
    rwa [inv_div] at h
  have hWR : ((Real.log (reductionY x))⁻¹) ^ (q * (1 - 2 * q))
      ≤ (8 * Real.log (Real.log x) / Real.log x) ^ (q * (1 - 2 * q)) :=
    Real.rpow_le_rpow hW0 hWle hexp0
  have hmomeq : (Real.log (reductionY x)) ^ (q * (2 * q - 1))
      = ((Real.log (reductionY x))⁻¹) ^ (q * (1 - 2 * q)) := by
    rw [Real.inv_rpow hlogy0.le, ← Real.rpow_neg hlogy0.le]
    congr 1
    ring
  -- `log y ≤ log x`, and `√y ≥ (log x)^2`, so `log x/√y ≤ (log y)⁻¹`
  have hyx : Real.log (reductionY x) ≤ Real.log x := by
    have h : Real.log x / (4 * Real.log (Real.log x)) ≤ Real.log x := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * Real.log (Real.log x))]
      have h' := mul_le_mul_of_nonneg_left
        (by linarith : (1 : ℝ) ≤ 4 * Real.log (Real.log x)) hlogx.le
      linarith
    exact le_trans hlogle h
  have hsqy : (Real.log x) ^ (2 : ℕ) ≤ Real.sqrt ((reductionY x : ℕ) : ℝ) := by
    rw [Real.le_sqrt (pow_nonneg hlogx.le 2) (Nat.cast_nonneg _)]
    calc ((Real.log x) ^ (2 : ℕ)) ^ (2 : ℕ) = (Real.log x) ^ (4 : ℕ) := by ring
      _ ≤ ((reductionY x : ℕ) : ℝ) := hy4
  have hdiv : Real.log x / Real.sqrt ((reductionY x : ℕ) : ℝ) ≤ (Real.log (reductionY x))⁻¹ := by
    have hsqrt0 : (0 : ℝ) < Real.sqrt ((reductionY x : ℕ) : ℝ) := Real.sqrt_pos.2 hy0
    rw [div_le_iff₀ hsqrt0]
    have hstep : Real.log x * Real.log (reductionY x) ≤ Real.sqrt ((reductionY x : ℕ) : ℝ) :=
      calc Real.log x * Real.log (reductionY x) ≤ Real.log x * Real.log x :=
            mul_le_mul_of_nonneg_left hyx hlogx.le
        _ = (Real.log x) ^ (2 : ℕ) := by ring
        _ ≤ Real.sqrt ((reductionY x : ℕ) : ℝ) := hsqy
    have h1 := mul_le_mul_of_nonneg_left hstep hW0
    have h2 : (Real.log (reductionY x))⁻¹ * (Real.log x * Real.log (reductionY x))
        = Real.log x := by
      field_simp
    linarith
  have hsum0 : (0 : ℝ) ≤ Real.log x / Real.sqrt ((reductionY x : ℕ) : ℝ)
      + (Real.log (reductionY x))⁻¹ := by
    have h : (0 : ℝ) ≤ Real.log x / Real.sqrt ((reductionY x : ℕ) : ℝ) :=
      div_nonneg hlogx.le (Real.sqrt_nonneg _)
    linarith
  have hsum : Real.log x / Real.sqrt ((reductionY x : ℕ) : ℝ) + (Real.log (reductionY x))⁻¹
      ≤ 2 * (Real.log (reductionY x))⁻¹ := by linarith
  -- `(log y)^{-q} ≤ (log y)^{q(2q-1)}`: this is where `0 < q ≤ ½` is spent
  have hWq : ((Real.log (reductionY x))⁻¹) ^ q
      ≤ (8 * Real.log (Real.log x) / Real.log x) ^ (q * (1 - 2 * q)) :=
    calc ((Real.log (reductionY x))⁻¹) ^ q = (Real.log (reductionY x)) ^ (-q) := by
          rw [Real.inv_rpow hlogy0.le, ← Real.rpow_neg hlogy0.le]
      _ ≤ (Real.log (reductionY x)) ^ (q * (2 * q - 1)) := rpow_neg_le_rpow_moment hlogy1
      _ = ((Real.log (reductionY x))⁻¹) ^ (q * (1 - 2 * q)) := hmomeq
      _ ≤ (8 * Real.log (Real.log x) / Real.log x) ^ (q * (1 - 2 * q)) := hWR
  -- term 4: the smoothing error
  have hterm4 : (Real.log x / Real.sqrt ((reductionY x : ℕ) : ℝ)
        + (Real.log (reductionY x))⁻¹) ^ q
      ≤ 2 * (8 * Real.log (Real.log x) / Real.log x) ^ (q * (1 - 2 * q)) :=
    calc (Real.log x / Real.sqrt ((reductionY x : ℕ) : ℝ) + (Real.log (reductionY x))⁻¹) ^ q
        ≤ (2 * (Real.log (reductionY x))⁻¹) ^ q := Real.rpow_le_rpow hsum0 hsum hq0.le
      _ = (2 : ℝ) ^ q * ((Real.log (reductionY x))⁻¹) ^ q := Real.mul_rpow (by norm_num) hW0
      _ ≤ 2 * (8 * Real.log (Real.log x) / Real.log x) ^ (q * (1 - 2 * q)) := by
          refine mul_le_mul ?_ hWq (Real.rpow_nonneg hW0 q) (by norm_num)
          calc (2 : ℝ) ^ q ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hq1
            _ = 2 := Real.rpow_one 2
  -- term 3: the smooth tail, below the smoothing error by `exists_smoothTail_le_error`
  have hmid3 : (C₃ * (Real.log x / Real.sqrt ((reductionY x : ℕ) : ℝ)
        + (Real.log (reductionY x))⁻¹)) ^ q
      ≤ max 1 C₃ * (2 * (8 * Real.log (Real.log x) / Real.log x) ^ (q * (1 - 2 * q))) := by
    rw [Real.mul_rpow hC₃.le hsum0]
    exact mul_le_mul (rpow_le_max_one hC₃ hq0.le hq1) hterm4 (Real.rpow_nonneg hsum0 q)
      (by linarith)
  have hterm3 := le_trans (Real.rpow_le_rpow (Finset.sum_nonneg fun m _ => by positivity)
    (htail x hxx₃) hq0.le) hmid3
  -- term 2: the Euler moment at `½`
  have hmomle := hmom Ω' (fun ω => squarefreeExtension fun p => X p ω) μ hX.isRademacherRMF q
    (Set.mem_Icc.2 ⟨by linarith, hq1⟩) (reductionY x) hy2n
  have hmid2 : C₂ * (Real.log (reductionY x)) ^ (q * (2 * q - 1))
      ≤ C₂ * (8 * Real.log (Real.log x) / Real.log x) ^ (q * (1 - 2 * q)) := by
    rw [hmomeq]
    exact mul_le_mul_of_nonneg_left hWR hC₂.le
  have hterm2 := le_trans hmomle hmid2
  -- collect the three absorbed terms against the surviving chaos term
  have habs : ∀ a b t e r : ℝ, 0 ≤ a → 0 ≤ r →
      b + t + e ≤ (C₂ + 2 * max 1 C₃ + 2) * r →
      C₁ * (a + b + t + e) ≤ C₁ * (1 + (C₂ + 2 * max 1 C₃ + 2)) * (a + r) := by
    intro a b t e r ha hr h
    have hK0 : (0 : ℝ) ≤ C₂ + 2 * max 1 C₃ + 2 := by linarith
    have hnn : (0 : ℝ) ≤ (C₂ + 2 * max 1 C₃ + 2) * a + r := add_nonneg (mul_nonneg hK0 ha) hr
    have h1 : a + b + t + e ≤ (1 + (C₂ + 2 * max 1 C₃ + 2)) * (a + r) := by linarith
    calc C₁ * (a + b + t + e) ≤ C₁ * ((1 + (C₂ + 2 * max 1 C₃ + 2)) * (a + r)) :=
          mul_le_mul_of_nonneg_left h1 hC₁.le
      _ = C₁ * (1 + (C₂ + 2 * max 1 C₃ + 2)) * (a + r) := by ring
  refine le_trans (hfour q hq0 hq2 Ω' X μ hX x hxx₁) (habs _ _ _ _ _ ?_ hR0 ?_)
  · exact integral_nonneg fun ω =>
      Real.rpow_nonneg (mul_nonneg hW0 (integral_nonneg fun t => by positivity)) q
  · linarith

end RMF
