/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import RMF.Analysis.ShiftWeight
import RMF.EulerProduct.Defs
import RMF.Main
import RMF.Reduction.Periodisation
import RMF.Probability.ChaosMoment
import RMF.Reduction.Steps

/-!
# The reduction to moments of integrals of Euler products

Gorodetsky–Wong, *A short proof of Helson's conjecture*, Lemma 1.2; the same argument is
reproduced in Hamdan, *Partial sums of random multiplicative functions with supercritical divisor
twists* (arXiv:2604.05563), §2.1.  This is the upper half of Harper's theorem (Harper, *Moments of
random multiplicative functions, I*, arXiv:1703.06654), reduced to a statement about the random
Euler product `A_y(s) = ∏_{p ≤ y} (1 - f(p) p^{-s})⁻¹` alone.

## The two forms

Hamdan and Gorodetsky–Wong run the *same* proof and differ only in where they stop.

* **Gorodetsky–Wong** stop at the line integral `∫_ℝ |A_y(1/2+it)/(1/2+it)|² dt`, whose weight
  `|1/2+it|⁻²` makes it converge on its own, so the reduction is uniform for `q ∈ [0,1]`
  (`RMF.reduction_upper`).
* **Hamdan** periodises `∫_ℝ` into `∑_{n ∈ ℤ} ∫_n^{n+1}` and shifts each piece back to `[0,1]`
  (`RMF.periodisation_upper`).  That costs `∑_{n ∈ ℤ} (1 + n²)^(-q)`, finite only for `q > 1/2`.

Gorodetsky–Wong take the same periodisation step inside their Lemma 1.3, at an exponent bounded
away from `1/2`.  Here the Hölder descent of `RMF/Main.lean` reduces both bounds to
`q ∈ [2/3,1]`, so `q > 1/2` costs nothing, and `RMF.reduction_upper_unitIntegral` composes the two.
The printed range in Gorodetsky–Wong is `q ∈ [0, 1-δ]`, but `δ` never appears in their Section 2;
it is inherited from their Theorem 1.1.  The reduction is therefore stated on all of `[0,1]`.

## Ingredients

In dependency order:

1. conditional orthogonality `E[f(n) conj(f(m)) ∣ 𝓕_y] = 1_{n=m}` for `y`-rough `n, m`;
2. the rough–smooth factorisation of `∑_{n ≤ x} f(n)`;
3. the resulting **identity** for `E[|S_x|² ∣ 𝓕_y]`;
4. Rankin's smooth-number bound, twice: on the smooth block and on `y < m ≤ T`;
5. a sieve bound for rough numbers in short intervals, on `T < m ≤ x` — the only source of the
   `1/log y` normalisation;
6. Parseval for Dirichlet series, at `σ = 1/2`;
7. conditional Jensen and subadditivity of `t ↦ t^q`, both with constant `1`.

The split point is `T = x^{3/4}`, which forces `y` to be small against `√x`.
-/

open MeasureTheory

open scoped Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The reduction -/

/-- **The upper reduction for the Steinhaus RMF.**  The `RMF.reduction_upper_of_core` instance;
the mathematics is there. -/
theorem reduction_upper :
    ∃ (C K c : ℝ) (y₀ : ℕ), 0 < C ∧ 0 ≤ K ∧ 0 < c ∧ 2 ≤ y₀ ∧
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ (x : ℝ) (y : ℕ) (q : ℝ), y₀ ≤ y →
          5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ Real.sqrt x / 2 → 0 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ C * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ
              + C * (Real.log y ^ K * Real.exp (-c * Real.log x / Real.log y)) ^ q :=
  reduction_upper_of_core (P := IsSteinhausRMF) reduction_core

/-- **Periodisation** (Hamdan §2.1, final step): for `y ≥ 2` and `1/2 < q ≤ 1`, trading the line
integral for the unit integral costs the factor `8 ∑_{n ∈ ℤ} (1 + n²)^(-q)`, the `8` from
`|1/2 + it|² ≥ (1 + n²)/8` on `t ∈ [n, n+1]`.  The shift of each `∫_n^{n+1}` back to `[0,1]` uses
rotation invariance of the Steinhaus law: `p^{-in}` is a fixed unimodular constant
(`IsSteinhausPrimeValues.mul_unimodular`).  This step, and only this step, needs `q > 1/2`
(`RMF.summable_shiftWeight`). -/
theorem periodisation_upper :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ y q : ℝ, 2 ≤ y → 1 / 2 < q → q ≤ 1 →
        ∫ ω, eulerLineIntegral f y ω ^ q ∂μ
          ≤ 8 * (∑' n : ℤ, shiftWeight q n) * ∫ ω, chaosUnit f y ω ^ q ∂μ := by
  intro f μ hf y q hy hq0 hq1
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI := hX.isProbabilityMeasure
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hunit : ∀ ω, chaosUnit (fun ω => compMultExtension fun p => X p ω) y ω
      = (Real.log y)⁻¹ * ∫ h in Set.Ioc (0 : ℝ) 1, lineSq (1 / 2) X (⌊y⌋₊ + 1) ω h := by
    intro ω
    rw [chaosUnit, intervalIntegral.integral_of_le zero_le_one]
    rfl
  simp_rw [eulerLineIntegral, hunit]
  exact integral_rpow_line_le (1 / 2) (by norm_num) hX (⌊y⌋₊ + 1)
    (inv_nonneg.2 hlog.le) hq0 hq1

/-- **The composite**: the reduction followed by the periodisation, landing on `∫_0^1` on
Harper's range `q ∈ [2/3,1]`.  The periodisation contributes only the factor
`8 ∑_{n ∈ ℤ} (1+n²)^(-2/3) ≈ 58`, uniform in `q` because the weight sum decreases in `q`
(`tsum_shiftWeight_le`); its `q > 1/2` is implied by `q ≥ 2/3`, to which the Hölder descent of
`RMF/Main.lean` reduces both bounds. -/
theorem reduction_upper_unitIntegral :
    ∃ (C K c : ℝ) (y₀ : ℕ), 0 < C ∧ 0 ≤ K ∧ 0 < c ∧ 2 ≤ y₀ ∧
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ (x : ℝ) (y : ℕ) (q : ℝ), y₀ ≤ y →
          5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ Real.sqrt x / 2 → 2 / 3 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ C * ∫ ω, chaosUnit f (y : ℝ) ω ^ q ∂μ
              + C * (Real.log y ^ K * Real.exp (-c * Real.log x / Real.log y)) ^ q := by
  obtain ⟨C, K, c, y₀, hC, hK, hc, hy₀, hred⟩ := reduction_upper (Ω := Ω)
  set S : ℝ := ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun n => shiftWeight_nonneg _ _
  refine ⟨C * (1 + 8 * S), K, c, y₀, by positivity, hK, hc, hy₀, ?_⟩
  intro f μ hf x y q hy₀y hyx hq23 hq1
  have hy0N : (2 : ℕ) ≤ y := le_trans hy₀ hy₀y
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy0N
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  have hunit : (0 : ℝ) ≤ ∫ ω, chaosUnit f y ω ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (chaosUnit_nonneg hy2 ω) _
  have herr : (0 : ℝ) ≤ (Real.log y ^ K * Real.exp (-c * Real.log x / Real.log y)) ^ q :=
    (Real.rpow_pos_of_pos
      (mul_pos (Real.rpow_pos_of_pos hlog _) (Real.exp_pos _)) q).le
  have hw : (∑' n : ℤ, shiftWeight q n) ≤ S := tsum_shiftWeight_le (by norm_num) hq23
  have hline : ∫ ω, eulerLineIntegral f y ω ^ q ∂μ
      ≤ (1 + 8 * S) * ∫ ω, chaosUnit f y ω ^ q ∂μ := by
    refine (periodisation_upper f μ hf y q hy2 (by linarith) hq1).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hunit
  have h1 : C * ∫ ω, eulerLineIntegral f y ω ^ q ∂μ
      ≤ C * (1 + 8 * S) * ∫ ω, chaosUnit f y ω ^ q ∂μ := by
    calc C * ∫ ω, eulerLineIntegral f y ω ^ q ∂μ
        ≤ C * ((1 + 8 * S) * ∫ ω, chaosUnit f y ω ^ q ∂μ) :=
          mul_le_mul_of_nonneg_left hline hC.le
      _ = C * (1 + 8 * S) * ∫ ω, chaosUnit f y ω ^ q ∂μ := by ring
  have h2 : C * (Real.log y ^ K * Real.exp (-c * Real.log x / Real.log y)) ^ q
      ≤ C * (1 + 8 * S) * (Real.log y ^ K * Real.exp (-c * Real.log x / Real.log y)) ^ q :=
    mul_le_mul_of_nonneg_right (by nlinarith) herr
  linarith [hred f μ hf x y q hy₀y hyx (by linarith) hq1]

/-! ### What the reduction is for

Two statements at Harper's own parameters.  The first says the moment we care about is
dominated by the Euler-product moment; the second says that, granted the Euler-product bound
(`RMF.euler_unitIntegral_moment_le`), Harper's upper bound follows. -/

/-- Harper's cutoff: `log y = log x / (log log x)²`. -/
noncomputable def harperCutoff (x : ℝ) : ℝ :=
  Real.exp (Real.log x / Real.log (Real.log x) ^ 2)

/-! ### The cutoff `y = exp(log x / (log log x)²)`

Two mechanical facts before the asymptotics: what `log` of the cutoff is, and what it costs to
replace the cutoff by its integer part, which is what `reduction_upper_unitIntegral` needs since
its `y` ranges over `ℕ`. -/

@[simp]
lemma log_harperCutoff (x : ℝ) :
    Real.log (harperCutoff x) = Real.log x / Real.log (Real.log x) ^ 2 :=
  Real.log_exp _

omit [MeasurableSpace Ω] in
/-- `chaosUnit` at `y` and at `⌊y⌋` differ only in the `(log y)⁻¹` factor: the Euler
product itself is over `primesBelow (⌊y⌋ + 1)` either way.  Rounding down therefore costs at
most a factor `2`, once `y ≥ 4`. -/
lemma chaosUnit_floor_le {f : Ω → ArithmeticFunction ℂ} {y : ℝ} (hy : 4 ≤ y) (ω : Ω) :
    chaosUnit f ((⌊y⌋₊ : ℕ) : ℝ) ω ≤ 2 * chaosUnit f y ω := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hfl : (1 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by
    have : (1 : ℕ) ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ y))
    exact_mod_cast this
  have hfl3 : (3 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by
    have : (3 : ℕ) ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (3 : ℝ) ≤ y))
    exact_mod_cast this
  have hfle : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le hy0.le
  have hlogfl : (0 : ℝ) < Real.log ((⌊y⌋₊ : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  -- the two Euler products agree, since `⌊⌊y⌋⌋ = ⌊y⌋`
  have hfloor : ⌊((⌊y⌋₊ : ℕ) : ℝ)⌋₊ = ⌊y⌋₊ := Nat.floor_natCast _
  -- `y ≤ ⌊y⌋²`, hence `log y ≤ 2 log ⌊y⌋`
  have hsq : y ≤ ((⌊y⌋₊ : ℕ) : ℝ) ^ 2 := by
    have h1 : y - 1 ≤ ((⌊y⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one y
      linarith
    nlinarith
  have hlog2 : Real.log y ≤ 2 * Real.log ((⌊y⌋₊ : ℕ) : ℝ) := by
    have := Real.log_le_log (by linarith) hsq
    rwa [Real.log_pow] at this
  have hJ : (0 : ℝ) ≤ ∫ h in (0 : ℝ)..1,
      ‖randomEulerProduct f (⌊y⌋₊ + 1) (((1 / 2 : ℝ) : ℂ) + (h : ℂ) * Complex.I) ω‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun h _ => by positivity
  rw [chaosUnit, chaosUnit, hfloor, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hJ
  rw [← sub_nonneg]
  have hkey : (Real.log ((⌊y⌋₊ : ℕ) : ℝ))⁻¹ ≤ 2 * (Real.log y)⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ hlogfl]
    have hinv : (0 : ℝ) < (Real.log y)⁻¹ := inv_pos.2 hlogy
    have hmul := mul_le_mul_of_nonneg_left hlog2 hinv.le
    rw [inv_mul_cancel₀ hlogy.ne'] at hmul
    linarith
  linarith

/-! ### Growth facts for the threshold

All the asymptotics below are run through `L = log log x`, and the thresholds are deliberately
generous — the statement only claims *some* `x₀`, so there is no reason to economise.  `L ≥ 36` is
what makes `log L ≤ 2√L ≤ L/3` comfortable. -/

lemma log_le_two_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt ht.le] at h
  linarith

lemma sqrt_le_of_le {L : ℝ} (hL : 36 ≤ L) : (6 : ℝ) ≤ Real.sqrt L := by
  have h := Real.sqrt_le_sqrt hL
  rwa [show Real.sqrt 36 = 6 by
    rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h

lemma three_log_le {L : ℝ} (hL : 36 ≤ L) : 3 * Real.log L ≤ L := by
  have hL0 : (0 : ℝ) < L := by linarith
  have h1 := log_le_two_sqrt hL0
  have h2 := sqrt_le_of_le hL
  nlinarith [Real.sq_sqrt hL0.le, Real.sqrt_nonneg L]

/-- `L³ ≤ e^L` once `L ≥ 36`. -/
lemma cube_le_exp {L : ℝ} (hL : 36 ≤ L) : L ^ 3 ≤ Real.exp L := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hpow : L ^ (3 : ℕ) = Real.exp (Real.log L * 3) := by
    rw [← Real.rpow_natCast L 3, Real.rpow_def_of_pos hL0]
    norm_num
  rw [hpow]
  exact Real.exp_le_exp.2 (by linarith [three_log_le hL])

/-- Consequently `e^L / L² ≥ L`, which is the growth of `log (harperCutoff x)` in terms of
`L = log log x`. -/
lemma le_exp_div_sq {L : ℝ} (hL : 36 ≤ L) : L ≤ Real.exp L / L ^ 2 := by
  have hL0 : (0 : ℝ) < L := by linarith
  rw [le_div_iff₀ (by positivity)]
  calc L * L ^ 2 = L ^ 3 := by ring
    _ ≤ Real.exp L := cube_le_exp hL

/-- The regime the Harper statements are proved in: `x ≥ exp(exp 36)`, which gives
`log x ≥ exp 36` and `L = log log x ≥ 36`.  The threshold is not optimised; the statements only
claim *some* `x₀`. -/
lemma harper_regime {x : ℝ} (hx : Real.exp (Real.exp 36) ≤ x) :
    0 < x ∧ Real.exp 36 ≤ Real.log x ∧ 36 ≤ Real.log (Real.log x) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have h1 : Real.exp 36 ≤ Real.log x := by
    rw [← Real.log_exp (Real.exp 36)]
    exact Real.log_le_log (Real.exp_pos _) hx
  refine ⟨hx0, h1, ?_⟩
  rw [← Real.log_exp 36]
  exact Real.log_le_log (Real.exp_pos _) h1

/-- **The sieve hypothesis holds at the Harper cutoff.**  With `ℓ = log Y = u/L²` the left side is
at most `5e^{5ℓ}` and the right is `e^{u/2}/2`, so it reduces to `log 10 + 5u/L² ≤ u/2`, and
`L ≥ 36` leaves the factor `5/L² ≤ 1/4` with room to spare. -/
lemma harperCutoff_sieve {x : ℝ} (hx : Real.exp (Real.exp 36) ≤ x) :
    5 * ((⌊harperCutoff x⌋₊ : ℝ)) * (1 + Real.log ((⌊harperCutoff x⌋₊ : ℝ))) ^ 3
        * Real.log ((⌊harperCutoff x⌋₊ : ℝ))
      ≤ Real.sqrt x / 2 := by
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx
  have hu0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hu36
  have hu37 : (37 : ℝ) ≤ Real.log x := by
    have := Real.add_one_le_exp (36 : ℝ)
    linarith
  have hL0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  have hlogY : Real.log (harperCutoff x) = Real.log x / Real.log (Real.log x) ^ 2 :=
    log_harperCutoff x
  have hlogY0 : (0 : ℝ) < Real.log (harperCutoff x) := by
    rw [hlogY]; positivity
  have hY1 : (1 : ℝ) < harperCutoff x := by
    rw [harperCutoff, show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.2 (by rw [← hlogY]; exact hlogY0)
  have hY0 : (0 : ℝ) < harperCutoff x := by linarith
  have hy1 : (1 : ℝ) ≤ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ ⌊harperCutoff x⌋₊ := Nat.le_floor (by exact_mod_cast hY1.le)
    exact_mod_cast this
  have hyY : ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) ≤ harperCutoff x := Nat.floor_le hY0.le
  have hlogy0 : 0 ≤ Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := Real.log_nonneg hy1
  have hlogyY : Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) ≤ Real.log (harperCutoff x) :=
    Real.log_le_log (by linarith) hyY
  -- step 1: round up to the cutoff itself
  have step1 : 5 * ((⌊harperCutoff x⌋₊ : ℝ)) * (1 + Real.log ((⌊harperCutoff x⌋₊ : ℝ))) ^ 3
      * Real.log ((⌊harperCutoff x⌋₊ : ℝ))
      ≤ 5 * harperCutoff x * (1 + Real.log (harperCutoff x)) ^ 4 := by
    have h3 : (1 + Real.log ((⌊harperCutoff x⌋₊ : ℝ))) ^ 3
        ≤ (1 + Real.log (harperCutoff x)) ^ 3 := by
      gcongr
    have h4 : Real.log ((⌊harperCutoff x⌋₊ : ℝ)) ≤ 1 + Real.log (harperCutoff x) := by linarith
    have hA : 5 * ((⌊harperCutoff x⌋₊ : ℝ)) ≤ 5 * harperCutoff x := by linarith
    have hB0 : (0 : ℝ) ≤ (1 + Real.log ((⌊harperCutoff x⌋₊ : ℝ))) ^ 3 := by positivity
    have hAB : 5 * ((⌊harperCutoff x⌋₊ : ℝ)) * (1 + Real.log ((⌊harperCutoff x⌋₊ : ℝ))) ^ 3
        ≤ 5 * harperCutoff x * (1 + Real.log (harperCutoff x)) ^ 3 :=
      mul_le_mul hA h3 hB0 (by linarith)
    exact le_trans (mul_le_mul hAB h4 hlogy0 (by positivity)) (le_of_eq (by ring))
  -- step 2: `1 + t ≤ e^t`
  have step2 : 5 * harperCutoff x * (1 + Real.log (harperCutoff x)) ^ 4
      ≤ 5 * Real.exp (5 * Real.log (harperCutoff x)) := by
    have hexp4 : (1 + Real.log (harperCutoff x)) ^ 4
        ≤ Real.exp (4 * Real.log (harperCutoff x)) := by
      have h1 : 1 + Real.log (harperCutoff x) ≤ Real.exp (Real.log (harperCutoff x)) := by
        have := Real.add_one_le_exp (Real.log (harperCutoff x))
        linarith
      calc (1 + Real.log (harperCutoff x)) ^ 4
          ≤ (Real.exp (Real.log (harperCutoff x))) ^ 4 := by
            gcongr
        _ = Real.exp (4 * Real.log (harperCutoff x)) := by
            rw [← Real.exp_nat_mul]
            norm_num
    have hYe : harperCutoff x = Real.exp (Real.log (harperCutoff x)) := (Real.exp_log hY0).symm
    calc 5 * harperCutoff x * (1 + Real.log (harperCutoff x)) ^ 4
        ≤ 5 * Real.exp (Real.log (harperCutoff x))
            * Real.exp (4 * Real.log (harperCutoff x)) := by
          rw [← hYe]
          exact mul_le_mul_of_nonneg_left hexp4 (by positivity)
      _ = 5 * Real.exp (5 * Real.log (harperCutoff x)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          ring_nf
  -- step 3: the numeric inequality
  have step3 : 5 * Real.exp (5 * Real.log (harperCutoff x)) ≤ Real.sqrt x / 2 := by
    have hsq : Real.sqrt x = Real.exp (Real.log x / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
      ring_nf
    have hLsq : (1296 : ℝ) ≤ Real.log (Real.log x) ^ 2 := by nlinarith
    have hbnd : 5 * Real.log (harperCutoff x) ≤ Real.log x / 4 := by
      rw [hlogY]
      have h1 : Real.log x / Real.log (Real.log x) ^ 2 ≤ Real.log x / 1296 := by
        gcongr
      linarith
    have hlog10 : Real.log 10 ≤ 9 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
      linarith
    have h52 : Real.log 5 + Real.log 2 = Real.log 10 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    calc 5 * Real.exp (5 * Real.log (harperCutoff x))
        = Real.exp (Real.log 5 + 5 * Real.log (harperCutoff x)) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ Real.exp (Real.log x / 2 - Real.log 2) := Real.exp_le_exp.2 (by linarith)
      _ = Real.sqrt x / 2 := by
          rw [Real.exp_sub, Real.exp_log (by norm_num), hsq]
  linarith

/-- `log (harperCutoff x) ≥ L`, the growth of the cutoff. -/
lemma log_harperCutoff_ge {x : ℝ} (hx : Real.exp (Real.exp 36) ≤ x) :
    Real.log (Real.log x) ≤ Real.log (harperCutoff x) := by
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx
  have hu0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hu36
  rw [log_harperCutoff]
  have h := le_exp_div_sq hL36
  rwa [Real.exp_log hu0] at h

/-- The cutoff is large. -/
lemma exp_le_harperCutoff {x : ℝ} (hx : Real.exp (Real.exp 36) ≤ x) :
    Real.exp 36 ≤ harperCutoff x := by
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx
  have hY0 : (0 : ℝ) < harperCutoff x := by
    rw [harperCutoff]; exact Real.exp_pos _
  calc Real.exp 36 ≤ Real.exp (Real.log (Real.log x)) := Real.exp_le_exp.2 hL36
    _ ≤ Real.exp (Real.log (harperCutoff x)) := Real.exp_le_exp.2 (log_harperCutoff_ge hx)
    _ = harperCutoff x := Real.exp_log hY0

/-- **The cutoff exceeds `log x`.**  Exponentiating `RMF.log_harperCutoff_ge`.  This is what
turns a threshold on the cutoff into a threshold on `x`: `y₀ ≤ log x ≤ harperCutoff x` as soon as
`x ≥ exp y₀`, with no reference to how the cutoff is built. -/
lemma log_le_harperCutoff {x : ℝ} (hx : Real.exp (Real.exp 36) ≤ x) :
    Real.log x ≤ harperCutoff x := by
  obtain ⟨-, hu36, -⟩ := harper_regime hx
  have hu0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hu36
  have hY0 : (0 : ℝ) < harperCutoff x := by rw [harperCutoff]; exact Real.exp_pos _
  calc Real.log x = Real.exp (Real.log (Real.log x)) := (Real.exp_log hu0).symm
    _ ≤ Real.exp (Real.log (harperCutoff x)) := Real.exp_le_exp.2 (log_harperCutoff_ge hx)
    _ = harperCutoff x := Real.exp_log hY0

/-- **The cutoff exceeds any fixed `m`**, once `L = log log x` does.  The mechanism is
`log (harperCutoff x) = e^L/L² ≥ L`, which is `RMF.le_exp_div_sq`; so a threshold on `L` alone
suffices, with no reference to `x` itself. -/
lemma le_floor_harperCutoff {x : ℝ} (hx : Real.exp (Real.exp 36) ≤ x) {m : ℕ}
    (hm : Real.log ((m : ℝ) + 1) ≤ Real.log (Real.log x)) :
    m ≤ ⌊harperCutoff x⌋₊ := by
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx
  have hu0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hu36
  have hY0 : (0 : ℝ) < harperCutoff x := by
    rw [harperCutoff]
    exact Real.exp_pos _
  have hkey : Real.log (Real.log x) ≤ Real.log (harperCutoff x) := log_harperCutoff_ge hx
  have hYm : ((m : ℝ) + 1) ≤ harperCutoff x := by
    calc ((m : ℝ) + 1) = Real.exp (Real.log ((m : ℝ) + 1)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (Real.log (harperCutoff x)) := Real.exp_le_exp.2 (le_trans hm hkey)
      _ = harperCutoff x := Real.exp_log hY0
  have hfl : m + 1 ≤ ⌊harperCutoff x⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    exact hYm
  omega

/-- The regime at a threshold `T ≥ 36`. -/
lemma harper_regime_of {T x : ℝ} (hT : 36 ≤ T) (hx : Real.exp (Real.exp T) ≤ x) :
    Real.exp (Real.exp 36) ≤ x ∧ T ≤ Real.log (Real.log x) := by
  have h36 : Real.exp (Real.exp 36) ≤ Real.exp (Real.exp T) :=
    Real.exp_le_exp.2 (Real.exp_le_exp.2 hT)
  refine ⟨le_trans h36 hx, ?_⟩
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) (le_trans h36 hx)
  have h1 : Real.exp T ≤ Real.log x := by
    rw [← Real.log_exp (Real.exp T)]
    exact Real.log_le_log (Real.exp_pos _) hx
  rw [← Real.log_exp T]
  exact Real.log_le_log (Real.exp_pos _) h1

/-- **The error term of `reduction_upper_unitIntegral` is below `e^{-(c/3)L²}`** at the Harper
cutoff.  The chain is `ℓ ≤ u/L² ⇒ u/ℓ ≥ L²`, then `q ≥ 2/3` on the exponential and `q ≤ 1` on the
power, leaving `log C + KL ≤ (c/3)L²` — which is what the threshold `L ≥ 3(|log C|+K)/c` buys. -/
lemma harper_error_bound {x C K c q ℓ : ℝ} (hC : 0 < C) (hK : 0 ≤ K) (hc : 0 < c)
    (hx : Real.exp (Real.exp 36) ≤ x)
    (hthr : 3 * (|Real.log C| + K) / c ≤ Real.log (Real.log x))
    (hq0 : 2 / 3 ≤ q) (hq1 : q ≤ 1)
    (hℓ0 : 0 < ℓ) (hℓY : ℓ ≤ Real.log (harperCutoff x)) :
    C * (ℓ ^ K * Real.exp (-c * Real.log x / ℓ)) ^ q
      ≤ Real.exp (-(c / 3 * Real.log (Real.log x) ^ 2)) := by
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx
  have hu0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hu36
  have hL0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  have hu1 : (1 : ℝ) ≤ Real.log x := by
    have h := Real.add_one_le_exp (36 : ℝ)
    linarith
  have hq0' : (0 : ℝ) < q := by linarith
  have hlogY : Real.log (harperCutoff x) = Real.log x / Real.log (Real.log x) ^ 2 :=
    log_harperCutoff x
  have hLsq : (1 : ℝ) ≤ Real.log (Real.log x) ^ 2 := by nlinarith
  -- `ℓ L² ≤ u`, hence both the exponent and the base bounds
  have hkey : ℓ * Real.log (Real.log x) ^ 2 ≤ Real.log x := by
    have h := hℓY
    rw [hlogY] at h
    calc ℓ * Real.log (Real.log x) ^ 2
        ≤ (Real.log x / Real.log (Real.log x) ^ 2) * Real.log (Real.log x) ^ 2 := by gcongr
      _ = Real.log x := by field_simp
  have hℓu : ℓ ≤ Real.log x := by nlinarith
  have hexp : -c * Real.log x / ℓ ≤ -(c * Real.log (Real.log x) ^ 2) := by
    rw [div_le_iff₀ hℓ0]
    nlinarith [hkey, hc.le]
  -- the bracket
  have hbrk0 : (0 : ℝ) ≤ ℓ ^ K * Real.exp (-c * Real.log x / ℓ) := by positivity
  have hbrk : ℓ ^ K * Real.exp (-c * Real.log x / ℓ)
      ≤ Real.log x ^ K * Real.exp (-(c * Real.log (Real.log x) ^ 2)) :=
    mul_le_mul (Real.rpow_le_rpow hℓ0.le hℓu hK) (Real.exp_le_exp.2 hexp)
      (Real.exp_pos _).le (by positivity)
  -- take `q`-th powers and expand
  have hexpand : (Real.log x ^ K * Real.exp (-(c * Real.log (Real.log x) ^ 2))) ^ q
      = Real.log x ^ (K * q) * Real.exp (-(c * Real.log (Real.log x) ^ 2) * q) := by
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.rpow_mul hu0.le]
    congr 1
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hpow : Real.log x ^ (K * q) ≤ Real.log x ^ K :=
    Real.rpow_le_rpow_of_exponent_le hu1
      (by nlinarith [mul_nonneg hK (by linarith : (0 : ℝ) ≤ 1 - q)])
  have hE : Real.exp (-(c * Real.log (Real.log x) ^ 2) * q)
      ≤ Real.exp (-(2 * c / 3 * Real.log (Real.log x) ^ 2)) :=
    Real.exp_le_exp.2 (by
      nlinarith [mul_nonneg (mul_nonneg hc.le
        (sq_nonneg (Real.log (Real.log x)))) (by linarith : (0 : ℝ) ≤ q - 2 / 3)])
  -- the final numeric step
  have hfin : C * (Real.log x ^ K * Real.exp (-(2 * c / 3 * Real.log (Real.log x) ^ 2)))
      ≤ Real.exp (-(c / 3 * Real.log (Real.log x) ^ 2)) := by
    have hu_pow : Real.log x ^ K = Real.exp (Real.log (Real.log x) * K) :=
      Real.rpow_def_of_pos hu0 K
    have hC_exp : C = Real.exp (Real.log C) := (Real.exp_log hC).symm
    rw [hu_pow, hC_exp, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h2 : |Real.log C| + K ≤ c / 3 * Real.log (Real.log x) := by
      rw [div_le_iff₀ hc] at hthr
      linarith
    have h3 : Real.log C ≤ |Real.log C| := le_abs_self _
    have h4 := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ Real.log (Real.log x))
    nlinarith [h4, h3, abs_nonneg (Real.log C), hK, hL36]
  -- assemble
  have hstep : C * (ℓ ^ K * Real.exp (-c * Real.log x / ℓ)) ^ q
      ≤ C * (Real.log x ^ K * Real.exp (-(2 * c / 3 * Real.log (Real.log x) ^ 2))) := by
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    refine le_trans (Real.rpow_le_rpow hbrk0 hbrk hq0'.le) ?_
    rw [hexpand]
    exact mul_le_mul hpow hE (Real.exp_pos _).le (Real.rpow_nonneg hu0.le K)
  linarith

/-- **The moment is dominated by the Euler-product moment**, at `y = harperCutoff x`: for
`q ∈ [2/3,1]` and `x ≥ x₀`,
`E|S_x|^{2q} ≤ C E[((1/log y)∫_0^1|F_y(1/2+ih)|²dh)^q] + e^{-c(log log x)²}`.
This is `RMF.reduction_upper_unitIntegral` at `log y = log x/(log log x)²`, where its hypotheses
hold for large `x` (`RMF.harperCutoff_sieve`, `RMF.le_floor_harperCutoff`).  The error term is below
every power of `log log x`, so it is stronger than an `o((log log x)^{-q/2})` term. -/
theorem harper_upper_le_euler :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ x₀ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ C * ∫ ω, chaosUnit f (harperCutoff x) ω ^ q ∂μ
              + Real.exp (-(c * Real.log (Real.log x) ^ 2)) := by
  obtain ⟨C, K, c, y₀, hC, hK, hc, hy₀, hred⟩ := reduction_upper_unitIntegral (Ω := Ω)
  refine ⟨2 * C, c / 3, by linarith, by linarith,
    Real.exp (Real.exp (max 36 (max (Real.log ((y₀ : ℝ) + 1))
      (3 * (|Real.log C| + K) / c)))), ?_⟩
  intro f μ hf x q hx hq0 hq1
  obtain ⟨hx36, hLT⟩ := harper_regime_of (le_max_left _ _) hx
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx36
  -- the two thresholds, read off the `max`
  have hm : Real.log ((y₀ : ℝ) + 1) ≤ Real.log (Real.log x) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLT
  have hthr : 3 * (|Real.log C| + K) / c ≤ Real.log (Real.log x) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLT
  -- the cutoff is large
  have hexp36 : (37 : ℝ) ≤ Real.exp 36 := by
    have := Real.add_one_le_exp (36 : ℝ); linarith
  have hY36 : Real.exp 36 ≤ harperCutoff x := exp_le_harperCutoff hx36
  have hY4 : (4 : ℝ) ≤ harperCutoff x := by linarith
  have hY2 : (2 : ℝ) ≤ harperCutoff x := by linarith
  have hfl2 : (2 : ℝ) ≤ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := by
    have h : (2 : ℕ) ≤ ⌊harperCutoff x⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast h
  have hkey := hred f μ hf x ⌊harperCutoff x⌋₊ q
    (le_floor_harperCutoff hx36 hm) (harperCutoff_sieve hx36) hq0 hq1
  refine le_trans hkey ?_
  -- the main term: rounding the cutoff down costs a factor `2`, and `2^q ≤ 2`
  have hmain : ∫ ω, chaosUnit f ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) ω ^ q ∂μ
      ≤ 2 * ∫ ω, chaosUnit f (harperCutoff x) ω ^ q ∂μ := by
    have hint : Integrable (fun ω => chaosUnit f (harperCutoff x) ω ^ q) μ :=
      integrable_chaosUnit_rpow hf hY2 (by linarith)
    have hle : ∀ ω, chaosUnit f ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) ω ^ q
        ≤ 2 * chaosUnit f (harperCutoff x) ω ^ q := by
      intro ω
      have hnn : 0 ≤ chaosUnit f (harperCutoff x) ω := chaosUnit_nonneg hY2 ω
      calc chaosUnit f ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) ω ^ q
          ≤ (2 * chaosUnit f (harperCutoff x) ω) ^ q :=
            Real.rpow_le_rpow (chaosUnit_nonneg hfl2 ω)
              (chaosUnit_floor_le hY4 ω) (by linarith)
        _ = 2 ^ q * chaosUnit f (harperCutoff x) ω ^ q :=
            Real.mul_rpow (by norm_num) hnn
        _ ≤ 2 * chaosUnit f (harperCutoff x) ω ^ q := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hnn q)
            calc (2 : ℝ) ^ q ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hq1
              _ = 2 := Real.rpow_one 2
    have h2 := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun ω =>
        Real.rpow_nonneg (chaosUnit_nonneg hfl2 ω) q)
      (hint.const_mul 2) (Filter.Eventually.of_forall hle)
    rwa [integral_const_mul] at h2
  have h1 : C * ∫ ω, chaosUnit f ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) ω ^ q ∂μ
      ≤ 2 * C * ∫ ω, chaosUnit f (harperCutoff x) ω ^ q ∂μ := by
    calc C * ∫ ω, chaosUnit f ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) ω ^ q ∂μ
        ≤ C * (2 * ∫ ω, chaosUnit f (harperCutoff x) ω ^ q ∂μ) :=
          mul_le_mul_of_nonneg_left hmain hC.le
      _ = 2 * C * ∫ ω, chaosUnit f (harperCutoff x) ω ^ q ∂μ := by ring
  -- the error term
  have herr := harper_error_bound (x := x) (C := C) (K := K) (c := c) (q := q)
    (ℓ := Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)) hC hK hc hx36 hthr hq0 hq1
    (Real.log_pos (by linarith))
    (Real.log_le_log (by linarith) (Nat.floor_le (by linarith)))
  linarith

/-- **The double log of the cutoff is `L - 2 log L`.**  This is the shift that has to be absorbed
into the constant when the Euler-product bound, stated at `y`, is transported to `x`. -/
lemma loglog_harperCutoff {x : ℝ} (hx : Real.exp (Real.exp 36) ≤ x) :
    Real.log (Real.log (harperCutoff x))
      = Real.log (Real.log x) - 2 * Real.log (Real.log (Real.log x)) := by
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx
  have hu0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hu36
  have hL0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  rw [log_harperCutoff, Real.log_div (ne_of_gt hu0) (by positivity), Real.log_pow]
  push_cast
  ring

/-- The shift costs at most a factor `4`: `L - 2 log L ≥ L/4` once `L ≥ 36`. -/
lemma loglog_harperCutoff_ge {x : ℝ} (hx : Real.exp (Real.exp 36) ≤ x) :
    Real.log (Real.log x) / 4 ≤ Real.log (Real.log (harperCutoff x)) := by
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx
  have hL0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  rw [loglog_harperCutoff hx]
  have h1 : Real.log (Real.log (Real.log x)) ≤ 2 * Real.sqrt (Real.log (Real.log x)) :=
    log_le_two_sqrt hL0
  have hs2 : Real.sqrt (Real.log (Real.log x)) ^ 2 = Real.log (Real.log x) :=
    Real.sq_sqrt hL0.le
  have hs6 : (6 : ℝ) ≤ Real.sqrt (Real.log (Real.log x)) := by
    rw [show (6 : ℝ) = Real.sqrt 36 by
      rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hL36
  nlinarith [h1, hs2, hs6, Real.sqrt_nonneg (Real.log (Real.log x))]

/-- **The target at the cutoff dominates the target at `x`, up to a factor `2`.**  This is where
`log log y = log log x - 2 log log log x` is absorbed: `√` turns the factor `4` into a factor
`2`, and `q ≤ 1` keeps `2^q ≤ 2`. -/
lemma rpow_neg_loglog_harperCutoff_le {x q : ℝ} (hx : Real.exp (Real.exp 36) ≤ x)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 + (1 - q) * Real.sqrt (Real.log (Real.log (harperCutoff x)))) ^ (-q)
      ≤ 2 * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx
  have hL0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  have ht : (0 : ℝ) ≤ 1 - q := by linarith
  have hM : Real.sqrt (Real.log (Real.log x)) / 2
      ≤ Real.sqrt (Real.log (Real.log (harperCutoff x))) := by
    have h := Real.sqrt_le_sqrt (loglog_harperCutoff_ge hx)
    rwa [Real.sqrt_div hL0.le, show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hA0 : (0 : ℝ) < 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) := by
    have := mul_nonneg ht (Real.sqrt_nonneg (Real.log (Real.log x)))
    linarith
  have hB0 : (0 : ℝ) < 1 + (1 - q) * Real.sqrt (Real.log (Real.log (harperCutoff x))) := by
    have := mul_nonneg ht (Real.sqrt_nonneg (Real.log (Real.log (harperCutoff x))))
    linarith
  have hAB : 1 + (1 - q) * Real.sqrt (Real.log (Real.log x))
      ≤ 2 * (1 + (1 - q) * Real.sqrt (Real.log (Real.log (harperCutoff x)))) := by
    have := mul_le_mul_of_nonneg_left hM ht
    linarith
  have hstep : (2 : ℝ) ^ (-q)
      * (1 + (1 - q) * Real.sqrt (Real.log (Real.log (harperCutoff x)))) ^ (-q)
      ≤ (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
    rw [← Real.mul_rpow (by norm_num) hB0.le]
    exact Real.rpow_le_rpow_of_nonpos hA0 hAB (by linarith)
  have h2q : (2 : ℝ)⁻¹ ≤ (2 : ℝ) ^ (-q) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : (-1 : ℝ) ≤ -q)
    rwa [Real.rpow_neg (by norm_num), Real.rpow_one] at h
  have hBq : (0 : ℝ)
      < (1 + (1 - q) * Real.sqrt (Real.log (Real.log (harperCutoff x)))) ^ (-q) :=
    Real.rpow_pos_of_pos hB0 _
  nlinarith [hstep, mul_nonneg (by linarith : (0 : ℝ) ≤ (2 : ℝ) ^ (-q) - 2⁻¹) hBq.le]

/-- **The additive error is below the target.**  `e^{-cL²} ≤ 1/L ≤ (1+(1-q)√L)^{-q}`: the target
is only a power of `L`, and `1 + (1-q)√L ≤ L` because `1-q ≤ 1/3` and `√L ≤ L/6`. -/
lemma harper_error_le_target {x c q : ℝ} (hc : 0 < c) (hx : Real.exp (Real.exp 36) ≤ x)
    (hthr : 1 / c ≤ Real.log (Real.log x)) (hq0 : 2 / 3 ≤ q) (hq1 : q ≤ 1) :
    Real.exp (-(c * Real.log (Real.log x) ^ 2))
      ≤ (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx
  have hL0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log (Real.log x)) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (Real.log (Real.log x)) ^ 2 = Real.log (Real.log x) :=
    Real.sq_sqrt hL0.le
  have hs6 : (6 : ℝ) ≤ Real.sqrt (Real.log (Real.log x)) := by
    rw [show (6 : ℝ) = Real.sqrt 36 by
      rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hL36
  have hA0 : (0 : ℝ) < 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - q) hs0
    linarith
  have hAL : 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) ≤ Real.log (Real.log x) := by
    nlinarith [hs2, hs6, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 3 - (1 - q)) hs0,
      mul_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt (Real.log (Real.log x)) - 6) hs0]
  have hstep1 : Real.log (Real.log x) ^ (-q)
      ≤ (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) :=
    Real.rpow_le_rpow_of_nonpos hA0 hAL (by linarith)
  have hstep2 : Real.log (Real.log x) ^ (-(1 : ℝ)) ≤ Real.log (Real.log x) ^ (-q) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hinv : Real.log (Real.log x) ^ (-(1 : ℝ)) = (Real.log (Real.log x))⁻¹ := by
    rw [Real.rpow_neg hL0.le, Real.rpow_one]
  have hexp : Real.exp (-(c * Real.log (Real.log x) ^ 2))
      ≤ (Real.log (Real.log x))⁻¹ := by
    rw [Real.exp_neg]
    refine inv_anti₀ hL0 ?_
    have h1 : (1 : ℝ) ≤ c * Real.log (Real.log x) := by
      rw [div_le_iff₀ hc] at hthr
      linarith
    have h2 := Real.add_one_le_exp (c * Real.log (Real.log x) ^ 2)
    nlinarith [h1, h2, mul_nonneg (by linarith : (0 : ℝ) ≤ c * Real.log (Real.log x) - 1)
      hL0.le]
  linarith [hstep1, hstep2, hinv, hexp]

/-! ### The Euler-product moment

The last input of the upper bound (Hamdan's Proposition 1.2), from the chaos estimate
`RMF.exists_const_integral_chaosUnit_rpow_le`. -/

/-- **The Euler-product moment** (Hamdan's Proposition 1.2): for `y ≥ y₀` and `q ∈ [0,1]`,
`E[((1/log y)∫_0^1|F_y(1/2+ih)|²dh)^q] ≤ C' (1+(1-q)√(log log y))^{-q}`, with `C'`, `y₀`
independent of `f`, `μ`, `y` and `q`.

This is `RMF.exists_const_integral_chaosUnit_rpow_le` with the block count
`t = RMF.harperBlockCount D y ≤ log log y` traded for `log log y`.  The trade goes the wrong way
and costs a factor `2`: past `log log y ≥ 2(D+1)`, `t ≥ ½ log log y`, so
`(1+(1-q)√t)^{-q} ≤ 2(1+(1-q)√(log log y))^{-q}` (`RMF.rpow_neg_target_le_of_quarter_le`).
Hence `y₀ = max{x₀, e^{e^{2(D+1)}}}`: at small `y` the block count is `0` and the chaos bound
degenerates to the trivial one. -/
theorem euler_unitIntegral_moment_le :
    ∃ C' y₀ : ℝ, 0 < C' ∧
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ y q : ℝ, y₀ ≤ y → 0 ≤ q → q ≤ 1 →
          ∫ ω, chaosUnit f y ω ^ q ∂μ
            ≤ C' * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q) := by
  obtain ⟨D, x₀, C, hC, H⟩ := exists_const_integral_chaosUnit_rpow_le (Ω := Ω)
  refine ⟨2 * C, max x₀ (Real.exp (Real.exp (2 * ((D : ℝ) + 1)))), by linarith, ?_⟩
  intro f μ hf y q hy hq0 hq1
  obtain ⟨Y, hY, rfl⟩ := hf.exists_primeValues
  have hxx₀ : x₀ ≤ y := le_trans (le_max_left _ _) hy
  have hexp : Real.exp (Real.exp (2 * ((D : ℝ) + 1))) ≤ y := le_trans (le_max_right _ _) hy
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (Real.exp_pos _) hexp
  have hlogy : Real.exp (2 * ((D : ℝ) + 1)) ≤ Real.log y := (Real.le_log_iff_exp_le hy0).2 hexp
  have hlogy0 : (0 : ℝ) < Real.log y := lt_of_lt_of_le (Real.exp_pos _) hlogy
  have hL : 2 * ((D : ℝ) + 1) ≤ Real.log (Real.log y) :=
    (Real.le_log_iff_exp_le hlogy0).2 hlogy
  have hD : (D : ℝ) ≤ Real.log (Real.log y) := by linarith
  -- the block count is at least half of `log log y`
  have ht : Real.log (Real.log y) / 2 ≤ (harperBlockCount D y : ℝ) := by
    rw [cast_harperBlockCount hD]
    have hfl : Real.log (Real.log y) < (⌊Real.log (Real.log y)⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    linarith
  have ht0 : (0 : ℝ) ≤ (harperBlockCount D y : ℝ) := Nat.cast_nonneg _
  -- the two targets differ by a factor two
  have htar := rpow_neg_target_le_of_quarter_le
    (t := (harperBlockCount D y : ℝ)) (Λ := Real.log (Real.log y)) (by linarith) hq0 hq1
  calc ∫ ω, chaosUnit (fun ω => compMultExtension fun p => Y p ω) y ω ^ q ∂μ
      ≤ C * (1 + (1 - q) * Real.sqrt (harperBlockCount D y : ℝ)) ^ (-q) :=
        H Y μ hY y q hxx₀ hq0 hq1
    _ ≤ C * (2 * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q)) :=
        mul_le_mul_of_nonneg_left htar hC.le
    _ = 2 * C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q) := by ring

/-- **Harper's upper bound** on `[2/3,1]` (the upper half of Harper's Theorem 1, restricted to
`[2/3,1]`): for `q ∈ [2/3,1]` and `x ≥ x₀`, `E|S_x|^{2q} ≤ C (1+(1-q)√(log log x))^{-q}`, with `C`,
`x₀` independent of `f`, `μ`, `x` and `q`.  `RMF.harper_upper_full` extends it to `[0,1]`.

It combines `RMF.harper_upper_le_euler` with `RMF.euler_unitIntegral_moment_le`.  Two things are
checked in the deduction.  The cutoff enters the right-hand side as `log log y`, and
`log log y = log log x - 2 log log log x`; that shift is absorbed into the constant.  And the
additive error of `RMF.harper_upper_le_euler` is `≪ (1+(1-q)√(log log x))^{-q}`, because it is
below every power of `log log x` while the target is only a power.

The threshold is a `max` of `RMF.harper_upper_le_euler`'s own `x₁`, the regime bound
`exp(exp(max 36 (1/c₁)))` that `RMF.harper_error_le_target` needs, and `exp y₀`, which delivers
`y₀ ≤ harperCutoff x` through `RMF.log_le_harperCutoff`. -/
theorem harper_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  obtain ⟨C', y₀, hC'0, hEu⟩ := euler_unitIntegral_moment_le (Ω := Ω)
  obtain ⟨C₁, c₁, hC₁, hc₁, x₁, hup⟩ := harper_upper_le_euler (Ω := Ω)
  refine ⟨2 * C₁ * C' + 1, by positivity,
    max (max x₁ (Real.exp (Real.exp (max 36 (1 / c₁))))) (Real.exp y₀), ?_⟩
  intro f μ hf x q hx hq0 hq1
  have hxa : max x₁ (Real.exp (Real.exp (max 36 (1 / c₁)))) ≤ x := le_trans (le_max_left _ _) hx
  have hxb : Real.exp y₀ ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hx36, hLT⟩ := harper_regime_of (le_max_left _ _) (le_trans (le_max_right _ _) hxa)
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx36
  have hthr : 1 / c₁ ≤ Real.log (Real.log x) := le_trans (le_max_right _ _) hLT
  have hY : y₀ ≤ harperCutoff x :=
    le_trans ((Real.le_log_iff_exp_le hx0).2 hxb) (log_le_harperCutoff hx36)
  have h1 := hup f μ hf x q (le_trans (le_max_left _ _) hxa) hq0 hq1
  have h2 := hEu f μ hf (harperCutoff x) q hY (by linarith) hq1
  have h3 := rpow_neg_loglog_harperCutoff_le hx36 (by linarith : (0 : ℝ) ≤ q) hq1
  have h4 := harper_error_le_target hc₁ hx36 hthr hq0 hq1
  have hI : C₁ * ∫ ω, chaosUnit f (harperCutoff x) ω ^ q ∂μ
      ≤ 2 * C₁ * C' * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
    calc C₁ * ∫ ω, chaosUnit f (harperCutoff x) ω ^ q ∂μ
        ≤ C₁ * (C' * (1 + (1 - q)
            * Real.sqrt (Real.log (Real.log (harperCutoff x)))) ^ (-q)) :=
          mul_le_mul_of_nonneg_left h2 hC₁.le
      _ ≤ C₁ * (C' * (2 * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hC'0.le) hC₁.le
      _ = 2 * C₁ * C' * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by ring
  have hgoal : (2 * C₁ * C' + 1)
        * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
      = 2 * C₁ * C' * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
        + (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by ring
  rw [hgoal]
  linarith [h1, hI, h4]

/-! ### The rest of the `q`-range

`RMF.harper_upper` proves the upper bound on `[2/3,1]`, which is where all the work is: "it will
suffice to prove Theorems 1 and 2 for `2/3 ≤ q ≤ 1`" (Harper, *Moments of random multiplicative
functions, I*, arXiv:1703.06654).  The descent to `q = 0` is
`RMF.integral_rpow_le_rpow_integral_of_le_two_thirds`, whose one hypothesis is that `S_x ∈ L^{4/3}`
— immediate here, because a Steinhaus partial sum is `⌊x⌋₊` unimodular terms and hence bounded.

The target moves as well, and that is the only thing to check.  The descent delivers
`(1 + \tfrac13\sqrt L)^{-q}`, where the statement asks for `(1 + (1-q)\sqrt L)^{-q}`; the two
differ by at most `3^q ≤ 3`, since `1/3 ≤ 1 - q ≤ 1` throughout the range in play. -/

/-- **The descent, as arithmetic.**  Everything in the passage from `q = 2/3` to a smaller `q` that
does not mention the random multiplicative function.

`I₄₃` is `E|S|^{4/3}` and `Iq` is `E|S|^{2q}`; `hdesc` is Hölder and `h43` is the bound at
`q = 2/3`.  The constant `3 · max 1 C` has the two sources named in the section docstring: `max 1 C`
because `C^{3q/2} ≤ max 1 C` for `3q/2 ∈ [0,1]`, and `3` for the shift in the target. -/
lemma le_target_of_two_thirds {I₄₃ Iq C t q : ℝ} (hC0 : 0 < C) (ht0 : 0 ≤ t)
    (hq0 : 0 ≤ q) (hq23 : q ≤ 2 / 3) (hI0 : 0 ≤ I₄₃)
    (hdesc : Iq ≤ I₄₃ ^ (3 * q / 2))
    (h43 : I₄₃ ≤ C * (1 + (1 - 2 / 3) * t) ^ (-(2 / 3) : ℝ)) :
    Iq ≤ 3 * max 1 C * (1 + (1 - q) * t) ^ (-q) := by
  have hA0 : (0 : ℝ) < 1 + (1 - 2 / 3) * t := by linarith
  have hT0 : (0 : ℝ) < 1 + (1 - q) * t := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - q by linarith) ht0]
  have hApow : (0 : ℝ) ≤ (1 + (1 - 2 / 3) * t) ^ (-q) := Real.rpow_nonneg hA0.le _
  have hTpow : (0 : ℝ) ≤ (1 + (1 - q) * t) ^ (-q) := Real.rpow_nonneg hT0.le _
  have hstep : I₄₃ ^ (3 * q / 2)
      ≤ (C * (1 + (1 - 2 / 3) * t) ^ (-(2 / 3) : ℝ)) ^ (3 * q / 2) :=
    Real.rpow_le_rpow hI0 h43 (by linarith)
  have hsplit : (C * (1 + (1 - 2 / 3) * t) ^ (-(2 / 3) : ℝ)) ^ (3 * q / 2)
      = C ^ (3 * q / 2) * (1 + (1 - 2 / 3) * t) ^ (-q) := by
    rw [Real.mul_rpow hC0.le (Real.rpow_nonneg hA0.le _), ← Real.rpow_mul hA0.le]
    congr 2
    ring
  have hCq : C ^ (3 * q / 2) ≤ max 1 C := by
    rcases le_or_gt C 1 with h | h
    · exact le_trans (Real.rpow_le_one hC0.le h (by linarith)) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have hle := Real.rpow_le_rpow_of_exponent_le h.le (show 3 * q / 2 ≤ 1 by linarith)
      rwa [Real.rpow_one] at hle
  have hAT : (1 + (1 - 2 / 3) * t) ^ (-q) ≤ 3 * (1 + (1 - q) * t) ^ (-q) := by
    have hTA : 1 + (1 - q) * t ≤ 3 * (1 + (1 - 2 / 3) * t) := by
      nlinarith [mul_nonneg hq0 ht0]
    have h1 : (3 * (1 + (1 - 2 / 3) * t)) ^ (-q) ≤ (1 + (1 - q) * t) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos hT0 hTA (by linarith)
    rw [Real.mul_rpow (by norm_num) hA0.le] at h1
    have hpos : (0 : ℝ) < (3 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) q
    have hmul := mul_le_mul_of_nonneg_left h1 hpos.le
    rw [← mul_assoc, ← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero,
      one_mul] at hmul
    have h3 : (3 : ℝ) ^ q ≤ 3 := by
      have hle := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 3 by norm_num)
        (show q ≤ 1 by linarith)
      rwa [Real.rpow_one] at hle
    exact le_trans hmul (mul_le_mul_of_nonneg_right h3 hTpow)
  calc Iq ≤ I₄₃ ^ (3 * q / 2) := hdesc
    _ ≤ C ^ (3 * q / 2) * (1 + (1 - 2 / 3) * t) ^ (-q) := by rw [← hsplit]; exact hstep
    _ ≤ max 1 C * (3 * (1 + (1 - q) * t) ^ (-q)) :=
        mul_le_mul hCq hAT hApow (le_trans zero_le_one (le_max_left _ _))
    _ = 3 * max 1 C * (1 + (1 - q) * t) ^ (-q) := by ring

/-- The normalised partial sum is measurable: a finite sum of measurable values, divided by a
constant. -/
lemma IsSteinhausRMF.measurable_normalisedSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) (x : ℝ) : Measurable (normalisedSum f x) :=
  (Finset.measurable_sum _ fun n _ => hf.measurable_apply n).div_const _

/-- **The normalised partial sum is bounded**, almost surely, by `⌊x⌋₊/√x`: it is `⌊x⌋₊` unimodular
terms over `√x`. -/
lemma IsSteinhausRMF.ae_norm_normalisedSum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) (x : ℝ) :
    ∀ᵐ ω ∂μ, ‖normalisedSum f x ω‖ ≤ (⌊x⌋₊ : ℝ) / Real.sqrt x := by
  have hall : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ = 1 := fun n hn =>
    hf.norm_apply (by have := (Finset.mem_Icc.1 hn).1; omega)
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
  have hnum : ‖randomSum f x ω‖ ≤ (⌊x⌋₊ : ℝ) := by
    rw [randomSum]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ => (1 : ℝ))
      fun n hn => le_of_eq (hω n hn)) ?_
    simp
  rw [normalisedSum, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg x)]
  exact div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg x)

/-- **The normalised partial sum is in `L^{4/3}`** (it is bounded), the exponent
`RMF.integral_rpow_le_rpow_integral_of_le_two_thirds` asks for. -/
lemma IsSteinhausRMF.memLp_normalisedSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) (x : ℝ) :
    MemLp (normalisedSum f x) (ENNReal.ofReal (4 / 3)) μ := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  exact (memLp_top_of_bound (hf.measurable_normalisedSum x).aestronglyMeasurable _
    (hf.ae_norm_normalisedSum_le x)).mono_exponent le_top

/-- **Harper's upper bound, on all of `[0,1]`.**  `E|S_x|^{2q} ≪ (1+(1-q)√(log log x))^{-q}` for
every `q ∈ [0,1]` and every `x` past the same threshold as `RMF.harper_upper`, with constant
`3 · max 1 C` for `RMF.harper_upper`'s `C`. -/
theorem harper_upper_full :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ x q : ℝ, x₀ ≤ x → 0 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  obtain ⟨C, hC0, x₀, hup⟩ := harper_upper (Ω := Ω)
  refine ⟨3 * max 1 C, by positivity, x₀, ?_⟩
  intro f μ hf x q hx hq0 hq1
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have ht0 : (0 : ℝ) ≤ Real.sqrt (Real.log (Real.log x)) := Real.sqrt_nonneg _
  have hC1 : (1 : ℝ) ≤ max 1 C := le_max_left _ _
  have hC2 : C ≤ max 1 C := le_max_right _ _
  rcases le_or_gt (2 / 3 : ℝ) q with hq23 | hq23
  · have hT0 : (0 : ℝ) ≤ 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - q by linarith) ht0]
    refine le_trans (hup f μ hf x q hx hq23 hq1)
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hT0 _))
  refine le_target_of_two_thirds hC0 ht0 hq0 hq23.le
    (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _)
    (integral_rpow_le_rpow_integral_of_le_two_thirds hq0 hq23.le
      (hf.memLp_normalisedSum x)) ?_
  rw [show (4 / 3 : ℝ) = 2 * (2 / 3) by norm_num]
  exact hup f μ hf x (2 / 3) hx le_rfl (by norm_num)

/-! ### Down to `x = 3`

`RMF.harper_upper_full` is asymptotic: its threshold `x₀` is existentially quantified.
`RMF.harper_low_moments` is stated at `3 ≤ x`, so the two do not meet until the bounded range
`[3, x₀]` is covered as well.

There is nothing in that range.  A Steinhaus partial sum is `⌊x⌋₊` unimodular terms, so
`‖S_x‖ ≤ √x`, and on a bounded range that is a constant; the target is bounded below there because
`\log\log 3 > 0`.  Enlarging `C` absorbs both.  This is the only step of the upper bound that is
not asymptotic. -/

/-- **The moment is bounded on a bounded range.**  For `3 ≤ x ≤ X`, `E|S_x|^{2q} ≤ \max\{1, X\}`,
uniformly in `q ∈ [0,1]`.

`‖S_x‖ ≤ ⌊x⌋₊/√x ≤ √x ≤ √X`, and `(√X)^{2q} = X^q ≤ \max\{1, X\}` by
`RMF.rpow_le_max_one`. -/
lemma IsSteinhausRMF.integral_norm_normalisedSum_rpow_le_of_le
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ)
    {x X q : ℝ} (hx : 3 ≤ x) (hxX : x ≤ X) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) ≤ max 1 X := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨Y, hY, rfl⟩ := hf.exists_primeValues
    exact hY.isProbabilityMeasure
  have hX0 : (0 : ℝ) < X := by linarith
  have hsX0 : (0 : ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg _
  -- the pointwise bound, on the bounded range
  have hb : ∀ᵐ ω ∂μ, ‖normalisedSum f x ω‖ ≤ Real.sqrt X := by
    filter_upwards [hf.ae_norm_normalisedSum_le x] with ω hω
    refine le_trans hω ?_
    calc ((⌊x⌋₊ : ℕ) : ℝ) / Real.sqrt x ≤ x / Real.sqrt x :=
          div_le_div_of_nonneg_right (Nat.floor_le (by linarith)) (Real.sqrt_nonneg x)
      _ = Real.sqrt x := Real.div_sqrt
      _ ≤ Real.sqrt X := Real.sqrt_le_sqrt hxX
  -- and its `2q`-th power, which is what makes the integrand integrable
  have hbq : ∀ᵐ ω ∂μ, ‖‖normalisedSum f x ω‖ ^ (2 * q)‖ ≤ Real.sqrt X ^ (2 * q) := by
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) hω (by linarith)
  have hint : Integrable (fun ω => ‖normalisedSum f x ω‖ ^ (2 * q)) μ :=
    (memLp_top_of_bound
      (((hf.measurable_normalisedSum x).norm.pow_const (2 * q)).aestronglyMeasurable) _
      hbq).integrable le_top
  -- `(√X)^{2q} = X^q`
  have hpow : Real.sqrt X ^ (2 * q) = X ^ q := by
    rw [Real.rpow_mul hsX0]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt hX0.le]
  calc (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ)
      ≤ ∫ _ : Ω, Real.sqrt X ^ (2 * q) ∂μ := by
        refine integral_mono_ae hint (integrable_const _) ?_
        filter_upwards [hb] with ω hω
        exact Real.rpow_le_rpow (norm_nonneg _) hω (by linarith)
    _ = Real.sqrt X ^ (2 * q) := by simp
    _ = X ^ q := hpow
    _ ≤ max 1 X := rpow_le_max_one hX0 hq0 hq1

/-- **Harper's upper bound down to `x = 3`, at a general law predicate `P`**: the asymptotic bound
`Hfull` and the crude bound `Hbdd` on `3 ≤ x ≤ X` give the bound for all `x ≥ 3`.  The
threshold-lowering is four inequalities about `log log` and one bounded-range estimate, none of
which looks at the law; both models are instances. -/
theorem harper_upper_ge_three_of_full
    {P : (Ω → ArithmeticFunction ℂ) → Measure Ω → Prop}
    (Hfull : ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ →
        ∀ x q : ℝ, x₀ ≤ x → 0 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q))
    (Hbdd : ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ →
      ∀ x X q : ℝ, 3 ≤ x → x ≤ X → 0 ≤ q → q ≤ 1 →
        (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) ≤ max 1 X) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ →
        ∀ x q : ℝ, 3 ≤ x → 0 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  obtain ⟨C₀, hC₀, x₀, H⟩ := Hfull
  refine ⟨max C₀ (max 1 (max x₀ 3)
      * (1 + Real.sqrt (Real.log (Real.log (max x₀ 3))))),
    lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  intro f μ hf x q hx hq0 hq1
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log (Real.log x)) := Real.sqrt_nonneg _
  have hT0 : (0 : ℝ) < 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - q by linarith) hs0]
  rcases le_or_gt (max x₀ 3) x with hXx | hxX
  · -- the asymptotic range
    refine le_trans (H f μ hf x q (le_trans (le_max_left _ _) hXx) hq0 hq1) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hT0.le _)
  -- the bounded range `3 ≤ x ≤ max x₀ 3`
  have hX3 : (3 : ℝ) ≤ max x₀ 3 := le_max_right _ _
  have hsX0 : (0 : ℝ) ≤ Real.sqrt (Real.log (Real.log (max x₀ 3))) := Real.sqrt_nonneg _
  have hB1 : (1 : ℝ) ≤ 1 + Real.sqrt (Real.log (Real.log (max x₀ 3))) := by linarith
  have hLmono : Real.log (Real.log x) ≤ Real.log (Real.log (max x₀ 3)) :=
    Real.log_le_log (Real.log_pos (by linarith))
      (Real.log_le_log (by linarith) hxX.le)
  have hup : 1 + (1 - q) * Real.sqrt (Real.log (Real.log x))
      ≤ 1 + Real.sqrt (Real.log (Real.log (max x₀ 3))) := by
    have h := mul_le_mul_of_nonneg_right (show 1 - q ≤ 1 by linarith) hs0
    rw [one_mul] at h
    linarith [Real.sqrt_le_sqrt hLmono]
  have hlow : (1 + Real.sqrt (Real.log (Real.log (max x₀ 3))))⁻¹
      ≤ (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
    have h1 : (1 + Real.sqrt (Real.log (Real.log (max x₀ 3)))) ^ (-q)
        ≤ (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos hT0 hup (by linarith)
    have h2 : (1 + Real.sqrt (Real.log (Real.log (max x₀ 3)))) ^ (-(1 : ℝ))
        ≤ (1 + Real.sqrt (Real.log (Real.log (max x₀ 3)))) ^ (-q) :=
      Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
    rw [Real.rpow_neg_one] at h2
    linarith
  calc (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ)
      ≤ max 1 (max x₀ 3) :=
        Hbdd f μ hf x (max x₀ 3) q hx hxX.le hq0 hq1
    _ = (max 1 (max x₀ 3) * (1 + Real.sqrt (Real.log (Real.log (max x₀ 3)))))
          * (1 + Real.sqrt (Real.log (Real.log (max x₀ 3))))⁻¹ := by
        field_simp
    _ ≤ max C₀ (max 1 (max x₀ 3)
            * (1 + Real.sqrt (Real.log (Real.log (max x₀ 3)))))
          * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) :=
        mul_le_mul (le_max_right _ _) hlow (by positivity)
          (le_trans hC₀.le (le_max_left _ _))

/-- **Harper's upper bound, at the threshold the target is stated with**: for every `x ≥ 3` and
every `q ∈ [0,1]`, `E|S_x|^{2q} ≤ C (1 + (1-q)√(log log x))^{-q}`, with `C` independent of `f`,
`μ`, `x` and `q`.  This is the second conjunct of `RMF.harper_low_moments`; the first is
`RMF.exists_le_integral_rpow_normalisedSum_full`.

It is the `P := RMF.IsSteinhausRMF` instance of `RMF.harper_upper_ge_three_of_full`: above
`RMF.harper_upper_full`'s threshold `x₀` it is that theorem; below it, the left side is at most
`max 1 x₀` (`RMF.IsSteinhausRMF.integral_norm_normalisedSum_rpow_le_of_le`) and the right side is
at least `C/(1 + √(log log x₀))`. -/
theorem harper_upper_ge_three :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ x q : ℝ, 3 ≤ x → 0 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) :=
  harper_upper_ge_three_of_full harper_upper_full
    (fun _ _ hf _ _ _ hx hxX hq0 hq1 =>
      hf.integral_norm_normalisedSum_rpow_le_of_le hx hxX hq0 hq1)

end RMF
