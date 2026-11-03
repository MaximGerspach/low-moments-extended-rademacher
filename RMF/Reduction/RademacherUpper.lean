/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.Upper
import RMF.Reduction.WindowBridge

/-!
# Harper's upper bound for the Rademacher function

`RMF.exists_const_harper_upper_window_rademacher` is the analytic content: Harper's Proposition 2
composed with the chaos estimate on a window, landing on
`(1 + (1-q)√(harperBlockCount D₀ y / 4))^{-q}` at any admissible Euler-product cutoff `y`.  This
file turns that into `RMF.harper_upper_ge_three`'s
Rademacher twin, and **everything it does is law-free bookkeeping** — the same three moves the
Steinhaus side makes in `RMF/Reduction/Upper.lean`:

* the cutoff `RMF.harperCutoff`, at `\log y = \log x/(ℓogℓog x)²`, with its sieve condition;
* the target traded from the block count to `ℓogℓog x`;
* the `L^p` packaging of `RMF.normalisedSum`, and the bounded range `3 ≤ x ≤ x₀`.

## Two trades, where the Steinhaus side makes one

The Steinhaus chain trades `√(harperBlockCount D y)` for `√ℓogℓog y` once, in
`RMF.euler_unitIntegral_moment_le`.  Here the count is **quartered**, the price of the windowed
chaos estimate, so the first trade costs a factor `4` rather than `2`, and there is a second:
the reduction takes a *natural* cutoff, so `y = ⌊harperCutoff x⌋₊` and `ℓogℓog ⌊h⌋` has to be
compared with `ℓogℓog h` as well.  Flooring costs at most `\log 2`, which against `ℓogℓog h ≥ 9`
is another factor `9/8`; both are absorbed by `RMF.rpow_neg_target_le_of_sq_le`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The two target trades -/

/-- **The quartered block count still dominates `ℓogℓog x`**, up to `4²`.
`harperBlockCount D x = ⌊Λ⌋ - D` and `ℕ`-division loses at most `3`, so `Λ < D + 4m + 4` with
`m` the quartered count; the threshold `Λ ≥ 8(D+4)` turns that into `Λ < (32/7)m`, comfortably
inside `16m`. -/
private lemma loglog_le_sq_blockCount_div_four {D : ℕ} {x : ℝ}
    (hx : 8 * ((D : ℝ) + 4) ≤ Real.log (Real.log x)) :
    Real.log (Real.log x) ≤ (4 : ℝ) ^ 2 * ((harperBlockCount D x / 4 : ℕ) : ℝ) := by
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  have hD : (D : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hcast : (harperBlockCount D x : ℝ) = (⌊Real.log (Real.log x)⌋₊ : ℝ) - (D : ℝ) :=
    cast_harperBlockCount hD
  have hfl : Real.log (Real.log x) < (⌊Real.log (Real.log x)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hmdiv : harperBlockCount D x ≤ 4 * (harperBlockCount D x / 4) + 3 := by omega
  have hmdivR : (harperBlockCount D x : ℝ)
      ≤ 4 * ((harperBlockCount D x / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast hmdiv
  have hm0 : (0 : ℝ) ≤ ((harperBlockCount D x / 4 : ℕ) : ℝ) := Nat.cast_nonneg _
  norm_num
  linarith

/-- **Flooring the cutoff costs a factor `3²`.**  `⌊h⌋ ≥ h - 1 ≥ h/2` and `\log h ≥ 36`, so
`\log⌊h⌋ ≥ \log h - \log 2 ≥ \log h/2`, and one more application gives
`ℓogℓog⌊h⌋ ≥ ℓogℓog h - 1`.  With `RMF.loglog_harperCutoff_ge`'s `ℓogℓog h ≥ Λ/4` and `Λ ≥ 36`
that is `≥ Λ/9`. -/
private lemma loglog_le_sq_loglog_floor_harperCutoff {x : ℝ}
    (hx : Real.exp (Real.exp 36) ≤ x) :
    Real.log (Real.log x)
      ≤ (3 : ℝ) ^ 2 * Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)) := by
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hY36 : Real.exp 36 ≤ harperCutoff x := exp_le_harperCutoff hx
  have he36 : (37 : ℝ) ≤ Real.exp 36 := by linarith [Real.add_one_le_exp (36 : ℝ)]
  have hY2 : (2 : ℝ) ≤ harperCutoff x := by linarith
  have hfl : harperCutoff x - 1 ≤ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (harperCutoff x)
    linarith
  have hhalf : harperCutoff x / 2 ≤ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := by linarith
  have hlogh : (36 : ℝ) ≤ Real.log (harperCutoff x) :=
    le_trans hL36 (log_harperCutoff_ge hx)
  -- `\log ⌊h⌋ ≥ \log h - \log 2 ≥ \log h / 2`
  have hlogfl : Real.log (harperCutoff x) / 2
      ≤ Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := by
    have h1 : Real.log (harperCutoff x / 2)
        ≤ Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hhalf
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    linarith
  -- and once more, at the second logarithm
  have hll : Real.log (Real.log (harperCutoff x)) - 1
      ≤ Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)) := by
    have h1 : Real.log (Real.log (harperCutoff x) / 2)
        ≤ Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)) :=
      Real.log_le_log (by linarith) hlogfl
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    linarith
  have hLh : Real.log (Real.log x) / 4 ≤ Real.log (Real.log (harperCutoff x)) :=
    loglog_harperCutoff_ge hx
  norm_num
  linarith

/-! ### Harper's upper bound on `[2/3, 1]` -/

/-- **Harper's upper bound for the Rademacher function**, `q ∈ [2/3,1]` and `x` past a threshold,
with constant and threshold independent of `f`, `μ`, `x`, `q` — the twin of `RMF.harper_upper`.

The composite `RMF.exists_const_harper_upper_window_rademacher` is read at
`y = ⌊RMF.harperCutoff x⌋₊`, where `RMF.harperCutoff_sieve` discharges the sieve condition and
`RMF.le_floor_harperCutoff` the two thresholds; the main term is traded down to `ℓogℓog x` by the
two lemmas above, and the additive error is below the target by
`RMF.harper_error_bound` and `RMF.harper_error_le_target`, exactly as on the Steinhaus side. -/
theorem harper_upper_rademacher :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
        ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  obtain ⟨D₀, x₁, C₁, K, c, y₀, hC₁, hK, hc, hy₀, H⟩ :=
    exists_const_harper_upper_window_rademacher (Ω := Ω)
  refine ⟨12 * C₁ + 1, by positivity,
    Real.exp (Real.exp (max 36 (max (3 * (|Real.log C₁| + K) / c)
      (max (Real.log ((y₀ : ℝ) + 1))
        (max (Real.log ((⌈x₁⌉₊ : ℝ) + 1))
        (max (72 * ((D₀ : ℝ) + 4)) (3 / c))))))), ?_⟩
  intro f μ hf x q hx hq0 hq1
  obtain ⟨Y, hY, rfl⟩ := hf.exists_primeValues
  obtain ⟨hx36, hLT⟩ := harper_regime_of (le_max_left _ _) hx
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx36
  -- the four thresholds, read off the `max`
  have hthr : 3 * (|Real.log C₁| + K) / c ≤ Real.log (Real.log x) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLT
  have hmy : Real.log ((y₀ : ℝ) + 1) ≤ Real.log (Real.log x) :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hLT
  have hmx : Real.log ((⌈x₁⌉₊ : ℝ) + 1) ≤ Real.log (Real.log x) :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)) hLT
  have hmD : 72 * ((D₀ : ℝ) + 4) ≤ Real.log (Real.log x) :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) hLT
  have hthr3 : 3 / c ≤ Real.log (Real.log x) :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) hLT
  -- the cutoff, as a natural number, and the two hypotheses it has to satisfy
  have hY36 : Real.exp 36 ≤ harperCutoff x := exp_le_harperCutoff hx36
  have he36 : (37 : ℝ) ≤ Real.exp 36 := by linarith [Real.add_one_le_exp (36 : ℝ)]
  have hY4 : (4 : ℝ) ≤ harperCutoff x := by linarith
  have hfl2 : (2 : ℝ) ≤ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := by
    have h : (2 : ℕ) ≤ ⌊harperCutoff x⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast h
  have hy₀y : y₀ ≤ ⌊harperCutoff x⌋₊ := le_floor_harperCutoff hx36 hmy
  have hx₁y : x₁ ≤ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := by
    have h := le_floor_harperCutoff hx36 hmx
    have hceil : x₁ ≤ (⌈x₁⌉₊ : ℝ) := Nat.le_ceil x₁
    have hcast : ((⌈x₁⌉₊ : ℕ) : ℝ) ≤ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  have hstep := H Y μ hY x ⌊harperCutoff x⌋₊ q hy₀y hx₁y (harperCutoff_sieve hx36) hq0 hq1
  -- the two trades, from the quartered block count down to `ℓogℓog x`
  have hll : Real.log (Real.log x)
      ≤ (3 : ℝ) ^ 2 * Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)) :=
    loglog_le_sq_loglog_floor_harperCutoff hx36
  have hLy8 : 8 * ((D₀ : ℝ) + 4)
      ≤ Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)) := by
    have hD0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
    norm_num at hll
    linarith
  have ht1 : (1 + (1 - q)
        * Real.sqrt ((harperBlockCount D₀ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) / 4 : ℕ) : ℝ)) ^ (-q)
      ≤ 4 * (1 + (1 - q)
        * Real.sqrt (Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)))) ^ (-q) :=
    rpow_neg_target_le_of_sq_le (by norm_num) (loglog_le_sq_blockCount_div_four hLy8)
      (by linarith) hq1
  have ht2 : (1 + (1 - q)
        * Real.sqrt (Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)))) ^ (-q)
      ≤ 3 * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) :=
    rpow_neg_target_le_of_sq_le (by norm_num) hll (by linarith) hq1
  -- the additive error is below the target
  have herr := harper_error_bound (x := x) (C := C₁) (K := K) (c := c) (q := q)
    (ℓ := Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)) hC₁ hK hc hx36 hthr hq0 hq1
    (Real.log_pos (by linarith))
    (Real.log_le_log (by linarith) (Nat.floor_le (by linarith)))
  have htar := harper_error_le_target (c := c / 3) (by linarith) hx36
    (by rw [show (1 : ℝ) / (c / 3) = 3 / c by field_simp]; exact hthr3) hq0 hq1
  have hT0 : (0 : ℝ) ≤ (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) :=
    Real.rpow_nonneg (by nlinarith [Real.sqrt_nonneg (Real.log (Real.log x))]) _
  have hmain : C₁ * (1 + (1 - q)
        * Real.sqrt ((harperBlockCount D₀ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) / 4 : ℕ) : ℝ)) ^ (-q)
      ≤ 12 * C₁ * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
    calc C₁ * (1 + (1 - q)
          * Real.sqrt ((harperBlockCount D₀ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) / 4 : ℕ) : ℝ)) ^ (-q)
        ≤ C₁ * (4 * (1 + (1 - q)
            * Real.sqrt (Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)))) ^ (-q)) :=
          mul_le_mul_of_nonneg_left ht1 hC₁.le
      _ ≤ C₁ * (4 * (3 * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left ht2 (by norm_num : (0 : ℝ) ≤ 4)) hC₁.le
      _ = 12 * C₁ * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by ring
  linarith [hstep, hmain, herr, htar]

/-- **Harper's upper bound, on all of `[0,1]`.**  `E|S_x|^{2q} ≪ (1+(1-q)√(log log x))^{-q}` for
every `q ∈ [0,1]` and every `x` past the same threshold as `RMF.harper_upper_rademacher`, with
constant `3 · max 1 C` for that theorem's `C`. -/
theorem harper_upper_full_rademacher :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
        ∀ x q : ℝ, x₀ ≤ x → 0 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  obtain ⟨C, hC0, x₀, hup⟩ := harper_upper_rademacher (Ω := Ω)
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

`RMF.harper_upper_full_rademacher` is asymptotic: its threshold `x₀` is existentially quantified.
`RMF.harper_low_moments_rademacher` is stated at `3 ≤ x`, so the two do not meet until
the bounded range `[3, x₀]` is covered as well.

There is nothing in that range.  A Rademacher partial sum is `⌊x⌋₊` terms of modulus **at
most** `1` — the function vanishes off the squarefrees — so `‖S_x‖ ≤ √x` all the same, and on a
bounded range that is a constant; the target is bounded below there because `\log\log 3 > 0`.
Enlarging `C` absorbs both.  This is the only step of the upper bound that is not asymptotic. -/

/-- **The moment is bounded on a bounded range.**  For `3 ≤ x ≤ X`, `E|S_x|^{2q} ≤ \max\{1, X\}`,
uniformly in `q ∈ [0,1]`.

`‖S_x‖ ≤ ⌊x⌋₊/√x ≤ √x ≤ √X` (`RMF.IsRademacherRMF.ae_norm_normalisedSum_le`), and
`(√X)^{2q} = X^q ≤ \max\{1, X\}` by
`RMF.rpow_le_max_one`. -/
lemma IsRademacherRMF.integral_norm_normalisedSum_rpow_le_of_le
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ)
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

/-- **Harper's upper bound for the Rademacher function, at the threshold the target is stated
with**: for every `x ≥ 3` and `q ∈ [0,1]`, `E|S_x|^{2q} ≤ C (1 + (1-q)√(log log x))^{-q}`, with `C`
independent of `f`, `μ`, `x` and `q`.  This is the upper half of Harper's Theorem 2, on the range
`RMF.harper_low_moments_rademacher` asks for; the twin of `RMF.harper_upper_ge_three`.

Above `RMF.harper_upper_full_rademacher`'s threshold `x₀` this is that theorem; below it, the left
side is at most `max 1 x₀` (`RMF.IsRademacherRMF.integral_norm_normalisedSum_rpow_le_of_le`) and
the right side is at least `C/(1 + √(log log x₀))`. -/
theorem harper_upper_ge_three_rademacher :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
        ∀ x q : ℝ, 3 ≤ x → 0 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) :=
  harper_upper_ge_three_of_full harper_upper_full_rademacher
    (fun _ _ hf _ _ _ hx hxX hq0 hq1 =>
      hf.integral_norm_normalisedSum_rpow_le_of_le hx hxX hq0 hq1)
end RMF
