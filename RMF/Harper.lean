/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import RMF.Reduction.CoordinateModel
import RMF.Reduction.HarperMoment
import RMF.Reduction.Upper
import RMF.Reduction.UpperSieveNumeral

/-!
# Harper's theorem

Harper's Theorem 1: for the Steinhaus random multiplicative function `f`, uniformly for `q ∈ [0,1]`
and `x ≥ 3`,

`E|S_x|^{2q} ≍ (1 + (1-q)√(log log x))^{-q}`,   `S_x = x^{-1/2} ∑_{n ≤ x} f(n)`,

with constants independent of the probability space (`RMF.harper_low_moments`).

The upper bound is `RMF.harper_upper_ge_three`; the lower bound for `q ∈ [2/3, 1)` and large `x`
is `RMF.exists_le_integral_rpow_normalisedSum`.  This file supplies the rest:

1. the bounded range of `x` and the endpoint `q = 1`, from the second moment;
2. the range `q < 2/3`, by Hölder descent from `q = 2/3` and `q = 3/4`, which reproduces the shape
   `(1 + (1-q)√Λ)^{-q}` exactly; the upper bound at `q = 3/4` is `RMF.harper_upper_numeral`, with
   the explicit constant `20`;
3. the assembly on one probability space, carried to every space through the coordinate model
   (`RMF.IsIIDPrimeValues.integral_rpow_normalisedSum_compMultExtension_eq`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

universe u

/-! ### The bounded range, and the endpoint `q = 1`

For `0 ≤ q ≤ 1` and `‖S‖ ≤ M` with `M ≥ 1`, `‖S‖² ≤ M²‖S‖^{2q}` pointwise, so
`E‖S‖^{2q} ≥ E‖S‖²/M²`.  With `M = √x` this is a positive constant on a bounded range of `x`; at
`q = 1` the second moment is the moment itself. -/

/-- `t^(2 : ℝ) = t^2`. -/
lemma rpow_two_eq_sq (t : ℝ) : t ^ (2 : ℝ) = t ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **Low moments of a bounded variable are bounded below by its second moment**:
`E‖S‖^{2q} ≥ m/M²` whenever `m ≤ E‖S‖²`, `‖S‖ ≤ M` a.e., `1 ≤ M`, `0 ≤ q ≤ 1` and `‖S‖^{2q}` is
integrable. -/
lemma le_integral_rpow_of_second_moment {S : Ω → ℂ} {μ : Measure Ω} {q M m : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hM : 1 ≤ M)
    (hbdd : ∀ᵐ ω ∂μ, ‖S ω‖ ≤ M)
    (hm : m ≤ ∫ ω, ‖S ω‖ ^ (2 : ℝ) ∂μ)
    (hint : Integrable (fun ω => ‖S ω‖ ^ (2 * q)) μ) :
    m / M ^ 2 ≤ ∫ ω, ‖S ω‖ ^ (2 * q) ∂μ := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hM2 : M ^ (2 : ℝ) = M ^ 2 := rpow_two_eq_sq M
  have hptw : ∀ᵐ ω ∂μ, ‖S ω‖ ^ (2 : ℝ) ≤ M ^ 2 * ‖S ω‖ ^ (2 * q) := by
    filter_upwards [hbdd] with ω hω
    have hn := norm_nonneg (S ω)
    rcases eq_or_lt_of_le hn with h0 | h0
    · rw [← h0, Real.zero_rpow (by norm_num)]
      positivity
    · have hsplit : ‖S ω‖ ^ (2 : ℝ) = ‖S ω‖ ^ (2 * q) * ‖S ω‖ ^ (2 - 2 * q) := by
        rw [← Real.rpow_add h0]
        ring_nf
      have hle : ‖S ω‖ ^ (2 - 2 * q) ≤ M ^ (2 - 2 * q) :=
        Real.rpow_le_rpow hn hω (by linarith)
      have hMle : M ^ (2 - 2 * q) ≤ M ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hM (by linarith)
      rw [hsplit]
      calc ‖S ω‖ ^ (2 * q) * ‖S ω‖ ^ (2 - 2 * q)
          ≤ ‖S ω‖ ^ (2 * q) * M ^ (2 : ℝ) := by
            gcongr
            exact le_trans hle hMle
        _ = M ^ 2 * ‖S ω‖ ^ (2 * q) := by rw [hM2]; ring
  have hmono : ∫ ω, ‖S ω‖ ^ (2 : ℝ) ∂μ ≤ ∫ ω, M ^ 2 * ‖S ω‖ ^ (2 * q) ∂μ :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) _)
      (hint.const_mul _) hptw
  rw [integral_const_mul] at hmono
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hm, hmono]

/-- **The second moment of the normalised sum**: `E‖S_x‖² = ⌊x⌋/x`. -/
lemma integral_rpow_two_normalisedSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsSteinhausRMF f μ) {x : ℝ} (hx : 0 < x) :
    ∫ ω, ‖normalisedSum f x ω‖ ^ (2 : ℝ) ∂μ = (⌊x⌋₊ : ℝ) / x := by
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
  have hpt : ∀ ω, ‖normalisedSum f x ω‖ ^ (2 : ℝ) = ‖partialSum f ⌊x⌋₊ ω‖ ^ 2 / x := by
    intro ω
    rw [rpow_two_eq_sq, normalisedSum, randomSum_eq_partialSum, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hsx.le, div_pow, Real.sq_sqrt hx.le]
  simp_rw [hpt]
  rw [integral_div, hf.second_moment]

/-- `E‖S_x‖² ≥ 2/3` for `x ≥ 3`, since `⌊x⌋ > x - 1`. -/
lemma two_thirds_le_integral_rpow_two_normalisedSum {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hf : IsSteinhausRMF f μ) {x : ℝ} (hx : 3 ≤ x) :
    (2 : ℝ) / 3 ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 : ℝ) ∂μ := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [integral_rpow_two_normalisedSum hf hx0, le_div_iff₀ hx0]
  have h1 : x - 1 < (⌊x⌋₊ : ℝ) := Nat.sub_one_lt_floor x
  linarith

/-! ### The descent below `q = 2/3`

A lower bound at `q = 2/3` and an upper bound at `q = 3/4` give a lower bound at every `q ≤ 2/3`,
of the form `(A/B^β)^{1/α}`, where `α + β = 1` are the Hölder weights interpolating the
`4/3`-moment between the `2q`- and the `3/2`-moment.  It reproduces the target's shape exactly,
since `(-2/3 + 3β/4)/α = -q`; the bases `1 + t/3`, `1 + t/4` and `1 + (1-q)t` all lie between
`(1+t)/4` and `1+t`, which costs only absolute constants. -/

/-- **The descent against an upper bound at any `q' ∈ (2/3, 1)`.**  From
`c(1+t/3)^{-2/3} ≤ E‖S‖^{4/3}` and `E‖S‖^{2q'} ≤ C(1+(1-q')t)^{-q'}`, for every `q ∈ [0, 2/3]`,
`E‖S‖^{2q} ≥ (1/3)·\min\{K₀, K₀^p\}·(1 + (1-q)t)^{-q}` with `K₀ = c/\max\{1, C/(1-q')\}` and
`p = q'/(q' - 2/3)`.  The power `p` falls to `3` as `q' → 1`; at `q' = 3/4` it is `9`. -/
lemma le_target_of_two_thirds_lower_of {S : Ω → ℂ} {μ : Measure Ω} {q q' c C t : ℝ}
    (hq0 : 0 ≤ q) (hq23 : q ≤ 2 / 3) (hq'23 : 2 / 3 < q') (hq'1 : q' < 1)
    (hc : 0 < c) (hC : 0 < C) (ht : 0 ≤ t)
    (hlow : c * (1 + (1 - 2 / 3) * t) ^ (-(2 / 3) : ℝ) ≤ ∫ ω, ‖S ω‖ ^ (4 / 3 : ℝ) ∂μ)
    (hup : (∫ ω, ‖S ω‖ ^ (2 * q') ∂μ) ≤ C * (1 + (1 - q') * t) ^ (-q'))
    (hIq : Integrable (fun ω => ‖S ω‖ ^ (2 * q)) μ)
    (hIq' : Integrable (fun ω => ‖S ω‖ ^ (2 * q')) μ)
    (hI43 : Integrable (fun ω => ‖S ω‖ ^ (4 / 3 : ℝ)) μ) :
    1 / 3 * min (c / max 1 (C / (1 - q'))) ((c / max 1 (C / (1 - q'))) ^ (q' / (q' - 2 / 3)))
        * (1 + (1 - q) * t) ^ (-q)
      ≤ ∫ ω, ‖S ω‖ ^ (2 * q) ∂μ := by
  have hq1' : q ≤ 1 := by linarith
  have hδ : (0 : ℝ) < 1 - q' := by linarith
  have hd : (0 : ℝ) < 2 * q' - 2 * q := by linarith
  have he : (0 : ℝ) < 2 * q' - 4 / 3 := by linarith
  have hd' : (2 * q' - 2 * q : ℝ) ≠ 0 := hd.ne'
  -- the interpolation weights: `4/3` between `2q` and `2q'`
  set α : ℝ := (2 * q' - 4 / 3) / (2 * q' - 2 * q) with hαdef
  set β : ℝ := (4 / 3 - 2 * q) / (2 * q' - 2 * q) with hβdef
  have hα0 : 0 < α := div_pos he hd
  have hβ0 : 0 ≤ β := div_nonneg (by linarith) hd.le
  have hαd : α * (2 * q' - 2 * q) = 2 * q' - 4 / 3 := by rw [hαdef]; exact div_mul_cancel₀ _ hd'
  have hβd : β * (2 * q' - 2 * q) = 4 / 3 - 2 * q := by rw [hβdef]; exact div_mul_cancel₀ _ hd'
  have hαβ : α + β = 1 := by
    apply mul_right_cancel₀ hd'
    linear_combination hαd + hβd
  have habc : 2 * q * α + 2 * q' * β = 4 / 3 := by
    apply mul_right_cancel₀ hd'
    linear_combination 2 * q * hαd + 2 * q' * hβd
  have hβ1 : β ≤ 1 := by linarith
  set u : ℝ := 1 + t with hudef
  have hu1 : (1 : ℝ) ≤ u := by rw [hudef]; linarith
  have hu0 : (0 : ℝ) < u := by linarith
  set D : ℝ := C / (1 - q') with hDdef
  have hD0 : (0 : ℝ) < D := div_pos hC hδ
  -- replace the three bases by `u`
  set A : ℝ := c * u ^ (-(2 / 3) : ℝ) with hAdef
  set B : ℝ := D * u ^ (-q') with hBdef
  have hA0 : (0 : ℝ) < A := by rw [hAdef]; positivity
  have hB0 : (0 : ℝ) < B := by rw [hBdef]; positivity
  have hAle : A ≤ ∫ ω, ‖S ω‖ ^ (4 / 3 : ℝ) ∂μ := by
    refine le_trans ?_ hlow
    have hb : (0 : ℝ) < 1 + (1 - 2 / 3) * t := by linarith
    have hmono : u ^ (-(2 / 3) : ℝ) ≤ (1 + (1 - 2 / 3) * t) ^ (-(2 / 3) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hb (by rw [hudef]; linarith) (by norm_num)
    rw [hAdef]
    exact mul_le_mul_of_nonneg_left hmono hc.le
  have hBge : (∫ ω, ‖S ω‖ ^ (2 * q') ∂μ) ≤ B := by
    refine le_trans hup ?_
    have hbase : (1 - q') * u ≤ 1 + (1 - q') * t := by rw [hudef]; nlinarith
    have hmono : (1 + (1 - q') * t) ^ (-q') ≤ ((1 - q') * u) ^ (-q') :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
    have hsplit : ((1 - q') * u) ^ (-q') = (1 - q') ^ (-q') * u ^ (-q') :=
      Real.mul_rpow hδ.le hu0.le
    have hδq : (1 - q') ^ (-q') ≤ (1 - q') ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) (by linarith)
    have hδ1 : (1 - q') ^ (-1 : ℝ) = 1 / (1 - q') := by
      rw [Real.rpow_neg_one, one_div]
    have hu' : (0 : ℝ) ≤ u ^ (-q') := Real.rpow_nonneg hu0.le _
    rw [hBdef, hDdef]
    calc C * (1 + (1 - q') * t) ^ (-q')
        ≤ C * (((1 - q') * u) ^ (-q')) := mul_le_mul_of_nonneg_left hmono hC.le
      _ = C * ((1 - q') ^ (-q') * u ^ (-q')) := by rw [hsplit]
      _ ≤ C * ((1 - q') ^ (-1 : ℝ) * u ^ (-q')) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδq hu') hC.le
      _ = C / (1 - q') * u ^ (-q') := by rw [hδ1]; ring
  -- the interpolation, then replace the `2q'`-moment by its upper bound
  have hcore := integral_rpow_le_mul_rpow (S := S) (μ := μ) (a := 2 * q) (b := 2 * q')
    (c := 4 / 3) hα0.le hβ0 hαβ habc (by norm_num) hIq hIq' hI43
  have hIq0 : (0 : ℝ) ≤ ∫ ω, ‖S ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hIq'0 : (0 : ℝ) ≤ ∫ ω, ‖S ω‖ ^ (2 * q') ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hstep : A ≤ (∫ ω, ‖S ω‖ ^ (2 * q) ∂μ) ^ α * B ^ β := by
    refine hAle.trans (hcore.trans ?_)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hIq'0 hBge hβ0)
      (Real.rpow_nonneg hIq0 _)
  have hBb : (0 : ℝ) < B ^ β := Real.rpow_pos_of_pos hB0 _
  have hdiv : A / B ^ β ≤ (∫ ω, ‖S ω‖ ^ (2 * q) ∂μ) ^ α := (div_le_iff₀ hBb).2 hstep
  have hdesc : (A / B ^ β) ^ α⁻¹ ≤ ∫ ω, ‖S ω‖ ^ (2 * q) ∂μ := by
    calc (A / B ^ β) ^ α⁻¹
        ≤ ((∫ ω, ‖S ω‖ ^ (2 * q) ∂μ) ^ α) ^ α⁻¹ :=
          Real.rpow_le_rpow (le_of_lt (div_pos hA0 hBb)) hdiv (inv_nonneg.2 hα0.le)
      _ = ∫ ω, ‖S ω‖ ^ (2 * q) ∂μ := by
          rw [← Real.rpow_mul hIq0, mul_inv_cancel₀ hα0.ne', Real.rpow_one]
  refine le_trans ?_ hdesc
  -- the quotient, in closed form
  have hquot : A / B ^ β = c / D ^ β * u ^ (-(2 / 3 : ℝ) + q' * β) := by
    have hBp : B ^ β = D ^ β * u ^ (-q' * β) := by
      rw [hBdef, Real.mul_rpow hD0.le (Real.rpow_pos_of_pos hu0 _).le,
        ← Real.rpow_mul hu0.le]
    have h1 : D ^ β ≠ 0 := (Real.rpow_pos_of_pos hD0 β).ne'
    have h2 : u ^ (-q' * β) ≠ 0 := (Real.rpow_pos_of_pos hu0 _).ne'
    have hexp : -(2 / 3 : ℝ) + q' * β = -(2 / 3 : ℝ) - -q' * β := by ring
    rw [hAdef, hBp, hexp, Real.rpow_sub hu0]
    field_simp
  have hexpq : (-(2 / 3 : ℝ) + q' * β) * α⁻¹ = -q := by
    have hkey : -(2 / 3 : ℝ) + q' * β = -q * α := by
      apply mul_right_cancel₀ hd'
      linear_combination q' * hβd + q * hαd
    rw [hkey, mul_assoc, mul_inv_cancel₀ hα0.ne', mul_one]
  have hKq : (A / B ^ β) ^ α⁻¹ = (c / D ^ β) ^ α⁻¹ * u ^ (-q) := by
    rw [hquot, Real.mul_rpow (div_nonneg hc.le (Real.rpow_pos_of_pos hD0 β).le)
      (Real.rpow_pos_of_pos hu0 _).le, ← Real.rpow_mul hu0.le, hexpq]
  rw [hKq]
  -- the constant: `D^β ≤ max 1 D`, and `α⁻¹ ∈ [1, p]`
  have hK0 : (0 : ℝ) < c / max 1 D :=
    div_pos hc (lt_of_lt_of_le one_pos (le_max_left _ _))
  have hDβ : D ^ β ≤ max 1 D := by
    rcases le_total D 1 with h | h
    · exact le_trans (Real.rpow_le_one hD0.le h hβ0) (le_max_left _ _)
    · refine le_trans (Real.rpow_le_rpow_of_exponent_le h hβ1) ?_
      rw [Real.rpow_one]
      exact le_max_right _ _
  have hKle : c / max 1 D ≤ c / D ^ β :=
    div_le_div_of_nonneg_left hc.le (Real.rpow_pos_of_pos hD0 β) hDβ
  have hαinv : α⁻¹ = (2 * q' - 2 * q) / (2 * q' - 4 / 3) := by
    rw [hαdef, inv_div]
  have hα1 : 1 ≤ α⁻¹ := by
    rw [hαinv, le_div_iff₀ he]
    linarith
  have hαp : α⁻¹ ≤ q' / (q' - 2 / 3) := by
    rw [hαinv, div_le_div_iff₀ he (by linarith)]
    nlinarith [mul_nonneg hq0 he.le]
  have hmin : min (c / max 1 D) ((c / max 1 D) ^ (q' / (q' - 2 / 3)))
      ≤ (c / D ^ β) ^ α⁻¹ := by
    refine le_trans ?_ (Real.rpow_le_rpow hK0.le hKle (by linarith))
    have h := min_rpow_le_rpow hK0 hα1 hαp
    rwa [Real.rpow_one] at h
  -- the base: `1 + (1-q)t ≥ u/3`, so `(1+(1-q)t)^{-q} ≤ 3 u^{-q}`
  have hqt : (0 : ℝ) ≤ (2 / 3 - q) * t := mul_nonneg (by linarith) ht
  have hb0 : (0 : ℝ) < 1 + (1 - q) * t := by linarith
  have hbase : (1 + (1 - q) * t) ^ (-q) ≤ 3 * u ^ (-q) := by
    have hu3 : u / 3 ≤ 1 + (1 - q) * t := by rw [hudef]; linarith
    have hmono : (1 + (1 - q) * t) ^ (-q) ≤ (u / 3) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos (div_pos hu0 (by norm_num)) hu3 (neg_nonpos.2 hq0)
    have hsplit : (u / 3) ^ (-q) = 3 ^ q * u ^ (-q) := by
      rw [Real.div_rpow hu0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3)]
      field_simp
    have h3q : (3 : ℝ) ^ q ≤ 3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hq1'
      rwa [Real.rpow_one] at h
    rw [hsplit] at hmono
    refine le_trans hmono ?_
    have hup0 : (0 : ℝ) ≤ u ^ (-q) := Real.rpow_nonneg hu0.le _
    exact mul_le_mul_of_nonneg_right h3q hup0
  have hmin0 : (0 : ℝ) ≤ min (c / max 1 D) ((c / max 1 D) ^ (q' / (q' - 2 / 3))) :=
    le_min hK0.le (Real.rpow_nonneg hK0.le _)
  have hMq0 : (0 : ℝ) ≤ (c / D ^ β) ^ α⁻¹ :=
    Real.rpow_nonneg (div_nonneg hc.le (Real.rpow_pos_of_pos hD0 β).le) _
  calc 1 / 3 * min (c / max 1 D) ((c / max 1 D) ^ (q' / (q' - 2 / 3)))
          * (1 + (1 - q) * t) ^ (-q)
      ≤ 1 / 3 * (c / D ^ β) ^ α⁻¹ * (3 * u ^ (-q)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmin (by norm_num)) hbase
          (Real.rpow_nonneg hb0.le _) (mul_nonneg (by norm_num) hMq0)
    _ = (c / D ^ β) ^ α⁻¹ * u ^ (-q) := by ring

/-- **The descent, in the target's shape.**  From `c(1+t/3)^{-2/3} ≤ E‖S‖^{4/3}` and
`E‖S‖^{3/2} ≤ C(1+t/4)^{-3/4}`, for every `q ∈ [0, 2/3]`,
`E‖S‖^{2q} ≥ (1/3)·min{K₀, K₀^9}·(1 + (1-q)t)^{-q}` with `K₀ = c/max{1, 4C}`, independent of `q`.
This is Harper's own descent (Harper, arXiv:1703.06654):
`RMF.le_target_of_two_thirds_lower_of` at `q' = 3/4`. -/
lemma le_target_of_two_thirds_lower {S : Ω → ℂ} {μ : Measure Ω} {q c C t : ℝ}
    (hq0 : 0 ≤ q) (hq23 : q ≤ 2 / 3) (hc : 0 < c) (hC : 0 < C) (ht : 0 ≤ t)
    (hlow : c * (1 + (1 - 2 / 3) * t) ^ (-(2 / 3) : ℝ) ≤ ∫ ω, ‖S ω‖ ^ (4 / 3 : ℝ) ∂μ)
    (hup : (∫ ω, ‖S ω‖ ^ (3 / 2 : ℝ) ∂μ) ≤ C * (1 + (1 - 3 / 4) * t) ^ (-(3 / 4) : ℝ))
    (hIq : Integrable (fun ω => ‖S ω‖ ^ (2 * q)) μ)
    (hI32 : Integrable (fun ω => ‖S ω‖ ^ (3 / 2 : ℝ)) μ)
    (hI43 : Integrable (fun ω => ‖S ω‖ ^ (4 / 3 : ℝ)) μ) :
    1 / 3 * min (c / max 1 (4 * C)) ((c / max 1 (4 * C)) ^ (9 : ℝ))
        * (1 + (1 - q) * t) ^ (-q)
      ≤ ∫ ω, ‖S ω‖ ^ (2 * q) ∂μ := by
  have h32 : (2 : ℝ) * (3 / 4) = 3 / 2 := by norm_num
  have h := le_target_of_two_thirds_lower_of (q' := 3 / 4) hq0 hq23 (by norm_num) (by norm_num)
    hc hC ht hlow (by rw [h32]; exact hup) hIq (by rw [h32]; exact hI32) hI43
  rw [show C / (1 - 3 / 4 : ℝ) = 4 * C by ring,
    show (3 / 4 : ℝ) / (3 / 4 - 2 / 3) = 9 by norm_num] at h
  exact h

/-! ### The assembly on one probability space -/

/-- `‖S_x‖^r` is integrable for every `r ≥ 0`: it is bounded and `μ` is a probability measure. -/
lemma integrable_rpow_normalisedSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω => ‖normalisedSum f x ω‖ ^ r) μ := by
  haveI := hf.isProbabilityMeasure
  have hmeas : Measurable fun ω => normalisedSum f x ω := hf.measurable_normalisedSum x
  have hm : AEStronglyMeasurable (fun ω => ‖normalisedSum f x ω‖ ^ r) μ := by fun_prop
  refine (memLp_top_of_bound hm (((⌊x⌋₊ : ℝ) / Real.sqrt x) ^ r) ?_).integrable le_top
  filter_upwards [hf.ae_norm_normalisedSum_le x] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_rpow (norm_nonneg _) hω hr

/-! ### The full-range constant, as a formula

The extension to `q ∈ [0,1]` and `x ≥ 3` costs three more branch constants, and one of them —
the bounded range — is governed by the *threshold* `x₀` of the Euler-product chain rather than by
its constant.  Naming the combination keeps both dependences usable.

The assembly is law-agnostic: it needs the chain's bound, an upper bound at `q = 3/4`, a second
moment, and integrability.  Harper's Theorem 1 and his Theorem 2 are both instances, differing
only in the second-moment constant (`2/3` against `1/48`) and in the upper constant (the numeral
`20` of `RMF.harper_upper_numeral` against the existential of
`RMF.harper_upper_ge_three_rademacher`). -/

/-- **The full-range lower constant**, as a formula in the second-moment constant `sm`, the upper
constant `C₁`, the Euler-product chain's constant `c₁` and its threshold `x₀`.  The four branches
are: the bounded range `x < \max(x₀,3)`, where the second moment gives `sm/x`; the chain
itself on `q ∈ [2/3,1)`; the endpoint `q = 1`, where `W = 1`; and the descent below `q = 2/3`,
which costs `K₀ = c₁/\max(1,4C₁)` to the ninth power.

The bounded range is `1/x`, not `1/x²`: the a.e. bound on `‖S_x‖` is `\lfloor x\rfloor/\sqrt x
≤ \sqrt x`, so the second moment is divided by `x` rather than by `x²`.  This matters because
`x₀` is a tower, and this branch is what decides the constant at `x ≥ 3`. -/
noncomputable def harperFullConstOf (sm C₁ c₁ x₀ : ℝ) : ℝ :=
  min (min (sm / max 1 (max x₀ 3)) c₁)
    (min sm (1 / 3 * min (c₁ / max 1 (4 * C₁)) ((c₁ / max 1 (4 * C₁)) ^ (9 : ℝ))))

lemma harperFullConstOf_pos {sm C₁ c₁ x₀ : ℝ} (hsm : 0 < sm) (hc₁ : 0 < c₁) :
    0 < harperFullConstOf sm C₁ c₁ x₀ := by
  have hX : (0 : ℝ) < max 1 (max x₀ 3) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK : (0 : ℝ) < c₁ / max 1 (4 * C₁) :=
    div_pos hc₁ (lt_of_lt_of_le one_pos (le_max_left _ _))
  rw [harperFullConstOf]
  exact lt_min (lt_min (div_pos hsm hX) hc₁)
    (lt_min hsm (mul_pos (by norm_num) (lt_min hK (Real.rpow_pos_of_pos hK (9 : ℝ)))))

/-- **The full-range lower constant for the Steinhaus function**: `sm = 2/3` from the second
moment `\lfloor x\rfloor/x ≥ 2/3`, and `C₁ = 20` from `RMF.harper_upper_numeral`. -/
noncomputable def harperFullConst (c₁ x₀ : ℝ) : ℝ := harperFullConstOf (2 / 3) 20 c₁ x₀

lemma harperFullConst_pos {c₁ x₀ : ℝ} (hc₁ : 0 < c₁) : 0 < harperFullConst c₁ x₀ :=
  harperFullConstOf_pos (by norm_num) hc₁

/-- **Harper's lower bound on `0 ≤ q ≤ 1` and `x ≥ 3`, for any law, with the constant a
formula.**  Above the threshold and on `q ∈ [2/3, 1)` it is the Euler-product chain `HA`; below
`2/3`, the descent `RMF.le_target_of_two_thirds_lower` against `HU` at `q = 3/4`; the bounded
range of `x` and the endpoint `q = 1` come from the second moment `hsq`.

Every hypothesis is supplied by both laws: `hae`, `hsq` and `hint` are the three facts about
`‖S_x‖` that the argument uses, and each is proved for the Steinhaus and the Rademacher predicate
alike. -/
theorem le_integral_rpow_normalisedSum_full_of_law {Ω : Type*} [MeasurableSpace Ω]
    (P : (Ω → ArithmeticFunction ℂ) → Measure Ω → Prop) {sm C₁ c₁ x₀ : ℝ}
    (hsm : 0 < sm) (hC₁ : 0 < C₁) (hc₁ : 0 < c₁)
    (hae : ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ → ∀ x : ℝ,
      ∀ᵐ ω ∂μ, ‖normalisedSum f x ω‖ ≤ (⌊x⌋₊ : ℝ) / Real.sqrt x)
    (hsq : ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ → ∀ x : ℝ, 3 ≤ x →
      sm ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 : ℝ) ∂μ)
    (hint : ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ → ∀ x r : ℝ, 0 ≤ r →
      Integrable (fun ω => ‖normalisedSum f x ω‖ ^ r) μ)
    (HA : ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ →
      ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q < 1 →
        c₁ * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
          ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ)
    (HU : ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ →
      ∀ x q : ℝ, 3 ≤ x → 0 ≤ q → q ≤ 1 →
        (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ)
          ≤ C₁ * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)) :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ →
      ∀ x q : ℝ, 3 ≤ x → 0 ≤ q → q ≤ 1 →
        harperFullConstOf sm C₁ c₁ x₀
            * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
          ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ := by
  set X₀ : ℝ := max x₀ 3 with hX₀def
  have hX₀3 : (3 : ℝ) ≤ X₀ := le_max_right _ _
  have hX1 : (0 : ℝ) < max 1 X₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
  set K₀ : ℝ := c₁ / max 1 (4 * C₁) with hK₀def
  have hK₀ : (0 : ℝ) < K₀ := by
    rw [hK₀def]
    exact div_pos hc₁ (lt_of_lt_of_le one_pos (le_max_left _ _))
  set cs : ℝ := sm / max 1 X₀ with hcsdef
  have hcs : (0 : ℝ) < cs := by
    rw [hcsdef]
    exact div_pos hsm hX1
  set cd : ℝ := 1 / 3 * min K₀ (K₀ ^ (9 : ℝ)) with hcddef
  have hcd : (0 : ℝ) < cd := by
    rw [hcddef]
    exact mul_pos (by norm_num) (lt_min hK₀ (Real.rpow_pos_of_pos hK₀ (9 : ℝ)))
  have hconst : harperFullConstOf sm C₁ c₁ x₀ = min (min cs c₁) (min sm cd) := by
    rw [harperFullConstOf, hcsdef, hcddef, hK₀def, hX₀def]
  intro f μ hf x q hx hq0 hq1
  rw [hconst]
  set t : ℝ := Real.sqrt (Real.log (Real.log x)) with htdef
  have ht0 : (0 : ℝ) ≤ t := Real.sqrt_nonneg _
  have hW1 : (1 : ℝ) ≤ 1 + (1 - q) * t := by nlinarith
  have hW0 : (0 : ℝ) < 1 + (1 - q) * t := by linarith
  have hWq0 : (0 : ℝ) ≤ (1 + (1 - q) * t) ^ (-q) := Real.rpow_nonneg hW0.le _
  have hWq1 : (1 + (1 - q) * t) ^ (-q) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hx0 : (0 : ℝ) < x := by linarith
  -- it is enough to hit any of the four branch constants
  have hmin : ∀ b : ℝ, min (min cs c₁) (min sm cd) ≤ b →
      b * (1 + (1 - q) * t) ^ (-q) ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ →
      min (min cs c₁) (min sm cd) * (1 + (1 - q) * t) ^ (-q)
        ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ := by
    intro b hb hbound
    exact le_trans (mul_le_mul_of_nonneg_right hb hWq0) hbound
  rcases (le_or_gt X₀ x).symm with hsmall | hlarge
  · -- **the bounded range**: the second moment, with `W^{-q} ≤ 1`
    refine hmin cs (le_trans (min_le_left _ _) (min_le_left _ _)) ?_
    -- `‖S_x‖ ≤ ⌊x⌋/√x ≤ √x`, so the second moment is divided by `x`, not by `x²`
    have hMx : (1 : ℝ) ≤ Real.sqrt x := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by linarith)
    have hbdd : ∀ᵐ ω ∂μ, ‖normalisedSum f x ω‖ ≤ Real.sqrt x := by
      filter_upwards [hae f μ hf x] with ω hω
      refine le_trans hω ?_
      rw [div_le_iff₀ (Real.sqrt_pos.2 hx0), Real.mul_self_sqrt hx0.le]
      exact Nat.floor_le hx0.le
    have hsm2 := le_integral_rpow_of_second_moment (S := normalisedSum f x) (μ := μ)
      hq0 hq1 hMx hbdd (hsq f μ hf x hx) (hint f μ hf x _ (by linarith))
    rw [Real.sq_sqrt hx0.le] at hsm2
    refine le_trans (le_trans (mul_le_mul_of_nonneg_left hWq1 hcs.le) ?_) hsm2
    rw [mul_one, hcsdef]
    have hle : x ≤ max 1 X₀ := le_trans hsmall.le (le_max_right _ _)
    have hsm0 : (0 : ℝ) ≤ sm := hsm.le
    gcongr
  -- **`x` is large**
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hlarge
  rcases eq_or_lt_of_le hq1 with hq1' | hq1'
  · -- **the endpoint `q = 1`**: `W = 1`, and the second moment is `sm`
    refine hmin sm (le_trans (min_le_right _ _) (min_le_left _ _)) ?_
    subst hq1'
    have hWone : (1 : ℝ) + (1 - 1) * t = 1 := by ring
    rw [hWone, Real.one_rpow, mul_one, show (2 : ℝ) * 1 = 2 by norm_num]
    exact hsq f μ hf x hx
  rcases le_or_gt (2 / 3 : ℝ) q with hq23 | hq23
  · -- **`q ∈ [2/3, 1)`**: the Euler-product chain
    exact hmin c₁ (le_trans (min_le_left _ _) (min_le_right _ _))
      (HA f μ hf x q hxx₀ hq23 hq1')
  · -- **`q < 2/3`**: descend from `q = 2/3`
    refine hmin cd (le_trans (min_le_right _ _) (min_le_right _ _)) ?_
    have hA23 := HA f μ hf x (2 / 3) hxx₀ le_rfl (by norm_num)
    rw [show (2 : ℝ) * (2 / 3) = 4 / 3 by norm_num] at hA23
    have hU34 := HU f μ hf x (3 / 4) hx (by norm_num) (by norm_num)
    rw [show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num] at hU34
    rw [hcddef, hK₀def]
    exact le_target_of_two_thirds_lower hq0 hq23.le hc₁ hC₁ ht0 hA23 hU34
      (hint f μ hf x _ (by linarith)) (hint f μ hf x _ (by norm_num))
      (hint f μ hf x _ (by norm_num))

/-- **Harper's lower bound on `0 ≤ q ≤ 1` and `x ≥ 3` for the Steinhaus function, with the
constant a formula**: `RMF.le_integral_rpow_normalisedSum_full_of_law` at `sm = 2/3` and
`C₁ = 20`. -/
theorem le_integral_rpow_normalisedSum_full_of_lower {Ω : Type*} [MeasurableSpace Ω]
    {c₁ x₀ : ℝ} (hc₁ : 0 < c₁)
    (HA : ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q < 1 →
        c₁ * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
          ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ x q : ℝ, 3 ≤ x → 0 ≤ q → q ≤ 1 →
        harperFullConst c₁ x₀ * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
          ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ := by
  rw [harperFullConst]
  exact le_integral_rpow_normalisedSum_full_of_law (fun f μ => IsSteinhausRMF f μ)
    (by norm_num) (by norm_num) hc₁
    (fun _ _ hf x => hf.ae_norm_normalisedSum_le x)
    (fun _ _ hf x hx => by
      haveI := hf.isProbabilityMeasure
      exact two_thirds_le_integral_rpow_two_normalisedSum hf hx)
    (fun _ _ hf x _ hr => integrable_rpow_normalisedSum hf x hr) HA
    (fun _ _ hf x q hx hq0 hq1 => harper_upper_numeral _ _ hf x q (by linarith) hq0 hq1)

/-- **Harper's lower bound on `0 ≤ q ≤ 1` and `x ≥ 3`, on one probability space.**  For
`q ∈ [2/3, 1)` and large `x` it is `RMF.exists_le_integral_rpow_normalisedSum`; below `2/3`, the
descent `RMF.le_target_of_two_thirds_lower` against the upper bound `20` at `q = 3/4`
(`RMF.harper_upper_numeral`); the bounded range of `x` and `q = 1` come from the second moment.

The `c` produced is `RMF.harperFullConst c₁ x₀`, with `c₁` and `x₀` the constant and threshold of
`RMF.exists_le_integral_rpow_normalisedSum`; the work is
`RMF.le_integral_rpow_normalisedSum_full_of_lower`. -/
theorem exists_le_integral_rpow_normalisedSum_full (Ω : Type*) [MeasurableSpace Ω] :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ x q : ℝ, 3 ≤ x → 0 ≤ q → q ≤ 1 →
          c * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
            ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨c₁, hc₁, x₀, HA⟩ := exists_le_integral_rpow_normalisedSum Ω
  exact ⟨harperFullConst c₁ x₀, harperFullConst_pos hc₁,
    le_integral_rpow_normalisedSum_full_of_lower hc₁ HA⟩

/-! ### Harper's theorem -/

/-- **Harper's Theorem 1: better than squareroot cancellation.**  For the Steinhaus random
multiplicative function, uniformly for `q ∈ [0,1]` and `x ≥ 3`,

`E|S_x|^{2q} ≍ (1 + (1-q)√(log log x))^{-q}`,

with constants independent of the probability space.  On the coordinate model the two bounds are
`RMF.exists_le_integral_rpow_normalisedSum_full` and `RMF.harper_upper_ge_three`;
`RMF.IsIIDPrimeValues.integral_rpow_normalisedSum_compMultExtension_eq` carries them to every
space. -/
theorem harper_low_moments :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω),
        IsSteinhausRMF f μ →
        ∀ x q : ℝ, 3 ≤ x → 0 ≤ q → q ≤ 1 →
          c * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
              ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ ∧
            (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ)
              ≤ C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  have hcoord : IsSteinhausRMF (fun v : Nat.Primes → ℂ => compMultExtension (primeExtend v))
      (Measure.infinitePi fun _ : Nat.Primes => steinhausLaw) :=
    IsSteinhausPrimeValues.isSteinhausRMF (isIIDPrimeValues_primeExtend steinhausLaw)
  obtain ⟨c, hc, HL⟩ := exists_le_integral_rpow_normalisedSum_full (Nat.Primes → ℂ)
  obtain ⟨C, hC, HU⟩ := harper_upper_ge_three (Ω := Nat.Primes → ℂ)
  refine ⟨c, C, hc, hC, fun Ω _ f μ hf x q hx hq0 hq1 => ?_⟩
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  rw [IsIIDPrimeValues.integral_rpow_normalisedSum_compMultExtension_eq hX]
  exact ⟨HL _ _ hcoord x q hx hq0 hq1, HU _ _ hcoord x q hx hq0 hq1⟩

/-! ### `log log x` is bounded below on `x ≥ 3` -/

/-- **`log log x ≥ 4/961` for `x ≥ 3`.**  `4/961 = (2/31)²`, and `log log 3 = 0.094…` clears it. -/
lemma four_div_nine_hundred_sixty_one_le_log_log {x : ℝ} (hx : 3 ≤ x) :
    (4 : ℝ) / 961 ≤ Real.log (Real.log x) := by
  have h3 : (1.0986122885 : ℝ) < Real.log 3 := Real.log_three_gt_d9
  have hlx : (1.0986122885 : ℝ) ≤ Real.log x :=
    le_trans h3.le (Real.log_le_log (by norm_num) hx)
  have hpos : (0 : ℝ) < Real.log x := by linarith
  refine le_trans ?_ (Real.log_le_log (by norm_num) hlx)
  have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1.0986122885 by norm_num)
  norm_num at this ⊢
  linarith

end RMF
