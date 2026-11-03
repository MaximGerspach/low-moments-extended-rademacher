/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2WindowExt.Rest

/-!
# HP2's window integral: the rest on short tubes

`RMF/UniformLower/HP2WindowExt/Rest.lean` for tubes of `r ≥ 35` blocks, where `r + k` may lie below
the explicit PNT's floor `104`.  The rest's exponent is at most
`2∫_{e^{r+k}}^U cos(|h₁ - h₂|u)e^{-2σu}/u du + 10⁻⁴` (`RMF.rest_exponent_le_short`), and the rest
multiplies into the pair moment with it (`RMF.integral_hp1Tube_inter_rest_le_short`).

* **The top block** by explicit Mertens (`RMF.abs_rangeCosSum_top_sub_integral_le_mertens`):
  within `2Ke^{-(R+k)} + Kτ` of its integral, `K = RMF.mertensErrConst`.  Mertens has no floor
  and the top block is one block, so this covers it below scale `104` and above: `≤ 7.43·10⁻⁸`
  from `r + k ≥ 20` with `τ ≤ 2e^{-20}` (`RMF.abs_rangeCosSum_top_sub_integral_le_floor`).
* **The full blocks** `r ≤ m < R` by the two-regime telescoping
  (`RMF.abs_sum_blockCosSum_sub_integral_le_two_regime`, `≤ 3.16·10⁻⁶`), so the rest's cosine sum
  is within `3.24·10⁻⁶` of its integral (`RMF.abs_rangeCosSum_rest_sub_integral_le_short`).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### The top block by explicit Mertens -/

/-- **The top block's partial cosine sum against its integral, by explicit Mertens**: for
`τ, σ ≥ 0` and `y ≥ c_r`, `∑_{c_R ≤ p < y} cos(τ log p)p^{-1-2σ}` is within `2Ke^{-(R+k)} + Kτ` of
`∫_{e^{R+k}}^{U} cos(τu)e^{-2σu}/u du`, `K = RMF.mertensErrConst` — the twin of
`RMF.abs_rangeCosSum_top_sub_integral_le` with no floor on `R + k` (the block's top
`max(y - 1, e^{e^{R+k}}) ≤ e^{e^{R+k+1}}`, so `log log` grows by at most `1`). -/
theorem abs_rangeCosSum_top_sub_integral_le_mertens {k r y : ℕ} {σ τ : ℝ} (hτ : 0 ≤ τ)
    (hσ : 0 ≤ σ) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) :
    |rangeCosSum (⌊blockScale k (restTop k r y)⌋₊ + 1) y σ τ
        - ∫ u in Real.exp ((restTop k r y : ℝ) + k)..restU k r y,
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
      ≤ 2 * mertensErrConst * Real.exp (-((restTop k r y : ℝ) + k)) + mertensErrConst * τ := by
  set R := restTop k r y with hRdef
  set y₁ : ℝ := blockScale k R with hy₁def
  set Y : ℝ := max ((y : ℝ) - 1) y₁ with hYdef
  have hy₁pos : (0 : ℝ) < y₁ := blockScale_pos _ _
  have hlogy₁ : Real.log y₁ = Real.exp ((R : ℝ) + k) := log_blockScale _ _
  have hRk : (0 : ℝ) ≤ (R : ℝ) + k := by positivity
  have hy₁2 : (2 : ℝ) ≤ y₁ := by
    have h1 : Real.exp 1 ≤ y₁ := Real.exp_le_exp.2 (Real.one_le_exp hRk)
    linarith [Real.exp_one_gt_d9]
  have hy₁Y : y₁ ≤ Y := le_max_right _ _
  have hYpos : (0 : ℝ) < Y := hy₁pos.trans_le hy₁Y
  -- the top of the range is below the next block's scale
  have hYtop : Y ≤ blockScale k (R + 1) := by
    refine max_le ?_ (blockScale_mono _ (Nat.le_succ R))
    have h1 := lt_cut_restTop k r y
    have h2 : (y : ℝ) - 1 ≤ (⌊blockScale k (R + 1)⌋₊ : ℝ) := by
      have : y ≤ ⌊blockScale k (R + 1)⌋₊ + 1 := h1.le
      have : (y : ℝ) ≤ (⌊blockScale k (R + 1)⌋₊ : ℝ) + 1 := by exact_mod_cast this
      linarith
    exact h2.trans (Nat.floor_le (blockScale_pos _ _).le)
  have hlogX : Real.log (blockScale k (R + 1)) = Real.exp ((R : ℝ) + k + 1) := by
    rw [log_blockScale]
    push_cast
    ring_nf
  -- the sum over the partial block, as a sum over `(y₁, Y]`
  have hfl : ⌊Y⌋₊ = y - 1 := floor_max_eq hyr
  have hy1 : 1 ≤ y := by have := cut_restTop_le hyr; omega
  have hrw : rangeCosSum (⌊y₁⌋₊ + 1) y σ τ
      = ∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊Y⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log (p : ℝ)) / ((p : ℝ)) ^ (1 + 2 * σ) := by
    rw [filter_prime_Ioc_eq_primesIco, hfl, Nat.sub_add_cancel hy1, rangeCosSum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (prime_of_mem_primesIco hp).pos
    rw [show (-1 - 2 * σ : ℝ) = -(1 + 2 * σ) by ring, Real.rpow_neg hp0.le]
    ring
  rw [hrw, show restU k r y = Real.log Y from rfl]
  -- the integral, in the `u = log t` form
  rw [← hlogy₁, ← integral_cosLogDiv_mul_rpow_eq (by linarith) hy₁Y]
  refine (abs_cos_prime_sum_block_weight_sub_integral_le_mertens τ hy₁2 hy₁Y hσ).trans ?_
  -- `log log` grows by at most `1` across the partial block
  have hlogY : Real.log Y ≤ Real.exp ((R : ℝ) + k + 1) := by
    rw [← hlogX]
    exact Real.log_le_log hYpos hYtop
  have hlogY0 : 0 < Real.log Y := by
    have h := Real.log_le_log hy₁pos hy₁Y
    rw [hlogy₁] at h
    linarith [Real.exp_pos ((R : ℝ) + k)]
  have hll : Real.log (Real.log Y) ≤ (R : ℝ) + k + 1 := by
    have h := Real.log_le_log hlogY0 hlogY
    rwa [Real.log_exp] at h
  have hll₁ : Real.log (Real.log y₁) = (R : ℝ) + k := by rw [hlogy₁, Real.log_exp]
  rw [hll₁, hlogy₁, abs_of_nonneg hτ]
  have hK := mertensErrConst_nonneg
  have h1 : 2 * mertensErrConst / Real.exp ((R : ℝ) + k)
      = 2 * mertensErrConst * Real.exp (-((R : ℝ) + k)) := by
    rw [Real.exp_neg]
    ring
  have h2 : τ * mertensErrConst * (Real.log (Real.log Y) - ((R : ℝ) + k))
      ≤ mertensErrConst * τ := by
    have hτK : 0 ≤ τ * mertensErrConst := mul_nonneg hτ hK
    calc τ * mertensErrConst * (Real.log (Real.log Y) - ((R : ℝ) + k))
        ≤ τ * mertensErrConst * 1 := mul_le_mul_of_nonneg_left (by linarith) hτK
      _ = mertensErrConst * τ := by ring
  linarith

/-- **The top block from the floor `20`**: for `r + k ≥ 20`, `0 ≤ τ ≤ 2e^{-20}`, `σ ≥ 0` and
`y ≥ c_r`, the top block's partial cosine sum is within `7.43·10⁻⁸` of its integral, below scale
`104` and above it alike (`RMF.abs_rangeCosSum_top_sub_integral_le_mertens`:
`2Ke^{-20} + 2Ke^{-20}`, `K ≤ 9.0028`). -/
theorem abs_rangeCosSum_top_sub_integral_le_floor {k r y : ℕ} {σ τ : ℝ}
    (hkr : 20 ≤ (r : ℝ) + k) (hτ : 0 ≤ τ) (hτ2 : τ ≤ 2 * Real.exp (-20)) (hσ : 0 ≤ σ)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) :
    |rangeCosSum (⌊blockScale k (restTop k r y)⌋₊ + 1) y σ τ
        - ∫ u in Real.exp ((restTop k r y : ℝ) + k)..restU k r y,
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
      ≤ 7.43 / 10 ^ 8 := by
  refine (abs_rangeCosSum_top_sub_integral_le_mertens hτ hσ hyr).trans ?_
  have hR : (r : ℝ) ≤ restTop k r y := by exact_mod_cast le_restTop k r y
  have hK := mertensErrConst_le
  have hK0 := mertensErrConst_nonneg
  have he := exp_neg_twenty_le_numeral
  have he0 : 0 ≤ Real.exp (-20) := (Real.exp_pos _).le
  have hem : Real.exp (-((restTop k r y : ℝ) + k)) ≤ Real.exp (-20) :=
    Real.exp_le_exp.2 (by linarith)
  have h1 : mertensErrConst * Real.exp (-((restTop k r y : ℝ) + k))
      ≤ mertensErrConst * Real.exp (-20) := mul_le_mul_of_nonneg_left hem hK0
  have h2 : mertensErrConst * τ ≤ mertensErrConst * (2 * Real.exp (-20)) :=
    mul_le_mul_of_nonneg_left hτ2 hK0
  have h3 : mertensErrConst * Real.exp (-20) ≤ 9.0028 * (1 / 485000000) :=
    mul_le_mul hK he he0 (by norm_num)
  linarith

/-! ### The rest's cosine sum -/

/-- **The rest's cosine sum against its integral from the floor `20`**: for `r + k ≥ 20`,
`0 ≤ τ ≤ 2e^{-20}`, `σ ≥ 0` and `y ≥ c_r`,
`|∑_{c_r ≤ p < y} cos(τ log p)p^{-1-2σ} - ∫_{e^{r+k}}^{U} cos(τu)e^{-2σu}/u du| ≤ 3.24·10⁻⁶` — the
full blocks `r ≤ m < R` by the two-regime telescoping (`RMF.blockCosTelErr_le_numeral`,
`3.16·10⁻⁶`), the top block by Mertens (`7.43·10⁻⁸`). -/
theorem abs_rangeCosSum_rest_sub_integral_le_short {k r y : ℕ} {σ τ : ℝ}
    (hkr : 20 ≤ (r : ℝ) + k) (hτ : 0 ≤ τ) (hτ2 : τ ≤ 2 * Real.exp (-20)) (hσ : 0 ≤ σ)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) :
    |rangeCosSum (⌊blockScale k r⌋₊ + 1) y σ τ
        - ∫ u in Real.exp ((r : ℝ) + k)..restU k r y,
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
      ≤ 3.24 / 10 ^ 6 := by
  set R := restTop k r y with hRdef
  have hrR : r ≤ R := le_restTop k r y
  have hrR' : (r : ℝ) ≤ R := by exact_mod_cast hrR
  have hcut : ⌊blockScale k r⌋₊ + 1 ≤ ⌊blockScale k R⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_mono (blockScale_mono _ hrR))
  rw [rangeCosSum_split hcut (cut_restTop_le hyr), rangeCosSum_cut_eq k hrR]
  have hA := (abs_sum_blockCosSum_sub_integral_le_two_regime (σ := σ) (θ := k) hrR hτ hσ
    (by linarith)).trans (blockCosTelErr_le_numeral hkr hτ hτ2)
  have hB := abs_rangeCosSum_top_sub_integral_le_floor hkr hτ hτ2 hσ hyr
  have h1 : Real.exp ((r : ℝ) + k) ≤ Real.exp ((R : ℝ) + k) := Real.exp_le_exp.2 (by linarith)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_cos_mul_exp_div (τ := τ) (σ := σ) (Real.exp_pos ((r : ℝ) + k)) h1)
    (intervalIntegrable_cos_mul_exp_div (τ := τ) (σ := σ) (Real.exp_pos ((R : ℝ) + k))
      (exp_restTop_le_restU k r y))
  rw [← hsplit]
  have htri := abs_add_le
    (∑ m ∈ Finset.Ico r R, blockCosSum k σ τ m - ∫ u in Real.exp ((r : ℝ) + k)..Real.exp
      ((R : ℝ) + k), Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
    (rangeCosSum (⌊blockScale k R⌋₊ + 1) y σ τ - ∫ u in Real.exp ((R : ℝ) + k)..restU k r y,
      Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
  have e : (∑ m ∈ Finset.Ico r R, blockCosSum k σ τ m
        + rangeCosSum (⌊blockScale k R⌋₊ + 1) y σ τ)
      - ((∫ u in Real.exp ((r : ℝ) + k)..Real.exp ((R : ℝ) + k),
          Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
        + ∫ u in Real.exp ((R : ℝ) + k)..restU k r y,
          Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
      = (∑ m ∈ Finset.Ico r R, blockCosSum k σ τ m - ∫ u in Real.exp ((r : ℝ) + k)..Real.exp
          ((R : ℝ) + k), Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
        + (rangeCosSum (⌊blockScale k R⌋₊ + 1) y σ τ - ∫ u in Real.exp ((R : ℝ) + k)..restU k r y,
          Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u) := by ring
  rw [e]
  linarith

/-! ### The rest's exponent -/

/-- **The rest's pair-mass exponent on short tubes**: for `k ≥ 20`, `r ≥ 35`, `σ ≥ 0`, heights in
the window and `y ≥ c_r`,
`2(C(h₁-h₂) + C(h₁+h₂)) + 12Q ≤ 2∫_{e^{r+k}}^U cos(|h₁ - h₂|u)e^{-2σu}/u du + 10⁻⁴` over the primes
of `[c_r, y)`, `U = RMF.restU k r y` — `RMF.rest_exponent_le` with both frequencies' errors
`3.24·10⁻⁶` (`RMF.abs_rangeCosSum_rest_sub_integral_le_short`) in place of the PNT's; in all
`4·3.24·10⁻⁶ + 2e^{1-r} + 2·10⁻²⁰ ≤ 1.3·10⁻⁵`. -/
theorem rest_exponent_le_short {k r y : ℕ} {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hr : 35 ≤ r)
    (hσ : 0 ≤ σ) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) :
    2 * (rangeCosSum (⌊blockScale k r⌋₊ + 1) y σ (h₁ - h₂)
        + rangeCosSum (⌊blockScale k r⌋₊ + 1) y σ (h₁ + h₂))
      + 12 * rangeSqSum (⌊blockScale k r⌋₊ + 1) y σ
      ≤ 2 * (∫ u in Real.exp ((r : ℝ) + k)..restU k r y,
          Real.cos (|h₁ - h₂| * u) * Real.exp (-(2 * σ) * u) / u) + 1 / 10 ^ 4 := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hr' : (35 : ℝ) ≤ r := by exact_mod_cast hr
  have hkr : 20 ≤ (r : ℝ) + k := by linarith
  obtain ⟨hS0, hS2⟩ := add_mem_of_mem_halfWindow_floor hk hh₁ hh₂
  have hSpos : 0 < h₁ + h₂ := by
    obtain ⟨a₁, -⟩ := hh₁
    obtain ⟨a₂, -⟩ := hh₂
    linarith [Real.exp_pos (-((k : ℝ) + 1))]
  have hD2 : |h₁ - h₂| ≤ 2 * Real.exp (-20) := by
    obtain ⟨a₁, b₁⟩ := hh₁
    obtain ⟨a₂, b₂⟩ := hh₂
    have e1 : Real.exp (-(k : ℝ)) ≤ Real.exp (-20) := Real.exp_le_exp.2 (by linarith)
    have e2 := Real.exp_pos (-((k : ℝ) + 1))
    rw [abs_le]
    constructor <;> linarith
  -- the difference frequency
  have hD := abs_rangeCosSum_rest_sub_integral_le_short (y := y) (σ := σ) (τ := |h₁ - h₂|) hkr
    (abs_nonneg _) hD2 hσ hyr
  rw [rangeCosSum_abs] at hD
  -- the sum frequency
  have hS := abs_rangeCosSum_rest_sub_integral_le_short (y := y) (σ := σ) (τ := h₁ + h₂) hkr hS0
    hS2 hσ hyr
  have hSint := abs_integral_cos_mul_exp_div_le (σ := σ) hSpos hσ (Real.exp_pos ((r : ℝ) + k))
    (exp_le_restU k r y)
  have hSe := two_div_sum_freq_le (r := r) hh₁ hh₂
  -- the quadratic remainder
  have hQ := rangeSqSum_rest_le (r := r) (y := y) hk hσ
  -- the sum frequency's integral is at most `e^{1-r} ≤ e^{-20}`
  have hr1 : Real.exp (1 - (r : ℝ)) ≤ Real.exp (-20) := Real.exp_le_exp.2 (by linarith)
  have he20 := exp_neg_twenty_le_numeral
  have hD' := (abs_le.1 hD).2
  have hS' := (abs_le.1 hS).2
  have hSint' := (abs_le.1 hSint).2
  linarith

section Extension

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The rest multiplies in, on short tubes**: `RMF.integral_hp1Tube_inter_rest_le` for `r ≥ 35`
with the exponent's `10⁻¹⁹` replaced by `10⁻⁴` (`RMF.rest_exponent_le_short`): from a bound
`E[1_{H₁∩H₂}W_{[c₀,c_r)}] ≤ E‖F_r(s₁)‖²E‖F_r(s₂)‖²·K` over the blocks `m < r`,
`E[1_{H₁∩H₂}W_{[c₀,y)}] ≤ E‖F_y(s₁)‖²E‖F_y(s₂)‖²·K·e^{2∫_A^U cos(|h₁-h₂|u)e^{-2σu}/u du + 10⁻⁴}`,
`A = e^{r+k}`, `U = RMF.restU k r y`. -/
theorem integral_hp1Tube_inter_rest_le_short (hX : IsRademacherPrimeValues X μ) {k r y : ℕ}
    {σ h₁ h₂ K : ℝ} (hk : 20 ≤ k) (hr : 35 ≤ r) (hσ : 0 ≤ σ) (hh₁ : h₁ ∈ halfWindow k)
    (hh₂ : h₂ ∈ halfWindow k) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y)
    (hK : ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ) * K) :
    ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * K * Real.exp (2 * (∫ u in Real.exp ((r : ℝ) + k)..restU k r y,
            Real.cos (|h₁ - h₂| * u) * Real.exp (-(2 * σ) * u) / u) + 1 / 10 ^ 4) := by
  classical
  haveI := hX.isProbabilityMeasure
  have hc0r : ⌊blockScale k 0⌋₊ + 1 ≤ ⌊blockScale k r⌋₊ + 1 := cut_mono k (Nat.zero_le r)
  set H : Set Ω := hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂ with hHdef
  have hHa : MeasurableSet[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)] H :=
    (measurableSet_primeAlgebra_hp1Tube y k le_rfl σ h₁).inter
      (measurableSet_primeAlgebra_hp1Tube y k le_rfl σ h₂)
  have hH : MeasurableSet H := measurableSet_of_primeAlgebra hX hHa
  set W : ℕ → ℕ → Ω → ℝ := fun a b ω =>
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h₁) ω‖
        ^ 2
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
        (shiftLine σ h₂) ω‖ ^ 2 with hWdef
  have hWa : ∀ a b, Measurable[primeAlgebra X a b] (W a b) := fun a b =>
    (measurable_primeAlgebra_normSq a b _).mul (measurable_primeAlgebra_normSq a b _)
  have hind : IndepFun (H.indicator (W (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)))
      (W (⌊blockScale k r⌋₊ + 1) y) μ :=
    indepFun_of_primeAlgebra hX ((hWa _ _).indicator hHa) (hWa _ _)
  have hsplit : ∀ ω, H.indicator (W (⌊blockScale k 0⌋₊ + 1) y) ω
      = H.indicator (W (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)) ω
        * W (⌊blockScale k r⌋₊ + 1) y ω := by
    intro ω
    by_cases hω : ω ∈ H
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      simp only [hWdef]
      rw [normSq_randomEulerProductIco_split hc0r hyr (shiftLine σ h₁) ω,
        normSq_randomEulerProductIco_split hc0r hyr (shiftLine σ h₂) ω]
      ring
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
  have hfac : ∫ ω, H.indicator (W (⌊blockScale k 0⌋₊ + 1) y) ω ∂μ
      = (∫ ω, H.indicator (W (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)) ω ∂μ)
        * ∫ ω, W (⌊blockScale k r⌋₊ + 1) y ω ∂μ := by
    rw [integral_congr_ae (ae_of_all _ hsplit)]
    exact hind.integral_fun_mul_eq_mul_integral
      (((hWa _ _).indicator hHa).mono (primeAlgebra_le hX _ _) le_rfl).aestronglyMeasurable
      ((hWa _ _).mono (primeAlgebra_le hX _ _) le_rfl).aestronglyMeasurable
  set T : ℝ := 2 * (∫ u in Real.exp ((r : ℝ) + k)..restU k r y,
      Real.cos (|h₁ - h₂| * u) * Real.exp (-(2 * σ) * u) / u) + 1 / 10 ^ 4 with hTdef
  have hmass := integral_normSq_mul_normSq_Ico_le hX (⌊blockScale k r⌋₊ + 1) y
    (h₁ := h₁) (h₂ := h₂) hσ
  have hexp := rest_exponent_le_short hk hr hσ hh₁ hh₂ hyr
  have hmass' : ∫ ω, W (⌊blockScale k r⌋₊ + 1) y ω ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k r⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k r⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * Real.exp T :=
    hmass.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp)
      (mul_nonneg (integral_nonneg fun ω => by positivity)
        (integral_nonneg fun ω => by positivity)))
  have hsq₁ := integral_normSq_Ico_split hX hc0r hyr (shiftLine σ h₁)
  have hsq₂ := integral_normSq_Ico_split hX hc0r hyr (shiftLine σ h₂)
  rw [← integral_indicator hH] at hK ⊢
  change ∫ ω, H.indicator (W (⌊blockScale k 0⌋₊ + 1) y) ω ∂μ ≤ _
  change ∫ ω, H.indicator (W (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)) ω ∂μ ≤ _ at hK
  rw [hfac, hsq₁, hsq₂]
  have hA0 : 0 ≤ ∫ ω, H.indicator (W (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)) ω ∂μ :=
    integral_nonneg fun ω => Set.indicator_nonneg (fun ω _ => by simp only [hWdef]; positivity) ω
  have hB0 : 0 ≤ ∫ ω, W (⌊blockScale k r⌋₊ + 1) y ω ∂μ :=
    integral_nonneg fun ω => by simp only [hWdef]; positivity
  calc (∫ ω, H.indicator (W (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)) ω ∂μ)
        * ∫ ω, W (⌊blockScale k r⌋₊ + 1) y ω ∂μ
      ≤ ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ) * K)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k r⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k r⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
          * Real.exp T) :=
        mul_le_mul hK hmass' hB0 (le_trans hA0 hK)
    _ = _ := by ring

end Extension

end RMF
