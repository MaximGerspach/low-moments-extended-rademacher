/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherRestrictedSecondMoment.Assembly
import RMF.Probability.RestrictedSecondMoment

/-!
# Harper's Key Proposition 5 at his numeric data, for the Rademacher function

The Rademacher twin of `Probability/RestrictedSecondMoment.lean`, following Harper's §5.3: the four
range estimates (crude split, crude top, far, middle) at `θ = RMF.harperTheta B x`,
`N = RMF.harperN B x`, `b = RMF.harperBarrierTop B V' x` and `σ = 4V/\log x`, and
`RMF.integral_sq_setIntegral_indicator_normSq_harper_data_le_rademacher`, which assembles them.
`V'` ranges over `[V, e^3V]`: the Rademacher numerator's barrier top is three blocks below the
Steinhaus one, and three blocks down is `V ↦ e^3V`.  The law-free lemmas about Harper's data are
imported from the Steinhaus file.

The heights are `T ⊆ [1/3, 1/2]`, Harper's restriction in the Rademacher case, where the Steinhaus
chain has `T ⊆ [-1/2, 1/2]`: without rotation invariance the two-point moment sees the sum
frequency `t+u` as well as the difference, and the restriction keeps it away from zero.  The range
theorems assume `t, u ∈ [1/3, 1/2]`; the assembled statement assumes only `T ⊆ [1/3, 1/2]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}

/-! ### The instantiation at Harper's numeric data

The law-free lemmas of `Probability/RestrictedSecondMoment.lean` (`RMF.harperShift`,
`RMF.harperTruncation`, the barrier-top bounds, the reshapes, the constants) are used directly;
what follows is specific to the Rademacher function. -/

/-- **Probability Lemma 1's level threshold, at a general slope.**  The general form of
`RMF.result1Threshold_le_shiftLevel`.

`RMF.harperShiftFloor` is defined by dividing by `1 + RMF.blockSlope 125`, so a *larger* slope only
makes the threshold easier — which is why the chain carries `blockSlope 125 ≤ Bs` and not merely
`20 ≤ Bs`. -/
lemma result1Threshold_le_shiftedHeight {a Bs : ℝ} (ha : 0 ≤ a)
    (hBs : blockSlope 125 ≤ Bs) {r : ℕ} (hr : harperShiftFloor ≤ r) :
    max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ shiftedHeight a Bs harperHf r := by
  have hs : (0 : ℝ) < blockSlope 125 := blockSlope_pos 125
  have hden : (0 : ℝ) < 1 + blockSlope 125 := by linarith
  have hceil : max 1 (result1Threshold (1 / 18) (9 / 2)) / (1 + blockSlope 125) ≤ (r : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast hr
  rw [div_le_iff₀ hden] at hceil
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have h1 : (0 : ℝ) ≤ |harperHf r| := abs_nonneg _
  have h2 : (0 : ℝ) ≤ 10 * Real.log (1 + (r : ℝ)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + (r : ℝ) by linarith)
    linarith
  rw [shiftedHeight]
  nlinarith [hceil, mul_nonneg (sub_nonneg.2 hBs) hr0]

/-- **The crude range's first regime, at Harper's numeric data, for the Rademacher function.**
The twin of `RMF.exists_setIntegral_normSq_pair_crude_split_harper_data_le`, with Harper's heights
`t, u ∈ [1/3, 1/2]` added; no tilt bound and no `η` enter, since no barrier probability does.  The
regime is `\log 2 + 2θ + 2 ≤ \log(1/τ) ≤ b + θ - 2`, `τ = |t-u|`; with `1/τ ≤ L_c/e^2` as its
upper end instead, a band of `τ` would belong to neither regime. -/
theorem exists_setIntegral_normSq_pair_crude_split_harper_data_le_rademacher (Bs : ℝ)
    {Ω' : Type*} [MeasurableSpace Ω'] :
    ∃ KQ CP : ℝ, 0 < KQ ∧ 0 < CP ∧
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
      ∀ (B : ℕ) (V x σ a t u : ℝ),
      124 ≤ B → 1 ≤ V → 1 < x →
      (B : ℝ) + 2 ≤ Real.log (Real.log x) →
      ⌊Real.log V⌋₊ + 3 ≤ harperN B x →
      0 < σ → σ ≤ 1 / 2 → 1 ≤ σ * Real.log x → σ * Real.log x ≤ 4 * V →
      0 < |t - u| → |t - u| ≤ 1 →
      1 / 3 ≤ t → t ≤ 1 / 2 → 1 / 3 ≤ u → u ≤ 1 / 2 →
      Real.log 2 + 2 * harperTheta B x + 2 ≤ Real.log (1 / |t - u|) →
      Real.log (1 / |t - u|)
        ≤ ((harperBarrierTop B V x : ℕ) : ℝ) + harperTheta B x - 2 →
      Real.log 2 + harperTheta B x - 2 ≤ ((harperBarrierTop B V x : ℕ) : ℝ) →
      (B : ℝ) + Real.log V + 8 ≤ 2 / 3 * Real.log (Real.log x) →
      (∫ ω in barrierEventPair (blockPairAdd (harperTheta B x) (shiftLine σ t)
          (shiftLine σ u) Y) (harperBarrierTop B V x)
          (fun j => -a - Bs * j) (fun j => a + j + harperHf j)
          (fun j => -a - Bs * j) (fun j => a + j + harperHf j),
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ (4 * Real.exp 1 ^ 2 * Real.exp (a - harperTheta B x)) ^ 2 * KQ * CP
            * bottomSupConst ((B : ℝ) + 2) / σ ^ 2
            * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 4)) := by
  obtain ⟨KQ, CP, hKQ, hCP, hsrc⟩ :=
    exists_setIntegral_normSq_pair_crude_split_harper_le_rademacher Bs (Ω' := Ω')
  refine ⟨KQ, CP, hKQ, hCP, ?_⟩
  intro Y ν hY B V x σ a t u hB hV hx1 hx hle hσ0 hσhalf hσx hσ4 hτ0 hτ1 htl htu hul
    huu hsmall hreg hbθ hΛ1
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hθ125 : (125 : ℝ) ≤ harperTheta B x := harperTheta_ge hB hΛ0
  have hθ0 : (0 : ℝ) ≤ harperTheta B x := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- `b ≥ 2`, from the boundary condition and `θ ≥ 125`
  have hb2R : (2 : ℝ) ≤ ((harperBarrierTop B V x : ℕ) : ℝ) := by linarith
  have hb2 : 2 ≤ harperBarrierTop B V x := by exact_mod_cast hb2R
  -- the split index, and the two spare blocks
  have hsp : ⌊Real.log (1 / |t - u|) - harperTheta B x⌋₊ + 2 ≤ harperBarrierTop B V x :=
    floor_log_one_div_sub_theta_add_two_le_of_le hb2 hreg
  have hfloor : ⌊Real.log (1 / |t - u|) - harperTheta B x⌋₊ ≤ harperBarrierTop B V x := by
    omega
  have hsplit : splitIndex (harperTheta B x) (harperBarrierTop B V x) (t - u)
      = ⌊Real.log (1 / |t - u|) - harperTheta B x⌋₊ := by
    rw [splitIndex, min_eq_right hfloor]
  have hb1 : 1 ≤ harperBarrierTop B V x := by omega
  have h1split : 1 ≤ splitIndex (harperTheta B x) (harperBarrierTop B V x) (t - u) :=
    one_le_splitIndex hθ0 hb1 hsmall
  have hspb : splitIndex (harperTheta B x) (harperBarrierTop B V x) (t - u) + 2
      ≤ harperBarrierTop B V x := by rw [hsplit]; exact hsp
  -- `\log(2/τ) ≤ 2b`, from the boundary and `\log 2 + θ - 2 ≤ b`
  have hmb : Real.log (2 / |t - u|) ≤ 2 * ((harperBarrierTop B V x : ℕ) : ℝ) := by
    rw [log_two_div_eq hτ0]
    linarith
  -- the drop, which is what `hNM` reads
  have hdrop : σ * Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x)) ≤ 1 := by
    have he3 : (4 : ℝ) ≤ Real.exp 3 := by
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]
        norm_num
      have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hpow : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he1.le 3
      rw [h3]
      linarith [hpow, (by norm_num : (4 : ℝ) ≤ (2.7 : ℝ) ^ 3)]
    refine le_trans (sigma_mul_log_blockScale_barrierTop_le hV hx1 hx hle hσ4) ?_
    rw [div_le_one (Real.exp_pos 3)]
    exact he3
  exact hsrc Y ν hY (harperTheta B x) σ a ((B : ℝ) + 2) t u (harperN B x)
    (harperBarrierTop B V x)
    hθ125 (harperTheta_lt B x).le hσ0 hσhalf (harperBarrierTop_le B V x)
    hspb h1split hfloor hτ0 hτ1 htl htu hul huu hsmall hmb
    (exp_splitIndex_add_two_le_of_le hσ0 hspb hdrop)
    (one_div_sigma_le_log_blockScale_harperN_succ hx1 hx hσ0 hσx)

/-- **The crude range's second regime, at Harper's numeric data, for the Rademacher function.**
The twin of `RMF.exists_setIntegral_normSq_pair_crude_top_harper_data_le`, with Harper's heights
added.  The bound has the `C·L_b³/n_b⁴` shape `RMF.crude_top_le_min` consumes, and there is no
hypothesis on `τ`, so this regime covers the band `L_c/e² ≤ 1/τ` the first cannot reach.  The
ratio `\log M/\log⌊x_b⌋` stays in the bound; it does not depend on `t` or `u`. -/
theorem exists_setIntegral_normSq_pair_crude_top_harper_data_le_rademacher (Bs : ℝ)
    {Ω' : Type*} [MeasurableSpace Ω'] :
    ∃ KQ CP : ℝ, 0 < KQ ∧ 0 < CP ∧
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
      ∀ (B : ℕ) (V x σ a t u : ℝ),
      124 ≤ B → 1 ≤ V → 1 < x → 3 ≤ x →
      (B : ℝ) + 2 ≤ Real.log (Real.log x) →
      ⌊Real.log V⌋₊ + 3 ≤ harperN B x →
      1 ≤ harperBarrierTop B V x →
      0 < σ → σ * Real.log x ≤ 4 * V → 1 ≤ σ * Real.log x →
      1 / 3 ≤ t → t ≤ 1 / 2 → 1 / 3 ≤ u → u ≤ 1 / 2 →
      (∫ ω in barrierEventPair (blockPairAdd (harperTheta B x) (shiftLine σ t)
          (shiftLine σ u) Y) (harperBarrierTop B V x)
          (fun j => -a - Bs * j) (fun j => a + j + harperHf j)
          (fun j => -a - Bs * j) (fun j => a + j + harperHf j),
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ Real.exp (2 * a) * Real.exp (-(2 * harperTheta B x))
            * (KQ * (Real.log ((harperTruncation σ : ℕ) : ℝ)
                / Real.log ((⌊blockScale (harperTheta B x) (harperBarrierTop B V x)⌋₊ : ℕ) : ℝ))
                  ^ 4)
            * CP * bottomSupConst ((B : ℝ) + 2)
            * Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x)) ^ 3
            / ((harperBarrierTop B V x : ℕ) : ℝ) ^ 4 := by
  obtain ⟨KQ, CP, hKQ, hCP, hsrc⟩ :=
    exists_setIntegral_normSq_pair_crude_top_harper_le_rademacher Bs (Ω' := Ω')
  refine ⟨KQ, CP, hKQ, hCP, ?_⟩
  intro Y ν hY B V x σ a t u hB hV hx1 hx3 hx hle hb1 hσ0 hσ hσx htl htu hul huu
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hθ125 : (125 : ℝ) ≤ harperTheta B x := harperTheta_ge hB hΛ0
  have hθ0 : (0 : ℝ) ≤ harperTheta B x := by linarith
  have hsrc' := hsrc Y ν hY (harperTheta B x) σ a ((B : ℝ) + 2) t u (harperN B x)
    (harperBarrierTop B V x) (harperTruncation σ)
    hθ0 (harperTheta_lt B x).le hσ0.le hb1 (harperBarrierTop_le B V x)
    (four_hundred_le_floor_blockScale (by linarith) _)
    (floor_blockScale_barrierTop_le_harperTruncation hV hx1 hx hle hσ0 hσ)
    (harperTruncation_le_floor_blockScale_harperN_succ hx1 hx3 hx hσ0 hσx)
    (one_le_two_mul_sigma_mul_log_harperTruncation hσ0) htl htu hul huu
  refine le_trans hsrc' (le_of_eq ?_)
  rw [exp_barrier_top_sq_eq a (harperTheta B x) hb1]
  ring

/-! ### `hosc` at Harper's heights

The general far and middle ranges assume two oscillation bounds `hosc` on the cosine sums at the
doubled height `τ = 2t`; at Harper's heights they are proved.  For `t ∈ [1/3, 1/2]` we have
`τ ∈ [2/3, 1]`, so the condition `τ² ≤ e^{m+θ}` of
`RMF.exists_abs_sum_cos_primeBlockSub_rpow_le` holds, and `1/τ ≤ 3/2` makes its bound
`K/(τe^{m+θ})` geometric in `m` with an absolute constant. -/

/-- **`hosc` at Harper's heights**: `|∑_{p ∈ P_m} \cos(2t\log p)\,p^{-1-2σ}| ≤ (2/3)K_d e^{-m}` for
`t ∈ [1/3, 1/2]`, `θ ≥ 0` and `|σ|\log x_{m+1} ≤ 1`, with `P_m = RMF.primeBlockSub θ m` and `K_d`
absolute.  At `τ = 2t ≥ 2/3`, `RMF.exists_abs_sum_cos_primeBlockSub_rpow_le` gives
`K/(τe^{m+θ}) ≤ (3K/2)e^{-m}`, so `K_d = 9K/4`. -/
theorem exists_abs_sum_cos_primeBlockSub_harper_le :
    ∃ Kd > 0, ∀ (t σ θ : ℝ) (m : ℕ), 1 / 3 ≤ t → t ≤ 1 / 2 → 0 ≤ θ →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 →
      |∑ p ∈ primeBlockSub θ m,
          Real.cos (2 * t * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ))) := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_sum_cos_primeBlockSub_rpow_le
  refine ⟨9 / 4 * K, by positivity, fun t σ θ m htl htu hθ hσ => ?_⟩
  have hτ0 : (0 : ℝ) < 2 * t := by linarith
  have hem0 : (0 : ℝ) < Real.exp (m : ℝ) := Real.exp_pos _
  have heθ0 : (0 : ℝ) < Real.exp θ := Real.exp_pos _
  have heθ : (1 : ℝ) ≤ Real.exp θ := Real.one_le_exp hθ
  -- the height condition `τ² ≤ e^{m+θ}`, free at `t ≤ 1/2`
  have hτ2 : (2 * t) ^ 2 ≤ Real.exp ((m : ℝ) + θ) := by
    have h1 : (1 : ℝ) ≤ Real.exp ((m : ℝ) + θ) :=
      Real.one_le_exp (by positivity)
    nlinarith
  refine le_trans (hK (2 * t) σ θ m hτ0 hθ hτ2 hσ) ?_
  -- `K/(τ e^{m+θ}) ≤ (3K/2)e^{-m}`, since `τ ≥ 2/3` and `e^θ ≥ 1`
  have h3teθ : (1 : ℝ) ≤ 3 * t * Real.exp θ := by nlinarith
  have hrw : (2 : ℝ) / 3 * (9 / 4 * K * Real.exp (-(m : ℝ)))
      = 3 / 2 * K / Real.exp (m : ℝ) := by
    rw [Real.exp_neg]
    field_simp
    ring
  rw [hrw, Real.exp_add, div_le_div_iff₀ (by positivity) hem0,
    show 3 / 2 * K * (2 * t * (Real.exp (m : ℝ) * Real.exp θ))
      = K * Real.exp (m : ℝ) * (3 * t * Real.exp θ) from by ring]
  exact le_mul_of_one_le_right (by positivity) h3teθ

/-- **`e^3 \ge 10`.**  The whole reason three blocks of drop are enough to turn the Steinhaus
tilt bound `\le 1` into the Rademacher `\le 1/10`.  Two would not: `e^{-2} = 0.135`. -/
lemma ten_le_exp_three : (10 : ℝ) ≤ Real.exp 3 := by
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7) he1.le 3]

/-- **The Rademacher drop covers `40V`**: `4V ≤ e^{D+3}/10` for `D = RMF.harperD V`.
`RMF.harperD V` is built so that `4V ≤ e^D`, and `e^3 ≥ 10` (`RMF.ten_le_exp_three`) covers the
Rademacher tilt bound `≤ 1/10`. -/
lemma four_mul_le_one_div_ten_mul_exp_harperD_add_three (V : ℝ) :
    4 * V ≤ 1 / 10 * Real.exp (((harperD V + 3 : ℕ) : ℝ)) := by
  have hexp3 : (10 : ℝ) ≤ Real.exp 3 := ten_le_exp_three
  have h4V : 4 * V ≤ Real.exp ((harperD V : ℕ) : ℝ) :=
    le_trans (le_max_left _ _) (le_exp_harperD V)
  have hsplit : Real.exp (((harperD V + 3 : ℕ) : ℝ))
      = Real.exp ((harperD V : ℕ) : ℝ) * Real.exp 3 := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hpos : (0 : ℝ) < Real.exp ((harperD V : ℕ) : ℝ) := Real.exp_pos _
  rw [hsplit]
  nlinarith

/-- **The far range, at Harper's numeric data, for the Rademacher function.**  The twin of
`RMF.exists_setIntegral_normSq_pair_far_harper_data_le`, with Harper's heights `t, u ∈ [1/3, 1/2]`
added.  The drop is `RMF.harperD V + 3` at `η = 1/10`, and both `hosc` are proved inside
(`RMF.exists_abs_sum_cos_primeBlockSub_harper_le`, with `RMF.sigma_le_of_drop` for its tilt
hypothesis), so no oscillation hypothesis appears.  `Cst` depends only on `κ` and `Bs`. -/
theorem exists_setIntegral_normSq_pair_far_harper_data_le_rademacher (κ Bs : ℝ) (hκ : 0 ≤ κ)
    (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'],
        ∃ K > 0, ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ : ℝ,
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (σ a q m x τ0 t u : ℝ),
          1 < x → Λ₀ ≤ Real.log (Real.log x) →
          0 < σ → σ ≤ 1 / 2 → σ * Real.log x ≤ 4 * V → 1 ≤ σ * Real.log x →
          0 < |t - u| → |t - u| ≤ 1 →
          1 / 3 ≤ t → t ≤ 1 / 2 → 1 / 3 ≤ u → u ≤ 1 / 2 →
          Real.log (1 / |t - u|) ≤ Real.log (Real.log x) / 3 →
          1 ≤ a → 0 ≤ q → q ≤ 1 →
          0 ≤ m → m ≤ Real.sqrt (Real.log (Real.log x)) → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / |t - u|) →
          1 / |t - u| ≤ τ0 → 2 * τ0 + 7 ≤ 1 / σ →
            (∫ ω in barrierEventPair (blockPairAdd (harperTheta B x) (shiftLine σ t)
                (shiftLine σ u) Y) (harperBarrierTop B V x)
                (fun j => -a - Bs * j) (fun j => a + j + harperHf j)
                (fun j => -a - Bs * j) (fun j => a + j + harperHf j),
                ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                    (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2
                  * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                      (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ u) ω‖ ^ 2 ∂ν)
              ≤ Cst * K * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4
                  * ((1 / σ) ^ 2
                      / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ 2)
                  * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) := by
  obtain ⟨Kd, hKd0, hoscsrc⟩ := exists_abs_sum_cos_primeBlockSub_harper_le
  obtain ⟨Cst, hCst, n₀, θ₀, hsrc⟩ :=
    exists_setIntegral_normSq_pair_far_harper_le_rademacher κ Kd Bs hκ hKd0.le hBs
  refine ⟨Cst, hCst, ⌈θ₀⌉₊ + 124, ?_⟩
  intro B hB Ω' _
  obtain ⟨K, hK, hfar⟩ := hsrc Ω'
  refine ⟨K, hK, ?_⟩
  intro V hV
  refine ⟨12 * harperSlack B V + 12 * Real.log V + 72 + 3 * (n₀ : ℝ) + ((B : ℝ) + 2), ?_⟩
  intro Y ν hY σ a q m x τ0 t u hx1 hΛ₀ hσ0 hσhalf hσ4 hσx hτ0 hτ1 htl htu hul huu hτL
    ha hq0 hq1 hm0 hmΛ hmq ham hτ0le hτ0σ
  -- the pieces of `Λ₀`
  have hS5 : (5 : ℝ) ≤ harperSlack B V := le_harperSlack (by linarith)
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hn₀0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg n₀
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hx : (B : ℝ) + 2 ≤ Real.log (Real.log x) := by linarith
  have hΛ12 : 12 * harperSlack B V ≤ Real.log (Real.log x) := by linarith
  have hΛ3 : 3 * harperSlack B V + 3 * Real.log V + 21 ≤ Real.log (Real.log x) := by linarith
  have hΛ6 : (B : ℝ) + Real.log V + 6 ≤ Real.log (Real.log x) := by
    have hBS : (B : ℝ) + 5 ≤ harperSlack B V := by
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hlog4 : (0 : ℝ) ≤ Real.log (4 * V) := Real.log_nonneg (by linarith)
      rw [harperSlack]
      linarith
    linarith
  have hle := floor_log_add_three_le_harperN hV hx hΛ6
  -- the count at the barrier top
  obtain ⟨hnat, hcore⟩ := harper_block_count_barrierTop hV hτ0 hτ1 hτL hle hΛ12 hΛ3
  have hd : harperD V ≤ harperBarrierTop B V x := by omega
  have hr : harperR |t - u| ≤ harperBarrierTop B V x - harperD V := by omega
  have hcast : ((harperBarrierTop B V x - harperD V - harperR |t - u| : ℕ) : ℝ)
      = ((harperBarrierTop B V x : ℕ) : ℝ) - (harperD V : ℝ) - (harperR |t - u| : ℝ) := by
    rw [Nat.cast_sub hr, Nat.cast_sub hd]
  -- the drop is `harperD V + 3`, not `harperD V`: the Rademacher tilt bound is `≤ 1/10`, so the
  -- drop has to cover `40V`, and three more blocks do it because `e³ > 10`
  have hd3nat : harperR |t - u| + (harperD V + 3) + 4 ≤ harperBarrierTop B V x := by
    have hR : ((harperR |t - u| + harperD V + 7 : ℕ) : ℝ)
        ≤ ((harperBarrierTop B V x : ℕ) : ℝ) := by
      push_cast
      linarith
    have hR' : harperR |t - u| + harperD V + 7 ≤ harperBarrierTop B V x := by exact_mod_cast hR
    omega
  have hcast3 : ((harperBarrierTop B V x - (harperD V + 3) - harperR |t - u| : ℕ) : ℝ)
      = ((harperBarrierTop B V x : ℕ) : ℝ) - (harperD V : ℝ) - 3 - (harperR |t - u| : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hn₀le : n₀ ≤ harperBarrierTop B V x - (harperD V + 3) - harperR |t - u| := by
    have hR : ((n₀ : ℕ) : ℝ)
        ≤ ((harperBarrierTop B V x - (harperD V + 3) - harperR |t - u| : ℕ) : ℝ) := by
      rw [hcast3]
      linarith
    exact_mod_cast hR
  have hn4 : Real.log (Real.log x)
      ≤ 4 * ((harperBarrierTop B V x - (harperD V + 3) - harperR |t - u| : ℕ) : ℝ) := by
    rw [hcast3]
    linarith
  -- `4V ≤ (1/10)e^{D+3}`, because `e³ > 10`
  have h4V : 4 * V ≤ Real.exp ((harperD V : ℕ) : ℝ) :=
    le_trans (le_max_left _ _) (le_exp_harperD V)
  have hdrop : 4 * V ≤ 1 / 10 * Real.exp (((harperD V + 3 : ℕ) : ℝ)) :=
    four_mul_le_one_div_ten_mul_exp_harperD_add_three V
  -- the tilt at the barrier top, in the `≤ 4V` form the Rademacher chain reads
  have hσtop : |σ| * Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x + 1))
      ≤ 4 * V := by
    refine le_trans
      (abs_sigma_mul_log_blockScale_barrierTop_succ_le_one hV hx1 hx hle hσ0.le hσ4) ?_
    linarith
  -- `hosc`, closed rather than threaded: `exists_abs_sum_cos_primeBlockSub_harper_le` needs the
  -- tilt bound at each block, and `sigma_le_of_drop` supplies it from the drop
  have hΛ0R : (0 : ℝ) ≤ Real.log (Real.log x) :=
    le_trans (add_nonneg hB0 (by norm_num)) hx
  have hθ0 : (0 : ℝ) ≤ harperTheta B x :=
    le_trans (add_nonneg hB0 zero_le_one) (le_harperTheta hΛ0R)
  have hosc : ∀ (w : ℝ), 1 / 3 ≤ w → w ≤ 1 / 2 →
      ∀ mm, mm < harperBarrierTop B V x - (harperD V + 3) →
        |∑ p ∈ primeBlockSub (harperTheta B x) mm,
            Real.cos (2 * w * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
          ≤ 2 / 3 * (Kd * Real.exp (-(mm : ℝ))) := by
    intro w hwl hwu mm hmm
    refine hoscsrc w σ (harperTheta B x) mm hwl hwu hθ0 ?_
    have hDle : harperD V ≤ harperBarrierTop B V x - mm := by omega
    have hDleR : ((harperD V : ℕ) : ℝ)
        ≤ ((harperBarrierTop B V x - mm : ℕ) : ℝ) := by exact_mod_cast hDle
    have hK : 4 * V ≤ 1 * Real.exp (((harperBarrierTop B V x - mm : ℕ) : ℝ)) := by
      rw [one_mul]
      exact le_trans h4V (Real.exp_le_exp.2 hDleR)
    have h := sigma_le_of_drop (θ := harperTheta B x) (σ := σ) hK (by omega) hσtop
    rwa [show harperBarrierTop B V x - (harperBarrierTop B V x - mm) = mm from by omega] at h
  -- `θ₀ ≤ θ`
  have hθ₀ : θ₀ ≤ harperTheta B x := by
    have hceil : θ₀ ≤ ((⌈θ₀⌉₊ : ℕ) : ℝ) := Nat.le_ceil θ₀
    have hBc : ((⌈θ₀⌉₊ : ℕ) : ℝ) + 124 ≤ (B : ℝ) := by exact_mod_cast hB
    have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
    linarith [le_harperTheta (B := B) (x := x) hΛ0]
  have hΛ1 : (1 : ℝ) ≤ Real.log (Real.log x) := by linarith
  exact hfar Y ν hY (harperTheta B x) σ (1 / 10) a (Real.log (Real.log x)) q m V τ0
    (harperN B x) (harperBarrierTop B V x) (harperD V + 3) t u hθ₀ hσ0 hσhalf
    (harperBarrierTop_le B V x) hd3nat hn₀le (by norm_num) le_rfl hdrop hσtop
    htl htu hul huu hτ0 hτ1 (hosc t htl htu) (hosc u hul huu)
    ha hΛ1 hq0 hq1 hm0 hmΛ hmq ham hn4 hτ0le hτ0σ
    (one_div_sigma_le_log_blockScale_harperN_succ hx1 hx hσ0 hσx)

/-- **The middle range, at Harper's numeric data, for the Rademacher function.**  The twin of
`RMF.exists_setIntegral_normSq_pair_middle_harper_data_le`, with Harper's heights added.  The
estimate `RMF.exists_setIntegral_normSq_pair_middle_harper_le_rademacher` runs three blocks short
of the barrier, `n = b - r - 3`, where the tilt bound `≤ 1` at the top becomes `≤ 1/10`.  `B₀`
clears `⌈RMF.blockOffsetThresholdOf Bs⌉`, the threshold of the envelope at `36`
(`RMF.boxEnvelope_pair_gen_le_thirtysix`); both `hosc` are proved inside, as in the far range. -/
theorem exists_setIntegral_normSq_pair_middle_harper_data_le_rademacher (κ Bs : ℝ)
    (hκ : 0 ≤ κ) (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'],
        ∃ KQ CP : ℝ, 0 < KQ ∧ 0 < CP ∧ ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ : ℝ,
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (σ a q m x t u : ℝ),
          1 < x → Λ₀ ≤ Real.log (Real.log x) →
          0 < σ → σ ≤ 1 / 2 → σ * Real.log x ≤ 4 * V → 1 ≤ σ * Real.log x →
          0 < |t - u| → |t - u| ≤ 1 →
          1 / 3 ≤ t → t ≤ 1 / 2 → 1 / 3 ≤ u → u ≤ 1 / 2 →
          Real.log 2 + 2 * harperTheta B x + 2 ≤ Real.log (1 / |t - u|) →
          Real.log (1 / |t - u|) ≤ Real.log (Real.log x) / 3 →
          1 / |t - u| ≤ 1 / σ / Real.exp 2 →
          0 ≤ a → 0 ≤ m → m ≤ Real.sqrt (Real.log (Real.log x)) → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / |t - u|) → 0 ≤ q → q ≤ 1 →
            (∫ ω in barrierEventPair (blockPairAdd (harperTheta B x) (shiftLine σ t)
                (shiftLine σ u) Y) (harperBarrierTop B V x)
                (fun j => -a - Bs * j) (fun j => a + j + harperHf j)
                (fun j => -a - Bs * j) (fun j => a + j + harperHf j),
                ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                    (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2
                  * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                      (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ u) ω‖ ^ 2 ∂ν)
              ≤ (4 * Real.exp 1 ^ 2 * Real.exp (a - harperTheta B x)) ^ 2 * Cst * KQ * CP
                  * bottomSupConst ((B : ℝ) + 2) * (1 / σ) ^ 2
                  / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ 2
                  * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) := by
  obtain ⟨Kd, hKd0, hoscsrc⟩ := exists_abs_sum_cos_primeBlockSub_harper_le
  obtain ⟨Cst, Tsh, hCst, hTsh, hsrc⟩ :=
    exists_setIntegral_normSq_pair_middle_harper_le_rademacher κ Kd Bs hκ hKd0.le hBs
  obtain ⟨n₁, hn₁1, hn₁⟩ := exists_forall_log_pow_le
  set c : ℕ := ⌈Real.log Tsh⌉₊ with hcdef
  refine ⟨Cst, hCst,
    124 + c + ⌈blockOffsetThresholdOf Bs⌉₊ + harperShiftFloor, ?_⟩
  intro B hB Ω' _
  obtain ⟨KQ, CP, hKQ, hCP, hmid⟩ := hsrc Ω'
  refine ⟨KQ, CP, hKQ, hCP, ?_⟩
  intro V hV
  refine ⟨5 * (B : ℝ) + 5 * Real.log V + 50 + 3 * (harperShiftFloor : ℝ) + 3 * (c : ℝ)
      + 3 * (n₁ : ℝ), ?_⟩
  intro Y ν hY σ a q m x t u hx1 hΛ₀ hσ0 hσhalf hσ4 hσx hτ0 hτ1 htl htu hul huu hsmall hτL hτσ
    ha0 hm0 hmΛ hmq ham hq0 hq1
  -- notation
  set θ : ℝ := harperTheta B x with hθdef
  set b : ℕ := harperBarrierTop B V x with hbdef
  set Λ : ℝ := Real.log (Real.log x) with hΛdef
  set r : ℕ := harperShift θ b (t - u) c with hrdef
  set n₂ : ℕ := max (max 4 n₁) ⌈Λ / 4⌉₊ with hn₂def
  -- the pieces of `B₀` and `Λ₀`
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hSF0 : (0 : ℝ) ≤ (harperShiftFloor : ℝ) := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hn₁0 : (0 : ℝ) ≤ (n₁ : ℝ) := Nat.cast_nonneg n₁
  have hx : (B : ℝ) + 2 ≤ Λ := by linarith
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  have hB124 : 124 ≤ B := by omega
  have hθ125 : (125 : ℝ) ≤ θ := harperTheta_ge hB124 hΛ0
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hθB : (B : ℝ) + 1 ≤ θ := le_harperTheta hΛ0
  -- `B` clears the three absolute thresholds; the envelope one is `⌈blockOffsetThresholdOf Bs⌉`
  have hcB : (c : ℝ) + 1 ≤ θ := by
    have : ((c : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast (by omega : c ≤ B)
    linarith
  have hSFB : (harperShiftFloor : ℝ) ≤ 4 * θ := by
    have : ((harperShiftFloor : ℕ) : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast (by omega : harperShiftFloor ≤ B)
    linarith
  have hbot : blockOffsetThresholdOf Bs ≤ θ + (r : ℝ) := by
    have hcl : blockOffsetThresholdOf Bs
        ≤ ((⌈blockOffsetThresholdOf Bs⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hcb : ((⌈blockOffsetThresholdOf Bs⌉₊ : ℕ) : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast (by omega : ⌈blockOffsetThresholdOf Bs⌉₊ ≤ B)
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    linarith
  -- the drop, and the split index
  have hΛ6 : (B : ℝ) + Real.log V + 6 ≤ Λ := by linarith
  have hle := floor_log_add_three_le_harperN hV hx hΛ6
  have hsp2 : ⌊Real.log (1 / |t - u|) - θ⌋₊ + 2 ≤ b :=
    floor_log_one_div_sub_theta_add_two_le_barrierTop hV hx hle hτL (by linarith)
  have hfloor : ⌊Real.log (1 / |t - u|) - θ⌋₊ ≤ b := by omega
  have hsplit : splitIndex θ b (t - u) = ⌊Real.log (1 / |t - u|) - θ⌋₊ := by
    rw [splitIndex, min_eq_right hfloor]
  have hb1 : 1 ≤ b := by omega
  have h1split : 1 ≤ splitIndex θ b (t - u) := one_le_splitIndex hθ0 hb1 hsmall
  -- the count, with three blocks of headroom for the drop
  have hn₂R : (n₂ : ℝ) ≤ (max 4 n₁ : ℕ) + Λ / 4 + 1 := by
    rw [hn₂def]
    rcases max_cases (max 4 n₁) ⌈Λ / 4⌉₊ with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]
      have : (0 : ℝ) ≤ Λ / 4 := by linarith
      linarith
    · rw [he]
      have hcl : (⌈Λ / 4⌉₊ : ℝ) ≤ Λ / 4 + 1 := (Nat.ceil_lt_add_one (by linarith)).le
      have : (0 : ℝ) ≤ ((max 4 n₁ : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  have hmax4 : ((max 4 n₁ : ℕ) : ℝ) ≤ 4 + (n₁ : ℝ) := by
    rcases max_cases 4 n₁ with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; norm_num
    · rw [he]; linarith
  have hcount : (B : ℝ) + Real.log V + 7 + (harperShiftFloor : ℝ) + (c : ℝ)
      + ((n₂ + 3 : ℕ) : ℝ) ≤ 2 / 3 * Λ := by
    push_cast
    linarith
  have hshift : r + (n₂ + 3) ≤ b := harperShift_add_le_barrierTop hV hx hle hτL hcount
  set n : ℕ := b - r - 3 with hndef
  have hrb : r ≤ b := by omega
  have hnbr : n ≤ b - r := by omega
  have hn₂le : n₂ ≤ n := by omega
  have hsr : splitIndex θ b (t - u) + 2 ≤ r := splitIndex_add_two_le_harperShift θ b (t - u) c
  have hn4b : 4 ≤ n := le_trans (le_trans (le_max_left 4 n₁) (le_max_left _ _)) hn₂le
  have hn₁b : n₁ ≤ n := le_trans (le_trans (le_max_right 4 n₁) (le_max_left _ _)) hn₂le
  obtain ⟨hbig, hbig2⟩ := hn₁ n hn₁b
  have hcnt4 : Λ ≤ 4 * (n : ℝ) := by
    have hceil : (⌈Λ / 4⌉₊ : ℕ) ≤ n := le_trans (le_max_right (max 4 n₁) ⌈Λ / 4⌉₊) hn₂le
    have hR : ((⌈Λ / 4⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hceil
    have hcl : Λ / 4 ≤ (⌈Λ / 4⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  -- the tilt: `≤ 1` at the barrier top, and three blocks down it is `≤ 1/10`
  have habs1 : |σ| * Real.log (blockScale θ (b + 1)) ≤ 1 :=
    abs_sigma_mul_log_blockScale_barrierTop_succ_le_one hV hx1 hx hle hσ0.le hσ4
  have hσtop : |σ| * Real.log (blockScale θ (r + n + 1)) ≤ 1 / 10 := by
    have hK10 : (1 : ℝ) ≤ 1 / 10 * Real.exp (((3 : ℕ) : ℝ)) := by
      have h := ten_le_exp_three
      push_cast
      linarith
    have h := sigma_le_of_drop (θ := θ) (σ := σ) hK10 (by omega : 3 ≤ b) habs1
    rwa [show b - 3 + 1 = r + n + 1 from by omega] at h
  -- `hosc`, closed as in the far range
  have hosc : ∀ (w : ℝ), 1 / 3 ≤ w → w ≤ 1 / 2 →
      ∀ mm, mm < r + n →
        |∑ p ∈ primeBlockSub θ mm,
            Real.cos (2 * w * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
          ≤ 2 / 3 * (Kd * Real.exp (-(mm : ℝ))) := by
    intro w hwl hwu mm hmm
    refine hoscsrc w σ θ mm hwl hwu hθ0 ?_
    have hK1 : (1 : ℝ) ≤ 1 * Real.exp (((b - mm : ℕ) : ℝ)) := by
      rw [one_mul]
      exact Real.one_le_exp (Nat.cast_nonneg _)
    have h := sigma_le_of_drop (θ := θ) (σ := σ) hK1 (Nat.sub_le b mm) habs1
    rwa [show b - (b - mm) + 1 = mm + 1 from by omega] at h
  -- the remaining analytic inputs
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  exact hmid Y ν hY θ σ (1 / 10) a Λ q m ((B : ℝ) + 2) t u (harperN B x) b r n hθ125
    (harperTheta_lt B x).le hσ0 hσhalf (harperBarrierTop_le B V x) hsr hrb hnbr h1split
    hfloor hτ0 hτ1 htl htu hul huu hsmall
    (log_two_div_le_two_mul_barrierTop hV hτ0 hx hle hτL (by linarith))
    (by norm_num) le_rfl hσtop
    (le_mul_exp_harperShift hTsh hτ0 hfloor)
    (hosc t htl htu) (hosc u hul huu)
    (fun mm _ => boxEnvelope_pair_gen_le_thirtysix (twenty_le_of_blockSlope_le hBs) hbot mm)
    (result1Threshold_le_shiftedHeight ha0 hBs (harperShiftFloor_le_harperShift θ b (t - u) c))
    hn4b hbig hbig2 hΛ1 hq0 hq1 hm0 hmΛ hmq ham ha0
    (harperShift_le_two_mul_log hτ0 hτ1 hcB hSFB hsmall) hcnt4
    (le_trans (exp_splitIndex_add_two_add_theta_le hθ0 h1split)
      (exp_two_div_le_of_le_div hτσ))
    (one_div_sigma_le_log_blockScale_harperN_succ hx1 hx hσ0 hσx)

/-- **The barrier tube `\{(ω, t) : ω ∈ L(t)\}` is jointly measurable**, for the Rademacher
function: the twin of `RMF.measurableSet_prod_barrierEvent`, and the joint measurability
`RMF.integral_sq_setIntegral_indicator_normSq_harper_le_rademacher` asks for. -/
lemma measurableSet_prod_barrierEventAdd {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν)
    (θ σ : ℝ) (b : ℕ) (u v : ℕ → ℝ) :
    MeasurableSet {q : Ω' × ℝ |
      q.1 ∈ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y (p : ℕ) ω)) b u v} := by
  -- `t ↦ p^{-(1/2+σ+it)}` is continuous
  have hshift : Continuous fun t : ℝ => -(shiftLine σ t) := by
    simp only [shiftLine]
    exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg
  have hcpow : ∀ p : Nat.Primes,
      Continuous fun t : ℝ => ((p : ℕ) : ℂ) ^ (-(shiftLine σ t)) := by
    intro p
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by
      have hpos : 0 < (p : ℕ) := p.2.pos
      exact_mod_cast Nat.cast_ne_zero.2 hpos.ne'
    exact continuous_iff_continuousAt.2 fun t =>
      (continuousAt_const_cpow hp0).comp hshift.continuousAt
  -- each summand is jointly measurable
  have hterm : ∀ p : Nat.Primes, Measurable
      (fun q : Ω' × ℝ => localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y (p : ℕ) q.1)) := by
    intro p
    have h1 : Measurable fun q : Ω' × ℝ => Y (p : ℕ) q.1 :=
      (hY.measurable (p : ℕ) p.2).comp measurable_fst
    have h2 : Measurable fun q : Ω' × ℝ => ((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)) :=
      (hcpow p).measurable.comp measurable_snd
    have h3 : Measurable fun q : Ω' × ℝ =>
        (1 : ℂ) + Y (p : ℕ) q.1 * ((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)) :=
      measurable_const.add (h1.mul h2)
    simp only [localLogAdd]
    exact Real.measurable_log.comp h3.norm
  -- hence so is each partial sum
  have hwalk : ∀ j : ℕ, Measurable fun q : Ω' × ℝ =>
      walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y (p : ℕ) ω)) j q.1 := by
    intro j
    simp only [walk_apply]
    exact Finset.measurable_sum _ fun m _ =>
      Finset.measurable_sum _ fun p _ => hterm p
  -- the set is a finite intersection of preimages
  have hrw : {q : Ω' × ℝ |
        q.1 ∈ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y (p : ℕ) ω)) b u v}
      = ⋂ j ∈ Set.Icc 1 b, {q : Ω' × ℝ |
          walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
            localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y (p : ℕ) ω)) j q.1
            ∈ Set.Icc (u j) (v j)} := by
    ext q
    simp only [barrierEvent, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Icc]
    exact ⟨fun h j hj => h j hj.1 hj.2, fun h j h1 h2 => h j ⟨h1, h2⟩⟩
  rw [hrw]
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ => (hwalk j) measurableSet_Icc

/-! ### Three blocks down: the barrier top the numerator forces

The Rademacher numerator's tilt drop must satisfy `10η ≤ e^d` with `η = σ\log x = 4V`, so
`d = ⌊\log V⌋ + 6` (`RMF.forty_mul_le_exp_floor_log_add_six`) where the Steinhaus numerator has
`+3`.  Paley–Zygmund wants the numerator's event inside the denominator's, and a shorter barrier
is a bigger event, so the denominator's barrier moves down three blocks.  Since
`⌊\log(e^3V)⌋ = ⌊\log V⌋ + 3`, that barrier is `RMF.harperBarrierTop` at `e^3V`; the range
theorems read the tilt only through `σ\log x ≤ 4V`, which holds at `e^3V` too, so they apply there
unchanged.  The facts that read the drop from below lose `e^3`: `σ\log x_b ≥ 4/e^7` in place of
`4/e^4`, and the truncation ratio is bounded by `e^7` in place of `e^4`. -/

/-- **`\lfloor\log(e^3V)\rfloor = \lfloor\log V\rfloor + 3`.**  The whole content of the
three-block shift. -/
lemma floor_log_exp_three_mul {V : ℝ} (hV : 1 ≤ V) :
    ⌊Real.log (Real.exp 3 * V)⌋₊ = ⌊Real.log V⌋₊ + 3 := by
  have hV0 : (0 : ℝ) < V := by linarith
  have hlog : Real.log (Real.exp 3 * V) = Real.log V + 3 := by
    rw [Real.log_mul (Real.exp_ne_zero 3) hV0.ne', Real.log_exp]
    ring
  rw [hlog, Nat.floor_add_ofNat (Real.log_nonneg hV)]

/-- **The numerator's grid, at the Rademacher drop.**  The twin of
`RMF.harperBlockCount_sub_eq_harperBarrierTop`, whose drop is `\lfloor\log V\rfloor + 3`: here it
is `+6`, and the barrier that matches it is the one at `e^3V`. -/
lemma harperBlockCount_sub_eq_harperBarrierTop_exp_three (B : ℕ) {V : ℝ} (hV : 1 ≤ V) (x : ℝ) :
    harperBlockCount (B + 2) x - (⌊Real.log V⌋₊ + 6)
      = harperBarrierTop B (Real.exp 3 * V) x := by
  rw [harperBlockCount, harperBarrierTop, harperN, floor_log_exp_three_mul hV]
  omega

/-- **`\sigma\log x_b \ge 4/e^7` at a shortened barrier.**  The two-parameter form of
`RMF.le_sigma_mul_log_blockScale_barrierTop`: the tilt is set by `V` and the barrier by `W`, and
`W \le e^3V` is what bounds the loss.  At `W = V` it is the original with `e^7` for `e^4`.

`\sigma\log x_b = \sigma\log x\cdot e^{-\lfloor\log W\rfloor-4} \ge 4V/(We^4)`, and `W \le e^3V`
turns that into `4/e^7`. -/
lemma le_sigma_mul_log_blockScale_barrierTop_of_le {B : ℕ} {V W x σ : ℝ} (hV : 1 ≤ V)
    (hx1 : 1 < x) (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log W⌋₊ + 3 ≤ harperN B x) (hVW : V ≤ W) (hWV : W ≤ Real.exp 3 * V)
    (hσ : 4 * V ≤ σ * Real.log x) :
    4 / Real.exp 7 ≤ σ * Real.log (blockScale (harperTheta B x) (harperBarrierTop B W x)) := by
  have hV0 : (0 : ℝ) < V := by linarith
  have hW1 : (1 : ℝ) ≤ W := le_trans hV hVW
  have hW0 : (0 : ℝ) < W := by linarith
  have hlogW : (0 : ℝ) ≤ Real.log W := Real.log_nonneg hW1
  have hfl : ((⌊Real.log W⌋₊ : ℕ) : ℝ) ≤ Real.log W := Nat.floor_le hlogW
  have htop : Real.log (blockScale (harperTheta B x) (harperN B x + 1)) = Real.log x := by
    rw [blockScale_harperN_succ hx1 hx]
  rw [log_blockScale] at htop
  have hcast : ((harperBarrierTop B W x : ℕ) : ℝ)
      = ((harperN B x : ℕ) : ℝ) - ((⌊Real.log W⌋₊ : ℕ) : ℝ) - 3 := by
    have h1 : harperBarrierTop B W x + (⌊Real.log W⌋₊ + 3) = harperN B x := by
      rw [harperBarrierTop]
      omega
    have h2 : ((harperBarrierTop B W x + (⌊Real.log W⌋₊ + 3) : ℕ) : ℝ)
        = ((harperN B x : ℕ) : ℝ) := by rw [h1]
    push_cast at h2
    linarith
  have hsplit : Real.log (blockScale (harperTheta B x) (harperBarrierTop B W x))
      = Real.log x * Real.exp (-(((⌊Real.log W⌋₊ : ℕ) : ℝ) + 4)) := by
    rw [log_blockScale, ← htop, ← Real.exp_add]
    congr 1
    push_cast [hcast]
    ring
  rw [hsplit, ← mul_assoc]
  have hexp : Real.exp (-(Real.log W + 4))
      ≤ Real.exp (-(((⌊Real.log W⌋₊ : ℕ) : ℝ) + 4)) :=
    Real.exp_le_exp.2 (by linarith)
  have hval : Real.exp (-(Real.log W + 4)) = 1 / (W * Real.exp 4) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log hW0]
    field_simp
  have he3 : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
  have he4 : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  have he7 : Real.exp 7 = Real.exp 3 * Real.exp 4 := by
    rw [← Real.exp_add]
    norm_num
  have hstart : 4 / Real.exp 7 ≤ 4 * V * (1 / (W * Real.exp 4)) := by
    rw [he7, show 4 * V * (1 / (W * Real.exp 4)) = 4 * V / (W * Real.exp 4) from by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hWV (by positivity : (0 : ℝ) ≤ 4 * Real.exp 4)]
  calc (4 : ℝ) / Real.exp 7 ≤ 4 * V * (1 / (W * Real.exp 4)) := hstart
    _ = 4 * V * Real.exp (-(Real.log W + 4)) := by rw [hval]
    _ ≤ 4 * V * Real.exp (-(((⌊Real.log W⌋₊ : ℕ) : ℝ) + 4)) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
    _ ≤ σ * Real.log x * Real.exp (-(((⌊Real.log W⌋₊ : ℕ) : ℝ) + 4)) :=
        mul_le_mul_of_nonneg_right hσ (Real.exp_pos _).le

/-- **The truncation ratio is absolute at a shortened barrier too**: `\log M/\log⌊x_b⌋ ≤ e^7` for
the barrier top at `W ∈ [V, e^3V]`.  The two-parameter form of
`RMF.log_harperTruncation_div_log_floor_le`, by the same proof with
`RMF.le_sigma_mul_log_blockScale_barrierTop_of_le` in place of its one-parameter original. -/
lemma log_harperTruncation_div_log_floor_le_of_le {B : ℕ} {V W x σ : ℝ} (hV : 1 ≤ V)
    (hx1 : 1 < x) (hB : 124 ≤ B) (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log W⌋₊ + 3 ≤ harperN B x) (hσ0 : 0 < σ) (hVW : V ≤ W)
    (hWV : W ≤ Real.exp 3 * V) (hσ : 4 * V ≤ σ * Real.log x) :
    Real.log ((harperTruncation σ : ℕ) : ℝ)
        / Real.log ((⌊blockScale (harperTheta B x) (harperBarrierTop B W x)⌋₊ : ℕ) : ℝ)
      ≤ Real.exp 7 := by
  set θ : ℝ := harperTheta B x with hθdef
  set b : ℕ := harperBarrierTop B W x with hbdef
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by
    have : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
    linarith
  have hθ125 : (125 : ℝ) ≤ θ := harperTheta_ge hB hΛ0
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he7 : (1 : ℝ) ≤ Real.exp 7 := by linarith [Real.add_one_le_exp (7 : ℝ)]
  -- `\log x_b = e^{b+θ} ≥ 8`
  set Lb : ℝ := Real.log (blockScale θ b) with hLbdef
  have hLbeq : Lb = Real.exp ((b : ℝ) + θ) := log_blockScale θ b
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hLb8 : (8 : ℝ) ≤ Lb := by
    rw [hLbeq]
    linarith [Real.add_one_le_exp ((b : ℝ) + θ)]
  -- the floor costs at most `\log 2`
  have hXb2 : (2 : ℝ) ≤ blockScale θ b := two_le_blockScale hθ0 b
  have hfl : blockScale θ b / 2 ≤ ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) := by
    have h1 := Nat.lt_floor_add_one (blockScale θ b)
    linarith
  have hflpos : (0 : ℝ) < ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) := by linarith
  have hlogfl : Lb - Real.log 2 ≤ Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) := by
    have h1 : Real.log (blockScale θ b / 2) ≤ Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hfl
    rwa [Real.log_div (by linarith) (by norm_num)] at h1
  have hlogflpos : (0 : ℝ) < Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) := by linarith
  -- the ceiling costs at most `\log 2`
  have hMle : Real.log ((harperTruncation σ : ℕ) : ℝ) ≤ 1 / (2 * σ) + Real.log 2 := by
    have hexp0 : (1 : ℝ) ≤ Real.exp (1 / (2 * σ)) := by
      have : (0 : ℝ) ≤ 1 / (2 * σ) := by positivity
      linarith [Real.add_one_le_exp (1 / (2 * σ))]
    have hceil : ((harperTruncation σ : ℕ) : ℝ) ≤ 2 * Real.exp (1 / (2 * σ)) := by
      rw [harperTruncation]
      have := (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ Real.exp (1 / (2 * σ)))).le
      linarith
    have h1 : Real.log ((harperTruncation σ : ℕ) : ℝ)
        ≤ Real.log (2 * Real.exp (1 / (2 * σ))) := by
      refine Real.log_le_log ?_ hceil
      rw [harperTruncation]
      have : (0 : ℝ) < Real.exp (1 / (2 * σ)) := Real.exp_pos _
      have h2 := Nat.le_ceil (Real.exp (1 / (2 * σ)))
      linarith
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, add_comm] at h1
  -- the drop from below, three blocks lower than the Steinhaus one
  have hlow : 4 / Real.exp 7 ≤ σ * Lb :=
    le_sigma_mul_log_blockScale_barrierTop_of_le hV hx1 hx hle hVW hWV hσ
  have h8 : (8 : ℝ) ≤ 2 * Real.exp 7 * (σ * Lb) := by
    have hpos : (0 : ℝ) < Real.exp 7 := Real.exp_pos 7
    have hmul := mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ 2 * Real.exp 7)
    have heq : 2 * Real.exp 7 * (4 / Real.exp 7) = 8 := by
      field_simp
      norm_num
    linarith [hmul, heq.ge, heq.le]
  have hinv : 1 / (2 * σ) ≤ Real.exp 7 * Lb / 8 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 8)]
    nlinarith [h8]
  -- `\log 2 ≤ L_b/8`
  have hlog2Lb : Real.log 2 ≤ Lb / 8 := by linarith
  rw [div_le_iff₀ hlogflpos]
  nlinarith [hMle, hinv, hlog2Lb, hlogfl, he7, hLb8]

/-- **The crude boundary is at most `e^9/4` below `L_c` at a shortened barrier.**  The twin of
`RMF.one_div_sigma_le_K_mul_kappa` at the drop's shortened lower bound: three blocks cost `e^3`
and nothing else changes. -/
lemma one_div_sigma_le_K_mul_kappa_of_low {Lb sg : ℝ} (hs0 : 0 < sg)
    (hlow : 4 / Real.exp 7 ≤ sg * Lb) :
    1 / sg ≤ Real.exp 9 / 4 * (Lb / Real.exp 2) := by
  have hpos2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hpos7 : (0 : ℝ) < Real.exp 7 := Real.exp_pos 7
  have h9 : Real.exp 9 = Real.exp 2 * Real.exp 7 := by
    rw [← Real.exp_add]
    norm_num
  have hkey : Real.exp 9 / 4 * (Lb / Real.exp 2) = Real.exp 7 * Lb / 4 := by
    rw [h9]; field_simp
  have h4 : (4 : ℝ) ≤ Real.exp 7 * (sg * Lb) := by
    have hm := mul_le_mul_of_nonneg_left hlow hpos7.le
    have heq : Real.exp 7 * (4 / Real.exp 7) = 4 := by field_simp
    linarith [hm, heq.ge, heq.le]
  rw [hkey, div_le_div_iff₀ hs0 (by norm_num : (0 : ℝ) < 4)]
  nlinarith [h4]

set_option maxHeartbeats 4000000 in
-- the four range bounds are elaborated against the assembly's twenty-odd parameters, which is
-- what raises the limit here
/-- **Harper's Key Proposition 5 for the Rademacher function, at his numeric data** (his §5.3):
`E(∫_L |F(1/2+4V/\log x+it)|² dt)² ≤ (6 + 2/\log 2)·E·e^{2a}(\log x/4V)²/W²` with
`W = 1 + (1-q)√(\log\log x)`, where `L` is the set of `t ∈ T` at which the barrier event on
`[1, b]`, `b = RMF.harperBarrierTop B V' x`, occurs.  The twin of
`RMF.integral_sq_setIntegral_indicator_normSq_harper_data_le`.  `E` depends on `κ`, `Bs`, `B` and
`Ω'` only.

`T ⊆ [1/3, 1/2]` is Harper's restriction in the Rademacher case: without rotation invariance the
two-point moment also sees the sum frequency `t+u`.  The barrier top is taken at any
`V' ∈ [V, e^3V]`; `V' = e^3V` gives `RMF.harperBarrierTop B V x - 3`, the event of the Rademacher
numerator.  The count `6B + 3\log V' + 40 ≤ \log\log x` dominates the thresholds of the four
ranges, and `4V(4e^{2B+6}+7) ≤ \log x` is the far range's window `2τ₀ + 7 ≤ 1/σ`.
`1 ≤ q√(\log\log x)` is equivalent to `W² ≤ \log\log x`; Harper's `q ≥ 2/3` gives it once
`\log\log x ≥ 3`. -/
theorem integral_sq_setIntegral_indicator_normSq_harper_data_le_rademacher (κ Bs : ℝ) (hκ : 0 ≤ κ)
    (hBs : blockSlope 125 ≤ Bs) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'],
        ∃ E : ℝ, 0 < E ∧ ∀ V V' : ℝ, 1 ≤ V → V ≤ V' → V' ≤ Real.exp 3 * V →
          ∃ Λ₀ : ℝ,
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (σ a q m x : ℝ) (T : Set ℝ),
          1 < x → 3 ≤ x → Λ₀ ≤ Real.log (Real.log x) →
          6 * (B : ℝ) + 3 * Real.log V' + 40 ≤ Real.log (Real.log x) →
          4 * V * (4 * Real.exp (2 * (B : ℝ) + 6) + 7) ≤ Real.log x →
          0 < σ → σ ≤ 1 / 2 → σ * Real.log x = 4 * V →
          MeasurableSet T → T ⊆ Set.Icc (1 / 3 : ℝ) (1 / 2) →
          1 ≤ a → 0 ≤ m → m ≤ Real.sqrt (Real.log (Real.log x)) → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log 2 →
          0 ≤ q → q ≤ 1 → 1 ≤ q * Real.sqrt (Real.log (Real.log x)) →
            (∫ ω, (∫ t in T, Set.indicator
                (barrierEvent (fun m ω => ∑ p ∈ primeBlockSub (harperTheta B x) m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω))
                  (harperBarrierTop B V' x)
                  (fun j => -a - Bs * j) (fun j => a + j + harperHf j))
                (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                    (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                  ^ 2 ∂ν)
              ≤ (6 + 2 / Real.log 2) * (E * Real.exp (2 * a) * (1 / σ) ^ 2
                  / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ 2) := by
  obtain ⟨Cf, hCf, Bf, hfarsrc⟩ :=
    exists_setIntegral_normSq_pair_far_harper_data_le_rademacher κ Bs hκ hBs
  obtain ⟨Cm, hCm, Bm, hmidsrc⟩ :=
    exists_setIntegral_normSq_pair_middle_harper_data_le_rademacher κ Bs hκ hBs
  refine ⟨max (max 124 Bf) Bm, ?_⟩
  intro B hB
  have hB124 : 124 ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  intro Ω' _
  obtain ⟨Kf, hKf, hfar1⟩ :=
    hfarsrc B (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB) Ω'
  obtain ⟨KQ3, CP3, hKQ3, hCP3, hmid1⟩ := hmidsrc B (le_trans (le_max_right _ _) hB) Ω'
  obtain ⟨KQ1, CP1, hKQ1, hCP1, hcs⟩ :=
    exists_setIntegral_normSq_pair_crude_split_harper_data_le_rademacher Bs (Ω' := Ω')
  obtain ⟨KQ2, CP2, hKQ2, hCP2, hct⟩ :=
    exists_setIntegral_normSq_pair_crude_top_harper_data_le_rademacher Bs (Ω' := Ω')
  set bc : ℝ := bottomSupConst ((B : ℝ) + 2) with hbcdef
  have hbc1 : (1 : ℝ) ≤ bc := one_le_bottomSupConst _
  set τ0 : ℝ := 2 * Real.exp (2 * (B : ℝ) + 6) with hτ0def
  have hτ0pos : (0 : ℝ) < τ0 := by positivity
  refine ⟨max (max (81 * (16 * Real.exp 4 * KQ1 * CP1 * bc))
        (16 * (Real.exp 9 / 4) * (4 / Real.exp 3) ^ 3 * (KQ2 * Real.exp 28 * CP2 * bc)))
      (max (16 * Real.exp 4 * Cm * KQ3 * CP3 * bc)
        (Cf * Kf * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4)), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 81 * (16 * Real.exp 4 * KQ1 * CP1 * bc) := by positivity
    exact lt_of_lt_of_le h1 (le_trans (le_max_left _ _) (le_max_left _ _))
  intro V V' hV hVV' hV'V
  have hV'1 : (1 : ℝ) ≤ V' := le_trans hV hVV'
  obtain ⟨Λf, hfar⟩ := hfar1 V' hV'1
  obtain ⟨Λm, hmid⟩ := hmid1 V' hV'1
  refine ⟨max (max Λf Λm) 1, ?_⟩
  intro Y ν hY σ a q m x T hx1 hx3 hΛ₀ hΛcnt hfarwin hσ0 hσhalf hσeq hTm hTsub ha1 hm0 hmΛ hmq ham
    hq0 hq1 hqΛ
  -- Harper's height range, and the weaker one the assembly and `|t-u| ≤ 1` read
  have hTsub' : T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := fun _ ht =>
    Set.Icc_subset_Icc (by norm_num) le_rfl (hTsub ht)
  -- notation
  set θ : ℝ := harperTheta B x with hθdef
  set b : ℕ := harperBarrierTop B V' x with hbdef
  set Λ : ℝ := Real.log (Real.log x) with hΛdef
  set Lb : ℝ := Real.log (blockScale θ b) with hLbdef
  -- arithmetic ground
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hlogVle : Real.log V ≤ Real.log V' := Real.log_le_log (by linarith) hVV'
  have hlogV' : (0 : ℝ) ≤ Real.log V' := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hΛ1 : (1 : ℝ) ≤ Λ := le_trans (le_max_right _ _) hΛ₀
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  have hΛf : Λf ≤ Λ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΛ₀
  have hΛm : Λm ≤ Λ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΛ₀
  have hx : (B : ℝ) + 2 ≤ Λ := by linarith
  have hσ4 : σ * Real.log x ≤ 4 * V := le_of_eq hσeq
  have hσ4' : 4 * V ≤ σ * Real.log x := ge_of_eq hσeq
  have hσ4V' : σ * Real.log x ≤ 4 * V' := by linarith
  have hσx : 1 ≤ σ * Real.log x := by rw [hσeq]; linarith
  have hΛ6 : (B : ℝ) + Real.log V' + 6 ≤ Λ := by linarith
  have hle : ⌊Real.log V'⌋₊ + 3 ≤ harperN B x :=
    floor_log_add_three_le_harperN hV'1 hx hΛ6
  have hbge : Λ - (B : ℝ) - Real.log V' - 6 ≤ (b : ℝ) :=
    barrierTop_ge_data hV'1 hx hle
  have hb1 : 1 ≤ b := by
    have h : (1 : ℝ) ≤ (b : ℝ) := by linarith
    exact_mod_cast h
  have hb0R : (0 : ℝ) < (b : ℝ) := by linarith
  have hθ125 : (125 : ℝ) ≤ θ := harperTheta_ge hB124 hΛ0
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hθlt : θ < (B : ℝ) + 2 := harperTheta_lt B x
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  -- the block scale at the barrier top
  have hLbeq : Lb = Real.exp ((b : ℝ) + θ) := log_blockScale θ b
  have hLb0 : (0 : ℝ) ≤ Lb := by rw [hLbeq]; positivity
  have hlogLb : Real.log Lb = (b : ℝ) + θ := by rw [hLbeq, Real.log_exp]
  have hLbpos : (0 : ℝ) < Lb := by rw [hLbeq]; positivity
  -- the drop, from both sides
  have hdropup : σ * Lb ≤ 4 / Real.exp 3 :=
    sigma_mul_log_blockScale_barrierTop_le hV'1 hx1 hx hle hσ4V'
  have hdroplow : 4 / Real.exp 7 ≤ σ * Lb :=
    le_sigma_mul_log_blockScale_barrierTop_of_le hV hx1 hx hle hVV' hV'V hσ4'
  -- the crude boundary and its slack
  set κc : ℝ := Lb / Real.exp 2 with hκcdef
  set Kc : ℝ := Real.exp 9 / 4 with hKcdef
  have hK1 : (1 : ℝ) ≤ Kc := by
    rw [hKcdef]
    have h69 : Real.exp 6 ≤ Real.exp 9 := Real.exp_le_exp.2 (by norm_num)
    linarith [one_le_exp_six_div_four]
  have hκLc : κc ≤ 1 / σ := kappa_le_one_div_sigma hσ0 hdropup
  have hLcκ : 1 / σ ≤ Kc * κc := one_div_sigma_le_K_mul_kappa_of_low hσ0 hdroplow
  -- `ε` and `ε'`
  set ε : ℝ := Real.exp (-(Λ / 3)) with hεdef
  set ε' : ℝ := Real.exp (-(2 * θ + 2)) / 2 with hε'def
  have hε0 : (0 : ℝ) < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := by
    rw [hεdef, Real.exp_le_one_iff]
    linarith
  have hcrudeτ : ∀ τ : ℝ, 0 < τ → τ ≤ ε → Λ / 3 ≤ Real.log (1 / τ) := by
    intro τ hτ0 hτε
    have h1 : Real.log τ ≤ -(Λ / 3) := by
      rw [← Real.log_exp (-(Λ / 3))]
      exact Real.log_le_log hτ0 hτε
    rw [one_div, Real.log_inv]
    linarith
  have houterτ : ∀ τ : ℝ, 0 < τ → ε < τ → Real.log (1 / τ) ≤ Λ / 3 := by
    intro τ hτ0 hτε
    have h1 : -(Λ / 3) ≤ Real.log τ := by
      rw [← Real.log_exp (-(Λ / 3))]
      exact Real.log_le_log (Real.exp_pos _) hτε.le
    rw [one_div, Real.log_inv]
    linarith
  -- the two thresholds the ranges share
  have hsmallcr : Real.log 2 + 2 * θ + 2 ≤ Λ / 3 := by linarith
  have hbθ : Real.log 2 + θ - 2 ≤ (b : ℝ) := by linarith
  have hΛcs : (B : ℝ) + Real.log V' + 8 ≤ 2 / 3 * Λ := by linarith
  have hΛ4V : Real.log (4 * V) + 2 ≤ 2 / 3 * Λ := by
    have h4V : Real.log (4 * V) = Real.log 4 + Real.log V := Real.log_mul (by norm_num) (by
      linarith : V ≠ 0)
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    rw [h4V, hlog4]
    linarith
  -- `1/σ ≤ \log x`, hence `\log(2L_c) ≤ \log 2 + Λ`
  have hinvσ : 1 / σ ≤ Real.log x := by
    rw [div_le_iff₀ hσ0, mul_comm]
    linarith
  have hlogL : 1 + Real.log (2 * (1 / σ)) ≤ 3 * Λ := by
    have hpos : (0 : ℝ) < 1 / σ := by positivity
    have h1 : Real.log (1 / σ) ≤ Λ := by
      rw [hΛdef]
      exact Real.log_le_log hpos hinvσ
    rw [Real.log_mul (by norm_num) hpos.ne']
    linarith
  -- the barrier event, and its two measurability facts
  have hXmeas : ∀ (t : ℝ) (m : ℕ), Measurable (fun ω => ∑ p ∈ primeBlockSub θ m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) := fun t m =>
    Finset.measurable_sum _ fun p _ => (measurable_localLogAdd _).comp (hY.measurable (p : ℕ) p.2)
  refine le_trans (integral_sq_setIntegral_indicator_normSq_harper_of_ranges_rademacher hY
    (blockCutoff θ (harperN B x))
    (fun t => barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) b
      (fun j => -a - Bs * j) (fun j => a + j + harperHf j))
    (fun t => measurableSet_barrierEvent (hXmeas t) b _ _)
    (measurableSet_prod_barrierEventAdd hY θ σ b _ _) hTm hTsub'
    (C₁ := 16 * Real.exp 4 * Real.exp (2 * a) * KQ1 * CP1 * bc)
    (C₂ := Real.exp (2 * a) * (KQ2 * Real.exp 28) * CP2 * bc)
    (E₁ := 16 * Real.exp 4 * Real.exp (2 * a) * Cm * KQ3 * CP3 * bc)
    (E₂ := Real.exp (2 * a) * (Cf * Kf * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4))
    (S := 4 / Real.exp 3) (Lb := Lb) (nb := (b : ℝ)) (Lc := 1 / σ)
    (W := 1 + (1 - q) * Real.sqrt Λ) (Λ := Λ) (ε := ε) (ε' := ε') (κ := κc) (K := Kc)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hLb0 hb0R hσ0 rfl (by rw [le_div_iff₀ hσ0]; linarith) hΛ1
    (by nlinarith only [Real.sqrt_nonneg Λ, hq1])
    (sq_one_add_one_sub_mul_sqrt_le hq1 hΛ1 hqΛ)
    hlogL hε0 hε1 hdropup (log_log_le_two_mul_barrierTop hV'1 hx hle (by linarith))
    hK1 hκLc hLcκ ?_ ?_ ?_ ?_ ?_) ?_
  · -- `hcrudelog`
    intro τ hτ0 hτε
    have h := hcrudeτ τ hτ0 hτε
    rw [log_two_div_eq hτ0]
    linarith
  · -- `hcr1`, the first crude regime
    intro t ht u hu htu hτε hκτ
    obtain ⟨htl, htu'⟩ := hTsub ht
    obtain ⟨hul, huu⟩ := hTsub hu
    have hτ0 : (0 : ℝ) < |t - u| := abs_sub_pos.mpr htu
    have hτ1 : |t - u| ≤ 1 := abs_sub_le_one_of_mem_Icc hTsub' ht hu
    have hsmall : Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t - u|) :=
      le_trans hsmallcr (hcrudeτ _ hτ0 hτε)
    have hreg : Real.log (1 / |t - u|) ≤ (b : ℝ) + θ - 2 := by
      have hlogκ : Real.log κc = (b : ℝ) + θ - 2 := by
        rw [hκcdef, Real.log_div hLbpos.ne' (Real.exp_pos 2).ne', Real.log_exp, hlogLb]
      have hpos : (0 : ℝ) < 1 / |t - u| := by positivity
      have := Real.log_le_log hpos hκτ
      rwa [hlogκ] at this
    have hsrc := hcs Y ν hY B V' x σ a t u hB124 hV'1 hx1 hx hle hσ0 hσhalf hσx hσ4V' hτ0
      hτ1 htl htu' hul huu hsmall hreg hbθ hΛcs
    rw [barrierEvent_inter_eq_blockPairAdd]
    exact le_trans hsrc (crude_split_reshape hθ0 hσ0 hKQ1.le hCP1.le (by linarith)
      (by positivity))
  · -- `hcr2`, the second crude regime
    intro t ht u hu htu hτε hτκ
    obtain ⟨htl, htu'⟩ := hTsub ht
    obtain ⟨hul, huu⟩ := hTsub hu
    have hτ0 : (0 : ℝ) < |t - u| := abs_sub_pos.mpr htu
    have hsrc := hct Y ν hY B V' x σ a t u hB124 hV'1 hx1 hx3 hx hle hb1 hσ0 hσ4V' hσx
      htl htu' hul huu
    rw [barrierEvent_inter_eq_blockPairAdd]
    refine le_trans hsrc ?_
    have hR : Real.log ((harperTruncation σ : ℕ) : ℝ)
        / Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) ≤ Real.exp 7 :=
      log_harperTruncation_div_log_floor_le_of_le hV hx1 hB124 hx hle hσ0 hVV' hV'V hσ4'
    have hR0 : (0 : ℝ) ≤ Real.log ((harperTruncation σ : ℕ) : ℝ)
        / Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) := by
      have h400 := four_hundred_le_floor_blockScale (θ := θ) (by linarith) b
      have hM := Nat.le_ceil (Real.exp (1 / (2 * σ)))
      have hMpos : (0 : ℝ) < ((harperTruncation σ : ℕ) : ℝ) := by
        rw [harperTruncation]
        have := Real.exp_pos (1 / (2 * σ))
        linarith
      have hnum : (0 : ℝ) ≤ Real.log ((harperTruncation σ : ℕ) : ℝ) := by
        refine Real.log_nonneg ?_
        rw [harperTruncation]
        have hexp1 : (1 : ℝ) ≤ Real.exp (1 / (2 * σ)) := by
          have : (0 : ℝ) ≤ 1 / (2 * σ) := by positivity
          linarith [Real.add_one_le_exp (1 / (2 * σ))]
        linarith
      have hden : (0 : ℝ) ≤ Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) :=
        Real.log_nonneg (by linarith)
      positivity
    have hpow : (Real.log ((harperTruncation σ : ℕ) : ℝ)
        / Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ)) ^ 4 ≤ Real.exp 28 := by
      have h4 : Real.exp 28 = Real.exp 7 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h4]
      exact pow_le_pow_left₀ hR0 hR 4
    exact crude_top_reshape hθ0 hpow hKQ2.le hCP2.le (by linarith) hLb0 hb0R
  · -- `hmid`
    intro t ht u hu htu hτε hτε'
    obtain ⟨htl, htu'⟩ := hTsub ht
    obtain ⟨hul, huu⟩ := hTsub hu
    have hτ0 : (0 : ℝ) < |t - u| := abs_sub_pos.mpr htu
    have hτ1 : |t - u| ≤ 1 := abs_sub_le_one_of_mem_Icc hTsub' ht hu
    have hτL : Real.log (1 / |t - u|) ≤ Λ / 3 := houterτ _ hτ0 hτε
    have hsmall : Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t - u|) :=
      log_two_add_two_theta_add_two_le hτ0 hτε'
    have hτσ : 1 / |t - u| ≤ 1 / σ / Real.exp 2 :=
      le_one_div_sigma_div_exp_two hV hx1 hσ0 hσ4 hτ0 hτL hΛ4V
    have hamτ : a ≤ m + κ * Real.log (2 / |t - u|) := by
      have hlog : Real.log 2 ≤ Real.log (2 / |t - u|) := by
        refine Real.log_le_log (by norm_num) ?_
        rw [le_div_iff₀ hτ0]
        linarith
      nlinarith only [hκ, hlog, ham]
    have hsrc := hmid Y ν hY σ a q m x t u hx1 hΛm hσ0 hσhalf hσ4V' hσx hτ0 hτ1 htl htu'
      hul huu hsmall hτL hτσ (by linarith) hm0 hmΛ hmq hamτ hq0 hq1
    have hWpos : (0 : ℝ) < 1 + (1 - q) * Real.sqrt Λ := by
      nlinarith only [Real.sqrt_nonneg Λ, hq1]
    rw [barrierEvent_inter_eq_blockPairAdd]
    exact le_trans hsrc (middle_reshape hθ0 hσ0 hWpos hCm.le hKQ3.le hCP3.le (by linarith)
      (by positivity))
  · -- `hfar`
    intro t ht u hu htu hτε hτε'
    obtain ⟨htl, htu'⟩ := hTsub ht
    obtain ⟨hul, huu⟩ := hTsub hu
    have hτ0 : (0 : ℝ) < |t - u| := abs_sub_pos.mpr htu
    have hτ1 : |t - u| ≤ 1 := abs_sub_le_one_of_mem_Icc hTsub' ht hu
    have hτL : Real.log (1 / |t - u|) ≤ Λ / 3 := houterτ _ hτ0 hτε
    have hτ0le : 1 / |t - u| ≤ τ0 := by
      rw [hτ0def, show 2 * (B : ℝ) + 6 = 2 * ((B : ℝ) + 2) + 2 by ring]
      exact one_div_abs_le_two_mul_exp (by linarith) hτ0 hτε'
    have hτ0σ : 2 * τ0 + 7 ≤ 1 / σ := by
      rw [hτ0def]
      exact two_mul_add_seven_le_one_div_sigma hσ0 hσeq hV hfarwin
    have hamτ : a ≤ m + κ * Real.log (2 / |t - u|) := by
      have hlog : Real.log 2 ≤ Real.log (2 / |t - u|) := by
        refine Real.log_le_log (by norm_num) ?_
        rw [le_div_iff₀ hτ0]
        linarith
      nlinarith only [hκ, hlog, ham]
    have hsrc := hfar Y ν hY σ a q m x τ0 t u hx1 hΛf hσ0 hσhalf hσ4V' hσx hτ0 hτ1 htl
      htu' hul huu hτL ha1 hq0 hq1 hm0 hmΛ hmq hamτ hτ0le hτ0σ
    rw [barrierEvent_inter_eq_blockPairAdd]
    refine le_trans hsrc ?_
    have hlogT : (0 : ℝ) ≤ Real.log (2 * (2 * τ0 + 7)) :=
      Real.log_nonneg (by nlinarith only [hτ0pos])
    have hlogpos : (0 : ℝ) < Real.log (2 / |t - u|) := log_two_div_pos hτ0 hτ1
    refine le_trans (far_reshape (a := a) (by linarith) hCf.le hKf.le
      (by positivity : (0 : ℝ) ≤ (2 * τ0 + 7) ^ 2)
      (by positivity : (0 : ℝ) ≤ Real.log (2 * (2 * τ0 + 7)) ^ 4)
      (by positivity : (0 : ℝ) ≤ (1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2)
      (by positivity : (0 : ℝ) ≤ 1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)))
      (le_of_eq (by ring))
  · -- collapse the four constants
    have hea : (1 : ℝ) ≤ Real.exp (2 * a) := by
      have : (0 : ℝ) ≤ 2 * a := by linarith
      linarith [Real.add_one_le_exp (2 * a)]
    have hW2 : (0 : ℝ) < (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
      have hs : (0 : ℝ) ≤ Real.sqrt Λ := Real.sqrt_nonneg Λ
      have : (0 : ℝ) < 1 + (1 - q) * Real.sqrt Λ := by nlinarith
      positivity
    have hE0 : (0 : ℝ) ≤ Real.exp (2 * a) := (Real.exp_pos _).le
    have hmaxle : max (max (81 * (16 * Real.exp 4 * Real.exp (2 * a) * KQ1 * CP1 * bc))
          (16 * Kc * (4 / Real.exp 3) ^ 3
            * (Real.exp (2 * a) * (KQ2 * Real.exp 28) * CP2 * bc)))
        (max (16 * Real.exp 4 * Real.exp (2 * a) * Cm * KQ3 * CP3 * bc)
          (Real.exp (2 * a)
            * (Cf * Kf * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4)))
        ≤ max (max (81 * (16 * Real.exp 4 * KQ1 * CP1 * bc))
              (16 * (Real.exp 9 / 4) * (4 / Real.exp 3) ^ 3 * (KQ2 * Real.exp 28 * CP2 * bc)))
            (max (16 * Real.exp 4 * Cm * KQ3 * CP3 * bc)
              (Cf * Kf * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4))
          * Real.exp (2 * a) := by
      refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
      · refine le_trans (le_of_eq ?_)
          (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) hE0)
        ring
      · refine le_trans (le_of_eq ?_)
          (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _)) hE0)
        rw [hKcdef]
        ring
      · refine le_trans (le_of_eq ?_)
          (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _)) hE0)
        ring
      · refine le_trans (le_of_eq ?_)
          (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) hE0)
        ring
    have hcoef : (0 : ℝ) ≤ (6 + 2 / Real.log 2)
        * ((1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2) := by positivity
    calc (6 + 2 / Real.log 2)
          * (max (max (81 * (16 * Real.exp 4 * Real.exp (2 * a) * KQ1 * CP1 * bc))
              (16 * Kc * (4 / Real.exp 3) ^ 3
                * (Real.exp (2 * a) * (KQ2 * Real.exp 28) * CP2 * bc)))
            (max (16 * Real.exp 4 * Real.exp (2 * a) * Cm * KQ3 * CP3 * bc)
              (Real.exp (2 * a)
                * (Cf * Kf * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4)))
            * (1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2)
        = (6 + 2 / Real.log 2) * ((1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2)
            * max (max (81 * (16 * Real.exp 4 * Real.exp (2 * a) * KQ1 * CP1 * bc))
              (16 * Kc * (4 / Real.exp 3) ^ 3
                * (Real.exp (2 * a) * (KQ2 * Real.exp 28) * CP2 * bc)))
            (max (16 * Real.exp 4 * Real.exp (2 * a) * Cm * KQ3 * CP3 * bc)
              (Real.exp (2 * a)
                * (Cf * Kf * (2 * τ0 + 7) ^ 2
                  * Real.log (2 * (2 * τ0 + 7)) ^ 4))) := by ring
      _ ≤ (6 + 2 / Real.log 2) * ((1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2)
            * (max (max (81 * (16 * Real.exp 4 * KQ1 * CP1 * bc))
                (16 * (Real.exp 9 / 4) * (4 / Real.exp 3) ^ 3
                  * (KQ2 * Real.exp 28 * CP2 * bc)))
              (max (16 * Real.exp 4 * Cm * KQ3 * CP3 * bc)
                (Cf * Kf * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4))
              * Real.exp (2 * a)) := mul_le_mul_of_nonneg_left hmaxle hcoef
      _ = (6 + 2 / Real.log 2)
            * (max (max (81 * (16 * Real.exp 4 * KQ1 * CP1 * bc))
                (16 * (Real.exp 9 / 4) * (4 / Real.exp 3) ^ 3
                  * (KQ2 * Real.exp 28 * CP2 * bc)))
              (max (16 * Real.exp 4 * Cm * KQ3 * CP3 * bc)
                (Cf * Kf * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4))
              * Real.exp (2 * a) * (1 / σ) ^ 2
              / (1 + (1 - q) * Real.sqrt Λ) ^ 2) := by ring

end RMF
