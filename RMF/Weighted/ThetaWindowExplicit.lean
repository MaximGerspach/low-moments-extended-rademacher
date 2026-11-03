/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.HalfWindowExplicit

/-!
# The windows of `Z` at `q = ½`, split at slope `θ`, to second order

The windows of `Z` at `q = ½` (`RMF/Weighted/HalfWindowExplicit.lean`), bounded sharply enough for
the constant `10` of `RMF/Weighted/TenNumeralExplicit.lean`:

* **the weight to second order**: on a window `e^{βt²} ≤ 1 + bl + l²(e^b - 1 - b)`, `l = (t/T)²`,
  `b = βT²` (`RMF.exp_mul_le_taylor`), so the weight integrates to at most `W(b)/T`,
  `W(b) = (e - 1) + b(1 - e⁻¹) + (e^b - 1 - b)(1 - e⁻³)/3` (`RMF.taylorWindowW`,
  `RMF.setIntegral_inv_sq_add_sq_mul_exp_window_le_taylor`), against the chord's
  `(e - 1) + (e^b - 1)(1 - e⁻¹)`;
* **the split at slope `θ`**: window `k` is split at `z_k = ⌈exp(θe^k)⌉` (`RMF.thetaSplit`), so
  `T_k log z_k ≥ θ`, and costs `G_k² = (2/θ)W(b_k)e^{9.0028/log y + 9.0028e^{-k}/θ}`
  (`RMF.thetaWindowConst`), `b_k → θ²/2`.  At `θ = 3/2`, `G_∞ = 1.9090`.

`RMF.window_theta_le_jensen` and `RMF.window_theta_le_chaos` are one window by Jensen and by the
weighted chaos, through `RMF.integral_rpow_window_le_split_jensen_of_weight` and
`RMF.integral_rpow_window_le_split_chaos_of_weight`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The window's weight to second order -/

/-- **The exponential against its second-order Taylor polynomial on `[0, 1]`**: for `b ≥ 0` and
`0 ≤ v ≤ 1`, `e^{bv} ≤ 1 + bv + v²(e^b - 1 - b)`, termwise in the exponential series
(`v^n ≤ v²` for `n ≥ 2`). -/
lemma exp_mul_le_taylor {b v : ℝ} (hb : 0 ≤ b) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Real.exp (b * v) ≤ 1 + b * v + v ^ 2 * (Real.exp b - 1 - b) := by
  have h1 : HasSum (fun n : ℕ => (b * v) ^ n / (n.factorial : ℝ)) (Real.exp (b * v)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (b * v)
  have h2 : HasSum (fun n : ℕ => b ^ n / (n.factorial : ℝ)) (Real.exp b) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp b
  have h3 := (h2.mul_left (v ^ 2)).sub h1
  rw [← hasSum_nat_add_iff' 2] at h3
  have hnn : ∀ n : ℕ, 0 ≤ v ^ 2 * (b ^ (n + 2) / ((n + 2).factorial : ℝ))
      - (b * v) ^ (n + 2) / ((n + 2).factorial : ℝ) := by
    intro n
    have hf : (0 : ℝ) < ((n + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hvn : v ^ n ≤ 1 := pow_le_one₀ hv0 hv1
    have heq : v ^ 2 * (b ^ (n + 2) / ((n + 2).factorial : ℝ))
        - (b * v) ^ (n + 2) / ((n + 2).factorial : ℝ)
        = v ^ 2 * b ^ (n + 2) * (1 - v ^ n) / ((n + 2).factorial : ℝ) := by
      rw [mul_pow]
      ring
    rw [heq]
    apply div_nonneg _ hf.le
    have hb2 : 0 ≤ v ^ 2 * b ^ (n + 2) := by positivity
    exact mul_nonneg hb2 (by linarith)
  have h4 := h3.nonneg hnn
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, zero_add] at h4
  nlinarith [h4]

/-- The window's weight bound to second order, at `b = βT²`:
`(e - 1) + b(1 - e⁻¹) + (e^b - 1 - b)(1 - e⁻³)/3`. -/
noncomputable def taylorWindowW (b : ℝ) : ℝ :=
  (Real.exp 1 - 1) + b * (1 - (Real.exp 1)⁻¹)
    + (Real.exp b - 1 - b) * (1 - (Real.exp 1)⁻¹ ^ 3) / 3

/-- **The block window's weight against the two-point ratio, to second order.**  For `T > 0` and
`β ≥ 0`, with `b = βT²`,
`∫_{T/e}^{T} e^{βt²}dt/(σ²+t²) ≤ ((e - 1) + b(1 - e⁻¹) + (e^b - 1 - b)(1 - e⁻³)/3)/T`: on the
window `(σ²+t²)⁻¹ ≤ t⁻²` and `e^{βt²} ≤ 1 + bl + l²(e^b - 1 - b)`, `l = (t/T)²`
(`RMF.exp_mul_le_taylor`). -/
lemma setIntegral_inv_sq_add_sq_mul_exp_window_le_taylor (σ : ℝ) {T β : ℝ} (hT : 0 < T)
    (hβ : 0 ≤ β) :
    (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2))
      ≤ taylorWindowW (β * T ^ 2) / T := by
  unfold taylorWindowW
  have he1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have ha0 : 0 < T / Real.exp 1 := div_pos hT he0
  have haT : T / Real.exp 1 ≤ T := div_le_self hT.le he1.le
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (T / Real.exp 1) T)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hT2 : 0 < T ^ 2 := by positivity
  have hb0 : 0 ≤ β * T ^ 2 := mul_nonneg hβ hT2.le
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (Real.exp (β * T ^ 2) - 1 - β * T ^ 2) / T ^ 4 := ⟨_, rfl⟩
  have hpt : ∀ t ∈ Set.Icc (T / Real.exp 1) T,
      (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2) ≤ t ^ (-2 : ℝ) + β + K * t ^ 2 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    have ht2 : 0 < t ^ 2 := by positivity
    have hsq : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ ht0.le ht.2 2
    have hrw : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = t ^ 2 / T ^ 2 := ⟨_, rfl⟩
    have hl0 : 0 ≤ l := by rw [hl]; positivity
    have hl1 : l ≤ 1 := by rw [hl, div_le_one hT2]; exact hsq
    have hexp : Real.exp (β * t ^ 2)
        ≤ 1 + β * T ^ 2 * l + l ^ 2 * (Real.exp (β * T ^ 2) - 1 - β * T ^ 2) := by
      have : β * t ^ 2 = β * T ^ 2 * l := by
        rw [hl]
        field_simp
      rw [this]
      exact exp_mul_le_taylor hb0 hl0 hl1
    have hinv : (σ ^ 2 + t ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ :=
      inv_anti₀ ht2 (le_add_of_nonneg_left (sq_nonneg σ))
    have hE0 : 0 ≤ 1 + β * T ^ 2 * l + l ^ 2 * (Real.exp (β * T ^ 2) - 1 - β * T ^ 2) :=
      le_trans (Real.exp_pos _).le hexp
    have htne : t ≠ 0 := ht0.ne'
    have hTne : T ≠ 0 := hT.ne'
    calc (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2)
        ≤ (t ^ 2)⁻¹ * (1 + β * T ^ 2 * l
            + l ^ 2 * (Real.exp (β * T ^ 2) - 1 - β * T ^ 2)) :=
          mul_le_mul hinv hexp (Real.exp_pos _).le (inv_nonneg.2 ht2.le)
      _ = (t ^ 2)⁻¹ + β + K * t ^ 2 := by
          rw [hl, hK]
          field_simp
      _ = t ^ (-2 : ℝ) + β + K * t ^ 2 := by rw [hrw]
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Icc (T / Real.exp 1) T) :=
    continuousOn_id.rpow_const fun t ht => Or.inl (lt_of_lt_of_le ha0 ht.1).ne'
  have hcont1 : ContinuousOn (fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2))
      (Set.Icc (T / Real.exp 1) T) := by
    refine ContinuousOn.mul ?_ (by fun_prop : Continuous fun t : ℝ =>
      Real.exp (β * t ^ 2)).continuousOn
    refine ContinuousOn.inv₀ (by fun_prop : Continuous fun t : ℝ => σ ^ 2 + t ^ 2).continuousOn ?_
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    positivity
  have hcont2 : Continuous fun t : ℝ => K * t ^ 2 := by fun_prop
  have hval : (∫ t in Set.Icc (T / Real.exp 1) T, t ^ (-2 : ℝ))
      = (T / Real.exp 1)⁻¹ - T⁻¹ := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le haT,
      integral_rpow (Or.inr ⟨by norm_num, ?_⟩)]
    · rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, Real.rpow_neg_one]
      ring
    · rw [Set.uIcc_of_le haT]
      exact fun h => absurd h.1 (not_le.2 ha0)
  have hval2 : (∫ t in Set.Icc (T / Real.exp 1) T, K * t ^ 2)
      = K * ((T ^ 3 - (T / Real.exp 1) ^ 3) / 3) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le haT,
      intervalIntegral.integral_const_mul, integral_pow]
    ring
  have hi1 : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Icc (T / Real.exp 1) T) :=
    hcont.integrableOn_Icc
  have hi2 : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ) + β) (Set.Icc (T / Real.exp 1) T) :=
    hi1.add (integrable_const β)
  have hi3 : IntegrableOn (fun t : ℝ => K * t ^ 2) (Set.Icc (T / Real.exp 1) T) :=
    hcont2.integrableOn_Icc
  calc (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2))
      ≤ ∫ t in Set.Icc (T / Real.exp 1) T, (t ^ (-2 : ℝ) + β + K * t ^ 2) :=
        setIntegral_mono_on hcont1.integrableOn_Icc (hi2.add hi3) measurableSet_Icc hpt
    _ = (∫ t in Set.Icc (T / Real.exp 1) T, t ^ (-2 : ℝ))
          + (∫ _t in Set.Icc (T / Real.exp 1) T, β)
          + ∫ t in Set.Icc (T / Real.exp 1) T, K * t ^ 2 := by
        rw [integral_add hi2 hi3, integral_add hi1 (integrable_const β)]
    _ = ((T / Real.exp 1)⁻¹ - T⁻¹) + (T - T / Real.exp 1) * β
          + K * ((T ^ 3 - (T / Real.exp 1) ^ 3) / 3) := by
        rw [hval, hval2, setIntegral_const, Real.volume_real_Icc_of_le haT, smul_eq_mul]
    _ = ((Real.exp 1 - 1) + β * T ^ 2 * (1 - (Real.exp 1)⁻¹)
          + (Real.exp (β * T ^ 2) - 1 - β * T ^ 2) * (1 - (Real.exp 1)⁻¹ ^ 3) / 3) / T := by
        rw [hK]
        field_simp

/-! ### The split point of a window at slope `θ` -/

/-- The split point of the `k`-th window at slope `θ`: `⌈exp(θe^k)⌉`, so that
`log z_k ≥ θe^k = θ/T_k`. -/
noncomputable def thetaSplit (θ : ℝ) (k : ℕ) : ℕ := ⌈Real.exp (θ * Real.exp k)⌉₊

lemma exp_le_thetaSplit (θ : ℝ) (k : ℕ) : Real.exp (θ * Real.exp k) ≤ thetaSplit θ k :=
  Nat.le_ceil _

lemma mul_exp_le_log_thetaSplit (θ : ℝ) (k : ℕ) :
    θ * Real.exp k ≤ Real.log (thetaSplit θ k) := by
  have hpos : 0 < Real.exp (θ * Real.exp k) := Real.exp_pos _
  calc θ * Real.exp k = Real.log (Real.exp (θ * Real.exp k)) := (Real.log_exp _).symm
    _ ≤ Real.log (thetaSplit θ k) := Real.log_le_log hpos (exp_le_thetaSplit θ k)

lemma two_le_thetaSplit {θ : ℝ} (hθ : 1 ≤ θ) (k : ℕ) : 2 ≤ thetaSplit θ k := by
  have h1 : (1 : ℝ) ≤ θ * Real.exp k := by
    have := Real.one_le_exp (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    nlinarith
  have h2 : (2 : ℝ) < Real.exp (θ * Real.exp k) :=
    lt_of_lt_of_le (by linarith [Real.exp_one_gt_d9]) (Real.exp_le_exp.2 h1)
  have h3 : (2 : ℝ) < (thetaSplit θ k : ℝ) := lt_of_lt_of_le h2 (exp_le_thetaSplit θ k)
  exact_mod_cast h3.le

lemma thetaSplit_le {θ : ℝ} (hθ : 0 < θ) {k y : ℕ} (hky : θ * Real.exp k ≤ Real.log y) :
    thetaSplit θ k ≤ y := by
  have hy : (0 : ℝ) < (y : ℝ) := by
    by_contra h
    have h0 : (y : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg y)
    rw [h0, Real.log_zero] at hky
    have : 0 < θ * Real.exp k := mul_pos hθ (Real.exp_pos _)
    linarith
  refine Nat.ceil_le.2 ?_
  calc Real.exp (θ * Real.exp k) ≤ Real.exp (Real.log y) := Real.exp_le_exp.2 hky
    _ = y := Real.exp_log hy

lemma log_thetaSplit_add_one_le {θ : ℝ} (hθ : 1 ≤ θ) {k : ℕ} (hk : 2 ≤ k) :
    Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ≤ θ * Real.exp k + 1 / 100 := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have he : (7 : ℝ) ≤ Real.exp k := by
    have h1 : Real.exp 2 ≤ Real.exp k := Real.exp_le_exp.2 hk2
    have h2 : (7 : ℝ) ≤ Real.exp 2 := by
      have := Real.exp_one_gt_d9
      have h3 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [Real.exp_one_pow]; norm_num
      rw [h3]
      nlinarith
    linarith
  have he' : (7 : ℝ) ≤ θ * Real.exp k := by nlinarith
  have hbig : (200 : ℝ) ≤ Real.exp (θ * Real.exp k) := by
    have h1 : Real.exp 7 ≤ Real.exp (θ * Real.exp k) := Real.exp_le_exp.2 he'
    have h2 : (200 : ℝ) ≤ Real.exp 7 := by
      have := Real.exp_one_gt_d9
      have h3 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [Real.exp_one_pow]; norm_num
      rw [h3]
      have h4 : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith) 7
      linarith [show (200 : ℝ) ≤ 2.7 ^ 7 by norm_num]
    linarith
  have hceil : (thetaSplit θ k : ℝ) < Real.exp (θ * Real.exp k) + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  have h01 : (1 : ℝ) / 100 + 1 ≤ Real.exp (1 / 100) := Real.add_one_le_exp _
  have hle : ((thetaSplit θ k + 1 : ℕ) : ℝ) ≤ Real.exp (θ * Real.exp k) * Real.exp (1 / 100) := by
    push_cast
    nlinarith
  have hpos : (0 : ℝ) < ((thetaSplit θ k + 1 : ℕ) : ℝ) := by positivity
  calc Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ)
      ≤ Real.log (Real.exp (θ * Real.exp k) * Real.exp (1 / 100)) := Real.log_le_log hpos hle
    _ = θ * Real.exp k + 1 / 100 := by rw [← Real.exp_add, Real.log_exp]

/-! ### The constant of a window at slope `θ` -/

/-- The exponent of the two-point ratio on the `k`-th window at slope `θ`, `q = ½`, from above:
`½(θ + e^{-k}/100)² + 15.003(θe^{-k} + e^{-2k}/100) + 34e^{-2k}`. -/
noncomputable def thetaWindowExp (θ : ℝ) (k : ℕ) : ℝ :=
  (θ + Real.exp (-(k : ℝ)) / 100) ^ 2 / 2
    + 15.003 * (θ * Real.exp (-(k : ℝ)) + Real.exp (-(k : ℝ)) ^ 2 / 100)
    + 34 * Real.exp (-(k : ℝ)) ^ 2

/-- The square of the `k`-th window's constant at slope `θ`, `q = ½`:
`(2/θ)·W(b_k)·e^{9.0028/log y + 9.0028e^{-k}/θ}`, `W = RMF.taylorWindowW`,
`b_k = RMF.thetaWindowExp θ k`. -/
noncomputable def thetaWindowConst (θ : ℝ) (k y : ℕ) : ℝ :=
  2 / θ * taylorWindowW (thetaWindowExp θ k)
    * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ)

/-- **The ratio's exponent on the window**: `S₂(z_k + 1)·T_k² ≤ b_k`, from
`log(z_k + 1) ≤ θe^k + 1/100`. -/
lemma thetaWindow_beta_le {θ : ℝ} (hθ : 1 ≤ θ) {k : ℕ} (hk : 2 ≤ k) :
    (Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) + 34) * Real.exp (-(k : ℝ)) ^ 2
      ≤ thetaWindowExp θ k := by
  have hl0 : 0 ≤ Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ thetaSplit θ k + 1))
  have hl1 := log_thetaSplit_add_one_le hθ hk
  have hEk : Real.exp k * Real.exp (-(k : ℝ)) = 1 := by rw [← Real.exp_add]; simp
  have hmono : Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) + 34
      ≤ (θ * Real.exp k + 1 / 100) ^ 2 / 2 + 15.003 * (θ * Real.exp k + 1 / 100) + 34 := by
    have h2 : Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ^ 2 ≤ (θ * Real.exp k + 1 / 100) ^ 2 :=
      pow_le_pow_left₀ hl0 hl1 2
    linarith
  calc (Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) + 34) * Real.exp (-(k : ℝ)) ^ 2
      ≤ ((θ * Real.exp k + 1 / 100) ^ 2 / 2 + 15.003 * (θ * Real.exp k + 1 / 100) + 34)
          * Real.exp (-(k : ℝ)) ^ 2 := mul_le_mul_of_nonneg_right hmono (sq_nonneg _)
    _ = thetaWindowExp θ k := by
        rw [thetaWindowExp]
        linear_combination (θ ^ 2 * (Real.exp k * Real.exp (-(k : ℝ)) + 1) / 2
          + θ * Real.exp (-(k : ℝ)) / 100 + 15.003 * θ * Real.exp (-(k : ℝ))) * hEk

lemma exp_one_inv_le : (Real.exp 1)⁻¹ ≤ 37 / 100 := by
  rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
  linarith [Real.exp_one_gt_d9]

lemma taylorWindowW_nonneg {b : ℝ} (hb : 0 ≤ b) : 0 ≤ taylorWindowW b := by
  unfold taylorWindowW
  have h1 := one_sub_exp_one_inv_pos
  have h2 : 0 ≤ Real.exp b - 1 - b := by linarith [Real.add_one_le_exp b]
  have h3 : 0 ≤ 1 - (Real.exp 1)⁻¹ ^ 3 := by
    have h4 : (Real.exp 1)⁻¹ ^ 3 ≤ 1 :=
      pow_le_one₀ (inv_nonneg.2 (Real.exp_pos 1).le) (by linarith)
    linarith
  have h5 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.exp_one_gt_d9]
  have := mul_nonneg hb h1.le
  have := mul_nonneg h2 h3
  positivity

lemma taylorWindowW_mono {b b' : ℝ} (hbb : b ≤ b') : taylorWindowW b ≤ taylorWindowW b' := by
  unfold taylorWindowW
  have hinv := exp_one_inv_le
  have hinv0 : 0 ≤ (Real.exp 1)⁻¹ := inv_nonneg.2 (Real.exp_pos 1).le
  have hc0 : 0 ≤ 1 - (Real.exp 1)⁻¹ ^ 3 := by
    have h4 : (Real.exp 1)⁻¹ ^ 3 ≤ 1 := pow_le_one₀ hinv0 (by linarith)
    linarith
  have hc1 : 1 - (Real.exp 1)⁻¹ ^ 3 ≤ 1 := by
    have := pow_nonneg hinv0 3
    linarith
  have he : Real.exp b ≤ Real.exp b' := Real.exp_le_exp.2 hbb
  -- `W(b) = (e-1) + b(1 - e⁻¹ - c) + (e^b - 1)c`, `c = (1 - e⁻³)/3 ≤ 1/3 < 1 - e⁻¹`
  have h1 : 0 ≤ (b' - b) * (1 - (Real.exp 1)⁻¹ - (1 - (Real.exp 1)⁻¹ ^ 3) / 3) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (Real.exp b' - Real.exp b) * ((1 - (Real.exp 1)⁻¹ ^ 3) / 3) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- **The window's weight and mean at `q = ½`, against the window's constant**, at slope `θ`:
`(2/log y)·(W(βT²)/T)·(log y/log z_k)e^{9.0028/log y + 9.0028/log z_k} ≤ G_k²` since
`T log z_k ≥ θ`. -/
lemma two_div_mul_window_le_thetaWindowConst {θ : ℝ} (hθ : 1 ≤ θ) {k y : ℕ} (hk : 2 ≤ k)
    (hky : θ * Real.exp k ≤ Real.log y) :
    2 / Real.log y * (taylorWindowW ((Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) + 34) * Real.exp (-(k : ℝ)) ^ 2)
          / Real.exp (-(k : ℝ))
        * (Real.log y / Real.log (thetaSplit θ k)
          * Real.exp (9.0028 / Real.log y + 9.0028 / Real.log (thetaSplit θ k))))
      ≤ thetaWindowConst θ k y := by
  have hθ0 : 0 < θ := by linarith
  have hek : (1 : ℝ) ≤ Real.exp k := Real.one_le_exp (Nat.cast_nonneg k)
  have hlogy : 0 < Real.log y := lt_of_lt_of_le (by nlinarith) hky
  have hlz := mul_exp_le_log_thetaSplit θ k
  have hlz0 : 0 < Real.log (thetaSplit θ k) := lt_of_lt_of_le (by positivity) hlz
  have hT0 : 0 < Real.exp (-(k : ℝ)) := Real.exp_pos _
  have hEk : Real.exp k * Real.exp (-(k : ℝ)) = 1 := by rw [← Real.exp_add]; simp
  set b := (Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ^ 2 / 2
    + 15.003 * Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) + 34) * Real.exp (-(k : ℝ)) ^ 2
    with hbdef
  have hb0 : 0 ≤ b := by
    have hl0 : 0 ≤ Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ thetaSplit θ k + 1))
    positivity
  have hbk : b ≤ thetaWindowExp θ k := thetaWindow_beta_le hθ hk
  have hW0 : 0 ≤ taylorWindowW b := taylorWindowW_nonneg hb0
  have hWW : taylorWindowW b ≤ taylorWindowW (thetaWindowExp θ k) := taylorWindowW_mono hbk
  -- `T·log z ≥ θ` and `9.0028/log z ≤ 9.0028·T/θ`
  have hTz : θ ≤ Real.exp (-(k : ℝ)) * Real.log (thetaSplit θ k) := by
    calc θ = Real.exp (-(k : ℝ)) * (θ * Real.exp k) := by
          rw [mul_comm θ, ← mul_assoc, mul_comm (Real.exp (-(k : ℝ))), hEk, one_mul]
      _ ≤ Real.exp (-(k : ℝ)) * Real.log (thetaSplit θ k) :=
          mul_le_mul_of_nonneg_left hlz hT0.le
  have hinv : 9.0028 / Real.log (thetaSplit θ k) ≤ 9.0028 * Real.exp (-(k : ℝ)) / θ := by
    rw [div_le_div_iff₀ hlz0 hθ0]
    nlinarith
  have hexp : Real.exp (9.0028 / Real.log y + 9.0028 / Real.log (thetaSplit θ k))
      ≤ Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ) :=
    Real.exp_le_exp.2 (by linarith)
  set Ex := Real.exp (9.0028 / Real.log y + 9.0028 / Real.log (thetaSplit θ k)) with hExdef
  have hEx0 : 0 ≤ Ex := (Real.exp_pos _).le
  have heq : 2 / Real.log y * (taylorWindowW b / Real.exp (-(k : ℝ))
      * (Real.log y / Real.log (thetaSplit θ k) * Ex))
      = 2 * taylorWindowW b * Ex / (Real.exp (-(k : ℝ)) * Real.log (thetaSplit θ k)) := by
    field_simp
  rw [heq, thetaWindowConst]
  rw [div_le_iff₀ (mul_pos hT0 hlz0)]
  have h1 : 2 * taylorWindowW b * Ex ≤ 2 * taylorWindowW (thetaWindowExp θ k)
      * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hWW (by norm_num)) hexp hEx0
      (mul_nonneg (by norm_num) (le_trans hW0 hWW))
  have hG0 : 0 ≤ 2 / θ * taylorWindowW (thetaWindowExp θ k)
      * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ) := by
    have : 0 ≤ taylorWindowW (thetaWindowExp θ k) := le_trans hW0 hWW
    positivity
  have h3 : 2 / θ * taylorWindowW (thetaWindowExp θ k)
      * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ) * θ
      ≤ 2 / θ * taylorWindowW (thetaWindowExp θ k)
      * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ)
      * (Real.exp (-(k : ℝ)) * Real.log (thetaSplit θ k)) :=
    mul_le_mul_of_nonneg_left hTz hG0
  have h4 : 2 / θ * taylorWindowW (thetaWindowExp θ k)
      * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ) * θ
      = 2 * taylorWindowW (thetaWindowExp θ k)
      * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ) := by
    field_simp
  linarith

/-! ### One window at `q = ½` and slope `θ` -/

/-- **One window at `q = ½`, split at slope `θ`, by Jensen**: for `1 ≤ θ`, `k ≥ 2` with
`θe^k ≤ log y` and `σ > 0`,
`(2/log y)^{1/2}·E[(∫_{T_k/e}^{T_k}(σ²+t²)⁻¹‖F_{y+1}(½+σ+it)‖²dt)^{1/2}] ≤ G_k`,
`G_k² = RMF.thetaWindowConst θ k y`.  `RMF.integral_rpow_window_le_split_jensen_of_weight` at
`z = RMF.thetaSplit θ k`, `T = e^{-k}`, `β = S₂(z+1)`, the weight to second order
(`RMF.setIntegral_inv_sq_add_sq_mul_exp_window_le_taylor`) and `E‖F_{z+1}(½+σ)‖ ≤ 1`
(`RMF.integral_norm_randomEulerProduct_shiftLine_half_le_one`). -/
theorem window_theta_le_jensen {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {θ : ℝ} (hθ : 1 ≤ θ) {k y : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (hk : 2 ≤ k) (hky : θ * Real.exp k ≤ Real.log y) :
    (2 / Real.log y) ^ (1 / 2 : ℝ) * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
        (Real.exp (-(k : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂ν
      ≤ thetaWindowConst θ k y ^ (1 / 2 : ℝ) := by
  have hθ0 : 0 < θ := by linarith
  have hek : (1 : ℝ) ≤ Real.exp k := Real.one_le_exp (Nat.cast_nonneg k)
  have hlogy : 0 < Real.log y := lt_of_lt_of_le (by nlinarith) hky
  have hz2 := two_le_thetaSplit hθ k
  have hzy := thetaSplit_le hθ0 hky
  set β := Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) + 34 with hβdef
  have hβ0 : 0 ≤ β := by
    have hl0 : 0 ≤ Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ thetaSplit θ k + 1))
    positivity
  have hR := setIntegral_inv_sq_add_sq_mul_exp_window_le_taylor σ (Real.exp_pos (-(k : ℝ))) hβ0
  have h := integral_rpow_window_le_split_jensen_of_weight hY hz2 hzy (σ := σ) (q := 1 / 2)
    (T := Real.exp (-(k : ℝ))) (β := β) hσ (by norm_num) le_rfl (Real.exp_pos _)
    (le_of_eq (by rw [hβdef]; ring)) hR
  have hPF := integral_norm_randomEulerProduct_shiftLine_half_le_one hY hz2 hσ.le
  have hW := two_div_mul_window_le_thetaWindowConst hθ hk hky
  set Q := taylorWindowW (β * Real.exp (-(k : ℝ)) ^ 2) / Real.exp (-(k : ℝ))
      * (Real.log y / Real.log (thetaSplit θ k)
        * Real.exp (9.0028 / Real.log y + 9.0028 / Real.log (thetaSplit θ k))) with hQdef
  have hQ0 : 0 ≤ Q := by
    have hlz0 : 0 < Real.log (thetaSplit θ k) :=
      lt_of_lt_of_le (by positivity) (mul_exp_le_log_thetaSplit θ k)
    have h1 : 0 ≤ taylorWindowW (β * Real.exp (-(k : ℝ)) ^ 2) :=
      taylorWindowW_nonneg (by positivity)
    positivity
  have hstep : (∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1) (Real.exp (-(k : ℝ))),
      (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂ν) ≤ Q ^ (1 / 2 : ℝ) :=
    le_trans h (mul_le_of_le_one_left (Real.rpow_nonneg hQ0 _) hPF)
  have h2y : (0 : ℝ) ≤ (2 / Real.log y) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  calc (2 / Real.log y) ^ (1 / 2 : ℝ) * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
        (Real.exp (-(k : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂ν
      ≤ (2 / Real.log y) ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hstep h2y
    _ = (2 / Real.log y * Q) ^ (1 / 2 : ℝ) := (Real.mul_rpow (by positivity) hQ0).symm
    _ ≤ thetaWindowConst θ k y ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (mul_nonneg (by positivity) hQ0) hW (by norm_num)

/-- **One window at `q = ½`, split at slope `θ`, by the weighted chaos**: for `1 ≤ θ ≤ 2`,
`97 ≤ k` with `k + 8 ≤ ⌊log log y⌋`, the offset `D = k + 8`, `σ log y ≤ E₀ ≤ 1/10` and the
chaos's parameters,

`(2/log y)^{1/2}·E[(∫_{T_k/e}^{T_k}(σ²+t²)⁻¹‖F_{y+1}(½+σ+it)‖²dt)^{1/2}]
  ≤ G_k·shiftMomentConst 1 C_i (C_b e⁸) A s λ δ ½·(1 + √n/2)^{-1/2}`,

`n = harperBlockCount (k+8) y`: `RMF.integral_rpow_window_le_split_chaos_of_weight` at
`z = RMF.thetaSplit θ k`, `T = e^{-k}`, `K_ϑ = e⁸`, the weight to second order. -/
theorem window_theta_le_chaos (E₀ βc : ℝ) (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 10)
    (hβc : 1 / 2 < βc) (hβc2 : βc ≤ 2) {Tr κ Amax δ : ℝ} {N : ℕ} (hTr : 4 < Tr)
    (hκ : 1 ≤ κ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δ * N)
    (hmono : 3 ≤ 8 * δ * Real.sqrt (N : ℝ))
    {Y : ℕ → Ω → ℂ} {ν : Measure Ω} (hY : IsRademacherPrimeValues Y ν) {θ : ℝ} (hθ : 1 ≤ θ)
    (hθ2 : θ ≤ 2) {k y : ℕ} {σ A lam : ℝ}
    (hσ : 0 < σ) (hk : 97 ≤ k) (hky : k + 8 ≤ ⌊Real.log (Real.log y)⌋₊)
    (hσy : σ * Real.log y ≤ E₀) (hNn : N ≤ harperBlockCount (k + 8) y)
    (hA : radBlockBadLevel E₀ ≤ A) (hAmax : A ≤ Amax) (hlam : 1 ≤ lam) :
    (2 / Real.log y) ^ (1 / 2 : ℝ) * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
        (Real.exp (-(k : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂ν
      ≤ thetaWindowConst θ k y ^ (1 / 2 : ℝ)
        * (shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ) (radBlockBadConst E₀ βc * Real.exp 8)
            A (radAveragedShift E₀ βc Tr κ) lam δ (1 / 2)
          * (1 + (1 - 1 / 2) * Real.sqrt (harperBlockCount (k + 8) y : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  have hk2 : 2 ≤ k := by omega
  have hθ0 : 0 < θ := by linarith
  -- `log log y ≥ k + 8`
  have hLL : ((k + 8 : ℕ) : ℝ) ≤ Real.log (Real.log y) :=
    (Nat.le_floor_iff' (by omega)).1 hky
  have hkR : (97 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hy2 : 2 ≤ y := by
    by_contra hcon
    have hy1 : y ≤ 1 := by omega
    have h0 : Real.log (Real.log y) = 0 := by
      interval_cases y <;> simp
    rw [h0] at hLL
    have : (0 : ℝ) < ((k + 8 : ℕ) : ℝ) := by positivity
    linarith
  have hlogy : 0 < Real.log y :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  -- `θe^k ≤ e^{k+1} ≤ log y`
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hθek : θ * Real.exp k ≤ Real.exp ((k : ℝ) + 1) := by
    calc θ * Real.exp k ≤ 2 * Real.exp k := mul_le_mul_of_nonneg_right hθ2 (Real.exp_pos _).le
      _ ≤ Real.exp 1 * Real.exp k := mul_le_mul_of_nonneg_right he1 (Real.exp_pos _).le
      _ = Real.exp ((k : ℝ) + 1) := by rw [Real.exp_add, mul_comm]
  have hky' : θ * Real.exp k ≤ Real.log y := by
    refine le_trans hθek ?_
    calc Real.exp ((k : ℝ) + 1) ≤ Real.exp (Real.log (Real.log y)) :=
          Real.exp_le_exp.2 (by push_cast at hLL; linarith)
      _ = Real.log y := Real.exp_log hlogy
  -- the offset
  have hϑlo : (k : ℝ) + 7 ≤ harperOffset (k + 8) y := by
    have := sub_one_le_harperOffset (k + 8) (y : ℝ)
    push_cast at this
    linarith
  have hϑhi : harperOffset (k + 8) y < (k : ℝ) + 8 := by
    have := harperOffset_lt_natCast (k + 8) (y : ℝ)
    push_cast at this
    linarith
  have hϑ104 : (104 : ℝ) ≤ harperOffset (k + 8) y := by linarith
  have hϑ : radFreeStartThreshold E₀ ≤ harperOffset (k + 8) y :=
    le_trans (radFreeStartThreshold_le_104 hE₀ (by linarith)) hϑ104
  -- the window's conditions
  have hT1 : Real.exp (-(k : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hlo : 600 * Real.exp (2 * E₀) ≤ 2 * (Real.exp (-(k : ℝ)) / Real.exp 1)
      * Real.exp (harperOffset (k + 8) y) := by
    have h1 : 2 * (Real.exp (-(k : ℝ)) / Real.exp 1) * Real.exp (harperOffset (k + 8) y)
        = 2 * Real.exp (harperOffset (k + 8) y - k - 1) := by
      rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    rw [h1]
    have h2 : Real.exp 6 ≤ Real.exp (harperOffset (k + 8) y - k - 1) :=
      Real.exp_le_exp.2 (by linarith)
    have h3 : (403 : ℝ) ≤ Real.exp 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
      have := Real.exp_one_gt_d9
      have h4 : (2.718 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith) 6
      linarith [show (403 : ℝ) ≤ 2.718 ^ 6 by norm_num]
    have h5 : Real.exp (2 * E₀) ≤ Real.exp (1 / 5) := Real.exp_le_exp.2 (by linarith)
    have h6 := exp_one_fifth_le
    linarith
  have hKθ : Real.exp (-(k : ℝ)) * Real.exp (harperOffset (k + 8) y) ≤ Real.exp 8 := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hzb : ((thetaSplit θ k + 1 : ℕ) : ℝ) ≤ blockScale (harperOffset (k + 8) y) 0 := by
    have hl := log_thetaSplit_add_one_le hθ hk2
    have hpos : (0 : ℝ) < ((thetaSplit θ k + 1 : ℕ) : ℝ) := by positivity
    have h1 : ((thetaSplit θ k + 1 : ℕ) : ℝ) ≤ Real.exp (θ * Real.exp k + 1 / 100) :=
      (Real.log_le_iff_le_exp hpos).1 hl
    refine le_trans h1 ?_
    rw [blockScale]
    refine Real.exp_le_exp.2 ?_
    have h2 : Real.exp ((k : ℝ) + 2) ≤ Real.exp (((0 : ℕ) : ℝ) + harperOffset (k + 8) y) :=
      Real.exp_le_exp.2 (by push_cast; linarith)
    have h3 : Real.exp ((k : ℝ) + 2) = Real.exp ((k : ℝ) + 1) * Real.exp 1 := by
      rw [← Real.exp_add]
      ring_nf
    have h4 : (1 : ℝ) ≤ Real.exp ((k : ℝ) + 1) := Real.one_le_exp (by positivity)
    have h6 : Real.exp ((k : ℝ) + 1) * 2 ≤ Real.exp ((k : ℝ) + 1) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left he1 (Real.exp_pos _).le
    calc θ * Real.exp k + 1 / 100 ≤ Real.exp ((k : ℝ) + 1) * 2 := by linarith
      _ ≤ Real.exp ((k : ℝ) + 1) * Real.exp 1 := h6
      _ = Real.exp ((k : ℝ) + 2) := h3.symm
      _ ≤ _ := h2
  set β := Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) + 34 with hβdef
  have hβ0 : 0 ≤ β := by
    have hl0 : 0 ≤ Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ thetaSplit θ k + 1))
    positivity
  have hβ : 2 * (1 - 1 / 2 : ℝ) * (Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) + 34) ≤ β :=
    le_of_eq (by rw [hβdef]; ring)
  have hR := setIntegral_inv_sq_add_sq_mul_exp_window_le_taylor σ (Real.exp_pos (-(k : ℝ))) hβ0
  have h := integral_rpow_window_le_split_chaos_of_weight E₀ βc hE₀ (by linarith) hβc hβc2 hTr
    hκ hδ0 hδ hN hmono hY (two_le_thetaSplit hθ k) (thetaSplit_le hθ0 hky') (D := k + 8)
    (σ := σ) (η := E₀) (q := 1 / 2) (T := Real.exp (-(k : ℝ))) (Kθ := Real.exp 8) (A := A)
    (lam := lam) hσ (by norm_num) le_rfl (Real.exp_pos _) hT1 hβ hLL hϑ hϑ104 hE₀ le_rfl hσy
    hlo hKθ hzb hNn hA hAmax hlam hR
  have hPF := integral_norm_randomEulerProduct_shiftLine_half_le_one hY (two_le_thetaSplit hθ k)
    hσ.le
  have hW := two_div_mul_window_le_thetaWindowConst hθ hk2 hky'
  set Q := taylorWindowW (β * Real.exp (-(k : ℝ)) ^ 2) / Real.exp (-(k : ℝ))
      * (Real.log y / Real.log (thetaSplit θ k)
        * Real.exp (9.0028 / Real.log y + 9.0028 / Real.log (thetaSplit θ k))) with hQdef
  have hQ0 : 0 ≤ Q := by
    have hlz0 : 0 < Real.log (thetaSplit θ k) :=
      lt_of_lt_of_le (by positivity) (mul_exp_le_log_thetaSplit θ k)
    have h1 : 0 ≤ taylorWindowW (β * Real.exp (-(k : ℝ)) ^ 2) :=
      taylorWindowW_nonneg (by positivity)
    positivity
  set C := shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ) (radBlockBadConst E₀ βc * Real.exp 8)
    A (radAveragedShift E₀ βc Tr κ) lam δ (1 / 2) with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef, shiftMomentConst]
    exact le_trans (Real.rpow_nonneg (by positivity) _) (le_max_left _ _)
  set G := (1 + (1 - 1 / 2) * Real.sqrt (harperBlockCount (k + 8) y : ℝ)) ^ (-(1 / 2 : ℝ))
    with hGdef
  have hG0 : 0 ≤ G := Real.rpow_nonneg (by positivity) _
  have hQq : 0 ≤ Q ^ (1 / 2 : ℝ) := Real.rpow_nonneg hQ0 _
  have hCQG : 0 ≤ C * Q ^ (1 / 2 : ℝ) * G := by positivity
  have hstep : (∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1) (Real.exp (-(k : ℝ))),
      (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂ν) ≤ C * Q ^ (1 / 2 : ℝ) * G :=
    le_trans h (mul_le_of_le_one_left hCQG hPF)
  have h2y : (0 : ℝ) ≤ (2 / Real.log y) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  calc (2 / Real.log y) ^ (1 / 2 : ℝ) * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
        (Real.exp (-(k : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂ν
      ≤ (2 / Real.log y) ^ (1 / 2 : ℝ) * (C * Q ^ (1 / 2 : ℝ) * G) :=
        mul_le_mul_of_nonneg_left hstep h2y
    _ = (2 / Real.log y * Q) ^ (1 / 2 : ℝ) * (C * G) := by
        rw [Real.mul_rpow (by positivity) hQ0]
        ring
    _ ≤ thetaWindowConst θ k y ^ (1 / 2 : ℝ) * (C * G) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (mul_nonneg (by positivity) hQ0) hW (by norm_num))
          (mul_nonneg hC0 hG0)

end RMF
