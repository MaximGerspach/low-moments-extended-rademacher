/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.UpperSieve

/-!
# Harper's upper bound with a Jensen switch point

`RMF.harper_upper_of_chaos_sieve` bounds the moments on `[2/3, 1]`; descending below `2/3` by
Jensen is free once the constant is at least `e^{4/3}`.  The chain's constant is largest at the
bottom of its range, so it pays to switch higher.  At `p ∈ [2/3, 1)` the chain gives
`C_p = k·R(p)·K(p) + η`, and for `q ≤ p`

`E|S_x|^{2q} ≤ (E|S_x|^{2p})^{q/p} ≤ C_p^{q/p}((1-q)/(1-p))^q·(1 + (1-q)√(log log x))^{-q}`.

The constant on the right can stay below the chain's constant at `p` for every `q ≤ p` once it is
allowed to exceed `C_p` a little, so no condition of the form `C ≥ e^{p²/(1-p)}` is needed.

* `RMF.integral_rpow_le_rpow_integral_of_le`: `E|S|^{2q} ≤ (E|S|^{2p})^{q/p}` for `0 ≤ q ≤ p`;
* `RMF.le_target_of_le_switch`: the target's shift from `p` to `q` costs `((1-q)/(1-p))^q`;
* `RMF.upperSwitchConst` and `RMF.harper_upper_full_of_chaos_sieve_switch`: the bound for every
  `q ∈ [0, 1]`, with the chain above `p` and the descent below;
* `RMF.harper_upper_averaged_sieve_switch`: the same at the averaged free start;
* `RMF.switchDescent_le_of_end`: the descent's constant on `[q₁, q₂]` from its endpoints.
-/

open MeasureTheory
open scoped Real ENNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Jensen between two moments**: on a probability space, `E|S|^{2q} ≤ (E|S|^{2p})^{q/p}` for
`0 ≤ q ≤ p`, by `L^p` monotonicity (`RMF.integral_rpow_le_rpow_integral_of_le_two_thirds` is
`p = 2/3`). -/
theorem integral_rpow_le_rpow_integral_of_le {S : Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {p q : ℝ} (hq0 : 0 ≤ q) (hqp : q ≤ p)
    (hS : MemLp S (ENNReal.ofReal (2 * p)) μ) :
    (∫ ω, ‖S ω‖ ^ (2 * q) ∂μ) ≤ (∫ ω, ‖S ω‖ ^ (2 * p) ∂μ) ^ (q / p) := by
  have hIq : (0 : ℝ) ≤ ∫ ω, ‖S ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hIp : (0 : ℝ) ≤ ∫ ω, ‖S ω‖ ^ (2 * p) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  rcases eq_or_lt_of_le hq0 with hq0' | hq0'
  · -- `q = 0`: both sides are `1`
    subst hq0'
    simp
  have hp : 0 < p := lt_of_lt_of_le hq0' hqp
  have h2q : (0 : ℝ) < 2 * q := by linarith
  have h2p : (0 : ℝ) < 2 * p := by linarith
  have hple : ENNReal.ofReal (2 * q) ≤ ENNReal.ofReal (2 * p) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hSq : MemLp S (ENNReal.ofReal (2 * q)) μ := hS.mono_exponent hple
  have hmono := eLpNorm_le_eLpNorm_of_exponent_le hple hS.aestronglyMeasurable (μ := μ)
  rw [hSq.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.2 h2q).ne' ENNReal.ofReal_ne_top,
    hS.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.2 h2p).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal h2q.le, ENNReal.toReal_ofReal h2p.le] at hmono
  have hkey : (∫ ω, ‖S ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
      ≤ (∫ ω, ‖S ω‖ ^ (2 * p) ∂μ) ^ (2 * p)⁻¹ :=
    (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hIp _)).1 hmono
  have hexp : (2 * p)⁻¹ * (2 * q) = q / p := by
    field_simp
  calc ∫ ω, ‖S ω‖ ^ (2 * q) ∂μ
      = ((∫ ω, ‖S ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹) ^ (2 * q) := by
        rw [← Real.rpow_mul hIq, inv_mul_cancel₀ h2q.ne', Real.rpow_one]
    _ ≤ ((∫ ω, ‖S ω‖ ^ (2 * p) ∂μ) ^ (2 * p)⁻¹) ^ (2 * q) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hIq _) hkey h2q.le
    _ = (∫ ω, ‖S ω‖ ^ (2 * p) ∂μ) ^ (q / p) := by
        rw [← Real.rpow_mul hIp, hexp]

/-- **The normalised partial sum is in every `L^r`** (`RMF.IsSteinhausRMF.memLp_normalisedSum` is
`r = 4/3`). -/
lemma IsSteinhausRMF.memLp_normalisedSum_of {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) (x : ℝ) (r : ℝ≥0∞) : MemLp (normalisedSum f x) r μ := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  exact (memLp_top_of_bound (hf.measurable_normalisedSum x).aestronglyMeasurable _
    (hf.ae_norm_normalisedSum_le x)).mono_exponent le_top

/-- **The target's shift from `p` down to `q`**: for `0 ≤ q ≤ p < 1` and `t ≥ 0`, a bound
`I_p ≤ C_p(1 + (1-p)t)^{-p}` and `I_q ≤ I_p^{q/p}` give
`I_q ≤ C_p^{q/p}((1-q)/(1-p))^q(1 + (1-q)t)^{-q}`, since
`1 + (1-q)t ≤ ((1-q)/(1-p))(1 + (1-p)t)`. -/
lemma le_target_of_le_switch {Ip Iq Cp t p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (ht0 : 0 ≤ t)
    (hq0 : 0 ≤ q) (hqp : q ≤ p) (hIp0 : 0 ≤ Ip) (hdesc : Iq ≤ Ip ^ (q / p))
    (hIp : Ip ≤ Cp * (1 + (1 - p) * t) ^ (-p)) :
    Iq ≤ Cp ^ (q / p) * ((1 - q) / (1 - p)) ^ q * (1 + (1 - q) * t) ^ (-q) := by
  have hp0 : p ≠ 0 := hp.ne'
  have hA0 : 0 < 1 + (1 - p) * t := by nlinarith
  have hT0 : 0 < 1 + (1 - q) * t := by nlinarith
  have hr0 : 0 < (1 - q) / (1 - p) := div_pos (by linarith) (by linarith)
  have hqp0 : 0 ≤ q / p := div_nonneg hq0 hp.le
  have hCp0 : 0 ≤ Cp := by
    by_contra hneg
    have : Cp * (1 + (1 - p) * t) ^ (-p) < 0 :=
      mul_neg_of_neg_of_pos (not_le.1 hneg) (Real.rpow_pos_of_pos hA0 _)
    linarith
  -- Jensen, then the bound at `p`
  have h1 : Ip ^ (q / p) ≤ (Cp * (1 + (1 - p) * t) ^ (-p)) ^ (q / p) :=
    Real.rpow_le_rpow hIp0 hIp hqp0
  have hexp : -p * (q / p) = -q := by
    field_simp
  have h2 : (Cp * (1 + (1 - p) * t) ^ (-p)) ^ (q / p)
      = Cp ^ (q / p) * (1 + (1 - p) * t) ^ (-q) := by
    rw [Real.mul_rpow hCp0 (Real.rpow_nonneg hA0.le _), ← Real.rpow_mul hA0.le, hexp]
  -- the shift in the target
  have hAT : (1 + (1 - p) * t) ^ (-q) ≤ ((1 - q) / (1 - p)) ^ q * (1 + (1 - q) * t) ^ (-q) := by
    have hTA : 1 + (1 - q) * t ≤ (1 - q) / (1 - p) * (1 + (1 - p) * t) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      nlinarith
    have h3 : ((1 - q) / (1 - p) * (1 + (1 - p) * t)) ^ (-q) ≤ (1 + (1 - q) * t) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos hT0 hTA (by linarith)
    rw [Real.mul_rpow hr0.le hA0.le] at h3
    have hpos : (0 : ℝ) < ((1 - q) / (1 - p)) ^ q := Real.rpow_pos_of_pos hr0 q
    have hmul := mul_le_mul_of_nonneg_left h3 hpos.le
    rwa [← mul_assoc, ← Real.rpow_add hr0, add_neg_cancel, Real.rpow_zero, one_mul] at hmul
  calc Iq ≤ Ip ^ (q / p) := hdesc
    _ ≤ Cp ^ (q / p) * (1 + (1 - p) * t) ^ (-q) := h1.trans h2.le
    _ ≤ Cp ^ (q / p) * (((1 - q) / (1 - p)) ^ q * (1 + (1 - q) * t) ^ (-q)) :=
        mul_le_mul_of_nonneg_left hAT (Real.rpow_nonneg hCp0 _)
    _ = Cp ^ (q / p) * ((1 - q) / (1 - p)) ^ q * (1 + (1 - q) * t) ^ (-q) := by ring

/-- **The constant at `q` with the switch point `p`**: the chain's `k·R(q)·K(q) + η` for `q ≥ p`,
and below `p` the descent `C_p^{q/p}((1-q)/(1-p))^q` from `C_p = k·R(p)·K(p) + η`. -/
noncomputable def upperSwitchConst (K : ℝ → ℝ) (k η p q : ℝ) : ℝ :=
  if p ≤ q then k * reductionSieveConst q * K q + η
  else (k * reductionSieveConst p * K p + η) ^ (q / p) * ((1 - q) / (1 - p)) ^ q

/-- **Harper's upper bound for every `q ∈ [0, 1]` with a switch point `p ∈ [2/3, 1)`**: past
`exp(exp Λ)`, `E|S_x|^{2q} ≤ upperSwitchConst K k η p q·(1 + (1-q)√(log log x))^{-q}`.  Above `p`
this is `RMF.harper_upper_of_chaos_sieve`; below, Jensen from `p`
(`RMF.integral_rpow_le_rpow_integral_of_le`) and the target's shift
(`RMF.le_target_of_le_switch`). -/
theorem harper_upper_full_of_chaos_sieve_switch {K : ℝ → ℝ} {ℓ₀ k η Λ p : ℝ} (hk : 1 < k)
    (hη : 0 < η) (hp23 : 2 / 3 ≤ p) (hp1 : p < 1)
    (hℓ₀ : 1000000 ≤ Real.exp ℓ₀) (hΛ36 : 36 ≤ Λ) (hΛℓ : ℓ₀ + 1 + 2 * Real.log Λ ≤ Λ)
    (hΛk : k ^ 2 * (2 * Real.log Λ + 1) ≤ (k ^ 2 - 1) * Λ)
    (hΛC : 3 * (|Real.log reductionUpperConst| + reductionUpperExponent) / reductionUpperDecay
      ≤ Λ)
    (hΛη : 6 * (1 + |Real.log η|) / reductionUpperDecay ≤ Λ)
    (hchaos : ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ y q : ℝ, Real.exp (Real.exp ℓ₀) ≤ y → 2 / 3 ≤ q → q ≤ 1 →
        ∫ ω, chaosUnit f y ω ^ q ∂μ
          ≤ K q * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q)) :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ x q : ℝ, Real.exp (Real.exp Λ) ≤ x → 0 ≤ q → q ≤ 1 →
        ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
          ≤ upperSwitchConst K k η p q
            * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  have hup := harper_upper_of_chaos_sieve hk hη hℓ₀ hΛ36 hΛℓ hΛk hΛC hΛη hchaos
  intro f μ hf x q hx hq0 hq1
  have ht0 : (0 : ℝ) ≤ Real.sqrt (Real.log (Real.log x)) := Real.sqrt_nonneg _
  unfold upperSwitchConst
  split_ifs with hpq
  · exact hup f μ hf x q hx (le_trans hp23 hpq) hq1
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have hqp : q < p := not_le.1 hpq
  have hp : 0 < p := by linarith
  exact le_target_of_le_switch hp hp1 ht0 hq0 hqp.le
    (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _)
    (integral_rpow_le_rpow_integral_of_le hq0 hqp.le (hf.memLp_normalisedSum_of x _))
    (hup f μ hf x p hx hp23 hp1.le)

/-- **Harper's upper bound at the averaged free start with a switch point `p ∈ [2/3, 1)`**:
`RMF.harper_upper_full_of_chaos_sieve_switch` with the chaos moments of
`RMF.integral_chaosUnit_rpow_le_averaged`. -/
theorem harper_upper_averaged_sieve_switch {A lam T κ β : ℝ → ℝ} {Amax δ k η L₀ ℓ₀ Λ p : ℝ}
    {N : ℕ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hk : 1 < k) (hη : 0 < η) (hL₀ : 1 ≤ L₀)
    (hp23 : 2 / 3 ≤ p) (hp1 : p < 1)
    (hA : ∀ q, harperBadLevel 0 ≤ A q ∧ A q ≤ Amax) (hlam : ∀ q, 1 ≤ lam q)
    (hT : ∀ q, 4 < T q) (hκ : ∀ q, 1 ≤ κ q) (hβ : ∀ q, 1 / 2 < β q ∧ β q ≤ 2)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δ * N)
    (hmono : 3 ≤ 8 * δ * Real.sqrt (N : ℝ)) (hℓN : (freeStartHarperD 0 : ℝ) + N ≤ ℓ₀)
    (hℓk : k ^ 2 * ((freeStartHarperD 0 : ℝ) + 1) / (k ^ 2 - 1) ≤ ℓ₀)
    (hℓL : L₀ + 1 ≤ Real.exp ℓ₀) (hℓ₀ : 1000000 ≤ Real.exp ℓ₀) (hΛ36 : 36 ≤ Λ)
    (hΛℓ : ℓ₀ + 1 + 2 * Real.log Λ ≤ Λ)
    (hΛk : k ^ 2 * (2 * Real.log Λ + 1) ≤ (k ^ 2 - 1) * Λ)
    (hΛC : 3 * (|Real.log reductionUpperConst| + reductionUpperExponent) / reductionUpperDecay
      ≤ Λ)
    (hΛη : 6 * (1 + |Real.log η|) / reductionUpperDecay ≤ Λ) :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ x q : ℝ, Real.exp (Real.exp Λ) ≤ x → 0 ≤ q → q ≤ 1 →
        ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
          ≤ upperSwitchConst (chaosAveragedConst A lam T κ β δ k L₀) k η p q
            * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) :=
  harper_upper_full_of_chaos_sieve_switch hk hη hp23 hp1 hℓ₀ hΛ36 hΛℓ hΛk hΛC hΛη
    fun f μ hf y q hy hq23 hq1 =>
      integral_chaosUnit_rpow_le_averaged hδ0 hδ hk hL₀ hA hlam hT hκ hβ hN hmono hℓN hℓk hℓL f μ
        hf y q hy (by linarith) hq1

/-- **The descent's constant on `[q₁, q₂]` from its endpoints**: for `0 ≤ q₁ ≤ q ≤ q₂ ≤ p < 1`,
`0 ≤ C ≤ c` with `c ≥ 1`, `q₂/p ≤ r` and `(1-q₁)/(1-p) ≤ s`,
`C^{q/p}((1-q)/(1-p))^q ≤ e^{r log c + q₂ log s}`: the base `(1-q)/(1-p) ≥ 1` decreases in `q`, and
both exponents increase. -/
lemma switchDescent_le_of_end {C c p q q₁ q₂ r s : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq₁ : 0 ≤ q₁)
    (h1q : q₁ ≤ q) (hq2 : q ≤ q₂) (hq₂p : q₂ ≤ p) (hC0 : 0 ≤ C) (hCc : C ≤ c) (hc : 1 ≤ c)
    (hr : q₂ / p ≤ r) (hs : (1 - q₁) / (1 - p) ≤ s) :
    C ^ (q / p) * ((1 - q) / (1 - p)) ^ q ≤ Real.exp (r * Real.log c + q₂ * Real.log s) := by
  refine le_trans ?_ (Real.exp_le_exp.2 (add_le_add
    (mul_le_mul_of_nonneg_right hr (Real.log_nonneg hc))
    (mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos (by linarith) (by linarith)) hs)
      (le_trans hq₁ (le_trans h1q hq2)))))
  have hq0 : 0 ≤ q := le_trans hq₁ h1q
  have h1p : 0 < 1 - p := by linarith
  have hr1 : 1 ≤ (1 - q) / (1 - p) := by
    rw [le_div_iff₀ h1p]
    linarith
  have hr0 : 0 < (1 - q) / (1 - p) := by linarith
  have hr₁ : (1 - q) / (1 - p) ≤ (1 - q₁) / (1 - p) :=
    div_le_div_of_nonneg_right (by linarith) h1p.le
  have t1 : C ^ (q / p) ≤ Real.exp (q₂ / p * Real.log c) := by
    calc C ^ (q / p) ≤ c ^ (q / p) := Real.rpow_le_rpow hC0 hCc (div_nonneg hq0 hp.le)
      _ ≤ c ^ (q₂ / p) :=
          Real.rpow_le_rpow_of_exponent_le hc (div_le_div_of_nonneg_right hq2 hp.le)
      _ = Real.exp (q₂ / p * Real.log c) := by
          rw [Real.rpow_def_of_pos (by linarith), mul_comm]
  have t2 : ((1 - q) / (1 - p)) ^ q ≤ Real.exp (q₂ * Real.log ((1 - q₁) / (1 - p))) := by
    calc ((1 - q) / (1 - p)) ^ q ≤ ((1 - q₁) / (1 - p)) ^ q := Real.rpow_le_rpow hr0.le hr₁ hq0
      _ ≤ ((1 - q₁) / (1 - p)) ^ q₂ := Real.rpow_le_rpow_of_exponent_le (le_trans hr1 hr₁) hq2
      _ = Real.exp (q₂ * Real.log ((1 - q₁) / (1 - p))) := by
          rw [Real.rpow_def_of_pos (by linarith), mul_comm]
  rw [Real.exp_add]
  exact mul_le_mul t1 t2 (Real.rpow_nonneg hr0.le _) (Real.exp_pos _).le

end RMF
