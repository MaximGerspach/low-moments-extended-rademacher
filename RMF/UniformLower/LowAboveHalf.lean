/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.PerScale
import RMF.UniformLower.BonamiBecknerExplicit
import RMF.NumberTheory.LogPrimeSum

/-!
# `N_q(k) = E‖F_{[0,c_k)}(σ)‖^{2q}` from below, `½ ≤ q ≤ ½ + 1/20`

The twin above `½` of `RMF.le_integral_rpow_norm_low`, with the exact exponent `β = q(2q-1)`:
`E‖F_{[0,c_k)}(½+σ)‖^{2q} ≥ e^{βk}` for `k ≥ 20` and `σe^k ≤ 1/200`
(`RMF.le_integral_rpow_norm_low_of_half_le`).  A coefficient `β(1-ε)` would lose `e^{-εβk}`,
unbounded in the sliver regime (`RMF.le_integral_rpow_sliverRegime`), so the damping `p^{-2σ}`
goes through Mertens' first theorem, not a pointwise bound.

* Per prime (`RMF.one_add_sq_le_rademacher_local`): `((1+u)^a + (1-u)^a)/2 ≥ 1 + a(a-1)u²/2` for
  `1 ≤ a ≤ 2`; the difference vanishes to first order at `0` and is convex, since
  `(1 ± u)^{a-2} ≥ 1/(1 ± (2-a)u)` (Bernoulli).  With `1 + y ≥ e^{y-y²}`:
  `E|1 + X p^{-1/2-σ}|^{2q} ≥ exp(βp^{-(1+2σ)} - β²/p²)`
  (`RMF.exp_sub_sq_le_rademacher_of_half_le`), and over the primes below the cut
  (`RMF.exp_sum_le_integral_rpow_norm_low_of_half_le`).
* Mertens (`RMF.le_sum_rpow_primesIco_scaleCut`):
  `∑_{p<c_k} p^{-(1+2σ)} ≥ k + 3/20 - 9.0028e^{-k} - 2σ(e^k + log 4 + 4)`; with
  `∑ 1/p² ≤ 3/4` and `β ≤ 0.055` the exponent is at least `βk`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-! ### Per prime -/

/-- **The Rademacher local moment from below, `1 ≤ a ≤ 2`**: for `0 ≤ u ≤ 1`,
`((1+u)^a + (1-u)^a)/2 ≥ 1 + a(a-1)u²/2`. -/
theorem one_add_sq_le_rademacher_local {a u : ℝ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    1 + a * (a - 1) / 2 * u ^ 2 ≤ ((1 + u) ^ a + (1 - u) ^ a) / 2 := by
  set c : ℝ := a * (a - 1) / 2 with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ a - 1 := by linarith
    rw [hc]; positivity
  -- the difference and its first two derivatives on `(-1, 1)`
  have hd1 : ∀ v : ℝ, -1 < v → v < 1 →
      HasDerivAt (fun v => ((1 + v) ^ a + (1 - v) ^ a) / 2 - 1 - c * v ^ 2)
        (a / 2 * ((1 + v) ^ (a - 1) - (1 - v) ^ (a - 1)) - 2 * c * v) v := by
    intro v hv1 hv2
    have hp : (0 : ℝ) < 1 + v := by linarith
    have hm : (0 : ℝ) < 1 - v := by linarith
    have h1 : HasDerivAt (fun v : ℝ => (1 + v) ^ a) (1 * a * (1 + v) ^ (a - 1)) v :=
      ((hasDerivAt_id' v).const_add 1).rpow_const (Or.inl hp.ne')
    have h2 : HasDerivAt (fun v : ℝ => (1 - v) ^ a) (-1 * a * (1 - v) ^ (a - 1)) v :=
      ((hasDerivAt_id' v).const_sub 1).rpow_const (Or.inl hm.ne')
    have h3 : HasDerivAt (fun v : ℝ => v ^ 2) ((2 : ℕ) * v ^ (2 - 1)) v := hasDerivAt_pow 2 v
    have h := (((h1.add h2).div_const 2).sub_const 1).sub (h3.const_mul c)
    refine h.congr_deriv ?_
    norm_num
    ring
  have hd2 : ∀ v : ℝ, -1 < v → v < 1 →
      HasDerivAt (fun v => a / 2 * ((1 + v) ^ (a - 1) - (1 - v) ^ (a - 1)) - 2 * c * v)
        (a / 2 * ((a - 1) * (1 + v) ^ (a - 2) + (a - 1) * (1 - v) ^ (a - 2)) - 2 * c) v := by
    intro v hv1 hv2
    have hp : (0 : ℝ) < 1 + v := by linarith
    have hm : (0 : ℝ) < 1 - v := by linarith
    have h1 : HasDerivAt (fun v : ℝ => (1 + v) ^ (a - 1)) (1 * (a - 1) * (1 + v) ^ (a - 1 - 1)) v :=
      ((hasDerivAt_id' v).const_add 1).rpow_const (Or.inl hp.ne')
    have h2 : HasDerivAt (fun v : ℝ => (1 - v) ^ (a - 1))
        (-1 * (a - 1) * (1 - v) ^ (a - 1 - 1)) v :=
      ((hasDerivAt_id' v).const_sub 1).rpow_const (Or.inl hm.ne')
    have h3 : HasDerivAt (fun v : ℝ => 2 * c * v) (2 * c * 1) v :=
      (hasDerivAt_id' v).const_mul (2 * c)
    have h := ((h1.sub h2).const_mul (a / 2)).sub h3
    refine h.congr_deriv ?_
    rw [show a - 1 - 1 = a - 2 by ring]
    ring
  -- the second derivative is nonnegative on `[0, 1)`: `(1 ± v)^{a-2} ≥ 1/(1 ± (2-a)v)`
  have hd2nn : ∀ v : ℝ, 0 ≤ v → v < 1 →
      0 ≤ a / 2 * ((a - 1) * (1 + v) ^ (a - 2) + (a - 1) * (1 - v) ^ (a - 2)) - 2 * c := by
    intro v hv0 hv1
    have hp : (0 : ℝ) < 1 + v := by linarith
    have hm : (0 : ℝ) < 1 - v := by linarith
    have hb0 : 0 ≤ 2 - a := by linarith
    have hb1 : 2 - a ≤ 1 := by linarith
    have hbp : (1 + v) ^ (2 - a) ≤ 1 + (2 - a) * v :=
      rpow_one_add_le_one_add_mul_self (by linarith) hb0 hb1
    have hbm : (1 - v) ^ (2 - a) ≤ 1 - (2 - a) * v := by
      have h := rpow_one_add_le_one_add_mul_self (s := -v) (by linarith) hb0 hb1
      rw [← sub_eq_add_neg] at h
      linarith
    have ep : (1 + v) ^ (a - 2) = ((1 + v) ^ (2 - a))⁻¹ := by
      rw [show a - 2 = -(2 - a) by ring, Real.rpow_neg hp.le]
    have em : (1 - v) ^ (a - 2) = ((1 - v) ^ (2 - a))⁻¹ := by
      rw [show a - 2 = -(2 - a) by ring, Real.rpow_neg hm.le]
    have hpb : 0 < (1 + v) ^ (2 - a) := Real.rpow_pos_of_pos hp _
    have hmb : 0 < (1 - v) ^ (2 - a) := Real.rpow_pos_of_pos hm _
    have hw0 : 0 ≤ (2 - a) * v := mul_nonneg hb0 hv0
    have hw1 : (2 - a) * v ≤ v := by nlinarith
    have hkey : 2 ≤ (1 + v) ^ (a - 2) + (1 - v) ^ (a - 2) := by
      rw [ep, em]
      have hw2 : 0 < 1 - (2 - a) * v := by linarith
      have hw3 : 0 < 1 + (2 - a) * v := by linarith
      have i1 : (1 + (2 - a) * v)⁻¹ ≤ ((1 + v) ^ (2 - a))⁻¹ := inv_anti₀ hpb hbp
      have i2 : (1 - (2 - a) * v)⁻¹ ≤ ((1 - v) ^ (2 - a))⁻¹ := inv_anti₀ hmb hbm
      have i3 : 2 ≤ (1 + (2 - a) * v)⁻¹ + (1 - (2 - a) * v)⁻¹ := by
        rw [inv_add_inv hw3.ne' hw2.ne', le_div_iff₀ (mul_pos hw3 hw2)]
        nlinarith
      linarith
    have e : a / 2 * ((a - 1) * (1 + v) ^ (a - 2) + (a - 1) * (1 - v) ^ (a - 2)) - 2 * c
        = c * ((1 + v) ^ (a - 2) + (1 - v) ^ (a - 2) - 2) := by
      rw [hc]
      ring
    rw [e]
    exact mul_nonneg hc0 (by linarith)
  -- the first derivative is nonnegative on `[0, 1)`
  have hI : interior (Set.Ico (0 : ℝ) 1) = Set.Ioo 0 1 := interior_Ico
  have hmono1 : MonotoneOn (fun v => a / 2 * ((1 + v) ^ (a - 1) - (1 - v) ^ (a - 1)) - 2 * c * v)
      (Set.Ico 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
      (fun v hv => (hd2 v (by linarith [hv.1]) hv.2).continuousAt.continuousWithinAt)
      (fun v hv => ?_) (fun v hv => ?_)
    · rw [hI] at hv
      exact (hd2 v (by linarith [hv.1]) hv.2).differentiableAt.differentiableWithinAt
    · rw [hI] at hv
      rw [(hd2 v (by linarith [hv.1]) hv.2).deriv]
      exact hd2nn v hv.1.le hv.2
  have hd1nn : ∀ v : ℝ, 0 ≤ v → v < 1 →
      0 ≤ a / 2 * ((1 + v) ^ (a - 1) - (1 - v) ^ (a - 1)) - 2 * c * v := by
    intro v hv0 hv1
    have h := hmono1 ⟨le_rfl, zero_lt_one⟩ ⟨hv0, hv1⟩ hv0
    simpa using h
  -- the difference is nonnegative on `[0, 1]`, continuous up to `1` since `a > 0`
  have hr : Continuous fun y : ℝ => y ^ a := Real.continuous_rpow_const (by linarith)
  have hcont : ContinuousOn (fun v => ((1 + v) ^ a + (1 - v) ^ a) / 2 - 1 - c * v ^ 2)
      (Set.Icc 0 1) :=
    (((((hr.comp (continuous_const.add continuous_id)).add
      (hr.comp (continuous_const.sub continuous_id))).div_const 2).sub continuous_const).sub
      (continuous_const.mul (continuous_pow 2))).continuousOn
  have hIcc : interior (Set.Icc (0 : ℝ) 1) = Set.Ioo 0 1 := interior_Icc
  have hmono : MonotoneOn (fun v => ((1 + v) ^ a + (1 - v) ^ a) / 2 - 1 - c * v ^ 2)
      (Set.Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hcont (fun v hv => ?_) (fun v hv => ?_)
    · rw [hIcc] at hv
      exact (hd1 v (by linarith [hv.1]) hv.2).differentiableAt.differentiableWithinAt
    · rw [hIcc] at hv
      rw [(hd1 v (by linarith [hv.1]) hv.2).deriv]
      exact hd1nn v hv.1.le hv.2
  have h := hmono ⟨le_rfl, zero_le_one⟩ ⟨hu0, hu1⟩ hu0
  simp only [add_zero, sub_zero, Real.one_rpow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero] at h
  linarith

/-- **The local moment at a prime from below, `½ ≤ q ≤ 1`**: with `β = q(2q-1)` and `σ ≥ 0`,
`E|1 + X p^{-1/2-σ}|^{2q} ≥ exp(βp^{-(1+2σ)} - β²/p²)`. -/
theorem exp_sub_sq_le_rademacher_of_half_le {p : ℕ} (hp : p.Prime) {σ q : ℝ} (hσ : 0 ≤ σ)
    (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) :
    Real.exp (q * (2 * q - 1) * (p : ℝ) ^ (-(1 + 2 * σ))
        - (q * (2 * q - 1)) ^ 2 * (1 / (p : ℝ) ^ 2))
      ≤ ∫ z, ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ (2 * q) ∂rademacherLaw := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hu0 : 0 ≤ (p : ℝ) ^ (-(1 / 2 + σ)) := Real.rpow_nonneg hp0.le _
  have hu1 : (p : ℝ) ^ (-(1 / 2 + σ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hu2 : ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 = (p : ℝ) ^ (-(1 + 2 * σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  rw [cpow_neg_shiftLine_zero p σ, integral_norm_one_add_mul_rpow_rademacherLaw_real hu0 hu1]
  have hD := one_add_sq_le_rademacher_local (a := 2 * q) (u := (p : ℝ) ^ (-(1 / 2 + σ)))
    (by linarith) (by linarith) hu0 hu1
  have hβ0 : 0 ≤ q * (2 * q - 1) := mul_nonneg (by linarith) (by linarith)
  rw [hu2, show 2 * q * (2 * q - 1) / 2 = q * (2 * q - 1) by ring] at hD
  have hr0 : 0 ≤ (p : ℝ) ^ (-(1 + 2 * σ)) := Real.rpow_nonneg hp0.le _
  have hpow : (p : ℝ) ^ (-(1 + 2 * σ)) ≤ 1 / (p : ℝ) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hy0 : 0 ≤ q * (2 * q - 1) * (p : ℝ) ^ (-(1 + 2 * σ)) := mul_nonneg hβ0 hr0
  have hy2 : (q * (2 * q - 1) * (p : ℝ) ^ (-(1 + 2 * σ))) ^ 2
      ≤ (q * (2 * q - 1)) ^ 2 * (1 / (p : ℝ) ^ 2) := by
    rw [mul_pow, ← one_div_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hpow 2) (sq_nonneg _)
  calc Real.exp (q * (2 * q - 1) * (p : ℝ) ^ (-(1 + 2 * σ))
        - (q * (2 * q - 1)) ^ 2 * (1 / (p : ℝ) ^ 2))
      ≤ Real.exp (q * (2 * q - 1) * (p : ℝ) ^ (-(1 + 2 * σ))
        - (q * (2 * q - 1) * (p : ℝ) ^ (-(1 + 2 * σ))) ^ 2) := Real.exp_le_exp.2 (by linarith)
    _ ≤ 1 + q * (2 * q - 1) * (p : ℝ) ^ (-(1 + 2 * σ)) := exp_sub_sq_le_one_add hy0
    _ ≤ _ := hD

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **Over the primes below a cut**: for `σ ≥ 0` and `½ ≤ q ≤ 1`, with `β = q(2q-1)`,
`E‖F_{[0,c)}(σ)‖^{2q} ≥ exp(β∑_{p<c} p^{-(1+2σ)} - β²∑_{p<c} 1/p²)`. -/
theorem exp_sum_le_integral_rpow_norm_low_of_half_le (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (c : ℕ) :
    Real.exp (q * (2 * q - 1) * ∑ p ∈ primesIco 0 c, (p : ℝ) ^ (-(1 + 2 * σ))
        - (q * (2 * q - 1)) ^ 2 * ∑ p ∈ primesIco 0 c, 1 / (p : ℝ) ^ 2)
      ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 c
          (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ := by
  have hSp : ∀ p ∈ primesIco 0 c, p.Prime := fun p hp => prime_of_mem_primesIco hp
  have hbase : ∀ c : ℂ, Measurable fun z : ℂ => ‖1 + z * c‖ :=
    fun c => (measurable_const.add (measurable_id.mul measurable_const)).norm
  rw [integral_congr_ae (Filter.Eventually.of_forall
      (rpow_norm_randomEulerProductIco_eq_prod (X := X) 0 c (shiftLine σ 0) (2 * q))),
    hX.integral_prod hSp (fun p z => ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ (2 * q))
      fun p _ => ((hbase _).pow_const _).aestronglyMeasurable,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Real.exp_sum]
  exact Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le)
    fun p hp => exp_sub_sq_le_rademacher_of_half_le (hSp p hp) hσ hq0 hq1

/-! ### Mertens below the cut -/

/-- **Mertens below the cut, damped**: for `σ ≥ 0`,
`∑_{p<c_k} p^{-(1+2σ)} ≥ k + 3/20 - 9.0028e^{-k} - 2σ(e^k + log 4 + 4)`: `p^{-2σ} ≥ 1 - 2σ log p`,
Mertens' second theorem at `x = exp(e^k)` with `M ≥ 3/20` (`RMF.mertens_const_ge`) and his first,
`∑_{p ≤ x} log p/p ≤ log x + log 4 + 4` (`RMF.sum_log_div_prime_le`). -/
theorem le_sum_rpow_primesIco_scaleCut (k : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    (k : ℝ) + 3 / 20 - 9.0028 / Real.exp (k : ℝ) - 2 * σ * (Real.exp (k : ℝ) + Real.log 4 + 4)
      ≤ ∑ p ∈ primesIco 0 (scaleCut (k : ℝ)), (p : ℝ) ^ (-(1 + 2 * σ)) := by
  set x : ℝ := blockScale (k : ℝ) 0 with hx
  have hlogx : Real.log x = Real.exp (k : ℝ) := by
    rw [hx, log_blockScale]
    simp
  have hx2 : (2 : ℝ) ≤ x := by
    have h1 : (1 : ℝ) ≤ Real.exp (k : ℝ) := Real.one_le_exp (Nat.cast_nonneg k)
    have h2 : Real.exp 1 ≤ x := by
      rw [hx, blockScale]
      exact Real.exp_le_exp.2 (by rw [Nat.cast_zero, zero_add]; exact h1)
    linarith [Real.exp_one_gt_d9]
  have hS : primesIco 0 (scaleCut (k : ℝ)) = {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime} := by
    rw [primesIco_zero, scaleCut, primesBelow_succ_eq_filter_Ioc]
  have hterm : ∀ p ∈ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime},
      (1 : ℝ) / p - 2 * σ * (Real.log p / p) ≤ (p : ℝ) ^ (-(1 + 2 * σ)) := by
    intro p hp
    have hprime : p.Prime := (Finset.mem_filter.1 hp).2
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hfac : (p : ℝ) ^ (-(1 + 2 * σ)) = (1 / (p : ℝ)) * Real.exp (-(2 * σ * Real.log p)) := by
      rw [Real.rpow_def_of_pos hp0, one_div, ← Real.exp_log (inv_pos.2 hp0), ← Real.exp_add,
        Real.log_inv]
      congr 1
      ring
    have hexp : 1 - 2 * σ * Real.log p ≤ Real.exp (-(2 * σ * Real.log p)) := by
      linarith [Real.add_one_le_exp (-(2 * σ * Real.log p))]
    have hmul := mul_le_mul_of_nonneg_left hexp (one_div_nonneg.2 hp0.le)
    rw [← hfac] at hmul
    refine le_trans (le_of_eq ?_) hmul
    field_simp
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hmer := Mertens.sum_prime_div_eq x
  have habs := Mertens.E₂p.abs_le hx2
  have hconst := mertens_error_const_le
  have hM := mertens_const_ge
  have hlog0 : 0 < Real.log x := by rw [hlogx]; exact Real.exp_pos _
  have hE : -(9.0028 / Real.log x) ≤ Mertens.E₂p x := by
    have h1 := (abs_le.1 habs).1
    have h2 : (Real.log 4 + 6 + Mertens.E₁) / Real.log x ≤ 9.0028 / Real.log x :=
      div_le_div_of_nonneg_right hconst hlog0.le
    linarith
  have hfirst := sum_log_div_prime_le (x := x) (by linarith)
  have hshift : 2 * σ * ∑ p ∈ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime}, Real.log p / p
      ≤ 2 * σ * (Real.log x + Real.log 4 + 4) := mul_le_mul_of_nonneg_left hfirst (by linarith)
  rw [hS]
  rw [hmer, hlogx, Real.log_exp] at hsum
  rw [hlogx] at hE hshift
  linarith

/-! ### `N_q(k)` from below -/

/-- **`N_q(k)` from below, `½ ≤ q ≤ ½ + 1/20`**: for `σ ≥ 0`, `k ≥ 20` and `σe^k ≤ 1/200`,
`E‖F_{[0,c_k)}(σ)‖^{2q} ≥ e^{q(2q-1)k}`, the exponent exact
(`RMF.exp_sum_le_integral_rpow_norm_low_of_half_le`, `RMF.le_sum_rpow_primesIco_scaleCut`,
`∑ 1/p² ≤ 3/4`). -/
theorem le_integral_rpow_norm_low_of_half_le (hX : IsRademacherPrimeValues X μ) {σ q : ℝ}
    (hσ : 0 ≤ σ) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1 / 2 + 1 / 20) {k : ℕ} (hk : 20 ≤ k)
    (hσk : σ * Real.exp (k : ℝ) ≤ 1 / 200) :
    Real.exp (q * (2 * q - 1) * k)
      ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
          (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ := by
  refine le_trans (Real.exp_le_exp.2 ?_)
    (exp_sum_le_integral_rpow_norm_low_of_half_le hX hσ hq0 (by linarith) _)
  have h1 := le_sum_rpow_primesIco_scaleCut k hσ
  have h2 : ∑ p ∈ primesIco 0 (scaleCut (k : ℝ)), 1 / (p : ℝ) ^ 2 ≤ 3 / 4 := by
    rw [primesIco_zero, scaleCut]
    exact sum_primesBelow_inv_sq_le_three_quarters _
  set S₁ := ∑ p ∈ primesIco 0 (scaleCut (k : ℝ)), (p : ℝ) ^ (-(1 + 2 * σ))
  set S₂ := ∑ p ∈ primesIco 0 (scaleCut (k : ℝ)), 1 / (p : ℝ) ^ 2
  set β : ℝ := q * (2 * q - 1) with hβ
  have hβ0 : 0 ≤ β := mul_nonneg (by linarith) (by linarith)
  have hβ1 : β ≤ 11 / 200 := by
    have h := mul_le_mul (by linarith : q ≤ 11 / 20) (by linarith : 2 * q - 1 ≤ 1 / 10)
      (by linarith) (by norm_num)
    rw [hβ]
    linarith
  -- the small terms
  have hek : Real.exp 20 ≤ Real.exp (k : ℝ) :=
    Real.exp_le_exp.2 (by exact_mod_cast hk)
  have he20 : (9002.8 : ℝ) ≤ Real.exp 20 := by interval_decide (trust := kernel)
  have hek0 : 0 < Real.exp (k : ℝ) := Real.exp_pos _
  have hsmall : 9.0028 / Real.exp (k : ℝ) ≤ 1 / 1000 := by
    rw [div_le_iff₀ hek0]
    linarith
  have hek1 : 1 ≤ Real.exp (k : ℝ) := Real.one_le_exp (Nat.cast_nonneg k)
  have hσ1 : σ ≤ 1 / 200 := le_trans (le_mul_of_one_le_right hσ hek1) hσk
  have hl4 : Real.log 4 ≤ 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have hσl : σ * Real.log 4 ≤ 1 / 200 * 1.3863 :=
    mul_le_mul hσ1 hl4 (Real.log_nonneg (by norm_num)) (by norm_num)
  have hA : 0 ≤ 3 / 20 - 9.0028 / Real.exp (k : ℝ)
      - 2 * σ * (Real.exp (k : ℝ) + Real.log 4 + 4) - 3 / 4 * β := by
    linarith
  have i1 := mul_le_mul_of_nonneg_left h1 hβ0
  have i2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg β)
  have i3 := mul_nonneg hβ0 hA
  linarith

end RMF
