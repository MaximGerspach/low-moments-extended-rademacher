/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.ThetaClassical
import RMF.UniformLower.DiscrepancyExplicit

/-!
# The window lemma and the floor's primes from `log log x ≈ 47`

The lower reduction's two prime number theorem inputs from `RMF.abs_theta_sub_le_classical`
(`|θ t - t| ≤ t/log²t` for `t ≥ exp(10²⁰)`), in place of `RMF.abs_theta_sub_le_pntAll` at
`RMF.windowThreshold`.

* **The window covering.**  `RMF.window_weight_ge_of_pnt_from` is `RMF.window_weight_ge_of_pnt`
  with the prime number theorem assumed only from `u₀` on: the window weight at `t ∈ [√x, x]`
  uses `θ` at `t` and at `t/(1 + 1/log x)`, both at least `√x/(1 + 1/log x)`.
  `RMF.isWindowCovering_of_pnt_from` is `RMF.half_setIntegral_le_window_sumOf_explicit` through
  it, and `RMF.isWindowCovering_of_classical` its instance at `C = 1`, `u₀ = exp(10²⁰)`:
  `RMF.IsWindowCovering x` for every `x ≥ exp(2·10²⁰ + 2)`, that is from `log log x ≈ 46.7`.
* **The floor's primes.**  `RMF.theta_sub_theta_half_ge_classical`: `θ(x) - θ(x/2) ≥ 0.49x` for
  every `x ≥ exp(10²⁰)`, and `RMF.le_sum_inv_largePrimeSet_half_classical`:
  `∑_{x/2<p≤x} 1/p ≥ 0.49/log x` there, `RMF.le_sum_inv_largePrimeSet_half` without its
  `RMF.windowThreshold`.
-/

open MeasureTheory

namespace RMF

/-! ### The window covering -/

open Finset in
/-- **`RMF.window_weight_ge_of_pnt` with the prime number theorem only from `u₀`**: if
`|θ(u) - u| ≤ Cu/log²u` for every `u ≥ u₀`, then for `x ≥ e^{200 + 80C}` with
`u₀ ≤ √x/(1 + 1/log x)` the window weight at every `t ∈ [√x, x]` is at least `1/2`.  The proof is
that of `RMF.window_weight_ge_of_pnt`, whose prime number theorem is used only at `t` and at
`t/(1 + 1/log x) ≥ √x/(1 + 1/log x)`. -/
theorem window_weight_ge_of_pnt_from {C u₀ : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, u₀ ≤ u → |Chebyshev.theta u - u| ≤ C * u / Real.log u ^ 2) :
    ∀ x t : ℝ, Real.exp (200 + 80 * C) ≤ x → u₀ ≤ Real.sqrt x / (1 + 1 / Real.log x) →
      Real.sqrt x ≤ t → t ≤ x →
      ∀ T : Finset ℕ,
        (∀ p : ℕ, p.Prime → (p : ℝ) < t → t ≤ p * (1 + 1 / Real.log x) → p ∈ T) →
        (1 : ℝ) / 2 ≤ Real.log x * ∑ p ∈ T, Real.log p / p := by
  intro x t hx hu₀ hsx htx T hT
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hX : 200 + 80 * C ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hX0 : (0 : ℝ) < Real.log x := by linarith
  have hsqrt : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by rw [hsqrt]; exact Real.exp_pos _) hsx
  have hLlb : Real.log x / 2 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le ht0, ← hsqrt]
    exact hsx
  have hLub : Real.log t ≤ Real.log x := Real.log_le_log ht0 htx
  have hXt : Real.log x ^ 4 / 1024 ≤ t := by
    refine le_trans (pow_four_le_exp_half hX0.le) ?_
    rw [← hsqrt]
    exact hsx
  have hlogt : (100 : ℝ) ≤ Real.log t := by linarith
  have hlogt0 : (0 : ℝ) < Real.log t := by linarith
  have ht101 : (101 : ℝ) ≤ t := by
    have hexp : Real.log x / 2 + 1 ≤ Real.exp (Real.log x / 2) := Real.add_one_le_exp _
    rw [hsqrt] at hsx
    linarith
  -- the lower endpoint of the window
  set r : ℝ := 1 + 1 / Real.log x with hrdef
  have hr0 : (0 : ℝ) < r := by
    have : (0 : ℝ) < 1 / Real.log x := by positivity
    linarith
  have hr1 : (1 : ℝ) < r := by
    have : (0 : ℝ) < 1 / Real.log x := by positivity
    linarith
  have hr2 : r ≤ 2 := by
    have h : 1 / Real.log x ≤ 1 := by
      rw [div_le_one hX0]
      linarith
    linarith
  set s : ℝ := t / r with hsdef
  have hsr : s * r = t := by
    rw [hsdef]
    field_simp
  have hst : s ≤ t := by nlinarith
  have hs2 : t / 2 ≤ s := by nlinarith
  -- the prime number theorem is used at `s` and `t`, both at least `√x/(1 + 1/log x) ≥ u₀`
  have hsu₀ : u₀ ≤ s := le_trans hu₀ (div_le_div_of_nonneg_right hsx hr0.le)
  have htu₀ : u₀ ≤ t := le_trans hsu₀ hst
  have hs4 : (4 : ℝ) ≤ t := by linarith
  -- `log s ≥ (log t)/2`, because `s ≥ t/2 ≥ √t`
  have hlogs : Real.log t / 2 ≤ Real.log s := by
    have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (by linarith)
    have h2 : (2 : ℝ) ≤ Real.sqrt t := by
      have h4 : Real.sqrt 4 ≤ Real.sqrt t := Real.sqrt_le_sqrt (by linarith)
      rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h4
    have h3 : Real.sqrt t ≤ s := by nlinarith [Real.sqrt_nonneg t]
    have h5 := Real.log_le_log (Real.sqrt_pos.2 (by linarith)) h3
    rwa [Real.log_sqrt (by linarith)] at h5
  have hlogs0 : (0 : ℝ) < Real.log s := by linarith
  -- the window's primes lie in `T`
  have hsub : windowPrimes s t ⊆ T := by
    intro p hp
    obtain ⟨hprime, hps, hpt⟩ := windowPrimes_spec hp
    exact hT p hprime hpt (by nlinarith)
  have hmono : ∑ p ∈ windowPrimes s t, Real.log p / p ≤ ∑ p ∈ T, Real.log p / p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => log_div_natCast_nonneg p
  -- on the window `p ≤ t`, so `log p / p ≥ log p / t`
  have hdiv : (∑ p ∈ windowPrimes s t, Real.log p) / t
      ≤ ∑ p ∈ windowPrimes s t, Real.log p / p := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hprime, hps, hpt⟩ := windowPrimes_spec hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hp0 hpt.le) (Real.log_natCast_nonneg p)
  -- the prime number theorem
  have hfl : ⌊s⌋₊ ≤ ⌊t⌋₊ := Nat.floor_mono hst
  have hstep4 := sum_log_windowPrimes_ge hfl (by linarith)
  have hstep5 : t - s - (C * t / Real.log t ^ 2 + C * s / Real.log s ^ 2)
      ≤ Chebyshev.theta t - Chebyshev.theta s := by
    have h1 := abs_le.1 (hC t htu₀)
    have h2 := abs_le.1 (hC s hsu₀)
    linarith [h1.1, h2.2]
  have htsub : t - s = t / (Real.log x + 1) := by
    rw [hsdef, hrdef]
    field_simp
    ring
  have hkey2 : C * s / Real.log s ^ 2 ≤ 4 * (C * t / Real.log t ^ 2) := by
    have hden : (Real.log t / 2) ^ 2 ≤ Real.log s ^ 2 := by nlinarith
    have hd0 : (0 : ℝ) < (Real.log t / 2) ^ 2 := by positivity
    have hnum : C * s ≤ C * t := mul_le_mul_of_nonneg_left hst hC0
    have h1 : C * s / Real.log s ^ 2 ≤ C * t / (Real.log t / 2) ^ 2 := by
      calc C * s / Real.log s ^ 2 ≤ C * t / Real.log s ^ 2 := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right hnum (by positivity)
        _ ≤ C * t / (Real.log t / 2) ^ 2 := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left (inv_anti₀ hd0 hden)
              (mul_nonneg hC0 ht0.le)
    have h2 : C * t / (Real.log t / 2) ^ 2 = 4 * (C * t / Real.log t ^ 2) := by
      field_simp
      ring
    linarith
  -- assemble
  have h1 : t / (Real.log x + 1) - 5 * (C * t / Real.log t ^ 2) - Real.log t
      ≤ ∑ p ∈ windowPrimes s t, Real.log p := by linarith
  have h2 : (t / (Real.log x + 1) - 5 * (C * t / Real.log t ^ 2) - Real.log t) / t
      ≤ (∑ p ∈ windowPrimes s t, Real.log p) / t := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have h5 := mul_le_mul_of_nonneg_left (le_trans (le_trans h2 hdiv) hmono) hX0.le
  have hexpand : Real.log x
      * ((t / (Real.log x + 1) - 5 * (C * t / Real.log t ^ 2) - Real.log t) / t)
      = Real.log x / (Real.log x + 1) - 5 * C * Real.log x / Real.log t ^ 2
        - Real.log x * Real.log t / t := by
    have h1' : t ≠ 0 := ne_of_gt ht0
    have h2' : Real.log x + 1 ≠ 0 := by positivity
    have h3' : Real.log t ≠ 0 := ne_of_gt hlogt0
    field_simp
  rw [hexpand] at h5
  exact le_trans (window_weight_numeric hC0 hX hLlb hLub hXt) h5

/-- **The window covering from a prime number theorem from `u₀`**: `RMF.IsWindowCovering x` for
`x ≥ e^{200 + 80C}` with `u₀ ≤ √x/(1 + 1/log x)`, if `|θ(u) - u| ≤ Cu/log²u` for every `u ≥ u₀`.
The proof of `RMF.half_setIntegral_le_window_sumOf_explicit`, with the window weight from
`RMF.window_weight_ge_of_pnt_from`. -/
theorem isWindowCovering_of_pnt_from {C u₀ : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, u₀ ≤ u → |Chebyshev.theta u - u| ≤ C * u / Real.log u ^ 2) {x : ℝ}
    (hx : Real.exp (200 + 80 * C) ≤ x) (hu₀ : u₀ ≤ Real.sqrt x / (1 + 1 / Real.log x)) :
    IsWindowCovering x := by
  have hw := window_weight_ge_of_pnt_from hC0 hC
  unfold IsWindowCovering
  intro G hG0 hGi S hSp hS
  have hx4 : (4 : ℝ) ≤ x := by
    have h := Real.add_one_le_exp (200 + 80 * C)
    linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hXpos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  set r : ℝ := 1 + 1 / Real.log x with hrdef
  have hr0 : (0 : ℝ) < r := by
    have : (0 : ℝ) < 1 / Real.log x := by positivity
    linarith
  have hr1 : (1 : ℝ) < r := by
    have : (0 : ℝ) < 1 / Real.log x := by positivity
    linarith
  have hsq1 : (1 : ℝ) ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq0 : (0 : ℝ) < Real.sqrt x := by linarith
  set a : ℝ := Real.sqrt x * r with hadef
  have hsqa : Real.sqrt x < a := by nlinarith
  have ha1 : (1 : ℝ) ≤ a := by linarith
  set c : ℕ → ℝ := fun p => Real.log p * (Real.log x / p) with hcdef
  have hc0 : ∀ p : ℕ, 0 ≤ c p := by
    intro p
    rw [hcdef]
    exact mul_nonneg (Real.log_natCast_nonneg p) (by positivity)
  -- integrability, on the range and on each window
  have hIG : IntegrableOn G (Set.Ioc a x) := hGi a x ha1
  have hIind : ∀ p : ℕ, IntegrableOn (Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G)
      (Set.Ioc a x) := fun p => hIG.indicator measurableSet_Ioc
  -- (1) each window integral dominates its part inside the range
  have hstep1 : ∀ p ∈ S, (∫ t in Set.Ioc a x,
      Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t)
      ≤ ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * r), G t := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hSp p hp).two_le
    rw [setIntegral_indicator measurableSet_Ioc]
    refine setIntegral_mono_set (hGi p (p * r) (by linarith))
      (Filter.Eventually.of_forall hG0) ?_
    exact LE.le.eventuallyLE Set.inter_subset_right
  -- (2) the finite sum comes out of the integral
  have hstep2 : (∫ t in Set.Ioc a x, ∑ p ∈ S, c p *
      Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t)
      = ∑ p ∈ S, c p * ∫ t in Set.Ioc a x,
          Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t := by
    rw [integral_finsetSum _ fun p _ => (hIind p).const_mul (c p)]
    exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _
  -- (3) the weight is at least `1/2` on the range
  have hstep3 : ∀ t ∈ Set.Ioc a x, 1 / 2 * G t ≤ ∑ p ∈ S, c p *
      Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t := by
    intro t ht
    have hat : a < t := ht.1
    have htx : t ≤ x := ht.2
    have hsqt : Real.sqrt x ≤ t := le_of_lt (lt_trans hsqa hat)
    -- the primes of the window at `t`
    set W : Finset ℕ := S.filter (fun q : ℕ => (q : ℝ) < t ∧ t ≤ (q : ℝ) * r) with hWdef
    have hmem : ∀ p : ℕ, p.Prime → (p : ℝ) < t → t ≤ (p : ℝ) * r → p ∈ W := by
      intro p hprime hpt htp
      rw [hWdef]
      refine Finset.mem_filter.2 ⟨hS p hprime ?_ (le_of_lt (lt_of_lt_of_le hpt htx)), hpt, htp⟩
      nlinarith
    have hweight := hw x t hx hu₀ hsqt htx W hmem
    -- the indicator sum collapses onto that set
    have hcollapse : (∑ p ∈ S, c p *
        Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t) = (∑ p ∈ W, c p) * G t := by
      rw [Finset.sum_mul, hWdef, Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : (p : ℝ) < t ∧ t ≤ (p : ℝ) * r
      · rw [if_pos hp, Set.indicator_of_mem (Set.mem_Ioc.2 ⟨hp.1, hp.2⟩)]
      · rw [if_neg hp, Set.indicator_of_notMem (fun hm => hp (Set.mem_Ioc.1 hm)), mul_zero]
    rw [hcollapse]
    have hcsum : (1 : ℝ) / 2 ≤ ∑ p ∈ W, c p := by
      refine le_trans hweight (le_of_eq ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by rw [hcdef]; ring
    nlinarith [hG0 t]
  -- (4) assemble
  have hI2 : IntegrableOn (fun t => ∑ p ∈ S, c p *
      Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t) (Set.Ioc a x) :=
    integrable_finsetSum _ fun p _ => (hIind p).const_mul (c p)
  calc 1 / 2 * (∫ t in Set.Ioc a x, G t)
      = ∫ t in Set.Ioc a x, 1 / 2 * G t := (integral_const_mul _ _).symm
    _ ≤ ∫ t in Set.Ioc a x, ∑ p ∈ S, c p *
          Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t :=
        setIntegral_mono_on (hIG.const_mul _) hI2 measurableSet_Ioc hstep3
    _ = ∑ p ∈ S, c p * ∫ t in Set.Ioc a x,
          Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t := hstep2
    _ ≤ ∑ p ∈ S, c p * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * r), G t :=
        Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hstep1 p hp) (hc0 p)
    _ = ∑ p ∈ S, Real.log p * (Real.log x / p
          * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * r), G t) :=
        Finset.sum_congr rfl fun p _ => by rw [hcdef]; ring

/-- **The window covering from `log log x ≈ 46.7`**: `RMF.IsWindowCovering x` for every
`x ≥ exp(2·10²⁰ + 2)`.  `RMF.isWindowCovering_of_pnt_from` with `C = 1` and `u₀ = exp(10²⁰)`
(`RMF.abs_theta_sub_le_classical`): `√x ≥ e^{10²⁰ + 1} ≥ 2e^{10²⁰}` and `1 + 1/log x ≤ 2`. -/
theorem isWindowCovering_of_classical :
    ∀ x : ℝ, Real.exp (2 * 10 ^ 20 + 2) ≤ x → IsWindowCovering x := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 2 * 10 ^ 20 + 2 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hL1 : 1 ≤ Real.log x := le_trans (by norm_num) hL
  refine isWindowCovering_of_pnt_from (C := 1) (u₀ := Real.exp (10 ^ 20)) zero_le_one
    (fun u hu => by rw [one_mul]; exact abs_theta_sub_le_classical u hu)
    (le_trans (Real.exp_le_exp.2 (by norm_num)) hx) ?_
  have hsq : Real.sqrt (Real.exp (2 * 10 ^ 20 + 2)) = Real.exp (10 ^ 20 + 1) := by
    rw [show (2 : ℝ) * 10 ^ 20 + 2 = (10 ^ 20 + 1) + (10 ^ 20 + 1) by ring, Real.exp_add,
      Real.sqrt_mul_self (Real.exp_pos _).le]
  have hsqrt : Real.exp (10 ^ 20 + 1) ≤ Real.sqrt x := by
    rw [← hsq]
    exact Real.sqrt_le_sqrt hx
  have he : 2 * Real.exp (10 ^ 20) ≤ Real.exp (10 ^ 20 + 1) := by
    have h := Real.add_one_le_exp (1 : ℝ)
    calc 2 * Real.exp (10 ^ 20) ≤ Real.exp 1 * Real.exp (10 ^ 20) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = Real.exp (10 ^ 20 + 1) := by rw [Real.exp_add, mul_comm]
  have hr : 1 + 1 / Real.log x ≤ 2 := by
    have h : 1 / Real.log x ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hL1
    linarith
  rw [le_div_iff₀ (by positivity)]
  calc Real.exp (10 ^ 20) * (1 + 1 / Real.log x) ≤ Real.exp (10 ^ 20) * 2 :=
        mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le
    _ ≤ Real.exp (10 ^ 20 + 1) := by linarith
    _ ≤ Real.sqrt x := hsqrt

/-! ### The floor's primes -/

/-- **`θ(x) - θ(x/2) ≥ 0.49x` for every `x ≥ exp(10²⁰)`**: `RMF.theta_half_arith` at `C = 1`,
with `RMF.abs_theta_sub_le_classical_of_exp_half_le` at `x` and at `x/2 ≥ exp(10²⁰/2)`. -/
theorem theta_sub_theta_half_ge_classical {x : ℝ} (hx : Real.exp (10 ^ 20) ≤ x) :
    49 / 100 * x ≤ Chebyshev.theta x - Chebyshev.theta (x / 2) := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 10 ^ 20 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hh : Real.exp (10 ^ 20 / 2) ≤ x / 2 := by
    have h1 : Real.exp (10 ^ 20) = Real.exp (10 ^ 20 / 2) * Real.exp (10 ^ 20 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h2 : 2 ≤ Real.exp (10 ^ 20 / 2) := by
      have h := Real.add_one_le_exp (10 ^ 20 / 2 : ℝ)
      linarith
    have h3 : 2 * Real.exp (10 ^ 20 / 2) ≤ Real.exp (10 ^ 20) := by
      rw [h1]
      exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    have h4 : 2 * Real.exp (10 ^ 20 / 2) ≤ x := le_trans h3 hx
    linarith
  have hθx := abs_le.1 (abs_theta_sub_le_classical_of_exp_half_le x
    (le_trans (Real.exp_le_exp.2 (by norm_num)) hx))
  have hθh := abs_le.1 (abs_theta_sub_le_classical_of_exp_half_le (x / 2) hh)
  have hl₂ : Real.log x / 2 ≤ Real.log (x / 2) := by
    rw [Real.log_div hx0.ne' two_ne_zero]
    have := Real.log_two_lt_d9
    linarith
  refine theta_half_arith (C := 1) zero_le_one (by linarith) hl₂ hx0 ?_
  rw [one_mul, one_mul]
  linarith [hθx.1, hθh.2]

/-- **The primes of `(x/2, x]` from `exp(10²⁰)`**: `∑_{x/2<p≤x} 1/p ≥ 0.49/log x` for every
`x ≥ exp(10²⁰)`.  The proof of `RMF.le_sum_inv_largePrimeSet_half`, with
`RMF.theta_sub_theta_half_ge_classical` in place of its prime number theorem. -/
theorem le_sum_inv_largePrimeSet_half_classical {x : ℝ} (hx : Real.exp (10 ^ 20) ≤ x) :
    49 / (100 * Real.log x) ≤ ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹ := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 10 ^ 20 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL
  have hθ' := theta_sub_theta_half_ge_classical hx
  rw [theta_sub_theta_eq (Nat.floor_mono (by linarith))] at hθ'
  have hterm : ∀ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊,
      Real.log p / (x * Real.log x) ≤ (p : ℝ)⁻¹ := by
    intro p hp
    obtain ⟨⟨-, hpx⟩, hprime⟩ := mem_largePrimeSet.1 hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpxR : (p : ℝ) ≤ x := le_trans (by exact_mod_cast hpx) (Nat.floor_le hx0.le)
    have hlogp : Real.log p ≤ Real.log x := Real.log_le_log hp0 hpxR
    have hlogp0 : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    rw [div_le_iff₀ (mul_pos hx0 hL0)]
    have h1 : (1 : ℝ) ≤ (p : ℝ)⁻¹ * x := by
      rw [inv_mul_eq_div, one_le_div hp0]
      exact hpxR
    nlinarith [mul_le_mul h1 hlogp hlogp0 (zero_le_one.trans h1)]
  calc 49 / (100 * Real.log x) = 49 / 100 * x / (x * Real.log x) := by
        field_simp
    _ ≤ (∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, Real.log p) / (x * Real.log x) :=
        div_le_div_of_nonneg_right hθ' (mul_pos hx0 hL0).le
    _ = ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, Real.log p / (x * Real.log x) := Finset.sum_div _ _ _
    _ ≤ ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹ := Finset.sum_le_sum hterm

end RMF
