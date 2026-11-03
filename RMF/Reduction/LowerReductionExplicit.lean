/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.HarperMoment
import RMF.Probability.GaussianNumerals
import RMF.Probability.RestrictedSecondMoment
import RMF.Probability.RestrictedSecondMoment.RangeNumerals
import RMF.NumberTheory.MertensProductExplicit
import RMF.NumberTheory.CosinePrimeSum
import RMF.Probability.RestrictedSecondMoment.Assembly
import RMF.Probability.RestrictedSecondMoment.Drift
import RMF.NumberTheory.StrongPNT
import RMF.PNTPlus.MediumPNTExplicit
import RMF.NumberTheory.ThetaClassicalBound
import RMF.Harper
import RMF.NumberTheory.ThetaMedium
import RMF.NumberTheory.ThetaFar
import RMF.Probability.BlockComparisonExplicit
import RMF.Probability.ChaosMoment
import RMF.Probability.ChaosFirstMomentExplicit
import RMF.Probability.MaximalBarrierExplicit
import RMF.Probability.MaximalBarrierSharp
import RMF.Probability.SharpNumerals
import RMF.Probability.HarperScalesExplicit
import RMF.NumberTheory.PNTThresholdExplicit

/-!
# The lower reduction's mean-square threshold, named

The window weight's threshold is `e^{200 + 80C}`, with `C` the constant of
`|θ(t) - t| ≤ Ct/\log²t` for `t ≥ 2`.  `RMF.window_weight_ge` takes that `C` from `RS_prime.pnt`,
which is not effective; `RMF.window_weight_ge_of_pnt` takes it as a hypothesis, and
`RMF.abs_theta_sub_le_pntAll` supplies it at
`RMF.pntAllConst = max thetaMediumConst (\log 4 · \log² thetaExpThreshold)`: the effective prime
number theorem past its threshold, and Chebyshev's `θ(t) ≤ t\log 4` below it.
`RMF.half_setIntegral_le_window_sumOf_explicit` is `RMF.half_setIntegral_le_window_sumOf` at the
resulting threshold, pushed past `4`: `RMF.windowThreshold`.
-/

open MeasureTheory

namespace RMF

/-! ### The prime number theorem for every `t ≥ 2`, effective -/

/-- **The constant of the prime number theorem from `2`**: `RMF.thetaMediumConst` past
`RMF.thetaExpThreshold`, and Chebyshev's bound, at a cost of `\log 4 · \log² thetaExpThreshold`,
below it. -/
noncomputable def pntAllConst : ℝ :=
  max thetaMediumConst (Real.log 4 * Real.log thetaExpThreshold ^ 2)

lemma pntAllConst_nonneg : 0 ≤ pntAllConst :=
  le_trans thetaMediumConst_pos.le (le_max_left _ _)

/-- **`|θ t - t| ≤ RMF.pntAllConst · t/\log² t` for every `t ≥ 2`**: `RS_prime.pnt`'s shape, with
an effective constant. -/
theorem abs_theta_sub_le_pntAll :
    ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ pntAllConst * t / Real.log t ^ 2 :=
  abs_theta_sub_le_of_threshold' abs_theta_sub_le_medium_explicit.2

/-- **The mean-square leg's threshold**: the window weight's `e^{200 + 80 RMF.pntAllConst}`,
pushed past `4`. -/
noncomputable def windowThreshold : ℝ := max (Real.exp (200 + 80 * pntAllConst)) 4

lemma four_le_windowThreshold : (4 : ℝ) ≤ windowThreshold := le_max_right _ _

open Finset in
/-- **`RMF.window_weight_ge` for any prime number theorem `|θ(u) - u| ≤ Cu/\log²u` from `u = 2`**,
at the threshold `e^{200 + 80C}`. -/
theorem window_weight_ge_of_pnt {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, 2 ≤ u → |Chebyshev.theta u - u| ≤ C * u / Real.log u ^ 2) :
    ∀ x t : ℝ, Real.exp (200 + 80 * C) ≤ x → Real.sqrt x ≤ t → t ≤ x →
      ∀ T : Finset ℕ,
        (∀ p : ℕ, p.Prime → (p : ℝ) < t → t ≤ p * (1 + 1 / Real.log x) → p ∈ T) →
        (1 : ℝ) / 2 ≤ Real.log x * ∑ p ∈ T, Real.log p / p := by
  intro x t hx hsx htx T hT
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
  have hs0 : (2 : ℝ) ≤ s := by linarith
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
  have hstep5 := theta_sub_theta_ge hC hs0 hst
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

/-- **`RMF.half_setIntegral_le_window_sumOf` at its threshold** `RMF.windowThreshold`. -/
theorem half_setIntegral_le_window_sumOf_explicit :
    ∀ x : ℝ, windowThreshold ≤ x → ∀ G : ℝ → ℝ, (∀ t, 0 ≤ G t) →
      (∀ c d : ℝ, 1 ≤ c → IntegrableOn G (Set.Ioc c d)) →
      ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) →
        (∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) →
        1 / 2 * (∫ t in Set.Ioc (Real.sqrt x * (1 + 1 / Real.log x)) x, G t)
          ≤ ∑ p ∈ S, Real.log p * (Real.log x / p
              * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), G t) := by
  unfold windowThreshold
  have hw := window_weight_ge_of_pnt pntAllConst_nonneg abs_theta_sub_le_pntAll
  set x₀ : ℝ := Real.exp (200 + 80 * pntAllConst)
  intro x hx G hG0 hGi S hSp hS
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
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
    have hweight := hw x t hxx₀ hsqt htx W hmem
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

end RMF
