/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UAssemblyExplicit
import RMF.Analysis.FracMellinExplicit

/-!
# The remainder's windows, II: the numerals

The numbers the windows of `Z_R` are summed with.  `m_j = ∫_{e^{j-4}}^{e^{j-3}}|φ̂(½+σ+it)|²dt` is
the mass of the far window `j`.

* **Masses**: the windows are adjacent, so `∑_{j<J₀} m_j ≤ 0.6305`
  (`RMF.sum_setIntegral_normSq_fracMellin_far_le`); for `j ≥ 13`, by the decay bound,
  `m_j ≤ (e-1)e^{3-j}(j - 1.999)²` (`RMF.setIntegral_normSq_fracMellin_far_le_cap`); the tail
  `∫_{t>T}|φ̂|² ≤ 90T^{-1/2}` for `T ≥ 1` (`RMF.setIntegral_Ioi_normSq_fracMellin_le_tail`).
* **The chaos constants** at `q = ½`, `E₀ ≤ 1/160000`, `T = 30`, `κ = 8`, `λ = 49`, `δ = 1/50`,
  `β = 11/20`: a mesoscopic window (level `65`, shift `≤ e^{101}`) `≤ 7.08`
  (`RMF.fracMesoChaosConst_le`); the far window `j` (level `65 + j`, shift `e^{2j+102}`)
  `≤ 0.81√(78.07 + j)` (`RMF.fracFarChaosConst_le`).
* **The sums**: `∑_{j<J} 0.81√(78.07+j)(1.195m_j)^{1/2} ≤ 26.6` for `J ≥ 13`
  (`RMF.sum_fracFar_weight_le`: Cauchy–Schwarz on `j < 13`, geometric beyond), and
  `∑_{4≤k<K}(0.7151(σ²+e^{-2k})/2)^{1/2} ≤ 0.598(Kσ + 0.03)` (`RMF.sum_fracMeso_weight_le`).
-/

open MeasureTheory

namespace RMF

/-! ### Window masses -/

/-- **The far windows below `e^{J₀-4}`, together**: the windows `[e^{j-4}, e^{j-3}]` are adjacent,
so their masses add up to `∫_{e^{-4}}^{e^{J₀-4}}|φ̂|² ≤ 0.6305`
(`RMF.setIntegral_normSq_fracMellin_le`). -/
theorem sum_setIntegral_normSq_fracMellin_far_le {σ : ℝ} (hσ : 0 ≤ σ) (J₀ : ℕ) :
    ∑ j ∈ Finset.range J₀, ∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1)
        (Real.exp ((j : ℝ) - 3)), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 ≤ 0.6305 := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun j : ℕ => Real.exp ((j : ℝ) - 4) := ⟨_, rfl⟩
  have hlo : ∀ j : ℕ, Real.exp ((j : ℝ) - 3) / Real.exp 1 = a j := fun j => by
    rw [ha, ← Real.exp_sub]
    congr 1
    ring
  have hhi : ∀ j : ℕ, Real.exp ((j : ℝ) - 3) = a (j + 1) := fun j => by
    rw [ha]
    push_cast
    congr 1
    ring
  have hle : ∀ j k : ℕ, j ≤ k → a j ≤ a k := fun j k hjk => by
    rw [ha]
    have : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
    exact Real.exp_le_exp.2 (by linarith)
  have ha0 : 0 < a 0 := by rw [ha]; exact Real.exp_pos _
  have hρi := integrable_normSq_fracMellin (σ := σ) (by linarith)
  have hterm : ∀ j ∈ Finset.range J₀, (∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1)
      (Real.exp ((j : ℝ) - 3)), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
      = ∫ t in a j..a (j + 1), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := fun j _ => by
    rw [hlo j, hhi j, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (hle j (j + 1) (Nat.le_succ j))]
  rw [Finset.sum_congr rfl hterm,
    intervalIntegral.sum_integral_adjacent_intervals fun k _ => hρi.intervalIntegrable,
    intervalIntegral.integral_of_le (hle 0 J₀ (Nat.zero_le _))]
  exact setIntegral_normSq_fracMellin_le hσ fun t ht => lt_trans ha0 ht.1

/-- `e^{-9} ≤ 1/8000`. -/
lemma exp_neg_nine_le : Real.exp (-9) ≤ 1 / 8000 := by
  interval_decide (trust := kernel)

/-- **A far window's mass from the decay**: for `j ≥ 13`,
`∫_{e^{j-4}}^{e^{j-3}}|φ̂(½+σ+it)|²dt ≤ (e - 1)e^{3-j}(j - 1.999)²`: on the window
`|φ̂| ≤ (1 + 1/t + log(1+t))/t ≤ (j - 1.999)/t` (`RMF.norm_fracMellin_le_decay`), and
`∫_{T/e}^{T}t^{-2}dt = (e - 1)/T`. -/
theorem setIntegral_normSq_fracMellin_far_le_cap {σ : ℝ} (hσ : 0 ≤ σ) {j : ℕ} (hj : 13 ≤ j) :
    ∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1) (Real.exp ((j : ℝ) - 3)),
        ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2
      ≤ (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ)) * ((j : ℝ) - 1.999) ^ 2 := by
  have hjR : (13 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.exp ((j : ℝ) - 3) := ⟨_, rfl⟩
  rw [← hT]
  have hT0 : 0 < T := by rw [hT]; exact Real.exp_pos _
  have he1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ha0 : 0 < T / Real.exp 1 := div_pos hT0 (Real.exp_pos 1)
  have haT : T / Real.exp 1 ≤ T := div_le_self hT0.le he1.le
  have hTe : T / Real.exp 1 = Real.exp ((j : ℝ) - 4) := by
    rw [hT, ← Real.exp_sub]
    congr 1
    ring
  have hTinv : T⁻¹ = Real.exp (3 - (j : ℝ)) := by
    rw [hT, ← Real.exp_neg]
    congr 1
    ring
  have h9 := exp_neg_nine_le
  have he4 : Real.exp (4 - (j : ℝ)) ≤ Real.exp (-9) := Real.exp_le_exp.2 (by linarith)
  have he3 : Real.exp (3 - (j : ℝ)) ≤ Real.exp (-9) := Real.exp_le_exp.2 (by linarith)
  -- the pointwise cap
  have hpt : ∀ t ∈ Set.Icc (T / Real.exp 1) T, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2
      ≤ ((j : ℝ) - 1.999) ^ 2 * t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    have hret : (1 / 2 + σ + t * Complex.I : ℂ).re = 1 / 2 + σ := by simp
    have himt : (1 / 2 + σ + t * Complex.I : ℂ).im = t := by simp
    have hre : 1 / 2 ≤ (1 / 2 + σ + t * Complex.I : ℂ).re := by rw [hret]; linarith
    have him0 : (1 / 2 + σ + t * Complex.I : ℂ).im ≠ 0 := by rw [himt]; exact ht0.ne'
    have hdec := norm_fracMellin_le_decay hre him0
    have him : |(1 / 2 + σ + t * Complex.I : ℂ).im| = t := by rw [himt, abs_of_pos ht0]
    rw [him] at hdec
    have h1 : 1 / t ≤ Real.exp (4 - (j : ℝ)) := by
      have h := one_div_le_one_div_of_le ha0 ht.1
      rw [hTe] at h
      calc 1 / t ≤ 1 / Real.exp ((j : ℝ) - 4) := h
        _ = Real.exp (4 - (j : ℝ)) := by
          rw [one_div, ← Real.exp_neg]
          ring_nf
    have h2 : Real.log (1 + t) ≤ (j : ℝ) - 3 + Real.exp (3 - (j : ℝ)) := by
      have hlog1 : Real.log (1 + t) ≤ Real.log (1 + T) :=
        Real.log_le_log (by linarith) (by linarith [ht.2])
      have hsplit : 1 + T = T * (1 + T⁻¹) := by
        rw [mul_add, mul_one, mul_inv_cancel₀ hT0.ne']
        ring
      have hlog2 : Real.log (1 + T) = Real.log T + Real.log (1 + T⁻¹) := by
        rw [hsplit, Real.log_mul hT0.ne' (by positivity)]
      have hlogT : Real.log T = (j : ℝ) - 3 := by rw [hT, Real.log_exp]
      have hlog3 : Real.log (1 + T⁻¹) ≤ Real.exp (3 - (j : ℝ)) := by
        have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + T⁻¹)
        rw [← hTinv]
        linarith
      linarith
    have hlog0 : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
    have hnum : 1 + 1 / |(1 / 2 + σ + t * Complex.I : ℂ).im| + Real.log (1 + t)
        ≤ (j : ℝ) - 1.999 := by
      rw [him]
      linarith
    have hnum0 : 0 ≤ 1 + 1 / t + Real.log (1 + t) := by positivity
    rw [him] at hnum
    have hφ : ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ≤ ((j : ℝ) - 1.999) / t :=
      le_trans hdec (div_le_div_of_nonneg_right hnum ht0.le)
    have hrw : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
    rw [hrw]
    calc ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 ≤ (((j : ℝ) - 1.999) / t) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hφ 2
      _ = ((j : ℝ) - 1.999) ^ 2 * (t ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
  -- the integral of `t^{-2}`
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Icc (T / Real.exp 1) T) :=
    continuousOn_id.rpow_const fun t ht => Or.inl (lt_of_lt_of_le ha0 ht.1).ne'
  have hval : (∫ t in Set.Icc (T / Real.exp 1) T, t ^ (-2 : ℝ))
      = (T / Real.exp 1)⁻¹ - T⁻¹ := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le haT,
      integral_rpow (Or.inr ⟨by norm_num, ?_⟩)]
    · rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, Real.rpow_neg_one]
      ring
    · rw [Set.uIcc_of_le haT]
      exact fun h => absurd h.1 (not_le.2 ha0)
  have hρi := (integrable_normSq_fracMellin (σ := σ) (by linarith)).integrableOn
    (s := Set.Icc (T / Real.exp 1) T)
  calc (∫ t in Set.Icc (T / Real.exp 1) T, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
      ≤ ∫ t in Set.Icc (T / Real.exp 1) T, ((j : ℝ) - 1.999) ^ 2 * t ^ (-2 : ℝ) :=
        setIntegral_mono_on hρi (hcont.integrableOn_Icc.const_mul _) measurableSet_Icc hpt
    _ = ((j : ℝ) - 1.999) ^ 2 * ((T / Real.exp 1)⁻¹ - T⁻¹) := by
        rw [integral_const_mul, hval]
    _ = (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ)) * ((j : ℝ) - 1.999) ^ 2 := by
        rw [inv_div, div_eq_mul_inv, hTinv]
        ring

/-- **The tail mass**: for `T ≥ 1`, `∫_{t>T}|φ̂(½+σ+it)|²dt ≤ 90T^{-1/2}`: for `t ≥ 1`,
`|φ̂| ≤ (1 + 1/t + log(1+t))/t ≤ 6.6932t^{1/4}/t` (`log(1+t) ≤ log 2 + 4t^{1/4}`), and
`∫_{t>T}t^{-3/2}dt = 2T^{-1/2}`. -/
theorem setIntegral_Ioi_normSq_fracMellin_le_tail {σ : ℝ} (hσ : 0 ≤ σ) {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in Set.Ioi T, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 ≤ 90 * T ^ (-(1 / 2 : ℝ)) := by
  have hT0 : 0 < T := by linarith
  have hpt : ∀ t ∈ Set.Ioi T, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2
      ≤ 44.8 * t ^ (-(3 / 2 : ℝ)) := by
    intro t ht
    have ht1 : 1 ≤ t := le_trans hT (le_of_lt ht)
    have ht0 : 0 < t := by linarith
    have hret : (1 / 2 + σ + t * Complex.I : ℂ).re = 1 / 2 + σ := by simp
    have himt : (1 / 2 + σ + t * Complex.I : ℂ).im = t := by simp
    have hre : 1 / 2 ≤ (1 / 2 + σ + t * Complex.I : ℂ).re := by rw [hret]; linarith
    have him0 : (1 / 2 + σ + t * Complex.I : ℂ).im ≠ 0 := by rw [himt]; exact ht0.ne'
    have hdec := norm_fracMellin_le_decay hre him0
    have him : |(1 / 2 + σ + t * Complex.I : ℂ).im| = t := by rw [himt, abs_of_pos ht0]
    rw [him] at hdec
    -- `1 + 1/t + log(1+t) ≤ 6.6932 t^{1/4}`
    set u := t ^ (1 / 4 : ℝ) with hu
    have hu1 : 1 ≤ u := Real.one_le_rpow ht1 (by norm_num)
    have hlogt : Real.log t ≤ 4 * u := by
      have := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 1 / 4)
      rw [← hu] at this
      linarith
    have hlog2 : Real.log (1 + t) ≤ 0.6932 + 4 * u := by
      have h1 : Real.log (1 + t) ≤ Real.log (2 * t) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul two_ne_zero ht0.ne'] at h1
      linarith [Real.log_two_lt_d9]
    have hinv : 1 / t ≤ 1 := by rw [div_le_one ht0]; exact ht1
    have hnum : 1 + 1 / t + Real.log (1 + t) ≤ 6.6932 * u := by linarith
    have hnum0 : 0 ≤ 1 + 1 / t + Real.log (1 + t) := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + t)
      positivity
    have hφ : ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ≤ 6.6932 * u / t :=
      le_trans hdec (div_le_div_of_nonneg_right hnum ht0.le)
    have hu2 : u ^ 2 = t ^ (1 / 2 : ℝ) := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
      norm_num
    have hpow : t ^ (1 / 2 : ℝ) / t ^ 2 = t ^ (-(3 / 2 : ℝ)) := by
      rw [show (-(3 / 2 : ℝ)) = 1 / 2 - (2 : ℕ) by norm_num, Real.rpow_sub ht0,
        Real.rpow_natCast]
    calc ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 ≤ (6.6932 * u / t) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hφ 2
      _ = 6.6932 ^ 2 * (t ^ (1 / 2 : ℝ) / t ^ 2) := by rw [div_pow, mul_pow, hu2]; ring
      _ ≤ 44.8 * (t ^ (1 / 2 : ℝ) / t ^ 2) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = 44.8 * t ^ (-(3 / 2 : ℝ)) := by rw [hpow]
  have hρi := (integrable_normSq_fracMellin (σ := σ) (by linarith)).integrableOn
    (s := Set.Ioi T)
  have hri : IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (Set.Ioi T) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hT0
  calc (∫ t in Set.Ioi T, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
      ≤ ∫ t in Set.Ioi T, 44.8 * t ^ (-(3 / 2 : ℝ)) :=
        setIntegral_mono_on hρi (hri.const_mul _) measurableSet_Ioi hpt
    _ = 44.8 * (2 * T ^ (-(1 / 2 : ℝ))) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT0]
        norm_num
        ring
    _ ≤ 90 * T ^ (-(1 / 2 : ℝ)) := by
        have := Real.rpow_nonneg hT0.le (-(1 / 2 : ℝ))
        nlinarith

/-! ### The chaos constants -/

/-- `exp(½ log u) = √u` for `u > 0`. -/
lemma exp_half_mul_log {u : ℝ} (hu : 0 < u) : Real.exp (1 / 2 * Real.log u) = Real.sqrt u := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu, mul_comm]

/-- **The mesoscopic windows' chaos constant**: level `65`, `λ = 49`, `T = 30`, `κ = 8`,
`δ = 1/50`, `β = 11/20`, at a level shift `e^{D-k} ≤ e^{101}` and `0 ≤ E₀ ≤ 1/160000`: at most
`7.08`. -/
theorem fracMesoChaosConst_le {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 160000) {D k : ℕ}
    (hDk : (D : ℝ) - k ≤ 101) :
    shiftMomentConst 1 (radAveragedConst E₀ (11 / 20) 30 8)
      (radBlockBadConst E₀ (11 / 20) * Real.exp ((D : ℝ) - k)) 65
      (radAveragedShift E₀ (11 / 20) 30 8) 49 (1 / 50) (1 / 2) ≤ 7.08 := by
  have hCi := radAveragedConst_le_B hE₀ hE₀1
  have hCi0 : 0 ≤ radAveragedConst E₀ (11 / 20) 30 8 := by
    have := one_le_radAveragedConst hE₀ (by norm_num : (0 : ℝ) ≤ 11 / 20) (by norm_num)
      (by norm_num : (4 : ℝ) < 30) (by norm_num : (1 : ℝ) ≤ 8)
    linarith
  have hs := radAveragedShift_le_B hE₀ hE₀1
  have hs0 := radAveragedShift_nonneg hE₀ (by norm_num : (0 : ℝ) ≤ 11 / 20) (by norm_num)
    (by norm_num : (4 : ℝ) < 30) (by norm_num : (1 : ℝ) ≤ 8)
  have hCb8 := radBlockBadConst_mul_le_B hE₀1
  have hCbpos := radBlockBadConst_pos E₀ (by norm_num : (1 : ℝ) / 2 < 11 / 20)
  have hCb : radBlockBadConst E₀ (11 / 20) * Real.exp ((D : ℝ) - k)
      ≤ Real.exp (11928 / 100) := by
    have heq : radBlockBadConst E₀ (11 / 20) * Real.exp ((D : ℝ) - k)
        = radBlockBadConst E₀ (11 / 20) * Real.exp 8 * Real.exp ((D : ℝ) - k - 8) := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
    rw [heq]
    calc radBlockBadConst E₀ (11 / 20) * Real.exp 8 * Real.exp ((D : ℝ) - k - 8)
        ≤ Real.exp (2628 / 100) * Real.exp 93 :=
          mul_le_mul hCb8 (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
            (Real.exp_pos _).le
      _ = Real.exp (11928 / 100) := by rw [← Real.exp_add]; norm_num
  have hCb0 : 0 ≤ radBlockBadConst E₀ (11 / 20) * Real.exp ((D : ℝ) - k) :=
    mul_nonneg hCbpos.le (Real.exp_pos _).le
  have hAs : (0 : ℝ) ≤ 65 + radAveragedShift E₀ (11 / 20) 30 8 := by linarith
  have hU : (65 + radAveragedShift E₀ (11 / 20) 30 8) * (1 - 1 / 2) ≤ 390345 / 10000 := by
    linarith
  have h := shiftMomentConst_le_exp (C₁ := 1) (N := 1)
    (Ci := radAveragedConst E₀ (11 / 20) 30 8) (Ci' := 12285 / 10000)
    (Cb := radBlockBadConst E₀ (11 / 20) * Real.exp ((D : ℝ) - k)) (LB := 11928 / 100)
    (s := radAveragedShift E₀ (11 / 20) 30 8) (U := 390345 / 10000) (IS := 10102 / 10000)
    (S1 := 1156519 / 1000000) (S2 := 181016 / 1000000) (EM2 := 135336 / 1000000) (A := 65)
    (lam := 49) (δ := 1 / 50) (q := 1 / 2) (by norm_num) (by norm_num) zero_le_one le_rfl
    hCi0 hCi hCb0 hCb hAs hU (by norm_num) (by norm_num) inv_sqrt_one_sub_fiftieth_le
    inv_one_sub_exp_neg_two_le exp_neg_two_mul_inv_sq_le exp_neg_two_le_cert
  refine le_trans h (max_le ?_ ?_)
  · interval_decide (trust := kernel)
  · interval_decide (trust := kernel)

/-- `exp(½ log 50) ≤ 7.0711`. -/
lemma exp_half_log_fifty_le : Real.exp (1 / 2 * Real.log (1 * (1 + 49))) ≤ 7.0711 := by
  interval_decide (trust := kernel)

/-- `exp(½ log((1 + 1/49)·1.0102·1.2285)) ≤ 1.12533`. -/
lemma exp_half_log_far_le :
    Real.exp (1 / 2 * Real.log ((1 + 1 / 49) * (10102 / 10000) * (12285 / 10000))) ≤ 1.12533 := by
  interval_decide (trust := kernel)

/-- `e^{-4.86} ≤ 0.00776`. -/
lemma exp_neg_486_le : Real.exp (-(486 / 100)) ≤ 0.00776 := by
  interval_decide (trust := kernel)

/-- **The far windows' chaos constant**: the window `j` at level `65 + j` and level shift
`e^{2j+102}`, so that the bad sets' factor `(C_b e^{2j+102}e^{-2(65+j)})^{1/2}` does not depend
on `j`; `λ = 49`, `T = 30`, `κ = 8`, `δ = 1/50`, `β = 11/20`, `0 ≤ E₀ ≤ 1/160000`: at most
`0.81√(78.07 + j)`. -/
theorem fracFarChaosConst_le {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 160000) (j : ℕ) :
    shiftMomentConst 1 (radAveragedConst E₀ (11 / 20) 30 8)
      (radBlockBadConst E₀ (11 / 20) * Real.exp (2 * (j : ℝ) + 102)) (65 + j)
      (radAveragedShift E₀ (11 / 20) 30 8) 49 (1 / 50) (1 / 2)
      ≤ 0.81 * Real.sqrt (78.07 + j) := by
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hCi := radAveragedConst_le_B hE₀ hE₀1
  have hCi0 : 0 ≤ radAveragedConst E₀ (11 / 20) 30 8 := by
    have := one_le_radAveragedConst hE₀ (by norm_num : (0 : ℝ) ≤ 11 / 20) (by norm_num)
      (by norm_num : (4 : ℝ) < 30) (by norm_num : (1 : ℝ) ≤ 8)
    linarith
  have hs := radAveragedShift_le_B hE₀ hE₀1
  have hs0 := radAveragedShift_nonneg hE₀ (by norm_num : (0 : ℝ) ≤ 11 / 20) (by norm_num)
    (by norm_num : (4 : ℝ) < 30) (by norm_num : (1 : ℝ) ≤ 8)
  have hCb8 := radBlockBadConst_mul_le_B hE₀1
  have hCbpos := radBlockBadConst_pos E₀ (by norm_num : (1 : ℝ) / 2 < 11 / 20)
  have hCb : radBlockBadConst E₀ (11 / 20) * Real.exp (2 * (j : ℝ) + 102)
      ≤ Real.exp (12028 / 100 + 2 * j) := by
    have heq : radBlockBadConst E₀ (11 / 20) * Real.exp (2 * (j : ℝ) + 102)
        = radBlockBadConst E₀ (11 / 20) * Real.exp 8 * Real.exp (2 * (j : ℝ) + 94) := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
    rw [heq]
    calc radBlockBadConst E₀ (11 / 20) * Real.exp 8 * Real.exp (2 * (j : ℝ) + 94)
        ≤ Real.exp (2628 / 100) * Real.exp (2 * (j : ℝ) + 94) :=
          mul_le_mul_of_nonneg_right hCb8 (Real.exp_pos _).le
      _ = Real.exp (12028 / 100 + 2 * j) := by rw [← Real.exp_add]; ring_nf
  have hCb0 : 0 ≤ radBlockBadConst E₀ (11 / 20) * Real.exp (2 * (j : ℝ) + 102) :=
    mul_nonneg hCbpos.le (Real.exp_pos _).le
  set U : ℝ := (78069 / 1000 + j) / 2 with hUdef
  have hU0 : 39 ≤ U := by rw [hUdef]; linarith
  have hAs : (0 : ℝ) ≤ 65 + j + radAveragedShift E₀ (11 / 20) 30 8 := by linarith
  have hU : (65 + j + radAveragedShift E₀ (11 / 20) 30 8) * (1 - 1 / 2) ≤ U := by
    rw [hUdef]
    linarith
  have h := shiftMomentConst_le_exp (C₁ := 1) (N := 1)
    (Ci := radAveragedConst E₀ (11 / 20) 30 8) (Ci' := 12285 / 10000)
    (Cb := radBlockBadConst E₀ (11 / 20) * Real.exp (2 * (j : ℝ) + 102))
    (LB := 12028 / 100 + 2 * j) (s := radAveragedShift E₀ (11 / 20) 30 8) (U := U)
    (IS := 10102 / 10000) (S1 := 1156519 / 1000000) (S2 := 181016 / 1000000)
    (EM2 := 135336 / 1000000) (A := 65 + j) (lam := 49) (δ := 1 / 50) (q := 1 / 2) (by norm_num)
    (by norm_num) zero_le_one le_rfl hCi0 hCi hCb0 hCb hAs hU (by norm_num) (by norm_num)
    inv_sqrt_one_sub_fiftieth_le inv_one_sub_exp_neg_two_le exp_neg_two_mul_inv_sq_le
    exp_neg_two_le_cert
  -- the target is at least `1.1455√U`
  have hsqU0 : 0 ≤ Real.sqrt U := Real.sqrt_nonneg _
  have hsqU : 6 ≤ Real.sqrt U := by
    rw [show (6 : ℝ) = Real.sqrt (6 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq2 : 1.4142 ≤ Real.sqrt 2 := by
    rw [show (1.4142 : ℝ) = Real.sqrt (1.4142 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have htarget : 1.4142 * 0.81 * Real.sqrt U ≤ 0.81 * Real.sqrt (78.07 + j) := by
    have h1 : Real.sqrt (2 * U) ≤ Real.sqrt (78.07 + j) :=
      Real.sqrt_le_sqrt (by rw [hUdef]; linarith)
    rw [Real.sqrt_mul (by norm_num)] at h1
    nlinarith
  refine le_trans h (max_le ?_ ?_)
  · have h1 := exp_half_log_fifty_le
    have h8 : 8.83 ≤ Real.sqrt (78.07 + j) := by
      rw [show (8.83 : ℝ) = Real.sqrt (8.83 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  · have hexpo : (1 - 1 / 2 : ℝ) * (12028 / 100 + 2 * j - 2 * (65 + j)) = -(486 / 100) := by
      ring
    rw [hexpo, Real.log_one, mul_zero, Real.exp_zero, exp_half_mul_log (u := U) (by linarith),
      exp_half_mul_log (u := U + 1) (by linarith)]
    have hc := exp_half_log_far_le
    have hE := exp_neg_486_le
    have hc0 : 0 ≤ Real.exp (1 / 2 * Real.log ((1 + 1 / 49) * (10102 / 10000) * (12285 / 10000))) :=
      (Real.exp_pos _).le
    have hE0 : 0 ≤ Real.exp (-(486 / 100)) := (Real.exp_pos _).le
    have hsq1 : Real.sqrt (U + 1) ≤ Real.sqrt U + 1 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ U)]
    have hin : Real.sqrt U + Real.exp (-(486 / 100)) * (Real.sqrt (U + 1) * (1156519 / 1000000)
        + 181016 / 1000000) ≤ Real.sqrt U + 0.00776 * ((Real.sqrt U + 1) * (1156519 / 1000000)
        + 181016 / 1000000) := by
      have : Real.exp (-(486 / 100)) * (Real.sqrt (U + 1) * (1156519 / 1000000) + 181016 / 1000000)
          ≤ 0.00776 * ((Real.sqrt U + 1) * (1156519 / 1000000) + 181016 / 1000000) :=
        mul_le_mul hE (by nlinarith) (by positivity) (by norm_num)
      linarith
    have hin0 : 0 ≤ Real.sqrt U + 0.00776 * ((Real.sqrt U + 1) * (1156519 / 1000000)
        + 181016 / 1000000) := by positivity
    have hstep : Real.exp (1 / 2 * Real.log ((1 + 1 / 49) * (10102 / 10000) * (12285 / 10000)))
        * (Real.sqrt U + Real.exp (-(486 / 100)) * (Real.sqrt (U + 1) * (1156519 / 1000000)
          + 181016 / 1000000))
        ≤ 1.12533 * (Real.sqrt U + 0.00776 * ((Real.sqrt U + 1) * (1156519 / 1000000)
          + 181016 / 1000000)) :=
      mul_le_mul hc hin (by positivity) (by norm_num)
    have hlast : 135336 / 1000000 * Real.exp (-(486 / 100)) * 1 ≤ 135336 / 1000000 * 0.00776 := by
      nlinarith
    nlinarith

/-! ### The sums -/

/-- One far window beyond `j = 13`, against a geometric series: for `i ≥ 0`,
`0.81√(91.07+i)·(1.195(e-1)e^{-10-i}(11.001+i)²)^{1/2} ≤ 0.8212e^{-2i/5}`, from
`91.07 + i ≤ 91.07e^{i/91.07}` and `11.001 + i ≤ 11.001e^{i/11.001}`. -/
lemma fracFar_tail_term_le (i : ℕ) :
    0.81 * Real.sqrt (91.07 + i)
        * Real.sqrt (1.195 * ((Real.exp 1 - 1) * Real.exp (-10 - (i : ℝ)) * (11.001 + i) ^ 2))
      ≤ 0.8212 * Real.exp (-(2 / 5)) ^ i := by
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have he1 : Real.exp 1 - 1 ≤ 1.71829 := by linarith [Real.exp_one_lt_d9]
  have he0 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he10 : Real.exp (-10) ≤ 0.00004541 := by interval_decide (trust := kernel)
  have ha : 91.07 + (i : ℝ) ≤ 91.07 * Real.exp ((i : ℝ) * (100 / 9107)) := by
    have := Real.add_one_le_exp ((i : ℝ) * (100 / 9107))
    linarith
  have hb : 11.001 + (i : ℝ) ≤ 11.001 * Real.exp ((i : ℝ) * (1000 / 11001)) := by
    have := Real.add_one_le_exp ((i : ℝ) * (1000 / 11001))
    linarith
  have hb2 : (11.001 + (i : ℝ)) ^ 2 ≤ 11.001 ^ 2 * Real.exp ((i : ℝ) * (1000 / 11001)) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hb 2
  -- the exponents
  have hL : Real.exp ((i : ℝ) * (100 / 9107)) * Real.exp ((i : ℝ) * (1000 / 11001)) ^ 2
      * Real.exp (-10 - (i : ℝ))
      = Real.exp ((i : ℝ) * (100 / 9107) + ((i : ℝ) * (1000 / 11001) + (i : ℝ) * (1000 / 11001))
        + (-10 - (i : ℝ))) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
    ring
  have hR : Real.exp (-10) * Real.exp (-(2 / 5)) ^ i * Real.exp (-(2 / 5)) ^ i
      = Real.exp (-10 + (i : ℝ) * (-(2 / 5)) + (i : ℝ) * (-(2 / 5))) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul]
  have hexp : Real.exp ((i : ℝ) * (100 / 9107)) * Real.exp ((i : ℝ) * (1000 / 11001)) ^ 2
      * Real.exp (-10 - (i : ℝ))
      ≤ Real.exp (-10) * Real.exp (-(2 / 5)) ^ i * Real.exp (-(2 / 5)) ^ i := by
    rw [hL, hR]
    exact Real.exp_le_exp.2 (by linarith)
  have hE0 : 0 ≤ Real.exp (-(2 / 5)) ^ i := by positivity
  -- square both sides
  have hrhs : 0 ≤ 0.8212 * Real.exp (-(2 / 5)) ^ i := by positivity
  have hA0 : 0 ≤ 91.07 + (i : ℝ) := by linarith
  have hB0 : 0 ≤ 1.195 * ((Real.exp 1 - 1) * Real.exp (-10 - (i : ℝ)) * (11.001 + i) ^ 2) := by
    positivity
  have hX0 : 0 ≤ Real.exp ((i : ℝ) * (100 / 9107)) := (Real.exp_pos _).le
  have hY0 : 0 ≤ Real.exp ((i : ℝ) * (1000 / 11001)) ^ 2 := by positivity
  have hZ0 : 0 ≤ Real.exp (-10 - (i : ℝ)) := (Real.exp_pos _).le
  have hsq : (0.81 * Real.sqrt (91.07 + i)
        * Real.sqrt (1.195 * ((Real.exp 1 - 1) * Real.exp (-10 - (i : ℝ)) * (11.001 + i) ^ 2)))
        ^ 2 ≤ (0.8212 * Real.exp (-(2 / 5)) ^ i) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    calc 0.81 ^ 2 * (91.07 + (i : ℝ)) * (1.195 * ((Real.exp 1 - 1) * Real.exp (-10 - (i : ℝ))
          * (11.001 + i) ^ 2))
        ≤ 0.81 ^ 2 * (91.07 * Real.exp ((i : ℝ) * (100 / 9107))) * (1.195 * ((Real.exp 1 - 1)
          * Real.exp (-10 - (i : ℝ))
          * (11.001 ^ 2 * Real.exp ((i : ℝ) * (1000 / 11001)) ^ 2))) := by
          gcongr
      _ = 0.81 ^ 2 * 91.07 * 1.195 * (Real.exp 1 - 1) * 11.001 ^ 2
          * (Real.exp ((i : ℝ) * (100 / 9107)) * Real.exp ((i : ℝ) * (1000 / 11001)) ^ 2
            * Real.exp (-10 - (i : ℝ))) := by ring
      _ ≤ 0.81 ^ 2 * 91.07 * 1.195 * 1.71829 * 11.001 ^ 2
          * (Real.exp (-10) * Real.exp (-(2 / 5)) ^ i * Real.exp (-(2 / 5)) ^ i) := by
          gcongr
      _ ≤ 0.81 ^ 2 * 91.07 * 1.195 * 1.71829 * 11.001 ^ 2
          * (0.00004541 * Real.exp (-(2 / 5)) ^ i * Real.exp (-(2 / 5)) ^ i) := by
          gcongr
      _ ≤ (0.8212 * Real.exp (-(2 / 5)) ^ i) ^ 2 := by
          have hEE : 0 ≤ Real.exp (-(2 / 5)) ^ i * Real.exp (-(2 / 5)) ^ i := by positivity
          nlinarith
  have hlhs0 : 0 ≤ 0.81 * Real.sqrt (91.07 + i)
      * Real.sqrt (1.195 * ((Real.exp 1 - 1) * Real.exp (-10 - (i : ℝ)) * (11.001 + i) ^ 2)) := by
    positivity
  exact (pow_le_pow_iff_left₀ hlhs0 hrhs (by norm_num : (2 : ℕ) ≠ 0)).1 hsq

/-- **The far windows' weighted masses, summed**: for `J ≥ 13`,
`∑_{j<J} 0.81√(78.07+j)·(1.195 m_j)^{1/2} ≤ 26.6`: Cauchy–Schwarz on `j < 13` against
`∑ m_j ≤ 0.6305` (`RMF.sum_setIntegral_normSq_fracMellin_far_le`), and beyond the caps
(`RMF.setIntegral_normSq_fracMellin_far_le_cap`), geometric with ratio `e^{-2/5}`. -/
theorem sum_fracFar_weight_le {σ : ℝ} (hσ : 0 ≤ σ) {J : ℕ} (hJ : 13 ≤ J) :
    ∑ j ∈ Finset.range J, 0.81 * Real.sqrt (78.07 + j)
        * (1.195 * ∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1) (Real.exp ((j : ℝ) - 3)),
          ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ (1 / 2 : ℝ) ≤ 26.6 := by
  set m : ℕ → ℝ := fun j => ∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1)
    (Real.exp ((j : ℝ) - 3)), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 with hm
  have hm0 : ∀ j, 0 ≤ m j := fun j => integral_nonneg fun t => sq_nonneg _
  have hterm : ∀ j : ℕ, (1.195 * m j) ^ (1 / 2 : ℝ) = Real.sqrt 1.195 * Real.sqrt (m j) := by
    intro j
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num)]
  rw [← Finset.sum_range_add_sum_Ico _ hJ]
  -- the head, by Cauchy–Schwarz
  have hhead : ∑ j ∈ Finset.range 13, 0.81 * Real.sqrt (78.07 + j) * (1.195 * m j) ^ (1 / 2 : ℝ)
      ≤ 24.07 := by
    have hA : ∀ j ∈ Finset.range 13, 0.81 * Real.sqrt (78.07 + j) * (1.195 * m j) ^ (1 / 2 : ℝ)
        ≤ 0.81 * Real.sqrt 90.07 * Real.sqrt 1.195 * Real.sqrt (m j) := by
      intro j hj
      have hj12 : (j : ℝ) ≤ 12 := by
        have := Finset.mem_range.1 hj
        have : j ≤ 12 := by omega
        exact_mod_cast this
      rw [hterm j]
      have h1 : Real.sqrt (78.07 + j) ≤ Real.sqrt 90.07 := Real.sqrt_le_sqrt (by linarith)
      have h2 : 0 ≤ Real.sqrt 1.195 * Real.sqrt (m j) := by positivity
      calc 0.81 * Real.sqrt (78.07 + j) * (Real.sqrt 1.195 * Real.sqrt (m j))
          ≤ 0.81 * Real.sqrt 90.07 * (Real.sqrt 1.195 * Real.sqrt (m j)) := by gcongr
        _ = 0.81 * Real.sqrt 90.07 * Real.sqrt 1.195 * Real.sqrt (m j) := by ring
    refine le_trans (Finset.sum_le_sum hA) ?_
    rw [← Finset.mul_sum]
    have hCS : (∑ j ∈ Finset.range 13, Real.sqrt (m j)) ^ 2 ≤ 13 * 0.6305 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range 13) (fun _ => (1 : ℝ))
        (fun j => Real.sqrt (m j))
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Real.sq_sqrt (hm0 _)] at h
      have hsum := sum_setIntegral_normSq_fracMellin_far_le hσ 13
      push_cast at h
      nlinarith
    have hS0 : 0 ≤ ∑ j ∈ Finset.range 13, Real.sqrt (m j) :=
      Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
    have hS : ∑ j ∈ Finset.range 13, Real.sqrt (m j) ≤ 2.8631 := by
      nlinarith
    have hnum : 0.81 * Real.sqrt 90.07 * Real.sqrt 1.195 ≤ 8.4035 := by
      have h1 : Real.sqrt 90.07 ≤ 9.49053 := by
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num
      have h2 : Real.sqrt 1.195 ≤ 1.093162 := by
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num
      have h3 := Real.sqrt_nonneg 90.07
      have h4 := Real.sqrt_nonneg 1.195
      nlinarith
    have hnum0 : 0 ≤ 0.81 * Real.sqrt 90.07 * Real.sqrt 1.195 := by positivity
    nlinarith
  -- the tail, against a geometric series
  have htail : ∑ j ∈ Finset.Ico 13 J, 0.81 * Real.sqrt (78.07 + j) * (1.195 * m j) ^ (1 / 2 : ℝ)
      ≤ 2.5 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hB : ∀ i ∈ Finset.range (J - 13), 0.81 * Real.sqrt (78.07 + ((13 + i : ℕ) : ℝ))
        * (1.195 * m (13 + i)) ^ (1 / 2 : ℝ) ≤ 0.8212 * Real.exp (-(2 / 5)) ^ i := by
      intro i _
      have hcap := setIntegral_normSq_fracMellin_far_le_cap hσ (j := 13 + i) (by omega)
      have hc : (1.195 * m (13 + i)) ^ (1 / 2 : ℝ) ≤ Real.sqrt (1.195
          * ((Real.exp 1 - 1) * Real.exp (-10 - (i : ℝ)) * (11.001 + i) ^ 2)) := by
        rw [← Real.sqrt_eq_rpow]
        refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (le_trans hcap (le_of_eq ?_))
          (by norm_num))
        push_cast
        ring_nf
      have hcast : (78.07 : ℝ) + ((13 + i : ℕ) : ℝ) = 91.07 + i := by push_cast; ring
      rw [hcast]
      calc 0.81 * Real.sqrt (91.07 + i) * (1.195 * m (13 + i)) ^ (1 / 2 : ℝ)
          ≤ 0.81 * Real.sqrt (91.07 + i)
            * Real.sqrt (1.195 * ((Real.exp 1 - 1) * Real.exp (-10 - (i : ℝ))
              * (11.001 + i) ^ 2)) := by gcongr
        _ ≤ 0.8212 * Real.exp (-(2 / 5)) ^ i := fracFar_tail_term_le i
    refine le_trans (Finset.sum_le_sum hB) ?_
    rw [← Finset.mul_sum]
    have hr0 : 0 ≤ Real.exp (-(2 / 5)) := (Real.exp_pos _).le
    have hr1 : Real.exp (-(2 / 5)) ≤ 0.6704 := by interval_decide (trust := kernel)
    have hgeom := geom_sum_Ico_le_of_lt_one (m := 0) (n := J - 13) hr0 (by linarith)
    rw [pow_zero, ← Finset.range_eq_Ico] at hgeom
    have hgeom' : ∑ i ∈ Finset.range (J - 13), Real.exp (-(2 / 5)) ^ i ≤ 1 / (1 - 0.6704) :=
      le_trans hgeom (one_div_le_one_div_of_le (by norm_num) (by linarith))
    have : (0.8212 : ℝ) * (1 / (1 - 0.6704)) ≤ 2.5 := by norm_num
    nlinarith
  linarith

/-- **The mesoscopic windows' weights, summed**: for `σ ≥ 0`,
`∑_{4≤k<K}(0.7151(σ² + e^{-2k})/2)^{1/2} ≤ 0.598(Kσ + 0.03)`, since
`√(σ² + e^{-2k}) ≤ σ + e^{-k}` and `∑_{k≥4}e^{-k} = e^{-4}/(1-e^{-1}) ≤ 0.03`. -/
theorem sum_fracMeso_weight_le {σ : ℝ} (hσ : 0 ≤ σ) (K : ℕ) :
    ∑ k ∈ Finset.Ico 4 K, (0.7151 * (σ ^ 2 + Real.exp (-(k : ℝ)) ^ 2) / 2) ^ (1 / 2 : ℝ)
      ≤ 0.598 * (K * σ + 0.03) := by
  have hc : Real.sqrt (0.7151 / 2) ≤ 0.598 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hterm : ∀ k ∈ Finset.Ico 4 K,
      (0.7151 * (σ ^ 2 + Real.exp (-(k : ℝ)) ^ 2) / 2) ^ (1 / 2 : ℝ)
        ≤ 0.598 * (σ + Real.exp (-1) ^ k) := by
    intro k _
    have hek : Real.exp (-(k : ℝ)) = Real.exp (-1) ^ k := by
      rw [← Real.exp_nat_mul]
      ring_nf
    rw [← hek, ← Real.sqrt_eq_rpow,
      show 0.7151 * (σ ^ 2 + Real.exp (-(k : ℝ)) ^ 2) / 2
        = 0.7151 / 2 * (σ ^ 2 + Real.exp (-(k : ℝ)) ^ 2) by ring,
      Real.sqrt_mul (by norm_num)]
    have he0 := (Real.exp_pos (-(k : ℝ))).le
    have hs : Real.sqrt (σ ^ 2 + Real.exp (-(k : ℝ)) ^ 2) ≤ σ + Real.exp (-(k : ℝ)) := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    have hs0 := Real.sqrt_nonneg (σ ^ 2 + Real.exp (-(k : ℝ)) ^ 2)
    have hc0 := Real.sqrt_nonneg (0.7151 / 2)
    exact mul_le_mul hc hs hs0 (by norm_num)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hr0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hr1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 4) (n := K) hr0 hr1
  have hnum : Real.exp (-1) ^ 4 / (1 - Real.exp (-1)) ≤ 0.03 := by
    have h4 : Real.exp (-1) ^ 4 = Real.exp (-4) := by
      rw [← Real.exp_nat_mul]
      norm_num
    have he4 := exp_neg_four_le_sharp
    have he1 : Real.exp (-1) ≤ 0.368 := by interval_decide (trust := kernel)
    rw [h4, div_le_iff₀ (by linarith)]
    linarith
  have hK : ((K - 4 : ℕ) : ℝ) * σ ≤ K * σ := by
    refine mul_le_mul_of_nonneg_right ?_ hσ
    exact_mod_cast Nat.sub_le K 4
  nlinarith

end RMF
