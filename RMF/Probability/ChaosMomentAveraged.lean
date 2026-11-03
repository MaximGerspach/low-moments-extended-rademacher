/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ChaosMomentMertens
import RMF.Probability.FreeStartAveragedSteinhaus

/-!
# The chaos moments at the averaged free start

The level-shift chaos moment bound `RMF.integral_chaosUnitShift_rpow_le_shift_of_bad` takes as a
hypothesis a bound `C_i min{1, (a + s)/√(t - ⌈a/4⌉)}` on the restricted chaos over the good sets.
Here the averaged free start (`RMF.freeStart_barrier_harper_le_averaged_steinhaus`) supplies it:

* `RMF.integral_restrictedChaosUnitShift_le_of_tilted`: the restricted chaos is at most
  `B·e^{γ + 9.0028/L₀}` once the tilted barrier probability is at most `B` at every height;
* `RMF.averagedConst` and `RMF.averagedShift`: `C_i = averagedConst·e^{γ + 9.0028/L₀}` and
  `s = averagedShift`, at the good set's log-slope `β ∈ [0, 2]`, with `β log r` absorbed linearly
  at `κ`;
* `RMF.integral_chaosUnitShift_rpow_le_averaged`: the chaos moments at these constants, past
  `harperThreshold D N` for a block count `N` with room for the levels
  (`RMF.free_start_room_of_le`), with no block count of Proposition 5: the averaged free start
  needs only `⌈a/4⌉ < n`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The restricted chaos from the tilted barrier probability.**  If at every height `t` the
barrier event `{W_j ∈ [u_j, v_j] ∀ r ≤ j ≤ n}` of the walk at `1/2 + σ + it` has tilted probability
at most `B`, then the restricted chaos on the unit window is at most `B·e^{γ + 9.0028/L₀}`: the tilt
at each height (`RMF.IsSteinhausRMF.setIntegral_normSq_eq`), and Mertens' product at `e^γ`
(`RMF.inv_log_mul_integral_normSq_shift_le_sharp`). -/
theorem integral_restrictedChaosUnitShift_le_of_tilted {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsSteinhausPrimeValues Y ν) {x σ L₀ B ϑ : ℝ} {r n : ℕ} {u v : ℕ → ℝ}
    (hL₀ : 1 ≤ L₀) (hx : Real.exp L₀ + 1 ≤ x) (hσ0 : 0 ≤ σ) (hB : 0 ≤ B)
    (hP : ∀ t : ℝ, ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1)
        (shiftLine σ t) ν) {ω | ∀ j, r ≤ j → j ≤ n →
          walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
            localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
            ∈ Set.Icc (u j) (v j)}).toReal ≤ B) :
    (∫ ω, restrictedChaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ
        (fun t => {ω | ∀ j, r ≤ j → j ≤ n →
          walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
            localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
            ∈ Set.Icc (u j) (v j)}) ω ∂ν)
      ≤ B * normSqLogSharpConst L₀ := by
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  have hσ0' : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hf' : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  have hx2 : (2 : ℝ) ≤ x := by
    have := Real.add_one_le_exp L₀
    linarith
  have hlogx0 : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hvol : volume (Set.Ioc (0 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  set y : ℕ := ⌊x⌋₊ + 1 with hydef
  set L : ℝ → Set Ω := fun t => {ω | ∀ j, r ≤ j → j ≤ n →
    walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
      ∈ Set.Icc (u j) (v j)} with hLdef
  set g : ℝ → Ω → ℝ := fun t ω =>
    ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y (shiftLine σ t) ω‖ ^ 2
    with hgdef
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) :=
    fun p => hY.measurable _ (p : Nat.Primes).2
  have hLmeas : ∀ t, MeasurableSet (L t) := fun t =>
    measurableSet_freeStartBarrier (fun m => Finset.measurable_sum _ fun p _ =>
      (measurable_localLog _).comp (hYm p)) _ _ _ _
  have hInt : Integrable
      (Function.uncurry fun (ω : Ω) (t : ℝ) => Set.indicator (L t) (g t) ω)
      (ν.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    integrable_uncurry_indicator_normSq hY y hσ0' L hLmeas
      (measurableSet_freeStartBarrier_uncurry hYm σ ϑ r n u v) hvol
  have hper : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      (∫ ω, Set.indicator (L t) (g t) ω ∂ν) ≤ B * ∫ ω, g 0 ω ∂ν := by
    intro t _
    have hs : 0 < (shiftLine σ t).re := by rw [re_shiftLine]; exact hσ0'
    rw [hf'.integral_normSq_shiftLine_eq y hσ0' 0 t, integral_indicator (hLmeas t),
      hf'.setIntegral_normSq_eq y hs (hLmeas t)]
    exact mul_le_mul_of_nonneg_right (hP t) (integral_nonneg fun ω => by positivity)
  have hjoin := integral_indicator_le_of_per_height measurableSet_Ioc hvol hInt hper
  have hvol1 : (volume (Set.Ioc (0 : ℝ) 1)).toReal = 1 := by
    rw [Real.volume_Ioc]
    norm_num
  rw [hvol1, one_mul] at hjoin
  have hswap : (∫ ω, (∫ t in Set.Ioc (0 : ℝ) 1, Set.indicator (L t) (g t) ω) ∂ν)
      = ∫ t in Set.Ioc (0 : ℝ) 1, ∫ ω, Set.indicator (L t) (g t) ω ∂ν :=
    integral_integral_swap hInt
  have hM := inv_log_mul_integral_normSq_shift_le_sharp hY hL₀ hx hσ0
  have hl : (0 : ℝ) ≤ (Real.log x)⁻¹ := inv_nonneg.2 hlogx0.le
  rw [integral_restrictedChaosUnitShift_eq]
  calc (Real.log x)⁻¹ * ∫ ω, (∫ t in Set.Ioc (0 : ℝ) 1, Set.indicator (L t) (g t) ω) ∂ν
      = (Real.log x)⁻¹ * ∫ t in Set.Ioc (0 : ℝ) 1, ∫ ω, Set.indicator (L t) (g t) ω ∂ν := by
        rw [hswap]
    _ ≤ (Real.log x)⁻¹ * (B * ∫ ω, g 0 ω ∂ν) := mul_le_mul_of_nonneg_left hjoin hl
    _ = B * ((Real.log x)⁻¹ * ∫ ω, g 0 ω ∂ν) := by ring
    _ ≤ B * normSqLogSharpConst L₀ := mul_le_mul_of_nonneg_left hM hB

/-! ### The constants -/

/-- **Probability Result 1's constant at the Steinhaus variance floor** `0.475e^{-2E₀}`
(`RMF.blockGaussVar_lower_of_le_sharp`), at the Gaussian constant with the split `M = 25`
(`RMF.result1Affine_sharp`): `K = √(2·25/(24·0.475πe^{-2E₀}))`, about `1.18` at `E₀ = 0`. -/
noncomputable def averagedK (E₀ : ℝ) : ℝ :=
  √(2 * 25 / (24 * (Real.pi * (0.475 * Real.exp (-(2 * E₀))))))

lemma averagedK_sq_mul (E₀ : ℝ) :
    2 * ((25 : ℕ) : ℝ) ≤ averagedK E₀ ^ 2 * (((25 : ℕ) : ℝ) - 1)
      * (Real.pi * (0.475 * Real.exp (-(2 * E₀)))) := by
  have hv : 0 < Real.pi * (0.475 * Real.exp (-(2 * E₀))) := by positivity
  rw [averagedK, Real.sq_sqrt (by positivity)]
  push_cast
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

lemma one_le_averagedK {E₀ : ℝ} (hE₀ : 0 ≤ E₀) : 1 ≤ averagedK E₀ := by
  have hv : 0 < Real.pi * (0.475 * Real.exp (-(2 * E₀))) := by positivity
  have he : Real.exp (-(2 * E₀)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hpi := Real.pi_lt_d2
  have hle : 24 * (Real.pi * (0.475 * Real.exp (-(2 * E₀)))) ≤ 2 * 25 := by
    have h1 : Real.pi * (0.475 * Real.exp (-(2 * E₀))) ≤ Real.pi * 0.475 :=
      mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
    linarith
  rw [averagedK]
  exact Real.one_le_sqrt.2 ((one_le_div (by positivity)).2 hle)

/-- **The constant of the averaged free start at log-slope `β`**, `C_i` divided by
`e^{γ + 9.0028/L₀}`: `(1 + e^{-100})K(1 + β/(4κ))/(1 - 2β/T)` with `K = averagedK E₀`. -/
noncomputable def averagedConst (E₀ β T κ : ℝ) : ℝ :=
  (1 + Real.exp (-100)) * averagedK E₀ * (1 + β / (4 * κ)) / (1 - 2 * β / T)

/-- **The level shift of the averaged free start at log-slope `β`**:
`3C + β log κ + β/κ + β log 2 + (2 - β) + 45/32 + result1SharpShift (9/2) β K T 25`, with the drift
`C = driftSharpOf E₀ 16` and `K = averagedK E₀`.  The `2 - β` is the free start's `+2`, which the
concavity of `log` pays back only at `β = 2` (`RMF.averaged_level_le`). -/
noncomputable def averagedShift (E₀ β T κ : ℝ) : ℝ :=
  3 * driftSharpOf E₀ 16 + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 45 / 32
    + result1SharpShift (9 / 2) β (averagedK E₀) T 25

lemma one_le_averagedK_mul {E₀ T : ℝ} (hE₀ : 0 ≤ E₀) (hT : 4 < T) : 1 ≤ averagedK E₀ * T := by
  have hK := one_le_averagedK hE₀
  nlinarith

lemma averagedShift_nonneg {E₀ β T κ : ℝ} (hE₀ : 0 ≤ E₀) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2)
    (hT : 4 < T) (hκ : 1 ≤ κ) : 0 ≤ averagedShift E₀ β T κ := by
  have h1 := driftSharpOf_nonneg E₀ 16
  have h2 : 0 ≤ β * Real.log κ := mul_nonneg hβ0 (Real.log_nonneg hκ)
  have h3 : 0 ≤ β / κ := div_nonneg hβ0 (by linarith)
  have h4 : 0 ≤ β * Real.log 2 := mul_nonneg hβ0 (Real.log_nonneg (by norm_num))
  have h5 := result1SharpShift_nonneg (vmax := 9 / 2) (β := β) (M := 25) hβ0
    (one_le_averagedK_mul hE₀ hT) (by norm_num)
  unfold averagedShift
  linarith

lemma one_le_averagedConst {E₀ β T κ : ℝ} (hE₀ : 0 ≤ E₀) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2)
    (hT : 4 < T) (hκ : 1 ≤ κ) : 1 ≤ averagedConst E₀ β T κ := by
  have hK := one_le_averagedK hE₀
  have hT0 : 0 < T := by linarith
  have hden : 0 < 1 - 2 * β / T := by
    rw [sub_pos, div_lt_one hT0]
    linarith
  have hden1 : 1 - 2 * β / T ≤ 1 := by
    have : 0 ≤ 2 * β / T := div_nonneg (by linarith) hT0.le
    linarith
  have he : 0 ≤ Real.exp (-100) := (Real.exp_pos _).le
  have hκ2 : 1 ≤ 1 + β / (4 * κ) := by
    have : 0 ≤ β / (4 * κ) := div_nonneg hβ0 (by linarith)
    linarith
  have h1 : 1 ≤ (1 + Real.exp (-100)) * averagedK E₀ := by nlinarith
  have h2 : 1 ≤ (1 + Real.exp (-100)) * averagedK E₀ * (1 + β / (4 * κ)) := by nlinarith
  unfold averagedConst
  rw [le_div_iff₀ hden]
  linarith

/-- **The level of the averaged free start is affine in `a`**: at `β ∈ [0, 2]` and a free start
`1 ≤ r ≤ a/4 + 1`, `a ≥ 1`,
`a + 2 + 3C + β(log r + log 2) + (9/2)r/(4a) + σ ≤ (1 + β/(4κ))(a + s)` with
`s = 3C + β log κ + β/κ + β log 2 + (2 - β) + 45/32 + σ`: `log r ≤ log κ + r/κ - 1` by concavity,
and `(9/2)r/(4a) ≤ 9/32 + 9/(8a) ≤ 45/32`. -/
lemma averaged_level_le {a κ C σ₀ β : ℝ} {r : ℕ} (ha : 1 ≤ a) (hκ : 1 ≤ κ) (hr1 : 1 ≤ r)
    (hr : (r : ℝ) ≤ a / 4 + 1) (hC : 0 ≤ C) (hσ₀ : 0 ≤ σ₀) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) :
    a + 2 + 3 * C + β * (Real.log r + Real.log 2) + 9 / 2 * r / (4 * a) + σ₀
      ≤ (1 + β / (4 * κ))
        * (a + (3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 45 / 32 + σ₀)) := by
  have hκ0 : 0 < κ := by linarith
  have ha0 : 0 < a := by linarith
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  -- `log r ≤ log κ + r/κ - 1`
  have hlogr : Real.log r ≤ Real.log κ + r / κ - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hr0 hκ0)
    rw [Real.log_div hr0.ne' hκ0.ne'] at h
    linarith
  have hrκ : (r : ℝ) / κ ≤ (a / 4 + 1) / κ := div_le_div_of_nonneg_right hr hκ0.le
  have hβlogr : β * Real.log r ≤ β * Real.log κ + β * a / (4 * κ) + β / κ - β := by
    have h1 : β * Real.log r ≤ β * (Real.log κ + (a / 4 + 1) / κ - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hβ0
    have e : β * (Real.log κ + (a / 4 + 1) / κ - 1)
        = β * Real.log κ + β * a / (4 * κ) + β / κ - β := by ring
    linarith
  -- `(9/2)r/(4a) ≤ 45/32`
  have hfrac : 9 / 2 * r / (4 * a) ≤ 45 / 32 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hS : 0 ≤ 3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 45 / 32 + σ₀ := by
    have h2 : 0 ≤ β * Real.log κ := mul_nonneg hβ0 (Real.log_nonneg hκ)
    have h3 : 0 ≤ β / κ := div_nonneg hβ0 hκ0.le
    have h4 : 0 ≤ β * Real.log 2 := mul_nonneg hβ0 (Real.log_nonneg (by norm_num))
    linarith
  have hSw : 0 ≤ β * (3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 45 / 32 + σ₀)
      / (4 * κ) := div_nonneg (mul_nonneg hβ0 hS) (by linarith)
  have e2 : (1 + β / (4 * κ))
      * (a + (3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 45 / 32 + σ₀))
      = a + (3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 45 / 32 + σ₀)
        + β * a / (4 * κ)
        + β * (3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 45 / 32 + σ₀)
          / (4 * κ) := by ring
  rw [e2]
  linarith

/-- **The averaged free start in the form `C_i min{1, (a + s)/√m}`.** -/
lemma le_averagedConst_mul_min {P a κ T K e σ₀ C m β : ℝ} {r : ℕ} (hP1 : P ≤ 1)
    (hP : P ≤ (1 + e) * (K * ((a + 2 + 3 * C + β * (Real.log r + Real.log 2)
      + 9 / 2 * r / (4 * a) + σ₀) / (1 - 2 * β / T)) / √m))
    (ha : 1 ≤ a) (hκ : 1 ≤ κ) (hr1 : 1 ≤ r) (hr : (r : ℝ) ≤ a / 4 + 1) (hC : 0 ≤ C)
    (hσ₀ : 0 ≤ σ₀) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) (hT : 4 < T)
    (hCi : 1 ≤ (1 + e) * K * (1 + β / (4 * κ)) / (1 - 2 * β / T)) :
    P ≤ ((1 + e) * K * (1 + β / (4 * κ)) / (1 - 2 * β / T))
      * min 1 ((a + (3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 45 / 32 + σ₀))
        / √m) := by
  have hT0 : 0 < T := by linarith
  have hden : 0 < 1 - 2 * β / T := by
    rw [sub_pos, div_lt_one hT0]
    linarith
  have hK : 0 ≤ (1 + e) * K := by
    have h := hCi
    rw [le_div_iff₀ hden] at h
    have hκ2 : 0 < 1 + β / (4 * κ) := by
      have : 0 ≤ β / (4 * κ) := div_nonneg hβ0 (by linarith)
      linarith
    by_contra hneg
    have : (1 + e) * K * (1 + β / (4 * κ)) < 0 := mul_neg_of_neg_of_pos (not_le.1 hneg) hκ2
    linarith
  have hlev := averaged_level_le ha hκ hr1 hr hC hσ₀ hβ0 hβ2
  set N := a + 2 + 3 * C + β * (Real.log r + Real.log 2) + 9 / 2 * r / (4 * a) + σ₀ with hN
  set S := 3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 45 / 32 + σ₀ with hS
  have hc0 : 0 ≤ (1 + e) * K / (1 - 2 * β / T) / √m := by
    have := Real.sqrt_nonneg m
    exact div_nonneg (div_nonneg hK hden.le) this
  have hB' : (1 + e) * (K * (N / (1 - 2 * β / T)) / √m)
      = ((1 + e) * K / (1 - 2 * β / T) / √m) * N := by ring
  have hRHS : ((1 + e) * K * (1 + β / (4 * κ)) / (1 - 2 * β / T)) * ((a + S) / √m)
      = ((1 + e) * K / (1 - 2 * β / T) / √m) * ((1 + β / (4 * κ)) * (a + S)) := by ring
  have hPle : P ≤ ((1 + e) * K * (1 + β / (4 * κ)) / (1 - 2 * β / T)) * ((a + S) / √m) := by
    rw [hRHS]
    rw [hB'] at hP
    exact le_trans hP (mul_le_mul_of_nonneg_left hlev hc0)
  exact le_trans (le_min hP1 hPle) (min_one_le_mul_min_one hCi le_rfl)

/-! ### The restricted chaos on the good sets, and the chaos moments -/

/-- **The level-shift chaos moments at the bad sets' level, past a block count**: given the chaos's
first moment `C₁` (`H₁`) and the restricted chaos hypothesis `Hi`, asked only for levels
`a ≥ harperBadLevel E₀` and only where `⌈a/4⌉ < n`, the chaos's `q`-th moment is at most
`shiftMomentConst C₁ C_i C_b A s λ₀ δ q·(1 + (1-q)√t)^{-q}`, `C_b = harperGoodBadConstOf E₀ β`, for
`A ≥ harperBadLevel E₀` and `x ≥ max{x₁, harperThreshold D N}`.  The block count `N` needs room
for the levels, `A_max/4 + 3√N/4 + 1 ≤ δN` and `3 ≤ 8δ√N` (`RMF.free_start_room_of_le`); the bad
sets at log-slope `β ∈ (1/2, 2]` are `RMF.measureReal_not_harperGoodSlopeOf_le_of_harperThreshold`.
-/
theorem integral_chaosUnitShift_rpow_le_shift_of_bad (E₀ β : ℝ) (hβ : 1 / 2 < β) (hβ2 : β ≤ 2)
    {Amax δ C₁ Ci s x₁ : ℝ} {N : ℕ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hC₁ : 0 < C₁) (hCi : 0 < Ci)
    (hs : 0 ≤ s) (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δ * N)
    (hmono : 3 ≤ 8 * δ * Real.sqrt (N : ℝ))
    (H₁ : ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν → ∀ x σ : ℝ,
      x₁ ≤ x → 0 ≤ σ →
        (∫ ω, chaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ ω ∂ν) ≤ C₁)
    (Hi : ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
      ∀ x σ η a : ℝ, x₁ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η →
        harperBadLevel E₀ ≤ a → ⌈a / 4⌉₊ < harperBlockCount (freeStartHarperD E₀) x →
          (∫ ω, restrictedChaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ
              (harperGoodSlopeOf β Y prop5UpperSlope (freeStartHarperD E₀) x σ a) ω ∂ν)
            ≤ Ci * min 1 ((a + s) / Real.sqrt ((harperBlockCount (freeStartHarperD E₀) x : ℝ)
                - ⌈a / 4⌉₊))) :
    ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
      ∀ x σ η q A lam : ℝ, max x₁ (harperThreshold (freeStartHarperD E₀) N) ≤ x → 0 ≤ σ →
        0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 1 → harperBadLevel E₀ ≤ A →
        A ≤ Amax → 1 ≤ lam →
        (∫ ω, chaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ ω ^ q ∂ν)
          ≤ shiftMomentConst C₁ Ci (harperGoodBadConstOf E₀ β) A s lam δ q
            * (1 + (1 - q) * Real.sqrt (harperBlockCount (freeStartHarperD E₀) x : ℝ)) ^ (-q) := by
  have hCb := harperGoodBadConstOf_pos E₀ hβ
  have H₂ := measureReal_not_harperGoodSlopeOf_le_of_harperThreshold (Ω := Ω) E₀ β hβ hβ2
  intro Y ν hY x σ η q A lam hx hσ0 hη0 hηE hσ hq0 hq1 hA hAmax hlam
  have hx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  set D := freeStartHarperD E₀ with hD_expl
  have hxN : harperThreshold D N ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : harperThreshold D 0 ≤ x := le_trans (harperThreshold_mono D (Nat.zero_le N)) hxN
  have hx2 : (2 : ℝ) ≤ x := le_trans (two_le_harperThreshold D N) hxN
  obtain ⟨hxgt1, -, hcount⟩ := exists_harperThreshold_of_blockCount_explicit D N x hxN
  have hA1 : (1 : ℝ) ≤ A := by
    have h : (1 : ℝ) ≤ harperBadLevel E₀ := le_max_left _ _
    linarith
  have hroom : A / 4 + 3 * Real.sqrt (harperBlockCount D x : ℝ) / 4 + 1 + ((0 : ℕ) : ℝ)
      ≤ δ * (harperBlockCount D x : ℝ) := by
    rw [Nat.cast_zero, add_zero]
    exact free_start_room_of_le hδ0.le hAmax (Nat.cast_nonneg _) hN hmono
      (by exact_mod_cast hcount)
  exact integral_rpow_le_of_goodFamilySplit hY hx2 hxgt1 hσ0 hq0 hq1 hC₁ hCi hCb hA
    (by linarith) hs hlam hδ (H₁ Y ν hY x σ hx₁ hσ0) hroom
    { set := fun a => harperGoodSlopeOf β Y prop5UpperSlope D x σ a
      measurableSet := fun a h => measurableSet_harperGoodSlopeOf hY β _ D x σ a h
      measurableSet_uncurry := fun a =>
        measurableSet_harperGoodSlopeOf_uncurry hY β _ D x σ a
      measure_bad_le := fun a ha =>
        H₂ Y ν hY x σ η a hx0 hσ0 hη0 hηE hσ ha
      integral_restricted_le := fun a ha h2 _ => by
        have h1 : (1 : ℝ) ≤ harperBadLevel E₀ := le_max_left _ _
        have hr1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
        exact Hi Y ν hY x σ η a hx₁ hσ0 hη0 hηE hσ ha (by omega) }

/-- **The restricted chaos on the good sets at the averaged free start, at log-slope `β`**: the
hypothesis `Hi` of `RMF.integral_chaosUnitShift_rpow_le_shift_of_bad` at
`C_i = averagedConst E₀ β T κ·e^{γ + 9.0028/L₀}` and `s = averagedShift E₀ β T κ`.  The free start
is `r = ⌈a/4⌉` and `hf = β log`; it needs `log log x ≥ D`, `log x ≥ L₀` and `r < n`, and no block
count of Proposition 5. -/
theorem integral_restrictedChaosUnitShift_harperGoodSlope_le_averaged (E₀ β : ℝ) (hE₀ : 0 ≤ E₀)
    (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) {L₀ T κ : ℝ} (hL₀ : 1 ≤ L₀) (hT : 4 < T) (hκ : 1 ≤ κ) :
    ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
      ∀ x σ η a : ℝ, max (harperThreshold (freeStartHarperD E₀) 0) (Real.exp L₀ + 1) ≤ x →
        0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η →
        harperBadLevel E₀ ≤ a → ⌈a / 4⌉₊ < harperBlockCount (freeStartHarperD E₀) x →
          (∫ ω, restrictedChaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ
              (harperGoodSlopeOf β Y prop5UpperSlope (freeStartHarperD E₀) x σ a) ω ∂ν)
            ≤ (averagedConst E₀ β T κ * normSqLogSharpConst L₀)
              * min 1 ((a + averagedShift E₀ β T κ)
                / Real.sqrt ((harperBlockCount (freeStartHarperD E₀) x : ℝ) - ⌈a / 4⌉₊)) := by
  intro Y ν hY x σ η a hx hσ0 hη0 hηE hσ ha hrn'
  set D := freeStartHarperD E₀ with hDdef
  set n := harperBlockCount D x with hndef
  set r := ⌈a / 4⌉₊ with hrdef
  set K := averagedK E₀ with hKdef
  have hK1 : 1 ≤ K := one_le_averagedK hE₀
  have hKT : 1 ≤ K * T := one_le_averagedK_mul hE₀ hT
  have ha1 : (1 : ℝ) ≤ a := by
    have h : (1 : ℝ) ≤ harperBadLevel E₀ := le_max_left _ _
    linarith
  have ha0 : (0 : ℝ) < a := by linarith
  have hr1 : 1 ≤ r := Nat.ceil_pos.2 (by linarith)
  have hra : a ≤ 4 * (r : ℝ) := by
    have := Nat.le_ceil (a / 4)
    linarith
  have hra' : (r : ℝ) ≤ a / 4 + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hxL : Real.exp L₀ + 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxH : harperThreshold D 0 ≤ x := le_trans (le_max_left _ _) hx
  have hσ₀ : 0 ≤ result1SharpShift (9 / 2) β K T 25 :=
    result1SharpShift_nonneg hβ0 hKT (by norm_num)
  have hKσ : 1 ≤ K * result1SharpShift (9 / 2) β K T 25 := by
    have hsq : (2.6 : ℝ) ≤ √(Real.pi * (9 / 2) / 2) := by
      rw [Real.le_sqrt' (by norm_num)]
      linarith [Real.pi_gt_d2]
    have h1 : (5.2 : ℝ) ≤ result1SharpShift (9 / 2) β K T 25 := by
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hlog50 : 0 ≤ Real.log (2 * ((25 : ℕ) : ℝ)) := Real.log_nonneg (by norm_num)
      have hlogKT : 0 ≤ Real.log (K * T) := Real.log_nonneg hKT
      have h2 : (0 : ℝ) ≤ β * (1 + Real.log 2 + Real.log (2 * ((25 : ℕ) : ℝ))) :=
        mul_nonneg hβ0 (by positivity)
      have h3 : (0 : ℝ) ≤ 2 * β * Real.log (K * T) := mul_nonneg (by linarith) hlogKT
      have h4 : (5.2 : ℝ) ≤ 2 * √(Real.pi * (9 / 2) / 2) := by linarith
      calc (5.2 : ℝ) = 5.2 + 0 + 0 := by norm_num
        _ ≤ 2 * √(Real.pi * (9 / 2) / 2) + β * (1 + Real.log 2 + Real.log (2 * ((25 : ℕ) : ℝ)))
            + 2 * β * Real.log (K * T) := add_le_add (add_le_add h4 h2) h3
        _ = result1SharpShift (9 / 2) β K T 25 := rfl
    nlinarith
  have hCi := one_le_averagedConst hE₀ hβ0 hβ2 hT hκ
  -- the tilted barrier probability at every height
  have hB : ∀ t : ℝ, ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1)
      (shiftLine σ t) ν) {ω | ∀ j, r ≤ j → j ≤ n →
        walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
          localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
          ∈ Set.Icc (-a - prop5UpperSlope * (j : ℝ)) (a + (j : ℝ) + β * Real.log j)}).toReal
      ≤ averagedConst E₀ β T κ
        * min 1 ((a + averagedShift E₀ β T κ) / Real.sqrt ((n : ℝ) - r)) := by
    intro t
    have hs : 0 < (shiftLine σ t).re := by rw [re_shiftLine]; linarith
    haveI := hY.isProbabilityMeasure_tiltedMeasure (⌊x⌋₊ + 1) hs
    have h1 := freeStart_barrier_harper_le_averaged_steinhaus E₀ hE₀ hY (s := shiftLine σ t)
      (hf := fun j => β * Real.log j) (β := β) (K := K) (T := T) hxH (re_shiftLine σ t) hσ0 hη0
      hηE hσ ha0 hr1 hra hrn'
      (fun j _ _ => by
        have h0 := Real.log_natCast_nonneg j
        rw [abs_of_nonneg (mul_nonneg hβ0 h0)]
        nlinarith)
      hβ0 (fun j _ _ => le_rfl) (by linarith) (by linarith) hσ₀
      (result1Affine_sharp hβ0 (by linarith) (by linarith) hKT (by norm_num)
        (averagedK_sq_mul E₀) hKσ)
    rw [Nat.cast_sub hrn'.le] at h1
    exact le_averagedConst_mul_min measureReal_le_one h1 ha1 hκ hr1 hra'
      (driftSharpOf_nonneg _ _) hσ₀ hβ0 hβ2 hT hCi
  have hBnn : 0 ≤ averagedConst E₀ β T κ
      * min 1 ((a + averagedShift E₀ β T κ) / Real.sqrt ((n : ℝ) - r)) := by
    have h1 : (0 : ℝ) ≤ averagedConst E₀ β T κ := by linarith
    have h2 : 0 ≤ a + averagedShift E₀ β T κ := by
      linarith [averagedShift_nonneg hE₀ hβ0 hβ2 hT hκ]
    exact mul_nonneg h1 (le_min zero_le_one (div_nonneg h2 (Real.sqrt_nonneg _)))
  have h := integral_restrictedChaosUnitShift_le_of_tilted hY hL₀ hxL hσ0 hBnn hB
  calc (∫ ω, restrictedChaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ
          (harperGoodSlopeOf β Y prop5UpperSlope D x σ a) ω ∂ν)
      ≤ averagedConst E₀ β T κ * min 1 ((a + averagedShift E₀ β T κ) / Real.sqrt ((n : ℝ) - r))
          * normSqLogSharpConst L₀ := h
    _ = (averagedConst E₀ β T κ * normSqLogSharpConst L₀)
          * min 1 ((a + averagedShift E₀ β T κ) / Real.sqrt ((n : ℝ) - r)) := by ring

/-- **The level-shift chaos moments at the averaged free start, at log-slope `β ∈ (1/2, 2]`**:
`RMF.integral_chaosUnitShift_rpow_le_shift_of_bad` at `C₁ = e^{γ + 9.0028/L₀}`,
`C_i = averagedConst E₀ β T κ·e^{γ + 9.0028/L₀}`, `s = averagedShift E₀ β T κ` and
`C_b = harperGoodBadConstOf E₀ β`, past `max{harperThreshold D 0, e^{L₀} + 1, harperThreshold D N}`
for a block count `N` with room. -/
theorem integral_chaosUnitShift_rpow_le_averaged (E₀ β : ℝ) (hE₀ : 0 ≤ E₀) (hβ : 1 / 2 < β)
    (hβ2 : β ≤ 2) {Amax δ L₀ T κ : ℝ}
    {N : ℕ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hL₀ : 1 ≤ L₀) (hT : 4 < T) (hκ : 1 ≤ κ)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δ * N)
    (hmono : 3 ≤ 8 * δ * Real.sqrt (N : ℝ)) :
    ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
      ∀ x σ η q A lam : ℝ, max (max (harperThreshold (freeStartHarperD E₀) 0) (Real.exp L₀ + 1))
          (harperThreshold (freeStartHarperD E₀) N) ≤ x → 0 ≤ σ → 0 ≤ η →
        η ≤ E₀ → |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 1 → harperBadLevel E₀ ≤ A → A ≤ Amax →
        1 ≤ lam →
        (∫ ω, chaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ ω ^ q ∂ν)
          ≤ shiftMomentConst (normSqLogSharpConst L₀)
              (averagedConst E₀ β T κ * normSqLogSharpConst L₀) (harperGoodBadConstOf E₀ β) A
              (averagedShift E₀ β T κ) lam δ q
            * (1 + (1 - q) * Real.sqrt (harperBlockCount (freeStartHarperD E₀) x : ℝ)) ^ (-q) :=
  integral_chaosUnitShift_rpow_le_shift_of_bad E₀ β hβ hβ2 hδ0 hδ (normSqLogSharpConst_pos L₀)
    (mul_pos (lt_of_lt_of_le one_pos (one_le_averagedConst hE₀ (by linarith) hβ2 hT hκ))
      (normSqLogSharpConst_pos L₀))
    (averagedShift_nonneg hE₀ (by linarith) hβ2 hT hκ) hN hmono
    (fun _ _ hY _ _ hx hσ =>
      integral_chaosUnitShift_le_sharp hY hL₀ (le_trans (le_max_right _ _) hx) hσ)
    (integral_restrictedChaosUnitShift_harperGoodSlope_le_averaged E₀ β hE₀ (by linarith) hβ2 hL₀
      hT hκ)

end RMF
