/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ChaosMomentAveraged
import RMF.Probability.FreeStartAveragedRademacherExplicit

/-!
# The averaged free start for the Rademacher block walk, in the form the chaos consumes

The Rademacher twin of the constants of `RMF/Probability/ChaosMomentAveraged.lean`: the tilted
probability of the barrier at one height (`RMF.freeStart_barrier_le_averaged_rademacher_of_floor`)
is put in the shape `C_i min{1, (a + s)/√(n - ⌈a/4⌉)}` which the level-shift interpolation
(`RMF.integral_rpow_le_of_goodSets_shift`) asks of the restricted chaos:

* `RMF.radAveragedK`: Probability Result 1's constant at the Rademacher variance floor
  `0.49e^{-2E₀}` (the Steinhaus `RMF.averagedK` has `0.475`);
* `RMF.radAveragedConst`, `RMF.radAveragedShift`: `C_i` and `s`, with the Rademacher drift
  `driftRadSharpOf E₀ 16 (e^{-2E₀}/100)`, the walk variance `0.51r` (so `0.51r/(4a) ≤ 4/25`, against
  the Steinhaus `45/32`) and Result 1's shift at `v₊ = 1`;
* `RMF.measureReal_mesoGood_le_radAveraged_of_floor`: the tilted barrier probability at one height.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The constants -/

/-- **Probability Result 1's constant at the Rademacher variance floor** `0.49e^{-2E₀}`
(`RMF.exists_isGaussianWalk_rademacher_of_le_sharp`), at the Gaussian constant with the split
`M = 25` (`RMF.result1Affine_sharp`): `K = √(2·25/(24·0.49πe^{-2E₀}))`, about `1.16` at `E₀ = 0`. -/
noncomputable def radAveragedK (E₀ : ℝ) : ℝ :=
  √(2 * 25 / (24 * (Real.pi * (0.49 * Real.exp (-(2 * E₀))))))

lemma radAveragedK_sq_mul (E₀ : ℝ) :
    2 * ((25 : ℕ) : ℝ) ≤ radAveragedK E₀ ^ 2 * (((25 : ℕ) : ℝ) - 1)
      * (Real.pi * (0.49 * Real.exp (-(2 * E₀)))) := by
  have hv : 0 < Real.pi * (0.49 * Real.exp (-(2 * E₀))) := by positivity
  rw [radAveragedK, Real.sq_sqrt (by positivity)]
  push_cast
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

lemma one_le_radAveragedK {E₀ : ℝ} (hE₀ : 0 ≤ E₀) : 1 ≤ radAveragedK E₀ := by
  have hv : 0 < Real.pi * (0.49 * Real.exp (-(2 * E₀))) := by positivity
  have he : Real.exp (-(2 * E₀)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hpi := Real.pi_lt_d2
  have hle : 24 * (Real.pi * (0.49 * Real.exp (-(2 * E₀)))) ≤ 2 * 25 := by
    have h1 : Real.pi * (0.49 * Real.exp (-(2 * E₀))) ≤ Real.pi * 0.49 :=
      mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
    linarith
  rw [radAveragedK]
  exact Real.one_le_sqrt.2 ((one_le_div (by positivity)).2 hle)

lemma one_le_radAveragedK_mul {E₀ T : ℝ} (hE₀ : 0 ≤ E₀) (hT : 4 < T) :
    1 ≤ radAveragedK E₀ * T := by
  have hK := one_le_radAveragedK hE₀
  nlinarith

/-- **The constant of the Rademacher averaged free start at log-slope `β`**:
`(1 + e^{-100})K(1 + β/(4κ))/(1 - 2β/T)` with `K = radAveragedK E₀`. -/
noncomputable def radAveragedConst (E₀ β T κ : ℝ) : ℝ :=
  (1 + Real.exp (-100)) * radAveragedK E₀ * (1 + β / (4 * κ)) / (1 - 2 * β / T)

/-- **The level shift of the Rademacher averaged free start at log-slope `β`**:
`3C + β log κ + β/κ + β log 2 + (2 - β) + 4/25 + result1SharpShift 1 β K T 25`, with the drift
`C = driftRadSharpOf E₀ 16 (e^{-2E₀}/100)` and `K = radAveragedK E₀`. -/
noncomputable def radAveragedShift (E₀ β T κ : ℝ) : ℝ :=
  3 * driftRadSharpOf E₀ 16 (Real.exp (-(2 * E₀)) / 100) + β * Real.log κ + β / κ
    + β * Real.log 2 + (2 - β) + 4 / 25 + result1SharpShift 1 β (radAveragedK E₀) T 25

lemma radAveragedShift_nonneg {E₀ β T κ : ℝ} (hE₀ : 0 ≤ E₀) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2)
    (hT : 4 < T) (hκ : 1 ≤ κ) : 0 ≤ radAveragedShift E₀ β T κ := by
  have h1 := driftRadSharpOf_nonneg (K := E₀) (θ := 16)
    (by positivity : (0 : ℝ) ≤ Real.exp (-(2 * E₀)) / 100)
  have h2 : 0 ≤ β * Real.log κ := mul_nonneg hβ0 (Real.log_nonneg hκ)
  have h3 : 0 ≤ β / κ := div_nonneg hβ0 (by linarith)
  have h4 : 0 ≤ β * Real.log 2 := mul_nonneg hβ0 (Real.log_nonneg (by norm_num))
  have h5 := result1SharpShift_nonneg (vmax := 1) (β := β) (M := 25) hβ0
    (one_le_radAveragedK_mul hE₀ hT) (by norm_num)
  unfold radAveragedShift
  linarith

lemma one_le_radAveragedConst {E₀ β T κ : ℝ} (hE₀ : 0 ≤ E₀) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2)
    (hT : 4 < T) (hκ : 1 ≤ κ) : 1 ≤ radAveragedConst E₀ β T κ := by
  have hK := one_le_radAveragedK hE₀
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
  have h1 : 1 ≤ (1 + Real.exp (-100)) * radAveragedK E₀ := by nlinarith
  have h2 : 1 ≤ (1 + Real.exp (-100)) * radAveragedK E₀ * (1 + β / (4 * κ)) := by nlinarith
  unfold radAveragedConst
  rw [le_div_iff₀ hden]
  linarith

/-- **The level of the Rademacher averaged free start is affine in `a`**: at `β ∈ [0, 2]` and a
free start `1 ≤ r ≤ a/4 + 1`, `a ≥ 1`,
`a + 2 + 3C + β(log r + log 2) + 0.51r/(4a) + σ ≤ (1 + β/(4κ))(a + s)` with
`s = 3C + β log κ + β/κ + β log 2 + (2 - β) + 4/25 + σ`: `log r ≤ log κ + r/κ - 1` by concavity,
and `0.51r/(4a) ≤ 0.51/16 + 0.51/(4a) ≤ 4/25`.  The proof of `RMF.averaged_level_le`. -/
lemma rad_averaged_level_le {a κ C σ₀ β : ℝ} {r : ℕ} (ha : 1 ≤ a) (hκ : 1 ≤ κ) (hr1 : 1 ≤ r)
    (hr : (r : ℝ) ≤ a / 4 + 1) (hC : 0 ≤ C) (hσ₀ : 0 ≤ σ₀) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) :
    a + 2 + 3 * C + β * (Real.log r + Real.log 2) + 0.51 * r / (4 * a) + σ₀
      ≤ (1 + β / (4 * κ))
        * (a + (3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 4 / 25 + σ₀)) := by
  have hκ0 : 0 < κ := by linarith
  have ha0 : 0 < a := by linarith
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
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
  have hfrac : 0.51 * r / (4 * a) ≤ 4 / 25 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hS : 0 ≤ 3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 4 / 25 + σ₀ := by
    have h2 : 0 ≤ β * Real.log κ := mul_nonneg hβ0 (Real.log_nonneg hκ)
    have h3 : 0 ≤ β / κ := div_nonneg hβ0 hκ0.le
    have h4 : 0 ≤ β * Real.log 2 := mul_nonneg hβ0 (Real.log_nonneg (by norm_num))
    linarith
  have hSw : 0 ≤ β * (3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 4 / 25 + σ₀)
      / (4 * κ) := div_nonneg (mul_nonneg hβ0 hS) (by linarith)
  have e2 : (1 + β / (4 * κ))
      * (a + (3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 4 / 25 + σ₀))
      = a + (3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 4 / 25 + σ₀)
        + β * a / (4 * κ)
        + β * (3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 4 / 25 + σ₀)
          / (4 * κ) := by ring
  rw [e2]
  linarith

/-- **The Rademacher averaged free start in the form `C_i min{1, (a + s)/√m}`.**  The proof of
`RMF.le_averagedConst_mul_min`, at `RMF.rad_averaged_level_le`. -/
lemma le_radAveragedConst_mul_min {P a κ T K e σ₀ C m β : ℝ} {r : ℕ} (hP1 : P ≤ 1)
    (hP : P ≤ (1 + e) * (K * ((a + 2 + 3 * C + β * (Real.log r + Real.log 2)
      + 0.51 * r / (4 * a) + σ₀) / (1 - 2 * β / T)) / √m))
    (ha : 1 ≤ a) (hκ : 1 ≤ κ) (hr1 : 1 ≤ r) (hr : (r : ℝ) ≤ a / 4 + 1) (hC : 0 ≤ C)
    (hσ₀ : 0 ≤ σ₀) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) (hT : 4 < T)
    (hCi : 1 ≤ (1 + e) * K * (1 + β / (4 * κ)) / (1 - 2 * β / T)) :
    P ≤ ((1 + e) * K * (1 + β / (4 * κ)) / (1 - 2 * β / T))
      * min 1 ((a + (3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 4 / 25 + σ₀))
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
  have hlev := rad_averaged_level_le ha hκ hr1 hr hC hσ₀ hβ0 hβ2
  set N := a + 2 + 3 * C + β * (Real.log r + Real.log 2) + 0.51 * r / (4 * a) + σ₀ with hN
  set S := 3 * C + β * Real.log κ + β / κ + β * Real.log 2 + (2 - β) + 4 / 25 + σ₀ with hS
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

/-! ### The tilted barrier at one height -/

/-- `2 < Kσ`-type condition of `RMF.result1Affine_sharp` at `v₊ = 1`: `1 ≤ K·result1SharpShift`. -/
lemma one_le_radAveragedK_mul_shift {E₀ β T : ℝ} (hE₀ : 0 ≤ E₀) (hβ0 : 0 ≤ β) (hT : 4 < T) :
    1 ≤ radAveragedK E₀ * result1SharpShift 1 β (radAveragedK E₀) T 25 := by
  have hK1 := one_le_radAveragedK hE₀
  have hKT := one_le_radAveragedK_mul hE₀ hT
  have hsq : (1.2 : ℝ) ≤ √(Real.pi * 1 / 2) := by
    rw [Real.le_sqrt' (by norm_num)]
    linarith [Real.pi_gt_d2]
  have h1 : (2.4 : ℝ) ≤ result1SharpShift 1 β (radAveragedK E₀) T 25 := by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog50 : 0 ≤ Real.log (2 * ((25 : ℕ) : ℝ)) := Real.log_nonneg (by norm_num)
    have hlogKT : 0 ≤ Real.log (radAveragedK E₀ * T) := Real.log_nonneg hKT
    have h2 : (0 : ℝ) ≤ β * (1 + Real.log 2 + Real.log (2 * ((25 : ℕ) : ℝ))) :=
      mul_nonneg hβ0 (by positivity)
    have h3 : (0 : ℝ) ≤ 2 * β * Real.log (radAveragedK E₀ * T) := mul_nonneg (by linarith) hlogKT
    have h4 : (2.4 : ℝ) ≤ 2 * √(Real.pi * 1 / 2) := by linarith
    calc (2.4 : ℝ) = 2.4 + 0 + 0 := by norm_num
      _ ≤ 2 * √(Real.pi * 1 / 2) + β * (1 + Real.log 2 + Real.log (2 * ((25 : ℕ) : ℝ)))
          + 2 * β * Real.log (radAveragedK E₀ * T) := add_le_add (add_le_add h4 h2) h3
      _ = result1SharpShift 1 β (radAveragedK E₀) T 25 := rfl
  nlinarith

/-- **The tilted barrier probability of the block good set at one height, at the floor `ϑ`**:
at most `radAveragedConst · min{1, (a + radAveragedShift)/√(n - ⌈a/4⌉)}`, under the height
condition `(2|Im s| + 1)·pntFloorConst ϑ ≤ e^{-2E₀}/200`
(`RMF.freeStart_barrier_le_averaged_rademacher_of_floor`). -/
theorem measureReal_mesoGood_le_radAveraged_of_floor (E₀ β : ℝ) (hE₀ : 0 ≤ E₀) (hβ0 : 0 ≤ β)
    (hβ2 : β ≤ 2) {T κ : ℝ} (hT : 4 < T) (hκ : 1 ≤ κ) (hX : IsRademacherPrimeValues X μ)
    {ϑ σ η a : ℝ} {n : ℕ} {s : ℂ}
    (hϑ : radFreeStartThreshold E₀ ≤ ϑ) (hϑ104 : (104 : ℝ) ≤ ϑ) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hη0 : 0 ≤ η) (hηE : η ≤ E₀)
    (hσ : |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η)
    (hlo : 600 * Real.exp (2 * E₀) ≤ 2 * |s.im| * Real.exp ϑ)
    (hhiF : (2 * |s.im| + 1) * pntFloorConst ϑ ≤ Real.exp (-(2 * E₀)) / 200)
    (ha : 1 ≤ a) (hrn : ⌈a / 4⌉₊ < n) :
    ((tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (blockCutoff ϑ n) s μ)
        {ω | ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ n →
          walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
            localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) j ω
            ∈ Set.Icc (-a - prop5UpperSlope * (j : ℝ)) (a + (j : ℝ) + β * Real.log j)}).toReal
      ≤ radAveragedConst E₀ β T κ
        * min 1 ((a + radAveragedShift E₀ β T κ) / Real.sqrt ((n : ℝ) - ⌈a / 4⌉₊)) := by
  set r := ⌈a / 4⌉₊ with hrdef
  set K := radAveragedK E₀ with hKdef
  have hK1 : 1 ≤ K := one_le_radAveragedK hE₀
  have hKT : 1 ≤ K * T := one_le_radAveragedK_mul hE₀ hT
  have ha0 : (0 : ℝ) < a := by linarith
  have hr1 : 1 ≤ r := Nat.ceil_pos.2 (by linarith)
  have hra : a ≤ 4 * (r : ℝ) := by
    have := Nat.le_ceil (a / 4)
    linarith
  have hra' : (r : ℝ) ≤ a / 4 + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hσ₀ : 0 ≤ result1SharpShift 1 β K T 25 := result1SharpShift_nonneg hβ0 hKT (by norm_num)
  have hCi := one_le_radAveragedConst hE₀ hβ0 hβ2 hT hκ
  have hs : 0 < s.re := by rw [hres]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure_rademacher hX (blockCutoff ϑ n) hs
  have h1 := freeStart_barrier_le_averaged_rademacher_of_floor E₀ hE₀ hX (s := s)
    (hf := fun j => β * Real.log j) (β := β) (K := K) (T := T) hϑ hϑ104 hres hσ0 hη0 hηE hσ
    hlo hhiF ha0 hr1 hra hrn
    (fun j _ _ => by
      have h0 := Real.log_natCast_nonneg j
      rw [abs_of_nonneg (mul_nonneg hβ0 h0)]
      nlinarith)
    hβ0 (fun j _ _ => le_rfl) (by linarith) (by linarith) hσ₀
    (result1Affine_sharp hβ0 (by linarith) (by linarith) hKT (by norm_num)
      (radAveragedK_sq_mul E₀) (one_le_radAveragedK_mul_shift hE₀ hβ0 hT))
  rw [Nat.cast_sub hrn.le] at h1
  exact le_radAveragedConst_mul_min measureReal_le_one h1 ha hκ hr1 hra'
    (driftRadSharpOf_nonneg (by positivity)) hσ₀ hβ0 hβ2 hT hCi

end RMF
