/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.BlockComparison

/-!
# The block comparison's thresholds, named

Explicit twins of three statements of `RMF/Probability/BlockComparison.lean` whose block offset
is existential there; here it is a closed form:

* `RMF.blockNumThreshold E₀ G = log(200(10 + E₀ + G))`, for `RMF.exists_blockNum_le_of_scale`;
* `RMF.thrDirectThreshold A a B h τ = log(5A(a + B + e² + h)²/τ)`, for `RMF.exists_thr_direct`;
* `RMF.blockQThrThreshold E₀ a B`, for `RMF.exists_blockQThr_le_measure`: the maximum of the direct
  threshold at `A = 2e^{2E₀}`, `h = 1`, `τ = 3/100` with `9` and `log(14 + 2E₀)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

/-! ### The numerical thresholds -/

/-- The block offset of `RMF.exists_blockNum_le_of_scale`, `log(200(10 + E₀ + G))`. -/
noncomputable def blockNumThreshold (E₀ G : ℝ) : ℝ := Real.log (200 * (10 + E₀ + G))

/-- **`RMF.exists_blockNum_le_of_scale` at its threshold** `RMF.blockNumThreshold E₀ G`. -/
theorem exists_blockNum_le_of_scale_explicit (E₀ G : ℝ) (hE₀ : 0 ≤ E₀) (hG : 0 ≤ G) :
    ∀ (θ η V T Kb : ℝ) (m : ℕ), (blockNumThreshold E₀ G) ≤ θ → 0 ≤ η → η ≤ E₀ →
      Real.exp (-(2 * η)) / 4 ≤ V → 0 ≤ T → 0 ≤ Kb → Kb ≤ Real.exp (4 * G) →
      T ≤ Kb / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m)) →
        (450 + 4 / Real.sqrt (2 * Real.pi * V)) * T ^ (1 / 4 : ℝ)
          ≤ blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
            * (1 / ((m : ℝ) + 1) ^ 2 * blockScale θ (m + 1) ^ (-(3 : ℝ) / 100)) := by
  have he1u : Real.exp 1 ≤ 2.7183 := by linarith [Real.exp_one_lt_d9]
  have hpos : (0 : ℝ) < 200 * (10 + E₀ + G) := by linarith
  rw [show blockNumThreshold E₀ G =
      Real.log (200 * (10 + E₀ + G)) from rfl]
  intro θ η V T Kb m hθ hη0 hηE hV hT0 hKb0 hKb hT
  have hexpθ : 200 * (10 + E₀ + G) ≤ Real.exp θ := by
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 hθ
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hθ0 : (0 : ℝ) ≤ θ := by
    by_contra hcon
    push Not at hcon
    have h1 : Real.exp θ < Real.exp 0 := Real.exp_lt_exp.2 hcon
    rw [Real.exp_zero] at h1
    linarith
  set Eb := Real.exp ((m : ℝ) + θ) with hEdef
  have hE0 : (0 : ℝ) < Eb := Real.exp_pos _
  -- `E_m ≥ e^θ(1+m)`
  have hEsplit : Eb = Real.exp (m : ℝ) * Real.exp θ := by rw [hEdef, ← Real.exp_add]
  have hm1 : (1 : ℝ) + (m : ℝ) ≤ Real.exp (m : ℝ) := by
    linarith [Real.add_one_le_exp ((m : ℝ))]
  have hEge : (1 + (m : ℝ)) * Real.exp θ ≤ Eb := by
    rw [hEsplit]
    exact mul_le_mul_of_nonneg_right hm1 (Real.exp_pos _).le
  have hE1 : (1 : ℝ) ≤ Eb := Real.one_le_exp (by linarith)
  -- the two scales, as exponentials
  have hXm : blockScale θ m = Real.exp Eb := by rw [blockScale]
  have hLm : Real.log (blockScale θ m) = Eb := log_blockScale θ m
  have hXm1 : blockScale θ (m + 1) = Real.exp (Real.exp 1 * Eb) := by
    have h : Real.exp 1 * Eb = Real.exp (((m + 1 : ℕ) : ℝ) + θ) := by
      rw [hEdef, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [h, blockScale]
  have hsq : Real.sqrt (blockScale θ m) = Real.exp (Eb / 2) := by
    rw [hXm, ← Real.exp_half]
  clear_value Eb
  -- `T ≤ Kb e^{-E/2}`
  have hT2 : T ≤ Kb * Real.exp (-(Eb / 2)) := by
    refine le_trans hT ?_
    rw [hsq, hLm, Real.exp_neg, ← div_eq_mul_inv,
      div_le_div_iff₀ (by positivity) (Real.exp_pos (Eb / 2))]
    nlinarith [mul_nonneg (mul_nonneg hKb0 (Real.exp_pos (Eb / 2)).le)
      (sub_nonneg.2 hE1)]
  -- `T^{1/4} ≤ e^G e^{-E/8}`
  have hquarter : T ^ (1 / 4 : ℝ) ≤ Real.exp G * Real.exp (-(Eb / 8)) := by
    have h1 : T ^ (1 / 4 : ℝ) ≤ (Kb * Real.exp (-(Eb / 2))) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hT0 hT2 (by norm_num)
    have h2 : (Kb * Real.exp (-(Eb / 2))) ^ (1 / 4 : ℝ)
        = Kb ^ (1 / 4 : ℝ) * Real.exp (-(Eb / 8)) := by
      rw [Real.mul_rpow hKb0 (Real.exp_pos _).le]
      congr 1
      rw [← Real.exp_mul]
      congr 1
      ring
    have h3 : Kb ^ (1 / 4 : ℝ) ≤ Real.exp G := by
      have h := Real.rpow_le_rpow hKb0 hKb (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rwa [show Real.exp (4 * G) ^ (1 / 4 : ℝ) = Real.exp G by
        rw [← Real.exp_mul]; congr 1; ring] at h
    calc T ^ (1 / 4 : ℝ) ≤ Kb ^ (1 / 4 : ℝ) * Real.exp (-(Eb / 8)) := by rw [← h2]; exact h1
      _ ≤ Real.exp G * Real.exp (-(Eb / 8)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  -- the coefficient, from `V ≥ e^{-2η}/4`
  have hη1 : (1 : ℝ) ≤ Real.exp η := Real.one_le_exp hη0
  have hen : Real.exp (-η) * Real.exp η = 1 := by
    rw [← Real.exp_add, show -η + η = 0 by ring, Real.exp_zero]
  have hcoef : 450 + 4 / Real.sqrt (2 * Real.pi * V) ≤ 454 * Real.exp η := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hrw : Real.exp (-(2 * η)) = Real.exp (-η) * Real.exp (-η) := by
      rw [← Real.exp_add]; ring_nf
    have hen0 : (0 : ℝ) < Real.exp (-η) := Real.exp_pos _
    have hsq2 : ((6 / 5 : ℝ) * Real.exp (-η)) ^ 2 = 36 / 25 * Real.exp (-(2 * η)) := by
      rw [mul_pow, pow_two (Real.exp (-η)), ← hrw]
      norm_num
    have h2pv : ((6 / 5 : ℝ) * Real.exp (-η)) ^ 2 ≤ 2 * Real.pi * V := by
      rw [hsq2]
      nlinarith [hV, hpi, Real.exp_pos (-(2 * η))]
    have hs : (6 / 5 : ℝ) * Real.exp (-η) ≤ Real.sqrt (2 * Real.pi * V) := by
      have h := Real.sqrt_le_sqrt h2pv
      rwa [Real.sqrt_sq (by positivity)] at h
    have hs0 : (0 : ℝ) < Real.sqrt (2 * Real.pi * V) := by linarith [hs, hen0]
    have h4 : 4 / Real.sqrt (2 * Real.pi * V) ≤ 4 * Real.exp η := by
      rw [div_le_iff₀ hs0]
      nlinarith [hs, hen, Real.exp_pos η]
    linarith
  -- the right-hand side, as a single exponential
  have hprod : blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * blockScale θ (m + 1) ^ (-(3 : ℝ) / 100)
      = Real.exp (-(Real.exp 1 * Eb / 25)) := by
    rw [← Real.rpow_add (blockScale_pos θ (m + 1)), hXm1, ← Real.exp_mul]
    congr 1
    ring
  rw [show blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * (1 / ((m : ℝ) + 1) ^ 2 * blockScale θ (m + 1) ^ (-(3 : ℝ) / 100))
      = blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * blockScale θ (m + 1) ^ (-(3 : ℝ) / 100) * (1 / ((m : ℝ) + 1) ^ 2) from by ring,
    hprod]
  -- the margin: `454 e^{η+G} (m+1)² ≤ e^{cE}` with `c = 1/8 - e/25 ≥ 0.0162`
  have hc : (0.0162 : ℝ) ≤ 1 / 8 - Real.exp 1 / 25 := by linarith
  have hcE : (0.0162 : ℝ) * Eb ≤ Eb / 8 - Real.exp 1 * Eb / 25 := by
    have h := mul_le_mul_of_nonneg_right hc hE0.le
    linarith
  have hhalf : (454 : ℝ) * Real.exp η * Real.exp G ≤ Real.exp (0.0081 * Eb) := by
    have hlog : Real.log 454 ≤ 7 := by
      have h7 : (1090 : ℝ) ≤ Real.exp 7 := by
        have he : (2.7182 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        simpa using le_exp_natCast_of_le_pow (c := 2.7182) (k := 7)
          (by norm_num) he.le (by norm_num)
      have hle : (454 : ℝ) ≤ Real.exp 7 := by linarith
      exact (Real.log_le_iff_le_exp (by norm_num)).2 hle
    have hrw : (454 : ℝ) * Real.exp η * Real.exp G
        = Real.exp (Real.log 454 + η + G) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 454)]
    rw [hrw]
    refine Real.exp_le_exp.2 ?_
    have hE : 200 * (10 + E₀ + G) ≤ Eb := by
      have hmul : (0 : ℝ) ≤ (m : ℝ) * Real.exp θ := mul_nonneg hm0 (Real.exp_pos θ).le
      linarith [hEge, hexpθ, hmul]
    linarith
  have hsqm : ((m : ℝ) + 1) ^ 2 ≤ Real.exp (0.0081 * Eb) := by
    have h1 : ((m : ℝ) + 1) ^ 2 ≤ Real.exp (2 * (m : ℝ)) := by
      have h2 : ((m : ℝ) + 1) ^ 2 ≤ Real.exp (m : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      rwa [show Real.exp (m : ℝ) ^ 2 = Real.exp (2 * (m : ℝ)) by
        rw [pow_two, ← Real.exp_add]; congr 1; ring] at h2
    refine le_trans h1 (Real.exp_le_exp.2 ?_)
    have h3 : (2000 : ℝ) ≤ Real.exp θ := by linarith
    have hbig : (2000 : ℝ) * (1 + (m : ℝ)) ≤ Eb := by
      have hmul : (1 + (m : ℝ)) * 2000 ≤ (1 + (m : ℝ)) * Real.exp θ :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
      linarith [hEge, hmul]
    linarith
  have hmargin : (454 : ℝ) * Real.exp η * Real.exp G * ((m : ℝ) + 1) ^ 2
      ≤ Real.exp (Eb / 8 - Real.exp 1 * Eb / 25) := by
    have hmul : Real.exp (0.0081 * Eb) * Real.exp (0.0081 * Eb)
        = Real.exp (0.0162 * Eb) := by rw [← Real.exp_add]; ring_nf
    calc (454 : ℝ) * Real.exp η * Real.exp G * ((m : ℝ) + 1) ^ 2
        ≤ Real.exp (0.0081 * Eb) * Real.exp (0.0081 * Eb) :=
          mul_le_mul hhalf hsqm (by positivity) (Real.exp_pos _).le
      _ = Real.exp (0.0162 * Eb) := hmul
      _ ≤ Real.exp (Eb / 8 - Real.exp 1 * Eb / 25) := Real.exp_le_exp.2 hcE
  have hkey : 454 * Real.exp η * Real.exp G * ((m : ℝ) + 1) ^ 2 * Real.exp (-(Eb / 8))
      ≤ Real.exp (-(Real.exp 1 * Eb / 25)) := by
    have hmul : Real.exp (Eb / 8 - Real.exp 1 * Eb / 25) * Real.exp (-(Eb / 8))
        = Real.exp (-(Real.exp 1 * Eb / 25)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc 454 * Real.exp η * Real.exp G * ((m : ℝ) + 1) ^ 2 * Real.exp (-(Eb / 8))
        ≤ Real.exp (Eb / 8 - Real.exp 1 * Eb / 25) * Real.exp (-(Eb / 8)) :=
          mul_le_mul_of_nonneg_right hmargin (Real.exp_pos _).le
      _ = Real.exp (-(Real.exp 1 * Eb / 25)) := hmul
  have hL : (450 + 4 / Real.sqrt (2 * Real.pi * V)) * T ^ (1 / 4 : ℝ)
      ≤ 454 * Real.exp η * (Real.exp G * Real.exp (-(Eb / 8))) := by
    have hT4 : (0 : ℝ) ≤ T ^ (1 / 4 : ℝ) := Real.rpow_nonneg hT0 _
    calc (450 + 4 / Real.sqrt (2 * Real.pi * V)) * T ^ (1 / 4 : ℝ)
        ≤ 454 * Real.exp η * T ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_right hcoef hT4
      _ ≤ 454 * Real.exp η * (Real.exp G * Real.exp (-(Eb / 8))) :=
          mul_le_mul_of_nonneg_left hquarter (by positivity)
  refine le_trans hL ?_
  rw [mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < ((m : ℝ) + 1) ^ 2)]
  linarith [hkey]

/-- The block offset of `RMF.exists_thr_direct`, `log(5A(a + B + e² + h)²/τ)`. -/
noncomputable def thrDirectThreshold (A a Bs h τ : ℝ) : ℝ :=
  Real.log (5 * A * (a + Bs + Real.exp 2 + h) ^ 2 / τ)

/-- **`RMF.exists_thr_direct` at its threshold** `RMF.thrDirectThreshold A a Bs h τ`. -/
theorem exists_thr_direct_explicit (A a Bs h τ : ℝ) (hA : 1 ≤ A) (ha : 0 ≤ a) (hB : 0 < Bs)
    (hh : 0 ≤ h)
    (hτ : 0 < τ) :
    ∀ (θ : ℝ) (j : ℕ), (thrDirectThreshold A a Bs h τ) ≤ θ →
      A * (a + Bs * j + Real.exp 2 + h) ^ 2 + Real.log (Real.pi * 9) / 2
        ≤ τ * Real.log (blockScale θ (j + 1)) := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hSpos : (0 : ℝ) < a + Bs + Real.exp 2 + h := by
    have := Real.exp_pos (2 : ℝ)
    linarith
  have hq : (0 : ℝ) < 5 * A * (a + Bs + Real.exp 2 + h) ^ 2 / τ := by positivity
  rw [show thrDirectThreshold A a Bs h τ =
      Real.log (5 * A * (a + Bs + Real.exp 2 + h) ^ 2 / τ) from rfl]
  refine fun θ j hθ => ?_
  refine thr_direct_of_offset hA ha hB hh ?_
  have hexp : 5 * A * (a + Bs + Real.exp 2 + h) ^ 2 / τ ≤ Real.exp θ := by
    rw [← Real.exp_log hq]
    exact Real.exp_le_exp.2 hθ
  rw [div_le_iff₀ hτ] at hexp
  rw [mul_comm τ (Real.exp θ)]
  exact hexp

/-! ### The window-mass threshold -/

/-- The block offset of `RMF.exists_blockQThr_le_measure`. -/
noncomputable def blockQThrThreshold (E₀ a Bs : ℝ) : ℝ :=
  max (max (thrDirectThreshold (2 * Real.exp (2 * E₀)) a Bs 1 (3 / 100)) 9)
    (Real.log (14 + 2 * E₀))

/-- **`RMF.exists_blockQThr_le_measure` at its threshold** `RMF.blockQThrThreshold E₀ a Bs`. -/
theorem exists_blockQThr_le_measure_explicit (E₀ a Bs : ℝ)
    (hE₀ : 0 ≤ E₀) (ha : 0 ≤ a) (hBs : 0 < Bs) :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsSteinhausPrimeValues X μ →
      ∀ (θ σ η : ℝ) (m n : ℕ) (s : ℂ) (w : Nat.Primes → ℂ) (M : ℝ),
      (blockQThrThreshold E₀ a Bs) ≤ θ → m ≤ n → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ η →
      (∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) →
      0 ≤ M → M ≤ a + Bs * m →
      ∀ c, |c| ≤ M → blockQThr θ (3 / 100) m ≤ (gaussianReal
          (blockMean X μ (blockCutoff θ n) s w (primeBlockSub θ m))
          (blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m))
          (Set.Ioc c (c + blockWindow m))).toReal := by
  have hA1 : (1 : ℝ) ≤ 2 * Real.exp (2 * E₀) := by
    have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 2 * E₀)
    linarith
  have hθ₁ := exists_thr_direct_explicit (2 * Real.exp (2 * E₀)) a Bs 1 (3 / 100)
    hA1 ha hBs (by norm_num) (by norm_num)
  set θ₁ := thrDirectThreshold (2 * Real.exp (2 * E₀)) a Bs 1 (3 / 100) with hθ₁_expl
  rw [show blockQThrThreshold E₀ a Bs =
      max (max θ₁ 9) (Real.log (14 + 2 * E₀)) from rfl]
  intro Ω _ X μ hX θ σ η m n s w M hθ hmn hres hσ0 hη0 hηE hσ hwn hM0 hM
  have hAη : (1 : ℝ) ≤ 2 * Real.exp (2 * η) := by
    have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 2 * η)
    linarith
  have hθ₁' : θ₁ ≤ θ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hθ
  have hθ9 : (9 : ℝ) ≤ θ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hθ
  have hθlog : Real.log (14 + 2 * E₀) ≤ θ := le_trans (le_max_right _ _) hθ
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm5 : (5 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hm8 : (8 : ℝ) ≤ (m : ℝ) + θ := by linarith
  -- the one hypothesis that replaces every cap on the tilt scale
  have hsc : (14 : ℝ) + 2 * η ≤ Real.exp ((m : ℝ) + θ) := by
    have hpos : (0 : ℝ) < 14 + 2 * E₀ := by linarith
    have h1 : (14 : ℝ) + 2 * E₀ ≤ Real.exp θ := by
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.2 hθlog
    have hmt : Real.exp θ ≤ Real.exp ((m : ℝ) + θ) := Real.exp_le_exp.2 (by linarith)
    linarith
  have hsre : 0 < s.re := re_pos_of_block_of_le hres hsc hσ
  have hb0 : (0 : ℝ) < blockScale θ m := blockScale_pos θ m
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ (2 : ℕ) := by rw [← Real.exp_nat_mul]; ring_nf
    rw [h2]; nlinarith
  -- the drift, at the per-block cutoff
  have habs := abs_blockMean_le_of_le hX hm5 hmn hres hσ0 hsc hσ hwn
  rw [blockMean_blockCutoff_eq hX hsre hmn w, blockCutoff] at habs
  have hL : (7000 : ℝ) ≤ Real.log (blockScale θ (m + 1)) := by
    rw [log_blockScale]
    have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (7000 : ℝ) ≤ (2.7 : ℝ) ^ (9 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 9
      _ = Real.exp ((9 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (((m + 1 : ℕ) : ℝ) + θ) := Real.exp_le_exp.2 (by push_cast; linarith)
  have hmert : (60 : ℝ) / Real.log (blockScale θ (m + 1)) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  -- `2e^{2η}` is under the block scale, which is where `θ ≥ \log(1+2η)` is spent
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hbs : 2 * Real.exp (2 * η) ≤ blockScale θ m := by
    have hkey : Real.log 2 + 2 * η ≤ Real.exp ((m : ℝ) + θ) := by
      linarith [Real.log_two_lt_d9]
    have hrw : 2 * Real.exp (2 * η) = Real.exp (Real.log 2 + 2 * η) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [hrw, blockScale]
    exact Real.exp_le_exp.2 hkey
  have hterm : 2 * Real.exp (2 * η) / blockScale θ m ≤ 1 := by
    rw [div_le_one hb0]; exact hbs
  have hdrift : |blockMean X μ (⌊blockScale θ (m + 1)⌋₊ + 1) s w (primeBlockSub θ m)|
      ≤ Real.exp 2 := by linarith
  have hwin : blockWindow m ≤ 1 := by
    rw [blockWindow, div_le_one (by positivity)]
    nlinarith
  have hwin0 : (0 : ℝ) < blockWindow m := blockWindow_pos m
  -- the variance bracket, already at the per-block cutoff
  obtain ⟨hV₁, hV₂⟩ := blockMatchedVar_concrete_of_le hX θ σ η m s w hm8 hres hσ0 hsc hσ hwn
  have hV₁' : 1 / (2 * Real.exp (2 * η))
      ≤ 2 * ((blockMatchedVar X μ (⌊blockScale θ (m + 1)⌋₊ + 1) s w
        (primeBlockSub θ m) : ℝ≥0) : ℝ) := by
    have hrw : Real.exp (-(2 * η)) / 2 = 1 / (2 * Real.exp (2 * η)) := by
      rw [Real.exp_neg]
      field_simp
    rw [← hrw]; exact hV₁
  -- the threshold, at `A = 2e^{2η}`, `B = 9`, `τ = 3/100`
  have hthr1 := hθ₁ θ m hθ₁'
  have hEη : 2 * Real.exp (2 * η) ≤ 2 * Real.exp (2 * E₀) := by
    have := Real.exp_le_exp.2 (by linarith : 2 * η ≤ 2 * E₀)
    linarith
  have hthr0 : 2 * Real.exp (2 * η) * (a + Bs * m + Real.exp 2 + 1) ^ 2
      + Real.log (Real.pi * 9) / 2
      ≤ 3 / 100 * Real.log (blockScale θ (m + 1)) := by
    have hsq : (0 : ℝ) ≤ (a + Bs * m + Real.exp 2 + 1) ^ 2 := sq_nonneg _
    nlinarith [hthr1, hEη, hsq]
  have henv : M + |blockMean X μ (⌊blockScale θ (m + 1)⌋₊ + 1) s w (primeBlockSub θ m)|
      + blockWindow m ≤ a + Bs * m + Real.exp 2 + 1 := by linarith
  have henv0 : (0 : ℝ) ≤ M
      + |blockMean X μ (⌊blockScale θ (m + 1)⌋₊ + 1) s w (primeBlockSub θ m)|
      + blockWindow m := by positivity
  have hthr : 2 * Real.exp (2 * η) * (M
        + |blockMean X μ (⌊blockScale θ (m + 1)⌋₊ + 1) s w (primeBlockSub θ m)|
        + blockWindow m) ^ 2 + Real.log (Real.pi * 9) / 2
      ≤ 3 / 100 * Real.log (blockScale θ (m + 1)) := by
    have hmono := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ henv0 henv 2)
      (by linarith : (0 : ℝ) ≤ 2 * Real.exp (2 * η))
    linarith
  have hmain := le_toReal_measure_Ioc_blockGaussian_of_thr hX hm5 hres hsc hσ hwn
    hwin0.le (by linarith : (0 : ℝ) < 2 * Real.exp (2 * η)) (by norm_num : (0 : ℝ) < 9)
    hV₁' hV₂ hthr
  intro c hc
  rw [blockQThr, blockMean_blockCutoff_eq hX hsre hmn w,
    blockMatchedVar_blockCutoff_eq hX hsre hmn w]
  simp only [blockCutoff]
  exact hmain c hc

end RMF
