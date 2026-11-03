/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.BlockComparisonExplicit
import RMF.Probability.CurvedBarrierSharp

/-!
# The upper half of Proposition 5, sharpened

Harper's upper bound uses only the upper half of Proposition 5, and the upper half uses only the
upper half of Probability Result 1.  So it need not carry three costs of the lower half: the slope
`B = blockSlopeOf E₀ 125 ≈ 1.8·10²³`, which Probability Result 2's lower bound needs; the level
`a ≥ result1Threshold ≈ 1.7·10¹⁰`, where Result 1's lower bound starts; and the block offset floor
`125`, sized to `B`.

This file runs the window comparison and the Gaussian walk from the offset floor `16`, with
comparison error `e^{-100}`, at the threshold `RMF.proposition5UpperThreshold`
(`RMF.exists_isWindowComparison_steinhaus_of_le_sharp`,
`RMF.exists_isGaussianWalk_steinhaus_of_le_sharp`), and names the constants of the upper half: the
slope `RMF.prop5UpperSlope = 20`, the level `RMF.prop5UpperLevel = 50` and the threshold
`RMF.prop5UpperThreshold E₀`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

/-! ### The comparison and the Gaussian walk, at the floor `16` -/

/-- `ε_m ≤ (e^{-100}/4)(1/2)^m` once `θ ≥ 16`.  `RMF.blockEps_le` proves `(1/8)(1/2)^m`; both are
far from `ε_0 ≤ e^{-240000}`. -/
lemma blockEps_le_exp {θ : ℝ} (hθ : (16 : ℝ) ≤ θ) (m : ℕ) :
    blockEps θ m ≤ Real.exp (-100) / 4 * (1 / 2) ^ m := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have he14 : (1000000 : ℝ) ≤ Real.exp 14 := by
    have he : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    simpa using le_exp_natCast_of_le_pow (c := 2.718) (k := 14) (by norm_num) he (by norm_num)
  -- `e^{m+1+θ} ≥ e¹⁴(1+m)`
  have hEm : Real.exp 14 * (1 + (m : ℝ)) ≤ Real.exp ((m : ℝ) + 1 + θ) := by
    have h1 : (1 : ℝ) + m ≤ Real.exp (m : ℝ) := by linarith [Real.add_one_le_exp (m : ℝ)]
    calc Real.exp 14 * (1 + (m : ℝ)) ≤ Real.exp 14 * Real.exp (m : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos 14).le
      _ = Real.exp (14 + (m : ℝ)) := by rw [← Real.exp_add]
      _ ≤ Real.exp ((m : ℝ) + 1 + θ) := Real.exp_le_exp.2 (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have h6 : 1000000 * (1 + (m : ℝ)) ≤ Real.exp 14 * (1 + (m : ℝ)) :=
    mul_le_mul_of_nonneg_right he14 (by linarith)
  have hkey : 100 + Real.log 4 + (m : ℝ) ≤ 1 / 100 * Real.exp ((m : ℝ) + 1 + θ) := by
    linarith
  -- `e^{-m} ≤ (1/2)^m`, since `e^{-1} ≤ 1/2`
  have hhalf : Real.exp (-(m : ℝ)) ≤ ((1 : ℝ) / 2) ^ m := by
    have he : Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    refine pow_le_pow_left₀ (Real.exp_pos _).le ?_ m
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [blockEps_eq]
  calc Real.exp (-(1 / 100) * Real.exp ((m : ℝ) + 1 + θ))
      ≤ Real.exp (-100 + -Real.log 4 + -(m : ℝ)) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (-100) / 4 * Real.exp (-(m : ℝ)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_neg (Real.log 4),
          Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        ring
    _ ≤ Real.exp (-100) / 4 * ((1 : ℝ) / 2) ^ m :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)

/-- `∑_{m<n} ε_m ≤ e^{-100}/2`, so the compounded error `2E` of the comparison is `e^{-100}`. -/
lemma sum_blockEps_le_exp {θ : ℝ} (hθ : (16 : ℝ) ≤ θ) (n : ℕ) :
    ∑ m ∈ Finset.range n, blockEps θ m ≤ Real.exp (-100) / 2 := by
  have hgeom : ∑ m ∈ Finset.range n, ((1 : ℝ) / 2) ^ m ≤ 2 := by
    rw [geom_sum_eq (by norm_num : ((1 : ℝ) / 2) ≠ 1)]
    have hp : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ n := by positivity
    rw [div_le_iff_of_neg (by norm_num : ((1 : ℝ) / 2 - 1) < 0)]
    linarith
  calc ∑ m ∈ Finset.range n, blockEps θ m
      ≤ ∑ m ∈ Finset.range n, Real.exp (-100) / 4 * ((1 : ℝ) / 2) ^ m :=
        Finset.sum_le_sum fun m _ => blockEps_le_exp hθ m
    _ = Real.exp (-100) / 4 * ∑ m ∈ Finset.range n, ((1 : ℝ) / 2) ^ m := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-100) / 4 * 2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = Real.exp (-100) / 2 := by ring

/-- `e^{-100} ≤ 1/2`, the comparison error against Proposition 5's `ε ≤ 1/2`. -/
lemma exp_neg_hundred_le_half : Real.exp (-100) ≤ 1 / 2 := by
  have h := Real.add_one_le_exp (100 : ℝ)
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 100) (by norm_num)]
  linarith

/-- **The block offset of the upper half of Proposition 5**: the maximum of the window-mass
threshold `RMF.blockQThrThreshold`, the numerical threshold `RMF.blockNumThreshold`,
`log(14 + 2E₀)` and the floor `16`, the least offset `RMF.sum_blockEps_le` accepts.  The comparison
and the Gaussian walk run at this one threshold. -/
noncomputable def proposition5UpperThreshold (E₀ a Bs : ℝ) : ℝ :=
  max (max (blockQThrThreshold E₀ a Bs) (blockNumThreshold E₀ ((3 * E₀ + 8) / 4)))
    (max 16 (Real.log (14 + 2 * E₀)))

/-- **`RMF.exists_isWindowComparison_steinhaus_of_le` at the threshold
`RMF.proposition5UpperThreshold`, with error `e^{-100}`**: the proof uses the floor only as
`θ ≥ 16` (`RMF.sum_blockEps_le_exp`) and `m + θ ≥ 14`. -/
theorem exists_isWindowComparison_steinhaus_of_le_sharp
    (E₀ a Bs : ℝ) (hE₀ : 0 ≤ E₀) (ha : 0 ≤ a) (hBs : 0 < Bs) :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsSteinhausPrimeValues X μ →
      ∀ (θ σ η : ℝ) (n : ℕ) (s : ℂ) (M : ℕ → ℝ),
      (proposition5UpperThreshold E₀ a Bs) ≤ θ → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
      |σ| * Real.log (blockScale θ (n + 1)) ≤ η →
      (∀ m, 0 ≤ M m) → (∀ m, M m ≤ a + Bs * m) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ),
        IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
        (∀ m, Q.map (N m)
          = gaussianReal (blockGaussMean X μ θ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)
              (blockGaussVar X μ θ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)) ∧
        (∀ k, k ≤ n → IsWindowComparison
          (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ n) s μ) Q
          (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
            localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
          (fun m => N (m + k)) (fun m => blockWindow (m + k)) (fun m => M (m + k)) (n - k)
          (Real.exp (-100))) := by
  have hθq := exists_blockQThr_le_measure_explicit E₀ a Bs hE₀ ha hBs
  set θq := blockQThrThreshold E₀ a Bs with hθq_expl
  have hθn := exists_blockNum_le_of_scale_explicit E₀ ((3 * E₀ + 8) / 4) hE₀ (by linarith)
  set θn := blockNumThreshold E₀ ((3 * E₀ + 8) / 4) with hθn_expl
  rw [show proposition5UpperThreshold E₀ a Bs =
      max (max θq θn) (max 16 (Real.log (14 + 2 * E₀))) from rfl]
  intro Ω _ X μ hX θ σ η n s M hθ hres hσ0 hη0 hηE hσtop hM0 hM
  have hθq' : θq ≤ θ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hθ
  have hθn' : θn ≤ θ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hθ
  have hθ16 : (16 : ℝ) ≤ θ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hθ
  have hθlog : Real.log (14 + 2 * E₀) ≤ θ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hθ
  have hsc : ∀ m : ℕ, (14 : ℝ) + 2 * η ≤ Real.exp ((m : ℝ) + θ) := by
    intro m
    have hpos : (0 : ℝ) < 14 + 2 * E₀ := by linarith
    have h1 : (14 : ℝ) + 2 * E₀ ≤ Real.exp θ := by
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.2 hθlog
    have hmt : Real.exp θ ≤ Real.exp ((m : ℝ) + θ) :=
      Real.exp_le_exp.2 (by linarith [Nat.cast_nonneg (α := ℝ) m])
    linarith
  set w : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-s) with hwdef
  have hσm := hsigma_of_top_of_le hσtop
  have hmθ : ∀ m : ℕ, (14 : ℝ) ≤ (m : ℝ) + θ := by
    intro m
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hm3 : ∀ m : ℕ, (3 : ℝ) ≤ (m : ℝ) + θ := fun m => by linarith [hmθ m]
  have hm5 : ∀ m : ℕ, (5 : ℝ) ≤ (m : ℝ) + θ := fun m => by linarith [hmθ m]
  have hm8 : ∀ m : ℕ, (8 : ℝ) ≤ (m : ℝ) + θ := fun m => by linarith [hmθ m]
  have hwn : ∀ m : ℕ, ∀ p ∈ primeBlockSub θ m,
      ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := fun m p _ => norm_sq_prime_cpow_neg p hres
  have hs : 0 < s.re := re_pos_of_block_of_le hres (hsc 0) (hσm 0 (Nat.zero_le n))
  have hV : ∀ m, m ≤ n →
      Real.exp (-(2 * η)) / 2
          ≤ 2 * ((blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m) : ℝ≥0) : ℝ)
            ≤ 9 := by
    intro m hm
    rw [blockMatchedVar_blockCutoff_eq hX hs hm w, blockCutoff]
    exact blockMatchedVar_concrete_of_le hX θ σ η m s w (hm8 m) hres hσ0 (hsc m)
      (hσm m hm) (hwn m)
  -- the numerical condition, at `Kb = e^{3η}·blockThirdConst·8\log 4`
  have hlog40 : (0 : ℝ) ≤ 8 * Real.log 4 := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hbt0 : (0 : ℝ) < blockThirdConst := blockThirdConst_pos
  have hKb0 : (0 : ℝ) ≤ Real.exp (3 * η) * (blockThirdConst * (8 * Real.log 4)) := by
    have := Real.exp_pos (3 * η)
    positivity
  have hKb : Real.exp (3 * η) * (blockThirdConst * (8 * Real.log 4))
      ≤ Real.exp (4 * ((3 * E₀ + 8) / 4)) := by
    have h1152 : blockThirdConst * (8 * Real.log 4) ≤ 1152 := by
      have hb := blockThirdConst_le
      have hl : 8 * Real.log 4 ≤ 12 := by
        have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
          push_cast
          ring
        rw [h4]
        linarith
      nlinarith [hbt0, hlog40]
    have he8 : (1152 : ℝ) ≤ Real.exp 8 := by
      have he : (2.7182 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      simpa using le_exp_natCast_of_le_pow (c := 2.7182) (k := 8)
        (by norm_num) he.le (by norm_num)
    have hsplit : Real.exp (4 * ((3 * E₀ + 8) / 4)) = Real.exp (3 * E₀) * Real.exp 8 := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3η : Real.exp (3 * η) ≤ Real.exp (3 * E₀) := Real.exp_le_exp.2 (by linarith)
    rw [hsplit]
    have hc0 : (0 : ℝ) ≤ blockThirdConst * (8 * Real.log 4) := by positivity
    exact mul_le_mul h3η (le_trans h1152 he8) hc0 (Real.exp_pos _).le
  have hnum : ∀ m, m < n → (450 + 4 / Real.sqrt (2 * Real.pi *
        ((blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m) : ℝ≥0) : ℝ)))
      * (Real.exp (3 * η - 3) * blockT θ m) ^ (1 / 4 : ℝ)
        ≤ blockEps θ m * blockQThr θ (3 / 100) m := by
    intro m hm
    have hVm := (hV m (le_of_lt hm)).1
    have hVge : Real.exp (-(2 * η)) / 4
        ≤ ((blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m) : ℝ≥0) : ℝ) := by
      linarith
    have hT0 : (0 : ℝ) ≤ Real.exp (3 * η - 3) * blockT θ m := by
      have h1 : (0 : ℝ) < blockT θ m := blockT_pos θ m
      have h2 : (0 : ℝ) < Real.exp (3 * η - 3) := Real.exp_pos _
      positivity
    have he3 : Real.exp (3 * η - 3) * Real.exp 3 = Real.exp (3 * η) := by
      rw [← Real.exp_add]; ring_nf
    have hden : (0 : ℝ) < Real.sqrt (blockScale θ m) * Real.log (blockScale θ m) := by
      have h1 : (0 : ℝ) < Real.sqrt (blockScale θ m) := Real.sqrt_pos.2 (blockScale_pos θ m)
      have h2 : (0 : ℝ) < Real.log (blockScale θ m) := by
        rw [log_blockScale]; exact Real.exp_pos _
      positivity
    have hTle : Real.exp (3 * η - 3) * blockT θ m
        ≤ Real.exp (3 * η) * (blockThirdConst * (8 * Real.log 4))
          / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m)) :=
      le_of_eq (by rw [blockT, ← he3]; field_simp [hden.ne'])
    have h := hθn θ η _ _ _ m hθn' hη0 hηE hVge hT0 hKb0 hKb hTle
    rw [blockEps, blockQThr, blockWindow]
    refine le_trans h (le_of_eq ?_)
    norm_num
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, hcmp⟩ :=
    exists_isWindowComparison_primeBlockSub (X := X) (μ := μ) (W := blockWindow) (M := M)
      (T := fun m => Real.exp (3 * η - 3) * blockT θ m) (q := blockQThr θ (3 / 100))
      (ε := blockEps θ) (E := Real.exp (-100) / 2) hX hs
      (fun m _ p hp => norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσm m (by omega)) hp)
      (fun m _ p hp => norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσm m (by omega)) hp)
      (fun m _ => by
        have h1 : (0 : ℝ) < blockT θ m := blockT_pos θ m
        have h2 : (0 : ℝ) < Real.exp (3 * η - 3) := Real.exp_pos _
        positivity)
      (fun m _ => blockQThr_pos θ (3 / 100) m)
      (fun m hm => by
        have h := (hV m (le_of_lt hm)).1
        have hpos : (0 : ℝ) < Real.exp (-(2 * η)) := Real.exp_pos _
        intro hzero
        rw [hzero] at h
        norm_num at h
        linarith)
      (fun m hm => blockThirdConst_mul_sum_le_of_le (hm3 m) (hσm m (le_of_lt hm)) (hwn m))
      (fun m hm => hθq Ω X μ hX θ σ η m n s w (M m) hθq' (le_of_lt hm) hres hσ0 hη0 hηE
        (hσm m (le_of_lt hm)) (hwn m) (hM0 m) (hM m))
      hnum
      (fun m _ => blockEps_nonneg θ m) (sum_blockEps_le_exp (by linarith) n)
      (by linarith [exp_neg_hundred_le_half])
  refine ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, fun k hk => ?_⟩
  have h := hcmp k hk
  rwa [show (2 : ℝ) * (Real.exp (-100) / 2) = Real.exp (-100) by ring] at h

/-- **`RMF.var_bracket_of_bounds` without the lost factor**: its inputs give `0.95e^{-2η} ≤ 2V`
(`0.959·0.9914 ≥ 0.95`), where it states only `e^{-2η}/2 ≤ 2V`. -/
lemma var_bracket_of_bounds_sharp {κ Lx V η : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 1000)
    (hL : (7000 : ℝ) ≤ Lx)
    (hlo : (1 - (40 * κ + 5 * κ ^ 2)) * (Real.exp (-(2 * η)) * (1 - 60 / Lx)) ≤ 2 * V) :
    0.95 * Real.exp (-(2 * η)) ≤ 2 * V := by
  have hL0 : (0 : ℝ) < Lx := by linarith
  have hd : (60 : ℝ) / Lx ≤ 0.0086 := by rw [div_le_iff₀ hL0]; linarith
  have hfac1 : (0.959 : ℝ) ≤ 1 - (40 * κ + 5 * κ ^ 2) := by nlinarith
  have hem0 : (0 : ℝ) < Real.exp (-(2 * η)) := Real.exp_pos _
  have h1 : (0.9914 : ℝ) ≤ 1 - 60 / Lx := by linarith
  have hinner : (0.9914 : ℝ) * Real.exp (-(2 * η))
      ≤ Real.exp (-(2 * η)) * (1 - 60 / Lx) := by nlinarith [hem0, h1]
  have hlow2 : (0.959 : ℝ) * (0.9914 * Real.exp (-(2 * η)))
      ≤ (1 - (40 * κ + 5 * κ ^ 2)) * (Real.exp (-(2 * η)) * (1 - 60 / Lx)) :=
    mul_le_mul hfac1 hinner (by positivity) (by linarith)
  linarith

/-- **The block variance's lower end at a general tilt scale, `0.95e^{-2η} ≤ 2V`**: the lower half
of `RMF.blockMatchedVar_concrete_of_le` through `RMF.var_bracket_of_bounds_sharp`. -/
theorem blockMatchedVar_lower_of_le_sharp {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsSteinhausPrimeValues X μ)
    (θ σ η : ℝ) (j : ℕ) (s : ℂ) (w : Nat.Primes → ℂ)
    (hjθ : (8 : ℝ) ≤ (j : ℝ) + θ) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hsc : 14 + 2 * η ≤ Real.exp ((j : ℝ) + θ))
    (hσ : |σ| * Real.log (blockScale θ (j + 1)) ≤ η)
    (hwn : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    0.95 * Real.exp (-(2 * η)) ≤ 2 * ((blockMatchedVar X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w
        (primeBlockSub θ j) : ℝ≥0) : ℝ) := by
  have hj3 : (3 : ℝ) ≤ (j : ℝ) + θ := by linarith
  have hb0 : (0 : ℝ) < blockScale θ j := blockScale_pos θ j
  have hκ0 : (0 : ℝ) ≤ Real.exp η / √(blockScale θ j) := by
    have := Real.sqrt_pos.2 hb0
    positivity
  have hκ : Real.exp η / √(blockScale θ j) ≤ 1 / 1000 := blockWeightSize_le_of_le hsc
  have hw : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ≤ Real.exp η / √(blockScale θ j) := fun p hp =>
    norm_le_of_mem_primeBlockSub_of_le hσ hp (hwn p hp)
  have ha : ∀ p ∈ primeBlockSub θ j,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ Real.exp η / √(blockScale θ j) := fun p hp =>
    norm_le_of_mem_primeBlockSub_of_le hσ hp (norm_sq_prime_cpow_neg p hres)
  obtain ⟨hlo, -⟩ := blockMatchedVar_bounds_of_le hX hj3 hres hσ0 hsc hσ hκ0 hκ hw ha hwn
  -- the Mertens term at `j + θ ≥ 8`
  have hL : (7000 : ℝ) ≤ Real.log (blockScale θ (j + 1)) := by
    rw [log_blockScale]
    have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (7000 : ℝ) ≤ (2.7 : ℝ) ^ (9 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 9
      _ = Real.exp ((9 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (((j + 1 : ℕ) : ℝ) + θ) := Real.exp_le_exp.2 (by push_cast; linarith)
  exact var_bracket_of_bounds_sharp hκ0 hκ hL hlo

/-- **The variance floor `0.475e^{-2η}` at every index**: the lower half of
`RMF.blockGaussVar_bounds_of_le` at `RMF.blockMatchedVar_lower_of_le_sharp`; the dummy indices above
`n` keep the value `1`. -/
theorem blockGaussVar_lower_of_le_sharp {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsSteinhausPrimeValues X μ) {θ σ η : ℝ} {n : ℕ} {s : ℂ}
    {w : Nat.Primes → ℂ} (hθ : (8 : ℝ) ≤ θ) (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hsc : ∀ j : ℕ, 14 + 2 * η ≤ Real.exp ((j : ℝ) + θ))
    (hσ : ∀ j, j ≤ n → |σ| * Real.log (blockScale θ (j + 1)) ≤ η)
    (hwn : ∀ j, j ≤ n → ∀ p ∈ primeBlockSub θ j,
      ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    ∀ m, 0.475 * Real.exp (-(2 * η)) ≤ ((blockGaussVar X μ θ n s w m : ℝ≥0) : ℝ) := by
  have hlog0 : (0 : ℝ) ≤ Real.log (blockScale θ (0 + 1)) := by
    rw [log_blockScale]; positivity
  have hη0 : (0 : ℝ) ≤ η :=
    le_trans (mul_nonneg (abs_nonneg σ) hlog0) (hσ 0 (Nat.zero_le n))
  have he1 : Real.exp (-(2 * η)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  intro m
  by_cases hm : m ≤ n
  · have hmθ : (8 : ℝ) ≤ (m : ℝ) + θ := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    rw [blockGaussVar, if_pos hm, blockMatchedVar_blockCutoff_eq hX hs hm w, blockCutoff]
    have hlo :=
      blockMatchedVar_lower_of_le_sharp hX θ σ η m s w hmθ hres hσ0 (hsc m) (hσ m hm) (hwn m hm)
    linarith
  · rw [blockGaussVar, if_neg hm]
    push_cast
    linarith

/-- **`RMF.exists_isGaussianWalk_steinhaus_of_le` at the floor `16`**, at the threshold
`RMF.proposition5UpperThreshold E₀ a Bs`, with comparison error `e^{-100}` and variance floor
`0.475e^{-2η}` (`RMF.blockGaussVar_lower_of_le_sharp`): the Gaussian walk needs only `θ ≥ 8` beyond
the comparison. -/
theorem exists_isGaussianWalk_steinhaus_of_le_sharp
    (E₀ a Bs : ℝ) (hE₀ : 0 ≤ E₀) (ha : 0 ≤ a) (hBs : 0 < Bs) :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsSteinhausPrimeValues X μ →
      ∀ (θ σ η : ℝ) (n : ℕ) (s : ℂ) (M : ℕ → ℝ),
      (proposition5UpperThreshold E₀ a Bs) ≤ θ → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
      |σ| * Real.log (blockScale θ (n + 1)) ≤ η →
      (∀ m, 0 ≤ M m) → (∀ m, M m ≤ a + Bs * m) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (G N : ℕ → Ω' → ℝ) (v : ℕ → ℝ≥0),
        IsProbabilityMeasure Q ∧ IsGaussianWalk G v Q ∧ (∀ m, Measurable (N m)) ∧
        (∀ m ω, N m ω
          = G m ω + blockGaussMean X μ θ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m) ∧
        (∀ i, 0.475 * Real.exp (-(2 * η)) ≤ (v i : ℝ)) ∧ (∀ i, (v i : ℝ) ≤ 9 / 2) ∧
        (∀ k, k ≤ n → IsWindowComparison
          (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ n) s μ) Q
          (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
            localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
          (fun m => N (m + k)) (fun m => blockWindow (m + k)) (fun m => M (m + k)) (n - k)
          (Real.exp (-100))) := by
  have hθw := exists_isWindowComparison_steinhaus_of_le_sharp E₀ a Bs hE₀ ha hBs
  intro Ω _ X μ hX θ σ η n s M hθ hres hσ0 hη0 hηE hσtop hM0 hM
  have hθ' : max (max (blockQThrThreshold E₀ a Bs) (blockNumThreshold E₀ ((3 * E₀ + 8) / 4)))
      (max 16 (Real.log (14 + 2 * E₀))) ≤ θ := hθ
  have hθ16 : (16 : ℝ) ≤ θ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hθ'
  have hθlog : Real.log (14 + 2 * E₀) ≤ θ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hθ'
  have hθE : (14 : ℝ) + 2 * E₀ ≤ Real.exp θ := by
    have hpos : (0 : ℝ) < 14 + 2 * E₀ := by linarith
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 hθlog
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, hcmp⟩ :=
    hθw Ω X μ hX θ σ η n s M hθ hres hσ0 hη0 hηE hσtop hM0 hM
  have hσm := hsigma_of_top_of_le hσtop
  have hs : 0 < s.re :=
    re_pos_of_block_of_le hres (scale_cond_of_le hηE hθE) (hσm 0 (Nat.zero_le n))
  have hwn : ∀ j : ℕ, j ≤ n → ∀ p ∈ primeBlockSub θ j,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun _ _ p _ => norm_sq_prime_cpow_neg p hres
  have hvb := blockGaussVar_bounds_of_le hX (by linarith : (8 : ℝ) ≤ θ) hs hres hσ0
    (fun j => scale_cond_of_le hηE hθE) hσm hwn
  have hvlo := blockGaussVar_lower_of_le_sharp hX (by linarith : (8 : ℝ) ≤ θ) hs hres hσ0
    (fun j => scale_cond_of_le hηE hθE) hσm hwn
  exact ⟨Ω', mΩ', Q, fun m ω => N m ω
      - blockGaussMean X μ θ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m, N,
    blockGaussVar X μ θ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)), hQ,
    isGaussianWalk_sub_const hNm hNi hNlaw, hNm, fun m ω => by ring,
    hvlo, fun i => (hvb i).2, hcmp⟩

/-! ### The constants of the upper half -/

/-- **The slope of the lower barrier in Harper's upper bound**, `20`: the upper half of
Proposition 5 holds at every slope `B ≥ 20`, and `20` is the least slope the index barrier
(`RMF.IsSteinhausPrimeValues.measure_exists_barrier_le_of_le_sharp`) admits. -/
noncomputable def prop5UpperSlope : ℝ := 20

lemma prop5UpperSlope_eq : prop5UpperSlope = 20 := rfl

lemma twenty_le_prop5UpperSlope : (20 : ℝ) ≤ prop5UpperSlope := prop5UpperSlope_eq.ge

/-- **The threshold of the upper half of Proposition 5**: `RMF.proposition5UpperThreshold` at the
envelope `25 + 2B + (48 + 4B)m`, `B = prop5UpperSlope`. -/
noncomputable def prop5UpperThreshold (E₀ : ℝ) : ℝ :=
  proposition5UpperThreshold E₀ (25 + 2 * prop5UpperSlope) (48 + 4 * prop5UpperSlope)

/-- `prop5UpperThreshold E₀ ≥ 16`: the floor. -/
lemma sixteen_le_prop5UpperThreshold (E₀ : ℝ) : (16 : ℝ) ≤ prop5UpperThreshold E₀ := by
  unfold prop5UpperThreshold proposition5UpperThreshold
  exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- **The level of the upper half of Proposition 5**, `50`. -/
noncomputable def prop5UpperLevel : ℝ := 50

end RMF
