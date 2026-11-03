/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherBlockExplicit
import RMF.Probability.BlockComparisonSharp

/-!
# The Rademacher window comparison, sharp

The Rademacher twins of `RMF.exists_isWindowComparison_steinhaus_of_le_sharp` and
`RMF.exists_isGaussianWalk_steinhaus_of_le_sharp`.  The tilted Rademacher block walk at one point
`s` is compared with a Gaussian walk block by block, with error `e^{-100}`, at the block offset
`RMF.radUpperThreshold E₀ a Bs` (floor `16`).  The one Rademacher-specific input is that every
block's oscillatory sum `∑_{p ∈ B} cos(2 Im s·log p)/p^{1+2σ}` is at most `εc ≤ e^{-2E₀}/100`,
which the explicit prime number theorem supplies past the block floor `104`, under conditions on
the height.

The per-block inputs are those of `RMF/Probability/RademacherBlockExplicit.lean`, and the Lindeberg
step is the generic seam `RMF.exists_isWindowComparison_primeBlockSubAdd`.  The Gaussian walk's
variances lie in `[0.49e^{-2η}, 1]`, against the Steinhaus `[0.475e^{-2η}, 9/2]`.

## Main results

* `RMF.exists_isWindowComparison_rademacher_of_le_sharp`
* `RMF.exists_isGaussianWalk_rademacher_of_le_sharp`
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The block offset of the sharp Rademacher comparison: the thresholds of the window mass and of
the numerical condition, the floor `16` of `RMF.sum_blockEps_le_exp`, and `log(28 + 2E₀)` for
the weight bound `10⁻⁶`. -/
noncomputable def radUpperThreshold (E₀ a Bs : ℝ) : ℝ :=
  max (max (thrDirectThreshold (2 * Real.exp (2 * E₀)) a Bs 1 (3 / 100))
      (blockNumThreshold E₀ ((3 * E₀ + 8) / 4)))
    (max 16 (Real.log (28 + 2 * E₀)))

/-- The four facts the offset `RMF.radUpperThreshold` carries. -/
lemma radUpperThreshold_facts {E₀ a Bs θ : ℝ} (hE₀ : 0 ≤ E₀)
    (hθ : radUpperThreshold E₀ a Bs ≤ θ) :
    thrDirectThreshold (2 * Real.exp (2 * E₀)) a Bs 1 (3 / 100) ≤ θ ∧
      blockNumThreshold E₀ ((3 * E₀ + 8) / 4) ≤ θ ∧ (16 : ℝ) ≤ θ ∧
      28 + 2 * E₀ ≤ Real.exp θ := by
  unfold radUpperThreshold at hθ
  refine ⟨le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hθ,
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hθ,
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hθ, ?_⟩
  have hlog : Real.log (28 + 2 * E₀) ≤ θ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hθ
  have hpos : (0 : ℝ) < 28 + 2 * E₀ := by linarith
  rw [← Real.exp_log hpos]
  exact Real.exp_le_exp.2 hlog

/-- The scale condition on every block from the offset: `28 + 2η ≤ e^{m+θ}`. -/
lemma scale_cond_28_of_le {θ η E : ℝ} {m : ℕ} (hηE : η ≤ E) (hθ : 28 + 2 * E ≤ Real.exp θ) :
    28 + 2 * η ≤ Real.exp ((m : ℝ) + θ) := by
  have hmθ : Real.exp θ ≤ Real.exp ((m : ℝ) + θ) :=
    Real.exp_le_exp.2 (by linarith [Nat.cast_nonneg (α := ℝ) m])
  linarith

/-! ### The per-block inputs -/

/-- **The variance of the sharp comparison**: `0.98e^{-2η} ≤ 2V ≤ 1.02`, from
`RMF.blockMatchedVarAdd_bounds_sharp` once the oscillatory sum is at most `e^{-2E₀}/100`. -/
lemma blockMatchedVarAdd_concrete_sharp (hX : IsRademacherPrimeValues X μ)
    {E₀ θ σ η εc : ℝ} {m n : ℕ} {s : ℂ} (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hηE : η ≤ E₀) (hθ16 : (16 : ℝ) ≤ θ) (hθE : 28 + 2 * E₀ ≤ Real.exp θ)
    (hmn : m ≤ n) (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hεc : εc ≤ Real.exp (-(2 * E₀)) / 100)
    (hcos : |∑ p ∈ primeBlockSub θ m,
        Real.cos (2 * s.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)| ≤ εc) :
    0.98 * Real.exp (-(2 * η))
        ≤ 2 * ((blockMatchedVarAdd X μ (blockCutoff θ n) s (fun p => ((p : ℕ) : ℂ) ^ (-s))
            (primeBlockSub θ m) : ℝ≥0) : ℝ)
      ∧ 2 * ((blockMatchedVarAdd X μ (blockCutoff θ n) s (fun p => ((p : ℕ) : ℂ) ^ (-s))
            (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 1.02 := by
  have hmθ : (16 : ℝ) ≤ (m : ℝ) + θ := by linarith [Nat.cast_nonneg (α := ℝ) m]
  obtain ⟨hlo, hhi⟩ := blockMatchedVarAdd_bounds_sharp hX hs hres hσ0 hmθ
    (scale_cond_28_of_le hηE hθE) hσ (primeBlockSub_subset_primesBelowSub_of_le hmn le_rfl) hcos
  have hE : Real.exp (-(2 * E₀)) ≤ Real.exp (-(2 * η)) := Real.exp_le_exp.2 (by linarith)
  have hE1 : Real.exp (-(2 * E₀)) ≤ 1 := by
    have h0 : (0 : ℝ) ≤ E₀ := by
      have hl : 0 ≤ Real.log (blockScale θ (m + 1)) := by
        rw [log_blockScale]; exact (Real.exp_pos _).le
      linarith [mul_nonneg (abs_nonneg σ) hl]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hc0 : (0 : ℝ) ≤ εc := le_trans (abs_nonneg _) hcos
  have hpos : (0 : ℝ) < Real.exp (-(2 * η)) := Real.exp_pos _
  exact ⟨by linarith, by linarith⟩

/-- The block's window `1/(m+1)^2` is at most `1`. -/
private lemma blockWindow_le_one' (m : ℕ) : blockWindow m ≤ 1 := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [blockWindow, div_le_one (by positivity)]
  nlinarith

/-- **The block mean is at most `e²`**: `S + C/2 ≤ 1.01` up to the `37·10⁻⁶S` of
`RMF.abs_blockMeanAdd_sub_le_sharp`, once `|C| ≤ 1/100`. -/
lemma abs_blockMeanAdd_le_exp_two_sharp (hX : IsRademacherPrimeValues X μ)
    {θ σ η εc : ℝ} {m : ℕ} {y : ℕ} {s : ℂ} (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hmθ : (16 : ℝ) ≤ (m : ℝ) + θ)
    (hsc : 28 + 2 * η ≤ Real.exp ((m : ℝ) + θ))
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) (hc1 : εc ≤ 1 / 100)
    (hcos : |∑ p ∈ primeBlockSub θ m,
        Real.cos (2 * s.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)| ≤ εc) :
    |blockMeanAdd X μ y s (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m)|
      ≤ Real.exp 2 := by
  have hwn : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun p _ => norm_sq_prime_cpow_neg p hres
  obtain ⟨-, hShi⟩ := sum_norm_sq_primeBlockSub_bounds_sharp hmθ hσ0 hσ hwn
  rw [Finset.sum_congr rfl hwn] at hShi
  have hS0 : (0 : ℝ) ≤ ∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    Finset.sum_nonneg fun p _ => Real.rpow_nonneg (by positivity) _
  have hmean := abs_blockMeanAdd_sub_le_sharp hX hs hres hsc hσ hB
  rw [abs_le] at hmean hcos
  have he2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  rw [abs_le]
  constructor <;> linarith [hmean.1, hmean.2, hcos.1, hcos.2]

/-- **The window mass of the sharp comparison**: `blockQThr θ (3/100) m` below the Gaussian mass
of every window `(c, c + W_m]` with `|c| ≤ M ≤ a + Bs·m`.  The block mean is at most `e²`
(`RMF.abs_blockMeanAdd_sub_le_sharp`: `S + C/2 ≤ 1.01`), so `RMF.exists_thr_direct_explicit`
at `A = 2e^{2E₀}` is the Steinhaus threshold unchanged. -/
lemma blockQThrAdd_le_measure_sharp (hX : IsRademacherPrimeValues X μ)
    {E₀ a Bs θ σ η εc M : ℝ} {m n : ℕ} {s : ℂ} (hE₀ : 0 ≤ E₀) (ha : 0 ≤ a) (hBs : 0 < Bs)
    (hθ : radUpperThreshold E₀ a Bs ≤ θ) (hmn : m ≤ n) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hηE : η ≤ E₀)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hεc : εc ≤ Real.exp (-(2 * E₀)) / 100)
    (hcos : |∑ p ∈ primeBlockSub θ m,
        Real.cos (2 * s.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)| ≤ εc)
    (hM0 : 0 ≤ M) (hM : M ≤ a + Bs * m) :
    ∀ c, |c| ≤ M → blockQThr θ (3 / 100) m ≤ (gaussianReal
        (blockMeanAdd X μ (blockCutoff θ n) s (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m))
        (blockMatchedVarAdd X μ (blockCutoff θ n) s (fun p => ((p : ℕ) : ℂ) ^ (-s))
          (primeBlockSub θ m))
        (Set.Ioc c (c + blockWindow m))).toReal := by
  obtain ⟨hθthr, -, hθ16, hθE⟩ := radUpperThreshold_facts hE₀ hθ
  set w : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-s) with hwdef
  have hsc := scale_cond_28_of_le (m := m) hηE hθE
  have hsc14 : 14 + 2 * η ≤ Real.exp ((m : ℝ) + θ) := by linarith
  have hs : 0 < s.re := re_pos_of_block_of_le hres hsc14 hσ
  have hmθ : (16 : ℝ) ≤ (m : ℝ) + θ := by linarith [Nat.cast_nonneg (α := ℝ) m]
  obtain ⟨hVlo, hVhi⟩ := blockMatchedVarAdd_concrete_sharp hX hs hres hσ0 hηE hθ16 hθE
    hmn hσ hεc hcos
  have hVη : Real.exp (-(2 * η)) / 2
      ≤ 2 * ((blockMatchedVarAdd X μ (blockCutoff θ n) s w (primeBlockSub θ m) : ℝ≥0) : ℝ) := by
    have := Real.exp_pos (-(2 * η))
    linarith
  have hv : blockMatchedVarAdd X μ (blockCutoff θ n) s w (primeBlockSub θ m) ≠ 0 := by
    intro h0
    rw [h0] at hVlo
    have := Real.exp_pos (-(2 * η))
    norm_num at hVlo
    linarith
  have hE1 : Real.exp (-(2 * E₀)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hmabs : |blockMeanAdd X μ (blockCutoff θ n) s w (primeBlockSub θ m)| ≤ Real.exp 2 :=
    abs_blockMeanAdd_le_exp_two_sharp hX hs hres hσ0 hmθ hsc hσ
      (primeBlockSub_subset_primesBelowSub_of_le hmn le_rfl) (by linarith) hcos
  -- the threshold at `A = 2e^{2E₀}`, `B = 9`, hence at `A = 2e^{2η} ≤ 2e^{2E₀}`
  have hthr1 := exists_thr_direct_explicit (2 * Real.exp (2 * E₀)) a Bs 1 (3 / 100)
    (by have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 2 * E₀); linarith) ha hBs
    (by norm_num) (by norm_num) θ m hθthr
  have hEη : 2 * Real.exp (2 * η) ≤ 2 * Real.exp (2 * E₀) := by
    have := Real.exp_le_exp.2 (by linarith : 2 * η ≤ 2 * E₀)
    linarith
  have hwin : blockWindow m ≤ 1 := blockWindow_le_one' m
  have hwin0 : (0 : ℝ) < blockWindow m := blockWindow_pos m
  have henv : M + |blockMeanAdd X μ (blockCutoff θ n) s w (primeBlockSub θ m)| + blockWindow m
      ≤ a + Bs * m + Real.exp 2 + 1 := by linarith
  have henv0 : (0 : ℝ)
      ≤ M + |blockMeanAdd X μ (blockCutoff θ n) s w (primeBlockSub θ m)| + blockWindow m :=
    add_nonneg (add_nonneg hM0 (abs_nonneg _)) hwin0.le
  have hthr : 2 * Real.exp (2 * η) * (M
        + |blockMeanAdd X μ (blockCutoff θ n) s w (primeBlockSub θ m)| + blockWindow m) ^ 2
        + Real.log (Real.pi * 9) / 2
      ≤ 3 / 100 * Real.log (blockScale θ (m + 1)) := by
    have hmono := mul_le_mul hEη (pow_le_pow_left₀ henv0 henv 2) (sq_nonneg _)
      (by positivity : (0 : ℝ) ≤ 2 * Real.exp (2 * E₀))
    linarith
  have hV₁ : 1 / (2 * Real.exp (2 * η))
      ≤ 2 * ((blockMatchedVarAdd X μ (blockCutoff θ n) s w (primeBlockSub θ m) : ℝ≥0) : ℝ) := by
    have hrw : Real.exp (-(2 * η)) / 2 = 1 / (2 * Real.exp (2 * η)) := by
      rw [Real.exp_neg]
      field_simp
    rw [← hrw]
    exact hVη
  have hx1 : (1 : ℝ) ≤ blockScale θ (m + 1) := by
    rw [blockScale]; exact Real.one_le_exp (Real.exp_pos _).le
  intro c hc
  rw [blockQThr]
  exact le_toReal_measure_Ioc_gaussianReal_of_thr hv hwin0.le
    (by positivity : (0 : ℝ) < 2 * Real.exp (2 * η)) (by norm_num : (0 : ℝ) < 9) hV₁
    (by linarith) hx1 hc hthr

/-- **`hTb` of the sharp comparison**: `blockThirdConstAdd·∑‖w‖³ ≤ e^{3η-3}·blockTAdd θ m`, the
Rademacher counterpart of `RMF.blockThirdConst_mul_sum_le_of_le`. -/
lemma blockThirdConstAdd_mul_sum_le_of_le {θ σ η : ℝ} {m : ℕ} {w : Nat.Primes → ℂ}
    (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    blockThirdConstAdd * ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 3
      ≤ Real.exp (3 * η - 3) * blockTAdd θ m := by
  have he : Real.exp (3 * η - 3) * Real.exp 3 = Real.exp (3 * η) := by
    rw [← Real.exp_add]; ring_nf
  have hrw : Real.exp (3 * η - 3) * blockTAdd θ m
      = blockThirdConstAdd * (Real.exp (3 * η) * (8 * Real.log 4
          / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m)))) := by
    rw [blockTAdd, ← he]; ring
  rw [hrw]
  exact mul_le_mul_of_nonneg_left (sum_norm_cube_primeBlockSub_le_of_le hmθ hσ hwn)
    blockThirdConstAdd_pos.le

/-- **`hnum` of the sharp comparison**: `RMF.exists_blockNum_le_of_scale_explicit` at the
Rademacher third-moment constant.  `e^{3η}·blockThirdConstAdd·8 log 4 ≤ 2400e^{3E₀} ≤ e^{3E₀+8}`,
so the Steinhaus threshold `RMF.blockNumThreshold E₀ ((3E₀+8)/4)` serves unchanged. -/
lemma blockNumAdd_le_sharp {E₀ θ η V : ℝ} {m : ℕ} (hE₀ : 0 ≤ E₀)
    (hθn : blockNumThreshold E₀ ((3 * E₀ + 8) / 4) ≤ θ) (hη0 : 0 ≤ η) (hηE : η ≤ E₀)
    (hV : Real.exp (-(2 * η)) / 4 ≤ V) :
    (450 + 4 / Real.sqrt (2 * Real.pi * V)) * (Real.exp (3 * η - 3) * blockTAdd θ m) ^ (1 / 4 : ℝ)
      ≤ blockEps θ m * blockQThr θ (3 / 100) m := by
  have hθ0 : (0 : ℝ) < Real.log (blockScale θ m) := by rw [log_blockScale]; exact Real.exp_pos _
  have hT0 : (0 : ℝ) ≤ Real.exp (3 * η - 3) * blockTAdd θ m :=
    mul_nonneg (Real.exp_pos _).le (blockTAdd_pos hθ0).le
  have hl40 : (0 : ℝ) ≤ 8 * Real.log 4 := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hbt0 : (0 : ℝ) < blockThirdConstAdd := blockThirdConstAdd_pos
  have hKb0 : (0 : ℝ) ≤ Real.exp (3 * η) * (blockThirdConstAdd * (8 * Real.log 4)) := by
    have := Real.exp_pos (3 * η)
    positivity
  have hKb : Real.exp (3 * η) * (blockThirdConstAdd * (8 * Real.log 4))
      ≤ Real.exp (4 * ((3 * E₀ + 8) / 4)) := by
    have h2400 : blockThirdConstAdd * (8 * Real.log 4) ≤ 2400 := by
      have hb := blockThirdConstAdd_le
      have hl : 8 * Real.log 4 ≤ 12 := by
        have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
          push_cast
          ring
        rw [h4]
        linarith
      nlinarith [hbt0, hl40]
    have he8 : (2400 : ℝ) ≤ Real.exp 8 := by
      have he : (2.7182 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      simpa using le_exp_natCast_of_le_pow (c := 2.7182) (k := 8)
        (by norm_num) he.le (by norm_num)
    have hsplit : Real.exp (4 * ((3 * E₀ + 8) / 4)) = Real.exp (3 * E₀) * Real.exp 8 := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3η : Real.exp (3 * η) ≤ Real.exp (3 * E₀) := Real.exp_le_exp.2 (by linarith)
    rw [hsplit]
    have hc0 : (0 : ℝ) ≤ blockThirdConstAdd * (8 * Real.log 4) := by positivity
    exact mul_le_mul h3η (le_trans h2400 he8) hc0 (Real.exp_pos _).le
  have he3 : Real.exp (3 * η - 3) * Real.exp 3 = Real.exp (3 * η) := by
    rw [← Real.exp_add]; ring_nf
  have hden : (0 : ℝ) < Real.sqrt (blockScale θ m) * Real.log (blockScale θ m) := by
    have h1 : (0 : ℝ) < Real.sqrt (blockScale θ m) := Real.sqrt_pos.2 (blockScale_pos θ m)
    positivity
  have hTle : Real.exp (3 * η - 3) * blockTAdd θ m
      ≤ Real.exp (3 * η) * (blockThirdConstAdd * (8 * Real.log 4))
        / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m)) :=
    le_of_eq (by rw [blockTAdd, ← he3]; field_simp [hden.ne'])
  have h := exists_blockNum_le_of_scale_explicit E₀ ((3 * E₀ + 8) / 4) hE₀ (by linarith)
    θ η _ _ _ m hθn hη0 hηE hV hT0 hKb0 hKb hTle
  rw [blockEps, blockQThr, blockWindow]
  refine le_trans h (le_of_eq ?_)
  norm_num

/-! ### The oscillatory sum, from the explicit prime number theorem -/

/-- The oscillatory sum of a block in the `rpow` spelling, at `τ = 2|t|`: the cosine is even. -/
lemma sum_cos_div_primeBlockSub_eq_abs (θ σ t : ℝ) (m : ℕ) :
    ∑ p ∈ primeBlockSub θ m,
        Real.cos (2 * t * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)
      = ∑ p ∈ primeBlockSub θ m,
        Real.cos (2 * |t| * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hc : Real.cos (2 * t * Real.log ((p : ℕ) : ℝ))
      = Real.cos (2 * |t| * Real.log ((p : ℕ) : ℝ)) := by
    rcases abs_choice t with ht | ht <;> rw [ht]
    rw [show 2 * -t * Real.log ((p : ℕ) : ℝ) = -(2 * t * Real.log ((p : ℕ) : ℝ)) by ring,
      Real.cos_neg]
  rw [hc, show (-1 - 2 * σ : ℝ) = -(1 + 2 * σ) by ring, Real.rpow_neg hp0.le, div_eq_mul_inv]

/-- The constant `K_t = 3/(2|t|e^θ) + (2|t|+1)/10²⁸`: `RMF.cosGeomConstF` with `pntFloorConst θ`
replaced by its bound `10⁻²⁸` past the floor `104` (`RMF.pntFloorConst_le`). -/
noncomputable def cosGeomConst (θ t : ℝ) : ℝ :=
  3 / (2 * |t| * Real.exp θ) + (2 * |t| + 1) / 10 ^ 28

/-! ### The oscillatory sum at a higher floor

The height condition `2|t| + 1 ≤ 5·10²⁵e^{-2E₀}` is the prime number theorem's term evaluated at
the floor `104`.  At a higher floor `θ` the term is `pntFloorConst θ`, which falls doubly
exponentially, so the heights allowed grow with the floor. -/

/-- The effective prime number theorem's term at the floor `θ`: `32·10⁴⁰·exp(-e^{θ/10}/200)`. -/
noncomputable def pntFloorConst (θ : ℝ) : ℝ :=
  32 * 10 ^ (40 : ℕ) * Real.exp (-(1 / 200 : ℝ) * Real.exp (θ / 10))

lemma pntFloorConst_nonneg (θ : ℝ) : 0 ≤ pntFloorConst θ := by
  unfold pntFloorConst
  positivity

/-- `pntFloorConst θ ≤ 10⁻²⁸` past the floor `104` (`RMF.pnt_term_at_floor_le`). -/
lemma pntFloorConst_le {θ : ℝ} (hθ : (104 : ℝ) ≤ θ) : pntFloorConst θ ≤ 1 / 10 ^ 28 := by
  refine le_trans ?_ pnt_term_at_floor_le
  unfold pntFloorConst
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have : Real.exp 10.4 ≤ Real.exp (θ / 10) := Real.exp_le_exp.2 (by linarith)
  linarith

/-- **The prime number theorem's term, geometric in the block index, at the floor `θ`**:
`32·10⁴⁰·exp(-e^{(m+θ)/10}/200) ≤ pntFloorConst θ·e^{-m}` for `θ ≥ 104`. -/
lemma pnt_term_le_geometric_floor {θ : ℝ} (hθ : (104 : ℝ) ≤ θ) (m : ℕ) :
    32 * 10 ^ (40 : ℕ) * Real.exp (-(1 / 200 : ℝ) * Real.exp (((m : ℝ) + θ) / 10))
      ≤ pntFloorConst θ * Real.exp (-(m : ℝ)) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have he : (2.7182 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h8 : (2400 : ℝ) ≤ Real.exp 8 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.7182) (k := 8) (by norm_num) he.le
      (by norm_num)
  have hθ10 : (2000 : ℝ) ≤ Real.exp (θ / 10) :=
    le_trans (by linarith) (le_trans h8 (Real.exp_le_exp.2 (by linarith)))
  have hsplit : Real.exp (θ / 10) * Real.exp ((m : ℝ) / 10)
      = Real.exp (((m : ℝ) + θ) / 10) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hlin : (m : ℝ) / 10 + 1 ≤ Real.exp ((m : ℝ) / 10) := Real.add_one_le_exp _
  have hprod : Real.exp (θ / 10) * ((m : ℝ) / 10 + 1)
      ≤ Real.exp (θ / 10) * Real.exp ((m : ℝ) / 10) :=
    mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le
  have hm2 : 2000 * ((m : ℝ) / 10) ≤ Real.exp (θ / 10) * ((m : ℝ) / 10) :=
    mul_le_mul_of_nonneg_right hθ10 (by positivity)
  have hexp : Real.exp (-(1 / 200 : ℝ) * Real.exp (((m : ℝ) + θ) / 10))
      ≤ Real.exp (-(1 / 200 : ℝ) * Real.exp (θ / 10)) * Real.exp (-(m : ℝ)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  unfold pntFloorConst
  calc 32 * 10 ^ (40 : ℕ) * Real.exp (-(1 / 200 : ℝ) * Real.exp (((m : ℝ) + θ) / 10))
      ≤ 32 * 10 ^ (40 : ℕ)
          * (Real.exp (-(1 / 200 : ℝ) * Real.exp (θ / 10)) * Real.exp (-(m : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 32 * 10 ^ (40 : ℕ) * Real.exp (-(1 / 200 : ℝ) * Real.exp (θ / 10))
          * Real.exp (-(m : ℝ)) := by ring

/-- The constant of `RMF.abs_sum_cos_div_primeBlockSub_le_geometric_floor`,
`K_t = 3/(2|t|e^θ) + (2|t|+1)·pntFloorConst θ`. -/
noncomputable def cosGeomConstF (θ t : ℝ) : ℝ :=
  3 / (2 * |t| * Real.exp θ) + (2 * |t| + 1) * pntFloorConst θ

lemma cosGeomConstF_nonneg (θ t : ℝ) : 0 ≤ cosGeomConstF θ t := by
  have := pntFloorConst_nonneg θ
  rw [cosGeomConstF]
  positivity

/-- **The oscillatory sum, geometric in the block index, at the floor `θ`**: past the floor `104`,
`|∑_{p ∈ B_m} cos(2t log p)/p^{1+2σ}| ≤ K_t e^{-m}` with `K_t = RMF.cosGeomConstF θ t`, the prime
number theorem's term kept at `θ` (`RMF.pnt_term_le_geometric_floor`). -/
theorem abs_sum_cos_div_primeBlockSub_le_geometric_floor {θ σ t : ℝ} (m : ℕ) (hσ0 : 0 ≤ σ)
    (hθ : (104 : ℝ) ≤ θ) (ht : 0 < |t|) :
    |∑ p ∈ primeBlockSub θ m,
        Real.cos (2 * t * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
      ≤ cosGeomConstF θ t * Real.exp (-(m : ℝ)) := by
  have hτ : 0 < 2 * |t| := by linarith
  have hm : Real.log (Real.log blockCosineThreshold) ≤ (m : ℝ) + θ :=
    le_trans log_log_blockCosineThreshold_le_104 (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have h := abs_sum_cos_primeBlockSub_rpow_le_of_weight_bound_of_nonneg
    abs_cos_prime_sum_block_weight_le_blockCosineThreshold.1
    abs_cos_prime_sum_block_weight_le_blockCosineThreshold.2 (2 * |t|) σ θ m hτ hσ0 hm
  rw [sum_cos_div_primeBlockSub_eq_abs]
  refine le_trans h ?_
  have h1 : 3 / (2 * |t| * Real.exp ((m : ℝ) + θ))
      = 3 / (2 * |t| * Real.exp θ) * Real.exp (-(m : ℝ)) := by
    rw [show (m : ℝ) + θ = θ + m by ring, Real.exp_add, Real.exp_neg]
    field_simp
  have h2 : 32 * 10 ^ (40 : ℕ) * (2 * |t| + 1)
        * Real.exp (-(1 / 200 : ℝ) * Real.exp (((m : ℝ) + θ) / 10))
      ≤ (2 * |t| + 1) * pntFloorConst θ * Real.exp (-(m : ℝ)) := by
    have hp := pnt_term_le_geometric_floor hθ m
    have hτ1 : (0 : ℝ) ≤ 2 * |t| + 1 := by positivity
    calc 32 * 10 ^ (40 : ℕ) * (2 * |t| + 1)
          * Real.exp (-(1 / 200 : ℝ) * Real.exp (((m : ℝ) + θ) / 10))
        = (2 * |t| + 1) * (32 * 10 ^ (40 : ℕ)
          * Real.exp (-(1 / 200 : ℝ) * Real.exp (((m : ℝ) + θ) / 10))) := by ring
      _ ≤ (2 * |t| + 1) * (pntFloorConst θ * Real.exp (-(m : ℝ))) :=
          mul_le_mul_of_nonneg_left hp hτ1
      _ = (2 * |t| + 1) * pntFloorConst θ * Real.exp (-(m : ℝ)) := by ring
  rw [h1, cosGeomConstF, add_mul]
  exact add_le_add le_rfl h2

/-- **`K_t ≤ e^{-2E₀}/100` at the floor `θ`**: once `600e^{2E₀} ≤ 2|t|e^θ` and
`(2|t| + 1)·pntFloorConst θ ≤ e^{-2E₀}/200`. -/
lemma cosGeomConstF_le_of_height {E₀ θ t : ℝ}
    (hlo : 600 * Real.exp (2 * E₀) ≤ 2 * |t| * Real.exp θ)
    (hhiF : (2 * |t| + 1) * pntFloorConst θ ≤ Real.exp (-(2 * E₀)) / 200) :
    cosGeomConstF θ t ≤ Real.exp (-(2 * E₀)) / 100 := by
  have hEp : (0 : ℝ) < Real.exp (2 * E₀) := Real.exp_pos _
  have hEn : (0 : ℝ) < Real.exp (-(2 * E₀)) := Real.exp_pos _
  have hτ : 0 < 2 * |t| * Real.exp θ := by linarith
  have hE : Real.exp (2 * E₀) * Real.exp (-(2 * E₀)) = 1 := by
    rw [← Real.exp_add]; simp
  have h1 : 3 / (2 * |t| * Real.exp θ) ≤ Real.exp (-(2 * E₀)) / 200 := by
    rw [div_le_iff₀ hτ]
    have hmul := mul_le_mul_of_nonneg_left hlo
      (by positivity : (0 : ℝ) ≤ Real.exp (-(2 * E₀)) / 200)
    have h3 : Real.exp (-(2 * E₀)) / 200 * (600 * Real.exp (2 * E₀)) = 3 := by
      rw [show Real.exp (-(2 * E₀)) / 200 * (600 * Real.exp (2 * E₀))
          = 3 * (Real.exp (2 * E₀) * Real.exp (-(2 * E₀))) by ring, hE]
      ring
    linarith
  rw [cosGeomConstF]
  linarith

/-- **The height condition at the floor `104` gives it at every floor `θ ≥ 104`**:
`2|t| + 1 ≤ 5·10²⁵e^{-2E₀}` implies `(2|t| + 1)·pntFloorConst θ ≤ e^{-2E₀}/200`. -/
lemma height_floor_of_height {E₀ θ t : ℝ} (hθ : (104 : ℝ) ≤ θ)
    (hhi : 2 * |t| + 1 ≤ 5 * 10 ^ 25 * Real.exp (-(2 * E₀))) :
    (2 * |t| + 1) * pntFloorConst θ ≤ Real.exp (-(2 * E₀)) / 200 := by
  have hP := pntFloorConst_le hθ
  have h1 : (2 * |t| + 1) * pntFloorConst θ ≤ (2 * |t| + 1) * (1 / 10 ^ 28) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have h2 : (2 * |t| + 1) * (1 / 10 ^ 28) ≤ 5 * 10 ^ 25 * Real.exp (-(2 * E₀)) * (1 / 10 ^ 28) :=
    mul_le_mul_of_nonneg_right hhi (by norm_num)
  have h3 : 5 * 10 ^ 25 * Real.exp (-(2 * E₀)) * (1 / 10 ^ 28) = Real.exp (-(2 * E₀)) / 200 := by
    ring
  linarith

/-! ### The comparison and the Gaussian walk -/

/-- **The sharp window comparison for the Rademacher RMF**: the tilted block walk at `s` against
independent Gaussians of the block's mean and matched variance, with error `e^{-100}`, at every
shift `k ≤ n`.  The Rademacher twin of `RMF.exists_isWindowComparison_steinhaus_of_le_sharp`;
`hcos`, the bound `e^{-2E₀}/100` on every block's oscillatory sum, is the one extra input. -/
theorem exists_isWindowComparison_rademacher_of_le_sharp (hX : IsRademacherPrimeValues X μ)
    {E₀ a Bs θ σ η : ℝ} {n : ℕ} {s : ℂ} {M : ℕ → ℝ} (hE₀ : 0 ≤ E₀) (ha : 0 ≤ a) (hBs : 0 < Bs)
    (hθ : radUpperThreshold E₀ a Bs ≤ θ) (hres : s.re = 1 / 2 + σ) (hσ0 : 0 ≤ σ)
    (hη0 : 0 ≤ η) (hηE : η ≤ E₀) (hσtop : |σ| * Real.log (blockScale θ (n + 1)) ≤ η)
    (hM0 : ∀ m, 0 ≤ M m) (hM : ∀ m, M m ≤ a + Bs * m)
    (hcos : ∀ m, m ≤ n → |∑ p ∈ primeBlockSub θ m,
        Real.cos (2 * s.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
          ≤ Real.exp (-(2 * E₀)) / 100) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ),
      IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
      (∀ m, Q.map (N m) = gaussianReal
        (blockGaussMeanAddAt X μ θ (blockCutoff θ n) n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)
        (blockGaussVarAddAt X μ θ (blockCutoff θ n) n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)) ∧
      (∀ k, k ≤ n → IsWindowComparison
        (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (blockCutoff θ n) s μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
          localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
        (fun m => N (m + k)) (fun m => blockWindow (m + k)) (fun m => M (m + k)) (n - k)
        (Real.exp (-100))) := by
  obtain ⟨-, hθn, hθ16, hθE⟩ := radUpperThreshold_facts hE₀ hθ
  have hσm := hsigma_of_top_of_le hσtop
  have hsc : ∀ m : ℕ, (14 : ℝ) + 2 * η ≤ Real.exp ((m : ℝ) + θ) := fun m => by
    linarith [scale_cond_28_of_le (m := m) hηE hθE]
  have hs : 0 < s.re := re_pos_of_block_of_le hres (hsc 0) (hσm 0 (Nat.zero_le n))
  have hwn : ∀ m : ℕ, ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun m p _ => norm_sq_prime_cpow_neg p hres
  have hV : ∀ m, m ≤ n → 0.98 * Real.exp (-(2 * η))
        ≤ 2 * ((blockMatchedVarAdd X μ (blockCutoff θ n) s (fun p => ((p : ℕ) : ℂ) ^ (-s))
            (primeBlockSub θ m) : ℝ≥0) : ℝ)
      ∧ 2 * ((blockMatchedVarAdd X μ (blockCutoff θ n) s (fun p => ((p : ℕ) : ℂ) ^ (-s))
            (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 1.02 := fun m hm =>
    blockMatchedVarAdd_concrete_sharp hX hs hres hσ0 hηE hθ16 hθE hm (hσm m hm) le_rfl
      (hcos m hm)
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, hcmp⟩ :=
    exists_isWindowComparison_primeBlockSubAdd hX (w := fun p => ((p : ℕ) : ℂ) ^ (-s))
      (W := blockWindow) (M := M)
      (T := fun m => Real.exp (3 * η - 3) * blockTAdd θ m) (q := blockQThr θ (3 / 100))
      (ε := blockEps θ) (E := Real.exp (-100) / 2) hs
      (fun m hm p hp => norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσm m hm) hp)
      (fun m hm p hp => norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσm m hm) hp)
      (fun m _ => mul_pos (Real.exp_pos _)
        (blockTAdd_pos (by rw [log_blockScale]; exact Real.exp_pos _)))
      (fun m _ => blockQThr_pos θ (3 / 100) m)
      (fun m hm h0 => by
        have h := (hV m hm.le).1
        rw [h0] at h
        have := Real.exp_pos (-(2 * η))
        norm_num at h
        linarith)
      (fun m hm => blockThirdConstAdd_mul_sum_le_of_le
        (by linarith [Nat.cast_nonneg (α := ℝ) m]) (hσm m hm.le) (hwn m))
      (fun m hm => blockQThrAdd_le_measure_sharp hX hE₀ ha hBs hθ hm.le hres hσ0 hηE
        (hσm m hm.le) le_rfl (hcos m hm.le) (hM0 m) (hM m))
      (fun m hm => blockNumAdd_le_sharp hE₀ hθn hη0 hηE (by
        have h := (hV m hm.le).1
        have := Real.exp_pos (-(2 * η))
        linarith))
      (fun m _ => blockEps_nonneg θ m) (sum_blockEps_le_exp hθ16 n)
      (by linarith [exp_neg_hundred_le_half])
  refine ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, fun k hk => ?_⟩
  have h := hcmp k hk
  rwa [show (2 : ℝ) * (Real.exp (-100) / 2) = Real.exp (-100) by ring] at h

/-- **The sharp Gaussian walk for the Rademacher RMF**:
`RMF.exists_isWindowComparison_rademacher_of_le_sharp` centred, `G m = N m - θ_m`, with
variances in `[0.49e^{-2η}, 1]` at every index (the dummy indices above `n` keep the value `1`).
The Rademacher twin of `RMF.exists_isGaussianWalk_steinhaus_of_le_sharp`, whose variances lie in
`[0.475e^{-2η}, 9/2]`. -/
theorem exists_isGaussianWalk_rademacher_of_le_sharp (hX : IsRademacherPrimeValues X μ)
    {E₀ a Bs θ σ η : ℝ} {n : ℕ} {s : ℂ} {M : ℕ → ℝ} (hE₀ : 0 ≤ E₀) (ha : 0 ≤ a) (hBs : 0 < Bs)
    (hθ : radUpperThreshold E₀ a Bs ≤ θ) (hres : s.re = 1 / 2 + σ) (hσ0 : 0 ≤ σ)
    (hη0 : 0 ≤ η) (hηE : η ≤ E₀) (hσtop : |σ| * Real.log (blockScale θ (n + 1)) ≤ η)
    (hM0 : ∀ m, 0 ≤ M m) (hM : ∀ m, M m ≤ a + Bs * m)
    (hcos : ∀ m, m ≤ n → |∑ p ∈ primeBlockSub θ m,
        Real.cos (2 * s.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
          ≤ Real.exp (-(2 * E₀)) / 100) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (G N : ℕ → Ω' → ℝ) (v : ℕ → ℝ≥0),
      IsProbabilityMeasure Q ∧ IsGaussianWalk G v Q ∧ (∀ m, Measurable (N m)) ∧
      (∀ m ω, N m ω = G m ω
        + blockGaussMeanAddAt X μ θ (blockCutoff θ n) n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m) ∧
      (∀ i, 0.49 * Real.exp (-(2 * η)) ≤ (v i : ℝ)) ∧ (∀ i, (v i : ℝ) ≤ 1) ∧
      (∀ k, k ≤ n → IsWindowComparison
        (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (blockCutoff θ n) s μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
          localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
        (fun m => N (m + k)) (fun m => blockWindow (m + k)) (fun m => M (m + k)) (n - k)
        (Real.exp (-100))) := by
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, hcmp⟩ :=
    exists_isWindowComparison_rademacher_of_le_sharp hX hE₀ ha hBs hθ hres hσ0 hη0 hηE hσtop
      hM0 hM hcos
  obtain ⟨-, -, hθ16, hθE⟩ := radUpperThreshold_facts hE₀ hθ
  have hσm := hsigma_of_top_of_le hσtop
  have hs : 0 < s.re := re_pos_of_block_of_le hres
    (by linarith [scale_cond_28_of_le (m := 0) hηE hθE]) (hσm 0 (Nat.zero_le n))
  have he1 : Real.exp (-(2 * η)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hv : ∀ i, 0.49 * Real.exp (-(2 * η))
        ≤ ((blockGaussVarAddAt X μ θ (blockCutoff θ n) n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) i
          : ℝ≥0) : ℝ)
      ∧ ((blockGaussVarAddAt X μ θ (blockCutoff θ n) n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) i
          : ℝ≥0) : ℝ) ≤ 1 := by
    intro i
    by_cases hi : i ≤ n
    · rw [blockGaussVarAddAt_of_le hi]
      obtain ⟨h1, h2⟩ := blockMatchedVarAdd_concrete_sharp hX hs hres hσ0 hηE hθ16 hθE hi
        (hσm i hi) le_rfl (hcos i hi)
      constructor <;> linarith
    · rw [blockGaussVarAddAt, if_neg hi]
      push_cast
      constructor <;> linarith
  exact ⟨Ω', mΩ', Q, fun m ω => N m ω
      - blockGaussMeanAddAt X μ θ (blockCutoff θ n) n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m, N,
    blockGaussVarAddAt X μ θ (blockCutoff θ n) n s (fun p => ((p : ℕ) : ℂ) ^ (-s)), hQ,
    isGaussianWalk_sub_const hNm hNi hNlaw, hNm, fun m ω => by ring,
    fun i => (hv i).1, fun i => (hv i).2, hcmp⟩

end RMF
