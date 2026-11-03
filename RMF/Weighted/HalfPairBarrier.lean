/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherRestrictedSecondMoment.Assembly

/-!
# The pair barrier on a mesoscopic window

The second moment of the barriered window integral (Proposition 6.4 of the paper,
`RMF/Weighted/HalfSecondMoment.lean`) needs, in its far
range, the pair-tilted probability that the two walks `log|F(½+σ+ih₁)|` and `log|F(½+σ+ih₂)|`
both stay in their tubes, for heights `h₁ ≠ h₂` in one window `[e^{-(k+1)}, e^{-k}]`.  Here it is
Harper's Proposition 7 for the Rademacher RMF, in the form
`RMF.exists_proposition7_upper_rademacher_of_ratio`, which asks of the heights only that they be
positive, within a factor `3` of each other, and of sum at most `1` — so a window of ratio `e`
qualifies.

This file discharges that theorem's two cosine hypotheses and its envelope condition:

* **the cosine sums** at the doubled heights: `RMF.exists_abs_sum_cos_primeBlockSub_rpow_le`
  bounds block `m`'s sum at frequency `2h` by `K/(2h e^{m+θ})`, which is
  `(2/3)·((3/4)eK)·e^{-m}` at most once the offset has `h e^{θ+1} ≥ 1`, on the window at `θ = k`.
  So `K_d` is absolute, and Proposition 7's constants depend on the slope `Bs` alone;
* **the envelope**: `RMF.boxEnvelope_pair_gen_le_thirtysix`, from the walk's offset alone.

Proposition 7 compares the pair with a correlated Gaussian pair, and needs of the walk's start
`n₁` only `Tsh ≤ |h₁-h₂| e^{n₁}`, i.e. `n₁ ≥ log|h₁-h₂|^{-1} + O(1)`.
-/

open MeasureTheory

namespace RMF

/-- **`hosc` above a height's own scale.**  For `0 < w ≤ 1`, `θ ≥ 3`, `w e^{θ+1} ≥ 1` and
`|σ|·log(blockScale θ (m+1)) ≤ 1`, block `m`'s cosine sum at the doubled height `2w` is at most
`(2/3)·K_d·e^{-m}`, `K_d` absolute.  The mesoscopic twin of
`RMF.exists_abs_sum_cos_primeBlockSub_harper_le`, where Harper's `w ≥ 1/3` plays the part of the
offset condition.  The bound `K/(2w e^{m+θ})` of `RMF.exists_abs_sum_cos_primeBlockSub_rpow_le` is
`(eK/2)e^{-m}/(w e^{θ+1})`; its own condition `(2w)² ≤ e^{m+θ}` is at most `4 ≤ e^{m+θ}`, free at
`θ ≥ 3`. -/
theorem exists_abs_sum_cos_primeBlockSub_le_of_offset :
    ∃ Kd > 0, ∀ (w σ θ : ℝ) (m : ℕ), 0 < w → w ≤ 1 → 3 ≤ θ → 1 ≤ w * Real.exp (θ + 1) →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 →
      |∑ p ∈ primeBlockSub θ m,
          Real.cos (2 * w * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ))) := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_sum_cos_primeBlockSub_rpow_le
  refine ⟨3 / 4 * Real.exp 1 * K, by positivity, fun w σ θ m hw0 hw1 hθ hwe hσ => ?_⟩
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h4 : (4 : ℝ) ≤ Real.exp ((m : ℝ) + θ) := by
    linarith [Real.add_one_le_exp ((m : ℝ) + θ)]
  have hτ2 : (2 * w) ^ 2 ≤ Real.exp ((m : ℝ) + θ) := by nlinarith only [hw0, hw1, h4]
  refine le_trans (hK (2 * w) σ θ m (by linarith) (by linarith) hτ2 hσ) ?_
  have hpos : 0 < 2 * w * Real.exp ((m : ℝ) + θ) := by positivity
  rw [div_le_iff₀ hpos]
  have he : Real.exp 1 * Real.exp (-(m : ℝ)) * Real.exp ((m : ℝ) + θ) = Real.exp (θ + 1) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsplit : 2 / 3 * (3 / 4 * Real.exp 1 * K * Real.exp (-(m : ℝ)))
        * (2 * w * Real.exp ((m : ℝ) + θ))
      = K * (w * (Real.exp 1 * Real.exp (-(m : ℝ)) * Real.exp ((m : ℝ) + θ))) := by ring
  rw [hsplit, he]
  exact le_mul_of_one_le_right hK0.le hwe

/-- **Harper's Proposition 7 for the Rademacher RMF, above the heights' own scale.**  For positive
heights `t₁ ≠ t₂` within a factor `3` of each other with `t₁ + t₂ ≤ 1`, and an offset `θ ≥ 125`
with `t_i e^{θ+1} ≥ 1`, the pair-tilted barrier probability is at most `Cst·min{1, a/√n}²`.
`RMF.exists_proposition7_upper_rademacher_of_ratio`, with its cosine hypotheses discharged by
`RMF.exists_abs_sum_cos_primeBlockSub_le_of_offset` and its envelope condition by
`RMF.boxEnvelope_pair_gen_le_thirtysix`; `Cst` and `Tsh` depend on the slope `Bs` alone. -/
theorem exists_proposition7_upper_rademacher_of_offset (Bs : ℝ) (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
        ∀ (θ σ η a : ℝ) (N r n : ℕ) (s₁ s₂ : ℂ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → blockOffsetThresholdOf Bs ≤ θ + r → r + n ≤ N →
          s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
          0 ≤ η → η ≤ 1 / 10 → |σ| * Real.log (blockScale θ (r + n + 1)) ≤ η →
          0 < s₁.im → 0 < s₂.im → s₁.im + s₂.im ≤ 1 →
          |s₁.im - s₂.im| ≤ 2 * s₁.im → |s₁.im - s₂.im| ≤ 2 * s₂.im → s₁.im ≠ s₂.im →
          1 ≤ s₁.im * Real.exp (θ + 1) → 1 ≤ s₂.im * Real.exp (θ + 1) →
          Tsh ≤ |s₁.im - s₂.im| * Real.exp ((r : ℝ) + θ) →
          max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ a → 4 ≤ n →
          4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
                (blockCutoff θ N) s₁ s₂ μ)
              (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ X (m + r)) n
                (fun j => -a - Bs * j) (fun j => a + j + hf j)
                (fun j => -a - Bs * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (a / Real.sqrt n) ^ 2 := by
  obtain ⟨Kd, hKd0, hosc⟩ := exists_abs_sum_cos_primeBlockSub_le_of_offset
  obtain ⟨Cst, Tsh, hCst, hTsh, H⟩ :=
    exists_proposition7_upper_rademacher_of_ratio Kd Bs hKd0.le hBs
  refine ⟨Cst, Tsh, hCst, hTsh, ?_⟩
  intro Ω' _ X μ hX θ σ η a N r n s₁ s₂ hf hθ hbot hrn hre₁ hre₂ hη0 hη1 hσtop him₁0 him₂0 hν1
    hdif₁ hdif₂ himne he₁ he₂ hTsh' ha hn4 hbig hbig2 hhf
  have hσm : ∀ m, m ≤ r + n → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := fun m hm =>
    le_trans (hsigma_of_top_of_le hσtop m hm) (by linarith)
  have hprop := H Ω' X μ hX θ σ η a N r n s₁ s₂ hf hθ hrn hre₁ hre₂ hη0 hη1 hσtop him₁0 him₂0
    hν1 hdif₁ hdif₂ himne hTsh'
    (fun m hm => hosc s₁.im σ θ m him₁0 (by linarith) (by linarith) he₁ (hσm m hm.le))
    (fun m hm => hosc s₂.im σ θ m him₂0 (by linarith) (by linarith) he₂ (hσm m hm.le))
    (fun m _ => boxEnvelope_pair_gen_le_thirtysix (twenty_le_of_blockSlope_le hBs) hbot m)
    ha hn4 hbig hbig2 hhf
  rwa [barrierEventPair_sumPairAdd_shift_eq] at hprop

/-- **Two heights in one window `[e^{-(k+1)}, e^{-k}]`**, `k ≥ 1`, meet the height hypotheses of
`RMF.exists_proposition7_upper_rademacher_of_offset` at the offset `θ = k`: they are positive,
within a factor `e < 3` of each other, of sum at most `2/e < 1`, and `h e^{k+1} ≥ 1`. -/
lemma window_height_bounds {k h₁ h₂ : ℝ} (hk : 1 ≤ k)
    (h₁l : Real.exp (-(k + 1)) ≤ h₁) (h₁u : h₁ ≤ Real.exp (-k))
    (h₂l : Real.exp (-(k + 1)) ≤ h₂) (h₂u : h₂ ≤ Real.exp (-k)) :
    0 < h₁ ∧ 0 < h₂ ∧ h₁ + h₂ ≤ 1 ∧ |h₁ - h₂| ≤ 2 * h₁ ∧ |h₁ - h₂| ≤ 2 * h₂
      ∧ 1 ≤ h₁ * Real.exp (k + 1) ∧ 1 ≤ h₂ * Real.exp (k + 1) := by
  have hpos : 0 < Real.exp (-(k + 1)) := Real.exp_pos _
  have h₁0 : 0 < h₁ := lt_of_lt_of_le hpos h₁l
  have h₂0 : 0 < h₂ := lt_of_lt_of_le hpos h₂l
  -- `e^{-k} = e·e^{-(k+1)} ≤ 3e^{-(k+1)}`
  have hratio : Real.exp (-k) ≤ 3 * Real.exp (-(k + 1)) := by
    have he : Real.exp (-k) = Real.exp 1 * Real.exp (-(k + 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (by linarith [Real.exp_one_lt_d9]) hpos.le
  -- `e^{-k} ≤ e^{-1} < 1/2`
  have hhalf : Real.exp (-k) ≤ 1 / 2 := by
    have h1 : Real.exp (-k) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    linarith [Real.exp_neg_one_lt_d9]
  have hone : ∀ h : ℝ, Real.exp (-(k + 1)) ≤ h → 1 ≤ h * Real.exp (k + 1) := by
    intro h hl
    have h1 : Real.exp (-(k + 1)) * Real.exp (k + 1) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc (1 : ℝ) = Real.exp (-(k + 1)) * Real.exp (k + 1) := h1.symm
      _ ≤ h * Real.exp (k + 1) := mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
  refine ⟨h₁0, h₂0, by linarith, ?_, ?_, hone h₁ h₁l, hone h₂ h₂l⟩
  · rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> linarith

/-- **Harper's Proposition 7 on a mesoscopic window.**  For heights `h₁ ≠ h₂` in one window
`[e^{-(k+1)}, e^{-k}]`, `k ≥ 125`, and the two walks read from block `r` at offset `k` (the primes
with `k + r < log log p ≤ k + r + n`) past the shift `Tsh ≤ |h₁-h₂| e^{k+r}`, the pair-tilted
probability that both stay in their tubes is at most `Cst·min{1, a/√n}²`, `Cst` and `Tsh`
depending on the slope `Bs` alone.  The far-range input of the second moment
(`RMF/Weighted/HalfSecondMoment.lean`). -/
theorem exists_proposition7_upper_rademacher_window (Bs : ℝ) (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
        ∀ (k : ℕ) (σ η a h₁ h₂ : ℝ) (N r n : ℕ) (hf : ℕ → ℝ),
          125 ≤ k → blockOffsetThresholdOf Bs ≤ (k : ℝ) + r → r + n ≤ N →
          0 ≤ η → η ≤ 1 / 10 → |σ| * Real.log (blockScale (k : ℝ) (r + n + 1)) ≤ η →
          Real.exp (-((k : ℝ) + 1)) ≤ h₁ → h₁ ≤ Real.exp (-(k : ℝ)) →
          Real.exp (-((k : ℝ) + 1)) ≤ h₂ → h₂ ≤ Real.exp (-(k : ℝ)) → h₁ ≠ h₂ →
          Tsh ≤ |h₁ - h₂| * Real.exp ((r : ℝ) + k) →
          max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ a → 4 ≤ n →
          4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
                (blockCutoff (k : ℝ) N) (shiftLine σ h₁) (shiftLine σ h₂) μ)
              (barrierEventPair
                (fun m => blockPairAdd (k : ℝ) (shiftLine σ h₁) (shiftLine σ h₂) X (m + r)) n
                (fun j => -a - Bs * j) (fun j => a + j + hf j)
                (fun j => -a - Bs * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (a / Real.sqrt n) ^ 2 := by
  obtain ⟨Cst, Tsh, hCst, hTsh, H⟩ := exists_proposition7_upper_rademacher_of_offset Bs hBs
  refine ⟨Cst, Tsh, hCst, hTsh, ?_⟩
  intro Ω' _ X μ hX k σ η a h₁ h₂ N r n hf hk hbot hrn hη0 hη1 hσtop h₁l h₁u h₂l h₂u hne hTsh'
    ha hn4 hbig hbig2 hhf
  have hk125 : (125 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  obtain ⟨h₁0, h₂0, hsum, hd₁, hd₂, he₁, he₂⟩ :=
    window_height_bounds (by linarith) h₁l h₁u h₂l h₂u
  exact H Ω' X μ hX k σ η a N r n (shiftLine σ h₁) (shiftLine σ h₂) hf hk125 hbot hrn
    (re_shiftLine σ h₁) (re_shiftLine σ h₂) hη0 hη1 hσtop
    (by simpa only [im_shiftLine] using h₁0) (by simpa only [im_shiftLine] using h₂0)
    (by simpa only [im_shiftLine] using hsum) (by simpa only [im_shiftLine] using hd₁)
    (by simpa only [im_shiftLine] using hd₂) (by simpa only [im_shiftLine] using hne)
    (by simpa only [im_shiftLine] using he₁) (by simpa only [im_shiftLine] using he₂)
    (by simpa only [im_shiftLine] using hTsh') ha hn4 hbig hbig2 hhf

end RMF
