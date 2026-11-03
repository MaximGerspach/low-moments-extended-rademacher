/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.StrongBlockCosine
import RMF.Probability.RademacherBlockShift

/-!
# The barrier chain at Harper's height range

`RMF/NumberTheory/StrongBlockCosine.lean` gives the two consumers of the height condition — the
oscillatory pair and the variance bracket — at `τ² ≤ exp((c/2)·e^{(m+θ)/10})` in place of
`τ² ≤ e^{m+θ}`.  This file carries that condition through the Rademacher block variance bracket,
Harper's Proposition 6 and the free start.  Each `_wide` theorem is its mirror's proof with the
condition swapped and a threshold `m₀` or `ϑ₀` threaded; once `m + θ` passes a `c`-dependent
threshold, the new condition is the weaker hypothesis.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

/-- **The matched block variance satisfies `1/8 ≤ 2·var ≤ 9`**, at Harper's height range.  The
mirror of `RMF.exists_blockMatchedVarAdd_concrete_top`. -/
theorem exists_blockMatchedVarAdd_concrete_top_wide :
    ∃ Tsh c m₀ : ℝ, 0 < Tsh ∧ 0 < c ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ →
      ∀ (θ σ η : ℝ) (m y : ℕ) (s u : ℂ) (w : Nat.Primes → ℂ),
      0 < s.re → s.re = 1 / 2 + σ → u.re = 1 / 2 + σ →
      (9 : ℝ) ≤ (m : ℝ) + θ → m₀ ≤ (m : ℝ) + θ → 0 ≤ θ → 0 ≤ η → η ≤ 1 / 10 →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ η →
      0 < 2 * u.im →
      (2 * u.im) ^ 2 ≤ Real.exp (c / 2 * Real.exp (((m : ℝ) + θ) / 10)) →
      Tsh ≤ 2 * u.im * Real.exp ((m : ℝ) + θ) →
      (∀ p ∈ primeBlockSub θ m, w p = ((p : ℕ) : ℂ) ^ (-u)) →
      primeBlockSub θ m ⊆ primesBelowSub y →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd X μ y s w (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd X μ y s w (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9 := by
  obtain ⟨Tsh, c, m₀, hTsh0, hc, hbr⟩ := exists_sum_re_cpow_neg_sq_primeBlockSub_bounds_wide
  refine ⟨Tsh, c, m₀, hTsh0, hc, ?_⟩
  intro Ω _ X μ hX θ σ η m y s u w hs hres hu hmθ hm0 hθ hη hη' hσ hτ hτ2 hTsh hwv hB
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hσ1 : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := by linarith
  -- the weights, and the tilt radius, have the same modulus on the block
  have hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := fun p hp => by
    rw [hwv p hp]
    exact norm_sq_prime_cpow_neg p hu
  have han : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := fun p _ =>
    norm_sq_prime_cpow_neg p hres
  have hw5 : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5 := fun p hp => by
    rw [hwv p hp]
    exact norm_prime_cpow_le_fifth hm3 hu hσ1 hp
  -- the error is at most `52/1000`
  have hcube := sum_norm_cube_primeBlockSub_le_of_nine hmθ hσ1 hwn
  have hterm : ∀ p ∈ primeBlockSub θ m,
      42 * ‖w p‖ ^ 3 + 48 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 * ‖w p‖ ^ 2
        ≤ 52 * ‖w p‖ ^ 3 := fun p hp => by
    have heq : ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ‖w p‖ ^ 2 := by rw [han p hp, hwn p hp]
    have h5 := hw5 p hp
    have h0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
    rw [heq]
    nlinarith [mul_nonneg (mul_nonneg h0 h0) h0, pow_nonneg h0 3]
  have herr : (∑ p ∈ primeBlockSub θ m,
      (42 * ‖w p‖ ^ 3 + 48 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 * ‖w p‖ ^ 2)) ≤ 52 / 1000 := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    linarith
  -- the main term, in the block's own variables
  have hsum : (∑ p ∈ primeBlockSub θ m, (w p).re ^ 2)
      = ∑ p ∈ primeBlockSub θ m, ((((p : ℕ) : ℂ)) ^ (-u)).re ^ 2 :=
    Finset.sum_congr rfl fun p hp => by rw [hwv p hp]
  obtain ⟨hlo, hhi⟩ := hbr θ σ η m u hu hmθ hm0 hθ hη hη' hσ hτ hτ2 hTsh
  have hgap := abs_coe_blockMatchedVarAdd_sub_le hX y hs hB hw5
  rw [abs_le] at hgap
  rw [hsum] at hgap
  constructor <;> linarith [hgap.1, hgap.2]

/-- **The block variance bracket at Harper's offsets**, at Harper's height range.  The mirror of
`RMF.exists_blockMatchedVarAdd_concrete_of_offset_top`. -/
theorem exists_blockMatchedVarAdd_concrete_of_offset_top_wide :
    ∃ Tsh c m₀ : ℝ, 0 < Tsh ∧ 0 < c ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ →
      ∀ (θ σ η : ℝ) (t : ℕ → ℝ) (m y : ℕ) (s : ℂ),
      0 < s.re → s.re = 1 / 2 + σ →
      (9 : ℝ) ≤ (m : ℝ) + θ → m₀ ≤ (m : ℝ) + θ → 0 ≤ θ → 0 ≤ η → η ≤ 1 / 10 →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ η →
      0 < 2 * (s.im + t m) →
      (2 * (s.im + t m)) ^ 2 ≤ Real.exp (c / 2 * Real.exp (((m : ℝ) + θ) / 10)) →
      Tsh ≤ 2 * (s.im + t m) * Real.exp ((m : ℝ) + θ) →
      primeBlockSub θ m ⊆ primesBelowSub y →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd X μ y s (blockOffsetWeight θ t s)
          (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd X μ y s (blockOffsetWeight θ t s)
          (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9 := by
  obtain ⟨Tsh, c, m₀, hTsh0, hc, H⟩ := exists_blockMatchedVarAdd_concrete_top_wide
  refine ⟨Tsh, c, m₀, hTsh0, hc, ?_⟩
  intro Ω _ X μ hX θ σ η t m y s hs hres hmθ hm0 hθ hη hη' hσ hτ hτ2 hTsh hB
  have hre : (s + (t m : ℂ) * Complex.I).re = 1 / 2 + σ := by
    simp [hres]
  have him : (s + (t m : ℂ) * Complex.I).im = s.im + t m := by
    simp
  refine H _ X μ hX θ σ η m y s (s + (t m : ℂ) * Complex.I) (blockOffsetWeight θ t s)
    hs hres hre hmθ hm0 hθ
    hη hη' hσ (by rw [him]; exact hτ) (by rw [him]; exact hτ2) (by rw [him]; exact hTsh)
    (fun p hp => blockOffsetWeight_eq_of_mem hp) hB

set_option maxHeartbeats 400000 in
-- as in the mirror: this proof applies BOTH Proposition 6 halves, and with the tilt cutoff free
-- neither application has the cutoff to pin its implicit indices early
/-- **Harper's Proposition 6 at his offsets and height range**, both bounds, with the tilt cutoff
free.  The mirror of `RMF.exists_const_proposition5_rademacher_of_offset_of_cutoff`.  Its inputs
are `RMF.exists_blockMatchedVarAdd_concrete_of_offset_top_wide` and
`RMF.exists_abs_sum_cos_primeBlockSub_rpow_le_wide`; `c` is the smaller of their two rates and
`ϑ₀` absorbs both of their thresholds. -/
theorem exists_const_proposition5_rademacher_of_offset_of_cutoff_wide :
    ∃ (ϑ₀ : ℝ) (n₀ : ℕ) (a₀ α A B Tsh c : ℝ),
      0 < α ∧ 0 < A ∧ 20 ≤ B ∧ 0 < Tsh ∧ 0 < c ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (ϑ σ a : ℝ) (n y : ℕ) (s : ℂ) (t hf : ℕ → ℝ),
          ϑ₀ ≤ ϑ → blockCutoff ϑ n ≤ y → s.re = 1 / 2 + σ →
          |σ| * Real.log (blockScale ϑ (n + 1)) ≤ 1 / 10 →
          (∀ m, m < n →
            |t m| * Real.log (blockScale ϑ (m + 1)) ≤ ((m : ℝ) + 1) ^ (-((2 : ℝ) / 3))) →
          (∀ m, m ≤ n →
            0 < 2 * s.im + t m
              ∧ (2 * s.im + t m) ^ 2 ≤ Real.exp (c / 2 * Real.exp (ϑ / 10))
              ∧ Tsh ≤ (2 * s.im + t m) * Real.exp ϑ
              ∧ 0 < 2 * (s.im + t m)
              ∧ (2 * (s.im + t m)) ^ 2 ≤ Real.exp (c / 2 * Real.exp (ϑ / 10))
              ∧ Tsh ≤ 2 * (s.im + t m) * Real.exp ϑ) →
          a₀ ≤ a → n₀ ≤ n →
          (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
            α * min 1 (a / Real.sqrt n)
                ≤ ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω)
                      (y) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLogAdd (blockOffsetWeight ϑ t s p) (Y (p : ℕ) ω)) n
                      (fun j => -a - B * j) (fun j => a + j + hf j))).toReal
              ∧ ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω)
                      (y) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLogAdd (blockOffsetWeight ϑ t s p) (Y (p : ℕ) ω)) n
                      (fun j => -a - B * j) (fun j => a + j + hf j))).toReal
                  ≤ A * min 1 (a / Real.sqrt n) := by
  obtain ⟨n₀, hn₀⟩ := exists_blockSizeThreshold
  obtain ⟨Tsh, cV, mV, hTsh0, hcV, HV⟩ := exists_blockMatchedVarAdd_concrete_of_offset_top_wide
  obtain ⟨K, cK, mK, hK0, hcK, HK⟩ := exists_abs_sum_cos_primeBlockSub_rpow_le_wide
  obtain ⟨c, hccV, hccK, hc0⟩ : ∃ c : ℝ, c ≤ cV ∧ c ≤ cK ∧ 0 < c :=
    ⟨min cV cK, min_le_left _ _, min_le_right _ _, lt_min hcV hcK⟩
  set Kd : ℝ := 3 / 2 * (K / Tsh) with hKddef
  have hKd : (0 : ℝ) ≤ Kd := by
    rw [hKddef]
    positivity
  have hB0 : (0 : ℝ) < blockSlopeAdd Kd 125 := blockSlopeAdd_pos hKd
  have hB20 : (20 : ℝ) ≤ blockSlopeAdd Kd 125 := twenty_le_blockSlopeAdd hKd
  have hdc0 : (0 : ℝ) ≤ driftConstAdd Kd 125 := driftConstAdd_nonneg hKd
  have hRC1 : (1 : ℝ) ≤ result1Const (1 / 16) (9 / 2) := one_le_result1Const _ _
  have h2s : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max (blockOffsetThresholdAdd Kd) (max mV mK), n₀,
    max (max 1 (result2Threshold (1 / 16) (9 / 2) + 2 + driftConstAdd Kd 125))
      (max (4 + 2 * driftConstAdd Kd 125) (max 1 (result1Threshold (1 / 16) (9 / 2)))),
    result1LowerConst (1 / 16) (9 / 2) / 2 / 4,
    2 * result1Const (1 / 16) (9 / 2)
      * (Real.sqrt 2 * (15 + blockSlopeAdd Kd 125 + 2 * driftConstAdd Kd 125 + 10 * Real.log 2)),
    blockSlopeAdd Kd 125, Tsh, c, ?_, ?_, hB20, hTsh0, hc0, ?_⟩
  · have hlc : (0 : ℝ) < result1LowerConst (1 / 16) (9 / 2) :=
      result1LowerConst_pos (by norm_num) (by norm_num)
    linarith
  · have hp1 : (0 : ℝ) < 2 * result1Const (1 / 16) (9 / 2) := by linarith
    have hin : (0 : ℝ)
        < 15 + blockSlopeAdd Kd 125 + 2 * driftConstAdd Kd 125 + 10 * Real.log 2 := by
      linarith
    exact mul_pos hp1 (by nlinarith [h2s, hin])
  intro Ω' _ Y ν hY ϑ σ a n y s t hf hϑ hy hres hσtop ht hfreq ha hn hhf
  have hϑb : blockOffsetThresholdAdd Kd ≤ ϑ := le_trans (le_max_left _ _) hϑ
  have hmV : mV ≤ ϑ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hϑ
  have hmK : mK ≤ ϑ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hϑ
  have h125 : (125 : ℝ) ≤ ϑ := le_trans (le_blockOffsetThresholdAdd Kd) hϑb
  have hϑ0 : (0 : ℝ) ≤ ϑ := by linarith
  obtain ⟨hn4, hbig, hbig2⟩ := hn₀ n hn
  have hn1 : 1 ≤ n := by omega
  have hσtop1 : |σ| * Real.log (blockScale ϑ (n + 1)) ≤ 1 := by linarith
  have hσm : ∀ m : ℕ, m ≤ n → |σ| * Real.log (blockScale ϑ (m + 1)) ≤ 1 / 10 := by
    intro m hmn
    have h := sigma_le_mul_exp_sub ϑ σ (1 / 10) hσtop (m := m) (n := n)
    have hle : Real.exp ((m : ℝ) - n) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    nlinarith [h, hle, Real.exp_pos ((m : ℝ) - n)]
  have hm3' : (3 : ℝ) ≤ ((0 : ℕ) : ℝ) + ϑ := by
    push_cast
    linarith
  have hweak : ∀ d : ℝ, c ≤ d → ∀ m : ℕ,
      Real.exp (c / 2 * Real.exp (ϑ / 10))
        ≤ Real.exp (d / 2 * Real.exp (((m : ℝ) + ϑ) / 10)) := by
    intro d hd m
    refine Real.exp_le_exp.2 ?_
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hmono : Real.exp (ϑ / 10) ≤ Real.exp (((m : ℝ) + ϑ) / 10) :=
      Real.exp_le_exp.2 (by linarith)
    have h1 : c / 2 * Real.exp (ϑ / 10) ≤ d / 2 * Real.exp (ϑ / 10) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    have h2 : d / 2 * Real.exp (ϑ / 10) ≤ d / 2 * Real.exp (((m : ℝ) + ϑ) / 10) :=
      mul_le_mul_of_nonneg_left hmono (by linarith)
    linarith
  have hs : 0 < s.re := re_pos_of_block hm3' hres (hsigma_of_top hσtop1 0 (Nat.zero_le n))
  -- the variance bracket, at every block
  have hV : ∀ m, m ≤ n →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd Y ν (y) s (blockOffsetWeight ϑ t s)
          (primeBlockSub ϑ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd Y ν (y) s (blockOffsetWeight ϑ t s)
          (primeBlockSub ϑ m) : ℝ≥0) : ℝ) ≤ 9 := by
    intro m hmn
    obtain ⟨-, -, -, hτ0, hτsq, hT⟩ := hfreq m hmn
    have hm9 : (9 : ℝ) ≤ (m : ℝ) + ϑ := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hexp : Real.exp ϑ ≤ Real.exp ((m : ℝ) + ϑ) := by
      refine Real.exp_le_exp.2 ?_
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    refine HV Ω' Y ν hY ϑ σ (1 / 10) t m (y) s hs hres hm9 (by linarith) hϑ0
      (by norm_num) le_rfl (hσm m hmn) hτ0 (le_trans hτsq (hweak cV hccV m)) ?_
      (primeBlockSub_subset_primesBelowSub_of_le hmn hy)
    exact le_trans hT (mul_le_mul_of_nonneg_left hexp (by linarith))
  -- the oscillatory pair, geometric under the height threshold
  have hosc : ∀ m, m < n →
      |∑ p ∈ primeBlockSub ϑ m,
          Real.cos ((2 * s.im + t m) * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        + |∑ p ∈ primeBlockSub ϑ m,
            Real.cos (2 * (s.im + t m) * Real.log ((p : ℕ) : ℝ))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)| / 2
        ≤ Kd * Real.exp (-(m : ℝ)) := by
    intro m hmn
    obtain ⟨hτ10, hτ1sq, hT1, hτ20, hτ2sq, hT2⟩ := hfreq m hmn.le
    have hσ1 : |σ| * Real.log (blockScale ϑ (m + 1)) ≤ 1 := by
      linarith [hσm m hmn.le]
    have hexp : Real.exp ϑ ≤ Real.exp ((m : ℝ) + ϑ) := by
      refine Real.exp_le_exp.2 ?_
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hA := HK (2 * s.im + t m) σ ϑ m hτ10 hϑ0 (by linarith)
      (le_trans hτ1sq (hweak cK hccK m)) hσ1
    have hC := HK (2 * (s.im + t m)) σ ϑ m hτ20 hϑ0 (by linarith)
      (le_trans hτ2sq (hweak cK hccK m)) hσ1
    exact abs_sum_cos_pair_le_of_threshold hK0 hTsh0 hA hC hτ10 hτ20 hT1 hT2
  -- Everything the strengthened height condition needed is spent; drop it, so the arithmetic
  -- below faces the same context its mirror does.
  clear hfreq HV HK hweak hccV hccK hcV hcK hmV hmK hϑ hc0
  clear cV cK mV mK c
  -- the envelope
  set M : ℕ → ℝ := fun j =>
    (3 + blockSlopeAdd Kd 125) * min a (j : ℝ) + blockSlopeAdd Kd 125 * (j : ℝ) + (j : ℝ)
      + 20 * Real.log (j : ℝ) with hMdef
  set M' : ℕ → ℝ := fun m => M m + M (m + 1) + blockWindow m with hM'def
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hlogn : ∀ j : ℕ, (0 : ℝ) ≤ Real.log (j : ℝ) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hj)
  have henvc : ∀ m, m < n →
      M' m + blockWindow m + 21
        ≤ 1 / 40 * Real.sqrt (Real.log (blockScale ϑ (m + 1))) := by
    intro m _
    have hW0 : (0 : ℝ) < blockWindow m := blockWindow_pos m
    have hW : blockWindow m ≤ 1 := by
      rw [blockWindow, div_le_one (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hlogm : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 1) := by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp
      · exact Real.log_le_log (by exact_mod_cast hm0) (by linarith)
    have hminmono : min a (m : ℝ) ≤ min a ((m : ℝ) + 1) := min_le_min le_rfl (by linarith)
    have hmm : (3 + blockSlopeAdd Kd 125) * min a (m : ℝ)
        ≤ (3 + blockSlopeAdd Kd 125) * min a ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hminmono (by linarith)
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have hbud := envelope_of_le_add (Kd := Kd) (ϑ := ϑ) (a := a) (m := m) hKd hϑb ha1
    simp only [hM'def, hMdef, hcast]
    nlinarith [hbud, hlogm, hW, hW0, hmm]
  have hM0 : ∀ j, 0 ≤ M j := by
    intro j
    have hmin : (0 : ℝ) ≤ min a (j : ℝ) := le_min ha0 (Nat.cast_nonneg j)
    simp only [hMdef]
    nlinarith [hlogn j, Nat.cast_nonneg (α := ℝ) j, hB0, ha0, hmin]
  have hMcap : ∀ j, 1 ≤ j → j ≤ n →
      blockSlopeAdd Kd 125 * j ≤ M j ∧
        blockSlopeAdd Kd 125 * j + j + hf j ≤ M j := by
    intro j hj1 hjn
    have habs := abs_le.1 (hhf j hj1 hjn)
    have hmin : (0 : ℝ) ≤ min a (j : ℝ) := le_min ha0 (Nat.cast_nonneg j)
    simp only [hMdef]
    exact ⟨by nlinarith [hlogn j, ha0, hB0, hmin],
      by nlinarith [habs.2, hlogn j, ha0, hB0, hmin]⟩
  have hMup : ∀ j : ℕ, a < (j : ℝ) → j ≤ n →
      (3 + blockSlopeAdd Kd 125) * a + blockSlopeAdd Kd 125 * j + j
        + 20 * Real.log j ≤ M j := by
    intro j hj _
    have hmin : min a (j : ℝ) = a := min_eq_left hj.le
    simp only [hMdef, hmin]
    exact le_rfl
  have hMM : ∀ m, m < n → M m + M (m + 1) + blockWindow m ≤ M' m := by
    intro m _
    simp only [hM'def]
    exact le_rfl
  have hdc : driftConstAdd Kd ϑ ≤ driftConstAdd Kd 125 := driftConstAdd_antitone h125
  have halow : max (max 1 (result2Threshold (1 / 16) (9 / 2) + 2 + driftConstAdd Kd ϑ))
      (4 + 2 * driftConstAdd Kd ϑ) ≤ a := by
    refine max_le (max_le ?_ ?_) ?_
    · exact ha1
    · refine le_trans ?_ ha
      refine le_trans ?_ (le_max_left _ _)
      refine le_trans ?_ (le_max_right _ _)
      linarith
    · refine le_trans ?_ ha
      refine le_trans ?_ (le_max_right _ _)
      refine le_trans ?_ (le_max_left _ _)
      linarith
  have haup : max 1 (result1Threshold (1 / 16) (9 / 2)) ≤ a :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ha
  refine ⟨proposition5_lower_rademacher_of_offset_of_cutoff hY h125 hy hres hσtop1 ht hKd
      hosc hV henvc
      hM0 hMcap hMM halow hn1 hbig hbig2 hhf, ?_⟩
  refine le_trans (proposition5_upper_rademacher_of_offset_of_cutoff hY h125 hy hres hσtop1
    ht hKd hosc hV henvc hM0 hMup hMM haup hn4 hbig hbig2 hhf) ?_
  have hmin0 : (0 : ℝ) ≤ min 1 (a / Real.sqrt n) := le_min zero_le_one (by positivity)
  refine mul_le_mul_of_nonneg_right ?_ hmin0
  have hstep : 15 + blockSlopeAdd Kd 125 + 2 * driftConstAdd Kd ϑ + 10 * Real.log 2
      ≤ 15 + blockSlopeAdd Kd 125 + 2 * driftConstAdd Kd 125 + 10 * Real.log 2 := by linarith
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep (by linarith))
    (by linarith)

/-- **Harper's Proposition 6 at zero offsets, at his height range.**  The mirror of
`RMF.exists_const_proposition5_rademacher_of_cutoff`.  At `t ≡ 0` the height condition reads
`(2·Im s)² ≤ exp((c/2)·exp(ϑ/10))`, in place of the mirror's `(2·Im s)² ≤ exp ϑ`. -/
theorem exists_const_proposition5_rademacher_of_cutoff_wide :
    ∃ (ϑ₀ : ℝ) (n₀ : ℕ) (a₀ α A B Tsh c : ℝ),
      0 < α ∧ 0 < A ∧ 20 ≤ B ∧ 0 < Tsh ∧ 0 < c ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (ϑ σ a : ℝ) (n y : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          ϑ₀ ≤ ϑ → blockCutoff ϑ n ≤ y → s.re = 1 / 2 + σ →
          |σ| * Real.log (blockScale ϑ (n + 1)) ≤ 1 / 10 →
          0 < 2 * s.im →
          (2 * s.im) ^ 2 ≤ Real.exp (c / 2 * Real.exp (ϑ / 10)) →
          Tsh ≤ 2 * s.im * Real.exp ϑ →
          a₀ ≤ a → n₀ ≤ n →
          (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
            α * min 1 (a / Real.sqrt n)
                ≤ ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω)
                      (y) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) n
                      (fun j => -a - B * j) (fun j => a + j + hf j))).toReal
              ∧ ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω)
                      (y) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) n
                      (fun j => -a - B * j) (fun j => a + j + hf j))).toReal
                  ≤ A * min 1 (a / Real.sqrt n) := by
  obtain ⟨ϑ₀, n₀, a₀, α, A, B, Tsh, c, hα, hA, hB, hTsh, hc, H⟩ :=
    exists_const_proposition5_rademacher_of_offset_of_cutoff_wide
  refine ⟨ϑ₀, n₀, a₀, α, A, B, Tsh, c, hα, hA, hB, hTsh, hc, ?_⟩
  intro Ω' _ Y ν hY ϑ σ a n y s hf hϑ hy hres hσtop hτ0 hτsq hT ha hn hhf
  have h := H Ω' Y ν hY ϑ σ a n y s (fun _ => 0) hf hϑ hy hres hσtop
    (fun m _ => by
      simpa using Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1) _)
    (fun m _ => by
      exact ⟨by simpa using hτ0, by simpa using hτsq, by simpa using hT,
        by simpa using hτ0, by simpa using hτsq, by simpa using hT⟩)
    ha hn hhf
  simpa only [blockOffsetWeight_zero] using h

/-- **The free start, at Harper's height range.**  The mirror of
`RMF.exists_const_freeStart_barrier_le_rademacher_of_cutoff`.  The offset shift `ϑ ↦ ϑ + r` only
weakens the height condition, since `c > 0` and `r ≥ 0`. -/
theorem exists_const_freeStart_barrier_le_rademacher_of_cutoff_wide :
    ∃ (ϑ₀ : ℝ) (n₀ : ℕ) (a₀ C B Tsh c : ℝ), 0 < C ∧ 20 ≤ B ∧ 0 < Tsh ∧ 0 < c ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (ϑ σ a : ℝ) (n r y : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          ϑ₀ ≤ ϑ → blockCutoff ϑ n ≤ y → s.re = 1 / 2 + σ → 0 < s.re →
          |σ| * Real.log (blockScale ϑ (n + 1)) ≤ 1 / 10 →
          0 < 2 * s.im →
          (2 * s.im) ^ 2 ≤ Real.exp (c / 2 * Real.exp (ϑ / 10)) →
          Tsh ≤ 2 * s.im * Real.exp ϑ →
          a₀ ≤ a → 1 ≤ a → n₀ ≤ n - r → 1 ≤ r → r ≤ n → (r : ℝ) ≤ a / 4 + 1 →
          (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω)
                (y) s ν)
                {ω | ∀ j, r ≤ j → j ≤ n →
                  walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - B * (j : ℝ)) (a + (j : ℝ) + hf j)}).toReal
              ≤ C * min 1 (a / Real.sqrt ((n : ℝ) - r)) := by
  obtain ⟨ϑ₀, n₀, a₀, α, A, B, Tsh, c, hα, hA, hB, hTsh, hcpos, H⟩ :=
    exists_const_proposition5_rademacher_of_cutoff_wide
  have hB0 : (0 : ℝ) < B := by linarith only [hB]
  refine ⟨ϑ₀, n₀, a₀, A * (29 + 2 * B), B, Tsh, c, by positivity, hB, hTsh, hcpos, ?_⟩
  intro Ω' _ Y ν hY ϑ σ a n r y s hf hϑ hy hres hspos hσ hτ0 hτsq hT ha₀ ha1 hn₀ hr1 hrn hra hhf
  haveI := isProbabilityMeasure_tiltedMeasure_rademacher hY (y) hspos
  set a' := shiftedHeight a B hf r with ha'def
  have hc : (0 : ℝ) ≤ B := by linarith only [hB]
  have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hscale : blockScale (ϑ + r) (n - r + 1) = blockScale ϑ (n + 1) := by
    rw [← blockScale_add, show n - r + 1 + r = n + 1 from by omega]
  have ha'0 : a ≤ a' := by
    rw [ha'def, shiftedHeight]
    have h1 : (0 : ℝ) ≤ (B + 1) * (r : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ |hf r| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ Real.log (1 + (r : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  -- the height conditions weaken at the shifted offset, since `e^ϑ ≤ e^{ϑ+r}` — and, for the
  -- strengthened one, since `(c/2)e^{ϑ/10} ≤ (c/2)e^{(ϑ+r)/10}` as well
  have hexpr : Real.exp ϑ ≤ Real.exp (ϑ + (r : ℝ)) := Real.exp_le_exp.2 (by linarith)
  have hexpc : Real.exp (c / 2 * Real.exp (ϑ / 10))
      ≤ Real.exp (c / 2 * Real.exp ((ϑ + (r : ℝ)) / 10)) :=
    Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by linarith))
  have hp1 : ϑ₀ ≤ ϑ + (r : ℝ) := by linarith
  have hp2 : |σ| * Real.log (blockScale (ϑ + r) (n - r + 1)) ≤ 1 / 10 := by
    rw [hscale]; exact hσ
  have hp3 : a₀ ≤ a' := by linarith
  have hpsq : (2 * s.im) ^ 2 ≤ Real.exp (c / 2 * Real.exp ((ϑ + (r : ℝ)) / 10)) :=
    le_trans hτsq hexpc
  have hpT : Tsh ≤ 2 * s.im * Real.exp (ϑ + (r : ℝ)) :=
    le_trans hT (mul_le_mul_of_nonneg_left hexpr (by linarith))
  have hp4 : ∀ j : ℕ, 1 ≤ j → j ≤ n - r →
      |(fun m : ℕ => 10 * Real.log m) j| ≤ 10 * Real.log j := by
    intro j hj1 _
    have hl : (0 : ℝ) ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj1)
    simp only
    rw [abs_of_nonneg (by linarith)]
  have hy' : blockCutoff (ϑ + r) (n - r) ≤ y :=
    le_of_eq_of_le (blockCutoff_add hrn) hy
  have hP5 := (H Ω' Y ν hY (ϑ + r) σ a' (n - r) y s (fun m => 10 * Real.log m)
    hp1 hy' hres hp2 hτ0 hpsq hpT hp3 hn₀ hp4).2
  rw [Nat.cast_sub hrn] at hP5
  -- the shifted walk is the block walk at offset `ϑ + r`
  have hXshift : (fun m (ω : Ω') => ∑ p ∈ primeBlockSub ϑ (m + r),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
      = fun m ω => ∑ p ∈ primeBlockSub (ϑ + r) m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω) := by
    funext m
    rw [primeBlockSub_add]
  have hsub := freeStart_subset_barrierEvent (X := fun m (ω : Ω') => ∑ p ∈ primeBlockSub ϑ m,
    localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) (a := a) (c := B) (hf := hf) hrn hhf
  rw [hXshift] at hsub
  have hmono := measure_mono (μ := tiltedMeasure
    (fun ω => squarefreeExtension fun p => Y p ω) (y) s ν) hsub
  refine le_trans (le_trans (ENNReal.toReal_mono (measure_ne_top _ _) hmono) hP5) ?_
  -- the widened height is `O(a)`, and `min 1 (K x) ≤ K · min 1 x` for `K ≥ 1`
  have hheight : a' ≤ (29 + 2 * B) * a :=
    shiftedHeight_le ha1 hc hr1 hra (hhf r hr1 hrn)
  have hK : (1 : ℝ) ≤ 29 + 2 * B := by linarith
  have hsq : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) - r) := Real.sqrt_nonneg _
  have hdiv : a' / Real.sqrt ((n : ℝ) - r)
      ≤ (29 + 2 * B) * (a / Real.sqrt ((n : ℝ) - r)) := by
    rw [← mul_div_assoc]
    gcongr
  have h1 := min_one_le_mul_min_one hK hdiv
  calc A * min 1 (a' / Real.sqrt ((n : ℝ) - r))
      ≤ A * ((29 + 2 * B) * min 1 (a / Real.sqrt ((n : ℝ) - r))) :=
        mul_le_mul_of_nonneg_left h1 hA.le
    _ = A * (29 + 2 * B) * min 1 (a / Real.sqrt ((n : ℝ) - r)) := by ring

end RMF
