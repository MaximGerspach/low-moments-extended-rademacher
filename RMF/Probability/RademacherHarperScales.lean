/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.HarperScales
import RMF.Probability.RademacherBlockShift

/-!
# The free start at Harper's scales, for the Rademacher random multiplicative function

`Probability/HarperScales.lean` restates the block-level results in Harper's own variables: the
offset is `RMF.harperOffset D x` and the block count is `RMF.harperBlockCount D x`, both read off
`x` rather than supplied.  Every scale lemma it uses — `RMF.log_blockScale_harperOffset_top`,
`RMF.blockCutoff_harperOffset`, `RMF.le_harperOffset_of_le`,
`RMF.exists_harperThreshold_of_blockCount` — is law-free and reused verbatim.

This file proves the Rademacher free-start barrier bound at Harper's scales, with the offset as
an input and the top blocks dropped.

## The height conditions stay free of `x`

`RMF.harperOffset D x = \{log log x\} + D - 1` lies in `[D-1, D)` — the fractional part moves with
`x` but the offset is **bounded**.  So `(2 Im s)² ≤ e^{ϑ}` and `Tsh ≤ 2 Im s · e^{ϑ}` at
`ϑ = harperOffset D x` are, up to that bounded part, conditions on `Im s` and `D` alone.  That is
exactly Harper's `D ≥ max\{log(1/|t|), 2 log log(1+|t|)\} + (B+1)` (Harper, arXiv:1703.06654,
Proposition 6), and it is why they can be stated here without dragging `x` into them.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RMF

/-- **The tilt at a dropped top index, in this branch's `1/10` spelling.**
`RMF.sigma_le_one_of_drop` is the same statement with `1` in place of `1/10`; the Rademacher
variance bracket needs the tenth, so the drop has to cover `10K` rather than `K`.  Because
`RMF.blockScale θ j = e^{e^{j+θ}}`, dropping `r` indices **divides** the tilt scale by `e^r`, so an
absolute `K` is covered by `r = ⌈log(10K)⌉` blocks. -/
lemma sigma_le_tenth_of_drop {θ σ K : ℝ} {n r : ℕ} (hK : 10 * K ≤ Real.exp r) (hrn : r ≤ n)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ K) :
    |σ| * Real.log (blockScale θ (n - r + 1)) ≤ 1 / 10 := by
  refine le_trans (sigma_le_mul_exp_sub θ σ K hσ) ?_
  have hcast : ((n - r : ℕ) : ℝ) = (n : ℝ) - (r : ℝ) := Nat.cast_sub hrn
  rw [hcast, show (n : ℝ) - (r : ℝ) - (n : ℝ) = -(r : ℝ) by ring, Real.exp_neg,
    inv_eq_one_div, mul_one_div, div_le_iff₀ (Real.exp_pos _)]
  linarith

/-! ### The free start with the offset as an input

The chaos wrapper applies the free start at `RMF.harperDt D₀ h`, which **varies with the
height**, so `D` is an input above a threshold `D₀` rather than existentially fixed, and
`(D : ℝ) ≤ log log x` is a hypothesis.  `RMF.harper_block_count_of_height` supplies
`D₀ ≤ harperDt D₀ h` and `(harperDt D₀ h : ℝ) ≤ log log x` uniformly for every height with
`log(1/|h|) ≤ (log log x)/3`. -/

/-- **The free-start barrier bound at Harper's scales, with the offset as an input and a drop.**
The tilted probability that the walk stays in the tube on `[r, N - d]`, `N = harperBlockCount D x`,
is at most `C·min\{1, a/√(N - d - r)\}`, for every `D` above the absolute threshold `D₀`; so `D`
may depend on the height, as `RMF.harperDt D₀ h` does in the chaos wrapper. -/
theorem exists_const_freeStart_barrier_harper_le_rademacher_of_offset_of_drop :
    ∃ (D₀ n₀ : ℕ) (x₀ a₀ C B Tsh : ℝ), 4 ≤ D₀ ∧ 0 < C ∧ 20 ≤ B ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (x σ a η : ℝ) (D r d : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → D₀ ≤ D → (D : ℝ) ≤ Real.log (Real.log x) →
          s.re = 1 / 2 + σ → 0 < s.re →
          |σ| * Real.log x ≤ η → 10 * η ≤ Real.exp d →
          0 < 2 * s.im → (2 * s.im) ^ 2 ≤ Real.exp (harperOffset D x) →
          Tsh ≤ 2 * s.im * Real.exp (harperOffset D x) →
          a₀ ≤ a → 1 ≤ a →
          1 ≤ r → r ≤ harperBlockCount D x - d → (r : ℝ) ≤ a / 4 + 1 →
          n₀ ≤ harperBlockCount D x - d - r →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1) s ν)
                {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x - d →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - B * (j : ℝ)) (a + (j : ℝ) + hf j)}).toReal
              ≤ C * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ) - r)) := by
  obtain ⟨ϑ₀, n₀, a₀, C, B, Tsh, hC, hB, hTsh, H⟩ :=
    exists_const_freeStart_barrier_le_rademacher_of_cutoff
  refine ⟨⌈ϑ₀⌉₊ + 5, n₀, Real.exp 3, a₀, C, B, Tsh, by omega, hC, hB, hTsh, ?_⟩
  intro Ω' _ Y ν hY x σ a η D r d s hf hx hD₀ hDlog hres hspos hσ hη hτ0 hτsq hT ha ha1 hr1
    hrn hra hn₀ hhf
  have hx1 : 1 < x := by
    have h1 : (1 : ℝ) < Real.exp 3 := by
      linarith [Real.add_one_le_exp (3 : ℝ)]
    linarith
  have hϑ : ϑ₀ ≤ harperOffset D x := by
    refine le_harperOffset_of_le x ?_
    have hD₀' : ((⌈ϑ₀⌉₊ + 5 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD₀
    have := le_ceil_add_sub_one ϑ₀ 5 (by norm_num)
    linarith
  have hdc : d ≤ harperBlockCount D x := by omega
  have hσ' : |σ| * Real.log (blockScale (harperOffset D x)
      (harperBlockCount D x - d + 1)) ≤ 1 / 10 := by
    refine sigma_le_tenth_of_drop hη hdc ?_
    rw [log_blockScale_harperOffset_top hx1 hDlog]
    exact hσ
  have hcut : blockCutoff (harperOffset D x) (harperBlockCount D x) = ⌊x⌋₊ + 1 :=
    blockCutoff_harperOffset hx1 hDlog
  have hy : blockCutoff (harperOffset D x) (harperBlockCount D x - d) ≤ ⌊x⌋₊ + 1 :=
    le_of_le_of_eq (blockCutoff_mono _ (Nat.sub_le _ _)) hcut
  exact H Ω' Y ν hY (harperOffset D x) σ a (harperBlockCount D x - d) r (⌊x⌋₊ + 1) s hf hϑ hy
    hres hspos hσ' hτ0 hτsq hT ha ha1 hn₀ hr1 hrn hra hhf

end RMF
