/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherRestrictedFirstMomentLower
import RMF.Reduction.RademacherLower

/-!
# The numerator of the Paley–Zygmund step, for the Rademacher function

The twin of the Steinhaus `RMF.exists_le_integral_restricted_normSq_numerator`, and the last piece
before Paley–Zygmund.

Paley–Zygmund wants `E[X]` from *below*, at `X = \int_L |F(1/2+\sigma+it)|^2\,dt`.  Two things
supply it:

* `RMF.exists_le_integral_restricted_normSq_rademacher_of_top` — the barrier restriction, a lower
  bound on `E[X]` *relative to* `E\|F(1/2+\sigma)\|^2`;
* `RMF.le_integral_normSq_of_drop_sqfree'` — a lower bound on `E\|F(1/2+\sigma)\|^2` itself,
  **with the full exponent**.

The second needs care.  The squarefree Euler product's second moment is
`\prod_{p<y}(1 + p^{-1-2\sigma})`, and the sharp *per-factor* comparison `e^{u/2} \le 1+u` loses a
square root — which Paley–Zygmund cannot absorb, since it consumes the numerator as
`N^{2-q}/D_n^{1-q}`.  Summing over primes instead of bounding factor by factor recovers the full
exponent at the cost of `\sum_p p^{-2} \le 1`, and that is the `64` here where the Steinhaus
numerator has `63`.

**The `V`-dependence is the `d` blocks given up**, exactly as on the Steinhaus side: since
`\log x_{n} = e^{n+\theta}`, `e^{n-d}` is `\log x` divided by `e^{\theta}e^{d}`.
-/

open MeasureTheory

namespace RMF

/-- **The numerator of the Paley–Zygmund step, for the Rademacher function**, the twin of
`RMF.exists_le_integral_restricted_normSq_numerator`: for `T` in the admissible height range,
`|T|\cdot\alpha\cdot\min(1, a/\sqrt{n-d})\cdot e^{(n-d)-64} \le E[X]`, with `\alpha` and `64`
absolute.  The tilt condition is `10\eta \le e^d` rather than `\eta \le e^d`, because Harper's
Proposition 6, the Rademacher barrier estimate, needs `\eta \le 1/10`.  The `3 \le \theta` that
`RMF.le_integral_normSq_of_drop_sqfree'` asks for comes from `4 \le D`. -/
theorem exists_le_integral_restricted_normSq_numerator_rademacher :
    ∃ (D₀ : ℕ) (a₀ α Bs Tsh c : ℝ),
      4 ≤ D₀ ∧ 0 < α ∧ blockSlope 125 ≤ Bs ∧ 0 < Tsh ∧ 0 < c ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ d : ℕ, ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (T : Set ℝ) (hf : ℕ → ℝ),
          x₀ ≤ x → 0 ≤ σ → |σ| * Real.log x ≤ η → 10 * η ≤ Real.exp d → a₀ ≤ a →
          MeasurableSet T → volume T ≠ ⊤ →
          (∀ t ∈ T, 0 < 2 * t
            ∧ (2 * t) ^ 2 ≤ Real.exp (c / 2 * Real.exp (harperOffset D x / 10))
            ∧ Tsh ≤ 2 * t * Real.exp (harperOffset D x)) →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            (volume T).toReal
                * (α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ))))
                * Real.exp (((harperBlockCount D x - d : ℕ) : ℝ) - 64)
              ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω))
                    (harperBlockCount D x - d)
                    (fun j => -a - Bs * j) (fun j => a + j + hf j))
                  (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω) ∂ν := by
  obtain ⟨D₀, a₀, α, Bs, Tsh, c, hD, hα, hBs, hTsh, hcpos, H⟩ :=
    exists_le_integral_restricted_normSq_rademacher_of_top
  refine ⟨D₀, max a₀ 0, α, Bs, Tsh, c, hD, hα, hBs, hTsh, hcpos, ?_⟩
  intro D hDD d
  obtain ⟨x₁, H⟩ := H D hDD d
  obtain ⟨x₂, hx₂⟩ := exists_harperThreshold_of_blockCount D d
  refine ⟨max x₁ x₂, ?_⟩
  intro Ω' _ Y ν hY x σ η a T hf hx hσ0 hσ hη ha hT hTfin hheight hhf
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxx₂ : x₂ ≤ x := le_trans (le_max_right _ _) hx
  have haa₀ : a₀ ≤ a := le_trans (le_max_left _ _) ha
  have ha0 : (0 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  obtain ⟨hx1, hDlog, hcount⟩ := hx₂ x hxx₂
  refine le_trans ?_
    (H Ω' Y ν hY x σ a η T hf hxx₁ (by linarith) hσ hη haa₀ hT hTfin hheight hhf)
  -- the block estimate's own threshold, from `4 ≤ D`
  have hθ3 : (3 : ℝ) ≤ harperOffset D x := by
    have hsub := sub_one_le_harperOffset D x
    have hD4 : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast le_trans hD hDD
    linarith
  -- the tilt at the top of the block range: `|σ|·\log x ≤ η ≤ e^d/10 ≤ e^d`
  have hσtop : |σ| * Real.log (blockScale (harperOffset D x)
      (harperBlockCount D x + 1)) ≤ Real.exp d := by
    rw [log_blockScale_harperOffset_top hx1 hDlog]
    have hpos : (0 : ℝ) < Real.exp d := Real.exp_pos _
    linarith
  -- the prime range reaches the cutoff
  have hxeq : blockScale (harperOffset D x) (harperBlockCount D x + 1) = x :=
    blockScale_harperOffset_top hx1 hDlog
  have hy : ⌊blockScale (harperOffset D x) (harperBlockCount D x - d)⌋₊ + 1 ≤ ⌊x⌋₊ + 1 := by
    have hmono := blockScale_mono (harperOffset D x)
      (show harperBlockCount D x - d ≤ harperBlockCount D x + 1 by omega)
    rw [hxeq] at hmono
    exact Nat.succ_le_succ (Nat.floor_mono hmono)
  have heuler := le_integral_normSq_of_drop_sqfree' hY (θ := harperOffset D x)
    (n := harperBlockCount D x) (d := d) (y := ⌊x⌋₊ + 1) hθ3 hcount hσ0 hσtop hy
  rw [← Nat.cast_sub hcount] at heuler
  have hC0 : (0 : ℝ) ≤ (volume T).toReal
      * (α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ)))) := by
    refine mul_nonneg ENNReal.toReal_nonneg (mul_nonneg hα.le ?_)
    exact le_min zero_le_one (div_nonneg ha0 (Real.sqrt_nonneg _))
  exact mul_le_mul_of_nonneg_left heuler hC0

end RMF
