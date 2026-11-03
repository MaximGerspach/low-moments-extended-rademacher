/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.EulerMomentShiftExplicit
import RMF.Weighted.MesoscopicChaos

/-!
# One mesoscopic block, end to end

Three results meet here, and nothing else is needed for a single block:

* `RMF.integral_rpow_setIntegral_normSq_split_le` — the split at `z`, which turns the full
  product into `E‖F_z(½+σ)‖^{2q}` times the block product;
* `RMF.IsRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_log_of_le_half` — (PF),
  the moment bound `E‖F_z(½+σ)‖^{2q} ≤ e⁷·(log z)^{q(2q-1)}`, below the critical exponent at the
  shifted abscissa;
* `RMF.exists_const_integral_rpow_setIntegral_normSq_randomEulerProductIco_le_rademacher` — the
  mesoscopic chaos estimate for the block product.

The product of the three is

`E[(∫_{T/e}^{T}‖F_x(½+σ+it)‖²dt)^q] ≤ A·(log w)^{q(2q-1)}·(T²·log x)^q·(1+(1-q)√t)^{-q}`,

and at `T·log w ≍ 1` the first factor is `≍ T^{q(1-2q)}`.  **That factor is the whole reason for
the split**: without it the block would contribute `(T·log x)^q` and the sum over blocks would
not converge for `q` near `½`.

## The `+1`

The split point is written `w + 1` rather than `z`, because
`RMF.randomEulerProduct f (w+1)` is the product over `p ≤ w` and (PF) is stated in terms of
`log w`.  That is where (PF) is proved, at either sign of `q(2q-1)`: below `½` Mertens is read
from below at `w`, above `½` from above at `w`.  (For `q ≤ ½` it is also the weaker of the two
readings, since `log w ≤ log(w+1)` and the exponent is negative; above `½` it is the stronger
one, and it is available because nothing here goes through `log(w+1)`.)
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The split and (PF), with the chaos factor left open.**  For `2 ≤ w`, `w + 1 ≤ ⌊x⌋ + 1`,
`0 ≤ σ` with `σ·log w ≤ 1`, `0 ≤ q ≤ 1`, `T > 0` and `T·log(w+1) ≤ 2`,
`E[(∫_{T/e}^{T}‖F_x(½+σ+it)‖²dt)^q] ≤ e^{143800}·e⁷(log w)^{q(2q-1)}·G` whenever `G` bounds the
same moment of the block product over `(w, x]`.  Both block bounds are this lemma at two `G`: the
sharp one from the mesoscopic chaos estimate, the shallowest blocks from Jensen and Mertens.  (PF)
holds at either sign of `q(2q-1)`, with `e^{101/50} ≤ e⁷` so that one constant serves both. -/
theorem integral_rpow_setIntegral_normSq_block_le_of_chaos {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {x σ T q : ℝ} {w : ℕ} {G : ℝ}
    (hw2 : 2 ≤ w) (hwfl : w + 1 ≤ ⌊x⌋₊ + 1) (hσ : 0 ≤ σ) (hσw : σ * Real.log w ≤ 1)
    (hq0 : 0 ≤ q) (hq2 : q ≤ 1) (hT0 : 0 < T)
    (hThi : T * Real.log ((w : ℝ) + 1) ≤ 2)
    (hchaos : (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (w + 1)
          (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν) ≤ G) :
    (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      ≤ Real.exp 143800 * (Real.exp 7 * (Real.log w) ^ (q * (2 * q - 1))) * G := by
  haveI := hY.isProbabilityMeasure
  have hw2R : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw2
  have hcast : (((w + 1 : ℕ)) : ℝ) = (w : ℝ) + 1 := by push_cast; ring
  have hlogw0 : (0 : ℝ) ≤ Real.log w := Real.log_nonneg (by linarith)
  have he1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hab : T / Real.exp 1 < T := by
    rw [div_lt_iff₀ (Real.exp_pos 1)]; nlinarith
  have hTe0 : (0 : ℝ) < T / Real.exp 1 := div_pos hT0 (Real.exp_pos 1)
  -- the split
  have hzt : ∀ t ∈ Set.Icc (T / Real.exp 1) T, |t| * Real.log ((w + 1 : ℕ) : ℝ) ≤ 2 := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hTe0 ht.1
    have hlog0 : (0 : ℝ) ≤ Real.log ((w : ℝ) + 1) := Real.log_nonneg (by linarith)
    rw [abs_of_pos ht0, hcast]
    exact le_trans (mul_le_mul_of_nonneg_right ht.2 hlog0) hThi
  have hsplit := integral_rpow_setIntegral_normSq_split_le hY (z := w + 1) (y := ⌊x⌋₊ + 1)
    (by omega) hwfl hσ hab hq0 (by linarith) hzt
  have hs0 : shiftLine σ 0 = (((1 / 2 + σ : ℝ)) : ℂ) := by simp [shiftLine]
  rw [hs0] at hsplit
  -- (PF) at the shifted abscissa
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hlogw0' : (0 : ℝ) ≤ (Real.log w) ^ (q * (2 * q - 1)) :=
    Real.rpow_nonneg hlogw0 _
  have hPF : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (w + 1)
        (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂ν)
      ≤ Real.exp 7 * (Real.log w) ^ (q * (2 * q - 1)) := by
    rcases le_total q (1 / 2) with h | h
    · exact hf.integral_norm_randomEulerProduct_shift_rpow_le_log_of_le_half hσ hq0 h hw2 hσw
    · refine le_trans (hf.integral_norm_randomEulerProduct_shift_rpow_le_log hσ h hq2 hw2) ?_
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by norm_num)) hlogw0'
  have hPF0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
      (w + 1) (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂ν :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hCH0 : (0 : ℝ) ≤ ∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (w + 1)
        (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν :=
    integral_nonneg fun ω => Real.rpow_nonneg (integral_nonneg fun t => sq_nonneg _) _
  have hlogpow0 : (0 : ℝ) ≤ (Real.log w) ^ (q * (2 * q - 1)) := Real.rpow_nonneg hlogw0 _
  have hPFb0 : (0 : ℝ) ≤ Real.exp 7 * (Real.log w) ^ (q * (2 * q - 1)) :=
    mul_nonneg (Real.exp_pos 7).le hlogpow0
  have hexpq : Real.exp 143800 ^ q ≤ Real.exp 143800 := by
    calc Real.exp 143800 ^ q ≤ Real.exp 143800 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le
            (by linarith [Real.add_one_le_exp (143800 : ℝ)]) (by linarith)
      _ = Real.exp 143800 := Real.rpow_one _
  refine le_trans hsplit ?_
  calc Real.exp 143800 ^ q
        * ((∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (w + 1)
              (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂ν)
          * ∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (w + 1)
                (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      ≤ Real.exp 143800 * ((Real.exp 7 * (Real.log w) ^ (q * (2 * q - 1))) * G) :=
        mul_le_mul hexpq (mul_le_mul hPF hchaos hCH0 hPFb0) (mul_nonneg hPF0 hCH0)
          (Real.exp_pos _).le
    _ = Real.exp 143800 * (Real.exp 7 * (Real.log w) ^ (q * (2 * q - 1))) * G := by ring

/-- **One mesoscopic block.**  For the window `[T/e, T]`, the split point `w + 1` and the depth
`t = harperBlockCount D x - 3`, uniformly for `0 ≤ q ≤ 1`,
`E[(∫_{T/e}^{T}‖F_x(½+σ+it)‖²dt)^q] ≤ A·(log w)^{q(2q-1)}·(T²·log x)^q·(1+(1-q)√t)^{-q}`.
Of the window hypotheses, `1 ≤ T·log(w+1)` is the block first moment's, `T·log(w+1) ≤ 2` the
split's, and `Klo ≤ T·e^{harperOffset D x} ≤ e⁴·Klo` the barrier's; at `T·log(w+1) ≍ 1` all three
hold with `D` chosen by `RMF.exists_harperOffset_at_split_scale`. -/
theorem exists_const_integral_rpow_setIntegral_normSq_block_le_rademacher :
    ∃ (D₀ t₀ : ℕ) (x₀ Klo A : ℝ), 4 ≤ D₀ ∧ 4 ≤ Klo ∧ Real.exp (D₀ : ℝ) ≤ Klo ∧ 0 < A ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (x σ T q : ℝ) (w D : ℕ),
          x₀ ≤ x → D₀ ≤ D → (D : ℝ) ≤ Real.log (Real.log x) →
          2 ≤ w → ((w : ℝ) + 1) ≤ x → w + 1 ≤ ⌊x⌋₊ + 1 →
          ((w : ℝ) + 1) ≤ blockScale (harperOffset D x) 0 →
          0 ≤ σ → σ * Real.log x ≤ 1 → 0 ≤ q → q ≤ 1 →
          0 < T → T ≤ 1 →
          1 ≤ T * Real.log ((w : ℝ) + 1) → T * Real.log ((w : ℝ) + 1) ≤ 2 →
          Klo ≤ T * Real.exp (harperOffset D x) →
          T * Real.exp (harperOffset D x) ≤ Real.exp 4 * Klo →
          t₀ ≤ harperBlockCount D x - 3 →
            (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
                ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                  (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
              ≤ A * ((Real.log w) ^ (q * (2 * q - 1)) * (T ^ 2 * Real.log x) ^ q)
                * (1 + (1 - q) * Real.sqrt ((harperBlockCount D x - 3 : ℕ) : ℝ)) ^ (-q) := by
  obtain ⟨D₀, t₀, x₀, Klo, Ac, hD₀, hKlo, hKloD, hAc, HC⟩ :=
    exists_const_integral_rpow_setIntegral_normSq_randomEulerProductIco_le_rademacher (Ω := Ω)
  refine ⟨D₀, t₀, max x₀ 2, Klo, Real.exp 143800 * Real.exp 7 * Ac, hD₀, hKlo, hKloD,
    by positivity, ?_⟩
  intro Y ν hY x σ T q w D hx hDD hDlog hw2 hwx hwfl hwb hσ hσx hq0 hq2 hT0 hT1 hTlo hThi
    hKl hKb ht₀
  haveI := hY.isProbabilityMeasure
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hw2R : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw2
  have hcast : (((w + 1 : ℕ)) : ℝ) = (w : ℝ) + 1 := by push_cast; ring
  have hwxle : (w : ℝ) ≤ x := by linarith
  have hσw : σ * Real.log w ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hwxle) hσ) hσx
  have hchaos := HC Y ν hY x σ T q (w + 1) D hx0 hDD hDlog (by omega)
    (by rw [hcast]; linarith) hwfl (by rw [hcast]; exact hwb) hσ hσx (by linarith)
    (by linarith) hT0 hT1 (by rw [hcast]; exact hTlo) hKl hKb ht₀
  refine le_trans (integral_rpow_setIntegral_normSq_block_le_of_chaos hY hw2 hwfl hσ hσw
    hq0 hq2 hT0 hThi hchaos) (le_of_eq ?_)
  ring

end RMF
