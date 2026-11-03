/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import RMF.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Harper's theorem — the model and the interpolation core

This file fixes the model — `RMF.randomSum` and `RMF.normalisedSum` — and the Hölder interpolation
that both halves of the theorem descend through.  The theorem is `RMF.harper_low_moments` in
`RMF/Harper.lean`; this file is imported by the reduction and holds the model, the interpolation
inequality and the upper descent.

## The statement

With `f` a Steinhaus random multiplicative function and `S_x := x^(-1/2) ∑_{n ≤ x} f(n)`, Harper's
Theorem 1 is that for `q ∈ [0,1]`, uniformly for large `x`,

`E |S_x|^(2q)  ≍  (1 + (1-q) √(log log x))^(-q)`.

The normalisation is chosen so that `E |S_x|² ≍ 1`; squareroot cancellation alone would give `≍ 1`.
The familiar form at `q = 1/2` is `E |∑_{n ≤ x} f(n)| ≍ √x (log log x)^(-1/4)`.

## Assembly

**Both** bounds reduce to `q ∈ [2/3, 1]` — in the words of Harper, *Moments of random
multiplicative functions, I* (arXiv:1703.06654), "it will suffice to prove Theorems 1 and 2 for
`2/3 ≤ q ≤ 1`".

* `q ∈ [0, 2/3]`, **upper**: descends from `q = 2/3` alone, by `L^p`-monotonicity
  (`RMF.integral_rpow_le_rpow_integral_of_le_two_thirds`).
* `q ∈ [0, 2/3]`, **lower**: monotonicity runs the wrong way, so it descends by Hölder
  interpolation from **two** inputs — the *lower* bound at `q = 2/3` and the *upper* bound at
  `q = 3/4` (`RMF.le_target_of_two_thirds_lower`, in `RMF/Harper.lean`).  The upper bound on
  `[2/3,1]` is therefore an input of the lower descent.
* `q ∈ [2/3, 1]` — upper and lower separately, fed by the chaos estimate and by Key Proposition 5.

On all of `[0,1]` and for `x ≥ 3`, the upper bound is `RMF.harper_upper_ge_three` and the lower
bound `RMF.exists_le_integral_rpow_normalisedSum_full`.
-/

open MeasureTheory

open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The partial sum -/

/-- The partial sum `∑_{n ≤ x} f(n)` of a random multiplicative function. -/
noncomputable def randomSum (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f ω n

/-- The normalised partial sum `S_x = x^(-1/2) ∑_{n ≤ x} f(n)`, scaled so that `E |S_x|² ≍ 1`.

Harper's theorem is about this quantity; the unnormalised statement carries a factor `x^q` that
obscures the `log log x` the theorem is actually about. -/
noncomputable def normalisedSum (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) : ℂ :=
  randomSum f x ω / (Real.sqrt x : ℂ)

/-! ### The interpolation core

Both descents are Hölder, but the lower one needs the two-sided form: `4/3` is interpolated from
below by `2q` and from above by `3/2`.  This is that inequality, stated for powers of a norm with
the two weights left as parameters, since the specialisation to Harper's exponents is then pure
arithmetic. -/

/-- **Hölder interpolation between two powers of a norm.**  If `aα + bβ = c ≠ 0` with `α + β = 1`
and `α, β ≥ 0`, then `∫ ‖S‖^c ≤ (∫ ‖S‖^a)^α (∫ ‖S‖^b)^β`.

This is the `p + q = 1` form of Hölder (`ENNReal.lintegral_mul_norm_pow_le`), transported to
Bochner integrals.  With `α > 0`, a *lower* bound on the left and an *upper* bound on the
`b`-factor force a lower bound on the `a`-factor, which is how the lower descent works. -/
theorem integral_rpow_le_mul_rpow {S : Ω → ℂ} {μ : Measure Ω} {a b c α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) (habc : a * α + b * β = c) (hc : c ≠ 0)
    (hIa : Integrable (fun ω => ‖S ω‖ ^ a) μ) (hIb : Integrable (fun ω => ‖S ω‖ ^ b) μ)
    (hIc : Integrable (fun ω => ‖S ω‖ ^ c) μ) :
    (∫ ω, ‖S ω‖ ^ c ∂μ) ≤ (∫ ω, ‖S ω‖ ^ a ∂μ) ^ α * (∫ ω, ‖S ω‖ ^ b ∂μ) ^ β := by
  have hna : ∀ ω, (0 : ℝ) ≤ ‖S ω‖ ^ a := fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hnb : ∀ ω, (0 : ℝ) ≤ ‖S ω‖ ^ b := fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hnc : ∀ ω, (0 : ℝ) ≤ ‖S ω‖ ^ c := fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hIa0 : (0 : ℝ) ≤ ∫ ω, ‖S ω‖ ^ a ∂μ := integral_nonneg hna
  have hIb0 : (0 : ℝ) ≤ ∫ ω, ‖S ω‖ ^ b ∂μ := integral_nonneg hnb
  -- the pointwise identity that turns the two factors into one
  have hpt : ∀ ω, ENNReal.ofReal (‖S ω‖ ^ c)
      = ENNReal.ofReal (‖S ω‖ ^ a) ^ α * ENNReal.ofReal (‖S ω‖ ^ b) ^ β := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg (hna ω) hα, ENNReal.ofReal_rpow_of_nonneg (hnb ω) hβ,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (hna ω) _), ← Real.rpow_mul (norm_nonneg _),
      ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_add' (norm_nonneg _) (by rw [habc]; exact hc),
      habc]
  -- Hölder in `ℒ¹`
  have hma : AEMeasurable (fun ω => ENNReal.ofReal (‖S ω‖ ^ a)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hIa.aemeasurable
  have hmb : AEMeasurable (fun ω => ENNReal.ofReal (‖S ω‖ ^ b)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hIb.aemeasurable
  have hkey := ENNReal.lintegral_mul_norm_pow_le hma hmb hα hβ hαβ
  -- transport all three integrals back
  rw [← lintegral_congr hpt, ← ofReal_integral_eq_lintegral_ofReal hIa (.of_forall hna),
    ← ofReal_integral_eq_lintegral_ofReal hIb (.of_forall hnb),
    ← ofReal_integral_eq_lintegral_ofReal hIc (.of_forall hnc),
    ENNReal.ofReal_rpow_of_nonneg hIa0 hα, ENNReal.ofReal_rpow_of_nonneg hIb0 hβ,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hIa0 _)] at hkey
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.rpow_nonneg hIa0 _) (Real.rpow_nonneg hIb0 _))).1 hkey

/-! ### The Hölder descent

The one step of the assembly that is pure `L^p` monotonicity: on a probability space `p ↦ ‖·‖_p`
is increasing, so the `2q`-norm is controlled by the `4/3`-norm exactly when `2q ≤ 4/3`. -/

/-- **Hölder descent.**  For `0 ≤ q ≤ 2/3` on a probability space,
`E |S|^(2q) ≤ (E |S|^(4/3))^(3q/2)`.  So the upper bound in Harper's theorem need only be proved
for `q ∈ [2/3, 1]`: `E |S|^(4/3) ≪ (log log x)^(-1/3)` gives `≪ (log log x)^(-q/2)` for every
smaller `q`.  `hS` holds for the normalised sum (`RMF.IsSteinhausRMF.memLp_normalisedSum`,
`RMF.IsRademacherRMF.memLp_normalisedSum`). -/
theorem integral_rpow_le_rpow_integral_of_le_two_thirds {S : Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 2 / 3)
    (hS : MemLp S (ENNReal.ofReal (4 / 3)) μ) :
    (∫ ω, ‖S ω‖ ^ (2 * q) ∂μ) ≤ (∫ ω, ‖S ω‖ ^ (4 / 3 : ℝ) ∂μ) ^ (3 * q / 2) := by
  have hIq : (0 : ℝ) ≤ ∫ ω, ‖S ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hI43 : (0 : ℝ) ≤ ∫ ω, ‖S ω‖ ^ (4 / 3 : ℝ) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  rcases eq_or_lt_of_le hq0 with hq0' | hq0'
  · -- `q = 0`: both sides are `1`, since `t ^ (0 : ℝ) = 1` even at `t = 0`
    subst_vars
    simp
  -- `0 < q`.  Set up the two exponents in `ℝ≥0∞`.
  have h2q : (0 : ℝ) < 2 * q := by linarith
  set p : ℝ≥0∞ := ENNReal.ofReal (2 * q) with hpdef
  have hple : p ≤ ENNReal.ofReal (4 / 3) := ENNReal.ofReal_le_ofReal (by linarith)
  have hp0 : p ≠ 0 := (ENNReal.ofReal_pos.2 h2q).ne'
  have hptop : p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpre : p.toReal = 2 * q := ENNReal.toReal_ofReal h2q.le
  have hrre : (ENNReal.ofReal (4 / 3)).toReal = (4 / 3 : ℝ) :=
    ENNReal.toReal_ofReal (by norm_num)
  have hSp : MemLp S p μ := hS.mono_exponent hple
  -- `L^p` monotonicity on a probability space
  have hmono := eLpNorm_le_eLpNorm_of_exponent_le hple hS.aestronglyMeasurable (μ := μ)
  rw [hSp.eLpNorm_eq_integral_rpow_norm hp0 hptop,
    hS.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.2 (by norm_num)).ne'
      ENNReal.ofReal_ne_top, hpre, hrre] at hmono
  have hkey : (∫ ω, ‖S ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
      ≤ (∫ ω, ‖S ω‖ ^ (4 / 3 : ℝ) ∂μ) ^ (4 / 3 : ℝ)⁻¹ :=
    (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hI43 _)).1 hmono
  -- raise both sides to the power `2q`
  calc ∫ ω, ‖S ω‖ ^ (2 * q) ∂μ
      = ((∫ ω, ‖S ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹) ^ (2 * q) := by
        rw [← Real.rpow_mul hIq, inv_mul_cancel₀ h2q.ne', Real.rpow_one]
    _ ≤ ((∫ ω, ‖S ω‖ ^ (4 / 3 : ℝ) ∂μ) ^ (4 / 3 : ℝ)⁻¹) ^ (2 * q) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hIq _) hkey h2q.le
    _ = (∫ ω, ‖S ω‖ ^ (4 / 3 : ℝ) ∂μ) ^ (3 * q / 2) := by
        rw [← Real.rpow_mul hI43]
        congr 1
        ring

end RMF
