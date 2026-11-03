/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Minkowski's inequality in integral form

The upper bound `E|S(x)|^{2q} ≪ (log x)^{q(2q-1)}` for fixed `½ < q < 1` applies Minkowski at
exponent `2q ≥ 1` to the layered identity: `‖S(x)‖_{2q}` is at most the sum of the `2q`-norms of
the `K + 1` terms.

Mathlib has this as `MeasureTheory.eLpNorm_sum_le`, in `ℝ≥0∞` and phrased through `eLpNorm`.
The library is phrased through Bochner integrals of `‖·‖ ^ r`, so what is proved here is the
translation,

`(∫ ‖∑ᵢ gᵢ‖^r)^{1/r} ≤ ∑ᵢ (∫ ‖gᵢ‖^r)^{1/r}`   for `1 ≤ r`,

by `MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm` at `p = ENNReal.ofReal r` — the same
translation `RMF.integral_rpow_le_rpow_integral_of_le_two_thirds` makes for `L^p` monotonicity.

Only the `MemLp` hypothesis is needed; there is no separate integrability side condition, and `r`
is a real exponent, not a natural power.

The other direction of the `L^p` scale — `‖·‖_{2q} ≤ ‖·‖_2` for `2q ≤ 2` — is **not** here: on a
probability space that is Jensen for the concave `t ↦ t^q`, already available as
`RMF.integral_rpow_le_rpow_of_integral_le`, and that is the form the upper bound needs, since its
tail bounds control `∫ ‖T‖²` rather than its root.
-/

open MeasureTheory

namespace RMF

/-- **`MemLp` from a bound**, at a real exponent.  On a finite measure space an almost everywhere
bounded function lies in every `L^p`. -/
theorem memLp_ofReal_of_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] {g : Ω → E} {M r : ℝ}
    (hmeas : AEStronglyMeasurable g μ) (hb : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ M) :
    MemLp g (ENNReal.ofReal r) μ :=
  (memLp_top_of_bound hmeas M hb).mono_exponent le_top

/-- **Minkowski's inequality** in integral form:
`(∫ ‖∑ᵢ gᵢ‖^r)^{1/r} ≤ ∑ᵢ (∫ ‖gᵢ‖^r)^{1/r}` for `1 ≤ r`.

`MeasureTheory.eLpNorm_sum_le` with both sides pushed through
`MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm`. -/
theorem rpow_inv_integral_rpow_norm_sum_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ι E : Type*} [NormedAddCommGroup E] {s : Finset ι} {g : ι → Ω → E} {r : ℝ} (hr : 1 ≤ r)
    (hg : ∀ i ∈ s, MemLp (g i) (ENNReal.ofReal r) μ) :
    (∫ ω, ‖∑ i ∈ s, g i ω‖ ^ r ∂μ) ^ r⁻¹ ≤ ∑ i ∈ s, (∫ ω, ‖g i ω‖ ^ r ∂μ) ^ r⁻¹ := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hptop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpre : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr
  have hnn : ∀ i, (0 : ℝ) ≤ (∫ ω, ‖g i ω‖ ^ r ∂μ) ^ r⁻¹ := fun i =>
    Real.rpow_nonneg (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) _
  have hsum : MemLp (fun ω => ∑ i ∈ s, g i ω) (ENNReal.ofReal r) μ := memLp_finsetSum s hg
  have hfun : (∑ i ∈ s, g i) = fun ω => ∑ i ∈ s, g i ω := funext fun ω => Finset.sum_apply ω s g
  have hle := eLpNorm_sum_le (μ := μ) (f := g) (s := s) (p := ENNReal.ofReal r)
    (fun i hi => (hg i hi).aestronglyMeasurable) hp1
  rw [hfun, hsum.eLpNorm_eq_integral_rpow_norm hp0 hptop, hpre] at hle
  have hrhs : ∑ i ∈ s, eLpNorm (g i) (ENNReal.ofReal r) μ
      = ENNReal.ofReal (∑ i ∈ s, (∫ ω, ‖g i ω‖ ^ r ∂μ) ^ r⁻¹) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => hnn i]
    exact Finset.sum_congr rfl fun i hi => by
      rw [(hg i hi).eLpNorm_eq_integral_rpow_norm hp0 hptop, hpre]
  rw [hrhs] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ => hnn i)).1 hle

end RMF
