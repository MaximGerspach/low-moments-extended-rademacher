/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.UpperShift
import RMF.Probability.ChaosMomentAveraged

/-!
# The chaos moments at the averaged free start

`RMF.integral_chaosUnit_rpow_le_averaged`: the chaos moments of
`RMF.integral_chaosUnitShift_rpow_le_averaged` against `log log y`, at the constant
`RMF.chaosAveragedConst`.  The restricted chaos constant `freeStartConst 0·e^{γ + 9.0028/L₀}` at
level shift `0` becomes `averagedConst 0 β T κ·e^{γ + 9.0028/L₀}` at level shift
`averagedShift 0 β T κ`, with the good set's log-slope `β`, `T` and `κ` free per `q`.
`RMF.harper_upper_averaged_sieve_switch` assembles Harper's upper bound from it.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The constant of `RMF.integral_chaosUnit_rpow_le_averaged`, as a function of `q`. -/
noncomputable def chaosAveragedConst (A lam T κ β : ℝ → ℝ) (δ k L₀ q : ℝ) : ℝ :=
  k * shiftMomentConst (normSqLogSharpConst L₀)
    (averagedConst 0 (β q) (T q) (κ q) * normSqLogSharpConst L₀) (harperGoodBadConstOf 0 (β q))
    (A q) (averagedShift 0 (β q) (T q) (κ q)) (lam q) δ q

/-- `e^u + 1 ≤ e^{u+1}` for `u ≥ 0`: `e^{u+1} = e·e^u ≥ 2e^u`. -/
lemma exp_add_one_le_exp_add_one {u : ℝ} (hu : 0 ≤ u) : Real.exp u + 1 ≤ Real.exp (u + 1) := by
  rw [Real.exp_add]
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  nlinarith

/-- **The chaos moments against `log log y`, at the averaged free start**:
`RMF.integral_chaosUnitShift_rpow_le_averaged` at `σ = 0`, through
`RMF.integral_chaosUnit_rpow_le_loglog_of`, past `exp(exp ℓ₀)`.  The level `ℓ₀` pays for the block
count `N` with room (`D + N ≤ ℓ₀`), for the conversion to `log log y` at the cost `k`
(`k²(D+1)/(k²-1) ≤ ℓ₀`) and for Mertens' product (`L₀ + 1 ≤ e^{ℓ₀}`), where
`D = freeStartHarperD 0`. -/
theorem integral_chaosUnit_rpow_le_averaged {A lam T κ β : ℝ → ℝ} {Amax δ k L₀ ℓ₀ : ℝ} {N : ℕ}
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hk : 1 < k) (hL₀ : 1 ≤ L₀)
    (hA : ∀ q, harperBadLevel 0 ≤ A q ∧ A q ≤ Amax) (hlam : ∀ q, 1 ≤ lam q)
    (hT : ∀ q, 4 < T q) (hκ : ∀ q, 1 ≤ κ q) (hβ : ∀ q, 1 / 2 < β q ∧ β q ≤ 2)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δ * N)
    (hmono : 3 ≤ 8 * δ * Real.sqrt (N : ℝ)) (hℓN : (freeStartHarperD 0 : ℝ) + N ≤ ℓ₀)
    (hℓk : k ^ 2 * ((freeStartHarperD 0 : ℝ) + 1) / (k ^ 2 - 1) ≤ ℓ₀)
    (hℓL : L₀ + 1 ≤ Real.exp ℓ₀) :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ y q : ℝ, Real.exp (Real.exp ℓ₀) ≤ y → 0 ≤ q → q ≤ 1 →
        ∫ ω, chaosUnit f y ω ^ q ∂μ
          ≤ chaosAveragedConst A lam T κ β δ k L₀ q
            * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q) := by
  intro f μ hf y q hy hq0 hq1
  set D := freeStartHarperD 0 with hD
  have hthr : ∀ n : ℕ, (D : ℝ) + n ≤ ℓ₀ → harperThreshold D n ≤ Real.exp (Real.exp ℓ₀) :=
    fun n hn => Real.exp_le_exp.2 (Real.exp_le_exp.2 hn)
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hL : Real.exp L₀ + 1 ≤ Real.exp (Real.exp ℓ₀) :=
    le_trans (exp_add_one_le_exp_add_one (by linarith)) (Real.exp_le_exp.2 hℓL)
  have hy' : max (max (max (harperThreshold D 0) (Real.exp L₀ + 1)) (harperThreshold D N))
      (Real.exp (Real.exp (k ^ 2 * ((D : ℝ) + 1) / (k ^ 2 - 1)))) ≤ y :=
    le_trans (max_le (max_le (max_le (hthr 0 (by push_cast; linarith)) hL) (hthr N hℓN))
      (Real.exp_le_exp.2 (Real.exp_le_exp.2 hℓk))) hy
  exact integral_chaosUnit_rpow_le_loglog_of (D := D)
    (y₁ := max (max (harperThreshold D 0) (Real.exp L₀ + 1)) (harperThreshold D N))
    (S := fun q => shiftMomentConst (normSqLogSharpConst L₀)
      (averagedConst 0 (β q) (T q) (κ q) * normSqLogSharpConst L₀) (harperGoodBadConstOf 0 (β q))
      (A q) (averagedShift 0 (β q) (T q) (κ q)) (lam q) δ q)
    hk (le_trans (two_le_harperThreshold D N) (le_max_right _ _))
    (fun Y ν hY y q hy hq0 hq1 => integral_chaosUnitShift_rpow_le_averaged 0 (β q) le_rfl
      (hβ q).1 (hβ q).2 hδ0 hδ hL₀ (hT q) (hκ q) hN hmono Y ν hY y 0 0 q (A q) (lam q) hy le_rfl
      le_rfl le_rfl (by simp) hq0 hq1 (hA q).1 (hA q).2 (hlam q))
    f μ hf y q hy' hq0 hq1

end RMF
