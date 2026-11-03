/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherFirstMoment
import RMF.SecondMoment

/-!
# The periodisation tail, Rademacher case: Jensen against the second moment

The Steinhaus periodisation trades `∫_ℝ` for `∫_0^1` by moving each window `∫_n^{n+1}` onto the
unit window: `RMF.integral_rpow_window_eq` says *every window has the same `q`-th moment as the
unit window*, and it is proved by **rotating** the primes by `p^{-in}`
(`RMF.integral_rpow_unitFunctional_rotate`, resting on `RMF.IsSteinhausPrimeValues.mul_unimodular`).
Rotation is not a Rademacher symmetry, so that equality is not available here.

## What replaces it for the far windows

For `|n|` large the equality is more than the periodisation needs.  A *bound uniform in `n`* is
enough, because the weights `(1+n²)^{-q}` are summable, and such a bound is available with **no
rotation at all**:

    ∫_Ω (∫_n^{n+1} ‖F(σ+it)‖² dt)^q dν
      ≤ (∫_Ω ∫_n^{n+1} ‖F(σ+it)‖² dt dν)^q      Jensen, `t ↦ t^q` concave for `q ∈ [0,1]`
      = (∫_n^{n+1} ∫_Ω ‖F(σ+it)‖² dν dt)^q      Fubini
      = (∫_Ω ‖F(σ)‖² dν)^q                      height-independence of the SECOND moment

The last step is `RMF.IsRademacherRMF.integral_normSq_shiftLine_eq`, and it is where the Rademacher
case is *easier* than the Steinhaus one rather than harder: the second moment is
`∏_{p<y}(1 + p^{-2σ})`, which depends only on `Re s`, so the collapse needs **no hypothesis on the
law's rotation invariance and none on `σ`**.  The Steinhaus sibling of that lemma carries an `hσ0`;
this one does not.

**The right-hand side does not mention `n`.**  That is the whole point: every window, however far
out, contributes at most `(E‖F(σ)‖²)^q`, so the tail `∑_{|n| > N₀} (1+n²)^{-q}·(E‖F(σ)‖²)^q`
converges and the rotation is never needed there.

## What this does not do

It does not replace `RMF.integral_rpow_window_eq` on the *near* windows, where the loss from
Jensen is real and the barrier argument is what gives the saving.  It is the tail, and the tail is
**load-bearing rather than an optimisation**: without it the periodisation sum runs over all of `ℤ`
and no reach in `n` suffices.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- **The window integral is integrable in `ω`.**

The `ω`-slice of `RMF.integrable_uncurry_indicator_normSq_rademacher` at the trivial event, over
the window `(n, n+1]` instead of `(0,1]`.  Nothing here is special to length one. -/
lemma integrable_setIntegral_normSq_shiftLine_rademacher
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ0 : 0 < 1 / 2 + σ) (n : ℝ) :
    Integrable (fun ω => ∫ t in Set.Ioc n (n + 1),
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
        (shiftLine σ t) ω‖ ^ 2) ν := by
  have hInt := integrable_uncurry_indicator_normSq_rademacher hY y hσ0
    (fun _ => Set.univ) (fun _ => MeasurableSet.univ) (by simp)
    (T := Set.Ioc n (n + 1)) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  simp only [Set.indicator_univ] at hInt
  have hslice := hInt.integral_prod_left
  simpa only [Function.uncurry_apply_pair] using hslice

/-- **Fubini and height-independence collapse the window integral.**
`E ∫_n^{n+1} ‖F(σ+it)‖² dt = E ‖F(σ)‖²`, for every `n`: the window has length one, and the
`t`-integrand is constant in `t` *after* the `ω`-integral is taken
(`RMF.IsRademacherRMF.integral_normSq_shiftLine_eq`). -/
lemma integral_setIntegral_normSq_shiftLine_eq_rademacher
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ0 : 0 < 1 / 2 + σ) (n : ℝ) :
    (∫ ω, (∫ t in Set.Ioc n (n + 1),
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ∂ν)
      = ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂ν := by
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hInt := integrable_uncurry_indicator_normSq_rademacher hY y hσ0
    (fun _ => Set.univ) (fun _ => MeasurableSet.univ) (by simp)
    (T := Set.Ioc n (n + 1)) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  simp only [Set.indicator_univ] at hInt
  have hpt : ∀ t ∈ Set.Ioc n (n + 1),
      (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2 ∂ν)
        = ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
            (shiftLine σ 0) ω‖ ^ 2 ∂ν :=
    fun t _ => hf'.integral_normSq_shiftLine_eq y (σ := σ) t 0
  rw [integral_integral_swap hInt, setIntegral_congr_fun measurableSet_Ioc hpt,
    setIntegral_const, Real.volume_real_Ioc_of_le (by linarith)]
  simp

/-- **The periodisation tail, Rademacher case.**  For `q ∈ [0,1]`, **uniformly in `n`**,
`E (∫_n^{n+1} ‖F(σ+it)‖² dt)^q ≤ (E ‖F(σ)‖²)^q`.  It replaces `RMF.integral_rpow_window_eq` on the
far windows with no rotation and no hypothesis on the law beyond `IsRademacherPrimeValues`: Jensen
(`RMF.integral_rpow_le_rpow_integral`), with side conditions from
`RMF.integrable_setIntegral_normSq_shiftLine_rademacher` and `RMF.integrable_rpow_of_integrable`. -/
lemma integral_rpow_setIntegral_normSq_shiftLine_le_rademacher
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ0 : 0 < 1 / 2 + σ) (n : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, (∫ t in Set.Ioc n (n + 1),
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      ≤ (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂ν) ^ q := by
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  have hg := integrable_setIntegral_normSq_shiftLine_rademacher hY y hσ0 n
  have hnn : ∀ᵐ ω ∂ν, (∫ t in Set.Ioc n (n + 1),
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
        (shiftLine σ t) ω‖ ^ 2) ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall fun ω =>
      setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity
  have hgq := integrable_rpow_of_integrable hg (hnn.mono fun ω h => h) hq0 hq1
  refine le_trans (integral_rpow_le_rpow_integral hq0 hq1 hnn hg hgq) (le_of_eq ?_)
  rw [integral_setIntegral_normSq_shiftLine_eq_rademacher hY y hσ0 n]

end RMF
