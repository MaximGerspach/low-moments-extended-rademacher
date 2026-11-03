/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ChaosFirstMoment
import RMF.Probability.RademacherFirstMoment
import RMF.Probability.RademacherRestrictedFirstMoment
import RMF.Probability.RademacherPeriodisation

/-!
# The chaos first moment, for the Rademacher random multiplicative function

The Rademacher counterpart of `RMF/Probability/ChaosFirstMoment.lean`: Hamdan's Proposition 2.1
(Hamdan, arXiv:2604.05563), `E[Z²(A)] ≪ \min\{1, a/√(n-r)\}`, for the squarefree Euler product.
The chaos definitions are law-free and reused from there.  This file holds:

* integrability, the mean chaos, and Mertens through `∏_{p<N}(1 + 1/p) ≤ ∏_{p<N}(1 - 1/p)⁻¹`;
* the decomposition over `(w, w+1]`, and the periodisation tail;
* the height cut: Harper's Proposition 6 (Harper, arXiv:1703.06654, §3.3) needs the block offset
  to grow as the height tends to `0`, so the good set carries `RMF.harperDt D₀ h`, and the window
  is cut at `e^{-L/3}`, `L = log log x`;
* the resulting bound at a shifted abscissa, with the top `d` blocks dropped and the level rising
  along the height bands
  (`RMF.exists_const_integral_restrictedChaosUnitShift_raise_le_rademacher_of_drop`).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RMF

/-- **The Rademacher Euler-product second moment is antitone in the shift.**
`∫‖F(1/2+σ)‖² = ∏_{p<N}(1 + p^{-1-2σ})` exactly
(`RMF.IsRademacherRMF.integral_norm_randomEulerProduct_sq'`), and each factor decreases in `σ`,
so moving off the critical line in the direction the lower reduction moves costs nothing.  The
Steinhaus counterpart is `RMF.integral_normSq_shiftLine_mono`, with factors `(1 - p^{-1-2σ})⁻¹`. -/
lemma integral_normSq_shiftLine_mono_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (N : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) N
        (shiftLine σ 0) ω‖ ^ 2 ∂ν)
      ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) N
        (shiftLine 0 0) ω‖ ^ 2 ∂ν := by
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  rw [hf'.integral_norm_randomEulerProduct_sq' N (shiftLine σ 0),
    hf'.integral_norm_randomEulerProduct_sq' N (shiftLine 0 0)]
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have : (0 : ℝ) ≤ (p : ℝ) ^ (-2 * (shiftLine σ 0).re) :=
      Real.rpow_nonneg (by linarith) _
    linarith
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
    have hexp : -2 * (shiftLine σ 0).re ≤ -2 * (shiftLine 0 0).re := by
      rw [re_shiftLine, re_shiftLine]
      linarith
    have := Real.rpow_le_rpow_of_exponent_le hp1 hexp
    linarith

/-! ### The mean chaos, and the shifted abscissa

`RMF.restrictedChaosUnitShift`, `RMF.chaosUnitShift`, `RMF.restrictedChaosUnitShift_univ` and
`RMF.integral_restrictedChaosUnitShift_eq` are all **law-free** and reused verbatim.  Only the
four statements below see the law, and each sees it through
`RMF.integrable_uncurry_indicator_normSq_rademacher` or through
`RMF.IsRademacherRMF.integral_normSq_shiftLine_eq`. -/

/-- **The restricted chaos at a shifted abscissa is integrable**, by the same Tonelli slice as at
`σ = 0`.  The mirror of `RMF.integrable_restrictedChaosUnitShift`. -/
lemma integrable_restrictedChaosUnitShift_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (x σ : ℝ)
    (hσ0 : 0 < 1 / 2 + σ)
    (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {p : Ω' × ℝ | p.1 ∈ L p.2}) :
    Integrable (restrictedChaosUnitShift
      (fun ω => squarefreeExtension fun p => Y p ω) x σ L) ν := by
  have hInt := integrable_uncurry_indicator_normSq_rademacher hY (⌊x⌋₊ + 1) hσ0
    L hLmeas hSmeas (T := Set.Ioc (0 : ℝ) 1)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hslice := hInt.integral_prod_left
  simp only [Function.uncurry_apply_pair] at hslice
  have hrw : restrictedChaosUnitShift
      (fun ω => squarefreeExtension fun p => Y p ω) x σ L
      = fun ω => (Real.log x)⁻¹ * ∫ t in Set.Ioc (0 : ℝ) 1, Set.indicator (L t)
          (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
            (shiftLine σ t) ω‖ ^ 2) ω := by
    funext ω
    rw [restrictedChaosUnitShift, intervalIntegral.integral_of_le (by norm_num)]
  rw [hrw]
  exact hslice.const_mul _

/-- **The unrestricted chaos at a shifted abscissa is integrable**, the case `G = univ`.  The
mirror of `RMF.integrable_chaosUnitShift`. -/
lemma integrable_chaosUnitShift_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (x σ : ℝ)
    (hσ0 : 0 < 1 / 2 + σ) :
    Integrable (chaosUnitShift
      (fun ω => squarefreeExtension fun p => Y p ω) x σ) ν := by
  have h := integrable_restrictedChaosUnitShift_rademacher hY x σ hσ0 (fun _ => Set.univ)
    (fun _ => MeasurableSet.univ) (by simp)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  exact restrictedChaosUnitShift_univ _ x σ ω

/-- **The restricted chaos on the window `[n, n+1]` is integrable.**  The window form of
`RMF.integrable_restrictedChaosUnitShift_rademacher`; the underlying Tonelli slice
`RMF.integrable_uncurry_indicator_normSq_rademacher` already carries the interval `T` as a
parameter, so only the instantiation changes. -/
lemma integrable_restrictedChaosWindowShift_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (x σ n : ℝ)
    (hσ0 : 0 < 1 / 2 + σ)
    (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {p : Ω' × ℝ | p.1 ∈ L p.2}) :
    Integrable (restrictedChaosWindowShift
      (fun ω => squarefreeExtension fun p => Y p ω) x σ n L) ν := by
  have hInt := integrable_uncurry_indicator_normSq_rademacher hY (⌊x⌋₊ + 1) hσ0
    L hLmeas hSmeas (T := Set.Ioc n (n + 1))
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hslice := hInt.integral_prod_left
  simp only [Function.uncurry_apply_pair] at hslice
  have hrw : restrictedChaosWindowShift
      (fun ω => squarefreeExtension fun p => Y p ω) x σ n L
      = fun ω => (Real.log x)⁻¹ * ∫ t in Set.Ioc n (n + 1), Set.indicator (L t)
          (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
            (shiftLine σ t) ω‖ ^ 2) ω := by
    funext ω
    rw [restrictedChaosWindowShift, intervalIntegral.integral_of_le (by linarith)]
  rw [hrw]
  exact hslice.const_mul _

/-- **The unrestricted chaos on the window `[n, n+1]` is integrable**, the case `G = univ`. -/
lemma integrable_chaosWindowShift_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (x σ n : ℝ)
    (hσ0 : 0 < 1 / 2 + σ) :
    Integrable (chaosWindowShift
      (fun ω => squarefreeExtension fun p => Y p ω) x σ n) ν := by
  have h := integrable_restrictedChaosWindowShift_rademacher hY x σ n hσ0
    (fun _ => Set.univ) (fun _ => MeasurableSet.univ) (by simp)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  exact restrictedChaosWindowShift_univ _ x σ n ω

/-! ### The periodisation tail, in the windowed chaos

`RMF.integral_rpow_setIntegral_normSq_shiftLine_le_rademacher` bounds

  `E (∫_n^{n+1} ‖F(σ+it)‖² dt)^q ≤ (E ‖F(σ)‖²)^q`  for `q ∈ [0,1]`, **uniformly in `n`**,

with no rotation; on the far windows, where a uniform bound suffices, it replaces
`RMF.integral_rpow_window_eq`.  Here it is read through `RMF.chaosWindowShift`; the normalisation
is the only work, `((ℓog x)⁻¹ · S)^q = ((ℓog x)⁻¹)^q · S^q` by `Real.mul_rpow`. -/

/-- **The periodisation tail, in the windowed chaos.**  For `q ∈ [0,1]` and every `n`,
`E[(Z²_{[n,n+1]})^q] ≤ ((ℓog x)⁻¹E‖F(1/2+σ)‖²)^q`: the right-hand side does not mention `n`. -/
lemma integral_rpow_chaosWindowShift_le_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) {x : ℝ} (hx : 1 < x)
    {σ : ℝ} (hσ0 : 0 < 1 / 2 + σ) (n : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ n ω ^ q ∂ν)
      ≤ ((Real.log x)⁻¹ * ∫ ω, ‖randomEulerProduct
          (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
            (shiftLine σ 0) ω‖ ^ 2 ∂ν) ^ q := by
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  have hlog : (0 : ℝ) ≤ (Real.log x)⁻¹ := inv_nonneg.2 (Real.log_nonneg hx.le)
  set S : Ω' → ℝ := fun ω => ∫ t in Set.Ioc n (n + 1),
    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
      (shiftLine σ t) ω‖ ^ 2 with hSdef
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω =>
    setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity
  have hrw : ∀ ω, chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ n ω
      = (Real.log x)⁻¹ * S ω := by
    intro ω
    rw [chaosWindowShift, hSdef, intervalIntegral.integral_of_le (by linarith)]
  have hZ0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProduct
      (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν :=
    integral_nonneg fun ω => by positivity
  have htail :=
    integral_rpow_setIntegral_normSq_shiftLine_le_rademacher hY (⌊x⌋₊ + 1) hσ0 n hq0 hq1
  calc (∫ ω, chaosWindowShift
          (fun ω => squarefreeExtension fun p => Y p ω) x σ n ω ^ q ∂ν)
      = ∫ ω, ((Real.log x)⁻¹) ^ q * S ω ^ q ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        dsimp only
        rw [hrw ω, Real.mul_rpow hlog (hS0 ω)]
    _ = ((Real.log x)⁻¹) ^ q * ∫ ω, S ω ^ q ∂ν := integral_const_mul _ _
    _ ≤ ((Real.log x)⁻¹) ^ q * (∫ ω, ‖randomEulerProduct
          (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
            (shiftLine σ 0) ω‖ ^ 2 ∂ν) ^ q :=
        mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg hlog q)
    _ = _ := (Real.mul_rpow hlog hZ0).symm

/-! ### The decomposition over the half-open window `(w, w+1]`

The Steinhaus chain decomposes the chaos against bad sets indexed by `Set.Ico 0 1`.  **The
Rademacher chain cannot**: its measure bounds exclude `h = 0`, because the block variance and the
block drift both see the height; Harper's `c(t, t_j - t, p)` is `3/2` at `t = t_j = 0` and
averages `1` over the primes away from `0` (Harper, arXiv:1703.06654, §3.3).  The forms below are
therefore stated over the half-open windows `(w, w+1]`.

They cost nothing: `RMF.chaosWindowShift` integrates `h` over `(w)..(w+1)`, whose a.e. index set
is `Set.uIoc w (w+1) = Set.Ioc w (w+1)`, so no almost-everywhere step is needed.  The lemmas are
law-free. -/

/-- On the window `(w, w+1]` the restricted chaos is the chaos, at every `ω` that lies in `G h`
for all `h ∈ (w, w+1]`. -/
lemma restrictedChaosWindowShift_eq_of_forall_mem_Ioc {Ω' : Type*}
    {f : Ω' → ArithmeticFunction ℂ} {y σ w : ℝ} (G : ℝ → Set Ω') {ω : Ω'}
    (hω : ∀ h ∈ Set.Ioc w (w + 1), ω ∈ G h) :
    restrictedChaosWindowShift f y σ w G ω = chaosWindowShift f y σ w ω := by
  rw [restrictedChaosWindowShift, chaosWindowShift]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with h hmem
  rw [Set.uIoc_of_le (by linarith : w ≤ w + 1)] at hmem
  exact Set.indicator_of_mem (hω h hmem) _

/-- The chaos on the window `(w, w+1]` is at most the restricted chaos plus the chaos on the
event that `ω ∉ G h` for some `h ∈ (w, w+1]`. -/
lemma chaosWindowShift_le_restricted_add_Ioc {Ω' : Type*}
    {f : Ω' → ArithmeticFunction ℂ} {y : ℝ} (hy : 1 < y) (σ w : ℝ) (G : ℝ → Set Ω') (ω : Ω') :
    chaosWindowShift f y σ w ω
      ≤ restrictedChaosWindowShift f y σ w G ω
        + Set.indicator {ω | ∃ h ∈ Set.Ioc w (w + 1), ω ∉ G h} (fun _ => (1 : ℝ)) ω
          * chaosWindowShift f y σ w ω := by
  by_cases hmem : ω ∈ {ω | ∃ h ∈ Set.Ioc w (w + 1), ω ∉ G h}
  · rw [Set.indicator_of_mem hmem, one_mul]
    linarith [restrictedChaosWindowShift_nonneg (f := f) hy σ w G ω]
  · rw [Set.indicator_of_notMem hmem, zero_mul, add_zero]
    refine le_of_eq
      (restrictedChaosWindowShift_eq_of_forall_mem_Ioc G fun h hh => ?_).symm
    by_contra hc
    exact hmem ⟨h, hh, hc⟩

/-- **The decomposition of the chaos over the good sets `G r, …, G m`**, on the window
`(w, w+1]`: it lets the chaos bound be read on every unit window, not only on `(0, 1]`. -/
theorem chaosWindowShift_le_decomposition_Ioc {Ω' : Type*}
    {f : Ω' → ArithmeticFunction ℂ} {y : ℝ} (hy : 1 < y) (σ w : ℝ)
    (G : ℕ → ℝ → Set Ω') (ω : Ω') (r m : ℕ) (hrm : r ≤ m) :
    chaosWindowShift f y σ w ω
      ≤ restrictedChaosWindowShift f y σ w (G r) ω
        + (∑ j ∈ Finset.Ico r m,
            Set.indicator {ω | ∃ h ∈ Set.Ioc w (w + 1), ω ∉ G j h} (fun _ => (1 : ℝ)) ω
              * restrictedChaosWindowShift f y σ w (G (j + 1)) ω)
        + Set.indicator {ω | ∃ h ∈ Set.Ioc w (w + 1), ω ∉ G m h} (fun _ => (1 : ℝ)) ω
            * chaosWindowShift f y σ w ω := by
  refine le_add_sum_add_of_le_add_mul (Z := chaosWindowShift f y σ w ω)
    (R := fun j => restrictedChaosWindowShift f y σ w (G j) ω)
    (I := fun j => Set.indicator {ω | ∃ h ∈ Set.Ioc w (w + 1), ω ∉ G j h}
      (fun _ => (1 : ℝ)) ω)
    ?_ ?_ ?_ (fun j => chaosWindowShift_le_restricted_add_Ioc hy σ w (G j) ω) r m hrm
  · have hlog : (0 : ℝ) < Real.log y := Real.log_pos hy
    exact mul_nonneg (inv_nonneg.2 hlog.le)
      (intervalIntegral.integral_nonneg (by linarith) fun h _ => by positivity)
  · exact fun j => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  · exact fun j => Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le_one)

/-- **The mean chaos at a shifted abscissa.**  The mirror of `RMF.integral_chaosUnitShift_eq`. -/
lemma integral_chaosUnitShift_eq_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (x σ : ℝ)
    (hσ0 : 0 < 1 / 2 + σ) :
    (∫ ω, chaosUnitShift (fun ω => squarefreeExtension fun p => Y p ω) x σ ω ∂ν)
      = (Real.log x)⁻¹ * ∫ ω, ‖randomEulerProduct
          (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν := by
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hInt := integrable_uncurry_indicator_normSq_rademacher hY (⌊x⌋₊ + 1) hσ0
    (fun _ => Set.univ) (fun _ => MeasurableSet.univ) (by simp)
    (T := Set.Ioc (0 : ℝ) 1) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      (∫ ω, Set.indicator (Set.univ : Set Ω')
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
          (shiftLine σ t) ω‖ ^ 2) ω ∂ν)
        = ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
            (shiftLine σ 0) ω‖ ^ 2 ∂ν := by
    intro t _
    simp only [Set.indicator_univ]
    exact hf'.integral_normSq_shiftLine_eq (⌊x⌋₊ + 1) (σ := σ) t 0
  have hrw : (∫ ω, chaosUnitShift
        (fun ω => squarefreeExtension fun p => Y p ω) x σ ω ∂ν)
      = ∫ ω, restrictedChaosUnitShift
          (fun ω => squarefreeExtension fun p => Y p ω) x σ (fun _ => Set.univ) ω ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (restrictedChaosUnitShift_univ _ x σ ω).symm)
  rw [hrw, integral_restrictedChaosUnitShift_eq]
  congr 1
  rw [integral_integral_swap hInt, setIntegral_congr_fun measurableSet_Ioc hpt,
    setIntegral_const, Real.volume_real_Ioc]
  simp

/-! ### Mertens, in the form the normalisation needs

The Steinhaus second moment on the critical line is `∏_{p<N} (1 - 1/p)⁻¹`, which
`RMF.exists_abs_log_prod_primesBelow_sub_log_log_le` bounds by `e^{C_M} log⌊x⌋`.  The Rademacher one
is `∏_{p<N} (1 + 1/p)` — a **different product**, and the one place in this module where that could
have cost new number theory.

It does not, because `(1 + t)(1 - t) = 1 - t² ≤ 1` gives `1 + t ≤ (1 - t)⁻¹` on `[0, 1)`, so
`∏ (1 + 1/p) ≤ ∏ (1 - 1/p)⁻¹` and the same Mertens input serves. -/

/-- `1 + t ≤ (1 - t)⁻¹` on `[0, 1)`, from `(1 + t)(1 - t) = 1 - t² ≤ 1`.  This is what lets the
Rademacher Euler factor be compared to the Steinhaus one term by term. -/
lemma one_add_le_inv_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : 1 + t ≤ (1 - t)⁻¹ := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have key : (1 + t) * (1 - t) ≤ 1 := by nlinarith [sq_nonneg t]
  have hle := mul_le_mul_of_nonneg_right key (inv_nonneg.2 h1t.le)
  rw [one_mul] at hle
  calc 1 + t = (1 + t) * (1 - t) * (1 - t)⁻¹ := by field_simp
    _ ≤ (1 - t)⁻¹ := hle

/-- **Mertens, in the form the normalisation needs**, for the Rademacher RMF:
`(log x)⁻¹ E‖F_x(1/2)‖²` is bounded by an absolute constant.  The mirror of
`RMF.exists_const_inv_log_mul_integral_normSq_le`: the Rademacher product `∏ (1 + 1/p)` is
dominated term by term by the Steinhaus `∏ (1 - 1/p)⁻¹`, so the same Mertens input applies. -/
lemma exists_const_inv_log_mul_integral_normSq_le_rademacher :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
      IsRademacherPrimeValues Y ν → ∀ x : ℝ, 2 ≤ x →
        (Real.log x)⁻¹ * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊x⌋₊ + 1) (shiftLine 0 0) ω‖ ^ 2 ∂ν ≤ C := by
  obtain ⟨CM, hCM, hM⟩ := exists_abs_log_prod_primesBelow_sub_log_log_le
  refine ⟨Real.exp CM, Real.exp_pos _, ?_⟩
  intro Ω' _ Y ν hY x hx
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hN2' : (2 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN2
  have hNx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlogN : (0 : ℝ) < Real.log ((⌊x⌋₊ : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hlogx : Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log x := Real.log_le_log (by linarith) hNx
  have hlogx0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le hlogN hlogx
  -- the Rademacher second moment is `∏ (1 + 1/p)`
  have hprod : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
      (⌊x⌋₊ + 1) (shiftLine 0 0) ω‖ ^ 2 ∂ν)
      = ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + ((p : ℝ))⁻¹) := by
    rw [hf'.integral_norm_randomEulerProduct_sq' (⌊x⌋₊ + 1) (shiftLine 0 0)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [re_shiftLine, show (-2 : ℝ) * (1 / 2 + 0) = -1 by ring, Real.rpow_neg_one]
  -- dominated term by term by the Steinhaus product
  have hstep : (∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + ((p : ℝ))⁻¹))
      ≤ ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 - ((p : ℝ))⁻¹)⁻¹ := by
    refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    exact one_add_le_inv_one_sub (by positivity) (by linarith)
  have hppos : (0 : ℝ) < ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 - ((p : ℝ))⁻¹)⁻¹ := by
    refine Finset.prod_pos fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    exact inv_pos.2 (by linarith)
  -- Mertens bounds the Steinhaus product by `e^{C_M} log⌊x⌋`
  have hMx := abs_le.1 (hM ⌊x⌋₊ hN2)
  have hbound : (∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 - ((p : ℝ))⁻¹)⁻¹)
      ≤ Real.exp CM * Real.log ((⌊x⌋₊ : ℕ) : ℝ) := by
    have hle : Real.log (∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 - ((p : ℝ))⁻¹)⁻¹)
        ≤ CM + Real.log (Real.log ((⌊x⌋₊ : ℕ) : ℝ)) := by linarith [hMx.2]
    have h := Real.exp_le_exp.2 hle
    rwa [Real.exp_log hppos, Real.exp_add, Real.exp_log hlogN] at h
  rw [hprod, inv_mul_eq_div, div_le_iff₀ hlogx0]
  nlinarith [Real.exp_pos CM, hstep, hbound, hlogx]

/-- **The same, off the critical line.**  The shift enters the second moment only through the
Mertens product, where it can only help.  The mirror of
`RMF.exists_const_inv_log_mul_integral_normSq_shift_le`. -/
theorem exists_const_inv_log_mul_integral_normSq_shift_le_rademacher :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
      IsRademacherPrimeValues Y ν → ∀ x σ : ℝ, 2 ≤ x → 0 ≤ σ →
        (Real.log x)⁻¹ * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν ≤ C := by
  obtain ⟨C, hC, H⟩ := exists_const_inv_log_mul_integral_normSq_le_rademacher
  refine ⟨C, hC, ?_⟩
  intro Ω' _ Y ν hY x σ hx hσ
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hlog : (0 : ℝ) ≤ (Real.log x)⁻¹ := by positivity
  refine le_trans
    (mul_le_mul_of_nonneg_left (integral_normSq_shiftLine_mono_rademacher hY _ hσ) hlog) ?_
  exact H Ω' Y ν hY x hx

/-! ### The height split, with `D` varying with the height

Harper's Proposition 6 (Harper, arXiv:1703.06654, §3.3) needs `D ≥ log(1/|t|) + (B+1)` for
`|t| ≤ 1`, so on the Rademacher side the block offset depends on the height:
`RMF.harperDt D₀ t = D₀ + ⌈log(1/|t|)⌉`.  The Steinhaus chain fixes one `D`.

Write `m` for `harperBlockCount D₀ x - r` and cut the window at `h = e^{-K}`:

* **above the cut** `⌈log(1/h)⌉ ≤ K`, so for `2K ≤ m` the block count is at least `m/2` and
  `min\{1, a/√·\}` grows by at most `√2` (`RMF.min_one_div_sqrt_le_of_half_le`);
* **below the cut** the indicator is at most `1` and the region has measure `e^{-K}`, itself at
  most `min\{1, a/√m\}` with constant `1` (`RMF.exp_neg_third_le_min_one_div_sqrt` at `K = L/3`,
  `L = log log x`).

So the split costs `√2 + 1`, and no dyadic decomposition is needed. -/

/-- **Above the cut.**  Halving the block count costs a factor `√2` in `min\{1, a/√·\}`. -/
lemma min_one_div_sqrt_le_of_half_le {M M' a : ℝ} (hM : 0 < M) (hM' : 0 < M')
    (hhalf : M / 2 ≤ M') (ha : 0 ≤ a) :
    min 1 (a / Real.sqrt M') ≤ Real.sqrt 2 * min 1 (a / Real.sqrt M) := by
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by linarith
  have hsM : (0 : ℝ) < Real.sqrt M := Real.sqrt_pos.2 hM
  have hsM' : (0 : ℝ) < Real.sqrt M' := Real.sqrt_pos.2 hM'
  -- `√M/√2 = √(M/2) ≤ √M'`
  have hge : Real.sqrt M / Real.sqrt 2 ≤ Real.sqrt M' := by
    rw [div_le_iff₀ hs2]
    have h1 : Real.sqrt M ≤ Real.sqrt (M' * 2) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_mul hM'.le] at h1
  have hkey : a / Real.sqrt M' ≤ Real.sqrt 2 * (a / Real.sqrt M) := by
    have h1 : a / Real.sqrt M' ≤ a / (Real.sqrt M / Real.sqrt 2) :=
      div_le_div_of_nonneg_left ha (by positivity) hge
    calc a / Real.sqrt M' ≤ a / (Real.sqrt M / Real.sqrt 2) := h1
      _ = Real.sqrt 2 * (a / Real.sqrt M) := by field_simp
  rcases le_or_gt (a / Real.sqrt M) 1 with hv | hv
  · calc min 1 (a / Real.sqrt M') ≤ a / Real.sqrt M' := min_le_right _ _
      _ ≤ Real.sqrt 2 * (a / Real.sqrt M) := hkey
      _ = Real.sqrt 2 * min 1 (a / Real.sqrt M) := by rw [min_eq_right hv]
  · calc min 1 (a / Real.sqrt M') ≤ 1 := min_le_left _ _
      _ ≤ Real.sqrt 2 * 1 := by linarith
      _ = Real.sqrt 2 * min 1 (a / Real.sqrt M) := by rw [min_eq_left hv.le]

/-- **The per-band bound when the level rises with the band.**  If `M/2 ≤ M'` and `a ≥ 1`, then
`min{1, (a+k)/√M'} ≤ (k+1)·√2·min{1, a/√M}`.  `a + k ≤ (k+1)a` spends `a ≥ 1`, which is why the
band factor is `k+1` rather than growing with `a`; `RMF.min_one_le_mul_min_one` moves it outside
the `min`, and `RMF.min_one_div_sqrt_le_of_half_le` pays `√2`.  The factor `k+1` is summable
against the band widths `e^{-k}`, so no head/tail split is needed. -/
lemma min_one_div_sqrt_raise_le {M M' a : ℝ} {k : ℕ} (hM : 0 < M) (hM' : 0 < M')
    (hhalf : M / 2 ≤ M') (ha1 : 1 ≤ a) :
    min 1 ((a + (k : ℝ)) / Real.sqrt M')
      ≤ ((k : ℝ) + 1) * (Real.sqrt 2 * min 1 (a / Real.sqrt M)) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hsq' : (0 : ℝ) < Real.sqrt M' := Real.sqrt_pos.2 hM'
  have hK : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hnum : a + (k : ℝ) ≤ ((k : ℝ) + 1) * a := by nlinarith
  have hdiv : (a + (k : ℝ)) / Real.sqrt M' ≤ ((k : ℝ) + 1) * (a / Real.sqrt M') := by
    rw [← mul_div_assoc]
    gcongr
  refine le_trans (min_one_le_mul_min_one hK hdiv) ?_
  have hbase := min_one_div_sqrt_le_of_half_le hM hM' hhalf (by linarith : (0 : ℝ) ≤ a)
  exact mul_le_mul_of_nonneg_left hbase (by linarith)

/-! ### The band factor, integrated in `h`

The per-band bound `RMF.min_one_div_sqrt_raise_le` costs a factor `k + 1` on the band where
`RMF.harperDt D₀ h = D₀ + k`, i.e. `k = ⌈ℓog(1/h)⌉`.  The chaos bound integrates that factor over
`h ∈ (0, 1]`, and decomposing the integral over the bands is **not needed**: pointwise
`⌈ℓog(1/h)⌉ + 1 ≤ ℓog(1/h) + 2`, and `ℓog(1/·)` is integrable on `(0,1]` with integral `1`.

So the step function never has to be integrated, only dominated, which also avoids proving
`Nat.ceil` measurable. -/

/-- `⌈ℓog(1/h)⌉ + 1 ≤ ℓog(1/h) + 2` on `(0, 1]` — the band factor, dominated by a smooth
function. -/
lemma ceil_log_one_div_add_one_le {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) :
    ((⌈Real.log (1 / h)⌉₊ : ℝ) + 1) ≤ Real.log (1 / h) + 2 := by
  have hnn : 0 ≤ Real.log (1 / h) := by
    rw [one_div, Real.log_inv, neg_nonneg]
    exact Real.log_nonpos hh0.le hh1
  have h1 := Nat.ceil_lt_add_one hnn
  linarith

/-- **The dominating function integrates to `3`.**  `∫₀¹ (ℓog(1/h) + 2) dh = 1 + 2`, so the band
factor costs an absolute constant and nothing that grows with `x`. -/
lemma integral_log_one_div_add_two :
    (∫ h in (0 : ℝ)..1, (Real.log (1 / h) + 2)) = 3 := by
  have hrw : ∀ h : ℝ, Real.log (1 / h) + 2 = -Real.log h + 2 := by
    intro h
    rw [one_div, Real.log_inv]
  have hlog : (∫ h in (0 : ℝ)..1, Real.log h) = -1 := by
    rw [integral_log]
    simp
  calc (∫ h in (0 : ℝ)..1, (Real.log (1 / h) + 2))
      = ∫ h in (0 : ℝ)..1, (-Real.log h + 2) := by simp_rw [hrw]
    _ = (∫ h in (0 : ℝ)..1, -Real.log h) + ∫ _h in (0 : ℝ)..1, (2 : ℝ) :=
        intervalIntegral.integral_add
          (IntervalIntegrable.neg intervalIntegral.intervalIntegrable_log')
          intervalIntegrable_const
    _ = 3 := by
        rw [intervalIntegral.integral_neg, hlog, intervalIntegral.integral_const]
        norm_num

/-- **The band factor's majorant is integrable on `(0, 1]`**, the range
`RMF.integral_restrictedChaosUnitShift_eq` rewrites the chaos to.  `IntervalIntegrable` on `[0,1]`
is by definition integrability on `Set.Ioc 0 1`, so the conversion is one iff. -/
lemma integrableOn_log_one_div_add_two :
    IntegrableOn (fun h : ℝ => Real.log (1 / h) + 2) (Set.Ioc (0 : ℝ) 1) := by
  have hlog : IntervalIntegrable (fun h : ℝ => Real.log h) MeasureTheory.volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'
  have h1 : IntervalIntegrable (fun h : ℝ => Real.log (1 / h) + 2)
      MeasureTheory.volume 0 1 := by
    have h2 := (IntervalIntegrable.neg hlog).add
      (intervalIntegrable_const (c := (2 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))
    simpa only [one_div, Real.log_inv, Pi.neg_apply] using h2
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 h1

/-- **And it integrates to `3` there.**  `RMF.integral_log_one_div_add_two` on `Set.Ioc 0 1`. -/
lemma setIntegral_log_one_div_add_two :
    (∫ h in Set.Ioc (0 : ℝ) 1, (Real.log (1 / h) + 2)) = 3 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_log_one_div_add_two

/-- **Below the cut, at the threshold `e^{-L/3}`.**  For a block count `1 ≤ M ≤ L` and `a ≥ 1`,
`e^{-L/3} ≤ min\{1, a/√M\}`, with constant `1`: `√L ≤ 1 + L/3 ≤ e^{L/3}`, the first for every
`L ≥ 0` because `u²/3 - u + 1` has negative discriminant, so no threshold on `x` is needed.
`RMF.harper_block_count_of_height` supports the cut `log(1/|t|) ≤ L/3`, and this is the form the
height split uses. -/
lemma exp_neg_third_le_min_one_div_sqrt {L M a : ℝ} (hL : 0 ≤ L) (hM1 : 1 ≤ M) (hML : M ≤ L)
    (ha : 1 ≤ a) : Real.exp (-(L / 3)) ≤ min 1 (a / Real.sqrt M) := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hsM : (0 : ℝ) < Real.sqrt M := Real.sqrt_pos.2 hM0
  have hsM1 : (1 : ℝ) ≤ Real.sqrt M := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hM1
  have hsL : Real.sqrt M ≤ Real.sqrt L := Real.sqrt_le_sqrt hML
  have hsL0 : (0 : ℝ) < Real.sqrt L := lt_of_lt_of_le hsM hsL
  -- `min 1 (a/√M) ≥ 1/√M ≥ 1/√L`
  have hmin : 1 / Real.sqrt L ≤ min 1 (a / Real.sqrt M) := by
    have h1 : 1 / Real.sqrt L ≤ 1 / Real.sqrt M := one_div_le_one_div_of_le hsM hsL
    have h2 : 1 / Real.sqrt M ≤ min 1 (a / Real.sqrt M) := by
      refine le_min ?_ ?_
      · rw [div_le_one hsM]; exact hsM1
      · gcongr
    linarith
  -- `√L ≤ 1 + L/3` for every `L ≥ 0`: `u²/3 - u + 1` has negative discriminant
  have hquad : Real.sqrt L ≤ 1 + L / 3 := by
    have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL
    nlinarith [Real.sqrt_nonneg L, sq_nonneg (Real.sqrt L - 3 / 2)]
  have hexp : Real.sqrt L ≤ Real.exp (L / 3) := by
    linarith [Real.add_one_le_exp (L / 3)]
  have hstep : Real.exp (-(L / 3)) ≤ 1 / Real.sqrt L := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), one_div, inv_inv]
    exact hexp
  linarith

/-! ### `harperDt`'s level sets are intervals

**`RMF.harperDt D₀ t` is a natural number**, so on `(0, 1]` it takes countably many values, and
each level set is an interval.  That makes the varying-`D` integrand tractable: every link of the
chain fixes one `D`, and because `D(t)` is a step function the height window splits into intervals
on each of which `D` is constant, so the fixed-`D` results apply on each piece.

Above the cut `log(1/t) ≤ L/3` only finitely many levels occur (`k ≤ L/3 + 1`), so the
decomposition is finite, and since the pieces are disjoint subsets of `(0, 1]` their measures sum
to at most `1`: the `√2` of `RMF.min_one_div_sqrt_le_of_half_le` is paid once, not per piece. -/

/-- **The level sets of `RMF.harperDt` are intervals.**  `harperDt D₀ t = D₀ + k` exactly when
`t ∈ [e^{-k}, e^{-(k-1)})`, for `k ≥ 1` and `t > 0`. -/
lemma harperDt_eq_add_iff {D₀ k : ℕ} (hk : k ≠ 0) {t : ℝ} (ht0 : 0 < t) :
    harperDt D₀ t = D₀ + k ↔
      Real.exp (-(k : ℝ)) ≤ t ∧ t < Real.exp (-((k : ℝ) - 1)) := by
  have hinv : (0 : ℝ) < 1 / t := by positivity
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk
    push_cast [Nat.cast_sub hk1]
    ring
  have hlog : Real.log (1 / t) = -Real.log t := by
    rw [one_div, Real.log_inv]
  rw [harperDt, add_right_inj, abs_of_pos ht0, Nat.ceil_eq_iff hk, hcast, hlog]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [← Real.le_log_iff_exp_le ht0]
      linarith
    · rw [← Real.log_lt_iff_lt_exp ht0]
      linarith
  · rintro ⟨h1, h2⟩
    rw [← Real.le_log_iff_exp_le ht0] at h1
    rw [← Real.log_lt_iff_lt_exp ht0] at h2
    exact ⟨by linarith, by linarith⟩

/-! ### Joint measurability at a height-dependent offset

`RMF.measurableSet_freeStartBarrierAdd_uncurry` fixes the block offset and the count; here both
move with the height, through `RMF.harperDt D₀ t`.  The set is the countable union over `d : ℕ` of
the fixed-`D` set at `D = d` intersected with the fibre `\{q | harperDt D₀ q.2 = d\}`.  On each
fibre the offset and the count are constants, so the fixed-`D` lemma applies, and the fibre is
measurable because `harperDt D₀` is a measurable `ℝ → ℕ` map. -/

/-- `RMF.harperDt D₀` is measurable as a map `ℝ → ℕ`.  Every ingredient is: `|·|`, `1/·`,
`Real.log`, `Nat.ceil`, and adding a constant natural number. -/
lemma measurable_harperDt (D₀ : ℕ) : Measurable (harperDt D₀) := by
  have hceil : Measurable fun t : ℝ => ⌈Real.log (1 / |t|)⌉₊ :=
    Nat.measurable_ceil.comp
      (Real.measurable_log.comp (measurable_const.div measurable_id.abs))
  exact (measurable_from_top (f := fun k : ℕ => D₀ + k)).comp hceil

/-- The fibres of `RMF.harperDt D₀`, read on `Ω' × ℝ`, are measurable. -/
lemma measurableSet_harperDt_fibre {Ω' : Type*} [MeasurableSpace Ω'] (D₀ d : ℕ) :
    MeasurableSet {q : Ω' × ℝ | harperDt D₀ q.2 = d} := by
  have hpre : {q : Ω' × ℝ | harperDt D₀ q.2 = d}
      = (fun q : Ω' × ℝ => harperDt D₀ q.2) ⁻¹' {d} := rfl
  rw [hpre]
  exact ((measurable_harperDt D₀).comp measurable_snd) MeasurableSet.of_discrete

/-- **The free-start barrier at the height-dependent offset, jointly measurable**, with the top
`k` blocks dropped and the start `r` and the bounds `u, v` indexed by the offset.  On the fibre
`\{q | harperDt D₀ q.2 = D\}` these are constants, which is all the proof needs.  The raised-level
good set needs this form, since its start and its `Icc` move with the height. -/
lemma measurableSet_freeStartBarrierAdd_uncurry_harperDt_raise {Ω' : Type*}
    [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    (hY : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)))
    (σ x : ℝ) (D₀ k : ℕ) (r : ℕ → ℕ) (u v : ℕ → ℕ → ℝ) :
    MeasurableSet {q : Ω' × ℝ | q.1 ∈ {ω | ∀ j, r (harperDt D₀ q.2) ≤ j →
      j ≤ harperBlockCount (harperDt D₀ q.2) x - k →
      walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset (harperDt D₀ q.2) x) m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)))
          (Y ((p : Nat.Primes) : ℕ) ω)) j ω
        ∈ Set.Icc (u (harperDt D₀ q.2) j) (v (harperDt D₀ q.2) j)}} := by
  have hrw : {q : Ω' × ℝ | q.1 ∈ {ω | ∀ j, r (harperDt D₀ q.2) ≤ j →
      j ≤ harperBlockCount (harperDt D₀ q.2) x - k →
      walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset (harperDt D₀ q.2) x) m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)))
          (Y ((p : Nat.Primes) : ℕ) ω)) j ω
        ∈ Set.Icc (u (harperDt D₀ q.2) j) (v (harperDt D₀ q.2) j)}}
      = ⋃ D : ℕ, ({q : Ω' × ℝ | q.1 ∈ {ω | ∀ j, r D ≤ j →
            j ≤ harperBlockCount D x - k →
            walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
              localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)))
                (Y ((p : Nat.Primes) : ℕ) ω)) j ω
              ∈ Set.Icc (u D j) (v D j)}}
          ∩ {q : Ω' × ℝ | harperDt D₀ q.2 = D}) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨harperDt D₀ q.2, h, rfl⟩
    · rintro ⟨D, hmem, hD⟩
      rw [hD]
      exact hmem
  rw [hrw]
  refine MeasurableSet.iUnion fun D => ?_
  exact (measurableSet_freeStartBarrierAdd_uncurry hY σ (harperOffset D x) (r D)
    (harperBlockCount D x - k) (u D) (v D)).inter (measurableSet_harperDt_fibre D₀ D)

/-! ### The cut

`RMF.exists_setIntegral_restricted_normSq_le_rademacher_of_offset_of_drop` is applied **pointwise
in the height**, at `D = RMF.harperDt D₀ h`, not through the height-integrated link, since within
one application of that link the offset is fixed.  The window `Ioc 0 1` is cut at
`δ = e^{-L/3}`, `L = log log x`:

* **above the cut** `log(1/h) ≤ L/3`, so `RMF.harper_block_count_of_height` supplies every count
  hypothesis at `harperDt D₀ h`, and `RMF.min_one_div_sqrt_le_of_half_le` converts the smaller
  block count back to the base one at a cost of `√2`;
* **below the cut** the good set is discarded (the restricted second moment is `P'(G_h)` times the
  unrestricted one) and the piece's measure `δ` pays through
  `RMF.exp_neg_third_le_min_one_div_sqrt`, at a cost of `1`.

So the constant is `(A√2 + 1)·C_M` against the Steinhaus `A·C_M`. -/

/-- **The block-count comparison, with the top `d` blocks dropped.**  Above the cut
`ℓog(1/|h|) ≤ L/3`, `L = ℓogℓog x`, and under `4(r + D₀ + n₀ + 2d + 4) ≤ L`, the base range
`m = harperBlockCount D₀ x - r` satisfies `1 ≤ m ≤ L`, and `m/2` is at most the shortened range
`(harperBlockCount (harperDt D₀ h) x - d) - r`.  The weight `2d` is forced: the halving needs
`2⌈ℓog(1/h)⌉ + r + 2d ≤ m`.  The fourth conclusion,
`d + r ≤ harperBlockCount (harperDt D₀ h) x`, keeps the shortened range from truncating in `ℕ`. -/
lemma harperBlockCount_harperDt_bounds_of_drop {D₀ n₀ r d : ℕ} {x h : ℝ} (hr1 : 1 ≤ r)
    (hΛ : 4 * ((r : ℝ) + (D₀ : ℝ) + (n₀ : ℝ) + 2 * (d : ℝ) + 4)
      ≤ Real.log (Real.log x))
    (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hcut : Real.log (1 / |h|) ≤ Real.log (Real.log x) / 3) :
    1 ≤ (harperBlockCount D₀ x : ℝ) - r
      ∧ (harperBlockCount D₀ x : ℝ) - r ≤ Real.log (Real.log x)
      ∧ ((harperBlockCount D₀ x : ℝ) - r) / 2
          ≤ ((harperBlockCount (harperDt D₀ h) x - d : ℕ) : ℝ) - r
      ∧ d + r ≤ harperBlockCount (harperDt D₀ h) x := by
  have hr0 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hD0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have habs : |h| = h := abs_of_pos hh0
  have hlog0 : 0 ≤ Real.log (1 / |h|) :=
    log_one_div_abs_nonneg (by rw [habs]; exact hh0) (by rw [habs]; exact hh1)
  have hkR : ((⌈Real.log (1 / |h|)⌉₊ : ℕ) : ℝ) < Real.log (Real.log x) / 3 + 1 := by
    have h1 := Nat.ceil_lt_add_one hlog0
    linarith
  have hfl : Real.log (Real.log x) - 1 < ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) :=
    Nat.sub_one_lt_floor _
  have hflle : ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) ≤ Real.log (Real.log x) := Nat.floor_le hL0
  have hDfl : D₀ ≤ ⌊Real.log (Real.log x)⌋₊ := Nat.le_floor (by linarith)
  have hbase : ((harperBlockCount D₀ x : ℕ) : ℝ)
      = ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) - (D₀ : ℝ) := by
    simp only [harperBlockCount]
    exact Nat.cast_sub hDfl
  have hstep : harperBlockCount (harperDt D₀ h) x
      = harperBlockCount D₀ x - ⌈Real.log (1 / |h|)⌉₊ := by
    simp only [harperBlockCount, harperDt]
    omega
  have hcast : ((harperBlockCount D₀ x : ℕ) : ℝ) - ((⌈Real.log (1 / |h|)⌉₊ : ℕ) : ℝ)
      ≤ ((harperBlockCount (harperDt D₀ h) x : ℕ) : ℝ) := by
    rw [hstep]
    rcases le_or_gt (⌈Real.log (1 / |h|)⌉₊) (harperBlockCount D₀ x) with hle | hgt
    · rw [Nat.cast_sub hle]
    · have h0 : harperBlockCount D₀ x - ⌈Real.log (1 / |h|)⌉₊ = 0 := by omega
      have h1 : ((harperBlockCount D₀ x : ℕ) : ℝ) ≤ ((⌈Real.log (1 / |h|)⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast hgt.le
      rw [h0]
      push_cast
      linarith
  -- the drop fits inside the shortened count, which is what the threshold bought
  have hfit : ((d : ℕ) : ℝ) + (r : ℝ) ≤ ((harperBlockCount (harperDt D₀ h) x : ℕ) : ℝ) := by
    linarith
  have hfitN : d + r ≤ harperBlockCount (harperDt D₀ h) x := by exact_mod_cast hfit
  have hdle : d ≤ harperBlockCount (harperDt D₀ h) x := by omega
  have hsub : ((harperBlockCount (harperDt D₀ h) x - d : ℕ) : ℝ)
      = ((harperBlockCount (harperDt D₀ h) x : ℕ) : ℝ) - (d : ℝ) := Nat.cast_sub hdle
  exact ⟨by linarith, by linarith, by rw [hsub]; linarith, hfitN⟩

/-- **The halving at a rising level, with the level bounded by the count.**  For a band index
`k ≤ L/3 + 1`, `L = ℓogℓog x`, and `m₀ = harperBlockCount D₀ x`: the raised start fits,
`⌈(a+k)/4⌉ + d + n₀ ≤ harperBlockCount (D₀ + k) x`, and the shortened range is at least half the
base one, under `8⌈a/4⌉ ≤ m₀` and a threshold free of `a`.
`RMF.GoodFamilyAdd.integral_restricted_le` quantifies over `a` with only `2⌈a/4⌉ ≤ t`, so no
`a`-dependent threshold on `x` is available; reading the family at `t = m₀/4` turns that into
`⌈a/4⌉ ≤ m₀/8`, and then `m₀ - ⌈a/4⌉ ≥ 7m₀/8` with `m₀ > L - 1 - D₀` needs only
`L ≥ 21D₀ + 48d + 129`, which `24(D₀ + n₀ + 2d + 6) ≤ L` supplies. -/
lemma harperBlockCount_raise_halving_of_drop_of_level {D₀ n₀ k d : ℕ} {a x : ℝ} (ha1 : 1 ≤ a)
    (hR : 8 * (⌈a / 4⌉₊ : ℝ) ≤ (harperBlockCount D₀ x : ℝ))
    (hΛ : 24 * ((D₀ : ℝ) + (n₀ : ℝ) + 2 * (d : ℝ) + 6) ≤ Real.log (Real.log x))
    (hk : (k : ℝ) ≤ Real.log (Real.log x) / 3 + 1) :
    ⌈(a + (k : ℝ)) / 4⌉₊ + d + n₀ ≤ harperBlockCount (D₀ + k) x
      ∧ ((harperBlockCount D₀ x : ℝ) - (⌈a / 4⌉₊ : ℝ)) / 2
          ≤ ((harperBlockCount (D₀ + k) x - d : ℕ) : ℝ) - (⌈(a + (k : ℝ)) / 4⌉₊ : ℝ) := by
  have hr0 : (0 : ℝ) ≤ (⌈a / 4⌉₊ : ℝ) := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hceilk : ((⌈(a + (k : ℝ)) / 4⌉₊ : ℕ) : ℝ) ≤ (⌈a / 4⌉₊ : ℝ) + (k : ℝ) / 4 + 1 := by
    have hbase : (a / 4 : ℝ) ≤ (⌈a / 4⌉₊ : ℝ) := Nat.le_ceil _
    have h1 : ((⌈(a + (k : ℝ)) / 4⌉₊ : ℕ) : ℝ) < (a + (k : ℝ)) / 4 + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    linarith
  have hfl : Real.log (Real.log x) - 1 < ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) :=
    Nat.sub_one_lt_floor _
  have hflle : ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) ≤ Real.log (Real.log x) :=
    Nat.floor_le hL0
  have hDk : D₀ + k ≤ ⌊Real.log (Real.log x)⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    linarith
  have hD : D₀ ≤ ⌊Real.log (Real.log x)⌋₊ := le_trans (Nat.le_add_right _ _) hDk
  have hbase : ((harperBlockCount D₀ x : ℕ) : ℝ)
      = ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) - (D₀ : ℝ) := by
    simp only [harperBlockCount]
    exact Nat.cast_sub hD
  have hband : ((harperBlockCount (D₀ + k) x : ℕ) : ℝ)
      = ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) - (D₀ : ℝ) - (k : ℝ) := by
    simp only [harperBlockCount]
    rw [Nat.cast_sub hDk]
    push_cast
    ring
  rw [hbase] at hR
  have hfitR : ((⌈(a + (k : ℝ)) / 4⌉₊ : ℕ) : ℝ) + (d : ℝ) + (n₀ : ℝ)
      ≤ ((harperBlockCount (D₀ + k) x : ℕ) : ℝ) := by
    rw [hband]
    linarith
  have hfit : ⌈(a + (k : ℝ)) / 4⌉₊ + d + n₀ ≤ harperBlockCount (D₀ + k) x := by
    exact_mod_cast hfitR
  have hdle : d ≤ harperBlockCount (D₀ + k) x := by omega
  have hsub : ((harperBlockCount (D₀ + k) x - d : ℕ) : ℝ)
      = ((harperBlockCount (D₀ + k) x : ℕ) : ℝ) - (d : ℝ) := Nat.cast_sub hdle
  refine ⟨hfit, ?_⟩
  rw [hsub, hband, hbase]
  linarith

/-- **The per-band factor with the level bounded by the count.**  The composition of
`RMF.harperBlockCount_raise_halving_of_drop_of_level` with `RMF.min_one_div_sqrt_raise_le`, in the
form `RMF.GoodFamilyAdd.integral_restricted_le` can supply its hypotheses in. -/
lemma min_one_div_sqrt_harperBlockCount_raise_le_of_drop_of_level {D₀ n₀ k d : ℕ} {a x : ℝ}
    (ha1 : 1 ≤ a)
    (hR : 8 * (⌈a / 4⌉₊ : ℝ) ≤ (harperBlockCount D₀ x : ℝ))
    (hΛ : 24 * ((D₀ : ℝ) + (n₀ : ℝ) + 2 * (d : ℝ) + 6) ≤ Real.log (Real.log x))
    (hk : (k : ℝ) ≤ Real.log (Real.log x) / 3 + 1) :
    min 1 ((a + (k : ℝ))
        / Real.sqrt (((harperBlockCount (D₀ + k) x - d : ℕ) : ℝ)
          - (⌈(a + (k : ℝ)) / 4⌉₊ : ℝ)))
      ≤ ((k : ℝ) + 1) * (Real.sqrt 2
          * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - (⌈a / 4⌉₊ : ℝ)))) := by
  have hr0 : (0 : ℝ) ≤ (⌈a / 4⌉₊ : ℝ) := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hfl : Real.log (Real.log x) - 1 < ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) :=
    Nat.sub_one_lt_floor _
  have hD : D₀ ≤ ⌊Real.log (Real.log x)⌋₊ := by
    refine Nat.le_floor ?_
    linarith
  have hbase : ((harperBlockCount D₀ x : ℕ) : ℝ)
      = ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) - (D₀ : ℝ) := by
    simp only [harperBlockCount]
    exact Nat.cast_sub hD
  have hM : (0 : ℝ) < (harperBlockCount D₀ x : ℝ) - (⌈a / 4⌉₊ : ℝ) := by
    rw [hbase]
    rw [hbase] at hR
    linarith
  obtain ⟨-, hhalf⟩ :=
    harperBlockCount_raise_halving_of_drop_of_level (n₀ := n₀) ha1 hR hΛ hk
  have hM' : (0 : ℝ) < ((harperBlockCount (D₀ + k) x - d : ℕ) : ℝ)
      - (⌈(a + (k : ℝ)) / 4⌉₊ : ℝ) := by linarith
  exact min_one_div_sqrt_raise_le hM hM' hhalf ha1

/-! ### The band index of a height

The halving comparison and the per-band bound are stated at an abstract band index `k`.  In the
chaos bound that index is `RMF.harperDt D₀ h - D₀ = ⌈ℓog(1/|h|)⌉`, the amount by which the
height-dependent offset exceeds the base one, and it is the shift the raised good set carries in
its level, `a + (harperDt D₀ h - D₀)`.  These lemmas connect the two.

**The hypothesis `(r : ℝ) ≤ a/4 + 1` of
`RMF.exists_setIntegral_restricted_normSq_le_rademacher_of_offset_of_drop` survives.**  On band `k`
the good set starts at `r = ⌈(a+k)/4⌉`, which read at the base level would need
`⌈(a+k)/4⌉ ≤ a/4 + 1`, false for large `k`.  But the bound is applied at the raised level `a + k`,
since `RMF.harperGoodRangeAdd` takes its start `⌈a/4⌉` from the same `a` as its `Icc`, so the
hypothesis reads `⌈(a+k)/4⌉ ≤ (a+k)/4 + 1`, which is `Nat.ceil_lt_add_one`. -/

/-- **The band index.**  `RMF.harperDt D₀ h` exceeds `D₀` by exactly `⌈ℓog(1/|h|)⌉`. -/
lemma harperDt_sub_self (D₀ : ℕ) (h : ℝ) :
    harperDt D₀ h - D₀ = ⌈Real.log (1 / |h|)⌉₊ := by
  simp only [harperDt]
  omega

/-! ### The reach of the chaos bound in the height

The periodisation tail bounds every window by Jensen, uniformly in `n`, but at `n = 0` that gives
`(E‖F(σ)‖²)^q`, which after the `(ℓog x)⁻¹` normalisation is `O(1)`, while the target
`(1 + (1-q)√ℓogℓog x)^{-q}` decays.  So the near windows need the chaos bound.

Its reach is set by `D`.
`RMF.exists_setIntegral_restricted_normSq_le_rademacher_of_offset_of_drop` carries
`(2·Im s)² ≤ exp (harperOffset D x)`, and `harperOffset D x < D` (`RMF.harperOffset_lt_natCast`),
so the hypothesis forces `|h| < e^{D/2}/2`.  `D` may grow with the height: Harper's Proposition 6
(Harper, arXiv:1703.06654, §3.3) takes any natural
`D ≥ max{log(1/|t|), 2·log log(1+|t|)} + (B+1)`, while his Proposition 5, the Steinhaus analogue
(§3.2), has no `t` and runs at `D = B + 1`.  The condition here needs `D ≳ 2·log(2|t|)`;
Harper's doubly-logarithmic offset is `RMF.harperDwExp` (`RMF/Probability/StrongScales.lean`). -/

/-- **The band index below the cut.**  The hypothesis `k ≤ L/3 + 1` of
`RMF.harperBlockCount_raise_halving_of_drop_of_level`, produced from the cut
`ℓog(1/|h|) ≤ L/3`. -/
lemma harperDt_sub_le_of_cut {D₀ : ℕ} {h L : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hcut : Real.log (1 / |h|) ≤ L / 3) :
    ((harperDt D₀ h - D₀ : ℕ) : ℝ) ≤ L / 3 + 1 := by
  have habs : |h| = h := abs_of_pos hh0
  have hnn : 0 ≤ Real.log (1 / |h|) :=
    log_one_div_abs_nonneg (by rw [habs]; exact hh0) (by rw [habs]; exact hh1)
  have h1 := Nat.ceil_lt_add_one hnn
  rw [harperDt_sub_self]
  linarith

/-- **The band factor, in band-index form.**  `RMF.ceil_log_one_div_add_one_le` read at the band
index: the factor `k + 1` that `RMF.min_one_div_sqrt_raise_le` pays on band `k` is dominated by
`ℓog(1/h) + 2`, which `RMF.integral_log_one_div_add_two` integrates over `(0, 1]` to `3`. -/
lemma harperDt_sub_add_one_le {D₀ : ℕ} {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) :
    ((harperDt D₀ h - D₀ : ℕ) : ℝ) + 1 ≤ Real.log (1 / h) + 2 := by
  rw [harperDt_sub_self, abs_of_pos hh0]
  exact ceil_log_one_div_add_one_le hh0 hh1

/-! ### The mean chaos at a shifted abscissa

The Rademacher counterpart of `RMF.exists_const_integral_chaosUnitShift_le`: the shift
monotonicity composed with the Mertens bound. -/

/-- **The mean chaos at a shifted abscissa is bounded by an absolute constant**, for the Rademacher
RMF, `2 ≤ x` and `σ ≥ 0`: the mirror of `RMF.exists_const_integral_chaosUnitShift_le`.  The shift
enters only the Mertens factor, where it helps (`RMF.integral_normSq_shiftLine_mono_rademacher`).
The `σ = 0` form is not stated separately on this side. -/
theorem exists_const_integral_chaosUnitShift_le_rademacher :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
      IsRademacherPrimeValues Y ν → ∀ x σ : ℝ, 2 ≤ x → 0 ≤ σ →
        (∫ ω, chaosUnitShift (fun ω => squarefreeExtension fun p => Y p ω) x σ ω ∂ν)
          ≤ C := by
  obtain ⟨C, hC, H⟩ := exists_const_inv_log_mul_integral_normSq_shift_le_rademacher
  refine ⟨C, hC, ?_⟩
  intro Ω' _ Y ν hY x σ hx hσ
  rw [integral_chaosUnitShift_eq_rademacher hY x σ (by linarith)]
  exact H Ω' Y ν hY x σ hx hσ

/-! ### The cut at a shifted abscissa

The cut of the sections above, with `σ` threaded: every ingredient of the cut already takes an
abscissa shift.  The tilt scale is limited by the **variance bracket**:
`RMF.exists_blockMatchedVarAdd_concrete_top` brackets the Rademacher block variance only under
`η ≤ 1/10`, where the Steinhaus bracket `[exp(-2E)/4, 9/2]` degrades with `E`.  A general `E₀` is
reached by dropping the top `d` blocks with `10E₀ ≤ e^d`, which puts the tilt scale of the blocks
walked under `1/10` (`RMF.sigma_le_tenth_of_drop`). -/

/-- **The cut at a shifted abscissa with the level rising along the height bands.**  On band
`k = harperDt D₀ h - D₀` the good set sits at level `a + k`, with start `⌈(a+k)/4⌉` and envelope
`2\log j`; the top `d` blocks are dropped.  `D₀`, `a₀`, `C` and `B` do not depend on `E₀` or `d`,
only `x₀` does.  The raise costs a factor `3`, from `∫₀¹(\log(1/h) + 2) dh = 3`, in the constant
`(3A√2 + 1)C_M`.  The hypothesis on `a` is `8⌈a/4⌉ ≤ m₀` rather than a threshold on `x`, the form
`RMF.GoodFamilyAdd.integral_restricted_le` can supply; `_n₀` is unused. -/
theorem exists_const_integral_restrictedChaosUnitShift_raise_le_rademacher_of_drop :
    ∃ (D₀ _n₀ : ℕ) (a₀ C B : ℝ), 4 ≤ D₀ ∧ 0 < C ∧ 20 ≤ B ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → 10 * E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (x σ η a : ℝ),
          x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η →
          a₀ ≤ a → 1 ≤ a →
          8 * (⌈a / 4⌉₊ : ℝ) ≤ (harperBlockCount D₀ x : ℝ) →
            (∫ ω, restrictedChaosUnitShift
                (fun ω => squarefreeExtension fun p => Y p ω) x σ
                (fun h => {ω | ∀ j, ⌈(a + ((harperDt D₀ h - D₀ : ℕ) : ℝ)) / 4⌉₊ ≤ j →
                  j ≤ harperBlockCount (harperDt D₀ h) x - d →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset (harperDt D₀ h) x) m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
                      (Y ((p : Nat.Primes) : ℕ) ω)) j ω
                    ∈ Set.Icc (-(a + ((harperDt D₀ h - D₀ : ℕ) : ℝ)) - B * (j : ℝ))
                      (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ) + (j : ℝ)
                        + 2 * Real.log j)}) ω ∂ν)
              ≤ C * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - (⌈a / 4⌉₊ : ℝ)))
                := by
  obtain ⟨D₁, n₀, x₀, a₀, A, B, Tsh, hD₁, hA, hB, hTsh, H⟩ :=
    exists_setIntegral_restricted_normSq_le_rademacher_of_offset_of_drop
  obtain ⟨CM, hCM, hMert⟩ := exists_const_inv_log_mul_integral_normSq_shift_le_rademacher
  obtain ⟨D₀, hD₀ge, hTexp⟩ := exists_le_two_mul_exp_sub_one Tsh (max D₁ 4)
  have hD₁D₀ : D₁ ≤ D₀ := le_trans (le_max_left _ _) hD₀ge
  have h4D₀ : 4 ≤ D₀ := le_trans (le_max_right _ _) hD₀ge
  have hAs : (0 : ℝ) < 3 * (A * Real.sqrt 2) + 1 := by
    have h1 : (0 : ℝ) ≤ A * Real.sqrt 2 := mul_nonneg hA.le (Real.sqrt_nonneg 2)
    linarith
  refine ⟨D₀, n₀, a₀, (3 * (A * Real.sqrt 2) + 1) * CM, B, h4D₀, mul_pos hAs hCM,
    hB, ?_⟩
  intro E₀ d _hE₀ _hE₁
  obtain ⟨x₂, hx₂⟩ :=
    exists_harperThreshold_of_blockCount D₀ (24 * (D₀ + n₀ + 2 * d + 6))
  refine ⟨max (max x₀ (Real.exp 3)) x₂, ?_⟩
  intro Ω' _ Y ν hY x σ η a hx hσ0 hη0 hηE hσx ha ha1 hR
  -- the `a`-free part of the threshold is a condition on `x` alone, so it lives in `x₀`
  obtain ⟨-, hD₀L, hcount24⟩ := hx₂ x (le_trans (le_max_right _ _) hx)
  have hL0a : (0 : ℝ) ≤ Real.log (Real.log x) :=
    le_trans (Nat.cast_nonneg _) hD₀L
  have hcountfl : harperBlockCount D₀ x ≤ ⌊Real.log (Real.log x)⌋₊ := by
    simp only [harperBlockCount]
    exact Nat.sub_le _ _
  have hcountL : ((harperBlockCount D₀ x : ℕ) : ℝ) ≤ Real.log (Real.log x) := by
    have h1 : ((harperBlockCount D₀ x : ℕ) : ℝ)
        ≤ ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcountfl
    linarith [Nat.floor_le hL0a]
  have hΛ24 : 24 * ((D₀ : ℝ) + (n₀ : ℝ) + 2 * (d : ℝ) + 6)
      ≤ Real.log (Real.log x) := by
    have h1 : ((24 * (D₀ + n₀ + 2 * d + 6) : ℕ) : ℝ)
        ≤ ((harperBlockCount D₀ x : ℕ) : ℝ) := by exact_mod_cast hcount24
    push_cast at h1
    linarith
  set r : ℕ := ⌈a / 4⌉₊ with hrdef
  have hr1 : 1 ≤ r := Nat.ceil_pos.2 (by linarith)
  have hΛ : 4 * ((r : ℝ) + (D₀ : ℝ) + (n₀ : ℝ) + 2 * (d : ℝ) + 4)
      ≤ Real.log (Real.log x) := by
    have h1 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    linarith
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hxm : max x₀ (Real.exp 3) ≤ x := le_trans (le_max_left _ _) hx
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hxm
  have hxe3 : Real.exp 3 ≤ x := le_trans (le_max_right _ _) hxm
  have hx2 : (2 : ℝ) ≤ x := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hlogx0 : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hηd : 10 * η ≤ Real.exp d := by linarith
  have hσre : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hr0 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hD₀0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hn₀0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  obtain ⟨hM1, hML, -, -⟩ :=
    harperBlockCount_harperDt_bounds_of_drop (h := 1) (n₀ := n₀) (d := d) hr1 hΛ
    one_pos le_rfl (by rw [abs_one, div_one, Real.log_one]; linarith)
  have hMpos : (0 : ℝ) < (harperBlockCount D₀ x : ℝ) - r := by linarith
  have hmin0 : (0 : ℝ) ≤ min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r)) :=
    le_min zero_le_one (div_nonneg ha0 (Real.sqrt_nonneg _))
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) :=
    fun p => hY.measurable _ (p : Nat.Primes).2
  have hΛ' : 2 * ((D₀ : ℝ) + ((max (2 * (r + d)) (n₀ + (r + d)) : ℕ) : ℝ) + 2)
      ≤ Real.log (Real.log x) := by
    have hmax : ((max (2 * (r + d)) (n₀ + (r + d)) : ℕ) : ℝ)
        ≤ 2 * (r : ℝ) + 2 * (d : ℝ) + (n₀ : ℝ) := by
      have h1 : (max (2 * (r + d)) (n₀ + (r + d)) : ℕ) ≤ 2 * r + 2 * d + n₀ := by omega
      exact_mod_cast h1
    linarith
  set G : ℝ → Set Ω' := fun h => {ω | ∀ j,
    ⌈(a + ((harperDt D₀ h - D₀ : ℕ) : ℝ)) / 4⌉₊ ≤ j →
    j ≤ harperBlockCount (harperDt D₀ h) x - d →
    walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset (harperDt D₀ h) x) m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
      ∈ Set.Icc (-(a + ((harperDt D₀ h - D₀ : ℕ) : ℝ)) - B * (j : ℝ))
        (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ) + (j : ℝ) + 2 * Real.log j)} with hGdef
  have hGmeas : ∀ h, MeasurableSet (G h) := by
    intro h
    simp only [hGdef]
    exact measurableSet_freeStartBarrier (fun m => Finset.measurable_sum _ fun p _ =>
      (measurable_localLogAdd _).comp (hYm p)) _ _ _ _
  have hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ G q.2} := by
    simp only [hGdef]
    exact measurableSet_freeStartBarrierAdd_uncurry_harperDt_raise hYm σ x D₀ d
      (fun D => ⌈(a + ((D - D₀ : ℕ) : ℝ)) / 4⌉₊)
      (fun D j => -(a + ((D - D₀ : ℕ) : ℝ)) - B * (j : ℝ))
      (fun D j => a + ((D - D₀ : ℕ) : ℝ) + (j : ℝ) + 2 * Real.log j)
  rw [integral_restrictedChaosUnitShift_eq]
  set y : ℕ := ⌊x⌋₊ + 1 with hydef
  set g : ℝ → Ω' → ℝ := fun t ω =>
    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y (shiftLine σ t) ω‖ ^ 2
    with hgdef
  have hQ0 : (0 : ℝ) ≤ ∫ ω, g 0 ω ∂ν := by
    simp only [hgdef]
    exact integral_nonneg fun ω => by positivity
  have hInt : Integrable
      (Function.uncurry fun (ω : Ω') (t : ℝ) => Set.indicator (G t) (g t) ω)
      (ν.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    integrable_uncurry_indicator_normSq_rademacher hY y (σ := σ) hσre G hGmeas hSmeas
      (T := Set.Ioc (0 : ℝ) 1) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hIntOn : IntegrableOn (fun h => ∫ ω, Set.indicator (G h) (g h) ω ∂ν)
      (Set.Ioc (0 : ℝ) 1) := hInt.integral_prod_right
  rw [integral_integral_swap hInt]
  have hMert' : (Real.log x)⁻¹ * ∫ ω, g 0 ω ∂ν ≤ CM := hMert Ω' Y ν hY x σ hx2 hσ0
  have hjoin : (∫ h in Set.Ioc (0 : ℝ) 1, ∫ ω, Set.indicator (G h) (g h) ω ∂ν)
      ≤ (3 * (A * Real.sqrt 2) + 1)
        * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r)) * ∫ ω, g 0 ω ∂ν := by
    set δ : ℝ := Real.exp (-(Real.log (Real.log x) / 3)) with hδdef
    have hδ0 : (0 : ℝ) < δ := Real.exp_pos _
    have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hsub1 : Set.Ioc (0 : ℝ) δ ⊆ Set.Ioc (0 : ℝ) 1 := Set.Ioc_subset_Ioc_right hδ1
    have hsub2 : Set.Ioc δ 1 ⊆ Set.Ioc (0 : ℝ) 1 := Set.Ioc_subset_Ioc_left hδ0.le
    have hbelow : (∫ h in Set.Ioc (0 : ℝ) δ, ∫ ω, Set.indicator (G h) (g h) ω ∂ν)
        ≤ min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r)) * ∫ ω, g 0 ω ∂ν := by
      have hper : ∀ h ∈ Set.Ioc (0 : ℝ) δ,
          (∫ ω, Set.indicator (G h) (g h) ω ∂ν) ≤ ∫ ω, g 0 ω ∂ν := by
        intro h _
        have hsre : (0 : ℝ) < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
        haveI := isProbabilityMeasure_tiltedMeasure_rademacher hY y hsre
        have heq := hf'.setIntegral_normSq_eq y hsre (hGmeas h)
        have hle1 : (tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω) y
            (shiftLine σ h) ν (G h)).toReal ≤ 1 := measureReal_le_one
        have hgh0 : (0 : ℝ) ≤ ∫ ω, g h ω ∂ν := by
          simp only [hgdef]
          exact integral_nonneg fun ω => by positivity
        have hheight : (∫ ω, g h ω ∂ν) = ∫ ω, g 0 ω ∂ν := by
          simp only [hgdef]
          exact hf'.integral_normSq_shiftLine_eq y (σ := σ) h 0
        rw [integral_indicator (hGmeas h)]
        calc (∫ ω in G h, g h ω ∂ν)
            = (tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ h) ν (G h)).toReal * ∫ ω, g h ω ∂ν := heq
          _ ≤ 1 * ∫ ω, g h ω ∂ν := mul_le_mul_of_nonneg_right hle1 hgh0
          _ = ∫ ω, g 0 ω ∂ν := by rw [one_mul, hheight]
      have hconst : IntegrableOn (fun _ : ℝ => ∫ ω, g 0 ω ∂ν) (Set.Ioc (0 : ℝ) δ) :=
        integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      have hmono := setIntegral_mono_on (hIntOn.mono_set hsub1) hconst measurableSet_Ioc hper
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hδ0.le, sub_zero] at hmono
      have hδmin : δ ≤ min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r)) := by
        rw [hδdef]
        exact exp_neg_third_le_min_one_div_sqrt hL0 hM1 hML ha1
      exact le_trans hmono (mul_le_mul_of_nonneg_right hδmin hQ0)
    have habove : (∫ h in Set.Ioc δ 1, ∫ ω, Set.indicator (G h) (g h) ω ∂ν)
        ≤ 3 * (A * Real.sqrt 2 * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r))
          * ∫ ω, g 0 ω ∂ν) := by
      have hc0 : (0 : ℝ) ≤ A * Real.sqrt 2 * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r))
          * ∫ ω, g 0 ω ∂ν :=
        mul_nonneg (mul_nonneg (mul_nonneg hA.le (Real.sqrt_nonneg 2)) hmin0) hQ0
      have hper : ∀ h ∈ Set.Ioc δ 1, (∫ ω, Set.indicator (G h) (g h) ω ∂ν)
          ≤ (Real.log (1 / h) + 2)
            * (A * Real.sqrt 2 * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r))
              * ∫ ω, g 0 ω ∂ν) := by
        intro h hh
        obtain ⟨hhδ, hh1⟩ := hh
        have hh0 : (0 : ℝ) < h := lt_trans hδ0 hhδ
        have habs : |h| = h := abs_of_pos hh0
        have him : (shiftLine σ h).im = h := by simp [shiftLine]
        have hcut : Real.log (1 / |h|) ≤ Real.log (Real.log x) / 3 := by
          have h1 : Real.log δ ≤ Real.log h := Real.log_le_log hδ0 hhδ.le
          rw [hδdef, Real.log_exp] at h1
          rw [habs, one_div, Real.log_inv]
          linarith
        obtain ⟨hD₀le, hDlog, -, -⟩ :=
          harper_block_count_of_height (D₀ := D₀) (d := r + d) (n₀ := n₀)
            (by rw [habs]; exact hh0) (by rw [habs]; exact hh1) hcut hΛ'
        set k : ℕ := harperDt D₀ h - D₀ with hkdef
        have hDk : harperDt D₀ h = D₀ + k := by
          have := le_harperDt D₀ h
          omega
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
        have hkR : (k : ℝ) ≤ Real.log (Real.log x) / 3 + 1 :=
          harperDt_sub_le_of_cut (D₀ := D₀) hh0 hh1 hcut
        have hak : (0 : ℝ) < (a + (k : ℝ)) / 4 := by linarith
        have hra1 : 1 ≤ ⌈(a + (k : ℝ)) / 4⌉₊ := Nat.ceil_pos.2 hak
        have hraub : ((⌈(a + (k : ℝ)) / 4⌉₊ : ℕ) : ℝ) ≤ (a + (k : ℝ)) / 4 + 1 :=
          (Nat.ceil_lt_add_one hak.le).le
        obtain ⟨hfit, -⟩ := harperBlockCount_raise_halving_of_drop_of_level (D₀ := D₀)
          (n₀ := n₀) (k := k) (d := d) (a := a) (x := x) ha1 hR hΛ24 hkR
        have hshift := min_one_div_sqrt_harperBlockCount_raise_le_of_drop_of_level
          (D₀ := D₀) (n₀ := n₀) (k := k) (d := d) (a := a) (x := x) ha1 hR hΛ24 hkR
        rw [← hDk] at hfit hshift
        have hrn : ⌈(a + (k : ℝ)) / 4⌉₊ ≤ harperBlockCount (harperDt D₀ h) x - d := by omega
        have hn₀le' : n₀ ≤ harperBlockCount (harperDt D₀ h) x - d - ⌈(a + (k : ℝ)) / 4⌉₊ := by
          omega
        have hoff : (4 : ℝ) ≤ Real.exp (harperOffset (harperDt D₀ h) x) := by
          have h1 : (4 : ℝ) ≤ ((harperDt D₀ h : ℕ) : ℝ) := by
            have h2 : (4 : ℕ) ≤ harperDt D₀ h := le_trans h4D₀ (le_harperDt D₀ h)
            exact_mod_cast h2
          have h3 : (3 : ℝ) ≤ harperOffset (harperDt D₀ h) x := by
            linarith [sub_one_le_harperOffset (harperDt D₀ h) x]
          calc (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
            _ ≤ _ := Real.exp_le_exp.2 h3
        have hτsq : (2 * (shiftLine σ h).im) ^ 2
            ≤ Real.exp (harperOffset (harperDt D₀ h) x) := by
          have hh2 : h ^ 2 ≤ 1 := by
            have h1 : h * h ≤ 1 * 1 := mul_le_mul hh1 hh1 hh0.le zero_le_one
            rw [pow_two]
            linarith
          rw [him]
          calc (2 * h) ^ 2 = 4 * h ^ 2 := by ring
            _ ≤ 4 * 1 := by linarith
            _ ≤ _ := by linarith
        have hTsh' : Tsh ≤ 2 * (shiftLine σ h).im
            * Real.exp (harperOffset (harperDt D₀ h) x) := by
          have h1 := two_mul_exp_le_mul_exp_harperOffset_harperDt (D₀ := D₀) (t := h)
            (by rw [habs]; exact hh0) x
          rw [habs] at h1
          rw [him]
          linarith
        have hchain := H Ω' Y ν hY x σ (a + (k : ℝ)) η (harperDt D₀ h)
          ⌈(a + (k : ℝ)) / 4⌉₊ d (shiftLine σ h) (fun j => 2 * Real.log j) hxx₀
          (le_trans hD₁D₀ hD₀le) hDlog (re_shiftLine σ h)
          (by rw [re_shiftLine]; linarith) hσx hηd (by rw [him]; linarith) hτsq
          hTsh' (by linarith) (by linarith) hra1 hrn hraub hn₀le'
          (fun j hj _ => by
            have h0 : (0 : ℝ) ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj)
            rw [abs_of_nonneg (by linarith)]
            linarith)
        have hheight : (∫ ω, ‖randomEulerProduct
            (fun ω => squarefreeExtension fun p => Y p ω) y (shiftLine σ h) ω‖ ^ 2 ∂ν)
            = ∫ ω, g 0 ω ∂ν := by
          simp only [hgdef]
          exact hf'.integral_normSq_shiftLine_eq y (σ := σ) h 0
        have hband : ((k : ℝ) + 1) ≤ Real.log (1 / h) + 2 := by
          rw [hkdef]
          exact harperDt_sub_add_one_le hh0 hh1
        rw [integral_indicator (hGmeas h)]
        calc (∫ ω in G h, g h ω ∂ν)
            ≤ A * min 1 ((a + (k : ℝ)) / Real.sqrt
                (((harperBlockCount (harperDt D₀ h) x - d : ℕ) : ℝ)
                  - (⌈(a + (k : ℝ)) / 4⌉₊ : ℝ)))
                * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                    (shiftLine σ h) ω‖ ^ 2 ∂ν := hchain
          _ = A * min 1 ((a + (k : ℝ)) / Real.sqrt
                (((harperBlockCount (harperDt D₀ h) x - d : ℕ) : ℝ)
                  - (⌈(a + (k : ℝ)) / 4⌉₊ : ℝ)))
                * ∫ ω, g 0 ω ∂ν := by rw [hheight]
          _ ≤ A * (((k : ℝ) + 1) * (Real.sqrt 2
                * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r))))
                * ∫ ω, g 0 ω ∂ν :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hshift hA.le) hQ0
          _ = ((k : ℝ) + 1) * (A * Real.sqrt 2
                * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r))
                * ∫ ω, g 0 ω ∂ν) := by ring
          _ ≤ (Real.log (1 / h) + 2)
                * (A * Real.sqrt 2 * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r))
                    * ∫ ω, g 0 ω ∂ν) :=
              mul_le_mul_of_nonneg_right hband hc0
      have hmaj : IntegrableOn (fun h : ℝ => (Real.log (1 / h) + 2)
          * (A * Real.sqrt 2 * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r))
            * ∫ ω, g 0 ω ∂ν)) (Set.Ioc δ 1) :=
        (integrableOn_log_one_div_add_two.mono_set hsub2).mul_const _
      have hle3 : (∫ h in Set.Ioc δ 1, (Real.log (1 / h) + 2)) ≤ 3 := by
        rw [← setIntegral_log_one_div_add_two]
        refine setIntegral_mono_set integrableOn_log_one_div_add_two ?_
          (Filter.Eventually.of_forall fun _ hx => hsub2 hx)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
        have hlog : (0 : ℝ) ≤ Real.log (1 / h) + 2 := by
          have h1 := Real.log_nonpos hh.1.le hh.2
          rw [one_div, Real.log_inv]
          linarith
        exact hlog
      have hmono := setIntegral_mono_on (hIntOn.mono_set hsub2) hmaj measurableSet_Ioc hper
      refine le_trans hmono ?_
      rw [MeasureTheory.integral_mul_const]
      exact mul_le_mul_of_nonneg_right hle3 hc0
    rw [← Set.Ioc_union_Ioc_eq_Ioc hδ0.le hδ1,
      setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hIntOn.mono_set hsub1) (hIntOn.mono_set hsub2)]
    linarith
  exact mul_le_mul_of_join_of_norm (inv_nonneg.2 hlogx0.le) hAs hmin0 hjoin hMert'

end RMF
