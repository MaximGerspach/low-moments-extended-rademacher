/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.RademacherPaleyZygmund
import RMF.Reduction.HarperMoment
import RMF.Reduction.WindowBridge

/-!
# The shape, through the reduction, for the Rademacher function

The twin of `RMF/Reduction/HarperMoment.lean`'s first two steps.
`RMF.exists_le_integral_rpow_harper_shape_rademacher` bounds

`∫_Ω (∫_T 1_barrier ‖F(½+σ+it)‖² dt)^q dν`

from below, and the reduction wants a lower bound on
`∫_Ω chaosShift (squarefreeExtension f) x σ ω ^ q dν`.

Three differences, and only the third costs anything:

1. **The cutoff is the same.**  `RMF.blockCutoff_harperN` is law-free, so
   `blockCutoff (harperTheta B x) (harperN B x) = ⌊x⌋₊ + 1` here too.
2. **The barrier only shrinks the integral.**  `1_barrier ≤ 1`.
3. **The window is `(1/3, 1/2]`, not `(-1/2, 1/2]`.**  Harper's height restriction is carried all
   the way to here: the shape's `T` must lie in `[1/3,1/2]`, so `|T| = 1/6` where the Steinhaus
   window has `|T| = 1`.  That is *not* free, but it costs only a constant: the restricted
   integral is compared with the full one by `setIntegral_mono_set`, the integrand being a
   norm squared, and `1/6` is absorbed into the theorem's `α`.

The remaining factor `(\log x)^{-1}` in `RMF.chaosShift`'s definition cancels the shape's
`(\log x)^q` exactly, as on the Steinhaus side.

## The last step

`RMF.exists_le_integral_rpow_normalisedSum_rademacher`, at the end of this file, composes
`RMF.exists_le_integral_rpow_chaosShift_rademacher` with
`RMF.reduction_lower_chaosShift_rademacher_absorbed`.
-/

open MeasureTheory

namespace RMF

/-! ### Dropping the barrier, and widening the window -/

/-- **The barrier-restricted Harper window is at most the full Euler window.**  The twin of
`RMF.setIntegral_indicator_le_window`, with the extra step that Harper's height range forces:
the restricted integral runs over `(1/3, 1/2]` and the majorant over `(-1/2, 1/2]`.
The integrability of the restricted integrand is not needed: if it fails, Bochner's integral is
`0`, and the majorant is nonnegative, so the inequality holds anyway.  That case split is what
lets this lemma avoid the joint measurability of the barrier event in `(ω,t)`. -/
lemma setIntegral_indicator_le_window_rademacher {Ω' : Type*}
    {Y : ℕ → Ω' → ℂ} {N : ℕ} {σ : ℝ} {ω : Ω'} (hσ : 0 ≤ σ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖Y p ω‖ ≤ 1) (S : ℝ → Set Ω') :
    ∫ t in Set.Ioc (1 / 3 : ℝ) (1 / 2 : ℝ), Set.indicator (S t)
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) N
          (shiftLine σ t) ω‖ ^ 2) ω
      ≤ ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ),
          lineSqOf (1 / 2 + σ) (fun ω => squarefreeExtension fun p => Y p ω) N ω t := by
  have hre : (1 : ℝ) / 2 ≤ 1 / 2 + σ := by linarith
  have hbd : ∀ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) N
      (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ eulerBound N := fun t =>
    norm_randomEulerProduct_sqfree_le hω (by simpa using hre)
  have hwin : IntegrableOn (fun t : ℝ =>
      lineSqOf (1 / 2 + σ) (fun ω => squarefreeExtension fun p => Y p ω) N ω t)
      (Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ)) :=
    integrableOn_windowOf (1 / 2 + σ)
      (measurable_randomEulerProduct_sqfree_line (1 / 2 + σ)) hbd _ _
  have hwin' : IntegrableOn (fun t : ℝ =>
      lineSqOf (1 / 2 + σ) (fun ω => squarefreeExtension fun p => Y p ω) N ω t)
      (Set.Ioc (1 / 3 : ℝ) (1 / 2 : ℝ)) :=
    integrableOn_windowOf (1 / 2 + σ)
      (measurable_randomEulerProduct_sqfree_line (1 / 2 + σ)) hbd _ _
  -- Harper's window sits inside the Euler one, and the integrand is a norm squared
  have hwide : (∫ t in Set.Ioc (1 / 3 : ℝ) (1 / 2 : ℝ),
        lineSqOf (1 / 2 + σ) (fun ω => squarefreeExtension fun p => Y p ω) N ω t)
      ≤ ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ),
          lineSqOf (1 / 2 + σ) (fun ω => squarefreeExtension fun p => Y p ω) N ω t := by
    refine setIntegral_mono_set hwin
      (Filter.Eventually.of_forall fun t => by simp only [lineSqOf]; positivity) ?_
    refine Filter.Eventually.of_forall fun t ht => ?_
    exact ⟨by linarith [ht.1], ht.2⟩
  refine le_trans ?_ hwide
  by_cases hint : IntegrableOn (fun t : ℝ => Set.indicator (S t)
      (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) N
        (shiftLine σ t) ω‖ ^ 2) ω) (Set.Ioc (1 / 3 : ℝ) (1 / 2 : ℝ))
  · refine setIntegral_mono_on hint hwin' measurableSet_Ioc fun t _ => ?_
    exact Set.indicator_le_self' (fun _ _ => pow_nonneg (norm_nonneg _) 2) ω
  · rw [integral_undef hint]
    refine setIntegral_nonneg measurableSet_Ioc fun t _ => ?_
    simp only [lineSqOf]
    positivity

/-! ### The shape, with `(\log x)^q` cancelled -/

set_option maxHeartbeats 1000000 in
-- the goal carries the two integrals literally, so every `rw` and `linarith` below works
-- against terms the size of the statement; the Steinhaus twin raises the limit for the same reason
/-- **The lower bound on the chaos moment as the reduction wants it, for the Rademacher
function**; the twin of `RMF.exists_le_integral_rpow_chaosShift`, with the same bound
`\gg V^{-q}\,W^{-q}` and the implied factor depending on `κ`, `B` and the space `Ω'`.  Two constants
differ and nothing else does: `e^{B+73}` for `e^{B+69}`, and the count threshold
`6B + 3\log V + 49` for `+40`.  Harper's height range survives as the factor `|T| = 1/6`, absorbed
into `α`. -/
theorem exists_le_integral_rpow_chaosShift_rademacher :
    ∃ (a₀ α : ℝ), 0 < α ∧ 1 ≤ a₀ ∧
      ∀ κ : ℝ, a₀ ≤ κ * Real.log 2 → ∃ B₀ : ℕ,
      ∀ B : ℕ, B₀ ≤ B →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'], ∃ E : ℝ, 0 < E ∧
        ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ x₀ : ℝ,
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (σ q x : ℝ),
          x₀ ≤ x → 1 < x → 3 ≤ x → Λ₀ ≤ Real.log (Real.log x) →
          (B : ℝ) + 2 ≤ Real.log (Real.log x) →
          6 * (B : ℝ) + 3 * Real.log V + 49 ≤ Real.log (Real.log x) →
          4 * V * (4 * Real.exp (2 * (B : ℝ) + 6) + 7) ≤ Real.log x →
          0 < σ → σ ≤ 1 / 2 → σ * Real.log x = 4 * V →
          0 < q → q < 1 → 1 ≤ q * Real.sqrt (Real.log (Real.log x)) →
            min α (α ^ (2 : ℝ)) * min 1 (1 / ((6 + 2 / Real.log 2) * E))
                * Real.exp (-(2 * (1 + κ * Real.log 2)))
                * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
                * (Real.exp ((B : ℝ) + 73) ^ (-(2 : ℝ)) * V ^ (-q))
              ≤ ∫ ω, chaosShift (fun ω => squarefreeExtension fun p => Y p ω) x σ ω ^ q
                  ∂ν := by
  obtain ⟨a₀, α, Bs, hα, ha₀, hBs, hshape⟩ :=
    exists_le_integral_rpow_harper_shape_rademacher
  refine ⟨a₀, 1 / 6 * α, by positivity, ha₀, ?_⟩
  intro κ hκa
  obtain ⟨B₀, hshape⟩ := hshape κ hκa
  refine ⟨B₀, ?_⟩
  intro B hB Ω' _
  obtain ⟨E, hE, hshape⟩ := hshape B hB Ω'
  refine ⟨E, hE, ?_⟩
  intro V hV
  obtain ⟨Λ₀, x₀, hshape⟩ := hshape V hV
  refine ⟨Λ₀, x₀, ?_⟩
  intro Y ν hY σ q x hx hx1 hx3 hΛ₀ hxΛ hΛcnt hfarwin hσ0 hσhalf hσeq hq0 hq1 hqΛ
  haveI := hY.isProbabilityMeasure
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogq : (0 : ℝ) < Real.log x ^ q := Real.rpow_pos_of_pos hlogx q
  -- Harper's window is a sixth of `chaosShift`'s own
  have hTvol : (volume (Set.Ioc (1 / 3 : ℝ) (1 / 2 : ℝ))).toReal = 1 / 6 := by
    rw [Real.volume_Ioc]
    norm_num
  have hTsub : Set.Ioc (1 / 3 : ℝ) (1 / 2 : ℝ) ⊆ Set.Icc (1 / 3 : ℝ) (1 / 2) := fun t ht =>
    ⟨ht.1.le, ht.2⟩
  have hmain := hshape Y ν hY σ q x (Set.Ioc (1 / 3 : ℝ) (1 / 2 : ℝ)) hx hx1 hx3 hΛ₀
    hxΛ hΛcnt hfarwin hσ0 hσhalf hσeq measurableSet_Ioc hTsub
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by rw [hTvol]; norm_num)
    hq0 hq1 hqΛ
  rw [hTvol] at hmain
  -- the cutoff is `⌊x⌋₊ + 1`, so the inner integral is the Euler-shift window
  have hcut : blockCutoff (harperTheta B x) (harperN B x) = ⌊x⌋₊ + 1 :=
    blockCutoff_harperN hx1 hxΛ
  rw [hcut] at hmain
  -- pass to the majorant, `ω` by `ω`
  set S : ℝ → Set Ω' := fun t => barrierEvent
      (fun mm ω => ∑ p ∈ primeBlockSub (harperTheta B x) mm,
        localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω))
      (harperBarrierTop B (Real.exp 3 * V) x)
      (fun j => -harperLevel a₀ ((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ) q - Bs * j)
      (fun j => harperLevel a₀ ((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ) q + j
        + harperHf j) with hSdef
  set F : Ω' → ℝ := fun ω => (∫ t in Set.Ioc (1 / 3 : ℝ) (1 / 2 : ℝ),
      Set.indicator (S t)
      (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
        (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω) ^ q with hFdef
  set G : Ω' → ℝ := fun ω => Real.log x ^ q
      * chaosShift (fun ω => squarefreeExtension fun p => Y p ω) x σ ω ^ q with hGdef
  have hGint : Integrable G ν := by
    rw [hGdef]
    exact (integrable_chaosShift_rpow_sqfree hY (by positivity) hσ0.le hq0.le).const_mul _
  have hae := ae_forall_norm_le_one hY norm_le_one_rademacherLaw (⌊x⌋₊ + 1)
  have hFG : F ≤ᵐ[ν] G := by
    filter_upwards [hae] with ω hω
    have hstep : (∫ t in Set.Ioc (1 / 3 : ℝ) (1 / 2 : ℝ), Set.indicator (S t)
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
          (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω)
        ≤ Real.log x
            * chaosShift (fun ω => squarefreeExtension fun p => Y p ω) x σ ω := by
      rw [chaosShift_eqOf, ← mul_assoc, mul_inv_cancel₀ hlogx.ne', one_mul]
      exact setIntegral_indicator_le_window_rademacher hσ0.le hω _
    have hnn : (0 : ℝ) ≤ ∫ t in Set.Ioc (1 / 3 : ℝ) (1 / 2 : ℝ), Set.indicator (S t)
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
          (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω :=
      setIntegral_nonneg measurableSet_Ioc fun t _ =>
        Set.indicator_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2) ω
    have := Real.rpow_le_rpow hnn hstep hq0.le
    rwa [Real.mul_rpow hlogx.le (chaosShift_nonnegOf (by positivity) ω)] at this
  have hFnn : 0 ≤ᵐ[ν] F := by
    filter_upwards with ω
    simp only [hFdef]
    exact Real.rpow_nonneg (setIntegral_nonneg measurableSet_Ioc fun t _ =>
      Set.indicator_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2) ω) q
  have hmono : ∫ ω, F ω ∂ν ≤ ∫ ω, G ω ∂ν := integral_mono_of_nonneg hFnn hGint hFG
  rw [hGdef, integral_const_mul] at hmono
  -- and cancel the `(\log x)^q` the reduction supplies
  refine le_of_mul_le_mul_left ?_ hlogq
  calc Real.log x ^ q * (min (1 / 6 * α) ((1 / 6 * α) ^ (2 : ℝ))
          * min 1 (1 / ((6 + 2 / Real.log 2) * E))
          * Real.exp (-(2 * (1 + κ * Real.log 2)))
          * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
          * (Real.exp ((B : ℝ) + 73) ^ (-(2 : ℝ)) * V ^ (-q)))
      = min (1 / 6 * α) ((1 / 6 * α) ^ (2 : ℝ))
          * min 1 (1 / ((6 + 2 / Real.log 2) * E))
          * Real.exp (-(2 * (1 + κ * Real.log 2)))
          * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
          * (Real.exp ((B : ℝ) + 73) ^ (-(2 : ℝ)) * Real.log x ^ q * V ^ (-q)) := by ring
    _ ≤ ∫ ω, F ω ∂ν := hmain
    _ ≤ Real.log x ^ q
          * ∫ ω, chaosShift (fun ω => squarefreeExtension fun p => Y p ω) x σ ω ^ q ∂ν :=
        hmono

/-! ### Harper's lower bound, composed

`RMF.reduction_lower_chaosShift_rademacher_absorbed` has the Steinhaus shape, with no tilt scale in
the statement and no cap on `V`, so `V` may be chosen after the reduction's constant.  The proof
below is `RMF.exists_le_integral_rpow_normalisedSum`'s with the two constants that moved. -/

/-- **Harper's lower bound for the Rademacher random multiplicative function**, on
`q ∈ [2/3, 1)`, with the constant a formula in the walls.  The twin of
`RMF.exists_walls_le_integral_rpow_normalisedSum`, and like it a corollary of
`RMF.le_integral_rpow_normalisedSum_of_shape`: the choice of `V` and the exponent bookkeeping are
law-agnostic, so only the two constants that moved appear here — `e^{B₀+73}` for `e^{B₀+69}`
inside `A₀`, and the count threshold `6B₀ + 3\log V + 49` for `+40`. -/
theorem exists_walls_le_integral_rpow_normalisedSum_rademacher (Ω : Type*)
    [MeasurableSpace Ω] :
    ∃ A₀ cr C₀ V₀ : ℝ, 0 < A₀ ∧ 0 < cr ∧ 0 ≤ C₀ ∧ ∃ x₀ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
        ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q < 1 →
          harperMomentConst A₀ cr C₀ V₀
              * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
            ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨cr, C₀, V₀, hcr, hC₀, hV₀, HR⟩ :=
    reduction_lower_chaosShift_rademacher_absorbed (Ω := Ω)
  obtain ⟨a₀, α, hα, ha₀, HL⟩ := exists_le_integral_rpow_chaosShift_rademacher
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the slack, and the block parameter
  obtain ⟨B₀, HL⟩ := HL (a₀ / Real.log 2) (by rw [div_mul_cancel₀ _ hlog2.ne'])
  obtain ⟨E, hE, HL⟩ := HL B₀ le_rfl Ω
  set κ : ℝ := a₀ / Real.log 2 with hκdef
  -- the absolute factor the shape carries, with `W^{-q}` and `V^{-q}` split off
  set A₀ : ℝ := min α (α ^ (2 : ℝ)) * min 1 (1 / ((6 + 2 / Real.log 2) * E))
      * Real.exp (-(2 * (1 + κ * Real.log 2))) * Real.exp ((B₀ : ℝ) + 73) ^ (-(2 : ℝ))
    with hA₀def
  have hA₀ : (0 : ℝ) < A₀ := by
    rw [hA₀def]
    have h1 : (0 : ℝ) < min α (α ^ (2 : ℝ)) := lt_min hα (Real.rpow_pos_of_pos hα _)
    have h2 : (0 : ℝ) < min 1 (1 / ((6 + 2 / Real.log 2) * E)) := by
      refine lt_min one_pos ?_
      have : (0 : ℝ) < (6 + 2 / Real.log 2) * E := by positivity
      positivity
    positivity
  refine ⟨A₀, cr, C₀, V₀, hA₀, hcr, hC₀.le, ?_⟩
  refine le_integral_rpow_normalisedSum_of_shape (Ω := Ω) (fun f μ => IsRademacherRMF f μ)
    (A₀ := A₀) (cr := cr) (C₀ := C₀) (V₀ := V₀) (ct := 49) (B₀ := B₀) hA₀ hcr hC₀.le ?_ ?_
  · -- the chaos shape, at the tilt the core picks
    intro V hV1
    obtain ⟨Λ₀, x₁, HL⟩ := HL V hV1
    refine ⟨Λ₀, x₁, ?_⟩
    intro f μ hf x q hxx₁ hx1 hx3 hΛ₀ hBΛ hΛcnt hfarwin h8V hq0 hq1 hqΛ
    replace hf : IsRademacherRMF f μ := hf
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hV0 : (0 : ℝ) < V := by linarith
    obtain ⟨Y, hY, rfl⟩ := hf.exists_primeValues
    have h := HL Y μ hY (4 * V / Real.log x) q x hxx₁ hx1 hx3 hΛ₀ hBΛ hΛcnt hfarwin
      (by positivity) (by rw [div_le_iff₀ hlogx]; linarith)
      (div_mul_cancel₀ _ hlogx.ne') hq0 hq1 hqΛ
    refine le_trans (le_of_eq ?_) h
    rw [hA₀def]
    ring
  · -- the reduction, at the same tilt
    intro V hVV₀
    obtain ⟨x₂, HR⟩ := HR V hVV₀
    refine ⟨x₂, ?_⟩
    intro f μ hf x q hxx₂ hq23 hq1
    replace hf : IsRademacherRMF f μ := hf
    obtain ⟨Y, hY, rfl⟩ := hf.exists_primeValues
    exact HR Y μ hY x q hxx₂ hq23 hq1

/-- **Harper's lower bound for the Rademacher random multiplicative function**, on
`q ∈ [2/3, 1)`.

`\displaystyle \int \|S_x\|^{2q} \ \ge\ c\,\big(1+(1-q)\sqrt{\log\log x}\big)^{-q}`

with `c` and `x₀` independent of `f`, `μ`, `x` and `q`; the space `Ω` is fixed first, and the form
with `c` independent of `Ω` too is Harper's theorem in `RMF/HarperRademacher.lean`.  The twin of
`RMF.exists_le_integral_rpow_normalisedSum`;
`RMF.exists_walls_le_integral_rpow_normalisedSum_rademacher` is the same bound with the constant
left as a formula. -/
theorem exists_le_integral_rpow_normalisedSum_rademacher (Ω : Type*)
    [MeasurableSpace Ω] :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
        ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q < 1 →
          c * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
            ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨A₀, cr, C₀, V₀, hA₀, hcr, _, x₀, H⟩ :=
    exists_walls_le_integral_rpow_normalisedSum_rademacher Ω
  exact ⟨harperMomentConst A₀ cr C₀ V₀, harperMomentConst_pos hA₀ hcr, x₀, H⟩

end RMF
