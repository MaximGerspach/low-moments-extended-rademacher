/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.MertensProduct
import RMF.Probability.RestrictedChaos
import RMF.Probability.RestrictedFirstMoment

/-!
# The restricted first moment of the chaos

Hamdan's Proposition 2.1 (Hamdan, *Partial sums of random multiplicative functions with
supercritical divisor twists*, arXiv:2604.05563): `E[Z²(A)] ≪ A/√t`, uniformly in large `t`.  This
is where the upper bound gains its `(log log x)^{-1/2}`: the trivial bound is `E[Z²] ≍ 1`, and the
barrier constraint costs the factor `A/√t`.

## The route: tilt first

Hamdan inserts his barrier estimate, Lemma 2.2, into a level-set representation of `Z²(A)`.  This
file does not.  The tilted measure is defined so that `P'(A) = (∫_A ‖F‖² dμ) / (∫ ‖F‖² dμ)`,
which rearranged (`RMF.IsSteinhausRMF.setIntegral_normSq_eq`) is the identity
`∫_A ‖F‖² = P'(A)·E‖F‖²`.  So the restricted second moment is `E‖F‖²` times the tilted probability
of the barrier event, and Harper's Proposition 5 bounds that probability directly.

## Where each factor comes from

* `RMF.exists_integral_restricted_normSq_le_of_le`: the upper half of Harper's Proposition 5,
  joined to the second moment and integrated over the heights, at a tilt scale `η ≤ E₀`.  This
  supplies `A·min{1,a/√n}`.
* `RMF.exists_const_inv_log_mul_integral_normSq_le`: Mertens' third theorem.  The `(log y)⁻¹` in
  `RMF.chaosUnit` is Hamdan's `e^{-t}`, and it cancels the growth of
  `E‖F_y(1/2)‖² = ∏_{p<y}(1-1/p)⁻¹ ≍ log y`.

The `min{1, a/√n}` is kept rather than weakened to `a/√n`: the `q`-th moment
(`Probability/ChaosMoment.lean`) uses the `1` branch where `(1-q)√t < 2` and the `a/√n` branch
elsewhere.

The file also defines the chaos at a shifted abscissa, on the unit window and on `[n, n+1]`, with
its integrability, its mean, and Hamdan's pointwise decomposition (2.18).
-/

open MeasureTheory

namespace RMF

/-- `shiftLine 0 h` is the point `1/2 + ih` of the critical line. -/
@[simp] lemma shiftLine_zero (h : ℝ) :
    shiftLine 0 h = ((1 / 2 : ℝ) : ℂ) + (h : ℂ) * Complex.I := by
  rw [shiftLine]
  norm_num

/-! ### The normalisation

`E‖F_y(1/2)‖²` is the Mertens product, which grows like `log y`; the `(log y)⁻¹` in front of `Z²`
is what makes the first moment `O(1)` rather than `O(log y)`. -/

/-- **Mertens' third theorem, in the form the normalisation needs.**  `(log x)⁻¹ E‖F_x(1/2)‖²` is
bounded by an absolute constant.

This is the factor that turns `A·min{1,a/√n}·E‖F‖²` into a bound on `E[Z²(A)]` itself. -/
lemma exists_const_inv_log_mul_integral_normSq_le :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
      IsSteinhausPrimeValues Y ν → ∀ x : ℝ, 2 ≤ x →
        (Real.log x)⁻¹ * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
            (⌊x⌋₊ + 1) (shiftLine 0 0) ω‖ ^ 2 ∂ν ≤ C := by
  obtain ⟨CM, hCM, hM⟩ := exists_abs_log_prod_primesBelow_sub_log_log_le
  refine ⟨Real.exp CM, Real.exp_pos _, ?_⟩
  intro Ω' _ Y ν hY x hx
  have hf' : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  have hsre : (0 : ℝ) < (shiftLine 0 0).re := by rw [re_shiftLine]; norm_num
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hN2' : (2 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN2
  have hNx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlogN : (0 : ℝ) < Real.log ((⌊x⌋₊ : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hlogx : Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log x := Real.log_le_log (by linarith) hNx
  have hlogx0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le hlogN hlogx
  -- the second moment is the Mertens product
  have hprod : (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
      (⌊x⌋₊ + 1) (shiftLine 0 0) ω‖ ^ 2 ∂ν)
      = ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 - ((p : ℝ))⁻¹)⁻¹ := by
    rw [hf'.integral_norm_randomEulerProduct_sq' (⌊x⌋₊ + 1) hsre]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [re_shiftLine, show (-2 : ℝ) * (1 / 2 + 0) = -1 by ring, Real.rpow_neg_one]
  have hppos : (0 : ℝ) < ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 - ((p : ℝ))⁻¹)⁻¹ := by
    refine Finset.prod_pos fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    exact inv_pos.2 (by linarith)
  -- Mertens bounds it by `e^{C} log ⌊x⌋₊`
  have hMx := abs_le.1 (hM ⌊x⌋₊ hN2)
  have hbound : (∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 - ((p : ℝ))⁻¹)⁻¹)
      ≤ Real.exp CM * Real.log ((⌊x⌋₊ : ℕ) : ℝ) := by
    have hle : Real.log (∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 - ((p : ℝ))⁻¹)⁻¹)
        ≤ CM + Real.log (Real.log ((⌊x⌋₊ : ℕ) : ℝ)) := by linarith [hMx.2]
    have h := Real.exp_le_exp.2 hle
    rwa [Real.exp_log hppos, Real.exp_add, Real.exp_log hlogN] at h
  rw [hprod, inv_mul_eq_div, div_le_iff₀ hlogx0]
  nlinarith [Real.exp_pos CM]

/-! ### The same, off the critical line

The lower reduction `RMF.reduction_lower_chaosShift` (the second bound of Harper's Proposition 3)
subtracts a chaos term at `σ = 2V/\log x`, so the upper bound is needed at that shift.  The shift
enters the second moment only through the Mertens product, where it can only help. -/

/-- **The Euler-product second moment is antitone in the shift.**

`∫‖F(1/2+σ)‖² = ∏_{p<N}(1 - p^{-1-2σ})^{-1}` exactly
(`RMF.IsSteinhausRMF.integral_norm_randomEulerProduct_sq'`), and each factor is increasing in
`p^{-1-2σ}`, which is decreasing in `σ`.  So moving off the critical line in the direction the
lower reduction moves costs nothing at all. -/
lemma integral_normSq_shiftLine_mono {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (N : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) N
        (shiftLine σ 0) ω‖ ^ 2 ∂ν)
      ≤ ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) N
        (shiftLine 0 0) ω‖ ^ 2 ∂ν := by
  have hf' : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  have hsre : (0 : ℝ) < (shiftLine σ 0).re := by rw [re_shiftLine]; linarith
  have hsre0 : (0 : ℝ) < (shiftLine 0 0).re := by rw [re_shiftLine]; norm_num
  rw [hf'.integral_norm_randomEulerProduct_sq' N hsre,
    hf'.integral_norm_randomEulerProduct_sq' N hsre0]
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
    rw [re_shiftLine]
    have hle : ((p : ℝ)) ^ (-2 * (1 / 2 + σ)) ≤ ((p : ℝ)) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have hinv : ((p : ℝ)) ^ (-1 : ℝ) = ((p : ℝ))⁻¹ := Real.rpow_neg_one _
    have hhalf : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hp0 (by norm_num)]; linarith
    have h0 : (0 : ℝ) < 1 - ((p : ℝ)) ^ (-2 * (1 / 2 + σ)) := by
      rw [hinv] at hle; linarith
    exact (inv_pos.2 h0).le
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
    rw [re_shiftLine, re_shiftLine]
    have hle : ((p : ℝ)) ^ (-2 * (1 / 2 + σ)) ≤ ((p : ℝ)) ^ (-2 * (1 / 2 + (0 : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have hv : ((p : ℝ)) ^ (-2 * (1 / 2 + (0 : ℝ))) = ((p : ℝ))⁻¹ := by
      rw [show (-2 : ℝ) * (1 / 2 + 0) = -1 by ring, Real.rpow_neg_one]
    have hhalf : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hp0 (by norm_num)]; linarith
    refine inv_anti₀ ?_ ?_
    · rw [hv]; linarith
    · linarith

/-- **The mean chaos off the critical line is bounded by an absolute constant.**
`(\log x)^{-1}E‖F_x(1/2+σ)‖² ≤ C` for `2 ≤ x` and `σ ≥ 0`: the `σ = 0` bound
(`RMF.exists_const_inv_log_mul_integral_normSq_le`) with `RMF.integral_normSq_shiftLine_mono` in
front of it.  The `q`-th moment at the shift, Hamdan's Proposition 1.2 there, needs the barrier
machinery at `σ` and is `RMF.exists_const_integral_chaosUnitShift_rpow_le`. -/
theorem exists_const_inv_log_mul_integral_normSq_shift_le :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
      IsSteinhausPrimeValues Y ν → ∀ x σ : ℝ, 2 ≤ x → 0 ≤ σ →
        (Real.log x)⁻¹ * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
            (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν ≤ C := by
  obtain ⟨C, hC, H⟩ := exists_const_inv_log_mul_integral_normSq_le
  refine ⟨C, hC, ?_⟩
  intro Ω' _ Y ν hY x σ hx hσ
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hlog : (0 : ℝ) ≤ (Real.log x)⁻¹ := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left (integral_normSq_shiftLine_mono hY _ hσ) hlog) ?_
  exact H Ω' Y ν hY x hx

/-! ### The restricted first moment -/

/-- The arithmetic of the assembly, isolated so the two big integrals never have to be written
out: from `P ≤ A·M·Q` and `ℓ·Q ≤ C` conclude `ℓ·P ≤ A·C·M`. -/
lemma mul_le_mul_of_join_of_norm {P Q l A C M : ℝ} (hl : 0 ≤ l) (hA : 0 < A) (hM : 0 ≤ M)
    (hjoin : P ≤ A * M * Q) (hnorm : l * Q ≤ C) : l * P ≤ A * C * M := by
  nlinarith [mul_nonneg hA.le hM]

/-! ### The chaos, and how its variants are named

Each is `(\log y)^{-1}` times an integral of `\|randomEulerProduct\|^2` over a window of heights,
which this development and Harper both call **the chaos**.  The name says which one in three
independent syllables:

* the window --- nothing for `[-1/2, 1/2]`, `Unit` for `[0, 1]`, `Window` for `[n, n+1]`;
* `Shift` --- the abscissa is `1/2 + \sigma` rather than `1/2`;
* `restricted` --- the integrand is cut down to a good-point family `G h`.

`RMF.eulerLineIntegral` is not one of them: it carries the weight `|1/2+it|^{-2}` and runs over
all of `\R`, as Gorodetsky--Wong's object does. -/

/-- **The restricted chaos on the unit window at a shifted abscissa**:
`(\log y)^{-1} ∫_0^1 1_{G h}(ω) ‖randomEulerProduct f (⌊y⌋₊+1) (1/2+σ+ih)‖² dh`.  The window is
`[0, 1]` because the decomposition puts the bad event `∃ h ∈ [0,1), ω ∉ G h` outside the height
integral and the maximal-barrier chain (`Probability/Chaining.lean` and up) is stated over
`[0, 1)`; for the Steinhaus law `RMF.integral_rpow_window_eq` moves any unit window there. -/
noncomputable def restrictedChaosUnitShift {Ω' : Type*} (f : Ω' → ArithmeticFunction ℂ)
    (y σ : ℝ) (G : ℝ → Set Ω') (ω : Ω') : ℝ :=
  (Real.log y)⁻¹ * ∫ h in (0 : ℝ)..1,
    Set.indicator (G h)
      (fun ω => ‖randomEulerProduct f (⌊y⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2) ω

/-- The `ω`-integral, with the constant outside and the interval integral as a set integral. -/
lemma integral_restrictedChaosUnitShift_eq {Ω' : Type*} [MeasurableSpace Ω']
    (f : Ω' → ArithmeticFunction ℂ) (ν : Measure Ω') (x σ : ℝ) (G : ℝ → Set Ω') :
    (∫ ω, restrictedChaosUnitShift f x σ G ω ∂ν)
      = (Real.log x)⁻¹ * ∫ ω, (∫ h in Set.Ioc (0 : ℝ) 1,
          Set.indicator (G h) (fun ω => ‖randomEulerProduct f (⌊x⌋₊ + 1)
            (shiftLine σ h) ω‖ ^ 2) ω) ∂ν := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  rw [restrictedChaosUnitShift, intervalIntegral.integral_of_le (by norm_num)]

/-- **The chaos on the unit window at a shifted abscissa**:
`(\log y)^{-1} ∫_0^1 ‖randomEulerProduct f (⌊y⌋₊+1) (1/2+σ+ih)‖² dh`.  `RMF.chaosUnit` is the case
`σ = 0`; `RMF.chaosShift` is the same integrand over `[-1/2, 1/2]`. -/
noncomputable def chaosUnitShift {Ω' : Type*} (f : Ω' → ArithmeticFunction ℂ)
    (y σ : ℝ) (ω : Ω') : ℝ :=
  (Real.log y)⁻¹ * ∫ h in (0 : ℝ)..1,
    ‖randomEulerProduct f (⌊y⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2

/-- At `σ = 0` it is `RMF.chaosUnit`. -/
lemma chaosUnitShift_zero {Ω' : Type*} (f : Ω' → ArithmeticFunction ℂ) (y : ℝ)
    (ω : Ω') : chaosUnitShift f y 0 ω = chaosUnit f y ω := by
  have hs : ∀ h : ℝ, shiftLine 0 h = ((1 / 2 : ℝ) : ℂ) + (h : ℂ) * Complex.I := fun h => by
    rw [shiftLine]; norm_num
  rw [chaosUnitShift, chaosUnit]
  simp only [hs]

/-! ### The chaos on an arbitrary unit window

`RMF.integral_rpow_window_eq` moves any unit window to `[0, 1]`, but it takes
`RMF.IsSteinhausPrimeValues`: its proof is rotation invariance
(`RMF.integral_rpow_unitFunctional_rotate` at `shiftConst n p = p^{-in}`), which the Rademacher
law does not have.  Harper's Proposition 2, the Rademacher case, keeps a `max` over the integer
translates `N`, damped by `(|N|+1)^{-1/8}` (Harper, arXiv:1703.06654).

So the Rademacher branch reads the chaos on `[n, n+1]`.  Nothing in the law obstructs that: the
barrier `RMF.IsRademacherPrimeValues.exists_const_measure_exists_barrier_le_of_le` is stated on an
arbitrary window, with `h₀` absent from its bound, and
`RMF.IsRademacherRMF.integral_normSq_shiftLine_eq` takes arbitrary heights.  The unit-window
definitions are the `n = 0` instances. -/

/-- **The restricted chaos on the window `[n, n+1]`** at a shifted abscissa:
`(\log y)^{-1} ∫_n^{n+1} 1_{G h}(ω) ‖randomEulerProduct f (⌊y⌋₊+1) (1/2+σ+ih)‖² dh`.
`RMF.restrictedChaosUnitShift` is the case `n = 0`. -/
noncomputable def restrictedChaosWindowShift {Ω' : Type*}
    (f : Ω' → ArithmeticFunction ℂ) (y σ n : ℝ) (G : ℝ → Set Ω') (ω : Ω') : ℝ :=
  (Real.log y)⁻¹ * ∫ h in n..(n + 1),
    Set.indicator (G h)
      (fun ω => ‖randomEulerProduct f (⌊y⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2) ω

/-- At `n = 0` it is `RMF.restrictedChaosUnitShift`. -/
lemma restrictedChaosWindowShift_zero {Ω' : Type*} (f : Ω' → ArithmeticFunction ℂ)
    (y σ : ℝ) (G : ℝ → Set Ω') (ω : Ω') :
    restrictedChaosWindowShift f y σ 0 G ω
      = restrictedChaosUnitShift f y σ G ω := by
  rw [restrictedChaosWindowShift, restrictedChaosUnitShift, zero_add]

/-- **The chaos on the window `[n, n+1]`** at a shifted abscissa:
`(\log y)^{-1} ∫_n^{n+1} ‖randomEulerProduct f (⌊y⌋₊+1) (1/2+σ+ih)‖² dh`.
`RMF.chaosUnitShift` is the case `n = 0`. -/
noncomputable def chaosWindowShift {Ω' : Type*} (f : Ω' → ArithmeticFunction ℂ)
    (y σ n : ℝ) (ω : Ω') : ℝ :=
  (Real.log y)⁻¹ * ∫ h in n..(n + 1),
    ‖randomEulerProduct f (⌊y⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2

/-- At `n = 0` it is `RMF.chaosUnitShift`. -/
lemma chaosWindowShift_zero {Ω' : Type*} (f : Ω' → ArithmeticFunction ℂ) (y σ : ℝ)
    (ω : Ω') : chaosWindowShift f y σ 0 ω = chaosUnitShift f y σ ω := by
  rw [chaosWindowShift, chaosUnitShift, zero_add]

/-- The `ω`-integral of the windowed restricted chaos, with the constant outside and the interval
integral as a set integral: the window form of `RMF.integral_restrictedChaosUnitShift_eq`. -/
lemma integral_restrictedChaosWindowShift_eq {Ω' : Type*} [MeasurableSpace Ω']
    (f : Ω' → ArithmeticFunction ℂ) (ν : Measure Ω') (x σ n : ℝ) (G : ℝ → Set Ω') :
    (∫ ω, restrictedChaosWindowShift f x σ n G ω ∂ν)
      = (Real.log x)⁻¹ * ∫ ω, (∫ h in Set.Ioc n (n + 1),
          Set.indicator (G h) (fun ω => ‖randomEulerProduct f (⌊x⌋₊ + 1)
            (shiftLine σ h) ω‖ ^ 2) ω) ∂ν := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  rw [restrictedChaosWindowShift, intervalIntegral.integral_of_le (by linarith)]

/-- **With no restriction the restricted chaos is the chaos** — the sanity check that the two
definitions above are the same object read two ways. -/
@[simp]
lemma restrictedChaosUnitShift_univ {Ω' : Type*} (f : Ω' → ArithmeticFunction ℂ)
    (y σ : ℝ) (ω : Ω') :
    restrictedChaosUnitShift f y σ (fun _ => Set.univ) ω
      = chaosUnitShift f y σ ω := by
  rw [restrictedChaosUnitShift, chaosUnitShift]
  congr 1
  refine intervalIntegral.integral_congr fun h _ => ?_
  simp

/-- The integrand is nonnegative, whatever the restriction. -/
lemma indicator_normSq_shift_nonneg {Ω' : Type*} (f : Ω' → ArithmeticFunction ℂ) (y σ : ℝ)
    (G : ℝ → Set Ω') (h : ℝ) (ω : Ω') :
    0 ≤ Set.indicator (G h)
      (fun ω => ‖randomEulerProduct f (⌊y⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2) ω :=
  Set.indicator_nonneg (fun _ _ => by positivity) ω

/-- The restricted chaos is nonnegative, whatever the restriction. -/
lemma restrictedChaosUnitShift_nonneg {Ω' : Type*} {f : Ω' → ArithmeticFunction ℂ}
    {y : ℝ} (hy : 1 < y) (σ : ℝ) (G : ℝ → Set Ω') (ω : Ω') :
    0 ≤ restrictedChaosUnitShift f y σ G ω := by
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos hy
  exact mul_nonneg (inv_nonneg.2 hlog.le)
    (intervalIntegral.integral_nonneg (by norm_num) fun h _ =>
      indicator_normSq_shift_nonneg f y σ G h ω)

/-- The window form of `RMF.restrictedChaosUnitShift_nonneg`.  Nothing about
nonnegativity sees the window: `n ≤ n + 1` is all that is used. -/
lemma restrictedChaosWindowShift_nonneg {Ω' : Type*} {f : Ω' → ArithmeticFunction ℂ}
    {y : ℝ} (hy : 1 < y) (σ n : ℝ) (G : ℝ → Set Ω') (ω : Ω') :
    0 ≤ restrictedChaosWindowShift f y σ n G ω := by
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos hy
  exact mul_nonneg (inv_nonneg.2 hlog.le)
    (intervalIntegral.integral_nonneg (by linarith) fun h _ =>
      indicator_normSq_shift_nonneg f y σ G h ω)

/-- The window form of `RMF.restrictedChaosUnitShift_univ`. -/
lemma restrictedChaosWindowShift_univ {Ω' : Type*} (f : Ω' → ArithmeticFunction ℂ)
    (y σ n : ℝ) (ω : Ω') :
    restrictedChaosWindowShift f y σ n (fun _ => Set.univ) ω
      = chaosWindowShift f y σ n ω := by
  rw [restrictedChaosWindowShift, chaosWindowShift]
  congr 1
  refine intervalIntegral.integral_congr fun h _ => ?_
  simp

/-- The window form of `RMF.chaosUnitShift_nonneg`. -/
lemma chaosWindowShift_nonneg {Ω' : Type*} {f : Ω' → ArithmeticFunction ℂ} {y : ℝ}
    (hy : 2 ≤ y) (σ n : ℝ) (ω : Ω') : 0 ≤ chaosWindowShift f y σ n ω := by
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  refine mul_nonneg (inv_nonneg.2 hlog.le) ?_
  exact intervalIntegral.integral_nonneg (by linarith) fun h _ => by positivity

/-- **Where every height is good, the restriction does nothing.**  The event runs over `[0,1)` and
the integral over `(0,1]`; they differ by the single point `1`, which is null. -/
lemma restrictedChaosUnitShift_eq_of_forall_mem {Ω' : Type*}
    {f : Ω' → ArithmeticFunction ℂ} {y σ : ℝ} (G : ℝ → Set Ω') {ω : Ω'}
    (hω : ∀ h ∈ Set.Ico (0 : ℝ) 1, ω ∈ G h) :
    restrictedChaosUnitShift f y σ G ω = chaosUnitShift f y σ ω := by
  rw [restrictedChaosUnitShift, chaosUnitShift]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ h : ℝ, h ≠ 1 := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with h hh1 hmem
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hmem
  exact Set.indicator_of_mem (hω h ⟨le_of_lt hmem.1, lt_of_le_of_ne hmem.2 hh1⟩) _

/-- **The basic inequality**, `Z² ≤ Z²(A) + 1(ω ∉ G_A)·Z²`, pointwise and at any abscissa. -/
lemma chaosUnitShift_le_restricted_add {Ω' : Type*} {f : Ω' → ArithmeticFunction ℂ}
    {y : ℝ} (hy : 1 < y) (σ : ℝ) (G : ℝ → Set Ω') (ω : Ω') :
    chaosUnitShift f y σ ω
      ≤ restrictedChaosUnitShift f y σ G ω
        + Set.indicator {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ω ∉ G h} (fun _ => (1 : ℝ)) ω
          * chaosUnitShift f y σ ω := by
  by_cases hmem : ω ∈ {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ω ∉ G h}
  · rw [Set.indicator_of_mem hmem, one_mul]
    linarith [restrictedChaosUnitShift_nonneg (f := f) hy σ G ω]
  · rw [Set.indicator_of_notMem hmem, zero_mul, add_zero]
    refine le_of_eq (restrictedChaosUnitShift_eq_of_forall_mem G fun h hh => ?_).symm
    by_contra hc
    exact hmem ⟨h, hh, hc⟩

/-- The chaos on the unit window at a shifted abscissa is nonnegative. -/
lemma chaosUnitShift_nonneg {Ω' : Type*} {f : Ω' → ArithmeticFunction ℂ} {y σ : ℝ}
    (hy : 2 ≤ y) (ω : Ω') : 0 ≤ chaosUnitShift f y σ ω := by
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  refine mul_nonneg (inv_nonneg.2 hlog.le) ?_
  exact intervalIntegral.integral_nonneg (by norm_num) fun h _ => by positivity

/-- **The restricted chaos at a shifted abscissa is integrable**, by the same Tonelli slice as at
`σ = 0`: `RMF.integrable_uncurry_indicator_normSq` already quantifies over the abscissa. -/
lemma integrable_restrictedChaosUnitShift {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (x σ : ℝ)
    (hσ0 : 0 < 1 / 2 + σ)
    (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {p : Ω' × ℝ | p.1 ∈ L p.2}) :
    Integrable (restrictedChaosUnitShift
      (fun ω => compMultExtension fun p => Y p ω) x σ L) ν := by
  have hInt := integrable_uncurry_indicator_normSq hY (⌊x⌋₊ + 1) hσ0
    L hLmeas hSmeas (T := Set.Ioc (0 : ℝ) 1)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hslice := hInt.integral_prod_left
  simp only [Function.uncurry_apply_pair] at hslice
  have hrw : restrictedChaosUnitShift
        (fun ω => compMultExtension fun p => Y p ω) x σ L
      = fun ω => (Real.log x)⁻¹ * ∫ t in Set.Ioc (0 : ℝ) 1, Set.indicator (L t)
          (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1)
            (shiftLine σ t) ω‖ ^ 2) ω := by
    funext ω
    rw [restrictedChaosUnitShift, intervalIntegral.integral_of_le (by norm_num)]
  rw [hrw]
  exact hslice.const_mul _

/-- **The unrestricted chaos at a shifted abscissa is integrable**, the case `G = univ`. -/
lemma integrable_chaosUnitShift {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (x σ : ℝ)
    (hσ0 : 0 < 1 / 2 + σ) :
    Integrable (chaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ) ν := by
  have h := integrable_restrictedChaosUnitShift hY x σ hσ0 (fun _ => Set.univ)
    (fun _ => MeasurableSet.univ) (by simp)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  exact restrictedChaosUnitShift_univ _ x σ ω

/-- **The mean chaos at a shifted abscissa is an identity, not an estimate.**
`E‖F(1/2+σ+it)‖² = ∏_{p<y}(1-p^{-1-2σ})^{-1}` does not move with the height, so the height integral
is that constant: `E[Z²] = (\log x)^{-1}E‖F(1/2+σ)‖²`. -/
lemma integral_chaosUnitShift_eq {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (x σ : ℝ)
    (hσ0 : 0 < 1 / 2 + σ) :
    (∫ ω, chaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ ω ∂ν)
      = (Real.log x)⁻¹ * ∫ ω, ‖randomEulerProduct
          (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν := by
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  have hf' : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  have hInt : Integrable (Function.uncurry fun (ω : Ω') (t : ℝ) =>
      Set.indicator (Set.univ : Set Ω')
        (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1)
          (shiftLine σ t) ω‖ ^ 2) ω)
      (ν.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    integrable_uncurry_indicator_normSq hY (⌊x⌋₊ + 1) hσ0
      (fun _ => Set.univ) (fun _ => MeasurableSet.univ) (by simp)
      (T := Set.Ioc (0 : ℝ) 1) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      (∫ ω, Set.indicator (Set.univ : Set Ω')
        (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1)
          (shiftLine σ t) ω‖ ^ 2) ω ∂ν)
        = ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1)
            (shiftLine σ 0) ω‖ ^ 2 ∂ν := by
    intro t _
    simp only [Set.indicator_univ]
    exact hf'.integral_normSq_shiftLine_eq (⌊x⌋₊ + 1) hσ0 t 0
  have hrw : (∫ ω, chaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ ω ∂ν)
      = ∫ ω, restrictedChaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ
          (fun _ => Set.univ) ω ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (restrictedChaosUnitShift_univ _ x σ ω).symm)
  rw [hrw, integral_restrictedChaosUnitShift_eq]
  congr 1
  rw [integral_integral_swap hInt, setIntegral_congr_fun measurableSet_Ioc hpt,
    setIntegral_const, Real.volume_real_Ioc]
  simp

/-- **The mean chaos at a shifted abscissa is bounded by an absolute constant**, for `2 ≤ x` and
`σ ≥ 0`.  The shift enters only the Mertens factor, where it helps
(`RMF.integral_normSq_shiftLine_mono`). -/
theorem exists_const_integral_chaosUnitShift_le :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
      IsSteinhausPrimeValues Y ν → ∀ x σ : ℝ, 2 ≤ x → 0 ≤ σ →
        (∫ ω, chaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ ω ∂ν)
          ≤ C := by
  obtain ⟨C, hC, H⟩ := exists_const_inv_log_mul_integral_normSq_shift_le
  refine ⟨C, hC, ?_⟩
  intro Ω' _ Y ν hY x σ hx hσ
  rw [integral_chaosUnitShift_eq hY x σ (by linarith)]
  exact H Ω' Y ν hY x σ hx hσ

/-- **Hamdan's decomposition (2.18) at a shifted abscissa**, pointwise: `Z²` is bounded by the
chaos restricted to the first barrier, plus one term per barrier of the family, plus the tail.

The telescoping step (`RMF.le_add_sum_add_of_le_add_mul`) is arithmetic and sees neither the
abscissa nor the barriers, so the shift enters only through the one-step inequality. -/
theorem chaosUnitShift_le_decomposition {Ω' : Type*}
    {f : Ω' → ArithmeticFunction ℂ} {y : ℝ} (hy : 1 < y) (σ : ℝ)
    (G : ℕ → ℝ → Set Ω') (ω : Ω') (r m : ℕ) (hrm : r ≤ m) :
    chaosUnitShift f y σ ω
      ≤ restrictedChaosUnitShift f y σ (G r) ω
        + (∑ j ∈ Finset.Ico r m,
            Set.indicator {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ω ∉ G j h} (fun _ => (1 : ℝ)) ω
              * restrictedChaosUnitShift f y σ (G (j + 1)) ω)
        + Set.indicator {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ω ∉ G m h} (fun _ => (1 : ℝ)) ω
            * chaosUnitShift f y σ ω := by
  refine le_add_sum_add_of_le_add_mul (Z := chaosUnitShift f y σ ω)
    (R := fun j => restrictedChaosUnitShift f y σ (G j) ω)
    (I := fun j => Set.indicator {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ω ∉ G j h}
      (fun _ => (1 : ℝ)) ω)
    ?_ ?_ ?_ (fun j => chaosUnitShift_le_restricted_add hy σ (G j) ω) r m hrm
  · have hlog : (0 : ℝ) < Real.log y := Real.log_pos hy
    exact mul_nonneg (inv_nonneg.2 hlog.le)
      (intervalIntegral.integral_nonneg (by norm_num) fun h _ => by positivity)
  · exact fun j => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  · exact fun j => Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le_one)

/-- **Hamdan's Proposition 2.1 on the unit window, at a shifted abscissa and a general tilt
scale.**  The join `RMF.exists_integral_restricted_normSq_le_of_le` takes the window as a
parameter, and only its length `1` is used.  This is the form the decomposition composes with. -/
theorem exists_const_integral_restrictedChaosUnitShift_le_of_le (E₀ : ℝ) (hE₀ : 0 ≤ E₀) :
    ∃ (D n₀ : ℕ) (x₀ a₀ C : ℝ), 4 ≤ D ∧ 0 < C ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (r : ℕ) (hf : ℕ → ℝ),
          x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η →
          a₀ ≤ a → 1 ≤ a →
          1 ≤ r → r ≤ harperBlockCount D x → (r : ℝ) ≤ a / 4 + 1 →
          n₀ ≤ harperBlockCount D x - r →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x → |hf j| ≤ 10 * Real.log j) →
            (∫ ω, restrictedChaosUnitShift
                (fun ω => compMultExtension fun p => Y p ω) x σ
                (fun t => {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t)))
                      (Y ((p : Nat.Primes) : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - blockSlopeOf E₀ 125 * (j : ℝ))
                        (a + (j : ℝ) + hf j)}) ω ∂ν)
              ≤ C * min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - r)) := by
  obtain ⟨D, n₀, x₀, a₀, A, hD, hA, H⟩ := exists_integral_restricted_normSq_le_of_le E₀ hE₀
  obtain ⟨CM, hCM, hMert⟩ := exists_const_inv_log_mul_integral_normSq_shift_le
  refine ⟨D, n₀, max x₀ 2, max a₀ 0, A * CM, hD, by positivity, ?_⟩
  intro Ω' _ Y ν hY x σ η a r hf hx hσ0 hη0 hηE hσ ha ha1 hr1 hrn hra hn₀ hhf
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have haa₀ : a₀ ≤ a := le_trans (le_max_left _ _) ha
  have ha0 : (0 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  have hlogx0 : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hmin0 : (0 : ℝ) ≤ min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - r)) :=
    le_min zero_le_one (div_nonneg ha0 (Real.sqrt_nonneg _))
  rw [integral_restrictedChaosUnitShift_eq]
  have hjoin := H Ω' Y ν hY x σ η a r (Set.Ioc (0 : ℝ) 1) hf hxx₀ hσ0 hη0
    hηE hσ haa₀ ha1 hr1 hrn hra hn₀ measurableSet_Ioc
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hhf
  have hvol : (volume (Set.Ioc (0 : ℝ) 1)).toReal = 1 := by
    rw [Real.volume_Ioc]
    norm_num
  rw [hvol, one_mul] at hjoin
  exact mul_le_mul_of_join_of_norm (inv_nonneg.2 hlogx0.le) hA hmin0 hjoin
    (hMert Ω' Y ν hY x σ hx2 hσ0)

/-- **Hamdan's Proposition 2.1 on the unit window at a shifted abscissa, with the top `d` blocks
dropped.**  The barrier is constrained on `[r, n-d]` while the chaos and the tilt run to `x`, with
the slope `RMF.blockSlope 125`.  `D`, `n₀`, `a₀` and `C` do not depend on `d` or on `E₀ ≤ e^d`;
only `x₀` does.  `RMF.exists_const_integral_restrictedChaosUnitShift_le_of_le` keeps every block. -/
theorem exists_const_integral_restrictedChaosUnitShift_le_of_top :
    ∃ (D n₀ : ℕ) (a₀ C : ℝ), 4 ≤ D ∧ 0 < C ∧
      ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (r : ℕ) (hf : ℕ → ℝ),
          x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η →
          a₀ ≤ a → 1 ≤ a →
          1 ≤ r → r ≤ harperBlockCount D x → (r : ℝ) ≤ a / 4 + 1 →
          2 * d ≤ harperBlockCount D x - r → n₀ ≤ harperBlockCount D x - r - d →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            (∫ ω, restrictedChaosUnitShift
                (fun ω => compMultExtension fun p => Y p ω) x σ
                (fun t => {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x - d →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t)))
                      (Y ((p : Nat.Primes) : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - blockSlope 125 * (j : ℝ))
                        (a + (j : ℝ) + hf j)}) ω ∂ν)
              ≤ C * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ) - r)) := by
  obtain ⟨D, n₀, a₀, A, hD, hA, H⟩ := exists_integral_restricted_normSq_le_of_top
  obtain ⟨CM, hCM, hMert⟩ := exists_const_inv_log_mul_integral_normSq_shift_le
  refine ⟨D, n₀, max a₀ 0, A * CM, hD, by positivity, ?_⟩
  intro d E₀ hE₀ hEd
  obtain ⟨x₀, H⟩ := H d E₀ hE₀ hEd
  refine ⟨max x₀ 2, ?_⟩
  intro Ω' _ Y ν hY x σ η a r hf hx hσ0 hη0 hηE hσ ha ha1 hr1 hrn hra hdn hn₀ hhf
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have haa₀ : a₀ ≤ a := le_trans (le_max_left _ _) ha
  have ha0 : (0 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  have hlogx0 : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hmin0 : (0 : ℝ) ≤ min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ) - r)) :=
    le_min zero_le_one (div_nonneg ha0 (Real.sqrt_nonneg _))
  rw [integral_restrictedChaosUnitShift_eq]
  have hjoin := H Ω' Y ν hY x σ η a r (Set.Ioc (0 : ℝ) 1) hf hxx₀ hσ0 hη0
    hηE hσ haa₀ ha1 hr1 hrn hra hdn hn₀ measurableSet_Ioc
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hhf
  have hvol : (volume (Set.Ioc (0 : ℝ) 1)).toReal = 1 := by
    rw [Real.volume_Ioc]
    norm_num
  rw [hvol, one_mul] at hjoin
  exact mul_le_mul_of_join_of_norm (inv_nonneg.2 hlogx0.le) hA hmin0 hjoin
    (hMert Ω' Y ν hY x σ hx2 hσ0)

end RMF
