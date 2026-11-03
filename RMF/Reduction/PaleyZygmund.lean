/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RestrictedSecondMoment
import RMF.Reduction.Numerator

/-!
# Numerator and denominator on the same event

Paley–Zygmund needs `∫X` and `∫X²` for the **same** `X`.  The numerator is stated in
`RMF/Reduction/Numerator.lean` on the grid `RMF.harperOffset D x` with block count
`RMF.harperBlockCount D x - d`; the denominator, Harper's Key Proposition 5, is stated in
`RMF/Probability/RestrictedSecondMoment.lean` on `RMF.harperTheta B x` with barrier top
`RMF.harperBarrierTop B V x`.

They are the same grid, at

`D = B + 2` and `d = ⌊\log V⌋ + 3`,

which is `RMF.harperOffset_eq_harperTheta` and `RMF.harperBlockCount_sub_eq_harperBarrierTop`; and
the two products agree because `RMF.blockScale_harperN_succ` makes
`blockCutoff (harperTheta B x) (harperN B x)` equal to `⌊x⌋₊ + 1`.

The tilt condition closes too, though not by much: the numerator wants
`|σ|\log x ≤ η ≤ E₀ ≤ e^d`, and at Harper's data `η = 4V` against `e^d = e^{⌊\log V⌋+3}`.  The
ratio `e^d/(4V)` is smallest as the fractional part of `\log V` approaches `1`, where it tends to
`e²/4 ≈ 1.847`.  So `E₀ = 4V` fits at every `V`, with under a factor of two in hand
(`RMF.four_mul_le_exp_floor_log_add_three`).

The numerator chain quantifies `∃ D₀, ∀ D ≥ D₀`, which this identification needs: a single
`B = D - 2` would not do, since the denominator needs `B ≥ 124` (its barrier wants `θ ≥ 125`).
-/

namespace RMF

open MeasureTheory

/-- **The tilt scale fits under the drop**: `4V ≤ e^{⌊\log V⌋+3}`.

`⌊\log V⌋ > \log V - 1` gives `e^{⌊\log V⌋+3} > Ve²`, and `4 ≤ e²`.  The slack is exactly
`e²/4 = 1.847` in the limit, which is why `d = ⌊\log V⌋ + 3` and not `+2`: at `+2` the bound would
read `4 ≤ e`, which is false. -/
lemma four_mul_le_exp_floor_log_add_three {V : ℝ} (hV : 1 ≤ V) :
    4 * V ≤ Real.exp (((⌊Real.log V⌋₊ : ℕ) : ℝ) + 3) := by
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hV0 : (0 : ℝ) < V := by linarith
  have hfl : Real.log V - 1 < ((⌊Real.log V⌋₊ : ℕ) : ℝ) := by
    linarith [Nat.lt_floor_add_one (Real.log V)]
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by nlinarith [h2.ge, h2.le, he1]
  calc 4 * V ≤ Real.exp 2 * V := by nlinarith
    _ = Real.exp (Real.log V + 2) := by
        rw [Real.exp_add, Real.exp_log hV0]
        ring
    _ ≤ Real.exp (((⌊Real.log V⌋₊ : ℕ) : ℝ) + 3) := Real.exp_le_exp.2 (by linarith)

/-- **The product's cutoff, in Harper's variables.**  `blockCutoff θ N = ⌊x⌋₊ + 1`, because the
block above the top is `x` itself. -/
lemma blockCutoff_harperN {B : ℕ} {x : ℝ} (hx1 : 1 < x)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x)) :
    blockCutoff (harperTheta B x) (harperN B x) = ⌊x⌋₊ + 1 := by
  rw [blockCutoff, blockScale_harperN_succ hx1 hx]

/-- **`RMF.exists_le_integral_restricted_normSq_harper_data` with the level left
free.**  Specialising the numerator to Harper's own scales — `θ = harperTheta B x`,
`n - d = harperBarrierTop B V x`, cutoff `⌊x⌋₊ + 1` — moves neither the level nor the block
offset, so the level that reaches Paley–Zygmund is the numerator's. -/
theorem le_integral_restricted_normSq_harper_data_of_numerator.{u} {D₀ : ℕ} {a₀ α : ℝ}
    (H :
      ∀ D : ℕ, D₀ ≤ D → ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (T : Set ℝ) (hf : ℕ → ℝ),
          x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η → a₀ ≤ a →
          MeasurableSet T → volume T ≠ ⊤ →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            (volume T).toReal
                * (α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ))))
                * Real.exp (((harperBlockCount D x - d : ℕ) : ℝ) - 63)
              ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
                    (harperBlockCount D x - d)
                    (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))
                  (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω) ∂ν) :
    ∀ B : ℕ, D₀ ≤ B → ∀ V : ℝ, 1 ≤ V → ∃ x₀ : ℝ,
    ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
      IsSteinhausPrimeValues Y ν →
      ∀ (x σ a : ℝ) (T : Set ℝ),
        x₀ ≤ x → 1 < x → (B : ℝ) + 2 ≤ Real.log (Real.log x) →
        0 ≤ σ → σ * Real.log x ≤ 4 * V → a₀ ≤ a →
        MeasurableSet T → volume T ≠ ⊤ →
          (volume T).toReal
              * (α * min 1 (a / Real.sqrt (((harperBarrierTop B V x : ℕ) : ℝ))))
              * Real.exp (((harperBarrierTop B V x : ℕ) : ℝ) - 63)
            ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                  (fun m ω => ∑ p ∈ primeBlockSub (harperTheta B x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
                  (harperBarrierTop B V x)
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j))
                (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                ∂ν := by
  intro B hB V hV
  obtain ⟨x₀, H⟩ := H (B + 2) (by omega) (⌊Real.log V⌋₊ + 3) (4 * V)
    (by linarith) (by push_cast; exact four_mul_le_exp_floor_log_add_three hV)
  refine ⟨x₀, ?_⟩
  intro Ω' _ Y ν hY x σ a T hx hx1 hxΛ hσ0 hσ4 ha hT hTfin
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hsrc := H Ω' Y ν hY x σ (σ * Real.log x) a T harperHf hx hσ0
    (by positivity) hσ4 (by rw [abs_of_nonneg hσ0]) ha hT hTfin
    (fun j _ _ => abs_harperHf_le j)
  rw [harperOffset_eq_harperTheta B hΛ0, harperBlockCount_sub_eq_harperBarrierTop B V x] at hsrc
  rwa [blockCutoff_harperN hx1 hxΛ]

/-- **The numerator at Harper's numeric data** — the numerator of Paley–Zygmund, on exactly the
event and product that `RMF.integral_sq_setIntegral_indicator_normSq_harper_data_le` bounds.
`B₀` is the numerator chain's own `D₀` shifted by two; the caller combines it with the
denominator's. -/
theorem exists_le_integral_restricted_normSq_harper_data :
    ∃ (B₀ : ℕ) (a₀ α : ℝ), 0 < α ∧
      ∀ B : ℕ, B₀ ≤ B → ∀ V : ℝ, 1 ≤ V → ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ a : ℝ) (T : Set ℝ),
          x₀ ≤ x → 1 < x → (B : ℝ) + 2 ≤ Real.log (Real.log x) →
          0 ≤ σ → σ * Real.log x ≤ 4 * V → a₀ ≤ a →
          MeasurableSet T → volume T ≠ ⊤ →
            (volume T).toReal
                * (α * min 1 (a / Real.sqrt (((harperBarrierTop B V x : ℕ) : ℝ))))
                * Real.exp (((harperBarrierTop B V x : ℕ) : ℝ) - 63)
              ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperTheta B x) m,
                      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
                    (harperBarrierTop B V x)
                    (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j))
                  (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                  ∂ν := by
  obtain ⟨D₀, a₀, α, hD₀, hα, H⟩ := exists_le_integral_restricted_normSq_numerator
  exact ⟨D₀, a₀, α, hα,
    le_integral_restricted_normSq_harper_data_of_numerator H⟩

/-! ### Paley–Zygmund on the restricted integral

`RMF.rpow_integral_div_rpow_integral_sq_le_integral_rpow` is
`(\int X)^{2-q}/(\int X^2)^{1-q} \le \int X^q`.  Its three side conditions are all available for
`X ω = \int_T 1_{L(t)}(ω)‖F_t(ω)‖^2\,dt`: `X` is a.e. measurable because the integrand is jointly
integrable (`RMF.integrable_uncurry_indicator_normSq`), and it is a.e. **bounded** by
`\text{eulerBound } y^2·|T|` because `RMF.ae_forall_norm_indicator_normSq_shiftLine_le` bounds the
integrand pointwise — so both `X^q` and `X^2` are integrable against a probability measure.  The
positivity of `\int X^2` comes from the numerator: if it vanished then `X` would vanish a.e. and
`\int X` with it. -/

/-- **Paley–Zygmund, with the two bounds substituted**: a lower bound `N` on the numerator and an
upper bound `Dn` on the denominator give `N^{2-q}/Dn^{1-q} ≤ \int X^q`.  No law appears here: the
two facts the argument needs of the model — that the indicator's square is jointly integrable, and
a.e. bounded by `RMF.eulerBound y ^ 2` — are hypotheses about a bare `f`, so both RMFs are
instances; beyond them, `ν` must be a probability measure. -/
theorem rpow_div_rpow_le_integral_rpow_of_bounds_of_integrable {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → ArithmeticFunction ℂ} {ν : Measure Ω'} [IsProbabilityMeasure ν] (y : ℕ) {σ : ℝ}
    (L : ℝ → Set Ω') {T : Set ℝ} (hTm : MeasurableSet T) (hTfin : volume T ≠ ⊤)
    (hbase : Integrable (Function.uncurry fun (ω : Ω') (t : ℝ) =>
        Set.indicator (L t) (fun ω => ‖randomEulerProduct f y (shiftLine σ t) ω‖ ^ 2) ω)
      (ν.prod (volume.restrict T)))
    (hbnd : ∀ᵐ ω ∂ν, ∀ t : ℝ, ‖Set.indicator (L t)
        (fun ω => ‖randomEulerProduct f y (shiftLine σ t) ω‖ ^ 2) ω‖ ≤ eulerBound y ^ 2)
    {q N Dn : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hN0 : 0 < N) (hDn0 : 0 < Dn)
    (hN : N ≤ ∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct f y (shiftLine σ t) ω‖ ^ 2) ω) ∂ν)
    (hD : (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct f y (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν) ≤ Dn) :
    N ^ (2 - q) / Dn ^ (1 - q)
      ≤ ∫ ω, (∫ t in T, Set.indicator (L t)
          (fun ω => ‖randomEulerProduct f y (shiftLine σ t) ω‖ ^ 2) ω) ^ q ∂ν := by
  haveI : IsFiniteMeasure (volume.restrict T) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hTfin⟩
  set g : ℝ → Ω' → ℝ := fun t ω =>
    ‖randomEulerProduct f y (shiftLine σ t) ω‖ ^ 2
    with hgdef
  set X : Ω' → ℝ := fun ω => ∫ t in T, Set.indicator (L t) (g t) ω with hXdef
  -- `X` is measurable and a.e. bounded
  have hXm : AEStronglyMeasurable X ν := hbase.integral_prod_left.aestronglyMeasurable
  have hXb : ∀ᵐ ω ∂ν, ‖X ω‖ ≤ eulerBound y ^ 2 * volume.real T := by
    filter_upwards [hbnd] with ω hω
    exact norm_setIntegral_le_of_norm_le_const (lt_of_le_of_ne le_top hTfin) fun t _ => hω t
  have hX0 : 0 ≤ᵐ[ν] X := by
    refine Filter.Eventually.of_forall fun ω => ?_
    refine setIntegral_nonneg hTm ?_
    intro t _
    exact Set.indicator_nonneg (fun _ _ => by positivity) ω
  -- both powers are integrable, being bounded on a probability space
  have hXqm : AEStronglyMeasurable (fun ω => X ω ^ q) ν :=
    (Real.continuous_rpow_const hq0.le).comp_aestronglyMeasurable hXm
  have hX2m : AEStronglyMeasurable (fun ω => X ω ^ (2 : ℝ)) ν :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)).comp_aestronglyMeasurable hXm
  have hXle : ∀ᵐ ω ∂ν, X ω ≤ eulerBound y ^ 2 * volume.real T := by
    filter_upwards [hX0, hXb] with ω h0 hb
    rwa [Real.norm_eq_abs, abs_of_nonneg h0] at hb
  have hXq : Integrable (fun ω => X ω ^ q) ν := by
    refine Integrable.mono' (integrable_const ((eulerBound y ^ 2 * volume.real T) ^ q)) hXqm ?_
    filter_upwards [hX0, hXle] with ω h0 hb
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 q)]
    exact Real.rpow_le_rpow h0 hb hq0.le
  have hX2 : Integrable (fun ω => X ω ^ (2 : ℝ)) ν := by
    refine Integrable.mono' (integrable_const ((eulerBound y ^ 2 * volume.real T) ^ (2 : ℝ)))
      hX2m ?_
    filter_upwards [hX0, hXle] with ω h0 hb
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _)]
    exact Real.rpow_le_rpow h0 hb (by norm_num)
  -- the denominator is positive, because the numerator is
  have hpos : 0 < ∫ ω, X ω ^ (2 : ℝ) ∂ν := by
    rcases lt_or_eq_of_le (integral_nonneg_of_ae (hX0.mono fun ω h => Real.rpow_nonneg h _))
      with h | h
    · exact h
    · exfalso
      have hzero := (integral_eq_zero_iff_of_nonneg_ae
        (hX0.mono fun ω hω => Real.rpow_nonneg hω _) hX2).1 h.symm
      have hX0' : X =ᵐ[ν] 0 := by
        filter_upwards [hzero, hX0] with ω hω h0
        have : X ω ^ (2 : ℝ) = 0 := hω
        by_contra hne
        exact hne (by
          have hp : 0 < X ω := lt_of_le_of_ne h0 (Ne.symm hne)
          exact absurd this (ne_of_gt (Real.rpow_pos_of_pos hp 2)))
      have : (∫ ω, X ω ∂ν) = 0 := by
        rw [integral_congr_ae hX0']
        simp
      linarith [hN, hN0]
  -- Paley–Zygmund, then the two substitutions
  have hPZ := rpow_integral_div_rpow_integral_sq_le_integral_rpow hq0 hq1 hX0 hXq hX2 hpos
  refine le_trans ?_ hPZ
  have hsq : (∫ ω, X ω ^ (2 : ℝ) ∂ν) = ∫ ω, X ω ^ 2 ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => Real.rpow_two (X ω))
  have hX0' : (0 : ℝ) ≤ ∫ ω, X ω ∂ν := integral_nonneg_of_ae hX0
  have hnum : N ^ (2 - q) ≤ (∫ ω, X ω ∂ν) ^ (2 - q) :=
    Real.rpow_le_rpow hN0.le hN (by linarith)
  have hden : (∫ ω, X ω ^ (2 : ℝ) ∂ν) ^ (1 - q) ≤ Dn ^ (1 - q) := by
    refine Real.rpow_le_rpow hpos.le ?_ (by linarith)
    rw [hsq]
    exact hD
  have hdpos : (0 : ℝ) < (∫ ω, X ω ^ (2 : ℝ) ∂ν) ^ (1 - q) := Real.rpow_pos_of_pos hpos _
  have hNp : (0 : ℝ) < N ^ (2 - q) := Real.rpow_pos_of_pos hN0 _
  calc N ^ (2 - q) / Dn ^ (1 - q)
      ≤ (∫ ω, X ω ∂ν) ^ (2 - q) / Dn ^ (1 - q) := by gcongr
    _ ≤ (∫ ω, X ω ∂ν) ^ (2 - q) / (∫ ω, X ω ^ (2 : ℝ) ∂ν) ^ (1 - q) := by gcongr

/-- **Paley–Zygmund on the restricted integral, for the Steinhaus RMF.**  The
`RMF.rpow_div_rpow_le_integral_rpow_of_bounds_of_integrable` instance; the mathematics is there. -/
theorem rpow_div_rpow_le_integral_rpow_of_bounds {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTm : MeasurableSet T)
    (hTfin : volume T ≠ ⊤)
    {q N Dn : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hN0 : 0 < N) (hDn0 : 0 < Dn)
    (hN : N ≤ ∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ∂ν)
    (hD : (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν) ≤ Dn) :
    N ^ (2 - q) / Dn ^ (1 - q)
      ≤ ∫ ω, (∫ t in T, Set.indicator (L t)
          (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
            (shiftLine σ t) ω‖ ^ 2) ω) ^ q ∂ν := by
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  exact rpow_div_rpow_le_integral_rpow_of_bounds_of_integrable y L hTm hTfin
    (integrable_uncurry_indicator_normSq hY y (by linarith) L hLmeas hSmeas hTfin)
    (ae_forall_norm_indicator_normSq_shiftLine_le hY y hσ L)
    hq0 hq1 hN0 hDn0 hN hD
/-! ### Harper's choice of the level `a`

The requirement Paley–Zygmund leaves is

`\min\{1, a/\sqrt n\} \gg 1/(1 + (1-q)\sqrt Λ)`,

and `RestrictedFirstMoment.lean`'s module docstring settles it with
`a := \max\{a_0, \min\{\sqrt n, 1/(1-q)\}\}`.  `a_0` never enters: all that is used is
`a ≥ \min\{\sqrt n, 1/(1-q)\}`, and the constant is **exactly `1`**. -/

/-- **The level clears the shape factor**, with constant `1`.

`\min\{1, a/s\} ≥ 1/(1+ds)` whenever `a ≥ \min\{s, 1/d\}`.  Both cases are one line: if `s ≤ 1/d`
then `a(1+ds) ≥ s(1+ds) ≥ s`, and if `s > 1/d` then `a(1+ds) ≥ 1/d + s ≥ s`. -/
lemma one_div_one_add_mul_le_min {a s d : ℝ} (hs : 0 < s) (hd0 : 0 < d)
    (ha : min s (1 / d) ≤ a) :
    1 / (1 + d * s) ≤ min 1 (a / s) := by
  have hds : (0 : ℝ) < d * s := by positivity
  have hmin0 : (0 : ℝ) < min s (1 / d) := lt_min hs (by positivity)
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le hmin0 ha
  refine le_min ?_ ?_
  · rw [div_le_one (by linarith)]
    linarith
  · rw [div_le_div_iff₀ (by linarith) hs]
    have hkey : s ≤ min s (1 / d) * (1 + d * s) := by
      rcases le_total s (1 / d) with h | h
      · rw [min_eq_left h]
        nlinarith
      · rw [min_eq_right h]
        have hexp : (1 / d) * (1 + d * s) = 1 / d + s := by
          field_simp
        rw [hexp]
        have : (0 : ℝ) < 1 / d := by positivity
        linarith
    nlinarith [hkey, ha, hds]

/-- **Harper's level.**  `a := \max\{a_0, \min\{\sqrt n, 1/(1-q)\}\}`: the barrier wants `a ≥ a_0`
absolutely, and the shape factor wants `a ≥ \min\{\sqrt n, 1/(1-q)\}`. -/
noncomputable def harperLevel (a₀ n q : ℝ) : ℝ :=
  max a₀ (min (Real.sqrt n) (1 / (1 - q)))

lemma le_harperLevel (a₀ n q : ℝ) : a₀ ≤ harperLevel a₀ n q := le_max_left _ _

/-- **What the level buys**: `1/W ≤ \min\{1, a/\sqrt n\}` at `a = harperLevel`, where
`W = 1 + (1-q)\sqrt Λ`.

The block count `n` is at most `Λ`, so `\sqrt n ≤ \sqrt Λ` and the `W` built on `Λ` is the larger
of the two — which is the direction needed, since it sits in a denominator. -/
lemma one_div_W_le_min_one_div_sqrt {a₀ n Λ q : ℝ} (hn : 0 < n) (hnΛ : n ≤ Λ) (hq1 : q < 1) :
    1 / (1 + (1 - q) * Real.sqrt Λ) ≤ min 1 (harperLevel a₀ n q / Real.sqrt n) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hd : (0 : ℝ) < 1 - q := by linarith
  have hsn : Real.sqrt n ≤ Real.sqrt Λ := Real.sqrt_le_sqrt hnΛ
  refine le_trans ?_ (one_div_one_add_mul_le_min hs hd (le_max_right _ _))
  gcongr

/-! ### The composition, and the level's joint range

Feeding `RMF.exists_le_integral_restricted_normSq_harper_data` and
`RMF.integral_sq_setIntegral_indicator_normSq_harper_data_le` into
`RMF.rpow_div_rpow_le_integral_rpow_of_bounds` gives the lower bound on `\int X^q`.

**The level `a` and the shape parameter `m` are separate, and that is what makes the range
non-empty.**  The numerator wants `a₀ ≤ a`, `a₀` the threshold of Probability Lemma 1's chain
(through `RMF.result1Threshold`); the denominator wants `m ≤ √Λ`, `m(1-q) ≤ 1` and
`a ≤ m + κ\log 2`.  Harper's `m = \min\{√Λ, 1/(1-q)\}` works at every `q`, the last condition
being `κ ≥ (a₀ - m)/\log 2`, checkable because `a₀` and `α` are bound before `κ`.  Taking `m := a`
instead would force `a(1-q) ≤ 1`, hence `q ≥ 1 - 1/a₀`.  The slack is paid through the
denominator's `K = K₀ + 2κ`.

**`a₀` is `1.59·10¹¹`, not `8000`** — the `8000` is only the first argument of
`RMF.result1Threshold`'s `max`, and the second one binds.  Since the shape factor is
`e^{-2(1+κ\log 2)} = e^{-2(1+a₀)}`, that is what fixes the size of Harper's constant here; see the
note on `RMF.result1Threshold`. -/

/-- **`RMF.exists_le_integral_rpow_harper_data` with the level left free.**  Paley–Zygmund does
not move the level: it pairs the numerator bound with
`RMF.integral_sq_setIntegral_indicator_normSq_harper_data_le` on the same barrier event and takes
the larger of the two block offsets.  So the level that reaches the reduction is the numerator's
own. -/
theorem le_integral_rpow_harper_data_of_numerator.{u} {B₁ : ℕ} {a₀ α : ℝ}
    (hα : 0 < α) (HN :
      ∀ B : ℕ, B₁ ≤ B → ∀ V : ℝ, 1 ≤ V → ∃ x₀ : ℝ,
      ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ a : ℝ) (T : Set ℝ),
          x₀ ≤ x → 1 < x → (B : ℝ) + 2 ≤ Real.log (Real.log x) →
          0 ≤ σ → σ * Real.log x ≤ 4 * V → a₀ ≤ a →
          MeasurableSet T → volume T ≠ ⊤ →
            (volume T).toReal
                * (α * min 1 (a / Real.sqrt (((harperBarrierTop B V x : ℕ) : ℝ))))
                * Real.exp (((harperBarrierTop B V x : ℕ) : ℝ) - 63)
              ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperTheta B x) m,
                      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
                    (harperBarrierTop B V x)
                    (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j))
                  (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                  ∂ν) :
    ∀ κ : ℝ, 0 ≤ κ → ∃ B₀ : ℕ,
    ∀ B : ℕ, B₀ ≤ B →
    ∀ (Ω' : Type u) [MeasurableSpace Ω'], ∃ E : ℝ, 0 < E ∧
      ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ x₀ : ℝ,
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
      ∀ (σ a q m x : ℝ) (T : Set ℝ),
        x₀ ≤ x → 1 < x → 3 ≤ x → Λ₀ ≤ Real.log (Real.log x) →
        (B : ℝ) + 2 ≤ Real.log (Real.log x) →
        6 * (B : ℝ) + 3 * Real.log V + 40 ≤ Real.log (Real.log x) →
        4 * V * (4 * Real.exp (2 * (B : ℝ) + 6) + 7) ≤ Real.log x →
        0 < σ → σ ≤ 1 / 2 → σ * Real.log x = 4 * V →
        MeasurableSet T → T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → volume T ≠ ⊤ →
        0 < (volume T).toReal →
        a₀ ≤ a → 1 ≤ a → 0 ≤ m → m ≤ Real.sqrt (Real.log (Real.log x)) →
        m * (1 - q) ≤ 1 → a ≤ m + κ * Real.log 2 →
        0 < q → q < 1 → 1 ≤ q * Real.sqrt (Real.log (Real.log x)) →
          ((volume T).toReal
                * (α * min 1 (a / Real.sqrt (((harperBarrierTop B V x : ℕ) : ℝ))))
                * Real.exp (((harperBarrierTop B V x : ℕ) : ℝ) - 63)) ^ (2 - q)
              / ((6 + 2 / Real.log 2) * (E * Real.exp (2 * a) * (1 / σ) ^ 2
                  / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ 2)) ^ (1 - q)
            ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                  (fun m ω => ∑ p ∈ primeBlockSub (harperTheta B x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
                  (harperBarrierTop B V x)
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j))
                (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                ^ q ∂ν := by
  intro κ hκ
  obtain ⟨B₂, HD⟩ := integral_sq_setIntegral_indicator_normSq_harper_data_le κ hκ
  refine ⟨max B₁ B₂, ?_⟩
  intro B hB Ω' _
  obtain ⟨E, hE, HD⟩ := HD B (le_trans (le_max_right _ _) hB) Ω'
  refine ⟨E, hE, ?_⟩
  intro V hV
  obtain ⟨x₀, HN⟩ := HN B (le_trans (le_max_left _ _) hB) V hV
  obtain ⟨Λ₀, HD⟩ := HD V hV
  refine ⟨Λ₀, x₀, ?_⟩
  intro Y ν hY σ a q m x T hx hx1 hx3 hΛ₀ hxΛ hΛcnt hfarwin hσ0 hσhalf hσeq hTm hTsub
    hTfin hT0
    ha₀ ha1 hm0 hmΛ hmq ham hq0 hq1 hqΛ
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hσ4 : σ * Real.log x ≤ 4 * V := le_of_eq hσeq
  -- the barrier top is positive
  have hΛ6 : (B : ℝ) + Real.log V + 6 ≤ Real.log (Real.log x) := by linarith
  have hle := floor_log_add_three_le_harperN hV hxΛ hΛ6
  have hbge := barrierTop_ge_data hV hxΛ hle
  have hb0R : (0 : ℝ) < ((harperBarrierTop B V x : ℕ) : ℝ) := by linarith
  have hsq0 : (0 : ℝ) < Real.sqrt (((harperBarrierTop B V x : ℕ) : ℝ)) := Real.sqrt_pos.2 hb0R
  -- the two bounds
  have hnum := HN Ω' Y ν hY x σ a T hx hx1 hxΛ hσ0.le hσ4 ha₀ hTm hTfin
  have hden := HD Y ν hY σ a q m x T hx1 hx3 hΛ₀ hΛcnt hfarwin hσ0 hσhalf hσeq hTm hTsub
    ha1
    hm0 hmΛ hmq ham (by linarith) hq1.le hqΛ
  -- the measurability the Paley–Zygmund step needs
  have hXmeas : ∀ (t : ℝ) (m : ℕ), Measurable (fun ω => ∑ p ∈ primeBlockSub (harperTheta B x) m,
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) := fun t m =>
    Finset.measurable_sum _ fun p _ => (measurable_localLog _).comp (hY.measurable (p : ℕ) p.2)
  -- both bounds are positive
  have hminpos : (0 : ℝ) < min 1 (a / Real.sqrt (((harperBarrierTop B V x : ℕ) : ℝ))) :=
    lt_min one_pos (by positivity)
  have hNpos : (0 : ℝ) < (volume T).toReal
      * (α * min 1 (a / Real.sqrt (((harperBarrierTop B V x : ℕ) : ℝ))))
      * Real.exp (((harperBarrierTop B V x : ℕ) : ℝ) - 63) := by positivity
  have hWpos : (0 : ℝ) < 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) := by
    nlinarith [Real.sqrt_nonneg (Real.log (Real.log x))]
  have hDpos : (0 : ℝ) < (6 + 2 / Real.log 2) * (E * Real.exp (2 * a) * (1 / σ) ^ 2
      / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ 2) := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  exact rpow_div_rpow_le_integral_rpow_of_bounds hY (blockCutoff (harperTheta B x) (harperN B x))
    hσ0.le _ (fun t => measurableSet_barrierEvent (hXmeas t) _ _ _)
    (measurableSet_prod_barrierEvent hY (harperTheta B x) σ (harperBarrierTop B V x) _ _)
    hTm hTfin hq0 hq1 hNpos hDpos hnum hden

/-- **The lower bound on `\int X^q`, composed**: Paley–Zygmund with the numerator and denominator
both at Harper's data, on the same barrier event.  The conclusion is the raw quotient; its
simplification to `(\log x)^q V^{-q} W^{-q}` is `RMF.exists_le_integral_rpow_harper_shape`, using
`RMF.one_div_W_le_min_one_div_sqrt` for the shape factor and `RMF.exp_neg_le_exp_neg_two_mul`
for `e^{-2a(1-q)}`. -/
theorem exists_le_integral_rpow_harper_data :
    ∃ (a₀ α : ℝ), 0 < α ∧ ∀ κ : ℝ, 0 ≤ κ → ∃ B₀ : ℕ,
      ∀ B : ℕ, B₀ ≤ B →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'], ∃ E : ℝ, 0 < E ∧
        ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ x₀ : ℝ,
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
        ∀ (σ a q m x : ℝ) (T : Set ℝ),
          x₀ ≤ x → 1 < x → 3 ≤ x → Λ₀ ≤ Real.log (Real.log x) →
          (B : ℝ) + 2 ≤ Real.log (Real.log x) →
          6 * (B : ℝ) + 3 * Real.log V + 40 ≤ Real.log (Real.log x) →
          4 * V * (4 * Real.exp (2 * (B : ℝ) + 6) + 7) ≤ Real.log x →
          0 < σ → σ ≤ 1 / 2 → σ * Real.log x = 4 * V →
          MeasurableSet T → T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → volume T ≠ ⊤ →
          0 < (volume T).toReal →
          a₀ ≤ a → 1 ≤ a → 0 ≤ m → m ≤ Real.sqrt (Real.log (Real.log x)) →
          m * (1 - q) ≤ 1 → a ≤ m + κ * Real.log 2 →
          0 < q → q < 1 → 1 ≤ q * Real.sqrt (Real.log (Real.log x)) →
            ((volume T).toReal
                  * (α * min 1 (a / Real.sqrt (((harperBarrierTop B V x : ℕ) : ℝ))))
                  * Real.exp (((harperBarrierTop B V x : ℕ) : ℝ) - 63)) ^ (2 - q)
                / ((6 + 2 / Real.log 2) * (E * Real.exp (2 * a) * (1 / σ) ^ 2
                    / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ 2)) ^ (1 - q)
              ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperTheta B x) m,
                      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
                    (harperBarrierTop B V x)
                    (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j))
                  (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                  ^ q ∂ν := by
  obtain ⟨B₁, a₀, α, hα, HN⟩ := exists_le_integral_restricted_normSq_harper_data
  exact ⟨a₀, α, hα, le_integral_rpow_harper_data_of_numerator hα HN⟩

/-! ### The exponent bookkeeping

Paley-Zygmund leaves `N^{2-q}/D^{1-q}`, and turning that into Harper's `(\log x)^q V^{-q} W^{-q}`
is arithmetic on four bases. -/

/-- **The shape factor, at the exponents Paley-Zygmund produces.**
`M^{2-q}W^{2(1-q)} ≥ W^{-q}` whenever `M ≥ 1/W`, because `-(2-q) + 2(1-q) = -q`.  This is where
`RMF.one_div_W_le_min_one_div_sqrt` is spent. -/
lemma rpow_neg_le_rpow_mul_rpow {M W q : ℝ} (hW : 0 < W) (hM : 1 / W ≤ M) (hq1 : q < 1) :
    W ^ (-q) ≤ M ^ (2 - q) * W ^ (2 * (1 - q)) := by
  have h2q : (0 : ℝ) < 2 - q := by linarith
  have hkey : (1 / W) ^ (2 - q) ≤ M ^ (2 - q) :=
    Real.rpow_le_rpow (by positivity) hM h2q.le
  have hdiv : (1 / W) ^ (2 - q) = W ^ (-(2 - q)) := by
    rw [Real.div_rpow (by norm_num) hW.le, Real.one_rpow, Real.rpow_neg hW.le, one_div]
  rw [hdiv] at hkey
  calc W ^ (-q) = W ^ (-(2 - q)) * W ^ (2 * (1 - q)) := by
        rw [← Real.rpow_add hW]
        congr 1
        ring
    _ ≤ M ^ (2 - q) * W ^ (2 * (1 - q)) :=
        mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hW.le _)

/-- **The `\log x` and `V` exponents**:
`(L/(Vc))^{2-q}\,(4V/L)^{2(1-q)} = L^q\,V^{-q}\,c^{-(2-q)}\,4^{2(1-q)}`.
The exponent of `L` is `(2-q) - 2(1-q) = q`; that of `V` is `-(2-q) + 2(1-q) = -q`, so **`V` costs
rather than helps**. -/
lemma rpow_log_V_identity {L V c q : ℝ} (hL : 0 < L) (hV : 0 < V) (hc : 0 < c) :
    (L / (V * c)) ^ (2 - q) * (4 * V / L) ^ (2 * (1 - q))
      = L ^ q * V ^ (-q) * c ^ (-(2 - q)) * 4 ^ (2 * (1 - q)) := by
  have hVc : (0 : ℝ) < V * c := by positivity
  have h4V : (0 : ℝ) < 4 * V := by positivity
  have hVs : (0 : ℝ) < V ^ (2 - q) := Real.rpow_pos_of_pos hV _
  have hcs : (0 : ℝ) < c ^ (2 - q) := Real.rpow_pos_of_pos hc _
  have hLt : (0 : ℝ) < L ^ (2 * (1 - q)) := Real.rpow_pos_of_pos hL _
  have hL2 : L ^ (2 - q) = L ^ q * L ^ (2 * (1 - q)) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hV2 : V ^ (2 * (1 - q)) = V ^ (-q) * V ^ (2 - q) := by
    rw [← Real.rpow_add hV]
    congr 1
    ring
  rw [Real.div_rpow hL.le hVc.le, Real.div_rpow h4V.le hL.le,
    Real.mul_rpow hV.le hc.le, Real.mul_rpow (by norm_num) hV.le,
    hL2, hV2, Real.rpow_neg hc.le]
  field_simp

/-- **The level's exponential, bounded in terms of `κ` alone.**  `a(1-q) ≤ 1 + κ\log 2` follows from
`a ≤ m + κ\log 2` and `m(1-q) ≤ 1`, so the denominator's `e^{2a}` costs `e^{2(1+κ\log 2)}` and no
more.  This is the second thing the slack `κ` has to pay for. -/
lemma exp_neg_le_exp_neg_two_mul {a m q κ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hκ : 0 ≤ κ)
    (hmq : m * (1 - q) ≤ 1) (ham : a ≤ m + κ * Real.log 2) :
    Real.exp (-(2 * (1 + κ * Real.log 2))) ≤ Real.exp (-(2 * (a * (1 - q)))) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hd0 : (0 : ℝ) ≤ 1 - q := by linarith
  have hd1 : (1 : ℝ) - q ≤ 1 := by linarith
  refine Real.exp_le_exp.2 ?_
  have hstep : a * (1 - q) ≤ 1 + κ * Real.log 2 := by
    nlinarith [hmq, ham, hd0, hd1, mul_nonneg hκ hlog2.le]
  linarith

/-- **A negative fractional power beats the reciprocal**: `y^{-(1-q)} ≥ \min\{1, 1/y\}`.  Above `1`
the exponent is milder than `-1`; below `1` a negative exponent only helps. -/
lemma min_one_div_le_rpow_neg {y q : ℝ} (hy : 0 < y) (hq0 : 0 < q) (hq1 : q < 1) :
    min 1 (1 / y) ≤ y ^ (-(1 - q)) := by
  rcases le_total 1 y with h | h
  · have h1 : y ^ (-1 : ℝ) ≤ y ^ (-(1 - q)) :=
      Real.rpow_le_rpow_of_exponent_le h (by linarith)
    have h2 : y ^ (-1 : ℝ) = y⁻¹ := by
      rw [Real.rpow_neg hy.le, Real.rpow_one]
    rw [h2] at h1
    refine le_trans (min_le_right _ _) ?_
    rwa [one_div]
  · have h1 : y ^ (0 : ℝ) ≤ y ^ (-(1 - q)) :=
      Real.rpow_le_rpow_of_exponent_ge hy h (by linarith)
    rw [Real.rpow_zero] at h1
    exact le_trans (min_le_left _ _) h1

/-- **A power in `[1,2]` beats the smaller of the two ends**: `z^{2-q} ≥ \min\{z, z^2\}`. -/
lemma min_le_rpow_two_sub {z q : ℝ} (hz : 0 < z) (hq0 : 0 < q) (hq1 : q < 1) :
    min z (z ^ (2 : ℝ)) ≤ z ^ (2 - q) := by
  rcases le_total 1 z with h | h
  · have h1 : z ^ (1 : ℝ) ≤ z ^ (2 - q) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    rw [Real.rpow_one] at h1
    exact le_trans (min_le_left _ _) h1
  · exact le_trans (min_le_right _ _)
      (Real.rpow_le_rpow_of_exponent_ge hz h (by linarith))

/-- **The numerator's `e^{n-63}` is `\log x/V` up to a factor depending only on `B`.**
`n ≥ Λ - B - \log V - 6` and `e^Λ = \log x`, so `e^{n-63} ≥ \log x/(Ve^{B+69})`.  **This is where
the numerator's `1/V` comes from** — the `⌊\log V⌋+3` blocks the drop gives up, seen through the
exponential. -/
lemma log_div_le_exp_barrierTop_sub {B : ℕ} {V x : ℝ} (hV : 1 ≤ V) (hx1 : 1 < x)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x) :
    Real.log x / (V * Real.exp ((B : ℝ) + 69))
      ≤ Real.exp (((harperBarrierTop B V x : ℕ) : ℝ) - 63) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hV0 : (0 : ℝ) < V := by linarith
  have hbge := barrierTop_ge_data hV hx hle
  have hkey : Real.exp (Real.log (Real.log x) - (((B : ℝ) + 69) + Real.log V))
      = Real.log x / (V * Real.exp ((B : ℝ) + 69)) := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_log hV0, Real.exp_log hlogx]
    ring
  rw [← hkey]
  exact Real.exp_le_exp.2 (by linarith)

/-- **The regrouping.**  Paley–Zygmund produces `N^{2-q}/D^{1-q}`; this sorts its factors into the
three groups the bounds above address — the factors in `Tv`, `α`, `C`, `E` and `ea`, the shape
factor `M^{2-q}W^{2(1-q)}`, and the `\log x`/`V` pair `E_1^{2-q}\,\Sigma^{-(1-q)}`. -/
lemma pz_regroup {Tv α M E₁ C E ea Sg W q : ℝ}
    (hTv : 0 < Tv) (hα : 0 < α) (hM : 0 < M) (hE₁ : 0 < E₁)
    (hC : 0 < C) (hE : 0 < E) (hea : 0 < ea) (hSg : 0 < Sg) (hW : 0 < W) :
    (Tv * (α * M) * E₁) ^ (2 - q) / (C * (E * ea * Sg / W ^ 2)) ^ (1 - q)
      = (Tv * α) ^ (2 - q) * (C * E) ^ (-(1 - q)) * ea ^ (-(1 - q))
          * (M ^ (2 - q) * W ^ (2 * (1 - q))) * (E₁ ^ (2 - q) * Sg ^ (-(1 - q))) := by
  have hW2 : (0 : ℝ) < W ^ 2 := by positivity
  have hden : (0 : ℝ) < E * ea * Sg / W ^ 2 := by positivity
  have hWr : (W ^ 2) ^ (1 - q) = W ^ (2 * (1 - q)) := by
    rw [← Real.rpow_natCast W 2, ← Real.rpow_mul hW.le]
    norm_num
  rw [show Tv * (α * M) * E₁ = (Tv * α) * M * E₁ by ring,
    Real.mul_rpow (by positivity) hE₁.le, Real.mul_rpow (by positivity) hM.le,
    Real.mul_rpow hC.le hden.le, Real.div_rpow (by positivity) hW2.le,
    Real.mul_rpow (by positivity) hSg.le, Real.mul_rpow hE.le hea.le,
    Real.mul_rpow hC.le hE.le, hWr,
    Real.rpow_neg (by positivity), Real.rpow_neg hea.le, Real.rpow_neg hSg.le]
  field_simp
  rw [← Real.rpow_add hE, show (1 : ℝ) - q + -(1 - q) = 0 by ring, Real.rpow_zero]

/-- `((L/(4V))^2)^{-(1-q)} = (4V/L)^{2(1-q)}` — the denominator's `σ^{-2}` seen as a positive
power of `σ`, which is the form `RMF.rpow_log_V_identity` consumes. -/
lemma sigma_sq_rpow_neg (L V q : ℝ) (hL : 0 < L) (hV : 0 < V) :
    ((L / (4 * V)) ^ 2) ^ (-(1 - q)) = (4 * V / L) ^ (2 * (1 - q)) := by
  have h4V : (0 : ℝ) < 4 * V := by positivity
  have hdiv : (0 : ℝ) < L / (4 * V) := by positivity
  rw [← Real.rpow_natCast (L / (4 * V)) 2, ← Real.rpow_mul hdiv.le,
    show ((2 : ℕ) : ℝ) * -(1 - q) = -(2 * (1 - q)) by push_cast; ring,
    Real.rpow_neg hdiv.le, Real.div_rpow hL.le h4V.le, Real.div_rpow h4V.le hL.le]
  rw [inv_div]

/-- **The shape, from the five bounds.**  The left side is `|T|`, `\log x`, `V` and `W` against
factors free of them; the exponents are `q`, `-q`, `-q`, which is Harper's. -/
lemma pz_shape_le {Tv α M E₁ C E a Sg W Lx V c₀ q κ m : ℝ}
    (hTv : 0 < Tv) (hα : 0 < α) (hM : 0 < M) (hE₁ : 0 < E₁)
    (hC : 0 < C) (hE : 0 < E) (hSg : 0 < Sg) (hW : 0 < W)
    (hLx : 0 < Lx) (hV : 0 < V) (hc₀ : 1 ≤ c₀)
    (hq0 : 0 < q) (hq1 : q < 1) (hκ : 0 ≤ κ)
    (hMW : 1 / W ≤ M) (hE₁ge : Lx / (V * c₀) ≤ E₁)
    (hSgeq : Sg = (Lx / (4 * V)) ^ 2)
    (hmq : m * (1 - q) ≤ 1) (ham : a ≤ m + κ * Real.log 2) :
    min (Tv * α) ((Tv * α) ^ (2 : ℝ)) * min 1 (1 / (C * E))
        * Real.exp (-(2 * (1 + κ * Real.log 2))) * W ^ (-q)
        * (c₀ ^ (-(2 : ℝ)) * Lx ^ q * V ^ (-q))
      ≤ (Tv * (α * M) * E₁) ^ (2 - q)
          / (C * (E * Real.exp (2 * a) * Sg / W ^ 2)) ^ (1 - q) := by
  have hCE : (0 : ℝ) < C * E := by positivity
  have hTα : (0 : ℝ) < Tv * α := by positivity
  -- the five component bounds
  have h1 : min (Tv * α) ((Tv * α) ^ (2 : ℝ)) ≤ (Tv * α) ^ (2 - q) :=
    min_le_rpow_two_sub hTα hq0 hq1
  have h2 : min 1 (1 / (C * E)) ≤ (C * E) ^ (-(1 - q)) := min_one_div_le_rpow_neg hCE hq0 hq1
  have h3 : Real.exp (-(2 * (1 + κ * Real.log 2))) ≤ Real.exp (2 * a) ^ (-(1 - q)) := by
    rw [← Real.exp_mul]
    refine le_trans (exp_neg_le_exp_neg_two_mul hq0.le hq1.le hκ hmq ham) ?_
    exact Real.exp_le_exp.2 (by ring_nf; linarith)
  have h4 : W ^ (-q) ≤ M ^ (2 - q) * W ^ (2 * (1 - q)) :=
    rpow_neg_le_rpow_mul_rpow hW hMW hq1
  have h5 : c₀ ^ (-(2 : ℝ)) * Lx ^ q * V ^ (-q) ≤ E₁ ^ (2 - q) * Sg ^ (-(1 - q)) := by
    have hVc : (0 : ℝ) < V * c₀ := by positivity
    have hE₁r : (Lx / (V * c₀)) ^ (2 - q) ≤ E₁ ^ (2 - q) :=
      Real.rpow_le_rpow (by positivity) hE₁ge (by linarith)
    have hSgr : Sg ^ (-(1 - q)) = (4 * V / Lx) ^ (2 * (1 - q)) := by
      rw [hSgeq]
      exact sigma_sq_rpow_neg Lx V q hLx hV
    have hc₀r : c₀ ^ (-(2 : ℝ)) ≤ c₀ ^ (-(2 - q)) :=
      Real.rpow_le_rpow_of_exponent_le hc₀ (by linarith)
    have h4r : (1 : ℝ) ≤ (4 : ℝ) ^ (2 * (1 - q)) := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
        (show (0 : ℝ) ≤ 2 * (1 - q) by linarith)
      rwa [Real.rpow_zero] at this
    have hc₀0 : (0 : ℝ) < c₀ := by linarith
    have hb : (0 : ℝ) ≤ Lx ^ q * V ^ (-q) := by positivity
    have hp : (0 : ℝ) ≤ Lx ^ q * V ^ (-q) * c₀ ^ (-(2 - q)) := by positivity
    rw [hSgr]
    calc c₀ ^ (-(2 : ℝ)) * Lx ^ q * V ^ (-q)
        = Lx ^ q * V ^ (-q) * c₀ ^ (-(2 : ℝ)) := by ring
      _ ≤ Lx ^ q * V ^ (-q) * c₀ ^ (-(2 - q)) := mul_le_mul_of_nonneg_left hc₀r hb
      _ ≤ Lx ^ q * V ^ (-q) * c₀ ^ (-(2 - q)) * (4 : ℝ) ^ (2 * (1 - q)) := by
          nlinarith [h4r, hp]
      _ = (Lx / (V * c₀)) ^ (2 - q) * (4 * V / Lx) ^ (2 * (1 - q)) :=
          (rpow_log_V_identity hLx hV (by linarith)).symm
      _ ≤ E₁ ^ (2 - q) * (4 * V / Lx) ^ (2 * (1 - q)) :=
          mul_le_mul_of_nonneg_right hE₁r (Real.rpow_nonneg (by positivity) _)
  -- and their product
  rw [pz_regroup hTv hα hM hE₁ hC hE (Real.exp_pos (2 * a)) hSg hW]
  gcongr

/-- **`RMF.exists_le_integral_rpow_harper_shape` with the level left free.**  The step from the
raw Paley–Zygmund quotient to the shape `(\log x)^qV^{-q}W^{-q}` raises the level to `max 1 a₀` —
the only point in the chain where the level is touched at all — and then fixes Harper's shape
parameter `m = \min\{\sqrt Λ, 1/(1-q)\}` together with the slack `a ≤ m + κ\log 2`.

With `a₀` free, a bound `a₀ ≤ N` gives `\max(1, a₀) ≤ \max(1, N)`, and one step further up that
bound becomes the admissible `κ` and so the factor `e^{-2(1+κ\log 2)}` of the constant. -/
theorem le_integral_rpow_harper_shape_of_data.{u} {a₀ α : ℝ} (hα : 0 < α)
    (hcomp :
      ∀ κ : ℝ, 0 ≤ κ → ∃ B₀ : ℕ,
      ∀ B : ℕ, B₀ ≤ B →
      ∀ (Ω' : Type u) [MeasurableSpace Ω'], ∃ E : ℝ, 0 < E ∧
        ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ x₀ : ℝ,
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
        ∀ (σ a q m x : ℝ) (T : Set ℝ),
          x₀ ≤ x → 1 < x → 3 ≤ x → Λ₀ ≤ Real.log (Real.log x) →
          (B : ℝ) + 2 ≤ Real.log (Real.log x) →
          6 * (B : ℝ) + 3 * Real.log V + 40 ≤ Real.log (Real.log x) →
          4 * V * (4 * Real.exp (2 * (B : ℝ) + 6) + 7) ≤ Real.log x →
          0 < σ → σ ≤ 1 / 2 → σ * Real.log x = 4 * V →
          MeasurableSet T → T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → volume T ≠ ⊤ →
          0 < (volume T).toReal →
          a₀ ≤ a → 1 ≤ a → 0 ≤ m → m ≤ Real.sqrt (Real.log (Real.log x)) →
          m * (1 - q) ≤ 1 → a ≤ m + κ * Real.log 2 →
          0 < q → q < 1 → 1 ≤ q * Real.sqrt (Real.log (Real.log x)) →
            ((volume T).toReal
                  * (α * min 1 (a / Real.sqrt (((harperBarrierTop B V x : ℕ) : ℝ))))
                  * Real.exp (((harperBarrierTop B V x : ℕ) : ℝ) - 63)) ^ (2 - q)
                / ((6 + 2 / Real.log 2) * (E * Real.exp (2 * a) * (1 / σ) ^ 2
                    / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ 2)) ^ (1 - q)
              ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperTheta B x) m,
                      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
                    (harperBarrierTop B V x)
                    (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j))
                  (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                  ^ q ∂ν) :
    ∀ κ : ℝ, (max 1 a₀) ≤ κ * Real.log 2 → ∃ B₀ : ℕ,
    ∀ B : ℕ, B₀ ≤ B →
    ∀ (Ω' : Type u) [MeasurableSpace Ω'], ∃ E : ℝ, 0 < E ∧
      ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ x₀ : ℝ,
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
      ∀ (σ q x : ℝ) (T : Set ℝ),
        x₀ ≤ x → 1 < x → 3 ≤ x → Λ₀ ≤ Real.log (Real.log x) →
        (B : ℝ) + 2 ≤ Real.log (Real.log x) →
        6 * (B : ℝ) + 3 * Real.log V + 40 ≤ Real.log (Real.log x) →
        4 * V * (4 * Real.exp (2 * (B : ℝ) + 6) + 7) ≤ Real.log x →
        0 < σ → σ ≤ 1 / 2 → σ * Real.log x = 4 * V →
        MeasurableSet T → T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → volume T ≠ ⊤ →
        0 < (volume T).toReal →
        0 < q → q < 1 → 1 ≤ q * Real.sqrt (Real.log (Real.log x)) →
          min ((volume T).toReal * α) (((volume T).toReal * α) ^ (2 : ℝ))
              * min 1 (1 / ((6 + 2 / Real.log 2) * E))
              * Real.exp (-(2 * (1 + κ * Real.log 2)))
              * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
              * (Real.exp ((B : ℝ) + 69) ^ (-(2 : ℝ)) * Real.log x ^ q * V ^ (-q))
            ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                  (fun mm ω => ∑ p ∈ primeBlockSub (harperTheta B x) mm,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
                  (harperBarrierTop B V x)
                  (fun j => -harperLevel (max 1 a₀) ((harperBarrierTop B V x : ℕ) : ℝ) q
                    - blockSlope 125 * j)
                  (fun j => harperLevel (max 1 a₀) ((harperBarrierTop B V x : ℕ) : ℝ) q + j
                    + harperHf j))
                (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                ^ q ∂ν := by
  intro κ hκa
  have hlog2' : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hκ : 0 ≤ κ := by
    by_contra hcon
    have hneg : κ < 0 := not_le.mp hcon
    nlinarith [le_max_left (1 : ℝ) a₀, hκa]
  obtain ⟨B₀, hcomp⟩ := hcomp κ hκ
  refine ⟨B₀, ?_⟩
  intro B hB Ω' _
  obtain ⟨E, hE, hcomp⟩ := hcomp B hB Ω'
  refine ⟨E, hE, ?_⟩
  intro V hV
  obtain ⟨Λ₀, x₀, hcomp⟩ := hcomp V hV
  refine ⟨Λ₀, x₀, ?_⟩
  intro Y ν hY σ q x T hx hx1 hx3 hΛ₀ hxΛ hΛcnt hfarwin hσ0 hσhalf hσeq hTm hTsub hTfin
    hT0
    hq0 hq1 hqΛ
  have hlog2 : (0 : ℝ) < Real.log 2 := hlog2'
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hσ4 : σ * Real.log x ≤ 4 * V := le_of_eq hσeq
  have hΛ6 : (B : ℝ) + Real.log V + 6 ≤ Real.log (Real.log x) := by linarith
  have hle := floor_log_add_three_le_harperN hV hxΛ hΛ6
  have hbge := barrierTop_ge_data hV hxΛ hle
  have hn0 : (0 : ℝ) < ((harperBarrierTop B V x : ℕ) : ℝ) := by linarith
  -- the block count is at most `Λ`
  have hnΛ : ((harperBarrierTop B V x : ℕ) : ℝ) ≤ Real.log (Real.log x) := by
    have h1 : ((harperBarrierTop B V x : ℕ) : ℝ) ≤ ((harperN B x : ℕ) : ℝ) := by
      exact_mod_cast harperBarrierTop_le B V x
    have h2 : ((harperN B x : ℕ) : ℝ) ≤ ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) := by
      have : harperN B x ≤ ⌊Real.log (Real.log x)⌋₊ := by
        rw [harperN]; omega
      exact_mod_cast this
    linarith [Nat.floor_le hΛ0, h1, h2]
  -- the level and the shape parameter
  set a : ℝ := harperLevel (max 1 a₀) ((harperBarrierTop B V x : ℕ) : ℝ) q with hadef
  set m : ℝ := min (Real.sqrt (Real.log (Real.log x))) (1 / (1 - q)) with hmdef
  have hd0 : (0 : ℝ) < 1 - q := by linarith
  have hm0 : (0 : ℝ) ≤ m := le_min (Real.sqrt_nonneg _) (by positivity)
  have hmΛ : m ≤ Real.sqrt (Real.log (Real.log x)) := min_le_left _ _
  have hmq : m * (1 - q) ≤ 1 := by
    have h1 : m ≤ 1 / (1 - q) := min_le_right _ _
    rw [le_div_iff₀ hd0] at h1
    linarith
  have ha₀ : max 1 a₀ ≤ a := le_harperLevel _ _ _
  have hκa' : max 1 a₀ ≤ κ * Real.log 2 := hκa
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_left _ _) ha₀
  have ham : a ≤ m + κ * Real.log 2 := by
    rw [hadef, harperLevel]
    refine max_le (le_trans hκa' (by linarith)) ?_
    refine le_trans ?_ (by linarith [mul_nonneg hκ hlog2.le] : m ≤ m + κ * Real.log 2)
    exact min_le_min (Real.sqrt_le_sqrt hnΛ) le_rfl
  -- the composition, at this level
  have hcomp' := hcomp Y ν hY σ a q m x T hx hx1 hx3 hΛ₀ hxΛ hΛcnt hfarwin hσ0 hσhalf hσeq
    hTm hTsub
    hTfin hT0 (le_trans (le_max_right 1 a₀) ha₀) ha1 hm0 hmΛ hmq ham hq0 hq1 hqΛ
  refine le_trans ?_ hcomp'
  -- and the shape
  have hMW : 1 / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x)))
      ≤ min 1 (a / Real.sqrt (((harperBarrierTop B V x : ℕ) : ℝ))) :=
    one_div_W_le_min_one_div_sqrt hn0 hnΛ hq1
  have hE₁ge : Real.log x / (V * Real.exp ((B : ℝ) + 69))
      ≤ Real.exp (((harperBarrierTop B V x : ℕ) : ℝ) - 63) :=
    log_div_le_exp_barrierTop_sub hV hx1 hxΛ hle
  have hSgeq : (1 / σ) ^ 2 = (Real.log x / (4 * V)) ^ 2 := by
    have : 1 / σ = Real.log x / (4 * V) := by
      rw [eq_div_iff (by linarith), ← hσeq]
      field_simp
    rw [this]
  have hWpos : (0 : ℝ) < 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) := by
    nlinarith [Real.sqrt_nonneg (Real.log (Real.log x))]
  have hminpos : (0 : ℝ) < min 1 (a / Real.sqrt (((harperBarrierTop B V x : ℕ) : ℝ))) :=
    lt_min one_pos (by positivity)
  have hclog : (1 : ℝ) ≤ Real.exp ((B : ℝ) + 69) := by
    have := Real.add_one_le_exp ((B : ℝ) + 69)
    linarith
  exact pz_shape_le hT0 hα hminpos (Real.exp_pos _) (by positivity) hE (by positivity) hWpos
    hlogx (by linarith) hclog hq0 hq1 hκ hMW hE₁ge hSgeq hmq ham

/-- **The lower bound on `\int X^q`, in Harper's shape**:
`\int X^q \gg c\cdot(\log x)^q\,V^{-q}\,W^{-q}`, `W = 1 + (1-q)\sqrt{\log\log x}`, where `c` depends
on `|T|`, `κ`, `B` and the space `Ω'` (through `E`) but not on `V`, `x`, `q`, `Y` or `ν`.

The level is `RMF.harperLevel a₀ n q` and the shape parameter is Harper's own
`m = \min\{\sqrt Λ, 1/(1-q)\}`.  **They are different, and that is the point**: `a` clears
Probability Lemma 1's threshold `a₀ ≥ 8000` while `m` satisfies `m(1-q) ≤ 1`, and the slack
condition `a₀ ≤ κ\log 2` lets both hold at once.  `a₀` is bound before `κ`, so a caller reads off
`a₀` and then chooses the slack; `κ` reaches `B₀` through the denominator's `K = K₀ + 2κ`.
`harperLevel`'s `\sqrt n` rather than `\sqrt Λ` is harmless because `n ≤ Λ`. -/
theorem exists_le_integral_rpow_harper_shape :
    ∃ (a₀ α : ℝ), 0 < α ∧ 1 ≤ a₀ ∧
      ∀ κ : ℝ, a₀ ≤ κ * Real.log 2 → ∃ B₀ : ℕ,
      ∀ B : ℕ, B₀ ≤ B →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'], ∃ E : ℝ, 0 < E ∧
        ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ x₀ : ℝ,
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
        ∀ (σ q x : ℝ) (T : Set ℝ),
          x₀ ≤ x → 1 < x → 3 ≤ x → Λ₀ ≤ Real.log (Real.log x) →
          (B : ℝ) + 2 ≤ Real.log (Real.log x) →
          6 * (B : ℝ) + 3 * Real.log V + 40 ≤ Real.log (Real.log x) →
          4 * V * (4 * Real.exp (2 * (B : ℝ) + 6) + 7) ≤ Real.log x →
          0 < σ → σ ≤ 1 / 2 → σ * Real.log x = 4 * V →
          MeasurableSet T → T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → volume T ≠ ⊤ →
          0 < (volume T).toReal →
          0 < q → q < 1 → 1 ≤ q * Real.sqrt (Real.log (Real.log x)) →
            min ((volume T).toReal * α) (((volume T).toReal * α) ^ (2 : ℝ))
                * min 1 (1 / ((6 + 2 / Real.log 2) * E))
                * Real.exp (-(2 * (1 + κ * Real.log 2)))
                * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
                * (Real.exp ((B : ℝ) + 69) ^ (-(2 : ℝ)) * Real.log x ^ q * V ^ (-q))
              ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                    (fun mm ω => ∑ p ∈ primeBlockSub (harperTheta B x) mm,
                      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
                    (harperBarrierTop B V x)
                    (fun j => -harperLevel a₀ ((harperBarrierTop B V x : ℕ) : ℝ) q
                      - blockSlope 125 * j)
                    (fun j => harperLevel a₀ ((harperBarrierTop B V x : ℕ) : ℝ) q + j
                      + harperHf j))
                  (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                  ^ q ∂ν := by
  obtain ⟨a₀, α, hα, hcomp⟩ := exists_le_integral_rpow_harper_data
  exact ⟨max 1 a₀, α, hα, le_max_left _ _,
    le_integral_rpow_harper_shape_of_data hα hcomp⟩

end RMF
