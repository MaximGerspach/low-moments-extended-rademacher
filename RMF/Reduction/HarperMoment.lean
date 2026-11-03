/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.PaleyZygmund
import RMF.Reduction.LowerAssembly

/-!
# The shape, through the reduction

`RMF.exists_le_integral_rpow_harper_shape` bounds

`∫_Ω (∫_T 1_barrier ‖F(½+σ+it)‖² dt)^q dν`

from below, and `RMF.reduction_lower_chaosShift_absorbed` wants a lower bound on

`∫_Ω chaosShift f x σ ω ^ q dν`.

These differ by three things, and none of them costs anything:

1. **The cutoff is the same.**  `RMF.blockCutoff_harperN` says
   `blockCutoff (harperTheta B x) (harperN B x) = ⌊x⌋₊ + 1`, because Harper's grid is built so
   that the block above the top is `x` itself.  This is the reason the two chains meet at all.
2. **The barrier only shrinks the integral.**  `1_barrier ≤ 1`, so dropping it is free — the
   inequality points the right way.
3. **The window is the whole of `[-½,½]`.**  `T` is a free parameter of the shape, so take
   `T = (-½,½]`, which is `RMF.chaosShift`'s own window; then `|T| = 1` and the two
   integrals are literally the same integral.

The remaining difference is the factor `(\log x)^{-1}` in `RMF.chaosShift`'s definition, and
**that is the whole point**: the shape carries `(\log x)^q`, the reduction divides by
`(\log x)^q`, and they cancel exactly.  What comes out the far side depends on `x` only through
`W = 1 + (1-q)\sqrt{\log\log x}`.
-/

open MeasureTheory

namespace RMF

/-! ### Dropping the barrier -/

/-- **The barrier-restricted window integral is at most the full one.**

The integrability of the restricted integrand is not needed: if it fails, Bochner's integral is
`0`, and the majorant is nonnegative, so the inequality holds anyway.  That case split is what
lets this lemma avoid the joint measurability of the barrier event in `(ω,t)`. -/
lemma setIntegral_indicator_le_window {Ω' : Type*}
    {Y : ℕ → Ω' → ℂ} {N : ℕ} {σ : ℝ} {ω : Ω'} (hσ : 0 ≤ σ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖Y p ω‖ ≤ 1) (S : ℝ → Set Ω') :
    ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ), Set.indicator (S t)
        (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) N
          (shiftLine σ t) ω‖ ^ 2) ω
      ≤ ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ), lineSq (1 / 2 + σ) Y N ω t := by
  have hwin : IntegrableOn (fun t : ℝ => lineSq (1 / 2 + σ) Y N ω t)
      (Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ)) :=
    integrableOn_window (1 / 2 + σ) (by linarith) hω _ _
  by_cases hint : IntegrableOn (fun t : ℝ => Set.indicator (S t)
      (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) N
        (shiftLine σ t) ω‖ ^ 2) ω) (Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ))
  · refine setIntegral_mono_on hint hwin measurableSet_Ioc fun t _ => ?_
    exact Set.indicator_le_self' (fun _ _ => pow_nonneg (norm_nonneg _) 2) ω
  · rw [integral_undef hint]
    exact setIntegral_nonneg measurableSet_Ioc fun t _ =>
      pow_nonneg (norm_nonneg _) 2

/-! ### The shape, with `(\log x)^q` cancelled -/

/-- **`RMF.exists_le_integral_rpow_chaosShift` with the level left free.**  The last step of the
reduction's lower half does not move the level: it reads
`RMF.exists_le_integral_rpow_harper_shape` at `T = (-1/2, 1/2]`, whose volume is `1`, and spends
the shape's `(\log x)^q` against `RMF.chaosShift`'s `(\log x)^{-1}`.  The level reaches the
constant only through the slack condition `a₀ ≤ κ\log 2` and the factor `e^{-2(1+κ\log 2)}`, so
`a₀ ≤ N` licenses `κ = N/\log 2` and a constant `e^{-2(1+N)}`. -/
theorem le_integral_rpow_chaosShift_of_shape.{u} {a₀ α : ℝ}
    (hshape :
      ∀ κ : ℝ, a₀ ≤ κ * Real.log 2 → ∃ B₀ : ℕ,
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
                    (fun j => -harperLevel a₀ ((harperBarrierTop B V x : ℕ) : ℝ) q
                      - blockSlope 125 * j)
                    (fun j => harperLevel a₀ ((harperBarrierTop B V x : ℕ) : ℝ) q + j
                      + harperHf j))
                  (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                  ^ q ∂ν) :
    ∀ κ : ℝ, a₀ ≤ κ * Real.log 2 → ∃ B₀ : ℕ,
    ∀ B : ℕ, B₀ ≤ B →
    ∀ (Ω' : Type u) [MeasurableSpace Ω'], ∃ E : ℝ, 0 < E ∧
      ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ x₀ : ℝ,
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
      ∀ (σ q x : ℝ),
        x₀ ≤ x → 1 < x → 3 ≤ x → Λ₀ ≤ Real.log (Real.log x) →
        (B : ℝ) + 2 ≤ Real.log (Real.log x) →
        6 * (B : ℝ) + 3 * Real.log V + 40 ≤ Real.log (Real.log x) →
        4 * V * (4 * Real.exp (2 * (B : ℝ) + 6) + 7) ≤ Real.log x →
        0 < σ → σ ≤ 1 / 2 → σ * Real.log x = 4 * V →
        0 < q → q < 1 → 1 ≤ q * Real.sqrt (Real.log (Real.log x)) →
          min α (α ^ (2 : ℝ)) * min 1 (1 / ((6 + 2 / Real.log 2) * E))
              * Real.exp (-(2 * (1 + κ * Real.log 2)))
              * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
              * (Real.exp ((B : ℝ) + 69) ^ (-(2 : ℝ)) * V ^ (-q))
            ≤ ∫ ω, chaosShift (fun ω => compMultExtension fun p => Y p ω) x σ ω ^ q
                ∂ν := by
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
  -- Harper's window is `chaosShift`'s own, so `|T| = 1`
  have hTvol : (volume (Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ))).toReal = 1 := by
    rw [Real.volume_Ioc]
    norm_num
  have hTsub : Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ) ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hmain := hshape Y ν hY σ q x (Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ)) hx hx1 hx3 hΛ₀
    hxΛ hΛcnt
    hfarwin hσ0 hσhalf hσeq measurableSet_Ioc hTsub
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by rw [hTvol]; norm_num)
    hq0 hq1 hqΛ
  rw [hTvol, one_mul] at hmain
  -- the cutoff is `⌊x⌋₊ + 1`, so the inner integral is the Euler-shift window
  have hcut : blockCutoff (harperTheta B x) (harperN B x) = ⌊x⌋₊ + 1 :=
    blockCutoff_harperN hx1 hxΛ
  rw [hcut] at hmain
  -- pass to the majorant, `ω` by `ω`
  set F : Ω' → ℝ := fun ω => (∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ),
      Set.indicator (barrierEvent
        (fun mm ω => ∑ p ∈ primeBlockSub (harperTheta B x) mm,
          localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
        (harperBarrierTop B V x)
        (fun j => -harperLevel a₀ ((harperBarrierTop B V x : ℕ) : ℝ) q - blockSlope 125 * j)
        (fun j => harperLevel a₀ ((harperBarrierTop B V x : ℕ) : ℝ) q + j + harperHf j))
      (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
        (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω) ^ q with hFdef
  set G : Ω' → ℝ := fun ω => Real.log x ^ q
      * chaosShift (fun ω => compMultExtension fun p => Y p ω) x σ ω ^ q with hGdef
  have hGint : Integrable G ν := by
    rw [hGdef]
    exact (integrable_chaosShift_rpow hY (by positivity) hσ0.le hq0.le).const_mul _
  have hae := ae_forall_norm_le_one hY norm_le_one_steinhausLaw (⌊x⌋₊ + 1)
  have hFG : F ≤ᵐ[ν] G := by
    filter_upwards [hae] with ω hω
    have hstep : (∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ), Set.indicator (barrierEvent
        (fun mm ω => ∑ p ∈ primeBlockSub (harperTheta B x) mm,
          localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
        (harperBarrierTop B V x)
        (fun j => -harperLevel a₀ ((harperBarrierTop B V x : ℕ) : ℝ) q - blockSlope 125 * j)
        (fun j => harperLevel a₀ ((harperBarrierTop B V x : ℕ) : ℝ) q + j + harperHf j))
      (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
        (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω)
        ≤ Real.log x
            * chaosShift (fun ω => compMultExtension fun p => Y p ω) x σ ω := by
      rw [chaosShift_eq, ← mul_assoc, mul_inv_cancel₀ hlogx.ne', one_mul]
      exact setIntegral_indicator_le_window hσ0.le hω _
    have hnn : (0 : ℝ) ≤ ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ), Set.indicator (barrierEvent
        (fun mm ω => ∑ p ∈ primeBlockSub (harperTheta B x) mm,
          localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
        (harperBarrierTop B V x)
        (fun j => -harperLevel a₀ ((harperBarrierTop B V x : ℕ) : ℝ) q - blockSlope 125 * j)
        (fun j => harperLevel a₀ ((harperBarrierTop B V x : ℕ) : ℝ) q + j + harperHf j))
      (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
        (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω :=
      setIntegral_nonneg measurableSet_Ioc fun t _ =>
        Set.indicator_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2) ω
    have := Real.rpow_le_rpow hnn hstep hq0.le
    rwa [Real.mul_rpow hlogx.le (chaosShift_nonneg (by positivity) ω)] at this
  have hFnn : 0 ≤ᵐ[ν] F := by
    filter_upwards with ω
    simp only [hFdef]
    exact Real.rpow_nonneg (setIntegral_nonneg measurableSet_Ioc fun t _ =>
      Set.indicator_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2) ω) q
  have hmono : ∫ ω, F ω ∂ν ≤ ∫ ω, G ω ∂ν := integral_mono_of_nonneg hFnn hGint hFG
  rw [hGdef, integral_const_mul] at hmono
  -- and cancel the `(\log x)^q` the reduction supplies
  refine le_of_mul_le_mul_left ?_ hlogq
  calc Real.log x ^ q * (min α (α ^ (2 : ℝ)) * min 1 (1 / ((6 + 2 / Real.log 2) * E))
          * Real.exp (-(2 * (1 + κ * Real.log 2)))
          * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
          * (Real.exp ((B : ℝ) + 69) ^ (-(2 : ℝ)) * V ^ (-q)))
      = min α (α ^ (2 : ℝ)) * min 1 (1 / ((6 + 2 / Real.log 2) * E))
          * Real.exp (-(2 * (1 + κ * Real.log 2)))
          * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
          * (Real.exp ((B : ℝ) + 69) ^ (-(2 : ℝ)) * Real.log x ^ q * V ^ (-q)) := by ring
    _ ≤ ∫ ω, F ω ∂ν := hmain
    _ ≤ Real.log x ^ q
          * ∫ ω, chaosShift (fun ω => compMultExtension fun p => Y p ω) x σ ω ^ q ∂ν :=
        hmono

/-- **The lower bound on the chaos moment, as the reduction wants it**:
`\int_Ω \big(\tfrac{1}{\log x}\int_{-1/2}^{1/2}\|F(\tfrac12+σ+it)\|^2\,dt\big)^q`
`\gg V^{-q}\,W^{-q}`, `W = 1 + (1-q)\sqrt{\log\log x}`, the implied factor depending on `κ`, `B` and
the space `Ω'` but not on `V`, `x`, `σ`, `q`, `Y` or `ν`.  The shape's `(\log x)^q` is spent against
`RMF.chaosShift`'s `(\log x)^{-1}`; this is the form `RMF.reduction_lower_chaosShift_absorbed`
consumes. -/
theorem exists_le_integral_rpow_chaosShift :
    ∃ (a₀ α : ℝ), 0 < α ∧ 1 ≤ a₀ ∧
      ∀ κ : ℝ, a₀ ≤ κ * Real.log 2 → ∃ B₀ : ℕ,
      ∀ B : ℕ, B₀ ≤ B →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'], ∃ E : ℝ, 0 < E ∧
        ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ x₀ : ℝ,
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
        ∀ (σ q x : ℝ),
          x₀ ≤ x → 1 < x → 3 ≤ x → Λ₀ ≤ Real.log (Real.log x) →
          (B : ℝ) + 2 ≤ Real.log (Real.log x) →
          6 * (B : ℝ) + 3 * Real.log V + 40 ≤ Real.log (Real.log x) →
          4 * V * (4 * Real.exp (2 * (B : ℝ) + 6) + 7) ≤ Real.log x →
          0 < σ → σ ≤ 1 / 2 → σ * Real.log x = 4 * V →
          0 < q → q < 1 → 1 ≤ q * Real.sqrt (Real.log (Real.log x)) →
            min α (α ^ (2 : ℝ)) * min 1 (1 / ((6 + 2 / Real.log 2) * E))
                * Real.exp (-(2 * (1 + κ * Real.log 2)))
                * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
                * (Real.exp ((B : ℝ) + 69) ^ (-(2 : ℝ)) * V ^ (-q))
              ≤ ∫ ω, chaosShift (fun ω => compMultExtension fun p => Y p ω) x σ ω ^ q
                  ∂ν := by
  obtain ⟨a₀, α, hα, ha₀, hshape⟩ := exists_le_integral_rpow_harper_shape
  exact ⟨a₀, α, hα, ha₀, le_integral_rpow_chaosShift_of_shape hshape⟩

/-! ### Beating the collar

`RMF.reduction_lower_chaosShift_absorbed` does not hand over the Euler-product moment: it hands over
that moment *minus* `C₀e^{-V}W^{-1/2}`, and the bound is vacuous until the moment beats the
collar.  It does, and cheaply, because `V` is ours to choose: the moment decays like `V^{-1/2}`
and the collar like `e^{-V}`.  Every constant below is fixed before `V`, so choosing `V` in terms
of them is not circular. -/

/-- **A power with a bounded exponent is bounded below by the smaller endpoint.**  Used twice,
for `A₀^{1/(2q)}` and for `c₂^{2q}` on `q ∈ [2/3, 1)`. -/
lemma min_rpow_le_rpow {z t t₁ t₂ : ℝ} (hz : 0 < z) (h1 : t₁ ≤ t) (h2 : t ≤ t₂) :
    min (z ^ t₁) (z ^ t₂) ≤ z ^ t := by
  rcases le_total 1 z with h | h
  · exact le_trans (min_le_left _ _) (Real.rpow_le_rpow_of_exponent_le h h1)
  · exact le_trans (min_le_right _ _) (Real.rpow_le_rpow_of_exponent_ge hz h h2)

/-- **`e^V` beats `√V` by any constant, once `V` is past it.**  `e^V ≥ (1+V/2)^2 ≥ V^2/4`, and for
`V ≥ 1` we have `√V ≤ V`, so `V ≥ 8K` already gives `K√V ≤ e^V/2`. -/
lemma mul_sqrt_le_exp {K V : ℝ} (hK : 0 ≤ K) (hV1 : 1 ≤ V) (hVK : 8 * K ≤ V) :
    2 * (K * Real.sqrt V) ≤ Real.exp V := by
  have hV0 : (0 : ℝ) < V := by linarith
  have hsq : Real.sqrt V ≤ V := by
    have h := Real.sqrt_le_sqrt (show V ≤ V ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h
  have hexp : V ^ 2 / 4 ≤ Real.exp V := by
    have h1 : 1 + V / 2 ≤ Real.exp (V / 2) := by
      have := Real.add_one_le_exp (V / 2)
      linarith
    have h2 : (1 + V / 2) ^ 2 ≤ Real.exp (V / 2) ^ 2 := by
      have hpos : (0 : ℝ) ≤ 1 + V / 2 := by linarith
      exact pow_le_pow_left₀ hpos h1 2
    have h3 : Real.exp (V / 2) ^ 2 = Real.exp V := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    nlinarith [h2, h3]
  nlinarith [hsq, hexp, hK]

/-! ### The constant, as a formula in the walls

`RMF.exists_le_integral_rpow_normalisedSum` below fixes its `c` from four inputs: the absolute
factor `A₀` that the chaos shape carries, and the reduction's `cr`, `C₀`, `V₀`.  Naming that
choice makes the dependence usable: a sharper wall gives a sharper `c` by instantiating
`RMF.le_integral_rpow_normalisedSum_of_shape`.

Nothing here is evaluated: `A₀` is the output of an existential, and no claim is made about its
size.  The same formula serves the Rademacher chain, which differs only inside `A₀` and in the
`\log\log x` count threshold `ct`. -/

/-- **The moment scale** `a₁ = \min(A₀^{1/2}, A₀^{3/4})`: a lower bound for `A₀^{1/(2q)}`,
uniform over `q ∈ [2/3, 1)`. -/
noncomputable def harperMomentScale (A₀ : ℝ) : ℝ :=
  min (A₀ ^ ((1 : ℝ) / 2)) (A₀ ^ ((3 : ℝ) / 4))

/-- **The tilt scale** `V`, large enough that the moment `a₁V^{-1/2}` beats the collar
`C₀e^{-V}`.  Every constant it mentions is fixed before `V`, so this is not circular. -/
noncomputable def harperMomentTilt (A₀ C₀ V₀ : ℝ) : ℝ :=
  max (max V₀ 1) (8 * (C₀ / harperMomentScale A₀))

/-- **The constant at the `2q`-th root**, `c₂ = c_r\,a₁/(2\sqrt V)`. -/
noncomputable def harperMomentRoot (A₀ cr C₀ V₀ : ℝ) : ℝ :=
  cr * (harperMomentScale A₀ / (2 * Real.sqrt (harperMomentTilt A₀ C₀ V₀)))

/-- **Harper's lower constant as a formula in the walls**, `c = \min(c₂^{4/3}, c₂^{2})`: the
value of `c₂^{2q}` at its worst `q ∈ [2/3, 1)`. -/
noncomputable def harperMomentConst (A₀ cr C₀ V₀ : ℝ) : ℝ :=
  min (harperMomentRoot A₀ cr C₀ V₀ ^ ((4 : ℝ) / 3))
    (harperMomentRoot A₀ cr C₀ V₀ ^ (2 : ℝ))

lemma harperMomentScale_pos {A₀ : ℝ} (hA₀ : 0 < A₀) : 0 < harperMomentScale A₀ :=
  lt_min (Real.rpow_pos_of_pos hA₀ _) (Real.rpow_pos_of_pos hA₀ _)

lemma one_le_harperMomentTilt (A₀ C₀ V₀ : ℝ) : 1 ≤ harperMomentTilt A₀ C₀ V₀ :=
  le_trans (le_max_right _ _) (le_max_left _ _)

lemma le_harperMomentTilt (A₀ C₀ V₀ : ℝ) : V₀ ≤ harperMomentTilt A₀ C₀ V₀ :=
  le_trans (le_max_left _ _) (le_max_left _ _)

lemma harperMomentRoot_pos {A₀ cr C₀ V₀ : ℝ} (hA₀ : 0 < A₀) (hcr : 0 < cr) :
    0 < harperMomentRoot A₀ cr C₀ V₀ := by
  have hV : (0 : ℝ) < harperMomentTilt A₀ C₀ V₀ :=
    lt_of_lt_of_le one_pos (one_le_harperMomentTilt A₀ C₀ V₀)
  have hsV : (0 : ℝ) < Real.sqrt (harperMomentTilt A₀ C₀ V₀) := Real.sqrt_pos.2 hV
  exact mul_pos hcr (div_pos (harperMomentScale_pos hA₀) (by linarith))

lemma harperMomentConst_pos {A₀ cr C₀ V₀ : ℝ} (hA₀ : 0 < A₀) (hcr : 0 < cr) :
    0 < harperMomentConst A₀ cr C₀ V₀ :=
  lt_min (Real.rpow_pos_of_pos (harperMomentRoot_pos hA₀ hcr) _)
    (Real.rpow_pos_of_pos (harperMomentRoot_pos hA₀ hcr) _)

set_option maxHeartbeats 1000000 in
-- the goal carries the two integrals literally, as in the existential form below
/-- **Harper's lower bound, with the constant a formula in the walls.**

The chaos shape supplies `A₀` and the reduction supplies `cr`, `C₀`, `V₀`; this lemma is the
choice of `V` and the exponent bookkeeping that turn them into

`\displaystyle \int \|S_x\|^{2q} \ \ge\ \mathrm{harperMomentConst}\,
  \big(1+(1-q)\sqrt{\log\log x}\big)^{-q}`

on `q ∈ [2/3, 1)`.  The law enters only through the predicate `P`, and the two bounds `HL`, `HR`
are exactly what `RMF.exists_le_integral_rpow_chaosShift` and
`RMF.reduction_lower_chaosShift_absorbed` produce.
`RMF.exists_le_integral_rpow_normalisedSum` is this with the walls existentially quantified. -/
theorem le_integral_rpow_normalisedSum_of_shape {Ω : Type*} [MeasurableSpace Ω]
    (P : (Ω → ArithmeticFunction ℂ) → Measure Ω → Prop) {A₀ cr C₀ V₀ ct : ℝ} {B₀ : ℕ}
    (hA₀ : 0 < A₀) (hcr : 0 < cr) (hC₀ : 0 ≤ C₀)
    (HL : ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ x₁ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ →
        ∀ x q : ℝ, x₁ ≤ x → 1 < x → 3 ≤ x →
          Λ₀ ≤ Real.log (Real.log x) → (B₀ : ℝ) + 2 ≤ Real.log (Real.log x) →
          6 * (B₀ : ℝ) + 3 * Real.log V + ct ≤ Real.log (Real.log x) →
          4 * V * (4 * Real.exp (2 * (B₀ : ℝ) + 6) + 7) ≤ Real.log x →
          8 * V ≤ Real.log x → 0 < q → q < 1 →
          1 ≤ q * Real.sqrt (Real.log (Real.log x)) →
            A₀ * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) * V ^ (-q)
              ≤ ∫ ω, chaosShift f x (4 * V / Real.log x) ω ^ q ∂μ)
    (HR : ∀ V : ℝ, V₀ ≤ V → ∃ x₂ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ →
        ∀ x q : ℝ, x₂ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
          cr * ((∫ ω, chaosShift f x (4 * V / Real.log x) ω ^ q ∂μ) ^ (1 / (2 * q))
                - C₀ / Real.exp V
                    * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ))
            ≤ (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) ^ (1 / (2 * q))) :
    ∃ x₀ : ℝ, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ →
      ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q < 1 →
        harperMomentConst A₀ cr C₀ V₀
            * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
          ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ := by
  set a₁ : ℝ := harperMomentScale A₀ with ha₁def
  have ha₁ : (0 : ℝ) < a₁ := harperMomentScale_pos hA₀
  have ha₁' : a₁ ≠ 0 := ha₁.ne'
  set V : ℝ := harperMomentTilt A₀ C₀ V₀ with hVdef
  have hVV₀ : V₀ ≤ V := le_harperMomentTilt A₀ C₀ V₀
  have hV1 : (1 : ℝ) ≤ V := one_le_harperMomentTilt A₀ C₀ V₀
  have hV0 : (0 : ℝ) < V := by linarith
  have hVK : 8 * (C₀ / a₁) ≤ V := by
    rw [hVdef, ha₁def, harperMomentTilt]
    exact le_max_right _ _
  obtain ⟨x₂, HR⟩ := HR V hVV₀
  obtain ⟨Λ₀, x₁, HL⟩ := HL V hV1
  -- the collar is beaten, uniformly in `q`
  have hcollar : 2 * (C₀ / a₁ * Real.sqrt V) ≤ Real.exp V :=
    mul_sqrt_le_exp (div_nonneg hC₀ ha₁.le) hV1 hVK
  have hsV : (0 : ℝ) < Real.sqrt V := Real.sqrt_pos.2 hV0
  have hsV' : Real.sqrt V ≠ 0 := hsV.ne'
  have hVq : ∀ t : ℝ, (0 : ℝ) < V ^ t := fun t => Real.rpow_pos_of_pos hV0 t
  set c₂ : ℝ := harperMomentRoot A₀ cr C₀ V₀ with hc₂def
  have hc₂ : (0 : ℝ) < c₂ := harperMomentRoot_pos hA₀ hcr
  have hc₂eq : c₂ = cr * (a₁ / (2 * Real.sqrt V)) := by
    rw [hc₂def, ha₁def, hVdef, harperMomentRoot]
  have hconst : harperMomentConst A₀ cr C₀ V₀ = min (c₂ ^ ((4 : ℝ) / 3)) (c₂ ^ (2 : ℝ)) := by
    rw [hc₂def, harperMomentConst]
  -- the `x`-threshold: every hypothesis of the two sources is `x` large
  set Λm : ℝ := max (max Λ₀ ((B₀ : ℝ) + 2))
      (max (6 * (B₀ : ℝ) + 3 * Real.log V + ct) (9 / 4)) with hΛmdef
  set Lm : ℝ := max (4 * V * (4 * Real.exp (2 * (B₀ : ℝ) + 6) + 7)) (8 * V) with hLmdef
  refine ⟨max (max x₁ x₂) (max 3 (max (Real.exp (Real.exp Λm)) (Real.exp Lm))), ?_⟩
  intro f μ hf x q hx hq23 hq1
  -- unpack the threshold
  have hxx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxx₂ : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : (3 : ℝ) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxΛ : Real.exp (Real.exp Λm) ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hx)
  have hxL : Real.exp Lm ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hx)
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hLmx : Lm ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxL
  have hLm0 : (0 : ℝ) < Lm := by
    rw [hLmdef]
    exact lt_of_lt_of_le (show (0 : ℝ) < 8 * V by linarith) (le_max_right _ _)
  have hlogx : (0 : ℝ) < Real.log x := lt_of_lt_of_le hLm0 hLmx
  have hΛmx : Λm ≤ Real.log (Real.log x) :=
    (Real.le_log_iff_exp_le hlogx).2 ((Real.le_log_iff_exp_le hx0).2 hxΛ)
  -- the four `Λ` hypotheses and the two `log x` ones
  have hΛ₀le : Λ₀ ≤ Real.log (Real.log x) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΛmx
  have hBΛ : (B₀ : ℝ) + 2 ≤ Real.log (Real.log x) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΛmx
  have hΛcnt : 6 * (B₀ : ℝ) + 3 * Real.log V + ct ≤ Real.log (Real.log x) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hΛmx
  have hΛ94 : (9 : ℝ) / 4 ≤ Real.log (Real.log x) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΛmx
  have hfarwin : 4 * V * (4 * Real.exp (2 * (B₀ : ℝ) + 6) + 7) ≤ Real.log x :=
    le_trans (le_max_left _ _) hLmx
  have h8V : 8 * V ≤ Real.log x := le_trans (le_max_right _ _) hLmx
  -- `1 ≤ q√Λ`
  have hq0 : (0 : ℝ) < q := by linarith
  have hq2 : (0 : ℝ) < 2 * q := by linarith
  have hqΛ : (1 : ℝ) ≤ q * Real.sqrt (Real.log (Real.log x)) := by
    have h32 : (3 : ℝ) / 2 ≤ Real.sqrt (Real.log (Real.log x)) := by
      have h := Real.sqrt_le_sqrt hΛ94
      rwa [show (9 : ℝ) / 4 = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
    nlinarith
  -- the shape factor
  set W : ℝ := 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) with hWdef
  have hW : (0 : ℝ) < W := by
    rw [hWdef]
    nlinarith [Real.sqrt_nonneg (Real.log (Real.log x))]
  have hWq : ∀ t : ℝ, (0 : ℝ) < W ^ t := fun t => Real.rpow_pos_of_pos hW t
  -- the two sources, at this `x` and `q`
  have hR := HR f μ hf x q hxx₂ hq23 hq1.le
  have hL := HL f μ hf x q hxx₁ hx1 hx3 hΛ₀le hBΛ hΛcnt hfarwin h8V hq0 hq1 hqΛ
  set Z : ℝ := ∫ ω, chaosShift f x (4 * V / Real.log x) ω ^ q ∂μ with hZdef
  -- **the exponent bookkeeping**: `(A₀ W^{-q} V^{-q})^{1/(2q)} = A₀^{1/(2q)} W^{-1/2} V^{-1/2}`
  have hrw : A₀ * W ^ (-q) * V ^ (-q) ≤ Z := by
    rw [hWdef]
    exact hL
  have hAWV : (0 : ℝ) ≤ A₀ * W ^ (-q) * V ^ (-q) :=
    mul_nonneg (mul_nonneg hA₀.le (hWq _).le) (hVq _).le
  have hZ0 : (0 : ℝ) ≤ Z := le_trans hAWV hrw
  have hroot : A₀ ^ (1 / (2 * q)) * W ^ (-(1 / 2) : ℝ) * V ^ (-(1 / 2) : ℝ)
      ≤ Z ^ (1 / (2 * q)) := by
    have hmono := Real.rpow_le_rpow hAWV hrw (div_pos one_pos hq2).le
    refine le_trans (le_of_eq ?_) hmono
    have he : (-q) * (1 / (2 * q)) = -(1 / 2 : ℝ) := by
      field_simp
    rw [Real.mul_rpow (mul_nonneg hA₀.le (hWq _).le) (hVq _).le,
      Real.mul_rpow hA₀.le (hWq _).le,
      ← Real.rpow_mul hW.le, ← Real.rpow_mul hV0.le, he]
  -- `A₀^{1/(2q)} ≥ a₁`, uniformly on `q ∈ [2/3, 1)`
  have hexp1 : (1 : ℝ) / 2 ≤ 1 / (2 * q) := by
    rw [le_div_iff₀ hq2]
    linarith
  have hexp2 : 1 / (2 * q) ≤ (3 : ℝ) / 4 := by
    rw [div_le_iff₀ hq2]
    linarith
  have ha₁le : a₁ ≤ A₀ ^ (1 / (2 * q)) := by
    rw [ha₁def, harperMomentScale]
    exact min_rpow_le_rpow hA₀ hexp1 hexp2
  -- the collar, beaten
  have hVhalf : V ^ (-(1 / 2) : ℝ) = (Real.sqrt V)⁻¹ := by
    rw [Real.rpow_neg hV0.le, Real.sqrt_eq_rpow]
  have hcol : C₀ / Real.exp V ≤ a₁ / 2 * V ^ (-(1 / 2) : ℝ) := by
    rw [hVhalf, div_le_iff₀ (Real.exp_pos V)]
    have hkey := mul_le_mul_of_nonneg_left hcollar
      (show (0 : ℝ) ≤ a₁ / 2 * (Real.sqrt V)⁻¹ from
        mul_nonneg (by linarith) (inv_nonneg.2 (Real.sqrt_nonneg V)))
    have heq : a₁ / 2 * (Real.sqrt V)⁻¹ * (2 * (C₀ / a₁ * Real.sqrt V)) = C₀ := by
      field_simp
    linarith [hkey, heq.ge, heq.le]
  -- put the two together
  have hWr : (0 : ℝ) < W ^ (-(1 / 2) : ℝ) := hWq _
  have hmid : c₂ * W ^ (-(1 / 2) : ℝ)
      ≤ (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) ^ (1 / (2 * q)) := by
    refine le_trans ?_ hR
    rw [hc₂eq]
    have hgap : a₁ / (2 * Real.sqrt V) * W ^ (-(1 / 2) : ℝ)
        ≤ Z ^ (1 / (2 * q)) - C₀ / Real.exp V * W ^ (-(1 / 2) : ℝ) := by
      have h1 : a₁ * V ^ (-(1 / 2) : ℝ) * W ^ (-(1 / 2) : ℝ) ≤ Z ^ (1 / (2 * q)) := by
        refine le_trans ?_ hroot
        have hmul := mul_le_mul_of_nonneg_right ha₁le
          (mul_nonneg (hWq (-(1 / 2) : ℝ)).le (hVq (-(1 / 2) : ℝ)).le)
        calc a₁ * V ^ (-(1 / 2) : ℝ) * W ^ (-(1 / 2) : ℝ)
            = a₁ * (W ^ (-(1 / 2) : ℝ) * V ^ (-(1 / 2) : ℝ)) := by ring
          _ ≤ A₀ ^ (1 / (2 * q)) * (W ^ (-(1 / 2) : ℝ) * V ^ (-(1 / 2) : ℝ)) := hmul
          _ = A₀ ^ (1 / (2 * q)) * W ^ (-(1 / 2) : ℝ) * V ^ (-(1 / 2) : ℝ) := by ring
      have h2 : C₀ / Real.exp V * W ^ (-(1 / 2) : ℝ)
          ≤ a₁ / 2 * V ^ (-(1 / 2) : ℝ) * W ^ (-(1 / 2) : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right hcol hWr.le
        linarith [hmul]
      have h3 : a₁ / (2 * Real.sqrt V) * W ^ (-(1 / 2) : ℝ)
          = a₁ / 2 * V ^ (-(1 / 2) : ℝ) * W ^ (-(1 / 2) : ℝ) := by
        rw [hVhalf]
        field_simp
      rw [h3]
      linarith [h1, h2]
    calc cr * (a₁ / (2 * Real.sqrt V)) * W ^ (-(1 / 2) : ℝ)
        = cr * (a₁ / (2 * Real.sqrt V) * W ^ (-(1 / 2) : ℝ)) := by ring
      _ ≤ cr * (Z ^ (1 / (2 * q)) - C₀ / Real.exp V * W ^ (-(1 / 2) : ℝ)) :=
          mul_le_mul_of_nonneg_left hgap hcr.le
  -- undo the `1/(2q)` root
  set I : ℝ := ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ with hIdef
  have hI0 : (0 : ℝ) ≤ I := by
    rw [hIdef]
    exact integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hpow : (c₂ * W ^ (-(1 / 2) : ℝ)) ^ (2 * q) ≤ I := by
    have h := Real.rpow_le_rpow (mul_nonneg hc₂.le hWr.le) hmid hq2.le
    have hII : (I ^ (1 / (2 * q))) ^ (2 * q) = I := by
      rw [one_div, Real.rpow_inv_rpow hI0 hq2.ne']
    rwa [hII] at h
  refine le_trans ?_ hpow
  rw [hconst, Real.mul_rpow hc₂.le hWr.le, ← Real.rpow_mul hW.le,
    show (-(1 / 2) : ℝ) * (2 * q) = -q by ring]
  gcongr
  exact min_rpow_le_rpow hc₂ (by linarith) (by linarith)

/-- **Harper's lower bound for the Steinhaus random multiplicative function**, on `q ∈ [2/3, 1)`,
with the constant a formula in the walls.

`\displaystyle \int \|S_x\|^{2q} \ \ge\
  \mathrm{harperMomentConst}\,A₀\,c_r\,C₀\,V₀\,\big(1+(1-q)\sqrt{\log\log x}\big)^{-q}`

The two sources are unpacked and the chaos shape's constants collected into `A₀`; the work is
`RMF.le_integral_rpow_normalisedSum_of_shape`.  The walls are existential (none of them is an
explicit numeral) but exposed, so a sharper wall sharpens the constant by instantiation.
`RMF.exists_le_integral_rpow_normalisedSum` is this with them packed away. -/
theorem exists_walls_le_integral_rpow_normalisedSum (Ω : Type*) [MeasurableSpace Ω] :
    ∃ A₀ cr C₀ V₀ : ℝ, 0 < A₀ ∧ 0 < cr ∧ 0 ≤ C₀ ∧ ∃ x₀ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q < 1 →
          harperMomentConst A₀ cr C₀ V₀
              * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
            ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨cr, C₀, V₀, hcr, hC₀, hV₀, HR⟩ := reduction_lower_chaosShift_absorbed (Ω := Ω)
  obtain ⟨a₀, α, hα, ha₀, HL⟩ := exists_le_integral_rpow_chaosShift
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the slack, and the block parameter
  obtain ⟨B₀, HL⟩ := HL (a₀ / Real.log 2) (by rw [div_mul_cancel₀ _ hlog2.ne'])
  obtain ⟨E, hE, HL⟩ := HL B₀ le_rfl Ω
  set κ : ℝ := a₀ / Real.log 2 with hκdef
  -- the absolute factor the shape carries, with `W^{-q}` and `V^{-q}` split off
  set A₀ : ℝ := min α (α ^ (2 : ℝ)) * min 1 (1 / ((6 + 2 / Real.log 2) * E))
      * Real.exp (-(2 * (1 + κ * Real.log 2))) * Real.exp ((B₀ : ℝ) + 69) ^ (-(2 : ℝ))
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
  refine le_integral_rpow_normalisedSum_of_shape (Ω := Ω) (fun f μ => IsSteinhausRMF f μ)
    (A₀ := A₀) (cr := cr) (C₀ := C₀) (V₀ := V₀) (ct := 40) (B₀ := B₀) hA₀ hcr hC₀.le ?_ ?_
  · -- the chaos shape, at the tilt the core picks
    intro V hV1
    obtain ⟨Λ₀, x₁, HL⟩ := HL V hV1
    refine ⟨Λ₀, x₁, ?_⟩
    intro f μ hf x q hxx₁ hx1 hx3 hΛ₀ hBΛ hΛcnt hfarwin h8V hq0 hq1 hqΛ
    replace hf : IsSteinhausRMF f μ := hf
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
    exact HR V hVV₀

/-- **Harper's lower bound for the Steinhaus random multiplicative function**, on `q ∈ [2/3, 1)`.

`\displaystyle \int \|S_x\|^{2q} \ \ge\ c\,\big(1+(1-q)\sqrt{\log\log x}\big)^{-q}`

with `c` and `x₀` independent of `f`, `μ`, `x` and `q`; the space `Ω` is fixed first, and the form
with `c` independent of `Ω` too is Harper's theorem in `RMF/Harper.lean`.

This is the lower half of Harper's theorem on the range where the Euler-product chain applies.
`q < 2/3` comes from it by `RMF.le_target_of_two_thirds_lower`; `q = 1` is the second moment and is
separate.  `RMF.exists_walls_le_integral_rpow_normalisedSum` is the same bound with the constant
left as a formula. -/
theorem exists_le_integral_rpow_normalisedSum (Ω : Type*) [MeasurableSpace Ω] :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q < 1 →
          c * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
            ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨A₀, cr, C₀, V₀, hA₀, hcr, _, x₀, H⟩ := exists_walls_le_integral_rpow_normalisedSum Ω
  exact ⟨harperMomentConst A₀ cr C₀ V₀, harperMomentConst_pos hA₀ hcr, x₀, H⟩

end RMF
