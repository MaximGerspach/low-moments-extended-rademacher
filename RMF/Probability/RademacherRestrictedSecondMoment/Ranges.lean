/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherRestrictedSecondMoment.Drift
import RMF.Probability.RestrictedSecondMoment.Ranges

/-!
# The ranges of the `t`-integral, for the Rademacher function

The Rademacher counterpart of `RMF/Probability/RestrictedSecondMoment/Ranges.lean`: Harper's
`t`-integral in the proof of Key Proposition 5, split into its outer, middle, far and crude ranges,
each bounded, and the `t`-integration.  The geometry (the barrier shifts, the level, the block-count
arithmetic, the split index) is law-free and imported from the Steinhaus file.  What changes:

* the statements carry Harper's height restriction `t ∈ [1/3, 1/2]` (§5.3), because the Rademacher
  pair statistics see the sum frequency as well as the difference;
* the oscillation hypotheses `hosc` at the two doubled heights travel with them, and `Kd` sits
  outside the existential, as in `RMF.exists_proposition7_upper_rademacher`;
* the envelope condition carries `36` where the Steinhaus one carries `13`, the constant of
  `RMF.exists_isBoxComparison_rademacher_of_range`;
* the barrier slope is a parameter `Bs` with `RMF.blockSlope 125 ≤ Bs`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}

/-! ### The outer range

Towards Harper's `P~₂(L(0) ∩ L(t)) ≪ \log²(2/|t|)/(1+(1-q)√Λ)²`: after a shift by `r` blocks the
level is `RMF.shiftedHeight a Bs hf r`, which is `2a + O(\log(2/τ))` for `r ≤ 2\log(2/τ) + 1`
(`RMF.shiftedHeight_le_of_le`; Harper shifts by `D(t) = ⌈2\log(1/|t|)⌉ + B + 1`), and the
denominator `√(N-r)` stays `≫ √Λ` because the outer range keeps `\log(1/τ) < Λ/3`.  The barrier
surgery (`RMF.barrierEventPair_subset_shiftOf`, `RMF.barrierEventPair_subset_of_le`) is law-free. -/

/-- `0 ≤ Bs` from `RMF.blockSlope 125 ≤ Bs`, since the Steinhaus slope is positive. -/
lemma zero_le_of_blockSlope_le {Bs : ℝ} (hBs : blockSlope 125 ≤ Bs) : (0 : ℝ) ≤ Bs :=
  le_trans (blockSlope_pos 125).le hBs

/-- `20 ≤ Bs` from `RMF.blockSlope 125 ≤ Bs`, by `RMF.twenty_le_blockSlope`.  This is why the chain
carries `blockSlope 125 ≤ Bs` rather than `20 ≤ Bs`: the stronger hypothesis gives the weaker one
free, and `RMF.result1Threshold_le_shiftedHeight` needs the stronger. -/
lemma twenty_le_of_blockSlope_le {Bs : ℝ} (hBs : blockSlope 125 ≤ Bs) : (20 : ℝ) ≤ Bs :=
  le_trans (twenty_le_blockSlope 125) hBs

/-! ### The shift geometry at a general slope

`RMF.shiftLevel` is `RMF.shiftedHeight` at `RMF.blockSlope 125` — `RMF.shiftLevel_eq_shiftedHeight`
— and `RMF.freeStart_subset_barrierEvent` is already stated at a general slope `c`.  So the
Rademacher slope needs **no new definition**, only the four facts below: the `RMF.shiftLevel`
lemmas with the constant replaced by a variable `c ≥ 0`, proved as their siblings are. -/

/-- `a ≤ shiftedHeight a c hf r` — the general form of `RMF.le_shiftLevel`. -/
lemma le_shiftedHeight {a c : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (r : ℕ) (hf : ℕ → ℝ) :
    a ≤ shiftedHeight a c hf r := by
  rw [shiftedHeight]
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hlog : (0 : ℝ) ≤ Real.log (1 + r) := Real.log_nonneg (by linarith)
  nlinarith [abs_nonneg (hf r), hc, hr0, ha]

/-- The general form of `RMF.shiftLevel_mul_le`. -/
lemma shiftedHeight_mul_le {T a c : ℝ} (hc : 0 ≤ c) (hT : 1 ≤ T) (r : ℕ) (hf : ℕ → ℝ) :
    shiftedHeight (T * a) c hf r ≤ T * shiftedHeight a c hf r := by
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hlog : (0 : ℝ) ≤ Real.log (1 + r) := Real.log_nonneg (by linarith)
  have hcc : (0 : ℝ) ≤ (c + 1) * r + |hf r| + 10 * Real.log (1 + r) := by
    nlinarith [abs_nonneg (hf r)]
  rw [shiftedHeight, shiftedHeight]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ T - 1) hcc]

/-- The general form of `RMF.shiftLevel_le_of_le`. -/
lemma shiftedHeight_le_of_le {a c τ : ℝ} {r : ℕ} {hf : ℕ → ℝ} (hc : 0 ≤ c)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hr : (r : ℝ) ≤ 2 * Real.log (2 / τ) + 1)
    (hhf : |hf r| ≤ 10 * Real.log r) :
    shiftedHeight a c hf r
      ≤ 2 * a + (42 + 2 * c + (31 + c) / Real.log 2) * Real.log (2 / τ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ Real.log (2 / τ) := by
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ hτ0]
    linarith
  have hL0 : (0 : ℝ) < Real.log (2 / τ) := lt_of_lt_of_le hlog2 hL
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hlogr : Real.log r ≤ (r : ℝ) := by
    rcases Nat.eq_zero_or_pos r with h | h
    · simp [h]
    · have h1 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h
      linarith [Real.log_le_sub_one_of_pos h1]
  have hlog1r : Real.log (1 + r) ≤ 1 + (r : ℝ) := by
    have h1 : (0 : ℝ) < 1 + (r : ℝ) := by linarith
    linarith [Real.log_le_sub_one_of_pos h1]
  have hconst : (31 : ℝ) + c ≤ (31 + c) / Real.log 2 * Real.log (2 / τ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith [hL, hlog2, hc]
  rw [shiftedHeight]
  nlinarith [hr, hlogr, hlog1r, hconst, hc, hL0, abs_nonneg (hf r), hhf]

/-- **`hAR` at a general slope.**  The general form of `RMF.barrierEventPair_subset_shift` and of
`RMF.barrierEventPair_subset_shiftLevel`, which are the same statement proved two ways.

`RMF.freeStart_subset_barrierEvent` already carries the slope as a parameter, so this is that
lemma on each coordinate and nothing else. -/
lemma barrierEventPair_subset_shiftOf {Ω'' : Type*} {Z : ℕ → Ω'' → ℝ × ℝ} {b r : ℕ}
    (hr1 : 1 ≤ r) (hrb : r ≤ b) {a c : ℝ} {hf : ℕ → ℝ}
    (hhf : ∀ j, 1 ≤ j → j ≤ b → |hf j| ≤ 10 * Real.log j) :
    barrierEventPair Z b (fun j => -a - c * j) (fun j => a + j + hf j)
        (fun j => -a - c * j) (fun j => a + j + hf j)
      ⊆ barrierEventPair (fun m => Z (m + r)) (b - r)
          (fun m => -shiftedHeight a c hf r - c * m)
          (fun m => shiftedHeight a c hf r + m + 10 * Real.log m)
          (fun m => -shiftedHeight a c hf r - c * m)
          (fun m => shiftedHeight a c hf r + m + 10 * Real.log m) :=
  Set.inter_subset_inter
    (fun _ hω => freeStart_subset_barrierEvent (X := fun m ω => (Z m ω).1) hrb hhf
      (fun j hjr hjb => hω j (le_trans hr1 hjr) hjb))
    (fun _ hω => freeStart_subset_barrierEvent (X := fun m ω => (Z m ω).2) hrb hhf
      (fun j hjr hjb => hω j (le_trans hr1 hjr) hjb))

/-- **Harper's outer-range barrier bound, for the Rademacher function.**  The twin of
`RMF.exists_measure_barrierEventPair_harper_le`, at Harper's height range. -/
theorem exists_measure_barrierEventPair_harper_le_rademacher (Kd Bs : ℝ) (hKd : 0 ≤ Kd)
    (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
        ∀ (θ σ η τ a : ℝ) (N r d : ℕ) (s₁ s₂ : ℂ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → 1 ≤ r → r + d + 4 ≤ N →
          s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
          0 ≤ η → η ≤ 1 / 10 → |σ| * Real.log (blockScale θ (N - d + 1)) ≤ η →
          1 / 3 ≤ s₁.im → s₁.im ≤ 1 / 2 → 1 / 3 ≤ s₂.im → s₂.im ≤ 1 / 2 → s₁.im ≠ s₂.im →
          |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
          (∀ m, m < N - d →
            |∑ p ∈ primeBlockSub θ m,
                Real.cos (2 * s₁.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) →
          (∀ m, m < N - d →
            |∑ p ∈ primeBlockSub θ m,
                Real.cos (2 * s₂.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) →
          (∀ m, m < N - d - r →
            boxEnvelope (Bs) m + boxEnvelope (Bs) (m + 1)
                + blockWindow m + blockWindow m + 36
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
          max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ a →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 20 ≤ ((N - d - r : ℕ) : ℝ) →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 8 ≤ ((N - d - r : ℕ) : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
                (blockCutoff θ N) s₁ s₂ μ)
              (barrierEventPair
                (fun m ω => ∑ p ∈ primeBlockSub θ m,
                  (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) N
                (fun j => -a - Bs * j) (fun j => a + j + hf j)
                (fun j => -a - Bs * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (shiftedHeight a Bs hf r / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2 := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hprop7⟩ := exists_proposition7_upper_rademacher Kd Bs hKd hBs
  refine ⟨Cst, Tsh, hCst, hTsh, ?_⟩
  intro Ω' _ X μ hX θ σ η τ a N r d s₁ s₂ hf hθ hr1 hrN hre₁ hre₂ hη0 hη1 hσtop
    him₁l him₁u him₂l him₂u himne hτeq hTshle hosc₁ hosc₂ henvc ha hbig hbig2 hhf
  have ha0 : (0 : ℝ) ≤ a := le_trans (le_trans zero_le_one (le_max_left _ _)) ha
  have hσm : ∀ m, m ≤ N - d → |σ| * Real.log (blockScale θ (m + 1)) ≤ η :=
    hsigma_of_top_of_le hσtop
  have hσm1 : ∀ m, m ≤ N - d → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 :=
    fun m hm => le_trans (hσm m hm) (by linarith)
  have hm3 : (3 : ℝ) ≤ ((0 : ℕ) : ℝ) + θ := by
    push_cast
    linarith
  haveI hP : IsProbabilityMeasure (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
      (blockCutoff θ N) s₁ s₂ μ) :=
    isProbabilityMeasure_tiltedMeasure₂_rademacher hX (blockCutoff θ N)
      (re_pos_of_block hm3 hre₁ (hσm1 0 (by omega)))
      (re_pos_of_block hm3 hre₂ (hσm1 0 (by omega)))
  have hsub := barrierEventPair_subset_shiftOf (a := a) (c := Bs)
    (Z := fun m ω => (∑ p ∈ primeBlockSub θ m,
      (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))))
    hr1 (by omega : r ≤ N) hhf
  have hsub' := le_trans hsub (barrierEventPair_subset_of_le (by omega : N - d - r ≤ N - r))
  refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub')) ?_
  refine hprop7 Ω' X μ hX θ σ η (shiftedHeight a Bs hf r) N r (N - d - r) s₁ s₂
    (fun m => 10 * Real.log m) hθ (by omega) hre₁ hre₂ hη0 hη1
    (by rw [show r + (N - d - r) = N - d from by omega]; exact hσtop)
    him₁l him₁u him₂l him₂u himne
    (by rw [hτeq]; exact hTshle)
    (fun m hm => hosc₁ m (by omega)) (fun m hm => hosc₂ m (by omega)) henvc
    (le_trans ha (le_shiftedHeight (zero_le_of_blockSlope_le hBs) ha0 r hf)) (by omega) hbig hbig2
    (fun j hj1 _ => by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 10 * Real.log j)])

/-! ### The two one-height barriers and the pair barrier

The intersection of the two one-height barriers is the pair barrier.  Law-free apart from the
local logarithm, and the identity behind it — `RMF.sum_pair_eq` — is shared. -/

/-- **The intersection of the two barriers is the pair barrier**, for the Rademacher increments. -/
lemma barrierEvent_inter_eq_barrierEventPairAdd {Ω' : Type*} {Y : ℕ → Ω' → ℂ} {θ : ℝ} {N : ℕ}
    {s₁ s₂ : ℂ} {u₁ v₁ u₂ v₂ : ℕ → ℝ} :
    barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω)) N u₁ v₁
        ∩ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω)) N u₂ v₂
      = barrierEventPair (fun m ω => ∑ p ∈ primeBlockSub θ m,
          (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω),
            localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω))) N u₁ v₁ u₂ v₂ := by
  have hpair : ∀ (m : ℕ) (ω : Ω'), (∑ p ∈ primeBlockSub θ m,
      (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω)))
      = ((∑ p ∈ primeBlockSub θ m, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω)),
          ∑ p ∈ primeBlockSub θ m, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω)) :=
    fun m ω => congrFun (sum_pair_eq (fun p ω =>
      (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω))) (primeBlockSub θ m)) ω
  rw [barrierEventPair]
  congr 1
  · congr 1
    funext m ω
    rw [hpair m ω]
  · congr 1
    funext m ω
    rw [hpair m ω]

/-- **The two-height increment process**, for the Rademacher function:
`m ↦ (∑_{p ∈ P_m} \log‖1 + Y_p p^{-s₁}‖, ∑_{p ∈ P_m} \log‖1 + Y_p p^{-s₂}‖)` with
`P_m = RMF.primeBlockSub θ m`, the block sums of `RMF.localLogAdd`.  Every barrier in the outer
range is stated on it. -/
noncomputable def blockPairAdd {Ω' : Type*} (θ : ℝ) (s₁ s₂ : ℂ) (Y : ℕ → Ω' → ℂ) :
    ℕ → Ω' → ℝ × ℝ := fun m ω =>
  (∑ p ∈ primeBlockSub θ m, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω),
    ∑ p ∈ primeBlockSub θ m, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω))

lemma measurable_blockPairAdd {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'}
    (hY : IsRademacherPrimeValues Y ν) (θ : ℝ) (s₁ s₂ : ℂ) (m : ℕ) :
    Measurable (blockPairAdd θ s₁ s₂ Y m) := by
  refine Measurable.prodMk ?_ ?_ <;>
    exact Finset.measurable_sum _ fun p _ =>
      (measurable_localLogAdd _).comp (hY.measurable (p : ℕ) p.2)

/-! ### The in-phase exponent, and why it is still `4`

The far and crude ranges use a two-point bound with no oscillation at all:
`RMF.exists_sum_two_add_two_cos_rpow_low_le` bounds `2 + 2\cos ≤ 4` and gets the fourth power
`(\log N₂/\log N₁)⁴`.  Done crudely, the Rademacher weight `2 + 2\cos uL + 2\cos vL` reaches `6`,
and that is not an artifact: at `t₁ = t₂ = 0` the local moment is exactly `1 + 6n + n²`, so
`E‖F(1/2+σ)‖⁴` is of order `(\log)⁶` for the Rademacher function and `(\log)⁴` for Steinhaus (the
extra `2n` is `E f(p)² = 1`).  Harper's height restriction brings it back to `4`: for
`t₁, t₂ ∈ [1/3, 1/2]` the sum frequency `v = t₁ + t₂ ∈ [2/3, 1]` has `1/v ≤ 3/2 ≤ \log N₁` for
`N₁ ≥ 5`, so its cosine sum is `O(1)` throughout, and only the difference frequency is discarded,
as in the Steinhaus proof.  First `RMF.exists_abs_cos_primesIco_weight_le` loses its tilt
hypothesis `2σ\log N₂ ≤ 1`, which the far range does not have. -/

/-- **The cosine prime sum above `e^{1/τ}` is `O(1)`, with no hypothesis on the tilt**: the
tilt-free form of `RMF.exists_abs_cos_primesIco_weight_le`, whose `2σ\log N₂ ≤ 1` the far range
does not have.  Split at `e^{1/(2σ)}` as in `RMF.exists_sum_two_add_four_cos_rpow_split_le`:
below, the tilted estimate applies; above, the tail `∑ p^{-1-2σ}` is an absolute constant
(`RMF.exists_sum_prime_Ioc_rpow_tail_le`). -/
theorem exists_abs_cos_primesIco_weight_le' :
    ∃ B > 0, ∀ τ σ : ℝ, 0 < τ → τ ≤ 1 → 0 ≤ σ → ∀ N₁ N₂ : ℕ, 2 ≤ N₁ → N₁ ≤ N₂ →
      1 / τ ≤ Real.log (N₁ : ℝ) →
      |∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          Real.cos (τ * Real.log (p : ℝ)) * (p : ℝ) ^ (-1 - 2 * σ)| ≤ B := by
  obtain ⟨B, hB, hcos⟩ := exists_abs_cos_primesIco_weight_le
  obtain ⟨C, hC, htail⟩ := exists_sum_prime_Ioc_rpow_tail_le
  refine ⟨B + C, by positivity, fun τ σ hτ hτ1 hσ N₁ N₂ hN₁ hN12 hlog => ?_⟩
  have hN₁R : (2 : ℝ) ≤ ((N₁ : ℕ) : ℝ) := by exact_mod_cast hN₁
  have hN12R : ((N₁ : ℕ) : ℝ) ≤ ((N₂ : ℕ) : ℝ) := by exact_mod_cast hN12
  -- `|cos| ≤ 1`, so any sub-sum is dominated by the untilted tail
  have habs : ∀ S : Finset ℕ,
      |∑ p ∈ S, Real.cos (τ * Real.log (p : ℝ)) * (p : ℝ) ^ (-1 - 2 * σ)|
        ≤ ∑ p ∈ S, (p : ℝ) ^ (-1 - 2 * σ) := by
    intro S
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun p _ => ?_)
    have hnn : (0 : ℝ) ≤ (p : ℝ) ^ (-1 - 2 * σ) := Real.rpow_nonneg (by positivity) _
    rw [abs_mul, abs_of_nonneg hnn]
    exact mul_le_of_le_one_left hnn (Real.abs_cos_le_one _)
  rcases le_or_gt (2 * σ * Real.log ((N₂ : ℕ) : ℝ)) 1 with hcase | hcase
  · exact le_trans (hcos τ σ hτ hτ1 hσ N₁ N₂ hN₁ hN12 hlog hcase) (by linarith)
  · have hσ0 : 0 < σ := by
      rcases hσ.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h] at hcase
        simp only [mul_zero, zero_mul] at hcase
        linarith
    have h2σ : (0 : ℝ) < 2 * σ := by linarith
    rcases le_or_gt 1 (2 * σ * Real.log ((N₁ : ℕ) : ℝ)) with hlow | hlow
    · -- the range already starts past the truncation: the whole sum is an absolute constant
      refine le_trans (habs _) ?_
      have hconv : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1), (p : ℝ) ^ (-1 - 2 * σ))
          = ∑ p ∈ Finset.Ioc ⌊((N₁ : ℕ) : ℝ)⌋₊ ⌊((N₂ : ℕ) : ℝ)⌋₊ with Nat.Prime p,
              (p : ℝ) ^ (-1 - 2 * σ) := by
        rw [Nat.floor_natCast, Nat.floor_natCast, filter_prime_Ioc_eq_primesIco]
      rw [hconv]
      have hb := htail (2 * σ) ((N₁ : ℕ) : ℝ) ((N₂ : ℕ) : ℝ) (by linarith) hN₁R hN12R hlow
      linarith
    · -- split at the truncation scale `e^{1/(2σ)}`
      have hA : Real.log ((N₁ : ℕ) : ℝ) < 1 / (2 * σ) := by
        rw [lt_div_iff₀ h2σ]
        linarith
      have hBt : 1 / (2 * σ) < Real.log ((N₂ : ℕ) : ℝ) := by
        rw [div_lt_iff₀ h2σ]
        linarith
      have hN₁y : ((N₁ : ℕ) : ℝ) < Real.exp (1 / (2 * σ)) := by
        rw [← Real.exp_log (show (0 : ℝ) < ((N₁ : ℕ) : ℝ) by linarith)]
        exact Real.exp_lt_exp.2 hA
      have hN₂y : Real.exp (1 / (2 * σ)) < ((N₂ : ℕ) : ℝ) := by
        rw [← Real.exp_log (show (0 : ℝ) < ((N₂ : ℕ) : ℝ) by linarith)]
        exact Real.exp_lt_exp.2 hBt
      have hy2 : (2 : ℝ) ≤ Real.exp (1 / (2 * σ)) := by linarith
      have hytilt : 1 ≤ 2 * σ * Real.log (Real.exp (1 / (2 * σ))) := by
        rw [Real.log_exp, mul_one_div, div_self (ne_of_gt h2σ)]
      have hN₁K : N₁ ≤ ⌊Real.exp (1 / (2 * σ))⌋₊ := Nat.le_floor hN₁y.le
      have hKN₂ : ⌊Real.exp (1 / (2 * σ))⌋₊ ≤ N₂ := Nat.floor_le_of_le hN₂y.le
      have hK2 : 2 ≤ ⌊Real.exp (1 / (2 * σ))⌋₊ := le_trans hN₁ hN₁K
      have hKy : ((⌊Real.exp (1 / (2 * σ))⌋₊ : ℕ) : ℝ) ≤ Real.exp (1 / (2 * σ)) :=
        Nat.floor_le (Real.exp_pos _).le
      have hKlog : Real.log ((⌊Real.exp (1 / (2 * σ))⌋₊ : ℕ) : ℝ) ≤ 1 / (2 * σ) := by
        have h := Real.log_le_log (by linarith [(by exact_mod_cast hK2 :
          (2 : ℝ) ≤ ((⌊Real.exp (1 / (2 * σ))⌋₊ : ℕ) : ℝ))]) hKy
        rwa [Real.log_exp] at h
      have hKtilt : 2 * σ * Real.log ((⌊Real.exp (1 / (2 * σ))⌋₊ : ℕ) : ℝ) ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left hKlog h2σ.le
        rwa [mul_one_div, div_self (ne_of_gt h2σ)] at h
      have hsum : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
            Real.cos (τ * Real.log (p : ℝ)) * (p : ℝ) ^ (-1 - 2 * σ))
          = (∑ p ∈ primesIco (N₁ + 1) (⌊Real.exp (1 / (2 * σ))⌋₊ + 1),
              Real.cos (τ * Real.log (p : ℝ)) * (p : ℝ) ^ (-1 - 2 * σ))
            + ∑ p ∈ primesIco (⌊Real.exp (1 / (2 * σ))⌋₊ + 1) (N₂ + 1),
                Real.cos (τ * Real.log (p : ℝ)) * (p : ℝ) ^ (-1 - 2 * σ) := by
        rw [← primesIco_union (by omega : N₁ + 1 ≤ ⌊Real.exp (1 / (2 * σ))⌋₊ + 1)
            (by omega : ⌊Real.exp (1 / (2 * σ))⌋₊ + 1 ≤ N₂ + 1),
          Finset.sum_union (disjoint_primesIco _ _ _)]
      -- below the truncation, the tilted estimate applies
      have hbelow := hcos τ σ hτ hτ1 hσ N₁ ⌊Real.exp (1 / (2 * σ))⌋₊ hN₁ hN₁K hlog hKtilt
      -- above it, the whole tail is an absolute constant
      have habove : |∑ p ∈ primesIco (⌊Real.exp (1 / (2 * σ))⌋₊ + 1) (N₂ + 1),
          Real.cos (τ * Real.log (p : ℝ)) * (p : ℝ) ^ (-1 - 2 * σ)| ≤ C := by
        refine le_trans (habs _) ?_
        have hconv : (∑ p ∈ primesIco (⌊Real.exp (1 / (2 * σ))⌋₊ + 1) (N₂ + 1),
              (p : ℝ) ^ (-1 - 2 * σ))
            = ∑ p ∈ Finset.Ioc ⌊Real.exp (1 / (2 * σ))⌋₊ ⌊((N₂ : ℕ) : ℝ)⌋₊ with Nat.Prime p,
                (p : ℝ) ^ (-1 - 2 * σ) := by
          rw [Nat.floor_natCast, filter_prime_Ioc_eq_primesIco]
        rw [hconv]
        exact htail (2 * σ) (Real.exp (1 / (2 * σ))) ((N₂ : ℕ) : ℝ) (by linarith) hy2
          (by linarith) hytilt
      rw [hsum]
      exact le_trans (abs_add_le _ _) (add_le_add hbelow habove)

/-- **The Rademacher (5.1) exponent at a general pair, with no oscillation used at the difference
frequency.**  The twin of `RMF.exists_sum_two_add_two_cos_rpow_low_le`, at the same exponent `4`:
the difference frequency `u` is discarded as `2\cos ≤ 2`, and the sum frequency `v` contributes
`O(1)` because `1/|v| ≤ \log N₁`.  Neither the tilt nor a bound on `u` is needed; the far range has
neither. -/
theorem exists_sum_two_add_two_cos_pair_rpow_low_le :
    ∃ D > 0, ∀ (u v σ : ℝ), 0 < |v| → |v| ≤ 1 → 0 ≤ σ → ∀ N₁ N₂ : ℕ, 2 ≤ N₁ → N₁ ≤ N₂ →
      1 / |v| ≤ Real.log (N₁ : ℝ) →
      (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          (2 + 2 * Real.cos (u * Real.log (p : ℝ)) + 2 * Real.cos (v * Real.log (p : ℝ)))
            * (p : ℝ) ^ (-1 - 2 * σ))
        ≤ 4 * (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + D := by
  obtain ⟨D₀, hD₀, hlow⟩ := exists_sum_two_add_two_cos_rpow_low_le
  obtain ⟨B, hB, hcos⟩ := exists_abs_cos_primesIco_weight_le'
  refine ⟨D₀ + 2 * B, by positivity, fun u v σ hv hv1 hσ N₁ N₂ hN₁ hN12 hlogv => ?_⟩
  have habsv : ∀ p : ℕ, Real.cos (v * Real.log (p : ℝ)) = Real.cos (|v| * Real.log (p : ℝ)) := by
    intro p
    rcases abs_cases v with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_mul, Real.cos_neg]
  have hsplit : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
        (2 + 2 * Real.cos (u * Real.log (p : ℝ)) + 2 * Real.cos (v * Real.log (p : ℝ)))
          * (p : ℝ) ^ (-1 - 2 * σ))
      = (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          (2 + 2 * Real.cos (u * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ))
        + 2 * ∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
            Real.cos (|v| * Real.log (p : ℝ)) * (p : ℝ) ^ (-1 - 2 * σ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [habsv p]; ring
  have h1 := hlow u σ hσ N₁ N₂ hN₁ hN12
  have h2 := hcos |v| σ hv hv1 hσ N₁ N₂ hN₁ hN12 hlogv
  rw [abs_le] at h2
  rw [hsplit]
  linarith [h2.1, h2.2]

/-- **The same with the tilt kept**, the twin of `RMF.exists_sum_two_add_two_cos_rpow_split4_le`:
the main term stops at the truncation scale `M`.  The sum-frequency correction is unchanged,
because `RMF.exists_abs_cos_primesIco_weight_le'` is already tilt-free and covers the whole
range. -/
theorem exists_sum_two_add_two_cos_pair_rpow_split4_le :
    ∃ D > 0, ∀ (u v σ : ℝ), 0 < |v| → |v| ≤ 1 → 0 ≤ σ → ∀ N₁ M N₂ : ℕ,
      2 ≤ N₁ → N₁ ≤ M → M ≤ N₂ → 1 / |v| ≤ Real.log (N₁ : ℝ) → 1 ≤ 2 * σ * Real.log (M : ℝ) →
      (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          (2 + 2 * Real.cos (u * Real.log (p : ℝ)) + 2 * Real.cos (v * Real.log (p : ℝ)))
            * (p : ℝ) ^ (-1 - 2 * σ))
        ≤ 4 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + D := by
  obtain ⟨D₀, hD₀, hlow⟩ := exists_sum_two_add_two_cos_rpow_split4_le
  obtain ⟨B, hB, hcos⟩ := exists_abs_cos_primesIco_weight_le'
  refine ⟨D₀ + 2 * B, by positivity,
    fun u v σ hv hv1 hσ N₁ M N₂ hN₁ hNM hMN₂ hlogv hM => ?_⟩
  have hN12 : N₁ ≤ N₂ := le_trans hNM hMN₂
  have habsv : ∀ p : ℕ, Real.cos (v * Real.log (p : ℝ)) = Real.cos (|v| * Real.log (p : ℝ)) := by
    intro p
    rcases abs_cases v with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_mul, Real.cos_neg]
  have hsplit : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
        (2 + 2 * Real.cos (u * Real.log (p : ℝ)) + 2 * Real.cos (v * Real.log (p : ℝ)))
          * (p : ℝ) ^ (-1 - 2 * σ))
      = (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          (2 + 2 * Real.cos (u * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ))
        + 2 * ∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
            Real.cos (|v| * Real.log (p : ℝ)) * (p : ℝ) ^ (-1 - 2 * σ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [habsv p]; ring
  have h1 := hlow u σ hσ N₁ M N₂ hN₁ hNM hMN₂ hM
  have h2 := hcos |v| σ hv hv1 hσ N₁ N₂ hN₁ hN12 hlogv
  rw [abs_le] at h2
  rw [hsplit]
  linarith [h2.1, h2.2]

/-- **The free two-point moment over a range at a general pair, Rademacher, with no oscillation
used at the difference frequency**: `E‖I_{(N₁,N₂]}(s₁)‖²‖I_{(N₁,N₂]}(s₂)‖² ≪ (\log N₂/\log N₁)⁴`,
the fourth power of the Steinhaus twin `RMF.exists_integral_normSq_pairIco_le`.  It needs neither
the tilt nor `1/|t₁-t₂| ≤ \log N₁`, but it needs `1/|t₁+t₂| ≤ \log N₁`: without Harper's height
restriction the weight reaches `6` and the bound would be a sixth power. -/
theorem exists_integral_normSq_pairIco_le_rademacher_at :
    ∃ K > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (σ : ℝ) (s₁ s₂ : ℂ) (N₁ N₂ : ℕ), 0 ≤ σ → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        0 < |s₁.im + s₂.im| → |s₁.im + s₂.im| ≤ 1 →
        400 ≤ (N₁ : ℝ) → N₁ ≤ N₂ → 1 / |s₁.im + s₂.im| ≤ Real.log (N₁ : ℝ) →
        (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₂ ω‖ ^ 2 ∂μ)
          ≤ K * (Real.log (N₂ : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := by
  obtain ⟨C, hC, h51⟩ := exists_abs_log_integral_two_point_le_rademacher_at (Ω := Ω)
  obtain ⟨D, hD, hsum⟩ := exists_sum_two_add_two_cos_pair_rpow_low_le
  refine ⟨Real.exp (D + C), Real.exp_pos _,
    fun f μ hf σ s₁ s₂ N₁ N₂ hσ hre₁ hre₂ hv hv1 hN₁ hN12 hlogv => ?_⟩
  have hexp4 : ∀ r : ℝ, 0 < r → Real.exp (4 * Real.log r) = r ^ 4 := by
    intro r hr
    rw [show (4 : ℝ) * Real.log r = Real.log r + Real.log r + Real.log r + Real.log r by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hr]
    ring
  have hN₁pos : (0 : ℝ) < (N₁ : ℝ) := by linarith
  have hlogN : (1 : ℝ) ≤ Real.log (N₁ : ℝ) := by
    rw [Real.le_log_iff_exp_le hN₁pos]
    linarith [Real.exp_one_lt_d9]
  have hN₂R : ((N₁ : ℕ) : ℝ) ≤ ((N₂ : ℕ) : ℝ) := by exact_mod_cast hN12
  have hlogN₂ : (1 : ℝ) ≤ Real.log (N₂ : ℝ) := le_trans hlogN (Real.log_le_log hN₁pos hN₂R)
  have hs₁ : (0 : ℝ) < s₁.re := by rw [hre₁]; linarith
  have hs₂ : (0 : ℝ) < s₂.re := by rw [hre₂]; linarith
  have hσ' : -(1 / Real.log ((N₂ : ℕ) : ℝ)) ≤ σ := by
    have hpos : (0 : ℝ) < Real.log ((N₂ : ℕ) : ℝ) := by linarith
    have : (0 : ℝ) ≤ 1 / Real.log ((N₂ : ℕ) : ℝ) := by positivity
    linarith
  have h := h51 f μ hf σ ((N₁ : ℕ) : ℝ) ((N₂ : ℕ) : ℝ) s₁ s₂ (by exact_mod_cast hN₁) hN₂R hσ'
    hre₁ hre₂
  rw [Nat.floor_natCast, Nat.floor_natCast] at h
  have herr : C / (Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ)) ≤ C := by
    have hsq : (1 : ℝ) ≤ Real.sqrt ((N₁ : ℕ) : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
    have hden : (1 : ℝ) ≤ Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ) := by nlinarith
    calc C / (Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ)) ≤ C / 1 :=
          div_le_div_of_nonneg_left hC.le (by norm_num) hden
      _ = C := by ring
  have hps := hsum (s₁.im - s₂.im) (s₁.im + s₂.im) σ hv hv1 hσ N₁ N₂
    (by exact_mod_cast (by linarith : (2 : ℝ) ≤ (N₁ : ℝ))) hN12 hlogv
  rw [filter_prime_Ioc_eq_primesIco] at h
  rw [abs_le] at h
  have hlogE : Real.log (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₁ ω‖ ^ 2
      * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₂ ω‖ ^ 2 ∂μ)
      ≤ 4 * (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + (D + C) := by
    linarith [h.2, hps, herr]
  have hEpos := hf.integral_normSq_mul_normSq_Ico_pos (N₁ + 1) (N₂ + 1) hs₁ hs₂
  have hratio : (0 : ℝ) < Real.log (N₂ : ℝ) / Real.log (N₁ : ℝ) := by
    apply div_pos <;> linarith
  have hconv : Real.exp (4 * (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ)))
      + (D + C)) = Real.exp (D + C) * (Real.log (N₂ : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := by
    rw [← Real.log_div (by linarith) (by linarith), Real.exp_add, hexp4 _ hratio]
    ring
  calc (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₂ ω‖ ^ 2 ∂μ)
      = Real.exp (Real.log (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₂ ω‖ ^ 2 ∂μ)) :=
        (Real.exp_log hEpos).symm
    _ ≤ Real.exp (4 * (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + (D + C)) :=
        Real.exp_le_exp.2 hlogE
    _ = Real.exp (D + C) * (Real.log (N₂ : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := hconv

/-- **The same with the tilt kept**, at a general pair: the twin of
`RMF.exists_integral_normSq_pairIco_split_le`, with the main term stopping at the truncation scale
`M`.  This is what keeps the crude range's second regime free of `V`. -/
theorem exists_integral_normSq_pairIco_split_le_rademacher_at :
    ∃ K > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (σ : ℝ) (s₁ s₂ : ℂ) (N₁ M N₂ : ℕ), 0 ≤ σ → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        0 < |s₁.im + s₂.im| → |s₁.im + s₂.im| ≤ 1 →
        400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ → 1 / |s₁.im + s₂.im| ≤ Real.log (N₁ : ℝ) →
        1 ≤ 2 * σ * Real.log (M : ℝ) →
        (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₂ ω‖ ^ 2 ∂μ)
          ≤ K * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := by
  obtain ⟨C, hC, h51⟩ := exists_abs_log_integral_two_point_le_rademacher_at (Ω := Ω)
  obtain ⟨D, hD, hsum⟩ := exists_sum_two_add_two_cos_pair_rpow_split4_le
  refine ⟨Real.exp (D + C), Real.exp_pos _,
    fun f μ hf σ s₁ s₂ N₁ M N₂ hσ hre₁ hre₂ hv hv1 hN₁ hNM hMN₂ hlogv hM => ?_⟩
  have hexp4 : ∀ r : ℝ, 0 < r → Real.exp (4 * Real.log r) = r ^ 4 := by
    intro r hr
    rw [show (4 : ℝ) * Real.log r = Real.log r + Real.log r + Real.log r + Real.log r by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hr]
    ring
  have hN12 : N₁ ≤ N₂ := le_trans hNM hMN₂
  have hN₁pos : (0 : ℝ) < (N₁ : ℝ) := by linarith
  have hlogN : (1 : ℝ) ≤ Real.log (N₁ : ℝ) := by
    rw [Real.le_log_iff_exp_le hN₁pos]
    linarith [Real.exp_one_lt_d9]
  have hMR : ((N₁ : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hNM
  have hN₂R : ((N₁ : ℕ) : ℝ) ≤ ((N₂ : ℕ) : ℝ) := by exact_mod_cast hN12
  have hlogM : (1 : ℝ) ≤ Real.log (M : ℝ) := le_trans hlogN (Real.log_le_log hN₁pos hMR)
  have hlogN₂ : (1 : ℝ) ≤ Real.log (N₂ : ℝ) := le_trans hlogN (Real.log_le_log hN₁pos hN₂R)
  have hs₁ : (0 : ℝ) < s₁.re := by rw [hre₁]; linarith
  have hs₂ : (0 : ℝ) < s₂.re := by rw [hre₂]; linarith
  have hσ' : -(1 / Real.log ((N₂ : ℕ) : ℝ)) ≤ σ := by
    have hpos : (0 : ℝ) < Real.log ((N₂ : ℕ) : ℝ) := by linarith
    have : (0 : ℝ) ≤ 1 / Real.log ((N₂ : ℕ) : ℝ) := by positivity
    linarith
  have h := h51 f μ hf σ ((N₁ : ℕ) : ℝ) ((N₂ : ℕ) : ℝ) s₁ s₂ (by exact_mod_cast hN₁) hN₂R hσ'
    hre₁ hre₂
  rw [Nat.floor_natCast, Nat.floor_natCast] at h
  have herr : C / (Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ)) ≤ C := by
    have hsq : (1 : ℝ) ≤ Real.sqrt ((N₁ : ℕ) : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
    have hden : (1 : ℝ) ≤ Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ) := by nlinarith
    calc C / (Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ)) ≤ C / 1 :=
          div_le_div_of_nonneg_left hC.le (by norm_num) hden
      _ = C := by ring
  have hps := hsum (s₁.im - s₂.im) (s₁.im + s₂.im) σ hv hv1 hσ N₁ M N₂
    (by exact_mod_cast (by linarith : (2 : ℝ) ≤ (N₁ : ℝ))) hNM hMN₂ hlogv hM
  rw [filter_prime_Ioc_eq_primesIco] at h
  rw [abs_le] at h
  have hlogE : Real.log (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₁ ω‖ ^ 2
      * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₂ ω‖ ^ 2 ∂μ)
      ≤ 4 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + (D + C) := by
    linarith [h.2, hps, herr]
  have hEpos := hf.integral_normSq_mul_normSq_Ico_pos (N₁ + 1) (N₂ + 1) hs₁ hs₂
  have hratio : (0 : ℝ) < Real.log (M : ℝ) / Real.log (N₁ : ℝ) := by
    apply div_pos <;> linarith
  have hconv : Real.exp (4 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ)))
      + (D + C)) = Real.exp (D + C) * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := by
    rw [← Real.log_div (by linarith) (by linarith), Real.exp_add, hexp4 _ hratio]
    ring
  calc (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₂ ω‖ ^ 2 ∂μ)
      = Real.exp (Real.log (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₂ ω‖ ^ 2 ∂μ)) :=
        (Real.exp_log hEpos).symm
    _ ≤ Real.exp (4 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + (D + C)) :=
        Real.exp_le_exp.2 hlogE
    _ = Real.exp (D + C) * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := hconv

/-! ### The range-level bounds, with nothing to rotate

The Steinhaus file rotates the common centre away before applying its pair bounds (as in
`RMF.exists_integral_normSq_pair_full_le`).  The Rademacher bounds are already stated at a general
pair, so the rotation has no counterpart here.

The split at `400` is forced by (5.1), whose error term needs it.  Below it the product is bounded
deterministically by `RMF.eulerBound 401`, uniformly in the height, at no cost since the range is
fixed; above it the pair bounds apply. -/

/-- **Splitting the free two-point moment at an intermediate cutoff, for the Rademacher function.**
The twin of `RMF.IsSteinhausRMF.integral_normSq_mul_normSq_Ico_split`, and it needs **no hypothesis
on the two heights**: the squarefree Euler product is a polynomial, so
`RMF.IsRademacherRMF.integral_norm_randomEulerProductIco_sq_mul_sq` factors unconditionally where
its Steinhaus model wants `0 < \Re s` at both points. -/
theorem IsRademacherRMF.integral_normSq_mul_normSq_Ico_split {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ) {y₀ c y : ℕ}
    (h₀ : y₀ ≤ c) (h₁ : c ≤ y) (s₁ s₂ : ℂ) :
    (∫ ω, ‖randomEulerProductIco f y₀ y s₁ ω‖ ^ 2
        * ‖randomEulerProductIco f y₀ y s₂ ω‖ ^ 2 ∂μ)
      = (∫ ω, ‖randomEulerProductIco f y₀ c s₁ ω‖ ^ 2
            * ‖randomEulerProductIco f y₀ c s₂ ω‖ ^ 2 ∂μ)
        * ∫ ω, ‖randomEulerProductIco f c y s₁ ω‖ ^ 2
            * ‖randomEulerProductIco f c y s₂ ω‖ ^ 2 ∂μ := by
  rw [hf.integral_norm_randomEulerProductIco_sq_mul_sq y₀ y s₁ s₂,
    hf.integral_norm_randomEulerProductIco_sq_mul_sq y₀ c s₁ s₂,
    hf.integral_norm_randomEulerProductIco_sq_mul_sq c y s₁ s₂,
    ← primesIco_union h₀ h₁, Finset.prod_union (disjoint_primesIco y₀ c y)]

/-- **The free two-point moment of the full product, at a general pair, Rademacher**:
`E‖F_{N₂}(s₁)‖²‖F_{N₂}(s₂)‖² ≪ \log⁴N₁·(\log M/\log N₁)²`, the twin of
`RMF.exists_integral_normSq_pair_full_le` and `RMF.exists_integral_normSq_pair_full_shift_le`.
Three ranges: `[2,400]` by `RMF.eulerBound 401`, `(400,N₁]` in phase by
`RMF.exists_integral_normSq_pairIco_le_rademacher_at`, `(N₁,N₂]` oscillating by
`RMF.exists_integral_normSq_high_le_rademacher_at`. -/
theorem exists_integral_normSq_pair_full_le_rademacher_at :
    ∃ K > 0, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (σ : ℝ) (s₁ s₂ : ℂ) (N₁ M N₂ : ℕ), 0 ≤ σ → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        0 < |s₁.im - s₂.im| → |s₁.im - s₂.im| ≤ 1 →
        0 < |s₁.im + s₂.im| → |s₁.im + s₂.im| ≤ 1 →
        400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ →
        1 / |s₁.im - s₂.im| ≤ Real.log (N₁ : ℝ) → 1 / |s₁.im + s₂.im| ≤ Real.log 400 →
        1 ≤ 2 * σ * Real.log (M : ℝ) →
        (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N₂ + 1)
                s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N₂ + 1)
                s₂ ω‖ ^ 2 ∂μ)
          ≤ K * Real.log (N₁ : ℝ) ^ 4 * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := by
  obtain ⟨K₁, hK₁, hlow⟩ := exists_integral_normSq_pairIco_le_rademacher_at (Ω := Ω)
  obtain ⟨K₂, hK₂, hhigh⟩ := exists_integral_normSq_high_le_rademacher_at (Ω := Ω)
  have hlog400 : (0 : ℝ) < Real.log 400 := Real.log_pos (by norm_num)
  refine ⟨(1 + eulerBound 401 ^ 4) * K₁ * K₂ / Real.log 400 ^ 4, by positivity,
    fun X μ hX σ s₁ s₂ N₁ M N₂ hσ hre₁ hre₂ hu hu1 hv hv1 hN₁ hNM hMN₂ hlogu hlogv hM => ?_⟩
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hs₁ : (0 : ℝ) < s₁.re := by rw [hre₁]; linarith
  have hs₂ : (0 : ℝ) < s₂.re := by rw [hre₂]; linarith
  have hh₁ : (1 : ℝ) / 2 ≤ s₁.re := by rw [hre₁]; linarith
  have hh₂ : (1 : ℝ) / 2 ≤ s₂.re := by rw [hre₂]; linarith
  have hN₁N : 400 ≤ N₁ := by exact_mod_cast hN₁
  have hcast : (((400 : ℕ) : ℝ)) = (400 : ℝ) := by norm_num
  -- the three ranges
  simp only [← randomEulerProductIco_zero]
  rw [hf.integral_normSq_mul_normSq_Ico_split (Nat.zero_le 401) (by omega : 401 ≤ N₂ + 1) s₁ s₂,
    hf.integral_normSq_mul_normSq_Ico_split (by omega : (400 : ℕ) + 1 ≤ N₁ + 1)
      (by omega : N₁ + 1 ≤ N₂ + 1) s₁ s₂]
  -- `[2,400]`: deterministic, uniform in the height
  have hbot : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 401
          s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 401
            s₂ ω‖ ^ 2 ∂μ)
      ≤ 1 + eulerBound 401 ^ 4 := by
    have hae : ∀ᵐ ω ∂μ,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 401 s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 401
                s₂ ω‖ ^ 2
          ≤ 1 + eulerBound 401 ^ 4 := by
      filter_upwards [ae_forall_norm_le_one hX norm_le_one_rademacherLaw 401] with ω hω
      rw [randomEulerProductIco_zero, randomEulerProductIco_zero]
      have h1 := norm_randomEulerProduct_sqfree_le hω hh₁
      have h2 := norm_randomEulerProduct_sqfree_le hω hh₂
      have hE : (0 : ℝ) ≤ eulerBound 401 := eulerBound_nonneg 401
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2, pow_le_pow_left₀ (norm_nonneg _) h2 2,
        pow_nonneg (norm_nonneg (randomEulerProduct
          (fun ω => squarefreeExtension fun p => X p ω) 401 s₁ ω)) 2,
        pow_nonneg hE 2, sq_nonneg (eulerBound 401 ^ 2)]
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity)
      (integrable_const _) hae) ?_
    simp
  -- `(400,N₁]`: in phase
  have hmid := hlow (fun ω => squarefreeExtension fun p => X p ω) μ hf σ s₁ s₂ 400 N₁ hσ hre₁ hre₂
    hv hv1 (by rw [hcast]) hN₁N (by rw [hcast]; exact hlogv)
  -- `(N₁,N₂]`: oscillating
  have hlogvN : 1 / |s₁.im + s₂.im| ≤ Real.log (N₁ : ℝ) := by
    have : Real.log 400 ≤ Real.log (N₁ : ℝ) := Real.log_le_log (by norm_num) hN₁
    linarith
  have hhi := hhigh (fun ω => squarefreeExtension fun p => X p ω) μ hf σ s₁ s₂ N₁ M N₂ hσ hre₁ hre₂
    hu hu1 hv hv1 hN₁ hNM hMN₂ hlogu hlogvN hM
  have hmid0 := (hf.integral_normSq_mul_normSq_Ico_pos (400 + 1) (N₁ + 1) hs₁ hs₂).le
  have hhi0 := (hf.integral_normSq_mul_normSq_Ico_pos (N₁ + 1) (N₂ + 1) hs₁ hs₂).le
  have hstep : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 401
          (N₁ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 401 (N₁ + 1)
            s₂ ω‖ ^ 2 ∂μ)
      * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (N₁ + 1)
            (N₂ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (N₁ + 1)
              (N₂ + 1) s₂ ω‖ ^ 2 ∂μ
      ≤ (K₁ * (Real.log (N₁ : ℝ) / Real.log ((400 : ℕ) : ℝ)) ^ 4)
        * (K₂ * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2) :=
    mul_le_mul hmid hhi hhi0 (by positivity)
  calc (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 401
              s₁ ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 401
              s₂ ω‖ ^ 2 ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 401
                (N₁ + 1) s₁ ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 401 (N₁ + 1)
                  s₂ ω‖ ^ 2 ∂μ)
            * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (N₁ + 1)
                  (N₂ + 1) s₁ ω‖ ^ 2
                * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (N₁ + 1)
                    (N₂ + 1) s₂ ω‖ ^ 2 ∂μ)
      ≤ (1 + eulerBound 401 ^ 4)
          * ((K₁ * (Real.log (N₁ : ℝ) / Real.log ((400 : ℕ) : ℝ)) ^ 4)
            * (K₂ * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2)) :=
        mul_le_mul hbot hstep (mul_nonneg hmid0 hhi0) (by positivity)
    _ = (1 + eulerBound 401 ^ 4) * K₁ * K₂ / Real.log 400 ^ 4 * Real.log (N₁ : ℝ) ^ 4
          * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := by
        rw [hcast, div_pow]
        field_simp

/-! ### The `shiftLine` forms, specialisations rather than rotations

Downstream everything is stated at `(\text{shiftLine }σ\,t, \text{shiftLine }σ\,u)`.  On the
Steinhaus side the corresponding wrappers are *rotations* — `RMF.integral_normSq_ico_pair_shift`
moves the pair to `(σ, σ+i(u-t))` so that the tower's own shape applies.  Here they are
**specialisations**: the bounds already hold at an arbitrary pair, so each wrapper is one
application with `RMF.re_shiftLine` and `RMF.im_shiftLine` discharging the side conditions.

The Rademacher hypotheses are the Steinhaus ones plus the same three conditions on the **sum**
frequency `t+u`, which on Harper's height range `t, u \in [1/3,1/2]` are free. -/

/-- **The high factor at a general pair of heights, Rademacher.**  The twin of
`RMF.exists_integral_normSq_high_shift_le`. -/
theorem exists_integral_normSq_high_shift_le_rademacher :
    ∃ K > 0, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (σ t u : ℝ) (N₁ M N₂ : ℕ), 0 ≤ σ → 0 < |t - u| → |t - u| ≤ 1 →
        0 < |t + u| → |t + u| ≤ 1 →
        400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ →
        1 / |t - u| ≤ Real.log (N₁ : ℝ) → 1 / |t + u| ≤ Real.log (N₁ : ℝ) →
        1 ≤ 2 * σ * Real.log (M : ℝ) →
        (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (N₁ + 1)
                (N₂ + 1) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (N₁ + 1)
                (N₂ + 1) (shiftLine σ u) ω‖ ^ 2 ∂μ)
          ≤ K * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := exists_integral_normSq_high_le_rademacher_at (Ω := Ω)
  refine ⟨K, hK, fun X μ hX σ t u N₁ M N₂ hσ htu htu1 hsm hsm1 hN₁ hNM hMN₂ hlgd hlgs hM => ?_⟩
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  exact hbound _ μ hf σ (shiftLine σ t) (shiftLine σ u) N₁ M N₂ hσ (re_shiftLine σ t)
    (re_shiftLine σ u) (by simpa using htu) (by simpa using htu1) (by simpa using hsm)
    (by simpa using hsm1) hN₁ hNM hMN₂ (by simpa using hlgd) (by simpa using hlgs) hM

/-- **`RMF.exists_integral_normSq_pairIco_split_le_rademacher_at` in the `shiftLine` shape.**  The
twin of `RMF.exists_integral_normSq_pairIco_split_shift_le`. -/
theorem exists_integral_normSq_pairIco_split_shift_le_rademacher :
    ∃ K > 0, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (σ t u : ℝ) (N₁ M N₂ : ℕ), 0 ≤ σ → 0 < |t + u| → |t + u| ≤ 1 →
        400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ → 1 / |t + u| ≤ Real.log (N₁ : ℝ) →
        1 ≤ 2 * σ * Real.log (M : ℝ) →
        (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (N₁ + 1)
                (N₂ + 1) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (N₁ + 1)
                (N₂ + 1) (shiftLine σ u) ω‖ ^ 2 ∂μ)
          ≤ K * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := by
  obtain ⟨K, hK, hbound⟩ := exists_integral_normSq_pairIco_split_le_rademacher_at (Ω := Ω)
  refine ⟨K, hK, fun X μ hX σ t u N₁ M N₂ hσ hsm hsm1 hN₁ hNM hMN₂ hlgs hM => ?_⟩
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  exact hbound _ μ hf σ (shiftLine σ t) (shiftLine σ u) N₁ M N₂ hσ (re_shiftLine σ t)
    (re_shiftLine σ u) (by simpa using hsm) (by simpa using hsm1) hN₁ hNM hMN₂
    (by simpa using hlgs) hM

/-- **The free two-point moment of the full product at a general pair, in the `shiftLine` shape.**
The twin of `RMF.exists_integral_normSq_pair_full_shift_le`, which is the form the far range
needs. -/
theorem exists_integral_normSq_pair_full_shift_le_rademacher :
    ∃ K > 0, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (σ t u : ℝ) (N₁ M N₂ : ℕ), 0 ≤ σ → 0 < |t - u| → |t - u| ≤ 1 →
        0 < |t + u| → |t + u| ≤ 1 →
        400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ →
        1 / |t - u| ≤ Real.log (N₁ : ℝ) → 1 / |t + u| ≤ Real.log 400 →
        1 ≤ 2 * σ * Real.log (M : ℝ) →
        (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N₂ + 1)
                (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N₂ + 1)
                (shiftLine σ u) ω‖ ^ 2 ∂μ)
          ≤ K * Real.log (N₁ : ℝ) ^ 4 * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := exists_integral_normSq_pair_full_le_rademacher_at (Ω := Ω)
  refine ⟨K, hK, fun X μ hX σ t u N₁ M N₂ hσ htu htu1 hsm hsm1 hN₁ hNM hMN₂ hlgd hlgs hM => ?_⟩
  exact hbound X μ hX σ (shiftLine σ t) (shiftLine σ u) N₁ M N₂ hσ (re_shiftLine σ t)
    (re_shiftLine σ u) (by simpa using htu) (by simpa using htu1) (by simpa using hsm)
    (by simpa using hsm1) hN₁ hNM hMN₂ (by simpa using hlgd) (by simpa using hlgs) hM

/-! ### The far range

The split index is `0`, so there is no quotient and no pull-out: the restricted moment is a barrier
probability times a free one, exactly, and the free one is bounded by the full-product estimate
above.  Everything between the two is law-free — `RMF.harper_far_collapse` does the arithmetic —
so only the two ends need twinning. -/

/-- **The far range, end to end, Rademacher**: the twin of
`RMF.setIntegral_normSq_pair_far_envelope_le`, in the same shape,
`P~₂(L t ∩ L u)·E‖F_t‖²‖F_u‖² ≤ \text{Cst}\,K\,Θ²\log⁴(2Θ)·(L²/W²)·1/(τ\log²(2/τ))`.  The barrier
probability is a hypothesis, since its own hypothesis list is Harper's data; the free two-point
moment is `RMF.exists_integral_normSq_pair_full_shift_le_rademacher`, and the law-free
`RMF.harper_far_collapse` multiplies them out. -/
theorem setIntegral_normSq_pair_far_envelope_le_rademacher {Ω' : Type*} [MeasurableSpace Ω'] :
    ∃ K > 0, ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
      ∀ (σ t u : ℝ) (N₁ M N₂ : ℕ) (Θ W Cst : ℝ) (A : Set Ω'),
      0 ≤ σ → 0 < |t - u| → |t - u| ≤ 1 → 0 < |t + u| → |t + u| ≤ 1 →
      400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ →
      1 / |t - u| ≤ Real.log (N₁ : ℝ) → 1 / |t + u| ≤ Real.log 400 →
      1 ≤ 2 * σ * Real.log (M : ℝ) →
      0 ≤ Cst → Real.log (N₁ : ℝ) ≤ Θ →
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) (N₂ + 1)
            (shiftLine σ t) (shiftLine σ u) ν A).toReal
          ≤ Cst * Real.log (2 / |t - u|) ^ 2 / W ^ 2 →
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) (N₂ + 1)
            (shiftLine σ t) (shiftLine σ u) ν A).toReal
          * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (N₂ + 1)
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (N₂ + 1)
                  (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ Cst * K * Θ ^ 2 * Real.log (2 * Θ) ^ 4
            * (Real.log (M : ℝ) ^ 2 / W ^ 2)
            * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) := by
  obtain ⟨K, hK, hfree⟩ := exists_integral_normSq_pair_full_shift_le_rademacher (Ω := Ω')
  refine ⟨K, hK, ?_⟩
  intro Y ν hY σ t u N₁ M N₂ Θ W Cst A hσ htu htu1 hsm hsm1 hN₁ hNM hMN₂ hlgd hlgs hM
    hCst hΘ hbar
  have hmom := hfree Y ν hY σ t u N₁ M N₂ hσ htu htu1 hsm hsm1 hN₁ hNM hMN₂ hlgd hlgs hM
  have hE0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
        (N₂ + 1) (shiftLine σ t) ω‖ ^ 2
      * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (N₂ + 1)
          (shiftLine σ u) ω‖ ^ 2 ∂ν := integral_nonneg fun ω => by positivity
  have hmom' : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (N₂ + 1)
          (shiftLine σ t) ω‖ ^ 2
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (N₂ + 1)
            (shiftLine σ u) ω‖ ^ 2 ∂ν)
      ≤ K * Real.log (N₁ : ℝ) ^ 4
          * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := hmom
  exact harper_far_collapse hCst hK.le htu htu1 hlgd hΘ hE0 hbar hmom'

/-! ### The block products are the exponentials the pull-out reads

The middle range's chain moves between two descriptions of the same object: the Euler product over
a range of blocks, and the exponential of the increments between them.  For the Rademacher function
the increment is `RMF.localLogAdd` and the base identity is
`RMF.log_norm_randomEulerProductIco_sqfree_eq_walk`; everything else is the Steinhaus argument
unchanged, because the blocks multiply (`RMF.eulerProductIco_mul`, law-free) and the norms are
positive (`RMF.norm_randomEulerProductIco_sqfree_pos`). -/

/-- **The block product from `x_a` to `x_b` is the exponential of the increments between**, for the
Rademacher function.  The twin of `RMF.log_norm_randomEulerProductIco_eq_sum`. -/
lemma log_norm_randomEulerProductIco_sqfree_eq_sum {Ω : Type*} {Y : ℕ → Ω → ℂ} (θ : ℝ) {a b : ℕ}
    (hab : a ≤ b) {s : ℂ} (hs : 0 < s.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1), ‖Y p ω‖ ≤ 1) :
    Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
        (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖
      = ∑ m ∈ Finset.Ico a b, ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y ((p : Nat.Primes) : ℕ) ω) := by
  have hfa : ⌊blockScale θ 0⌋₊ + 1 ≤ ⌊blockScale θ a⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (Nat.zero_le a)))
  have hab' : ⌊blockScale θ a⌋₊ + 1 ≤ ⌊blockScale θ b⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ hab))
  have hωa : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ a⌋₊ + 1), ‖Y p ω‖ ≤ 1 := by
    intro p hp
    refine hω p ?_
    rw [mem_primesIco] at hp ⊢
    exact ⟨hp.1, hp.2.1, lt_of_lt_of_le hp.2.2 hab'⟩
  have hωmid : ∀ p ∈ primesIco (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1), ‖Y p ω‖ ≤ 1 := by
    intro p hp
    refine hω p ?_
    rw [mem_primesIco] at hp ⊢
    exact ⟨hp.1, le_trans hfa hp.2.1, hp.2.2⟩
  have hpa := norm_randomEulerProductIco_sqfree_pos (X := Y) hs hωa
  have hpm := norm_randomEulerProductIco_sqfree_pos (X := Y) hs hωmid
  have hmul : ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
        (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ a⌋₊ + 1) s ω‖
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
        (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖
      = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
        (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖ := by
    rw [← norm_mul]
    simp only [randomEulerProductIco]
    rw [eulerProductIco_mul _ hfa hab']
  have hlogsplit := congrArg Real.log hmul
  rw [Real.log_mul hpa.ne' hpm.ne'] at hlogsplit
  have hkey : Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
        (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖
      = Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
          (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖
        - Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
          (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ a⌋₊ + 1) s ω‖ := by
    rw [← hlogsplit]
    ring
  rw [hkey, log_norm_randomEulerProductIco_sqfree_eq_walk θ b hs hω,
    log_norm_randomEulerProductIco_sqfree_eq_walk θ a hs hωa, walk_apply, walk_apply,
    Finset.sum_Ico_eq_sub _ hab]

/-- **The low product is the exponential too**, at one height — the `(2,0)` end of the pull-out's
free coefficients.  The twin of `RMF.normSq_randomEulerProductIco_eq_exp`. -/
lemma normSq_randomEulerProductIco_sqfree_eq_exp {Ω : Type*} {Y : ℕ → Ω → ℂ} (θ : ℝ) {a b : ℕ}
    (hab : a ≤ b) {s : ℂ} (hs : 0 < s.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1), ‖Y p ω‖ ≤ 1) :
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
          (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖ ^ 2
      = Real.exp (2 * ∑ m ∈ Finset.Ico a b, ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y ((p : Nat.Primes) : ℕ) ω)) := by
  have hfa : ⌊blockScale θ 0⌋₊ + 1 ≤ ⌊blockScale θ a⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (Nat.zero_le a)))
  have hωmid : ∀ p ∈ primesIco (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1), ‖Y p ω‖ ≤ 1 := by
    intro p hp
    refine hω p ?_
    rw [mem_primesIco] at hp ⊢
    exact ⟨hp.1, le_trans hfa hp.2.1, hp.2.2⟩
  rw [← log_norm_randomEulerProductIco_sqfree_eq_sum θ hab hs hω,
    show (2 : ℝ) * Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
          (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖
        = Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖
          + Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖ by ring,
    Real.exp_add, Real.exp_log (norm_randomEulerProductIco_sqfree_pos (X := Y) hs hωmid)]
  ring

/-- **The quotient is the exponential the pull-out reads**, for the Rademacher function.  The twin
of `RMF.normSq_mul_normSq_randomEulerProductIco_eq_exp`: the two-height block product between
`x_a` and `x_b`, squared at both heights, is
`\exp(∑_{m ∈ [a,b)}(2\,\text{inc}₁ + 2\,\text{inc}₂))`. -/
lemma normSq_mul_normSq_randomEulerProductIco_sqfree_eq_exp {Ω : Type*} {Y : ℕ → Ω → ℂ} (θ : ℝ)
    {a b : ℕ} (hab : a ≤ b) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1), ‖Y p ω‖ ≤ 1) :
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
          (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
          (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s₂ ω‖ ^ 2
      = Real.exp (∑ m ∈ Finset.Ico a b,
          (2 * (∑ p ∈ primeBlockSub θ m,
                localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω))
            + 2 * ∑ p ∈ primeBlockSub θ m,
                localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω))) := by
  have hfa : ⌊blockScale θ 0⌋₊ + 1 ≤ ⌊blockScale θ a⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (Nat.zero_le a)))
  have hωmid : ∀ p ∈ primesIco (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1), ‖Y p ω‖ ≤ 1 := by
    intro p hp
    refine hω p ?_
    rw [mem_primesIco] at hp ⊢
    exact ⟨hp.1, le_trans hfa hp.2.1, hp.2.2⟩
  have hexp2 : ∀ x : ℝ, 0 < x → Real.exp (2 * Real.log x) = x ^ 2 := by
    intro x hx
    rw [show (2 : ℝ) * Real.log x = Real.log x + Real.log x by ring, Real.exp_add,
      Real.exp_log hx]
    ring
  have hsplit : (∑ m ∈ Finset.Ico a b,
        (2 * (∑ p ∈ primeBlockSub θ m,
              localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω))
          + 2 * ∑ p ∈ primeBlockSub θ m,
              localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω)))
      = 2 * (∑ m ∈ Finset.Ico a b, ∑ p ∈ primeBlockSub θ m,
            localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω))
        + 2 * ∑ m ∈ Finset.Ico a b, ∑ p ∈ primeBlockSub θ m,
            localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsplit, ← log_norm_randomEulerProductIco_sqfree_eq_sum θ hab hs₁ hω,
    ← log_norm_randomEulerProductIco_sqfree_eq_sum θ hab hs₂ hω, Real.exp_add,
    hexp2 _ (norm_randomEulerProductIco_sqfree_pos (X := Y) hs₁ hωmid),
    hexp2 _ (norm_randomEulerProductIco_sqfree_pos (X := Y) hs₂ hωmid)]

/-- **The two-height increment process is independent across blocks**, for the Rademacher
function.  The twin of `RMF.iIndepFun_blockPair`: the blocks are disjoint sets of primes and the
prime values are independent, so the pair-valued block sums are too. -/
lemma iIndepFun_blockPairAdd {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'}
    (hY : IsRademacherPrimeValues Y ν) (θ : ℝ) (s₁ s₂ : ℂ) :
    iIndepFun (blockPairAdd θ s₁ s₂ Y) ν := by
  have h := iIndepFun_finsetSum_of_pairwiseDisjoint
    (f := fun (p : Nat.Primes) (ω : Ω') =>
      (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω)))
    (fun p => ((measurable_localLogAdd _).comp (hY.measurable (p : ℕ) p.2)).prodMk
      ((measurable_localLogAdd _).comp (hY.measurable (p : ℕ) p.2)))
    (hY.iIndep.comp
      (fun (p : Nat.Primes) (z : ℂ) => (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) z,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) z))
      fun _ => (measurable_localLogAdd _).prodMk (measurable_localLogAdd _))
    (S := fun m => primeBlockSub θ m) (pairwise_disjoint_primeBlockSub θ)
  have heq : (fun m (ω : Ω') => ∑ p ∈ primeBlockSub θ m,
        (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω),
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω)))
      = blockPairAdd θ s₁ s₂ Y := by
    funext m
    exact sum_pair_eq _ _
  rwa [heq] at h

@[simp] lemma blockPairAdd_fst {Ω' : Type*} (θ : ℝ) (s₁ s₂ : ℂ) (Y : ℕ → Ω' → ℂ) (m : ℕ)
    (ω : Ω') : (blockPairAdd θ s₁ s₂ Y m ω).1
      = ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω) := rfl

@[simp] lemma blockPairAdd_snd {Ω' : Type*} (θ : ℝ) (s₁ s₂ : ℂ) (Y : ℕ → Ω' → ℂ) (m : ℕ)
    (ω : Ω') : (blockPairAdd θ s₁ s₂ Y m ω).2
      = ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω) := rfl

/-! ### Integrability, for free and with no hypothesis on the heights

The pull-out's monotonicity steps need every integrand to be integrable.  For the Steinhaus
product that is where `\Re s > 0` earns its keep: the deterministic bound
`RMF.IsSteinhausRMF.ae_norm_randomEulerProductIco_le` is `∏_p(1-‖p^{-s}‖)^{-1}`, which is finite
only when the local factors do not reach `1`.

The squarefree product is a polynomial, so its bound is `∏_p(1+‖p^{-s}‖)` and needs nothing at
all — and `RMF.IsRademacherRMF.aemeasurable_randomEulerProductIco` carries no hypothesis on `s`
either.  So the two integrability lemmas below are **unconditional**, where their Steinhaus twins
take `0 < \Re s` at both heights.  Very lossy, as there: used only to license monotonicity, never
to estimate anything.

The bound itself is `RMF.IsRademacherRMF.ae_norm_randomEulerProductIco_le`, beside its
Steinhaus twin in `RMF/EulerProduct/Block.lean`. -/

/-- **The pull-out's integrand is integrable**, deterministically — the low product at one height
times the two high ones.  The twin of `RMF.IsSteinhausRMF.integrable_normSq_triple_Ico`, without
its hypotheses on the heights. -/
lemma IsRademacherRMF.integrable_normSq_triple_Ico {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → ArithmeticFunction ℂ} {μ : Measure Ω'} [IsFiniteMeasure μ]
    (hf : IsRademacherRMF f μ) (a b c d : ℕ) (s₁ s₂ : ℂ) :
    Integrable (fun ω => ‖randomEulerProductIco f a b s₁ ω‖ ^ 2
      * (‖randomEulerProductIco f c d s₁ ω‖ ^ 2
        * ‖randomEulerProductIco f c d s₂ ω‖ ^ 2)) μ := by
  have hpos : ∀ (y₀ y₁ : ℕ) (s : ℂ),
      (0 : ℝ) ≤ ∏ p ∈ primesIco y₀ y₁, (1 + ‖((p : ℕ) : ℂ) ^ (-s)‖) :=
    fun y₀ y₁ s => Finset.prod_nonneg fun p _ => by positivity
  refine Integrable.mono' (integrable_const
    ((∏ p ∈ primesIco a b, (1 + ‖((p : ℕ) : ℂ) ^ (-s₁)‖)) ^ 2
      * (((∏ p ∈ primesIco c d, (1 + ‖((p : ℕ) : ℂ) ^ (-s₁)‖)) ^ 2)
        * ((∏ p ∈ primesIco c d, (1 + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)) ^ 2)))) ?_ ?_
  · exact ((((hf.aemeasurable_randomEulerProductIco a b s₁).norm.pow_const 2).mul
      ((((hf.aemeasurable_randomEulerProductIco c d s₁).norm.pow_const 2)).mul
        ((hf.aemeasurable_randomEulerProductIco c d s₂).norm.pow_const 2)))).aestronglyMeasurable
  · filter_upwards [hf.ae_norm_randomEulerProductIco_le a b s₁,
      hf.ae_norm_randomEulerProductIco_le c d s₁,
      hf.ae_norm_randomEulerProductIco_le c d s₂] with ω h₁ h₂ h₃
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h₁ 2)
      (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h₂ 2)
        (pow_le_pow_left₀ (norm_nonneg _) h₃ 2) (by positivity)
        (pow_nonneg (hpos c d s₁) 2))
      (by positivity) (pow_nonneg (hpos a b s₁) 2)

/-- **The two-height block product is integrable**, deterministically.  The twin of
`RMF.IsSteinhausRMF.integrable_normSq_pair_Ico`, without its hypotheses on the heights. -/
lemma IsRademacherRMF.integrable_normSq_pair_Ico {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → ArithmeticFunction ℂ} {μ : Measure Ω'} [IsFiniteMeasure μ]
    (hf : IsRademacherRMF f μ) (c d : ℕ) (s₁ s₂ : ℂ) :
    Integrable (fun ω => ‖randomEulerProductIco f c d s₁ ω‖ ^ 2
      * ‖randomEulerProductIco f c d s₂ ω‖ ^ 2) μ := by
  have hpos : ∀ (y₀ y₁ : ℕ) (s : ℂ),
      (0 : ℝ) ≤ ∏ p ∈ primesIco y₀ y₁, (1 + ‖((p : ℕ) : ℂ) ^ (-s)‖) :=
    fun y₀ y₁ s => Finset.prod_nonneg fun p _ => by positivity
  refine Integrable.mono' (integrable_const
    ((∏ p ∈ primesIco c d, (1 + ‖((p : ℕ) : ℂ) ^ (-s₁)‖)) ^ 2
      * (∏ p ∈ primesIco c d, (1 + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)) ^ 2)) ?_ ?_
  · exact (((hf.aemeasurable_randomEulerProductIco c d s₁).norm.pow_const 2).mul
      ((hf.aemeasurable_randomEulerProductIco c d s₂).norm.pow_const 2)).aestronglyMeasurable
  · filter_upwards [hf.ae_norm_randomEulerProductIco_le c d s₁,
      hf.ae_norm_randomEulerProductIco_le c d s₂] with ω h₁ h₂
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h₁ 2)
      (pow_le_pow_left₀ (norm_nonneg _) h₂ 2) (by positivity) (pow_nonneg (hpos c d s₁) 2)

/-- **Steps 1 and 2 of the outer-range chain, for the Rademacher function.**  The twin of
`RMF.setIntegral_normSq_pair_le_indicator`: (5.2) at the unshifted envelope replaces the second low
product by its deterministic bound, then the barrier relaxes to any larger event `R` (the order is
forced: (5.2) is stated at the unshifted envelope).  No hypothesis on `s₁`, where the Steinhaus
twin needs `0 < \Re s₁`: the integrability is unconditional and (5.2) is applied only at `s₂`. -/
theorem setIntegral_normSq_pair_le_indicator_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₂ : 0 < s₂.re) {N b k : ℕ} (hkb : k + 1 ≤ b) (hbN : b ≤ N)
    {u₁ v₁ u₂ v₂ : ℕ → ℝ} {R : Set Ω'} (hRm : MeasurableSet R)
    (hAR : barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂ ⊆ R) :
    (∫ ω in barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ Real.exp (v₂ (k + 1)) ^ 2
        * ∫ ω, Set.indicator R (fun ω =>
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2
              * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                    (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
                * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                    (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2))
              ω ∂ν := by
  classical
  haveI := hY.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hf0 : ⌊blockScale θ 0⌋₊ + 1 ≤ ⌊blockScale θ (k + 1)⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (Nat.zero_le _)))
  have hfk : ⌊blockScale θ (k + 1)⌋₊ + 1 ≤ ⌊blockScale θ (N + 1)⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (by omega)))
  have hAm : MeasurableSet (barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂) :=
    measurableSet_barrierEventPair (measurable_blockPairAdd hY θ s₁ s₂) b u₁ v₁ u₂ v₂
  have hGint := hf.integrable_normSq_triple_Ico (⌊blockScale θ 0⌋₊ + 1)
    (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1)
    (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ s₂
  have hae := ae_forall_norm_le_one_primesIco hY norm_le_one_rademacherLaw
    (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1)
  have hkey : ∀ᵐ ω ∂ν, Set.indicator (barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂)
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2) ω
      ≤ Real.exp (v₂ (k + 1)) ^ 2 * Set.indicator R (fun ω =>
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                  (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                  (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2)) ω := by
    filter_upwards [hae] with ω hω
    have hRnn : (0 : ℝ) ≤ Set.indicator R (fun ω =>
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2)) ω :=
      Set.indicator_nonneg (fun _ _ => by positivity) ω
    by_cases hmem : ω ∈ barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hAR hmem)]
      have hmul : ∀ s : ℂ, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s ω‖
          = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s ω‖
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s ω‖ := by
        intro s
        rw [← norm_mul]
        simp only [randomEulerProductIco]
        rw [eulerProductIco_mul _ hf0 hfk]
      have hωk : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1),
          ‖Y p ω‖ ≤ 1 := by
        intro p hp
        refine hω p ?_
        rw [mem_primesIco] at hp ⊢
        exact ⟨hp.1, hp.2.1, lt_of_lt_of_le hp.2.2 hfk⟩
      have h52 := normSq_randomEulerProductIco_sqfree_le_of_mem_barrierEvent θ hs₂ hωk hmem.2
        (Nat.le_add_left 1 k) hkb
      rw [hmul s₁, hmul s₂, mul_pow, mul_pow]
      have hnn : (0 : ℝ) ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2) := by
        positivity
      nlinarith [mul_nonneg (sub_nonneg.2 h52) hnn]
    · rw [Set.indicator_of_notMem hmem]
      have : (0 : ℝ) ≤ Real.exp (v₂ (k + 1)) ^ 2 := by positivity
      exact mul_nonneg this hRnn
  calc (∫ ω in barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      = ∫ ω, Set.indicator (barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2) ω ∂ν :=
        (integral_indicator hAm).symm
    _ ≤ ∫ ω, Real.exp (v₂ (k + 1)) ^ 2 * Set.indicator R (fun ω =>
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                  (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                  (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2)) ω ∂ν :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω =>
            Set.indicator_nonneg (fun _ _ => by positivity) ω)
          ((hGint.indicator hRm).const_mul _) hkey
    _ = _ := integral_const_mul _ _

/-- **Steps 1–3 of the outer-range chain, composed, for the Rademacher function**:
`∫_A ‖F_t‖²‖F_u‖² ≤ e^{2v₂(k+1)}·\big(∫ 1_{R(t)}Q\big)·E[P_t]`.  The twin of
`RMF.setIntegral_normSq_pair_le_pullout`: `RMF.setIntegral_normSq_pair_le_indicator_rademacher`,
then the law-free `RMF.integral_barrierHighProd_mul_lowBlocks` with independence and measurability
from `RMF.iIndepFun_blockPairAdd` and `RMF.measurable_blockPairAdd`. -/
theorem setIntegral_normSq_pair_le_pullout_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b k r n : ℕ} (hkb : k + 1 ≤ b) (hbN : b ≤ N)
    (hkr : k < r) (hrn : r + n ≤ N + 1) {u₁ v₁ u₂ v₂ u₁' v₁' u₂' v₂' : ℕ → ℝ}
    (hAR : barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂
      ⊆ barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂') :
    (∫ ω in barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ Real.exp (v₂ (k + 1)) ^ 2
        * ((∫ ω, Set.indicator
              (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                    (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
                  * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                      (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2)
              ω ∂ν)
          * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν) := by
  classical
  haveI := hY.isProbabilityMeasure
  have hRm : MeasurableSet
      (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂') :=
    measurableSet_barrierEventPair (fun m => measurable_blockPairAdd hY θ s₁ s₂ (m + r))
      n u₁' v₁' u₂' v₂'
  refine le_trans (setIntegral_normSq_pair_le_indicator_rademacher hY θ hs₂ hkb hbN hRm hAR) ?_
  have hfk : ⌊blockScale θ (k + 1)⌋₊ + 1 ≤ ⌊blockScale θ (N + 1)⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (by omega)))
  have hae := ae_forall_norm_le_one_primesIco hY norm_le_one_rademacherLaw
    (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1)
  have hrestrict : ∀ ω : Ω',
      (∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1), ‖Y p ω‖ ≤ 1) →
      ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1), ‖Y p ω‖ ≤ 1 := by
    intro ω hω p hp
    refine hω p ?_
    rw [mem_primesIco] at hp ⊢
    exact ⟨hp.1, hp.2.1, lt_of_lt_of_le hp.2.2 hfk⟩
  have hlowrw : ∀ ω : Ω', (∑ m ∈ Finset.range (k + 1),
        (2 * (∑ p ∈ primeBlockSub θ m,
              localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω))
          + 0 * ∑ p ∈ primeBlockSub θ m,
              localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω)))
      = 2 * ∑ m ∈ Finset.Ico 0 (k + 1), ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω) := by
    intro ω
    rw [← Finset.range_eq_Ico, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hform : (∫ ω, Set.indicator
        (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                  (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                  (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2))
            ω ∂ν)
      = ∫ ω, Set.indicator
            (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
            (fun ω => Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
              (2 * (blockPairAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAdd θ s₁ s₂ Y m ω).2))) ω
          * Real.exp (∑ m ∈ Finset.range (k + 1),
              (2 * (blockPairAdd θ s₁ s₂ Y m ω).1 + 0 * (blockPairAdd θ s₁ s₂ Y m ω).2)) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    by_cases hmem : ω ∈ barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r))
      n u₁' v₁' u₂' v₂'
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      simp only [blockPairAdd_fst, blockPairAdd_snd]
      rw [hlowrw ω,
        normSq_randomEulerProductIco_sqfree_eq_exp θ (Nat.zero_le (k + 1)) hs₁ (hrestrict ω hω),
        normSq_mul_normSq_randomEulerProductIco_sqfree_eq_exp θ (by omega : k + 1 ≤ N + 1)
          hs₁ hs₂ hω]
      ring
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]
  rw [hform, integral_barrierHighProd_mul_lowBlocks (iIndepFun_blockPairAdd hY θ s₁ s₂)
    (measurable_blockPairAdd hY θ s₁ s₂) hkr hrn u₁' v₁' u₂' v₂' 2 0]
  have hQback : (∫ ω, Set.indicator
        (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
        (fun ω => Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
          (2 * (blockPairAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAdd θ s₁ s₂ Y m ω).2))) ω ∂ν)
      = ∫ ω, Set.indicator
            (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                  (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
                * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                    (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2)
            ω ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    by_cases hmem : ω ∈ barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r))
      n u₁' v₁' u₂' v₂'
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      simp only [blockPairAdd_fst, blockPairAdd_snd]
      rw [normSq_mul_normSq_randomEulerProductIco_sqfree_eq_exp θ (by omega : k + 1 ≤ N + 1)
        hs₁ hs₂ hω]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
  have hPback : (∫ ω, Real.exp (∑ m ∈ Finset.range (k + 1),
        (2 * (blockPairAdd θ s₁ s₂ Y m ω).1 + 0 * (blockPairAdd θ s₁ s₂ Y m ω).2)) ∂ν)
      = ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
          (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    simp only [blockPairAdd_fst, blockPairAdd_snd]
    rw [hlowrw ω,
      normSq_randomEulerProductIco_sqfree_eq_exp θ (Nat.zero_le (k + 1)) hs₁ (hrestrict ω hω)]
  rw [hQback, hPback]

/-! ### Harper's licence, for the Rademacher function

The tilt's cutoff does not matter for an event that does not involve the primes in between.  The
whole argument is `MeasureTheory.tilted_tilted` plus `RMF.measure_tilted_preimage_eq_of_indep'`,
both law-free; what has to be twinned is the integrability of a finite block of local weights, and
the two cutoff statements built on it.  The finite-product bound is `(1+‖p^{-s}‖)²`, where the
Steinhaus one is `(1-‖p^{-s}‖)^{-2}`. -/

/-- **A finite block of local weights is bounded, hence integrable**, under any finite measure
absolutely continuous with respect to `μ`.  The twin of `RMF.integrable_exp_sum_localTilt₂`;
`RMF.integrable_exp_localTiltAdd₂` is the one-prime case, and the point of the finite product is
that the bound multiplies out. -/
lemma integrable_exp_sum_localTiltAdd₂ {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (S : Finset Nat.Primes) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) (ν : Measure Ω) [IsFiniteMeasure ν] (hν : ν ≪ μ) :
    Integrable (fun ω => Real.exp (∑ p ∈ S, localTiltAdd₂ s₁ s₂ p (X (p : ℕ) ω))) ν := by
  classical
  haveI := hX.isProbabilityMeasure
  have hae : ∀ p : Nat.Primes, ∀ᵐ ω ∂ν, ‖X (p : ℕ) ω‖ = 1 := by
    intro p
    refine hν.ae_le ?_
    refine ((hX.hasLaw (p : ℕ) p.2).ae_iff ?_).2 norm_eq_one_rademacherLaw
    exact measurableSet_setOf.1 (measurableSet_eq_fun measurable_norm measurable_const)
  have haeS : ∀ᵐ ω ∂ν, ∀ p ∈ S, ‖X (p : ℕ) ω‖ = 1 :=
    (ae_ball_iff S.countable_toSet).2 fun p _ => hae p
  set C : ℝ := ∏ p ∈ S, ((1 + ‖((p : ℕ) : ℂ) ^ (-s₁)‖) ^ 2
    * (1 + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2) with hCdef
  refine (memLp_top_of_bound ?_ C ?_).integrable le_top
  · refine Measurable.aestronglyMeasurable (Real.measurable_exp.comp ?_)
    exact Finset.measurable_sum _ fun p _ =>
      (measurable_localTiltAdd₂ s₁ s₂ p).comp (hX.measurable (p : ℕ) p.2)
  · filter_upwards [haeS] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_sum, hCdef]
    refine Finset.prod_le_prod (fun p _ => (Real.exp_nonneg _)) fun p hp => ?_
    have hw₁ : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ < 1 := norm_prime_cpow_neg_lt_one p.2 hs₁
    have hw₂ : ‖((p : ℕ) : ℂ) ^ (-s₂)‖ < 1 := norm_prime_cpow_neg_lt_one p.2 hs₂
    rw [localTiltAdd₂_apply, Real.exp_add]
    exact mul_le_mul (exp_two_localLogAdd_le (hω p hp) hw₁)
      (exp_two_localLogAdd_le (hω p hp) hw₂) (Real.exp_nonneg _) (by positivity)

/-- **Two prime sets differ by a tilt over the difference**, for an arbitrary subset, Rademacher.
The twin of `RMF.tilted_sum_localTilt₂_eq_tilted_sdiff`: the quotient's tilt weight is a product
over a middle range, not an initial segment, and `Finset.sum_sdiff` does not care. -/
theorem tilted_sum_localTiltAdd₂_eq_tilted_sdiff {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {S S₁ : Finset Nat.Primes} (hS : S₁ ⊆ S)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    μ.tilted (fun ω => ∑ p ∈ S, localTiltAdd₂ s₁ s₂ p (X (p : ℕ) ω))
      = (μ.tilted (fun ω => ∑ p ∈ S₁, localTiltAdd₂ s₁ s₂ p (X (p : ℕ) ω))).tilted
          (fun ω => ∑ p ∈ S \ S₁, localTiltAdd₂ s₁ s₂ p (X (p : ℕ) ω)) := by
  classical
  haveI := hX.isProbabilityMeasure
  rw [tilted_tilted (integrable_exp_sum_localTiltAdd₂ hX S₁ hs₁ hs₂ μ
    (Measure.AbsolutelyContinuous.refl μ))]
  congr 1
  funext ω
  simp only [Pi.add_apply]
  rw [← Finset.sum_sdiff hS]
  exact add_comm _ _

/-- **The licence at a subset, Rademacher.**  The tilt may be taken over `S₁` instead of `S` for an
event that does not involve the primes in between. -/
theorem measure_tilted_sum_localTiltAdd₂_congr {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {S S₁ : Finset Nat.Primes} (hS : S₁ ⊆ S)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {β : Type*} [MeasurableSpace β]
    {u : Ω → β} (hu : Measurable u) {B : Set β} (hB : MeasurableSet B)
    (hindep : IndepFun u (fun ω => ∑ p ∈ S \ S₁, localTiltAdd₂ s₁ s₂ p (X (p : ℕ) ω))
      (μ.tilted (fun ω => ∑ p ∈ S₁, localTiltAdd₂ s₁ s₂ p (X (p : ℕ) ω)))) :
    μ.tilted (fun ω => ∑ p ∈ S, localTiltAdd₂ s₁ s₂ p (X (p : ℕ) ω)) (u ⁻¹' B)
      = μ.tilted (fun ω => ∑ p ∈ S₁, localTiltAdd₂ s₁ s₂ p (X (p : ℕ) ω)) (u ⁻¹' B) := by
  classical
  haveI := hX.isProbabilityMeasure
  haveI : IsProbabilityMeasure
      (μ.tilted (fun ω => ∑ p ∈ S₁, localTiltAdd₂ s₁ s₂ p (X (p : ℕ) ω))) :=
    isProbabilityMeasure_tilted (integrable_exp_sum_localTiltAdd₂ hX S₁ hs₁ hs₂ μ
      (Measure.AbsolutelyContinuous.refl μ))
  have hvm : Measurable (fun ω => ∑ p ∈ S \ S₁, localTiltAdd₂ s₁ s₂ p (X (p : ℕ) ω)) :=
    Finset.measurable_sum _ fun p _ =>
      (measurable_localTiltAdd₂ s₁ s₂ p).comp (hX.measurable (p : ℕ) p.2)
  rw [tilted_sum_localTiltAdd₂_eq_tilted_sdiff hX hS hs₁ hs₂]
  exact measure_tilted_preimage_eq_of_indep' hindep hu hvm hB
    (integrable_exp_sum_localTiltAdd₂ hX (S \ S₁) hs₁ hs₂ _
      (tilted_absolutelyContinuous μ _))

/-! ### The block below the blocks, for the Rademacher function

Step 5 wants `P~_Q(R(t)) = P~₂(R(t))`, and `P~₂` tilts by the product over **all** primes below the
cutoff — including those below `x₀`, which lie in no block at all.  `RMF.augBlock` gives them a
block of their own; it and `RMF.pairwise_disjoint_augBlock` and `RMF.biUnion_augBlock_eq` are
statements about `Finset Nat.Primes` and are law-free, so only the increment process attached to
them has to be twinned. -/

/-- **The quotient's exponent, as a sum over primes**, for the Rademacher function.  The twin of
`RMF.sum_blockPair_Ico_eq_sum_localTilt₂`. -/
lemma sum_blockPairAdd_Ico_eq_sum_localTiltAdd₂ {Ω' : Type*} {Y : ℕ → Ω' → ℂ} (θ : ℝ) {a b : ℕ}
    (hab : a ≤ b) (s₁ s₂ : ℂ) (ω : Ω') :
    (∑ m ∈ Finset.Ico a b,
        (2 * (blockPairAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAdd θ s₁ s₂ Y m ω).2))
      = ∑ p ∈ primesBelowSub (⌊blockScale θ b⌋₊ + 1) \ primesBelowSub (⌊blockScale θ a⌋₊ + 1),
          localTiltAdd₂ s₁ s₂ p (Y ((p : Nat.Primes) : ℕ) ω) := by
  classical
  rw [← biUnion_primeBlockSub_Ico_eq_sdiff θ hab,
    Finset.sum_biUnion fun i _ j _ hij => pairwise_disjoint_primeBlockSub θ hij]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [blockPairAdd_fst, blockPairAdd_snd]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by simp [localTiltAdd₂, localTiltAdd]

/-- The two-height increment process of the augmented family, for the Rademacher function:
`m ↦ (∑_{p ∈ A_m} \log‖1 + Y_p p^{-s₁}‖, ∑_{p ∈ A_m} \log‖1 + Y_p p^{-s₂}‖)` with
`A_m = RMF.augBlock θ m`, so block `m + 1` is `RMF.blockPairAdd θ s₁ s₂ Y m` and block `0` holds
the primes below `x₀`. -/
noncomputable def blockPairAugAdd {Ω' : Type*} (θ : ℝ) (s₁ s₂ : ℂ) (Y : ℕ → Ω' → ℂ) :
    ℕ → Ω' → ℝ × ℝ := fun m ω =>
  (∑ p ∈ augBlock θ m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω),
    ∑ p ∈ augBlock θ m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω))

@[simp] lemma blockPairAugAdd_succ {Ω' : Type*} (θ : ℝ) (s₁ s₂ : ℂ) (Y : ℕ → Ω' → ℂ) (m : ℕ) :
    blockPairAugAdd θ s₁ s₂ Y (m + 1) = blockPairAdd θ s₁ s₂ Y m := rfl

lemma measurable_blockPairAugAdd {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (θ : ℝ) (s₁ s₂ : ℂ) (m : ℕ) :
    Measurable (blockPairAugAdd θ s₁ s₂ Y m) := by
  refine Measurable.prodMk ?_ ?_ <;>
    exact Finset.measurable_sum _ fun p _ =>
      (measurable_localLogAdd _).comp (hY.measurable (p : ℕ) p.2)

/-- **The augmented blocks are independent under any measure the primes are independent under**,
for the Rademacher function.  The form step 5 needs, where the measure is the quotient's own tilt
rather than `ν`. -/
lemma iIndepFun_blockPairAugAdd_of {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    (ν' : Measure Ω') (hm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)))
    (hi : iIndepFun (fun p : Nat.Primes => Y ((p : Nat.Primes) : ℕ)) ν') (θ : ℝ) (s₁ s₂ : ℂ) :
    iIndepFun (blockPairAugAdd θ s₁ s₂ Y) ν' := by
  have h := iIndepFun_finsetSum_of_pairwiseDisjoint
    (f := fun (p : Nat.Primes) (ω : Ω') =>
      (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω)))
    (fun p => ((measurable_localLogAdd _).comp (hm p)).prodMk
      ((measurable_localLogAdd _).comp (hm p)))
    (hi.comp
      (fun (p : Nat.Primes) (z : ℂ) => (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) z,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) z))
      fun _ => (measurable_localLogAdd _).prodMk (measurable_localLogAdd _))
    (S := augBlock θ) (pairwise_disjoint_augBlock θ)
  have heq : (fun m (ω : Ω') => ∑ p ∈ augBlock θ m,
        (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω),
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω)))
      = blockPairAugAdd θ s₁ s₂ Y := by
    funext m
    exact sum_pair_eq _ _
  rwa [heq] at h

/-- **The augmented blocks are independent**, for the Rademacher function.  The base-measure
case of `RMF.iIndepFun_blockPairAugAdd_of`. -/
lemma iIndepFun_blockPairAugAdd {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (θ : ℝ) (s₁ s₂ : ℂ) :
    iIndepFun (blockPairAugAdd θ s₁ s₂ Y) ν :=
  iIndepFun_blockPairAugAdd_of ν (fun p => hY.measurable ((p : Nat.Primes) : ℕ) p.2)
    hY.iIndep θ s₁ s₂

/-- **The low tilt, as a sum over augmented blocks**, for the Rademacher function.  The `(2,2)`
functional over `[0,j]` is `∑_{p < x_j} localTiltAdd₂ p` — all of it, not just the part above
`x₀`. -/
lemma sum_blockPairAugAdd_range_eq_sum_localTiltAdd₂ {Ω' : Type*} {Y : ℕ → Ω' → ℂ} (θ : ℝ)
    (j : ℕ) (s₁ s₂ : ℂ) (ω : Ω') :
    (∑ m ∈ Finset.range (j + 1),
        (2 * (blockPairAugAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAugAdd θ s₁ s₂ Y m ω).2))
      = ∑ p ∈ primesBelowSub (⌊blockScale θ j⌋₊ + 1),
          localTiltAdd₂ s₁ s₂ p (Y ((p : Nat.Primes) : ℕ) ω) := by
  classical
  rw [← biUnion_augBlock_eq θ j,
    Finset.sum_biUnion fun i _ k _ hik => pairwise_disjoint_augBlock θ hik]
  refine Finset.sum_congr rfl fun m _ => ?_
  change 2 * (∑ p ∈ augBlock θ m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω))
      + 2 * (∑ p ∈ augBlock θ m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω))
    = _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by simp [localTiltAdd₂, localTiltAdd]

/-- **The shift sees the same function either way**, for the Rademacher function.  Shifting the
augmented family by `r+1` is shifting the plain one by `r`. -/
lemma shiftExtend_blockPairAugAdd {Ω' : Type*} {Y : ℕ → Ω' → ℂ} (θ : ℝ) (s₁ s₂ : ℂ) (r n : ℕ)
    (ω : Ω') :
    (shiftExtend (r + 1) n fun p : ↑(Finset.Ico (r + 1) (r + 1 + n)) =>
        blockPairAugAdd θ s₁ s₂ Y (p : ℕ) ω)
      = shiftExtend r n fun p : ↑(Finset.Ico r (r + n)) => blockPairAdd θ s₁ s₂ Y (p : ℕ) ω := by
  funext m
  by_cases h : m + r ∈ Finset.Ico r (r + n)
  · have h' : m + (r + 1) ∈ Finset.Ico (r + 1) (r + 1 + n) := by
      rw [Finset.mem_Ico] at h ⊢
      omega
    simp only [shiftExtend, dif_pos h, dif_pos h']
    change blockPairAugAdd θ s₁ s₂ Y (m + (r + 1)) ω = blockPairAdd θ s₁ s₂ Y (m + r) ω
    rw [show m + (r + 1) = m + r + 1 by ring]
    rfl
  · have h' : m + (r + 1) ∉ Finset.Ico (r + 1) (r + 1 + n) := by
      rw [Finset.mem_Ico] at h ⊢
      omega
    simp only [shiftExtend, dif_neg h, dif_neg h']

/-- **Step 5: Harper's licence, at the quotient's tilt, for the Rademacher function**:
`P~_Q(R(t)) = P~₂(R(t))`, tilting by the quotient alone gives the shifted barrier the same measure
as tilting by the whole product.  The twin of `RMF.measure_tilted_quotient_eq_tiltedMeasure₂`: the
primes stay independent under the quotient's tilt (`RMF.iIndepFun_tilted_finsetSum`), hence so do
the augmented blocks, and `RMF.indepFun_barrierShift_lowBlocks` at `(k+1, r+1)` is the hypothesis
of `RMF.measure_tilted_sum_localTiltAdd₂_congr`. -/
theorem measure_tilted_quotient_eq_tiltedMeasure₂_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N k r n : ℕ} (hkN : k + 1 ≤ N + 1)
    (hkr : k < r) (u₁' v₁' u₂' v₂' : ℕ → ℝ) :
    ν.tilted (fun ω => ∑ m ∈ Finset.Ico (k + 1) (N + 1),
          (2 * (blockPairAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAdd θ s₁ s₂ Y m ω).2))
        (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
      = tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω)
          (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ s₂ ν
          (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂') := by
  classical
  haveI := hY.isProbabilityMeasure
  have hTS : primesBelowSub (⌊blockScale θ (k + 1)⌋₊ + 1)
      ⊆ primesBelowSub (⌊blockScale θ (N + 1)⌋₊ + 1) := primesBelowSub_floor_mono hkN
  have hS₁S : primesBelowSub (⌊blockScale θ (N + 1)⌋₊ + 1)
        \ primesBelowSub (⌊blockScale θ (k + 1)⌋₊ + 1)
      ⊆ primesBelowSub (⌊blockScale θ (N + 1)⌋₊ + 1) := Finset.sdiff_subset
  have hdiff : primesBelowSub (⌊blockScale θ (N + 1)⌋₊ + 1)
        \ (primesBelowSub (⌊blockScale θ (N + 1)⌋₊ + 1)
          \ primesBelowSub (⌊blockScale θ (k + 1)⌋₊ + 1))
      = primesBelowSub (⌊blockScale θ (k + 1)⌋₊ + 1) := Finset.sdiff_sdiff_eq_self hTS
  have hexp : (fun ω => ∑ m ∈ Finset.Ico (k + 1) (N + 1),
        (2 * (blockPairAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAdd θ s₁ s₂ Y m ω).2))
      = fun ω => ∑ p ∈ primesBelowSub (⌊blockScale θ (N + 1)⌋₊ + 1)
            \ primesBelowSub (⌊blockScale θ (k + 1)⌋₊ + 1),
          localTiltAdd₂ s₁ s₂ p (Y ((p : Nat.Primes) : ℕ) ω) := by
    funext ω
    exact sum_blockPairAdd_Ico_eq_sum_localTiltAdd₂ θ hkN s₁ s₂ ω
  have hprimes : iIndepFun (fun p : Nat.Primes => Y ((p : Nat.Primes) : ℕ))
      (ν.tilted fun ω => ∑ p ∈ primesBelowSub (⌊blockScale θ (N + 1)⌋₊ + 1)
          \ primesBelowSub (⌊blockScale θ (k + 1)⌋₊ + 1),
        localTiltAdd₂ s₁ s₂ p (Y ((p : Nat.Primes) : ℕ) ω)) :=
    iIndepFun_tilted_finsetSum (𝓧 := fun _ : Nat.Primes => ℂ)
      (X := fun p : Nat.Primes => Y ((p : Nat.Primes) : ℕ)) (g := localTiltAdd₂ s₁ s₂)
      hY.iIndep (fun p => hY.measurable ((p : Nat.Primes) : ℕ) p.2)
      (fun p => measurable_localTiltAdd₂ s₁ s₂ p)
      (fun p _ => integrable_exp_localTiltAdd₂ hY p hs₁ hs₂)
  have hAug := indepFun_barrierShift_lowBlocks
    (iIndepFun_blockPairAugAdd_of _ (fun p => hY.measurable ((p : Nat.Primes) : ℕ) p.2)
      hprimes θ s₁ s₂)
    (measurable_blockPairAugAdd hY θ s₁ s₂) (n := n) (r := r + 1) (k := k + 1) (by omega)
  have hfun1 : (fun ω => shiftExtend (r + 1) n fun p : ↑(Finset.Ico (r + 1) (r + 1 + n)) =>
        blockPairAugAdd θ s₁ s₂ Y (p : ℕ) ω)
      = fun ω => shiftExtend r n fun p : ↑(Finset.Ico r (r + n)) =>
        blockPairAdd θ s₁ s₂ Y (p : ℕ) ω := by
    funext ω
    exact shiftExtend_blockPairAugAdd θ s₁ s₂ r n ω
  have hfun2 : (fun ω => ∑ m ∈ Finset.range (k + 1 + 1),
        (2 * (blockPairAugAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAugAdd θ s₁ s₂ Y m ω).2))
      = fun ω => ∑ p ∈ primesBelowSub (⌊blockScale θ (k + 1)⌋₊ + 1),
          localTiltAdd₂ s₁ s₂ p (Y ((p : Nat.Primes) : ℕ) ω) := by
    funext ω
    exact sum_blockPairAugAdd_range_eq_sum_localTiltAdd₂ θ (k + 1) s₁ s₂ ω
  rw [hfun1, hfun2] at hAug
  have hu : Measurable (fun ω => shiftExtend r n fun p : ↑(Finset.Ico r (r + n)) =>
      blockPairAdd θ s₁ s₂ Y (p : ℕ) ω) :=
    (measurable_shiftExtend r n).comp
      (measurable_pi_lambda _ fun p => measurable_blockPairAdd hY θ s₁ s₂ (p : ℕ))
  rw [hexp, tiltedMeasure₂_eq_tilted_finsetSum_rademacher hY _ hs₁ hs₂,
    barrierEventPair_shift_eq_preimage]
  refine (measure_tilted_sum_localTiltAdd₂_congr hY hS₁S hs₁ hs₂ hu
    (measurableSet_barrierSet n u₁' v₁' u₂' v₂') ?_).symm
  rw [hdiff]
  exact hAug

/-- **The middle range, assembled, for the Rademacher function**: steps 1–5 in Harper's shape,
`∫_A ‖F_t‖²‖F_u‖² ≤ (5.2)·P~₂(R(t))·E[Q]·E[P_t]`, the four factors of his display on p. 53.  The
twin of `RMF.setIntegral_normSq_pair_middle_le`. -/
theorem setIntegral_normSq_pair_middle_le_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b k r n : ℕ} (hkb : k + 1 ≤ b) (hbN : b ≤ N)
    (hkr : k < r) (hrn : r + n ≤ N + 1) {u₁ v₁ u₂ v₂ u₁' v₁' u₂' v₂' : ℕ → ℝ}
    (hAR : barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂
      ⊆ barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂') :
    (∫ ω in barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ Real.exp (v₂ (k + 1)) ^ 2
        * ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ s₂ ν
                (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r))
                  n u₁' v₁' u₂' v₂')).toReal
            * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
                * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                    (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
          * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν) := by
  classical
  haveI := hY.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hRm : MeasurableSet
      (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂') :=
    measurableSet_barrierEventPair (fun m => measurable_blockPairAdd hY θ s₁ s₂ (m + r))
      n u₁' v₁' u₂' v₂'
  refine le_trans (setIntegral_normSq_pair_le_pullout_rademacher hY θ hs₁ hs₂ hkb hbN hkr hrn hAR)
    (le_of_eq ?_)
  have hae := ae_forall_norm_le_one_primesIco hY norm_le_one_rademacherLaw
    (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1)
  have hQae : ∀ᵐ ω ∂ν, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2
      = Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
          (2 * (blockPairAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAdd θ s₁ s₂ Y m ω).2)) := by
    filter_upwards [hae] with ω hω
    simp only [blockPairAdd_fst, blockPairAdd_snd]
    exact normSq_mul_normSq_randomEulerProductIco_sqfree_eq_exp θ (by omega : k + 1 ≤ N + 1)
      hs₁ hs₂ hω
  have hint : Integrable (fun ω => Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
      (2 * (blockPairAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAdd θ s₁ s₂ Y m ω).2))) ν :=
    (hf.integrable_normSq_pair_Ico (⌊blockScale θ (k + 1)⌋₊ + 1)
      (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ s₂).congr hQae
  have h4 := integral_indicator_exp_eq_tilted_mul hint hRm
  have h5 := measure_tilted_quotient_eq_tiltedMeasure₂_rademacher hY θ hs₁ hs₂
    (by omega : k + 1 ≤ N + 1) hkr (n := n) u₁' v₁' u₂' v₂'
  have hind : (∫ ω, Set.indicator
        (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2) ω ∂ν)
      = ∫ ω, Set.indicator
          (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
          (fun ω => Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
            (2 * (blockPairAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAdd θ s₁ s₂ Y m ω).2))) ω ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hQae] with ω hω
    by_cases hmem : ω ∈ barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r))
      n u₁' v₁' u₂' v₂'
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hω]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
  have hfree : (∫ ω, Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
        (2 * (blockPairAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAdd θ s₁ s₂ Y m ω).2)) ∂ν)
      = ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hQae] with ω hω
    rw [hω]
  rw [hind, h4, h5, hfree]

/-- **The two-fold weight is the exponential of the prime sum**, for the Rademacher function.
`RMF.tiltExponent₂_ae_eq_sum_rademacher` and `RMF.IsRademacherRMF.exp_tiltExponent₂_ae_eq`,
composed.  The twin of `RMF.exp_sum_localTilt₂_ae_eq`. -/
lemma exp_sum_localTiltAdd₂_ae_eq {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) :
    (fun ω => Real.exp (∑ p ∈ primesBelowSub y,
        localTiltAdd₂ s₁ s₂ p (X ((p : Nat.Primes) : ℕ) ω)))
      =ᵐ[μ] fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s₁ ω‖ ^ 2
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s₂ ω‖ ^ 2 := by
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  filter_upwards [tiltExponent₂_ae_eq_sum_rademacher hX y hs₁ hs₂,
    hf.exp_tiltExponent₂_ae_eq y hs₁ hs₂] with ω h1 h2
  rw [← h1]
  exact h2

/-- **The bottom of the Euler product comes out**, for the Rademacher function.  The twin of
`RMF.setIntegral_normSq_pair_split_bottom`: the primes below `x₀` lie in no block, so
`RMF.integral_barrierHighProd_mul_lowBlocks` is applied to the *augmented* family at `r = 1`,
`k = 0`, where block `0` is exactly them. -/
theorem setIntegral_normSq_pair_split_bottom_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) (N b : ℕ) (hbN : b ≤ N) (u₁ v₁ u₂ v₂ : ℕ → ℝ) :
    (∫ ω in barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      = (∫ ω in barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                  (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
        * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν := by
  classical
  haveI := hY.isProbabilityMeasure
  have hAm : MeasurableSet (barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂) :=
    measurableSet_barrierEventPair (measurable_blockPairAdd hY θ s₁ s₂) b u₁ v₁ u₂ v₂
  have hf0 : ⌊blockScale θ 0⌋₊ + 1 ≤ ⌊blockScale θ (N + 1)⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (Nat.zero_le _)))
  have hae := ae_forall_norm_le_one_primesIco hY norm_le_one_rademacherLaw
    (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1)
  have hbar : (fun m => blockPairAugAdd θ s₁ s₂ Y (m + 1)) = blockPairAdd θ s₁ s₂ Y := by
    funext m
    exact blockPairAugAdd_succ θ s₁ s₂ Y m
  have hpull := integral_barrierHighProd_mul_lowBlocks (iIndepFun_blockPairAugAdd hY θ s₁ s₂)
    (measurable_blockPairAugAdd hY θ s₁ s₂) (n := b) (r := 1) (k := 0) (N := N + 1)
    (by omega) (by omega) u₁ v₁ u₂ v₂ 2 2
  rw [hbar] at hpull
  have hW : ∀ᵐ ω ∂ν, Real.exp (∑ m ∈ Finset.Ico (0 + 1) (N + 1 + 1),
        (2 * (blockPairAugAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAugAdd θ s₁ s₂ Y m ω).2))
      = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 := by
    filter_upwards [hae] with ω hω
    rw [← Finset.sum_Ico_add' (fun m => 2 * (blockPairAugAdd θ s₁ s₂ Y m ω).1
      + 2 * (blockPairAugAdd θ s₁ s₂ Y m ω).2) 0 (N + 1) 1]
    simp only [blockPairAugAdd_succ, blockPairAdd_fst, blockPairAdd_snd]
    exact (normSq_mul_normSq_randomEulerProductIco_sqfree_eq_exp θ (Nat.zero_le (N + 1))
      hs₁ hs₂ hω).symm
  have hP : ∀ᵐ ω ∂ν, Real.exp (∑ m ∈ Finset.range (0 + 1),
        (2 * (blockPairAugAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAugAdd θ s₁ s₂ Y m ω).2))
      = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 := by
    filter_upwards [exp_sum_localTiltAdd₂_ae_eq hY (⌊blockScale θ 0⌋₊ + 1) hs₁ hs₂] with ω hω
    rw [sum_blockPairAugAdd_range_eq_sum_localTiltAdd₂ θ 0 s₁ s₂ ω]
    exact hω
  have hsplit : ∀ᵐ ω ∂ν,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2
        = (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2)
          * (‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                  (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2) := by
    refine Filter.Eventually.of_forall fun ω => ?_
    have hmul : ∀ s : ℂ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
          (⌊blockScale θ (N + 1)⌋₊ + 1) s ω‖
        = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) s ω‖
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s ω‖ := by
      intro s
      rw [← norm_mul]
      simp only [randomEulerProduct, randomEulerProductIco]
      rw [eulerProduct_mul_eulerProductIco _ hf0]
    rw [hmul s₁, hmul s₂, mul_pow, mul_pow]
    ring
  rw [← integral_indicator hAm, ← integral_indicator hAm]
  have hleft : (∫ ω, Set.indicator (barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂)
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2) ω ∂ν)
      = ∫ ω, Set.indicator (barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂)
          (fun ω => Real.exp (∑ m ∈ Finset.Ico (0 + 1) (N + 1 + 1),
            (2 * (blockPairAugAdd θ s₁ s₂ Y m ω).1
              + 2 * (blockPairAugAdd θ s₁ s₂ Y m ω).2))) ω
        * Real.exp (∑ m ∈ Finset.range (0 + 1),
            (2 * (blockPairAugAdd θ s₁ s₂ Y m ω).1
              + 2 * (blockPairAugAdd θ s₁ s₂ Y m ω).2)) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hW, hP, hsplit] with ω hw hp hs
    by_cases hmem : ω ∈ barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hs, hw, hp]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]
  rw [hleft, hpull]
  refine congrArg₂ (· * ·) (integral_congr_ae ?_) (integral_congr_ae hP)
  filter_upwards [hW] with ω hw
  by_cases hmem : ω ∈ barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hw]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

/-- **The middle range, at the factorised integrand, for the Rademacher function.**  The twin of
`RMF.setIntegral_normSq_pair_full_middle_le`: the middle range with the bottom of the Euler
product pulled out, so that the left-hand side is exactly what the height-integral swap leaves. -/
theorem setIntegral_normSq_pair_full_middle_le_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b k r n : ℕ} (hkb : k + 1 ≤ b) (hbN : b ≤ N)
    (hkr : k < r) (hrn : r + n ≤ N + 1) {u₁ v₁ u₂ v₂ u₁' v₁' u₂' v₂' : ℕ → ℝ}
    (hAR : barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂
      ⊆ barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂') :
    (∫ ω in barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ Real.exp (v₂ (k + 1)) ^ 2
          * ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω)
                  (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ s₂ ν
                  (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n
                    u₁' v₁' u₂' v₂')).toReal
              * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                      (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
                    * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                        (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2
                    ∂ν)
            * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν)
        * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν := by
  rw [setIntegral_normSq_pair_split_bottom_rademacher hY θ hs₁ hs₂ N b hbN u₁ v₁ u₂ v₂]
  exact mul_le_mul_of_nonneg_right
    (setIntegral_normSq_pair_middle_le_rademacher hY θ hs₁ hs₂ hkb hbN hkr hrn hAR)
    (integral_nonneg fun ω => by positivity)

/-- **The middle range end to end, for the Rademacher function**:
`RMF.setIntegral_normSq_pair_full_middle_le_rademacher` composed with the law-free
`RMF.harper_middle_collapse`; the twin of `RMF.setIntegral_normSq_pair_middle_envelope_le`.  The
five bounds are hypotheses because each carries its own hypothesis list about Harper's data. -/
theorem setIntegral_normSq_pair_middle_envelope_le_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b k r n : ℕ} (hkb : k + 1 ≤ b) (hbN : b ≤ N)
    (hkr : k < r) (hrn : r + n ≤ N + 1) {u₁ v₁ u₂ v₂ u₁' v₁' u₂' v₂' : ℕ → ℝ}
    (hAR : barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂
      ⊆ barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
    {X Cst KQ CP K0 L W τ : ℝ} (hCst : 0 ≤ Cst) (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP)
    (hτ0 : 0 < τ) (hlog : Real.log (2 / τ) ≠ 0) (hW : W ≠ 0)
    (h52 : Real.exp (v₂ (k + 1)) ^ 2 ≤ X ^ 2 * (1 / (τ * Real.log (2 / τ) ^ 2)) ^ 2)
    (hbar : (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ s₂ ν
            (barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')).toReal
        ≤ Cst * Real.log (2 / τ) ^ 2 / W ^ 2)
    (hQ : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
        ≤ KQ * (τ * L) ^ 2)
    (hPt : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν)
        ≤ CP * (1 / τ))
    (hP0 : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν) ≤ K0) :
    (∫ ω in barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ X ^ 2 * Cst * KQ * CP * K0 * L ^ 2 / W ^ 2
          * (1 / (τ * Real.log (2 / τ) ^ 2)) := by
  refine le_trans
    (setIntegral_normSq_pair_full_middle_le_rademacher hY θ hs₁ hs₂ hkb hbN hkr hrn hAR) ?_
  exact harper_middle_collapse ENNReal.toReal_nonneg
    (integral_nonneg fun ω => by positivity) (integral_nonneg fun ω => by positivity)
    (integral_nonneg fun ω => by positivity) hCst hKQ hCP hτ0 hlog hW h52 hbar hQ hPt hP0

/-- **The crude range, for the Rademacher function.**  The twin of
`RMF.setIntegral_normSq_pair_crude_le`: the pull-out at `r = k+1`, `n = 0`, where the shifted
barrier is the whole space and the two moments are taken abstractly, so that both of Harper's
regimes are instantiations of one statement rather than two chains. -/
theorem setIntegral_normSq_pair_crude_le_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b k : ℕ} (hkb : k + 1 ≤ b) (hbN : b ≤ N)
    {u₁ v₁ u₂ v₂ : ℕ → ℝ} {KQ CP K0 : ℝ} (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP)
    (hQ : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν) ≤ KQ)
    (hPt : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν) ≤ CP)
    (hP0 : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν) ≤ K0) :
    (∫ ω in barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ Real.exp (v₂ (k + 1)) ^ 2 * (KQ * CP) * K0 := by
  rw [setIntegral_normSq_pair_split_bottom_rademacher hY θ hs₁ hs₂ N b hbN u₁ v₁ u₂ v₂]
  have h12 := setIntegral_normSq_pair_le_pullout_rademacher hY θ hs₁ hs₂ hkb hbN
    (r := k + 1) (n := 0) (lt_add_one k) (by omega)
    (u₁ := u₁) (v₁ := v₁) (u₂ := u₂) (v₂ := v₂)
    (u₁' := u₁) (v₁' := v₁) (u₂' := u₂) (v₂' := v₂)
    (by simp)
  rw [barrierEventPair_zero] at h12
  simp only [Set.indicator_univ] at h12
  refine mul_le_mul (le_trans h12 ?_) hP0 (integral_nonneg fun ω => by positivity)
    (by positivity)
  exact mul_le_mul_of_nonneg_left (mul_le_mul hQ hPt (integral_nonneg fun ω => by positivity) hKQ)
    (by positivity)

/-- **`RMF.exists_measure_barrierEventPair_harper_le_rademacher` with `1 ≤ a`**: the same bound
with the level threshold `max 1 (result1Threshold (1/18) (9/2)) ≤ a` traded for a factor in the
constant; the twin of `RMF.exists_measure_barrierEventPair_harper_one_le`.  The level-`a` event
sits inside the level-`Ta` one (`RMF.barrierEventPair_mono`), and `\min\{1, ·\}` of the scaled level
costs a factor `T`; both steps are law-free. -/
theorem exists_measure_barrierEventPair_harper_one_le_rademacher (Kd Bs : ℝ) (hKd : 0 ≤ Kd)
    (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
        ∀ (θ σ η τ a : ℝ) (N r d : ℕ) (s₁ s₂ : ℂ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → 1 ≤ r → r + d + 4 ≤ N →
          s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
          0 ≤ η → η ≤ 1 / 10 → |σ| * Real.log (blockScale θ (N - d + 1)) ≤ η →
          1 / 3 ≤ s₁.im → s₁.im ≤ 1 / 2 → 1 / 3 ≤ s₂.im → s₂.im ≤ 1 / 2 → s₁.im ≠ s₂.im →
          |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
          (∀ m, m < N - d →
            |∑ p ∈ primeBlockSub θ m,
                Real.cos (2 * s₁.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) →
          (∀ m, m < N - d →
            |∑ p ∈ primeBlockSub θ m,
                Real.cos (2 * s₂.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) →
          (∀ m, m < N - d - r →
            boxEnvelope (Bs) m + boxEnvelope (Bs) (m + 1)
                + blockWindow m + blockWindow m + 36
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
          (1 : ℝ) ≤ a →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 20 ≤ ((N - d - r : ℕ) : ℝ) →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 8 ≤ ((N - d - r : ℕ) : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
                (blockCutoff θ N) s₁ s₂ μ)
              (barrierEventPair
                (fun m ω => ∑ p ∈ primeBlockSub θ m,
                  (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) N
                (fun j => -a - Bs * j) (fun j => a + j + hf j)
                (fun j => -a - Bs * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (shiftedHeight a Bs hf r / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2 := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hbound⟩ := exists_measure_barrierEventPair_harper_le_rademacher
    Kd Bs hKd hBs
  set T : ℝ := max 1 (result1Threshold (1 / 18) (9 / 2)) with hTdef
  have hT1 : (1 : ℝ) ≤ T := le_max_left _ _
  refine ⟨Cst * T ^ 2, Tsh, by positivity, hTsh, ?_⟩
  intro Ω' _ X μ hX θ σ η τ a N r d s₁ s₂ hf hθ hr1 hrN hre₁ hre₂ hη0 hη1 hσtop
    him₁l him₁u him₂l him₂u himne hτeq hTshle hosc₁ hosc₂ henvc ha hbig hbig2 hhf
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hTa : T ≤ T * a := by nlinarith
  have haTa : a ≤ T * a := le_mul_of_one_le_left ha0 hT1
  have hkey := hbound Ω' X μ hX θ σ η τ (T * a) N r d s₁ s₂ hf hθ hr1 hrN hre₁ hre₂ hη0 hη1
    hσtop him₁l him₁u him₂l him₂u himne hτeq hTshle hosc₁ hosc₂ henvc hTa hbig hbig2 hhf
  -- the tilt is a probability measure, so the enlarged event has finite measure
  have hσsm : |σ| ≤ 1 / 4 := by
    have hlog : (4 : ℝ) ≤ Real.log (blockScale θ (N - d + 1)) := by
      rw [log_blockScale]
      have h1 : (0 : ℝ) ≤ ((N - d + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith [Real.add_one_le_exp (((N - d + 1 : ℕ) : ℝ) + θ)]
    nlinarith [abs_nonneg σ, hσtop]
  have hs₁ : (0 : ℝ) < s₁.re := by rw [hre₁]; linarith [neg_abs_le σ, hσsm]
  have hs₂ : (0 : ℝ) < s₂.re := by rw [hre₂]; linarith [neg_abs_le σ, hσsm]
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hPM := hf'.isProbabilityMeasure_tiltedMeasure₂ (blockCutoff θ N) hs₁ hs₂
  -- the level-`a` event sits inside the level-`Ta` one
  have hsub := barrierEventPair_mono
    (Z := fun m ω => ∑ p ∈ primeBlockSub θ m,
      (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) (n := N)
    (u₁ := fun j => -(T * a) - Bs * j) (v₁ := fun j => T * a + j + hf j)
    (u₂ := fun j => -(T * a) - Bs * j) (v₂ := fun j => T * a + j + hf j)
    (u₁' := fun j => -a - Bs * j) (v₁' := fun j => a + j + hf j)
    (u₂' := fun j => -a - Bs * j) (v₂' := fun j => a + j + hf j)
    (fun j _ _ => by linarith) (fun j _ _ => by linarith)
    (fun j _ _ => by linarith) (fun j _ _ => by linarith)
  refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub))
    (le_trans hkey ?_)
  -- and `min\{1, ·\}` of the scaled level costs a factor `T`
  have hsn : (0 : ℝ) ≤ Real.sqrt ((N - d - r : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hlev : shiftedHeight (T * a) Bs hf r / Real.sqrt ((N - d - r : ℕ) : ℝ)
      ≤ T * (shiftedHeight a Bs hf r / Real.sqrt ((N - d - r : ℕ) : ℝ)) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right
      (shiftedHeight_mul_le (zero_le_of_blockSlope_le hBs) hT1 r hf) hsn
  have hmin : min 1 (shiftedHeight (T * a) Bs hf r / Real.sqrt ((N - d - r : ℕ) : ℝ))
      ≤ T * min 1 (shiftedHeight a Bs hf r / Real.sqrt ((N - d - r : ℕ) : ℝ)) :=
    le_trans (min_le_min le_rfl hlev) (min_one_mul_le hT1)
  have hTa0 : (0 : ℝ) ≤ T * a := mul_nonneg (by linarith) ha0
  have hmin0 : (0 : ℝ) ≤ min 1 (shiftedHeight (T * a) Bs hf r / Real.sqrt ((N - d - r : ℕ) : ℝ)) :=
    le_min zero_le_one (div_nonneg (le_trans hTa0
      (le_shiftedHeight (zero_le_of_blockSlope_le hBs) hTa0 r hf)) hsn)
  have hsq := pow_le_pow_left₀ hmin0 hmin 2
  rw [mul_pow] at hsq
  calc Cst * min 1 (shiftedHeight (T * a) Bs hf r / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2
      ≤ Cst * (T ^ 2 * min 1 (shiftedHeight a Bs hf r / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hCst.le
    _ = Cst * T ^ 2
        * min 1 (shiftedHeight a Bs hf r / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2 := by
        ring

/-- **The barrier probability of the factorised integrand in the outer range, for the Rademacher
function.**  The twin of `RMF.exists_measure_barrier_inter_harper_le`: the factorisation produces
an intersection of two one-coordinate barriers, Proposition 7 bounds a pair-valued one, and
`RMF.barrierEvent_inter_eq_barrierEventPairAdd` identifies them.  At the heights `shiftLine σ t`,
`shiftLine σ u` Harper's restriction reads `t, u ∈ [1/3, 1/2]`, and the oscillation hypotheses sit
at `2t` and `2u`. -/
theorem exists_measure_barrier_inter_harper_le_rademacher (Kd Bs : ℝ) (hKd : 0 ≤ Kd)
    (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (θ σ η a : ℝ) (N r d : ℕ) (t u : ℝ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → 1 ≤ r → r + d + 4 ≤ N →
          0 ≤ η → η ≤ 1 / 10 → |σ| * Real.log (blockScale θ (N - d + 1)) ≤ η →
          1 / 3 ≤ t → t ≤ 1 / 2 → 1 / 3 ≤ u → u ≤ 1 / 2 →
          0 < |t - u| → |t - u| ≤ 1 → Tsh ≤ |t - u| * Real.exp ((r : ℝ) + θ) →
          (∀ m, m < N - d →
            |∑ p ∈ primeBlockSub θ m,
                Real.cos (2 * t * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) →
          (∀ m, m < N - d →
            |∑ p ∈ primeBlockSub θ m,
                Real.cos (2 * u * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) →
          (∀ m, m < N - d - r →
            boxEnvelope (Bs) m + boxEnvelope (Bs) (m + 1)
                + blockWindow m + blockWindow m + 36
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
          (1 : ℝ) ≤ a →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 20 ≤ ((N - d - r : ℕ) : ℝ) →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 8 ≤ ((N - d - r : ℕ) : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) (blockCutoff θ N)
                (shiftLine σ t) (shiftLine σ u) ν)
              (barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) N
                  (fun j => -a - Bs * j) (fun j => a + j + hf j)
                ∩ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ u))) (Y (p : ℕ) ω)) N
                  (fun j => -a - Bs * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (shiftedHeight a Bs hf r / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2 := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hbound⟩ :=
    exists_measure_barrierEventPair_harper_one_le_rademacher Kd Bs hKd hBs
  refine ⟨Cst, Tsh, hCst, hTsh, ?_⟩
  intro Ω' _ Y ν hY θ σ η a N r d t u hf hθ hr1 hrN hη0 hη1 hσtop htl htu hul huu
    hτ0 hτ1 hTshle hosc₁ hosc₂ henvc ha hbig hbig2 hhf
  rw [barrierEvent_inter_eq_barrierEventPairAdd]
  have hne : (shiftLine σ t).im ≠ (shiftLine σ u).im := by
    simp only [im_shiftLine]
    intro h
    rw [h, sub_self, abs_zero] at hτ0
    exact lt_irrefl 0 hτ0
  exact hbound Ω' Y ν hY θ σ η |t - u| a N r d (shiftLine σ t) (shiftLine σ u) hf hθ hr1 hrN
    (re_shiftLine σ t) (re_shiftLine σ u) hη0 hη1 hσtop
    (by simpa using htl) (by simpa using htu) (by simpa using hul) (by simpa using huu) hne
    (by simp only [im_shiftLine]) hTshle
    (by simpa using hosc₁) (by simpa using hosc₂) henvc ha hbig hbig2 hhf

/-- **Harper's display on p. 53, for the Rademacher function**: in the outer range the two-point
barrier probability is at most `Cst·\log²(2/|t-u|)/(1+(1-q)√Λ)²`, `Cst` depending only on `κ`,
`Kd` and `Bs`.  The twin of `RMF.exists_measure_barrier_inter_display_le`, with the same `Λ`
arithmetic (`RMF.min_one_div_sqrt_sq_le`).  `m` stands for `\min\{√Λ, 1/(1-q)\}` through its two
defining properties, so `q = 1` is not a division by zero. -/
theorem exists_measure_barrier_inter_display_le_rademacher (κ Kd Bs : ℝ) (hκ : 0 ≤ κ)
    (hKd : 0 ≤ Kd) (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (θ σ η a Λ q m : ℝ) (N r d : ℕ) (t u : ℝ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → 1 ≤ r → r + d + 4 ≤ N →
          0 ≤ η → η ≤ 1 / 10 → |σ| * Real.log (blockScale θ (N - d + 1)) ≤ η →
          1 / 3 ≤ t → t ≤ 1 / 2 → 1 / 3 ≤ u → u ≤ 1 / 2 →
          0 < |t - u| → |t - u| ≤ 1 → Tsh ≤ |t - u| * Real.exp ((r : ℝ) + θ) →
          (∀ mm, mm < N - d →
            |∑ p ∈ primeBlockSub θ mm,
                Real.cos (2 * t * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(mm : ℝ)))) →
          (∀ mm, mm < N - d →
            |∑ p ∈ primeBlockSub θ mm,
                Real.cos (2 * u * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(mm : ℝ)))) →
          (∀ mm, mm < N - d - r →
            boxEnvelope (Bs) mm + boxEnvelope (Bs) (mm + 1)
                + blockWindow mm + blockWindow mm + 36
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (mm + 1)))) →
          (1 : ℝ) ≤ a →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 20 ≤ ((N - d - r : ℕ) : ℝ) →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 8 ≤ ((N - d - r : ℕ) : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
          1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / |t - u|) →
          (r : ℝ) ≤ 2 * Real.log (2 / |t - u|) + 1 → Λ ≤ 4 * ((N - d - r : ℕ) : ℝ) →
            ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) (blockCutoff θ N)
                (shiftLine σ t) (shiftLine σ u) ν)
              (barrierEvent (fun mm ω => ∑ p ∈ primeBlockSub θ mm,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) N
                  (fun j => -a - Bs * j) (fun j => a + j + hf j)
                ∩ barrierEvent (fun mm ω => ∑ p ∈ primeBlockSub θ mm,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ u))) (Y (p : ℕ) ω)) N
                  (fun j => -a - Bs * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * Real.log (2 / |t - u|) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hbound⟩ := exists_measure_barrier_inter_harper_le_rademacher
    Kd Bs hKd hBs
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hB : (0 : ℝ) ≤ Bs := le_trans (blockSlope_pos 125).le hBs
  set K : ℝ := 42 + 2 * Bs + (31 + Bs) / Real.log 2 + 2 * κ
    with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef]
    positivity
  refine ⟨Cst * (4 * (4 / Real.log 2 + 2 * K) ^ 2), Tsh, by positivity, hTsh, ?_⟩
  intro Ω' _ Y ν hY θ σ η a Λ q m N r d t u hf hθ hr1 hrN hη0 hη1 hσtop htl htu hul huu
    hτ0 hτ1 hTshle hosc₁ hosc₂ henvc ha hbig hbig2 hhf hΛ hq0 hq1 hm0 hmΛ hmq ham hr hn3
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hn1 : 1 ≤ N - d - r := by omega
  have hlev : shiftedHeight a Bs hf r ≤ 2 * m + K * Real.log (2 / |t - u|) := by
    have h := shiftedHeight_le_of_le (a := a) (c := Bs) (hf := hf)
      (zero_le_of_blockSlope_le hBs) hτ0 hτ1 hr (hhf r hr1 (by omega))
    have hKL : K * Real.log (2 / |t - u|)
        = (42 + 2 * Bs + (31 + Bs) / Real.log 2)
            * Real.log (2 / |t - u|) + 2 * (κ * Real.log (2 / |t - u|)) := by
      rw [hKdef]
      ring
    linarith [h, ham, hKL]
  have harith := min_one_div_sqrt_sq_le (Λ := Λ) (a := shiftedHeight a Bs hf r)
    (τ := |t - u|) (K := K) (q := q) (m := m) (n := N - d - r)
    hΛ hq0 hq1 hτ0 hτ1 hK0 hn1 hm0 hmΛ hmq
    (le_trans ha0 (le_shiftedHeight (zero_le_of_blockSlope_le hBs) ha0 r hf)) hlev (by norm_num) hn3
  refine le_trans (hbound Ω' Y ν hY θ σ η a N r d t u hf hθ hr1 hrN hη0 hη1 hσtop
    htl htu hul huu hτ0 hτ1 hTshle hosc₁ hosc₂ henvc ha hbig hbig2 hhf) ?_
  calc Cst * min 1 (shiftedHeight a Bs hf r / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2
      ≤ Cst * (4 * (4 / Real.log 2 + 2 * K) ^ 2 * Real.log (2 / |t - u|) ^ 2
          / (1 + (1 - q) * Real.sqrt Λ) ^ 2) := mul_le_mul_of_nonneg_left harith hCst.le
    _ = Cst * (4 * (4 / Real.log 2 + 2 * K) ^ 2) * Real.log (2 / |t - u|) ^ 2
          / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by ring

/-! ### The height integral, for the Rademacher function

The double integral over `T × T` of the pointwise bound, integrated out.  Everything between the
swap and the answer is law-free (`outerEnvelope` and its lemmas, `setIntegral_sub_le_of_subset`,
`integral_outerEnvelope_le`), so only the swap is twinned, and
`RMF.integral_sq_setIntegral_indicator_normSq_sqfree_eq` supplies it. -/

/-- **The height integral, bounded by the envelope's integral.**  The twin of
`RMF.integral_sq_setIntegral_indicator_normSq_le`.  The pointwise bound is a hypothesis: it is what
the three ranges produce, and each carries its own hypothesis list about Harper's data. -/
theorem integral_sq_setIntegral_indicator_normSq_le_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTm : MeasurableSet T)
    (hTsub : T ⊆ Set.Icc (-1 : ℝ) 1) {C Lc D ε : ℝ} (hC : 0 ≤ C) (hLc : 1 ≤ Lc)
    (hD : 0 ≤ D) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hpt : ∀ t ∈ T, ∀ u ∈ T, t ≠ u →
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) y
            (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
          * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ outerEnvelope C Lc D ε |t - u|) :
    (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν)
      ≤ (volume T).toReal * (2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2) := by
  have hTfin : volume T ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono hTsub) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  rw [integral_sq_setIntegral_indicator_normSq_sqfree_eq hY y hσ L hLmeas hSmeas hTfin]
  have hnn : ∀ t u : ℝ, (0 : ℝ) ≤
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) y
            (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
        * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν := fun t u =>
    mul_nonneg ENNReal.toReal_nonneg (integral_nonneg fun ω => by positivity)
  have hinner : ∀ t ∈ T, (∫ u in T,
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) y
            (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
        * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
      ≤ 2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2 := by
    intro t ht
    have hmaj : IntegrableOn (fun u => outerEnvelope C Lc D ε |t - u|) T := by
      refine Measure.integrableOn_of_bounded (M := C * Lc + D / (ε * Real.log 2 ^ 2)) hTfin ?_ ?_
      · exact ((measurable_outerEnvelope C Lc D ε).comp
          ((measurable_const.sub measurable_id).norm)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun u => ?_
        rw [Real.norm_eq_abs,
          abs_of_nonneg (outerEnvelope_nonneg (Lc := Lc) hC (by linarith) hD hε0 _)]
        exact outerEnvelope_le (Lc := Lc) hC hD hε0 _
    calc (∫ u in T,
        (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) y
              (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
          * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ ∫ u in T, outerEnvelope C Lc D ε |t - u| :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => hnn t u) hmaj
            (by
              have hne : ∀ᵐ u : ℝ, u ≠ t := by
                have h0 : (volume ({t} : Set ℝ)) = 0 := by simp
                filter_upwards [compl_mem_ae_iff.2 h0] with u hu
                simpa using hu
              filter_upwards [ae_restrict_mem hTm, ae_restrict_of_ae hne] with u hu hune
              exact hpt t ht u hu (Ne.symm hune))
      _ ≤ ∫ v in Set.Icc (-2 : ℝ) 2, outerEnvelope C Lc D ε |v| :=
          setIntegral_sub_le_of_subset
            (outerEnvelope_nonneg (Lc := Lc) hC (by linarith) hD hε0) hTsub (hTsub ht)
            (integrableOn_outerEnvelope (Lc := Lc) hC (by linarith) hD hε0 (-2 : ℝ) 2)
      _ ≤ 2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2 :=
          integral_outerEnvelope_le hC hLc hD hε0 hε1
  calc (∫ t in T, ∫ u in T,
        (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) y
              (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
          * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν)
      ≤ ∫ _t in T, (2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun t => integral_nonneg fun u => hnn t u)
          (integrableOn_const hTfin)
          ((ae_restrict_iff' hTm).2 (Filter.Eventually.of_forall fun t ht => hinner t ht))
    _ = (volume T).toReal • (2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2) :=
        setIntegral_const _
    _ = (volume T).toReal * (2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2) :=
        smul_eq_mul _ _

/-- **The second moment of the restricted chaos from the ranges, for the Rademacher function**:
`E[X²] ≤ |T|·\big(2C(1+\log 2L_c) + 2D/\log 2\big)`, `X = ∫_T 1_{L t}‖F_t‖²\,dt`, given the two
pointwise bounds the ranges produce: `C\min\{L_c,1/τ\}` on the crude range and `D/(τ\log²(2/τ))`
above it (the middle and far ranges give the same function of `τ`).  The twin of
`RMF.integral_sq_setIntegral_indicator_normSq_le_of_cases`; the law-free
`RMF.le_outerEnvelope_of_cases` does the case split. -/
theorem integral_sq_setIntegral_indicator_normSq_le_of_cases_rademacher {Ω' : Type*}
    [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν)
    (y : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTm : MeasurableSet T)
    (hTsub : T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) {C Lc D ε : ℝ} (hC : 0 ≤ C) (hLc : 1 ≤ Lc)
    (hD : 0 ≤ D) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hcrude : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → |t - u| ≤ ε →
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) y
            (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
          * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ C * min Lc (1 / |t - u|))
    (hout : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ε < |t - u| →
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) y
            (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
          * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ D / (|t - u| * Real.log (2 / |t - u|) ^ 2)) :
    (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν)
      ≤ (volume T).toReal * (2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2) := by
  have hTsub' : T ⊆ Set.Icc (-1 : ℝ) 1 := fun t ht =>
    ⟨by linarith [(hTsub ht).1], by linarith [(hTsub ht).2]⟩
  refine integral_sq_setIntegral_indicator_normSq_le_rademacher hY y hσ L hLmeas hSmeas hTm
    hTsub' hC hLc hD hε0 hε1 ?_
  intro t ht u hu htu
  have hτ0 : 0 < |t - u| := abs_pos.2 (sub_ne_zero.2 htu)
  have hτ1 : |t - u| ≤ 1 := by
    have h1 := hTsub ht
    have h2 := hTsub hu
    rw [abs_le]
    constructor
    · linarith [h1.1, h2.2]
    · linarith [h1.2, h2.1]
  exact le_outerEnvelope_of_cases hC (by linarith) hD hε0 hτ0 hτ1
    (fun h => hcrude t ht u hu htu h) (fun h => hout t ht u hu htu h)

end RMF
