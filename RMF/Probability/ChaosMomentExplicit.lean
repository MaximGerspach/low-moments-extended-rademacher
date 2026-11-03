/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ChaosMoment
import RMF.Probability.ChaosFirstMomentExplicit
import RMF.Probability.MaximalBarrierExplicit
import RMF.Probability.MaximalBarrierSharp
import RMF.Probability.SharpNumerals
import RMF.Probability.ChaosMomentShift

/-!
# The chaos moments with their constants named

Explicit constants for the good sets of `RMF/Probability/ChaosMoment.lean`, as Harper's upper
bound uses them:

* `RMF.harperGoodDeficit E₀ = 1 + 45√E₀ + 120e² + blockRangeSumConst`, a barrier deficit of the
  shape the main file's proof uses, and `RMF.harperSharpDeficit E₀ = 1 + 45√E₀`, the part of it
  the sharp form of Hamdan's Lemma 2.3 (`RMF/Probability/MaximalBarrierSharp.lean`) pays for;
* `RMF.harperGoodLevel` and `RMF.harperBadLevel`, levels built from the sharp Lemma 2.3's level
  `indexSharpLevel (harperSharpDeficit E₀) 0`;
* `RMF.harperGoodSlopeOf`, the good set at log-slope `β`, and
  `RMF.measureReal_not_harperGoodSlopeOf_le_of_harperThreshold`, its bad sets at the level
  `RMF.harperBadLevel E₀` and the constant `RMF.harperGoodBadConstOf E₀ β`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The barrier deficit `1 + 45√E₀ + 120e² + blockRangeSumConst`: the deficit
`Δ = 1 + 45√E₀ + 120e² + C` of the proof of `RMF.exists_const_harperGood_bounds_of_scale`, at
`C = blockRangeSumConst`. -/
noncomputable def harperGoodDeficit (E₀ : ℝ) : ℝ :=
  1 + 45 * √E₀ + 120 * Real.exp 2 + blockRangeSumConst

/-- The variance deficit the sharp Lemma 2.3 pays for, `1 + 45√E₀`: the barrier's block sums are
within `45√E₀ + 120e²e^{-(1+ϑ)} ≤ 45√E₀ + 1` of the index once `ϑ ≥ 16`. -/
noncomputable def harperSharpDeficit (E₀ : ℝ) : ℝ := 1 + 45 * √E₀

/-- `max{restrictedChaosLevel E₀, 1, 4·indexSharpLevel (harperSharpDeficit E₀) 0}`: the larger of
the restricted chaos's level and `RMF.harperBadLevel E₀`, which takes the sharp Lemma 2.3's level
at excess `0` (no excess in Mertens' first theorem over the block range,
`RMF.sum_primesIco_rpow_log_le_exp`). -/
noncomputable def harperGoodLevel (E₀ : ℝ) : ℝ :=
  max (max (restrictedChaosLevel E₀) 1)
    (4 * indexSharpLevel (harperSharpDeficit E₀) 0)

/-- The level of the good set's bad sets alone,
`max{1, 4·indexSharpLevel (harperSharpDeficit E₀) 0}`
(`RMF.measureReal_not_harperGoodSlopeOf_le_of_harperThreshold`): `RMF.harperGoodLevel` without
the restricted chaos's level.  It is `32` at `E₀ = 0`. -/
noncomputable def harperBadLevel (E₀ : ℝ) : ℝ :=
  max 1 (4 * indexSharpLevel (harperSharpDeficit E₀) 0)

/-- The block offset is at least `17`: `RMF.prop5UpperThreshold` is at least `16`. -/
lemma le_freeStartHarperD (E₀ : ℝ) : 17 ≤ freeStartHarperD E₀ := by
  have hc : (16 : ℕ) ≤ ⌈prop5UpperThreshold E₀⌉₊ := by
    have := le_trans (sixteen_le_prop5UpperThreshold E₀) (Nat.le_ceil (prop5UpperThreshold E₀))
    exact_mod_cast this
  unfold freeStartHarperD
  omega

/-- **Mertens' first theorem over the block range, with no excess**: for `ϑ ≥ 3` and `δ ≥ 0`,
`∑_{x_0 < p ≤ x_j} p^{-(1+2δ)} log p ≤ e^{j+ϑ}`.  The sum up to `x_j` is at most
`log x_j + log 4 + 4` and the sum up to `x_0` at least `log x_0 - log 4 - 4`
(`Mertens.sum_log_prime_div_eq_log`), and `log x_0 = e^ϑ ≥ 2(log 4 + 4)`, so no excess
`blockRangeSumConst` is needed. -/
lemma sum_primesIco_rpow_log_le_exp {ϑ δ : ℝ} (hϑ : 3 ≤ ϑ) (hδ : 0 ≤ δ) (j : ℕ) :
    (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Real.exp ((j : ℝ) + ϑ) := by
  have hset : ∀ N : ℕ, Nat.primesBelow (N + 1) = {p ∈ Finset.Ioc 0 N | p.Prime} := by
    intro N
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h2.pos, by omega⟩, h2⟩
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨by omega, h3⟩
  -- Mertens' first theorem at the block scales
  have hM : ∀ k : ℕ, |(∑ p ∈ Nat.primesBelow (⌊blockScale ϑ k⌋₊ + 1), Real.log p / p)
      - Real.exp ((k : ℝ) + ϑ)| ≤ Real.log 4 + 4 := by
    intro k
    have hx1 : (1 : ℝ) ≤ blockScale ϑ k := Real.one_le_exp (Real.exp_pos _).le
    have h := Mertens.sum_log_prime_div_eq_log hx1
    rw [← hset, log_blockScale] at h
    exact h
  -- the range as a difference
  have hmono : ⌊blockScale ϑ 0⌋₊ + 1 ≤ ⌊blockScale ϑ j⌋₊ + 1 := by
    have := Nat.floor_le_floor (blockScale_mono ϑ (Nat.zero_le j))
    omega
  have hsub : Nat.primesBelow (⌊blockScale ϑ 0⌋₊ + 1) ⊆ Nat.primesBelow (⌊blockScale ϑ j⌋₊ + 1) :=
    primesBelow_mono hmono
  have hsplit : (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        Real.log p / p)
      = (∑ p ∈ Nat.primesBelow (⌊blockScale ϑ j⌋₊ + 1), Real.log p / p)
        - ∑ p ∈ Nat.primesBelow (⌊blockScale ϑ 0⌋₊ + 1), Real.log p / p := by
    simp only [primesIco]
    rw [eq_sub_iff_add_eq]
    exact Finset.sum_sdiff hsub
  -- termwise, `p^{-(1+2δ)} log p ≤ log p/p`
  have hterm : (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p)
      ≤ ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1), Real.log p / p := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp : Nat.Prime p := prime_of_mem_primesIco hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    have hlog : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1
    have hrp : ((p : ℝ)) ^ (-2 * (1 / 2 + δ)) ≤ ((p : ℝ)) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    rw [Real.rpow_neg_one] at hrp
    calc ((p : ℝ)) ^ (-2 * (1 / 2 + δ)) * Real.log p ≤ ((p : ℝ))⁻¹ * Real.log p :=
          mul_le_mul_of_nonneg_right hrp hlog
      _ = Real.log p / p := by ring
  -- `e^ϑ ≥ e³ ≥ 19 ≥ 2(log 4 + 4)`
  have he3 : (19 : ℝ) ≤ Real.exp ϑ := by
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h19 : (19 : ℝ) ≤ Real.exp ((3 : ℕ) : ℝ) :=
      le_exp_natCast_of_le_pow (c := 2.7) (k := 3) (by norm_num) he (by norm_num)
    have h3 : Real.exp ((3 : ℕ) : ℝ) ≤ Real.exp ϑ := Real.exp_le_exp.2 (by push_cast; linarith)
    linarith
  have hlog4 : Real.log 4 ≤ 1.3863 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    rw [h4]
    linarith [Real.log_two_lt_d9]
  have hj := abs_le.1 (hM j)
  have h0 := abs_le.1 (hM 0)
  push_cast at h0
  rw [zero_add] at h0
  rw [hsplit] at hterm
  linarith [hj.2, h0.1]

/-- **The good set at level `a`, barrier slope `c` and log-slope `β`**: the tube is
`[-a - c·j, a + j + β log j]`; `RMF.harperGoodSlope` is the case `β = 2`. -/
def harperGoodSlopeOf {Ω' : Type*} (β : ℝ) (Y : ℕ → Ω' → ℂ) (c : ℝ) (D : ℕ) (x δ a t : ℝ) :
    Set Ω' :=
  {ω | ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ harperBlockCount D x →
    walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine δ t))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
      ∈ Set.Icc (-a - c * (j : ℝ)) (a + (j : ℝ) + β * Real.log j)}

lemma mem_harperGoodSlopeOf {Ω' : Type*} {β : ℝ} {Y : ℕ → Ω' → ℂ} {c : ℝ} {D : ℕ} {x δ a t : ℝ}
    {ω : Ω'} :
    ω ∈ harperGoodSlopeOf β Y c D x δ a t ↔ ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ harperBlockCount D x →
      walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
        localLog (((p : ℕ) : ℂ) ^ (-(shiftLine δ t))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
        ∈ Set.Icc (-a - c * (j : ℝ)) (a + (j : ℝ) + β * Real.log j) := Iff.rfl

/-- It is measurable, at any slopes. -/
lemma measurableSet_harperGoodSlopeOf {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (β c : ℝ) (D : ℕ) (x δ a t : ℝ) :
    MeasurableSet (harperGoodSlopeOf β Y c D x δ a t) :=
  measurableSet_freeStartBarrier (fun _ => Finset.measurable_sum _ fun p _ =>
    (measurable_localLog _).comp (hY.measurable ((p : Nat.Primes) : ℕ) p.2)) _ _ _ _

/-- And so is its uncurried form, which the `t`-integral needs. -/
lemma measurableSet_harperGoodSlopeOf_uncurry {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (β c : ℝ) (D : ℕ)
    (x δ a : ℝ) :
    MeasurableSet {q : Ω' × ℝ | q.1 ∈ harperGoodSlopeOf β Y c D x δ a q.2} :=
  measurableSet_freeStartBarrier_uncurry
    (fun p => hY.measurable ((p : Nat.Primes) : ℕ) p.2) δ _ _ _ _ _

/-- **The envelope sum at log-slope `β > 1/2` converges**, uniformly in the range:
`Σ_{i=r}^n e^{-2β log i} ≤ Σ_i i^{-2β}` (`RMF.sum_exp_neg_envelope_le` is `β = 2`). -/
lemma sum_exp_neg_envelope_le_of {β : ℝ} (hβ : 1 / 2 < β) {r n : ℕ} (hr : 1 ≤ r) :
    ∑ i ∈ Finset.Icc r n, Real.exp (-(2 * (β * Real.log i)))
      ≤ ∑' i : ℕ, (i : ℝ) ^ (-(2 * β)) := by
  have hterm : ∀ i ∈ Finset.Icc r n,
      Real.exp (-(2 * (β * Real.log i))) = (i : ℝ) ^ (-(2 * β)) := by
    intro i hi
    have hi1 : 1 ≤ i := le_trans hr (Finset.mem_Icc.1 hi).1
    have hipos : (0 : ℝ) < i := by exact_mod_cast hi1
    rw [Real.rpow_def_of_pos hipos]
    congr 1
    ring
  rw [Finset.sum_congr rfl hterm]
  exact Summable.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
    (Real.summable_nat_rpow.mpr (by linarith))

/-- The envelope at log-slope `β ∈ [0, 2]` is admissible for Hamdan's Lemma 2.3:
`β log i ≤ 2 log i ≤ i` once `i ≥ 1` (`RMF.two_log_le_self`). -/
lemma mul_log_le_self {β : ℝ} (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) {i : ℕ} (hi : 1 ≤ i) :
    β * Real.log i ≤ (i : ℝ) := by
  have h0 : 0 ≤ Real.log i := Real.log_natCast_nonneg i
  have h := two_log_le_self hi
  nlinarith

/-- **The constant of the bad sets at log-slope `β`**: `indexSharpConst Δ·e^D·Σ_i i^{-2β}` with
`Δ = harperSharpDeficit E₀` and `D = freeStartHarperD E₀`. -/
noncomputable def harperGoodBadConstOf (E₀ β : ℝ) : ℝ :=
  indexSharpConst (harperSharpDeficit E₀) * Real.exp (freeStartHarperD E₀)
    * ∑' i : ℕ, (i : ℝ) ^ (-(2 * β))

lemma harperGoodBadConstOf_pos (E₀ : ℝ) {β : ℝ} (hβ : 1 / 2 < β) :
    0 < harperGoodBadConstOf E₀ β := by
  have hs : Summable fun i : ℕ => (i : ℝ) ^ (-(2 * β)) :=
    Real.summable_nat_rpow.2 (by linarith)
  have h1 : (1 : ℝ) ≤ ∑' i : ℕ, (i : ℝ) ^ (-(2 * β)) := by
    have h := hs.le_tsum 1 (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
    simpa using h
  have := indexSharpConst_pos (harperSharpDeficit E₀)
  unfold harperGoodBadConstOf
  positivity

/-- **The good set's bad sets at log-slope `β ∈ (1/2, 2]`, at the level `RMF.harperBadLevel E₀`**:
for `a ≥ harperBadLevel E₀` and `log log x ≥ D` (`x ≥ harperThreshold D 0`,
`D = freeStartHarperD E₀`), `P(∃ h ∈ [0,1) : ω ∉ G_a(h)) ≤ harperGoodBadConstOf E₀ β·e^{-2a}`, the
union over the blocks costing `Σ_j j^{-2β}`.  The sharp Lemma 2.3
(`RMF.IsSteinhausPrimeValues.measure_exists_barrier_le_of_le_sharp`) at the deficit
`harperSharpDeficit E₀` and no excess (`RMF.sum_primesIco_rpow_log_le_exp`).  It needs `ϑ ≥ 16`
twice: for `120e²e^{-(1+ϑ)} ≤ 1`, and for the first block to start past
`chainSharpThreshold (1/2) 7`.  Neither the restricted chaos's level nor a block count plays a
part. -/
theorem measureReal_not_harperGoodSlopeOf_le_of_harperThreshold (E₀ β : ℝ) (hβ : 1 / 2 < β)
    (hβ2 : β ≤ 2) :
    ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
      ∀ x δ η a : ℝ, harperThreshold (freeStartHarperD E₀) 0 ≤ x → 0 ≤ δ → 0 ≤ η → η ≤ E₀ →
        |δ| * Real.log x ≤ η → (harperBadLevel E₀) ≤ a →
        ν.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
            ω ∉ harperGoodSlopeOf β Y prop5UpperSlope (freeStartHarperD E₀) x δ a h}
          ≤ (harperGoodBadConstOf E₀ β) * Real.exp (-(2 * a)) := by
  have hD : 4 ≤ freeStartHarperD E₀ := by
    have := le_freeStartHarperD E₀
    omega
  set D := freeStartHarperD E₀ with hD_expl
  have hx₂ := exists_harperThreshold_of_blockCount_explicit D 0
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ, Δ = 1 + 45 * √E₀ := ⟨_, rfl⟩
  have hΔ1 : (1 : ℝ) ≤ Δ := by
    rw [hΔdef]
    linarith [Real.sqrt_nonneg E₀]
  have hC₂ : 0 < indexSharpConst Δ := indexSharpConst_pos Δ
  set C₂ := indexSharpConst Δ with hC₂_expl
  set Lv := indexSharpLevel Δ 0 with hLv_expl
  have hWa : harperBadLevel E₀ = max 1 (4 * Lv) := by
    unfold harperBadLevel harperSharpDeficit
    rw [← hΔdef]
  have hWB : harperGoodBadConstOf E₀ β = C₂ * Real.exp D * ∑' i : ℕ, (i : ℝ) ^ (-(2 * β)) := by
    unfold harperGoodBadConstOf harperSharpDeficit
    rw [← hΔdef]
  rw [hWa, hWB]
  intro Y ν hY x δ η a hx hδ0 hη0 hηE hδx ha
  obtain ⟨hx1, hDlog, -⟩ := hx₂ x hx
  have hD4 : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hϑ3 : (3 : ℝ) ≤ harperOffset D x := by linarith [sub_one_le_harperOffset D x]
  have hϑ16 : (16 : ℝ) ≤ harperOffset D x := by
    have hD17 : (17 : ℝ) ≤ (D : ℝ) := by exact_mod_cast le_freeStartHarperD E₀
    linarith [sub_one_le_harperOffset D x]
  have hδtop : |δ| * Real.log (blockScale (harperOffset D x)
      (harperBlockCount D x + 1)) ≤ η := by
    rw [log_blockScale_harperOffset_top hx1 hDlog]
    exact hδx
  have hps : ∀ j, j ≤ harperBlockCount D x →
      |(∑ p ∈ primesIco (⌊blockScale (harperOffset D x) 0⌋₊ + 1)
          (⌊blockScale (harperOffset D x) j⌋₊ + 1), (p : ℝ) ^ (-2 * (1 / 2 + δ))) - (j : ℝ)|
        ≤ 45 * √η + 120 * Real.exp 2 * Real.exp (-(1 + harperOffset D x)) := fun j hj =>
    abs_sum_primesIco_rpow_sub_le_of_le' hϑ3 (by omega) hη0 hδ0 hδtop
  have hpsΔ : ∀ j, j ≤ harperBlockCount D x →
      |(∑ p ∈ primesIco (⌊blockScale (harperOffset D x) 0⌋₊ + 1)
          (⌊blockScale (harperOffset D x) j⌋₊ + 1), (p : ℝ) ^ (-2 * (1 / 2 + δ))) - (j : ℝ)|
        ≤ Δ := by
    intro j hj
    refine le_trans (hps j hj) ?_
    have hsmall : 120 * Real.exp 2 * Real.exp (-(1 + harperOffset D x)) ≤ 1 := by
      have h1 : Real.exp 2 * Real.exp (-(1 + harperOffset D x))
          * Real.exp (harperOffset D x - 1) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        simp only [show 2 + -(1 + harperOffset D x) + (harperOffset D x - 1) = 0 by ring,
          Real.exp_zero]
      have h2 : (120 : ℝ) ≤ Real.exp (harperOffset D x - 1) := by
        have ht : (15 : ℝ) ≤ harperOffset D x - 1 := by linarith
        have hq := Real.quadratic_le_exp_of_nonneg (x := harperOffset D x - 1) (by linarith)
        have ht2 : (225 : ℝ) ≤ (harperOffset D x - 1) ^ 2 := by
          have h := mul_le_mul ht ht (by norm_num) (by linarith)
          calc (225 : ℝ) = 15 * 15 := by norm_num
            _ ≤ (harperOffset D x - 1) * (harperOffset D x - 1) := h
            _ = (harperOffset D x - 1) ^ 2 := by ring
        linarith
      have h3 : (0 : ℝ) ≤ Real.exp 2 * Real.exp (-(1 + harperOffset D x)) := by positivity
      nlinarith
    have hsq : √η ≤ √E₀ := Real.sqrt_le_sqrt hηE
    rw [hΔdef]
    linarith
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_left _ _) ha
  have haC₂ : 4 * Lv ≤ a := le_trans (le_max_right _ _) ha
  have ha4 : (0 : ℝ) ≤ a / 4 := by linarith
  have hr1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
  have hrge : a / 4 ≤ (⌈a / 4⌉₊ : ℝ) := Nat.le_ceil _
  have hCr : Lv ≤ ((⌈a / 4⌉₊ : ℕ) : ℝ) := by linarith
  have h4 : ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ harperBlockCount D x → a ≤ 4 * (j : ℝ) := by
    intro j hj _
    have : ((⌈a / 4⌉₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have hlog : ∀ j, ⌈a / 4⌉₊ ≤ j → (0 : ℝ) ≤ Real.log j := by
    intro j hj
    exact Real.log_nonneg (by exact_mod_cast le_trans hr1 hj)
  -- the barrier
  have hϑ : (1 : ℝ) ≤ harperOffset D x := by
    have hD2 : (2 : ℕ) ≤ D := by omega
    have hD' : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD2
    linarith [sub_one_le_harperOffset D x]
  have hϑ₀ : chainSharpThreshold (1 / 2) 7
      ≤ ((⌊blockScale (harperOffset D x) 0⌋₊ + 1 : ℕ) : ℝ) := by
    have hbs : Real.exp (Real.exp 16) ≤ blockScale (harperOffset D x) 0 := by
      unfold blockScale
      exact Real.exp_le_exp.2 (Real.exp_le_exp.2 (by push_cast; linarith))
    have hfl := Nat.lt_floor_add_one (blockScale (harperOffset D x) 0)
    have ht := chainSharpThreshold_le_exp_exp_sixteen
    push_cast
    linarith
  have hbar := hY.measure_exists_barrier_le_of_le_sharp (A := a) (c := prop5UpperSlope)
    (r := ⌈a / 4⌉₊) (n := harperBlockCount D x) (b := fun j => β * Real.log j) hΔ1 hϑ hϑ₀
    (by linarith) twenty_le_prop5UpperSlope hδ0 hCr
    (fun j hj _ => mul_nonneg (by linarith) (hlog j hj))
    (fun j hj _ => mul_log_le_self (by linarith) hβ2 (le_trans hr1 hj)) h4
    (fun j _ hjn => by linarith [(abs_le.1 (hpsΔ j hjn)).2])
    (fun j _ hjn => by linarith [(abs_le.1 (hpsΔ j hjn)).1])
    (fun j _ _ => by rw [add_zero]; exact sum_primesIco_rpow_log_le_exp hϑ3 hδ0 _)
  have hset : {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
      ω ∉ harperGoodSlopeOf β Y prop5UpperSlope D x δ a h}
      = {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ harperBlockCount D x →
          walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
            localLog (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (Y (p : ℕ) ω)) j ω
            ∈ Set.Icc (-a - prop5UpperSlope * (j : ℝ))
              (a + (j : ℝ) + (fun j => β * Real.log j) j)} := by
    ext ω
    simp only [Set.mem_setOf_eq, mem_harperGoodSlopeOf, heightLine_eq_shiftLine]
  rw [hset]
  refine le_trans hbar ?_
  have hsum := sum_exp_neg_envelope_le_of hβ (r := ⌈a / 4⌉₊) (n := harperBlockCount D x) hr1
  have hexpϑ : Real.exp (harperOffset D x) ≤ Real.exp D :=
    Real.exp_le_exp.2 (harperOffset_lt_natCast D x).le
  have h2 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc ⌈a / 4⌉₊ (harperBlockCount D x),
      Real.exp (-(2 * (β * Real.log j))) :=
    Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
  have hA : C₂ * Real.exp (harperOffset D x) * Real.exp (-(2 * a))
      ≤ C₂ * Real.exp D * Real.exp (-(2 * a)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexpϑ hC₂.le)
      (Real.exp_pos _).le
  calc C₂ * Real.exp (harperOffset D x) * Real.exp (-(2 * a))
        * ∑ j ∈ Finset.Icc ⌈a / 4⌉₊ (harperBlockCount D x),
            Real.exp (-(2 * (β * Real.log j)))
      ≤ C₂ * Real.exp D * Real.exp (-(2 * a)) * ∑' i : ℕ, (i : ℝ) ^ (-(2 * β)) :=
        mul_le_mul hA hsum h2 (by positivity)
    _ = C₂ * Real.exp D * (∑' i : ℕ, (i : ℝ) ^ (-(2 * β))) * Real.exp (-(2 * a)) := by ring

end RMF
