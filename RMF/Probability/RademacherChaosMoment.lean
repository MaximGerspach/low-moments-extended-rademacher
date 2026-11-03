/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherBarrier
import RMF.Probability.RademacherChaosFirstMoment
import RMF.Probability.ChaosMoment

/-!
# The good set for the squarefree product, and the Rademacher `q`-th moment

The Rademacher counterparts of `Probability/ChaosMoment.lean`: the good set, its two bounds, and
the interpolation of Soundararajan and Zaman (as in Hamdan's proof of his Proposition 1.2) for the
chaos of the Rademacher random multiplicative function.

## One definition

This file defines a single good set, `RMF.harperGoodRangeAdd`, which differs from the Steinhaus
`RMF.harperGoodRange` only in using `localLogAdd` for `localLog`.

## `D` varies with the height

Harper's Proposition 6, the Rademacher barrier estimate, needs the block offset to grow as the
height tends to `0`, so the good sets here are read at `D = RMF.harperDt D₀ h`; at height `h` the
set is `harperGoodRangeAdd Y c (harperDt D₀ h) x δ a (harperBlockCount (harperDt D₀ h) x) h`.
The barrier bound is summed over the bands `[e^{-k}, e^{-(k-1)})` on which `harperDt D₀` is
constant, and read at level `a + k` on band `k` so that the bands sum a geometric series.

## Main results

* `RMF.exists_const_harperGoodRangeAdd_bounds_of_scale_rademacher_raise_of_top`: both bounds
  at the raised level with the top `d` blocks dropped, the constants independent of `E₀` and `d`.
* `RMF.exists_const_integral_chaosUnitShift_rpow_le_rademacher_of_top`,
  `RMF.exists_const_integral_chaosUnitShift_rpow_le_rademacher` and
  `RMF.exists_const_integral_chaosUnitShift_rpow_le_loglog_rademacher`: the `q`-th moment bound.

The measurability lemmas take `∀ p, Measurable (Y p)` rather than a law, which is all their proofs
use; a caller holding `IsRademacherPrimeValues Y ν` supplies it as `fun p => hY.measurable _ p.2`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-- **The good set for the squarefree product**: the `ω` whose `localLogAdd` block walk at
`1/2 + δ + ih`, with offset `RMF.harperOffset D x`, stays in the tube
`[-a - c·j, a + j + 2ℓog j]` for every block `j` from `⌈a/4⌉₊` to `t`.  The `localLogAdd`
counterpart of `RMF.harperGoodRange`. -/
def harperGoodRangeAdd {Ω' : Type*} (Y : ℕ → Ω' → ℂ) (c : ℝ) (D : ℕ) (x δ a : ℝ) (t : ℕ)
    (h : ℝ) : Set Ω' :=
  {ω | ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ t →
    walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine δ h))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
      ∈ Set.Icc (-a - c * (j : ℝ)) (a + (j : ℝ) + 2 * Real.log j)}

lemma mem_harperGoodRangeAdd {Ω' : Type*} {Y : ℕ → Ω' → ℂ} {c : ℝ} {D : ℕ} {x δ a : ℝ} {t : ℕ}
    {h : ℝ} {ω : Ω'} :
    ω ∈ harperGoodRangeAdd Y c D x δ a t h ↔ ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ t →
      walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine δ h))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
        ∈ Set.Icc (-a - c * (j : ℝ)) (a + (j : ℝ) + 2 * Real.log j) := Iff.rfl

/-- **It grows as the range shrinks.**  The condition is `∀ j ≤ t`, so a shorter range is a
weaker requirement and a larger set — which is why dropping blocks from the top makes the
complement *smaller* and its measure bound survive unchanged. -/
lemma harperGoodRangeAdd_subset_of_le {Ω' : Type*} {Y : ℕ → Ω' → ℂ} {c : ℝ} {D : ℕ}
    {x δ a : ℝ} {t t' : ℕ} {h : ℝ} (htt : t' ≤ t) :
    harperGoodRangeAdd Y c D x δ a t h ⊆ harperGoodRangeAdd Y c D x δ a t' h :=
  fun _ hω j hj1 hj2 => hω j hj1 (le_trans hj2 htt)

/-- It is measurable, at any slope, block parameter and range.

`RMF.measurableSet_freeStartBarrier` is stated over an abstract real walk and is reused verbatim;
only `RMF.measurable_localLogAdd` replaces `measurable_localLog`. -/
lemma measurableSet_harperGoodRangeAdd {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    (hY : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ))) (c : ℝ) (D : ℕ)
    (x δ a : ℝ) (t : ℕ) (h : ℝ) :
    MeasurableSet (harperGoodRangeAdd Y c D x δ a t h) :=
  measurableSet_freeStartBarrier (fun _ => Finset.measurable_sum _ fun p _ =>
    (measurable_localLogAdd _).comp (hY p)) _ _ _ _

/-- And so is its uncurried form, which the `t`-integral's Tonelli step needs.  This is
`RMF.measurableSet_freeStartBarrierAdd_uncurry`, which takes the measurability rather than a law. -/
lemma measurableSet_harperGoodRangeAdd_uncurry {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} (hY : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)))
    (c : ℝ) (D : ℕ) (x δ a : ℝ) (t : ℕ) :
    MeasurableSet {q : Ω' × ℝ | q.1 ∈ harperGoodRangeAdd Y c D x δ a t q.2} :=
  measurableSet_freeStartBarrierAdd_uncurry hY δ _ _ _ _ _

/-- **The raised-level family is jointly measurable**: at height `h` the level is
`a + (harperDt D₀ h - D₀)`, so the start `⌈·/4⌉₊` and the tube move with `h`, and the range is
`harperBlockCount (harperDt D₀ h) x - k`.  This is the `measurableSet_uncurry` field of
`RMF.GoodFamilyAdd` for that family, an instance of
`RMF.measurableSet_freeStartBarrierAdd_uncurry_harperDt_raise` (which splits over the fibres of
`RMF.harperDt`); the `measurableSet` field is `RMF.measurableSet_harperGoodRangeAdd`. -/
lemma measurableSet_harperGoodRangeAdd_raise_uncurry {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} (hY : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)))
    (c δ x a : ℝ) (D₀ k : ℕ) :
    MeasurableSet {q : Ω' × ℝ | q.1 ∈ harperGoodRangeAdd Y c (harperDt D₀ q.2) x δ
      (a + ((harperDt D₀ q.2 - D₀ : ℕ) : ℝ))
      (harperBlockCount (harperDt D₀ q.2) x - k) q.2} :=
  measurableSet_freeStartBarrierAdd_uncurry_harperDt_raise hY δ x D₀ k
    (fun D => ⌈(a + ((D - D₀ : ℕ) : ℝ)) / 4⌉₊)
    (fun D j => -(a + ((D - D₀ : ℕ) : ℝ)) - c * (j : ℝ))
    (fun D j => a + ((D - D₀ : ℕ) : ℝ) + (j : ℝ) + 2 * Real.log j)

/-! ### Tiling `(0,1)` by bands, and the bands that cost nothing

The two ingredients the band summation needs.  Together they say: every height in `(0,1)` lies in
some band `k ≥ 1`, and every band past the block count's death contributes **nothing at all** —
so the sum over `k` is finite, with at most `⌊ℓogℓog x⌋₊` live terms.
-/

/-- **A good range with no blocks is everything**, at any block count, not only at
`RMF.harperBlockCount`.  The general form of
`RMF.harperGoodRangeAdd_eq_univ_of_blockCount_zero`, which the `_of_top` ladder needs because
its count is `RMF.harperBlockCount D x - d`: the condition ranges over `[⌈a/4⌉, 0]`, and
`⌈a/4⌉ ≥ 1`. -/
lemma harperGoodRangeAdd_eq_univ_of_zero {Ω' : Type*} {Y : ℕ → Ω' → ℂ} {c : ℝ}
    {D : ℕ} {x δ a h : ℝ} {t : ℕ} (hr : 1 ≤ ⌈a / 4⌉₊) (hdead : t = 0) :
    harperGoodRangeAdd Y c D x δ a t h = Set.univ := by
  subst hdead
  ext ω
  simp only [mem_harperGoodRangeAdd, Set.mem_univ, iff_true]
  intro j hj1 hj2
  omega

/-- **A band past the block count's death is free.**  `RMF.harperBlockCount` is `ℕ`-truncated, so
once `D` is large enough it is `0`; the index range `[⌈a/4⌉₊, 0]` is then empty, the good set is
everything, and the band's bad set is empty.  This truncation is what makes the band sum finite. -/
lemma harperGoodRangeAdd_eq_univ_of_blockCount_zero {Ω' : Type*} {Y : ℕ → Ω' → ℂ} {c : ℝ}
    {D : ℕ} {x δ a h : ℝ} (hr : 1 ≤ ⌈a / 4⌉₊) (hdead : harperBlockCount D x = 0) :
    harperGoodRangeAdd Y c D x δ a (harperBlockCount D x) h = Set.univ := by
  rw [hdead]
  ext ω
  simp only [mem_harperGoodRangeAdd, Set.mem_univ, iff_true]
  intro j hj1 hj2
  omega

/-- **Every height in `(0,1)` lies in a band with `k ≥ 1`.**

`RMF.harperDt D₀ h = D₀ + ⌈ℓog(1/|h|)⌉₊`, and on `(0,1)` that ceiling is at least one.  With
`RMF.harperDt_eq_add_iff` this is what tiles `(0,1)` by the bands `[e^{−k}, e^{−(k−1)})`. -/
lemma exists_harperDt_eq_add_of_mem_Ioo {D₀ : ℕ} {h : ℝ} (hh : h ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ k : ℕ, 1 ≤ k ∧ harperDt D₀ h = D₀ + k := by
  refine ⟨⌈Real.log (1 / |h|)⌉₊, ?_, rfl⟩
  have h0 : (0 : ℝ) < h := hh.1
  have habs : |h| = h := abs_of_pos h0
  have hinv : (1 : ℝ) < 1 / |h| := by
    rw [habs, lt_div_iff₀ h0]
    linarith [hh.2]
  exact Nat.ceil_pos.2 (Real.log_pos hinv)

/-! ### The barrier bound at a shifted abscissa

The `δ`-carrying forms, in the shape of `RMF.exists_const_harperGood_bounds_of_scale`. -/

/-- **The barrier bound at a shifted abscissa, on an arbitrary window**, with `D` universally
quantified and `e^D` explicit.  The three prime-sum hypotheses of
`RMF.IsRademacherPrimeValues.exists_const_measure_exists_barrier_le_of_le` are discharged by
`RMF.abs_sum_primesIco_rpow_sub_le_of_le'` and `RMF.exists_const_sum_primesIco_rpow_log_le`, with
deficit `Δ = 1 + 45√E₀ + 120e² + C`; the tilt hypothesis `|δ|·ℓog x ≤ η` is `D`-free. -/
theorem exists_const_measureReal_notMem_harperGoodRangeAdd_of_le {Ω' : Type*}
    [MeasurableSpace Ω'] (E₀ : ℝ) (_hE₀ : 0 ≤ E₀) :
    ∃ a₀ C : ℝ, 0 < C ∧
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (D : ℕ) (x δ η a c h₀ w : ℝ), 4 ≤ D → 1 < x →
          (D : ℝ) ≤ Real.log (Real.log x) →
          0 ≤ δ → 0 ≤ η → η ≤ E₀ → |δ| * Real.log x ≤ η → a₀ ≤ a → 20 ≤ c →
          Real.exp (-((⌈a / 4⌉₊ : ℝ) + harperOffset D x)) ≤ w →
            ν.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w),
                ω ∉ harperGoodRangeAdd Y c D x δ a (harperBlockCount D x) h}
              ≤ C * Real.exp D * w * Real.exp (-(2 * a)) := by
  obtain ⟨Clog, hClog, hlogsum⟩ := exists_const_sum_primesIco_rpow_log_le
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ, Δ = 1 + 45 * √E₀ + 120 * Real.exp 2 + Clog := ⟨_, rfl⟩
  have hΔ1 : (1 : ℝ) ≤ Δ := by
    rw [hΔdef]
    have := Real.exp_pos (2 : ℝ)
    linarith [Real.sqrt_nonneg E₀]
  obtain ⟨C₂, hC₂, H⟩ :=
    IsRademacherPrimeValues.exists_const_measure_exists_barrier_le_of_le (Ω := Ω') Δ hΔ1
  have hζ40 : (0 : ℝ) ≤ ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ) :=
    tsum_nonneg fun i => Real.rpow_nonneg (Nat.cast_nonneg i) _
  have hClogΔ : Clog ≤ Δ := by
    rw [hΔdef]
    linarith [Real.sqrt_nonneg E₀, Real.exp_pos (2 : ℝ)]
  refine ⟨max 1 (4 * C₂), C₂ * (1 + ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ)),
    mul_pos hC₂ (by linarith), ?_⟩
  intro Y ν hY D x δ η a c h₀ w hD hx1 hxD hδ0 hη0 hηE hδx ha hc hw
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_left _ _) ha
  have haC₂ : 4 * C₂ ≤ a := le_trans (le_max_right _ _) ha
  have ha4 : (0 : ℝ) ≤ a / 4 := by linarith
  have hr1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
  have hrge : a / 4 ≤ (⌈a / 4⌉₊ : ℝ) := Nat.le_ceil _
  have hCr : C₂ ≤ ((⌈a / 4⌉₊ : ℕ) : ℝ) := by linarith
  have hD' : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hϑ3 : (3 : ℝ) ≤ harperOffset D x := by linarith [sub_one_le_harperOffset D x]
  have hϑ : (1 : ℝ) ≤ harperOffset D x := by linarith
  have hlog : ∀ j, ⌈a / 4⌉₊ ≤ j → (0 : ℝ) ≤ Real.log j := fun j hj =>
    Real.log_nonneg (by exact_mod_cast le_trans hr1 hj)
  have h4 : ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ harperBlockCount D x → a ≤ 4 * (j : ℝ) := by
    intro j hj _
    have hjr : ((⌈a / 4⌉₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  -- the tilt hypothesis, in the form the discharge lemma wants
  have hδtop : |δ| * Real.log (blockScale (harperOffset D x)
      (harperBlockCount D x + 1)) ≤ η := by
    rw [log_blockScale_harperOffset_top hx1 hxD]
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
    have h1 : Real.exp (-(1 + harperOffset D x)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
    have hsq : √η ≤ √E₀ := Real.sqrt_le_sqrt hηE
    rw [hΔdef]
    nlinarith [hClog]
  have hbar := H Y ν hY (harperOffset D x) a c δ h₀ w ⌈a / 4⌉₊
    (harperBlockCount D x) (fun j => 2 * Real.log j) hϑ (by linarith) hc hδ0 hCr
    (fun j hj _ => by linarith [hlog j hj])
    (fun j hj _ => two_log_le_self (le_trans hr1 hj)) h4
    (fun j _ hjn => by linarith [(abs_le.1 (hpsΔ j hjn)).2])
    (fun j _ hjn => by linarith [(abs_le.1 (hpsΔ j hjn)).1])
    (fun j _ _ => le_trans (hlogsum (harperOffset D x) δ hϑ hδ0 _) (by linarith only [hClogΔ]))
    hw
  have hset : {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w),
      ω ∉ harperGoodRangeAdd Y c D x δ a (harperBlockCount D x) h}
      = {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ harperBlockCount D x →
          walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
            localLogAdd (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (Y (p : ℕ) ω)) j ω
            ∈ Set.Icc (-a - c * (j : ℝ)) (a + (j : ℝ) + (fun j => 2 * Real.log j) j)} := by
    ext ω
    simp only [Set.mem_setOf_eq, mem_harperGoodRangeAdd, heightLine_eq_shiftLine]
  rw [hset]
  refine le_trans hbar ?_
  have hsum := sum_exp_neg_envelope_le (r := ⌈a / 4⌉₊) (n := harperBlockCount D x) hr1
  have hexpϑ : Real.exp (harperOffset D x) ≤ Real.exp D :=
    Real.exp_le_exp.2 (harperOffset_lt_natCast D x).le
  have hw0 : (0 : ℝ) ≤ w := le_trans (Real.exp_pos _).le hw
  have h2 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc ⌈a / 4⌉₊ (harperBlockCount D x),
      Real.exp (-(2 * (2 * Real.log j))) :=
    Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
  calc C₂ * w * Real.exp (harperOffset D x) * Real.exp (-(2 * a))
        * ∑ j ∈ Finset.Icc ⌈a / 4⌉₊ (harperBlockCount D x),
            Real.exp (-(2 * (2 * Real.log j)))
      ≤ C₂ * w * Real.exp D * Real.exp (-(2 * a)) * (1 + ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ)) := by
        gcongr
        linarith [hsum]
    _ = C₂ * (1 + ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ)) * Real.exp D * w * Real.exp (-(2 * a)) := by
        ring

/-- **The barrier bound with the top `d` blocks dropped, at a shift of either sign**: as
`RMF.exists_const_measureReal_notMem_harperGoodRangeAdd_of_top`, with `δ ≥ -1/12` for `δ ≥ 0`.
On the blocks walked `RMF.sigma_le_one_of_drop` gives `|δ|·log x_j ≤ 1`, so the signed prime-sum
bounds apply at `K = 1` with the barrier probability
`RMF.IsRademacherPrimeValues.exists_const_measure_exists_barrier_le_of_le_signed`, and the deficit
`1 + 45 + 120e² + e²·C` does not depend on `E₀`. -/
theorem exists_const_measureReal_notMem_harperGoodRangeAdd_of_top_signed {Ω' : Type*}
    [MeasurableSpace Ω'] :
    ∃ a₀ C : ℝ, 0 < C ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → E₀ ≤ Real.exp d →
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (D : ℕ) (x δ η a c h₀ w : ℝ), 4 ≤ D → 1 < x →
          (D : ℝ) ≤ Real.log (Real.log x) →
          -(1 / 12) ≤ δ → 0 ≤ η → η ≤ E₀ → |δ| * Real.log x ≤ η → a₀ ≤ a → 20 ≤ c →
          Real.exp (-((⌈a / 4⌉₊ : ℝ) + harperOffset D x)) ≤ w →
            ν.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w),
                ω ∉ harperGoodRangeAdd Y c D x δ a (harperBlockCount D x - d) h}
              ≤ C * Real.exp D * w * Real.exp (-(2 * a)) := by
  obtain ⟨Clog, hClog, hlogsum⟩ := exists_const_sum_primesIco_rpow_log_le_signed
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ, Δ = 1 + 45 + 120 * Real.exp 2 + Real.exp 2 * Clog :=
    ⟨_, rfl⟩
  have hΔ1 : (1 : ℝ) ≤ Δ := by
    rw [hΔdef]
    have := Real.exp_pos (2 : ℝ)
    nlinarith [hClog]
  obtain ⟨C₂, hC₂, H⟩ :=
    IsRademacherPrimeValues.exists_const_measure_exists_barrier_le_of_le_signed
      (Ω := Ω') Δ hΔ1
  have hζ40 : (0 : ℝ) ≤ ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ) :=
    tsum_nonneg fun i => Real.rpow_nonneg (Nat.cast_nonneg i) _
  have hClogΔ : Real.exp 2 * Clog ≤ Δ := by
    rw [hΔdef]
    linarith [Real.exp_pos (2 : ℝ)]
  refine ⟨max 1 (4 * C₂), C₂ * (1 + ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ)),
    mul_pos hC₂ (by linarith), ?_⟩
  intro E₀ d hE₀ hEd Y ν hY D x δ η a c h₀ w hD hx1 hxD hδ0 hη0 hηE hδx ha hc hw
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_left _ _) ha
  have haC₂ : 4 * C₂ ≤ a := le_trans (le_max_right _ _) ha
  have ha4 : (0 : ℝ) ≤ a / 4 := by linarith
  have hr1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
  have hrge : a / 4 ≤ (⌈a / 4⌉₊ : ℝ) := Nat.le_ceil _
  have hCr : C₂ ≤ ((⌈a / 4⌉₊ : ℕ) : ℝ) := by linarith
  have hD' : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hϑ3 : (3 : ℝ) ≤ harperOffset D x := by linarith [sub_one_le_harperOffset D x]
  have hϑ : (1 : ℝ) ≤ harperOffset D x := by linarith
  have hw0 : (0 : ℝ) ≤ w := le_trans (Real.exp_pos _).le hw
  rcases le_or_gt d (harperBlockCount D x) with hdn | hdn
  · -- the live branch: the drop puts the tilt scale under one
    have hlog : ∀ j, ⌈a / 4⌉₊ ≤ j → (0 : ℝ) ≤ Real.log j := fun j hj =>
      Real.log_nonneg (by exact_mod_cast le_trans hr1 hj)
    have h4 : ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ harperBlockCount D x - d → a ≤ 4 * (j : ℝ) := by
      intro j hj _
      have hjr : ((⌈a / 4⌉₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      linarith
    -- the tilt at the top of the full range, against `max E₀ 1`
    have hKd : max E₀ 1 ≤ Real.exp d := max_le hEd (Real.one_le_exp (Nat.cast_nonneg d))
    have hδE : |δ| * Real.log (blockScale (harperOffset D x)
        (harperBlockCount D x + 1)) ≤ max E₀ 1 := by
      rw [log_blockScale_harperOffset_top hx1 hxD]
      exact le_trans (le_trans hδx hηE) (le_max_left _ _)
    have hδtop : |δ| * Real.log (blockScale (harperOffset D x)
        (harperBlockCount D x - d + 1)) ≤ 1 := sigma_le_one_of_drop hKd hdn hδE
    have hδj : ∀ j, j ≤ harperBlockCount D x - d →
        |δ| * Real.log (blockScale (harperOffset D x) j) ≤ 1 := by
      intro j hj
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg δ)) hδtop
      exact Real.log_le_log (blockScale_pos _ _) (blockScale_mono _ (by omega))
    have hpsΔ : ∀ j, j ≤ harperBlockCount D x - d →
        |(∑ p ∈ primesIco (⌊blockScale (harperOffset D x) 0⌋₊ + 1)
            (⌊blockScale (harperOffset D x) j⌋₊ + 1), (p : ℝ) ^ (-2 * (1 / 2 + δ))) - (j : ℝ)|
          ≤ Δ := by
      intro j hj
      refine le_trans
        (abs_sum_primesIco_rpow_sub_le_of_le_signed' hϑ3 (by omega) zero_le_one
          (Or.inr le_rfl) hδtop) ?_
      have h1 : Real.exp (-(1 + harperOffset D x)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      have h2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
      rw [hΔdef, Real.sqrt_one]
      nlinarith [hClog, mul_nonneg (Real.exp_pos (2 : ℝ)).le hClog.le]
    have hbar := H Y ν hY (harperOffset D x) a c δ h₀ w ⌈a / 4⌉₊
      (harperBlockCount D x - d) (fun j => 2 * Real.log j) hϑ (by linarith) hc hδ0 hCr
      (fun j hj _ => by linarith [hlog j hj])
      (fun j hj _ => two_log_le_self (le_trans hr1 hj)) h4
      (fun j _ hjn => by linarith [(abs_le.1 (hpsΔ j hjn)).2])
      (fun j _ hjn => by linarith [(abs_le.1 (hpsΔ j hjn)).1])
      (fun j _ hjn => le_trans (hlogsum (harperOffset D x) δ hϑ j (Or.inr (hδj j hjn)))
        (by linarith only [hClogΔ]))
      hw
    have hset : {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w),
        ω ∉ harperGoodRangeAdd Y c D x δ a (harperBlockCount D x - d) h}
        = {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, ⌈a / 4⌉₊ ≤ j →
            j ≤ harperBlockCount D x - d →
            walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
              localLogAdd (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (Y (p : ℕ) ω)) j ω
              ∈ Set.Icc (-a - c * (j : ℝ)) (a + (j : ℝ) + (fun j => 2 * Real.log j) j)} := by
      ext ω
      simp only [Set.mem_setOf_eq, mem_harperGoodRangeAdd, heightLine_eq_shiftLine]
    rw [hset]
    refine le_trans hbar ?_
    have hsum := sum_exp_neg_envelope_le (r := ⌈a / 4⌉₊) (n := harperBlockCount D x - d) hr1
    have hexpϑ : Real.exp (harperOffset D x) ≤ Real.exp D :=
      Real.exp_le_exp.2 (harperOffset_lt_natCast D x).le
    have h2 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc ⌈a / 4⌉₊ (harperBlockCount D x - d),
        Real.exp (-(2 * (2 * Real.log j))) :=
      Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
    calc C₂ * w * Real.exp (harperOffset D x) * Real.exp (-(2 * a))
          * ∑ j ∈ Finset.Icc ⌈a / 4⌉₊ (harperBlockCount D x - d),
              Real.exp (-(2 * (2 * Real.log j)))
        ≤ C₂ * w * Real.exp D * Real.exp (-(2 * a)) * (1 + ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ)) := by
          gcongr
          linarith [hsum]
      _ = C₂ * (1 + ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ)) * Real.exp D * w * Real.exp (-(2 * a)) := by
          ring
  · -- the drop swallows the range, so the good set is everything
    have hgood : ∀ (ω : Ω') (h : ℝ),
        ω ∈ harperGoodRangeAdd Y c D x δ a (harperBlockCount D x - d) h := by
      intro ω h
      rw [mem_harperGoodRangeAdd]
      intro j hj1 hj2
      exfalso
      omega
    have hempty : {ω : Ω' | ∃ h ∈ Set.Ico h₀ (h₀ + w),
        ω ∉ harperGoodRangeAdd Y c D x δ a (harperBlockCount D x - d) h} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      rintro h ⟨-, hnot⟩
      exact hnot (hgood ω h)
    rw [hempty, measureReal_empty]
    have hC0 : (0 : ℝ) ≤ C₂ * (1 + ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ)) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hC0 (Real.exp_pos _).le) hw0) (Real.exp_pos _).le

/-- **The barrier bound at a shifted abscissa with the top `d` blocks dropped, at a deficit
independent of `E₀`.**  The good range stops `d` blocks short, where `RMF.sigma_le_one_of_drop`
puts the tilt scale under `1`, so `Δ = 46 + 120e² + C` instead of `1 + 45√E₀ + 120e² + C`, and
`E₀`, `d` are quantified inside `∃ a₀ C`: a caller may choose `E₀` after the constants.  When `d`
exceeds the block count the range is empty and so is the bad set.  The case `δ ≥ 0` of
`RMF.exists_const_measureReal_notMem_harperGoodRangeAdd_of_top_signed`. -/
theorem exists_const_measureReal_notMem_harperGoodRangeAdd_of_top {Ω' : Type*}
    [MeasurableSpace Ω'] :
    ∃ a₀ C : ℝ, 0 < C ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → E₀ ≤ Real.exp d →
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (D : ℕ) (x δ η a c h₀ w : ℝ), 4 ≤ D → 1 < x →
          (D : ℝ) ≤ Real.log (Real.log x) →
          0 ≤ δ → 0 ≤ η → η ≤ E₀ → |δ| * Real.log x ≤ η → a₀ ≤ a → 20 ≤ c →
          Real.exp (-((⌈a / 4⌉₊ : ℝ) + harperOffset D x)) ≤ w →
            ν.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w),
                ω ∉ harperGoodRangeAdd Y c D x δ a (harperBlockCount D x - d) h}
              ≤ C * Real.exp D * w * Real.exp (-(2 * a)) := by
  obtain ⟨a₀, C, hC, H⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_of_top_signed (Ω' := Ω')
  refine ⟨a₀, C, hC, ?_⟩
  intro E₀ d hE₀ hEd Y ν hY D x δ η a c h₀ w hD hx1 hxD hδ0 hη0 hηE hδx ha hc hw
  exact H E₀ d hE₀ hEd Y ν hY D x δ η a c h₀ w hD hx1 hxD (by linarith) hη0 hηE hδx ha hc hw

/-- **The barrier bound at a shifted abscissa with the top `d` blocks dropped, on one
`RMF.harperDt` band**: the drop form of
`RMF.exists_const_measureReal_notMem_harperGoodRangeAdd_band_of_le`, with `E₀` and `d` inside the
constants.  The band width still cancels the entropy, so `C·e^{D₀}` is `k`-free; a band whose
shortened range is empty has an empty bad set. -/
theorem exists_const_measureReal_notMem_harperGoodRangeAdd_band_of_top {Ω' : Type*}
    [MeasurableSpace Ω'] :
    ∃ a₀ C : ℝ, 0 < C ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → E₀ ≤ Real.exp d →
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (D₀ k : ℕ) (x δ η a c : ℝ), 4 ≤ D₀ → k ≠ 0 → 1 < x →
          0 ≤ δ → 0 ≤ η → η ≤ E₀ → |δ| * Real.log x ≤ η → a₀ ≤ a → 20 ≤ c →
            ν.real {ω | ∃ h ∈ Set.Ico (Real.exp (-(k : ℝ))) (Real.exp (-((k : ℝ) - 1))),
                ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ a
                  (harperBlockCount (harperDt D₀ h) x - d) h}
              ≤ C * Real.exp D₀ * Real.exp (-(2 * a)) := by
  obtain ⟨a₀, C, hC, H⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_of_top (Ω' := Ω')
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨max a₀ 1, C * (Real.exp 1 - 1), mul_pos hC (by linarith), ?_⟩
  intro E₀ d hE₀ hEd Y ν hY D₀ k x δ η a c hD₀ hk hx1 hδ0 hη0 hηE hδx ha hc
  haveI := hY.isProbabilityMeasure
  have ha₀ : a₀ ≤ a := le_trans (le_max_left _ _) ha
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  have hr1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
  have hek : (0 : ℝ) < Real.exp (-(k : ℝ)) := Real.exp_pos _
  have hband : Real.exp (-((k : ℝ) - 1)) = Real.exp (-(k : ℝ)) * Real.exp 1 := by
    rw [← Real.exp_add]; ring_nf
  have hw : Real.exp (-((k : ℝ) - 1)) - Real.exp (-(k : ℝ))
      = Real.exp (-(k : ℝ)) * (Real.exp 1 - 1) := by rw [hband]; ring
  have hset : {ω | ∃ h ∈ Set.Ico (Real.exp (-(k : ℝ))) (Real.exp (-((k : ℝ) - 1))),
      ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ a
        (harperBlockCount (harperDt D₀ h) x - d) h}
      = {ω | ∃ h ∈ Set.Ico (Real.exp (-(k : ℝ))) (Real.exp (-((k : ℝ) - 1))),
          ω ∉ harperGoodRangeAdd Y c (D₀ + k) x δ a (harperBlockCount (D₀ + k) x - d) h} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_Ico]
    constructor <;> rintro ⟨h, ⟨h1, h2⟩, hnot⟩ <;> refine ⟨h, ⟨h1, h2⟩, ?_⟩
    · rwa [(harperDt_eq_add_iff hk (lt_of_lt_of_le hek h1)).2 ⟨h1, h2⟩] at hnot
    · rwa [(harperDt_eq_add_iff hk (lt_of_lt_of_le hek h1)).2 ⟨h1, h2⟩]
  rw [hset]
  by_cases hdead : harperBlockCount (D₀ + k) x - d = 0
  · -- a dead band's bad set is empty, and the fixed-`D` bound is never invoked
    have hempty : {ω : Ω' | ∃ h ∈ Set.Ico (Real.exp (-(k : ℝ))) (Real.exp (-((k : ℝ) - 1))),
        ω ∉ harperGoodRangeAdd Y c (D₀ + k) x δ a (harperBlockCount (D₀ + k) x - d) h} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h, _, hnot⟩
      refine hnot ?_
      rw [mem_harperGoodRangeAdd]
      intro j hj1 hj2
      exfalso
      omega
    rw [hempty]
    have hz : ν.real (∅ : Set Ω') = 0 := by simp
    rw [hz]
    have hprod : (0 : ℝ) < C * (Real.exp 1 - 1) * Real.exp (D₀ : ℝ)
        * Real.exp (-(2 * a)) :=
      mul_pos (mul_pos (mul_pos hC (by linarith)) (Real.exp_pos _)) (Real.exp_pos _)
    linarith
  · -- a live band supplies `(D₀+k : ℝ) ≤ ℓogℓog x` itself
    have hlive : D₀ + k < ⌊Real.log (Real.log x)⌋₊ := by
      rcases Nat.lt_or_ge (D₀ + k) ⌊Real.log (Real.log x)⌋₊ with h | h
      · exact h
      · exact absurd (by rw [harperBlockCount]; omega) hdead
    have hfl0 : 0 < ⌊Real.log (Real.log x)⌋₊ := by omega
    have hL1 : (1 : ℝ) ≤ Real.log (Real.log x) := Nat.floor_pos.1 hfl0
    have hDL : ((D₀ + k : ℕ) : ℝ) ≤ Real.log (Real.log x) := by
      have h1 : ((D₀ + k : ℕ) : ℝ) < (⌊Real.log (Real.log x)⌋₊ : ℝ) := by exact_mod_cast hlive
      have h2 : (⌊Real.log (Real.log x)⌋₊ : ℝ) ≤ Real.log (Real.log x) :=
        Nat.floor_le (by linarith)
      linarith
    have hwin : Real.exp (-((⌈a / 4⌉₊ : ℝ) + harperOffset (D₀ + k) x))
        ≤ Real.exp (-((k : ℝ) - 1)) - Real.exp (-(k : ℝ)) := by
      rw [hw]
      have hrR : (1 : ℝ) ≤ ((⌈a / 4⌉₊ : ℕ) : ℝ) := by exact_mod_cast hr1
      have hD₀' : (4 : ℝ) ≤ (D₀ : ℝ) := by exact_mod_cast hD₀
      have hoff : ((D₀ : ℝ) + (k : ℝ)) - 1 ≤ harperOffset (D₀ + k) x := by
        have h := sub_one_le_harperOffset (D₀ + k) x
        push_cast at h
        linarith
      calc Real.exp (-((⌈a / 4⌉₊ : ℝ) + harperOffset (D₀ + k) x))
          ≤ Real.exp (-(1 + (((D₀ : ℝ) + (k : ℝ)) - 1))) := Real.exp_le_exp.2 (by linarith)
        _ = Real.exp (-(k : ℝ)) * Real.exp (-(D₀ : ℝ)) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (-(k : ℝ)) * (Real.exp 1 - 1) := by
            refine mul_le_mul_of_nonneg_left ?_ hek.le
            have h1 : Real.exp (-(D₀ : ℝ)) ≤ Real.exp 0 := Real.exp_le_exp.2 (by linarith)
            rw [Real.exp_zero] at h1
            linarith
    have hadd : Real.exp (-(k : ℝ)) + (Real.exp (-((k : ℝ) - 1)) - Real.exp (-(k : ℝ)))
        = Real.exp (-((k : ℝ) - 1)) := by ring
    have hbar := H E₀ d hE₀ hEd Y ν hY (D₀ + k) x δ η a c (Real.exp (-(k : ℝ)))
      (Real.exp (-((k : ℝ) - 1)) - Real.exp (-(k : ℝ))) (by omega) hx1 hDL hδ0 hη0 hηE hδx
      ha₀ hc hwin
    rw [hadd] at hbar
    refine le_trans hbar (le_of_eq ?_)
    have hkk : Real.exp (k : ℝ) * Real.exp (-(k : ℝ)) = 1 := by
      rw [← Real.exp_add]; simp
    have hcast : ((D₀ + k : ℕ) : ℝ) = (D₀ : ℝ) + (k : ℝ) := by push_cast; ring
    rw [hcast, hw, Real.exp_add]
    linear_combination (C * Real.exp (D₀ : ℝ) * (Real.exp 1 - 1) * Real.exp (-(2 * a))) * hkk

/-- **The union over `(0,1)` with the level growing along the bands**, with the top `d` blocks
dropped: the drop form of `RMF.exists_const_measureReal_notMem_harperGoodRangeAdd_Ioo_raise_of_le`.
Its constant carries no `⌊ℓogℓog x⌋` factor and does not depend on `E₀` or `d`. -/
theorem exists_const_measureReal_notMem_harperGoodRangeAdd_Ioo_raise_of_top {Ω' : Type*}
    [MeasurableSpace Ω'] :
    ∃ a₀ C : ℝ, 0 < C ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → E₀ ≤ Real.exp d →
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (D₀ : ℕ) (x δ η a c : ℝ), 4 ≤ D₀ → 1 < x →
          0 ≤ δ → 0 ≤ η → η ≤ E₀ → |δ| * Real.log x ≤ η → a₀ ≤ a → 20 ≤ c →
            ν.real {ω | ∃ h ∈ Set.Ioo (0 : ℝ) 1,
                ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ
                  (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
                  (harperBlockCount (harperDt D₀ h) x - d) h}
              ≤ C * Real.exp D₀ * Real.exp (-(2 * a)) := by
  obtain ⟨a₀, C, hC, H⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_band_of_top (Ω' := Ω')
  refine ⟨max a₀ 1, 2 * C, by linarith, ?_⟩
  intro E₀ d hE₀ hEd Y ν hY D₀ x δ η a c hD₀ hx1 hδ0 hη0 hηE hδx ha hc
  haveI := hY.isProbabilityMeasure
  have ha₀ : a₀ ≤ a := le_trans (le_max_left _ _) ha
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  set K := ⌊Real.log (Real.log x)⌋₊ with hKdef
  obtain ⟨E, hE⟩ : ∃ E : ℕ → Set Ω', E = fun k : ℕ =>
      {ω | ∃ h ∈ Set.Ico (Real.exp (-(k : ℝ))) (Real.exp (-((k : ℝ) - 1))),
        ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ (a + (k : ℝ))
          (harperBlockCount (harperDt D₀ h) x - d) h} := ⟨_, rfl⟩
  have hsub : {ω | ∃ h ∈ Set.Ioo (0 : ℝ) 1,
      ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ
        (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
        (harperBlockCount (harperDt D₀ h) x - d) h}
      ⊆ ⋃ k ∈ Finset.Icc 1 K, E k := by
    rintro ω ⟨h, hh, hnot⟩
    obtain ⟨k, hk1, hkeq⟩ := exists_harperDt_eq_add_of_mem_Ioo (D₀ := D₀) hh
    have hkne : k ≠ 0 := Nat.one_le_iff_ne_zero.1 hk1
    have hlev : ((harperDt D₀ h - D₀ : ℕ) : ℝ) = (k : ℝ) := by
      have hnat : harperDt D₀ h - D₀ = k := by omega
      rw [hnat]
    rw [hlev] at hnot
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hr1 : 1 ≤ ⌈(a + (k : ℝ)) / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
    have hkK : k ≤ K := by
      by_contra hcon
      push Not at hcon
      have hdead : harperBlockCount (harperDt D₀ h) x - d = 0 := by
        rw [hkeq, harperBlockCount, ← hKdef]
        omega
      rw [harperGoodRangeAdd_eq_univ_of_zero hr1 hdead] at hnot
      exact hnot (Set.mem_univ ω)
    refine Set.mem_biUnion (Finset.mem_Icc.2 ⟨hk1, hkK⟩) ?_
    rw [hE]
    exact ⟨h, Set.mem_Ico.2 ((harperDt_eq_add_iff hkne hh.1).1 hkeq), hnot⟩
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  have he2 : Real.exp (-2) ≤ 1 / 2 := by
    have h3 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have h4 : Real.exp (-2) * Real.exp 2 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have h5 : (0 : ℝ) < Real.exp (-2) := Real.exp_pos _
    nlinarith [mul_nonneg h5.le (by linarith : (0 : ℝ) ≤ Real.exp 2 - 2)]
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      ν.real (E k) ≤ (C * Real.exp D₀ * Real.exp (-(2 * a))) * (1 / 2 : ℝ) ^ k := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hband := H E₀ d hE₀ hEd Y ν hY D₀ k x δ η (a + (k : ℝ)) c hD₀
      (Nat.one_le_iff_ne_zero.1 hk1)
      hx1 hδ0 hη0 hηE hδx (by linarith) hc
    rw [hE]
    refine le_trans hband ?_
    have hsplit : Real.exp (-(2 * (a + (k : ℝ))))
        = Real.exp (-(2 * a)) * Real.exp (-2) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    have hpow : Real.exp (-2) ^ k ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_left₀ (Real.exp_nonneg _) he2 k
    rw [hsplit]
    calc C * Real.exp D₀ * (Real.exp (-(2 * a)) * Real.exp (-2) ^ k)
        = (C * Real.exp D₀ * Real.exp (-(2 * a))) * Real.exp (-2) ^ k := by ring
      _ ≤ (C * Real.exp D₀ * Real.exp (-(2 * a))) * (1 / 2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hgeo : (∑ k ∈ Finset.Icc 1 K, (1 / 2 : ℝ) ^ k) ≤ 2 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (sum_geometric_two_le (K + 1))
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_range]
      omega
    · intro i _ _
      positivity
  calc (C * Real.exp D₀ * Real.exp (-(2 * a))) * ∑ k ∈ Finset.Icc 1 K, (1 / 2 : ℝ) ^ k
      ≤ (C * Real.exp D₀ * Real.exp (-(2 * a))) * 2 :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = 2 * C * Real.exp D₀ * Real.exp (-(2 * a)) := by ring

/-- **The shifted union over `(0,1]`, at the drop** --- the top of the bad-set ladder, and
the form `RMF.exists_const_harperGoodRangeAdd_bounds_of_scale_rademacher_raise_of_top`
reads.  The `_of_top` twin of
`RMF.exists_const_measureReal_notMem_harperGoodRangeAdd_Ioc_raise_of_le`. -/
theorem exists_const_measureReal_notMem_harperGoodRangeAdd_Ioc_raise_of_top {Ω' : Type*}
    [MeasurableSpace Ω'] :
    ∃ a₀ C : ℝ, 0 < C ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → E₀ ≤ Real.exp d →
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (D₀ : ℕ) (x δ η a c : ℝ), 4 ≤ D₀ → 1 < x →
          0 ≤ δ → 0 ≤ η → η ≤ E₀ → |δ| * Real.log x ≤ η → a₀ ≤ a → 20 ≤ c →
            ν.real {ω | ∃ h ∈ Set.Ioc (0 : ℝ) 1,
                ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ
                  (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
                  (harperBlockCount (harperDt D₀ h) x - d) h}
              ≤ C * Real.exp D₀ * Real.exp (-(2 * a)) := by
  obtain ⟨a₀o, Co, hCo, Ho⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_Ioo_raise_of_top (Ω' := Ω')
  obtain ⟨a₀p, Cp, hCp, Hp⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_of_top (Ω' := Ω')
  refine ⟨max (max a₀o a₀p) 1, Co + Cp, by linarith, ?_⟩
  intro E₀ d hE₀ hEd Y ν hY D₀ x δ η a c hD₀ hx1 hδ0 hη0 hηE hδx ha hc
  haveI := hY.isProbabilityMeasure
  have hao : a₀o ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha
  have hap : a₀p ≤ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  have hr1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
  have hdt1 : harperDt D₀ (1 : ℝ) = D₀ := by simp [harperDt]
  have hsplit : {ω | ∃ h ∈ Set.Ioc (0 : ℝ) 1,
      ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ
        (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
        (harperBlockCount (harperDt D₀ h) x - d) h}
      ⊆ {ω | ∃ h ∈ Set.Ioo (0 : ℝ) 1,
            ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ
              (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
              (harperBlockCount (harperDt D₀ h) x - d) h}
        ∪ {ω | ∃ h ∈ Set.Ico (1 : ℝ) (1 + 1),
            ω ∉ harperGoodRangeAdd Y c D₀ x δ a (harperBlockCount D₀ x - d) h} := by
    rintro ω ⟨h, hh, hnot⟩
    rcases lt_or_eq_of_le hh.2 with hlt | heq
    · exact Or.inl ⟨h, ⟨hh.1, hlt⟩, hnot⟩
    · refine Or.inr ⟨1, Set.mem_Ico.2 ⟨le_rfl, by norm_num⟩, ?_⟩
      rw [heq, hdt1] at hnot
      simpa using hnot
  refine le_trans (measureReal_mono hsplit (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_union_le _ _) ?_
  have hA := Ho E₀ d hE₀ hEd Y ν hY D₀ x δ η a c hD₀ hx1 hδ0 hη0 hηE hδx hao hc
  have hB : ν.real {ω : Ω' | ∃ h ∈ Set.Ico (1 : ℝ) (1 + 1),
      ω ∉ harperGoodRangeAdd Y c D₀ x δ a (harperBlockCount D₀ x - d) h}
      ≤ Cp * Real.exp D₀ * Real.exp (-(2 * a)) := by
    by_cases hdead : harperBlockCount D₀ x - d = 0
    · have hempty : {ω : Ω' | ∃ h ∈ Set.Ico (1 : ℝ) (1 + 1),
          ω ∉ harperGoodRangeAdd Y c D₀ x δ a (harperBlockCount D₀ x - d) h} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h, _, hnot⟩
        rw [harperGoodRangeAdd_eq_univ_of_zero hr1 hdead] at hnot
        exact hnot (Set.mem_univ ω)
      rw [hempty]
      have hz : ν.real (∅ : Set Ω') = 0 := by simp
      rw [hz]
      have := mul_pos (mul_pos hCp (Real.exp_pos (D₀ : ℝ))) (Real.exp_pos (-(2 * a)))
      linarith
    · have hlive : D₀ < ⌊Real.log (Real.log x)⌋₊ := by
        rcases Nat.lt_or_ge D₀ ⌊Real.log (Real.log x)⌋₊ with h | h
        · exact h
        · exact absurd (by rw [harperBlockCount]; omega) hdead
      have hL1 : (1 : ℝ) ≤ Real.log (Real.log x) := Nat.floor_pos.1 (by omega)
      have hDL : (D₀ : ℝ) ≤ Real.log (Real.log x) := by
        have h1 : (D₀ : ℝ) < (⌊Real.log (Real.log x)⌋₊ : ℝ) := by exact_mod_cast hlive
        have h2 : (⌊Real.log (Real.log x)⌋₊ : ℝ) ≤ Real.log (Real.log x) :=
          Nat.floor_le (by linarith)
        linarith
      have hwin : Real.exp (-((⌈a / 4⌉₊ : ℝ) + harperOffset D₀ x)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have h1 := sub_one_le_harperOffset D₀ x
        have h2 : (0 : ℝ) ≤ (⌈a / 4⌉₊ : ℕ) := Nat.cast_nonneg _
        have hD₀' : (4 : ℝ) ≤ (D₀ : ℝ) := by exact_mod_cast hD₀
        linarith
      have h := Hp E₀ d hE₀ hEd Y ν hY D₀ x δ η a c 1 1 hD₀ hx1 hDL hδ0 hη0 hηE hδx hap hc hwin
      rw [mul_one] at h
      exact h
  have hring : (Co + Cp) * Real.exp D₀ * Real.exp (-(2 * a))
      = Co * Real.exp D₀ * Real.exp (-(2 * a)) + Cp * Real.exp D₀ * Real.exp (-(2 * a)) := by
    ring
  linarith

/-- **The barrier bound at a shifted abscissa, on one `RMF.harperDt` band**, with the `k`-free
constant `C·e^{D₀}`.  The fixed-`D` bound needs `(D : ℝ) ≤ ℓogℓog x`, which a live band supplies
itself; on a dead band the bad set is empty.  `1 < x` is a hypothesis because `Real.log` is even:
at `x = e^{-100}`, `ℓogℓog x = ℓog 100 > 4`, so a live block count does not imply `x > 1`. -/
theorem exists_const_measureReal_notMem_harperGoodRangeAdd_band_of_le {Ω' : Type*}
    [MeasurableSpace Ω'] (E₀ : ℝ) (hE₀ : 0 ≤ E₀) :
    ∃ a₀ C : ℝ, 0 < C ∧
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (D₀ k : ℕ) (x δ η a c : ℝ), 4 ≤ D₀ → k ≠ 0 → 1 < x →
          0 ≤ δ → 0 ≤ η → η ≤ E₀ → |δ| * Real.log x ≤ η → a₀ ≤ a → 20 ≤ c →
            ν.real {ω | ∃ h ∈ Set.Ico (Real.exp (-(k : ℝ))) (Real.exp (-((k : ℝ) - 1))),
                ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ a
                  (harperBlockCount (harperDt D₀ h) x) h}
              ≤ C * Real.exp D₀ * Real.exp (-(2 * a)) := by
  obtain ⟨a₀, C, hC, H⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_of_le (Ω' := Ω') E₀ hE₀
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨max a₀ 1, C * (Real.exp 1 - 1), mul_pos hC (by linarith), ?_⟩
  intro Y ν hY D₀ k x δ η a c hD₀ hk hx1 hδ0 hη0 hηE hδx ha hc
  haveI := hY.isProbabilityMeasure
  have ha₀ : a₀ ≤ a := le_trans (le_max_left _ _) ha
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  have hr1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
  have hek : (0 : ℝ) < Real.exp (-(k : ℝ)) := Real.exp_pos _
  have hband : Real.exp (-((k : ℝ) - 1)) = Real.exp (-(k : ℝ)) * Real.exp 1 := by
    rw [← Real.exp_add]; ring_nf
  have hw : Real.exp (-((k : ℝ) - 1)) - Real.exp (-(k : ℝ))
      = Real.exp (-(k : ℝ)) * (Real.exp 1 - 1) := by rw [hband]; ring
  have hset : {ω | ∃ h ∈ Set.Ico (Real.exp (-(k : ℝ))) (Real.exp (-((k : ℝ) - 1))),
      ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ a
        (harperBlockCount (harperDt D₀ h) x) h}
      = {ω | ∃ h ∈ Set.Ico (Real.exp (-(k : ℝ))) (Real.exp (-((k : ℝ) - 1))),
          ω ∉ harperGoodRangeAdd Y c (D₀ + k) x δ a (harperBlockCount (D₀ + k) x) h} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_Ico]
    constructor <;> rintro ⟨h, ⟨h1, h2⟩, hnot⟩ <;> refine ⟨h, ⟨h1, h2⟩, ?_⟩
    · rwa [(harperDt_eq_add_iff hk (lt_of_lt_of_le hek h1)).2 ⟨h1, h2⟩] at hnot
    · rwa [(harperDt_eq_add_iff hk (lt_of_lt_of_le hek h1)).2 ⟨h1, h2⟩]
  rw [hset]
  by_cases hdead : harperBlockCount (D₀ + k) x = 0
  · -- a dead band's bad set is empty, and the fixed-`D` bound is never invoked
    have hempty : {ω : Ω' | ∃ h ∈ Set.Ico (Real.exp (-(k : ℝ))) (Real.exp (-((k : ℝ) - 1))),
        ω ∉ harperGoodRangeAdd Y c (D₀ + k) x δ a (harperBlockCount (D₀ + k) x) h} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h, _, hnot⟩
      rw [harperGoodRangeAdd_eq_univ_of_blockCount_zero hr1 hdead] at hnot
      exact hnot (Set.mem_univ ω)
    rw [hempty]
    have hz : ν.real (∅ : Set Ω') = 0 := by simp
    rw [hz]
    have hprod : (0 : ℝ) < C * (Real.exp 1 - 1) * Real.exp (D₀ : ℝ)
        * Real.exp (-(2 * a)) :=
      mul_pos (mul_pos (mul_pos hC (by linarith)) (Real.exp_pos _)) (Real.exp_pos _)
    linarith
  · -- a live band supplies `(D₀+k : ℝ) ≤ ℓogℓog x` itself
    have hlive : D₀ + k < ⌊Real.log (Real.log x)⌋₊ := by
      rcases Nat.lt_or_ge (D₀ + k) ⌊Real.log (Real.log x)⌋₊ with h | h
      · exact h
      · exact absurd (by rw [harperBlockCount]; omega) hdead
    have hfl0 : 0 < ⌊Real.log (Real.log x)⌋₊ := by omega
    have hL1 : (1 : ℝ) ≤ Real.log (Real.log x) := Nat.floor_pos.1 hfl0
    have hDL : ((D₀ + k : ℕ) : ℝ) ≤ Real.log (Real.log x) := by
      have h1 : ((D₀ + k : ℕ) : ℝ) < (⌊Real.log (Real.log x)⌋₊ : ℝ) := by exact_mod_cast hlive
      have h2 : (⌊Real.log (Real.log x)⌋₊ : ℝ) ≤ Real.log (Real.log x) :=
        Nat.floor_le (by linarith)
      linarith
    have hwin : Real.exp (-((⌈a / 4⌉₊ : ℝ) + harperOffset (D₀ + k) x))
        ≤ Real.exp (-((k : ℝ) - 1)) - Real.exp (-(k : ℝ)) := by
      rw [hw]
      have hrR : (1 : ℝ) ≤ ((⌈a / 4⌉₊ : ℕ) : ℝ) := by exact_mod_cast hr1
      have hD₀' : (4 : ℝ) ≤ (D₀ : ℝ) := by exact_mod_cast hD₀
      have hoff : ((D₀ : ℝ) + (k : ℝ)) - 1 ≤ harperOffset (D₀ + k) x := by
        have h := sub_one_le_harperOffset (D₀ + k) x
        push_cast at h
        linarith
      calc Real.exp (-((⌈a / 4⌉₊ : ℝ) + harperOffset (D₀ + k) x))
          ≤ Real.exp (-(1 + (((D₀ : ℝ) + (k : ℝ)) - 1))) := Real.exp_le_exp.2 (by linarith)
        _ = Real.exp (-(k : ℝ)) * Real.exp (-(D₀ : ℝ)) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (-(k : ℝ)) * (Real.exp 1 - 1) := by
            refine mul_le_mul_of_nonneg_left ?_ hek.le
            have h1 : Real.exp (-(D₀ : ℝ)) ≤ Real.exp 0 := Real.exp_le_exp.2 (by linarith)
            rw [Real.exp_zero] at h1
            linarith
    have hadd : Real.exp (-(k : ℝ)) + (Real.exp (-((k : ℝ) - 1)) - Real.exp (-(k : ℝ)))
        = Real.exp (-((k : ℝ) - 1)) := by ring
    have hbar := H Y ν hY (D₀ + k) x δ η a c (Real.exp (-(k : ℝ)))
      (Real.exp (-((k : ℝ) - 1)) - Real.exp (-(k : ℝ))) (by omega) hx1 hDL hδ0 hη0 hηE hδx
      ha₀ hc hwin
    rw [hadd] at hbar
    refine le_trans hbar (le_of_eq ?_)
    have hkk : Real.exp (k : ℝ) * Real.exp (-(k : ℝ)) = 1 := by
      rw [← Real.exp_add]; simp
    have hcast : ((D₀ + k : ℕ) : ℝ) = (D₀ : ℝ) + (k : ℝ) := by push_cast; ring
    rw [hcast, hw, Real.exp_add]
    linear_combination (C * Real.exp (D₀ : ℝ) * (Real.exp 1 - 1) * Real.exp (-(2 * a))) * hkk

/-- **The union over `(0,1)` with the level growing along the bands**, with a constant free of any
factor `⌊ℓogℓog x⌋`.  Every band holds about `e^{a/4 + D₀}` discretisation points whatever `k` is,
so at a fixed level the bands contribute equally; read at level `a + k`, band `k` carries
`e^{-2(a+k)}` and the bands sum a geometric series (`sum_geometric_two_le`, `e^{-2} ≤ 1/2`).  The
chaos bound at the raised level is
`RMF.exists_const_integral_restrictedChaosUnitShift_raise_le_rademacher_of_drop`. -/
theorem exists_const_measureReal_notMem_harperGoodRangeAdd_Ioo_raise_of_le {Ω' : Type*}
    [MeasurableSpace Ω'] (E₀ : ℝ) (hE₀ : 0 ≤ E₀) :
    ∃ a₀ C : ℝ, 0 < C ∧
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (D₀ : ℕ) (x δ η a c : ℝ), 4 ≤ D₀ → 1 < x →
          0 ≤ δ → 0 ≤ η → η ≤ E₀ → |δ| * Real.log x ≤ η → a₀ ≤ a → 20 ≤ c →
            ν.real {ω | ∃ h ∈ Set.Ioo (0 : ℝ) 1,
                ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ
                  (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
                  (harperBlockCount (harperDt D₀ h) x) h}
              ≤ C * Real.exp D₀ * Real.exp (-(2 * a)) := by
  obtain ⟨a₀, C, hC, H⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_band_of_le (Ω' := Ω') E₀ hE₀
  refine ⟨max a₀ 1, 2 * C, by linarith, ?_⟩
  intro Y ν hY D₀ x δ η a c hD₀ hx1 hδ0 hη0 hηE hδx ha hc
  haveI := hY.isProbabilityMeasure
  have ha₀ : a₀ ≤ a := le_trans (le_max_left _ _) ha
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  set K := ⌊Real.log (Real.log x)⌋₊ with hKdef
  obtain ⟨E, hE⟩ : ∃ E : ℕ → Set Ω', E = fun k : ℕ =>
      {ω | ∃ h ∈ Set.Ico (Real.exp (-(k : ℝ))) (Real.exp (-((k : ℝ) - 1))),
        ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ (a + (k : ℝ))
          (harperBlockCount (harperDt D₀ h) x) h} := ⟨_, rfl⟩
  have hsub : {ω | ∃ h ∈ Set.Ioo (0 : ℝ) 1,
      ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ
        (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
        (harperBlockCount (harperDt D₀ h) x) h}
      ⊆ ⋃ k ∈ Finset.Icc 1 K, E k := by
    rintro ω ⟨h, hh, hnot⟩
    obtain ⟨k, hk1, hkeq⟩ := exists_harperDt_eq_add_of_mem_Ioo (D₀ := D₀) hh
    have hkne : k ≠ 0 := Nat.one_le_iff_ne_zero.1 hk1
    have hlev : ((harperDt D₀ h - D₀ : ℕ) : ℝ) = (k : ℝ) := by
      have hnat : harperDt D₀ h - D₀ = k := by omega
      rw [hnat]
    rw [hlev] at hnot
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hr1 : 1 ≤ ⌈(a + (k : ℝ)) / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
    have hkK : k ≤ K := by
      by_contra hcon
      push Not at hcon
      have hdead : harperBlockCount (harperDt D₀ h) x = 0 := by
        rw [hkeq, harperBlockCount, ← hKdef]
        omega
      rw [harperGoodRangeAdd_eq_univ_of_blockCount_zero hr1 hdead] at hnot
      exact hnot (Set.mem_univ ω)
    refine Set.mem_biUnion (Finset.mem_Icc.2 ⟨hk1, hkK⟩) ?_
    rw [hE]
    exact ⟨h, Set.mem_Ico.2 ((harperDt_eq_add_iff hkne hh.1).1 hkeq), hnot⟩
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  have he2 : Real.exp (-2) ≤ 1 / 2 := by
    have h3 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have h4 : Real.exp (-2) * Real.exp 2 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have h5 : (0 : ℝ) < Real.exp (-2) := Real.exp_pos _
    nlinarith [mul_nonneg h5.le (by linarith : (0 : ℝ) ≤ Real.exp 2 - 2)]
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      ν.real (E k) ≤ (C * Real.exp D₀ * Real.exp (-(2 * a))) * (1 / 2 : ℝ) ^ k := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hband := H Y ν hY D₀ k x δ η (a + (k : ℝ)) c hD₀ (Nat.one_le_iff_ne_zero.1 hk1)
      hx1 hδ0 hη0 hηE hδx (by linarith) hc
    rw [hE]
    refine le_trans hband ?_
    have hsplit : Real.exp (-(2 * (a + (k : ℝ))))
        = Real.exp (-(2 * a)) * Real.exp (-2) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    have hpow : Real.exp (-2) ^ k ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_left₀ (Real.exp_nonneg _) he2 k
    rw [hsplit]
    calc C * Real.exp D₀ * (Real.exp (-(2 * a)) * Real.exp (-2) ^ k)
        = (C * Real.exp D₀ * Real.exp (-(2 * a))) * Real.exp (-2) ^ k := by ring
      _ ≤ (C * Real.exp D₀ * Real.exp (-(2 * a))) * (1 / 2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hgeo : (∑ k ∈ Finset.Icc 1 K, (1 / 2 : ℝ) ^ k) ≤ 2 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (sum_geometric_two_le (K + 1))
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_range]
      omega
    · intro i _ _
      positivity
  calc (C * Real.exp D₀ * Real.exp (-(2 * a))) * ∑ k ∈ Finset.Icc 1 K, (1 / 2 : ℝ) ^ k
      ≤ (C * Real.exp D₀ * Real.exp (-(2 * a))) * 2 :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = 2 * C * Real.exp D₀ * Real.exp (-(2 * a)) := by ring

/-- **The union over `(0, 1]` at a growing level**:
`RMF.exists_const_measureReal_notMem_harperGoodRangeAdd_Ioo_raise_of_le` plus the endpoint
`h = 1`, where `RMF.harperDt D₀ 1 = D₀`, so the level shift is `0` and the endpoint is the unshifted
bound.  This is the shape of `RMF.GoodFamilyAdd.measure_bad_le`; its `integral_restricted_le` at
the raised level is
`RMF.exists_const_integral_restrictedChaosUnitShift_raise_le_rademacher_of_drop`. -/
theorem exists_const_measureReal_notMem_harperGoodRangeAdd_Ioc_raise_of_le {Ω' : Type*}
    [MeasurableSpace Ω'] (E₀ : ℝ) (hE₀ : 0 ≤ E₀) :
    ∃ a₀ C : ℝ, 0 < C ∧
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (D₀ : ℕ) (x δ η a c : ℝ), 4 ≤ D₀ → 1 < x →
          0 ≤ δ → 0 ≤ η → η ≤ E₀ → |δ| * Real.log x ≤ η → a₀ ≤ a → 20 ≤ c →
            ν.real {ω | ∃ h ∈ Set.Ioc (0 : ℝ) 1,
                ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ
                  (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
                  (harperBlockCount (harperDt D₀ h) x) h}
              ≤ C * Real.exp D₀ * Real.exp (-(2 * a)) := by
  obtain ⟨a₀o, Co, hCo, Ho⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_Ioo_raise_of_le (Ω' := Ω') E₀ hE₀
  obtain ⟨a₀p, Cp, hCp, Hp⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_of_le (Ω' := Ω') E₀ hE₀
  refine ⟨max (max a₀o a₀p) 1, Co + Cp, by linarith, ?_⟩
  intro Y ν hY D₀ x δ η a c hD₀ hx1 hδ0 hη0 hηE hδx ha hc
  haveI := hY.isProbabilityMeasure
  have hao : a₀o ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha
  have hap : a₀p ≤ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  have hr1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
  have hdt1 : harperDt D₀ (1 : ℝ) = D₀ := by simp [harperDt]
  have hsplit : {ω | ∃ h ∈ Set.Ioc (0 : ℝ) 1,
      ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ
        (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
        (harperBlockCount (harperDt D₀ h) x) h}
      ⊆ {ω | ∃ h ∈ Set.Ioo (0 : ℝ) 1,
            ω ∉ harperGoodRangeAdd Y c (harperDt D₀ h) x δ
              (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
              (harperBlockCount (harperDt D₀ h) x) h}
        ∪ {ω | ∃ h ∈ Set.Ico (1 : ℝ) (1 + 1),
            ω ∉ harperGoodRangeAdd Y c D₀ x δ a (harperBlockCount D₀ x) h} := by
    rintro ω ⟨h, hh, hnot⟩
    rcases lt_or_eq_of_le hh.2 with hlt | heq
    · exact Or.inl ⟨h, ⟨hh.1, hlt⟩, hnot⟩
    · refine Or.inr ⟨1, Set.mem_Ico.2 ⟨le_rfl, by norm_num⟩, ?_⟩
      rw [heq, hdt1] at hnot
      simpa using hnot
  refine le_trans (measureReal_mono hsplit (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_union_le _ _) ?_
  have hA := Ho Y ν hY D₀ x δ η a c hD₀ hx1 hδ0 hη0 hηE hδx hao hc
  have hB : ν.real {ω : Ω' | ∃ h ∈ Set.Ico (1 : ℝ) (1 + 1),
      ω ∉ harperGoodRangeAdd Y c D₀ x δ a (harperBlockCount D₀ x) h}
      ≤ Cp * Real.exp D₀ * Real.exp (-(2 * a)) := by
    by_cases hdead : harperBlockCount D₀ x = 0
    · have hempty : {ω : Ω' | ∃ h ∈ Set.Ico (1 : ℝ) (1 + 1),
          ω ∉ harperGoodRangeAdd Y c D₀ x δ a (harperBlockCount D₀ x) h} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h, _, hnot⟩
        rw [harperGoodRangeAdd_eq_univ_of_blockCount_zero hr1 hdead] at hnot
        exact hnot (Set.mem_univ ω)
      rw [hempty]
      have hz : ν.real (∅ : Set Ω') = 0 := by simp
      rw [hz]
      have := mul_pos (mul_pos hCp (Real.exp_pos (D₀ : ℝ))) (Real.exp_pos (-(2 * a)))
      linarith
    · have hlive : D₀ < ⌊Real.log (Real.log x)⌋₊ := by
        rcases Nat.lt_or_ge D₀ ⌊Real.log (Real.log x)⌋₊ with h | h
        · exact h
        · exact absurd (by rw [harperBlockCount]; omega) hdead
      have hL1 : (1 : ℝ) ≤ Real.log (Real.log x) := Nat.floor_pos.1 (by omega)
      have hDL : (D₀ : ℝ) ≤ Real.log (Real.log x) := by
        have h1 : (D₀ : ℝ) < (⌊Real.log (Real.log x)⌋₊ : ℝ) := by exact_mod_cast hlive
        have h2 : (⌊Real.log (Real.log x)⌋₊ : ℝ) ≤ Real.log (Real.log x) :=
          Nat.floor_le (by linarith)
        linarith
      have hwin : Real.exp (-((⌈a / 4⌉₊ : ℝ) + harperOffset D₀ x)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have h1 := sub_one_le_harperOffset D₀ x
        have h2 : (0 : ℝ) ≤ (⌈a / 4⌉₊ : ℕ) := Nat.cast_nonneg _
        have hD₀' : (4 : ℝ) ≤ (D₀ : ℝ) := by exact_mod_cast hD₀
        linarith
      have h := Hp Y ν hY D₀ x δ η a c 1 1 hD₀ hx1 hDL hδ0 hη0 hηE hδx hap hc hwin
      rw [mul_one] at h
      exact h
  have hring : (Co + Cp) * Real.exp D₀ * Real.exp (-(2 * a))
      = Co * Real.exp D₀ * Real.exp (-(2 * a)) + Cp * Real.exp D₀ * Real.exp (-(2 * a)) := by
    ring
  linarith

/-- **Both good-set bounds at the raised level**, with the top `d` blocks dropped: the data of
`RMF.GoodFamilyAdd` for the family read at level `a + k` on band `k`.  At a fixed level the measure
bound carries `(⌊ℓogℓog x⌋ + 1)·C·e^{D₀}·e^{-2a}`, which `GoodFamilyAdd` cannot take as a
constant; the raise makes the bands sum a geometric series, at a factor `3` in the chaos bound.
The count hypothesis `8⌈a/4⌉ ≤ harperBlockCount D₀ x` guards only the chaos bound, because
`measure_bad_le` has none; `_n₀` is unused. -/
theorem exists_const_harperGoodRangeAdd_bounds_of_scale_rademacher_raise_of_drop {Ω' : Type*}
    [MeasurableSpace Ω'] (E₀ : ℝ) (hE₀ : 0 ≤ E₀) (d : ℕ)
    (hE₁ : 10 * E₀ ≤ Real.exp d) :
    ∃ (D₀ _n₀ : ℕ) (x₀ a₀ C B : ℝ), 4 ≤ D₀ ∧ 0 < C ∧ 20 ≤ B ∧
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ x δ η a : ℝ, x₀ ≤ x → 0 ≤ δ → 0 ≤ η → η ≤ E₀ → |δ| * Real.log x ≤ η →
          a₀ ≤ a → 1 ≤ a →
            ν.real {ω | ∃ h ∈ Set.Ioc (0 : ℝ) 1,
                ω ∉ harperGoodRangeAdd Y B (harperDt D₀ h) x δ
                  (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
                  (harperBlockCount (harperDt D₀ h) x - d) h}
                ≤ C * Real.exp D₀ * Real.exp (-(2 * a))
              ∧ (8 * (⌈a / 4⌉₊ : ℝ) ≤ (harperBlockCount D₀ x : ℝ) →
                (∫ ω, restrictedChaosUnitShift
                  (fun ω => squarefreeExtension fun p => Y p ω) x δ
                  (fun h => harperGoodRangeAdd Y B (harperDt D₀ h) x δ
                    (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
                    (harperBlockCount (harperDt D₀ h) x - d) h) ω ∂ν)
                ≤ C * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - ⌈a / 4⌉₊))) := by
  obtain ⟨D₀, n₀, a₀c, Cc, B, hD₀, hCc, hB, Hc₀⟩ :=
    exists_const_integral_restrictedChaosUnitShift_raise_le_rademacher_of_drop
  obtain ⟨x₀c, Hc⟩ := Hc₀ E₀ d hE₀ hE₁
  obtain ⟨a₀b, Cb, hCb, Hb⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_Ioc_raise_of_le (Ω' := Ω') E₀ hE₀
  refine ⟨D₀, n₀, max x₀c (Real.exp 1), max a₀c a₀b, max Cc Cb, B, hD₀,
    lt_of_lt_of_le hCc (le_max_left _ _), hB, ?_⟩
  intro Y ν hY x δ η a hx hδ0 hη0 hηE hδx ha ha1
  haveI := hY.isProbabilityMeasure
  have hxc : x₀c ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) < x := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hac : a₀c ≤ a := le_trans (le_max_left _ _) ha
  have hab : a₀b ≤ a := le_trans (le_max_right _ _) ha
  refine ⟨?_, ?_⟩
  · have hsub : {ω : Ω' | ∃ h ∈ Set.Ioc (0 : ℝ) 1,
        ω ∉ harperGoodRangeAdd Y B (harperDt D₀ h) x δ
          (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
          (harperBlockCount (harperDt D₀ h) x - d) h}
        ⊆ {ω : Ω' | ∃ h ∈ Set.Ioc (0 : ℝ) 1,
        ω ∉ harperGoodRangeAdd Y B (harperDt D₀ h) x δ
          (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
          (harperBlockCount (harperDt D₀ h) x) h} := by
      rintro ω ⟨h, hh, hnot⟩
      exact ⟨h, hh, fun hmem =>
        hnot (harperGoodRangeAdd_subset_of_le (Nat.sub_le _ _) hmem)⟩
    refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
    refine le_trans (Hb Y ν hY D₀ x δ η a B hD₀ hx1 hδ0 hη0 hηE hδx hab hB) ?_
    have h1 : (0 : ℝ) ≤ Real.exp D₀ * Real.exp (-(2 * a)) := by positivity
    have h2 : Cb ≤ max Cc Cb := le_max_right _ _
    nlinarith
  · intro hΛ
    refine le_trans (Hc Ω' Y ν hY x δ η a hxc hδ0 hη0 hηE hδx hac ha1 hΛ) ?_
    have ha0 : (0 : ℝ) ≤ a := by linarith
    have hmin0 : (0 : ℝ)
        ≤ min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - ⌈a / 4⌉₊)) :=
      le_min zero_le_one (div_nonneg ha0 (Real.sqrt_nonneg _))
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hmin0

/-- **The good-set estimate at the drop, with `E₀` and `d` inside the constants**: the Rademacher
counterpart of `RMF.exists_const_harperGood_bounds_of_top`.
`RMF.exists_const_harperGoodRangeAdd_bounds_of_scale_rademacher_raise_of_drop` binds `E₀` and `d`
before its constants; here both bounds run to `t - d`, where `RMF.sigma_le_one_of_drop` puts the
tilt scale under `1`, so `D₀`, `a₀`, `C` and `B` do not depend on `E₀` or `d`, and a caller may
choose `E₀` after them. -/
theorem exists_const_harperGoodRangeAdd_bounds_of_scale_rademacher_raise_of_top {Ω' : Type*}
    [MeasurableSpace Ω'] :
    ∃ (D₀ _n₀ : ℕ) (a₀ C B : ℝ), 4 ≤ D₀ ∧ 0 < C ∧ 20 ≤ B ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → 10 * E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ x δ η a : ℝ, x₀ ≤ x → 0 ≤ δ → 0 ≤ η → η ≤ E₀ → |δ| * Real.log x ≤ η →
          a₀ ≤ a → 1 ≤ a →
            ν.real {ω | ∃ h ∈ Set.Ioc (0 : ℝ) 1,
                ω ∉ harperGoodRangeAdd Y B (harperDt D₀ h) x δ
                  (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
                  (harperBlockCount (harperDt D₀ h) x - d) h}
                ≤ C * Real.exp D₀ * Real.exp (-(2 * a))
              ∧ (8 * (⌈a / 4⌉₊ : ℝ) ≤ (harperBlockCount D₀ x : ℝ) →
                (∫ ω, restrictedChaosUnitShift
                  (fun ω => squarefreeExtension fun p => Y p ω) x δ
                  (fun h => harperGoodRangeAdd Y B (harperDt D₀ h) x δ
                    (a + ((harperDt D₀ h - D₀ : ℕ) : ℝ))
                    (harperBlockCount (harperDt D₀ h) x - d) h) ω ∂ν)
                ≤ C * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - ⌈a / 4⌉₊))) := by
  obtain ⟨D₀, n₀, a₀c, Cc, B, hD₀, hCc, hB, Hc₀⟩ :=
    exists_const_integral_restrictedChaosUnitShift_raise_le_rademacher_of_drop
  obtain ⟨a₀b, Cb, hCb, Hb⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_Ioc_raise_of_top (Ω' := Ω')
  refine ⟨D₀, n₀, max a₀c a₀b, max Cc Cb, B, hD₀,
    lt_of_lt_of_le hCc (le_max_left _ _), hB, ?_⟩
  intro E₀ d hE₀ hE₁
  obtain ⟨x₀c, Hc⟩ := Hc₀ E₀ d hE₀ hE₁
  have hEd : E₀ ≤ Real.exp d := by linarith
  refine ⟨max x₀c (Real.exp 1), ?_⟩
  intro Y ν hY x δ η a hx hδ0 hη0 hηE hδx ha ha1
  haveI := hY.isProbabilityMeasure
  have hxc : x₀c ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) < x := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hac : a₀c ≤ a := le_trans (le_max_left _ _) ha
  have hab : a₀b ≤ a := le_trans (le_max_right _ _) ha
  refine ⟨?_, ?_⟩
  · refine le_trans (Hb E₀ d hE₀ hEd Y ν hY D₀ x δ η a B hD₀ hx1 hδ0 hη0 hηE hδx hab hB) ?_
    have h1 : (0 : ℝ) ≤ Real.exp D₀ * Real.exp (-(2 * a)) := by positivity
    have h2 : Cb ≤ max Cc Cb := le_max_right _ _
    nlinarith
  · intro hΛ
    refine le_trans (Hc Ω' Y ν hY x δ η a hxc hδ0 hη0 hηE hδx hac ha1 hΛ) ?_
    have ha0 : (0 : ℝ) ≤ a := by linarith
    have hmin0 : (0 : ℝ)
        ≤ min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - ⌈a / 4⌉₊)) :=
      le_min zero_le_one (div_nonneg ha0 (Real.sqrt_nonneg _))
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hmin0

/-! ### The interpolation, for the Rademacher law

`RMF.GoodFamily` and `RMF.integral_rpow_le_of_goodFamily` for the Rademacher law.  The good-set
family is indexed over the half-open window `(w, w+1]` rather than over `Set.Ico 0 1`, because the
Rademacher measure bounds exclude `h = 0`; `RMF.chaosWindowShift_le_decomposition_Ioc` is the
decomposition in that spelling. -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **What the Rademacher interpolation reads a good-set family through**, on the window
`(w, w+1]`: `set a h` is the good set at level `a` and height `h`; the two measurability fields are
what the `h`-integral needs, `measure_bad_le` drives the geometric sum, and
`integral_restricted_le` is the chaos bound on the good set.  The bad set is indexed over a
half-open window because at `h = 0` Harper's `c(t, t_j - t, p)` is `3/2` rather than `1`. -/
structure GoodFamilyAdd {Ω : Type*} [MeasurableSpace Ω] (Y : ℕ → Ω → ℂ) (ν : Measure Ω)
    (x σ w : ℝ) (t n₀ : ℕ) (a₀ C₂ : ℝ) where
  /-- The good set at level `a` and height `h`. -/
  set : ℝ → ℝ → Set Ω
  measurableSet : ∀ a h, MeasurableSet (set a h)
  measurableSet_uncurry : ∀ a, MeasurableSet {p : Ω × ℝ | p.1 ∈ set a p.2}
  /-- The bad set is exponentially small in the level. -/
  measure_bad_le : ∀ a, a₀ ≤ a →
    ν.real {ω | ∃ h ∈ Set.Ioc w (w + 1), ω ∉ set a h} ≤ C₂ * Real.exp (-(2 * a))
  /-- The chaos, restricted to the good set. -/
  integral_restricted_le : ∀ a, a₀ ≤ a → 2 * ⌈a / 4⌉₊ ≤ t → n₀ ≤ t - ⌈a / 4⌉₊ →
    (∫ ω, restrictedChaosWindowShift
        (fun ω => squarefreeExtension fun p => Y p ω) x σ w (set a) ω ∂ν)
      ≤ C₂ * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))

/-- **The interpolation, for the Rademacher RMF.**  The `RMF.integral_rpow_le_of_goodSets`
instance at the chaos on `(w, w+1]`. -/
theorem integral_rpow_le_of_goodFamily_rademacher {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {x σ q w : ℝ} {t n₀ : ℕ} {a₀ C₁ C₂ : ℝ}
    (hx2 : (2 : ℝ) ≤ x) (hxgt1 : (1 : ℝ) < x) (_hσ0 : 0 ≤ σ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hZmean : (∫ ω, chaosWindowShift
        (fun ω => squarefreeExtension fun p => Y p ω) x σ w ω ∂ν) ≤ C₁)
    (hT1 : 2 * n₀ ≤ t) (hT2 : ⌈max a₀ 3⌉₊ ^ 2 ≤ t)
    (G : GoodFamilyAdd Y ν x σ w t n₀ a₀ C₂) :
    (∫ ω, chaosWindowShift
        (fun ω => squarefreeExtension fun p => Y p ω) x σ w ω ^ q ∂ν)
      ≤ 3 * (max 1 C₁ + max 1 (2 * C₂ * (max a₀ 3 + 1))
          + 2 * (max 1 (2 * C₂) * max 1 (2 * C₂)) + max 1 (2 * C₂) * max 1 C₁)
        * (1 + (1 - q) * Real.sqrt (t : ℝ)) ^ (-q) := by
  haveI := hY.isProbabilityMeasure
  exact integral_rpow_le_of_goodSets
    (Z := chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ w)
    (Rst := fun S => restrictedChaosWindowShift
      (fun ω => squarefreeExtension fun p => Y p ω) x σ w S)
    (win := Set.Ioc w (w + 1))
    (fun ω => chaosWindowShift_nonneg hx2 σ w ω)
    (integrable_chaosWindowShift_rademacher hY x σ w (by linarith))
    (fun S ω => restrictedChaosWindowShift_nonneg hxgt1 σ w S ω)
    (fun S hm hu =>
      integrable_restrictedChaosWindowShift_rademacher hY x σ w (by linarith) S hm hu)
    (fun S ω r m hrm => chaosWindowShift_le_decomposition_Ioc hxgt1 σ w S ω r m hrm)
    hq0 hq1 hC₁ hC₂ hZmean hT1 hT2
    G.set G.measurableSet G.measurableSet_uncurry G.measure_bad_le G.integral_restricted_le

/-! ### The `q`-th moment for the Rademacher law

The Rademacher counterpart of `RMF.exists_const_integral_chaosUnitShift_rpow_le`: the Steinhaus
construction is the template, and the four fields of `RMF.GoodFamilyAdd` differ only in which
theorems supply them. -/

/-- **The `q`-th moment of the chaos at a shifted abscissa, with `E₀` and `d` inside the
constants**: the Rademacher counterpart of
`RMF.exists_const_integral_chaosUnitShift_rpow_le_of_top`.  The good family is read with the top
`d` blocks dropped, with the constants of
`RMF.exists_const_harperGoodRangeAdd_bounds_of_scale_rademacher_raise_of_top`, so `D` and `C` do
not depend on `E₀` or `d`; `t = harperBlockCount D x / 4`, as in the form below. -/
theorem exists_const_integral_chaosUnitShift_rpow_le_rademacher_of_top :
    ∃ (D : ℕ) (C : ℝ), 0 < C ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → 10 * E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ x σ η q : ℝ, x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 1 →
          (∫ ω, chaosUnitShift
              (fun ω => squarefreeExtension fun p => Y p ω) x σ ω ^ q ∂ν)
            ≤ C * (1 + (1 - q) * Real.sqrt ((harperBlockCount D x / 4 : ℕ) : ℝ)) ^ (-q) := by
  obtain ⟨D, -, a₀c, Cc, B, hD, hCc, hB, H₂₀⟩ :=
    exists_const_harperGoodRangeAdd_bounds_of_scale_rademacher_raise_of_top (Ω' := Ω)
  obtain ⟨C₁, hC₁, H₁⟩ := exists_const_integral_chaosUnitShift_le_rademacher
  obtain ⟨x₂, hx₂⟩ :=
    exists_harperThreshold_of_blockCount D (4 * ⌈max (max a₀c 1) 3⌉₊ ^ 2)
  have hC₂ : (0 : ℝ) < Cc * Real.exp D := by positivity
  refine ⟨D,
    3 * (max 1 C₁ + max 1 (2 * (Cc * Real.exp D) * (max (max a₀c 1) 3 + 1))
      + 2 * (max 1 (2 * (Cc * Real.exp D)) * max 1 (2 * (Cc * Real.exp D)))
      + max 1 (2 * (Cc * Real.exp D)) * max 1 C₁), by positivity, ?_⟩
  intro E₀ d hE₀ hE₁
  obtain ⟨x₁, H₂⟩ := H₂₀ E₀ d hE₀ hE₁
  refine ⟨max (max x₁ x₂) 2, ?_⟩
  intro Y ν hY x σ η q hx hσ0 hη0 hηE hσ hq0 hq1
  have hxa : max x₁ x₂ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hxa
  obtain ⟨hxgt1, -, hcount⟩ := hx₂ x (le_trans (le_max_right _ _) hxa)
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) :=
    fun p => hY.measurable _ (p : Nat.Primes).2
  have hT2 : ⌈max (max a₀c 1) 3⌉₊ ^ 2 ≤ harperBlockCount D x / 4 := by
    refine (Nat.le_div_iff_mul_le (by norm_num)).2 ?_
    rw [Nat.mul_comm]
    exact hcount
  simp only [← chaosWindowShift_zero]
  refine integral_rpow_le_of_goodFamily_rademacher (n₀ := 0) (w := 0)
    (t := harperBlockCount D x / 4) (a₀ := max a₀c 1) (C₂ := Cc * Real.exp D)
    hY hx2 hxgt1 hσ0 hq0 hq1 hC₁ hC₂
    (by simp only [chaosWindowShift_zero]; exact H₁ Ω Y ν hY x σ hx2 hσ0)
    (by omega) hT2 ?_
  refine
    { set := fun a h => harperGoodRangeAdd Y B (harperDt D h) x σ
        (a + ((harperDt D h - D : ℕ) : ℝ))
        (harperBlockCount (harperDt D h) x - d) h
      measurableSet := fun a h => measurableSet_harperGoodRangeAdd hYm _ _ _ _ _ _ _
      measurableSet_uncurry := fun a =>
        measurableSet_harperGoodRangeAdd_raise_uncurry hYm B σ x a D d
      measure_bad_le := ?_
      integral_restricted_le := ?_ }
  · intro a ha
    have hac : a₀c ≤ a := le_trans (le_max_left _ _) ha
    have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
    rw [show (0 : ℝ) + 1 = 1 by norm_num]
    exact (H₂ Y ν hY x σ η a hxx₁ hσ0 hη0 hηE hσ hac ha1).1
  · intro a ha h2 _
    have hac : a₀c ≤ a := le_trans (le_max_left _ _) ha
    have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
    have ha0 : (0 : ℝ) ≤ a := by linarith
    have hR1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
    have hRm : 8 * ⌈a / 4⌉₊ ≤ harperBlockCount D x := by omega
    have hRmR : 8 * (⌈a / 4⌉₊ : ℝ) ≤ (harperBlockCount D x : ℝ) := by exact_mod_cast hRm
    have hbound := (H₂ Y ν hY x σ η a hxx₁ hσ0 hη0 hηE hσ hac ha1).2 hRmR
    have htmR : ((harperBlockCount D x / 4 : ℕ) : ℝ) ≤ (harperBlockCount D x : ℝ) := by
      exact_mod_cast Nat.div_le_self _ _
    have hposN : ⌈a / 4⌉₊ < harperBlockCount D x / 4 := by omega
    have hpos : (0 : ℝ) < ((harperBlockCount D x / 4 : ℕ) : ℝ) - (⌈a / 4⌉₊ : ℝ) := by
      have h1 : ((⌈a / 4⌉₊ : ℕ) : ℝ) < ((harperBlockCount D x / 4 : ℕ) : ℝ) := by
        exact_mod_cast hposN
      linarith
    have hmin0 : (0 : ℝ)
        ≤ min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - (⌈a / 4⌉₊ : ℝ))) :=
      le_min zero_le_one (div_nonneg ha0 (Real.sqrt_nonneg _))
    have hmin : min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - (⌈a / 4⌉₊ : ℝ)))
        ≤ min 1 (a / Real.sqrt (((harperBlockCount D x / 4 : ℕ) : ℝ)
          - (⌈a / 4⌉₊ : ℝ))) := by
      gcongr
    have hCle : Cc ≤ Cc * Real.exp D := by
      have h1 : (1 : ℝ) ≤ Real.exp D := Real.one_le_exp (Nat.cast_nonneg _)
      nlinarith
    simp only [restrictedChaosWindowShift_zero]
    calc (∫ ω, restrictedChaosUnitShift
            (fun ω => squarefreeExtension fun p => Y p ω) x σ
            (fun h => harperGoodRangeAdd Y B (harperDt D h) x σ
              (a + ((harperDt D h - D : ℕ) : ℝ))
              (harperBlockCount (harperDt D h) x - d) h) ω ∂ν)
        ≤ Cc * min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - (⌈a / 4⌉₊ : ℝ))) :=
          hbound
      _ ≤ Cc * Real.exp D
            * min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - (⌈a / 4⌉₊ : ℝ))) :=
          mul_le_mul_of_nonneg_right hCle hmin0
      _ ≤ Cc * Real.exp D
            * min 1 (a / Real.sqrt (((harperBlockCount D x / 4 : ℕ) : ℝ)
              - (⌈a / 4⌉₊ : ℝ))) :=
          mul_le_mul_of_nonneg_left hmin hC₂.le

/-- **The `q`-th moment of the chaos at a shifted abscissa, for the Rademacher RMF.**
`E[(Z²)^q] ≪ (1 + (1-q)√t)^{-q}` with `t = harperBlockCount D x / 4`, uniformly in `q ∈ [0,1]`,
`σ ≥ 0` with `|σ|ℓog x ≤ η ≤ E₀`, and `x ≥ x₀`; `D`, `x₀` and `C` depend on `E₀`.  The good set on
band `k` is read at level `a + k`, since a fixed level leaves `⌊ℓogℓog x⌋ + 1` in the bad-set
constant, and `t` is quartered because `RMF.GoodFamilyAdd.integral_restricted_le` bounds the
level only through `2⌈a/4⌉ ≤ t`.  The drop is `d = ⌈10E₀⌉`. -/
theorem exists_const_integral_chaosUnitShift_rpow_le_rademacher (E₀ : ℝ)
    (hE₀ : 0 ≤ E₀) :
    ∃ (D : ℕ) (x₀ C : ℝ), 0 < C ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ x σ η q : ℝ, x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 1 →
          (∫ ω, chaosUnitShift
              (fun ω => squarefreeExtension fun p => Y p ω) x σ ω ^ q ∂ν)
            ≤ C * (1 + (1 - q) * Real.sqrt ((harperBlockCount D x / 4 : ℕ) : ℝ)) ^ (-q) := by
  obtain ⟨D, -, x₁, a₀c, Cc, B, hD, hCc, hB, H₂⟩ :=
    exists_const_harperGoodRangeAdd_bounds_of_scale_rademacher_raise_of_drop (Ω' := Ω)
      E₀ hE₀ ⌈10 * E₀⌉₊ (by
        have h1 : (10 : ℝ) * E₀ ≤ ((⌈10 * E₀⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
        linarith [Real.add_one_le_exp ((⌈10 * E₀⌉₊ : ℕ) : ℝ)])
  obtain ⟨C₁, hC₁, H₁⟩ := exists_const_integral_chaosUnitShift_le_rademacher
  obtain ⟨x₂, hx₂⟩ :=
    exists_harperThreshold_of_blockCount D (4 * ⌈max (max a₀c 1) 3⌉₊ ^ 2)
  have hC₂ : (0 : ℝ) < Cc * Real.exp D := by positivity
  refine ⟨D, max (max x₁ x₂) 2,
    3 * (max 1 C₁ + max 1 (2 * (Cc * Real.exp D) * (max (max a₀c 1) 3 + 1))
      + 2 * (max 1 (2 * (Cc * Real.exp D)) * max 1 (2 * (Cc * Real.exp D)))
      + max 1 (2 * (Cc * Real.exp D)) * max 1 C₁), by positivity, ?_⟩
  intro Y ν hY x σ η q hx hσ0 hη0 hηE hσ hq0 hq1
  have hxa : max x₁ x₂ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hxa
  obtain ⟨hxgt1, -, hcount⟩ := hx₂ x (le_trans (le_max_right _ _) hxa)
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) :=
    fun p => hY.measurable _ (p : Nat.Primes).2
  have hT2 : ⌈max (max a₀c 1) 3⌉₊ ^ 2 ≤ harperBlockCount D x / 4 := by
    refine (Nat.le_div_iff_mul_le (by norm_num)).2 ?_
    rw [Nat.mul_comm]
    exact hcount
  simp only [← chaosWindowShift_zero]
  refine integral_rpow_le_of_goodFamily_rademacher (n₀ := 0) (w := 0)
    (t := harperBlockCount D x / 4) (a₀ := max a₀c 1) (C₂ := Cc * Real.exp D)
    hY hx2 hxgt1 hσ0 hq0 hq1 hC₁ hC₂
    (by simp only [chaosWindowShift_zero]; exact H₁ Ω Y ν hY x σ hx2 hσ0)
    (by omega) hT2 ?_
  refine
    { set := fun a h => harperGoodRangeAdd Y B (harperDt D h) x σ
        (a + ((harperDt D h - D : ℕ) : ℝ))
        (harperBlockCount (harperDt D h) x - ⌈10 * E₀⌉₊) h
      measurableSet := fun a h => measurableSet_harperGoodRangeAdd hYm _ _ _ _ _ _ _
      measurableSet_uncurry := fun a =>
        measurableSet_harperGoodRangeAdd_raise_uncurry hYm B σ x a D ⌈10 * E₀⌉₊
      measure_bad_le := ?_
      integral_restricted_le := ?_ }
  · intro a ha
    have hac : a₀c ≤ a := le_trans (le_max_left _ _) ha
    have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
    rw [show (0 : ℝ) + 1 = 1 by norm_num]
    exact (H₂ Y ν hY x σ η a hxx₁ hσ0 hη0 hηE hσ hac ha1).1
  · intro a ha h2 _
    have hac : a₀c ≤ a := le_trans (le_max_left _ _) ha
    have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
    have ha0 : (0 : ℝ) ≤ a := by linarith
    have hR1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
    have hRm : 8 * ⌈a / 4⌉₊ ≤ harperBlockCount D x := by omega
    have hRmR : 8 * (⌈a / 4⌉₊ : ℝ) ≤ (harperBlockCount D x : ℝ) := by exact_mod_cast hRm
    have hbound := (H₂ Y ν hY x σ η a hxx₁ hσ0 hη0 hηE hσ hac ha1).2 hRmR
    have htmR : ((harperBlockCount D x / 4 : ℕ) : ℝ) ≤ (harperBlockCount D x : ℝ) := by
      exact_mod_cast Nat.div_le_self _ _
    have hposN : ⌈a / 4⌉₊ < harperBlockCount D x / 4 := by omega
    have hpos : (0 : ℝ) < ((harperBlockCount D x / 4 : ℕ) : ℝ) - (⌈a / 4⌉₊ : ℝ) := by
      have h1 : ((⌈a / 4⌉₊ : ℕ) : ℝ) < ((harperBlockCount D x / 4 : ℕ) : ℝ) := by
        exact_mod_cast hposN
      linarith
    have hmin0 : (0 : ℝ)
        ≤ min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - (⌈a / 4⌉₊ : ℝ))) :=
      le_min zero_le_one (div_nonneg ha0 (Real.sqrt_nonneg _))
    have hmin : min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - (⌈a / 4⌉₊ : ℝ)))
        ≤ min 1 (a / Real.sqrt (((harperBlockCount D x / 4 : ℕ) : ℝ)
          - (⌈a / 4⌉₊ : ℝ))) := by
      gcongr
    have hCle : Cc ≤ Cc * Real.exp D := by
      have h1 : (1 : ℝ) ≤ Real.exp D := Real.one_le_exp (Nat.cast_nonneg _)
      nlinarith
    simp only [restrictedChaosWindowShift_zero]
    calc (∫ ω, restrictedChaosUnitShift
            (fun ω => squarefreeExtension fun p => Y p ω) x σ
            (fun h => harperGoodRangeAdd Y B (harperDt D h) x σ
              (a + ((harperDt D h - D : ℕ) : ℝ))
              (harperBlockCount (harperDt D h) x - ⌈10 * E₀⌉₊) h) ω ∂ν)
        ≤ Cc * min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - (⌈a / 4⌉₊ : ℝ))) :=
          hbound
      _ ≤ Cc * Real.exp D
            * min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - (⌈a / 4⌉₊ : ℝ))) :=
          mul_le_mul_of_nonneg_right hCle hmin0
      _ ≤ Cc * Real.exp D
            * min 1 (a / Real.sqrt (((harperBlockCount D x / 4 : ℕ) : ℝ)
              - (⌈a / 4⌉₊ : ℝ))) :=
          mul_le_mul_of_nonneg_left hmin hC₂.le

/-- **The `q`-th moment of the chaos for the Rademacher law, read at `ℓogℓog x`**: the block
count and the quartering leave the statement, as `Reduction/` consumes it (compare
`RMF.exists_const_integral_chaosUnit_rpow_le` in `Reduction/Upper.lean`).  With the count
quartered, `Λ ≤ 4t` fails, so `RMF.rpow_neg_target_le_of_sq_le` is used at `k = 4` rather than
`RMF.rpow_neg_target_le_of_quarter_le`, at a factor `4` rather than `2`. -/
theorem exists_const_integral_chaosUnitShift_rpow_le_loglog_rademacher (E₀ : ℝ)
    (hE₀ : 0 ≤ E₀) :
    ∃ x₀ C : ℝ, 0 < C ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ x σ η q : ℝ, x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 1 →
          (∫ ω, chaosUnitShift
              (fun ω => squarefreeExtension fun p => Y p ω) x σ ω ^ q ∂ν)
            ≤ C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  obtain ⟨D, x₀, C, hC, H⟩ :=
    exists_const_integral_chaosUnitShift_rpow_le_rademacher (Ω := Ω) E₀ hE₀
  refine ⟨max (max x₀ 2) (Real.exp (Real.exp (8 * ((D : ℝ) + 4)))), 4 * C, by linarith, ?_⟩
  intro Y ν hY x σ η q hx hσ0 hη0 hηE hσ hq0 hq1
  have hxa : max x₀ 2 ≤ x := le_trans (le_max_left _ _) hx
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hxa
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hxa
  have hexp : Real.exp (Real.exp (8 * ((D : ℝ) + 4))) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : Real.exp (8 * ((D : ℝ) + 4)) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hexp
  have hlogx0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hlogx
  have hL : 8 * ((D : ℝ) + 4) ≤ Real.log (Real.log x) :=
    (Real.le_log_iff_exp_le hlogx0).2 hlogx
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  have hD : (D : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hcast : (harperBlockCount D x : ℝ)
      = (⌊Real.log (Real.log x)⌋₊ : ℝ) - (D : ℝ) := cast_harperBlockCount hD
  have hfl : Real.log (Real.log x) < (⌊Real.log (Real.log x)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  -- `ℕ`-division loses at most `3`
  have hmdiv : harperBlockCount D x ≤ 4 * (harperBlockCount D x / 4) + 3 := by omega
  have hmdivR : (harperBlockCount D x : ℝ)
      ≤ 4 * ((harperBlockCount D x / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast hmdiv
  have htar := rpow_neg_target_le_of_sq_le (k := 4)
    (t := ((harperBlockCount D x / 4 : ℕ) : ℝ)) (Λ := Real.log (Real.log x))
    (by norm_num) (by norm_num; linarith) hq0 hq1
  calc (∫ ω, chaosUnitShift
          (fun ω => squarefreeExtension fun p => Y p ω) x σ ω ^ q ∂ν)
      ≤ C * (1 + (1 - q)
          * Real.sqrt ((harperBlockCount D x / 4 : ℕ) : ℝ)) ^ (-q) :=
        H Y ν hY x σ η q hxx₀ hσ0 hη0 hηE hσ hq0 hq1
    _ ≤ C * (4 * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)) :=
        mul_le_mul_of_nonneg_left htar hC.le
    _ = 4 * C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by ring

end RMF
