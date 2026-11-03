/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.BlockComparison
import RMF.Probability.TiltTransfer

/-!
# Shifting the block index

`RMF.blockScale θ j = exp(exp(j + θ))`, so **advancing the block index by `r` is the same as
advancing the offset by `r`**: `blockScale θ (j + r) = blockScale (θ + r) j`, and likewise for
`RMF.primeBlockSub`.

Two consequences make the free start of the restricted first moment (Hamdan's Proposition 2.1)
cheap.

* The walk started at block `r` is again a *block walk*, at offset `ϑ + r`. So Proposition 5
  applies to it directly — no new comparison, no new Gaussian family.
* **The tilt does not move.** `blockCutoff (ϑ + r) (n − r) = blockCutoff ϑ n` whenever `r ≤ n`,
  because both are `⌊blockScale ϑ (n+1)⌋₊ + 1`. The measure tilting the shifted problem is
  *literally the same measure* as the one tilting the original, not merely comparable to it. That
  is what stops the shift from costing anything.

Together with `RMF.subset_barrierEvent_shift` this reduces Hamdan's `G_A` — constrained only on
`[A/4, t]` — to a Proposition 5 barrier event on `[1, t − A/4]`, at a widened `a` that is still
`O(a)`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RMF

/-! ### The shift identities -/

/-- Advancing the block index is advancing the offset. -/
lemma blockScale_add (θ : ℝ) (j r : ℕ) : blockScale θ (j + r) = blockScale (θ + r) j := by
  unfold blockScale
  congr 2
  push_cast
  ring

/-- The same, for the blocks of primes themselves. -/
lemma primeBlockSub_add (θ : ℝ) (j r : ℕ) :
    primeBlockSub θ (j + r) = primeBlockSub (θ + r) j := by
  unfold primeBlockSub
  rw [show j + r + 1 = j + 1 + r from by omega, blockScale_add]

/-- **The tilt does not move under a shift.**  Both sides are `⌊blockScale ϑ (n+1)⌋₊ + 1`. -/
lemma blockCutoff_add {θ : ℝ} {n r : ℕ} (hrn : r ≤ n) :
    blockCutoff (θ + r) (n - r) = blockCutoff θ n := by
  unfold blockCutoff
  rw [← blockScale_add, show n - r + 1 + r = n + 1 from by omega]

/-! ### The free-start event, inside a Proposition 5 event

Shifting the tube `[-a - c·j, a + j + hf j]` to start at `r` and re-centring at `walk_r` gives
endpoints that are *differences* of the original ones, and those are again of the form
`[-a' - c·m, a' + m + hf(m+r)]`, at a widened height `a'` that is `O(a)` once `r ≤ a/4 + 1` and
`|hf r| ≤ 10 log r`.  The remaining obstruction is that Proposition 5 asks for
`|hf j| ≤ 10 log j`, while the shifted envelope only satisfies `|hf(j+r)| ≤ 10 log (j+r)`.  The gap
is `10 log((m+r)/m) ≤ 10 log(1+r)`, an additive constant, and it is absorbed into `a'` — which is
why `RMF.shiftedHeight` carries a `10 log(1+r)` term besides `2a + (c+1)r + |hf r|`.  So
Proposition 5 accepts the shifted problem, and its conclusion `≪ a'/√(n-r)` is `≍ a/√n`. -/

/-- The widened barrier height for the shifted problem. -/
noncomputable def shiftedHeight (a c : ℝ) (hf : ℕ → ℝ) (r : ℕ) : ℝ :=
  2 * a + (c + 1) * r + |hf r| + 10 * Real.log (1 + r)

/-- **Hamdan's good-point event sits inside a Proposition 5 barrier event for the shifted walk.**

The left-hand event constrains only `[r, n]`, as `G_A` does.  The right-hand one is of exactly the
shape Proposition 5 accepts (`RMF.exists_const_proposition5_steinhaus_of_le`) — lower barrier
`-a' - c·m`, upper barrier `a' + m + hf' m` with `|hf' m| ≤ 10 log m` — at
`a' = RMF.shiftedHeight a c hf r`. -/
lemma freeStart_subset_barrierEvent {Ω : Type*} {X : ℕ → Ω → ℝ} {n r : ℕ} {a c : ℝ}
    {hf : ℕ → ℝ} (hrn : r ≤ n)
    (hhf : ∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) :
    {ω | ∀ j, r ≤ j → j ≤ n →
        walk X j ω ∈ Set.Icc (-a - c * (j : ℝ)) (a + (j : ℝ) + hf j)}
      ⊆ barrierEvent (fun m => X (m + r)) (n - r)
          (fun m => -shiftedHeight a c hf r - c * (m : ℝ))
          (fun m => shiftedHeight a c hf r + (m : ℝ) + 10 * Real.log m) := by
  intro ω hω m hm1 hmn
  have hr := hω r le_rfl hrn
  have hmr := hω (m + r) (Nat.le_add_left r m) (by omega)
  have hm0 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hlog1r : (0 : ℝ) ≤ Real.log (1 + (r : ℝ)) := Real.log_nonneg (by linarith)
  -- `log(m+r) ≤ log m + log(1+r)`, because `m + r ≤ m(1+r)` once `m ≥ 1`
  have hsplit : Real.log ((m : ℝ) + (r : ℝ)) ≤ Real.log m + Real.log (1 + (r : ℝ)) := by
    have hprod : (m : ℝ) + (r : ℝ) ≤ (m : ℝ) * (1 + (r : ℝ)) := by nlinarith
    calc Real.log ((m : ℝ) + (r : ℝ)) ≤ Real.log ((m : ℝ) * (1 + (r : ℝ))) :=
          Real.log_le_log (by linarith) hprod
      _ = Real.log m + Real.log (1 + (r : ℝ)) := Real.log_mul (by linarith) (by linarith)
  have hhfmr : hf (m + r) ≤ 10 * Real.log m + 10 * Real.log (1 + (r : ℝ)) := by
    have h := hhf (m + r) (by omega) (by omega)
    have hc : Real.log (((m + r : ℕ) : ℝ)) ≤ Real.log m + Real.log (1 + (r : ℝ)) := by
      push_cast
      exact hsplit
    calc hf (m + r) ≤ |hf (m + r)| := le_abs_self _
      _ ≤ 10 * Real.log (((m + r : ℕ) : ℝ)) := h
      _ ≤ 10 * (Real.log m + Real.log (1 + (r : ℝ))) := by linarith
      _ = 10 * Real.log m + 10 * Real.log (1 + (r : ℝ)) := by ring
  have hhfr : hf r ≤ |hf r| := le_abs_self _
  have habs : (0 : ℝ) ≤ |hf r| := abs_nonneg _
  have hshift : walk (fun i => X (i + r)) m ω = walk X (m + r) ω - walk X r ω := by
    rw [walk_shift X r m, Nat.add_comm r m]
  rw [Set.mem_Icc] at hr hmr ⊢
  rw [hshift, shiftedHeight]
  push_cast at hr hmr ⊢
  exact ⟨by linarith [hr.2, hmr.1], by linarith [hr.1, hmr.2]⟩

/-- The widened height is `O(a)`: `log r \le r` and `log(1+r) \le r` turn every term into a
multiple of `a` once `r \le a/4 + 1` and `a \ge 1`. -/
lemma shiftedHeight_le {a c : ℝ} {hf : ℕ → ℝ} {r : ℕ} (ha : 1 ≤ a) (hc : 0 ≤ c)
    (hr1 : 1 ≤ r) (hr : (r : ℝ) ≤ a / 4 + 1) (hhf : |hf r| ≤ 10 * Real.log r) :
    shiftedHeight a c hf r ≤ (29 + 2 * c) * a := by
  have hr0 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hlogr : Real.log (r : ℝ) ≤ (r : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (r : ℝ) by linarith)
    linarith
  have hlog1r : Real.log (1 + (r : ℝ)) ≤ (r : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + (r : ℝ) by linarith)
    linarith
  have hr5 : (r : ℝ) ≤ 5 * a / 4 := by linarith
  have hca : (0 : ℝ) ≤ c * a := mul_nonneg hc (by linarith)
  have hkey : (c + 21) * (r : ℝ) ≤ (c + 21) * (5 * a / 4) :=
    mul_le_mul_of_nonneg_left hr5 (by linarith)
  rw [shiftedHeight]
  linarith

/-- `min 1 u ≤ K · min 1 v` when `u ≤ K v` and `K ≥ 1`: the `min` caps at `1 ≤ K`, so inflating
the argument by `K` inflates the capped value by at most `K`.  This is what lets Proposition 5's
conclusion at the widened `a'` be read back as a conclusion at `a`. -/
lemma min_one_le_mul_min_one {K u v : ℝ} (hK : 1 ≤ K) (huv : u ≤ K * v) :
    min 1 u ≤ K * min 1 v := by
  rcases le_or_gt 1 v with h | h
  · rw [min_eq_left h]
    linarith [min_le_left (1 : ℝ) u]
  · rw [min_eq_right h.le]
    exact le_trans (min_le_right _ _) huv

/-- **The restricted first moment's probabilistic core, at a general tilt scale**: for `0 ≤ σ`, a
tilt `≤ η ≤ E₀`, a free start `1 ≤ r ≤ a/4 + 1` and `|h(j)| ≤ 10 log j`, the walk stays in
`[-a - Bj, a + j + h(j)]` on `[r, n]` with tilted probability at most `C·min{1, a/√(n-r)}`, at the
slope `B = RMF.blockSlopeOf E₀ 125`.  Nothing about the shift sees the tilt, so this is
`RMF.exists_const_proposition5_steinhaus_of_le`'s upper half read through the shift. -/
theorem exists_const_freeStart_barrier_le_of_le (E₀ : ℝ) (hE₀ : 0 ≤ E₀) :
    ∃ (ϑ₀ : ℝ) (n₀ : ℕ) (a₀ C : ℝ), 0 < C ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (ϑ σ η a : ℝ) (n r : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          ϑ₀ ≤ ϑ → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η →
          a₀ ≤ a → 1 ≤ a → n₀ ≤ n - r → 1 ≤ r → r ≤ n → (r : ℝ) ≤ a / 4 + 1 →
          (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω) (blockCutoff ϑ n) s ν)
                {ω | ∀ j, r ≤ j → j ≤ n →
                  walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                    localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - blockSlopeOf E₀ 125 * (j : ℝ))
                        (a + (j : ℝ) + hf j)}).toReal
              ≤ C * min 1 (a / Real.sqrt ((n : ℝ) - r)) := by
  obtain ⟨ϑ₀, n₀, a₀, α, A, hα, hA, H⟩ := exists_const_proposition5_steinhaus_of_le E₀ hE₀
  have hc : (0 : ℝ) ≤ blockSlopeOf E₀ 125 := (blockSlopeOf_pos E₀ 125).le
  refine ⟨ϑ₀, n₀, a₀, A * (29 + 2 * blockSlopeOf E₀ 125), by positivity, ?_⟩
  intro Ω' _ Y ν hY ϑ σ η a n r s hf hϑ hres hσ0 hη0 hηE hσ ha₀ ha1 hn₀ hr1 hrn
    hra hhf
  have hspos : 0 < s.re := by rw [hres]; linarith
  haveI := hY.isProbabilityMeasure_tiltedMeasure (blockCutoff ϑ n) hspos
  set c := blockSlopeOf E₀ 125 with hcdef
  set a' := shiftedHeight a c hf r with ha'def
  have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hscale : blockScale (ϑ + r) (n - r + 1) = blockScale ϑ (n + 1) := by
    rw [← blockScale_add, show n - r + 1 + r = n + 1 from by omega]
  have ha'0 : a ≤ a' := by
    rw [ha'def, shiftedHeight]
    have h1 : (0 : ℝ) ≤ (c + 1) * (r : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ |hf r| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ Real.log (1 + (r : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hp1 : ϑ₀ ≤ ϑ + (r : ℝ) := by linarith
  have hp2 : |σ| * Real.log (blockScale (ϑ + r) (n - r + 1)) ≤ η := by
    rw [hscale]; exact hσ
  have hp3 : a₀ ≤ a' := by linarith
  have hp4 : ∀ j : ℕ, 1 ≤ j → j ≤ n - r →
      |(fun m : ℕ => 10 * Real.log m) j| ≤ 10 * Real.log j := by
    intro j hj1 _
    have hl : (0 : ℝ) ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj1)
    simp only
    rw [abs_of_nonneg (by linarith)]
  have hP5 := (H Ω' Y ν hY (ϑ + r) σ η a' (n - r) s (fun m => 10 * Real.log m)
    hp1 hres hσ0 hη0 hηE hp2 hp3 hn₀ hp4).2
  rw [blockCutoff_add hrn, Nat.cast_sub hrn] at hP5
  have hXshift : (fun m (ω : Ω') => ∑ p ∈ primeBlockSub ϑ (m + r),
        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
      = fun m ω => ∑ p ∈ primeBlockSub (ϑ + r) m,
        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω) := by
    funext m
    rw [primeBlockSub_add]
  have hsub := freeStart_subset_barrierEvent (X := fun m (ω : Ω') => ∑ p ∈ primeBlockSub ϑ m,
    localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) (a := a) (c := c) (hf := hf) hrn hhf
  rw [hXshift] at hsub
  have hmono := measure_mono (μ := tiltedMeasure
    (fun ω => compMultExtension fun p => Y p ω) (blockCutoff ϑ n) s ν) hsub
  refine le_trans (le_trans (ENNReal.toReal_mono (measure_ne_top _ _) hmono) hP5) ?_
  have hheight : a' ≤ (29 + 2 * c) * a :=
    shiftedHeight_le ha1 hc hr1 hra (hhf r hr1 hrn)
  have hK : (1 : ℝ) ≤ 29 + 2 * c := by linarith
  have hsq : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) - r) := Real.sqrt_nonneg _
  have hdiv : a' / Real.sqrt ((n : ℝ) - r)
      ≤ (29 + 2 * c) * (a / Real.sqrt ((n : ℝ) - r)) := by
    rw [← mul_div_assoc]
    gcongr
  have h1 := min_one_le_mul_min_one hK hdiv
  calc A * min 1 (a' / Real.sqrt ((n : ℝ) - r))
      ≤ A * ((29 + 2 * c) * min 1 (a / Real.sqrt ((n : ℝ) - r))) :=
        mul_le_mul_of_nonneg_left h1 hA.le
    _ = A * (29 + 2 * c) * min 1 (a / Real.sqrt ((n : ℝ) - r)) := by ring

/-- **The restricted first moment's probabilistic core at a general tilt, with absolute
constants.**  The good set is constrained on `[r, n-d]` while the tilt stays at the top block `n`,
which buys `η ≤ e^d`.  This is `RMF.exists_const_proposition5_steinhaus_of_top`'s upper half read
through the shift; the two subtractions commute, `n - r - d = (n - d) - r`. -/
theorem exists_const_freeStart_barrier_le_of_top :
    ∃ (ϑ₀ : ℝ) (n₀ : ℕ) (a₀ C : ℝ), 0 < C ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (ϑ σ η a : ℝ) (d n r : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          ϑ₀ ≤ ϑ → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ Real.exp d →
          |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η →
          a₀ ≤ a → 1 ≤ a → 1 ≤ r → r ≤ n → 2 * d ≤ n - r → n₀ ≤ n - r - d →
          (r : ℝ) ≤ a / 4 + 1 →
          (∀ j, 1 ≤ j → j ≤ n - d → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω) (blockCutoff ϑ n) s ν)
                {ω | ∀ j, r ≤ j → j ≤ n - d →
                  walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                    localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - blockSlope 125 * (j : ℝ))
                        (a + (j : ℝ) + hf j)}).toReal
              ≤ C * min 1 (a / Real.sqrt (((n - d : ℕ) : ℝ) - r)) := by
  obtain ⟨ϑ₀, n₀, a₀, α, A, hα, hA, H⟩ := exists_const_proposition5_steinhaus_of_top
  have hc : (0 : ℝ) ≤ blockSlope 125 := (blockSlope_pos 125).le
  refine ⟨ϑ₀, n₀, a₀, A * (29 + 2 * blockSlope 125), by positivity, ?_⟩
  intro Ω' _ Y ν hY ϑ σ η a d n r s hf hϑ hres hσ0 hη0 hηE hσ ha₀ ha1 hr1 hrn hdn
    hn₀ hra hhf
  have hspos : 0 < s.re := by rw [hres]; linarith
  haveI := hY.isProbabilityMeasure_tiltedMeasure (blockCutoff ϑ n) hspos
  have hrnd : r ≤ n - d := by omega
  set c := blockSlope 125 with hcdef
  set a' := shiftedHeight a c hf r with ha'def
  have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hscale : blockScale (ϑ + r) (n - r + 1) = blockScale ϑ (n + 1) := by
    rw [← blockScale_add, show n - r + 1 + r = n + 1 from by omega]
  have ha'0 : a ≤ a' := by
    rw [ha'def, shiftedHeight]
    have h1 : (0 : ℝ) ≤ (c + 1) * (r : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ |hf r| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ Real.log (1 + (r : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hp1 : ϑ₀ ≤ ϑ + (r : ℝ) := by linarith
  have hp2 : |σ| * Real.log (blockScale (ϑ + r) (n - r + 1)) ≤ η := by
    rw [hscale]; exact hσ
  have hp3 : a₀ ≤ a' := by linarith
  have hp4 : ∀ j : ℕ, 1 ≤ j → j ≤ n - r - d →
      |(fun m : ℕ => 10 * Real.log m) j| ≤ 10 * Real.log j := by
    intro j hj1 _
    have hl : (0 : ℝ) ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj1)
    simp only
    rw [abs_of_nonneg (by linarith)]
  have hP5 := (H Ω' Y ν hY (ϑ + r) σ η a' d (n - r) s (fun m => 10 * Real.log m)
    hp1 hres hσ0 hη0 hηE hp2 hp3 hdn hn₀ hp4).2
  have hcast : ((n - r - d : ℕ) : ℝ) = ((n - d : ℕ) : ℝ) - (r : ℝ) := by
    rw [show n - r - d = n - d - r from by omega, Nat.cast_sub hrnd]
  rw [blockCutoff_add hrn, hcast] at hP5
  have hXshift : (fun m (ω : Ω') => ∑ p ∈ primeBlockSub ϑ (m + r),
        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
      = fun m ω => ∑ p ∈ primeBlockSub (ϑ + r) m,
        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω) := by
    funext m
    rw [primeBlockSub_add]
  have hsub := freeStart_subset_barrierEvent (X := fun m (ω : Ω') => ∑ p ∈ primeBlockSub ϑ m,
    localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) (a := a) (c := c) (hf := hf) hrnd hhf
  rw [hXshift, show n - d - r = n - r - d from by omega] at hsub
  have hmono := measure_mono (μ := tiltedMeasure
    (fun ω => compMultExtension fun p => Y p ω) (blockCutoff ϑ n) s ν) hsub
  refine le_trans (le_trans (ENNReal.toReal_mono (measure_ne_top _ _) hmono) hP5) ?_
  have hheight : a' ≤ (29 + 2 * c) * a :=
    shiftedHeight_le ha1 hc hr1 hra (hhf r hr1 hrnd)
  have hK : (1 : ℝ) ≤ 29 + 2 * c := by linarith
  have hsq : (0 : ℝ) ≤ Real.sqrt (((n - d : ℕ) : ℝ) - r) := Real.sqrt_nonneg _
  have hdiv : a' / Real.sqrt (((n - d : ℕ) : ℝ) - r)
      ≤ (29 + 2 * c) * (a / Real.sqrt (((n - d : ℕ) : ℝ) - r)) := by
    rw [← mul_div_assoc]
    gcongr
  have h1 := min_one_le_mul_min_one hK hdiv
  calc A * min 1 (a' / Real.sqrt (((n - d : ℕ) : ℝ) - r))
      ≤ A * ((29 + 2 * c) * min 1 (a / Real.sqrt (((n - d : ℕ) : ℝ) - r))) :=
        mul_le_mul_of_nonneg_left h1 hA.le
    _ = A * (29 + 2 * c) * min 1 (a / Real.sqrt (((n - d : ℕ) : ℝ) - r)) := by ring

/-! ### The block walk is an annulus sum

The cumulant machinery works with `∑_{p ∈ T \ S}` — the primes between two cutoffs — while the
barrier machinery works with `walk` of the block family.  They are the same sum, and the bridge is
one atomic fact plus a telescoping induction.

*The atomic fact*: a single block is the difference of two prime-below sets, because
`p ∈ primesBelowSub (⌊x⌋₊ + 1) ↔ p ≤ x`.  *The induction*: adjacent annuli glue, which is the set
identity `(B \ A) ∪ (A \ C) = B \ C` for `C ⊆ A ⊆ B`. -/

/-- `p` is below `⌊x⌋₊ + 1` exactly when `p ≤ x`. -/
lemma mem_primesBelowSub_floor {x : ℝ} (hx : 0 ≤ x) {p : Nat.Primes} :
    p ∈ primesBelowSub (⌊x⌋₊ + 1) ↔ ((p : ℕ) : ℝ) ≤ x := by
  rw [mem_primesBelowSub, Nat.mem_primesBelow]
  constructor
  · rintro ⟨h, -⟩
    exact (Nat.le_floor_iff hx).1 (Nat.lt_succ_iff.1 h)
  · intro h
    exact ⟨Nat.lt_succ_iff.2 ((Nat.le_floor_iff hx).2 h), p.2⟩

/-- **A block is a difference of two prime-below sets.** -/
lemma primeBlockSub_eq_sdiff (θ : ℝ) (m : ℕ) :
    primeBlockSub θ m
      = primesBelowSub (⌊blockScale θ (m + 1)⌋₊ + 1)
          \ primesBelowSub (⌊blockScale θ m⌋₊ + 1) := by
  ext p
  rw [mem_primeBlockSub, Finset.mem_sdiff,
    mem_primesBelowSub_floor (blockScale_pos θ (m + 1)).le,
    mem_primesBelowSub_floor (blockScale_pos θ m).le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, not_le.2 h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨not_le.1 h2, h1⟩

/-- Prime-below sets grow with the cutoff. -/
lemma primesBelowSub_floor_mono {θ : ℝ} {a b : ℕ} (h : a ≤ b) :
    primesBelowSub (⌊blockScale θ a⌋₊ + 1) ⊆ primesBelowSub (⌊blockScale θ b⌋₊ + 1) := by
  intro p hp
  rw [mem_primesBelowSub_floor (blockScale_pos θ a).le] at hp
  rw [mem_primesBelowSub_floor (blockScale_pos θ b).le]
  exact le_trans hp (blockScale_mono θ h)

/-- **The blocks below `j` telescope to the annulus between the cutoffs `0` and `j`.** -/
lemma biUnion_primeBlockSub_eq_sdiff (θ : ℝ) (j : ℕ) :
    (Finset.range j).biUnion (primeBlockSub θ)
      = primesBelowSub (⌊blockScale θ j⌋₊ + 1) \ primesBelowSub (⌊blockScale θ 0⌋₊ + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert, ih, primeBlockSub_eq_sdiff]
    ext p
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, fun hc => h2 (primesBelowSub_floor_mono (Nat.zero_le j) hc)⟩
      · exact ⟨primesBelowSub_floor_mono (Nat.le_succ j) h1, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases hj : p ∈ primesBelowSub (⌊blockScale θ j⌋₊ + 1)
      · exact Or.inr ⟨hj, h2⟩
      · exact Or.inl ⟨h1, hj⟩

/-- **The block walk is the annulus sum.**  This bridges the two halves of the estimate that most
points are good (Hamdan's Lemma 2.3): the barrier side speaks of `walk` of the block family, the
cumulant side of a sum over the primes between two cutoffs. -/
theorem walk_blockSum_eq_sum_sdiff {Ω : Type*} {X : ℕ → Ω → ℂ} (θ : ℝ) (w : Nat.Primes → ℂ)
    (j : ℕ) (ω : Ω) :
    walk (fun m ω => ∑ p ∈ primeBlockSub θ m, localLog (w p) (X (p : ℕ) ω)) j ω
      = ∑ p ∈ primesBelowSub (⌊blockScale θ j⌋₊ + 1)
            \ primesBelowSub (⌊blockScale θ 0⌋₊ + 1),
          localLog (w p) (X (p : ℕ) ω) := by
  classical
  rw [walk_apply, ← biUnion_primeBlockSub_eq_sdiff θ j]
  refine (Finset.sum_biUnion ?_).symm
  intro a _ b _ hab
  exact pairwise_disjoint_primeBlockSub θ hab

end RMF
