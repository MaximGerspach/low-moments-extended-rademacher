/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.BlockComparison
import RMF.Probability.BlockShift

/-!
# Harper's scales

Proposition 5 is stated against an abstract block offset `θ`, with `blockScale θ j = exp(exp(j+θ))`.
Harper's own scales are `x_j = x^{e^{-(l_j+1)}}` with `l_j = ⌊log log x⌋ - D - j`, so that
`log log x_j = fract(log log x) + D - 1 + j`.  Matching the two forces

  `θ = fract(log log x) + D - 1`   and   `x_j = blockScale θ j`,

and Harper's largest admissible `j` is the one with `l_j = 0`, namely `n = ⌊log log x⌋ - D`.  Both
of these are *determined* by `x` and `D`; neither is a free parameter.

**Why the offset is introduced this way.**  Only the fractional part of `log log x` moves, so `θ`
is confined to `[D-1, D)` however large `x` is.  A threshold `θ₀ ≤ θ` is therefore a condition on
`D` alone — `RMF.sub_one_le_harperOffset` — and every constant built from `θ` stays
absolute.  That is the whole reason the chain can carry `RMF.blockOffsetThreshold ≤ θ` without
anything growing with `x`.

`D` is Harper's `B + 1`.  It is chosen *existentially*, as `⌈ϑ₀⌉₊ + 5` for the block-offset
threshold `ϑ₀` handed over by `RMF.exists_const_proposition5_steinhaus_of_top`
(`RMF.le_ceil_add_one_sub_one`), never written as a numeral.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

/-- **Harper's block offset**, `θ = fract(log log x) + D - 1`, where `D` is Harper's `B + 1`.

Only the fractional part depends on `x`, so this ranges over `[D-1, D)` for every `x` — see
`RMF.sub_one_le_harperOffset` and `RMF.harperOffset_lt_natCast`. -/
noncomputable def harperOffset (D : ℕ) (x : ℝ) : ℝ :=
  Int.fract (Real.log (Real.log x)) + (D : ℝ) - 1

/-- **Harper's block count**, `n = ⌊log log x⌋ - D`: the largest `j` with `l_j ≥ 0`.

This is forced by `D` and `x`, not chosen.  At this `n` the top scale is `x` itself. -/
noncomputable def harperBlockCount (D : ℕ) (x : ℝ) : ℕ :=
  ⌊Real.log (Real.log x)⌋₊ - D

/-- **The tilt is mild.**  `|σ|\log x ≤ η` together with `3η ≤ \log x` forces `|σ| ≤ 1/3`,
hence `\Re s = 1/2 + σ ≥ 1/6 > 0`.

Negating the goal gives `η ≥ |σ|\log x > \tfrac13\log x ≥ η`.  Stated once so that the `nlinarith`
runs in a two-hypothesis context. -/
lemma abs_le_one_third_of_mul_log_le {x σ η : ℝ}
    (hL0 : 0 < Real.log x) (hL : 3 * η ≤ Real.log x) (hσ : |σ| * Real.log x ≤ η) :
    |σ| ≤ 1 / 3 := by
  nlinarith [abs_nonneg σ]

/-- The offset never falls below `D - 1`. -/
lemma sub_one_le_harperOffset (D : ℕ) (x : ℝ) : (D : ℝ) - 1 ≤ harperOffset D x := by
  have := Int.fract_nonneg (Real.log (Real.log x))
  rw [harperOffset]
  linarith

/-- And never reaches `D`.  Together with `RMF.sub_one_le_harperOffset` this is the statement that
`θ` does not move with `x` beyond a bounded window. -/
lemma harperOffset_lt_natCast (D : ℕ) (x : ℝ) : harperOffset D x < (D : ℝ) := by
  have := Int.fract_lt_one (Real.log (Real.log x))
  rw [harperOffset]
  linarith

/-- **A threshold on the offset is a condition on `D` alone.**  This is what makes the chain's
`ϑ₀ ≤ ϑ` dischargeable without anything growing with `x`: `harperOffset D x ≥ D - 1` for every `x`,
so it suffices to push `D` past `ϑ₀ + 1`.

Stated for an arbitrary `ϑ₀` rather than for `RMF.blockOffsetThreshold`, because
`RMF.exists_const_proposition5_steinhaus_of_top` hands over its threshold as an opaque
existential. -/
lemma le_harperOffset_of_le {ϑ₀ : ℝ} {D : ℕ} (x : ℝ) (hD : ϑ₀ ≤ (D : ℝ) - 1) :
    ϑ₀ ≤ harperOffset D x :=
  le_trans hD (sub_one_le_harperOffset D x)

/-- **The witness.**  `D = ⌈ϑ₀⌉₊ + 5` clears any real threshold, which lets `D` be chosen
existentially from an opaque threshold instead of written as a numeral. -/
lemma le_ceil_add_one_sub_one (ϑ₀ : ℝ) : ϑ₀ ≤ ((⌈ϑ₀⌉₊ + 5 : ℕ) : ℝ) - 1 := by
  have := Nat.le_ceil ϑ₀
  push_cast
  linarith

/-- `ϑ₀ ≤ ⌈ϑ₀⌉₊ + k - 1` for any `k ≥ 1` — the general form of `RMF.le_ceil_add_one_sub_one`: the
block offset is pushed above any threshold by choosing `D`. -/
lemma le_ceil_add_sub_one (ϑ₀ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ϑ₀ ≤ ((⌈ϑ₀⌉₊ + k : ℕ) : ℝ) - 1 := by
  have hc := Nat.le_ceil ϑ₀
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  push_cast
  linarith

/-! ### The top block reaches `x`

`harperBlockCount` is not one admissible choice of `n` among many: it is the choice for which the
top scale is `x` itself.  That is what ties the abstract chain to the number theory. -/

/-- The block count as a real.  `D ≤ log log x` is what makes the truncated subtraction honest;
without it `harperBlockCount` is `0` and the identity below fails. -/
lemma cast_harperBlockCount {D : ℕ} {x : ℝ} (hx : (D : ℝ) ≤ Real.log (Real.log x)) :
    (harperBlockCount D x : ℝ) = (⌊Real.log (Real.log x)⌋₊ : ℝ) - (D : ℝ) := by
  have hDf : D ≤ ⌊Real.log (Real.log x)⌋₊ := Nat.le_floor hx
  rw [harperBlockCount, Nat.cast_sub hDf]

/-- **The scale identity**: `n + 1 + θ = log log x`.  The `D` cancels, leaving
`⌊log log x⌋ + fract(log log x)`. -/
lemma harperBlockCount_add_one_add_offset {D : ℕ} {x : ℝ}
    (hx : (D : ℝ) ≤ Real.log (Real.log x)) :
    (harperBlockCount D x : ℝ) + 1 + harperOffset D x = Real.log (Real.log x) := by
  have h0 : (0 : ℝ) ≤ Real.log (Real.log x) := le_trans (Nat.cast_nonneg D) hx
  have hfl : (⌊Real.log (Real.log x)⌋₊ : ℝ) = (⌊Real.log (Real.log x)⌋ : ℝ) :=
    natCast_floor_eq_intCast_floor h0
  have hadd := Int.floor_add_fract (Real.log (Real.log x))
  rw [cast_harperBlockCount hx, harperOffset, hfl]
  linarith

/-- **The top scale is `x`, exactly.**

`1 < x` is not an extra assumption in practice: `hxD` with `D ≥ 1` already forces
`log log x ≥ 1`, hence `log x ≥ e`, hence `x > 1`.  It is stated separately only because it is
what `Real.exp_log` needs, twice. -/
theorem blockScale_harperOffset_top {D : ℕ} {x : ℝ} (hx1 : 1 < x)
    (hxD : (D : ℝ) ≤ Real.log (Real.log x)) :
    blockScale (harperOffset D x) (harperBlockCount D x + 1) = x := by
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hcast : ((harperBlockCount D x + 1 : ℕ) : ℝ) + harperOffset D x
      = Real.log (Real.log x) := by
    push_cast
    linarith [harperBlockCount_add_one_add_offset hxD]
  rw [blockScale, hcast, Real.exp_log hlx, Real.exp_log hx0]

/-- **Harper's `x_n = x^{1/e}`**, the top of the last *observed* block.

The blocks are `(x_j^{1/e}, x_j]`, so the observed primes stop at `x^{1/e}` while the tilt reaches
`x`.  Immediate from `RMF.blockScale_rpow_inv_exp_one`. -/
theorem blockScale_harperOffset_last {D : ℕ} {x : ℝ} (hx1 : 1 < x)
    (hxD : (D : ℝ) ≤ Real.log (Real.log x)) :
    blockScale (harperOffset D x) (harperBlockCount D x) = x ^ (Real.exp 1)⁻¹ := by
  rw [← blockScale_rpow_inv_exp_one, blockScale_harperOffset_top hx1 hxD]

/-- The tilt cutoff is `⌊x⌋₊ + 1`, i.e. the tilt runs over every prime `p ≤ x`.

**A divergence from Harper worth naming.**  He tilts by `∏_{p ≤ x^{1/e}}`, one block lower.  He
licenses the choice explicitly — the exact range of `p` in the tilt is not important to him — but
the object here is his with the range widened, not his verbatim. -/
theorem blockCutoff_harperOffset {D : ℕ} {x : ℝ} (hx1 : 1 < x)
    (hxD : (D : ℝ) ≤ Real.log (Real.log x)) :
    blockCutoff (harperOffset D x) (harperBlockCount D x) = ⌊x⌋₊ + 1 := by
  rw [blockCutoff, blockScale_harperOffset_top hx1 hxD]

/-- `hσtop` in terms of `x`: the chain's small-`σ` hypothesis reads `|σ| log x ≤ 1`.

Harper's Lemma 3 asks for `|σ| ≤ 1/log x_n = e/log x`, so ours is stronger by a factor `e`.  That
is harmless — a stronger hypothesis on `σ` only shrinks the range of `s` covered, and the
application supplies `σ` far smaller than either. -/
theorem log_blockScale_harperOffset_top {D : ℕ} {x : ℝ} (hx1 : 1 < x)
    (hxD : (D : ℝ) ≤ Real.log (Real.log x)) :
    Real.log (blockScale (harperOffset D x) (harperBlockCount D x + 1)) = Real.log x := by
  rw [blockScale_harperOffset_top hx1 hxD]

/-! ### Large `x`, not large `n`

`RMF.exists_blockSizeThreshold` gives a threshold on the block count.  Since the block count is
forced to be `⌊log log x⌋ - D`, that threshold becomes one on `x` — which is Harper's own "let `x`
be large", and not an extra constraint.  Note `n → ∞` with `x`, so there is no clash between
wanting `n` large and having it determined. -/

/-- **The threshold on `x`.**  Past `x₀ = exp(exp(D + n₀))` every size condition the chain wants
holds at once, including `D ≤ log log x`, which is what makes `harperBlockCount`'s truncated
subtraction honest.

`x₀` is existential because `n₀` is; that is inherited from `RMF.exists_blockSizeThreshold`, not
newly introduced here. -/
theorem exists_harperThreshold_of_blockCount (D n₀ : ℕ) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      1 < x ∧ (D : ℝ) ≤ Real.log (Real.log x) ∧ n₀ ≤ harperBlockCount D x := by
  refine ⟨Real.exp (Real.exp ((D : ℝ) + (n₀ : ℝ))), fun x hx => ?_⟩
  have hn₀0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg n₀
  have hinner : (0 : ℝ) < Real.exp ((D : ℝ) + (n₀ : ℝ)) := Real.exp_pos _
  have hx1 : 1 < x := by
    have hone : (1 : ℝ) < Real.exp (Real.exp ((D : ℝ) + (n₀ : ℝ))) := by
      linarith [Real.add_one_le_exp (Real.exp ((D : ℝ) + (n₀ : ℝ)))]
    linarith
  -- `log x ≥ e^{D+n₀}`, then `log log x ≥ D + n₀`
  have hlx : Real.exp ((D : ℝ) + (n₀ : ℝ)) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos (Real.exp ((D : ℝ) + (n₀ : ℝ)))) hx
    rwa [Real.log_exp] at this
  have hllx : (D : ℝ) + (n₀ : ℝ) ≤ Real.log (Real.log x) := by
    have := Real.log_le_log hinner hlx
    rwa [Real.log_exp] at this
  have hDlog : (D : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hfloor : D + n₀ ≤ ⌊Real.log (Real.log x)⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    linarith
  have hcount : n₀ ≤ harperBlockCount D x := by
    rw [harperBlockCount]
    omega
  exact ⟨hx1, hDlog, hcount⟩

/-! ### Proposition 5, in terms of `x`

Everything above exists to make this statement possible: the offset and the block count are
*determined* by `x` and `D`, so the only free choices left are `D` itself and how large `x` must be
— which is exactly Harper's "let `B` be a large natural number and `x` be large". -/

/-- **`RMF.exists_const_proposition5_harper_of_top` with the level left free.**
Reading Proposition 5 at Harper's offset `RMF.harperOffset D x` fixes the block offset at
`⌈ϑ₀⌉₊ + 5` and folds the block count into `x₀`; the level is untouched. -/
theorem le_const_proposition5_harper_of_steinhaus.{u} {ϑ₀ : ℝ} {n₀ : ℕ} {a₀ α A : ℝ}
    (H :
      ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (ϑ σ η a : ℝ) (d n : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          ϑ₀ ≤ ϑ → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ Real.exp d →
          |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η →
          a₀ ≤ a → 2 * d ≤ n → n₀ ≤ n - d →
          (∀ j, 1 ≤ j → j ≤ n - d → |hf j| ≤ 10 * Real.log j) →
            α * min 1 (a / Real.sqrt ((n - d : ℕ) : ℝ))
                ≤ ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω)
                      (blockCutoff ϑ n) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) (n - d)
                      (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ∧ ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω)
                      (blockCutoff ϑ n) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) (n - d)
                      (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
                  ≤ A * min 1 (a / Real.sqrt ((n - d : ℕ) : ℝ))) :
    ∀ D : ℕ, ⌈ϑ₀⌉₊ + 5 ≤ D → ∀ d : ℕ, ∃ x₀ : ℝ,
    ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
      IsSteinhausPrimeValues Y ν →
      ∀ (x σ η a : ℝ) (s : ℂ) (hf : ℕ → ℝ),
        x₀ ≤ x → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ Real.exp d →
        |σ| * Real.log x ≤ η → a₀ ≤ a →
        (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
          α * min 1 (a / Real.sqrt ((harperBlockCount D x - d : ℕ) : ℝ))
              ≤ ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1) s ν)
                  (barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                      localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
                    (harperBlockCount D x - d)
                    (fun j => -a - blockSlope 125 * j)
                    (fun j => a + j + hf j))).toReal
            ∧ ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1) s ν)
                  (barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                      localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
                    (harperBlockCount D x - d)
                    (fun j => -a - blockSlope 125 * j)
                    (fun j => a + j + hf j))).toReal
                ≤ A * min 1 (a / Real.sqrt ((harperBlockCount D x - d : ℕ) : ℝ)) := by
  intro D hD d
  obtain ⟨x₀, hx₀⟩ := exists_harperThreshold_of_blockCount D (max (2 * d) (n₀ + d))
  refine ⟨x₀, ?_⟩
  intro Ω' _ Y ν hY x σ η a s hf hx hres hσ0 hη0 hηE hσ ha hhf
  obtain ⟨hx1, hDlog, hcount⟩ := hx₀ x hx
  have h2d : 2 * d ≤ harperBlockCount D x := le_trans (le_max_left _ _) hcount
  have hn₀ : n₀ ≤ harperBlockCount D x - d := by omega
  have hϑ : ϑ₀ ≤ harperOffset D x := by
    refine le_harperOffset_of_le x ?_
    have h1 : ϑ₀ ≤ ((⌈ϑ₀⌉₊ + 5 : ℕ) : ℝ) - 1 := le_ceil_add_one_sub_one ϑ₀
    have h2 : ((⌈ϑ₀⌉₊ + 5 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    linarith
  have hσ' : |σ| * Real.log (blockScale (harperOffset D x)
      (harperBlockCount D x + 1)) ≤ η := by
    rw [log_blockScale_harperOffset_top hx1 hDlog]
    exact hσ
  have hcut : blockCutoff (harperOffset D x) (harperBlockCount D x)
      = ⌊x⌋₊ + 1 := blockCutoff_harperOffset hx1 hDlog
  have hmain := H Ω' Y ν hY (harperOffset D x) σ η a d
    (harperBlockCount D x) s hf hϑ hres hσ0 hη0 hηE hσ' ha h2d hn₀ hhf
  rwa [hcut] at hmain

/-- **Proposition 5 at Harper's scales and a general tilt, with absolute constants.**  The walk is
shortened by `d` top blocks, which buys the tilt `η ≤ e^d`.  `D₀`, `a₀`, `α`, `A` and the slope
`RMF.blockSlope 125` are absolute; only `x₀` depends on `D ≥ D₀` and on `d`.  The block-count
threshold absorbs `d`: `max(2d, n₀+d) ≤ n` gives both `2d ≤ n` and `n₀ ≤ n - d`. -/
theorem exists_const_proposition5_harper_of_top :
    ∃ (D₀ : ℕ) (a₀ α A : ℝ), 4 ≤ D₀ ∧ 0 < α ∧ 0 < A ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ d : ℕ, ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ Real.exp d →
          |σ| * Real.log x ≤ η → a₀ ≤ a →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            α * min 1 (a / Real.sqrt ((harperBlockCount D x - d : ℕ) : ℝ))
                ≤ ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
                      (harperBlockCount D x - d)
                      (fun j => -a - blockSlope 125 * j)
                      (fun j => a + j + hf j))).toReal
              ∧ ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
                      (harperBlockCount D x - d)
                      (fun j => -a - blockSlope 125 * j)
                      (fun j => a + j + hf j))).toReal
                  ≤ A * min 1 (a / Real.sqrt ((harperBlockCount D x - d : ℕ) : ℝ)) := by
  obtain ⟨ϑ₀, n₀, a₀, α, A, hα, hA, H⟩ := exists_const_proposition5_steinhaus_of_top
  exact ⟨⌈ϑ₀⌉₊ + 5, a₀, α, A, by omega, hα, hA,
    le_const_proposition5_harper_of_steinhaus H⟩

/-! ### Why `D` is a parameter in the `_of_top` form

The other `harper` variants in this file fix `D := ⌈ϑ₀⌉₊ + 5`; `_of_top` quantifies over `D ≥ D₀`,
because the restricted second moment (Harper's Key Proposition 5) is stated at
`RMF.harperTheta B x = RMF.harperOffset (B+2) x`, whose barrier machinery needs `θ ≥ 125`, hence
`D ≥ 126`.  With `D` existential the numerator would exist at one `B` only, and Paley–Zygmund needs
numerator and denominator on the same event.

### The free start, at Harper's scales

The free-start barrier bound in Harper's variables.  The block count `n₀` is exposed in the
existential rather than folded into `x₀`, because its hypothesis is `n₀ ≤ n - r` and `r` is the
caller's — `≈ a/4` in the passage from the first moment to the `q`-th — so no threshold on `x`
alone can discharge it. -/

/-- **The free-start barrier bound at Harper's scales and at a general tilt scale**, for `0 ≤ σ`
and `|σ| log x ≤ η ≤ E₀`, with slope `RMF.blockSlopeOf E₀ 125`:
`RMF.exists_const_freeStart_barrier_le_of_le` read at `RMF.harperOffset D x`.  All constants
depend on `E₀`. -/
theorem exists_const_freeStart_barrier_harper_le_of_le (E₀ : ℝ) (hE₀ : 0 ≤ E₀) :
    ∃ (D n₀ : ℕ) (x₀ a₀ C : ℝ), 4 ≤ D ∧ 0 < C ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (r : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → a₀ ≤ a → 1 ≤ a →
          1 ≤ r → r ≤ harperBlockCount D x → (r : ℝ) ≤ a / 4 + 1 →
          n₀ ≤ harperBlockCount D x - r →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1) s ν)
                {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - blockSlopeOf E₀ 125 * (j : ℝ))
                        (a + (j : ℝ) + hf j)}).toReal
              ≤ C * min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - r)) := by
  obtain ⟨ϑ₀, n₀, a₀, C, hC, H⟩ := exists_const_freeStart_barrier_le_of_le E₀ hE₀
  obtain ⟨x₀, hx₀⟩ := exists_harperThreshold_of_blockCount (⌈ϑ₀⌉₊ + 5) n₀
  refine ⟨⌈ϑ₀⌉₊ + 5, n₀, x₀, a₀, C, by omega, hC, ?_⟩
  intro Ω' _ Y ν hY x σ η a r s hf hx hres hσ0 hη0 hηE hσ ha ha1 hr1 hrn hra hn₀ hhf
  obtain ⟨hx1, hDlog, hcount⟩ := hx₀ x hx
  have hϑ : ϑ₀ ≤ harperOffset (⌈ϑ₀⌉₊ + 5) x :=
    le_harperOffset_of_le x (le_ceil_add_sub_one ϑ₀ 5 (by norm_num))
  have hσ' : |σ| * Real.log (blockScale (harperOffset (⌈ϑ₀⌉₊ + 5) x)
      (harperBlockCount (⌈ϑ₀⌉₊ + 5) x + 1)) ≤ η := by
    rw [log_blockScale_harperOffset_top hx1 hDlog]
    exact hσ
  have hcut : blockCutoff (harperOffset (⌈ϑ₀⌉₊ + 5) x) (harperBlockCount (⌈ϑ₀⌉₊ + 5) x)
      = ⌊x⌋₊ + 1 := blockCutoff_harperOffset hx1 hDlog
  have hmain := H Ω' Y ν hY (harperOffset (⌈ϑ₀⌉₊ + 5) x) σ η a
    (harperBlockCount (⌈ϑ₀⌉₊ + 5) x) r s hf hϑ hres hσ0 hη0 hηE hσ' ha ha1 hn₀
    hr1 hrn hra hhf
  rwa [hcut] at hmain

/-- **The free-start barrier bound at Harper's scales and a general tilt, with absolute
constants.**  The good set runs to `n - d`, which buys `η ≤ E₀ ≤ e^d`; `D`, `n₀`, `a₀`, `C` and the
slope `RMF.blockSlope 125` are absolute, and only `x₀` depends on `d` and `E₀`. -/
theorem exists_const_freeStart_barrier_harper_le_of_top :
    ∃ (D n₀ : ℕ) (a₀ C : ℝ), 4 ≤ D ∧ 0 < C ∧
      ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (r : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → a₀ ≤ a → 1 ≤ a →
          1 ≤ r → r ≤ harperBlockCount D x → (r : ℝ) ≤ a / 4 + 1 →
          2 * d ≤ harperBlockCount D x - r → n₀ ≤ harperBlockCount D x - r - d →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1) s ν)
                {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x - d →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - blockSlope 125 * (j : ℝ))
                        (a + (j : ℝ) + hf j)}).toReal
              ≤ C * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ) - r)) := by
  obtain ⟨ϑ₀, n₀, a₀, C, hC, H⟩ := exists_const_freeStart_barrier_le_of_top
  obtain ⟨x₀, hx₀⟩ := exists_harperThreshold_of_blockCount (⌈ϑ₀⌉₊ + 5) 0
  refine ⟨⌈ϑ₀⌉₊ + 5, n₀, a₀, C, by omega, hC, ?_⟩
  intro d E₀ _hE₀ hEd
  refine ⟨x₀, ?_⟩
  intro Ω' _ Y ν hY x σ η a r s hf hx hres hσ0 hη0 hηE hσ ha ha1 hr1 hrn hra hdn hn₀ hhf
  obtain ⟨hx1, hDlog, -⟩ := hx₀ x hx
  have hϑ : ϑ₀ ≤ harperOffset (⌈ϑ₀⌉₊ + 5) x :=
    le_harperOffset_of_le x (le_ceil_add_sub_one ϑ₀ 5 (by norm_num))
  have hσ' : |σ| * Real.log (blockScale (harperOffset (⌈ϑ₀⌉₊ + 5) x)
      (harperBlockCount (⌈ϑ₀⌉₊ + 5) x + 1)) ≤ η := by
    rw [log_blockScale_harperOffset_top hx1 hDlog]
    exact hσ
  have hcut : blockCutoff (harperOffset (⌈ϑ₀⌉₊ + 5) x) (harperBlockCount (⌈ϑ₀⌉₊ + 5) x)
      = ⌊x⌋₊ + 1 := blockCutoff_harperOffset hx1 hDlog
  have hmain := H Ω' Y ν hY (harperOffset (⌈ϑ₀⌉₊ + 5) x) σ η a d
    (harperBlockCount (⌈ϑ₀⌉₊ + 5) x) r s hf hϑ hres hσ0 hη0 (le_trans hηE hEd) hσ' ha
    ha1 hr1 hrn hdn hn₀ hra hhf
  rwa [hcut] at hmain

/-! ### Harper's `D(t)`

Harper takes the block offset to depend on the height: `D(t) = ⌈log(1/|t|)⌉ + (B+1)`
(Harper, arXiv:1703.06654, §4.4).  The offset raises the **smallest** block scale —
`log x₁ ≥ e^D` — which is what makes the Rademacher block variance's cosine sum small, since the
bound `|∑_{block m} cos(τ log p)/p^{1+2σ}| ≤ K/(τ e^{m+θ})` is small exactly when `m + θ` is large.

Which end moves is easy to get backwards.  `RMF.harperOffset` sets the bottom; the drop `d` of
`RMF.exists_const_proposition5_harper_of_top` removes blocks from the **top**, and
`RMF.blockCutoff_harperOffset` pins the top scale at `x` for every admissible `D`.  So raising `D`
raises the bottom and shortens the walk.  Putting `D(t)` in `d` instead is satisfiable, and proves
a different theorem, whose `t`-range has a floor that does not shrink with `x`.  Below: the two
shift identities, and the height condition they buy. -/

/-- Raising the offset by `k` raises `θ` by `k`. -/
lemma harperOffset_add (D k : ℕ) (x : ℝ) :
    harperOffset (D + k) x = harperOffset D x + (k : ℝ) := by
  simp only [harperOffset, Nat.cast_add]
  ring

/-- **Harper's `D(t)`**: the base offset raised by `⌈log(1/|t|)⌉`.

The pair side already has this device under the name `RMF.harperR`, as a *shift* rather than an
offset; this is the one-point form, and it is what the Rademacher Proposition 6 needs. -/
noncomputable def harperDt (D₀ : ℕ) (t : ℝ) : ℕ := D₀ + ⌈Real.log (1 / |t|)⌉₊

lemma le_harperDt (D₀ : ℕ) (t : ℝ) : D₀ ≤ harperDt D₀ t := Nat.le_add_right _ _

/-- `log(1/|t|) ≥ 0` on `0 < |t| ≤ 1`, which is what makes the ceiling honest. -/
lemma log_one_div_abs_nonneg {t : ℝ} (ht0 : 0 < |t|) (ht1 : |t| ≤ 1) :
    0 ≤ Real.log (1 / |t|) := by
  refine Real.log_nonneg ?_
  rw [le_div_iff₀ ht0]
  linarith

/-- **The height condition, at `D = harperDt D₀ t`.**  `2|t| e^θ ≥ 2 e^{D₀-1}`, uniformly in
`t` — so a threshold `Tsh ≤ 2|t| e^θ` is cleared by `Tsh ≤ 2 e^{D₀-1}`, a condition on `D₀`
alone.  This is the exact analogue of `RMF.two_mul_exp_le_mul_exp_harperR` on the pair side, and
it is the whole reason `D(t)` sits in the offset. -/
lemma two_mul_exp_le_mul_exp_harperOffset_harperDt {D₀ : ℕ} {t : ℝ} (ht0 : 0 < |t|) (x : ℝ) :
    2 * Real.exp ((D₀ : ℝ) - 1) ≤ 2 * |t| * Real.exp (harperOffset (harperDt D₀ t) x) := by
  have hinv : (0 : ℝ) < 1 / |t| := by positivity
  have hθ : (D₀ : ℝ) - 1 + Real.log (1 / |t|) ≤ harperOffset (harperDt D₀ t) x := by
    rw [harperDt, harperOffset_add]
    linarith [sub_one_le_harperOffset D₀ x, Nat.le_ceil (Real.log (1 / |t|))]
  have hexp : Real.exp ((D₀ : ℝ) - 1) * (1 / |t|) ≤ Real.exp (harperOffset (harperDt D₀ t) x) := by
    calc Real.exp ((D₀ : ℝ) - 1) * (1 / |t|)
        = Real.exp ((D₀ : ℝ) - 1 + Real.log (1 / |t|)) := by
          rw [Real.exp_add, Real.exp_log hinv]
      _ ≤ _ := Real.exp_le_exp.2 hθ
  have hid : 2 * |t| * (Real.exp ((D₀ : ℝ) - 1) * (1 / |t|)) = 2 * Real.exp ((D₀ : ℝ) - 1) := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ 2 * |t|)]

/-- `log y ≤ 2√y`, the crude bound that makes the height arithmetic go through: `log` is
`2 log √`, and `log ≤ · - 1`. -/
lemma log_le_two_mul_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have h2 : Real.log (Real.sqrt y ^ 2) = 2 * Real.log (Real.sqrt y) := by
    rw [Real.log_pow]
    norm_num
  rw [Real.sq_sqrt hy.le] at h2
  have h1 : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 := Real.log_le_sub_one_of_pos hs
  linarith

/-- **The block count at Harper's `D(t)`** — the one-point counterpart of
`RMF.harper_block_count`.  From one threshold on `log log x`, the count hypotheses of
`RMF.exists_const_proposition5_harper_of_top` hold at `D = D(t)` for every height with
`log(1/|t|) ≤ log log x / 3`: `D₀ ≤ D(t)`, `D(t) ≤ log log x` (without which `harperBlockCount`
truncates to `0`), `2d ≤ n` and `n₀ ≤ n - d`.  `D(t)` depends on `t` alone, not on `x`, `a` or
`n`. -/
lemma harper_block_count_of_height {D₀ d n₀ : ℕ} {x t : ℝ} (ht0 : 0 < |t|) (ht1 : |t| ≤ 1)
    (htL : Real.log (1 / |t|) ≤ Real.log (Real.log x) / 3)
    (hΛ : 2 * ((D₀ : ℝ) + (max (2 * d) (n₀ + d) : ℕ) + 2) ≤ Real.log (Real.log x)) :
    D₀ ≤ harperDt D₀ t ∧ (harperDt D₀ t : ℝ) ≤ Real.log (Real.log x)
      ∧ 2 * d ≤ harperBlockCount (harperDt D₀ t) x
      ∧ n₀ ≤ harperBlockCount (harperDt D₀ t) x - d := by
  set L : ℝ := Real.log (Real.log x) with hLdef
  set M : ℕ := max (2 * d) (n₀ + d) with hMdef
  have hD0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hK : ((⌈Real.log (1 / |t|)⌉₊ : ℕ) : ℝ) ≤ L / 3 + 1 := by
    have h := (Nat.ceil_lt_add_one (log_one_div_abs_nonneg ht0 ht1)).le
    linarith
  have hDle : ((harperDt D₀ t : ℕ) : ℝ) ≤ (D₀ : ℝ) + L / 3 + 1 := by
    rw [harperDt]
    push_cast
    linarith
  have hfl : L - 1 < (⌊L⌋₊ : ℝ) := Nat.sub_one_lt_floor L
  have hDL : ((harperDt D₀ t : ℕ) : ℝ) ≤ L := by linarith
  have hcount : harperDt D₀ t + M ≤ ⌊L⌋₊ := by
    have h : ((harperDt D₀ t + M : ℕ) : ℝ) ≤ ((⌊L⌋₊ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h
  have h2d : 2 * d ≤ M := le_max_left _ _
  have hn₀ : n₀ + d ≤ M := le_max_right _ _
  refine ⟨le_harperDt D₀ t, hDL, ?_, ?_⟩ <;> · simp only [harperBlockCount, ← hLdef]; omega

/-- Any absolute threshold `Tsh` is cleared by taking the base offset large enough, and `D₀`
may still be asked to clear anything else first.  This is what discharges `hTsh` below. -/
lemma exists_le_two_mul_exp_sub_one (Tsh : ℝ) (D₁ : ℕ) :
    ∃ D₀ : ℕ, D₁ ≤ D₀ ∧ Tsh ≤ 2 * Real.exp ((D₀ : ℝ) - 1) := by
  obtain ⟨T, hT1, hTle⟩ : ∃ T : ℝ, 1 ≤ T ∧ Tsh ≤ T :=
    ⟨max Tsh 1, le_max_right _ _, le_max_left _ _⟩
  refine ⟨max D₁ (⌈Real.log T⌉₊ + 1), le_max_left _ _, ?_⟩
  have hle : Real.log T ≤ ((max D₁ (⌈Real.log T⌉₊ + 1) : ℕ) : ℝ) - 1 := by
    have h1 : Real.log T ≤ (⌈Real.log T⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.log T⌉₊ + 1 : ℕ) : ℝ) ≤ ((max D₁ (⌈Real.log T⌉₊ + 1) : ℕ) : ℝ) :=
      Nat.cast_le.2 (le_max_right _ _)
    push_cast at h2 ⊢
    linarith
  have hexp := Real.exp_le_exp.2 hle
  rw [Real.exp_log (by linarith : (0 : ℝ) < T)] at hexp
  linarith [Real.exp_pos (((max D₁ (⌈Real.log T⌉₊ + 1) : ℕ) : ℝ) - 1)]

end RMF
