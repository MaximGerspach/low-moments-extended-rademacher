/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.Chaining
import RMF.Probability.ChaosInterpolation

/-!
# The maximal barrier bound (Hamdan's Lemma 2.3)

Hamdan's Lemma 2.3 (Hamdan, arXiv:2604.05563) bounds the probability that the barrier fails
somewhere in `h ∈ [0,1]`.  A bound at a **fixed** height does not suffice: the good-set
decomposition of the chaos moment needs it uniformly over `h ∈ [0,1]`, because the
Soundararajan–Zaman indicator `1(h ∉ G_A)` sits outside the `h`-integral and must therefore be an
`ω`-event.

Hamdan's proof is a union bound over `j`, then at each `j` a union bound over a partition of
`[0,1]` into intervals of width `e^{-j}` (here `e^{-(j+ϑ)}`), with Lemma B.2 on each interval:
`RMF.IsSteinhausRMF.exists_measure_exists_gt_le_shift` above the barrier and
`RMF.IsSteinhausRMF.exists_measure_exists_lt_le` below it.

## What this file supplies first

Lemma B.2 leaves both prime sums symbolic.  Turning them into `j` is what makes the entropy factor
and the Gaussian exponent comparable, and it is the content of the first section:

```
∑_{p < x_j} p^{-1} = j + ϑ + O(1),        ∑_{p < x_j} p^{-1}\log p ≤ e^{j+ϑ} + O(1).
```

Both come from Mertens, as `RMF.exists_abs_sum_primesBelow_inv_sub_log_log_le` and
`RMF.sum_primesBelow_log_div_le`, plus the floor comparisons `RMF.log_log_floor_blockScale_le`
and `RMF.le_log_log_floor_blockScale`.  The lower bound is the one that costs something: it is
taken at `⌊x_j⌋₊ - 1`, since Mertens is indexed by `Nat.primesBelow (N+1)`.

**Why `ϑ` and not just `j`.**  Hamdan's scales are `x_j = \exp(e^j)`; ours are
`\exp(e^{j+ϑ})`, and the partition of `[0,1]` matched to them has `e^{j+ϑ}` intervals, not `e^j`.
The extra entropy is a factor `e^ϑ`, and it is carried explicitly rather than hidden in the
constant.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-! ### The block scales are at least `4`

Everything below needs `⌊x_j⌋₊` to be large enough for `\log\log` of it, and of it minus one, to
be defined and positive.  With `ϑ ≥ 1` that is automatic: `x_j ≥ \exp(e) > e^2 > 4`. -/

/-- `4 ≤ ⌊x_j⌋₊` for every `j`, once `ϑ ≥ 1`. -/
lemma four_le_floor_blockScale {ϑ : ℝ} (hϑ : 1 ≤ ϑ) (j : ℕ) : 4 ≤ ⌊blockScale ϑ j⌋₊ := by
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
  have h1 : (1 : ℝ) ≤ (j : ℝ) + ϑ := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have h2 : (2 : ℝ) ≤ Real.exp ((j : ℝ) + ϑ) := le_trans he1 (Real.exp_le_exp.2 h1)
  have h4 : (4 : ℝ) ≤ blockScale ϑ j := by
    rw [blockScale]
    calc (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ Real.exp 1 * Real.exp 1 := by nlinarith
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
      _ ≤ Real.exp (Real.exp ((j : ℝ) + ϑ)) := Real.exp_le_exp.2 h2
  exact Nat.le_floor (by exact_mod_cast h4)

/-- `\log\log⌊x_j⌋₊ ≤ j + ϑ`: the floor only shrinks the scale. -/
lemma log_log_floor_blockScale_le {ϑ : ℝ} (hϑ : 1 ≤ ϑ) (j : ℕ) :
    Real.log (Real.log ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ)) ≤ (j : ℝ) + ϑ := by
  have hM4 := four_le_floor_blockScale hϑ j
  have h2 : (2 : ℝ) ≤ ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ) := by
    have h : (2 : ℕ) ≤ ⌊blockScale ϑ j⌋₊ := by omega
    exact_mod_cast h
  have hfl : ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ) ≤ blockScale ϑ j :=
    Nat.floor_le (blockScale_pos ϑ j).le
  have hl1 : (0 : ℝ) < Real.log ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hstep : Real.log ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ) ≤ Real.log (blockScale ϑ j) :=
    Real.log_le_log (by linarith) hfl
  calc Real.log (Real.log ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ))
      ≤ Real.log (Real.log (blockScale ϑ j)) := Real.log_le_log hl1 hstep
    _ = (j : ℝ) + ϑ := log_log_blockScale ϑ j

/-- `j + ϑ - 1 ≤ \log\log⌊x_j⌋₊`.

Two floors cost a factor `2`, and `e^u - \log 2 ≥ e^{u-1}` for `u ≥ 1` absorbs it into the `-1`. -/
lemma le_log_log_floor_blockScale {ϑ : ℝ} (hϑ : 1 ≤ ϑ) (j : ℕ) :
    (j : ℝ) + ϑ - 1 ≤ Real.log (Real.log ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ)) := by
  have hM4 := four_le_floor_blockScale hϑ j
  have hxpos : (0 : ℝ) < blockScale ϑ j := blockScale_pos ϑ j
  have hfl : ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ) ≤ blockScale ϑ j := Nat.floor_le hxpos.le
  have hx4 : (4 : ℝ) ≤ blockScale ϑ j := by
    have h : ((4 : ℕ) : ℝ) ≤ ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ) := by exact_mod_cast hM4
    push_cast at h
    linarith
  have hlt := Nat.lt_floor_add_one (blockScale ϑ j)
  have hhalf : blockScale ϑ j / 2 ≤ ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ) := by linarith
  have hu1 : (1 : ℝ) ≤ (j : ℝ) + ϑ := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hlogx : Real.log (blockScale ϑ j) = Real.exp ((j : ℝ) + ϑ) := by
    rw [blockScale, Real.log_exp]
  have hlog2 : Real.log 2 ≤ 7 / 10 :=
    le_of_lt (lt_of_lt_of_le Real.log_two_lt_d9 (by norm_num))
  have hkey : Real.exp ((j : ℝ) + ϑ - 1) ≤ Real.log (blockScale ϑ j) - Real.log 2 := by
    rw [hlogx, Real.exp_sub]
    have he : (27 / 10 : ℝ) < Real.exp 1 :=
      lt_of_le_of_lt (by norm_num) Real.exp_one_gt_d9
    have h1 : Real.exp 1 ≤ Real.exp ((j : ℝ) + ϑ) := Real.exp_le_exp.2 hu1
    have hdiv : Real.exp ((j : ℝ) + ϑ) / Real.exp 1
        ≤ Real.exp ((j : ℝ) + ϑ) / (27 / 10) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) he.le
    linarith
  have hstep : Real.log (blockScale ϑ j) - Real.log 2
      ≤ Real.log ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ) := by
    have h1 : Real.log (blockScale ϑ j / 2)
        ≤ Real.log ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hhalf
    rwa [Real.log_div (ne_of_gt hxpos) (by norm_num)] at h1
  have hpos2 : (0 : ℝ) < Real.log (blockScale ϑ j) - Real.log 2 :=
    lt_of_lt_of_le (Real.exp_pos _) hkey
  calc (j : ℝ) + ϑ - 1 = Real.log (Real.exp ((j : ℝ) + ϑ - 1)) := (Real.log_exp _).symm
    _ ≤ Real.log (Real.log (blockScale ϑ j) - Real.log 2) :=
        Real.log_le_log (Real.exp_pos _) hkey
    _ ≤ Real.log (Real.log ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ)) := Real.log_le_log hpos2 hstep

/-! ### The two prime sums at the block scales

Lemma B.2's hypotheses and conclusion are stated through `A = ∑_{p<y} p^{-2σ}` and
`P₁ = ∑_{p<y} p^{-2σ}\log p`.  The cutoffs are `⌊x_k⌋₊ + 1`, which is what
`p ≤ x_k` says about a natural number, and is also exactly how Mertens is indexed here
(`RMF.exists_abs_sum_primesBelow_inv_sub_log_log_le` compares `∑_{p ∈ primesBelow (N+1)}` with
`\log\log N`).  At `σ = 1/2` the two sums are `k + ϑ + O(1)` and `≤ e^{k+ϑ} + O(1)`.

**All three bounds are needed, and for different reasons.**  The upper bound on `A` is what makes
the Gaussian exponent `-V²/A` large; the *lower* bound is what discharges Lemma B.2's hypothesis
`V ≤ Λ A`, and it is the reason Lemma 2.3 needs its index range to start above a
constant.  The bound on `P₁` discharges `r P₁ ≤ Λ` at `r = e^{-(k+ϑ)}`, and it is the only place
the width of the partition's intervals is pinned down. -/

/-- **Both prime sums up to the block scale `x_j`**, on the critical line. -/
theorem exists_const_sum_primesBelow_blockScale_le :
    ∃ C > 0, ∀ ϑ : ℝ, 1 ≤ ϑ → ∀ j : ℕ,
      (∑ p ∈ Nat.primesBelow (⌊blockScale ϑ j⌋₊ + 1), (p : ℝ) ^ (-2 * (1 / 2 : ℝ)))
            ≤ (j : ℝ) + ϑ + C
        ∧ (j : ℝ) + ϑ - C
            ≤ ∑ p ∈ Nat.primesBelow (⌊blockScale ϑ j⌋₊ + 1),
                (p : ℝ) ^ (-2 * (1 / 2 : ℝ))
        ∧ (∑ p ∈ Nat.primesBelow (⌊blockScale ϑ j⌋₊ + 1),
              (p : ℝ) ^ (-2 * (1 / 2 : ℝ)) * Real.log p)
            ≤ Real.exp ((j : ℝ) + ϑ) + C := by
  obtain ⟨CM, hCM, hM⟩ := exists_abs_sum_primesBelow_inv_sub_log_log_le
  refine ⟨CM + Real.log 4 + Real.log 2 + 5, by positivity, fun ϑ hϑ j => ?_⟩
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hM4 : 4 ≤ ⌊blockScale ϑ j⌋₊ := four_le_floor_blockScale hϑ j
  have hMer := abs_le.1 (hM ⌊blockScale ϑ j⌋₊ (by omega))
  refine ⟨?_, ?_, ?_⟩
  · rw [sum_primesBelow_rpow_half]
    have hup := log_log_floor_blockScale_le hϑ j
    linarith [hMer.2]
  · rw [sum_primesBelow_rpow_half]
    have hlow := le_log_log_floor_blockScale hϑ j
    linarith [hMer.1]
  · rw [sum_primesBelow_rpow_half_mul_log]
    have h := sum_primesBelow_log_div_le (y := ⌊blockScale ϑ j⌋₊ + 1) (by omega)
    have hxpos : (0 : ℝ) < blockScale ϑ j := blockScale_pos ϑ j
    have hfl : ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ) ≤ blockScale ϑ j := Nat.floor_le hxpos.le
    have hx4 : (4 : ℝ) ≤ blockScale ϑ j := by
      have h4 : ((4 : ℕ) : ℝ) ≤ ((⌊blockScale ϑ j⌋₊ : ℕ) : ℝ) := by exact_mod_cast hM4
      push_cast at h4
      linarith
    have hle2 : ((⌊blockScale ϑ j⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * blockScale ϑ j := by
      push_cast
      linarith
    have hlogM : Real.log ((⌊blockScale ϑ j⌋₊ + 1 : ℕ) : ℝ)
        ≤ Real.log 2 + Real.exp ((j : ℝ) + ϑ) := by
      have hle := Real.log_le_log (by positivity) hle2
      rw [Real.log_mul (by norm_num) (ne_of_gt hxpos), blockScale, Real.log_exp] at hle
      exact hle
    linarith

/-! ### The same two sums over a block range

The block walk runs over `x_0 < p ≤ x_j`, not over `p ≤ x_j`, and its variance is therefore
`\log\log x_j - \log\log x_0 = j` -- **the `ϑ` cancels**.  That is where the upper barrier
`A + j + b_j` is centred, and it is why Lemma 2.3 has to be stated for this range rather than for
the head sum: with the head included the variance is `j + ϑ` and the lower barrier `-20j` would be
crossed with probability close to one for large `ϑ`.

The second sum does *not* lose its `ϑ`: it is dominated by the largest prime, so it is still
`≤ e^{j+ϑ}`.  That mismatch is exactly the factor `e^ϑ` that survives in Lemma 2.3's bound -- the
partition of `[0,1)` has `e^{j+ϑ}` intervals while the drift that pays for them is only `j`.
Hamdan's scales have `ϑ = 0` and he does not see it. -/

/-- **Both prime sums over the block range `x_0 < p ≤ x_j`**, on the critical line. -/
theorem exists_const_sum_primesIco_blockScale_le :
    ∃ C > 0, ∀ ϑ : ℝ, 1 ≤ ϑ → ∀ j : ℕ,
      (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 : ℝ)))
            ≤ (j : ℝ) + C
        ∧ (j : ℝ) - C
            ≤ ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
                (p : ℝ) ^ (-2 * (1 / 2 : ℝ))
        ∧ (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
              (p : ℝ) ^ (-2 * (1 / 2 : ℝ)) * Real.log p)
            ≤ Real.exp ((j : ℝ) + ϑ) + C := by
  obtain ⟨C, hC, h⟩ := exists_const_sum_primesBelow_blockScale_le
  refine ⟨2 * C, by linarith, fun ϑ hϑ j => ?_⟩
  have hmono : ⌊blockScale ϑ 0⌋₊ + 1 ≤ ⌊blockScale ϑ j⌋₊ + 1 := by
    have := Nat.floor_le_floor (blockScale_mono ϑ (Nat.zero_le j))
    omega
  have hsub : Nat.primesBelow (⌊blockScale ϑ 0⌋₊ + 1) ⊆ Nat.primesBelow (⌊blockScale ϑ j⌋₊ + 1) :=
    primesBelow_mono hmono
  have hsplit : ∀ g : ℕ → ℝ,
      (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1), g p)
        = (∑ p ∈ Nat.primesBelow (⌊blockScale ϑ j⌋₊ + 1), g p)
          - ∑ p ∈ Nat.primesBelow (⌊blockScale ϑ 0⌋₊ + 1), g p := by
    intro g
    simp only [primesIco]
    rw [eq_sub_iff_add_eq]
    exact Finset.sum_sdiff hsub
  obtain ⟨hupj, hlowj, hPj⟩ := h ϑ hϑ j
  obtain ⟨hup0, hlow0, -⟩ := h ϑ hϑ 0
  push_cast at hup0 hlow0
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit]
    linarith
  · rw [hsplit]
    linarith
  · have hstep : (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
          (p : ℝ) ^ (-2 * (1 / 2 : ℝ)) * Real.log p)
        ≤ ∑ p ∈ Nat.primesBelow (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 : ℝ)) * Real.log p := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro p hp
        rw [mem_primesIco] at hp
        exact Nat.mem_primesBelow.2 ⟨hp.2.2, hp.1⟩
      · intro p hp _
        have hpp := Nat.prime_of_mem_primesBelow hp
        have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
        have hlog : (0 : ℝ) ≤ Real.log p := Real.log_nonneg h1
        have hpow : (0 : ℝ) ≤ (p : ℝ) ^ (-2 * (1 / 2 : ℝ)) :=
          Real.rpow_nonneg (by linarith) _
        positivity
    linarith

/-! ### The partition of `[0,1)`, and the two exponent inequalities

Three deterministic facts, separated from the assembly because each is numeric and the assembly's
context is large enough for `nlinarith` to time out in.

The two exponent inequalities are where the design of the barrier shows.  **Above**, the entropy
`e^τ` of the partition is cancelled *exactly* by the drift term `τ` in `A + τ + b`:
`(A+τ+b)²/τ ≥ 2A + 2b + τ`, and nothing is left over.  That is why the barrier carries a drift at
all, and why the envelope `b` may not be dropped -- the `j`-sum has to converge on `e^{-2b}` alone.
**Below**, the barrier sits at `-20τ` and the same computation leaves a factor `e^{-100τ}` unused;
that slack is what pays for the reflection's loss `4∑_{p<y}p^{-2σ}`. -/

/-- **The `\log p`-weighted prime sum at a non-negative shift:**
`∑_{x_0 < p ≤ x_j} p^{-2(1/2+δ)}\log p ≤ e^{j+ϑ} + C` for `δ ≥ 0`.  The third of the three facts
`RMF.IsSteinhausRMF.exists_const_measureReal_index_le_of_le` asks for, and the only free one:
`p^{-2(1/2+δ)}\log p ≤ p^{-1}\log p` termwise, so the `δ = 0` bound serves unchanged. -/
theorem exists_const_sum_primesIco_rpow_log_le :
    ∃ C > 0, ∀ (ϑ δ : ℝ), 1 ≤ ϑ → 0 ≤ δ → ∀ j : ℕ,
      (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
          (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p)
        ≤ Real.exp ((j : ℝ) + ϑ) + C := by
  obtain ⟨C, hC, h⟩ := exists_const_sum_primesIco_blockScale_le
  refine ⟨C, hC, ?_⟩
  intro ϑ δ hϑ hδ j
  refine le_trans (Finset.sum_le_sum ?_) (h ϑ hϑ j).2.2
  intro p hp
  have hpp : Nat.Prime p := prime_of_mem_primesIco hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
  have hlog : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1
  have hrp : ((p : ℝ)) ^ (-2 * (1 / 2 + δ)) ≤ ((p : ℝ)) ^ (-2 * (1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  exact mul_le_mul_of_nonneg_right hrp hlog

/-- **The `log p`-weighted prime sum at a shift of either sign**, at the cost of a factor `e²`.

`RMF.exists_const_sum_primesIco_rpow_log_le` compares termwise with `δ = 0`, which is free for
`δ ≥ 0`.  To the left of `½` the terms grow, by `p^{-2δ} = e^{-2δ log p} ≤ e²` as long as
`|δ|·log p ≤ 1`, and that is all it costs. -/
theorem exists_const_sum_primesIco_rpow_log_le_signed :
    ∃ C > 0, ∀ (ϑ δ : ℝ), 1 ≤ ϑ → ∀ j : ℕ,
      (0 ≤ δ ∨ |δ| * Real.log (blockScale ϑ j) ≤ 1) →
      (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
          (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p)
        ≤ Real.exp 2 * Real.exp ((j : ℝ) + ϑ) + Real.exp 2 * C := by
  obtain ⟨C, hC, h⟩ := exists_const_sum_primesIco_blockScale_le
  refine ⟨C, hC, ?_⟩
  intro ϑ δ hϑ j hδ
  have hsum := (h ϑ hϑ j).2.2
  have hbound : (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p)
      ≤ Real.exp 2 * ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 : ℝ)) * Real.log p := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp : Nat.Prime p := prime_of_mem_primesIco hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    have hlog : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1
    -- `p^{-2(½+δ)} = p^{-1}·e^{-2δ log p}`, and the exponential is at most `e²`
    have hfac : (p : ℝ) ^ (-2 * (1 / 2 + δ))
        = (p : ℝ) ^ (-2 * (1 / 2 : ℝ)) * Real.exp (-(2 * δ * Real.log p)) := by
      rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0, ← Real.exp_add]
      congr 1
      ring
    have hexp : Real.exp (-(2 * δ * Real.log p)) ≤ Real.exp 2 := by
      refine Real.exp_le_exp.2 ?_
      rcases hδ with hδ0 | hδj
      · nlinarith [mul_nonneg hδ0 hlog]
      · have hpj : Real.log p ≤ Real.log (blockScale ϑ j) := by
          have hlt := (mem_primesIco.1 hp).2.2
          have h1 : p ≤ ⌊blockScale ϑ j⌋₊ := by omega
          have hpfl : (p : ℝ) ≤ blockScale ϑ j :=
            le_trans (by exact_mod_cast h1) (Nat.floor_le (blockScale_pos ϑ j).le)
          exact Real.log_le_log hp0 hpfl
        have h2 : |δ| * Real.log p ≤ 1 :=
          le_trans (mul_le_mul_of_nonneg_left hpj (abs_nonneg δ)) hδj
        nlinarith [mul_le_mul_of_nonneg_right (neg_abs_le δ) hlog]
    rw [hfac]
    have hq0 : (0 : ℝ) ≤ (p : ℝ) ^ (-2 * (1 / 2 : ℝ)) := Real.rpow_nonneg hp0.le _
    calc (p : ℝ) ^ (-2 * (1 / 2 : ℝ)) * Real.exp (-(2 * δ * Real.log p)) * Real.log p
        ≤ (p : ℝ) ^ (-2 * (1 / 2 : ℝ)) * Real.exp 2 * Real.log p :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hq0) hlog
      _ = Real.exp 2 * ((p : ℝ) ^ (-2 * (1 / 2 : ℝ)) * Real.log p) := by ring
  calc _ ≤ Real.exp 2 * ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 : ℝ)) * Real.log p := hbound
    _ ≤ Real.exp 2 * (Real.exp ((j : ℝ) + ϑ) + C) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos 2).le
    _ = Real.exp 2 * Real.exp ((j : ℝ) + ϑ) + Real.exp 2 * C := by ring

/-- **The partition, on a window of arbitrary length.**  Every `h ∈ [0,w)` lies in one of the `N`
intervals `[kρ, kρ+ρ)`, `k < N`, provided `Nρ ≥ w`; `RMF.exists_lt_mem_Ico` is the case `w = 1`.
It lets the Rademacher barrier be stated on `[h₀, h₀+w)` (`Probability/RademacherBarrier.lean`),
where the union over the `N` intervals is paid for in proportion to `w`. -/
lemma exists_lt_mem_Ico_of_lt {h ρ w : ℝ} {N : ℕ} (hρ : 0 < ρ) (h0 : 0 ≤ h) (h1 : h < w)
    (hN : w ≤ (N : ℝ) * ρ) :
    ∃ k : ℕ, k < N ∧ h ∈ Set.Ico ((k : ℝ) * ρ) ((k : ℝ) * ρ + ρ) := by
  have hfl : ((⌊h / ρ⌋₊ : ℕ) : ℝ) ≤ h / ρ := Nat.floor_le (by positivity)
  have hlt : h / ρ < ((⌊h / ρ⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlow : ((⌊h / ρ⌋₊ : ℕ) : ℝ) * ρ ≤ h := (le_div_iff₀ hρ).1 hfl
  have hhigh : h < ((⌊h / ρ⌋₊ : ℕ) : ℝ) * ρ + ρ := by
    have h := (div_lt_iff₀ hρ).1 hlt
    linarith
  refine ⟨⌊h / ρ⌋₊, ?_, hlow, hhigh⟩
  have hkN : ((⌊h / ρ⌋₊ : ℕ) : ℝ) * ρ < (N : ℝ) * ρ := by linarith
  exact_mod_cast lt_of_mul_lt_mul_right hkN hρ.le

/-- **The partition.**  Every `h ∈ [0,1)` lies in one of the `N` intervals of width `ρ`, provided
`Nρ ≥ 1`.  The case `w = 1` of `RMF.exists_lt_mem_Ico_of_lt`. -/
lemma exists_lt_mem_Ico {h ρ : ℝ} {N : ℕ} (hρ : 0 < ρ) (h0 : 0 ≤ h) (h1 : h < 1)
    (hN : 1 ≤ (N : ℝ) * ρ) :
    ∃ k : ℕ, k < N ∧ h ∈ Set.Ico ((k : ℝ) * ρ) ((k : ℝ) * ρ + ρ) :=
  exists_lt_mem_Ico_of_lt hρ h0 h1 hN

/-- **Above the barrier**: `(A+τ+b)²/a ≥ τ + 2A + 2b - C₀` whenever `a ≤ τ + C₀`. -/
lemma barrier_upper_exponent_le {τ A b a C₀ : ℝ} (ha : 0 < a) (hle : a ≤ τ + C₀)
    (hu : 0 < τ + C₀) :
    τ + 2 * A + 2 * b - C₀ ≤ (A + τ + b) ^ 2 / a := by
  have h1 : (A + τ + b) ^ 2 / (τ + C₀) ≤ (A + τ + b) ^ 2 / a :=
    div_le_div_of_nonneg_left (sq_nonneg _) ha hle
  have h2 := two_mul_add_le_sq_div (A := A + b - C₀) (j := τ + C₀) hu
  rw [show A + b - C₀ + (τ + C₀) = A + τ + b from by ring] at h2
  linarith

/-- **Below the barrier**: with the reflection's loss `4a` already subtracted, the exponent still
dominates `τ + 2A + 2b` by a wide margin.

The threshold used is `20τ`, not the barrier's own `A + cτ`: the event is contained in the one at
the smaller threshold whenever `c ≥ 20`, and keeping `A` and `c` out of it is what stops the
Chernoff parameter from leaving Lemma B.2's range as the slope grows. -/
lemma barrier_lower_exponent_le {τ A b a C₀ : ℝ} (hC₀ : 1 ≤ C₀) (hτ : 8 * C₀ ≤ τ)
    (hA : A ≤ 4 * τ) (hb : b ≤ τ) (hle : a ≤ τ + C₀) (hge : τ - C₀ ≤ a) :
    τ + 2 * A + 2 * b ≤ (20 * τ - 4 * a) ^ 2 / a := by
  have hτ0 : (0 : ℝ) < τ := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  have hW : 31 * τ / 2 ≤ 20 * τ - 4 * a := by linarith
  have haup : a ≤ 9 * τ / 8 := by linarith
  have hlhs : τ + 2 * A + 2 * b ≤ 11 * τ := by linarith
  rw [le_div_iff₀ hapos]
  calc (τ + 2 * A + 2 * b) * a ≤ 11 * τ * (9 * τ / 8) :=
        mul_le_mul hlhs haup hapos.le (by linarith)
    _ ≤ (31 * τ / 2) ^ 2 := by nlinarith [sq_nonneg τ]
    _ ≤ (20 * τ - 4 * a) ^ 2 := by nlinarith [hW, hτ0]

/-! ### The barrier fails at one index

The union bound over the partition, with Lemma B.2 on each interval: above the barrier through
`RMF.IsSteinhausRMF.exists_measure_exists_gt_le_shift`, below it through
`RMF.IsSteinhausRMF.exists_measure_exists_lt_le`, both read over the block range `(x_0, x_j]`.

Every constant is pinned here.  `Λ = C₀ + 40` is what makes all three of Lemma B.2's hypotheses
hold at once: `ρP₁ ≤ 1 + C₀` at the interval width `ρ = e^{-(j+ϑ)}`, and both thresholds are at most
`20j` against `Λ a ≥ 41(7j/8)`.  The requirement `j ≥ 8C₀` makes the prime sum `a` comparable to
`j` in *both* directions; it is why Lemma 2.3's index range starts above a constant, and the
application discharges it by `A > 4C₀` with `A ≤ 4j`.

**The factor `e^ϑ`.**  The partition has `e^{j+ϑ}` intervals -- the scale on which the walk at
`x_j = \exp(e^{j+ϑ})` oscillates -- while the drift term that pays for them is only `j`.  The
remaining `e^ϑ` is carried in the conclusion rather than hidden in the constant. -/

/-- **The per-index barrier bound at a shifted abscissa `1/2 + δ`, `δ ≥ 0`**, with the deficit `Δ`
of the two-sided prime sum as a parameter and the three prime-sum facts as hypotheses, met by
`RMF.abs_sum_primesIco_rpow_sub_le_of_le'` (`Δ = 45√K + …` at `|δ|·\log x_n ≤ K`) and
`RMF.exists_const_sum_primesIco_rpow_log_le`.  `C` depends on `Δ`, which enters
`RMF.barrier_upper_exponent_le` additively in the exponent and fixes `Λ = Δ + 40`. -/
theorem IsSteinhausRMF.exists_const_measureReal_index_le_of_le {Ω : Type*} [MeasurableSpace Ω]
    (Δ : ℝ) (hΔ : 1 ≤ Δ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (ϑ A b c δ : ℝ) (j : ℕ), 1 ≤ ϑ → 0 ≤ A → 0 ≤ b → 20 ≤ c → 0 ≤ δ →
        (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ →
        (j : ℝ) - Δ ≤ ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ)) →
        (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Real.exp ((j : ℝ) + ϑ) + Δ →
        C ≤ (j : ℝ) → A ≤ 4 * (j : ℝ) → b ≤ (j : ℝ) →
          μ.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
              Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
                  (heightLine (1 / 2 + δ) h) ω‖
                ∉ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b)}
            ≤ C * Real.exp ϑ * Real.exp (-(2 * A)) * Real.exp (-(2 * b)) := by
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = Δ + 40 := ⟨_, rfl⟩
  have hΛ1 : (1 : ℝ) ≤ Λ := by rw [hΛdef]; linarith
  obtain ⟨Cu, hCu, Hu⟩ := IsSteinhausRMF.exists_measure_exists_gt_le_shift
    (Ω := Ω) (σ₀ := 1 / 2) (Λ := Λ) (by norm_num) hΛ1
  obtain ⟨Cl, hCl, Hl⟩ := IsSteinhausRMF.exists_measure_exists_lt_le
    (Ω := Ω) (σ₀ := 1 / 2) (Λ := Λ) (by norm_num) hΛ1
  refine ⟨max (8 * Δ) (2 * (Cu + Cl) * Real.exp Δ), ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith : (0 : ℝ) < 8 * Δ) (le_max_left _ _)
  intro f μ hf ϑ A b c δ j hϑ hA0 hb0 hc hδ0 hupA hlowA hP hτC hA hb
  have hDone : (1 : ℝ) ≤ Δ := hΔ
  have hδσ : (1 : ℝ) / 2 ≤ 1 / 2 + δ := by linarith
  haveI := hf.isProbabilityMeasure
  set τ := (j : ℝ) with hτdef
  have hτ8 : 8 * Δ ≤ τ := le_trans (le_max_left _ _) hτC
  have hτ0 : (0 : ℝ) < τ := by linarith
  set a := ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
    (p : ℝ) ^ (-2 * (1 / 2 + δ)) with hadef
  clear_value τ a
  have hale : a ≤ τ + Δ := by linarith
  have hage : τ - Δ ≤ a := by linarith
  have ha1 : (1 : ℝ) ≤ a := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  -- the partition of `[0,1)` into intervals of width `e^{-(τ+ϑ)}`
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = Real.exp (-(τ + ϑ)) := ⟨_, rfl⟩
  have hρ0 : (0 : ℝ) < ρ := by rw [hρdef]; exact Real.exp_pos _
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef, Real.exp_le_one_iff]
    linarith
  have hρinv : Real.exp (τ + ϑ) * ρ = 1 := by
    rw [hρdef, ← Real.exp_add]
    simp
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈Real.exp (τ + ϑ)⌉₊ := ⟨_, rfl⟩
  have hNge : Real.exp (τ + ϑ) ≤ (N : ℝ) := by rw [hNdef]; exact Nat.le_ceil _
  have hNle : (N : ℝ) ≤ 2 * Real.exp (τ + ϑ) := by
    rw [hNdef]
    have hce := Nat.ceil_lt_add_one (Real.exp_pos (τ + ϑ)).le
    have hone : (1 : ℝ) ≤ Real.exp (τ + ϑ) := Real.one_le_exp (by linarith)
    linarith
  have hNρ : (1 : ℝ) ≤ (N : ℝ) * ρ := by
    have h := mul_le_mul_of_nonneg_right hNge hρ0.le
    linarith
  -- Lemma B.2's three hypotheses, at every interval
  have hrP : ρ * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Λ := by
    have h1 := mul_le_mul_of_nonneg_left hP hρ0.le
    have h2 : ρ * (Real.exp (τ + ϑ) + Δ) = 1 + ρ * Δ := by
      rw [mul_add, mul_comm ρ (Real.exp (τ + ϑ)), hρinv]
    have h3 : ρ * Δ ≤ Δ := by nlinarith
    rw [hΛdef]
    linarith
  have h41 : (41 : ℝ) ≤ Λ := by rw [hΛdef]; linarith
  have h78 : 7 * τ / 8 ≤ a := by linarith
  have hbig : (41 : ℝ) * (7 * τ / 8) ≤ Λ * a :=
    mul_le_mul h41 h78 (by linarith) (by linarith)
  have hVΛ : A + τ + b ≤ Λ * a := by linarith
  have hWΛ : 20 * τ - 4 * a ≤ Λ * a := by linarith
  have hW0 : (0 : ℝ) ≤ 20 * τ - 4 * a := by linarith
  have hV0 : (0 : ℝ) ≤ A + τ + b := by linarith
  -- the same three, in the unfolded form Lemma B.2 asks for
  have ha1' : (1 : ℝ) ≤ ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ)) := hadef ▸ ha1
  have hVΛ' : A + τ + b ≤ Λ * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ))) := hadef ▸ hVΛ
  have hWΛ' : 20 * τ - 4 * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)))
      ≤ Λ * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ))) := hadef ▸ hWΛ
  have hW0' : (0 : ℝ) ≤ 20 * τ
      - 4 * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ))) := hadef ▸ hW0
  -- the two Gaussian exponents, against the entropy of the partition
  have hexpU : Real.exp (τ + ϑ) * Real.exp (-((A + τ + b) ^ 2 / a))
      ≤ Real.exp ϑ * (Real.exp Δ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))) := by
    have hkey := barrier_upper_exponent_le (τ := τ) (A := A) (b := b) (a := a) (C₀ := Δ)
      hapos hale (by linarith)
    have e1 : Real.exp (τ + ϑ) * Real.exp (-((A + τ + b) ^ 2 / a))
        = Real.exp (τ + ϑ + -((A + τ + b) ^ 2 / a)) := (Real.exp_add _ _).symm
    have e2 : Real.exp ϑ * (Real.exp Δ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))
        = Real.exp (ϑ + (Δ + (-(2 * A) + -(2 * b)))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    rw [e1, e2]
    exact Real.exp_le_exp.2 (by linarith)
  have hexpL : Real.exp (τ + ϑ) * Real.exp (-((20 * τ - 4 * a) ^ 2 / a))
      ≤ Real.exp ϑ * (Real.exp Δ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))) := by
    have hkey := barrier_lower_exponent_le (τ := τ) (A := A) (b := b) (a := a) (C₀ := Δ)
      hDone hτ8 hA hb hale hage
    have e1 : Real.exp (τ + ϑ) * Real.exp (-((20 * τ - 4 * a) ^ 2 / a))
        = Real.exp (τ + ϑ + -((20 * τ - 4 * a) ^ 2 / a)) := (Real.exp_add _ _).symm
    have e2 : Real.exp ϑ * (Real.exp Δ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))
        = Real.exp (ϑ + (Δ + (-(2 * A) + -(2 * b)))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    rw [e1, e2]
    exact Real.exp_le_exp.2 (by linarith)
  -- the two families of events, one per interval
  obtain ⟨Eup, hEup⟩ : ∃ E : ℕ → Set Ω, E = fun k : ℕ =>
      {ω | ∃ h ∈ Set.Ico ((k : ℝ) * ρ) ((k : ℝ) * ρ + ρ),
        A + τ + b < Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1)
          (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖} := ⟨_, rfl⟩
  obtain ⟨Elo, hElo⟩ : ∃ E : ℕ → Set Ω, E = fun k : ℕ =>
      {ω | ∃ h ∈ Set.Ico ((k : ℝ) * ρ) ((k : ℝ) * ρ + ρ),
        20 * τ - 4 * a + 4 * a < -Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1)
          (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖} := ⟨_, rfl⟩
  have hboundU : μ.real (⋃ k ∈ Finset.range N, Eup k)
      ≤ (N : ℝ) * (Cu * Real.exp (-((A + τ + b) ^ 2 / a))) := by
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    have hterm : ∀ k ∈ Finset.range N,
        μ.real (Eup k) ≤ Cu * Real.exp (-((A + τ + b) ^ 2 / a)) := by
      intro k _
      have h := Hu f μ hf (1 / 2 + δ) (A + τ + b) ρ ((k : ℝ) * ρ) (⌊blockScale ϑ 0⌋₊ + 1)
        (⌊blockScale ϑ j⌋₊ + 1) hδσ hρ0 hV0 ha1' hVΛ' hrP
      rw [← hadef] at h
      simp only [hEup]
      exact h
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hboundL : μ.real (⋃ k ∈ Finset.range N, Elo k)
      ≤ (N : ℝ) * (Cl * Real.exp (-((20 * τ - 4 * a) ^ 2 / a))) := by
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    have hterm : ∀ k ∈ Finset.range N,
        μ.real (Elo k) ≤ Cl * Real.exp (-((20 * τ - 4 * a) ^ 2 / a)) := by
      intro k _
      have h := Hl f μ hf (1 / 2 + δ)
        (20 * τ - 4 * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
          (p : ℝ) ^ (-2 * (1 / 2 + δ)))) ρ ((k : ℝ) * ρ) (⌊blockScale ϑ 0⌋₊ + 1)
        (⌊blockScale ϑ j⌋₊ + 1) hδσ hρ0 hW0' ha1' hWΛ' hrP
      rw [← hadef] at h
      simp only [hElo]
      exact h
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the failure at this index is covered by the two families
  have hsub : {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
      Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
          (heightLine (1 / 2 + δ) h) ω‖
        ∉ Set.Icc (-A - c * τ) (A + τ + b)}
      ⊆ (⋃ k ∈ Finset.range N, Eup k) ∪ (⋃ k ∈ Finset.range N, Elo k) := by
    rintro ω ⟨h, hh, hnot⟩
    obtain ⟨k, hkN, hk⟩ := exists_lt_mem_Ico hρ0 hh.1 hh.2 hNρ
    simp only [Set.mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with hlt | hgt
    · refine Or.inr (Set.mem_biUnion (Finset.mem_range.2 hkN) ?_)
      simp only [hElo]
      have hct : 20 * τ ≤ c * τ := mul_le_mul_of_nonneg_right hc hτ0.le
      exact ⟨h, hk, by linarith⟩
    · refine Or.inl (Set.mem_biUnion (Finset.mem_range.2 hkN) ?_)
      simp only [hEup]
      exact ⟨h, hk, hgt⟩
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_union_le _ _) ?_
  have hU : (N : ℝ) * (Cu * Real.exp (-((A + τ + b) ^ 2 / a)))
      ≤ 2 * Cu * (Real.exp ϑ * (Real.exp Δ
        * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))) := by
    have h1 : (N : ℝ) * Real.exp (-((A + τ + b) ^ 2 / a))
        ≤ 2 * (Real.exp (τ + ϑ) * Real.exp (-((A + τ + b) ^ 2 / a))) := by
      have h := mul_le_mul_of_nonneg_right hNle
        (Real.exp_pos (-((A + τ + b) ^ 2 / a))).le
      linarith
    calc (N : ℝ) * (Cu * Real.exp (-((A + τ + b) ^ 2 / a)))
        = Cu * ((N : ℝ) * Real.exp (-((A + τ + b) ^ 2 / a))) := by ring
      _ ≤ Cu * (2 * (Real.exp (τ + ϑ) * Real.exp (-((A + τ + b) ^ 2 / a)))) :=
          mul_le_mul_of_nonneg_left h1 hCu.le
      _ ≤ Cu * (2 * (Real.exp ϑ * (Real.exp Δ
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexpU (by norm_num)) hCu.le
      _ = 2 * Cu * (Real.exp ϑ * (Real.exp Δ
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))) := by ring
  have hL : (N : ℝ) * (Cl * Real.exp (-((20 * τ - 4 * a) ^ 2 / a)))
      ≤ 2 * Cl * (Real.exp ϑ * (Real.exp Δ
        * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))) := by
    have h1 : (N : ℝ) * Real.exp (-((20 * τ - 4 * a) ^ 2 / a))
        ≤ 2 * (Real.exp (τ + ϑ) * Real.exp (-((20 * τ - 4 * a) ^ 2 / a))) := by
      have h := mul_le_mul_of_nonneg_right hNle
        (Real.exp_pos (-((20 * τ - 4 * a) ^ 2 / a))).le
      linarith
    calc (N : ℝ) * (Cl * Real.exp (-((20 * τ - 4 * a) ^ 2 / a)))
        = Cl * ((N : ℝ) * Real.exp (-((20 * τ - 4 * a) ^ 2 / a))) := by ring
      _ ≤ Cl * (2 * (Real.exp (τ + ϑ)
            * Real.exp (-((20 * τ - 4 * a) ^ 2 / a)))) :=
          mul_le_mul_of_nonneg_left h1 hCl.le
      _ ≤ Cl * (2 * (Real.exp ϑ * (Real.exp Δ
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexpL (by norm_num)) hCl.le
      _ = 2 * Cl * (Real.exp ϑ * (Real.exp Δ
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))) := by ring
  have hmax : 2 * (Cu + Cl) * Real.exp Δ
      ≤ max (8 * Δ) (2 * (Cu + Cl) * Real.exp Δ) := le_max_right _ _
  have hpos : (0 : ℝ) < Real.exp ϑ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))) := by
    positivity
  have hlast := mul_le_mul_of_nonneg_right hmax hpos.le
  linarith [hboundU, hboundL, hU, hL, hlast]

/-! ### Lemma 2.3

The union bound over the indices: push the negation through and sum, since the per-index bound
already carries the factor `e^{-2b_j}` that makes the sum converge.

**The envelope may not be dropped.**  At a fixed height one can discard `b j` and recover
summability from the geometric `e^{-j}` in `(A+j)²/L_j ≥ 2A + j`; here that `e^{-j}` is spent on
the entropy of the partition, and only `∑_j e^{-2b_j}` remains to sum.  With Hamdan's envelope
`b_j = 2\log(1 + j ∧ (t-j))` that sum is `∑_j (1 + j ∧ (t-j))^{-4}`, bounded independently of
`t`. -/

/-- **Hamdan's Lemma 2.3 at a shifted abscissa `1/2 + δ`, `δ ≥ 0`.**  The three prime-sum
hypotheses of `RMF.IsSteinhausRMF.exists_const_measureReal_index_le_of_le` are quantified over the
index range; `RMF.abs_sum_primesIco_rpow_sub_le_of_le'` supplies the first two at
`Δ = 45√K + …` whenever `|δ|·\log x_n ≤ K`, and the third is free for `δ ≥ 0`. -/
theorem IsSteinhausRMF.exists_const_measure_exists_barrier_le_of_le {Ω : Type*}
    [MeasurableSpace Ω] (Δ : ℝ) (hΔ : 1 ≤ Δ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (ϑ A c δ : ℝ) (r n : ℕ) (b : ℕ → ℝ), 1 ≤ ϑ → 0 ≤ A → 20 ≤ c → 0 ≤ δ → C ≤ (r : ℝ) →
        (∀ j, r ≤ j → j ≤ n → 0 ≤ b j) →
        (∀ j, r ≤ j → j ≤ n → b j ≤ (j : ℝ)) →
        (∀ j, r ≤ j → j ≤ n → A ≤ 4 * (j : ℝ)) →
        (∀ j, r ≤ j → j ≤ n →
          (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ) →
        (∀ j, r ≤ j → j ≤ n → (j : ℝ) - Δ ≤
          ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) →
        (∀ j, r ≤ j → j ≤ n →
          (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Real.exp ((j : ℝ) + ϑ) + Δ) →
          μ.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
              Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
                  (heightLine (1 / 2 + δ) h) ω‖
                ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
            ≤ C * Real.exp ϑ * Real.exp (-(2 * A))
              * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) := by
  obtain ⟨C₂, hC₂, H⟩ := IsSteinhausRMF.exists_const_measureReal_index_le_of_le (Ω := Ω) Δ hΔ
  refine ⟨C₂, hC₂, ?_⟩
  intro f μ hf ϑ A c δ r n b hϑ hA0 hc hδ0 hC₂r hb0 hble h4 hup hlow hlogP
  haveI := hf.isProbabilityMeasure
  obtain ⟨E, hE⟩ : ∃ E : ℕ → Set Ω, E = fun j : ℕ =>
      {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
        Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
            (heightLine (1 / 2 + δ) h) ω‖
          ∉ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)} := ⟨_, rfl⟩
  have hsub : {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
      Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
          (heightLine (1 / 2 + δ) h) ω‖
        ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      ⊆ ⋃ j ∈ Finset.Icc r n, E j := by
    rintro ω ⟨h, hh, hnot⟩
    push Not at hnot
    obtain ⟨j, hjr, hjn, hj⟩ := hnot
    refine Set.mem_biUnion (Finset.mem_Icc.2 ⟨hjr, hjn⟩) ?_
    simp only [hE]
    exact ⟨h, hh, hj⟩
  have hlast : ∑ j ∈ Finset.Icc r n,
        C₂ * Real.exp ϑ * Real.exp (-(2 * A)) * Real.exp (-(2 * b j))
      = C₂ * Real.exp ϑ * Real.exp (-(2 * A))
        * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) := by
    rw [Finset.mul_sum]
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun j hj => ?_) (le_of_eq hlast)
  obtain ⟨hjr, hjn⟩ := Finset.mem_Icc.1 hj
  have hjR : (r : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjr
  simp only [hE]
  exact H f μ hf ϑ A (b j) c δ j hϑ hA0 (hb0 j hjr hjn) hc hδ0
    (hup j hjr hjn) (hlow j hjr hjn) (hlogP j hjr hjn) (by linarith) (h4 j hjr hjn)
    (hble j hjr hjn)

/-! ### The block walk `RMF.walk`

Lemma 2.3 above is stated through `\log‖F^{Ico}‖`; the chaos moment speaks of `RMF.walk` of the
block family, indexed by `Finset Nat.Primes`.  The two agree, and the endpoint conventions match
on the nose: for a natural `p`, `x_0 < p ≤ x_j` **is** `⌊x_0⌋₊ + 1 ≤ p < ⌊x_j⌋₊ + 1`.
`RMF.walk_blockSum_eq_sum_sdiff` telescopes the blocks to
`primesBelowSub (⌊x_j⌋₊+1) \ primesBelowSub (⌊x_0⌋₊+1)`, that difference is `RMF.primesIcoSub`, and
`RMF.sum_primesIcoSub` reads it back over `ℕ`. -/

/-- The difference of two prime-below sets is the block, as a `Finset Nat.Primes`. -/
lemma primesBelowSub_sdiff (y₀ y₁ : ℕ) :
    primesBelowSub y₁ \ primesBelowSub y₀ = primesIcoSub y₀ y₁ := by
  ext p
  simp only [Finset.mem_sdiff, mem_primesBelowSub, mem_primesIcoSub, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    refine ⟨?_, h1⟩
    by_contra hc
    exact h2 ⟨by omega, p.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h2, p.2⟩, fun hc => absurd hc.1 (by omega)⟩

/-- The prime sum over `(x_0, x_j]` splits into blocks — the plain version of
`RMF.walk_blockSum_eq_sum_sdiff`, with no walk and no `localLog` in it. -/
lemma sum_primesIco_eq_sum_blocks (θ : ℝ) (j : ℕ) (F : ℕ → ℝ) :
    (∑ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1), F p)
      = ∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ m, F (p : ℕ) := by
  classical
  rw [← sum_primesIcoSub, ← primesBelowSub_sdiff, ← biUnion_primeBlockSub_eq_sdiff θ j]
  refine Finset.sum_biUnion ?_
  intro a _ b _ hab
  exact pairwise_disjoint_primeBlockSub θ hab

/-- **The prime sum over `(x_0, x_j]` at a tilt of either sign**, with a deficit `O(√K)`.

`RMF.abs_sum_primesIco_rpow_sub_le_of_le` asks `σ ≥ 0` and uses it in one place only: a block the
tilt has thinned, `K·e^{m-n} > 1`, is bounded by its value at `σ = 0`.  Such a block exists only
when `K > 1`, so the hypothesis here is `σ ≥ 0` **or** `K ≤ 1`.  The second covers the shifts to
the left with `|σ|·log x_{n+1} ≤ 1`, which is how the barrier reads the tilt at the drop. -/
theorem abs_sum_primesIco_rpow_sub_le_of_le_signed {θ σ K : ℝ} {n j : ℕ}
    (hθ3 : (3 : ℝ) ≤ θ) (hj : j ≤ n + 1) (hK0 : 0 ≤ K) (hσK : 0 ≤ σ ∨ K ≤ 1)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ K) :
    |(∑ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1),
        (p : ℝ) ^ (-1 - 2 * σ)) - (j : ℝ)|
      ≤ 45 * √K + 120 * Real.exp 2 * Real.exp (-(1 + θ)) := by
  have he2 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have he2u : Real.exp 2 ≤ 7.4 := by
    have hrw : Real.exp 2 = Real.exp 1 ^ (2 : ℕ) := by rw [← Real.exp_nat_mul]; ring_nf
    rw [hrw]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
  have hblock : ∀ m ∈ Finset.range j,
      |(∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) - 1|
        ≤ 15 * min (K * Real.exp ((m : ℝ) - n)) 1
          + Real.exp 2 * (60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ)))) := by
    intro m hm
    have hmj : m < j := Finset.mem_range.1 hm
    have hmn : m ≤ n := by omega
    have hmθ : (3 : ℝ) ≤ (m : ℝ) + θ := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hem0 : (0 : ℝ) < Real.exp ((m : ℝ) - n) := Real.exp_pos _
    have hη0 : (0 : ℝ) ≤ K * Real.exp ((m : ℝ) - n) := by positivity
    have hd0 : (0 : ℝ) ≤ 60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ))) := by positivity
    rcases le_or_gt (K * Real.exp ((m : ℝ) - n)) 1 with hcase | hcase
    · -- the tilt is mild here: the two-sided block estimate, linearised
      have hmain := abs_sum_rpow_primeBlockSub_sub_one_le θ σ (K * Real.exp ((m : ℝ) - n)) m
        hmθ hη0 (sigma_le_mul_exp_sub θ σ K hσ)
      rw [sixty_div_log_blockScale] at hmain
      have hle2 : Real.exp (2 * (K * Real.exp ((m : ℝ) - n))) ≤ Real.exp 2 :=
        Real.exp_le_exp.2 (by linarith)
      have hlin := exp_sub_one_le_mul_exp (2 * (K * Real.exp ((m : ℝ) - n)))
      rw [min_eq_left hcase]
      nlinarith [hmain, hle2, hlin, hη0, hd0, he2u]
    · -- the tilt has thinned the block: the σ-uniform upper bound is all that is needed
      have hσ0 : 0 ≤ σ := by
        rcases hσK with h | h
        · exact h
        · exfalso
          have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
          have hle1 : Real.exp ((m : ℝ) - n) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
          nlinarith [hcase, hK0, h, hle1, Real.exp_pos ((m : ℝ) - n)]
      have hup := sum_rpow_primeBlockSub_le_of_nonneg θ σ m hmθ hσ0
      rw [sixty_div_log_blockScale] at hup
      have hlow : (0 : ℝ) ≤ ∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
        Finset.sum_nonneg fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
      rw [min_eq_right hcase.le, abs_le]
      constructor <;> nlinarith [hup, hlow, hd0, he2]
  rw [sum_primesIco_eq_sum_blocks]
  have hsplit : (∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ m,
        ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) - (j : ℝ)
      = ∑ m ∈ Finset.range j,
          ((∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hA : ∑ m ∈ Finset.range j, 15 * min (K * Real.exp ((m : ℝ) - n)) 1 ≤ 45 * √K := by
    have hterm : ∀ m ∈ Finset.range j,
        15 * min (K * Real.exp ((m : ℝ) - n)) 1
          ≤ 15 * √K * Real.exp (((m : ℝ) - n) / 2) := by
      intro m _
      have h := min_one_le_sqrt (show (0 : ℝ) ≤ K * Real.exp ((m : ℝ) - n) by positivity)
      rw [Real.sqrt_mul hK0, sqrt_exp] at h
      nlinarith [h]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    calc 15 * √K * ∑ m ∈ Finset.range j, Real.exp (((m : ℝ) - n) / 2)
        ≤ 15 * √K * 3 :=
          mul_le_mul_of_nonneg_left (sum_exp_half_sub_le hj) (by positivity)
      _ = 45 * √K := by ring
  have hB : ∑ m ∈ Finset.range j,
        Real.exp 2 * (60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ))))
      ≤ 120 * Real.exp 2 * Real.exp (-(1 + θ)) := by
    have hre : ∀ m : ℕ, Real.exp 2 * (60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ))))
        = 60 * Real.exp 2 * Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ)) := fun m => by ring
    rw [Finset.sum_congr rfl (fun m _ => hre m), ← Finset.mul_sum]
    calc 60 * Real.exp 2 * Real.exp (-(1 + θ)) * ∑ m ∈ Finset.range j, Real.exp (-(m : ℝ))
        ≤ 60 * Real.exp 2 * Real.exp (-(1 + θ)) * 2 :=
          mul_le_mul_of_nonneg_left (sum_exp_neg_nat_le j) (by positivity)
      _ = 120 * Real.exp 2 * Real.exp (-(1 + θ)) := by ring
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hblock) ?_
  rw [Finset.sum_add_distrib]
  linarith [hA, hB]

/-- **The prime sum over `(x_0, x_j]` at a tilt `σ ≥ 0`:**
`|∑ p^{-1-2σ} - j| ≤ 45√K + 120e²e^{-(1+θ)}` for `j ≤ n + 1` and `|σ|·\log x_{n+1} ≤ K`;
`RMF.exists_const_sum_primesIco_blockScale_le` is the `σ = 0` counterpart.  The per-block
distortion is `η_m = Ke^{m-n}` (`RMF.sigma_le_mul_exp_sub`), and
`|∑_{p∈B_m} p^{-1-2σ} - 1| ≤ 15·\min(η_m, 1) + e²·60/L_m` sums, by `\min(x,1) ≤ √x`, to `O(√K)`.
The case `σ ≥ 0` of `RMF.abs_sum_primesIco_rpow_sub_le_of_le_signed`. -/
theorem abs_sum_primesIco_rpow_sub_le_of_le {θ σ K : ℝ} {n j : ℕ}
    (hθ3 : (3 : ℝ) ≤ θ) (hj : j ≤ n + 1) (hK0 : 0 ≤ K) (hσ0 : 0 ≤ σ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ K) :
    |(∑ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1),
        (p : ℝ) ^ (-1 - 2 * σ)) - (j : ℝ)|
      ≤ 45 * √K + 120 * Real.exp 2 * Real.exp (-(1 + θ)) := by
  exact abs_sum_primesIco_rpow_sub_le_of_le_signed hθ3 hj hK0 (Or.inl hσ0) hσ

/-- The two ways the chain writes the shifted exponent: the block estimates say `-1 - 2δ`, the
barrier chain says `-2(1/2 + δ)`.  Equal, but not syntactically. -/
lemma rpow_neg_two_half_add (p δ : ℝ) : p ^ (-2 * (1 / 2 + δ)) = p ^ (-1 - 2 * δ) := by
  congr 1
  ring

/-- **`RMF.abs_sum_primesIco_rpow_sub_le_of_le_signed` in the barrier chain's exponent form.** -/
theorem abs_sum_primesIco_rpow_sub_le_of_le_signed' {θ δ K : ℝ} {n j : ℕ}
    (hθ3 : (3 : ℝ) ≤ θ) (hj : j ≤ n + 1) (hK0 : 0 ≤ K) (hδK : 0 ≤ δ ∨ K ≤ 1)
    (hδ : |δ| * Real.log (blockScale θ (n + 1)) ≤ K) :
    |(∑ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ))) - (j : ℝ)|
      ≤ 45 * √K + 120 * Real.exp 2 * Real.exp (-(1 + θ)) := by
  have h : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1),
      ((p : ℝ)) ^ (-2 * (1 / 2 + δ)) = ((p : ℝ)) ^ (-1 - 2 * δ) :=
    fun p _ => rpow_neg_two_half_add (p : ℝ) δ
  rw [Finset.sum_congr rfl h]
  exact abs_sum_primesIco_rpow_sub_le_of_le_signed hθ3 hj hK0 hδK hδ

/-- **`RMF.abs_sum_primesIco_rpow_sub_le_of_le` in the barrier chain's exponent form.**  A separate
lemma because `-1 - 2δ` and `-2(1/2 + δ)` are the same real number and different terms.  The case
`δ ≥ 0` of `RMF.abs_sum_primesIco_rpow_sub_le_of_le_signed'`. -/
theorem abs_sum_primesIco_rpow_sub_le_of_le' {θ δ K : ℝ} {n j : ℕ}
    (hθ3 : (3 : ℝ) ≤ θ) (hj : j ≤ n + 1) (hK0 : 0 ≤ K) (hδ0 : 0 ≤ δ)
    (hδ : |δ| * Real.log (blockScale θ (n + 1)) ≤ K) :
    |(∑ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ))) - (j : ℝ)|
      ≤ 45 * √K + 120 * Real.exp 2 * Real.exp (-(1 + θ)) := by
  exact abs_sum_primesIco_rpow_sub_le_of_le_signed' hθ3 hj hK0 (Or.inl hδ0) hδ

/-- **The block walk is the sum over `x_0 < p ≤ x_j`**, indexed by `ℕ`. -/
theorem walk_blockSum_eq_sum_primesIco {Ω : Type*} {X : ℕ → Ω → ℂ} (ϑ : ℝ) (w : ℕ → ℂ)
    (j : ℕ) (ω : Ω) :
    walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m, localLog (w (p : ℕ)) (X (p : ℕ) ω)) j ω
      = ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
          localLog (w p) (X p ω) := by
  rw [walk_blockSum_eq_sum_sdiff ϑ (fun p => w (p : ℕ)) j ω, primesBelowSub_sdiff]
  exact sum_primesIcoSub _ _ fun p => localLog (w p) (X p ω)

/-- **Hamdan's Lemma 2.3 for the block walk, at a shifted abscissa.**  The bookkeeping between
`\log‖F^{Ico}‖` and `RMF.walk` of the block family is indifferent to the abscissa. -/
theorem IsSteinhausPrimeValues.exists_const_measure_exists_barrier_le_of_le
    {Ω : Type*} [MeasurableSpace Ω] (Δ : ℝ) (hΔ : 1 ≤ Δ) :
    ∃ C > 0, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
      ∀ (ϑ A c δ : ℝ) (r n : ℕ) (b : ℕ → ℝ), 1 ≤ ϑ → 0 ≤ A → 20 ≤ c → 0 ≤ δ → C ≤ (r : ℝ) →
        (∀ j, r ≤ j → j ≤ n → 0 ≤ b j) →
        (∀ j, r ≤ j → j ≤ n → b j ≤ (j : ℝ)) →
        (∀ j, r ≤ j → j ≤ n → A ≤ 4 * (j : ℝ)) →
        (∀ j, r ≤ j → j ≤ n →
          (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ) →
        (∀ j, r ≤ j → j ≤ n → (j : ℝ) - Δ ≤
          ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) →
        (∀ j, r ≤ j → j ≤ n →
          (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Real.exp ((j : ℝ) + ϑ) + Δ) →
          μ.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
              walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLog (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
                ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
            ≤ C * Real.exp ϑ * Real.exp (-(2 * A))
              * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) := by
  obtain ⟨C, hC, H⟩ :=
    IsSteinhausRMF.exists_const_measure_exists_barrier_le_of_le (Ω := Ω) Δ hΔ
  refine ⟨C, hC, ?_⟩
  intro X μ hX ϑ A c δ r n b hϑ hA0 hc hδ0 hCr hb0 hble h4 hup hlow hlogP
  haveI := hX.isProbabilityMeasure
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ := hX.isSteinhausRMF
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G =
      {ω | ∀ p ∈ Nat.primesBelow (⌊blockScale ϑ n⌋₊ + 1), ‖X p ω‖ ≤ 1} := ⟨_, rfl⟩
  have hGnull : μ Gᶜ = 0 := by
    have h := ae_forall_norm_le_one hX norm_le_one_steinhausLaw (⌊blockScale ϑ n⌋₊ + 1)
    rw [ae_iff] at h
    rw [hGdef, Set.compl_setOf]
    exact h
  have hwalk : ∀ ω ∈ G, ∀ (h : ℝ) (j : ℕ), j ≤ n →
      walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLog (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
        = Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω)
              (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖ := by
    intro ω hωG h j hjn
    rw [hGdef] at hωG
    have hjm : ⌊blockScale ϑ j⌋₊ ≤ ⌊blockScale ϑ n⌋₊ :=
      Nat.floor_le_floor (blockScale_mono ϑ hjn)
    have hsub : ∀ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        ‖X p ω‖ ≤ 1 := by
      intro p hp
      obtain ⟨hpp, -, hp2⟩ := mem_primesIco.1 hp
      exact hωG p (Nat.mem_primesBelow.2 ⟨by omega, hpp⟩)
    rw [walk_blockSum_eq_sum_primesIco ϑ
      (fun m => (m : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) j ω]
    exact (log_norm_randomEulerProductIco_eq (by rw [re_heightLine]; linarith) hsub).symm
  have hset : G ∩ {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
        walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLog (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      = G ∩ {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
        Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω)
              (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)} := by
    ext ω
    constructor
    · rintro ⟨hωG, h, hh, hnot⟩
      exact ⟨hωG, h, hh, fun hall => hnot fun j hjr hjn => by
        rw [hwalk ω hωG h j hjn]; exact hall j hjr hjn⟩
    · rintro ⟨hωG, h, hh, hnot⟩
      exact ⟨hωG, h, hh, fun hall => hnot fun j hjr hjn => by
        rw [← hwalk ω hωG h j hjn]; exact hall j hjr hjn⟩
  calc μ.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
        walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLog (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      = μ.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
          Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω)
              (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖
            ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)} := by
        unfold MeasureTheory.Measure.real
        rw [measure_eq_measure_inter_of_compl_null hGnull _, hset,
          ← measure_eq_measure_inter_of_compl_null hGnull _]
    _ ≤ C * Real.exp ϑ * Real.exp (-(2 * A))
          * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) :=
        H _ μ hf ϑ A c δ r n b hϑ hA0 hc hδ0 hCr hb0 hble h4 hup hlow hlogP

/-! ### Two joints to the restricted first moment

Two notational facts join Lemma 2.3 to the restricted first moment: the slope of Harper's
Proposition 5 (Harper, arXiv:1703.06654, §3.2) clears the one Lemma 2.3 needs, and the two halves
write the critical line differently. -/

/-- `20 ≤ blockSlope ϑ`: the slope of Harper's Proposition 5 clears Lemma 2.3's threshold.

`blockSlope ϑ = result2Slope (1/16) (9/2) + 2 + driftConst ϑ`, and `RMF.le_result2Slope` puts the
first summand at `20` on its own. -/
lemma twenty_le_blockSlope (ϑ : ℝ) : (20 : ℝ) ≤ blockSlope ϑ := by
  rw [blockSlope]
  have h20 := le_result2Slope (1 / 16 : ℝ) (9 / 2 : ℝ)
  have hd := driftConst_nonneg ϑ
  linarith

/-- `heightLine (1/2 + δ) = shiftLine δ` — the two halves' names for the shifted line. -/
lemma heightLine_eq_shiftLine (δ h : ℝ) :
    heightLine (1 / 2 + δ) h = shiftLine δ h := by
  rw [heightLine, shiftLine]

end RMF
