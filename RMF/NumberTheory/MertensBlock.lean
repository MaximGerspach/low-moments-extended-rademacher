/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.CosinePrimeSum

/-!
# Mertens' second theorem over a block of primes

`∑_{x < p ≤ y} 1/p = log log y − log log x + O(1/log x)`, for `2 ≤ x ≤ y`.

This is the bridge from per-prime to per-block estimates, and the reason the blocks are the unit
intervals of `log log p`: taking `x = exp(exp j)` and `y = exp(exp (j+1))` the main term is
`(j+1) − j = 1`, **on the nose, with no logarithm left over**, and the error is `O(e^{−j})`.
Hence each block carries `∑ 1/p = 1 + O(e^{−j})`, so the Steinhaus local terms over a block have
variance `1/2 + O(e^{−j})`, and the partial sums satisfy `∑_{i<j} Var = j/2 + O(1)` — which is
exactly the hypothesis the ballot theorems take.

An `O(1)` form of Mertens would *not* do here.  Over a block of log-log length one the main term
is itself `1`, so an `O(1)` error destroys it; the quantitative `O(1/log x)` is what makes the
statement say anything.

The endpoints are real, and the sum is indexed by `Finset.Ioc ⌊x⌋₊ ⌊y⌋₊` — the same indexing
`RMF.sum_prime_Ioc_rpow_le` uses, and the one
`PrimeNumberTheoremAnd.IEANTN.Mertens.sum_prime_div_eq` is stated in.  Keeping it avoids any
floor-or-ceiling bookkeeping: `log log (exp (exp j))` is exactly `j`.
-/

open Finset

namespace RMF

/-- The **error** constant in `PrimeNumberTheoremAnd`'s quantitative Mertens is nonnegative.  It
bounds an absolute value divided by a positive number, so this is forced.  Not to be confused with
Mertens' constant `Mertens.M` itself, bounded in `RMF.mertens_const_le`. -/
lemma mertens_error_const_nonneg : (0 : ℝ) ≤ Real.log 4 + 6 + Mertens.E₁ := by
  have h := Mertens.E₂p.abs_le (x := 2) le_rfl
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : (0 : ℝ) ≤ (Real.log 4 + 6 + Mertens.E₁) / Real.log 2 :=
    le_trans (abs_nonneg _) h
  rwa [le_div_iff₀ hlog, zero_mul] at h0

/-- **Mertens' second theorem over a block.**  For `2 ≤ x ≤ y`,
`|∑_{x < p ≤ y} 1/p − (log log y − log log x)| ≤ 20 / log x`.

The `O(1)` constants of Mertens cancel in the difference; what survives is the error term, and only
its *quantitative* form is of any use over a block of log-log length one. -/
theorem abs_sum_prime_Ioc_inv_sub_log_log_sub_le (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    |(∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (1 : ℝ) / p)
        - (Real.log (Real.log y) - Real.log (Real.log x))| ≤ 20 / Real.log x := by
  set K : ℝ := Real.log 4 + 6 + Mertens.E₁ with hK
  have hK10 : K ≤ 10 := by
    have hE := Mertens.E₁.le
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    rw [hK, hlog4]
    linarith [Real.log_two_lt_d9]
  have hy : (2 : ℝ) ≤ y := hx.trans hxy
  have hlx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hly : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlxy : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  -- split the head sums
  have hfloor : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  have hsplit : (∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with Nat.Prime p, (1 : ℝ) / p)
      + (∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (1 : ℝ) / p)
      = ∑ p ∈ Finset.Ioc 0 ⌊y⌋₊ with Nat.Prime p, (1 : ℝ) / p := by
    simp only [Finset.sum_filter]
    exact Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfloor
  have hxeq := Mertens.sum_prime_div_eq x
  have hyeq := Mertens.sum_prime_div_eq y
  have hEx := Mertens.E₂p.abs_le hx
  have hEy := Mertens.E₂p.abs_le hy
  -- the block sum is the difference of the two error terms
  have hblock : (∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (1 : ℝ) / p)
      - (Real.log (Real.log y) - Real.log (Real.log x))
      = Mertens.E₂p y - Mertens.E₂p x := by
    rw [← hsplit] at hyeq
    rw [hxeq] at hyeq
    linarith
  rw [hblock]
  -- and both are `O(1/log x)`
  have h1 : |Mertens.E₂p y| ≤ K / Real.log x :=
    hEy.trans (div_le_div_of_nonneg_left mertens_error_const_nonneg hlx hlxy)
  have h2 : |Mertens.E₂p x| ≤ K / Real.log x := hEx
  have h3 : |Mertens.E₂p y - Mertens.E₂p x| ≤ |Mertens.E₂p y| + |Mertens.E₂p x| :=
    abs_sub _ _
  have h4 : (0 : ℝ) < 1 / Real.log x := by positivity
  calc |Mertens.E₂p y - Mertens.E₂p x| ≤ K / Real.log x + K / Real.log x := by linarith
    _ ≤ 20 / Real.log x := by
        rw [show K / Real.log x + K / Real.log x = 2 * K / Real.log x by ring]
        gcongr
        linarith

/-- **Mertens over a block of bounded log-log length.**  For `2 ≤ y ≤ z` and `1 ≤ Λ` with
`log z ≤ Λ·log y`, `∑_{y < p ≤ z} 1/p ≤ log Λ + 20/log 2`, a bound depending only on `Λ`: the main
term of `RMF.abs_sum_prime_Ioc_inv_sub_log_log_sub_le` is at most `log Λ`.  The layered proof of
the upper bound `E|S(x)|^{2q} ≪ (log x)^{q(2q-1)}` for fixed `½ < q < 1` uses such a bound
`≍ log log x` times.  `Λ` is a parameter rather than `e` because its layers are integers, and the
floors force `Λ = 2e`; `RMF.sum_prime_Ioc_inv_le_of_log_le'` has the constant `1.86`. -/
theorem sum_prime_Ioc_inv_le_of_log_le {y z : ℕ} {Λ : ℝ} (hy : 2 ≤ y) (hyz : y ≤ z)
    (hΛ : 1 ≤ Λ) (hlog : Real.log z ≤ Λ * Real.log y) :
    (∑ p ∈ Finset.Ioc y z with Nat.Prime p, (1 : ℝ) / p)
      ≤ Real.log Λ + 20 / Real.log 2 := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  have hly : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlz : (0 : ℝ) < Real.log z := lt_of_lt_of_le hly (Real.log_le_log (by linarith) hyzR)
  have hkey := abs_sum_prime_Ioc_inv_sub_log_log_sub_le (y : ℝ) (z : ℝ) hy2 hyzR
  rw [Nat.floor_natCast, Nat.floor_natCast] at hkey
  -- `log z ≤ Λ·log y` is `log log z ≤ log Λ + log log y`
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hmain : Real.log (Real.log z) ≤ Real.log Λ + Real.log (Real.log y) := by
    have h := Real.log_le_log hlz hlog
    rwa [Real.log_mul (ne_of_gt hΛ0) (ne_of_gt hly)] at h
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2y : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy2
  have herr : 20 / Real.log y ≤ 20 / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) hlog2 hl2y
  have hub := (abs_le.1 hkey).2
  linarith

/-! ### The tilted block sum

What the Gaussian comparison is matched to is not `∑_{p∈B} 1/p` but the variance
`∑_{p∈B} ‖p^{-1/2-σ-it}‖² = ∑_{p∈B} p^{-1-2σ}`.  The extra `p^{-2σ}` is **not** `1 + o(1)`: over a
block it wanders over the whole of `[e^{-2}, e²]`, since `2σ log p` ranges over an interval of
length comparable to `1`.  So the block sum is only pinned two-sidedly, and that is genuinely all
that is true — which is exactly the form
`RMF.le_measure_Icc_gaussianReal_normalised_of_bounds` takes. -/

/-- **The tilt weight, per prime, at a general `η`.**  For `1 ≤ t ≤ y` with `|σ| log y ≤ η`,
`e^{-2η}/t ≤ t^{-1-2σ} ≤ e^{2η}/t`.

At `η = 1` this is the variance estimate; at `η = e^{m-n}` it is the *drift* estimate, where the
weight is `1 + O(η)` rather than merely confined to `[e^{-2}, e²]`. -/
lemma rpow_neg_one_sub_two_mul_bounds_of_le {t y σ η : ℝ} (ht : 1 ≤ t) (hty : t ≤ y)
    (hσ : |σ| * Real.log y ≤ η) :
    Real.exp (-(2 * η)) * (1 / t) ≤ t ^ (-1 - 2 * σ)
      ∧ t ^ (-1 - 2 * σ) ≤ Real.exp (2 * η) * (1 / t) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hσt : |σ| * Real.log t ≤ η :=
    le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log ht0 hty) (abs_nonneg σ)) hσ
  have hsplit : t ^ (-1 - 2 * σ) = t ^ (-(2 * σ)) * (1 / t) := by
    rw [show (-1 - 2 * σ : ℝ) = -(2 * σ) - 1 by ring, Real.rpow_sub ht0, Real.rpow_one,
      div_eq_mul_one_div]
  have hinv : (0 : ℝ) ≤ 1 / t := by positivity
  rw [hsplit]
  exact ⟨mul_le_mul_of_nonneg_right (le_rpow_neg_two_mul_of_le ht hσt) hinv,
    mul_le_mul_of_nonneg_right (rpow_neg_two_mul_le_of_le ht hσt) hinv⟩

/-- The case `η = 1`. -/
lemma rpow_neg_one_sub_two_mul_bounds {t y σ : ℝ} (ht : 1 ≤ t) (hty : t ≤ y)
    (hσ : |σ| * Real.log y ≤ 1) :
    Real.exp (-2) * (1 / t) ≤ t ^ (-1 - 2 * σ) ∧ t ^ (-1 - 2 * σ) ≤ Real.exp 2 * (1 / t) := by
  simpa using rpow_neg_one_sub_two_mul_bounds_of_le ht hty hσ

/-- **The tilted block sum is comparable to the unweighted one**, in both directions, with the
factors `e^{±2η}` under `|σ| log y ≤ η`.  No cancellation is available in the weight, so this is
sharp in order. -/
theorem sum_prime_Ioc_rpow_bounds_of_le {x y σ η : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y)
    (hσ : |σ| * Real.log y ≤ η) :
    Real.exp (-(2 * η)) * (∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (1 : ℝ) / p)
        ≤ ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - 2 * σ)
      ∧ ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - 2 * σ)
        ≤ Real.exp (2 * η) * (∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (1 : ℝ) / p) := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hkey : ∀ p ∈ {p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ | Nat.Prime p},
      Real.exp (-(2 * η)) * ((1 : ℝ) / p) ≤ (p : ℝ) ^ (-1 - 2 * σ)
        ∧ (p : ℝ) ^ (-1 - 2 * σ) ≤ Real.exp (2 * η) * ((1 : ℝ) / p) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hfx : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      have : 1 ≤ p := by omega
      exact_mod_cast this
    have hpy : (p : ℝ) ≤ y :=
      le_trans (by exact_mod_cast hp.1.2) (Nat.floor_le hy0)
    exact rpow_neg_one_sub_two_mul_bounds_of_le hp1 hpy hσ
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => (hkey p hp).1
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => (hkey p hp).2

/-- **The tilted block sum, two-sided** — block Mertens with the tilt weight carried through.  For
`2 ≤ x ≤ y` and `|σ| log y ≤ η`, with `M = log log y − log log x`,
`e^{-2η}(M − 20/log x) ≤ ∑_{x<p≤y} p^{-1-2σ} ≤ e^{2η}(M + 20/log x)`.
The `e^{±2η}` are irreducible (`RMF.rpow_neg_one_sub_two_mul_bounds_of_le`), whereas `20/log x` is a
genuine error term; it pushes the variance bounds slightly outside `[e^{-2η}, e^{2η}]`, which is why
`RMF.rpow_le_exp_neg_sq_div_of_bounds` takes them as parameters. -/
theorem sum_prime_Ioc_rpow_mertens_bounds_of_le (x y σ η : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y)
    (hσ : |σ| * Real.log y ≤ η) :
      Real.exp (-(2 * η)) * (Real.log (Real.log y) - Real.log (Real.log x) - 20 / Real.log x)
          ≤ ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - 2 * σ)
        ∧ ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - 2 * σ)
          ≤ Real.exp (2 * η)
            * (Real.log (Real.log y) - Real.log (Real.log x) + 20 / Real.log x) := by
  obtain ⟨hlo, hhi⟩ := sum_prime_Ioc_rpow_bounds_of_le hx hxy hσ
  have hm := abs_le.1 (abs_sum_prime_Ioc_inv_sub_log_log_sub_le x y hx hxy)
  have he₁ : (0 : ℝ) < Real.exp (-(2 * η)) := Real.exp_pos _
  have he₂ : (0 : ℝ) < Real.exp (2 * η) := Real.exp_pos _
  constructor
  · refine le_trans (mul_le_mul_of_nonneg_left ?_ he₁.le) hlo
    linarith [hm.1]
  · refine le_trans hhi (mul_le_mul_of_nonneg_left ?_ he₂.le)
    linarith [hm.2]

/-- **Harper's block, tilted**: for `X ≥ e^e` and `|σ| log X ≤ η`, the block `X^{1/e} < p ≤ X`
satisfies `e^{-2η}(1 − 60/log X) ≤ ∑_{p} p^{-1-2σ} ≤ e^{2η}(1 + 60/log X)`.  The main term is `1`
exactly, `log log X − log log X^{1/e} = 1`, which is why a block runs from `X^{1/e}` to `X`.  At
`η = 1` and `w_p = p^{-1/2-σ-it}` it discharges
`RMF.le_measure_Icc_gaussianReal_normalised_of_bounds` with `1/A = e^{-2}(1 − 60/log X)`, whose
condition `A < 9` holds once `log X ≥ 336`. -/
theorem sum_prime_block_rpow_bounds_of_le (X σ η : ℝ) (hX : Real.exp (Real.exp 1) ≤ X)
    (hσ : |σ| * Real.log X ≤ η) :
      Real.exp (-(2 * η)) * (1 - 60 / Real.log X)
          ≤ ∑ p ∈ Finset.Ioc ⌊X ^ (Real.exp 1)⁻¹⌋₊ ⌊X⌋₊ with Nat.Prime p,
              (p : ℝ) ^ (-1 - 2 * σ)
        ∧ ∑ p ∈ Finset.Ioc ⌊X ^ (Real.exp 1)⁻¹⌋₊ ⌊X⌋₊ with Nat.Prime p,
              (p : ℝ) ^ (-1 - 2 * σ)
          ≤ Real.exp (2 * η) * (1 + 60 / Real.log X) := by
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlX : Real.exp 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX0).2 hX
  have hlX0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le he0 hlX
  -- the lower end of the block
  have hx0 : (0 : ℝ) < X ^ (Real.exp 1)⁻¹ := Real.rpow_pos_of_pos hX0 _
  have hlogx : Real.log (X ^ (Real.exp 1)⁻¹) = Real.log X / Real.exp 1 := by
    rw [Real.log_rpow hX0, inv_mul_eq_div]
  have hlogx0 : (0 : ℝ) < Real.log (X ^ (Real.exp 1)⁻¹) := by
    rw [hlogx]; positivity
  have hx2 : (2 : ℝ) ≤ X ^ (Real.exp 1)⁻¹ := by
    refine le_trans he1 ((Real.le_log_iff_exp_le hx0).1 ?_)
    rw [hlogx, le_div_iff₀ he0, one_mul]
    exact hlX
  have hxX : X ^ (Real.exp 1)⁻¹ ≤ X := by
    refine (Real.log_le_log_iff hx0 hX0).1 ?_
    rw [hlogx, div_le_iff₀ he0]
    nlinarith
  -- the main term is `1`, on the nose
  have hll : Real.log (Real.log X) - Real.log (Real.log (X ^ (Real.exp 1)⁻¹)) = 1 := by
    rw [hlogx, Real.log_div hlX0.ne' he0.ne', Real.log_exp]
    ring
  -- and the error term transfers: `20/log(X^{1/e}) = 20e/log X ≤ 60/log X`
  have hCdiv : (20 : ℝ) / Real.log (X ^ (Real.exp 1)⁻¹) = 20 * Real.exp 1 / Real.log X := by
    rw [hlogx, div_div_eq_mul_div, mul_comm]
  obtain ⟨hlo, hhi⟩ :=
    sum_prime_Ioc_rpow_mertens_bounds_of_le (X ^ (Real.exp 1)⁻¹) X σ η hx2 hxX hσ
  rw [hll, hCdiv] at hlo hhi
  have h60 : (20 : ℝ) * Real.exp 1 / Real.log X ≤ 60 / Real.log X := by
    gcongr
    linarith [Real.exp_one_lt_d9]
  have he₁ : (0 : ℝ) < Real.exp (-(2 * η)) := Real.exp_pos _
  have he₂ : (0 : ℝ) < Real.exp (2 * η) := Real.exp_pos _
  constructor
  · refine le_trans (mul_le_mul_of_nonneg_left ?_ he₁.le) hlo
    linarith
  · refine le_trans hhi (mul_le_mul_of_nonneg_left ?_ he₂.le)
    linarith

/-- **The block sum's upper bound, with no `η` in it.**  For `X ≥ e^e` and `σ ≥ 0`,
`∑_{X^{1/e} < p ≤ X} p^{-1-2σ} ≤ 1 + 60/log X`, since `p^{-2σ} ≤ 1` termwise.  The two directions
are not symmetric: `1/A ≤ 2V` needs the lower bound, which degrades like `e^{-2η}` and is paid for
in `θ` (`RMF.thr_direct_of_offset`); the envelope needs only this upper one, where an `e^{40}`
would be fatal. -/
theorem sum_prime_block_rpow_le_of_nonneg (X σ : ℝ) (hX : Real.exp (Real.exp 1) ≤ X)
    (hσ : 0 ≤ σ) :
    ∑ p ∈ Finset.Ioc ⌊X ^ (Real.exp 1)⁻¹⌋₊ ⌊X⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - 2 * σ)
      ≤ 1 + 60 / Real.log X := by
  have h0 := (sum_prime_block_rpow_bounds_of_le X 0 0 hX (by simp)).2
  rw [mul_zero, Real.exp_zero, one_mul] at h0
  refine le_trans (Finset.sum_le_sum fun p hp => ?_) h0
  have hpp : Nat.Prime p := (Finset.mem_filter.1 hp).2
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
  exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)

/-- The case `η = 1`, the variance form. -/
theorem sum_prime_block_rpow_bounds (X σ : ℝ) (hX : Real.exp (Real.exp 1) ≤ X)
    (hσ : |σ| * Real.log X ≤ 1) :
      Real.exp (-2) * (1 - 60 / Real.log X)
          ≤ ∑ p ∈ Finset.Ioc ⌊X ^ (Real.exp 1)⁻¹⌋₊ ⌊X⌋₊ with Nat.Prime p,
              (p : ℝ) ^ (-1 - 2 * σ)
        ∧ ∑ p ∈ Finset.Ioc ⌊X ^ (Real.exp 1)⁻¹⌋₊ ⌊X⌋₊ with Nat.Prime p,
              (p : ℝ) ^ (-1 - 2 * σ)
          ≤ Real.exp 2 * (1 + 60 / Real.log X) := by
  simpa using sum_prime_block_rpow_bounds_of_le X σ 1 hX hσ

/-- **The block sum's deviation from `1`**, the form the *drift* estimate consumes:
`|∑_{p∈B} p^{-1-2σ} - 1| ≤ (e^{2η} - 1) + e^{2η}·(60/log X)`.  At `η = 1` this is useless
(`e² - 1 = 6.39`); but Harper's `|σ| ≤ 1/log x_n` is a bound at the **top** scale, so at block `m`
one takes `η = e^{m-n}` and the deviation is `O(e^{m-n})`, summable over `m`. -/
theorem abs_sum_prime_block_rpow_sub_one_le (X σ η : ℝ) (hη : 0 ≤ η)
    (hX : Real.exp (Real.exp 1) ≤ X) (hσ : |σ| * Real.log X ≤ η) :
    |(∑ p ∈ Finset.Ioc ⌊X ^ (Real.exp 1)⁻¹⌋₊ ⌊X⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - 2 * σ))
        - 1|
      ≤ (Real.exp (2 * η) - 1) + Real.exp (2 * η) * (60 / Real.log X) := by
  obtain ⟨hlo, hhi⟩ := sum_prime_block_rpow_bounds_of_le X σ η hX hσ
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlX : Real.exp 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX0).2 hX
  have hlX0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 1) hlX
  have hd : (0 : ℝ) ≤ 60 / Real.log X := by positivity
  have ha : (0 : ℝ) < Real.exp (2 * η) := Real.exp_pos _
  have hb : (0 : ℝ) < Real.exp (-(2 * η)) := Real.exp_pos _
  -- `e^{2η} + e^{-2η} ≥ 2`, i.e. `a + 1/a ≥ 2`
  have hab : Real.exp (2 * η) * Real.exp (-(2 * η)) = 1 := by
    rw [← Real.exp_add]; simp
  have hsum2 : (2 : ℝ) ≤ Real.exp (2 * η) + Real.exp (-(2 * η)) := by
    nlinarith [sq_nonneg (Real.exp (2 * η) - 1), hab, ha, hb]
  -- and `e^{-2η} ≤ e^{2η}`
  have hle : Real.exp (-(2 * η)) ≤ Real.exp (2 * η) := Real.exp_le_exp.2 (by linarith)
  rw [abs_le]
  constructor
  · nlinarith [hlo, hd, hsum2, hle]
  · nlinarith [hhi, hd, ha]

/-! ### The tilted tail: when the weight truncates the range

Everything above bounds `∑_{x<p≤y} p^{-1-2σ}` with `|σ| log y ≤ η`, `η = O(1)`, where the tilt is a
bounded distortion of Mertens.  Harper's Key Proposition 5 needs the *opposite* regime:
`σ = 4V/log x` on `(x^{1/V}, x]`, where `2σ log p ≥ 8` throughout and the weight is what makes the
sum converge at all.  `RMF.exists_sum_prime_Ioc_rpow_tail_le` bounds the tail `∑_{a<p≤b} p^{-1-s}`
by an **absolute constant** once `s log a ≥ 1`, however long the range.

**The proof is elementary.**  Cut `(a,b]` at the repeated squares `a, a², a⁴, …`.  On the `k`-th
block the weight is at most `e^{-2^k s log a}` and the Mertens mass is `log 2 + O(1/log a)`, the
`log log`s telescoping to `log 2` *exactly*; so the blocks contribute a geometric series in
`e^{-s log a} ≤ e^{-1}`.  Analytically this is `∫_{1/V}^1 e^{-8Vu} du/u ≤ E₁(8)`. -/

/-- **One dyadic block.**  Over `(a, a²]` the tilted sum is at most the weight at the left
endpoint times the block's Mertens mass, and that mass is `\log 2 + O(1/\log a)` because the two
`\log\log`s differ by exactly `\log 2`. -/
lemma sum_prime_Ioc_rpow_sq_block_le {a s : ℝ} (ha : 2 ≤ a) (hs : 0 ≤ s) :
    (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊a ^ 2⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - s))
      ≤ Real.exp (-(s * Real.log a)) * (Real.log 2 + 20 / Real.log a) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hla : (0 : ℝ) < Real.log a := Real.log_pos (by linarith)
  have haa : a ≤ a ^ 2 := by nlinarith
  -- the weight is at most its value at the left endpoint
  have hmain : (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊a ^ 2⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - s))
      ≤ ∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊a ^ 2⌋₊ with Nat.Prime p, a ^ (-s) * ((1 : ℝ) / p) := by
    refine Finset.sum_le_sum fun p hp => ?_
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hap : a < (p : ℝ) := (Nat.floor_lt ha0.le).1 hp.1.1
    have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans ha0 hap
    have hsplit : (p : ℝ) ^ (-1 - s) = (p : ℝ) ^ (-s) * (p : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hp0]
      ring_nf
    have hw : (p : ℝ) ^ (-s) ≤ a ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos ha0 hap.le (by linarith)
    rw [hsplit, Real.rpow_neg_one, one_div]
    exact mul_le_mul_of_nonneg_right hw (by positivity)
  refine le_trans hmain ?_
  rw [← Finset.mul_sum]
  -- Mertens over the block: the two `log log`s differ by exactly `log 2`
  have hmert := abs_sum_prime_Ioc_inv_sub_log_log_sub_le a (a ^ 2) ha haa
  have hlogsq : Real.log (a ^ 2) = 2 * Real.log a := by
    rw [Real.log_pow]
    push_cast
    ring
  have hll : Real.log (Real.log (a ^ 2)) = Real.log 2 + Real.log (Real.log a) := by
    rw [hlogsq, Real.log_mul (by norm_num) hla.ne']
  rw [abs_le] at hmert
  have hmass : (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊a ^ 2⌋₊ with Nat.Prime p, (1 : ℝ) / p)
      ≤ Real.log 2 + 20 / Real.log a := by
    have h := hmert.2
    rw [hll] at h
    linarith
  have hwpos : a ^ (-s) = Real.exp (-(s * Real.log a)) := by
    rw [Real.rpow_def_of_pos ha0]
    ring_nf
  rw [hwpos]
  exact mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le

/-- **The dyadic bound.**  If `\log b` is within `2^n` doublings of `\log a`, the tail is bounded
by the geometric sum of the `n` block weights. -/
lemma sum_prime_Ioc_rpow_dyadic_le {s : ℝ} (hs : 0 ≤ s) :
    ∀ (n : ℕ) (a b : ℝ), 2 ≤ a → a ≤ b → Real.log b ≤ 2 ^ n * Real.log a →
      (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - s))
        ≤ (Real.log 2 + 20 / Real.log a)
            * ∑ k ∈ Finset.range n, Real.exp (-(2 ^ k * (s * Real.log a))) := by
  intro n
  induction n with
  | zero =>
    intro a b ha hab hlog
    have ha0 : (0 : ℝ) < a := by linarith
    have hb0 : (0 : ℝ) < b := by linarith
    have hba : b ≤ a := by
      have hl : Real.log b ≤ Real.log a := by simpa using hlog
      calc b = Real.exp (Real.log b) := (Real.exp_log hb0).symm
        _ ≤ Real.exp (Real.log a) := Real.exp_le_exp.2 hl
        _ = a := Real.exp_log ha0
    have hfl : ⌊b⌋₊ ≤ ⌊a⌋₊ := Nat.floor_mono hba
    have hempty : Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ = ∅ := Finset.Ioc_eq_empty (by omega)
    simp [hempty]
  | succ n ih =>
    intro a b ha hab hlog
    have ha0 : (0 : ℝ) < a := by linarith
    have hla : (0 : ℝ) < Real.log a := Real.log_pos (by linarith)
    have ha2 : (2 : ℝ) ≤ a ^ 2 := by nlinarith
    have haa : a ≤ a ^ 2 := by nlinarith
    have hlogsq : Real.log (a ^ 2) = 2 * Real.log a := by
      rw [Real.log_pow]; push_cast; ring
    have hblock := sum_prime_Ioc_rpow_sq_block_le ha hs
    have hcoef : (0 : ℝ) ≤ Real.log 2 + 20 / Real.log a := by
      have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    have hrest : (0 : ℝ) ≤ (Real.log 2 + 20 / Real.log a)
        * ∑ k ∈ Finset.range n, Real.exp (-(2 ^ (k + 1) * (s * Real.log a))) :=
      mul_nonneg hcoef (Finset.sum_nonneg fun k _ => (Real.exp_pos _).le)
    have hblock' : (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊a ^ 2⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - s))
        ≤ (Real.log 2 + 20 / Real.log a) * Real.exp (-(s * Real.log a)) := by
      rw [mul_comm]; exact hblock
    rw [Finset.sum_range_succ', pow_zero, one_mul]
    have hexpand : (Real.log 2 + 20 / Real.log a)
        * ((∑ k ∈ Finset.range n, Real.exp (-(2 ^ (k + 1) * (s * Real.log a))))
            + Real.exp (-(s * Real.log a)))
        = (Real.log 2 + 20 / Real.log a)
            * ∑ k ∈ Finset.range n, Real.exp (-(2 ^ (k + 1) * (s * Real.log a)))
          + (Real.log 2 + 20 / Real.log a) * Real.exp (-(s * Real.log a)) := by ring
    rw [hexpand]
    rcases le_or_gt b (a ^ 2) with hb | hb
    · -- one block already covers `(a, b]`
      have hsub : Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ ⊆ Finset.Ioc ⌊a⌋₊ ⌊a ^ 2⌋₊ :=
        Finset.Ioc_subset_Ioc_right (Nat.floor_mono hb)
      have hmono : (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - s))
          ≤ ∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊a ^ 2⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hsub)
          fun p _ _ => Real.rpow_nonneg (by positivity) _
      linarith
    · -- split off the first block and recurse
      have hsplit : (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊a ^ 2⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - s))
          + (∑ p ∈ Finset.Ioc ⌊a ^ 2⌋₊ ⌊b⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - s))
          = ∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - s) := by
        simp only [Finset.sum_filter]
        exact Finset.sum_Ioc_consecutive _ (Nat.floor_mono haa) (Nat.floor_mono hb.le)
      have hlog' : Real.log b ≤ 2 ^ n * Real.log (a ^ 2) := by
        rw [hlogsq]
        calc Real.log b ≤ 2 ^ (n + 1) * Real.log a := hlog
          _ = 2 ^ n * (2 * Real.log a) := by ring
      have hIH := ih (a ^ 2) b ha2 hb.le hlog'
      have hcoef' : Real.log 2 + 20 / Real.log (a ^ 2) ≤ Real.log 2 + 20 / Real.log a := by
        rw [hlogsq]
        have hd : 20 / (2 * Real.log a) ≤ 20 / Real.log a :=
          div_le_div_of_nonneg_left (by norm_num) hla (by linarith)
        linarith
      have hterms : ∀ k ∈ Finset.range n,
          Real.exp (-(2 ^ k * (s * Real.log (a ^ 2))))
            = Real.exp (-(2 ^ (k + 1) * (s * Real.log a))) := by
        intro k _
        rw [hlogsq]
        ring_nf
      rw [Finset.sum_congr rfl hterms] at hIH
      have hsum0 : (0 : ℝ)
          ≤ ∑ k ∈ Finset.range n, Real.exp (-(2 ^ (k + 1) * (s * Real.log a))) :=
        Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
      have hIH' : (∑ p ∈ Finset.Ioc ⌊a ^ 2⌋₊ ⌊b⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - s))
          ≤ (Real.log 2 + 20 / Real.log a)
              * ∑ k ∈ Finset.range n, Real.exp (-(2 ^ (k + 1) * (s * Real.log a))) :=
        le_trans hIH (mul_le_mul_of_nonneg_right hcoef' hsum0)
      linarith

/-- **The tilted tail is an absolute constant.**  For `s\log a ≥ 1` and any `b`,
`∑_{a<p≤b} p^{-1-s} ≤ C`.

This is Harper's `∑_{x^{1/V}<p≤x} p^{-1-8V/\log x} = O(1)`, at `a = x^{1/V}` and `s = 8V/\log x`,
where the hypothesis reads `s\log a = 8 ≥ 1`. -/
theorem exists_sum_prime_Ioc_rpow_tail_le :
    ∃ C > 0, ∀ (s a b : ℝ), 0 ≤ s → 2 ≤ a → a ≤ b → 1 ≤ s * Real.log a →
      (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - s)) ≤ C := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have he1 : Real.exp (-1 : ℝ) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have he0 : (0 : ℝ) < Real.exp (-1 : ℝ) := Real.exp_pos _
  refine ⟨(Real.log 2 + 20 / Real.log 2) * (Real.exp (-1 : ℝ) * (1 - Real.exp (-1 : ℝ))⁻¹),
    by positivity, fun s a b hs ha hab hL => ?_⟩
  have ha0 : (0 : ℝ) < a := by linarith
  have hla : (0 : ℝ) < Real.log a := Real.log_pos (by linarith)
  have hla2 : Real.log 2 ≤ Real.log a := Real.log_le_log (by norm_num) ha
  have hb0 : (0 : ℝ) < b := by linarith
  -- choose `n` with `log b ≤ 2^n log a`
  set n : ℕ := ⌈Real.log b / Real.log a⌉₊ with hn
  have hnge : Real.log b / Real.log a ≤ (n : ℝ) := Nat.le_ceil _
  have h2n : ((n : ℝ)) ≤ 2 ^ n := by
    have := Nat.lt_two_pow_self (n := n)
    have : (n : ℝ) < ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hlog : Real.log b ≤ 2 ^ n * Real.log a := by
    rw [div_le_iff₀ hla] at hnge
    nlinarith [hnge, h2n, hla]
  refine le_trans (sum_prime_Ioc_rpow_dyadic_le hs n a b ha hab hlog) ?_
  -- the geometric bound on the block weights
  have hgeo : ∀ k : ℕ, Real.exp (-(2 ^ k * (s * Real.log a))) ≤ Real.exp (-1 : ℝ) ^ (k + 1) := by
    intro k
    have hk : ((k : ℝ) + 1) ≤ 2 ^ k := by
      have := Nat.lt_two_pow_self (n := k)
      have h : (k : ℝ) < ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h
      have hint : (k : ℝ) + 1 ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.lt_two_pow_self
      push_cast at hint
      linarith
    have hmul : ((k : ℝ) + 1) ≤ 2 ^ k * (s * Real.log a) := by nlinarith [hk, hL]
    calc Real.exp (-(2 ^ k * (s * Real.log a))) ≤ Real.exp (-((k : ℝ) + 1)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = Real.exp (-1 : ℝ) ^ (k + 1) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
  have hsum : (∑ k ∈ Finset.range n, Real.exp (-(2 ^ k * (s * Real.log a))))
      ≤ Real.exp (-1 : ℝ) * (1 - Real.exp (-1 : ℝ))⁻¹ := by
    have hstep : (∑ k ∈ Finset.range n, Real.exp (-(2 ^ k * (s * Real.log a))))
        ≤ ∑ k ∈ Finset.range n, Real.exp (-1 : ℝ) ^ (k + 1) :=
      Finset.sum_le_sum fun k _ => hgeo k
    have hgeom : (∑ k ∈ Finset.range n, Real.exp (-1 : ℝ) ^ (k + 1))
        ≤ Real.exp (-1 : ℝ) * (1 - Real.exp (-1 : ℝ))⁻¹ := by
      have hfac : ∀ k : ℕ, Real.exp (-1 : ℝ) ^ (k + 1)
          = Real.exp (-1 : ℝ) * Real.exp (-1 : ℝ) ^ k := fun k => by ring
      rw [Finset.sum_congr rfl fun k _ => hfac k, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ he0.le
      have hsummable : Summable (fun k : ℕ => Real.exp (-1 : ℝ) ^ k) :=
        summable_geometric_of_lt_one he0.le he1
      calc (∑ k ∈ Finset.range n, Real.exp (-1 : ℝ) ^ k)
          ≤ ∑' k : ℕ, Real.exp (-1 : ℝ) ^ k :=
            hsummable.sum_le_tsum _ (fun k _ => by positivity)
        _ = (1 - Real.exp (-1 : ℝ))⁻¹ := tsum_geometric_of_lt_one he0.le he1
    linarith
  have hcoef : Real.log 2 + 20 / Real.log a ≤ Real.log 2 + 20 / Real.log 2 := by
    have : 20 / Real.log a ≤ 20 / Real.log 2 :=
      div_le_div_of_nonneg_left (by norm_num) hl2 hla2
    linarith
  have hsum0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range n, Real.exp (-(2 ^ k * (s * Real.log a))) :=
    Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
  have hcoef0 : (0 : ℝ) ≤ Real.log 2 + 20 / Real.log a := by positivity
  calc (Real.log 2 + 20 / Real.log a)
        * ∑ k ∈ Finset.range n, Real.exp (-(2 ^ k * (s * Real.log a)))
      ≤ (Real.log 2 + 20 / Real.log 2)
        * ∑ k ∈ Finset.range n, Real.exp (-(2 ^ k * (s * Real.log a))) :=
        mul_le_mul_of_nonneg_right hcoef hsum0
    _ ≤ (Real.log 2 + 20 / Real.log 2) * (Real.exp (-1 : ℝ) * (1 - Real.exp (-1 : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)

end RMF
