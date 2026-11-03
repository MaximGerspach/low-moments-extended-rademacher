/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.CosinePrimeSum

/-!
# The two log-weighted prime sums of the smoothing error

The error term of the smoothing step in the lower-bound reduction (Harper's Proposition 3) bounds
the discrepancy by `x/(pX) + 1` for each prime `p`, and then sums that against the weight `log p`.
The sum splits into exactly two classical pieces:

`∑_{p ≤ x} log p · (x/(pX) + 1) = (x/X) ∑_{p ≤ x} (log p)/p + ∑_{p ≤ x} log p`,

Mertens' first theorem and Chebyshev's `θ`.  Both are already available: Mertens in the explicit
form `PrimeNumberTheoremAnd.IEANTN.Mertens`, Chebyshev as `Chebyshev.theta_le_log4_mul_x` in
Mathlib.  Nothing here is new mathematics; the file exists so that the reduction can quote a
single inequality with the constants written out.

## Why `X ≈ log x` is forced

The first piece is `≈ x log x / X` and the second is `≤ log 4 · x`.  For the error to stay within
the `O(x)` that Proposition 3 allows, the smoothing scale must satisfy `X ≫ log x` — and taking
`X = log x` makes the two pieces comparable, which is why Harper's subtracted term is
`√(x/log x)`.  Pushing `X` any higher costs a stronger prime input in the main term
(`RMF.window_weight_ge`) without buying anything here.
-/

open Finset

namespace RMF

/-- **Mertens' first theorem, one-sided.**  `∑_{p ≤ x} (log p)/p ≤ log x + log 4 + 4`.

This is `Mertens.E₁p.le` rearranged; the constant `log 4 + 4 ≈ 5.39` is the one PNT+ proves, not
the true `≈ 1.33`, and nothing downstream is sensitive to it. -/
theorem sum_log_div_prime_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / p
      ≤ Real.log x + Real.log 4 + 4 := by
  have heq := Mertens.sum_log_prime_div_eq x
  have hle := Mertens.E₁p.le hx
  linarith

/-- **Chebyshev's bound.**  `∑_{p ≤ x} log p ≤ log 4 · x`, with the sum written out rather than
as `Chebyshev.theta`. -/
theorem sum_log_prime_le {x : ℝ} (hx : 0 ≤ x) :
    ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p ≤ Real.log 4 * x :=
  Chebyshev.theta_le_log4_mul_x hx

/-- Every term of either sum is nonnegative. -/
lemma log_div_natCast_nonneg (p : ℕ) : 0 ≤ Real.log p / p :=
  div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/-- **The arithmetic of the error term.**  The `log p`-weighted sum of the per-prime discrepancy
bound `x/(pX) + 1`, over any set `S` of primes below `x`.

Leaving `S` arbitrary is deliberate: the reduction sums over `√x < p ≤ x`, but the bound only
ever uses `S ⊆ {p ≤ x : p prime}`, and both pieces are sums of nonnegative terms. -/
theorem sum_log_prime_mul_smoothing_le {x X : ℝ} (hx : 1 ≤ x) (hX : 0 < X) {S : Finset ℕ}
    (hS : S ⊆ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime}) :
    ∑ p ∈ S, Real.log p * (x / (p * X) + 1)
      ≤ x * (Real.log x + Real.log 4 + 4) / X + Real.log 4 * x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hX0 : X ≠ 0 := ne_of_gt hX
  have hprime : ∀ p ∈ S, Nat.Prime p := fun p hp => (Finset.mem_filter.1 (hS hp)).2
  -- split the summand
  have hsplit : ∀ p ∈ S, Real.log p * (x / (p * X) + 1)
      = x / X * (Real.log p / p) + Real.log p := by
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hprime p hp).ne_zero
    field_simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- Mertens for the first piece
  have hA : ∑ p ∈ S, Real.log p / p ≤ Real.log x + Real.log 4 + 4 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hS ?_) (sum_log_div_prime_le hx)
    exact fun p _ _ => log_div_natCast_nonneg p
  -- Chebyshev for the second
  have hB : ∑ p ∈ S, Real.log p ≤ Real.log 4 * x := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hS ?_) (sum_log_prime_le hx0)
    exact fun p _ _ => Real.log_natCast_nonneg p
  have hxX : (0 : ℝ) ≤ x / X := by positivity
  have hmul := mul_le_mul_of_nonneg_left hA hxX
  have heq : x / X * (Real.log x + Real.log 4 + 4)
      = x * (Real.log x + Real.log 4 + 4) / X := by ring
  linarith

/-! ### The main term: the window weight

Swapping the sum over primes with the `t`-integral in the smoothing step turns
`∑_{p} log p · (X/p) ∫_p^{p(1+1/X)} G(t) dt` into `∫ G(t) w(t) dt`, where

`w(t) = X ∑_{p < t ≤ p(1+1/X)} (log p)/p = X ∑_{s ≤ p < t} (log p)/p`,  `s := t/(1+1/X)`.

Since `p ≤ t` in that range, `w(t) ≥ (X/t)(θ(t) - θ(s) - log t)`, and `θ(t) - θ(s) ≈ t - s
= t/(X+1)`, so `w(t) ≈ X/(X+1) ≈ 1`.  The prime input is `RS_prime.pnt`, and it is the *only*
place in the lower-bound reduction where the prime number theorem is needed. -/

/-- The primes the smoothing window at `t` picks up: those with `s < p < t`.  Membership is
recorded through `⌊s⌋ < p ≤ ⌊t⌋` together with the real condition `p < t`, so that the sum can be
compared with `θ(t) - θ(s)` on the one hand and sits inside the window's index set on the other. -/
noncomputable def windowPrimes (s t : ℝ) : Finset ℕ :=
  {p ∈ Finset.Ioc ⌊s⌋₊ ⌊t⌋₊ | p.Prime ∧ (p : ℝ) < t}

/-- Every element of `RMF.windowPrimes s t` is a prime in `(s, t)`. -/
lemma windowPrimes_spec {s t : ℝ} {p : ℕ} (hp : p ∈ windowPrimes s t) :
    p.Prime ∧ s < p ∧ (p : ℝ) < t := by
  rw [windowPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨hp.2.1, ?_, hp.2.2⟩
  have h := hp.1.1
  have : s < (⌊s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s
  have hcast : (⌊s⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast h
  linarith

/-- `θ t - θ s` is the sum of `log p` over the primes in `(s, t]`. -/
lemma theta_sub_theta_eq {s t : ℝ} (hst : ⌊s⌋₊ ≤ ⌊t⌋₊) :
    Chebyshev.theta t - Chebyshev.theta s
      = ∑ p ∈ Finset.Ioc ⌊s⌋₊ ⌊t⌋₊ with p.Prime, Real.log p := by
  have hsub : {p ∈ Finset.Ioc 0 ⌊s⌋₊ | p.Prime} ⊆ {p ∈ Finset.Ioc 0 ⌊t⌋₊ | p.Prime} :=
    Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right hst)
  have hdiff : {p ∈ Finset.Ioc 0 ⌊t⌋₊ | p.Prime} \ {p ∈ Finset.Ioc 0 ⌊s⌋₊ | p.Prime}
      = {p ∈ Finset.Ioc ⌊s⌋₊ ⌊t⌋₊ | p.Prime} := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, not_and]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3⟩
      refine ⟨⟨?_, h2⟩, hp⟩
      by_contra h
      exact absurd hp (h3 ⟨h1, by omega⟩)
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨⟨by omega, h2⟩, hp⟩, fun h => absurd h.2 (by omega)⟩
  simp only [Chebyshev.theta]
  rw [← Finset.sum_sdiff_eq_sub hsub, hdiff]

/-- The window sum loses at most one prime against `θ(t) - θ(s)` — namely `t` itself, when `t` is
a prime integer, which the strict inequality `p < t` excludes. -/
lemma sum_log_windowPrimes_ge {s t : ℝ} (hst : ⌊s⌋₊ ≤ ⌊t⌋₊) (ht : 1 ≤ t) :
    Chebyshev.theta t - Chebyshev.theta s - Real.log t
      ≤ ∑ p ∈ windowPrimes s t, Real.log p := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hsub : windowPrimes s t ⊆ {p ∈ Finset.Ioc ⌊s⌋₊ ⌊t⌋₊ | p.Prime} := by
    intro p hp
    rw [windowPrimes, Finset.mem_filter] at hp
    exact Finset.mem_filter.2 ⟨hp.1, hp.2.1⟩
  -- the discarded terms all sit at `p = ⌊t⌋`
  have hone : {p ∈ Finset.Ioc ⌊s⌋₊ ⌊t⌋₊ | p.Prime} \ windowPrimes s t ⊆ {⌊t⌋₊} := by
    intro p hp
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, windowPrimes,
      Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨⟨h1, h2⟩, hprime⟩, hnot⟩ := hp
    have hge : t ≤ (p : ℝ) := by
      by_contra hlt
      exact hnot ⟨⟨h1, h2⟩, hprime, by linarith⟩
    have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
    have : (⌊t⌋₊ : ℝ) ≤ (p : ℝ) := by linarith
    have : ⌊t⌋₊ ≤ p := by exact_mod_cast this
    simp only [Finset.mem_singleton]
    omega
  have hlast : ∑ p ∈ {p ∈ Finset.Ioc ⌊s⌋₊ ⌊t⌋₊ | p.Prime} \ windowPrimes s t, Real.log p
      ≤ Real.log t := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hone
      (fun p _ _ => Real.log_natCast_nonneg p)) ?_
    rw [Finset.sum_singleton]
    have h1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
    have hpos : (0 : ℝ) < (⌊t⌋₊ : ℝ) := by exact_mod_cast h1
    exact Real.log_le_log hpos (Nat.floor_le ht0)
  have hsplit : ∑ p ∈ {p ∈ Finset.Ioc ⌊s⌋₊ ⌊t⌋₊ | p.Prime} \ windowPrimes s t, Real.log p
      = (∑ p ∈ {p ∈ Finset.Ioc ⌊s⌋₊ ⌊t⌋₊ | p.Prime}, Real.log p)
        - ∑ p ∈ windowPrimes s t, Real.log p := Finset.sum_sdiff_eq_sub hsub
  rw [theta_sub_theta_eq hst]
  linarith

/-- **The prime number theorem, as the window weight uses it.**  With `C` from `RS_prime.pnt`,
`θ(t) - θ(s) ≥ (t - s) - C(t/log²t + s/log²s)` for `2 ≤ s ≤ t`. -/
lemma theta_sub_theta_ge {C : ℝ}
    (hC : ∀ u : ℝ, 2 ≤ u → |Chebyshev.theta u - u| ≤ C * u / Real.log u ^ 2)
    {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) :
    t - s - (C * t / Real.log t ^ 2 + C * s / Real.log s ^ 2)
      ≤ Chebyshev.theta t - Chebyshev.theta s := by
  have h1 := abs_le.1 (hC t (by linarith))
  have h2 := abs_le.1 (hC s hs)
  linarith [h1.1, h2.2]

/-- `exp(X/2)` beats `X⁴/1024`, from the quadratic lower bound on `exp` applied at `X/4`.
This is what makes the boundary term `X log t / t` of the window weight negligible. -/
lemma pow_four_le_exp_half {X : ℝ} (hX : 0 ≤ X) : X ^ 4 / 1024 ≤ Real.exp (X / 2) := by
  have hq : X ^ 2 / 32 ≤ Real.exp (X / 4) := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ X / 4 by linarith)
    nlinarith
  have h0 : (0 : ℝ) ≤ X ^ 2 / 32 := by positivity
  have hmul : X ^ 2 / 32 * (X ^ 2 / 32) ≤ Real.exp (X / 4) * Real.exp (X / 4) :=
    mul_le_mul hq hq h0 (le_trans h0 hq)
  have hexp : Real.exp (X / 4) * Real.exp (X / 4) = Real.exp (X / 2) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hexp] at hmul
  nlinarith

/-- The numeric content of `RMF.window_weight_ge`, with `L` standing for `log t`.

The three pieces of `X/(X+1) - 5CX/L² - XL/t` are `≥ 1 - 1/X`, `≤ 20C/X` and `≤ 1024/X²`, and
`X ≥ 200 + 80C` makes the last two at most `1/4` each. -/
lemma window_weight_numeric {C X L t : ℝ} (hC0 : 0 ≤ C) (hX : 200 + 80 * C ≤ X)
    (hLlb : X / 2 ≤ L) (hLub : L ≤ X) (hXt : X ^ 4 / 1024 ≤ t) :
    (1 : ℝ) / 2 ≤ X / (X + 1) - 5 * C * X / L ^ 2 - X * L / t := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hd4 : (0 : ℝ) < X ^ 4 / 1024 := by positivity
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hd4 hXt
  have hb1 : 1 - 1 / X ≤ X / (X + 1) := by
    have h : X / (X + 1) - (1 - 1 / X) = 1 / (X * (X + 1)) := by
      field_simp
      ring
    have hp : (0 : ℝ) < 1 / (X * (X + 1)) := by positivity
    linarith
  have hb2 : 5 * C * X / L ^ 2 ≤ 20 * C / X := by
    have hden : X ^ 2 / 4 ≤ L ^ 2 := by nlinarith
    have hd0 : (0 : ℝ) < X ^ 2 / 4 := by positivity
    have h1 : 5 * C * X / L ^ 2 ≤ 5 * C * X / (X ^ 2 / 4) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hd0 hden) (by positivity)
    have h2 : 5 * C * X / (X ^ 2 / 4) = 20 * C / X := by
      field_simp
      ring
    linarith
  have hb3 : X * L / t ≤ 1024 / X ^ 2 := by
    have hnum : X * L ≤ X ^ 2 := by nlinarith
    have h1 : X * L / t ≤ X ^ 2 / (X ^ 4 / 1024) := by
      calc X * L / t ≤ X ^ 2 / t := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right hnum (by positivity)
        _ ≤ X ^ 2 / (X ^ 4 / 1024) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left (inv_anti₀ hd4 hXt) (by positivity)
    have h2 : X ^ 2 / (X ^ 4 / 1024) = 1024 / X ^ 2 := by field_simp
    linarith
  have hc1 : 1 / X + 20 * C / X ≤ 1 / 4 := by
    rw [← add_div, div_le_iff₀ hX0]
    linarith
  have hc2 : 1024 / X ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < X ^ 2)]
    nlinarith
  linarith

/-- **The window weight bound.**  At the smoothing scale `X = log x`, the window weight
`w(t) = X ∑_{p < t ≤ p(1+1/X)} (log p)/p` is at least `1/2`, for every `t ∈ [√x, x]` and every `x`
past an absolute threshold; the true value is `≈ X/(X+1) ≈ 1`.  `T` is any finite set of naturals
containing the primes of the window, every term being nonnegative. -/
theorem window_weight_ge :
    ∃ x₀ : ℝ, ∀ x t : ℝ, x₀ ≤ x → Real.sqrt x ≤ t → t ≤ x →
      ∀ T : Finset ℕ,
        (∀ p : ℕ, p.Prime → (p : ℝ) < t → t ≤ p * (1 + 1 / Real.log x) → p ∈ T) →
        (1 : ℝ) / 2 ≤ Real.log x * ∑ p ∈ T, Real.log p / p := by
  obtain ⟨C, hC0, hC⟩ := RS_prime.pnt
  refine ⟨Real.exp (200 + 80 * C), fun x t hx hsx htx T hT => ?_⟩
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hX : 200 + 80 * C ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hX0 : (0 : ℝ) < Real.log x := by linarith
  have hsqrt : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by rw [hsqrt]; exact Real.exp_pos _) hsx
  have hLlb : Real.log x / 2 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le ht0, ← hsqrt]
    exact hsx
  have hLub : Real.log t ≤ Real.log x := Real.log_le_log ht0 htx
  have hXt : Real.log x ^ 4 / 1024 ≤ t := by
    refine le_trans (pow_four_le_exp_half hX0.le) ?_
    rw [← hsqrt]
    exact hsx
  have hlogt : (100 : ℝ) ≤ Real.log t := by linarith
  have hlogt0 : (0 : ℝ) < Real.log t := by linarith
  have ht101 : (101 : ℝ) ≤ t := by
    have hexp : Real.log x / 2 + 1 ≤ Real.exp (Real.log x / 2) := Real.add_one_le_exp _
    rw [hsqrt] at hsx
    linarith
  -- the lower endpoint of the window
  set r : ℝ := 1 + 1 / Real.log x with hrdef
  have hr0 : (0 : ℝ) < r := by
    have : (0 : ℝ) < 1 / Real.log x := by positivity
    linarith
  have hr1 : (1 : ℝ) < r := by
    have : (0 : ℝ) < 1 / Real.log x := by positivity
    linarith
  have hr2 : r ≤ 2 := by
    have h : 1 / Real.log x ≤ 1 := by
      rw [div_le_one hX0]
      linarith
    linarith
  set s : ℝ := t / r with hsdef
  have hsr : s * r = t := by
    rw [hsdef]
    field_simp
  have hst : s ≤ t := by nlinarith
  have hs2 : t / 2 ≤ s := by nlinarith
  have hs0 : (2 : ℝ) ≤ s := by linarith
  have hs4 : (4 : ℝ) ≤ t := by linarith
  -- `log s ≥ (log t)/2`, because `s ≥ t/2 ≥ √t`
  have hlogs : Real.log t / 2 ≤ Real.log s := by
    have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (by linarith)
    have h2 : (2 : ℝ) ≤ Real.sqrt t := by
      have h4 : Real.sqrt 4 ≤ Real.sqrt t := Real.sqrt_le_sqrt (by linarith)
      rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h4
    have h3 : Real.sqrt t ≤ s := by nlinarith [Real.sqrt_nonneg t]
    have h5 := Real.log_le_log (Real.sqrt_pos.2 (by linarith)) h3
    rwa [Real.log_sqrt (by linarith)] at h5
  have hlogs0 : (0 : ℝ) < Real.log s := by linarith
  -- the window's primes lie in `T`
  have hsub : windowPrimes s t ⊆ T := by
    intro p hp
    obtain ⟨hprime, hps, hpt⟩ := windowPrimes_spec hp
    exact hT p hprime hpt (by nlinarith)
  have hmono : ∑ p ∈ windowPrimes s t, Real.log p / p ≤ ∑ p ∈ T, Real.log p / p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => log_div_natCast_nonneg p
  -- on the window `p ≤ t`, so `log p / p ≥ log p / t`
  have hdiv : (∑ p ∈ windowPrimes s t, Real.log p) / t
      ≤ ∑ p ∈ windowPrimes s t, Real.log p / p := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hprime, hps, hpt⟩ := windowPrimes_spec hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hp0 hpt.le) (Real.log_natCast_nonneg p)
  -- the prime number theorem
  have hfl : ⌊s⌋₊ ≤ ⌊t⌋₊ := Nat.floor_mono hst
  have hstep4 := sum_log_windowPrimes_ge hfl (by linarith)
  have hstep5 := theta_sub_theta_ge hC hs0 hst
  have htsub : t - s = t / (Real.log x + 1) := by
    rw [hsdef, hrdef]
    field_simp
    ring
  have hkey2 : C * s / Real.log s ^ 2 ≤ 4 * (C * t / Real.log t ^ 2) := by
    have hden : (Real.log t / 2) ^ 2 ≤ Real.log s ^ 2 := by nlinarith
    have hd0 : (0 : ℝ) < (Real.log t / 2) ^ 2 := by positivity
    have hnum : C * s ≤ C * t := mul_le_mul_of_nonneg_left hst hC0
    have h1 : C * s / Real.log s ^ 2 ≤ C * t / (Real.log t / 2) ^ 2 := by
      calc C * s / Real.log s ^ 2 ≤ C * t / Real.log s ^ 2 := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right hnum (by positivity)
        _ ≤ C * t / (Real.log t / 2) ^ 2 := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left (inv_anti₀ hd0 hden)
              (mul_nonneg hC0 ht0.le)
    have h2 : C * t / (Real.log t / 2) ^ 2 = 4 * (C * t / Real.log t ^ 2) := by
      field_simp
      ring
    linarith
  -- assemble
  have h1 : t / (Real.log x + 1) - 5 * (C * t / Real.log t ^ 2) - Real.log t
      ≤ ∑ p ∈ windowPrimes s t, Real.log p := by linarith
  have h2 : (t / (Real.log x + 1) - 5 * (C * t / Real.log t ^ 2) - Real.log t) / t
      ≤ (∑ p ∈ windowPrimes s t, Real.log p) / t := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have h5 := mul_le_mul_of_nonneg_left (le_trans (le_trans h2 hdiv) hmono) hX0.le
  have hexpand : Real.log x
      * ((t / (Real.log x + 1) - 5 * (C * t / Real.log t ^ 2) - Real.log t) / t)
      = Real.log x / (Real.log x + 1) - 5 * C * Real.log x / Real.log t ^ 2
        - Real.log x * Real.log t / t := by
    have h1' : t ≠ 0 := ne_of_gt ht0
    have h2' : Real.log x + 1 ≠ 0 := by positivity
    have h3' : Real.log t ≠ 0 := ne_of_gt hlogt0
    field_simp
  rw [hexpand] at h5
  exact le_trans (window_weight_numeric hC0 hX hLlb hLub hXt) h5

end RMF
