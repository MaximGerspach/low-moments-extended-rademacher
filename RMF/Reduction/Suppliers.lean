/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.ConditionalExpectation
import RMF.SecondMoment
import RMF.EulerProduct.Defs
import RMF.Main
import PrimeNumberTheoremAnd.BrunTitchmarsh
import RMF.NumberTheory.CosinePrimeSum
import RMF.Analysis.PartialSumBounds
import RMF.NumberTheory.Rough
import RMF.Reduction.Periodisation
import RMF.Probability.PrimeValues

/-!
# The arithmetic and analytic inputs to the reduction

Gorodetsky–Wong quote three facts and prove only the first.  All three are proved here:

| here | source | used at |
|---|---|---|
| `exists_smoothCount_le` | Rankin; Cojocaru–Murty Thm 5.3.1 | the smooth block, and `y < m ≤ T` |
| `exists_roughCount_sub_le` | Brun; Cojocaru–Murty Thm 6.2.5 | `T < m ≤ x` |
| `integral_normSq_partialSum_eq` | Montgomery–Vaughan (5.26) | the final step |

**The constants are absolute.**  `A`, `c` and the implied constants do not depend on `x`, `y` or
`H`.  That is the whole content of the statements: a version of Rankin with `c` shrinking as `x`
grows would be true and useless.

The file also holds the conditioning on `𝓕_y` — the rough–smooth splitting (Gorodetsky–Wong (2.4))
and the conditional second moment (2.5) — and the two Euler-product integrals
`RMF.eulerLineIntegral` and `RMF.chaosUnit`.
-/

open MeasureTheory Filter Set
open scoped Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Counting functions -/

/-- `Ψ(x,y)`, the number of `y`-smooth integers in `[1,x]`.

Mathlib's `Nat.smoothNumbers N` is defined by the *strict* `p < N`, so `y`-smooth is
`Nat.smoothNumbers (y+1)`; `RMF.mem_smoothNumbers_succ_iff` is the translation. -/
noncomputable def smoothCount (y : ℕ) (x : ℝ) : ℕ :=
  {n ∈ Finset.Icc 1 ⌊x⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}.card

/-- `Φ(x,y)`, the number of `y`-rough integers in `[1,x]` — every prime factor exceeds `y`. -/
noncomputable def roughCount (y : ℕ) (x : ℝ) : ℕ :=
  {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n}.card

/-- `S_{t,y} = t^{-1/2} ∑_{n ≤ t, n y-smooth} f(n)`, the smooth partial sum.

The numerator depends on `t` only through `⌊t⌋`, which is what lets the sum over rough `m` be
regrouped by `r = ⌊x/m⌋` and then compared with an integral. -/
noncomputable def smoothSum (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (t : ℝ) (ω : Ω) : ℂ :=
  (∑ n ∈ {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, f ω n) / (Real.sqrt t : ℂ)

/-- The Dirichlet series `∑ aₙ n^{-s}`.  The `n = 0` term vanishes, since `(0:ℂ)^s = 0` for
`s ≠ 0` and division by zero is zero. -/
noncomputable def dirichletSeries (a : ℕ → ℂ) (s : ℂ) : ℂ := ∑' n : ℕ, a n / (n : ℂ) ^ s

/-! ### The monoid hom `n ↦ n^{-σ}`

Mathlib's smooth-number Euler product,
`EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric`, takes a *bundled*
`ℕ →* F` whose only hypothesis is `‖f p‖ < 1` at primes — crucially **not** `Summable f`, which
would force `σ > 1` and be useless here.  Building the bundle is the one piece of work.

The junk value at `0` is what makes it a hom: `(0:ℝ)^{-σ} = 0` for `σ ≠ 0`, so
`f 0 * f n = 0 = f (0 * n)`.  This is the one place the argument touches Lean-specific
junk-value behaviour, and it is why `σ ≠ 0` is a hypothesis. -/
/-- `n ↦ n^{-σ}` as a monoid hom on `ℕ`, for `σ ≠ 0`. -/
noncomputable def rpowNegHom {σ : ℝ} (hσ : σ ≠ 0) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' m n := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [Real.zero_rpow (neg_ne_zero.2 hσ)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow (neg_ne_zero.2 hσ)]
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast
    exact Real.mul_rpow hm0 hn0

lemma rpowNegHom_apply {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    rpowNegHom hσ n = (n : ℝ) ^ (-σ) := rfl

lemma norm_rpowNegHom_prime_lt_one {σ : ℝ} (hσ : σ ≠ 0) (hσ0 : 0 < σ) {p : ℕ} (hp : p.Prime) :
    ‖rpowNegHom hσ p‖ < 1 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  rw [rpowNegHom_apply, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp0.le _)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)

/-! ### The sieve bound, from `PrimeNumberTheoremAnd` -/

/-- **Brun's sieve bound for rough numbers in an interval**, in the explicit form supplied by
`PrimeNumberTheoremAnd.BrunTitchmarsh`: `Φ(x+H, y) - Φ(x, y) ≤ 2H/log y + 5y(1 + log y)³`.

Mellendijk's `BrunTitchmarsh.siftedSum_le` bounds the Selberg sifted sum of `[⌈x⌉, ⌊x+H⌋]`, and
`siftedSum_eq_card` identifies it with the count of integers there with no prime factor `≤ y`
(`RMF.IsRough y`); our difference runs over `[⌊x⌋+1, ⌊x+H⌋]`, and `⌈x⌉ ≤ ⌊x⌋ + 1`. -/
theorem roughCount_sub_le_brun {y : ℕ} (hy : 2 ≤ y) {x H : ℝ} (hx : 0 < x) (hH : 0 < H) :
    (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ)
      ≤ 2 * H / Real.log y + 5 * (y : ℝ) * (1 + Real.log y) ^ 3 := by
  classical
  have hy1 : (1 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hxH : x ≤ x + H := by linarith
  set A : Finset ℕ := {n ∈ Finset.Icc 1 ⌊x + H⌋₊ | IsRough y n} with hA
  set B : Finset ℕ := {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n} with hB
  have hBA : B ⊆ A := by
    intro n hn
    rw [hB, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [hA, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_le_floor hxH)⟩, hn.2⟩
  -- the difference of counts is the count over the gap
  have hdiff : (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ) = ((A \ B).card : ℝ) := by
    have hcard := Finset.card_sdiff_add_card_eq_card hBA
    rw [roughCount, roughCount, ← hA, ← hB]
    have : ((A \ B).card : ℝ) + (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hcard
    linarith
  -- the gap sits inside the sifted set
  have hsub : A \ B ⊆ {d ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊ |
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (y : ℝ) → ¬ p ∣ d} := by
    intro n hn
    rw [Finset.mem_sdiff, hA, hB, Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_Icc] at hn
    obtain ⟨⟨⟨hn1, hn2⟩, hrough⟩, hnotB⟩ := hn
    have hgt : ⌊x⌋₊ < n := by
      by_contra hle
      push Not at hle
      exact hnotB ⟨⟨hn1, hle⟩, hrough⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨le_trans (Nat.ceil_le_floor_add_one x) (by omega), hn2⟩, fun p hp hpy hpn => ?_⟩
    have := (isRough_iff.1 hrough) p hp hpn
    have : (y : ℝ) < (p : ℝ) := by exact_mod_cast this
    linarith
  calc (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ) = ((A \ B).card : ℝ) := hdiff
    _ ≤ (({d ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊ |
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (y : ℝ) → ¬ p ∣ d}).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = BoundingSieve.siftedSum (s := SelbergSieve.toBoundingSieve
          (self := BrunTitchmarsh.primeInterSieve x H (y : ℝ) hy1.le)) := by
        rw [BrunTitchmarsh.siftedSum_eq_card]
    _ ≤ 2 * H / Real.log y + 5 * (y : ℝ) * (1 + Real.log y) ^ 3 :=
        BrunTitchmarsh.siftedSum_le x H (y : ℝ) hx hH hy1

/-! ### Rankin's smooth-number bound -/

lemma summable_smoothNumbers_rpow (y : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Summable (Set.indicator (Nat.smoothNumbers (y + 1)) fun n : ℕ => (n : ℝ) ^ (-σ)) := by
  classical
  have h := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := rpowNegHom hσ.ne') (fun {p} hp => norm_rpowNegHom_prime_lt_one hσ.ne' hσ hp) (y + 1)).1
  have h' : Summable ((fun n : ℕ => ‖(rpowNegHom hσ.ne') n‖) ∘
      (Subtype.val : Nat.smoothNumbers (y + 1) → ℕ)) := h
  rw [summable_subtype_iff_indicator] at h'
  refine h'.congr fun n => ?_
  by_cases hn : n ∈ Nat.smoothNumbers (y + 1)
  · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn, rpowNegHom_apply, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn]

/-- **Rankin's inequality.**  `Ψ(x,y) ≤ x^σ ∑_{n y-smooth} n^{-σ}` for every `σ > 0` and `x ≥ 1`:
every counted `n` has `1 ≤ (x/n)^σ`, and the counted set is part of the full smooth sum.

The point is that `σ < 1` is allowed — the right-hand side is finite for *any* `σ > 0` because
the sum is over smooth numbers only, and that is what makes the bound strong. -/
lemma smoothCount_le_rpow_mul_tsum (y : ℕ) {x σ : ℝ} (hσ : 0 < σ) (hx : 1 ≤ x) :
    (smoothCount y x : ℝ)
      ≤ x ^ σ * ∑' n : ℕ, Set.indicator (Nat.smoothNumbers (y + 1))
          (fun n : ℕ => (n : ℝ) ^ (-σ)) n := by
  classical
  have hx0 : (0 : ℝ) < x := by linarith
  have hsum := summable_smoothNumbers_rpow y hσ
  set S : Finset ℕ := {n ∈ Finset.Icc 1 ⌊x⌋₊ | n ∈ Nat.smoothNumbers (y + 1)} with hS
  have hterm : ∀ n ∈ S, (1 : ℝ) ≤ x ^ σ * (n : ℝ) ^ (-σ) := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1.1
    have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hn.1.2) (Nat.floor_le hx0.le)
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hn0 _),
      one_mul]
    exact Real.rpow_le_rpow hn0.le hnx hσ.le
  calc (smoothCount y x : ℝ) = ∑ _n ∈ S, (1 : ℝ) := by
        rw [smoothCount, hS, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ n ∈ S, x ^ σ * (n : ℝ) ^ (-σ) := Finset.sum_le_sum hterm
    _ = x ^ σ * ∑ n ∈ S, (n : ℝ) ^ (-σ) := by rw [Finset.mul_sum]
    _ ≤ x ^ σ * ∑' n : ℕ, Set.indicator (Nat.smoothNumbers (y + 1))
          (fun n : ℕ => (n : ℝ) ^ (-σ)) n := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx0.le _)
        refine le_trans (le_of_eq ?_) (hsum.sum_le_tsum S fun n _ => ?_)
        · refine Finset.sum_congr rfl fun n hn => ?_
          rw [hS, Finset.mem_filter] at hn
          rw [Set.indicator_of_mem hn.2]
        · exact Set.indicator_nonneg (fun m _ => Real.rpow_nonneg (Nat.cast_nonneg m) _) n

/-- The smooth sum in closed form: the finite Euler product over `p ≤ y`. -/
lemma tsum_smoothNumbers_rpow_eq (y : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∑' n : ℕ, Set.indicator (Nat.smoothNumbers (y + 1))
        (fun n : ℕ => (n : ℝ) ^ (-σ)) n
      = ∏ p ∈ Nat.primesBelow (y + 1), (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  classical
  have h := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := rpowNegHom hσ.ne') (fun {p} hp => norm_rpowNegHom_prime_lt_one hσ.ne' hσ hp) (y + 1)).2
  rw [← tsum_subtype]
  exact h.tsum_eq

/-- `(1-t)⁻¹ ≤ e^{6t}` on `[0, 9/10]`, by the squaring trick `e^{6t} = (e^{3t})² ≥ (1+3t)²`:
`(1-t)(1+3t)² ≥ 1` holds up to `t ≈ 0.930`. -/
lemma inv_one_sub_le_exp {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 9 / 10) :
    (1 - t)⁻¹ ≤ Real.exp (6 * t) := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have h3 : 1 + 3 * t ≤ Real.exp (3 * t) := by linarith [Real.add_one_le_exp (3 * t)]
  have h6 : Real.exp (6 * t) = Real.exp (3 * t) * Real.exp (3 * t) := by
    rw [← Real.exp_add]
    ring_nf
  have hsq : (1 + 3 * t) ^ 2 ≤ Real.exp (6 * t) := by
    rw [h6]
    nlinarith [h3, Real.exp_pos (3 * t)]
  rw [inv_eq_one_div, div_le_iff₀ h1t]
  have hmul : (1 + 3 * t) ^ 2 * (1 - t) ≤ Real.exp (6 * t) * (1 - t) :=
    mul_le_mul_of_nonneg_right hsq h1t.le
  nlinarith [hmul, ht0, ht, mul_nonneg (sub_nonneg.2 ht) ht0, mul_nonneg ht0 ht0]

/-- The Euler product is at most `exp (6 ∑ p^{-σ})`, provided each `p^{-σ} ≤ 9/10`. -/
lemma prod_inv_one_sub_le_exp {N : ℕ} {σ : ℝ}
    (hb : ∀ p ∈ Nat.primesBelow N, (p : ℝ) ^ (-σ) ≤ 9 / 10) :
    ∏ p ∈ Nat.primesBelow N, (1 - (p : ℝ) ^ (-σ))⁻¹
      ≤ Real.exp (6 * ∑ p ∈ Nat.primesBelow N, (p : ℝ) ^ (-σ)) := by
  have hnn : ∀ p ∈ Nat.primesBelow N, (0 : ℝ) ≤ (p : ℝ) ^ (-σ) :=
    fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _
  calc ∏ p ∈ Nat.primesBelow N, (1 - (p : ℝ) ^ (-σ))⁻¹
      ≤ ∏ p ∈ Nat.primesBelow N, Real.exp (6 * (p : ℝ) ^ (-σ)) := by
        refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => inv_one_sub_le_exp
          (hnn p hp) (hb p hp))
        have h1 : (1 : ℝ) - (p : ℝ) ^ (-σ) > 0 := by linarith [hb p hp]
        positivity
    _ = Real.exp (6 * ∑ p ∈ Nat.primesBelow N, (p : ℝ) ^ (-σ)) := by
        rw [← Real.exp_sum, Finset.mul_sum]

/-- The prime-sum comparison.  At `σ = 1 - c/log y` and `p ≤ y`,

`p^{-σ} = p^{-1} p^{c/log y} = p^{-1} e^{(c/log y) log p} ≤ e^c p^{-1}`,

because `log p ≤ log y`.  This is what converts Rankin's sum over primes into Mertens'. -/
lemma rpow_neg_sigma_le {y p : ℕ} (hy : 2 ≤ y) (hp : 2 ≤ p) (hpy : p ≤ y) {c : ℝ} (hc : 0 < c) :
    (p : ℝ) ^ (-(1 - c / Real.log y)) ≤ Real.exp c * (p : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hLy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.trans' one_le_two)
  have hlog : Real.log p ≤ Real.log y := Real.log_le_log hp0 (by exact_mod_cast hpy)
  have hpow : (p : ℝ) ^ (c / Real.log y) ≤ Real.exp c := by
    rw [Real.rpow_def_of_pos hp0]
    refine Real.exp_le_exp.2 ?_
    calc Real.log p * (c / Real.log y) ≤ Real.log y * (c / Real.log y) := by
          exact mul_le_mul_of_nonneg_right hlog (by positivity)
      _ = c := by field_simp
  calc (p : ℝ) ^ (-(1 - c / Real.log y))
      = (p : ℝ)⁻¹ * (p : ℝ) ^ (c / Real.log y) := by
        rw [show -(1 - c / Real.log y) = -1 + c / Real.log y by ring, Real.rpow_add hp0,
          Real.rpow_neg_one]
    _ ≤ (p : ℝ)⁻¹ * Real.exp c := by
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = Real.exp c * (p : ℝ)⁻¹ := by ring

/-- Summed over `p ≤ y`. -/
lemma sum_rpow_neg_sigma_le {y : ℕ} (hy : 2 ≤ y) {c : ℝ} (hc : 0 < c) :
    ∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ) ^ (-(1 - c / Real.log y))
      ≤ Real.exp c * ∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ)⁻¹ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
  have hplt : p < y + 1 := Nat.lt_of_mem_primesBelow hp
  exact rpow_neg_sigma_le hy hpp.two_le (by omega) hc

/-- **Rankin's bound** (Cojocaru–Murty Thm 5.3.1): for `2 ≤ y` and `2 ≤ x`,
`Ψ(x,y) ≤ C x (log y)^A e^{-c log x / log y}` with absolute `A ≥ 0`, `c > 0`, `C > 0`.

Gorodetsky–Wong's proof: `Ψ(x,y) ≤ x^α ∏_{p ≤ y}(1-p^{-α})^{-1}` at `α = 1 - c/log y`, and
`∑_{p ≤ y} -log(1-p^{-α}) ≪ ∑_{p ≤ y} p^{-1} ≪ log log y` by Mertens
(`RMF.exists_abs_sum_primesBelow_inv_sub_log_log_le`).  De Bruijn's sharper form admits `A = 0`. -/
theorem exists_smoothCount_le :
    ∃ A c C : ℝ, 0 ≤ A ∧ 0 < c ∧ 0 < C ∧
      ∀ (y : ℕ) (x : ℝ), 2 ≤ y → 2 ≤ x →
        (smoothCount y x : ℝ)
          ≤ C * x * Real.log y ^ A * Real.exp (-c * Real.log x / Real.log y) := by
  obtain ⟨CM, hCM0, hM⟩ := exists_abs_sum_primesBelow_inv_sub_log_log_le
  refine ⟨6 * Real.exp (1 / 4), 1 / 4, Real.exp (6 * Real.exp (1 / 4) * CM),
    by positivity, by norm_num, Real.exp_pos _, ?_⟩
  intro y x hy hx
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hl2 : (69 / 100 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hLy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hyR
  have hLy0 : (0 : ℝ) < Real.log y := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  set σ : ℝ := 1 - (1 / 4) / Real.log y with hσdef
  have hquart : (1 / 4 : ℝ) / Real.log y ≤ (1 / 4) / Real.log 2 := by
    gcongr
  have hq2 : (1 / 4 : ℝ) / Real.log 2 < 1 / 2 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have hσ0 : (1 / 2 : ℝ) < σ := by
    rw [hσdef]
    linarith
  have hσpos : (0 : ℝ) < σ := by linarith
  -- every local factor is well inside the range where `(1-t)⁻¹ ≤ e^{6t}` applies
  have hb : ∀ p ∈ Nat.primesBelow (y + 1), (p : ℝ) ^ (-σ) ≤ 9 / 10 := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hstep : (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    have hexp : (2 : ℝ) ^ (-σ) = Real.exp (-(σ * Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1
      ring
    have hpos : (0 : ℝ) < 1 + σ * Real.log 2 := by nlinarith
    have hinv : Real.exp (-(σ * Real.log 2)) ≤ (1 + σ * Real.log 2)⁻¹ := by
      rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) hpos]
      linarith [Real.add_one_le_exp (σ * Real.log 2)]
    have hfin : (1 + σ * Real.log 2)⁻¹ ≤ 9 / 10 := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith
    rw [hexp] at hstep
    linarith
  -- Rankin, the Euler product, and the exponential bound
  have hmert : ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹ ≤ Real.log (Real.log y) + CM := by
    have := abs_le.1 (hM y hy)
    linarith [this.2]
  have hchain : (smoothCount y x : ℝ)
      ≤ x ^ σ * Real.exp (6 * (Real.exp (1 / 4) * (Real.log (Real.log y) + CM))) := by
    refine le_trans (smoothCount_le_rpow_mul_tsum y hσpos (by linarith)) ?_
    rw [tsum_smoothNumbers_rpow_eq y hσpos]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx0.le _)
    refine le_trans (prod_inv_one_sub_le_exp hb) (Real.exp_le_exp.2 ?_)
    have hsum := sum_rpow_neg_sigma_le (c := 1 / 4) hy (by norm_num)
    have hcast : ∀ p : ℕ, (p : ℝ) ^ (-(1 - (1 / 4) / Real.log y)) = (p : ℝ) ^ (-σ) := by
      intro p
      rw [hσdef]
    simp only [hcast] at hsum
    have hE : (0 : ℝ) < Real.exp (1 / 4) := Real.exp_pos _
    nlinarith [hsum, hmert, hE]
  -- unwind the constants
  have hxs : x ^ σ = x * Real.exp (-(1 / 4) * Real.log x / Real.log y) := by
    rw [Real.rpow_def_of_pos hx0, hσdef,
      show Real.log x * (1 - (1 / 4) / Real.log y)
        = Real.log x + -(1 / 4) * Real.log x / Real.log y by field_simp; ring,
      Real.exp_add, Real.exp_log hx0]
  have hloglog : Real.exp (6 * Real.exp (1 / 4) * Real.log (Real.log y))
      = Real.log y ^ (6 * Real.exp (1 / 4)) := by
    rw [Real.rpow_def_of_pos hLy0]
    congr 1
    ring
  refine le_trans hchain (le_of_eq ?_)
  rw [hxs, show (6 : ℝ) * (Real.exp (1 / 4) * (Real.log (Real.log y) + CM))
      = 6 * Real.exp (1 / 4) * Real.log (Real.log y) + 6 * Real.exp (1 / 4) * CM by ring,
    Real.exp_add, hloglog]
  ring

/-! ### The sieve bound for rough numbers in short intervals -/

/-- **Brun's sieve bound** (Cojocaru–Murty Thm 6.2.5), in the form the reduction consumes:
`Φ(x+H,y) - Φ(x,y) ≤ C H / log y` for `2 ≤ y ≤ H`, `x > 0` and `5y(1+log y)³ log y ≤ H`, with `C`
absolute.  The last hypothesis absorbs the error term of `RMF.roughCount_sub_le_brun`, turning
`2H/log y + 5y(1+log y)³` into `3H/log y`.  The bound is needed per interval, not on average: the
reduction weights `(x/(r+1), x/r]` by `|S_{r,y}|²`.  Both hypotheses are met at
`H = x/r - x/(r+1)` by `RMF.sieve_conditions`. -/
theorem exists_roughCount_sub_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (y : ℕ) (x H : ℝ), 2 ≤ y → 0 < x → 0 < H → (y : ℝ) ≤ H →
        5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ H →
        (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ) ≤ C * H / Real.log y := by
  refine ⟨3, by norm_num, fun y x H hy hx hH _ habs => ?_⟩
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hLy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  refine le_trans (roughCount_sub_le_brun hy hx hH) ?_
  have hkey : 5 * (y : ℝ) * (1 + Real.log y) ^ 3 ≤ H / Real.log y := by
    rw [le_div_iff₀ hLy]
    linarith [habs]
  rw [← sub_nonneg, show 3 * H / Real.log y
      - (2 * H / Real.log y + 5 * (y : ℝ) * (1 + Real.log y) ^ 3)
      = H / Real.log y - 5 * (y : ℝ) * (1 + Real.log y) ^ 3 by ring]
  linarith [hkey]

/-! ### Parseval for Dirichlet series -/

/-- **Parseval for Dirichlet series** (Montgomery–Vaughan (5.26)) at `σ = 1/2`: if
`∑ ‖aₙ‖/√n < ∞`, then with `A(u) = ∑_{n ≤ u} aₙ` and `D(s) = ∑ aₙ n^{-s}`,

`∫_0^∞ |A(u)|²/u² du = (1/2π) ∫_ℝ |D(1/2+it)/(1/2+it)|² dt`,

and the left integrand is integrable on `(0, ∞)`.

The summability hypothesis replaces the textbook one (abscissa of convergence below `1/2`) and makes
every interchange a Tonelli away; the reduction's coefficients meet it via
`RMF.summable_smoothIndicator_div_sqrt`.  The proof is Plancherel under `u = eᵛ`
(`RMF.fourier_logPartialSum`, `RMF.coeFn_fourier_toLp`); the `(2π)⁻¹` is the Jacobian of `t = 2πξ`.
Integrability is part of the conclusion because `∫` of a non-integrable function is `0` in Lean,
so the equality alone could hold vacuously. -/
theorem integral_normSq_partialSum_eq (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ / Real.sqrt n) :
    IntegrableOn (fun u : ℝ => ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ 2) (Ioi (0 : ℝ))
      ∧ ∫ u in Ioi (0 : ℝ), ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ 2
        = (2 * π)⁻¹ * ∫ t : ℝ,
            ‖dirichletSeries a (1 / 2 + t * Complex.I) / (1 / 2 + t * Complex.I)‖ ^ 2 := by
  refine ⟨integrableOn_normSq_partialSum_half a ha, ?_⟩
  simpa [dirichletSeries] using integral_normSq_partialSum_eq_line_half a ha

/-! ### The conditioning

`𝓕_y` and the two statements the reduction consumes from it.  The rough–smooth factorisation and
conditional orthogonality are the ingredients; what the assembly actually uses is the splitting of
`S_x` and the resulting second-moment identity, so those are what is stated. -/

/-- `𝓕_y`, the σ-algebra generated by the values at primes `p ≤ y`.

Indexed by **primes**, not by all naturals `≤ y`: `IsIIDPrimeValues` asserts measurability of
`X p` only at primes, so an index set containing composites would not even be below `mΩ`.  It is
also the form `ProbabilityTheory.indep_iSup_of_disjoint` consumes when conditional orthogonality
splits the family over `{p ≤ y}` and `{p > y}`. -/
@[reducible]
noncomputable def smoothAlgebra (X : ℕ → Ω → ℂ) (y : ℕ) : MeasurableSpace Ω :=
  ⨆ p ∈ {p : ℕ | p.Prime ∧ p ≤ y}, MeasurableSpace.comap (X p) inferInstance

lemma smoothAlgebra_le {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) (y : ℕ) :
    smoothAlgebra X y ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun p hp => (hX.measurable p hp.1).comap_le

omit [MeasurableSpace Ω] in
/-- **The rough–smooth reindexing**, for multiplicative `f ω` and `x ≥ 0`:
`∑_{n ≤ x} f(n) = ∑_{m ≤ x rough} ∑_{k ≤ x/m smooth} f(m) f(k)`.

Every `n` factors uniquely as `n = m·k` with `m` `y`-rough and `k` `y`-smooth, and the two factors
are coprime, so multiplicativity suffices.  The bijection is `(m,k) ↦ mk` with inverse
`n ↦ (roughPart n, smoothPart n)`; see `RMF.rough_smooth_unique`. -/
theorem sum_Icc_eq_sum_rough_smooth {f : Ω → ArithmeticFunction ℂ} (y : ℕ)
    {x : ℝ} (hx : 0 ≤ x) {ω : Ω} (hmul : (f ω).IsMultiplicative) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f ω n
      = ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
          ∑ k ∈ {k ∈ Finset.Icc 1 ⌊x / m⌋₊ | k ∈ Nat.smoothNumbers (y + 1)}, f ω m * f ω k := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun n => (⟨roughPart y n, smoothPart y n⟩ : Σ _ : ℕ, ℕ))
    (fun p => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · -- the two parts land in the right fibres
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hnx : (n : ℝ) ≤ x := le_trans (Nat.cast_le.2 hn.2) (Nat.floor_le hx)
    have hrpos : 0 < roughPart y n := roughPart_pos y n
    have hrposR : (0 : ℝ) < (roughPart y n : ℝ) := by exact_mod_cast hrpos
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨hrpos, le_trans (Nat.le_of_dvd (by omega) (roughPart_dvd y hn0)) hn.2⟩,
      isRough_roughPart y n⟩, ⟨smoothPart_pos y n, ?_⟩, smoothPart_mem_smoothNumbers y n⟩
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hrposR, ← Nat.cast_mul, mul_comm]
    exact le_trans (Nat.cast_le.2 (le_of_eq (roughPart_mul_smoothPart y hn0))) hnx
  · -- the product lands back in `[1, x]`
    rintro ⟨m, k⟩ hp
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hm1, _⟩, _⟩, ⟨hk1, hk2⟩, _⟩ := hp
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hkx : (k : ℝ) ≤ x / m :=
      le_trans (Nat.cast_le.2 hk2) (Nat.floor_le (by positivity))
    rw [Finset.mem_Icc]
    refine ⟨Nat.one_le_iff_ne_zero.2 (by positivity), Nat.le_floor ?_⟩
    rw [Nat.cast_mul]
    calc (m : ℝ) * k ≤ (m : ℝ) * (x / m) := by nlinarith [hkx, hmR]
      _ = x := by field_simp
  · -- `roughPart n · smoothPart n = n`
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact roughPart_mul_smoothPart y (by omega)
  · -- and conversely, by uniqueness
    rintro ⟨m, k⟩ hp
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hm1, _⟩, hmr⟩, _, hks⟩ := hp
    obtain ⟨h1, h2⟩ := roughPart_smoothPart_mul hmr hks hm1
    exact Sigma.ext h1 (heq_of_eq h2)
  · -- multiplicativity on the coprime pair
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [← hmul.map_mul_of_coprime
      ((isRough_roughPart y n).coprime_of_mem_smoothNumbers (smoothPart_mem_smoothNumbers y n)),
      roughPart_mul_smoothPart y (by omega)]

/-! ### Conditional orthogonality

The engine of (2.5).  `𝓕_y` is generated by the primes `≤ y`; the values at the primes above `y`
generate a σ-algebra independent of it, and a rough `n` has all its prime factors there, so
`f(n)` is measurable for that second σ-algebra.  Conditioning on `𝓕_y` therefore replaces
`f(m) conj(f(m'))` by its unconditional expectation, which `RMF.IsSteinhausRMF.orthogonality`
already computes. -/

/-- `𝓖_y`, the σ-algebra generated by the values at the primes `p > y`. -/
@[reducible]
noncomputable def roughAlgebra (X : ℕ → Ω → ℂ) (y : ℕ) : MeasurableSpace Ω :=
  ⨆ p ∈ {p : Nat.Primes | y < (p : ℕ)}, MeasurableSpace.comap (X (p : ℕ)) inferInstance

lemma roughAlgebra_le {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) (y : ℕ) : roughAlgebra X y ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun p _ => (hX.measurable p p.2).comap_le

omit [MeasurableSpace Ω] in
/-- `𝓕_y` reindexed over `Nat.Primes`, which is the form `indep_iSup_of_disjoint` consumes. -/
lemma smoothAlgebra_eq_iSup_primes (X : ℕ → Ω → ℂ) (y : ℕ) :
    smoothAlgebra X y
      = ⨆ p ∈ {p : Nat.Primes | (p : ℕ) ≤ y}, MeasurableSpace.comap (X (p : ℕ)) inferInstance := by
  refine le_antisymm (iSup₂_le fun p hp => ?_) (iSup₂_le fun p hp => ?_)
  · exact le_iSup₂_of_le (⟨p, hp.1⟩ : Nat.Primes) hp.2 le_rfl
  · exact le_iSup₂_of_le (p : ℕ) ⟨p.2, hp⟩ le_rfl

/-- **The two halves of the prime family are independent.**  This is the only place the full
strength of `iIndepFun` over the primes is used. -/
theorem indep_smoothAlgebra_roughAlgebra {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) (y : ℕ) :
    ProbabilityTheory.Indep (smoothAlgebra X y) (roughAlgebra X y) μ := by
  rw [smoothAlgebra_eq_iSup_primes]
  exact ProbabilityTheory.indep_iSup_of_disjoint
    (fun p : Nat.Primes => (hX.measurable (p : ℕ) p.2).comap_le)
    hX.iIndep (Set.disjoint_left.2 fun p hp hq =>
      absurd (Set.mem_setOf.1 hq) (not_lt.2 (Set.mem_setOf.1 hp)))

omit [MeasurableSpace Ω] in
/-- **A rough `n` is measurable for the primes above `y`.**  Every prime factor of `n` exceeds
`y`, so each factor `X p ^ v_p(n)` of `compMultExtension` already is. -/
lemma measurable_roughAlgebra_compMultExtension {X : ℕ → Ω → ℂ} {y n : ℕ} (hn : IsRough y n)
    (hn0 : n ≠ 0) :
    Measurable[roughAlgebra X y] fun ω => compMultExtension (fun p => X p ω) n := by
  simp only [compMultExtension_apply_of_ne_zero _ hn0, Finsupp.prod, Nat.support_factorization]
  refine Finset.measurable_prod _ fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hle : MeasurableSpace.comap (X p) inferInstance ≤ roughAlgebra X y :=
    le_iSup₂_of_le (⟨p, hpp⟩ : Nat.Primes)
      (isRough_iff.1 hn p hpp (Nat.dvd_of_mem_primeFactors hp)) le_rfl
  exact (Measurable.mono (Measurable.of_comap_le le_rfl) hle le_rfl).pow_const _

omit [MeasurableSpace Ω] in
/-- **A rough `n` is measurable for `𝓖_y`, squarefree extension.**  The twin of
`RMF.measurable_roughAlgebra_compMultExtension`.

Simpler than its model: off the squarefrees the value is the constant `0`, and on them it is a
product of *first* powers, so no `pow_const` step is needed. -/
lemma measurable_roughAlgebra_squarefreeExtension {X : ℕ → Ω → ℂ} {y n : ℕ} (hn : IsRough y n) :
    Measurable[roughAlgebra X y] fun ω => squarefreeExtension (fun p => X p ω) n := by
  by_cases hsf : Squarefree n
  · simp only [squarefreeExtension_apply_of_squarefree _ hsf]
    refine Finset.measurable_prod _ fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hle : MeasurableSpace.comap (X p) inferInstance ≤ roughAlgebra X y :=
      le_iSup₂_of_le (⟨p, hpp⟩ : Nat.Primes)
        (isRough_iff.1 hn p hpp (Nat.dvd_of_mem_primeFactors hp)) le_rfl
    exact Measurable.mono (Measurable.of_comap_le le_rfl) hle le_rfl
  · simp only [squarefreeExtension_apply_of_not_squarefree _ hsf]
    exact measurable_const

omit [MeasurableSpace Ω] in
/-- The squarefree analogue of `RMF.measurable_rough_mul_conj`. -/
lemma measurable_rough_mul_conj_sqfree {X : ℕ → Ω → ℂ} {y m m' : ℕ} (hm : IsRough y m)
    (hm' : IsRough y m') :
    Measurable[roughAlgebra X y] fun ω => squarefreeExtension (fun p => X p ω) m
      * (starRingEnd ℂ) (squarefreeExtension (fun p => X p ω) m') :=
  (measurable_roughAlgebra_squarefreeExtension hm).mul
    (Complex.continuous_conj.measurable.comp
      (measurable_roughAlgebra_squarefreeExtension hm'))

omit [MeasurableSpace Ω] in
/-- `f(m) conj(f(m'))` is measurable for the primes above `y` when both are rough. -/
lemma measurable_rough_mul_conj {X : ℕ → Ω → ℂ} {y m m' : ℕ} (hm : IsRough y m)
    (hm' : IsRough y m') (hm0 : m ≠ 0) (hm'0 : m' ≠ 0) :
    Measurable[roughAlgebra X y] fun ω => compMultExtension (fun p => X p ω) m
      * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) m') :=
  (measurable_roughAlgebra_compMultExtension hm hm0).mul
    (Complex.continuous_conj.measurable.comp
      (measurable_roughAlgebra_compMultExtension hm' hm'0))

omit [MeasurableSpace Ω] in
/-- **A smooth `n` is measurable for `𝓕_y`.**  The mirror of
`measurable_roughAlgebra_compMultExtension`. -/
lemma measurable_smoothAlgebra_compMultExtension {X : ℕ → Ω → ℂ} {y n : ℕ}
    (hn : n ∈ Nat.smoothNumbers (y + 1)) :
    Measurable[smoothAlgebra X y] fun ω => compMultExtension (fun p => X p ω) n := by
  have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hn
  simp only [compMultExtension_apply_of_ne_zero _ hn0, Finsupp.prod, Nat.support_factorization]
  refine Finset.measurable_prod _ fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hle : MeasurableSpace.comap (X p) inferInstance ≤ smoothAlgebra X y :=
    le_iSup₂_of_le p
      ⟨hpp, mem_smoothNumbers_succ_iff.1 hn p hpp (Nat.dvd_of_mem_primeFactors hp)⟩ le_rfl
  exact (Measurable.mono (Measurable.of_comap_le le_rfl) hle le_rfl).pow_const _

omit [MeasurableSpace Ω] in
/-- **`S_{t,y}` is `𝓕_y`-measurable**, which is what lets it pull out of the conditional
expectation in (2.5). -/
lemma measurable_smoothAlgebra_smoothSum {f : Ω → ArithmeticFunction ℂ} {X : ℕ → Ω → ℂ}
    (hf : f = fun ω => compMultExtension fun p => X p ω) (y : ℕ) (t : ℝ) :
    Measurable[smoothAlgebra X y] (smoothSum f y t) := by
  subst hf
  refine Measurable.div_const (Finset.measurable_sum _ fun n hn => ?_) _
  exact measurable_smoothAlgebra_compMultExtension (Finset.mem_filter.1 hn).2

omit [MeasurableSpace Ω] in
/-- **A smooth `n` is measurable for `𝓕_y`, squarefree extension.**  The twin of
`RMF.measurable_smoothAlgebra_compMultExtension`. -/
lemma measurable_smoothAlgebra_squarefreeExtension {X : ℕ → Ω → ℂ} {y n : ℕ}
    (hn : n ∈ Nat.smoothNumbers (y + 1)) :
    Measurable[smoothAlgebra X y] fun ω => squarefreeExtension (fun p => X p ω) n := by
  by_cases hsf : Squarefree n
  · simp only [squarefreeExtension_apply_of_squarefree _ hsf]
    refine Finset.measurable_prod _ fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hle : MeasurableSpace.comap (X p) inferInstance ≤ smoothAlgebra X y :=
      le_iSup₂_of_le p
        ⟨hpp, mem_smoothNumbers_succ_iff.1 hn p hpp (Nat.dvd_of_mem_primeFactors hp)⟩ le_rfl
    exact Measurable.mono (Measurable.of_comap_le le_rfl) hle le_rfl
  · simp only [squarefreeExtension_apply_of_not_squarefree _ hsf]
    exact measurable_const

omit [MeasurableSpace Ω] in
/-- The squarefree analogue of `RMF.measurable_smoothAlgebra_smoothSum`. -/
lemma measurable_smoothAlgebra_smoothSum_sqfree {X : ℕ → Ω → ℂ} (y : ℕ) (t : ℝ) :
    Measurable[smoothAlgebra X y]
      (smoothSum (fun ω => squarefreeExtension fun p => X p ω) y t) := by
  refine Measurable.div_const (Finset.measurable_sum _ fun n hn => ?_) _
  exact measurable_smoothAlgebra_squarefreeExtension (Finset.mem_filter.1 hn).2

/-- **Conditional orthogonality, real part**: for rough nonzero `m`, `m'`,
`E[(f(m) conj(f(m'))).re ∣ 𝓕_y] = δ_{m,m'}` almost surely.  Conditional expectation does not
commute with `Complex.re` for free, so the independence argument is applied to the real part
directly, which is again `𝓖_y`-measurable. -/
lemma condExp_rough_mul_conj_re {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsSteinhausPrimeValues X μ) {y m m' : ℕ} (hm : IsRough y m) (hm' : IsRough y m')
    (hm0 : m ≠ 0) (hm'0 : m' ≠ 0) :
    μ[fun ω => (compMultExtension (fun p => X p ω) m
        * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) m')).re | smoothAlgebra X y]
      =ᵐ[μ] fun _ => if m = m' then (1 : ℝ) else 0 := by
  have hSt : IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ := hX.isSteinhausRMF
  have hint := hSt.integrable_mul_conj hm0 hm'0
  refine (MeasureTheory.condExp_indep_eq (roughAlgebra_le hX y) (smoothAlgebra_le hX y)
    (Complex.continuous_re.measurable.comp
      (measurable_rough_mul_conj hm hm' hm0 hm'0)).stronglyMeasurable
    (indep_smoothAlgebra_roughAlgebra hX y).symm).trans
    (Filter.EventuallyEq.of_eq (funext fun _ => ?_))
  have hre : ∫ ω, (compMultExtension (fun p => X p ω) m
      * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) m')).re ∂μ
      = (∫ ω, compMultExtension (fun p => X p ω) m
          * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) m') ∂μ).re := by
    simpa using Complex.reCLM.integral_comp_comm hint
  simp only [Function.comp_apply]
  rw [hre, hSt.orthogonality hm0 hm'0]
  split_ifs <;> simp

/-- The imaginary part vanishes identically: `∫ f(m) conj(f(m'))` is real (it is `δ_{m,m'}`). -/
lemma condExp_rough_mul_conj_im {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsSteinhausPrimeValues X μ) {y m m' : ℕ} (hm : IsRough y m) (hm' : IsRough y m')
    (hm0 : m ≠ 0) (hm'0 : m' ≠ 0) :
    μ[fun ω => (compMultExtension (fun p => X p ω) m
        * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) m')).im | smoothAlgebra X y]
      =ᵐ[μ] fun _ => (0 : ℝ) := by
  have hSt : IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ := hX.isSteinhausRMF
  have hint := hSt.integrable_mul_conj hm0 hm'0
  refine (MeasureTheory.condExp_indep_eq (roughAlgebra_le hX y) (smoothAlgebra_le hX y)
    (Complex.continuous_im.measurable.comp
      (measurable_rough_mul_conj hm hm' hm0 hm'0)).stronglyMeasurable
    (indep_smoothAlgebra_roughAlgebra hX y).symm).trans
    (Filter.EventuallyEq.of_eq (funext fun _ => ?_))
  have him : ∫ ω, (compMultExtension (fun p => X p ω) m
      * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) m')).im ∂μ
      = (∫ ω, compMultExtension (fun p => X p ω) m
          * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) m') ∂μ).im := by
    simpa using Complex.imCLM.integral_comp_comm hint
  simp only [Function.comp_apply]
  rw [him, hSt.orthogonality hm0 hm'0]
  split_ifs <;> simp

/-- `‖∑ a_i‖²` as a real double sum.  Expanding in `ℂ` and taking real parts once, here, is what
keeps the whole of (2.5) inside `ℝ` — conditional expectation does not commute with
`Complex.ofReal` at this Mathlib pin, so a `ℂ`-valued expansion would have no way back. -/
lemma norm_sq_sum_eq_sum_re {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    ‖∑ i ∈ s, a i‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, (a i * (starRingEnd ℂ) (a j)).re := by
  have hz : ‖∑ i ∈ s, a i‖ ^ 2
      = ((∑ i ∈ s, a i) * (starRingEnd ℂ) (∑ i ∈ s, a i)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hz, map_sum, Finset.sum_mul_sum]
  simp [Complex.re_sum]

/-- `S_{t,y}` is bounded, with an explicit bound: it is an average of at most `⌊t⌋` values of
modulus one.  Only boundedness is used — the constant is irrelevant, since it is discharged
against `IsFiniteMeasure` in `condExp_stronglyMeasurable_mul_of_bound`. -/
lemma ae_norm_smoothSum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) (y : ℕ) (t : ℝ) :
    ∀ᵐ ω ∂μ, ‖smoothSum f y t ω‖ ≤ (⌊t⌋₊ : ℝ) / Real.sqrt t := by
  have hall : ∀ᵐ ω ∂μ, ∀ n ∈ (Finset.Icc 1 ⌊t⌋₊ : Finset ℕ), ‖f ω n‖ = 1 := by
    have hset := (MeasureTheory.ae_ball_iff
      (Finset.Icc 1 ⌊t⌋₊ : Finset ℕ).countable_toSet).2
      (fun n (hn : n ∈ ((Finset.Icc 1 ⌊t⌋₊ : Finset ℕ) : Set ℕ)) =>
        hf.norm_apply (n := n) (by simp only [Finset.mem_coe, Finset.mem_Icc] at hn; omega))
    filter_upwards [hset] with ω hω n hn
    exact hω n (by simpa using hn)
  filter_upwards [hall] with ω hω
  have hnum : ‖∑ n ∈ {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, f ω n‖
      ≤ (⌊t⌋₊ : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ n ∈ {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, ‖f ω n‖
        ≤ ∑ _n ∈ {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, (1 : ℝ) :=
          Finset.sum_le_sum fun n hn =>
            le_of_eq (hω n (by simpa using (Finset.mem_filter.1 hn).1))
      _ ≤ (⌊t⌋₊ : ℝ) := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact_mod_cast le_trans (Finset.card_filter_le _ _) (by simp)
  rw [smoothSum, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg t)]
  exact div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg t)

/-- **The pull-out step of (2.5), for one pair `(m, m')`.**  `V` stands for
`S_{x/m} conj(S_{x/m'})`, which is `𝓕_y`-measurable and bounded; the rough factor is
independent of `𝓕_y`, so it contributes its unconditional expectation `δ_{m,m'}`.

`V` is left abstract: nothing beyond `𝓕_y`-measurability and boundedness is used, and stating it
this way keeps the `re`/`im` bookkeeping in one place. -/
lemma condExp_mul_rough_re {f : Ω → ArithmeticFunction ℂ} {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsSteinhausPrimeValues X μ)
    (hf : f = fun ω => compMultExtension fun p => X p ω) {y m m' : ℕ}
    (hm : IsRough y m) (hm' : IsRough y m') (hm0 : m ≠ 0) (hm'0 : m' ≠ 0) {V : Ω → ℂ} {c : ℝ}
    (hV : Measurable[smoothAlgebra X y] V) (hVb : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ c) :
    μ[fun ω => (V ω * (f ω m * (starRingEnd ℂ) (f ω m'))).re | smoothAlgebra X y]
      =ᵐ[μ] fun ω => (if m = m' then (1 : ℝ) else 0) * (V ω).re := by
  subst hf
  have hSt : IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ := hX.isSteinhausRMF
  have hZint := hSt.integrable_mul_conj hm0 hm'0
  have hZre : Integrable (fun ω => (compMultExtension (fun p => X p ω) m
      * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) m')).re) μ := by
    simpa using hZint.re
  have hZim : Integrable (fun ω => (compMultExtension (fun p => X p ω) m
      * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) m')).im) μ := by
    simpa using hZint.im
  have hVre : StronglyMeasurable[smoothAlgebra X y] fun ω => (V ω).re :=
    (Complex.continuous_re.measurable.comp hV).stronglyMeasurable
  have hVim : StronglyMeasurable[smoothAlgebra X y] fun ω => (V ω).im :=
    (Complex.continuous_im.measurable.comp hV).stronglyMeasurable
  have hVreb : ∀ᵐ ω ∂μ, ‖(V ω).re‖ ≤ c := by
    filter_upwards [hVb] with ω hω
    exact le_trans (Complex.abs_re_le_norm _) hω
  have hVimb : ∀ᵐ ω ∂μ, ‖(V ω).im‖ ≤ c := by
    filter_upwards [hVb] with ω hω
    exact le_trans (Complex.abs_im_le_norm _) hω
  have hle := smoothAlgebra_le hX y
  have hi1 : Integrable ((fun ω => (V ω).re)
      * fun ω => (compMultExtension (fun p => X p ω) m
        * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) m')).re) μ :=
    hZre.bdd_mul ((hVre.mono hle).aestronglyMeasurable) hVreb
  have hi2 : Integrable ((fun ω => (V ω).im)
      * fun ω => (compMultExtension (fun p => X p ω) m
        * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) m')).im) μ :=
    hZim.bdd_mul ((hVim.mono hle).aestronglyMeasurable) hVimb
  have key : (fun ω => (V ω * (compMultExtension (fun p => X p ω) m
        * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) m'))).re)
      = ((fun ω => (V ω).re) * fun ω => (compMultExtension (fun p => X p ω) m
          * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) m')).re)
        - ((fun ω => (V ω).im) * fun ω => (compMultExtension (fun p => X p ω) m
          * (starRingEnd ℂ) (compMultExtension (fun p => X p ω) m')).im) := by
    funext ω
    simp [Complex.mul_re]
  rw [key]
  filter_upwards [condExp_sub hi1 hi2 (smoothAlgebra X y),
    condExp_stronglyMeasurable_mul_of_bound hle hVre hZre c hVreb,
    condExp_stronglyMeasurable_mul_of_bound hle hVim hZim c hVimb,
    condExp_rough_mul_conj_re hX hm hm' hm0 hm'0,
    condExp_rough_mul_conj_im hX hm hm' hm0 hm'0] with ω e0 e1 e2 e3 e4
  rw [e0]
  simp only [Pi.sub_apply, Pi.mul_apply] at e1 e2 ⊢
  rw [e1, e2, e3, e4]
  ring

omit [MeasurableSpace Ω] in
/-- **The rough-smooth splitting** (Gorodetsky–Wong (2.4)):

`S_x = ∑_{m ≤ x, m y-rough} (f(m)/√m) · S_{x/m, y}`.

The arithmetic is `RMF.sum_Icc_eq_sum_rough_smooth`; all that is added here is the normalisation,
which works out exactly because `√m · √(x/m) = √x`.  Gorodetsky–Wong's `y ≥ 2` is not needed. -/
theorem normalisedSum_eq_sum_rough_smooth {f : Ω → ArithmeticFunction ℂ} (y : ℕ)
    {x : ℝ} (hx : 1 ≤ x) {ω : Ω} (hmul : (f ω).IsMultiplicative) :
    normalisedSum f x ω
      = ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
          f ω m / (Real.sqrt m : ℂ) * smoothSum f y (x / m) ω := by
  rw [normalisedSum, randomSum, sum_Icc_eq_sum_rough_smooth y (by linarith) hmul, Finset.sum_div]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_filter, Finset.mem_Icc] at hm
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.1.1
  have hsm : Real.sqrt m * Real.sqrt (x / m) = Real.sqrt x := by
    rw [← Real.sqrt_mul hmR.le]
    congr 1
    field_simp
  rw [smoothSum, ← Finset.mul_sum, div_mul_div_comm, ← Complex.ofReal_mul, hsm]

/-- `‖S_x‖²` as a real double sum over rough pairs, in exactly the shape
`RMF.condExp_mul_rough_re` consumes: a real scalar times `(V · Z).re`, with `V` built from smooth
sums and `Z` from rough values. -/
lemma normSq_normalisedSum_eq_double_sum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hSt : IsSteinhausRMF f μ) (y : ℕ) {x : ℝ} (hx : 1 ≤ x) (ω : Ω) :
    ‖normalisedSum f x ω‖ ^ 2
      = ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
          ∑ m' ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
            ((((Real.sqrt m * Real.sqrt m')⁻¹ : ℝ) : ℂ)
                * (smoothSum f y (x / m) ω * (starRingEnd ℂ) (smoothSum f y (x / m') ω))
              * (f ω m * (starRingEnd ℂ) (f ω m'))).re := by
  rw [normalisedSum_eq_sum_rough_smooth y hx (hSt.isMultiplicative ω), norm_sq_sum_eq_sum_re]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  congr 1
  rw [map_mul, map_div₀, Complex.conj_ofReal]
  push_cast
  ring

/-- The integrability that `RMF.condExp_mul_rough_re` needs of its own integrand, and that the
assembly needs to move `condExp` through the double sum. -/
lemma integrable_mul_rough_re {f : Ω → ArithmeticFunction ℂ} {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hX : IsSteinhausPrimeValues X μ)
    (hf : f = fun ω => compMultExtension fun p => X p ω) {m m' : ℕ}
    (hm0 : m ≠ 0) (hm'0 : m' ≠ 0)
    {V : Ω → ℂ} {c : ℝ} (hV : AEStronglyMeasurable V μ) (hVb : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ c) :
    Integrable (fun ω => (V ω * (f ω m * (starRingEnd ℂ) (f ω m'))).re) μ := by
  subst hf
  have hSt : IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ := hX.isSteinhausRMF
  simpa using ((hSt.integrable_mul_conj hm0 hm'0).bdd_mul hV hVb).re

/-- **The conditional second moment** (Gorodetsky–Wong (2.5)), an identity:
`E[|S_x|² ∣ 𝓕_y] = ∑_{m ≤ x, m y-rough} m⁻¹ |S_{x/m, y}|²`.

Each `S_{x/m,y}` is `𝓕_y`-measurable and pulls out, and the cross terms vanish by conditional
orthogonality (`RMF.condExp_mul_rough_re`).  Gorodetsky–Wong display the `m = 1` term separately;
here it is part of the sum, since a rough `m > 1` already exceeds `y`. -/
theorem condExp_normSq_normalisedSum {f : Ω → ArithmeticFunction ℂ} {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hX : IsSteinhausPrimeValues X μ)
    (hf : f = fun ω => compMultExtension fun p => X p ω) {y : ℕ}
    {x : ℝ} (hx : 1 ≤ x) :
    μ[fun ω => ‖normalisedSum f x ω‖ ^ 2 | smoothAlgebra X y]
      =ᵐ[μ] fun ω => ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
          (m : ℝ)⁻¹ * ‖smoothSum f y (x / m) ω‖ ^ 2 := by
  have hSt : IsSteinhausRMF f μ := isSteinhausRMF_iff_exists.2 ⟨X, hX, hf⟩
  have hle := smoothAlgebra_le hX y
  set A : Finset ℕ := {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m} with hAdef
  have hAmem : ∀ m ∈ A, m ≠ 0 ∧ IsRough y m := by
    intro m hm
    rw [hAdef, Finset.mem_filter, Finset.mem_Icc] at hm
    exact ⟨by omega, hm.2⟩
  -- `V m m'` is the smooth half of the `(m, m')` term, scalar included; `T m m'` the whole term
  set V : ℕ → ℕ → Ω → ℂ := fun m m' ω =>
    (((Real.sqrt m * Real.sqrt m')⁻¹ : ℝ) : ℂ)
      * (smoothSum f y (x / m) ω * (starRingEnd ℂ) (smoothSum f y (x / m') ω)) with hVdef
  set T : ℕ → ℕ → Ω → ℝ := fun m m' ω =>
    (V m m' ω * (f ω m * (starRingEnd ℂ) (f ω m'))).re with hTdef
  have hVmeas : ∀ m m' : ℕ, Measurable[smoothAlgebra X y] (V m m') := by
    intro m m'
    simp only [hVdef]
    exact Measurable.const_mul ((measurable_smoothAlgebra_smoothSum hf y (x / m)).mul
      (Complex.continuous_conj.measurable.comp
        (measurable_smoothAlgebra_smoothSum hf y (x / m')))) _
  have hVb : ∀ m m' : ℕ, ∀ᵐ ω ∂μ, ‖V m m' ω‖
      ≤ (Real.sqrt m * Real.sqrt m')⁻¹ * (((⌊x / m⌋₊ : ℝ) / Real.sqrt (x / m))
          * ((⌊x / m'⌋₊ : ℝ) / Real.sqrt (x / m'))) := by
    intro m m'
    filter_upwards [ae_norm_smoothSum_le hSt y (x / m), ae_norm_smoothSum_le hSt y (x / m')]
      with ω h1 h2
    simp only [hVdef]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul,
      Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
      (by positivity)
  have hGint : ∀ m ∈ A, ∀ m' ∈ A, Integrable (T m m') μ := fun m hm m' hm' =>
    integrable_mul_rough_re hX hf (hAmem m hm).1 (hAmem m' hm').1
      ((hVmeas m m').mono hle le_rfl).aestronglyMeasurable (hVb m m')
  -- each row, after conditioning, collapses to its diagonal term
  have hrow : ∀ m ∈ A, μ[fun ω => ∑ m' ∈ A, T m m' ω | smoothAlgebra X y]
      =ᵐ[μ] fun ω => (m : ℝ)⁻¹ * ‖smoothSum f y (x / m) ω‖ ^ 2 := by
    intro m hm
    rw [show (fun ω => ∑ m' ∈ A, T m m' ω) = ∑ m' ∈ A, T m m' from
      funext fun ω => by simp [Finset.sum_apply]]
    refine (condExp_finsetSum (fun m' hm' => hGint m hm m' hm') (smoothAlgebra X y)).trans ?_
    have hpairs : ∀ᵐ ω ∂μ, ∀ m' ∈ (A : Set ℕ),
        (μ[T m m' | smoothAlgebra X y]) ω
          = (if m = m' then (1 : ℝ) else 0) * (V m m' ω).re := by
      rw [MeasureTheory.ae_ball_iff A.countable_toSet]
      intro m' hm'
      have hm'A : m' ∈ A := by simpa using hm'
      exact condExp_mul_rough_re hX hf (hAmem m hm).2 (hAmem m' hm'A).2 (hAmem m hm).1
        (hAmem m' hm'A).1 (hVmeas m m') (hVb m m')
    filter_upwards [hpairs] with ω hω
    simp only [Finset.sum_apply]
    rw [Finset.sum_congr rfl fun m' hm' => hω m' (by simpa using hm'), Finset.sum_eq_single m]
    · simp only [hVdef]
      rw [Real.mul_self_sqrt (Nat.cast_nonneg m), Complex.mul_conj, ← Complex.ofReal_mul,
        Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      simp
    · intro m' _ hne
      rw [if_neg fun h => hne h.symm, zero_mul]
    · intro hnm
      exact absurd hm hnm
  -- assemble: the outer sum
  rw [show (fun ω => ‖normalisedSum f x ω‖ ^ 2) = ∑ m ∈ A, fun ω => ∑ m' ∈ A, T m m' ω from
    funext fun ω => by
      simp only [Finset.sum_apply, hTdef, hVdef]
      exact normSq_normalisedSum_eq_double_sum hSt y hx ω]
  refine (condExp_finsetSum (fun m hm =>
    integrable_finsetSum _ fun m' hm' => hGint m hm m' hm') (smoothAlgebra X y)).trans ?_
  have hrows : ∀ᵐ ω ∂μ, ∀ m ∈ (A : Set ℕ),
      (μ[fun ω => ∑ m' ∈ A, T m m' ω | smoothAlgebra X y]) ω
        = (m : ℝ)⁻¹ * ‖smoothSum f y (x / m) ω‖ ^ 2 := by
    rw [MeasureTheory.ae_ball_iff A.countable_toSet]
    intro m hm
    exact hrow m (by simpa using hm)
  filter_upwards [hrows] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun m hm => hω m (by simpa using hm)

/-- `∑_{n y-smooth} n^{-1/2} < ∞`: Parseval's hypothesis, for the coefficients the reduction feeds
it.  The sum is the finite Euler product `∏_{p ≤ y}(1-p^{-1/2})⁻¹`, by
`EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric` applied to the monoid
hom `n ↦ n^{-1/2}`, whose hypothesis is only `‖f p‖ < 1` at primes. -/
theorem summable_smoothIndicator_div_sqrt (y : ℕ) :
    Summable fun n : ℕ =>
      (if n ∈ Nat.smoothNumbers (y + 1) then (1 : ℝ) else 0) / Real.sqrt n := by
  classical
  have hσ : (1 / 2 : ℝ) ≠ 0 := by norm_num
  have hsum := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := rpowNegHom hσ) (fun {p} hp => norm_rpowNegHom_prime_lt_one hσ (by norm_num) hp)
    (y + 1)).1
  have hsum' : Summable ((fun n : ℕ => ‖(rpowNegHom hσ) n‖) ∘
      (Subtype.val : Nat.smoothNumbers (y + 1) → ℕ)) := hsum
  rw [summable_subtype_iff_indicator] at hsum'
  refine hsum'.congr fun n => ?_
  by_cases hn : n ∈ Nat.smoothNumbers (y + 1)
  · have hn0 : n ≠ 0 := hn.1
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := Nat.pos_of_ne_zero hn0
      exact_mod_cast this
    rw [Set.indicator_of_mem hn, if_pos hn, rpowNegHom_apply, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hnR.le _), Real.sqrt_eq_rpow,
      Real.rpow_neg hnR.le, inv_eq_one_div]
  · rw [Set.indicator_of_notMem hn, if_neg hn, zero_div]

/-! ### The two Euler-product integrals -/

/-- `(1/log y) ∫_ℝ |A_y(1/2+it)/(1/2+it)|² dt`, the object Gorodetsky–Wong reduce to.

The weight `|1/2+it|⁻²` is what makes this converge without any further truncation, and
hence what keeps the reduction free of `q`. -/
noncomputable def eulerLineIntegral (f : Ω → ArithmeticFunction ℂ) (y : ℝ) (ω : Ω) : ℝ :=
  (Real.log y)⁻¹ * ∫ t : ℝ,
    ‖randomEulerProduct f (⌊y⌋₊ + 1) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω /
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2

/-- `(1/log y) ∫_0^1 |A_y(1/2+ih)|² dh`, the object Harper's later argument works with. -/
noncomputable def chaosUnit (f : Ω → ArithmeticFunction ℂ) (y : ℝ) (ω : Ω) : ℝ :=
  (Real.log y)⁻¹ * ∫ h in (0 : ℝ)..1,
    ‖randomEulerProduct f (⌊y⌋₊ + 1) (((1 / 2 : ℝ) : ℂ) + (h : ℂ) * Complex.I) ω‖ ^ 2

omit [MeasurableSpace Ω] in
/-- Both integrands are nonnegative and `log y > 0`, so the normalised integrals are too.
Needed to chain the two bounds: `Real.rpow` is not automatically nonnegative. -/
lemma chaosUnit_nonneg {f : Ω → ArithmeticFunction ℂ} {y : ℝ} (hy : 2 ≤ y) (ω : Ω) :
    0 ≤ chaosUnit f y ω := by
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  refine mul_nonneg (inv_nonneg.2 hlog.le) ?_
  exact intervalIntegral.integral_nonneg (by norm_num) fun h _ => by positivity

omit [MeasurableSpace Ω] in
/-- The line integral is nonnegative: the integrand is a square and `log y > 0`. -/
lemma eulerLineIntegral_nonneg {f : Ω → ArithmeticFunction ℂ} {y : ℝ} (hy : 2 ≤ y) (ω : Ω) :
    0 ≤ eulerLineIntegral f y ω := by
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  exact mul_nonneg (inv_nonneg.2 hlog.le)
    (MeasureTheory.integral_nonneg fun t => by positivity)

/-- **The target's integrand is integrable**, for `y ≥ 2` and `q ≥ 0`.  Otherwise
`∫ (eulerLineIntegral)^q`, on the right of the reduction, would be `0` by Lean's convention and the
reduction would assert something false rather than something weak.  The quantitative moment bound
is `RMF.euler_unitIntegral_moment_le`, for `RMF.chaosUnit`. -/
theorem integrable_eulerLineIntegral_rpow {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) {y q : ℝ} (hy : 2 ≤ y) (hq : 0 ≤ q) :
    Integrable (fun ω => eulerLineIntegral f y ω ^ q) μ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI := hX.isProbabilityMeasure
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hae := ae_forall_norm_le_one hX norm_le_one_steinhausLaw (⌊y⌋₊ + 1)
  set C : ℝ := (Real.log y)⁻¹ * (8 * eulerBound (⌊y⌋₊ + 1) ^ 2 * ∑' n : ℤ, shiftWeight 1 n)
    with hCdef
  have hmeas : AEStronglyMeasurable
      (fun ω => eulerLineIntegral (fun ω => compMultExtension fun p => X p ω) y ω ^ q) μ := by
    have h1 := (measurable_lineFunctional (1 / 2) (⌊y⌋₊ + 1)).comp
      (measurable_pi_lambda _ fun p : Nat.Primes => hX.measurable (p : ℕ) p.2)
    have hmap : Measurable fun ω =>
        ((Real.log y)⁻¹ * lineFunctional (1 / 2) (⌊y⌋₊ + 1)
          (fun p : Nat.Primes => X (p : ℕ) ω)) ^ q := by fun_prop
    refine hmap.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with ω hω
    rw [lineFunctional_eq (1 / 2) (by norm_num) hω]
    rfl
  have hbd : ∀ᵐ ω ∂μ,
      ‖eulerLineIntegral (fun ω => compMultExtension fun p => X p ω) y ω ^ q‖ ≤ C ^ q := by
    filter_upwards [hae] with ω hω
    have hnn : 0 ≤ eulerLineIntegral (fun ω => compMultExtension fun p => X p ω) y ω :=
      eulerLineIntegral_nonneg hy ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnn q)]
    refine Real.rpow_le_rpow hnn ?_ hq
    rw [eulerLineIntegral, hCdef]
    exact mul_le_mul_of_nonneg_left (integral_lineDivSq_le (1 / 2) (by norm_num) hω)
      (inv_nonneg.2 hlog.le)
  exact (memLp_top_of_bound hmeas _ hbd).integrable le_top

/-- **The unit-integral analogue of `RMF.integrable_eulerLineIntegral_rpow`.**  Needed to compare
the moment at the integer cutoff `⌊y⌋` with the one at `y`. -/
theorem integrable_chaosUnit_rpow {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) {y q : ℝ} (hy : 2 ≤ y) (hq : 0 ≤ q) :
    Integrable (fun ω => chaosUnit f y ω ^ q) μ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI := hX.isProbabilityMeasure
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hae := ae_forall_norm_le_one hX norm_le_one_steinhausLaw (⌊y⌋₊ + 1)
  set C : ℝ := (Real.log y)⁻¹ * eulerBound (⌊y⌋₊ + 1) ^ 2 with hCdef
  have hmeas : AEStronglyMeasurable
      (fun ω => chaosUnit (fun ω => compMultExtension fun p => X p ω) y ω ^ q) μ := by
    have h1 := (measurable_unitFunctional (1 / 2) (⌊y⌋₊ + 1)).comp
      (measurable_pi_lambda _ fun p : Nat.Primes => hX.measurable (p : ℕ) p.2)
    have hmap : Measurable fun ω =>
        ((Real.log y)⁻¹ * unitFunctional (1 / 2) (⌊y⌋₊ + 1)
          (fun p : Nat.Primes => X (p : ℕ) ω)) ^ q := by fun_prop
    refine hmap.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with ω hω
    rw [unitFunctional_eq (1 / 2) (by norm_num) hω, chaosUnit,
      intervalIntegral.integral_of_le zero_le_one]
    rfl
  have hbd : ∀ᵐ ω ∂μ,
      ‖chaosUnit (fun ω => compMultExtension fun p => X p ω) y ω ^ q‖ ≤ C ^ q := by
    filter_upwards [hae] with ω hω
    have hnn : 0 ≤ chaosUnit (fun ω => compMultExtension fun p => X p ω) y ω :=
      chaosUnit_nonneg hy ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnn q)]
    refine Real.rpow_le_rpow hnn ?_ hq
    rw [chaosUnit, intervalIntegral.integral_of_le zero_le_one, hCdef]
    exact mul_le_mul_of_nonneg_left (integral_unit_le (1 / 2) (by norm_num) hω)
      (inv_nonneg.2 hlog.le)
  exact (memLp_top_of_bound hmeas _ hbd).integrable le_top

/-- `n ↦ f(n)·n^{-s}` as a bundled hom, for `f = compMultExtension x`.

The Euler product needs a bundled `ℕ →* ℂ`; the two ingredients are complete multiplicativity
of `compMultExtension` (`compMultExtension_apply_mul`, on nonzero arguments) and multiplicativity
of `n ↦ n^{-s}` on the nonnegative reals.  At `0` both sides vanish because an
`ArithmeticFunction` does. -/
noncomputable def compMultCpowHom (x : ℕ → ℂ) (s : ℂ) : ℕ →* ℂ where
  toFun n := compMultExtension x n * (n : ℂ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hcast : ((m * n : ℕ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
      have h := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg (α := ℝ) m)
        (Nat.cast_nonneg (α := ℝ) n) (-s)
      push_cast at h ⊢
      exact h
    rw [compMultExtension_apply_mul x hm.ne' hn.ne', hcast]
    ring

lemma compMultCpowHom_apply (x : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    compMultCpowHom x s n = compMultExtension x n * (n : ℂ) ^ (-s) := rfl

/-! ### The smooth coefficients and their Dirichlet series -/

/-- `aₙ = f(n)·1_{n y-smooth}`, the coefficients the reduction feeds to Parseval. -/
noncomputable def smoothCoeff (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (ω : Ω) (n : ℕ) : ℂ :=
  if n ∈ Nat.smoothNumbers (y + 1) then f ω n else 0

/-- **The Dirichlet series over `y`-smooth numbers is the Euler product over `p ≤ y`**:
`∑_{n y-smooth} f(n) n^{-s} = ∏_{p ≤ y} (1 - f(p)p^{-s})⁻¹` for all `Re s > 0`, almost surely.

`s` is quantified inside the `∀ᵐ`: the reduction integrates the identity over `t ∈ ℝ`, and null
sets depending on `s` would not assemble into one.  The good `ω` are those with `‖f ω p‖ = 1` at
every prime. -/
theorem dirichletSeries_smoothCoeff_eq {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) (y : ℕ) :
    ∀ᵐ ω ∂μ, ∀ s : ℂ, 0 < s.re →
      dirichletSeries (smoothCoeff f y ω) s = randomEulerProduct f (y + 1) s ω := by
  classical
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have hmeasP : Measurable fun z : ℂ => ‖z‖ ≤ 1 :=
    measurableSet_setOf.1 (measurableSet_le measurable_norm measurable_const)
  have hall : ∀ᵐ ω ∂μ, ∀ p : ℕ, p.Prime → ‖X p ω‖ ≤ 1 := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro hp
    exact ((hX.hasLaw p hp).ae_iff hmeasP).2 norm_le_one_steinhausLaw
  filter_upwards [hall] with ω hω
  intro s hs
  -- the local hypothesis of the Euler product, at every prime
  have hlt : ∀ {p : ℕ}, p.Prime → ‖compMultCpowHom (fun p => X p ω) s p‖ < 1 := by
    intro p hp
    rw [compMultCpowHom_apply, norm_mul,
      compMultExtension_apply_prime _ hp, Complex.norm_natCast_cpow_of_pos hp.pos,
      Complex.neg_re]
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have hlt1 : (p : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have hpos : (0 : ℝ) < (p : ℝ) ^ (-s.re) :=
      Real.rpow_pos_of_pos (by linarith) _
    nlinarith [hω p hp, norm_nonneg (X p ω)]
  have hprod := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := compMultCpowHom (fun p => X p ω) s) hlt (y + 1)).2
  -- the Dirichlet series is the sum over smooth numbers
  have hds : dirichletSeries (smoothCoeff (fun ω => compMultExtension fun p => X p ω) y ω) s
      = ∑' m : Nat.smoothNumbers (y + 1), compMultCpowHom (fun p => X p ω) s m := by
    rw [tsum_subtype, dirichletSeries]
    refine tsum_congr fun n => ?_
    by_cases hn : n ∈ Nat.smoothNumbers (y + 1)
    · rw [Set.indicator_of_mem hn, smoothCoeff, if_pos hn, compMultCpowHom_apply,
        Complex.cpow_neg, div_eq_mul_inv]
    · rw [Set.indicator_of_notMem hn, smoothCoeff, if_neg hn, zero_div]
  rw [hds, hprod.tsum_eq, randomEulerProduct_compMult_eq hs
    (fun p hp => hω p (Nat.prime_of_mem_primesBelow hp))]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [compMultCpowHom_apply, compMultExtension_apply_prime _ (Nat.prime_of_mem_primesBelow hp)]

end RMF
