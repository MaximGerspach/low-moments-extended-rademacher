/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.BlockShift
import RMF.EulerProduct.LogField
import RMF.EulerProduct.LogExpansion
import RMF.EulerProduct.Moments
import RMF.EulerProduct.RademacherLogField
import RMF.EulerProduct.RademacherPrimeSum
import RMF.NumberTheory.CosinePrimeSum
import RMF.SecondMoment

/-!
# From the first moment to the `q`-th: the analytic inputs

The upper bound's `q`-th moment comes from an interpolation of Soundararajan and Zaman over a
geometric family of barriers, as in Hamdan's proof of his Proposition 1.2
(Hamdan, arXiv:2604.05563).  With `n_j := j/(1-q)`, his decomposition (2.18) is

`Z² ≤ Z²(n_{j₀}) + ∑_{j₀ ≤ j ≤ K} 1(h ∉ G_{n_j}) Z²(n_{j+1}) + 1(h ∉ G_{n_{K+1}}) Z²`;

take `q`-th moments, use subadditivity of `x ↦ x^q` and `E[X^q] ≤ (E X)^q`, split each indicator
off by Hölder, and feed in Hamdan's Lemma 2.3 (`P(h ∉ G_A) ≪ e^{-2A}`) and Proposition 2.1
(`E[Z²(A)] ≪ A/√t`).

**The point of `n_j = j/(1-q)` is that the exponent becomes `q`-free**: Lemma 2.3 gives
`P(h ∉ G_{n_j})^{1-q} ≪ e^{-2n_j(1-q)} = e^{-2j}`.  Proposition 2.1 then contributes
`((j+1)/((1-q)√t))^q`, and `∑_j e^{-2j} ((j+1)/((1-q)√t))^q = ((1-q)√t)^{-q} · ∑_j e^{-2j}(j+1)^q`
collapses because the second factor is bounded uniformly in `q`.

This file proves that uniform bound, the subadditivity and Hölder steps, and some arithmetic of
Lemma 2.3; Lemma 2.3 itself is proved in `RMF/Probability/MaximalBarrier.lean`, and the
interpolation is `RMF.integral_rpow_le_of_goodSets` (`RMF/Probability/ChaosMoment.lean`).

## The range of `q`

The interpolation does not run for all `q ∈ [0,1]`, although its conclusion holds for all of them.
Lemma 2.3 and Proposition 2.1 need `4C₀ < A ≤ 3√t`, and `A = n_K` with `K = j₀ + ⌈√t(1-q)⌉`
gives `n_K < 4C₀ + √t + 2/(1-q)`, so `n_K ≤ 3√t` forces `4C₀ + 2/(1-q) ≤ 2√t`.  A sufficient form
is `(1-q)√t ≥ 2` together with `t ≥ (4C₀)²`.

On the complement `(1-q)√t < 2` the conclusion is free: the target `(1+(1-q)√t)^{-q}` exceeds
`3^{-q} ≥ 1/3` (`RMF.one_third_le_target`), and `E[Z^{2q}] ≤ (E Z²)^q ≍ 1` by Jensen
(`RMF.integral_rpow_le_rpow_integral`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

/-! ### The geometric weight

`∑_j e^{-2j} (j+1)^q ≤ 2`, uniformly in `q ∈ [0,1]`.  Two crude steps suffice and avoid computing
`∑ j r^j`: `(j+1)^q ≤ j+1` because `q ≤ 1` and the base is at least `1`, and `(j+1) ≤ 2^j`, which
turns the series into the single geometric sum `∑ (2e^{-2})^j` with ratio `2e^{-2} < 2/7`. -/

/-- `e^{-2} < 1/7`, from `e > 2.7`. -/
lemma exp_neg_two_lt : Real.exp (-2) < 1 / 7 := by
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have hgt : (7 : ℝ) < Real.exp 2 := by rw [h2]; nlinarith
  have hrx : Real.exp (-2) * Real.exp 2 = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-2)]

/-- The ratio of the dominating geometric series, `2e^{-2} < 2/7`. -/
lemma two_mul_exp_neg_two_lt_one : 2 * Real.exp (-2) < 1 := by
  linarith [exp_neg_two_lt]

/-- Every term of the geometric weight is nonnegative. -/
lemma exp_mul_rpow_nonneg (q : ℝ) (j : ℕ) :
    0 ≤ Real.exp (-2 * (j : ℝ)) * ((j : ℝ) + 1) ^ q := by
  have : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ q := Real.rpow_nonneg (by positivity) q
  positivity

/-- **Each term is below the geometric one.**  Two crude steps: `(j+1)^q ≤ j+1` because `q ≤ 1`
and the base is at least `1`, and `j + 1 ≤ 2^j`. -/
lemma exp_mul_rpow_le_geometric {q : ℝ} (hq1 : q ≤ 1) (j : ℕ) :
    Real.exp (-2 * j) * ((j : ℝ) + 1) ^ q ≤ (2 * Real.exp (-2)) ^ j := by
  have hexp : Real.exp (-2 * (j : ℝ)) = Real.exp (-2) ^ j := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hbase : (1 : ℝ) ≤ (j : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hrpow : ((j : ℝ) + 1) ^ q ≤ (j : ℝ) + 1 := by
    calc ((j : ℝ) + 1) ^ q ≤ ((j : ℝ) + 1) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase hq1
      _ = (j : ℝ) + 1 := Real.rpow_one _
  have hnat : ((j : ℝ) + 1) ≤ 2 ^ j := by
    have h := Nat.lt_two_pow_self (n := j)
    have h' : (j : ℝ) + 1 ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast h
    simpa using h'
  calc Real.exp (-2 * (j : ℝ)) * ((j : ℝ) + 1) ^ q
      = Real.exp (-2) ^ j * ((j : ℝ) + 1) ^ q := by rw [hexp]
    _ ≤ Real.exp (-2) ^ j * ((j : ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ ≤ Real.exp (-2) ^ j * 2 ^ j := by exact mul_le_mul_of_nonneg_left hnat (by positivity)
    _ = (2 * Real.exp (-2)) ^ j := by rw [mul_pow]; ring

/-- The geometric weight is summable, uniformly in `q ≤ 1`. -/
lemma summable_exp_mul_rpow {q : ℝ} (hq1 : q ≤ 1) :
    Summable fun j : ℕ => Real.exp (-2 * (j : ℝ)) * ((j : ℝ) + 1) ^ q :=
  (summable_geometric_of_lt_one (by positivity) two_mul_exp_neg_two_lt_one).of_nonneg_of_le
    (exp_mul_rpow_nonneg q) (exp_mul_rpow_le_geometric hq1)

/-- **The geometric weight of the interpolation, bounded uniformly in `q`.**

This is why the sum over the barrier family collapses to a single `((1-q)√t)^{-q}`: the `q`
appears only inside `(j+1)^q`, which is dominated by `j+1` for every `q ≤ 1`. -/
theorem tsum_exp_mul_rpow_le {q : ℝ} (hq1 : q ≤ 1) :
    ∑' j : ℕ, Real.exp (-2 * j) * ((j : ℝ) + 1) ^ q ≤ 2 := by
  have h2r0 : (0 : ℝ) ≤ 2 * Real.exp (-2) := by positivity
  have h2r1 : 2 * Real.exp (-2) < 1 := two_mul_exp_neg_two_lt_one
  calc ∑' j : ℕ, Real.exp (-2 * (j : ℝ)) * ((j : ℝ) + 1) ^ q
      ≤ ∑' j : ℕ, (2 * Real.exp (-2)) ^ j :=
        (summable_exp_mul_rpow hq1).tsum_le_tsum (exp_mul_rpow_le_geometric hq1)
          (summable_geometric_of_lt_one h2r0 h2r1)
    _ = (1 - 2 * Real.exp (-2))⁻¹ := tsum_geometric_of_lt_one h2r0 h2r1
    _ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith [exp_neg_two_lt]

/-- The same bound over any finite index set, which is the form the interpolation uses: the
barrier family is indexed by `Finset.Ico j₀ K`, not by all of `ℕ`. -/
lemma sum_exp_mul_rpow_le {q : ℝ} (hq1 : q ≤ 1) (s : Finset ℕ) :
    ∑ j ∈ s, Real.exp (-2 * (j : ℝ)) * ((j : ℝ) + 1) ^ q ≤ 2 :=
  le_trans (Summable.sum_le_tsum s (fun i _ => exp_mul_rpow_nonneg q i)
    (summable_exp_mul_rpow hq1)) (tsum_exp_mul_rpow_le hq1)

/-! ### Two more pieces of arithmetic

Both are used in the interpolation, and both say the same kind of thing: a quantity that looks
`q`-dependent is bounded uniformly in `q ∈ [0,1]`.  The third of the kind is
`RMF.rpow_le_max_one` (`RMF/SecondMoment.lean`). -/

/-- **The tail term is negligible.**  `e^{-2L} ≤ L^{-q}` for `L ≥ 2` and `q ≤ 1`, because
`e^{2L} ≥ 2L + 1 > L` and `L^{-1} ≤ L^{-q}`. -/
lemma exp_neg_two_mul_le_rpow_neg {L q : ℝ} (hL : 2 ≤ L) (hq1 : q ≤ 1) :
    Real.exp (-(2 * L)) ≤ L ^ (-q) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have h1 : Real.exp (-(2 * L)) ≤ L⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hL0 (by linarith [Real.add_one_le_exp (2 * L)])
  have h2 : L ^ (-(1 : ℝ)) ≤ L ^ (-q) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  rw [Real.rpow_neg_one] at h2
  linarith

/-- **Moving the target.**  If `v ≤ k u` with `k ≥ 1`, then `u^{-q} ≤ k v^{-q}` for `q ∈ [0,1]`.

Raising to a negative power reverses the inequality, and the cost is `k^q ≤ k`, uniformly in `q`.
The target is moved twice: the interpolation produces `((1-q)√t)^{-q}` where the bound asks for
`(1 + (1-q)√t)^{-q}`, and Hamdan's Proposition 1.2 asks for `\log\log y` where the block count `t`
sits an additive constant below it. -/
lemma rpow_neg_le_mul_rpow_neg {u v k q : ℝ} (hu : 0 < u) (hv : 0 < v) (hk : 1 ≤ k)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h : v ≤ k * u) :
    u ^ (-q) ≤ k * v ^ (-q) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have h1 : (k * u) ^ (-q) ≤ v ^ (-q) := Real.rpow_le_rpow_of_nonpos hv h (by linarith)
  rw [Real.mul_rpow hk0.le hu.le] at h1
  have hpos : (0 : ℝ) < k ^ q := Real.rpow_pos_of_pos hk0 q
  have hmul := mul_le_mul_of_nonneg_left h1 hpos.le
  rw [← mul_assoc, ← Real.rpow_add hk0, add_neg_cancel, Real.rpow_zero, one_mul] at hmul
  have hkq : k ^ q ≤ k := by
    have hle := Real.rpow_le_rpow_of_exponent_le hk hq1
    rwa [Real.rpow_one] at hle
  exact le_trans hmul (mul_le_mul_of_nonneg_right hkq (Real.rpow_nonneg hv.le _))

/-- **Trading the block count for `Λ`, at any ratio.**  If `Λ ≤ k²t` with `k ≥ 1`, then
`(1 + (1-q)√t)^{-q} ≤ k(1 + (1-q)√Λ)^{-q}`: `√Λ ≤ k√t` gives `1 + (1-q)√Λ ≤ k(1 + (1-q)√t)`, and
`RMF.rpow_neg_le_mul_rpow_neg` reverses it.

The Rademacher branch uses `k = 4`: its `q`-th moment is read at `harperBlockCount D x / 4`, and
there `Λ ≤ 4t` fails, because the count is `⌊Λ⌋ - D`. -/
lemma rpow_neg_target_le_of_sq_le {t Λ k q : ℝ} (hk : 1 ≤ k) (hΛt : Λ ≤ k ^ 2 * t)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 + (1 - q) * Real.sqrt t) ^ (-q) ≤ k * (1 + (1 - q) * Real.sqrt Λ) ^ (-q) := by
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hs0' : (0 : ℝ) ≤ Real.sqrt Λ := Real.sqrt_nonneg _
  have hsq : Real.sqrt Λ ≤ k * Real.sqrt t := by
    have e1 : Real.sqrt (k ^ 2 * t) = k * Real.sqrt t := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hk0]
    rw [show k * Real.sqrt t = Real.sqrt (k ^ 2 * t) from e1.symm]
    exact Real.sqrt_le_sqrt hΛt
  have hu0 : (0 : ℝ) < 1 + (1 - q) * Real.sqrt t := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - q by linarith) hs0]
  have hv0 : (0 : ℝ) < 1 + (1 - q) * Real.sqrt Λ := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - q by linarith) hs0']
  exact rpow_neg_le_mul_rpow_neg hu0 hv0 hk hq0 hq1
    (by nlinarith [mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 1 - q by linarith)])

/-- **Trading the block count for `Λ`.**  If `Λ ≤ 4t`, the target built on `t` is within a factor
`2` of the target built on `Λ`: the case `k = 2` of `RMF.rpow_neg_target_le_of_sq_le`. -/
lemma rpow_neg_target_le_of_quarter_le {t Λ q : ℝ} (hΛt : Λ ≤ 4 * t)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 + (1 - q) * Real.sqrt t) ^ (-q) ≤ 2 * (1 + (1 - q) * Real.sqrt Λ) ^ (-q) :=
  rpow_neg_target_le_of_sq_le (k := 2) (by norm_num) (by linarith) hq0 hq1

/-- **The target, without the `1`.**  `L^{-q} ≤ \tfrac32 (1+L)^{-q}` for `L ≥ 2`. -/
lemma rpow_neg_le_target {L q : ℝ} (hL : 2 ≤ L) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    L ^ (-q) ≤ 3 / 2 * (1 + L) ^ (-q) := by
  refine rpow_neg_le_mul_rpow_neg (by linarith) (by linarith) (by norm_num) hq0 hq1 ?_
  linarith

/-! ### The range of `q`, and the trivial complement -/

/-- On the complement the target is `≥ 1/3`: `(1 + (1-q)√t)^{-q} ≥ 3^{-q} ≥ 1/3` once
`(1-q)√t < 2` and `q ≤ 1`.  So there any bound by an absolute constant gives the `q`-th moment
bound, and `E[Z^{2q}] ≤ (E Z²)^q` supplies one. -/
lemma one_third_le_target {q t : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hsmall : (1 - q) * Real.sqrt t < 2) :
    (1 : ℝ) / 3 ≤ (1 + (1 - q) * Real.sqrt t) ^ (-q) := by
  have hs : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hlow : (0 : ℝ) < 1 + (1 - q) * Real.sqrt t := by nlinarith
  have hle : 1 + (1 - q) * Real.sqrt t ≤ 3 := by linarith
  have h3 : (3 : ℝ) ^ (-q) ≤ (1 + (1 - q) * Real.sqrt t) ^ (-q) :=
    Real.rpow_le_rpow_of_nonpos hlow hle (by linarith)
  have h1 : (1 : ℝ) / 3 ≤ (3 : ℝ) ^ (-q) := by
    have hmono : (3 : ℝ) ^ (-(1 : ℝ)) ≤ (3 : ℝ) ^ (-q) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_neg_one] at hmono
    norm_num at hmono
    linarith
  linarith

/-! ### Hamdan's Lemma 2.3: the union bound

`P(h ∉ G_A) ≪ e^{-2A}` is a union bound over `j ≤ t` of the two one-sided failures.  For the
upper failures, `P(S_j > A + j + 2log(...)) ≤ exp(-(A+j)²/j)`, the Gaussian exponent at
`Var S_j = j/2`, and `(A+j)²/j = A²/j + 2A + j` peels off `e^{-2A}` and leaves a geometric `e^{-j}`.
For the lower failures, `j ≥ A/4` gives `20j - A ≥ 16j`; for `j < A/4` the failure probability
would be near `1`, which is why `G_A` starts at `A/4`. -/

/-- `(A+j)²/j ≥ 2A + j` for `j > 0` — the identity that peels `e^{-2A}` off the Gaussian tail and
leaves a summable `e^{-j}`.  It is an equality up to `A²/j ≥ 0`. -/
lemma two_mul_add_le_sq_div {A j : ℝ} (hj : 0 < j) : 2 * A + j ≤ (A + j) ^ 2 / j := by
  rw [le_div_iff₀ hj]
  nlinarith [sq_nonneg A]

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- `log log (blockScale θ k) = k + θ`, exactly. -/
lemma log_log_blockScale (θ : ℝ) (k : ℕ) :
    Real.log (Real.log (blockScale θ k)) = (k : ℝ) + θ := by
  rw [blockScale, Real.log_exp, Real.log_exp]

/-! ### The three inequalities behind the `q`-th moment

Taking the `q`-th moment of the decomposition (2.18) needs three facts: subadditivity of
`x ↦ x^q` over the sum, Hölder to pull each indicator out as `P(bad)^{1-q}`, and Jensen
`E[X^q] ≤ (E X)^q` for the two unrestricted terms.  The first two are here; Jensen is
`RMF.integral_rpow_le_rpow_integral`, with integrability side condition
`RMF.integrable_rpow_of_integrable`, both in `RMF/SecondMoment.lean`.

**The exponent `1-q` on `P(bad)` is the point of the geometric family.**  Hamdan's Lemma 2.3 gives
`P(bad_j) ≪ e^{-2n_j}`, and `n_j = j/(1-q)` makes `P(bad_j)^{1-q} ≪ e^{-2j}`, free of `q`; that is
what `RMF.tsum_exp_mul_rpow_le` sums. -/

/-- **`x ↦ x^q` is subadditive over a finite sum**, for `q ∈ (0,1]`.

`q > 0` is not a convenience: at `q = 0` the empty sum gives `0^0 = 1 > 0` and the statement is
false. -/
lemma rpow_sum_le_sum_rpow {ι : Type*} (s : Finset ι) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑ i ∈ s, x i) ^ q ≤ ∑ i ∈ s, x i ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hq0.ne']
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hs0 : (0 : ℝ) ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i _ => hx i
      have h := Real.rpow_add_le_add_rpow (hx a) hs0 hq0.le hq1
      linarith

/-- **Hölder**, in the shape the `q`-th moment consumes: `∫_B X^q ≤ μ(B)^{1-q}(∫ X)^q`.

`X ≥ 0` and integrable, on a probability space, and `q ∈ (0,1)`.  The two `MemLp` facts are the
only work: the indicator is bounded, so it lies in every `L^p`; and `X^q ∈ L^{1/q}` because
`(X^q)^{1/q} = X`. -/
lemma integral_indicator_mul_rpow_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX0 : 0 ≤ᵐ[μ] X) (hX : Integrable X μ)
    {B : Set Ω} (hB : MeasurableSet B) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (∫ ω, Set.indicator B (fun _ => (1 : ℝ)) ω * X ω ^ q ∂μ)
      ≤ μ.real B ^ (1 - q) * (∫ ω, X ω ∂μ) ^ q := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hpq : Real.HolderConjugate (1 / (1 - q)) (1 / q) :=
    Real.holderConjugate_one_div h1q hq0 (by ring)
  have hf0 : 0 ≤ᵐ[μ] Set.indicator B (fun _ => (1 : ℝ)) :=
    Filter.Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hg0 : 0 ≤ᵐ[μ] fun ω => X ω ^ q := by
    filter_upwards [hX0] with ω hω
    exact Real.rpow_nonneg hω q
  -- the indicator is bounded, hence in every `L^p`
  have hfmeas : AEStronglyMeasurable (Set.indicator B (fun _ => (1 : ℝ))) μ :=
    (measurable_const.indicator hB).aestronglyMeasurable
  have hfL : MemLp (Set.indicator B (fun _ => (1 : ℝ))) (ENNReal.ofReal (1 / (1 - q))) μ := by
    refine MemLp.mono_exponent (memLp_top_of_bound hfmeas 1 ?_) le_top
    refine Filter.Eventually.of_forall fun ω => ?_
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω]
      simp
    · rw [Set.indicator_of_notMem hω]
      simp
  -- `(X^q)^{1/q} = X`, so `X^q ∈ L^{1/q}`
  have hgL : MemLp (fun ω => X ω ^ q) (ENNReal.ofReal (1 / q)) μ := by
    have h := (memLp_one_iff_integrable.2 hX).norm_rpow_div (ENNReal.ofReal q)
    have hexp : (1 : ℝ≥0∞) / ENNReal.ofReal q = ENNReal.ofReal (1 / q) := by
      simp [one_div, ENNReal.ofReal_inv_of_pos hq0]
    rw [ENNReal.toReal_ofReal hq0.le, hexp] at h
    refine (memLp_congr_ae ?_).1 h
    filter_upwards [hX0] with ω hω
    rw [Real.norm_of_nonneg hω]
  have hHold := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf0 hg0 hfL hgL
  rw [one_div_one_div, one_div_one_div] at hHold
  -- the two factors
  have hind : (∫ ω, Set.indicator B (fun _ => (1 : ℝ)) ω ^ (1 / (1 - q)) ∂μ) = μ.real B := by
    have hcongr : (fun ω => Set.indicator B (fun _ => (1 : ℝ)) ω ^ (1 / (1 - q)))
        = Set.indicator B 1 := by
      funext ω
      by_cases hω : ω ∈ B
      · simp [Set.indicator_of_mem hω, Real.one_rpow]
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω,
          Real.zero_rpow (by positivity)]
    rw [hcongr, integral_indicator_one hB]
  have hpow : (∫ ω, (X ω ^ q) ^ (1 / q) ∂μ) = ∫ ω, X ω ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hX0] with ω hω
    rw [← Real.rpow_mul hω, mul_one_div_cancel hq0.ne', Real.rpow_one]
  rw [hind, hpow] at hHold
  exact hHold

/-! ### The envelope sum

The barrier bound behind Hamdan's Lemma 2.3 carries `∑_{i ∈ [r,n]} e^{-2b_i}`, the one sum left
that has to converge: the entropy of the partition has already spent the geometric `e^{-j}`.

The envelope used is the one-sided `b_i = 2\log i` rather than Hamdan's `2\log(1 + i ∧ (n-i))`
(his (2.12)).  Both satisfy what the two halves ask: `0 ≤ b_i ≤ i` on the range for Lemma 2.3, and
`|b_i| ≤ 10\log i` for Harper's Proposition 5; the one-sided form sums to `ζ(4)` by comparison
with a `p`-series. -/

/-- **The envelope sum converges**, uniformly in the range. -/
lemma sum_exp_neg_envelope_le {r n : ℕ} (hr : 1 ≤ r) :
    ∑ i ∈ Finset.Icc r n, Real.exp (-(2 * (2 * Real.log i)))
      ≤ ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ) := by
  have hterm : ∀ i ∈ Finset.Icc r n,
      Real.exp (-(2 * (2 * Real.log i))) = (i : ℝ) ^ (-4 : ℝ) := by
    intro i hi
    have hi1 : 1 ≤ i := le_trans hr (Finset.mem_Icc.1 hi).1
    have hipos : (0 : ℝ) < i := by exact_mod_cast hi1
    rw [Real.rpow_def_of_pos hipos]
    congr 1
    ring
  rw [Finset.sum_congr rfl hterm]
  exact Summable.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
    (Real.summable_nat_rpow.mpr (by norm_num))

/-- The envelope is admissible for Hamdan's Lemma 2.3: `2\log i ≤ i` once `i ≥ 1`. -/
lemma two_log_le_self {i : ℕ} (hi : 1 ≤ i) : 2 * Real.log i ≤ (i : ℝ) := by
  have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hhalf : (0 : ℝ) < (i : ℝ) / 2 := by linarith
  have hlog := Real.log_le_sub_one_of_pos hhalf
  rw [Real.log_div (by linarith) (by norm_num)] at hlog
  have hlt : Real.log 2 ≤ 7 / 10 :=
    le_of_lt (lt_of_lt_of_le Real.log_two_lt_d9 (by norm_num))
  linarith

end RMF
