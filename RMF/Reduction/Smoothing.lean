/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import RMF.Main
import RMF.SecondMoment
import RMF.NumberTheory.LogPrimeSum

/-!
# The smoothing step

The smoothing step of Harper's proof of his Proposition 3 (Harper, *Moments of random
multiplicative functions, I*, arXiv:1703.06654).  The sum
`∑_{√x<p≤x} log p · |∑_{m≤x/p} f(m)|²` has its summand depending on `p` through the *cutoff*
`x/p`, which is what stops it from being read as an integral.  Smoothing replaces the cutoff
`x/p` by a moving cutoff `x/t` with `t` ranging over a short interval `(p, p(1+1/X)]`; the price
is the discrepancy `∑_{x/t<m≤x/p} f(m)`, which is short because the interval is.

Two ingredients, and neither involves probability:

* an elementary inequality, `|a+b|² ≥ ¼|a|² − min{|b|², ¼|a|²}`, which is how the discrepancy is
  paid for — note the right-hand side is itself non-negative, so nothing is lost when the
  discrepancy is large;
* the observation that the summand is *constant* in `t`, so it equals its own average over the
  interval, of length `p/X`.

`X` is Harper's smoothing parameter.  He takes `X = e^{√log x}`, which needs a
Vinogradov–Korobov-strength prime input downstream; `X = log x` suffices and needs only the
classical error term.  Nothing in this file depends on that choice.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The elementary inequality -/

/-- **The smoothing inequality.**  `¼|a|² − min{|b|², ¼|a|²} ≤ |a+b|²`.

The subtracted term is capped at `¼|a|²`, so the left side is never negative: when the
discrepancy `b` is large the bound degrades to `0 ≤ |a+b|²` rather than going negative, which is
what makes it usable after summing over `p`. -/
lemma normSq_sub_min_le_normSq_add (a b : ℂ) :
    1 / 4 * ‖a‖ ^ 2 - min (‖b‖ ^ 2) (1 / 4 * ‖a‖ ^ 2) ≤ ‖a + b‖ ^ 2 := by
  rcases le_or_gt (1 / 4 * ‖a‖ ^ 2) (‖b‖ ^ 2) with h | h
  · rw [min_eq_right h, sub_self]
    positivity
  · rw [min_eq_left h.le]
    have h1 : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
      have h2 := norm_add_le (a + b) (-b)
      simpa using h2
    have hb : ‖b‖ < ‖a‖ / 2 := by
      nlinarith [norm_nonneg a, norm_nonneg b]
    nlinarith [h1, hb, norm_nonneg a, norm_nonneg b, norm_nonneg (a + b)]

/-! ### The averaging identity

The summand does not move with `t`, so it is its own average over the window, whose length is
`p/X`.  This is the only place the length of the window is used. -/

lemma window_length {p X : ℝ} (hp : 0 < p) (hX : 0 < X) :
    p * (1 + 1 / X) - p = p / X := by
  field_simp
  ring

lemma setIntegral_const_window {A : ℝ} {p X : ℝ} (hp : 0 < p) (hX : 0 < X) :
    X / p * ∫ _t in Set.Ioc p (p * (1 + 1 / X)), A = A := by
  have hle : p ≤ p * (1 + 1 / X) := by
    have : (0 : ℝ) ≤ p * (1 / X) := by positivity
    nlinarith
  have hmax : max (p / X) 0 = p / X := max_eq_left (by positivity)
  rw [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul, window_length hp hX, hmax]
  field_simp

/-! ### The partial sum along a moving cutoff -/

omit [MeasurableSpace Ω] in
/-- A partial sum is bounded by the sum of the moduli up to any larger cutoff. -/
lemma norm_randomSum_le_of_le (f : Ω → ArithmeticFunction ℂ) {t b : ℝ} (htb : t ≤ b) (ω : Ω) :
    ‖randomSum f t ω‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f ω n‖ := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · exact Finset.Icc_subset_Icc_right (Nat.floor_mono htb)
  · exact fun n _ _ => norm_nonneg _

omit [MeasurableSpace Ω] in
/-- `t ↦ ∑_{m ≤ x/t} f(m)` is measurable: it is a step function of `⌊x/t⌋`. -/
lemma measurable_randomSum_div (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) :
    Measurable fun t : ℝ => randomSum f (x / t) ω := by
  unfold randomSum
  exact (measurable_from_top (f := fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f ω n)).comp
    (Nat.measurable_floor.comp (measurable_const.div measurable_id))

/-- The discrepancy subtracted in `RMF.smoothing_bound`: the squared length of the block
`∑_{x/t<m≤x/p} f(m)`, capped at a quarter of the smoothed square.  The cap is what makes the
smoothing inequality true pointwise; the block is what makes it small in mean. -/
noncomputable def discrepancy (f : Ω → ArithmeticFunction ℂ) (x p : ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  min (‖randomSum f (x / p) ω - randomSum f (x / t) ω‖ ^ 2)
    (1 / 4 * ‖randomSum f (x / t) ω‖ ^ 2)

omit [MeasurableSpace Ω] in
/-- The discrepancy is nonnegative. -/
lemma discrepancy_nonneg (f : Ω → ArithmeticFunction ℂ) (x p : ℝ) (ω : Ω) (t : ℝ) :
    0 ≤ discrepancy f x p ω t :=
  le_min (by positivity) (by positivity)

omit [MeasurableSpace Ω] in
/-- The discrepancy is at most the squared length of the block. -/
lemma discrepancy_le_block (f : Ω → ArithmeticFunction ℂ) (x p : ℝ) (ω : Ω) (t : ℝ) :
    discrepancy f x p ω t ≤ ‖randomSum f (x / p) ω - randomSum f (x / t) ω‖ ^ 2 :=
  min_le_left _ _

omit [MeasurableSpace Ω] in
/-- The discrepancy is at most a quarter of the smoothed square. -/
lemma discrepancy_le_quarter (f : Ω → ArithmeticFunction ℂ) (x p : ℝ) (ω : Ω) (t : ℝ) :
    discrepancy f x p ω t ≤ 1 / 4 * ‖randomSum f (x / t) ω‖ ^ 2 :=
  min_le_right _ _

/-! ### The smoothing bound -/

omit [MeasurableSpace Ω] in
/-- **The smoothing bound.**  For each prime `p` and each `ω`,
`¼·(X/p)∫_p^{p(1+1/X)}|∑_{m≤x/t}f(m)|²dt - (X/p)∫_p^{p(1+1/X)} D(t) dt ≤ |∑_{m≤x/p}f(m)|²`,
where `D` is `RMF.discrepancy`.  The right side is Harper's summand; the left is the one whose sum
over `p` becomes an integral, because its dependence on `p` is now only through the window.
`D` is bounded in mean by `RMF.integral_discrepancy_le`. -/
theorem smoothing_bound {f : Ω → ArithmeticFunction ℂ} {x X p : ℝ} (hx : 0 ≤ x) (hX : 0 < X)
    (hp : 0 < p) (ω : Ω) :
    1 / 4 * (X / p * ∫ t in Set.Ioc p (p * (1 + 1 / X)), ‖randomSum f (x / t) ω‖ ^ 2)
        - X / p * ∫ t in Set.Ioc p (p * (1 + 1 / X)), discrepancy f x p ω t
      ≤ ‖randomSum f (x / p) ω‖ ^ 2 := by
  simp only [discrepancy]
  have hle : p ≤ p * (1 + 1 / X) := by
    have h : (0 : ℝ) ≤ p * (1 / X) := by positivity
    nlinarith
  have hXp : (0 : ℝ) < X / p := by positivity
  set K : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x / p⌋₊, ‖f ω n‖ with hKdef
  have hK0 : (0 : ℝ) ≤ K := Finset.sum_nonneg fun n _ => norm_nonneg _
  -- on the window the cutoff only decreases, so the partial sum stays below `K`
  have hbound : ∀ t ∈ Set.Ioc p (p * (1 + 1 / X)), ‖randomSum f (x / t) ω‖ ≤ K := by
    intro t ht
    have hdiv : x / t ≤ x / p := by
      gcongr
      exact ht.1.le
    exact norm_randomSum_le_of_le f hdiv ω
  -- measurability
  have hm1 : Measurable fun t : ℝ => ‖randomSum f (x / t) ω‖ ^ 2 :=
    ((measurable_randomSum_div f x ω).norm).pow_const 2
  have hm2 : Measurable fun t : ℝ =>
      min (‖randomSum f (x / p) ω - randomSum f (x / t) ω‖ ^ 2)
        (1 / 4 * ‖randomSum f (x / t) ω‖ ^ 2) :=
    (((measurable_const.sub (measurable_randomSum_div f x ω)).norm).pow_const 2).min
      (hm1.const_mul _)
  -- integrability on the window
  have hI1 : IntegrableOn (fun t : ℝ => ‖randomSum f (x / t) ω‖ ^ 2)
      (Set.Ioc p (p * (1 + 1 / X))) := by
    refine Measure.integrableOn_of_bounded (M := K ^ 2) measure_Ioc_lt_top.ne
      hm1.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound t ht) 2
  have hI2 : IntegrableOn (fun t : ℝ =>
      min (‖randomSum f (x / p) ω - randomSum f (x / t) ω‖ ^ 2)
        (1 / 4 * ‖randomSum f (x / t) ω‖ ^ 2)) (Set.Ioc p (p * (1 + 1 / X))) := by
    refine Measure.integrableOn_of_bounded (M := 1 / 4 * K ^ 2) measure_Ioc_lt_top.ne
      hm2.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hnn : (0 : ℝ) ≤ min (‖randomSum f (x / p) ω - randomSum f (x / t) ω‖ ^ 2)
        (1 / 4 * ‖randomSum f (x / t) ω‖ ^ 2) := le_min (by positivity) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    refine le_trans (min_le_right _ _) ?_
    have := pow_le_pow_left₀ (norm_nonneg (randomSum f (x / t) ω)) (hbound t ht) 2
    linarith
  -- the pointwise inequality
  have hpt : ∀ t ∈ Set.Ioc p (p * (1 + 1 / X)),
      1 / 4 * ‖randomSum f (x / t) ω‖ ^ 2
        - min (‖randomSum f (x / p) ω - randomSum f (x / t) ω‖ ^ 2)
            (1 / 4 * ‖randomSum f (x / t) ω‖ ^ 2)
      ≤ ‖randomSum f (x / p) ω‖ ^ 2 := by
    intro t _
    have h := normSq_sub_min_le_normSq_add (randomSum f (x / t) ω)
      (randomSum f (x / p) ω - randomSum f (x / t) ω)
    rwa [add_sub_cancel] at h
  -- integrate and scale
  have hmono := setIntegral_mono_on ((hI1.const_mul (1 / 4)).sub hI2)
    (integrableOn_const (by simp)) measurableSet_Ioc hpt
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub (hI1.const_mul (1 / 4)) hI2, integral_const_mul] at hmono
  have hfinal := mul_le_mul_of_nonneg_left hmono hXp.le
  rw [setIntegral_const_window hp hX] at hfinal
  have heq : X / p * (1 / 4 * (∫ t in Set.Ioc p (p * (1 + 1 / X)), ‖randomSum f (x / t) ω‖ ^ 2)
      - ∫ t in Set.Ioc p (p * (1 + 1 / X)),
          min (‖randomSum f (x / p) ω - randomSum f (x / t) ω‖ ^ 2)
            (1 / 4 * ‖randomSum f (x / t) ω‖ ^ 2))
      = 1 / 4 * (X / p * ∫ t in Set.Ioc p (p * (1 + 1 / X)), ‖randomSum f (x / t) ω‖ ^ 2)
        - X / p * ∫ t in Set.Ioc p (p * (1 + 1 / X)),
            min (‖randomSum f (x / p) ω - randomSum f (x / t) ω‖ ^ 2)
              (1 / 4 * ‖randomSum f (x / t) ω‖ ^ 2) := by ring
  rw [heq] at hfinal
  exact hfinal

/-- The summatory function is jointly measurable in `(ω, z)`. -/
lemma measurable_randomSum_uncurry {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) :
    Measurable fun p : Ω × ℝ => randomSum f p.2 p.1 := by
  have h1 : Measurable fun p : ℕ × Ω => ∑ n ∈ Finset.Icc 1 p.1, f p.2 n :=
    measurable_from_prod_countable_right fun N =>
      (Finset.measurable_sum (Finset.Icc 1 N) fun n _ => hf.measurable_apply n :
        Measurable fun y : Ω => ∑ n ∈ Finset.Icc 1 N, f y n)
  exact h1.comp ((Nat.measurable_floor.comp measurable_snd).prodMk measurable_fst)

/-! ### The discrepancy in mean square

`RMF.discrepancy` is dominated by `‖∑_{x/t<m≤x/p} f(m)‖²`, whose expectation is at most the
number of integers in the range — orthogonality again, now over an interval rather than an
initial segment. -/

/-- **The mean square of a sum over any finite set of nonzero indices** is at most the number of
terms.  The initial-segment case, with equality for Steinhaus, is
`RMF.IsSteinhausRMF.second_moment`; the interval case is what the discrepancy needs. -/
theorem integral_normSq_finsetSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) :
    (∫ ω, ‖∑ n ∈ s, f ω n‖ ^ 2 ∂μ) ≤ s.card :=
  hf.integral_normSq_sum_le s hs

omit [MeasurableSpace Ω] in
/-- A difference of partial sums is the sum over the intervening integers. -/
lemma randomSum_sub_eq (f : Ω → ArithmeticFunction ℂ) {a b : ℝ} (hab : a ≤ b) (ω : Ω) :
    randomSum f b ω - randomSum f a ω = ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f ω n := by
  have hsub : Finset.Icc 1 ⌊a⌋₊ ⊆ Finset.Icc 1 ⌊b⌋₊ :=
    Finset.Icc_subset_Icc_right (Nat.floor_mono hab)
  have hsdiff : Finset.Icc 1 ⌊b⌋₊ \ Finset.Icc 1 ⌊a⌋₊ = Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [randomSum, randomSum, ← Finset.sum_sdiff_eq_sub hsub, hsdiff]

/-- **The block's mean square.**  `E‖∑_{a<m≤b} f(m)‖² ≤ ⌊b⌋ - ⌊a⌋`.

An *inequality*: Steinhaus attains it, Rademacher counts only the squarefree indices in the
range. -/
theorem integral_normSq_randomSum_sub {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) {a b : ℝ} (hab : a ≤ b) :
    (∫ ω, ‖randomSum f b ω - randomSum f a ω‖ ^ 2 ∂μ) ≤ (⌊b⌋₊ : ℝ) - ⌊a⌋₊ := by
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have hcongr : (∫ ω, ‖randomSum f b ω - randomSum f a ω‖ ^ 2 ∂μ)
      = ∫ ω, ‖∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f ω n‖ ^ 2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only
      rw [randomSum_sub_eq f hab ω])
  rw [hcongr]
  refine le_trans (integral_normSq_finsetSum hf (fun n hn => by
    have := (Finset.mem_Ioc.1 hn).1; omega)) ?_
  rw [Nat.card_Ioc]
  push_cast [hfl]
  ring_nf
  rfl

/-- **The number of integers in the smoothing window's discrepancy range.**  For
`p ≤ t ≤ p(1+1/X)`, the range `(x/t, x/p]` contains at most `x/(pX) + 1` integers. -/
lemma floor_sub_floor_le {x X p t : ℝ} (hx : 0 ≤ x) (hX : 0 < X) (hp : 0 < p)
    (ht1 : p ≤ t) (ht2 : t ≤ p * (1 + 1 / X)) :
    (⌊x / p⌋₊ : ℝ) - ⌊x / t⌋₊ ≤ x / (p * X) + 1 := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hp ht1
  have h1 : (⌊x / p⌋₊ : ℝ) ≤ x / p := Nat.floor_le (by positivity)
  have h2 : x / t - 1 < (⌊x / t⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (x / t)
    linarith
  -- `x/p - x/t = x(t-p)/(pt) ≤ x(p/X)/p² = x/(pX)`
  have hexp : p * (1 + 1 / X) = p + p / X := by field_simp
  have htp : t - p ≤ p / X := by
    rw [hexp] at ht2
    linarith
  have hkey : x / p - x / t ≤ x / (p * X) := by
    have heq : x / p - x / t = x * (t - p) / (p * t) := by field_simp
    rw [heq]
    calc x * (t - p) / (p * t) ≤ x * (p / X) / (p * t) := by gcongr
      _ ≤ x * (p / X) / (p * p) := by gcongr
      _ = x / (p * X) := by field_simp
  linarith

/-- Almost surely, *every* partial sum with cutoff at most `b` is bounded by `⌊b⌋`.  The
quantifier over the cutoff is inside the `∀ᵐ`, which is what lets the bound be used along a whole
window of cutoffs at once. -/
lemma ae_norm_randomSum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (b : ℝ) :
    ∀ᵐ ω ∂μ, ∀ a : ℝ, a ≤ b → ‖randomSum f a ω‖ ≤ (⌊b⌋₊ : ℝ) := by
  have hall : ∀ n ∈ Finset.Icc 1 ⌊b⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 :=
    fun n _ => hf.ae_norm_le_one n
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω a hab
  refine le_trans (norm_randomSum_le_of_le f hab ω) ?_
  refine le_trans (Finset.sum_le_sum fun n hn => hω n hn) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
  simp

/-- The summatory function is measurable in `ω`, from boundedness alone — a finite sum of
measurable coordinates. -/
lemma IsBoundedRMF.measurable_randomSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (b : ℝ) : Measurable fun ω => randomSum f b ω :=
  Finset.measurable_sum _ fun n _ => hf.measurable_apply n

/-- With the cutoff moving as `x/t`, the summatory function is jointly measurable in `(ω, t)`. -/
lemma measurable_randomSum_div_uncurry {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (x : ℝ) :
    Measurable fun z : Ω × ℝ => randomSum f (x / z.2) z.1 :=
  (measurable_randomSum_uncurry hf).comp
    (measurable_fst.prodMk (measurable_const.div measurable_snd))

/-- The squared length of the block `∑_{x/t<m≤x/p} f(m)` is jointly measurable in `(ω, t)`. -/
lemma measurable_normSq_block {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (x p : ℝ) :
    Measurable fun z : Ω × ℝ =>
      ‖randomSum f (x / p) z.1 - randomSum f (x / z.2) z.1‖ ^ 2 :=
  ((((hf.measurable_randomSum (x / p)).comp measurable_fst).sub
    (measurable_randomSum_div_uncurry hf x)).norm).pow_const 2

/-- The discrepancy is jointly measurable in `(ω, t)`.  The dependence on `t` is through the
cutoff `⌊x/t⌋`, so this is `RMF.measurable_randomSum_uncurry` and nothing more. -/
lemma measurable_discrepancy {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (x p : ℝ) :
    Measurable fun z : Ω × ℝ => discrepancy f x p z.1 z.2 := by
  simp only [discrepancy]
  exact (measurable_normSq_block hf x p).min
    (((measurable_randomSum_div_uncurry hf x).norm.pow_const 2).const_mul (1 / 4 : ℝ))

/-- The squared length of a block of the summatory function is integrable. -/
lemma integrable_normSq_randomSum_sub {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) {a b : ℝ} (hab : a ≤ b) :
    Integrable (fun ω => ‖randomSum f b ω - randomSum f a ω‖ ^ 2) μ := by
  refine Integrable.mono' (integrable_const (4 * (⌊b⌋₊ : ℝ) ^ 2))
    ((((hf.measurable_randomSum b).sub
      (hf.measurable_randomSum a)).norm.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [ae_norm_randomSum_le hf b] with ω hω
  have h1 := hω b le_rfl
  have h2 := hω a hab
  have h3 : ‖randomSum f b ω - randomSum f a ω‖ ≤ 2 * (⌊b⌋₊ : ℝ) :=
    le_trans (norm_sub_le _ _) (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [norm_nonneg (randomSum f b ω - randomSum f a ω)]

/-- For a fixed `t` in the window, the discrepancy is integrable in `ω`. -/
lemma integrable_discrepancy_slice {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) {x p t : ℝ} (hx : 0 ≤ x) (hp : 0 < p)
    (ht : p ≤ t) : Integrable (fun ω => discrepancy f x p ω t) μ := by
  have hdiv : x / t ≤ x / p := by gcongr
  have hm : Measurable fun ω => discrepancy f x p ω t := by
    simp only [discrepancy]
    exact (((hf.measurable_randomSum (x / p)).sub
      (hf.measurable_randomSum (x / t))).norm.pow_const 2).min
      (((hf.measurable_randomSum (x / t)).norm.pow_const 2).const_mul (1 / 4 : ℝ))
  refine Integrable.mono' (integrable_normSq_randomSum_sub hf hdiv) hm.aestronglyMeasurable ?_
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (discrepancy_nonneg f x p ω t)]
    exact discrepancy_le_block f x p ω t

/-- The discrepancy is bounded on the window, hence integrable for the product measure — which is
what licenses the exchange of `∀ᵐ ω` and `∫ dt` below. -/
lemma integrable_discrepancy {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) {x X p : ℝ} (hx : 0 ≤ x) (hp : 0 < p) :
    Integrable (Function.uncurry (discrepancy f x p))
      (μ.prod (volume.restrict (Set.Ioc p (p * (1 + 1 / X))))) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc p (p * (1 + 1 / X)))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  refine integrableOn_univ.1 (Measure.integrableOn_of_bounded
    (M := 1 / 4 * (⌊x / p⌋₊ : ℝ) ^ 2) (measure_ne_top _ _)
    (measurable_discrepancy hf x p).aestronglyMeasurable ?_)
  rw [Measure.restrict_univ]
  refine (Measure.ae_prod_iff_ae_ae (measurableSet_le
    (measurable_discrepancy hf x p).norm measurable_const)).2 ?_
  filter_upwards [ae_norm_randomSum_le hf (x / p)] with ω hω
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hpt : p ≤ t := ht.1.le
  have hdiv : x / t ≤ x / p := by gcongr
  have hnorm := hω (x / t) hdiv
  rw [Real.norm_eq_abs, abs_of_nonneg (discrepancy_nonneg f x p ω t)]
  refine le_trans (discrepancy_le_quarter f x p ω t) ?_
  have := pow_le_pow_left₀ (norm_nonneg (randomSum f (x / t) ω)) hnorm 2
  linarith

/-- **The discrepancy, one prime at a time.**  The expected discrepancy over the window
`(p, p(1+1/X)]` is at most `x/(pX) + 1`.  Three inputs, in order: Fubini (the discrepancy is
bounded, so product-integrable); orthogonality, which bounds the mean square of the block by the
number of integers it contains (`RMF.integral_normSq_randomSum_sub`); and the length of the
window (`RMF.floor_sub_floor_le`). -/
theorem integral_discrepancy_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) {x X p : ℝ} (hx : 0 ≤ x) (hX : 0 < X)
    (hp : 0 < p) :
    (∫ ω, X / p * (∫ t in Set.Ioc p (p * (1 + 1 / X)), discrepancy f x p ω t) ∂μ)
      ≤ x / (p * X) + 1 := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc p (p * (1 + 1 / X)))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hInt := integrable_discrepancy (X := X) hf hx hp
  rw [integral_const_mul, integral_integral_swap hInt]
  have hbound : ∀ t ∈ Set.Ioc p (p * (1 + 1 / X)),
      (∫ ω, discrepancy f x p ω t ∂μ) ≤ x / (p * X) + 1 := by
    intro t ht
    have hpt : p ≤ t := ht.1.le
    have hdiv : x / t ≤ x / p := by gcongr
    have hle : (∫ ω, discrepancy f x p ω t ∂μ)
        ≤ ∫ ω, ‖randomSum f (x / p) ω - randomSum f (x / t) ω‖ ^ 2 ∂μ :=
      integral_mono_ae (integrable_discrepancy_slice hf hx hp hpt)
        (integrable_normSq_randomSum_sub hf hdiv)
        (Filter.Eventually.of_forall fun ω => discrepancy_le_block f x p ω t)
    refine le_trans (le_trans hle (integral_normSq_randomSum_sub hf hdiv)) ?_
    exact floor_sub_floor_le hx hX hp hpt ht.2
  have hconst : X / p * ∫ _t in Set.Ioc p (p * (1 + 1 / X)), (x / (p * X) + 1)
      = x / (p * X) + 1 := setIntegral_const_window hp hX
  rw [← hconst]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact setIntegral_mono_on hInt.integral_prod_right (integrableOn_const (by simp))
    measurableSet_Ioc hbound

/-! ### The discrepancy, summed over the primes

Multiplying the per-prime bound by `log p` and summing turns the two pieces of `x/(pX) + 1` into
Mertens' first theorem and Chebyshev's `θ` — `RMF.sum_log_prime_mul_smoothing_le`.  Jensen then
trades the `q`-th moment for the mean, which is legitimate because `q ≤ 1`. -/

/-- The discrepancy sum is integrable, prime by prime. -/
lemma integrable_log_mul_window_discrepancy {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) {x X : ℝ} (hx : 0 ≤ x) {p : ℕ}
    (hp : (0 : ℝ) < p) :
    Integrable (fun ω => Real.log p *
      (X / p * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / X)),
        discrepancy f x p ω t)) μ :=
  (((integrable_discrepancy (X := X) hf hx hp).integral_prod_left).const_mul _).const_mul _

/-- **The total discrepancy, in mean**, over any set `S` of primes below `x`. -/
theorem integral_sum_discrepancy_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) {x X : ℝ} (hx : 1 ≤ x) (hX : 0 < X)
    {S : Finset ℕ} (hS : S ⊆ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime}) :
    (∫ ω, ∑ p ∈ S, Real.log p *
        (X / p * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / X)),
          discrepancy f x p ω t) ∂μ)
      ≤ x * (Real.log x + Real.log 4 + 4) / X + Real.log 4 * x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hpos : ∀ p ∈ S, (0 : ℝ) < p := fun p hp => by
    exact_mod_cast (Finset.mem_filter.1 (hS hp)).2.pos
  rw [integral_finsetSum _ fun p hp =>
    integrable_log_mul_window_discrepancy hf hx0 (hpos p hp)]
  refine le_trans (Finset.sum_le_sum ?_) (sum_log_prime_mul_smoothing_le hx hX hS)
  intro p hp
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_discrepancy_le hf hx0 hX (hpos p hp))
    (Real.log_natCast_nonneg p)

/-! ### The discrepancy at the working scale `X = log x`

`X = log x` is the smallest smoothing scale for which the error stays `O(x)`, as Harper's
Proposition 3 needs, and it is the largest for which the prime input of the main term
(`RMF.window_weight_ge`) is `RS_prime.pnt` rather than a zero-free region.  At that scale the
two pieces of the error are comparable and the total is `(5 + 2 log 4) x < 8x`. -/

/-- `log 4 < 1.4`, from `Real.log_two_lt_d9`. -/
lemma log_four_lt : Real.log 4 < 1.4 := by
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith

/-- The discrepancy bound at `X = log x`: `x(log x + log 4 + 4)/log x + log 4 · x ≤ 8x`. -/
lemma discrepancy_budget_le {x : ℝ} (hx : Real.exp 1 ≤ x) :
    x * (Real.log x + Real.log 4 + 4) / Real.log x + Real.log 4 * x ≤ 8 * x := by
  have hx1 : (1 : ℝ) ≤ x := by
    have := Real.exp_one_gt_d9
    linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hL : (1 : ℝ) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have h40 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h4 := log_four_lt
  have hdiv : x * (Real.log x + Real.log 4 + 4) / Real.log x
      ≤ x + x * (Real.log 4 + 4) := by
    rw [div_le_iff₀ hLpos]
    nlinarith [mul_nonneg (mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ Real.log 4 + 4))
      (by linarith : (0 : ℝ) ≤ Real.log x - 1)]
  nlinarith

/-- **The total discrepancy at `X = log x`, in mean**: at most `8x`. -/
theorem integral_sum_discrepancy_le_log {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) {x : ℝ} (hx : Real.exp 1 ≤ x)
    {S : Finset ℕ} (hS : S ⊆ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime}) :
    (∫ ω, ∑ p ∈ S, Real.log p *
        (Real.log x / p * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
          discrepancy f x p ω t) ∂μ)
      ≤ 8 * x := by
  have hx1 : (1 : ℝ) ≤ x := by
    have := Real.exp_one_gt_d9
    linarith
  have hLpos : (0 : ℝ) < Real.log x := by
    have hL : (1 : ℝ) ≤ Real.log x := (Real.le_log_iff_exp_le (by linarith)).2 hx
    linarith
  exact le_trans (integral_sum_discrepancy_le hf hx1 hLpos hS) (discrepancy_budget_le hx)

end RMF
