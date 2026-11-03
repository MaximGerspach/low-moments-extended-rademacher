/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Main
import RMF.SecondMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import RMF.Reduction.Periodisation
import RMF.Reduction.Steps

/-!
# Symmetrisation: the rough part is no larger than the whole

Harper's proof of Proposition 3 opens by discarding the `√x`-smooth numbers,

`‖∑_{n≤x} f(n)‖_{2q} ≫ ‖∑_{n≤x, P(n)>√x} f(n)‖_{2q}`,

and he obtains it by introducing an auxiliary Rademacher variable `ε` independent of everything.

**That variable is avoidable**, which matters because introducing it in Lean means enlarging the
probability space and threading the enlargement through every downstream statement.  Write
`∑_{n≤x} f(n) = A + B` with `A` the rough part and `B` the smooth part.  Negating `f(p)` for every
`p > √x` maps `(A,B) ↦ (−A,B)`: below `x` a number has *at most one* prime factor above `√x`, and
that factor occurs to the first power, so each rough term changes sign exactly once while the
smooth terms do not move at all.  Negation is unimodular, so it preserves the Steinhaus law, and
hence `E|A−B|^{2q} = E|A+B|^{2q}`.  Convexity of `t ↦ |t|^r` for `r ≥ 1` then gives

`|A|^r ≤ (|A+B|^r + |A−B|^r)/2`

pointwise, and averaging finishes.  The constant is `1`, where Harper's argument gives `1/2`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The sign attached by a large-prime flip -/

/-- The flip: `+1` at the small primes, `-1` at the large ones. -/
noncomputable def flipSign (y p : ℕ) : ℂ := if p ≤ y then 1 else -1

lemma norm_flipSign (y p : ℕ) : ‖flipSign y p‖ = 1 := by
  rw [flipSign]
  split <;> simp

/-- **Below `(y+1)²` a number has at most one prime factor above `y`.** -/
lemma card_large_primeFactors_le {y n : ℕ} (hn2 : n < (y + 1) ^ 2) :
    ({p ∈ n.primeFactors | y < p} : Finset ℕ).card ≤ 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨p, hp, p', hp', hne⟩ := Finset.one_lt_card.1 hc
  rw [Finset.mem_filter] at hp hp'
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
  have hpp' : p'.Prime := Nat.prime_of_mem_primeFactors hp'.1
  have hn0 : n ≠ 0 := (Nat.mem_primeFactors.1 hp.1).2.2
  have hcop : Nat.Coprime p p' := (Nat.coprime_primes hpp hpp').2 hne
  have hdvd : p * p' ∣ n :=
    hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp.1)
      (Nat.dvd_of_mem_primeFactors hp'.1)
  have hle : p * p' ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
  have h1 : y + 1 ≤ p := hp.2
  have h2 : y + 1 ≤ p' := hp'.2
  nlinarith [hle, h1, h2, hn2]

/-- **And that factor occurs to the first power.** -/
lemma factorization_large_eq_one {y n : ℕ} (hn2 : n < (y + 1) ^ 2)
    {p : ℕ} (hp : p ∈ n.primeFactors) (hpy : y < p) : n.factorization p = 1 := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hn0 : n ≠ 0 := (Nat.mem_primeFactors.1 hp).2.2
  have h1 : 1 ≤ n.factorization p :=
    (Nat.Prime.factorization_pos_of_dvd hpp hn0 (Nat.dvd_of_mem_primeFactors hp))
  by_contra hne
  have h2 : 2 ≤ n.factorization p := by omega
  have hdvd : p ^ 2 ∣ n := dvd_trans (pow_dvd_pow p h2) (Nat.ordProj_dvd n p)
  have hle : p ^ 2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
  have h3 : y + 1 ≤ p := hpy
  nlinarith [hle, h3, hn2]

/-- Smoothness is exactly the absence of large prime factors. -/
lemma smoothNumbers_iff_filter_empty {y n : ℕ} (hn : n ≠ 0) :
    n ∈ Nat.smoothNumbers (y + 1) ↔ ({p ∈ n.primeFactors | y < p} : Finset ℕ) = ∅ := by
  rw [Nat.mem_smoothNumbers', Finset.filter_eq_empty_iff]
  constructor
  · intro h p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have := h p hpp (Nat.dvd_of_mem_primeFactors hp)
    omega
  · intro h p hpp hpd
    have hp : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hpp, hpd, hn⟩
    have := h hp
    omega

/-- **The sign.**  Flipping the values at the primes above `y` multiplies `f(n)` by `-1` exactly
when `n` is not `y`-smooth, provided `n < (y+1)²`. -/
lemma compMultExtension_flipSign {x : ℕ → ℂ} {y n : ℕ} (hn : n ≠ 0) (hn2 : n < (y + 1) ^ 2) :
    compMultExtension (fun p => flipSign y p * x p) n
      = (if n ∈ Nat.smoothNumbers (y + 1) then (1 : ℂ) else -1) * compMultExtension x n := by
  rw [compMultExtension_apply_of_ne_zero _ hn, compMultExtension_apply_of_ne_zero _ hn,
    Finsupp.prod, Finsupp.prod, Nat.support_factorization]
  have hsplit : ∀ p ∈ n.primeFactors,
      (flipSign y p * x p) ^ n.factorization p
        = flipSign y p ^ n.factorization p * x p ^ n.factorization p :=
    fun p _ => mul_pow _ _ _
  rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib]
  congr 1
  -- the sign product
  rw [← Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => y < p)]
  have hsmall : (∏ p ∈ {p ∈ n.primeFactors | ¬ y < p}, flipSign y p ^ n.factorization p)
      = 1 := by
    refine Finset.prod_eq_one fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [flipSign, if_pos (by omega), one_pow]
  have hlarge : (∏ p ∈ {p ∈ n.primeFactors | y < p}, flipSign y p ^ n.factorization p)
      = ∏ _p ∈ {p ∈ n.primeFactors | y < p}, (-1 : ℂ) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [flipSign, if_neg (by omega), factorization_large_eq_one hn2 hp.1 hp.2, pow_one]
  rw [hsmall, hlarge, mul_one, Finset.prod_const]
  rcases Finset.eq_empty_or_nonempty ({p ∈ n.primeFactors | y < p} : Finset ℕ) with he | hne
  · rw [he, if_pos ((smoothNumbers_iff_filter_empty hn).2 he)]
    simp
  · have hcard : ({p ∈ n.primeFactors | y < p} : Finset ℕ).card = 1 := by
      have h1 := card_large_primeFactors_le (y := y) hn2
      have h2 := Finset.card_pos.2 hne
      omega
    rw [hcard, if_neg (fun hs => hne.ne_empty ((smoothNumbers_iff_filter_empty hn).1 hs))]
    simp

/-- **The sign extraction for the squarefree extension.**  The mirror of
`RMF.compMultExtension_flipSign`.

The sign product is the same — `1` on the `y`-smooth numbers and `-1` off them, since below
`(y+1)²` a number has at most one prime factor above `y` — but the exponents are all `1` here, so
the `factorization_large_eq_one` step is not needed.  Off the squarefrees both sides vanish. -/
lemma squarefreeExtension_flipSign {x : ℕ → ℂ} {y n : ℕ} (hn : n ≠ 0) (hn2 : n < (y + 1) ^ 2) :
    squarefreeExtension (fun p => flipSign y p * x p) n
      = (if n ∈ Nat.smoothNumbers (y + 1) then (1 : ℂ) else -1) * squarefreeExtension x n := by
  by_cases hsf : Squarefree n
  · rw [squarefreeExtension_apply_of_squarefree _ hsf,
      squarefreeExtension_apply_of_squarefree _ hsf, Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => y < p)]
    have hsmall : (∏ p ∈ {p ∈ n.primeFactors | ¬ y < p}, flipSign y p) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      rw [Finset.mem_filter] at hp
      rw [flipSign, if_pos (by omega)]
    have hlarge : (∏ p ∈ {p ∈ n.primeFactors | y < p}, flipSign y p)
        = ∏ _p ∈ {p ∈ n.primeFactors | y < p}, (-1 : ℂ) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Finset.mem_filter] at hp
      rw [flipSign, if_neg (by omega)]
    rw [hsmall, hlarge, mul_one, Finset.prod_const]
    rcases Finset.eq_empty_or_nonempty ({p ∈ n.primeFactors | y < p} : Finset ℕ) with he | hne
    · rw [he, if_pos ((smoothNumbers_iff_filter_empty hn).2 he)]
      simp
    · have hcard : ({p ∈ n.primeFactors | y < p} : Finset ℕ).card = 1 := by
        have h1 := card_large_primeFactors_le (y := y) hn2
        have h2 := Finset.card_pos.2 hne
        omega
      rw [hcard, if_neg (fun hs => hne.ne_empty ((smoothNumbers_iff_filter_empty hn).1 hs))]
      simp
  · rw [squarefreeExtension_apply_of_not_squarefree _ hsf,
      squarefreeExtension_apply_of_not_squarefree _ hsf, mul_zero]

/-! ### The flip on the partial sums

`∑_{n≤x} f'(n) = 2∑_{n≤x, smooth} f(n) - ∑_{n≤x} f(n)`, which is `-A + B` written in terms of the
whole sum and its smooth part. -/

omit [MeasurableSpace Ω] in
lemma randomSum_flipSignOf {ext : (ℕ → ℂ) → ArithmeticFunction ℂ} {X : ℕ → Ω → ℂ}
    {x : ℝ} {y : ℕ}
    (hsign : ∀ (v : ℕ → ℂ) (n : ℕ), n ≠ 0 → n < (y + 1) ^ 2 →
      ext (fun p => flipSign y p * v p) n
        = (if n ∈ Nat.smoothNumbers (y + 1) then (1 : ℂ) else -1) * ext v n)
    (hxy : ⌊x⌋₊ < (y + 1) ^ 2) (ω : Ω) :
    randomSum (fun ω => ext fun p => flipSign y p * X p ω) x ω
      = 2 * smoothPartial (fun ω => ext fun p => X p ω) y x ω
        - randomSum (fun ω => ext fun p => X p ω) x ω := by
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ext (fun p => flipSign y p * X p ω) n
        = (if n ∈ Nat.smoothNumbers (y + 1) then (1 : ℂ) else -1)
            * ext (fun p => X p ω) n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact hsign _ _ (by omega) (by omega)
  rw [randomSum, randomSum, smoothPartial, Finset.sum_congr rfl hterm]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊x⌋₊)
    (fun n => n ∈ Nat.smoothNumbers (y + 1))
    (fun n => ext (fun p => X p ω) n)]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊x⌋₊)
    (fun n => n ∈ Nat.smoothNumbers (y + 1))
    (fun n => (if n ∈ Nat.smoothNumbers (y + 1) then (1 : ℂ) else -1)
      * ext (fun p => X p ω) n)]
  have hyes : (∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | n ∈ Nat.smoothNumbers (y + 1)},
        (if n ∈ Nat.smoothNumbers (y + 1) then (1 : ℂ) else -1)
          * ext (fun p => X p ω) n)
      = ∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | n ∈ Nat.smoothNumbers (y + 1)},
          ext (fun p => X p ω) n :=
    Finset.sum_congr rfl fun n hn => by
      rw [if_pos (Finset.mem_filter.1 hn).2, one_mul]
  have hno : (∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | ¬ n ∈ Nat.smoothNumbers (y + 1)},
        (if n ∈ Nat.smoothNumbers (y + 1) then (1 : ℂ) else -1)
          * ext (fun p => X p ω) n)
      = -∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | ¬ n ∈ Nat.smoothNumbers (y + 1)},
          ext (fun p => X p ω) n := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun n hn => by
      rw [if_neg (Finset.mem_filter.1 hn).2]
      ring
  rw [hyes, hno]
  ring

/-! ### Convexity -/

/-- `|u|^r ≤ (|u+v|^r + |u-v|^r)/2` for `r ≥ 1`: the parallelogram-flavoured half of convexity,
and the only analytic input the symmetrisation needs. -/
lemma norm_rpow_le_avg {u v : ℂ} {r : ℝ} (hr : 1 ≤ r) :
    ‖u‖ ^ r ≤ (‖u + v‖ ^ r + ‖u - v‖ ^ r) / 2 := by
  have hmid : ‖u‖ ≤ (‖u + v‖ + ‖u - v‖) / 2 := by
    have h2 : ‖(2 : ℂ) * u‖ ≤ ‖u + v‖ + ‖u - v‖ := by
      have : (2 : ℂ) * u = (u + v) + (u - v) := by ring
      rw [this]
      exact norm_add_le _ _
    rw [norm_mul] at h2
    simp only [Complex.norm_ofNat] at h2
    linarith
  have hcvx := (convexOn_rpow hr).2 (Set.mem_Ici.2 (norm_nonneg (u + v)))
    (Set.mem_Ici.2 (norm_nonneg (u - v))) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hcvx
  calc ‖u‖ ^ r ≤ ((‖u + v‖ + ‖u - v‖) / 2) ^ r :=
        Real.rpow_le_rpow (norm_nonneg _) hmid (by linarith)
    _ = (1 / 2 * ‖u + v‖ + 1 / 2 * ‖u - v‖) ^ r := by ring_nf
    _ ≤ 1 / 2 * ‖u + v‖ ^ r + 1 / 2 * ‖u - v‖ ^ r := hcvx
    _ = (‖u + v‖ ^ r + ‖u - v‖ ^ r) / 2 := by ring

/-! ### The symmetrisation step

The flip preserves the law, so the two `±` sums have the same moment, and convexity does the
rest. -/

/-- The partial sum as a functional of the values at the primes, which is the form
`RMF.IsSteinhausPrimeValues.integral_comp_rotate` transports. -/
noncomputable def sumFunctionalOf (ext : (ℕ → ℂ) → ArithmeticFunction ℂ) (x r : ℝ)
    (v : Nat.Primes → ℂ) : ℝ :=
  ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ext (primeExtend v) n‖ ^ r

lemma measurable_sumFunctionalOf {ext : (ℕ → ℂ) → ArithmeticFunction ℂ}
    (hmeas : ∀ n : ℕ, Measurable fun v : Nat.Primes → ℂ => ext (primeExtend v) n) (x r : ℝ) :
    Measurable (sumFunctionalOf ext x r) := by
  unfold sumFunctionalOf
  exact ((Finset.measurable_sum _ fun n _ => hmeas n).norm).pow_const r

lemma sumFunctionalOf_apply {ext : (ℕ → ℂ) → ArithmeticFunction ℂ}
    (hcongr : ∀ {v w : ℕ → ℂ}, (∀ p, p.Prime → v p = w p) → ext v = ext w)
    (g : ℕ → ℂ) (x r : ℝ) :
    sumFunctionalOf ext x r (fun p : Nat.Primes => g (p : ℕ))
      = ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ext g n‖ ^ r := by
  unfold sumFunctionalOf
  rw [hcongr (v := primeExtend fun p : Nat.Primes => g (p : ℕ)) (w := g)
    fun p hp => primeExtend_apply _ hp]

lemma measurable_compMultExtension_primeExtend (n : ℕ) :
    Measurable fun v : Nat.Primes → ℂ => compMultExtension (primeExtend v) n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [compMultExtension_apply_of_ne_zero _ hn, Finsupp.prod, Nat.support_factorization]
    exact Finset.measurable_prod _ fun p _ => (measurable_primeExtend p).pow_const _

/-- The partial sum is bounded by the number of its terms. -/
lemma norm_randomSum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (x : ℝ) :
    ∀ᵐ ω ∂μ, ‖randomSum f x ω‖ ≤ ⌊x⌋₊ := by
  have hall : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 :=
    fun n _ => hf.ae_norm_le_one n
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun n hn => hω n hn) ?_
  simp

lemma measurable_randomSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (x : ℝ) :
    Measurable fun ω => randomSum f x ω :=
  Finset.measurable_sum _ fun n _ => hf.measurable_apply n

lemma ae_norm_smoothPartial_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (y : ℕ) (x : ℝ) :
    ∀ᵐ ω ∂μ, ‖smoothPartial f y x ω‖ ≤ ⌊x⌋₊ := by
  have hall : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 :=
    fun n _ => hf.ae_norm_le_one n
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
  rw [smoothPartial]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun n hn => ?_) ?_
  · exact hω n (Finset.mem_filter.1 hn).1
  · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have h1 : ({n ∈ Finset.Icc 1 ⌊x⌋₊ | n ∈ Nat.smoothNumbers (y + 1)} : Finset ℕ).card
        ≤ (Finset.Icc 1 ⌊x⌋₊).card := Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : (Finset.Icc 1 ⌊x⌋₊).card = ⌊x⌋₊ := by simp
    rw [h2] at h1
    exact_mod_cast h1

/-- **Symmetrisation.**  The rough part has no larger a moment than the whole sum.

Harper obtains this with an auxiliary Rademacher variable and a factor `1/2`; negating the values
at the large primes does the same job with constant `1` and no enlargement of the space. -/
theorem integral_rough_leOf {ext : (ℕ → ℂ) → ArithmeticFunction ℂ} {X : ℕ → Ω → ℂ}
    {ν : Measure ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsIIDPrimeValues X ν μ) {x : ℝ} {y : ℕ}
    (hc : ∀ p : ℕ, 0 < p → Measure.map (fun z : ℂ => flipSign y p * z) ν = ν)
    (hsign : ∀ (v : ℕ → ℂ) (n : ℕ), n ≠ 0 → n < (y + 1) ^ 2 →
      ext (fun p => flipSign y p * v p) n
        = (if n ∈ Nat.smoothNumbers (y + 1) then (1 : ℂ) else -1) * ext v n)
    (hbd : ∀ Y : ℕ → Ω → ℂ, IsIIDPrimeValues Y ν μ →
      IsBoundedRMF (fun ω => ext fun p => Y p ω) μ)
    (hmeasExt : ∀ n : ℕ, Measurable fun v : Nat.Primes → ℂ => ext (primeExtend v) n)
    (hcongr : ∀ {v w : ℕ → ℂ}, (∀ p, p.Prime → v p = w p) → ext v = ext w)
    (hxy : ⌊x⌋₊ < (y + 1) ^ 2) {q : ℝ} (hq : 1 ≤ 2 * q) :
    (∫ ω, ‖randomSum (fun ω => ext fun p => X p ω) x ω
        - smoothPartial (fun ω => ext fun p => X p ω) y x ω‖ ^ (2 * q) ∂μ)
      ≤ ∫ ω, ‖randomSum (fun ω => ext fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  have hq0 : (0 : ℝ) < 2 * q := by linarith
  set X' : ℕ → Ω → ℂ := fun p ω => flipSign y p * X p ω with hX'def
  have hX' : IsIIDPrimeValues X' ν μ := hX.mul_const hc
  -- the flipped sum is `2B - (A+B)`, so `A - B = -(flipped)`
  have hAB : ∀ ω, randomSum (fun ω => ext fun p => X p ω) x ω
        - smoothPartial (fun ω => ext fun p => X p ω) y x ω
        - smoothPartial (fun ω => ext fun p => X p ω) y x ω
      = -randomSum (fun ω => ext fun p => X' p ω) x ω := by
    intro ω
    rw [hX'def, randomSum_flipSignOf hsign hxy ω]
    ring
  -- pointwise convexity
  have hpt : ∀ ω, ‖randomSum (fun ω => ext fun p => X p ω) x ω
        - smoothPartial (fun ω => ext fun p => X p ω) y x ω‖ ^ (2 * q)
      ≤ (‖randomSum (fun ω => ext fun p => X p ω) x ω‖ ^ (2 * q)
          + ‖randomSum (fun ω => ext fun p => X' p ω) x ω‖ ^ (2 * q)) / 2 := by
    intro ω
    have h := norm_rpow_le_avg
      (u := randomSum (fun ω => ext fun p => X p ω) x ω
        - smoothPartial (fun ω => ext fun p => X p ω) y x ω)
      (v := smoothPartial (fun ω => ext fun p => X p ω) y x ω) hq
    rw [sub_add_cancel, hAB ω, norm_neg] at h
    exact h
  -- integrability
  have hb : ∀ (Y : ℕ → Ω → ℂ), IsIIDPrimeValues Y ν μ →
      Integrable (fun ω => ‖randomSum (fun ω => ext fun p => Y p ω) x ω‖
        ^ (2 * q)) μ := by
    intro Y hY
    refine (memLp_top_of_bound
      (((measurable_randomSum (hbd Y hY) x).norm.pow_const (2 * q)).aestronglyMeasurable)
      ((⌊x⌋₊ : ℝ) ^ (2 * q)) ?_).integrable le_top
    filter_upwards [norm_randomSum_le (hbd Y hY) x] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) hω hq0.le
  have hI1 := hb X hX
  have hI2 := hb X' hX'
  -- the law is preserved
  have hlaw : (∫ ω, ‖randomSum (fun ω => ext fun p => X' p ω) x ω‖ ^ (2 * q) ∂μ)
      = ∫ ω, ‖randomSum (fun ω => ext fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
    have h := hX.integral_comp_mul_const (c := flipSign y) hc
      (measurable_sumFunctionalOf hmeasExt x (2 * q))
    have hL : ∀ ω : Ω, sumFunctionalOf ext x (2 * q)
        (fun p : Nat.Primes => flipSign y (p : ℕ) * X (p : ℕ) ω)
        = ‖randomSum (fun ω => ext fun p => X' p ω) x ω‖ ^ (2 * q) :=
      fun ω => sumFunctionalOf_apply hcongr (fun n => flipSign y n * X n ω) x (2 * q)
    have hR : ∀ ω : Ω, sumFunctionalOf ext x (2 * q) (fun p : Nat.Primes => X (p : ℕ) ω)
        = ‖randomSum (fun ω => ext fun p => X p ω) x ω‖ ^ (2 * q) :=
      fun ω => sumFunctionalOf_apply hcongr (fun n => X n ω) x (2 * q)
    rw [integral_congr_ae (Filter.Eventually.of_forall hL),
      integral_congr_ae (Filter.Eventually.of_forall hR)] at h
    exact h
  -- assemble
  have hmono : (∫ ω, ‖randomSum (fun ω => ext fun p => X p ω) x ω
        - smoothPartial (fun ω => ext fun p => X p ω) y x ω‖ ^ (2 * q) ∂μ)
      ≤ ∫ ω, (‖randomSum (fun ω => ext fun p => X p ω) x ω‖ ^ (2 * q)
          + ‖randomSum (fun ω => ext fun p => X' p ω) x ω‖ ^ (2 * q)) / 2 ∂μ := by
    refine integral_mono ?_ (((hI1.add hI2).div_const 2)) hpt
    refine (memLp_top_of_bound ?_ ((2 * ⌊x⌋₊ : ℝ) ^ (2 * q)) ?_).integrable le_top
    · exact (((measurable_randomSum (hbd X hX) x).sub
        (Finset.measurable_sum _ fun n _ => (hbd X hX).measurable_apply n)).norm.pow_const
        (2 * q)).aestronglyMeasurable
    · filter_upwards [norm_randomSum_le (hbd X hX) x,
      ae_norm_smoothPartial_le (hbd X hX) y x] with ω h1 h2
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      refine Real.rpow_le_rpow (norm_nonneg _) ?_ hq0.le
      exact le_trans (norm_sub_le _ _) (by linarith)
  rw [integral_div, integral_add hI1 hI2, hlaw] at hmono
  linarith

/-! ### Symmetrisation below `2q = 1`

Convexity of `t ↦ t^{2q}` is lost below `2q = 1`, and subadditivity takes its place: the flip
still writes the rough part as `(S - S')/2` with `S'` equal in law to `S`, and
`‖S - S'‖^{2q} ≤ ‖S‖^{2q} + ‖S'‖^{2q}` then costs the constant `2^{1-2q}`.  This is the step of
Proposition 6 of Gerspach, *Low pseudomoments of the Riemann zeta function and its powers*
(arXiv:1909.10224), done with the flip rather than an auxiliary Rademacher variable, as for
`RMF.integral_rough_leOf`. -/

/-- `‖u - v‖^r ≤ ‖u‖^r + ‖v‖^r` for `0 ≤ r ≤ 1`: subadditivity of `t ↦ t^r`. -/
lemma norm_sub_rpow_le_add {u v : ℂ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖u - v‖ ^ r ≤ ‖u‖ ^ r + ‖v‖ ^ r :=
  le_trans (Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le u v) hr0)
    (Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) hr0 hr1)

/-- **Symmetrisation for `2q ≤ 1`.**  The rough part's `2q`-th moment is at most `2^{1-2q}`
times the whole sum's. -/
theorem integral_rough_le_of_le_oneOf {ext : (ℕ → ℂ) → ArithmeticFunction ℂ}
    {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsIIDPrimeValues X ν μ) {x : ℝ} {y : ℕ}
    (hc : ∀ p : ℕ, 0 < p → Measure.map (fun z : ℂ => flipSign y p * z) ν = ν)
    (hsign : ∀ (v : ℕ → ℂ) (n : ℕ), n ≠ 0 → n < (y + 1) ^ 2 →
      ext (fun p => flipSign y p * v p) n
        = (if n ∈ Nat.smoothNumbers (y + 1) then (1 : ℂ) else -1) * ext v n)
    (hbd : ∀ Y : ℕ → Ω → ℂ, IsIIDPrimeValues Y ν μ →
      IsBoundedRMF (fun ω => ext fun p => Y p ω) μ)
    (hmeasExt : ∀ n : ℕ, Measurable fun v : Nat.Primes → ℂ => ext (primeExtend v) n)
    (hcongr : ∀ {v w : ℕ → ℂ}, (∀ p, p.Prime → v p = w p) → ext v = ext w)
    (hxy : ⌊x⌋₊ < (y + 1) ^ 2) {q : ℝ} (hq0 : 0 < q) (hq1 : 2 * q ≤ 1) :
    (∫ ω, ‖randomSum (fun ω => ext fun p => X p ω) x ω
        - smoothPartial (fun ω => ext fun p => X p ω) y x ω‖ ^ (2 * q) ∂μ)
      ≤ 2 ^ (1 - 2 * q)
          * ∫ ω, ‖randomSum (fun ω => ext fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  have hr0 : (0 : ℝ) ≤ 2 * q := by linarith
  set X' : ℕ → Ω → ℂ := fun p ω => flipSign y p * X p ω with hX'def
  have hX' : IsIIDPrimeValues X' ν μ := hX.mul_const hc
  -- the flipped sum is `2B - S`, so the rough part `S - B` is `(S - S')/2`
  have hA : ∀ ω, randomSum (fun ω => ext fun p => X p ω) x ω
        - smoothPartial (fun ω => ext fun p => X p ω) y x ω
      = (randomSum (fun ω => ext fun p => X p ω) x ω
          - randomSum (fun ω => ext fun p => X' p ω) x ω) / 2 := by
    intro ω
    rw [hX'def, randomSum_flipSignOf hsign hxy ω]
    ring
  -- pointwise subadditivity
  have hpt : ∀ ω, ‖randomSum (fun ω => ext fun p => X p ω) x ω
        - smoothPartial (fun ω => ext fun p => X p ω) y x ω‖ ^ (2 * q)
      ≤ ((2 : ℝ) ^ (2 * q))⁻¹ * (‖randomSum (fun ω => ext fun p => X p ω) x ω‖ ^ (2 * q)
          + ‖randomSum (fun ω => ext fun p => X' p ω) x ω‖ ^ (2 * q)) := by
    intro ω
    rw [hA ω, norm_div, show ‖(2 : ℂ)‖ = 2 by simp,
      Real.div_rpow (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (norm_sub_rpow_le_add hr0 hq1)
      (inv_nonneg.2 (Real.rpow_nonneg (by norm_num) _))
  -- integrability
  have hb : ∀ (Y : ℕ → Ω → ℂ), IsIIDPrimeValues Y ν μ →
      Integrable (fun ω => ‖randomSum (fun ω => ext fun p => Y p ω) x ω‖
        ^ (2 * q)) μ := by
    intro Y hY
    refine (memLp_top_of_bound
      (((measurable_randomSum (hbd Y hY) x).norm.pow_const (2 * q)).aestronglyMeasurable)
      ((⌊x⌋₊ : ℝ) ^ (2 * q)) ?_).integrable le_top
    filter_upwards [norm_randomSum_le (hbd Y hY) x] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) hω hr0
  have hI1 := hb X hX
  have hI2 := hb X' hX'
  -- the law is preserved
  have hlaw : (∫ ω, ‖randomSum (fun ω => ext fun p => X' p ω) x ω‖ ^ (2 * q) ∂μ)
      = ∫ ω, ‖randomSum (fun ω => ext fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
    have h := hX.integral_comp_mul_const (c := flipSign y) hc
      (measurable_sumFunctionalOf hmeasExt x (2 * q))
    have hL : ∀ ω : Ω, sumFunctionalOf ext x (2 * q)
        (fun p : Nat.Primes => flipSign y (p : ℕ) * X (p : ℕ) ω)
        = ‖randomSum (fun ω => ext fun p => X' p ω) x ω‖ ^ (2 * q) :=
      fun ω => sumFunctionalOf_apply hcongr (fun n => flipSign y n * X n ω) x (2 * q)
    have hR : ∀ ω : Ω, sumFunctionalOf ext x (2 * q) (fun p : Nat.Primes => X (p : ℕ) ω)
        = ‖randomSum (fun ω => ext fun p => X p ω) x ω‖ ^ (2 * q) :=
      fun ω => sumFunctionalOf_apply hcongr (fun n => X n ω) x (2 * q)
    rw [integral_congr_ae (Filter.Eventually.of_forall hL),
      integral_congr_ae (Filter.Eventually.of_forall hR)] at h
    exact h
  -- assemble
  have hmono : (∫ ω, ‖randomSum (fun ω => ext fun p => X p ω) x ω
        - smoothPartial (fun ω => ext fun p => X p ω) y x ω‖ ^ (2 * q) ∂μ)
      ≤ ∫ ω, ((2 : ℝ) ^ (2 * q))⁻¹ * (‖randomSum (fun ω => ext fun p => X p ω) x ω‖ ^ (2 * q)
          + ‖randomSum (fun ω => ext fun p => X' p ω) x ω‖ ^ (2 * q)) ∂μ := by
    refine integral_mono ?_ ((hI1.add hI2).const_mul _) hpt
    refine (memLp_top_of_bound ?_ ((2 * ⌊x⌋₊ : ℝ) ^ (2 * q)) ?_).integrable le_top
    · exact (((measurable_randomSum (hbd X hX) x).sub
        (Finset.measurable_sum _ fun n _ => (hbd X hX).measurable_apply n)).norm.pow_const
        (2 * q)).aestronglyMeasurable
    · filter_upwards [norm_randomSum_le (hbd X hX) x,
      ae_norm_smoothPartial_le (hbd X hX) y x] with ω h1 h2
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      refine Real.rpow_le_rpow (norm_nonneg _) ?_ hr0
      exact le_trans (norm_sub_le _ _) (by linarith)
  rw [integral_const_mul, integral_add hI1 hI2, hlaw] at hmono
  have h2 : (2 : ℝ) ^ (1 - 2 * q) = ((2 : ℝ) ^ (2 * q))⁻¹ * 2 := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num)]
    ring
  rw [h2]
  linarith

/-! ### The rough part as a sum over its large prime

Below `(y+1)²` a rough number is a single prime: it has a prime factor above `y`, and a second
one would push it past `(y+1)²`.  So the general rough–smooth reindexing
`RMF.sum_Icc_eq_sum_rough_smooth`, the rough–smooth factorisation of the upper bound, specialises to
the factorisation `n = p·m` that the lower bound needs, and the inner smoothness filter becomes
vacuous because `m ≤ x/p < y+1`. -/

/-- A rough number below `(y+1)²` other than `1` is prime, and its prime is above `y`. -/
lemma prime_of_isRough_of_lt {y m : ℕ} (hm1 : m ≠ 1) (hm0 : m ≠ 0) (hrough : IsRough y m)
    (hlt : m < (y + 1) ^ 2) : m.Prime ∧ y < m := by
  have hmin : (Nat.minFac m).Prime := Nat.minFac_prime hm1
  have hdvd : Nat.minFac m ∣ m := Nat.minFac_dvd m
  have hminy : y < Nat.minFac m := (isRough_iff.1 hrough) _ hmin hdvd
  -- the cofactor is rough too, so it is `1` or at least `y+1`
  set c : ℕ := m / Nat.minFac m with hcdef
  have hmc : Nat.minFac m * c = m := Nat.mul_div_cancel' hdvd
  have hcdvd : c ∣ m := ⟨Nat.minFac m, ((mul_comm c (Nat.minFac m)).trans hmc).symm⟩
  have hcrough : IsRough y c := hrough.of_dvd hcdvd
  rcases eq_or_ne c 1 with hc1 | hc1
  · rw [hc1, mul_one] at hmc
    exact ⟨hmc ▸ hmin, hmc ▸ hminy⟩
  · exfalso
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, mul_zero] at hmc
      exact hm0 hmc.symm
    have hcmin : (Nat.minFac c).Prime := Nat.minFac_prime hc1
    have hcy : y < Nat.minFac c := (isRough_iff.1 hcrough) _ hcmin (Nat.minFac_dvd c)
    have hcge : y + 1 ≤ c := le_trans hcy (Nat.minFac_le (Nat.pos_of_ne_zero hc0))
    have hmge : y + 1 ≤ Nat.minFac m := hminy
    nlinarith [hmc, hcge, hmge, hlt]

omit [MeasurableSpace Ω] in
/-- **The factorisation `n = p·m`.**  For `⌊x⌋ < (y+1)²`, the part of `∑_{n≤x} f(n)` carried by
the numbers with a prime factor above `y` is `∑_{y<p≤x} f(p) · ∑_{m≤x/p} f(m)`, with no smoothness
constraint left on the inner sum.  Ordinary multiplicativity suffices — the two factors are
coprime. -/
theorem randomSum_sub_smoothPartial_eq {f : Ω → ArithmeticFunction ℂ} {x : ℝ} {y : ℕ}
    (hx : 1 ≤ x) (hxy : ⌊x⌋₊ < (y + 1) ^ 2) {ω : Ω} (hmul : (f ω).IsMultiplicative) :
    randomSum f x ω - smoothPartial f y x ω
      = ∑ p ∈ {p ∈ Finset.Icc 1 ⌊x⌋₊ | p.Prime ∧ y < p}, f ω p * randomSum f (x / p) ω := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hxlt : x < ((y : ℝ) + 1) ^ 2 := by
    have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (((y + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hxy
    push_cast at h2
    linarith
  have hfl1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  -- the rough–smooth factorisation, at this `y`
  have hsplit := sum_Icc_eq_sum_rough_smooth (f := f) y hx0 hmul
  -- the `m = 1` term is the smooth partial sum
  have hmem1 : (1 : ℕ) ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m} :=
    Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_refl 1, hfl1⟩, isRough_one y⟩
  have hone : (∑ k ∈ {k ∈ Finset.Icc 1 ⌊x / (1 : ℕ)⌋₊ | k ∈ Nat.smoothNumbers (y + 1)},
      f ω 1 * f ω k) = smoothPartial f y x ω := by
    rw [smoothPartial]
    simp only [Nat.cast_one, div_one, hmul.map_one, one_mul]
  -- the remaining `m` are exactly the primes above `y`
  have hset : ({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m}).erase 1
      = {p ∈ Finset.Icc 1 ⌊x⌋₊ | p.Prime ∧ y < p} := by
    ext m
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hm1, ⟨hm1', hm2⟩, hrough⟩
      have hmlt : m < (y + 1) ^ 2 := lt_of_le_of_lt hm2 hxy
      exact ⟨⟨hm1', hm2⟩, prime_of_isRough_of_lt hm1 (by omega) hrough hmlt⟩
    · rintro ⟨⟨hm1', hm2⟩, hprime, hy⟩
      refine ⟨hprime.ne_one, ⟨hm1', hm2⟩, isRough_iff.2 fun q hq hqd => ?_⟩
      rwa [(Nat.prime_dvd_prime_iff_eq hq hprime).1 hqd]
  -- and on those, the smoothness filter is vacuous
  have hinner : ∀ p ∈ {p ∈ Finset.Icc 1 ⌊x⌋₊ | p.Prime ∧ y < p},
      {k ∈ Finset.Icc 1 ⌊x / (p : ℕ)⌋₊ | k ∈ Nat.smoothNumbers (y + 1)}
        = Finset.Icc 1 ⌊x / (p : ℕ)⌋₊ := by
    intro p hp
    obtain ⟨hpIcc, hprime, hpy⟩ := Finset.mem_filter.1 hp
    have hpR : ((y : ℝ) + 1) ≤ (p : ℝ) := by exact_mod_cast hpy
    have hp0 : (0 : ℝ) < p := by linarith [Nat.cast_nonneg (α := ℝ) y]
    refine Finset.filter_true_of_mem fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    have hkR : (k : ℝ) ≤ x / p := le_trans (by exact_mod_cast hk2) (Nat.floor_le (by positivity))
    have hky : (k : ℝ) < (y : ℝ) + 1 := by
      rw [le_div_iff₀ hp0] at hkR
      nlinarith
    have hkyN : k ≤ y := by exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast hky)
    refine Nat.mem_smoothNumbers'.2 fun q hq hqd => ?_
    exact lt_of_le_of_lt (le_trans (Nat.le_of_dvd (by omega) hqd) hkyN) (by omega)
  -- assemble
  rw [randomSum, hsplit, ← Finset.add_sum_erase _ _ hmem1, hone, hset]
  rw [Finset.sum_congr rfl fun p hp => by rw [hinner p hp, ← Finset.mul_sum]]
  simp only [randomSum]
  ring

end RMF
