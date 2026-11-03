/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Main
import RMF.SecondMoment

/-!
# Khintchine's lower bound for a Steinhaus linear form

Harper's proof of Proposition 3 applies "the lower bound part of Khintchine's inequality", which is
not in Mathlib.

It is not needed.  For a *fixed* coefficient sequence `(c_p)` supported on a finite set of primes,
write `S = ∑_p c_p f(p)` and `M = ∑_p ‖c_p‖²`.  Two moments are available exactly, and Hölder
interpolation between them delivers the low moment:

* `E‖S‖² = M`, by orthogonality;
* `E‖S‖⁴ ≤ 2M²`, because `S² = ∑_{p,q} c_p c_q f(pq)` — the values are *completely*
  multiplicative — so orthogonality applies again, and the only thing left is that `pq = rt`
  forces `(r,t) ∈ {(p,q),(q,p)}`;
* `integral_rpow_le_mul_rpow` at `(a,b,c) = (2q,4,2)` with `α = 1/(2−q)`, `β = (1−q)/(2−q)`.

The result is `E‖S‖^{2q} ≥ 2^{−(1−q)} M^q`, which is what Harper takes from Khintchine, with an
absolute constant `≥ 2^{−1/3}` on `q ∈ [2/3,1]`.

The route through complete multiplicativity turns the four-fold character average into a single
application of `RMF.IsSteinhausRMF.orthogonality`, instead of a case analysis over four indices.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The linear form -/

/-- `∑_{p ∈ s} c_p f(p)`, the linear form Khintchine's inequality is about. -/
noncomputable def primeLinearForm (f : Ω → ArithmeticFunction ℂ) (s : Finset ℕ) (c : ℕ → ℂ)
    (ω : Ω) : ℂ :=
  ∑ p ∈ s, c p * f ω p

/-- **Two primes are determined by their product, up to order.**  This is the whole combinatorial
content of the fourth moment: the fibre of `(p,q) ↦ pq` over a product of two primes has at most
two points. -/
lemma prime_pair_eq_of_mul_eq {p q r t : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h : p * q = r * t) : (r = p ∧ t = q) ∨ (r = q ∧ t = p) := by
  have hrd : r ∣ p * q := ⟨t, h⟩
  rcases (Nat.Prime.dvd_mul hr).1 hrd with h1 | h1
  · have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).1 h1
    subst hrp
    exact Or.inl ⟨rfl, (Nat.eq_of_mul_eq_mul_left hr.pos h).symm⟩
  · have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).1 h1
    subst hrq
    refine Or.inr ⟨rfl, ?_⟩
    have hswap : r * p = r * t := by rw [← h]; ring
    exact (Nat.eq_of_mul_eq_mul_left hr.pos hswap).symm

/-! ### The second moment -/

omit [MeasurableSpace Ω] in
/-- The cross terms of the expanded square, with the coefficients pulled out. -/
lemma normSq_primeLinearForm_expand (f : Ω → ArithmeticFunction ℂ) (s : Finset ℕ) (c : ℕ → ℂ)
    (ω : Ω) :
    ((‖primeLinearForm f s c ω‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ s, ∑ q ∈ s, c p * (starRingEnd ℂ) (c q)
          * (f ω p * (starRingEnd ℂ) (f ω q)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', primeLinearForm, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by simp only [map_mul]; ring

/-- **What Khintchine's inequality asks of the law.**  At the primes the values are measurable,
unimodular and orthonormal, with integrable products; nothing else about the law is used.  **Both**
the Steinhaus and the Rademacher functions satisfy it: the squarefreeness side condition of
`RMF.IsRademacherRMF.orthogonality` is vacuous at primes. -/
structure IsOrthonormalAtPrimes (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω) : Prop where
  /-- Each value is measurable. -/
  measurable_apply : ∀ n : ℕ, Measurable fun ω => f ω n
  /-- At a prime the value is unimodular, almost surely. -/
  ae_norm_prime : ∀ p : ℕ, p.Prime → ∀ᵐ ω ∂μ, ‖f ω p‖ = 1
  /-- Products of values at primes are integrable. -/
  integrable_mul_conj_prime : ∀ p q : ℕ, p.Prime → q.Prime →
    Integrable (fun ω => f ω p * (starRingEnd ℂ) (f ω q)) μ
  /-- Values at distinct primes are orthogonal, and unit vectors at equal ones. -/
  orthogonality_prime : ∀ p q : ℕ, p.Prime → q.Prime →
    (∫ ω, f ω p * (starRingEnd ℂ) (f ω q) ∂μ) = if p = q then 1 else 0

/-- The Steinhaus function is orthonormal at the primes. -/
lemma IsSteinhausRMF.isOrthonormalAtPrimes {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsSteinhausRMF f μ) : IsOrthonormalAtPrimes f μ where
  measurable_apply := hf.measurable_apply
  ae_norm_prime _p hp := hf.norm_apply hp.ne_zero
  integrable_mul_conj_prime _p _q hp hq := hf.integrable_mul_conj hp.ne_zero hq.ne_zero
  orthogonality_prime _p _q hp hq := hf.orthogonality hp.ne_zero hq.ne_zero

/-- **The Rademacher function is orthonormal at the primes**, the squarefreeness condition being
vacuous there. -/
lemma IsRademacherRMF.isOrthonormalAtPrimes {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsRademacherRMF f μ) : IsOrthonormalAtPrimes f μ where
  measurable_apply := hf.measurable_apply
  ae_norm_prime p hp := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    have hmeasP : Measurable fun z : ℂ => ‖z‖ = 1 :=
      measurableSet_setOf.1 (measurable_norm (measurableSet_singleton 1))
    filter_upwards [((hX.hasLaw p hp).ae_iff hmeasP).2 norm_eq_one_rademacherLaw] with ω hω
    rwa [squarefreeExtension_apply_prime _ hp]
  integrable_mul_conj_prime p q _ _ := hf.integrable_mul_conj p q
  orthogonality_prime p q hp hq := by
    rw [hf.orthogonality hp.ne_zero hq.ne_zero]
    by_cases h : p = q
    · rw [if_pos ⟨h, hp.squarefree⟩, if_pos h]
    · rw [if_neg (fun hh => h hh.1), if_neg h]

/-- Each cross term is integrable. -/
lemma integrable_cross {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsOrthonormalAtPrimes f μ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (c : ℕ → ℂ) :
    Integrable (fun ω => c p * (starRingEnd ℂ) (c q)
      * (f ω p * (starRingEnd ℂ) (f ω q))) μ :=
  (hf.integrable_mul_conj_prime p q hp hq).const_mul _

/-- **The second moment.**  `E‖∑_p c_p f(p)‖² = ∑_p ‖c_p‖²`. -/
theorem integral_normSq_primeLinearForm {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsOrthonormalAtPrimes f μ) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) (c : ℕ → ℂ) :
    (∫ ω, ‖primeLinearForm f s c ω‖ ^ 2 ∂μ) = ∑ p ∈ s, ‖c p‖ ^ 2 := by
  have hcast : ((∫ ω, ‖primeLinearForm f s c ω‖ ^ 2 ∂μ : ℝ) : ℂ)
      = ((∑ p ∈ s, ‖c p‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [normSq_primeLinearForm_expand f s c]
    rw [integral_finsetSum _ fun p hp => integrable_finsetSum _ fun q hq =>
      integrable_cross hf (hs p hp) (hs q hq) c]
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [integral_finsetSum _ fun q hq =>
      integrable_cross hf (hs p hp) (hs q hq) c]
    have hterm : ∀ q ∈ s, (∫ ω, c p * (starRingEnd ℂ) (c q)
        * (f ω p * (starRingEnd ℂ) (f ω q)) ∂μ)
        = if p = q then c p * (starRingEnd ℂ) (c q) else 0 := by
      intro q hq
      rw [integral_const_mul, hf.orthogonality_prime p q (hs p hp) (hs q hq)]
      split <;> simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq _ _ _, if_pos hp,
      Complex.mul_conj']
  exact_mod_cast hcast

/-! ### The fourth moment

`S² = ∑_{p,q} c_p c_q f(pq)`, so orthogonality applies to it verbatim and the four-fold character
average never has to be computed by hand; the rest is the combinatorics of the fibre,
`RMF.prime_pair_eq_of_mul_eq`. -/

/-- **The square of the linear form is a linear form over pairwise products** (of two primes,
when `s` is a set of primes).  Complete multiplicativity is all it uses. -/
lemma sq_primeLinearForm {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) {s : Finset ℕ} (c : ℕ → ℂ) (ω : Ω) :
    primeLinearForm f s c ω ^ 2 = ∑ p ∈ s, ∑ q ∈ s, c p * c q * f ω (p * q) := by
  rw [primeLinearForm, sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [hf.apply_mul]
  ring

/-- **The fibre bound.**  For fixed `p, q` the pairs `(r,t)` with `rt = pq` contribute at most
`2‖c_p‖‖c_q‖`. -/
lemma fibre_sum_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (c : ℕ → ℂ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (∑ r ∈ s, ∑ t ∈ s, (if p * q = r * t then ‖c r‖ * ‖c t‖ else 0))
      ≤ 2 * (‖c p‖ * ‖c q‖) := by
  have hprod : (∑ r ∈ s, ∑ t ∈ s, (if p * q = r * t then ‖c r‖ * ‖c t‖ else 0))
      = ∑ z ∈ s ×ˢ s, (if p * q = z.1 * z.2 then ‖c z.1‖ * ‖c z.2‖ else 0) :=
    (Finset.sum_product' _ _ _).symm
  have hsub : {z ∈ s ×ˢ s | p * q = z.1 * z.2} ⊆ ({(p, q), (q, p)} : Finset (ℕ × ℕ)) := by
    intro z hz
    rw [Finset.mem_filter, Finset.mem_product] at hz
    obtain ⟨⟨h1, _⟩, h3⟩ := hz
    rcases prime_pair_eq_of_mul_eq hp hq (hs z.1 h1) h3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · simp [Finset.mem_insert, Prod.ext_iff, e1, e2]
    · simp [Finset.mem_insert, Prod.ext_iff, e1, e2]
  have hbound : ∀ z ∈ ({(p, q), (q, p)} : Finset (ℕ × ℕ)),
      ‖c z.1‖ * ‖c z.2‖ ≤ ‖c p‖ * ‖c q‖ := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz2
    · exact le_refl _
    · rw [Finset.mem_singleton] at hz2
      subst hz2
      exact le_of_eq (mul_comm _ _)
  have hcard : ({(p, q), (q, p)} : Finset (ℕ × ℕ)).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  calc (∑ r ∈ s, ∑ t ∈ s, (if p * q = r * t then ‖c r‖ * ‖c t‖ else 0))
      = ∑ z ∈ {z ∈ s ×ˢ s | p * q = z.1 * z.2}, ‖c z.1‖ * ‖c z.2‖ := by
        rw [hprod, Finset.sum_filter]
    _ ≤ ∑ z ∈ ({(p, q), (q, p)} : Finset (ℕ × ℕ)), ‖c z.1‖ * ‖c z.2‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => by positivity)
    _ ≤ ({(p, q), (q, p)} : Finset (ℕ × ℕ)).card • (‖c p‖ * ‖c q‖) :=
        Finset.sum_le_card_nsmul _ _ _ hbound
    _ ≤ 2 * (‖c p‖ * ‖c q‖) := by
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

/-- **The fourth moment.**  `E‖∑_p c_p f(p)‖⁴ ≤ 2(∑_p ‖c_p‖²)²`.

The exact value is `2M² - ∑_p ‖c_p‖⁴`; only the inequality is needed, and it is what the fibre
bound gives directly. -/
theorem integral_norm_pow_four_primeLinearForm_le {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hf : IsSteinhausRMF f μ) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) (c : ℕ → ℂ) :
    (∫ ω, ‖primeLinearForm f s c ω‖ ^ 4 ∂μ) ≤ 2 * (∑ p ∈ s, ‖c p‖ ^ 2) ^ 2 := by
  have hne : ∀ z ∈ s ×ˢ s, z.1 * z.2 ≠ 0 := by
    intro z hz
    rw [Finset.mem_product] at hz
    exact Nat.mul_ne_zero (hs z.1 hz.1).ne_zero (hs z.2 hz.2).ne_zero
  -- the square, as a single sum over pairs
  have hsq : ∀ ω, primeLinearForm f s c ω ^ 2
      = ∑ z ∈ s ×ˢ s, c z.1 * c z.2 * f ω (z.1 * z.2) := fun ω => by
    rw [sq_primeLinearForm hf c ω, ← Finset.sum_product']
  -- the fourth power, expanded
  have hexp : ∀ ω, ((‖primeLinearForm f s c ω‖ ^ 4 : ℝ) : ℂ)
      = ∑ z ∈ s ×ˢ s, ∑ w ∈ s ×ˢ s,
          c z.1 * c z.2 * (starRingEnd ℂ) (c w.1 * c w.2)
            * (f ω (z.1 * z.2) * (starRingEnd ℂ) (f ω (w.1 * w.2))) := by
    intro ω
    have h4 : (‖primeLinearForm f s c ω‖ ^ 4 : ℝ) = ‖primeLinearForm f s c ω ^ 2‖ ^ 2 := by
      rw [norm_pow]; ring
    rw [h4, Complex.ofReal_pow, ← Complex.mul_conj', hsq ω, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by simp only [map_mul]; ring
  -- integrate, using orthogonality on each cross term
  have hint : ∀ z ∈ s ×ˢ s, ∀ w ∈ s ×ˢ s,
      Integrable (fun ω => c z.1 * c z.2 * (starRingEnd ℂ) (c w.1 * c w.2)
        * (f ω (z.1 * z.2) * (starRingEnd ℂ) (f ω (w.1 * w.2)))) μ :=
    fun z hz w hw => (hf.integrable_mul_conj (hne z hz) (hne w hw)).const_mul _
  have hval : ((∫ ω, ‖primeLinearForm f s c ω‖ ^ 4 ∂μ : ℝ) : ℂ)
      = ∑ z ∈ s ×ˢ s, ∑ w ∈ s ×ˢ s,
          (if z.1 * z.2 = w.1 * w.2 then
            c z.1 * c z.2 * (starRingEnd ℂ) (c w.1 * c w.2) else 0) := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun z hz => integrable_finsetSum _ fun w hw => hint z hz w hw]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [integral_finsetSum _ fun w hw => hint z hz w hw]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [integral_const_mul, hf.orthogonality (hne z hz) (hne w hw)]
    split <;> simp
  -- pass to moduli
  have hnn : (0 : ℝ) ≤ ∫ ω, ‖primeLinearForm f s c ω‖ ^ 4 ∂μ :=
    integral_nonneg fun ω => by positivity
  have hmod : (∫ ω, ‖primeLinearForm f s c ω‖ ^ 4 ∂μ)
      ≤ ∑ z ∈ s ×ˢ s, ∑ w ∈ s ×ˢ s,
          (if z.1 * z.2 = w.1 * w.2 then ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0) := by
    have h1 : (∫ ω, ‖primeLinearForm f s c ω‖ ^ 4 ∂μ)
        = ‖((∫ ω, ‖primeLinearForm f s c ω‖ ^ 4 ∂μ : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    rw [h1, hval]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun z _ => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun w _ => ?_)
    split
    · rw [norm_mul, norm_mul, Complex.norm_conj, norm_mul]
    · simp
  refine le_trans hmod ?_
  -- the fibre bound, then the product of the two sums
  have hstep : ∀ z ∈ s ×ˢ s, (∑ w ∈ s ×ˢ s,
      (if z.1 * z.2 = w.1 * w.2 then ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0))
      ≤ 2 * (‖c z.1‖ ^ 2 * ‖c z.2‖ ^ 2) := by
    intro z hz
    rw [Finset.mem_product] at hz
    have hpull : (∑ w ∈ s ×ˢ s,
        (if z.1 * z.2 = w.1 * w.2 then ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0))
        = (‖c z.1‖ * ‖c z.2‖) * ∑ r ∈ s, ∑ t ∈ s,
            (if z.1 * z.2 = r * t then ‖c r‖ * ‖c t‖ else 0) := by
      rw [← Finset.sum_product', Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by split <;> simp
    rw [hpull]
    have hfib := fibre_sum_le hs c (hs z.1 hz.1) (hs z.2 hz.2)
    nlinarith [hfib, norm_nonneg (c z.1), norm_nonneg (c z.2),
      mul_nonneg (norm_nonneg (c z.1)) (norm_nonneg (c z.2))]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  have hprodsum : (∑ i ∈ s ×ˢ s, ‖c i.1‖ ^ 2 * ‖c i.2‖ ^ 2)
      = (∑ p ∈ s, ‖c p‖ ^ 2) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  rw [← Finset.mul_sum, hprodsum]

/-! ### Interpolation

Hölder at `(a,b,c) = (2q,4,2)`.  With `α = 1/(2-q)` and `β = (1-q)/(2-q)` one has `α+β = 1` and
`2qα + 4β = 2`, so the exact second moment and the fourth-moment bound between them force the low
moment from below. -/

/-- The linear form is bounded, so every power of it is integrable. -/
lemma integrable_norm_rpow_primeLinearForm {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsOrthonormalAtPrimes f μ) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) (c : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω => ‖primeLinearForm f s c ω‖ ^ r) μ := by
  have hmeas : Measurable fun ω => primeLinearForm f s c ω := by
    unfold primeLinearForm
    exact Finset.measurable_sum _ fun p _ => (hf.measurable_apply p).const_mul _
  have hae : ∀ᵐ ω ∂μ, ‖primeLinearForm f s c ω‖ ≤ ∑ p ∈ s, ‖c p‖ := by
    have hprimes : ∀ p ∈ s, ∀ᵐ ω ∂μ, ‖f ω p‖ = 1 := fun p hp =>
      hf.ae_norm_prime p (hs p hp)
    filter_upwards [(Filter.eventually_all_finset s).2 hprimes] with ω hω
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p hp => ?_)
    rw [norm_mul, hω p hp, mul_one]
  refine (memLp_top_of_bound (hmeas.norm.pow_const r).aestronglyMeasurable
    ((∑ p ∈ s, ‖c p‖) ^ r) ?_).integrable le_top
  filter_upwards [hae] with ω hb
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) r)]
  exact Real.rpow_le_rpow (norm_nonneg _) hb hr

/-- The Steinhaus fourth-moment bound in the `rpow` form that
`RMF.khintchine_lower_of_fourth_of_pos` consumes. -/
lemma integral_norm_rpow_four_primeLinearForm_le {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hf : IsSteinhausRMF f μ) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) (c : ℕ → ℂ) :
    (∫ ω, ‖primeLinearForm f s c ω‖ ^ (4 : ℝ) ∂μ) ≤ 2 * (∑ p ∈ s, ‖c p‖ ^ 2) ^ 2 := by
  have heq : (∫ ω, ‖primeLinearForm f s c ω‖ ^ (4 : ℝ) ∂μ)
      = ∫ ω, ‖primeLinearForm f s c ω‖ ^ 4 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [heq]
  exact integral_norm_pow_four_primeLinearForm_le hf hs c

/-- **Khintchine's lower bound for fixed coefficients**, with the fourth-moment constant carried,
for `0 < q ≤ 1`: `E‖∑_p c_p f(p)‖^{2q} ≥ K^{-(1-q)} (∑_p ‖c_p‖²)^q` when the fourth moment is at
most `K(∑_p‖c_p‖²)²`.  Hölder interpolates the exact second moment against the fourth at
`α = 1/(2-q)`, `β = (1-q)/(2-q)`.  `K` is carried because the Rademacher fourth moment
(`RMF.integral_norm_pow_four_primeLinearForm_le_sqfree`) has constant `3`, the Steinhaus one `2`.
-/
theorem khintchine_lower_of_fourth_of_pos {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsOrthonormalAtPrimes f μ) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) (c : ℕ → ℂ) {K : ℝ} (hK0 : 0 < K)
    (hfour : (∫ ω, ‖primeLinearForm f s c ω‖ ^ (4 : ℝ) ∂μ)
      ≤ K * (∑ p ∈ s, ‖c p‖ ^ 2) ^ 2)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    K ^ (-(1 - q)) * (∑ p ∈ s, ‖c p‖ ^ 2) ^ q
      ≤ ∫ ω, ‖primeLinearForm f s c ω‖ ^ (2 * q) ∂μ := by
  have h2q : (0 : ℝ) < 2 - q := by linarith
  set α : ℝ := 1 / (2 - q) with hαdef
  set β : ℝ := (1 - q) / (2 - q) with hβdef
  have hα0 : (0 : ℝ) < α := by rw [hαdef]; positivity
  have hβ0 : (0 : ℝ) ≤ β := by rw [hβdef]; positivity
  have hαβ : α + β = 1 := by rw [hαdef, hβdef]; field_simp; ring
  have habc : 2 * q * α + 4 * β = 2 := by rw [hαdef, hβdef]; field_simp; ring
  set M : ℝ := ∑ p ∈ s, ‖c p‖ ^ 2 with hMdef
  set A : ℝ := ∫ ω, ‖primeLinearForm f s c ω‖ ^ (2 * q) ∂μ with hAdef
  have hM0 : (0 : ℝ) ≤ M := Finset.sum_nonneg fun p _ => by positivity
  have hA0 : (0 : ℝ) ≤ A := integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  -- the exact second moment, as an `rpow`
  have hcast2 : (∫ ω, ‖primeLinearForm f s c ω‖ ^ (2 : ℝ) ∂μ) = M := by
    rw [hMdef, ← integral_normSq_primeLinearForm hf hs c]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h40 : (0 : ℝ) ≤ ∫ ω, ‖primeLinearForm f s c ω‖ ^ (4 : ℝ) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  -- Hölder
  have hhold := integral_rpow_le_mul_rpow (S := fun ω => primeLinearForm f s c ω) (μ := μ)
    hα0.le hβ0 hαβ habc (by norm_num)
    (integrable_norm_rpow_primeLinearForm hf hs c (by linarith : (0 : ℝ) ≤ 2 * q))
    (integrable_norm_rpow_primeLinearForm hf hs c (by norm_num : (0 : ℝ) ≤ 4))
    (integrable_norm_rpow_primeLinearForm hf hs c (by norm_num : (0 : ℝ) ≤ 2))
  rw [hcast2] at hhold
  have hstep : M ≤ A ^ α * (K * M ^ 2) ^ β :=
    le_trans hhold (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow h40 hfour hβ0) (Real.rpow_nonneg hA0 α))
  -- conclude
  rcases eq_or_lt_of_le hM0 with hM | hM
  · rw [← hM, Real.zero_rpow hq0.ne', mul_zero]
    exact hA0
  · by_contra hcon
    push Not at hcon
    have hKa : (K ^ (-(1 - q)) * M ^ q) ^ α = K ^ (-β) * M ^ (q * α) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hK0.le _) (Real.rpow_nonneg hM0 _),
        ← Real.rpow_mul hK0.le, ← Real.rpow_mul hM0]
      congr 2
      rw [hαdef, hβdef]
      field_simp
    have h2M : (K * M ^ 2) ^ β = K ^ β * M ^ (2 * β) := by
      rw [Real.mul_rpow hK0.le (by positivity), ← Real.rpow_natCast M 2,
        ← Real.rpow_mul hM0]
      norm_num
    have hlt : A ^ α < (K ^ (-(1 - q)) * M ^ q) ^ α := Real.rpow_lt_rpow hA0 hcon hα0
    have hsum : q * α + 2 * β = 1 := by rw [hαdef, hβdef]; field_simp; ring
    have hfin : A ^ α * (K * M ^ 2) ^ β < M := by
      calc A ^ α * (K * M ^ 2) ^ β
          < (K ^ (-β) * M ^ (q * α)) * (K ^ β * M ^ (2 * β)) := by
            rw [← hKa, ← h2M]
            exact mul_lt_mul_of_pos_right hlt (by positivity)
        _ = M := by
            rw [show K ^ (-β) * M ^ (q * α) * (K ^ β * M ^ (2 * β))
                = (K ^ (-β) * K ^ β) * (M ^ (q * α) * M ^ (2 * β)) by ring,
              ← Real.rpow_add hK0, ← Real.rpow_add hM,
              show -β + β = (0 : ℝ) by ring, Real.rpow_zero, one_mul, hsum, Real.rpow_one]
    linarith

/-! ### From fixed coefficients to independent ones

The coefficients Harper's proof actually uses are random — `c_p = ∑_{m≤x/p} f(m)` — but they are
built from the *small* primes, and the multipliers `f(p)` from the *large* ones, so the two are
independent.

The transfer goes through the joint law: independence makes it a product, Fubini splits the
integral, and on each fibre the coefficients are *constants*, so the fixed-coefficient bound
applies verbatim.  The lemma below is that step, isolated from anything about Steinhaus
variables. -/

/-- **Fibrewise transfer.**  If `W` and `Z` are independent, and on every fibre `y` the bound
`G y ≤ ∫ F y (Z ω) dμ` holds with `y` *frozen*, then it holds with `y` replaced by `W ω`.

The point is that `∫ F y (Z ω) dμ` is the constant-coefficient statement — `y` does not move with
`ω` — and independence is exactly what lets `y` be frozen inside the integral. -/
theorem integral_le_of_indepFun_fibrewise {Ω γ δ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace γ] [MeasurableSpace δ] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : Ω → γ} {Z : Ω → δ} (hW : Measurable W) (hZ : Measurable Z)
    (hind : ProbabilityTheory.IndepFun W Z μ) {G : γ → ℝ} {F : γ → δ → ℝ}
    (hGm : StronglyMeasurable G) (hFm : StronglyMeasurable fun p : γ × δ => F p.1 p.2)
    (hFi : Integrable (fun ω => F (W ω) (Z ω)) μ)
    (hGi : Integrable (fun ω => G (W ω)) μ)
    (hfib : ∀ y, G y ≤ ∫ ω, F y (Z ω) ∂μ) :
    (∫ ω, G (W ω) ∂μ) ≤ ∫ ω, F (W ω) (Z ω) ∂μ := by
  haveI : IsProbabilityMeasure (μ.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  haveI : IsProbabilityMeasure (μ.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hpair : Measurable fun ω => (W ω, Z ω) := hW.prodMk hZ
  have hmap : μ.map (fun ω => (W ω, Z ω)) = (μ.map W).prod (μ.map Z) :=
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable
      hZ.aemeasurable).1 hind
  have hG : (∫ ω, G (W ω) ∂μ) = ∫ y, G y ∂(μ.map W) :=
    (integral_map hW.aemeasurable hGm.aestronglyMeasurable).symm
  have hFprod : Integrable (fun p : γ × δ => F p.1 p.2) ((μ.map W).prod (μ.map Z)) := by
    rw [← hmap, integrable_map_measure hFm.aestronglyMeasurable hpair.aemeasurable]
    exact hFi
  have hF : (∫ ω, F (W ω) (Z ω) ∂μ) = ∫ y, (∫ z, F y z ∂(μ.map Z)) ∂(μ.map W) := by
    rw [← integral_prod _ hFprod, ← hmap,
      integral_map hpair.aemeasurable hFm.aestronglyMeasurable]
  have hfib' : ∀ y, G y ≤ ∫ z, F y z ∂(μ.map Z) := by
    intro y
    have hmy : AEStronglyMeasurable (fun z => F y z) (μ.map Z) :=
      (hFm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    rw [integral_map hZ.aemeasurable hmy]
    exact hfib y
  have hGmap : Integrable G (μ.map W) := by
    rw [integrable_map_measure hGm.aestronglyMeasurable hW.aemeasurable]
    exact hGi
  rw [hG, hF]
  exact integral_mono hGmap hFprod.integral_prod_left hfib'

/-- **Khintchine's lower bound with independent random coefficients**, for `0 < q ≤ 1`:
`E‖∑_p C(W)_p f(p)‖^{2q} ≥ K^{-(1-q)} E[(∑_p ‖C(W)_p‖²)^q]` whenever the coefficient data `W` is
independent of the values `f(p)`, `p ∈ s`.  The bound `B` on the coefficients makes both sides
integrable; in Harper's application `C(W)_p = ∑_{m ≤ x/p} f(m)` and `B = x` will do.  Harper's range
`[2/3,1]` is `RMF.khintchine_lower_indep`. -/
theorem khintchine_lower_indep_of_pos {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsOrthonormalAtPrimes f μ) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime)
    {γ : Type*} [MeasurableSpace γ] {W : Ω → γ} (hW : Measurable W)
    {C : γ → ℕ → ℂ} (hC : ∀ p, Measurable fun y => C y p)
    {K : ℝ} (hK0 : 0 < K)
    (hfour : ∀ y : γ, (∫ ω, ‖primeLinearForm f s (C y) ω‖ ^ (4 : ℝ) ∂μ)
      ≤ K * (∑ p ∈ s, ‖C y p‖ ^ 2) ^ 2)
    {B : ℝ} (hB : ∀ y, ∀ p ∈ s, ‖C y p‖ ≤ B)
    (hind : ProbabilityTheory.IndepFun W (fun ω n => if n ∈ s then f ω n else 0) μ)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    K ^ (-(1 - q)) * ∫ ω, (∑ p ∈ s, ‖C (W ω) p‖ ^ 2) ^ q ∂μ
      ≤ ∫ ω, ‖∑ p ∈ s, C (W ω) p * f ω p‖ ^ (2 * q) ∂μ := by
  set Z : Ω → (ℕ → ℂ) := fun ω n => if n ∈ s then f ω n else 0 with hZdef
  set F : γ → (ℕ → ℂ) → ℝ := fun y z => ‖∑ p ∈ s, C y p * z p‖ ^ (2 * q) with hFdef
  set G : γ → ℝ := fun y => K ^ (-(1 - q)) * (∑ p ∈ s, ‖C y p‖ ^ 2) ^ q with hGdef
  have hZm : Measurable Z := by
    rw [hZdef]
    refine measurable_pi_lambda _ fun n => ?_
    by_cases hn : n ∈ s
    · simpa [hn] using hf.measurable_apply n
    · simp [hn]
  -- `F` and `G` are measurable
  have hlin : Measurable fun p : γ × (ℕ → ℂ) => ∑ r ∈ s, C p.1 r * p.2 r :=
    Finset.measurable_sum _ fun r _ =>
      ((hC r).comp measurable_fst).mul ((measurable_pi_apply r).comp measurable_snd)
  have hFm : StronglyMeasurable fun p : γ × (ℕ → ℂ) => F p.1 p.2 :=
    (hlin.norm.pow_const (2 * q)).stronglyMeasurable
  have hGm : StronglyMeasurable G :=
    ((Finset.measurable_sum _ fun r _ =>
      ((hC r).norm.pow_const 2)).pow_const q).const_mul _ |>.stronglyMeasurable
  -- on the fibre the coefficients are constants, so this is the fixed-coefficient bound
  have hfibeq : ∀ y ω, F y (Z ω) = ‖primeLinearForm f s (C y) ω‖ ^ (2 * q) := by
    intro y ω
    have hsum : (∑ p ∈ s, C y p * Z ω p) = ∑ p ∈ s, C y p * f ω p :=
      Finset.sum_congr rfl fun p hp => by simp [hZdef, hp]
    simp only [hFdef, primeLinearForm]
    rw [hsum]
  have hfib : ∀ y, G y ≤ ∫ ω, F y (Z ω) ∂μ := by
    intro y
    simp_rw [hfibeq y]
    exact khintchine_lower_of_fourth_of_pos hf hs (C y) hK0 (hfour y) hq0 hq1
  -- both sides are bounded
  have hone : ∀ᵐ ω ∂μ, ∀ p ∈ s, ‖f ω p‖ = 1 :=
    (Filter.eventually_all_finset s).2 fun p hp => hf.ae_norm_prime p (hs p hp)
  have hFb : ∀ᵐ ω ∂μ, ‖F (W ω) (Z ω)‖ ≤ (s.card * B) ^ (2 * q) := by
    filter_upwards [hone] with ω hω
    rw [hfibeq, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    refine Real.rpow_le_rpow (norm_nonneg _) ?_ (by linarith)
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ => B) fun p hp => ?_) ?_
    · rw [norm_mul, hω p hp, mul_one]
      exact hB (W ω) p hp
    · rw [Finset.sum_const, nsmul_eq_mul]
  have hGb : ∀ᵐ ω ∂μ, ‖G (W ω)‖ ≤ K ^ (-(1 - q)) * (s.card * B ^ 2) ^ q := by
    filter_upwards with ω
    have hsum0 : (0 : ℝ) ≤ ∑ p ∈ s, ‖C (W ω) p‖ ^ 2 :=
      Finset.sum_nonneg fun p _ => by positivity
    rw [hGdef, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hK0.le _)
        (Real.rpow_nonneg hsum0 q))]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hsum0 ?_ hq0.le)
      (Real.rpow_nonneg hK0.le _)
    refine le_trans (Finset.sum_le_sum (g := fun _ => B ^ 2) fun p hp => ?_) ?_
    · exact pow_le_pow_left₀ (norm_nonneg _) (hB (W ω) p hp) 2
    · rw [Finset.sum_const, nsmul_eq_mul]
  have hFi : Integrable (fun ω => F (W ω) (Z ω)) μ := by
    refine (memLp_top_of_bound ?_ _ hFb).integrable le_top
    exact (hFm.comp_measurable (hW.prodMk hZm)).aestronglyMeasurable
  have hGi : Integrable (fun ω => G (W ω)) μ :=
    (memLp_top_of_bound ((hGm.comp_measurable hW).aestronglyMeasurable) _ hGb).integrable le_top
  have hmain := integral_le_of_indepFun_fibrewise hW hZm hind hGm hFm hFi hGi hfib
  -- unwind
  have hL : (∫ ω, G (W ω) ∂μ)
      = K ^ (-(1 - q)) * ∫ ω, (∑ p ∈ s, ‖C (W ω) p‖ ^ 2) ^ q ∂μ := by
    rw [hGdef, integral_const_mul]
  have hR : (∫ ω, F (W ω) (Z ω) ∂μ)
      = ∫ ω, ‖∑ p ∈ s, C (W ω) p * f ω p‖ ^ (2 * q) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [hfibeq, primeLinearForm]
  rw [hL, hR] at hmain
  exact hmain

/-- **Khintchine's lower bound with independent coefficients, on Harper's range** `q ∈ [2/3,1]`:
the case of `RMF.khintchine_lower_indep_of_pos` that Harper's Proposition 3 uses. -/
theorem khintchine_lower_indep {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsOrthonormalAtPrimes f μ) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime)
    {γ : Type*} [MeasurableSpace γ] {W : Ω → γ} (hW : Measurable W)
    {C : γ → ℕ → ℂ} (hC : ∀ p, Measurable fun y => C y p)
    {K : ℝ} (hK0 : 0 < K)
    (hfour : ∀ y : γ, (∫ ω, ‖primeLinearForm f s (C y) ω‖ ^ (4 : ℝ) ∂μ)
      ≤ K * (∑ p ∈ s, ‖C y p‖ ^ 2) ^ 2)
    {B : ℝ} (hB : ∀ y, ∀ p ∈ s, ‖C y p‖ ≤ B)
    (hind : ProbabilityTheory.IndepFun W (fun ω n => if n ∈ s then f ω n else 0) μ)
    {q : ℝ} (hq23 : 2 / 3 ≤ q) (hq1 : q ≤ 1) :
    K ^ (-(1 - q)) * ∫ ω, (∑ p ∈ s, ‖C (W ω) p‖ ^ 2) ^ q ∂μ
      ≤ ∫ ω, ‖∑ p ∈ s, C (W ω) p * f ω p‖ ^ (2 * q) ∂μ :=
  khintchine_lower_indep_of_pos hf hs hW hC hK0 hfour hB hind (by linarith) hq1

end RMF
