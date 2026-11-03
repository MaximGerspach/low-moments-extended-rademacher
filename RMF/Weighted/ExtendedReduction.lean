/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.LineSplit

/-!
# Extended Rademacher sums: the square classes

Proposition 3.1 of the paper, here for `x ≥ 1`.  Write
`n = s²m` with `m` squarefree.
Then `X^e(n) = X(m)`, as `X(p)² = 1` almost surely, and `m` has `⌊√(x/m)⌋` squares `s²m ≤ x`, so
almost surely

`x^{-1/2}∑_{n≤x} X^e(n) = ∑_{m≤x} X(m)/√m − x^{-1/2}∑_{m≤x} X(m){√(x/m)}`

(`RMF.ae_normalisedSum_compMultExtension_eq`; the last sum is `RMF.fracPartSum`).  With
`‖a+b‖^r ≤ 2(‖a‖^r + ‖b‖^r)` for `0 ≤ r ≤ 2` (`RMF.norm_add_rpow_le_two_mul`) this compares the
moments for `0 ≤ q ≤ 1`:

* `E|x^{-1/2}∑X^e|^{2q} ≤ 2E|S(x)|^{2q} + 2E|R(x)|^{2q}`
  (`RMF.integral_rpow_norm_normalisedSum_compMultExtension_le`);
* `½E|S(x)|^{2q} − E|R(x)|^{2q} ≤ E|x^{-1/2}∑X^e|^{2q}`
  (`RMF.le_integral_rpow_norm_normalisedSum_compMultExtension`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The fractional-part sum** `R(x) = x^{-1/2}∑_{m≤x} f(m){√(x/m)}`, what separates the extended
Rademacher sum from the weighted one. -/
noncomputable def fracPartSum (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f ω n * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ) / (Real.sqrt x : ℂ)

/-- **The squarefree kernel is unique.**  `s²m = t²m'` with `m`, `m'` squarefree and `s, t ≠ 0`
forces `m = m'` and `s = t`: each exponent of `m` is the parity of the same exponent of `s²m`. -/
lemma eq_and_eq_of_sq_mul_eq_sq_mul {s t m m' : ℕ} (hs : s ≠ 0) (ht : t ≠ 0)
    (hm : Squarefree m) (hm' : Squarefree m') (h : s ^ 2 * m = t ^ 2 * m') :
    m = m' ∧ s = t := by
  have hm0 := hm.ne_zero
  have hm0' := hm'.ne_zero
  have hmm : m = m' := by
    refine Nat.eq_of_factorization_eq hm0 hm0' fun p => ?_
    have h1 := congrArg (fun n => n.factorization p) h
    simp only [Nat.factorization_mul (pow_ne_zero 2 hs) hm0,
      Nat.factorization_mul (pow_ne_zero 2 ht) hm0', Nat.factorization_pow, Finsupp.coe_add,
      Pi.add_apply, Finsupp.smul_apply, smul_eq_mul] at h1
    have h2 := (Nat.squarefree_iff_factorization_le_one hm0).1 hm p
    have h3 := (Nat.squarefree_iff_factorization_le_one hm0').1 hm' p
    omega
  subst hmm
  exact ⟨rfl, Nat.pow_left_injective two_ne_zero
    (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hm0) h)⟩

/-- `s ≤ ⌊√(x/m)⌋` exactly when `s²m ≤ ⌊x⌋`: the squares below `x/m`. -/
lemma le_floor_sqrt_div_iff {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 0 < m) (s : ℕ) :
    s ≤ ⌊Real.sqrt (x / m)⌋₊ ↔ s ^ 2 * m ≤ ⌊x⌋₊ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Nat.le_floor_iff (Real.sqrt_nonneg _),
    Real.le_sqrt (Nat.cast_nonneg s) (div_nonneg hx hm'.le), le_div_iff₀ hm',
    Nat.le_floor_iff hx, Nat.cast_mul, Nat.cast_pow]

/-- **A square does not change `v^e`.**  If `v(p)² = 1` at the primes dividing `s`, then
`v^e(s²m) = v^e(m)`, which at a squarefree `m` is `v` extended over the squarefrees. -/
lemma compMultExtension_sq_mul_eq {v : ℕ → ℂ} {s m : ℕ} (hs : s ≠ 0) (hm : Squarefree m)
    (hv : ∀ p, p.Prime → p ∣ s → v p ^ 2 = 1) :
    compMultExtension v (s ^ 2 * m) = squarefreeExtension v m := by
  have hs2 : compMultExtension v s ^ 2 = 1 := by
    rw [compMultExtension_apply_of_ne_zero v hs, Finsupp.prod, Nat.support_factorization,
      ← Finset.prod_pow]
    refine Finset.prod_eq_one fun p hp => ?_
    rw [← pow_mul, mul_comm, pow_mul,
      hv p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp), one_pow]
  rw [compMultExtension_apply_mul v (pow_ne_zero 2 hs) hm.ne_zero, pow_two,
    compMultExtension_apply_mul v hs hs, ← pow_two, hs2, one_mul,
    compMultExtension_eq_squarefreeExtension_of_squarefree v hm]

/-- **The square classes.**  If `v(p)² = 1` at the primes `p ≤ x`, then
`∑_{n≤x} v^e(n) = ∑_{m≤x} v^{sf}(m)·⌊√(x/m)⌋`: every `n ≤ x` is `s²m` for exactly one squarefree
`m` and one `s ≥ 1`, and `m` has `⌊√(x/m)⌋` of them. -/
lemma sum_compMultExtension_eq_sum_squarefreeExtension_mul {v : ℕ → ℂ} {x : ℝ} (hx : 0 ≤ x)
    (hv : ∀ p, p.Prime → p ≤ ⌊x⌋₊ → v p ^ 2 = 1) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, compMultExtension v n
      = ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, squarefreeExtension v m * (⌊Real.sqrt (x / m)⌋₊ : ℂ) := by
  classical
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, compMultExtension v n
      = ∑ p ∈ ((Finset.Icc 1 ⌊x⌋₊).filter Squarefree).sigma
          (fun m => Finset.Icc 1 ⌊Real.sqrt (x / m)⌋₊), squarefreeExtension v p.1 := by
        symm
        refine Finset.sum_bij (fun p _ => p.2 ^ 2 * p.1) (fun p hp => ?_)
          (fun p hp p' hp' h => ?_) (fun n hn => ?_) (fun p hp => ?_)
        · obtain ⟨hm, hs⟩ := Finset.mem_sigma.1 hp
          obtain ⟨hm1, -⟩ := Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1
          obtain ⟨hs1, hsx⟩ := Finset.mem_Icc.1 hs
          refine Finset.mem_Icc.2 ⟨?_, (le_floor_sqrt_div_iff hx hm1 p.2).1 hsx⟩
          exact le_trans hm1
            (le_mul_of_one_le_left (Nat.zero_le _) (Nat.pos_of_ne_zero (pow_ne_zero 2 (by omega))))
        · obtain ⟨hm, hs⟩ := Finset.mem_sigma.1 hp
          obtain ⟨hm', hs'⟩ := Finset.mem_sigma.1 hp'
          have hs1 := (Finset.mem_Icc.1 hs).1
          have hs1' := (Finset.mem_Icc.1 hs').1
          obtain ⟨h1, h2⟩ := eq_and_eq_of_sq_mul_eq_sq_mul (by omega) (by omega)
            (Finset.mem_filter.1 hm).2 (Finset.mem_filter.1 hm').2 h
          exact Sigma.ext h1 (heq_of_eq h2)
        · obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.1 hn
          obtain ⟨a, b, ha, hb, hab, hasf⟩ := Nat.sq_mul_squarefree_of_pos (by omega : 0 < n)
          have hb1 : 1 ≤ b ^ 2 := Nat.pos_of_ne_zero (pow_ne_zero 2 hb.ne')
          have han : a ≤ n := by
            rw [← hab]
            exact le_mul_of_one_le_left (Nat.zero_le a) hb1
          have hbx : b ^ 2 * a ≤ ⌊x⌋₊ := by
            rw [hab]
            exact hnx
          exact ⟨⟨a, b⟩, Finset.mem_sigma.2 ⟨Finset.mem_filter.2
            ⟨Finset.mem_Icc.2 ⟨ha, han.trans hnx⟩, hasf⟩,
            Finset.mem_Icc.2 ⟨hb, (le_floor_sqrt_div_iff hx ha b).2 hbx⟩⟩, hab⟩
        · obtain ⟨hm, hs⟩ := Finset.mem_sigma.1 hp
          obtain ⟨hmI, hmsf⟩ := Finset.mem_filter.1 hm
          obtain ⟨hs1, hsx⟩ := Finset.mem_Icc.1 hs
          have hm1 := (Finset.mem_Icc.1 hmI).1
          have hle := (le_floor_sqrt_div_iff hx hm1 p.2).1 hsx
          refine (compMultExtension_sq_mul_eq (by omega) hmsf fun q hq hqs => hv q hq ?_).symm
          calc q ≤ p.2 := Nat.le_of_dvd (by omega) hqs
            _ ≤ p.2 ^ 2 := le_self_pow hs1 two_ne_zero
            _ ≤ p.2 ^ 2 * p.1 := le_mul_of_one_le_right (Nat.zero_le _) hm1
            _ ≤ ⌊x⌋₊ := hle
    _ = ∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter Squarefree,
          ∑ _s ∈ Finset.Icc 1 ⌊Real.sqrt (x / m)⌋₊, squarefreeExtension v m :=
        Finset.sum_sigma _ _ _
    _ = ∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter Squarefree,
          squarefreeExtension v m * (⌊Real.sqrt (x / m)⌋₊ : ℂ) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_comm]
    _ = ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, squarefreeExtension v m * (⌊Real.sqrt (x / m)⌋₊ : ℂ) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun m _ => ?_
        split_ifs with h
        · rfl
        · rw [squarefreeExtension_apply_of_not_squarefree v h, zero_mul]

/-- **The reduction identity** (from the proof of Proposition 3.1 of the paper).  Almost surely, for
`x ≥ 1`,

`x^{-1/2}∑_{n≤x} X^e(n) = ∑_{m≤x} X(m)/√m − x^{-1/2}∑_{m≤x} X(m){√(x/m)}`. -/
theorem ae_normalisedSum_compMultExtension_eq {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 1 ≤ x) :
    ∀ᵐ ω ∂μ, normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω
      = weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω
        - fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω := by
  have hx0 : 0 ≤ x := by linarith
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hmeas : Measurable fun z : ℂ => z ^ 2 = 1 :=
    measurableSet_setOf.1 ((measurable_id.pow_const 2) (measurableSet_singleton 1))
  have hprimes : ∀ p ∈ Finset.Icc 1 ⌊x⌋₊, ∀ᵐ ω ∂μ, p.Prime → X p ω ^ 2 = 1 := by
    intro p _
    by_cases hp : p.Prime
    · filter_upwards [((hX.hasLaw p hp).ae_iff hmeas).2 sq_eq_one_rademacherLaw] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hp
  filter_upwards [(Filter.eventually_all_finset _).2 hprimes] with ω hω
  have hv : ∀ p, p.Prime → p ≤ ⌊x⌋₊ → X p ω ^ 2 = 1 := fun p hp hpx =>
    hω p (Finset.mem_Icc.2 ⟨hp.one_lt.le, hpx⟩) hp
  rw [normalisedSum, randomSum, weightedRademacherSum, fracPartSum,
    sum_compMultExtension_eq_sum_squarefreeExtension_mul hx0 hv, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
  have hfl : (⌊Real.sqrt (x / m)⌋₊ : ℝ) = Real.sqrt (x / m) - Int.fract (Real.sqrt (x / m)) := by
    rw [natCast_floor_eq_intCast_floor (Real.sqrt_nonneg _), ← Int.self_sub_floor, sub_sub_cancel]
  have hdiv : Real.sqrt (x / m) / Real.sqrt x = (Real.sqrt m)⁻¹ := by
    rw [Real.sqrt_div' x (by linarith : (0 : ℝ) ≤ m), div_div, mul_comm, ← div_div, div_self hsx,
      one_div]
  rw [← Complex.ofReal_natCast, hfl, Complex.ofReal_sub, mul_sub, sub_div]
  congr 1
  rw [mul_div_assoc, ← Complex.ofReal_div, hdiv, Complex.ofReal_inv, div_eq_mul_inv]

/-- `‖a + b‖^r ≤ 2(‖a‖^r + ‖b‖^r)` for `0 ≤ r ≤ 2`: through `((‖a‖+‖b‖)²)^{r/2}`,
`(‖a‖+‖b‖)² ≤ 2‖a‖² + 2‖b‖²` and subadditivity of `t ↦ t^{r/2}`. -/
lemma norm_add_rpow_le_two_mul {a b : ℂ} {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    ‖a + b‖ ^ r ≤ 2 * (‖a‖ ^ r + ‖b‖ ^ r) := by
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hr : 0 ≤ r / 2 := by linarith
  have hr1 : r / 2 ≤ 1 := by linarith
  have hsq : ∀ t : ℝ, 0 ≤ t → (t ^ 2) ^ (r / 2) = t ^ r := fun t ht => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    congr 1
    push_cast
    ring
  calc ‖a + b‖ ^ r ≤ (‖a‖ + ‖b‖) ^ r := Real.rpow_le_rpow (norm_nonneg _) (norm_add_le a b) hr0
    _ = ((‖a‖ + ‖b‖) ^ 2) ^ (r / 2) := (hsq _ (by positivity)).symm
    _ ≤ (2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2) ^ (r / 2) :=
        Real.rpow_le_rpow (by positivity) (by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]) hr
    _ ≤ (2 * ‖a‖ ^ 2) ^ (r / 2) + (2 * ‖b‖ ^ 2) ^ (r / 2) :=
        Real.rpow_add_le_add_rpow (by positivity) (by positivity) hr hr1
    _ = 2 ^ (r / 2) * (‖a‖ ^ r + ‖b‖ ^ r) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg ‖a‖),
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg ‖b‖), hsq _ ha, hsq _ hb]
        ring
    _ ≤ 2 * (‖a‖ ^ r + ‖b‖ ^ r) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc (2 : ℝ) ^ (r / 2) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hr1
          _ = 2 := Real.rpow_one 2

/-- `½‖a‖^r − ‖b‖^r ≤ ‖a + b‖^r` for `0 ≤ r ≤ 2`, from `RMF.norm_add_rpow_le_two_mul` at
`(a + b) + (−b)`. -/
lemma half_mul_norm_rpow_sub_le {a b : ℂ} {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    1 / 2 * ‖a‖ ^ r - ‖b‖ ^ r ≤ ‖a + b‖ ^ r := by
  have h := norm_add_rpow_le_two_mul (a := a + b) (b := -b) hr0 hr2
  have e : a + b + -b = a := by ring
  rw [e, norm_neg] at h
  linarith

/-- `R(x)` is bounded, by `⌊x⌋/√x`, so its moments are integrable. -/
lemma integrable_rpow_norm_fracPartSum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω =>
      ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ r) μ := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hm : Measurable (fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x) :=
    Finset.measurable_sum _ fun n _ => ((hRa.measurable_apply n).mul_const _).div_const _
  refine (memLp_top_of_bound
    ((Real.continuous_rpow_const hr).measurable.comp hm.norm).aestronglyMeasurable
    (((⌊x⌋₊ : ℝ) * (Real.sqrt x)⁻¹) ^ r) ?_).integrable le_top
  filter_upwards [(Filter.eventually_all_finset (Finset.Icc 1 ⌊x⌋₊)).2
    fun n _ => hRa.norm_apply_le_one n] with ω hω
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) r)]
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖squarefreeExtension (fun p => X p ω) n
      * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ) / (Real.sqrt x : ℂ)‖ ≤ (Real.sqrt x)⁻¹ := by
    intro n hn
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
      div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.2 (Real.sqrt_nonneg _))
      (mul_le_one₀ (hω n hn) (Int.fract_nonneg _) (Int.fract_lt_one _).le)
  refine Real.rpow_le_rpow (norm_nonneg _) (le_trans (norm_sum_le _ _) ?_) hr
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖squarefreeExtension (fun p => X p ω) n
          * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ) / (Real.sqrt x : ℂ)‖
      ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, (Real.sqrt x)⁻¹ := Finset.sum_le_sum hterm
    _ = (⌊x⌋₊ : ℝ) * (Real.sqrt x)⁻¹ := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

/-- **The extended sum against the weighted one, from above** (Proposition 3.1 of the paper).
For `x ≥ 1` and `0 ≤ q ≤ 1`,

`E|x^{-1/2}∑_{n≤x} X^e(n)|^{2q} ≤ 2E|S(x)|^{2q} + 2E|R(x)|^{2q}`. -/
theorem integral_rpow_norm_normalisedSum_compMultExtension_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ 2 * (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ)
        + 2 * (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ) := by
  have hr0 : (0 : ℝ) ≤ 2 * q := by linarith
  have hr2 : 2 * q ≤ 2 := by linarith
  have hS := integrable_rpow_norm_weightedRademacherSum hX x hr0
  have hR := integrable_rpow_norm_fracPartSum hX x hr0
  calc (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ ∫ ω, (2 * ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) + 2 * ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q)) ∂μ := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) _)
          ((hS.const_mul 2).add (hR.const_mul 2)) ?_
        filter_upwards [ae_normalisedSum_compMultExtension_eq hX hx] with ω hω
        rw [hω, sub_eq_add_neg]
        have h := norm_add_rpow_le_two_mul
          (a := weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω)
          (b := -fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω) hr0 hr2
        rw [norm_neg] at h
        linarith
    _ = 2 * (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ)
        + 2 * (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ) := by
        rw [integral_add (hS.const_mul 2) (hR.const_mul 2), integral_const_mul, integral_const_mul]

/-- **The extended sum against the weighted one, from below** (Proposition 3.1 of the paper).
For `x ≥ 1` and `0 ≤ q ≤ 1`,

`½E|S(x)|^{2q} − E|R(x)|^{2q} ≤ E|x^{-1/2}∑_{n≤x} X^e(n)|^{2q}`. -/
theorem le_integral_rpow_norm_normalisedSum_compMultExtension {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    1 / 2 * (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ)
        - (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  have hr0 : (0 : ℝ) ≤ 2 * q := by linarith
  have hr2 : 2 * q ≤ 2 := by linarith
  have hS := integrable_rpow_norm_weightedRademacherSum hX x hr0
  have hR := integrable_rpow_norm_fracPartSum hX x hr0
  have hid := ae_normalisedSum_compMultExtension_eq hX hx
  have hmE : Measurable (normalisedSum (fun ω => compMultExtension fun p => X p ω) x) :=
    (Finset.measurable_sum _ fun n _ => hX.measurable_compMultExtension n).div_const _
  have hE : Integrable (fun ω =>
      ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q)) μ := by
    refine Integrable.mono' (g := fun ω =>
        2 * ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
          + 2 * ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q))
      ((hS.const_mul 2).add (hR.const_mul 2))
      ((Real.continuous_rpow_const hr0).measurable.comp hmE.norm).aestronglyMeasurable ?_
    filter_upwards [hid] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), hω, sub_eq_add_neg]
    have h := norm_add_rpow_le_two_mul
      (a := weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω)
      (b := -fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω) hr0 hr2
    rw [norm_neg] at h
    linarith
  calc 1 / 2 * (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ)
        - (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      = ∫ ω, (1 / 2
          * ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
          - ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)) ∂μ := by
        rw [integral_sub (hS.const_mul _) hR, integral_const_mul]
    _ ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
        refine integral_mono_ae ((hS.const_mul _).sub hR) hE ?_
        filter_upwards [hid] with ω hω
        rw [hω]
        have h := half_mul_norm_rpow_sub_le
          (a := weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω)
          (b := -fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω) hr0 hr2
        rwa [norm_neg, ← sub_eq_add_neg] at h

end RMF
