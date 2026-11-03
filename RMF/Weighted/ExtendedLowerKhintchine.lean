/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.LowerKhintchine

/-!
# The extended sum's lower bound: symmetrisation and Khintchine

For the extended Rademacher function `X^e = RMF.compMultExtension X`, `0 < q ≤ ½` and `x ≥ 1`,

`3^{-(1-q)}·E[(∑_{y<p≤x} |∑_{m≤x/p} X^e(m)|²)^q] ≤ 2^{1-2q}·E|∑_{n≤x} X^e(n)|^{2q}`

(`RMF.khintchine_rough_extended`), for `⌊x⌋ < (y+1)²`: the symmetrisation and Khintchine steps of
the proof of Proposition 4.3 of the paper, as in `RMF.khintchine_rough_weighted`.

## What changes against the weighted sum

`X^e` is not `RMF.IsBoundedRMF`: `E|∑_{n∈s} X^e(n)|²` counts the pairs with `mn` a square, which
can exceed `#s`.  The symmetrisation `RMF.integral_rough_le_of_le_oneOf` asks for that structure
but uses only its measurability and `|f| ≤ 1`, so it is restated with those two hypotheses
(`RMF.integral_rough_le_of_le_oneOf'`, the same proof).  Khintchine is untouched: the linear form
is in the values at the primes, where `X^e` and `X` agree.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Boundedness without orthogonality -/

/-- Values bounded by one almost surely give partial sums bounded by the number of terms.
`RMF.norm_randomSum_le` with the boundedness hypothesis it actually uses. -/
lemma norm_randomSum_le_of_ae {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1) (x : ℝ) :
    ∀ᵐ ω ∂μ, ‖randomSum f x ω‖ ≤ ⌊x⌋₊ := by
  have hall : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 := fun n _ => hf n
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun n hn => hω n hn) ?_
  simp

/-- `RMF.ae_norm_smoothPartial_le` with the boundedness hypothesis it actually uses. -/
lemma ae_norm_smoothPartial_le_of_ae {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1) (y : ℕ) (x : ℝ) :
    ∀ᵐ ω ∂μ, ‖smoothPartial f y x ω‖ ≤ ⌊x⌋₊ := by
  have hall : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 := fun n _ => hf n
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

/-- The completely multiplicative extension of values bounded by one is bounded by one, almost
surely. -/
lemma IsIIDPrimeValues.ae_norm_compMultExtension_le_one {X : ℕ → Ω → ℂ} {ν : Measure ℂ}
    {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) (n : ℕ) :
    ∀ᵐ ω ∂μ, ‖compMultExtension (fun p => X p ω) n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact Filter.Eventually.of_forall fun ω => by simp
  · have hmeasP : Measurable fun z : ℂ => ‖z‖ ≤ 1 :=
      measurableSet_setOf.1 (measurableSet_le measurable_norm measurable_const)
    filter_upwards [(Filter.eventually_all_finset n.primeFactors).2 fun p hp =>
      ((hX.hasLaw p (Nat.prime_of_mem_primeFactors hp)).ae_iff hmeasP).2 hν] with ω hω
    rw [compMultExtension_apply_of_ne_zero _ hn, Finsupp.prod, Nat.support_factorization,
      norm_prod]
    exact Finset.prod_le_one (fun p _ => norm_nonneg _) fun p hp => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hω p hp)

/-! ### Symmetrisation -/

/-- **Symmetrisation for `2q ≤ 1`, without orthogonality.**
`RMF.integral_rough_le_of_le_oneOf` with `RMF.IsBoundedRMF` replaced by the two of its fields the
proof uses: measurability and `|f| ≤ 1` almost surely.  The proof is the original's. -/
theorem integral_rough_le_of_le_oneOf' {ext : (ℕ → ℂ) → ArithmeticFunction ℂ}
    {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsIIDPrimeValues X ν μ) {x : ℝ} {y : ℕ}
    (hc : ∀ p : ℕ, 0 < p → Measure.map (fun z : ℂ => flipSign y p * z) ν = ν)
    (hsign : ∀ (v : ℕ → ℂ) (n : ℕ), n ≠ 0 → n < (y + 1) ^ 2 →
      ext (fun p => flipSign y p * v p) n
        = (if n ∈ Nat.smoothNumbers (y + 1) then (1 : ℂ) else -1) * ext v n)
    (hmeas : ∀ Y : ℕ → Ω → ℂ, IsIIDPrimeValues Y ν μ →
      ∀ n : ℕ, Measurable fun ω => ext (fun p => Y p ω) n)
    (hbd : ∀ Y : ℕ → Ω → ℂ, IsIIDPrimeValues Y ν μ →
      ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖ext (fun p => Y p ω) n‖ ≤ 1)
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
      (((Finset.measurable_sum _ fun n _ => hmeas Y hY n).norm.pow_const
        (2 * q)).aestronglyMeasurable)
      ((⌊x⌋₊ : ℝ) ^ (2 * q)) ?_).integrable le_top
    filter_upwards [norm_randomSum_le_of_ae (hbd Y hY) x] with ω hω
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
    · exact (((Finset.measurable_sum _ fun n _ => hmeas X hX n).sub
        (Finset.measurable_sum _ fun n _ => hmeas X hX n)).norm.pow_const
        (2 * q)).aestronglyMeasurable
    · filter_upwards [norm_randomSum_le_of_ae (hbd X hX) x,
      ae_norm_smoothPartial_le_of_ae (hbd X hX) y x] with ω h1 h2
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      refine Real.rpow_le_rpow (norm_nonneg _) ?_ hr0
      exact le_trans (norm_sub_le _ _) (by linarith)
  rw [integral_const_mul, integral_add hI1 hI2, hlaw] at hmono
  have h2 : (2 : ℝ) ^ (1 - 2 * q) = ((2 : ℝ) ^ (2 * q))⁻¹ * 2 := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num)]
    ring
  rw [h2]
  linarith

/-- **Symmetrisation for the extended sum**: the `RMF.compMultExtension` instance of
`RMF.integral_rough_le_of_le_oneOf'`, for `0 < q ≤ ½`. -/
theorem integral_rough_le_extended {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} {y : ℕ} (hxy : ⌊x⌋₊ < (y + 1) ^ 2)
    {q : ℝ} (hq0 : 0 < q) (hq1 : 2 * q ≤ 1) :
    (∫ ω, ‖randomSum (fun ω => compMultExtension fun p => X p ω) x ω
        - smoothPartial (fun ω => compMultExtension fun p => X p ω) y x ω‖ ^ (2 * q) ∂μ)
      ≤ 2 ^ (1 - 2 * q)
          * ∫ ω, ‖randomSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ :=
  integral_rough_le_of_le_oneOf' hX
    (fun p _ => map_mul_left_rademacherLaw (flipSign_eq_one_or_neg_one y p))
    (fun _ _ hn hn2 => compMultExtension_flipSign hn hn2)
    (fun _ hY n => hY.measurable_compMultExtension n)
    (fun _ hY n => hY.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n)
    measurable_compMultExtension_primeExtend (fun h => compMultExtension_congr_primes h)
    hxy hq0 hq1

/-! ### Khintchine -/

/-- **Symmetrisation and Khintchine for the extended sum.**  For `x ≥ 1`, `⌊x⌋ < (y+1)²` and
`0 < q ≤ ½`,
`3^{-(1-q)}·E[(∑_{y<p≤x} |∑_{m≤x/p} X^e(m)|²)^q] ≤ 2^{1-2q}·E|∑_{n≤x} X^e(n)|^{2q}`.

Symmetrisation (`RMF.integral_rough_le_extended`) and Khintchine conditionally on the primes up to
`y`, with the coefficients `∑_{m≤x/p} X^e(m)` of the large primes (`RMF.roughCoeffOf`). -/
theorem khintchine_rough_extended {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} {y : ℕ} (hx : 1 ≤ x)
    (hxy : ⌊x⌋₊ < (y + 1) ^ 2) {q : ℝ} (hq0 : 0 < q) (hq1 : 2 * q ≤ 1) :
    (3 : ℝ) ^ (-(1 - q)) * ∫ ω, (∑ p ∈ largePrimeSet y ⌊x⌋₊,
        ‖randomSum (fun ω => compMultExtension fun r => X r ω) (x / p) ω‖ ^ 2) ^ q ∂μ
      ≤ 2 ^ (1 - 2 * q) * ∫ ω, ‖randomSum
          (fun ω => compMultExtension fun r => X r ω) x ω‖ ^ (2 * q) ∂μ := by
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun r => X r ω with hfdef
  set g : Ω → ArithmeticFunction ℂ := fun ω => compMultExtension fun r => X r ω with hgdef
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set s : Finset ℕ := largePrimeSet y ⌊x⌋₊ with hsdef
  have hs : ∀ p ∈ s, Nat.Prime p := fun p hp => (mem_largePrimeSet.1 hp).2
  -- the two data maps
  set W : Ω → (ℕ → ℂ) := fun ω =>
    primeRestrict (smallPrimes y) fun i : smallPrimes y => X ((i : Nat.Primes) : ℕ) ω with hWdef
  have hW : Measurable W :=
    (measurable_primeRestrict _).comp
      (measurable_pi_lambda _ fun i => hX.measurable ((i : Nat.Primes) : ℕ)
        (i : Nat.Primes).2)
  have hZ : (fun ω n => if n ∈ s then f ω n else 0)
      = fun ω => primeRestrict (largePrimes y ⌊x⌋₊)
          fun i : largePrimes y ⌊x⌋₊ => X ((i : Nat.Primes) : ℕ) ω := by
    funext ω
    rw [primeRestrict_largePrimes_eqOf (fun v _ hp => squarefreeExtension_apply_prime v hp)]
  have hind : IndepFun W (fun ω n => if n ∈ s then f ω n else 0) μ := by
    rw [hZ]
    exact indepFun_primeRestrict hX _ _ (disjoint_smallPrimes_largePrimes y ⌊x⌋₊)
  -- Khintchine, on the whole range `0 < q ≤ 1`
  have hkh := khintchine_lower_indep_of_pos hX.isRademacherRMF.isOrthonormalAtPrimes
    hs hW (C := roughCoeffOf compMultExtension x)
    (fun p => measurable_roughCoeffOf isCoeffExtension_compMultExtension x p)
    (by norm_num : (0 : ℝ) < 3)
    (fun v => integral_norm_rpow_four_primeLinearForm_le_sqfree hX hs
      (roughCoeffOf compMultExtension x v))
    (B := (⌊x⌋₊ : ℝ))
    (fun v p hp => norm_roughCoeffOf_le isCoeffExtension_compMultExtension hx0
      (hs p hp).one_lt.le v) hind hq0 (by linarith)
  -- identify the coefficients
  have hae := ae_roughCoeffOf_eq isCoeffExtension_compMultExtension hX norm_eq_one_rademacherLaw
    hx hxy
  have hcoeff : ∀ᵐ ω ∂μ, ∀ p ∈ s,
      roughCoeffOf compMultExtension x (W ω) p = randomSum g (x / p) ω := by
    filter_upwards [hae] with ω hω
    intro p hp
    obtain ⟨⟨hy, _⟩, hprime⟩ := mem_largePrimeSet.1 hp
    rw [hω p hprime hy]
  have hL : (∫ ω, (∑ p ∈ s, ‖roughCoeffOf compMultExtension x (W ω) p‖ ^ 2) ^ q ∂μ)
      = ∫ ω, (∑ p ∈ s, ‖randomSum g (x / p) ω‖ ^ 2) ^ q ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hcoeff] with ω hω
    exact congrArg (· ^ q) (Finset.sum_congr rfl fun p hp => by rw [hω p hp])
  have hR : (∫ ω, ‖∑ p ∈ s, roughCoeffOf compMultExtension x (W ω) p * f ω p‖ ^ (2 * q) ∂μ)
      ≤ 2 ^ (1 - 2 * q) * ∫ ω, ‖randomSum g x ω‖ ^ (2 * q) ∂μ := by
    refine le_trans (le_of_eq (integral_congr_ae ?_)) (integral_rough_le_extended hX hxy hq0 hq1)
    filter_upwards [hcoeff] with ω hω
    have hsum : (∑ p ∈ s, roughCoeffOf compMultExtension x (W ω) p * f ω p)
        = ∑ p ∈ s, g ω p * randomSum g (x / p) ω := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [hω p hp, hgdef, hfdef, compMultExtension_apply_prime _ (hs p hp),
        squarefreeExtension_apply_prime _ (hs p hp)]
      ring
    have hset : s = {p ∈ Finset.Icc 1 ⌊x⌋₊ | p.Prime ∧ y < p} := by
      ext p
      rw [hsdef, mem_largePrimeSet, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hy, hN⟩, hp⟩
        exact ⟨⟨hp.one_lt.le, hN⟩, hp, hy⟩
      · rintro ⟨⟨_, hN⟩, hp, hy⟩
        exact ⟨⟨hy, hN⟩, hp⟩
    rw [hsum, hset, ← randomSum_sub_smoothPartial_eq (f := g) hx hxy
      (isMultiplicative_compMultExtension _)]
  rw [hL] at hkh
  exact le_trans hkh hR

end RMF
