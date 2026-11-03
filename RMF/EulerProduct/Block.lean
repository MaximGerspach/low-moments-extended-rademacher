/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.LogField

/-!
# Euler products over a block of primes

Harper's argument does not use the full Euler product `F_y(s) = ∏_{p < y}` but a decomposition of
it into **blocks**, one per multiplicative scale, whose logarithms are the increments of the
random walk the barrier estimates apply to.  This file defines the block product and its
logarithm, and records that the blocks multiply back up to the head product.

## Naming

The block is `RMF.primesIco y₀ y₁`, the primes `p` with `y₀ ≤ p < y₁`.  The `Ico` is deliberate:
half-open on the right, matching `Nat.primesBelow`, so that

`RMF.eulerProductIco f 0 y s = RMF.eulerProduct f y s`  and
`RMF.eulerProductIco f y₀ y₁ s * RMF.eulerProductIco f y₁ y₂ s = RMF.eulerProductIco f y₀ y₂ s`

hold with no off-by-one, and adjacent blocks are automatically disjoint.  Harper writes his blocks
half-open on the *left*, `x_j^{1/e} < p ≤ x_j`; since the endpoints are irrational powers of `x`
the two conventions describe the same sets of primes in every application, but the Lean side has
to pick one and this is the one that composes.

## On indexing

`RMF.eulerProductIco` takes the two endpoints of the block, not an index into a ladder of scales.
Harper indexes blocks by an integer `ℓ`, with block `ℓ` the primes in
`(x^{e^{-(ℓ+2)}}, x^{e^{-(ℓ+1)}}]` and a *strictly decreasing* selection `ℓ_1 > … > ℓ_n`.  That is
inverted twice over — larger `ℓ` means smaller primes, and the selection then runs backwards to
recover an increasing traversal — and nothing downstream needs it: what the argument uses is that
the blocks are consecutive, disjoint, and separated by a fixed factor in the exponent.  Stating a
block by its endpoints leaves that visible.
-/

open Finset MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Blocks of primes -/

/-- The primes in the half-open range `[y₀, y₁)`. -/
noncomputable def primesIco (y₀ y₁ : ℕ) : Finset ℕ :=
  Nat.primesBelow y₁ \ Nat.primesBelow y₀

@[simp]
lemma mem_primesIco {y₀ y₁ p : ℕ} : p ∈ primesIco y₀ y₁ ↔ p.Prime ∧ y₀ ≤ p ∧ p < y₁ := by
  simp only [primesIco, Finset.mem_sdiff, Nat.primesBelow, Finset.mem_filter, Finset.mem_range,
    not_and]
  constructor
  · rintro ⟨⟨hlt, hp⟩, hnot⟩
    exact ⟨hp, by by_contra h; exact absurd hp (hnot (by omega)), hlt⟩
  · rintro ⟨hp, hge, hlt⟩
    exact ⟨⟨hlt, hp⟩, fun h => absurd h (by omega)⟩

lemma prime_of_mem_primesIco {y₀ y₁ p : ℕ} (hp : p ∈ primesIco y₀ y₁) : p.Prime :=
  (mem_primesIco.1 hp).1

@[simp]
lemma primesIco_zero (y : ℕ) : primesIco 0 y = Nat.primesBelow y := by
  ext p
  simp [Nat.primesBelow, and_comm]

lemma primesBelow_mono {y₀ y₁ : ℕ} (h : y₀ ≤ y₁) :
    Nat.primesBelow y₀ ⊆ Nat.primesBelow y₁ := by
  intro p hp
  simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨lt_of_lt_of_le hp.1 h, hp.2⟩

/-- Consecutive blocks are disjoint. -/
lemma disjoint_primesIco (y₀ y₁ y₂ : ℕ) :
    Disjoint (primesIco y₀ y₁) (primesIco y₁ y₂) := by
  refine Finset.disjoint_left.2 fun p hp hp' => ?_
  rw [mem_primesIco] at hp hp'
  omega

/-- Consecutive blocks fit together. -/
lemma primesIco_union {y₀ y₁ y₂ : ℕ} (h₀ : y₀ ≤ y₁) (h₁ : y₁ ≤ y₂) :
    primesIco y₀ y₁ ∪ primesIco y₁ y₂ = primesIco y₀ y₂ := by
  ext p
  simp only [Finset.mem_union, mem_primesIco]
  constructor
  · rintro (⟨hp, hge, hlt⟩ | ⟨hp, hge, hlt⟩) <;> exact ⟨hp, by omega, by omega⟩
  · rintro ⟨hp, hge, hlt⟩
    rcases lt_or_ge p y₁ with h | h
    · exact Or.inl ⟨hp, hge, h⟩
    · exact Or.inr ⟨hp, h, hlt⟩

/-- **The shift of one.**  The `Ioc`-indexed prime sums of the Mertens estimates and the
`Ico`-indexed blocks are the same set. -/
lemma filter_prime_Ioc_eq_primesIco (m n : ℕ) :
    {p ∈ Finset.Ioc m n | Nat.Prime p} = primesIco (m + 1) (n + 1) := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_Ioc, mem_primesIco]
  constructor
  · rintro ⟨⟨h1, h2⟩, hq⟩
    exact ⟨hq, by omega, by omega⟩
  · rintro ⟨hq, h1, h2⟩
    exact ⟨⟨by omega, by omega⟩, hq⟩

/-! ### The block Euler product -/

/-- The Euler product over the block of primes `y₀ ≤ p < y₁`. -/
noncomputable def eulerProductIco (f : ℕ → ℂ) (y₀ y₁ : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ primesIco y₀ y₁, localFactor f p s

/-- The random Euler product over the block of primes `y₀ ≤ p < y₁`. -/
noncomputable def randomEulerProductIco (f : Ω → ArithmeticFunction ℂ) (y₀ y₁ : ℕ) (s : ℂ)
    (ω : Ω) : ℂ :=
  eulerProductIco (fun n => f ω n) y₀ y₁ s

@[simp]
lemma eulerProductIco_zero (f : ℕ → ℂ) (y : ℕ) (s : ℂ) :
    eulerProductIco f 0 y s = eulerProduct f y s := by
  rw [eulerProductIco, primesIco_zero, eulerProduct]

omit [MeasurableSpace Ω] in
@[simp]
lemma randomEulerProductIco_zero (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (s : ℂ) (ω : Ω) :
    randomEulerProductIco f 0 y s ω = randomEulerProduct f y s ω :=
  eulerProductIco_zero _ y s

/-- **Blocks multiply.**  Consecutive blocks combine into the block spanning both. -/
lemma eulerProductIco_mul (f : ℕ → ℂ) {y₀ y₁ y₂ : ℕ} (h₀ : y₀ ≤ y₁) (h₁ : y₁ ≤ y₂) (s : ℂ) :
    eulerProductIco f y₀ y₁ s * eulerProductIco f y₁ y₂ s = eulerProductIco f y₀ y₂ s := by
  rw [eulerProductIco, eulerProductIco, eulerProductIco, ← primesIco_union h₀ h₁,
    Finset.prod_union (disjoint_primesIco y₀ y₁ y₂)]

/-- A block times the head product below it is the head product above it. -/
lemma eulerProduct_mul_eulerProductIco (f : ℕ → ℂ) {y₀ y₁ : ℕ} (h : y₀ ≤ y₁) (s : ℂ) :
    eulerProduct f y₀ s * eulerProductIco f y₀ y₁ s = eulerProduct f y₁ s := by
  simpa using eulerProductIco_mul f (Nat.zero_le y₀) h s

/-! ### The closed form -/

/-- The block Euler product of a completely multiplicative function, in closed form. -/
lemma eulerProductIco_compMultExtension (x : ℕ → ℂ) (y₀ y₁ : ℕ) {s : ℂ}
    (hx : ∀ p ∈ primesIco y₀ y₁, ‖x p‖ < (p : ℝ) ^ s.re) :
    eulerProductIco (fun n => compMultExtension x n) y₀ y₁ s
      = ∏ p ∈ primesIco y₀ y₁, (1 - x p * (p : ℂ) ^ (-s))⁻¹ :=
  Finset.prod_congr rfl fun p hp =>
    localFactor_compMultExtension x (prime_of_mem_primesIco hp) (hx p hp)

omit [MeasurableSpace Ω] in
/-- Closed form in the completely multiplicative case, at any `ω` where the values at the
relevant primes are bounded by one. -/
lemma randomEulerProductIco_compMult_eq {X : ℕ → Ω → ℂ} {y₀ y₁ : ℕ} {s : ℂ} (hs : 0 < s.re)
    {ω : Ω} (hω : ∀ p ∈ primesIco y₀ y₁, ‖X p ω‖ ≤ 1) :
    randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y₁ s ω
      = ∏ p ∈ primesIco y₀ y₁, (1 - X p ω * (p : ℂ) ^ (-s))⁻¹ :=
  eulerProductIco_compMultExtension _ y₀ y₁ fun p hp =>
    lt_of_le_of_lt (hω p hp) (one_lt_prime_rpow (prime_of_mem_primesIco hp) hs)

/-- Values at the primes of a block are all bounded by one, almost surely. -/
lemma ae_forall_norm_le_one_primesIco {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) (y₀ y₁ : ℕ) :
    ∀ᵐ ω ∂μ, ∀ p ∈ primesIco y₀ y₁, ‖X p ω‖ ≤ 1 := by
  refine (Filter.eventually_all_finset _).2 fun p hp => ?_
  have hmeasP : Measurable fun z : ℂ => ‖z‖ ≤ 1 :=
    measurableSet_setOf.1 (measurableSet_le measurable_norm measurable_const)
  exact ((hX.hasLaw p (prime_of_mem_primesIco hp)).ae_iff hmeasP).2 hν

/-! ### The joint moment over a range of primes

Hamdan's Lemma B.1 needs a joint moment of Euler products factored over a **range** of primes,
since the walk the barrier constrains is an increment between two scales, not a head sum.  The proof
is independence at distinct primes and an exchange of two finite products, over `RMF.primesIco`. -/

/-- The convergence input of the local expansion, over a range: `∑_{p ∈ [y₀,y₁)} p^{-3σ}` is
bounded by the same series that bounds the head sum, since the range is a subset of it. -/
lemma sum_primesIco_rpow_le {σ σ₀ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hσ : σ₀ ≤ σ) (y₀ y₁ : ℕ) :
    ∑ p ∈ primesIco y₀ y₁, (p : ℝ) ^ (-3 * σ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 * σ₀) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    (sum_primesBelow_rpow_le hσ₀ hσ y₁)
  · intro p hp
    rw [mem_primesIco] at hp
    exact Nat.mem_primesBelow.2 ⟨hp.2.2, hp.1⟩
  · exact fun p _ _ => Real.rpow_nonneg (Nat.cast_nonneg p) _

/-- **A joint moment over a range of primes factors over that range.**

The exponents may have either sign: a negative exponent is what a *ratio* `‖F(s₁)‖/‖F(s₂)‖`
costs, and that is the shape Hamdan's Lemma B.1 needs. -/
theorem integral_prod_norm_randomEulerProductIco_rpow_compMult {ι : Type*} {X : ℕ → Ω → ℂ}
    {ν : Measure ℂ} {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1)
    (y₀ y₁ : ℕ) (J : Finset ι) {s : ι → ℂ} (hs : ∀ j ∈ J, 0 < (s j).re) {q : ι → ℝ} :
    (∫ ω, ∏ j ∈ J, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω)
        y₀ y₁ (s j) ω‖ ^ (2 * q j) ∂μ)
      = ∏ p ∈ primesIco y₀ y₁,
          ∫ z, ∏ j ∈ J, ‖(1 - z * (p : ℂ) ^ (-s j))⁻¹‖ ^ (2 * q j) ∂ν := by
  have hae : ∀ᵐ ω ∂μ,
      (∏ j ∈ J, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω)
          y₀ y₁ (s j) ω‖ ^ (2 * q j))
        = ∏ p ∈ primesIco y₀ y₁, ∏ j ∈ J,
            ‖(1 - X p ω * (p : ℂ) ^ (-s j))⁻¹‖ ^ (2 * q j) := by
    filter_upwards [ae_forall_norm_le_one_primesIco hX hν y₀ y₁] with ω hω
    have hj : ∀ j ∈ J,
        ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y₁ (s j) ω‖
            ^ (2 * q j)
          = ∏ p ∈ primesIco y₀ y₁, ‖(1 - X p ω * (p : ℂ) ^ (-s j))⁻¹‖ ^ (2 * q j) := by
      intro j hjJ
      rw [randomEulerProductIco_compMult_eq (hs j hjJ) hω, norm_prod,
        Real.finsetProd_rpow _ _ (fun _ _ => norm_nonneg _) (2 * q j)]
    rw [Finset.prod_congr rfl hj, Finset.prod_comm]
  have hmeas : ∀ p ∈ primesIco y₀ y₁, AEStronglyMeasurable
      (fun z => ∏ j ∈ J, ‖(1 - z * (p : ℂ) ^ (-s j))⁻¹‖ ^ (2 * q j)) ν := by
    intro p hp
    have hp2 := prime_of_mem_primesIco hp
    refine Finset.aestronglyMeasurable_fun_prod _ fun j hj => ?_
    have hlt : ‖((p : ℂ)) ^ (-s j)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp2.pos, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp2.one_lt)
        (by linarith [hs j hj])
    exact aestronglyMeasurable_localIntegrand_of_norm_le hν hlt (2 * q j)
  rw [integral_congr_ae hae,
    hX.integral_prod (fun _ hp => prime_of_mem_primesIco hp)
      (fun p z => ∏ j ∈ J, ‖(1 - z * (p : ℂ) ^ (-s j))⁻¹‖ ^ (2 * q j)) hmeas]

/-- The Steinhaus case of `RMF.integral_prod_norm_randomEulerProductIco_rpow_compMult`. -/
theorem IsSteinhausRMF.integral_prod_norm_randomEulerProductIco_rpow {ι : Type*}
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) (y₀ y₁ : ℕ)
    (J : Finset ι) {s : ι → ℂ} (hs : ∀ j ∈ J, 0 < (s j).re) {q : ι → ℝ} :
    (∫ ω, ∏ j ∈ J, ‖randomEulerProductIco f y₀ y₁ (s j) ω‖ ^ (2 * q j) ∂μ)
      = ∏ p ∈ primesIco y₀ y₁,
          ∫ z, ∏ j ∈ J, ‖(1 - z * (p : ℂ) ^ (-s j))⁻¹‖ ^ (2 * q j) ∂steinhausLaw := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  exact integral_prod_norm_randomEulerProductIco_rpow_compMult hX norm_le_one_steinhausLaw
    y₀ y₁ J hs

/-! ### The same, for the squarefree extension

Here the local factor is the polynomial `1 + x_p p^{-s}` (`RMF.localFactor_squarefreeExtension`),
with no hypothesis on `s` or on `x`, so the closed form `RMF.randomEulerProductIco_sqfree_eq` holds
at every `ω`.  The completely multiplicative factor `(1 - x_p p^{-s})⁻¹` needs `‖x_p‖ < p^{Re s}`,
which is why `RMF.randomEulerProductIco_compMult_eq` carries `0 < Re s` and a bound on the values,
and why that factorisation needs `RMF.ae_forall_norm_le_one_primesIco` first.

In the squarefree factorisation `0 < Re s` and `‖z‖ ≤ 1` on the law are used only for
measurability: at a negative exponent `‖1 + z w‖^r` needs `1 + z w` bounded away from zero
(`RMF.aestronglyMeasurable_localIntegrandAdd_of_norm_le`).  **Signed exponents are allowed**: a
ratio of Euler products costs one, and the Rademacher negative moments need them
(`RMF.integral_norm_randomEulerProduct_rpow_sqfree_of_norm_le`). -/

/-- The block Euler product of a squarefree-supported function, in closed form.  No hypothesis:
the local factors are polynomials. -/
lemma eulerProductIco_squarefreeExtension (x : ℕ → ℂ) (y₀ y₁ : ℕ) (s : ℂ) :
    eulerProductIco (fun n => squarefreeExtension x n) y₀ y₁ s
      = ∏ p ∈ primesIco y₀ y₁, (1 + x p * (p : ℂ) ^ (-s)) :=
  Finset.prod_congr rfl fun _p hp =>
    localFactor_squarefreeExtension x (prime_of_mem_primesIco hp) s

omit [MeasurableSpace Ω] in
/-- Closed form in the squarefree case, at **every** `ω` and with no hypothesis on `s` — where
`RMF.randomEulerProductIco_compMult_eq` needs `0 < Re s` and an almost-sure bound on the values. -/
lemma randomEulerProductIco_sqfree_eq {X : ℕ → Ω → ℂ} (y₀ y₁ : ℕ) (s : ℂ) (ω : Ω) :
    randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω
      = ∏ p ∈ primesIco y₀ y₁, (1 + X p ω * (p : ℂ) ^ (-s)) :=
  eulerProductIco_squarefreeExtension _ y₀ y₁ s

/-- **A joint moment over a range of primes factors over that range**, squarefree case.

The exponents may have either sign; `0 < Re s` and the bound on the law are needed only to make
the integrand measurable at a negative one. -/
theorem integral_prod_norm_randomEulerProductIco_rpow_sqfree {ι : Type*} {X : ℕ → Ω → ℂ}
    {ν : Measure ℂ} {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1)
    (y₀ y₁ : ℕ) (J : Finset ι) {s : ι → ℂ} (hs : ∀ j ∈ J, 0 < (s j).re) {q : ι → ℝ} :
    (∫ ω, ∏ j ∈ J, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        y₀ y₁ (s j) ω‖ ^ (2 * q j) ∂μ)
      = ∏ p ∈ primesIco y₀ y₁,
          ∫ z, ∏ j ∈ J, ‖1 + z * (p : ℂ) ^ (-s j)‖ ^ (2 * q j) ∂ν := by
  have hpt : ∀ ω : Ω,
      (∏ j ∈ J, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          y₀ y₁ (s j) ω‖ ^ (2 * q j))
        = ∏ p ∈ primesIco y₀ y₁, ∏ j ∈ J,
            ‖1 + X p ω * (p : ℂ) ^ (-s j)‖ ^ (2 * q j) := by
    intro ω
    have hj : ∀ j ∈ J,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ (s j) ω‖
            ^ (2 * q j)
          = ∏ p ∈ primesIco y₀ y₁, ‖1 + X p ω * (p : ℂ) ^ (-s j)‖ ^ (2 * q j) := by
      intro j _
      rw [randomEulerProductIco_sqfree_eq, norm_prod,
        Real.finsetProd_rpow _ _ (fun _ _ => norm_nonneg _) (2 * q j)]
    rw [Finset.prod_congr rfl hj, Finset.prod_comm]
  have hmeas : ∀ p ∈ primesIco y₀ y₁, AEStronglyMeasurable
      (fun z => ∏ j ∈ J, ‖1 + z * (p : ℂ) ^ (-s j)‖ ^ (2 * q j)) ν := by
    intro p hp
    have hp2 := prime_of_mem_primesIco hp
    refine Finset.aestronglyMeasurable_fun_prod _ fun j hj => ?_
    have hlt : ‖((p : ℂ)) ^ (-s j)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp2.pos, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp2.one_lt)
        (by linarith [hs j hj])
    exact aestronglyMeasurable_localIntegrandAdd_of_norm_le hν hlt (2 * q j)
  simp_rw [hpt]
  rw [hX.integral_prod (fun _ hp => prime_of_mem_primesIco hp)
    (fun p z => ∏ j ∈ J, ‖1 + z * (p : ℂ) ^ (-s j)‖ ^ (2 * q j)) hmeas]

/-- The Rademacher case of `RMF.integral_prod_norm_randomEulerProductIco_rpow_sqfree`.  This is
the gateway the joint-Laplace wrappers need, and the counterpart of
`RMF.IsSteinhausRMF.integral_prod_norm_randomEulerProductIco_rpow`. -/
theorem IsRademacherRMF.integral_prod_norm_randomEulerProductIco_rpow {ι : Type*}
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ) (y₀ y₁ : ℕ)
    (J : Finset ι) {s : ι → ℂ} (hs : ∀ j ∈ J, 0 < (s j).re) {q : ι → ℝ} :
    (∫ ω, ∏ j ∈ J, ‖randomEulerProductIco f y₀ y₁ (s j) ω‖ ^ (2 * q j) ∂μ)
      = ∏ p ∈ primesIco y₀ y₁,
          ∫ z, ∏ j ∈ J, ‖1 + z * (p : ℂ) ^ (-s j)‖ ^ (2 * q j) ∂rademacherLaw := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  exact integral_prod_norm_randomEulerProductIco_rpow_sqfree hX norm_le_one_rademacherLaw
    y₀ y₁ J hs

/-! ### Two-sided bounds on the squarefree block product

The Chernoff bound needs the block product bounded **on both sides**, so that its logarithm is
finite and `‖F‖^{2q}` is integrable at a negative exponent.  The squarefree factors
`1 + X_p ω p^{-s}` give the bounds `∏ (1 ± ‖p^{-s}‖)`, where the completely multiplicative side
carries `∏ (1 ∓ ‖p^{-s}‖)⁻¹` (`RMF.IsSteinhausRMF.ae_norm_randomEulerProductIco_le` and
`RMF.IsSteinhausRMF.ae_le_norm_randomEulerProductIco`).

**The value bound is needed for both laws**: `‖1 + z w‖ ≥ 1 - ‖w‖` uses `‖z‖ ≤ 1`.  What the
squarefree extension saves is the closed form, not the non-vanishing.  **Measurability needs
nothing**: the closed form is pointwise, so `RMF.IsRademacherRMF.aemeasurable_randomEulerProductIco`
has no hypothesis on `s`, where its Steinhaus counterpart needs `0 < Re s`. -/

omit [MeasurableSpace Ω] in
/-- **Upper bound on the squarefree block product**, pointwise wherever the values are bounded by
one. -/
lemma norm_randomEulerProductIco_sqfree_le {X : ℕ → Ω → ℂ} (y₀ y₁ : ℕ) (s : ℂ) {ω : Ω}
    (hω : ∀ p ∈ primesIco y₀ y₁, ‖X p ω‖ ≤ 1) :
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖
      ≤ ∏ p ∈ primesIco y₀ y₁, (1 + ‖(p : ℂ) ^ (-s)‖) := by
  rw [randomEulerProductIco_sqfree_eq, norm_prod]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp => ?_
  have h1 : ‖X p ω * (p : ℂ) ^ (-s)‖ ≤ ‖(p : ℂ) ^ (-s)‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hω p hp)
  have h2 := norm_add_le (1 : ℂ) (X p ω * (p : ℂ) ^ (-s))
  rw [norm_one] at h2
  linarith

omit [MeasurableSpace Ω] in
/-- **Lower bound on the squarefree block product.**  The mirror of
`RMF.norm_randomEulerProductIco_sqfree_le`; `0 < Re s` enters only to keep each factor positive. -/
lemma le_norm_randomEulerProductIco_sqfree {X : ℕ → Ω → ℂ} (y₀ y₁ : ℕ) {s : ℂ}
    (hs : 0 < s.re) {ω : Ω} (hω : ∀ p ∈ primesIco y₀ y₁, ‖X p ω‖ ≤ 1) :
    (∏ p ∈ primesIco y₀ y₁, (1 - ‖(p : ℂ) ^ (-s)‖))
      ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖ := by
  rw [randomEulerProductIco_sqfree_eq, norm_prod]
  refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
  · have hw := norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
    linarith
  · have h1 : ‖X p ω * (p : ℂ) ^ (-s)‖ ≤ ‖(p : ℂ) ^ (-s)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hω p hp)
    have h2 := norm_sub_norm_le (1 : ℂ) (-(X p ω * (p : ℂ) ^ (-s)))
    rw [norm_one, norm_neg, sub_neg_eq_add] at h2
    linarith

/-- **A deterministic bound on the squarefree block product.**  Each local factor has modulus at
most `1 + ‖p^{-s}‖`.  Unlike `RMF.IsSteinhausRMF.ae_norm_randomEulerProductIco_le` this needs no
hypothesis on `s`: there is nothing to invert. -/
lemma IsRademacherRMF.ae_norm_randomEulerProductIco_le {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsRademacherRMF f μ) (y₀ y₁ : ℕ) (s : ℂ) :
    ∀ᵐ ω ∂μ, ‖randomEulerProductIco f y₀ y₁ s ω‖
      ≤ ∏ p ∈ primesIco y₀ y₁, (1 + ‖(p : ℂ) ^ (-s)‖) := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw y₀ y₁] with ω hω
  exact norm_randomEulerProductIco_sqfree_le y₀ y₁ s hω

/-- **The squarefree block product is almost surely non-zero.**  From the lower bound, which is
positive because each `1 - ‖p^{-s}‖` is. -/
theorem IsRademacherRMF.ae_randomEulerProductIco_ne_zero {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsRademacherRMF f μ) (y₀ y₁ : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ∀ᵐ ω ∂μ, randomEulerProductIco f y₀ y₁ s ω ≠ 0 := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw y₀ y₁] with ω hω
  have hlow := le_norm_randomEulerProductIco_sqfree y₀ y₁ hs hω
  have hpos : (0 : ℝ) < ∏ p ∈ primesIco y₀ y₁, (1 - ‖(p : ℂ) ^ (-s)‖) := by
    refine Finset.prod_pos fun p hp => ?_
    have hw := norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
    linarith
  intro h
  rw [h, norm_zero] at hlow
  linarith

/-- **Measurability of the squarefree block product, with no hypothesis on `s`.**

The closed form `RMF.randomEulerProductIco_sqfree_eq` is pointwise and unconditional, so this is a
`funext` and a finite product of measurable functions.  `RMF.IsSteinhausRMF`'s counterpart needs
`0 < Re s` and an almost-everywhere rewrite before it can start. -/
lemma IsRademacherRMF.aemeasurable_randomEulerProductIco {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsRademacherRMF f μ) (y₀ y₁ : ℕ) (s : ℂ) :
    AEMeasurable (randomEulerProductIco f y₀ y₁ s) μ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have he : randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s
      = fun ω => ∏ p ∈ primesIco y₀ y₁, (1 + X p ω * (p : ℂ) ^ (-s)) :=
    funext fun ω => randomEulerProductIco_sqfree_eq y₀ y₁ s ω
  rw [he]
  exact (Finset.measurable_prod _ fun p hp =>
    ((hX.measurable p (prime_of_mem_primesIco hp)).mul_const _).const_add _).aemeasurable

/-- **A deterministic bound on the whole squarefree Euler product.**  The whole-product form of
`RMF.IsRademacherRMF.ae_norm_randomEulerProductIco_le`, and like it needs no hypothesis on `s`. -/
lemma IsRademacherRMF.ae_norm_randomEulerProduct_le {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsRademacherRMF f μ) (y : ℕ) (s : ℂ) :
    ∀ᵐ ω ∂μ, ‖randomEulerProduct f y s ω‖
      ≤ ∏ p ∈ Nat.primesBelow y, (1 + ‖((p : ℕ) : ℂ) ^ (-s)‖) := by
  filter_upwards [hf.ae_norm_randomEulerProductIco_le 0 y s] with ω hω
  rwa [randomEulerProductIco_zero, primesIco_zero] at hω

/-- **The whole squarefree Euler product is a.e. measurable**, with no hypothesis on `s`. -/
lemma IsRademacherRMF.aemeasurable_randomEulerProduct {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsRademacherRMF f μ) (y : ℕ) (s : ℂ) :
    AEMeasurable (randomEulerProduct f y s) μ := by
  have he : randomEulerProductIco f 0 y s = randomEulerProduct f y s :=
    funext fun ω => randomEulerProductIco_zero f y s ω
  have h := hf.aemeasurable_randomEulerProductIco 0 y s
  rwa [he] at h

/-! ### The block product is bounded and measurable

The two crude facts every integrability argument needs, transported to a range.  Both are the
range versions of lemmas in `RMF/EulerProduct/Tilted.lean`, with the same proofs. -/

/-- **A deterministic bound on the block product.**  Each local factor has modulus at most
`(1 - ‖p^{-s}‖)⁻¹`.  Very lossy, and used only for integrability. -/
lemma IsSteinhausRMF.ae_norm_randomEulerProductIco_le {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsSteinhausRMF f μ) (y₀ y₁ : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ∀ᵐ ω ∂μ, ‖randomEulerProductIco f y₀ y₁ s ω‖
      ≤ ∏ p ∈ primesIco y₀ y₁, (1 - ‖(p : ℂ) ^ (-s)‖)⁻¹ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_steinhausLaw y₀ y₁] with ω hω
  rw [randomEulerProductIco_compMult_eq hs hω, norm_prod]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp => ?_
  have hw : ‖(p : ℂ) ^ (-s)‖ < 1 :=
    norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
  have hlow : 1 - ‖(p : ℂ) ^ (-s)‖ ≤ ‖1 - X p ω * (p : ℂ) ^ (-s)‖ := by
    have h1 : ‖X p ω * (p : ℂ) ^ (-s)‖ ≤ ‖(p : ℂ) ^ (-s)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hω p hp)
    have h2 := norm_sub_norm_le (1 : ℂ) (X p ω * (p : ℂ) ^ (-s))
    rw [norm_one] at h2
    linarith
  rw [norm_inv]
  exact inv_anti₀ (by linarith) hlow

/-- The block product is a.e. measurable, being a.e. a finite product of measurable functions. -/
lemma IsSteinhausRMF.aemeasurable_randomEulerProductIco {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsSteinhausRMF f μ) (y₀ y₁ : ℕ) {s : ℂ} (hs : 0 < s.re) :
    AEMeasurable (randomEulerProductIco f y₀ y₁ s) μ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have hae : randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y₁ s
      =ᵐ[μ] fun ω => ∏ p ∈ primesIco y₀ y₁, (1 - X p ω * (p : ℂ) ^ (-s))⁻¹ := by
    filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_steinhausLaw y₀ y₁] with ω hω
    exact randomEulerProductIco_compMult_eq hs hω
  refine AEMeasurable.congr ?_ hae.symm
  refine (Finset.measurable_prod _ fun p hp => ?_).aemeasurable
  have hm : Measurable (X p) := hX.measurable p (prime_of_mem_primesIco hp)
  exact ((hm.mul measurable_const).const_sub 1).inv

/-- **The block product does not vanish.**  Each local factor is an inverse, and the element
inverted has modulus at least `1 - ‖p^{-s}‖ > 0`. -/
lemma IsSteinhausRMF.ae_randomEulerProductIco_ne_zero {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsSteinhausRMF f μ) (y₀ y₁ : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ∀ᵐ ω ∂μ, randomEulerProductIco f y₀ y₁ s ω ≠ 0 := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_steinhausLaw y₀ y₁] with ω hω
  rw [randomEulerProductIco_compMult_eq hs hω]
  refine Finset.prod_ne_zero_iff.2 fun p hp => inv_ne_zero fun hzero => ?_
  have hw : ‖(p : ℂ) ^ (-s)‖ < 1 :=
    norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
  have h1 : ‖X p ω * (p : ℂ) ^ (-s)‖ ≤ ‖(p : ℂ) ^ (-s)‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hω p hp)
  have h2 := norm_sub_norm_le (1 : ℂ) (X p ω * (p : ℂ) ^ (-s))
  rw [norm_one, hzero, norm_zero] at h2
  linarith

end RMF
