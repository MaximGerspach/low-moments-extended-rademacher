/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.Khintchine
import RMF.Probability.Symmetrisation

/-!
# The rough part as a linear form in the large primes

`RMF.randomSum_sub_smoothPartial_eq` writes the rough part of `∑_{n≤x} f(n)` as

`∑_{√x<p≤x} f(p) · ∑_{m≤x/p} f(m)`,

which is a linear form in the values `f(p)` at the large primes, with coefficients that depend
only on the values at the small ones.  That is exactly the shape
`RMF.khintchine_lower_indep` consumes — once the coefficients are exhibited as a *measurable
function of the small-prime data*, and that data is shown independent of the large-prime data.

This file supplies both.

## Why the coefficients are truncated

`khintchine_lower_indep` asks for a bound `‖C v p‖ ≤ B` at **every** `v` in the coefficient space,
not merely at those in the range of the small-prime map.  On `ℕ → ℂ` no such bound exists, so
`RMF.unitize` forces every value onto the unit circle before the multiplicative extension is
formed.  On the range of the small-prime map this changes nothing — the values are already
unimodular, almost surely — and off it, it buys a global bound `‖C v p‖ ≤ ⌊x⌋`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The multiplicative extension sees only the primes dividing `n` -/

/-- `compMultExtension` depends on `v` only through its values at the primes dividing `n`. -/
lemma compMultExtension_congr {v w : ℕ → ℂ} {n : ℕ}
    (h : ∀ p ∈ n.primeFactors, v p = w p) :
    compMultExtension v n = compMultExtension w n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [compMultExtension]
  · rw [compMultExtension_apply_of_ne_zero v hn, compMultExtension_apply_of_ne_zero w hn]
    refine Finsupp.prod_congr fun p hp => ?_
    rw [h p (by rwa [← Nat.support_factorization])]

/-! ### The truncated coefficient map -/

/-- Every value forced onto the unit circle.  A no-op on unimodular data. -/
noncomputable def unitize (v : ℕ → ℂ) (q : ℕ) : ℂ := if ‖v q‖ = 1 then v q else 1

lemma norm_unitize (v : ℕ → ℂ) (q : ℕ) : ‖unitize v q‖ = 1 := by
  rw [unitize]
  split
  · assumption
  · simp

lemma measurable_unitize (q : ℕ) : Measurable fun v : ℕ → ℂ => unitize v q := by
  refine Measurable.ite ?_ (measurable_pi_apply q) measurable_const
  exact measurableSet_eq_fun ((measurable_pi_apply q).norm) measurable_const

/-- The multiplicative extension of unitised data is unimodular away from `0`. -/
lemma norm_compMultExtension_unitize {v : ℕ → ℂ} {n : ℕ} (hn : n ≠ 0) :
    ‖compMultExtension (unitize v) n‖ = 1 := by
  rw [compMultExtension_apply_of_ne_zero _ hn, Finsupp.prod]
  rw [norm_prod]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [norm_pow, norm_unitize, one_pow]

/-- `squarefreeExtension` depends on `v` only through its values at the primes dividing `n`. -/
lemma squarefreeExtension_congr {v w : ℕ → ℂ} {n : ℕ}
    (h : ∀ p ∈ n.primeFactors, v p = w p) :
    squarefreeExtension v n = squarefreeExtension w n := by
  by_cases hsf : Squarefree n
  · rw [squarefreeExtension_apply_of_squarefree v hsf,
      squarefreeExtension_apply_of_squarefree w hsf]
    exact Finset.prod_congr rfl h
  · rw [squarefreeExtension_apply_of_not_squarefree v hsf,
      squarefreeExtension_apply_of_not_squarefree w hsf]

/-- The squarefree extension of unitised data is bounded by one.  Its `compMultExtension` mirror
`RMF.norm_compMultExtension_unitize` is an *equality*; off the squarefrees this is `0`. -/
lemma norm_squarefreeExtension_unitize_le (v : ℕ → ℂ) (n : ℕ) :
    ‖squarefreeExtension (unitize v) n‖ ≤ 1 := by
  by_cases hsf : Squarefree n
  · rw [squarefreeExtension_apply_of_squarefree _ hsf, norm_prod]
    exact le_of_eq (Finset.prod_eq_one fun p _ => norm_unitize v p)
  · rw [squarefreeExtension_apply_of_not_squarefree _ hsf, norm_zero]
    norm_num

lemma measurable_compMultExtension_unitize (k : ℕ) :
    Measurable fun v : ℕ → ℂ => compMultExtension (unitize v) k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [compMultExtension]
  · have : (fun v : ℕ → ℂ => compMultExtension (unitize v) k)
        = fun v => (k.factorization).prod fun p e => (unitize v p) ^ e := by
      funext v
      exact compMultExtension_apply_of_ne_zero _ hk
    rw [this]
    simp only [Finsupp.prod]
    exact Finset.measurable_prod _ fun p _ => (measurable_unitize p).pow_const _

lemma measurable_squarefreeExtension_unitize (k : ℕ) :
    Measurable fun v : ℕ → ℂ => squarefreeExtension (unitize v) k := by
  by_cases hsf : Squarefree k
  · have : (fun v : ℕ → ℂ => squarefreeExtension (unitize v) k)
        = fun v => ∏ p ∈ k.primeFactors, unitize v p := by
      funext v
      exact squarefreeExtension_apply_of_squarefree _ hsf
    rw [this]
    exact Finset.measurable_prod _ fun p _ => measurable_unitize p
  · have : (fun v : ℕ → ℂ => squarefreeExtension (unitize v) k) = fun _ => 0 := by
      funext v
      exact squarefreeExtension_apply_of_not_squarefree _ hsf
    rw [this]
    exact measurable_const

/-- **What the rough-coefficient reconstruction asks of an extension**: it is determined by the
values at the primes dividing `n`, it does not grow on unitised data, and it is measurable in that
data.  Both `RMF.compMultExtension` and `RMF.squarefreeExtension` qualify. -/
structure IsCoeffExtension (ext : (ℕ → ℂ) → ArithmeticFunction ℂ) : Prop where
  /-- Only the values at the primes dividing `n` matter. -/
  congr_primeFactors : ∀ {v w : ℕ → ℂ} {n : ℕ},
    (∀ p ∈ n.primeFactors, v p = w p) → ext v n = ext w n
  /-- On unitised data the values are bounded by one. -/
  norm_unitize_le : ∀ (v : ℕ → ℂ) (n : ℕ), ‖ext (unitize v) n‖ ≤ 1
  /-- Measurable in the data. -/
  measurable_unitize_apply : ∀ k : ℕ, Measurable fun v : ℕ → ℂ => ext (unitize v) k

lemma isCoeffExtension_compMultExtension : IsCoeffExtension compMultExtension where
  congr_primeFactors h := compMultExtension_congr h
  norm_unitize_le v n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [compMultExtension]
    · exact le_of_eq (norm_compMultExtension_unitize hn)
  measurable_unitize_apply := measurable_compMultExtension_unitize

lemma isCoeffExtension_squarefreeExtension : IsCoeffExtension squarefreeExtension where
  congr_primeFactors h := squarefreeExtension_congr h
  norm_unitize_le := norm_squarefreeExtension_unitize_le
  measurable_unitize_apply := measurable_squarefreeExtension_unitize

/-- The coefficient of the large prime `p`, for a general extension: the partial sum of the
extension of the (unitised) small-prime data up to `x/p`. -/
noncomputable def roughCoeffOf (ext : (ℕ → ℂ) → ArithmeticFunction ℂ) (x : ℝ) (v : ℕ → ℂ)
    (p : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊x / p⌋₊, ext (unitize v) k

lemma norm_roughCoeffOf_le {ext : (ℕ → ℂ) → ArithmeticFunction ℂ}
    (hext : IsCoeffExtension ext) {x : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : 1 ≤ p) (v : ℕ → ℂ) :
    ‖roughCoeffOf ext x v p‖ ≤ (⌊x⌋₊ : ℝ) := by
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hdiv : x / p ≤ x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun k _ =>
    hext.norm_unitize_le v k) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
  have hmono : ⌊x / p⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hdiv
  have hcast : ((⌊x / p⌋₊ + 1 - 1 : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    simp only [Nat.add_sub_cancel]
    exact_mod_cast hmono
  exact hcast

lemma measurable_roughCoeffOf {ext : (ℕ → ℂ) → ArithmeticFunction ℂ}
    (hext : IsCoeffExtension ext) (x : ℝ) (p : ℕ) :
    Measurable fun v : ℕ → ℂ => roughCoeffOf ext x v p :=
  Finset.measurable_sum _ fun k _ => hext.measurable_unitize_apply k

/-! ### Splitting the primes

`ProbabilityTheory.iIndepFun.indepFun_finset` separates the values at two disjoint finite sets of
primes.  What it hands back are the *tuples* `(X p)_{p ∈ S}` and `(X p)_{p ∈ T}`; both sides of
the Khintchine step want functions on `ℕ` instead, so each tuple is pushed forward along
`RMF.primeRestrict`, which spreads it back over `ℕ` and pads with `0`.  The padding value is
irrelevant downstream because `RMF.unitize` sends `0` to `1`. -/

open scoped Classical in
/-- A tuple indexed by a finite set of primes, spread over `ℕ` and padded with `0`. -/
noncomputable def primeRestrict (S : Finset Nat.Primes) (u : S → ℂ) (q : ℕ) : ℂ :=
  if h : ∃ i : S, ((i : Nat.Primes) : ℕ) = q then u h.choose else 0

lemma primeRestrict_apply_of_mem {S : Finset Nat.Primes} {i : Nat.Primes} (hi : i ∈ S)
    (u : S → ℂ) : primeRestrict S u (i : ℕ) = u ⟨i, hi⟩ := by
  have h : ∃ j : S, ((j : Nat.Primes) : ℕ) = (i : ℕ) := ⟨⟨i, hi⟩, rfl⟩
  rw [primeRestrict, dif_pos h]
  congr 1
  have hval : ((h.choose : Nat.Primes) : ℕ) = (i : ℕ) := h.choose_spec
  exact Subtype.ext (Subtype.ext hval)

lemma primeRestrict_apply_of_notMem {S : Finset Nat.Primes} {q : ℕ}
    (hq : ∀ i : Nat.Primes, i ∈ S → (i : ℕ) ≠ q) (u : S → ℂ) :
    primeRestrict S u q = 0 := by
  rw [primeRestrict, dif_neg]
  rintro ⟨i, hi⟩
  exact hq (i : Nat.Primes) i.2 hi

lemma measurable_primeRestrict (S : Finset Nat.Primes) : Measurable (primeRestrict S) := by
  refine measurable_pi_lambda _ fun q => ?_
  by_cases h : ∃ i : S, ((i : Nat.Primes) : ℕ) = q
  · simp only [primeRestrict, dif_pos h]
    exact measurable_pi_apply _
  · simp only [primeRestrict, dif_neg h]
    exact measurable_const

/-- **The split.**  For disjoint finite sets of primes `S` and `T`, the small-prime data is
independent of the large-prime data.  Both are presented as functions on `ℕ`, padded with `0`
off the respective set. -/
theorem indepFun_primeRestrict {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) (S T : Finset Nat.Primes) (hST : Disjoint S T) :
    IndepFun (fun ω => primeRestrict S fun i : S => X ((i : Nat.Primes) : ℕ) ω)
      (fun ω => primeRestrict T fun i : T => X ((i : Nat.Primes) : ℕ) ω) μ := by
  have hmeas : ∀ i : Nat.Primes, Measurable (X (i : ℕ)) := fun i => hX.measurable (i : ℕ) i.2
  exact (hX.iIndep.indepFun_finset S T hST hmeas).comp (measurable_primeRestrict S)
    (measurable_primeRestrict T)

/-! ### The two blocks of primes, and what the coefficient map computes on them -/

/-- The primes at most `y`. -/
noncomputable def smallPrimes (y : ℕ) : Finset Nat.Primes :=
  (Finset.Icc 1 y).subtype fun n => Nat.Prime n

/-- The primes in `(y, N]`. -/
noncomputable def largePrimes (y N : ℕ) : Finset Nat.Primes :=
  (Finset.Ioc y N).subtype fun n => Nat.Prime n

lemma mem_smallPrimes {y : ℕ} {i : Nat.Primes} : i ∈ smallPrimes y ↔ (i : ℕ) ≤ y := by
  constructor
  · intro hi
    exact (Finset.mem_Icc.1 (Finset.mem_subtype.1 hi)).2
  · intro hi
    exact Finset.mem_subtype.2 (Finset.mem_Icc.2 ⟨i.2.one_lt.le, hi⟩)

lemma mem_largePrimes {y N : ℕ} {i : Nat.Primes} :
    i ∈ largePrimes y N ↔ y < (i : ℕ) ∧ (i : ℕ) ≤ N := by
  constructor
  · intro hi
    exact Finset.mem_Ioc.1 (Finset.mem_subtype.1 hi)
  · intro hi
    exact Finset.mem_subtype.2 (Finset.mem_Ioc.2 hi)

lemma disjoint_smallPrimes_largePrimes (y N : ℕ) :
    Disjoint (smallPrimes y) (largePrimes y N) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  exact absurd (mem_largePrimes.1 hi').1 (not_lt.2 (mem_smallPrimes.1 hi))

/-- Almost surely, every value at a prime is unimodular. -/
lemma ae_norm_X_eq_one {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) (hν : ∀ᵐ z ∂ν, ‖z‖ = 1)
    {p : ℕ} (hp : p.Prime) : ∀ᵐ ω ∂μ, ‖X p ω‖ = 1 := by
  have hmeasP : Measurable fun z : ℂ => ‖z‖ = 1 :=
    measurableSet_setOf.1 (measurable_norm (measurableSet_singleton 1))
  exact ((hX.hasLaw p hp).ae_iff hmeasP).2 hν

/-- **The coefficient map computes the small partial sum.**  For a large prime `p`, every
`m ≤ x/p` is below `y+1`, so its prime factors all lie in `smallPrimes y`, where the padded and
unitised data agrees with `X`. -/
theorem ae_roughCoeffOf_eq {ext : (ℕ → ℂ) → ArithmeticFunction ℂ}
    (hext : IsCoeffExtension ext) {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) (hν : ∀ᵐ z ∂ν, ‖z‖ = 1)
    {x : ℝ} {y : ℕ} (hx : 1 ≤ x) (hxy : ⌊x⌋₊ < (y + 1) ^ 2) :
    ∀ᵐ ω ∂μ, ∀ p : ℕ, p.Prime → y < p →
      roughCoeffOf ext x (primeRestrict (smallPrimes y) fun i : smallPrimes y =>
          X ((i : Nat.Primes) : ℕ) ω) p
        = randomSum (fun ω => ext fun q => X q ω) (x / p) ω := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hxlt : x < ((y : ℝ) + 1) ^ 2 := by
    have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (((y + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hxy
    push_cast at h2
    linarith
  have hall : ∀ q ∈ Finset.Icc 1 y, ∀ᵐ ω ∂μ, q.Prime → ‖X q ω‖ = 1 := by
    intro q _
    by_cases hq : q.Prime
    · filter_upwards [ae_norm_X_eq_one hX hν hq] with ω h _ using h
    · exact Filter.Eventually.of_forall fun ω h => absurd h hq
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
  intro p hp hpy
  have hpR : ((y : ℝ) + 1) ≤ (p : ℝ) := by exact_mod_cast hpy
  have hp0 : (0 : ℝ) < p := by linarith [Nat.cast_nonneg (α := ℝ) y]
  -- every `k` in range is at most `y`
  have hk_le : ∀ k ∈ Finset.Icc 1 ⌊x / (p : ℕ)⌋₊, k ≤ y := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    have hkR : (k : ℝ) ≤ x / p := le_trans (by exact_mod_cast hk2) (Nat.floor_le (by positivity))
    rw [le_div_iff₀ hp0] at hkR
    have : (k : ℝ) < (y : ℝ) + 1 := by nlinarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  rw [roughCoeffOf, randomSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.1 hk).1; omega
  refine hext.congr_primeFactors fun q hq => ?_
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqk : q ≤ k := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq)
  have hqy : q ≤ y := le_trans hqk (hk_le k hk)
  have hqmem : (⟨q, hqp⟩ : Nat.Primes) ∈ smallPrimes y := mem_smallPrimes.2 hqy
  have hnorm : ‖X q ω‖ = 1 :=
    hω q (Finset.mem_Icc.2 ⟨hqp.one_lt.le, hqy⟩) hqp
  have hres : primeRestrict (smallPrimes y)
      (fun i : smallPrimes y => X ((i : Nat.Primes) : ℕ) ω) q = X q ω :=
    primeRestrict_apply_of_mem (i := (⟨q, hqp⟩ : Nat.Primes)) hqmem _
  rw [unitize, hres, if_pos hnorm]

/-! ### Khintchine applied to the rough part

`RMF.randomSum_sub_smoothPartial_eq` presents the rough part as a linear form in the large primes,
`RMF.ae_roughCoeffOf_eq` presents its coefficients as a function of the small-prime data, and
`RMF.indepFun_primeRestrict` separates the two.  Feeding these to `RMF.khintchine_lower_indep` and
following with `RMF.integral_rough_leOf` bounds the mean square sum by the moment of the full
partial sum. -/

/-- The large primes, as a set of naturals. -/
noncomputable def largePrimeSet (y N : ℕ) : Finset ℕ := {p ∈ Finset.Ioc y N | p.Prime}

lemma mem_largePrimeSet {y N p : ℕ} : p ∈ largePrimeSet y N ↔ (y < p ∧ p ≤ N) ∧ p.Prime := by
  rw [largePrimeSet, Finset.mem_filter, Finset.mem_Ioc]

omit [MeasurableSpace Ω] in
/-- The padded large-prime data is the linear form's variable, in the shape Khintchine wants. -/
lemma primeRestrict_largePrimes_eqOf {ext : (ℕ → ℂ) → ArithmeticFunction ℂ}
    (happ : ∀ (v : ℕ → ℂ) (p : ℕ), p.Prime → ext v p = v p)
    {X : ℕ → Ω → ℂ} (y N : ℕ) (ω : Ω) :
    (primeRestrict (largePrimes y N) fun i : largePrimes y N => X ((i : Nat.Primes) : ℕ) ω)
      = fun n => if n ∈ largePrimeSet y N then ext (fun q => X q ω) n else 0 := by
  funext n
  by_cases hn : n ∈ largePrimeSet y N
  · obtain ⟨⟨hy, hN⟩, hp⟩ := mem_largePrimeSet.1 hn
    rw [if_pos hn, happ _ _ hp]
    exact primeRestrict_apply_of_mem (i := (⟨n, hp⟩ : Nat.Primes)) (mem_largePrimes.2 ⟨hy, hN⟩) _
  · rw [if_neg hn]
    refine primeRestrict_apply_of_notMem (fun i hi hin => hn ?_) _
    obtain ⟨hy, hN⟩ := mem_largePrimes.1 hi
    exact mem_largePrimeSet.2 ⟨⟨hin ▸ hy, hin ▸ hN⟩, hin ▸ i.2⟩

/-- **Symmetrisation and Khintchine, assembled.**  The mean square sum over the large primes is
controlled by the `2q`-th moment of the full partial sum. -/
theorem khintchine_roughOf {ext : (ℕ → ℂ) → ArithmeticFunction ℂ}
    (hext : IsCoeffExtension ext) {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure ℂ} (hX : IsIIDPrimeValues X ν μ) (hν : ∀ᵐ z ∂ν, ‖z‖ = 1)
    (hf : IsOrthonormalAtPrimes (fun ω => ext fun p => X p ω) μ)
    (hmul : ∀ ω : Ω, (ext fun q => X q ω).IsMultiplicative)
    (happ : ∀ (v : ℕ → ℂ) (p : ℕ), p.Prime → ext v p = v p)
    {x : ℝ} {y : ℕ} (hx : 1 ≤ x)
    (hxy : ⌊x⌋₊ < (y + 1) ^ 2)
    (hc : ∀ p : ℕ, 0 < p → Measure.map (fun z : ℂ => flipSign y p * z) ν = ν)
    (hsign : ∀ (v : ℕ → ℂ) (n : ℕ), n ≠ 0 → n < (y + 1) ^ 2 →
      ext (fun p => flipSign y p * v p) n
        = (if n ∈ Nat.smoothNumbers (y + 1) then (1 : ℂ) else -1) * ext v n)
    (hbd : ∀ Y : ℕ → Ω → ℂ, IsIIDPrimeValues Y ν μ →
      IsBoundedRMF (fun ω => ext fun p => Y p ω) μ)
    (hmeasExt : ∀ n : ℕ, Measurable fun v : Nat.Primes → ℂ => ext (primeExtend v) n)
    (hcongrP : ∀ {v w : ℕ → ℂ}, (∀ p, p.Prime → v p = w p) → ext v = ext w)
    {K : ℝ} (hK0 : 0 < K)
    (hfour : ∀ v : ℕ → ℂ, (∫ ω, ‖primeLinearForm
        (fun ω => ext fun q => X q ω) (largePrimeSet y ⌊x⌋₊) v ω‖ ^ (4 : ℝ) ∂μ)
      ≤ K * (∑ p ∈ largePrimeSet y ⌊x⌋₊, ‖v p‖ ^ 2) ^ 2)
    {q : ℝ} (hq23 : 2 / 3 ≤ q) (hq1 : q ≤ 1) :
    K ^ (-(1 - q)) * ∫ ω, (∑ p ∈ largePrimeSet y ⌊x⌋₊,
        ‖randomSum (fun ω => ext fun q => X q ω) (x / p) ω‖ ^ 2) ^ q ∂μ
      ≤ ∫ ω, ‖randomSum (fun ω => ext fun q => X q ω) x ω‖ ^ (2 * q) ∂μ := by
  set f : Ω → ArithmeticFunction ℂ := fun ω => ext fun q => X q ω with hfdef
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hq0 : (1 : ℝ) ≤ 2 * q := by linarith
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
    rw [primeRestrict_largePrimes_eqOf happ]
  have hind : ProbabilityTheory.IndepFun W (fun ω n => if n ∈ s then f ω n else 0) μ := by
    rw [hZ]
    exact indepFun_primeRestrict hX _ _ (disjoint_smallPrimes_largePrimes y ⌊x⌋₊)
  -- Khintchine
  have hkh := khintchine_lower_indep hf hs hW (C := roughCoeffOf ext x)
    (fun p => measurable_roughCoeffOf hext x p) hK0
    (fun v => hfour (roughCoeffOf ext x v))
    (B := (⌊x⌋₊ : ℝ))
    (fun v p hp => norm_roughCoeffOf_le hext hx0 (hs p hp).one_lt.le v) hind hq23 hq1
  -- identify the coefficients
  have hae := ae_roughCoeffOf_eq hext hX hν hx hxy
  have hL : (∫ ω, (∑ p ∈ s, ‖roughCoeffOf ext x (W ω) p‖ ^ 2) ^ q ∂μ)
      = ∫ ω, (∑ p ∈ s, ‖randomSum f (x / p) ω‖ ^ 2) ^ q ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    refine congrArg (· ^ q) (Finset.sum_congr rfl fun p hp => ?_)
    obtain ⟨⟨hy, _⟩, hprime⟩ := mem_largePrimeSet.1 hp
    rw [hω p hprime hy]
  have hR : (∫ ω, ‖∑ p ∈ s, roughCoeffOf ext x (W ω) p * f ω p‖ ^ (2 * q) ∂μ)
      ≤ ∫ ω, ‖randomSum f x ω‖ ^ (2 * q) ∂μ := by
    refine le_trans (le_of_eq (integral_congr_ae ?_))
      (integral_rough_leOf hX hc hsign hbd hmeasExt hcongrP hxy hq0)
    filter_upwards [hae] with ω hω
    have hsum : (∑ p ∈ s, roughCoeffOf ext x (W ω) p * f ω p)
        = ∑ p ∈ s, f ω p * randomSum f (x / p) ω := by
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨⟨hy, _⟩, hprime⟩ := mem_largePrimeSet.1 hp
      rw [hω p hprime hy, mul_comm]
    have hset : s = {p ∈ Finset.Icc 1 ⌊x⌋₊ | p.Prime ∧ y < p} := by
      ext p
      rw [hsdef, mem_largePrimeSet, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hy, hN⟩, hp⟩
        exact ⟨⟨hp.one_lt.le, hN⟩, hp, hy⟩
      · rintro ⟨⟨_, hN⟩, hp, hy⟩
        exact ⟨⟨hy, hN⟩, hp⟩
    rw [hsum, hset,
      ← randomSum_sub_smoothPartial_eq (f := f) hx hxy
        (hmul ω)]
  rw [hL] at hkh
  exact le_trans hkh hR

/-! ### Three facts for the Rademacher instance -/

omit [MeasurableSpace Ω] in
/-- `RMF.flipSign` takes only the values `±1`, which is what `RMF.map_mul_left_rademacherLaw`
asks for. -/
lemma flipSign_eq_one_or_neg_one (y p : ℕ) : flipSign y p = 1 ∨ flipSign y p = -1 := by
  rw [flipSign]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [MeasurableSpace Ω] in
/-- The squarefree extension is determined by the values at the primes.  The mirror of
`RMF.compMultExtension_congr_primes`. -/
lemma squarefreeExtension_congr_primes {v w : ℕ → ℂ} (h : ∀ p, p.Prime → v p = w p) :
    squarefreeExtension v = squarefreeExtension w := by
  ext n
  exact squarefreeExtension_congr fun p hp => h p (Nat.prime_of_mem_primeFactors hp)

omit [MeasurableSpace Ω] in
/-- The mirror of `RMF.measurable_compMultExtension_primeExtend`. -/
lemma measurable_squarefreeExtension_primeExtend (n : ℕ) :
    Measurable fun v : Nat.Primes → ℂ => squarefreeExtension (primeExtend v) n := by
  by_cases hsf : Squarefree n
  · have heq : (fun v : Nat.Primes → ℂ => squarefreeExtension (primeExtend v) n)
        = fun v => ∏ p ∈ n.primeFactors, primeExtend v p := by
      funext v
      exact squarefreeExtension_apply_of_squarefree _ hsf
    rw [heq]
    exact Finset.measurable_prod _ fun p _ => measurable_primeExtend p
  · have heq : (fun v : Nat.Primes → ℂ => squarefreeExtension (primeExtend v) n) = fun _ => 0 := by
      funext v
      exact squarefreeExtension_apply_of_not_squarefree _ hsf
    rw [heq]
    exact measurable_const

/-- **Khintchine on the rough part, for the Rademacher function**: the `RMF.squarefreeExtension`
and `RMF.rademacherLaw` instance of `RMF.khintchine_roughOf`, its hypotheses met by
`RMF.isCoeffExtension_squarefreeExtension`, `RMF.IsRademacherRMF.isOrthonormalAtPrimes`,
`RMF.isMultiplicative_squarefreeExtension`, `RMF.squarefreeExtension_apply_prime`,
`RMF.map_mul_left_rademacherLaw`, `RMF.squarefreeExtension_flipSign`,
`RMF.IsRademacherRMF.isBoundedRMF` and the three lemmas above. -/
theorem khintchine_rough_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} {y : ℕ} (hx : 1 ≤ x)
    (hxy : ⌊x⌋₊ < (y + 1) ^ 2) {K : ℝ} (hK0 : 0 < K)
    (hfour : ∀ v : ℕ → ℂ, (∫ ω, ‖primeLinearForm
        (fun ω => squarefreeExtension fun q => X q ω) (largePrimeSet y ⌊x⌋₊) v ω‖ ^ (4 : ℝ) ∂μ)
      ≤ K * (∑ p ∈ largePrimeSet y ⌊x⌋₊, ‖v p‖ ^ 2) ^ 2)
    {q : ℝ} (hq23 : 2 / 3 ≤ q) (hq1 : q ≤ 1) :
    K ^ (-(1 - q)) * ∫ ω, (∑ p ∈ largePrimeSet y ⌊x⌋₊,
        ‖randomSum (fun ω => squarefreeExtension fun q => X q ω) (x / p) ω‖ ^ 2) ^ q ∂μ
      ≤ ∫ ω, ‖randomSum (fun ω => squarefreeExtension fun q => X q ω) x ω‖ ^ (2 * q) ∂μ :=
  khintchine_roughOf isCoeffExtension_squarefreeExtension hX norm_eq_one_rademacherLaw
    (IsRademacherRMF.isOrthonormalAtPrimes hX.isRademacherRMF)
    (fun ω => isMultiplicative_squarefreeExtension fun q => X q ω)
    (fun v _ hp => squarefreeExtension_apply_prime v hp) hx hxy
    (fun p _ => map_mul_left_rademacherLaw (flipSign_eq_one_or_neg_one y p))
    (fun _ _ hn hn2 => squarefreeExtension_flipSign hn hn2)
    (fun _ hY => IsRademacherRMF.isBoundedRMF (IsRademacherPrimeValues.isRademacherRMF hY))
    measurable_squarefreeExtension_primeExtend
    (fun h => squarefreeExtension_congr_primes h)
    hK0 hfour hq23 hq1

/-- **Khintchine on the rough part, for the Steinhaus function**: the
`RMF.compMultExtension` and `RMF.steinhausLaw` instance of `RMF.khintchine_roughOf`. -/
theorem khintchine_rough {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsSteinhausPrimeValues X μ) {x : ℝ} {y : ℕ} (hx : 1 ≤ x)
    (hxy : ⌊x⌋₊ < (y + 1) ^ 2) {K : ℝ} (hK0 : 0 < K)
    (hfour : ∀ v : ℕ → ℂ, (∫ ω, ‖primeLinearForm
        (fun ω => compMultExtension fun q => X q ω) (largePrimeSet y ⌊x⌋₊) v ω‖ ^ (4 : ℝ) ∂μ)
      ≤ K * (∑ p ∈ largePrimeSet y ⌊x⌋₊, ‖v p‖ ^ 2) ^ 2)
    {q : ℝ} (hq23 : 2 / 3 ≤ q) (hq1 : q ≤ 1) :
    K ^ (-(1 - q)) * ∫ ω, (∑ p ∈ largePrimeSet y ⌊x⌋₊,
        ‖randomSum (fun ω => compMultExtension fun q => X q ω) (x / p) ω‖ ^ 2) ^ q ∂μ
      ≤ ∫ ω, ‖randomSum (fun ω => compMultExtension fun q => X q ω) x ω‖ ^ (2 * q) ∂μ :=
  khintchine_roughOf isCoeffExtension_compMultExtension hX norm_eq_one_steinhausLaw
    (IsSteinhausRMF.isOrthonormalAtPrimes hX.isSteinhausRMF)
    (fun ω => isMultiplicative_compMultExtension fun q => X q ω)
    (fun v _ hp => compMultExtension_apply_prime v hp) hx hxy
    (fun p _ => map_mul_left_steinhausLaw (norm_flipSign y p))
    (fun _ _ hn hn2 => compMultExtension_flipSign hn hn2)
    (fun _ hY => IsSteinhausRMF.isBoundedRMF (IsSteinhausPrimeValues.isSteinhausRMF hY))
    measurable_compMultExtension_primeExtend (fun h => compMultExtension_congr_primes h)
    hK0 hfour hq23 hq1

end RMF
