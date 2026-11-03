/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.EulerProduct.Basic
import RMF.Basic

/-!
# Random Euler products

The partial Euler product of a random multiplicative function over the primes below `y`.
These are the central objects in Harper's work: on the critical line the full product does
not converge, so one works with partial products `∏_{p < y}` and lets `y` grow.

## Well-definedness

Two separate finiteness questions arise, and they are answered differently.

* *Over the primes*: the product is always capped at `y`, hence finite.  Nothing is needed.
* *At each prime*: the local factor is the local Dirichlet series
  `∑_{k} f (p ^ k) · (p ^ (-s)) ^ k` (`RMF.localFactor`), an infinite sum.  This needs a
  growth hypothesis on `f` at prime powers.

The local series is a power series in `p ^ (-s)`, so geometric growth at each prime,
`‖f (p ^ k)‖ ≤ r ^ k` for some `r < p ^ s.re`, puts its abscissa of convergence to the left of `s`.

The case used for the applications is `‖f (p ^ k)‖ ≤ 1` with `0 < s.re`, since `1 < p ^ s.re`
there.  All three classical random multiplicative functions satisfy it — Steinhaus and extended
Rademacher have modulus exactly one, Rademacher modulus `0` or `1` — and it covers the critical
line `s = 1/2 + it` where Harper works.  Since only almost sure statements are needed downstream,
the bound is imposed almost everywhere in the random results.

## The two conventions

The definition is uniform: one Euler product for every random multiplicative function.  The
familiar closed forms of the local factors are theorems, one per extension convention:

* `RMF.localFactor_compMultExtension`: `(1 - f p · p ^ (-s))⁻¹` — Steinhaus and extended
  Rademacher;
* `RMF.localFactor_squarefreeExtension`: `1 + f p · p ^ (-s)` — Rademacher.  The local
  series terminates here, since the value at `p ^ k` vanishes for `k ≥ 2`.
-/

open Finset MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Definitions -/

/-- The local factor of `f` at the prime `p`: the local Dirichlet series
`∑_k f (p ^ k) · (p ^ (-s)) ^ k`. -/
noncomputable def localFactor (f : ℕ → ℂ) (p : ℕ) (s : ℂ) : ℂ :=
  ∑' k : ℕ, f (p ^ k) * ((p : ℂ) ^ (-s)) ^ k

/-- The partial Euler product of `f` over the primes below `y`. -/
noncomputable def eulerProduct (f : ℕ → ℂ) (y : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ Nat.primesBelow y, localFactor f p s

/-- The random Euler product `∏_{p < y} ∑_{k ≥ 0} f(p^k) p^{-ks}`; closed forms for the classical
functions are the `randomEulerProduct_eq` theorems below. -/
noncomputable def randomEulerProduct (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (s : ℂ) (ω : Ω) :
    ℂ := eulerProduct (fun n => f ω n) y s

/-! ### Convergence of the local factor -/

/-- A prime power grows: `1 < p ^ σ` for `σ > 0`. -/
lemma one_lt_prime_rpow {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 < σ) : 1 < (p : ℝ) ^ σ :=
  (Real.one_lt_rpow_iff_of_pos (by exact_mod_cast hp.pos)).2
    (Or.inl ⟨by exact_mod_cast hp.one_lt, hσ⟩)

/-! ### The two closed forms -/

/-- The modulus of `p ^ (-s)` is less than one for a prime `p` and `s` to the right of the
imaginary axis. -/
lemma norm_prime_cpow_neg_lt_one {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

/-- **Steinhaus and extended Rademacher.**  For a completely multiplicative function the
local factor is the familiar `(1 - f p · p ^ (-s))⁻¹`. -/
lemma localFactor_compMultExtension (x : ℕ → ℂ) {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hx : ‖x p‖ < (p : ℝ) ^ s.re) :
    localFactor (fun n => compMultExtension x n) p s = (1 - x p * (p : ℂ) ^ (-s))⁻¹ := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hz : ‖x p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re,
      Real.rpow_neg hp0.le, ← div_eq_mul_inv, div_lt_one (Real.rpow_pos_of_pos hp0 _)]
    exact hx
  rw [localFactor, ← tsum_geometric_of_norm_lt_one hz]
  refine tsum_congr fun k => ?_
  rw [compMultExtension_apply_prime_pow _ hp, mul_pow]

/-- **Rademacher.**  For the squarefree-supported convention the local series has only two
nonzero terms, giving the factor `1 + f p · p ^ (-s)`. -/
lemma localFactor_squarefreeExtension (x : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (s : ℂ) :
    localFactor (fun n => squarefreeExtension x n) p s = 1 + x p * (p : ℂ) ^ (-s) := by
  rw [localFactor, tsum_eq_sum (s := {0, 1}) fun k hk => ?_]
  · rw [Finset.sum_pair (by norm_num)]
    simp [squarefreeExtension_apply_prime _ hp]
  · have hk2 : 2 ≤ k := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      omega
    rw [squarefreeExtension_apply_prime_pow _ hp hk2, zero_mul]

/-! ### The Euler product -/

lemma primesBelow_eq_empty {y : ℕ} (hy : y ≤ 2) : Nat.primesBelow y = ∅ := by
  ext p
  simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty,
    iff_false, not_and]
  intro hpy hp
  exact absurd hp.two_le (by omega)

@[simp]
lemma eulerProduct_of_le_two (f : ℕ → ℂ) {y : ℕ} (hy : y ≤ 2) (s : ℂ) :
    eulerProduct f y s = 1 := by
  rw [eulerProduct, primesBelow_eq_empty hy, Finset.prod_empty]

/-- The Euler product of a completely multiplicative function, in closed form. -/
lemma eulerProduct_compMultExtension (x : ℕ → ℂ) (y : ℕ) {s : ℂ}
    (hx : ∀ p ∈ Nat.primesBelow y, ‖x p‖ < (p : ℝ) ^ s.re) :
    eulerProduct (fun n => compMultExtension x n) y s
      = ∏ p ∈ Nat.primesBelow y, (1 - x p * (p : ℂ) ^ (-s))⁻¹ :=
  Finset.prod_congr rfl fun p hp =>
    localFactor_compMultExtension x (Nat.prime_of_mem_primesBelow hp) (hx p hp)

/-- The Euler product of a squarefree-supported function, in closed form. -/
lemma eulerProduct_squarefreeExtension (x : ℕ → ℂ) (y : ℕ) (s : ℂ) :
    eulerProduct (fun n => squarefreeExtension x n) y s
      = ∏ p ∈ Nat.primesBelow y, (1 + x p * (p : ℂ) ^ (-s)) :=
  Finset.prod_congr rfl fun _p hp =>
    localFactor_squarefreeExtension x (Nat.prime_of_mem_primesBelow hp) s

/-! ### The three classical products

The definition is the same for all three; what differs is the closed form of the local
factors, and — for the two completely multiplicative cases — that the closed form holds
almost everywhere rather than pointwise, since the bound `‖f ω p‖ ≤ 1` is a statement about
the law.
-/

/-- If the law of the values at the primes is carried by the closed unit disc, then almost surely
`‖X p‖ ≤ 1` for every prime `p < y`. -/
lemma ae_forall_norm_le_one {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) (y : ℕ) :
    ∀ᵐ ω ∂μ, ∀ p ∈ Nat.primesBelow y, ‖X p ω‖ ≤ 1 := by
  refine (Filter.eventually_all_finset _).2 fun p hp => ?_
  have hmeasP : Measurable fun z : ℂ => ‖z‖ ≤ 1 :=
    measurableSet_setOf.1 (measurableSet_le measurable_norm measurable_const)
  exact ((hX.hasLaw p (Nat.prime_of_mem_primesBelow hp)).ae_iff hmeasP).2 hν

omit [MeasurableSpace Ω] in
/-- Closed form in the completely multiplicative case, at any `ω` where the values at the
relevant primes are bounded by one. -/
lemma randomEulerProduct_compMult_eq {X : ℕ → Ω → ℂ} {y : ℕ} {s : ℂ} (hs : 0 < s.re) {ω : Ω}
    (hω : ∀ p ∈ Nat.primesBelow y, ‖X p ω‖ ≤ 1) :
    randomEulerProduct (fun ω => compMultExtension fun p => X p ω) y s ω
      = ∏ p ∈ Nat.primesBelow y, (1 - X p ω * (p : ℂ) ^ (-s))⁻¹ :=
  eulerProduct_compMultExtension _ y fun p hp =>
    lt_of_le_of_lt (hω p hp) (one_lt_prime_rpow (Nat.prime_of_mem_primesBelow hp) hs)

/-- **The Steinhaus random Euler product**: almost surely
`∏_{p < y} (1 - f ω p · p ^ (-s))⁻¹`. -/
theorem IsSteinhausRMF.randomEulerProduct_eq {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ∀ᵐ ω ∂μ, randomEulerProduct f y s ω
      = ∏ p ∈ Nat.primesBelow y, (1 - f ω p * (p : ℂ) ^ (-s))⁻¹ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  filter_upwards [ae_forall_norm_le_one hX norm_le_one_steinhausLaw y] with ω hω
  rw [randomEulerProduct_compMult_eq hs hω]
  exact Finset.prod_congr rfl fun p hp => by
    rw [compMultExtension_apply_prime _ (Nat.prime_of_mem_primesBelow hp)]

/-- **The Rademacher random Euler product**: `∏_{p < y} (1 + f ω p · p ^ (-s))`.  Unlike the
other two this needs no hypothesis on `s` or on `ω` — the local series terminates. -/
theorem IsRademacherRMF.randomEulerProduct_eq {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (y : ℕ) (s : ℂ) (ω : Ω) :
    randomEulerProduct f y s ω = ∏ p ∈ Nat.primesBelow y, (1 + f ω p * (p : ℂ) ^ (-s)) := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  rw [randomEulerProduct, eulerProduct_squarefreeExtension _ y s]
  exact Finset.prod_congr rfl fun p hp => by
    rw [squarefreeExtension_apply_prime _ (Nat.prime_of_mem_primesBelow hp)]

end RMF
