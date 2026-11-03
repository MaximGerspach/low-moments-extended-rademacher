/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import RMF.Analysis.ShiftWeight
import RMF.EulerProduct.Defs
import RMF.Probability.PrimeValues

/-!
# Ingredients for the periodisation step

Hamdan's final step in §2.1 trades the line integral `∫_ℝ |A(1/2+it)/(1/2+it)|² dt` for the unit
integral `∫_0^1 |A(1/2+ih)|² dh`.  The mechanism is:

* split `∫_ℝ` into `∑_{n ∈ ℤ} ∫_n^{n+1}`;
* on `[n, n+1]` bound `|1/2+it|⁻²` by `8/(1+n²)` (`RMF.one_add_sq_div_eight_le`);
* take `q`-th powers and use subadditivity of `x ↦ x^q` for `q ≤ 1`, which for a countable sum is
  `RMF.rpow_tsum_le_tsum_rpow`;
* shift each `∫_n^{n+1}` back to `[0,1]`, which is where rotation-invariance of the Steinhaus law
  enters through `IsSteinhausPrimeValues.mul_unimodular`.
-/

open MeasureTheory

open scoped ENNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

-- The abscissa.  Everything below holds for any `σ ≥ 1/2`: raising the line only shrinks each
-- local factor (`|p^{-s}| = p^{-σ} ≤ p^{-1/2}`) and only grows the divisor (`|σ+it| ≥ |1/2+it|`),
-- so `eulerBound` and the constant `8` are unchanged.
variable (σ : ℝ)

/-! ### Subadditivity of `x ↦ x^q` over a countable sum

Mathlib has the two-term inequality (`ENNReal.rpow_add_le_add_rpow`) but not the `tsum` version.
Working in `ℝ≥0∞` is what makes the statement unconditional: no summability hypothesis, and no
side condition on the terms.

`0 < q` is genuinely needed and not just convenient: at `q = 0` over an empty index the left side
is `0^0 = 1` and the right side is `0`. -/
theorem rpow_tsum_le_tsum_rpow {ι : Type*} (z : ι → ℝ≥0∞) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑' i, z i) ^ q ≤ ∑' i, z i ^ q := by
  classical
  have hfin : ∀ s : Finset ι, (∑ i ∈ s, z i) ^ q ≤ ∑ i ∈ s, z i ^ q := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [ENNReal.zero_rpow_of_pos hq0]
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        exact le_trans (ENNReal.rpow_add_le_add_rpow _ _ hq0.le hq1) (by gcongr)
  have hsum : (∑' i, z i) ≤ (∑' i, z i ^ q) ^ (1 / q) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have hle := ENNReal.rpow_le_rpow
      (le_trans (hfin s) (ENNReal.sum_le_tsum s)) (one_div_pos.2 hq0).le
    rwa [← ENNReal.rpow_mul, mul_one_div, div_self hq0.ne', ENNReal.rpow_one] at hle
  calc (∑' i, z i) ^ q ≤ ((∑' i, z i ^ q) ^ (1 / q)) ^ q := ENNReal.rpow_le_rpow hsum hq0.le
    _ = ∑' i, z i ^ q := by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]

/-! ### The pointwise bound on the critical line

`|1/2 + it|² = 1/4 + t²`, and on `t ∈ [n, n+1]` this is at least `(1+n²)/8`.  The constant `8` is
sharp at `n = -1`, where `t` may be `0` and the two sides are `1/4` and `2/8`. -/

lemma normSq_ofReal_add_mul_I (t : ℝ) :
    ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = σ ^ 2 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

/-- On `[n, n+1]` the weight `1/|1/2+it|²` is at most `8/(1+n²)`.

Both signs need their own argument: for `n ≥ 0` the minimum of `t²` is at `t = n`, for `n ≤ -1`
it is at `t = n+1`, and the resulting polynomial inequality `(7n+9)(n+1) ≥ 0` is where the `8`
comes from. -/
lemma one_add_sq_div_eight_le {n : ℤ} {t : ℝ} (h0 : (n : ℝ) ≤ t) (h1 : t ≤ (n : ℝ) + 1) :
    (1 + (n : ℝ) ^ 2) / 8 ≤ 1 / 4 + t ^ 2 := by
  rcases le_or_gt 0 n with hn | hn
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - t)]
  · rcases eq_or_lt_of_le (by omega : n ≤ -1) with hn1 | hn1
    · have : (n : ℝ) = -1 := by rw [hn1]; norm_num
      rw [this]
      nlinarith [sq_nonneg t]
    · have hn2 : (n : ℝ) ≤ -2 := by
        have : n ≤ -2 := by omega
        exact_mod_cast this
      have ht2 : ((n : ℝ) + 1) ^ 2 ≤ t ^ 2 := by nlinarith
      nlinarith [ht2]

/-- The same bound in the form the integrand needs. -/
lemma norm_div_sq_le (hσ : 1 / 2 ≤ σ) {n : ℤ} {t : ℝ} (h0 : (n : ℝ) ≤ t)
    (h1 : t ≤ (n : ℝ) + 1) (z : ℂ) :
    ‖z / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 ≤ 8 / (1 + (n : ℝ) ^ 2) * ‖z‖ ^ 2 := by
  have hden : (0 : ℝ) < σ ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hnsq : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := by positivity
  have hlow : (1 + (n : ℝ) ^ 2) / 8 ≤ σ ^ 2 + t ^ 2 := by
    have h14 : (1 : ℝ) / 4 ≤ σ ^ 2 := by nlinarith
    linarith [one_add_sq_div_eight_le h0 h1]
  have hstep : ‖z‖ ^ 2 / (σ ^ 2 + t ^ 2) ≤ ‖z‖ ^ 2 / ((1 + (n : ℝ) ^ 2) / 8) := by
    gcongr
  rw [norm_div, div_pow, normSq_ofReal_add_mul_I]
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-! ### Shifting the critical line

Moving from `½ + i(h+n)` to `½ + ih` multiplies the value at each prime by `p^{-in}`, which is
unimodular.  Everything here is an identity between Euler products — no probability yet; the
probability enters when `RMF.IsSteinhausPrimeValues.integral_comp_rotate` is applied to the
resulting family. -/

/-- The rotation constant at `p` induced by shifting the line by `n`. -/
noncomputable def shiftConst (n : ℝ) (p : ℕ) : ℂ := (p : ℂ) ^ (-(n : ℂ) * Complex.I)

lemma norm_shiftConst (n : ℝ) {p : ℕ} (hp : 0 < p) : ‖shiftConst n p‖ = 1 := by
  rw [shiftConst, Complex.norm_natCast_cpow_of_pos hp]
  simp

/-- The local factor at `p` of a completely multiplicative extension, shifted. -/
lemma localFactor_shift (x : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (s : ℂ) (n : ℝ) :
    localFactor (fun m => compMultExtension x m) p (s + (n : ℂ) * Complex.I)
      = localFactor (fun m => compMultExtension (fun q => shiftConst n q * x q) m) p s := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.pos.ne'
  have hbase : x p * (p : ℂ) ^ (-(s + (n : ℂ) * Complex.I))
      = shiftConst n p * x p * (p : ℂ) ^ (-s) := by
    rw [shiftConst, show -(s + (n : ℂ) * Complex.I) = -s + -(n : ℂ) * Complex.I by ring,
      Complex.cpow_add _ _ hp0]
    ring
  rw [localFactor, localFactor]
  refine tsum_congr fun k => ?_
  rw [compMultExtension_apply_prime_pow _ hp, compMultExtension_apply_prime_pow _ hp,
    ← mul_pow, ← mul_pow, hbase]

/-- The partial Euler product, shifted. -/
lemma eulerProduct_shift (x : ℕ → ℂ) (y : ℕ) (s : ℂ) (n : ℝ) :
    eulerProduct (fun m => compMultExtension x m) y (s + (n : ℂ) * Complex.I)
      = eulerProduct (fun m => compMultExtension (fun q => shiftConst n q * x q) m) y s :=
  Finset.prod_congr rfl fun _ hp => localFactor_shift x (Nat.prime_of_mem_primesBelow hp) s n

omit [MeasurableSpace Ω] in
/-- **The shift, on the random Euler product.**  Evaluating at `s + in` is the same as rotating
every prime value by `p^{-in}` and evaluating at `s`. -/
lemma randomEulerProduct_shift {X : ℕ → Ω → ℂ} (y : ℕ) (s : ℂ) (n : ℝ) (ω : Ω) :
    randomEulerProduct (fun ω => compMultExtension fun p => X p ω) y
        (s + (n : ℂ) * Complex.I) ω
      = randomEulerProduct (fun ω => compMultExtension fun p => shiftConst n p * X p ω) y s ω :=
  eulerProduct_shift _ y s n

/-! ### The Euler product as a functional of the prime values

`RMF.IsSteinhausPrimeValues.integral_comp_rotate` transports a measurable functional of the family
`Nat.Primes → ℂ`, so the unit integral has to be presented in that form.  Two adjustments are
needed: the values must be extended from `Nat.Primes` to `ℕ` (`RMF.primeExtend`), and
`RMF.localFactor`'s `tsum` must be replaced by its closed form (`RMF.eulerClosed`), which is
manifestly measurable in the values whereas a `tsum` is not. -/

/-- The values at the primes, extended by zero to all of `ℕ`. -/
noncomputable def primeExtend (x : Nat.Primes → ℂ) (n : ℕ) : ℂ :=
  if h : n.Prime then x ⟨n, h⟩ else 0

lemma primeExtend_apply (x : Nat.Primes → ℂ) {p : ℕ} (hp : p.Prime) :
    primeExtend x p = x ⟨p, hp⟩ := dif_pos hp

lemma measurable_primeExtend (n : ℕ) :
    Measurable fun x : Nat.Primes → ℂ => primeExtend x n := by
  unfold primeExtend
  split
  · exact measurable_pi_apply _
  · exact measurable_const

/-- `compMultExtension` reads only the values at the primes. -/
lemma compMultExtension_congr_primes {x y : ℕ → ℂ} (h : ∀ p, p.Prime → x p = y p) :
    compMultExtension x = compMultExtension y := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [compMultExtension_apply_of_ne_zero _ hn, compMultExtension_apply_of_ne_zero _ hn]
    refine Finset.prod_congr rfl fun p hp => ?_
    simp only
    rw [h p (Nat.prime_of_mem_primeFactors (by simpa using hp))]

/-- The closed form of the partial Euler product, as a function of the values at the primes. -/
noncomputable def eulerClosed (x : Nat.Primes → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ Nat.primesBelow N, (1 - primeExtend x p * (p : ℂ) ^ (-s))⁻¹

/-! ### Measurability of the functional

The parameter integral `x ↦ ∫₀¹ ‖eulerClosed x N (½+ih)‖² dh` is measurable because the integrand is
jointly measurable in `(x, h)`; `StronglyMeasurable.integral_prod_right'` then does the rest. -/

lemma measurable_eulerClosed_uncurry (σ : ℝ) (N : ℕ) :
    Measurable fun z : (Nat.Primes → ℂ) × ℝ =>
      eulerClosed z.1 N ((σ : ℂ) + (z.2 : ℂ) * Complex.I) := by
  unfold eulerClosed
  refine Finset.measurable_prod _ fun p hp => ?_
  have hp0 : (p : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.prime_of_mem_primesBelow hp).pos.ne'
  have hcont : Continuous fun t : ℝ => (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl hp0)
  refine Measurable.inv (measurable_const.sub ?_)
  exact ((measurable_primeExtend p).comp measurable_fst).mul
    (hcont.measurable.comp measurable_snd)

/-- The unit integral of `‖A_y‖²`, as a functional of the values at the primes. -/
noncomputable def unitFunctional (σ : ℝ) (N : ℕ) (x : Nat.Primes → ℂ) : ℝ :=
  ∫ h in Set.Ioc (0 : ℝ) 1, ‖eulerClosed x N ((σ : ℂ) + (h : ℂ) * Complex.I)‖ ^ 2

lemma measurable_unitFunctional (σ : ℝ) (N : ℕ) : Measurable (unitFunctional σ N) := by
  unfold unitFunctional
  refine StronglyMeasurable.measurable ?_
  exact MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (((measurable_eulerClosed_uncurry σ N).norm.pow_const 2).stronglyMeasurable)

/-! ### Rotation invariance of the unit window

Putting the pieces together: the unit integral is `unitFunctional` of the family, the shifted
window is `unitFunctional` of the *rotated* family, and rotation does not change the expectation. -/

omit [MeasurableSpace Ω] in
/-- At any `ω` where the relevant values are bounded by one, the functional agrees with the random
Euler product. -/
lemma eulerClosed_eq_randomEulerProduct {X : ℕ → Ω → ℂ} {N : ℕ} {s : ℂ} (hs : 0 < s.re)
    {ω : Ω} (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    eulerClosed (fun p : Nat.Primes => X (p : ℕ) ω) N s
      = randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N s ω := by
  rw [randomEulerProduct_compMult_eq hs hω, eulerClosed]
  exact Finset.prod_congr rfl fun p hp => by
    rw [primeExtend_apply _ (Nat.prime_of_mem_primesBelow hp)]

/-- **The expectation of the `q`-th power of the unit window is rotation invariant.**  This is the
probabilistic content of the periodisation step, in the form the assembly needs. -/
theorem integral_rpow_unitFunctional_rotate {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (N : ℕ) (n : ℝ) (q : ℝ) :
    ∫ ω, unitFunctional σ N (fun p => shiftConst n (p : ℕ) * X (p : ℕ) ω) ^ q ∂μ
      = ∫ ω, unitFunctional σ N (fun p => X (p : ℕ) ω) ^ q ∂μ := by
  have hm := measurable_unitFunctional σ N
  exact hX.integral_comp_rotate (Φ := fun x => unitFunctional σ N x ^ q)
    (fun p hp => norm_shiftConst n hp) (by fun_prop)

omit [MeasurableSpace Ω] in
/-- **A window is the unit window of the rotated family.**  `∫_n^{n+1} ‖A_y(½+it)‖² dt` equals
`unitFunctional` evaluated at the family rotated by `p ↦ p^{-in}`.  Substituting `t = h+n` and
applying `RMF.randomEulerProduct_shift` is all that happens. -/
lemma window_eq_unitFunctional {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} (hσ : 1 / 2 ≤ σ) (n : ℝ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    (∫ t in Set.Ioc (n) (n + 1),
        ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
          ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2)
      = unitFunctional σ N (fun p => shiftConst n (p : ℕ) * X (p : ℕ) ω) := by
  set F : ℝ → ℝ := fun t =>
    ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
      ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 with hF
  have hrot : ∀ p ∈ Nat.primesBelow N, ‖shiftConst n p * X p ω‖ ≤ 1 := by
    intro p hp
    rw [norm_mul, norm_shiftConst _ (Nat.prime_of_mem_primesBelow hp).pos, one_mul]
    exact hω p hp
  have hre : ∀ h : ℝ, (0 : ℝ) < ((σ : ℂ) + (h : ℂ) * Complex.I).re := by
    intro h
    simp
    linarith
  have hpt : ∀ h : ℝ, F (h + n)
      = ‖eulerClosed (fun p : Nat.Primes => shiftConst n (p : ℕ) * X (p : ℕ) ω) N
          ((σ : ℂ) + (h : ℂ) * Complex.I)‖ ^ 2 := by
    intro h
    rw [eulerClosed_eq_randomEulerProduct (X := fun p ω => shiftConst n p * X p ω)
      (hre h) hrot, hF]
    simp only
    congr 2
    rw [show ((σ : ℂ) + ((h + n : ℝ) : ℂ) * Complex.I)
        = ((σ : ℂ) + (h : ℂ) * Complex.I) + (n : ℂ) * Complex.I by push_cast; ring]
    exact randomEulerProduct_shift N _ _ ω
  calc (∫ t in Set.Ioc (n) (n + 1), F t)
      = ∫ t in (n)..(n + 1), F t :=
        (intervalIntegral.integral_of_le (by linarith)).symm
    _ = ∫ h in (0 : ℝ)..1, F (h + n) := by
        rw [intervalIntegral.integral_comp_add_right F n, zero_add, add_comm (1 : ℝ)]
    _ = ∫ h in (0 : ℝ)..1,
          ‖eulerClosed (fun p : Nat.Primes => shiftConst n (p : ℕ) * X (p : ℕ) ω) N
            ((σ : ℂ) + (h : ℂ) * Complex.I)‖ ^ 2 :=
        intervalIntegral.integral_congr fun h _ => hpt h
    _ = unitFunctional σ N (fun p => shiftConst n (p : ℕ) * X (p : ℕ) ω) :=
        intervalIntegral.integral_of_le zero_le_one

@[simp]
lemma shiftConst_zero (p : ℕ) : shiftConst 0 p = 1 := by
  rw [shiftConst]
  norm_num

/-- **Every window has the same `q`-th moment as the unit window.**  This is the periodisation
step's whole probabilistic input, assembled: the change of variables `t = h+n` turns a window into
the unit window of the rotated family, and rotation is invisible to the expectation. -/
theorem integral_rpow_window_eq {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hσ : 1 / 2 ≤ σ)
    (hX : IsSteinhausPrimeValues X μ) (N : ℕ) (n : ℝ) (q : ℝ) :
    (∫ ω, (∫ t in Set.Ioc (n) (n + 1),
        ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
          ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) ^ q ∂μ)
      = ∫ ω, (∫ h in Set.Ioc (0 : ℝ) 1,
          ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
            ((σ : ℂ) + (h : ℂ) * Complex.I) ω‖ ^ 2) ^ q ∂μ := by
  have hae := ae_forall_norm_le_one hX norm_le_one_steinhausLaw N
  have hL : (∫ ω, (∫ t in Set.Ioc (n) (n + 1),
      ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
        ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) ^ q ∂μ)
      = ∫ ω, unitFunctional σ N (fun p => shiftConst n (p : ℕ) * X (p : ℕ) ω) ^ q ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [window_eq_unitFunctional σ hσ (n : ℝ) hω]
  have hR : (∫ ω, (∫ h in Set.Ioc (0 : ℝ) 1,
      ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
        ((σ : ℂ) + (h : ℂ) * Complex.I) ω‖ ^ 2) ^ q ∂μ)
      = ∫ ω, unitFunctional σ N (fun p => X (p : ℕ) ω) ^ q ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    have h0 := window_eq_unitFunctional σ hσ (X := X) (N := N) (ω := ω) 0 hω
    norm_num at h0
    rw [h0]
  rw [hL, hR, integral_rpow_unitFunctional_rotate σ hX N n q]

/-! ### Integrability on the critical line

The partial Euler product is *bounded* on the line `Re s = ½`, uniformly in `t` and in `ω` (on the
a.e. set where the values are unimodular): each factor has modulus at most `(1 - p^{-1/2})⁻¹`.
Dividing by `½+it` then leaves something dominated by `C²/(¼+t²)`, which is integrable. -/

/-- The uniform bound on the partial Euler product on the critical line. -/
noncomputable def eulerBound (N : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesBelow N, (1 - (Real.sqrt p)⁻¹)⁻¹

lemma one_lt_sqrt_prime {p : ℕ} (hp : p.Prime) : (1 : ℝ) < Real.sqrt p := by
  have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  calc (1 : ℝ) = Real.sqrt 1 := by simp
    _ < Real.sqrt p := Real.sqrt_lt_sqrt (by norm_num) h1

lemma one_sub_inv_sqrt_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - (Real.sqrt p)⁻¹ := by
  have h1 := one_lt_sqrt_prime hp
  have hs : (0 : ℝ) < Real.sqrt p := lt_trans zero_lt_one h1
  have hlt : (Real.sqrt p)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr h1
  linarith

/-- Each local factor is bounded on the critical line. -/
lemma norm_inv_one_sub_le {x : ℂ} (hx : ‖x‖ ≤ 1) {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) :
    ‖(1 - x * (p : ℂ) ^ (-s))⁻¹‖ ≤ (1 - (Real.sqrt p)⁻¹)⁻¹ := by
  have hpos := one_sub_inv_sqrt_pos hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hhalf : (p : ℝ) ^ (-(1 / 2) : ℝ) = (Real.sqrt p)⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg p), Real.sqrt_eq_rpow]
  have hnorm : ‖x * (p : ℂ) ^ (-s)‖ ≤ (Real.sqrt p)⁻¹ := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    have hle : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    calc ‖x‖ * (p : ℝ) ^ (-s.re)
        ≤ 1 * (p : ℝ) ^ (-(1 / 2) : ℝ) :=
          mul_le_mul hx hle (Real.rpow_nonneg (Nat.cast_nonneg p) _) zero_le_one
      _ = (Real.sqrt p)⁻¹ := by rw [one_mul, hhalf]
  have hge : 1 - (Real.sqrt p)⁻¹ ≤ ‖1 - x * (p : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (x * (p : ℂ) ^ (-s))
    simp only [norm_one] at this
    linarith
  rw [norm_inv]
  exact inv_anti₀ hpos hge

lemma eulerBound_nonneg (N : ℕ) : 0 ≤ eulerBound N :=
  Finset.prod_nonneg fun _ hp =>
    (inv_pos.2 (one_sub_inv_sqrt_pos (Nat.prime_of_mem_primesBelow hp))).le

omit [MeasurableSpace Ω] in
/-- **The partial Euler product is bounded on the critical line**, uniformly in `t`. -/
lemma norm_randomEulerProduct_le {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω}
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N s ω‖ ≤ eulerBound N := by
  rw [randomEulerProduct_compMult_eq (by linarith) hω, eulerBound, norm_prod]
  exact Finset.prod_le_prod (fun p _ => norm_nonneg _)
    fun p hp => norm_inv_one_sub_le (hω p hp) (Nat.prime_of_mem_primesBelow hp) hs

lemma measurable_eulerClosed_line (σ : ℝ) (x : Nat.Primes → ℂ) (N : ℕ) :
    Measurable fun t : ℝ => eulerClosed x N ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  unfold eulerClosed
  refine Finset.measurable_prod _ fun p hp => ?_
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.prime_of_mem_primesBelow hp).pos.ne'
  have hcont : Continuous fun t : ℝ => (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl hp0)
  exact ((hcont.measurable.const_mul (primeExtend x p)).const_sub 1).inv

/-! ### The window estimates, parametrised by the arithmetic function

`RMF.lineSq` and `RMF.lineDivSq` below are written against `RMF.compMultExtension`, the Steinhaus
Euler product.  Every estimate in this section needs only **two** things about that product:

* it is measurable along the vertical line, and
* it is bounded there by `RMF.eulerBound N`.

Both hold for the **squarefree** product too — `RMF.norm_randomEulerProduct_sqfree_le` supplies the
second at the *same* constant, because `1 + u ≤ (1 - u)⁻¹`.  So the estimates are stated once
against a general `F : Ω → ArithmeticFunction ℂ` carrying those two hypotheses, and the Steinhaus
forms are recovered as instances.
-/

/-- `‖A_y(σ+it)‖²` for a general random arithmetic function, as a function of `t`. -/
noncomputable def lineSqOf (σ : ℝ) (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ‖randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2

/-- `‖A_y(σ+it)/(σ+it)‖²` for a general random arithmetic function. -/
noncomputable def lineDivSqOf (σ : ℝ) (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (ω : Ω)
    (t : ℝ) : ℝ :=
  ‖randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω
    / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2

omit [MeasurableSpace Ω] in
/-- **The line integrand is integrable**, given measurability and a uniform bound on the product.
Bounded numerator over `¼+t²`, dominated by `C²·4/(1+t²)`. -/
lemma integrable_lineDivSqOf {F : Ω → ArithmeticFunction ℂ} {N : ℕ} {ω : Ω} {C : ℝ}
    (hσ : 1 / 2 ≤ σ)
    (hmeas : Measurable fun t : ℝ =>
      randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω)
    (hbd : ∀ t : ℝ, ‖randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ C) :
    Integrable fun t : ℝ => lineDivSqOf σ F N ω t := by
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hbd 0)
  have hm : Measurable fun t : ℝ => lineDivSqOf σ F N ω t := by
    simp only [lineDivSqOf]
    exact (hmeas.div (by fun_prop)).norm.pow_const 2
  refine Integrable.mono' (g := fun t : ℝ => C ^ 2 * (4 * (1 + t ^ 2)⁻¹))
    ((integrable_inv_one_add_sq.const_mul (4 : ℝ)).const_mul _)
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  have hden : (0 : ℝ) < σ ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  simp only [lineDivSqOf]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_div, div_pow,
    normSq_ofReal_add_mul_I]
  have hsq : ‖randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ≤ C ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hbd t) 2
  have h4 : (1 + t ^ 2) / 4 ≤ σ ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hstep : C ^ 2 / (σ ^ 2 + t ^ 2) ≤ C ^ 2 * (4 * (1 + t ^ 2)⁻¹) := by
    have hd : C ^ 2 / (σ ^ 2 + t ^ 2) ≤ C ^ 2 / ((1 + t ^ 2) / 4) := by gcongr
    refine le_trans hd (le_of_eq ?_)
    have hne : (1 + t ^ 2) ≠ 0 := by positivity
    field_simp
  exact le_trans (by gcongr) hstep

omit [MeasurableSpace Ω] in
/-- **`‖A_y‖²` is integrable on a window**, given measurability and a uniform bound: it is
bounded and the window has finite measure. -/
lemma integrableOn_windowOf {F : Ω → ArithmeticFunction ℂ} {N : ℕ} {ω : Ω} {C : ℝ}
    (hmeas : Measurable fun t : ℝ =>
      randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω)
    (hbd : ∀ t : ℝ, ‖randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ C)
    (a b : ℝ) :
    IntegrableOn (fun t : ℝ => lineSqOf σ F N ω t) (Set.Ioc a b) := by
  refine Measure.integrableOn_of_bounded (M := C ^ 2) measure_Ioc_lt_top.ne ?_ ?_
  · exact (hmeas.norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with t
    simp only [lineSqOf]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd t) 2

omit [MeasurableSpace Ω] in
/-- The Steinhaus product is measurable along the line — the hypothesis
`RMF.integrable_lineDivSqOf` and `RMF.integrableOn_windowOf` ask for. -/
lemma measurable_randomEulerProduct_compMult_line {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω}
    (hσ : 1 / 2 ≤ σ) (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    Measurable fun t : ℝ =>
      randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
        ((σ : ℂ) + (t : ℂ) * Complex.I) ω := by
  have hre : ∀ t : ℝ, 1 / 2 ≤ ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
    intro t
    simpa using hσ
  have hpos : ∀ t : ℝ, (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := fun t => by
    have h := hre t
    linarith
  have heq : ∀ t : ℝ,
      randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
          ((σ : ℂ) + (t : ℂ) * Complex.I) ω
        = eulerClosed (fun p : Nat.Primes => X (p : ℕ) ω) N ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    fun t => (eulerClosed_eq_randomEulerProduct (hpos t) hω).symm
  simp_rw [heq]
  exact measurable_eulerClosed_line σ _ N

omit [MeasurableSpace Ω] in
/-- **The line integrand is integrable.**  Bounded numerator over `¼+t²`, dominated by
`C²·4/(1+t²)`. -/
lemma integrable_line_integrand {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} (hσ : 1 / 2 ≤ σ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    Integrable fun t : ℝ =>
      ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
        ((σ : ℂ) + (t : ℂ) * Complex.I) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
  integrable_lineDivSqOf σ hσ (measurable_randomEulerProduct_compMult_line σ hσ hω)
    (fun t => norm_randomEulerProduct_le hω (by simpa using hσ))

/-! ### Folding the line into unit windows -/

lemma pairwise_disjoint_Ioc_intCast :
    Pairwise (Function.onFun Disjoint fun n : ℤ => Set.Ioc ((n : ℝ)) ((n : ℝ) + 1)) := by
  intro m n hmn
  simp only [Function.onFun, Set.Ioc_disjoint_Ioc]
  rcases lt_or_gt_of_ne hmn with h | h
  · have hle : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h
    simp only [min_def, max_def]
    split_ifs <;> linarith
  · have hle : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h
    simp only [min_def, max_def]
    split_ifs <;> linarith

omit [MeasurableSpace Ω] in
/-- `‖A_y‖²` is integrable on a unit window: it is bounded and the window has finite measure. -/
lemma integrableOn_window {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} (hσ : 1 / 2 ≤ σ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) (a b : ℝ) :
    IntegrableOn (fun t : ℝ =>
      ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
        ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) (Set.Ioc a b) :=
  integrableOn_windowOf σ (measurable_randomEulerProduct_compMult_line σ hσ hω)
    (fun t => norm_randomEulerProduct_le hω (by simpa using hσ)) a b

omit [MeasurableSpace Ω] in
/-- **The per-window bound**, for a general product: dividing by `σ+it` costs at most `8/(1+n²)`
on `(n, n+1]`. -/
lemma window_boundOf {F : Ω → ArithmeticFunction ℂ} {N : ℕ} {ω : Ω} {C : ℝ} (hσ : 1 / 2 ≤ σ)
    (hmeas : Measurable fun t : ℝ =>
      randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω)
    (hbd : ∀ t : ℝ, ‖randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ C) (n : ℤ) :
    (∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineDivSqOf σ F N ω t)
      ≤ 8 / (1 + (n : ℝ) ^ 2) * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSqOf σ F N ω t := by
  rw [← integral_const_mul]
  refine setIntegral_mono_on (integrable_lineDivSqOf σ hσ hmeas hbd).integrableOn
    ((integrableOn_windowOf σ hmeas hbd ((n : ℝ)) ((n : ℝ) + 1)).const_mul _) measurableSet_Ioc
    fun t ht => ?_
  exact norm_div_sq_le σ hσ ht.1.le ht.2 _

/-! ### The pointwise periodisation bound

Two abbreviations keep the statements readable: `lineSq` is `‖A_y(½+it)‖²` and `lineDivSq` is
`‖A_y(½+it)/(½+it)‖²`, both as functions of `t`. -/

/-- `‖A_y(½+it)‖²`, as a function of `t`. -/
noncomputable def lineSq (σ : ℝ) (X : ℕ → Ω → ℂ) (N : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
    ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2

/-- `‖A_y(½+it)/(½+it)‖²`, as a function of `t`. -/
noncomputable def lineDivSq (σ : ℝ) (X : ℕ → Ω → ℂ) (N : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
    ((σ : ℂ) + (t : ℂ) * Complex.I) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2

/-- The real form of `RMF.rpow_tsum_le_tsum_rpow`, transported through `ENNReal.ofReal`.
Unlike the `ℝ≥0∞` version this needs both series to converge. -/
lemma rpow_tsum_le_tsum_rpow_real {ι : Type*} {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hs : Summable a) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hsq : Summable fun i => a i ^ q) :
    (∑' i, a i) ^ q ≤ ∑' i, a i ^ q := by
  have hnn : 0 ≤ ∑' i, a i ^ q := tsum_nonneg fun i => Real.rpow_nonneg (ha i) q
  rw [← ENNReal.ofReal_le_ofReal_iff hnn,
    ← ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg ha) hq0.le,
    ENNReal.ofReal_tsum_of_nonneg ha hs,
    ENNReal.ofReal_tsum_of_nonneg (fun i => Real.rpow_nonneg (ha i) q) hsq]
  refine le_trans (rpow_tsum_le_tsum_rpow _ hq0 hq1) (le_of_eq (tsum_congr fun i => ?_))
  rw [ENNReal.ofReal_rpow_of_nonneg (ha i) hq0.le]

/-- `∫_ℝ F` is the sum of its unit windows, with summability. -/
lemma hasSum_integral_Ioc {F : ℝ → ℝ} (hF : Integrable F) :
    HasSum (fun n : ℤ => ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), F t) (∫ t : ℝ, F t) := by
  have hu := MeasureTheory.hasSum_integral_iUnion (μ := volume) (f := F)
    (fun _ : ℤ => measurableSet_Ioc) pairwise_disjoint_Ioc_intCast
    (by rw [iUnion_Ioc_intCast ℝ]; exact hF.integrableOn)
  rwa [iUnion_Ioc_intCast ℝ, MeasureTheory.setIntegral_univ] at hu

omit [MeasurableSpace Ω] in
/-- **Every window is bounded by `C²`**, for a general product bounded by `C`. -/
lemma window_leOf {F : Ω → ArithmeticFunction ℂ} {N : ℕ} {ω : Ω} {C : ℝ}
    (hmeas : Measurable fun t : ℝ =>
      randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω)
    (hbd : ∀ t : ℝ, ‖randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ C) (n : ℝ) :
    (∫ t in Set.Ioc n (n + 1), lineSqOf σ F N ω t) ≤ C ^ 2 := by
  have hmono := setIntegral_mono_on (integrableOn_windowOf σ hmeas hbd n (n + 1))
    (integrableOn_const (by simp)) measurableSet_Ioc
    (fun t _ => pow_le_pow_left₀ (norm_nonneg _) (hbd t) 2)
  refine le_trans hmono (le_of_eq ?_)
  rw [setIntegral_const]
  simp [Real.volume_real_Ioc]

omit [MeasurableSpace Ω] in
lemma integral_lineSqOf_nonneg {F : Ω → ArithmeticFunction ℂ} {N : ℕ} {ω : Ω} (a b : ℝ) :
    0 ≤ ∫ t in Set.Ioc a b, lineSqOf σ F N ω t :=
  integral_nonneg fun t => by unfold lineSqOf; positivity

omit [MeasurableSpace Ω] in
/-- **A window is bounded by `eulerBound N ²`.** -/
lemma window_le {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} (hσ : 1 / 2 ≤ σ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) (n : ℝ) :
    (∫ t in Set.Ioc n (n + 1), lineSq σ X N ω t) ≤ eulerBound N ^ 2 :=
  window_leOf σ (measurable_randomEulerProduct_compMult_line σ hσ hω)
    (fun t => norm_randomEulerProduct_le hω (by simpa using hσ)) n

omit [MeasurableSpace Ω] in
lemma integral_lineSq_nonneg {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} (a b : ℝ) :
    0 ≤ ∫ t in Set.Ioc a b, lineSq σ X N ω t :=
  integral_lineSqOf_nonneg σ a b

lemma eight_div_eq (n : ℤ) : 8 / (1 + (n : ℝ) ^ 2) = 8 * shiftWeight 1 n := by
  rw [shiftWeight, Real.rpow_neg_one]
  ring

lemma rpow_eight_div (n : ℤ) {q : ℝ} :
    (8 / (1 + (n : ℝ) ^ 2)) ^ q = 8 ^ q * shiftWeight q n := by
  have hpos : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := by positivity
  rw [shiftWeight, div_eq_mul_inv, Real.mul_rpow (by norm_num) (by positivity),
    Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le]

omit [MeasurableSpace Ω] in
/-- **The pointwise periodisation bound**, for a general product bounded by `C` along the line.
`(c·∫_ℝ)^q` is at most `8` times the weighted sum of the windows' `q`-th powers. -/
theorem rpow_line_leOf {F : Ω → ArithmeticFunction ℂ} {N : ℕ} {ω : Ω} {C : ℝ}
    (hσ : 1 / 2 ≤ σ)
    (hmeas : Measurable fun t : ℝ =>
      randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω)
    (hbd : ∀ t : ℝ, ‖randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ C)
    {c : ℝ} (hc : 0 ≤ c) {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) :
    (c * ∫ t : ℝ, lineDivSqOf σ F N ω t) ^ q
      ≤ 8 * ∑' n : ℤ, shiftWeight q n
          * (c * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSqOf σ F N ω t) ^ q := by
  have hq0' : (0 : ℝ) < q := lt_trans (by norm_num) hq0
  set W : ℤ → ℝ := fun n => ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSqOf σ F N ω t with hWdef
  set B : ℝ := C with hBdef
  have hWnn : ∀ n, 0 ≤ W n := fun n => integral_lineSqOf_nonneg σ (n : ℝ) ((n : ℝ) + 1)
  have hWle : ∀ n, W n ≤ B ^ 2 := fun n => window_leOf σ hmeas hbd (n : ℝ)
  have hw1 : Summable (shiftWeight (1 : ℝ)) := summable_shiftWeight (by norm_num)
  have hwq : Summable (shiftWeight q) := summable_shiftWeight hq0
  have hcW : ∀ n, 0 ≤ c * W n := fun n => mul_nonneg hc (hWnn n)
  -- the weighted sum of `q`-th powers converges
  have hkey : Summable fun n : ℤ => shiftWeight q n * (c * W n) ^ q := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (shiftWeight_nonneg q n) (Real.rpow_nonneg (hcW n) q))
      (fun n => ?_) (hwq.mul_right ((c * B ^ 2) ^ q))
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hcW n) (mul_le_mul_of_nonneg_left (hWle n) hc) hq0'.le)
      (shiftWeight_nonneg q n)
  -- the windows sum to the line integral, and are bounded termwise
  have hIsum : HasSum (fun n : ℤ => ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineDivSqOf σ F N ω t)
      (∫ t : ℝ, lineDivSqOf σ F N ω t) :=
    hasSum_integral_Ioc (integrable_lineDivSqOf σ hσ hmeas hbd)
  have hMnn : ∀ n : ℤ, 0 ≤ 8 / (1 + (n : ℝ) ^ 2) * W n :=
    fun n => mul_nonneg (by positivity) (hWnn n)
  have hMsum : Summable fun n : ℤ => 8 / (1 + (n : ℝ) ^ 2) * W n := by
    refine Summable.of_nonneg_of_le hMnn (fun n => ?_) (hw1.mul_left (8 * B ^ 2))
    rw [eight_div_eq]
    calc 8 * shiftWeight 1 n * W n ≤ 8 * shiftWeight 1 n * B ^ 2 :=
          mul_le_mul_of_nonneg_left (hWle n)
            (mul_nonneg (by norm_num) (shiftWeight_nonneg 1 n))
      _ = 8 * B ^ 2 * shiftWeight 1 n := by ring
  have hline : (∫ t : ℝ, lineDivSqOf σ F N ω t) ≤ ∑' n : ℤ, 8 / (1 + (n : ℝ) ^ 2) * W n := by
    rw [← hIsum.tsum_eq]
    exact hIsum.summable.tsum_le_tsum (fun n => window_boundOf σ hσ hmeas hbd n) hMsum
  -- scale by `c`
  set a : ℤ → ℝ := fun n => 8 / (1 + (n : ℝ) ^ 2) * (c * W n) with hadef
  have hann : ∀ n, 0 ≤ a n := fun n => mul_nonneg (by positivity) (hcW n)
  have hasum : Summable a := by
    have hc' : Summable fun n : ℤ => c * (8 / (1 + (n : ℝ) ^ 2) * W n) := hMsum.mul_left c
    refine hc'.congr fun n => ?_
    rw [hadef]
    ring
  have hcline : c * (∫ t : ℝ, lineDivSqOf σ F N ω t) ≤ ∑' n : ℤ, a n := by
    have hrw : ∑' n : ℤ, a n = c * ∑' n : ℤ, 8 / (1 + (n : ℝ) ^ 2) * W n := by
      rw [← tsum_mul_left]
      exact tsum_congr fun n => by rw [hadef]; ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hline hc
  -- the `q`-th power, termwise
  have haq : ∀ n : ℤ, a n ^ q = 8 ^ q * (shiftWeight q n * (c * W n) ^ q) := by
    intro n
    rw [hadef]
    simp only
    rw [Real.mul_rpow (by positivity) (hcW n), rpow_eight_div n]
    ring
  have haqsum : Summable fun n : ℤ => a n ^ q := by
    refine (hkey.mul_left ((8 : ℝ) ^ q)).congr fun n => ?_
    rw [haq n]
  have h8q : (8 : ℝ) ^ q ≤ 8 := by
    calc (8 : ℝ) ^ q ≤ 8 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq1
      _ = 8 := Real.rpow_one 8
  have hnn0 : 0 ≤ c * ∫ t : ℝ, lineDivSqOf σ F N ω t :=
    mul_nonneg hc (integral_nonneg fun t => by unfold lineDivSqOf; positivity)
  calc (c * ∫ t : ℝ, lineDivSqOf σ F N ω t) ^ q
      ≤ (∑' n : ℤ, a n) ^ q := Real.rpow_le_rpow hnn0 hcline hq0'.le
    _ ≤ ∑' n : ℤ, a n ^ q := rpow_tsum_le_tsum_rpow_real hann hasum hq0' hq1 haqsum
    _ ≤ 8 * ∑' n : ℤ, shiftWeight q n * (c * W n) ^ q := by
        rw [← tsum_mul_left]
        refine haqsum.tsum_le_tsum (fun n => ?_) (hkey.mul_left 8)
        rw [haq n]
        exact mul_le_mul_of_nonneg_right h8q
          (mul_nonneg (shiftWeight_nonneg q n) (Real.rpow_nonneg (hcW n) q))

omit [MeasurableSpace Ω] in
/-- The `RMF.compMultExtension` case of `RMF.rpow_line_leOf`, at `C = RMF.eulerBound N`. -/
theorem rpow_line_le {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} (hσ : 1 / 2 ≤ σ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) {c : ℝ} (hc : 0 ≤ c)
    {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) :
    (c * ∫ t : ℝ, lineDivSq σ X N ω t) ^ q
      ≤ 8 * ∑' n : ℤ, shiftWeight q n
          * (c * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSq σ X N ω t) ^ q :=
  rpow_line_leOf σ hσ (measurable_randomEulerProduct_compMult_line σ hσ hω)
    (fun t => norm_randomEulerProduct_le hω (by simpa using hσ)) hc hq0 hq1

omit [MeasurableSpace Ω] in
/-- **Restricting to `|t| ≤ 1/2`** costs only a constant: there `|σ+it|² = σ²+t² ≤ 5/4` once
`σ ≤ 1`, so the line integral dominates `4/5` of the window integral.  The upper bound `σ ≤ 1` is
harmless where this is used: the shift is `4V/log x`, which tends to `0`. -/
lemma integral_lineDivSqOf_ge {G : Ω → ArithmeticFunction ℂ} {N : ℕ} {ω : Ω} {C : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1)
    (hmeas : Measurable fun t : ℝ =>
      randomEulerProduct G N ((σ : ℂ) + (t : ℂ) * Complex.I) ω)
    (hbd : ∀ t : ℝ, ‖randomEulerProduct G N ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ C) :
    (4 / 5 : ℝ) * ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ), lineSqOf σ G N ω t
      ≤ ∫ t : ℝ, lineDivSqOf σ G N ω t := by
  have hint : Integrable (fun t : ℝ => lineDivSqOf σ G N ω t) :=
    integrable_lineDivSqOf σ hσ hmeas hbd
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume] fun t => lineDivSqOf σ G N ω t :=
    Filter.Eventually.of_forall fun t => by
      simp only [Pi.zero_apply]
      unfold lineDivSqOf
      positivity
  refine le_trans ?_
    (setIntegral_le_integral (s := Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ)) hint hnn)
  rw [← integral_const_mul]
  refine setIntegral_mono_on
    ((integrableOn_windowOf σ hmeas hbd (-(1 : ℝ) / 2) (1 / 2 : ℝ)).const_mul _)
    hint.integrableOn measurableSet_Ioc fun t ht => ?_
  -- pointwise: `‖A‖²/(σ²+t²) ≥ (4/5)‖A‖²`
  have ht2 : t ^ 2 ≤ 1 / 4 := by
    rcases abs_le.1 (abs_le.2 ⟨by linarith [ht.1], ht.2⟩) with ⟨h1, h2⟩
    nlinarith
  have hden : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 ≤ 5 / 4 := by
    rw [normSq_ofReal_add_mul_I]
    nlinarith
  have hd0 : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 := by
    rw [normSq_ofReal_add_mul_I]
    nlinarith [sq_nonneg t]
  simp only [lineSqOf, lineDivSqOf, norm_div, div_pow]
  rw [le_div_iff₀ hd0]
  nlinarith [sq_nonneg (‖randomEulerProduct G N ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖)]

omit [MeasurableSpace Ω] in
/-- The `RMF.compMultExtension` case of `RMF.integral_lineDivSqOf_ge`. -/
lemma integral_lineDivSq_ge {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    (4 / 5 : ℝ) * ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ), lineSq σ X N ω t
      ≤ ∫ t : ℝ, lineDivSq σ X N ω t :=
  integral_lineDivSqOf_ge σ hσ hσ1 (measurable_randomEulerProduct_compMult_line σ hσ hω)
    (fun t => norm_randomEulerProduct_le hω (by simpa using hσ))

/-! ### The line integral as a measurable functional

The mirror of `RMF.unitFunctional`, needed so that `ω ↦ ∫_ℝ` is measurable. -/

/-- `∫_ℝ ‖A_y(½+it)/(½+it)‖² dt`, as a functional of the values at the primes. -/
noncomputable def lineFunctional (σ : ℝ) (N : ℕ) (x : Nat.Primes → ℂ) : ℝ :=
  ∫ t : ℝ, ‖eulerClosed x N ((σ : ℂ) + (t : ℂ) * Complex.I)
    / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2

lemma measurable_lineFunctional (σ : ℝ) (N : ℕ) : Measurable (lineFunctional σ N) := by
  have hden : Measurable fun z : (Nat.Primes → ℂ) × ℝ => ((σ : ℂ) + (z.2 : ℂ) * Complex.I) := by
    fun_prop
  have hnum := measurable_eulerClosed_uncurry σ N
  have hjoint : Measurable fun z : (Nat.Primes → ℂ) × ℝ =>
      ‖eulerClosed z.1 N ((σ : ℂ) + (z.2 : ℂ) * Complex.I)
        / ((σ : ℂ) + (z.2 : ℂ) * Complex.I)‖ ^ 2 := (hnum.div hden).norm.pow_const 2
  unfold lineFunctional
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ)) hjoint.stronglyMeasurable).measurable

omit [MeasurableSpace Ω] in
lemma lineFunctional_eq {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} (hσ : 1 / 2 ≤ σ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    lineFunctional σ N (fun p : Nat.Primes => X (p : ℕ) ω) = ∫ t : ℝ, lineDivSq σ X N ω t := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hre : 1 / 2 ≤ ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  simp only [lineDivSq]
  rw [eulerClosed_eq_randomEulerProduct (X := X) (by linarith) hω]

/-! ### The periodisation bound, integrated -/

set_option maxHeartbeats 400000 in
-- the chain threads a `tsum` through a Bochner integral and back through `ℝ≥0∞`
/-- **The periodisation bound.**  Integrating `RMF.rpow_line_le` over `Ω`: the weights come out,
and every window contributes the same expectation by `RMF.integral_rpow_window_eq`. -/
theorem integral_rpow_line_le {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hσ : 1 / 2 ≤ σ) (hX : IsSteinhausPrimeValues X μ) (N : ℕ) {c : ℝ} (hc : 0 ≤ c)
    {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) :
    (∫ ω, (c * ∫ t : ℝ, lineDivSq σ X N ω t) ^ q ∂μ)
      ≤ 8 * (∑' n : ℤ, shiftWeight q n)
        * ∫ ω, (c * ∫ h in Set.Ioc (0 : ℝ) 1, lineSq σ X N ω h) ^ q ∂μ := by
  have hq0' : (0 : ℝ) < q := lt_trans (by norm_num) hq0
  have hae := ae_forall_norm_le_one hX norm_le_one_steinhausLaw N
  have hwq : Summable (shiftWeight q) := summable_shiftWeight hq0
  have hwnn : 0 ≤ ∑' n : ℤ, shiftWeight q n := tsum_nonneg fun n => shiftWeight_nonneg q n
  set K : ℝ := (c * eulerBound N ^ 2) ^ q with hKdef
  have hK : 0 ≤ K := Real.rpow_nonneg (mul_nonneg hc (by positivity)) q
  set W : ℤ → Ω → ℝ := fun n ω => ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSq σ X N ω t
    with hWdef
  set F : ℤ → Ω → ℝ := fun n ω => shiftWeight q n * (c * W n ω) ^ q with hFdef
  set M : ℝ := ∫ ω, (c * ∫ h in Set.Ioc (0 : ℝ) 1, lineSq σ X N ω h) ^ q ∂μ with hMdef
  have hWnn : ∀ n ω, 0 ≤ W n ω := fun n ω => integral_lineSq_nonneg σ (n : ℝ) ((n : ℝ) + 1)
  have hFnn : ∀ n ω, 0 ≤ F n ω := fun n ω =>
    mul_nonneg (shiftWeight_nonneg q n) (Real.rpow_nonneg (mul_nonneg hc (hWnn n ω)) q)
  have hMnn : 0 ≤ M :=
    integral_nonneg fun ω => Real.rpow_nonneg
      (mul_nonneg hc (integral_nonneg fun t => by unfold lineSq; positivity)) q
  -- the termwise bound and the pointwise inequality, on the good set
  have hgood : ∀ᵐ ω ∂μ, (∀ n : ℤ, F n ω ≤ shiftWeight q n * K) ∧
      (c * ∫ t : ℝ, lineDivSq σ X N ω t) ^ q ≤ 8 * ∑' n : ℤ, F n ω := by
    filter_upwards [hae] with ω hω
    refine ⟨fun n => ?_, rpow_line_le σ hσ hω hc hq0 hq1⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hc (hWnn n ω))
        (mul_le_mul_of_nonneg_left (window_le σ hσ hω (n : ℝ)) hc) hq0'.le)
      (shiftWeight_nonneg q n)
  -- measurability of each `F n`, through the unit functional
  have hFmeas : ∀ n : ℤ, AEStronglyMeasurable (F n) μ := by
    intro n
    have hrot : Measurable fun ω =>
        (fun p : Nat.Primes => shiftConst (n : ℝ) (p : ℕ) * X (p : ℕ) ω) :=
      measurable_pi_lambda _ fun p => (hX.measurable (p : ℕ) p.2).const_mul _
    have h1 : Measurable fun ω => unitFunctional σ N
        (fun p : Nat.Primes => shiftConst (n : ℝ) (p : ℕ) * X (p : ℕ) ω) :=
      (measurable_unitFunctional σ N).comp hrot
    have h2 : Measurable fun ω => shiftWeight q n * (c * unitFunctional σ N
        (fun p : Nat.Primes => shiftConst (n : ℝ) (p : ℕ) * X (p : ℕ) ω)) ^ q := by fun_prop
    refine h2.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with ω hω
    have h := window_eq_unitFunctional σ hσ (X := X) (N := N) (ω := ω) (n : ℝ) hω
    rw [hFdef]
    simp only [hWdef, lineSq]
    rw [h]
  have hFint : ∀ n : ℤ, Integrable (F n) μ := by
    intro n
    refine (memLp_top_of_bound (hFmeas n) (shiftWeight q n * K) ?_).integrable le_top
    filter_upwards [hgood] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn n ω)]
    exact hω.1 n
  -- the value of each integral
  have hsplit : ∀ m : ℤ, ∫ ω, (c * W m ω) ^ q ∂μ = c ^ q * ∫ ω, W m ω ^ q ∂μ := by
    intro m
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => Real.mul_rpow hc (hWnn m ω))
  have hsplit0 : M = c ^ q * ∫ ω, (∫ h in Set.Ioc (0 : ℝ) 1, lineSq σ X N ω h) ^ q ∂μ := by
    rw [hMdef, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      Real.mul_rpow hc (integral_nonneg fun t => by unfold lineSq; positivity))
  have hFval : ∀ n : ℤ, ∫ ω, F n ω ∂μ = shiftWeight q n * M := by
    intro n
    have hwin : ∫ ω, W n ω ^ q ∂μ
        = ∫ ω, (∫ h in Set.Ioc (0 : ℝ) 1, lineSq σ X N ω h) ^ q ∂μ := by
      simp only [hWdef, lineSq]
      exact integral_rpow_window_eq σ hσ hX N (n : ℝ) q
    rw [hFdef]
    simp only
    rw [integral_const_mul, hsplit n, hwin, ← hsplit0]
  -- the left side is integrable
  have hLnn : ∀ ω, 0 ≤ (c * ∫ t : ℝ, lineDivSq σ X N ω t) ^ q := fun ω =>
    Real.rpow_nonneg
      (mul_nonneg hc (integral_nonneg fun t => by unfold lineDivSq; positivity)) q
  have hLmeas : AEStronglyMeasurable (fun ω => (c * ∫ t : ℝ, lineDivSq σ X N ω t) ^ q) μ := by
    have hmap : Measurable fun ω =>
        (c * lineFunctional σ N (fun p : Nat.Primes => X (p : ℕ) ω)) ^ q := by
      have h1 := (measurable_lineFunctional σ N).comp
        (measurable_pi_lambda _ fun p : Nat.Primes => hX.measurable (p : ℕ) p.2)
      fun_prop
    refine hmap.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with ω hω
    rw [lineFunctional_eq σ hσ hω]
  have hLbd : ∀ᵐ ω ∂μ,
      ‖(c * ∫ t : ℝ, lineDivSq σ X N ω t) ^ q‖ ≤ 8 * (∑' n : ℤ, shiftWeight q n) * K := by
    filter_upwards [hgood] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hLnn ω), mul_assoc]
    refine le_trans hω.2 (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    rw [← tsum_mul_right]
    exact (Summable.of_nonneg_of_le (fun n => hFnn n ω) hω.1
      (hwq.mul_right K)).tsum_le_tsum hω.1 (hwq.mul_right K)
  have hLint : Integrable (fun ω => (c * ∫ t : ℝ, lineDivSq σ X N ω t) ^ q) μ :=
    (memLp_top_of_bound hLmeas _ hLbd).integrable le_top
  -- compare in `ℝ≥0∞`, where `lintegral_tsum` has no side conditions
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
    ofReal_integral_eq_lintegral_ofReal hLint (Filter.Eventually.of_forall hLnn)]
  calc ∫⁻ ω, ENNReal.ofReal ((c * ∫ t : ℝ, lineDivSq σ X N ω t) ^ q) ∂μ
      ≤ ∫⁻ ω, 8 * ∑' n : ℤ, ENNReal.ofReal (F n ω) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hgood] with ω hω
        refine le_trans (ENNReal.ofReal_le_ofReal hω.2) ?_
        rw [ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_tsum_of_nonneg (fun n => hFnn n ω)
            (Summable.of_nonneg_of_le (fun n => hFnn n ω) hω.1 (hwq.mul_right K))]
        norm_num
    _ = 8 * ∑' n : ℤ, ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ := by
        rw [lintegral_const_mul' _ _ (by norm_num),
          lintegral_tsum (f := fun (n : ℤ) (ω : Ω) => ENNReal.ofReal (F n ω))
            (fun n =>
              ENNReal.measurable_ofReal.comp_aemeasurable (hFmeas n).aemeasurable)]
    _ = ENNReal.ofReal (8 * (∑' n : ℤ, shiftWeight q n) * M) := by
        have hterm : ∀ n : ℤ, ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ
            = ENNReal.ofReal (shiftWeight q n * M) := by
          intro n
          rw [← ofReal_integral_eq_lintegral_ofReal (hFint n)
            (Filter.Eventually.of_forall fun ω => hFnn n ω), hFval n]
        simp_rw [hterm]
        rw [← ENNReal.ofReal_tsum_of_nonneg
            (fun n => mul_nonneg (shiftWeight_nonneg q n) hMnn) (hwq.mul_right M),
          tsum_mul_right,
          show (8 : ℝ) * (∑' n : ℤ, shiftWeight q n) * M
            = 8 * ((∑' n : ℤ, shiftWeight q n) * M) from by ring,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
        norm_num

set_option maxHeartbeats 400000 in
-- the chain threads a `tsum` through a Bochner integral and back through `ℝ≥0∞`
/-- **The periodisation bound, in Harper's sum-to-max form**: if every window's
`q`-th moment is at most `(|n|+1)^{1/4} S`, the line integral's is at most
`8 (∑_n shiftWeight q n · (|n|+1)^{1/4}) S`.  This replaces the Steinhaus step
`RMF.integral_rpow_window_eq` (rotation invariance), which fails for the Rademacher function.
Paying `(|n|+1)^{1/4}` costs an eighth in `RMF.summable_shiftWeight_mul_abs_add_one_rpow`, hence
`5/8 < q`. -/
theorem integral_rpow_line_le_maxOf {G : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hσ : 1 / 2 ≤ σ) (N : ℕ) {C : ℝ}
    (hae : ∀ᵐ ω ∂μ,
      (Measurable fun t : ℝ => randomEulerProduct G N ((σ : ℂ) + (t : ℂ) * Complex.I) ω) ∧
        ∀ t : ℝ, ‖randomEulerProduct G N ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ C)
    (hWmeas : ∀ n : ℤ, AEStronglyMeasurable
      (fun ω => ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSqOf σ G N ω t) μ)
    (hLmeas : AEStronglyMeasurable (fun ω => ∫ t : ℝ, lineDivSqOf σ G N ω t) μ)
    {c : ℝ} (hc : 0 ≤ c)
    {q : ℝ} (hq0 : 5 / 8 < q) (hq1 : q ≤ 1) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ n : ℤ, (∫ ω, (c * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
        lineSqOf σ G N ω t) ^ q ∂μ) ≤ (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) * S) :
    (∫ ω, (c * ∫ t : ℝ, lineDivSqOf σ G N ω t) ^ q ∂μ)
      ≤ 8 * (∑' n : ℤ, shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)) * S := by
  have hq0'' : (1 : ℝ) / 2 < q := by linarith
  have hq0' : (0 : ℝ) < q := lt_trans (by norm_num) hq0''
  have hwq : Summable (shiftWeight q) := summable_shiftWeight hq0''
  have hwq' : Summable fun n : ℤ => shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) :=
    summable_shiftWeight_mul_abs_add_one_rpow hq0
  have hwnn' : ∀ n : ℤ, (0 : ℝ) ≤ shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) :=
    fun n => mul_nonneg (shiftWeight_nonneg q n) (Real.rpow_nonneg (by positivity) _)
  have hwnn : 0 ≤ ∑' n : ℤ, shiftWeight q n := tsum_nonneg fun n => shiftWeight_nonneg q n
  set K : ℝ := (c * C ^ 2) ^ q with hKdef
  have hK : 0 ≤ K := Real.rpow_nonneg (mul_nonneg hc (by positivity)) q
  set W : ℤ → Ω → ℝ := fun n ω => ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSqOf σ G N ω t
    with hWdef
  set F : ℤ → Ω → ℝ := fun n ω => shiftWeight q n * (c * W n ω) ^ q with hFdef
  have hWnn : ∀ n ω, 0 ≤ W n ω := fun n ω => integral_lineSqOf_nonneg σ (n : ℝ) ((n : ℝ) + 1)
  have hFnn : ∀ n ω, 0 ≤ F n ω := fun n ω =>
    mul_nonneg (shiftWeight_nonneg q n) (Real.rpow_nonneg (mul_nonneg hc (hWnn n ω)) q)
  -- the termwise bound and the pointwise inequality, on the good set
  have hgood : ∀ᵐ ω ∂μ, (∀ n : ℤ, F n ω ≤ shiftWeight q n * K) ∧
      (c * ∫ t : ℝ, lineDivSqOf σ G N ω t) ^ q ≤ 8 * ∑' n : ℤ, F n ω := by
    filter_upwards [hae] with ω hω
    refine ⟨fun n => ?_, rpow_line_leOf σ hσ hω.1 hω.2 hc hq0'' hq1⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hc (hWnn n ω))
        (mul_le_mul_of_nonneg_left (window_leOf σ hω.1 hω.2 (n : ℝ)) hc) hq0'.le)
      (shiftWeight_nonneg q n)
  -- measurability of each `F n`, an input
  have hFmeas : ∀ n : ℤ, AEStronglyMeasurable (F n) μ := fun n =>
    (((Real.continuous_rpow_const hq0'.le).comp_aestronglyMeasurable
      ((hWmeas n).const_mul c)).const_mul (shiftWeight q n))
  have hFint : ∀ n : ℤ, Integrable (F n) μ := by
    intro n
    refine (memLp_top_of_bound (hFmeas n) (shiftWeight q n * K) ?_).integrable le_top
    filter_upwards [hgood] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn n ω)]
    exact hω.1 n
  -- each window's contribution, bounded by `S` after paying the weight
  have hFle : ∀ n : ℤ, ∫ ω, F n ω ∂μ
      ≤ shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) * S := by
    intro n
    rw [hFdef]
    simp only
    rw [integral_const_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hS n) (shiftWeight_nonneg q n)
  -- the left side is integrable
  have hLnn : ∀ ω, 0 ≤ (c * ∫ t : ℝ, lineDivSqOf σ G N ω t) ^ q := fun ω =>
    Real.rpow_nonneg
      (mul_nonneg hc (integral_nonneg fun t => by unfold lineDivSqOf; positivity)) q
  have hLmeas' : AEStronglyMeasurable (fun ω => (c * ∫ t : ℝ, lineDivSqOf σ G N ω t) ^ q) μ :=
    (Real.continuous_rpow_const hq0'.le).comp_aestronglyMeasurable (hLmeas.const_mul c)
  have hLbd : ∀ᵐ ω ∂μ,
      ‖(c * ∫ t : ℝ, lineDivSqOf σ G N ω t) ^ q‖ ≤ 8 * (∑' n : ℤ, shiftWeight q n) * K := by
    filter_upwards [hgood] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hLnn ω), mul_assoc]
    refine le_trans hω.2 (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    rw [← tsum_mul_right]
    exact (Summable.of_nonneg_of_le (fun n => hFnn n ω) hω.1
      (hwq.mul_right K)).tsum_le_tsum hω.1 (hwq.mul_right K)
  have hLint : Integrable (fun ω => (c * ∫ t : ℝ, lineDivSqOf σ G N ω t) ^ q) μ :=
    (memLp_top_of_bound hLmeas' _ hLbd).integrable le_top
  -- compare in `ℝ≥0∞`, where `lintegral_tsum` has no side conditions
  rw [← ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg (by norm_num) (tsum_nonneg hwnn')) hS0),
    ofReal_integral_eq_lintegral_ofReal hLint (Filter.Eventually.of_forall hLnn)]
  calc ∫⁻ ω, ENNReal.ofReal ((c * ∫ t : ℝ, lineDivSqOf σ G N ω t) ^ q) ∂μ
      ≤ ∫⁻ ω, 8 * ∑' n : ℤ, ENNReal.ofReal (F n ω) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hgood] with ω hω
        refine le_trans (ENNReal.ofReal_le_ofReal hω.2) ?_
        rw [ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_tsum_of_nonneg (fun n => hFnn n ω)
            (Summable.of_nonneg_of_le (fun n => hFnn n ω) hω.1 (hwq.mul_right K))]
        norm_num
    _ = 8 * ∑' n : ℤ, ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ := by
        rw [lintegral_const_mul' _ _ (by norm_num),
          lintegral_tsum (f := fun (n : ℤ) (ω : Ω) => ENNReal.ofReal (F n ω))
            (fun n =>
              ENNReal.measurable_ofReal.comp_aemeasurable (hFmeas n).aemeasurable)]
    _ ≤ 8 * ∑' n : ℤ, ENNReal.ofReal
          (shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) * S) := by
        refine mul_le_mul_right (ENNReal.tsum_le_tsum fun n => ?_) _
        rw [← ofReal_integral_eq_lintegral_ofReal (hFint n)
          (Filter.Eventually.of_forall fun ω => hFnn n ω)]
        exact ENNReal.ofReal_le_ofReal (hFle n)
    _ = ENNReal.ofReal
          (8 * (∑' n : ℤ, shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)) * S) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg
            (fun n => mul_nonneg (hwnn' n) hS0) (hwq'.mul_right S),
          tsum_mul_right,
          show (8 : ℝ) * (∑' n : ℤ, shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)) * S
            = 8 * ((∑' n : ℤ, shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)) * S)
            from by ring,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
        norm_num

omit [MeasurableSpace Ω] in
/-- **The line integral is bounded**, for a general product bounded by `C` along the line.

Folding `ℝ` into unit windows, each window contributes at most `C²` and the division by `σ+it`
contributes `8/(1+n²) = 8·shiftWeight 1 n`, which is summable. -/
lemma integral_lineDivSqOf_le {F : Ω → ArithmeticFunction ℂ} {N : ℕ} {ω : Ω} {C : ℝ}
    (hσ : 1 / 2 ≤ σ)
    (hmeas : Measurable fun t : ℝ =>
      randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω)
    (hbd : ∀ t : ℝ, ‖randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ C) :
    (∫ t : ℝ, lineDivSqOf σ F N ω t) ≤ 8 * C ^ 2 * ∑' n : ℤ, shiftWeight 1 n := by
  have hw1 : Summable (shiftWeight (1 : ℝ)) := summable_shiftWeight (by norm_num)
  have hIsum : HasSum (fun n : ℤ => ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
      lineDivSqOf σ F N ω t) (∫ t : ℝ, lineDivSqOf σ F N ω t) :=
    hasSum_integral_Ioc (integrable_lineDivSqOf σ hσ hmeas hbd)
  have hMnn : ∀ n : ℤ, 0 ≤ 8 / (1 + (n : ℝ) ^ 2)
      * (∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSqOf σ F N ω t) :=
    fun n => mul_nonneg (by positivity) (integral_lineSqOf_nonneg σ (n : ℝ) ((n : ℝ) + 1))
  have hterm : ∀ n : ℤ, 8 / (1 + (n : ℝ) ^ 2)
      * (∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSqOf σ F N ω t)
      ≤ 8 * C ^ 2 * shiftWeight 1 n := by
    intro n
    rw [eight_div_eq]
    calc 8 * shiftWeight 1 n * (∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSqOf σ F N ω t)
        ≤ 8 * shiftWeight 1 n * C ^ 2 :=
          mul_le_mul_of_nonneg_left (window_leOf σ hmeas hbd (n : ℝ))
            (mul_nonneg (by norm_num) (shiftWeight_nonneg 1 n))
      _ = 8 * C ^ 2 * shiftWeight 1 n := by ring
  have hMsum : Summable fun n : ℤ => 8 / (1 + (n : ℝ) ^ 2)
      * (∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSqOf σ F N ω t) :=
    Summable.of_nonneg_of_le hMnn hterm (hw1.mul_left (8 * C ^ 2))
  rw [← hIsum.tsum_eq, ← tsum_mul_left]
  refine le_trans (hIsum.summable.tsum_le_tsum
    (fun n => window_boundOf σ hσ hmeas hbd n) hMsum) ?_
  exact hMsum.tsum_le_tsum hterm (hw1.mul_left (8 * C ^ 2))

omit [MeasurableSpace Ω] in
/-- **The line integral is bounded**, uniformly in `t`, at any `ω` where the values at the primes
below `N` are bounded by one.  The bound is `q`-free, which is what lets it serve
`RMF.integrable_eulerLineIntegral_rpow` for every `q ≥ 0`, not just `q > 1/2`. -/
lemma integral_lineDivSq_le {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} (hσ : 1 / 2 ≤ σ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    (∫ t : ℝ, lineDivSq σ X N ω t)
      ≤ 8 * eulerBound N ^ 2 * ∑' n : ℤ, shiftWeight 1 n :=
  integral_lineDivSqOf_le σ hσ (measurable_randomEulerProduct_compMult_line σ hσ hω)
    (fun t => norm_randomEulerProduct_le hω (by simpa using hσ))

omit [MeasurableSpace Ω] in
/-- The unit-window analogue of `RMF.lineFunctional_eq`. -/
lemma unitFunctional_eq {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} (hσ : 1 / 2 ≤ σ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    unitFunctional σ N (fun p : Nat.Primes => X (p : ℕ) ω)
      = ∫ h in Set.Ioc (0 : ℝ) 1, lineSq σ X N ω h := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hre : 1 / 2 ≤ ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  simp only [lineSq]
  rw [eulerClosed_eq_randomEulerProduct (X := X) (by linarith) hω]

omit [MeasurableSpace Ω] in
/-- The unit window is bounded by `eulerBound N ²`, like every other window. -/
lemma integral_unit_le {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} (hσ : 1 / 2 ≤ σ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    (∫ h in Set.Ioc (0 : ℝ) 1, lineSq σ X N ω h) ≤ eulerBound N ^ 2 := by
  simpa using window_le σ hσ hω (0 : ℝ)

end RMF
