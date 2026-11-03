/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.ReductionExplicit

/-!
# The reduction's discrepancy constant: `2` instead of `16`

Step L9 of the lower reduction (`RMF.meanSquare_le_sum_weighted_explicit`) pays the smoothing
discrepancy through `E[D] ≤ 16` (`RMF.integral_sum_discrepancy_le_weighted`, any primes up to `x`).
On the primes the reduction uses, those of `(√x, x]`, the per-prime bound `(1 + 1/L)(1/L + p/x)`
(`RMF.integral_discrepancy_le_weighted`, `L = log x`) sums to

`E[D] ≤ (1 + 1/L)(1/2 + log 4 + 9.003/L)` for every `x > 1`

(`RMF.integral_sum_discrepancy_le_sqrt_weighted_of_one_lt`): Mertens' first theorem on `(√x, x]`,
`∑ log p/p ≤ L/2 + 9.003` (`RMF.sum_log_div_largePrimeSet_sqrt_le`, from PNT+'s bounds on
`Mertens.E₁p` at `x` and at `√x`), and Chebyshev's `θ(x) ≤ x log 4`.  So `E[D] ≤ 2` for
`x ≥ e^{97}` (`RMF.integral_sum_discrepancy_le_sqrt_weighted`); the limit is `1/2 + log 4 ≈ 1.886`.

L9 and the reduction are restated with `(2/log x)^q` and
`RMF.cErrD q = 3^{-(1-q)}2^{-max(1-2q, 0)}2^q` in place of `(16/log x)^q` and `RMF.cErr q`.  Their
only prime number theorem input, the window covering of step L8, enters as the hypothesis
`RMF.IsWindowCovering x`: the conclusion of `RMF.half_setIntegral_le_window_sumOf_explicit` at `x`,
which produces it for `x ≥ RMF.windowThreshold`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Mertens on `(√x, x]` -/

/-- **Mertens' first theorem on `(√x, x]`**: `∑_{√x<p≤x} (log p)/p ≤ (log x)/2 + 9.003` for
`x ≥ 1`, from `Mertens.E₁p.le` at `x` and `Mertens.E₁p.ge`, `Mertens.E₁.le` at `√x`
(`log 4 + 6 + (5 log 2 + 3)/4 < 9.003`). -/
lemma sum_log_div_largePrimeSet_sqrt_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ p ∈ largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊, Real.log p / p ≤ Real.log x / 2 + 9.003 := by
  have hs1 : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx
  have hfl : ⌊Real.sqrt x⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (Real.sqrt_le_self_iff.2 (Or.inr hx))
  have hsplit : (∑ p ∈ Finset.Ioc 0 ⌊Real.sqrt x⌋₊ with p.Prime, Real.log p / p)
      + ∑ p ∈ largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊, Real.log p / p
      = ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / p := by
    rw [largePrimeSet, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
    exact Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl
  have hup := Mertens.sum_log_prime_div_eq x
  have hle := Mertens.E₁p.le hx
  have hlow := Mertens.sum_log_prime_div_eq (Real.sqrt x)
  have hge := Mertens.E₁p.ge hs1
  have hE := Mertens.E₁.le
  have hsq : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt (by linarith)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h2 := Real.log_two_lt_d9
  linarith

/-! ### Step L7 on the primes of `(√x, x]` -/

/-- **Step L7 for the weighted sum, on the primes of `(√x, x]`, in closed form.**  For `x > 1` and
any set of primes of `(√x, x]`, the expected total discrepancy at `Y = log x` is at most
`(1 + 1/log x)(1/2 + log 4 + 9.003/log x)`: `RMF.integral_discrepancy_le_weighted` per prime,
`RMF.sum_log_div_largePrimeSet_sqrt_le` and `θ(x) ≤ x log 4`. -/
theorem integral_sum_discrepancy_le_sqrt_weighted_of_one_lt {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 1 < x)
    {S : Finset ℕ} (hS : S ⊆ largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊) :
    (∫ ω, ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
        discrepancy (fun ω => weightedExt fun q => X q ω) x p ω t)) ∂μ)
      ≤ (1 + 1 / Real.log x) * (1 / 2 + Real.log 4 + 9.003 / Real.log x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog0 : (0 : ℝ) < Real.log x := Real.log_pos hx
  have hSp : ∀ p ∈ S, Nat.Prime p := fun p hp => (mem_largePrimeSet.1 (hS hp)).2
  have hpos : ∀ p ∈ S, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hSp p hp).pos
  rw [integral_finsetSum]
  swap
  · intro p hp
    exact (((integrable_discrepancy (X := Real.log x) (isBoundedRMF_weightedExt hX) hx0.le
      (hpos p hp)).integral_prod_left.const_mul _).const_mul _).const_mul _
  have hper : ∀ p ∈ S, (∫ ω, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
        discrepancy (fun ω => weightedExt fun q => X q ω) x p ω t)) ∂μ)
      ≤ (1 + 1 / Real.log x)
          * ((Real.log x)⁻¹ * (Real.log p / p) + x⁻¹ * Real.log p) := by
    intro p hp
    have hp0 := hpos p hp
    rw [integral_const_mul, integral_const_mul]
    have h := integral_discrepancy_le_weighted hX hx0 hlog0 hp0
    have hlp : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
    calc Real.log p * ((p : ℝ)⁻¹ * ∫ ω, Real.log x / p * (∫ t in Set.Ioc (p : ℝ)
          ((p : ℝ) * (1 + 1 / Real.log x)),
            discrepancy (fun ω => weightedExt fun q => X q ω) x p ω t) ∂μ)
        ≤ Real.log p * ((p : ℝ)⁻¹ * ((1 + 1 / Real.log x) * (1 / Real.log x + p / x))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (by positivity)) hlp
      _ = (1 + 1 / Real.log x)
          * ((Real.log x)⁻¹ * (Real.log p / p) + x⁻¹ * Real.log p) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hS1 : ∑ p ∈ S, Real.log p / p ≤ Real.log x / 2 + 9.003 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hS fun p _ _ => log_div_natCast_nonneg p)
      (sum_log_div_largePrimeSet_sqrt_le hx.le)
  have hsub : S ⊆ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime} := fun p hp => by
    obtain ⟨⟨-, hpx⟩, hprime⟩ := mem_largePrimeSet.1 (hS hp)
    exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hprime.pos, hpx⟩, hprime⟩
  have hS2 : ∑ p ∈ S, Real.log p ≤ Real.log 4 * x :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
      Real.log_natCast_nonneg p) (sum_log_prime_le hx0.le)
  have hA : (Real.log x)⁻¹ * ∑ p ∈ S, Real.log p / p ≤ 1 / 2 + 9.003 / Real.log x := by
    calc (Real.log x)⁻¹ * ∑ p ∈ S, Real.log p / p
        ≤ (Real.log x)⁻¹ * (Real.log x / 2 + 9.003) :=
          mul_le_mul_of_nonneg_left hS1 (inv_nonneg.2 hlog0.le)
      _ = 1 / 2 + 9.003 / Real.log x := by field_simp
  have hB : x⁻¹ * ∑ p ∈ S, Real.log p ≤ Real.log 4 := by
    rw [inv_mul_le_iff₀ hx0]
    linarith
  have hr0 : (0 : ℝ) ≤ 1 + 1 / Real.log x := by positivity
  calc (1 + 1 / Real.log x) * ((Real.log x)⁻¹ * ∑ p ∈ S, Real.log p / p
        + x⁻¹ * ∑ p ∈ S, Real.log p)
      ≤ (1 + 1 / Real.log x) * (1 / 2 + 9.003 / Real.log x + Real.log 4) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) hr0
    _ = (1 + 1 / Real.log x) * (1 / 2 + Real.log 4 + 9.003 / Real.log x) := by ring

/-- `(1 + 1/L)(1/2 + log 4 + 9.003/L) ≤ 2` for `L ≥ 97` (`≈ 1.99951` at `L = 97`). -/
lemma one_add_inv_mul_sqrt_discrepancy_le_two {L : ℝ} (hL : 97 ≤ L) :
    (1 + 1 / L) * (1 / 2 + Real.log 4 + 9.003 / L) ≤ 2 := by
  have hL0 : 0 < L := by linarith
  have hl4 : Real.log 4 < 1.3862944 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
    linarith [Real.log_two_lt_d9]
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hu : 1 / L ≤ 1 / 97 := one_div_le_one_div_of_le (by norm_num) hL
  have h9 : 9.003 / L ≤ 9.003 / 97 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have h90 : 0 ≤ 9.003 / L := by positivity
  calc (1 + 1 / L) * (1 / 2 + Real.log 4 + 9.003 / L)
      ≤ (1 + 1 / 97) * (1 / 2 + 1.3862944 + 9.003 / 97) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    _ ≤ 2 := by norm_num

/-- **Step L7 for the weighted sum, on the primes of `(√x, x]`: `E[D] ≤ 2` for `x ≥ e^{97}`.**  The
twin of `RMF.integral_sum_discrepancy_le_weighted` (`≤ 16` for any primes up to `x`), through
`RMF.integral_sum_discrepancy_le_sqrt_weighted_of_one_lt`. -/
theorem integral_sum_discrepancy_le_sqrt_weighted {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : Real.exp 97 ≤ x)
    {S : Finset ℕ} (hS : S ⊆ largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊) :
    (∫ ω, ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
        discrepancy (fun ω => weightedExt fun q => X q ω) x p ω t)) ∂μ) ≤ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 97 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hx1 : 1 < x := by linarith [Real.add_one_le_exp (97 : ℝ)]
  exact le_trans (integral_sum_discrepancy_le_sqrt_weighted_of_one_lt hX hx1 hS)
    (one_add_inv_mul_sqrt_discrepancy_le_two hL)

/-! ### The window covering, as a hypothesis -/

/-- **The window covering at `x`**: the conclusion of
`RMF.half_setIntegral_le_window_sumOf_explicit` at this `x`, verbatim.  For every nonnegative `G`
integrable on the intervals above `1` and every set `S` of primes containing those of `(√x, x]`,
`½∫_{√x(1+1/log x)}^x G ≤ ∑_{p∈S} log p·(log x/p)∫_p^{p(1+1/log x)} G`.  That lemma produces it
for `x ≥ RMF.windowThreshold`. -/
def IsWindowCovering (x : ℝ) : Prop :=
  ∀ G : ℝ → ℝ, (∀ t, 0 ≤ G t) →
    (∀ c d : ℝ, 1 ≤ c → IntegrableOn G (Set.Ioc c d)) →
    ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) →
      (∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) →
      1 / 2 * (∫ t in Set.Ioc (Real.sqrt x * (1 + 1 / Real.log x)) x, G t)
        ≤ ∑ p ∈ S, Real.log p * (Real.log x / p
            * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), G t)

/-- `x ≥ e^{97}` gives `x ≥ 4`. -/
lemma four_le_of_exp_ninetySeven_le {x : ℝ} (hx : Real.exp 97 ≤ x) : 4 ≤ x := by
  linarith [Real.add_one_le_exp (97 : ℝ)]

/-! ### Steps L4–L9 with the window covering supplied -/

omit [MeasurableSpace Ω] in
/-- **`RMF.sum_normSq_ge_weighted_explicit` with the window covering supplied**: steps L4, L5 and L8
for the weighted sum, pointwise, for `x ≥ 4` with `RMF.IsWindowCovering x` (produced by
`RMF.half_setIntegral_le_window_sumOf_explicit` for `x ≥ RMF.windowThreshold`). -/
theorem sum_normSq_ge_weighted_of_windowCovering (g : Ω → ArithmeticFunction ℂ) (ω : Ω) {x : ℝ}
    (hx : 4 ≤ x) (hwin : IsWindowCovering x) (S : Finset ℕ) (hSp : ∀ p ∈ S, Nat.Prime p)
    (hSx : ∀ p ∈ S, (p : ℝ) ≤ x)
    (hS : ∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) :
    (8 * Real.log x)⁻¹ * (∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
          ‖randomSum g z ω‖ ^ 2 / z)
        - (∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
            ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
              discrepancy g x p ω t))) / Real.log x
      ≤ ∑ p ∈ S, (p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2 := by
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hr0 : (0 : ℝ) < 1 + 1 / Real.log x := by linarith
  have hpos : ∀ p ∈ S, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hSp p hp).pos
  have hp1 : ∀ p ∈ S, (1 : ℝ) ≤ p := fun p hp => by exact_mod_cast (hSp p hp).one_lt.le
  -- the four sums
  set V : ℝ := ∑ p ∈ S, (p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2 with hVdef
  set L : ℝ := ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2) with hLdef
  set Wsum : ℝ := ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
      ‖randomSum g (x / t) ω‖ ^ 2)) with hWdef
  set Dsum : ℝ := ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), discrepancy g x p ω t)) with hDdef
  set Gsum : ℝ := ∑ p ∈ S, Real.log p * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
      ‖randomSum g (x / t) ω‖ ^ 2 / |t|) with hGdef
  set M : ℝ := ∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
    ‖randomSum g z ω‖ ^ 2 / z with hMdef
  -- L4: `log p ≤ log x`
  have hL4 : L ≤ Real.log x * V :=
    sum_log_mul_le_log_mul_sum (x := x) (by linarith) hSx
      (v := fun p => (p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2) fun p => by positivity
  -- L5: smoothing, prime by prime, weighted by `log p / p`
  have hL5 : 1 / 4 * Wsum - Dsum ≤ L := by
    have hstep : ∀ p ∈ S, 1 / 4 * (Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
          ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
            ‖randomSum g (x / t) ω‖ ^ 2)))
        - Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
          ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), discrepancy g x p ω t))
        ≤ Real.log p * ((p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2) := by
      intro p hp
      have hb := smoothing_bound (f := g) hx0.le hlog0 (hpos p hp) ω
      have hw : (0 : ℝ) ≤ Real.log p * (p : ℝ)⁻¹ :=
        mul_nonneg (Real.log_natCast_nonneg p) (inv_nonneg.2 (hpos p hp).le)
      have := mul_le_mul_of_nonneg_left hb hw
      linarith [this]
    have hsum := Finset.sum_le_sum hstep
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    exact hsum
  -- L8: the extra `1/p` against `1/t`, then the covering
  have hGW : Gsum ≤ Wsum := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hp0 := hpos p hp
    have hIG := integrableOn_normSq_randomSum_div_abs g hx0.le (c := (p : ℝ))
      (d := (p : ℝ) * (1 + 1 / Real.log x)) (hp1 p hp) ω
    have hIA := (integrableOn_normSq_randomSum_div g hx0.le (c := (p : ℝ))
      (d := (p : ℝ) * (1 + 1 / Real.log x)) (hp1 p hp) ω).const_mul ((p : ℝ)⁻¹)
    have hmono : (∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
          ‖randomSum g (x / t) ω‖ ^ 2 / |t|)
        ≤ ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
          (p : ℝ)⁻¹ * ‖randomSum g (x / t) ω‖ ^ 2 := by
      refine setIntegral_mono_on hIG hIA measurableSet_Ioc fun t ht => ?_
      have ht0 : (0 : ℝ) < t := lt_trans hp0 ht.1
      rw [abs_of_pos ht0, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hp0 ht.1.le) (by positivity)
    rw [integral_const_mul] at hmono
    have hlp : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
    have hcoef : (0 : ℝ) ≤ Real.log x / p := by positivity
    calc Real.log p * (Real.log x / p * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
          ‖randomSum g (x / t) ω‖ ^ 2 / |t|)
        ≤ Real.log p * (Real.log x / p * ((p : ℝ)⁻¹ * ∫ t in Set.Ioc (p : ℝ)
          ((p : ℝ) * (1 + 1 / Real.log x)), ‖randomSum g (x / t) ω‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hcoef) hlp
      _ = Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p * ∫ t in Set.Ioc (p : ℝ)
          ((p : ℝ) * (1 + 1 / Real.log x)), ‖randomSum g (x / t) ω‖ ^ 2)) := by ring
  have hcover := hwin (fun t => ‖randomSum g (x / t) ω‖ ^ 2 / |t|)
    (fun t => by positivity)
    (fun c d hc => integrableOn_normSq_randomSum_div_abs g hx0.le hc ω) S hSp hS
  -- the substitution
  have hsq0 : (0 : ℝ) < Real.sqrt x := by linarith
  have ha0 : (0 : ℝ) < Real.sqrt x * (1 + 1 / Real.log x) := by positivity
  have hax : Real.sqrt x * (1 + 1 / Real.log x) ≤ x := by
    have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    nlinarith
  have hxa : x / (Real.sqrt x * (1 + 1 / Real.log x)) = Real.sqrt x / (1 + 1 / Real.log x) := by
    have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    field_simp
    nlinarith
  have habs : (∫ t in Set.Ioc (Real.sqrt x * (1 + 1 / Real.log x)) x,
        ‖randomSum g (x / t) ω‖ ^ 2 / |t|)
      = ∫ t in Set.Ioc (Real.sqrt x * (1 + 1 / Real.log x)) x,
        ‖randomSum g (x / t) ω‖ ^ 2 / t :=
    setIntegral_congr_fun measurableSet_Ioc fun t ht => by
      rw [abs_of_pos (lt_trans ha0 ht.1)]
  have hsub := setIntegral_div_eq_dz_div_z g hx0 ha0 hax ω
  rw [hxa] at hsub
  rw [habs, hsub] at hcover
  -- assemble: `M/8 ≤ Gsum/4 ≤ Wsum/4 ≤ L + Dsum ≤ log x · V + Dsum`
  have hkey : M / 8 - Dsum ≤ Real.log x * V := by linarith
  rw [show (8 * Real.log x)⁻¹ * M - Dsum / Real.log x = (M / 8 - Dsum) / Real.log x by
    field_simp]
  rw [div_le_iff₀ hlog0]
  linarith

/-- **Step L9, `RMF.meanSquare_le_sum_weighted_explicit` with `2` in place of `16`**, on the
primes of `(√x, x]`: for `x ≥ e^{97}` with `RMF.IsWindowCovering x` (produced by
`RMF.half_setIntegral_le_window_sumOf_explicit` for `x ≥ RMF.windowThreshold`), `0 ≤ q ≤ 1` and `S`
the primes of `(√x, x]`,
`(8 log x)^{-q}E[weightedMeanSquare^q] - (2/log x)^q ≤ E[(∑_{p∈S} p^{-1}|S(x/p)|²)^q]`. -/
theorem meanSquare_le_sum_weighted_of_windowCovering {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp 97 ≤ x)
    (hwin : IsWindowCovering x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (S : Finset ℕ)
    (hSp : ∀ p ∈ S, Nat.Prime p) (hSs : ∀ p ∈ S, Real.sqrt x < p) (hSx : ∀ p ∈ S, (p : ℝ) ≤ x)
    (hS : ∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) :
    (8 * Real.log x)⁻¹ ^ q
          * ∫ ω, weightedMeanSquare (fun ω => squarefreeExtension fun r => X r ω) x ω ^ q ∂μ
        - (2 / Real.log x) ^ q
      ≤ ∫ ω, (∑ p ∈ S, (p : ℝ)⁻¹ * ‖weightedRademacherSum
          (fun ω => squarefreeExtension fun r => X r ω) (x / p) ω‖ ^ 2) ^ q ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hx4 : (4 : ℝ) ≤ x := four_le_of_exp_ninetySeven_le hx
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx4
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun r => X r ω with hfdef
  set g : Ω → ArithmeticFunction ℂ := fun ω => weightedExt fun r => X r ω with hgdef
  have hg : IsBoundedRMF g μ := isBoundedRMF_weightedExt hX
  have hSsub : S ⊆ largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊ := fun p hp =>
    mem_largePrimeSet.2 ⟨⟨(Nat.floor_lt (Real.sqrt_nonneg x)).2 (hSs p hp),
      Nat.le_floor (hSx p hp)⟩, hSp p hp⟩
  -- the three quantities, in terms of `g`
  set w : ℝ := Real.sqrt x / (1 + 1 / Real.log x) with hwdef
  set Mg : Ω → ℝ := fun ω => ∫ z in Set.Ioc 1 w, ‖randomSum g z ω‖ ^ 2 / z with hMgdef
  set D : Ω → ℝ := fun ω => ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), discrepancy g x p ω t))
    with hDdef
  set A : Ω → ℝ := fun ω => ∑ p ∈ S, (p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2 with hAdef
  have hMeq : ∀ ω, weightedMeanSquare f x ω = Mg ω := by
    intro ω
    simp only [weightedMeanSquare, hMgdef, hfdef, hgdef, hwdef, weightedRademacherSum_eq_randomSum]
  have hAeq : ∀ ω, (∑ p ∈ S, (p : ℝ)⁻¹ * ‖weightedRademacherSum f (x / p) ω‖ ^ 2) = A ω := by
    intro ω
    simp only [hAdef, hfdef, hgdef, weightedRademacherSum_eq_randomSum]
  -- nonnegativity
  have hM0 : ∀ ω, 0 ≤ Mg ω := fun ω => by
    rw [← hMeq]
    exact weightedMeanSquare_nonneg f x ω
  have hD0 : ∀ ω, 0 ≤ D ω := by
    intro ω
    refine Finset.sum_nonneg fun p hp => mul_nonneg (Real.log_natCast_nonneg p) ?_
    refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (mul_nonneg (by positivity) ?_)
    exact setIntegral_nonneg measurableSet_Ioc fun t _ => discrepancy_nonneg g x p ω t
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => Finset.sum_nonneg fun p _ => by positivity
  have hP0 : ∀ ω, 0 ≤ (8 * Real.log x)⁻¹ * Mg ω := fun ω =>
    mul_nonneg (by positivity) (hM0 ω)
  have hR0 : ∀ ω, 0 ≤ D ω / Real.log x := fun ω => div_nonneg (hD0 ω) hlog0.le
  -- integrability
  have hMi : Integrable Mg μ := (integrable_weightedMeanSquare_prod hX w).integral_prod_left
  have hDi : Integrable D μ := integrable_weightedDiscrepancySum hX hx0.le hSp
  have hAi : Integrable A μ :=
    integrable_finsetSum _ fun p _ => (integrable_normSq_randomSum hg (x / p)).const_mul _
  have hPi : Integrable (fun ω => (8 * Real.log x)⁻¹ * Mg ω) μ := hMi.const_mul _
  have hRi : Integrable (fun ω => D ω / Real.log x) μ := hDi.div_const _
  have hPq := integrable_rpow_of_integrable hPi (Filter.Eventually.of_forall hP0) hq0 hq1
  have hRq := integrable_rpow_of_integrable hRi (Filter.Eventually.of_forall hR0) hq0 hq1
  have hAq := integrable_rpow_of_integrable hAi (Filter.Eventually.of_forall hA0) hq0 hq1
  -- the pointwise inequality, at the `q`-th power
  have hpt : ∀ ω, ((8 * Real.log x)⁻¹ * Mg ω) ^ q - (D ω / Real.log x) ^ q ≤ A ω ^ q :=
    fun ω => rpow_sub_rpow_le_of_sub_le (hP0 ω) (hR0 ω) (hA0 ω)
      (sum_normSq_ge_weighted_of_windowCovering g ω hx4 hwin S hSp hSx hS) hq0 hq1
  have hmain : (∫ ω, ((8 * Real.log x)⁻¹ * Mg ω) ^ q ∂μ) - ∫ ω, (D ω / Real.log x) ^ q ∂μ
      ≤ ∫ ω, A ω ^ q ∂μ := by
    rw [← integral_sub hPq hRq]
    exact integral_mono (hPq.sub hRq) hAq hpt
  -- the two evaluations
  have hPval : (∫ ω, ((8 * Real.log x)⁻¹ * Mg ω) ^ q ∂μ)
      = (8 * Real.log x)⁻¹ ^ q * ∫ ω, Mg ω ^ q ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      Real.mul_rpow (by positivity) (hM0 ω))
  have hRval : (∫ ω, (D ω / Real.log x) ^ q ∂μ) ≤ (2 / Real.log x) ^ q := by
    refine le_trans (integral_rpow_le_rpow_integral hq0 hq1
      (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (hR0 ω)) hRi hRq) ?_
    refine Real.rpow_le_rpow (integral_nonneg hR0) ?_ hq0
    rw [integral_div]
    exact div_le_div_of_nonneg_right (integral_sum_discrepancy_le_sqrt_weighted hX hx hSsub)
      hlog0.le
  -- back to the weighted sums
  have hL : (∫ ω, weightedMeanSquare f x ω ^ q ∂μ) = ∫ ω, Mg ω ^ q ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hMeq ω])
  have hR : (∫ ω, (∑ p ∈ S, (p : ℝ)⁻¹ * ‖weightedRademacherSum f (x / p) ω‖ ^ 2) ^ q ∂μ)
      = ∫ ω, A ω ^ q ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hAeq ω])
  rw [hL, hR]
  rw [hPval] at hmain
  linarith

/-! ### The reduction with the error constant `RMF.cErrD` -/

/-- **The error constant at the discrepancy constant `2`**: `3^{-(1-q)}2^{-max(1-2q, 0)}2^q`,
`RMF.cErr` with `2` in place of `16`. -/
noncomputable def cErrD (q : ℝ) : ℝ :=
  (3 : ℝ) ^ (-(1 - q)) * (2 : ℝ) ^ (-max (1 - 2 * q) 0) * (2 : ℝ) ^ q

lemma cErrD_pos (q : ℝ) : 0 < cErrD q := by
  unfold cErrD
  positivity

/-- **`RMF.reduction_arith_explicit` with `2` in place of `16`.**  From Khintchine
`3^{-(1-q)}2^{-max(1-2q, 0)}ER ≤ ES`, L9 `(8L)^{-q}EM - (2/L)^q ≤ ER` and Parseval
`(2π)^{-q}EW - (π⁻¹e^{-V})^qEJ ≤ EM`:
`cRed·L^{-q}EW - cJ·e^{-Vq}L^{-q}EJ - cErrD·L^{-q} ≤ ES`. -/
lemma reduction_arith_explicit' {ES ER EM EW EJ L V q : ℝ} (hL : 0 < L)
    (hkh : (3 : ℝ) ^ (-(1 - q)) * (2 : ℝ) ^ (-max (1 - 2 * q) 0) * ER ≤ ES)
    (h9 : (8 * L)⁻¹ ^ q * EM - (2 / L) ^ q ≤ ER)
    (hPar : (2 * Real.pi)⁻¹ ^ q * EW - (Real.pi⁻¹ * Real.exp (-V)) ^ q * EJ ≤ EM) :
    cRed q * L ^ (-q) * EW - cJ q * Real.exp (-(V * q)) * L ^ (-q) * EJ - cErrD q * L ^ (-q)
      ≤ ES := by
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have hLq : L⁻¹ ^ q = L ^ (-q) := by rw [Real.inv_rpow hL.le, ← Real.rpow_neg hL.le]
  have h8 : (8 * L)⁻¹ ^ q = (8 : ℝ)⁻¹ ^ q * L ^ (-q) := by
    rw [mul_inv, Real.mul_rpow (by norm_num) (inv_nonneg.2 hL.le), hLq]
  have h2 : (2 / L) ^ q = (2 : ℝ) ^ q * L ^ (-q) := by
    rw [div_eq_mul_inv, Real.mul_rpow (by norm_num) (inv_nonneg.2 hL.le), hLq]
  have hpe : (Real.pi⁻¹ * Real.exp (-V)) ^ q = Real.pi⁻¹ ^ q * Real.exp (-(V * q)) := by
    rw [Real.mul_rpow (inv_nonneg.2 hπ0.le) (Real.exp_pos _).le, ← Real.exp_mul, neg_mul]
  have hred : (16 * Real.pi) ^ (-q) = (8 : ℝ)⁻¹ ^ q * (2 * Real.pi)⁻¹ ^ q := by
    rw [← Real.mul_rpow (by norm_num) (inv_nonneg.2 (by positivity)), ← mul_inv,
      show (8 : ℝ) * (2 * Real.pi) = 16 * Real.pi by ring,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 16 * Real.pi),
      Real.inv_rpow (by positivity : (0 : ℝ) ≤ 16 * Real.pi)]
  have hJ : (8 * Real.pi) ^ (-q) = (8 : ℝ)⁻¹ ^ q * Real.pi⁻¹ ^ q := by
    rw [← Real.mul_rpow (by norm_num) (inv_nonneg.2 hπ0.le), ← mul_inv,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 8 * Real.pi),
      Real.inv_rpow (by positivity : (0 : ℝ) ≤ 8 * Real.pi)]
  rw [h8, h2] at h9
  rw [hpe] at hPar
  have hk0 : 0 ≤ (3 : ℝ) ^ (-(1 - q)) * (2 : ℝ) ^ (-max (1 - 2 * q) 0) := by positivity
  have hA0 : 0 ≤ (8 : ℝ)⁻¹ ^ q * L ^ (-q) := by positivity
  have p1 := mul_le_mul_of_nonneg_left hPar hA0
  have p2 : (8 : ℝ)⁻¹ ^ q * L ^ (-q)
        * ((2 * Real.pi)⁻¹ ^ q * EW - Real.pi⁻¹ ^ q * Real.exp (-(V * q)) * EJ)
      - (2 : ℝ) ^ q * L ^ (-q) ≤ ER := by linarith
  have p3 := mul_le_mul_of_nonneg_left p2 hk0
  unfold cRed cJ cErrD
  rw [hred, hJ]
  linarith

/-- **Gerspach's Proposition 6 (arXiv:1909.10224) at `α = 1` with the error constant
`RMF.cErrD`**, for any main term the Parseval step bounds:
`RMF.le_integral_rpow_weightedRademacherSum_of_parseval_explicit` with `cErrD` in place of `cErr`,
for `x ≥ e^{97}` with `RMF.IsWindowCovering x` (produced by
`RMF.half_setIntegral_le_window_sumOf_explicit` for `x ≥ RMF.windowThreshold`),
`log x ≥ 3V + 3`, `0 < q ≤ 1`:

`cRed(q)(log x)^{-q}E[W^q] - cJ(q)e^{-Vq}(log x)^{-q}E[J(V/log x)^q] - cErrD(q)(log x)^{-q}`
`  ≤ E|S(x)|^{2q}`. -/
theorem le_integral_rpow_weightedRademacherSum_of_parseval_of_windowCovering {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {V x q : ℝ} (hV : 0 < V)
    (hx : Real.exp 97 ≤ x) (hwin : IsWindowCovering x) (hlogV : 3 * V + 3 ≤ Real.log x)
    (hq0 : 0 < q) (hq1 : q ≤ 1) {W : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω)
    (hae : ∀ᵐ ω ∂μ, (2 * Real.pi)⁻¹ * W ω - Real.pi⁻¹ * Real.exp (-V) * (∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
            ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
          / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ weightedMeanSquare (fun ω => squarefreeExtension fun p => X p ω) x ω) :
    cRed q * Real.log x ^ (-q) * (∫ ω, W ω ^ q ∂μ)
      - cJ q * Real.exp (-(V * q)) * Real.log x ^ (-q) * (∫ ω, (∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
            / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      - cErrD q * Real.log x ^ (-q)
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hx4 : (4 : ℝ) ≤ x := four_le_of_exp_ninetySeven_le hx
  obtain ⟨hx0, hlog, -, -, -⟩ := log_scale_facts hx4
  have hσ₂0 : 0 < V / Real.log x := div_pos hV (by linarith)
  have hy2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (2 : ℝ) ≤ x))
  -- steps L1–L3 and L4–L9, on the primes of `(√x, x]`
  obtain ⟨hSp, hSx, hScov⟩ := primesIoc_sqrt_spec hx0.le
  have hSs : ∀ p ∈ largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊, Real.sqrt x < p := fun p hp =>
    (Nat.floor_lt (Real.sqrt_nonneg x)).1 (mem_largePrimeSet.1 hp).1.1
  have hkh := khintchine_rough_weighted_of_le_one hX (by linarith)
    (floor_lt_floor_sqrt_add_one_sq hx0.le) hq0 hq1
  have h9 := meanSquare_le_sum_weighted_of_windowCovering hX hx hwin hq0.le hq1
    (largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊) hSp hSs hSx hScov
  -- Parseval, at the `q`-th power
  have hPar := integral_rpow_sub_le_of_ae hae (by positivity) (by positivity) hq0.le hq1 hW0
    (fun ω => integral_nonneg fun t => sq_nonneg _)
    (fun ω => weightedMeanSquare_nonneg _ x ω)
    (integrable_rpow_eulerProductLine_of_two_le hX hy2 hσ₂0 hq0.le)
    (integrable_rpow_of_integrable (integrable_weightedMeanSquare hX x)
      (Filter.Eventually.of_forall fun ω => weightedMeanSquare_nonneg _ x ω) hq0.le hq1)
  exact reduction_arith_explicit' (by linarith) hkh h9 hPar

/-- **The reduction at the canonical main term** `W = J(2V/log x)`, with the window covering
supplied: `RMF.le_integral_rpow_weightedRademacherSum_euler_full_explicit` with `RMF.cErrD` in
place of `RMF.cErr`, for `x ≥ e^{97}` with `RMF.IsWindowCovering x` (produced by
`RMF.half_setIntegral_le_window_sumOf_explicit` for `x ≥ RMF.windowThreshold`),
`log x ≥ 3V + 3` and `0 < q ≤ 1`, at `σ = 2V/log x`. -/
theorem le_integral_rpow_weightedRademacherSum_euler_full_of_windowCovering {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {V x q : ℝ} (hV : 0 < V)
    (hx : Real.exp 97 ≤ x) (hwin : IsWindowCovering x) (hlogV : 3 * V + 3 ≤ Real.log x)
    (hq0 : 0 < q) (hq1 : q ≤ 1) :
    cRed q * (Real.log x ^ (-q) * ∫ ω, (∫ u : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
            (shiftLine (2 * V / Real.log x) u) ω
          / (((2 * V / Real.log x : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      - cJ q * Real.exp (-(V * q)) * Real.log x ^ (-q) * (∫ ω, (∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
            / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      - cErrD q * Real.log x ^ (-q)
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  have hx4 : (4 : ℝ) ≤ x := four_le_of_exp_ninetySeven_le hx
  have h := le_integral_rpow_weightedRademacherSum_of_parseval_of_windowCovering hX hV hx hwin
    hlogV hq0 hq1 (fun ω => integral_nonneg fun t => sq_nonneg _)
    (Filter.Eventually.of_forall fun ω => weightedMeanSquare_ge_line_full hV hlogV hx4 ω)
  simp only [← integral_lineDiv_eq_shiftLine]
  rw [← mul_assoc]
  exact h

end RMF
