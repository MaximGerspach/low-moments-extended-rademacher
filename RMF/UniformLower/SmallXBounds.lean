/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.MainExplicit
import Mathlib.NumberTheory.Bertrand

/-!
# Below `½` for small `x`: three elementary lower bounds

For a Rademacher family, `0 < q < ½` and `u = 1 - 2q`, three lower bounds for `E|S(x)|^{2q}` that
need no Euler product:

* **H** (Hölder), every `x ≥ 1`: `(1 + log x)^{-u}`
  (`RMF.le_integral_rpow_weightedRademacherSum_holder`), from `E|S| ≥ 1` and `E|S|² ≤ 1 + log x`;
* **I** (interpolation), every `x ≥ 3` and `½ < b ≤ 1`: `U_b^{-u/(2b-1)}` with the explicit upper
  bound `U_b = 25(log x)^{b(2b-1)}min{1/(2b-1), log log x}^{3/4}` of
  `RMF.weighted_rademacher_moments_upper_uniform_explicit`
  (`RMF.le_integral_rpow_weightedRademacherSum_interp`), by log-convexity of the moments
  (`RMF.integral_le_rpow_integral_rpow_mul_rpow_integral_rpow`) and `E|S| ≥ 1`;
* **F** (the floor), every `x ≥ 10^{16}`: `2^{-u}3^{-(1-q)}(0.23/log x)^q`
  (`RMF.le_integral_rpow_weightedRademacherSum_floor_small`), Khintchine with the primes of
  `(x/2, x]` counted by Chebyshev's method: `C(2n, n) ≤ (2n)^{√(2n)}4^{2n/3}∏_{n<p≤2n} p`
  (`RMF.centralBinom_le_mul_prod_largePrimeSet`) gives `θ(2n) - θ(n) ≥ (n/3)log 4 - O(√n log n)`,
  so `∑_{x/2<p≤x} 1/p ≥ 0.23/log x` (`RMF.le_sum_inv_largePrimeSet_half_small`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Hölder between two exponents -/

/-- **Log-convexity of the moments**: for `a < 1 < c` and `X ≥ 0` with `X^a`, `X^c`
integrable, `E X ≤ (E X^a)^{(c-1)/(c-a)}(E X^c)^{(1-a)/(c-a)}` — Hölder with the conjugate pair
`((c-a)/(c-1), (c-a)/(1-a))` on `X = X^{a(c-1)/(c-a)}X^{c(1-a)/(c-a)}`. -/
theorem integral_le_rpow_integral_rpow_mul_rpow_integral_rpow {X : Ω → ℝ} {μ : Measure Ω}
    {a c : ℝ} (ha1 : a < 1) (hc1 : 1 < c) (hX0 : 0 ≤ᵐ[μ] X)
    (hXa : Integrable (fun ω => X ω ^ a) μ) (hXc : Integrable (fun ω => X ω ^ c) μ) :
    (∫ ω, X ω ∂μ)
      ≤ (∫ ω, X ω ^ a ∂μ) ^ ((c - 1) / (c - a)) * (∫ ω, X ω ^ c ∂μ) ^ ((1 - a) / (c - a)) := by
  have hca : 0 < c - a := by linarith
  have hc1' : 0 < c - 1 := by linarith
  have ha1' : 0 < 1 - a := by linarith
  have hp : 0 < (c - a) / (c - 1) := div_pos hca hc1'
  have hp' : 0 < (c - a) / (1 - a) := div_pos hca ha1'
  have hpq : Real.HolderConjugate ((c - a) / (c - 1)) ((c - a) / (1 - a)) := by
    have h := Real.holderConjugate_one_div (a := (c - 1) / (c - a)) (b := (1 - a) / (c - a))
      (div_pos hc1' hca) (div_pos ha1' hca) (by field_simp; ring)
    rwa [one_div_div, one_div_div] at h
  have hf0 : 0 ≤ᵐ[μ] fun ω => X ω ^ (a / ((c - a) / (c - 1))) := by
    filter_upwards [hX0] with ω hω
    exact Real.rpow_nonneg hω _
  have hg0 : 0 ≤ᵐ[μ] fun ω => X ω ^ (c / ((c - a) / (1 - a))) := by
    filter_upwards [hX0] with ω hω
    exact Real.rpow_nonneg hω _
  have hHold := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf0 hg0
    (memLp_rpow_div_of_integrable_rpow hp hX0 hXa) (memLp_rpow_div_of_integrable_rpow hp' hX0 hXc)
  have hsum : a / ((c - a) / (c - 1)) + c / ((c - a) / (1 - a)) = 1 := by
    field_simp
    ring
  have e1 : (∫ ω, X ω ^ (a / ((c - a) / (c - 1))) * X ω ^ (c / ((c - a) / (1 - a))) ∂μ)
      = ∫ ω, X ω ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hX0] with ω hω
    rw [← Real.rpow_add' hω (by rw [hsum]; norm_num), hsum, Real.rpow_one]
  have e2 : (∫ ω, (X ω ^ (a / ((c - a) / (c - 1)))) ^ ((c - a) / (c - 1)) ∂μ)
      = ∫ ω, X ω ^ a ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hX0] with ω hω
    rw [← Real.rpow_mul hω, div_mul_cancel₀ _ hp.ne']
  have e3 : (∫ ω, (X ω ^ (c / ((c - a) / (1 - a)))) ^ ((c - a) / (1 - a)) ∂μ)
      = ∫ ω, X ω ^ c ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hX0] with ω hω
    rw [← Real.rpow_mul hω, div_mul_cancel₀ _ hp'.ne']
  rw [e1, e2, e3, one_div_div, one_div_div] at hHold
  exact hHold

/-- **Interpolation, the arithmetic**: for `a < 1 < c`, `1 ≤ E ≤ A^{(c-1)/(c-a)}B^{(1-a)/(c-a)}`,
`A ≥ 0` and `0 < B ≤ U`, `U^{-(1-a)/(c-1)} ≤ A`. -/
lemma rpow_neg_le_of_interp {E A B U a c : ℝ} (ha1 : a < 1) (hc1 : 1 < c) (hE : 1 ≤ E)
    (hH : E ≤ A ^ ((c - 1) / (c - a)) * B ^ ((1 - a) / (c - a))) (hA0 : 0 ≤ A) (hB : 0 < B)
    (hBU : B ≤ U) :
    U ^ (-((1 - a) / (c - 1))) ≤ A := by
  have hca : 0 < c - a := by linarith
  have hc1' : 0 < c - 1 := by linarith
  have hθ : 0 < (c - 1) / (c - a) := div_pos hc1' hca
  have hφ0 : 0 < B ^ ((1 - a) / (c - a)) := Real.rpow_pos_of_pos hB _
  have h1 : B ^ (-((1 - a) / (c - a))) ≤ A ^ ((c - 1) / (c - a)) := by
    rw [Real.rpow_neg hB.le, ← one_div, div_le_iff₀ hφ0]
    linarith
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hB.le _) h1 (inv_nonneg.2 hθ.le)
  rw [← Real.rpow_mul hB.le, ← Real.rpow_mul hA0, mul_inv_cancel₀ hθ.ne', Real.rpow_one] at h2
  have e : -((1 - a) / (c - a)) * ((c - 1) / (c - a))⁻¹ = -((1 - a) / (c - 1)) := by
    field_simp
  rw [e] at h2
  have hexp : -((1 - a) / (c - 1)) ≤ 0 := by
    have : 0 ≤ (1 - a) / (c - 1) := div_nonneg (by linarith) hc1'.le
    linarith
  exact le_trans (Real.rpow_le_rpow_of_nonpos hB hBU hexp) h2

/-- **I, interpolation against the upper bound `C = 25`**: for a Rademacher family, `x ≥ 3`,
`0 < q < ½` and `½ < b ≤ 1`, with `U = 25(log x)^{b(2b-1)}min{1/(2b-1), log log x}^{3/4}`
(`RMF.weighted_rademacher_moments_upper_uniform_explicit` at `b`),
`U^{-(1-2q)/(2b-1)} ≤ E|S(x)|^{2q}`: `1 ≤ E|S| ≤ (E|S|^{2q})^θ(E|S|^{2b})^{1-θ}`,
`θ = (2b-1)/(2b-2q)`. -/
theorem le_integral_rpow_weightedRademacherSum_interp {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q b : ℝ} (hx : 3 ≤ x) (hq0 : 0 < q) (hq : q < 1 / 2)
    (hb : 1 / 2 < b) (hb1 : b ≤ 1) :
    (25 * (Real.log x ^ (b * (2 * b - 1))
        * min (2 * b - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ)))
        ^ (-((1 - 2 * q) / (2 * b - 1)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hint : ∀ r : ℝ, 0 < r → Integrable (fun ω =>
      ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ r) μ :=
    fun r hr => by
      have h := (memLp_weightedRademacherSum hX x (ENNReal.ofReal r)).integrable_norm_rpow
        (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top
      rwa [ENNReal.toReal_ofReal hr.le] at h
  have hH := integral_le_rpow_integral_rpow_mul_rpow_integral_rpow (μ := μ)
    (X := fun ω =>
      ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖)
    (a := 2 * q) (c := 2 * b) (by linarith) (by linarith)
    (Filter.Eventually.of_forall fun ω => norm_nonneg _) (hint _ (by linarith))
    (hint _ (by linarith))
  have hB1 := one_le_integral_rpow_weightedRademacherSum hX hx1 hb.le
  have hU := (weighted_rademacher_moments_upper_uniform_explicit Ω X μ hX x hx).2.2 b hb hb1
  exact rpow_neg_le_of_interp (by linarith) (by linarith)
    (one_le_integral_norm_weightedRademacherSum hX hx1) hH
    (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) (by linarith) hU

/-! ### Hölder -/

/-- **H, Hölder**: for a Rademacher family, `x ≥ 1` and `0 < q < ½`,
`(1 + log x)^{-(1-2q)} ≤ E|S(x)|^{2q}`: `E|S|^{2q} ≥ (E|S|)^{2-2q}/(E|S|²)^{1-2q}`
(`RMF.rpow_integral_div_rpow_integral_sq_le_integral_rpow`), `E|S| ≥ 1` and
`E|S|² ≤ 1 + log x` (`RMF.integral_normSq_weightedRademacherSum_le_one_add_log`). -/
theorem le_integral_rpow_weightedRademacherSum_holder {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 < q) (hq : q < 1 / 2) :
    (1 + Real.log x) ^ (-(1 - 2 * q))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hint : ∀ r : ℝ, 0 < r → Integrable (fun ω =>
      ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ r) μ :=
    fun r hr => by
      have h := (memLp_weightedRademacherSum hX x (ENNReal.ofReal r)).integrable_norm_rpow
        (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top
      rwa [ENNReal.toReal_ofReal hr.le] at h
  have h1 := one_le_integral_norm_weightedRademacherSum hX hx
  have h2 : (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 : ℝ) ∂μ) ≤ 1 + Real.log x := by
    simp only [Real.rpow_two]
    exact integral_normSq_weightedRademacherSum_le_one_add_log hX.isRademacherRMF hx
  have hpos : 0 < ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 : ℝ) ∂μ := by
    have h := one_le_integral_rpow_weightedRademacherSum hX hx (q := 1) (by norm_num)
    rw [show (2 : ℝ) * 1 = 2 by norm_num] at h
    linarith
  have hPZ := rpow_integral_div_rpow_integral_sq_le_integral_rpow (μ := μ)
    (X := fun ω =>
      ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖)
    (q := 2 * q) (by linarith) (by linarith)
    (Filter.Eventually.of_forall fun ω => norm_nonneg _) (hint _ (by linarith))
    (hint 2 (by norm_num)) hpos
  have hnum1 : 1 ≤ (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ∂μ) ^ (2 - 2 * q) := Real.one_le_rpow h1 (by linarith)
  have hden0 : 0 < (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 : ℝ) ∂μ) ^ (1 - 2 * q) := Real.rpow_pos_of_pos hpos _
  have hden := Real.rpow_le_rpow hpos.le h2 (by linarith : (0 : ℝ) ≤ 1 - 2 * q)
  rw [Real.rpow_neg (by linarith)]
  refine le_trans (inv_anti₀ hden0 hden) (le_trans ?_ hPZ)
  rw [div_eq_mul_inv]
  exact le_mul_of_one_le_left (inv_nonneg.2 hden0.le) hnum1

/-! ### The primes of `(x/2, x]`, by the central binomial coefficient -/

/-- **The central binomial coefficient keeps the primes of `(n, 2n]`**: for `n > 2`,
`C(2n, n) ≤ (2n)^{⌊√(2n)⌋}4^{⌊2n/3⌋}∏_{n<p≤2n} p`.  The bound of Bertrand's postulate
(`centralBinom_le_of_no_bertrand_prime`) with the primes of `(n, 2n]` kept: those of `(2n/3, n]`
do not divide `C(2n, n)`, those above `n` divide it once. -/
lemma centralBinom_le_mul_prod_largePrimeSet {n : ℕ} (hn : 2 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)
      * ∏ p ∈ largePrimeSet n (2 * n), p := by
  have n_pos : 0 < n := by omega
  have n2_pos : 1 ≤ 2 * n := by omega
  let f : ℕ → ℕ := fun p => p ^ n.centralBinom.factorization p
  -- the primes up to `2n/3`, as in Bertrand's postulate
  have hA : ∏ p ∈ Finset.range (2 * n / 3 + 1), f p
      ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
    let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
    have hS : ∏ p ∈ S, f p = ∏ p ∈ Finset.range (2 * n / 3 + 1), f p := by
      refine Finset.prod_filter_of_ne fun p _ h => ?_
      contrapose h
      dsimp only [f]
      rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom h, pow_zero]
    rw [← hS, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
      · exact Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)
      have hcard : (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun p hp => ?_).trans hcard.le)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
      refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  -- the primes of `(2n/3, 2n]`: only those above `n` divide, once
  have hsub : largePrimeSet n (2 * n) ⊆ Finset.Ico (2 * n / 3 + 1) (2 * n + 1) := fun p hp => by
    obtain ⟨⟨h1, h2⟩, -⟩ := mem_largePrimeSet.1 hp
    rw [Finset.mem_Ico]
    omega
  have hB : ∏ p ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1), f p
      ≤ ∏ p ∈ largePrimeSet n (2 * n), p := by
    calc ∏ p ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1), f p
        ≤ ∏ p ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1),
            if p ∈ largePrimeSet n (2 * n) then p else 1 := by
          refine Finset.prod_le_prod' fun p hp => ?_
          rw [Finset.mem_Ico] at hp
          split_ifs with hL
          · obtain ⟨⟨hnp, -⟩, hprime⟩ := mem_largePrimeSet.1 hL
            refine (pow_right_mono₀ hprime.one_lt.le ?_).trans (pow_one p).le
            exact Nat.factorization_choose_le_one (by nlinarith)
          · have hv : n.centralBinom.factorization p = 0 := by
              by_cases hprime : p.Prime
              · have hpn : p ≤ n := by
                  by_contra h
                  exact hL (mem_largePrimeSet.2 ⟨⟨by omega, by omega⟩, hprime⟩)
                exact Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn
                  (by omega)
              · exact Nat.factorization_eq_zero_of_not_prime _ hprime
            dsimp only [f]
            rw [hv, pow_zero]
      _ = ∏ p ∈ largePrimeSet n (2 * n), p := by
          rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.filter_mem_eq_inter,
            Finset.inter_eq_right.2 hsub]
  calc n.centralBinom = ∏ p ∈ Finset.range (2 * n + 1), f p :=
        (Nat.prod_pow_factorization_centralBinom n).symm
    _ = (∏ p ∈ Finset.range (2 * n / 3 + 1), f p)
          * ∏ p ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1), f p :=
        (Finset.prod_range_mul_prod_Ico f (by omega)).symm
    _ ≤ _ := Nat.mul_le_mul hA hB

/-- **The primes of `(n, 2n]`, by Chebyshev's method**: for `n ≥ 4`,
`n log 4 - log n - ⌊√(2n)⌋log(2n) - ⌊2n/3⌋log 4 ≤ ∑_{n<p≤2n} log p`, from
`RMF.centralBinom_le_mul_prod_largePrimeSet` and `4^n < n·C(2n, n)`. -/
lemma le_sum_log_largePrimeSet {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log n - (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * n)
        - ((2 * n / 3 : ℕ) : ℝ) * Real.log 4
      ≤ ∑ p ∈ largePrimeSet n (2 * n), Real.log p := by
  have h3 : 4 ^ n < n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)
      * ∏ p ∈ largePrimeSet n (2 * n), p) :=
    lt_of_lt_of_le (Nat.four_pow_lt_mul_centralBinom n hn)
      (Nat.mul_le_mul_left n (centralBinom_le_mul_prod_largePrimeSet (by omega)))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hP : ∀ p ∈ largePrimeSet n (2 * n), (p : ℝ) ≠ 0 := fun p hp => by
    exact_mod_cast (mem_largePrimeSet.1 hp).2.ne_zero
  have hP0 : (0 : ℝ) < ∏ p ∈ largePrimeSet n (2 * n), (p : ℝ) :=
    Finset.prod_pos fun p hp => by exact_mod_cast (mem_largePrimeSet.1 hp).2.pos
  have hA : (0 : ℝ) < (2 * (n : ℝ)) ^ Nat.sqrt (2 * n) := by positivity
  have hB : (0 : ℝ) < (4 : ℝ) ^ (2 * n / 3) := by positivity
  have h4 : (4 : ℝ) ^ n < (n : ℝ) * ((2 * (n : ℝ)) ^ Nat.sqrt (2 * n) * (4 : ℝ) ^ (2 * n / 3)
      * ∏ p ∈ largePrimeSet n (2 * n), (p : ℝ)) := by
    have h := (Nat.cast_lt (α := ℝ)).2 h3
    push_cast at h
    exact h
  have e : Real.log ((n : ℝ) * ((2 * (n : ℝ)) ^ Nat.sqrt (2 * n) * (4 : ℝ) ^ (2 * n / 3)
      * ∏ p ∈ largePrimeSet n (2 * n), (p : ℝ)))
      = Real.log n + ((Nat.sqrt (2 * n) : ℝ) * Real.log (2 * n)
        + ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 + ∑ p ∈ largePrimeSet n (2 * n), Real.log p) := by
    rw [Real.log_mul hn0.ne' (mul_pos (mul_pos hA hB) hP0).ne',
      Real.log_mul (mul_pos hA hB).ne' hP0.ne', Real.log_mul hA.ne' hB.ne', Real.log_pow,
      Real.log_pow, Real.log_prod hP]
  have hlog := Real.log_lt_log (by positivity) h4
  rw [e, Real.log_pow] at hlog
  linarith

/-- **The primes of `(x/2, x]`, elementary**: `∑_{x/2<p≤x} 1/p ≥ 0.23/log x` for `x ≥ 10^{16}`.
With `n = ⌊x/2⌋`, `RMF.le_sum_log_largePrimeSet` gives `θ(2n) - θ(n) ≥ (n/3)log 4 - (1 + √x)log x`;
`1/p ≥ log p/(x log x)` for `p ≤ x`, and `(log 4)/6 > 0.231`. -/
lemma le_sum_inv_largePrimeSet_half_small {x : ℝ} (hx : (10 : ℝ) ^ 16 ≤ x) :
    23 / (100 * Real.log x) ≤ ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹ := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hL : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le (by norm_num) hx)
  set n := ⌊x / 2⌋₊ with hn
  have hn_le : (n : ℝ) ≤ x / 2 := Nat.floor_le (by positivity)
  have hn_gt : x / 2 < n + 1 := Nat.lt_floor_add_one _
  have hn4 : 4 ≤ n := by
    have : (4 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2n : 2 * n ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hsub : largePrimeSet n (2 * n) ⊆ largePrimeSet n ⌊x⌋₊ := fun p hp => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := mem_largePrimeSet.1 hp
    exact mem_largePrimeSet.2 ⟨⟨h1, h2.trans h2n⟩, h3⟩
  -- each term: `1/p ≥ log p/(x log x)`
  have hterm : ∀ p ∈ largePrimeSet n (2 * n), Real.log p / (x * Real.log x) ≤ (p : ℝ)⁻¹ := by
    intro p hp
    obtain ⟨⟨-, hpx⟩, hprime⟩ := mem_largePrimeSet.1 hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpxR : (p : ℝ) ≤ x := by
      have : (p : ℝ) ≤ 2 * n := by exact_mod_cast hpx
      linarith
    have hlogp : Real.log p ≤ Real.log x := Real.log_le_log hp0 hpxR
    have hlogp0 : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    rw [div_le_iff₀ (mul_pos hx0 hL)]
    have h1 : (1 : ℝ) ≤ (p : ℝ)⁻¹ * x := by
      rw [inv_mul_eq_div, one_le_div hp0]
      exact hpxR
    nlinarith [mul_le_mul h1 hlogp hlogp0 (zero_le_one.trans h1)]
  -- the error terms
  have hθ := le_sum_log_largePrimeSet hn4
  have hlogn : Real.log n ≤ Real.log x := Real.log_le_log hn0 (by linarith)
  have hlog2n : Real.log (2 * n) ≤ Real.log x := Real.log_le_log (by positivity) (by linarith)
  have hlog2n0 : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have hsq : (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt x := by
    refine le_trans Real.nat_sqrt_le_real_sqrt (Real.sqrt_le_sqrt ?_)
    push_cast
    linarith
  have hdiv : ((2 * n / 3 : ℕ) : ℝ) ≤ 2 * n / 3 := by
    have h := (Nat.cast_div_le : ((2 * n / 3 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) / ((3 : ℕ) : ℝ))
    push_cast at h
    exact h
  have hl4 : (1.3862 : ℝ) ≤ Real.log 4 := by
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_gt_d9
    linarith
  -- `r = √√x`, with `x = r⁴` and `r ≥ 10⁴`
  set r := Real.sqrt (Real.sqrt x) with hr
  have hsx : Real.sqrt x = r ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg x)).symm
  have hxr : x = r ^ 4 := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, ← hsx, Real.sq_sqrt hx0.le]
  have hr4 : (10000 : ℝ) ≤ r := by
    have h8 : Real.sqrt ((10 : ℝ) ^ 16) = 10 ^ 8 := by
      rw [show (10 : ℝ) ^ 16 = (10 ^ 8) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    have h4 : Real.sqrt ((10 : ℝ) ^ 8) = 10000 := by
      rw [show (10 : ℝ) ^ 8 = 10000 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    have h1 : (10 : ℝ) ^ 8 ≤ Real.sqrt x := h8 ▸ Real.sqrt_le_sqrt hx
    rw [hr, ← h4]
    exact Real.sqrt_le_sqrt h1
  have hr0 : 0 < r := by linarith
  have hlogx : Real.log x ≤ 4 * r := by
    rw [hxr, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hr0
    push_cast
    linarith
  -- `0.23x ≤ θ(2n) - θ(n)`
  have hkey : 23 / 100 * x ≤ ∑ p ∈ largePrimeSet n (2 * n), Real.log p := by
    have hA : (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * n) ≤ Real.sqrt x * Real.log x :=
      mul_le_mul hsq hlog2n hlog2n0 (Real.sqrt_nonneg x)
    have hB : ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 ≤ 2 * n / 3 * Real.log 4 :=
      mul_le_mul_of_nonneg_right hdiv (by linarith)
    have hC : Real.sqrt x * Real.log x ≤ r ^ 2 * (4 * r) :=
      mul_le_mul hsx.le hlogx hL.le (by positivity)
    have hN : (n : ℝ) * 1.3862 ≤ n * Real.log 4 := mul_le_mul_of_nonneg_left hl4 hn0.le
    have hr3 : 10000 * r ^ 3 ≤ r ^ 4 := by
      have : 0 ≤ r ^ 3 := by positivity
      nlinarith
    have hr1 : 4 * r + 1 ≤ r ^ 3 := by nlinarith
    linarith
  calc 23 / (100 * Real.log x) = 23 / 100 * x / (x * Real.log x) := by
        field_simp
    _ ≤ (∑ p ∈ largePrimeSet n (2 * n), Real.log p) / (x * Real.log x) :=
        div_le_div_of_nonneg_right hkey (mul_pos hx0 hL).le
    _ = ∑ p ∈ largePrimeSet n (2 * n), Real.log p / (x * Real.log x) := Finset.sum_div _ _ _
    _ ≤ ∑ p ∈ largePrimeSet n (2 * n), (p : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ ≤ ∑ p ∈ largePrimeSet n ⌊x⌋₊, (p : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => inv_nonneg.2 (Nat.cast_nonneg _)

/-! ### The floor -/

/-- **The floor, from a lower bound on the prime sum**: for a Rademacher family, `x ≥ 4`,
`0 < q ≤ ½` and `0 ≤ c ≤ ∑_{x/2<p≤x} 1/p`, `2^{-(1-2q)}3^{-(1-q)}c^q ≤ E|S(x)|^{2q}`: Khintchine
(`RMF.khintchine_rough_weighted`) at `y = ⌊x/2⌋`, where `S(x/p) = 1`, as in
`RMF.le_integral_rpow_weightedRademacherSum_floor_explicit`. -/
theorem le_integral_rpow_weightedRademacherSum_floor_of_le_sum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q c : ℝ} (hx : 4 ≤ x) (hq0 : 0 < q) (hq12 : q ≤ 1 / 2)
    (hc : 0 ≤ c) (hsum : c ≤ ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹) :
    (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * c ^ q
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hx0 : (0 : ℝ) < x := by linarith
  -- Khintchine at `y = ⌊x/2⌋`
  have hxy : ⌊x⌋₊ < (⌊x / 2⌋₊ + 1) ^ 2 := by
    have hs : x / 2 < (⌊x / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hlt : x < ((⌊x / 2⌋₊ : ℝ) + 1) ^ 2 := by nlinarith
    have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
    have hcast : (⌊x⌋₊ : ℝ) < (((⌊x / 2⌋₊ + 1) ^ 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  have hkh := khintchine_rough_weighted hX (by linarith) hxy hq0 (by linarith)
  -- the prime sum is deterministic
  have hS1 : ∀ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, ∀ ω,
      weightedRademacherSum (fun ω => squarefreeExtension fun r => X r ω) (x / p) ω = 1 := by
    intro p hp ω
    obtain ⟨⟨hyp, hpx⟩, hprime⟩ := mem_largePrimeSet.1 hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpxR : (p : ℝ) ≤ x := le_trans (by exact_mod_cast hpx) (Nat.floor_le hx0.le)
    have hhalf : x / 2 < p := by
      have h1 : (⌊x / 2⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast hyp
      have h2 := Nat.lt_floor_add_one (x / 2)
      linarith
    refine weightedRademacherSum_eq_one_of_lt_two X ?_ ?_ ω
    · rw [le_div_iff₀ hp0]
      linarith
    · rw [div_lt_iff₀ hp0]
      linarith
  have hconst : ∀ ω, (∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹ * ‖weightedRademacherSum
      (fun ω => squarefreeExtension fun r => X r ω) (x / p) ω‖ ^ 2)
      = ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹ := fun ω =>
    Finset.sum_congr rfl fun p hp => by rw [hS1 p hp ω, norm_one, one_pow, mul_one]
  simp only [hconst, integral_const, probReal_univ, smul_eq_mul, one_mul] at hkh
  -- the constant, bounded below
  have hmono : c ^ q ≤ (∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹) ^ q :=
    Real.rpow_le_rpow hc hsum hq0.le
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 - q)) := Real.rpow_nonneg (by norm_num) _
  have h20 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 - 2 * q)) := Real.rpow_nonneg (by norm_num) _
  have h2 : (2 : ℝ) ^ (-(1 - 2 * q)) * 2 ^ (1 - 2 * q) = 1 := by
    rw [← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero]
  have p1 := le_trans (mul_le_mul_of_nonneg_left hmono h3) hkh
  have p2 := mul_le_mul_of_nonneg_left p1 h20
  rw [← mul_assoc ((2 : ℝ) ^ (-(1 - 2 * q))) ((2 : ℝ) ^ (1 - 2 * q)), h2, one_mul] at p2
  linarith

/-- **F, the floor for small `x`**: for a Rademacher family, `x ≥ 10^{16}` and `0 < q ≤ ½`,
`2^{-(1-2q)}3^{-(1-q)}(0.23/log x)^q ≤ E|S(x)|^{2q}`
(`RMF.le_sum_inv_largePrimeSet_half_small`). -/
theorem le_integral_rpow_weightedRademacherSum_floor_small {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : (10 : ℝ) ^ 16 ≤ x) (hq0 : 0 < q)
    (hq12 : q ≤ 1 / 2) :
    (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (23 / (100 * Real.log x)) ^ q
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ :=
  le_integral_rpow_weightedRademacherSum_floor_of_le_sum hX
    (le_trans (by norm_num) hx) hq0 hq12
    (div_nonneg (by norm_num) (mul_nonneg (by norm_num)
      (Real.log_nonneg (le_trans (by norm_num) hx))))
    (le_sum_inv_largePrimeSet_half_small hx)

end RMF
