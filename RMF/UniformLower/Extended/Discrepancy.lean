/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.Extended.Basics
import RMF.Analysis.ShellSum

/-!
# The extended sum's explicit lower bound: the smoothing discrepancy

On the primes of `(√x, x]` the weighted sum's step L7 bounds the mean smoothing discrepancy by
`2` (`RMF.integral_sum_discrepancy_le_sqrt_weighted`, from orthogonality); for the extended sum
over any primes up to `x` the bound is `40x` (`RMF.integral_sum_discrepancy_le_extended`).  Here
it is `2x` on the primes of `(√x, x]`.

## The sharp square-class count

By the square classes `E|∑_{a<n≤b} X^e(n)|² = ∑_{m squarefree} c_m²`,
`c_m = ⌊√(b/m)⌋ - ⌊√(a/m)⌋` (`RMF.integral_normSq_sum_Ioc_compMult`), and `∑ c_m = ⌊b⌋ - ⌊a⌋`.
The excess `∑ c_m(c_m - 1)` lives on `c_m ≥ 2`, which forces `m < M₀ = (b-a)²/(4a)`, and there
`c_m(c_m - 1) ≤ u² + u ≤ M₀/m + √(M₀/m)`, `u = √(b/m) - √(a/m)`.  Summed with `H_K ≤ 1 + log K`
and `∑_{m≤K} m^{-1/2} ≤ 2√K`:
`E|∑_{a<n≤b} X^e(n)|² ≤ (⌊b⌋ - ⌊a⌋) + max 0 (M₀(3 + log M₀))` for `0 < a ≤ b`
(`RMF.integral_normSq_sum_Ioc_compMult_le_sharp`).

## The discrepancy

On the window `(p, p(1 + 1/L)]` the count is at most `x/(pL) + 1` and `M₀ ≤ m = x/(4L²p)`
(`RMF.integral_discrepancy_le_extended_sharp`).  For `p > √x`, `log m ≤ (log x)/2`; with Mertens on
`(√x, x]` and Chebyshev, at `L = log x ≥ 1`,
`E[D] ≤ x((1/2 + log 4 + 9.003/L) + (3 + L/2)(L/2 + 9.003)/(4L²))`
(`RMF.integral_sum_discrepancy_le_sqrt_extended_of_exp_one_le`), at most `2x` from `L ≥ 206`
(`RMF.sqrt_discrepancy_extended_le_two`; the limit is `1/2 + log 4 + 1/16 ≈ 1.949`), stated from
`x ≥ e^{300}` (`RMF.integral_sum_discrepancy_le_sqrt_extended`).
-/

open MeasureTheory

namespace RMF

/-! ### The sharp square-class count -/

/-- `c_m ≥ 2` forces `m < (b-a)²/(4a)`, for `c_m = ⌊√(b/m)⌋ - ⌊√(a/m)⌋` and `0 < a ≤ b`: then
`√(b/m) - √(a/m) > 1`, and `(√(b/m) - √(a/m))² ≤ (b-a)²/(4am)`.  This sharpens
`RMF.lt_sub_of_two_le_floor_sqrt_sub`. -/
lemma lt_sq_sub_div_of_two_le_floor_sqrt_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {m : ℕ}
    (hm : 0 < m) (h : 2 ≤ ⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊) :
    (m : ℝ) < (b - a) ^ 2 / (4 * a) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hu : 0 < a / m := div_pos ha hm0
  have huw : a / m ≤ b / m := div_le_div_of_nonneg_right hab hm0.le
  have h1 : ⌊Real.sqrt (a / m)⌋₊ + 2 ≤ ⌊Real.sqrt (b / m)⌋₊ := by omega
  have hsa : Real.sqrt (a / m) < ⌊Real.sqrt (a / m)⌋₊ + 1 := Nat.lt_floor_add_one _
  have hsb : (⌊Real.sqrt (b / m)⌋₊ : ℝ) ≤ Real.sqrt (b / m) := Nat.floor_le (Real.sqrt_nonneg _)
  have h2 : 1 < Real.sqrt (b / m) - Real.sqrt (a / m) := by
    have h3 : ((⌊Real.sqrt (a / m)⌋₊ + 2 : ℕ) : ℝ) ≤ (⌊Real.sqrt (b / m)⌋₊ : ℝ) := by
      exact_mod_cast h1
    push_cast at h3
    linarith
  have hsq := sqrt_sub_sqrt_sq_le hu huw
  have heq : (b / m - a / m) ^ 2 / (4 * (a / m)) = (b - a) ^ 2 / (4 * a) / m := by
    field_simp
  rw [heq] at hsq
  have h4 : 1 < (Real.sqrt (b / m) - Real.sqrt (a / m)) ^ 2 := by nlinarith
  have h5 : 1 < (b - a) ^ 2 / (4 * a) / m := lt_of_lt_of_le h4 hsq
  rwa [lt_div_iff₀ hm0, one_mul] at h5

/-- `c_m(c_m - 1) ≤ M₀/m + √M₀/√m` for `c_m = ⌊√(b/m)⌋ - ⌊√(a/m)⌋`, `M₀ = (b-a)²/(4a)`,
`0 < a ≤ b` and `m > 0`: `c_m ≤ u + 1` with `u = √(b/m) - √(a/m)`, and `u² ≤ M₀/m`. -/
lemma floor_sqrt_sub_mul_sub_one_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {m : ℕ} (hm : 0 < m) :
    ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)
        * (((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) - 1)
      ≤ (b - a) ^ 2 / (4 * a) / m + Real.sqrt ((b - a) ^ 2 / (4 * a)) / Real.sqrt m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hu : 0 < a / m := div_pos ha hm0
  have huw : a / m ≤ b / m := div_le_div_of_nonneg_right hab hm0.le
  have hmono : ⌊Real.sqrt (a / m)⌋₊ ≤ ⌊Real.sqrt (b / m)⌋₊ :=
    Nat.floor_le_floor (Real.sqrt_le_sqrt huw)
  have hc : ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)
      ≤ (Real.sqrt (b / m) - Real.sqrt (a / m)) + 1 := by
    rw [Nat.cast_sub hmono]
    have h1 : (⌊Real.sqrt (b / m)⌋₊ : ℝ) ≤ Real.sqrt (b / m) := Nat.floor_le (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (a / m) < ⌊Real.sqrt (a / m)⌋₊ + 1 := Nat.lt_floor_add_one _
    linarith
  have hc0 : (0 : ℝ) ≤ ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hu0 : 0 ≤ Real.sqrt (b / m) - Real.sqrt (a / m) := sub_nonneg.2 (Real.sqrt_le_sqrt huw)
  have hsq := sqrt_sub_sqrt_sq_le hu huw
  have heq : (b / m - a / m) ^ 2 / (4 * (a / m)) = (b - a) ^ 2 / (4 * a) / m := by
    field_simp
  rw [heq] at hsq
  have hM0 : 0 ≤ (b - a) ^ 2 / (4 * a) := by positivity
  -- `u ≤ √(M₀/m) = √M₀/√m`
  have hu' : Real.sqrt (b / m) - Real.sqrt (a / m)
      ≤ Real.sqrt ((b - a) ^ 2 / (4 * a)) / Real.sqrt m := by
    rw [← Real.sqrt_div hM0, ← Real.sqrt_sq hu0]
    exact Real.sqrt_le_sqrt hsq
  -- `c(c - 1) ≤ (u + 1)u`
  have hcc : ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)
        * (((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) - 1)
      ≤ (Real.sqrt (b / m) - Real.sqrt (a / m)) ^ 2 + (Real.sqrt (b / m) - Real.sqrt (a / m)) := by
    rcases le_or_gt 1 ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) with h1 | h1
    · calc ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)
            * (((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) - 1)
          ≤ ((Real.sqrt (b / m) - Real.sqrt (a / m)) + 1)
            * (Real.sqrt (b / m) - Real.sqrt (a / m)) :=
            mul_le_mul hc (by linarith) (by linarith) (by linarith)
        _ = (Real.sqrt (b / m) - Real.sqrt (a / m)) ^ 2
            + (Real.sqrt (b / m) - Real.sqrt (a / m)) := by ring
    · have hneg : ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)
          * (((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc0 (by linarith)
      have hpos : 0 ≤ (Real.sqrt (b / m) - Real.sqrt (a / m)) ^ 2
          + (Real.sqrt (b / m) - Real.sqrt (a / m)) := by positivity
      linarith
  linarith

/-- **The sharp count.**  For `0 < a ≤ b`, with `M₀ = (b-a)²/(4a)`,
`∑_{m≤b squarefree} (⌊√(b/m)⌋ - ⌊√(a/m)⌋)² ≤ (⌊b⌋ - ⌊a⌋) + max 0 (M₀(3 + log M₀))`.  It sharpens
`RMF.sum_sq_floor_sqrt_sub_le`. -/
lemma sum_sq_floor_sqrt_sub_le_sharp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∑ m ∈ Finset.Icc 1 ⌊b⌋₊, (((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) ^ 2
        * (if Squarefree m then 1 else 0))
      ≤ ((⌊b⌋₊ : ℝ) - ⌊a⌋₊)
        + max 0 ((b - a) ^ 2 / (4 * a) * (3 + Real.log ((b - a) ^ 2 / (4 * a)))) := by
  set M : ℝ := (b - a) ^ 2 / (4 * a) with hMdef
  have hM0 : 0 ≤ M := by positivity
  set K : ℕ := ⌊M⌋₊ with hKdef
  -- pointwise: the excess lives on `m ≤ K`
  have hpt : ∀ m ∈ Finset.Icc 1 ⌊b⌋₊,
      ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) ^ 2
          * (if Squarefree m then 1 else 0)
        ≤ ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)
            * (if Squarefree m then 1 else 0)
          + (if m ≤ K then M / m + Real.sqrt M / Real.sqrt m else 0) := by
    intro m hm
    have hm1 : 0 < m := (Finset.mem_Icc.1 hm).1
    have hind : (0 : ℝ) ≤ (if Squarefree m then 1 else 0) := by split_ifs <;> norm_num
    have hind1 : (if Squarefree m then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    have hc0 : (0 : ℝ) ≤ ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    have hextra : (0 : ℝ) ≤ (if m ≤ K then M / m + Real.sqrt M / Real.sqrt m else 0) := by
      split_ifs <;> positivity
    rcases Nat.lt_or_ge (⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊) 2 with hc | hc
    · have hc1 : ⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ ≤ 1 := by omega
      have hcr : ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) ≤ 1 := by
        exact_mod_cast hc1
      have hsq : ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) ^ 2
          ≤ ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) := by nlinarith
      have := mul_le_mul_of_nonneg_right hsq hind
      linarith
    · have hlt := lt_sq_sub_div_of_two_le_floor_sqrt_sub ha hab hm1 hc
      rw [← hMdef] at hlt
      have hmK : m ≤ K := Nat.le_floor hlt.le
      rw [if_pos hmK]
      have hb := floor_sqrt_sub_mul_sub_one_le ha hab hm1
      rw [← hMdef] at hb
      have hc2 : (2 : ℝ) ≤ ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hc
      have hcc0 : 0 ≤ ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)
          * (((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) - 1) :=
        mul_nonneg hc0 (by linarith)
      have hdrop := mul_le_of_le_one_right hcc0 hind1
      have e : ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) ^ 2
            * (if Squarefree m then 1 else 0)
          = ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)
              * (if Squarefree m then 1 else 0)
            + ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)
              * (((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) - 1)
              * (if Squarefree m then 1 else 0) := by ring
      rw [e]
      linarith
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_add_distrib, sum_floor_sqrt_sub_squarefree_eq ha.le hab]
  -- the excess lives on `m ≤ K`
  have hsub : ∑ m ∈ Finset.Icc 1 ⌊b⌋₊,
      (if m ≤ K then M / m + Real.sqrt M / Real.sqrt m else 0)
      ≤ ∑ m ∈ Finset.Icc 1 K, (M / m + Real.sqrt M / Real.sqrt m) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => by positivity
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    exact Finset.mem_Icc.2 ⟨hm.1.1, hm.2⟩
  have hbound : ∑ m ∈ Finset.Icc 1 K, (M / m + Real.sqrt M / Real.sqrt m)
      ≤ max 0 (M * (3 + Real.log M)) := by
    rcases Nat.eq_zero_or_pos K with hK0 | hK0
    · rw [hK0]
      simp
    · have hM1 : 1 ≤ M := by
        have : 1 ≤ ⌊M⌋₊ := hK0
        exact (Nat.one_le_floor_iff M).1 this
      have hKM : (K : ℝ) ≤ M := Nat.floor_le hM0
      have hK0' : (0 : ℝ) < K := by exact_mod_cast hK0
      rw [Finset.sum_add_distrib]
      have h1 : ∑ m ∈ Finset.Icc 1 K, M / (m : ℝ) = M * ∑ m ∈ Finset.Icc 1 K, ((m : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => div_eq_mul_inv _ _
      have h2 : ∑ m ∈ Finset.Icc 1 K, Real.sqrt M / Real.sqrt m
          = Real.sqrt M * ∑ m ∈ Finset.Icc 1 K, 1 / Real.sqrt m := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by rw [mul_one_div]
      have hH : ∑ m ∈ Finset.Icc 1 K, ((m : ℝ))⁻¹ ≤ 1 + Real.log M := by
        have h := sum_inv_Icc_le_one_add_log K
        have hlog : Real.log (K : ℝ) ≤ Real.log M := Real.log_le_log hK0' hKM
        linarith
      have hR : ∑ m ∈ Finset.Icc 1 K, 1 / Real.sqrt m ≤ 2 * Real.sqrt M := by
        have h := sum_one_div_sqrt_le K
        have hs : Real.sqrt K ≤ Real.sqrt M := Real.sqrt_le_sqrt hKM
        linarith
      have hsM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM0
      rw [h1, h2]
      refine le_trans ?_ (le_max_right _ _)
      have p1 := mul_le_mul_of_nonneg_left hH hM0
      have p2 := mul_le_mul_of_nonneg_left hR (Real.sqrt_nonneg M)
      nlinarith
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The sharp square-class count.**  For Rademacher `X` and `0 < a ≤ b`, with
`M₀ = (b-a)²/(4a)`, `E|∑_{a<n≤b} X^e(n)|² ≤ (⌊b⌋ - ⌊a⌋) + max 0 (M₀(3 + log M₀))`: the exact mean
square of the square classes (`RMF.integral_normSq_sum_Ioc_compMult`) and
`RMF.sum_sq_floor_sqrt_sub_le_sharp`. -/
theorem integral_normSq_sum_Ioc_compMult_le_sharp {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, compMultExtension (fun p => X p ω) n‖ ^ 2 ∂μ)
      ≤ ((⌊b⌋₊ : ℝ) - ⌊a⌋₊)
        + max 0 ((b - a) ^ 2 / (4 * a) * (3 + Real.log ((b - a) ^ 2 / (4 * a)))) := by
  rw [integral_normSq_sum_Ioc_compMult hX ha.le hab]
  exact sum_sq_floor_sqrt_sub_le_sharp ha hab

/-! ### The discrepancy, one prime at a time -/

/-- `M ↦ max 0 (M(3 + log M))` is monotone on `[0, ∞)`. -/
lemma max_zero_mul_three_add_log_mono {M M' : ℝ} (hM : 0 ≤ M) (hMM' : M ≤ M') :
    max 0 (M * (3 + Real.log M)) ≤ max 0 (M' * (3 + Real.log M')) := by
  rcases le_or_gt (M * (3 + Real.log M)) 0 with h | h
  · rw [max_eq_left h]
    exact le_max_left _ _
  · have hMpos : 0 < M := by
      rcases hM.lt_or_eq with h' | h'
      · exact h'
      · rw [← h', zero_mul] at h
        exact absurd h (lt_irrefl 0)
    have h3 : 0 < 3 + Real.log M := by
      by_contra hc
      have hc' : 3 + Real.log M ≤ 0 := not_lt.1 hc
      have := mul_nonpos_of_nonneg_of_nonpos hMpos.le hc'
      linarith
    have hlog : Real.log M ≤ Real.log M' := Real.log_le_log hMpos hMM'
    rw [max_eq_right h.le]
    refine le_trans ?_ (le_max_right _ _)
    exact mul_le_mul hMM' (by linarith) h3.le (by linarith)

/-- `max 0 (M(3 + log M)) ≤ M(3 + (log x)/2)` for `0 ≤ M ≤ √x`, `x ≥ 1`. -/
lemma max_zero_mul_three_add_log_le_of_le_sqrt {M x : ℝ} (hM : 0 ≤ M) (hx : 1 ≤ x)
    (hMx : M ≤ Real.sqrt x) :
    max 0 (M * (3 + Real.log M)) ≤ M * (3 + Real.log x / 2) := by
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  refine max_le (by positivity) ?_
  rcases hM.lt_or_eq with hpos | h0
  · have hlog : Real.log M ≤ Real.log x / 2 := by
      rw [← Real.log_sqrt (by linarith)]
      exact Real.log_le_log hpos hMx
    exact mul_le_mul_of_nonneg_left (by linarith) hM
  · rw [← h0]
    simp

/-- On the window `p ≤ t ≤ p(1 + 1/L)`, `M₀ = (x/p - x/t)²/(4x/t) ≤ x/(4L²p)`. -/
lemma window_sq_sub_div_le {x L p t : ℝ} (hx : 0 < x) (hL : 0 < L) (hp : 0 < p) (hpt : p ≤ t)
    (ht : t ≤ p * (1 + 1 / L)) :
    (x / p - x / t) ^ 2 / (4 * (x / t)) ≤ x / (4 * L ^ 2 * p) := by
  have ht0 : 0 < t := lt_of_lt_of_le hp hpt
  have htp : t - p ≤ p / L := by
    have : p * (1 + 1 / L) = p + p / L := by ring
    linarith
  have heq : (x / p - x / t) ^ 2 / (4 * (x / t)) = x * (t - p) ^ 2 / (4 * p ^ 2 * t) := by
    field_simp
  rw [heq]
  have h1 : (t - p) ^ 2 ≤ (p / L) ^ 2 := pow_le_pow_left₀ (by linarith) htp 2
  calc x * (t - p) ^ 2 / (4 * p ^ 2 * t) ≤ x * (p / L) ^ 2 / (4 * p ^ 2 * t) := by gcongr
    _ = x / (4 * L ^ 2 * t) := by
        field_simp
    _ ≤ x / (4 * L ^ 2 * p) := by gcongr

/-- **The smoothing error of the extended sum, per prime, sharp.**  For `x, L, p > 0`, the expected
discrepancy over the window `(p, p(1+1/L)]` is at most `x/(pL) + 1 + max 0 (m(3 + log m))`,
`m = x/(4L²p)`: the sharp count (`RMF.integral_normSq_sum_Ioc_compMult_le_sharp`) with
`M₀ ≤ m` on the window.  It sharpens `RMF.integral_discrepancy_le_extended`. -/
theorem integral_discrepancy_le_extended_sharp {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {x L p : ℝ} (hx : 0 < x)
    (hL : 0 < L) (hp : 0 < p) :
    (∫ ω, L / p * (∫ t in Set.Ioc p (p * (1 + 1 / L)),
        discrepancy (fun ω => compMultExtension fun q => X q ω) x p ω t) ∂μ)
      ≤ x / (p * L) + 1
        + max 0 (x / (4 * L ^ 2 * p) * (3 + Real.log (x / (4 * L ^ 2 * p)))) := by
  set g : Ω → ArithmeticFunction ℂ := fun ω => compMultExtension fun q => X q ω with hgdef
  have hmeas : ∀ n : ℕ, Measurable fun ω => g ω n := fun n => hX.measurable_compMultExtension n
  have hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖g ω n‖ ≤ 1 := fun n =>
    hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n
  set B : ℝ := x / (p * L) + 1
    + max 0 (x / (4 * L ^ 2 * p) * (3 + Real.log (x / (4 * L ^ 2 * p)))) with hBdef
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc p (p * (1 + 1 / L)))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hInt := integrable_discrepancy_of (X := L) hmeas hbd hx.le hp
  rw [integral_const_mul, integral_integral_swap hInt]
  have hbound : ∀ t ∈ Set.Ioc p (p * (1 + 1 / L)), (∫ ω, discrepancy g x p ω t ∂μ) ≤ B := by
    intro t ht
    have hpt : p ≤ t := ht.1.le
    have ht0 : 0 < t := lt_of_lt_of_le hp hpt
    have hdiv : x / t ≤ x / p := by gcongr
    have hle : (∫ ω, discrepancy g x p ω t ∂μ)
        ≤ ∫ ω, ‖randomSum g (x / p) ω - randomSum g (x / t) ω‖ ^ 2 ∂μ :=
      integral_mono_ae (integrable_discrepancy_slice_of hmeas hbd hp hpt hx.le)
        (integrable_normSq_randomSum_sub_of hmeas hbd hdiv)
        (Filter.Eventually.of_forall fun ω => discrepancy_le_block g x p ω t)
    have hblock : (∫ ω, ‖randomSum g (x / p) ω - randomSum g (x / t) ω‖ ^ 2 ∂μ)
        = ∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x / t⌋₊ ⌊x / p⌋₊, compMultExtension (fun q => X q ω) n‖ ^ 2
          ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        simp only
        rw [randomSum_sub_eq _ hdiv ω])
    have hwin := integral_normSq_sum_Ioc_compMult_le_sharp hX (div_pos hx ht0) hdiv
    have hcount := floor_sub_floor_le hx.le hL hp hpt ht.2
    have hM := window_sq_sub_div_le hx hL hp hpt ht.2
    have hmono := max_zero_mul_three_add_log_mono (by positivity) hM
    rw [hblock] at hle
    rw [hBdef]
    linarith
  have hconst : L / p * ∫ _t in Set.Ioc p (p * (1 + 1 / L)), B = B :=
    setIntegral_const_window hp hL
  rw [← hconst]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact setIntegral_mono_on hInt.integral_prod_right (integrableOn_const (by simp))
    measurableSet_Ioc hbound

/-! ### The discrepancy, summed over the primes of `(√x, x]` -/

/-- **Step L7 for the extended sum, on the primes of `(√x, x]`, in closed form.**  For `x ≥ e` and
any set of primes of `(√x, x]`, at `L = log x` the expected total discrepancy is at most
`x((1/2 + log 4 + 9.003/L) + (3 + L/2)(L/2 + 9.003)/(4L²))`:
`RMF.integral_discrepancy_le_extended_sharp` per prime, with `log m ≤ L/2` (`p > √x`),
`RMF.sum_log_div_largePrimeSet_sqrt_le` and `θ(x) ≤ x log 4`. -/
theorem integral_sum_discrepancy_le_sqrt_extended_of_exp_one_le {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {x : ℝ}
    (hx : Real.exp 1 ≤ x) {S : Finset ℕ} (hS : S ⊆ largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊) :
    (∫ ω, ∑ p ∈ S, Real.log p * (Real.log x / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
        discrepancy (fun ω => compMultExtension fun q => X q ω) x p ω t) ∂μ)
      ≤ x * ((1 / 2 + Real.log 4 + 9.003 / Real.log x)
        + (3 + Real.log x / 2) * (Real.log x / 2 + 9.003) / (4 * Real.log x ^ 2)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact hx
  have hSp : ∀ p ∈ S, Nat.Prime p := fun p hp => (mem_largePrimeSet.1 (hS hp)).2
  have hpos : ∀ p ∈ S, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hSp p hp).pos
  rw [integral_finsetSum]
  swap
  · intro p hp
    exact ((integrable_discrepancy_of (X := Real.log x)
      (fun n => hX.measurable_compMultExtension n)
      (fun n => hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n) hx0.le
      (hpos p hp)).integral_prod_left.const_mul _).const_mul _
  set L := Real.log x with hLdef
  have hL0 : (0 : ℝ) < L := by linarith
  set A : ℝ := x / L + x * (3 + L / 2) / (4 * L ^ 2) with hAdef
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hper : ∀ p ∈ S, (∫ ω, Real.log p * (L / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / L)),
        discrepancy (fun ω => compMultExtension fun q => X q ω) x p ω t) ∂μ)
      ≤ A * (Real.log p / p) + Real.log p := by
    intro p hp
    have hp0 := hpos p hp
    obtain ⟨⟨hyp, -⟩, -⟩ := mem_largePrimeSet.1 (hS hp)
    have hsp : Real.sqrt x < p := (Nat.floor_lt (Real.sqrt_nonneg x)).1 hyp
    rw [integral_const_mul]
    have h := integral_discrepancy_le_extended_sharp hX hx0 hL0 hp0
    -- `m = x/(4L²p) ≤ √x`, so `log m ≤ L/2`
    have hm0 : 0 ≤ x / (4 * L ^ 2 * p) := by positivity
    have hmx : x / (4 * L ^ 2 * p) ≤ Real.sqrt x := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : Real.sqrt x * Real.sqrt x ≤ Real.sqrt x * p :=
        mul_le_mul_of_nonneg_left hsp.le hs0.le
      have h2 : (1 : ℝ) ≤ 4 * L ^ 2 := by nlinarith
      have h3 : Real.sqrt x * p ≤ Real.sqrt x * p * (4 * L ^ 2) :=
        le_mul_of_one_le_right (by positivity) h2
      have hxs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
      nlinarith
    have hmax := max_zero_mul_three_add_log_le_of_le_sqrt hm0 hx1 hmx
    have hlp : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
    have h2 : (∫ ω, L / p * (∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / L)),
          discrepancy (fun ω => compMultExtension fun q => X q ω) x p ω t) ∂μ)
        ≤ x / (p * L) + 1 + x / (4 * L ^ 2 * p) * (3 + L / 2) := by
      rw [← hLdef] at hmax
      linarith
    calc Real.log p * (∫ ω, L / p * (∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / L)),
          discrepancy (fun ω => compMultExtension fun q => X q ω) x p ω t) ∂μ)
        ≤ Real.log p * (x / (p * L) + 1 + x / (4 * L ^ 2 * p) * (3 + L / 2)) :=
          mul_le_mul_of_nonneg_left h2 hlp
      _ = A * (Real.log p / p) + Real.log p := by
          rw [hAdef]
          field_simp
          ring
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hS1 : ∑ p ∈ S, Real.log p / p ≤ L / 2 + 9.003 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hS fun p _ _ => log_div_natCast_nonneg p)
      (sum_log_div_largePrimeSet_sqrt_le hx1)
  have hsub : S ⊆ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime} := fun p hp => by
    obtain ⟨⟨-, hpx⟩, hprime⟩ := mem_largePrimeSet.1 (hS hp)
    exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hprime.pos, hpx⟩, hprime⟩
  have hS2 : ∑ p ∈ S, Real.log p ≤ Real.log 4 * x :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
      Real.log_natCast_nonneg p) (sum_log_prime_le hx0.le)
  have hA0 : 0 ≤ A := by positivity
  have hS1' := mul_le_mul_of_nonneg_left hS1 hA0
  have e : A * (L / 2 + 9.003) + Real.log 4 * x
      = x * ((1 / 2 + Real.log 4 + 9.003 / L) + (3 + L / 2) * (L / 2 + 9.003) / (4 * L ^ 2)) := by
    rw [hAdef]
    field_simp
    ring
  linarith

/-- `(1/2 + log 4 + 9.003/L) + (3 + L/2)(L/2 + 9.003)/(4L²) ≤ 2` for `L ≥ 206` (`≈ 1.99994` at
`L = 206`; the limit is `1/2 + log 4 + 1/16 ≈ 1.949`). -/
lemma sqrt_discrepancy_extended_le_two {L : ℝ} (hL : 206 ≤ L) :
    (1 / 2 + Real.log 4 + 9.003 / L) + (3 + L / 2) * (L / 2 + 9.003) / (4 * L ^ 2) ≤ 2 := by
  have hL0 : 0 < L := by linarith
  have hl4 : Real.log 4 < 1.3862944 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
    linarith [Real.log_two_lt_d9]
  have e : (3 + L / 2) * (L / 2 + 9.003) / (4 * L ^ 2)
      = 1 / 16 + 1.500375 / L + 6.75225 / L ^ 2 := by
    field_simp
    ring
  have h1 : 9.003 / L ≤ 9.003 / 206 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have h2 : 1.500375 / L ≤ 1.500375 / 206 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have h3 : 6.75225 / L ^ 2 ≤ 6.75225 / 206 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hL 2)
  have hnum : (1 / 2 + 1.3862944 + 9.003 / 206) + (1 / 16 + 1.500375 / 206 + 6.75225 / 206 ^ 2)
      ≤ (2 : ℝ) := by norm_num
  rw [e]
  linarith

/-- **Step L7 for the extended sum, on the primes of `(√x, x]`: `E[D] ≤ 2x` for `x ≥ e^{300}`.**
The twin of `RMF.integral_sum_discrepancy_le_sqrt_weighted` (`E[D] ≤ 2` for the weighted sum),
through `RMF.integral_sum_discrepancy_le_sqrt_extended_of_exp_one_le`, whose bound is at most `2x`
already from `log x ≥ 206` (`RMF.sqrt_discrepancy_extended_le_two`). -/
theorem integral_sum_discrepancy_le_sqrt_extended {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : Real.exp 300 ≤ x)
    {S : Finset ℕ} (hS : S ⊆ largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊) :
    (∫ ω, ∑ p ∈ S, Real.log p * (Real.log x / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
        discrepancy (fun ω => compMultExtension fun q => X q ω) x p ω t) ∂μ) ≤ 2 * x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 300 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hxe : Real.exp 1 ≤ x := le_trans (Real.exp_le_exp.2 (by norm_num)) hx
  have h := integral_sum_discrepancy_le_sqrt_extended_of_exp_one_le hX hxe hS
  have h2 := sqrt_discrepancy_extended_le_two (by linarith : (206 : ℝ) ≤ Real.log x)
  calc _ ≤ _ := h
    _ ≤ x * 2 := mul_le_mul_of_nonneg_left h2 hx0.le
    _ = 2 * x := by ring

end RMF
