/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.CosinePrimeSum
import RMF.NumberTheory.StrongBlockCosine
import RMF.NumberTheory.MertensUniform
import RMF.Reduction.RademacherLower

/-!
# The extended Euler product against the Rademacher one

The Euler-product ratio in the proof of Proposition 4.3 of the paper.  For Rademacher `X` the
extended Euler product
`F^e(s) = ∏_{p<N}(1 - X(p)p^{-s})⁻¹` and the Rademacher one `F(s) = ∏_{p<N}(1 + X(p)p^{-s})`
differ by a deterministic factor, because `X(p)² = 1`:

`|F^e(s)|² = |F(s)|² · ∏_{p<N}|1 - (p^{-s})²|^{-2}`

(`RMF.ae_normSq_randomEulerProduct_compMult_eq`).

On the line `s = ½ + σ + it` the factor lies between `exp(2S - 1)` and `exp(2S + 5)`, with
`S = ∑_{p<N} cos(2t log p)/p^{1+2σ}`.  The cosine sums with the weight `p^{-2σ}` inherit the
bounds of the unweighted ones by summation by parts, for every `σ ≥ 0`.
-/

open MeasureTheory

namespace RMF

/-! ### Summation by parts against decreasing weights -/

/-- **Summation by parts from `0`.**  If `C(0) = 0` and `C(k+1) = C(k) + c(k)`, then
`∑_{i<n} c(i)w(i) = C(n)w(n) + ∑_{k<n} C(k+1)(w(k) - w(k+1))`. -/
lemma sum_range_mul_eq_of_partial {c w C : ℕ → ℝ} (hC0 : C 0 = 0)
    (hC : ∀ k, C (k + 1) = C k + c k) (n : ℕ) :
    ∑ i ∈ Finset.range n, c i * w i
      = C n * w n + ∑ k ∈ Finset.range n, C (k + 1) * (w k - w (k + 1)) := by
  induction n with
  | zero => simp [hC0]
  | succ n ih =>
    rw [Finset.sum_range_succ (fun i => c i * w i) n, ih,
      Finset.sum_range_succ (fun k => C (k + 1) * (w k - w (k + 1))) n, hC n]
    ring

/-- **Summation by parts, from above.**  If `w` decreases on `[0, n]` with `w(n) ≥ 0` and every
partial sum `C(k)`, `k ≤ n`, is at most `U`, then `∑_{i<n} c(i)w(i) ≤ U·w(0)`. -/
lemma sum_range_mul_le_of_partial {c w C : ℕ → ℝ} (hC0 : C 0 = 0)
    (hC : ∀ k, C (k + 1) = C k + c k) {n : ℕ} (hw : ∀ k < n, w (k + 1) ≤ w k) (hwn : 0 ≤ w n)
    {U : ℝ} (hU : ∀ k ≤ n, C k ≤ U) :
    ∑ i ∈ Finset.range n, c i * w i ≤ U * w 0 := by
  rw [sum_range_mul_eq_of_partial hC0 hC n]
  have h1 : C n * w n ≤ U * w n := mul_le_mul_of_nonneg_right (hU n le_rfl) hwn
  have h2 : ∑ k ∈ Finset.range n, C (k + 1) * (w k - w (k + 1))
      ≤ ∑ k ∈ Finset.range n, U * (w k - w (k + 1)) :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right
      (hU (k + 1) (Finset.mem_range.1 hk)) (sub_nonneg.2 (hw k (Finset.mem_range.1 hk)))
  rw [← Finset.mul_sum, Finset.sum_range_sub', mul_sub] at h2
  linarith

/-- **Summation by parts, from below.**  The mirror of `RMF.sum_range_mul_le_of_partial`. -/
lemma le_sum_range_mul_of_partial {c w C : ℕ → ℝ} (hC0 : C 0 = 0)
    (hC : ∀ k, C (k + 1) = C k + c k) {n : ℕ} (hw : ∀ k < n, w (k + 1) ≤ w k) (hwn : 0 ≤ w n)
    {L : ℝ} (hL : ∀ k ≤ n, L ≤ C k) :
    L * w 0 ≤ ∑ i ∈ Finset.range n, c i * w i := by
  rw [sum_range_mul_eq_of_partial hC0 hC n]
  have h1 : L * w n ≤ C n * w n := mul_le_mul_of_nonneg_right (hL n le_rfl) hwn
  have h2 : ∑ k ∈ Finset.range n, L * (w k - w (k + 1))
      ≤ ∑ k ∈ Finset.range n, C (k + 1) * (w k - w (k + 1)) :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right
      (hL (k + 1) (Finset.mem_range.1 hk)) (sub_nonneg.2 (hw k (Finset.mem_range.1 hk)))
  rw [← Finset.mul_sum, Finset.sum_range_sub', mul_sub] at h2
  linarith

/-! ### The weight `p^{-2σ}` -/

/-- A sum over the primes below `N` as a sum over `range N`. -/
lemma sum_primesBelow_eq_sum_range (N : ℕ) (g : ℕ → ℝ) :
    ∑ p ∈ Nat.primesBelow N, g p = ∑ i ∈ Finset.range N, if i.Prime then g i else 0 := by
  rw [Nat.primesBelow, Finset.sum_filter]

/-- The data of the summation by parts for a weighted prime sum: coefficients `g(p)` at primes,
weights `max(i,1)^{-2σ}`, which decrease from `1` for `σ ≥ 0`. -/
lemma sum_primesBelow_div_rpow_eq (N : ℕ) (g : ℕ → ℝ) (σ : ℝ) :
    ∑ p ∈ Nat.primesBelow N, g p / (p : ℝ) ^ (1 + 2 * σ)
      = ∑ i ∈ Finset.range N, (if i.Prime then g i / i else 0)
          * ((max i 1 : ℕ) : ℝ) ^ (-(2 * σ)) := by
  rw [sum_primesBelow_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · have hi0 : (0 : ℝ) < i := by exact_mod_cast hi.pos
    rw [max_eq_left hi.one_lt.le, Real.rpow_add hi0, Real.rpow_one, Real.rpow_neg hi0.le]
    ring
  · rw [zero_mul]

lemma max_one_rpow_neg_antitone {σ : ℝ} (hσ : 0 ≤ σ) (k : ℕ) :
    ((max (k + 1) 1 : ℕ) : ℝ) ^ (-(2 * σ)) ≤ ((max k 1 : ℕ) : ℝ) ^ (-(2 * σ)) := by
  have h0 : (0 : ℝ) < ((max k 1 : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.one_pos (le_max_right k 1)
  exact Real.rpow_le_rpow_of_nonpos h0
    (by exact_mod_cast max_le_max (Nat.le_succ k) le_rfl) (by linarith)

/-- **The weight `p^{-2σ}` keeps an upper bound on the partial sums.**  For `σ ≥ 0`, if
`∑_{p<k} g(p)/p ≤ U` for every `k ≤ N`, then `∑_{p<N} g(p)/p^{1+2σ} ≤ U`. -/
lemma sum_primesBelow_div_rpow_le {g : ℕ → ℝ} {σ U : ℝ} (hσ : 0 ≤ σ) {N : ℕ}
    (hU : ∀ k ≤ N, ∑ p ∈ Nat.primesBelow k, g p / p ≤ U) :
    ∑ p ∈ Nat.primesBelow N, g p / (p : ℝ) ^ (1 + 2 * σ) ≤ U := by
  rw [sum_primesBelow_div_rpow_eq]
  have h := sum_range_mul_le_of_partial (n := N)
    (c := fun i => if i.Prime then g i / i else 0)
    (w := fun i => ((max i 1 : ℕ) : ℝ) ^ (-(2 * σ)))
    (C := fun k => ∑ i ∈ Finset.range k, if i.Prime then g i / i else 0)
    (Finset.sum_range_zero _) (fun k => Finset.sum_range_succ _ k)
    (fun k _ => max_one_rpow_neg_antitone hσ k) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (U := U) (fun k hk => by
      have := hU k hk
      rwa [sum_primesBelow_eq_sum_range] at this)
  simpa using h

/-- **The weight `p^{-2σ}` keeps a lower bound on the partial sums.** -/
lemma le_sum_primesBelow_div_rpow {g : ℕ → ℝ} {σ L : ℝ} (hσ : 0 ≤ σ) {N : ℕ}
    (hL : ∀ k ≤ N, L ≤ ∑ p ∈ Nat.primesBelow k, g p / p) :
    L ≤ ∑ p ∈ Nat.primesBelow N, g p / (p : ℝ) ^ (1 + 2 * σ) := by
  rw [sum_primesBelow_div_rpow_eq]
  have h := le_sum_range_mul_of_partial (n := N)
    (c := fun i => if i.Prime then g i / i else 0)
    (w := fun i => ((max i 1 : ℕ) : ℝ) ^ (-(2 * σ)))
    (C := fun k => ∑ i ∈ Finset.range k, if i.Prime then g i / i else 0)
    (Finset.sum_range_zero _) (fun k => Finset.sum_range_succ _ k)
    (fun k _ => max_one_rpow_neg_antitone hσ k) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (L := L) (fun k hk => by
      have := hL k hk
      rwa [sum_primesBelow_eq_sum_range] at this)
  simpa using h

/-! ### The cosine prime sums below height `1` -/

lemma one_le_min_log_div_log_two {τ y : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hy : 2 ≤ y) :
    1 ≤ min (Real.log y) (1 / τ) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2, one_mul]
  exact le_min (Real.log_le_log (by norm_num) hy)
    (le_trans (by linarith [Real.log_two_lt_d9]) ((one_le_div hτ).2 hτ1))

lemma log_min_log_div_log_two_le {τ y z : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hy : 2 ≤ y)
    (hyz : y ≤ z) :
    Real.log (min (Real.log y) (1 / τ) / Real.log 2)
      ≤ Real.log (min (Real.log z) (1 / τ) / Real.log 2) :=
  Real.log_le_log (by linarith [one_le_min_log_div_log_two hτ hτ1 hy])
    (div_le_div_of_nonneg_right (min_le_min (Real.log_le_log (by linarith) hyz) le_rfl)
      (Real.log_pos (by norm_num)).le)

/-- The unweighted cosine prime sums over `p < k`, for `0 < τ ≤ 1`: at least `-B`, and at most
`log(min{log k, 1/τ}/log 2) + B` once `k ≥ 2` (`RMF.exists_abs_cos_prime_sum_sub_log_min_le`). -/
lemma sum_primesBelow_cos_div_bounds {B : ℝ}
    (H : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ y : ℝ, 2 ≤ y →
      |∑ p ∈ Finset.Icc 0 ⌊y⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p
        - Real.log (min (Real.log y) (1 / τ) / Real.log 2)| ≤ B)
    (hB : 0 ≤ B) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (k : ℕ) :
    -B ≤ ∑ p ∈ Nat.primesBelow k, Real.cos (τ * Real.log p) / p ∧
      (2 ≤ k → ∑ p ∈ Nat.primesBelow k, Real.cos (τ * Real.log p) / p
        ≤ Real.log (min (Real.log k) (1 / τ) / Real.log 2) + B) := by
  have hmin : ∀ y : ℝ, 2 ≤ y → 0 ≤ Real.log (min (Real.log y) (1 / τ) / Real.log 2) :=
    fun y hy => Real.log_nonneg (one_le_min_log_div_log_two hτ hτ1 hy)
  rcases le_or_gt k 2 with hk | hk
  · rw [primesBelow_eq_empty hk, Finset.sum_empty]
    exact ⟨by linarith, fun hk2 => by linarith [hmin k (by exact_mod_cast hk2)]⟩
  · have hk0 : k ≠ 0 := by omega
    have hset : Nat.primesBelow k
        = {p ∈ Finset.Icc 0 ⌊((k - 1 : ℕ) : ℝ)⌋₊ | Nat.Prime p} := by
      rw [Nat.floor_natCast, Nat.primesBelow, Nat.range_eq_Icc_zero_sub_one k hk0]
    have hy : (2 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
      have : 2 ≤ k - 1 := by omega
      exact_mod_cast this
    have h := H τ hτ hτ1 _ hy
    rw [← hset] at h
    obtain ⟨h1, h2⟩ := abs_le.1 h
    refine ⟨by linarith [hmin _ hy], fun _ => ?_⟩
    have hmono := log_min_log_div_log_two_le hτ hτ1 hy
      (by exact_mod_cast Nat.sub_le k 1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ))
    linarith

/-- **The weighted cosine prime sum is bounded below, below height `1`.**  There is an absolute
`B` with `∑_{p<N} cos(τ log p)/p^{1+2σ} ≥ -B` for all `0 < τ ≤ 1`, `σ ≥ 0` and `N`. -/
theorem exists_neg_le_sum_cos_div_rpow :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ σ : ℝ, 0 ≤ σ → ∀ N : ℕ,
      -B ≤ ∑ p ∈ Nat.primesBelow N, Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) := by
  obtain ⟨B, hB, H⟩ := exists_abs_cos_prime_sum_sub_log_min_le
  exact ⟨B, hB.le, fun τ hτ hτ1 σ hσ N => le_sum_primesBelow_div_rpow hσ
    fun k _ => (sum_primesBelow_cos_div_bounds H hB.le hτ hτ1 k).1⟩

/-- **The weighted cosine prime sum is bounded above, below height `1`.**  There is an absolute
`B` with `∑_{p<N} cos(τ log p)/p^{1+2σ} ≤ log(min{log N, 1/τ}/log 2) + B` for all `0 < τ ≤ 1`,
`σ ≥ 0` and `N ≥ 2`. -/
theorem exists_sum_cos_div_rpow_le_log_min :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ σ : ℝ, 0 ≤ σ → ∀ N : ℕ, 2 ≤ N →
      ∑ p ∈ Nat.primesBelow N, Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ)
        ≤ Real.log (min (Real.log N) (1 / τ) / Real.log 2) + B := by
  obtain ⟨B, hB, H⟩ := exists_abs_cos_prime_sum_sub_log_min_le
  refine ⟨B, hB.le, fun τ hτ hτ1 σ hσ N hN => sum_primesBelow_div_rpow_le hσ fun k hk => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hmin := Real.log_nonneg (one_le_min_log_div_log_two hτ hτ1 hN2)
  rcases le_or_gt k 1 with hk1 | hk1
  · rw [primesBelow_eq_empty (by omega), Finset.sum_empty]
    linarith
  · have hk2 : 2 ≤ k := hk1
    have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    refine le_trans ((sum_primesBelow_cos_div_bounds H hB.le hτ hτ1 k).2 hk2) ?_
    have := log_min_log_div_log_two_le hτ hτ1 hk2' (by exact_mod_cast hk : (k : ℝ) ≤ N)
    linarith

/-! ### The factor `|1 - z|^{-2}` -/

/-- `|1 - z|² ≤ exp(-2 Re z + |z|²)`, from `1 + u ≤ eᵘ`. -/
lemma normSq_one_sub_le_exp (z : ℂ) : ‖1 - z‖ ^ 2 ≤ Real.exp (-2 * z.re + ‖z‖ ^ 2) := by
  have h : ‖1 - z‖ ^ 2 = 1 + (-2 * z.re + ‖z‖ ^ 2) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  rw [h]
  linarith [Real.add_one_le_exp (-2 * z.re + ‖z‖ ^ 2)]

/-- `|1 + z|² ≤ exp(2 Re z + |z|²)`. -/
lemma normSq_one_add_le_exp (z : ℂ) : ‖1 + z‖ ^ 2 ≤ Real.exp (2 * z.re + ‖z‖ ^ 2) := by
  have h : ‖1 + z‖ ^ 2 = 1 + (2 * z.re + ‖z‖ ^ 2) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
    ring
  rw [h]
  linarith [Real.add_one_le_exp (2 * z.re + ‖z‖ ^ 2)]

/-- `exp(2 Re z - |z|²) ≤ |1 - z|^{-2}` for `z ≠ 1`. -/
lemma exp_le_inv_normSq_one_sub {z : ℂ} (hz : z ≠ 1) :
    Real.exp (2 * z.re - ‖z‖ ^ 2) ≤ (‖1 - z‖ ^ 2)⁻¹ := by
  have hpos : 0 < ‖1 - z‖ ^ 2 := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hz))) 2
  rw [le_inv_comm₀ (Real.exp_pos _) hpos, ← Real.exp_neg]
  calc ‖1 - z‖ ^ 2 ≤ Real.exp (-2 * z.re + ‖z‖ ^ 2) := normSq_one_sub_le_exp z
    _ = Real.exp (-(2 * z.re - ‖z‖ ^ 2)) := by congr 1; ring

/-- `|1 - z|^{-2} ≤ exp(2 Re z + |z|²)/(1 - |z|²)²` for `|z| < 1`, because
`|1 - z|·|1 + z| = |1 - z²| ≥ 1 - |z|²`. -/
lemma inv_normSq_one_sub_le {z : ℂ} (hz : ‖z‖ < 1) :
    (‖1 - z‖ ^ 2)⁻¹ ≤ Real.exp (2 * z.re + ‖z‖ ^ 2) / (1 - ‖z‖ ^ 2) ^ 2 := by
  have hz0 := norm_nonneg z
  have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith
  have hd : 0 < 1 - ‖z‖ ^ 2 := by linarith
  have hprod : ‖1 - z‖ * ‖1 + z‖ = ‖1 - z ^ 2‖ := by
    rw [← norm_mul]
    congr 1
    ring
  have hlow : 1 - ‖z‖ ^ 2 ≤ ‖1 - z ^ 2‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (z ^ 2)
    rwa [norm_one, norm_pow] at h
  have hne1 : 0 < ‖1 - z‖ := by
    refine norm_pos_iff.2 (sub_ne_zero.2 fun h => ?_)
    rw [← h, norm_one] at hz
    exact lt_irrefl _ hz
  have hne2 : 0 < ‖1 + z‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have hz' : z = -1 := by linear_combination h
    rw [hz', norm_neg, norm_one] at hz
    exact lt_irrefl _ hz
  have h1 : (‖1 - z‖ ^ 2)⁻¹ = ‖1 + z‖ ^ 2 / ‖1 - z ^ 2‖ ^ 2 := by
    rw [← hprod, mul_pow]
    field_simp
  rw [h1]
  calc ‖1 + z‖ ^ 2 / ‖1 - z ^ 2‖ ^ 2 ≤ ‖1 + z‖ ^ 2 / (1 - ‖z‖ ^ 2) ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hd 2) (pow_le_pow_left₀ hd.le hlow 2)
    _ ≤ Real.exp (2 * z.re + ‖z‖ ^ 2) / (1 - ‖z‖ ^ 2) ^ 2 :=
        div_le_div_of_nonneg_right (normSq_one_add_le_exp z) (pow_pos hd 2).le

/-- `exp(-2u) ≤ 1 - u` for `0 ≤ u ≤ ½`. -/
lemma exp_neg_two_mul_le_one_sub {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    Real.exp (-(2 * u)) ≤ 1 - u := by
  have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  have hpos : 0 < 1 + 2 * u := by linarith
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - u)]

/-! ### The extended Euler product -/

/-- **The extended Euler product is the Rademacher one times a deterministic factor**, wherever
`v(p)² = 1`: `F^e(s) = F(s)·∏_{p<N}(1 - (p^{-s})²)⁻¹` for `Re s > 0`. -/
lemma eulerProduct_compMultExtension_eq_mul {v : ℕ → ℂ} {N : ℕ} {s : ℂ} (hs : 0 < s.re)
    (hv : ∀ p ∈ Nat.primesBelow N, v p ^ 2 = 1) :
    eulerProduct (fun n => compMultExtension v n) N s
      = eulerProduct (fun n => squarefreeExtension v n) N s
        * ∏ p ∈ Nat.primesBelow N, (1 - ((p : ℂ) ^ (-s)) ^ 2)⁻¹ := by
  have hv1 : ∀ p ∈ Nat.primesBelow N, ‖v p‖ = 1 := by
    intro p hp
    have h := congrArg norm (hv p hp)
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  have hnorm : ∀ p ∈ Nat.primesBelow N, ‖v p‖ < (p : ℝ) ^ s.re := by
    intro p hp
    rw [hv1 p hp]
    exact one_lt_prime_rpow (Nat.prime_of_mem_primesBelow hp) hs
  rw [eulerProduct_compMultExtension v N hnorm, eulerProduct_squarefreeExtension,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' := Nat.prime_of_mem_primesBelow hp
  have hz : ‖(p : ℂ) ^ (-s)‖ < 1 := norm_prime_cpow_neg_lt_one hp' hs
  have hz2 : ‖((p : ℂ) ^ (-s)) ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hz two_ne_zero
  have h1 : (1 : ℂ) - ((p : ℂ) ^ (-s)) ^ 2 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hz2
    exact lt_irrefl _ hz2
  have h2 : (1 : ℂ) - v p * (p : ℂ) ^ (-s) ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    have h' := congrArg norm h
    rw [norm_one, norm_mul, hv1 p hp, one_mul] at h'
    rw [← h'] at hz
    exact lt_irrefl _ hz
  rw [eq_mul_inv_iff_mul_eq₀ h1, inv_mul_eq_iff_eq_mul₀ h2]
  linear_combination ((p : ℂ) ^ (-s)) ^ 2 * hv p hp

/-- **The ratio, almost surely.**  For Rademacher `X`, almost surely, for every `s` with
`Re s > 0`, `|F^e(s)|² = |F(s)|²·∏_{p<N}|1 - (p^{-s})²|^{-2}`. -/
theorem ae_normSq_randomEulerProduct_compMult_eq {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) (N : ℕ) :
    ∀ᵐ ω ∂μ, ∀ s : ℂ, 0 < s.re →
      ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N s ω‖ ^ 2
        = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N s ω‖ ^ 2
          * ∏ p ∈ Nat.primesBelow N, (‖1 - ((p : ℂ) ^ (-s)) ^ 2‖ ^ 2)⁻¹ := by
  filter_upwards [(Filter.eventually_all_finset (Nat.primesBelow N)).2
    fun p hp => ae_sq_X_eq_one hX (Nat.prime_of_mem_primesBelow hp)] with ω hω
  intro s hs
  rw [randomEulerProduct, randomEulerProduct, eulerProduct_compMultExtension_eq_mul hs hω,
    norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [norm_inv, inv_pow]

/-- `exp(∑(2 Re z_p - |z_p|²)) ≤ ∏ |1 - z_p|^{-2}`, factor by factor. -/
lemma exp_sum_le_prod_inv_normSq {s : Finset ℕ} {z : ℕ → ℂ} (hz : ∀ p ∈ s, z p ≠ 1) :
    Real.exp (∑ p ∈ s, (2 * (z p).re - ‖z p‖ ^ 2)) ≤ ∏ p ∈ s, (‖1 - z p‖ ^ 2)⁻¹ := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le)
    fun p hp => exp_le_inv_normSq_one_sub (hz p hp)

/-- `∏ |1 - z_p|^{-2} ≤ exp(∑(2 Re z_p + |z_p|²))/∏(1 - |z_p|²)²`, factor by factor. -/
lemma prod_inv_normSq_le_exp_sum {s : Finset ℕ} {z : ℕ → ℂ} (hz : ∀ p ∈ s, ‖z p‖ < 1) :
    ∏ p ∈ s, (‖1 - z p‖ ^ 2)⁻¹
      ≤ Real.exp (∑ p ∈ s, (2 * (z p).re + ‖z p‖ ^ 2)) / ∏ p ∈ s, (1 - ‖z p‖ ^ 2) ^ 2 := by
  rw [Real.exp_sum, ← Finset.prod_div_distrib]
  exact Finset.prod_le_prod (fun p _ => inv_nonneg.2 (sq_nonneg _))
    fun p hp => inv_normSq_one_sub_le (hz p hp)

/-! ### The factor on the line `½ + σ + it` -/

/-- `|p^{-s}| = p^{-(½+σ)}` on the line `s = ½ + σ + it`. -/
lemma norm_prime_cpow_neg_line {p : ℕ} (hp : p.Prime) (σ t : ℝ) :
    ‖(p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))‖ = (p : ℝ) ^ (-(1 / 2 + σ)) := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos]
  congr 1
  simp

/-- `|(p^{-s})²|² ≤ p^{-2}` on the line, for `σ ≥ 0`. -/
lemma normSq_sq_prime_cpow_neg_line_le {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) :
    ‖((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) ^ 2‖ ^ 2
      ≤ (((p : ℕ) : ℝ) ^ 2)⁻¹ := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  rw [norm_pow, norm_prime_cpow_neg_line hp σ t, ← pow_mul]
  have hle : (p : ℝ) ^ (-(1 / 2 + σ)) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  calc ((p : ℝ) ^ (-(1 / 2 + σ))) ^ (2 * 2)
      ≤ ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ (2 * 2) :=
        pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) hle _
    _ = ((p : ℝ) ^ 2)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast,
          ← Real.rpow_neg hp0.le]
        norm_num

/-- `Re (p^{-s})² = cos(2t log p)/p^{1+2σ}` on the line `s = ½ + σ + it`. -/
lemma re_sq_prime_cpow_neg_line {p : ℕ} (hp : p.Prime) (σ t : ℝ) :
    (((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) ^ 2).re
      = Real.cos (2 * t * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.exp_nat_mul, Complex.exp_re,
    ← Complex.natCast_log]
  have hre : (((2 : ℕ) : ℂ) * ((Real.log p : ℂ)
      * -((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))).re = -(Real.log p * (1 + 2 * σ)) := by
    simp [Complex.log_re, Complex.log_im, Complex.natCast_arg]
    ring
  have him : (((2 : ℕ) : ℂ) * ((Real.log p : ℂ)
      * -((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))).im = -(2 * t * Real.log p) := by
    simp [Complex.log_re, Complex.log_im, Complex.natCast_arg]
    ring
  rw [hre, him, Real.cos_neg, Real.exp_neg, ← Real.rpow_def_of_pos hpR, div_eq_mul_inv, mul_comm]

/-- **The factor on the line, from below.**  For `σ ≥ 0` and every `t`,
`exp(2∑_{p<N} cos(2t log p)/p^{1+2σ} - 1) ≤ ∏_{p<N}|1 - (p^{-s})²|^{-2}`. -/
theorem exp_two_mul_sum_cos_sub_one_le_prod {N : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) :
    Real.exp (2 * ∑ p ∈ Nat.primesBelow N,
        Real.cos (2 * t * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) - 1)
      ≤ ∏ p ∈ Nat.primesBelow N,
          (‖1 - ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) ^ 2‖ ^ 2)⁻¹ := by
  have hsre : 0 < ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re := by
    simp
    linarith
  have hz : ∀ p ∈ Nat.primesBelow N,
      ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) ^ 2 ≠ 1 := by
    intro p hp h
    have hlt : ‖((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) ^ 2‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _)
        (norm_prime_cpow_neg_lt_one (Nat.prime_of_mem_primesBelow hp) hsre) two_ne_zero
    rw [h, norm_one] at hlt
    exact lt_irrefl _ hlt
  refine le_trans (Real.exp_le_exp.2 ?_) (exp_sum_le_prod_inv_normSq hz)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ p ∈ Nat.primesBelow N,
      (((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) ^ 2).re
      = ∑ p ∈ Nat.primesBelow N, Real.cos (2 * t * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) :=
    Finset.sum_congr rfl fun p hp => re_sq_prime_cpow_neg_line (Nat.prime_of_mem_primesBelow hp) σ t
  have h2 : ∑ p ∈ Nat.primesBelow N,
      ‖((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) ^ 2‖ ^ 2 ≤ 1 :=
    le_trans (Finset.sum_le_sum fun p hp =>
      normSq_sq_prime_cpow_neg_line_le (Nat.prime_of_mem_primesBelow hp) hσ t)
      (sum_primesBelow_inv_sq_le N)
  rw [h1]
  linarith

/-- **The factor on the line, from above.**  For `σ ≥ 0` and every `t`,
`∏_{p<N}|1 - (p^{-s})²|^{-2} ≤ exp(2∑_{p<N} cos(2t log p)/p^{1+2σ} + 5)`. -/
theorem prod_le_exp_two_mul_sum_cos_add_five {N : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) :
    ∏ p ∈ Nat.primesBelow N,
        (‖1 - ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) ^ 2‖ ^ 2)⁻¹
      ≤ Real.exp (2 * ∑ p ∈ Nat.primesBelow N,
          Real.cos (2 * t * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) + 5) := by
  have hsre : 0 < ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re := by
    simp
    linarith
  set z : ℕ → ℂ := fun p => ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) ^ 2
    with hzdef
  have hz1 : ∀ p ∈ Nat.primesBelow N, ‖z p‖ < 1 := by
    intro p hp
    rw [hzdef, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _)
      (norm_prime_cpow_neg_lt_one (Nat.prime_of_mem_primesBelow hp) hsre) two_ne_zero
  have hsq : ∀ p ∈ Nat.primesBelow N, ‖z p‖ ^ 2 ≤ (((p : ℕ) : ℝ) ^ 2)⁻¹ := fun p hp =>
    normSq_sq_prime_cpow_neg_line_le (Nat.prime_of_mem_primesBelow hp) hσ t
  have hsum : ∑ p ∈ Nat.primesBelow N, ‖z p‖ ^ 2 ≤ 1 :=
    le_trans (Finset.sum_le_sum hsq) (sum_primesBelow_inv_sq_le N)
  have hquart : ∀ p ∈ Nat.primesBelow N, ‖z p‖ ^ 2 ≤ 1 / 2 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have : (((p : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      nlinarith
    exact le_trans (hsq p hp) this
  -- the denominator: `∏(1 - |z_p|²)² ≥ exp(-4∑|z_p|²) ≥ e^{-4}`
  have hden : Real.exp (-4) ≤ ∏ p ∈ Nat.primesBelow N, (1 - ‖z p‖ ^ 2) ^ 2 := by
    calc Real.exp (-4) ≤ Real.exp (∑ p ∈ Nat.primesBelow N, (-(2 * ‖z p‖ ^ 2)) * 2) := by
          refine Real.exp_le_exp.2 ?_
          rw [← Finset.sum_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]
          linarith
      _ = ∏ p ∈ Nat.primesBelow N, Real.exp (-(2 * ‖z p‖ ^ 2)) ^ 2 := by
          rw [Real.exp_sum]
          refine Finset.prod_congr rfl fun p _ => ?_
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
      _ ≤ ∏ p ∈ Nat.primesBelow N, (1 - ‖z p‖ ^ 2) ^ 2 :=
          Finset.prod_le_prod (fun p _ => sq_nonneg _) fun p hp =>
            pow_le_pow_left₀ (Real.exp_pos _).le
              (exp_neg_two_mul_le_one_sub (sq_nonneg _) (hquart p hp)) 2
  have hre : ∑ p ∈ Nat.primesBelow N, (z p).re
      = ∑ p ∈ Nat.primesBelow N, Real.cos (2 * t * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) :=
    Finset.sum_congr rfl fun p hp => re_sq_prime_cpow_neg_line (Nat.prime_of_mem_primesBelow hp) σ t
  have hnum : Real.exp (∑ p ∈ Nat.primesBelow N, (2 * (z p).re + ‖z p‖ ^ 2))
      ≤ Real.exp (2 * ∑ p ∈ Nat.primesBelow N,
          Real.cos (2 * t * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) + 1) := by
    refine Real.exp_le_exp.2 ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hre]
    linarith
  refine le_trans (prod_inv_normSq_le_exp_sum hz1) ?_
  rw [div_le_iff₀ (lt_of_lt_of_le (Real.exp_pos _) hden)]
  calc Real.exp (∑ p ∈ Nat.primesBelow N, (2 * (z p).re + ‖z p‖ ^ 2))
      ≤ Real.exp (2 * ∑ p ∈ Nat.primesBelow N,
          Real.cos (2 * t * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) + 1) := hnum
    _ = Real.exp (2 * ∑ p ∈ Nat.primesBelow N,
          Real.cos (2 * t * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) + 5) * Real.exp (-4) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (2 * ∑ p ∈ Nat.primesBelow N,
          Real.cos (2 * t * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) + 5)
          * ∏ p ∈ Nat.primesBelow N, (1 - ‖z p‖ ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le

/-! ### The cosine prime sums above height `1` -/

/-- **The wide block bound, iterated.**  If the block estimate `K/(τ log y₁)` holds on every block
`(y₁, y₂]` with `e^ℓ ≤ y₁` and `log y₂ ≤ 3 log y₁`, then the cosine prime sum over `(e^ℓ, u]` with
`log u ≤ 3^j ℓ` is at most `K/(τℓ)·∑_{i<j} 3^{-i}` in modulus: the blocks
`(e^{3^i ℓ}, e^{3^{i+1} ℓ}]` contribute a geometric series. -/
lemma abs_sum_Ioc_cos_div_le_of_blocks {K τ ℓ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hℓ : 0 < ℓ)
    (H : ∀ y₁ y₂ : ℝ, Real.exp ℓ ≤ y₁ → y₁ ≤ y₂ → Real.log y₂ ≤ 3 * Real.log y₁ →
      |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p|
        ≤ K / (τ * Real.log y₁)) (j : ℕ) :
    ∀ u : ℝ, Real.exp ℓ ≤ u → Real.log u ≤ 3 ^ j * ℓ →
      |∑ p ∈ Finset.Ioc ⌊Real.exp ℓ⌋₊ ⌊u⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p|
        ≤ K / (τ * ℓ) * ∑ i ∈ Finset.range j, (1 / 3 : ℝ) ^ i := by
  induction j with
  | zero =>
    intro u hu hlog
    have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos ℓ) hu
    have hue : u ≤ Real.exp ℓ := by
      rw [← Real.exp_log hu0]
      exact Real.exp_le_exp.2 (by simpa using hlog)
    rw [le_antisymm hue hu]
    simp
  | succ j ih =>
    intro u hu hlog
    have hcoef : 0 ≤ K / (τ * ℓ) := by positivity
    rcases le_or_gt (Real.log u) (3 ^ j * ℓ) with hj | hj
    · refine le_trans (ih u hu hj) (mul_le_mul_of_nonneg_left ?_ hcoef)
      rw [Finset.sum_range_succ]
      linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3) j]
    · have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos ℓ) hu
      have h3j : (1 : ℝ) ≤ 3 ^ j := one_le_pow₀ (by norm_num)
      have hvℓ : Real.exp ℓ ≤ Real.exp (3 ^ j * ℓ) :=
        Real.exp_le_exp.2 (le_mul_of_one_le_left hℓ.le h3j)
      have hvu : Real.exp (3 ^ j * ℓ) ≤ u := by
        rw [← Real.exp_log hu0]
        exact Real.exp_le_exp.2 hj.le
      have hlogv : Real.log (Real.exp (3 ^ j * ℓ)) = 3 ^ j * ℓ := Real.log_exp _
      have hsplit : ∑ p ∈ Finset.Ioc ⌊Real.exp ℓ⌋₊ ⌊u⌋₊ with Nat.Prime p,
            Real.cos (τ * Real.log p) / p
          = (∑ p ∈ Finset.Ioc ⌊Real.exp ℓ⌋₊ ⌊Real.exp (3 ^ j * ℓ)⌋₊ with Nat.Prime p,
              Real.cos (τ * Real.log p) / p)
            + ∑ p ∈ Finset.Ioc ⌊Real.exp (3 ^ j * ℓ)⌋₊ ⌊u⌋₊ with Nat.Prime p,
              Real.cos (τ * Real.log p) / p := by
        rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
          Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor hvℓ) (Nat.floor_le_floor hvu)]
      have h1 := ih (Real.exp (3 ^ j * ℓ)) hvℓ (le_of_eq hlogv)
      have h2 := H (Real.exp (3 ^ j * ℓ)) u hvℓ hvu (by
        rw [hlogv]
        have : (3 : ℝ) ^ (j + 1) * ℓ = 3 * (3 ^ j * ℓ) := by ring
        linarith)
      rw [hlogv] at h2
      have hK3 : K / (τ * (3 ^ j * ℓ)) = K / (τ * ℓ) * (1 / 3) ^ j := by
        rw [one_div_pow, div_mul_div_comm, mul_one, mul_comm (3 ^ j) ℓ, ← mul_assoc]
      rw [hsplit, Finset.sum_range_succ, mul_add]
      calc _ ≤ |∑ p ∈ Finset.Ioc ⌊Real.exp ℓ⌋₊ ⌊Real.exp (3 ^ j * ℓ)⌋₊ with Nat.Prime p,
              Real.cos (τ * Real.log p) / p|
            + |∑ p ∈ Finset.Ioc ⌊Real.exp (3 ^ j * ℓ)⌋₊ ⌊u⌋₊ with Nat.Prime p,
              Real.cos (τ * Real.log p) / p| := abs_add_le _ _
        _ ≤ _ := by linarith

/-- `∑_{i<j} 3^{-i} ≤ 3/2`. -/
lemma sum_range_one_third_pow_le (j : ℕ) : ∑ i ∈ Finset.range j, (1 / 3 : ℝ) ^ i ≤ 3 / 2 := by
  rw [geom_sum_eq (by norm_num) j]
  have h : (0 : ℝ) ≤ (1 / 3) ^ j := by positivity
  rw [div_le_iff_of_neg (by norm_num)]
  linarith

/-- **The unweighted cosine prime sums above height `1`.**  There is an absolute `B` with
`∑_{p<k} cos(τ log p)/p ≤ 10·log log(τ+3) + B` for every `τ ≥ 1` and every `k`.  The primes up to
`e^ℓ`, `ℓ = max{log y₀, ((4/c)·log(τ+3))^{10}}`, are bounded by Mertens
(`RMF.sum_primesBelow_inv_le_log_log_add`), at a cost `log ℓ ≤ 10 log log(τ+3) + O(1)`; past `e^ℓ`
the wide block estimate (`RMF.exists_abs_cos_prime_sum_block_le_wide`) applies on every block
`(v, v³]`, and the blocks sum geometrically. -/
theorem exists_sum_primesBelow_cos_div_le_log_log :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, 1 ≤ τ → ∀ k : ℕ,
      ∑ p ∈ Nat.primesBelow k, Real.cos (τ * Real.log p) / p
        ≤ 10 * Real.log (Real.log (τ + 3)) + B := by
  obtain ⟨K, c, y₀, hK, hc, hy₀, Hw⟩ := exists_abs_cos_prime_sum_block_le_wide
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hly₀ : Real.log 2 ≤ Real.log y₀ := Real.log_le_log (by norm_num) hy₀
  have hc4 : (1 : ℝ) ≤ 1 + 4 / c := le_add_of_nonneg_right (by positivity)
  have hy1 : (1 : ℝ) ≤ 1 + Real.log y₀ := by linarith
  refine ⟨Real.log (1 + Real.log y₀) + 10 * Real.log (1 + 4 / c) + 1.42 + 3 / 2 * K / Real.log 2,
    add_nonneg (add_nonneg (add_nonneg (Real.log_nonneg hy1)
      (mul_nonneg (by norm_num) (Real.log_nonneg hc4))) (by norm_num))
      (div_nonneg (mul_nonneg (by norm_num) hK.le) hlog2.le), ?_⟩
  intro τ hτ k
  have hτ0 : 0 < τ := by linarith
  -- `L = log(τ+3) ≥ 1`
  have hL1 : 1 ≤ Real.log (τ + 3) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  -- the threshold `ℓ`
  have hℓ0 : 0 < max (Real.log y₀) ((4 / c * Real.log (τ + 3)) ^ 10) :=
    lt_of_lt_of_le hlog2 (le_trans hly₀ (le_max_left _ _))
  have hy₀ℓ : y₀ ≤ Real.exp (max (Real.log y₀) ((4 / c * Real.log (τ + 3)) ^ 10)) :=
    calc y₀ = Real.exp (Real.log y₀) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.2 (le_max_left _ _)
  -- the block estimate holds past `e^ℓ`
  have Hb : ∀ y₁ y₂ : ℝ, Real.exp (max (Real.log y₀) ((4 / c * Real.log (τ + 3)) ^ 10)) ≤ y₁ →
      y₁ ≤ y₂ → Real.log y₂ ≤ 3 * Real.log y₁ →
      |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p|
        ≤ K / (τ * Real.log y₁) := by
    intro y₁ y₂ h1 h12 h3
    refine Hw τ hτ0 y₁ y₂ (le_trans hy₀ℓ h1) h12 h3 ?_
    have hlog1 : max (Real.log y₀) ((4 / c * Real.log (τ + 3)) ^ 10) ≤ Real.log y₁ := by
      rw [← Real.log_exp (max (Real.log y₀) ((4 / c * Real.log (τ + 3)) ^ 10))]
      exact Real.log_le_log (Real.exp_pos _) h1
    have hb0 : 0 ≤ 4 / c * Real.log (τ + 3) := by positivity
    have hroot : 4 / c * Real.log (τ + 3) ≤ Real.log y₁ ^ ((1 : ℝ) / 10) := by
      calc 4 / c * Real.log (τ + 3)
          = ((4 / c * Real.log (τ + 3)) ^ 10) ^ ((1 : ℝ) / 10) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hb0]
            norm_num
        _ ≤ Real.log y₁ ^ ((1 : ℝ) / 10) :=
            Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hlog1) (by norm_num)
    have hlogτ : Real.log τ ≤ Real.log (τ + 3) := Real.log_le_log hτ0 (by linarith)
    calc τ ^ 2 = Real.exp (2 * Real.log τ) := by
          rw [← Real.log_rpow hτ0, Real.exp_log (Real.rpow_pos_of_pos hτ0 _)]
          norm_num
      _ ≤ Real.exp (c / 2 * Real.log y₁ ^ ((1 : ℝ) / 10)) := by
          refine Real.exp_le_exp.2 ?_
          have h := mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ c / 2)
          have he : c / 2 * (4 / c * Real.log (τ + 3)) = 2 * Real.log (τ + 3) := by
            field_simp
            ring
          linarith
  set ℓ : ℝ := max (Real.log y₀) ((4 / c * Real.log (τ + 3)) ^ 10) with hℓdef
  -- the head: Mertens below `e^ℓ`
  have hM2 : 2 ≤ ⌊Real.exp ℓ⌋₊ := Nat.le_floor (by exact_mod_cast le_trans hy₀ hy₀ℓ)
  have hMℓ : Real.log (Real.log (⌊Real.exp ℓ⌋₊ : ℕ)) ≤ Real.log ℓ := by
    have hM2' : (2 : ℝ) ≤ (⌊Real.exp ℓ⌋₊ : ℕ) := by exact_mod_cast hM2
    have hlogM : Real.log (⌊Real.exp ℓ⌋₊ : ℕ) ≤ ℓ :=
      calc Real.log (⌊Real.exp ℓ⌋₊ : ℕ) ≤ Real.log (Real.exp ℓ) :=
            Real.log_le_log (by linarith) (Nat.floor_le (Real.exp_pos ℓ).le)
        _ = ℓ := Real.log_exp ℓ
    exact Real.log_le_log (Real.log_pos (by linarith)) hlogM
  have hlogℓ : Real.log ℓ ≤ Real.log (1 + Real.log y₀) + 10 * Real.log (1 + 4 / c)
      + 10 * Real.log (Real.log (τ + 3)) := by
    have hb0 : 0 ≤ 4 / c * Real.log (τ + 3) :=
      mul_nonneg (div_nonneg (by norm_num) hc.le) (by linarith)
    have hb1 : 1 + 4 / c * Real.log (τ + 3) ≤ (1 + 4 / c) * Real.log (τ + 3) := by nlinarith
    have hb2 : (1 : ℝ) ≤ 1 + 4 / c * Real.log (τ + 3) := le_add_of_nonneg_right hb0
    have hmax : ℓ ≤ (1 + Real.log y₀) * (1 + 4 / c * Real.log (τ + 3)) ^ 10 := by
      have hA : (1 : ℝ) ≤ (1 + 4 / c * Real.log (τ + 3)) ^ 10 := one_le_pow₀ hb2
      have hB : (4 / c * Real.log (τ + 3)) ^ 10 ≤ (1 + 4 / c * Real.log (τ + 3)) ^ 10 :=
        pow_le_pow_left₀ hb0 (by linarith) 10
      refine max_le ?_ ?_
      · nlinarith
      · nlinarith [hly₀]
    calc Real.log ℓ ≤ Real.log ((1 + Real.log y₀) * (1 + 4 / c * Real.log (τ + 3)) ^ 10) :=
          Real.log_le_log hℓ0 hmax
      _ = Real.log (1 + Real.log y₀) + 10 * Real.log (1 + 4 / c * Real.log (τ + 3)) := by
          rw [Real.log_mul (by linarith : (0 : ℝ) < 1 + Real.log y₀).ne'
            (pow_pos (by linarith : (0 : ℝ) < 1 + 4 / c * Real.log (τ + 3)) 10).ne', Real.log_pow]
          norm_num
      _ ≤ Real.log (1 + Real.log y₀) + 10 * Real.log ((1 + 4 / c) * Real.log (τ + 3)) := by
          gcongr
      _ = Real.log (1 + Real.log y₀) + 10 * Real.log (1 + 4 / c)
            + 10 * Real.log (Real.log (τ + 3)) := by
          rw [Real.log_mul (by linarith : (0 : ℝ) < 1 + 4 / c).ne'
            (by linarith : (0 : ℝ) < Real.log (τ + 3)).ne']
          ring
  have hhead : ∑ p ∈ Nat.primesBelow (⌊Real.exp ℓ⌋₊ + 1), ((p : ℝ))⁻¹
      ≤ Real.log ℓ + 1.42 := by
    have := sum_primesBelow_inv_le_log_log_add hM2
    linarith
  -- the tail: the blocks past `e^ℓ`
  have hKℓ : K / (τ * ℓ) ≤ K / Real.log 2 :=
    div_le_div_of_nonneg_left hK.le hlog2 (by nlinarith [le_trans hly₀ (le_max_left (Real.log y₀)
      ((4 / c * Real.log (τ + 3)) ^ 10))])
  have htail : ∀ u : ℝ, Real.exp ℓ ≤ u →
      |∑ p ∈ Finset.Ioc ⌊Real.exp ℓ⌋₊ ⌊u⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p|
        ≤ 3 / 2 * K / Real.log 2 := by
    intro u hu
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (Real.log u / ℓ) (by norm_num : (1 : ℝ) < 3)
    have hlogu : Real.log u ≤ 3 ^ j * ℓ := by
      rw [div_lt_iff₀ hℓ0] at hj
      linarith
    refine le_trans (abs_sum_Ioc_cos_div_le_of_blocks hK.le hτ0 hℓ0 Hb j u hu hlogu) ?_
    calc K / (τ * ℓ) * ∑ i ∈ Finset.range j, (1 / 3 : ℝ) ^ i ≤ K / Real.log 2 * (3 / 2) :=
          mul_le_mul hKℓ (sum_range_one_third_pow_le j)
            (Finset.sum_nonneg fun i _ => by positivity) (by positivity)
      _ = 3 / 2 * K / Real.log 2 := by ring
  have hlogL : 0 ≤ Real.log (Real.log (τ + 3)) := Real.log_nonneg hL1
  -- assemble at `k`
  have hcos : ∀ p : ℕ, Real.cos (τ * Real.log p) / p ≤ ((p : ℝ))⁻¹ := fun p => by
    rw [← one_div]
    exact div_le_div_of_nonneg_right (Real.cos_le_one _) (Nat.cast_nonneg p)
  have hpos : ∀ p : ℕ, (0 : ℝ) ≤ ((p : ℝ))⁻¹ := fun p => inv_nonneg.2 (Nat.cast_nonneg p)
  have hconst : 0 ≤ 3 / 2 * K / Real.log 2 := by positivity
  rcases le_or_gt k (⌊Real.exp ℓ⌋₊ + 1) with hk | hk
  · have hsub : Nat.primesBelow k ⊆ Nat.primesBelow (⌊Real.exp ℓ⌋₊ + 1) := fun p hp => by
      rw [Nat.mem_primesBelow] at hp ⊢
      exact ⟨lt_of_lt_of_le hp.1 hk, hp.2⟩
    calc ∑ p ∈ Nat.primesBelow k, Real.cos (τ * Real.log p) / p
        ≤ ∑ p ∈ Nat.primesBelow k, ((p : ℝ))⁻¹ := Finset.sum_le_sum fun p _ => hcos p
      _ ≤ ∑ p ∈ Nat.primesBelow (⌊Real.exp ℓ⌋₊ + 1), ((p : ℝ))⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hpos p
      _ ≤ _ := by linarith
  · have hsplit : ∑ p ∈ Nat.primesBelow k, Real.cos (τ * Real.log p) / p
        = ∑ p ∈ Nat.primesBelow (⌊Real.exp ℓ⌋₊ + 1), Real.cos (τ * Real.log p) / p
          + ∑ p ∈ Finset.Ioc ⌊Real.exp ℓ⌋₊ ⌊((k - 1 : ℕ) : ℝ)⌋₊ with Nat.Prime p,
            Real.cos (τ * Real.log p) / p := by
      rw [sum_primesBelow_eq_sum_range, sum_primesBelow_eq_sum_range, Finset.sum_filter,
        Nat.floor_natCast, ← Finset.sum_range_add_sum_Ico _ hk.le]
      congr 1
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    have hu : Real.exp ℓ ≤ ((k - 1 : ℕ) : ℝ) := by
      have h1 : Real.exp ℓ < (⌊Real.exp ℓ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : ⌊Real.exp ℓ⌋₊ + 1 ≤ k - 1 := by omega
      have h3 : ((⌊Real.exp ℓ⌋₊ + 1 : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at h3
      linarith
    have ht := abs_le.1 (htail _ hu)
    have hh : ∑ p ∈ Nat.primesBelow (⌊Real.exp ℓ⌋₊ + 1), Real.cos (τ * Real.log p) / p
        ≤ Real.log ℓ + 1.42 :=
      le_trans (Finset.sum_le_sum fun p _ => hcos p) hhead
    rw [hsplit]
    linarith [ht.2]

/-- **The weighted cosine prime sum above height `1`.**  There is an absolute `B` with
`∑_{p<N} cos(τ log p)/p^{1+2σ} ≤ 10·log log(τ+3) + B` for all `τ ≥ 1`, `σ ≥ 0` and `N`. -/
theorem exists_sum_cos_div_rpow_le_log_log :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, 1 ≤ τ → ∀ σ : ℝ, 0 ≤ σ → ∀ N : ℕ,
      ∑ p ∈ Nat.primesBelow N, Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ)
        ≤ 10 * Real.log (Real.log (τ + 3)) + B := by
  obtain ⟨B, hB, H⟩ := exists_sum_primesBelow_cos_div_le_log_log
  exact ⟨B, hB, fun τ hτ σ hσ N => sum_primesBelow_div_rpow_le hσ fun k _ => H τ hτ k⟩

/-! ### The factor on the line, in the forms consumed -/

/-- `cos(2t log p) = cos(2|t| log p)`. -/
lemma cos_two_mul_mul_log_eq_abs (t : ℝ) (p : ℕ) :
    Real.cos (2 * t * Real.log p) = Real.cos (2 * |t| * Real.log p) := by
  rw [← Real.cos_abs (2 * t * Real.log p), abs_mul, abs_mul, abs_two,
    abs_of_nonneg (Real.log_natCast_nonneg p)]

/-- **The factor is bounded below on `|t| ≤ ½`.**  There is an absolute `c > 0` with
`c ≤ ∏_{p<N}|1 - (p^{-s})²|^{-2}`, `s = ½ + σ + it`, for all `N`, `σ ≥ 0` and `|t| ≤ ½`. -/
theorem exists_le_prod_inv_normSq_of_abs_le_half :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (σ t : ℝ), 0 ≤ σ → |t| ≤ 1 / 2 →
      c ≤ ∏ p ∈ Nat.primesBelow N,
          (‖1 - ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) ^ 2‖ ^ 2)⁻¹ := by
  obtain ⟨B, hB, H⟩ := exists_neg_le_sum_cos_div_rpow
  refine ⟨Real.exp (-(2 * B) - 1), Real.exp_pos _, fun N σ t hσ ht => ?_⟩
  refine le_trans (Real.exp_le_exp.2 ?_) (exp_two_mul_sum_cos_sub_one_le_prod hσ t)
  have hS : -B ≤ ∑ p ∈ Nat.primesBelow N,
      Real.cos (2 * t * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) := by
    simp_rw [cos_two_mul_mul_log_eq_abs t]
    rcases eq_or_lt_of_le (abs_nonneg t) with h0 | hpos
    · rw [← h0]
      simp only [mul_zero, zero_mul, Real.cos_zero]
      exact le_trans (by linarith) (Finset.sum_nonneg fun p _ => by positivity)
    · exact H (2 * |t|) (by positivity) (by linarith) σ hσ N
  linarith

/-- **The factor from above on `0 < |t| ≤ ½`.**  There is an absolute `C` with
`∏_{p<N}|1 - (p^{-s})²|^{-2} ≤ C·min{log N, 1/(2|t|)}²` for all `N ≥ 2`, `σ ≥ 0` and
`0 < |t| ≤ ½`. -/
theorem exists_prod_inv_normSq_le_of_abs_le_half :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (σ t : ℝ), 2 ≤ N → 0 ≤ σ → 0 < |t| → |t| ≤ 1 / 2 →
      ∏ p ∈ Nat.primesBelow N,
          (‖1 - ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) ^ 2‖ ^ 2)⁻¹
        ≤ C * min (Real.log N) (1 / (2 * |t|)) ^ 2 := by
  obtain ⟨B, hB, H⟩ := exists_sum_cos_div_rpow_le_log_min
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.exp (2 * B + 5) / Real.log 2 ^ 2, by positivity,
    fun N σ t hN hσ ht0 ht => ?_⟩
  refine le_trans (prod_le_exp_two_mul_sum_cos_add_five hσ t) ?_
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hS := H (2 * |t|) (by positivity) (by linarith) σ hσ N hN
  simp_rw [cos_two_mul_mul_log_eq_abs t]
  have hm1 := one_le_min_log_div_log_two (τ := 2 * |t|) (by positivity) (by linarith) hN2
  have hm0 : 0 < min (Real.log N) (1 / (2 * |t|)) / Real.log 2 := by linarith
  calc Real.exp (2 * ∑ p ∈ Nat.primesBelow N,
        Real.cos (2 * |t| * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) + 5)
      ≤ Real.exp (2 * (Real.log (min (Real.log N) (1 / (2 * |t|)) / Real.log 2) + B) + 5) :=
        Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (2 * B + 5) * (min (Real.log N) (1 / (2 * |t|)) / Real.log 2) ^ 2 := by
        rw [show 2 * (Real.log (min (Real.log N) (1 / (2 * |t|)) / Real.log 2) + B) + 5
            = (2 * B + 5) + Real.log ((min (Real.log N) (1 / (2 * |t|)) / Real.log 2) ^ 2) by
              rw [Real.log_pow]
              push_cast
              ring,
          Real.exp_add, Real.exp_log (pow_pos hm0 2)]
    _ = Real.exp (2 * B + 5) / Real.log 2 ^ 2 * min (Real.log N) (1 / (2 * |t|)) ^ 2 := by
        rw [div_pow]
        ring

/-- **The factor from above on `|t| ≥ ½`.**  There is an absolute `C` with
`∏_{p<N}|1 - (p^{-s})²|^{-2} ≤ C·log²⁰(2|t|+3)` for all `N`, `σ ≥ 0` and `|t| ≥ ½`. -/
theorem exists_prod_inv_normSq_le_of_half_le_abs :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (σ t : ℝ), 0 ≤ σ → 1 / 2 ≤ |t| →
      ∏ p ∈ Nat.primesBelow N,
          (‖1 - ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) ^ 2‖ ^ 2)⁻¹
        ≤ C * Real.log (2 * |t| + 3) ^ 20 := by
  obtain ⟨B, hB, H⟩ := exists_sum_cos_div_rpow_le_log_log
  refine ⟨Real.exp (2 * B + 5), Real.exp_pos _, fun N σ t hσ ht => ?_⟩
  refine le_trans (prod_le_exp_two_mul_sum_cos_add_five hσ t) ?_
  have hS := H (2 * |t|) (by linarith) σ hσ N
  simp_rw [cos_two_mul_mul_log_eq_abs t]
  have hL : 0 < Real.log (2 * |t| + 3) := Real.log_pos (by linarith [abs_nonneg t])
  calc Real.exp (2 * ∑ p ∈ Nat.primesBelow N,
        Real.cos (2 * |t| * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) + 5)
      ≤ Real.exp (2 * (10 * Real.log (Real.log (2 * |t| + 3)) + B) + 5) :=
        Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (2 * B + 5) * Real.log (2 * |t| + 3) ^ 20 := by
        rw [show 2 * (10 * Real.log (Real.log (2 * |t| + 3)) + B) + 5
            = (2 * B + 5) + Real.log (Real.log (2 * |t| + 3) ^ 20) by
              rw [Real.log_pow]
              push_cast
              ring,
          Real.exp_add, Real.exp_log (pow_pos hL 20)]

end RMF
