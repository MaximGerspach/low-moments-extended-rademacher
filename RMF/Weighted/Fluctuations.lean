/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import RMF.Weighted.BlockSums

/-!
# The fluctuation bounds (T0) and (T1)

Second moments of the truncation tails `T_y(x)` (`RMF.truncationTail`) and `T_{y,z}(x)`
(`RMF.blockTruncationTail`):

* (T0) `E|T_y(x)|² ≪ log y` for `2 ≤ y ≤ x` (`RMF.exists_integral_normSq_truncationTail_le_log`);
* (T1) `E|T_{y,z}(x)|² ≪_Λ 1` for `2 ≤ y ≤ z ≤ x` with `log z ≤ Λ·log y`
  (`RMF.exists_integral_normSq_blockTruncationTail_le`).

## The proof

Orthogonality (`RMF.integral_normSq_sum_div_sqrt_of_squarefree`) turns the second moment into
`∑ 1/n` over `T_y(x)`'s index set.  Reindexing `n = m·r` by the rough–smooth factorisation — `m`
smooth squarefree, `r = r_y(n) ≤ x` rough — that sum is `∑_m (1/m)·Σ(m)` with

`Σ(m) = ∑_{x/m < r ≤ x, r y-rough} 1/r`.

The `r = 1` term occurs only when `m > x`, and every other `y`-rough `r` exceeds `y`, so the
bound for rough reciprocals on an interval (`RMF.exists_sum_inv_rough_Ioc_le`, with
`R = max{y + H, x/m}`, `R' = max{x, y + H}`, noting `log(R'/R) ≤ log m`) gives
`Σ(m) ≪ 1_{m>x} + (1 + log m)/log y`.  Hence

`E|T_y(x)|² ≪ ∑_{m>x} 1/m + (1/log y)·∑_m (1+log m)/m`;

the first half is at most `∑_m 1/m ≪ log y` (`RMF.exists_sum_smoothSquarefree_inv_le`), and the
second is `RMF.exists_sum_smoothSquarefree_one_add_log_div_le`, giving `(log y)²/log y = log y`.

## Where the endpoint `y + H` comes from

`RMF.exists_sum_inv_rough_Ioc_le` carries an absolute threshold `H₀` on its lower endpoint, so the
endpoint used here is `max{y + H, x/m}` with `H = max{H₀, 2}`, and the upper endpoint is
`max{x, y + H}`; this keeps `R ≤ R' ≤ m·R` for every `x ≥ y ≥ 2`.  The rough `r ∈ (y, y + ⌈H⌉]`
this discards have harmonic mass `≤ log(1 + ⌈H⌉/y)`, which `RMF.log_mul_log_add_sub_le` bounds by
a constant over `log y`.
-/

open Finset MeasureTheory

namespace RMF

/-! ### The second moment of a weighted sum over a squarefree index set -/

/-- **The second moment of `∑_{n ∈ s} f(n)/√n` on the squarefrees.**  Orthogonality with
`c n = n^{-1/2}`; on a set of squarefree indices every diagonal term contributes `1/n`.

The index-set-free form of `RMF.integral_normSq_weightedRademacherSum`: the layered argument needs
the same computation over `T_y(x)`'s index set, which is not an initial segment. -/
theorem integral_normSq_sum_div_sqrt_of_squarefree {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ) {s : Finset ℕ}
    (hs0 : ∀ n ∈ s, n ≠ 0) (hssf : ∀ n ∈ s, Squarefree n) :
    (∫ ω, ‖∑ n ∈ s, f ω n / (Real.sqrt n : ℂ)‖ ^ 2 ∂μ) = ∑ n ∈ s, (n : ℝ)⁻¹ := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, -⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have key := integral_normSq_weightedSum_of_orthogonality' (f := f) (μ := μ) (s := s)
    (c := fun n : ℕ => ((Real.sqrt n : ℂ))⁻¹)
    (d := fun m => if Squarefree m then 1 else 0)
    (fun m _ n _ => hf.integrable_mul_conj m n)
    (fun m hm n hn => by
      rw [hf.orthogonality (hs0 m hm) (hs0 n hn)]
      by_cases h : m = n
      · subst h; simp
      · simp [h])
  have hTeq : ∀ ω : Ω, ∑ n ∈ s, f ω n / (Real.sqrt n : ℂ)
      = ∑ n ∈ s, ((Real.sqrt n : ℂ))⁻¹ * f ω n :=
    fun ω => Finset.sum_congr rfl fun n _ => div_eq_inv_mul _ _
  simp_rw [hTeq]
  rw [← Complex.ofReal_inj, key, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (hs0 n hn)
  have hnorm : ‖((Real.sqrt n : ℂ))⁻¹‖ = (Real.sqrt n)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [if_pos (hssf n hn), mul_one, hnorm, ← Complex.ofReal_pow, ← Real.sqrt_inv,
    Real.sq_sqrt (by positivity)]

/-! ### The rough–smooth reindexing of the tail

`RMF.sum_blockSmooth_mul_sum_rough` reindexes `{n y-rough, r_z(n) ≤ x}` as a *product*; the tail
carries the extra constraint `n > x`, which under `n = k·r` is the constraint `k·r > x` tying the
two factors together.  So the same bijection `n ↦ (s_z(n), r_z(n))` is run again, now onto a
filtered product.

Stated relatively, cut at `z` inside the `y`-rough numbers, for the same reason
`RMF.sum_blockSmooth_mul_sum_rough` is: both (T0) and (T1) are this one reindexing, the former at
`y = 0`. -/

/-- **The block tail, reindexed, for any weight multiplicative on coprime arguments.**
`∑_{n ∈ T_{y,z}(x)} g(n) = ∑_k g(k)·∑_{r ≤ x z-rough, kr > x} g(r)`, with `k` running over the
squarefree `z`-smooth `y`-rough numbers and `r` over the squarefree `z`-rough ones: the bijection
`n ↦ (s_z(n), r_z(n))` onto the filtered product, the two parts being coprime.  `hyz` makes a
`z`-rough `r` `y`-rough, so that `k·r` is `y`-rough; nothing is assumed about `x`. -/
theorem sum_blockTruncationTailIndex_eq {M : Type*} [CommSemiring M] {g : ℕ → M}
    (hg : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) {y z : ℕ} (hyz : y ≤ z) (x : ℝ) :
    ∑ n ∈ {n ∈ Finset.Icc 1 (primorial z * ⌊x⌋₊) |
        ⌊x⌋₊ < n ∧ IsRough y n ∧ roughPart z n ≤ ⌊x⌋₊ ∧ Squarefree n}, g n
      = ∑ k ∈ {k ∈ Finset.Icc 1 (primorial z) |
            k ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y k ∧ Squarefree k},
          g k * ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ |
            (IsRough z r ∧ Squarefree r) ∧ ⌊x⌋₊ < k * r}, g r := by
  -- the one use of `y ≤ z`: a `z`-rough number is `y`-rough
  have hmono : ∀ n : ℕ, IsRough z n → IsRough y n := fun n hn =>
    isRough_iff.2 fun p hp hpd => lt_of_le_of_lt hyz (isRough_iff.1 hn p hp hpd)
  have hstep : ∀ k : ℕ, g k * ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ |
        (IsRough z r ∧ Squarefree r) ∧ ⌊x⌋₊ < k * r}, g r
      = ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r ∧ Squarefree r},
          if ⌊x⌋₊ < k * r then g k * g r else 0 := fun _ => by
    rw [Finset.mul_sum, ← Finset.filter_filter, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun k _ => hstep k, ← Finset.sum_product', ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun n => (smoothPart z n, roughPart z n)) (fun p => p.1 * p.2)
    (fun n hn => ?_) (fun p hp => ?_) (fun n hn => ?_) (fun p hp => ?_) fun n hn => ?_
  · -- the two parts of a tail element land in the two ranges, with product above `x`
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, -⟩, hnx, hny, hnr, hnsf⟩ := hn
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn1
    have hssf : Squarefree (smoothPart z n) := hnsf.squarefree_of_dvd (smoothPart_dvd z hn0)
    have hrsf : Squarefree (roughPart z n) := hnsf.squarefree_of_dvd (roughPart_dvd z hn0)
    have hprod : smoothPart z n * roughPart z n = n := by
      rw [mul_comm]; exact roughPart_mul_smoothPart z hn0
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨⟨smoothPart_pos z n, Nat.le_of_dvd (primorial_pos z)
          (dvd_primorial_of_squarefree_of_mem_smoothNumbers hssf
            (smoothPart_mem_smoothNumbers z n))⟩, smoothPart_mem_smoothNumbers z n,
          hny.of_dvd (smoothPart_dvd z hn0), hssf⟩,
        ⟨roughPart_pos z n, hnr⟩, isRough_roughPart z n, hrsf⟩, by rw [hprod]; exact hnx⟩
  · -- and conversely the product of a block-smooth and a `z`-rough factor is a tail element
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨⟨hk1, hk2⟩, hks, hkro, hksf⟩, ⟨hr1, hr2⟩, hrr, hrsf⟩, hpx⟩ := hp
    have hcop : Nat.Coprime p.2 p.1 := hrr.coprime_of_mem_smoothNumbers hks
    obtain ⟨hrp, -⟩ := roughPart_smoothPart_mul hrr hks hr1
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)),
      Nat.mul_le_mul hk2 hr2⟩, hpx, isRough_mul_iff.2 ⟨hkro, hmono p.2 hrr⟩, ?_,
      Nat.squarefree_mul_iff.2 ⟨hcop.symm, hksf, hrsf⟩⟩
    rw [mul_comm p.1 p.2, hrp]
    exact hr2
  · -- a tail element is the product of its two parts
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    change smoothPart z n * roughPart z n = n
    rw [mul_comm]
    exact roughPart_mul_smoothPart z (Nat.one_le_iff_ne_zero.1 hn.1.1)
  · -- and the two parts of a product are its two factors
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨-, hks, -⟩, ⟨hr1, -⟩, hrr, -⟩, -⟩ := hp
    obtain ⟨hrp, hsp⟩ := roughPart_smoothPart_mul hrr hks hr1
    rw [mul_comm p.1 p.2, hrp, hsp]
  · -- the weight splits along the factorisation, the two parts being coprime
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn.1.1
    have hprod : smoothPart z n * roughPart z n = n := by
      rw [mul_comm]; exact roughPart_mul_smoothPart z hn0
    have hcop : Nat.Coprime (smoothPart z n) (roughPart z n) :=
      ((isRough_roughPart z n).coprime_of_mem_smoothNumbers
        (smoothPart_mem_smoothNumbers z n)).symm
    change g n = g (smoothPart z n) * g (roughPart z n)
    rw [← hg _ _ hcop, hprod]

/-- **The block tail's harmonic sum, reindexed.**  `∑_{n ∈ T_{y,z}(x)} 1/n = ∑_k (1/k)·Σ(k)` with
`k` running over the squarefree `z`-smooth `y`-rough numbers and
`Σ(k) = ∑_{r ≤ x z-rough, kr > x} 1/r`: the weight `n ↦ 1/n` in
`RMF.sum_blockTruncationTailIndex_eq`. -/
theorem sum_inv_blockTruncationTailIndex {y z : ℕ} (hyz : y ≤ z) (x : ℝ) :
    ∑ n ∈ {n ∈ Finset.Icc 1 (primorial z * ⌊x⌋₊) |
        ⌊x⌋₊ < n ∧ IsRough y n ∧ roughPart z n ≤ ⌊x⌋₊ ∧ Squarefree n}, (n : ℝ)⁻¹
      = ∑ k ∈ {k ∈ Finset.Icc 1 (primorial z) |
            k ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y k ∧ Squarefree k},
          (k : ℝ)⁻¹ * ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ |
            (IsRough z r ∧ Squarefree r) ∧ ⌊x⌋₊ < k * r}, (r : ℝ)⁻¹ :=
  sum_blockTruncationTailIndex_eq (g := fun n : ℕ => (n : ℝ)⁻¹)
    (fun m n _ => by simp only [Nat.cast_mul, mul_inv]) hyz x

/-- **The tail's harmonic sum, reindexed.**  `∑_{n ∈ T_y(x)} 1/n = ∑_k (1/k)·Σ(k)` with `k` running
over the squarefree `y`-smooth numbers and `Σ(k) = ∑_{r ≤ x rough, kr > x} 1/r`.

The case `y = 0` of `RMF.sum_inv_blockTruncationTailIndex`, every integer being `0`-rough. -/
theorem sum_inv_truncationTailIndex (y : ℕ) (x : ℝ) :
    ∑ n ∈ {n ∈ Finset.Icc 1 (primorial y * ⌊x⌋₊) |
        ⌊x⌋₊ < n ∧ roughPart y n ≤ ⌊x⌋₊ ∧ Squarefree n}, (n : ℝ)⁻¹
      = ∑ k ∈ {k ∈ Finset.Icc 1 (primorial y) | k ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree k},
          (k : ℝ)⁻¹ * ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ |
            (IsRough y r ∧ Squarefree r) ∧ ⌊x⌋₊ < k * r}, (r : ℝ)⁻¹ := by
  have h0 : ∀ n : ℕ, IsRough 0 n := fun n => isRough_iff.2 fun p hp _ => hp.pos
  have hA : {n ∈ Finset.Icc 1 (primorial y * ⌊x⌋₊) |
        ⌊x⌋₊ < n ∧ IsRough 0 n ∧ roughPart y n ≤ ⌊x⌋₊ ∧ Squarefree n}
      = {n ∈ Finset.Icc 1 (primorial y * ⌊x⌋₊) |
        ⌊x⌋₊ < n ∧ roughPart y n ≤ ⌊x⌋₊ ∧ Squarefree n} :=
    Finset.filter_congr fun n _ => by simp [h0 n]
  have hB : {k ∈ Finset.Icc 1 (primorial y) |
        k ∈ Nat.smoothNumbers (y + 1) ∧ IsRough 0 k ∧ Squarefree k}
      = {k ∈ Finset.Icc 1 (primorial y) | k ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree k} :=
    Finset.filter_congr fun k _ => by simp [h0 k]
  have key := sum_inv_blockTruncationTailIndex (y := 0) (z := y) (Nat.zero_le y) x
  rw [hA, hB] at key
  exact key

/-! ### The harmonic mass of an interval, against the logarithm

The integral comparison gives `∑_{a<n≤b} 1/n ≤ log(b/a)`, and `log y · log(1 + W/y)` is bounded
**uniformly in `y`**: the maximum sits at `y ≈ √W` and is quadratic in `log W`, where counting the
window's elements (`RMF.sum_inv_Ioc_le`) would give a bound linear in `W`. -/

/-- **`∑_{a < n ≤ b} 1/n ≤ log b − log a`**, for `1 ≤ a ≤ b`.

Telescoped from `1/(m+1) ≤ log(m+1) − log m`, which is `log(m/(m+1)) ≤ m/(m+1) − 1`. -/
theorem sum_inv_Ioc_le_log_sub {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, (n : ℝ)⁻¹ ≤ Real.log b - Real.log a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
      have hm1 : 1 ≤ m := le_trans ha hm
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
      have hstep : (((m + 1 : ℕ) : ℝ))⁻¹ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log m := by
        rw [hcast]
        have h := Real.log_le_sub_one_of_pos (x := (m : ℝ) / ((m : ℝ) + 1)) (by positivity)
        rw [Real.log_div (ne_of_gt hm0) (by positivity)] at h
        have hid : (m : ℝ) / ((m : ℝ) + 1) - 1 = -((m : ℝ) + 1)⁻¹ := by
          field_simp
          ring
        rw [hid] at h
        linarith
      rw [Finset.sum_Ioc_succ_top hm]
      linarith

/-- **The window's harmonic mass, uniformly in `y`.**  For `2 ≤ y` and `2 ≤ W`,
`log y · (log(y + W) − log y) ≤ M + M²/4`,   `M = log 2 + log(1 + W)`.

Below `y = 1 + W` the second factor is at most `M − log y` and `u(M − u) ≤ M²/4`; above it
`log(1 + W/y) ≤ W/y` and `log y / y` decreases past `e` (`Real.log_div_self_antitoneOn`).  So a
sieve threshold `H₀` enters as `(log H₀)²/4` rather than as `H₀`. -/
theorem log_mul_log_add_sub_le {y W : ℝ} (hy : 2 ≤ y) (hW : 2 ≤ W) :
    Real.log y * (Real.log (y + W) - Real.log y)
      ≤ (Real.log 2 + Real.log (1 + W)) + (Real.log 2 + Real.log (1 + W)) ^ 2 / 4 := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hW0 : (0 : ℝ) < 1 + W := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogW : (0 : ℝ) ≤ Real.log (1 + W) := Real.log_nonneg (by linarith)
  have hM0 : (0 : ℝ) < Real.log 2 + Real.log (1 + W) := by linarith
  have hu0 : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  rcases le_or_gt y (1 + W) with hcase | hcase
  · have h1 : Real.log (y + W) ≤ Real.log 2 + Real.log (1 + W) := by
      rw [← Real.log_mul (by norm_num) (ne_of_gt hW0)]
      exact Real.log_le_log (by linarith) (by linarith)
    have hstep : Real.log y * (Real.log (y + W) - Real.log y)
        ≤ Real.log y * ((Real.log 2 + Real.log (1 + W)) - Real.log y) :=
      mul_le_mul_of_nonneg_left (by linarith) hu0.le
    nlinarith [hstep, sq_nonneg ((Real.log 2 + Real.log (1 + W)) / 2 - Real.log y), hM0]
  · have he3 : Real.exp 1 ≤ 1 + W := by
      have := Real.exp_one_lt_d9
      linarith
    have hey : Real.exp 1 ≤ y := le_trans he3 (le_of_lt hcase)
    have hanti : Real.log y / y ≤ Real.log (1 + W) / (1 + W) :=
      Real.log_div_self_antitoneOn (Set.mem_Ici.2 he3) (Set.mem_Ici.2 hey) (le_of_lt hcase)
    have hshort : Real.log (y + W) - Real.log y ≤ W / y := by
      have h := Real.log_le_sub_one_of_pos (x := (y + W) / y) (by positivity)
      rw [Real.log_div (by linarith) (ne_of_gt hy0)] at h
      have hid : (y + W) / y - 1 = W / y := by
        field_simp
        ring
      rw [hid] at h
      linarith
    have hmul : Real.log y * (Real.log (y + W) - Real.log y) ≤ Real.log y * (W / y) :=
      mul_le_mul_of_nonneg_left hshort hu0.le
    have hrw : Real.log y * (W / y) = W * (Real.log y / y) := by field_simp
    have h3 : W * (Real.log y / y) ≤ W * (Real.log (1 + W) / (1 + W)) :=
      mul_le_mul_of_nonneg_left hanti (by linarith)
    have hfrac : W / (1 + W) ≤ 1 := by
      rw [div_le_one hW0]
      linarith
    have h4 : W * (Real.log (1 + W) / (1 + W)) ≤ Real.log (1 + W) := by
      have hid : W * (Real.log (1 + W) / (1 + W)) = (W / (1 + W)) * Real.log (1 + W) := by
        field_simp
      rw [hid]
      nlinarith [hlogW, hfrac]
    nlinarith [hmul, hrw.le, hrw.ge, h3, h4, hM0, sq_nonneg (Real.log 2 + Real.log (1 + W))]

/-- **The rough integers forced above `x/k`.**  `∑_{r ≤ x rough, kr > x} 1/r ≤ 1_{k>x} +
K·(1 + log k)/log y` for `2 ≤ y ≤ x` and `k ≥ 1`, `K` absolute, over any `Finset` of such `r`.

The witness is `Cs + M + M²/4`, `M = log 2 + log(1 + ⌈H⌉)`, `H = max{H₀, 2}`, with `Cs` and `H₀`
those of `RMF.exists_sum_inv_rough_Ioc_le`: the window `(y, y + ⌈H⌉]` is integrated
(`RMF.log_mul_log_add_sub_le`), not counted. -/
theorem exists_sum_inv_rough_gt_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (y : ℕ) (x : ℝ) (k : ℕ) (s : Finset ℕ), 2 ≤ y → (y : ℝ) ≤ x → 1 ≤ k →
      (∀ r ∈ s, r ≤ ⌊x⌋₊ ∧ IsRough y r ∧ ⌊x⌋₊ < k * r) →
        ∑ r ∈ s, (r : ℝ)⁻¹
          ≤ (if ⌊x⌋₊ < k then 1 else 0) + K * (1 + Real.log k) / Real.log y := by
  classical
  obtain ⟨Cs, H₀, hCs, hH₀, hrough⟩ := exists_sum_inv_rough_Ioc_le
  -- the threshold is enlarged to `≥ 2` so that the window bound has a single regime
  set H : ℝ := max H₀ 2 with hH_def
  have hH2 : (2 : ℝ) ≤ H := le_max_right _ _
  have hH0H : H₀ ≤ H := le_max_left _ _
  have hHpos : (0 : ℝ) < H := by linarith
  have hW2 : (2 : ℝ) ≤ ((⌈H⌉₊ : ℕ) : ℝ) := le_trans hH2 (Nat.le_ceil H)
  set N : ℝ := (Real.log 2 + Real.log (1 + ((⌈H⌉₊ : ℕ) : ℝ)))
    + (Real.log 2 + Real.log (1 + ((⌈H⌉₊ : ℕ) : ℝ))) ^ 2 / 4 with hN_def
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogW : (0 : ℝ) ≤ Real.log (1 + ((⌈H⌉₊ : ℕ) : ℝ)) := Real.log_nonneg (by linarith)
  have hN0 : (0 : ℝ) < N := by
    rw [hN_def]
    nlinarith [sq_nonneg (Real.log 2 + Real.log (1 + ((⌈H⌉₊ : ℕ) : ℝ)))]
  refine ⟨Cs + N, by linarith, ?_⟩
  intro y x k s hy hyx hk1 hmem
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk0
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hlogk : (0 : ℝ) ≤ Real.log k := Real.log_nonneg hk1R
  -- the two endpoints, kept abstract so that only their seven properties are used below
  obtain ⟨R, R', hR0, hyR, hH0R, hRR', hkR, hlowR, hxR'⟩ :
      ∃ R R' : ℝ, 0 < R ∧ (y : ℝ) ≤ R ∧ H ≤ R ∧ R ≤ R' ∧ R' ≤ (k : ℝ) * R
        ∧ (∀ t : ℝ, t ≤ R → x / k < t → t ≤ (y : ℝ) + H) ∧ x ≤ R' := by
    refine ⟨max ((y : ℝ) + H) (x / k), max x ((y : ℝ) + H), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · exact le_trans (by linarith) (le_max_left _ _)
    · exact le_trans (by linarith) (le_max_left _ _)
    · exact max_le (le_max_right _ _) (le_trans (div_le_self hx0.le hk1R) (le_max_left _ _))
    · refine max_le ?_ ?_
      · calc x = (k : ℝ) * (x / k) := by field_simp
          _ ≤ (k : ℝ) * max ((y : ℝ) + H) (x / k) :=
              mul_le_mul_of_nonneg_left (le_max_right _ _) hk0.le
      · calc (y : ℝ) + H ≤ max ((y : ℝ) + H) (x / k) := le_max_left _ _
          _ = 1 * max ((y : ℝ) + H) (x / k) := (one_mul _).symm
          _ ≤ (k : ℝ) * max ((y : ℝ) + H) (x / k) :=
              mul_le_mul_of_nonneg_right hk1R (le_trans (by linarith) (le_max_left _ _))
    · intro t htR htx
      rcases max_choice ((y : ℝ) + H) (x / k) with h | h
      · rwa [h] at htR
      · rw [h] at htR; linarith
    · exact le_max_left _ _
  -- the discarded window `(y, y + ⌈H⌉]`, integrated rather than counted
  have hwin : ∑ r ∈ Finset.Ioc y (y + ⌈H⌉₊), (r : ℝ)⁻¹
      ≤ Real.log ((y : ℝ) + ((⌈H⌉₊ : ℕ) : ℝ)) - Real.log (y : ℝ) := by
    have h := sum_inv_Ioc_le_log_sub (a := y) (b := y + ⌈H⌉₊) (by omega) (by omega)
    have hcast : (((y + ⌈H⌉₊ : ℕ) : ℝ)) = (y : ℝ) + ((⌈H⌉₊ : ℕ) : ℝ) := by push_cast; ring
    rwa [hcast] at h
  have hstep2 : Real.log ((y : ℝ) + ((⌈H⌉₊ : ℕ) : ℝ)) - Real.log (y : ℝ)
      ≤ N * (1 + Real.log k) / Real.log y := by
    have hkey := log_mul_log_add_sub_le (y := (y : ℝ)) (W := ((⌈H⌉₊ : ℕ) : ℝ)) hy2 hW2
    rw [← hN_def] at hkey
    rw [le_div_iff₀ hlogy]
    nlinarith [hkey, hN0, hlogk, hlogy]
  -- below the lower endpoint only `r = 1` and the window survive
  have hmemlow : ∀ r ∈ ({r ∈ s | r ≤ ⌊R⌋₊} : Finset ℕ),
      r = 1 ∨ r ∈ Finset.Ioc y (y + ⌈H⌉₊) := by
    intro r hr
    obtain ⟨hrs, hrR⟩ := Finset.mem_filter.1 hr
    obtain ⟨-, hroughr, hkr⟩ := hmem r hrs
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hkr
    rcases eq_or_ne r 1 with h1 | h1
    · exact Or.inl h1
    · refine Or.inr (Finset.mem_Ioc.2 ⟨hroughr.lt_of_one_lt (by omega), ?_⟩)
      have hkr' : ⌊x⌋₊ + 1 ≤ r * k := by rwa [Nat.mul_comm] at hkr
      have h6 : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ (r : ℝ) * (k : ℝ) := by exact_mod_cast hkr'
      have hxk : x / (k : ℝ) < (r : ℝ) := by
        rw [div_lt_iff₀ hk0]
        linarith [Nat.lt_floor_add_one x]
      have hrRR : (r : ℝ) ≤ R := le_trans (Nat.cast_le.2 hrR) (Nat.floor_le hR0.le)
      have hcast : (r : ℝ) ≤ ((y + ⌈H⌉₊ : ℕ) : ℝ) := by
        push_cast
        linarith [Nat.le_ceil H, hlowR r hrRR hxk]
      exact_mod_cast hcast
  have hlowbd : ∑ r ∈ ({r ∈ s | r ≤ ⌊R⌋₊} : Finset ℕ), (r : ℝ)⁻¹
      ≤ (if ⌊x⌋₊ < k then 1 else 0) + N * (1 + Real.log k) / Real.log y := by
    by_cases hkx : ⌊x⌋₊ < k
    · rw [if_pos hkx]
      have h1notin : (1 : ℕ) ∉ Finset.Ioc y (y + ⌈H⌉₊) := by
        simp only [Finset.mem_Ioc]
        omega
      have hsub : ({r ∈ s | r ≤ ⌊R⌋₊} : Finset ℕ) ⊆ insert 1 (Finset.Ioc y (y + ⌈H⌉₊)) := by
        intro r hr
        rcases hmemlow r hr with h | h
        · exact Finset.mem_insert.2 (Or.inl h)
        · exact Finset.mem_insert.2 (Or.inr h)
      calc ∑ r ∈ ({r ∈ s | r ≤ ⌊R⌋₊} : Finset ℕ), (r : ℝ)⁻¹
          ≤ ∑ r ∈ insert 1 (Finset.Ioc y (y + ⌈H⌉₊)), (r : ℝ)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
        _ = 1 + ∑ r ∈ Finset.Ioc y (y + ⌈H⌉₊), (r : ℝ)⁻¹ := by
            rw [Finset.sum_insert h1notin]
            norm_num
        _ ≤ 1 + N * (1 + Real.log k) / Real.log y := by linarith
    · rw [if_neg hkx, zero_add]
      have hsub : ({r ∈ s | r ≤ ⌊R⌋₊} : Finset ℕ) ⊆ Finset.Ioc y (y + ⌈H⌉₊) := by
        intro r hr
        rcases hmemlow r hr with h | h
        · exact absurd (by simpa [h, Nat.mul_one] using (hmem r (Finset.mem_filter.1 hr).1).2.2)
            hkx
        · exact h
      calc ∑ r ∈ ({r ∈ s | r ≤ ⌊R⌋₊} : Finset ℕ), (r : ℝ)⁻¹
          ≤ ∑ r ∈ Finset.Ioc y (y + ⌈H⌉₊), (r : ℝ)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
        _ ≤ Real.log ((y : ℝ) + ((⌈H⌉₊ : ℕ) : ℝ)) - Real.log (y : ℝ) := hwin
        _ ≤ N * (1 + Real.log k) / Real.log y := hstep2
  -- above the lower endpoint, `RMF.exists_sum_inv_rough_Ioc_le` applies verbatim
  have hhighbd : ∑ r ∈ ({r ∈ s | ¬ r ≤ ⌊R⌋₊} : Finset ℕ), (r : ℝ)⁻¹
      ≤ Cs * (1 + Real.log k) / Real.log y := by
    have hsub : ({r ∈ s | ¬ r ≤ ⌊R⌋₊} : Finset ℕ)
        ⊆ {n ∈ Finset.Ioc ⌊R⌋₊ ⌊R'⌋₊ | IsRough y n} := by
      intro r hr
      obtain ⟨hrs, hrR⟩ := Finset.mem_filter.1 hr
      obtain ⟨hrx, hroughr, -⟩ := hmem r hrs
      exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2
        ⟨by omega, le_trans hrx (Nat.floor_le_floor hxR')⟩, hroughr⟩
    calc ∑ r ∈ ({r ∈ s | ¬ r ≤ ⌊R⌋₊} : Finset ℕ), (r : ℝ)⁻¹
        ≤ ∑ r ∈ {n ∈ Finset.Ioc ⌊R⌋₊ ⌊R'⌋₊ | IsRough y n}, (r : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
      _ ≤ Cs * (1 + Real.log (R' / R)) / Real.log y :=
          hrough y R R' hy hyR (le_trans hH0H hH0R) hRR'
      _ ≤ Cs * (1 + Real.log k) / Real.log y := by
          refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hCs.le) hlogy.le
          have h : Real.log (R' / R) ≤ Real.log k := by
            refine Real.log_le_log (div_pos (lt_of_lt_of_le hR0 hRR') hR0) ?_
            rw [div_le_iff₀ hR0]
            exact hkR
          linarith
  have hsplit : ∑ r ∈ s, (r : ℝ)⁻¹
      = (∑ r ∈ ({r ∈ s | r ≤ ⌊R⌋₊} : Finset ℕ), (r : ℝ)⁻¹)
        + ∑ r ∈ ({r ∈ s | ¬ r ≤ ⌊R⌋₊} : Finset ℕ), (r : ℝ)⁻¹ :=
    (Finset.sum_filter_add_sum_filter_not s _ _).symm
  have hid : (Cs + N) * (1 + Real.log k) / Real.log y
      = Cs * (1 + Real.log k) / Real.log y + N * (1 + Real.log k) / Real.log y := by
    ring
  rw [hsplit, hid]
  linarith

/-! ### (T0)

Rankin's trick gives `∑_{m>x} 1/m ≪ (log y)^e·e^{-U}`, `U = log x/log y`, which is worse than
`log y` when `U` is **bounded**, and the uniform-in-`q` upper bound runs `y` up to `x^{1/e}`,
where `U = e`.  So `m > x` is dropped altogether: `∑_{m>x} 1/m ≤ ∑_m 1/m = ∏_{p≤y}(1+1/p) ≪ log y`.
The same trade as (T1)'s, one range up. -/

/-- **(T0).**  `E|T_y(x)|² ≤ C·log y` with `C` absolute, for `2 ≤ y ≤ x` — **no condition
relating `x` to `y` beyond `y ≤ x`**, and in particular nothing that degenerates as
`log x / log y → 1`. -/
theorem exists_integral_normSq_truncationTail_le_log :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ →
      ∀ (y : ℕ) (x : ℝ), 2 ≤ y → (y : ℝ) ≤ x →
        (∫ ω, ‖truncationTail (fun ω => squarefreeExtension fun p => X p ω) y x ω‖ ^ 2 ∂μ)
          ≤ C * Real.log y := by
  obtain ⟨K, hK, hsig⟩ := exists_sum_inv_rough_gt_le
  obtain ⟨Cs, hCs, hsmoothinv⟩ := exists_sum_smoothSquarefree_inv_le
  obtain ⟨Cm, hCm, hsmooth⟩ := exists_sum_smoothSquarefree_one_add_log_div_le
  refine ⟨Cs + K * Cm, add_pos hCs (mul_pos hK hCm), ?_⟩
  intro Ω _ X μ hX y x hy hyx
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlogyne : Real.log y ≠ 0 := ne_of_gt hlogy
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  -- step 1: orthogonality
  have hmoment :
      (∫ ω, ‖truncationTail (fun ω => squarefreeExtension fun p => X p ω) y x ω‖ ^ 2 ∂μ)
        = ∑ n ∈ {n ∈ Finset.Icc 1 (primorial y * ⌊x⌋₊) |
            ⌊x⌋₊ < n ∧ roughPart y n ≤ ⌊x⌋₊ ∧ Squarefree n}, (n : ℝ)⁻¹ :=
    integral_normSq_sum_div_sqrt_of_squarefree hRa
      (fun n hn => Nat.one_le_iff_ne_zero.1 (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1)
      (fun n hn => (Finset.mem_filter.1 hn).2.2.2)
  rw [hmoment, sum_inv_truncationTailIndex y x]
  -- step 2: the pointwise bound on the inner sum
  have hterm : ∀ k ∈ ({k ∈ Finset.Icc 1 (primorial y) |
      k ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree k} : Finset ℕ),
      (k : ℝ)⁻¹ * ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ |
          (IsRough y r ∧ Squarefree r) ∧ ⌊x⌋₊ < k * r}, (r : ℝ)⁻¹
        ≤ (if ⌊x⌋₊ < k then (k : ℝ)⁻¹ else 0) + K / Real.log y * ((1 + Real.log k) / k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk0
    have hb := hsig y x k {r ∈ Finset.Icc 1 ⌊x⌋₊ |
      (IsRough y r ∧ Squarefree r) ∧ ⌊x⌋₊ < k * r} hy hyx hk1 fun r hr => by
        obtain ⟨hr1, hr2⟩ := Finset.mem_filter.1 hr
        exact ⟨(Finset.mem_Icc.1 hr1).2, hr2.1.1, hr2.2⟩
    have hmul := mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.2 hk0))
    have hrw : (k : ℝ)⁻¹ * ((if ⌊x⌋₊ < k then (1 : ℝ) else 0)
          + K * (1 + Real.log k) / Real.log y)
        = (if ⌊x⌋₊ < k then (k : ℝ)⁻¹ else 0) + K / Real.log y * ((1 + Real.log k) / k) := by
      rw [mul_add, mul_ite, mul_one, mul_zero]
      congr 1
      field_simp
      try ring
    rw [← hrw]
    exact hmul
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum]
  -- step 3: the whole smooth harmonic mass, in place of Rankin
  have hfirst : ∑ k ∈ ({k ∈ ({k ∈ Finset.Icc 1 (primorial y) |
        k ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree k} : Finset ℕ) | ⌊x⌋₊ < k} : Finset ℕ),
        (k : ℝ)⁻¹
      ≤ Cs * Real.log y :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun i _ _ => by positivity) (hsmoothinv y hy)
  -- step 4: the log-weighted smooth sum
  have hsecond : K / Real.log y * ∑ k ∈ ({k ∈ Finset.Icc 1 (primorial y) |
        k ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree k} : Finset ℕ), (1 + Real.log k) / k
      ≤ K * Cm * Real.log y := by
    refine le_trans (mul_le_mul_of_nonneg_left (hsmooth y hy) (le_of_lt (div_pos hK hlogy)))
      (le_of_eq ?_)
    field_simp
    try ring
  have hexp : (Cs + K * Cm) * Real.log y = Cs * Real.log y + K * Cm * Real.log y := by ring
  rw [hexp]
  linarith

/-! ### (T1), the block instance

The same argument for the block tail `T_{y,z}(x)`, with `m` running over the squarefrees composed
of primes in `(y, z]`.  Here the bound does **not depend on `y` or `z`**: the layered sum uses it
`K ≍ log log x` times.  Mertens' block form gives `∑_{y<p≤z} 1/p ≤ log Λ + 1.86` for
`log z ≤ Λ·log y` (`RMF.sum_inv_primesIco_le`), hence `∑_m 1/m ≤ ∏_{y<p≤z}(1+1/p) ≪ 1`
(`RMF.sum_blockSquarefree_inv_le`) and `∑_m (1+log m)/m ≪ log z`
(`RMF.sum_blockSquarefree_one_add_log_div_le`); neither half needs Rankin.

The hypothesis is `log z ≤ Λ·log y` rather than `z = y^e`: it avoids a `⌊y^e⌋₊`, and the layers
are integers, so at `y_k = ⌊x^{e^{-(k-1)}}⌋₊` the two floors cost `log(t/(t-1)) ≤ log 2` each and
only `log y_k ≤ 2e·log y_{k+1}` survives.  `z ≤ x` is used once, to apply
`RMF.exists_sum_inv_rough_gt_le` at roughness `z`. -/

/-- **(T1), the block tail.**  `E|T_{y,z}(x)|² ≤ C` with `C` depending only on `Λ`, for
`2 ≤ y ≤ z ≤ x` and `log z ≤ Λ·log y`. -/
theorem exists_integral_normSq_blockTruncationTail_le {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ →
      ∀ (y z : ℕ), 2 ≤ y → y ≤ z → Real.log z ≤ Λ * Real.log y →
      ∀ x : ℝ, (z : ℝ) ≤ x →
        (∫ ω, ‖blockTruncationTail
            (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ 2 ∂μ) ≤ C := by
  obtain ⟨K, hK, hsig⟩ := exists_sum_inv_rough_gt_le
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (0 : ℝ) < 1 / Real.log 2 := div_pos one_pos hlog2
  have h20 : (0 : ℝ) < 1.86 := by norm_num
  have hlΛ : (0 : ℝ) ≤ Real.log Λ := Real.log_nonneg hΛ
  have hfac : (0 : ℝ) < 1 / Real.log 2 + (Real.log Λ + 1.86) := by linarith
  refine ⟨Real.exp (Real.log Λ + 1.86)
      + K * Real.exp (Real.log Λ + 1.86)
          * (1 / Real.log 2 + (Real.log Λ + 1.86)),
    add_pos (Real.exp_pos _) (mul_pos (mul_pos hK (Real.exp_pos _)) hfac), ?_⟩
  intro Ω _ X μ hX y z hy hyz hlog x hzx
  have hz : 2 ≤ z := le_trans hy hyz
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  have hlogzne : Real.log z ≠ 0 := ne_of_gt hlogz
  have hl2z : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) hz2
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  -- step 1: orthogonality
  have hmoment :
      (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ 2 ∂μ)
        = ∑ n ∈ {n ∈ Finset.Icc 1 (primorial z * ⌊x⌋₊) |
            ⌊x⌋₊ < n ∧ IsRough y n ∧ roughPart z n ≤ ⌊x⌋₊ ∧ Squarefree n}, (n : ℝ)⁻¹ :=
    integral_normSq_sum_div_sqrt_of_squarefree hRa
      (fun n hn => Nat.one_le_iff_ne_zero.1 (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1)
      (fun n hn => (Finset.mem_filter.1 hn).2.2.2.2)
  rw [hmoment, sum_inv_blockTruncationTailIndex hyz x]
  -- step 2: the pointwise bound on the inner sum, at roughness `z`
  have hterm : ∀ k ∈ ({k ∈ Finset.Icc 1 (primorial z) |
      k ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y k ∧ Squarefree k} : Finset ℕ),
      (k : ℝ)⁻¹ * ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ |
          (IsRough z r ∧ Squarefree r) ∧ ⌊x⌋₊ < k * r}, (r : ℝ)⁻¹
        ≤ (if ⌊x⌋₊ < k then (k : ℝ)⁻¹ else 0) + K / Real.log z * ((1 + Real.log k) / k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk0
    have hb := hsig z x k {r ∈ Finset.Icc 1 ⌊x⌋₊ |
      (IsRough z r ∧ Squarefree r) ∧ ⌊x⌋₊ < k * r} hz hzx hk1 fun r hr => by
        obtain ⟨hr1, hr2⟩ := Finset.mem_filter.1 hr
        exact ⟨(Finset.mem_Icc.1 hr1).2, hr2.1.1, hr2.2⟩
    have hmul := mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.2 hk0))
    have hrw : (k : ℝ)⁻¹ * ((if ⌊x⌋₊ < k then (1 : ℝ) else 0)
          + K * (1 + Real.log k) / Real.log z)
        = (if ⌊x⌋₊ < k then (k : ℝ)⁻¹ else 0) + K / Real.log z * ((1 + Real.log k) / k) := by
      rw [mul_add, mul_ite, mul_one, mul_zero]
      congr 1
      field_simp
      try ring
    rw [← hrw]
    exact hmul
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum]
  -- step 3: the block's harmonic mass, in place of Rankin
  have hfirst : ∑ k ∈ ({k ∈ ({k ∈ Finset.Icc 1 (primorial z) |
        k ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y k ∧ Squarefree k} : Finset ℕ) |
        ⌊x⌋₊ < k} : Finset ℕ), (k : ℝ)⁻¹
      ≤ Real.exp (Real.log Λ + 1.86) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun i _ _ => by positivity)
      (sum_blockSquarefree_inv_le hy hyz hΛ hlog)
  -- step 4: the block's log-weighted mass
  have hsecond : K / Real.log z * ∑ k ∈ ({k ∈ Finset.Icc 1 (primorial z) |
        k ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y k ∧ Squarefree k} : Finset ℕ),
        (1 + Real.log k) / k
      ≤ K * Real.exp (Real.log Λ + 1.86)
          * (1 / Real.log 2 + (Real.log Λ + 1.86)) := by
    have hstep := mul_le_mul_of_nonneg_left (sum_blockSquarefree_one_add_log_div_le hy hyz hΛ hlog)
      (le_of_lt (div_pos hK hlogz))
    have heq : K / Real.log z * (Real.exp (Real.log Λ + 1.86)
          * (1 + (Real.log Λ + 1.86) * Real.log z))
        = K * Real.exp (Real.log Λ + 1.86)
            * (1 / Real.log z + (Real.log Λ + 1.86)) := by
      field_simp
    have hinv : (1 : ℝ) / Real.log z ≤ 1 / Real.log 2 :=
      div_le_div_of_nonneg_left zero_le_one hlog2 hl2z
    have hmono : K * Real.exp (Real.log Λ + 1.86)
          * (1 / Real.log z + (Real.log Λ + 1.86))
        ≤ K * Real.exp (Real.log Λ + 1.86)
          * (1 / Real.log 2 + (Real.log Λ + 1.86)) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg hK.le (Real.exp_pos _).le)
    rw [heq] at hstep
    linarith
  linarith

end RMF
