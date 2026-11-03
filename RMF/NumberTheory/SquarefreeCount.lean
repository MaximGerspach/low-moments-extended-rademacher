/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Counting squarefree integers

The number of squarefree integers up to `N` is `6/π² · N + O(√N)`.  This file builds that
estimate from the Möbius function; it depends on nothing else in this development and could
be read (or upstreamed) on its own.

The main results are `RMF.abs_squarefreeCount_sub_le`, the estimate
`|Q N - 6/π² · N| ≤ 3 √N`, and `RMF.tsum_moebius_div_sq`, the value `∑ μ d / d ² = 6/π²`.

The route, in four steps:

1. The squarefree indicator is a divisor sum, `μ n ^ 2 = ∑_{d ^ 2 ∣ n} μ d`
   (`sum_moebius_of_sq_dvd`).  Writing `n = b ^ 2 * a` with `a` squarefree, the `d` with
   `d ^ 2 ∣ n` are exactly the divisors of `b`, so the sum is `∑_{d ∣ b} μ d`, which
   vanishes unless `b = 1` — that is, unless `n` is squarefree.
2. Summing over `n ≤ N` and exchanging the order gives
   `Q N = ∑_{d ≤ √N} μ d ⌊N / d²⌋` (`squarefreeCount_eq_sum`).
3. Replacing `⌊N / d²⌋` by `N / d²` costs at most one per term, so at most `√N` in total
   (`abs_squarefreeCount_sub_mul_sum_le`); extending the sum to infinity costs at most
   `2√N` (`abs_tsum_sub_sum_le`).
4. The resulting series is `1 / ζ 2 = 6/π²`, from Mathlib's `L ζ s · L μ s = 1` at `s = 2`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta Real

namespace RMF

/-- `∑_{d ∣ n} μ d` is `1` at `n = 1` and `0` elsewhere. -/
lemma sum_divisors_moebius (n : ℕ) : ∑ d ∈ n.divisors, μ d = if n = 1 then 1 else 0 := by
  have h : ((μ : ArithmeticFunction ℤ) * ζ) n = (1 : ArithmeticFunction ℤ) n := by
    rw [moebius_mul_coe_zeta]
  rwa [coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h

/-- With `a` squarefree, `d ^ 2` divides `b ^ 2 * a` exactly when `d` divides `b`: the square
part of `b ^ 2 * a` is `b ^ 2`. -/
lemma sq_dvd_sq_mul_iff {a b d : ℕ} (ha : Squarefree a) (hb : b ≠ 0) (hd : d ≠ 0) :
    d ^ 2 ∣ b ^ 2 * a ↔ d ∣ b := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have ha1 : ∀ p, a.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one ha0).1 ha
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd) (by positivity),
    ← Nat.factorization_le_iff_dvd hd hb, Nat.factorization_mul (pow_ne_zero 2 hb) ha0,
    Nat.factorization_pow, Nat.factorization_pow, Finsupp.le_def, Finsupp.le_def]
  constructor
  · intro h p
    have h1 := h p
    have h2 := ha1 p
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply, smul_eq_mul] at h1
    omega
  · intro h p
    have h1 := h p
    have h2 := ha1 p
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply, smul_eq_mul]
    omega

/-- **The squarefree indicator is a divisor sum.**  Summing `μ` over the `d` with `d ^ 2 ∣ n`
detects squarefreeness of `n`. -/
theorem sum_moebius_of_sq_dvd {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), μ d = if Squarefree n then 1 else 0 := by
  obtain ⟨a, b, rfl, ha⟩ := Nat.sq_mul_squarefree n
  have hb : b ≠ 0 := by rintro rfl; simp at hn
  have hset : (b ^ 2 * a).divisors.filter (fun d => d ^ 2 ∣ b ^ 2 * a) = b.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, -⟩, hsq⟩
      have hd : d ≠ 0 := by rintro rfl; simp at hdn; omega
      exact ⟨(sq_dvd_sq_mul_iff ha hb hd).1 hsq, hb⟩
    · rintro ⟨hdb, -⟩
      have hd : d ≠ 0 := by rintro rfl; exact hb (zero_dvd_iff.1 hdb)
      have hsq : d ^ 2 ∣ b ^ 2 * a := (sq_dvd_sq_mul_iff ha hb hd).2 hdb
      exact ⟨⟨(dvd_pow_self d two_ne_zero).trans hsq, hn⟩, hsq⟩
  rw [hset, sum_divisors_moebius]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · subst h; simpa using ha
  · exact Nat.isUnit_iff.1 (h b ⟨a, by ring⟩)

/-- The counting function of the squarefree integers, `Q N = #{n ≤ N : n squarefree}`. -/
def squarefreeCount (N : ℕ) : ℕ := #{n ∈ Finset.Icc 1 N | Squarefree n}

/-- `|μ d| ≤ 1`. -/
lemma abs_moebius_le_one (d : ℕ) : |(μ d : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

/-- The index set of Step 2 is an interval: `d ² ≤ N` and `d ≥ 1` say exactly `d ≤ ⌊√N⌋`. -/
lemma filter_sq_le_eq_Icc (N : ℕ) :
    (Finset.Icc 1 N).filter (fun d => d ^ 2 ≤ N) = Finset.Icc 1 (Nat.sqrt N) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, Nat.le_sqrt'.2 h2⟩
  · rintro ⟨h1, h2⟩
    have hd2 : d ^ 2 ≤ N := Nat.le_sqrt'.1 h2
    exact ⟨⟨h1, (Nat.le_self_pow two_ne_zero d).trans hd2⟩, hd2⟩

/-- Each term of the Möbius series is dominated by `1 / d ²`. -/
lemma abs_moebius_div_sq_le (d : ℕ) : |(μ d : ℝ) / (d : ℝ) ^ 2| ≤ ((d : ℝ) ^ 2)⁻¹ := by
  rcases eq_or_ne d 0 with rfl | hd0
  · simp
  · have hd : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    rw [abs_div, abs_of_pos hd, inv_eq_one_div]
    exact div_le_div_of_nonneg_right (abs_moebius_le_one d) hd.le

/-- **Interchange of summation.**  Counting squarefree integers up to `N` by the divisor sum
of Step 1 and summing over `d` first gives `Q N = ∑_{d² ≤ N} μ d ⌊N / d²⌋`. -/
theorem squarefreeCount_eq_sum (N : ℕ) :
    (squarefreeCount N : ℤ)
      = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), μ d * (N / d ^ 2 : ℕ) := by
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by ext x; simp; omega
  have step1 : ∀ n ∈ Finset.Icc 1 N, (if Squarefree n then (1 : ℤ) else 0)
      = ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ^ 2 ∣ n), μ d := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.1 hn
    have hn0 : n ≠ 0 := by omega
    rw [← sum_moebius_of_sq_dvd hn0]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hdn, -⟩, hsq⟩
      have hd0 : d ≠ 0 := by rintro rfl; exact hn0 (zero_dvd_iff.1 hdn)
      exact ⟨⟨by omega, (Nat.le_of_dvd (by omega) hdn).trans hnN⟩, hsq⟩
    · rintro ⟨-, hsq⟩
      exact ⟨⟨(dvd_pow_self d two_ne_zero).trans hsq, hn0⟩, hsq⟩
  calc (squarefreeCount N : ℤ)
      = ∑ n ∈ Finset.Icc 1 N, if Squarefree n then (1 : ℤ) else 0 := by
        rw [squarefreeCount, Finset.sum_boole]
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ^ 2 ∣ n), μ d :=
        Finset.sum_congr rfl step1
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ _n ∈ (Finset.Icc 1 N).filter (fun n => d ^ 2 ∣ n), μ d := by
        refine Finset.sum_comm' ?_
        intro n d
        simp only [Finset.mem_filter, Finset.mem_Icc]
        tauto
    _ = ∑ d ∈ Finset.Icc 1 N, μ d * (N / d ^ 2 : ℕ) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm, hIcc, Nat.Ioc_filter_dvd_card_eq_div]
    _ = ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ^ 2 ≤ N), μ d * (N / d ^ 2 : ℕ) := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) fun d hd hd' => ?_).symm
        simp only [Finset.mem_filter, not_and, not_le] at hd'
        rw [Nat.div_eq_of_lt (hd' hd)]
        simp
    _ = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), μ d * (N / d ^ 2 : ℕ) := by
        rw [filter_sq_le_eq_Icc]

/-- The truncation error from replacing `⌊N / d²⌋` by `N / d²` is at most one per term, and
there are at most `√N` terms. -/
theorem abs_squarefreeCount_sub_mul_sum_le (N : ℕ) :
    |(squarefreeCount N : ℝ) - N * ∑ d ∈ Finset.Icc 1 (Nat.sqrt N),
        (μ d : ℝ) / (d : ℝ) ^ 2| ≤ Real.sqrt N := by
  set S := Finset.Icc 1 (Nat.sqrt N) with hS
  -- each term contributes at most one
  have hfloor : ∀ d : ℕ, |((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) ^ 2| ≤ 1 := by
    intro d
    have h1 : (⌊(N : ℝ) / (d : ℝ) ^ 2⌋₊ : ℝ) = ((N / d ^ 2 : ℕ) : ℝ) := by
      rw [← Nat.cast_pow, Nat.floor_div_natCast, Nat.floor_natCast]
    have hx : (0 : ℝ) ≤ (N : ℝ) / (d : ℝ) ^ 2 := by positivity
    rw [← h1, abs_le]
    constructor
    · have := Nat.sub_one_lt_floor ((N : ℝ) / (d : ℝ) ^ 2)
      linarith
    · have := Nat.floor_le hx
      linarith
  -- the difference is a sum of small terms
  have key : (squarefreeCount N : ℝ) - N * ∑ d ∈ S, (μ d : ℝ) / (d : ℝ) ^ 2
      = ∑ d ∈ S, (μ d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) ^ 2) := by
    have h2 : (squarefreeCount N : ℝ) = ∑ d ∈ S, (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) := by
      have h3 := congrArg (fun z : ℤ => (z : ℝ)) (squarefreeCount_eq_sum N)
      push_cast at h3
      exact h3
    rw [h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [key]
  calc |∑ d ∈ S, (μ d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) ^ 2)|
      ≤ ∑ d ∈ S, |(μ d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) ^ 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ S, (1 : ℝ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [abs_mul]
        exact mul_le_one₀ (abs_moebius_le_one d) (abs_nonneg _) (hfloor d)
    _ = (S.card : ℝ) := by simp
    _ ≤ Real.sqrt N := by
        rw [hS, Nat.card_Icc]
        simp only [Nat.add_sub_cancel]
        exact (Real.le_sqrt (by positivity) (by positivity)).2
          (by exact_mod_cast Nat.sqrt_le' N)

/-- The Möbius series `∑ μ d / d ²` is summable, being dominated by `∑ 1 / d ²`. -/
lemma summable_moebius_div_sq : Summable fun d : ℕ => (μ d : ℝ) / (d : ℝ) ^ 2 := by
  refine Summable.of_norm_bounded (g := fun d : ℕ => ((d : ℝ) ^ 2)⁻¹) ?_ ?_
  · simp
  · intro d
    rw [Real.norm_eq_abs]
    exact abs_moebius_div_sq_le d

/-- **The tail of the Möbius series is small.**  Truncating `∑ μ d / d ²` at `d ² ≤ N`
costs at most `2 / (⌊√N⌋ + 1)`. -/
theorem abs_tsum_sub_sum_le (N : ℕ) :
    |(∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2)
        - ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (μ d : ℝ) / (d : ℝ) ^ 2|
      ≤ 2 / (Nat.sqrt N + 1) := by
  set K := Nat.sqrt N with hK
  set f : ℕ → ℝ := fun d => (μ d : ℝ) / (d : ℝ) ^ 2 with hf
  have hbdd : ∀ d : ℕ, |f d| ≤ ((d : ℝ) ^ 2)⁻¹ := fun d => abs_moebius_div_sq_le d
  -- compare with the partial sums over `range n`
  have htend := summable_moebius_div_sq.hasSum.tendsto_sum_nat
  have h2 : Filter.Tendsto (fun n => |∑ d ∈ Finset.range n, f d - ∑ d ∈ Finset.Icc 1 K, f d|)
      Filter.atTop (nhds |(∑' d : ℕ, f d) - ∑ d ∈ Finset.Icc 1 K, f d|) :=
    (htend.sub_const _).abs
  refine le_of_tendsto h2 ?_
  filter_upwards [Filter.eventually_ge_atTop (K + 1)] with n hn
  have hsub : Finset.Icc 1 K ⊆ Finset.range n := by
    intro d hd
    simp only [Finset.mem_Icc] at hd
    simp only [Finset.mem_range]
    omega
  have hsplit : ∑ d ∈ Finset.range n, f d - ∑ d ∈ Finset.Icc 1 K, f d
      = ∑ d ∈ Finset.range n \ Finset.Icc 1 K, f d := (Finset.sum_sdiff_eq_sub hsub).symm
  have hins : Finset.range n \ Finset.Icc 1 K ⊆ insert 0 (Finset.Ioo K n) := by
    intro d hd
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc] at hd
    simp only [Finset.mem_insert, Finset.mem_Ioo]
    omega
  calc |∑ d ∈ Finset.range n, f d - ∑ d ∈ Finset.Icc 1 K, f d|
      = |∑ d ∈ Finset.range n \ Finset.Icc 1 K, f d| := by rw [hsplit]
    _ ≤ ∑ d ∈ Finset.range n \ Finset.Icc 1 K, |f d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ insert 0 (Finset.Ioo K n), |f d| :=
        Finset.sum_le_sum_of_subset_of_nonneg hins fun _ _ _ => abs_nonneg _
    _ = ∑ d ∈ Finset.Ioo K n, |f d| := by
        rw [Finset.sum_insert (by simp)]
        simp [hf]
    _ ≤ ∑ d ∈ Finset.Ioo K n, ((d : ℝ) ^ 2)⁻¹ := Finset.sum_le_sum fun d _ => hbdd d
    _ ≤ 2 / (K + 1) := sum_Ioo_inv_sq_le K n

/-- **The squarefree count against the full Möbius series.**  Combining the floor error
(`√N`) with the truncation error (`2√N`). -/
theorem abs_squarefreeCount_sub_mul_tsum_le (N : ℕ) :
    |(squarefreeCount N : ℝ) - N * ∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2| ≤ 3 * Real.sqrt N := by
  have h3 := abs_squarefreeCount_sub_mul_sum_le N
  have h4 := abs_tsum_sub_sum_le N
  have hK1 : Real.sqrt N < (Nat.sqrt N : ℝ) + 1 := by
    have h : (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt' N
      exact_mod_cast this
    calc Real.sqrt N < Real.sqrt (((Nat.sqrt N : ℝ) + 1) ^ 2) :=
          Real.sqrt_lt_sqrt (by positivity) h
      _ = (Nat.sqrt N : ℝ) + 1 := Real.sqrt_sq (by positivity)
  have hNK : (N : ℝ) * (2 / ((Nat.sqrt N : ℝ) + 1)) ≤ 2 * Real.sqrt N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hK1, hs, hsq]
  set S := Finset.Icc 1 (Nat.sqrt N) with hS
  set A := ∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 with hA
  set P := ∑ d ∈ S, (μ d : ℝ) / (d : ℝ) ^ 2 with hP
  have habs : |(N : ℝ) * (P - A)| ≤ (N : ℝ) * (2 / ((Nat.sqrt N : ℝ) + 1)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)), abs_sub_comm]
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  calc |(squarefreeCount N : ℝ) - N * A|
      = |((squarefreeCount N : ℝ) - N * P) + (N : ℝ) * (P - A)| := by ring_nf
    _ ≤ |(squarefreeCount N : ℝ) - N * P| + |(N : ℝ) * (P - A)| := abs_add_le _ _
    _ ≤ Real.sqrt N + 2 * Real.sqrt N := add_le_add h3 (habs.trans hNK)
    _ = 3 * Real.sqrt N := by ring

/-- **The value of the Möbius series**: `∑ μ d / d ² = 1 / ζ 2 = 6 / π ²`.  Mathlib supplies
the identity `L ζ s · L μ s = 1` for complex `s` with `1 < re s`; the work here is
specialising it to `s = 2` and descending to a real series. -/
theorem tsum_moebius_div_sq : ∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 = 6 / π ^ 2 := by
  have hs : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hmul := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at hmul
  have hmu : LSeries (fun n => (μ n : ℂ)) 2 = 6 / (π : ℂ) ^ 2 := by
    field_simp at hmul
    field_simp
    linear_combination hmul
  have hterm : ∀ n : ℕ,
      LSeries.term (fun n => (μ n : ℂ)) 2 n = (((μ n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn]
      push_cast
      norm_num
  have hcast : ((∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ) = 6 / (π : ℂ) ^ 2 := by
    rw [Complex.ofReal_tsum, ← hmu, LSeries]
    exact tsum_congr fun n => (hterm n).symm
  exact_mod_cast hcast

/-- **The count of squarefree integers.**  `#{n ≤ N : n squarefree} = 6/π² · N + O(√N)`,
with the error at most `3 √N`. -/
theorem abs_squarefreeCount_sub_le (N : ℕ) :
    |(squarefreeCount N : ℝ) - 6 / π ^ 2 * N| ≤ 3 * Real.sqrt N := by
  have h := abs_squarefreeCount_sub_mul_tsum_le N
  rwa [tsum_moebius_div_sq, mul_comm ((N : ℝ)) (6 / π ^ 2)] at h

/-- `Q` is monotone: a longer range cannot hold fewer squarefree integers. -/
lemma squarefreeCount_mono {m n : ℕ} (h : m ≤ n) : squarefreeCount m ≤ squarefreeCount n :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl h))

/-- `Q N ≥ 3` for `N ≥ 3`, because `1`, `2` and `3` are squarefree.

Crude, and deliberately so: below the range where the density `6/π²` means anything this is the
only lower bound there is, and the Rademacher second moment needs *some* bound there. -/
lemma three_le_squarefreeCount {N : ℕ} (hN : 3 ≤ N) : 3 ≤ squarefreeCount N := by
  have hsub : ({1, 2, 3} : Finset ℕ) ⊆ {n ∈ Finset.Icc 1 3 | Squarefree n} := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rcases hn with rfl | rfl | rfl
    · exact ⟨⟨le_rfl, by norm_num⟩, squarefree_one⟩
    · exact ⟨⟨by norm_num, by norm_num⟩, Nat.squarefree_two⟩
    · exact ⟨⟨by norm_num, le_rfl⟩, Nat.prime_three.squarefree⟩
  have hcard : ({1, 2, 3} : Finset ℕ).card = 3 := by decide
  have h := Finset.card_le_card hsub
  rw [hcard] at h
  exact le_trans h (squarefreeCount_mono hN)

/-- **`Q N ≥ N/8` for `N ≥ 144`.**  `RMF.abs_squarefreeCount_sub_le` gives `Q N ≥ 6/π² · N - 3√N`;
the density is at least `3/8` because `π ≤ 4`, and the error is at most `N/4` because `√N ≥ 12`.
Neither constant is sharp (the density is `6/π² = 0.6079…`); `Real.pi_lt_d2` would give `N/2` from
`N ≥ 900`, but it lives in `Mathlib.Analysis.Real.Pi.Bounds`, which this file does not import. -/
lemma eighth_le_squarefreeCount {N : ℕ} (hN : 144 ≤ N) : (N : ℝ) / 8 ≤ squarefreeCount N := by
  have hN0 : (144 : ℝ) ≤ N := by exact_mod_cast hN
  have hpi2 : π ^ 2 ≤ 16 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  have hdens : (3 : ℝ) / 8 ≤ 6 / π ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hmul : (3 : ℝ) / 8 * N ≤ 6 / π ^ 2 * N := by nlinarith
  have hsq : Real.sqrt N ≤ (N : ℝ) / 12 := by
    have h12 : (12 : ℝ) ≤ Real.sqrt N := by
      have h := Real.sqrt_le_sqrt hN0
      rwa [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (N : ℝ))]
  have herr := (abs_le.1 (abs_squarefreeCount_sub_le N)).1
  linarith
end RMF
