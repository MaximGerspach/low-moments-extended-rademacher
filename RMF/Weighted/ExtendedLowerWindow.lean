/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ExtendedLowerKhintchine
import RMF.Weighted.ExtendedReduction
import RMF.Weighted.LowerWindow
import RMF.Weighted.LowerReduction

/-!
# The extended sum's lower bound: the smoothing steps

After `RMF.khintchine_rough_extended` the lower bound needs
`E[(∑_{√x<p≤x} |∑_{m≤x/p} X^e(m)|²)^q]` from below.  The smoothing steps of the weighted chain are
pointwise and hold for any arithmetic function (`RMF.sum_normSq_ge`); with the sliver folded back
(`RMF.meanSquare_split`) they give

`(x/(8 log x))·∫_1^{√x/(1+1/log x)} |∑_{n≤z} X^e(n)|² dz/z² - D/log x ≤ ∑_p |∑_{m≤x/p} X^e(m)|²`,

`D` the smoothing discrepancy.  What does not transfer is the bound on its mean, which the
Steinhaus chain gets from orthogonality.

## The smoothing error without orthogonality

By the square classes (`RMF.sum_compMultExtension_eq_sum_squarefreeExtension_mul`),
`∑_{a<n≤b} X^e(n) = ∑_m X(m)·c_m` with `c_m = ⌊√(b/m)⌋ - ⌊√(a/m)⌋`, and orthogonality of `X`
gives `E|∑_{a<n≤b} X^e(n)|² = ∑_{m squarefree} c_m²` (`RMF.integral_normSq_sum_Ioc_compMult`).
Now `∑_{m squarefree} c_m = ⌊b⌋ - ⌊a⌋` (the same identity at `X ≡ 1`); `c_m ≥ 2` forces
`m < b - a`; and `c_m² ≤ 2 + (b-a)²/(2am)`.  So
`E|∑_{a<n≤b} X^e(n)|² ≤ (⌊b⌋ - ⌊a⌋) + 2(b-a) + (b-a)²(1 + log b)/(2a)`
(`RMF.sum_sq_floor_sqrt_sub_le`), which on a smoothing window is at most five times the
orthogonal bound (`RMF.integral_discrepancy_le_extended`).

The integrability lemmas of the Steinhaus chain ask for `RMF.IsBoundedRMF`, which `X^e` is not;
they use only measurability and `|f| ≤ 1`, and are restated with those hypotheses (`…_of`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Intervals of `v^e` by square classes -/

/-- **An interval of `v^e`, by square classes.**  If `v(p)² = 1` at the primes up to `b`, then for
`0 ≤ a ≤ b`, `∑_{a<n≤b} v^e(n) = ∑_{m≤b} v_sf(m)·(⌊√(b/m)⌋ - ⌊√(a/m)⌋)`. -/
lemma sum_Ioc_compMultExtension_eq {v : ℕ → ℂ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hv : ∀ p, p.Prime → p ≤ ⌊b⌋₊ → v p ^ 2 = 1) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, compMultExtension v n
      = ∑ m ∈ Finset.Icc 1 ⌊b⌋₊, squarefreeExtension v m
          * ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℂ) := by
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have hva : ∀ p, p.Prime → p ≤ ⌊a⌋₊ → v p ^ 2 = 1 := fun p hp h => hv p hp (le_trans h hfl)
  have hB := sum_compMultExtension_eq_sum_squarefreeExtension_mul (le_trans ha hab) hv
  have hA := sum_compMultExtension_eq_sum_squarefreeExtension_mul ha hva
  have hA' : ∑ m ∈ Finset.Icc 1 ⌊a⌋₊, squarefreeExtension v m * (⌊Real.sqrt (a / m)⌋₊ : ℂ)
      = ∑ m ∈ Finset.Icc 1 ⌊b⌋₊, squarefreeExtension v m * (⌊Real.sqrt (a / m)⌋₊ : ℂ) := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right hfl) fun m hm hma => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    have hma' : ⌊a⌋₊ < m := by
      by_contra h
      exact hma (Finset.mem_Icc.2 ⟨hm1, not_lt.1 h⟩)
    have hzero : ⌊Real.sqrt (a / m)⌋₊ = 0 := by
      rw [Nat.floor_eq_zero, Real.sqrt_lt' one_pos, one_pow,
        div_lt_one (by exact_mod_cast hm1)]
      exact Nat.lt_of_floor_lt hma'
    rw [hzero, Nat.cast_zero, mul_zero]
  have hdiff : ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, compMultExtension v n
      = ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, compMultExtension v n
        - ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, compMultExtension v n := by
    have hsub : Finset.Icc 1 ⌊a⌋₊ ⊆ Finset.Icc 1 ⌊b⌋₊ := Finset.Icc_subset_Icc_right hfl
    have hsdiff : Finset.Icc 1 ⌊b⌋₊ \ Finset.Icc 1 ⌊a⌋₊ = Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
      ext n
      simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [← Finset.sum_sdiff_eq_sub hsub, hsdiff]
  rw [hdiff, hB, hA, hA', ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
  have hmono : ⌊Real.sqrt (a / m)⌋₊ ≤ ⌊Real.sqrt (b / m)⌋₊ :=
    Nat.floor_le_floor (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hab hm0.le))
  rw [Nat.cast_sub hmono]
  ring

/-- **The mean square of an interval of `X^e`.**  For Rademacher `X` and `0 ≤ a ≤ b`,
`E|∑_{a<n≤b} X^e(n)|² = ∑_{m≤b squarefree} (⌊√(b/m)⌋ - ⌊√(a/m)⌋)²`. -/
theorem integral_normSq_sum_Ioc_compMult {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, compMultExtension (fun p => X p ω) n‖ ^ 2 ∂μ)
      = ∑ m ∈ Finset.Icc 1 ⌊b⌋₊, (((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) ^ 2
          * (if Squarefree m then 1 else 0)) := by
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hsq : ∀ᵐ ω ∂μ, ∀ p ∈ Nat.primesBelow (⌊b⌋₊ + 1), X p ω ^ 2 = 1 :=
    (Filter.eventually_all_finset _).2 fun p hp =>
      ae_sq_X_eq_one hX (Nat.prime_of_mem_primesBelow hp)
  have hcongr : (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, compMultExtension (fun p => X p ω) n‖ ^ 2 ∂μ)
      = ∫ ω, ‖∑ m ∈ Finset.Icc 1 ⌊b⌋₊,
          ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℂ)
            * squarefreeExtension (fun p => X p ω) m‖ ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hsq] with ω hω
    have hcomm : ∀ m ∈ Finset.Icc 1 ⌊b⌋₊, squarefreeExtension (fun p => X p ω) m
        * ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℂ)
        = ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℂ)
          * squarefreeExtension (fun p => X p ω) m := fun m _ => mul_comm _ _
    rw [sum_Ioc_compMultExtension_eq ha hab fun p hp hpb =>
      hω p (Nat.mem_primesBelow.2 ⟨by omega, hp⟩), Finset.sum_congr rfl hcomm]
  have hne : ∀ m ∈ Finset.Icc 1 ⌊b⌋₊, m ≠ 0 := fun m hm =>
    Nat.one_le_iff_ne_zero.1 (Finset.mem_Icc.1 hm).1
  have key := integral_normSq_weightedSum_of_orthogonality'
    (f := fun ω => squarefreeExtension fun p => X p ω) (μ := μ) (s := Finset.Icc 1 ⌊b⌋₊)
    (c := fun m : ℕ => ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℂ))
    (d := fun m => ((if Squarefree m then 1 else 0 : ℝ) : ℂ))
    (fun m _ n _ => hf.integrable_mul_conj m n)
    (fun m hm n hn => by
      rw [hf.orthogonality (hne m hm) (hne n hn)]
      by_cases h : m = n
      · subst h
        by_cases hs : Squarefree m <;> simp [hs]
      · simp [h])
  rw [hcongr]
  simp_rw [Complex.norm_natCast] at key
  exact_mod_cast key

/-! ### The count -/

/-- `(√w - √u)² ≤ (w-u)²/(4u)` for `0 < u ≤ w`. -/
lemma sqrt_sub_sqrt_sq_le {u w : ℝ} (hu : 0 < u) (huw : u ≤ w) :
    (Real.sqrt w - Real.sqrt u) ^ 2 ≤ (w - u) ^ 2 / (4 * u) := by
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsw : Real.sqrt u ≤ Real.sqrt w := Real.sqrt_le_sqrt huw
  have hprod : (Real.sqrt w - Real.sqrt u) * (Real.sqrt w + Real.sqrt u) = w - u := by
    rw [show (Real.sqrt w - Real.sqrt u) * (Real.sqrt w + Real.sqrt u)
        = Real.sqrt w ^ 2 - Real.sqrt u ^ 2 by ring,
      Real.sq_sqrt (le_trans hu.le huw), Real.sq_sqrt hu.le]
  have hd0 : 0 ≤ Real.sqrt w - Real.sqrt u := by linarith
  have hd : Real.sqrt w - Real.sqrt u ≤ (w - u) / (2 * Real.sqrt u) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc (Real.sqrt w - Real.sqrt u) ^ 2 ≤ ((w - u) / (2 * Real.sqrt u)) ^ 2 :=
        pow_le_pow_left₀ hd0 hd 2
    _ = (w - u) ^ 2 / (4 * u) := by
        rw [div_pow, mul_pow, Real.sq_sqrt hu.le]
        norm_num

/-- `c_m² ≤ 2 + (b-a)²/(2am)` for `c_m = ⌊√(b/m)⌋ - ⌊√(a/m)⌋`, `0 < a ≤ b`, `m > 0`. -/
lemma floor_sqrt_sub_sq_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {m : ℕ} (hm : 0 < m) :
    ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) ^ 2
      ≤ 2 + (b - a) ^ 2 / (2 * a * m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hu : 0 < a / m := div_pos ha hm0
  have huw : a / m ≤ b / m := div_le_div_of_nonneg_right hab hm0.le
  have hmono : ⌊Real.sqrt (a / m)⌋₊ ≤ ⌊Real.sqrt (b / m)⌋₊ :=
    Nat.floor_le_floor (Real.sqrt_le_sqrt huw)
  have hc : ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)
      ≤ Real.sqrt (b / m) - Real.sqrt (a / m) + 1 := by
    rw [Nat.cast_sub hmono]
    have h1 : (⌊Real.sqrt (b / m)⌋₊ : ℝ) ≤ Real.sqrt (b / m) := Nat.floor_le (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (a / m) < ⌊Real.sqrt (a / m)⌋₊ + 1 := Nat.lt_floor_add_one _
    linarith
  have hd0 : 0 ≤ Real.sqrt (b / m) - Real.sqrt (a / m) := sub_nonneg.2 (Real.sqrt_le_sqrt huw)
  have hsq := sqrt_sub_sqrt_sq_le hu huw
  have heq : (b / m - a / m) ^ 2 / (4 * (a / m)) = (b - a) ^ 2 / (4 * a * m) := by
    field_simp
  rw [heq] at hsq
  have hc0 : (0 : ℝ) ≤ ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) ^ 2
      ≤ (Real.sqrt (b / m) - Real.sqrt (a / m) + 1) ^ 2 := pow_le_pow_left₀ hc0 hc 2
    _ ≤ 2 * (Real.sqrt (b / m) - Real.sqrt (a / m)) ^ 2 + 2 := by
        nlinarith [sq_nonneg (Real.sqrt (b / m) - Real.sqrt (a / m) - 1)]
    _ ≤ 2 * ((b - a) ^ 2 / (4 * a * m)) + 2 := by linarith
    _ = 2 + (b - a) ^ 2 / (2 * a * m) := by
        field_simp
        ring

/-- `c_m ≥ 2` forces `m < b - a`: two consecutive squares `s²m, (s+1)²m` fit in `(a, b]`. -/
lemma lt_sub_of_two_le_floor_sqrt_sub {a b : ℝ} (ha : 0 ≤ a) {m : ℕ} (hm : 0 < m)
    (h : 2 ≤ ⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊) : (m : ℝ) < b - a := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : ⌊Real.sqrt (a / m)⌋₊ + 2 ≤ ⌊Real.sqrt (b / m)⌋₊ := by omega
  have hsa : Real.sqrt (a / m) < ⌊Real.sqrt (a / m)⌋₊ + 1 := Nat.lt_floor_add_one _
  have hsb : (⌊Real.sqrt (b / m)⌋₊ : ℝ) ≤ Real.sqrt (b / m) := Nat.floor_le (Real.sqrt_nonneg _)
  have h2 : Real.sqrt (a / m) + 1 < Real.sqrt (b / m) := by
    have h3 : ((⌊Real.sqrt (a / m)⌋₊ + 2 : ℕ) : ℝ) ≤ (⌊Real.sqrt (b / m)⌋₊ : ℝ) := by
      exact_mod_cast h1
    push_cast at h3
    linarith
  have hb : 0 < b / m := by
    by_contra hc
    rw [Real.sqrt_eq_zero'.2 (not_lt.1 hc)] at h2
    linarith [Real.sqrt_nonneg (a / m)]
  have hsq : (Real.sqrt (a / m) + 1) ^ 2 < Real.sqrt (b / m) ^ 2 :=
    pow_lt_pow_left₀ h2 (by positivity) two_ne_zero
  rw [Real.sq_sqrt hb.le, add_sq, Real.sq_sqrt (div_nonneg ha hm0.le)] at hsq
  have h4 : a / m + 1 < b / m := by nlinarith [Real.sqrt_nonneg (a / m)]
  have h5 : (a / m + 1) * m < b := by
    have := (lt_div_iff₀ hm0).1 h4
    linarith
  rw [add_mul, div_mul_cancel₀ a hm0.ne', one_mul] at h5
  linarith

/-- `∑_{m≤b squarefree} (⌊√(b/m)⌋ - ⌊√(a/m)⌋) = ⌊b⌋ - ⌊a⌋`: the square classes at `v ≡ 1`. -/
lemma sum_floor_sqrt_sub_squarefree_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∑ m ∈ Finset.Icc 1 ⌊b⌋₊, (((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)
        * (if Squarefree m then 1 else 0)) = (⌊b⌋₊ : ℝ) - ⌊a⌋₊ := by
  have h := sum_Ioc_compMultExtension_eq (v := fun _ => (1 : ℂ)) ha hab fun _ _ _ => one_pow 2
  have hL : ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, compMultExtension (fun _ => (1 : ℂ)) n
      = ((⌊b⌋₊ - ⌊a⌋₊ : ℕ) : ℂ) := by
    rw [Finset.sum_congr rfl fun n hn => ?_, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Ioc.1 hn).1
      omega
    rw [compMultExtension_apply_of_ne_zero _ hn0]
    simp [Finsupp.prod]
  have hR : ∀ m ∈ Finset.Icc 1 ⌊b⌋₊, squarefreeExtension (fun _ => (1 : ℂ)) m
      * ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℂ)
      = ((((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)
          * (if Squarefree m then 1 else 0) : ℝ) : ℂ) := by
    intro m _
    by_cases hs : Squarefree m
    · rw [squarefreeExtension_apply_of_squarefree _ hs]
      simp [hs]
    · rw [squarefreeExtension_apply_of_not_squarefree _ hs]
      simp [hs]
  rw [hL, Finset.sum_congr rfl hR] at h
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have h' : ((∑ m ∈ Finset.Icc 1 ⌊b⌋₊, (((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)
        * (if Squarefree m then 1 else 0)) : ℝ) : ℂ) = (((⌊b⌋₊ : ℝ) - ⌊a⌋₊ : ℝ) : ℂ) := by
    push_cast [Nat.cast_sub hfl] at h ⊢
    rw [← h]
  exact_mod_cast h'

/-- **The count.**  For `1 ≤ a ≤ b`,
`∑_{m≤b squarefree} (⌊√(b/m)⌋ - ⌊√(a/m)⌋)² ≤ (⌊b⌋ - ⌊a⌋) + 2(b-a) + (b-a)²(1 + log b)/(2a)`. -/
lemma sum_sq_floor_sqrt_sub_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ m ∈ Finset.Icc 1 ⌊b⌋₊, (((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) ^ 2
        * (if Squarefree m then 1 else 0))
      ≤ ((⌊b⌋₊ : ℝ) - ⌊a⌋₊) + 2 * (b - a) + (b - a) ^ 2 * (1 + Real.log b) / (2 * a) := by
  have ha0 : (0 : ℝ) < a := by linarith
  set K : ℝ := (b - a) ^ 2 / (2 * a) with hK
  have hK0 : 0 ≤ K := by positivity
  -- pointwise
  have hpt : ∀ m ∈ Finset.Icc 1 ⌊b⌋₊,
      ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) ^ 2 * (if Squarefree m then 1 else 0)
        ≤ ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)
            * (if Squarefree m then 1 else 0)
          + (if (m : ℝ) < b - a then 2 + K / m else 0) := by
    intro m hm
    have hm1 : 0 < m := (Finset.mem_Icc.1 hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hind : (0 : ℝ) ≤ (if Squarefree m then 1 else 0) := by split_ifs <;> norm_num
    have hind1 : (if Squarefree m then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    rcases Nat.lt_or_ge (⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊) 2 with hc | hc
    · have hc1 : ⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ ≤ 1 := by omega
      have hcr : ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) ≤ 1 := by
        exact_mod_cast hc1
      have hc0 : (0 : ℝ) ≤ ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      have hextra : (0 : ℝ) ≤ (if (m : ℝ) < b - a then 2 + K / m else 0) := by
        split_ifs <;> positivity
      have hsq : ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) ^ 2
          ≤ ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) := by nlinarith
      nlinarith
    · have hlt := lt_sub_of_two_le_floor_sqrt_sub ha0.le hm1 hc
      rw [if_pos hlt]
      have hbound := floor_sqrt_sub_sq_le ha0 hab hm1
      have hK' : (b - a) ^ 2 / (2 * a * m) = K / m := by
        rw [hK]
        field_simp
      rw [hK'] at hbound
      have hc0 : (0 : ℝ) ≤ ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hind1 (sq_nonneg
        ((⌊Real.sqrt (b / m)⌋₊ - ⌊Real.sqrt (a / m)⌋₊ : ℕ) : ℝ)), mul_nonneg hc0 hind]
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_add_distrib, sum_floor_sqrt_sub_squarefree_eq (by linarith) hab]
  -- the extra terms live on `m < b - a`
  have hba : 0 ≤ b - a := by linarith
  have hfl : ⌊b - a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor (by linarith)
  have hsub : ∑ m ∈ Finset.Icc 1 ⌊b⌋₊, (if (m : ℝ) < b - a then 2 + K / m else 0)
      ≤ ∑ m ∈ Finset.Icc 1 ⌊b - a⌋₊, (2 + K / m) := by
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hfl) fun m hm hm' => ?_]
    · refine Finset.sum_le_sum fun m hm => ?_
      split_ifs
      · exact le_rfl
      · have : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
        positivity
    · rw [if_neg]
      intro hlt
      exact hm' (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hm).1, Nat.le_floor hlt.le⟩)
  have hharm : ∑ m ∈ Finset.Icc 1 ⌊b - a⌋₊, (2 + K / m)
      ≤ 2 * (b - a) + K * (1 + Real.log b) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have h1 : (⌊b - a⌋₊ : ℝ) * 2 ≤ 2 * (b - a) := by
      nlinarith [Nat.floor_le hba]
    have hsumK : ∑ m ∈ Finset.Icc 1 ⌊b - a⌋₊, K / (m : ℝ)
        = K * ∑ m ∈ Finset.Icc 1 ⌊b - a⌋₊, ((m : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => div_eq_mul_inv _ _
    have hH : ∑ m ∈ Finset.Icc 1 ⌊b - a⌋₊, ((m : ℝ))⁻¹ ≤ 1 + Real.log b := by
      have hh := harmonic_le_one_add_log ⌊b - a⌋₊
      rw [harmonic_eq_sum_Icc] at hh
      push_cast at hh
      refine le_trans hh ?_
      rcases Nat.eq_zero_or_pos ⌊b - a⌋₊ with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.log_zero]
        linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ b)]
      · have : ((⌊b - a⌋₊ : ℕ) : ℝ) ≤ b := le_trans (Nat.floor_le hba) (by linarith)
        linarith [Real.log_le_log (by exact_mod_cast hpos) this]
    rw [hsumK]
    nlinarith [mul_le_mul_of_nonneg_left hH hK0]
  have hfinal : K * (1 + Real.log b) = (b - a) ^ 2 * (1 + Real.log b) / (2 * a) := by
    rw [hK]
    ring
  linarith

/-! ### The smoothing window -/

/-- **The mean square on a smoothing window.**  For Rademacher `X`, `0 < a ≤ b ≤ (1+1/L)a`,
`1 ≤ L` and `1 + log b ≤ 2L`: `E|∑_{a<n≤b} X^e(n)|² ≤ (⌊b⌋ - ⌊a⌋) + 4(b-a) + 1`. -/
theorem integral_normSq_sum_Ioc_compMult_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {a b L : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbL : b ≤ (1 + 1 / L) * a) (hL : 1 ≤ L) (hlog : 1 + Real.log b ≤ 2 * L) :
    (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, compMultExtension (fun p => X p ω) n‖ ^ 2 ∂μ)
      ≤ ((⌊b⌋₊ : ℝ) - ⌊a⌋₊) + 4 * (b - a) + 1 := by
  haveI := hX.isProbabilityMeasure
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have hcount : (0 : ℝ) ≤ (⌊b⌋₊ : ℝ) - ⌊a⌋₊ := by
    have : (⌊a⌋₊ : ℝ) ≤ ⌊b⌋₊ := by exact_mod_cast hfl
    linarith
  rcases lt_or_ge a 1 with ha1 | ha1
  · -- `b < 2`: at most one integer
    have hb2 : b < 2 := by
      have h1 : 1 / L ≤ 1 := by rw [div_le_one (by linarith)]; exact hL
      calc b ≤ (1 + 1 / L) * a := hbL
        _ < (1 + 1 / L) * 1 := mul_lt_mul_of_pos_left ha1 (by positivity)
        _ ≤ 2 := by linarith
    have hfb : ⌊b⌋₊ ≤ 1 := by
      have := Nat.floor_lt (by linarith : (0 : ℝ) ≤ b) |>.2
        (by exact_mod_cast hb2 : b < ((2 : ℕ) : ℝ))
      omega
    have hcard : (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).card ≤ 1 := by
      rw [Nat.card_Ioc]
      omega
    calc (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, compMultExtension (fun p => X p ω) n‖ ^ 2 ∂μ)
        ≤ ∫ _ω, (1 : ℝ) ∂μ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
            (integrable_const _) ?_
          filter_upwards [(Filter.eventually_all_finset (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊)).2
            fun n _ => hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n]
            with ω hω
          have hn : ‖∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, compMultExtension (fun p => X p ω) n‖ ≤ 1 := by
            calc _ ≤ ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ‖compMultExtension (fun p => X p ω) n‖ :=
                  norm_sum_le _ _
              _ ≤ ∑ _n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (1 : ℝ) := Finset.sum_le_sum hω
              _ = (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).card := by simp
              _ ≤ 1 := by exact_mod_cast hcard
          exact pow_le_one₀ (norm_nonneg _) hn
      _ = 1 := by simp
      _ ≤ ((⌊b⌋₊ : ℝ) - ⌊a⌋₊) + 4 * (b - a) + 1 := by linarith
  · rw [integral_normSq_sum_Ioc_compMult hX ha.le hab]
    refine le_trans (sum_sq_floor_sqrt_sub_le ha1 hab) ?_
    have hba : 0 ≤ b - a := by linarith
    have hL0 : 0 < L := by linarith
    have hratio : b - a ≤ a / L := by
      have : (1 + 1 / L) * a = a + a / L := by ring
      linarith
    have hkey : (b - a) ^ 2 * (1 + Real.log b) / (2 * a) ≤ b - a := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : (b - a) * (1 + Real.log b) ≤ (a / L) * (2 * L) :=
        mul_le_mul hratio hlog (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ b)])
          (by positivity)
      have h2 : (a / L) * (2 * L) = 2 * a := by field_simp
      nlinarith
    linarith

/-! ### Integrability without `RMF.IsBoundedRMF` -/

section Integrability

variable {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}

lemma measurable_randomSum_uncurry_of (hmeas : ∀ n : ℕ, Measurable fun ω => f ω n) :
    Measurable fun p : Ω × ℝ => randomSum f p.2 p.1 := by
  have h1 : Measurable fun p : ℕ × Ω => ∑ n ∈ Finset.Icc 1 p.1, f p.2 n :=
    measurable_from_prod_countable_right fun N =>
      (Finset.measurable_sum (Finset.Icc 1 N) fun n _ => hmeas n :
        Measurable fun y : Ω => ∑ n ∈ Finset.Icc 1 N, f y n)
  exact h1.comp ((Nat.measurable_floor.comp measurable_snd).prodMk measurable_fst)

lemma ae_norm_randomSum_le_of (hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1) (b : ℝ) :
    ∀ᵐ ω ∂μ, ∀ a : ℝ, a ≤ b → ‖randomSum f a ω‖ ≤ (⌊b⌋₊ : ℝ) := by
  have hall : ∀ n ∈ Finset.Icc 1 ⌊b⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 := fun n _ => hbd n
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω a hab
  refine le_trans (norm_randomSum_le_of_le f hab ω) ?_
  refine le_trans (Finset.sum_le_sum fun n hn => hω n hn) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
  simp

lemma measurable_discrepancy_of (hmeas : ∀ n : ℕ, Measurable fun ω => f ω n) (x p : ℝ) :
    Measurable fun z : Ω × ℝ => discrepancy f x p z.1 z.2 := by
  have hA : Measurable fun z : Ω × ℝ => randomSum f (x / z.2) z.1 :=
    (measurable_randomSum_uncurry_of hmeas).comp
      (measurable_fst.prodMk (measurable_const.div measurable_snd))
  have hB : Measurable fun z : Ω × ℝ => randomSum f (x / p) z.1 :=
    (Finset.measurable_sum _ fun n _ => hmeas n).comp measurable_fst
  simp only [discrepancy]
  exact ((hB.sub hA).norm.pow_const 2).min ((hA.norm.pow_const 2).const_mul (1 / 4 : ℝ))

lemma integrable_normSq_randomSum_sub_of [IsProbabilityMeasure μ]
    (hmeas : ∀ n : ℕ, Measurable fun ω => f ω n) (hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1)
    {a b : ℝ} (hab : a ≤ b) :
    Integrable (fun ω => ‖randomSum f b ω - randomSum f a ω‖ ^ 2) μ := by
  refine Integrable.mono' (integrable_const (4 * (⌊b⌋₊ : ℝ) ^ 2))
    ((((Finset.measurable_sum _ fun n _ => hmeas n).sub
      (Finset.measurable_sum _ fun n _ => hmeas n)).norm.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [ae_norm_randomSum_le_of hbd b] with ω hω
  have h1 := hω b le_rfl
  have h2 := hω a hab
  have h3 : ‖randomSum f b ω - randomSum f a ω‖ ≤ 2 * (⌊b⌋₊ : ℝ) :=
    le_trans (norm_sub_le _ _) (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [norm_nonneg (randomSum f b ω - randomSum f a ω)]

lemma integrable_discrepancy_slice_of [IsProbabilityMeasure μ]
    (hmeas : ∀ n : ℕ, Measurable fun ω => f ω n) (hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1)
    {x p t : ℝ} (hp : 0 < p) (ht : p ≤ t) (hx : 0 ≤ x) :
    Integrable (fun ω => discrepancy f x p ω t) μ := by
  have hdiv : x / t ≤ x / p := by gcongr
  have hm : Measurable fun ω => discrepancy f x p ω t := by
    simp only [discrepancy]
    exact (((Finset.measurable_sum _ fun n _ => hmeas n).sub
      (Finset.measurable_sum _ fun n _ => hmeas n)).norm.pow_const 2).min
      (((Finset.measurable_sum _ fun n _ => hmeas n).norm.pow_const 2).const_mul (1 / 4 : ℝ))
  refine Integrable.mono' (integrable_normSq_randomSum_sub_of hmeas hbd hdiv)
    hm.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (discrepancy_nonneg f x p ω t)]
  exact discrepancy_le_block f x p ω t

lemma integrable_discrepancy_of [IsProbabilityMeasure μ]
    (hmeas : ∀ n : ℕ, Measurable fun ω => f ω n) (hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1)
    {x X p : ℝ} (hx : 0 ≤ x) (hp : 0 < p) :
    Integrable (Function.uncurry (discrepancy f x p))
      (μ.prod (volume.restrict (Set.Ioc p (p * (1 + 1 / X))))) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc p (p * (1 + 1 / X)))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  refine integrableOn_univ.1 (Measure.integrableOn_of_bounded
    (M := 1 / 4 * (⌊x / p⌋₊ : ℝ) ^ 2) (measure_ne_top _ _)
    (measurable_discrepancy_of hmeas x p).aestronglyMeasurable ?_)
  rw [Measure.restrict_univ]
  refine (Measure.ae_prod_iff_ae_ae (measurableSet_le
    (measurable_discrepancy_of hmeas x p).norm measurable_const)).2 ?_
  filter_upwards [ae_norm_randomSum_le_of hbd (x / p)] with ω hω
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hpt : p ≤ t := ht.1.le
  have hdiv : x / t ≤ x / p := by gcongr
  have hnorm := hω (x / t) hdiv
  rw [Real.norm_eq_abs]
  change |discrepancy f x p ω t| ≤ 1 / 4 * (⌊x / p⌋₊ : ℝ) ^ 2
  rw [abs_of_nonneg (discrepancy_nonneg f x p ω t)]
  refine le_trans (discrepancy_le_quarter f x p ω t) ?_
  have := pow_le_pow_left₀ (norm_nonneg (randomSum f (x / t) ω)) hnorm 2
  linarith

lemma integrable_normSq_randomSum_of [IsProbabilityMeasure μ]
    (hmeas : ∀ n : ℕ, Measurable fun ω => f ω n) (hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1)
    (b : ℝ) : Integrable (fun ω => ‖randomSum f b ω‖ ^ 2) μ := by
  refine Integrable.mono' (integrable_const ((⌊b⌋₊ : ℝ) ^ 2))
    ((Finset.measurable_sum _ fun n _ => hmeas n).norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_norm_randomSum_le_of hbd b] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hω b le_rfl) 2

lemma integrable_meanSquare_prod_of [IsProbabilityMeasure μ]
    (hmeas : ∀ n : ℕ, Measurable fun ω => f ω n) (hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1)
    {c d : ℝ} (hc : 1 ≤ c) :
    Integrable (Function.uncurry fun (ω : Ω) (z : ℝ) => ‖randomSum f z ω‖ ^ 2 / z ^ 2)
      (μ.prod (volume.restrict (Set.Ioc c d))) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc c d)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hm : Measurable fun p : Ω × ℝ => ‖randomSum f p.2 p.1‖ ^ 2 / p.2 ^ 2 :=
    (((measurable_randomSum_uncurry_of hmeas).norm).pow_const 2).div (measurable_snd.pow_const 2)
  refine integrableOn_univ.1 (Measure.integrableOn_of_bounded
    (M := (⌊d⌋₊ : ℝ) ^ 2) (measure_ne_top _ _) hm.aestronglyMeasurable ?_)
  rw [Measure.restrict_univ]
  refine (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).2 ?_
  filter_upwards [ae_norm_randomSum_le_of hbd d] with ω hω
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
  have hz1 : (1 : ℝ) ≤ z := le_trans hc hz.1.le
  have hn := hω z hz.2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : ‖randomSum f z ω‖ ^ 2 ≤ (⌊d⌋₊ : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h2 : ‖randomSum f z ω‖ ^ 2 / z ^ 2 ≤ ‖randomSum f z ω‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    have hz2 : (1 : ℝ) ≤ z ^ 2 := by nlinarith
    nlinarith [sq_nonneg ‖randomSum f z ω‖, hz2]
  linarith

end Integrability

/-! ### The smoothing error of the extended sum -/

/-- **The smoothing error of the extended sum, per prime.**  For `x > 0`, `1 ≤ L`, `0 < p` with
`1 + log(x/p) ≤ 2L`, the expected discrepancy over the window `(p, p(1+1/L)]` is at most
`5(x/(pL) + 1)`, five times the orthogonal bound of `RMF.integral_discrepancy_le`. -/
theorem integral_discrepancy_le_extended {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {x L p : ℝ} (hx : 0 < x)
    (hL : 1 ≤ L) (hp : 0 < p) (hlog : 1 + Real.log (x / p) ≤ 2 * L) :
    (∫ ω, L / p * (∫ t in Set.Ioc p (p * (1 + 1 / L)),
        discrepancy (fun ω => compMultExtension fun q => X q ω) x p ω t) ∂μ)
      ≤ 5 * (x / (p * L) + 1) := by
  set g : Ω → ArithmeticFunction ℂ := fun ω => compMultExtension fun q => X q ω with hgdef
  have hmeas : ∀ n : ℕ, Measurable fun ω => g ω n := fun n => hX.measurable_compMultExtension n
  have hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖g ω n‖ ≤ 1 := fun n =>
    hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n
  have hL0 : 0 < L := by linarith
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc p (p * (1 + 1 / L)))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hInt := integrable_discrepancy_of (X := L) hmeas hbd hx.le hp
  rw [integral_const_mul, integral_integral_swap hInt]
  have hbound : ∀ t ∈ Set.Ioc p (p * (1 + 1 / L)),
      (∫ ω, discrepancy g x p ω t ∂μ) ≤ 5 * (x / (p * L) + 1) := by
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
    have hratio : x / p ≤ (1 + 1 / L) * (x / t) := by
      rw [div_le_iff₀ hp]
      have h1 : t ≤ p * (1 + 1 / L) := ht.2
      have h2 : (1 + 1 / L) * (x / t) * p = x * (p * (1 + 1 / L)) / t := by
        field_simp
      rw [h2, le_div_iff₀ ht0]
      nlinarith
    have hwin := integral_normSq_sum_Ioc_compMult_le hX (div_pos hx ht0) hdiv hratio hL hlog
    have hcount := floor_sub_floor_le hx.le hL0 hp hpt ht.2
    have hlen : x / p - x / t ≤ x / (p * L) := by
      have hxt : x / p - x / t = x * (t - p) / (p * t) := by field_simp
      rw [hxt]
      calc x * (t - p) / (p * t) ≤ x * (p / L) / (p * t) := by
            gcongr
            have : t ≤ p + p / L := by
              have := ht.2
              linarith [show p * (1 + 1 / L) = p + p / L by ring]
            linarith
        _ ≤ x * (p / L) / (p * p) := by gcongr
        _ = x / (p * L) := by field_simp
    linarith [hle, hblock ▸ hwin]
  have hconst : L / p * ∫ _t in Set.Ioc p (p * (1 + 1 / L)), 5 * (x / (p * L) + 1)
      = 5 * (x / (p * L) + 1) := setIntegral_const_window hp hL0
  rw [← hconst]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact setIntegral_mono_on hInt.integral_prod_right (integrableOn_const (by simp))
    measurableSet_Ioc hbound

/-- The extended discrepancy sum is integrable, prime by prime. -/
lemma integrable_extendedDiscrepancySum {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsRademacherPrimeValues X μ) {x L : ℝ} (hx : 0 ≤ x) {S : Finset ℕ}
    (hSp : ∀ p ∈ S, Nat.Prime p) :
    Integrable (fun ω => ∑ p ∈ S, Real.log p * (L / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / L)),
        discrepancy (fun ω => compMultExtension fun q => X q ω) x p ω t)) μ :=
  integrable_finsetSum _ fun p hp =>
    (((integrable_discrepancy_of (X := L) (fun n => hX.measurable_compMultExtension n)
      (fun n => hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n) hx
      (by exact_mod_cast (hSp p hp).pos)).integral_prod_left).const_mul _).const_mul _

/-- **The smoothing error of the extended sum, summed.**  At `L = log x`, for `x ≥ e` and any set
of primes up to `x`, the expected total discrepancy is at most `40x`. -/
theorem integral_sum_discrepancy_le_extended {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : Real.exp 1 ≤ x)
    {S : Finset ℕ} (hS : S ⊆ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime}) :
    (∫ ω, ∑ p ∈ S, Real.log p * (Real.log x / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
        discrepancy (fun ω => compMultExtension fun q => X q ω) x p ω t) ∂μ) ≤ 40 * x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact hx
  have hSp : ∀ p ∈ S, Nat.Prime p := fun p hp => (Finset.mem_filter.1 (hS hp)).2
  have hpos : ∀ p ∈ S, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hSp p hp).pos
  rw [integral_finsetSum]
  swap
  · intro p hp
    exact ((integrable_discrepancy_of (X := Real.log x)
      (fun n => hX.measurable_compMultExtension n)
      (fun n => hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n) hx0.le
      (hpos p hp)).integral_prod_left.const_mul _).const_mul _
  have hper : ∀ p ∈ S, (∫ ω, Real.log p * (Real.log x / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
        discrepancy (fun ω => compMultExtension fun q => X q ω) x p ω t) ∂μ)
      ≤ 5 * (Real.log p * (x / (p * Real.log x) + 1)) := by
    intro p hp
    have hp0 := hpos p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hSp p hp).one_lt.le
    have hlogp : 1 + Real.log (x / p) ≤ 2 * Real.log x := by
      have : Real.log (x / p) ≤ Real.log x :=
        Real.log_le_log (div_pos hx0 hp0) (div_le_self hx0.le hp1)
      linarith
    rw [integral_const_mul]
    have h := integral_discrepancy_le_extended hX hx0 hlog1 hp0 hlogp
    have hlp : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
    nlinarith [mul_le_mul_of_nonneg_left h hlp]
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [← Finset.mul_sum]
  have hsum := sum_log_prime_mul_smoothing_le hx1 (by linarith : (0 : ℝ) < Real.log x) hS
  have hl4 : Real.log 4 < 1.4 := log_four_lt
  have hA : x * (Real.log x + Real.log 4 + 4) / Real.log x ≤ 6.4 * x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  nlinarith

/-! ### The smoothing reduction for the extended sum -/

/-- **The smoothing reduction for the extended sum.**  There is `x₀` such that for `x ≥ x₀`,
`0 ≤ q ≤ 1` and `S` a set of primes up to `x` containing every prime of `(√x, x]`,

`(x/(8 log x))^q E[M^q] - (40x/log x)^q ≤ E[(∑_{p∈S} |∑_{m≤x/p} X^e(m)|²)^q]`,

`M = ∫_1^{√x/(1+1/log x)} |∑_{n≤z} X^e(n)|² dz/z²`. -/
theorem meanSquare_le_sum_extended :
    ∃ x₀ : ℝ, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ x q : ℝ, x₀ ≤ x → 0 ≤ q → q ≤ 1 →
        ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) → (∀ p ∈ S, (p : ℝ) ≤ x) →
          (∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) →
          (x / (8 * Real.log x)) ^ q
                * ∫ ω, (∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
                    ‖randomSum (fun ω => compMultExtension fun r => X r ω) z ω‖ ^ 2 / z ^ 2)
                      ^ q ∂μ
              - (40 * x / Real.log x) ^ q
            ≤ ∫ ω, (∑ p ∈ S, ‖randomSum (fun ω => compMultExtension fun r => X r ω)
                (x / p) ω‖ ^ 2) ^ q ∂μ := by
  obtain ⟨x₀, hchain⟩ := sum_normSq_ge (Ω := Ω)
  refine ⟨max x₀ 4, fun X μ hX x q hx hq0 hq1 S hSp hSx hS => ?_⟩
  haveI := hX.isProbabilityMeasure
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx4
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hxe : Real.exp 1 ≤ x := by nlinarith [Real.exp_one_lt_d9]
  set g : Ω → ArithmeticFunction ℂ := fun ω => compMultExtension fun r => X r ω with hgdef
  have hmeas : ∀ n : ℕ, Measurable fun ω => g ω n := fun n => hX.measurable_compMultExtension n
  have hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖g ω n‖ ≤ 1 := fun n =>
    hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n
  have hSsub : S ⊆ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime} := fun p hp =>
    Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨(hSp p hp).pos, Nat.le_floor (hSx p hp)⟩, hSp p hp⟩
  set w : ℝ := Real.sqrt x / (1 + 1 / Real.log x) with hwdef
  set M : Ω → ℝ := fun ω => ∫ z in Set.Ioc 1 w, ‖randomSum g z ω‖ ^ 2 / z ^ 2 with hMdef
  set D : Ω → ℝ := fun ω => ∑ p ∈ S, Real.log p * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), discrepancy g x p ω t) with hDdef
  set A : Ω → ℝ := fun ω => ∑ p ∈ S, ‖randomSum g (x / p) ω‖ ^ 2 with hAdef
  -- the pointwise inequality, with the sliver folded back
  have hpt0 : ∀ ω, x / (8 * Real.log x) * M ω - D ω / Real.log x ≤ A ω := by
    intro ω
    have h := hchain g ω x hxx₀ S hSp hSx hS
    have hsplit := meanSquare_split (f := g) hx4 ω
    have heq : x / (8 * Real.log x) * M ω
        = x / 8 * meanSquareIntegral g x ω - x / (8 * Real.log x) * sliverIntegral g x ω := by
      rw [hMdef]
      simp only
      rw [hsplit]
      field_simp
    rw [heq]
    exact h
  -- nonnegativity
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω =>
    setIntegral_nonneg measurableSet_Ioc fun z hz =>
      div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hD0 : ∀ ω, 0 ≤ D ω := by
    intro ω
    refine Finset.sum_nonneg fun p hp => mul_nonneg (Real.log_natCast_nonneg p) ?_
    refine mul_nonneg (by positivity) ?_
    exact setIntegral_nonneg measurableSet_Ioc fun t _ => discrepancy_nonneg g x p ω t
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => Finset.sum_nonneg fun p _ => by positivity
  have hP0 : ∀ ω, 0 ≤ x / (8 * Real.log x) * M ω := fun ω => mul_nonneg (by positivity) (hM0 ω)
  have hR0 : ∀ ω, 0 ≤ D ω / Real.log x := fun ω => div_nonneg (hD0 ω) hlog0.le
  -- integrability
  have hc1 : (1 : ℝ) ≤ w := one_le_sqrt_div hx4
  have hMi : Integrable M μ :=
    (integrable_meanSquare_prod_of hmeas hbd (c := 1) (d := w) le_rfl).integral_prod_left
  have hDi : Integrable D μ := integrable_extendedDiscrepancySum hX hx0.le hSp
  have hAi : Integrable A μ :=
    integrable_finsetSum _ fun p _ => integrable_normSq_randomSum_of hmeas hbd (x / p)
  have hPi : Integrable (fun ω => x / (8 * Real.log x) * M ω) μ := hMi.const_mul _
  have hRi : Integrable (fun ω => D ω / Real.log x) μ := hDi.div_const _
  have hPq := integrable_rpow_of_integrable hPi (Filter.Eventually.of_forall hP0) hq0 hq1
  have hRq := integrable_rpow_of_integrable hRi (Filter.Eventually.of_forall hR0) hq0 hq1
  have hAq := integrable_rpow_of_integrable hAi (Filter.Eventually.of_forall hA0) hq0 hq1
  have hpt : ∀ ω, (x / (8 * Real.log x) * M ω) ^ q - (D ω / Real.log x) ^ q ≤ A ω ^ q :=
    fun ω => rpow_sub_rpow_le_of_sub_le (hP0 ω) (hR0 ω) (hA0 ω) (by linarith [hpt0 ω]) hq0 hq1
  have hmain : (∫ ω, (x / (8 * Real.log x) * M ω) ^ q ∂μ) - ∫ ω, (D ω / Real.log x) ^ q ∂μ
      ≤ ∫ ω, A ω ^ q ∂μ := by
    rw [← integral_sub hPq hRq]
    exact integral_mono (hPq.sub hRq) hAq hpt
  have hPval : (∫ ω, (x / (8 * Real.log x) * M ω) ^ q ∂μ)
      = (x / (8 * Real.log x)) ^ q * ∫ ω, M ω ^ q ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      Real.mul_rpow (by positivity) (hM0 ω))
  have hRval : (∫ ω, (D ω / Real.log x) ^ q ∂μ) ≤ (40 * x / Real.log x) ^ q := by
    refine le_trans (integral_rpow_le_rpow_integral hq0 hq1
      (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (hR0 ω)) hRi hRq) ?_
    refine Real.rpow_le_rpow (integral_nonneg hR0) ?_ hq0
    rw [integral_div]
    exact div_le_div_of_nonneg_right (integral_sum_discrepancy_le_extended hX hxe hSsub)
      hlog0.le
  rw [hPval] at hmain
  linarith

end RMF
