/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Fluctuations
import RMF.Weighted.SmoothTail
import RMF.Analysis.TailParseval
import RMF.Weighted.EulerMomentBand

/-!
# The band tail of the truncation bound

The truncation error of a band `(y, z]` is

`𝒯_{y,z}(x) = ∑_{r ≤ x, r z-rough} X(r)r^{-1/2}·T(x/r)`,  `T(w) = ∑_{m > w} X(m)m^{-1/2}`,

with `m` squarefree and every prime factor of `m` in `(y, z]`: the rough variable carries only
tails.  This file holds the band tail `T = RMF.blockTailSum` and what the truncation bound for the
band (`RMF.exists_const_integral_rpow_norm_blockTruncationTail_le`) uses of it.

* **The decomposition** (`RMF.blockTruncationTail_eq_sum_rough_mul_blockTailSum`), in the shape
  `RMF.condExp_normSq_roughSmoothSum_sqfree` consumes: `T(x/r)` is measurable for the smooth
  `σ`-algebra (`RMF.measurable_smoothAlgebra_blockTailSum`) and bounded
  (`RMF.ae_norm_blockTailSum_le`).  It is the reindexing `RMF.sum_blockTruncationTailIndex_eq`.
* **The second moment**, `E|T(w)|² = ∑_{m > w} 1/m` (`RMF.integral_normSq_blockTailSum`).  Rankin
  (`RMF.blockTailSum_le_rankin`) at `δ = 1/log z` and Mertens at the shift `-1/(2 log z)` bound it
  by `e^{45}·κ·w^{-1/log z}`, `κ = log z/log y` (`RMF.integral_normSq_blockTailSum_le`), and by
  `e^{18}·log z·w^{-1/log z}` on the bottom band (`RMF.integral_normSq_blockTailSum_zero_le`).  At
  `w = x/r` this is `κ·e^{-V}·r^{1/log z}` up to the constant, `V = log x/log z`: the truncation
  bound's atom (`r = 1`) and its Rankin range.
* **Tail Plancherel for the band** (`RMF.integral_normSq_blockTailSum_eq_line`): tail Plancherel
  (`RMF.integral_normSq_tailSum_eq_line`) at the band's coefficients, whose Dirichlet polynomial is
  the band product (`RMF.sum_blockWeighted_cpow_eq_randomEulerProductIco`), read at `½ - c + it`
  after `t ↦ -t`.  Its integrand is integrable
  (`RMF.integrableOn_normSq_blockTailSum_mul_rpow`, through `RMF.blockTailSum_eq_sum_Ioc`).
* **Conditioning** (`RMF.integral_rpow_norm_blockTruncationTail_le`): the first step of the
  truncation bound, `E|𝒯|^{2q} ≤ E|T(x)|^{2q} + E[(∑_{1<r≤x} r⁻¹|T(x/r)|²)^q]`.
* **Smoothing** (`RMF.sum_blockTailTerm_le_setIntegral`,
  `RMF.integral_sum_setIntegral_normSq_blockTailSum_sub_le`): the steps of
  `Weighted/Conditional.lean`, stated there for any function, at the band tail.  The sieve and
  the principal term follow in `Weighted/BandTailSmoothing.lean`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The band tail and the decomposition -/

/-- `T_{y,z}(w) = ∑_{m > w} X(m)/√m` over the `y`-rough `z`-smooth `m`: the band tail of the
truncation bound.  The index set stops at `z#`, past which nothing squarefree is left on the
band. -/
noncomputable def blockTailSum (f : Ω → ArithmeticFunction ℂ) (y z : ℕ) (w : ℝ) (ω : Ω) : ℂ :=
  ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) |
      m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m ∧ ⌊w⌋₊ < m}, f ω m / (Real.sqrt m : ℂ)

/-- `⌊x⌋ < k·r` exactly when `⌊x/r⌋ < k`, for `r ≥ 1`. -/
lemma floor_lt_mul_iff_floor_div_lt {x : ℝ} {k r : ℕ} (hr : 0 < r) :
    ⌊x⌋₊ < k * r ↔ ⌊x / r⌋₊ < k := by
  rw [Nat.floor_div_natCast, Nat.div_lt_iff_lt_mul hr]

omit [MeasurableSpace Ω] in
/-- **The truncation error of a band is a rough sum of band tails**:
`𝒯_{y,z}(x) = ∑_{r ≤ x, r z-rough} X(r)r^{-1/2}·T_{y,z}(x/r)`.

The reindexing `RMF.sum_blockTruncationTailIndex_eq` at `g(n) = X(n)/√n`, the two sums swapped,
the constraint `kr > x` read as `k > x/r`, and the squarefree filters dropped since `X` vanishes
off the squarefrees.  `y ≤ z` is the reindexing's. -/
theorem blockTruncationTail_eq_sum_rough_mul_blockTailSum {X : ℕ → Ω → ℂ} {y z : ℕ}
    (hyz : y ≤ z) (x : ℝ) (ω : Ω) :
    blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω
      = ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r},
          (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * ((squarefreeExtension fun p => X p ω) r
            * blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω) := by
  classical
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ → ℂ,
      g = fun n => (squarefreeExtension fun p => X p ω) n / (Real.sqrt n : ℂ) := ⟨_, rfl⟩
  have hg : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n := by
    intro m n hmn
    rw [hgdef]
    dsimp only
    rw [(isMultiplicative_squarefreeExtension _).map_mul_of_coprime hmn, div_mul_div_comm,
      Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m), Complex.ofReal_mul]
  have hg0 : ∀ n : ℕ, ¬ Squarefree n → g n = 0 := fun n hn => by
    rw [hgdef]
    dsimp only
    rw [squarefreeExtension_apply_of_not_squarefree _ hn, zero_div]
  have hgT : ∀ w : ℝ, blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z w ω
      = ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) |
          m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m ∧ ⌊w⌋₊ < m}, g m := by
    intro w
    rw [blockTailSum, hgdef]
  have hr0 : ∀ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r ∧ Squarefree r}, 0 < r := by
    intro r hr
    have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hr).1).1
    omega
  -- the inner sum is the band tail at `x/r`
  have hT : ∀ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r ∧ Squarefree r},
      ∑ k ∈ {k ∈ Finset.Icc 1 (primorial z) |
          (k ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y k ∧ Squarefree k) ∧ ⌊x⌋₊ < k * r}, g k
        = blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω := by
    intro r hr
    rw [hgT]
    refine Finset.sum_subset (fun k hk => ?_) (fun k hk hk' => ?_)
    · simp only [Finset.mem_filter] at hk ⊢
      exact ⟨hk.1, hk.2.1.1, hk.2.1.2.1, (floor_lt_mul_iff_floor_div_lt (hr0 r hr)).1 hk.2.2⟩
    · simp only [Finset.mem_filter] at hk hk'
      exact hg0 k fun hsf => hk' ⟨hk.1, ⟨hk.2.1, hk.2.2.1, hsf⟩,
        (floor_lt_mul_iff_floor_div_lt (hr0 r hr)).2 hk.2.2.2⟩
  calc blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω
      = ∑ k ∈ {k ∈ Finset.Icc 1 (primorial z) |
            k ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y k ∧ Squarefree k},
          ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | (IsRough z r ∧ Squarefree r) ∧ ⌊x⌋₊ < k * r},
            g k * g r := by
        have hdef : blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω
            = ∑ n ∈ {n ∈ Finset.Icc 1 (primorial z * ⌊x⌋₊) |
                ⌊x⌋₊ < n ∧ IsRough y n ∧ roughPart z n ≤ ⌊x⌋₊ ∧ Squarefree n}, g n := by
          rw [blockTruncationTail, hgdef]
        rw [hdef, sum_blockTruncationTailIndex_eq hg hyz x]
        exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
    _ = ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r ∧ Squarefree r},
          ∑ k ∈ {k ∈ Finset.Icc 1 (primorial z) |
            (k ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y k ∧ Squarefree k) ∧ ⌊x⌋₊ < k * r},
            g k * g r := by
        refine Finset.sum_comm' fun k r => ?_
        simp only [Finset.mem_filter]
        tauto
    _ = ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r ∧ Squarefree r},
          g r * blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [← hT r hr, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    _ = ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r},
          g r * blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω := by
        refine Finset.sum_subset (fun r hr => ?_) (fun r hr hr' => ?_)
        · simp only [Finset.mem_filter] at hr ⊢
          exact ⟨hr.1, hr.2.1⟩
        · simp only [Finset.mem_filter] at hr hr'
          rw [hg0 r fun hsf => hr' ⟨hr.1, hr.2, hsf⟩, zero_mul]
    _ = _ := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hgdef]
        dsimp only
        rw [div_eq_mul_inv, Complex.ofReal_inv]
        ring

omit [MeasurableSpace Ω] in
/-- **The band tail is measurable for the smooth `σ`-algebra** at `z`: every index of it is
`z`-smooth. -/
lemma measurable_smoothAlgebra_blockTailSum {X : ℕ → Ω → ℂ} (y z : ℕ) (w : ℝ) :
    Measurable[smoothAlgebra X z]
      (blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z w) := by
  refine Finset.measurable_sum _ fun n hn => ?_
  exact (measurable_smoothAlgebra_squarefreeExtension (Finset.mem_filter.1 hn).2.1).div_const _

omit [MeasurableSpace Ω] in
/-- **A deterministic bound on the band tail**, at an `ω` where every value has norm at most one:
each weight is at most one and there are at most `z#` terms. -/
lemma norm_blockTailSum_le_of_bound {f : Ω → ArithmeticFunction ℂ} {ω : Ω}
    (hb : ∀ n, ‖f ω n‖ ≤ 1) (y z : ℕ) (w : ℝ) :
    ‖blockTailSum f y z w ω‖ ≤ (primorial z : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ k ∈ {m ∈ Finset.Icc 1 (primorial z) |
      m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m ∧ ⌊w⌋₊ < m},
      ‖f ω k / (Real.sqrt k : ℂ)‖ ≤ 1 := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
    have hk1R : (1 : ℝ) ≤ Real.sqrt k := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hk1)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_one_of_le₀ (le_trans (hb k) hk1R) (Real.sqrt_nonneg _)
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 hterm) ?_
  rw [nsmul_eq_mul, mul_one]
  exact_mod_cast le_trans (Finset.card_filter_le _ _) (by simp)

/-- **A crude almost-sure bound on the band tail**: every value has norm at most one and every
weight at most one, so `‖T(w)‖ ≤ z#`: `RMF.norm_blockTailSum_le_of_bound` on the almost-sure
event where every value has norm at most one.  Only integrability uses it. -/
lemma ae_norm_blockTailSum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (y z : ℕ) (w : ℝ) :
    ∀ᵐ ω ∂μ, ‖blockTailSum f y z w ω‖ ≤ (primorial z : ℝ) := by
  filter_upwards [MeasureTheory.ae_all_iff.2 fun n => hf.norm_apply_le_one n] with ω hω
  exact norm_blockTailSum_le_of_bound hω y z w

/-! ### The second moment -/

/-- **The second moment of the band tail is its harmonic mass**, `E|T(w)|² = ∑_{m > w} 1/m` over
the squarefree `y`-rough `z`-smooth `m`: orthogonality
(`RMF.integral_normSq_sum_div_sqrt_of_squarefree`) once the non-squarefree indices, where the
Rademacher function vanishes, are dropped. -/
theorem integral_normSq_blockTailSum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y z : ℕ) (w : ℝ) :
    (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z w ω‖ ^ 2 ∂μ)
      = ∑ m ∈ {m ∈ Finset.Ioc ⌊w⌋₊ (primorial z)
          | m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m ∧ Squarefree m}, ((m : ℝ))⁻¹ := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hidx : ∀ ω, blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z w ω
      = ∑ m ∈ {m ∈ Finset.Ioc ⌊w⌋₊ (primorial z)
          | m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m ∧ Squarefree m},
        (squarefreeExtension fun p => X p ω) m / (Real.sqrt m : ℂ) := by
    intro ω
    rw [blockTailSum]
    symm
    refine Finset.sum_subset (fun m hm => ?_) (fun m hm hm' => ?_)
    · simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hm ⊢
      exact ⟨⟨Nat.one_le_of_lt hm.1.1, hm.1.2⟩, hm.2.1, hm.2.2.1, hm.1.1⟩
    · simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hm hm'
      rw [squarefreeExtension_apply_of_not_squarefree _
        fun hs => hm' ⟨⟨hm.2.2.2, hm.1.2⟩, hm.2.1, hm.2.2.1, hs⟩, zero_div]
  simp_rw [hidx]
  exact integral_normSq_sum_div_sqrt_of_squarefree hRa
    (fun m hm => by
      have := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hm).1).1
      omega)
    (fun m hm => (Finset.mem_filter.1 hm).2.2.2)

/-- **Rankin and Mertens for the band tail.**  For `2 ≤ y ≤ z` and `w > 0`,
`E|T_{y,z}(w)|² ≤ e^{45}·(log z/log y)·w^{-1/log z}`.

`RMF.blockTailSum_le_rankin` at `δ = 1/log z`, the product `∏_{y<p≤z}(1 + p^{δ-1})` being at most
`exp ∑_{y<p≤z} p^{-(1-δ)}`, which is Mertens at the shift `σ = -δ/2`
(`RMF.sum_primesIco_rpow_signed_shift_le_log_div_add`, `2|σ| log z = 1`). -/
theorem integral_normSq_blockTailSum_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y z : ℕ} (hy : 2 ≤ y) (hyz : y ≤ z) {w : ℝ}
    (hw : 0 < w) :
    (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z w ω‖ ^ 2 ∂μ)
      ≤ Real.exp 45 * (Real.log z / Real.log y) * w ^ (-(Real.log z)⁻¹) := by
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ z := by exact_mod_cast hyz
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hδ : 0 < (Real.log z)⁻¹ := inv_pos.2 hlogz
  rw [integral_normSq_blockTailSum hX y z w]
  refine le_trans (blockTailSum_le_rankin y z hw hδ) ?_
  -- Mertens at the shift `σ = -1/(2 log z)`, where `p^{-(1+2σ)} = p^{δ-1}`
  have hσ : 2 * |(-((Real.log z)⁻¹ / 2))| * Real.log z ≤ 1 := le_of_eq (by
    rw [abs_neg, abs_of_pos (div_pos hδ two_pos),
      show 2 * ((Real.log z)⁻¹ / 2) * Real.log z = (Real.log z)⁻¹ * Real.log z by ring,
      inv_mul_cancel₀ hlogz.ne'])
  have hmert := sum_primesIco_rpow_signed_shift_le_log_div_add hy hyz hσ
  have hexp : ∀ p ∈ primesIco (y + 1) (z + 1),
      (p : ℝ) ^ (-(1 + 2 * -((Real.log z)⁻¹ / 2))) = (p : ℝ) ^ ((Real.log z)⁻¹ - 1) := by
    intro p _
    congr 1
    ring
  rw [Finset.sum_congr rfl hexp] at hmert
  have hprod : ∏ p ∈ primesIco (y + 1) (z + 1), (1 + (p : ℝ) ^ ((Real.log z)⁻¹ - 1))
      ≤ Real.exp 45 * (Real.log z / Real.log y) := by
    refine le_trans (Real.prod_one_add_le_exp_sum _ fun p =>
      Real.rpow_nonneg (Nat.cast_nonneg p) _) ?_
    calc Real.exp (∑ p ∈ primesIco (y + 1) (z + 1), (p : ℝ) ^ ((Real.log z)⁻¹ - 1))
        ≤ Real.exp (Real.log (Real.log z / Real.log y) + 45) := Real.exp_le_exp.2 hmert
      _ = Real.exp 45 * (Real.log z / Real.log y) := by
          rw [Real.exp_add, Real.exp_log (div_pos hlogz hlogy)]
          ring
  calc w ^ (-(Real.log z)⁻¹) * ∏ p ∈ primesIco (y + 1) (z + 1),
        (1 + (p : ℝ) ^ ((Real.log z)⁻¹ - 1))
      ≤ w ^ (-(Real.log z)⁻¹) * (Real.exp 45 * (Real.log z / Real.log y)) :=
        mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hw.le _)
    _ = Real.exp 45 * (Real.log z / Real.log y) * w ^ (-(Real.log z)⁻¹) := by ring

/-- **Rankin and Mertens for the bottom band's tail.**  For `z ≥ 2` and `w > 0`, over the
squarefree `z`-smooth `m > w`, `E|T_{0,z}(w)|² ≤ e^{18}·log z·w^{-1/log z}`.

As `RMF.integral_normSq_blockTailSum_le`, with the primes below `z` and the bottom band's Mertens
(`RMF.sum_primesBelow_rpow_signed_shift_le_log_log_add`). -/
theorem integral_normSq_blockTailSum_zero_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {z : ℕ} (hz : 2 ≤ z) {w : ℝ} (hw : 0 < w) :
    (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) 0 z w ω‖ ^ 2 ∂μ)
      ≤ Real.exp 18 * Real.log z * w ^ (-(Real.log z)⁻¹) := by
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hδ : 0 < (Real.log z)⁻¹ := inv_pos.2 hlogz
  rw [integral_normSq_blockTailSum hX 0 z w]
  refine le_trans (blockTailSum_le_rankin 0 z hw hδ) ?_
  rw [zero_add, primesIco_one]
  have hσ : 2 * |(-((Real.log z)⁻¹ / 2))| * Real.log z ≤ 1 := le_of_eq (by
    rw [abs_neg, abs_of_pos (div_pos hδ two_pos),
      show 2 * ((Real.log z)⁻¹ / 2) * Real.log z = (Real.log z)⁻¹ * Real.log z by ring,
      inv_mul_cancel₀ hlogz.ne'])
  have hmert := sum_primesBelow_rpow_signed_shift_le_log_log_add hz hσ
  have hexp : ∀ p ∈ Nat.primesBelow (z + 1),
      (p : ℝ) ^ (-(1 + 2 * -((Real.log z)⁻¹ / 2))) = (p : ℝ) ^ ((Real.log z)⁻¹ - 1) := by
    intro p _
    congr 1
    ring
  rw [Finset.sum_congr rfl hexp] at hmert
  have hprod : ∏ p ∈ Nat.primesBelow (z + 1), (1 + (p : ℝ) ^ ((Real.log z)⁻¹ - 1))
      ≤ Real.exp 18 * Real.log z := by
    refine le_trans (Real.prod_one_add_le_exp_sum _ fun p =>
      Real.rpow_nonneg (Nat.cast_nonneg p) _) ?_
    calc Real.exp (∑ p ∈ Nat.primesBelow (z + 1), (p : ℝ) ^ ((Real.log z)⁻¹ - 1))
        ≤ Real.exp (Real.log (Real.log z) + 18) := Real.exp_le_exp.2 hmert
      _ = Real.exp 18 * Real.log z := by
          rw [Real.exp_add, Real.exp_log hlogz]
          ring
  calc w ^ (-(Real.log z)⁻¹) * ∏ p ∈ Nat.primesBelow (z + 1),
        (1 + (p : ℝ) ^ ((Real.log z)⁻¹ - 1))
      ≤ w ^ (-(Real.log z)⁻¹) * (Real.exp 18 * Real.log z) :=
        mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hw.le _)
    _ = Real.exp 18 * Real.log z * w ^ (-(Real.log z)⁻¹) := by ring

/-! ### Tail Plancherel for the band -/

omit [MeasurableSpace Ω] in
/-- The band tail as a tail sum over `(⌊w⌋, z#]`, the band's coefficients carried by an indicator:
the shape tail Plancherel (`RMF.integral_normSq_tailSum_eq_line`) reads. -/
lemma blockTailSum_eq_sum_Ioc (f : Ω → ArithmeticFunction ℂ) (y z : ℕ) (w : ℝ) (ω : Ω) :
    blockTailSum f y z w ω
      = ∑ n ∈ Finset.Ioc ⌊w⌋₊ (primorial z),
          (if n ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y n then f ω n / (Real.sqrt n : ℂ)
            else 0) := by
  have hset : {m ∈ Finset.Icc 1 (primorial z) |
        m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m ∧ ⌊w⌋₊ < m}
      = {m ∈ Finset.Ioc ⌊w⌋₊ (primorial z) | m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨-, h2⟩, h3, h4, h5⟩
      exact ⟨⟨h5, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨Nat.one_le_of_lt h1, h2⟩, h3, h4, h1⟩
  rw [blockTailSum, hset, Finset.sum_filter]

omit [MeasurableSpace Ω] in
/-- **The band's Plancherel integrand is integrable**: `|T(w)|² w^{2c-1}` on `w > 0`, for `c > 0`.
The companion of `RMF.integral_normSq_blockTailSum_eq_line`, which as an equation between
integrals could hold vacuously; it is `RMF.integrableOn_norm_tail_mul_rpow` at the band's
coefficients (`RMF.blockTailSum_eq_sum_Ioc`). -/
lemma integrableOn_normSq_blockTailSum_mul_rpow (f : Ω → ArithmeticFunction ℂ) (y z : ℕ) {c : ℝ}
    (hc : 0 < c) (ω : Ω) :
    IntegrableOn (fun w : ℝ => ‖blockTailSum f y z w ω‖ ^ 2 * w ^ (2 * c - 1)) (Set.Ioi 0) := by
  simp_rw [blockTailSum_eq_sum_Ioc]
  exact integrableOn_norm_tail_mul_rpow (primorial z) _ (by linarith) two_ne_zero

omit [MeasurableSpace Ω] in
/-- **Tail Plancherel for the band.**  For `c > 0`,
`∫₀^∞ |T_{y,z}(w)|² w^{2c-1} dw = (2π)⁻¹ ∫_ℝ |F_{y,z}(½-c+it)|²/|c+it|² dt`.

`RMF.integral_normSq_tailSum_eq_line` at the band's coefficients `aₙ = X(n)/√n`, `n` up to `z#`:
their Dirichlet polynomial `∑ aₙ n^{c+it}` is `F_{y,z}(½-c-it)`
(`RMF.sum_blockWeighted_cpow_eq_randomEulerProductIco`), and `t ↦ -t` leaves `|c+it|` unchanged. -/
theorem integral_normSq_blockTailSum_eq_line {X : ℕ → Ω → ℂ} (y z : ℕ) {c : ℝ} (hc : 0 < c)
    (ω : Ω) :
    (∫ w in Set.Ioi (0 : ℝ),
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z w ω‖ ^ 2
          * w ^ (2 * c - 1))
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
              ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
            / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ, a = fun n =>
      if n ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y n then
        (squarefreeExtension fun p => X p ω) n / (Real.sqrt n : ℂ) else 0 := ⟨_, rfl⟩
  -- the band tail is the tail sum of `a`
  have htail : ∀ w : ℝ, blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z w ω
      = ∑ n ∈ Finset.Ioc ⌊w⌋₊ (primorial z), a n := by
    intro w
    rw [blockTailSum_eq_sum_Ioc, ha]
  -- the Dirichlet polynomial of `a` is the band product at the reflected point
  have hpoly : ∀ t : ℝ,
      ∑ n ∈ Finset.Icc 1 (primorial z), a n * (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        = randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
            ((1 / 2 : ℂ) - (c : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) ω := by
    intro t
    rw [← sum_blockWeighted_cpow_eq_randomEulerProductIco, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := (Finset.mem_Icc.1 hn).1; omega)
    rw [ha]
    dsimp only
    split_ifs with h
    · have hsq : (((Real.sqrt n : ℝ) : ℂ))⁻¹ = (n : ℂ) ^ (-(1 / 2 : ℂ)) := by
        rw [Complex.cpow_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]
        norm_num
      rw [div_eq_mul_inv, hsq, mul_assoc, ← Complex.cpow_add _ _ hn0]
      congr 2
      push_cast
      ring
    · rw [zero_mul]
  simp_rw [htail]
  rw [integral_normSq_tailSum_eq_line c (primorial z) a hc]
  congr 1
  simp_rw [hpoly]
  -- reflect `t ↦ -t`
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun u : ℝ =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
          ((1 / 2 : ℂ) - (c : ℂ) + (u : ℂ) * Complex.I) ω
        / ((c : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2 := ⟨_, rfl⟩
  have hpt : ∀ t : ℝ,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
          ((1 / 2 : ℂ) - (c : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) ω
        / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = G (-1 * t) := by
    intro t
    rw [hG, neg_one_mul]
    dsimp only
    rw [norm_div, norm_div, div_pow, div_pow, Complex.sq_norm ((c : ℂ) + (t : ℂ) * Complex.I),
      Complex.sq_norm ((c : ℂ) + ((-t : ℝ) : ℂ) * Complex.I), Complex.normSq_add_mul_I,
      Complex.normSq_add_mul_I, neg_sq]
  calc (∫ t : ℝ, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) ω
        / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      = ∫ t : ℝ, G (-1 * t) := integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = |(-1 : ℝ)⁻¹| • ∫ t : ℝ, G t := MeasureTheory.Measure.integral_comp_mul_left G (-1)
    _ = ∫ t : ℝ, G t := by norm_num
    _ = _ := by rw [hG]

/-! ### Conditioning -/

omit [MeasurableSpace Ω] in
/-- The bottom band's truncation error is the block one at `y = 0`, every integer being
`0`-rough. -/
lemma blockTruncationTail_zero (f : Ω → ArithmeticFunction ℂ) (z : ℕ) (x : ℝ) (ω : Ω) :
    blockTruncationTail f 0 z x ω = truncationTail f z x ω := by
  have h0 : ∀ n : ℕ, IsRough 0 n := fun n => isRough_iff.2 fun p hp _ => hp.pos
  rw [blockTruncationTail, truncationTail]
  exact Finset.sum_congr (Finset.filter_congr fun n _ => by simp [h0 n]) fun _ _ => rfl

/-- The summand of the band's rough sum, `r⁻¹ |T_{y,z}(x/r)|²`: the band-tail counterpart of
`RMF.weightedRoughTerm`. -/
noncomputable def blockTailTerm (f : Ω → ArithmeticFunction ℂ) (y z : ℕ) (x : ℝ) (ω : Ω)
    (r : ℕ) : ℝ := (r : ℝ)⁻¹ * ‖blockTailSum f y z (x / r) ω‖ ^ 2

omit [MeasurableSpace Ω] in
lemma blockTailTerm_nonneg (f : Ω → ArithmeticFunction ℂ) (y z : ℕ) (x : ℝ) (ω : Ω) (r : ℕ) :
    0 ≤ blockTailTerm f y z x ω r := by
  rw [blockTailTerm]
  positivity

/-- **The band's rough sums have integrable `q`-th powers**, over any set of positive indices:
measurable, and at most `#s·(z#)²` almost surely. -/
lemma integrable_rpow_sum_blockTailTerm {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y z : ℕ) (x : ℝ)
    {s : Finset ℕ} (hs : ∀ r ∈ s, 1 ≤ r) {q : ℝ} (hq0 : 0 ≤ q) :
    Integrable (fun ω => (∑ r ∈ s,
      blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q) μ := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hle := smoothAlgebra_le hX z
  have hmeas : Measurable fun ω => ∑ r ∈ s,
      blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r := by
    refine Finset.measurable_sum _ fun r _ => ?_
    exact measurable_const.mul
      (((measurable_smoothAlgebra_blockTailSum y z (x / r)).mono hle le_rfl).norm.pow_const 2)
  have hbd : ∀ᵐ ω ∂μ, ∑ r ∈ s,
      blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r
        ≤ (s.card : ℝ) * (primorial z : ℝ) ^ 2 := by
    have hall : ∀ r ∈ s, ∀ᵐ ω ∂μ,
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω‖
          ≤ (primorial z : ℝ) := fun r _ => ae_norm_blockTailSum_le hRa y z (x / r)
    filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
    calc ∑ r ∈ s, blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r
        ≤ ∑ _r ∈ s, (primorial z : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hs r hr
          rw [blockTailTerm]
          calc (r : ℝ)⁻¹ * ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z
                (x / r) ω‖ ^ 2
              ≤ 1 * (primorial z : ℝ) ^ 2 :=
                mul_le_mul (inv_le_one_of_one_le₀ hr1)
                  (pow_le_pow_left₀ (norm_nonneg _) (hω r hr) 2) (by positivity) zero_le_one
            _ = (primorial z : ℝ) ^ 2 := one_mul _
      _ = (s.card : ℝ) * (primorial z : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have h0 : ∀ ω, (0 : ℝ) ≤ ∑ r ∈ s,
      blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r :=
    fun ω => Finset.sum_nonneg fun r _ => blockTailTerm_nonneg _ _ _ _ _ _
  refine (memLp_top_of_bound (hmeas.pow_const q).aestronglyMeasurable
    (((s.card : ℝ) * (primorial z : ℝ) ^ 2) ^ q) ?_).integrable le_top
  filter_upwards [hbd] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (h0 ω) q)]
  exact Real.rpow_le_rpow (h0 ω) hω hq0

/-- **The rough sum of band tails is bounded almost surely**, by `⌊x⌋·z#`: each weight and each
value has norm at most one, and each band tail is at most `z#`. -/
lemma ae_norm_sum_rough_mul_blockTailSum_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y z : ℕ) (x : ℝ) :
    ∀ᵐ ω ∂μ, ‖∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r},
        (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * ((squarefreeExtension fun p => X p ω) r
          * blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω)‖
      ≤ ((Finset.Icc 1 ⌊x⌋₊).card : ℝ) * (primorial z : ℝ) := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hall : ∀ r ∈ Finset.Icc 1 ⌊x⌋₊, ∀ᵐ ω ∂μ,
      ‖(squarefreeExtension fun p => X p ω) r‖ ≤ 1
        ∧ ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω‖
          ≤ (primorial z : ℝ) :=
    fun r _ => (hRa.norm_apply_le_one r).and (ae_norm_blockTailSum_le hRa y z (x / r))
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun r _ _ => norm_nonneg _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ (primorial z : ℝ) fun r hr => ?_)
    (nsmul_eq_mul _ _).le
  have hr1 : (1 : ℝ) ≤ Real.sqrt r := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_Icc.1 hr).1)
  have hc : ‖(((Real.sqrt r)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    exact inv_le_one_of_one_le₀ hr1
  rw [norm_mul, norm_mul]
  calc ‖(((Real.sqrt r)⁻¹ : ℝ) : ℂ)‖ * (‖(squarefreeExtension fun p => X p ω) r‖
        * ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω‖)
      ≤ 1 * (1 * (primorial z : ℝ)) :=
        mul_le_mul hc (mul_le_mul (hω r hr).1 (hω r hr).2 (norm_nonneg _) zero_le_one)
          (by positivity) zero_le_one
    _ = (primorial z : ℝ) := by ring

/-- **Conditioning for the band's truncation error**, the first step of the truncation bound.  For
`y ≤ z`, `x ≥ 1` and `0 ≤ q ≤ 1`,
`E|𝒯_{y,z}(x)|^{2q} ≤ E|T(x)|^{2q} + E[(∑_{1 < r ≤ x} r⁻¹|T(x/r)|²)^q]`, `r` squarefree and
`z`-rough, `T = RMF.blockTailSum`.  Conditional Jensen
(`RMF.integral_rpow_norm_le_integral_condExp_rpow`) on the rough sum of band tails, whose
conditional second moment is `RMF.condExp_normSq_roughSmoothSum_sqfree`; the term `r = 1` peeled
off by subadditivity (`RMF.integral_rpow_sum_le_add_integral_rpow_erase`). -/
theorem integral_rpow_norm_blockTruncationTail_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {y z : ℕ} (hyz : y ≤ z)
    {x : ℝ} (hx : 1 ≤ x) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
        ^ (2 * q) ∂μ)
      ≤ (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ (2 * q) ∂μ)
        + ∫ ω, (∑ r ∈ ({r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r ∧ Squarefree r}).erase 1,
            blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q ∂μ := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hle := smoothAlgebra_le hX z
  haveI : SigmaFinite (μ.trim hle) := (isFiniteMeasure_trim hle).toSigmaFinite
  have hA1 : ∀ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r ∧ Squarefree r}, 1 ≤ r :=
    fun r hr => (Finset.mem_Icc.1 (Finset.mem_filter.1 hr).1).1
  have h1A : 1 ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r ∧ Squarefree r} := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, Nat.le_floor (by exact_mod_cast hx)⟩, isRough_one z, squarefree_one⟩
  have hSm : Measurable fun ω => ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r},
      (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * ((squarefreeExtension fun p => X p ω) r
        * blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω) :=
    Finset.measurable_sum _ fun r _ => measurable_const.mul ((hRa.measurable_apply r).mul
      ((measurable_smoothAlgebra_blockTailSum y z (x / r)).mono hle le_rfl))
  have hid := condExp_normSq_roughSmoothSum_sqfree (x := x) hX
    (G := fun r => blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r))
    (B := fun _ => (primorial z : ℝ))
    (fun r => measurable_smoothAlgebra_blockTailSum y z (x / r))
    (fun r => ae_norm_blockTailSum_le hRa y z (x / r))
  have hsplit := integral_rpow_sum_le_add_integral_rpow_erase (μ := μ)
    (g := fun r ω => blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r)
    h1A (fun r ω => blockTailTerm_nonneg _ _ _ _ _ _) hq0 hq1
    (integrable_rpow_sum_blockTailTerm hX y z x hA1 hq0)
    (by simpa using integrable_rpow_sum_blockTailTerm hX y z x (s := {1}) (by simp) hq0)
    (integrable_rpow_sum_blockTailTerm hX y z x
      (fun r hr => hA1 r (Finset.mem_of_mem_erase hr)) hq0)
  have hpow : ∀ ω, (blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω 1) ^ q
      = ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ (2 * q) := by
    intro ω
    rw [blockTailTerm, Nat.cast_one, inv_one, one_mul, div_one,
      ← Real.rpow_natCast ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ 2,
      ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  calc (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
          ^ (2 * q) ∂μ)
      = ∫ ω, ‖∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r},
          (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * ((squarefreeExtension fun p => X p ω) r
            * blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω)‖
            ^ (2 * q) ∂μ := by
        simp_rw [blockTruncationTail_eq_sum_rough_mul_blockTailSum hyz x]
    _ ≤ _ := integral_rpow_norm_le_integral_condExp_rpow hle hSm
        (ae_norm_sum_rough_mul_blockTailSum_le hX y z x) hq0 hq1
    _ = ∫ ω, (∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r ∧ Squarefree r},
          blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hid] with ω hω
        rw [hω]
        rfl
    _ ≤ _ := hsplit
    _ = _ := by simp_rw [hpow]

/-! ### Smoothing the band tail

The truncation bound's smoothing replaces each `r⁻¹|T(x/r)|²` by an average of `|T(x/t)|²` over
`t ∈ [r, r(1+η)]`.  The steps of `Weighted/Conditional.lean` are stated for any function; what the
band tail has to supply is measurability as a step function of its truncation point, a bound, and
the mean square of its difference across a window. -/

omit [MeasurableSpace Ω] in
/-- The band tail depends on its truncation point only through `⌊·⌋₊`, so it is a step function
of it. -/
lemma measurable_blockTailSum_truncation (f : Ω → ArithmeticFunction ℂ) (y z : ℕ) (ω : Ω) :
    Measurable fun w : ℝ => blockTailSum f y z w ω := by
  have h : (fun w : ℝ => blockTailSum f y z w ω)
      = (fun n : ℕ => ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) |
          m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m ∧ n < m}, f ω m / (Real.sqrt m : ℂ))
        ∘ (fun w : ℝ => ⌊w⌋₊) := rfl
  rw [h]
  exact measurable_from_top.comp Nat.measurable_floor

omit [MeasurableSpace Ω] in
/-- The averaged integrand of the band tail is interval integrable: measurable, and at most
`(z#)²` for an `ω` at which every value has norm at most one. -/
lemma intervalIntegrable_normSq_blockTailSum {f : Ω → ArithmeticFunction ℂ} {ω : Ω}
    (hb : ∀ n, ‖f ω n‖ ≤ 1) (y z : ℕ) {x r s : ℝ} (hrs : r ≤ s) :
    IntervalIntegrable (fun t => ‖blockTailSum f y z (x / t) ω‖ ^ 2) volume r s := by
  have hmeas : Measurable fun t : ℝ => ‖blockTailSum f y z (x / t) ω‖ ^ 2 :=
    ((measurable_blockTailSum_truncation f y z ω).comp
      (measurable_const.div measurable_id)).norm.pow_const 2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hrs]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := (primorial z : ℝ) ^ 2)
    measure_Ioc_lt_top.ne hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  change ‖‖blockTailSum f y z (x / t) ω‖ ^ 2‖ ≤ (primorial z : ℝ) ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_blockTailSum_le_of_bound hb y z _) 2

omit [MeasurableSpace Ω] in
/-- The difference integrand of the band tail is interval integrable, at most `(2z#)²`. -/
lemma intervalIntegrable_normSq_blockTailSum_sub {f : Ω → ArithmeticFunction ℂ} {ω : Ω}
    (hb : ∀ n, ‖f ω n‖ ≤ 1) (y z : ℕ) {x r s : ℝ} (hrs : r ≤ s) :
    IntervalIntegrable
      (fun t => ‖blockTailSum f y z (x / r) ω - blockTailSum f y z (x / t) ω‖ ^ 2)
      volume r s := by
  have hmeas : Measurable fun t : ℝ =>
      ‖blockTailSum f y z (x / r) ω - blockTailSum f y z (x / t) ω‖ ^ 2 :=
    (measurable_const.sub ((measurable_blockTailSum_truncation f y z ω).comp
      (measurable_const.div measurable_id))).norm.pow_const 2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hrs]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := (2 * (primorial z : ℝ)) ^ 2)
    measure_Ioc_lt_top.ne hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  change ‖‖blockTailSum f y z (x / r) ω - blockTailSum f y z (x / t) ω‖ ^ 2‖
    ≤ (2 * (primorial z : ℝ)) ^ 2
  have h1 := norm_blockTailSum_le_of_bound hb y z (x / r)
  have h2 := norm_blockTailSum_le_of_bound hb y z (x / t)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (le_trans (norm_sub_le _ _) (by linarith)) 2

omit [MeasurableSpace Ω] in
/-- **The smoothing step for the band, at a fixed `ω`**: `RMF.sum_inv_mul_normSq_le_setIntegral`
at `G = T_{y,z}`, its interval integrability from the crude bound `‖T‖ ≤ z#`. -/
theorem sum_blockTailTerm_le_setIntegral {f : Ω → ArithmeticFunction ℂ} {ω : Ω}
    (hb : ∀ n, ‖f ω n‖ ≤ 1) (y z : ℕ) {x η : ℝ} (hη : 0 < η) {S : Finset ℕ}
    (hS : ∀ r ∈ S, 0 < r) {T : Set ℝ} (hTm : MeasurableSet T) {b : ℝ → ℝ}
    (hsub : ∀ r ∈ S, Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)) ⊆ T)
    (hbd : ∀ t ∈ T, ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t ≤ b t)
    (hint : ∀ r ∈ S, IntegrableOn (fun t => (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator
            (fun t => ‖blockTailSum f y z (x / t) ω‖ ^ 2) t) T volume)
    (hintT : IntegrableOn (fun t => ‖blockTailSum f y z (x / t) ω‖ ^ 2 * b t) T volume) :
    ∑ r ∈ S, blockTailTerm f y z x ω r
      ≤ (2 / η) * (∫ t in T, ‖blockTailSum f y z (x / t) ω‖ ^ 2 * b t)
        + (1 / η) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
              ‖blockTailSum f y z (x / r) ω - blockTailSum f y z (x / t) ω‖ ^ 2))
              / ((r : ℝ)) ^ 2 :=
  sum_inv_mul_normSq_le_setIntegral (fun u => blockTailSum f y z u ω) hη hS
    (fun r _ => intervalIntegrable_normSq_blockTailSum hb y z
      (le_mul_of_one_le_right (Nat.cast_nonneg r) (by linarith)))
    (fun r _ => intervalIntegrable_normSq_blockTailSum_sub hb y z
      (le_mul_of_one_le_right (Nat.cast_nonneg r) (by linarith)))
    hTm hsub hbd hint hintT

omit [MeasurableSpace Ω] in
/-- **Two band tails differ by a window sum**: for `⌊v⌋ ≤ ⌊u⌋`,
`T(v) = T(u) + ∑_{⌊v⌋ < m ≤ ⌊u⌋} X(m)/√m` over the band. -/
lemma blockTailSum_eq_add_sum_window (f : Ω → ArithmeticFunction ℂ) (y z : ℕ) {u v : ℝ}
    (huv : ⌊v⌋₊ ≤ ⌊u⌋₊) (ω : Ω) :
    blockTailSum f y z v ω = blockTailSum f y z u ω
      + ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) | m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m
          ∧ (⌊v⌋₊ < m ∧ m ≤ ⌊u⌋₊)}, f ω m / (Real.sqrt m : ℂ) := by
  rw [blockTailSum, blockTailSum, ← Finset.sum_union]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext m
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hm, hs, hr, hv⟩
      by_cases hmu : ⌊u⌋₊ < m
      · exact Or.inl ⟨hm, hs, hr, hmu⟩
      · exact Or.inr ⟨hm, hs, hr, hv, not_lt.1 hmu⟩
    · rintro (⟨hm, hs, hr, hu⟩ | ⟨hm, hs, hr, hv, -⟩)
      · exact ⟨hm, hs, hr, lt_of_le_of_lt huv hu⟩
      · exact ⟨hm, hs, hr, hv⟩
  · refine Finset.disjoint_filter.2 fun m _ h1 h2 => ?_
    exact absurd h1.2.2 (not_lt.2 h2.2.2.2)

/-- **The mean square of the difference of two band tails**: the harmonic mass of the window,
`E|T(u) - T(v)|² ≤ #(⌊v⌋, ⌊u⌋]/(⌊v⌋+1)` for `⌊v⌋ ≤ ⌊u⌋`.  Orthogonality on the squarefree band
integers of the window (`RMF.integral_normSq_sum_div_sqrt_of_squarefree`), then
`RMF.sum_inv_Ioc_le`. -/
theorem integral_normSq_blockTailSum_sub_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y z : ℕ) {u v : ℝ} (huv : ⌊v⌋₊ ≤ ⌊u⌋₊) :
    (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z u ω
        - blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z v ω‖ ^ 2 ∂μ)
      ≤ ((Finset.Ioc ⌊v⌋₊ ⌊u⌋₊).card : ℝ) / (⌊v⌋₊ + 1) := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hdiff : ∀ ω, blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z u ω
        - blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z v ω
      = -∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) | m ∈ Nat.smoothNumbers (z + 1)
          ∧ IsRough y m ∧ Squarefree m ∧ (⌊v⌋₊ < m ∧ m ≤ ⌊u⌋₊)},
          (squarefreeExtension fun p => X p ω) m / (Real.sqrt m : ℂ) := by
    intro ω
    rw [blockTailSum_eq_add_sum_window _ y z huv ω]
    have hsq : ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) | m ∈ Nat.smoothNumbers (z + 1)
          ∧ IsRough y m ∧ Squarefree m ∧ (⌊v⌋₊ < m ∧ m ≤ ⌊u⌋₊)},
          (squarefreeExtension fun p => X p ω) m / (Real.sqrt m : ℂ)
        = ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) | m ∈ Nat.smoothNumbers (z + 1)
          ∧ IsRough y m ∧ (⌊v⌋₊ < m ∧ m ≤ ⌊u⌋₊)},
          (squarefreeExtension fun p => X p ω) m / (Real.sqrt m : ℂ) := by
      refine Finset.sum_subset (fun m hm => ?_) (fun m hm hm' => ?_)
      · simp only [Finset.mem_filter] at hm ⊢
        exact ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.2⟩
      · simp only [Finset.mem_filter] at hm hm'
        rw [squarefreeExtension_apply_of_not_squarefree _
          fun hs => hm' ⟨hm.1, hm.2.1, hm.2.2.1, hs, hm.2.2.2⟩, zero_div]
    rw [hsq]
    ring
  simp_rw [hdiff, norm_neg]
  refine le_trans (le_of_eq (integral_normSq_sum_div_sqrt_of_squarefree hRa
    (fun m hm => by
      have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1
      omega)
    (fun m hm => by exact (Finset.mem_filter.1 hm).2.2.2.1))) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => ?_)
    (fun m _ _ => inv_nonneg.2 (Nat.cast_nonneg m))) (sum_inv_Ioc_le _ _)
  simp only [Finset.mem_filter] at hm
  exact Finset.mem_Ioc.2 hm.2.2.2.2

/-- **The mean square of the smoothing difference of the band tail on a short window**: for
`t ∈ [r, r(1+η)]`, `E|T(x/r) - T(x/t)|² ≤ η + (1+η)r/x`. -/
theorem integral_normSq_blockTailSum_sub_le_of_mem_Icc {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y z : ℕ) {x r t η : ℝ} (hx : 0 < x) (hr : 0 < r)
    (ht : t ∈ Set.Icc r (r * (1 + η))) :
    (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω
        - blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / t) ω‖ ^ 2 ∂μ)
      ≤ η + (1 + η) * r / x :=
  le_trans (integral_normSq_blockTailSum_sub_le hX y z
    (Nat.floor_le_floor (div_le_div_of_nonneg_left hx.le hr ht.1)))
    (card_Ioc_floor_div_div_le hx hr ht)

omit [MeasurableSpace Ω] in
/-- The band tail over the fixed index set of the band, the truncation carried by an indicator. -/
lemma blockTailSum_eq_sum_ite (f : Ω → ArithmeticFunction ℂ) (y z : ℕ) (w : ℝ) (ω : Ω) :
    blockTailSum f y z w ω
      = ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) | m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m},
          (if ⌊w⌋₊ < m then f ω m / (Real.sqrt m : ℂ) else 0) := by
  rw [blockTailSum, ← Finset.sum_filter, Finset.filter_filter]
  exact Finset.sum_congr (Finset.filter_congr fun m _ => by simp only [and_assoc]) fun _ _ => rfl

omit [MeasurableSpace Ω] in
/-- **A crude bound on the band tail, with no hypothesis on the values**: at most the sum of the
moduli of the band's weights, whatever the truncation point. -/
lemma norm_blockTailSum_le_sum (f : Ω → ArithmeticFunction ℂ) (y z : ℕ) (w : ℝ) (ω : Ω) :
    ‖blockTailSum f y z w ω‖
      ≤ ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) | m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m},
          ‖f ω m / (Real.sqrt m : ℂ)‖ := by
  rw [blockTailSum_eq_sum_ite]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m _ => ?_)
  split_ifs
  · exact le_rfl
  · rw [norm_zero]
    exact norm_nonneg _

/-- **The band's smoothing difference is jointly integrable** on `Ω × (r, s]`: jointly measurable,
the truncation being an indicator over the fixed index set, and at most `(2z#)²` almost surely. -/
theorem integrable_uncurry_normSq_blockTailSum_sub {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y z : ℕ) (x r s : ℝ) :
    Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω
          - blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / t) ω‖ ^ 2)
      (μ.prod (volume.restrict (Set.Ioc r s))) := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc r s)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have h1 : Measurable fun p : Ω × ℝ =>
      blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) p.1 :=
    ((measurable_smoothAlgebra_blockTailSum y z (x / r)).mono (smoothAlgebra_le hX z)
      le_rfl).comp measurable_fst
  have h2 : Measurable fun p : Ω × ℝ =>
      blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / p.2) p.1 := by
    simp_rw [blockTailSum_eq_sum_ite]
    refine Finset.measurable_sum _ fun m _ => ?_
    have hfloor : Measurable fun p : Ω × ℝ => ⌊x / p.2⌋₊ :=
      Nat.measurable_floor.comp (measurable_const.div measurable_snd)
    exact Measurable.ite (measurableSet_lt hfloor measurable_const)
      (((hRa.measurable_apply m).comp measurable_fst).div_const _) measurable_const
  have hmeas : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω
        - blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / t) ω‖ ^ 2) :=
    (h1.sub h2).norm.pow_const 2
  have hbdd : ∀ᵐ ω ∂μ, ∀ n, ‖(squarefreeExtension fun p => X p ω) n‖ ≤ 1 :=
    MeasureTheory.ae_all_iff.2 fun n => hRa.norm_apply_le_one n
  have hbddP : ∀ᵐ p ∂(μ.prod (volume.restrict (Set.Ioc r s))),
      ∀ n, ‖(squarefreeExtension fun q => X q p.1) n‖ ≤ 1 :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hbdd
  have hbound : ∀ᵐ p ∂(μ.prod (volume.restrict (Set.Ioc r s))),
      ‖(Function.uncurry fun (ω : Ω) (t : ℝ) =>
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω
          - blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / t) ω‖ ^ 2) p‖
        ≤ (2 * (primorial z : ℝ)) ^ 2 := by
    filter_upwards [hbddP] with p hb
    change ‖‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) p.1
        - blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / p.2) p.1‖ ^ 2‖
      ≤ (2 * (primorial z : ℝ)) ^ 2
    have hb1 := norm_blockTailSum_le_of_bound (f := fun ω => squarefreeExtension fun p => X p ω)
      hb y z (x / r)
    have hb2 := norm_blockTailSum_le_of_bound (f := fun ω => squarefreeExtension fun p => X p ω)
      hb y z (x / p.2)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (le_trans (norm_sub_le _ _) (by linarith)) 2
  exact (memLp_top_of_bound hmeas.aestronglyMeasurable ((2 * (primorial z : ℝ)) ^ 2)
    hbound).integrable le_top

/-- **The expectation of the band's smoothing error**: each window `[r, r(1+η)]` contributes
`2η(η + (1+η)r/x)/r`.  `RMF.integral_sum_setIntegral_normSq_sub_le_of_integrable` at `G = T_{y,z}`,
with `RMF.integrable_uncurry_normSq_blockTailSum_sub` and
`RMF.integral_normSq_blockTailSum_sub_le_of_mem_Icc`. -/
theorem integral_sum_setIntegral_normSq_blockTailSum_sub_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y z : ℕ) {x η : ℝ}
    (hx : 0 < x) (hη : 0 < η) {S : Finset ℕ} (hS : ∀ r ∈ S, 0 < r) :
    (∫ ω, ∑ r ∈ S, (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω
          - blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / t) ω‖ ^ 2))
        / ((r : ℝ)) ^ 2 ∂μ)
      ≤ ∑ r ∈ S, 2 * η * (η + (1 + η) * (r : ℝ) / x) / (r : ℝ) :=
  integral_sum_setIntegral_normSq_sub_le_of_integrable
    (fun ω u => blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z u ω) hx hη hS
    (fun r _ => integrable_uncurry_normSq_blockTailSum_sub hX y z x _ _)
    (fun r hr t ht => integral_normSq_blockTailSum_sub_le_of_mem_Icc hX y z hx
      (by exact_mod_cast hS r hr) ht)

end RMF
