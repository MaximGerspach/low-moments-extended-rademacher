/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.RademacherSteps
import RMF.Weighted.Defs

/-!
# The conditional second moment of the weighted Rademacher sum

Step 1 of the small-`q` reduction.  Conditionally on the smooth `σ`-algebra `𝓕_y` the rough
values are orthogonal, so the second moment of

`S(x) = ∑_{r ≤ x, r y-rough} f(r)r^{-1/2} · A_y(x/r)`

collapses to the diagonal — and, the Rademacher function vanishing off the squarefrees, only the
squarefree `r` survive.

**No new argument is made here.**  `RMF.condExp_normSq_roughSmoothSum_sqfree` proves exactly this
for an arbitrary smooth factor `G`; the work is supplying the two properties it asks of `G` —
measurability for `𝓕_y`, which `RMF.measurable_smoothAlgebra_smoothWeightedSum` gives, and an
almost-sure bound, which is the crude `‖A_y(t)‖ ≤ ⌊t⌋₊` below.  The bound is only ever used for
integrability, so its size does not matter.
-/

open Finset MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A crude almost-sure bound on the smooth factor.**  Every value has norm at most one and
every weight `k^{-1/2}` is at most one, so the sum is at most the number of terms.

Lossy on purpose: `RMF.condExp_normSq_roughSmoothSum_sqfree` uses the bound only to know its
integrands are integrable. -/
lemma ae_norm_smoothWeightedSum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (y : ℕ) (t : ℝ) :
    ∀ᵐ ω ∂μ, ‖smoothWeightedSum f y t ω‖ ≤ (⌊t⌋₊ : ℝ) := by
  have hall : ∀ n ∈ Finset.Icc 1 ⌊t⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 :=
    fun n _ => hf.norm_apply_le_one n
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ k ∈ {k ∈ Finset.Icc 1 ⌊t⌋₊ | k ∈ Nat.smoothNumbers (y + 1)},
      ‖f ω k / (Real.sqrt k : ℂ)‖ ≤ 1 := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
    have hk1R : (1 : ℝ) ≤ Real.sqrt k := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hk1)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_one_of_le₀ (le_trans (hω k (Finset.mem_filter.1 hk).1) hk1R)
      (Real.sqrt_nonneg _)
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 hterm) ?_
  rw [nsmul_eq_mul, mul_one]
  exact_mod_cast le_trans (Finset.card_filter_le _ _) (by simp)

/-- **The conditional second moment of the weighted Rademacher sum.**  An *identity*:

`E[|S(x)|² ∣ 𝓕_y] = ∑_{r ≤ x, r rough and squarefree} r⁻¹ |A_y(x/r)|²`.

The `RMF.smoothWeightedSum` instance of `RMF.condExp_normSq_roughSmoothSum_sqfree`, whose
Steinhaus-shaped sibling `RMF.condExp_normSq_normalisedSum_sqfree` is the other one. -/
theorem condExp_normSq_weightedRademacherSum_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {y : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    μ[fun ω => ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ 2
        | smoothAlgebra X y]
      =ᵐ[μ] fun ω => ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m},
          (m : ℝ)⁻¹ * ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω)
              y (x / m) ω‖ ^ 2 := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have key := condExp_normSq_roughSmoothSum_sqfree (x := x) hX
    (G := fun m => smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / m))
    (B := fun m => (⌊x / m⌋₊ : ℝ))
    (fun m => measurable_smoothAlgebra_smoothWeightedSum y (x / m))
    (fun m => ae_norm_smoothWeightedSum_le hRa y (x / m))
  refine Filter.EventuallyEq.trans (condExp_congr_ae ?_) key
  filter_upwards with ω
  rw [weightedRademacherSum_eq_sum_rough_smooth
    (f := fun ω => squarefreeExtension fun p => X p ω) y hx (hRa.isMultiplicative ω)]
  refine congrArg (fun z : ℂ => ‖z‖ ^ 2) (Finset.sum_congr rfl fun m _ => ?_)
  rw [Complex.ofReal_inv]
  ring

/-- **A crude almost-sure bound on the weighted sum itself.**  Each value has norm at most one
and each weight `n^{-1/2}` is at most one, so `‖S(x)‖ ≤ ⌊x⌋₊`.

As with `RMF.ae_norm_smoothWeightedSum_le`, this exists only to feed integrability. -/
lemma ae_norm_weightedRademacherSum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (x : ℝ) :
    ∀ᵐ ω ∂μ, ‖weightedRademacherSum f x ω‖ ≤ (⌊x⌋₊ : ℝ) := by
  have hall : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 :=
    fun n _ => hf.norm_apply_le_one n
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖f ω n / (Real.sqrt n : ℂ)‖ ≤ 1 := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hn1R : (1 : ℝ) ≤ Real.sqrt n := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_one_of_le₀ (le_trans (hω n hn) hn1R) (Real.sqrt_nonneg _)
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 hterm) ?_
  rw [nsmul_eq_mul, mul_one, Nat.card_Icc]
  simp

/-! ### Step 1: conditioning

Conditional Jensen turns `E|S(x)|^{2q}` into the `q`-th moment of the conditional second moment,
which the identity above evaluates.  The four integrability hypotheses of
`RMF.integral_rpow_le_integral_condExp_rpow` all come from the crude bound `‖A_y(t)‖ ≤ ⌊t⌋₊`,
since a bounded measurable function on a probability space is integrable. -/

/-- The summand of the rough sum, `m⁻¹ |A_y(x/m)|²`.  The weighted counterpart of
`RMF.roughTerm`. -/
noncomputable def weightedRoughTerm (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (x : ℝ) (ω : Ω)
    (m : ℕ) : ℝ := (m : ℝ)⁻¹ * ‖smoothWeightedSum f y (x / m) ω‖ ^ 2

omit [MeasurableSpace Ω] in
lemma weightedRoughTerm_nonneg (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (x : ℝ) (ω : Ω) (m : ℕ) :
    0 ≤ weightedRoughTerm f y x ω m := by
  rw [weightedRoughTerm]
  positivity

/-- The smooth factor is measurable for the ambient `σ`-algebra: a finite sum of measurable
values divided by constants. -/
lemma measurable_smoothWeightedSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (y : ℕ) (t : ℝ) : Measurable (smoothWeightedSum f y t) :=
  Finset.measurable_sum _ fun n _ => (hf.measurable_apply n).div_const _

/-- **Step 1, the conditioning bound.**  `E|S(x)|^{2q}` is at most the `q`-th moment of the
rough sum, uniformly in `q`: no constant appears, so nothing here has to be tracked when the
pieces are assembled. -/
theorem integral_rpow_weightedRademacherSum_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x : ℝ} (hx : 1 ≤ x)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m},
          weightedRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω m) ^ q ∂μ := by
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  have hRa : IsRademacherRMF f μ := hX.isRademacherRMF
  have hle := smoothAlgebra_le hX y
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hWm : Measurable (weightedRademacherSum f x) :=
    Finset.measurable_sum _ fun n _ => (hRa.measurable_apply n).div_const _
  refine le_trans (integral_rpow_norm_le_integral_condExp_rpow hle hWm
    (ae_norm_weightedRademacherSum_le hRa x) hq0 hq1) (le_of_eq ?_)
  refine integral_congr_ae ?_
  filter_upwards [condExp_normSq_weightedRademacherSum_sqfree hX (y := y) hx0] with ω hω
  simp only [weightedRoughTerm]
  rw [hω]

/-! ### Step 2a: splitting off the term `m = 1`

The `m = 1` term of the rough sum is `‖A_y(x)‖²` — the whole smooth sum, untruncated by any
rough factor — and it is the one term the chaos estimate cannot absorb.  Subadditivity of
`t ↦ t^q` for `q ≤ 1` peels it off.  Nothing here needs `q > 0`, and no constant appears. -/

/-- Every rough term is at most `⌊x⌋₊²`: the weight `m⁻¹` is at most one and `A_y(x/m)` is a sum
of at most `⌊x⌋₊` terms of norm at most one. -/
lemma ae_weightedRoughTerm_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (y : ℕ) {x : ℝ} (hx : 0 ≤ x) (m : ℕ) (hm : 1 ≤ m) :
    ∀ᵐ ω ∂μ, weightedRoughTerm f y x ω m ≤ (⌊x⌋₊ : ℝ) ^ 2 := by
  filter_upwards [ae_norm_smoothWeightedSum_le hf y (x / m)] with ω hω
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hfl : (⌊x / m⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    have : x / m ≤ x := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    exact_mod_cast Nat.floor_le_floor this
  have hsq : ‖smoothWeightedSum f y (x / m) ω‖ ^ 2 ≤ (⌊x⌋₊ : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (le_trans hω hfl) 2
  rw [weightedRoughTerm]
  calc (m : ℝ)⁻¹ * ‖smoothWeightedSum f y (x / m) ω‖ ^ 2
      ≤ 1 * ‖smoothWeightedSum f y (x / m) ω‖ ^ 2 := by
        gcongr
        exact inv_le_one_of_one_le₀ hmR
    _ = ‖smoothWeightedSum f y (x / m) ω‖ ^ 2 := one_mul _
    _ ≤ (⌊x⌋₊ : ℝ) ^ 2 := hsq

/-- The rough sum over any index set is bounded, hence so is its `q`-th power. -/
lemma integrable_rpow_sum_weightedRoughTerm {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsRademacherRMF f μ) (y : ℕ) {x : ℝ} (hx : 0 ≤ x)
    {s : Finset ℕ} (hs : ∀ m ∈ s, 1 ≤ m) {q : ℝ} (hq0 : 0 ≤ q) :
    Integrable (fun ω => (∑ m ∈ s, weightedRoughTerm f y x ω m) ^ q) μ := by
  have hmeas : Measurable fun ω => ∑ m ∈ s, weightedRoughTerm f y x ω m := by
    refine Finset.measurable_sum _ fun m _ => ?_
    have : Measurable (smoothWeightedSum f y (x / m)) := measurable_smoothWeightedSum hf y _
    unfold weightedRoughTerm
    fun_prop
  have hbdd : ∀ᵐ ω ∂μ, ∑ m ∈ s, weightedRoughTerm f y x ω m
      ≤ (s.card : ℝ) * (⌊x⌋₊ : ℝ) ^ 2 := by
    have hall : ∀ m ∈ s, ∀ᵐ ω ∂μ, weightedRoughTerm f y x ω m ≤ (⌊x⌋₊ : ℝ) ^ 2 :=
      fun m hm => ae_weightedRoughTerm_le hf y hx m (hs m hm)
    filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
    calc ∑ m ∈ s, weightedRoughTerm f y x ω m ≤ ∑ _m ∈ s, (⌊x⌋₊ : ℝ) ^ 2 :=
          Finset.sum_le_sum fun m hm => hω m hm
      _ = (s.card : ℝ) * (⌊x⌋₊ : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hmq : Measurable fun ω => (∑ m ∈ s, weightedRoughTerm f y x ω m) ^ q :=
    (Real.continuous_rpow_const hq0).measurable.comp hmeas
  refine (memLp_top_of_bound hmq.aestronglyMeasurable
    (((s.card : ℝ) * (⌊x⌋₊ : ℝ) ^ 2) ^ q) ?_).integrable le_top
  filter_upwards [hbdd] with ω hω
  have h0 : (0 : ℝ) ≤ ∑ m ∈ s, weightedRoughTerm f y x ω m :=
    Finset.sum_nonneg fun m _ => weightedRoughTerm_nonneg _ _ _ _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 q)]
  exact Real.rpow_le_rpow h0 hω hq0

/-- **Step 2a.**  The `m = 1` term of the rough sum is `‖A_y(x)‖²`, and subadditivity peels it
off:

`E|S(x)|^{2q} ≤ E|A_y(x)|^{2q} + E[(∑_{1 < m ≤ x, m rough and squarefree} m⁻¹|A_y(x/m)|²)^q]`.

Still uniform in `q` with no constant. -/
theorem integral_rpow_weightedRademacherSum_le_split {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x : ℝ} (hx : 1 ≤ x)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ (∫ ω, ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y x ω‖ ^ (2 * q)
            ∂μ)
        + ∫ ω, (∑ m ∈ ({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m}).erase 1,
            weightedRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω m) ^ q ∂μ := by
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  have hRa : IsRademacherRMF f μ := hX.isRademacherRMF
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set A : Finset ℕ := {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m} with hAdef
  have hmem : ∀ m ∈ A, 1 ≤ m := fun m hm => (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1
  have h1A : 1 ∈ A := by
    rw [hAdef, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, Nat.le_floor (by exact_mod_cast hx)⟩, isRough_one y, squarefree_one⟩
  have hT1 : ∀ ω : Ω, weightedRoughTerm f y x ω 1 = ‖smoothWeightedSum f y x ω‖ ^ 2 := by
    intro ω
    rw [weightedRoughTerm]
    norm_num
  have hpow : ∀ ω : Ω, ‖smoothWeightedSum f y x ω‖ ^ (2 * q)
      = (‖smoothWeightedSum f y x ω‖ ^ 2) ^ q := by
    intro ω
    rw [← Real.rpow_natCast ‖smoothWeightedSum f y x ω‖ 2, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have hint1 : Integrable (fun ω => (‖smoothWeightedSum f y x ω‖ ^ 2) ^ q) μ := by
    have := integrable_rpow_sum_weightedRoughTerm hRa y hx0 (s := {1})
      (fun m hm => (Finset.mem_singleton.1 hm).ge) hq0
    simpa [hT1] using this
  have hint2 := integrable_rpow_sum_weightedRoughTerm hRa y hx0 (s := A.erase 1)
    (fun m hm => hmem m (Finset.mem_of_mem_erase hm)) hq0
  refine le_trans (integral_rpow_weightedRademacherSum_le hX y hx hq0 hq1) ?_
  have hstep : ∀ ω : Ω, (∑ m ∈ A, weightedRoughTerm f y x ω m) ^ q
      ≤ (‖smoothWeightedSum f y x ω‖ ^ 2) ^ q
        + (∑ m ∈ A.erase 1, weightedRoughTerm f y x ω m) ^ q := by
    intro ω
    rw [← Finset.add_sum_erase _ _ h1A, hT1]
    exact Real.rpow_add_le_add_rpow (by positivity)
      (Finset.sum_nonneg fun m _ => weightedRoughTerm_nonneg _ _ _ _ _) hq0 hq1
  calc ∫ ω, (∑ m ∈ A, weightedRoughTerm f y x ω m) ^ q ∂μ
      ≤ ∫ ω, ((‖smoothWeightedSum f y x ω‖ ^ 2) ^ q
          + (∑ m ∈ A.erase 1, weightedRoughTerm f y x ω m) ^ q) ∂μ :=
        integral_mono (integrable_rpow_sum_weightedRoughTerm hRa y hx0 hmem hq0)
          (hint1.add hint2) hstep
    _ = (∫ ω, (‖smoothWeightedSum f y x ω‖ ^ 2) ^ q ∂μ)
          + ∫ ω, (∑ m ∈ A.erase 1, weightedRoughTerm f y x ω m) ^ q ∂μ :=
        integral_add hint1 hint2
    _ = _ := by simp_rw [hpow]

/-! ### The smooth tail over an interval

The smoothing step compares `A_y(x/r)` with `A_y(x/t)` for `t` in a short interval above `r`, and
the difference is a smooth sum over `x/t < m ≤ x/r`.  Its mean square is the harmonic mass of that
range — small when the range is short, which is the whole content of the error term.

Step 2b uses it for the range `(⌊x⌋, ⌊x'⌋]`, and the smoothing step at ranges that have nothing
to do with a truncation point. -/

/-- `∑_{a < m ≤ b, m y-smooth} f(m)/√m`, the smooth sum over an interval. -/
noncomputable def smoothTailSum (f : Ω → ArithmeticFunction ℂ) (y a b : ℕ) (ω : Ω) : ℂ :=
  ∑ m ∈ {m ∈ Finset.Ioc a b | m ∈ Nat.smoothNumbers (y + 1)}, f ω m / (Real.sqrt m : ℂ)

/-- **The mean square of a smooth interval sum is the harmonic mass of the interval.**
Orthogonality, with the squarefree condition surviving on the diagonal. -/
theorem integral_normSq_smoothTailSum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y a b : ℕ) :
    (∫ ω, ‖smoothTailSum (fun ω => squarefreeExtension fun p => X p ω) y a b ω‖ ^ 2 ∂μ)
      = ∑ m ∈ {m ∈ Finset.Ioc a b | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m},
          (m : ℝ)⁻¹ := by
  haveI := hX.isProbabilityMeasure
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  have hRa : IsRademacherRMF f μ := hX.isRademacherRMF
  set S : Finset ℕ := {m ∈ Finset.Ioc a b | m ∈ Nat.smoothNumbers (y + 1)} with hSdef
  have hne : ∀ m ∈ S, m ≠ 0 := by
    intro m hm
    have := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hm).1).1
    omega
  have key := integral_normSq_weightedSum_of_orthogonality' (f := f) (μ := μ) (s := S)
    (c := fun n : ℕ => ((Real.sqrt n : ℂ))⁻¹)
    (d := fun m => if Squarefree m then 1 else 0)
    (fun m _ n _ => hRa.integrable_mul_conj m n)
    (fun m hm n hn => by
      rw [hRa.orthogonality (hne m hm) (hne n hn)]
      by_cases h : m = n
      · subst h; simp
      · simp [h])
  have hTeq : ∀ ω : Ω, smoothTailSum f y a b ω
      = ∑ n ∈ S, ((Real.sqrt n : ℂ))⁻¹ * f ω n :=
    fun ω => Finset.sum_congr rfl fun n _ => div_eq_inv_mul _ _
  simp_rw [← hTeq] at key
  have hfil : ∑ m ∈ {m ∈ S | Squarefree m}, (((m : ℝ)⁻¹ : ℝ) : ℂ)
      = ∑ m ∈ S, (if Squarefree m then (((m : ℝ)⁻¹ : ℝ) : ℂ) else 0) :=
    Finset.sum_filter _ _
  rw [show {m ∈ Finset.Ioc a b | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m}
      = {m ∈ S | Squarefree m} from by rw [hSdef, Finset.filter_filter]]
  rw [← Complex.ofReal_inj, key, Complex.ofReal_sum, hfil]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (hne n hn)
  have hnorm : ‖((Real.sqrt n : ℂ))⁻¹‖ = (Real.sqrt n)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  by_cases h : Squarefree n
  · rw [if_pos h, if_pos h, mul_one, hnorm, ← Complex.ofReal_pow, ← Real.sqrt_inv,
      Real.sq_sqrt (by positivity)]
  · rw [if_neg h, if_neg h, mul_zero]

/-- **The harmonic mass of an interval.**  Every `m` in `(a, b]` is at least `a + 1`, so the sum
is at most the number of terms over `a + 1`. -/
theorem sum_inv_Ioc_le (a b : ℕ) :
    ∑ m ∈ Finset.Ioc a b, (m : ℝ)⁻¹ ≤ ((Finset.Ioc a b).card : ℝ) / (a + 1) := by
  rw [div_eq_mul_inv, mul_comm]
  calc ∑ m ∈ Finset.Ioc a b, (m : ℝ)⁻¹
      ≤ ∑ _m ∈ Finset.Ioc a b, ((a : ℝ) + 1)⁻¹ := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : a + 1 ≤ m := (Finset.mem_Ioc.1 hm).1
        have hmR : ((a : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hm1
        exact inv_anti₀ (by positivity) hmR
    _ = ((a : ℝ) + 1)⁻¹ * ((Finset.Ioc a b).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- **The error estimate of the smoothing step.**  The mean square of a smooth interval sum is at
most the harmonic mass of the interval, dropping both the smoothness and squarefree conditions. -/
theorem integral_normSq_smoothTailSum_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y a b : ℕ) :
    (∫ ω, ‖smoothTailSum (fun ω => squarefreeExtension fun p => X p ω) y a b ω‖ ^ 2 ∂μ)
      ≤ ((Finset.Ioc a b).card : ℝ) / (a + 1) := by
  rw [integral_normSq_smoothTailSum hX y a b]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun m _ _ => by positivity) (sum_inv_Ioc_le a b)

omit [MeasurableSpace Ω] in
/-- **Two truncations of the smooth sum differ by a tail**: for `⌊v⌋ ≤ ⌊u⌋`, `A_y(u)` is `A_y(v)`
plus the smooth sum over `(⌊v⌋, ⌊u⌋]`.  Step 2b uses it, and the smoothing step at truncation
points `x/t` and `x/r`. -/
lemma smoothWeightedSum_eq_add_smoothTailSum (f : Ω → ArithmeticFunction ℂ) (y : ℕ) {u v : ℝ}
    (huv : ⌊v⌋₊ ≤ ⌊u⌋₊) (ω : Ω) :
    smoothWeightedSum f y u ω
      = smoothWeightedSum f y v ω + smoothTailSum f y ⌊v⌋₊ ⌊u⌋₊ ω := by
  rw [smoothWeightedSum, smoothWeightedSum, smoothTailSum, ← Finset.sum_union]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    rw [← Finset.filter_union]
    congr 1
    rw [show Finset.Icc 1 ⌊v⌋₊ = Finset.Ioc 0 ⌊v⌋₊ from rfl,
      show Finset.Icc 1 ⌊u⌋₊ = Finset.Ioc 0 ⌊u⌋₊ from rfl]
    exact (Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) huv).symm
  · refine Finset.disjoint_filter_filter (Finset.disjoint_left.2 fun m hm hm' => ?_)
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_Ioc] at hm'
    omega

/-- **The mean square of the difference of two truncations.**  Its harmonic mass, by the tail
estimate; this is the `E|D_r(t)|²` of the smoothing step. -/
theorem integral_normSq_smoothWeightedSum_sub_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {u v : ℝ} (huv : ⌊v⌋₊ ≤ ⌊u⌋₊) :
    (∫ ω, ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y u ω
        - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y v ω‖ ^ 2 ∂μ)
      ≤ (((Finset.Ioc ⌊v⌋₊ ⌊u⌋₊).card : ℝ)) / (⌊v⌋₊ + 1) := by
  have hsub : ∀ ω : Ω,
      smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y u ω
          - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y v ω
        = smoothTailSum (fun ω => squarefreeExtension fun p => X p ω) y ⌊v⌋₊ ⌊u⌋₊ ω := by
    intro ω
    rw [smoothWeightedSum_eq_add_smoothTailSum _ y huv ω]
    ring
  simp_rw [hsub]
  exact integral_normSq_smoothTailSum_le hX y ⌊v⌋₊ ⌊u⌋₊

/-- **The harmonic width of a short multiplicative window.**  For `t ∈ [r, r(1+η)]`,
`#(⌊x/t⌋, ⌊x/r⌋]/(⌊x/t⌋+1) ≤ η + (1+η)r/x`: the numerator is at most `x/r - x/t + 1` and the
denominator at least `x/t`. -/
lemma card_Ioc_floor_div_div_le {x r t η : ℝ} (hx : 0 < x) (hr : 0 < r)
    (ht : t ∈ Set.Icc r (r * (1 + η))) :
    ((Finset.Ioc ⌊x / t⌋₊ ⌊x / r⌋₊).card : ℝ) / (⌊x / t⌋₊ + 1) ≤ η + (1 + η) * r / x := by
  have ht0 : 0 < t := lt_of_lt_of_le hr ht.1
  have hxr : 0 < x / r := div_pos hx hr
  have hxt : 0 < x / t := div_pos hx ht0
  have hfl : ⌊x / t⌋₊ ≤ ⌊x / r⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_left hx.le hr ht.1)
  have hcard : ((Finset.Ioc ⌊x / t⌋₊ ⌊x / r⌋₊).card : ℝ)
      = (⌊x / r⌋₊ : ℝ) - (⌊x / t⌋₊ : ℝ) := by
    rw [Nat.card_Ioc, Nat.cast_sub hfl]
  -- the numerator is at most `x/r - x/t + 1`, the denominator at least `x/t`
  have hnum : (⌊x / r⌋₊ : ℝ) - (⌊x / t⌋₊ : ℝ) ≤ x / r - x / t + 1 := by
    have h1 : (⌊x / r⌋₊ : ℝ) ≤ x / r := Nat.floor_le hxr.le
    have h2 : x / t < (⌊x / t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hden : x / t ≤ (⌊x / t⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hb0 : (0 : ℝ) ≤ x / r - x / t + 1 := by
    have : x / t ≤ x / r := div_le_div_of_nonneg_left hx.le hr ht.1
    linarith
  have hchain : ((⌊x / r⌋₊ : ℝ) - (⌊x / t⌋₊ : ℝ)) / ((⌊x / t⌋₊ : ℝ) + 1)
      ≤ (x / r - x / t + 1) / (x / t) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul hnum (inv_anti₀ hxt hden) (inv_nonneg.2 (by linarith)) hb0
  have heq : (x / r - x / t + 1) / (x / t) = t / r - 1 + t / x := by
    field_simp
  -- and `t/r - 1 ≤ η`, `t/x ≤ (1+η)r/x`
  have htr : t ≤ (1 + η) * r := by linarith [ht.2, mul_comm r (1 + η)]
  have hb1 : t / r - 1 ≤ η := by
    have : t / r ≤ 1 + η := by
      rw [div_le_iff₀ hr]
      linarith
    linarith
  have hb2 : t / x ≤ (1 + η) * r / x := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right htr (inv_nonneg.2 hx.le)
  rw [hcard]
  rw [heq] at hchain
  linarith

/-- **Step 4a: the mean square of the smoothing difference on a short interval.**  For `t` in
`[r, r(1+η)]` the sums `A_y(x/r)` and `A_y(x/t)` differ by the terms in `(x/t, x/r]`, a range of
multiplicative width at most `1+η`, so the second moment is at most `η + (1+η)r/x`.  In the
assembly `η` meets the **harmonic mass** of the rough `r` and `(1+η)r/x` their **count**, whence
the error's shape `log x/√y + (log y)⁻¹`. -/
theorem integral_normSq_smoothWeightedSum_sub_le_of_mem_Icc {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x r t η : ℝ}
    (hx : 0 < x) (hr : 0 < r) (ht : t ∈ Set.Icc r (r * (1 + η))) :
    (∫ ω, ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
        - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2 ∂μ)
      ≤ η + (1 + η) * r / x := by
  have hfl : ⌊x / t⌋₊ ≤ ⌊x / r⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_left hx.le hr ht.1)
  exact le_trans (integral_normSq_smoothWeightedSum_sub_le hX y hfl)
    (card_Ioc_floor_div_div_le hx hr ht)

/-! ### Step 2b: truncating the smooth sum

`A_y(x)` differs from `A_y(x')` by the tail `∑_{x < m ≤ x'}`, whose mean square is the harmonic
mass of the tail.  Subadditivity of `t ↦ t^{2q}` needs `2q ≤ 1` here — one power lower than
step 2a, and exactly the reason this reduction is for `q ≤ ½`. -/

/-- **Step 2b.**  For `⌊x⌋ ≤ ⌊x'⌋` and `0 ≤ 2q ≤ 1`, truncating the smooth sum at `x` rather
than `x'` costs the tail's harmonic mass:
`E|A_y(x)|^{2q} ≤ E|A_y(x')|^{2q} + (∑_{x < m ≤ x', m smooth and squarefree} m⁻¹)^q`.
Taking `x'` past the primorial makes `A_y(x')` the full Euler product `F_y(½)`
(`RMF.integral_rpow_weightedRademacherSum_le_eulerProduct`). -/
theorem integral_rpow_smoothWeightedSum_le_of_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x x' : ℝ}
    (hxx : ⌊x⌋₊ ≤ ⌊x'⌋₊) {q : ℝ} (hq0 : 0 ≤ q) (hq : 2 * q ≤ 1) :
    (∫ ω, ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y x ω‖ ^ (2 * q) ∂μ)
      ≤ (∫ ω, ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y x' ω‖ ^ (2 * q)
            ∂μ)
        + (∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ ⌊x'⌋₊ | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m},
            (m : ℝ)⁻¹) ^ q := by
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  have hRa : IsRademacherRMF f μ := hX.isRademacherRMF
  set S : Finset ℕ := {m ∈ Finset.Ioc ⌊x⌋₊ ⌊x'⌋₊ | m ∈ Nat.smoothNumbers (y + 1)} with hSdef
  set T : Ω → ℂ := fun ω => ∑ m ∈ S, f ω m / (Real.sqrt m : ℂ) with hTdef
  have hne : ∀ m ∈ S, m ≠ 0 := by
    intro m hm
    have := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hm).1).1
    omega
  -- the two ranges differ by the tail
  have hsplit : ∀ ω : Ω, smoothWeightedSum f y x' ω = smoothWeightedSum f y x ω + T ω :=
    fun ω => smoothWeightedSum_eq_add_smoothTailSum f y hxx ω
  -- the tail's mean square is the harmonic mass of the tail
  have hTsq : (∫ ω, ‖T ω‖ ^ 2 ∂μ)
      = ∑ m ∈ {m ∈ S | Squarefree m}, (m : ℝ)⁻¹ := by
    rw [show T = smoothTailSum f y ⌊x⌋₊ ⌊x'⌋₊ from rfl,
      integral_normSq_smoothTailSum hX y ⌊x⌋₊ ⌊x'⌋₊, hSdef, Finset.filter_filter]
  -- the tail is bounded, so every integral below exists
  have hTm : Measurable T := Finset.measurable_sum _ fun n _ => (hRa.measurable_apply n).div_const _
  have hTb : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ (S.card : ℝ) := by
    have hall : ∀ n ∈ S, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 := fun n _ => hRa.norm_apply_le_one n
    filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ S, ‖f ω n / (Real.sqrt n : ℂ)‖ ≤ 1 := by
      intro n hn
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (hne n hn)
      have hn1R : (1 : ℝ) ≤ Real.sqrt n := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact div_le_one_of_le₀ (le_trans (hω n hn) hn1R) (Real.sqrt_nonneg _)
    simpa using Finset.sum_le_card_nsmul _ _ 1 hterm
  have hbnd : ∀ (g : Ω → ℂ) (c : ℝ), Measurable g → (∀ᵐ ω ∂μ, ‖g ω‖ ≤ c) → ∀ r : ℝ, 0 ≤ r →
      Integrable (fun ω => ‖g ω‖ ^ r) μ := by
    intro g c hg hgb r hr
    have hc : 0 ≤ c := by
      obtain ⟨ω, hω⟩ := hgb.exists
      exact le_trans (norm_nonneg _) hω
    have hm : Measurable fun ω => ‖g ω‖ ^ r :=
      (Real.continuous_rpow_const hr).measurable.comp hg.norm
    refine (memLp_top_of_bound hm.aestronglyMeasurable (c ^ r) ?_).integrable le_top
    filter_upwards [hgb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) r)]
    exact Real.rpow_le_rpow (norm_nonneg _) hω hr
  have hq2 : (0 : ℝ) ≤ 2 * q := by linarith
  have hintx := hbnd _ _ (measurable_smoothWeightedSum hRa y x)
    (ae_norm_smoothWeightedSum_le hRa y x) _ hq2
  have hintx' := hbnd _ _ (measurable_smoothWeightedSum hRa y x')
    (ae_norm_smoothWeightedSum_le hRa y x') _ hq2
  have hintT := hbnd _ _ hTm hTb _ hq2
  have hintT2 : Integrable (fun ω => ‖T ω‖ ^ 2) μ := by
    have hm : Measurable fun ω => ‖T ω‖ ^ 2 := by fun_prop
    refine (memLp_top_of_bound hm.aestronglyMeasurable ((S.card : ℝ) ^ 2) ?_).integrable
      le_top
    filter_upwards [hTb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hω 2
  have hpow : ∀ z : ℂ, ‖z‖ ^ (2 * q) = (‖z‖ ^ 2) ^ q := by
    intro z
    rw [← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have hintTq : Integrable (fun ω => (‖T ω‖ ^ 2) ^ q) μ := by
    simpa only [hpow] using hintT
  -- subadditivity of `t ↦ t^{2q}`, which is where `2q ≤ 1` is used
  have hpt : ∀ ω : Ω, ‖smoothWeightedSum f y x ω‖ ^ (2 * q)
      ≤ ‖smoothWeightedSum f y x' ω‖ ^ (2 * q) + ‖T ω‖ ^ (2 * q) := by
    intro ω
    have hsub : smoothWeightedSum f y x ω = smoothWeightedSum f y x' ω - T ω := by
      rw [hsplit ω]; ring
    calc ‖smoothWeightedSum f y x ω‖ ^ (2 * q)
        ≤ (‖smoothWeightedSum f y x' ω‖ + ‖T ω‖) ^ (2 * q) := by
          refine Real.rpow_le_rpow (norm_nonneg _) ?_ hq2
          rw [hsub]
          exact norm_sub_le _ _
      _ ≤ ‖smoothWeightedSum f y x' ω‖ ^ (2 * q) + ‖T ω‖ ^ (2 * q) :=
          Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) hq2 hq
  -- Jensen for the concave `t ↦ t^q`
  have hjen : (∫ ω, ‖T ω‖ ^ (2 * q) ∂μ) ≤ (∫ ω, ‖T ω‖ ^ 2 ∂μ) ^ q := by
    have hq1 : q ≤ 1 := by linarith
    simp_rw [hpow]
    exact (Real.concaveOn_rpow hq0 hq1).le_map_integral
      ((Real.continuous_rpow_const hq0).continuousOn) isClosed_Ici
      (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (by positivity))
      hintT2 (by simpa [Function.comp_def] using hintTq)
  calc ∫ ω, ‖smoothWeightedSum f y x ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω, (‖smoothWeightedSum f y x' ω‖ ^ (2 * q) + ‖T ω‖ ^ (2 * q)) ∂μ :=
        integral_mono hintx (hintx'.add hintT) hpt
    _ = (∫ ω, ‖smoothWeightedSum f y x' ω‖ ^ (2 * q) ∂μ) + ∫ ω, ‖T ω‖ ^ (2 * q) ∂μ :=
        integral_add hintx' hintT
    _ ≤ (∫ ω, ‖smoothWeightedSum f y x' ω‖ ^ (2 * q) ∂μ) + (∫ ω, ‖T ω‖ ^ 2 ∂μ) ^ q := by
        gcongr
    _ = _ := by rw [hTsq, hSdef, Finset.filter_filter]

/-! ### The smooth sum past the primorial is the Euler product

`A_y(t)` stops changing once `t` passes `primorial y`, because the Rademacher function vanishes
off the squarefrees and a squarefree `y`-smooth number divides the primorial.  So the whole
smooth sum is a **finite** object here, and its value is `F_y(½)`.

That finiteness is the one real simplification the Rademacher side enjoys over Steinhaus, where
the corresponding series is infinite and its convergence has to be argued. -/

/-- A squarefree `y`-smooth number divides `primorial y`: it is the product of its prime factors,
all of which are at most `y`. -/
lemma dvd_primorial_of_squarefree_of_mem_smoothNumbers {y n : ℕ} (hn : Squarefree n)
    (hs : n ∈ Nat.smoothNumbers (y + 1)) : n ∣ primorial y := by
  rw [← Nat.prod_primeFactors_of_squarefree hn, primorial]
  refine Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hple : p ≤ y := mem_smoothNumbers_succ_iff.1 hs p hpp (Nat.dvd_of_mem_primeFactors hp)
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hple, hpp⟩

omit [MeasurableSpace Ω] in
/-- **The smooth sum past the primorial is the Euler product.**  `A_y(N) = F_y(½)` as soon as
`N ≥ primorial y`. -/
theorem smoothWeightedSum_eq_randomEulerProduct {X : ℕ → Ω → ℂ} (y : ℕ) {N : ℝ}
    (hN : (primorial y : ℝ) ≤ N) (ω : Ω) :
    smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y N ω
      = randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (1 / 2) ω := by
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  rw [← dirichletSeries_smoothCoeff_eq_sqfree y ω (1 / 2), dirichletSeries]
  have hzero : ∀ n ∉ {n ∈ Finset.Icc 1 ⌊N⌋₊ | n ∈ Nat.smoothNumbers (y + 1)},
      smoothCoeff f y ω n / (n : ℂ) ^ (1 / 2 : ℂ) = 0 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    by_cases hsm : n ∈ Nat.smoothNumbers (y + 1)
    · have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hsm
      have hnot : n ∉ Finset.Icc 1 ⌊N⌋₊ := fun h => hn ⟨h, hsm⟩
      have hsf : ¬ Squarefree n := by
        intro hsf
        refine hnot (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hn0, ?_⟩)
        have hdvd := dvd_primorial_of_squarefree_of_mem_smoothNumbers hsf hsm
        have hp0 : 0 < primorial y := by
          rw [primorial]
          exact Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.pos
        have hle : n ≤ primorial y := Nat.le_of_dvd hp0 hdvd
        have hleR : (n : ℝ) ≤ N := le_trans (by exact_mod_cast hle) hN
        exact Nat.le_floor hleR
      rw [smoothCoeff, if_pos hsm, hfdef]
      simp [squarefreeExtension_apply_of_not_squarefree _ hsf]
    · rw [smoothCoeff, if_neg hsm, zero_div]
  rw [tsum_eq_sum hzero, smoothWeightedSum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hsm := (Finset.mem_filter.1 hn).2
  have hcast : ((n : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt n : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    norm_num
  rw [smoothCoeff, if_pos hsm, hcast]

/-! ### The smoothing step: averaging over a short interval

`A_y(w)` is a step function of `w` — it changes only when `⌊w⌋` does — so `t ↦ A_y(x/t)` is
measurable, and the averaging inequality `‖a‖² ≤ 2‖b‖² + 2‖a-b‖²` can be integrated over
`t ∈ [r, r(1+η)]`.  That replaces the value at the single point `x/r` by an average over a short
range of `t`, which is what lets the sum over rough `r` become an integral. -/

omit [MeasurableSpace Ω] in
/-- The truncation point enters `A_y` only through `⌊·⌋₊`, so the sum is a step function of it. -/
lemma measurable_smoothWeightedSum_truncation (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (ω : Ω) :
    Measurable fun t : ℝ => smoothWeightedSum f y t ω := by
  have h : (fun t : ℝ => smoothWeightedSum f y t ω)
      = (fun n : ℕ => ∑ k ∈ {k ∈ Finset.Icc 1 n | k ∈ Nat.smoothNumbers (y + 1)},
          f ω k / (Real.sqrt k : ℂ)) ∘ (fun t : ℝ => ⌊t⌋₊) := rfl
  rw [h]
  exact measurable_from_top.comp Nat.measurable_floor

omit [MeasurableSpace Ω] in
/-- **The averaging inequality.**  `‖a‖² ≤ 2‖b‖² + 2‖a - b‖²`, the parallelogram-style bound that
lets a value be replaced by a nearby one at the cost of the difference. -/
lemma normSq_le_two_add_two_sub (a b : ℂ) : ‖a‖ ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 * ‖a - b‖ ^ 2 := by
  have h : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
    calc ‖a‖ = ‖b + (a - b)‖ := by ring_nf
      _ ≤ ‖b‖ + ‖a - b‖ := norm_add_le _ _
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b),
    sq_nonneg (‖b‖ - ‖a - b‖)]

/-- **The averaging step, at one `r`, for any function.**  Integrating
`‖a‖² ≤ 2‖b‖² + 2‖a-b‖²` over `t ∈ [r, r(1+η)]`, whose length is `ηr`, replaces the value
`G(x/r)` by an average over a short range of `t`, at the cost of the differences
`G(x/r) - G(x/t)`.  Integrability is a hypothesis: the caller knows why its function is bounded. -/
lemma normSq_average_bound (G : ℝ → ℂ) (x : ℝ) {r η : ℝ} (hr : 0 < r) (hη : 0 < η)
    (h₁ : IntervalIntegrable (fun t => ‖G (x / t)‖ ^ 2) volume r (r * (1 + η)))
    (h₂ : IntervalIntegrable (fun t => ‖G (x / r) - G (x / t)‖ ^ 2) volume r (r * (1 + η))) :
    (η * r) * ‖G (x / r)‖ ^ 2
      ≤ 2 * (∫ t in r..(r * (1 + η)), ‖G (x / t)‖ ^ 2)
        + 2 * (∫ t in r..(r * (1 + η)), ‖G (x / r) - G (x / t)‖ ^ 2) := by
  have hle : r ≤ r * (1 + η) := by nlinarith
  have hconst : (∫ _t in r..(r * (1 + η)), ‖G (x / r)‖ ^ 2) = (η * r) * ‖G (x / r)‖ ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [← hconst, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (h₁.const_mul 2) (h₂.const_mul 2)]
  refine intervalIntegral.integral_mono_on hle intervalIntegrable_const
    ((h₁.const_mul 2).add (h₂.const_mul 2)) fun t _ => ?_
  exact normSq_le_two_add_two_sub _ _

/-! ### The exchange: a sum of integrals over overlapping intervals

The smoothing produces `∑_{r rough} c_r ∫_{I_r} g` with the `I_r` overlapping.  Because the index
set is **finite**, no product measure is involved: each set integral is an integral of an
indicator, the sum of finitely many integrals is the integral of the sum, and the sum of
indicators is the counting function of how many `I_r` contain the point.

That is the whole exchange.  It is stated over an arbitrary finite family, so the sieve estimate
enters only as the bound `b` on the counting function. -/

omit [MeasurableSpace Ω] in
/-- **A finite sum of integrals over overlapping sets is an integral against their count.**
If `∑_r c_r·1_{I_r}(t) ≤ b t` on `T`, then `∑_r c_r ∫_{I_r} g ≤ ∫_T g·b` for nonnegative `g`.

No Fubini: the index set is a `Finset`, so this is `MeasureTheory.integral_finsetSum`. -/
theorem sum_smul_setIntegral_le {S : Finset ℕ} {I : ℕ → Set ℝ} {c : ℕ → ℝ} {g b : ℝ → ℝ}
    {T : Set ℝ} (hg0 : ∀ t, 0 ≤ g t) (hsub : ∀ r ∈ S, I r ⊆ T)
    (hIm : ∀ r ∈ S, MeasurableSet (I r))
    (hint : ∀ r ∈ S, IntegrableOn (fun t => c r * (I r).indicator g t) T volume)
    (hintT : IntegrableOn (fun t => g t * b t) T volume)
    (hb : ∀ t ∈ T, ∑ r ∈ S, c r * (I r).indicator (fun _ => (1 : ℝ)) t ≤ b t)
    (hTm : MeasurableSet T) :
    ∑ r ∈ S, c r * ∫ t in I r, g t ≤ ∫ t in T, g t * b t := by
  have hrw : ∀ r ∈ S, c r * (∫ t in I r, g t) = ∫ t in T, c r * (I r).indicator g t := by
    intro r hr
    rw [integral_const_mul, MeasureTheory.setIntegral_indicator (hIm r hr),
      Set.inter_eq_self_of_subset_right (hsub r hr)]
  rw [Finset.sum_congr rfl hrw, ← MeasureTheory.integral_finsetSum _ hint]
  refine setIntegral_mono_on (integrable_finsetSum _ hint) hintT hTm fun t ht => ?_
  have hpt : ∑ r ∈ S, c r * (I r).indicator g t
      = g t * ∑ r ∈ S, c r * (I r).indicator (fun _ => (1 : ℝ)) t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : t ∈ I r
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      ring
  rw [hpt]
  exact mul_le_mul_of_nonneg_left (hb t ht) (hg0 t)

/-! ### The assembly of the smoothing step

Dividing the averaging bound at each `r` by `η r²` and summing turns

`∑_{r ∈ S} ‖A_y(x/r)‖² / r`

into `(2/η)` times a sum of weighted interval integrals, plus the errors.  The exchange bounds the
first by a single integral.  Nothing analytic happens here: the averaging bound
(`RMF.normSq_average_bound`) and the exchange (`RMF.sum_smul_setIntegral_le`) are hypotheses. -/

omit [MeasurableSpace Ω] in
/-- **The smoothing step, assembled.**  From an averaging bound at each `r` and an exchange bound
for the weighted interval integrals, the harmonic sum over `S` is controlled by the single
integral `J` plus the errors.

The shape `(η·r)·g(r) ≤ 2∫ + e r` is what `RMF.normSq_average_bound` supplies; the shape
`∑ r⁻²∫ ≤ J` is what `RMF.sum_smul_setIntegral_le` and `RMF.sum_inv_sq_indicator_le` supply. -/
theorem sum_div_le_of_average {S : Finset ℕ} {η : ℝ} (hη : 0 < η) {g : ℝ → ℝ} {e : ℕ → ℝ}
    {J : ℝ} (hS : ∀ r ∈ S, 0 < r)
    (havg : ∀ r ∈ S, (η * (r : ℝ)) * g (r : ℝ)
      ≤ 2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), g t) + e r)
    (hexch : ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
      * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), g t) ≤ J) :
    ∑ r ∈ S, g (r : ℝ) / (r : ℝ)
      ≤ (2 / η) * J + (1 / η) * ∑ r ∈ S, e r / ((r : ℝ)) ^ 2 := by
  have hstep : ∀ r ∈ S, g (r : ℝ) / (r : ℝ)
      ≤ (2 / η) * ((((r : ℝ)) ^ 2)⁻¹
            * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), g t))
        + (1 / η) * (e r / ((r : ℝ)) ^ 2) := by
    intro r hr
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hS r hr
    have hden : (0 : ℝ) < η * (r : ℝ) ^ 2 := by positivity
    calc g (r : ℝ) / (r : ℝ)
        = (η * (r : ℝ) * g (r : ℝ)) / (η * (r : ℝ) ^ 2) := by
          field_simp
      _ ≤ (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), g t) + e r)
            / (η * (r : ℝ) ^ 2) := by
          gcongr
          exact havg r hr
      _ = (2 / η) * ((((r : ℝ)) ^ 2)⁻¹
              * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), g t))
            + (1 / η) * (e r / ((r : ℝ)) ^ 2) := by
          field_simp
  calc ∑ r ∈ S, g (r : ℝ) / (r : ℝ)
      ≤ ∑ r ∈ S, ((2 / η) * ((((r : ℝ)) ^ 2)⁻¹
            * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), g t))
          + (1 / η) * (e r / ((r : ℝ)) ^ 2)) := Finset.sum_le_sum hstep
    _ = (2 / η) * (∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
            * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), g t))
          + (1 / η) * ∑ r ∈ S, e r / ((r : ℝ)) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (2 / η) * J + (1 / η) * ∑ r ∈ S, e r / ((r : ℝ)) ^ 2 := by
        gcongr

/-! ### The change of variable `w = x/t`

The last step of the smoothing turns `∫ h(x/t) dt/t` into `∫ h(w) dw/w` — the invariance of the
multiplicative Haar measure `dt/t` under inversion.

Mathlib's *interval* substitutions are affine (`intervalIntegral.integral_comp_div` is `t ↦ t/c`),
and the ones that are not require the integrand to be continuous.  `A_y` is a step function, so
neither applies.  What does is the measure-theoretic change of variables,
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul`, which asks only that the *substitution*
be injective and differentiable and puts no condition on the integrand at all. -/

omit [MeasurableSpace Ω] in
/-- The image of an interval under `t ↦ x/t`. -/
lemma image_div_Ioo {x a b : ℝ} (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b) :
    (fun t => x / t) '' Set.Ioo a b = Set.Ioo (x / b) (x / a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  ext w
  constructor
  · rintro ⟨t, ⟨hat, htb⟩, rfl⟩
    have ht : 0 < t := lt_trans ha hat
    exact ⟨by rw [div_lt_div_iff₀ hb ht]; nlinarith,
      by rw [div_lt_div_iff₀ ht ha]; nlinarith⟩
  · rintro ⟨h1, h2⟩
    have hw : 0 < w := lt_trans (by positivity) h1
    refine ⟨x / w, ⟨?_, ?_⟩, by field_simp⟩
    · rw [lt_div_iff₀ hw, lt_div_iff₀ ha] at *
      nlinarith
    · rw [div_lt_iff₀ hw, div_lt_iff₀ hb] at *
      nlinarith

omit [MeasurableSpace Ω] in
/-- **`dt/t` is invariant under `t ↦ x/t`.**  `∫_a^b h(x/t) dt/t = ∫_{x/b}^{x/a} h(w) dw/w`.

No hypothesis on `h`: the change-of-variables theorem used here constrains only the substitution.
That is what makes it applicable to `A_y`, which is a step function. -/
theorem integral_comp_div_div {x a b : ℝ} (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b) (h : ℝ → ℝ) :
    (∫ t in Set.Ioo a b, h (x / t) / t) = ∫ w in Set.Ioo (x / b) (x / a), h w / w := by
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt (fun t => x / t) (-(x / t ^ 2)) (Set.Ioo a b) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans ha ht.1)
    have h1 : HasDerivAt (fun u : ℝ => u⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht0
    have h2 : HasDerivAt (fun u : ℝ => x / u) (-(x / t ^ 2)) t := by
      have h3 := h1.const_mul x
      simpa [div_eq_mul_inv, mul_neg] using h3
    exact h2.hasDerivWithinAt
  have hinj : Set.InjOn (fun t => x / t) (Set.Ioo a b) := by
    intro u hu v hv huv
    have hu0 : u ≠ 0 := ne_of_gt (lt_trans ha hu.1)
    have hv0 : v ≠ 0 := ne_of_gt (lt_trans ha hv.1)
    field_simp at huv
    linarith
  have key := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hderiv hinj (fun w => h w / w)
  rw [image_div_Ioo hx ha hab] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := lt_trans ha ht.1
  rw [smul_eq_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x / t ^ 2)]
  field_simp

/-! ### Step 4: Parseval

`RMF.integral_normSq_partialSum_eq_line` holds at general `σ` **and** general coefficients — the
`σ = ½` forms in `RMF/Reduction/Suppliers.lean` are its `_half` specialisations.  So this step
takes `aₙ = f(n)·1_{n smooth}/√n`, whose partial sums are `A_y` and whose Dirichlet series is the
Euler product at `½ + σ + it`.

Summability is free: the coefficients are supported on the squarefree `y`-smooth numbers, which
are finitely many. -/

omit [MeasurableSpace Ω] in
/-- **Step 4, Parseval at the shifted abscissa.**  For `σ > 0`,
`∫₀^∞ |A_y(u)|² du/u^{1+2σ} = (2π)⁻¹ ∫_ℝ |F_y(½+σ+it)/(σ+it)|² dt`.

The `|σ+it|⁻²` on the right is what makes the central window `|t| ≲ 1/log y` dominant, and it is
available because the coefficients carry the `n^{-1/2}`, letting `σ` fall to `1/log x`. -/
theorem integral_normSq_smoothWeightedSum_eq_line {X : ℕ → Ω → ℂ} (y : ℕ) {σ : ℝ} (hσ : 0 < σ)
    (ω : Ω) :
    (∫ u in Set.Ioi (0 : ℝ),
        ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y u ω‖ ^ 2
          / u ^ (1 + 2 * σ))
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  set a : ℕ → ℂ := fun n => smoothCoeff f y ω n / (Real.sqrt n : ℂ) with hadef
  -- the partial sums of `a` are `A_y`
  have hpart : ∀ u : ℝ, ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n = smoothWeightedSum f y u ω := by
    intro u
    rw [smoothWeightedSum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hadef, smoothCoeff]
    by_cases h : n ∈ Nat.smoothNumbers (y + 1)
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_div]
  -- the coefficients vanish past the primorial
  have hsupp : ∀ n ∉ Finset.Icc 1 (primorial y), a n = 0 := by
    intro n hn
    simp only [hadef, smoothCoeff]
    by_cases hsm : n ∈ Nat.smoothNumbers (y + 1)
    · rw [if_pos hsm]
      have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hsm
      have hsf : ¬ Squarefree n := by
        intro hsf
        have hp0 : 0 < primorial y := by
          rw [primorial]
          exact Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.pos
        exact hn (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hn0,
          Nat.le_of_dvd hp0 (dvd_primorial_of_squarefree_of_mem_smoothNumbers hsf hsm)⟩)
      rw [hfdef]
      simp [squarefreeExtension_apply_of_not_squarefree _ hsf]
    · rw [if_neg hsm, zero_div]
  have hsum : Summable (coeffWeight σ a) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc 1 (primorial y)) fun n hn => ?_
    rw [coeffWeight, hsupp n hn, norm_zero, zero_div]
  have key := integral_normSq_partialSum_eq_line σ a hσ hsum
  simp_rw [hpart] at key
  rw [key]
  refine congrArg (fun z : ℝ => (2 * Real.pi)⁻¹ * z) ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  refine congrArg (fun z : ℂ => ‖z‖ ^ 2) ?_
  refine congrArg (fun z : ℂ => z / ((σ : ℂ) + (t : ℂ) * Complex.I)) ?_
  rw [← dirichletSeries_smoothCoeff_eq_sqfree y ω ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I),
    dirichletSeries]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hadef, smoothCoeff]
  · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hcast : ((n : ℂ)) ^ ((1 / 2 : ℂ)) = ((Real.sqrt n : ℝ) : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]
      norm_num
    rw [hadef, div_div, ← hcast, ← Complex.cpow_add _ _ hn0, ← hfdef]
    ring_nf

/-! ### The reduction to the rough sum

Steps 1, 2a and 2b, chained, with the smooth sum taken past the primorial so that it *is* the
Euler product:

`E|S(x)|^{2q} ≤ E|F_y(½)|^{2q} + (tail harmonic mass)^q + E[(∑_{1<m≤x} m⁻¹|A_y(x/m)|²)^q]`.

**No constant appears, and `q` is a bare parameter**, so the bound is uniform in `q`.  The
`2q ≤ 1` comes from step 2b and is what makes this the range `q ≤ ½`.

Step 3 turns the third term into an integral and step 4 turns that into the Euler product's line
integral. -/

/-- **The reduction to the rough sum.**  The `m = 1` term of the conditional second moment has
become the Euler product, at the cost of the smooth tail past `x`; everything else is the rough
sum, which is what steps 3 and 4 process. -/
theorem integral_rpow_weightedRademacherSum_le_eulerProduct {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x : ℝ} (hx : 1 ≤ x)
    (hxy : ⌊x⌋₊ ≤ primorial y) {q : ℝ} (hq0 : 0 ≤ q) (hq : 2 * q ≤ 1) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (1 / 2) ω‖ ^ (2 * q) ∂μ)
        + (∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial y)
            | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m}, (m : ℝ)⁻¹) ^ q
        + ∫ ω, (∑ m ∈ ({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m}).erase 1,
            weightedRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω m) ^ q ∂μ := by
  have hq1 : q ≤ 1 := by linarith
  -- step 2b at the primorial, where the smooth sum is the Euler product
  have hfl : ⌊x⌋₊ ≤ ⌊((primorial y : ℕ) : ℝ)⌋₊ := by rwa [Nat.floor_natCast]
  have h2b := integral_rpow_smoothWeightedSum_le_of_le hX y hfl hq0 hq
  rw [Nat.floor_natCast] at h2b
  have heuler : ∀ ω : Ω,
      smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y
          ((primorial y : ℕ) : ℝ) ω
        = randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (1 / 2) ω :=
    fun ω => smoothWeightedSum_eq_randomEulerProduct y le_rfl ω
  simp only [heuler] at h2b
  exact le_trans (integral_rpow_weightedRademacherSum_le_split hX y hx hq0 hq1)
    (add_le_add h2b le_rfl)

/-! ### Prerequisites for chaining step 3

Two things the pieces of step 3 need before they compose.

First, the averaging bound `RMF.normSq_average_bound` produces **interval** integrals while
`RMF.sum_div_le_of_average` consumes **set** integrals over `Set.Icc`; they agree, but the
bridge has to be written down.

Second, the averaging bound takes integrability as a hypothesis, and discharging it needs a
*deterministic* bound on `A_y` — which holds exactly for the `ω` where every value has norm at
most one, an almost-sure condition the caller supplies. -/

omit [MeasurableSpace Ω] in
/-- A deterministic bound on the smooth sum, for a single `ω`.  The pointwise counterpart of
`RMF.ae_norm_smoothWeightedSum_le`, which is what the interval integrability below needs. -/
lemma norm_smoothWeightedSum_le_of_bound {f : Ω → ArithmeticFunction ℂ} {ω : Ω}
    (hb : ∀ n, ‖f ω n‖ ≤ 1) (y : ℕ) (t : ℝ) :
    ‖smoothWeightedSum f y t ω‖ ≤ (⌊t⌋₊ : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ k ∈ {k ∈ Finset.Icc 1 ⌊t⌋₊ | k ∈ Nat.smoothNumbers (y + 1)},
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

omit [MeasurableSpace Ω] in
/-- The averaged integrand is interval integrable: measurable in `t`, and bounded on `[r, s]` by
`⌊x/r⌋₊²` because `x/t` decreases. -/
lemma intervalIntegrable_normSq_smoothWeightedSum {f : Ω → ArithmeticFunction ℂ} {ω : Ω}
    (hb : ∀ n, ‖f ω n‖ ≤ 1) (y : ℕ) {x r s : ℝ} (hx : 0 ≤ x) (hr : 0 < r) (hrs : r ≤ s) :
    IntervalIntegrable (fun t => ‖smoothWeightedSum f y (x / t) ω‖ ^ 2) volume r s := by
  have hmeas : Measurable fun t : ℝ => ‖smoothWeightedSum f y (x / t) ω‖ ^ 2 := by
    have h1 : Measurable fun t : ℝ => smoothWeightedSum f y (x / t) ω :=
      (measurable_smoothWeightedSum_truncation f y ω).comp (measurable_const.div measurable_id)
    fun_prop
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hrs]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := ((⌊x / r⌋₊ : ℝ)) ^ 2)
    (measure_Ioc_lt_top).ne hmeas.aestronglyMeasurable ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hrt : r < t := ht.1
    have hfl : (⌊x / t⌋₊ : ℝ) ≤ (⌊x / r⌋₊ : ℝ) := by
      have : x / t ≤ x / r := by
        apply div_le_div_of_nonneg_left hx hr (le_of_lt hrt)
      exact_mod_cast Nat.floor_le_floor this
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (le_trans (norm_smoothWeightedSum_le_of_bound hb y _) hfl) 2

omit [MeasurableSpace Ω] in
/-- The bridge: an interval integral over `[a, b]` is the set integral over `Set.Icc a b`. -/
lemma intervalIntegral_eq_setIntegral_Icc {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, g t) = ∫ t in Set.Icc a b, g t := by
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]

/-! ### Joint measurability of the averaged integrand

The Tonelli swap for the error term needs `(ω, t) ↦ A_y(x/t) ω` measurable on the product.  It is
not obviously so as written: the truncation point sits inside `⌊·⌋₊`, which is a `ℕ`-valued
parameter of the summation range.

The way round is to fix a single index set.  On `t ≥ r` the truncation `⌊x/t⌋₊` never exceeds
`N = ⌊x/r⌋₊`, so the sum can be written over `Icc 1 N` throughout with an indicator carrying the
truncation — and then each term is a product of something measurable in `ω` with something
measurable in `t`. -/

omit [MeasurableSpace Ω] in
/-- The smooth sum over a **fixed** index set, with the truncation carried by an indicator.
Valid whenever `N` is past the truncation point. -/
lemma smoothWeightedSum_eq_sum_indicator (f : Ω → ArithmeticFunction ℂ) (y : ℕ) {u : ℝ} {N : ℕ}
    (hN : ⌊u⌋₊ ≤ N) (ω : Ω) :
    smoothWeightedSum f y u ω
      = ∑ k ∈ {k ∈ Finset.Icc 1 N | k ∈ Nat.smoothNumbers (y + 1)},
          (if k ≤ ⌊u⌋₊ then f ω k / (Real.sqrt k : ℂ) else 0) := by
  rw [← Finset.sum_filter, smoothWeightedSum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hsm⟩
    exact ⟨⟨⟨h1, le_trans h2 hN⟩, hsm⟩, h2⟩
  · rintro ⟨⟨⟨h1, -⟩, hsm⟩, h2⟩
    exact ⟨⟨h1, h2⟩, hsm⟩

/-- **The averaged integrand is jointly measurable.**  A finite sum, each term a product of a
function of `ω` with an indicator depending only on `t`. -/
lemma measurable_uncurry_sum_indicator {f : Ω → ArithmeticFunction ℂ}
    (hf : ∀ n, Measurable fun ω => f ω n) (y : ℕ) (x : ℝ) (N : ℕ) :
    Measurable fun p : Ω × ℝ =>
      ∑ k ∈ {k ∈ Finset.Icc 1 N | k ∈ Nat.smoothNumbers (y + 1)},
        (if k ≤ ⌊x / p.2⌋₊ then f p.1 k / (Real.sqrt k : ℂ) else 0) := by
  refine Finset.measurable_sum _ fun k _ => ?_
  have hfloor : Measurable fun p : Ω × ℝ => ⌊x / p.2⌋₊ :=
    Nat.measurable_floor.comp (measurable_const.div measurable_snd)
  refine Measurable.ite (measurableSet_le measurable_const hfloor) ?_ measurable_const
  exact (hf k).comp measurable_fst |>.div_const _

/-! ### The Tonelli swap for the error term

`E[∫ ‖D_r(t)‖² dt] = ∫ E‖D_r(t)‖² dt`.  The integrand is bounded, so integrability on the
(finite) product measure follows once it is jointly measurable — which is what the fixed-index
rewriting `RMF.smoothWeightedSum_eq_sum_indicator` supplies, valid on `t ≥ r`.

The idiom for lifting an almost-sure condition on `ω` to the product is
`Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually`, as
`RMF/Probability/RademacherRestrictedSecondMoment/Drift.lean` already uses. -/

/-- **The error integrand is product-integrable.**  Jointly measurable — through the indicator
truncation, since `⌊x/t⌋₊` is bounded on the interval — and bounded by `(2⌊x/r⌋₊)²`.

This is the core that both the Tonelli swap and the `ω`-integrability of the error rest on.  The
latter is what Jensen needs, and it is the one side condition the smoothing error cannot supply
pointwise: its bound exists only in expectation. -/
theorem integrable_uncurry_normSq_sub {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x r s : ℝ}
    (hx : 0 ≤ x) (hr : 0 < r) :
    Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
        ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
          - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2)
      (μ.prod (volume.restrict (Set.Ioc r s))) := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  set N : ℕ := ⌊x / r⌋₊ with hNdef
  set S : Set ℝ := Set.Ioc r s with hSdef
  set F : Ω → ℝ → ℝ := fun ω t =>
    ‖smoothWeightedSum f y (x / r) ω - smoothWeightedSum f y (x / t) ω‖ ^ 2 with hFdef
  set G : Ω × ℝ → ℝ := fun p =>
    ‖smoothWeightedSum f y (x / r) p.1
      - ∑ k ∈ {k ∈ Finset.Icc 1 N | k ∈ Nat.smoothNumbers (y + 1)},
          (if k ≤ ⌊x / p.2⌋₊ then f p.1 k / (Real.sqrt k : ℂ) else 0)‖ ^ 2 with hGdef
  haveI : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ, hSdef]; exact measure_Ioc_lt_top⟩
  have hGmeas : Measurable G := by
    have h1 : Measurable fun p : Ω × ℝ => smoothWeightedSum f y (x / r) p.1 :=
      (measurable_smoothWeightedSum hRa y (x / r)).comp measurable_fst
    have h2 := measurable_uncurry_sum_indicator (f := f) hRa.measurable_apply y x N
    exact ((h1.sub h2).norm).pow_const 2
  have hleN : ∀ t ∈ S, ⌊x / t⌋₊ ≤ N := by
    intro t ht
    exact Nat.floor_le_floor (div_le_div_of_nonneg_left hx hr (le_of_lt ht.1))
  have hFG : ∀ ω : Ω, ∀ t ∈ S, F ω t = G (ω, t) := by
    intro ω t ht
    simp only [hFdef, hGdef]
    rw [smoothWeightedSum_eq_sum_indicator f y (hleN t ht) ω]
  -- lift both almost-sure conditions to the product
  have hbdd : ∀ᵐ ω ∂μ, ∀ n, ‖f ω n‖ ≤ 1 :=
    MeasureTheory.ae_all_iff.2 fun n => hRa.norm_apply_le_one n
  have hbddP : ∀ᵐ p ∂(μ.prod (volume.restrict S)), ∀ n, ‖f p.1 n‖ ≤ 1 :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hbdd
  have hmemP : ∀ᵐ p ∂(μ.prod (volume.restrict S)), p.2 ∈ S :=
    Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually
      (ae_restrict_mem (hSdef ▸ measurableSet_Ioc))
  have hae : (Function.uncurry F) =ᵐ[μ.prod (volume.restrict S)] G := by
    filter_upwards [hmemP] with p hp
    exact hFG p.1 p.2 hp
  have hmeasF : AEStronglyMeasurable (Function.uncurry F) (μ.prod (volume.restrict S)) :=
    hGmeas.aestronglyMeasurable.congr hae.symm
  have hbound : ∀ᵐ p ∂(μ.prod (volume.restrict S)),
      ‖Function.uncurry F p‖ ≤ (2 * (N : ℝ)) ^ 2 := by
    filter_upwards [hbddP, hmemP] with p hb hp
    have h1 : ‖smoothWeightedSum f y (x / r) p.1‖ ≤ (N : ℝ) :=
      norm_smoothWeightedSum_le_of_bound hb y (x / r)
    have h2 : ‖smoothWeightedSum f y (x / p.2) p.1‖ ≤ (N : ℝ) := by
      refine le_trans (norm_smoothWeightedSum_le_of_bound hb y (x / p.2)) ?_
      exact_mod_cast hleN p.2 hp
    have hsub : ‖smoothWeightedSum f y (x / r) p.1
        - smoothWeightedSum f y (x / p.2) p.1‖ ≤ 2 * (N : ℝ) := by
      refine le_trans (norm_sub_le _ _) ?_
      linarith
    have hn0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    rw [Function.uncurry_apply_pair, hFdef, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hsub 2
  have hInt : Integrable (Function.uncurry F) (μ.prod (volume.restrict S)) :=
    (memLp_top_of_bound hmeasF ((2 * (N : ℝ)) ^ 2) hbound).integrable le_top
  exact hInt

/-- **The error term is integrable in `ω`.**  Immediate from product-integrability, by
`MeasureTheory.Integrable.integral_prod_left`. -/
theorem integrable_setIntegral_normSq_sub {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x r s : ℝ}
    (hx : 0 ≤ x) (hr : 0 < r) :
    Integrable (fun ω => ∫ t in Set.Ioc r s,
        ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
          - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2) μ :=
  (integrable_uncurry_normSq_sub hX y hx hr).integral_prod_left

/-! ### The smoothing bound, instantiated

`RMF.sum_div_le_of_average` takes the averaging bound and the exchange as hypotheses.  Here the
first is discharged from `RMF.normSq_average_bound` through the interval/set bridge, with its
integrability supplied by the deterministic bound; the exchange is left as the sum itself, for
the sieve to process. -/

omit [MeasurableSpace Ω] in
/-- The difference integrand is interval integrable: the same argument as
`RMF.intervalIntegrable_normSq_smoothWeightedSum`, with `2⌊x/r⌋₊` in place of `⌊x/r⌋₊`. -/
lemma intervalIntegrable_normSq_smoothWeightedSum_sub {f : Ω → ArithmeticFunction ℂ} {ω : Ω}
    (hb : ∀ n, ‖f ω n‖ ≤ 1) (y : ℕ) {x r s : ℝ} (hx : 0 ≤ x) (hr : 0 < r) (hrs : r ≤ s) :
    IntervalIntegrable
      (fun t => ‖smoothWeightedSum f y (x / r) ω - smoothWeightedSum f y (x / t) ω‖ ^ 2)
      volume r s := by
  have hmeas : Measurable fun t : ℝ =>
      ‖smoothWeightedSum f y (x / r) ω - smoothWeightedSum f y (x / t) ω‖ ^ 2 := by
    have h1 : Measurable fun t : ℝ => smoothWeightedSum f y (x / t) ω :=
      (measurable_smoothWeightedSum_truncation f y ω).comp (measurable_const.div measurable_id)
    fun_prop
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hrs]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := (2 * (⌊x / r⌋₊ : ℝ)) ^ 2)
    (measure_Ioc_lt_top).ne hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hrt : r < t := ht.1
  have hfl : (⌊x / t⌋₊ : ℝ) ≤ (⌊x / r⌋₊ : ℝ) := by
    have hd : x / t ≤ x / r := div_le_div_of_nonneg_left hx hr (le_of_lt hrt)
    exact_mod_cast Nat.floor_le_floor hd
  have h1 := norm_smoothWeightedSum_le_of_bound hb y (x / r)
  have h2 := le_trans (norm_smoothWeightedSum_le_of_bound hb y (x / t)) hfl
  have hsub : ‖smoothWeightedSum f y (x / r) ω - smoothWeightedSum f y (x / t) ω‖
      ≤ 2 * (⌊x / r⌋₊ : ℝ) := le_trans (norm_sub_le _ _) (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) hsub 2

/-- **The smoothing bound for any function**: `∑_{r ∈ S} r⁻¹‖G(x/r)‖²` is at most `2/η` times the
weighted interval integrals, plus `1/η` times the errors.

`RMF.sum_div_le_of_average` with its averaging hypothesis discharged by
`RMF.normSq_average_bound`: the sieve has not entered yet, and the first term is still the sum the
exchange will process. -/
theorem sum_inv_mul_normSq_le (G : ℝ → ℂ) {x η : ℝ} (hη : 0 < η) {S : Finset ℕ}
    (hS : ∀ r ∈ S, 0 < r)
    (h₁ : ∀ r ∈ S, IntervalIntegrable (fun t => ‖G (x / t)‖ ^ 2) volume (r : ℝ)
      ((r : ℝ) * (1 + η)))
    (h₂ : ∀ r ∈ S, IntervalIntegrable (fun t => ‖G (x / r) - G (x / t)‖ ^ 2) volume (r : ℝ)
      ((r : ℝ) * (1 + η))) :
    ∑ r ∈ S, (r : ℝ)⁻¹ * ‖G (x / r)‖ ^ 2
      ≤ (2 / η) * (∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
            * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), ‖G (x / t)‖ ^ 2))
        + (1 / η) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), ‖G (x / r) - G (x / t)‖ ^ 2))
              / ((r : ℝ)) ^ 2 := by
  have hterm : ∀ r ∈ S, (r : ℝ)⁻¹ * ‖G (x / r)‖ ^ 2
      = (fun t => ‖G (x / t)‖ ^ 2) (r : ℝ) / (r : ℝ) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hS r hr
    field_simp
  rw [Finset.sum_congr rfl hterm]
  refine sum_div_le_of_average (g := fun t => ‖G (x / t)‖ ^ 2)
    (e := fun r => 2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
      ‖G (x / r) - G (x / t)‖ ^ 2))
    hη hS (fun r hr => ?_) le_rfl
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hS r hr
  have hle : (r : ℝ) ≤ (r : ℝ) * (1 + η) := by nlinarith
  have hkey := normSq_average_bound G x hr0 hη (h₁ r hr) (h₂ r hr)
  rwa [intervalIntegral_eq_setIntegral_Icc hle, intervalIntegral_eq_setIntegral_Icc hle] at hkey

/-! ### The smoothing step, composed

`RMF.sum_inv_mul_normSq_le` leaves a sum of weighted interval integrals;
`RMF.sum_smul_setIntegral_le` turns that into a single integral against a bound `b` on the
counting function.  Composing them is one `le_trans`.

`b` stays abstract here; it is supplied by `RMF.exists_sum_inv_sq_indicator_le_sieve'` of
`RMF/Weighted/Sieve.lean`. -/

/-- **The smoothing step for any function, composed with the exchange.**  `∑_{r ∈ S} r⁻¹‖G(x/r)‖²`
is at most `2/η` times a single integral against the counting bound `b`, plus `1/η` times the
errors. -/
theorem sum_inv_mul_normSq_le_setIntegral (G : ℝ → ℂ) {x η : ℝ} (hη : 0 < η) {S : Finset ℕ}
    (hS : ∀ r ∈ S, 0 < r)
    (h₁ : ∀ r ∈ S, IntervalIntegrable (fun t => ‖G (x / t)‖ ^ 2) volume (r : ℝ)
      ((r : ℝ) * (1 + η)))
    (h₂ : ∀ r ∈ S, IntervalIntegrable (fun t => ‖G (x / r) - G (x / t)‖ ^ 2) volume (r : ℝ)
      ((r : ℝ) * (1 + η)))
    {T : Set ℝ} (hTm : MeasurableSet T) {b : ℝ → ℝ}
    (hsub : ∀ r ∈ S, Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)) ⊆ T)
    (hb : ∀ t ∈ T, ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t ≤ b t)
    (hint : ∀ r ∈ S, IntegrableOn (fun t => (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun t => ‖G (x / t)‖ ^ 2) t) T volume)
    (hintT : IntegrableOn (fun t => ‖G (x / t)‖ ^ 2 * b t) T volume) :
    ∑ r ∈ S, (r : ℝ)⁻¹ * ‖G (x / r)‖ ^ 2
      ≤ (2 / η) * (∫ t in T, ‖G (x / t)‖ ^ 2 * b t)
        + (1 / η) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), ‖G (x / r) - G (x / t)‖ ^ 2))
              / ((r : ℝ)) ^ 2 := by
  refine le_trans (sum_inv_mul_normSq_le G hη hS h₁ h₂) ?_
  have hexch := sum_smul_setIntegral_le
    (g := fun t => ‖G (x / t)‖ ^ 2) (b := b) (S := S)
    (I := fun r => Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)))
    (c := fun r => (((r : ℝ)) ^ 2)⁻¹)
    (fun t => by positivity) hsub (fun r _ => measurableSet_Icc) hint hintT hb hTm
  have hcoef : (0 : ℝ) ≤ 2 / η := by positivity
  exact add_le_add (mul_le_mul_of_nonneg_left hexch hcoef) le_rfl

omit [MeasurableSpace Ω] in
/-- **The smoothing step, composed.**  The rough sum is at most `2/η` times a single integral
against the counting bound, plus `1/η` times the errors: `RMF.sum_inv_mul_normSq_le_setIntegral`
at `G = A_y`. -/
theorem sum_weightedRoughTerm_le_setIntegral {f : Ω → ArithmeticFunction ℂ} {ω : Ω}
    (hbnd : ∀ n, ‖f ω n‖ ≤ 1) (y : ℕ) {x η : ℝ} (hx : 0 ≤ x) (hη : 0 < η)
    {S : Finset ℕ} (hS : ∀ r ∈ S, 0 < r) {T : Set ℝ} (hTm : MeasurableSet T) {b : ℝ → ℝ}
    (hsub : ∀ r ∈ S, Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)) ⊆ T)
    (hb : ∀ t ∈ T, ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t ≤ b t)
    (hint : ∀ r ∈ S, IntegrableOn (fun t => (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator
            (fun t => ‖smoothWeightedSum f y (x / t) ω‖ ^ 2) t) T volume)
    (hintT : IntegrableOn
      (fun t => ‖smoothWeightedSum f y (x / t) ω‖ ^ 2 * b t) T volume) :
    ∑ r ∈ S, weightedRoughTerm f y x ω r
      ≤ (2 / η) * (∫ t in T, ‖smoothWeightedSum f y (x / t) ω‖ ^ 2 * b t)
        + (1 / η) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
              ‖smoothWeightedSum f y (x / r) ω - smoothWeightedSum f y (x / t) ω‖ ^ 2))
              / ((r : ℝ)) ^ 2 :=
  sum_inv_mul_normSq_le_setIntegral (fun u => smoothWeightedSum f y u ω) hη hS
    (fun r hr => intervalIntegrable_normSq_smoothWeightedSum hbnd y hx
      (by exact_mod_cast hS r hr) (le_mul_of_one_le_right (Nat.cast_nonneg r) (by linarith)))
    (fun r hr => intervalIntegrable_normSq_smoothWeightedSum_sub hbnd y hx
      (by exact_mod_cast hS r hr) (le_mul_of_one_le_right (Nat.cast_nonneg r) (by linarith)))
    hTm hsub hb hint hintT

/-- **The expectation of the smoothing error, from joint integrability.**  If on each window
`t ∈ [r, r(1+η)]` the mean square of `G(x/r) - G(x/t)` is at most `η + (1+η)r/x`, and the
difference is jointly integrable, then each interval of length `rη` contributes
`2η(η + (1+η)r/x)/r`.  Fubini (`MeasureTheory.integral_integral_swap`) does the rest. -/
theorem integral_sum_setIntegral_normSq_sub_le_of_integrable {μ : Measure Ω}
    [IsProbabilityMeasure μ] (G : Ω → ℝ → ℂ) {x η : ℝ} (hx : 0 < x) (hη : 0 < η)
    {S : Finset ℕ} (hS : ∀ r ∈ S, 0 < r)
    (hjoint : ∀ r ∈ S, Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
        ‖G ω (x / r) - G ω (x / t)‖ ^ 2)
        (μ.prod (volume.restrict (Set.Ioc (r : ℝ) ((r : ℝ) * (1 + η))))))
    (hpt : ∀ r ∈ S, ∀ t ∈ Set.Icc (r : ℝ) ((r : ℝ) * (1 + η)),
        (∫ ω, ‖G ω (x / r) - G ω (x / t)‖ ^ 2 ∂μ) ≤ η + (1 + η) * (r : ℝ) / x) :
    (∫ ω, ∑ r ∈ S, (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
        ‖G ω (x / r) - G ω (x / t)‖ ^ 2)) / ((r : ℝ)) ^ 2 ∂μ)
      ≤ ∑ r ∈ S, 2 * η * (η + (1 + η) * (r : ℝ) / x) / (r : ℝ) := by
  classical
  -- `Icc` and `Ioc` differ by a null set, and the swap is stated over `Ioc`
  have hbridge : ∀ (g : ℝ → ℝ) (a b : ℝ), (∫ t in Set.Icc a b, g t) = ∫ t in Set.Ioc a b, g t := by
    intro g a b
    rw [← MeasureTheory.Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))]
  have hint : ∀ r ∈ S, Integrable (fun ω => (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
      ‖G ω (x / r)
        - G ω (x / t)‖ ^ 2
      )) / ((r : ℝ)) ^ 2) μ := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hS r hr
    simp_rw [hbridge]
    exact (((hjoint r hr).integral_prod_left).const_mul 2).div_const _
  rw [integral_finsetSum _ hint]
  refine Finset.sum_le_sum fun r hr => ?_
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hS r hr
  have hlen : (r : ℝ) * (1 + η) - (r : ℝ) = (r : ℝ) * η := by ring
  have hvol : volume.real (Set.Ioc ((r : ℝ)) ((r : ℝ) * (1 + η))) = (r : ℝ) * η := by
    rw [measureReal_def, Real.volume_Ioc, hlen,
      ENNReal.toReal_ofReal (mul_nonneg hr0.le hη.le)]
  -- pull the constant out, swap, and bound the inner integral pointwise in `t`
  have hshape : ∀ ω : Ω, (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
      ‖G ω (x / r)
        - G ω (x / t)‖ ^ 2
      )) / ((r : ℝ)) ^ 2
      = (2 / ((r : ℝ)) ^ 2) * (∫ t in Set.Ioc ((r : ℝ)) ((r : ℝ) * (1 + η)),
          ‖G ω (x / r)
            - G ω (x / t)‖ ^ 2
            ) := by
    intro ω
    rw [hbridge]
    ring
  simp_rw [hshape]
  rw [integral_const_mul, integral_integral_swap (hjoint r hr)]
  have hmono : (∫ t in Set.Ioc ((r : ℝ)) ((r : ℝ) * (1 + η)), (∫ ω,
          ‖G ω (x / r)
            - G ω (x / t)‖ ^ 2 ∂μ))
      ≤ ∫ _t in Set.Ioc ((r : ℝ)) ((r : ℝ) * (1 + η)), (η + (1 + η) * (r : ℝ) / x) := by
    refine setIntegral_mono_on ((hjoint r hr).integral_prod_right)
      (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc ?_
    intro t ht
    exact hpt r hr t ⟨ht.1.le, ht.2⟩
  rw [setIntegral_const, hvol, smul_eq_mul] at hmono
  have hc0 : (0 : ℝ) ≤ 2 / ((r : ℝ)) ^ 2 := by positivity
  have hfin : (2 / ((r : ℝ)) ^ 2) * ((r : ℝ) * η * (η + (1 + η) * (r : ℝ) / x))
      = 2 * η * (η + (1 + η) * (r : ℝ) / x) / (r : ℝ) := by
    field_simp
  calc (2 / ((r : ℝ)) ^ 2) * (∫ t in Set.Ioc ((r : ℝ)) ((r : ℝ) * (1 + η)), (∫ ω,
            ‖G ω (x / r)
              - G ω (x / t)‖ ^ 2
              ∂μ))
      ≤ (2 / ((r : ℝ)) ^ 2) * ((r : ℝ) * η * (η + (1 + η) * (r : ℝ) / x)) :=
        mul_le_mul_of_nonneg_left hmono hc0
    _ = 2 * η * (η + (1 + η) * (r : ℝ) / x) / (r : ℝ) := hfin

/-- **The expectation of the smoothing error.**  Each interval `[r, r(1+η)]` has length `rη`, and
on it the mean square is at most `η + (1+η)r/x`, so the `r`-th term contributes
`2η(η + (1+η)r/x)/r`.  Summed over `r`, `η²·∑1/r` meets the **harmonic mass** of the rough `r`
(`RMF.exists_sum_inv_rough_Ioc_le`) and `η(1+η)·#S/x` their **count**
(`RMF.exists_roughCount_le`). -/
theorem integral_sum_setIntegral_normSq_sub_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x η : ℝ}
    (hx : 0 < x) (hη : 0 < η) {S : Finset ℕ} (hS : ∀ r ∈ S, 0 < r) :
    (∫ ω, ∑ r ∈ S, (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
        ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
          - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2
        )) / ((r : ℝ)) ^ 2 ∂μ)
      ≤ ∑ r ∈ S, 2 * η * (η + (1 + η) * (r : ℝ) / x) / (r : ℝ) :=
  integral_sum_setIntegral_normSq_sub_le_of_integrable
    (fun ω u => smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y u ω) hx hη hS
    (fun r hr => integrable_uncurry_normSq_sub hX y hx.le (by exact_mod_cast hS r hr))
    (fun r hr t ht => integral_normSq_smoothWeightedSum_sub_le_of_mem_Icc hX y hx
      (by exact_mod_cast hS r hr) ht)

end RMF
