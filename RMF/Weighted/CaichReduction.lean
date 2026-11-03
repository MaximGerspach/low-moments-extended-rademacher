/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Analysis.DilatedParseval
import RMF.Reduction.RademacherUpper
import RMF.Probability.Symmetrisation
import RMF.Weighted.Sieve

/-!
# The short-interval reduction, Rademacher case

The Gorodetsky–Wong reduction of `RMF/Reduction/Steps.lean`, run over a short interval `(x, x+H]`:
the first step of the proof of Theorem 1.1 of Caich (arXiv:2402.06426),
`RMF.integral_rpow_shortSum_le_sqfree`.

* **The conditional variance.**  With `A(t) = RMF.smoothPartial f y t` the `y`-smooth partial sum,
  `∑_{x<n≤x+H} f(n) = ∑_{m ≤ x+H rough} f(m)·(A((x+H)/m) − A(x/m))`
  (`RMF.sum_Ioc_eq_sum_rough_shortSmoothDiff`), so conditional Jensen and
  `RMF.condExp_normSq_roughSmoothSum_sqfree` give
  `E|∑_{x<n≤x+H} f(n)|^{2q} ≤ E[(∑_{m rough} |A((x+H)/m) − A(x/m)|²)^q]`
  (`RMF.integral_rpow_shortSum_le_rough`).
* **Three ranges of `m`.**  `m ≤ N` by orthogonality and Rankin; `N < m ≤ x` by the two-candidate
  bound, the fibres and the dilated Parseval identity; `x < m` pathwise, by a count.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The rough–smooth splitting of a short sum -/

/-- `A((x+H)/m) − A(x/m)`, `A = RMF.smoothPartial f y`: the `y`-smooth part of the short sum over
`(x, x+H]` attached to the rough `m`. -/
noncomputable def shortSmoothDiff (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (x H : ℝ) (ω : Ω)
    (m : ℕ) : ℂ :=
  smoothPartial f y ((x + H) / m) ω - smoothPartial f y (x / m) ω

omit [MeasurableSpace Ω] in
/-- **The rough–smooth splitting of a short sum**: `RMF.sum_Icc_eq_sum_rough_smooth` at `x + H`
and at `x`, the second extended to `m ≤ x + H` by zeros, since `A(x/m) = 0` for `m > x`. -/
lemma sum_Ioc_eq_sum_rough_shortSmoothDiff {f : Ω → ArithmeticFunction ℂ} (y : ℕ) {x H : ℝ}
    (hx : 0 ≤ x) (hH : 0 ≤ H) {ω : Ω} (hmul : (f ω).IsMultiplicative) :
    ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, f ω n
      = ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x + H⌋₊ | IsRough y m},
          f ω m * shortSmoothDiff f y x H ω m := by
  classical
  have hxH : 0 ≤ x + H := by linarith
  have hle : ⌊x⌋₊ ≤ ⌊x + H⌋₊ := Nat.floor_le_floor (by linarith)
  have hIcc : ∀ b : ℕ, Finset.Icc 1 b = Finset.Ioc 0 b := fun b => by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsplit : ∀ z : ℝ, 0 ≤ z → ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, f ω n
      = ∑ m ∈ {m ∈ Finset.Icc 1 ⌊z⌋₊ | IsRough y m}, f ω m * smoothPartial f y (z / m) ω := by
    intro z hz
    rw [sum_Icc_eq_sum_rough_smooth y hz hmul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smoothPartial, Finset.mul_sum]
  have hext : ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m}, f ω m * smoothPartial f y (x / m) ω
      = ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x + H⌋₊ | IsRough y m},
          f ω m * smoothPartial f y (x / m) ω := by
    refine Finset.sum_subset (fun m hm => ?_) (fun m hm hmx => ?_)
    · rw [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
      exact ⟨⟨hm.1.1, le_trans hm.1.2 hle⟩, hm.2⟩
    · rw [Finset.mem_filter, Finset.mem_Icc] at hm hmx
      have hm1 : 1 ≤ m := hm.1.1
      have hmx' : ⌊x⌋₊ < m := by
        by_contra hc
        exact hmx ⟨⟨hm1, not_lt.1 hc⟩, hm.2⟩
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
      have hxm : x / m < 1 := by
        rw [div_lt_one hmR]
        have h1 := Nat.lt_floor_add_one x
        have hm' : (⌊x⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast hmx'
        linarith
      rw [smoothPartial_eq_zero hxm, mul_zero]
  have hIoc : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, f ω n
      = ∑ n ∈ Finset.Icc 1 ⌊x + H⌋₊, f ω n - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f ω n := by
    rw [hIcc, hIcc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊x⌋₊) hle]
    ring
  rw [hIoc, hsplit (x + H) hxH, hsplit x hx, hext, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [shortSmoothDiff, mul_sub]

/-! ### The conditional variance -/

omit [MeasurableSpace Ω] in
/-- The squarefree smooth partial sum is measurable for the smooth `σ`-algebra. -/
lemma measurable_smoothAlgebra_smoothPartial_sqfree {X : ℕ → Ω → ℂ} (y : ℕ) (t : ℝ) :
    Measurable[smoothAlgebra X y]
      (smoothPartial (fun ω => squarefreeExtension fun p => X p ω) y t) :=
  Finset.measurable_sum _ fun _ hn =>
    measurable_smoothAlgebra_squarefreeExtension (Finset.mem_filter.1 hn).2

/-- **The conditional second moment of a short sum, Rademacher case.**  An identity:
`E[|∑_{x<n≤x+H} f(n)|² | 𝓕_y] = ∑_{m ≤ x+H rough, squarefree} |A((x+H)/m) − A(x/m)|²`.

`RMF.condExp_normSq_roughSmoothSum_sqfree` at `x + H`, with the smooth factor
`√m·(A((x+H)/m) − A(x/m))`. -/
theorem condExp_normSq_shortSum_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x H : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) :
    μ[fun ω => ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, squarefreeExtension (fun p => X p ω) n‖ ^ 2
        | smoothAlgebra X y]
      =ᵐ[μ] fun ω => ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x + H⌋₊ | IsRough y m ∧ Squarefree m},
          ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2 := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have key := condExp_normSq_roughSmoothSum_sqfree (x := x + H) hX
    (G := fun m ω => ((Real.sqrt m : ℝ) : ℂ)
      * shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m)
    (B := fun m => Real.sqrt m * ((⌊(x + H) / m⌋₊ : ℝ) + (⌊x / m⌋₊ : ℝ)))
    (fun m => measurable_const.mul ((measurable_smoothAlgebra_smoothPartial_sqfree y _).sub
      (measurable_smoothAlgebra_smoothPartial_sqfree y _)))
    (fun m => by
      filter_upwards [ae_norm_smoothPartial_le hRa.isBoundedRMF y ((x + H) / m),
        ae_norm_smoothPartial_le hRa.isBoundedRMF y (x / m)] with ω h1 h2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        shortSmoothDiff]
      exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2))
        (Real.sqrt_nonneg _))
  refine Filter.EventuallyEq.trans (condExp_congr_ae ?_) (key.trans ?_)
  · refine Filter.Eventually.of_forall fun ω => ?_
    have hsum := sum_Ioc_eq_sum_rough_shortSmoothDiff
      (f := fun ω => squarefreeExtension fun p => X p ω) y hx hH (hRa.isMultiplicative ω)
    simp only at hsum ⊢
    rw [hsum]
    refine congrArg (fun z : ℂ => ‖z‖ ^ 2) (Finset.sum_congr rfl fun m hm => ?_)
    have hm1 : (1 : ℝ) ≤ m := by
      rw [Finset.mem_filter, Finset.mem_Icc] at hm
      exact_mod_cast hm.1.1
    have hs : ((Real.sqrt m : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by linarith)).ne'
    rw [Complex.ofReal_inv]
    field_simp
  · refine Filter.Eventually.of_forall fun ω => Finset.sum_congr rfl fun m hm => ?_
    have hm1 : (1 : ℝ) ≤ m := by
      rw [Finset.mem_filter, Finset.mem_Icc] at hm
      exact_mod_cast hm.1.1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (by linarith), ← mul_assoc, inv_mul_cancel₀ (by linarith), one_mul]

/-- **Conditional Jensen for a short sum.**  Jensen for `t ↦ t^q` given the smooth primes, then the
conditional second moment, widened from the squarefree rough `m` to all rough `m`:

`E|∑_{x<n≤x+H} f(n)|^{2q} ≤ E[(∑_{m ≤ x+H rough} |A((x+H)/m) − A(x/m)|²)^q]`. -/
theorem integral_rpow_shortSum_le_rough {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x H q : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, squarefreeExtension (fun p => X p ω) n‖ ^ (2 * q) ∂μ
      ≤ ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x + H⌋₊ | IsRough y m},
          ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2) ^ q
          ∂μ := by
  classical
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hle := smoothAlgebra_le hX y
  haveI : SigmaFinite (μ.trim hle) := (isFiniteMeasure_trim hle).toSigmaFinite
  have hS : Measurable fun ω =>
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, squarefreeExtension (fun p => X p ω) n :=
    Finset.measurable_sum _ fun n _ => hRa.isBoundedRMF.measurable_apply n
  have hSb : ∀ᵐ ω ∂μ,
      ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, squarefreeExtension (fun p => X p ω) n‖
        ≤ ((Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℝ) := by
    have hall : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, ∀ᵐ ω ∂μ,
        ‖squarefreeExtension (fun p => X p ω) n‖ ≤ 1 := fun n _ => hRa.norm_apply_le_one n
    filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, ‖squarefreeExtension (fun p => X p ω) n‖
        ≤ ∑ _n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, (1 : ℝ) := Finset.sum_le_sum fun n hn => hω n hn
      _ = ((Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hid := condExp_normSq_shortSum_sqfree hX y hx hH
  -- the rough sum is measurable and bounded, so its `q`-th power is integrable
  set s : Finset ℕ := {m ∈ Finset.Icc 1 ⌊x + H⌋₊ | IsRough y m} with hsdef
  set V : Ω → ℝ := fun ω => ∑ m ∈ s,
    ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2 with hVdef
  have hVm : Measurable V := by
    refine Finset.measurable_sum _ fun m _ => ?_
    have h := ((measurable_smoothAlgebra_smoothPartial_sqfree (X := X) y ((x + H) / m)).sub
      (measurable_smoothAlgebra_smoothPartial_sqfree (X := X) y (x / m))).mono hle le_rfl
    exact h.norm.pow_const 2
  set K : ℝ := (s.card : ℝ) * (2 * (⌊x + H⌋₊ : ℝ)) ^ 2 with hKdef
  have hV0 : ∀ ω, 0 ≤ V ω := fun ω => Finset.sum_nonneg fun m _ => sq_nonneg _
  have hVb : ∀ᵐ ω ∂μ, V ω ≤ K := by
    have hall : ∀ m ∈ s, ∀ᵐ ω ∂μ,
        ‖smoothPartial (fun ω => squarefreeExtension fun p => X p ω) y ((x + H) / m) ω‖
            ≤ (⌊(x + H) / m⌋₊ : ℝ)
          ∧ ‖smoothPartial (fun ω => squarefreeExtension fun p => X p ω) y (x / m) ω‖
            ≤ (⌊x / m⌋₊ : ℝ) := fun m _ =>
      (ae_norm_smoothPartial_le hRa.isBoundedRMF y _).and
        (ae_norm_smoothPartial_le hRa.isBoundedRMF y _)
    filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
    calc V ω ≤ ∑ _m ∈ s, (2 * (⌊x + H⌋₊ : ℝ)) ^ 2 := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm1 : (1 : ℝ) ≤ m := by
            rw [hsdef, Finset.mem_filter, Finset.mem_Icc] at hm
            exact_mod_cast hm.1.1
          have hmR : (0 : ℝ) < m := by linarith
          have hf1 : (⌊(x + H) / m⌋₊ : ℝ) ≤ ⌊x + H⌋₊ := by
            exact_mod_cast Nat.floor_le_floor (div_le_self (by linarith) hm1)
          have hf2 : (⌊x / m⌋₊ : ℝ) ≤ ⌊x + H⌋₊ := by
            exact_mod_cast Nat.floor_le_floor
              (le_trans (div_le_self hx hm1) (by linarith))
          have hn : ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖
              ≤ 2 * (⌊x + H⌋₊ : ℝ) := by
            rw [shortSmoothDiff]
            refine (norm_sub_le _ _).trans ?_
            linarith [(hω m hm).1, (hω m hm).2]
          exact pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = K := by rw [Finset.sum_const, nsmul_eq_mul]
  have hVq : Integrable (fun ω => V ω ^ q) μ := by
    refine (memLp_top_of_bound (hVm.pow_const q).aestronglyMeasurable (K ^ q) ?_).integrable
      le_top
    filter_upwards [hVb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hV0 ω) _)]
    exact Real.rpow_le_rpow (hV0 ω) hω hq0
  calc ∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, squarefreeExtension (fun p => X p ω) n‖
        ^ (2 * q) ∂μ
      ≤ ∫ ω, (μ[fun ω => ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊,
          squarefreeExtension (fun p => X p ω) n‖ ^ 2 | smoothAlgebra X y] ω) ^ q ∂μ :=
        integral_rpow_norm_le_integral_condExp_rpow hle hS hSb hq0 hq1
    _ ≤ ∫ ω, V ω ^ q ∂μ := by
        refine integral_mono_of_nonneg ?_ hVq ?_
        · filter_upwards [hid] with ω hω
          rw [hω]
          exact Real.rpow_nonneg (Finset.sum_nonneg fun m _ => sq_nonneg _) _
        · filter_upwards [hid] with ω hω
          rw [hω]
          refine Real.rpow_le_rpow (Finset.sum_nonneg fun m _ => sq_nonneg _) ?_ hq0
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) fun m _ _ => sq_nonneg _
          rw [Finset.mem_filter] at hm
          rw [hsdef, Finset.mem_filter]
          exact ⟨hm.1, hm.2.1⟩

/-! ### The large range: two candidates, fibres, and the integral

For `m` with `⌊x/m⌋ = r` the lower end `A(x/m)` is `A(u)` for every `u ∈ [r, r+1)`, but the upper
end `A((x+H)/m)` is not a function of `r`.  It is, up to two terms: `(x+H)/m = λ·(x/m)` and `λu`
both lie in `[λr, λ(r+1))`, an interval of length `λ = (x+H)/x ≤ 2`, and a half-open interval of
length less than two holds at most two integers (`RMF.norm_smoothPartial_sub_le_two`).  Hence
`|A((x+H)/m) − A(x/m)|² ≤ 2|A(λu) − A(u)|² + 8` (`RMF.normSq_shortSmoothDiff_le_of_mem`), and
averaging over `u` puts the fibre on the integral. -/

omit [MeasurableSpace Ω] in
/-- `A(t) − A(s) = ∑_{s < n ≤ t, smooth} f(n)` for `s ≤ t`. -/
lemma smoothPartial_sub_eq_sum_Ioc (f : Ω → ArithmeticFunction ℂ) (y : ℕ) {s t : ℝ}
    (hst : s ≤ t) (ω : Ω) :
    smoothPartial f y t ω - smoothPartial f y s ω
      = ∑ n ∈ {n ∈ Finset.Ioc ⌊s⌋₊ ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, f ω n := by
  have hle : ⌊s⌋₊ ≤ ⌊t⌋₊ := Nat.floor_le_floor hst
  have hdisj : Disjoint {n ∈ Finset.Ioc ⌊s⌋₊ ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}
      {n ∈ Finset.Icc 1 ⌊s⌋₊ | n ∈ Nat.smoothNumbers (y + 1)} := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    rw [Finset.mem_filter, Finset.mem_Ioc] at h1
    rw [Finset.mem_filter, Finset.mem_Icc] at h2
    obtain ⟨⟨h1a, -⟩, -⟩ := h1
    obtain ⟨⟨-, h2b⟩, -⟩ := h2
    omega
  rw [smoothPartial, smoothPartial, sub_eq_iff_eq_add, ← Finset.sum_union hdisj]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hsm⟩
    by_cases hns : n ≤ ⌊s⌋₊
    · exact Or.inr ⟨⟨h1, hns⟩, hsm⟩
    · exact Or.inl ⟨⟨by omega, h2⟩, hsm⟩
  · rintro (⟨⟨h1, h2⟩, hsm⟩ | ⟨⟨h1, h2⟩, hsm⟩)
    · exact ⟨⟨by omega, h2⟩, hsm⟩
    · exact ⟨⟨h1, by omega⟩, hsm⟩

omit [MeasurableSpace Ω] in
/-- **Nearby endpoints give nearby smooth sums.**  If `|f| ≤ 1` and `0 ≤ s ≤ t < s + 2`, then
`‖A(t) − A(s)‖ ≤ 2`: at most two integers lie in `(s, t]`. -/
lemma norm_smoothPartial_sub_le_two {f : Ω → ArithmeticFunction ℂ} {y : ℕ} {ω : Ω}
    (hf : ∀ n, ‖f ω n‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < s + 2) :
    ‖smoothPartial f y t ω - smoothPartial f y s ω‖ ≤ 2 := by
  rw [smoothPartial_sub_eq_sum_Ioc f y hst ω]
  have h1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have h2 : s < (⌊s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s
  have h4 : ⌊t⌋₊ < ⌊s⌋₊ + 3 := by
    have h3 : (⌊t⌋₊ : ℝ) < (⌊s⌋₊ : ℝ) + 3 := by linarith
    exact_mod_cast h3
  have hcard : ({n ∈ Finset.Ioc ⌊s⌋₊ ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)} : Finset ℕ).card
      ≤ 2 := by
    refine le_trans (Finset.card_filter_le _ _) ?_
    rw [Nat.card_Ioc]
    omega
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ n ∈ {n ∈ Finset.Ioc ⌊s⌋₊ ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, ‖f ω n‖
      ≤ ∑ _n ∈ {n ∈ Finset.Ioc ⌊s⌋₊ ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => hf n
    _ = (({n ∈ Finset.Ioc ⌊s⌋₊ ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)} : Finset ℕ).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 2 := by exact_mod_cast hcard

omit [MeasurableSpace Ω] in
/-- **The two-candidate bound.**  For `|f| ≤ 1`, `0 ≤ H ≤ x`, `⌊x/m⌋ = r` and `u ∈ [r, r+1)`,

`|A((x+H)/m) − A(x/m)|² ≤ 2|A(λu) − A(u)|² + 8`,   `λ = (x+H)/x`. -/
lemma normSq_shortSmoothDiff_le_of_mem {f : Ω → ArithmeticFunction ℂ} {y : ℕ} {ω : Ω}
    (hf : ∀ n, ‖f ω n‖ ≤ 1) {x H : ℝ} (hx : 0 < x) (hH : 0 ≤ H) (hHx : H ≤ x) {m r : ℕ}
    (hm : 0 < m) (hr : ⌊x / (m : ℝ)⌋₊ = r) {u : ℝ} (hu0 : (r : ℝ) ≤ u)
    (hu1 : u < (r : ℝ) + 1) :
    ‖shortSmoothDiff f y x H ω m‖ ^ 2
      ≤ 2 * ‖smoothPartial f y ((x + H) / x * u) ω - smoothPartial f y u ω‖ ^ 2 + 8 := by
  set l : ℝ := (x + H) / x with hldef
  have hl1 : 1 ≤ l := by rw [hldef, le_div_iff₀ hx]; linarith
  have hl2 : l ≤ 2 := by rw [hldef, div_le_iff₀ hx]; linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hxm0 : 0 ≤ x / m := div_nonneg hx.le hmR.le
  have hu : 0 ≤ u := le_trans (Nat.cast_nonneg r) hu0
  have hxr : (r : ℝ) ≤ x / m := by rw [← hr]; exact Nat.floor_le hxm0
  have hxr1 : x / m < (r : ℝ) + 1 := by rw [← hr]; exact Nat.lt_floor_add_one _
  have hAu : smoothPartial f y (x / m) ω = smoothPartial f y u ω := by
    refine smoothPartial_congr f y ?_ ω
    rw [hr]
    exact ((Nat.floor_eq_iff hu).2 ⟨hu0, hu1⟩).symm
  have hlm : (x + H) / m = l * (x / m) := by rw [hldef, div_mul_div_cancel₀ hx.ne']
  have hlu0 : 0 ≤ l * u := mul_nonneg (by linarith) hu
  have hxH0 : 0 ≤ (x + H) / m := div_nonneg (by linarith) hmR.le
  -- `l·(x/m)` and `l·u` both lie in `[l r, l(r+1))`, of length `l ≤ 2`
  have hA : l * (x / m) < l * u + 2 := by
    have e1 : l * (x / m) < l * ((r : ℝ) + 1) := mul_lt_mul_of_pos_left hxr1 (by linarith)
    have e2 : l * (r : ℝ) ≤ l * u := mul_le_mul_of_nonneg_left hu0 (by linarith)
    linarith
  have hB : l * u < l * (x / m) + 2 := by
    have e1 : l * u < l * ((r : ℝ) + 1) := mul_lt_mul_of_pos_left hu1 (by linarith)
    have e2 : l * (r : ℝ) ≤ l * (x / m) := mul_le_mul_of_nonneg_left hxr (by linarith)
    linarith
  have hclose : ‖smoothPartial f y ((x + H) / m) ω - smoothPartial f y (l * u) ω‖ ≤ 2 := by
    rcases le_total (l * u) ((x + H) / m) with h | h
    · exact norm_smoothPartial_sub_le_two hf hlu0 h (by rw [hlm]; exact hA)
    · rw [norm_sub_rev]
      exact norm_smoothPartial_sub_le_two hf hxH0 h (by rw [hlm]; exact hB)
  have htri : ‖smoothPartial f y ((x + H) / m) ω - smoothPartial f y u ω‖
      ≤ 2 + ‖smoothPartial f y (l * u) ω - smoothPartial f y u ω‖ := by
    have hsplit : smoothPartial f y ((x + H) / m) ω - smoothPartial f y u ω
        = (smoothPartial f y ((x + H) / m) ω - smoothPartial f y (l * u) ω)
          + (smoothPartial f y (l * u) ω - smoothPartial f y u ω) := by ring
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hclose le_rfl)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  rw [shortSmoothDiff, hAu]
  linarith [sq_nonneg (‖smoothPartial f y (l * u) ω - smoothPartial f y u ω‖ - 2)]

omit [MeasurableSpace Ω] in
/-- **The large range of `m`, pathwise.**  On a path with `|f| ≤ 1`, for rough `m` in the fibres
`⌊x/m⌋ = r ∈ [1, R]` with the sieve conditions of `RMF.sum_roughTerm_large_le`,
`∑_m |A((x+H)/m) − A(x/m)|² ≤ (C_s x/log y)·(4∫_0^∞ |A(λu) − A(u)|² u^{−2} du + 16)`.
Each fibre: the two-candidate bound averaged over `u ∈ (r, r+1]`, times the sieve count
`C_s x/(r(r+1) log y)`; the fibres then tile `(1, R+1]`. -/
lemma sum_normSq_shortSmoothDiff_large_le {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hS : ∀ (y : ℕ) (x H : ℝ), 2 ≤ y → 0 < x → 0 < H → (y : ℝ) ≤ H →
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ H →
      (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ) ≤ Cs * H / Real.log y)
    {f : Ω → ArithmeticFunction ℂ} {y : ℕ} (hy : 2 ≤ y) {x H : ℝ} (hx : 0 < x) (hH : 0 ≤ H)
    (hHx : H ≤ x) {R : ℕ} {s : Finset ℕ} (hs0 : ∀ m ∈ s, 0 < m)
    (hmaps : ∀ m ∈ s, ⌊x / (m : ℝ)⌋₊ ∈ Finset.Icc 1 R)
    (hsieveOK : ∀ r ∈ Finset.Icc 1 R, 2 ≤ x / ((r : ℝ) + 1) ∧
      2 ≤ x / r - x / ((r : ℝ) + 1) ∧ (y : ℝ) ≤ x / r - x / ((r : ℝ) + 1) ∧
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ x / r - x / ((r : ℝ) + 1))
    (hfib : ∀ r ∈ Finset.Icc 1 R,
      s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)
        ⊆ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r})
    {ω : Ω} (hf : ∀ n, ‖f ω n‖ ≤ 1)
    (hint : IntegrableOn (fun u : ℝ =>
      ‖smoothPartial f y ((x + H) / x * u) ω - smoothPartial f y u ω‖ ^ 2 / u ^ 2)
      (Set.Ioi (0 : ℝ))) :
    ∑ m ∈ s, ‖shortSmoothDiff f y x H ω m‖ ^ 2
      ≤ Cs * x / Real.log y * (4 * (∫ u in Set.Ioi (0 : ℝ),
          ‖smoothPartial f y ((x + H) / x * u) ω - smoothPartial f y u ω‖ ^ 2 / u ^ 2) + 16) := by
  classical
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hCx : 0 ≤ Cs * x / Real.log y := div_nonneg (mul_nonneg hCs hx.le) hL.le
  set g : ℝ → ℝ := fun u =>
    ‖smoothPartial f y ((x + H) / x * u) ω - smoothPartial f y u ω‖ ^ 2 with hgdef
  have hg0 : ∀ u, 0 ≤ g u := fun u => sq_nonneg _
  have hgnn : ∀ u : ℝ, 0 ≤ g u / u ^ 2 := fun u => div_nonneg (hg0 u) (sq_nonneg u)
  set φ : ℝ → ℝ := fun u => (2 * g u + 8) / u ^ 2 with hφdef
  have hφ0 : ∀ u, 0 ≤ φ u := fun u => by
    simp only [hφdef]
    exact div_nonneg (by linarith [hg0 u]) (sq_nonneg u)
  -- `1/u²` and `φ` are integrable on `(1, ∞)`, and `∫_{(1,∞)} u^{-2} = 1`
  have hEq : Set.EqOn (fun u : ℝ => u ^ (-2 : ℝ)) (fun u : ℝ => 1 / u ^ 2) (Set.Ioi 1) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos (Set.mem_Ioi.1 hu)
    change u ^ (-2 : ℝ) = 1 / u ^ 2
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hu0.le, Real.rpow_natCast,
      one_div]
  have hinv : IntegrableOn (fun u : ℝ => 1 / u ^ 2) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).congr_fun hEq
      measurableSet_Ioi
  have hinvval : (∫ u in Set.Ioi (1 : ℝ), 1 / u ^ 2) = 1 := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hEq,
      integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos]
    norm_num
  have hg1 : IntegrableOn (fun u => g u / u ^ 2) (Set.Ioi 1) :=
    hint.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have hφeq : ∀ u, φ u = 2 * (g u / u ^ 2) + 8 * (1 / u ^ 2) := fun u => by
    simp only [hφdef]
    ring
  have hφint : IntegrableOn φ (Set.Ioi 1) := by
    have h : IntegrableOn (fun u => 2 * (g u / u ^ 2) + 8 * (1 / u ^ 2)) (Set.Ioi 1) :=
      (hg1.const_mul 2).add (hinv.const_mul 8)
    exact h.congr_fun (fun u _ => (hφeq u).symm) measurableSet_Ioi
  have hφr : ∀ r ∈ Finset.Icc 1 R, IntegrableOn φ (Set.Ioc (r : ℝ) (r + 1)) := by
    intro r hr
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.1 hr).1
    exact hφint.mono_set fun u hu => lt_of_le_of_lt hr1 hu.1
  have hnull : ∀ᵐ u ∂(volume : Measure ℝ), ∀ r : ℕ, u ≠ (r : ℝ) + 1 := by
    rw [ae_all_iff]
    intro r
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (Real.volume_singleton (a := (r : ℝ) + 1))] with u hu
    exact fun h => hu (Set.mem_singleton_iff.2 h)
  -- one fibre
  have hfibre : ∀ r ∈ Finset.Icc 1 R,
      ∑ m ∈ s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r), ‖shortSmoothDiff f y x H ω m‖ ^ 2
        ≤ Cs * x / Real.log y * (2 * ∫ u in Set.Ioc (r : ℝ) (r + 1), φ u) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.1 hr).1
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    obtain ⟨h1, h2, h3, h4⟩ := hsieveOK r hr
    have hcard : ((s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)).card : ℝ)
        ≤ Cs * (x / r - x / ((r : ℝ) + 1)) / Real.log y := by
      refine le_trans ?_ (card_fibre_le_of_sieve hS hy hx.le (by omega) h1 h2 h3 h4)
      exact_mod_cast Finset.card_le_card (hfib r hr)
    have hI0 : 0 ≤ ∫ u in Set.Ioc (r : ℝ) (r + 1), φ u :=
      setIntegral_nonneg measurableSet_Ioc fun u _ => hφ0 u
    have hT : ∀ m ∈ s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r),
        ‖shortSmoothDiff f y x H ω m‖ ^ 2
          ≤ ((r : ℝ) + 1) ^ 2 * ∫ u in Set.Ioc (r : ℝ) (r + 1), φ u := by
      intro m hm
      rw [Finset.mem_filter] at hm
      have hconst : (∫ _u in Set.Ioc (r : ℝ) (r + 1), ‖shortSmoothDiff f y x H ω m‖ ^ 2)
          = ‖shortSmoothDiff f y x H ω m‖ ^ 2 := by
        rw [setIntegral_const, smul_eq_mul,
          Real.volume_real_Ioc_of_le (show (r : ℝ) ≤ r + 1 by linarith),
          show (r : ℝ) + 1 - r = 1 by ring, one_mul]
      rw [← hconst, ← integral_const_mul]
      refine setIntegral_mono_ae_restrict
        (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
        ((hφr r hr).const_mul _) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hnull]
        with u hu hu1
      have hu1' : u < (r : ℝ) + 1 := lt_of_le_of_ne hu.2 (hu1 r)
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one (le_trans hrR hu.1.le)
      have hbd := normSq_shortSmoothDiff_le_of_mem (y := y) hf hx hH hHx (hs0 m hm.1) hm.2
        hu.1.le hu1'
      have hφu : 2 * g u + 8 = u ^ 2 * φ u := by
        simp only [hφdef]
        rw [mul_div_cancel₀ _ (pow_ne_zero 2 hu0.ne')]
      have hu2 : u ^ 2 ≤ ((r : ℝ) + 1) ^ 2 := pow_le_pow_left₀ hu0.le hu.2 2
      calc ‖shortSmoothDiff f y x H ω m‖ ^ 2 ≤ 2 * g u + 8 := hbd
        _ = u ^ 2 * φ u := hφu
        _ ≤ ((r : ℝ) + 1) ^ 2 * φ u := mul_le_mul_of_nonneg_right hu2 (hφ0 u)
    calc ∑ m ∈ s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r), ‖shortSmoothDiff f y x H ω m‖ ^ 2
        ≤ ∑ _m ∈ s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r),
            ((r : ℝ) + 1) ^ 2 * ∫ u in Set.Ioc (r : ℝ) (r + 1), φ u := Finset.sum_le_sum hT
      _ = ((s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)).card : ℝ)
            * (((r : ℝ) + 1) ^ 2 * ∫ u in Set.Ioc (r : ℝ) (r + 1), φ u) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Cs * (x / r - x / ((r : ℝ) + 1)) / Real.log y
            * (((r : ℝ) + 1) ^ 2 * ∫ u in Set.Ioc (r : ℝ) (r + 1), φ u) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg (sq_nonneg _) hI0)
      _ = Cs * x / Real.log y * (((r : ℝ) + 1) / r * ∫ u in Set.Ioc (r : ℝ) (r + 1), φ u) := by
          have hr0 : (r : ℝ) ≠ 0 := (lt_of_lt_of_le zero_lt_one hrR).ne'
          have hr10 : (r : ℝ) + 1 ≠ 0 := by positivity
          have hL0 : Real.log y ≠ 0 := hL.ne'
          field_simp
          ring
      _ ≤ Cs * x / Real.log y * (2 * ∫ u in Set.Ioc (r : ℝ) (r + 1), φ u) := by
          have hr2 : ((r : ℝ) + 1) / r ≤ 2 := by
            rw [div_le_iff₀ (by linarith)]
            linarith
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr2 hI0) hCx
  -- the fibres tile `(1, R+1]`
  have hdisj : Set.Pairwise (↑(Finset.Icc 1 R) : Set ℕ)
      (Function.onFun Disjoint fun r : ℕ => Set.Ioc (r : ℝ) (r + 1)) := by
    intro a _ b _ hab
    rw [Function.onFun_apply, Set.disjoint_left]
    intro u hua hub
    rcases lt_or_gt_of_ne hab with h | h
    · have h' : a + 1 ≤ b := by omega
      have h'' : (a : ℝ) + 1 ≤ b := by exact_mod_cast h'
      linarith [hua.2, hub.1]
    · have h' : b + 1 ≤ a := by omega
      have h'' : (b : ℝ) + 1 ≤ a := by exact_mod_cast h'
      linarith [hub.2, hua.1]
  have htile : ∑ r ∈ Finset.Icc 1 R, ∫ u in Set.Ioc (r : ℝ) (r + 1), φ u
      ≤ ∫ u in Set.Ioi (1 : ℝ), φ u := by
    rw [← integral_biUnion_finset (Finset.Icc 1 R) (s := fun r : ℕ => Set.Ioc (r : ℝ) (r + 1))
      (fun r _ => measurableSet_Ioc) hdisj hφr]
    refine setIntegral_mono_set hφint (Filter.Eventually.of_forall fun u => hφ0 u)
      (Filter.Eventually.of_forall ?_)
    intro u hu
    have hu' : u ∈ ⋃ r ∈ Finset.Icc 1 R, Set.Ioc (r : ℝ) (r + 1) := hu
    obtain ⟨r, hr, hur⟩ := Set.mem_iUnion₂.1 hu'
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.1 hr).1
    change (1 : ℝ) < u
    exact lt_of_le_of_lt hr1 hur.1
  have hφval : (∫ u in Set.Ioi (1 : ℝ), φ u)
      ≤ 2 * (∫ u in Set.Ioi (0 : ℝ), g u / u ^ 2) + 8 := by
    have hsplit : (∫ u in Set.Ioi (1 : ℝ), φ u)
        = 2 * (∫ u in Set.Ioi (1 : ℝ), g u / u ^ 2) + 8 * ∫ u in Set.Ioi (1 : ℝ), 1 / u ^ 2 := by
      simp only [hφeq]
      rw [integral_add (hg1.const_mul 2) (hinv.const_mul 8), integral_const_mul,
        integral_const_mul]
    have hmono : (∫ u in Set.Ioi (1 : ℝ), g u / u ^ 2) ≤ ∫ u in Set.Ioi (0 : ℝ), g u / u ^ 2 := by
      refine setIntegral_mono_set hint (Filter.Eventually.of_forall hgnn)
        (Filter.Eventually.of_forall ?_)
      intro u hu
      have hu' : u ∈ Set.Ioi (1 : ℝ) := hu
      exact Set.Ioi_subset_Ioi zero_le_one hu'
    rw [hsplit, hinvval]
    linarith
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ r ∈ Finset.Icc 1 R, ∑ m ∈ s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r),
          ‖shortSmoothDiff f y x H ω m‖ ^ 2
      ≤ ∑ r ∈ Finset.Icc 1 R, Cs * x / Real.log y * (2 * ∫ u in Set.Ioc (r : ℝ) (r + 1), φ u) :=
        Finset.sum_le_sum hfibre
    _ = Cs * x / Real.log y * (2 * ∑ r ∈ Finset.Icc 1 R, ∫ u in Set.Ioc (r : ℝ) (r + 1), φ u) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ Cs * x / Real.log y * (2 * (2 * (∫ u in Set.Ioi (0 : ℝ), g u / u ^ 2) + 8)) :=
        mul_le_mul_of_nonneg_left (by linarith [htile, hφval]) hCx
    _ = Cs * x / Real.log y * (4 * (∫ u in Set.Ioi (0 : ℝ),
          ‖smoothPartial f y ((x + H) / x * u) ω - smoothPartial f y u ω‖ ^ 2 / u ^ 2) + 16) := by
        simp only [hgdef]
        ring

/-! ### The three ranges of `m`

The rough `m ≤ x + H` split as `m ≤ N`, `N < m ≤ x` and `x < m`
(`RMF.sum_rough_Icc_eq_three`).  The first range is bounded in expectation — orthogonality, then
Rankin — and the top range pathwise, by the number of rough `m ∈ (x, x+H]`. -/

/-- The short difference is bounded a.s. by the number of integers below its two endpoints. -/
lemma ae_norm_shortSmoothDiff_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) (x H : ℝ) (m : ℕ) :
    ∀ᵐ ω ∂μ, ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖
      ≤ (⌊(x + H) / m⌋₊ : ℝ) + (⌊x / m⌋₊ : ℝ) := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  filter_upwards [ae_norm_smoothPartial_le hRa.isBoundedRMF y ((x + H) / m),
    ae_norm_smoothPartial_le hRa.isBoundedRMF y (x / m)] with ω h1 h2
  rw [shortSmoothDiff]
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

lemma measurable_normSq_shortSmoothDiff {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) (x H : ℝ) (m : ℕ) :
    Measurable fun ω =>
      ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2 := by
  have h := ((measurable_smoothAlgebra_smoothPartial_sqfree (X := X) y ((x + H) / m)).sub
    (measurable_smoothAlgebra_smoothPartial_sqfree (X := X) y (x / m))).mono
    (smoothAlgebra_le hX y) le_rfl
  exact h.norm.pow_const 2

/-- Every range's `q`-th power is integrable: the sum is measurable and bounded a.s. -/
lemma integrable_rpow_sum_normSq_shortSmoothDiff {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) (x H : ℝ) (s : Finset ℕ) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun ω => (∑ m ∈ s,
      ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2) ^ q) μ := by
  haveI := hX.isProbabilityMeasure
  have hV0 : ∀ ω, 0 ≤ ∑ m ∈ s,
      ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2 :=
    fun ω => Finset.sum_nonneg fun m _ => sq_nonneg _
  have hVm : Measurable fun ω => (∑ m ∈ s,
      ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2) ^ q :=
    (Finset.measurable_sum _ fun m _ => measurable_normSq_shortSmoothDiff hX y x H m).pow_const q
  refine (memLp_top_of_bound hVm.aestronglyMeasurable
    ((∑ m ∈ s, ((⌊(x + H) / m⌋₊ : ℝ) + (⌊x / m⌋₊ : ℝ)) ^ 2) ^ q) ?_).integrable le_top
  have hall : ∀ m ∈ s, ∀ᵐ ω ∂μ,
      ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖
        ≤ (⌊(x + H) / m⌋₊ : ℝ) + (⌊x / m⌋₊ : ℝ) :=
    fun m _ => ae_norm_shortSmoothDiff_le hX y x H m
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hV0 ω) _)]
  refine Real.rpow_le_rpow (hV0 ω) (Finset.sum_le_sum fun m hm => ?_) hq
  exact pow_le_pow_left₀ (norm_nonneg _) (hω m hm) 2

/-- **Orthogonality for one short difference**: `E|A((x+H)/m) − A(x/m)|² ≤ Ψ((x+H)/m, y)`, the
difference being a sum over the smooth `n ∈ (x/m, (x+H)/m]`. -/
lemma integral_normSq_shortSmoothDiff_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x H : ℝ} (hH : 0 ≤ H) (m : ℕ) :
    ∫ ω, ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2 ∂μ
      ≤ (smoothCount y ((x + H) / m) : ℝ) := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hle : x / m ≤ (x + H) / m := div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg m)
  have hid : ∀ ω, shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m
      = ∑ n ∈ {n ∈ Finset.Ioc ⌊x / m⌋₊ ⌊(x + H) / m⌋₊ | n ∈ Nat.smoothNumbers (y + 1)},
          squarefreeExtension (fun p => X p ω) n :=
    fun ω => smoothPartial_sub_eq_sum_Ioc _ y hle ω
  simp_rw [hid]
  have hne : ∀ n ∈ {n ∈ Finset.Ioc ⌊x / m⌋₊ ⌊(x + H) / m⌋₊ | n ∈ Nat.smoothNumbers (y + 1)},
      n ≠ 0 := by
    intro n hn
    have := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hn).1).1
    omega
  refine le_trans (hRa.isBoundedRMF.integral_normSq_sum_le _ hne) ?_
  rw [smoothCount]
  refine Nat.cast_le.2 (Finset.card_le_card fun n hn => ?_)
  rw [Finset.mem_filter, Finset.mem_Ioc] at hn
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩

/-- **The small range, in expectation.**  Jensen, orthogonality, and Rankin at `x + H`
(`RMF.sum_smoothCount_div_le`). -/
theorem integral_rpow_sum_shortSmoothDiff_small_le {A cR CR : ℝ}
    (hR : ∀ (y : ℕ) (x : ℝ), 2 ≤ y → 2 ≤ x →
      (smoothCount y x : ℝ)
        ≤ CR * x * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y))
    (hCR : 0 ≤ CR) {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {y : ℕ} (hy : 2 ≤ y) {x H q : ℝ} (hx : 0 < x) (hH : 0 ≤ H) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {N : ℕ} {s : Finset ℕ} (hsub : s ⊆ Finset.Icc 1 N) (hsm : ∀ m ∈ s, 0 < m ∧ 2 ≤ x / m)
    (hβ0 : 0 < cR / Real.log y) (hβ1 : cR / Real.log y ≤ 1) :
    ∫ ω, (∑ m ∈ s,
        ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2) ^ q ∂μ
      ≤ ((x + H) * (CR * Real.log y ^ A * Real.exp (-cR * Real.log (x + H) / Real.log y)
          * (1 + (N : ℝ) ^ (cR / Real.log y) / (cR / Real.log y)))) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hxH : 0 < x + H := by linarith
  have hsm' : ∀ m ∈ s, 0 < m ∧ 2 ≤ (x + H) / m := fun m hm =>
    ⟨(hsm m hm).1, le_trans (hsm m hm).2
      (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg m))⟩
  have hV0 : ∀ ω, 0 ≤ ∑ m ∈ s,
      ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2 :=
    fun ω => Finset.sum_nonneg fun m _ => sq_nonneg _
  have hint1 : Integrable (fun ω => ∑ m ∈ s,
      ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2) μ := by
    have h := integrable_rpow_sum_normSq_shortSmoothDiff hX y x H s zero_le_one
    simp only [Real.rpow_one] at h
    exact h
  have hsum : (∫ ω, ∑ m ∈ s,
      ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2 ∂μ)
      ≤ ∑ m ∈ s, (smoothCount y ((x + H) / m) : ℝ) := by
    rw [integral_finsetSum _ fun m _ => ?_]
    · exact Finset.sum_le_sum fun m _ => integral_normSq_shortSmoothDiff_le hX y hH m
    · have h := integrable_rpow_sum_normSq_shortSmoothDiff hX y x H {m} zero_le_one
      simp only [Real.rpow_one, Finset.sum_singleton] at h
      exact h
  have hnn : ∀ᵐ ω ∂μ, (∑ m ∈ s,
      ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2)
        ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (hV0 ω)
  have hmul : ∑ m ∈ s, (smoothCount y ((x + H) / m) : ℝ)
      = (x + H) * ∑ m ∈ s, (smoothCount y ((x + H) / m) : ℝ) / (x + H) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => (mul_div_cancel₀ _ hxH.ne').symm
  calc ∫ ω, (∑ m ∈ s,
        ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2) ^ q ∂μ
      ≤ (∫ ω, ∑ m ∈ s,
          ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2 ∂μ)
          ^ q :=
        integral_rpow_le_rpow_integral hq0 hq1 hnn hint1
          (integrable_rpow_sum_normSq_shortSmoothDiff hX y x H s hq0)
    _ ≤ (∑ m ∈ s, (smoothCount y ((x + H) / m) : ℝ)) ^ q :=
        Real.rpow_le_rpow (integral_nonneg hV0) hsum hq0
    _ ≤ ((x + H) * (CR * Real.log y ^ A * Real.exp (-cR * Real.log (x + H) / Real.log y)
          * (1 + (N : ℝ) ^ (cR / Real.log y) / (cR / Real.log y)))) ^ q := by
        refine Real.rpow_le_rpow (Finset.sum_nonneg fun m _ => Nat.cast_nonneg _) ?_ hq0
        rw [hmul]
        exact mul_le_mul_of_nonneg_left
          (sum_smoothCount_div_le hR hCR hy hxH hsub hsm' hβ0 hβ1) hxH.le

omit [MeasurableSpace Ω] in
/-- **The top range, pathwise.**  For `x < m` and `H ≤ x`, both `x/m` and `(x+H)/m − x/m` are
below one, so each short difference has at most two terms. -/
lemma sum_normSq_shortSmoothDiff_top_le {f : Ω → ArithmeticFunction ℂ} {y : ℕ} {ω : Ω}
    (hf : ∀ n, ‖f ω n‖ ≤ 1) {x H : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) (hHx : H ≤ x) :
    ∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m}, ‖shortSmoothDiff f y x H ω m‖ ^ 2
      ≤ 4 * (({m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m}.card : ℕ) : ℝ) := by
  have hterm : ∀ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m},
      ‖shortSmoothDiff f y x H ω m‖ ^ 2 ≤ 4 := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    have hmx : x < m := by
      have h1 := Nat.lt_floor_add_one x
      have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast hm.1.1
      linarith
    have hmR : (0 : ℝ) < m := lt_of_le_of_lt hx hmx
    have hle : x / m ≤ (x + H) / m := div_le_div_of_nonneg_right (by linarith) hmR.le
    have hlt : (x + H) / m < x / m + 2 := by
      have hHm : H / m < 2 := by
        rw [div_lt_iff₀ hmR]
        linarith
      rw [add_div]
      linarith
    have h2 := norm_smoothPartial_sub_le_two (y := y) hf (div_nonneg hx hmR.le) hle hlt
    rw [shortSmoothDiff]
    calc ‖smoothPartial f y ((x + H) / m) ω - smoothPartial f y (x / m) ω‖ ^ 2
        ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = 4 := by norm_num
  calc ∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m}, ‖shortSmoothDiff f y x H ω m‖ ^ 2
      ≤ ∑ _m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m}, (4 : ℝ) := Finset.sum_le_sum hterm
    _ = 4 * (({m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m}.card : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The rough `m ≤ x + H`, split at `N` and at `x`. -/
lemma sum_rough_Icc_eq_three {g : ℕ → ℝ} (y N : ℕ) {x H : ℝ} (hH : 0 ≤ H) :
    ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x + H⌋₊ | IsRough y m}, g m
      = ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N}, g m
        + ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N}, g m
        + ∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m}, g m := by
  have hxH : ⌊x⌋₊ ≤ ⌊x + H⌋₊ := Nat.floor_le_floor (by linarith)
  have hsplit : {m ∈ Finset.Icc 1 ⌊x + H⌋₊ | IsRough y m}
      = {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m}
        ∪ {m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m} := by
    rw [← Finset.filter_union]
    congr 1
    rw [show Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ from rfl,
      show Finset.Icc 1 ⌊x + H⌋₊ = Finset.Ioc 0 ⌊x + H⌋₊ from rfl]
    exact (Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hxH).symm
  have hdisj : Disjoint {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m}
      {m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m} := by
    refine Finset.disjoint_filter_filter (Finset.disjoint_left.2 fun n hn hn' => ?_)
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_Ioc] at hn'
    omega
  have hN := Finset.sum_filter_add_sum_filter_not
    ({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m}) (fun m => m ≤ N) g
  rw [Finset.filter_filter, Finset.filter_filter] at hN
  rw [hsplit, Finset.sum_union hdisj, ← hN]

/-- Subadditivity of `t ↦ t^q`, three terms. -/
lemma rpow_add_add_le_add_add_rpow {a b c q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : (a + b + c) ^ q ≤ a ^ q + b ^ q + c ^ q :=
  (Real.rpow_add_le_add_rpow (add_nonneg ha hb) hc hq0 hq1).trans
    (add_le_add (Real.rpow_add_le_add_rpow ha hb hq0 hq1) le_rfl)

/-! ### The dilated line integral

The right-hand side of the dilated Parseval identity, `∫_ℝ |l^s − 1|²|F(s)/s|² dt` on
`s = ½ + it`.  For the squarefree product it is measurable in `ω` and bounded on the paths with
`|X_p| ≤ 1`, so all its moments are finite. -/

/-- `∫_ℝ |l^s − 1|² |F(s)/s|² dt`, `s = ½ + it`, `F` the Euler product over the primes below
`N`. -/
noncomputable def dilatedLineIntegral (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (l : ℝ) (ω : Ω) :
    ℝ :=
  ∫ t : ℝ, ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2
    * lineDivSqOf (1 / 2) F N ω t

omit [MeasurableSpace Ω] in
lemma dilatedLineIntegral_nonneg (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (l : ℝ) (ω : Ω) :
    0 ≤ dilatedLineIntegral F N l ω :=
  integral_nonneg fun t => mul_nonneg (sq_nonneg _) (by rw [lineDivSqOf]; positivity)

/-- **The dilated line integral is measurable in `ω`**, Rademacher case: the weight is continuous
in `t`, and the rest is `RMF.measurable_lineDivSqOf_sqfree_uncurry`. -/
lemma measurable_dilatedLineIntegral_sqfree {X : ℕ → Ω → ℂ} {N : ℕ}
    (hX : ∀ p ∈ Nat.primesBelow N, Measurable (X p)) {l : ℝ} (hl : 0 < l) :
    Measurable fun ω =>
      dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) N l ω := by
  have hj := measurable_lineDivSqOf_sqfree_uncurry (X := X) N (1 / 2) hX
  have hl0 : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl.ne'
  have hcp : Continuous fun t : ℝ => (l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) :=
    Continuous.const_cpow (by fun_prop) (Or.inl hl0)
  have hw : Continuous fun t : ℝ => ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2 :=
    (hcp.sub continuous_const).norm.pow 2
  have hprod : Measurable fun z : Ω × ℝ =>
      ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (z.2 : ℂ) * Complex.I) - 1‖ ^ 2
        * lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N z.1 z.2 :=
    (hw.measurable.comp measurable_snd).mul hj
  have hint : Measurable fun ω : Ω => ∫ t : ℝ,
      ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2
        * lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N ω t :=
    (MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure ℝ)) hprod.stronglyMeasurable).measurable
  exact hint

omit [MeasurableSpace Ω] in
/-- **The dilated line integral is bounded** on the paths with `|X_p| ≤ 1`: the weight is at most
`7` for `1 ≤ l ≤ 2` (`RMF.normSq_cpow_half_sub_one_le_seven`), and the rest is
`RMF.integral_lineDivSqOf_sqfree_le`. -/
lemma dilatedLineIntegral_sqfree_le {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω}
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) {l : ℝ} (hl1 : 1 ≤ l) (hl2 : l ≤ 2) :
    dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) N l ω
      ≤ 7 * (8 * eulerBound N ^ 2 * ∑' n : ℤ, shiftWeight 1 n) := by
  have hL0 : ∀ t : ℝ,
      0 ≤ lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N ω t := fun t => by
    rw [lineDivSqOf]
    positivity
  have hint := integrable_lineDivSqOf (σ := 1 / 2) (by norm_num)
    (measurable_randomEulerProduct_sqfree_line (X := X) (N := N) (ω := ω) (1 / 2))
    (fun t => norm_randomEulerProduct_sqfree_le hω (by norm_num))
  calc dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) N l ω
      ≤ ∫ t : ℝ,
          7 * lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N ω t := by
        rw [dilatedLineIntegral]
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun t => mul_nonneg (sq_nonneg _) (hL0 t))
          (hint.const_mul 7) (Filter.Eventually.of_forall fun t => ?_)
        exact mul_le_mul_of_nonneg_right (normSq_cpow_half_sub_one_le_seven hl1 hl2 t) (hL0 t)
    _ = 7 * ∫ t : ℝ, lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N ω t :=
        integral_const_mul _ _
    _ ≤ 7 * (8 * eulerBound N ^ 2 * ∑' n : ℤ, shiftWeight 1 n) :=
        mul_le_mul_of_nonneg_left (integral_lineDivSqOf_sqfree_le (by norm_num) hω)
          (by norm_num)

/-- **`(dilatedLineIntegral)^q` is integrable**, Rademacher case, for `1 ≤ l ≤ 2`. -/
theorem integrable_dilatedLineIntegral_rpow_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (N : ℕ) {l q : ℝ} (hl1 : 1 ≤ l) (hl2 : l ≤ 2)
    (hq : 0 ≤ q) :
    Integrable (fun ω =>
      dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) N l ω ^ q) μ := by
  haveI := hX.isProbabilityMeasure
  have hae := ae_forall_norm_le_one hX norm_le_one_rademacherLaw N
  have hm : Measurable fun ω =>
      dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) N l ω :=
    measurable_dilatedLineIntegral_sqfree
      (fun p hp => hX.measurable p (Nat.prime_of_mem_primesBelow hp)) (by linarith)
  refine (memLp_top_of_bound (hm.pow_const q).aestronglyMeasurable
    ((7 * (8 * eulerBound N ^ 2 * ∑' n : ℤ, shiftWeight 1 n)) ^ q) ?_).integrable le_top
  filter_upwards [hae] with ω hω
  have hnn := dilatedLineIntegral_nonneg (fun ω => squarefreeExtension fun p => X p ω) N l ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnn q)]
  exact Real.rpow_le_rpow hnn (dilatedLineIntegral_sqfree_le hω hl1 hl2) hq

/-- **The dilated Parseval identity for the smooth partial sums**, Rademacher case.  Almost surely
the integrand is integrable and
`∫_0^∞ |A(lu) − A(u)|² u^{−2} du = (2π)^{−1} ∫_ℝ |l^s − 1|² |F(s)/s|² dt`,   `s = ½ + it`,
`F` the Euler product over `p ≤ y`: `RMF.integral_normSq_dilatedPartialSum_eq_line_half` at the
smooth coefficients, whose Dirichlet series is `F` (`RMF.dirichletSeries_smoothCoeff_eq_sqfree`). -/
theorem integral_normSq_dilated_smoothPartial_eq_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {l : ℝ} (hl : 0 < l) :
    ∀ᵐ ω ∂μ, IntegrableOn (fun u : ℝ =>
        ‖smoothPartial (fun ω => squarefreeExtension fun p => X p ω) y (l * u) ω
          - smoothPartial (fun ω => squarefreeExtension fun p => X p ω) y u ω‖ ^ 2 / u ^ 2)
        (Set.Ioi (0 : ℝ))
      ∧ (∫ u in Set.Ioi (0 : ℝ),
          ‖smoothPartial (fun ω => squarefreeExtension fun p => X p ω) y (l * u) ω
            - smoothPartial (fun ω => squarefreeExtension fun p => X p ω) y u ω‖ ^ 2 / u ^ 2)
        = (2 * Real.pi)⁻¹
          * dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) (y + 1) l ω := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  filter_upwards [summable_norm_smoothCoeff_div_sqrt hRa.isBoundedRMF y] with ω hω
  refine ⟨?_, ?_⟩
  · simpa only [sum_smoothCoeff] using integrableOn_normSq_dilatedPartialSum_half _ hω hl
  · have h := integral_normSq_dilatedPartialSum_eq_line_half _ hω hl
    simp only [sum_smoothCoeff] at h
    rw [h, dilatedLineIntegral]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    have hc : (((1 / 2 : ℝ)) : ℂ) = 1 / 2 := by norm_num
    rw [lineDivSqOf, hc, ← dirichletSeries_smoothCoeff_eq_sqfree y ω, dirichletSeries,
      mul_div_assoc, norm_mul, mul_pow]

/-- **The middle range, in expectation.**  The pathwise fibre bound
`RMF.sum_normSq_shortSmoothDiff_large_le`, the dilated Parseval identity, and subadditivity:

`E[(∑_m |A((x+H)/m) − A(x/m)|²)^q] ≤ (C_s x/log y)^q (4^q E[I^q] + 16^q)`,

`I = (2π)^{−1}·RMF.dilatedLineIntegral` at `λ = (x+H)/x`. -/
theorem integral_rpow_sum_shortSmoothDiff_large_le {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hS : ∀ (y : ℕ) (x H : ℝ), 2 ≤ y → 0 < x → 0 < H → (y : ℝ) ≤ H →
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ H →
      (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ) ≤ Cs * H / Real.log y)
    {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {y : ℕ} (hy : 2 ≤ y) {x H q : ℝ} (hx : 0 < x) (hH : 0 ≤ H) (hHx : H ≤ x)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {R : ℕ} {s : Finset ℕ} (hs0 : ∀ m ∈ s, 0 < m)
    (hmaps : ∀ m ∈ s, ⌊x / (m : ℝ)⌋₊ ∈ Finset.Icc 1 R)
    (hsieveOK : ∀ r ∈ Finset.Icc 1 R, 2 ≤ x / ((r : ℝ) + 1) ∧
      2 ≤ x / r - x / ((r : ℝ) + 1) ∧ (y : ℝ) ≤ x / r - x / ((r : ℝ) + 1) ∧
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ x / r - x / ((r : ℝ) + 1))
    (hfib : ∀ r ∈ Finset.Icc 1 R,
      s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)
        ⊆ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r}) :
    ∫ ω, (∑ m ∈ s,
        ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2) ^ q ∂μ
      ≤ (Cs * x / Real.log y) ^ q
        * (4 ^ q * ∫ ω, ((2 * Real.pi)⁻¹ * dilatedLineIntegral
            (fun ω => squarefreeExtension fun p => X p ω) (y + 1) ((x + H) / x) ω) ^ q ∂μ
          + 16 ^ q) := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hc0 : 0 ≤ Cs * x / Real.log y := div_nonneg (mul_nonneg hCs hx.le) hL.le
  have hl0 : 0 < (x + H) / x := div_pos (by linarith) hx
  have hl1 : 1 ≤ (x + H) / x := by rw [le_div_iff₀ hx]; linarith
  have hl2 : (x + H) / x ≤ 2 := by rw [div_le_iff₀ hx]; linarith
  have hpi : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := inv_nonneg.2 (by positivity)
  set J : Ω → ℝ := fun ω => (2 * Real.pi)⁻¹ * dilatedLineIntegral
    (fun ω => squarefreeExtension fun p => X p ω) (y + 1) ((x + H) / x) ω with hJdef
  have hJ0 : ∀ ω, 0 ≤ J ω := fun ω => mul_nonneg hpi (dilatedLineIntegral_nonneg _ _ _ _)
  have hJq : Integrable (fun ω => J ω ^ q) μ := by
    refine ((integrable_dilatedLineIntegral_rpow_sqfree hX (y + 1) hl1 hl2 hq0).const_mul
      ((2 * Real.pi)⁻¹ ^ q)).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hJdef]
    rw [Real.mul_rpow hpi (dilatedLineIntegral_nonneg _ _ _ _)]
  have hall : ∀ᵐ ω ∂μ, ∀ n : ℕ, ‖squarefreeExtension (fun p => X p ω) n‖ ≤ 1 := by
    rw [ae_all_iff]
    exact hRa.norm_apply_le_one
  have hbd : ∀ᵐ ω ∂μ, (∑ m ∈ s,
        ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2) ^ q
      ≤ (Cs * x / Real.log y) ^ q * (4 ^ q * J ω ^ q + 16 ^ q) := by
    filter_upwards [hall, integral_normSq_dilated_smoothPartial_eq_sqfree hX y hl0]
      with ω hω hP
    have hpath := sum_normSq_shortSmoothDiff_large_le hCs hS hy hx hH hHx hs0 hmaps hsieveOK
      hfib (f := fun ω => squarefreeExtension fun p => X p ω) (ω := ω) hω hP.1
    rw [hP.2] at hpath
    have hV0 : 0 ≤ ∑ m ∈ s,
        ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2 :=
      Finset.sum_nonneg fun m _ => sq_nonneg _
    have h4J : 0 ≤ 4 * J ω := by linarith [hJ0 ω]
    calc (∑ m ∈ s,
          ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2) ^ q
        ≤ (Cs * x / Real.log y * (4 * J ω + 16)) ^ q := Real.rpow_le_rpow hV0 hpath hq0
      _ = (Cs * x / Real.log y) ^ q * (4 * J ω + 16) ^ q :=
          Real.mul_rpow hc0 (by linarith)
      _ ≤ (Cs * x / Real.log y) ^ q * ((4 * J ω) ^ q + 16 ^ q) :=
          mul_le_mul_of_nonneg_left (Real.rpow_add_le_add_rpow h4J (by norm_num) hq0 hq1)
            (Real.rpow_nonneg hc0 _)
      _ = (Cs * x / Real.log y) ^ q * (4 ^ q * J ω ^ q + 16 ^ q) := by
          rw [Real.mul_rpow (by norm_num) (hJ0 ω)]
  have hint : Integrable (fun ω => (Cs * x / Real.log y) ^ q * (4 ^ q * J ω ^ q + 16 ^ q)) μ :=
    ((hJq.const_mul (4 ^ q)).add (integrable_const _)).const_mul _
  calc ∫ ω, (∑ m ∈ s,
        ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2) ^ q ∂μ
      ≤ ∫ ω, (Cs * x / Real.log y) ^ q * (4 ^ q * J ω ^ q + 16 ^ q) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
          Real.rpow_nonneg (Finset.sum_nonneg fun m _ => sq_nonneg _) q) hint hbd
    _ = (Cs * x / Real.log y) ^ q * (4 ^ q * ∫ ω, J ω ^ q ∂μ + 16 ^ q) := by
        have hJq4 : Integrable (fun ω => 4 ^ q * J ω ^ q) μ := hJq.const_mul _
        rw [integral_const_mul, integral_add hJq4 (integrable_const _), integral_const_mul,
          integral_const, probReal_univ, one_smul]

/-- **The three ranges, integrated**: `RMF.sum_rough_Icc_eq_three` and subadditivity of `t ↦ t^q`
under the integral. -/
lemma integral_rpow_sum_rough_le_three {μ : Measure Ω} {g : Ω → ℕ → ℝ} (hg : ∀ ω m, 0 ≤ g ω m)
    (y N : ℕ) {x H q : ℝ} (hH : 0 ≤ H) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hint : ∀ s : Finset ℕ, Integrable (fun ω => (∑ m ∈ s, g ω m) ^ q) μ) :
    ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x + H⌋₊ | IsRough y m}, g ω m) ^ q ∂μ
      ≤ (∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N}, g ω m) ^ q ∂μ)
        + (∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N}, g ω m) ^ q ∂μ)
        + ∫ ω, (∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m}, g ω m) ^ q ∂μ := by
  have h12 : Integrable (fun ω =>
      (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N}, g ω m) ^ q
        + (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N}, g ω m) ^ q) μ :=
    (hint _).add (hint _)
  have h123 : Integrable (fun ω =>
      (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N}, g ω m) ^ q
        + (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N}, g ω m) ^ q
        + (∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m}, g ω m) ^ q) μ :=
    h12.add (hint _)
  have hpt : ∀ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x + H⌋₊ | IsRough y m}, g ω m) ^ q
      ≤ (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N}, g ω m) ^ q
        + (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N}, g ω m) ^ q
        + (∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m}, g ω m) ^ q := by
    intro ω
    rw [sum_rough_Icc_eq_three y N hH]
    exact rpow_add_add_le_add_add_rpow (Finset.sum_nonneg fun m _ => hg ω m)
      (Finset.sum_nonneg fun m _ => hg ω m) (Finset.sum_nonneg fun m _ => hg ω m) hq0 hq1
  rw [← integral_add (hint _) (hint _), ← integral_add h12 (hint _)]
  exact integral_mono (hint _) h123 hpt

/-- **The short-interval reduction, Rademacher case.**  For `y ≥ 4` and `0 ≤ q ≤ 1`, given the
Rankin and sieve inputs `hR`, `hS` (met by `RMF.exists_smoothCount_le` and
`RMF.exists_roughCount_sub_le`), for `0 < H ≤ x` with the sieve condition at `√x/2` and at `H`,
`N = ⌊x^{3/4}⌋` and `I = (2π)^{−1}·RMF.dilatedLineIntegral` at `λ = (x+H)/x` over `p ≤ y`:
`E|∑_{x<n≤x+H} f(n)|^{2q} ≤ ((x+H)·Rankin)^q + (C_s x/log y)^q (4^q E[I^q] + 16^q)
  + (4C_s H/log y)^q`, the terms coming from the rough `m ≤ N`, `N < m ≤ x` and `x < m`. -/
theorem integral_rpow_shortSum_le_sqfree {A cR CR Cs : ℝ}
    (hR : ∀ (y : ℕ) (x : ℝ), 2 ≤ y → 2 ≤ x →
      (smoothCount y x : ℝ)
        ≤ CR * x * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y))
    (hCR : 0 ≤ CR)
    (hS : ∀ (y : ℕ) (x H : ℝ), 2 ≤ y → 0 < x → 0 < H → (y : ℝ) ≤ H →
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ H →
      (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ) ≤ Cs * H / Real.log y)
    (hCs : 0 ≤ Cs) {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {y : ℕ} (hy : 4 ≤ y) {x H q : ℝ} (hH : 0 < H) (hHx : H ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (habs : 5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ Real.sqrt x / 2)
    (habsH : 5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ H)
    (hβ0 : 0 < cR / Real.log y) (hβ1 : cR / Real.log y ≤ 1) :
    ∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, squarefreeExtension (fun p => X p ω) n‖ ^ (2 * q) ∂μ
      ≤ ((x + H) * (CR * Real.log y ^ A * Real.exp (-cR * Real.log (x + H) / Real.log y)
            * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (cR / Real.log y) / (cR / Real.log y)))) ^ q
        + (Cs * x / Real.log y) ^ q
          * (4 ^ q * ∫ ω, ((2 * Real.pi)⁻¹ * dilatedLineIntegral
              (fun ω => squarefreeExtension fun p => X p ω) (y + 1) ((x + H) / x) ω) ^ q ∂μ
            + 16 ^ q)
        + (4 * (Cs * H / Real.log y)) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  -- the regime, as in `RMF.reduction_upper_of_core`
  have hyR : (4 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hy2N : 2 ≤ y := by omega
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by linarith
  have hexp1 : Real.exp 1 ≤ (y : ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  have hLy1 : (1 : ℝ) ≤ Real.log y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) hexp1
  have hcube : (8 : ℝ) ≤ (1 + Real.log y) ^ 3 * Real.log y := by
    have h2 : (2 : ℝ) ≤ 1 + Real.log y := by linarith
    have h := mul_le_mul (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 3) hLy1
      (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ (1 + Real.log y) ^ 3)
    norm_num at h
    linarith
  have h40 := mul_le_mul_of_nonneg_left hcube (show (0 : ℝ) ≤ 5 * (y : ℝ) by linarith)
  have hyx : 2 * (y : ℝ) ≤ Real.sqrt x := by linarith [habs, h40]
  have hyH : (y : ℝ) ≤ H := by linarith [habsH, h40]
  have hx64 : (64 : ℝ) ≤ x := by
    have h8 : (8 : ℝ) ≤ Real.sqrt x := by linarith
    have hx0 : (0 : ℝ) ≤ x := by
      by_contra hneg
      push Not at hneg
      rw [Real.sqrt_eq_zero_of_nonpos hneg.le] at h8
      linarith
    calc (64 : ℝ) = 8 ^ 2 := by norm_num
      _ ≤ Real.sqrt x ^ 2 := pow_le_pow_left₀ (by norm_num) h8 2
      _ = x := Real.sq_sqrt hx0
  have hx16 : (16 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hall : ∀ᵐ ω ∂μ, ∀ n : ℕ, ‖squarefreeExtension (fun p => X p ω) n‖ ≤ 1 := by
    rw [ae_all_iff]
    exact hRa.norm_apply_le_one
  have hcard : (({m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m}.card : ℕ) : ℝ)
      ≤ Cs * H / Real.log y := by
    rw [← roughCount_sub_eq_card hH.le]
    exact hS y x H hy2N hx0 hH hyH habsH
  -- conditional Jensen, then the three ranges
  have h1 := integral_rpow_shortSum_le_rough hX y hx0.le hH.le hq0 hq1
  have h2 := integral_rpow_sum_rough_le_three (μ := μ) (x := x)
    (g := fun ω m =>
      ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2)
    (fun ω m => sq_nonneg _) y ⌊x ^ (3 / 4 : ℝ)⌋₊ hH.le hq0 hq1
    (fun s => integrable_rpow_sum_normSq_shortSmoothDiff hX y x H s hq0)
  refine (h1.trans h2).trans (add_le_add (add_le_add ?_ ?_) ?_)
  · exact integral_rpow_sum_shortSmoothDiff_small_le hR hCR hX hy2N hx0 hH.le hq0 hq1
      (by
        intro m hm
        rw [Finset.mem_filter, Finset.mem_Icc] at hm
        rw [Finset.mem_Icc]
        exact ⟨hm.1.1, hm.2.2⟩)
      (fun m hm =>
        ⟨(rough_mem_facts (P := fun m => IsRough y m ∧ m ≤ ⌊x ^ (3 / 4 : ℝ)⌋₊) hx1 hm).1,
          two_le_div_of_le_split hx16
            (rough_mem_facts (P := fun m => IsRough y m ∧ m ≤ ⌊x ^ (3 / 4 : ℝ)⌋₊) hx1 hm).1
            (by rw [Finset.mem_filter] at hm; exact hm.2.2)⟩)
      hβ0 hβ1
  · exact integral_rpow_sum_shortSmoothDiff_large_le hCs hS hX hy2N hx0 hH.le hHx hq0 hq1
      (R := ⌊x ^ (1 / 4 : ℝ)⌋₊)
      (fun m hm =>
        (rough_mem_facts (P := fun m => IsRough y m ∧ ¬ m ≤ ⌊x ^ (3 / 4 : ℝ)⌋₊) hx1 hm).1)
      (fun m hm => floor_div_mem_of_split hx16
        (rough_mem_facts (P := fun m => IsRough y m ∧ ¬ m ≤ ⌊x ^ (3 / 4 : ℝ)⌋₊) hx1 hm).1
        (rough_mem_facts (P := fun m => IsRough y m ∧ ¬ m ≤ ⌊x ^ (3 / 4 : ℝ)⌋₊) hx1 hm).2
        (by rw [Finset.mem_filter] at hm; exact hm.2.2))
      (fun r hr => by
        rw [Finset.mem_Icc] at hr
        exact sieve_conditions hx64 hy2 hyx habs hr.1
          (le_trans (by exact_mod_cast hr.2)
            (Nat.floor_le (Real.rpow_pos_of_pos (by linarith) _).le)))
      (fun r _ m hm => by
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hm
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hm.1.1.1, hm.1.1.2⟩, hm.1.2.1, hm.2⟩)
  · have hbd : ∀ᵐ ω ∂μ, (∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m},
          ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2) ^ q
        ≤ (4 * (Cs * H / Real.log y)) ^ q := by
      filter_upwards [hall] with ω hω
      refine Real.rpow_le_rpow (Finset.sum_nonneg fun m _ => sq_nonneg _) ?_ hq0
      refine (sum_normSq_shortSmoothDiff_top_le
        (f := fun ω => squarefreeExtension fun p => X p ω) (ω := ω) hω hx0.le hH.le hHx).trans ?_
      linarith
    calc ∫ ω, (∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y m},
          ‖shortSmoothDiff (fun ω => squarefreeExtension fun p => X p ω) y x H ω m‖ ^ 2) ^ q ∂μ
        ≤ ∫ _ω, (4 * (Cs * H / Real.log y)) ^ q ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
            Real.rpow_nonneg (Finset.sum_nonneg fun m _ => sq_nonneg _) q)
            (integrable_const _) hbd
      _ = (4 * (Cs * H / Real.log y)) ^ q := by rw [integral_const, probReal_univ, one_smul]

end RMF
