/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Function.Floor
import RMF.Probability.CondJensen
import RMF.Reduction.Suppliers
import RMF.SecondMoment

/-!
# The reduction, step by step

Gorodetsky–Wong's Section 2, in their order.  The arithmetic and analytic inputs are the
theorems of `RMF/Reduction/Suppliers.lean`; everything here is assembly.

The normalised sum is bounded — `‖S_x‖ ≤ x` — because every value has modulus one and there are
at most `⌊x⌋` of them.  That single fact discharges every integrability side condition below, so
it comes first.
-/

open MeasureTheory Filter Set
open scoped Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Boundedness of the normalised sum -/

omit [MeasurableSpace Ω] in
lemma randomSum_eq_partialSum (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) :
    randomSum f x ω = partialSum f ⌊x⌋₊ ω := rfl

lemma one_le_sqrt_of_one_le {x : ℝ} (hx : 1 ≤ x) : (1 : ℝ) ≤ Real.sqrt x := by
  nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ x), Real.sqrt_nonneg x]

lemma measurable_normalisedSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) (x : ℝ) : Measurable fun ω => normalisedSum f x ω :=
  (Finset.measurable_sum _ fun n _ => hf.measurable_apply n).div_const _

/-- `‖S_x‖ ≤ x` for `x ≥ 1`.  Crude — its `L²` norm is at most `1` — but it holds uniformly in
`ω`, which is all the integrability arguments need. -/
lemma norm_normalisedSum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) {x : ℝ} (hx : 1 ≤ x) :
    ∀ᵐ ω ∂μ, ‖normalisedSum f x ω‖ ≤ x := by
  have hbdd : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 := by
    intro n hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.1 hn).1
      omega
    filter_upwards [hf.norm_apply hn0] with ω hω
    exact hω.le
  have hsx : (1 : ℝ) ≤ Real.sqrt x := one_le_sqrt_of_one_le hx
  filter_upwards [norm_partialSum_le hbdd] with ω hω
  have hnorm : ‖normalisedSum f x ω‖ = ‖partialSum f ⌊x⌋₊ ω‖ / Real.sqrt x := by
    rw [normalisedSum, randomSum_eq_partialSum, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg x)]
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  rw [hnorm, div_le_iff₀ (by linarith : (0 : ℝ) < Real.sqrt x)]
  nlinarith

/-! ### Step (a): conditioning on the smooth part -/

/-- **Step (a)** (Gorodetsky–Wong (2.3) then (2.5)).  For `0 ≤ q ≤ 1`,
`E|S_x|^{2q} ≤ E[(∑_{m ≤ x, m rough} m⁻¹ |S_{x/m,y}|²)^q]`: conditional Jensen for the concave
`t ↦ t^q` moves the expectation inside, and the conditional second moment is an exact sum over
rough `m`.  Both `q ≤ 1` steps of the reduction (this one and the later subadditivity) carry
constant `1`, which is why the argument is uniform in `q`. -/
theorem integral_rpow_le_integral_rough_sum {f : Ω → ArithmeticFunction ℂ} {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hX : IsSteinhausPrimeValues X μ)
    (hf : f = fun ω => compMultExtension fun p => X p ω) {y : ℕ}
    {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
          (m : ℝ)⁻¹ * ‖smoothSum f y (x / m) ω‖ ^ 2) ^ q ∂μ := by
  have hrmf : IsSteinhausRMF f μ := isSteinhausRMF_iff_exists.2 ⟨X, hX, hf⟩
  have hle := smoothAlgebra_le hX y
  haveI : SigmaFinite (μ.trim hle) := (isFiniteMeasure_trim hle).toSigmaFinite
  refine le_trans (integral_rpow_norm_le_integral_condExp_rpow hle
    (measurable_normalisedSum hrmf x) (norm_normalisedSum_le hrmf hx) hq0 hq1) (le_of_eq ?_)
  refine integral_congr_ae ?_
  filter_upwards [condExp_normSq_normalisedSum hX hf (y := y) hx] with ω hω
  rw [hω]

/-! ### Step (d): the smooth block -/

/-- **Step (d)** (Gorodetsky–Wong, the `m = 1` term).  The smooth block has second moment
exactly the smooth count: `E|S_{t,y}|² = Ψ(t,y)/t`.

An identity, not an estimate — the estimation happens when Rankin is applied to `Ψ`. -/
theorem integral_normSq_smoothSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsSteinhausRMF f μ) (y : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ ω, ‖smoothSum f y t ω‖ ^ 2 ∂μ) = (smoothCount y t : ℝ) / t := by
  have hs : ∀ n ∈ {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, n ≠ 0 := by
    intro n hn
    have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
    omega
  have hnorm : ∀ ω : Ω, ‖smoothSum f y t ω‖ ^ 2
      = ‖∑ n ∈ {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, f ω n‖ ^ 2 / t := by
    intro ω
    rw [smoothSum, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg t), div_pow, Real.sq_sqrt ht.le]
  simp_rw [hnorm]
  rw [integral_div, integral_normSq_sum_of_orthogonality hf hs, smoothCount]

/-! ### Step (c): splitting the rough sum at `T` -/

/-- The summand of the rough sum, `m⁻¹ |S_{x/m,y}|²`. -/
noncomputable def roughTerm (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (x : ℝ) (ω : Ω) (m : ℕ) :
    ℝ := (m : ℝ)⁻¹ * ‖smoothSum f y (x / m) ω‖ ^ 2

omit [MeasurableSpace Ω] in
lemma roughTerm_nonneg (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (x : ℝ) (ω : Ω) (m : ℕ) :
    0 ≤ roughTerm f y x ω m := by
  rw [roughTerm]
  positivity

omit [MeasurableSpace Ω] in
/-- **Step (c)** (Gorodetsky–Wong, the split at `T`).  Subadditivity of `t ↦ t^q` for `q ≤ 1`
separates the two ranges of `m` at no cost — the constant is `1`.

Smoothing the outer sum into an integral only pays when `m` is large, which is why the split
is made; Gorodetsky–Wong take `T = x^{3/4}`, and that choice is what forces `y ≤ √x`. -/
lemma rpow_rough_sum_le_add {f : Ω → ArithmeticFunction ℂ} {y : ℕ} {x q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (ω : Ω) :
    (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m}, roughTerm f y x ω m) ^ q
      ≤ (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N}, roughTerm f y x ω m) ^ q
        + (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N}, roughTerm f y x ω m) ^ q := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m}) (fun m => m ≤ N) (roughTerm f y x ω)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have hnn1 : 0 ≤ ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N}, roughTerm f y x ω m :=
    Finset.sum_nonneg fun m _ => roughTerm_nonneg _ _ _ _ _
  have hnn2 : 0 ≤ ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
      roughTerm f y x ω m :=
    Finset.sum_nonneg fun m _ => roughTerm_nonneg _ _ _ _ _
  rw [← hsplit]
  exact Real.rpow_add_le_add_rpow hnn1 hnn2 hq0 hq1

/-! ### Step (e1): the small range, as a smooth count

`E[∑_{m ≤ N, rough} m⁻¹ |S_{x/m,y}|²] = ∑_{m ≤ N, rough} Ψ(x/m, y)/x`.

Exact, by step (d) termwise: the `m⁻¹` cancels against the `x/m` in the denominator of
`Ψ(x/m,y)/(x/m)`, leaving `Ψ(x/m,y)/x`.  Rankin enters only at the next step. -/

lemma measurable_smoothSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (y : ℕ) (t : ℝ) : Measurable fun ω => smoothSum f y t ω :=
  (Finset.measurable_sum _ fun n _ => hf.measurable_apply n).div_const _

/-- `‖S_{t,y}‖ ≤ t` for `t ≥ 1`, by the same crude count as for `S_x`: at most `⌊t⌋` values, each
of modulus one, divided by `√t`. -/
lemma norm_smoothSum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (y : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    ∀ᵐ ω ∂μ, ‖smoothSum f y t ω‖ ≤ t := by
  have hbdd : ∀ n ∈ Finset.Icc 1 ⌊t⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 :=
    fun n _ => hf.ae_norm_le_one n
  have hsx : (1 : ℝ) ≤ Real.sqrt t := one_le_sqrt_of_one_le ht
  filter_upwards [(Filter.eventually_all_finset (Finset.Icc 1 ⌊t⌋₊)).2 hbdd] with ω hω
  set s : Finset ℕ := {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)} with hs
  have hsub : s ⊆ Finset.Icc 1 ⌊t⌋₊ := Finset.filter_subset _ _
  have hcard : (s.card : ℝ) ≤ (⌊t⌋₊ : ℝ) := by
    have h : s.card ≤ ⌊t⌋₊ := by
      simpa [Nat.card_Icc] using Finset.card_le_card hsub
    exact_mod_cast h
  have hsum : ‖∑ n ∈ s, f ω n‖ ≤ (s.card : ℝ) := by
    calc ‖∑ n ∈ s, f ω n‖ ≤ ∑ n ∈ s, ‖f ω n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ s, (1 : ℝ) := Finset.sum_le_sum fun n hn => hω n (hsub hn)
      _ = (s.card : ℝ) := by simp
  have hnorm : ‖smoothSum f y t ω‖ = ‖∑ n ∈ s, f ω n‖ / Real.sqrt t := by
    rw [smoothSum, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg t)]
  have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  rw [hnorm, div_le_iff₀ (by linarith : (0 : ℝ) < Real.sqrt t)]
  nlinarith

lemma integrable_normSq_smoothSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hf : IsBoundedRMF f μ) (y : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    Integrable (fun ω => ‖smoothSum f y t ω‖ ^ 2) μ := by
  have hm0 : Measurable fun ω => ‖smoothSum f y t ω‖ := (measurable_smoothSum hf y t).norm
  have hms : Measurable fun ω => ‖smoothSum f y t ω‖ ^ 2 := by fun_prop
  have hb : ∀ᵐ ω ∂μ, ‖‖smoothSum f y t ω‖ ^ 2‖ ≤ t ^ 2 := by
    filter_upwards [norm_smoothSum_le hf y ht] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hω 2
  exact (memLp_top_of_bound hms.aestronglyMeasurable (t ^ 2) hb).integrable le_top

lemma integrable_roughTerm {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hf : IsBoundedRMF f μ) (y : ℕ) {x : ℝ} {m : ℕ}
    (ht : 1 ≤ x / m) : Integrable (fun ω => roughTerm f y x ω m) μ :=
  (integrable_normSq_smoothSum hf y ht).const_mul _

/-- **Step (e1).**  The expectation of a partial rough sum is a sum of smooth counts. -/
theorem integral_sum_roughTerm {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsSteinhausRMF f μ) (y : ℕ) {x : ℝ} (hx : 0 < x)
    {s : Finset ℕ} (hs : ∀ m ∈ s, 0 < m ∧ 1 ≤ x / m) :
    (∫ ω, ∑ m ∈ s, roughTerm f y x ω m ∂μ) = ∑ m ∈ s, (smoothCount y (x / m) : ℝ) / x := by
  rw [integral_finsetSum _ fun m hm => integrable_roughTerm hf.isBoundedRMF y (hs m hm).2]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm0, hmt⟩ := hs m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  simp_rw [roughTerm]
  rw [integral_const_mul, integral_normSq_smoothSum hf y (by linarith : (0 : ℝ) < x / m)]
  field_simp

/-! ### Step (e3): the geometric sum

`∑_{m ≤ N} m^{β-1} ≤ 1 + N^β/β` for `0 < β ≤ 1`.

This is Gorodetsky–Wong's `∫ e^{cv/log y} dv ≪ (log y) e^{c log T/log y}` in disguise: with
`β = c/log y`, the summand `m⁻¹ e^{c log m/log y}` *is* `m^{β-1}`, and `1/β = (log y)/c` is where
the extra factor `log y` in their `(log y)^{A+1}` comes from.

**`β ≤ 1` is needed and is a real constraint.**  For `β > 1` the summand is increasing and the
bound is false (at `β = 2`, `∑_{m≤N} m = N(N+1)/2` exceeds `1 + N²/2`).  In the application
`β = c/log y`, so it asks `log y ≥ c` with `c` Rankin's absolute constant — satisfied once `y` is
bounded below, and at `log y = log x/(log log x)²` that holds for all large `x`.  The reduction
therefore assumes `y ≥ y₀` (`RMF.reduction_upper_of_core`). -/
lemma sum_rpow_sub_one_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (β - 1) ≤ 1 + (N : ℝ) ^ β / β := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · norm_num [Real.zero_rpow hβ0.ne']
  have hanti : AntitoneOn (fun u : ℝ => u ^ (β - 1)) (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro u hu v hv huv
    have hu0 : (0 : ℝ) < u := by
      have h := hu.1
      norm_num at h
      linarith
    exact Real.rpow_le_rpow_of_nonpos hu0 huv (by linarith)
  have hsum := AntitoneOn.sum_le_integral_Ico (f := fun u : ℝ => u ^ (β - 1))
    (a := 1) (b := N) hN hanti
  have hint : ∫ u in (1 : ℝ)..(N : ℝ), u ^ (β - 1) = ((N : ℝ) ^ β - 1) / β := by
    rw [integral_rpow (Or.inl (by linarith))]
    norm_num
  have hshift : ∑ i ∈ Finset.Ico 1 N, ((i + 1 : ℕ) : ℝ) ^ (β - 1)
      = ∑ m ∈ Finset.Ico 2 (N + 1), (m : ℝ) ^ (β - 1) := by
    simpa using Finset.sum_Ico_add' (fun m : ℕ => ((m : ℝ)) ^ (β - 1)) 1 N 1
  have hbot : ∑ m ∈ Finset.Ico 1 (N + 1), (m : ℝ) ^ (β - 1)
      = 1 + ∑ m ∈ Finset.Ico 2 (N + 1), (m : ℝ) ^ (β - 1) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    norm_num
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext m
    simp
  rw [hIcc, hbot, ← hshift]
  have hle : ∑ i ∈ Finset.Ico 1 N, ((i + 1 : ℕ) : ℝ) ^ (β - 1) ≤ ((N : ℝ) ^ β - 1) / β := by
    calc ∑ i ∈ Finset.Ico 1 N, ((i + 1 : ℕ) : ℝ) ^ (β - 1)
        ≤ ∫ u in (1 : ℝ)..(N : ℝ), u ^ (β - 1) := by exact_mod_cast hsum
      _ = ((N : ℝ) ^ β - 1) / β := hint
  have hmono : ((N : ℝ) ^ β - 1) / β ≤ (N : ℝ) ^ β / β :=
    (div_le_div_iff_of_pos_right hβ0).2 (by linarith)
  linarith

/-! ### Step (e2): Rankin applied termwise -/

/-- `m⁻¹ e^{-c log(x/m)/L} = e^{-c log x/L} · m^{c/L - 1}`, the identity that turns
Gorodetsky–Wong's exponential sum into a power sum: `log(x/m) = log x - log m` splits the
exponential, and `e^{(c/L) log m}` is `m^{c/L}`.  This is why `RMF.sum_rpow_sub_one_le` is stated
for `m^{β-1}`: Gorodetsky–Wong's change of variables `v = log u` is already done. -/
lemma inv_mul_exp_neg_log_div {c L x : ℝ} (hx : 0 < x) (hL : 0 < L) {m : ℕ} (hm : 0 < m) :
    (m : ℝ)⁻¹ * Real.exp (-c * Real.log (x / m) / L)
      = Real.exp (-c * Real.log x / L) * (m : ℝ) ^ (c / L - 1) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsplit : -c * Real.log (x / m) / L
      = -c * Real.log x / L + Real.log m * (c / L) := by
    rw [Real.log_div hx.ne' hmR.ne']
    field_simp
    ring
  rw [hsplit, Real.exp_add, ← Real.rpow_def_of_pos hmR, Real.rpow_sub hmR, Real.rpow_one]
  field_simp

/-- **Step (e2).**  Rankin, divided through by `x`: the smooth count at `x/m` contributes
`≪ (log y)^A m⁻¹ e^{-c log(x/m)/log y}` to the mean of the rough sum. -/
lemma smoothCount_div_le {A c C : ℝ}
    (hR : ∀ (y : ℕ) (x : ℝ), 2 ≤ y → 2 ≤ x →
      (smoothCount y x : ℝ) ≤ C * x * Real.log y ^ A * Real.exp (-c * Real.log x / Real.log y))
    {y : ℕ} {x : ℝ} {m : ℕ} (hy : 2 ≤ y) (hm : 0 < m) (hxm : 2 ≤ x / m) :
    (smoothCount y (x / m) : ℝ) / x
      ≤ C * Real.log y ^ A * ((m : ℝ)⁻¹ * Real.exp (-c * Real.log (x / m) / Real.log y)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hx : (0 : ℝ) < x := by
    have h1 : (0 : ℝ) < x / m := by linarith
    have h2 : x = x / m * m := by field_simp
    rw [h2]
    exact mul_pos h1 hmR
  have h := hR y (x / m) hy hxm
  rw [div_le_iff₀ hx]
  calc (smoothCount y (x / m) : ℝ)
      ≤ C * (x / m) * Real.log y ^ A * Real.exp (-c * Real.log (x / m) / Real.log y) := h
    _ = C * Real.log y ^ A * ((m : ℝ)⁻¹ * Real.exp (-c * Real.log (x / m) / Real.log y)) * x := by
        field_simp

/-! ### Step (e4): the small range, assembled

`∑_{m ∈ s} Ψ(x/m,y)/x ≪ (log y)^A e^{-c log x/log y} (1 + N^β/β)`, `β = c/log y`.

Termwise Rankin (e2), the identity (e2's `inv_mul_exp_neg_log_div`) to pull the `x`-dependence
out of the exponential, and then the power sum (e3).  The factor `1/β = (log y)/c` is the extra
`log y` in Gorodetsky–Wong's `(log y)^{A+1}`. -/
theorem sum_smoothCount_div_le {A c C : ℝ}
    (hR : ∀ (y : ℕ) (x : ℝ), 2 ≤ y → 2 ≤ x →
      (smoothCount y x : ℝ) ≤ C * x * Real.log y ^ A * Real.exp (-c * Real.log x / Real.log y))
    (hC : 0 ≤ C) {y : ℕ} (hy : 2 ≤ y) {x : ℝ} (hx : 0 < x) {N : ℕ} {s : Finset ℕ}
    (hsub : s ⊆ Finset.Icc 1 N) (hsm : ∀ m ∈ s, 0 < m ∧ 2 ≤ x / m)
    (hβ0 : 0 < c / Real.log y) (hβ1 : c / Real.log y ≤ 1) :
    ∑ m ∈ s, (smoothCount y (x / m) : ℝ) / x
      ≤ C * Real.log y ^ A * Real.exp (-c * Real.log x / Real.log y)
        * (1 + (N : ℝ) ^ (c / Real.log y) / (c / Real.log y)) := by
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hLA : (0 : ℝ) ≤ Real.log y ^ A := Real.rpow_nonneg hL.le _
  have hfac : (0 : ℝ) ≤ C * Real.log y ^ A * Real.exp (-c * Real.log x / Real.log y) := by
    positivity
  calc ∑ m ∈ s, (smoothCount y (x / m) : ℝ) / x
      ≤ ∑ m ∈ s, C * Real.log y ^ A
          * ((m : ℝ)⁻¹ * Real.exp (-c * Real.log (x / m) / Real.log y)) :=
        Finset.sum_le_sum fun m hm =>
          smoothCount_div_le hR hy (hsm m hm).1 (hsm m hm).2
    _ = ∑ m ∈ s, C * Real.log y ^ A * Real.exp (-c * Real.log x / Real.log y)
          * (m : ℝ) ^ (c / Real.log y - 1) := by
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [inv_mul_exp_neg_log_div hx hL (hsm m hm).1]
        ring
    _ = C * Real.log y ^ A * Real.exp (-c * Real.log x / Real.log y)
          * ∑ m ∈ s, (m : ℝ) ^ (c / Real.log y - 1) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * Real.log y ^ A * Real.exp (-c * Real.log x / Real.log y)
          * ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (c / Real.log y - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hfac
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity
    _ ≤ C * Real.log y ^ A * Real.exp (-c * Real.log x / Real.log y)
          * (1 + (N : ℝ) ^ (c / Real.log y) / (c / Real.log y)) :=
        mul_le_mul_of_nonneg_left (sum_rpow_sub_one_le hβ0 hβ1 N) hfac

/-! ### Step (g2): the fibres of `m ↦ ⌊x/m⌋` are intervals

`⌊x/m⌋ = r` exactly when `x/(r+1) < m ≤ x/r`.  So the fibre is an interval of length
`x/r - x/(r+1) = x/(r(r+1))`, and counting the rough `m` in it is precisely what the sieve
bound of `RMF.exists_roughCount_sub_le` does. -/
lemma floor_div_eq_iff {x : ℝ} {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hx : 0 ≤ x) :
    ⌊x / m⌋₊ = r ↔ x / ((r : ℝ) + 1) < m ∧ (m : ℝ) ≤ x / r := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by linarith
  have hcm : (r : ℝ) * m = (m : ℝ) * r := mul_comm _ _
  have hcm1 : ((r : ℝ) + 1) * m = (m : ℝ) * ((r : ℝ) + 1) := mul_comm _ _
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rintro ⟨h1, h2⟩
    rw [le_div_iff₀ hmR] at h1
    rw [div_lt_iff₀ hmR] at h2
    exact ⟨by rw [div_lt_iff₀ hr1]; linarith, by rw [le_div_iff₀ hrR]; linarith⟩
  · rintro ⟨h1, h2⟩
    rw [div_lt_iff₀ hr1] at h1
    rw [le_div_iff₀ hrR] at h2
    exact ⟨by rw [le_div_iff₀ hmR]; linarith, by rw [div_lt_iff₀ hmR]; linarith⟩

/-- **Step (g2b).**  The rough `m` in a fibre are counted by the sieve interval:
`#{m ≤ x : m rough, ⌊x/m⌋ = r} + Φ(x/(r+1), y) ≤ Φ(x/r, y)`.

Stated additively because `ℕ` subtraction truncates.  The fibre sits inside `A \ B` with `B ⊆ A`
the two counted sets, so this is `Finset.card_sdiff_add_card_eq_card`. -/
lemma card_fibre_add_roughCount_le {y : ℕ} {x : ℝ} (hx : 0 ≤ x) {r : ℕ} (hr : 0 < r) :
    ({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / m⌋₊ = r}).card
        + roughCount y (x / ((r : ℝ) + 1))
      ≤ roughCount y (x / r) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by linarith
  have hmono : x / ((r : ℝ) + 1) ≤ x / r := by
    apply div_le_div_of_nonneg_left hx hrR
    linarith
  have hfloor : ⌊x / ((r : ℝ) + 1)⌋₊ ≤ ⌊x / r⌋₊ := Nat.floor_le_floor hmono
  set A : Finset ℕ := {n ∈ Finset.Icc 1 ⌊x / r⌋₊ | IsRough y n} with hA
  set B : Finset ℕ := {n ∈ Finset.Icc 1 ⌊x / ((r : ℝ) + 1)⌋₊ | IsRough y n} with hB
  have hBA : B ⊆ A := by
    intro n hn
    rw [hB, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [hA, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hn.1.1, hn.1.2.trans hfloor⟩, hn.2⟩
  have hsub : {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / m⌋₊ = r} ⊆ A \ B := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, _⟩, hrough, hfl⟩ := hm
    have hm0 : 0 < m := hm1
    have hiff := (floor_div_eq_iff hm0 hr hx).1 hfl
    refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
    · rw [hA, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hm1, Nat.le_floor hiff.2⟩, hrough⟩
    · rw [hB, Finset.mem_filter]
      rintro ⟨hmem, -⟩
      rw [Finset.mem_Icc] at hmem
      have := (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ x / ((r : ℝ) + 1))).1 hmem.2
      linarith [hiff.1]
  calc ({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / m⌋₊ = r}).card + B.card
      ≤ (A \ B).card + B.card := by
        exact Nat.add_le_add_right (Finset.card_le_card hsub) _
    _ = A.card := Finset.card_sdiff_add_card_eq_card hBA

/-! ### Step (h1): the integral over one unit interval

`∫_r^{r+1} |A(t)|²/t² dt = |A(r)|²/(r(r+1))`, where `A(t) = ∑_{n ≤ t, y-smooth} f(n)`.

`A` is constant on `[r, r+1)`, since it depends on `t` only through `⌊t⌋`, and differs from
`A(r)` only at the single point `r+1`, which is null — hence the `integral_congr_ae`. -/

/-- `A_y(t) = ∑_{n ≤ t, y-smooth} f(n)`, the *unnormalised* smooth partial sum. -/
noncomputable def smoothPartial (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (t : ℝ) (ω : Ω) : ℂ :=
  ∑ n ∈ {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, f ω n

omit [MeasurableSpace Ω] in
lemma smoothSum_eq_smoothPartial_div (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (t : ℝ) (ω : Ω) :
    smoothSum f y t ω = smoothPartial f y t ω / (Real.sqrt t : ℂ) := rfl

omit [MeasurableSpace Ω] in
lemma smoothPartial_congr (f : Ω → ArithmeticFunction ℂ) (y : ℕ) {s t : ℝ}
    (h : ⌊s⌋₊ = ⌊t⌋₊) (ω : Ω) : smoothPartial f y s ω = smoothPartial f y t ω := by
  rw [smoothPartial, smoothPartial, h]

omit [MeasurableSpace Ω] in
/-- **Step (h1).** -/
lemma integral_normSq_smoothPartial_unit {f : Ω → ArithmeticFunction ℂ} (y : ℕ) {r : ℕ}
    (hr : 0 < r) (ω : Ω) :
    (∫ t in (r : ℝ)..((r : ℝ) + 1), ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2)
      = ‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / ((r : ℝ) * ((r : ℝ) + 1)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by linarith
  have hfl : ⌊(r : ℝ)⌋₊ = r := Nat.floor_natCast r
  -- the integrand is constant off a null set
  have hnotmem : (0 : ℝ) ∉ Set.uIcc (r : ℝ) ((r : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith : (r : ℝ) ≤ (r : ℝ) + 1)]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h0
    linarith
  have hae : ∀ᵐ t : ℝ, t ∈ Set.uIoc (r : ℝ) ((r : ℝ) + 1) →
      ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2 = ‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / t ^ 2 := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.2
      (MeasureTheory.measure_singleton ((r : ℝ) + 1))] with t ht htI
    have hmem : t ∈ Set.Ioc (r : ℝ) ((r : ℝ) + 1) := by
      rwa [Set.uIoc_of_le (by linarith)] at htI
    have hne : t ≠ (r : ℝ) + 1 := ht
    have hflt : ⌊t⌋₊ = r := by
      rw [Nat.floor_eq_iff (by linarith [hmem.1])]
      exact ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hne⟩
    rw [smoothPartial_congr f y (hflt.trans hfl.symm) ω]
  rw [intervalIntegral.integral_congr_ae hae]
  have hzp : ∀ t : ℝ, ‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / t ^ 2
      = ‖smoothPartial f y (r : ℝ) ω‖ ^ 2 * t ^ (-2 : ℤ) := by
    intro t
    rw [zpow_neg, zpow_two, ← pow_two]
    ring
  simp_rw [hzp]
  rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, hnotmem⟩)]
  have h1 : ((r : ℝ) + 1) ≠ 0 := by linarith
  have h2 : (r : ℝ) ≠ 0 := by linarith
  norm_num
  field_simp
  ring

/-! ### Step (h2): summing the unit intervals

`∑_{r=1}^{R} |A(r)|²/r² ≤ 2 ∫_1^{R+1} |A(t)|²/t² dt`.

By (h1) the `r`-th integral is `|A(r)|²/(r(r+1))`, and `r + 1 ≤ 2r` for `r ≥ 1`, so each term of
the sum is at most twice its integral.  The factor `2` is absolute. -/

omit [MeasurableSpace Ω] in
/-- `t ↦ A_y(t)` is a step function of `⌊t⌋`, hence measurable. -/
lemma measurable_smoothPartial (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (ω : Ω) :
    Measurable fun t : ℝ => smoothPartial f y t ω := by
  have h : (fun t : ℝ => smoothPartial f y t ω)
      = (fun n : ℕ => ∑ k ∈ {k ∈ Finset.Icc 1 n | k ∈ Nat.smoothNumbers (y + 1)}, f ω k)
        ∘ (fun t : ℝ => ⌊t⌋₊) := rfl
  rw [h]
  exact measurable_from_top.comp Nat.measurable_floor

omit [MeasurableSpace Ω] in
lemma norm_smoothPartial_le (f : Ω → ArithmeticFunction ℂ) (y : ℕ) {t b : ℝ} (htb : t ≤ b)
    (ω : Ω) : ‖smoothPartial f y t ω‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f ω n‖ := by
  have hsub : {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}
      ⊆ Finset.Icc 1 ⌊b⌋₊ := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_Icc]
    exact ⟨hn.1.1, hn.1.2.trans (Nat.floor_le_floor htb)⟩
  calc ‖smoothPartial f y t ω‖
      ≤ ∑ n ∈ {n ∈ Finset.Icc 1 ⌊t⌋₊ | n ∈ Nat.smoothNumbers (y + 1)}, ‖f ω n‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f ω n‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => norm_nonneg _

omit [MeasurableSpace Ω] in
/-- The step integrand is interval integrable away from `0`: measurable, and on `[a,b]` bounded
by `(∑_{n ≤ b} ‖f ω n‖)² / a²`.  No `a.e.`-in-`ω` hypothesis is needed — for each fixed `ω` the
bound is a finite sum. -/
lemma intervalIntegrable_normSq_smoothPartial (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (ω : Ω)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2)
      MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hms : Measurable fun t : ℝ => ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2 := by
    have := (measurable_smoothPartial f y ω).norm
    fun_prop
  refine (MeasureTheory.memLp_top_of_bound hms.aestronglyMeasurable
    ((∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f ω n‖) ^ 2 / a ^ 2) ?_).integrable le_top
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  have h1 : ‖smoothPartial f y t ω‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f ω n‖ :=
    norm_smoothPartial_le f y ht.2 ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  exact ht.1.le

omit [MeasurableSpace Ω] in
/-- **Step (h2).** -/
lemma sum_normSq_div_sq_le {f : Ω → ArithmeticFunction ℂ} (y : ℕ) (R : ℕ) (ω : Ω) :
    ∑ r ∈ Finset.Icc 1 R, ‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / (r : ℝ) ^ 2
      ≤ 2 * ∫ t in (1 : ℝ)..((R : ℝ) + 1), ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2 := by
  have hadj : ∑ k ∈ Finset.range R,
      (∫ t in ((k : ℝ) + 1)..((k : ℝ) + 1 + 1), ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2)
      = ∫ t in (1 : ℝ)..((R : ℝ) + 1), ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2 := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) + 1) (n := R)
      (f := fun t : ℝ => ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2)
      (fun k _ => intervalIntegrable_normSq_smoothPartial f y ω
        (by positivity) (by push_cast; linarith))
    simpa using h
  rw [← hadj, Finset.mul_sum]
  have hIcc : Finset.Icc 1 R = (Finset.range R).image (· + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨m - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  have hinj : ∀ a ∈ Finset.range R, ∀ b ∈ Finset.range R, a + 1 = b + 1 → a = b := by
    intro a _ b _ h
    omega
  rw [hIcc, Finset.sum_image hinj]
  refine Finset.sum_le_sum fun k _ => ?_
  have hkey := integral_normSq_smoothPartial_unit (f := f) y (Nat.succ_pos k) ω
  push_cast at hkey ⊢
  rw [hkey]
  have hk0 : (0 : ℝ) ≤ ‖smoothPartial f y ((k : ℝ) + 1) ω‖ ^ 2 := by positivity
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have hprod : (0 : ℝ)
      ≤ ‖smoothPartial f y ((k : ℝ) + 1) ω‖ ^ 2 * ((k : ℝ) + 1) * (k : ℝ) := by positivity
  nlinarith [hprod]

/-! ### Step (g2c): the large range, fibre by fibre

Writing `A` for the *unnormalised* smooth sum, `S_{x/m,y} = A(x/m)/√(x/m)`, so

`m⁻¹ |S_{x/m,y}|² = m⁻¹ · |A(x/m)|² · m/x = |A(⌊x/m⌋)|² / x`,

with **no `m` and no `r` left outside the argument of `A`**.  So each fibre of `m ↦ ⌊x/m⌋`
contributes `(fibre size) · |A(r)|²/x`, and the sieve bounds the fibre size directly. -/

omit [MeasurableSpace Ω] in
/-- **Step (g2c), the identity.**  `m⁻¹|S_{x/m,y}|² = |A(x/m)|²/x`. -/
lemma roughTerm_eq_normSq_smoothPartial (f : Ω → ArithmeticFunction ℂ) (y : ℕ) {x : ℝ}
    {m : ℕ} (hm : 0 < m) (hx : 0 < x) (ω : Ω) :
    roughTerm f y x ω m = ‖smoothPartial f y (x / m) ω‖ ^ 2 / x := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hq : (0 : ℝ) < x / m := by positivity
  have hnorm : ‖smoothSum f y (x / m) ω‖ ^ 2
      = ‖smoothPartial f y (x / m) ω‖ ^ 2 / (x / m) := by
    rw [smoothSum_eq_smoothPartial_div, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hq.le]
  rw [roughTerm, hnorm]
  field_simp

omit [MeasurableSpace Ω] in
/-- **Step (g2c), the regrouping.**  Summing over `m` becomes summing over the fibres of
`m ↦ ⌊x/m⌋`, each contributing its size times a value depending only on `r`. -/
lemma sum_roughTerm_fiberwise {f : Ω → ArithmeticFunction ℂ} (y : ℕ) {x : ℝ} (hx : 0 < x)
    {s : Finset ℕ} (hs0 : ∀ m ∈ s, 0 < m) {R : ℕ}
    (hmaps : ∀ m ∈ s, ⌊x / (m : ℝ)⌋₊ ∈ Finset.Icc 1 R) (ω : Ω) :
    ∑ m ∈ s, roughTerm f y x ω m
      = ∑ r ∈ Finset.Icc 1 R,
          ((s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)).card : ℝ)
            * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / x) := by
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun m => roughTerm f y x ω m)]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hconst : ∀ m ∈ s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r),
      roughTerm f y x ω m = ‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / x := by
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [roughTerm_eq_normSq_smoothPartial f y (hs0 m hm.1) hx ω,
      smoothPartial_congr f y (hm.2.trans (Nat.floor_natCast r).symm) ω]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

/-! ### Step (i): Parseval

`∫_0^∞ |A(u)|²/u² du = (1/2π) ∫_ℝ |F_y(1/2+it)/(1/2+it)|² dt`.

The coefficients are `aₙ = f(n)·1_{n y-smooth}`, whose partial sums are exactly `A`.  The
summability hypothesis holds **a.e. in `ω`**, not surely: `‖f ω n‖ ≤ 1` is itself an a.e.
statement, so the conclusion is an a.e. statement too.  That is the only step of the reduction
with this shape. -/

omit [MeasurableSpace Ω] in
lemma sum_smoothCoeff (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (u : ℝ) (ω : Ω) :
    ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, smoothCoeff f y ω n = smoothPartial f y u ω := by
  rw [smoothPartial, Finset.sum_filter]
  rfl

/-- Almost surely, the smooth coefficients satisfy Parseval's hypothesis. -/
lemma summable_norm_smoothCoeff_div_sqrt {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (y : ℕ) :
    ∀ᵐ ω ∂μ, Summable fun n : ℕ => ‖smoothCoeff f y ω n‖ / Real.sqrt n := by
  have hall : ∀ᵐ ω ∂μ, ∀ n : ℕ, ‖f ω n‖ ≤ 1 := by
    rw [MeasureTheory.ae_all_iff]
    exact hf.ae_norm_le_one
  filter_upwards [hall] with ω hω
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_smoothIndicator_div_sqrt y)
  rw [smoothCoeff]
  split_ifs with hmem
  · exact div_le_div_of_nonneg_right (hω n) (Real.sqrt_nonneg _)
  · simp

/-- **Step (i).**  Parseval for the smooth coefficients: almost surely `|A_y(u)|²/u²` is
integrable on `(0,∞)` and `∫_0^∞ |A_y(u)|²/u² du = (1/2π) ∫_ℝ |F_y(1/2+it)/(1/2+it)|² dt`,
with `F_y` the Dirichlet series of the coefficients.  The `a.e.` is unavoidable: Parseval needs
`Summable (‖aₙ‖/√n)`, which rests on `‖f ω n‖ ≤ 1`, itself only an almost-sure statement. -/
theorem integral_normSq_smoothPartial_eq {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (y : ℕ) :
    ∀ᵐ ω ∂μ, IntegrableOn (fun u : ℝ => ‖smoothPartial f y u ω‖ ^ 2 / u ^ 2) (Ioi (0 : ℝ))
      ∧ (∫ u in Ioi (0 : ℝ), ‖smoothPartial f y u ω‖ ^ 2 / u ^ 2)
        = (2 * π)⁻¹ * ∫ t : ℝ, ‖dirichletSeries (smoothCoeff f y ω) (1 / 2 + t * Complex.I)
            / (1 / 2 + t * Complex.I)‖ ^ 2 := by
  filter_upwards [summable_norm_smoothCoeff_div_sqrt hf y] with ω hω
  simpa only [sum_smoothCoeff] using integral_normSq_partialSum_eq (smoothCoeff f y ω) hω

omit [MeasurableSpace Ω] in
/-- The truncated integral is at most the full one: the integrand is nonnegative, and it is
integrable on `(0,∞)` by step (i). -/
lemma integral_unit_le_integral_Ioi {f : Ω → ArithmeticFunction ℂ} (y : ℕ) (R : ℕ) (ω : Ω)
    (hint : IntegrableOn (fun u : ℝ => ‖smoothPartial f y u ω‖ ^ 2 / u ^ 2) (Ioi (0 : ℝ))) :
    (∫ t in (1 : ℝ)..((R : ℝ) + 1), ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2)
      ≤ ∫ t in Ioi (0 : ℝ), ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2 := by
  have hle : (1 : ℝ) ≤ (R : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) R
    linarith
  have hsub : Set.Ioc (1 : ℝ) ((R : ℝ) + 1) ⊆ Set.Ioi (0 : ℝ) :=
    Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi (by norm_num))
  rw [intervalIntegral.integral_of_le hle]
  refine MeasureTheory.setIntegral_mono_set hint ?_ (LE.le.eventuallyLE hsub)
  filter_upwards with u using by positivity

/-- **Step (g2d).**  The fibre count, bounded by the sieve: `hS` (met by
`RMF.exists_roughCount_sub_le`) on `(x/(r+1), x/r]`, of length `H = x/r - x/(r+1)`, gives
`#{m : m rough, ⌊x/m⌋ = r} ≤ Cs·H/log y`.  This is the sole source of the `1/log y`
normalisation in the reduction; the side conditions are met by `RMF.sieve_conditions`. -/
lemma card_fibre_le_of_sieve {Cs : ℝ}
    (hS : ∀ (y : ℕ) (x H : ℝ), 2 ≤ y → 0 < x → 0 < H → (y : ℝ) ≤ H →
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ H →
      (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ) ≤ Cs * H / Real.log y)
    {y : ℕ} (hy : 2 ≤ y) {x : ℝ} (hx : 0 ≤ x) {r : ℕ} (hr : 0 < r)
    (hxr : 2 ≤ x / ((r : ℝ) + 1)) (hH : 2 ≤ x / r - x / ((r : ℝ) + 1))
    (hyH : (y : ℝ) ≤ x / r - x / ((r : ℝ) + 1))
    (habs : 5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ x / r - x / ((r : ℝ) + 1)) :
    (({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r}).card : ℝ)
      ≤ Cs * (x / r - x / ((r : ℝ) + 1)) / Real.log y := by
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hcast : (({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r}).card : ℝ)
      + (roughCount y (x / ((r : ℝ) + 1)) : ℝ) ≤ (roughCount y (x / r) : ℝ) := by
    exact_mod_cast card_fibre_add_roughCount_le (y := y) hx hr
  have hsieve := hS y (x / ((r : ℝ) + 1)) (x / r - x / ((r : ℝ) + 1)) hy
    (by linarith) (by linarith) hyH habs
  rw [show x / ((r : ℝ) + 1) + (x / r - x / ((r : ℝ) + 1)) = x / r by ring] at hsieve
  linarith

/-! ### Step (j1): the large range, bounded

Chaining (g2c), (g2d) and (h2): each fibre contributes `(size)·|A(r)|²/x`, the sieve bounds the
size by `Cs·H_r/log y` with `H_r/x = 1/(r(r+1))`, and `r(r+1) ≥ r²` turns the result into the
Riemann sum that (h2) compares with the integral.

The four sieve side conditions are carried as `hsieveOK`; at `R = ⌊x^{1/4}⌋` they are met by
`RMF.sieve_conditions`. -/
omit [MeasurableSpace Ω] in
lemma sum_roughTerm_large_le {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hS : ∀ (y : ℕ) (x H : ℝ), 2 ≤ y → 0 < x → 0 < H → (y : ℝ) ≤ H →
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ H →
      (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ) ≤ Cs * H / Real.log y)
    {f : Ω → ArithmeticFunction ℂ} {y : ℕ} (hy : 2 ≤ y) {x : ℝ} (hx : 0 < x) {R : ℕ}
    {s : Finset ℕ} (hs0 : ∀ m ∈ s, 0 < m)
    (hmaps : ∀ m ∈ s, ⌊x / (m : ℝ)⌋₊ ∈ Finset.Icc 1 R)
    (hsieveOK : ∀ r ∈ Finset.Icc 1 R, 2 ≤ x / ((r : ℝ) + 1) ∧
      2 ≤ x / r - x / ((r : ℝ) + 1) ∧ (y : ℝ) ≤ x / r - x / ((r : ℝ) + 1) ∧
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ x / r - x / ((r : ℝ) + 1))
    (hfib : ∀ r ∈ Finset.Icc 1 R,
      s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)
        ⊆ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r})
    (ω : Ω) :
    ∑ m ∈ s, roughTerm f y x ω m
      ≤ (2 * Cs / Real.log y)
          * ∫ t in (1 : ℝ)..((R : ℝ) + 1), ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2 := by
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  rw [sum_roughTerm_fiberwise y hx hs0 hmaps ω]
  have hterm : ∀ r ∈ Finset.Icc 1 R,
      ((s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)).card : ℝ)
          * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / x)
        ≤ Cs / Real.log y * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / (r : ℝ) ^ 2) := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := hsieveOK r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.1 hr).1
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
    have hcard : ((s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)).card : ℝ)
        ≤ Cs * (x / r - x / ((r : ℝ) + 1)) / Real.log y := by
      refine le_trans ?_ (card_fibre_le_of_sieve hS hy hx.le (by omega) h1 h2 h3 h4)
      exact_mod_cast Finset.card_le_card (hfib r hr)
    have hA : (0 : ℝ) ≤ ‖smoothPartial f y (r : ℝ) ω‖ ^ 2 := by positivity
    have hr0 : (r : ℝ) ≠ 0 := hrR.ne'
    have hr10 : ((r : ℝ) + 1) ≠ 0 := by positivity
    have hx0 : x ≠ 0 := hx.ne'
    have hL0 : Real.log y ≠ 0 := hL.ne'
    calc ((s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)).card : ℝ)
            * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / x)
        ≤ Cs * (x / r - x / ((r : ℝ) + 1)) / Real.log y
            * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / x) := by
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = Cs / Real.log y * ‖smoothPartial f y (r : ℝ) ω‖ ^ 2
            * (1 / ((r : ℝ) * ((r : ℝ) + 1))) := by
          field_simp
          ring
      _ ≤ Cs / Real.log y * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / (r : ℝ) ^ 2) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hA, hrR]
  calc ∑ r ∈ Finset.Icc 1 R,
        ((s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)).card : ℝ)
          * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / x)
      ≤ ∑ r ∈ Finset.Icc 1 R,
          Cs / Real.log y * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / (r : ℝ) ^ 2) :=
        Finset.sum_le_sum hterm
    _ = Cs / Real.log y
          * ∑ r ∈ Finset.Icc 1 R, ‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / (r : ℝ) ^ 2 :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ Cs / Real.log y
          * (2 * ∫ t in (1 : ℝ)..((R : ℝ) + 1), ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2) := by
        exact mul_le_mul_of_nonneg_left (sum_normSq_div_sq_le y R ω) (by positivity)
    _ = (2 * Cs / Real.log y)
          * ∫ t in (1 : ℝ)..((R : ℝ) + 1), ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2 := by ring

/-! ### Step (j2): the small range, bounded

Unconditional Jensen moves the expectation outside, (e1) turns it into a sum of smooth counts,
and (e4) bounds that by Rankin.  Conditioning has done its work by this point. -/

/-- The rough sum is bounded a.e., crudely: `‖S_{x/m,y}‖ ≤ x/m` gives each term `≤ x²/m³ ≤ x²`. -/
lemma sum_roughTerm_le_ae {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) (y : ℕ) {x : ℝ} (hx : 1 ≤ x) {s : Finset ℕ}
    (hs : ∀ m ∈ s, 0 < m ∧ 1 ≤ x / m) :
    ∀ᵐ ω ∂μ, ∑ m ∈ s, roughTerm f y x ω m ≤ x ^ 2 * s.card := by
  have hall : ∀ᵐ ω ∂μ, ∀ m ∈ s, ‖smoothSum f y (x / m) ω‖ ≤ x / m := by
    rw [Filter.eventually_all_finset]
    intro m hm
    exact norm_smoothSum_le hf y (hs m hm).2
  filter_upwards [hall] with ω hω
  calc ∑ m ∈ s, roughTerm f y x ω m ≤ ∑ _m ∈ s, x ^ 2 := by
        refine Finset.sum_le_sum fun m hm => ?_
        obtain ⟨hm0, hmx⟩ := hs m hm
        have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm0
        have hb := hω m hm
        have hnn : (0 : ℝ) ≤ ‖smoothSum f y (x / m) ω‖ := norm_nonneg _
        have hsq : ‖smoothSum f y (x / m) ω‖ ^ 2 ≤ (x / m) ^ 2 :=
          pow_le_pow_left₀ hnn hb 2
        have hxm : x / m ≤ x := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        rw [roughTerm]
        have : (m : ℝ)⁻¹ ≤ 1 := by
          rw [inv_le_one_iff₀]
          right
          exact hmR
        nlinarith [sq_nonneg (x / m), hsq, hxm, hnn]
    _ = x ^ 2 * s.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma integrable_rpow_sum_roughTerm {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) (y : ℕ) {x : ℝ} (hx : 1 ≤ x)
    {s : Finset ℕ} (hs : ∀ m ∈ s, 0 < m ∧ 1 ≤ x / m) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun ω => (∑ m ∈ s, roughTerm f y x ω m) ^ q) μ := by
  have hms : Measurable fun ω => (∑ m ∈ s, roughTerm f y x ω m) ^ q := by
    have h1 : ∀ m : ℕ, Measurable fun ω => roughTerm f y x ω m := by
      intro m
      have := (measurable_smoothSum hf y (x / m)).norm
      unfold roughTerm
      fun_prop
    have h2 : Measurable fun ω => ∑ m ∈ s, roughTerm f y x ω m :=
      Finset.measurable_sum _ fun m _ => h1 m
    fun_prop
  refine (MeasureTheory.memLp_top_of_bound hms.aestronglyMeasurable
    ((x ^ 2 * s.card) ^ q) ?_).integrable le_top
  filter_upwards [sum_roughTerm_le_ae hf y hx hs] with ω hω
  have hnn : (0 : ℝ) ≤ ∑ m ∈ s, roughTerm f y x ω m :=
    Finset.sum_nonneg fun m _ => roughTerm_nonneg _ _ _ _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnn q)]
  exact Real.rpow_le_rpow hnn hω hq

/-! ### Step (j3): the large range, in terms of the Euler product -/

omit [MeasurableSpace Ω] in
/-- (j1) followed by the comparison with the full integral. -/
lemma sum_roughTerm_large_le_Ioi {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hS : ∀ (y : ℕ) (x H : ℝ), 2 ≤ y → 0 < x → 0 < H → (y : ℝ) ≤ H →
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ H →
      (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ) ≤ Cs * H / Real.log y)
    {f : Ω → ArithmeticFunction ℂ} {y : ℕ} (hy : 2 ≤ y) {x : ℝ} (hx : 0 < x) {R : ℕ}
    {s : Finset ℕ} (hs0 : ∀ m ∈ s, 0 < m)
    (hmaps : ∀ m ∈ s, ⌊x / (m : ℝ)⌋₊ ∈ Finset.Icc 1 R)
    (hsieveOK : ∀ r ∈ Finset.Icc 1 R, 2 ≤ x / ((r : ℝ) + 1) ∧
      2 ≤ x / r - x / ((r : ℝ) + 1) ∧ (y : ℝ) ≤ x / r - x / ((r : ℝ) + 1) ∧
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ x / r - x / ((r : ℝ) + 1))
    (hfib : ∀ r ∈ Finset.Icc 1 R,
      s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)
        ⊆ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r})
    (ω : Ω)
    (hint : IntegrableOn (fun u : ℝ => ‖smoothPartial f y u ω‖ ^ 2 / u ^ 2) (Ioi (0 : ℝ))) :
    ∑ m ∈ s, roughTerm f y x ω m
      ≤ (2 * Cs / Real.log y) * ∫ u in Ioi (0 : ℝ), ‖smoothPartial f y u ω‖ ^ 2 / u ^ 2 := by
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  refine le_trans (sum_roughTerm_large_le hCs hS hy hx hs0 hmaps hsieveOK hfib ω) ?_
  exact mul_le_mul_of_nonneg_left (integral_unit_le_integral_Ioi y R ω hint) (by positivity)

/-- The full integral **is** the Euler-product line integral, up to `(2π)⁻¹ log y`.

Parseval (i) turns it into a Dirichlet-series integral, and the Euler-product supplier rewrites
the series as `randomEulerProduct` — pointwise in `t`, which is why that supplier quantifies `s`
inside the `a.e.`. -/
lemma integral_Ioi_eq_eulerLineIntegral {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsBoundedRMF f μ) {y : ℕ} (hy : 2 ≤ y)
    (hdir : ∀ᵐ ω ∂μ, ∀ z : ℂ, 0 < z.re →
      dirichletSeries (smoothCoeff f y ω) z = randomEulerProduct f (y + 1) z ω)
    :
    ∀ᵐ ω ∂μ, (∫ u in Ioi (0 : ℝ), ‖smoothPartial f y u ω‖ ^ 2 / u ^ 2)
      = (2 * π)⁻¹ * Real.log y * eulerLineIntegral f (y : ℝ) ω := by
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  filter_upwards [integral_normSq_smoothPartial_eq hf y, hdir] with ω h1 h2
  have hcongr : ∀ t : ℝ,
      ‖dirichletSeries (smoothCoeff f y ω) (1 / 2 + t * Complex.I)
          / (1 / 2 + t * Complex.I)‖ ^ 2
        = ‖randomEulerProduct f (y + 1) (1 / 2 + t * Complex.I) ω
            / (1 / 2 + t * Complex.I)‖ ^ 2 := by
    intro t
    rw [h2 _ (by simp)]
  rw [h1.2]
  simp_rw [hcongr]
  rw [eulerLineIntegral, Nat.floor_natCast,
    show (((1 / 2 : ℝ) : ℂ)) = 1 / 2 by push_cast; ring]
  -- abstract the integral: `field_simp` would otherwise normalise inside the integrand
  generalize (∫ t : ℝ, ‖randomEulerProduct f (y + 1) (1 / 2 + (t : ℂ) * Complex.I) ω
    / (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2) = I
  field_simp

/-- **The large range, in final form.**  Almost surely,
`∑_{m large} m⁻¹|S_{x/m,y}|² ≤ (Cs/π) · (1/log y)∫_ℝ|A_y(1/2+it)/(1/2+it)|² dt`.

**The `log y` cancels.**  The sieve contributes `1/log y` and Parseval contributes `log y` back
through the normalisation of `eulerLineIntegral`, leaving the constant `Cs/π`: this is why the
reduction's implied constant does not depend on `y`. -/
lemma sum_roughTerm_large_le_euler {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hS : ∀ (y : ℕ) (x H : ℝ), 2 ≤ y → 0 < x → 0 < H → (y : ℝ) ≤ H →
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ H →
      (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ) ≤ Cs * H / Real.log y)
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsBoundedRMF f μ)
    {y : ℕ} (hy : 2 ≤ y)
    (hdir : ∀ᵐ ω ∂μ, ∀ z : ℂ, 0 < z.re →
      dirichletSeries (smoothCoeff f y ω) z = randomEulerProduct f (y + 1) z ω)
    {x : ℝ} (hx : 0 < x) {R : ℕ} {s : Finset ℕ}
    (hs0 : ∀ m ∈ s, 0 < m) (hmaps : ∀ m ∈ s, ⌊x / (m : ℝ)⌋₊ ∈ Finset.Icc 1 R)
    (hsieveOK : ∀ r ∈ Finset.Icc 1 R, 2 ≤ x / ((r : ℝ) + 1) ∧
      2 ≤ x / r - x / ((r : ℝ) + 1) ∧ (y : ℝ) ≤ x / r - x / ((r : ℝ) + 1) ∧
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ x / r - x / ((r : ℝ) + 1))
    (hfib : ∀ r ∈ Finset.Icc 1 R,
      s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)
        ⊆ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r}) :
    ∀ᵐ ω ∂μ, ∑ m ∈ s, roughTerm f y x ω m
      ≤ (Cs / π) * eulerLineIntegral f (y : ℝ) ω := by
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  filter_upwards [integral_normSq_smoothPartial_eq hf y,
    integral_Ioi_eq_eulerLineIntegral hf hy hdir] with ω h1 h2
  have hchain := sum_roughTerm_large_le_Ioi hCs hS hy hx hs0 hmaps hsieveOK hfib ω h1.1
  rw [h2] at hchain
  refine hchain.trans (le_of_eq ?_)
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **The small range, in final form.**  Unconditional Jensen, then (e1) and (e4):

`E[(∑_{m ≤ N} m⁻¹|S_{x/m,y}|²)^q] ≤ (C (log y)^A e^{-c log x/log y}(1 + N^β/β))^q`.

At `log y = log x/(log log x)²` and `N = x^{3/4}` the bracket is `e^{-(c/4)(log log x)²}` up to
powers of `log y`, so the whole term is below every power of `log log x`. -/
lemma integral_rpow_sum_small_le {A cR CR : ℝ}
    (hR : ∀ (y : ℕ) (x : ℝ), 2 ≤ y → 2 ≤ x →
      (smoothCount y x : ℝ)
        ≤ CR * x * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y))
    (hCR : 0 ≤ CR) {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hf : IsSteinhausRMF f μ) {y : ℕ} (hy : 2 ≤ y) {x q : ℝ} (hx : 1 ≤ x)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {N : ℕ} {s : Finset ℕ} (hsub : s ⊆ Finset.Icc 1 N)
    (hsm : ∀ m ∈ s, 0 < m ∧ 2 ≤ x / m)
    (hβ0 : 0 < cR / Real.log y) (hβ1 : cR / Real.log y ≤ 1) :
    ∫ ω, (∑ m ∈ s, roughTerm f y x ω m) ^ q ∂μ
      ≤ (CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
          * (1 + (N : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))) ^ q := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsm1 : ∀ m ∈ s, 0 < m ∧ 1 ≤ x / m := fun m hm => ⟨(hsm m hm).1, by linarith [(hsm m hm).2]⟩
  have hnn : ∀ᵐ ω ∂μ, (∑ m ∈ s, roughTerm f y x ω m) ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall fun ω =>
      Set.mem_Ici.2 (Finset.sum_nonneg fun m _ => roughTerm_nonneg _ _ _ _ _)
  have hint : Integrable (fun ω => ∑ m ∈ s, roughTerm f y x ω m) μ :=
    integrable_finsetSum _ fun m hm => integrable_roughTerm hf.isBoundedRMF y (hsm1 m hm).2
  have hintq := integrable_rpow_sum_roughTerm hf.isBoundedRMF y hx hsm1 hq0
  calc ∫ ω, (∑ m ∈ s, roughTerm f y x ω m) ^ q ∂μ
      ≤ (∫ ω, ∑ m ∈ s, roughTerm f y x ω m ∂μ) ^ q :=
        integral_rpow_le_rpow_integral hq0 hq1 hnn hint hintq
    _ = (∑ m ∈ s, (smoothCount y (x / m) : ℝ) / x) ^ q := by
        rw [integral_sum_roughTerm hf y hx0 hsm1]
    _ ≤ (CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
          * (1 + (N : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))) ^ q := by
        refine Real.rpow_le_rpow (Finset.sum_nonneg fun m hm => ?_)
          (sum_smoothCount_div_le hR hCR hy hx0 hsub hsm hβ0 hβ1) hq0
        positivity

/-! ### Step (j4): splitting the integral -/

/-- Every `m` in the rough range satisfies `1 ≤ x/m`, since `m ≤ ⌊x⌋ ≤ x`. -/
lemma rough_mem_facts {x : ℝ} (hx : 1 ≤ x) {P : ℕ → Prop} [DecidablePred P]
    {m : ℕ} (hm : m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | P m}) : 0 < m ∧ 1 ≤ x / m := by
  rw [Finset.mem_filter, Finset.mem_Icc] at hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1.1
  refine ⟨hm.1.1, ?_⟩
  have h1 : (m : ℝ) ≤ x :=
    le_trans (by exact_mod_cast hm.1.2) (Nat.floor_le (by linarith))
  rw [le_div_iff₀ hm0]
  linarith

/-- **Step (j4).**  Subadditivity of `t ↦ t^q` splits the integral at `N`. -/
lemma integral_rpow_split {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) (y : ℕ) {x q : ℝ} (hx : 1 ≤ x)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) :
    ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m}, roughTerm f y x ω m) ^ q ∂μ
      ≤ (∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N},
            roughTerm f y x ω m) ^ q ∂μ)
        + ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
            roughTerm f y x ω m) ^ q ∂μ := by
  have hA := integrable_rpow_sum_roughTerm hf y hx
    (fun m hm => rough_mem_facts (P := fun m => IsRough y m) hx hm) hq0
  have hS := integrable_rpow_sum_roughTerm hf y hx
    (fun m hm => rough_mem_facts (P := fun m => IsRough y m ∧ m ≤ N) hx hm) hq0
  have hL := integrable_rpow_sum_roughTerm hf y hx
    (fun m hm => rough_mem_facts (P := fun m => IsRough y m ∧ ¬ m ≤ N) hx hm) hq0
  rw [← integral_add hS hL]
  exact integral_mono hA (hS.add hL) fun ω => rpow_rough_sum_le_add hq0 hq1 N ω

/-! ### Step (j5): the two branches combined -/

/-- **The reduction, given the parameters.**  Both branches, combined:
`E|S_x|^{2q} ≤ (Rankin bound)^q + (Cs/π)^q E[(eulerLineIntegral)^q]`.

`RMF.reduction_upper_of_core` chooses `N = ⌊x^{3/4}⌋` and `R = ⌊x^{1/4}⌋`, checks the
hypotheses, and folds the constants. -/
theorem reduction_core {A cR CR Cs : ℝ}
    (hR : ∀ (y : ℕ) (x : ℝ), 2 ≤ y → 2 ≤ x →
      (smoothCount y x : ℝ)
        ≤ CR * x * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y))
    (hCR : 0 ≤ CR)
    (hS : ∀ (y : ℕ) (x H : ℝ), 2 ≤ y → 0 < x → 0 < H → (y : ℝ) ≤ H →
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ H →
      (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ) ≤ Cs * H / Real.log y)
    (hCs : 0 ≤ Cs)
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ)
    {y : ℕ} (hy : 2 ≤ y) {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {N R : ℕ}
    (hsmall2 : ∀ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N}, 2 ≤ x / m)
    (hsmallsub : {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N} ⊆ Finset.Icc 1 N)
    (hmaps : ∀ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
      ⌊x / (m : ℝ)⌋₊ ∈ Finset.Icc 1 R)
    (hsieveOK : ∀ r ∈ Finset.Icc 1 R, 2 ≤ x / ((r : ℝ) + 1) ∧
      2 ≤ x / r - x / ((r : ℝ) + 1) ∧ (y : ℝ) ≤ x / r - x / ((r : ℝ) + 1) ∧
      5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ x / r - x / ((r : ℝ) + 1))
    (hfib : ∀ r ∈ Finset.Icc 1 R,
      {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N}.filter
          (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)
        ⊆ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r})
    (hβ0 : 0 < cR / Real.log y) (hβ1 : cR / Real.log y ≤ 1) :
    ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
      ≤ (CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
            * (1 + (N : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))) ^ q
        + (Cs / π) ^ q * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ := by
  obtain ⟨X, hX, hfX⟩ := hf.exists_primeValues
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hfr : IsSteinhausRMF f μ := isSteinhausRMF_iff_exists.2 ⟨X, hX, hfX⟩
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hx0 : (0 : ℝ) < x := by linarith
  have hCsπ : (0 : ℝ) ≤ Cs / π := by positivity
  -- the large branch, integrated
  have hlarge : ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
        roughTerm f y x ω m) ^ q ∂μ
      ≤ (Cs / π) ^ q * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ := by
    have hfun : (fun ω => ((Cs / π) * eulerLineIntegral f (y : ℝ) ω) ^ q)
        = fun ω => (Cs / π) ^ q * eulerLineIntegral f (y : ℝ) ω ^ q := by
      funext ω
      exact Real.mul_rpow hCsπ (eulerLineIntegral_nonneg hyR ω)
    have hint : Integrable (fun ω => ((Cs / π) * eulerLineIntegral f (y : ℝ) ω) ^ q) μ := by
      rw [hfun]
      exact (integrable_eulerLineIntegral_rpow hfr (y := (y : ℝ)) hyR hq0).const_mul _
    have hbd := sum_roughTerm_large_le_euler hCs hS hfr.isBoundedRMF hy
      (dirichletSeries_smoothCoeff_eq hfr y) hx0
      (fun m hm => (rough_mem_facts (P := fun m => IsRough y m ∧ ¬ m ≤ N) hx hm).1)
      hmaps hsieveOK hfib
    calc ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
            roughTerm f y x ω m) ^ q ∂μ
        ≤ ∫ ω, ((Cs / π) * eulerLineIntegral f (y : ℝ) ω) ^ q ∂μ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
            Real.rpow_nonneg (Finset.sum_nonneg fun m _ => roughTerm_nonneg _ _ _ _ _) q)
            hint ?_
          filter_upwards [hbd] with ω hω
          exact Real.rpow_le_rpow
            (Finset.sum_nonneg fun m _ => roughTerm_nonneg _ _ _ _ _) hω hq0
      _ = (Cs / π) ^ q * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ := by
          rw [hfun, integral_const_mul]
  calc ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
          roughTerm f y x ω m) ^ q ∂μ :=
        integral_rpow_le_integral_rough_sum hX hfX (y := y) hx hq0 hq1
    _ ≤ (∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N},
            roughTerm f y x ω m) ^ q ∂μ)
          + ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
            roughTerm f y x ω m) ^ q ∂μ :=
        integral_rpow_split hfr.isBoundedRMF y hx hq0 hq1 N
    _ ≤ (CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
            * (1 + (N : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))) ^ q
          + (Cs / π) ^ q * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ :=
        add_le_add (integral_rpow_sum_small_le hR hCR hfr hy hx hq0 hq1 hsmallsub
          (fun m hm => ⟨(rough_mem_facts (P := fun m => IsRough y m ∧ m ≤ N) hx hm).1,
            hsmall2 m hm⟩) hβ0 hβ1) hlarge

/-! ### Step (j6): the parameter choice

`T = x^{3/4}`, so `N = ⌊T⌋` and the fibre index runs over `r ≤ R = ⌊x^{1/4}⌋`.  Writing
`s = x^{1/4}`, so that `x = s⁴` and `√x = s²`, the sieve conditions become polynomial
inequalities in `s`:

* `x/(r+1) ≥ s⁴/(s+1) ≥ 2`  ⇐  `s⁴ ≥ 2s + 2`;
* `H_r = x/(r(r+1)) ≥ s³/(s+1) ≥ 2`  ⇐  `s³ ≥ 2s + 2`;
* `H_r ≥ y`, since `y ≤ √x/2 = s²/2` and `s³/(s+1) ≥ s²/2 ⇔ s³ ≥ s²`;
* `5y(1+log y)³ log y ≤ H_r`, since the left side is at most `√x/2 ≤ H_r`.

All hold for `s ≥ 2`, i.e. `x ≥ 16`; we ask `x ≥ 64` so that `2y ≤ √x` with `y ≥ 2` is
consistent.  The third is where `2y ≤ √x` is used. -/
lemma sieve_conditions {x y : ℝ} (hx : 64 ≤ x) (hy2 : 2 ≤ y) (hyx : 2 * y ≤ Real.sqrt x)
    (habs : 5 * y * (1 + Real.log y) ^ 3 * Real.log y ≤ Real.sqrt x / 2)
    {r : ℕ} (hr1 : 1 ≤ r) (hrs : (r : ℝ) ≤ x ^ (1 / 4 : ℝ)) :
    2 ≤ x / ((r : ℝ) + 1) ∧ 2 ≤ x / r - x / ((r : ℝ) + 1)
      ∧ y ≤ x / r - x / ((r : ℝ) + 1)
      ∧ 5 * y * (1 + Real.log y) ^ 3 * Real.log y ≤ x / r - x / ((r : ℝ) + 1) := by
  have hx0 : (0 : ℝ) < x := by linarith
  set s : ℝ := x ^ (1 / 4 : ℝ) with hsdef
  have hs0 : (0 : ℝ) < s := Real.rpow_pos_of_pos hx0 _
  have hs4 : s ^ 4 = x := by
    rw [hsdef, ← Real.rpow_natCast (x ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul hx0.le]
    norm_num
  have hs2 : s ^ 2 = Real.sqrt x := by
    rw [← hs4, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sqrt_sq (by positivity)]
  have hsge : (2 : ℝ) ≤ s := by nlinarith [hs4, hs0, hx]
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hr1pos : (0 : ℝ) < (r : ℝ) + 1 := by linarith
  have hdiff : x / r - x / ((r : ℝ) + 1) = x / ((r : ℝ) * ((r : ℝ) + 1)) := by
    field_simp
    ring
  have hys2 : y ≤ s ^ 2 / 2 := by
    rw [hs2]
    linarith
  have hrs1 : (r : ℝ) + 1 ≤ s + 1 := by linarith
  have hprod : (r : ℝ) * ((r : ℝ) + 1) ≤ s * (s + 1) :=
    mul_le_mul hrs hrs1 (by linarith) (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hr1pos, ← hs4]
    nlinarith [hrs1, hsge, hs0]
  · rw [hdiff, le_div_iff₀ (by positivity), ← hs4]
    nlinarith [hprod, hsge, hs0]
  · rw [hdiff, le_div_iff₀ (by positivity), ← hs4]
    have h1 : y * ((r : ℝ) * ((r : ℝ) + 1)) ≤ s ^ 2 / 2 * (s * (s + 1)) :=
      mul_le_mul hys2 hprod (by positivity) (by positivity)
    nlinarith [h1, hsge, hs0]
  · refine le_trans habs ?_
    rw [hdiff, le_div_iff₀ (by positivity)]
    have h1 : Real.sqrt x / 2 * ((r : ℝ) * ((r : ℝ) + 1)) ≤ s ^ 2 / 2 * (s * (s + 1)) :=
      mul_le_mul (le_of_eq (by rw [hs2])) hprod (by positivity) (by positivity)
    nlinarith [h1, hsge, hs0, hs4]

/-! ### Step (j7): the split point

`T = x^{3/4}`, `N = ⌊T⌋`, `R = ⌊x^{1/4}⌋`.  The only facts needed are `x^{3/4}·x^{1/4} = x` and
`x^{1/4} ≥ 2` for `x ≥ 16`. -/

lemma rpow_three_quarter_mul_quarter {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x := by
  rw [← Real.rpow_add' hx (by norm_num)]
  norm_num

lemma two_le_rpow_quarter {x : ℝ} (hx : 16 ≤ x) : 2 ≤ x ^ (1 / 4 : ℝ) := by
  have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 4,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  calc (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := h16.symm
    _ ≤ x ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by norm_num) hx (by norm_num)

/-- On the small range `m ≤ ⌊x^{3/4}⌋`, the argument `x/m` is at least `x^{1/4} ≥ 2`, which is
what Rankin needs. -/
lemma two_le_div_of_le_split {x : ℝ} (hx : 16 ≤ x) {m : ℕ} (hm0 : 0 < m)
    (hm : m ≤ ⌊x ^ (3 / 4 : ℝ)⌋₊) : 2 ≤ x / m := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hq0 : (0 : ℝ) < x ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmle : (m : ℝ) ≤ x ^ (3 / 4 : ℝ) :=
    le_trans (by exact_mod_cast hm) (Nat.floor_le hq0.le)
  rw [le_div_iff₀ hmR]
  calc (2 : ℝ) * m ≤ x ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) := by
        exact mul_le_mul (two_le_rpow_quarter hx) hmle hmR.le (by positivity)
    _ = x := by rw [mul_comm, rpow_three_quarter_mul_quarter hx0.le]

/-- On the large range `m > ⌊x^{3/4}⌋`, the fibre index `⌊x/m⌋` lands in `[1, ⌊x^{1/4}⌋]`. -/
lemma floor_div_mem_of_split {x : ℝ} (hx : 16 ≤ x) {m : ℕ} (hm0 : 0 < m)
    (hmx : 1 ≤ x / m) (hm : ¬ m ≤ ⌊x ^ (3 / 4 : ℝ)⌋₊) :
    ⌊x / (m : ℝ)⌋₊ ∈ Finset.Icc 1 ⌊x ^ (1 / 4 : ℝ)⌋₊ := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hq0 : (0 : ℝ) < x ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  rw [Finset.mem_Icc]
  refine ⟨Nat.le_floor (by exact_mod_cast hmx), ?_⟩
  -- `m > ⌊x^{3/4}⌋` gives `m > x^{3/4}`, hence `x/m < x^{1/4}`
  have hgt : x ^ (3 / 4 : ℝ) < m := by
    have := Nat.lt_floor_add_one (x ^ (3 / 4 : ℝ))
    have hle : ⌊x ^ (3 / 4 : ℝ)⌋₊ + 1 ≤ m := by omega
    calc x ^ (3 / 4 : ℝ) < (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) + 1 := this
      _ ≤ (m : ℝ) := by exact_mod_cast hle
  have hdiv : x / m ≤ x ^ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ hmR]
    calc x = x ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) := by
          rw [mul_comm, rpow_three_quarter_mul_quarter hx0.le]
      _ ≤ x ^ (1 / 4 : ℝ) * m := by
          exact mul_le_mul_of_nonneg_left hgt.le (by positivity)
  exact Nat.floor_le_floor hdiv

/-! ### Step (j8): folding the Rankin term

`CR (log y)^A e^{-cR L}(1 + N^β/β) ≤ (CR + CR/cR)(log y)^{A+1} e^{-(cR/4)L}`,
with `L = log x/log y`, `β = cR/log y`, `N = ⌊x^{3/4}⌋`.

This is where Gorodetsky–Wong's `K = A + 1` and their quarter come from.  Expanding,

* the `1` contributes `CR (log y)^A e^{-cR L}`;
* the `N^β/β` contributes `(CR/cR)(log y)^{A+1} e^{-cR L + (3cR/4)L}`,
  which is `(CR/cR)(log y)^{A+1} e^{-(cR/4)L}`,

because `N^β ≤ (x^{3/4})^β = e^{(3cR/4)L}` and `1/β = (log y)/cR`.  The second dominates: the
extra `log y` is the one Gorodetsky–Wong carry, and the `e^{-cR L}` of the first is smaller than
`e^{-(cR/4)L}`. -/
lemma rankin_term_le {A cR CR : ℝ} (hcR : 0 < cR) (hCR : 0 < CR)
    {x : ℝ} (hx : 16 ≤ x) {y : ℕ} (hy : Real.exp 1 ≤ (y : ℝ)) :
    CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
        * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))
      ≤ (CR + CR / cR) * Real.log y ^ (A + 1)
          * Real.exp (-(cR / 4) * Real.log x / Real.log y) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < (y : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hy
  have hLy : (1 : ℝ) ≤ Real.log y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hy
  have hLy0 : (0 : ℝ) < Real.log y := by linarith
  have hLy0' : Real.log y ≠ 0 := hLy0.ne'
  have hcR' : cR ≠ 0 := hcR.ne'
  have hlx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hβ : (0 : ℝ) < cR / Real.log y := by positivity
  have hq0 : (0 : ℝ) < x ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hexp : Real.exp (-cR * Real.log x / Real.log y)
      * Real.exp (3 * cR / 4 * (Real.log x / Real.log y))
      = Real.exp (-(cR / 4) * Real.log x / Real.log y) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hNle : ((⌊x ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) ^ (cR / Real.log y)
      ≤ Real.exp (3 * cR / 4 * (Real.log x / Real.log y)) := by
    calc ((⌊x ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) ^ (cR / Real.log y)
        ≤ (x ^ (3 / 4 : ℝ)) ^ (cR / Real.log y) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hq0.le) hβ.le
      _ = Real.exp (3 * cR / 4 * (Real.log x / Real.log y)) := by
          rw [← Real.rpow_mul hx0.le, Real.rpow_def_of_pos hx0]
          congr 1
          field_simp
  have hmono : Real.exp (-cR * Real.log x / Real.log y)
      ≤ Real.exp (-(cR / 4) * Real.log x / Real.log y) := by
    refine Real.exp_le_exp.2 ?_
    rw [div_le_div_iff₀ hLy0 hLy0]
    nlinarith [mul_pos hlx hLy0, hcR]
  have hpow : Real.log y ^ A ≤ Real.log y ^ (A + 1) :=
    Real.rpow_le_rpow_of_exponent_le hLy (by linarith)
  have hApos : (0 : ℝ) < Real.log y ^ A := Real.rpow_pos_of_pos hLy0 _
  rw [mul_add, mul_one]
  have hterm1 : CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
      ≤ CR * Real.log y ^ (A + 1) * Real.exp (-(cR / 4) * Real.log x / Real.log y) := by
    gcongr
  have hterm2 : CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
        * (((⌊x ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))
      ≤ CR / cR * Real.log y ^ (A + 1)
          * Real.exp (-(cR / 4) * Real.log x / Real.log y) := by
    have hstep : CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
          * (((⌊x ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))
        ≤ CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
          * (Real.exp (3 * cR / 4 * (Real.log x / Real.log y)) / (cR / Real.log y)) := by
      gcongr
    refine hstep.trans (le_of_eq ?_)
    rw [Real.rpow_add hLy0, Real.rpow_one, ← hexp]
    field_simp
  linarith

/-- **The reduction to moments of integrals of Euler products** (Gorodetsky–Wong, Lemma 1.2), for
a law `P` satisfying the core estimate `Hcore` (`RMF.reduction_core` for the Steinhaus law): for
`y ≥ y₀` with `5y(1 + log y)³ log y ≤ √x/2` and `q ∈ [0,1]`,

`E|S_x|^{2q} ≤ C E[((1/log y) ∫_ℝ |A_y(1/2+it)/(1/2+it)|² dt)^q]`
`  + C ((log y)^K e^{-c log x/log y})^q`,

with `C`, `K`, `c`, `y₀` independent of `f`, `μ`, `x`, `y`, `q`.  `K = A + 1` for Rankin's exponent
`A`, and `c` is a quarter of Rankin's constant, from `log(x/T) = (1/4) log x` at `T = x^{3/4}`.

Gorodetsky–Wong ask for `y ∈ [2, √x]`.  The condition on `y` here absorbs the error term of
`RMF.exists_roughCount_sub_le` and implies `2y ≤ √x`, whose factor `2` covers the last fibre, where
`H_r` falls just below `√x`.  `y ≥ y₀` makes `β = c/log y ≤ 1` in `RMF.sum_rpow_sub_one_le`.  At
`log y = log x/(log log x)²` both hold for large `x`, and the error term is `o((log log x)^{-q/2})`
uniformly on `q ≥ 2/3`. -/
theorem reduction_upper_of_core {P : (Ω → ArithmeticFunction ℂ) → Measure Ω → Prop}
    (Hcore :
  ∀ {A cR CR Cs : ℝ}
      (_ : ∀ (y : ℕ) (x : ℝ), 2 ≤ y → 2 ≤ x →
        (smoothCount y x : ℝ)
          ≤ CR * x * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y))
      (_ : 0 ≤ CR)
      (_ : ∀ (y : ℕ) (x H : ℝ), 2 ≤ y → 0 < x → 0 < H → (y : ℝ) ≤ H →
        5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ H →
        (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ) ≤ Cs * H / Real.log y)
      (_ : 0 ≤ Cs)
      {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (_ : P f μ)
      {y : ℕ} (_ : 2 ≤ y) {x q : ℝ} (_ : 1 ≤ x) (_ : 0 ≤ q) (_ : q ≤ 1) {N R : ℕ}
      (_ : ∀ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N}, 2 ≤ x / m)
      (_ : {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N} ⊆ Finset.Icc 1 N)
      (_ : ∀ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
        ⌊x / (m : ℝ)⌋₊ ∈ Finset.Icc 1 R)
      (_ : ∀ r ∈ Finset.Icc 1 R, 2 ≤ x / ((r : ℝ) + 1) ∧
        2 ≤ x / r - x / ((r : ℝ) + 1) ∧ (y : ℝ) ≤ x / r - x / ((r : ℝ) + 1) ∧
        5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ x / r - x / ((r : ℝ) + 1))
      (_ : ∀ r ∈ Finset.Icc 1 R,
        {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N}.filter
            (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)
          ⊆ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r})
      (_ : 0 < cR / Real.log y) (_ : cR / Real.log y ≤ 1),
      ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
        ≤ (CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
              * (1 + (N : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))) ^ q
          + (Cs / π) ^ q * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ) :
    ∃ (C K c : ℝ) (y₀ : ℕ), 0 < C ∧ 0 ≤ K ∧ 0 < c ∧ 2 ≤ y₀ ∧
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ →
        ∀ (x : ℝ) (y : ℕ) (q : ℝ), y₀ ≤ y →
          5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ Real.sqrt x / 2 → 0 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ C * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ
              + C * (Real.log y ^ K * Real.exp (-c * Real.log x / Real.log y)) ^ q := by
  obtain ⟨A, cR, CR, hA, hcR, hCR, hRank⟩ := exists_smoothCount_le
  obtain ⟨Cs, hCs, hSieve⟩ := exists_roughCount_sub_le
  refine ⟨max 1 (max (CR + CR / cR) (Cs / π)), A + 1, cR / 4, max 4 ⌈Real.exp cR⌉₊,
    lt_of_lt_of_le one_pos (le_max_left _ _), by linarith, by positivity,
    le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro f μ hf x y q hy0 habs hq0 hq1
  have hy4 : 4 ≤ y := le_trans (le_max_left _ _) hy0
  have hyR : (4 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy4
  have hy2N : 2 ≤ y := by omega
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by linarith
  have hexp1 : Real.exp 1 ≤ (y : ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  have hLy1 : (1 : ℝ) ≤ Real.log y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) hexp1
  -- `5y(1+log y)³ log y ≤ √x/2` is strictly stronger than Gorodetsky–Wong's `2y ≤ √x`:
  -- the extra factor is `≥ 8` once `log y ≥ 1`, which `y ≥ 4` supplies.
  have hcube : (8 : ℝ) ≤ (1 + Real.log y) ^ 3 * Real.log y := by
    have h2 : (2 : ℝ) ≤ 1 + Real.log y := by linarith
    have h := mul_le_mul (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 3) hLy1
      (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ (1 + Real.log y) ^ 3)
    norm_num at h
    linarith
  have hyx : 2 * (y : ℝ) ≤ Real.sqrt x := by
    have h := mul_le_mul_of_nonneg_left hcube (show (0 : ℝ) ≤ 5 * (y : ℝ) by linarith)
    linarith [habs, h]
  have hexpc : Real.exp cR ≤ (y : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right 4 _) hy0)
  have hLy : cR ≤ Real.log y := by
    rw [← Real.log_exp cR]
    exact Real.log_le_log (Real.exp_pos _) hexpc
  have hLy0 : (0 : ℝ) < Real.log y := lt_of_lt_of_le hcR hLy
  have hx64 : (64 : ℝ) ≤ x := by
    have h8 : (8 : ℝ) ≤ Real.sqrt x := by linarith
    have hx0 : (0 : ℝ) ≤ x := by
      by_contra hneg
      push Not at hneg
      rw [Real.sqrt_eq_zero_of_nonpos hneg.le] at h8
      linarith
    nlinarith [Real.sq_sqrt hx0, Real.sqrt_nonneg x]
  have hx16 : (16 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hβ0 : (0 : ℝ) < cR / Real.log y := by positivity
  have hβ1 : cR / Real.log y ≤ 1 := (div_le_one hLy0).2 hLy
  have hcore := Hcore hRank hCR.le hSieve hCs.le hf hy2N hx1 hq0 hq1
    (N := ⌊x ^ (3 / 4 : ℝ)⌋₊) (R := ⌊x ^ (1 / 4 : ℝ)⌋₊)
    (fun m hm => two_le_div_of_le_split hx16
      (rough_mem_facts (P := fun m => IsRough y m ∧ m ≤ ⌊x ^ (3 / 4 : ℝ)⌋₊) hx1 hm).1
      (by rw [Finset.mem_filter] at hm; exact hm.2.2))
    (by
      intro m hm
      rw [Finset.mem_filter, Finset.mem_Icc] at hm
      rw [Finset.mem_Icc]
      exact ⟨hm.1.1, hm.2.2⟩)
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
    hβ0 hβ1
  -- fold the Rankin term, then absorb both constants
  set Z : ℝ := Real.log y ^ (A + 1) * Real.exp (-(cR / 4) * Real.log x / Real.log y) with hZ
  have hZ0 : (0 : ℝ) < Z := by
    rw [hZ]
    exact mul_pos (Real.rpow_pos_of_pos hLy0 _) (Real.exp_pos _)
  have hRT0 : (0 : ℝ) ≤ CR * Real.log y ^ A
      * Real.exp (-cR * Real.log x / Real.log y)
      * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (cR / Real.log y) / (cR / Real.log y)) := by
    have h1 : (0 : ℝ) < Real.log y ^ A := Real.rpow_pos_of_pos hLy0 _
    have h2 : (0 : ℝ) ≤ (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (cR / Real.log y) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  have hEint : (0 : ℝ) ≤ ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (eulerLineIntegral_nonneg hy2 ω) _
  have hsmallq : (CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
      * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))) ^ q
      ≤ max 1 (max (CR + CR / cR) (Cs / π)) * Z ^ q := by
    have hrk := rankin_term_le (A := A) hcR hCR hx16 (y := y) hexp1
    calc _ ≤ ((CR + CR / cR) * Z) ^ q := by
          refine Real.rpow_le_rpow hRT0 ?_ hq0
          rw [hZ]
          linarith [hrk]
      _ = (CR + CR / cR) ^ q * Z ^ q := Real.mul_rpow (by positivity) hZ0.le
      _ ≤ max 1 (max (CR + CR / cR) (Cs / π)) * Z ^ q := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hZ0.le _)
          exact le_trans (rpow_le_max_one (by positivity) hq0 hq1)
            (max_le_max_left 1 (le_max_left _ _))
  have hlargeq : (Cs / π) ^ q * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ
      ≤ max 1 (max (CR + CR / cR) (Cs / π)) * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ := by
    refine mul_le_mul_of_nonneg_right ?_ hEint
    exact le_trans (rpow_le_max_one (by positivity) hq0 hq1)
      (max_le_max_left 1 (le_max_right _ _))
  linarith

end RMF
