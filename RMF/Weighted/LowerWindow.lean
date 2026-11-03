/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.LowerKhintchine
import RMF.Reduction.LowerAssembly

/-!
# The weighted sum's lower bound, steps L4–L9: from the prime mean square to `∫|S(z)|² dz/z`

After `RMF.khintchine_rough_weighted` the lower bound needs `E[(∑_{√x<p≤x} p^{-1}|S(x/p)|²)^q]`
from below.  The unweighted reduction (`RMF/Reduction/LowerAssembly.lean`) turns
`∑_p |∑_{m≤x/p} f(m)|²` into `x∫|∑_{m≤z}f(m)|² dz/z²`; the same steps turn the weighted sum into

`(8 log x)^{-1} ∫_1^{√x/(1+1/log x)} |S(z)|² dz/z`   (`RMF.weightedMeanSquare`),

less a smoothing error of expected size `16/log x` (`RMF.meanSquare_le_sum_weighted`).  The steps
are L4, `log p ≤ log x`; L5, the smoothing; L7, the smoothing error; L8, the prime windows; and L9,
the passage to `q`-th moments.

## What changes against the unweighted steps

* **L5, the smoothing, is verbatim**: `RMF.smoothing_bound` holds for any arithmetic function,
  and `S(z)` is the partial sum of `RMF.weightedExt`.
* **L8, the windows, needs the extra `1/p`.**  On the window `(p, p(1+1/X)]` one has `1/p ≥ 1/t`,
  so the weighted window sum dominates the unweighted one for the integrand `|S(x/t)|²/t`, and
  `RMF.half_setIntegral_le_window_sumOf` applies to that integrand.  The substitution `z = x/t`
  then turns `dt/t` into `dz/z`.
* **L7, the smoothing error, is where the weight earns its keep.**  The unweighted bound counts
  the integers of `(x/t, x/p]`, about `x/(pX)`; weighted, each carries `1/m ≤ t/x`, so a window's
  discrepancy has mean at most `(1+1/X)(1/X + p/x)` (`RMF.integral_discrepancy_le_weighted`), and
  summed against `log p/p` it is `O(1)` at `X = log x`: an `O(1/log x)` error once L4's `1/log x`
  is paid.

## No sliver

The unweighted chain restores the range `(√x/(1+1/X), √x]` that the windows miss, at the cost of
`RMF.sliverIntegral`.  Here the range is left where the windows put it: the Parseval step writes
`∫_1^{√x/(1+1/X)} = ∫_1^∞ - ∫_{√x/(1+1/X)}^∞`, and the tail is what the damped Euler-product term
of Gerspach's Proposition 6 (Gerspach, arXiv:1909.10224) absorbs.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The weighted mean square -/

/-- `∫_1^{√x/(1+1/log x)} |S(z)|² dz/z`: the quantity the weighted lower bound reduces to. -/
noncomputable def weightedMeanSquare (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) : ℝ :=
  ∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)), ‖weightedRademacherSum f z ω‖ ^ 2 / z

omit [MeasurableSpace Ω] in
lemma weightedMeanSquare_nonneg (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) :
    0 ≤ weightedMeanSquare f x ω :=
  setIntegral_nonneg measurableSet_Ioc fun z hz =>
    div_nonneg (by positivity) (lt_trans one_pos hz.1).le

/-! ### The mean square over an interval -/

/-- **The weighted block's mean square.**  `E‖S(b) - S(a)‖² ≤ (⌊b⌋ - ⌊a⌋)/(⌊a⌋+1)`: each
surviving term is `1/m` with `m > ⌊a⌋`. -/
theorem integral_normSq_weightedSum_sub_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {a b : ℝ} (hab : a ≤ b) :
    (∫ ω, ‖randomSum (fun ω => weightedExt fun p => X p ω) b ω
        - randomSum (fun ω => weightedExt fun p => X p ω) a ω‖ ^ 2 ∂μ)
      ≤ ((⌊b⌋₊ : ℝ) - ⌊a⌋₊) / (⌊a⌋₊ + 1) := by
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have hcongr : (∫ ω, ‖randomSum (fun ω => weightedExt fun p => X p ω) b ω
        - randomSum (fun ω => weightedExt fun p => X p ω) a ω‖ ^ 2 ∂μ)
      = ∫ ω, ‖∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, weightedExt (fun p => X p ω) n‖ ^ 2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only
      rw [randomSum_sub_eq _ hab ω])
  have hne : ∀ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, n ≠ 0 := fun n hn => by
    have := (Finset.mem_Ioc.1 hn).1
    omega
  rw [hcongr, integral_normSq_sum_weightedExt hX hne]
  have hd : (0 : ℝ) < (⌊a⌋₊ : ℝ) + 1 := by positivity
  calc ∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (if Squarefree m then (m : ℝ)⁻¹ else 0)
      ≤ ∑ _m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ((⌊a⌋₊ : ℝ) + 1)⁻¹ := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : ⌊a⌋₊ + 1 ≤ m := (Finset.mem_Ioc.1 hm).1
        have hmR : (⌊a⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast hm1
        split_ifs
        · exact inv_anti₀ hd hmR
        · exact inv_nonneg.2 hd.le
    _ = ((⌊b⌋₊ : ℝ) - ⌊a⌋₊) / (⌊a⌋₊ + 1) := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, div_eq_mul_inv]
        push_cast [hfl]
        ring

/-! ### Step L7: the smoothing error -/

/-- **Step L7 for the weighted sum, one prime at a time.**  The expected discrepancy over the
window `(p, p(1+1/Y)]` is at most `(1+1/Y)(1/Y + p/x)`.

The unweighted `RMF.integral_discrepancy_le` counts the integers of `(x/t, x/p]`, which here
would cost `x/(pY)`; the weight `1/m ≤ t/x` on that range is what brings it down. -/
theorem integral_discrepancy_le_weighted {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {x Y p : ℝ} (hx : 0 < x)
    (hY : 0 < Y) (hp : 0 < p) :
    (∫ ω, Y / p * (∫ t in Set.Ioc p (p * (1 + 1 / Y)),
        discrepancy (fun ω => weightedExt fun q => X q ω) x p ω t) ∂μ)
      ≤ (1 + 1 / Y) * (1 / Y + p / x) := by
  set g : Ω → ArithmeticFunction ℂ := fun ω => weightedExt fun q => X q ω with hgdef
  have hg : IsBoundedRMF g μ := isBoundedRMF_weightedExt hX
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc p (p * (1 + 1 / Y)))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hInt := integrable_discrepancy (X := Y) hg hx.le hp
  rw [integral_const_mul, integral_integral_swap hInt]
  have hbound : ∀ t ∈ Set.Ioc p (p * (1 + 1 / Y)),
      (∫ ω, discrepancy g x p ω t ∂μ) ≤ (1 + 1 / Y) * (1 / Y + p / x) := by
    intro t ht
    have hpt : p ≤ t := ht.1.le
    have ht0 : 0 < t := lt_of_lt_of_le hp hpt
    have hdiv : x / t ≤ x / p := by gcongr
    have hle : (∫ ω, discrepancy g x p ω t ∂μ)
        ≤ ∫ ω, ‖randomSum g (x / p) ω - randomSum g (x / t) ω‖ ^ 2 ∂μ :=
      integral_mono_ae (integrable_discrepancy_slice hg hx.le hp hpt)
        (integrable_normSq_randomSum_sub hg hdiv)
        (Filter.Eventually.of_forall fun ω => discrepancy_le_block g x p ω t)
    refine le_trans (le_trans hle (integral_normSq_weightedSum_sub_le hX hdiv)) ?_
    have hcount := floor_sub_floor_le hx.le hY hp hpt ht.2
    have hden : x / t < (⌊x / t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hxt : (0 : ℝ) < x / t := by positivity
    calc ((⌊x / p⌋₊ : ℝ) - ⌊x / t⌋₊) / (⌊x / t⌋₊ + 1)
        ≤ (x / (p * Y) + 1) / (x / t) :=
          div_le_div₀ (by positivity) hcount hxt hden.le
      _ = (x / (p * Y) + 1) * t / x := by field_simp
      _ ≤ (x / (p * Y) + 1) * (p * (1 + 1 / Y)) / x := by
          gcongr
          exact ht.2
      _ = (1 + 1 / Y) * (1 / Y + p / x) := by field_simp
  have hconst : Y / p * ∫ _t in Set.Ioc p (p * (1 + 1 / Y)), (1 + 1 / Y) * (1 / Y + p / x)
      = (1 + 1 / Y) * (1 / Y + p / x) := setIntegral_const_window hp hY
  rw [← hconst]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact setIntegral_mono_on hInt.integral_prod_right (integrableOn_const (by simp))
    measurableSet_Ioc hbound

/-- The weighted discrepancy sum is integrable, prime by prime. -/
lemma integrable_weightedDiscrepancySum {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsRademacherPrimeValues X μ) {x Y : ℝ} (hx : 0 ≤ x) {S : Finset ℕ}
    (hSp : ∀ p ∈ S, Nat.Prime p) :
    Integrable (fun ω => ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Y / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Y)),
        discrepancy (fun ω => weightedExt fun q => X q ω) x p ω t))) μ :=
  integrable_finsetSum _ fun p hp =>
    ((((integrable_discrepancy (X := Y) (isBoundedRMF_weightedExt hX) hx
      (by exact_mod_cast (hSp p hp).pos)).integral_prod_left).const_mul _).const_mul
        _).const_mul _

/-- **Step L7 for the weighted sum, summed.**  At `Y = log x`, for `x ≥ e` and any set of primes
up to `x`, the expected total discrepancy is at most `16`. -/
theorem integral_sum_discrepancy_le_weighted {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : Real.exp 1 ≤ x)
    {S : Finset ℕ} (hS : S ⊆ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime}) :
    (∫ ω, ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
        discrepancy (fun ω => weightedExt fun q => X q ω) x p ω t)) ∂μ) ≤ 16 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact hx
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hSp : ∀ p ∈ S, Nat.Prime p := fun p hp => (Finset.mem_filter.1 (hS hp)).2
  have hpos : ∀ p ∈ S, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hSp p hp).pos
  rw [integral_finsetSum]
  swap
  · intro p hp
    exact (((integrable_discrepancy (X := Real.log x) (isBoundedRMF_weightedExt hX) hx0.le
      (hpos p hp)).integral_prod_left.const_mul _).const_mul _).const_mul _
  have hper : ∀ p ∈ S, (∫ ω, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
        discrepancy (fun ω => weightedExt fun q => X q ω) x p ω t)) ∂μ)
      ≤ (1 + 1 / Real.log x)
          * ((Real.log x)⁻¹ * (Real.log p / p) + x⁻¹ * Real.log p) := by
    intro p hp
    have hp0 := hpos p hp
    rw [integral_const_mul, integral_const_mul]
    have h := integral_discrepancy_le_weighted hX hx0 hlog0 hp0
    have hlp : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
    calc Real.log p * ((p : ℝ)⁻¹ * ∫ ω, Real.log x / p * (∫ t in Set.Ioc (p : ℝ)
          ((p : ℝ) * (1 + 1 / Real.log x)),
            discrepancy (fun ω => weightedExt fun q => X q ω) x p ω t) ∂μ)
        ≤ Real.log p * ((p : ℝ)⁻¹ * ((1 + 1 / Real.log x) * (1 / Real.log x + p / x))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (by positivity)) hlp
      _ = (1 + 1 / Real.log x)
          * ((Real.log x)⁻¹ * (Real.log p / p) + x⁻¹ * Real.log p) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hS1 : ∑ p ∈ S, Real.log p / p ≤ Real.log x + Real.log 4 + 4 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hS fun p _ _ => log_div_natCast_nonneg p)
      (sum_log_div_prime_le hx1)
  have hS2 : ∑ p ∈ S, Real.log p ≤ Real.log 4 * x :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hS fun p _ _ =>
      Real.log_natCast_nonneg p) (sum_log_prime_le hx0.le)
  have hl4 : Real.log 4 < 1.4 := log_four_lt
  have hl40 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hr : 1 + 1 / Real.log x ≤ 2 := by
    have : 1 / Real.log x ≤ 1 := by rw [div_le_one hlog0]; exact hlog1
    linarith
  have hr0 : (0 : ℝ) ≤ 1 + 1 / Real.log x := by positivity
  have hA : (Real.log x)⁻¹ * ∑ p ∈ S, Real.log p / p ≤ 1 + (Real.log 4 + 4) := by
    rw [inv_mul_le_iff₀ hlog0]
    nlinarith
  have hB : x⁻¹ * ∑ p ∈ S, Real.log p ≤ Real.log 4 := by
    rw [inv_mul_le_iff₀ hx0]
    linarith
  have hsum0 : (0 : ℝ) ≤ (Real.log x)⁻¹ * ∑ p ∈ S, Real.log p / p + x⁻¹ * ∑ p ∈ S, Real.log p :=
    add_nonneg (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun p _ => log_div_natCast_nonneg p))
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p))
  nlinarith

/-! ### Steps L4, L5, L8, pointwise -/

omit [MeasurableSpace Ω] in
/-- `t ↦ ‖S(x/t)‖²/|t|` is integrable on any interval above `1`.  The absolute value makes the
integrand nonnegative everywhere, which `RMF.half_setIntegral_le_window_sumOf` asks for; on every
range where it is integrated `t > 0`, and it is `‖S(x/t)‖²/t`. -/
lemma integrableOn_normSq_randomSum_div_abs (g : Ω → ArithmeticFunction ℂ) {x c d : ℝ}
    (hx : 0 ≤ x) (hc : 1 ≤ c) (ω : Ω) :
    IntegrableOn (fun t => ‖randomSum g (x / t) ω‖ ^ 2 / |t|) (Set.Ioc c d) := by
  refine Measure.integrableOn_of_bounded (M := (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖g ω n‖) ^ 2)
    measure_Ioc_lt_top.ne
    (((measurable_randomSum_div g x ω).norm.pow_const 2).div
      measurable_id.abs).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht1 : (1 : ℝ) ≤ t := le_trans hc ht.1.le
  have hnum : ‖randomSum g (x / t) ω‖ ^ 2 ≤ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖g ω n‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_randomSum_div_le g hx ht1 ω) 2
  rw [abs_of_pos (by linarith : (0 : ℝ) < t), Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by positivity) (by linarith))]
  exact le_trans (div_le_self (by positivity) ht1) hnum

omit [MeasurableSpace Ω] in
/-- **The substitution `z = x/t`, for the measure `dt/t`:**
`∫_a^x ‖S(x/t)‖² dt/t = ∫_1^{x/a} ‖S(z)‖² dz/z`. -/
lemma setIntegral_div_eq_dz_div_z (g : Ω → ArithmeticFunction ℂ) {x a : ℝ} (hx : 0 < x)
    (ha : 0 < a) (hax : a ≤ x) (ω : Ω) :
    (∫ t in Set.Ioc a x, ‖randomSum g (x / t) ω‖ ^ 2 / t)
      = ∫ z in Set.Ioc 1 (x / a), ‖randomSum g z ω‖ ^ 2 / z := by
  have h := setIntegral_comp_div hx ha hax (fun z => ‖randomSum g z ω‖ ^ 2 * z / x)
  have e1 : (∫ t in Set.Ioc a x, ‖randomSum g (x / t) ω‖ ^ 2 / t)
      = ∫ t in Set.Ioc a x, ‖randomSum g (x / t) ω‖ ^ 2 * (x / t) / x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · simp only
      field_simp
  have e2 : x * (∫ z in Set.Ioc (x / x) (x / a), ‖randomSum g z ω‖ ^ 2 * z / x / z ^ 2)
      = ∫ z in Set.Ioc 1 (x / a), ‖randomSum g z ω‖ ^ 2 / z := by
    rw [div_self hx.ne', ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · simp only
      field_simp
  rw [e1, h, e2]

omit [MeasurableSpace Ω] in
/-- **Steps L4, L5 and L8 for the weighted sum, pointwise.**  For `x ≥ x₀` (`x₀` independent of
`g` and `ω`) and `S` sandwiched between the primes of `(√x, x]` and the naturals up to `x`,
`(8 log x)^{-1} ∫_1^{√x/(1+1/log x)} ‖S(z)‖² dz/z - D/log x ≤ ∑_{p∈S} p^{-1}‖S(x/p)‖²`, with `D`
the discrepancy sum of step L7.  Stated for any arithmetic function `g`: nothing probabilistic
happens here. -/
theorem sum_normSq_ge_weighted :
    ∃ x₀ : ℝ, ∀ (g : Ω → ArithmeticFunction ℂ) (ω : Ω) (x : ℝ), x₀ ≤ x →
      ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) → (∀ p ∈ S, (p : ℝ) ≤ x) →
        (∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) →
        (8 * Real.log x)⁻¹ * (∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
              ‖randomSum g z ω‖ ^ 2 / z)
            - (∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
                ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
                  discrepancy g x p ω t))) / Real.log x
          ≤ ∑ p ∈ S, (p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2 := by
  obtain ⟨x₀, hL8⟩ := half_setIntegral_le_window_sumOf
  refine ⟨max x₀ 4, fun g ω x hx S hSp hSx hS => ?_⟩
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx4
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hr0 : (0 : ℝ) < 1 + 1 / Real.log x := by linarith
  have hpos : ∀ p ∈ S, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hSp p hp).pos
  have hp1 : ∀ p ∈ S, (1 : ℝ) ≤ p := fun p hp => by exact_mod_cast (hSp p hp).one_lt.le
  -- the four sums
  set V : ℝ := ∑ p ∈ S, (p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2 with hVdef
  set L : ℝ := ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2) with hLdef
  set Wsum : ℝ := ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
      ‖randomSum g (x / t) ω‖ ^ 2)) with hWdef
  set Dsum : ℝ := ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), discrepancy g x p ω t)) with hDdef
  set Gsum : ℝ := ∑ p ∈ S, Real.log p * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
      ‖randomSum g (x / t) ω‖ ^ 2 / |t|) with hGdef
  set M : ℝ := ∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
    ‖randomSum g z ω‖ ^ 2 / z with hMdef
  -- L4: `log p ≤ log x`
  have hL4 : L ≤ Real.log x * V :=
    sum_log_mul_le_log_mul_sum (x := x) (by linarith) hSx
      (v := fun p => (p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2) fun p => by positivity
  -- L5: smoothing, prime by prime, weighted by `log p / p`
  have hL5 : 1 / 4 * Wsum - Dsum ≤ L := by
    have hstep : ∀ p ∈ S, 1 / 4 * (Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
          ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
            ‖randomSum g (x / t) ω‖ ^ 2)))
        - Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
          ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), discrepancy g x p ω t))
        ≤ Real.log p * ((p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2) := by
      intro p hp
      have hb := smoothing_bound (f := g) hx0.le hlog0 (hpos p hp) ω
      have hw : (0 : ℝ) ≤ Real.log p * (p : ℝ)⁻¹ :=
        mul_nonneg (Real.log_natCast_nonneg p) (inv_nonneg.2 (hpos p hp).le)
      have := mul_le_mul_of_nonneg_left hb hw
      linarith [this]
    have hsum := Finset.sum_le_sum hstep
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    exact hsum
  -- L8: the extra `1/p` against `1/t`, then the covering
  have hGW : Gsum ≤ Wsum := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hp0 := hpos p hp
    have hIG := integrableOn_normSq_randomSum_div_abs g hx0.le (c := (p : ℝ))
      (d := (p : ℝ) * (1 + 1 / Real.log x)) (hp1 p hp) ω
    have hIA := (integrableOn_normSq_randomSum_div g hx0.le (c := (p : ℝ))
      (d := (p : ℝ) * (1 + 1 / Real.log x)) (hp1 p hp) ω).const_mul ((p : ℝ)⁻¹)
    have hmono : (∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
          ‖randomSum g (x / t) ω‖ ^ 2 / |t|)
        ≤ ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
          (p : ℝ)⁻¹ * ‖randomSum g (x / t) ω‖ ^ 2 := by
      refine setIntegral_mono_on hIG hIA measurableSet_Ioc fun t ht => ?_
      have ht0 : (0 : ℝ) < t := lt_trans hp0 ht.1
      rw [abs_of_pos ht0, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hp0 ht.1.le) (by positivity)
    rw [integral_const_mul] at hmono
    have hlp : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
    have hcoef : (0 : ℝ) ≤ Real.log x / p := by positivity
    calc Real.log p * (Real.log x / p * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
          ‖randomSum g (x / t) ω‖ ^ 2 / |t|)
        ≤ Real.log p * (Real.log x / p * ((p : ℝ)⁻¹ * ∫ t in Set.Ioc (p : ℝ)
          ((p : ℝ) * (1 + 1 / Real.log x)), ‖randomSum g (x / t) ω‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hcoef) hlp
      _ = Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p * ∫ t in Set.Ioc (p : ℝ)
          ((p : ℝ) * (1 + 1 / Real.log x)), ‖randomSum g (x / t) ω‖ ^ 2)) := by ring
  have hcover := hL8 x hxx₀ (fun t => ‖randomSum g (x / t) ω‖ ^ 2 / |t|)
    (fun t => by positivity)
    (fun c d hc => integrableOn_normSq_randomSum_div_abs g hx0.le hc ω) S hSp hS
  -- the substitution
  have hsq0 : (0 : ℝ) < Real.sqrt x := by linarith
  have ha0 : (0 : ℝ) < Real.sqrt x * (1 + 1 / Real.log x) := by positivity
  have hax : Real.sqrt x * (1 + 1 / Real.log x) ≤ x := by
    have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    nlinarith
  have hxa : x / (Real.sqrt x * (1 + 1 / Real.log x)) = Real.sqrt x / (1 + 1 / Real.log x) := by
    have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    field_simp
    nlinarith
  have habs : (∫ t in Set.Ioc (Real.sqrt x * (1 + 1 / Real.log x)) x,
        ‖randomSum g (x / t) ω‖ ^ 2 / |t|)
      = ∫ t in Set.Ioc (Real.sqrt x * (1 + 1 / Real.log x)) x,
        ‖randomSum g (x / t) ω‖ ^ 2 / t :=
    setIntegral_congr_fun measurableSet_Ioc fun t ht => by
      rw [abs_of_pos (lt_trans ha0 ht.1)]
  have hsub := setIntegral_div_eq_dz_div_z g hx0 ha0 hax ω
  rw [hxa] at hsub
  rw [habs, hsub] at hcover
  -- assemble: `M/8 ≤ Gsum/4 ≤ Wsum/4 ≤ L + Dsum ≤ log x · V + Dsum`
  have hkey : M / 8 - Dsum ≤ Real.log x * V := by linarith
  rw [show (8 * Real.log x)⁻¹ * M - Dsum / Real.log x = (M / 8 - Dsum) / Real.log x by
    field_simp]
  rw [div_le_iff₀ hlog0]
  linarith

/-! ### Step L9 for the weighted sum: the `q`-th moment -/

/-- `a^q - b^q ≤ c^q` whenever `a - b ≤ c`, for nonnegative `a, b, c` and `0 ≤ q ≤ 1`. -/
lemma rpow_sub_rpow_le_of_sub_le {a b c q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a - b ≤ c) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : a ^ q - b ^ q ≤ c ^ q := by
  rcases le_or_gt b a with hba | hab
  · exact le_trans (rpow_sub_le_sub_rpow hb hba hq0 hq1)
      (Real.rpow_le_rpow (by linarith) h hq0)
  · have : a ^ q ≤ b ^ q := Real.rpow_le_rpow ha hab.le hq0
    linarith [Real.rpow_nonneg hc q]

/-- The weighted mean-square integrand is bounded, hence product-integrable. -/
lemma integrable_weightedMeanSquare_prod {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (w : ℝ) :
    Integrable (Function.uncurry fun (ω : Ω) (z : ℝ) =>
        ‖randomSum (fun ω => weightedExt fun p => X p ω) z ω‖ ^ 2 / z)
      (μ.prod (volume.restrict (Set.Ioc 1 w))) := by
  have hg := isBoundedRMF_weightedExt hX
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (1 : ℝ) w)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hm : Measurable fun p : Ω × ℝ =>
      ‖randomSum (fun ω => weightedExt fun p => X p ω) p.2 p.1‖ ^ 2 / p.2 :=
    (((measurable_randomSum_uncurry hg).norm).pow_const 2).div measurable_snd
  refine integrableOn_univ.1 (Measure.integrableOn_of_bounded
    (M := (⌊w⌋₊ : ℝ) ^ 2) (measure_ne_top _ _) hm.aestronglyMeasurable ?_)
  rw [Measure.restrict_univ]
  refine (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).2 ?_
  filter_upwards [ae_norm_randomSum_le hg w] with ω hω
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
  have hz1 : (1 : ℝ) ≤ z := hz.1.le
  have hn := hω z hz.2
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) (by linarith))]
  exact le_trans (div_le_self (by positivity) hz1) (pow_le_pow_left₀ (norm_nonneg _) hn 2)

/-- **Steps L4–L9 for the weighted sum.**  For `x ≥ x₀` (`x₀` independent of `x`, `q` and the
family), `0 ≤ q ≤ 1` and `S` sandwiched between the primes of `(√x, x]` and the naturals up to `x`,
`(8 log x)^{-q} E[weightedMeanSquare^q] - (16/log x)^q ≤ E[(∑_{p∈S} p^{-1}|S(x/p)|²)^q]`. -/
theorem meanSquare_le_sum_weighted :
    ∃ x₀ : ℝ, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ x q : ℝ, x₀ ≤ x → 0 ≤ q → q ≤ 1 →
        ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) → (∀ p ∈ S, (p : ℝ) ≤ x) →
          (∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) →
          (8 * Real.log x)⁻¹ ^ q
                * ∫ ω, weightedMeanSquare (fun ω => squarefreeExtension fun r => X r ω) x ω
                    ^ q ∂μ
              - (16 / Real.log x) ^ q
            ≤ ∫ ω, (∑ p ∈ S, (p : ℝ)⁻¹ * ‖weightedRademacherSum
                (fun ω => squarefreeExtension fun r => X r ω) (x / p) ω‖ ^ 2) ^ q ∂μ := by
  obtain ⟨x₀, hchain⟩ := sum_normSq_ge_weighted (Ω := Ω)
  refine ⟨max x₀ 4, fun X μ hX x q hx hq0 hq1 S hSp hSx hS => ?_⟩
  haveI := hX.isProbabilityMeasure
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx4
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hxe : Real.exp 1 ≤ x := by nlinarith [Real.exp_one_lt_d9]
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun r => X r ω with hfdef
  set g : Ω → ArithmeticFunction ℂ := fun ω => weightedExt fun r => X r ω with hgdef
  have hg : IsBoundedRMF g μ := isBoundedRMF_weightedExt hX
  have hSsub : S ⊆ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime} := fun p hp =>
    Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨(hSp p hp).pos, Nat.le_floor (hSx p hp)⟩, hSp p hp⟩
  -- the three quantities, in terms of `g`
  set w : ℝ := Real.sqrt x / (1 + 1 / Real.log x) with hwdef
  set Mg : Ω → ℝ := fun ω => ∫ z in Set.Ioc 1 w, ‖randomSum g z ω‖ ^ 2 / z with hMgdef
  set D : Ω → ℝ := fun ω => ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), discrepancy g x p ω t))
    with hDdef
  set A : Ω → ℝ := fun ω => ∑ p ∈ S, (p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2 with hAdef
  have hMeq : ∀ ω, weightedMeanSquare f x ω = Mg ω := by
    intro ω
    simp only [weightedMeanSquare, hMgdef, hfdef, hgdef, hwdef, weightedRademacherSum_eq_randomSum]
  have hAeq : ∀ ω, (∑ p ∈ S, (p : ℝ)⁻¹ * ‖weightedRademacherSum f (x / p) ω‖ ^ 2) = A ω := by
    intro ω
    simp only [hAdef, hfdef, hgdef, weightedRademacherSum_eq_randomSum]
  -- nonnegativity
  have hM0 : ∀ ω, 0 ≤ Mg ω := fun ω => by
    rw [← hMeq]
    exact weightedMeanSquare_nonneg f x ω
  have hD0 : ∀ ω, 0 ≤ D ω := by
    intro ω
    refine Finset.sum_nonneg fun p hp => mul_nonneg (Real.log_natCast_nonneg p) ?_
    refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (mul_nonneg (by positivity) ?_)
    exact setIntegral_nonneg measurableSet_Ioc fun t _ => discrepancy_nonneg g x p ω t
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => Finset.sum_nonneg fun p _ => by positivity
  have hP0 : ∀ ω, 0 ≤ (8 * Real.log x)⁻¹ * Mg ω := fun ω =>
    mul_nonneg (by positivity) (hM0 ω)
  have hR0 : ∀ ω, 0 ≤ D ω / Real.log x := fun ω => div_nonneg (hD0 ω) hlog0.le
  -- integrability
  have hMi : Integrable Mg μ := (integrable_weightedMeanSquare_prod hX w).integral_prod_left
  have hDi : Integrable D μ := integrable_weightedDiscrepancySum hX hx0.le hSp
  have hAi : Integrable A μ :=
    integrable_finsetSum _ fun p _ => (integrable_normSq_randomSum hg (x / p)).const_mul _
  have hPi : Integrable (fun ω => (8 * Real.log x)⁻¹ * Mg ω) μ := hMi.const_mul _
  have hRi : Integrable (fun ω => D ω / Real.log x) μ := hDi.div_const _
  have hPq := integrable_rpow_of_integrable hPi (Filter.Eventually.of_forall hP0) hq0 hq1
  have hRq := integrable_rpow_of_integrable hRi (Filter.Eventually.of_forall hR0) hq0 hq1
  have hAq := integrable_rpow_of_integrable hAi (Filter.Eventually.of_forall hA0) hq0 hq1
  -- the pointwise inequality, at the `q`-th power
  have hpt : ∀ ω, ((8 * Real.log x)⁻¹ * Mg ω) ^ q - (D ω / Real.log x) ^ q ≤ A ω ^ q :=
    fun ω => rpow_sub_rpow_le_of_sub_le (hP0 ω) (hR0 ω) (hA0 ω)
      (hchain g ω x hxx₀ S hSp hSx hS) hq0 hq1
  have hmain : (∫ ω, ((8 * Real.log x)⁻¹ * Mg ω) ^ q ∂μ) - ∫ ω, (D ω / Real.log x) ^ q ∂μ
      ≤ ∫ ω, A ω ^ q ∂μ := by
    rw [← integral_sub hPq hRq]
    exact integral_mono (hPq.sub hRq) hAq hpt
  -- the two evaluations
  have hPval : (∫ ω, ((8 * Real.log x)⁻¹ * Mg ω) ^ q ∂μ)
      = (8 * Real.log x)⁻¹ ^ q * ∫ ω, Mg ω ^ q ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      Real.mul_rpow (by positivity) (hM0 ω))
  have hRval : (∫ ω, (D ω / Real.log x) ^ q ∂μ) ≤ (16 / Real.log x) ^ q := by
    refine le_trans (integral_rpow_le_rpow_integral hq0 hq1
      (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (hR0 ω)) hRi hRq) ?_
    refine Real.rpow_le_rpow (integral_nonneg hR0) ?_ hq0
    rw [integral_div]
    exact div_le_div_of_nonneg_right (integral_sum_discrepancy_le_weighted hX hxe hSsub)
      hlog0.le
  -- back to the weighted sums
  have hL : (∫ ω, weightedMeanSquare f x ω ^ q ∂μ) = ∫ ω, Mg ω ^ q ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hMeq ω])
  have hR : (∫ ω, (∑ p ∈ S, (p : ℝ)⁻¹ * ‖weightedRademacherSum f (x / p) ω‖ ^ 2) ^ q ∂μ)
      = ∫ ω, A ω ^ q ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hAeq ω])
  rw [hL, hR]
  rw [hPval] at hmain
  linarith

end RMF
