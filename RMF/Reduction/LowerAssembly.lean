/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ChaosFirstMoment
import RMF.Probability.ChaosMoment
import RMF.Reduction.Lower
import RMF.Reduction.WindowSum
import RMF.Reduction.RoughLinearForm

/-!
# Assembling the lower-bound reduction

The assembly of the mean-square half of Harper's Proposition 3.  Symmetrisation
(`RMF.integral_rough_leOf`), the Khintchine substitute (`RMF.khintchine_lower_indep`), smoothing
(`RMF.smoothing_bound`), concavity (`RMF.rpow_sub_le_sub_rpow`), the smoothing error
(`RMF.integral_sum_discrepancy_le_log`) and the main term (`RMF.half_meanSquare_le_window_sum`)
are threaded together here into

`E[(∑_{√x<p≤x} ‖∑_{m≤x/p} f(m)‖²)^q] ≥ c·x^q·E[meanSquare^q] - C·(x/log x)^q`,

which is Proposition 3's content once `E‖∑_{n≤x} f(n)‖^{2q}` has been reduced to the left-hand
side by symmetrisation and Khintchine.

## The three error terms

Reading the chain from the top, `∑_p ‖∑_{m≤x/p} f(m)‖²` loses

1. a factor `log x`, because `log p ≤ log x` — this is a *factor*, not an error;
2. the smoothing discrepancy `∑_p log p · (X/p)∫ min{…}`, of expected size `≤ 8x`;
3. the sliver `∫_{√x/(1+1/X)}^{√x}‖∑_{m≤z}f(m)‖² dz/z²` that the main term's range misses, of
   expected size `≤ 1/log x`.

Both errors are small only **in expectation** — pointwise the sliver's integrand is bounded by
`1` over an interval of length `√x/(log x+1)`, which is useless — so both are subtracted after
the `ω`-integral is formed, and Jensen (`RMF.integral_rpow_le_rpow_integral`) turns `E[(·)^q]`
into `(E ·)^q`.  `RMF.rpow_sub_three_le` is the pointwise inequality that lets two such terms be
peeled off at once.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### `log p ≤ log x`

`log p ≤ log x` for every prime `p ≤ x`.  The one genuinely trivial step of the chain. -/

omit [MeasurableSpace Ω] in
/-- **`log p ≤ log x`, summed**: `∑_{p∈S} log p · v p ≤ log x · ∑_{p∈S} v p` for nonnegative `v`
and `S` a set of naturals below `x`. -/
lemma sum_log_mul_le_log_mul_sum {x : ℝ} (hx : 1 ≤ x) {S : Finset ℕ}
    (hS : ∀ p ∈ S, (p : ℝ) ≤ x) {v : ℕ → ℝ} (hv : ∀ p, 0 ≤ v p) :
    ∑ p ∈ S, Real.log p * v p ≤ Real.log x * ∑ p ∈ S, v p := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  refine mul_le_mul_of_nonneg_right ?_ (hv p)
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simpa using Real.log_nonneg hx
  · exact Real.log_le_log (by exact_mod_cast hp0) (hS p hp)

/-! ### Peeling off two error terms

`RMF.rpow_sub_le_sub_rpow` handles one subtraction; the chain needs two, and the combined
quantity can go negative, which `Real.rpow` does not handle gracefully.  Subadditivity covers
that case separately. -/

/-- **Two subtractions at the `q`-th power.**  If `P - Q - R ≤ A` with all of `A, P, Q, R`
nonnegative, then `P^q - Q^q - R^q ≤ A^q` for `0 ≤ q ≤ 1`.

No hypothesis relates `P` to `Q + R`: when `P ≤ Q + R` the left side is already `≤ 0`, by
subadditivity of `t ↦ t^q`. -/
lemma rpow_sub_three_le {A P Q R q : ℝ} (hA : 0 ≤ A) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (hle : P - Q - R ≤ A) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    P ^ q - Q ^ q - R ^ q ≤ A ^ q := by
  have hsub := Real.rpow_add_le_add_rpow hQ hR hq0 hq1
  rcases le_or_gt P (Q + R) with h | h
  · have h1 : P ^ q ≤ (Q + R) ^ q := Real.rpow_le_rpow hP h hq0
    have h2 : (0 : ℝ) ≤ A ^ q := Real.rpow_nonneg hA q
    linarith
  · have hQR : (0 : ℝ) ≤ Q + R := by linarith
    have h1 : P ^ q - (Q + R) ^ q ≤ (P - (Q + R)) ^ q :=
      rpow_sub_le_sub_rpow hQR h.le hq0 hq1
    have h2 : (P - (Q + R)) ^ q ≤ A ^ q :=
      Real.rpow_le_rpow (by linarith) (by linarith) hq0
    linarith

/-! ### The smoothing bound, summed over the primes -/

omit [MeasurableSpace Ω] in
/-- **The smoothing bound, summed**: `RMF.smoothing_bound` times `log p ≥ 0`, summed over `S`. -/
lemma sum_log_smoothing_bound {f : Ω → ArithmeticFunction ℂ} {x X : ℝ} (hx : 0 ≤ x)
    (hX : 0 < X) {S : Finset ℕ} (hSp : ∀ p ∈ S, Nat.Prime p) (ω : Ω) :
    1 / 4 * (∑ p ∈ S, Real.log p * (X / p *
        ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / X)), ‖randomSum f (x / t) ω‖ ^ 2))
      - ∑ p ∈ S, Real.log p * (X / p *
          ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / X)), discrepancy f x p ω t)
      ≤ ∑ p ∈ S, Real.log p * ‖randomSum f (x / p) ω‖ ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hSp p hp).pos
  have hbound := smoothing_bound (f := f) hx hX hp0 ω
  have hlog : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
  nlinarith [mul_le_mul_of_nonneg_left hbound hlog]

/-! ### The sliver the main term's range misses

The main term delivers `∫_1^{√x/(1+1/X)}`, while `RMF.meanSquareIntegral` is `∫_1^{√x}`.  The
difference is this file's `sliverIntegral`, and it is small only in expectation: pointwise its
integrand is bounded by `1` over an interval of length `√x/(X+1)`. -/

omit [MeasurableSpace Ω] in
/-- `z ↦ ∑_{m≤z} f(m)` is measurable, being a step function of `⌊z⌋`. -/
lemma measurable_randomSum_snd (f : Ω → ArithmeticFunction ℂ) (ω : Ω) :
    Measurable fun z : ℝ => randomSum f z ω := by
  unfold randomSum
  exact (measurable_from_top (f := fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f ω n)).comp
    Nat.measurable_floor

omit [MeasurableSpace Ω] in
/-- The mean-square integrand is integrable on any interval above `1`. -/
lemma integrableOn_meanSquare_integrand (f : Ω → ArithmeticFunction ℂ) {a b : ℝ} (ha : 1 ≤ a)
    (ω : Ω) : IntegrableOn (fun z => ‖randomSum f z ω‖ ^ 2 / z ^ 2) (Set.Ioc a b) := by
  refine Measure.integrableOn_of_bounded (M := (∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f ω n‖) ^ 2)
    measure_Ioc_lt_top.ne
    ((((measurable_randomSum_snd f ω).norm).pow_const 2).div
      (measurable_id.pow_const 2)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
  have hz1 : (1 : ℝ) ≤ z := le_trans ha hz.1.le
  have hnum : ‖randomSum f z ω‖ ^ 2 ≤ (∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f ω n‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_randomSum_le_of_le f hz.2 ω) 2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hle : ‖randomSum f z ω‖ ^ 2 / z ^ 2 ≤ ‖randomSum f z ω‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    have hz2 : (1 : ℝ) ≤ z ^ 2 := by nlinarith
    nlinarith [sq_nonneg ‖randomSum f z ω‖, hz2]
  linarith

/-- The part of `RMF.meanSquareIntegral` that the main term's range misses. -/
noncomputable def sliverIntegral (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) : ℝ :=
  ∫ z in Set.Ioc (Real.sqrt x / (1 + 1 / Real.log x)) (Real.sqrt x),
    ‖randomSum f z ω‖ ^ 2 / z ^ 2

omit [MeasurableSpace Ω] in
lemma sliverIntegral_nonneg (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) :
    0 ≤ sliverIntegral f x ω :=
  setIntegral_nonneg measurableSet_Ioc fun _ _ => by positivity

/-- The standing facts about the smoothing scale at `X = log x`, for `x ≥ 4`. -/
lemma log_scale_facts {x : ℝ} (hx : 4 ≤ x) :
    (0 : ℝ) < x ∧ 1 ≤ Real.log x ∧ (2 : ℝ) ≤ Real.sqrt x ∧
      1 + 1 / Real.log x ≤ 2 ∧ 1 ≤ 1 + 1 / Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : (1 : ℝ) ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    nlinarith [Real.exp_one_lt_d9]
  have hsq : (2 : ℝ) ≤ Real.sqrt x := by
    have h4 : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h4
  have hinv : 1 / Real.log x ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hinv0 : (0 : ℝ) ≤ 1 / Real.log x := by positivity
  exact ⟨hx0, hlog, hsq, by linarith, by linarith⟩

omit [MeasurableSpace Ω] in
/-- **The split.**  `∫_1^{√x/(1+1/X)} = log x · meanSquare - sliver`. -/
lemma meanSquare_split {f : Ω → ArithmeticFunction ℂ} {x : ℝ} (hx : 4 ≤ x) (ω : Ω) :
    (∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)), ‖randomSum f z ω‖ ^ 2 / z ^ 2)
      = Real.log x * meanSquareIntegral f x ω - sliverIntegral f x ω := by
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx
  have hr0 : (0 : ℝ) < 1 + 1 / Real.log x := by linarith
  have hc1 : (1 : ℝ) ≤ Real.sqrt x / (1 + 1 / Real.log x) := by
    rw [le_div_iff₀ hr0]
    linarith
  have hcs : Real.sqrt x / (1 + 1 / Real.log x) ≤ Real.sqrt x := by
    rw [div_le_iff₀ hr0]
    nlinarith
  have hsq1 : (1 : ℝ) ≤ Real.sqrt x := by linarith
  have hI1 := integrableOn_meanSquare_integrand f (b := Real.sqrt x /
    (1 + 1 / Real.log x)) le_rfl ω
  have hI2 := integrableOn_meanSquare_integrand f (a := Real.sqrt x / (1 + 1 / Real.log x))
    (b := Real.sqrt x) hc1 ω
  have hunion := setIntegral_union (f := fun z => ‖randomSum f z ω‖ ^ 2 / z ^ 2)
    (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hI1 hI2
  rw [Set.Ioc_union_Ioc_eq_Ioc hc1 hcs] at hunion
  have hms : Real.log x * meanSquareIntegral f x ω
      = ∫ z in Set.Ioc 1 (Real.sqrt x), ‖randomSum f z ω‖ ^ 2 / z ^ 2 := by
    rw [meanSquareIntegral, ← mul_assoc, mul_inv_cancel₀ (by linarith : Real.log x ≠ 0),
      one_mul, intervalIntegral.integral_of_le hsq1]
  rw [hms, sliverIntegral]
  linarith

/-- The sliver's integrand is bounded, hence product-integrable — which licenses the exchange
of `∫ dμ` and `∫ dz` below. -/
lemma integrable_meanSquare_prod {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) {x c : ℝ} (hc : 1 ≤ c) :
    Integrable (Function.uncurry fun (ω : Ω) (z : ℝ) => ‖randomSum f z ω‖ ^ 2 / z ^ 2)
      (μ.prod (volume.restrict (Set.Ioc c (Real.sqrt x)))) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc c (Real.sqrt x))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hm : Measurable fun p : Ω × ℝ => ‖randomSum f p.2 p.1‖ ^ 2 / p.2 ^ 2 :=
    (((measurable_randomSum_uncurry hf).norm).pow_const 2).div (measurable_snd.pow_const 2)
  refine integrableOn_univ.1 (Measure.integrableOn_of_bounded
    (M := (⌊Real.sqrt x⌋₊ : ℝ) ^ 2) (measure_ne_top _ _) hm.aestronglyMeasurable ?_)
  rw [Measure.restrict_univ]
  refine (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).2 ?_
  filter_upwards [ae_norm_randomSum_le hf (Real.sqrt x)] with ω hω
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
  have hz1 : (1 : ℝ) ≤ z := le_trans hc hz.1.le
  have hn := hω z hz.2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : ‖randomSum f z ω‖ ^ 2 ≤ (⌊Real.sqrt x⌋₊ : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h2 : ‖randomSum f z ω‖ ^ 2 / z ^ 2 ≤ ‖randomSum f z ω‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    have hz2 : (1 : ℝ) ≤ z ^ 2 := by nlinarith
    nlinarith [sq_nonneg ‖randomSum f z ω‖, hz2]
  linarith

/-- **The sliver in mean.**  `E[sliver] ≤ 1/log x`.

Orthogonality gives `E‖∑_{m≤z} f(m)‖² = ⌊z⌋ ≤ z`, so the `z`-integrand is at most `1/z` and the
whole thing is at most `log(1 + 1/log x) ≤ 1/log x`.  The exchange of the two integrals is the
only nontrivial move; the bound itself is `log(1+u) ≤ u`. -/
theorem integral_sliverIntegral_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) {x : ℝ} (hx : 4 ≤ x) :
    (∫ ω, sliverIntegral f x ω ∂μ) ≤ 1 / Real.log x := by
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx
  have hr0 : (0 : ℝ) < 1 + 1 / Real.log x := by linarith
  have hc1 : (1 : ℝ) ≤ Real.sqrt x / (1 + 1 / Real.log x) := by
    rw [le_div_iff₀ hr0]
    linarith
  have hc0 : (0 : ℝ) < Real.sqrt x / (1 + 1 / Real.log x) := by linarith
  have hcs : Real.sqrt x / (1 + 1 / Real.log x) ≤ Real.sqrt x := by
    rw [div_le_iff₀ hr0]
    nlinarith
  have hInt := integrable_meanSquare_prod hf (x := x) hc1
  simp only [sliverIntegral]
  rw [integral_integral_swap hInt]
  have hinner : ∀ z ∈ Set.Ioc (Real.sqrt x / (1 + 1 / Real.log x)) (Real.sqrt x),
      (∫ ω, ‖randomSum f z ω‖ ^ 2 / z ^ 2 ∂μ) ≤ 1 / z := by
    intro z hz
    have hz1 : (1 : ℝ) ≤ z := le_trans hc1 hz.1.le
    have hz0 : (0 : ℝ) < z := by linarith
    rw [integral_div]
    have hsecond : (∫ ω, ‖randomSum f z ω‖ ^ 2 ∂μ) ≤ (⌊z⌋₊ : ℝ) := by
      simp only [randomSum]
      refine le_trans (integral_normSq_finsetSum hf fun n hn => by
        have := (Finset.mem_Icc.1 hn).1; omega) ?_
      simp
    refine le_trans (div_le_div_of_nonneg_right hsecond (by positivity)) ?_
    have hfl : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le (by linarith)
    have h1 : (⌊z⌋₊ : ℝ) / z ^ 2 ≤ z / z ^ 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hfl (by positivity)
    have h2 : z / z ^ 2 = 1 / z := by field_simp
    linarith
  have hIone : IntegrableOn (fun z : ℝ => 1 / z)
      (Set.Ioc (Real.sqrt x / (1 + 1 / Real.log x)) (Real.sqrt x)) := by
    refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      (measurable_const.div measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    have hz1 : (1 : ℝ) ≤ z := le_trans hc1 hz.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one (by linarith)]
    linarith
  have hcmp : (∫ z in Set.Ioc (Real.sqrt x / (1 + 1 / Real.log x)) (Real.sqrt x),
      ∫ ω, ‖randomSum f z ω‖ ^ 2 / z ^ 2 ∂μ)
      ≤ ∫ z in Set.Ioc (Real.sqrt x / (1 + 1 / Real.log x)) (Real.sqrt x), 1 / z :=
    setIntegral_mono_on hInt.integral_prod_right hIone measurableSet_Ioc hinner
  have hval : (∫ z in Set.Ioc (Real.sqrt x / (1 + 1 / Real.log x)) (Real.sqrt x), 1 / z)
      = Real.log (1 + 1 / Real.log x) := by
    rw [← intervalIntegral.integral_of_le hcs, integral_one_div_of_pos hc0 (by linarith)]
    congr 1
    field_simp
  have hlogle : Real.log (1 + 1 / Real.log x) ≤ 1 / Real.log x := by
    have h := Real.log_le_sub_one_of_pos hr0
    linarith
  linarith

/-! ### Integrability of the four quantities

Every term of the chain is a nonnegative integrable function of `ω`, and on a probability space
that is already enough for its `q`-th power: `t^q ≤ 1 + t` for `0 ≤ q ≤ 1`, so no bound on the
function itself is needed.  The two general facts this rests on — `RMF.rpow_le_one_add` and
`RMF.integrable_rpow_of_integrable` — sit next to Jensen in `RMF/SecondMoment.lean`, because the
upper branch needs them as well. -/

/-- The squared partial sum is integrable. -/
lemma integrable_normSq_randomSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) (b : ℝ) :
    Integrable (fun ω => ‖randomSum f b ω‖ ^ 2) μ := by
  refine Integrable.mono' (integrable_const ((⌊b⌋₊ : ℝ) ^ 2))
    ((hf.measurable_randomSum b).norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_norm_randomSum_le hf b] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hω b le_rfl) 2

/-- The prime sum of squared partial sums, to which the moment is reduced. -/
lemma integrable_sum_normSq_randomSum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) (x : ℝ) (S : Finset ℕ) :
    Integrable (fun ω => ∑ p ∈ S, ‖randomSum f (x / p) ω‖ ^ 2) μ :=
  integrable_finsetSum _ fun p _ => integrable_normSq_randomSum hf (x / p)

/-- The mean-square integral is integrable, by Fubini on the same product bound. -/
lemma integrable_meanSquareIntegral {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) {x : ℝ} (hx : 4 ≤ x) :
    Integrable (fun ω => meanSquareIntegral f x ω) μ := by
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx
  have hsq1 : (1 : ℝ) ≤ Real.sqrt x := by linarith
  have hI := (integrable_meanSquare_prod hf (x := x) (c := 1) le_rfl).integral_prod_left
  have hcongr : (fun ω => meanSquareIntegral f x ω) = fun ω =>
      (Real.log x)⁻¹ * ∫ z in Set.Ioc 1 (Real.sqrt x), ‖randomSum f z ω‖ ^ 2 / z ^ 2 := by
    funext ω
    rw [meanSquareIntegral, intervalIntegral.integral_of_le hsq1]
  rw [hcongr]
  exact hI.const_mul _

/-- The sliver is integrable, likewise. -/
lemma integrable_sliverIntegral {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) {x : ℝ} (hx : 4 ≤ x) :
    Integrable (fun ω => sliverIntegral f x ω) μ := by
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx
  have hr0 : (0 : ℝ) < 1 + 1 / Real.log x := by linarith
  have hc1 : (1 : ℝ) ≤ Real.sqrt x / (1 + 1 / Real.log x) := by
    rw [le_div_iff₀ hr0]
    linarith
  exact (integrable_meanSquare_prod hf (x := x) hc1).integral_prod_left

/-- The total smoothing discrepancy is integrable, prime by prime. -/
lemma integrable_windowDiscrepancySum {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsBoundedRMF f μ) {x X : ℝ} (hx : 0 ≤ x) {S : Finset ℕ}
    (hSp : ∀ p ∈ S, Nat.Prime p) :
    Integrable (fun ω => ∑ p ∈ S, Real.log p * (X / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / X)), discrepancy f x p ω t)) μ :=
  integrable_finsetSum _ fun p hp =>
    integrable_log_mul_window_discrepancy hf hx (by exact_mod_cast (hSp p hp).pos)

/-! ### The chain, pointwise

The three bounds in sequence, then the split of the mean-square range.  Reading it backwards:
`∑_p ‖∑_{m≤x/p}f(m)‖²` is at least `(log x)⁻¹` times its `log p`-weighted version, which
smoothing bounds below by `¼` of the window sum minus the discrepancy, and the window sum is at
least `½ x ∫_1^{√x/(1+1/X)}`, which is `log x · meanSquare - sliver`. -/

omit [MeasurableSpace Ω] in
theorem sum_normSq_ge :
    ∃ x₀ : ℝ, ∀ (f : Ω → ArithmeticFunction ℂ) (ω : Ω) (x : ℝ), x₀ ≤ x →
      ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) → (∀ p ∈ S, (p : ℝ) ≤ x) →
        (∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) →
        x / 8 * meanSquareIntegral f x ω
            - x / (8 * Real.log x) * sliverIntegral f x ω
            - (∑ p ∈ S, Real.log p * (Real.log x / p *
                ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
                  discrepancy f x p ω t)) / Real.log x
          ≤ ∑ p ∈ S, ‖randomSum f (x / p) ω‖ ^ 2 := by
  obtain ⟨x₀, hL8⟩ := half_meanSquare_le_window_sum (Ω := Ω)
  refine ⟨max x₀ 4, fun f ω x hx S hSp hSx hS => ?_⟩
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx4
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hL4 := sum_log_mul_le_log_mul_sum (x := x) (by linarith) hSx
    (v := fun p => ‖randomSum f (x / p) ω‖ ^ 2) fun p => by positivity
  have hL5 := sum_log_smoothing_bound (f := f) (X := Real.log x) hx0.le hlog0 hSp ω
  have h8 := hL8 f ω x hxx₀ S hSp hS
  rw [meanSquare_split hx4 ω] at h8
  -- the discrepancy sum is an atom from here on: `field_simp` must not reach inside its
  -- integration ranges
  set Dsum : ℝ := ∑ p ∈ S, Real.log p * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), discrepancy f x p ω t) with hDdef
  refine le_of_mul_le_mul_right ?_ hlog0
  have hmul : (x / 8 * meanSquareIntegral f x ω
      - x / (8 * Real.log x) * sliverIntegral f x ω - Dsum / Real.log x) * Real.log x
      = x / 8 * (Real.log x * meanSquareIntegral f x ω) - x / 8 * sliverIntegral f x ω
        - Dsum := by field_simp
  rw [hmul]
  nlinarith [hL4, hL5, h8]

/-- Integrating a pointwise `F - G - H ≤ K`. -/
lemma integral_sub_two_le {μ : Measure Ω} {F G H K : Ω → ℝ} (hF : Integrable F μ)
    (hG : Integrable G μ) (hH : Integrable H μ) (hK : Integrable K μ)
    (h : ∀ ω, F ω - G ω - H ω ≤ K ω) :
    (∫ ω, F ω ∂μ) - (∫ ω, G ω ∂μ) - (∫ ω, H ω ∂μ) ≤ ∫ ω, K ω ∂μ := by
  have h1 : (∫ ω, (F ω - G ω - H ω) ∂μ) ≤ ∫ ω, K ω ∂μ :=
    integral_mono_ae ((hF.sub hG).sub hH) hK (Filter.Eventually.of_forall h)
  have hFG : Integrable (fun ω => F ω - G ω) μ := hF.sub hG
  rwa [integral_sub hFG hH, integral_sub hF hG] at h1

/-! ### The chain at the `q`-th power -/

/-- **The chain at the `q`-th power**: for `0 ≤ q ≤ 1`, `x ≥ x₀` and `S` as below,
`(x/8)^q E[meanSquare^q] - (x/(8 log²x))^q - (8x/log x)^q ≤ E[(∑_{p∈S}‖∑_{m≤x/p}f(m)‖²)^q]`,
with `x₀` independent of `f`, `μ`, `x`, `q`, `S`.  Divided by `x^q` the subtracted terms are
`(8 log²x)^{-q}` and `(8/log x)^q`; the second becomes Proposition 3's `C/√(log x)` after the
`2q`-th root.  Both are small only in mean, so both are peeled off with Jensen
(`RMF.integral_rpow_le_rpow_integral`) after the `ω`-integral has been formed. -/
theorem meanSquare_le_sum_normSq :
    ∃ x₀ : ℝ, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω) [IsProbabilityMeasure μ],
      IsBoundedRMF f μ → ∀ x q : ℝ, x₀ ≤ x → 0 ≤ q → q ≤ 1 →
        ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) → (∀ p ∈ S, (p : ℝ) ≤ x) →
          (∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) →
          (x / 8) ^ q * (∫ ω, meanSquareIntegral f x ω ^ q ∂μ)
              - (x / (8 * Real.log x ^ 2)) ^ q - (8 * x / Real.log x) ^ q
            ≤ ∫ ω, (∑ p ∈ S, ‖randomSum f (x / p) ω‖ ^ 2) ^ q ∂μ := by
  obtain ⟨x₀, hchain⟩ := sum_normSq_ge (Ω := Ω)
  refine ⟨max x₀ 4, ?_⟩
  intro f μ _ hf x q hx hq0 hq1 S hSp hSx hS
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx4
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hsq1 : (1 : ℝ) ≤ Real.sqrt x := by linarith
  have hxe : Real.exp 1 ≤ x := by nlinarith [Real.exp_one_lt_d9]
  have hSsub : S ⊆ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime} := fun p hp =>
    Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨(hSp p hp).pos, Nat.le_floor (hSx p hp)⟩, hSp p hp⟩
  -- nonnegativity of the four quantities
  have hMS0 : ∀ ω, 0 ≤ meanSquareIntegral f x ω := by
    intro ω
    rw [meanSquareIntegral]
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg hsq1 fun z _ => by positivity)
  have hD0 : ∀ ω, 0 ≤ ∑ p ∈ S, Real.log p * (Real.log x / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), discrepancy f x p ω t) := by
    intro ω
    refine Finset.sum_nonneg fun p _ => mul_nonneg (Real.log_natCast_nonneg p) ?_
    exact mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioc
      fun t _ => discrepancy_nonneg f x p ω t)
  have hP0 : ∀ ω, 0 ≤ x / 8 * meanSquareIntegral f x ω :=
    fun ω => mul_nonneg (by positivity) (hMS0 ω)
  have hQ0 : ∀ ω, 0 ≤ x / (8 * Real.log x) * sliverIntegral f x ω :=
    fun ω => mul_nonneg (by positivity) (sliverIntegral_nonneg f x ω)
  have hR0 : ∀ ω, 0 ≤ (∑ p ∈ S, Real.log p * (Real.log x / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
        discrepancy f x p ω t)) / Real.log x :=
    fun ω => div_nonneg (hD0 ω) hlog0.le
  have hA0 : ∀ ω, 0 ≤ ∑ p ∈ S, ‖randomSum f (x / p) ω‖ ^ 2 :=
    fun ω => Finset.sum_nonneg fun p _ => by positivity
  -- integrability
  have hPi : Integrable (fun ω => x / 8 * meanSquareIntegral f x ω) μ :=
    (integrable_meanSquareIntegral hf hx4).const_mul _
  have hQi : Integrable (fun ω => x / (8 * Real.log x) * sliverIntegral f x ω) μ :=
    (integrable_sliverIntegral hf hx4).const_mul _
  have hRi : Integrable (fun ω => (∑ p ∈ S, Real.log p * (Real.log x / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
        discrepancy f x p ω t)) / Real.log x) μ :=
    (integrable_windowDiscrepancySum hf (X := Real.log x) hx0.le hSp).div_const _
  have hAi : Integrable (fun ω => ∑ p ∈ S, ‖randomSum f (x / p) ω‖ ^ 2) μ :=
    integrable_sum_normSq_randomSum hf x S
  have hPq := integrable_rpow_of_integrable hPi
    (Filter.Eventually.of_forall hP0) hq0 hq1
  have hQq := integrable_rpow_of_integrable hQi
    (Filter.Eventually.of_forall hQ0) hq0 hq1
  have hRq := integrable_rpow_of_integrable hRi
    (Filter.Eventually.of_forall hR0) hq0 hq1
  have hAq := integrable_rpow_of_integrable hAi
    (Filter.Eventually.of_forall hA0) hq0 hq1
  -- the pointwise inequality at the `q`-th power
  have hpt : ∀ ω, (x / 8 * meanSquareIntegral f x ω) ^ q
      - (x / (8 * Real.log x) * sliverIntegral f x ω) ^ q
      - ((∑ p ∈ S, Real.log p * (Real.log x / p *
          ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
            discrepancy f x p ω t)) / Real.log x) ^ q
      ≤ (∑ p ∈ S, ‖randomSum f (x / p) ω‖ ^ 2) ^ q := fun ω =>
    rpow_sub_three_le (hA0 ω) (hP0 ω) (hQ0 ω) (hR0 ω)
      (hchain f ω x hxx₀ S hSp hSx hS) hq0 hq1
  have hmain := integral_sub_two_le hPq hQq hRq hAq hpt
  -- the three evaluations
  have hPval : (∫ ω, (x / 8 * meanSquareIntegral f x ω) ^ q ∂μ)
      = (x / 8) ^ q * ∫ ω, meanSquareIntegral f x ω ^ q ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      Real.mul_rpow (by positivity) (hMS0 ω))
  have hQval : (∫ ω, (x / (8 * Real.log x) * sliverIntegral f x ω) ^ q ∂μ)
      ≤ (x / (8 * Real.log x ^ 2)) ^ q := by
    refine le_trans (integral_rpow_le_rpow_integral hq0 hq1
      (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (hQ0 ω)) hQi hQq) ?_
    refine Real.rpow_le_rpow (integral_nonneg hQ0) ?_ hq0
    rw [integral_const_mul]
    have hstep := mul_le_mul_of_nonneg_left (integral_sliverIntegral_le hf hx4)
      (by positivity : (0 : ℝ) ≤ x / (8 * Real.log x))
    have heq : x / (8 * Real.log x) * (1 / Real.log x) = x / (8 * Real.log x ^ 2) := by
      field_simp
    linarith [hstep, heq.le, heq.ge]
  have hRval : (∫ ω, ((∑ p ∈ S, Real.log p * (Real.log x / p *
      ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
        discrepancy f x p ω t)) / Real.log x) ^ q ∂μ)
      ≤ (8 * x / Real.log x) ^ q := by
    refine le_trans (integral_rpow_le_rpow_integral hq0 hq1
      (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (hR0 ω)) hRi hRq) ?_
    refine Real.rpow_le_rpow (integral_nonneg hR0) ?_ hq0
    rw [integral_div, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (integral_sum_discrepancy_le_log hf hxe hSsub)
      (by positivity)
  rw [hPval] at hmain
  linarith

/-! ### The hypotheses on `S` are satisfiable

`RMF.sum_normSq_ge` and `RMF.meanSquare_le_sum_normSq` are stated for an arbitrary `S`
sandwiched between the primes of `(√x, x]` and the naturals below `x`.  The sandwich is not
vacuous: the primes of `(√x, x]` themselves sit in it, and that is the `S` the reduction will
supply. -/

omit [MeasurableSpace Ω] in
/-- The primes of `(√x, x]` satisfy all three hypotheses the assembly imposes on `S`. -/
lemma primesIoc_sqrt_spec {x : ℝ} (hx : 0 ≤ x) :
    (∀ p ∈ {p ∈ Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊x⌋₊ | p.Prime}, Nat.Prime p) ∧
      (∀ p ∈ {p ∈ Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊x⌋₊ | p.Prime}, (p : ℝ) ≤ x) ∧
      ∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x →
        p ∈ {p ∈ Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊x⌋₊ | p.Prime} := by
  refine ⟨fun p hp => (Finset.mem_filter.1 hp).2, fun p hp => ?_, fun p hprime hsq hpx => ?_⟩
  · have hple : p ≤ ⌊x⌋₊ := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hp).1).2
    have h1 : (p : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hple
    exact le_trans h1 (Nat.floor_le hx)
  · refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨?_, Nat.le_floor hpx⟩, hprime⟩
    have h1 : (⌊Real.sqrt x⌋₊ : ℝ) < (p : ℝ) :=
      lt_of_le_of_lt (Nat.floor_le (Real.sqrt_nonneg x)) hsq
    exact_mod_cast h1

/-! ### The chain closed: from the mean square to the moment

`RMF.khintchine_rough` (symmetrisation and Khintchine, with the factorisation and the
independence split) and `RMF.meanSquare_le_sum_normSq` meet at the prime sum
`∑_{√x<p≤x}‖∑_{m≤x/p}f(m)‖²`.  Composing them is Harper's Proposition 3 before the `2q`-th root
is taken. -/

/-- **The lower-bound chain, end to end.**  Given the Khintchine input with constant `K`, for
`x ≥ x₀` and `2/3 ≤ q ≤ 1`,

`K^{-(1-q)}·((x/8)^q E[meanSquare^q] - (x/(8 log²x))^q - (8x/log x)^q) ≤ E‖∑_{n≤x}f(n)‖^{2q}`,

with `x₀` independent of `f`, `μ`, `K`, `x` and `q`. -/
theorem meanSquare_le_momentOf :
    ∃ x₀ : ℝ, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω) [IsProbabilityMeasure μ],
      IsBoundedRMF f μ → ∀ K : ℝ, 0 < K →
      (∀ x q : ℝ, 1 ≤ x → ⌊x⌋₊ < (⌊Real.sqrt x⌋₊ + 1) ^ 2 → 2 / 3 ≤ q → q ≤ 1 →
        K ^ (-(1 - q)) * ∫ ω, (∑ p ∈ largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊,
            ‖randomSum f (x / p) ω‖ ^ 2) ^ q ∂μ
          ≤ ∫ ω, ‖randomSum f x ω‖ ^ (2 * q) ∂μ) →
      ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
        K ^ (-(1 - q)) * ((x / 8) ^ q * (∫ ω, meanSquareIntegral f x ω ^ q ∂μ)
            - (x / (8 * Real.log x ^ 2)) ^ q - (8 * x / Real.log x) ^ q)
          ≤ ∫ ω, ‖randomSum f x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨x₀, hL9⟩ := meanSquare_le_sum_normSq (Ω := Ω)
  refine ⟨max x₀ 4, fun f μ _ hf K hK0 hkhin x q hx hq23 hq1 => ?_⟩
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  set y : ℕ := ⌊Real.sqrt x⌋₊ with hydef
  have hxy : ⌊x⌋₊ < (y + 1) ^ 2 := by
    have hs : Real.sqrt x < (y : ℝ) + 1 := Nat.lt_floor_add_one _
    have hlt : x < ((y : ℝ) + 1) ^ 2 := by nlinarith [Real.sqrt_nonneg x]
    have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    have hcast : (⌊x⌋₊ : ℝ) < (((y + 1) ^ 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  -- the prime set the two halves share
  have hSp : ∀ p ∈ largePrimeSet y ⌊x⌋₊, Nat.Prime p := fun p hp => (mem_largePrimeSet.1 hp).2
  have hSx : ∀ p ∈ largePrimeSet y ⌊x⌋₊, (p : ℝ) ≤ x := by
    intro p hp
    have hple : p ≤ ⌊x⌋₊ := (mem_largePrimeSet.1 hp).1.2
    exact le_trans (by exact_mod_cast hple) (Nat.floor_le hx0)
  have hScov : ∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x →
      p ∈ largePrimeSet y ⌊x⌋₊ := by
    intro p hp hsqp hpx
    refine mem_largePrimeSet.2 ⟨⟨?_, Nat.le_floor hpx⟩, hp⟩
    have : ((y : ℝ)) < (p : ℝ) := lt_of_le_of_lt (Nat.floor_le (Real.sqrt_nonneg x)) hsqp
    exact_mod_cast this
  -- the two halves
  have h9 := hL9 _ μ hf x q hxx₀ (by linarith) hq1 _ hSp hSx hScov
  have hkh := hkhin x q hx1 hxy hq23 hq1
  have hpos : (0 : ℝ) < K ^ (-(1 - q)) := Real.rpow_pos_of_pos hK0 _
  linarith [mul_le_mul_of_nonneg_left h9 hpos.le, hkh]

/-- **The lower-bound chain, end to end**, Steinhaus: the `K = 2` instance of
`RMF.meanSquare_le_momentOf`, with the Khintchine input supplied by `RMF.khintchine_rough`. -/
theorem meanSquare_le_moment :
    ∃ x₀ : ℝ, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
        (2 : ℝ) ^ (-(1 - q)) * ((x / 8) ^ q * (∫ ω, meanSquareIntegral f x ω ^ q ∂μ)
            - (x / (8 * Real.log x ^ 2)) ^ q - (8 * x / Real.log x) ^ q)
          ≤ ∫ ω, ‖randomSum f x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨x₀, h⟩ := meanSquare_le_momentOf (Ω := Ω)
  refine ⟨x₀, fun f μ hf x q hx hq23 hq1 => ?_⟩
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  exact h _ μ (IsSteinhausRMF.isBoundedRMF hX.isSteinhausRMF) 2 two_pos
    (fun x q hx1 hxy hq23 hq1 => khintchine_rough hX hx1 hxy two_pos
      (fun v => integral_norm_rpow_four_primeLinearForm_le hX.isSteinhausRMF
        (fun p hp => (mem_largePrimeSet.1 hp).2) v) hq23 hq1)
    x q hx hq23 hq1

/-! ### Harper's Proposition 3

The `2q`-th root of `RMF.meanSquare_le_moment`.  Two exponent identities do the work:
`q·(1/(2q)) = 1/2`, which turns every `(x·E)^q` into `√x·√E`; and `(1-q)/(2q) ≤ 1/4` on
`q ∈ [2/3,1]`, which keeps the leading constant absolute.

The constants come out exactly, with no numerical evaluation.  With `α = √(1/8)`, `β = √8` and
`γ = 1/√(log x)`, the two error terms are `αγ²` and `βγ`; since `γ ≤ 1` and `β = 8α`, their sum
is at most `9αγ` — which is where `C = 9` comes from, and why it is sharp for this route. -/

/-- The arithmetic of Proposition 3's main case, isolated from the analysis:
`X` is `√x`, `K` the leading constant `K₀^{-(1-q)/(2q)}` and `L` the absolute lower bound
`K₀^{-1/4}` for it, and `α, β, γ` are `√(1/8)`, `√8` and `1/√(log x)`.  `L` is opaque here:
nothing in the proof needs to know what it is, which is what lets `K₀` be `2` for Steinhaus and
`3` for Rademacher.  The two facts that make it work are `γ ≤ 1`, which lets `αγ²` be absorbed into
`αγ`, and `β = 8α`, which makes the two error terms exactly `9αγ`. -/
lemma prop3_arith {A M K L α β γ X : ℝ} (hα0 : 0 < α) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hβα : β = 8 * α) (hK0 : 0 < K) (hKr : L ≤ K) (hX0 : 0 < X)
    (hA : 9 * γ < A)
    (h : (X * α * A - X * (α * γ * γ) - X * (β * γ)) * K ≤ M) :
    L * α * (A - 9 * γ) * X ≤ M := by
  have hαγ0 : (0 : ℝ) ≤ α * γ := mul_nonneg hα0.le hγ0.le
  have herr : α * γ * γ + β * γ ≤ 9 * (α * γ) := by
    have h1 : α * γ * γ ≤ α * γ * 1 := mul_le_mul_of_nonneg_left hγ1 hαγ0
    rw [mul_one] at h1
    rw [hβα]
    linarith
  have hb2 : (0 : ℝ) ≤ α * A - 9 * (α * γ) := by nlinarith
  have hb3 : L * (α * A - 9 * (α * γ))
      ≤ K * (α * A - (α * γ * γ + β * γ)) :=
    mul_le_mul hKr (by linarith) hb2 hK0.le
  nlinarith [mul_le_mul_of_nonneg_right hb3 hX0.le, h]

/-- The arithmetic of Proposition 3's second bound.  `K1` and `K2` stand for `c₁^{1/(2q)}` and
`C₁^{1/(2q)}`; all that is needed of them is `c₀ ≤ K1` and `K2 ≤ c₀C`, which is how the
`q`-dependence is kept out of the exported constants. -/
lemma prop3_arith2 {E4 E2 Sr RHS K1 K2 c₀ C c₂ C₂ ev L : ℝ}
    (hE4 : 0 ≤ E4) (hE2 : 0 ≤ E2) (hev : 0 < ev) (hL : 0 < L) (hc₂ : 0 < c₂)
    (hK1 : c₀ ≤ K1) (hK2 : K2 ≤ c₀ * C) (hC₂ : C₂ ≤ c₀ * C)
    (hlow : K1 * E4 - K2 * ev⁻¹ * E2 ≤ Sr)
    (hP : c₂ * (Sr - C₂ / L) ≤ RHS) :
    c₂ * c₀ * (E4 - C / ev * E2 - C / L) ≤ RHS := by
  have hevi : (0 : ℝ) < ev⁻¹ := by positivity
  have hLi : (0 : ℝ) ≤ L⁻¹ := by positivity
  have h1 : c₀ * E4 ≤ K1 * E4 := mul_le_mul_of_nonneg_right hK1 hE4
  have h2 : K2 * ev⁻¹ * E2 ≤ c₀ * C * ev⁻¹ * E2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2 hevi.le) hE2
  have h3 : C₂ * L⁻¹ ≤ c₀ * C * L⁻¹ := mul_le_mul_of_nonneg_right hC₂ hLi
  rw [div_eq_mul_inv] at hP
  rw [div_eq_mul_inv, div_eq_mul_inv]
  linarith [mul_le_mul_of_nonneg_left h1 hc₂.le, mul_le_mul_of_nonneg_left h2 hc₂.le,
    mul_le_mul_of_nonneg_left h3 hc₂.le, mul_le_mul_of_nonneg_left hlow hc₂.le, hP]

/-- **The multiplier of `RMF.reduction_lower_meanSquareOf`**, `K^{-1/4}·8^{-1/2}`: the `8^{-1/2}`
is the mean square's normalisation and `K^{-1/4}` the price of Hölder at `q ≥ 2/3`.  At the
`K = 2` the chain instantiates it is `2^{-7/4}`.  Its companion constant is the numeral `9`. -/
noncomputable def meanSquareRedLower (K : ℝ) : ℝ :=
  K ^ (-(1 : ℝ) / 4) * (1 / 8 : ℝ) ^ ((1 : ℝ) / 2)

lemma meanSquareRedLower_pos {K : ℝ} (hK : 0 < K) : 0 < meanSquareRedLower K :=
  mul_pos (Real.rpow_pos_of_pos hK _) (Real.rpow_pos_of_pos (by norm_num) _)

/-- **`RMF.reduction_lower_meanSquareOf` with its constants named.**  Both are closed forms: the
multiplier is `RMF.meanSquareRedLower K` and the subtracted constant the numeral `9`; only the
threshold `max x₀ e` depends on the chain below. -/
theorem reduction_lower_meanSquareOf_named {K : ℝ} (hK1 : 1 ≤ K)
    {Pr : (Ω → ArithmeticFunction ℂ) → Measure Ω → Prop} {x₀ : ℝ}
    (hchain :
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), Pr f μ →
      ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
        K ^ (-(1 - q)) * ((x / 8) ^ q * (∫ ω, meanSquareIntegral f x ω ^ q ∂μ)
            - (x / (8 * Real.log x ^ 2)) ^ q - (8 * x / Real.log x) ^ q)
          ≤ ∫ ω, ‖randomSum f x ω‖ ^ (2 * q) ∂μ) :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), Pr f μ →
      ∀ x q : ℝ, max x₀ (Real.exp 1) ≤ x → 2 / 3 ≤ q → q ≤ 1 →
        meanSquareRedLower K * ((∫ ω, meanSquareIntegral f x ω ^ q ∂μ) ^ (1 / (2 * q))
              - 9 / Real.sqrt (Real.log x))
          ≤ (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) ^ (1 / (2 * q)) := by
  have hK0' : (0 : ℝ) < K := by linarith
  have hα0 : (0 : ℝ) < (1 / 8 : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  rw [meanSquareRedLower]
  intro f μ hf x q hx hq23 hq1
  -- scales
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hL1 : (1 : ℝ) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by
    rw [← Real.exp_zero]
    exact le_trans (Real.exp_le_exp.2 zero_le_one) hxe
  have hq0 : (0 : ℝ) < q := by linarith
  have h2q : (1 : ℝ) < 2 * q := by linarith
  have hr0 : (0 : ℝ) < 1 / (2 * q) := by positivity
  have hr1 : 1 / (2 * q) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hqr : q * (1 / (2 * q)) = 1 / 2 := by field_simp
  -- the constants
  set α : ℝ := (1 / 8 : ℝ) ^ ((1 : ℝ) / 2) with hαdef
  set β : ℝ := (8 : ℝ) ^ ((1 : ℝ) / 2) with hβdef
  set γ : ℝ := ((Real.log x)⁻¹) ^ ((1 : ℝ) / 2) with hγdef
  have hβ0 : (0 : ℝ) < β := Real.rpow_pos_of_pos (by norm_num) _
  have hγ0 : (0 : ℝ) < γ := Real.rpow_pos_of_pos (by positivity) _
  have hβne : β ≠ 0 := ne_of_gt hβ0
  have hββ : β * β = 8 := by
    rw [hβdef, ← Real.rpow_add (by norm_num)]
    norm_num
  have hαβ : α = β⁻¹ := by
    rw [hαdef, hβdef, show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num,
      Real.inv_rpow (by norm_num)]
  have hβα : β = 8 * α := by
    rw [hαβ]
    field_simp
    linarith
  have hγsqrt : γ = 1 / Real.sqrt (Real.log x) := by
    rw [hγdef, Real.inv_rpow hL0.le, Real.sqrt_eq_rpow]
    exact (one_div _).symm
  have hinv1 : (Real.log x)⁻¹ ≤ 1 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hL1
    simpa using h
  have hγ1 : γ ≤ 1 := by
    have h1 : ((Real.log x)⁻¹) ^ ((1 : ℝ) / 2) ≤ (1 : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hinv1 (by norm_num)
    rwa [Real.one_rpow] at h1
  -- the two integrals
  have hA0 : (0 : ℝ) ≤ ∫ ω, meanSquareIntegral f x ω ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (meanSquareIntegral_nonneg hx1 ω) _
  have hM0 : (0 : ℝ) ≤ ∫ ω, ‖randomSum f x ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  -- the normalised moment
  have hnorm : (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ)
      = (∫ ω, ‖randomSum f x ω‖ ^ (2 * q) ∂μ) / x ^ q := by
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [normalisedSum]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg x), Real.div_rpow (norm_nonneg _) (Real.sqrt_nonneg x)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  rw [hnorm, Real.div_rpow hM0 (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le, hqr]
  -- the case where there is nothing to prove
  by_cases hcase : (∫ ω, meanSquareIntegral f x ω ^ q ∂μ) ^ (1 / (2 * q))
      ≤ 9 / Real.sqrt (Real.log x)
  · have hR : (0 : ℝ) ≤ (∫ ω, ‖randomSum f x ω‖ ^ (2 * q) ∂μ) ^ (1 / (2 * q))
        / x ^ ((1 : ℝ) / 2) := by positivity
    have hc0 : (0 : ℝ) < K ^ (-(1 : ℝ) / 4) * α :=
      mul_pos (Real.rpow_pos_of_pos hK0' _) hα0
    have hle : (∫ ω, meanSquareIntegral f x ω ^ q ∂μ) ^ (1 / (2 * q))
        - 9 / Real.sqrt (Real.log x) ≤ 0 := by linarith
    nlinarith [hR, mul_le_mul_of_nonneg_left hle hc0.le]
  replace hcase := lt_of_not_ge hcase
  set A : ℝ := ∫ ω, meanSquareIntegral f x ω ^ q ∂μ with hAdef
  set M : ℝ := ∫ ω, ‖randomSum f x ω‖ ^ (2 * q) ∂μ with hMdef
  -- the chain of `RMF.meanSquare_le_moment`, divided by its leading constant
  have hK0 : (0 : ℝ) < K ^ (-(1 - q)) := Real.rpow_pos_of_pos hK0' _
  have hmain := hchain f μ hf x q hxx₀ hq23 hq1
  have hP0 : (0 : ℝ) ≤ (x / 8) ^ q * A := mul_nonneg (Real.rpow_nonneg (by positivity) _) hA0
  have hQ0 : (0 : ℝ) ≤ (x / (8 * Real.log x ^ 2)) ^ q := Real.rpow_nonneg (by positivity) _
  have hR0 : (0 : ℝ) ≤ (8 * x / Real.log x) ^ q := Real.rpow_nonneg (by positivity) _
  have hdiv : (x / 8) ^ q * A - (x / (8 * Real.log x ^ 2)) ^ q - (8 * x / Real.log x) ^ q
      ≤ M / K ^ (-(1 - q)) := by
    rw [le_div_iff₀ hK0]
    linarith [hmain]
  have hthree := rpow_sub_three_le (div_nonneg hM0 hK0.le) hP0 hQ0 hR0 hdiv hr0.le hr1
  -- the three exponent identities, all instances of `q·(1/(2q)) = 1/2`
  have hPr : ((x / 8) ^ q * A) ^ (1 / (2 * q)) = x ^ ((1 : ℝ) / 2) * α * A ^ (1 / (2 * q)) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _) hA0,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ x / 8), hqr,
      show x / 8 = x * (1 / 8 : ℝ) by ring, Real.mul_rpow hx0.le (by norm_num), ← hαdef]
  have hQr : ((x / (8 * Real.log x ^ 2)) ^ q) ^ (1 / (2 * q))
      = x ^ ((1 : ℝ) / 2) * (α * γ * γ) := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ x / (8 * Real.log x ^ 2)), hqr,
      show x / (8 * Real.log x ^ 2)
        = x * ((1 / 8 : ℝ) * ((Real.log x)⁻¹ * (Real.log x)⁻¹)) by field_simp,
      Real.mul_rpow hx0.le (by positivity), Real.mul_rpow (by norm_num) (by positivity),
      Real.mul_rpow (by positivity) (by positivity), ← hαdef, ← hγdef, mul_assoc]
  have hRr : ((8 * x / Real.log x) ^ q) ^ (1 / (2 * q)) = x ^ ((1 : ℝ) / 2) * (β * γ) := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 8 * x / Real.log x), hqr,
      show 8 * x / Real.log x = x * ((8 : ℝ) * (Real.log x)⁻¹) by field_simp,
      Real.mul_rpow hx0.le (by positivity), Real.mul_rpow (by norm_num) (by positivity),
      ← hβdef, ← hγdef]
  have hMK : (M / K ^ (-(1 - q))) ^ (1 / (2 * q))
      = M ^ (1 / (2 * q)) / (K ^ (-(1 - q))) ^ (1 / (2 * q)) :=
    Real.div_rpow hM0 hK0.le _
  rw [hPr, hQr, hRr, hMK] at hthree
  -- the leading constant stays absolute, because `(1-q)/(2q) ≤ 1/4` on `[2/3,1]`
  have hKr0 : (0 : ℝ) < (K ^ (-(1 - q))) ^ (1 / (2 * q)) := Real.rpow_pos_of_pos hK0 _
  have hKr : K ^ (-(1 : ℝ) / 4) ≤ (K ^ (-(1 - q))) ^ (1 / (2 * q)) := by
    rw [← Real.rpow_mul hK0'.le]
    refine Real.rpow_le_rpow_of_exponent_le hK1 ?_
    have h : (1 - q) * (1 / (2 * q)) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * q)]
      linarith
    rw [neg_mul]
    linarith
  -- and the arithmetic
  have hx2 : (0 : ℝ) < x ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
  have hcase' : 9 * γ < A ^ (1 / (2 * q)) := by
    rw [hγsqrt]
    calc (9 : ℝ) * (1 / Real.sqrt (Real.log x)) = 9 / Real.sqrt (Real.log x) := by ring
      _ < A ^ (1 / (2 * q)) := hcase
  have h9 : (9 : ℝ) / Real.sqrt (Real.log x) = 9 * γ := by
    rw [hγsqrt]
    ring
  rw [h9, le_div_iff₀ hx2]
  refine prop3_arith hα0 hγ0 hγ1 hβα hKr0 hKr hx2 hcase' ?_
  rw [← le_div_iff₀ hKr0]
  exact hthree

/-- **Harper's Proposition 3, first bound.**

`‖∑_{n≤x} f(n)‖_{2q} ≫ √(x/log x)·‖∫_1^{√x}|∑_{m≤z}f(m)|² dz/z²‖_q^{1/2} - C√(x/log x)`,

uniformly for `2/3 ≤ q ≤ 1`, divided through by `√x` and with `(log x)⁻¹` folded into
`RMF.meanSquareIntegral`.

The subtracted `C/√(log x)` is what makes this statement one-sided in a way the upper bound is
not: nothing here forces the bracket to be positive. -/
theorem reduction_lower_meanSquareOf {K : ℝ} (hK1 : 1 ≤ K)
    {Pr : (Ω → ArithmeticFunction ℂ) → Measure Ω → Prop}
    (hchainAll : ∃ x₀ : ℝ, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), Pr f μ →
      ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
        K ^ (-(1 - q)) * ((x / 8) ^ q * (∫ ω, meanSquareIntegral f x ω ^ q ∂μ)
            - (x / (8 * Real.log x ^ 2)) ^ q - (8 * x / Real.log x) ^ q)
          ≤ ∫ ω, ‖randomSum f x ω‖ ^ (2 * q) ∂μ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ x₀ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), Pr f μ →
        ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
          c * ((∫ ω, meanSquareIntegral f x ω ^ q ∂μ) ^ (1 / (2 * q))
                - C / Real.sqrt (Real.log x))
            ≤ (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) ^ (1 / (2 * q)) := by
  obtain ⟨x₀, hchain⟩ := hchainAll
  exact ⟨meanSquareRedLower K, 9, meanSquareRedLower_pos (by linarith), by norm_num,
    max x₀ (Real.exp 1), reduction_lower_meanSquareOf_named hK1 hchain⟩

/-- **Harper's Proposition 3, first bound**, Steinhaus: the `K = 2` instance of
`RMF.reduction_lower_meanSquareOf`. -/
theorem reduction_lower_meanSquare :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ x₀ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
          c * ((∫ ω, meanSquareIntegral f x ω ^ q ∂μ) ^ (1 / (2 * q))
                - C / Real.sqrt (Real.log x))
            ≤ (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) ^ (1 / (2 * q)) :=
  reduction_lower_meanSquareOf (by norm_num) (meanSquare_le_moment (Ω := Ω))

/-- **`RMF.reduction_lower_chaosShift` with its constants left free.**  Raising
`RMF.meanSquare_ge_chaosShift` to the `2q`-th power inside
`RMF.reduction_lower_meanSquare` fixes

`c = c₂\min(c₁,1)`,  `C = \max((1+C₁)/\min(c₁,1),\ C₂/\min(c₁,1))`,  `V₀ = 1`,

so `V₀` is already a numeral and the other two are formulas in the two sources' constants. -/
theorem reduction_lower_chaosShift_of_bounds {c₁ C₁ c₂ C₂ x₀ : ℝ}
    (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hc₂ : 0 < c₂)
    (hM :
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ x q V : ℝ, Real.exp 1 ≤ x → 2 / 3 ≤ q → q ≤ 1 → 0 ≤ V →
          4 * V / Real.log x ≤ 1 / 2 →
          c₁ * (∫ ω, chaosShift f x (4 * V / Real.log x) ω ^ q ∂μ)
              - C₁ * Real.exp (-(2 * V * q))
                  * ∫ ω, chaosShift f x (2 * V / Real.log x) ω ^ q ∂μ
            ≤ ∫ ω, meanSquareIntegral f x ω ^ q ∂μ)
    (hprop :
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
          c₂ * ((∫ ω, meanSquareIntegral f x ω ^ q ∂μ) ^ (1 / (2 * q))
                - C₂ / Real.sqrt (Real.log x))
            ≤ (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) ^ (1 / (2 * q))) :
    ∀ V : ℝ, 1 ≤ V → ∃ x₁ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ x q : ℝ, x₁ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
          c₂ * min c₁ 1 * ((∫ ω, chaosShift f x (4 * V / Real.log x) ω ^ q ∂μ) ^ (1 / (2 * q))
                - max ((1 + C₁) / min c₁ 1) (C₂ / min c₁ 1) / Real.exp V
                    * (∫ ω, chaosShift f x (2 * V / Real.log x) ω ^ q ∂μ)
                        ^ (1 / (2 * q))
                - max ((1 + C₁) / min c₁ 1) (C₂ / min c₁ 1) / Real.sqrt (Real.log x))
            ≤ (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) ^ (1 / (2 * q)) := by
  have hc₀0 : (0 : ℝ) < min c₁ 1 := lt_min hc₁ one_pos
  intro V hV
  refine ⟨max x₀ (Real.exp (8 * V)), fun f μ hf x q hx hq23 hq1 => ?_⟩
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  -- scales
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxV : Real.exp (8 * V) ≤ x := le_trans (le_max_right _ _) hx
  have hV0 : (0 : ℝ) ≤ V := by linarith
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxV
  have hL8V : 8 * V ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxV
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hxe : Real.exp 1 ≤ x := le_trans (Real.exp_le_exp.2 (by linarith)) hxV
  have hx1 : (1 : ℝ) ≤ x := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith [hxe]
  have hshift : 4 * V / Real.log x ≤ 1 / 2 := by
    rw [div_le_iff₀ hL0]
    linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hr0 : (0 : ℝ) < 1 / (2 * q) := by positivity
  have hr1 : 1 / (2 * q) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hlinv : (0 : ℝ) ≤ (Real.log x)⁻¹ := by positivity
  -- nonnegativity
  have hE4 : (0 : ℝ) ≤ ∫ ω, chaosShift (fun ω => compMultExtension fun p => X p ω) x
      (4 * V / Real.log x) ω ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (chaosShift_nonneg hlinv ω) _
  have hE2 : (0 : ℝ) ≤ ∫ ω, chaosShift (fun ω => compMultExtension fun p => X p ω) x
      (2 * V / Real.log x) ω ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (chaosShift_nonneg hlinv ω) _
  have hS0 : (0 : ℝ) ≤ ∫ ω, meanSquareIntegral (fun ω => compMultExtension fun p => X p ω)
      x ω ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (meanSquareIntegral_nonneg hx1 ω) _
  -- the `M`-chain, at the `2q`-th power
  have hMc := hM _ μ hX.isSteinhausRMF x q V hxe hq23 hq1 hV0 hshift
  -- `sub_zero` rather than `linarith`: the goal's integrands carry `V / ℓog x`, and
  -- linarith's denominator-clearing step cannot rewrite under the integral's binder
  have hthree := rpow_sub_three_le hS0 (mul_nonneg hc₁.le hE4)
    (mul_nonneg (mul_nonneg hC₁.le (Real.exp_pos _).le) hE2) le_rfl
    (by rw [sub_zero]; exact hMc) hr0.le hr1
  rw [Real.zero_rpow (ne_of_gt hr0), sub_zero, Real.mul_rpow hc₁.le hE4,
    Real.mul_rpow (mul_nonneg hC₁.le (Real.exp_pos _).le) hE2,
    Real.mul_rpow hC₁.le (Real.exp_pos _).le] at hthree
  have hexp : (Real.exp (-(2 * V * q))) ^ (1 / (2 * q)) = (Real.exp V)⁻¹ := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_neg]
    congr 1
    field_simp
  rw [hexp] at hthree
  -- the constants stay `q`-free
  have hK1 : min c₁ 1 ≤ c₁ ^ (1 / (2 * q)) := by
    rcases le_or_gt c₁ 1 with h | h
    · refine le_trans (min_le_left _ _) ?_
      calc c₁ = c₁ ^ (1 : ℝ) := (Real.rpow_one c₁).symm
        _ ≤ c₁ ^ (1 / (2 * q)) := Real.rpow_le_rpow_of_exponent_ge hc₁ h hr1
    · exact le_trans (min_le_right _ _) (Real.one_le_rpow h.le hr0.le)
  have hK2 : C₁ ^ (1 / (2 * q))
      ≤ min c₁ 1 * max ((1 + C₁) / min c₁ 1) (C₂ / min c₁ 1) := by
    refine le_trans (rpow_le_one_add hC₁.le hr0.le hr1) ?_
    have h := mul_le_mul_of_nonneg_left
      (le_max_left ((1 + C₁) / min c₁ 1) (C₂ / min c₁ 1)) hc₀0.le
    rwa [mul_div_cancel₀ _ (ne_of_gt hc₀0)] at h
  have hC₂' : C₂ ≤ min c₁ 1 * max ((1 + C₁) / min c₁ 1) (C₂ / min c₁ 1) := by
    have h := mul_le_mul_of_nonneg_left
      (le_max_right ((1 + C₁) / min c₁ 1) (C₂ / min c₁ 1)) hc₀0.le
    rwa [mul_div_cancel₀ _ (ne_of_gt hc₀0)] at h
  -- and the first bound
  have hP := hprop _ μ hX.isSteinhausRMF x q hxx₀ hq23 hq1
  exact prop3_arith2 (Real.rpow_nonneg hE4 _) (Real.rpow_nonneg hE2 _) (Real.exp_pos V)
    (Real.sqrt_pos.2 hL0) hc₂ hK1 hK2 hC₂' hthree hP

/-! ### From the unit window to Harper's

`RMF.chaosShift` reads the chaos over `[-1/2, 1/2]`, `RMF.chaosUnitShift` over
`[0, 1]`, and the chaos estimate is proved on the second because that is the window the
barrier controls.  `RMF.integral_rpow_window_eq` closes the gap: at any abscissa `≥ 1/2` and any
`q`, every unit window has the same `ω`-moment.  Rotating the family by `p^{-iτ}` moves the window
and is invisible to the expectation. -/

/-- The two windows have the same `q`-th moment. -/
lemma integral_rpow_chaosShift_eq {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {x σ q : ℝ} (hx : 2 ≤ x) (hσ : 0 ≤ σ) :
    (∫ ω, chaosShift (fun ω => compMultExtension fun p => X p ω) x σ ω ^ q ∂μ)
      = ∫ ω, chaosUnitShift (fun ω => compMultExtension fun p => X p ω) x σ ω ^ q ∂μ := by
  have hc : (0 : ℝ) ≤ (Real.log x)⁻¹ := inv_nonneg.2 (Real.log_nonneg (by linarith))
  have hσ' : (1 : ℝ) / 2 ≤ 1 / 2 + σ := by linarith
  have hW := integral_rpow_window_eq (σ := 1 / 2 + σ) hσ' hX (⌊x⌋₊ + 1) (-(1 : ℝ) / 2) q
  rw [show (-(1 : ℝ) / 2 + 1) = (1 / 2 : ℝ) by norm_num] at hW
  have hA : ∀ ω, chaosShift (fun ω => compMultExtension fun p => X p ω) x σ ω
      = (Real.log x)⁻¹ * ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ),
        ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (⌊x⌋₊ + 1)
          (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 := fun ω => by
    rw [chaosShift, intervalIntegral.integral_of_le (by norm_num)]
  have hB : ∀ ω, chaosUnitShift (fun ω => compMultExtension fun p => X p ω) x σ ω
      = (Real.log x)⁻¹ * ∫ h in Set.Ioc (0 : ℝ) 1,
        ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (⌊x⌋₊ + 1)
          (((1 / 2 + σ : ℝ) : ℂ) + (h : ℂ) * Complex.I) ω‖ ^ 2 := fun ω => by
    rw [chaosUnitShift, intervalIntegral.integral_of_le (by norm_num)]
    rfl
  have hpull : ∀ W : Ω → ℝ, (∀ ω, 0 ≤ W ω) →
      (∫ ω, ((Real.log x)⁻¹ * W ω) ^ q ∂μ) = ((Real.log x)⁻¹) ^ q * ∫ ω, W ω ^ q ∂μ := by
    intro W hW0
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => Real.mul_rpow hc (hW0 ω))
  simp only [hA, hB]
  rw [hpull _ (fun ω => setIntegral_nonneg measurableSet_Ioc fun _ _ => by positivity),
    hpull _ (fun ω => setIntegral_nonneg measurableSet_Ioc fun _ _ => by positivity), hW]

/-- **`RMF.exists_const_integral_chaosShift_rpow_le_of_top` with its constant left free.**
Trading the block count for `\log\log y` costs the factor `2` and nothing else, so the constant
here is twice the unit-shift chain's. -/
theorem le_const_integral_chaosShift_rpow_of_unitShift {D : ℕ} {C : ℝ} (hC : 0 < C)
    (H :
      ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
        ∀ x σ η q : ℝ, x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 1 →
          (∫ ω, chaosUnitShift
              (fun ω => compMultExtension fun p => Y p ω) x σ ω ^ q ∂ν)
            ≤ C * (1 + (1 - q) * Real.sqrt ((harperBlockCount D x - d : ℕ) : ℝ)) ^ (-q)) :
    ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ y₀ : ℝ,
    ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
      ∀ y σ η q : ℝ, y₀ ≤ y → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log y ≤ η →
        0 ≤ q → q ≤ 1 →
        (∫ ω, chaosShift (fun ω => compMultExtension fun p => X p ω) y σ ω ^ q ∂μ)
          ≤ 2 * C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q) := by
  intro d E₀ _ hEd
  obtain ⟨x₀, H⟩ := H d E₀ ‹_› hEd
  refine ⟨max (max x₀ 2) (max (Real.exp (Real.exp (2 * ((D : ℝ) + 1))))
    (Real.exp (Real.exp (4 * (d : ℝ))))), ?_⟩
  intro X μ hX y σ η q hy hσ0 hη0 hηE hσ hq0 hq1
  have hxx₀ : x₀ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hy2 : (2 : ℝ) ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hexp : Real.exp (Real.exp (2 * ((D : ℝ) + 1))) ≤ y :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hexpd : Real.exp (Real.exp (4 * (d : ℝ))) ≤ y :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : Real.exp (2 * ((D : ℝ) + 1)) ≤ Real.log y := (Real.le_log_iff_exp_le hy0).2 hexp
  have hlogy0 : (0 : ℝ) < Real.log y := lt_of_lt_of_le (Real.exp_pos _) hlogy
  have hL : 2 * ((D : ℝ) + 1) ≤ Real.log (Real.log y) :=
    (Real.le_log_iff_exp_le hlogy0).2 hlogy
  have hLd : 4 * (d : ℝ) ≤ Real.log (Real.log y) :=
    (Real.le_log_iff_exp_le hlogy0).2 ((Real.le_log_iff_exp_le hy0).2 hexpd)
  have hD : (D : ℝ) ≤ Real.log (Real.log y) := by linarith
  -- the block count is at least half of `\log\log y`, and after the drop at least a quarter
  have ht2 : Real.log (Real.log y) / 2 ≤ (harperBlockCount D y : ℝ) := by
    rw [cast_harperBlockCount hD]
    have hfl : Real.log (Real.log y) < (⌊Real.log (Real.log y)⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    linarith
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdle : d ≤ harperBlockCount D y := by
    have hc : ((d : ℕ) : ℝ) ≤ (harperBlockCount D y : ℝ) := by linarith
    exact_mod_cast hc
  have ht : Real.log (Real.log y) / 4 ≤ ((harperBlockCount D y - d : ℕ) : ℝ) := by
    rw [Nat.cast_sub hdle]
    linarith
  have htar := rpow_neg_target_le_of_quarter_le
    (t := ((harperBlockCount D y - d : ℕ) : ℝ)) (Λ := Real.log (Real.log y))
    (by linarith) hq0 hq1
  rw [integral_rpow_chaosShift_eq hX hy2 hσ0]
  calc (∫ ω, chaosUnitShift (fun ω => compMultExtension fun p => X p ω) y σ ω ^ q ∂μ)
      ≤ C * (1 + (1 - q) * Real.sqrt ((harperBlockCount D y - d : ℕ) : ℝ)) ^ (-q) :=
        H X μ hX y σ η q hxx₀ hσ0 hη0 hηE hσ hq0 hq1
    _ ≤ C * (2 * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q)) :=
        mul_le_mul_of_nonneg_left htar hC.le
    _ = 2 * C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q) := by ring

/-! ### The subtracted chaos term

`RMF.reduction_lower_chaosShift` subtracts `C e^{-V} (\int G_{2V}^q)^{1/(2q)}`.  Whether that is
harmless is a question about the bound on `\int G_{2V}^q`, and **two things about it have to be
right**: the constant must not grow with `V`, and the *shape* must be kept.

A constant carrying `e^{\kappa V}` with `\kappa > 1` would make the subtracted term diverge however
large `V` is taken.

The second is where a flat bound fails.  Both `\int G_{4V}^q` and `\int G_{2V}^q` are of order
`W^{-q}` with `W = 1 + (1-q)\sqrt{\log\log x}`, so the main term `A^{1/(2q)}` is of order
`W^{-1/2}` and **tends to zero**.  A subtracted term bounded by a constant times `e^{-V}` is
therefore eventually *larger* than the main term for every fixed `V`.  Keeping `W^{-q}` puts both
terms at the same order, and there a large `V` makes the subtracted term small. -/

/-- **The Euler-product moment at a shifted abscissa, with the constants of the `σ = 0` chain**:
`C'` comes before `d` and `E₀ ≤ e^d`, so it is free of `E₀`.  The barrier is stopped `d` blocks
short of the top while the tilt stays there, so the tower runs at the absolute variance bracket
`[1/16, 9/2]`; the block-count trade costs a factor `2`, since `t - d ≥ ¼ log log y` once
`log log y ≥ 4d`.  This is the bound the lower reduction's subtracted term needs, at
`σ = 2V/log x`. -/
theorem exists_const_integral_chaosShift_rpow_le_of_top :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ y₀ : ℝ,
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
        ∀ y σ η q : ℝ, y₀ ≤ y → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log y ≤ η →
          0 ≤ q → q ≤ 1 →
          (∫ ω, chaosShift (fun ω => compMultExtension fun p => X p ω) y σ ω ^ q ∂μ)
            ≤ C' * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q) := by
  obtain ⟨D, C, hC, H⟩ :=
    exists_const_integral_chaosUnitShift_rpow_le_of_top (Ω := Ω)
  exact ⟨2 * C, by linarith, le_const_integral_chaosShift_rpow_of_unitShift hC H⟩

/-- **`RMF.exists_const_integral_chaosShift_rpow_le_shift` with its constant left free.**
Specialising to `σ = 2V/\log y` and choosing the drop `d` by `RMF.exists_drop` does not move the
constant at all. -/
theorem le_const_integral_chaosShift_rpow_shift_of_top {C' : ℝ}
    (H :
      ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ y₀ : ℝ,
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
        ∀ y σ η q : ℝ, y₀ ≤ y → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log y ≤ η →
          0 ≤ q → q ≤ 1 →
          (∫ ω, chaosShift (fun ω => compMultExtension fun p => X p ω) y σ ω ^ q ∂μ)
            ≤ C' * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q)) :
    ∀ V : ℝ, 0 ≤ V → ∃ y₀ : ℝ,
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
        ∀ y q : ℝ, y₀ ≤ y → 0 ≤ q → q ≤ 1 →
          (∫ ω, chaosShift (fun ω => compMultExtension fun p => X p ω) y
              (2 * V / Real.log y) ω ^ q ∂μ)
            ≤ C' * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q) := by
  intro V hV
  obtain ⟨d, hd⟩ := exists_drop (2 * V)
  obtain ⟨y₀, H⟩ := H d (2 * V) (by linarith) (le_trans (le_max_left _ _) hd)
  refine ⟨max y₀ 2, ?_⟩
  intro X μ hX y q hy hq0 hq1
  have hyy₀ : y₀ ≤ y := le_trans (le_max_left _ _) hy
  have hy2 : (2 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
  have hlog0 : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hσ0 : (0 : ℝ) ≤ 2 * V / Real.log y := by positivity
  have hσ : |2 * V / Real.log y| * Real.log y ≤ 2 * V := by
    rw [abs_of_nonneg hσ0, div_mul_cancel₀ _ (ne_of_gt hlog0)]
  exact H X μ hX y (2 * V / Real.log y) (2 * V) q hyy₀ hσ0 (by linarith) le_rfl hσ hq0 hq1

/-- **The chaos moment at the shift the lower reduction subtracts at**:
`RMF.exists_const_integral_chaosShift_rpow_le_of_top` at `σ = 2V/log y` and `η = E₀ = 2V`, with
the drop `d` from `RMF.exists_drop`.  The constant has **no `V` in it**.  The shape factor
`W^{-q}` is kept: discarding it (`W^{-q} ≤ 1`) gives a flat bound that is useless downstream, as
the section note explains. -/
theorem exists_const_integral_chaosShift_rpow_le_shift :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ V : ℝ, 0 ≤ V → ∃ y₀ : ℝ,
        ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
          ∀ y q : ℝ, y₀ ≤ y → 0 ≤ q → q ≤ 1 →
            (∫ ω, chaosShift (fun ω => compMultExtension fun p => X p ω) y
                (2 * V / Real.log y) ω ^ q ∂μ)
              ≤ C' * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q) := by
  obtain ⟨C', hC', H⟩ := exists_const_integral_chaosShift_rpow_le_of_top (Ω := Ω)
  exact ⟨C', hC', le_const_integral_chaosShift_rpow_shift_of_top H⟩

/-- **`RMF.reduction_lower_chaosShift_absorbed` with its three constants left free.**  Absorbing
the two subtracted terms into one does not touch `c` or `V₀` and takes the collar constant to
`C·\max(1, C') + C`, so a bound on the reduction's `C` and on the shift's `C'` is a bound on the
collar. -/
theorem reduction_lower_chaosShift_absorbed_of_bounds {c C V₀ C' : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hV₀ : 0 < V₀) (hC' : 0 < C')
    (H :
      ∀ V : ℝ, V₀ ≤ V → ∃ x₀ : ℝ,
        ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
          ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
            c * ((∫ ω, chaosShift f x (4 * V / Real.log x) ω ^ q ∂μ) ^ (1 / (2 * q))
                  - C / Real.exp V
                      * (∫ ω, chaosShift f x (2 * V / Real.log x) ω ^ q ∂μ)
                          ^ (1 / (2 * q))
                  - C / Real.sqrt (Real.log x))
              ≤ (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) ^ (1 / (2 * q)))
    (HB :
      ∀ V : ℝ, 0 ≤ V → ∃ y₀ : ℝ,
        ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
          ∀ y q : ℝ, y₀ ≤ y → 0 ≤ q → q ≤ 1 →
            (∫ ω, chaosShift (fun ω => compMultExtension fun p => X p ω) y
                (2 * V / Real.log y) ω ^ q ∂μ)
              ≤ C' * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q)) :
    ∀ V : ℝ, V₀ ≤ V → ∃ x₀ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
          c * ((∫ ω, chaosShift f x (4 * V / Real.log x) ω ^ q ∂μ) ^ (1 / (2 * q))
                - (C * max 1 C' + C) / Real.exp V
                    * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ))
            ≤ (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) ^ (1 / (2 * q)) := by
  intro V hV
  have hV0 : (0 : ℝ) ≤ V := le_trans hV₀.le hV
  obtain ⟨x₁, H⟩ := H V hV
  obtain ⟨y₀, HB⟩ := HB V hV0
  refine ⟨max (max x₁ y₀) (Real.exp (Real.exp (4 * V + 16))), ?_⟩
  intro f μ hf x q hx hq23 hq1
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have hxx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hyy₀ : y₀ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp (Real.exp (4 * V + 16)) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hlogx : Real.exp (4 * V + 16) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe
  have hlogx0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hlogx
  have hL : 4 * V + 16 ≤ Real.log (Real.log x) := (Real.le_log_iff_exp_le hlogx0).2 hlogx
  have hq0 : (0 : ℝ) < q := by linarith
  have hr0 : (0 : ℝ) ≤ 1 / (2 * q) := by positivity
  have hr1 : 1 / (2 * q) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  -- the shape factor and its two comparisons
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log (Real.log x)) := Real.sqrt_nonneg _
  have hW1 : (1 : ℝ) ≤ 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) := by
    nlinarith
  have hW0 : (0 : ℝ) < 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) := by linarith
  have hWle : 1 + (1 - q) * Real.sqrt (Real.log (Real.log x))
      ≤ 1 + Real.sqrt (Real.log (Real.log x)) := by nlinarith
  have hWr0 : (0 : ℝ) ≤ (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_nonneg hW0.le _
  -- `e^V(1 + √L) ≤ √(\log x)`, which is what the `x`-threshold was chosen for
  have hsqrtL : Real.sqrt (Real.log (Real.log x)) ≤ Real.log (Real.log x) / 4 := by
    have hle : Real.log (Real.log x) ≤ (Real.log (Real.log x) / 4) ^ 2 := by nlinarith
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (by linarith)] at h
  have hsqrtlogx : Real.sqrt (Real.log x) = Real.exp (Real.log (Real.log x) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hlogx0]
    congr 1
    ring
  have hev : Real.exp V * (1 + Real.sqrt (Real.log (Real.log x))) ≤ Real.sqrt (Real.log x) := by
    have hq1' : Real.exp V ≤ Real.exp (Real.log (Real.log x) / 4) :=
      Real.exp_le_exp.2 (by linarith)
    have hq2 : 1 + Real.sqrt (Real.log (Real.log x))
        ≤ Real.exp (Real.log (Real.log x) / 4) := by
      have := Real.add_one_le_exp (Real.log (Real.log x) / 4)
      linarith
    have hpos1 : (0 : ℝ) < Real.exp (Real.log (Real.log x) / 4) := Real.exp_pos _
    calc Real.exp V * (1 + Real.sqrt (Real.log (Real.log x)))
        ≤ Real.exp (Real.log (Real.log x) / 4)
            * Real.exp (Real.log (Real.log x) / 4) := by
          refine mul_le_mul hq1' hq2 (by linarith) hpos1.le
      _ = Real.exp (Real.log (Real.log x) / 2) := by
          rw [← Real.exp_add]; ring_nf
      _ = Real.sqrt (Real.log x) := hsqrtlogx.symm
  have hsq0 : (0 : ℝ) < Real.sqrt (Real.log x) :=
    lt_of_lt_of_le (by positivity) hev
  -- the collar term, at the shape
  have hcollar : C / Real.sqrt (Real.log x)
      ≤ C / Real.exp V
        * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ) := by
    have hmono : (1 + Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ)
        ≤ (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hW0 hWle (by norm_num)
    have hb1 : (1 : ℝ) ≤ 1 + Real.sqrt (Real.log (Real.log x)) := by linarith
    have hhalf : (1 + Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ)
        = (Real.sqrt (1 + Real.sqrt (Real.log (Real.log x))))⁻¹ := by
      rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 + Real.sqrt (Real.log (Real.log x))),
        ← Real.sqrt_eq_rpow]
    have hsr : Real.sqrt (1 + Real.sqrt (Real.log (Real.log x)))
        ≤ 1 + Real.sqrt (Real.log (Real.log x)) := by
      have h := Real.sqrt_le_sqrt (show (1 : ℝ) + Real.sqrt (Real.log (Real.log x))
        ≤ (1 + Real.sqrt (Real.log (Real.log x))) ^ 2 by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at h
    have hsrpos : (0 : ℝ) < Real.sqrt (1 + Real.sqrt (Real.log (Real.log x))) :=
      Real.sqrt_pos.2 (by linarith)
    have hgoal : Real.exp V * Real.sqrt (1 + Real.sqrt (Real.log (Real.log x)))
        ≤ Real.sqrt (Real.log x) :=
      le_trans (mul_le_mul_of_nonneg_left hsr (Real.exp_pos V).le) hev
    have hstep : C / Real.sqrt (Real.log x)
        ≤ C / Real.exp V * (1 + Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ) := by
      have hrw : C / Real.exp V * (Real.sqrt (1 + Real.sqrt (Real.log (Real.log x))))⁻¹
          = C / (Real.exp V * Real.sqrt (1 + Real.sqrt (Real.log (Real.log x)))) := by
        field_simp
      rw [hhalf, hrw, div_le_div_iff₀ hsq0 (by positivity)]
      exact mul_le_mul_of_nonneg_left hgoal hC.le
    exact hstep.trans (mul_le_mul_of_nonneg_left hmono (by positivity))
  -- the chaos term, at the shape
  have hlinv : (0 : ℝ) ≤ (Real.log x)⁻¹ := by positivity
  have hE2 : (0 : ℝ) ≤ ∫ ω, chaosShift (fun ω => compMultExtension fun p => X p ω) x
      (2 * V / Real.log x) ω ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (chaosShift_nonneg hlinv ω) _
  have hB := HB X μ hX x q hyy₀ hq0.le hq1
  have hBr : (∫ ω, chaosShift (fun ω => compMultExtension fun p => X p ω) x
        (2 * V / Real.log x) ω ^ q ∂μ) ^ (1 / (2 * q))
      ≤ max 1 C' * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ) := by
    have hstep := Real.rpow_le_rpow hE2 hB hr0
    rw [Real.mul_rpow hC'.le (Real.rpow_nonneg hW0.le _), ← Real.rpow_mul hW0.le,
      show -q * (1 / (2 * q)) = -(1 / 2 : ℝ) by field_simp] at hstep
    exact hstep.trans (mul_le_mul_of_nonneg_right (rpow_le_max_one hC' hr0 hr1) hWr0)
  -- the two together
  have hkey : C / Real.exp V * (∫ ω, chaosShift
        (fun ω => compMultExtension fun p => X p ω) x (2 * V / Real.log x) ω ^ q ∂μ)
          ^ (1 / (2 * q)) + C / Real.sqrt (Real.log x)
      ≤ (C * max 1 C' + C) / Real.exp V
          * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hBr (by positivity : (0 : ℝ) ≤ C / Real.exp V)
    have h4 : C / Real.exp V
          * (max 1 C' * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ))
        + C / Real.exp V
          * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ)
        = (C * max 1 C' + C) / Real.exp V
          * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ) := by
      field_simp
    linarith [hcollar]
  exact le_trans (mul_le_mul_of_nonneg_left (by linarith) hc.le)
    (H _ μ hX.isSteinhausRMF x q hxx₁ hq23 hq1)

/-- **Harper's Proposition 3, second bound** — the lower-bound counterpart of
`RMF.reduction_upper_unitIntegral`.  For large `V`, uniformly for `2/3 ≤ q ≤ 1`,

`‖∑_{n≤x} f(n)‖_{2q} ≫ √(x/log x)( ‖∫_{-1/2}^{1/2}|F(1/2+4V/log x+it)|²dt‖_q^{1/2}`
`  - (C/e^V)‖∫_{-1/2}^{1/2}|F(1/2+2V/log x+it)|²dt‖_q^{1/2} - C )`,

divided through by `√x`.  `V` is chosen first and the threshold `x₀` may depend on it, which is how
Harper uses it; letting `V` grow with `x` is not claimed, since the shift `4V/log x` has to stay
small.  The proof feeds `RMF.meanSquare_ge_chaosShift` through `RMF.reduction_lower_meanSquare` at
the `2q`-th power, which turns `e^{-2Vq}` into Harper's `e^{-V}`. -/
theorem reduction_lower_chaosShift :
    ∃ c C V₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < V₀ ∧
      ∀ V : ℝ, V₀ ≤ V → ∃ x₀ : ℝ,
        ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
          ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
            c * ((∫ ω, chaosShift f x (4 * V / Real.log x) ω ^ q ∂μ) ^ (1 / (2 * q))
                  - C / Real.exp V
                      * (∫ ω, chaosShift f x (2 * V / Real.log x) ω ^ q ∂μ)
                          ^ (1 / (2 * q))
                  - C / Real.sqrt (Real.log x))
              ≤ (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) ^ (1 / (2 * q)) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hM⟩ := meanSquare_ge_chaosShift (Ω := Ω)
  obtain ⟨c₂, C₂, hc₂, hC₂, x₀, hprop⟩ := reduction_lower_meanSquare (Ω := Ω)
  have hc₀0 : (0 : ℝ) < min c₁ 1 := lt_min hc₁ one_pos
  exact ⟨c₂ * min c₁ 1, max ((1 + C₁) / min c₁ 1) (C₂ / min c₁ 1), 1, by positivity,
    lt_of_lt_of_le (by positivity : (0 : ℝ) < C₂ / min c₁ 1) (le_max_right _ _), one_pos,
    reduction_lower_chaosShift_of_bounds hc₁ hC₁ hc₂ hM hprop⟩

/-- **The lower reduction with its subtracted term absorbed.**  `RMF.reduction_lower_chaosShift`
reads `c ( A^{1/(2q)} - C e^{-V} B^{1/(2q)} - C (\log x)^{-1/2} ) \le (E |S_x|^{2q})^{1/(2q)}`
with `A = \int G_{4V}^q` and `B = \int G_{2V}^q`.  Both subtracted terms are bounded here by a
single `C_0 e^{-V} W^{-1/2}`, `W = 1 + (1-q)\sqrt{\log\log x}`, with `C_0` independent of `V`,
`f`, `μ`, `x` and `q`:

* `B^{1/(2q)} \le \max(1,C') W^{-1/2}`, since `B \le C' W^{-q}` and `1/(2q) \in [1/2,3/4]`;
* `(\log x)^{-1/2} \le e^{-V} W^{-1/2}`, since `W \le 1 + \sqrt{L}` and
  `\log\log x \ge 4V + 16` forces `e^V(1 + \sqrt L) \le \sqrt{\log x}`.

Both terms are then of the same order as the main one, `W^{-1/2}`, so a large `V` shrinks the
subtracted term relative to `A^{1/(2q)}`.  The lower bound `A^{1/(2q)} \gg W^{-1/2}` is
`RMF.exists_le_integral_rpow_chaosShift` (Paley–Zygmund with Harper's Key Proposition 5), and
`RMF.exists_le_integral_rpow_normalisedSum` composes the two. -/
theorem reduction_lower_chaosShift_absorbed :
    ∃ c C₀ V₀ : ℝ, 0 < c ∧ 0 < C₀ ∧ 0 < V₀ ∧
      ∀ V : ℝ, V₀ ≤ V → ∃ x₀ : ℝ,
        ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
          ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
            c * ((∫ ω, chaosShift f x (4 * V / Real.log x) ω ^ q ∂μ) ^ (1 / (2 * q))
                  - C₀ / Real.exp V
                      * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ))
              ≤ (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) ^ (1 / (2 * q)) := by
  obtain ⟨c, C, V₀, hc, hC, hV₀, H⟩ := reduction_lower_chaosShift (Ω := Ω)
  obtain ⟨C', hC', HB⟩ := exists_const_integral_chaosShift_rpow_le_shift (Ω := Ω)
  exact ⟨c, C * max 1 C' + C, V₀, hc, by positivity, hV₀,
    reduction_lower_chaosShift_absorbed_of_bounds hc hC hV₀ hC' H HB⟩

end RMF
