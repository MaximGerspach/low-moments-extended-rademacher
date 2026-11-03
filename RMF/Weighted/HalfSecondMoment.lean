/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.HalfEvents
import RMF.Weighted.MesoscopicChaos
import RMF.Probability.RestrictedSecondMoment
import RMF.Probability.RademacherRestrictedSecondMoment

/-!
# The barriered second moment on a mesoscopic window

Proposition 6.4 of the paper:

`E[(∫_{h ∈ [e^{-(k+1)}, e^{-k}]} 1_{L(k,h)} |F_{(k,y)}(½+σ+ih)|² dh)²] ≪ e^{2t-4k}/(t-k)`,

for the barrier `L(k,h)` of `RMF.halfBarrier`, at any barrier constants `(j₀, C₁, a, B)`:
`RMF.exists_integral_sq_setIntegral_halfBarrier_le`.

The square expands into a double integral over pairs of heights of the pair integrand
`E[1_{L h₁}‖F(h₁)‖²·1_{L h₂}‖F(h₂)‖²]`, which is bounded shell by shell in `|h₁ - h₂|`.  Each shell
splits the primes at a scale `M` past which the two heights have decorrelated: below `M` the
barrier's upper edge bounds one of the two block products outright, above it the two-point moment
is `O(e^{2(t-M)})`.  Far from the diagonal that loses too much, and the barrier is kept instead, as
a pair barrier whose tilted measure is Harper's Proposition 7 on a window
(`RMF.exists_proposition7_upper_rademacher_window`).
-/

open MeasureTheory

namespace RMF

/-! ### Bookkeeping on the block ladder

`RMF.scaleCut θ = ⌊e^{e^θ}⌋₊ + 1`, and at an integer offset `k` the primes in
`[scaleCut k, scaleCut (k + d))` are exactly the blocks `0, …, d - 1` of `RMF.halfBlock X k σ h`,
so `log‖F_{[scaleCut k, scaleCut (k+d))}‖` is the walk at depth `d`.  On the barrier `L(k,h)` that
walk is at most `RMF.halfBarrierTop` at every depth up to `t - k`. -/

/-- The cut at the top of block `j - 1` at offset `θ`, as a `scaleCut`. -/
lemma scaleCut_add (θ : ℝ) (j : ℕ) : scaleCut (θ + j) = ⌊blockScale θ j⌋₊ + 1 := by
  rw [scaleCut, ← blockScale_add, zero_add]

lemma scaleCut_mono {θ θ' : ℝ} (h : θ ≤ θ') : scaleCut θ ≤ scaleCut θ' := by
  unfold scaleCut blockScale
  refine Nat.add_le_add_right (Nat.floor_le_floor ?_) 1
  exact Real.exp_le_exp.2 (Real.exp_le_exp.2 (by push_cast; linarith))

/-- **The walk is the logarithm of the block product.**  At offset `θ`, the walk of
`RMF.halfBlock` to depth `j` is `log‖F_{[scaleCut θ, scaleCut (θ+j))}(½+σ+ih)‖`, wherever the values
at those primes are bounded by one. -/
lemma log_norm_randomEulerProductIco_eq_walk_halfBlock {Ω : Type*} {X : ℕ → Ω → ℂ}
    (θ σ h : ℝ) (j : ℕ) (hσ : 0 ≤ σ) {ω : Ω}
    (hω : ∀ p ∈ primesIco (scaleCut θ) (scaleCut (θ + j)), ‖X p ω‖ ≤ 1) :
    Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut θ) (scaleCut (θ + j)) (shiftLine σ h) ω‖
      = walk (halfBlock X θ σ h) j ω := by
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  rw [scaleCut_add] at hω ⊢
  exact log_norm_randomEulerProductIco_sqfree_eq_walk θ j hs hω

/-- **The upper edge of the barrier at depth `d`**: `C₁` for the first `j₀` steps, then Harper's
`a + (d - j₀) - 2 log(d - j₀)` on top of `C₁`. -/
noncomputable def halfBarrierTop (j₀ : ℕ) (C₁ a : ℝ) (d : ℕ) : ℝ :=
  if d ≤ j₀ then C₁ else C₁ + a + ((d - j₀ : ℕ) : ℝ) + harperHf (d - j₀)

/-- **On `L(k,h)` the walk from `k` is below `RMF.halfBarrierTop`** at every depth up to `t - k`:
the first `j₀` steps by the box, the rest by the tube, added at `j₀`. -/
lemma walk_le_halfBarrierTop {Ω : Type*} {X : ℕ → Ω → ℂ} {σ h : ℝ} {k j₀ t : ℕ}
    {C₁ a B : ℝ} (hC₁ : 0 ≤ C₁) {ω : Ω} (hω : ω ∈ halfBarrier X σ h k j₀ t C₁ a B) {d : ℕ}
    (hd : d ≤ t - k) :
    walk (halfBlock X k σ h) d ω ≤ halfBarrierTop j₀ C₁ a d := by
  obtain ⟨h₀, h₁⟩ := hω
  have hbox : ∀ j, j ≤ j₀ → walk (halfBlock X k σ h) j ω ≤ C₁ := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · simp only [walk_apply, Finset.range_zero, Finset.sum_empty]
      exact hC₁
    · exact (h₀ j hj1 hj).2
  unfold halfBarrierTop
  split_ifs with hdj
  · exact hbox d hdj
  · have hsplit : walk (halfBlock X k σ h) d ω
        = walk (halfBlock X k σ h) j₀ ω + walk (halfBlock X ((k : ℝ) + j₀) σ h) (d - j₀) ω := by
      have hfun : halfBlock X ((k : ℝ) + j₀) σ h = fun m => halfBlock X k σ h (m + j₀) := by
        funext m ω'
        simp only [halfBlock]
        rw [primeBlockSub_add]
      rw [hfun, walk_shift, show j₀ + (d - j₀) = d from by omega]
      ring
    have htube := (h₁ (d - j₀) (by omega) (by omega)).2
    rw [hsplit]
    linarith [hbox j₀ le_rfl]

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The square of the window integral, expanded

`E[(∫_W 1_{L h}‖F_{[z,y)}(h)‖² dh)²] = ∫_W ∫_W E[1_{L h₁}‖F(h₁)‖² · 1_{L h₂}‖F(h₂)‖²]`, the block
product's twin of `RMF.integral_sq_setIntegral_indicator_normSq_sqfree_eq`, by the same two swaps.
Integrability is free for the same reason: on the unimodularity event the block product is at most
`∏(1 + p^{-(½+σ)})` at every height (`RMF.ae_forall_norm_randomEulerProductIco_mem_Icc`). -/

/-- **`L(k,h)` is jointly measurable in `(ω, h)`**: both of its parts are block barriers, and
`RMF.measurableSet_prod_barrierEventAdd` covers each. -/
lemma measurableSet_prod_halfBarrier {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (σ : ℝ) (k j₀ t : ℕ) (C₁ a B : ℝ) :
    MeasurableSet {q : Ω × ℝ | q.1 ∈ halfBarrier X σ q.2 k j₀ t C₁ a B} :=
  (measurableSet_prod_barrierEventAdd hX (k : ℝ) σ j₀ _ _).inter
    (measurableSet_prod_barrierEventAdd hX ((k : ℝ) + j₀) σ (t - k - j₀) _ _)

/-- The restricted block weight is bounded on the line `Re s = ½ + σ`, uniformly in the height,
off one null set. -/
lemma ae_forall_norm_indicator_normSq_Ico_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z y : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (L : ℝ → Set Ω) :
    ∀ᵐ ω ∂μ, ∀ h : ℝ, ‖Set.indicator (L h)
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ h) ω‖ ^ 2) ω‖
      ≤ (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 := by
  filter_upwards [ae_forall_norm_randomEulerProductIco_mem_Icc hX z y (c := 1 / 2 + σ)
    (by linarith)] with ω hω h
  have hb := (hω (shiftLine σ h) (re_shiftLine σ h)).2
  by_cases hmem : ω ∈ L h
  · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  · rw [Set.indicator_of_notMem hmem, norm_zero]
    positivity

/-- **One swap**, for the block product: for a weight `ψ` bounded and measurable in `ω`,
`E[ψ·∫_W 1_{L h}‖F(h)‖² dh] = ∫_W E[ψ·1_{L h}‖F(h)‖²] dh`. -/
theorem integral_mul_setIntegral_indicator_normSq_Ico_eq {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z y : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (L : ℝ → Set Ω)
    (hSmeas : MeasurableSet {q : Ω × ℝ | q.1 ∈ L q.2}) {W : Set ℝ} (hWfin : volume W ≠ ⊤)
    (ψ : Ω → ℝ) (hψm : AEStronglyMeasurable ψ μ) {c : ℝ} (hψb : ∀ᵐ ω ∂μ, ‖ψ ω‖ ≤ c) :
    (∫ ω, ψ ω * (∫ h in W, Set.indicator (L h)
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ h) ω‖ ^ 2) ω) ∂μ)
      = ∫ h in W, ∫ ω, ψ ω * Set.indicator (L h)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ h) ω‖ ^ 2) ω ∂μ := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hWfin⟩
  have hbase := integrable_uncurry_indicator_normSq_primesIco hX z y hσ hWfin L hSmeas
  have hψprod : AEStronglyMeasurable (fun q : Ω × ℝ => ψ q.1) (μ.prod (volume.restrict W)) :=
    hψm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hψbprod : ∀ᵐ q ∂(μ.prod (volume.restrict W)), ‖ψ q.1‖ ≤ c :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hψb
  have hInt : Integrable (Function.uncurry fun (ω : Ω) (h : ℝ) => ψ ω * Set.indicator (L h)
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ h) ω‖ ^ 2) ω) (μ.prod (volume.restrict W)) :=
    hbase.bdd_mul hψprod hψbprod
  rw [← integral_integral_swap hInt]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (integral_const_mul _ _).symm)

/-- **The expansion**: `E[(∫_W 1_{L h}‖F(h)‖² dh)²] = ∫_W ∫_W E[1_{L h₁}‖F(h₁)‖²·1_{L h₂}‖F(h₂)‖²]`
for the block product `F = F_{[z,y)}`. -/
theorem integral_sq_setIntegral_indicator_normSq_Ico_eq {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z y : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (L : ℝ → Set Ω)
    (hLmeas : ∀ h, MeasurableSet (L h)) (hSmeas : MeasurableSet {q : Ω × ℝ | q.1 ∈ L q.2})
    {W : Set ℝ} (hWfin : volume W ≠ ⊤) :
    (∫ ω, (∫ h in W, Set.indicator (L h)
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ h) ω‖ ^ 2) ω) ^ 2 ∂μ)
      = ∫ h₁ in W, ∫ h₂ in W, ∫ ω, Set.indicator (L h₁)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ h₁) ω‖ ^ 2) ω
          * Set.indicator (L h₂)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ := by
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  set g : ℝ → Ω → ℝ := fun h ω =>
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
      (shiftLine σ h) ω‖ ^ 2 with hgdef
  have hbase := integrable_uncurry_indicator_normSq_primesIco hX z y hσ hWfin L hSmeas
  have hbnd := ae_forall_norm_indicator_normSq_Ico_le hX z y hσ L
  -- the outer weight, bounded because the integrand is and `W` has finite measure
  have hXm : AEStronglyMeasurable (fun ω => ∫ h in W, Set.indicator (L h) (g h) ω) μ :=
    hbase.integral_prod_left.aestronglyMeasurable
  have hXb : ∀ᵐ ω ∂μ, ‖∫ h in W, Set.indicator (L h) (g h) ω‖
      ≤ (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 * volume.real W := by
    filter_upwards [hbnd] with ω hω
    exact norm_setIntegral_le_of_norm_le_const (lt_of_le_of_ne le_top hWfin) fun h _ => hω h
  have hexp : (∫ ω, (∫ h in W, Set.indicator (L h) (g h) ω) ^ 2 ∂μ)
      = ∫ ω, (∫ h in W, Set.indicator (L h) (g h) ω)
          * (∫ h in W, Set.indicator (L h) (g h) ω) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => sq _)
  rw [hexp, integral_mul_setIntegral_indicator_normSq_Ico_eq hX z y hσ L hSmeas hWfin _ hXm hXb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h₁ => ?_)
  have hφm : AEStronglyMeasurable (fun ω => Set.indicator (L h₁) (g h₁) ω) μ :=
    ((hf'.integrable_norm_randomEulerProductIco_sq z y (shiftLine σ h₁)).indicator
      (hLmeas h₁)).aestronglyMeasurable
  have hφb : ∀ᵐ ω ∂μ, ‖Set.indicator (L h₁) (g h₁) ω‖
      ≤ (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 := by
    filter_upwards [hbnd] with ω hω
    exact hω h₁
  calc (∫ ω, (∫ h₂ in W, Set.indicator (L h₂) (g h₂) ω) * Set.indicator (L h₁) (g h₁) ω ∂μ)
      = ∫ ω, Set.indicator (L h₁) (g h₁) ω * (∫ h₂ in W, Set.indicator (L h₂) (g h₂) ω) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
    _ = ∫ h₂ in W, ∫ ω, Set.indicator (L h₁) (g h₁) ω * Set.indicator (L h₂) (g h₂) ω ∂μ :=
        integral_mul_setIntegral_indicator_normSq_Ico_eq hX z y hσ L hSmeas hWfin _ hφm hφb

/-! ### The moment inputs

Three bounds on the moments of the block product above a scale `M`, none of which sees the
barrier:
* the one-point moment over `[scaleCut k, scaleCut M)` is `≤ e^{M-k+1}`, by Mertens;
* the pair moment over `[scaleCut M, y)` is `≪ e^{2(t-M)}` once `|h₁-h₂|e^M ≥ 2`
  (`RMF.exists_integral_normSq_high_le_rademacher_at`, truncated at `RMF.harperTruncation σ`);
* the pair moment over `[scaleCut M, y)` is `≪ e^{4(t-M)}` once only `(h₁+h₂)e^M ≥ 2`
  (`RMF.exists_integral_normSq_pairIco_split_le_rademacher_at`), which at `M = t` is a constant.
The truncation `e^{1/(2σ)}` is at scale `log(1/(2σ)) = t + O(1)`, because `σe^t ∈ [e^{-6}, 1/10e]`:
that is where the `σ`-damping ends every sum, and it is why no bound depends on `y`. -/

/-- `2 ≤ e^{e^θ}` for `θ ≥ 0`. -/
lemma two_le_blockScale_zero {θ : ℝ} (hθ : 0 ≤ θ) : (2 : ℝ) ≤ blockScale θ 0 := by
  simp only [blockScale, Nat.cast_zero, zero_add]
  have h1 : (1 : ℝ) ≤ Real.exp θ := Real.one_le_exp hθ
  have h2 : Real.exp 1 ≤ Real.exp (Real.exp θ) := Real.exp_le_exp.2 h1
  linarith [Real.exp_one_gt_d9]

/-- `log log e^{e^θ} = θ`. -/
lemma log_log_blockScale_zero (θ : ℝ) : Real.log (Real.log (blockScale θ 0)) = θ := by
  rw [log_blockScale, Real.log_exp]
  push_cast
  ring

/-- **The one-point moment over `[scaleCut k, scaleCut M)` is at most `e^{M-k+1}`**: the moment is
`∏(1 + p^{-1-2σ}) ≤ exp ∑ 1/p`, and by Mertens the sum over `e^{e^k} < p ≤ e^{e^M}` is
`M - k + O(e^{-k})`. -/
lemma integral_normSq_Ico_scaleCut_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {k M : ℕ} (hk : 20 ≤ k) (hkM : k ≤ M) {σ h : ℝ}
    (hσ : 0 ≤ σ) :
    ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut k) (scaleCut M) (shiftLine σ h) ω‖ ^ 2 ∂μ
      ≤ Real.exp ((M : ℝ) - k + 1) := by
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  refine le_trans (hf.integral_norm_randomEulerProductIco_sq_le _ _ _) (Real.exp_le_exp.2 ?_)
  rw [re_shiftLine]
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkMR : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hkM
  have hx2 : (2 : ℝ) ≤ blockScale (k : ℝ) 0 := two_le_blockScale_zero hk0
  have hxy : blockScale (k : ℝ) 0 ≤ blockScale (M : ℝ) 0 := by
    simp only [blockScale, Nat.cast_zero, zero_add]
    exact Real.exp_le_exp.2 (Real.exp_le_exp.2 hkMR)
  have hmert := abs_sum_prime_Ioc_inv_sub_log_log_sub_le _ _ hx2 hxy
  rw [filter_prime_Ioc_eq_primesIco, log_log_blockScale_zero, log_log_blockScale_zero] at hmert
  have h20 : 20 / Real.log (blockScale (k : ℝ) 0) ≤ 1 := by
    rw [log_blockScale, div_le_one (Real.exp_pos _)]
    have hkR : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    push_cast
    linarith [Real.add_one_le_exp ((0 : ℝ) + k)]
  have hterm : ∀ p ∈ primesIco (scaleCut (k : ℝ)) (scaleCut (M : ℝ)),
      ((p : ℕ) : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ (1 : ℝ) / p := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (prime_of_mem_primesIco hp).one_lt.le
    calc ((p : ℕ) : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ = (1 : ℝ) / p := by rw [Real.rpow_neg_one, one_div]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have habs := (abs_le.1 hmert).2
  unfold scaleCut
  linarith

/-- The cut at any scale up to `t` lies below the truncation `⌈e^{1/(2σ)}⌉`, since
`e^t ≤ 1/(10eσ) < 1/(2σ)`. -/
lemma scaleCut_le_harperTruncation {M t : ℕ} (hMt : M ≤ t) {σ : ℝ} (hσ : 0 < σ)
    (htop : σ * Real.exp ((t : ℝ) + 1) ≤ 1 / 10) : scaleCut (M : ℝ) ≤ harperTruncation σ := by
  have hMtR : (M : ℝ) ≤ (t : ℝ) := by exact_mod_cast hMt
  have het : Real.exp (M : ℝ) < 1 / (2 * σ) := by
    have h1 : Real.exp (M : ℝ) ≤ Real.exp (t : ℝ) := Real.exp_le_exp.2 hMtR
    have h2 : σ * Real.exp (t : ℝ) * Real.exp 1 ≤ 1 / 10 := by
      rw [mul_assoc, ← Real.exp_add]
      exact htop
    have h3 : σ * Real.exp (t : ℝ) < 1 / 2 := by
      nlinarith [Real.exp_one_gt_d9, Real.exp_pos (t : ℝ)]
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [Real.exp_pos (M : ℝ)]
  have hlt : blockScale (M : ℝ) 0 < Real.exp (1 / (2 * σ)) := by
    simp only [blockScale, Nat.cast_zero, zero_add]
    exact Real.exp_lt_exp.2 het
  unfold scaleCut harperTruncation
  have hfl : (⌊blockScale (M : ℝ) 0⌋₊ : ℝ) < ⌈Real.exp (1 / (2 * σ))⌉₊ :=
    lt_of_le_of_lt (Nat.floor_le (le_trans zero_le_two (two_le_blockScale_zero
      (Nat.cast_nonneg M)))) (lt_of_lt_of_le hlt (Nat.le_ceil _))
  exact_mod_cast hfl

/-- `log⌈e^{1/(2σ)}⌉ ≤ 1/σ` for `0 < σ ≤ 1/2`: `⌈e^u⌉ ≤ e^u + 1 ≤ e^{u+1}`. -/
lemma log_harperTruncation_le {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) :
    Real.log ((harperTruncation σ : ℕ) : ℝ) ≤ 1 / σ := by
  have hu : (0 : ℝ) ≤ 1 / (2 * σ) := by positivity
  have hceil : ((harperTruncation σ : ℕ) : ℝ) ≤ Real.exp (1 / (2 * σ) + 1) := by
    have h1 : ((harperTruncation σ : ℕ) : ℝ) < Real.exp (1 / (2 * σ)) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    have h2 : Real.exp (1 / (2 * σ)) + 1 ≤ Real.exp (1 / (2 * σ) + 1) := by
      rw [Real.exp_add]
      have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hE : (1 : ℝ) ≤ Real.exp (1 / (2 * σ)) := Real.one_le_exp hu
      nlinarith
    linarith
  have hpos : (0 : ℝ) < ((harperTruncation σ : ℕ) : ℝ) := by
    have := Nat.le_ceil (Real.exp (1 / (2 * σ)))
    unfold harperTruncation
    linarith [Real.exp_pos (1 / (2 * σ))]
  have hlog := Real.log_le_log hpos hceil
  rw [Real.log_exp] at hlog
  have hhalf : 1 / (2 * σ) + 1 ≤ 1 / σ := by
    rw [div_add_one (by positivity), div_le_div_iff₀ (by positivity) hσ]
    nlinarith
  linarith

/-- `log⌊e^{e^M}⌋ ≥ e^M/2` for `M ≥ 1`. -/
lemma half_exp_le_log_floor_blockScale {M : ℝ} (hM : 1 ≤ M) :
    Real.exp M / 2 ≤ Real.log ((⌊blockScale M 0⌋₊ : ℕ) : ℝ) := by
  have hx2 : (2 : ℝ) ≤ blockScale M 0 := two_le_blockScale_zero (by linarith)
  have hfl : blockScale M 0 / 2 ≤ ((⌊blockScale M 0⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (blockScale M 0)
    linarith
  have hpos : (0 : ℝ) < blockScale M 0 / 2 := by linarith
  have hlog := Real.log_le_log hpos hfl
  rw [Real.log_div (by linarith) (by norm_num), log_blockScale] at hlog
  simp only [Nat.cast_zero, zero_add] at hlog
  have hl2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have heM : (2 : ℝ) ≤ Real.exp M := by linarith [Real.add_one_le_exp M]
  linarith

/-- **The pair moment above a decorrelated scale is `≪ e^{2(t-M)}`.**  For `6 ≤ M ≤ t` and heights
in `[0, 1/2]` with `|h₁-h₂|e^M ≥ 2`, over `[scaleCut M, y)` past the truncation. -/
theorem exists_integral_normSq_pair_Ico_decorr_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (M t y : ℕ) (σ h₁ h₂ : ℝ), 6 ≤ M → M ≤ t → 0 < σ →
        σ * Real.exp ((t : ℝ) + 1) ≤ 1 / 10 → Real.exp (-6) ≤ σ * Real.exp (t : ℝ) →
        harperTruncation σ < y → 0 ≤ h₁ → h₁ ≤ 1 / 2 → 0 ≤ h₂ → h₂ ≤ 1 / 2 →
        2 ≤ |h₁ - h₂| * Real.exp (M : ℝ) →
        ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut M) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut M) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
          ≤ K * Real.exp (2 * ((t : ℝ) - M)) := by
  obtain ⟨K, hK, hhigh⟩ := exists_integral_normSq_high_le_rademacher_at (Ω := Ω)
  refine ⟨K * (4 * Real.exp 12), by positivity, ?_⟩
  intro X μ hX M t y σ h₁ h₂ hM6 hMt hσ htop hbot hy hh₁0 hh₁ hh₂0 hh₂ hdec
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hMR : (6 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM6
  -- `σ ≤ 1/2`, and the cuts
  have hσ2 : σ ≤ 1 / 2 := by
    have h1 : (1 : ℝ) ≤ Real.exp ((t : ℝ) + 1) := Real.one_le_exp (by positivity)
    nlinarith
  set N₁ : ℕ := ⌊blockScale (M : ℝ) 0⌋₊ with hN₁def
  have hcut : scaleCut (M : ℝ) = N₁ + 1 := rfl
  have hN₁400 : (400 : ℝ) ≤ (N₁ : ℝ) := four_hundred_le_floor_blockScale hMR 0
  have hN₁M : N₁ ≤ harperTruncation σ := by
    have := scaleCut_le_harperTruncation hMt hσ htop
    rw [hcut] at this
    omega
  have hy' : y = (y - 1) + 1 := by omega
  have hMN₂ : harperTruncation σ ≤ y - 1 := by omega
  have hlogN₁ : Real.exp (M : ℝ) / 2 ≤ Real.log (N₁ : ℝ) :=
    half_exp_le_log_floor_blockScale (by linarith)
  -- the two frequencies
  have hτ0 : 0 < |h₁ - h₂| := by
    by_contra hc
    have : |h₁ - h₂| = 0 := le_antisymm (not_lt.1 hc) (abs_nonneg _)
    rw [this, zero_mul] at hdec
    linarith
  have hτ1 : |h₁ - h₂| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hντ : |h₁ - h₂| ≤ |h₁ + h₂| := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h₁ + h₂), abs_le]
    constructor <;> linarith
  have hν0 : 0 < |h₁ + h₂| := lt_of_lt_of_le hτ0 hντ
  have hν1 : |h₁ + h₂| ≤ 1 := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h₁ + h₂)]
    linarith
  have hinvτ : 1 / |h₁ - h₂| ≤ Real.log (N₁ : ℝ) := by
    rw [div_le_iff₀ hτ0]
    nlinarith [hlogN₁]
  have hinvν : 1 / |h₁ + h₂| ≤ Real.log (N₁ : ℝ) :=
    le_trans (one_div_le_one_div_of_le hτ0 hντ) hinvτ
  have hre₁ : (shiftLine σ h₁).re = 1 / 2 + σ := re_shiftLine σ h₁
  have hre₂ : (shiftLine σ h₂).re = 1 / 2 + σ := re_shiftLine σ h₂
  have h := hhigh _ μ hf σ (shiftLine σ h₁) (shiftLine σ h₂) N₁ (harperTruncation σ) (y - 1)
    hσ.le hre₁ hre₂ (by simpa only [im_shiftLine] using hτ0)
    (by simpa only [im_shiftLine] using hτ1) (by simpa only [im_shiftLine] using hν0)
    (by simpa only [im_shiftLine] using hν1) hN₁400 hN₁M hMN₂
    (by simpa only [im_shiftLine] using hinvτ) (by simpa only [im_shiftLine] using hinvν)
    (one_le_two_mul_sigma_mul_log_harperTruncation hσ)
  rw [← hcut, ← hy'] at h
  refine le_trans h ?_
  -- `(log M_tr / log N₁)² ≤ 4 e^{12} e^{2(t-M)}`
  have hlogtr := log_harperTruncation_le hσ hσ2
  have hinvσ : 1 / σ ≤ Real.exp (6 + (t : ℝ)) := by
    rw [div_le_iff₀ hσ, Real.exp_add]
    have := hbot
    rw [show Real.exp (-6) = (Real.exp 6)⁻¹ from Real.exp_neg 6] at this
    have he6 : (0 : ℝ) < Real.exp 6 := Real.exp_pos 6
    rw [inv_eq_one_div, div_le_iff₀ he6] at this
    linarith
  have hN₁pos : (0 : ℝ) < Real.log (N₁ : ℝ) := lt_of_lt_of_le (by positivity) hlogN₁
  have htr0 : (0 : ℝ) ≤ Real.log ((harperTruncation σ : ℕ) : ℝ) := by
    have := one_le_two_mul_sigma_mul_log_harperTruncation hσ
    nlinarith
  have hratio : Real.log ((harperTruncation σ : ℕ) : ℝ) / Real.log (N₁ : ℝ)
      ≤ 2 * Real.exp 6 * Real.exp ((t : ℝ) - M) := by
    rw [div_le_iff₀ hN₁pos]
    have hsplit : Real.exp (6 + (t : ℝ)) = Real.exp 6 * Real.exp ((t : ℝ) - M) * Real.exp M := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
    have h2 : 2 * Real.exp 6 * Real.exp ((t : ℝ) - M) * (Real.exp M / 2)
        ≤ 2 * Real.exp 6 * Real.exp ((t : ℝ) - M) * Real.log (N₁ : ℝ) :=
      mul_le_mul_of_nonneg_left hlogN₁ (by positivity)
    nlinarith [hsplit]
  have hsq : (Real.log ((harperTruncation σ : ℕ) : ℝ) / Real.log (N₁ : ℝ)) ^ 2
      ≤ (2 * Real.exp 6 * Real.exp ((t : ℝ) - M)) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg htr0 hN₁pos.le) hratio 2
  have hid : (2 * Real.exp 6 * Real.exp ((t : ℝ) - M)) ^ 2
      = 4 * Real.exp 12 * Real.exp (2 * ((t : ℝ) - M)) := by
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [hid] at hsq
  calc K * (Real.log ((harperTruncation σ : ℕ) : ℝ) / Real.log (N₁ : ℝ)) ^ 2
      ≤ K * (4 * Real.exp 12 * Real.exp (2 * ((t : ℝ) - M))) :=
        mul_le_mul_of_nonneg_left hsq hK.le
    _ = K * (4 * Real.exp 12) * Real.exp (2 * ((t : ℝ) - M)) := by ring

/-- **The pair moment above a scale where only the sum frequency oscillates is `≪ e^{4(t-M)}`**:
for `6 ≤ M ≤ t` and `(h₁+h₂)e^M ≥ 2`; at `M = t` it is a constant. -/
theorem exists_integral_normSq_pair_Ico_sum_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (M t y : ℕ) (σ h₁ h₂ : ℝ), 6 ≤ M → M ≤ t → 0 < σ →
        σ * Real.exp ((t : ℝ) + 1) ≤ 1 / 10 → Real.exp (-6) ≤ σ * Real.exp (t : ℝ) →
        harperTruncation σ < y → 0 ≤ h₁ → 0 ≤ h₂ → h₁ + h₂ ≤ 1 →
        2 ≤ (h₁ + h₂) * Real.exp (M : ℝ) →
        ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut M) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut M) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
          ≤ K * Real.exp (4 * ((t : ℝ) - M)) := by
  obtain ⟨K, hK, hsplit⟩ := exists_integral_normSq_pairIco_split_le_rademacher_at (Ω := Ω)
  refine ⟨K * (16 * Real.exp 24), by positivity, ?_⟩
  intro X μ hX M t y σ h₁ h₂ hM6 hMt hσ htop hbot hy hh₁0 hh₂0 hsum hfreq
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hMR : (6 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM6
  have hσ2 : σ ≤ 1 / 2 := by
    have h1 : (1 : ℝ) ≤ Real.exp ((t : ℝ) + 1) := Real.one_le_exp (by positivity)
    nlinarith
  set N₁ : ℕ := ⌊blockScale (M : ℝ) 0⌋₊ with hN₁def
  have hcut : scaleCut (M : ℝ) = N₁ + 1 := rfl
  have hN₁400 : (400 : ℝ) ≤ (N₁ : ℝ) := four_hundred_le_floor_blockScale hMR 0
  have hN₁M : N₁ ≤ harperTruncation σ := by
    have := scaleCut_le_harperTruncation hMt hσ htop
    rw [hcut] at this
    omega
  have hy' : y = (y - 1) + 1 := by omega
  have hMN₂ : harperTruncation σ ≤ y - 1 := by omega
  have hlogN₁ : Real.exp (M : ℝ) / 2 ≤ Real.log (N₁ : ℝ) :=
    half_exp_le_log_floor_blockScale (by linarith)
  have hν0 : 0 < |h₁ + h₂| := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h₁ + h₂)]
    by_contra hc
    have : h₁ + h₂ = 0 := le_antisymm (not_lt.1 hc) (by linarith)
    rw [this, zero_mul] at hfreq
    linarith
  have hν1 : |h₁ + h₂| ≤ 1 := by rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h₁ + h₂)]
  have hinvν : 1 / |h₁ + h₂| ≤ Real.log (N₁ : ℝ) := by
    rw [div_le_iff₀ hν0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ h₁ + h₂)]
    nlinarith [hlogN₁]
  have h := hsplit _ μ hf σ (shiftLine σ h₁) (shiftLine σ h₂) N₁ (harperTruncation σ) (y - 1)
    hσ.le (re_shiftLine σ h₁) (re_shiftLine σ h₂) (by simpa only [im_shiftLine] using hν0)
    (by simpa only [im_shiftLine] using hν1) hN₁400 hN₁M hMN₂
    (by simpa only [im_shiftLine] using hinvν) (one_le_two_mul_sigma_mul_log_harperTruncation hσ)
  rw [← hcut, ← hy'] at h
  refine le_trans h ?_
  have hlogtr := log_harperTruncation_le hσ hσ2
  have hinvσ : 1 / σ ≤ Real.exp (6 + (t : ℝ)) := by
    rw [div_le_iff₀ hσ, Real.exp_add]
    have := hbot
    rw [show Real.exp (-6) = (Real.exp 6)⁻¹ from Real.exp_neg 6] at this
    have he6 : (0 : ℝ) < Real.exp 6 := Real.exp_pos 6
    rw [inv_eq_one_div, div_le_iff₀ he6] at this
    linarith
  have hN₁pos : (0 : ℝ) < Real.log (N₁ : ℝ) := lt_of_lt_of_le (by positivity) hlogN₁
  have htr0 : (0 : ℝ) ≤ Real.log ((harperTruncation σ : ℕ) : ℝ) := by
    have := one_le_two_mul_sigma_mul_log_harperTruncation hσ
    nlinarith
  have hratio : Real.log ((harperTruncation σ : ℕ) : ℝ) / Real.log (N₁ : ℝ)
      ≤ 2 * Real.exp 6 * Real.exp ((t : ℝ) - M) := by
    rw [div_le_iff₀ hN₁pos]
    have hsplit' : Real.exp (6 + (t : ℝ)) = Real.exp 6 * Real.exp ((t : ℝ) - M) * Real.exp M := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
    have h2 : 2 * Real.exp 6 * Real.exp ((t : ℝ) - M) * (Real.exp M / 2)
        ≤ 2 * Real.exp 6 * Real.exp ((t : ℝ) - M) * Real.log (N₁ : ℝ) :=
      mul_le_mul_of_nonneg_left hlogN₁ (by positivity)
    nlinarith [hsplit']
  have hpow : (Real.log ((harperTruncation σ : ℕ) : ℝ) / Real.log (N₁ : ℝ)) ^ 4
      ≤ (2 * Real.exp 6 * Real.exp ((t : ℝ) - M)) ^ 4 :=
    pow_le_pow_left₀ (div_nonneg htr0 hN₁pos.le) hratio 4
  have hid : (2 * Real.exp 6 * Real.exp ((t : ℝ) - M)) ^ 4
      = 16 * Real.exp 24 * Real.exp (4 * ((t : ℝ) - M)) := by
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [hid] at hpow
  calc K * (Real.log ((harperTruncation σ : ℕ) : ℝ) / Real.log (N₁ : ℝ)) ^ 4
      ≤ K * (16 * Real.exp 24 * Real.exp (4 * ((t : ℝ) - M))) :=
        mul_le_mul_of_nonneg_left hpow hK.le
    _ = K * (16 * Real.exp 24) * Real.exp (4 * ((t : ℝ) - M)) := by ring

/-! ### The pair integrand near the diagonal

For `h₁, h₂` closer than the barrier resolves, drop `L(k,h₁)` and use only `L(k,h₂)` at one depth
`M - k`: there `‖F_{[c_k, c_M)}(h₂)‖ ≤ e^{β}`, `β = RMF.halfBarrierTop j₀ C₁ a (M-k)`, and what is
left factorises across `c_M = scaleCut M` by independence
(`RMF.integral_normSq_split_factor_sqfree`). -/

omit [MeasurableSpace Ω] in
/-- **On `L(k,h)`, the block product up to depth `d ≤ t - k` is at most `e^{β}`**, wherever the
values at its primes are bounded by one. -/
lemma normSq_Ico_le_of_mem_halfBarrier {X : ℕ → Ω → ℂ} {σ h : ℝ} (hσ : 0 ≤ σ) {k j₀ t : ℕ}
    {C₁ a B : ℝ} (hC₁ : 0 ≤ C₁) {ω : Ω} (hω : ω ∈ halfBarrier X σ h k j₀ t C₁ a B) {d : ℕ}
    (hd : d ≤ t - k)
    (hval : ∀ p ∈ primesIco (scaleCut (k : ℝ)) (scaleCut ((k : ℝ) + d)), ‖X p ω‖ ≤ 1) :
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k : ℝ)) (scaleCut ((k : ℝ) + d)) (shiftLine σ h) ω‖ ^ 2
      ≤ Real.exp (2 * halfBarrierTop j₀ C₁ a d) := by
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  have hpos := norm_randomEulerProductIco_sqfree_pos hs hval
  have hlog := log_norm_randomEulerProductIco_eq_walk_halfBlock (X := X) k σ h d hσ hval
  have hwalk := walk_le_halfBarrierTop hC₁ hω hd
  have hle : ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (scaleCut (k : ℝ)) (scaleCut ((k : ℝ) + d)) (shiftLine σ h) ω‖
      ≤ Real.exp (halfBarrierTop j₀ C₁ a d) := by
    rw [← Real.exp_log hpos, hlog]
    exact Real.exp_le_exp.2 hwalk
  calc _ ≤ Real.exp (halfBarrierTop j₀ C₁ a d) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = Real.exp (2 * halfBarrierTop j₀ C₁ a d) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf

/-- `‖F_{[a,b)}(s₀)‖²·(‖F_{[c,d)}(s₁)‖²‖F_{[c,d)}(s₂)‖²)` is integrable: the first factor is bounded
on the line `Re s₀ = ½ + σ`, the second is integrable. -/
lemma integrable_normSq_Ico_mul_pair {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (a b c d : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (h₀ h₁ h₂ : ℝ) :
    Integrable (fun ω =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ h₀) ω‖ ^ 2
        * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) c d
            (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) c d
            (shiftLine σ h₂) ω‖ ^ 2)) μ := by
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hpair := hf.integrable_normSq_pair_Ico c d (shiftLine σ h₁) (shiftLine σ h₂)
  have hm : AEStronglyMeasurable (fun ω =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ h₀) ω‖ ^ 2) μ :=
    (hf.integrable_norm_randomEulerProductIco_sq a b (shiftLine σ h₀)).aestronglyMeasurable
  have hb : ∀ᵐ ω ∂μ, ‖‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
      (shiftLine σ h₀) ω‖ ^ 2‖ ≤ (∏ p ∈ primesIco a b, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 := by
    filter_upwards [ae_forall_norm_randomEulerProductIco_mem_Icc hX a b (c := 1 / 2 + σ)
      (by linarith)] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hω (shiftLine σ h₀) (re_shiftLine σ h₀)).2 2
  exact hpair.bdd_mul hm hb

/-- **The near bound.**  For a split scale `M` with `k < M ≤ t`,

`E[1_{L h₁}‖F(h₁)‖²·1_{L h₂}‖F(h₂)‖²]`
`  ≤ e^{2β}·E‖F_{[c_k,c_M)}(h₁)‖²·E[‖F_{[c_M,y)}(h₁)‖²‖F_{[c_M,y)}(h₂)‖²]`,

`F = F_{[c_k, y)}`, `β` the barrier's upper edge at depth `M - k`. -/
lemma integral_indicator_pair_le_near {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {σ : ℝ} (hσ : 0 ≤ σ) {k j₀ t y M : ℕ} {C₁ a B : ℝ}
    (hC₁ : 0 ≤ C₁) (hkM : k ≤ M) (hMt : M ≤ t) (hMy : scaleCut (M : ℝ) ≤ y) (h₁ h₂ : ℝ) :
    ∫ ω, Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut k) y (shiftLine σ h₁) ω‖ ^ 2) ω
        * Set.indicator (halfBarrier X σ h₂ k j₀ t C₁ a B)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut k) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ
      ≤ Real.exp (2 * halfBarrierTop j₀ C₁ a (M - k))
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut k) (scaleCut M) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
          * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut M) y (shiftLine σ h₁) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut M) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ) := by
  have hkM' : scaleCut (k : ℝ) ≤ scaleCut (M : ℝ) := scaleCut_mono (by exact_mod_cast hkM)
  have hMk : ((k : ℝ) + ((M - k : ℕ) : ℝ)) = (M : ℝ) := by rw [Nat.cast_sub hkM]; ring
  rw [← integral_normSq_split_factor_sqfree hX hkM' hMy, ← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_)
    ((integrable_normSq_Ico_mul_pair hX _ _ _ _ hσ h₁ h₁ h₂).const_mul _) ?_
  · exact mul_nonneg (Set.indicator_nonneg (fun _ _ => by positivity) _)
      (Set.indicator_nonneg (fun _ _ => by positivity) _)
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw
    (scaleCut (k : ℝ)) (scaleCut (M : ℝ))] with ω hω
  have hsplit₁ := normSq_randomEulerProductIco_split (X := X) hkM' hMy (shiftLine σ h₁) ω
  have hsplit₂ := normSq_randomEulerProductIco_split (X := X) hkM' hMy (shiftLine σ h₂) ω
  have hβ : 0 ≤ Real.exp (2 * halfBarrierTop j₀ C₁ a (M - k)) := (Real.exp_pos _).le
  have hind₁ : Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut k) y (shiftLine σ h₁) ω‖ ^ 2) ω
      ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut k) y (shiftLine σ h₁) ω‖ ^ 2 :=
    Set.indicator_le_self' (fun _ _ => by positivity) ω
  have hind₂ : Set.indicator (halfBarrier X σ h₂ k j₀ t C₁ a B)
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut k) y (shiftLine σ h₂) ω‖ ^ 2) ω
      ≤ Real.exp (2 * halfBarrierTop j₀ C₁ a (M - k))
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut M) y (shiftLine σ h₂) ω‖ ^ 2 := by
    by_cases hmem : ω ∈ halfBarrier X σ h₂ k j₀ t C₁ a B
    · rw [Set.indicator_of_mem hmem, hsplit₂]
      have hval : ∀ p ∈ primesIco (scaleCut (k : ℝ)) (scaleCut ((k : ℝ) + ((M - k : ℕ) : ℝ))),
          ‖X p ω‖ ≤ 1 := by rw [hMk]; exact hω
      have hb := normSq_Ico_le_of_mem_halfBarrier hσ hC₁ hmem (by omega) hval
      rw [hMk] at hb
      exact mul_le_mul_of_nonneg_right hb (by positivity)
    · rw [Set.indicator_of_notMem hmem]
      positivity
  have h0₁ : 0 ≤ Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut k) y (shiftLine σ h₁) ω‖ ^ 2) ω :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  calc _ ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut k) y (shiftLine σ h₁) ω‖ ^ 2
        * (Real.exp (2 * halfBarrierTop j₀ C₁ a (M - k))
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut M) y (shiftLine σ h₂) ω‖ ^ 2) :=
        mul_le_mul hind₁ hind₂ (Set.indicator_nonneg (fun _ _ => by positivity) _)
          (by positivity)
    _ = _ := by rw [hsplit₁]; ring

/-! ### Independence with a barrier inside, and the tilt of a block product

Far from the diagonal the barrier cannot be dropped: `L(k,h₁) ∩ L(k,h₂)` sits inside a pair barrier
`P` on the blocks from some `n₁` on, and Proposition 7 bounds the pair-tilted measure of `P`.  Three
factorisations get there, each `RMF.IsIIDPrimeValues.integral_mul_split` on the values in two
adjacent prime ranges (`RMF.integral_mul_split_Ico`), with `P` presented as an event on the values
of one range (`RMF.exists_tuple_barrierEventPair`, from `RMF.tupleGood`). -/

/-- **Independence across a cut, for functions of two adjacent prime ranges** `[w, z)` and `[z, n)`:
`RMF.IsIIDPrimeValues.integral_mul_split` with the low factor read through the restriction from the
primes below `z`. -/
theorem integral_mul_split_Ico {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) {w z n : ℕ}
    {φ : (↥(primesIco w z) → ℂ) → ℝ} {ψ : (↥(primesIco z n) → ℂ) → ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ) :
    (∫ ω, (φ fun p => X (p : ℕ) ω) * (ψ fun p => X (p : ℕ) ω) ∂μ)
      = (∫ ω, φ fun p => X (p : ℕ) ω ∂μ) * ∫ ω, ψ fun p => X (p : ℕ) ω ∂μ := by
  have hsub : ∀ p ∈ primesIco w z, p ∈ Nat.primesBelow z := fun p hp => by
    obtain ⟨hpp, _, hpz⟩ := mem_primesIco.1 hp
    exact Nat.mem_primesBelow.2 ⟨hpz, hpp⟩
  let res : (↥(Nat.primesBelow z) → ℂ) → (↥(primesIco w z) → ℂ) :=
    fun v p => v ⟨p.1, hsub p.1 p.2⟩
  have hresm : Measurable res := measurable_pi_lambda _ fun p => measurable_pi_apply _
  have hlow := measurable_primeTuple hX (Nat.primesBelow z)
    fun p hp => Nat.prime_of_mem_primesBelow hp
  have hhigh := measurable_primeTuple hX (primesIco z n) fun p hp => prime_of_mem_primesIco hp
  exact hX.integral_mul_split z n (hφ.comp hresm) hψ
    ((hφ.comp hresm).comp hlow).aestronglyMeasurable (hψ.comp hhigh).aestronglyMeasurable

/-- `‖F_{[a,b)}(s₁)‖²‖F_{[a,b)}(s₂)‖²` as a function of the values in `[a, b)`. -/
noncomputable def pairPoly (S : Finset ℕ) (s₁ s₂ : ℂ) (v : ↥S → ℂ) : ℝ :=
  ‖primePoly S s₁ v‖ ^ 2 * ‖primePoly S s₂ v‖ ^ 2

lemma measurable_pairPoly (S : Finset ℕ) (s₁ s₂ : ℂ) : Measurable (pairPoly S s₁ s₂) :=
  (((continuous_primePoly S s₁).norm.pow 2).mul ((continuous_primePoly S s₂).norm.pow 2)).measurable

omit [MeasurableSpace Ω] in
lemma pairPoly_primesIco {X : ℕ → Ω → ℂ} (a b : ℕ) (s₁ s₂ : ℂ) (ω : Ω) :
    pairPoly (primesIco a b) s₁ s₂ (fun p => X (p : ℕ) ω)
      = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s₂ ω‖ ^ 2 := by
  rw [pairPoly, primePoly_primesIco, primePoly_primesIco]

/-- **The tilt identity for a block product.**  For an event `G` that is a function of the values
in `[z, n)`, with `P̃_n` the pair tilt by the full product below `n`,
`∫_G ‖F_{[z,n)}(s₁)‖²‖F_{[z,n)}(s₂)‖² = P̃_n(G)·E[‖F_{[z,n)}(s₁)‖²‖F_{[z,n)}(s₂)‖²]`: the primes
below `z` factor out of both sides of `RMF.IsRademacherRMF.setIntegral_normSq_mul_normSq_eq` and
cancel. -/
theorem setIntegral_normSq_pair_Ico_eq_tilt {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {z n : ℕ} (hzn : z ≤ n) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {G : Set Ω} {T : Set (↥(primesIco z n) → ℂ)}
    (hT : MeasurableSet T)
    (hGT : ∀ ω, ω ∈ G ↔ (fun p : ↥(primesIco z n) => X (p : ℕ) ω) ∈ T) :
    (∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n s₂ ω‖ ^ 2 ∂μ)
      = (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) n s₁ s₂ μ G).toReal
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n s₂ ω‖ ^ 2
            ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hhigh := measurable_primeTuple hX (primesIco z n) fun p hp => prime_of_mem_primesIco hp
  have hG : MeasurableSet G := by
    have hGeq : G = (fun ω => (fun p : ↥(primesIco z n) => X (p : ℕ) ω)) ⁻¹' T := by
      ext ω; exact hGT ω
    rw [hGeq]; exact hhigh hT
  have hψ : Measurable (Set.indicator T (pairPoly (primesIco z n) s₁ s₂)) :=
    (measurable_pairPoly _ s₁ s₂).indicator hT
  have hsplit := integral_mul_split_Ico hX (w := 0) (measurable_pairPoly (primesIco 0 z) s₁ s₂) hψ
  have hψeq : ∀ ω, Set.indicator T (pairPoly (primesIco z n) s₁ s₂) (fun p => X (p : ℕ) ω)
      = Set.indicator G (fun ω =>
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n s₂ ω‖ ^ 2)
          ω := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_mem ((hGT ω).1 hω), Set.indicator_of_mem hω, pairPoly_primesIco]
    · rw [Set.indicator_of_notMem (fun hc => hω ((hGT ω).2 hc)), Set.indicator_of_notMem hω]
  -- the full product below `n` splits at `z`
  have hFn : ∀ (s : ℂ) (ω : Ω),
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n s ω‖ ^ 2
        = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 z s ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n s ω‖ ^ 2 := by
    intro s ω
    rw [← randomEulerProductIco_zero, normSq_randomEulerProductIco_split (Nat.zero_le z) hzn]
  have hfull := hf.setIntegral_normSq_mul_normSq_eq n hs₁ hs₂ hG
  have hlhs : (∫ ω in G,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n s₂ ω‖ ^ 2 ∂μ)
      = (∫ ω, pairPoly (primesIco 0 z) s₁ s₂ (fun p => X (p : ℕ) ω) ∂μ)
        * ∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n
              s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n s₂ ω‖ ^ 2
            ∂μ := by
    have hhighint : (∫ ω, Set.indicator T (pairPoly (primesIco z n) s₁ s₂)
          (fun p => X (p : ℕ) ω) ∂μ)
        = ∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n
              s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n s₂ ω‖ ^ 2
            ∂μ := by
      rw [← integral_indicator hG]
      exact integral_congr_ae (Filter.Eventually.of_forall hψeq)
    rw [← hhighint, ← hsplit, ← integral_indicator hG]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [hψeq ω, pairPoly_primesIco]
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hFn s₁ ω, hFn s₂ ω]
      ring
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, mul_zero]
  have hmom := hf.integral_normSq_mul_normSq_Ico_split (Nat.zero_le z) hzn s₁ s₂
  simp only [randomEulerProductIco_zero] at hmom
  have hlow : (∫ ω, pairPoly (primesIco 0 z) s₁ s₂ (fun p => X (p : ℕ) ω) ∂μ)
      = ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z s₂ ω‖ ^ 2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      dsimp only
      rw [pairPoly_primesIco, randomEulerProductIco_zero, randomEulerProductIco_zero])
  have hA := hf.integral_normSq_mul_normSq_Ico_pos 0 z hs₁ hs₂
  simp only [randomEulerProductIco_zero] at hA
  rw [hlhs, hmom, hlow] at hfull
  have hfull' : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z
          s₁ ω‖ ^ 2
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z s₂ ω‖ ^ 2 ∂μ)
      * ((∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n
              s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n s₂ ω‖ ^ 2
            ∂μ)
        - (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) n s₁ s₂ μ G).toReal
          * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n
                s₁ ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z n s₂ ω‖ ^ 2
              ∂μ) = 0 := by
    rw [mul_sub, hfull]
    ring
  rcases mul_eq_zero.1 hfull' with h0 | h0
  · exact absurd h0 hA.ne'
  · linarith

omit [MeasurableSpace Ω] in
/-- **A pair barrier on the blocks from `r` on is an event on the values in any `S` that holds those
blocks**: `RMF.tupleGood` at each height. -/
lemma exists_tuple_barrierEventPair {X : ℕ → Ω → ℂ} {S : Finset ℕ}
    (hSp : ∀ p ∈ S, Nat.Prime p) (θ : ℝ) (r n : ℕ) (s₁ s₂ : ℂ) (a c : ℝ) (hf : ℕ → ℝ)
    (hS : ∀ m, m < n → ∀ p ∈ primeBlockSub (θ + r) m, ((p : Nat.Primes) : ℕ) ∈ S) :
    ∃ T : Set (↥S → ℂ), MeasurableSet T ∧ ∀ ω,
      ω ∈ barrierEventPair (fun m => blockPairAdd θ s₁ s₂ X (m + r)) n
          (fun j => -a - c * j) (fun j => a + j + hf j)
          (fun j => -a - c * j) (fun j => a + j + hf j)
        ↔ (fun p : ↥S => X (p : ℕ) ω) ∈ T := by
  refine ⟨tupleGood S (θ + r) c n 1 a hf s₁ ∩ tupleGood S (θ + r) c n 1 a hf s₂,
    (measurableSet_tupleGood _ _ _ _ _ _ _ _).inter (measurableSet_tupleGood _ _ _ _ _ _ _ _),
    fun ω => ?_⟩
  rw [Set.mem_inter_iff, mem_tupleGood_iff hSp hS ω, mem_tupleGood_iff hSp hS ω]
  simp only [barrierEventPair, barrierEvent, mesoGood, Set.mem_inter_iff, Set.mem_setOf_eq,
    blockPairAdd, primeBlockSub_add]

omit [MeasurableSpace Ω] in
/-- **An event on the values in a sub-range is an event on the values in the range.** -/
lemma exists_tuple_event_of_subset {X : ℕ → Ω → ℂ} {S S' : Finset ℕ} (hSS' : S ⊆ S')
    {G : Set Ω} {T : Set (↥S → ℂ)} (hT : MeasurableSet T)
    (hGT : ∀ ω, ω ∈ G ↔ (fun p : ↥S => X (p : ℕ) ω) ∈ T) :
    ∃ T' : Set (↥S' → ℂ), MeasurableSet T' ∧
      ∀ ω, ω ∈ G ↔ (fun p : ↥S' => X (p : ℕ) ω) ∈ T' := by
  let res : (↥S' → ℂ) → (↥S → ℂ) := fun v p => v ⟨p.1, hSS' p.2⟩
  have hres : Measurable res := measurable_pi_lambda _ fun p => measurable_pi_apply _
  exact ⟨res ⁻¹' T, hres hT, fun ω => hGT ω⟩

/-- **The far factorisation.**  If `L(k,h₁) ∩ L(k,h₂) ⊆ G` for an event `G` on the values in
`[c_M, c_top)` (`c_M = scaleCut M`, `c_top = scaleCut (t+1)`), then the pair integrand is at most
`e^{2β}·E‖F_{[c_k,c_M)}(h₁)‖²·P̃_{c_top}(G)·E[‖F_{[c_M,y)}(h₁)‖²‖F_{[c_M,y)}(h₂)‖²]`, `β` the
barrier's upper edge at depth `M - k` and `P̃_{c_top}` the pair tilt below `c_top`.  The near bound
is the case `G = Ω`; far from the diagonal `G` is the pair barrier of Proposition 7. -/
lemma integral_indicator_pair_le_far {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {σ : ℝ} (hσ : 0 ≤ σ) {k j₀ t y M : ℕ} {C₁ a B : ℝ}
    (hC₁ : 0 ≤ C₁) (hkM : k ≤ M) (hMt : M ≤ t) (hty : scaleCut ((t : ℝ) + 1) ≤ y)
    (h₁ h₂ : ℝ) {G : Set Ω}
    (hGsub : halfBarrier X σ h₁ k j₀ t C₁ a B ∩ halfBarrier X σ h₂ k j₀ t C₁ a B ⊆ G)
    {T : Set (↥(primesIco (scaleCut (M : ℝ)) (scaleCut ((t : ℝ) + 1))) → ℂ)}
    (hT : MeasurableSet T)
    (hGT : ∀ ω, ω ∈ G ↔
      (fun p : ↥(primesIco (scaleCut (M : ℝ)) (scaleCut ((t : ℝ) + 1))) => X (p : ℕ) ω) ∈ T) :
    ∫ ω, Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut k) y (shiftLine σ h₁) ω‖ ^ 2) ω
        * Set.indicator (halfBarrier X σ h₂ k j₀ t C₁ a B)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut k) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ
      ≤ Real.exp (2 * halfBarrierTop j₀ C₁ a (M - k))
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut k) (scaleCut M) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
          * ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut ((t : ℝ) + 1)) (shiftLine σ h₁) (shiftLine σ h₂) μ G).toReal
            * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut M) y (shiftLine σ h₁) ω‖ ^ 2
                * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut M) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ)) := by
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hkM' : scaleCut (k : ℝ) ≤ (scaleCut (M : ℝ)) := scaleCut_mono (by exact_mod_cast hkM)
  have hMtR : (M : ℝ) ≤ (t : ℝ) := by exact_mod_cast hMt
  have hMct : scaleCut (M : ℝ) ≤ scaleCut ((t : ℝ) + 1) := scaleCut_mono (by linarith)
  have hMy : (scaleCut (M : ℝ)) ≤ y := le_trans hMct hty
  have hMk : ((k : ℝ) + ((M - k : ℕ) : ℝ)) = (M : ℝ) := by rw [Nat.cast_sub hkM]; ring
  have hs₁ : 0 < (shiftLine σ h₁).re := by rw [re_shiftLine]; linarith
  have hs₂ : 0 < (shiftLine σ h₂).re := by rw [re_shiftLine]; linarith
  -- `G` as an event on `[c_M, y)`, and measurable
  have hsubS : primesIco (scaleCut (M : ℝ)) (scaleCut ((t : ℝ) + 1))
      ⊆ primesIco (scaleCut (M : ℝ)) y := fun p hp => by
    obtain ⟨h1, h2, h3⟩ := mem_primesIco.1 hp
    exact mem_primesIco.2 ⟨h1, h2, lt_of_lt_of_le h3 hty⟩
  obtain ⟨T', hT', hGT'⟩ := exists_tuple_event_of_subset (X := X) hsubS hT hGT
  have hG : MeasurableSet G := by
    have hGeq : G
        = (fun ω => (fun p : ↥(primesIco (scaleCut (M : ℝ)) y) => X (p : ℕ) ω)) ⁻¹' T' := by
      ext ω; exact hGT' ω
    rw [hGeq]
    exact (measurable_primeTuple hX _ fun p hp => prime_of_mem_primesIco hp) hT'
  -- the pair moment above `c_M`, restricted to `G`, as a function of the values in `[c_M, y)`
  have hψeq : ∀ ω, Set.indicator T'
        (pairPoly (primesIco (scaleCut (M : ℝ)) y) (shiftLine σ h₁) (shiftLine σ h₂))
        (fun p => X (p : ℕ) ω)
      = Set.indicator G (fun ω =>
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (M : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (M : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ω := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_mem ((hGT' ω).1 hω), Set.indicator_of_mem hω, pairPoly_primesIco]
    · rw [Set.indicator_of_notMem (fun hc => hω ((hGT' ω).2 hc)), Set.indicator_of_notMem hω]
  -- step 1: the pointwise bound, off the null set where a value exceeds one
  have hstep1 : (∫ ω, Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut k) y (shiftLine σ h₁) ω‖ ^ 2) ω
        * Set.indicator (halfBarrier X σ h₂ k j₀ t C₁ a B)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut k) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ)
      ≤ ∫ ω, Real.exp (2 * halfBarrierTop j₀ C₁ a (M - k))
          * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut k) (scaleCut (M : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
            * Set.indicator G (fun ω =>
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                    (scaleCut (M : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
                  * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                    (scaleCut (M : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ω) ∂μ := by
    have hm : AEStronglyMeasurable (fun ω =>
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut k) (scaleCut (M : ℝ)) (shiftLine σ h₁) ω‖ ^ 2) μ :=
      (hf.integrable_norm_randomEulerProductIco_sq _ _ _).aestronglyMeasurable
    have hb : ∀ᵐ ω ∂μ, ‖‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut k) (scaleCut (M : ℝ)) (shiftLine σ h₁) ω‖ ^ 2‖
        ≤ (∏ p ∈ primesIco (scaleCut (k : ℝ)) (scaleCut (M : ℝ)),
            (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 := by
      filter_upwards [ae_forall_norm_randomEulerProductIco_mem_Icc hX (scaleCut (k : ℝ))
        (scaleCut (M : ℝ)) (c := 1 / 2 + σ) (by linarith)] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hω (shiftLine σ h₁) (re_shiftLine σ h₁)).2 2
    have hint : Integrable (fun ω => Real.exp (2 * halfBarrierTop j₀ C₁ a (M - k))
          * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut k) (scaleCut (M : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
            * Set.indicator G (fun ω =>
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                    (scaleCut (M : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
                  * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                    (scaleCut (M : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ω)) μ :=
      (((hf.integrable_normSq_pair_Ico (scaleCut (M : ℝ)) y _ _).indicator hG).bdd_mul hm
        hb).const_mul _
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_) hint ?_
    · exact mul_nonneg (Set.indicator_nonneg (fun _ _ => by positivity) _)
        (Set.indicator_nonneg (fun _ _ => by positivity) _)
    filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw
      (scaleCut (k : ℝ)) (scaleCut (M : ℝ))] with ω hω
    by_cases hmem : ω ∈ halfBarrier X σ h₁ k j₀ t C₁ a B ∩ halfBarrier X σ h₂ k j₀ t C₁ a B
    · obtain ⟨hm₁, hm₂⟩ := hmem
      rw [Set.indicator_of_mem hm₁, Set.indicator_of_mem hm₂,
        Set.indicator_of_mem (hGsub ⟨hm₁, hm₂⟩),
        normSq_randomEulerProductIco_split (X := X) hkM' hMy (shiftLine σ h₁) ω,
        normSq_randomEulerProductIco_split (X := X) hkM' hMy (shiftLine σ h₂) ω]
      have hval : ∀ p ∈ primesIco (scaleCut (k : ℝ)) (scaleCut ((k : ℝ) + ((M - k : ℕ) : ℝ))),
          ‖X p ω‖ ≤ 1 := by rw [hMk]; exact hω
      have hbar := normSq_Ico_le_of_mem_halfBarrier hσ hC₁ hm₂ (by omega) hval
      rw [hMk] at hbar
      have hβ0 : 0 ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (M : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2 := by positivity
      have hA0 : 0 ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut k) (scaleCut (M : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (M : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2 := by positivity
      calc _ ≤ (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut k) (scaleCut (M : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (M : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2)
          * (Real.exp (2 * halfBarrierTop j₀ C₁ a (M - k))
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (M : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbar hβ0) hA0
        _ = _ := by ring
    · have hzero : Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut k) y (shiftLine σ h₁) ω‖ ^ 2) ω
          * Set.indicator (halfBarrier X σ h₂ k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut k) y (shiftLine σ h₂) ω‖ ^ 2) ω = 0 := by
        rcases not_and_or.1 hmem with h | h
        · rw [Set.indicator_of_notMem h, zero_mul]
        · rw [Set.indicator_of_notMem h, mul_zero]
      rw [hzero]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (by positivity)
        (Set.indicator_nonneg (fun _ _ => by positivity) _))
  -- step 2: split at `c_M`
  have hφ₁ : Measurable fun v : ↥(primesIco (scaleCut (k : ℝ)) (scaleCut (M : ℝ))) → ℂ =>
      ‖primePoly (primesIco (scaleCut (k : ℝ)) (scaleCut (M : ℝ))) (shiftLine σ h₁) v‖ ^ 2 :=
    ((continuous_primePoly _ _).norm.pow 2).measurable
  have hψ₁ : Measurable (Set.indicator T'
      (pairPoly (primesIco (scaleCut (M : ℝ)) y) (shiftLine σ h₁) (shiftLine σ h₂))) :=
    (measurable_pairPoly _ _ _).indicator hT'
  have hsplit₁ := integral_mul_split_Ico hX hφ₁ hψ₁
  have hstep2 : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut k) (scaleCut (M : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
        * Set.indicator G (fun ω =>
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (M : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (M : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ)
      = (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut k) (scaleCut (M : ℝ)) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * ∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (M : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (M : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ := by
    have e1 : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut k) (scaleCut (M : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
          * Set.indicator G (fun ω =>
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (M : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
                * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (M : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ)
        = ∫ ω, (‖primePoly (primesIco (scaleCut (k : ℝ)) (scaleCut (M : ℝ))) (shiftLine σ h₁)
              (fun p => X (p : ℕ) ω)‖ ^ 2)
            * Set.indicator T'
              (pairPoly (primesIco (scaleCut (M : ℝ)) y) (shiftLine σ h₁) (shiftLine σ h₂))
              (fun p => X (p : ℕ) ω) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        dsimp only
        rw [hψeq ω, primePoly_primesIco])
    have e2 : (∫ ω, ‖primePoly (primesIco (scaleCut (k : ℝ)) (scaleCut (M : ℝ))) (shiftLine σ h₁)
          (fun p => X (p : ℕ) ω)‖ ^ 2 ∂μ)
        = ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut k) (scaleCut (M : ℝ)) (shiftLine σ h₁) ω‖ ^ 2 ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        dsimp only
        rw [primePoly_primesIco])
    have e3 : (∫ ω, Set.indicator T' (pairPoly (primesIco (scaleCut (M : ℝ)) y) (shiftLine σ h₁)
          (shiftLine σ h₂)) (fun p => X (p : ℕ) ω) ∂μ)
        = ∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (M : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (M : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ := by
      rw [← integral_indicator hG]
      exact integral_congr_ae (Filter.Eventually.of_forall hψeq)
    rw [e1, hsplit₁, e2, e3]
  -- step 3: split at `c_top`, then the tilt
  have hφ₂ : Measurable (Set.indicator T
      (pairPoly (primesIco (scaleCut (M : ℝ)) (scaleCut ((t : ℝ) + 1))) (shiftLine σ h₁)
        (shiftLine σ h₂))) :=
    (measurable_pairPoly _ _ _).indicator hT
  have hsplit₂ := integral_mul_split_Ico hX hφ₂
    (measurable_pairPoly (primesIco (scaleCut ((t : ℝ) + 1)) y) (shiftLine σ h₁) (shiftLine σ h₂))
  have hstep3 : (∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (M : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (M : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
      = (∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (M : ℝ)) (scaleCut ((t : ℝ) + 1)) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (M : ℝ)) (scaleCut ((t : ℝ) + 1)) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut ((t : ℝ) + 1)) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut ((t : ℝ) + 1)) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ := by
    have hφeq : ∀ ω, Set.indicator T
          (pairPoly (primesIco (scaleCut (M : ℝ)) (scaleCut ((t : ℝ) + 1))) (shiftLine σ h₁)
            (shiftLine σ h₂)) (fun p => X (p : ℕ) ω)
        = Set.indicator G (fun ω =>
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (M : ℝ)) (scaleCut ((t : ℝ) + 1)) (shiftLine σ h₁) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (M : ℝ)) (scaleCut ((t : ℝ) + 1)) (shiftLine σ h₂) ω‖ ^ 2) ω := by
      intro ω
      by_cases hω : ω ∈ G
      · rw [Set.indicator_of_mem ((hGT ω).1 hω), Set.indicator_of_mem hω, pairPoly_primesIco]
      · rw [Set.indicator_of_notMem (fun hc => hω ((hGT ω).2 hc)), Set.indicator_of_notMem hω]
    have e1 : (∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (M : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (M : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        = ∫ ω, Set.indicator T
              (pairPoly (primesIco (scaleCut (M : ℝ)) (scaleCut ((t : ℝ) + 1))) (shiftLine σ h₁)
                (shiftLine σ h₂))
              (fun p => X (p : ℕ) ω)
            * pairPoly (primesIco (scaleCut ((t : ℝ) + 1)) y) (shiftLine σ h₁) (shiftLine σ h₂)
              (fun p => X (p : ℕ) ω) ∂μ := by
      rw [← integral_indicator hG]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      dsimp only
      rw [hφeq ω, pairPoly_primesIco]
      by_cases hω : ω ∈ G
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω,
          normSq_randomEulerProductIco_split (X := X) hMct hty (shiftLine σ h₁) ω,
          normSq_randomEulerProductIco_split (X := X) hMct hty (shiftLine σ h₂) ω]
        ring
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
    have e2 : (∫ ω, Set.indicator T
          (pairPoly (primesIco (scaleCut (M : ℝ)) (scaleCut ((t : ℝ) + 1))) (shiftLine σ h₁)
            (shiftLine σ h₂)) (fun p => X (p : ℕ) ω) ∂μ)
        = ∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (M : ℝ)) (scaleCut ((t : ℝ) + 1)) (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (M : ℝ)) (scaleCut ((t : ℝ) + 1)) (shiftLine σ h₂) ω‖ ^ 2 ∂μ := by
      rw [← integral_indicator hG]
      exact integral_congr_ae (Filter.Eventually.of_forall hφeq)
    have e3 : (∫ ω, pairPoly (primesIco (scaleCut ((t : ℝ) + 1)) y) (shiftLine σ h₁)
          (shiftLine σ h₂) (fun p => X (p : ℕ) ω) ∂μ)
        = ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut ((t : ℝ) + 1)) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut ((t : ℝ) + 1)) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        pairPoly_primesIco (scaleCut ((t : ℝ) + 1)) y _ _ ω)
    rw [e1, hsplit₂, e2, e3]
  have htilt := setIntegral_normSq_pair_Ico_eq_tilt hX hMct hs₁ hs₂ hT hGT
  have hmom := hf.integral_normSq_mul_normSq_Ico_split hMct hty (shiftLine σ h₁) (shiftLine σ h₂)
  refine le_trans hstep1 (le_of_eq ?_)
  rw [integral_const_mul, hstep2, hstep3, htilt, hmom]
  ring

/-! ### The shells

For `h₁, h₂` in the window with `e^{-(m+1)} < |h₁-h₂| ≤ e^{-m}`, split at `M = m + 2`, where the two
heights have decorrelated (`|h₁-h₂|e^M > e`).  Three regimes:
* far, `m - k ≤ (t-k)/3`: the pair barrier from `n₁ = m + 2 + ⌈log Tsh⌉ + j₀` on, whose tilted
  measure is `≪ (d+1)²/(t-k)` by Proposition 7, `d = m - k`;
* near, `m - k ≥ (t-k)/3`: the barrier's curvature at depth `M - k ≍ t - k` gives `(t-k)^{-4}`;
* top, `m ≥ t - 1` or `|h₁-h₂| ≤ e^{-t}`: split at `t`, the curvature again.
Each bound is `≪ e^{2t-3k+m}` times a factor summable over `m`. -/

/-- `blockCutoff k (t-k) = scaleCut (t+1)`: the tilt of Proposition 7 at the top of the barrier. -/
lemma blockCutoff_natCast_sub {k t : ℕ} (hkt : k ≤ t) :
    blockCutoff (k : ℝ) (t - k) = scaleCut ((t : ℝ) + 1) := by
  rw [blockCutoff, ← scaleCut_add]
  congr 1
  push_cast [Nat.cast_sub hkt]
  ring

/-- **The curvature beats a fourth power**: `e^{2β(d)}(d+1)⁴ ≤ e^{2(C₁+a)}e^{2d}(2(j₀+1))⁴`, since
past `j₀` the barrier's edge carries `-2 log(d - j₀)` and `d + 1 ≤ 2(j₀+1)(d - j₀)`. -/
lemma exp_halfBarrierTop_mul_pow_le {j₀ : ℕ} {C₁ a : ℝ} (ha : 0 ≤ a) (d : ℕ) :
    Real.exp (2 * halfBarrierTop j₀ C₁ a d) * ((d : ℝ) + 1) ^ 4
      ≤ Real.exp (2 * (C₁ + a)) * Real.exp (2 * (d : ℝ)) * (2 * ((j₀ : ℝ) + 1)) ^ 4 := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  unfold halfBarrierTop
  split_ifs with hdj
  · have h1 : Real.exp (2 * C₁) ≤ Real.exp (2 * (C₁ + a)) * Real.exp (2 * (d : ℝ)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have h2 : ((d : ℝ) + 1) ^ 4 ≤ (2 * ((j₀ : ℝ) + 1)) ^ 4 := by
      have : (d : ℝ) ≤ j₀ := by exact_mod_cast hdj
      exact pow_le_pow_left₀ (by positivity) (by linarith) 4
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  · have hjd : j₀ < d := by omega
    have he1 : (1 : ℝ) ≤ ((d - j₀ : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ d - j₀)
    have hepos : (0 : ℝ) < ((d - j₀ : ℕ) : ℝ) := by linarith
    have hdeq : (d : ℝ) = (j₀ : ℝ) + ((d - j₀ : ℕ) : ℝ) := by
      rw [Nat.cast_sub hjd.le]; ring
    -- `e^{2β} = e^{2(C₁+a)} e^{2(d-j₀)} (d-j₀)^{-4}`
    have hsplit : Real.exp (2 * (C₁ + a + ((d - j₀ : ℕ) : ℝ) + harperHf (d - j₀)))
        = Real.exp (2 * (C₁ + a)) * Real.exp (2 * ((d - j₀ : ℕ) : ℝ))
          / ((d - j₀ : ℕ) : ℝ) ^ 4 := by
      rw [harperHf, show 2 * (C₁ + a + ((d - j₀ : ℕ) : ℝ) + -2 * Real.log ((d - j₀ : ℕ) : ℝ))
          = 2 * (C₁ + a) + 2 * ((d - j₀ : ℕ) : ℝ) - 4 * Real.log ((d - j₀ : ℕ) : ℝ) by ring,
        Real.exp_sub, Real.exp_add, show (4 : ℝ) * Real.log ((d - j₀ : ℕ) : ℝ)
          = ((4 : ℕ) : ℝ) * Real.log ((d - j₀ : ℕ) : ℝ) by norm_num, Real.exp_nat_mul,
        Real.exp_log hepos]
    rw [hsplit]
    -- `d + 1 ≤ 2(j₀+1)(d - j₀)`
    have hd1 : (d : ℝ) + 1 ≤ 2 * ((j₀ : ℝ) + 1) * ((d - j₀ : ℕ) : ℝ) := by
      rw [hdeq]
      have hj0 : (0 : ℝ) ≤ (j₀ : ℝ) := Nat.cast_nonneg j₀
      nlinarith
    have hpow : ((d : ℝ) + 1) ^ 4 ≤ (2 * ((j₀ : ℝ) + 1)) ^ 4 * ((d - j₀ : ℕ) : ℝ) ^ 4 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hd1 4
    have hexp : Real.exp (2 * ((d - j₀ : ℕ) : ℝ)) ≤ Real.exp (2 * (d : ℝ)) :=
      Real.exp_le_exp.2 (by rw [hdeq]; have : (0 : ℝ) ≤ (j₀ : ℝ) := Nat.cast_nonneg j₀; linarith)
    have h4pos : (0 : ℝ) < ((d - j₀ : ℕ) : ℝ) ^ 4 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ h4pos]
    calc Real.exp (2 * (C₁ + a)) * Real.exp (2 * ((d - j₀ : ℕ) : ℝ)) * ((d : ℝ) + 1) ^ 4
        ≤ Real.exp (2 * (C₁ + a)) * Real.exp (2 * (d : ℝ))
          * ((2 * ((j₀ : ℝ) + 1)) ^ 4 * ((d - j₀ : ℕ) : ℝ) ^ 4) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le) hpow (by positivity)
            (by positivity)
      _ = _ := by ring

omit [MeasurableSpace Ω] in
/-- **The barrier, restarted.**  On `L(k,h)` the walk from block `j₀ + r` at offset `k`, for
`1 ≤ r ≤ t - k - j₀`, stays in Proposition 7's tube `[-a'' - B'j, a'' + j + 10 log j]`, for any
`a'' ≥ shiftedHeight a B harperHf r` and `B' ≥ B` (`RMF.freeStart_subset_barrierEvent`). -/
lemma halfBarrier_subset_restart {X : ℕ → Ω → ℂ} {σ h : ℝ} {k j₀ t r : ℕ} {C₁ a B a'' B' : ℝ}
    (hr1 : 1 ≤ r) (hrn : r ≤ t - k - j₀) (ha'' : shiftedHeight a B harperHf r ≤ a'')
    (hBB' : B ≤ B') :
    halfBarrier X σ h k j₀ t C₁ a B
      ⊆ barrierEvent (fun m => halfBlock X k σ h (m + (j₀ + r))) (t - k - j₀ - r)
          (fun j => -a'' - B' * j) (fun j => a'' + j + 10 * Real.log j) := by
  intro ω hω
  have hfree := freeStart_subset_barrierEvent (X := halfBlock X ((k : ℝ) + j₀) σ h)
    (a := a) (c := B) (hf := harperHf) hrn (fun j _ _ => abs_harperHf_le j)
    (fun j hj hjn => hω.2 j (le_trans hr1 hj) hjn)
  have hfun : (fun m => halfBlock X ((k : ℝ) + j₀) σ h (m + r))
      = fun m => halfBlock X k σ h (m + (j₀ + r)) := by
    funext m ω'
    simp only [halfBlock]
    rw [show m + (j₀ + r) = m + r + j₀ by omega, primeBlockSub_add (k : ℝ) (m + r) j₀]
  rw [hfun] at hfree
  intro j hj1 hjn
  obtain ⟨hl, hu⟩ := hfree j hj1 hjn
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  constructor
  · nlinarith
  · linarith

/-- Any cut at a scale `θ ≥ 0` with `σe^θ ≤ 1/10` lies below the truncation `⌈e^{1/(2σ)}⌉`. -/
lemma scaleCut_le_harperTruncation_of_le {θ σ : ℝ} (hθ : 0 ≤ θ) (hσ : 0 < σ)
    (htop : σ * Real.exp θ ≤ 1 / 10) : scaleCut θ ≤ harperTruncation σ := by
  have het : Real.exp θ < 1 / (2 * σ) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [Real.exp_pos θ]
  have hlt : blockScale θ 0 < Real.exp (1 / (2 * σ)) := by
    simp only [blockScale, Nat.cast_zero, zero_add]
    exact Real.exp_lt_exp.2 het
  unfold scaleCut harperTruncation
  have hfl : (⌊blockScale θ 0⌋₊ : ℝ) < ⌈Real.exp (1 / (2 * σ))⌉₊ :=
    lt_of_le_of_lt (Nat.floor_le (le_trans zero_le_two (two_le_blockScale_zero hθ)))
      (lt_of_lt_of_le hlt (Nat.le_ceil _))
  exact_mod_cast hfl

omit [MeasurableSpace Ω] in
/-- The blocks from `n₁` up to the barrier's top lie in `[scaleCut M, scaleCut (t+1))`, `M ≤ n₁`. -/
lemma mem_primesIco_of_mem_primeBlockSub {k M n₁ t N : ℕ} (hkn : k ≤ n₁) (hMn : M ≤ n₁)
    (hNt : n₁ + N ≤ t) :
    ∀ m, m < N → ∀ p ∈ primeBlockSub ((k : ℝ) + ((n₁ - k : ℕ) : ℝ)) m,
      ((p : Nat.Primes) : ℕ) ∈ primesIco (scaleCut (M : ℝ)) (scaleCut ((t : ℝ) + 1)) := by
  intro m hm p hp
  have hθ : ((k : ℝ) + ((n₁ - k : ℕ) : ℝ)) = (n₁ : ℝ) := by rw [Nat.cast_sub hkn]; ring
  rw [hθ, mem_primeBlockSub] at hp
  obtain ⟨hlo, hhi⟩ := hp
  have hMR : (M : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast hMn
  have hmR : (m : ℝ) + 1 + n₁ ≤ (t : ℝ) + 1 := by
    have : m + 1 + n₁ ≤ t + 1 := by omega
    exact_mod_cast this
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine mem_primesIco.2 ⟨p.2, ?_, ?_⟩
  · -- `e^{e^M} < p`, so `⌊e^{e^M}⌋ + 1 ≤ p`
    have h1 : blockScale (M : ℝ) 0 ≤ blockScale (n₁ : ℝ) m := by
      simp only [blockScale, Nat.cast_zero, zero_add]
      exact Real.exp_le_exp.2 (Real.exp_le_exp.2 (by linarith))
    have hlt : blockScale (M : ℝ) 0 < ((p : ℕ) : ℝ) := lt_of_le_of_lt h1 hlo
    have := (Nat.floor_lt (le_trans zero_le_two (two_le_blockScale_zero
      (Nat.cast_nonneg M)))).2 hlt
    unfold scaleCut
    omega
  · -- `p ≤ e^{e^{m+1+n₁}} ≤ e^{e^{t+1}}`, so `p < ⌊e^{e^{t+1}}⌋ + 1`
    have h1 : blockScale (n₁ : ℝ) (m + 1) ≤ blockScale ((t : ℝ) + 1) 0 := by
      simp only [blockScale, Nat.cast_zero, zero_add]
      push_cast
      exact Real.exp_le_exp.2 (Real.exp_le_exp.2 (by linarith))
    have hle : ((p : ℕ) : ℝ) ≤ blockScale ((t : ℝ) + 1) 0 := le_trans hhi h1
    have := Nat.le_floor hle
    unfold scaleCut
    omega

/-- The level of the restarted barrier grows linearly with the restart: for `r = d + 2 + c`,
`max(shiftedHeight a B harperHf r, T) ≤ (T + 2a + (B+13)(3+c))(d+1)`. -/
lemma max_shiftedHeight_le {a B T : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hT : 0 ≤ T) (c d : ℕ) :
    max (shiftedHeight a B harperHf (d + 2 + c)) T
      ≤ (T + 2 * a + (B + 13) * (3 + c)) * ((d : ℝ) + 1) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  set r : ℕ := d + 2 + c with hr
  have hrR : (r : ℝ) = (d : ℝ) + 2 + c := by rw [hr]; push_cast; ring
  have hlogr : Real.log (r : ℝ) ≤ (r : ℝ) := by
    have hr0 : (0 : ℝ) < (r : ℝ) := by rw [hrR]; linarith
    linarith [Real.log_le_sub_one_of_pos hr0]
  have hlog1r : Real.log (1 + (r : ℝ)) ≤ (r : ℝ) := by
    have h1 : (0 : ℝ) < 1 + (r : ℝ) := by rw [hrR]; linarith
    linarith [Real.log_le_sub_one_of_pos h1]
  have hlog0 : (0 : ℝ) ≤ Real.log (r : ℝ) := Real.log_natCast_nonneg r
  have hsh : shiftedHeight a B harperHf r ≤ 2 * a + (B + 13) * (r : ℝ) := by
    rw [shiftedHeight, harperHf, abs_mul, abs_of_nonneg hlog0,
      show |(-2 : ℝ)| = 2 from by norm_num]
    nlinarith
  have hr3 : (r : ℝ) ≤ (3 + c) * ((d : ℝ) + 1) := by rw [hrR]; nlinarith
  refine max_le ?_ ?_
  · calc shiftedHeight a B harperHf r ≤ 2 * a + (B + 13) * (r : ℝ) := hsh
      _ ≤ 2 * a * ((d : ℝ) + 1) + (B + 13) * ((3 + c) * ((d : ℝ) + 1)) := by
          have h1 : 2 * a ≤ 2 * a * ((d : ℝ) + 1) := by nlinarith
          have h2 := mul_le_mul_of_nonneg_left hr3 (by linarith : (0 : ℝ) ≤ B + 13)
          linarith
      _ ≤ (T + 2 * a + (B + 13) * (3 + c)) * ((d : ℝ) + 1) := by nlinarith
  · nlinarith

/-- The arithmetic of a far shell: the far factorisation `G ≤ e^{2β}(E₁(P̃E₂))` with
`E₁ ≤ x`, `P̃ ≤ Cst·q`, `q ≤ A₀²D²/N`, `E₂ ≤ K₂z`, the curvature `e^{2β}D⁴ ≤ c·y`, `yxz = w` and
`N ≥ TK/2` gives `G ≤ 2cA₀²·Cst·K₂·w/(D²·TK)`. -/
lemma far_shell_combine {G e E₁ P E₂ Cst K₂ q A₀ D N TK x y z w c : ℝ}
    (hG : G ≤ e * (E₁ * (P * E₂))) (he : 0 ≤ e) (hP : 0 ≤ P) (hE₂0 : 0 ≤ E₂)
    (hE₁ : E₁ ≤ x) (hPb : P ≤ Cst * q) (hE₂ : E₂ ≤ K₂ * z) (hq0 : 0 ≤ q)
    (hq : q ≤ A₀ ^ 2 * D ^ 2 / N) (heD : e * D ^ 4 ≤ c * y) (hw : y * x * z = w)
    (hNTK : TK ≤ 2 * N) (hD : 0 < D) (hTK : 0 < TK) (hCst : 0 ≤ Cst) (hK₂ : 0 ≤ K₂)
    (hx : 0 ≤ x) (hz : 0 ≤ z) (hc : 0 ≤ c) (hy : 0 ≤ y) :
    G ≤ 2 * c * A₀ ^ 2 * Cst * K₂ * w / (D ^ 2 * TK) := by
  have hN : 0 < N := by linarith
  have hw0 : 0 ≤ w := by rw [← hw]; positivity
  have hA : 0 ≤ Cst * K₂ * A₀ ^ 2 * x * z := by positivity
  calc G ≤ e * (E₁ * (P * E₂)) := hG
    _ ≤ e * (x * ((Cst * q) * (K₂ * z))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hE₁ (mul_le_mul hPb hE₂ hE₂0 (by positivity))
          (mul_nonneg hP hE₂0) hx) he
    _ ≤ e * (x * ((Cst * (A₀ ^ 2 * D ^ 2 / N)) * (K₂ * z))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq hCst) (by positivity)) hx) he
    _ = Cst * K₂ * A₀ ^ 2 * x * z * (e * D ^ 4) / (D ^ 2 * N) := by
        field_simp
    _ ≤ Cst * K₂ * A₀ ^ 2 * x * z * (c * y) / (D ^ 2 * N) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left heD hA) (by positivity)
    _ = 2 * c * A₀ ^ 2 * Cst * K₂ * w / (D ^ 2 * (2 * N)) := by
        rw [← hw]
        field_simp
    _ ≤ 2 * c * A₀ ^ 2 * Cst * K₂ * w / (D ^ 2 * TK) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hNTK (by positivity))

/-- **The far shells.**  For `k ≤ m ≤ k + (t-k)/3` and `e^{-(m+1)} < |h₁-h₂|`, the pair integrand is
`≤ K e^{2t-3k+m}/((m-k+1)²(t-k))`: `RMF.integral_indicator_pair_le_far` with `M = m + 2` and `G`
the pair barrier restarted at `n₁ = m + 2 + ⌈log Tsh⌉ + j₀` (`RMF.halfBarrier_subset_restart`),
whose tilted measure `RMF.exists_proposition7_upper_rademacher_window` bounds by `Cst(a''/√N)²`,
`N = t - n₁ ≥ (t-k)/2`, `a'' ≪ m - k + 1`; the curvature of `L(k,h₂)` at depth `M - k` pays for
`(m-k+1)⁴`. -/
theorem exists_far_shell_bound (j₀ : ℕ) (C₁ a B : ℝ) (hC₁ : 0 ≤ C₁) (ha : 0 ≤ a) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∃ k₁ T₁ : ℕ,
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (k t y m : ℕ) (σ h₁ h₂ : ℝ), k₁ ≤ k → k + T₁ ≤ t → 0 < σ →
        σ * Real.exp ((t : ℝ) + 1) ≤ 1 / 10 → Real.exp (-6) ≤ σ * Real.exp (t : ℝ) →
        harperTruncation σ < y → h₁ ∈ halfWindow k → h₂ ∈ halfWindow k →
        k ≤ m → 3 * m ≤ 2 * k + t → Real.exp (-((m : ℝ) + 1)) < |h₁ - h₂| →
        ∫ ω, Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut k) y (shiftLine σ h₁) ω‖ ^ 2) ω
            * Set.indicator (halfBarrier X σ h₂ k j₀ t C₁ a B)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut k) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ
          ≤ K * Real.exp (2 * (t : ℝ) - 3 * k + m) / (((m : ℝ) - k + 1) ^ 2 * ((t : ℝ) - k)) := by
  obtain ⟨K₂, hK₂, hdec⟩ := exists_integral_normSq_pair_Ico_decorr_le (Ω := Ω)
  have hB'1 : blockSlope 125 ≤ max B (blockSlope 125) := le_max_right _ _
  obtain ⟨Cst, Tsh, hCst, hTsh, H7⟩ := exists_proposition7_upper_rademacher_window _ hB'1
  obtain ⟨n₀, hn₀1, hn₀⟩ := exists_forall_log_pow_le
  set cT : ℕ := ⌈Real.log Tsh⌉₊ with hcT
  set T₀ : ℝ := max 1 (result1Threshold (1 / 18) (9 / 2)) with hT₀def
  have hT₀1 : (1 : ℝ) ≤ T₀ := le_max_left _ _
  set A₀ : ℝ := T₀ + 2 * a + (B + 13) * (3 + cT) with hA₀def
  have hA₀ : 0 < A₀ := by rw [hA₀def]; positivity
  refine ⟨2 * Real.exp 3 * Real.exp (2 * (C₁ + a)) * (2 * ((j₀ : ℝ) + 1)) ^ 4 * A₀ ^ 2 * Cst
      * K₂, by positivity, max 125 (max ⌈blockOffsetThresholdOf (max B (blockSlope 125))⌉₊ 20),
    6 * (cT + j₀ + 2) + 2 * n₀ + 8, ?_⟩
  intro X μ hX k t y m σ h₁ h₂ hk ht hσ htop hbot hy hh₁ hh₂ hkm hm3 hsep
  have hk125 : 125 ≤ k := le_trans (le_max_left _ _) hk
  have hk20 : 20 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hkc : ⌈blockOffsetThresholdOf (max B (blockSlope 125))⌉₊ ≤ k :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkthr : blockOffsetThresholdOf (max B (blockSlope 125)) ≤ (k : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hkc)
  obtain ⟨hh₁l, hh₁u⟩ := hh₁
  obtain ⟨hh₂l, hh₂u⟩ := hh₂
  -- the indices
  set n₁ : ℕ := m + 2 + cT + j₀ with hn₁
  set N : ℕ := t - n₁ with hN
  have hn₁t : n₁ + N = t := by omega
  have hNk : t - k ≤ 2 * N := by omega
  have hNn₀ : n₀ ≤ N := by omega
  have hN4 : 4 ≤ N := by omega
  have hr1 : 1 ≤ m - k + 2 + cT := by omega
  have hrn : m - k + 2 + cT ≤ t - k - j₀ := by omega
  have hjr : j₀ + (m - k + 2 + cT) = n₁ - k := by omega
  have hNr : t - k - j₀ - (m - k + 2 + cT) = N := by omega
  -- heights
  have hkR : (125 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk125
  have hek : Real.exp (-(k : ℝ)) ≤ 1 / 2 := by
    have h1 : Real.exp (-(k : ℝ)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    linarith [Real.exp_neg_one_lt_d9]
  have hpos₁ : 0 < h₁ := lt_of_lt_of_le (Real.exp_pos _) hh₁l
  have hpos₂ : 0 < h₂ := lt_of_lt_of_le (Real.exp_pos _) hh₂l
  have hne : h₁ ≠ h₂ := by
    intro heq
    rw [heq, sub_self, abs_zero] at hsep
    exact absurd hsep (not_lt.2 (Real.exp_pos _).le)
  -- the restarted pair barrier
  set a'' : ℝ := max (shiftedHeight a B harperHf (m - k + 2 + cT)) T₀ with ha''def
  have ha''0 : 0 ≤ a'' := le_trans (by linarith) (le_max_right _ _)
  set P : Set Ω := barrierEventPair
    (fun m' => blockPairAdd (k : ℝ) (shiftLine σ h₁) (shiftLine σ h₂) X (m' + (n₁ - k))) N
    (fun j => -a'' - max B (blockSlope 125) * j) (fun j => a'' + j + 10 * Real.log j)
    (fun j => -a'' - max B (blockSlope 125) * j) (fun j => a'' + j + 10 * Real.log j) with hPdef
  have hGsub : halfBarrier X σ h₁ k j₀ t C₁ a B ∩ halfBarrier X σ h₂ k j₀ t C₁ a B ⊆ P := by
    intro ω ⟨hω₁, hω₂⟩
    have e₁ := halfBarrier_subset_restart (a'' := a'') (B' := max B (blockSlope 125)) hr1 hrn
      (le_max_left _ _) (le_max_left _ _) hω₁
    have e₂ := halfBarrier_subset_restart (a'' := a'') (B' := max B (blockSlope 125)) hr1 hrn
      (le_max_left _ _) (le_max_left _ _) hω₂
    rw [hjr, hNr] at e₁ e₂
    exact ⟨e₁, e₂⟩
  obtain ⟨T, hT, hGT⟩ := exists_tuple_barrierEventPair (X := X)
    (S := primesIco (scaleCut ((m + 2 : ℕ) : ℝ)) (scaleCut ((t : ℝ) + 1)))
    (fun p hp => prime_of_mem_primesIco hp) (k : ℝ) (n₁ - k) N (shiftLine σ h₁) (shiftLine σ h₂)
    a'' (max B (blockSlope 125)) (fun j => 10 * Real.log j)
    (mem_primesIco_of_mem_primeBlockSub (by omega) (by omega) hn₁t.le)
  -- the far factorisation at `M = m + 2`
  have hty : scaleCut ((t : ℝ) + 1) ≤ y :=
    le_trans (scaleCut_le_harperTruncation_of_le (by positivity) hσ htop) hy.le
  have hfar := integral_indicator_pair_le_far hX hσ.le hC₁ (by omega : k ≤ m + 2)
    (by omega : m + 2 ≤ t) hty h₁ h₂ hGsub hT hGT
  -- Proposition 7 on the window
  have hP7 := H7 _ X μ hX k σ (1 / 10) a'' h₁ h₂ (t - k) (n₁ - k) N (fun j => 10 * Real.log j)
    hk125 (by
      have : ((k : ℝ) + ((n₁ - k : ℕ) : ℝ)) = (n₁ : ℝ) := by rw [Nat.cast_sub (by omega)]; ring
      rw [this]
      have : (k : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast (by omega : k ≤ n₁)
      linarith) (by omega) (by norm_num) le_rfl
    (by
      rw [abs_of_pos hσ, log_blockScale,
        show (((n₁ - k + N + 1 : ℕ) : ℝ) + (k : ℝ)) = (t : ℝ) + 1 by
          rw [show n₁ - k + N + 1 = t - k + 1 by omega]; push_cast [Nat.cast_sub (by omega :
            k ≤ t)]; ring]
      exact htop)
    hh₁l hh₁u hh₂l hh₂u hne
    (by
      -- `Tsh ≤ e^{cT} < |h₁ - h₂| e^{n₁}`
      have hcTR : Real.log Tsh ≤ (cT : ℝ) := Nat.le_ceil _
      have hTsh' : Tsh ≤ Real.exp (cT : ℝ) := by
        rw [← Real.exp_log hTsh]; exact Real.exp_le_exp.2 hcTR
      have hexp : (((n₁ - k : ℕ) : ℝ) + (k : ℝ)) = (n₁ : ℝ) := by
        rw [Nat.cast_sub (by omega)]; ring
      rw [hexp]
      have hsplit : Real.exp (n₁ : ℝ)
          = Real.exp ((m : ℝ) + 1) * Real.exp ((cT : ℝ) + (j₀ : ℝ) + 1) := by
        rw [← Real.exp_add]; congr 1; rw [hn₁]; push_cast; ring
      have h1 : Real.exp (cT : ℝ) ≤ Real.exp ((cT : ℝ) + (j₀ : ℝ) + 1) :=
        Real.exp_le_exp.2 (by have := Nat.cast_nonneg (α := ℝ) j₀; linarith)
      have h2 : 1 < |h₁ - h₂| * Real.exp ((m : ℝ) + 1) := by
        have := mul_lt_mul_of_pos_right hsep (Real.exp_pos ((m : ℝ) + 1))
        rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
      rw [hsplit]
      calc Tsh ≤ Real.exp ((cT : ℝ) + (j₀ : ℝ) + 1) := le_trans hTsh' h1
        _ = 1 * Real.exp ((cT : ℝ) + (j₀ : ℝ) + 1) := (one_mul _).symm
        _ ≤ (|h₁ - h₂| * Real.exp ((m : ℝ) + 1)) * Real.exp ((cT : ℝ) + (j₀ : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right h2.le (Real.exp_pos _).le
        _ = _ := by ring)
    (le_max_right _ _) hN4 (hn₀ N hNn₀).1 (hn₀ N hNn₀).2
    (fun j hj1 _ => by rw [abs_of_nonneg (by have := Real.log_natCast_nonneg j; linarith)])
  rw [blockCutoff_natCast_sub (by omega : k ≤ t)] at hP7
  -- the two moments
  have hE₁ := integral_normSq_Ico_scaleCut_le hX hk20 (by omega : k ≤ m + 2) hσ.le (h := h₁)
  have hE₂ := hdec X μ hX (m + 2) t y σ h₁ h₂ (by omega) (by omega) hσ htop hbot hy hpos₁.le
    (le_trans hh₁u hek) hpos₂.le (le_trans hh₂u hek) (by
      have h2 : 1 < |h₁ - h₂| * Real.exp ((m : ℝ) + 1) := by
        have := mul_lt_mul_of_pos_right hsep (Real.exp_pos ((m : ℝ) + 1))
        rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
      have he : Real.exp (((m + 2 : ℕ) : ℝ)) = Real.exp ((m : ℝ) + 1) * Real.exp 1 := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      rw [he]
      calc (2 : ℝ) ≤ 1 * Real.exp 1 := by linarith
        _ ≤ (|h₁ - h₂| * Real.exp ((m : ℝ) + 1)) * Real.exp 1 :=
            mul_le_mul_of_nonneg_right h2.le (Real.exp_pos _).le
        _ = _ := by ring)
  -- the arithmetic
  have hmk : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := Nat.cast_sub hkm
  have hm2k : ((m + 2 - k : ℕ) : ℝ) = (m : ℝ) + 2 - k := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hD : 0 < (m : ℝ) - k + 1 := by
    have : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    linarith
  have hTK : 0 < (t : ℝ) - k := by
    have : (k : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ t)
    linarith
  have hNR : (t : ℝ) - k ≤ 2 * (N : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).2 hNk
    rw [Nat.cast_sub (by omega : k ≤ t)] at h
    push_cast at h
    exact h
  have ha''le : a'' ≤ A₀ * ((m : ℝ) - k + 1) := by
    have h := max_shiftedHeight_le ha hB (by linarith : (0 : ℝ) ≤ T₀) cT (m - k)
    rw [hmk] at h
    exact h
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hq : min 1 (a'' / Real.sqrt (N : ℝ)) ^ 2 ≤ A₀ ^ 2 * ((m : ℝ) - k + 1) ^ 2 / (N : ℝ) := by
    have hv0 : 0 ≤ a'' / Real.sqrt (N : ℝ) := div_nonneg ha''0 (Real.sqrt_nonneg _)
    have hmin0 : 0 ≤ min 1 (a'' / Real.sqrt (N : ℝ)) := le_min zero_le_one hv0
    calc min 1 (a'' / Real.sqrt (N : ℝ)) ^ 2 ≤ (a'' / Real.sqrt (N : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hmin0 (min_le_right _ _) 2
      _ = a'' ^ 2 / (N : ℝ) := by rw [div_pow, Real.sq_sqrt hNpos.le]
      _ ≤ (A₀ * ((m : ℝ) - k + 1)) ^ 2 / (N : ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ ha''0 ha''le 2) hNpos.le
      _ = A₀ ^ 2 * ((m : ℝ) - k + 1) ^ 2 / (N : ℝ) := by ring
  have heD : Real.exp (2 * halfBarrierTop j₀ C₁ a (m + 2 - k)) * ((m : ℝ) - k + 1) ^ 4
      ≤ (Real.exp (2 * (C₁ + a)) * (2 * ((j₀ : ℝ) + 1)) ^ 4)
        * Real.exp (2 * ((m + 2 - k : ℕ) : ℝ)) := by
    have h := exp_halfBarrierTop_mul_pow_le (j₀ := j₀) (C₁ := C₁) ha (m + 2 - k)
    have hle : ((m : ℝ) - k + 1) ^ 4 ≤ (((m + 2 - k : ℕ) : ℝ) + 1) ^ 4 :=
      pow_le_pow_left₀ hD.le (by rw [hm2k]; linarith) 4
    calc Real.exp (2 * halfBarrierTop j₀ C₁ a (m + 2 - k)) * ((m : ℝ) - k + 1) ^ 4
        ≤ Real.exp (2 * halfBarrierTop j₀ C₁ a (m + 2 - k)) * (((m + 2 - k : ℕ) : ℝ) + 1) ^ 4 :=
          mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
      _ ≤ _ := h
      _ = _ := by ring
  have hw : Real.exp (2 * ((m + 2 - k : ℕ) : ℝ)) * Real.exp (((m + 2 : ℕ) : ℝ) - k + 1)
        * Real.exp (2 * ((t : ℝ) - ((m + 2 : ℕ) : ℝ)))
      = Real.exp 3 * Real.exp (2 * (t : ℝ) - 3 * k + m) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hm2k]
    congr 1
    push_cast
    ring
  have hfinal := far_shell_combine hfar (Real.exp_pos _).le ENNReal.toReal_nonneg
    (integral_nonneg fun ω => by positivity) hE₁ hP7 hE₂ (sq_nonneg _) hq heD hw hNR hD hTK
    hCst.le hK₂.le (Real.exp_pos _).le (Real.exp_pos _).le (by positivity) (Real.exp_pos _).le
  refine le_trans hfinal (le_of_eq ?_)
  ring

/-- The arithmetic of a near shell: `G ≤ e^{2β}(E₁E₂)` with `E₁ ≤ x`, `E₂ ≤ K₂z`, the curvature
`e^{2β}D⁴ ≤ c·y` at a depth `D ≥ TK/3`, and `yxz = w` gives `G ≤ 81·c·K₂·w/TK⁴`. -/
lemma near_shell_combine {G e E₁ E₂ K₂ D TK x y z w c : ℝ}
    (hG : G ≤ e * (E₁ * E₂)) (he : 0 ≤ e) (hE₁0 : 0 ≤ E₁) (hE₂0 : 0 ≤ E₂) (hE₁ : E₁ ≤ x)
    (hE₂ : E₂ ≤ K₂ * z)
    (heD : e * D ^ 4 ≤ c * y) (hw : y * x * z = w) (hDTK : TK ≤ 3 * D) (hTK : 0 < TK)
    (hx : 0 ≤ x) (hc : 0 ≤ c) (hy : 0 ≤ y) :
    G ≤ 81 * c * K₂ * w / TK ^ 4 := by
  have hD : 0 < D := by linarith
  have hD4 : TK ^ 4 ≤ 81 * D ^ 4 := by
    have := pow_le_pow_left₀ hTK.le hDTK 4
    nlinarith [this]
  have he' : e ≤ 81 * (c * y) / TK ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    calc e * TK ^ 4 ≤ e * (81 * D ^ 4) := mul_le_mul_of_nonneg_left hD4 he
      _ = 81 * (e * D ^ 4) := by ring
      _ ≤ 81 * (c * y) := by linarith
  calc G ≤ e * (E₁ * E₂) := hG
    _ ≤ (81 * (c * y) / TK ^ 4) * (x * (K₂ * z)) :=
        mul_le_mul he' (mul_le_mul hE₁ hE₂ hE₂0 hx) (mul_nonneg hE₁0 hE₂0)
          (div_nonneg (mul_nonneg (by norm_num) (mul_nonneg hc hy)) (by positivity))
    _ = 81 * c * K₂ * (y * x * z) / TK ^ 4 := by ring
    _ = 81 * c * K₂ * w / TK ^ 4 := by rw [hw]

/-- **The near shells.**  For `m - k > (t-k)/3`, `m + 2 ≤ t` and `e^{-(m+1)} < |h₁-h₂|`, the pair
integrand is `≤ K e^{2t-3k+m}/(t-k)⁴`: the curvature of `L(k,h₂)` at depth `m + 2 - k ≍ t - k`. -/
theorem exists_near_shell_bound (j₀ : ℕ) (C₁ a B : ℝ) (hC₁ : 0 ≤ C₁) (ha : 0 ≤ a) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (k t y m : ℕ) (σ h₁ h₂ : ℝ), 20 ≤ k → 0 < σ →
        σ * Real.exp ((t : ℝ) + 1) ≤ 1 / 10 → Real.exp (-6) ≤ σ * Real.exp (t : ℝ) →
        harperTruncation σ < y → h₁ ∈ halfWindow k → h₂ ∈ halfWindow k →
        2 * k + t < 3 * m → m + 2 ≤ t → Real.exp (-((m : ℝ) + 1)) < |h₁ - h₂| →
        ∫ ω, Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut k) y (shiftLine σ h₁) ω‖ ^ 2) ω
            * Set.indicator (halfBarrier X σ h₂ k j₀ t C₁ a B)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut k) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ
          ≤ K * Real.exp (2 * (t : ℝ) - 3 * k + m) / ((t : ℝ) - k) ^ 4 := by
  obtain ⟨K₂, hK₂, hdec⟩ := exists_integral_normSq_pair_Ico_decorr_le (Ω := Ω)
  refine ⟨81 * (Real.exp (2 * (C₁ + a)) * (2 * ((j₀ : ℝ) + 1)) ^ 4) * K₂ * Real.exp 3,
    by positivity, ?_⟩
  intro X μ hX k t y m σ h₁ h₂ hk hσ htop hbot hy hh₁ hh₂ hm3 hmt hsep
  obtain ⟨hh₁l, hh₁u⟩ := hh₁
  obtain ⟨hh₂l, hh₂u⟩ := hh₂
  have hkR : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hek : Real.exp (-(k : ℝ)) ≤ 1 / 2 := by
    have h1 : Real.exp (-(k : ℝ)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    linarith [Real.exp_neg_one_lt_d9]
  have hpos₁ : 0 < h₁ := lt_of_lt_of_le (Real.exp_pos _) hh₁l
  have hpos₂ : 0 < h₂ := lt_of_lt_of_le (Real.exp_pos _) hh₂l
  have hMy : scaleCut ((m + 2 : ℕ) : ℝ) ≤ y :=
    le_trans (scaleCut_le_harperTruncation hmt hσ htop) hy.le
  have hnear := integral_indicator_pair_le_near hX hσ.le (j₀ := j₀) (a := a) (B := B) hC₁
    (by omega : k ≤ m + 2) hmt hMy h₁ h₂
  have hE₁ := integral_normSq_Ico_scaleCut_le hX hk (by omega : k ≤ m + 2) hσ.le (h := h₁)
  have h2 : 1 < |h₁ - h₂| * Real.exp ((m : ℝ) + 1) := by
    have := mul_lt_mul_of_pos_right hsep (Real.exp_pos ((m : ℝ) + 1))
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  have hE₂ := hdec X μ hX (m + 2) t y σ h₁ h₂ (by omega) hmt hσ htop hbot hy hpos₁.le
    (le_trans hh₁u hek) hpos₂.le (le_trans hh₂u hek) (by
      have he : Real.exp (((m + 2 : ℕ) : ℝ)) = Real.exp ((m : ℝ) + 1) * Real.exp 1 := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      rw [he]
      calc (2 : ℝ) ≤ 1 * Real.exp 1 := by linarith
        _ ≤ (|h₁ - h₂| * Real.exp ((m : ℝ) + 1)) * Real.exp 1 :=
            mul_le_mul_of_nonneg_right h2.le (Real.exp_pos _).le
        _ = _ := by ring)
  have hm2k : ((m + 2 - k : ℕ) : ℝ) = (m : ℝ) + 2 - k := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hTK : 0 < (t : ℝ) - k := by
    have : (k : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ t)
    linarith
  have hw : Real.exp (2 * ((m + 2 - k : ℕ) : ℝ)) * Real.exp (((m + 2 : ℕ) : ℝ) - k + 1)
        * Real.exp (2 * ((t : ℝ) - ((m + 2 : ℕ) : ℝ)))
      = Real.exp 3 * Real.exp (2 * (t : ℝ) - 3 * k + m) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hm2k]
    congr 1
    push_cast
    ring
  have heD := exp_halfBarrierTop_mul_pow_le (j₀ := j₀) (C₁ := C₁) ha (m + 2 - k)
  have hDTK : (t : ℝ) - k ≤ 3 * (((m + 2 - k : ℕ) : ℝ) + 1) := by
    rw [hm2k]
    have : (2 * k + t : ℝ) < 3 * m := by exact_mod_cast hm3
    linarith
  have hfinal := near_shell_combine hnear (Real.exp_pos _).le
    (integral_nonneg fun ω => by positivity) (integral_nonneg fun ω => by positivity) hE₁ hE₂
    (by rw [show Real.exp (2 * (C₁ + a)) * (2 * ((j₀ : ℝ) + 1)) ^ 4
          * Real.exp (2 * ((m + 2 - k : ℕ) : ℝ))
        = Real.exp (2 * (C₁ + a)) * Real.exp (2 * ((m + 2 - k : ℕ) : ℝ))
          * (2 * ((j₀ : ℝ) + 1)) ^ 4 by ring]; exact heD)
    hw hDTK hTK (Real.exp_pos _).le (by positivity) (Real.exp_pos _).le
  refine le_trans hfinal (le_of_eq ?_)
  ring

/-- **The top shell.**  For any two heights in the window, the pair integrand is
`≤ K e^{3(t-k)}/(t-k)⁴`: split at `t`, where only the sum frequency oscillates
(`RMF.exists_integral_normSq_pair_Ico_sum_le`) and the curvature at depth `t - k` pays. -/
theorem exists_top_shell_bound (j₀ : ℕ) (C₁ a B : ℝ) (hC₁ : 0 ≤ C₁) (ha : 0 ≤ a) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (k t y : ℕ) (σ h₁ h₂ : ℝ), 20 ≤ k → k + 1 ≤ t → 0 < σ →
        σ * Real.exp ((t : ℝ) + 1) ≤ 1 / 10 → Real.exp (-6) ≤ σ * Real.exp (t : ℝ) →
        harperTruncation σ < y → h₁ ∈ halfWindow k → h₂ ∈ halfWindow k →
        ∫ ω, Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut k) y (shiftLine σ h₁) ω‖ ^ 2) ω
            * Set.indicator (halfBarrier X σ h₂ k j₀ t C₁ a B)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut k) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ
          ≤ K * Real.exp (3 * ((t : ℝ) - k)) / ((t : ℝ) - k) ^ 4 := by
  obtain ⟨K₃, hK₃, hsum⟩ := exists_integral_normSq_pair_Ico_sum_le (Ω := Ω)
  refine ⟨81 * (Real.exp (2 * (C₁ + a)) * (2 * ((j₀ : ℝ) + 1)) ^ 4) * K₃ * Real.exp 1,
    by positivity, ?_⟩
  intro X μ hX k t y σ h₁ h₂ hk hkt hσ htop hbot hy hh₁ hh₂
  obtain ⟨hh₁l, hh₁u⟩ := hh₁
  obtain ⟨hh₂l, hh₂u⟩ := hh₂
  have hkR : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hek : Real.exp (-(k : ℝ)) ≤ 1 / 4 := by
    have h1 : Real.exp (-(k : ℝ)) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-2) = Real.exp (-1) * Real.exp (-1) := by rw [← Real.exp_add]; norm_num
    have h3 := Real.exp_neg_one_lt_d9
    nlinarith [Real.exp_pos (-1)]
  have hpos₁ : 0 < h₁ := lt_of_lt_of_le (Real.exp_pos _) hh₁l
  have hpos₂ : 0 < h₂ := lt_of_lt_of_le (Real.exp_pos _) hh₂l
  have hty : scaleCut (t : ℝ) ≤ y := le_trans (scaleCut_le_harperTruncation le_rfl hσ htop) hy.le
  have hnear := integral_indicator_pair_le_near hX hσ.le (j₀ := j₀) (a := a) (B := B) hC₁
    (by omega : k ≤ t) le_rfl hty h₁ h₂
  have hE₁ := integral_normSq_Ico_scaleCut_le hX hk (by omega : k ≤ t) hσ.le (h := h₁)
  have hE₂ := hsum X μ hX t t y σ h₁ h₂ (by omega) le_rfl hσ htop hbot hy hpos₁.le hpos₂.le
    (by linarith) (by
      -- `(h₁ + h₂)e^t ≥ 2e^{t-k-1} ≥ 2`
      have hkt' : ((k : ℝ) + 1) ≤ (t : ℝ) := by exact_mod_cast hkt
      have he : 1 ≤ Real.exp (-((k : ℝ) + 1)) * Real.exp (t : ℝ) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
      nlinarith [Real.exp_pos (t : ℝ)])
  have htk : ((t - k : ℕ) : ℝ) = (t : ℝ) - k := Nat.cast_sub (by omega)
  have hTK : 0 < (t : ℝ) - k := by
    have : (k : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast hkt
    linarith
  have hw : Real.exp (2 * ((t - k : ℕ) : ℝ)) * Real.exp ((t : ℝ) - k + 1)
        * Real.exp (4 * ((t : ℝ) - t))
      = Real.exp 1 * Real.exp (3 * ((t : ℝ) - k)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, htk]
    congr 1
    ring
  have heD := exp_halfBarrierTop_mul_pow_le (j₀ := j₀) (C₁ := C₁) ha (t - k)
  have hfinal := near_shell_combine hnear (Real.exp_pos _).le
    (integral_nonneg fun ω => by positivity) (integral_nonneg fun ω => by positivity) hE₁ hE₂
    (by rw [show Real.exp (2 * (C₁ + a)) * (2 * ((j₀ : ℝ) + 1)) ^ 4
          * Real.exp (2 * ((t - k : ℕ) : ℝ))
        = Real.exp (2 * (C₁ + a)) * Real.exp (2 * ((t - k : ℕ) : ℝ))
          * (2 * ((j₀ : ℝ) + 1)) ^ 4 by ring]; exact heD)
    hw (by rw [htk]; linarith) hTK (Real.exp_pos _).le (by positivity) (Real.exp_pos _).le
  refine le_trans hfinal (le_of_eq ?_)
  ring

/-! ### Integrating over the window -/

/-- **Integrating a shell bound over the window**: if `0 ≤ G` and
`G h₁ h₂ ≤ ∑_{d < n} b_d·1[|h₁ - h₂| ≤ r_d]` for `h₁, h₂ ∈ W`, then
`∫_W ∫_W G ≤ vol(W)·∑_d b_d·2r_d`, since `{h₂ : |h₁ - h₂| ≤ r}` has measure `2r`. -/
lemma setIntegral_setIntegral_le_of_shells {W : Set ℝ} (hW : MeasurableSet W)
    (hWfin : volume W ≠ ⊤) {G : ℝ → ℝ → ℝ} (hG0 : ∀ h₁ h₂, 0 ≤ G h₁ h₂) (n : ℕ)
    {b r : ℕ → ℝ} (hb : ∀ d, 0 ≤ b d) (hr : ∀ d, 0 ≤ r d)
    (hGb : ∀ h₁ ∈ W, ∀ h₂ ∈ W, G h₁ h₂
      ≤ ∑ d ∈ Finset.range n, Set.indicator (Metric.closedBall h₁ (r d)) (fun _ => b d) h₂) :
    (∫ h₁ in W, ∫ h₂ in W, G h₁ h₂) ≤ volume.real W * ∑ d ∈ Finset.range n, b d * (2 * r d) := by
  haveI : IsFiniteMeasure (volume.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hWfin⟩
  have hinner : ∀ h₁ ∈ W,
      (∫ h₂ in W, G h₁ h₂) ≤ ∑ d ∈ Finset.range n, b d * (2 * r d) := by
    intro h₁ hh₁
    have hint : Integrable (fun h₂ => ∑ d ∈ Finset.range n,
        Set.indicator (Metric.closedBall h₁ (r d)) (fun _ => b d) h₂) (volume.restrict W) :=
      integrable_finsetSum _ fun d _ => (integrable_const (b d)).indicator measurableSet_closedBall
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun h₂ => hG0 h₁ h₂)
      hint ((ae_restrict_iff' hW).2 (Filter.Eventually.of_forall fun h₂ hh₂ =>
        hGb h₁ hh₁ h₂ hh₂))) ?_
    rw [integral_finsetSum _ fun d _ =>
      (integrable_const (b d)).indicator measurableSet_closedBall]
    refine Finset.sum_le_sum fun d _ => ?_
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul]
    have hmeas : (volume.restrict W).real (Metric.closedBall h₁ (r d)) ≤ 2 * r d := by
      rw [Measure.real, Measure.restrict_apply measurableSet_closedBall]
      have h1 : volume (Metric.closedBall h₁ (r d) ∩ W) ≤ volume (Metric.closedBall h₁ (r d)) :=
        measure_mono Set.inter_subset_left
      rw [Real.volume_closedBall] at h1
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal (by linarith [hr d])] at h2
    have := mul_le_mul_of_nonneg_right hmeas (hb d)
    linarith
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun h₁ =>
    integral_nonneg fun h₂ => hG0 h₁ h₂) (integrable_const _)
    ((ae_restrict_iff' hW).2 (Filter.Eventually.of_forall hinner))) ?_
  rw [setIntegral_const, smul_eq_mul]

/-- The shell of a pair of heights: for `e^{-t} < δ < e^{-k}`, `m = ⌊log(1/δ)⌋` has
`k ≤ m < t` and `e^{-(m+1)} < δ ≤ e^{-m}`. -/
lemma exists_shell_index {δ : ℝ} {k t : ℕ} (hδt : Real.exp (-(t : ℝ)) < δ)
    (hδk : δ < Real.exp (-(k : ℝ))) :
    ∃ m : ℕ, k ≤ m ∧ m < t ∧ δ ≤ Real.exp (-(m : ℝ)) ∧ Real.exp (-((m : ℝ) + 1)) < δ := by
  have hδ0 : 0 < δ := lt_trans (Real.exp_pos _) hδt
  have hlog : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  have hlk : (k : ℝ) < Real.log (1 / δ) := by
    rw [hlog]
    have := Real.log_lt_log hδ0 hδk
    rw [Real.log_exp] at this
    linarith
  have hlt : Real.log (1 / δ) < (t : ℝ) := by
    rw [hlog]
    have := Real.log_lt_log (Real.exp_pos _) hδt
    rw [Real.log_exp] at this
    linarith
  have hl0 : 0 ≤ Real.log (1 / δ) := le_trans (Nat.cast_nonneg k) hlk.le
  refine ⟨⌊Real.log (1 / δ)⌋₊, Nat.le_floor hlk.le, ?_, ?_, ?_⟩
  · exact_mod_cast lt_of_le_of_lt (Nat.floor_le hl0) hlt
  · have h1 := Nat.floor_le hl0
    have : Real.log δ ≤ -(⌊Real.log (1 / δ)⌋₊ : ℝ) := by linarith
    calc δ = Real.exp (Real.log δ) := (Real.exp_log hδ0).symm
      _ ≤ Real.exp (-(⌊Real.log (1 / δ)⌋₊ : ℝ)) := Real.exp_le_exp.2 this
  · have h1 := Nat.lt_floor_add_one (Real.log (1 / δ))
    have : -((⌊Real.log (1 / δ)⌋₊ : ℝ) + 1) < Real.log δ := by linarith
    calc Real.exp (-((⌊Real.log (1 / δ)⌋₊ : ℝ) + 1)) < Real.exp (Real.log δ) :=
          Real.exp_lt_exp.2 this
      _ = δ := Real.exp_log hδ0

/-- The window is shorter than `e^{-k}`, so two of its heights are closer than `e^{-k}`. -/
lemma abs_sub_lt_of_mem_halfWindow {k : ℕ} {h₁ h₂ : ℝ} (hh₁ : h₁ ∈ halfWindow k)
    (hh₂ : h₂ ∈ halfWindow k) : |h₁ - h₂| < Real.exp (-(k : ℝ)) := by
  obtain ⟨h₁l, h₁u⟩ := hh₁
  obtain ⟨h₂l, h₂u⟩ := hh₂
  have hpos := Real.exp_pos (-((k : ℝ) + 1))
  rw [abs_lt]
  constructor <;> linarith

lemma shell_le_left {Kx K E u v : ℝ} (hK : Kx ≤ K) (hKx : 0 ≤ Kx) (hE : 0 ≤ E) (hu : 0 ≤ u)
    (hv : 0 ≤ v) : Kx * E * u ≤ K * E * (u + v) := by
  have h1 : Kx * E * u ≤ K * E * u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hE) hu
  have h2 : K * E * u ≤ K * E * (u + v) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (le_trans hKx hK) hE)
  linarith

lemma shell_le_right {Kx K E u v : ℝ} (hK : Kx ≤ K) (hKx : 0 ≤ Kx) (hE : 0 ≤ E) (hu : 0 ≤ u)
    (hv : 0 ≤ v) : Kx * E * v ≤ K * E * (u + v) := by
  have h := shell_le_left (u := v) (v := u) hK hKx hE hv hu
  linarith

/-- The final sum: `∑_{d ≤ T} (1/T⁴ + 1/((d+1)²T)) ≤ 4/T` for `T ≥ 1`. -/
lemma sum_shell_weights_le {T : ℝ} (hT : 1 ≤ T) (n : ℕ) (hn : (n : ℝ) ≤ T + 1) :
    ∑ d ∈ Finset.range n, (1 / T ^ 4 + 1 / (((d : ℝ) + 1) ^ 2 * T)) ≤ 4 / T := by
  have hT0 : 0 < T := by linarith
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsq : ∑ d ∈ Finset.range n, 1 / (((d : ℝ) + 1) ^ 2 * T)
      = (∑ d ∈ Finset.range n, (1 : ℝ) / ((d : ℝ) + 1) ^ 2) / T := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [div_div]
  rw [hsq]
  have h2 := sum_inv_sq_range_le_two n
  have h1 : (n : ℝ) * (1 / T ^ 4) ≤ 2 / T := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hT0]
    have hT2 : T ≤ T ^ 2 := by nlinarith
    have hT4 : T ^ 2 ≤ T ^ 4 := by nlinarith
    have hn2 : (n : ℝ) ≤ 2 * T := by linarith
    have hnT : (n : ℝ) * T ≤ 2 * T * T := mul_le_mul_of_nonneg_right hn2 hT0.le
    nlinarith
  have h3 : (∑ d ∈ Finset.range n, (1 : ℝ) / ((d : ℝ) + 1) ^ 2) / T ≤ 2 / T :=
    div_le_div_of_nonneg_right h2 hT0.le
  calc (n : ℝ) * (1 / T ^ 4) + (∑ d ∈ Finset.range n, (1 : ℝ) / ((d : ℝ) + 1) ^ 2) / T
      ≤ 2 / T + 2 / T := add_le_add h1 h3
    _ = 4 / T := by ring

/-- **The barriered second moment**, Proposition 6.4 of the paper.  For any barrier constants
`C₁, a, B ≥ 0` and `j₀` there are `C`, `k₁` and `T₀` with, for `k ≥ k₁` and `t - k ≥ T₀`,

`E[(∫_{h ∈ [e^{-(k+1)}, e^{-k}]} 1_{L(k,h)} |F_{(k,y)}(½+σ+ih)|² dh)²] ≤ C e^{2t-4k}/(t-k)`,

where `F_{(k,y)}` is the Euler product over the primes with `log log p > k` below `y`, `t` is the
barrier's top scale, and `σ` is tied to it by `e^{-6} ≤ σe^t` and `σe^{t+1} ≤ 1/10`.  The upper
tie keeps the tilt small up to `t`; the lower one, with `y` past the truncation `e^{1/(2σ)}`
(`RMF.harperTruncation`), makes the primes beyond `t` contribute `O(1)`: the two-point moments
above a scale `M` are `≪ (log e^{1/(2σ)} / e^M)^2 ≍ e^{2(t-M)}`.

The square is `∫_W ∫_W E[1_{L h₁}‖F(h₁)‖²·1_{L h₂}‖F(h₂)‖²]`; for `e^{-(m+1)} < |h₁-h₂| ≤ e^{-m}`
the integrand is `≪ e^{2t-3k+m}((t-k)^{-4} + 1/((m-k+1)²(t-k)))` by the far, near and top shell
bounds, and shell `m` has measure `≤ 2e^{-m}` about each `h₁`; the sum over `m` is
`RMF.sum_shell_weights_le`. -/
theorem exists_integral_sq_setIntegral_halfBarrier_le (j₀ : ℕ) (C₁ a B : ℝ) (hC₁ : 0 ≤ C₁)
    (ha : 0 ≤ a) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₁ T₀ : ℕ,
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (k t y : ℕ) (σ : ℝ), k₁ ≤ k → k + T₀ ≤ t → 0 < σ →
        σ * Real.exp ((t : ℝ) + 1) ≤ 1 / 10 → Real.exp (-6) ≤ σ * Real.exp (t : ℝ) →
        harperTruncation σ < y →
        ∫ ω, (∫ h in halfWindow k, Set.indicator (halfBarrier X σ h k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut k) y (shiftLine σ h) ω‖ ^ 2) ω) ^ 2 ∂μ
          ≤ C * Real.exp (2 * (t : ℝ) - 4 * k) / ((t : ℝ) - k) := by
  obtain ⟨Kf, hKf, kf, Tf, Hfar⟩ := exists_far_shell_bound (Ω := Ω) j₀ C₁ a B hC₁ ha hB
  obtain ⟨Kn, hKn, Hnear⟩ := exists_near_shell_bound (Ω := Ω) j₀ C₁ a B hC₁ ha
  obtain ⟨Kc, hKc, Htop⟩ := exists_top_shell_bound (Ω := Ω) j₀ C₁ a B hC₁ ha
  refine ⟨8 * (Kf + Kn + Kc * Real.exp 1), by positivity, max kf 20, Tf + 1, ?_⟩
  intro X μ hX k t y σ hk ht hσ htop hbot hy
  set K : ℝ := Kf + Kn + Kc * Real.exp 1 with hKdef
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hKce0 : 0 ≤ Kc * Real.exp 1 := mul_nonneg hKc.le (Real.exp_pos 1).le
  have hKfK : Kf ≤ K := by rw [hKdef]; linarith
  have hKnK : Kn ≤ K := by rw [hKdef]; linarith
  have hKceK : Kc * Real.exp 1 ≤ K := by rw [hKdef]; linarith
  have hKcK : Kc ≤ K := le_trans (le_mul_of_one_le_right hKc.le he1) hKceK
  have hkf : kf ≤ k := le_trans (le_max_left _ _) hk
  have hk20 : 20 ≤ k := le_trans (le_max_right _ _) hk
  have hkt : k + 1 ≤ t := by omega
  have hTK1 : 1 ≤ (t : ℝ) - k := by
    have : (k : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast hkt
    linarith
  have hTK : 0 < (t : ℝ) - k := by linarith
  have hWm : MeasurableSet (halfWindow k) := measurableSet_Icc
  have hWfin : volume (halfWindow k) ≠ ⊤ := by
    rw [halfWindow, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  -- the shell weights, indexed by `m = k + d`
  have hv : ∀ d : ℕ, 0 ≤ 1 / ((((k + d : ℕ) : ℝ) - k + 1) ^ 2 * ((t : ℝ) - k)) := fun d => by
    have : (((k + d : ℕ) : ℝ) - k + 1) = (d : ℝ) + 1 := by push_cast; ring
    rw [this]
    exact div_nonneg zero_le_one (mul_nonneg (by positivity) hTK.le)
  have hu : 0 ≤ 1 / ((t : ℝ) - k) ^ 4 := by positivity
  have hb : ∀ d : ℕ, 0 ≤ K * Real.exp (2 * (t : ℝ) - 3 * k + ((k + d : ℕ) : ℝ))
      * (1 / ((t : ℝ) - k) ^ 4 + 1 / ((((k + d : ℕ) : ℝ) - k + 1) ^ 2 * ((t : ℝ) - k))) :=
    fun d => mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (add_nonneg hu (hv d))
  -- the expansion, then the shell bound
  refine le_trans (le_of_eq (integral_sq_setIntegral_indicator_normSq_Ico_eq hX (scaleCut k) y
    hσ.le (fun h => halfBarrier X σ h k j₀ t C₁ a B)
    (fun h => measurableSet_halfBarrier hX σ h k j₀ t C₁ a B)
    (measurableSet_prod_halfBarrier hX σ k j₀ t C₁ a B) hWfin)) ?_
  refine le_trans (setIntegral_setIntegral_le_of_shells hWm hWfin
    (G := fun h₁ h₂ => ∫ ω, Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut k) y (shiftLine σ h₁) ω‖ ^ 2) ω
        * Set.indicator (halfBarrier X σ h₂ k j₀ t C₁ a B)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut k) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ)
    (fun h₁ h₂ => integral_nonneg fun ω => mul_nonneg
      (Set.indicator_nonneg (fun _ _ => by positivity) _)
      (Set.indicator_nonneg (fun _ _ => by positivity) _))
    (t - k + 1) (b := fun d => K * Real.exp (2 * (t : ℝ) - 3 * k + ((k + d : ℕ) : ℝ))
      * (1 / ((t : ℝ) - k) ^ 4 + 1 / ((((k + d : ℕ) : ℝ) - k + 1) ^ 2 * ((t : ℝ) - k))))
    (r := fun d => Real.exp (-(((k + d : ℕ) : ℝ)))) hb (fun d => (Real.exp_pos _).le) ?_) ?_
  · -- the shell bound at each pair
    intro h₁ hh₁ h₂ hh₂
    suffices hsuff : ∃ d, d < t - k + 1 ∧ |h₁ - h₂| ≤ Real.exp (-(((k + d : ℕ) : ℝ)))
        ∧ (∫ ω, Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut k) y (shiftLine σ h₁) ω‖ ^ 2) ω
            * Set.indicator (halfBarrier X σ h₂ k j₀ t C₁ a B)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut k) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ)
          ≤ K * Real.exp (2 * (t : ℝ) - 3 * k + ((k + d : ℕ) : ℝ))
            * (1 / ((t : ℝ) - k) ^ 4
              + 1 / ((((k + d : ℕ) : ℝ) - k + 1) ^ 2 * ((t : ℝ) - k))) by
      obtain ⟨d, hd, hdr, hGd⟩ := hsuff
      have hmem : h₂ ∈ Metric.closedBall h₁ (Real.exp (-(((k + d : ℕ) : ℝ)))) := by
        rw [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm]
        exact hdr
      refine le_trans hGd (le_trans (le_of_eq (Set.indicator_of_mem hmem
        (fun _ => K * Real.exp (2 * (t : ℝ) - 3 * k + ((k + d : ℕ) : ℝ))
          * (1 / ((t : ℝ) - k) ^ 4
            + 1 / ((((k + d : ℕ) : ℝ) - k + 1) ^ 2 * ((t : ℝ) - k))))).symm) ?_)
      exact Finset.single_le_sum (f := fun d => Set.indicator
          (Metric.closedBall h₁ (Real.exp (-(((k + d : ℕ) : ℝ)))))
          (fun _ => K * Real.exp (2 * (t : ℝ) - 3 * k + ((k + d : ℕ) : ℝ))
            * (1 / ((t : ℝ) - k) ^ 4
              + 1 / ((((k + d : ℕ) : ℝ) - k + 1) ^ 2 * ((t : ℝ) - k)))) h₂)
        (fun d' _ => Set.indicator_nonneg (fun _ _ => hb d') _) (Finset.mem_range.2 hd)
    by_cases hcore : |h₁ - h₂| ≤ Real.exp (-(t : ℝ))
    · -- the core: split at the top
      refine ⟨t - k, by omega, by rw [show k + (t - k) = t by omega]; exact hcore, ?_⟩
      rw [show k + (t - k) = t by omega]
      refine le_trans (Htop X μ hX k t y σ h₁ h₂ hk20 hkt hσ htop hbot hy hh₁ hh₂) ?_
      have hexp : Real.exp (3 * ((t : ℝ) - k)) = Real.exp (2 * (t : ℝ) - 3 * k + (t : ℝ)) := by
        congr 1; ring
      rw [hexp, div_eq_mul_one_div]
      exact shell_le_left hKcK hKc.le (Real.exp_pos _).le hu (hv (t - k) |>.trans_eq (by
        rw [show k + (t - k) = t by omega]))
    · rw [not_le] at hcore
      obtain ⟨m, hkm, hmt, hδm, hδm1⟩ :=
        exists_shell_index hcore (abs_sub_lt_of_mem_halfWindow hh₁ hh₂)
      refine ⟨m - k, by omega, by rw [show k + (m - k) = m by omega]; exact hδm, ?_⟩
      rw [show k + (m - k) = m by omega]
      have hvm : 0 ≤ 1 / (((m : ℝ) - k + 1) ^ 2 * ((t : ℝ) - k)) := by
        have := hv (m - k)
        rwa [show k + (m - k) = m by omega] at this
      rcases (show m + 1 = t ∨ (m + 2 ≤ t ∧ 2 * k + t < 3 * m) ∨ 3 * m ≤ 2 * k + t by omega)
        with hm1 | ⟨hm2, hm3⟩ | hm3
      · -- the last shell: split at the top
        refine le_trans (Htop X μ hX k t y σ h₁ h₂ hk20 hkt hσ htop hbot hy hh₁ hh₂) ?_
        have hexp : Real.exp (3 * ((t : ℝ) - k))
            = Real.exp 1 * Real.exp (2 * (t : ℝ) - 3 * k + (m : ℝ)) := by
          rw [← Real.exp_add]; congr 1
          have : (t : ℝ) = (m : ℝ) + 1 := by exact_mod_cast hm1.symm
          rw [this]; ring
        rw [hexp, div_eq_mul_one_div, ← mul_assoc]
        exact shell_le_left hKceK (by positivity) (Real.exp_pos _).le hu hvm
      · -- a near shell
        refine le_trans (Hnear X μ hX k t y m σ h₁ h₂ hk20 hσ htop hbot hy hh₁ hh₂ hm3 hm2
          hδm1) ?_
        rw [div_eq_mul_one_div]
        exact shell_le_left hKnK hKn.le (Real.exp_pos _).le hu hvm
      · -- a far shell
        refine le_trans (Hfar X μ hX k t y m σ h₁ h₂ hkf (by omega) hσ htop hbot hy hh₁ hh₂ hkm
          hm3 hδm1) ?_
        rw [div_eq_mul_one_div]
        exact shell_le_right hKfK hKf.le (Real.exp_pos _).le hu hvm
  · -- the arithmetic of the sum
    have hvol : volume.real (halfWindow k) ≤ Real.exp (-(k : ℝ)) := by
      rw [halfWindow, Real.volume_real_Icc]
      have := Real.exp_pos (-((k : ℝ) + 1))
      rw [max_le_iff]
      exact ⟨by linarith, (Real.exp_pos _).le⟩
    have hterm : ∀ d ∈ Finset.range (t - k + 1),
        K * Real.exp (2 * (t : ℝ) - 3 * k + ((k + d : ℕ) : ℝ))
          * (1 / ((t : ℝ) - k) ^ 4 + 1 / ((((k + d : ℕ) : ℝ) - k + 1) ^ 2 * ((t : ℝ) - k)))
          * (2 * Real.exp (-(((k + d : ℕ) : ℝ))))
        = 2 * K * Real.exp (2 * (t : ℝ) - 3 * k)
          * (1 / ((t : ℝ) - k) ^ 4 + 1 / (((d : ℝ) + 1) ^ 2 * ((t : ℝ) - k))) := by
      intro d _
      have hc : (((k + d : ℕ) : ℝ) - k + 1) = (d : ℝ) + 1 := by push_cast; ring
      have he : Real.exp (2 * (t : ℝ) - 3 * k + ((k + d : ℕ) : ℝ))
          * Real.exp (-(((k + d : ℕ) : ℝ))) = Real.exp (2 * (t : ℝ) - 3 * k) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hc]
      calc K * Real.exp (2 * (t : ℝ) - 3 * k + ((k + d : ℕ) : ℝ))
            * (1 / ((t : ℝ) - k) ^ 4 + 1 / (((d : ℝ) + 1) ^ 2 * ((t : ℝ) - k)))
            * (2 * Real.exp (-(((k + d : ℕ) : ℝ))))
          = 2 * K * (Real.exp (2 * (t : ℝ) - 3 * k + ((k + d : ℕ) : ℝ))
            * Real.exp (-(((k + d : ℕ) : ℝ))))
            * (1 / ((t : ℝ) - k) ^ 4 + 1 / (((d : ℝ) + 1) ^ 2 * ((t : ℝ) - k))) := by ring
        _ = _ := by rw [he]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hn : ((t - k + 1 : ℕ) : ℝ) ≤ ((t : ℝ) - k) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; linarith
    have hS := sum_shell_weights_le hTK1 (t - k + 1) hn
    have hS0 : 0 ≤ ∑ d ∈ Finset.range (t - k + 1),
        (1 / ((t : ℝ) - k) ^ 4 + 1 / (((d : ℝ) + 1) ^ 2 * ((t : ℝ) - k))) :=
      Finset.sum_nonneg fun d _ => add_nonneg hu (div_nonneg zero_le_one
        (mul_nonneg (by positivity) hTK.le))
    have hvol0 : 0 ≤ volume.real (halfWindow k) := measureReal_nonneg
    calc volume.real (halfWindow k) * (2 * K * Real.exp (2 * (t : ℝ) - 3 * k)
          * ∑ d ∈ Finset.range (t - k + 1),
            (1 / ((t : ℝ) - k) ^ 4 + 1 / (((d : ℝ) + 1) ^ 2 * ((t : ℝ) - k))))
        ≤ Real.exp (-(k : ℝ)) * (2 * K * Real.exp (2 * (t : ℝ) - 3 * k) * (4 / ((t : ℝ) - k))) :=
          mul_le_mul hvol (mul_le_mul_of_nonneg_left hS (by positivity))
            (mul_nonneg (by positivity) hS0) (Real.exp_pos _).le
      _ = 8 * K * (Real.exp (-(k : ℝ)) * Real.exp (2 * (t : ℝ) - 3 * k)) / ((t : ℝ) - k) := by
          field_simp
          ring
      _ = 8 * K * Real.exp (2 * (t : ℝ) - 4 * k) / ((t : ℝ) - k) := by
          rw [← Real.exp_add]; congr 2; ring_nf

end RMF
