/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Independence
import RMF.Weighted.EulerMomentHalf
import RMF.Analysis.Minkowski

/-!
# The upper bound for fixed `½ < q < 1`: the structural inequality

The upper bound `E|S(x)|^{2q} ≪ (log x)^{q(2q-1)}` for fixed `½ < q < 1` reads the layered
identity in `L^{2q}`: with `2q ≥ 1` Minkowski applies, independence factors each product, and
`‖·‖_{2q} ≤ ‖·‖_2` turns the tails into second moments, which the fluctuation bounds of
`RMF/Weighted/Fluctuations.lean` control:

`‖S(x)‖_{2q} ≤ ‖F_{y_1}(½)‖_{2q} + ∑_{k=1}^{K-1} ‖F_{y_{k+1}}(½)‖_{2q}·‖T_{y_{k+1},y_k}(x)‖_2
              + ‖T_{y_K}(x)‖_2.`

This file proves that inequality for **any** admissible sequence of scales
(`RMF.rpow_inv_integral_rpow_norm_weightedRademacherSum_le`) and leaves the choice
`y_k = x^{e^{-(k-1)}}` and the geometric series to `RMF/Weighted/FixedQTerms.lean`.  It is the
case `Y 1 = ⌊x⌋₊` of `RMF.rpow_inv_integral_rpow_norm_weightedRademacherSum_le_layered`, which
keeps the top scale free and every factor in `L^{2q}`, as the sharp bound above `q = ½`
(`RMF/Weighted/SharpAboveHalf.lean`) needs; that form needs no `q ≤ 1`.

## Preliminaries

Everything in sight is a finite sum or product of variables of modulus at most one, so the `MemLp`
hypotheses of Minkowski are discharged by a crude bound: `RMF.ae_norm_sum_div_sqrt_le` for the
sums, `RMF.IsRademacherRMF.ae_norm_randomEulerProduct_le` for the products, and
`RMF.memLp_ofReal_of_bound` for the passage.

`B_{y_1}(x) = 1` at `y_1 = ⌊x⌋₊`: a `⌊x⌋₊`-rough `r ≤ x` has every prime factor above `⌊x⌋₊ ≥ r`,
so `r = 1`.  This is what makes the first term of the identity the bare Euler product `F_x(½)`.
-/

open Finset MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Crude bounds, for the `MemLp` side conditions -/

/-- **A weighted sum over any index set is bounded by its cardinality.**  Each term has modulus
`‖f(n)‖/√n ≤ 1`; at `n = 0` the term is `0`.  The index-set-free form of
`RMF.ae_norm_weightedRademacherSum_le`, for the truncation tails. -/
lemma ae_norm_sum_div_sqrt_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (s : Finset ℕ) :
    ∀ᵐ ω ∂μ, ‖∑ n ∈ s, f ω n / (Real.sqrt n : ℂ)‖ ≤ (s.card : ℝ) := by
  have hall : ∀ n ∈ s, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 := fun n _ => hf.norm_apply_le_one n
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ s, ‖f ω n / (Real.sqrt n : ℂ)‖ ≤ 1 := by
    intro n hn
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · have hn1R : (1 : ℝ) ≤ Real.sqrt n := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn0)
      exact div_le_one_of_le₀ (le_trans (hω n hn) hn1R) (Real.sqrt_nonneg _)
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 hterm) ?_
  rw [nsmul_eq_mul, mul_one]

/-- **A weighted sum over any index set lies in every `L^r`.** -/
lemma memLp_sum_div_sqrt {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hf : IsRademacherRMF f μ) (s : Finset ℕ) (r : ℝ) :
    MemLp (fun ω => ∑ n ∈ s, f ω n / (Real.sqrt n : ℂ)) (ENNReal.ofReal r) μ :=
  memLp_ofReal_of_bound
    ((Finset.measurable_sum _ fun n _ =>
      (hf.measurable_apply n).div_const _).aestronglyMeasurable)
    (ae_norm_sum_div_sqrt_le hf s)

/-- **A product of a bounded factor with a weighted sum lies in every `L^r`.**  The shape of every
layer of the layered identity. -/
lemma memLp_mul_sum_div_sqrt {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsRademacherRMF f μ) {F : Ω → ℂ} {M : ℝ}
    (hFm : AEMeasurable F μ) (hFb : ∀ᵐ ω ∂μ, ‖F ω‖ ≤ M) (s : Finset ℕ) (r : ℝ) :
    MemLp (fun ω => F ω * ∑ n ∈ s, f ω n / (Real.sqrt n : ℂ)) (ENNReal.ofReal r) μ := by
  refine memLp_ofReal_of_bound (M := M * (s.card : ℝ))
    (hFm.aestronglyMeasurable.mul ((Finset.measurable_sum _ fun n _ =>
      (hf.measurable_apply n).div_const _).aestronglyMeasurable)) ?_
  filter_upwards [hFb, ae_norm_sum_div_sqrt_le hf s] with ω h1 h2
  rw [norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _)
    (le_trans (norm_nonneg _) h1)

/-! ### `‖·‖_{2q} ≤ ‖·‖_2` -/

/-- **The `L^{2q}` norm is below the `L²` norm**, `2q ≤ 2`, on a probability space.  Jensen for
the concave `t ↦ t^q` applied to `t = ‖g‖²`, then the `(2q)`-th root.

Stated with the second moment on the right in the shape the tail bounds produce it — a natural
square inside, a real root outside. -/
theorem rpow_inv_integral_rpow_le_rpow_inv_integral_sq {g : Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {q M : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hmeas : Measurable g)
    (hb : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ M) :
    (∫ ω, ‖g ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹ ≤ (∫ ω, ‖g ω‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹ := by
  have h2q : (0 : ℝ) < 2 * q := by linarith
  have hsq : (0 : ℝ) ≤ ∫ ω, ‖g ω‖ ^ 2 ∂μ := integral_nonneg fun ω => by positivity
  have hpow : ∀ ω : Ω, ‖g ω‖ ^ (2 * q) = (‖g ω‖ ^ 2) ^ q := by
    intro ω
    rw [← Real.rpow_natCast ‖g ω‖ 2, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have hjensen : (∫ ω, ‖g ω‖ ^ (2 * q) ∂μ) ≤ (∫ ω, ‖g ω‖ ^ 2 ∂μ) ^ q := by
    simp_rw [hpow]
    exact integral_rpow_le_rpow_integral_of_bound hq0.le hq1 (by fun_prop)
      (Filter.Eventually.of_forall fun ω => by positivity)
      (by filter_upwards [hb] with ω hω; exact pow_le_pow_left₀ (norm_nonneg _) hω 2)
  have hI : (0 : ℝ) ≤ ∫ ω, ‖g ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  calc (∫ ω, ‖g ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
      ≤ ((∫ ω, ‖g ω‖ ^ 2 ∂μ) ^ q) ^ (2 * q)⁻¹ :=
        Real.rpow_le_rpow hI hjensen (by positivity)
    _ = (∫ ω, ‖g ω‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹ := by
        rw [← Real.rpow_mul hsq]
        congr 1
        field_simp

/-! ### `B_{⌊x⌋₊}(x) = 1` -/

omit [MeasurableSpace Ω] in
/-- **The top layer's rough sum is the empty product.**  Only `r = 1` is `⌊x⌋₊`-rough and `≤ x`,
every larger such `r` needing a prime factor above `⌊x⌋₊ ≥ r`.  This is what turns the first term
of the layered identity into the bare Euler product `F_x(½)`. -/
theorem roughWeightedRademacherSum_floor_eq_one {X : ℕ → Ω → ℂ} {x : ℝ} (hx : 1 ≤ x) (ω : Ω) :
    roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) ⌊x⌋₊ x ω = 1 := by
  have hx1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.2 hx
  have hset : {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough ⌊x⌋₊ n} = {1} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, hro⟩
      by_contra hne
      exact absurd (hro.lt_of_one_lt (lt_of_le_of_ne h1 (Ne.symm hne))) (not_lt.2 h2)
    · rintro rfl
      exact ⟨⟨le_rfl, hx1⟩, isRough_one _⟩
  rw [roughWeightedRademacherSum, hset, Finset.sum_singleton,
    (isMultiplicative_squarefreeExtension _).map_one]
  norm_num

/-! ### The structural inequality

The layered identity read in `L^{2q}`: Minkowski over the `K + 1` terms and independence on each
product, with the top scale free and every factor in `L^{2q}`; then the top scale `⌊x⌋₊` and
`‖·‖_{2q} ≤ ‖·‖_2` on the two tails, which brings in their second moments. -/

/-- **The layered identity read in `L^{2q}`, every tail kept in `L^{2q}`.**  For `q ≥ ½` and
integer scales nonincreasing on `[1, K]`, the top scale `Y 1` free:
`‖S(x)‖_{2q} ≤ ‖F_{Y1}(½)‖_{2q}·‖B_{Y1}(x)‖_{2q}
  + ∑_{k=1}^{K-1} ‖F_{Y(k+1)}(½)‖_{2q}·‖T_{Y(k+1),Yk}(x)‖_{2q} + ‖T_{YK}(x)‖_{2q}`.
Minkowski, then independence (at the top by
`RMF.integral_rpow_norm_randomEulerProduct_mul_roughWeightedRademacherSum`); no `q ≤ 1`. -/
theorem rpow_inv_integral_rpow_norm_weightedRademacherSum_le_layered {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {q : ℝ} (hq0 : 1 / 2 ≤ q)
    {Y : ℕ → ℕ} {K : ℕ} (hK : 1 ≤ K) (hY : ∀ k, 1 ≤ k → k < K → Y (k + 1) ≤ Y k)
    (x : ℝ) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
        ^ (2 * q)⁻¹
      ≤ (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
              (Y 1 + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
          * (∫ ω, ‖roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω)
              (Y 1) x ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
        + (∑ k ∈ Finset.Ico 1 K,
            (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
                (Y (k + 1) + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
              * (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
                  (Y (k + 1)) (Y k) x ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹)
        + (∫ ω, ‖truncationTail (fun ω => squarefreeExtension fun p => X p ω)
              (Y K) x ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹ := by
  classical
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hq2 : (1 : ℝ) ≤ 2 * q := by linarith
  -- the `K + 1` summands of the layered identity
  obtain ⟨G, hG0, hGmid, hGK⟩ :
      ∃ G : ℕ → Ω → ℂ,
        G 0 = (fun ω => randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
                (Y 1 + 1) (1 / 2) ω
              * roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω)
                (Y 1) x ω)
        ∧ (∀ k, 1 ≤ k → k < K → G k
            = fun ω => -(randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
                (Y (k + 1) + 1) (1 / 2) ω
              * blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
                (Y (k + 1)) (Y k) x ω))
        ∧ G K = fun ω => -(truncationTail (fun ω => squarefreeExtension fun p => X p ω)
              (Y K) x ω) := by
    refine ⟨fun k => if k = 0 then
        (fun ω => randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
            (Y 1 + 1) (1 / 2) ω
          * roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) (Y 1) x ω)
      else if k = K then
        (fun ω => -(truncationTail (fun ω => squarefreeExtension fun p => X p ω) (Y K) x ω))
      else
        (fun ω => -(randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
            (Y (k + 1) + 1) (1 / 2) ω
          * blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
            (Y (k + 1)) (Y k) x ω)), by simp, fun k h1 h2 => ?_, ?_⟩
    · dsimp only
      rw [if_neg (by omega), if_neg (by omega)]
    · dsimp only
      rw [if_neg (by omega), if_pos rfl]
  -- the three groups of indices
  have hsplitC : ∀ g : ℕ → ℂ, ∑ k ∈ Finset.range (K + 1), g k
      = g 0 + (∑ k ∈ Finset.Ico 1 K, g k) + g K := fun g => by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < K + 1),
      Finset.sum_Ico_succ_top hK, ← add_assoc]
  have hsplitR : ∀ g : ℕ → ℝ, ∑ k ∈ Finset.range (K + 1), g k
      = g 0 + (∑ k ∈ Finset.Ico 1 K, g k) + g K := fun g => by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < K + 1),
      Finset.sum_Ico_succ_top hK, ← add_assoc]
  -- the identity
  have hmidsum : ∀ ω, ∑ k ∈ Finset.Ico 1 K, G k ω
      = ∑ k ∈ Finset.Ico 1 K, -(randomEulerProduct
          (fun ω => squarefreeExtension fun p => X p ω) (Y (k + 1) + 1) (1 / 2) ω
        * blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
          (Y (k + 1)) (Y k) x ω) := fun ω =>
    Finset.sum_congr rfl fun k hk => by
      rw [hGmid k (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2]
  have hid : ∀ ω, ∑ k ∈ Finset.range (K + 1), G k ω = weightedRademacherSum
      (fun ω => squarefreeExtension fun p => X p ω) x ω := by
    intro ω
    rw [hsplitC fun k => G k ω, hmidsum ω]
    simp only [hG0, hGK]
    rw [weightedRademacherSum_eq_layered Y x ω hK hY, Finset.sum_neg_distrib]
    ring
  -- integrability
  have hmem : ∀ k ∈ Finset.range (K + 1), MemLp (G k) (ENNReal.ofReal (2 * q)) μ := by
    intro k hk
    have hkK : k ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [hG0]
      exact memLp_mul_sum_div_sqrt hRa (hRa.aemeasurable_randomEulerProduct _ _)
        (hRa.ae_norm_randomEulerProduct_le _ _) _ _
    · rcases eq_or_ne k K with rfl | hkne
      · rw [hGK]
        exact (memLp_sum_div_sqrt hRa _ _).neg
      · rw [hGmid k (by omega) (by omega)]
        exact (memLp_mul_sum_div_sqrt hRa (hRa.aemeasurable_randomEulerProduct _ _)
          (hRa.ae_norm_randomEulerProduct_le _ _) _ _).neg
  have hmink := rpow_inv_integral_rpow_norm_sum_le (μ := μ) (s := Finset.range (K + 1))
    (g := G) hq2 hmem
  simp_rw [hid] at hmink
  rw [hsplitR fun k => (∫ ω, ‖G k ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹] at hmink
  refine le_trans hmink
    (add_le_add (add_le_add (le_of_eq ?_) (le_of_eq (Finset.sum_congr rfl fun k hk => ?_)))
      (le_of_eq ?_))
  · -- the top layer: independence, `B_{Y 1}(x)` being a genuine factor
    have hnorm : (∫ ω, ‖G 0 ω‖ ^ (2 * q) ∂μ)
        = (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
              (Y 1 + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ)
          * ∫ ω, ‖roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω)
              (Y 1) x ω‖ ^ (2 * q) ∂μ := by
      rw [hG0]
      exact integral_rpow_norm_randomEulerProduct_mul_roughWeightedRademacherSum hX _ _ _ _
    rw [hnorm, Real.mul_rpow (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _)
      (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _)]
  · -- a layer: independence
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.1 hk
    have hnorm : (∫ ω, ‖G k ω‖ ^ (2 * q) ∂μ)
        = (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
              (Y (k + 1) + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ)
          * ∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
              (Y (k + 1)) (Y k) x ω‖ ^ (2 * q) ∂μ := by
      rw [hGmid k hk1 hk2]
      simp only [norm_neg]
      exact integral_rpow_norm_randomEulerProduct_mul_blockTruncationTail hX _ _ _ _ _
    rw [hnorm, Real.mul_rpow (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _)
      (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _)]
  · -- the bottom tail
    rw [hGK]
    simp only [norm_neg]

/-- **The structural inequality**, for nonincreasing integer scales with `Y 1 = ⌊x⌋₊`:
`‖S(x)‖_{2q} ≤ ‖F_{Y1}(½)‖_{2q}
  + ∑_{k=1}^{K-1} ‖F_{Y(k+1)}(½)‖_{2q}·‖T_{Y(k+1),Yk}(x)‖_2 + ‖T_{YK}(x)‖_2`.
The case `Y 1 = ⌊x⌋₊` of `RMF.rpow_inv_integral_rpow_norm_weightedRademacherSum_le_layered`, where
`B_{Y1}(x) = 1`, with `‖·‖_{2q} ≤ ‖·‖_2` on the two tails; that last step is the only use of
`q ≤ 1`. -/
theorem rpow_inv_integral_rpow_norm_weightedRademacherSum_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1)
    {Y : ℕ → ℕ} {K : ℕ} (hK : 1 ≤ K) (hY : ∀ k, 1 ≤ k → k < K → Y (k + 1) ≤ Y k)
    {x : ℝ} (hx : 1 ≤ x) (hY1 : Y 1 = ⌊x⌋₊) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
        ^ (2 * q)⁻¹
      ≤ (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
              (Y 1 + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
        + (∑ k ∈ Finset.Ico 1 K,
            (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
                (Y (k + 1) + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
              * (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
                  (Y (k + 1)) (Y k) x ω‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹)
        + (∫ ω, ‖truncationTail (fun ω => squarefreeExtension fun p => X p ω)
              (Y K) x ω‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹ := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hqpos : (0 : ℝ) < q := by linarith
  refine le_trans (rpow_inv_integral_rpow_norm_weightedRademacherSum_le_layered hX hq0 hK hY x)
    (add_le_add (add_le_add (le_of_eq ?_) (Finset.sum_le_sum fun k _ => ?_)) ?_)
  · -- `B_{Y 1}(x) = 1` at the top scale `⌊x⌋₊`, so its factor is `1`
    have hpt : ∀ ω, ‖roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω)
        (Y 1) x ω‖ ^ (2 * q) = 1 := fun ω => by
      rw [hY1, roughWeightedRademacherSum_floor_eq_one hx ω, norm_one, Real.one_rpow]
    simp only [hpt, integral_const, probReal_univ, one_smul, Real.one_rpow, mul_one]
  · -- a layer: `‖T‖_{2q} ≤ ‖T‖_2`
    refine mul_le_mul_of_nonneg_left ?_
      (Real.rpow_nonneg (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) _)
    exact rpow_inv_integral_rpow_le_rpow_inv_integral_sq hqpos hq1
      (Finset.measurable_sum _ fun n _ => (hRa.measurable_apply n).div_const _)
      (ae_norm_sum_div_sqrt_le hRa _)
  · -- the bottom tail: `‖T‖_{2q} ≤ ‖T‖_2`
    exact rpow_inv_integral_rpow_le_rpow_inv_integral_sq hqpos hq1
      (Finset.measurable_sum _ fun n _ => (hRa.measurable_apply n).div_const _)
      (ae_norm_sum_div_sqrt_le hRa _)

end RMF
