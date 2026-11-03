/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Harper
import RMF.Weighted.ExtendedLowerFixedQ
import RMF.Weighted.ExtendedBounds
import RMF.Weighted.FixedQAboveHalf
import RMF.Weighted.LowerFixedQ
import RMF.Weighted.HalfInterface

/-!
# The two main theorems of the paper

The paper, §1.1 "Main results": for fixed
`0 ≤ q ≤ 1`, uniformly for `x ≥ 3`,

* Theorem 1.1: `E|x^{-1/2}∑_{n≤x} X^e(n)|^{2q} ≍ M_q(x)` (`RMF.extended_rademacher_moments`);
* Theorem 1.2: `E|∑_{n≤x} X(n)/√n|^{2q} ≍ M_q(x)` (`RMF.weighted_rademacher_moments`),

with `M_q(x) = (log log x)^{-q/2}` for `0 ≤ q < ½`, `(log log x)^{3/4}` at `q = ½` and
`(log x)^{q(2q-1)}` for `½ < q ≤ 1` (`RMF.momentOrder`).  `X` is the Rademacher function on the
squarefrees and `X^e` its completely multiplicative extension.  The constants depend on `q` only:
each theorem is proved on the coordinate model and carried to every probability space by the
moment transfers (`RMF/Reduction/CoordinateModel.lean`, `RMF/Weighted/CoordinateMoments.lean`).

Every range is an existing theorem for `x ≥ x₀`.  On the bounded range `3 ≤ x ≤ x₀` both sums are
bounded and their second moments are bounded below, so the moments and the rates lie between two
constants; `RMF.two_sided_of_ge_of_bounded` joins the ranges.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The order of magnitude -/

/-- **The order of magnitude in Theorems 1.1 and 1.2 of the paper**: `(log log x)^{-q/2}` for
`q < ½`, `(log log x)^{3/4}` at `q = ½`, and `(log x)^{q(2q-1)}` for `q > ½`. -/
noncomputable def momentOrder (q x : ℝ) : ℝ :=
  if q < 1 / 2 then Real.log (Real.log x) ^ (-(q / 2))
  else if q = 1 / 2 then Real.log (Real.log x) ^ (3 / 4 : ℝ)
  else Real.log x ^ (q * (2 * q - 1))

lemma momentOrder_of_lt {q : ℝ} (hq : q < 1 / 2) (x : ℝ) :
    momentOrder q x = Real.log (Real.log x) ^ (-(q / 2)) := by
  rw [momentOrder, if_pos hq]

lemma momentOrder_half (x : ℝ) :
    momentOrder (1 / 2) x = Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
  rw [momentOrder, if_neg (lt_irrefl _), if_pos rfl]

lemma momentOrder_of_gt {q : ℝ} (hq : 1 / 2 < q) (x : ℝ) :
    momentOrder q x = Real.log x ^ (q * (2 * q - 1)) := by
  rw [momentOrder, if_neg (not_lt.2 hq.le), if_neg hq.ne']

lemma momentOrder_nonneg (q : ℝ) {x : ℝ} (hx : 3 ≤ x) : 0 ≤ momentOrder q x := by
  have hL := four_div_nine_hundred_sixty_one_le_log_log hx
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  unfold momentOrder
  split_ifs
  · exact Real.rpow_nonneg (by linarith) _
  · exact Real.rpow_nonneg (by linarith) _
  · exact Real.rpow_nonneg hlx _

/-- **The rate below `½` on a bounded range**: for `3 ≤ x ≤ X₀`,
`(max 1 (log log X₀))⁻¹ ≤ (log log x)^{-q/2} ≤ 961/4`, from `4/961 ≤ log log x ≤ log log X₀`. -/
lemma momentOrder_bounds_of_lt {q X₀ : ℝ} (hq0 : 0 ≤ q) (hq : q < 1 / 2) {x : ℝ} (hx : 3 ≤ x)
    (hxX : x ≤ X₀) :
    (max 1 (Real.log (Real.log X₀)))⁻¹ ≤ momentOrder q x ∧ momentOrder q x ≤ 961 / 4 := by
  have hL := four_div_nine_hundred_sixty_one_le_log_log hx
  have hL0 : 0 < Real.log (Real.log x) := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hM1 : (1 : ℝ) ≤ max 1 (Real.log (Real.log X₀)) := le_max_left _ _
  have hLM : Real.log (Real.log x) ≤ max 1 (Real.log (Real.log X₀)) :=
    le_trans (Real.log_le_log hlog (Real.log_le_log (by linarith) hxX)) (le_max_right _ _)
  have he : -(q / 2) ≤ 0 := by linarith
  rw [momentOrder_of_lt hq]
  constructor
  · calc (max 1 (Real.log (Real.log X₀)))⁻¹ = max 1 (Real.log (Real.log X₀)) ^ (-1 : ℝ) :=
          (Real.rpow_neg_one _).symm
      _ ≤ max 1 (Real.log (Real.log X₀)) ^ (-(q / 2)) :=
          Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
      _ ≤ Real.log (Real.log x) ^ (-(q / 2)) := Real.rpow_le_rpow_of_nonpos hL0 hLM he
  · calc Real.log (Real.log x) ^ (-(q / 2)) ≤ (4 / 961 : ℝ) ^ (-(q / 2)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hL he
      _ ≤ (4 / 961 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = 961 / 4 := by rw [Real.rpow_neg_one]; norm_num

/-- **The rate at `½` on a bounded range**: for `3 ≤ x ≤ X₀`,
`4/961 ≤ (log log x)^{3/4} ≤ max 1 (log log X₀)`. -/
lemma momentOrder_bounds_half {X₀ x : ℝ} (hx : 3 ≤ x) (hxX : x ≤ X₀) :
    4 / 961 ≤ momentOrder (1 / 2) x
      ∧ momentOrder (1 / 2) x ≤ max 1 (Real.log (Real.log X₀)) := by
  have hL := four_div_nine_hundred_sixty_one_le_log_log hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hM1 : (1 : ℝ) ≤ max 1 (Real.log (Real.log X₀)) := le_max_left _ _
  have hLM : Real.log (Real.log x) ≤ max 1 (Real.log (Real.log X₀)) :=
    le_trans (Real.log_le_log hlog (Real.log_le_log (by linarith) hxX)) (le_max_right _ _)
  rw [momentOrder_half]
  constructor
  · calc (4 / 961 : ℝ) = (4 / 961 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (4 / 961 : ℝ) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      _ ≤ Real.log (Real.log x) ^ (3 / 4 : ℝ) := Real.rpow_le_rpow (by norm_num) hL (by norm_num)
  · calc Real.log (Real.log x) ^ (3 / 4 : ℝ)
        ≤ max 1 (Real.log (Real.log X₀)) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow (by linarith) hLM (by norm_num)
      _ ≤ max 1 (Real.log (Real.log X₀)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num)
      _ = max 1 (Real.log (Real.log X₀)) := Real.rpow_one _

/-- **The rate above `½` on a bounded range**: for `3 ≤ x ≤ X₀` and `½ < q ≤ 1`,
`1 ≤ (log x)^{q(2q-1)} ≤ max 1 (log X₀)`, the exponent lying in `(0, 1]`. -/
lemma momentOrder_bounds_of_gt {q X₀ : ℝ} (hq : 1 / 2 < q) (hq1 : q ≤ 1) {x : ℝ} (hx : 3 ≤ x)
    (hxX : x ≤ X₀) :
    1 ≤ momentOrder q x ∧ momentOrder q x ≤ max 1 (Real.log X₀) := by
  have he0 : 0 ≤ q * (2 * q - 1) := mul_nonneg (by linarith) (by linarith)
  have he1 : q * (2 * q - 1) ≤ 1 := by nlinarith
  have hlx1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hlogX : Real.log x ≤ max 1 (Real.log X₀) :=
    le_trans (Real.log_le_log (by linarith) hxX) (le_max_right _ _)
  rw [momentOrder_of_gt hq]
  exact ⟨Real.one_le_rpow hlx1 he0, le_trans (Real.rpow_le_rpow (by linarith) hlogX he0)
    (le_trans (Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) he1)
      (le_of_eq (Real.rpow_one _)))⟩

/-! ### The moments on a bounded range -/

/-- **The weighted sum's moments on a bounded range.**  For `1 ≤ x ≤ X₀` and `0 ≤ q ≤ 1`,
`(max 1 X₀)^{-2} ≤ E|S(x)|^{2q} ≤ (max 1 X₀)^2`: `‖S(x)‖ ≤ ⌊x⌋ ≤ max 1 X₀`
(`RMF.ae_norm_weightedRademacherSum_le`), and `E|S(x)|² ≥ 1` from its term `n = 1`
(`RMF.integral_normSq_weightedRademacherSum`, `RMF.le_integral_rpow_of_second_moment`). -/
lemma integral_rpow_weightedRademacherSum_mem_of_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x X₀ q : ℝ} (hx : 1 ≤ x) (hxX : x ≤ X₀) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    (max 1 X₀ ^ 2)⁻¹
        ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ
      ∧ (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ) ≤ max 1 X₀ ^ 2 := by
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hM : (1 : ℝ) ≤ max 1 X₀ := le_max_left _ _
  have hr0 : (0 : ℝ) ≤ 2 * q := by linarith
  have hbdd : ∀ᵐ ω ∂μ,
      ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ≤ max 1 X₀ := by
    filter_upwards [ae_norm_weightedRademacherSum_le hf x] with ω hω
    exact le_trans hω (le_trans (Nat.floor_le (by linarith)) (le_trans hxX (le_max_right _ _)))
  have hint := integrable_rpow_norm_weightedRademacherSum hX x hr0
  have hsecond : (1 : ℝ) ≤ ∫ ω,
      ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 : ℝ) ∂μ := by
    simp_rw [rpow_two_eq_sq]
    rw [integral_normSq_weightedRademacherSum hf x]
    have h1 : 1 ∈ ({n ∈ Finset.Icc 1 ⌊x⌋₊ | Squarefree n} : Finset ℕ) :=
      Finset.mem_filter.2
        ⟨Finset.mem_Icc.2 ⟨le_rfl, Nat.le_floor (by exact_mod_cast hx)⟩, squarefree_one⟩
    calc (1 : ℝ) = ((1 : ℕ) : ℝ)⁻¹ := by norm_num
      _ ≤ ∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | Squarefree n}, (n : ℝ)⁻¹ :=
          Finset.single_le_sum (f := fun n : ℕ => (n : ℝ)⁻¹)
            (fun n _ => inv_nonneg.2 (Nat.cast_nonneg _)) h1
  refine ⟨?_, ?_⟩
  · have h := le_integral_rpow_of_second_moment hq0 hq1 hM hbdd hsecond hint
    rwa [one_div] at h
  · calc (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ)
        ≤ ∫ _ω, max 1 X₀ ^ (2 * q) ∂μ :=
          integral_mono_ae hint (integrable_const _) (by
            filter_upwards [hbdd] with ω hω
            exact Real.rpow_le_rpow (norm_nonneg _) hω hr0)
      _ = max 1 X₀ ^ (2 * q) := by simp
      _ ≤ max 1 X₀ ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM (by linarith)
      _ = max 1 X₀ ^ 2 := rpow_two_eq_sq _

/-- **The extended sum's moments on a bounded range.**  For `1 ≤ x ≤ X₀` and `0 ≤ q ≤ 1`,
`(max 1 X₀)^{-3} ≤ E|x^{-1/2}∑_{n≤x} X^e(n)|^{2q} ≤ (max 1 X₀)^2`.  The sum is at most
`⌊x⌋/√x ≤ max 1 X₀` in norm, and its second moment is at least `1/x`: by the square classes
(`RMF.sum_compMultExtension_eq_sum_squarefreeExtension_mul`) and orthogonality it is
`x⁻¹∑_{m≤x, squarefree}⌊√(x/m)⌋²`, whose term `m = 1` is at least one. -/
lemma integral_rpow_normalisedSum_compMultExtension_mem_of_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x X₀ q : ℝ} (hx : 1 ≤ x) (hxX : x ≤ X₀) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    (max 1 X₀ ^ 3)⁻¹
        ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ
      ∧ (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
        ≤ max 1 X₀ ^ 2 := by
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hx0 : 0 < x := by linarith
  have hM : (1 : ℝ) ≤ max 1 X₀ := le_max_left _ _
  have hxM : x ≤ max 1 X₀ := le_trans hxX (le_max_right _ _)
  have hr0 : (0 : ℝ) ≤ 2 * q := by linarith
  -- the pointwise bound
  have hbdd : ∀ᵐ ω ∂μ, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
      ≤ max 1 X₀ := by
    filter_upwards [norm_randomSum_le_of_ae (f := fun ω => compMultExtension fun p => X p ω)
      (μ := μ) (fun n => hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n) x]
      with ω hω
    have hs1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx
    rw [normalisedSum, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc ‖randomSum (fun ω => compMultExtension fun p => X p ω) x ω‖ / Real.sqrt x
        ≤ ‖randomSum (fun ω => compMultExtension fun p => X p ω) x ω‖ :=
          div_le_self (norm_nonneg _) hs1
      _ ≤ (⌊x⌋₊ : ℝ) := hω
      _ ≤ max 1 X₀ := le_trans (Nat.floor_le hx0.le) hxM
  have hmE : Measurable (normalisedSum (fun ω => compMultExtension fun p => X p ω) x) :=
    (Finset.measurable_sum _ fun n _ => hX.measurable_compMultExtension n).div_const _
  have hint : Integrable (fun ω =>
      ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q)) μ := by
    refine (memLp_top_of_bound
      ((Real.continuous_rpow_const hr0).measurable.comp hmE.norm).aestronglyMeasurable
      (max 1 X₀ ^ (2 * q)) ?_).integrable le_top
    filter_upwards [hbdd] with ω hω
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) hω hr0
  -- the second moment, by the square classes and orthogonality
  have hne : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, n ≠ 0 := fun n hn =>
    Nat.one_le_iff_ne_zero.1 (Finset.mem_Icc.1 hn).1
  have hae : ∀ᵐ ω ∂μ, randomSum (fun ω => compMultExtension fun p => X p ω) x ω
      = ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
          ((⌊Real.sqrt (x / m)⌋₊ : ℕ) : ℂ) * squarefreeExtension (fun p => X p ω) m := by
    have hmeas : Measurable fun z : ℂ => z ^ 2 = 1 :=
      measurableSet_setOf.1 ((measurable_id.pow_const 2) (measurableSet_singleton 1))
    have hprimes : ∀ p ∈ Finset.Icc 1 ⌊x⌋₊, ∀ᵐ ω ∂μ, p.Prime → X p ω ^ 2 = 1 := by
      intro p _
      by_cases hp : p.Prime
      · filter_upwards [((hX.hasLaw p hp).ae_iff hmeas).2 sq_eq_one_rademacherLaw] with ω hω
        exact fun _ => hω
      · exact Filter.Eventually.of_forall fun ω h => absurd h hp
    filter_upwards [(Filter.eventually_all_finset _).2 hprimes] with ω hω
    have hv : ∀ p, p.Prime → p ≤ ⌊x⌋₊ → X p ω ^ 2 = 1 := fun p hp hpx =>
      hω p (Finset.mem_Icc.2 ⟨hp.one_lt.le, hpx⟩) hp
    rw [randomSum, sum_compMultExtension_eq_sum_squarefreeExtension_mul hx0.le hv]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have key := integral_normSq_weightedSum_of_orthogonality'
    (f := fun ω => squarefreeExtension fun p => X p ω) (μ := μ) (s := Finset.Icc 1 ⌊x⌋₊)
    (c := fun m : ℕ => ((⌊Real.sqrt (x / m)⌋₊ : ℕ) : ℂ))
    (d := fun m => if Squarefree m then 1 else 0)
    (fun m _ n _ => hf.integrable_mul_conj m n)
    (fun m hm n hn => by
      rw [hf.orthogonality (hne m hm) (hne n hn)]
      by_cases h : m = n
      · subst h; simp
      · simp [h])
  have hsq : (∫ ω, ‖randomSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ 2 ∂μ)
      = ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
          (⌊Real.sqrt (x / m)⌋₊ : ℝ) ^ 2 * (if Squarefree m then 1 else 0) := by
    have hae' : (fun ω => ‖randomSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ 2)
        =ᵐ[μ] fun ω => ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
          ((⌊Real.sqrt (x / m)⌋₊ : ℕ) : ℂ) * squarefreeExtension (fun p => X p ω) m‖ ^ 2 := by
      filter_upwards [hae] with ω hω
      rw [hω]
    rw [integral_congr_ae hae', ← Complex.ofReal_inj, key, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  have hsum1 : (1 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
      (⌊Real.sqrt (x / m)⌋₊ : ℝ) ^ 2 * (if Squarefree m then 1 else 0) := by
    have hmem : 1 ∈ Finset.Icc 1 ⌊x⌋₊ :=
      Finset.mem_Icc.2 ⟨le_rfl, Nat.le_floor (by exact_mod_cast hx)⟩
    have h1 : 1 ≤ ⌊Real.sqrt x⌋₊ := Nat.le_floor (by exact_mod_cast Real.one_le_sqrt.2 hx)
    have h1' : (1 : ℝ) ≤ (⌊Real.sqrt x⌋₊ : ℝ) := by exact_mod_cast h1
    have hterm : (1 : ℝ) ≤ (⌊Real.sqrt (x / ((1 : ℕ) : ℝ))⌋₊ : ℝ) ^ 2
        * (if Squarefree 1 then 1 else 0) := by
      rw [if_pos squarefree_one, mul_one, Nat.cast_one, div_one]
      exact one_le_pow₀ h1'
    refine le_trans hterm (Finset.single_le_sum (f := fun m : ℕ =>
      (⌊Real.sqrt (x / m)⌋₊ : ℝ) ^ 2 * (if Squarefree m then 1 else 0)) (fun m _ => ?_) hmem)
    exact mul_nonneg (sq_nonneg _) (by split_ifs <;> norm_num)
  have hsecond : (max 1 X₀)⁻¹
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 : ℝ) ∂μ := by
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hpt : ∀ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 : ℝ)
        = ‖randomSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ 2 / x := by
      intro ω
      rw [rpow_two_eq_sq, normalisedSum, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hsx.le, div_pow, Real.sq_sqrt hx0.le]
    simp_rw [hpt]
    rw [integral_div, hsq]
    calc (max 1 X₀)⁻¹ ≤ x⁻¹ := inv_anti₀ hx0 hxM
      _ = 1 / x := (one_div x).symm
      _ ≤ (∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
            (⌊Real.sqrt (x / m)⌋₊ : ℝ) ^ 2 * (if Squarefree m then 1 else 0)) / x :=
          div_le_div_of_nonneg_right hsum1 hx0.le
  refine ⟨?_, ?_⟩
  · have h := le_integral_rpow_of_second_moment hq0 hq1 hM hbdd hsecond hint
    calc (max 1 X₀ ^ 3)⁻¹ = (max 1 X₀)⁻¹ / max 1 X₀ ^ 2 := by ring
      _ ≤ _ := h
  · calc (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
        ≤ ∫ _ω, max 1 X₀ ^ (2 * q) ∂μ :=
          integral_mono_ae hint (integrable_const _) (by
            filter_upwards [hbdd] with ω hω
            exact Real.rpow_le_rpow (norm_nonneg _) hω hr0)
      _ = max 1 X₀ ^ (2 * q) := by simp
      _ ≤ max 1 X₀ ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM (by linarith)
      _ = max 1 X₀ ^ 2 := rpow_two_eq_sq _

/-! ### From `x ≥ x₀` to `x ≥ 3` -/

/-- **From `x ≥ x₀` to `x ≥ 3`.**  A two-sided bound `c·r(x) ≤ I(x) ≤ C·r(x)` for `x ≥ x₀` extends
to `x ≥ 3` when `a ≤ I(x) ≤ b` and `ρ₁ ≤ r(x) ≤ ρ₂` on `3 ≤ x ≤ x₀`, with the constants
`min c (a/ρ₂)` and `max C (b/ρ₁)`. -/
lemma two_sided_of_ge_of_bounded {I r : ℝ → ℝ} {c C x₀ a b ρ₁ ρ₂ : ℝ} (ha : 0 < a)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hr0 : ∀ x, 3 ≤ x → 0 ≤ r x)
    (hbig : ∀ x, x₀ ≤ x → c * r x ≤ I x ∧ I x ≤ C * r x)
    (hI : ∀ x, 3 ≤ x → x ≤ x₀ → a ≤ I x ∧ I x ≤ b)
    (hr : ∀ x, 3 ≤ x → x ≤ x₀ → ρ₁ ≤ r x ∧ r x ≤ ρ₂) :
    ∀ x, 3 ≤ x → min c (a / ρ₂) * r x ≤ I x ∧ I x ≤ max C (b / ρ₁) * r x := by
  intro x hx
  rcases le_total x₀ x with h | h
  · obtain ⟨h1, h2⟩ := hbig x h
    exact ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (hr0 x hx)) h1,
      le_trans h2 (mul_le_mul_of_nonneg_right (le_max_left _ _) (hr0 x hx))⟩
  · obtain ⟨hIa, hIb⟩ := hI x hx h
    obtain ⟨hr1, hr2⟩ := hr x hx h
    have hb : 0 ≤ b := by linarith
    refine ⟨?_, ?_⟩
    · calc min c (a / ρ₂) * r x ≤ a / ρ₂ * r x :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (hr0 x hx)
        _ ≤ a / ρ₂ * ρ₂ := mul_le_mul_of_nonneg_left hr2 (div_pos ha hρ₂).le
        _ = a := div_mul_cancel₀ a hρ₂.ne'
        _ ≤ I x := hIa
    · calc I x ≤ b := hIb
        _ = b / ρ₁ * ρ₁ := (div_mul_cancel₀ b hρ₁.ne').symm
        _ ≤ b / ρ₁ * r x := mul_le_mul_of_nonneg_left hr1 (div_nonneg hb hρ₁.le)
        _ ≤ max C (b / ρ₁) * r x := mul_le_mul_of_nonneg_right (le_max_right _ _) (hr0 x hx)

/-- **Theorem 1.2 from `x ≥ x₀`**: a two-sided bound by `RMF.momentOrder` for `x ≥ x₀`, uniform
in the Rademacher law, holds for `x ≥ 3` once the rate is bounded on `3 ≤ x ≤ max x₀ 3`
(`RMF.two_sided_of_ge_of_bounded`, `RMF.integral_rpow_weightedRademacherSum_mem_of_le`). -/
lemma weighted_two_sided_ge_three {q c C x₀ ρ₁ ρ₂ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hc : 0 < c) (hC : 0 < C) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hr : ∀ x : ℝ, 3 ≤ x → x ≤ max x₀ 3 → ρ₁ ≤ momentOrder q x ∧ momentOrder q x ≤ ρ₂)
    (H : ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ → ∀ x : ℝ, x₀ ≤ x →
      c * momentOrder q x
          ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ
        ∧ (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ) ≤ C * momentOrder q x) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        c * momentOrder q x
            ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ
          ∧ (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ) ≤ C * momentOrder q x := by
  have ha : 0 < (max 1 (max x₀ 3) ^ 2)⁻¹ :=
    inv_pos.2 (pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) 2)
  refine ⟨min c ((max 1 (max x₀ 3) ^ 2)⁻¹ / ρ₂), max C (max 1 (max x₀ 3) ^ 2 / ρ₁),
    lt_min hc (div_pos ha hρ₂), lt_of_lt_of_le hC (le_max_left _ _), fun X μ hX => ?_⟩
  exact two_sided_of_ge_of_bounded
    (I := fun x => ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ)
    (r := fun x => momentOrder q x) (x₀ := max x₀ 3) ha hρ₁ hρ₂
    (fun x hx => momentOrder_nonneg q hx)
    (fun x hx => H X μ hX x (le_trans (le_max_left _ _) hx))
    (fun x hx hxX => integral_rpow_weightedRademacherSum_mem_of_le hX (by linarith) hxX hq0 hq1)
    hr

/-- **Theorem 1.1 from `x ≥ x₀`**: as `RMF.weighted_two_sided_ge_three`, for the extended sum
(`RMF.integral_rpow_normalisedSum_compMultExtension_mem_of_le`). -/
lemma extended_two_sided_ge_three {q c C x₀ ρ₁ ρ₂ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hc : 0 < c) (hC : 0 < C) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hr : ∀ x : ℝ, 3 ≤ x → x ≤ max x₀ 3 → ρ₁ ≤ momentOrder q x ∧ momentOrder q x ≤ ρ₂)
    (H : ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ → ∀ x : ℝ, x₀ ≤ x →
      c * momentOrder q x
          ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ
        ∧ (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
          ≤ C * momentOrder q x) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        c * momentOrder q x
            ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ
          ∧ (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
            ≤ C * momentOrder q x := by
  have ha : 0 < (max 1 (max x₀ 3) ^ 3)⁻¹ :=
    inv_pos.2 (pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) 3)
  refine ⟨min c ((max 1 (max x₀ 3) ^ 3)⁻¹ / ρ₂), max C (max 1 (max x₀ 3) ^ 2 / ρ₁),
    lt_min hc (div_pos ha hρ₂), lt_of_lt_of_le hC (le_max_left _ _), fun X μ hX => ?_⟩
  exact two_sided_of_ge_of_bounded
    (I := fun x => ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ)
    (r := fun x => momentOrder q x) (x₀ := max x₀ 3) ha hρ₁ hρ₂
    (fun x hx => momentOrder_nonneg q hx)
    (fun x hx => H X μ hX x (le_trans (le_max_left _ _) hx))
    (fun x hx hxX =>
      integral_rpow_normalisedSum_compMultExtension_mem_of_le hX (by linarith) hxX hq0 hq1)
    hr

/-! ### The two theorems -/

/-- **Theorem 1.2 of the paper.**  Let `0 ≤ q ≤ 1` be fixed.  Uniformly for `x ≥ 3`,

`E|∑_{n≤x} X(n)/√n|^{2q} ≍ (log log x)^{-q/2}` if `0 ≤ q < ½`, `(log log x)^{3/4}` if `q = ½`,
and `(log x)^{q(2q-1)}` if `½ < q ≤ 1`

(`RMF.momentOrder`), for the Rademacher function `X` on the squarefrees, with `c`, `C` depending
on `q` only, not on the probability space.  The three
ranges are `RMF.exists_integral_rpow_weightedRademacherSum_asymp_smallQ`,
`RMF.exists_integral_weightedRademacherSum_asymp_half` and
`RMF.exists_integral_rpow_weightedRademacherSum_asymp_largeQ` for `x ≥ x₀`;
`RMF.weighted_two_sided_ge_three` brings each down to `x ≥ 3`. -/
theorem weighted_rademacher_moments (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        c * momentOrder q x
            ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ
          ∧ (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ) ≤ C * momentOrder q x := by
  obtain ⟨c, C, hc, hC, H⟩ : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X : ℕ → (Nat.Primes → ℂ) → ℂ) (μ : Measure (Nat.Primes → ℂ)),
        IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        c * momentOrder q x
            ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ
          ∧ (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ) ≤ C * momentOrder q x := by
    rcases eq_or_lt_of_le hq0 with h0 | hq0'
    · subst h0
      refine ⟨1, 1, one_pos, one_pos, fun X μ hX x _ => ?_⟩
      haveI := hX.isProbabilityMeasure
      have hm : momentOrder 0 x = 1 := by rw [momentOrder_of_lt (by norm_num)]; simp
      simp [hm]
    rcases lt_trichotomy q (1 / 2) with hq | rfl | hq
    · obtain ⟨c, C, x₀, hc, hC, H⟩ :=
        exists_integral_rpow_weightedRademacherSum_asymp_smallQ (Ω := Nat.Primes → ℂ) hq0' hq
      refine weighted_two_sided_ge_three (x₀ := x₀) hq0 hq1 hc hC
        (inv_pos.2 (lt_of_lt_of_le one_pos (le_max_left 1 (Real.log (Real.log (max x₀ 3))))))
        (by norm_num : (0 : ℝ) < 961 / 4) (fun x hx hxX => momentOrder_bounds_of_lt hq0 hq hx hxX)
        (fun X μ hX x hx => ?_)
      rw [momentOrder_of_lt hq]
      exact H X μ hX x hx
    · obtain ⟨c, C, x₀, hc, hC, H⟩ :=
        exists_integral_weightedRademacherSum_asymp_half (Ω := Nat.Primes → ℂ)
      refine weighted_two_sided_ge_three (x₀ := x₀) hq0 hq1 hc hC (by norm_num : (0 : ℝ) < 4 / 961)
        (lt_of_lt_of_le one_pos (le_max_left 1 (Real.log (Real.log (max x₀ 3)))))
        (fun x hx hxX => momentOrder_bounds_half hx hxX) (fun X μ hX x hx => ?_)
      rw [momentOrder_half, show (2 : ℝ) * (1 / 2) = 1 by norm_num]
      simp only [Real.rpow_one]
      exact H X μ hX x hx
    · obtain ⟨c, C, x₀, hc, hC, H⟩ :=
        exists_integral_rpow_weightedRademacherSum_asymp_largeQ (Ω := Nat.Primes → ℂ) hq
      refine weighted_two_sided_ge_three (x₀ := x₀) hq0 hq1 hc hC one_pos
        (lt_of_lt_of_le one_pos (le_max_left 1 (Real.log (max x₀ 3))))
        (fun x hx hxX => momentOrder_bounds_of_gt hq hq1 hx hxX) (fun X μ hX x hx => ?_)
      rw [momentOrder_of_gt hq]
      exact H X μ hX x hx
  refine ⟨c, C, hc, hC, fun Ω _ X μ hX x hx => ?_⟩
  rw [hX.integral_rpow_weightedRademacherSum_squarefreeExtension_eq]
  exact H _ _ (isIIDPrimeValues_primeExtend rademacherLaw) x hx

/-- **Theorem 1.1 of the paper.**  Let `0 ≤ q ≤ 1` be fixed.  Uniformly for `x ≥ 3`,

`E|x^{-1/2}∑_{n≤x} X^e(n)|^{2q} ≍ (log log x)^{-q/2}` if `0 ≤ q < ½`, `(log log x)^{3/4}` if
`q = ½`, and `(log x)^{q(2q-1)}` if `½ < q ≤ 1`

(`RMF.momentOrder`), for the completely multiplicative extension `X^e` of the Rademacher signs,
with `c`, `C` depending on `q` only, not on the probability space.  For `x ≥ x₀`: below `½`,
`RMF.exists_integral_rpow_normalisedSum_compMultExtension_asymp_smallQ`; at `½`,
`RMF.exists_le_integral_norm_normalisedSum_compMultExtension_half` and
`RMF.exists_const_integral_rpow_normalisedSum_compMultExtension_le_smallQ_uniform`; above `½`,
`RMF.exists_le_integral_rpow_norm_normalisedSum_compMultExtension_of_le_one` and
`RMF.exists_integral_rpow_norm_normalisedSum_compMultExtension_le_sharp_of_exp_exp_le`.
`RMF.extended_two_sided_ge_three` brings each down to `x ≥ 3`. -/
theorem extended_rademacher_moments (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        c * momentOrder q x
            ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ
          ∧ (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
            ≤ C * momentOrder q x := by
  obtain ⟨c, C, hc, hC, H⟩ : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X : ℕ → (Nat.Primes → ℂ) → ℂ) (μ : Measure (Nat.Primes → ℂ)),
        IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        c * momentOrder q x
            ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ
          ∧ (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
            ≤ C * momentOrder q x := by
    rcases eq_or_lt_of_le hq0 with h0 | hq0'
    · subst h0
      refine ⟨1, 1, one_pos, one_pos, fun X μ hX x _ => ?_⟩
      haveI := hX.isProbabilityMeasure
      have hm : momentOrder 0 x = 1 := by rw [momentOrder_of_lt (by norm_num)]; simp
      simp [hm]
    rcases lt_trichotomy q (1 / 2) with hq | rfl | hq
    · obtain ⟨c, C, x₀, hc, hC, H⟩ :=
        exists_integral_rpow_normalisedSum_compMultExtension_asymp_smallQ (Ω := Nat.Primes → ℂ)
          hq0' hq
      refine extended_two_sided_ge_three (x₀ := x₀) hq0 hq1 hc hC
        (inv_pos.2 (lt_of_lt_of_le one_pos (le_max_left 1 (Real.log (Real.log (max x₀ 3))))))
        (by norm_num : (0 : ℝ) < 961 / 4) (fun x hx hxX => momentOrder_bounds_of_lt hq0 hq hx hxX)
        (fun X μ hX x hx => ?_)
      rw [momentOrder_of_lt hq]
      exact H X μ hX x hx
    · obtain ⟨c, x₁, hc, HL⟩ :=
        exists_le_integral_norm_normalisedSum_compMultExtension_half (Ω := Nat.Primes → ℂ)
      obtain ⟨C, x₂, hC, HU⟩ :=
        exists_const_integral_rpow_normalisedSum_compMultExtension_le_smallQ_uniform
          (Ω := Nat.Primes → ℂ)
      refine extended_two_sided_ge_three (x₀ := max (max x₁ x₂) 3) hq0 hq1 hc hC
        (by norm_num : (0 : ℝ) < 4 / 961)
        (lt_of_lt_of_le one_pos
          (le_max_left 1 (Real.log (Real.log (max (max (max x₁ x₂) 3) 3)))))
        (fun x hx hxX => momentOrder_bounds_half hx hxX) (fun X μ hX x hx => ?_)
      have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
      have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
      have hx3 : (3 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
      have hL0 : 0 < Real.log (Real.log x) := by
        linarith [four_div_nine_hundred_sixty_one_le_log_log hx3]
      have h2 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
      rw [momentOrder_half, h2]
      simp only [Real.rpow_one]
      refine ⟨HL X μ hX x hx1, ?_⟩
      have h := HU X μ hX x (1 / 2) hx2 (by norm_num) le_rfl
      have e : ((Real.log (Real.log x))⁻¹ + (1 - 2 * (1 / 2)))⁻¹
          * Real.log (Real.log x) ^ (-((1 / 2 : ℝ) / 2)) = Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
        rw [show (1 : ℝ) - 2 * (1 / 2) = 0 by norm_num, add_zero, inv_inv]
        nth_rewrite 1 [← Real.rpow_one (Real.log (Real.log x))]
        rw [← Real.rpow_add hL0]
        norm_num
      rw [e, h2] at h
      simp only [Real.rpow_one] at h
      exact h
    · obtain ⟨c, x₁, hc, HL⟩ :=
        exists_le_integral_rpow_norm_normalisedSum_compMultExtension_of_le_one
          (Ω := Nat.Primes → ℂ) hq hq1
      obtain ⟨C, hC, HU⟩ :=
        exists_integral_rpow_norm_normalisedSum_compMultExtension_le_sharp_of_exp_exp_le
          (Ω := Nat.Primes → ℂ)
      have hm0 : 0 < (2 * q - 1)⁻¹ := inv_pos.2 (by linarith)
      have hb0 : 0 < ballotFactor q (2 * q - 1)⁻¹ := by
        unfold ballotFactor
        have h1 := mul_nonneg (sub_nonneg.2 hq1) (Real.sqrt_nonneg ((2 * q - 1)⁻¹))
        exact mul_pos hm0 (Real.rpow_pos_of_pos (by linarith) _)
      refine extended_two_sided_ge_three (x₀ := max x₁ (Real.exp (Real.exp 1))) hq0 hq1 hc
        (mul_pos hC hb0) one_pos
        (lt_of_lt_of_le one_pos (le_max_left 1 (Real.log (max (max x₁ (Real.exp (Real.exp 1))) 3))))
        (fun x hx hxX => momentOrder_bounds_of_gt hq hq1 hx hxX) (fun X μ hX x hx => ?_)
      have hx1 : x₁ ≤ x := le_trans (le_max_left _ _) hx
      have hxe : Real.exp (Real.exp 1) ≤ x := le_trans (le_max_right _ _) hx
      have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
      have hlogx : Real.exp 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe
      have hL1 : 1 ≤ Real.log (Real.log x) := by
        have h := Real.log_le_log (Real.exp_pos 1) hlogx
        rwa [Real.log_exp] at h
      have hmin0 : 0 < min (2 * q - 1)⁻¹ (Real.log (Real.log x)) := lt_min hm0 (by linarith)
      have hbmono := ballotFactor_le_ballotFactor (by linarith : (0 : ℝ) ≤ q) hq1 hmin0
        (min_le_left _ _)
      have hE0 : 0 ≤ Real.log x ^ (q * (2 * q - 1)) :=
        Real.rpow_nonneg ((Real.exp_pos 1).le.trans hlogx) _
      rw [momentOrder_of_gt hq]
      refine ⟨HL X μ hX x hx1, le_trans (HU X μ hX q x hq hq1 hxe) ?_⟩
      calc C * (Real.log x ^ (q * (2 * q - 1))
            * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log x))))
          ≤ C * (Real.log x ^ (q * (2 * q - 1)) * ballotFactor q (2 * q - 1)⁻¹) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbmono hE0) hC.le
        _ = C * ballotFactor q (2 * q - 1)⁻¹ * Real.log x ^ (q * (2 * q - 1)) := by ring
  refine ⟨c, C, hc, hC, fun Ω _ X μ hX x hx => ?_⟩
  rw [hX.integral_rpow_normalisedSum_compMultExtension_eq]
  exact H _ _ (isIIDPrimeValues_primeExtend rademacherLaw) x hx

end RMF
