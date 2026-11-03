/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.BlockSplitExplicit
import RMF.Weighted.BlockChaosWeightExplicit
import RMF.Weighted.LineSplit
import RMF.Weighted.LineTail
import RMF.Weighted.PropositionB
import RMF.Weighted.SmoothSumsExplicit

/-!
# The block family of `Z`, explicit

`Z` over the line, cut into the central window, the `e`-adic windows `(T_k/e, T_k]`,
`T_k = e^{-k}`, and the far range.

* **The windows keep their weight.**  The weight `(σ²+t²)⁻¹` stays inside each window
  (`RMF.integral_rpow_setIntegral_weight_le_sum_windows_inside`), and against the two-point ratio
  of the split it integrates to at most `((e - 1) + (e^{βT²} - 1)(1 - e⁻¹))/T`
  (`RMF.setIntegral_inv_sq_add_sq_mul_exp_window_le`).
* **Each window** is split at `z` with `log z ≈ 1/T_k`
  (`RMF.integral_rpow_setIntegral_weight_split_primesIco_le_sharp`), then its upper block is
  bounded by Jensen (`RMF.integral_rpow_window_le_split_jensen_of_weight`) or by the weighted
  chaos (`RMF.integral_rpow_window_le_split_chaos_of_weight`), at any bound on the window's
  weight.  The mean of the upper block is Mertens' ratio
  `(log y/log z)·e^{9.0028/log y + 9.0028/log z}`, in which Mertens' constant cancels.
* **The far range** `|t| > v` is Jensen against `∏_{p ≤ y}(1 + 1/p) ≤ 1.195 log y`
  (`RMF.integral_rpow_eulerProductLine_tail_le_explicit`); the three ranges are joined by
  `RMF.integral_rpow_lineDiv_le_of_three_ranges`
  (`RMF.integral_rpow_eulerLineDiv_le_of_three_ranges`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The weight of one window -/

/-- **The block window's weight against the two-point ratio.**  For `T > 0` and `β ≥ 0`,
`∫_{T/e}^{T} e^{βt²}dt/(σ²+t²) ≤ ((e - 1) + (e^{βT²} - 1)(1 - e⁻¹))/T`: on the window
`(σ²+t²)⁻¹ ≤ t⁻²` and `e^{βt²} ≤ 1 + (t/T)²(e^{βT²} - 1)` (`RMF.exp_mul_le_one_add_mul`), so the
integrand is at most `t⁻² + (e^{βT²} - 1)/T²`. -/
lemma setIntegral_inv_sq_add_sq_mul_exp_window_le (σ : ℝ) {T β : ℝ} (hT : 0 < T)
    (hβ : 0 ≤ β) :
    (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2))
      ≤ ((Real.exp 1 - 1) + (Real.exp (β * T ^ 2) - 1) * (1 - (Real.exp 1)⁻¹)) / T := by
  have he1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have ha0 : 0 < T / Real.exp 1 := div_pos hT he0
  have haT : T / Real.exp 1 ≤ T := div_le_self hT.le he1.le
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (T / Real.exp 1) T)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hT2 : 0 < T ^ 2 := by positivity
  have hE1 : 0 ≤ Real.exp (β * T ^ 2) - 1 := by
    linarith [Real.one_le_exp (mul_nonneg hβ hT2.le)]
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (Real.exp (β * T ^ 2) - 1) / T ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; exact div_nonneg hE1 hT2.le
  have hpt : ∀ t ∈ Set.Icc (T / Real.exp 1) T,
      (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2) ≤ t ^ (-2 : ℝ) + K := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    have ht2 : 0 < t ^ 2 := by positivity
    have hsq : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ ht0.le ht.2 2
    have hrw : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = t ^ 2 / T ^ 2 := ⟨_, rfl⟩
    have hl0 : 0 ≤ l := by rw [hl]; positivity
    have hl1 : l ≤ 1 := by rw [hl, div_le_one hT2]; exact hsq
    have hexp : Real.exp (β * t ^ 2) ≤ 1 + l * (Real.exp (β * T ^ 2) - 1) := by
      have : β * t ^ 2 = l * (β * T ^ 2) := by
        rw [hl]
        field_simp
      rw [this]
      exact exp_mul_le_one_add_mul hl0 hl1
    have hinv : (σ ^ 2 + t ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ :=
      inv_anti₀ ht2 (le_add_of_nonneg_left (sq_nonneg σ))
    have htne : t ≠ 0 := ht0.ne'
    have hTne : T ≠ 0 := hT.ne'
    calc (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2)
        ≤ (t ^ 2)⁻¹ * (1 + l * (Real.exp (β * T ^ 2) - 1)) :=
          mul_le_mul hinv hexp (Real.exp_pos _).le (inv_nonneg.2 ht2.le)
      _ = (t ^ 2)⁻¹ + K := by
          rw [hl, hK]
          field_simp
      _ = t ^ (-2 : ℝ) + K := by rw [hrw]
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Icc (T / Real.exp 1) T) :=
    continuousOn_id.rpow_const fun t ht => Or.inl (lt_of_lt_of_le ha0 ht.1).ne'
  have hcont1 : ContinuousOn (fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2))
      (Set.Icc (T / Real.exp 1) T) := by
    refine ContinuousOn.mul ?_ (by fun_prop : Continuous fun t : ℝ =>
      Real.exp (β * t ^ 2)).continuousOn
    refine ContinuousOn.inv₀ (by fun_prop : Continuous fun t : ℝ => σ ^ 2 + t ^ 2).continuousOn ?_
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    positivity
  have hval : (∫ t in Set.Icc (T / Real.exp 1) T, t ^ (-2 : ℝ))
      = (T / Real.exp 1)⁻¹ - T⁻¹ := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le haT,
      integral_rpow (Or.inr ⟨by norm_num, ?_⟩)]
    · rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, Real.rpow_neg_one]
      ring
    · rw [Set.uIcc_of_le haT]
      exact fun h => absurd h.1 (not_le.2 ha0)
  calc (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2))
      ≤ ∫ t in Set.Icc (T / Real.exp 1) T, (t ^ (-2 : ℝ) + K) :=
        setIntegral_mono_on hcont1.integrableOn_Icc
          (hcont.integrableOn_Icc.add (integrable_const K)) measurableSet_Icc hpt
    _ = (∫ t in Set.Icc (T / Real.exp 1) T, t ^ (-2 : ℝ))
          + ∫ _t in Set.Icc (T / Real.exp 1) T, K :=
        integral_add hcont.integrableOn_Icc (integrable_const K)
    _ = ((T / Real.exp 1)⁻¹ - T⁻¹) + (T - T / Real.exp 1) * K := by
        rw [hval, setIntegral_const, Real.volume_real_Icc_of_le haT, smul_eq_mul]
    _ = ((Real.exp 1 - 1) + (Real.exp (β * T ^ 2) - 1) * (1 - (Real.exp 1)⁻¹)) / T := by
        rw [hK]
        field_simp

/-! ### The mean of the upper block -/

/-- **Mertens' second theorem from above, with Mertens' constant**:
`∑_{p ≤ y} 1/p ≤ log log y + M + 9.0028/log y` for `y ≥ 2`.  The twin of
`RMF.log_log_add_le_sum_primesBelow_inv`. -/
theorem sum_primesBelow_inv_le_log_log_add_mertens {y : ℕ} (hy : 2 ≤ y) :
    ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹
      ≤ Real.log (Real.log y) + Mertens.M + 9.0028 / Real.log y := by
  classical
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have heq := Mertens.sum_prime_div_eq (y : ℝ)
  have habs := Mertens.E₂p.abs_le hy2
  have hconst := mertens_error_const_le
  have hE : Mertens.E₂p (y : ℝ) ≤ 9.0028 / Real.log y := by
    have h1 := (abs_le.1 habs).2
    have h2 : (Real.log 4 + 6 + Mertens.E₁) / Real.log y ≤ 9.0028 / Real.log y :=
      div_le_div_of_nonneg_right hconst hlogy.le
    linarith
  rw [Nat.floor_natCast] at heq
  have hset : Finset.filter (fun p => Nat.Prime p) (Finset.Ioc 0 y) = Nat.primesBelow (y + 1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesBelow]
    exact ⟨fun hp => ⟨by omega, hp.2⟩, fun hp => ⟨⟨hp.2.pos, by omega⟩, hp.2⟩⟩
  rw [hset] at heq
  have hinv : ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹
      = ∑ p ∈ Nat.primesBelow (y + 1), (1 : ℝ) / p :=
    Finset.sum_congr rfl fun p _ => (one_div _).symm
  rw [hinv, heq]
  linarith

/-- **Mertens' second theorem on a block**: for `2 ≤ z ≤ y`,
`∑_{z < p ≤ y} 1/p ≤ log log y - log log z + 9.0028/log y + 9.0028/log z`.  Mertens' constant
cancels between the two ends. -/
theorem sum_primesIco_inv_le {z y : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y) :
    ∑ p ∈ primesIco (z + 1) (y + 1), ((p : ℝ))⁻¹
      ≤ Real.log (Real.log y) - Real.log (Real.log z) + 9.0028 / Real.log y
        + 9.0028 / Real.log z := by
  have hup := sum_primesBelow_inv_le_log_log_add_mertens (le_trans hz hzy)
  have hlow := log_log_add_le_sum_primesBelow_inv hz
  have hsplit : ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹
      = ∑ p ∈ Nat.primesBelow (z + 1), ((p : ℝ))⁻¹
        + ∑ p ∈ primesIco (z + 1) (y + 1), ((p : ℝ))⁻¹ := by
    rw [← primesIco_zero (y + 1), ← primesIco_zero (z + 1),
      ← primesIco_union (Nat.zero_le _) (by omega : z + 1 ≤ y + 1),
      Finset.sum_union (disjoint_primesIco 0 (z + 1) (y + 1))]
  linarith

/-- **The upper block's second moment against Mertens**: for `2 ≤ z ≤ y` and `σ ≥ 0`, at every
height, `E‖F_{(z,y]}(½+σ+ih)‖² ≤ (log y/log z)·e^{9.0028/log y + 9.0028/log z}`. -/
theorem integral_normSq_Ico_shiftLine_le_mertens_ratio {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {z y : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y) {σ : ℝ}
    (hσ : 0 ≤ σ) (h : ℝ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (z + 1) (y + 1)
        (shiftLine σ h) ω‖ ^ 2 ∂ν)
      ≤ Real.log y / Real.log z * Real.exp (9.0028 / Real.log y + 9.0028 / Real.log z) := by
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  rw [hf.integral_norm_randomEulerProductIco_sq (z + 1) (y + 1) (shiftLine σ h)]
  have hnorm : ∀ p ∈ primesIco (z + 1) (y + 1),
      1 + ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h))‖ ^ 2 = 1 + (p : ℝ) ^ (-2 * (1 / 2 + σ)) := by
    intro p hp
    have hp0 : 0 < p := (prime_of_mem_primesIco hp).pos
    rw [Complex.norm_natCast_cpow_of_pos hp0, Complex.neg_re, re_shiftLine,
      ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
    ring_nf
  rw [Finset.prod_congr rfl hnorm]
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (le_trans hz hzy)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hfac : ∀ p ∈ primesIco (z + 1) (y + 1),
      1 + (p : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ Real.exp ((p : ℝ)⁻¹) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (prime_of_mem_primesIco hp).one_lt.le
    have h1 : (p : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ (p : ℝ)⁻¹ := by
      calc (p : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ (p : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
        _ = (p : ℝ)⁻¹ := Real.rpow_neg_one _
    linarith [Real.add_one_le_exp ((p : ℝ)⁻¹)]
  calc ∏ p ∈ primesIco (z + 1) (y + 1), (1 + (p : ℝ) ^ (-2 * (1 / 2 + σ)))
      ≤ ∏ p ∈ primesIco (z + 1) (y + 1), Real.exp ((p : ℝ)⁻¹) :=
        Finset.prod_le_prod (fun p _ => by positivity) hfac
    _ = Real.exp (∑ p ∈ primesIco (z + 1) (y + 1), (p : ℝ)⁻¹) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (Real.log (Real.log y) - Real.log (Real.log z) + 9.0028 / Real.log y
          + 9.0028 / Real.log z) :=
        Real.exp_le_exp.2 (sum_primesIco_inv_le hz hzy)
    _ = Real.log y / Real.log z * Real.exp (9.0028 / Real.log y + 9.0028 / Real.log z) := by
        rw [show Real.log (Real.log y) - Real.log (Real.log z) + 9.0028 / Real.log y
            + 9.0028 / Real.log z = (Real.log (Real.log y) - Real.log (Real.log z))
              + (9.0028 / Real.log y + 9.0028 / Real.log z) by ring,
          Real.exp_add, ← Real.log_div hlogy.ne' hlogz.ne', Real.exp_log (div_pos hlogy hlogz)]

/-! ### The windows, with the weight inside -/

/-- **The window decomposition with the weight kept inside**, in expectation: for `0 < q ≤ 1`,
`σ ≥ 0`, windows `(a i, b i] ⊆ [A, B]` covering `S ⊆ [A, B]` and a bounded measurable `ρ ≥ 0`,
`E[(∫_S ρ‖F_n(½+σ+it)‖²dt)^q] ≤ ∑_i E[(∫_{[a i, b i]}ρ‖F_n(½+σ+it)‖²dt)^q]`. -/
theorem integral_rpow_setIntegral_weight_le_sum_windows_inside {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (n : ℕ) {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 0 < q)
    (hq1 : q ≤ 1) {ι : Type*} (I : Finset ι) (a b : ι → ℝ) {A B Bρ : ℝ} {ρ : ℝ → ℝ}
    {S : Set ℝ} (hρ0 : ∀ t, 0 ≤ ρ t) (hρm : Measurable ρ) (hρb : ∀ t, ρ t ≤ Bρ)
    (hS : MeasurableSet S) (hSAB : S ⊆ Set.Icc A B)
    (hIAB : ∀ i ∈ I, Set.Ioc (a i) (b i) ⊆ Set.Icc A B)
    (hcov : ∀ t ∈ S, ∃ i ∈ I, t ∈ Set.Ioc (a i) (b i)) :
    (∫ ω, (∫ t in S, ρ t * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ ∑ i ∈ I, ∫ ω, (∫ t in Set.Icc (a i) (b i), ρ t *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hSnn : ∀ ω : Ω, (0 : ℝ) ≤ ∫ t in S, ρ t *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
        (shiftLine σ t) ω‖ ^ 2 :=
    fun ω => integral_nonneg fun t => mul_nonneg (hρ0 t) (sq_nonneg _)
  have hYnn : ∀ (i : ι) (ω : Ω), (0 : ℝ) ≤ ∫ t in Set.Icc (a i) (b i), ρ t *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
        (shiftLine σ t) ω‖ ^ 2 :=
    fun i ω => integral_nonneg fun t => mul_nonneg (hρ0 t) (sq_nonneg _)
  -- each window moment is integrable: measurable by the slice, bounded by the envelope
  have hYint : ∀ i ∈ I, Integrable (fun ω => (∫ t in Set.Icc (a i) (b i), ρ t *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
        (shiftLine σ t) ω‖ ^ 2) ^ q) μ := by
    intro i _
    have hvol : volume (Set.Icc (a i) (b i)) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hsl := integrable_uncurry_weight_normSq_primesIco hX 0 n hσ hvol hρm hρ0 hρb
    simp only [randomEulerProductIco_zero] at hsl
    have hbd := ae_setIntegral_weight_normSq_primesIco_mem_Icc hX 0 n (a := a i) (b := b i) hσ
      hρm hρ0 hρb
    simp only [randomEulerProductIco_zero] at hbd
    refine (memLp_top_of_bound
      ((Real.continuous_rpow_const hq0.le).comp_aestronglyMeasurable hsl.integral_prod_left.1)
      (((∫ t in Set.Icc (a i) (b i), ρ t)
        * (∏ p ∈ primesIco 0 n, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2) ^ q) ?_).integrable le_top
    filter_upwards [hbd] with ω hω
    simp only [Function.uncurry_apply_pair]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hYnn i ω) _)]
    exact Real.rpow_le_rpow (hYnn i ω) hω.2 hq0.le
  have hRint : Integrable (fun ω => ∑ i ∈ I, (∫ t in Set.Icc (a i) (b i), ρ t *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
        (shiftLine σ t) ω‖ ^ 2) ^ q) μ :=
    integrable_finsetSum _ fun i hi => hYint i hi
  -- pathwise: the window domination at weight `1`, then subadditivity of `u ↦ u^q`
  have hvolAB : volume (Set.Icc A B) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hslAB := integrable_uncurry_weight_normSq_primesIco hX 0 n hσ hvolAB hρm hρ0 hρb
  simp only [randomEulerProductIco_zero] at hslAB
  have hstep : ∀ᵐ ω ∂μ, (∫ t in S, ρ t *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
          (shiftLine σ t) ω‖ ^ 2) ^ q
      ≤ ∑ i ∈ I, (∫ t in Set.Icc (a i) (b i), ρ t *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
            (shiftLine σ t) ω‖ ^ 2) ^ q := by
    filter_upwards [hslAB.prod_right_ae] with ω hint0
    have hint : IntegrableOn (fun t => ρ t * ‖randomEulerProduct
        (fun ω => squarefreeExtension fun p => X p ω) n (shiftLine σ t) ω‖ ^ 2)
        (Set.Icc A B) := hint0
    have hA := setIntegral_weight_le_sum_windows (ρ := fun _ => (1 : ℝ)) (Bρ := 1) I a b
      (fun _ => 1) (fun t => mul_nonneg (hρ0 t) (sq_nonneg _)) hint (fun _ => zero_le_one)
      measurable_const (fun _ => le_rfl) hS hSAB hIAB hcov (fun _ _ => zero_le_one)
      (fun _ _ _ _ => le_rfl)
    simp only [one_mul] at hA
    exact le_trans (Real.rpow_le_rpow (hSnn ω) hA hq0.le)
      (rpow_sum_le_sum_rpow I (fun i => hYnn i ω) hq0 hq1)
  refine le_trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hSnn ω) q) hRint hstep) ?_
  exact le_of_eq (integral_finsetSum _ fun i hi => hYint i hi)

/-! ### The mesoscopic range -/

/-- **The mesoscopic range of `Z` as a sum of windows, the weight kept inside.**  For `σ > 0`,
`0 < q ≤ 1` and `k₀ ≤ J`, with `T_k = e^{-k}`:

`E[((log y)⁻¹∫_{e^{-J}<|t|≤e^{-k₀}}‖F_{y+1}(½+σ+it)/(σ+it)‖²dt)^q]
  ≤ (2/log y)^q·∑_{k₀≤k<J} E[(∫_{T_k/e}^{T_k}(σ²+t²)⁻¹‖F_{y+1}(½+σ+it)‖²dt)^q]`.

The fold `t ↦ -t` (`RMF.ae_setIntegral_weight_normSq_symm`), then the windows
(`RMF.integral_rpow_setIntegral_weight_le_sum_windows_inside`). -/
theorem integral_rpow_mesoRange_le_sum_windows {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {σ q : ℝ} {y k₀ J : ℕ} (hy2 : 2 ≤ y) (hσ : 0 < σ)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hk₀J : k₀ ≤ J) :
    (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-(J : ℝ)) < |t|
          ∧ |t| ≤ Real.exp (-(k₀ : ℝ))},
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
      ≤ (2 / Real.log y) ^ q * ∑ k ∈ Finset.Ico k₀ J,
          ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1) (Real.exp (-(k : ℝ))),
            (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (y + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν := by
  haveI := hY.isProbabilityMeasure
  have hy2' : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  -- the integrand, decoupled
  have hint : ∀ (ω : Ω) (t : ℝ),
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        = (σ ^ 2 + t ^ 2)⁻¹
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              (shiftLine σ t) ω‖ ^ 2 := by
    intro ω t
    rw [norm_div_ofReal_add_mul_I_sq]
    congr 3
    rw [shiftLine]
    push_cast
    ring
  simp only [hint]
  have hρb : ∀ t : ℝ, (σ ^ 2 + t ^ 2)⁻¹ ≤ (σ ^ 2)⁻¹ := fun t =>
    (inv_le_inv₀ (by positivity) (by positivity)).2 (by nlinarith [sq_nonneg t])
  have hkJ : (k₀ : ℝ) ≤ (J : ℝ) := by exact_mod_cast hk₀J
  have hk₀1 : Real.exp (-(J : ℝ)) ≤ Real.exp (-(k₀ : ℝ)) := Real.exp_le_exp.2 (by linarith)
  -- the reflection
  have hfold := ae_setIntegral_weight_normSq_symm hY (y + 1) hσ.le
    (ρ := fun t => (σ ^ 2 + t ^ 2)⁻¹) (Bρ := (σ ^ 2)⁻¹) (fun t => by norm_num)
    (by fun_prop) (fun t => by positivity) hρb (Real.exp_pos _).le hk₀1
  have hcongr : (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-(J : ℝ)) < |t|
          ∧ |t| ≤ Real.exp (-(k₀ : ℝ))},
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
          (y + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      = ∫ ω, (2 / Real.log y) ^ q * (∫ t in Set.Ioc (Real.exp (-(J : ℝ)))
          (Real.exp (-(k₀ : ℝ))), (σ ^ 2 + t ^ 2)⁻¹
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (y + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hfold] with ω hω
    rw [hω, ← Real.mul_rpow (by positivity) (integral_nonneg fun t => by positivity)]
    congr 1
    ring
  rw [hcongr, integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
  -- the windows
  have hk0 : ∀ k : ℕ, Real.exp (-(k : ℝ)) ≤ 1 := fun k =>
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Nat.cast_nonneg k))
  refine integral_rpow_setIntegral_weight_le_sum_windows_inside hY (y + 1) hσ.le hq0 hq1
    (Finset.Ico k₀ J) (fun k => Real.exp (-(k : ℝ)) / Real.exp 1)
    (fun k => Real.exp (-(k : ℝ))) (A := 0) (B := 1) (fun t => by positivity) (by fun_prop) hρb
    measurableSet_Ioc ?_ ?_ ?_
  · intro t ht
    exact ⟨le_trans (Real.exp_pos _).le ht.1.le, le_trans ht.2 (hk0 k₀)⟩
  · intro k _ t ht
    exact ⟨le_trans (by positivity) ht.1.le, le_trans ht.2 (hk0 k)⟩
  · intro t ht
    have ht0 : 0 < t := lt_trans (Real.exp_pos _) ht.1
    have hlo : -(J : ℝ) < Real.log t := by
      have := Real.log_lt_log (Real.exp_pos _) ht.1
      rwa [Real.log_exp] at this
    have hhi : Real.log t ≤ -(k₀ : ℝ) := by
      have := Real.log_le_log ht0 ht.2
      rwa [Real.log_exp] at this
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = -Real.log t := ⟨_, rfl⟩
    have hu0 : 0 ≤ u := by
      have : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg _
      linarith
    have hfl1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu0
    have hfl2 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
    have htu : t = Real.exp (-u) := by rw [hu, neg_neg, Real.exp_log ht0]
    refine ⟨⌊u⌋₊, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      constructor
      · exact Nat.le_floor (by linarith)
      · have h2 : (⌊u⌋₊ : ℝ) < J := by linarith
        exact_mod_cast h2
    · constructor
      · change Real.exp (-((⌊u⌋₊ : ℕ) : ℝ)) / Real.exp 1 < t
        rw [htu, ← Real.exp_sub]
        exact Real.exp_lt_exp.2 (by linarith)
      · change t ≤ Real.exp (-((⌊u⌋₊ : ℕ) : ℝ))
        rw [htu]
        exact Real.exp_le_exp.2 (by linarith)

/-! ### One window -/

/-- **The two weights of one window**: `ρ(t) = (σ²+t²)⁻¹` and
`ρ'(t) = (σ²+t²)⁻¹e^{β min(t², T²)}`, which is `ρ(t)e^{βt²}` on the window `[T/e, T]` and bounded
on the line; `∫_{[T/e,T]}ρ > 0`. -/
lemma window_weights {σ T β : ℝ} (hσ : 0 < σ) (hT : 0 < T) (hβ : 0 ≤ β) :
    (∀ t : ℝ, (σ ^ 2 + t ^ 2)⁻¹ ≤ (σ ^ 2)⁻¹)
      ∧ (∀ t : ℝ, (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2))
          ≤ (σ ^ 2)⁻¹ * Real.exp (β * T ^ 2))
      ∧ (∀ t ∈ Set.Icc (T / Real.exp 1) T,
          (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2)
            = (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)))
      ∧ 0 < ∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ := by
  have he1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hTe0 : 0 < T / Real.exp 1 := div_pos hT (Real.exp_pos 1)
  have hTeT : T / Real.exp 1 < T := div_lt_self hT he1
  have hρb : ∀ t : ℝ, (σ ^ 2 + t ^ 2)⁻¹ ≤ (σ ^ 2)⁻¹ := fun t =>
    (inv_le_inv₀ (by positivity) (by positivity)).2 (by nlinarith [sq_nonneg t])
  refine ⟨hρb, fun t => ?_, fun t ht => ?_, ?_⟩
  · refine mul_le_mul (hρb t) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by positivity)
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hβ
  · have ht0 : 0 ≤ t := le_trans hTe0.le ht.1
    rw [min_eq_left (pow_le_pow_left₀ ht0 ht.2 2)]
  · haveI : IsFiniteMeasure (volume.restrict (Set.Icc (T / Real.exp 1) T)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
    have hcont : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
      Continuous.inv₀ (by fun_prop) fun t => (by positivity : (0 : ℝ) < σ ^ 2 + t ^ 2).ne'
    have hle : (∫ _t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + T ^ 2)⁻¹)
        ≤ ∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ := by
      refine setIntegral_mono_on (integrable_const _) hcont.integrableOn_Icc measurableSet_Icc
        fun t ht => ?_
      have ht0 : 0 ≤ t := le_trans hTe0.le ht.1
      have hsq : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ ht0 ht.2 2
      exact inv_anti₀ (by positivity) (by linarith)
    rw [setIntegral_const, Real.volume_real_Icc_of_le hTeT.le, smul_eq_mul] at hle
    have hc : (0 : ℝ) < (σ ^ 2 + T ^ 2)⁻¹ := by positivity
    exact lt_of_lt_of_le (mul_pos (by linarith) hc) hle

/-- **One window by the split and Jensen, at any bound `R` on the window's weight**
`∫_{T/e}^{T}e^{βt²}dt/(σ²+t²) ≤ R`.  For `2 ≤ z ≤ y`, `σ > 0`, `0 ≤ q ≤ ½`, `T > 0` and
`β ≥ 2(1-q)S₂(z+1)`, `S₂(w) = (log w)²/2 + 15.003 log w + 34`, with `F_{z+1}` the product over
`p ≤ z`:

`E[(∫_{T/e}^{T}(σ²+t²)⁻¹‖F_{y+1}(½+σ+it)‖²dt)^q]
  ≤ E‖F_{z+1}(½+σ)‖^{2q}·(R·(log y/log z)·e^{9.0028/log y + 9.0028/log z})^q`:

the sharp weighted split (`RMF.integral_rpow_setIntegral_weight_split_primesIco_le_sharp`), then
Jensen on the upper block, whose mean is Mertens' ratio
(`RMF.integral_normSq_Ico_shiftLine_le_mertens_ratio`). -/
theorem integral_rpow_window_le_split_jensen_of_weight {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {z y : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y) {σ q T β R : ℝ}
    (hσ : 0 < σ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (hT : 0 < T)
    (hβ : 2 * (1 - q) * (Real.log ((z + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((z + 1 : ℕ) : ℝ) + 34) ≤ β)
    (hR : (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2)) ≤ R) :
    (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      ≤ (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (z + 1)
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂ν)
        * (R
          * (Real.log y / Real.log z
            * Real.exp (9.0028 / Real.log y + 9.0028 / Real.log z))) ^ q := by
  haveI := hY.isProbabilityMeasure
  have hq1 : q ≤ 1 := by linarith
  have hβ0 : 0 ≤ β := by
    have h1 : (0 : ℝ) ≤ 1 - q := by linarith
    have h2 : (0 : ℝ) ≤ Real.log ((z + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z + 1))
    have : (0 : ℝ) ≤ 2 * (1 - q) * (Real.log ((z + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((z + 1 : ℕ) : ℝ) + 34) := by positivity
    linarith
  obtain ⟨hρb, hρb', hρρ', hρpos⟩ := window_weights hσ hT hβ0
  have hvol : volume (Set.Icc (T / Real.exp 1) T) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hρm' : Measurable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)) :=
    by fun_prop
  have hρ0' : ∀ t : ℝ, 0 ≤ (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)) :=
    fun t => by positivity
  -- the split
  have hsplit := integral_rpow_setIntegral_weight_split_primesIco_le_sharp hY (y₀ := 0)
    (z := z + 1) (y := y + 1) (Nat.zero_le _) (by omega) (σ := σ) (a := T / Real.exp 1)
    (b := T) (q := q) (β := β) (Bd := (σ ^ 2)⁻¹) (Bd' := (σ ^ 2)⁻¹ * Real.exp (β * T ^ 2))
    (ρ := fun t => (σ ^ 2 + t ^ 2)⁻¹)
    (ρ' := fun t => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)))
    hσ.le hq0 hq hβ (by fun_prop) (fun t => by positivity) hρb hρm' hρ0' hρb'
    (fun t ht => le_of_eq (hρρ' t ht)) hρpos
  simp only [randomEulerProductIco_zero] at hsplit
  -- Jensen on the upper block
  set S : Ω → ℝ := fun ω => ∫ t in Set.Icc (T / Real.exp 1) T,
    (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2))
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (z + 1) (y + 1)
        (shiftLine σ t) ω‖ ^ 2 with hSdef
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => integral_nonneg fun t => mul_nonneg (hρ0' t) (sq_nonneg _)
  have hSi : Integrable S ν :=
    (integrable_uncurry_weight_normSq_primesIco hY (z + 1) (y + 1) hσ.le hvol hρm' hρ0'
      hρb').integral_prod_left
  have hSqi : Integrable (fun ω => S ω ^ q) ν :=
    integrable_rpow_of_integrable hSi (Filter.Eventually.of_forall hS0) hq0 hq1
  have hjen : (∫ ω, S ω ^ q ∂ν) ≤ (∫ ω, S ω ∂ν) ^ q :=
    integral_rpow_le_rpow_integral hq0 hq1 (Filter.Eventually.of_forall hS0) hSi hSqi
  have hmean := integral_setIntegral_weight_normSq_Ico_le hY (z + 1) (y + 1) (a := T / Real.exp 1)
    (b := T) hσ.le hρm' hρ0' hρb'
  -- the weight and the mean
  have hW : (∫ t in Set.Icc (T / Real.exp 1) T,
      (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)))
      ≤ R := by
    rw [← setIntegral_congr_fun measurableSet_Icc hρρ']
    exact hR
  have hM := integral_normSq_Ico_shiftLine_le_mertens_ratio hY hz hzy hσ.le 0
  have hW0 : 0 ≤ ∫ t in Set.Icc (T / Real.exp 1) T,
      (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)) :=
    integral_nonneg fun t => hρ0' t
  have hM0 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
      (z + 1) (y + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν := integral_nonneg fun ω => sq_nonneg _
  have hprod := mul_le_mul hW hM hM0 (le_trans hW0 hW)
  have hES0 : 0 ≤ ∫ ω, S ω ∂ν := integral_nonneg hS0
  have hupper : (∫ ω, S ω ^ q ∂ν)
      ≤ (R
          * (Real.log y / Real.log z
            * Real.exp (9.0028 / Real.log y + 9.0028 / Real.log z))) ^ q :=
    le_trans hjen (Real.rpow_le_rpow hES0 (le_trans hmean hprod) hq0)
  refine le_trans hsplit (mul_le_mul_of_nonneg_left hupper ?_)
  exact integral_nonneg fun ω => by positivity

/-- **One window by the split and the weighted chaos, at any bound `R` on the window's weight.**
As `RMF.integral_rpow_window_le_split_jensen_of_weight`, with the upper block bounded by the
weighted block chaos at the level floor `16Δ` (`RMF.integral_rpow_block_weight_le_floor`, at
`x = y`):

`E[(∫_{T/e}^{T}(σ²+t²)⁻¹‖F_{y+1}(½+σ+it)‖²dt)^q]
  ≤ E‖F_{z+1}(½+σ)‖^{2q}·shiftMomentConst 1 C_i (C_b K_ϑ) A s λ δ q
      ·(R·(log y/log z)·e^{9.0028/log y + 9.0028/log z})^q·(1 + (1-q)√n)^{-q}`,

`n = harperBlockCount D y`. -/
theorem integral_rpow_window_le_split_chaos_of_weight (E₀ βc : ℝ) (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1)
    (hβc : 1 / 2 < βc) (hβc2 : βc ≤ 2) {Tr κ Kθ Amax δ : ℝ} {N : ℕ} (hTr : 4 < Tr)
    (hκ : 1 ≤ κ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δ * N)
    (hmono : 3 ≤ 8 * δ * Real.sqrt (N : ℝ))
    {Y : ℕ → Ω → ℂ} {ν : Measure Ω} (hY : IsRademacherPrimeValues Y ν) {z y D : ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y) {σ η q T β A lam R : ℝ}
    (hσ : 0 < σ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (hT : 0 < T) (hT1 : T ≤ 1)
    (hβ : 2 * (1 - q) * (Real.log ((z + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((z + 1 : ℕ) : ℝ) + 34) ≤ β)
    (hDlog : (D : ℝ) ≤ Real.log (Real.log y))
    (hϑ : radFreeStartThreshold E₀ ≤ harperOffset D y)
    (hϑ104 : (104 : ℝ) ≤ harperOffset D y)
    (hη0 : 0 ≤ η) (hηE : η ≤ E₀) (hσx : σ * Real.log y ≤ η)
    (hlo : 600 * Real.exp (2 * E₀) ≤ 2 * (T / Real.exp 1) * Real.exp (harperOffset D y))
    (hKθ : T * Real.exp (harperOffset D y) ≤ Kθ)
    (hzb : ((z + 1 : ℕ) : ℝ) ≤ blockScale (harperOffset D y) 0)
    (hNn : N ≤ harperBlockCount D y)
    (hA : radBlockBadLevel E₀ ≤ A) (hAmax : A ≤ Amax) (hlam : 1 ≤ lam)
    (hR : (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2)) ≤ R) :
    (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      ≤ (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (z + 1)
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂ν)
        * (shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ) (radBlockBadConst E₀ βc * Kθ) A
            (radAveragedShift E₀ βc Tr κ) lam δ q
          * (R
            * (Real.log y / Real.log z
              * Real.exp (9.0028 / Real.log y + 9.0028 / Real.log z))) ^ q
          * (1 + (1 - q) * Real.sqrt (harperBlockCount D y : ℝ)) ^ (-q)) := by
  haveI := hY.isProbabilityMeasure
  have hq1 : q ≤ 1 := by linarith
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (le_trans hz hzy)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hβ0 : 0 ≤ β := by
    have h1 : (0 : ℝ) ≤ 1 - q := by linarith
    have h2 : (0 : ℝ) ≤ Real.log ((z + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z + 1))
    have : (0 : ℝ) ≤ 2 * (1 - q) * (Real.log ((z + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((z + 1 : ℕ) : ℝ) + 34) := by positivity
    linarith
  obtain ⟨hρb, hρb', hρρ', hρpos⟩ := window_weights hσ hT hβ0
  have hρm' : Measurable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)) :=
    by fun_prop
  have hρ0' : ∀ t : ℝ, 0 ≤ (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)) :=
    fun t => by positivity
  -- the split
  have hsplit := integral_rpow_setIntegral_weight_split_primesIco_le_sharp hY (y₀ := 0)
    (z := z + 1) (y := y + 1) (Nat.zero_le _) (by omega) (σ := σ) (a := T / Real.exp 1)
    (b := T) (q := q) (β := β) (Bd := (σ ^ 2)⁻¹) (Bd' := (σ ^ 2)⁻¹ * Real.exp (β * T ^ 2))
    (ρ := fun t => (σ ^ 2 + t ^ 2)⁻¹)
    (ρ' := fun t => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)))
    hσ.le hq0 hq hβ (by fun_prop) (fun t => by positivity) hρb hρm' hρ0' hρb'
    (fun t ht => le_of_eq (hρρ' t ht)) hρpos
  simp only [randomEulerProductIco_zero] at hsplit
  -- the weighted chaos on the upper block, at `x = y`
  have hρpos' : 0 < ∫ t in Set.Icc (T / Real.exp 1) T,
      (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)) := by
    rw [← setIntegral_congr_fun measurableSet_Icc hρρ']
    haveI : IsFiniteMeasure (volume.restrict (Set.Icc (T / Real.exp 1) T)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
    have hcont : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
      Continuous.inv₀ (by fun_prop) fun t => (by positivity : (0 : ℝ) < σ ^ 2 + t ^ 2).ne'
    refine lt_of_lt_of_le hρpos (setIntegral_mono_on hcont.integrableOn_Icc
      (hcont.mul (by fun_prop)).integrableOn_Icc measurableSet_Icc fun t _ => ?_)
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
  have hfloor : ⌊(y : ℝ)⌋₊ = y := Nat.floor_natCast y
  have hchaos := integral_rpow_block_weight_le_floor E₀ βc hE₀ hE₀1 hβc hβc2 hTr hκ hδ0 hδ hN
    hmono hY (x := (y : ℝ)) (σ := σ) (η := η) (T := T) (q := q) (A := A) (lam := lam)
    (Bd := (σ ^ 2)⁻¹ * Real.exp (β * T ^ 2)) (z := z + 1) (D := D)
    (ρ := fun t => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)))
    hρm' hρ0' hρb' hρpos' (by linarith) hDlog hϑ hϑ104 hσ.le hη0 hηE
    (by rw [abs_of_pos hσ]; exact hσx) hT hT1 hlo hKθ hzb (by rw [hfloor]; omega) hNn hq0 hq1
    hA hAmax hlam
  rw [hfloor] at hchaos
  -- the weight and the mean
  have hW : (∫ t in Set.Icc (T / Real.exp 1) T,
      (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)))
      ≤ R := by
    rw [← setIntegral_congr_fun measurableSet_Icc hρρ']
    exact hR
  have hM := integral_normSq_Ico_shiftLine_le_mertens_ratio hY hz hzy hσ.le 0
  have hW0 : 0 ≤ ∫ t in Set.Icc (T / Real.exp 1) T,
      (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)) :=
    integral_nonneg fun t => hρ0' t
  have hM0 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
      (z + 1) (y + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν := integral_nonneg fun ω => sq_nonneg _
  have hprod := mul_le_mul hW hM hM0 (le_trans hW0 hW)
  have hC0 : 0 ≤ shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ) (radBlockBadConst E₀ βc * Kθ)
      A (radAveragedShift E₀ βc Tr κ) lam δ q := by
    rw [shiftMomentConst]
    exact le_trans (Real.rpow_nonneg (by positivity) _) (le_max_left _ _)
  have h1q : 0 ≤ 1 - q := by linarith
  have hG0 : 0 ≤ (1 + (1 - q) * Real.sqrt (harperBlockCount D y : ℝ)) ^ (-q) :=
    Real.rpow_nonneg (by positivity) _
  have hupper := le_trans hchaos (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (mul_nonneg hW0 hM0) hprod hq0) hC0) hG0)
  refine le_trans hsplit (mul_le_mul_of_nonneg_left hupper ?_)
  exact integral_nonneg fun ω => by positivity

/-! ### The far range -/

/-- **The far range of `Z` by Jensen, explicit.**  For `0 < q ≤ 1`, `y ≥ e^99` and `σ, v > 0`,
`E[((log y)⁻¹∫_{|t|>v}‖F_{y+1}(½+σ+it)/(σ+it)‖²dt)^q] ≤ (2·1.195/v)^q`:
`RMF.exists_integral_rpow_eulerProductLine_tail_le` with Mertens' product
`∏_{p ≤ y}(1 + 1/p) ≤ 1.195 log y` (`RMF.prod_one_add_inv_primesBelow_le`) for its constant. -/
theorem integral_rpow_eulerProductLine_tail_le_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) {y : ℕ}
    (hy : Real.exp 99 ≤ (y : ℝ)) {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|},
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ (2 * 1.195 / T) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := le_trans (by linarith [Real.add_one_le_exp (99 : ℝ)]) hy
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hSmeas : MeasurableSet {t : ℝ | T < |t|} :=
    measurableSet_lt measurable_const (by fun_prop)
  obtain ⟨G, hG⟩ : ∃ G : Ω → ℝ → ℝ, ∀ (ω : Ω) (t : ℝ), G ω t =
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := ⟨_, fun _ _ => rfl⟩
  simp only [← hG]
  -- the weight and its tail
  have hwpos : ∀ t : ℝ, (0 : ℝ) < σ ^ 2 + t ^ 2 := fun t =>
    add_pos_of_pos_of_nonneg (pow_pos hσ 2) (sq_nonneg t)
  have hwmeas : Measurable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ := by fun_prop
  have hwint : Integrable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ := by
    have hcmin : (0 : ℝ) < min (σ ^ 2) 1 := lt_min (pow_pos hσ 2) one_pos
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (min (σ ^ 2) 1)⁻¹)
      hwmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have hb : min (σ ^ 2) 1 * t ^ 2 ≤ 1 * t ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg t)
    have h2 : min (σ ^ 2) 1 * (1 + t ^ 2) ≤ σ ^ 2 + t ^ 2 := by
      have hexp : min (σ ^ 2) 1 * (1 + t ^ 2) = min (σ ^ 2) 1 + min (σ ^ 2) 1 * t ^ 2 := by ring
      rw [hexp]
      linarith [min_le_left (σ ^ 2) 1]
    rw [Real.norm_of_nonneg (inv_nonneg.2 (hwpos t).le), ← mul_inv]
    exact inv_anti₀ (mul_pos hcmin h1) h2
  have hwtail := setIntegral_inv_sq_add_sq_abs_gt_le σ hT
  -- the second moment, the same at every height
  have hsline : ∀ t : ℝ, (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I
      = ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    intro t
    push_cast
    ring
  have hre : ∀ t : ℝ, ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 + σ := by
    intro t
    rw [hsline t]
    simp
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ,
      P = ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (-2 * (1 / 2 + σ))) := ⟨_, rfl⟩
  have hmom : ∀ t : ℝ,
      (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ) = P := by
    intro t
    rw [hRa.integral_norm_randomEulerProduct_sq' (y + 1)
      ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I), hre t, hPdef]
  have hnormsq : ∀ (u : ℂ) (t : ℝ), ‖u / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      = ‖u‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹ := by
    intro u t
    have hd : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = σ ^ 2 + t ^ 2 := by
      have h1 : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
      have h2 : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      rw [Complex.sq_norm, Complex.normSq_apply, h1, h2]
      ring
    rw [norm_div, div_pow, hd, div_eq_mul_inv]
  have hslice : ∀ t : ℝ, (∫ ω, G ω t ∂μ) = P * (σ ^ 2 + t ^ 2)⁻¹ := by
    intro t
    have h1 : (fun ω : Ω => G ω t)
        = fun ω : Ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹ :=
      funext fun ω => by rw [hG ω t, hnormsq]
    rw [h1, integral_mul_const, hmom t]
  have hslice' : ∀ t : ℝ, (∫ ω, ‖G ω t‖ ∂μ) = P * (σ ^ 2 + t ^ 2)⁻¹ := by
    intro t
    have h1 : (fun ω : Ω => ‖G ω t‖) = fun ω : Ω => G ω t :=
      funext fun ω => Real.norm_of_nonneg (by rw [hG ω t]; positivity)
    rw [h1, hslice t]
  -- Tonelli
  have hjm : Measurable (Function.uncurry G) := by
    have huncurry : Measurable fun z : Ω × ℝ =>
        randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (z.2 : ℂ) * Complex.I) z.1 := by
      have h := measurable_randomEulerProduct_sqfree_uncurry (X := X)
        (fun p hp => hX.measurable p hp) (1 / 2 + σ) (y + 1)
      have hcongr : (fun z : Ω × ℝ =>
          randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (z.2 : ℂ) * Complex.I) z.1)
          = fun z : Ω × ℝ =>
            randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (((1 / 2 + σ : ℝ) : ℂ) + (z.2 : ℂ) * Complex.I) z.1 :=
        funext fun z => by rw [hsline z.2]
      rw [hcongr]
      exact h
    have hden : Measurable fun z : Ω × ℝ => (σ : ℂ) + (z.2 : ℂ) * Complex.I :=
      ((Complex.measurable_ofReal.comp measurable_snd).mul_const Complex.I).const_add _
    have hcongr2 : Function.uncurry G
        = fun z : Ω × ℝ =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (z.2 : ℂ) * Complex.I) z.1
            / ((σ : ℂ) + (z.2 : ℂ) * Complex.I)‖ ^ 2 :=
      funext fun z => hG z.1 z.2
    rw [hcongr2]
    exact (huncurry.div hden).norm.pow_const 2
  have hProd : Integrable (Function.uncurry G) (μ.prod (volume.restrict {t : ℝ | T < |t|})) := by
    refine (integrable_prod_iff' hjm.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall fun t => ?_, ?_⟩
    · have h1 : (fun ω : Ω => Function.uncurry G (ω, t))
          = fun ω : Ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹ :=
        funext fun ω => by rw [Function.uncurry_apply_pair, hG ω t, hnormsq]
      rw [h1]
      exact (hRa.integrable_norm_randomEulerProduct_sq (y + 1) _).mul_const _
    · have h2 : (fun t : ℝ => ∫ ω, ‖Function.uncurry G (ω, t)‖ ∂μ)
          = fun t : ℝ => P * (σ ^ 2 + t ^ 2)⁻¹ :=
        funext fun t => by simp only [Function.uncurry_apply_pair]; exact hslice' t
      rw [h2]
      exact (hwint.const_mul P).integrableOn
  -- Mertens: the second moment is at most `1.195 log y`
  have hPle : P ≤ 1.195 * Real.log y := by
    rw [hPdef]
    refine le_trans (Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_)
      (prod_one_add_inv_primesBelow_le hy)
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    have : (p : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ ((p : ℝ))⁻¹ :=
      calc (p : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ (p : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
        _ = ((p : ℝ))⁻¹ := Real.rpow_neg_one _
    linarith
  -- the mean of the far-range functional
  have hZ0 : ∀ ω : Ω, (0 : ℝ) ≤ (Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|}, G ω t :=
    fun ω => mul_nonneg (inv_nonneg.2 hlogy.le)
      (setIntegral_nonneg hSmeas fun t _ => by rw [hG ω t]; positivity)
  have hZi : Integrable (fun ω => (Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|}, G ω t) μ := by
    have h := hProd.integral_prod_left
    simp only [Function.uncurry_apply_pair] at h
    exact h.const_mul _
  have hmean : (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|}, G ω t) ∂μ)
      ≤ 2 * 1.195 / T := by
    rw [integral_const_mul, integral_integral_swap hProd]
    have h1 : (∫ t in {t : ℝ | T < |t|}, ∫ ω, G ω t ∂μ)
        = ∫ t in {t : ℝ | T < |t|}, P * (σ ^ 2 + t ^ 2)⁻¹ :=
      setIntegral_congr_fun hSmeas fun t _ => hslice t
    rw [h1, integral_const_mul]
    have hw0 : (0 : ℝ) ≤ ∫ t in {t : ℝ | T < |t|}, (σ ^ 2 + t ^ 2)⁻¹ :=
      setIntegral_nonneg hSmeas fun t _ => inv_nonneg.2 (hwpos t).le
    have hstep : P * (∫ t in {t : ℝ | T < |t|}, (σ ^ 2 + t ^ 2)⁻¹)
        ≤ 1.195 * Real.log y * (2 / T) :=
      mul_le_mul hPle hwtail hw0 (by positivity)
    calc (Real.log y)⁻¹ * (P * ∫ t in {t : ℝ | T < |t|}, (σ ^ 2 + t ^ 2)⁻¹)
        ≤ (Real.log y)⁻¹ * (1.195 * Real.log y * (2 / T)) :=
          mul_le_mul_of_nonneg_left hstep (inv_nonneg.2 hlogy.le)
      _ = 2 * 1.195 / T := by
          field_simp
  -- Jensen
  have hZqi : Integrable (fun ω => ((Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|}, G ω t) ^ q) μ :=
    integrable_rpow_of_integrable hZi (Filter.Eventually.of_forall hZ0) hq0.le hq1
  refine le_trans (integral_rpow_le_rpow_integral hq0.le hq1
    (Filter.Eventually.of_forall hZ0) hZi hZqi) ?_
  exact Real.rpow_le_rpow (integral_nonneg fun ω => hZ0 ω) hmean hq0.le

/-! ### Three ranges -/

/-- **`Z` from three ranges**: the central window `|t| ≤ w`, the mesoscopic range `w < |t| ≤ v`
and the far range `|t| > v`, for `w ≤ v`.  `RMF.integral_rpow_lineDiv_le_of_three_ranges` for the
Euler product, which is jointly measurable (`RMF.measurable_randomEulerProduct_sqfree_uncurry`) and
bounded by its envelope. -/
theorem integral_rpow_eulerLineDiv_le_of_three_ranges {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {σ q w v : ℝ} {y : ℕ} {B₁ B₂ B₃ : ℝ}
    (hy2 : 2 ≤ y) (hσ0 : 0 < σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hwv : w ≤ v)
    (hb1 : (∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Icc (-w) w,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν) ≤ B₁)
    (hb2 : (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | w < |t| ∧ |t| ≤ v},
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν) ≤ B₂)
    (hb3 : (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | v < |t|},
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν) ≤ B₃) :
    (∫ ω, ((Real.log y)⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
      ≤ B₁ + B₂ + B₃ := by
  haveI := hY.isProbabilityMeasure
  have hy2' : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hsline : ∀ t : ℝ, (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I
      = ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    intro t
    push_cast
    ring
  have hF : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω) := by
    have h := measurable_randomEulerProduct_sqfree_uncurry (X := Y)
      (fun p hp => hY.measurable p hp) (1 / 2 + σ) (y + 1)
    have hcongr : (Function.uncurry fun (ω : Ω) (t : ℝ) =>
        randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
        = fun z : Ω × ℝ => randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (y + 1) (((1 / 2 + σ : ℝ) : ℂ) + (z.2 : ℂ) * Complex.I) z.1 :=
      funext fun z => by
        simp only [Function.uncurry]
        rw [hsline z.2]
    rw [hcongr]
    exact h
  have hU : ∀ᵐ ω ∂ν, ∀ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖
        ≤ ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (-(1 / 2 + σ))) := by
    filter_upwards [ae_forall_norm_randomEulerProduct_mem_Icc hY (y + 1) (c := 1 / 2 + σ)
      (by linarith)] with ω hω
    intro t
    exact (hω _ (by rw [hsline t]; simp)).2
  exact integral_rpow_lineDiv_le_of_three_ranges (μ := ν) hσ0 hlogy hq0 hq1 hwv hF hU hb1 hb2 hb3

end RMF
