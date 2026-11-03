/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.BlockSplitAboveHalfExplicit
import RMF.Weighted.BlockFamilyExplicit

/-!
# The windows of a band, for `q ≤ 1`

The band twins of the window lemmas of `Weighted/BlockFamilyExplicit.lean`, at any `q ≤ 1`.

* the windows' moments dominate the range's moment
  (`RMF.integral_rpow_setIntegral_weight_le_sum_windows_inside_Ico`);
* one window by the split at `z₁` and Jensen on the upper block
  (`RMF.integral_rpow_window_band_le_split_jensen_of_weight`), the split being the sharp one for
  `q ≤ 1` (`RMF.integral_rpow_setIntegral_weight_split_primesIco_le_sharp_of_le_one`);
* the mesoscopic range as a sum of windows (`RMF.integral_rpow_mesoRange_band_le_sum_windows`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A band's window moments dominate its range's moment**, the weight kept inside: the band
twin of `RMF.integral_rpow_setIntegral_weight_le_sum_windows_inside`, whose proof reads the full
product as the band `[0, n)`. -/
theorem integral_rpow_setIntegral_weight_le_sum_windows_inside_Ico {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) (y₀ n : ℕ) {σ q : ℝ} (hσ : 0 ≤ σ)
    (hq0 : 0 < q) (hq1 : q ≤ 1) {ι : Type*} (I : Finset ι) (a b : ι → ℝ) {A B Bρ : ℝ}
    {ρ : ℝ → ℝ} {S : Set ℝ} (hρ0 : ∀ t, 0 ≤ ρ t) (hρm : Measurable ρ) (hρb : ∀ t, ρ t ≤ Bρ)
    (hS : MeasurableSet S) (hSAB : S ⊆ Set.Icc A B)
    (hIAB : ∀ i ∈ I, Set.Ioc (a i) (b i) ⊆ Set.Icc A B)
    (hcov : ∀ t ∈ S, ∃ i ∈ I, t ∈ Set.Ioc (a i) (b i)) :
    (∫ ω, (∫ t in S, ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          y₀ n (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ ∑ i ∈ I, ∫ ω, (∫ t in Set.Icc (a i) (b i), ρ t *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ n
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hSnn : ∀ ω : Ω, (0 : ℝ) ≤ ∫ t in S, ρ t *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ n
        (shiftLine σ t) ω‖ ^ 2 :=
    fun ω => integral_nonneg fun t => mul_nonneg (hρ0 t) (sq_nonneg _)
  have hYnn : ∀ (i : ι) (ω : Ω), (0 : ℝ) ≤ ∫ t in Set.Icc (a i) (b i), ρ t *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ n
        (shiftLine σ t) ω‖ ^ 2 :=
    fun i ω => integral_nonneg fun t => mul_nonneg (hρ0 t) (sq_nonneg _)
  have hYint : ∀ i ∈ I, Integrable (fun ω => (∫ t in Set.Icc (a i) (b i), ρ t *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ n
        (shiftLine σ t) ω‖ ^ 2) ^ q) μ := by
    intro i _
    have hvol : volume (Set.Icc (a i) (b i)) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hsl := integrable_uncurry_weight_normSq_primesIco hX y₀ n hσ hvol hρm hρ0 hρb
    have hbd := ae_setIntegral_weight_normSq_primesIco_mem_Icc hX y₀ n (a := a i) (b := b i) hσ
      hρm hρ0 hρb
    refine (memLp_top_of_bound
      ((Real.continuous_rpow_const hq0.le).comp_aestronglyMeasurable hsl.integral_prod_left.1)
      (((∫ t in Set.Icc (a i) (b i), ρ t)
        * (∏ p ∈ primesIco y₀ n, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2) ^ q) ?_).integrable le_top
    filter_upwards [hbd] with ω hω
    simp only [Function.uncurry_apply_pair]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hYnn i ω) _)]
    exact Real.rpow_le_rpow (hYnn i ω) hω.2 hq0.le
  have hRint : Integrable (fun ω => ∑ i ∈ I, (∫ t in Set.Icc (a i) (b i), ρ t *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ n
        (shiftLine σ t) ω‖ ^ 2) ^ q) μ :=
    integrable_finsetSum _ fun i hi => hYint i hi
  have hvolAB : volume (Set.Icc A B) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hslAB := integrable_uncurry_weight_normSq_primesIco hX y₀ n hσ hvolAB hρm hρ0 hρb
  have hstep : ∀ᵐ ω ∂μ, (∫ t in S, ρ t *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ n
          (shiftLine σ t) ω‖ ^ 2) ^ q
      ≤ ∑ i ∈ I, (∫ t in Set.Icc (a i) (b i), ρ t *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ n
            (shiftLine σ t) ω‖ ^ 2) ^ q := by
    filter_upwards [hslAB.prod_right_ae] with ω hint0
    have hint : IntegrableOn (fun t => ρ t * ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) y₀ n (shiftLine σ t) ω‖ ^ 2)
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

/-- **One window of a band by the split and Jensen, for `q ≤ 1`.**  For a band `[y₀, y)` split at
`y₀ ≤ z₁ ≤ y`, `σ > 0`, `0 ≤ q ≤ 1`, `T > 0`, `β ≥ 2(1-q)S₂(z₁)`, a bound `R` on the window's weight
`∫_{T/e}^{T}e^{βt²}dt/(σ²+t²)` and a bound `M` on the upper block's mean `E‖F_{[z₁,y)}(½+σ)‖²`:

`E[(∫_{T/e}^{T}(σ²+t²)⁻¹‖F_{[y₀,y)}(½+σ+it)‖²dt)^q] ≤ E‖F_{[y₀,z₁)}(½+σ)‖^{2q}·(RM)^q`.

`RMF.integral_rpow_window_le_split_jensen_of_weight` with the band's lower block, the split at any
`q ≤ 1` (`RMF.integral_rpow_setIntegral_weight_split_primesIco_le_sharp_of_le_one`) and the upper
mean left to the caller; `z₁ = y` (no upper block, `M = 1`) is allowed. -/
theorem integral_rpow_window_band_le_split_jensen_of_weight {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {y₀ z₁ y : ℕ} (hy₀z₁ : y₀ ≤ z₁) (hz₁y : z₁ ≤ y)
    {σ q T β R M : ℝ} (hσ : 0 < σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hT : 0 < T)
    (hβ0 : 0 ≤ β)
    (hβ : 2 * (1 - q) * (Real.log z₁ ^ 2 / 2 + 15.003 * Real.log z₁ + 34) ≤ β)
    (hR : (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2)) ≤ R)
    (hM : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z₁ y
        (shiftLine σ 0) ω‖ ^ 2 ∂ν) ≤ M) :
    (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ z₁
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂ν) * (R * M) ^ q := by
  haveI := hY.isProbabilityMeasure
  obtain ⟨hρb, hρb', hρρ', hρpos⟩ := window_weights hσ hT hβ0
  have hvol : volume (Set.Icc (T / Real.exp 1) T) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hρm' : Measurable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)) :=
    by fun_prop
  have hρ0' : ∀ t : ℝ, 0 ≤ (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)) :=
    fun t => by positivity
  -- the split
  have hsplit := integral_rpow_setIntegral_weight_split_primesIco_le_sharp_of_le_one hY
    (y₀ := y₀) (z := z₁) (y := y) hy₀z₁ hz₁y (σ := σ) (a := T / Real.exp 1)
    (b := T) (q := q) (β := β) (Bd := (σ ^ 2)⁻¹) (Bd' := (σ ^ 2)⁻¹ * Real.exp (β * T ^ 2))
    (ρ := fun t => (σ ^ 2 + t ^ 2)⁻¹)
    (ρ' := fun t => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)))
    hσ.le hq0 hq1 hβ (by fun_prop) (fun t => by positivity) hρb hρm' hρ0' hρb'
    (fun t ht => le_of_eq (hρρ' t ht)) hρpos
  -- Jensen on the upper block
  set S : Ω → ℝ := fun ω => ∫ t in Set.Icc (T / Real.exp 1) T,
    (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2))
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z₁ y
        (shiftLine σ t) ω‖ ^ 2 with hSdef
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => integral_nonneg fun t => mul_nonneg (hρ0' t) (sq_nonneg _)
  have hSi : Integrable S ν :=
    (integrable_uncurry_weight_normSq_primesIco hY z₁ y hσ.le hvol hρm' hρ0'
      hρb').integral_prod_left
  have hSqi : Integrable (fun ω => S ω ^ q) ν :=
    integrable_rpow_of_integrable hSi (Filter.Eventually.of_forall hS0) hq0 hq1
  have hjen : (∫ ω, S ω ^ q ∂ν) ≤ (∫ ω, S ω ∂ν) ^ q :=
    integral_rpow_le_rpow_integral hq0 hq1 (Filter.Eventually.of_forall hS0) hSi hSqi
  have hmean := integral_setIntegral_weight_normSq_Ico_le hY z₁ y (a := T / Real.exp 1)
    (b := T) hσ.le hρm' hρ0' hρb'
  have hW : (∫ t in Set.Icc (T / Real.exp 1) T,
      (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)))
      ≤ R := by
    rw [← setIntegral_congr_fun measurableSet_Icc hρρ']
    exact hR
  have hW0 : 0 ≤ ∫ t in Set.Icc (T / Real.exp 1) T,
      (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * min (t ^ 2) (T ^ 2)) :=
    integral_nonneg fun t => hρ0' t
  have hM0 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
      z₁ y (shiftLine σ 0) ω‖ ^ 2 ∂ν := integral_nonneg fun ω => sq_nonneg _
  have hprod := mul_le_mul hW hM hM0 (le_trans hW0 hW)
  have hES0 : 0 ≤ ∫ ω, S ω ∂ν := integral_nonneg hS0
  have hupper : (∫ ω, S ω ^ q ∂ν) ≤ (R * M) ^ q :=
    le_trans hjen (Real.rpow_le_rpow hES0 (le_trans hmean hprod) hq0)
  refine le_trans hsplit (mul_le_mul_of_nonneg_left hupper ?_)
  exact integral_nonneg fun ω => by positivity

/-- **A band's mesoscopic range as a sum of windows**, the weight kept inside.  For `σ > 0`,
`0 < q ≤ 1`, `L > 0`, a real `c` and `k₀ ≤ J`, with windows `(e^{c-k-1}, e^{c-k}]`:

`E[(L⁻¹∫_{e^{c-J}<|t|≤e^{c-k₀}}‖F(½+σ+it)/(σ+it)‖²dt)^q]
  ≤ (2/L)^q·∑_{k₀≤k<J} E[(∫_{e^{c-k}/e}^{e^{c-k}}(σ²+t²)⁻¹‖F(½+σ+it)‖²dt)^q]`,

`F` the product over a band `[y₀, y)`: the fold `t ↦ -t`
(`RMF.ae_setIntegral_weight_normSq_symm_primesIco`) and the windows
(`RMF.integral_rpow_setIntegral_weight_le_sum_windows_inside_Ico`). -/
theorem integral_rpow_mesoRange_band_le_sum_windows {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) (y₀ y : ℕ) {σ q L c : ℝ} {k₀ J : ℕ} (hσ : 0 < σ)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hL : 0 < L) (hk₀J : k₀ ≤ J) :
    (∫ ω, (L⁻¹ * ∫ t in {t : ℝ | Real.exp (c - J) < |t| ∧ |t| ≤ Real.exp (c - k₀)},
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
      ≤ (2 / L) ^ q * ∑ k ∈ Finset.Ico k₀ J,
          ∫ ω, (∫ t in Set.Icc (Real.exp (c - k) / Real.exp 1) (Real.exp (c - k)),
            (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
              (fun ω => squarefreeExtension fun p => Y p ω) y₀ y (shiftLine σ t) ω‖ ^ 2) ^ q
            ∂ν := by
  haveI := hY.isProbabilityMeasure
  have hint : ∀ (ω : Ω) (t : ℝ),
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        = (σ ^ 2 + t ^ 2)⁻¹
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y
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
  have hk₀1 : Real.exp (c - J) ≤ Real.exp (c - k₀) := Real.exp_le_exp.2 (by linarith)
  have hfold := ae_setIntegral_weight_normSq_symm_primesIco hY y₀ y (σ := σ) (by linarith)
    (ρ := fun t => (σ ^ 2 + t ^ 2)⁻¹) (Bρ := (σ ^ 2)⁻¹) (fun t => by norm_num)
    (by fun_prop) (fun t => by positivity) hρb (Real.exp_pos _).le hk₀1
  have hcongr : (∫ ω, (L⁻¹ * ∫ t in {t : ℝ | Real.exp (c - J) < |t|
          ∧ |t| ≤ Real.exp (c - k₀)},
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
          y₀ y (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      = ∫ ω, (2 / L) ^ q * (∫ t in Set.Ioc (Real.exp (c - J)) (Real.exp (c - k₀)),
          (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => Y p ω) y₀ y (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hfold] with ω hω
    rw [hω, ← Real.mul_rpow (by positivity) (integral_nonneg fun t => by positivity)]
    congr 1
    ring
  rw [hcongr, integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
  refine integral_rpow_setIntegral_weight_le_sum_windows_inside_Ico hY y₀ y hσ.le hq0 hq1
    (Finset.Ico k₀ J) (fun k => Real.exp (c - k) / Real.exp 1)
    (fun k => Real.exp (c - k)) (A := 0) (B := Real.exp (c - k₀)) (fun t => by positivity)
    (by fun_prop) hρb measurableSet_Ioc ?_ ?_ ?_
  · intro t ht
    exact ⟨le_trans (Real.exp_pos _).le ht.1.le, ht.2⟩
  · intro k hk t ht
    have hk' : (k₀ : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.1 hk).1
    exact ⟨le_trans (by positivity) ht.1.le,
      le_trans ht.2 (Real.exp_le_exp.2 (by linarith))⟩
  · intro t ht
    have ht0 : 0 < t := lt_trans (Real.exp_pos _) ht.1
    have hlo : c - J < Real.log t := by
      have := Real.log_lt_log (Real.exp_pos _) ht.1
      rwa [Real.log_exp] at this
    have hhi : Real.log t ≤ c - k₀ := by
      have := Real.log_le_log ht0 ht.2
      rwa [Real.log_exp] at this
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = c - Real.log t := ⟨_, rfl⟩
    have hu0 : 0 ≤ u := by
      have : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg _
      linarith
    have hfl1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu0
    have hfl2 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
    have htu : t = Real.exp (c - u) := by rw [hu, sub_sub_cancel, Real.exp_log ht0]
    refine ⟨⌊u⌋₊, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      constructor
      · exact Nat.le_floor (by linarith)
      · have h2 : (⌊u⌋₊ : ℝ) < J := by linarith
        exact_mod_cast h2
    · constructor
      · change Real.exp (c - ((⌊u⌋₊ : ℕ) : ℝ)) / Real.exp 1 < t
        rw [htu, ← Real.exp_sub]
        exact Real.exp_lt_exp.2 (by linarith)
      · change t ≤ Real.exp (c - ((⌊u⌋₊ : ℕ) : ℝ))
        rw [htu]
        exact Real.exp_le_exp.2 (by linarith)

end RMF
