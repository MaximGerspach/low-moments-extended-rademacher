/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.BlockChaosExplicit
import RMF.Probability.RademacherBarrierFloor

/-!
# The mesoscopic block chaos with a weight in the height

The block family of `Z_m` meets each block through `∫_{T/e}^{T}ρ(h)‖F(½+σ+ih)‖²dh` with
`ρ(h) = e^{βh²}/(σ² + h²)`: the weight of `Z`, times the two-point ratio of the split.  The
weight rides through the level-shift interpolation: the process is normalised by its exact mean
`(∫ρ)·M₀`, the restricted chaos at each height is weighted by `ρ(h)`, and the bad sets do not
see it.

The bad sets are the level-floor-`16Δ` ones (`RMF.measureReal_not_mesoGood_le_rademacher_floor`),
so the levels start at `RMF.radBlockBadLevel E₀` rather than `RMF.harperBadLevel E₀ = 32Δ`
(`RMF.integral_rpow_block_weight_le_floor`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### A weight in the height -/

/-- **The per-height bound, integrated against a weight**: if at each height `t ∈ W` the
restricted integral is at most `k(t)`, then the double integral is at most `∫_W k`.  The weighted
twin of `RMF.integral_setIntegral_indicator_le_of_per_height`. -/
theorem integral_setIntegral_indicator_le_of_per_height_weight {ν : Measure Ω} [SFinite ν]
    {L : ℝ → Set Ω} {g : ℝ → Ω → ℝ} {W : Set ℝ} (hW : MeasurableSet W) {k : ℝ → ℝ}
    (hInt : Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) => Set.indicator (L t) (g t) ω)
      (ν.prod (volume.restrict W)))
    (hk : IntegrableOn k W) (hper : ∀ t ∈ W, (∫ ω, Set.indicator (L t) (g t) ω ∂ν) ≤ k t) :
    (∫ ω, (∫ t in W, Set.indicator (L t) (g t) ω) ∂ν) ≤ ∫ t in W, k t := by
  rw [integral_integral_swap hInt]
  exact setIntegral_mono_on hInt.integral_prod_right hk hW hper

/-- A bounded measurable weight keeps the uncurried restricted integrand product-integrable. -/
lemma integrable_uncurry_weight_indicator_normSq_primesIco {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z y : ℕ) {σ : ℝ} (hσ : 0 < 1 / 2 + σ) {I : Set ℝ}
    (hI : volume I ≠ ⊤) (S : ℝ → Set Ω) (hS : MeasurableSet {p : Ω × ℝ | p.1 ∈ S p.2})
    {ρ : ℝ → ℝ} {Bd : ℝ} (hρm : Measurable ρ) (hρ0 : ∀ h, 0 ≤ ρ h) (hρb : ∀ h, ρ h ≤ Bd) :
    Integrable (Function.uncurry fun (ω : Ω) (h : ℝ) => Set.indicator (S h)
        (fun ω => ρ h * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ h) ω‖ ^ 2) ω)
      (μ.prod (volume.restrict I)) := by
  have hbase := integrable_uncurry_indicator_normSq_primesIco_signed hX z y hσ hI S hS
  have heq : (Function.uncurry fun (ω : Ω) (h : ℝ) => Set.indicator (S h)
        (fun ω => ρ h * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ h) ω‖ ^ 2) ω)
      = fun w : Ω × ℝ => ρ w.2 * (Function.uncurry fun (ω : Ω) (h : ℝ) => Set.indicator (S h)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ h) ω‖ ^ 2) ω) w := by
    funext w
    simp only [Function.uncurry]
    by_cases hw : w.1 ∈ S w.2
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, mul_zero]
  rw [heq]
  refine hbase.bdd_mul (c := Bd) (hρm.comp measurable_snd).aestronglyMeasurable ?_
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 _)]
  exact hρb _

/-- **The weighted window integral's mean**: `E∫_{[a,b]}ρ(h)‖F_{[z,y)}(½+σ+ih)‖²dh ≤ (∫ρ)·M₀`. -/
lemma integral_setIntegral_weight_normSq_Ico_le {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) (z y : ℕ) {σ a b : ℝ} (hσ : 0 ≤ σ) {ρ : ℝ → ℝ}
    {Bd : ℝ} (hρm : Measurable ρ) (hρ0 : ∀ h, 0 ≤ ρ h) (hρb : ∀ h, ρ h ≤ Bd) :
    (∫ ω, (∫ h in Set.Icc a b, ρ h *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z y
          (shiftLine σ h) ω‖ ^ 2) ∂ν)
      ≤ (∫ h in Set.Icc a b, ρ h) * ∫ ω, ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => Y p ω) z y (shiftLine σ 0) ω‖ ^ 2 ∂ν := by
  haveI := hY.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hvolfin : volume (Set.Icc a b) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  set M₀ : ℝ := ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z y
    (shiftLine σ 0) ω‖ ^ 2 ∂ν with hM₀
  have hInt := integrable_uncurry_weight_indicator_normSq_primesIco hY z y (σ := σ)
    (by linarith) hvolfin (fun _ => (Set.univ : Set Ω))
    (by simp only [Set.mem_univ, Set.setOf_true]; exact MeasurableSet.univ) hρm hρ0 hρb
  have hρint : IntegrableOn ρ (Set.Icc a b) := by
    refine (memLp_top_of_bound hρm.aestronglyMeasurable Bd ?_).integrable le_top
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
    exact hρb t
  have h := integral_setIntegral_indicator_le_of_per_height_weight
    (L := fun _ => (Set.univ : Set Ω))
    (g := fun (t : ℝ) ω => ρ t * ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => Y p ω) z y (shiftLine σ t) ω‖ ^ 2)
    (k := fun t => ρ t * M₀) measurableSet_Icc hInt (hρint.mul_const M₀) (fun t _ => by
      simp only [Set.indicator_univ]
      rw [integral_const_mul]
      exact le_of_eq (congrArg (fun u => ρ t * u) (integral_normSq_Ico_shiftLine_eq hY z y σ t 0)))
  simp only [Set.indicator_univ] at h
  rwa [integral_mul_const] at h

/-! ### The weighted interpolation -/

set_option maxHeartbeats 800000 in
-- the level-shift interpolation with the weight carried through every restricted integral
/-- **The block chaos with a weight in the height, from its bad sets, at any height.**  For a
bounded measurable weight `ρ ≥ 0` with `∫ρ > 0`, bad sets of measure at most `C_b e^{-2a}` from
the level `A₀` on, and the height condition of the chaos's cosine input at the floor `ϑ`,
`(2T + 1)·pntFloorConst ϑ ≤ e^{-2E₀}/200`:

`E[(∫_{T/e}^{T}ρ(h)‖F_{[z,x]}(½+σ+ih)‖²dh)^q]
  ≤ shiftMomentConst 1 C_i C_b A s λ δ q·((∫ρ)·M₀)^q·(1 + (1-q)√n)^{-q}`,

`C_i = radAveragedConst E₀ β Tr κ`, `s = radAveragedShift E₀ β Tr κ`, `M₀ = E‖F_{[z,x]}(½+σ)‖²`,
`n = harperBlockCount D x`.  At `ϑ ≥ 104` the height condition holds once
`2T + 1 ≤ 5·10²⁵e^{-2E₀}` (`RMF.height_floor_of_height`). -/
theorem integral_rpow_block_weight_le_of_bad_of_height (E₀ β : ℝ) (hE₀ : 0 ≤ E₀)
    (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) {Tr κ Cb A₀ Amax δ : ℝ} {N : ℕ} (hTr : 4 < Tr) (hκ : 1 ≤ κ)
    (hCb : 0 < Cb) (hA₀ : 1 ≤ A₀) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δ * N)
    (hmono : 3 ≤ 8 * δ * Real.sqrt (N : ℝ))
    {Y : ℕ → Ω → ℂ} {ν : Measure Ω} (hY : IsRademacherPrimeValues Y ν)
    {x σ η T q A lam Bd : ℝ} {z D : ℕ} {ρ : ℝ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ h, 0 ≤ ρ h) (hρb : ∀ h, ρ h ≤ Bd)
    (hρpos : 0 < ∫ h in Set.Icc (T / Real.exp 1) T, ρ h)
    (hx1 : 1 < x) (hDlog : (D : ℝ) ≤ Real.log (Real.log x))
    (hϑ : radFreeStartThreshold E₀ ≤ harperOffset D x) (hϑ104 : (104 : ℝ) ≤ harperOffset D x)
    (hσ0 : 0 ≤ σ) (hη0 : 0 ≤ η) (hηE : η ≤ E₀) (hσx : |σ| * Real.log x ≤ η)
    (hT0 : 0 < T)
    (hhT : (2 * T + 1) * pntFloorConst (harperOffset D x) ≤ Real.exp (-(2 * E₀)) / 200)
    (hlo : 600 * Real.exp (2 * E₀) ≤ 2 * (T / Real.exp 1) * Real.exp (harperOffset D x))
    (hzb : (z : ℝ) ≤ blockScale (harperOffset D x) 0) (hzn : z ≤ ⌊x⌋₊ + 1)
    (hNn : N ≤ harperBlockCount D x)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hA : A₀ ≤ A) (hAmax : A ≤ Amax) (hlam : 1 ≤ lam)
    (hbad : ∀ a, A₀ ≤ a → ν.real {ω | ∃ h ∈ Set.Icc (T / Real.exp 1) T,
        ω ∉ mesoGood Y (harperOffset D x) prop5UpperSlope (harperBlockCount D x) ⌈a / 4⌉₊ a
          (fun j => β * Real.log j) (shiftLine σ h)} ≤ Cb * Real.exp (-(2 * a))) :
    (∫ ω, (∫ h in Set.Icc (T / Real.exp 1) T, ρ h *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1)
          (shiftLine σ h) ω‖ ^ 2) ^ q ∂ν)
      ≤ shiftMomentConst 1 (radAveragedConst E₀ β Tr κ) Cb A (radAveragedShift E₀ β Tr κ) lam
          δ q
        * ((∫ h in Set.Icc (T / Real.exp 1) T, ρ h) * ∫ ω, ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2
            ∂ν) ^ q
        * (1 + (1 - q) * Real.sqrt (harperBlockCount D x : ℝ)) ^ (-q) := by
  classical
  haveI := hY.isProbabilityMeasure
  set ϑ := harperOffset D x with hϑdef
  set n := harperBlockCount D x with hndef
  set Ci := radAveragedConst E₀ β Tr κ with hCidef
  set si := radAveragedShift E₀ β Tr κ with hsidef
  have hCi1 : 1 ≤ Ci := one_le_radAveragedConst hE₀ hβ0 hβ2 hTr hκ
  have hsi0 : 0 ≤ si := radAveragedShift_nonneg hE₀ hβ0 hβ2 hTr hκ
  have he1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hTe0 : (0 : ℝ) < T / Real.exp 1 := div_pos hT0 (Real.exp_pos 1)
  have hvolfin : volume (Set.Icc (T / Real.exp 1) T) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (T / Real.exp 1) T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hvolfin⟩
  have hρint : IntegrableOn ρ (Set.Icc (T / Real.exp 1) T) := by
    refine (memLp_top_of_bound hρm.aestronglyMeasurable Bd ?_).integrable le_top
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
    exact hρb t
  set Wρ : ℝ := ∫ h in Set.Icc (T / Real.exp 1) T, ρ h with hWρdef
  -- the normalising constant
  set M₀ : ℝ := ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z
    (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν with hM₀def
  have hM₀ : 0 < M₀ := integral_normSq_Ico_pos hY z (⌊x⌋₊ + 1) hσ0 (re_shiftLine σ 0)
  set M : ℝ := Wρ * M₀ with hMdef
  have hM0 : 0 < M := mul_pos hρpos hM₀
  set Zf : Ω → ℝ := fun ω => M⁻¹ * ∫ h in Set.Icc (T / Real.exp 1) T, ρ h *
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1)
      (shiftLine σ h) ω‖ ^ 2 with hZfdef
  set Rf : (ℝ → Set Ω) → Ω → ℝ := fun S ω => M⁻¹ * ∫ h in Set.Icc (T / Real.exp 1) T,
    Set.indicator (S h) (fun ω => ρ h * ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2) ω
    with hRfdef
  set Gset : ℝ → ℝ → Set Ω := fun a h =>
    mesoGood Y ϑ prop5UpperSlope n ⌈a / 4⌉₊ a (fun j => β * Real.log j) (shiftLine σ h)
    with hGsetdef
  have hZ0 : ∀ ω, 0 ≤ Zf ω := fun ω =>
    mul_nonneg (by positivity) (integral_nonneg fun h => mul_nonneg (hρ0 h) (sq_nonneg _))
  have hR0 : ∀ (S : ℝ → Set Ω) (ω : Ω), 0 ≤ Rf S ω := fun S ω =>
    mul_nonneg (by positivity)
      (integral_nonneg fun h => Set.indicator_nonneg (fun _ _ =>
        mul_nonneg (hρ0 h) (sq_nonneg _)) ω)
  have hZi : Integrable Zf ν := by
    have h := (integrable_uncurry_weight_indicator_normSq_primesIco hY z (⌊x⌋₊ + 1) (σ := σ)
      (by linarith) hvolfin (fun _ => (Set.univ : Set Ω))
      (by simp only [Set.mem_univ, Set.setOf_true]; exact MeasurableSet.univ)
      hρm hρ0 hρb).integral_prod_left
    simp only [Set.indicator_univ] at h
    exact h.const_mul _
  have hRi : ∀ S : ℝ → Set Ω, (∀ h, MeasurableSet (S h)) →
      MeasurableSet {p : Ω × ℝ | p.1 ∈ S p.2} → Integrable (Rf S) ν := fun S _ hS =>
    ((integrable_uncurry_weight_indicator_normSq_primesIco hY z (⌊x⌋₊ + 1) (σ := σ)
      (by linarith) hvolfin S hS hρm hρ0 hρb).integral_prod_left).const_mul _
  have hdec : ∀ (S : ℕ → ℝ → Set Ω) (ω : Ω) (r m : ℕ), r ≤ m →
      Zf ω ≤ Rf (S r) ω
        + (∑ j ∈ Finset.Ico r m,
            Set.indicator {ω | ∃ h ∈ Set.Icc (T / Real.exp 1) T, ω ∉ S j h}
              (fun _ => (1 : ℝ)) ω * Rf (S (j + 1)) ω)
        + Set.indicator {ω | ∃ h ∈ Set.Icc (T / Real.exp 1) T, ω ∉ S m h}
            (fun _ => (1 : ℝ)) ω * Zf ω := fun S ω r m hrm =>
    setIntegral_le_decomposition (fun h _ => mul_nonneg (hρ0 h) (sq_nonneg _)) measurableSet_Icc
      (inv_nonneg.2 hM0.le) S ω r m hrm
  -- `E Z ≤ 1`
  have hZmean : (∫ ω, Zf ω ∂ν) ≤ 1 := by
    have h := integral_setIntegral_weight_normSq_Ico_le hY z (⌊x⌋₊ + 1)
      (a := T / Real.exp 1) (b := T) hσ0 hρm hρ0 hρb
    rw [hZfdef, integral_const_mul, inv_mul_le_iff₀ hM0, mul_one]
    exact h
  -- the good family
  have hGmeas : ∀ a h, MeasurableSet (Gset a h) := fun a h =>
    measurableSet_mesoGood hY _ _ _ _ _ _ _
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) := fun p =>
    hY.measurable ((p : Nat.Primes) : ℕ) p.2
  have hGunc : ∀ a : ℝ, MeasurableSet {p : Ω × ℝ | p.1 ∈ Gset a p.2} := fun a =>
    measurableSet_freeStartBarrierAdd_uncurry hYm σ ϑ ⌈a / 4⌉₊ n
      (fun j => -a - prop5UpperSlope * (j : ℝ)) (fun j => a + (j : ℝ) + β * Real.log j)
  have hGint : ∀ a : ℝ, A₀ ≤ a → 2 * ⌈a / 4⌉₊ ≤ n → 0 ≤ n - ⌈a / 4⌉₊ →
      (∫ ω, Rf (Gset a) ω ∂ν) ≤ Ci * min 1 ((a + si) / Real.sqrt ((n : ℝ) - ⌈a / 4⌉₊)) := by
    intro a ha h2r _
    have ha1 : (1 : ℝ) ≤ a := le_trans hA₀ ha
    have hrn : ⌈a / 4⌉₊ < n := by
      have hr1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
      omega
    set Kc : ℝ := Ci * min 1 ((a + si) / Real.sqrt ((n : ℝ) - ⌈a / 4⌉₊)) * M₀ with hKc
    have hper : ∀ h ∈ Set.Icc (T / Real.exp 1) T,
        (∫ ω, Set.indicator (Gset a h) (fun ω => ρ h * ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1)
              (shiftLine σ h) ω‖ ^ 2) ω ∂ν)
          ≤ ρ h * Kc := by
      intro h hh
      have hh0 : (0 : ℝ) < h := lt_of_lt_of_le hTe0 hh.1
      have him : |(shiftLine σ h).im| = h := by rw [im_shiftLine, abs_of_pos hh0]
      have hlo' : 600 * Real.exp (2 * E₀) ≤ 2 * |(shiftLine σ h).im| * Real.exp ϑ := by
        rw [him]
        refine le_trans hlo (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
        linarith [hh.1]
      have hhi' : (2 * |(shiftLine σ h).im| + 1) * pntFloorConst ϑ
          ≤ Real.exp (-(2 * E₀)) / 200 := by
        rw [him]
        exact le_trans (mul_le_mul_of_nonneg_right (by linarith [hh.2]) (pntFloorConst_nonneg ϑ))
          hhT
      have hI := setIntegral_mesoGood_normSq_Ico_le_radAveraged_of_floor E₀ β hE₀ hβ0 hβ2 hTr hκ
        hY (s := shiftLine σ h) hx1 hDlog hϑ hϑ104 (re_shiftLine σ h) hσ0 hη0 hηE hσx hlo' hhi'
        hzb hzn ha1 hrn
      have hind : (fun ω => Set.indicator (Gset a h) (fun ω => ρ h * ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1)
              (shiftLine σ h) ω‖ ^ 2) ω)
          = fun ω => ρ h * Set.indicator (Gset a h) (fun ω => ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1)
              (shiftLine σ h) ω‖ ^ 2) ω := by
        funext ω
        by_cases hω : ω ∈ Gset a h
        · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, mul_zero]
      rw [hind, integral_const_mul, integral_indicator (hGmeas a h)]
      refine mul_le_mul_of_nonneg_left (le_trans hI (le_of_eq ?_)) (hρ0 h)
      exact congrArg (fun u => Ci * min 1 ((a + si) / Real.sqrt ((n : ℝ) - ⌈a / 4⌉₊)) * u)
        (integral_normSq_Ico_shiftLine_eq hY z (⌊x⌋₊ + 1) σ h 0)
    have hInt := integrable_uncurry_weight_indicator_normSq_primesIco hY z (⌊x⌋₊ + 1)
      (σ := σ) (by linarith) hvolfin (Gset a) (hGunc a) hρm hρ0 hρb
    have h := integral_setIntegral_indicator_le_of_per_height_weight measurableSet_Icc hInt
      (hρint.mul_const Kc) hper
    rw [integral_mul_const] at h
    rw [hRfdef, integral_const_mul, inv_mul_le_iff₀ hM0]
    refine le_trans h (le_of_eq ?_)
    rw [hMdef, hKc]
    ring
  -- the room for the levels
  have hroom : A / 4 + 3 * Real.sqrt (n : ℝ) / 4 + 1 + ((0 : ℕ) : ℝ) ≤ δ * (n : ℝ) := by
    rw [Nat.cast_zero, add_zero]
    exact free_start_room_of_le hδ0.le hAmax (Nat.cast_nonneg _) hN hmono
      (by exact_mod_cast hNn)
  have hmain := integral_rpow_le_of_goodSets_shift (ν := ν) (Z := Zf) (Rst := Rf)
    (win := Set.Icc (T / Real.exp 1) T) (q := q) (t := n) (n₀ := 0) (a₀ := A₀)
    (C₁ := 1) (Ci := Ci) (Cb := Cb) (A := A) (s := si) (lam := lam) (δ := δ)
    hZ0 hZi hR0 hRi hdec hq0 hq1 one_pos (by linarith) hCb hA (by linarith) hsi0 hlam hδ
    hZmean hroom Gset hGmeas hGunc hbad hGint
  -- undo the normalisation
  have hZeq : ∀ ω, (∫ h in Set.Icc (T / Real.exp 1) T, ρ h *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1)
        (shiftLine σ h) ω‖ ^ 2) = M * Zf ω := by
    intro ω
    rw [hZfdef, ← mul_assoc, mul_inv_cancel₀ hM0.ne', one_mul]
  simp only [hZeq]
  have hpow : ∀ ω : Ω, (M * Zf ω) ^ q = M ^ q * Zf ω ^ q := fun ω =>
    Real.mul_rpow hM0.le (hZ0 ω)
  simp only [hpow]
  rw [integral_const_mul]
  calc M ^ q * ∫ ω, Zf ω ^ q ∂ν
      ≤ M ^ q * (shiftMomentConst 1 Ci Cb A si lam δ q
          * (1 + (1 - q) * Real.sqrt (n : ℝ)) ^ (-q)) :=
        mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg hM0.le q)
    _ = shiftMomentConst 1 Ci Cb A si lam δ q * M ^ q
          * (1 + (1 - q) * Real.sqrt (n : ℝ)) ^ (-q) := by ring

/-! ### The weighted block chaos, explicit -/

/-- **The weighted block chaos from the level floor `16Δ`, at any height**: as
`RMF.integral_rpow_block_weight_le_floor` with `T ≤ 1` replaced by the height condition at the
floor, `(2T + 1)·pntFloorConst ϑ ≤ e^{-2E₀}/200`. -/
theorem integral_rpow_block_weight_le_floor_of_height (E₀ β : ℝ) (hE₀ : 0 ≤ E₀)
    (hβ : 1 / 2 < β) (hβ2 : β ≤ 2) {Tr κ Kθ Amax δ : ℝ} {N : ℕ} (hTr : 4 < Tr) (hκ : 1 ≤ κ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δ * N)
    (hmono : 3 ≤ 8 * δ * Real.sqrt (N : ℝ))
    {Y : ℕ → Ω → ℂ} {ν : Measure Ω} (hY : IsRademacherPrimeValues Y ν)
    {x σ η T q A lam Bd : ℝ} {z D : ℕ} {ρ : ℝ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ h, 0 ≤ ρ h) (hρb : ∀ h, ρ h ≤ Bd)
    (hρpos : 0 < ∫ h in Set.Icc (T / Real.exp 1) T, ρ h)
    (hx1 : 1 < x) (hDlog : (D : ℝ) ≤ Real.log (Real.log x))
    (hϑ : radFreeStartThreshold E₀ ≤ harperOffset D x) (hϑ104 : (104 : ℝ) ≤ harperOffset D x)
    (hσ0 : 0 ≤ σ) (hη0 : 0 ≤ η) (hηE : η ≤ E₀) (hσx : |σ| * Real.log x ≤ η)
    (hT0 : 0 < T)
    (hhT : (2 * T + 1) * pntFloorConst (harperOffset D x) ≤ Real.exp (-(2 * E₀)) / 200)
    (hlo : 600 * Real.exp (2 * E₀) ≤ 2 * (T / Real.exp 1) * Real.exp (harperOffset D x))
    (hKθ : T * Real.exp (harperOffset D x) ≤ Kθ)
    (hzb : (z : ℝ) ≤ blockScale (harperOffset D x) 0) (hzn : z ≤ ⌊x⌋₊ + 1)
    (hNn : N ≤ harperBlockCount D x)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hA : radBlockBadLevel E₀ ≤ A) (hAmax : A ≤ Amax)
    (hlam : 1 ≤ lam) :
    (∫ ω, (∫ h in Set.Icc (T / Real.exp 1) T, ρ h *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1)
          (shiftLine σ h) ω‖ ^ 2) ^ q ∂ν)
      ≤ shiftMomentConst 1 (radAveragedConst E₀ β Tr κ) (radBlockBadConst E₀ β * Kθ) A
          (radAveragedShift E₀ β Tr κ) lam δ q
        * ((∫ h in Set.Icc (T / Real.exp 1) T, ρ h) * ∫ ω, ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2
            ∂ν) ^ q
        * (1 + (1 - q) * Real.sqrt (harperBlockCount D x : ℝ)) ^ (-q) := by
  have hϑ16 : (16 : ℝ) ≤ harperOffset D x := by linarith
  have hTθ : 1 ≤ T * Real.exp (harperOffset D x) := by
    have hE : (1 : ℝ) ≤ Real.exp (2 * E₀) := Real.one_le_exp (by linarith)
    have h1 : 2 * (T / Real.exp 1) * Real.exp (harperOffset D x)
        = 2 / Real.exp 1 * (T * Real.exp (harperOffset D x)) := by ring
    have h2 : 2 / Real.exp 1 ≤ 2 := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have hTe0 : (0 : ℝ) ≤ T * Real.exp (harperOffset D x) := by positivity
    have h3 := mul_le_mul_of_nonneg_right h2 hTe0
    nlinarith
  have hKθ1 : (1 : ℝ) ≤ Kθ := le_trans hTθ hKθ
  have hCb := radBlockBadConst_pos E₀ hβ
  refine integral_rpow_block_weight_le_of_bad_of_height E₀ β hE₀ (by linarith) hβ2 hTr hκ
    (mul_pos hCb (by linarith)) (one_le_radBlockBadLevel E₀) hδ0 hδ hN hmono hY hρm hρ0 hρb
    hρpos hx1 hDlog hϑ hϑ104 hσ0 hη0 hηE hσx hT0 hhT hlo hzb hzn hNn hq0 hq1 hA hAmax hlam ?_
  intro a ha
  refine le_trans (measureReal_not_mesoGood_le_rademacher_floor E₀ β hβ hβ2 hY hx1 hDlog hϑ16
    hσ0 hη0 hηE hσx hT0 hTθ ha) ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left hKθ hCb.le

/-- **The weighted block chaos with named constants, from the level floor `16Δ`.**  For a bounded
measurable weight `ρ ≥ 0` in the height with `∫ρ > 0`, `0 < T ≤ 1`, and the levels from
`RMF.radBlockBadLevel E₀`:

`E[(∫_{T/e}^{T}ρ(h)‖F_{[z,x]}(½+σ+ih)‖²dh)^q]
  ≤ shiftMomentConst 1 C_i C_b A s λ δ q·((∫ρ)·M₀)^q·(1 + (1-q)√n)^{-q}`,

`C_i = radAveragedConst E₀ β Tr κ`, `s = radAveragedShift E₀ β Tr κ`,
`C_b = radBlockBadConst E₀ β·K_ϑ`, `K_ϑ ≥ T e^ϑ`, `M₀ = E‖F_{[z,x]}(½+σ)‖²`,
`n = harperBlockCount D x`. -/
theorem integral_rpow_block_weight_le_floor (E₀ β : ℝ) (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1)
    (hβ : 1 / 2 < β) (hβ2 : β ≤ 2) {Tr κ Kθ Amax δ : ℝ} {N : ℕ} (hTr : 4 < Tr) (hκ : 1 ≤ κ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δ * N)
    (hmono : 3 ≤ 8 * δ * Real.sqrt (N : ℝ))
    {Y : ℕ → Ω → ℂ} {ν : Measure Ω} (hY : IsRademacherPrimeValues Y ν)
    {x σ η T q A lam Bd : ℝ} {z D : ℕ} {ρ : ℝ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ h, 0 ≤ ρ h) (hρb : ∀ h, ρ h ≤ Bd)
    (hρpos : 0 < ∫ h in Set.Icc (T / Real.exp 1) T, ρ h)
    (hx1 : 1 < x) (hDlog : (D : ℝ) ≤ Real.log (Real.log x))
    (hϑ : radFreeStartThreshold E₀ ≤ harperOffset D x) (hϑ104 : (104 : ℝ) ≤ harperOffset D x)
    (hσ0 : 0 ≤ σ) (hη0 : 0 ≤ η) (hηE : η ≤ E₀) (hσx : |σ| * Real.log x ≤ η)
    (hT0 : 0 < T) (hT1 : T ≤ 1)
    (hlo : 600 * Real.exp (2 * E₀) ≤ 2 * (T / Real.exp 1) * Real.exp (harperOffset D x))
    (hKθ : T * Real.exp (harperOffset D x) ≤ Kθ)
    (hzb : (z : ℝ) ≤ blockScale (harperOffset D x) 0) (hzn : z ≤ ⌊x⌋₊ + 1)
    (hNn : N ≤ harperBlockCount D x)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hA : radBlockBadLevel E₀ ≤ A) (hAmax : A ≤ Amax)
    (hlam : 1 ≤ lam) :
    (∫ ω, (∫ h in Set.Icc (T / Real.exp 1) T, ρ h *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1)
          (shiftLine σ h) ω‖ ^ 2) ^ q ∂ν)
      ≤ shiftMomentConst 1 (radAveragedConst E₀ β Tr κ) (radBlockBadConst E₀ β * Kθ) A
          (radAveragedShift E₀ β Tr κ) lam δ q
        * ((∫ h in Set.Icc (T / Real.exp 1) T, ρ h) * ∫ ω, ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2
            ∂ν) ^ q
        * (1 + (1 - q) * Real.sqrt (harperBlockCount D x : ℝ)) ^ (-q) := by
  have hhT : 2 * T + 1 ≤ 5 * 10 ^ 25 * Real.exp (-(2 * E₀)) := by
    have he2 : Real.exp (-2) ≤ Real.exp (-(2 * E₀)) := Real.exp_le_exp.2 (by linarith)
    have he2' : (1 : ℝ) / 10 ≤ Real.exp (-2) := by
      rw [Real.exp_neg, one_div, inv_le_inv₀ (by norm_num) (Real.exp_pos 2)]
      have := Real.exp_one_lt_d9
      have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      rw [hsq]
      nlinarith [Real.exp_pos (1 : ℝ)]
    linarith
  have hhTF : (2 * T + 1) * pntFloorConst (harperOffset D x) ≤ Real.exp (-(2 * E₀)) / 200 := by
    have h := height_floor_of_height (t := T) hϑ104 (by rw [abs_of_pos hT0]; exact hhT)
    rwa [abs_of_pos hT0] at h
  exact integral_rpow_block_weight_le_floor_of_height E₀ β hE₀ hβ hβ2 hTr hκ hδ0 hδ hN hmono
    hY hρm hρ0 hρb hρpos hx1 hDlog hϑ hϑ104 hσ0 hη0 hηE hσx hT0 hhTF hlo hKθ hzb hzn hNn hq0
    hq1
    hA hAmax hlam

end RMF
