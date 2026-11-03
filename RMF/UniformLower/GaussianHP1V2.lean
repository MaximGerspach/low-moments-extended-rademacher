/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.GaussianHP1Main
import RMF.UniformLower.HP1Rademacher
import RMF.Probability.Harris

/-!
# The window's first moment, v2

In the Gaussian setting of `RMF/UniformLower/GaussianHP1Main.lean` — a Gaussian height walk `Z`
and an independent Gaussian residual walk `W`, slopes `β`, drifts `d`, the pair family
`(Z_m, d_m + β_m Z_m + W_m)` and its two-sided window event — the event has probability at least
`RMF.hp1LowerBoundV2 … / √n` for every `n ≥ n₀` (`RMF.le_measure_windowEvent_gaussian_v2`).  Two
features of the argument:

* **The exit factor inside the start.**  Given the start, the real suffix survives with
  probability at least `RMF.hp1ExitV2 … V₂ = max(1 - e^{t(V₂+L+ρ)+Λ} - e^{-A_W}, 0)`
  (`RMF.le_measureReal_exitV2`), and the start's main term `RMF.startMainV2` is the
  one-dimensional integral of `min((a - u)⁺, C)` against the conditional mean of the exit factor
  given `U₂ = u`.  The far floor enters additively, as `-e^{-A_W}` inside the exit factor: the
  residual walk's ceiling and floor events are negatively correlated.
* **Harris for the suffix blocks with `β_m ≥ 0`.**  Split the slopes as
  `β_m = max(β_m, 0) + min(β_m, 0)`.  Given the start and the residual walk `W`, the height event
  (ceiling only, and the slope walk of the blocks `β_m < 0` below `L`) and the reduced real event
  (ceiling only, the blocks `β_m ≥ 0` inside) are both lower sets along the coordinates `Z_m` with
  `β_m ≥ 0`, and the second depends on no other coordinate: Harris' inequality in those coordinates
  (`RMF.mul_integral_le_integral_mul_pi_partial`) gives the product of their probabilities
  (`RMF.measureReal_mul_le_measureReal_inter_harrisV2`).  So only `R⁻ = ∑ min(β_m, 0)Z_m` is paid
  by the margin `L` (`σ_R²` and `K_late` see only `min(β_m, 0)`), and the blocks `β_m ≥ 0` enter
  the real walk with their full variance `β_m²v_m + s_m` (in `Λ`).  The height floor is paid
  relatively, and once (`RMF.ofReal_le_measure_hp1SuffixV2`); the real walk's far floor sits on the
  residual walk, and the whole slope walk is bounded on the tube by `K_R`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

namespace RMF

/-! ### Harris' inequality in part of the coordinates -/

/-- **Harris' inequality in part of the coordinates.**  Under a product of probability measures on
`ℝ`, let `f` be antitone along the coordinates `i` with `p i` (the others held fixed), and let `g`
be antitone and depend only on the coordinates with `p i`.  Then `f` and `g` are positively
correlated.  By induction on the coordinates: at a coordinate with `p i` Chebyshev's inequality in
it, at one without the fibre integral of `g` does not depend on it. -/
theorem mul_integral_le_integral_mul_pi_partial {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (p : Fin n → Prop) {f g : (Fin n → ℝ) → ℝ}
    (hf : ∀ x y, x ≤ y → (∀ i, ¬ p i → x i = y i) → f y ≤ f x) (hg : Antitone g)
    (hgp : ∀ x y, (∀ i, p i → x i = y i) → g x = g y)
    (hfm : Measurable f) (hgm : Measurable g) {Cf Cg : ℝ}
    (hfb : ∀ x, |f x| ≤ Cf) (hgb : ∀ x, |g x| ≤ Cg) :
    (∫ x, f x ∂(Measure.pi μ)) * (∫ x, g x ∂(Measure.pi μ)) ≤ ∫ x, f x * g x ∂(Measure.pi μ) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty μ, integral_dirac, integral_dirac, integral_dirac]
  | succ n ih =>
    have hC : ∀ t : ℝ, Measurable fun y : Fin n → ℝ => (Fin.cons t y : Fin (n + 1) → ℝ) :=
      fun t => measurable_finCons_real.comp (measurable_const.prodMk measurable_id)
    have hCf : 0 ≤ Cf := le_trans (abs_nonneg _) (hfb 0)
    have hfgb : ∀ x, |f x * g x| ≤ Cf * Cg := fun x => by
      rw [abs_mul]
      exact mul_le_mul (hfb x) (hgb x) (abs_nonneg _) hCf
    have hfgm : Measurable fun x => f x * g x := hfm.mul hgm
    rw [integral_pi_succ_eq μ (integrable_of_measurable_of_abs_le hfm hfb),
      integral_pi_succ_eq μ (integrable_of_measurable_of_abs_le hgm hgb),
      integral_pi_succ_eq μ (integrable_of_measurable_of_abs_le hfgm hfgb)]
    set ν : Measure (Fin n → ℝ) := Measure.pi fun j => μ j.succ
    have habs : ∀ {H : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}, (∀ x, |H x| ≤ C) →
        ∀ t, |∫ y, H (Fin.cons t y) ∂ν| ≤ C := by
      intro H C hH t
      have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun y => H (Fin.cons t y))
        (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hH _)
      simpa [Real.norm_eq_abs, probReal_univ] using this
    -- the induction hypothesis on each fibre
    have hfib : ∀ t, (∫ y, f (Fin.cons t y) ∂ν) * (∫ y, g (Fin.cons t y) ∂ν)
        ≤ ∫ y, f (Fin.cons t y) * g (Fin.cons t y) ∂ν := fun t =>
      ih (fun j => μ j.succ) (fun j => p j.succ) (f := fun y => f (Fin.cons t y))
        (g := fun y => g (Fin.cons t y))
        (fun y y' h hq => hf _ _ (Fin.cons_le_cons.2 ⟨le_rfl, h⟩) fun i hi => by
          cases i using Fin.cases with
          | zero => simp
          | succ j => simpa using hq j hi)
        (fun y y' h => hg (Fin.cons_le_cons.2 ⟨le_rfl, h⟩))
        (fun y y' hq => hgp _ _ fun i hi => by
          cases i using Fin.cases with
          | zero => simp
          | succ j => simpa using hq j hi)
        (hfm.comp (hC t)) (hgm.comp (hC t)) (fun y => hfb _) (fun y => hgb _)
    -- the fibre integrals are integrable in the first coordinate
    have hFint : Integrable (fun t => ∫ y, f (Fin.cons t y) ∂ν) (μ 0) :=
      (integrable_of_measurable_of_abs_le (μ := (μ 0).prod ν)
        (hfm.comp measurable_finCons_real) fun q => hfb _).integral_prod_left
    have hGint : Integrable (fun t => ∫ y, g (Fin.cons t y) ∂ν) (μ 0) :=
      (integrable_of_measurable_of_abs_le (μ := (μ 0).prod ν)
        (hgm.comp measurable_finCons_real) fun q => hgb _).integral_prod_left
    have hFGint : Integrable (fun t => ∫ y, f (Fin.cons t y) * g (Fin.cons t y) ∂ν) (μ 0) :=
      (integrable_of_measurable_of_abs_le (μ := (μ 0).prod ν)
        (hfgm.comp measurable_finCons_real) fun q => hfgb _).integral_prod_left
    have hGa : Antitone fun t => ∫ y, g (Fin.cons t y) ∂ν := fun t t' htt' =>
      integral_mono (integrable_of_measurable_of_abs_le (hgm.comp (hC t')) fun y => hgb _)
        (integrable_of_measurable_of_abs_le (hgm.comp (hC t)) fun y => hgb _)
        fun y => hg (Fin.cons_le_cons.2 ⟨htt', le_rfl⟩)
    by_cases hp0 : p 0
    · -- a coordinate of `p`: Chebyshev's inequality in it
      have hFa : Antitone fun t => ∫ y, f (Fin.cons t y) ∂ν := fun t t' htt' =>
        integral_mono (integrable_of_measurable_of_abs_le (hfm.comp (hC t')) fun y => hfb _)
          (integrable_of_measurable_of_abs_le (hfm.comp (hC t)) fun y => hfb _)
          fun y => hf _ _ (Fin.cons_le_cons.2 ⟨htt', le_rfl⟩) fun i hi => by
            cases i using Fin.cases with
            | zero => exact absurd hp0 hi
            | succ j => simp
      have hcheb := mul_integral_le_integral_mul_of_antitone (μ := μ 0) hFa hGa hFa.measurable
        hGa.measurable (habs hfb) (habs hgb)
      refine le_trans hcheb (integral_mono ?_ hFGint hfib)
      exact integrable_of_measurable_of_abs_le (hFa.measurable.mul hGa.measurable) fun t => by
        rw [abs_mul]
        exact mul_le_mul (habs hfb t) (habs hgb t) (abs_nonneg _) hCf
    · -- not a coordinate of `p`: the fibre integral of `g` is constant in it
      have hGc : ∀ t, ∫ y, g (Fin.cons t y) ∂ν = ∫ y, g (Fin.cons 0 y) ∂ν := fun t =>
        integral_congr_ae (Filter.Eventually.of_forall fun y => hgp _ _ fun i hi => by
          cases i using Fin.cases with
          | zero => exact absurd hi hp0
          | succ j => simp)
      set G₀ := ∫ y, g (Fin.cons 0 y) ∂ν with hG₀
      have hIG : ∫ t, ∫ y, g (Fin.cons t y) ∂ν ∂(μ 0) = G₀ := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hGc), integral_const, probReal_univ,
          one_smul]
      calc (∫ t, ∫ y, f (Fin.cons t y) ∂ν ∂(μ 0)) * ∫ t, ∫ y, g (Fin.cons t y) ∂ν ∂(μ 0)
          = ∫ t, (∫ y, f (Fin.cons t y) ∂ν) * (∫ y, g (Fin.cons t y) ∂ν) ∂(μ 0) := by
            rw [hIG, ← integral_mul_const]
            exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
              dsimp only
              rw [hGc t])
        _ ≤ ∫ t, ∫ y, f (Fin.cons t y) * g (Fin.cons t y) ∂ν ∂(μ 0) :=
            integral_mono (hFint.mul_const G₀ |>.congr (Filter.Eventually.of_forall fun t => by
              dsimp only
              rw [hGc t])) hFGint hfib

/-- **Harris' inequality in part of the coordinates, for independent real random variables**:
`RMF.mul_integral_le_integral_mul_pi_partial` on the joint law of `Z`, the product of the
marginals. -/
theorem mul_integral_le_integral_mul_of_iIndepFun_partial {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {Z : Fin n → Ω → ℝ}
    (hZm : ∀ i, Measurable (Z i)) (hZ : iIndepFun Z P) (p : Fin n → Prop)
    {f g : (Fin n → ℝ) → ℝ} (hf : ∀ x y, x ≤ y → (∀ i, ¬ p i → x i = y i) → f y ≤ f x)
    (hg : Antitone g) (hgp : ∀ x y, (∀ i, p i → x i = y i) → g x = g y)
    (hfm : Measurable f) (hgm : Measurable g) {Cf Cg : ℝ}
    (hfb : ∀ x, |f x| ≤ Cf) (hgb : ∀ x, |g x| ≤ Cg) :
    (∫ ω, f (fun i => Z i ω) ∂P) * (∫ ω, g (fun i => Z i ω) ∂P)
      ≤ ∫ ω, f (fun i => Z i ω) * g (fun i => Z i ω) ∂P := by
  haveI := hZ.isProbabilityMeasure
  have hW : Measurable fun ω i => Z i ω := measurable_pi_lambda _ hZm
  have hlaw : P.map (fun ω i => Z i ω) = Measure.pi fun i => P.map (Z i) :=
    hZ.map_fun_eq_pi_map fun i => (hZm i).aemeasurable
  haveI : ∀ i, IsProbabilityMeasure (P.map (Z i)) := fun i =>
    Measure.isProbabilityMeasure_map (hZm i).aemeasurable
  have hfgm : Measurable fun x => f x * g x := hfm.mul hgm
  have h := mul_integral_le_integral_mul_pi_partial (fun i => P.map (Z i)) p hf hg hgp hfm hgm
    hfb hgb
  rw [← hlaw, integral_map hW.aemeasurable hfm.aestronglyMeasurable,
    integral_map hW.aemeasurable hgm.aestronglyMeasurable,
    integral_map hW.aemeasurable hfgm.aestronglyMeasurable] at h
  exact h

/-- **Harris' inequality in part of the coordinates, for events**: for independent real `Z`, a
set `S` that is a lower set along the coordinates with `p i` (the others held fixed), and a lower
set `T` depending only on those coordinates, `P(Z ∈ S) P(Z ∈ T) ≤ P(Z ∈ S, Z ∈ T)`. -/
theorem measureReal_mul_le_measureReal_inter_of_iIndepFun_partial {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {Z : Fin n → Ω → ℝ}
    (hZm : ∀ i, Measurable (Z i)) (hZ : iIndepFun Z P) (p : Fin n → Prop)
    {S T : Set (Fin n → ℝ)} (hS : ∀ x y, x ≤ y → (∀ i, ¬ p i → x i = y i) → y ∈ S → x ∈ S)
    (hT : IsLowerSet T) (hTp : ∀ x y, (∀ i, p i → x i = y i) → x ∈ T → y ∈ T)
    (hSm : MeasurableSet S) (hTm : MeasurableSet T) :
    P.real {ω | (fun i => Z i ω) ∈ S} * P.real {ω | (fun i => Z i ω) ∈ T}
      ≤ P.real ({ω | (fun i => Z i ω) ∈ S} ∩ {ω | (fun i => Z i ω) ∈ T}) := by
  have hW : Measurable fun ω i => Z i ω := measurable_pi_lambda _ hZm
  have hb : ∀ (U : Set (Fin n → ℝ)) x, |U.indicator (1 : (Fin n → ℝ) → ℝ) x| ≤ 1 := by
    intro U x
    by_cases hx : x ∈ U
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hf : ∀ x y, x ≤ y → (∀ i, ¬ p i → x i = y i) →
      S.indicator (1 : (Fin n → ℝ) → ℝ) y ≤ S.indicator 1 x := by
    intro x y hxy hq
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hS x y hxy hq hy)]
      exact le_rfl
    · rw [Set.indicator_of_notMem hy]
      exact Set.indicator_nonneg (fun _ _ => by simp) x
  have hg : Antitone (T.indicator (1 : (Fin n → ℝ) → ℝ)) := by
    intro x y hxy
    by_cases hy : y ∈ T
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hT hxy hy)]
      exact le_rfl
    · rw [Set.indicator_of_notMem hy]
      exact Set.indicator_nonneg (fun _ _ => by simp) x
  have hgp : ∀ x y, (∀ i, p i → x i = y i) →
      T.indicator (1 : (Fin n → ℝ) → ℝ) x = T.indicator 1 y := by
    intro x y hq
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hTp x y hq hx)]
      rfl
    · have hy : y ∉ T := fun hy => hx (hTp y x (fun i hi => (hq i hi).symm) hy)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  have h := mul_integral_le_integral_mul_of_iIndepFun_partial hZm hZ p hf hg hgp
    (measurable_one.indicator hSm) (measurable_one.indicator hTm) (hb S) (hb T)
  have e : ∀ {U : Set (Fin n → ℝ)}, MeasurableSet U →
      ∫ ω, U.indicator (1 : (Fin n → ℝ) → ℝ) (fun i => Z i ω) ∂P
        = P.real {ω | (fun i => Z i ω) ∈ U} :=
    fun hU => integral_indicator_one (hW hU)
  have e2 := integral_indicator_one (μ := P) ((hW hSm).inter (hW hTm))
  rw [Set.inter_indicator_one] at e2
  calc P.real {ω | (fun i => Z i ω) ∈ S} * P.real {ω | (fun i => Z i ω) ∈ T}
      = (∫ ω, S.indicator (1 : (Fin n → ℝ) → ℝ) (fun i => Z i ω) ∂P)
        * ∫ ω, T.indicator (1 : (Fin n → ℝ) → ℝ) (fun i => Z i ω) ∂P := by
        rw [e hSm, e hTm]
    _ ≤ _ := h
    _ = _ := e2

/-! ### The pair law, conditionally on the first coordinate -/

/-- **Integrals on the pair law, conditionally on the first coordinate**: for
`(U, Y) ~ gaussianPairLaw 0 0 V S κ` and bounded measurable `f`, `h`,
`E[f(U)h(Y)] = ∫ f(u) E[h(β̄u + N(0, σ²))] dN(0, V)(u)`, `β̄ = κ/V`, `σ² = S - κ²/V`: given the
first coordinate, the second is `β̄u + σW`. -/
theorem integral_mul_gaussianPairLaw_eq {V S κ Cf Ch : ℝ} (hV : 0 ≤ V) (hS : 0 ≤ S)
    (hCS : κ ^ 2 ≤ V * S) {f h : ℝ → ℝ} (hfm : Measurable f) (hhm : Measurable h)
    (hfb : ∀ x, |f x| ≤ Cf) (hhb : ∀ x, |h x| ≤ Ch) :
    ∫ p, f p.1 * h p.2 ∂(gaussianPairLaw 0 0 V S κ)
      = ∫ u, f u * ∫ y, h (pairSlope V κ * u + y)
          ∂(gaussianReal 0 (pairResidVar V S κ).toNNReal) ∂(gaussianReal 0 V.toNNReal) := by
  set β := pairSlope V κ with hβ
  set σ2 := pairResidVar V S κ with hσ2
  have hσ20 : 0 ≤ σ2 := pairResidVar_nonneg hV hS hCS
  set σ := Real.sqrt σ2 with hσ
  have hCf : 0 ≤ Cf := le_trans (abs_nonneg _) (hfb 0)
  have hFm : Measurable fun p : ℝ × ℝ => f p.1 * h p.2 :=
    (hfm.comp measurable_fst).mul (hhm.comp measurable_snd)
  rw [integral_gaussianPairLaw hFm.aestronglyMeasurable]
  simp only [zero_add]
  set G : ℝ × ℝ → ℝ := fun z => f z.1 * h (β * z.1 + σ * z.2) with hG
  change ∫ z, G z ∂(gaussianPairBase V) = _
  have hGm : Measurable G := (hfm.comp measurable_fst).mul (hhm.comp
    ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)))
  have hGint : Integrable G (gaussianPairBase V) :=
    integrable_of_measurable_of_abs_le hGm (C := Cf * Ch) fun z => by
      rw [hG, abs_mul]
      exact mul_le_mul (hfb _) (hhb _) (abs_nonneg _) hCf
  have hlaw : (gaussianReal 0 1).map (fun w => σ * w) = gaussianReal 0 σ2.toNNReal := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp [hσ, Real.sq_sqrt hσ20, Real.coe_toNNReal _ hσ20]
  rw [gaussianPairBase, integral_prod G hGint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [hG]
  rw [integral_const_mul]
  congr 1
  have hhu : Measurable fun y => h (β * u + y) :=
    hhm.comp (measurable_const.add measurable_id)
  rw [← hlaw, integral_map (by fun_prop) hhu.aestronglyMeasurable]

/-! ### The exit factor and the start -/

/-- **The exit factor of HP1 v2**: `max(1 - e^{t(y+L+ρ)+Λ} - e^{-A_W}, 0)`, a lower bound for the
probability that the real suffix started at `y` stays below `-L - ρ` and above its far floor
(`RMF.le_measureReal_exitV2`). -/
noncomputable def hp1ExitV2 (t L ρ Λ AW y : ℝ) : ℝ :=
  max (1 - Real.exp (t * (y + L + ρ) + Λ) - Real.exp (-AW)) 0

lemma hp1ExitV2_nonneg (t L ρ Λ AW y : ℝ) : 0 ≤ hp1ExitV2 t L ρ Λ AW y := le_max_right _ _

lemma hp1ExitV2_le_one (t L ρ Λ AW y : ℝ) : hp1ExitV2 t L ρ Λ AW y ≤ 1 := by
  unfold hp1ExitV2
  refine max_le ?_ zero_le_one
  have h1 := Real.exp_pos (t * (y + L + ρ) + Λ)
  have h2 := Real.exp_pos (-AW)
  linarith

lemma continuous_hp1ExitV2 (t L ρ Λ AW : ℝ) : Continuous (hp1ExitV2 t L ρ Λ AW) := by
  unfold hp1ExitV2
  fun_prop

lemma measurable_hp1ExitV2 (t L ρ Λ AW : ℝ) : Measurable (hp1ExitV2 t L ρ Λ AW) :=
  (continuous_hp1ExitV2 t L ρ Λ AW).measurable

/-- **The start's main term of HP1 v2**, `E[min((a - U₂)⁺, C)·RMF.hp1ExitV2(V₂)]` for
`(U₂, V₂ - D) ~ gaussianPairLaw 0 0 V S κ`, as the one-dimensional integral
`∫ min((a - u)⁺, C)·E[RMF.hp1ExitV2(D + β̄u + N(0, σ²))] dN(0, V)(u)`, `β̄ = κ/V`,
`σ² = S - κ²/V` (`RMF.integral_mul_gaussianPairLaw_eq`). -/
noncomputable def startMainV2 (a C V S κ D t L ρ Λ AW : ℝ) : ℝ :=
  ∫ u, startWeight a C u * ∫ y, hp1ExitV2 t L ρ Λ AW (D + pairSlope V κ * u + y)
    ∂(gaussianReal 0 (pairResidVar V S κ).toNNReal) ∂(gaussianReal 0 V.toNNReal)

section StartV2

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {Q₁ : Measure Ω₁}
  {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
  {Z : ℕ → Ω₁ → ℝ} {W : ℕ → Ω₂ → ℝ} {v s : ℕ → ℝ≥0}

/-- **The start of HP1 v2, blocks `0, 1` aggregated.**  On the product space, the weight
`min((a - U₂)⁺, C)·RMF.hp1ExitV2(V₂)`, `C = a + A + 2B`, over the start box `Z₀ ∈ [-A-B, a]`,
`U₂ ∈ [-A-2B, a]`, `|V₁| ≤ M₁`, `V₂ ≥ -K₂` integrates to at least the main term
`RMF.startMainV2`, less the ceiling loss `P(Z₀ > a)E[min((-Z₁)⁺, C)]` and `C` times the tails
`RMF.startTails`. -/
theorem le_integral_startGoodV2 (hZ : IsGaussianWalk Z v Q₁) (hW : IsGaussianWalk W s Q₂)
    (β d : ℕ → ℝ) (hv0 : 0 < (v 0 : ℝ)) (hv1 : 0 < (v 1 : ℝ))
    {a A B M₁ K₂ t L ρ Λ AW : ℝ} (hAB : 0 ≤ A + B) (hB : 0 ≤ B) (hC : 0 ≤ a + A + 2 * B)
    (hM₁ : |d 0| ≤ M₁) (hK₂ : 0 ≤ K₂ + d 0 + d 1) :
    startMainV2 a (a + A + 2 * B) (v 0 + v 1) (β 0 ^ 2 * v 0 + s 0 + (β 1 ^ 2 * v 1 + s 1))
        (β 0 * v 0 + β 1 * v 1) (d 0 + d 1) t L ρ Λ AW
      - (gaussianReal 0 (v 0)).real (Set.Ioi a)
        * ∫ x, startWeight 0 (a + A + 2 * B) x ∂(gaussianReal 0 (v 1))
      - (a + A + 2 * B) * startTails (v 0) (v 1) (s 0) (s 1) (β 0) (β 1) (d 0) (d 1) A B M₁ K₂
      ≤ ∫ ω, {ω : Ω₁ × Ω₂ | Z 0 ω.1 ∈ Set.Icc (-A - B) a
            ∧ Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a
            ∧ |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁
            ∧ -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)}.indicator
          (fun ω => startWeight a (a + A + 2 * B) (Z 0 ω.1 + Z 1 ω.1)
            * hp1ExitV2 t L ρ Λ AW ((d 0 + β 0 * Z 0 ω.1 + W 0 ω.2)
              + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2))) ω ∂(Q₁.prod Q₂) := by
  set C : ℝ := a + A + 2 * B with hCdef
  set Vs : ℝ := (v 0 : ℝ) + v 1 with hVs
  set S1 : ℝ := β 0 ^ 2 * v 0 + s 0 with hS1
  set S2 : ℝ := β 0 ^ 2 * v 0 + s 0 + (β 1 ^ 2 * v 1 + s 1) with hS2
  set κ : ℝ := β 0 * v 0 + β 1 * v 1 with hκ
  have hz0 : Measurable fun ω : Ω₁ × Ω₂ => Z 0 ω.1 := (hZ.measurable 0).comp measurable_fst
  have hz1 : Measurable fun ω : Ω₁ × Ω₂ => Z 1 ω.1 := (hZ.measurable 1).comp measurable_fst
  have hw0 : Measurable fun ω : Ω₁ × Ω₂ => W 0 ω.2 := (hW.measurable 0).comp measurable_snd
  have hw1 : Measurable fun ω : Ω₁ × Ω₂ => W 1 ω.2 := (hW.measurable 1).comp measurable_snd
  have hUm : Measurable fun ω : Ω₁ × Ω₂ => Z 0 ω.1 + Z 1 ω.1 := hz0.add hz1
  have hX₀m : Measurable fun ω : Ω₁ × Ω₂ => β 0 * Z 0 ω.1 + W 0 ω.2 := (hz0.const_mul _).add hw0
  have hYm : Measurable fun ω : Ω₁ × Ω₂ =>
      (β 0 * Z 0 ω.1 + W 0 ω.2) + (β 1 * Z 1 ω.1 + W 1 ω.2) :=
    ((hz0.const_mul _).add hw0).add ((hz1.const_mul _).add hw1)
  have hV₂m : Measurable fun ω : Ω₁ × Ω₂ =>
      (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2) :=
    ((measurable_const.add (hz0.const_mul _)).add hw0).add
      ((measurable_const.add (hz1.const_mul _)).add hw1)
  have hS10 : 0 ≤ S1 := by positivity
  have hS20 : 0 ≤ S2 := by positivity
  have hCS : κ ^ 2 ≤ Vs * S2 :=
    add_cauchy_schwarz (v 0).coe_nonneg hS10 (v 1).coe_nonneg (by positivity)
      (sq_mul_le_blockPair _ _ _) (sq_mul_le_blockPair _ _ _)
  -- the laws
  have hlawUY := map_startPair_eq hZ hW β hv0 hv1 (Q₁ := Q₁) (Q₂ := Q₂)
  have hlawU : (Q₁.prod Q₂).map (fun ω => Z 0 ω.1 + Z 1 ω.1) = gaussianReal 0 Vs.toNNReal := by
    have h := congrArg (Measure.map Prod.fst) hlawUY
    rw [Measure.map_map measurable_fst (hUm.prodMk hYm),
      map_fst_gaussianPairLaw (by positivity) hS20 hCS] at h
    exact h
  have hlawY : (Q₁.prod Q₂).map (fun ω => (β 0 * Z 0 ω.1 + W 0 ω.2)
      + (β 1 * Z 1 ω.1 + W 1 ω.2)) = gaussianReal 0 S2.toNNReal := by
    have h := congrArg (Measure.map Prod.snd) hlawUY
    rw [Measure.map_map measurable_snd (hUm.prodMk hYm),
      map_snd_gaussianPairLaw (by positivity) hS20 hCS] at h
    exact h
  have hlawX₀ : (Q₁.prod Q₂).map (fun ω => β 0 * Z 0 ω.1 + W 0 ω.2)
      = gaussianReal 0 S1.toNNReal := by
    have h := congrArg (Measure.map Prod.snd) (map_blockPair_eq hZ hW β hv0 (Q₁ := Q₁) (Q₂ := Q₂))
    rw [Measure.map_map measurable_snd (hz0.prodMk hX₀m),
      map_snd_gaussianPairLaw hv0.le hS10 (sq_mul_le_blockPair _ _ _)] at h
    exact h
  have hlawZ₀ : (Q₁.prod Q₂).map (fun ω => Z 0 ω.1) = gaussianReal 0 (v 0) := by
    rw [map_comp_fst_prod (hZ.measurable 0), hZ.map_eq 0]
  -- the sets
  set Good : Set (Ω₁ × Ω₂) := {ω : Ω₁ × Ω₂ | Z 0 ω.1 ∈ Set.Icc (-A - B) a
      ∧ Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a
      ∧ |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁
      ∧ -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)} with hGood
  set E1 : Set (Ω₁ × Ω₂) := {ω | a < Z 0 ω.1} with hE1
  set T1 : Set (Ω₁ × Ω₂) := {ω | Z 0 ω.1 ≤ 0 - (A + B)} with hT1
  set T2 : Set (Ω₁ × Ω₂) := {ω | Z 0 ω.1 + Z 1 ω.1 ≤ 0 - (A + 2 * B)} with hT2
  set T3a : Set (Ω₁ × Ω₂) := {ω | 0 + (M₁ - d 0) ≤ β 0 * Z 0 ω.1 + W 0 ω.2} with hT3a
  set T3b : Set (Ω₁ × Ω₂) := {ω | β 0 * Z 0 ω.1 + W 0 ω.2 ≤ 0 - (M₁ + d 0)} with hT3b
  set T4 : Set (Ω₁ × Ω₂) :=
    {ω | (β 0 * Z 0 ω.1 + W 0 ω.2) + (β 1 * Z 1 ω.1 + W 1 ω.2) ≤ 0 - (K₂ + d 0 + d 1)} with hT4
  have hE1m : MeasurableSet E1 := measurableSet_lt measurable_const hz0
  have hT1m : MeasurableSet T1 := measurableSet_le hz0 measurable_const
  have hT2m : MeasurableSet T2 := measurableSet_le hUm measurable_const
  have hT3am : MeasurableSet T3a := measurableSet_le measurable_const hX₀m
  have hT3bm : MeasurableSet T3b := measurableSet_le hX₀m measurable_const
  have hT4m : MeasurableSet T4 := measurableSet_le hYm measurable_const
  have hGoodm : MeasurableSet Good := by
    have h1 : MeasurableSet {ω : Ω₁ × Ω₂ | Z 0 ω.1 ∈ Set.Icc (-A - B) a} :=
      hz0 measurableSet_Icc
    have h2 : MeasurableSet {ω : Ω₁ × Ω₂ | Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a} :=
      hUm measurableSet_Icc
    have h3 : MeasurableSet {ω : Ω₁ × Ω₂ | |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁} :=
      measurableSet_le ((measurable_const.add (hz0.const_mul _)).add hw0).abs measurable_const
    have h4 : MeasurableSet {ω : Ω₁ × Ω₂ | -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2)
        + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)} :=
      measurableSet_le measurable_const hV₂m
    exact h1.inter (h2.inter (h3.inter h4))
  set F : Ω₁ × Ω₂ → ℝ := fun ω => startWeight a C (Z 0 ω.1 + Z 1 ω.1)
    * hp1ExitV2 t L ρ Λ AW ((d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2))
    with hF
  have hFm : Measurable F :=
    ((measurable_startWeight a C).comp hUm).mul ((measurable_hp1ExitV2 t L ρ Λ AW).comp hV₂m)
  have hFw : ∀ ω, F ω ≤ startWeight a C (Z 0 ω.1 + Z 1 ω.1) := fun ω =>
    mul_le_of_le_one_right (startWeight_nonneg hC _) (hp1ExitV2_le_one _ _ _ _ _ _)
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω =>
    mul_nonneg (startWeight_nonneg hC _) (hp1ExitV2_nonneg _ _ _ _ _ _)
  have hFC : ∀ ω, F ω ≤ C := fun ω => le_trans (hFw ω) (startWeight_le _)
  -- pointwise
  set T : Ω₁ × Ω₂ → ℝ := fun ω => T1.indicator (fun _ => (1 : ℝ)) ω
    + T2.indicator (fun _ => (1 : ℝ)) ω + T3a.indicator (fun _ => (1 : ℝ)) ω
    + T3b.indicator (fun _ => (1 : ℝ)) ω + T4.indicator (fun _ => (1 : ℝ)) ω with hT
  have hpt : ∀ ω, F ω - E1.indicator F ω - C * T ω ≤ Good.indicator F ω := by
    intro ω
    have hi : ∀ T' : Set (Ω₁ × Ω₂), 0 ≤ T'.indicator (fun _ => (1 : ℝ)) ω :=
      fun T' => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    have hone : ∀ T' : Set (Ω₁ × Ω₂), ω ∈ T' → T'.indicator (fun _ => (1 : ℝ)) ω = 1 :=
      fun T' h => Set.indicator_of_mem h _
    have hT0 : 0 ≤ T ω := by
      simp only [hT]
      linarith [hi T1, hi T2, hi T3a, hi T3b, hi T4]
    have hCT : 0 ≤ C * T ω := mul_nonneg hC hT0
    have hE1nn : 0 ≤ E1.indicator F ω := Set.indicator_nonneg (fun ω _ => hF0 ω) ω
    have hbig : ∀ T' : Set (Ω₁ × Ω₂), ω ∈ T' → T'.indicator (fun _ => (1 : ℝ)) ω ≤ T ω →
        F ω ≤ C * T ω := by
      intro T' hm hle
      rw [hone T' hm] at hle
      nlinarith [hFC ω]
    by_cases hg : ω ∈ Good
    · rw [Set.indicator_of_mem hg]
      linarith
    · rw [Set.indicator_of_notMem hg]
      by_cases he1 : ω ∈ E1
      · rw [Set.indicator_of_mem he1]
        linarith
      · have key : F ω ≤ C * T ω := by
          by_cases h1 : ω ∈ T1
          · exact hbig T1 h1 (by simp only [hT]; linarith [hi T2, hi T3a, hi T3b, hi T4])
          by_cases h2 : ω ∈ T2
          · exact hbig T2 h2 (by simp only [hT]; linarith [hi T1, hi T3a, hi T3b, hi T4])
          by_cases h3 : ω ∈ T3a
          · exact hbig T3a h3 (by simp only [hT]; linarith [hi T1, hi T2, hi T3b, hi T4])
          by_cases h4 : ω ∈ T3b
          · exact hbig T3b h4 (by simp only [hT]; linarith [hi T1, hi T2, hi T3a, hi T4])
          by_cases h5 : ω ∈ T4
          · exact hbig T4 h5 (by simp only [hT]; linarith [hi T1, hi T2, hi T3a, hi T3b])
          by_cases hu : a ≤ Z 0 ω.1 + Z 1 ω.1
          · rw [hF]
            simp only
            rw [startWeight_eq_zero hC hu, zero_mul]
            exact hCT
          exfalso
          apply hg
          simp only [hE1, hT1, hT2, hT3a, hT3b, hT4, Set.mem_setOf_eq, not_le,
            not_lt] at he1 h1 h2 h3 h4 h5 hu
          simp only [hGood, Set.mem_setOf_eq, Set.mem_Icc]
          refine ⟨⟨by linarith, he1⟩, ⟨by linarith, hu.le⟩, ?_, by linarith⟩
          rw [abs_le]
          constructor <;> linarith
        rw [Set.indicator_of_notMem he1]
        linarith
  -- the integrals
  have hbF : ∀ (E : Set (Ω₁ × Ω₂)), MeasurableSet E → Integrable (E.indicator F) (Q₁.prod Q₂) :=
    fun E hE => Integrable.of_bound (hFm.indicator hE).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun ω _ => hF0 ω) ω)]
        exact le_trans (Set.indicator_le_self' (fun ω _ => hF0 ω) ω) (hFC ω))
  have hFint : Integrable F (Q₁.prod Q₂) :=
    Integrable.of_bound hFm.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω)]
      exact hFC ω)
  have hb1 : ∀ (E : Set (Ω₁ × Ω₂)), MeasurableSet E →
      Integrable (E.indicator (fun _ => (1 : ℝ))) (Q₁.prod Q₂) :=
    fun E hE => (integrable_const (1 : ℝ)).indicator hE
  have hTint : Integrable T (Q₁.prod Q₂) :=
    ((((hb1 T1 hT1m).add (hb1 T2 hT2m)).add (hb1 T3a hT3am)).add (hb1 T3b hT3bm)).add
      (hb1 T4 hT4m)
  have hIT : ∫ ω, T ω ∂(Q₁.prod Q₂) = (Q₁.prod Q₂).real T1 + (Q₁.prod Q₂).real T2
      + (Q₁.prod Q₂).real T3a + (Q₁.prod Q₂).real T3b + (Q₁.prod Q₂).real T4 := by
    have h4 := integral_add (((hb1 T1 hT1m).add (hb1 T2 hT2m)).add (hb1 T3a hT3am) |>.add
        (hb1 T3b hT3bm)) (hb1 T4 hT4m)
    have h3 := integral_add (((hb1 T1 hT1m).add (hb1 T2 hT2m)).add (hb1 T3a hT3am))
      (hb1 T3b hT3bm)
    have h2 := integral_add ((hb1 T1 hT1m).add (hb1 T2 hT2m)) (hb1 T3a hT3am)
    have h1 := integral_add (hb1 T1 hT1m) (hb1 T2 hT2m)
    simp only [Pi.add_apply] at h4 h3 h2 h1
    simp only [hT]
    rw [h4, h3, h2, h1, integral_indicator_const _ hT1m, integral_indicator_const _ hT2m,
      integral_indicator_const _ hT3am, integral_indicator_const _ hT3bm,
      integral_indicator_const _ hT4m]
    simp only [smul_eq_mul, mul_one]
  -- the tails
  have htail1 : (Q₁.prod Q₂).real T1 ≤ Real.exp (-((A + B) ^ 2 / (2 * v 0))) :=
    measureReal_le_sub_le_of_map_eq hz0 hlawZ₀ hAB
  have htail2 : (Q₁.prod Q₂).real T2 ≤ Real.exp (-((A + 2 * B) ^ 2 / (2 * Vs))) := by
    have h := measureReal_le_sub_le_of_map_eq hUm hlawU (by linarith : 0 ≤ A + 2 * B)
    rwa [Real.coe_toNNReal _ (by positivity)] at h
  have hM₁a : 0 ≤ M₁ - |d 0| := by linarith
  have htail3a : (Q₁.prod Q₂).real T3a ≤ Real.exp (-((M₁ - |d 0|) ^ 2 / (2 * S1))) := by
    have h := measureReal_add_le_le_of_map_eq hX₀m hlawX₀ (by
      have := le_abs_self (d 0); linarith : 0 ≤ M₁ - d 0)
    rw [Real.coe_toNNReal _ hS10] at h
    exact le_trans h (exp_neg_sq_div_le hS10 hM₁a (by linarith [le_abs_self (d 0)]))
  have htail3b : (Q₁.prod Q₂).real T3b ≤ Real.exp (-((M₁ - |d 0|) ^ 2 / (2 * S1))) := by
    have h := measureReal_le_sub_le_of_map_eq hX₀m hlawX₀ (by
      have := neg_abs_le (d 0); linarith : 0 ≤ M₁ + d 0)
    rw [Real.coe_toNNReal _ hS10] at h
    exact le_trans h (exp_neg_sq_div_le hS10 hM₁a (by linarith [neg_abs_le (d 0)]))
  have htail4 : (Q₁.prod Q₂).real T4 ≤ Real.exp (-((K₂ + d 0 + d 1) ^ 2 / (2 * S2))) := by
    have h := measureReal_le_sub_le_of_map_eq hYm hlawY hK₂
    rwa [Real.coe_toNNReal _ hS20] at h
  -- the main term
  have hmain : startMainV2 a C Vs S2 κ (d 0 + d 1) t L ρ Λ AW = ∫ ω, F ω ∂(Q₁.prod Q₂) := by
    set G : ℝ × ℝ → ℝ := fun p => startWeight a C p.1 * hp1ExitV2 t L ρ Λ AW (d 0 + d 1 + p.2)
      with hG
    have hGm : Measurable G := ((measurable_startWeight a C).comp measurable_fst).mul
      ((measurable_hp1ExitV2 t L ρ Λ AW).comp (measurable_const.add measurable_snd))
    have hpt0 : ∀ ω, F ω = G (Z 0 ω.1 + Z 1 ω.1,
        (β 0 * Z 0 ω.1 + W 0 ω.2) + (β 1 * Z 1 ω.1 + W 1 ω.2)) := by
      intro ω
      simp only [hF, hG]
      congr 2
      ring
    have hmapint : ∫ p, G p ∂((Q₁.prod Q₂).map (fun ω => (Z 0 ω.1 + Z 1 ω.1,
        (β 0 * Z 0 ω.1 + W 0 ω.2) + (β 1 * Z 1 ω.1 + W 1 ω.2))))
        = ∫ ω, G (Z 0 ω.1 + Z 1 ω.1, (β 0 * Z 0 ω.1 + W 0 ω.2) + (β 1 * Z 1 ω.1 + W 1 ω.2))
          ∂(Q₁.prod Q₂) :=
      integral_map (hUm.prodMk hYm).aemeasurable hGm.aestronglyMeasurable
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt0), ← hmapint, hlawUY]
    have hh : Measurable fun y => hp1ExitV2 t L ρ Λ AW (d 0 + d 1 + y) :=
      (measurable_hp1ExitV2 t L ρ Λ AW).comp (measurable_const.add measurable_id)
    have h := integral_mul_gaussianPairLaw_eq (V := Vs) (S := S2) (κ := κ) (Cf := C) (Ch := 1)
      (by positivity) hS20 hCS (measurable_startWeight a C) hh
      (fun x => by rw [abs_of_nonneg (startWeight_nonneg hC x)]; exact startWeight_le x)
      (fun x => by
        rw [abs_of_nonneg (hp1ExitV2_nonneg _ _ _ _ _ _)]
        exact hp1ExitV2_le_one _ _ _ _ _ _)
    rw [h, startMainV2]
    simp only [add_assoc]
  have hceil := integral_indicator_startWeight_le hZ hC (Q₂ := Q₂) (a := a)
  have hE1le : ∫ ω, E1.indicator F ω ∂(Q₁.prod Q₂)
      ≤ (gaussianReal 0 (v 0)).real (Set.Ioi a)
        * ∫ x, startWeight 0 C x ∂(gaussianReal 0 (v 1)) := by
    refine le_trans (integral_mono (hbF E1 hE1m) ?_ fun ω => ?_) hceil
    · exact Integrable.of_bound (((measurable_startWeight a C).comp hUm).indicator
        hE1m).aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg
            (fun ω _ => startWeight_nonneg hC _) ω)]
          exact le_trans (Set.indicator_le_self' (fun ω _ => startWeight_nonneg hC _) ω)
            (startWeight_le _))
    · exact Set.indicator_le_indicator (hFw ω)
  -- assemble
  have hsum : ∫ ω, (F ω - E1.indicator F ω - C * T ω) ∂(Q₁.prod Q₂)
      ≤ ∫ ω, Good.indicator F ω ∂(Q₁.prod Q₂) :=
    integral_mono ((hFint.sub (hbF E1 hE1m)).sub (hTint.const_mul C)) (hbF Good hGoodm) hpt
  have i1 := integral_sub (hFint.sub (hbF E1 hE1m)) (hTint.const_mul C)
  have i2 := integral_sub hFint (hbF E1 hE1m)
  have i3 := integral_const_mul (μ := Q₁.prod Q₂) C T
  simp only [Pi.sub_apply] at i1 i2
  rw [hIT] at i3
  have htails : (Q₁.prod Q₂).real T1 + (Q₁.prod Q₂).real T2 + (Q₁.prod Q₂).real T3a
      + (Q₁.prod Q₂).real T3b + (Q₁.prod Q₂).real T4
      ≤ startTails (v 0) (v 1) (s 0) (s 1) (β 0) (β 1) (d 0) (d 1) A B M₁ K₂ := by
    unfold startTails
    rw [← hS1, ← hS2, ← hVs]
    linarith
  have hCt := mul_le_mul_of_nonneg_left htails hC
  change _ ≤ ∫ ω, Good.indicator F ω ∂(Q₁.prod Q₂)
  linarith

end StartV2

/-! ### The suffix at a fixed start -/

/-- A vector of `Fin k` coordinates, padded by `0` to a sequence. -/
noncomputable def finPad (k : ℕ) (x : Fin k → ℝ) (m : ℕ) : ℝ :=
  if h : m < k then x ⟨m, h⟩ else 0

lemma measurable_finPad (k m : ℕ) : Measurable fun x : Fin k → ℝ => finPad k x m := by
  unfold finPad
  split_ifs with h
  · exact measurable_pi_apply _
  · exact measurable_const

lemma finPad_mono {k : ℕ} {x y : Fin k → ℝ} (hxy : x ≤ y) (m : ℕ) :
    finPad k x m ≤ finPad k y m := by
  unfold finPad
  split_ifs with h
  · exact hxy _
  · exact le_rfl

/-- A walk with coefficients, read off the padded vector of its first `k` increments. -/
lemma walk_eq_sum_finPad {Ω : Type*} (c : ℕ → ℝ) (G : ℕ → Ω → ℝ) {j k : ℕ} (hjk : j ≤ k)
    (ω : Ω) :
    walk (fun m ω => c m * G m ω) j ω
      = ∑ m ∈ Finset.range j, c m * finPad k (fun i : Fin k => G i ω) m := by
  rw [walk_apply]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m < k := lt_of_lt_of_le (Finset.mem_range.1 hm) hjk
  simp [finPad, hmk]

/-- A walk, read off the padded vector of its first `k` increments. -/
lemma walk_eq_sum_finPad_one {Ω : Type*} (G : ℕ → Ω → ℝ) {j k : ℕ} (hjk : j ≤ k) (ω : Ω) :
    walk G j ω = ∑ m ∈ Finset.range j, finPad k (fun i : Fin k => G i ω) m := by
  rw [walk_apply]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m < k := lt_of_lt_of_le (Finset.mem_range.1 hm) hjk
  simp [finPad, hmk]

/-- The floor loss of the height suffix from a start `u ≥ -A - 2B`, linearised as in
`RMF.ofReal_suffixLow_le`: at most `αe^{-u}`. -/
lemma floorLossDepth_start_le {vmin vmax a A B u : ℝ} {N : ℕ} (hB : 2 * vmax < B)
    (hu1 : -A - 2 * B ≤ u) (hu2 : u ≤ a) :
    floorLossDepth (A + 2 * B + u) B vmin vmax N (a - u)
      ≤ Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
          * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
          / (√(N : ℝ) * (Real.exp ((B - 2 * vmax) / 2) - 1)) * Real.exp (-u) := by
  have hden : 0 ≤ √(N : ℝ) * (Real.exp ((B - 2 * vmax) / 2) - 1) :=
    mul_nonneg (Real.sqrt_nonneg _)
      (by have := Real.one_le_exp (show 0 ≤ (B - 2 * vmax) / 2 by linarith); linarith)
  have hM : 0 ≤ max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax))) :=
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  unfold floorLossDepth
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ a - u)]
  have he : Real.exp (-(A + 2 * B + u)) = Real.exp (-(A + 2 * B)) * Real.exp (-u) := by
    rw [← Real.exp_add]
    ring_nf
  rw [he, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ hden
  have hE : 0 ≤ Real.exp (-(A + 2 * B)) * Real.exp (-u) := by positivity
  calc Real.exp (-(A + 2 * B)) * Real.exp (-u) * (a - u + √(π * vmax / 2) + 2)
        * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
      ≤ Real.exp (-(A + 2 * B)) * Real.exp (-u) * (a + A + 2 * B + √(π * vmax / 2) + 2)
        * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax))) := by
        gcongr
        linarith
    _ = _ := by ring

/-- The last step of `RMF.ofReal_le_measure_hp1SuffixV2`, as real arithmetic: from
`c·b - e ≤ P`, `q + e ≤ c`, `g ≤ q`, `e ≤ φ` and `0 ≤ X ≤ b ≤ 1`, `(g + φ)X - φ ≤ P`. -/
lemma hp1SuffixV2_arith {P c q e b g φ X : ℝ} (hP : c * b - e ≤ P) (hc : q + e ≤ c)
    (hq : g ≤ q) (he : e ≤ φ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hX : X ≤ b) (hX0 : 0 ≤ X)
    (hP0 : 0 ≤ P) (hφ0 : 0 ≤ φ) : (g + φ) * X - φ ≤ P := by
  rcases le_or_gt 0 (g + φ) with h | h
  · have h1 : (g + φ) * X ≤ (g + φ) * b := mul_le_mul_of_nonneg_left hX h
    have h2 : g * b ≤ q * b := mul_le_mul_of_nonneg_right hq hb0
    have h3 : e * (1 - b) ≤ φ * (1 - b) := mul_le_mul_of_nonneg_right he (by linarith)
    have h4 : (q + e) * b ≤ c * b := mul_le_mul_of_nonneg_right hc hb0
    nlinarith
  · have h1 : (g + φ) * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h.le hX0
    linarith

section SuffixV2

variable {Ω₁ Ω₂ : Type*}

/-- **The suffix event of HP1 v2 at a start `(u, y)`**, blocks from `2` on: the height walk from
`u` in its tube `[-A - B(i+2) - u, a - u]`, the slope walk of the blocks `β_m < 0` below `L`, the
real suffix walk from `y` (drifts, residual walk and the slope walk of the blocks `β_m ≥ 0`) below
`-L - ρ`, and the drifted residual walk above its far floor `-(A_W + B_W i)`. -/
def hp1SuffixV2 (Z : ℕ → Ω₁ → ℝ) (W : ℕ → Ω₂ → ℝ) (β d : ℕ → ℝ) (n : ℕ)
    (a A B L ρ AW BW u y : ℝ) : Set (Ω₁ × Ω₂) :=
  {ω | ω.1 ∈ barrierEvent (fun m => Z (m + 2)) (n - 2) (fun i => -A - B * ((i : ℝ) + 2) - u)
      (fun _ => a - u)
    ∧ (∀ i ≤ n - 2, walk (fun m ω => min (β (m + 2)) 0 * Z (m + 2) ω) i ω.1 ≤ L)
    ∧ (∀ i ≤ n - 2, y + driftSum (fun m => d (m + 2)) i + walk (fun m => W (m + 2)) i ω.2
        + walk (fun m ω => max (β (m + 2)) 0 * Z (m + 2) ω) i ω.1 ≤ -L - ρ)
    ∧ ∀ i ≤ n - 2, -(AW + BW * i)
        ≤ walk (fun m => W (m + 2)) i ω.2 + driftSum (fun m => d (m + 2)) i}

variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {Q₁ : Measure Ω₁} {Q₂ : Measure Ω₂}
  [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
  {Z : ℕ → Ω₁ → ℝ} {W : ℕ → Ω₂ → ℝ} {v s : ℕ → ℝ≥0}

/-- **The real suffix walk on the product space**: for Gaussian walks `Z` (variances `v`) on `Q₁`
and `W` (variances `s`) on `Q₂`, the increments `c_mZ_m + W_m` form a Gaussian walk on `Q₁ × Q₂`
with variances `c_m²v_m + s_m`. -/
lemma IsGaussianWalk.mul_add_prod (hZ : IsGaussianWalk Z v Q₁) (hW : IsGaussianWalk W s Q₂)
    (c : ℕ → ℝ) :
    IsGaussianWalk (fun m (ω : Ω₁ × Ω₂) => c m * Z m ω.1 + W m ω.2)
      (fun m => ⟨c m ^ 2, sq_nonneg _⟩ * v m + s m) (Q₁.prod Q₂) where
  measurable m :=
    (((hZ.measurable m).comp measurable_fst).const_mul (c m)).add
      ((hW.measurable m).comp measurable_snd)
  indep :=
    (iIndepFun_pairProd hZ.measurable hW.measurable hZ.indep hW.indep).comp
      (fun m (p : ℝ × ℝ) => c m * p.1 + p.2) (fun m => by fun_prop)
  map_eq m := by
    have hcZ : (Q₁.prod Q₂).map (fun ω => c m * Z m ω.1)
        = gaussianReal 0 (⟨c m ^ 2, sq_nonneg _⟩ * v m) := by
      rw [map_comp_fst_prod ((hZ.measurable m).const_mul (c m))]
      exact (hZ.const_mul c).map_eq m
    have hW' : (Q₁.prod Q₂).map (fun ω => W m ω.2) = gaussianReal 0 (s m) := by
      rw [map_comp_snd_prod (hW.measurable m), hW.map_eq m]
    have h := gaussianReal_add_gaussianReal_of_indepFun
      (indepFun_comp_fst_snd (fun ω₁ => c m * Z m ω₁) (W m)) hcZ hW'
    rw [add_zero] at h
    exact h

/-- **The exit factor bounds the real suffix from below.**  Started at `y`, the real suffix walk
`y + D_i + W_i + P_i` (drifts, residual walk, and the slope walk `P` with the slopes
`max(β_m, 0)`) stays below `-L - ρ` for `i ≤ n'`, and the drifted residual walk above
`-(A_W + B_W i)`, with probability at least `RMF.hp1ExitV2 … y`: the exponential maximal bound
(`RMF.IsGaussianWalk.measureReal_survivalSet_compl_le_exp_sum`) for the Gaussian walk
`max(β_m, 0)Z_m + W_m` (variances `max(β_m, 0)²v_m + s_m`), and for the floor the same bound at
`t = 1` for `-W`, every step free as `s_m/2 - d_m ≤ B_W`.  Past the start (`y + L + ρ > 0`) the
factor is `0`. -/
theorem le_measureReal_exitV2 (hZ : IsGaussianWalk Z v Q₁) (hW : IsGaussianWalk W s Q₂)
    (β d : ℕ → ℝ) (n' : ℕ) {t L ρ Λ AW BW y : ℝ} (ht : 0 ≤ t) (hAW : 0 ≤ AW)
    (hΛ : ∑ m ∈ Finset.range n',
      max 0 (t * d m + t ^ 2 * (max (β m) 0 ^ 2 * (v m : ℝ) + s m) / 2) ≤ Λ)
    (hBW : ∀ m, m < n' → (s m : ℝ) / 2 - d m ≤ BW) :
    hp1ExitV2 t L ρ Λ AW y
      ≤ (Q₁.prod Q₂).real {ω | (∀ i ≤ n', y + driftSum d i + walk W i ω.2
          + walk (fun m ω => max (β m) 0 * Z m ω) i ω.1 ≤ -L - ρ)
        ∧ ∀ i ≤ n', -(AW + BW * i) ≤ walk W i ω.2 + driftSum d i} := by
  have hΛ0 : 0 ≤ Λ := le_trans (Finset.sum_nonneg fun m _ => le_max_left _ _) hΛ
  set E : Set (Ω₁ × Ω₂) := {ω | (∀ i ≤ n', y + driftSum d i + walk W i ω.2
      + walk (fun m ω => max (β m) 0 * Z m ω) i ω.1 ≤ -L - ρ)
    ∧ ∀ i ≤ n', -(AW + BW * i) ≤ walk W i ω.2 + driftSum d i} with hE
  rcases lt_or_ge 0 (y + L + ρ) with hz | hz
  · -- the ceiling lies below the start: the factor vanishes
    have h0 : hp1ExitV2 t L ρ Λ AW y = 0 := by
      unfold hp1ExitV2
      refine max_eq_right ?_
      have h1 : 1 ≤ Real.exp (t * (y + L + ρ) + Λ) :=
        Real.one_le_exp (add_nonneg (mul_nonneg ht hz.le) hΛ0)
      have h2 := Real.exp_pos (-AW)
      linarith
    rw [h0]
    exact measureReal_nonneg
  set z : ℝ := -(y + L + ρ) with hzdef
  have hz0 : 0 ≤ z := by linarith
  have htz : t * z = -(t * (y + L + ρ)) := by rw [hzdef]; ring
  have hG := hZ.mul_add_prod hW (fun m => max (β m) 0)
  set G : ℕ → Ω₁ × Ω₂ → ℝ := fun m ω => max (β m) 0 * Z m ω.1 + W m ω.2 with hGdef
  set S₁ : Set (Ω₁ × Ω₂) := survivalSet G (fun j => z - driftSum d j) n' with hS₁
  set S₂ : Set Ω₂ := survivalSet (fun m => -W m) (fun j => AW - driftSum (fun m => -d m - BW) j)
    n' with hS₂
  have hS₁m : MeasurableSet S₁ := hG.measurableSet_survivalSet _ n'
  have hS₂m : MeasurableSet S₂ := hW.neg.measurableSet_survivalSet _ n'
  have hsub : S₁ ∩ Prod.snd ⁻¹' S₂ ⊆ E := by
    rintro ω ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have e1 : walk G i ω ≤ z - driftSum d i := h1 i hi
      have hw : walk G i ω = walk (fun m ω => max (β m) 0 * Z m ω) i ω.1 + walk W i ω.2 := by
        simp only [hGdef, walk_apply, Finset.sum_add_distrib]
      rw [hw] at e1
      linarith
    · have e2 : walk (fun m => -W m) i ω.2 ≤ AW - driftSum (fun m => -d m - BW) i := h2 i hi
      have hneg : walk (fun m => -W m) i ω.2 = -walk W i ω.2 := by
        simp only [walk_apply, Pi.neg_apply, Finset.sum_neg_distrib]
      rw [hneg, driftSum_neg_sub] at e2
      linarith
  have hc1 : (Q₁.prod Q₂).real S₁ᶜ ≤ Real.exp (t * (y + L + ρ) + Λ) := by
    refine le_trans (hG.measureReal_survivalSet_compl_le_exp_sum ht hz0 n')
      (Real.exp_le_exp.2 ?_)
    have hsum : ∑ m ∈ Finset.range n', max 0 (t * d m
        + t ^ 2 * (((⟨max (β m) 0 ^ 2, sq_nonneg _⟩ * v m + s m : ℝ≥0)) : ℝ) / 2)
        = ∑ m ∈ Finset.range n',
          max 0 (t * d m + t ^ 2 * (max (β m) 0 ^ 2 * (v m : ℝ) + s m) / 2) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [NNReal.coe_add, NNReal.coe_mul]
      rfl
    rw [hsum]
    linarith
  have hc2 : (Q₁.prod Q₂).real (Prod.snd ⁻¹' S₂)ᶜ ≤ Real.exp (-AW) := by
    have h2 := hW.neg.measureReal_survivalSet_compl_le_exp_sum (d := fun m => -d m - BW)
      (t := 1) (z := AW) zero_le_one hAW n'
    have hsum : ∑ m ∈ Finset.range n', max 0 (1 * (-d m - BW) + 1 ^ 2 * (s m : ℝ) / 2) = 0 := by
      refine Finset.sum_eq_zero fun m hm => max_eq_left ?_
      have := hBW m (Finset.mem_range.1 hm)
      linarith
    rw [hsum, add_zero, one_mul] at h2
    have hpre : (Prod.snd ⁻¹' S₂)ᶜ = (Set.univ : Set Ω₁) ×ˢ S₂ᶜ := by
      ext ω
      simp
    rw [hpre, measureReal_prod_prod, probReal_univ, one_mul]
    exact h2
  have hinter : 1 - (Q₁.prod Q₂).real S₁ᶜ - (Q₁.prod Q₂).real (Prod.snd ⁻¹' S₂)ᶜ
      ≤ (Q₁.prod Q₂).real (S₁ ∩ Prod.snd ⁻¹' S₂) := by
    have hU : (Q₁.prod Q₂).real (S₁ ∩ Prod.snd ⁻¹' S₂)ᶜ
        ≤ (Q₁.prod Q₂).real S₁ᶜ + (Q₁.prod Q₂).real (Prod.snd ⁻¹' S₂)ᶜ := by
      rw [Set.compl_inter]
      exact measureReal_union_le _ _
    have hC : (Q₁.prod Q₂).real (S₁ ∩ Prod.snd ⁻¹' S₂)ᶜ
        = 1 - (Q₁.prod Q₂).real (S₁ ∩ Prod.snd ⁻¹' S₂) := by
      rw [measureReal_compl (hS₁m.inter (measurable_snd hS₂m)), probReal_univ]
    linarith
  unfold hp1ExitV2
  refine max_le ?_ measureReal_nonneg
  calc 1 - Real.exp (t * (y + L + ρ) + Λ) - Real.exp (-AW)
      ≤ 1 - (Q₁.prod Q₂).real S₁ᶜ - (Q₁.prod Q₂).real (Prod.snd ⁻¹' S₂)ᶜ := by linarith
    _ ≤ (Q₁.prod Q₂).real (S₁ ∩ Prod.snd ⁻¹' S₂) := hinter
    _ ≤ (Q₁.prod Q₂).real E := measureReal_mono hsub

/-- **Harris' inequality for the suffix, fibrewise in the residual walk.**  For independent `G`
on `Q₁` and slopes `β`, let `A` be the height event (the walk below `a'`, the slope walk with the
slopes `min(β_m, 0)` below `L`) and `B` the real event (the slope walk with the slopes
`max(β_m, 0)` below a ceiling `h_j(ω₂)` read off `Ω₂`, and `ω₂ ∈ F`).  Then
`Q₁(A)·P(B) ≤ P(A ∩ B)` on `Q₁ × Q₂`: for each `ω₂` both are lower sets along the coordinates
with `β_m ≥ 0` and the second depends on no other coordinate
(`RMF.measureReal_mul_le_measureReal_inter_of_iIndepFun_partial`), then integrate over `ω₂`. -/
theorem measureReal_mul_le_measureReal_inter_harrisV2 {G : ℕ → Ω₁ → ℝ}
    (hGm : ∀ m, Measurable (G m)) (hG : iIndepFun G Q₁) (β : ℕ → ℝ) (k : ℕ) (a' L : ℝ)
    {h : ℕ → Ω₂ → ℝ} (hh : ∀ j, Measurable (h j)) {F : Set Ω₂} (hF : MeasurableSet F) :
    Q₁.real {ω₁ | (∀ j ≤ k, walk G j ω₁ ≤ a')
        ∧ ∀ j ≤ k, walk (fun m ω => min (β m) 0 * G m ω) j ω₁ ≤ L}
      * (Q₁.prod Q₂).real {ω | (∀ j ≤ k,
          walk (fun m ω => max (β m) 0 * G m ω) j ω.1 ≤ h j ω.2) ∧ ω.2 ∈ F}
      ≤ (Q₁.prod Q₂).real {ω | ((∀ j ≤ k, walk G j ω.1 ≤ a')
          ∧ ∀ j ≤ k, walk (fun m ω => min (β m) 0 * G m ω) j ω.1 ≤ L)
        ∧ (∀ j ≤ k, walk (fun m ω => max (β m) 0 * G m ω) j ω.1 ≤ h j ω.2) ∧ ω.2 ∈ F} := by
  classical
  set A : Set Ω₁ := {ω₁ | (∀ j ≤ k, walk G j ω₁ ≤ a')
      ∧ ∀ j ≤ k, walk (fun m ω => min (β m) 0 * G m ω) j ω₁ ≤ L} with hA
  set Bs : Ω₂ → Set Ω₁ := fun ω₂ => {ω₁ | ∀ j ≤ k,
      walk (fun m ω => max (β m) 0 * G m ω) j ω₁ ≤ h j ω₂} with hBs
  set EB : Set (Ω₁ × Ω₂) := {ω | (∀ j ≤ k,
      walk (fun m ω => max (β m) 0 * G m ω) j ω.1 ≤ h j ω.2) ∧ ω.2 ∈ F} with hEB
  set EAB : Set (Ω₁ × Ω₂) := {ω | ((∀ j ≤ k, walk G j ω.1 ≤ a')
      ∧ ∀ j ≤ k, walk (fun m ω => min (β m) 0 * G m ω) j ω.1 ≤ L)
    ∧ (∀ j ≤ k, walk (fun m ω => max (β m) 0 * G m ω) j ω.1 ≤ h j ω.2) ∧ ω.2 ∈ F} with hEAB
  -- measurability
  have hwm : ∀ (c : ℕ → ℝ) j, Measurable (walk (fun m ω => c m * G m ω) j) := fun c j =>
    measurable_walk_of (fun m => (hGm m).const_mul (c m)) j
  have hw1 : ∀ j, Measurable (walk G j) := measurable_walk_of hGm
  have hAm : MeasurableSet A := by
    have e : A = (⋂ j ∈ Set.Iic k, {ω₁ | walk G j ω₁ ≤ a'})
        ∩ ⋂ j ∈ Set.Iic k, {ω₁ | walk (fun m ω => min (β m) 0 * G m ω) j ω₁ ≤ L} := by
      ext ω₁
      simp [hA]
    rw [e]
    exact (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
      measurableSet_le (hw1 j) measurable_const).inter
      (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
        measurableSet_le (hwm _ j) measurable_const)
  have hEBm : MeasurableSet EB := by
    have e : EB = (⋂ j ∈ Set.Iic k, {ω : Ω₁ × Ω₂ |
        walk (fun m ω => max (β m) 0 * G m ω) j ω.1 ≤ h j ω.2}) ∩ Prod.snd ⁻¹' F := by
      ext ω
      simp [hEB]
    rw [e]
    exact (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
      measurableSet_le ((hwm _ j).comp measurable_fst) ((hh j).comp measurable_snd)).inter
      (measurable_snd hF)
  have hEABeq : EAB = Prod.fst ⁻¹' A ∩ EB := by
    ext ω
    simp only [hEAB, hEB, hA, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  have hEABm : MeasurableSet EAB := by
    rw [hEABeq]
    exact (measurable_fst hAm).inter hEBm
  -- the vector of the first `k` increments, and the two events as sets of vectors
  have hZki : iIndepFun (fun i : Fin k => G i) Q₁ :=
    hG.precomp (g := fun i : Fin k => (i : ℕ)) Fin.val_injective
  set SA : Set (Fin k → ℝ) := {x | (∀ j ≤ k, ∑ m ∈ Finset.range j, finPad k x m ≤ a')
      ∧ ∀ j ≤ k, ∑ m ∈ Finset.range j, min (β m) 0 * finPad k x m ≤ L} with hSA
  set SB : Ω₂ → Set (Fin k → ℝ) := fun ω₂ => {x | ∀ j ≤ k,
      ∑ m ∈ Finset.range j, max (β m) 0 * finPad k x m ≤ h j ω₂} with hSB
  set p : Fin k → Prop := fun i => 0 ≤ β i with hp
  have hsum : ∀ (c : ℕ → ℝ) j,
      Measurable fun x : Fin k → ℝ => ∑ m ∈ Finset.range j, c m * finPad k x m := fun c j =>
    Finset.measurable_sum _ fun m _ => measurable_const.mul (measurable_finPad k m)
  have hsum1 : ∀ j, Measurable fun x : Fin k → ℝ => ∑ m ∈ Finset.range j, finPad k x m :=
    fun j => Finset.measurable_sum _ fun m _ => measurable_finPad k m
  have hSAm : MeasurableSet SA := by
    have e : SA = (⋂ j ∈ Set.Iic k, {x : Fin k → ℝ | ∑ m ∈ Finset.range j, finPad k x m ≤ a'})
        ∩ ⋂ j ∈ Set.Iic k, {x : Fin k → ℝ |
          ∑ m ∈ Finset.range j, min (β m) 0 * finPad k x m ≤ L} := by
      ext x
      simp [hSA]
    rw [e]
    exact (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
      measurableSet_le (hsum1 j) measurable_const).inter
      (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
        measurableSet_le (hsum _ j) measurable_const)
  have hSBm : ∀ ω₂, MeasurableSet (SB ω₂) := fun ω₂ => by
    have e : SB ω₂ = ⋂ j ∈ Set.Iic k, {x : Fin k → ℝ |
        ∑ m ∈ Finset.range j, max (β m) 0 * finPad k x m ≤ h j ω₂} := by
      ext x
      simp [hSB]
    rw [e]
    exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
      measurableSet_le (hsum _ j) measurable_const
  -- the order properties
  have hSAp : ∀ x y, x ≤ y → (∀ i, ¬ p i → x i = y i) → y ∈ SA → x ∈ SA := by
    rintro x y hxy hq ⟨hy1, hy2⟩
    refine ⟨fun j hj => le_trans (Finset.sum_le_sum fun m _ => finPad_mono hxy m) (hy1 j hj),
      fun j hj => le_of_eq_of_le (Finset.sum_congr rfl fun m _ => ?_) (hy2 j hj)⟩
    by_cases hm : m < k
    · by_cases hβ : 0 ≤ β m
      · rw [min_eq_right hβ, zero_mul, zero_mul]
      · simp only [finPad, dif_pos hm]
        rw [hq ⟨m, hm⟩ hβ]
    · simp [finPad, hm]
  have hSBl : ∀ ω₂, IsLowerSet (SB ω₂) := by
    intro ω₂ x y hyx hx j hj
    exact le_trans (Finset.sum_le_sum fun m _ =>
      mul_le_mul_of_nonneg_left (finPad_mono hyx m) (le_max_right _ _)) (hx j hj)
  have hSBp : ∀ ω₂ x y, (∀ i, p i → x i = y i) → x ∈ SB ω₂ → y ∈ SB ω₂ := by
    intro ω₂ x y hq hx j hj
    refine le_of_eq_of_le (Finset.sum_congr rfl fun m _ => ?_) (hx j hj)
    by_cases hm : m < k
    · by_cases hβ : 0 ≤ β m
      · simp only [finPad, dif_pos hm]
        rw [hq ⟨m, hm⟩ hβ]
      · rw [max_eq_right (le_of_lt (not_le.1 hβ)), zero_mul, zero_mul]
    · simp [finPad, hm]
  -- fibrewise Harris
  have hfib : ∀ ω₂, Q₁.real A * Q₁.real (Bs ω₂) ≤ Q₁.real (A ∩ Bs ω₂) := by
    intro ω₂
    have hH := measureReal_mul_le_measureReal_inter_of_iIndepFun_partial (fun i => hGm i) hZki p
      hSAp (hSBl ω₂) (hSBp ω₂) hSAm (hSBm ω₂)
    have eA : {ω₁ | (fun i : Fin k => G i ω₁) ∈ SA} = A := by
      ext ω₁
      simp only [Set.mem_setOf_eq, hSA, hA]
      refine and_congr (forall_congr' fun j => forall_congr' fun hj => ?_)
        (forall_congr' fun j => forall_congr' fun hj => ?_)
      · rw [walk_eq_sum_finPad_one G hj ω₁]
      · rw [walk_eq_sum_finPad _ G hj ω₁]
    have eB : {ω₁ | (fun i : Fin k => G i ω₁) ∈ SB ω₂} = Bs ω₂ := by
      ext ω₁
      simp only [Set.mem_setOf_eq, hSB, hBs]
      refine forall_congr' fun j => forall_congr' fun hj => ?_
      rw [walk_eq_sum_finPad _ G hj ω₁]
    rw [eA, eB] at hH
    exact hH
  -- the slices
  have hsB : ∀ ω₂, Q₁ ((fun ω₁ => (ω₁, ω₂)) ⁻¹' EB) = F.indicator (fun ω₂ => Q₁ (Bs ω₂)) ω₂ := by
    intro ω₂
    by_cases hω₂ : ω₂ ∈ F
    · rw [Set.indicator_of_mem hω₂]
      congr 1
      ext ω₁
      simp [hEB, hBs, hω₂]
    · rw [Set.indicator_of_notMem hω₂]
      have he : (fun ω₁ => (ω₁, ω₂)) ⁻¹' EB = ∅ := by
        ext ω₁
        simp [hEB, hω₂]
      rw [he, measure_empty]
  have hsAB : ∀ ω₂, Q₁ ((fun ω₁ => (ω₁, ω₂)) ⁻¹' EAB)
      = F.indicator (fun ω₂ => Q₁ (A ∩ Bs ω₂)) ω₂ := by
    intro ω₂
    by_cases hω₂ : ω₂ ∈ F
    · rw [Set.indicator_of_mem hω₂]
      congr 1
      ext ω₁
      simp [hEAB, hBs, hA, hω₂]
    · rw [Set.indicator_of_notMem hω₂]
      have he : (fun ω₁ => (ω₁, ω₂)) ⁻¹' EAB = ∅ := by
        ext ω₁
        simp [hEAB, hω₂]
      rw [he, measure_empty]
  -- integrate over `ω₂`
  have hle : Q₁ A * (Q₁.prod Q₂) EB ≤ (Q₁.prod Q₂) EAB := by
    rw [Measure.prod_apply_symm hEBm, Measure.prod_apply_symm hEABm,
      ← lintegral_const_mul' _ _ (measure_ne_top _ _)]
    refine lintegral_mono fun ω₂ => ?_
    rw [hsB ω₂, hsAB ω₂]
    by_cases hω₂ : ω₂ ∈ F
    · rw [Set.indicator_of_mem hω₂, Set.indicator_of_mem hω₂,
        ← ofReal_measureReal (measure_ne_top Q₁ A),
        ← ofReal_measureReal (measure_ne_top Q₁ (Bs ω₂)),
        ← ofReal_measureReal (measure_ne_top Q₁ (A ∩ Bs ω₂)),
        ← ENNReal.ofReal_mul measureReal_nonneg]
      exact ENNReal.ofReal_le_ofReal (hfib ω₂)
    · rw [Set.indicator_of_notMem hω₂, Set.indicator_of_notMem hω₂, mul_zero]
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hle
  rw [ENNReal.toReal_mul] at hreal
  exact hreal

/-- **The suffix of HP1 v2 from a start `(u, y)`, from below.**  For a start `u` of the box,
`((κ - K_rP_R)(a - u) - γ)·RMF.hp1ExitV2(y) - αe^{-u}` bounds the probability of
`RMF.hp1SuffixV2`, with `κ, K_r, P_R, α, γ` of `RMF.ofReal_suffixLow_le` at horizon `n - 2` and the
slope sums over the blocks `β_m < 0` only.  Let `T_c` be the height walk below `a - u` (no floor),
`R⁻` the slope walk of the blocks `β_m < 0` below `L`, `E` the real event: Harris gives
`P(T_c ∩ R⁻ ∩ E) ≥ Q₁(T_c ∩ R⁻)·P(E)` (`RMF.measureReal_mul_le_measureReal_inter_harrisV2`),
`P(E) ≥ RMF.hp1ExitV2(y)` (`RMF.le_measureReal_exitV2`), and the floor is paid relatively and once:
`Q₁(T_c ∩ R⁻) ≥ Q₁(T ∩ R⁻) + e` with `e` the floor-breaching part (`e ≤ αe^{-u}`,
`RMF.IsGaussianWalk.measure_inter_floorBreach_le_depth`), `Q₁(T ∩ R⁻)` bounded by
`RMF.ofReal_suffixLow_le`, and `e` subtracted once. -/
theorem ofReal_le_measure_hp1SuffixV2 (hZ : IsGaussianWalk Z v Q₁) (hW : IsGaussianWalk W s Q₂)
    (β d : ℕ → ℝ) {n m₀ : ℕ} (hm₀ : m₀ + 3 ≤ n)
    {vmin vmax a A B L Klate σR2 t ρ Λ AW BW u y : ℝ} (hvmin : 0 < vmin)
    (hvb : ∀ m, 2 ≤ m → vmin ≤ (v m : ℝ) ∧ (v m : ℝ) ≤ vmax) (ha : 0 ≤ a) (hA : 0 ≤ A)
    (hB : 2 * vmax < B) (hCn : (a + A + 2 * B) ^ 2 ≤ 2 * (((n - 2 : ℕ) : ℝ) * vmin))
    (hKlate : ∑ m ∈ Finset.Ico (m₀ + 2) n,
      |min (β m) 0| * ((a + A + B * m) + (a + A + B * (m + 1))) ≤ Klate) (hKL : Klate ≤ L)
    (hσR : ∑ m ∈ Finset.Ico 2 (m₀ + 2), min (β m) 0 ^ 2 * (v m : ℝ) ≤ σR2) (hσR0 : 0 < σR2)
    (ht : 0 ≤ t) (hAW : 0 ≤ AW)
    (hΛ : ∑ m ∈ Finset.Ico 2 n,
      max 0 (t * d m + t ^ 2 * (max (β m) 0 ^ 2 * (v m : ℝ) + s m) / 2) ≤ Λ)
    (hBW : ∀ m, 2 ≤ m → m < n → (s m : ℝ) / 2 - d m ≤ BW)
    (hu : u ∈ Set.Icc (-A - 2 * B) a) :
    ENNReal.ofReal (((2 * (1 - (a + A + 2 * B) ^ 2 / (2 * (((n - 2 : ℕ) : ℝ) * vmin)))
              / √(2 * π * (((n - 2 : ℕ) : ℝ) * vmax))
            - √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin)))
              * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))) * (a - u)
          - √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin)))
            * (√(π * vmax / 2) * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))
              + √(Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * ((m₀ : ℝ) * vmax))))
          * hp1ExitV2 t L ρ Λ AW y
        - Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
            * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
            / (√((n - 2 : ℕ) : ℝ) * (Real.exp ((B - 2 * vmax) / 2) - 1)) * Real.exp (-u))
      ≤ (Q₁.prod Q₂) (hp1SuffixV2 Z W β d n a A B L ρ AW BW u y) := by
  obtain ⟨hu1, hu2⟩ := hu
  have hvmax : 0 < vmax := lt_of_lt_of_le hvmin (le_trans (hvb 2 le_rfl).1 (hvb 2 le_rfl).2)
  have hB0 : 0 ≤ B := by linarith
  -- the constants
  set κn := 2 * (1 - (a + A + 2 * B) ^ 2 / (2 * (((n - 2 : ℕ) : ℝ) * vmin)))
    / √(2 * π * (((n - 2 : ℕ) : ℝ) * vmax)) with hκn
  set Kr := √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin))) with hKr
  set PR := Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) with hPR
  set α := Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
    * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
    / (√((n - 2 : ℕ) : ℝ) * (Real.exp ((B - 2 * vmax) / 2) - 1)) with hα
  set γ := Kr * (√(π * vmax / 2) * PR + √(PR * ((m₀ : ℝ) * vmax))) with hγ
  have hα0 : 0 ≤ α := by
    have hMx0 : 0 ≤ max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax))) :=
      le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
    have hEb0 : 0 ≤ Real.exp ((B - 2 * vmax) / 2) - 1 := by
      have := Real.one_le_exp (show 0 ≤ (B - 2 * vmax) / 2 by linarith)
      linarith
    exact div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (by have := Real.sqrt_nonneg (π * vmax / 2); linarith)) hMx0)
      (mul_nonneg (Real.sqrt_nonneg _) hEb0)
  -- the suffix walks
  set n' := n - 2 with hn'
  have hn'1 : 1 ≤ n' := by omega
  set G : ℕ → Ω₁ → ℝ := fun m => Z (m + 2) with hGdef
  have hG : IsGaussianWalk G (fun m => v (m + 2)) Q₁ := hZ.shift 2
  have hv : VarBracket (fun m => v (m + 2)) vmin vmax :=
    ⟨hvmin, fun i => (hvb (i + 2) (by omega)).1, fun i => (hvb (i + 2) (by omega)).2⟩
  set lo : ℕ → ℝ := fun i => -A - B * ((i : ℝ) + 2) - u with hlo
  set T : Set Ω₁ := barrierEvent G n' lo (fun _ => a - u) with hT
  set Rn : Set Ω₁ := {ω₁ | ∀ i ≤ n', walk (fun m ω => min (β (m + 2)) 0 * G m ω) i ω₁ ≤ L}
    with hRn
  set Tc : Set Ω₁ := {ω₁ | ∀ j ≤ n', walk G j ω₁ ≤ a - u} with hTc
  set fb : Set Ω₁ := floorBreach G n' lo with hfb
  set Ev : Set (Ω₁ × Ω₂) := {ω | (∀ i ≤ n', y + driftSum (fun m => d (m + 2)) i
      + walk (fun m => W (m + 2)) i ω.2 + walk (fun m ω => max (β (m + 2)) 0 * G m ω) i ω.1
        ≤ -L - ρ)
    ∧ ∀ i ≤ n', -(AW + BW * i) ≤ walk (fun m => W (m + 2)) i ω.2
      + driftSum (fun m => d (m + 2)) i} with hEv
  set Suf : Set (Ω₁ × Ω₂) := hp1SuffixV2 Z W β d n a A B L ρ AW BW u y with hSuf
  -- measurability
  have hwm : ∀ (c : ℕ → ℝ) j, Measurable (walk (fun m ω => c m * G m ω) j) := fun c j =>
    measurable_walk_of (fun m => (hG.measurable m).const_mul (c m)) j
  have hTm : MeasurableSet T := measurableSet_barrierEvent hG.measurable n' _ _
  have hRnm : MeasurableSet Rn := by
    have e : Rn = ⋂ i ∈ Set.Iic n',
        {ω₁ | walk (fun m ω => min (β (m + 2)) 0 * G m ω) i ω₁ ≤ L} := by
      ext ω₁
      simp [hRn]
    rw [e]
    exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
      measurableSet_le (hwm _ i) measurable_const
  have hTcm : MeasurableSet Tc := by
    have e : Tc = ⋂ j ∈ Set.Iic n', {ω₁ | walk G j ω₁ ≤ a - u} := by
      ext ω₁
      simp [hTc]
    rw [e]
    exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
      measurableSet_le (hG.measurable_walk j) measurable_const
  have hfbm : MeasurableSet fb := by
    have e : fb = ⋃ j ∈ Set.Icc 1 n', {ω₁ | walk G j ω₁ < lo j} := by
      ext ω₁
      simp only [hfb, floorBreach, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc, exists_prop]
      constructor
      · rintro ⟨j, h1, h2, h3⟩
        exact ⟨j, ⟨h1, h2⟩, h3⟩
      · rintro ⟨j, ⟨h1, h2⟩, h3⟩
        exact ⟨j, h1, h2, h3⟩
    rw [e]
    exact MeasurableSet.biUnion (Set.to_countable _) fun j _ =>
      measurableSet_lt (hG.measurable_walk j) measurable_const
  -- (i) the height suffix, with the slopes `min(β_m, 0)`
  have h1 := ofReal_suffixLow_le hZ (fun m => min (β m) 0) hm₀ hvmin hvb ha hA hB hCn hKlate hKL
    hσR hσR0 ⟨hu1, hu2⟩ (Q₁ := Q₁)
  have hq : (κn - Kr * PR) * (a - u) - (α * Real.exp (-u) + γ) ≤ Q₁.real (T ∩ Rn) := by
    rcases le_or_gt ((κn - Kr * PR) * (a - u) - (α * Real.exp (-u) + γ)) 0 with hg | hg
    · exact le_trans hg measureReal_nonneg
    · exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h1
  -- (ii) the floor-breaching part
  have hfloorE : Q₁ (Tc ∩ fb) ≤ ENNReal.ofReal (floorLossDepth (A + 2 * B + u) B vmin vmax n'
      (a - u)) :=
    hG.measure_inter_floorBreach_le_depth hv hn'1 (a - u) (by linarith) hB fun i _ => by
      simp only [hlo]
      linarith
  have he : Q₁.real (Tc ∩ Rn ∩ fb) ≤ α * Real.exp (-u) := by
    have h2 : Q₁.real (Tc ∩ fb) ≤ floorLossDepth (A + 2 * B + u) B vmin vmax n' (a - u) :=
      ENNReal.toReal_le_of_le_ofReal (floorLossDepth_nonneg hB _ _) hfloorE
    have h3 := floorLossDepth_start_le (vmin := vmin) (N := n') hB hu1 hu2
    refine le_trans (measureReal_mono ?_) (le_trans h2 h3)
    rintro ω₁ ⟨⟨h4, -⟩, h5⟩
    exact ⟨h4, h5⟩
  -- (iii) `Q₁(T_c ∩ R⁻) ≥ Q₁(T ∩ R⁻) + e`
  have hTsub : T ⊆ Tc := by
    intro ω₁ hω j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · simp only [walk_zero, Pi.zero_apply]
      linarith
    · exact (hω j hj1 hj).2
  have hsplit : Q₁.real (T ∩ Rn) + Q₁.real (Tc ∩ Rn ∩ fb) ≤ Q₁.real (Tc ∩ Rn) := by
    have hdisj : Disjoint (T ∩ Rn) (Tc ∩ Rn ∩ fb) := by
      rw [Set.disjoint_left]
      rintro ω₁ ⟨hT', -⟩ ⟨-, j, hj1, hjn, hlt⟩
      have := (hT' j hj1 hjn).1
      linarith
    rw [← measureReal_union hdisj ((hTcm.inter hRnm).inter hfbm)]
    refine measureReal_mono (Set.union_subset ?_ ?_)
    · exact fun ω₁ hω => ⟨hTsub hω.1, hω.2⟩
    · exact fun ω₁ hω => hω.1
  -- (iv) the real event and Harris
  have hEvm : MeasurableSet Ev := by
    have e : Ev = (⋂ i ∈ Set.Iic n', {ω : Ω₁ × Ω₂ | y + driftSum (fun m => d (m + 2)) i
        + walk (fun m => W (m + 2)) i ω.2 + walk (fun m ω => max (β (m + 2)) 0 * G m ω) i ω.1
          ≤ -L - ρ})
        ∩ ⋂ i ∈ Set.Iic n', {ω : Ω₁ × Ω₂ | -(AW + BW * i) ≤ walk (fun m => W (m + 2)) i ω.2
          + driftSum (fun m => d (m + 2)) i} := by
      ext ω
      simp [hEv]
    rw [e]
    have hWs := hW.shift 2
    refine (MeasurableSet.biInter (Set.to_countable _) fun i _ => ?_).inter
      (MeasurableSet.biInter (Set.to_countable _) fun i _ => ?_)
    · exact measurableSet_le (((measurable_const.add ((hWs.measurable_walk i).comp
        measurable_snd))).add ((hwm _ i).comp measurable_fst)) measurable_const
    · exact measurableSet_le measurable_const (((hWs.measurable_walk i).comp
        measurable_snd).add measurable_const)
  have hexit := le_measureReal_exitV2 hG (hW.shift 2) (fun m => β (m + 2)) (fun m => d (m + 2))
    n' (t := t) (L := L) (ρ := ρ) (y := y) ht hAW (by
      refine le_trans (le_of_eq ?_) hΛ
      rw [Finset.sum_Ico_eq_sum_range, show n - 2 = n' from rfl]
      exact Finset.sum_congr rfl fun k _ => by rw [add_comm k 2])
    (fun m hm => hBW (m + 2) (by omega) (by omega))
  have hharris := measureReal_mul_le_measureReal_inter_harrisV2 (Q₂ := Q₂) hG.measurable
    hG.indep (fun m => β (m + 2)) n' (a - u) L
    (h := fun i ω₂ => -L - ρ - y - driftSum (fun m => d (m + 2)) i
      - walk (fun m => W (m + 2)) i ω₂)
    (fun i => (measurable_const.sub ((hW.shift 2).measurable_walk i)))
    (F := {ω₂ | ∀ i ≤ n', -(AW + BW * i) ≤ walk (fun m => W (m + 2)) i ω₂
      + driftSum (fun m => d (m + 2)) i}) (by
        have e : {ω₂ | ∀ i ≤ n', -(AW + BW * i) ≤ walk (fun m => W (m + 2)) i ω₂
            + driftSum (fun m => d (m + 2)) i} = ⋂ i ∈ Set.Iic n', {ω₂ | -(AW + BW * i)
              ≤ walk (fun m => W (m + 2)) i ω₂ + driftSum (fun m => d (m + 2)) i} := by
          ext ω₂
          simp
        rw [e]
        exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
          measurableSet_le measurable_const (((hW.shift 2).measurable_walk i).add
            measurable_const))
  have eA : {ω₁ | (∀ j ≤ n', walk G j ω₁ ≤ a - u)
      ∧ ∀ j ≤ n', walk (fun m ω => min ((fun m => β (m + 2)) m) 0 * G m ω) j ω₁ ≤ L}
      = Tc ∩ Rn := rfl
  have eB : {ω : Ω₁ × Ω₂ | (∀ j ≤ n', walk (fun m ω => max ((fun m => β (m + 2)) m) 0 * G m ω)
      j ω.1 ≤ (fun i ω₂ => -L - ρ - y - driftSum (fun m => d (m + 2)) i
        - walk (fun m => W (m + 2)) i ω₂) j ω.2)
      ∧ ω.2 ∈ {ω₂ | ∀ i ≤ n', -(AW + BW * i) ≤ walk (fun m => W (m + 2)) i ω₂
        + driftSum (fun m => d (m + 2)) i}} = Ev := by
    ext ω
    simp only [hEv, Set.mem_setOf_eq]
    refine and_congr (forall_congr' fun i => forall_congr' fun hi => ?_) Iff.rfl
    constructor <;> intro hh <;> linarith
  have eAB : {ω : Ω₁ × Ω₂ | ((∀ j ≤ n', walk G j ω.1 ≤ a - u)
      ∧ ∀ j ≤ n', walk (fun m ω => min ((fun m => β (m + 2)) m) 0 * G m ω) j ω.1 ≤ L)
      ∧ (∀ j ≤ n', walk (fun m ω => max ((fun m => β (m + 2)) m) 0 * G m ω) j ω.1
        ≤ (fun i ω₂ => -L - ρ - y - driftSum (fun m => d (m + 2)) i
          - walk (fun m => W (m + 2)) i ω₂) j ω.2)
      ∧ ω.2 ∈ {ω₂ | ∀ i ≤ n', -(AW + BW * i) ≤ walk (fun m => W (m + 2)) i ω₂
        + driftSum (fun m => d (m + 2)) i}} = Prod.fst ⁻¹' (Tc ∩ Rn) ∩ Ev := by
    ext ω
    simp only [hEv, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, hTc, hRn]
    refine and_congr Iff.rfl (and_congr (forall_congr' fun i => forall_congr' fun hi => ?_)
      Iff.rfl)
    constructor <;> intro hh <;> linarith
  rw [eA, eB, eAB] at hharris
  -- (v) the event without the floor-breaching part lies in the suffix event
  have hcover : Prod.fst ⁻¹' (Tc ∩ Rn) ∩ Ev ⊆ Suf ∪ Prod.fst ⁻¹' (Tc ∩ Rn ∩ fb) := by
    rintro ω ⟨⟨hTc', hRn'⟩, hEv'⟩
    by_cases hfb' : ω.1 ∈ fb
    · exact Or.inr ⟨⟨hTc', hRn'⟩, hfb'⟩
    · left
      refine ⟨fun j hj1 hjn => ⟨?_, hTc' j hjn⟩, hRn', hEv'.1, hEv'.2⟩
      by_contra hlt
      exact hfb' ⟨j, hj1, hjn, lt_of_not_ge hlt⟩
  have hSufm : MeasurableSet Suf := by
    have e : Suf = Prod.fst ⁻¹' (T ∩ Rn) ∩ Ev := by
      ext ω
      simp only [hSuf, hp1SuffixV2, hEv, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
        hT, hRn]
      exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩, fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩
    rw [e]
    exact (measurable_fst (hTm.inter hRnm)).inter hEvm
  have hfst : (Q₁.prod Q₂).real (Prod.fst ⁻¹' (Tc ∩ Rn ∩ fb)) = Q₁.real (Tc ∩ Rn ∩ fb) := by
    have e : Prod.fst ⁻¹' (Tc ∩ Rn ∩ fb) = (Tc ∩ Rn ∩ fb) ×ˢ (Set.univ : Set Ω₂) := by
      ext ω
      simp
    rw [e, measureReal_prod_prod, probReal_univ, mul_one]
  have hP : Q₁.real (Tc ∩ Rn) * (Q₁.prod Q₂).real Ev - Q₁.real (Tc ∩ Rn ∩ fb)
      ≤ (Q₁.prod Q₂).real Suf := by
    have h6 := le_trans hharris (measureReal_mono hcover)
    have h7 := measureReal_union_le (μ := Q₁.prod Q₂) Suf (Prod.fst ⁻¹' (Tc ∩ Rn ∩ fb))
    rw [hfst] at h7
    linarith
  -- (vi) the arithmetic
  have hfinal := hp1SuffixV2_arith hP hsplit hq he measureReal_nonneg measureReal_le_one hexit
    (hp1ExitV2_nonneg _ _ _ _ _ _) measureReal_nonneg (mul_nonneg hα0 (Real.exp_pos _).le)
  refine ENNReal.ofReal_le_of_le_toReal (le_trans (le_of_eq ?_) hfinal)
  ring

end SuffixV2

/-! ### The window event, v2 -/

section AssemblyV2

variable {Ω₁ Ω₂ : Type*}

/-- **The window event contains the start box and the suffix event of v2.**  If the start box
holds (`Z₀`, `U₂`, `V₁`, and `V₂ ≥ -K₂`) and `RMF.hp1SuffixV2` holds at `(U₂, V₂)`, the two-sided
window event holds: from `j = 2` on the real walk is `V₂ + (drift + residual + P) + N`, with `P`,
`N` the slope walks of the blocks `β_m ≥ 0`, `β_m < 0`, so it is at most `-L - ρ + L`; and on the
tube the whole slope walk `P + N` is at least `-K_R`, which the far floor `-A' - B'j` absorbs. -/
theorem mem_hp1Event_of_partsV2 {Z : ℕ → Ω₁ → ℝ} {W : ℕ → Ω₂ → ℝ} {β d : ℕ → ℝ} {n : ℕ}
    {a A B A' B' M₁ K₂ ρ L AW BW KR : ℝ} (hn2 : 2 ≤ n) (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hKR : ∑ m ∈ Finset.Ico 2 n, |β m| * ((a + A + B * m) + (a + A + B * (m + 1))) ≤ KR)
    (hA' : K₂ + KR + AW ≤ A') (hBW' : BW ≤ B') (hB'0 : 0 ≤ B')
    {ω : Ω₁ × Ω₂}
    (hg : Z 0 ω.1 ∈ Set.Icc (-A - B) a ∧ Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a
      ∧ |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁
      ∧ -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2))
    (hs : ω ∈ hp1SuffixV2 Z W β d n a A B L ρ AW BW (Z 0 ω.1 + Z 1 ω.1)
      ((d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2))) :
    ω ∈ barrierEventPair (fun m ω => ((Z m ω.1, d m + β m * Z m ω.1 + W m ω.2) : ℝ × ℝ)) n
      (fun j => -A - B * j) (fun _ => a)
      (fun j => if j = 1 then -M₁ else -A' - B' * j) (fun j => if j = 1 then M₁ else -ρ) := by
  obtain ⟨hz0, hu2, hv1, hv2⟩ := hg
  obtain ⟨hT, hRn, hRc, hWf⟩ := hs
  set u := Z 0 ω.1 + Z 1 ω.1 with hu
  -- the height tube at every step
  have hU : ∀ j, 1 ≤ j → j ≤ n → -A - B * j ≤ walk Z j ω.1 ∧ walk Z j ω.1 ≤ a := by
    intro j hj1 hjn
    rcases Nat.lt_or_ge j 3 with hj3 | hj3
    · interval_cases j
      · simp only [walk_apply, Finset.sum_range_one, Nat.cast_one, mul_one]
        exact ⟨hz0.1, hz0.2⟩
      · have e : walk Z 2 ω.1 = u := by simp [walk_apply, Finset.sum_range_succ, hu]
        rw [e]
        push_cast
        exact ⟨by linarith [hu2.1], hu2.2⟩
    · obtain ⟨i, rfl⟩ : ∃ i, j = 2 + i := ⟨j - 2, by omega⟩
      have hb := hT i (by omega) (by omega)
      rw [Set.mem_Icc] at hb
      rw [walk_two_add]
      push_cast
      constructor <;> linarith [hb.1, hb.2]
  -- the whole slope walk is at least `-K_R` on the tube
  have hslope : ∀ i ≤ n - 2, -KR ≤ walk (fun m ω => β (m + 2) * Z (m + 2) ω) i ω.1 := by
    intro i hi
    have hinc : ∀ m, m < n - 2 → |Z (m + 2) ω.1|
        ≤ (a + A + B * ((m + 2 : ℕ) : ℝ)) + (a + A + B * ((m + 2 : ℕ) + 1 : ℝ)) := by
      intro m hm
      have e : Z (m + 2) ω.1 = walk Z (m + 3) ω.1 - walk Z (m + 2) ω.1 := by
        rw [show m + 3 = (m + 2) + 1 by omega, walk_succ, Pi.add_apply]
        ring
      have h1 := hU (m + 3) (by omega) (by omega)
      have h2 := hU (m + 2) (by omega) (by omega)
      rw [e, abs_le]
      push_cast at h1 h2 ⊢
      constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
    have hsum : |walk (fun m ω => β (m + 2) * Z (m + 2) ω) i ω.1|
        ≤ ∑ m ∈ Finset.Ico 2 n, |β m| * ((a + A + B * m) + (a + A + B * (m + 1))) := by
      rw [walk_apply]
      calc |∑ m ∈ Finset.range i, β (m + 2) * Z (m + 2) ω.1|
          ≤ ∑ m ∈ Finset.range i, |β (m + 2) * Z (m + 2) ω.1| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.range i, |β (m + 2)|
              * ((a + A + B * ((m + 2 : ℕ) : ℝ)) + (a + A + B * ((m + 2 : ℕ) + 1 : ℝ))) := by
            refine Finset.sum_le_sum fun m hm => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hinc m (by
              have := Finset.mem_range.1 hm; omega)) (abs_nonneg _)
        _ = ∑ m ∈ Finset.Ico 2 (2 + i), |β m| * ((a + A + B * m) + (a + A + B * (m + 1))) := by
            rw [Finset.sum_Ico_eq_sum_range, show 2 + i - 2 = i by omega]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [add_comm 2 m]
        _ ≤ ∑ m ∈ Finset.Ico 2 n, |β m| * ((a + A + B * m) + (a + A + B * (m + 1))) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right
              (by omega)) fun m _ _ => mul_nonneg (abs_nonneg _) ?_
            have : (0 : ℝ) ≤ B * m := mul_nonneg hB (Nat.cast_nonneg m)
            nlinarith
    have := neg_abs_le (walk (fun m ω => β (m + 2) * Z (m + 2) ω) i ω.1)
    linarith
  -- the slope walk splits by the sign of the slopes
  have hsplit : ∀ i, walk (fun m ω => β (m + 2) * Z (m + 2) ω) i ω.1
      = walk (fun m ω => max (β (m + 2)) 0 * Z (m + 2) ω) i ω.1
        + walk (fun m ω => min (β (m + 2)) 0 * Z (m + 2) ω) i ω.1 := by
    intro i
    simp only [walk_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← add_mul, max_add_min, add_zero]
  constructor
  · intro j hj1 hjn
    rw [walk_hp1_fst, Set.mem_Icc]
    exact hU j hj1 hjn
  · intro j hj1 hjn
    rw [walk_hp1_snd, Set.mem_Icc]
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have hj : j = 1 := by omega
      subst hj
      simp only [if_true]
      have e : driftSum d 1 + walk (fun m ω => β m * Z m ω) 1 ω.1 + walk W 1 ω.2
          = d 0 + β 0 * Z 0 ω.1 + W 0 ω.2 := by
        simp [driftSum, walk_apply]
      rw [e]
      exact abs_le.1 hv1
    · have hj1' : j ≠ 1 := by omega
      simp only [hj1', if_false]
      obtain ⟨i, rfl⟩ : ∃ i, j = 2 + i := ⟨j - 2, by omega⟩
      have hi : i ≤ n - 2 := by omega
      rw [driftSum_two_add, walk_two_add, walk_two_add]
      have hc := hRc i hi
      have hn' := hRn i hi
      have hw := hWf i hi
      have hs := hslope i hi
      have hsp := hsplit i
      have hBi : BW * (i : ℝ) ≤ B' * ((2 + i : ℕ) : ℝ) := by
        push_cast
        rcases le_total 0 BW with hBW0 | hBW0
        · nlinarith [Nat.cast_nonneg (α := ℝ) i]
        · nlinarith [Nat.cast_nonneg (α := ℝ) i]
      constructor <;> linarith

variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {Q₁ : Measure Ω₁} {Q₂ : Measure Ω₂}
  [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
  {Z : ℕ → Ω₁ → ℝ} {W : ℕ → Ω₂ → ℝ} {v s : ℕ → ℝ≥0}

/-- **Conditioning on the start, v2.**  The start `(Z₀, Z₁, W₀, W₁)` is independent of the
suffixes (`RMF.iIndepFun_pairProd`, `iIndepFun.indepFun_finset`); given the start `(u, y)`, the
suffix event is `RMF.hp1SuffixV2 … u y`, whose probability is bounded below by a measurable `g`
(any `g` with `ofReal (g (u, y)) ≤ P(RMF.hp1SuffixV2 … u y)` on the start box).  So the window
event has probability at least `E[1_{start box} g(U₂, V₂)⁺]`
(`RMF.measure_preimage_prod_eq_lintegral`, `RMF.mem_hp1Event_of_partsV2`). -/
theorem lintegral_start_le_measureV2 (hZ : IsGaussianWalk Z v Q₁) (hW : IsGaussianWalk W s Q₂)
    (β d : ℕ → ℝ) {n : ℕ} (hn2 : 2 ≤ n)
    {a A B A' B' M₁ K₂ ρ L AW BW KR : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hKR : ∑ m ∈ Finset.Ico 2 n, |β m| * ((a + A + B * m) + (a + A + B * (m + 1))) ≤ KR)
    (hA' : K₂ + KR + AW ≤ A') (hBW' : BW ≤ B') (hB'0 : 0 ≤ B')
    {g : ℝ × ℝ → ℝ} (hgm : Measurable g)
    (hg : ∀ u ∈ Set.Icc (-A - 2 * B) a, ∀ y, ENNReal.ofReal (g (u, y))
      ≤ (Q₁.prod Q₂) (hp1SuffixV2 Z W β d n a A B L ρ AW BW u y)) :
    ∫⁻ ω, {ω : Ω₁ × Ω₂ | Z 0 ω.1 ∈ Set.Icc (-A - B) a
          ∧ Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a
          ∧ |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁
          ∧ -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)}.indicator
        (fun ω => ENNReal.ofReal (g (Z 0 ω.1 + Z 1 ω.1,
          (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)))) ω ∂(Q₁.prod Q₂)
      ≤ (Q₁.prod Q₂) (barrierEventPair
          (fun m ω => ((Z m ω.1, d m + β m * Z m ω.1 + W m ω.2) : ℝ × ℝ)) n
          (fun j => -A - B * j) (fun _ => a)
          (fun j => if j = 1 then -M₁ else -A' - B' * j)
          (fun j => if j = 1 then M₁ else -ρ)) := by
  classical
  set n' := n - 2 with hn'
  -- the pair family, the start and the suffixes
  set P : ℕ → Ω₁ × Ω₂ → ℝ × ℝ := fun i ω => (Z i ω.1, W i ω.2) with hPdef
  have hPm : ∀ i, Measurable (P i) := fun i =>
    ((hZ.measurable i).comp measurable_fst).prodMk ((hW.measurable i).comp measurable_snd)
  have hpair : iIndepFun P (Q₁.prod Q₂) :=
    iIndepFun_pairProd hZ.measurable hW.measurable hZ.indep hW.indep
  have hdisj : Disjoint (Finset.range 2) (Finset.Ico 2 n) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_range] at hx
    simp only [Finset.mem_Ico] at hy
    omega
  have hind0 := hpair.indepFun_finset (Finset.range 2) (Finset.Ico 2 n) hdisj hPm
  have h0 : (0 : ℕ) ∈ Finset.range 2 := by simp
  have h1 : (1 : ℕ) ∈ Finset.range 2 := by simp
  set F₀ : (↥(Finset.range 2) → ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ) := fun x =>
    (((x ⟨0, h0⟩).1, (x ⟨1, h1⟩).1), ((x ⟨0, h0⟩).2, (x ⟨1, h1⟩).2)) with hF₀
  have hF₀m : Measurable F₀ :=
    ((measurable_fst.comp (measurable_pi_apply _)).prodMk
      (measurable_fst.comp (measurable_pi_apply _))).prodMk
      ((measurable_snd.comp (measurable_pi_apply _)).prodMk
        (measurable_snd.comp (measurable_pi_apply _)))
  set F₁ : (↥(Finset.Ico 2 n) → ℝ × ℝ) → (((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ) :=
    fun y => (((blockSums 2 n (fun i => (y i).1),
      blockSums 2 n (fun i => min (β i) 0 * (y i).1)),
      blockSums 2 n (fun i => max (β i) 0 * (y i).1)), blockSums 2 n (fun i => (y i).2))
    with hF₁
  have hF₁m : Measurable F₁ := by
    refine ((((measurable_blockSums 2 n).comp ?_).prodMk ((measurable_blockSums 2 n).comp
      ?_)).prodMk ((measurable_blockSums 2 n).comp ?_)).prodMk ((measurable_blockSums 2 n).comp ?_)
    · exact measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)
    · exact measurable_pi_lambda _ fun i =>
        measurable_const.mul (measurable_fst.comp (measurable_pi_apply i))
    · exact measurable_pi_lambda _ fun i =>
        measurable_const.mul (measurable_fst.comp (measurable_pi_apply i))
    · exact measurable_pi_lambda _ fun i => measurable_snd.comp (measurable_pi_apply i)
  set X : Ω₁ × Ω₂ → (ℝ × ℝ) × (ℝ × ℝ) := fun ω => F₀ (fun i => P i ω) with hX
  set Y : Ω₁ × Ω₂ → (((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ) := fun ω => F₁ (fun i => P i ω)
    with hY
  have hXm : Measurable X := hF₀m.comp (measurable_pi_lambda _ fun i => hPm i)
  have hYm : Measurable Y := hF₁m.comp (measurable_pi_lambda _ fun i => hPm i)
  have hind : IndepFun X Y (Q₁.prod Q₂) := hind0.comp hF₀m hF₁m
  -- the suffix sums as shifted walks
  have hbs1 : ∀ ω i, i ≤ n' → (Y ω).1.1.1 (2 + i) = walk (fun m => Z (m + 2)) i ω.1 := by
    intro ω i hi
    change blockSums 2 n (fun i => Z i ω.1) (2 + i) = _
    rw [blockSums_comp Z (by omega) (by omega) ω.1, walk_shift]
  have hbs2 : ∀ ω i, i ≤ n' → (Y ω).1.1.2 (2 + i)
      = walk (fun m ω => min (β (m + 2)) 0 * Z (m + 2) ω) i ω.1 := by
    intro ω i hi
    change blockSums 2 n (fun i => min (β i) 0 * Z i ω.1) (2 + i) = _
    have e := blockSums_comp (fun m ω => min (β m) 0 * Z m ω) (k := 2) (n := n) (j := 2 + i)
      (by omega) (by omega) ω.1
    have e2 := walk_shift (fun m ω => min (β m) 0 * Z m ω) 2 i ω.1
    rw [e, e2]
  have hbs3 : ∀ ω i, i ≤ n' → (Y ω).1.2 (2 + i)
      = walk (fun m ω => max (β (m + 2)) 0 * Z (m + 2) ω) i ω.1 := by
    intro ω i hi
    change blockSums 2 n (fun i => max (β i) 0 * Z i ω.1) (2 + i) = _
    have e := blockSums_comp (fun m ω => max (β m) 0 * Z m ω) (k := 2) (n := n) (j := 2 + i)
      (by omega) (by omega) ω.1
    have e2 := walk_shift (fun m ω => max (β m) 0 * Z m ω) 2 i ω.1
    rw [e, e2]
  have hbs4 : ∀ ω i, i ≤ n' → (Y ω).2 (2 + i) = walk (fun m => W (m + 2)) i ω.2 := by
    intro ω i hi
    change blockSums 2 n (fun i => W i ω.2) (2 + i) = _
    rw [blockSums_comp W (by omega) (by omega) ω.2, walk_shift]
  -- the fibre sets
  set Suf : ℝ → ℝ → Set ((((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ)) := fun u y => {q |
      (∀ i, 1 ≤ i → i ≤ n' →
        -A - B * ((i : ℝ) + 2) - u ≤ q.1.1.1 (2 + i) ∧ q.1.1.1 (2 + i) ≤ a - u)
      ∧ (∀ i ≤ n', q.1.1.2 (2 + i) ≤ L)
      ∧ (∀ i ≤ n', y + driftSum (fun m => d (m + 2)) i + q.2 (2 + i) + q.1.2 (2 + i) ≤ -L - ρ)
      ∧ ∀ i ≤ n', -(AW + BW * i) ≤ q.2 (2 + i) + driftSum (fun m => d (m + 2)) i} with hSuf
  set goodX : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {x | x.1.1 ∈ Set.Icc (-A - B) a
      ∧ x.1.1 + x.1.2 ∈ Set.Icc (-A - 2 * B) a
      ∧ |d 0 + β 0 * x.1.1 + x.2.1| ≤ M₁
      ∧ -K₂ ≤ (d 0 + β 0 * x.1.1 + x.2.1) + (d 1 + β 1 * x.1.2 + x.2.2)} with hgoodX
  set S : Set (((ℝ × ℝ) × (ℝ × ℝ)) × ((((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ))) :=
    {p | p.1 ∈ goodX ∧ p.2 ∈ Suf (p.1.1.1 + p.1.1.2)
      ((d 0 + β 0 * p.1.1.1 + p.1.2.1) + (d 1 + β 1 * p.1.1.2 + p.1.2.2))} with hS
  have hgoodXm : MeasurableSet goodX := by
    have e1 : MeasurableSet {x : (ℝ × ℝ) × (ℝ × ℝ) | x.1.1 ∈ Set.Icc (-A - B) a} :=
      (measurable_fst.comp measurable_fst) measurableSet_Icc
    have e2 : MeasurableSet {x : (ℝ × ℝ) × (ℝ × ℝ) | x.1.1 + x.1.2 ∈ Set.Icc (-A - 2 * B) a} :=
      ((measurable_fst.comp measurable_fst).add (measurable_snd.comp measurable_fst))
        measurableSet_Icc
    have e3 : MeasurableSet {x : (ℝ × ℝ) × (ℝ × ℝ) | |d 0 + β 0 * x.1.1 + x.2.1| ≤ M₁} :=
      measurableSet_le ((measurable_const.add (measurable_const.mul
        (measurable_fst.comp measurable_fst))).add (measurable_fst.comp measurable_snd)).abs
        measurable_const
    have e4 : MeasurableSet {x : (ℝ × ℝ) × (ℝ × ℝ) | -K₂ ≤ (d 0 + β 0 * x.1.1 + x.2.1)
        + (d 1 + β 1 * x.1.2 + x.2.2)} :=
      measurableSet_le measurable_const
        (((measurable_const.add (measurable_const.mul (measurable_fst.comp measurable_fst))).add
          (measurable_fst.comp measurable_snd)).add ((measurable_const.add (measurable_const.mul
            (measurable_snd.comp measurable_fst))).add (measurable_snd.comp measurable_snd)))
    exact e1.inter (e2.inter (e3.inter e4))
  have hSm : MeasurableSet S := by
    have hgood' : Measurable fun p : ((ℝ × ℝ) × (ℝ × ℝ))
        × ((((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ)) => p.1 ∈ goodX :=
      measurable_mem.2 (measurable_fst hgoodXm)
    refine measurableSet_setOf.2 (hgood'.and ?_)
    simp only [hSuf, Set.mem_setOf_eq]
    fun_prop
  -- the fibre sets are the suffix events
  have hYpre : ∀ u y, Y ⁻¹' Suf u y = hp1SuffixV2 Z W β d n a A B L ρ AW BW u y := by
    intro u y
    ext ω
    simp only [Set.mem_preimage, hSuf, hp1SuffixV2, barrierEvent, Set.mem_setOf_eq,
      Set.mem_Icc]
    refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
    · refine forall_congr' fun i => forall_congr' fun hi1 => forall_congr' fun hin => ?_
      rw [hbs1 ω i hin]
    · refine forall_congr' fun i => forall_congr' fun hi => ?_
      rw [hbs2 ω i hi]
    · refine forall_congr' fun i => forall_congr' fun hi => ?_
      rw [hbs3 ω i hi, hbs4 ω i hi]
    · refine forall_congr' fun i => forall_congr' fun hi => ?_
      rw [hbs4 ω i hi]
  -- the product of the parts lies in the window event
  have hsub : (fun ω => (X ω, Y ω)) ⁻¹' S
      ⊆ barrierEventPair (fun m ω => ((Z m ω.1, d m + β m * Z m ω.1 + W m ω.2) : ℝ × ℝ)) n
          (fun j => -A - B * j) (fun _ => a)
          (fun j => if j = 1 then -M₁ else -A' - B' * j)
          (fun j => if j = 1 then M₁ else -ρ) := by
    intro ω hω
    obtain ⟨hgx, hsuf⟩ := hω
    have hs : ω ∈ hp1SuffixV2 Z W β d n a A B L ρ AW BW (Z 0 ω.1 + Z 1 ω.1)
        ((d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)) := by
      rw [← hYpre]
      exact hsuf
    exact mem_hp1Event_of_partsV2 hn2 ha hA hB hKR hA' hBW' hB'0 hgx hs
  -- the fibres
  have hfib : ∀ x, goodX.indicator (fun x => ENNReal.ofReal (g (x.1.1 + x.1.2,
      (d 0 + β 0 * x.1.1 + x.2.1) + (d 1 + β 1 * x.1.2 + x.2.2)))) x
      ≤ ((Q₁.prod Q₂).map Y) (Prod.mk x ⁻¹' S) := by
    intro x
    by_cases hx : x ∈ goodX
    · rw [Set.indicator_of_mem hx, Measure.map_apply hYm (measurable_prodMk_left hSm)]
      have hpre : Y ⁻¹' (Prod.mk x ⁻¹' S) = Y ⁻¹' Suf (x.1.1 + x.1.2)
          ((d 0 + β 0 * x.1.1 + x.2.1) + (d 1 + β 1 * x.1.2 + x.2.2)) := by
        ext ω
        simp only [Set.mem_preimage, hS, Set.mem_setOf_eq]
        exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
      rw [hpre, hYpre]
      exact hg _ hx.2.1 _
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  have hφm : Measurable fun x : (ℝ × ℝ) × (ℝ × ℝ) => goodX.indicator (fun x =>
      ENNReal.ofReal (g (x.1.1 + x.1.2,
        (d 0 + β 0 * x.1.1 + x.2.1) + (d 1 + β 1 * x.1.2 + x.2.2)))) x :=
    (ENNReal.measurable_ofReal.comp (hgm.comp (((measurable_fst.comp measurable_fst).add
      (measurable_snd.comp measurable_fst)).prodMk
        (((measurable_const.add (measurable_const.mul (measurable_fst.comp measurable_fst))).add
          (measurable_fst.comp measurable_snd)).add ((measurable_const.add (measurable_const.mul
            (measurable_snd.comp measurable_fst))).add
              (measurable_snd.comp measurable_snd)))))).indicator hgoodXm
  calc ∫⁻ ω, {ω : Ω₁ × Ω₂ | Z 0 ω.1 ∈ Set.Icc (-A - B) a
          ∧ Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a
          ∧ |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁
          ∧ -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)}.indicator
        (fun ω => ENNReal.ofReal (g (Z 0 ω.1 + Z 1 ω.1,
          (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)))) ω ∂(Q₁.prod Q₂)
      = ∫⁻ ω, goodX.indicator (fun x => ENNReal.ofReal (g (x.1.1 + x.1.2,
          (d 0 + β 0 * x.1.1 + x.2.1) + (d 1 + β 1 * x.1.2 + x.2.2)))) (X ω) ∂(Q₁.prod Q₂) := by
        refine lintegral_congr fun ω => ?_
        by_cases hω : X ω ∈ goodX
        · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (show ω ∈ {ω : Ω₁ × Ω₂ |
            Z 0 ω.1 ∈ Set.Icc (-A - B) a ∧ Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a
            ∧ |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁
            ∧ -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)}
            from hω)]
        · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (show ω ∉ {ω : Ω₁ × Ω₂ |
            Z 0 ω.1 ∈ Set.Icc (-A - B) a ∧ Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a
            ∧ |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁
            ∧ -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)}
            from hω)]
    _ = ∫⁻ x, goodX.indicator (fun x => ENNReal.ofReal (g (x.1.1 + x.1.2,
          (d 0 + β 0 * x.1.1 + x.2.1) + (d 1 + β 1 * x.1.2 + x.2.2)))) x
          ∂((Q₁.prod Q₂).map X) := (lintegral_map hφm hXm).symm
    _ ≤ ∫⁻ x, ((Q₁.prod Q₂).map Y) (Prod.mk x ⁻¹' S) ∂((Q₁.prod Q₂).map X) :=
        lintegral_mono hfib
    _ = (Q₁.prod Q₂) ((fun ω => (X ω, Y ω)) ⁻¹' S) :=
        (measure_preimage_prod_eq_lintegral hXm hYm hind hSm).symm
    _ ≤ _ := measure_mono hsub

/-! ### The window's first moment, Gaussian side, v2 -/

/-- The start term of `RMF.hp1LowerBoundV2`: the main term `RMF.startMainV2`, with the exit factor
inside, less the ceiling loss `P(Z₀ > a)E[min((-Z₁)⁺, C)]` and `C` times the tails,
`C = a + A + 2B`. -/
noncomputable def hp1StartV2 (v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ a A B M₁ K₂ ρ L t Λ AW : ℝ) : ℝ :=
  startMainV2 a (a + A + 2 * B) (v₀ + v₁) (β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁))
      (β₀ * v₀ + β₁ * v₁) (d₀ + d₁) t L ρ Λ AW
    - (gaussianReal 0 v₀.toNNReal).real (Set.Ioi a)
      * ∫ x, startWeight 0 (a + A + 2 * B) x ∂(gaussianReal 0 v₁.toNNReal)
    - (a + A + 2 * B) * startTails v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ A B M₁ K₂

/-- **The window's first-moment lower bound, Gaussian side, v2**, `√n` removed:
`RMF.hp1Slope · RMF.hp1StartV2 - RMF.hp1Loss`, the exit factor inside the start (`RMF.hp1ExitV2`
in `RMF.startMainV2`). -/
noncomputable def hp1LowerBoundV2 (n₀ m₀ : ℕ)
    (vmin vmax v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ a A B M₁ K₂ ρ L t Λ AW Klate σR2 : ℝ) : ℝ :=
  hp1Slope n₀ m₀ vmin vmax a A B L Klate σR2
      * hp1StartV2 v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ a A B M₁ K₂ ρ L t Λ AW
    - hp1Loss n₀ m₀ vmin vmax (v₀ + v₁) a A B L Klate σR2

/-- **The window's first moment, Gaussian side, v2.**  For a Gaussian height walk `Z` (variances
`v`) and an independent Gaussian residual walk `W` (variances `s`), slopes `β`, drifts `d`, the
pair family `(Z_m, d_m + β_mZ_m + W_m)` and its two-sided window event, the event has probability
at least `RMF.hp1LowerBoundV2 … / √n` for every `n ≥ n₀`.  The margin sums `σ_R²`, `K_late` run
over the blocks `β_m < 0` (the slopes `min(β_m, 0)`), `Λ` carries the variance
`max(β_m, 0)²v_m + s_m` of the real suffix step, and `K_R` bounds the whole slope walk on the
tube.

The start is `RMF.le_integral_startGoodV2`; given the start `(U₂, V₂)` the suffix is bounded by
`RMF.ofReal_le_measure_hp1SuffixV2` (Harris for the blocks `β_m ≥ 0`, the exit factor at `V₂`);
they combine by conditioning on the start (`RMF.lintegral_start_le_measureV2`). -/
theorem le_measure_windowEvent_gaussian_v2 (hZ : IsGaussianWalk Z v Q₁)
    (hW : IsGaussianWalk W s Q₂) (β d : ℕ → ℝ) {n₀ m₀ n : ℕ} (hn₀ : m₀ + 3 ≤ n₀) (hn : n₀ ≤ n)
    {vmin vmax a A B A' B' M₁ K₂ ρ L t Λ AW BW Klate KR σR2 : ℝ}
    (hv0 : 0 < (v 0 : ℝ)) (hv1 : 0 < (v 1 : ℝ)) (hvmin : 0 < vmin)
    (hvb : ∀ m, 2 ≤ m → vmin ≤ (v m : ℝ) ∧ (v m : ℝ) ≤ vmax)
    (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 2 * vmax < B)
    (hCn : (a + A + 2 * B) ^ 2 ≤ 2 * (((n₀ : ℝ) - 2) * vmin))
    (ht : 0 ≤ t) (hAW : 0 ≤ AW)
    (hΛ : ∑ m ∈ Finset.Ico 2 n,
      max 0 (t * d m + t ^ 2 * (max (β m) 0 ^ 2 * (v m : ℝ) + s m) / 2) ≤ Λ)
    (hBW : ∀ m, 2 ≤ m → m < n → (s m : ℝ) / 2 - d m ≤ BW)
    (hσR : ∑ m ∈ Finset.Ico 2 (m₀ + 2), min (β m) 0 ^ 2 * (v m : ℝ) ≤ σR2) (hσR0 : 0 < σR2)
    (hKlate : ∑ m ∈ Finset.Ico (m₀ + 2) n,
      |min (β m) 0| * ((a + A + B * m) + (a + A + B * (m + 1))) ≤ Klate) (hKL : Klate ≤ L)
    (hKR : ∑ m ∈ Finset.Ico 2 n, |β m| * ((a + A + B * m) + (a + A + B * (m + 1))) ≤ KR)
    (hM₁ : |d 0| ≤ M₁) (hK₂ : 0 ≤ K₂ + d 0 + d 1)
    (hA' : K₂ + KR + AW ≤ A') (hBW' : BW ≤ B') (hB'0 : 0 ≤ B') :
    hp1LowerBoundV2 n₀ m₀ vmin vmax (v 0) (v 1) (s 0) (s 1) (β 0) (β 1) (d 0) (d 1) a A B M₁ K₂
        ρ L t Λ AW Klate σR2 / √(n : ℝ)
      ≤ ((Q₁.prod Q₂) (barrierEventPair
          (fun m ω => ((Z m ω.1, d m + β m * Z m ω.1 + W m ω.2) : ℝ × ℝ)) n
          (fun j => -A - B * j) (fun _ => a)
          (fun j => if j = 1 then -M₁ else -A' - B' * j)
          (fun j => if j = 1 then M₁ else -ρ))).toReal := by
  -- basic facts
  have hvmax : 0 < vmax := lt_of_lt_of_le hvmin (le_trans (hvb 2 le_rfl).1 (hvb 2 le_rfl).2)
  have hB0 : 0 ≤ B := by linarith
  have hC0 : 0 ≤ a + A + 2 * B := by linarith
  have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀3 : (3 : ℝ) ≤ n₀ := by exact_mod_cast (show 3 ≤ n₀ by omega)
  have hNeq : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hCnN : (a + A + 2 * B) ^ 2 ≤ 2 * (((n - 2 : ℕ) : ℝ) * vmin) := by
    refine le_trans hCn ?_
    have : ((n₀ : ℝ) - 2) * vmin ≤ ((n - 2 : ℕ) : ℝ) * vmin :=
      mul_le_mul_of_nonneg_right (by rw [hNeq]; linarith) hvmin.le
    linarith
  have hc0 : 0 ≤ √(π * vmax / 2) := Real.sqrt_nonneg _
  have hEb0 : 0 < Real.exp ((B - 2 * vmax) / 2) - 1 := by
    have : 0 < (B - 2 * vmax) / 2 := by linarith
    have := Real.add_one_lt_exp this.ne'
    linarith
  have hMx0 : 0 ≤ max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax))) :=
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hPR0 : 0 ≤ Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) := (Real.exp_pos _).le
  -- the constants of the height suffix
  set κ := 2 * (1 - (a + A + 2 * B) ^ 2 / (2 * (((n - 2 : ℕ) : ℝ) * vmin)))
    / √(2 * π * (((n - 2 : ℕ) : ℝ) * vmax)) with hκ
  set Kr := √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin))) with hKr
  set PR := Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) with hPR
  set α := Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
    * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
    / (√((n - 2 : ℕ) : ℝ) * (Real.exp ((B - 2 * vmax) / 2) - 1)) with hα
  set γ := Kr * (√(π * vmax / 2) * PR + √(PR * ((m₀ : ℝ) * vmax))) with hγ
  have hα0 : 0 ≤ α := div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith))
    hMx0) (mul_nonneg (Real.sqrt_nonneg _) hEb0.le)
  have hγ0 : 0 ≤ γ := mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (mul_nonneg hc0 hPR0)
    (Real.sqrt_nonneg _))
  set g : ℝ × ℝ → ℝ := fun p => ((κ - Kr * PR) * (a - p.1) - γ) * hp1ExitV2 t L ρ Λ AW p.2
    - α * Real.exp (-p.1) with hgdef
  have hgm : Measurable g :=
    (((measurable_const.mul (measurable_const.sub measurable_fst)).sub measurable_const).mul
      ((measurable_hp1ExitV2 t L ρ Λ AW).comp measurable_snd)).sub
      (measurable_const.mul (Real.measurable_exp.comp measurable_fst.neg))
  -- the suffix from each start of the box
  have hsuf : ∀ u ∈ Set.Icc (-A - 2 * B) a, ∀ y, ENNReal.ofReal (g (u, y))
      ≤ (Q₁.prod Q₂) (hp1SuffixV2 Z W β d n a A B L ρ AW BW u y) :=
    fun u hu y => ofReal_le_measure_hp1SuffixV2 hZ hW β d (by omega) hvmin hvb ha hA hB hCnN
      hKlate hKL hσR hσR0 ht hAW hΛ hBW hu
  -- conditioning on the start
  have hcond := lintegral_start_le_measureV2 hZ hW β d (n := n) (by omega) ha hA hB0 hKR hA'
    hBW' hB'0 hgm hsuf (M₁ := M₁) (K₂ := K₂)
  -- the start integral
  have hz0 : Measurable fun ω : Ω₁ × Ω₂ => Z 0 ω.1 := (hZ.measurable 0).comp measurable_fst
  have hz1 : Measurable fun ω : Ω₁ × Ω₂ => Z 1 ω.1 := (hZ.measurable 1).comp measurable_fst
  have hw0 : Measurable fun ω : Ω₁ × Ω₂ => W 0 ω.2 := (hW.measurable 0).comp measurable_snd
  have hw1 : Measurable fun ω : Ω₁ × Ω₂ => W 1 ω.2 := (hW.measurable 1).comp measurable_snd
  have hUm : Measurable fun ω : Ω₁ × Ω₂ => Z 0 ω.1 + Z 1 ω.1 := hz0.add hz1
  have hV₂m : Measurable fun ω : Ω₁ × Ω₂ =>
      (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2) :=
    ((measurable_const.add (hz0.const_mul _)).add hw0).add
      ((measurable_const.add (hz1.const_mul _)).add hw1)
  set Good : Set (Ω₁ × Ω₂) := {ω : Ω₁ × Ω₂ | Z 0 ω.1 ∈ Set.Icc (-A - B) a
      ∧ Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a
      ∧ |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁
      ∧ -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)} with hGood
  have hGoodm : MeasurableSet Good := by
    have e1 : MeasurableSet {ω : Ω₁ × Ω₂ | Z 0 ω.1 ∈ Set.Icc (-A - B) a} :=
      hz0 measurableSet_Icc
    have e2 : MeasurableSet {ω : Ω₁ × Ω₂ | Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a} :=
      hUm measurableSet_Icc
    have e3 : MeasurableSet {ω : Ω₁ × Ω₂ | |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁} :=
      measurableSet_le ((measurable_const.add (hz0.const_mul _)).add hw0).abs measurable_const
    have e4 : MeasurableSet {ω : Ω₁ × Ω₂ | -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2)
        + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)} :=
      measurableSet_le measurable_const hV₂m
    exact e1.inter (e2.inter (e3.inter e4))
  have hstart := le_integral_startGoodV2 hZ hW β d hv0 hv1 (by linarith) hB0 hC0 hM₁ hK₂
    (t := t) (L := L) (ρ := ρ) (Λ := Λ) (AW := AW) (Q₁ := Q₁) (Q₂ := Q₂)
  set X := hp1StartV2 (v 0) (v 1) (s 0) (s 1) (β 0) (β 1) (d 0) (d 1) a A B M₁ K₂ ρ L t Λ AW
    with hX
  have hXeq : X = startMainV2 a (a + A + 2 * B) ((v 0 : ℝ) + v 1)
        (β 0 ^ 2 * v 0 + s 0 + (β 1 ^ 2 * v 1 + s 1)) (β 0 * v 0 + β 1 * v 1) (d 0 + d 1)
        t L ρ Λ AW
      - (gaussianReal 0 (v 0)).real (Set.Ioi a)
        * ∫ x, startWeight 0 (a + A + 2 * B) x ∂(gaussianReal 0 (v 1))
      - (a + A + 2 * B)
        * startTails (v 0) (v 1) (s 0) (s 1) (β 0) (β 1) (d 0) (d 1) A B M₁ K₂ := by
    rw [hX, hp1StartV2, Real.toNNReal_coe, Real.toNNReal_coe]
  -- the integral `J` of `g(U₂, V₂)` over the box
  set F : Ω₁ × Ω₂ → ℝ := fun ω => startWeight a (a + A + 2 * B) (Z 0 ω.1 + Z 1 ω.1)
    * hp1ExitV2 t L ρ Λ AW ((d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2))
    with hF
  set Ex : Ω₁ × Ω₂ → ℝ := fun ω =>
    hp1ExitV2 t L ρ Λ AW ((d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2))
    with hEx
  have hFm : Measurable F :=
    ((measurable_startWeight a _).comp hUm).mul ((measurable_hp1ExitV2 t L ρ Λ AW).comp hV₂m)
  have hExm : Measurable Ex := (measurable_hp1ExitV2 t L ρ Λ AW).comp hV₂m
  have hexp := integral_exp_neg_start hZ (Q₂ := Q₂)
  have hiF : Integrable (Good.indicator F) (Q₁.prod Q₂) :=
    Integrable.of_bound (hFm.indicator hGoodm).aestronglyMeasurable (a + A + 2 * B)
      (Filter.Eventually.of_forall fun ω => by
        have hF0 : 0 ≤ F ω :=
          mul_nonneg (startWeight_nonneg hC0 _) (hp1ExitV2_nonneg _ _ _ _ _ _)
        have hFC : F ω ≤ a + A + 2 * B := le_trans (mul_le_of_le_one_right
          (startWeight_nonneg hC0 _) (hp1ExitV2_le_one _ _ _ _ _ _)) (startWeight_le _)
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg
          (fun ω _ => mul_nonneg (startWeight_nonneg hC0 _) (hp1ExitV2_nonneg _ _ _ _ _ _)) ω)]
        by_cases hω : ω ∈ Good
        · rw [Set.indicator_of_mem hω]
          exact hFC
        · rw [Set.indicator_of_notMem hω]
          exact hC0)
  have hiEx : Integrable (Good.indicator Ex) (Q₁.prod Q₂) :=
    Integrable.of_bound (hExm.indicator hGoodm).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg
          (fun ω _ => hp1ExitV2_nonneg _ _ _ _ _ _) ω)]
        by_cases hω : ω ∈ Good
        · rw [Set.indicator_of_mem hω]
          exact hp1ExitV2_le_one _ _ _ _ _ _
        · rw [Set.indicator_of_notMem hω]
          exact zero_le_one)
  have hiE : Integrable (Good.indicator fun ω => Real.exp (-(Z 0 ω.1 + Z 1 ω.1)))
      (Q₁.prod Q₂) := hexp.1.indicator hGoodm
  have hGpt : ∀ ω, Good.indicator (fun ω => g (Z 0 ω.1 + Z 1 ω.1,
      (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2))) ω
      = (κ - Kr * PR) * Good.indicator F ω - γ * Good.indicator Ex ω
        - α * Good.indicator (fun ω => Real.exp (-(Z 0 ω.1 + Z 1 ω.1))) ω := by
    intro ω
    by_cases hω : ω ∈ Good
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω,
        Set.indicator_of_mem hω]
      have hu := hω.2.1
      rw [Set.mem_Icc] at hu
      have hFω : startWeight a (a + A + 2 * B) (Z 0 ω.1 + Z 1 ω.1) = a - (Z 0 ω.1 + Z 1 ω.1) :=
        startWeight_eq (by linarith) hu.2
      simp only [hgdef, hF, hEx]
      rw [hFω]
      ring
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω,
        Set.indicator_of_notMem hω]
      ring
  have hiG : Integrable (Good.indicator fun ω => g (Z 0 ω.1 + Z 1 ω.1,
      (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2))) (Q₁.prod Q₂) :=
    ((hiF.const_mul (κ - Kr * PR)).sub (hiEx.const_mul γ)).sub (hiE.const_mul α) |>.congr
      (Filter.Eventually.of_forall fun ω => (hGpt ω).symm)
  set J := ∫ ω, Good.indicator (fun ω => g (Z 0 ω.1 + Z 1 ω.1,
    (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2))) ω ∂(Q₁.prod Q₂) with hJ
  have hJge : 0 ≤ κ - Kr * PR →
      (κ - Kr * PR) * X - (α * Real.exp (((v 0 : ℝ) + v 1) / 2) + γ) ≤ J := by
    intro hκ'
    have e1 : J = (κ - Kr * PR) * ∫ ω, Good.indicator F ω ∂(Q₁.prod Q₂)
        - γ * ∫ ω, Good.indicator Ex ω ∂(Q₁.prod Q₂)
        - α * ∫ ω, Good.indicator (fun ω => Real.exp (-(Z 0 ω.1 + Z 1 ω.1))) ω
          ∂(Q₁.prod Q₂) := by
      rw [hJ, integral_congr_ae (Filter.Eventually.of_forall hGpt)]
      have i1 := integral_sub ((hiF.const_mul (κ - Kr * PR)).sub (hiEx.const_mul γ))
        (hiE.const_mul α)
      have i2 := integral_sub (hiF.const_mul (κ - Kr * PR)) (hiEx.const_mul γ)
      simp only [Pi.sub_apply] at i1 i2
      rw [i1, i2, integral_const_mul, integral_const_mul, integral_const_mul]
    have hE : ∫ ω, Good.indicator (fun ω => Real.exp (-(Z 0 ω.1 + Z 1 ω.1))) ω ∂(Q₁.prod Q₂)
        ≤ Real.exp (((v 0 : ℝ) + v 1) / 2) := by
      rw [← hexp.2]
      exact integral_mono hiE hexp.1 fun ω =>
        Set.indicator_le_self' (fun ω _ => (Real.exp_pos _).le) ω
    have hP : ∫ ω, Good.indicator Ex ω ∂(Q₁.prod Q₂) ≤ 1 := by
      calc ∫ ω, Good.indicator Ex ω ∂(Q₁.prod Q₂)
          ≤ ∫ _ : Ω₁ × Ω₂, (1 : ℝ) ∂(Q₁.prod Q₂) :=
            integral_mono hiEx (integrable_const 1) fun ω => by
              by_cases hω : ω ∈ Good
              · rw [Set.indicator_of_mem hω]
                exact hp1ExitV2_le_one _ _ _ _ _ _
              · rw [Set.indicator_of_notMem hω]
                exact zero_le_one
        _ = 1 := by simp
    have hFX : X ≤ ∫ ω, Good.indicator F ω ∂(Q₁.prod Q₂) := by
      rw [hXeq]
      exact hstart
    rw [e1]
    have h1 := mul_le_mul_of_nonneg_left hFX hκ'
    have h2 := mul_le_mul_of_nonneg_left hE hα0
    have h3 := mul_le_mul_of_nonneg_left hP hγ0
    linarith
  -- the window event from below
  have hlint : ENNReal.ofReal J ≤ ∫⁻ ω, Good.indicator
      (fun ω => ENNReal.ofReal (g (Z 0 ω.1 + Z 1 ω.1,
        (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)))) ω
      ∂(Q₁.prod Q₂) := by
    refine le_trans (ofReal_integral_le_lintegral_ofReal hiG) (le_of_eq ?_)
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ Good
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, ENNReal.ofReal_zero]
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) (le_trans hlint hcond)
  rw [ENNReal.toReal_ofReal'] at hreal
  -- the scaling in `n`
  have hsqn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hKr := sqrt_slopeLoss_le hn₀ hn hvmin
  have hslope : 0 < hp1Slope n₀ m₀ vmin vmax a A B L Klate σR2 →
      hp1Slope n₀ m₀ vmin vmax a A B L Klate σR2 / √(n : ℝ) ≤ κ - Kr * PR := by
    intro hpos
    have hκge := ballotSlope_ge (vmax := vmax) (C := a + A + 2 * B) (by omega) hn hvmin hvmax
      hCn
    unfold hp1Slope at hpos ⊢
    rw [max_eq_left (le_of_lt (lt_max_iff.1 hpos |>.resolve_right (lt_irrefl 0)))]
    have e : (2 * (1 - (a + A + 2 * B) ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin))) / √(2 * π * vmax)
          - √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin))) * PR) / √(n : ℝ)
        = 2 * (1 - (a + A + 2 * B) ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin))) / √(2 * π * vmax)
            / √(n : ℝ)
          - √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin))) / √(n : ℝ) * PR := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hKr hPR0
    linarith
  have hα' : α ≤ √((n₀ : ℝ) / ((n₀ : ℝ) - 2))
      * (Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
        * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
        / (Real.exp ((B - 2 * vmax) / 2) - 1)) / √(n : ℝ) := by
    have h1 := sqrt_div_natSub_le (c := 1) zero_le_one (k := 2) (n₀ := n₀) (n := n)
      (by omega) hn
    rw [one_mul] at h1
    set K1 := Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
      * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
      / (Real.exp ((B - 2 * vmax) / 2) - 1) with hK1
    have hK10 : 0 ≤ K1 := div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith))
      hMx0) hEb0.le
    have hNpos : (0 : ℝ) < ((n - 2 : ℕ) : ℝ) := by rw [hNeq]; linarith
    have e1 : α = K1 * √(1 / ((n - 2 : ℕ) : ℝ)) := by
      rw [hα, hK1, Real.sqrt_div' _ hNpos.le, Real.sqrt_one]
      field_simp
    rw [e1]
    calc K1 * √(1 / ((n - 2 : ℕ) : ℝ)) ≤ K1 * (√((n₀ : ℝ) / ((n₀ : ℝ) - 2)) / √(n : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hK10
          simpa using h1
      _ = √((n₀ : ℝ) / ((n₀ : ℝ) - 2)) * K1 / √(n : ℝ) := by ring
  have hγ' : γ ≤ √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin)))
      * (√(π * vmax / 2) * PR + √(PR * ((m₀ : ℝ) * vmax))) / √(n : ℝ) := by
    have hQ0 : 0 ≤ √(π * vmax / 2) * PR + √(PR * ((m₀ : ℝ) * vmax)) :=
      add_nonneg (mul_nonneg hc0 hPR0) (Real.sqrt_nonneg _)
    rw [hγ]
    calc Kr * (√(π * vmax / 2) * PR + √(PR * ((m₀ : ℝ) * vmax)))
        ≤ √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin))) / √(n : ℝ)
          * (√(π * vmax / 2) * PR + √(PR * ((m₀ : ℝ) * vmax))) :=
          mul_le_mul_of_nonneg_right hKr hQ0
      _ = _ := by ring
  have hloss : α * Real.exp (((v 0 : ℝ) + v 1) / 2) + γ
      ≤ hp1Loss n₀ m₀ vmin vmax ((v 0 : ℝ) + v 1) a A B L Klate σR2 / √(n : ℝ) := by
    have hE0 : 0 ≤ Real.exp (((v 0 : ℝ) + v 1) / 2) := (Real.exp_pos _).le
    have h2 := mul_le_mul_of_nonneg_right hα' hE0
    have e : √((n₀ : ℝ) / ((n₀ : ℝ) - 2))
          * (Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
            * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
            / (Real.exp ((B - 2 * vmax) / 2) - 1)) / √(n : ℝ)
          * Real.exp (((v 0 : ℝ) + v 1) / 2)
        = √((n₀ : ℝ) / ((n₀ : ℝ) - 2))
          * (Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
            * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
            / (Real.exp ((B - 2 * vmax) / 2) - 1)) * Real.exp (((v 0 : ℝ) + v 1) / 2)
          / √(n : ℝ) := by ring
    rw [e] at h2
    refine le_trans (add_le_add h2 hγ') (le_of_eq ?_)
    rw [hp1Loss, ← add_div]
  -- conclude
  have hfin := hp1_final_arith (WL := 1) (Wr := 1) (le_of_eq (max_eq_left zero_le_one)) hJge
    hslope hloss (le_max_right _ _) (hp1Loss_nonneg hC0 hB.le) hsqn (by rw [mul_one]; exact hreal)
    ENNReal.toReal_nonneg
  rw [max_eq_left zero_le_one, one_mul] at hfin
  exact hfin

end AssemblyV2

end RMF
