/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.Anticoncentration
import RMF.Probability.MatchingGaussian

/-!
# Optional stopping below a nondecreasing barrier

`RMF.IsGaussianWalk.measure_forall_le_le` proves Probability Result 1's upper bound by Harper's
iterated-logarithm induction (Probability Lemma 1), at `result1Const ≈ 10¹³`.  This file proves the
ingredients of an optional-stopping argument instead, for a nondecreasing barrier `g`;
`RMF/Probability/BarrierSupermartingale.lean` uses the overshoot, the optional-stopping bound and
the renewal sum for Probability Result 1 at the Gaussian constant.

* **The overshoot**, `RMF.lintegral_posPart_sub_le_gaussianReal`: for `G ~ N(0, v)` and `c ≥ 0`,
  `E(G - c)⁺ ≤ √(πv/2)·P(G > c)`.  Shifting the density gives
  `P(G > c + t) ≤ e^{-t²/(2v)} P(G > c)`, and the layer cake integrates it.
* **Optional stopping**, one step at a time: with `A_n` the survival event and
  `Φ_n = E[(g(n) - S_n)1_{A_n}]`,
  `Φ_{n+1} ≤ Φ_n + (g(n+1) - g(n))P(A_n) + √(πv₊/2)(P(A_n) - P(A_{n+1}))`.
  The increment `G_n` is centred and independent of `A_n`, and the overshoot is the step above.
* **Anti-concentration**, `RMF.measure_inter_mem_Icc_le`: for `R ~ N(0, W)` independent of `X`,
  `P(X ∈ S, R ∈ [ζ(X) - η, ζ(X)]) ≤ P(X ∈ S)·η/√(2πW)`.
* **The renewal sum of a logarithmic barrier**, `RMF.sum_log_barrier_le`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### The Gaussian overshoot -/

/-- **The shifted Gaussian tail**: `P(G > c + t) ≤ e^{-t²/(2v)} P(G > c)` for `G ~ N(0, v)` and
`c, t ≥ 0`.  Shifting the density by `t` multiplies it by `e^{-(2yt + t²)/(2v)} ≤ e^{-t²/(2v)}` on
`y > c ≥ 0`. -/
lemma gaussianReal_Ioi_add_le (v : ℝ≥0) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    gaussianReal 0 v (Set.Ioi (c + t))
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * v)))) * gaussianReal 0 v (Set.Ioi c) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, Measure.dirac_apply' _ measurableSet_Ioi,
      Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; linarith)]
    exact zero_le
  have hv0 : (0 : ℝ) < (v : ℝ) := lt_of_le_of_ne v.2 (Ne.symm (by exact_mod_cast hv))
  rw [gaussianReal_apply 0 hv, gaussianReal_apply 0 hv]
  have hshift : (∫⁻ x in Set.Ioi (c + t), gaussianPDF 0 v x)
      = ∫⁻ y in Set.Ioi c, gaussianPDF 0 v (y + t) := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
      ← lintegral_add_right_eq_self _ t]
    refine lintegral_congr fun y => ?_
    by_cases hy : c < y
    · rw [Set.indicator_of_mem (show y + t ∈ Set.Ioi (c + t) by
          simp only [Set.mem_Ioi]; linarith),
        Set.indicator_of_mem (show y ∈ Set.Ioi c from hy)]
    · rw [Set.indicator_of_notMem (show y + t ∉ Set.Ioi (c + t) by
          simp only [Set.mem_Ioi, not_lt]; push Not at hy; linarith),
        Set.indicator_of_notMem (show y ∉ Set.Ioi c from hy)]
  rw [hshift, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioi fun y hy => ?_
  have hy0 : 0 ≤ y := le_trans hc (le_of_lt hy)
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [gaussianPDFReal, gaussianPDFReal]
  have h2v : (0 : ℝ) < 2 * (v : ℝ) := by positivity
  have hexp : Real.exp (-(y + t - 0) ^ 2 / (2 * v))
      ≤ Real.exp (-(t ^ 2 / (2 * v))) * Real.exp (-(y - 0) ^ 2 / (2 * v)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hnum : -(y + t - 0) ^ 2 ≤ -(t ^ 2) + -(y - 0) ^ 2 := by nlinarith [mul_nonneg hy0 ht]
    calc -(y + t - 0) ^ 2 / (2 * v) ≤ (-(t ^ 2) + -(y - 0) ^ 2) / (2 * v) :=
          div_le_div_of_nonneg_right hnum h2v.le
      _ = -(t ^ 2 / (2 * v)) + -(y - 0) ^ 2 / (2 * v) := by ring
  calc (√(2 * π * v))⁻¹ * Real.exp (-(y + t - 0) ^ 2 / (2 * v))
      ≤ (√(2 * π * v))⁻¹
          * (Real.exp (-(t ^ 2 / (2 * v))) * Real.exp (-(y - 0) ^ 2 / (2 * v))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.exp (-(t ^ 2 / (2 * v))) * ((√(2 * π * v))⁻¹ * Real.exp (-(y - 0) ^ 2 / (2 * v))) :=
        by ring

/-- **The Gaussian overshoot**: `E(G - c)⁺ ≤ √(πv/2)·P(G > c)` for `G ~ N(0, v)` and `c ≥ 0`.  The
layer cake writes `E(G - c)⁺ = ∫_0^∞ P(G > c + t) dt`; `RMF.gaussianReal_Ioi_add_le` and
`∫_0^∞ e^{-t²/(2v)} dt = √(πv/2)` finish.  The sharp constant is `√(2v/π)`. -/
lemma lintegral_posPart_sub_le_gaussianReal (v : ℝ≥0) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ x, ENNReal.ofReal (max (x - c) 0) ∂(gaussianReal 0 v)
      ≤ ENNReal.ofReal (√(π * v / 2)) * gaussianReal 0 v (Set.Ioi c) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, lintegral_dirac]
    simp only [zero_sub, max_eq_right (neg_nonpos.2 hc), ENNReal.ofReal_zero]
    exact zero_le
  have hv0 : (0 : ℝ) < (v : ℝ) := lt_of_le_of_ne v.2 (Ne.symm (by exact_mod_cast hv))
  have hlayer := lintegral_eq_lintegral_meas_lt (gaussianReal 0 v)
    (f := fun x => max (x - c) 0) (Filter.Eventually.of_forall fun x => le_max_right _ _)
    (by fun_prop)
  rw [hlayer]
  have hset : ∀ t : ℝ, 0 < t → {x : ℝ | t < max (x - c) 0} = Set.Ioi (c + t) := by
    intro t ht
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ioi, lt_max_iff]
    constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h
      left
      linarith
  -- the Gaussian integral on the half line
  have hb : (0 : ℝ) < 1 / (2 * (v : ℝ)) := by positivity
  have hfun : (fun t : ℝ => Real.exp (-(t ^ 2 / (2 * v))))
      = fun t : ℝ => Real.exp (-(1 / (2 * (v : ℝ))) * t ^ 2) := by
    funext t
    congr 1
    ring
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2 / (2 * v)))) (Set.Ioi 0) := by
    rw [hfun]
    exact integrableOn_Ioi_exp_neg_mul_sq_iff.2 hb
  have hgauss : ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * v))))
      = ENNReal.ofReal (√(π * v / 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le), hfun, integral_gaussian_Ioi]
    congr 1
    rw [show π / (1 / (2 * (v : ℝ))) = 4 * (π * v / 2) by field_simp; ring,
      Real.sqrt_mul (by norm_num),
      show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    ring
  calc ∫⁻ t in Set.Ioi 0, gaussianReal 0 v {x | t < max (x - c) 0}
      = ∫⁻ t in Set.Ioi 0, gaussianReal 0 v (Set.Ioi (c + t)) :=
        setLIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [hset t ht]
    _ ≤ ∫⁻ t in Set.Ioi 0,
          ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * v)))) * gaussianReal 0 v (Set.Ioi c) :=
        setLIntegral_mono' measurableSet_Ioi fun t ht =>
          gaussianReal_Ioi_add_le v hc (le_of_lt ht)
    _ = (∫⁻ t in Set.Ioi 0, ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * v)))))
          * gaussianReal 0 v (Set.Ioi c) :=
        lintegral_mul_const' _ _ (measure_ne_top _ _)
    _ = ENNReal.ofReal (√(π * v / 2)) * gaussianReal 0 v (Set.Ioi c) := by rw [hgauss]

/-! ### The overshoot, conditionally -/

section Conditional

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The overshoot, conditionally**: if `R ~ N(0, V)` is independent of `X` and `ζ ≥ 0` on `S`,
then `E[1_{X ∈ S}(R - ζ(X))⁺] ≤ √(πV/2)·P(X ∈ S, R > ζ(X))`.
`RMF.lintegral_posPart_sub_le_gaussianReal`, fibrewise over the law of `X`. -/
lemma lintegral_indicator_posPart_sub_le {α : Type*} [MeasurableSpace α] {X : Ω → α}
    {R : Ω → ℝ} {S : Set α} {ζ : α → ℝ} {V : ℝ≥0} (hX : Measurable X) (hR : Measurable R)
    (hS : MeasurableSet S) (hζ : Measurable ζ) (hζ0 : ∀ x ∈ S, 0 ≤ ζ x)
    (hind : IndepFun X R μ) (hlaw : μ.map R = gaussianReal 0 V) :
    ∫⁻ ω, (X ⁻¹' S).indicator (fun ω => ENNReal.ofReal (max (R ω - ζ (X ω)) 0)) ω ∂μ
      ≤ ENNReal.ofReal (√(π * V / 2)) * μ (X ⁻¹' S ∩ {ω | ζ (X ω) < R ω}) := by
  set F : α × ℝ → ℝ≥0∞ :=
    (Prod.fst ⁻¹' S).indicator (fun p => ENNReal.ofReal (max (p.2 - ζ p.1) 0)) with hFdef
  have hF : Measurable F :=
    (ENNReal.measurable_ofReal.comp ((measurable_snd.sub (hζ.comp measurable_fst)).max
      measurable_const)).indicator (measurable_fst hS)
  have hT : MeasurableSet {p : α × ℝ | p.1 ∈ S ∧ ζ p.1 < p.2} :=
    (measurable_fst hS).inter (measurableSet_lt (hζ.comp measurable_fst) measurable_snd)
  have hprod := hind.map_prod_eq_prod_map_map hX.aemeasurable hR.aemeasurable
  have hLHS : (fun ω => (X ⁻¹' S).indicator
      (fun ω => ENNReal.ofReal (max (R ω - ζ (X ω)) 0)) ω) = fun ω => F (X ω, R ω) := by
    funext ω
    rw [hFdef]
    by_cases hω : X ω ∈ S
    · rw [Set.indicator_of_mem (show ω ∈ X ⁻¹' S from hω),
        Set.indicator_of_mem (show (X ω, R ω) ∈ (Prod.fst ⁻¹' S : Set (α × ℝ)) from hω)]
    · rw [Set.indicator_of_notMem (show ω ∉ X ⁻¹' S from hω),
        Set.indicator_of_notMem (show (X ω, R ω) ∉ (Prod.fst ⁻¹' S : Set (α × ℝ)) from hω)]
  rw [hLHS, ← lintegral_map hF (hX.prodMk hR), hprod, lintegral_prod _ hF.aemeasurable]
  have hinner : ∀ x, ∫⁻ r, F (x, r) ∂(μ.map R)
      ≤ ENNReal.ofReal (√(π * V / 2)) * S.indicator (fun x => (μ.map R) (Set.Ioi (ζ x))) x := by
    intro x
    by_cases hx : x ∈ S
    · have hF' : ∀ r : ℝ, F (x, r) = ENNReal.ofReal (max (r - ζ x) 0) := fun r =>
        Set.indicator_of_mem (show (x, r) ∈ (Prod.fst ⁻¹' S : Set (α × ℝ)) from hx) _
      simp_rw [hF']
      rw [Set.indicator_of_mem hx, hlaw]
      exact lintegral_posPart_sub_le_gaussianReal V (hζ0 x hx)
    · have hF' : ∀ r : ℝ, F (x, r) = 0 := fun r =>
        Set.indicator_of_notMem (show (x, r) ∉ (Prod.fst ⁻¹' S : Set (α × ℝ)) from hx) _
      simp_rw [hF', lintegral_zero]
      rw [Set.indicator_of_notMem hx, mul_zero]
  calc ∫⁻ x, ∫⁻ r, F (x, r) ∂(μ.map R) ∂(μ.map X)
      ≤ ∫⁻ x, ENNReal.ofReal (√(π * V / 2))
          * S.indicator (fun x => (μ.map R) (Set.Ioi (ζ x))) x ∂(μ.map X) :=
        lintegral_mono hinner
    _ = ENNReal.ofReal (√(π * V / 2))
          * ∫⁻ x, S.indicator (fun x => (μ.map R) (Set.Ioi (ζ x))) x ∂(μ.map X) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (√(π * V / 2)) * μ (X ⁻¹' S ∩ {ω | ζ (X ω) < R ω}) := by
        congr 1
        rw [show X ⁻¹' S ∩ {ω | ζ (X ω) < R ω}
            = (fun ω => (X ω, R ω)) ⁻¹' {p : α × ℝ | p.1 ∈ S ∧ ζ p.1 < p.2} from rfl,
          ← Measure.map_apply (hX.prodMk hR) hT, hprod, Measure.prod_apply hT]
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx]
          congr 1
          ext r
          simp [hx]
        · rw [Set.indicator_of_notMem hx]
          have hempty : Prod.mk x ⁻¹' {p : α × ℝ | p.1 ∈ S ∧ ζ p.1 < p.2} = ∅ := by
            ext r
            simp [hx]
          rw [hempty, measure_empty]

end Conditional

/-! ### Optional stopping, one step -/

section Walk

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The event that the walk stays below the barrier `g` up to time `n`. -/
def survivalSet (G : ℕ → Ω → ℝ) (g : ℕ → ℝ) (n : ℕ) : Set Ω := {ω | ∀ j ≤ n, walk G j ω ≤ g j}

omit [IsProbabilityMeasure μ] in
lemma IsGaussianWalk.measurableSet_survivalSet (h : IsGaussianWalk G v μ) (g : ℕ → ℝ) (n : ℕ) :
    MeasurableSet (survivalSet G g n) := by
  have hrw : survivalSet G g n = ⋂ j ∈ Set.Iic n, {ω | walk G j ω ≤ g j} := by
    ext ω
    simp [survivalSet]
  rw [hrw]
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
    measurableSet_le (h.measurable_walk j) measurable_const

omit [MeasurableSpace Ω] in
lemma survivalSet_succ (G : ℕ → Ω → ℝ) (g : ℕ → ℝ) (n : ℕ) :
    survivalSet G g (n + 1) = survivalSet G g n ∩ {ω | walk G (n + 1) ω ≤ g (n + 1)} := by
  ext ω
  simp only [survivalSet, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro hω
    exact ⟨fun j hj => hω j (by omega), hω (n + 1) le_rfl⟩
  · rintro ⟨hω, hn⟩ j hj
    rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
    · exact hω j (by omega)
    · have hjn : j = n + 1 := by omega
      subst hjn
      exact hn

omit [MeasurableSpace Ω] in
lemma survivalSet_zero (G : ℕ → Ω → ℝ) {g : ℕ → ℝ} (hg : 0 ≤ g 0) :
    survivalSet G g 0 = Set.univ := by
  ext ω
  simp only [survivalSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  simpa [walk] using hg

omit [MeasurableSpace Ω] in
/-- The survival event up to time `n` is read off the prefix sums up to `n`. -/
lemma survivalSet_eq_preimage (G : ℕ → Ω → ℝ) (g : ℕ → ℝ) (n : ℕ) :
    survivalSet G g n
      = (fun ω => prefixSums n fun i => G i ω) ⁻¹' {f : ℕ → ℝ | ∀ j ≤ n, f j ≤ g j} := by
  ext ω
  simp only [survivalSet, Set.mem_setOf_eq, Set.mem_preimage]
  exact forall_congr' fun j => forall_congr' fun hj => by rw [prefixSums_comp G hj ω]

lemma measurableSet_forall_le_pi (g : ℕ → ℝ) (n : ℕ) :
    MeasurableSet {f : ℕ → ℝ | ∀ j ≤ n, f j ≤ g j} := by
  have hrw : {f : ℕ → ℝ | ∀ j ≤ n, f j ≤ g j} = ⋂ j ∈ Set.Iic n, {f : ℕ → ℝ | f j ≤ g j} := by
    ext f
    simp
  rw [hrw]
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
    measurableSet_le (measurable_pi_apply j) measurable_const

omit [IsProbabilityMeasure μ] in
/-- The `n`-th increment is independent of the prefix sums up to `n`. -/
lemma IsGaussianWalk.indepFun_prefixSums_step (h : IsGaussianWalk G v μ) (n : ℕ) :
    IndepFun (fun ω => prefixSums n fun i => G i ω) (G n) μ := by
  have hcomp := (h.indepFun_prefixSums_blockSums n (n + 1)).comp (measurable_id (α := ℕ → ℝ))
    (measurable_pi_apply (n + 1))
  have h1 : (id ∘ fun ω => prefixSums n fun i => G i ω) = fun ω => prefixSums n fun i => G i ω :=
    rfl
  have h2 : ((fun y : ℕ → ℝ => y (n + 1)) ∘ fun ω => blockSums n (n + 1) fun i => G i ω)
      = G n := by
    funext ω
    simp only [Function.comp_apply]
    rw [blockSums_comp G (by omega) le_rfl ω, walk_succ]
    simp
  rwa [h1, h2] at hcomp

/-- **Optional stopping, one step.**  For a barrier with `g(n) ≤ g(n+1)` and `v_n ≤ V`,
`Φ_{n+1} ≤ Φ_n + (g(n+1) - g(n))P(A_n) + √(πV/2)(P(A_n) - P(A_{n+1}))`, where `A_n` is the
survival event and `Φ_n = E[1_{A_n}(g(n) - S_n)]`.  The step `G_n` is centred and independent of
`A_n`, and the overshoot is `RMF.lintegral_indicator_posPart_sub_le`. -/
theorem IsGaussianWalk.survival_step (h : IsGaussianWalk G v μ) {g : ℕ → ℝ} {n : ℕ}
    (hg : g n ≤ g (n + 1)) {V : ℝ} (hV : (v n : ℝ) ≤ V) :
    ∫ ω, (survivalSet G g (n + 1)).indicator (fun ω => g (n + 1) - walk G (n + 1) ω) ω ∂μ
      ≤ ∫ ω, (survivalSet G g n).indicator (fun ω => g n - walk G n ω) ω ∂μ
        + (g (n + 1) - g n) * μ.real (survivalSet G g n)
        + √(π * V / 2) * (μ.real (survivalSet G g n) - μ.real (survivalSet G g (n + 1))) := by
  set A := survivalSet G g n with hA
  set A' := survivalSet G g (n + 1) with hA'
  have hAm : MeasurableSet A := h.measurableSet_survivalSet g n
  have hA'm : MeasurableSet A' := h.measurableSet_survivalSet g (n + 1)
  have hA'eq : A' = A ∩ {ω | walk G (n + 1) ω ≤ g (n + 1)} := survivalSet_succ G g n
  have hA'A : A' ⊆ A := by rw [hA'eq]; exact Set.inter_subset_left
  have hSn := h.measurable_walk n
  have hSn1 := h.measurable_walk (n + 1)
  have hGn := h.measurable n
  have hint_n : Integrable (walk G n) μ := integrable_of_hasLaw_gaussianReal hSn (h.map_walk n)
  have hint_n1 : Integrable (walk G (n + 1)) μ :=
    integrable_of_hasLaw_gaussianReal hSn1 (h.map_walk (n + 1))
  have hint_G : Integrable (G n) μ := integrable_of_hasLaw_gaussianReal hGn (h.map_eq n)
  have hstep : ∀ ω, walk G (n + 1) ω = walk G n ω + G n ω := fun ω => by
    rw [walk_succ]
    rfl
  -- the pointwise identity
  set O : Ω → ℝ := A.indicator (fun ω => max (walk G (n + 1) ω - g (n + 1)) 0) with hOdef
  have hpt : ∀ ω, A'.indicator (fun ω => g (n + 1) - walk G (n + 1) ω) ω
      = A.indicator (fun ω => g n - walk G n ω) ω
        + (g (n + 1) - g n) * A.indicator (fun _ => (1 : ℝ)) ω
        - A.indicator (G n) ω + O ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [hOdef, Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω,
        Set.indicator_of_mem hω]
      by_cases hω' : walk G (n + 1) ω ≤ g (n + 1)
      · have hmem : ω ∈ A' := by rw [hA'eq]; exact ⟨hω, hω'⟩
        rw [Set.indicator_of_mem hmem, max_eq_right (by linarith), hstep]
        ring
      · have hnot : ω ∉ A' := fun hmem => hω' (by rw [hA'eq] at hmem; exact hmem.2)
        rw [Set.indicator_of_notMem hnot, max_eq_left (by linarith), hstep]
        ring
    · have hnot : ω ∉ A' := fun hmem => hω (hA'A hmem)
      rw [hOdef, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω,
        Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Set.indicator_of_notMem hnot]
      ring
  have hint1 : Integrable (A.indicator (fun ω => g n - walk G n ω)) μ :=
    ((integrable_const _).sub hint_n).indicator hAm
  have hint2 : Integrable (fun ω => (g (n + 1) - g n) * A.indicator (fun _ => (1 : ℝ)) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator hAm).const_mul _
  have hint3 : Integrable (A.indicator (G n)) μ := hint_G.indicator hAm
  have hint4 : Integrable O μ :=
    ((hint_n1.sub (integrable_const _)).pos_part).indicator hAm
  have hint12 : Integrable (fun ω => A.indicator (fun ω => g n - walk G n ω) ω
      + (g (n + 1) - g n) * A.indicator (fun _ => (1 : ℝ)) ω) μ := hint1.add hint2
  have hint123 : Integrable (fun ω => A.indicator (fun ω => g n - walk G n ω) ω
      + (g (n + 1) - g n) * A.indicator (fun _ => (1 : ℝ)) ω - A.indicator (G n) ω) μ :=
    hint12.sub hint3
  have hΦ : ∫ ω, A'.indicator (fun ω => g (n + 1) - walk G (n + 1) ω) ω ∂μ
      = ∫ ω, A.indicator (fun ω => g n - walk G n ω) ω ∂μ
        + (g (n + 1) - g n) * μ.real A - ∫ ω, A.indicator (G n) ω ∂μ + ∫ ω, O ω ∂μ := by
    have hone : ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ = μ.real A := integral_indicator_one hAm
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hint123 hint4,
      integral_sub hint12 hint3, integral_add hint1 hint2, integral_const_mul, hone]
  -- the step is centred and independent of the past
  have hzero : ∫ ω, A.indicator (G n) ω ∂μ = 0 := by
    have hS := measurableSet_forall_le_pi g n
    have hind := (h.indepFun_prefixSums_step n).comp
      ((measurable_const : Measurable fun _ : ℕ → ℝ => (1 : ℝ)).indicator hS)
      (measurable_id (α := ℝ))
    have hfun : ((({f : ℕ → ℝ | ∀ j ≤ n, f j ≤ g j}).indicator fun _ => (1 : ℝ))
        ∘ fun ω => prefixSums n fun i => G i ω) = A.indicator fun _ => (1 : ℝ) := by
      funext ω
      rw [hA, survivalSet_eq_preimage]
      rfl
    rw [hfun] at hind
    have hmul : A.indicator (G n) = fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (id ∘ G n) ω := by
      funext ω
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        simp
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
    rw [hmul, hind.integral_fun_mul_eq_mul_integral
      (measurable_const.indicator hAm).aestronglyMeasurable hGn.aestronglyMeasurable]
    have hmean : ∫ ω, (id ∘ G n) ω ∂μ = 0 := by
      simpa using integral_of_hasLaw_gaussianReal hGn (h.map_eq n)
    rw [hmean, mul_zero]
  -- the overshoot
  have hover : ∫ ω, O ω ∂μ ≤ √(π * V / 2) * (μ.real A - μ.real A') := by
    have hS := measurableSet_forall_le_pi g n
    have hX : Measurable fun ω => prefixSums n fun i => G i ω :=
      (measurable_prefixSums n).comp (measurable_pi_lambda _ fun i => h.measurable i)
    have hζ : Measurable fun f : ℕ → ℝ => g (n + 1) - f n :=
      measurable_const.sub (measurable_pi_apply n)
    have hζ0 : ∀ f ∈ {f : ℕ → ℝ | ∀ j ≤ n, f j ≤ g j}, 0 ≤ g (n + 1) - f n := by
      intro f hf
      have := hf n le_rfl
      linarith
    have hcond := lintegral_indicator_posPart_sub_le (μ := μ) hX hGn hS hζ hζ0
      (h.indepFun_prefixSums_step n) (h.map_eq n)
    have hpre : ∀ ω, prefixSums n (fun i => G i ω) n = walk G n ω := fun ω =>
      prefixSums_comp G le_rfl ω
    have hL : ∫⁻ ω, ((fun ω => prefixSums n fun i => G i ω)
          ⁻¹' {f : ℕ → ℝ | ∀ j ≤ n, f j ≤ g j}).indicator
          (fun ω => ENNReal.ofReal
            (max (G n ω - (g (n + 1) - prefixSums n (fun i => G i ω) n)) 0)) ω ∂μ
        = ENNReal.ofReal (∫ ω, O ω ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint4 (Filter.Eventually.of_forall fun ω => by
        rw [hOdef]
        exact Set.indicator_nonneg (fun ω _ => le_max_right _ _) ω)]
      refine lintegral_congr fun ω => ?_
      rw [← survivalSet_eq_preimage, ← hA, hOdef]
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hpre, hstep]
        congr 2
        ring
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, ENNReal.ofReal_zero]
    have hset : (fun ω => prefixSums n fun i => G i ω) ⁻¹' {f : ℕ → ℝ | ∀ j ≤ n, f j ≤ g j}
        ∩ {ω | g (n + 1) - prefixSums n (fun i => G i ω) n < G n ω} = A \ A' := by
      ext ω
      rw [← survivalSet_eq_preimage, ← hA, hA'eq]
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_sdiff, not_and, not_le, hpre, hstep]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun _ => by linarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by linarith [h2 h1]⟩
    rw [hL, hset, measure_sdiff hA'A hA'm.nullMeasurableSet (measure_ne_top _ _)] at hcond
    have hsqrt : √(π * (v n : ℝ) / 2) ≤ √(π * V / 2) :=
      Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
    have hO0 : 0 ≤ ∫ ω, O ω ∂μ :=
      integral_nonneg fun ω => by
        rw [hOdef]
        exact Set.indicator_nonneg (fun ω _ => le_max_right _ _) ω
    have hdiff : 0 ≤ μ.real A - μ.real A' :=
      sub_nonneg.2 (measureReal_mono hA'A)
    have hreal := (ENNReal.ofReal_le_iff_le_toReal (by
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top (measure_ne_top μ A) tsub_le_self))).1 hcond
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      ENNReal.toReal_sub_of_le (measure_mono hA'A) (measure_ne_top _ _)] at hreal
    calc ∫ ω, O ω ∂μ ≤ √(π * (v n : ℝ) / 2) * ((μ A).toReal - (μ A').toReal) := hreal
      _ ≤ √(π * V / 2) * (μ.real A - μ.real A') :=
        mul_le_mul hsqrt le_rfl hdiff (Real.sqrt_nonneg _)
  rw [hΦ, hzero]
  linarith

/-- **Optional stopping.**  For a nondecreasing barrier with `g(0) ≥ 0` and variances at most `V`,
`E[1_{A_n}(g(n) - S_n)] ≤ g(0) + ∑_{j<n} (g(j+1) - g(j)) P(A_j) + √(πV/2)(1 - P(A_n))`: the one-step
bounds `RMF.IsGaussianWalk.survival_step`, summed. -/
theorem IsGaussianWalk.integral_survival_le (h : IsGaussianWalk G v μ) {g : ℕ → ℝ}
    (hg : Monotone g) (hg0 : 0 ≤ g 0) {V : ℝ} (hV : ∀ i, (v i : ℝ) ≤ V) (n : ℕ) :
    ∫ ω, (survivalSet G g n).indicator (fun ω => g n - walk G n ω) ω ∂μ
      ≤ g 0 + ∑ j ∈ Finset.range n, (g (j + 1) - g j) * μ.real (survivalSet G g j)
        + √(π * V / 2) * (1 - μ.real (survivalSet G g n)) := by
  induction n with
  | zero =>
    rw [survivalSet_zero G hg0]
    simp [walk]
  | succ n ih =>
    have hstep := h.survival_step (hg (Nat.le_succ n)) (hV n)
    rw [Finset.sum_range_succ]
    linarith

end Walk

/-! ### Anti-concentration at the barrier -/

section Window

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **A Gaussian window, conditionally**: if `R ~ N(0, W)`, `W ≠ 0`, is independent of `X`, then
`P(X ∈ S, R ∈ [ζ(X) - η, ζ(X)]) ≤ P(X ∈ S)·η/√(2πW)`. -/
lemma measure_inter_mem_Icc_le {α : Type*} [MeasurableSpace α] {X : Ω → α} {R : Ω → ℝ}
    {S : Set α} {ζ : α → ℝ} {W : ℝ≥0} (hW : W ≠ 0) (hX : Measurable X) (hR : Measurable R)
    (hS : MeasurableSet S) (hζ : Measurable ζ) (hind : IndepFun X R μ)
    (hlaw : μ.map R = gaussianReal 0 W) (η : ℝ) :
    μ (X ⁻¹' S ∩ {ω | R ω ∈ Set.Icc (ζ (X ω) - η) (ζ (X ω))})
      ≤ μ (X ⁻¹' S) * ENNReal.ofReal (η / √(2 * π * W)) := by
  have hT : MeasurableSet {p : α × ℝ | p.1 ∈ S ∧ p.2 ∈ Set.Icc (ζ p.1 - η) (ζ p.1)} :=
    (measurable_fst hS).inter
      ((measurableSet_le ((hζ.comp measurable_fst).sub measurable_const) measurable_snd).inter
        (measurableSet_le measurable_snd (hζ.comp measurable_fst)))
  have hprod := hind.map_prod_eq_prod_map_map hX.aemeasurable hR.aemeasurable
  rw [show X ⁻¹' S ∩ {ω | R ω ∈ Set.Icc (ζ (X ω) - η) (ζ (X ω))}
      = (fun ω => (X ω, R ω)) ⁻¹' {p : α × ℝ | p.1 ∈ S ∧ p.2 ∈ Set.Icc (ζ p.1 - η) (ζ p.1)}
      from rfl, ← Measure.map_apply (hX.prodMk hR) hT, hprod, Measure.prod_apply hT,
    ← Measure.map_apply hX hS, mul_comm, ← lintegral_indicator_const hS]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
    have hslice : Prod.mk x ⁻¹' {p : α × ℝ | p.1 ∈ S ∧ p.2 ∈ Set.Icc (ζ p.1 - η) (ζ p.1)}
        = Set.Icc (ζ x - η) (ζ x - η + η) := by
      ext r
      simp [hx]
    rw [hslice, hlaw]
    exact measure_Icc_gaussianReal_le_ofReal 0 hW _ _
  · rw [Set.indicator_of_notMem hx]
    have hslice : Prod.mk x ⁻¹' {p : α × ℝ | p.1 ∈ S ∧ p.2 ∈ Set.Icc (ζ p.1 - η) (ζ p.1)}
        = ∅ := by
      ext r
      simp [hx]
    rw [hslice, measure_empty]

end Window

/-! ### The renewal sum of a logarithmic barrier -/

/-- `∑_{1 ≤ j ≤ M} 1/j ≤ 1 + log M`. -/
lemma sum_Ico_inv_le_one_add_log (M : ℕ) (hM : 1 ≤ M) :
    ∑ j ∈ Finset.Ico 1 (M + 1), (1 / (j : ℝ)) ≤ 1 + Real.log M := by
  induction M with
  | zero => omega
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with rfl | hM0
    · norm_num
    · rw [Finset.sum_Ico_succ_top (by omega)]
      push_cast
      have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM0
      have hstep : 1 / ((M : ℝ) + 1) ≤ Real.log ((M : ℝ) + 1) - Real.log M := by
        rw [← Real.log_div (by linarith) (by linarith)]
        have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((M : ℝ) + 1) / M by positivity)
        have heq : 1 - (((M : ℝ) + 1) / M)⁻¹ = 1 / ((M : ℝ) + 1) := by
          field_simp
          ring
        linarith
      linarith [ih hM0]

/-- `1/(j√j) ≤ 2/√(j-1) - 2/√j` for `j ≥ 2`. -/
lemma inv_mul_sqrt_le_two_mul_sub {j : ℕ} (hj : 2 ≤ j) :
    1 / ((j : ℝ) * √j) ≤ 2 / √((j : ℝ) - 1) - 2 / √j := by
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  set a := √((j : ℝ) - 1) with ha
  set b := √(j : ℝ) with hb
  have ha0 : 0 < a := Real.sqrt_pos.2 (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.2 (by linarith)
  have ha2 : a ^ 2 = (j : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = (j : ℝ) := Real.sq_sqrt (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hjb : (j : ℝ) * b = b ^ 3 := by rw [← hb2]; ring
  have hid : (b - a) * (b + a) = 1 := by nlinarith [ha2, hb2]
  have hrhs : 2 / a - 2 / b = 2 * (b - a) / (a * b) := by
    field_simp
  rw [hjb, hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
  have hq : a * b + a ^ 2 ≤ 2 * b ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hab hb0.le]
  have hm := mul_le_mul_of_nonneg_left hq (sub_nonneg.2 hab)
  have hida : (b - a) * (a * b + a ^ 2) = a := by linear_combination a * hid
  have h1 : a ≤ 2 * (b - a) * b ^ 2 := by nlinarith [hm, hida]
  nlinarith [mul_le_mul_of_nonneg_left h1 hb0.le]

/-- `∑_{M < j < N} 1/(j√j) ≤ 2/√M` for `M ≥ 1`, by telescoping. -/
lemma sum_Ico_inv_mul_sqrt_le (M : ℕ) (hM : 1 ≤ M) (N : ℕ) :
    ∑ j ∈ Finset.Ico (M + 1) N, 1 / ((j : ℝ) * √j) ≤ 2 / √M := by
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hkey : ∀ N, M + 1 ≤ N →
      ∑ j ∈ Finset.Ico (M + 1) N, 1 / ((j : ℝ) * √j) ≤ 2 / √M - 2 / √((N : ℝ) - 1) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      simp only [Finset.Ico_self, Finset.sum_empty, Nat.cast_add, Nat.cast_one,
        add_sub_cancel_right, sub_self, le_refl]
    | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN]
      have hN2 : 2 ≤ N := by omega
      have hstep := inv_mul_sqrt_le_two_mul_sub hN2
      push_cast
      rw [add_sub_cancel_right]
      linarith
  rcases le_or_gt N (M + 1) with hN | hN
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have h := hkey N hN.le
    have h0 : 0 ≤ 2 / √((N : ℝ) - 1) := by positivity
    linarith

/-- **The renewal sum of a logarithmic barrier**: for `β ≥ 0`, `KU ≥ 1` and every `n`,
`∑_{1 ≤ j < n} β log((j+1)/j)·min(1, KU/√j) ≤ β(3 + log 2 + 2 log(KU))`.  Up to `M = ⌈(KU)²⌉` the
terms are at most `β/j`; beyond, at most `βKU/(j√j)`, which telescopes. -/
lemma sum_log_barrier_le {β K U : ℝ} (hβ : 0 ≤ β) (hKU : 1 ≤ K * U) (n : ℕ) :
    ∑ j ∈ Finset.Ico 1 n,
        (β * Real.log ((j + 1 : ℕ) : ℝ) - β * Real.log (j : ℝ)) * min 1 (K * U / √j)
      ≤ β * (3 + Real.log 2 + 2 * Real.log (K * U)) := by
  set M := ⌈(K * U) ^ 2⌉₊ with hMdef
  have hKU2 : (K * U) ^ 2 ≤ (M : ℝ) := Nat.le_ceil _
  have hM1 : 1 ≤ M := by
    have h : (1 : ℝ) ≤ (M : ℝ) := by nlinarith
    exact_mod_cast h
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hMlt : (M : ℝ) < (K * U) ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hsM : K * U ≤ √(M : ℝ) := by
    rw [show K * U = √((K * U) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt hKU2
  -- the pointwise bound
  set f : ℕ → ℝ := fun j => if j ≤ M then 1 / (j : ℝ) else K * U * (1 / ((j : ℝ) * √j))
    with hfdef
  have hterm : ∀ j ∈ Finset.Ico 1 n,
      (β * Real.log ((j + 1 : ℕ) : ℝ) - β * Real.log (j : ℝ)) * min 1 (K * U / √j) ≤ β * f j := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.1 hj).1
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hlog : Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) ≤ 1 / (j : ℝ) := by
      push_cast
      rw [← Real.log_div (by linarith) (by linarith)]
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((j : ℝ) + 1) / j by positivity)
      have heq : ((j : ℝ) + 1) / j - 1 = 1 / (j : ℝ) := by
        field_simp
        ring
      linarith
    have hlog0 : 0 ≤ Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) := by
      rw [sub_nonneg]
      exact Real.log_le_log (by linarith) (by push_cast; linarith)
    have hmin0 : 0 ≤ min 1 (K * U / √j) := le_min zero_le_one (by positivity)
    rw [show β * Real.log ((j + 1 : ℕ) : ℝ) - β * Real.log (j : ℝ)
        = β * (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)) by ring, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hβ
    rw [hfdef]
    simp only
    split_ifs with hjM
    · calc (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)) * min 1 (K * U / √j)
          ≤ (1 / (j : ℝ)) * 1 := mul_le_mul hlog (min_le_left _ _) hmin0 (by positivity)
        _ = 1 / (j : ℝ) := mul_one _
    · have hsj : 0 < √(j : ℝ) := Real.sqrt_pos.2 (by linarith)
      calc (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)) * min 1 (K * U / √j)
          ≤ (1 / (j : ℝ)) * (K * U / √j) :=
            mul_le_mul hlog (min_le_right _ _) hmin0 (by positivity)
        _ = K * U * (1 / ((j : ℝ) * √j)) := by
            field_simp
  have hf0 : ∀ j, 0 ≤ f j := by
    intro j
    rw [hfdef]
    simp only
    split_ifs <;> positivity
  -- extend the range and split at `M`
  have hsum1 : ∑ j ∈ Finset.Ico 1 n, f j ≤ ∑ j ∈ Finset.Ico 1 (max n (M + 1)), f j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (le_max_left _ _))
      fun j _ _ => hf0 j
  have hsplit : ∑ j ∈ Finset.Ico 1 (max n (M + 1)), f j
      = ∑ j ∈ Finset.Ico 1 (M + 1), f j + ∑ j ∈ Finset.Ico (M + 1) (max n (M + 1)), f j :=
    (Finset.sum_Ico_consecutive _ (by omega) (le_max_right _ _)).symm
  have hlow : ∑ j ∈ Finset.Ico 1 (M + 1), f j ≤ 1 + Real.log M := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j hj => ?_))
      (sum_Ico_inv_le_one_add_log M hM1)
    rw [hfdef]
    simp only
    rw [if_pos (by have := (Finset.mem_Ico.1 hj).2; omega)]
  have hhigh : ∑ j ∈ Finset.Ico (M + 1) (max n (M + 1)), f j ≤ 2 := by
    have h1 : ∑ j ∈ Finset.Ico (M + 1) (max n (M + 1)), f j
        = K * U * ∑ j ∈ Finset.Ico (M + 1) (max n (M + 1)), 1 / ((j : ℝ) * √j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hfdef]
      simp only
      rw [if_neg (by have := (Finset.mem_Ico.1 hj).1; omega)]
    rw [h1]
    have h2 := sum_Ico_inv_mul_sqrt_le M hM1 (max n (M + 1))
    have hsM0 : 0 < √(M : ℝ) := Real.sqrt_pos.2 (by linarith)
    calc K * U * ∑ j ∈ Finset.Ico (M + 1) (max n (M + 1)), 1 / ((j : ℝ) * √j)
        ≤ K * U * (2 / √M) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ ≤ 2 := by
          rw [mul_div_assoc', div_le_iff₀ hsM0]
          linarith
  have hlogM : Real.log M ≤ Real.log 2 + 2 * Real.log (K * U) := by
    have h1 : Real.log M ≤ Real.log (2 * (K * U) ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    push_cast at h1
    linarith
  calc ∑ j ∈ Finset.Ico 1 n,
          (β * Real.log ((j + 1 : ℕ) : ℝ) - β * Real.log (j : ℝ)) * min 1 (K * U / √j)
      ≤ ∑ j ∈ Finset.Ico 1 n, β * f j := Finset.sum_le_sum hterm
    _ = β * ∑ j ∈ Finset.Ico 1 n, f j := (Finset.mul_sum _ _ _).symm
    _ ≤ β * (3 + Real.log 2 + 2 * Real.log (K * U)) := by
        refine mul_le_mul_of_nonneg_left ?_ hβ
        linarith [hsum1, hsplit, hlow, hhigh, hlogM]

end RMF
