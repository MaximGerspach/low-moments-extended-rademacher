/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2PostFloor
import RMF.UniformLower.HP2PrefixBound
import RMF.Probability.StartFibreWeighted
import RMF.Weighted.HalfSecondMoment
import RMF.Weighted.HalfFirstMoment
import RMF.Probability.RademacherRestrictedSecondMoment.Ranges

/-!
# HP2's pair bound at a pair of heights

For heights `h₁, h₂ ∈ halfWindow k` (`k ≥ 20`) at depth `d` (`e^{-1} ≤ |h₁ - h₂|e^{k+d} ≤ 1`),
HP1's tubes `H(k,hᵢ) = RMF.hp1Tube` over `r` blocks (`σe^{k+r} ≤ 1/200`, tilt cutoff `y ≥ c_r`,
`c_m = ⌊e^{e^{k+m}}⌋ + 1`) and `F` the Euler product over the blocks `m < r`, the steps of the
bound `E[1_{H(k,h₁)∩H(k,h₂)}‖F(s₁)‖²‖F(s₂)‖²] ≤ E‖F(s₁)‖²E‖F(s₂)‖²·Φ/(r - b)`,
`b = hp2PostStart d`, `Φ = RMF.hp2PairBoundOf Cpost E_mass μ₁ μ₂ B₁ B₂`, which
`RMF.integral_hp1Tube_inter_le_hp2PairBoundOf` assembles:

* **The post, conditioned on its start** (`RMF.lintegral_hp1Tube_pair_le_post`): the post walks
  are independent of the values below `c_b` (`RMF.lintegral_eq_lintegral_lintegral_of_indepFun`);
  their fibre is the two-fold tilt of a block (`RMF.lintegral_pair_mul_eq_tiltedMeasure₂`) and the
  post bound `RMF.IsHP2PostBound` at the walks' own starts `Z_b`.
* **The bridge** `d ≤ m < b` (`RMF.lintegral_pre_le_bridge`): `A(Z_b) ≤ A(Z_d) + |ΔZ|` and
  `E₂'[(α₁ + |ΔZ₁|)(α₂ + |ΔZ₂|)] ≤ (α₁ + x)(α₂ + x)` once `E₂'ΔZᵢ² ≤ x²`, the second moment in
  the two-fold closed forms (`RMF.integral_bridgeZ_sq_eq`).
* **AM–GM on the products** (`RMF.lintegral_hp1Tube_pair_le_prefix`), each term by the one-point
  tilt of a block (`RMF.lintegral_normSq_mul_eq_tiltedMeasure`), `‖F^{pre}(s_h)‖² = e^{2(Z_d +
  Mean_d)}` (`RMF.normSq_prefix_eq_exp`), the prefix bound `RMF.hp2PrefixBound` and the mass
  factor.
* **The hypotheses discharged**: the post bound at a cell's numerals and push
  (`RMF.isHP2PostBound_of_numerals`); the bridge by cosine-sum bounds
  (`RMF.bridge_moment_le_of_cos`).
* **The deep pairs** (`RMF.integral_hp1Tube_inter_le_deep`): the prefix alone at `M = r`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### Conditioning by independence -/

section Freeze

/-- **Freezing one argument by independence**: for independent `Φ`, `Ψ`,
`E[F(Φ, Ψ)] = E[(x ↦ E[F(x, Ψ)])(Φ)]` for measurable `F ≥ 0`
(`RMF.lintegral_prod_map_of_indepFun`, Tonelli). -/
theorem lintegral_eq_lintegral_lintegral_of_indepFun {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] {P : Measure Ω} [IsProbabilityMeasure P]
    {Φ : Ω → α} {Ψ : Ω → β} (hΦ : Measurable Φ) (hΨ : Measurable Ψ) (hind : IndepFun Φ Ψ P)
    {F : α × β → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (Φ ω, Ψ ω) ∂P = ∫⁻ ω, (∫⁻ ω', F (Φ ω, Ψ ω') ∂P) ∂P := by
  rw [lintegral_prod_map_of_indepFun hΦ hΨ hind hF]
  have hinner : ∀ x, ∫⁻ y, F (x, y) ∂(P.map Ψ) = ∫⁻ ω', F (x, Ψ ω') ∂P := fun x =>
    lintegral_map (hF.comp measurable_prodMk_left) hΨ
  have hmeas : Measurable fun x => ∫⁻ ω', F (x, Ψ ω') ∂P := by
    have h := hF.lintegral_prod_right' (ν := P.map Ψ)
    simpa only [hinner] using h
  simp_rw [hinner]
  exact lintegral_map hmeas hΦ

end Freeze

section PrimeAlgebra

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The values at the primes of `[a, b)` and of `[b, c)` are independent. -/
lemma indep_primeAlgebra (hX : IsRademacherPrimeValues X μ) (a b c : ℕ) :
    Indep (primeAlgebra X a b) (primeAlgebra X b c) μ :=
  (IndepFun_iff_Indep _ _ _).1 (hX.indepFun_of_disjoint (S := primesIco a b)
    (T := primesIco b c) (fun _ hp => prime_of_mem_primesIco hp)
    (fun _ hp => prime_of_mem_primesIco hp) (disjoint_primesIco a b c))

/-- Functions of the values in `[a, b)` and in `[b, c)` are independent. -/
lemma indepFun_of_primeAlgebra (hX : IsRademacherPrimeValues X μ) {a b c : ℕ} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {Φ : Ω → α} {Ψ : Ω → β}
    (hΦ : Measurable[primeAlgebra X a b] Φ) (hΨ : Measurable[primeAlgebra X b c] Ψ) :
    IndepFun Φ Ψ μ := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left (indep_of_indep_of_le_right (indep_primeAlgebra hX a b c)
    hΨ.comap_le) hΦ.comap_le

/-- **Lower integrals split across a cut**: `E[g₁g₂] = E[g₁]E[g₂]` for `g₁ ≥ 0` a function of the
values in `[a, b)` and `g₂ ≥ 0` one of the values in `[b, c)`. -/
lemma lintegral_mul_of_primeAlgebra (hX : IsRademacherPrimeValues X μ) {a b c : ℕ}
    {g₁ g₂ : Ω → ℝ≥0∞} (hg₁ : Measurable[primeAlgebra X a b] g₁)
    (hg₂ : Measurable[primeAlgebra X b c] g₂) :
    ∫⁻ ω, g₁ ω * g₂ ω ∂μ = (∫⁻ ω, g₁ ω ∂μ) * ∫⁻ ω, g₂ ω ∂μ :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (primeAlgebra_le hX a b) (primeAlgebra_le hX b c) (indep_primeAlgebra hX a b c) hg₁ hg₂

omit [MeasurableSpace Ω] in
/-- `‖F_{[a,b)}(s)‖²` is a function of the values in `[a, b)`. -/
lemma measurable_primeAlgebra_normSq (a b : ℕ) (s : ℂ) :
    Measurable[primeAlgebra X a b] fun ω =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s ω‖ ^ 2 := by
  have h : (fun ω =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s ω‖ ^ 2)
      = normSqPoly (primesIco a b) s ∘ fun ω (p : ↥(primesIco a b)) => X (p : ℕ) ω := by
    funext ω
    exact (normSqPoly_primesIco a b s ω).symm
  rw [h]
  exact (measurable_normSqPoly _ s).comp (Measurable.of_comap_le le_rfl)

/-- Three factors on `[0, a)`, `[a, b)`, `[b, y)` split, the middle one carrying `g`. -/
lemma lintegral_ofReal_mul_split₃ (hX : IsRademacherPrimeValues X μ) {a b y : ℕ}
    (hab : a ≤ b) (hby : b ≤ y) {u₀ u₁ u₂ : Ω → ℝ}
    (h₀ : Measurable[primeAlgebra X 0 a] u₀) (h₁ : Measurable[primeAlgebra X a b] u₁)
    (h₂ : Measurable[primeAlgebra X b y] u₂) {g : Ω → ℝ≥0∞}
    (hg : Measurable[primeAlgebra X a b] g) :
    ∫⁻ ω, ENNReal.ofReal (u₀ ω) * (ENNReal.ofReal (u₁ ω) * g ω * ENNReal.ofReal (u₂ ω)) ∂μ
      = (∫⁻ ω, ENNReal.ofReal (u₀ ω) ∂μ) * ((∫⁻ ω, ENNReal.ofReal (u₁ ω) * g ω ∂μ)
        * ∫⁻ ω, ENNReal.ofReal (u₂ ω) ∂μ) := by
  have hm₁ : primeAlgebra X a b ≤ primeAlgebra X a y := primeAlgebra_mono le_rfl hby
  have hm₂ : primeAlgebra X b y ≤ primeAlgebra X a y := primeAlgebra_mono hab le_rfl
  have e₀ : Measurable[primeAlgebra X 0 a] fun ω => ENNReal.ofReal (u₀ ω) :=
    ENNReal.measurable_ofReal.comp h₀
  have e₁ : Measurable[primeAlgebra X a b] fun ω => ENNReal.ofReal (u₁ ω) * g ω :=
    (ENNReal.measurable_ofReal.comp h₁).mul hg
  have e₂ : Measurable[primeAlgebra X b y] fun ω => ENNReal.ofReal (u₂ ω) :=
    ENNReal.measurable_ofReal.comp h₂
  have e₁₂ : Measurable[primeAlgebra X a y] fun ω =>
      ENNReal.ofReal (u₁ ω) * g ω * ENNReal.ofReal (u₂ ω) :=
    (e₁.mono hm₁ le_rfl).mul (e₂.mono hm₂ le_rfl)
  rw [lintegral_mul_of_primeAlgebra hX e₀ e₁₂, lintegral_mul_of_primeAlgebra hX e₁ e₂]

/-- **A tilt whose weight splits in three**: if `e^T = u₀u₁u₂` a.e. with `uᵢ ≥ 0` integrable
functions of the values in `[0, a)`, `[a, b)`, `[b, y)` of positive mean, then for `g ≥ 0` a
function of the values in `[a, b)`, `E[u₁g] = E[u₁]·E_T[g]` under `μ.tilted T`. -/
lemma lintegral_ofReal_mul_eq_tilted_of_split (hX : IsRademacherPrimeValues X μ) {a b y : ℕ}
    (hab : a ≤ b) (hby : b ≤ y) {u₀ u₁ u₂ : Ω → ℝ}
    (h₀ : Measurable[primeAlgebra X 0 a] u₀) (h₁ : Measurable[primeAlgebra X a b] u₁)
    (h₂ : Measurable[primeAlgebra X b y] u₂) (hu₀ : ∀ ω, 0 ≤ u₀ ω) (hu₁ : ∀ ω, 0 ≤ u₁ ω)
    (hu₂ : ∀ ω, 0 ≤ u₂ ω) (hi₀ : Integrable u₀ μ) (hi₁ : Integrable u₁ μ)
    (hi₂ : Integrable u₂ μ) (hp₀ : 0 < ∫ ω, u₀ ω ∂μ) (hp₁ : 0 < ∫ ω, u₁ ω ∂μ)
    (hp₂ : 0 < ∫ ω, u₂ ω ∂μ) {T : Ω → ℝ}
    (hT : (fun ω => Real.exp (T ω)) =ᵐ[μ] fun ω => u₀ ω * u₁ ω * u₂ ω)
    {g : Ω → ℝ≥0∞} (hg : Measurable[primeAlgebra X a b] g) :
    ∫⁻ ω, ENNReal.ofReal (u₁ ω) * g ω ∂μ
      = ENNReal.ofReal (∫ ω, u₁ ω ∂μ) * ∫⁻ ω, g ω ∂(μ.tilted T) := by
  have hL : ∀ {u : Ω → ℝ}, (∀ ω, 0 ≤ u ω) → Integrable u μ →
      ∫⁻ ω, ENNReal.ofReal (u ω) ∂μ = ENNReal.ofReal (∫ ω, u ω ∂μ) := fun hu hi =>
    (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hu)).symm
  have hsplit := lintegral_ofReal_mul_split₃ hX hab hby h₀ h₁ h₂ hg
  have hsplit1 := lintegral_ofReal_mul_split₃ hX hab hby h₀ h₁ h₂ (g := fun _ => 1)
    measurable_const
  simp only [mul_one] at hsplit1
  rw [hL hu₀ hi₀, hL hu₁ hi₁, hL hu₂ hi₂] at hsplit1
  rw [hL hu₀ hi₀, hL hu₂ hi₂] at hsplit
  -- the normaliser
  set Z : ℝ := ∫ ω, Real.exp (T ω) ∂μ with hZdef
  have hZ : Z = (∫ ω, u₀ ω ∂μ) * ((∫ ω, u₁ ω ∂μ) * ∫ ω, u₂ ω ∂μ) := by
    have hm₁ : primeAlgebra X a b ≤ primeAlgebra X 0 y :=
      primeAlgebra_mono (Nat.zero_le a) hby
    have hm₀ : primeAlgebra X 0 a ≤ primeAlgebra X 0 y :=
      primeAlgebra_mono le_rfl (hab.trans hby)
    have hm₂ : primeAlgebra X b y ≤ primeAlgebra X 0 y :=
      primeAlgebra_mono (Nat.zero_le b) le_rfl
    have hle : primeAlgebra X 0 y ≤ ‹MeasurableSpace Ω› := primeAlgebra_le hX 0 y
    have hmeas : AEStronglyMeasurable (fun ω => u₀ ω * (u₁ ω * u₂ ω)) μ :=
      ((h₀.mono (hm₀.trans hle) le_rfl).mul ((h₁.mono (hm₁.trans hle) le_rfl).mul
        (h₂.mono (hm₂.trans hle) le_rfl))).aestronglyMeasurable
    rw [hZdef, integral_congr_ae hT, integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun ω => by have := hu₀ ω; have := hu₁ ω; have := hu₂ ω; positivity)
      (by simpa only [mul_assoc] using hmeas)]
    have hpt : ∀ ω, ENNReal.ofReal (u₀ ω * u₁ ω * u₂ ω)
        = ENNReal.ofReal (u₀ ω) * (ENNReal.ofReal (u₁ ω) * ENNReal.ofReal (u₂ ω)) := fun ω => by
      rw [mul_assoc, ENNReal.ofReal_mul (hu₀ ω), ENNReal.ofReal_mul (hu₁ ω)]
    simp_rw [hpt, hsplit1]
    rw [← ENNReal.ofReal_mul hp₁.le, ← ENNReal.ofReal_mul hp₀.le, ENNReal.toReal_ofReal
      (by positivity)]
  have hZpos : 0 < Z := by rw [hZ]; positivity
  -- the tilted integral
  have htilt : ∫⁻ ω, g ω ∂(μ.tilted T)
      = ENNReal.ofReal Z⁻¹ * (ENNReal.ofReal (∫ ω, u₀ ω ∂μ)
        * ((∫⁻ ω, ENNReal.ofReal (u₁ ω) * g ω ∂μ) * ENNReal.ofReal (∫ ω, u₂ ω ∂μ))) := by
    rw [lintegral_tilted, ← hsplit, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hT] with ω hω
    rw [← hZdef, hω]
    have h1 : u₀ ω * u₁ ω * u₂ ω / Z = Z⁻¹ * (u₀ ω * (u₁ ω * u₂ ω)) := by
      rw [div_eq_inv_mul]; ring
    rw [h1, ENNReal.ofReal_mul (inv_nonneg.2 hZpos.le), ENNReal.ofReal_mul (hu₀ ω),
      ENNReal.ofReal_mul (hu₁ ω)]
    ring
  rw [htilt]
  have hone : ENNReal.ofReal (∫ ω, u₁ ω ∂μ) * (ENNReal.ofReal Z⁻¹
      * (ENNReal.ofReal (∫ ω, u₀ ω ∂μ) * ENNReal.ofReal (∫ ω, u₂ ω ∂μ))) = 1 := by
    rw [← ENNReal.ofReal_mul hp₀.le, ← ENNReal.ofReal_mul (inv_nonneg.2 hZpos.le),
      ← ENNReal.ofReal_mul hp₁.le, ← ENNReal.ofReal_one]
    congr 1
    rw [hZ]
    field_simp
  calc ∫⁻ ω, ENNReal.ofReal (u₁ ω) * g ω ∂μ
      = (ENNReal.ofReal (∫ ω, u₁ ω ∂μ) * (ENNReal.ofReal Z⁻¹
          * (ENNReal.ofReal (∫ ω, u₀ ω ∂μ) * ENNReal.ofReal (∫ ω, u₂ ω ∂μ))))
        * ∫⁻ ω, ENNReal.ofReal (u₁ ω) * g ω ∂μ := by rw [hone, one_mul]
    _ = _ := by ring

end PrimeAlgebra

/-! ### The tilt identities for a block

For `g ≥ 0` a function of the values in a block `[a, b)` below the cutoff `y`, the block's weight
against `g` is the block's moment times the tilted mean of `g`: the primes of `[0, a)` and
`[b, y)` cancel between the weight and the normaliser. -/

section TiltIco

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The two-fold tilt of a block**: for `g ≥ 0` a function of the values in `[a, b)`, `b ≤ y`,
`E[‖F_{[a,b)}(s₁)‖²‖F_{[a,b)}(s₂)‖²g] = E‖F_{[a,b)}(s₁)‖²‖F_{[a,b)}(s₂)‖²·E₂'[g]`, `E₂'` under
the two-fold tilt at the cutoff `y`. -/
theorem lintegral_pair_mul_eq_tiltedMeasure₂ (hX : IsRademacherPrimeValues X μ) {a b y : ℕ}
    (hab : a ≤ b) (hby : b ≤ y) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re)
    {g : Ω → ℝ≥0∞} (hg : Measurable[primeAlgebra X a b] g) :
    ∫⁻ ω, ENNReal.ofReal
        (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s₁ ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s₂ ω‖ ^ 2)
        * g ω ∂μ
      = ENNReal.ofReal (∫ ω,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s₂ ω‖ ^ 2
            ∂μ)
        * ∫⁻ ω, g ω ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) := by
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hpm : ∀ c d, Measurable[primeAlgebra X c d] fun ω =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) c d s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) c d s₂ ω‖ ^ 2 :=
    fun c d => (measurable_primeAlgebra_normSq c d s₁).mul (measurable_primeAlgebra_normSq c d s₂)
  have hT : (fun ω => Real.exp (tiltExponent₂ (fun ω => squarefreeExtension fun p => X p ω)
      y s₁ s₂ ω)) =ᵐ[μ] fun ω =>
      (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 a s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 a s₂ ω‖ ^ 2)
      * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s₂ ω‖ ^ 2)
      * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b y s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b y s₂ ω‖ ^ 2) := by
    filter_upwards [hf.exp_tiltExponent₂_ae_eq y hs₁ hs₂] with ω hω
    rw [hω, ← randomEulerProductIco_zero, ← randomEulerProductIco_zero,
      normSq_randomEulerProductIco_split (Nat.zero_le a) (hab.trans hby) s₁ ω,
      normSq_randomEulerProductIco_split (Nat.zero_le a) (hab.trans hby) s₂ ω,
      normSq_randomEulerProductIco_split hab hby s₁ ω,
      normSq_randomEulerProductIco_split hab hby s₂ ω]
    ring
  exact lintegral_ofReal_mul_eq_tilted_of_split hX hab hby (hpm 0 a) (hpm a b) (hpm b y)
    (fun ω => by positivity) (fun ω => by positivity) (fun ω => by positivity)
    (hf.integrable_normSq_pair_Ico 0 a s₁ s₂) (hf.integrable_normSq_pair_Ico a b s₁ s₂)
    (hf.integrable_normSq_pair_Ico b y s₁ s₂) (hf.integral_normSq_mul_normSq_Ico_pos 0 a hs₁ hs₂)
    (hf.integral_normSq_mul_normSq_Ico_pos a b hs₁ hs₂)
    (hf.integral_normSq_mul_normSq_Ico_pos b y hs₁ hs₂) hT hg

/-- **The one-point tilt of a block**: for `g ≥ 0` a function of the values in `[a, b)`, `b ≤ y`,
`E[‖F_{[a,b)}(s)‖²g] = E‖F_{[a,b)}(s)‖²·E'[g]`, `E'` under the one-point tilt at the cutoff
`y`. -/
theorem lintegral_normSq_mul_eq_tiltedMeasure (hX : IsRademacherPrimeValues X μ) {a b y : ℕ}
    (hab : a ≤ b) (hby : b ≤ y) {s : ℂ} (hs : 0 < s.re) {g : Ω → ℝ≥0∞}
    (hg : Measurable[primeAlgebra X a b] g) :
    ∫⁻ ω, ENNReal.ofReal
        (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s ω‖ ^ 2)
        * g ω ∂μ
      = ENNReal.ofReal (∫ ω,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s ω‖ ^ 2 ∂μ)
        * ∫⁻ ω, g ω ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) := by
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hT : (fun ω => Real.exp (tiltExponent (fun ω => squarefreeExtension fun p => X p ω)
      y s ω)) =ᵐ[μ] fun ω =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 a s ω‖ ^ 2
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s ω‖ ^ 2
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b y s ω‖ ^ 2 := by
    filter_upwards [hf.exp_tiltExponent_ae_eq y hs] with ω hω
    rw [hω, ← randomEulerProductIco_zero,
      normSq_randomEulerProductIco_split (Nat.zero_le a) (hab.trans hby) s ω,
      normSq_randomEulerProductIco_split hab hby s ω]
    ring
  have hpos : ∀ c d, 0 < ∫ ω,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) c d s ω‖ ^ 2 ∂μ :=
    fun c d => lt_of_lt_of_le one_pos (one_le_integral_normSq_Ico hX c d s)
  exact lintegral_ofReal_mul_eq_tilted_of_split hX hab hby
    (measurable_primeAlgebra_normSq 0 a s) (measurable_primeAlgebra_normSq a b s)
    (measurable_primeAlgebra_normSq b y s)
    (fun ω => by positivity) (fun ω => by positivity) (fun ω => by positivity)
    (hf.integrable_norm_randomEulerProductIco_sq 0 a s)
    (hf.integrable_norm_randomEulerProductIco_sq a b s)
    (hf.integrable_norm_randomEulerProductIco_sq b y s) (hpos 0 a) (hpos a b) (hpos b y) hT hg

end TiltIco

/-! ### The tubes as functions of the prime values -/

/-- The post start is past the depth. -/
lemma le_hp2PostStart (d : ℕ) : d ≤ hp2PostStart d := by
  unfold hp2PostStart
  split_ifs <;> omega

/-- The post start is at least `2`. -/
lemma two_le_hp2PostStart (d : ℕ) : 2 ≤ hp2PostStart d := by
  unfold hp2PostStart
  split_ifs <;> omega

/-- The cuts `⌊e^{e^{k+m}}⌋ + 1` grow with `m`. -/
lemma cut_mono (k : ℕ) {m m' : ℕ} (h : m ≤ m') :
    ⌊blockScale k m⌋₊ + 1 ≤ ⌊blockScale k m'⌋₊ + 1 :=
  Nat.succ_le_succ (Nat.floor_mono (blockScale_mono _ h))

/-- The cut at the top of the post walk at offset `k + b`. -/
lemma scaleCut_natCast_add_add (k b n : ℕ) :
    scaleCut ((k : ℝ) + b + n) = ⌊blockScale k (b + n)⌋₊ + 1 := by
  have h : ((0 : ℕ) : ℝ) + ((k : ℝ) + b + n) = ((b + n : ℕ) : ℝ) + k := by push_cast; ring
  unfold scaleCut blockScale
  rw [h]

section Tubes

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- HP1's tube over the first `M` blocks is an event of the values in `[c₀, c_{M'})`, `M ≤ M'`. -/
lemma measurableSet_primeAlgebra_hp1Tube (y k : ℕ) {M M' : ℕ} (hM : M ≤ M')
    (σ h : ℝ) :
    MeasurableSet[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k M'⌋₊ + 1)]
      (hp1Tube X μ y k M σ h) :=
  measurableSet_primeAlgebra_barrierEvent (k : ℝ) σ h (n := M)
    (by rw [scaleCut_add]; exact cut_mono k hM) _ _

/-- The centred walk after `M` blocks is a function of the values in `[c₀, c_{M'})`. -/
lemma measurable_primeAlgebra_windowZ (y k : ℕ) {M M' : ℕ} (hM : M ≤ M')
    (σ h : ℝ) :
    Measurable[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k M'⌋₊ + 1)]
      (windowZ X μ y k σ h M) := by
  have hle : primeAlgebra X (scaleCut (k : ℝ)) (scaleCut ((k : ℝ) + M))
      ≤ primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k M'⌋₊ + 1) :=
    primeAlgebra_mono le_rfl (by rw [scaleCut_add]; exact cut_mono k hM)
  have hw : Measurable[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k M'⌋₊ + 1)]
      (walk (halfBlock X k σ h) M) :=
    (measurable_primeAlgebra_walk (X := X) (k : ℝ) σ h (le_refl M)).mono hle le_rfl
  exact hw.sub_const _

omit [MeasurableSpace Ω] in
/-- The post walk from block `b` is a function of the values in `[c_b, c_{b+n})`. -/
lemma measurable_primeAlgebra_walk_post (k b n : ℕ) (σ h : ℝ) {j : ℕ} (hj : j ≤ n) :
    Measurable[primeAlgebra X (⌊blockScale k b⌋₊ + 1) (⌊blockScale k (b + n)⌋₊ + 1)]
      (walk (halfBlock X ((k : ℝ) + b) σ h) j) := by
  have h := measurable_primeAlgebra_walk (X := X) ((k : ℝ) + b) σ h hj
  rwa [scaleCut_add, scaleCut_natCast_add_add] at h

/-- HP2's post tube is an event of the values in `[c_b, c_{b+n})`. -/
lemma measurableSet_primeAlgebra_hp2PostTube (y k b n : ℕ)
    (σ h a A B ρ z : ℝ) :
    MeasurableSet[primeAlgebra X (⌊blockScale k b⌋₊ + 1) (⌊blockScale k (b + n)⌋₊ + 1)]
      (hp2PostTube X μ y k b n σ h a A B ρ z) := by
  have h := measurableSet_primeAlgebra_barrierEvent (X := X) ((k : ℝ) + b) σ h (n := n)
    (b := scaleCut ((k : ℝ) + b + n)) le_rfl
    (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h (i + b) - A - B * ((b : ℝ) + j)
      - ρ - z)
    (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h (i + b) + a + ρ - z)
  rw [scaleCut_add, scaleCut_natCast_add_add] at h
  exact h

/-- The post tube as a condition on the post walk plus its start. -/
lemma mem_hp2PostTube_iff {y k b n : ℕ} {σ h a A B ρ z : ℝ} {ω : Ω} :
    ω ∈ hp2PostTube X μ y k b n σ h a A B ρ z ↔
      ∀ j ∈ Finset.Icc 1 n, walk (halfBlock X ((k : ℝ) + b) σ h) j ω + z ∈ Set.Icc
        (∑ i ∈ Finset.range j, windowMeanH X μ y k σ h (i + b) - A - B * ((b : ℝ) + j) - ρ)
        (∑ i ∈ Finset.range j, windowMeanH X μ y k σ h (i + b) + a + ρ) := by
  simp only [hp2PostTube, barrierEvent, Set.mem_setOf_eq, Set.mem_Icc, Finset.mem_Icc]
  constructor
  · intro hω j hj
    have := hω j hj.1 hj.2
    constructor <;> linarith [this.1, this.2]
  · intro hω j h1 h2
    have := hω j ⟨h1, h2⟩
    constructor <;> linarith [this.1, this.2]

end Tubes

/-- The pairs `(z, w)` of a start and a path whose shifted path stays in `[U_j, V_j]` for
`1 ≤ j ≤ n` form a measurable set. -/
lemma measurableSet_shiftedPath (n : ℕ) (U V : ℕ → ℝ) :
    MeasurableSet {q : ℝ × (ℕ → ℝ) | ∀ j ∈ Finset.Icc 1 n, q.2 j + q.1 ∈ Set.Icc (U j) (V j)} := by
  have : {q : ℝ × (ℕ → ℝ) | ∀ j ∈ Finset.Icc 1 n, q.2 j + q.1 ∈ Set.Icc (U j) (V j)}
      = ⋂ j ∈ Finset.Icc 1 n, (fun q : ℝ × (ℕ → ℝ) => q.2 j + q.1) ⁻¹' Set.Icc (U j) (V j) := by
    ext q
    simp
  rw [this]
  refine Finset.measurableSet_biInter _ fun j _ => ?_
  have hm : Measurable fun q : ℝ × (ℕ → ℝ) => q.2 j + q.1 :=
    ((measurable_pi_apply j).comp measurable_snd).add measurable_fst
  exact hm measurableSet_Icc

/-! ### The post part, conditioned on the start -/

section PostStep

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The post walk, stopped after `n` blocks, with its start lies in the shifted-path set iff the
walk lies in the post tube at that start. -/
lemma mem_shiftedPath_iff_mem_hp2PostTube {y k b n : ℕ} {σ h a A B ρ z : ℝ} {ω : Ω} :
    (z, fun j => walk (halfBlock X ((k : ℝ) + b) σ h) (min j n) ω)
        ∈ {q : ℝ × (ℕ → ℝ) | ∀ j ∈ Finset.Icc 1 n, q.2 j + q.1 ∈ Set.Icc
          (∑ i ∈ Finset.range j, windowMeanH X μ y k σ h (i + b) - A - B * ((b : ℝ) + j) - ρ)
          (∑ i ∈ Finset.range j, windowMeanH X μ y k σ h (i + b) + a + ρ)}
      ↔ ω ∈ hp2PostTube X μ y k b n σ h a A B ρ z := by
  rw [mem_hp2PostTube_iff]
  simp only [Set.mem_setOf_eq]
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  rw [min_eq_left (Finset.mem_Icc.1 hj).2]

/-- **The post bound at a pair** at HP1's tube parameters, the shape of the conclusion of
`RMF.hp2Post_bound_of_numerals_floor`: for starts `zᵢ ∈ [-5/2 - 3b - ρ, 3/2 + ρ]` at the post
start `b = hp2PostStart d`, `ρ = 10⁻¹⁵`, the two post tubes have two-fold tilted probability at
most `Cpost(A₁ + ch)(A₂ + ch)/(r - b)`, `Aᵢ = max(3/2 + ρ - zᵢ, 0)`. -/
def IsHP2PostBound (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k d r : ℕ) (σ h₁ h₂ Cpost ch : ℝ) : Prop :=
  ∀ z₁ z₂ : ℝ,
    (-(5 / 2) - 3 * (hp2PostStart d : ℝ) - 1 / 10 ^ 15 ≤ z₁ ∧ z₁ ≤ 3 / 2 + 1 / 10 ^ 15) →
    (-(5 / 2) - 3 * (hp2PostStart d : ℝ) - 1 / 10 ^ 15 ≤ z₂ ∧ z₂ ≤ 3 / 2 + 1 / 10 ^ 15) →
    (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h₁)
        (shiftLine σ h₂) μ).real
        (hp2PostTube X μ y k (hp2PostStart d) (r - hp2PostStart d) σ h₁ (3 / 2) (5 / 2) 3
            (1 / 10 ^ 15) z₁
          ∩ hp2PostTube X μ y k (hp2PostStart d) (r - hp2PostStart d) σ h₂ (3 / 2) (5 / 2) 3
            (1 / 10 ^ 15) z₂)
      ≤ Cpost * (max (3 / 2 + 1 / 10 ^ 15 - z₁) 0 + ch) * (max (3 / 2 + 1 / 10 ^ 15 - z₂) 0 + ch)
        / ((r - hp2PostStart d : ℕ) : ℝ)

/-- **The post part, conditioned on its start.**  On `H(k,h₁) ∩ H(k,h₂)` (HP1's tubes over `r`
blocks, cutoff `y ≥ c_r`), the pair weight over the blocks `m < r` is at most the post blocks'
pair moment times the prefix-and-bridge weight against the post bound at the walks' own starts
`zᵢ = RMF.windowZ` at `b = hp2PostStart d`, with only the prefix tubes (`d` blocks) kept:
`E[1_{H₁∩H₂}W_{[0,r)}] ≤ E W_{[b,r)}·E[1_{pre}W_{[0,b)}·Cpost(A₁ + ch)(A₂ + ch)/(r - b)]`.
The post walk is independent of the values below `c_b`; its fibre is the two-fold tilt identity
(`RMF.lintegral_pair_mul_eq_tiltedMeasure₂`) and the post bound. -/
theorem lintegral_hp1Tube_pair_le_post (hX : IsRademacherPrimeValues X μ) {k d r y : ℕ}
    {σ h₁ h₂ : ℝ} (hσ : 0 ≤ σ) (hbr : hp2PostStart d ≤ r) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y)
    {Cpost ch : ℝ} (hpost : IsHP2PostBound X μ y k d r σ h₁ h₂ Cpost ch) :
    ∫⁻ ω, ENNReal.ofReal ((hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂).indicator (fun ω =>
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2) ω) ∂μ
      ≤ ENNReal.ofReal (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k (hp2PostStart d)⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖
              ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k (hp2PostStart d)⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖
              ^ 2 ∂μ)
        * ∫⁻ ω, ENNReal.ofReal ((hp1Tube X μ y k d σ h₁ ∩ hp1Tube X μ y k d σ h₂).indicator
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k (hp2PostStart d)⌋₊ + 1)
                (shiftLine σ h₁) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k (hp2PostStart d)⌋₊ + 1)
                (shiftLine σ h₂) ω‖ ^ 2
              * (Cpost * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₁ (hp2PostStart d) ω) 0
                  + ch)
                * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₂ (hp2PostStart d) ω) 0 + ch)
                / ((r - hp2PostStart d : ℕ) : ℝ))) ω) ∂μ := by
  classical
  haveI := hX.isProbabilityMeasure
  have hs₁ : 0 < (shiftLine σ h₁).re := by rw [re_shiftLine]; linarith
  have hs₂ : 0 < (shiftLine σ h₂).re := by rw [re_shiftLine]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure₂_rademacher hX y hs₁ hs₂
  have hdb := le_hp2PostStart d
  have hb2 := two_le_hp2PostStart d
  have hdr : d ≤ r := hdb.trans hbr
  have hbn : hp2PostStart d + (r - hp2PostStart d) = r := by omega
  have hc0b : ⌊blockScale k 0⌋₊ + 1 ≤ ⌊blockScale k (hp2PostStart d)⌋₊ + 1 :=
    cut_mono k (Nat.zero_le _)
  have hcbr : ⌊blockScale k (hp2PostStart d)⌋₊ + 1 ≤ ⌊blockScale k r⌋₊ + 1 := cut_mono k hbr
  /- the objects -/
  set b := hp2PostStart d with hbdef
  set n := r - b with hndef
  set E : Set Ω := hp1Tube X μ y k d σ h₁ ∩ hp1Tube X μ y k d σ h₂
    ∩ {ω | -(5 / 2) - 3 * (b : ℝ) - 1 / 10 ^ 15 ≤ windowZ X μ y k σ h₁ b ω
      ∧ windowZ X μ y k σ h₁ b ω ≤ 3 / 2 + 1 / 10 ^ 15}
    ∩ {ω | -(5 / 2) - 3 * (b : ℝ) - 1 / 10 ^ 15 ≤ windowZ X μ y k σ h₂ b ω
      ∧ windowZ X μ y k σ h₂ b ω ≤ 3 / 2 + 1 / 10 ^ 15} with hEdef
  set pre : Ω → ℝ := fun ω =>
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k b⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k b⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 with hpredef
  set post : Ω → ℝ := fun ω =>
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (⌊blockScale k b⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (⌊blockScale k b⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 with hpostdef
  set U : ℝ → ℕ → ℝ := fun h j =>
    ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h (i + b) - 5 / 2 - 3 * ((b : ℝ) + j)
      - 1 / 10 ^ 15 with hUdef
  set V : ℝ → ℕ → ℝ := fun h j =>
    ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h (i + b) + 3 / 2 + 1 / 10 ^ 15 with hVdef
  set S : ℝ → Set (ℝ × (ℕ → ℝ)) := fun h =>
    {q | ∀ j ∈ Finset.Icc 1 n, q.2 j + q.1 ∈ Set.Icc (U h j) (V h j)} with hSdef
  set Φ : Ω → ℝ × (ℝ × ℝ) := fun ω =>
    (E.indicator pre ω, (windowZ X μ y k σ h₁ b ω, windowZ X μ y k σ h₂ b ω)) with hΦdef
  set Ψ : Ω → (ℕ → ℝ) × ((ℕ → ℝ) × ℝ) := fun ω =>
    (fun j => walk (halfBlock X ((k : ℝ) + b) σ h₁) (min j n) ω,
      (fun j => walk (halfBlock X ((k : ℝ) + b) σ h₂) (min j n) ω, post ω)) with hΨdef
  set F : (ℝ × (ℝ × ℝ)) × ((ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal q.1.1 * ((S h₁).indicator 1 (q.1.2.1, q.2.1)
      * ((S h₂).indicator 1 (q.1.2.2, q.2.2.1) * ENNReal.ofReal q.2.2.2)) with hFdef
  /- the tubes and the post tubes, as sets of the shifted paths -/
  have hSmem : ∀ (h z : ℝ) (ω : Ω),
      (z, fun j => walk (halfBlock X ((k : ℝ) + b) σ h) (min j n) ω) ∈ S h
        ↔ ω ∈ hp2PostTube X μ y k b n σ h (3 / 2) (5 / 2) 3 (1 / 10 ^ 15) z := by
    intro h z ω
    have := mem_shiftedPath_iff_mem_hp2PostTube (X := X) (μ := μ) (y := y) (k := k) (b := b)
      (n := n) (σ := σ) (h := h) (a := 3 / 2) (A := 5 / 2) (B := 3) (ρ := 1 / 10 ^ 15) (z := z)
      (ω := ω)
    simpa only [hSdef, hUdef, hVdef] using this
  /- measurability -/
  have hEm : MeasurableSet[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k b⌋₊ + 1)] E := by
    have hz₁ := measurable_primeAlgebra_windowZ (X := X) (μ := μ) y k (le_refl b) σ h₁
    have hz₂ := measurable_primeAlgebra_windowZ (X := X) (μ := μ) y k (le_refl b) σ h₂
    refine (((measurableSet_primeAlgebra_hp1Tube y k hdb σ h₁).inter
      (measurableSet_primeAlgebra_hp1Tube y k hdb σ h₂)).inter ?_).inter ?_
    · exact (measurableSet_le measurable_const hz₁).inter (measurableSet_le hz₁ measurable_const)
    · exact (measurableSet_le measurable_const hz₂).inter (measurableSet_le hz₂ measurable_const)
  have hprem : Measurable[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k b⌋₊ + 1)] pre :=
    (measurable_primeAlgebra_normSq _ _ _).mul (measurable_primeAlgebra_normSq _ _ _)
  have hΦm : Measurable[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k b⌋₊ + 1)] Φ :=
    (hprem.indicator hEm).prodMk
      ((measurable_primeAlgebra_windowZ (X := X) (μ := μ) y k (le_refl b) σ h₁).prodMk
        (measurable_primeAlgebra_windowZ (X := X) (μ := μ) y k (le_refl b) σ h₂))
  have hwalk : ∀ h : ℝ, Measurable[primeAlgebra X (⌊blockScale k b⌋₊ + 1)
      (⌊blockScale k r⌋₊ + 1)] fun ω (j : ℕ) =>
        walk (halfBlock X ((k : ℝ) + b) σ h) (min j n) ω := by
    intro h
    refine @measurable_pi_lambda Ω ℕ (fun _ => ℝ)
      (primeAlgebra X (⌊blockScale k b⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)) _ _ fun j => ?_
    have h' := measurable_primeAlgebra_walk_post (X := X) k b n σ h (min_le_right j n)
    rwa [hbn] at h'
  have hΨm : Measurable[primeAlgebra X (⌊blockScale k b⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)] Ψ :=
    (hwalk h₁).prodMk ((hwalk h₂).prodMk
      ((measurable_primeAlgebra_normSq _ _ _).mul (measurable_primeAlgebra_normSq _ _ _)))
  have hind : IndepFun Φ Ψ μ := indepFun_of_primeAlgebra hX hΦm hΨm
  have hΦ : Measurable Φ := hΦm.mono (primeAlgebra_le hX _ _) le_rfl
  have hΨ : Measurable Ψ := hΨm.mono (primeAlgebra_le hX _ _) le_rfl
  have hSm : ∀ h, MeasurableSet (S h) := fun h => measurableSet_shiftedPath n (U h) (V h)
  have hFm : Measurable F := by
    have e₁ : Measurable fun q : (ℝ × (ℝ × ℝ)) × ((ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) =>
        (S h₁).indicator (1 : ℝ × (ℕ → ℝ) → ℝ≥0∞) (q.1.2.1, q.2.1) :=
      (measurable_const.indicator (hSm h₁)).comp
        ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
          (measurable_fst.comp measurable_snd))
    have e₂ : Measurable fun q : (ℝ × (ℝ × ℝ)) × ((ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) =>
        (S h₂).indicator (1 : ℝ × (ℕ → ℝ) → ℝ≥0∞) (q.1.2.2, q.2.2.1) :=
      (measurable_const.indicator (hSm h₂)).comp
        ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
          (measurable_fst.comp (measurable_snd.comp measurable_snd)))
    exact (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_fst)).mul
      (e₁.mul (e₂.mul (ENNReal.measurable_ofReal.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))))
  /- the pointwise bound -/
  have hpt : ∀ ω, ENNReal.ofReal ((hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂).indicator
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2) ω)
      ≤ F (Φ ω, Ψ ω) := by
    intro ω
    by_cases hω : ω ∈ hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂
    · rw [Set.indicator_of_mem hω]
      obtain ⟨hω₁, hω₂⟩ := hω
      have hr₁ := windowZ_mem_of_mem_hp2Tube_of_le (a := 3 / 2) (A := 5 / 2) (B := 3)
        (ρ := 1 / 10 ^ 15) (by omega : 1 ≤ b) hbr hω₁
      have hr₂ := windowZ_mem_of_mem_hp2Tube_of_le (a := 3 / 2) (A := 5 / 2) (B := 3)
        (ρ := 1 / 10 ^ 15) (by omega : 1 ≤ b) hbr hω₂
      have hωE : ω ∈ E := ⟨⟨⟨hp1Tube_subset_hp2Tube hdr y k σ h₁ hω₁,
        hp1Tube_subset_hp2Tube hdr y k σ h₂ hω₂⟩, hr₁⟩, hr₂⟩
      have hp₁ : (windowZ X μ y k σ h₁ b ω,
          fun j => walk (halfBlock X ((k : ℝ) + b) σ h₁) (min j n) ω) ∈ S h₁ :=
        (hSmem h₁ _ ω).2 (mem_hp2PostTube_of_mem_hp1Tube (by omega) hω₁)
      have hp₂ : (windowZ X μ y k σ h₂ b ω,
          fun j => walk (halfBlock X ((k : ℝ) + b) σ h₂) (min j n) ω) ∈ S h₂ :=
        (hSmem h₂ _ ω).2 (mem_hp2PostTube_of_mem_hp1Tube (by omega) hω₂)
      simp only [hFdef, hΦdef, hΨdef]
      rw [Set.indicator_of_mem hp₁, Set.indicator_of_mem hp₂, Set.indicator_of_mem hωE]
      simp only [Pi.one_apply, one_mul]
      rw [← ENNReal.ofReal_mul (by simp only [hpredef]; positivity)]
      refine le_of_eq (congrArg ENNReal.ofReal ?_)
      simp only [hpredef, hpostdef]
      rw [normSq_randomEulerProductIco_split hc0b hcbr (shiftLine σ h₁) ω,
        normSq_randomEulerProductIco_split hc0b hcbr (shiftLine σ h₂) ω]
      ring
    · rw [Set.indicator_of_notMem hω, ENNReal.ofReal_zero]
      exact zero_le
  /- the freeze, and the fibre by the two-fold tilt identity and the post bound -/
  have hfreeze := lintegral_eq_lintegral_lintegral_of_indepFun hΦ hΨ hind hFm
  have hfib : ∀ ω, ∫⁻ ω', F (Φ ω, Ψ ω') ∂μ
      ≤ ENNReal.ofReal (∫ ω, post ω ∂μ)
        * ENNReal.ofReal ((hp1Tube X μ y k d σ h₁ ∩ hp1Tube X μ y k d σ h₂).indicator
            (fun ω => pre ω * (Cpost * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₁ b ω) 0
                  + ch)
                * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₂ b ω) 0 + ch)
                / ((r - b : ℕ) : ℝ))) ω) := by
    intro ω
    set P₁ := hp2PostTube X μ y k b n σ h₁ (3 / 2) (5 / 2) 3 (1 / 10 ^ 15)
      (windowZ X μ y k σ h₁ b ω) with hP₁def
    set P₂ := hp2PostTube X μ y k b n σ h₂ (3 / 2) (5 / 2) 3 (1 / 10 ^ 15)
      (windowZ X μ y k σ h₂ b ω) with hP₂def
    have hPm : MeasurableSet[primeAlgebra X (⌊blockScale k b⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)]
        (P₁ ∩ P₂) := by
      have e₁ := measurableSet_primeAlgebra_hp2PostTube (X := X) (μ := μ) y k b n σ h₁ (3 / 2)
        (5 / 2) 3 (1 / 10 ^ 15) (windowZ X μ y k σ h₁ b ω)
      have e₂ := measurableSet_primeAlgebra_hp2PostTube (X := X) (μ := μ) y k b n σ h₂ (3 / 2)
        (5 / 2) 3 (1 / 10 ^ 15) (windowZ X μ y k σ h₂ b ω)
      rw [hbn] at e₁ e₂
      exact e₁.inter e₂
    have hFeq : ∀ ω', F (Φ ω, Ψ ω') = ENNReal.ofReal (E.indicator pre ω)
        * (ENNReal.ofReal (post ω') * (P₁ ∩ P₂).indicator 1 ω') := by
      intro ω'
      simp only [hFdef, hΦdef, hΨdef]
      by_cases e₁ : ω' ∈ P₁
      · by_cases e₂ : ω' ∈ P₂
        · rw [Set.indicator_of_mem ((hSmem _ _ _).2 e₁),
            Set.indicator_of_mem ((hSmem _ _ _).2 e₂),
            Set.indicator_of_mem (Set.mem_inter e₁ e₂)]
          simp only [Pi.one_apply, one_mul, mul_one]
        · rw [Set.indicator_of_notMem (fun hc => e₂ ((hSmem _ _ _).1 hc)),
            Set.indicator_of_notMem (fun hc => e₂ hc.2 : ω' ∉ P₁ ∩ P₂)]
          simp only [zero_mul, mul_zero]
      · rw [Set.indicator_of_notMem (fun hc => e₁ ((hSmem _ _ _).1 hc)),
          Set.indicator_of_notMem (fun hc => e₁ hc.1 : ω' ∉ P₁ ∩ P₂)]
        simp only [zero_mul, mul_zero]
    rw [lintegral_congr hFeq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    simp only [hpostdef]
    rw [lintegral_pair_mul_eq_tiltedMeasure₂ hX hcbr hyr hs₁ hs₂ (g := (P₁ ∩ P₂).indicator 1)
        (measurable_const.indicator hPm),
      lintegral_indicator_one (measurableSet_of_primeAlgebra hX hPm)]
    by_cases hωE : ω ∈ E
    · have hωE' := hωE
      obtain ⟨⟨⟨hq₁, hq₂⟩, hr₁⟩, hr₂⟩ := hωE'
      have hb := hpost _ _ hr₁ hr₂
      rw [Set.indicator_of_mem hωE, Set.indicator_of_mem (Set.mem_inter hq₁ hq₂)]
      have hle : (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h₁)
          (shiftLine σ h₂) μ) (P₁ ∩ P₂)
          ≤ ENNReal.ofReal (Cpost * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₁ b ω) 0 + ch)
            * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₂ b ω) 0 + ch)
            / ((r - b : ℕ) : ℝ)) := by
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal hb
      have hpre0 : 0 ≤ pre ω := by simp only [hpredef]; positivity
      calc _ ≤ ENNReal.ofReal (pre ω) * (ENNReal.ofReal (∫ ω,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (⌊blockScale k b⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (⌊blockScale k b⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
            * ENNReal.ofReal (Cpost
              * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₁ b ω) 0 + ch)
              * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₂ b ω) 0 + ch)
              / ((r - b : ℕ) : ℝ))) := by gcongr
        _ = _ := by rw [ENNReal.ofReal_mul hpre0]; ring
    · rw [Set.indicator_of_notMem hωE, ENNReal.ofReal_zero, zero_mul]
      exact zero_le
  calc _ ≤ ∫⁻ ω, F (Φ ω, Ψ ω) ∂μ := lintegral_mono hpt
    _ = ∫⁻ ω, ∫⁻ ω', F (Φ ω, Ψ ω') ∂μ ∂μ := hfreeze
    _ ≤ _ := lintegral_mono hfib
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end PostStep

/-! ### The bridge

For a shallow depth the post start is past the decorrelation point, `b = hp2PostStart d > d`, and
the tubes on the bridge blocks `d ≤ m < b` are dropped.  The post factor at the walk's start `Z_b`
is at most the one at `Z_d` plus the bridge increment `|ΔZ|`, and under the two-fold tilt
`E[(α₁ + |ΔZ₁|)(α₂ + |ΔZ₂|)] ≤ (α₁ + x)(α₂ + x)` once `E ΔZᵢ² ≤ x²`. -/

section Bridge

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The bridge increment** `ΔZ = Z_b - Z_d` of the centred walk at `h` over the blocks
`d ≤ m < b`: the walk at offset `k + d` over `b - d` blocks minus its one-point tilted means. -/
noncomputable def bridgeZ (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k : ℕ) (σ h : ℝ) (d b : ℕ)
    (ω : Ω) : ℝ :=
  walk (halfBlock X ((k : ℝ) + d) σ h) (b - d) ω
    - ∑ i ∈ Finset.range (b - d), windowMeanH X μ y k σ h (i + d)

/-- `Z_b = Z_d + ΔZ`. -/
lemma windowZ_eq_add_bridgeZ {y k d b : ℕ} {σ h : ℝ} (hdb : d ≤ b) (ω : Ω) :
    windowZ X μ y k σ h b ω = windowZ X μ y k σ h d ω + bridgeZ X μ y k σ h d b ω := by
  have hw := walk_halfBlock_add X k d σ h (b - d) ω
  rw [show d + (b - d) = b by omega] at hw
  have hs : ∑ i ∈ Finset.range b, windowMeanH X μ y k σ h i
      = ∑ i ∈ Finset.range d, windowMeanH X μ y k σ h i
        + ∑ i ∈ Finset.range (b - d), windowMeanH X μ y k σ h (i + d) := by
    rw [show b = d + (b - d) by omega, Finset.sum_range_add, show d + (b - d) - d = b - d by omega]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [add_comm d i])
  simp only [windowZ, bridgeZ]
  rw [hw, hs]
  ring

/-- The bridge increment is a function of the values in `[c_d, c_b)`. -/
lemma measurable_primeAlgebra_bridgeZ (y k : ℕ) {d b : ℕ} (hdb : d ≤ b) (σ h : ℝ) :
    Measurable[primeAlgebra X (⌊blockScale k d⌋₊ + 1) (⌊blockScale k b⌋₊ + 1)]
      (bridgeZ X μ y k σ h d b) := by
  have hw := measurable_primeAlgebra_walk_post (X := X) k d (b - d) σ h (le_refl (b - d))
  rw [show d + (b - d) = b by omega] at hw
  exact hw.sub_const _

/-- The post factor after the bridge: `max(a - (z + δ), 0) ≤ max(a - z, 0) + |δ|`. -/
lemma max_sub_add_le_add_abs (a z δ : ℝ) : max (a - (z + δ)) 0 ≤ max (a - z) 0 + |δ| := by
  have h1 := le_max_left (a - z) 0
  have h2 := le_max_right (a - z) 0
  have h3 := neg_abs_le δ
  exact max_le (by linarith) (by positivity)

/-- **Cauchy–Schwarz for the bridge**: on a probability space, for `X₁, X₂ ∈ L²` with
`E Xᵢ² ≤ x²`, `x ≥ 0`, and `α₁, α₂ ≥ 0`, `E[(α₁ + |X₁|)(α₂ + |X₂|)] ≤ (α₁ + x)(α₂ + x)`
(`E|Xᵢ| ≤ x` by Jensen, `|X₁X₂| ≤ (X₁² + X₂²)/2`). -/
lemma integral_add_abs_mul_add_abs_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X₁ X₂ : Ω → ℝ} (h₁ : MemLp X₁ 2 P) (h₂ : MemLp X₂ 2 P)
    {α₁ α₂ x : ℝ} (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) (hx : 0 ≤ x)
    (hm₁ : ∫ ω, X₁ ω ^ 2 ∂P ≤ x ^ 2) (hm₂ : ∫ ω, X₂ ω ^ 2 ∂P ≤ x ^ 2) :
    ∫ ω, (α₁ + |X₁ ω|) * (α₂ + |X₂ ω|) ∂P ≤ (α₁ + x) * (α₂ + x) := by
  have hi₁ : Integrable (fun ω => |X₁ ω|) P := (h₁.integrable one_le_two).abs
  have hi₂ : Integrable (fun ω => |X₂ ω|) P := (h₂.integrable one_le_two).abs
  have hs₁ : Integrable (fun ω => X₁ ω ^ 2) P := h₁.integrable_sq
  have hs₂ : Integrable (fun ω => X₂ ω ^ 2) P := h₂.integrable_sq
  have hpt : ∀ ω, |X₁ ω| * |X₂ ω| ≤ (X₁ ω ^ 2 + X₂ ω ^ 2) / 2 := fun ω => by
    have := two_mul_le_add_sq |X₁ ω| |X₂ ω|
    rw [sq_abs, sq_abs] at this
    linarith
  have hi₁₂ : Integrable (fun ω => |X₁ ω| * |X₂ ω|) P := by
    refine ((hs₁.add hs₂).div_const 2).mono' (hi₁.1.mul hi₂.1) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt ω
  have hJ : ∀ {Y : Ω → ℝ}, MemLp Y 2 P → ∫ ω, Y ω ^ 2 ∂P ≤ x ^ 2 → ∫ ω, |Y ω| ∂P ≤ x := by
    intro Y hY hm
    have hsq : (∫ ω, |Y ω| ∂P) ^ 2 ≤ ∫ ω, |Y ω| * |Y ω| ∂P :=
      sq_integral_le_integral_mul_self (X := fun ω => |Y ω|) hY.abs
    have heq : ∫ ω, |Y ω| * |Y ω| ∂P = ∫ ω, Y ω ^ 2 ∂P :=
      integral_congr_ae (ae_of_all _ fun ω => by
        change |Y ω| * |Y ω| = Y ω ^ 2
        rw [← sq, sq_abs])
    rw [heq] at hsq
    have h0 : 0 ≤ ∫ ω, |Y ω| ∂P := integral_nonneg fun ω => abs_nonneg _
    nlinarith
  have e₁ := hJ h₁ hm₁
  have e₂ := hJ h₂ hm₂
  have e₁₂ : ∫ ω, |X₁ ω| * |X₂ ω| ∂P ≤ x ^ 2 := by
    have hint : Integrable (fun ω => (X₁ ω ^ 2 + X₂ ω ^ 2) / 2) P := (hs₁.add hs₂).div_const 2
    have hval : ∫ ω, (X₁ ω ^ 2 + X₂ ω ^ 2) / 2 ∂P
        = ((∫ ω, X₁ ω ^ 2 ∂P) + ∫ ω, X₂ ω ^ 2 ∂P) / 2 := by
      have h := integral_add hs₁ hs₂
      rw [integral_div]
      exact congrArg (· / 2) h
    have := integral_mono hi₁₂ hint hpt
    linarith
  have hexp : ∫ ω, (α₁ + |X₁ ω|) * (α₂ + |X₂ ω|) ∂P
      = α₁ * α₂ + α₁ * ∫ ω, |X₂ ω| ∂P + α₂ * ∫ ω, |X₁ ω| ∂P + ∫ ω, |X₁ ω| * |X₂ ω| ∂P := by
    have hpt' : ∀ ω, (α₁ + |X₁ ω|) * (α₂ + |X₂ ω|)
        = α₁ * α₂ + α₁ * |X₂ ω| + α₂ * |X₁ ω| + |X₁ ω| * |X₂ ω| := fun ω => by ring
    have i2 : Integrable (fun ω => α₁ * α₂ + α₁ * |X₂ ω|) P :=
      (integrable_const _).add (hi₂.const_mul _)
    have i1 : Integrable (fun ω => α₁ * α₂ + α₁ * |X₂ ω| + α₂ * |X₁ ω|) P :=
      i2.add (hi₁.const_mul _)
    have a1 : ∫ ω, α₁ * α₂ + α₁ * |X₂ ω| + α₂ * |X₁ ω| + |X₁ ω| * |X₂ ω| ∂P
        = ∫ ω, α₁ * α₂ + α₁ * |X₂ ω| + α₂ * |X₁ ω| ∂P + ∫ ω, |X₁ ω| * |X₂ ω| ∂P :=
      integral_add i1 hi₁₂
    have a2 : ∫ ω, α₁ * α₂ + α₁ * |X₂ ω| + α₂ * |X₁ ω| ∂P
        = ∫ ω, α₁ * α₂ + α₁ * |X₂ ω| ∂P + ∫ ω, α₂ * |X₁ ω| ∂P :=
      integral_add i2 (hi₁.const_mul _)
    have a3 : ∫ ω, α₁ * α₂ + α₁ * |X₂ ω| ∂P = ∫ ω, α₁ * α₂ ∂P + ∫ ω, α₁ * |X₂ ω| ∂P :=
      integral_add (integrable_const _) (hi₂.const_mul _)
    rw [integral_congr_ae (ae_of_all _ hpt'), a1, a2, a3, integral_const, integral_const_mul,
      integral_const_mul]
    simp
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_left e₂ hα₁, mul_le_mul_of_nonneg_left e₁ hα₂]

omit [MeasurableSpace Ω] in
/-- The walk from block `d` as one sum over the primes of its blocks. -/
lemma walk_halfBlock_eq_sum_biUnion (k d j : ℕ) (σ h : ℝ) (ω : Ω) :
    walk (halfBlock X ((k : ℝ) + d) σ h) j ω
      = ∑ p ∈ (Finset.range j).biUnion (fun i => primeBlockSub ((k : ℝ) + d) i),
          localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (X (p : ℕ) ω) := by
  classical
  have hdisj : (↑(Finset.range j) : Set ℕ).PairwiseDisjoint
      (fun i => primeBlockSub ((k : ℝ) + d) i) := fun a _ b _ hab =>
    pairwise_disjoint_primeBlockSub _ hab
  rw [walk_apply, Finset.sum_biUnion hdisj]
  rfl

/-- **The bridge increment's second moment under the two-fold tilt**, in the two-fold closed forms:
`E₂'[ΔZ²] = ∑_{d≤m<b} V_m(h) + (∑_{d≤m<b} (M₂_m(h) - μ̃_m(h)))²`, `V = RMF.pairVarH`,
`M₂ = RMF.pairMeanH`, `μ̃ = RMF.windowMeanH` (the primes are independent under the tilt,
`ProbabilityTheory.IndepFun.variance_sum`). -/
theorem integral_bridgeZ_sq_eq (hX : IsRademacherPrimeValues X μ) {y k d b : ℕ}
    {σ h₁ h₂ h : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hy : ∀ i, i < b - d → primeBlockSub k (i + d) ⊆ primesBelowSub y) :
    MemLp (bridgeZ X μ y k σ h d b) 2
        (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h₁)
          (shiftLine σ h₂) μ)
      ∧ ∫ ω, bridgeZ X μ y k σ h d b ω ^ 2
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h₁)
            (shiftLine σ h₂) μ)
        = ∑ i ∈ Finset.range (b - d), pairVarH X μ y k σ h₁ h₂ h (i + d)
          + (∑ i ∈ Finset.range (b - d),
              (pairMeanH X μ y k σ h₁ h₂ h (i + d) - windowMeanH X μ y k σ h (i + d))) ^ 2 := by
  classical
  have hs₁ : 0 < (shiftLine σ h₁).re := by rw [re_shiftLine]; linarith
  have hs₂ : 0 < (shiftLine σ h₂).re := by rw [re_shiftLine]; linarith
  haveI hP := isProbabilityMeasure_tiltedMeasure₂_rademacher hX y hs₁ hs₂
  set P := tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h₁)
    (shiftLine σ h₂) μ with hPdef
  set T := (Finset.range (b - d)).biUnion (fun i => primeBlockSub ((k : ℝ) + d) i) with hTdef
  set ξ : Nat.Primes → Ω → ℝ := fun p ω =>
    localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (X (p : ℕ) ω) with hξdef
  have hdisj : (↑(Finset.range (b - d)) : Set ℕ).PairwiseDisjoint
      (fun i => primeBlockSub ((k : ℝ) + d) i) := fun a _ b _ hab =>
    pairwise_disjoint_primeBlockSub _ hab
  have hblk : ∀ i : ℕ, primeBlockSub ((k : ℝ) + d) i = primeBlockSub k (i + d) := fun i =>
    (primeBlockSub_add (k : ℝ) i d).symm
  have hw : ∀ i, i < b - d → ∀ p ∈ primeBlockSub k (i + d),
      ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h))‖ ≤ 1 / 5 := by
    intro i _ p hp
    have hk' : (20 : ℝ) ≤ ((i + d : ℕ) : ℝ) + k := by
      have : (20 : ℝ) ≤ k := by exact_mod_cast hk
      linarith [Nat.cast_nonneg (α := ℝ) (i + d)]
    exact (norm_cpow_le_of_mem_primeBlockSub hσ hk' (re_shiftLine σ h) hp).trans (by norm_num)
  have hmem : ∀ p ∈ T, p ∈ primesBelowSub y ∧ ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h))‖ ≤ 1 / 5 := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.1 hp
    rw [hblk i] at hpi
    exact ⟨hy i (Finset.mem_range.1 hi) hpi, hw i (Finset.mem_range.1 hi) p hpi⟩
  have hML : ∀ p ∈ T, MemLp (ξ p) 2 P := fun p hp =>
    memLp_two_localLogAdd_tiltedMeasure₂ hX y hs₁ hs₂ (hmem p hp).1 (hmem p hp).2
  -- the bridge increment as a sum over the bridge primes minus a constant
  set c : ℝ := ∑ i ∈ Finset.range (b - d), windowMeanH X μ y k σ h (i + d) with hcdef
  have hZ : bridgeZ X μ y k σ h d b = fun ω => (∑ p ∈ T, ξ p ω) - c := by
    funext ω
    rw [bridgeZ, walk_halfBlock_eq_sum_biUnion]
  have hSML : MemLp (fun ω => ∑ p ∈ T, ξ p ω) 2 P := memLp_finsetSum T hML
  refine ⟨by rw [hZ]; exact hSML.sub (memLp_const c), ?_⟩
  -- the variance of the sum, prime by prime
  have hindep := iIndepFun_localLogAdd_tiltedMeasure₂_rademacher
    (w := fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) hX y hs₁ hs₂
  have hvar : variance (fun ω => ∑ p ∈ T, ξ p ω) P = ∑ p ∈ T, variance (ξ p) P := by
    have h := IndepFun.variance_sum hML (fun a _ b _ hab => hindep.indepFun hab)
    have hfe : (∑ p ∈ T, ξ p) = fun ω => ∑ p ∈ T, ξ p ω := by
      funext ω
      simp
    rwa [hfe] at h
  have hvarp : ∀ p ∈ T, variance (ξ p) P
      = (∫ ω, ξ p ω * ξ p ω ∂P) - (∫ ω, ξ p ω ∂P) ^ 2 := by
    intro p hp
    rw [variance_eq_sub (hML p hp)]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun ω => by simp [Pi.pow_apply, sq])
  have hmean : ∫ ω, ∑ p ∈ T, ξ p ω ∂P = ∑ p ∈ T, ∫ ω, ξ p ω ∂P :=
    integral_finsetSum T fun p hp => (hML p hp).integrable one_le_two
  -- the blocks' closed forms
  have hV : ∑ p ∈ T, ((∫ ω, ξ p ω * ξ p ω ∂P) - (∫ ω, ξ p ω ∂P) ^ 2)
      = ∑ i ∈ Finset.range (b - d), pairVarH X μ y k σ h₁ h₂ h (i + d) := by
    rw [Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [pairVarH, coe_blockMatchedVarAdd₂ hX y hs₁ hs₂ (hy i (Finset.mem_range.1 hi))
      (hw i (Finset.mem_range.1 hi)), hblk i]
  have hM : ∑ p ∈ T, ∫ ω, ξ p ω ∂P
      = ∑ i ∈ Finset.range (b - d), pairMeanH X μ y k σ h₁ h₂ h (i + d) := by
    rw [Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pairMeanH, blockMeanAdd₂, hblk i]
  -- `E(S - c)² = Var(S - c) + (E(S - c))²`
  have hsq := variance_eq_sub (hSML.sub (memLp_const c))
  have hvsc : variance ((fun ω => ∑ p ∈ T, ξ p ω) - fun _ => c) P
      = variance (fun ω => ∑ p ∈ T, ξ p ω) P := variance_sub_const hSML.1 c
  rw [hvsc] at hsq
  have hint : ∫ ω, (((fun ω => ∑ p ∈ T, ξ p ω) - fun _ => c : Ω → ℝ)) ω ∂P
      = (∫ ω, ∑ p ∈ T, ξ p ω ∂P) - c := by
    simp only [Pi.sub_apply]
    rw [integral_sub (hSML.integrable one_le_two) (integrable_const c), integral_const]
    simp
  have hsq2 : ∫ ω, (((fun ω => ∑ p ∈ T, ξ p ω) - fun _ => c : Ω → ℝ) ^ 2) ω ∂P
      = ∫ ω, bridgeZ X μ y k σ h d b ω ^ 2 ∂P := by
    rw [hZ]
    rfl
  rw [hint, hsq2, hvar, Finset.sum_congr rfl hvarp, hV, hmean, hM] at hsq
  have hsplit : ∑ i ∈ Finset.range (b - d),
      (pairMeanH X μ y k σ h₁ h₂ h (i + d) - windowMeanH X μ y k σ h (i + d))
      = ∑ i ∈ Finset.range (b - d), pairMeanH X μ y k σ h₁ h₂ h (i + d) - c := by
    rw [Finset.sum_sub_distrib]
  rw [hsplit]
  linarith

/-- The integrand of `RMF.integral_add_abs_mul_add_abs_le` is integrable. -/
lemma integrable_add_abs_mul_add_abs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X₁ X₂ : Ω → ℝ} (h₁ : MemLp X₁ 2 P) (h₂ : MemLp X₂ 2 P) (α₁ α₂ : ℝ) :
    Integrable (fun ω => (α₁ + |X₁ ω|) * (α₂ + |X₂ ω|)) P := by
  have hi₁ : Integrable (fun ω => |X₁ ω|) P := (h₁.integrable one_le_two).abs
  have hi₂ : Integrable (fun ω => |X₂ ω|) P := (h₂.integrable one_le_two).abs
  have hs : Integrable (fun ω => (X₁ ω ^ 2 + X₂ ω ^ 2) / 2) P :=
    (h₁.integrable_sq.add h₂.integrable_sq).div_const 2
  have hi₁₂ : Integrable (fun ω => |X₁ ω| * |X₂ ω|) P := by
    refine hs.mono' (hi₁.1.mul hi₂.1) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := two_mul_le_add_sq |X₁ ω| |X₂ ω|
    rw [sq_abs, sq_abs] at this
    linarith
  have heq : (fun ω => (α₁ + |X₁ ω|) * (α₂ + |X₂ ω|))
      = fun ω => α₁ * α₂ + α₁ * |X₂ ω| + α₂ * |X₁ ω| + |X₁ ω| * |X₂ ω| := by
    funext ω
    ring
  rw [heq]
  exact (((integrable_const _).add (hi₂.const_mul _)).add (hi₁.const_mul _)).add hi₁₂

/-- The bridge's pointwise step: the post factor at `Z_b = Z_d + ΔZ` is at most the one at `Z_d`
plus `|ΔZ|`, and both are nonnegative. -/
lemma bridge_factor_le {a zd δ ch : ℝ} (hch : 0 ≤ ch) :
    0 ≤ max (a - (zd + δ)) 0 + ch ∧ max (a - (zd + δ)) 0 + ch ≤ max (a - zd) 0 + ch + |δ| := by
  have h1 := max_sub_add_le_add_abs a zd δ
  have h2 := le_max_right (a - (zd + δ)) 0
  constructor <;> linarith

/-- The product of the bridged post factors, scaled by `C/N ≥ 0`. -/
lemma bridge_product_le {u₁ u₂ v₁ v₂ C N : ℝ} (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (h₁ : u₁ ≤ v₁)
    (h₂ : u₂ ≤ v₂) (hC : 0 ≤ C) (hN : 0 ≤ N) : C * u₁ * u₂ / N ≤ C * v₁ * v₂ / N := by
  have h := mul_le_mul h₁ h₂ hu₂ (hu₁.trans h₁)
  have h' := mul_le_mul_of_nonneg_left h hC
  rw [mul_assoc, mul_assoc]
  exact div_le_div_of_nonneg_right h' hN

/-- **The bridge, conditioned on the prefix.**  With the tubes on the bridge blocks `d ≤ m < b`
dropped, the prefix-and-bridge weight against the post factors at `Z_b` is at most the bridge's
pair moment times the prefix weight against the post factors at `Z_d` shifted by `x`:
`E[1_{pre}W_{[0,b)}·C(A₁(Z_b) + ch)(A₂(Z_b) + ch)/N]
  ≤ E W_{[d,b)}·E[1_{pre}W_{[0,d)}·C(A₁(Z_d) + ch + x)(A₂(Z_d) + ch + x)/N]`
once `E₂'[ΔZᵢ²] ≤ x²` under the two-fold tilt at the cutoff `y ≥ c_b`
(`RMF.integral_add_abs_mul_add_abs_le`). -/
theorem lintegral_pre_le_bridge (hX : IsRademacherPrimeValues X μ) {k d b y : ℕ} {σ h₁ h₂ : ℝ}
    (hk : 20 ≤ k) (hσ : 0 ≤ σ) (hdb : d ≤ b) (hyb : ⌊blockScale k b⌋₊ + 1 ≤ y)
    {C N ch x : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N) (hch : 0 ≤ ch) (hx : 0 ≤ x)
    (hx₁ : ∫ ω, bridgeZ X μ y k σ h₁ d b ω ^ 2
      ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h₁)
        (shiftLine σ h₂) μ) ≤ x ^ 2)
    (hx₂ : ∫ ω, bridgeZ X μ y k σ h₂ d b ω ^ 2
      ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h₁)
        (shiftLine σ h₂) μ) ≤ x ^ 2) :
    ∫⁻ ω, ENNReal.ofReal ((hp1Tube X μ y k d σ h₁ ∩ hp1Tube X μ y k d σ h₂).indicator
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k b⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k b⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2
          * (C * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₁ b ω) 0 + ch)
            * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₂ b ω) 0 + ch) / N)) ω) ∂μ
      ≤ ENNReal.ofReal (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k d⌋₊ + 1) (⌊blockScale k b⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k d⌋₊ + 1) (⌊blockScale k b⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * ∫⁻ ω, ENNReal.ofReal ((hp1Tube X μ y k d σ h₁ ∩ hp1Tube X μ y k d σ h₂).indicator
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2
              * (C * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₁ d ω) 0 + ch + x)
                * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₂ d ω) 0 + ch + x) / N))
            ω) ∂μ := by
  classical
  haveI := hX.isProbabilityMeasure
  have hs₁ : 0 < (shiftLine σ h₁).re := by rw [re_shiftLine]; linarith
  have hs₂ : 0 < (shiftLine σ h₂).re := by rw [re_shiftLine]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure₂_rademacher hX y hs₁ hs₂
  have hc0d : ⌊blockScale k 0⌋₊ + 1 ≤ ⌊blockScale k d⌋₊ + 1 := cut_mono k (Nat.zero_le _)
  have hcdb : ⌊blockScale k d⌋₊ + 1 ≤ ⌊blockScale k b⌋₊ + 1 := cut_mono k hdb
  have hyb' : ∀ i, i < b - d → primeBlockSub k (i + d) ⊆ primesBelowSub y := fun i hi =>
    primeBlockSub_subset_primesBelowSub_of_le (n := b - 1) (by omega)
      (le_trans (by rw [blockCutoff, show b - 1 + 1 = b by omega]) hyb)
  obtain ⟨hL₁, -⟩ := integral_bridgeZ_sq_eq (h₁ := h₁) (h₂ := h₂) (h := h₁) hX hk hσ hyb'
  obtain ⟨hL₂, -⟩ := integral_bridgeZ_sq_eq (h₁ := h₁) (h₂ := h₂) (h := h₂) hX hk hσ hyb'
  /- the objects -/
  set Pre : Set Ω := hp1Tube X μ y k d σ h₁ ∩ hp1Tube X μ y k d σ h₂ with hPredef
  set pre : Ω → ℝ := fun ω =>
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 with hpredef
  set br : Ω → ℝ := fun ω =>
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (⌊blockScale k d⌋₊ + 1) (⌊blockScale k b⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (⌊blockScale k d⌋₊ + 1) (⌊blockScale k b⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 with hbrdef
  set α : ℝ → Ω → ℝ := fun h ω =>
    max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h d ω) 0 + ch with hαdef
  set Φ : Ω → ℝ × (ℝ × ℝ) := fun ω => (Pre.indicator pre ω, (α h₁ ω, α h₂ ω)) with hΦdef
  set Ψ : Ω → ℝ × (ℝ × ℝ) := fun ω =>
    (bridgeZ X μ y k σ h₁ d b ω, (bridgeZ X μ y k σ h₂ d b ω, br ω)) with hΨdef
  set F : (ℝ × (ℝ × ℝ)) × (ℝ × (ℝ × ℝ)) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (q.1.1 * q.2.2.2 * (C * (q.1.2.1 + |q.2.1|) * (q.1.2.2 + |q.2.2.1|) / N))
    with hFdef
  /- measurability -/
  have hPrem : MeasurableSet[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1)]
      Pre := (measurableSet_primeAlgebra_hp1Tube y k le_rfl σ h₁).inter
        (measurableSet_primeAlgebra_hp1Tube y k le_rfl σ h₂)
  have hαm : ∀ h, Measurable[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1)]
      (α h) := fun h =>
    ((measurable_const.sub (measurable_primeAlgebra_windowZ (X := X) (μ := μ) y k le_rfl σ
      h)).max measurable_const).add_const _
  have hΦm : Measurable[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1)] Φ :=
    (((measurable_primeAlgebra_normSq _ _ _).mul (measurable_primeAlgebra_normSq _ _ _)).indicator
      hPrem).prodMk ((hαm h₁).prodMk (hαm h₂))
  have hΨm : Measurable[primeAlgebra X (⌊blockScale k d⌋₊ + 1) (⌊blockScale k b⌋₊ + 1)] Ψ :=
    (measurable_primeAlgebra_bridgeZ y k hdb σ h₁).prodMk
      ((measurable_primeAlgebra_bridgeZ y k hdb σ h₂).prodMk
        ((measurable_primeAlgebra_normSq _ _ _).mul (measurable_primeAlgebra_normSq _ _ _)))
  have hind : IndepFun Φ Ψ μ := indepFun_of_primeAlgebra hX hΦm hΨm
  have hΦ : Measurable Φ := hΦm.mono (primeAlgebra_le hX _ _) le_rfl
  have hΨ : Measurable Ψ := hΨm.mono (primeAlgebra_le hX _ _) le_rfl
  have hFm : Measurable F := by
    refine ENNReal.measurable_ofReal.comp ?_
    fun_prop
  /- the pointwise bound -/
  have hpt : ∀ ω, ENNReal.ofReal (Pre.indicator (fun ω =>
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k b⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k b⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2
          * (C * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₁ b ω) 0 + ch)
            * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₂ b ω) 0 + ch) / N)) ω)
      ≤ F (Φ ω, Ψ ω) := by
    intro ω
    by_cases hω : ω ∈ Pre
    · rw [Set.indicator_of_mem hω]
      simp only [hFdef, hΦdef, hΨdef, Set.indicator_of_mem hω]
      refine ENNReal.ofReal_le_ofReal ?_
      have hsplit : ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k b⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k b⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2
          = pre ω * br ω := by
        simp only [hpredef, hbrdef]
        rw [normSq_randomEulerProductIco_split hc0d hcdb (shiftLine σ h₁) ω,
          normSq_randomEulerProductIco_split hc0d hcdb (shiftLine σ h₂) ω]
        ring
      rw [hsplit]
      have hpb : 0 ≤ pre ω * br ω := by simp only [hpredef, hbrdef]; positivity
      refine mul_le_mul_of_nonneg_left ?_ hpb
      obtain ⟨f₁, g₁⟩ := bridge_factor_le (a := 3 / 2 + 1 / 10 ^ 15)
        (zd := windowZ X μ y k σ h₁ d ω) (δ := bridgeZ X μ y k σ h₁ d b ω) hch
      obtain ⟨f₂, g₂⟩ := bridge_factor_le (a := 3 / 2 + 1 / 10 ^ 15)
        (zd := windowZ X μ y k σ h₂ d ω) (δ := bridgeZ X μ y k σ h₂ d b ω) hch
      rw [windowZ_eq_add_bridgeZ hdb ω, windowZ_eq_add_bridgeZ (h := h₂) hdb ω]
      exact bridge_product_le f₁ f₂ g₁ g₂ hC hN
    · rw [Set.indicator_of_notMem hω, ENNReal.ofReal_zero]
      exact zero_le
  /- the freeze, and the fibre by the two-fold tilt identity and Cauchy–Schwarz -/
  have hfreeze := lintegral_eq_lintegral_lintegral_of_indepFun hΦ hΨ hind hFm
  have hfib : ∀ ω, ∫⁻ ω', F (Φ ω, Ψ ω') ∂μ
      ≤ ENNReal.ofReal (∫ ω, br ω ∂μ) * ENNReal.ofReal (Pre.indicator (fun ω =>
          pre ω * (C * (α h₁ ω + x) * (α h₂ ω + x) / N)) ω) := by
    intro ω
    have hg0 : 0 ≤ Pre.indicator pre ω :=
      Set.indicator_nonneg (fun ω _ => by simp only [hpredef]; positivity) ω
    have hα₁ : 0 ≤ α h₁ ω := by simp only [hαdef]; positivity
    have hα₂ : 0 ≤ α h₂ ω := by simp only [hαdef]; positivity
    set K : Ω → ℝ := fun ω' => C * (α h₁ ω + |bridgeZ X μ y k σ h₁ d b ω'|)
      * (α h₂ ω + |bridgeZ X μ y k σ h₂ d b ω'|) / N with hKdef
    have hK0 : ∀ ω', 0 ≤ K ω' := fun ω' => by simp only [hKdef]; positivity
    have hFeq : ∀ ω', F (Φ ω, Ψ ω') = ENNReal.ofReal (Pre.indicator pre ω)
        * (ENNReal.ofReal (br ω') * ENNReal.ofReal (K ω')) := by
      intro ω'
      simp only [hFdef, hΦdef, hΨdef, hKdef]
      rw [← ENNReal.ofReal_mul (by simp only [hbrdef]; positivity), ← ENNReal.ofReal_mul hg0]
      ring_nf
    have hKm : Measurable[primeAlgebra X (⌊blockScale k d⌋₊ + 1) (⌊blockScale k b⌋₊ + 1)]
        fun ω' => ENNReal.ofReal (K ω') := by
      refine ENNReal.measurable_ofReal.comp ?_
      simp only [hKdef]
      exact (((measurable_const.mul (measurable_const.add (continuous_abs.measurable.comp
        (measurable_primeAlgebra_bridgeZ y k hdb σ h₁)))).mul (measurable_const.add
        (continuous_abs.measurable.comp
          (measurable_primeAlgebra_bridgeZ y k hdb σ h₂))))).div_const _
    rw [lintegral_congr hFeq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    simp only [hbrdef]
    rw [lintegral_pair_mul_eq_tiltedMeasure₂ hX hcdb hyb hs₁ hs₂ hKm]
    have hKint : Integrable K (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y
        (shiftLine σ h₁) (shiftLine σ h₂) μ) := by
      simp only [hKdef]
      have := (integrable_add_abs_mul_add_abs hL₁ hL₂ (α h₁ ω) (α h₂ ω)).const_mul C
      simpa only [mul_assoc] using this.div_const N
    rw [← ofReal_integral_eq_lintegral_ofReal hKint (ae_of_all _ hK0)]
    have hCS := integral_add_abs_mul_add_abs_le hL₁ hL₂ hα₁ hα₂ hx hx₁ hx₂
    have hKle : ∫ ω', K ω' ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y
        (shiftLine σ h₁) (shiftLine σ h₂) μ) ≤ C * (α h₁ ω + x) * (α h₂ ω + x) / N := by
      simp only [hKdef]
      rw [integral_div, show (fun ω' => C * (α h₁ ω + |bridgeZ X μ y k σ h₁ d b ω'|)
          * (α h₂ ω + |bridgeZ X μ y k σ h₂ d b ω'|))
          = fun ω' => C * ((α h₁ ω + |bridgeZ X μ y k σ h₁ d b ω'|)
            * (α h₂ ω + |bridgeZ X μ y k σ h₂ d b ω'|)) by funext ω'; ring,
        integral_const_mul]
      refine div_le_div_of_nonneg_right ?_ hN
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hCS hC
    by_cases hω : ω ∈ Pre
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      have hpre0 : 0 ≤ pre ω := by simp only [hpredef]; positivity
      calc ENNReal.ofReal (pre ω) * (ENNReal.ofReal (∫ ω, br ω ∂μ)
            * ENNReal.ofReal (∫ ω', K ω' ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p =>
              X p ω) y (shiftLine σ h₁) (shiftLine σ h₂) μ)))
          ≤ ENNReal.ofReal (pre ω) * (ENNReal.ofReal (∫ ω, br ω ∂μ)
            * ENNReal.ofReal (C * (α h₁ ω + x) * (α h₂ ω + x) / N)) := by
            gcongr
        _ = _ := by rw [ENNReal.ofReal_mul hpre0]; ring
    · rw [Set.indicator_of_notMem hω, ENNReal.ofReal_zero, zero_mul]
      exact zero_le
  calc _ ≤ ∫⁻ ω, F (Φ ω, Ψ ω) ∂μ := lintegral_mono hpt
    _ = ∫⁻ ω, ∫⁻ ω', F (Φ ω, Ψ ω') ∂μ ∂μ := hfreeze
    _ ≤ _ := lintegral_mono hfib
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end Bridge

/-! ### The prefix: AM–GM on the products, then one walk under its own tilt

`‖F₁^{pre}‖²(A₁ + c₁)·‖F₂^{pre}‖²(A₂ + c₂) ≤ ½(‖F₁^{pre}‖⁴(A₁ + c₁)² + ‖F₂^{pre}‖⁴(A₂ + c₂)²)`, the
other walk's tube dropped in each term.  Each term is the one-point tilt identity
`E[1_{pre}‖F^{pre}‖⁴G] = E‖F^{pre}‖²·E'[1_{pre}‖F^{pre}‖²G]` with
`‖F^{pre}(s_h)‖² = e^{2(Z_d + Mean_d)}`, the prefix bound `RMF.hp2PrefixBound` and the mass
factor. -/

section Prefix

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The blocks below `M` lie below any cutoff past `c_M`. -/
lemma primeBlockSub_subset_of_cut_le {k M y : ℕ} (h : ⌊blockScale k M⌋₊ + 1 ≤ y) :
    ∀ m, m < M → primeBlockSub k m ⊆ primesBelowSub y := fun m hm =>
  primeBlockSub_subset_primesBelowSub_of_le (n := m) le_rfl
    (le_trans (by rw [blockCutoff]; exact cut_mono k (by omega)) h)

/-- **The prefix's second moment in closed form**:
`E‖F_{[c₀,c_d)}(s_h)‖² = ∏_{m<d}∏_{p∈B_m}(1 + p^{-1-2σ})`. -/
lemma integral_normSq_blocks_eq_prod (hX : IsRademacherPrimeValues X μ) (k d : ℕ) (σ h : ℝ) :
    ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2 ∂μ
      = ∏ m ∈ Finset.range d, ∏ p ∈ primeBlockSub k m, (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) := by
  classical
  rw [hX.isRademacherRMF.integral_norm_randomEulerProductIco_sq,
    ← Finset.prod_biUnion (fun a _ b _ hab => pairwise_disjoint_primeBlockSub (k : ℝ) hab),
    biUnion_primeBlockSub_eq_sdiff, primesBelowSub_sdiff]
  have hsub : ∏ p ∈ primesIcoSub (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1),
      (1 + ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h))‖ ^ 2)
      = ∏ q ∈ primesIco (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1),
        (1 + ‖(q : ℂ) ^ (-(shiftLine σ h))‖ ^ 2) :=
    Finset.prod_subtype_of_mem (fun q : ℕ => 1 + ‖(q : ℂ) ^ (-(shiftLine σ h))‖ ^ 2)
      fun _ hq => prime_of_mem_primesIco hq
  rw [← hsub]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [norm_sq_prime_cpow_neg p (re_shiftLine σ h)]

/-- `‖F^{pre}(s_h)‖² = e^{2Z_d}e^{2Mean_d}` wherever the values on the prefix are at most `1`. -/
lemma normSq_prefix_eq_exp {y k d : ℕ} {σ h : ℝ} (hσ : 0 ≤ σ) {ω : Ω}
    (hω : ∀ p ∈ primesIco (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1), ‖X p ω‖ ≤ 1) :
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2
      = Real.exp (2 * windowZ X μ y k σ h d ω)
        * Real.exp (2 * ∑ i ∈ Finset.range d, windowMeanH X μ y k σ h i) := by
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  rw [normSq_randomEulerProductIco_sqfree_eq_exp (k : ℝ) (Nat.zero_le d) hs hω, ← Real.exp_add]
  congr 1
  simp only [windowZ, walk_apply, halfBlock, Finset.range_eq_Ico]
  ring

/-- **One walk's prefix term.**  For `k ≥ 20`, `h ∈ halfWindow k`, `σe^{k+d} ≤ 1/200`, the cutoff
`y ≥ c_d` and `c ≥ 1.05`:
`E[1_{H_d(k,h)}(‖F^{pre}(s_h)‖²(A + c))²] ≤ (E‖F^{pre}(s_h)‖²)²·e^{∑_{m<d}(S_m + C_m(2h)) + 5·10⁻²⁰}
  ·hp2PrefixBound d c`, `A = max(3/2 + 10⁻¹⁵ - Z_d, 0)`, `H_d` HP1's tube over the first `d`
blocks. -/
theorem lintegral_hp1Tube_prefix_sq_le (hX : IsRademacherPrimeValues X μ) {k d y : ℕ} {σ h : ℝ}
    (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσd : σ * Real.exp ((k : ℝ) + d) ≤ 1 / 200) (hyd : ⌊blockScale k d⌋₊ + 1 ≤ y) {c : ℝ}
    (hc : 1.05 ≤ c) :
    ∫⁻ ω, ENNReal.ofReal ((hp1Tube X μ y k d σ h).indicator (fun ω =>
        (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2
          * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h d ω) 0 + c)) ^ 2) ω) ∂μ
      ≤ ENNReal.ofReal ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2 ∂μ) ^ 2
          * Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)
            + 5 / 10 ^ 20) * hp2PrefixBound d c) := by
  classical
  haveI := hX.isProbabilityMeasure
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure_rademacher hX y hs
  have hc0d : ⌊blockScale k 0⌋₊ + 1 ≤ ⌊blockScale k d⌋₊ + 1 := cut_mono k (Nat.zero_le _)
  have hy := primeBlockSub_subset_of_cut_le hyd
  set Pre : Set Ω := hp1Tube X μ y k d σ h with hPredef
  set sq : Ω → ℝ := fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
    (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2 with hsqdef
  set A : Ω → ℝ := fun ω => max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h d ω) 0 + c with hAdef
  set Mean : ℝ := ∑ i ∈ Finset.range d, windowMeanH X μ y k σ h i with hMeandef
  set P := tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ
    with hPdef
  have hsq0 : ∀ ω, 0 ≤ sq ω := fun ω => by simp only [hsqdef]; positivity
  have hPrem : MeasurableSet[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1)]
      Pre := measurableSet_primeAlgebra_hp1Tube y k le_rfl σ h
  have hsqm : Measurable[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1)] sq :=
    measurable_primeAlgebra_normSq _ _ _
  have hAm : Measurable[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1)] A :=
    ((measurable_const.sub (measurable_primeAlgebra_windowZ (X := X) (μ := μ) y k le_rfl σ
      h)).max measurable_const).add_const _
  -- split one `‖F^{pre}‖²` off, and tilt
  have hpt : ∀ ω, ENNReal.ofReal (Pre.indicator (fun ω => (sq ω * A ω) ^ 2) ω)
      = ENNReal.ofReal (sq ω) * ENNReal.ofReal (Pre.indicator (fun ω => sq ω * A ω ^ 2) ω) := by
    intro ω
    by_cases hω : ω ∈ Pre
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, ← ENNReal.ofReal_mul (hsq0 ω)]
      ring_nf
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, ENNReal.ofReal_zero, mul_zero]
  have hgm : Measurable[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1)]
      fun ω => ENNReal.ofReal (Pre.indicator (fun ω => sq ω * A ω ^ 2) ω) :=
    ENNReal.measurable_ofReal.comp ((hsqm.mul (hAm.pow_const 2)).indicator hPrem)
  rw [lintegral_congr hpt]
  have htilt : ∫⁻ ω, ENNReal.ofReal (sq ω)
        * ENNReal.ofReal (Pre.indicator (fun ω => sq ω * A ω ^ 2) ω) ∂μ
      = ENNReal.ofReal (∫ ω, sq ω ∂μ)
        * ∫⁻ ω, ENNReal.ofReal (Pre.indicator (fun ω => sq ω * A ω ^ 2) ω) ∂P :=
    lintegral_normSq_mul_eq_tiltedMeasure hX hc0d hyd hs hgm
  rw [htilt]
  -- the exponential identity under the tilt
  set W : Ω → ℝ := fun ω => Pre.indicator (fun ω => Real.exp (2 * windowZ X μ y k σ h d ω)
    * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h d ω) 0 + c) ^ 2) ω with hWdef
  have hae : ∀ᵐ ω ∂P, ENNReal.ofReal (Pre.indicator (fun ω => sq ω * A ω ^ 2) ω)
      = ENNReal.ofReal (Real.exp (2 * Mean)) * ENNReal.ofReal (W ω) := by
    have hμ := ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw
      (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1)
    filter_upwards [(tiltedMeasure_absolutelyContinuous _ y (shiftLine σ h) μ).ae_le hμ]
      with ω hω
    simp only [hWdef]
    by_cases hmem : ω ∈ Pre
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      simp only [hsqdef, hAdef]
      rw [normSq_prefix_eq_exp (μ := μ) (y := y) hσ hω]
      ring
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, ENNReal.ofReal_zero,
        mul_zero]
  have hint : Integrable W P :=
    integrable_indicator_hp2Tube_exp_mul_sq hX (P := P) (y := y) (k := k) (M := d)
      (σ := σ) (h := h) (a := 3 / 2) (A := 5 / 2) (B := 3) (ρ := 1 / 10 ^ 15)
      (b := 3 / 2 + 1 / 10 ^ 15) (by norm_num) le_rfl (by linarith : (0 : ℝ) ≤ c)
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => by
    simp only [hWdef]
    exact Set.indicator_nonneg (fun ω _ => by positivity) ω
  have hbound : ∫ ω, W ω ∂P ≤ hp2PrefixBound d c :=
    integral_hp1Tube_exp_mul_sq_le_hp2PrefixBound hX (r := d) (M := d) (y := y)
      (b := 3 / 2 + 1 / 10 ^ 15) hk hh hσ hσd hy le_rfl hc le_rfl
  have hlW : ∫⁻ ω, ENNReal.ofReal (Pre.indicator (fun ω => sq ω * A ω ^ 2) ω) ∂P
      = ENNReal.ofReal (Real.exp (2 * Mean) * ∫ ω, W ω ∂P) := by
    rw [lintegral_congr_ae hae, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hW0),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [hlW]
  -- the mass factor
  have hmass := exp_two_mul_sum_windowMeanH_div_prod_le hX (M := d) (y := y) (h := h) hk hσ hy
  rw [← integral_normSq_blocks_eq_prod hX k d σ h] at hmass
  have hE1 : 1 ≤ ∫ ω, sq ω ∂μ := one_le_integral_normSq_Ico hX _ _ _
  have hmean : Real.exp (2 * Mean) ≤ (∫ ω, sq ω ∂μ)
      * Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)
        + 5 / 10 ^ 20) := by
    rw [div_le_iff₀ (by linarith)] at hmass
    simpa only [hsqdef, hMeandef, mul_comm] using hmass
  have hE0 : 0 ≤ ∫ ω, sq ω ∂μ := by linarith
  have hPB0 : 0 ≤ ∫ ω, W ω ∂P := integral_nonneg hW0
  rw [← ENNReal.ofReal_mul hE0]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (∫ ω, sq ω ∂μ) * (Real.exp (2 * Mean) * ∫ ω, W ω ∂P)
      ≤ (∫ ω, sq ω ∂μ) * (((∫ ω, sq ω ∂μ)
          * Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)
            + 5 / 10 ^ 20)) * hp2PrefixBound d c) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hmean hbound hPB0 (by positivity)) hE0
    _ = _ := by simp only [hsqdef]; ring

omit [MeasurableSpace Ω] in
/-- AM–GM on the products at one point: `1_{T₁∩T₂}xy ≤ ½(1_{T₁}x² + 1_{T₂}y²)`. -/
lemma indicator_inter_mul_le {T₁ T₂ : Set Ω} {x y : Ω → ℝ} (ω : Ω) :
    (T₁ ∩ T₂).indicator (fun ω => x ω * y ω) ω
      ≤ 1 / 2 * T₁.indicator (fun ω => x ω ^ 2) ω + 1 / 2 * T₂.indicator (fun ω => y ω ^ 2) ω := by
  have h2 := two_mul_le_add_sq (x ω) (y ω)
  by_cases h₁ : ω ∈ T₁
  · by_cases h₂ : ω ∈ T₂
    · rw [Set.indicator_of_mem (Set.mem_inter h₁ h₂), Set.indicator_of_mem h₁,
        Set.indicator_of_mem h₂]
      linarith
    · rw [Set.indicator_of_notMem (fun h => h₂ h.2), Set.indicator_of_mem h₁,
        Set.indicator_of_notMem h₂]
      nlinarith [sq_nonneg (x ω)]
  · rw [Set.indicator_of_notMem (fun h => h₁ h.1), Set.indicator_of_notMem h₁]
    by_cases h₂ : ω ∈ T₂
    · rw [Set.indicator_of_mem h₂]
      nlinarith [sq_nonneg (y ω)]
    · rw [Set.indicator_of_notMem h₂]
      norm_num

/-- **The pair's prefix term, by AM–GM on the products**: for `c₁, c₂ ≥ 1.05`,
`E[1_{H_d(k,h₁)∩H_d(k,h₂)}W_{[0,d)}(A₁ + c₁)(A₂ + c₂)]
  ≤ E‖F^{pre}(s₁)‖²E‖F^{pre}(s₂)‖²·½∑ᵢ e^{μᵢ}·hp2PrefixBound d cᵢ`,
`μᵢ = ∑_{m<d}(S_m + C_m(2hᵢ)) + 5·10⁻²⁰`: the other walk's tube is dropped in each term, which is
then `RMF.lintegral_hp1Tube_prefix_sq_le` (the two moments `E‖F^{pre}(sᵢ)‖²` are equal). -/
theorem lintegral_hp1Tube_pair_le_prefix (hX : IsRademacherPrimeValues X μ) {k d y : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσd : σ * Real.exp ((k : ℝ) + d) ≤ 1 / 200)
    (hyd : ⌊blockScale k d⌋₊ + 1 ≤ y) {c₁ c₂ : ℝ} (hc₁ : 1.05 ≤ c₁) (hc₂ : 1.05 ≤ c₂) :
    ∫⁻ ω, ENNReal.ofReal ((hp1Tube X μ y k d σ h₁ ∩ hp1Tube X μ y k d σ h₂).indicator
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2
          * ((max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₁ d ω) 0 + c₁)
            * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₂ d ω) 0 + c₂))) ω) ∂μ
      ≤ ENNReal.ofReal ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
          * ((Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m)
                + 5 / 10 ^ 20) * hp2PrefixBound d c₁
            + Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m)
                + 5 / 10 ^ 20) * hp2PrefixBound d c₂) / 2)) := by
  classical
  set sq : ℝ → Ω → ℝ := fun h ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p =>
    X p ω) (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2 with hsqdef
  set a : ℝ → ℝ → Ω → ℝ := fun h c ω =>
    max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h d ω) 0 + c with hadef
  set T : ℝ → ℝ → Ω → ℝ := fun h c ω =>
    (hp1Tube X μ y k d σ h).indicator (fun ω => (sq h ω * a h c ω) ^ 2) ω with hTdef
  have hT0 : ∀ h c ω, 0 ≤ T h c ω := fun h c ω => by
    simp only [hTdef]
    exact Set.indicator_nonneg (fun ω _ => by positivity) ω
  have hTm : ∀ h c, Measurable (T h c) := by
    intro h c
    have hsqm := ((measurable_primeAlgebra_normSq (X := X) (⌊blockScale k 0⌋₊ + 1)
      (⌊blockScale k d⌋₊ + 1) (shiftLine σ h)).mono (primeAlgebra_le hX _ _) le_rfl)
    have ham : Measurable (a h c) :=
      ((measurable_const.sub (measurable_windowZ hX y k σ h d)).max measurable_const).add_const _
    exact ((hsqm.mul ham).pow_const 2).indicator
      (measurableSet_of_primeAlgebra hX (measurableSet_primeAlgebra_hp1Tube y k le_rfl σ h))
  -- AM–GM
  have hpt : ∀ ω, ENNReal.ofReal ((hp1Tube X μ y k d σ h₁ ∩ hp1Tube X μ y k d σ h₂).indicator
      (fun ω => sq h₁ ω * sq h₂ ω * (a h₁ c₁ ω * a h₂ c₂ ω)) ω)
      ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal (T h₁ c₁ ω)
        + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (T h₂ c₂ ω) := by
    intro ω
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by have := hT0 h₁ c₁ ω; positivity)
        (by have := hT0 h₂ c₂ ω; positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := indicator_inter_mul_le (T₁ := hp1Tube X μ y k d σ h₁)
      (T₂ := hp1Tube X μ y k d σ h₂) (x := fun ω => sq h₁ ω * a h₁ c₁ ω)
      (y := fun ω => sq h₂ ω * a h₂ c₂ ω) ω
    have e : ∀ ω, sq h₁ ω * sq h₂ ω * (a h₁ c₁ ω * a h₂ c₂ ω)
        = sq h₁ ω * a h₁ c₁ ω * (sq h₂ ω * a h₂ c₂ ω) := fun ω => by ring
    simp only [e]
    exact h
  have hterm : ∀ h c, h ∈ halfWindow k → 1.05 ≤ c → ∫⁻ ω, ENNReal.ofReal (T h c ω) ∂μ
      ≤ ENNReal.ofReal ((∫ ω, sq h ω ∂μ) ^ 2
          * Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)
            + 5 / 10 ^ 20) * hp2PrefixBound d c) := fun h c hh hc =>
    lintegral_hp1Tube_prefix_sq_le hX hk hh hσ hσd hyd hc
  have hEq : ∫ ω, sq h₁ ω ∂μ = ∫ ω, sq h₂ ω ∂μ := by
    simp only [hsqdef]
    rw [integral_normSq_blocks_eq_prod hX k d σ h₁, integral_normSq_blocks_eq_prod hX k d σ h₂]
  have hE0 : 0 ≤ ∫ ω, sq h₂ ω ∂μ := integral_nonneg fun ω => by simp only [hsqdef]; positivity
  calc _ ≤ ∫⁻ ω, (ENNReal.ofReal (1 / 2) * ENNReal.ofReal (T h₁ c₁ ω)
          + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (T h₂ c₂ ω)) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (1 / 2) * ∫⁻ ω, ENNReal.ofReal (T h₁ c₁ ω) ∂μ
        + ENNReal.ofReal (1 / 2) * ∫⁻ ω, ENNReal.ofReal (T h₂ c₂ ω) ∂μ := by
      have hm₁ : Measurable fun ω => ENNReal.ofReal (1 / 2) * ENNReal.ofReal (T h₁ c₁ ω) :=
        (ENNReal.measurable_ofReal.comp (hTm h₁ c₁)).const_mul _
      rw [lintegral_add_left hm₁,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal ((∫ ω, sq h₁ ω ∂μ) ^ 2
          * Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m)
            + 5 / 10 ^ 20) * hp2PrefixBound d c₁)
        + ENNReal.ofReal (1 / 2) * ENNReal.ofReal ((∫ ω, sq h₂ ω ∂μ) ^ 2
          * Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m)
            + 5 / 10 ^ 20) * hp2PrefixBound d c₂) := by
      gcongr
      · exact hterm h₁ c₁ hh₁ hc₁
      · exact hterm h₂ c₂ hh₂ hc₂
    _ = _ := by
      have hPB : ∀ c : ℝ, 0 ≤ c → 0 ≤ hp2PrefixBound d c := fun c hc => by
        unfold hp2PrefixBound hp2SlabBound
        have := hp2SlabPrefactor_nonneg hc
        split_ifs <;> exact le_min (by positivity) (by positivity)
      have hP₁ := hPB c₁ (by linarith)
      have hP₂ := hPB c₂ (by linarith)
      rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity), hEq]
      congr 1
      ring

end Prefix

/-! ### For the pair bound -/

/-- `hp2PrefixBound d c ≥ 0` for `c ≥ 0`. -/
lemma hp2PrefixBound_nonneg (d : ℕ) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ hp2PrefixBound d c := by
  unfold hp2PrefixBound hp2SlabBound
  have := hp2SlabPrefactor_nonneg hc
  split_ifs <;> exact le_min (by positivity) (by positivity)

/-- The assembly's algebra: the post and bridge moments against their one-point masses, the
constant `C/N` and the prefix term. -/
lemma pair_assembly_le {Ep Eb E₁d E₂d E₁r E₂r C N Q Q' EM : ℝ} (hEp : 0 ≤ Ep) (hEb : 0 ≤ Eb)
    (h₁d : 0 ≤ E₁d) (h₂d : 0 ≤ E₂d) (hC : 0 ≤ C) (hN : 0 ≤ N) (hQ0 : 0 ≤ Q)
    (hM : Eb * Ep ≤ E₁r * E₂r * Real.exp EM) (hQ : Q ≤ Q') :
    Ep * (Eb * (C / N * (E₁d * E₂d * Q)))
      ≤ E₁d * E₁r * (E₂d * E₂r) * (C * Real.exp EM * Q') / N := by
  have hCN : 0 ≤ C / N := div_nonneg hC hN
  have hX0 : 0 ≤ C / N * (E₁d * E₂d * Q) := by positivity
  have h1 : Ep * (Eb * (C / N * (E₁d * E₂d * Q))) = (Eb * Ep) * (C / N * (E₁d * E₂d * Q)) := by
    ring
  have h2 : (Eb * Ep) * (C / N * (E₁d * E₂d * Q))
      ≤ (E₁r * E₂r * Real.exp EM) * (C / N * (E₁d * E₂d * Q')) := by
    refine mul_le_mul hM ?_ hX0 (le_trans (mul_nonneg hEb hEp) hM)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ (mul_nonneg h₁d h₂d)) hCN
  have h3 : (E₁r * E₂r * Real.exp EM) * (C / N * (E₁d * E₂d * Q'))
      = E₁d * E₁r * (E₂d * E₂r) * (C * Real.exp EM * Q') / N := by
    rw [mul_div_assoc]
    ring
  rw [h1]
  exact h2.trans (le_of_eq h3)

/-! ### The hypotheses discharged: the post bound, the bridge

The post bound `RMF.IsHP2PostBound` at a cell's numerals, with the push `P` as a parameter
(`RMF.isHP2PostBound_of_numerals`), and the bridge's second moment from cosine-sum bounds
(`RMF.bridge_moment_le_of_cos`). -/

section Discharge

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The post bound at a cell's numerals** (`RMF.hp2Post_bound_of_numerals_floor`, with the push
`P` and the constants as parameters): `Cpost = C₀/√(β₁β₂)`, `ch` the shift, for the post start
`b = hp2PostStart d = d + s`. -/
theorem isHP2PostBound_of_numerals (hX : IsRademacherPrimeValues X μ) {k d s r y n₀ : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y)
    (hbs : hp2PostStart d = d + s)
    (hd1 : Real.exp (-1) ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + d))
    (hd2 : |h₁ - h₂| * Real.exp ((k : ℝ) + d) ≤ 1)
    (hcase : 4 ≤ hp2PostStart d ∨ (2 ≤ hp2PostStart d
      ∧ Real.exp 1 ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + hp2PostStart d)))
    (hn₀ : 3 ≤ n₀) (hr : hp2PostStart d + n₀ ≤ r)
    {VL vmax Dmax Smax DT ST PD κ Kt Vd P c sq β₁ β₂ Kn C₀ ch : ℝ}
    (hVL : ∀ m, hp2PostStart d ≤ m → VL ≤ varLoTier m)
    (hvmax : ∀ m, hp2PostStart d ≤ m → varHiTier m ≤ vmax)
    (hDmax : ∀ i, s ≤ i → diffTier i ≤ Dmax)
    (hSmax : ∀ m, hp2PostStart d ≤ m → sumTier m ≤ Smax)
    (hDT : ∀ n, ∑ j ∈ Finset.range n, diffTier (s + j) ≤ DT)
    (hST : ∀ n, ∑ j ∈ Finset.range n, sumTier (hp2PostStart d + j) ≤ ST)
    (hPD : ∀ n j, hp2PostStart d + n ≤ r → j ≤ n →
      -∑ i ∈ Finset.range j, blockCosSum k σ (h₁ - h₂) (i + hp2PostStart d) ≤ PD)
    (hVL0 : 0 < VL) (hκ : (Dmax + Smax) / 2 + 7.5 / 10 ^ 8 ≤ κ)
    (hKt : (DT + ST) / 2 + 3.3 / 10 ^ 6 ≤ Kt)
    (hVd : Real.exp (1 - hp2PostStart d) / 2 + 1.6 / 10 ^ 6 ≤ Vd)
    (hP : PD + Real.exp (1 - hp2PostStart d) + 3.2 / 10 ^ 6 ≤ P) (hc0 : 0 < c)
    (hc : π * vmax / 2 ≤ c ^ 2) (hsq0 : 0 ≤ sq) (hsq : vmax ≤ sq ^ 2) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hβ₁' : β₁ ≤ 0.495 - (Vd + vmax) / n₀)
    (hβ₂' : β₂ ≤ 0.495 - (Vd + κ * (Kt / VL)) / n₀)
    (hKn : 1 + Kt / VL * (sq + vmax / (c + P)) / (c + P) ≤ Kn) (hC₀ : 0.636621 * Kn ≤ C₀)
    (hch : c + 1 / 10 ^ 4 + P ≤ ch) :
    IsHP2PostBound X μ y k d r σ h₁ h₂ (C₀ / √(β₁ * β₂)) ch :=
  fun _ _ hz₁ hz₂ => hp2Post_bound_of_numerals_floor hX hk hh₁ hh₂ hσ hσr
    (primeBlockSub_subset_of_cut_le hyr) hbs (two_le_hp2PostStart d) hd1 hd2 hcase hn₀ hr
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hz₁ hz₂ hVL hvmax
    hDmax hSmax hDT hST hPD hVL0 hκ hKt hVd hP hc0 hc hsq0 hsq hβ₁ hβ₂ hβ₁' hβ₂' hKn hC₀ hch

/-- **The bridge's two-fold data in the cosine sums**, one block `m` (`m + k ≥ 20`) and one walk
`h ∈ {h₁, h₂}`: `V_m(h) ≤ (S_m + C_m(2h))/2 + e^{-m}/10²⁰` and
`|M₂_m(h) - μ̃_m(h) - (C_m(h₁-h₂) + C_m(h₁+h₂))| ≤ 2e^{-m}/10²⁰`
(`RMF.abs_blockMatchedVarAdd₂_sub_le_decay`, `RMF.abs_blockMeanAdd₂_fst_sub_le_decay`,
`RMF.abs_blockMeanAdd_height_sub_le_decay`). -/
lemma bridge_block_data (hX : IsRademacherPrimeValues X μ) {y k m : ℕ} {σ h₁ h₂ h : ℝ}
    (hk : 20 ≤ k) (hσ : 0 ≤ σ) (hh : h = h₁ ∨ h = h₂)
    (hB : primeBlockSub k m ⊆ primesBelowSub y) :
    pairVarH X μ y k σ h₁ h₂ h m
        ≤ (blockRpowSum k σ m + blockCosSum k σ (2 * h) m) / 2 + Real.exp (-(m : ℝ)) / 10 ^ 20
      ∧ |pairMeanH X μ y k σ h₁ h₂ h m - windowMeanH X μ y k σ h m
          - (blockCosSum k σ (h₁ - h₂) m + blockCosSum k σ (h₁ + h₂) m)|
        ≤ 2 * (Real.exp (-(m : ℝ)) / 10 ^ 20) := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : (20 : ℝ) ≤ (m : ℝ) + k := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hV := abs_le.1 (abs_blockMatchedVarAdd₂_sub_le_decay hX y (θ := k) (h₁ := h₁) (h₂ := h₂)
    (h := h) hσ (by positivity) hm hB)
  have hW := abs_le.1 (abs_blockMeanAdd_height_sub_le_decay hX y (θ := k) (h := h) hσ
    (by positivity) hm hB)
  refine ⟨by unfold pairVarH; linarith [hV.2], ?_⟩
  rcases hh with rfl | rfl
  · have hP := abs_le.1 (abs_blockMeanAdd₂_fst_sub_le_decay hX y (θ := k) (σ := σ) (h₁ := h)
      (h₂ := h₂) (m := m) hσ (by positivity) hm hB)
    unfold pairMeanH windowMeanH
    rw [abs_le]
    constructor <;> linarith [hP.1, hP.2, hW.1, hW.2]
  · have hP := abs_le.1 (abs_blockMeanAdd₂_snd_sub_le_decay hX y (θ := k) (σ := σ) (h₁ := h₁)
      (h₂ := h) (m := m) hσ (by positivity) hm hB)
    unfold pairMeanH windowMeanH
    rw [abs_le]
    constructor <;> linarith [hP.1, hP.2, hW.1, hW.2]

/-- **The bridge's second moment from cosine-sum bounds** (the form a cell discharges): for the
walk at `h ∈ {h₁, h₂}` over the bridge blocks `d ≤ m < b`, bounds
`∑(S_m + C_m(2h))/2 ≤ V` and `|∑(C_m(h₁-h₂) + C_m(h₁+h₂))| ≤ M` give
`∑V_m(h) + (∑(M₂_m(h) - μ̃_m(h)))² ≤ V + 1.6·10⁻²⁰ + (M + 3.2·10⁻²⁰)²`. -/
theorem bridge_moment_le_of_cos (hX : IsRademacherPrimeValues X μ) {y k d b : ℕ}
    {σ h₁ h₂ h : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ) (hh : h = h₁ ∨ h = h₂)
    (hy : ∀ i, i < b - d → primeBlockSub k (i + d) ⊆ primesBelowSub y) {V M : ℝ}
    (hV : ∑ i ∈ Finset.range (b - d),
      (blockRpowSum k σ (i + d) + blockCosSum k σ (2 * h) (i + d)) / 2 ≤ V)
    (hM : |∑ i ∈ Finset.range (b - d),
      (blockCosSum k σ (h₁ - h₂) (i + d) + blockCosSum k σ (h₁ + h₂) (i + d))| ≤ M) :
    ∑ i ∈ Finset.range (b - d), pairVarH X μ y k σ h₁ h₂ h (i + d)
        + (∑ i ∈ Finset.range (b - d),
          (pairMeanH X μ y k σ h₁ h₂ h (i + d) - windowMeanH X μ y k σ h (i + d))) ^ 2
      ≤ V + 1.6 / 10 ^ 20 + (M + 3.2 / 10 ^ 20) ^ 2 := by
  have hdat := fun i (hi : i ∈ Finset.range (b - d)) =>
    bridge_block_data (m := i + d) hX hk hσ hh (hy i (Finset.mem_range.1 hi))
  have hE := sum_exp_neg_add_le d (b - d)
  have hE' : ∑ i ∈ Finset.range (b - d), Real.exp (-((i + d : ℕ) : ℝ)) / 10 ^ 20
      ≤ 1.59 / 10 ^ 20 := by
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right hE (by positivity)
  have hVs : ∑ i ∈ Finset.range (b - d), pairVarH X μ y k σ h₁ h₂ h (i + d)
      ≤ V + 1.6 / 10 ^ 20 := by
    have h1 := Finset.sum_le_sum fun i hi => (hdat i hi).1
    rw [Finset.sum_add_distrib] at h1
    have h2 : (1.59 : ℝ) / 10 ^ 20 ≤ 1.6 / 10 ^ 20 := by norm_num
    linarith
  have hMs : |∑ i ∈ Finset.range (b - d),
      (pairMeanH X μ y k σ h₁ h₂ h (i + d) - windowMeanH X μ y k σ h (i + d))|
      ≤ M + 3.2 / 10 ^ 20 := by
    have h1 : |∑ i ∈ Finset.range (b - d),
        (pairMeanH X μ y k σ h₁ h₂ h (i + d) - windowMeanH X μ y k σ h (i + d)
          - (blockCosSum k σ (h₁ - h₂) (i + d) + blockCosSum k σ (h₁ + h₂) (i + d)))|
        ≤ 3.18 / 10 ^ 20 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i hi =>
        (hdat i hi).2).trans ?_)
      rw [← Finset.mul_sum]
      linarith
    rw [Finset.sum_sub_distrib] at h1
    have h2 := abs_sub_abs_le_abs_sub (∑ i ∈ Finset.range (b - d),
      (pairMeanH X μ y k σ h₁ h₂ h (i + d) - windowMeanH X μ y k σ h (i + d)))
      (∑ i ∈ Finset.range (b - d),
        (blockCosSum k σ (h₁ - h₂) (i + d) + blockCosSum k σ (h₁ + h₂) (i + d)))
    have h3 : (3.18 : ℝ) / 10 ^ 20 ≤ 3.2 / 10 ^ 20 := by norm_num
    linarith
  have hM0 : 0 ≤ M + 3.2 / 10 ^ 20 := le_trans (abs_nonneg _) hMs
  have hsq := sq_le_sq' (abs_le.1 hMs).1 (abs_le.1 hMs).2
  linarith

end Discharge

/-! ### The deep pairs -/

section Worst

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The deep pairs: the prefix alone** (`M = r`, no post).  For every pair of heights
`h₁, h₂ ∈ halfWindow k` (including `h₁ = h₂`) and `c ≥ 1.05`:
`E[1_{H(k,h₁)∩H(k,h₂)}‖F(s₁)‖²‖F(s₂)‖²]
  ≤ E‖F(s₁)‖²E‖F(s₂)‖²·½∑ᵢ e^{∑_{m<r}(S_m + C_m(2hᵢ)) + 5·10⁻²⁰}·hp2PrefixBound r c/c²`
(`(A₁ + c)(A₂ + c) ≥ c²`, then `RMF.lintegral_hp1Tube_pair_le_prefix` at `d = r`). -/
theorem integral_hp1Tube_inter_le_deep (hX : IsRademacherPrimeValues X μ) {k r y : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) {c : ℝ} (hc : 1.05 ≤ c) :
    ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * ((Real.exp (∑ m ∈ Finset.range r, (blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m)
              + 5 / 10 ^ 20)
            + Real.exp (∑ m ∈ Finset.range r, (blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m)
              + 5 / 10 ^ 20)) / 2)
        * hp2PrefixBound r c / c ^ 2 := by
  classical
  haveI := hX.isProbabilityMeasure
  have hc0 : 0 < c := by linarith
  set H : Set Ω := hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂ with hHdef
  set W : Ω → ℝ := fun ω =>
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 with hWdef
  set A : ℝ → Ω → ℝ := fun h ω => max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h r ω) 0 + c
    with hAdef
  have hstep := lintegral_hp1Tube_pair_le_prefix hX hk hh₁ hh₂ hσ hσr hyr hc hc
  have hpt : ∀ ω, ENNReal.ofReal (H.indicator W ω)
      ≤ ENNReal.ofReal (1 / c ^ 2) * ENNReal.ofReal (H.indicator (fun ω =>
          W ω * (A h₁ ω * A h₂ ω)) ω) := by
    intro ω
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hω : ω ∈ H
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      have hW0 : 0 ≤ W ω := by simp only [hWdef]; positivity
      have hA : c ^ 2 ≤ A h₁ ω * A h₂ ω := by
        simp only [hAdef]
        have := le_max_right (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₁ r ω) 0
        have := le_max_right (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₂ r ω) 0
        nlinarith
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      nlinarith
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, mul_zero]
  have hL : ∫⁻ ω, ENNReal.ofReal (H.indicator W ω) ∂μ
      ≤ ENNReal.ofReal (1 / c ^ 2 * ((∫ ω, ‖randomEulerProductIco (fun ω =>
          squarefreeExtension fun p => X p ω) (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)
            (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
          * ((Real.exp (∑ m ∈ Finset.range r, (blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m)
                + 5 / 10 ^ 20) * hp2PrefixBound r c
            + Real.exp (∑ m ∈ Finset.range r, (blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m)
                + 5 / 10 ^ 20) * hp2PrefixBound r c) / 2))) := by
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul_right hstep _
  have hH : MeasurableSet H :=
    (measurableSet_of_primeAlgebra hX (measurableSet_primeAlgebra_hp1Tube y k le_rfl σ h₁)).inter
      (measurableSet_of_primeAlgebra hX (measurableSet_primeAlgebra_hp1Tube y k le_rfl σ h₂))
  have hWm : Measurable W :=
    ((measurable_norm_randomEulerProductIco_sqfree hX _ _ _).pow_const 2).mul
      ((measurable_norm_randomEulerProductIco_sqfree hX _ _ _).pow_const 2)
  rw [← integral_indicator hH, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun ω => Set.indicator_nonneg (fun ω _ => by simp only [hWdef]; positivity) ω)
    (hWm.indicator hH).aestronglyMeasurable]
  have hPB := hp2PrefixBound_nonneg r (by linarith : (0 : ℝ) ≤ c)
  have h1 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ :=
    integral_nonneg fun ω => by positivity
  have h2 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ :=
    integral_nonneg fun ω => by positivity
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hL.trans (le_of_eq ?_))
  congr 1
  field_simp

end Worst

end RMF
