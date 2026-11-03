/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.CentralWindowAboveHalfExplicit
import RMF.Weighted.BandWindowsExplicit

/-!
# Proposition B′: the difference functional of a band, split

For the band product `F` over `[y₀, y₁)` and `Ψ = L⁻¹∫‖(F(½) - F(½+σ+it))/(σ+it)‖²dt`
(`RMF.bandDiffLine` at `L = 2π log z`), with `τ = e^{c-J}`, `T = e^{c-k₀}`:

`E[Ψ^q] ≤ (central)^q·E‖F(½)‖^{2q} + ((1+1/η)(2/τ)L⁻¹)^q·E‖F(½)‖^{2q}
  + (1+η)^q(2/L)^q·∑_{k₀≤k<J} E[W_k^q] + (1+η)^q(L⁻¹(2/T)M)^q`

(`RMF.integral_rpow_diffLine_le_split`): the central window `|t| ≤ τ` by Hölder
(`RMF.integral_rpow_centralWindow_diff_le`), the coherent part `‖F(½)‖²` off it, and the shifted
line off it split into the windows (`RMF.integral_rpow_mesoRange_band_le_sum_windows`) and the far
range by Jensen, `M` bounding the second moment on the line.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `‖a - b‖² ≤ (1 + 1/η)‖a‖² + (1 + η)‖b‖²` for `η > 0`. -/
lemma norm_sub_sq_le_split {η : ℝ} (hη : 0 < η) (a b : ℂ) :
    ‖a - b‖ ^ 2 ≤ (1 + 1 / η) * ‖a‖ ^ 2 + (1 + η) * ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 2 * ‖a‖ * ‖b‖ ≤ ‖a‖ ^ 2 / η + η * ‖b‖ ^ 2 := by
    rw [div_add' _ _ _ hη.ne', le_div_iff₀ hη]
    nlinarith [sq_nonneg (‖a‖ - η * ‖b‖)]
  have e : (1 + 1 / η) * ‖a‖ ^ 2 + (1 + η) * ‖b‖ ^ 2
      = ‖a‖ ^ 2 + ‖b‖ ^ 2 + (‖a‖ ^ 2 / η + η * ‖b‖ ^ 2) := by
    field_simp
    ring
  rw [e]
  nlinarith [h2, h3]

/-- `(a + b + c + d)^q ≤ a^q + b^q + c^q + d^q` for nonnegative reals and `0 ≤ q ≤ 1`. -/
lemma rpow_add_add_add_le {a b c d q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (a + b + c + d) ^ q ≤ a ^ q + b ^ q + c ^ q + d ^ q := by
  have h1 := Real.rpow_add_le_add_rpow (add_nonneg (add_nonneg ha hb) hc) hd hq0 hq1
  have h2 := Real.rpow_add_le_add_rpow (add_nonneg ha hb) hc hq0 hq1
  have h3 := Real.rpow_add_le_add_rpow ha hb hq0 hq1
  linarith

/-- **The split of the difference functional, pointwise.**  For `σ > 0`, `η > 0`, `0 < τ ≤ T`,
`A : ℂ` and `B` measurable and bounded:

`∫‖(A - B t)/(σ+it)‖² ≤ ∫_{|t|≤τ}‖(A - B t)/(σ+it)‖² + (1+1/η)(2/τ)‖A‖²
  + (1+η)(∫_{τ<|t|≤T}‖B t/(σ+it)‖² + ∫_{T<|t|}‖B t/(σ+it)‖²)`:

off the central window `‖A - B‖² ≤ (1+1/η)‖A‖² + (1+η)‖B‖²` and `∫_{|t|>τ}(σ²+t²)⁻¹ ≤ 2/τ`. -/
lemma integral_normSq_diff_div_le_split {σ η τ T U : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hτ : 0 < τ)
    (hτT : τ ≤ T) (A : ℂ) {B : ℝ → ℂ} (hB : Measurable B) (hBU : ∀ t, ‖B t‖ ≤ U) :
    (∫ t, ‖(A - B t) / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ (∫ t in Set.Icc (-τ) τ, ‖(A - B t) / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        + (1 + 1 / η) * (2 / τ) * ‖A‖ ^ 2
        + (1 + η) * ((∫ t in {t : ℝ | τ < |t| ∧ |t| ≤ T},
              ‖B t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
            + ∫ t in {t : ℝ | T < |t|}, ‖B t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
  have hρ := integrable_inv_sq_add_sq hσ.ne'
  have hw : ∀ (z : ℂ) (t : ℝ), ‖z / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      = (σ ^ 2 + t ^ 2)⁻¹ * ‖z‖ ^ 2 := fun z t => norm_div_ofReal_add_mul_I_sq σ t z
  have hw0 : ∀ t : ℝ, 0 ≤ (σ ^ 2 + t ^ 2)⁻¹ := fun t => inv_nonneg.2 (by positivity)
  -- integrability
  have hden : Measurable fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I := by fun_prop
  have hgm : Measurable fun t => ‖(A - B t) / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    ((measurable_const.sub hB).div hden).norm.pow_const 2
  have hhm : Measurable fun t => ‖B t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    (hB.div hden).norm.pow_const 2
  have hgi : Integrable fun t => ‖(A - B t) / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    refine (hρ.const_mul ((‖A‖ + U) ^ 2)).mono' hgm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), hw]
    have h := pow_le_pow_left₀ (norm_nonneg _) (le_trans (norm_sub_le A (B t))
      (add_le_add le_rfl (hBU t))) 2
    exact le_of_le_of_eq (mul_le_mul_of_nonneg_left h (hw0 t)) (mul_comm _ _)
  have hhi : Integrable fun t => ‖B t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    refine (hρ.const_mul (U ^ 2)).mono' hhm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), hw]
    have h := pow_le_pow_left₀ (norm_nonneg _) (hBU t) 2
    exact le_of_le_of_eq (mul_le_mul_of_nonneg_left h (hw0 t)) (mul_comm _ _)
  -- the sets
  have hCm : MeasurableSet (Set.Icc (-τ) τ) := measurableSet_Icc
  have hcompl : (Set.Icc (-τ) τ)ᶜ = {t : ℝ | τ < |t|} := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_setOf_eq, not_and_or, not_le]
    constructor
    · rintro (h | h)
      · exact lt_abs.2 (Or.inr (by linarith))
      · exact lt_abs.2 (Or.inl h)
    · intro h
      rcases lt_abs.1 h with h | h
      · exact Or.inr h
      · exact Or.inl (by linarith)
  have hfarm : MeasurableSet {t : ℝ | T < |t|} := measurableSet_lt measurable_const (by fun_prop)
  have hunion : {t : ℝ | τ < |t|} = {t : ℝ | τ < |t| ∧ |t| ≤ T} ∪ {t : ℝ | T < |t|} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro h
      by_cases h' : |t| ≤ T
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr (not_le.1 h')
    · rintro (h | h)
      · exact h.1
      · linarith
  have hdisj : Disjoint {t : ℝ | τ < |t| ∧ |t| ≤ T} {t : ℝ | T < |t|} := by
    rw [Set.disjoint_left]
    intro t h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    linarith [h1.2]
  -- the complement
  have hsplit := integral_add_compl hCm hgi
  have hbound : (∫ t in (Set.Icc (-τ) τ)ᶜ, ‖(A - B t) / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ ∫ t in (Set.Icc (-τ) τ)ᶜ, ((1 + 1 / η) * ‖A‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹
        + (1 + η) * ‖B t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
    refine setIntegral_mono hgi.integrableOn
      (((hρ.const_mul _).add (hhi.const_mul _)).integrableOn) (fun t => ?_)
    dsimp only
    rw [hw, hw]
    have h := mul_le_mul_of_nonneg_left (norm_sub_sq_le_split hη A (B t)) (hw0 t)
    nlinarith [h]
  have hint : (∫ t in (Set.Icc (-τ) τ)ᶜ, ((1 + 1 / η) * ‖A‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹
        + (1 + η) * ‖B t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2))
      = (1 + 1 / η) * ‖A‖ ^ 2 * (∫ t in (Set.Icc (-τ) τ)ᶜ, (σ ^ 2 + t ^ 2)⁻¹)
        + (1 + η) * ∫ t in (Set.Icc (-τ) τ)ᶜ, ‖B t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    rw [integral_add ((hρ.const_mul _).integrableOn) ((hhi.const_mul _).integrableOn),
      integral_const_mul, integral_const_mul]
  have hw2 : (∫ t in (Set.Icc (-τ) τ)ᶜ, (σ ^ 2 + t ^ 2)⁻¹) ≤ 2 / τ := by
    rw [hcompl]
    exact setIntegral_inv_sq_add_sq_abs_gt_le σ hτ
  have hh2 : (∫ t in (Set.Icc (-τ) τ)ᶜ, ‖B t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      = (∫ t in {t : ℝ | τ < |t| ∧ |t| ≤ T}, ‖B t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        + ∫ t in {t : ℝ | T < |t|}, ‖B t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    rw [hcompl, hunion]
    exact setIntegral_union hdisj hfarm hhi.integrableOn hhi.integrableOn
  have hA0 : 0 ≤ (1 + 1 / η) * ‖A‖ ^ 2 := by positivity
  have hcoh := mul_le_mul_of_nonneg_left hw2 hA0
  have hfinal : (∫ t in (Set.Icc (-τ) τ)ᶜ, ‖(A - B t) / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ (1 + 1 / η) * (2 / τ) * ‖A‖ ^ 2
        + (1 + η) * ((∫ t in {t : ℝ | τ < |t| ∧ |t| ≤ T},
              ‖B t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
            + ∫ t in {t : ℝ | T < |t|}, ‖B t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
    rw [hint, hh2] at hbound
    have e : (1 + 1 / η) * ‖A‖ ^ 2 * (2 / τ) = (1 + 1 / η) * (2 / τ) * ‖A‖ ^ 2 := by ring
    linarith
  rw [← hsplit]
  linarith

/-- **Proposition B′, split.**  For `½ ≤ q ≤ 1`, `σ > 0`, `L > 0`, `η > 0`, a real `c`
and `k₀ ≤ J`, with `τ = e^{c-J}`, `T = e^{c-k₀}` and `M` bounding `E‖F(½+σ+it)‖²` at every
height, `F` the band product over `[y₀, y₁)` and `P = E‖F(½)‖^{2q}`:

`E[(L⁻¹∫‖(F(½) - F(½+σ+it))/(σ+it)‖²)^q]
  ≤ (∫_{-τ}^{τ}L⁻¹(σ²+t²)⁻¹Q(σ,t))^q·P + ((1+1/η)(2/τ)L⁻¹)^q·P
    + (1+η)^q(2/L)^q∑_{k₀≤k<J}E[W_k^q] + (1+η)^q(L⁻¹(2/T)M)^q`,

`W_k = ∫_{e^{c-k}/e}^{e^{c-k}}(σ²+t²)⁻¹‖F(½+σ+it)‖²dt`: the pointwise split
(`RMF.integral_normSq_diff_div_le_split`), then the central window
(`RMF.integral_rpow_centralWindow_diff_le`), the windows
(`RMF.integral_rpow_mesoRange_band_le_sum_windows`) and Jensen on the far range
(`RMF.integral_rpow_setIntegral_lineDiv_le`). -/
theorem integral_rpow_diffLine_le_split {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {q σ L η c M : ℝ} {k₀ J : ℕ}
    (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hσ : 0 < σ) (hL : 0 < L) (hη : 0 < η) (hk₀J : k₀ ≤ J)
    (hM : ∀ t : ℝ, (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        y₀ y₁ ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ) ≤ M) :
    (∫ ω, (L⁻¹ * ∫ t : ℝ,
        ‖(randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ (1 / 2 : ℂ) ω
          - randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ (∫ t in Set.Icc (-Real.exp (c - J)) (Real.exp (c - J)),
            L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ y₀ y₁ q σ t) ^ q
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
        + ((1 + 1 / η) * (2 / Real.exp (c - J)) * L⁻¹) ^ q
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
        + (1 + η) ^ q * ((2 / L) ^ q * ∑ k ∈ Finset.Ico k₀ J,
            ∫ ω, (∫ t in Set.Icc (Real.exp (c - k) / Real.exp 1) (Real.exp (c - k)),
              (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
                (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ (shiftLine σ t) ω‖ ^ 2) ^ q
              ∂μ)
        + (1 + η) ^ q * (L⁻¹ * ((2 / Real.exp (c - k₀)) * M)) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have hL0 : 0 ≤ L⁻¹ := inv_nonneg.2 hL.le
  set F : ℂ → Ω → ℂ := fun w ω =>
    randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ w ω with hFdef
  set τ := Real.exp (c - J) with hτdef
  set T := Real.exp (c - k₀) with hTdef
  have hτ : 0 < τ := Real.exp_pos _
  have hτT : τ ≤ T := by
    have : (k₀ : ℝ) ≤ J := by exact_mod_cast hk₀J
    exact Real.exp_le_exp.2 (by linarith)
  -- measurability
  have hjoint0 := measurable_uncurry_randomEulerProductIco_line hX y₀ y₁ 0
  have hjoint := measurable_uncurry_randomEulerProductIco_line hX y₀ y₁ (-σ)
  have hline : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω) := by
    convert hjoint using 1
    funext z
    obtain ⟨ω, t⟩ := z
    simp [hFdef]
  have hF0m : Measurable (F (1 / 2 : ℂ)) := by
    have h := hjoint0.comp (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))
    convert h using 1
    funext ω
    simp [hFdef]
  have hdiffm : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω) :=
    (hF0m.comp measurable_fst).sub hline
  -- the envelope
  set Up : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ))) with hUp
  set Upσ : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) with hUpσ
  have henv := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y₁ (c := 1 / 2)
    (by norm_num)
  have henvσ := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y₁ (c := 1 / 2 + σ)
    (by linarith)
  have hre0 : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have hret : ∀ t : ℝ, ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 + σ :=
    fun t => by simp
  have hUB : ∀ᵐ ω ∂μ, ∀ t : ℝ, ‖F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ Upσ := by
    filter_upwards [henvσ] with ω hω t
    exact (hω _ (hret t)).2
  have hUA : ∀ᵐ ω ∂μ, ‖F (1 / 2 : ℂ) ω‖ ≤ Up := by
    filter_upwards [henv] with ω hω
    exact (hω _ hre0).2
  have hUD : ∀ᵐ ω ∂μ, ∀ t : ℝ,
      ‖F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ Up + Upσ := by
    filter_upwards [hUA, hUB] with ω hA hB t
    exact le_trans (norm_sub_le _ _) (add_le_add hA (hB t))
  -- the four pieces
  obtain ⟨a, ha⟩ : ∃ a : Ω → ℝ, a = fun ω => L⁻¹ * ∫ t in Set.Icc (-τ) τ,
      ‖(F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Ω → ℝ, b = fun ω => (1 + 1 / η) * (2 / τ) * L⁻¹ * ‖F (1 / 2 : ℂ) ω‖ ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : Ω → ℝ, m = fun ω => L⁻¹ * ∫ t in {t : ℝ | τ < |t| ∧ |t| ≤ T},
      ‖F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : Ω → ℝ, f = fun ω => L⁻¹ * ∫ t in {t : ℝ | T < |t|},
      ‖F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := ⟨_, rfl⟩
  have ha0 : ∀ ω, 0 ≤ a ω := fun ω => by
    rw [ha]; exact mul_nonneg hL0 (integral_nonneg fun t => sq_nonneg _)
  have hb0 : ∀ ω, 0 ≤ b ω := fun ω => by
    rw [hb]
    have : 0 ≤ (1 + 1 / η) * (2 / τ) * L⁻¹ := by positivity
    positivity
  have hm0 : ∀ ω, 0 ≤ m ω := fun ω => by
    rw [hm]; exact mul_nonneg hL0 (integral_nonneg fun t => sq_nonneg _)
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => by
    rw [hf]; exact mul_nonneg hL0 (integral_nonneg fun t => sq_nonneg _)
  -- the pointwise split
  have hpt : ∀ᵐ ω ∂μ, (L⁻¹ * ∫ t : ℝ,
        ‖(F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q
      ≤ a ω ^ q + b ω ^ q + (1 + η) ^ q * m ω ^ q + (1 + η) ^ q * f ω ^ q := by
    filter_upwards [hUB] with ω hω
    have hBm : Measurable fun t : ℝ => F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω :=
      hline.of_uncurry_left
    have hsp := integral_normSq_diff_div_le_split hσ hη hτ hτT (F (1 / 2 : ℂ) ω) hBm hω
    have hlhs0 : 0 ≤ L⁻¹ * ∫ t : ℝ,
        ‖(F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
      mul_nonneg hL0 (integral_nonneg fun t => sq_nonneg _)
    have hle : L⁻¹ * ∫ t : ℝ,
        ‖(F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        ≤ a ω + b ω + (1 + η) * m ω + (1 + η) * f ω := by
      have h := mul_le_mul_of_nonneg_left hsp hL0
      rw [ha, hb, hm, hf]
      dsimp only
      nlinarith [h]
    have hη0 : (0 : ℝ) ≤ 1 + η := by linarith
    refine le_trans (Real.rpow_le_rpow hlhs0 hle hq0') ?_
    refine le_trans (rpow_add_add_add_le (ha0 ω) (hb0 ω) (mul_nonneg hη0 (hm0 ω))
      (mul_nonneg hη0 (hf0 ω)) hq0' hq1) (le_of_eq ?_)
    rw [Real.mul_rpow hη0 (hm0 ω), Real.mul_rpow hη0 (hf0 ω)]
  -- integrability
  have hIlhs : Integrable (fun ω => (L⁻¹ * ∫ t : ℝ,
        ‖(F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q) μ := by
    have h := integrable_rpow_setIntegral_lineDiv_of_bound (μ := μ) (S := Set.univ)
      (q := q) hσ hL hq0' hdiffm hUD
    simpa only [Measure.restrict_univ] using h
  have hIa : Integrable (fun ω => a ω ^ q) μ := by
    rw [ha]
    exact integrable_rpow_setIntegral_lineDiv_of_bound (μ := μ) (S := Set.Icc (-τ) τ)
      (q := q) hσ hL hq0' hdiffm hUD
  have hIm : Integrable (fun ω => m ω ^ q) μ := by
    rw [hm]
    exact integrable_rpow_setIntegral_lineDiv_of_bound (μ := μ)
      (S := {t : ℝ | τ < |t| ∧ |t| ≤ T}) (q := q) hσ hL hq0' hline hUB
  have hIf : Integrable (fun ω => f ω ^ q) μ := by
    rw [hf]
    exact integrable_rpow_setIntegral_lineDiv_of_bound (μ := μ) (S := {t : ℝ | T < |t|})
      (q := q) hσ hL hq0' hline hUB
  have hk0 : 0 ≤ (1 + 1 / η) * (2 / τ) * L⁻¹ := by positivity
  have hbq : ∀ ω, b ω ^ q = ((1 + 1 / η) * (2 / τ) * L⁻¹) ^ q * ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q) := by
    intro ω
    rw [hb]
    dsimp only
    rw [Real.mul_rpow hk0 (sq_nonneg _), ← norm_rpow_two_mul]
  have hIP : Integrable (fun ω => ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q)) μ := by
    refine (memLp_top_of_bound (hF0m.norm.pow_const _).aestronglyMeasurable (Up ^ (2 * q)) ?_
      ).integrable le_top
    filter_upwards [hUA] with ω hω
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) hω (by linarith)
  have hIb : Integrable (fun ω => b ω ^ q) μ := by
    simp_rw [hbq]
    exact hIP.const_mul _
  -- integrate
  have hI2 : Integrable (fun ω => a ω ^ q + b ω ^ q) μ := hIa.add hIb
  have hIm' : Integrable (fun ω => (1 + η) ^ q * m ω ^ q) μ := hIm.const_mul _
  have hIf' : Integrable (fun ω => (1 + η) ^ q * f ω ^ q) μ := hIf.const_mul _
  have hI3 : Integrable (fun ω => a ω ^ q + b ω ^ q + (1 + η) ^ q * m ω ^ q) μ := hI2.add hIm'
  have hstep : (∫ ω, (L⁻¹ * ∫ t : ℝ,
        ‖(F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ ∫ ω, (a ω ^ q + b ω ^ q + (1 + η) ^ q * m ω ^ q + (1 + η) ^ q * f ω ^ q) ∂μ :=
    integral_mono_ae hIlhs (hI3.add hIf') hpt
  rw [integral_add hI3 hIf', integral_add hI2 hIm', integral_add hIa hIb, integral_const_mul,
    integral_const_mul] at hstep
  -- the central window
  have hEa : (∫ ω, a ω ^ q ∂μ)
      ≤ (∫ t in Set.Icc (-τ) τ, L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ y₀ y₁ q σ t) ^ q
        * ∫ ω, ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ := by
    have hcen := integral_rpow_centralWindow_diff_le hX y₀ y₁ (τ := τ) hq0 hq1 hσ hL
    have heq : ∀ ω, a ω = ∫ t in Set.Icc (-τ) τ, L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹
        * ‖F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 := by
      intro ω
      rw [ha]
      dsimp only
      rw [← integral_const_mul]
      congr 1
      funext t
      rw [norm_div_ofReal_add_mul_I_sq]
      ring
    simp_rw [heq]
    exact hcen
  -- the coherent part
  have hEb : (∫ ω, b ω ^ q ∂μ)
      = ((1 + 1 / η) * (2 / τ) * L⁻¹) ^ q * ∫ ω, ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ := by
    simp_rw [hbq]
    exact integral_const_mul _ _
  -- the windows
  have hEm : (∫ ω, m ω ^ q ∂μ)
      ≤ (2 / L) ^ q * ∑ k ∈ Finset.Ico k₀ J,
          ∫ ω, (∫ t in Set.Icc (Real.exp (c - k) / Real.exp 1) (Real.exp (c - k)),
            (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
              (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ (shiftLine σ t) ω‖ ^ 2) ^ q
            ∂μ := by
    rw [hm]
    exact integral_rpow_mesoRange_band_le_sum_windows hX y₀ y₁ (c := c) hσ
      (by linarith) hq1 hL hk₀J
  -- the far range
  have hEf : (∫ ω, f ω ^ q ∂μ) ≤ (L⁻¹ * ((2 / T) * M)) ^ q := by
    rw [hf]
    have hJ := integral_rpow_setIntegral_lineDiv_le (μ := μ)
      (F := fun ω t => F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
      (S := {t : ℝ | T < |t|}) (L := L) (q := q) (M := M) hσ hL hq0' hq1 hline hUB hM
    refine le_trans hJ (Real.rpow_le_rpow ?_ ?_ hq0')
    · have hM0 : 0 ≤ M := le_trans (integral_nonneg fun ω => sq_nonneg _) (hM 0)
      exact mul_nonneg hL0 (mul_nonneg (integral_nonneg fun t => inv_nonneg.2 (by positivity))
        hM0)
    · have hM0 : 0 ≤ M := le_trans (integral_nonneg fun ω => sq_nonneg _) (hM 0)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (setIntegral_inv_sq_add_sq_abs_gt_le σ (Real.exp_pos _)) hM0) hL0
  have hη1 : (0 : ℝ) ≤ (1 + η) ^ q := Real.rpow_nonneg (by linarith) _
  have h3 := mul_le_mul_of_nonneg_left hEm hη1
  have h4 := mul_le_mul_of_nonneg_left hEf hη1
  linarith [hstep, hEa, hEb, h3, h4]

/-- **Proposition B′ for the truncation bound's functional**: `RMF.integral_rpow_diffLine_le_split`
for `Ψ = RMF.bandDiffLine … y z σ`, the band `(y, z]` and `L = 2π log z`. -/
theorem integral_rpow_bandDiffLine_le_split {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y z : ℕ) (hz : 2 ≤ z) {q σ η c M : ℝ} {k₀ J : ℕ}
    (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hσ : 0 < σ) (hη : 0 < η) (hk₀J : k₀ ≤ J)
    (hM : ∀ t : ℝ, (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (y + 1) (z + 1) ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ) ≤ M) :
    (∫ ω, bandDiffLine (fun ω => squarefreeExtension fun p => X p ω) y z σ ω ^ q ∂μ)
      ≤ (∫ t in Set.Icc (-Real.exp (c - J)) (Real.exp (c - J)),
            (2 * Real.pi * Real.log z)⁻¹ * (σ ^ 2 + t ^ 2)⁻¹
              * diffQ (y + 1) (z + 1) q σ t) ^ q
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
        + ((1 + 1 / η) * (2 / Real.exp (c - J)) * (2 * Real.pi * Real.log z)⁻¹) ^ q
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
        + (1 + η) ^ q * ((2 / (2 * Real.pi * Real.log z)) ^ q * ∑ k ∈ Finset.Ico k₀ J,
            ∫ ω, (∫ t in Set.Icc (Real.exp (c - k) / Real.exp 1) (Real.exp (c - k)),
              (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
                (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1) (shiftLine σ t)
                  ω‖ ^ 2) ^ q ∂μ)
        + (1 + η) ^ q
          * ((2 * Real.pi * Real.log z)⁻¹ * ((2 / Real.exp (c - k₀)) * M)) ^ q := by
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hL : 0 < 2 * Real.pi * Real.log z := by
    have := Real.log_pos (by linarith : (1 : ℝ) < z)
    positivity
  exact integral_rpow_diffLine_le_split hX (y + 1) (z + 1) hq0 hq1 hσ hL hη hk₀J hM

/-- **The second moment on the shifted line**: over the band `[y₀, y₁)`,
`E‖F(½+σ+it)‖² ≤ exp(∑_p 1/p)` for `σ ≥ 0` and every `t`
(`RMF.IsRademacherRMF.integral_norm_randomEulerProductIco_sq_le`). -/
lemma integral_normSq_randomEulerProductIco_line_le_exp {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
      ≤ Real.exp (∑ p ∈ primesIco y₀ y₁, ((p : ℝ))⁻¹) := by
  refine le_trans (hX.isRademacherRMF.integral_norm_randomEulerProductIco_sq_le y₀ y₁ _) ?_
  refine Real.exp_le_exp.2 (Finset.sum_le_sum fun p hp => ?_)
  have hre : ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 + σ := by simp
  rw [hre, show -2 * (1 / 2 + σ) = -(1 + 2 * σ) by ring]
  exact rpow_neg_shift_le_inv (prime_of_mem_primesIco hp).one_lt.le hσ

/-- **One window of a band without a split, by Jensen**: for `σ > 0`, `0 ≤ q ≤ 1`, `T > 0` and `M`
bounding the second moment on the line,
`E[(∫_{T/e}^{T}(σ²+t²)⁻¹‖F(½+σ+it)‖²dt)^q] ≤ ((e-1)M/T)^q`
(`RMF.integral_rpow_setIntegral_lineDiv_le` at `L = 1`). -/
theorem integral_rpow_window_band_le_jensen_nosplit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {σ q T M : ℝ} (hσ : 0 < σ) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hT : 0 < T)
    (hM : ∀ t : ℝ, (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        y₀ y₁ ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ) ≤ M) :
    (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ ((Real.exp 1 - 1) / T * M) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hs : ∀ t : ℝ, shiftLine σ t = (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I := by
    intro t
    rw [shiftLine]
    push_cast
    ring
  have hjoint := measurable_uncurry_randomEulerProductIco_line hX y₀ y₁ (-σ)
  have hline : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω) := by
    convert hjoint using 1
    funext z
    obtain ⟨ω, t⟩ := z
    simp
  have henv := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y₁ (c := 1 / 2 + σ)
    (by linarith)
  have hU : ∀ᵐ ω ∂μ, ∀ t : ℝ,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖
        ≤ ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) := by
    filter_upwards [henv] with ω hω t
    exact (hω _ (by simp)).2
  have hJ := integral_rpow_setIntegral_lineDiv_le (μ := μ)
    (F := fun ω t => randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
      ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
    (S := Set.Icc (T / Real.exp 1) T) (L := 1) (q := q) (M := M) hσ one_pos hq0 hq1 hline hU hM
  have hEq : (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      = ∫ ω, ((1 : ℝ)⁻¹ * ∫ t in Set.Icc (T / Real.exp 1) T,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ := by
    congr 1
    funext ω
    rw [inv_one, one_mul]
    congr 2
    funext t
    rw [norm_div_ofReal_add_mul_I_sq, hs]
  rw [hEq]
  have hM0 : 0 ≤ M := le_trans (integral_nonneg fun ω => sq_nonneg _) (hM 0)
  have hw := setIntegral_inv_sq_add_sq_mul_exp_window_le σ hT (β := 0) le_rfl
  simp only [zero_mul, Real.exp_zero, mul_one, sub_self, add_zero] at hw
  refine le_trans hJ (Real.rpow_le_rpow ?_ ?_ hq0)
  · exact mul_nonneg (inv_nonneg.2 zero_le_one)
      (mul_nonneg (integral_nonneg fun t => inv_nonneg.2 (by positivity)) hM0)
  · rw [inv_one, one_mul]
    exact mul_le_mul_of_nonneg_right hw hM0

end RMF
