/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.LineSplit
import RMF.Weighted.LineTail
import RMF.Weighted.LowerDamped
import RMF.Weighted.FracWindowsExplicit.Pieces

/-!
# The weighted extended sum: the line integral

The third step of the proof of Proposition 1.5 of the paper.  `RMF.norm_logWeightedSum_le` bounds
the Riesz mean by `(e/2π)∫_ℝ ρ|F|`, `ρ(t) = (σ² + t²)⁻¹`, `F(t) = F_{⌊x⌋+1}(½+σ+it)`,
`σ = 1/log x`, with the first power of `|F|`.  For `x ≥ 8` and `0 < q ≤ ½`
(`RMF.exists_const_integral_rpow_lineAbs_le`), with `C` independent of `X`, `μ`, `x` and `q`,

`E[((log x)⁻¹∫_ℝ ρ|F|)^{2q}] ≤ C(1 + q⁻²)(log x)^{q(2q-1)}`.

`|F|` is even almost surely, so the line folds onto `t > 0`, cut at `e^{-J}` and `1`.
Cauchy–Schwarz on each piece (`RMF.sq_integral_mul_le`) turns `|F|` at exponent `2q` into `|F|²`
at exponent `q`: the central window, the `e`-adic windows `(T_j/e, T_j]` and the tail `|t| > 1`
then carry the existing bounds `RMF.exists_const_integral_rpow_centralRange_le_rademacher`,
`RMF.mesoBlock_weighted_le_trivial` and `RMF.exists_integral_rpow_eulerProductLine_tail_le`.
Window `j` contributes `≪ (log x)^{-q}e^{2q²(J-j)}`, and `e^{J-1} ≤ log x` sums these to
`≪ (1 + q⁻²)(log x)^{q(2q-1)}`.  The Cauchy–Schwarz is per window: over the whole range it would
lose a power of `log x`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Cauchy–Schwarz -/

/-- **Cauchy–Schwarz with a weight**: `(∫ρg)² ≤ (∫ρ)(∫ρg²)` for `ρ ≥ 0`, with `ρ`, `ρg` and `ρg²`
integrable.  The quadratic `λ ↦ ∫ρ(λ - g)²` is nonnegative, so its discriminant is not
positive. -/
lemma sq_integral_mul_le {α : Type*} [MeasurableSpace α] {ν : Measure α} {ρ g : α → ℝ}
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρ : Integrable ρ ν) (hρg : Integrable (fun t => ρ t * g t) ν)
    (hρg2 : Integrable (fun t => ρ t * g t ^ 2) ν) :
    (∫ t, ρ t * g t ∂ν) ^ 2 ≤ (∫ t, ρ t ∂ν) * ∫ t, ρ t * g t ^ 2 ∂ν := by
  have hquad : ∀ x : ℝ, 0 ≤ (∫ t, ρ t ∂ν) * (x * x) + (-2 * ∫ t, ρ t * g t ∂ν) * x
      + ∫ t, ρ t * g t ^ 2 ∂ν := by
    intro x
    have h1 : Integrable (fun t => ρ t * (x * x)) ν := hρ.mul_const _
    have h2 : Integrable (fun t => (-2 * x) * (ρ t * g t)) ν := hρg.const_mul _
    have h12 : Integrable (fun t => ρ t * (x * x) + (-2 * x) * (ρ t * g t)) ν := h1.add h2
    have hval : (∫ t, (ρ t * (x * x) + (-2 * x) * (ρ t * g t) + ρ t * g t ^ 2) ∂ν)
        = (∫ t, ρ t ∂ν) * (x * x) + (-2 * ∫ t, ρ t * g t ∂ν) * x + ∫ t, ρ t * g t ^ 2 ∂ν := by
      rw [integral_add h12 hρg2, integral_add h1 h2, integral_mul_const, integral_const_mul]
      ring
    rw [← hval]
    refine integral_nonneg fun t => ?_
    have e : ρ t * (x * x) + (-2 * x) * (ρ t * g t) + ρ t * g t ^ 2 = ρ t * (x - g t) ^ 2 := by
      ring
    rw [e]
    exact mul_nonneg (hρ0 t) (sq_nonneg _)
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  have e : (-2 * ∫ t, ρ t * g t ∂ν) ^ 2 = 4 * (∫ t, ρ t * g t ∂ν) ^ 2 := by ring
  rw [e] at hd
  linarith

/-- **Cauchy–Schwarz on an interval**: `(∫_{[a,b]} g)² ≤ (b - a)∫_{[a,b]} g²`. -/
lemma sq_setIntegral_Icc_le {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntegrableOn g (Set.Icc a b)) (hg2 : IntegrableOn (fun t => g t ^ 2) (Set.Icc a b)) :
    (∫ t in Set.Icc a b, g t) ^ 2 ≤ (b - a) * ∫ t in Set.Icc a b, g t ^ 2 := by
  have h := sq_integral_mul_le (ν := volume.restrict (Set.Icc a b)) (ρ := fun _ => (1 : ℝ))
    (g := g) (fun _ => zero_le_one)
    (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    (by simp only [one_mul]; exact hg) (by simp only [one_mul]; exact hg2)
  simp only [one_mul] at h
  rwa [setIntegral_const, Real.volume_real_Icc_of_le hab, smul_eq_mul, mul_one] at h

/-! ### Small algebra -/

/-- `u^{2q} ≤ v^q` from `u² ≤ v`, for `u, q ≥ 0`. -/
lemma rpow_two_mul_le_of_sq_le {u v q : ℝ} (hu : 0 ≤ u) (hq : 0 ≤ q) (h : u ^ 2 ≤ v) :
    u ^ (2 * q) ≤ v ^ q := by
  rw [Real.rpow_mul hu, Real.rpow_two]
  exact Real.rpow_le_rpow (sq_nonneg u) h hq

/-- `(2σQ)² ≤ 4π(ℓ⁻¹I)` from `Q² ≤ (π/σ)I` and `σ ≤ ℓ⁻¹`. -/
lemma sq_two_mul_le_pi {σ ℓ Q I : ℝ} (hσ : 0 < σ) (hσℓ : σ ≤ ℓ⁻¹) (hI : 0 ≤ I)
    (hQ : Q ^ 2 ≤ Real.pi / σ * I) : (2 * σ * Q) ^ 2 ≤ 4 * Real.pi * (ℓ⁻¹ * I) := by
  calc (2 * σ * Q) ^ 2 = 4 * σ ^ 2 * Q ^ 2 := by ring
    _ ≤ 4 * σ ^ 2 * (Real.pi / σ * I) := mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = 4 * Real.pi * (σ * I) := by field_simp
    _ ≤ 4 * Real.pi * (ℓ⁻¹ * I) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hσℓ hI) (by positivity)

/-- `(2σQ)² ≤ 8σ(ℓ⁻¹I)` from `Q² ≤ 2I` and `σ ≤ ℓ⁻¹`. -/
lemma sq_two_mul_le_eight {σ ℓ Q I : ℝ} (hσ : 0 < σ) (hσℓ : σ ≤ ℓ⁻¹) (hI : 0 ≤ I)
    (hQ : Q ^ 2 ≤ 2 * I) : (2 * σ * Q) ^ 2 ≤ 8 * σ * (ℓ⁻¹ * I) := by
  calc (2 * σ * Q) ^ 2 = 4 * σ ^ 2 * Q ^ 2 := by ring
    _ ≤ 4 * σ ^ 2 * (2 * I) := mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = 8 * σ * (σ * I) := by ring
    _ ≤ 8 * σ * (ℓ⁻¹ * I) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hσℓ hI) (by positivity)

/-- `(2σ(cV))² ≤ 4(σ²(cT))(cW)` from `V² ≤ TW`. -/
lemma sq_window_le {σ c T V W : ℝ} (hV : V ^ 2 ≤ T * W) :
    (2 * σ * (c * V)) ^ 2 ≤ 4 * (σ ^ 2 * (c * T)) * (c * W) := by
  calc (2 * σ * (c * V)) ^ 2 = 4 * σ ^ 2 * c ^ 2 * V ^ 2 := by ring
    _ ≤ 4 * σ ^ 2 * c ^ 2 * (T * W) := mul_le_mul_of_nonneg_left hV (by positivity)
    _ = 4 * (σ ^ 2 * (c * T)) * (c * W) := by ring

/-! ### The geometric sum, from the top -/

/-- **The geometric sum, from the top.**  `∑_{j=1}^{J} e^{(J-j)α} ≤ e^{(J-1)α}(1 + α⁻¹)` for
`α > 0`: `RMF.sum_exp_sub_mul_le` after `j ↦ J + 1 - j`. -/
lemma sum_exp_sub_mul_rev_le {α : ℝ} (hα : 0 < α) (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, Real.exp (((J : ℝ) - j) * α)
      ≤ Real.exp (((J : ℝ) - 1) * α) * (1 + α⁻¹) := by
  have hrefl : ∑ j ∈ Finset.Icc 1 J, Real.exp (((J : ℝ) - j) * α)
      = ∑ j ∈ Finset.Icc 1 J, Real.exp (((J : ℝ) - 1) * α) * Real.exp (((j : ℝ) - J) * α) := by
    refine Finset.sum_nbij' (fun j => J + 1 - j) (fun j => J + 1 - j) (fun j hj => ?_)
      (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
    · simp only [Finset.mem_Icc] at hj ⊢
      omega
    · simp only [Finset.mem_Icc] at hj ⊢
      omega
    · simp only [Finset.mem_Icc] at hj
      omega
    · simp only [Finset.mem_Icc] at hj
      omega
    · simp only [Finset.mem_Icc] at hj
      have hc : ((J + 1 - j : ℕ) : ℝ) = (J : ℝ) + 1 - j := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [hc, ← Real.exp_add]
      congr 1
      ring
  rw [hrefl, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_exp_sub_mul_le hα J) (Real.exp_pos _).le

/-! ### The fold and the cut -/

/-- **The fold and the cut**: for an even integrable `f` and `0 ≤ a ≤ b`,
`∫_ℝ f = 2(∫_{(0,a]} f + ∫_{(a,b]} f + ∫_{(b,∞)} f)`. -/
lemma integral_eq_two_mul_pieces_of_even {f : ℝ → ℝ} (hf : Integrable f)
    (heven : ∀ t, f (-t) = f t) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ t, f t = 2 * ((∫ t in Set.Ioc 0 a, f t) + (∫ t in Set.Ioc a b, f t)
      + ∫ t in Set.Ioi b, f t) := by
  have habs : ∀ t, f |t| = f t := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg ht, heven]
  have hfold : ∫ t, f t = 2 * ∫ t in Set.Ioi 0, f t := by
    have h := integral_comp_abs (f := f)
    simp only [habs] at h
    exact h
  rw [hfold, setIntegral_Ioi_eq_Ioc_add_Ioi ha hf.integrableOn,
    setIntegral_Ioi_eq_Ioc_add_Ioi hab hf.integrableOn]
  ring

/-! ### The three pieces, pathwise

For a continuous `g ≥ 0`, which below is `t ↦ |F(½+σ+it)|` on one path. -/

/-- **The central piece**: `(2σ∫_{(0,w]}ρg)^{2q} ≤ (4π)^q(ℓ⁻¹∫_{[-w,w]}ρg²)^q` for `σ ≤ ℓ⁻¹`:
the piece lies in `[-w, w]`, and Cauchy–Schwarz with `∫_{[-w,w]}ρ ≤ π/σ`. -/
lemma rpow_central_piece_le {g : ℝ → ℝ} (hgc : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    {σ ℓ q w : ℝ} (hσ : 0 < σ) (hσℓ : σ ≤ ℓ⁻¹) (hq0 : 0 ≤ q) (hw : 0 ≤ w) :
    (2 * σ * ∫ t in Set.Ioc 0 w, (σ ^ 2 + t ^ 2)⁻¹ * g t) ^ (2 * q)
      ≤ (4 * Real.pi) ^ q
        * (ℓ⁻¹ * ∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹ * g t ^ 2) ^ q := by
  have hρc : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun t => by positivity
  have hρ0 : ∀ t : ℝ, 0 ≤ (σ ^ 2 + t ^ 2)⁻¹ := fun t => by positivity
  have hI0 : IntegrableOn (fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹) (Set.Icc (-w) w) :=
    hρc.integrableOn_Icc
  have hI1 : IntegrableOn (fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ * g t) (Set.Icc (-w) w) :=
    (hρc.mul hgc).integrableOn_Icc
  have hI2 : IntegrableOn (fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ * g t ^ 2) (Set.Icc (-w) w) :=
    (hρc.mul (hgc.pow 2)).integrableOn_Icc
  have hsub : Set.Ioc 0 w ⊆ Set.Icc (-w) w := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  have hP0 : 0 ≤ ∫ t in Set.Ioc 0 w, (σ ^ 2 + t ^ 2)⁻¹ * g t :=
    setIntegral_nonneg measurableSet_Ioc fun t _ => mul_nonneg (hρ0 t) (hg0 t)
  have hPQ : (∫ t in Set.Ioc 0 w, (σ ^ 2 + t ^ 2)⁻¹ * g t)
      ≤ ∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹ * g t :=
    setIntegral_mono_set hI1 (Filter.Eventually.of_forall fun t => mul_nonneg (hρ0 t) (hg0 t))
      (show Set.Ioc 0 w ≤ Set.Icc (-w) w from hsub).eventuallyLE
  have hI2nn : 0 ≤ ∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹ * g t ^ 2 :=
    setIntegral_nonneg measurableSet_Icc fun t _ => mul_nonneg (hρ0 t) (sq_nonneg _)
  have hQ2 : (∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹ * g t) ^ 2
      ≤ Real.pi / σ * ∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹ * g t ^ 2 :=
    (sq_integral_mul_le hρ0 hI0 hI1 hI2).trans
      (mul_le_mul_of_nonneg_right (setIntegral_inv_sq_add_sq_le hσ hw) hI2nn)
  have hℓ0 : 0 ≤ ℓ⁻¹ := hσ.le.trans hσℓ
  calc (2 * σ * ∫ t in Set.Ioc 0 w, (σ ^ 2 + t ^ 2)⁻¹ * g t) ^ (2 * q)
      ≤ (2 * σ * ∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹ * g t) ^ (2 * q) :=
        Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_left hPQ (by positivity)) (by linarith)
    _ ≤ (4 * Real.pi * (ℓ⁻¹ * ∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹ * g t ^ 2)) ^ q :=
        rpow_two_mul_le_of_sq_le (mul_nonneg (by positivity) (hP0.trans hPQ)) hq0
          (sq_two_mul_le_pi hσ hσℓ hI2nn hQ2)
    _ = (4 * Real.pi) ^ q
        * (ℓ⁻¹ * ∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹ * g t ^ 2) ^ q :=
        Real.mul_rpow (by positivity) (mul_nonneg hℓ0 hI2nn)

/-- **The tail piece**: `(2σ∫_{(1,∞)}ρg)^{2q} ≤ (8σ)^q(ℓ⁻¹∫_{|t|>1}ρg²)^q` for bounded `g` and
`σ ≤ ℓ⁻¹`: the piece lies in `|t| > 1`, and Cauchy–Schwarz with `∫_{|t|>1}ρ ≤ 2`. -/
lemma rpow_tail_piece_le {g : ℝ → ℝ} (hgc : Continuous g) (hg0 : ∀ t, 0 ≤ g t) {U : ℝ}
    (hgU : ∀ t, g t ≤ U) {σ ℓ q : ℝ} (hσ : 0 < σ) (hσℓ : σ ≤ ℓ⁻¹) (hq0 : 0 ≤ q) :
    (2 * σ * ∫ t in Set.Ioi 1, (σ ^ 2 + t ^ 2)⁻¹ * g t) ^ (2 * q)
      ≤ (8 * σ) ^ q * (ℓ⁻¹ * ∫ t in {t : ℝ | 1 < |t|}, (σ ^ 2 + t ^ 2)⁻¹ * g t ^ 2) ^ q := by
  have hρc : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun t => by positivity
  have hρ0 : ∀ t : ℝ, 0 ≤ (σ ^ 2 + t ^ 2)⁻¹ := fun t => by positivity
  have hρi : Integrable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ := integrable_inv_sq_add_sq hσ.ne'
  have hU0 : 0 ≤ U := (hg0 0).trans (hgU 0)
  have hI1 : Integrable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ * g t := by
    refine Integrable.mono' (hρi.mul_const U) (hρc.mul hgc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hρ0 t) (hg0 t))]
    exact mul_le_mul_of_nonneg_left (hgU t) (hρ0 t)
  have hI2 : Integrable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ * g t ^ 2 := by
    refine Integrable.mono' (hρi.mul_const (U ^ 2)) (hρc.mul (hgc.pow 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hρ0 t) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hg0 t) (hgU t) 2) (hρ0 t)
  have hSmeas : MeasurableSet {t : ℝ | 1 < |t|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hsub : Set.Ioi (1 : ℝ) ⊆ {t : ℝ | 1 < |t|} := fun t ht => by
    have ht' : (1 : ℝ) < t := ht
    rw [Set.mem_setOf_eq, abs_of_pos (by linarith)]
    exact ht'
  have hP0 : 0 ≤ ∫ t in Set.Ioi 1, (σ ^ 2 + t ^ 2)⁻¹ * g t :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => mul_nonneg (hρ0 t) (hg0 t)
  have hPQ : (∫ t in Set.Ioi 1, (σ ^ 2 + t ^ 2)⁻¹ * g t)
      ≤ ∫ t in {t : ℝ | 1 < |t|}, (σ ^ 2 + t ^ 2)⁻¹ * g t :=
    setIntegral_mono_set hI1.integrableOn
      (Filter.Eventually.of_forall fun t => mul_nonneg (hρ0 t) (hg0 t))
      (show Set.Ioi (1 : ℝ) ≤ {t : ℝ | 1 < |t|} from hsub).eventuallyLE
  have hI2nn : 0 ≤ ∫ t in {t : ℝ | 1 < |t|}, (σ ^ 2 + t ^ 2)⁻¹ * g t ^ 2 :=
    setIntegral_nonneg hSmeas fun t _ => mul_nonneg (hρ0 t) (sq_nonneg _)
  have hmass : (∫ t in {t : ℝ | 1 < |t|}, (σ ^ 2 + t ^ 2)⁻¹) ≤ 2 := by
    have h := setIntegral_inv_sq_add_sq_abs_gt_le σ one_pos
    rwa [div_one] at h
  have hQ2 : (∫ t in {t : ℝ | 1 < |t|}, (σ ^ 2 + t ^ 2)⁻¹ * g t) ^ 2
      ≤ 2 * ∫ t in {t : ℝ | 1 < |t|}, (σ ^ 2 + t ^ 2)⁻¹ * g t ^ 2 :=
    (sq_integral_mul_le hρ0 hρi.integrableOn hI1.integrableOn hI2.integrableOn).trans
      (mul_le_mul_of_nonneg_right hmass hI2nn)
  have hℓ0 : 0 ≤ ℓ⁻¹ := hσ.le.trans hσℓ
  calc (2 * σ * ∫ t in Set.Ioi 1, (σ ^ 2 + t ^ 2)⁻¹ * g t) ^ (2 * q)
      ≤ (2 * σ * ∫ t in {t : ℝ | 1 < |t|}, (σ ^ 2 + t ^ 2)⁻¹ * g t) ^ (2 * q) :=
        Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_left hPQ (by positivity)) (by linarith)
    _ ≤ (8 * σ * (ℓ⁻¹ * ∫ t in {t : ℝ | 1 < |t|}, (σ ^ 2 + t ^ 2)⁻¹ * g t ^ 2)) ^ q :=
        rpow_two_mul_le_of_sq_le (mul_nonneg (by positivity) (hP0.trans hPQ)) hq0
          (sq_two_mul_le_eight hσ hσℓ hI2nn hQ2)
    _ = (8 * σ) ^ q * (ℓ⁻¹ * ∫ t in {t : ℝ | 1 < |t|}, (σ ^ 2 + t ^ 2)⁻¹ * g t ^ 2) ^ q :=
        Real.mul_rpow (by positivity) (mul_nonneg hℓ0 hI2nn)

/-- **The window piece**: over the `e`-adic windows `(T_j/e, T_j]`, `T_j = e^{j-J}`, which cover
`(e^{-J}, 1]` and on which `ρ ≤ c_j = e^{2(J+1-j)}`,
`(2σ∫_{(e^{-J},1]}ρg)^{2q} ≤ ∑_j (4σ²c_jT_j)^q·c_j^q(∫_{[T_j/e,T_j]}g²)^q`: the window
domination `RMF.setIntegral_weight_le_sum_windows`, subadditivity, and Cauchy–Schwarz on each
window, `(∫g)² ≤ T_j∫g²`. -/
lemma rpow_window_piece_le {g : ℝ → ℝ} (hgc : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    {σ q : ℝ} (hσ : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (J : ℕ) :
    (2 * σ * ∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1, (σ ^ 2 + t ^ 2)⁻¹ * g t) ^ (2 * q)
      ≤ ∑ j ∈ Finset.Icc 1 J,
          (4 * (σ ^ 2 * (Real.exp (2 * ((J : ℝ) + 1 - j)) * mesoT J j))) ^ q
            * ((Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
              * (∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j), g t ^ 2) ^ q) := by
  have he1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hρc : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun t => by positivity
  have hρ0 : ∀ t : ℝ, 0 ≤ (σ ^ 2 + t ^ 2)⁻¹ := fun t => by positivity
  have hρb : ∀ t : ℝ, (σ ^ 2 + t ^ 2)⁻¹ ≤ (σ ^ 2)⁻¹ := fun t =>
    (inv_le_inv₀ (by positivity) (by positivity)).2 (by nlinarith [sq_nonneg t])
  have hlow : ∀ j : ℕ, mesoT J j / Real.exp 1 = Real.exp ((j : ℝ) - 1 - J) := by
    intro j
    rw [mesoT, ← Real.exp_sub]
    congr 1
    ring
  -- the windows cover `(e^{-J}, 1]`, inside `[0, 1]`
  have hSAB : Set.Ioc (Real.exp (-(J : ℝ))) 1 ⊆ Set.Icc 0 1 := fun t ht =>
    ⟨le_trans (Real.exp_pos _).le ht.1.le, ht.2⟩
  have hIAB : ∀ j ∈ Finset.Icc 1 J,
      Set.Ioc (mesoT J j / Real.exp 1) (mesoT J j) ⊆ Set.Icc 0 1 := by
    intro j hj t ht
    rw [Finset.mem_Icc] at hj
    have hjJ : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hj.2
    refine ⟨le_trans (div_pos (mesoT_pos J j) (Real.exp_pos 1)).le ht.1.le, le_trans ht.2 ?_⟩
    exact mesoT_le_one hj.2
  have hcov : ∀ t ∈ Set.Ioc (Real.exp (-(J : ℝ))) 1,
      ∃ j ∈ Finset.Icc 1 J, t ∈ Set.Ioc (mesoT J j / Real.exp 1) (mesoT J j) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans (Real.exp_pos _) ht.1
    have hlt : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht.2
    have hgt : -(J : ℝ) < Real.log t := by
      have := Real.log_lt_log (Real.exp_pos (-(J : ℝ))) ht.1
      rwa [Real.log_exp] at this
    have hu0 : (0 : ℝ) < (J : ℝ) + Real.log t := by linarith
    refine ⟨⌈(J : ℝ) + Real.log t⌉₊, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Nat.ceil_pos.2 hu0, Nat.ceil_le.2 (by linarith)⟩
    · have hce : ((⌈(J : ℝ) + Real.log t⌉₊ : ℕ) : ℝ) < (J : ℝ) + Real.log t + 1 :=
        Nat.ceil_lt_add_one hu0.le
      have hge : (J : ℝ) + Real.log t ≤ ((⌈(J : ℝ) + Real.log t⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      constructor
      · rw [hlow]
        have : Real.exp (((⌈(J : ℝ) + Real.log t⌉₊ : ℕ) : ℝ) - 1 - J) < Real.exp (Real.log t) :=
          Real.exp_lt_exp.2 (by linarith)
        rwa [Real.exp_log ht0] at this
      · have : Real.exp (Real.log t)
            ≤ Real.exp (((⌈(J : ℝ) + Real.log t⌉₊ : ℕ) : ℝ) - J) :=
          Real.exp_le_exp.2 (by linarith)
        rwa [Real.exp_log ht0] at this
  -- the weight on the `j`-th window
  have hρw : ∀ j ∈ Finset.Icc 1 J, ∀ t ∈ Set.Ioc (mesoT J j / Real.exp 1) (mesoT J j),
      (σ ^ 2 + t ^ 2)⁻¹ ≤ Real.exp (2 * ((J : ℝ) + 1 - j)) := by
    intro j _ t ht
    rw [hlow] at ht
    have ht0 : (0 : ℝ) < Real.exp ((j : ℝ) - 1 - J) := Real.exp_pos _
    have htt : Real.exp ((j : ℝ) - 1 - J) < t := ht.1
    have hsq : Real.exp (2 * ((j : ℝ) - 1 - J)) < t ^ 2 := by
      rw [show (2 : ℝ) * ((j : ℝ) - 1 - J) = ((j : ℝ) - 1 - J) + ((j : ℝ) - 1 - J) by ring,
        Real.exp_add]
      nlinarith [ht0, htt]
    have hinv : (Real.exp (2 * ((J : ℝ) + 1 - j)))⁻¹ = Real.exp (2 * ((j : ℝ) - 1 - J)) := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [← inv_inv (Real.exp (2 * ((J : ℝ) + 1 - j))), hinv]
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 (by linarith [sq_nonneg σ, hsq])
  have hdom := setIntegral_weight_le_sum_windows (Finset.Icc 1 J)
    (fun j => mesoT J j / Real.exp 1) (fun j => mesoT J j)
    (fun j => Real.exp (2 * ((J : ℝ) + 1 - j))) (g := g) (ρ := fun t => (σ ^ 2 + t ^ 2)⁻¹)
    (A := 0) (B := 1) (Bρ := (σ ^ 2)⁻¹) (S := Set.Ioc (Real.exp (-(J : ℝ))) 1)
    hg0 hgc.integrableOn_Icc hρ0 hρc.measurable hρb measurableSet_Ioc hSAB hIAB hcov
    (fun j _ => (Real.exp_pos _).le) hρw
  -- Cauchy–Schwarz on each window
  have hV0 : ∀ j : ℕ, 0 ≤ ∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j), g t :=
    fun j => setIntegral_nonneg measurableSet_Icc fun t _ => hg0 t
  have hW0 : ∀ j : ℕ, 0 ≤ ∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j), g t ^ 2 :=
    fun j => setIntegral_nonneg measurableSet_Icc fun t _ => sq_nonneg _
  have hVW : ∀ j : ℕ, (∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j), g t) ^ 2
      ≤ mesoT J j * ∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j), g t ^ 2 := by
    intro j
    have hT0 := mesoT_pos J j
    have hab : mesoT J j / Real.exp 1 ≤ mesoT J j := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      nlinarith
    refine (sq_setIntegral_Icc_le hab hgc.integrableOn_Icc (hgc.pow 2).integrableOn_Icc).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (hW0 j)
    have : 0 ≤ mesoT J j / Real.exp 1 := (div_pos hT0 (Real.exp_pos 1)).le
    linarith
  have hP0 : 0 ≤ ∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1, (σ ^ 2 + t ^ 2)⁻¹ * g t :=
    setIntegral_nonneg measurableSet_Ioc fun t _ => mul_nonneg (hρ0 t) (hg0 t)
  have h2q0 : (0 : ℝ) < 2 * q := by linarith
  have h2q1 : 2 * q ≤ 1 := by linarith
  calc (2 * σ * ∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1, (σ ^ 2 + t ^ 2)⁻¹ * g t) ^ (2 * q)
      ≤ (∑ j ∈ Finset.Icc 1 J, 2 * σ * (Real.exp (2 * ((J : ℝ) + 1 - j))
          * ∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j), g t)) ^ (2 * q) := by
        rw [← Finset.mul_sum]
        exact Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hdom (by positivity))
          h2q0.le
    _ ≤ ∑ j ∈ Finset.Icc 1 J, (2 * σ * (Real.exp (2 * ((J : ℝ) + 1 - j))
          * ∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j), g t)) ^ (2 * q) :=
        rpow_sum_le_sum_rpow _ (fun j => mul_nonneg (by positivity)
          (mul_nonneg (Real.exp_pos _).le (hV0 j))) h2q0 h2q1
    _ ≤ ∑ j ∈ Finset.Icc 1 J,
          (4 * (σ ^ 2 * (Real.exp (2 * ((J : ℝ) + 1 - j)) * mesoT J j))) ^ q
            * ((Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
              * (∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j), g t ^ 2) ^ q) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hc0 : 0 ≤ Real.exp (2 * ((J : ℝ) + 1 - j)) := (Real.exp_pos _).le
        rw [← Real.mul_rpow hc0 (hW0 j),
          ← Real.mul_rpow (by have := mesoT_pos J j; positivity) (mul_nonneg hc0 (hW0 j))]
        exact rpow_two_mul_le_of_sq_le
          (mul_nonneg (by positivity) (mul_nonneg hc0 (hV0 j))) hq0.le (sq_window_le (hVW j))

/-- **The line integral, cut into its pieces, pathwise**: for a continuous even `g` with
`0 ≤ g ≤ U`, `σ ≤ ℓ⁻¹` and `0 < q ≤ ½`, `(σ∫_ℝ ρg)^{2q}` is at most the central, window and tail
pieces' bounds: the fold and the cut at `e^{-J}` and `1`, and subadditivity of `u ↦ u^{2q}`. -/
lemma rpow_lineAbs_le_pieces {g : ℝ → ℝ} (hgc : Continuous g) (hg0 : ∀ t, 0 ≤ g t) {U : ℝ}
    (hgU : ∀ t, g t ≤ U) (hgeven : ∀ t, g (-t) = g t) {σ ℓ q : ℝ} (hσ : 0 < σ)
    (hσℓ : σ ≤ ℓ⁻¹) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (J : ℕ) :
    (σ * ∫ t, (σ ^ 2 + t ^ 2)⁻¹ * g t) ^ (2 * q)
      ≤ (4 * Real.pi) ^ q
          * (ℓ⁻¹ * ∫ t in Set.Icc (-Real.exp (-(J : ℝ))) (Real.exp (-(J : ℝ))),
            (σ ^ 2 + t ^ 2)⁻¹ * g t ^ 2) ^ q
        + ∑ j ∈ Finset.Icc 1 J,
            (4 * (σ ^ 2 * (Real.exp (2 * ((J : ℝ) + 1 - j)) * mesoT J j))) ^ q
              * ((Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
                * (∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j), g t ^ 2) ^ q)
        + (8 * σ) ^ q * (ℓ⁻¹ * ∫ t in {t : ℝ | 1 < |t|}, (σ ^ 2 + t ^ 2)⁻¹ * g t ^ 2) ^ q := by
  have hw0 : 0 ≤ Real.exp (-(J : ℝ)) := (Real.exp_pos _).le
  have hw1 : Real.exp (-(J : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Nat.cast_nonneg J))
  have hρc : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun t => by positivity
  have hρ0 : ∀ t : ℝ, 0 ≤ (σ ^ 2 + t ^ 2)⁻¹ := fun t => by positivity
  have hρi : Integrable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ := integrable_inv_sq_add_sq hσ.ne'
  have hint : Integrable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ * g t := by
    refine Integrable.mono' (hρi.mul_const U) (hρc.mul hgc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hρ0 t) (hg0 t))]
    exact mul_le_mul_of_nonneg_left (hgU t) (hρ0 t)
  have hfold := integral_eq_two_mul_pieces_of_even hint
    (fun t => by simp only [neg_sq, hgeven]) hw0 hw1
  have hA := rpow_central_piece_le hgc hg0 hσ hσℓ hq0.le hw0 (ℓ := ℓ) (q := q)
  have hB := rpow_window_piece_le hgc hg0 hσ hq0 hq1 J
  have hC := rpow_tail_piece_le hgc hg0 hgU hσ hσℓ hq0.le (ℓ := ℓ)
  have ha0 : 0 ≤ ∫ t in Set.Ioc 0 (Real.exp (-(J : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ * g t :=
    setIntegral_nonneg measurableSet_Ioc fun t _ => mul_nonneg (hρ0 t) (hg0 t)
  have hb0 : 0 ≤ ∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1, (σ ^ 2 + t ^ 2)⁻¹ * g t :=
    setIntegral_nonneg measurableSet_Ioc fun t _ => mul_nonneg (hρ0 t) (hg0 t)
  have hc0 : 0 ≤ ∫ t in Set.Ioi 1, (σ ^ 2 + t ^ 2)⁻¹ * g t :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => mul_nonneg (hρ0 t) (hg0 t)
  rw [hfold]
  generalize (∫ t in Set.Ioc 0 (Real.exp (-(J : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ * g t) = a at hA ha0 ⊢
  generalize (∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1, (σ ^ 2 + t ^ 2)⁻¹ * g t) = b at hB hb0 ⊢
  generalize (∫ t in Set.Ioi 1, (σ ^ 2 + t ^ 2)⁻¹ * g t) = c at hC hc0 ⊢
  have e : σ * (2 * (a + b + c)) = 2 * σ * a + 2 * σ * b + 2 * σ * c := by ring
  rw [e]
  have h2q0 : (0 : ℝ) ≤ 2 * q := by linarith
  have h2q1 : 2 * q ≤ 1 := by linarith
  have h2σ : (0 : ℝ) ≤ 2 * σ := by positivity
  have h1 := Real.rpow_add_le_add_rpow
    (add_nonneg (mul_nonneg h2σ ha0) (mul_nonneg h2σ hb0)) (mul_nonneg h2σ hc0) h2q0 h2q1
  have h2 := Real.rpow_add_le_add_rpow (mul_nonneg h2σ ha0) (mul_nonneg h2σ hb0) h2q0 h2q1
  linarith

/-! ### On the paths of the Rademacher field -/

omit [MeasurableSpace Ω] in
/-- `‖F(½+σ+it)/(σ+it)‖² = (σ²+t²)⁻¹‖F(½+σ+it)‖²`, between the parametrisation of the line in
the central and tail bounds and `RMF.shiftLine`. -/
lemma normSq_randomEulerProduct_lineDiv_eq (f : Ω → ArithmeticFunction ℂ) (N : ℕ) (σ t : ℝ)
    (ω : Ω) :
    ‖randomEulerProduct f N ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      = (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct f N (shiftLine σ t) ω‖ ^ 2 := by
  have hs : (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I = shiftLine σ t := by
    rw [shiftLine]
    push_cast
    ring
  rw [hs, norm_div_ofReal_add_mul_I_sq]

/-- **The first-power line integral has integrable powers**: for a measurable weight `ρ ≥ 0`
integrable on `ℝ`, `a ≥ 0` and `r ≥ 0`, `ω ↦ (a∫_ℝ ρ|F_n(½+σ+it)|dt)^r` is measurable (Tonelli)
and bounded by `(aU∫ρ)^r`, `U` the envelope of `F_n`. -/
lemma integrable_rpow_integral_weight_norm {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) {ρ : ℝ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρi : Integrable ρ) {a r : ℝ} (ha : 0 ≤ a)
    (hr0 : 0 ≤ r) :
    Integrable (fun ω => (a * ∫ t, ρ t *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n (shiftLine σ t) ω‖)
        ^ r) μ := by
  haveI := hX.isProbabilityMeasure
  have hjoint : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) => ρ t *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
        (shiftLine σ t) ω‖) := by
    have h := measurable_randomEulerProduct_sqfree_uncurry (X := X)
      (fun p hp => hX.measurable p hp) (1 / 2 + σ) n
    exact (hρm.comp measurable_snd).mul h.norm
  have hmeas : Measurable fun ω => ∫ t, ρ t *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n (shiftLine σ t) ω‖ :=
    (hjoint.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have hI0 : ∀ ω, 0 ≤ ∫ t, ρ t *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n (shiftLine σ t) ω‖ :=
    fun ω => integral_nonneg fun t => mul_nonneg (hρ0 t) (norm_nonneg _)
  refine Integrable.mono' (integrable_const ((a * ((∏ p ∈ Nat.primesBelow n,
      (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) * ∫ t, ρ t)) ^ r))
    ((Real.continuous_rpow_const hr0).measurable.comp
      (measurable_const.mul hmeas)).aestronglyMeasurable ?_
  filter_upwards [ae_forall_norm_randomEulerProduct_shiftLine_le_rad hX n hσ] with ω hω
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (mul_nonneg ha (hI0 ω)) _)]
  refine Real.rpow_le_rpow (mul_nonneg ha (hI0 ω)) (mul_le_mul_of_nonneg_left ?_ ha) hr0
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun t => mul_nonneg (hρ0 t) (norm_nonneg _))
    (hρi.const_mul _) (Filter.Eventually.of_forall fun t => ?_)
  exact (mul_le_mul_of_nonneg_left (hω t) (hρ0 t)).trans_eq (mul_comm _ _)

/-- **The line integral, cut into its pieces, almost surely**: `RMF.rpow_lineAbs_le_pieces` at
`g(t) = |F_n(½+σ+it)|`, continuous, even (the coefficients are real) and below the envelope. -/
theorem ae_rpow_lineAbs_le {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    (n : ℕ) {σ ℓ q : ℝ} (hσ : 0 < σ) (hσℓ : σ ≤ ℓ⁻¹) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (J : ℕ) :
    ∀ᵐ ω ∂μ, (σ * ∫ t, (σ ^ 2 + t ^ 2)⁻¹
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
            (shiftLine σ t) ω‖) ^ (2 * q)
      ≤ (4 * Real.pi) ^ q
          * (ℓ⁻¹ * ∫ t in Set.Icc (-Real.exp (-(J : ℝ))) (Real.exp (-(J : ℝ))),
            (σ ^ 2 + t ^ 2)⁻¹
              * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
                (shiftLine σ t) ω‖ ^ 2) ^ q
        + ∑ j ∈ Finset.Icc 1 J,
            (4 * (σ ^ 2 * (Real.exp (2 * ((J : ℝ) + 1 - j)) * mesoT J j))) ^ q
              * ((Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
                * (∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j),
                  ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
                    (shiftLine σ t) ω‖ ^ 2) ^ q)
        + (8 * σ) ^ q * (ℓ⁻¹ * ∫ t in {t : ℝ | 1 < |t|}, (σ ^ 2 + t ^ 2)⁻¹
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
              (shiftLine σ t) ω‖ ^ 2) ^ q := by
  filter_upwards [ae_forall_norm_randomEulerProduct_shiftLine_neg hX n σ,
    ae_forall_norm_randomEulerProduct_shiftLine_le_rad hX n hσ.le] with ω hrefl henv
  exact rpow_lineAbs_le_pieces
    (g := fun t => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
      (shiftLine σ t) ω‖)
    (continuous_randomEulerProduct_sqfree_shiftLine n σ ω).norm (fun t => norm_nonneg _) henv
    hrefl hσ hσℓ hq0 hq1 J

/-- **The line integral from its three pieces, in expectation.**  Given bounds `B_a`, `B_j`,
`B_c` on the central window, the `j`-th weighted window and the tail, in the forms of
`RMF.exists_const_integral_rpow_centralRange_le_rademacher`, `RMF.mesoBlock_weighted_le_trivial`
and `RMF.exists_integral_rpow_eulerProductLine_tail_le`,
`E[(σ∫_ℝρ|F|)^{2q}] ≤ (4π)^qB_a + ∑_j(4σ²c_jT_j)^qB_j + (8σ)^qB_c`. -/
lemma integral_rpow_lineAbs_le_of_pieces {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {σ ℓ q : ℝ} (hσ : 0 < σ) (hσℓ : σ ≤ ℓ⁻¹)
    (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (J : ℕ) {Ba Bc : ℝ} {B : ℕ → ℝ}
    (ha : (∫ ω, (ℓ⁻¹ * ∫ t in Set.Icc (-Real.exp (-(J : ℝ))) (Real.exp (-(J : ℝ))),
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ) ≤ Ba)
    (hb : ∀ j ∈ Finset.Icc 1 J, (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
        * (∫ ω, (∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j),
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ) ≤ B j)
    (hc : (∫ ω, (ℓ⁻¹ * ∫ t in {t : ℝ | 1 < |t|},
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ) ≤ Bc) :
    (∫ ω, (σ * ∫ t, (σ ^ 2 + t ^ 2)⁻¹
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖) ^ (2 * q) ∂μ)
      ≤ (4 * Real.pi) ^ q * Ba
        + ∑ j ∈ Finset.Icc 1 J,
            (4 * (σ ^ 2 * (Real.exp (2 * ((J : ℝ) + 1 - j)) * mesoT J j))) ^ q * B j
        + (8 * σ) ^ q * Bc := by
  haveI := hX.isProbabilityMeasure
  have hℓ0 : 0 ≤ ℓ⁻¹ := hσ.le.trans hσℓ
  have hρm : Measurable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ := by fun_prop
  have hρ0 : ∀ t : ℝ, 0 ≤ (σ ^ 2 + t ^ 2)⁻¹ := fun t => by positivity
  have hρi : Integrable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ := integrable_inv_sq_add_sq hσ.ne'
  simp only [normSq_randomEulerProduct_lineDiv_eq] at ha hc
  have hIa := integrable_rpow_setIntegral_weight_normSq hX (y + 1) hσ.le
    (Set.Icc (-Real.exp (-(J : ℝ))) (Real.exp (-(J : ℝ)))) hρm hρ0 hρi.integrableOn hℓ0 hq0.le
  have hIc := integrable_rpow_setIntegral_weight_normSq hX (y + 1) hσ.le
    {t : ℝ | 1 < |t|} hρm hρ0 hρi.integrableOn hℓ0 hq0.le
  have hIw : ∀ j : ℕ, Integrable (fun ω =>
      (∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j),
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q) μ := by
    intro j
    have h := integrable_rpow_setIntegral_weight_normSq hX (y + 1) hσ.le
      (Set.Icc (mesoT J j / Real.exp 1) (mesoT J j)) (ρ := fun _ => (1 : ℝ)) measurable_const
      (fun _ => zero_le_one)
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      zero_le_one hq0.le
    simpa only [one_mul] using h
  have hfa : Integrable (fun ω => (4 * Real.pi) ^ q
      * (ℓ⁻¹ * ∫ t in Set.Icc (-Real.exp (-(J : ℝ))) (Real.exp (-(J : ℝ))),
        (σ ^ 2 + t ^ 2)⁻¹
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q) μ := hIa.const_mul _
  have hfb : Integrable (fun ω => ∑ j ∈ Finset.Icc 1 J,
      (4 * (σ ^ 2 * (Real.exp (2 * ((J : ℝ) + 1 - j)) * mesoT J j))) ^ q
        * ((Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
          * (∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j),
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (shiftLine σ t) ω‖ ^ 2) ^ q)) μ :=
    integrable_finsetSum _ fun j _ => ((hIw j).const_mul _).const_mul _
  have hfc : Integrable (fun ω => (8 * σ) ^ q * (ℓ⁻¹ * ∫ t in {t : ℝ | 1 < |t|},
      (σ ^ 2 + t ^ 2)⁻¹
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q) μ := hIc.const_mul _
  have hEa : (∫ ω, (4 * Real.pi) ^ q
      * (ℓ⁻¹ * ∫ t in Set.Icc (-Real.exp (-(J : ℝ))) (Real.exp (-(J : ℝ))),
        (σ ^ 2 + t ^ 2)⁻¹
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ) ≤ (4 * Real.pi) ^ q * Ba := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left ha (by positivity)
  have hEb : (∫ ω, ∑ j ∈ Finset.Icc 1 J,
      (4 * (σ ^ 2 * (Real.exp (2 * ((J : ℝ) + 1 - j)) * mesoT J j))) ^ q
        * ((Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
          * (∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j),
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (shiftLine σ t) ω‖ ^ 2) ^ q) ∂μ)
      ≤ ∑ j ∈ Finset.Icc 1 J,
          (4 * (σ ^ 2 * (Real.exp (2 * ((J : ℝ) + 1 - j)) * mesoT J j))) ^ q * B j := by
    rw [integral_finsetSum _ fun j _ => ((hIw j).const_mul _).const_mul _]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [integral_const_mul, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hb j hj) (Real.rpow_nonneg (by
      have := mesoT_pos J j
      positivity) _)
  have hEc : (∫ ω, (8 * σ) ^ q * (ℓ⁻¹ * ∫ t in {t : ℝ | 1 < |t|},
      (σ ^ 2 + t ^ 2)⁻¹
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ) ≤ (8 * σ) ^ q * Bc := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg
    (mul_nonneg hσ.le (integral_nonneg fun t => mul_nonneg (hρ0 t) (norm_nonneg _))) _)
    ((hfa.add hfb).add hfc) (ae_rpow_lineAbs_le hX (y + 1) hσ hσℓ hq0 hq1 J)).trans ?_
  exact integral_add_le (hfa.add hfb) hfc (integral_add_le hfa hfb hEa hEb) hEc

/-! ### The arithmetic of the three contributions -/

/-- `log x ≤ 2 log ⌊x⌋` for `x ≥ 3`, as `⌊x⌋² > (x - 1)² ≥ x`. -/
lemma log_le_two_mul_log_floor {x : ℝ} (hx : 3 ≤ x) : Real.log x ≤ 2 * Real.log ⌊x⌋₊ := by
  have hfl : x - 1 < (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  have hsq : x ≤ (⌊x⌋₊ : ℝ) ^ 2 := by
    nlinarith [mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ x - 1) hfl.le,
      mul_nonneg (by linarith : (0 : ℝ) ≤ x) (by linarith : (0 : ℝ) ≤ x - 3)]
  have h := Real.log_le_log (by linarith) hsq
  rw [Real.log_pow] at h
  push_cast at h
  exact h

/-- The central window's contribution: `(4π)^q·A((σℓ)⁻¹)^qℓ^{q(2q-1)} ≤ 16πA·L^{q(2q-1)}` at
`σ = L⁻¹`, for `ℓ ≤ L ≤ 2ℓ` and `0 < q ≤ ½`. -/
lemma lineAbs_central_le {L ℓ q A : ℝ} (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L) (hLℓ : L ≤ 2 * ℓ)
    (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (hA : 0 ≤ A) :
    (4 * Real.pi) ^ q * (A * ((L⁻¹ * ℓ)⁻¹) ^ q * ℓ ^ (q * (2 * q - 1)))
      ≤ 16 * Real.pi * A * L ^ (q * (2 * q - 1)) := by
  have hL : 0 < L := lt_of_lt_of_le hℓ hℓL
  have hq1' : q ≤ 1 := by linarith
  have h4π : (4 * Real.pi) ^ q ≤ 4 * Real.pi :=
    Real.rpow_le_self_of_one_le (by nlinarith [Real.pi_gt_three]) hq1'
  have hratio : (L⁻¹ * ℓ)⁻¹ = L / ℓ := by
    rw [mul_inv, inv_inv, div_eq_mul_inv]
  have hr1 : 1 ≤ L / ℓ := (one_le_div hℓ).2 hℓL
  have hr2 : L / ℓ ≤ 2 := (div_le_iff₀ hℓ).2 (by linarith)
  have hrq : ((L⁻¹ * ℓ)⁻¹) ^ q ≤ 2 := by
    rw [hratio]
    exact (Real.rpow_le_self_of_one_le hr1 hq1').trans hr2
  have he0 : q * (2 * q - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq0.le (by linarith)
  have he1 : -1 ≤ q * (2 * q - 1) := by nlinarith
  have hℓe : ℓ ^ (q * (2 * q - 1)) ≤ 2 * L ^ (q * (2 * q - 1)) := by
    have h1 : ℓ ^ (q * (2 * q - 1)) ≤ (L / 2) ^ (q * (2 * q - 1)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) he0
    have h2 : (L / 2) ^ (q * (2 * q - 1)) = L ^ (q * (2 * q - 1)) / 2 ^ (q * (2 * q - 1)) :=
      Real.div_rpow hL.le (by norm_num) _
    have h3 : (2 : ℝ) ^ (-1 : ℝ) ≤ 2 ^ (q * (2 * q - 1)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
    have h4 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by
      rw [Real.rpow_neg_one]
      norm_num
    have hLe : 0 < L ^ (q * (2 * q - 1)) := Real.rpow_pos_of_pos hL _
    have h2e : 0 < (2 : ℝ) ^ (q * (2 * q - 1)) := Real.rpow_pos_of_pos (by norm_num) _
    rw [h4] at h3
    rw [h2] at h1
    refine h1.trans ?_
    rw [div_le_iff₀ h2e]
    nlinarith [mul_le_mul_of_nonneg_left h3 hLe.le]
  have hrq0 : 0 ≤ ((L⁻¹ * ℓ)⁻¹) ^ q := Real.rpow_nonneg (by positivity) _
  have hℓe0 : 0 ≤ ℓ ^ (q * (2 * q - 1)) := Real.rpow_nonneg hℓ.le _
  calc (4 * Real.pi) ^ q * (A * ((L⁻¹ * ℓ)⁻¹) ^ q * ℓ ^ (q * (2 * q - 1)))
      ≤ (4 * Real.pi) * (A * 2 * (2 * L ^ (q * (2 * q - 1)))) := by
        refine mul_le_mul h4π ?_ (mul_nonneg (mul_nonneg hA hrq0) hℓe0) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hrq hA) hℓe hℓe0
          (mul_nonneg hA (by norm_num))
    _ = 16 * Real.pi * A * L ^ (q * (2 * q - 1)) := by ring

/-- One window's contribution, in closed form: at `σ = L⁻¹`, with `c_j = e^{2(J+1-j)}` and
`T_j = e^{j-J}`, `(4σ²c_jT_j)^q·KL^qe^{(j-J)q(1-2q)} = K(4e²)^qL^{-q}e^{(J-j)2q²}`. -/
lemma lineAbs_window_term_eq {L q K : ℝ} (hL : 0 < L) (J j : ℕ) :
    (4 * (L⁻¹ ^ 2 * (Real.exp (2 * ((J : ℝ) + 1 - j)) * mesoT J j))) ^ q
        * (K * L ^ q * Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) * 1)
      = K * ((4 * Real.exp 2) ^ q * (L ^ (-q) * Real.exp (((J : ℝ) - j) * (2 * q ^ 2)))) := by
  have hcT : 4 * (L⁻¹ ^ 2 * (Real.exp (2 * ((J : ℝ) + 1 - j)) * mesoT J j))
      = (4 * Real.exp 2) * (L⁻¹ ^ 2 * Real.exp ((J : ℝ) - j)) := by
    rw [mesoT, ← Real.exp_add,
      show (2 : ℝ) * ((J : ℝ) + 1 - j) + ((j : ℝ) - J) = 2 + ((J : ℝ) - j) by ring,
      Real.exp_add]
    ring
  have hLq : (L⁻¹ ^ 2) ^ q = L ^ (-(2 * q)) := by
    rw [inv_pow, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hL.le,
      Real.rpow_neg hL.le]
    norm_num
  have hL2 : L ^ (-(2 * q)) * L ^ q = L ^ (-q) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hE : Real.exp ((J : ℝ) - j) ^ q * Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q)))
      = Real.exp (((J : ℝ) - j) * (2 * q ^ 2)) := by
    rw [← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hcT, Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * Real.exp 2)
      (by positivity : (0 : ℝ) ≤ L⁻¹ ^ 2 * Real.exp ((J : ℝ) - j)),
    Real.mul_rpow (by positivity : (0 : ℝ) ≤ L⁻¹ ^ 2) (Real.exp_pos ((J : ℝ) - j)).le, hLq]
  calc (4 * Real.exp 2) ^ q * (L ^ (-(2 * q)) * Real.exp ((J : ℝ) - j) ^ q)
        * (K * L ^ q * Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) * 1)
      = K * ((4 * Real.exp 2) ^ q * ((L ^ (-(2 * q)) * L ^ q)
          * (Real.exp ((J : ℝ) - j) ^ q
            * Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q)))))) := by ring
    _ = K * ((4 * Real.exp 2) ^ q * (L ^ (-q) * Real.exp (((J : ℝ) - j) * (2 * q ^ 2)))) := by
        rw [hL2, hE]

/-- The windows' contribution: at `σ = L⁻¹` and when `e^{J-1} ≤ L`,
`∑_j(4σ²c_jT_j)^q·KL^qe^{(j-J)q(1-2q)} ≤ 4e²K(1 + q⁻²)L^{q(2q-1)}`: each window is
`K(4e²)^qL^{-q}e^{(J-j)2q²}` (`RMF.lineAbs_window_term_eq`), and `RMF.sum_exp_sub_mul_rev_le`
sums them to `≤ L^{2q²}(1 + (2q²)⁻¹)`. -/
lemma lineAbs_windows_le {L q K : ℝ} {J : ℕ} (hL : 0 < L) (hJL : Real.exp ((J : ℝ) - 1) ≤ L)
    (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (hK : 0 ≤ K) :
    ∑ j ∈ Finset.Icc 1 J, (4 * (L⁻¹ ^ 2 * (Real.exp (2 * ((J : ℝ) + 1 - j)) * mesoT J j))) ^ q
        * (K * L ^ q * Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) * 1)
      ≤ 4 * Real.exp 2 * K * (1 + (q ^ 2)⁻¹) * L ^ (q * (2 * q - 1)) := by
  have hα : 0 < 2 * q ^ 2 := by positivity
  rw [Finset.sum_congr rfl fun j _ => lineAbs_window_term_eq (K := K) (q := q) hL J j,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsum := sum_exp_sub_mul_rev_le hα J
  have h4 : (4 * Real.exp 2) ^ q ≤ 4 * Real.exp 2 :=
    Real.rpow_le_self_of_one_le (by nlinarith [Real.add_one_le_exp (2 : ℝ)]) (by linarith)
  have hexpJ : Real.exp (((J : ℝ) - 1) * (2 * q ^ 2)) ≤ L ^ (2 * q ^ 2) := by
    rw [Real.exp_mul]
    exact Real.rpow_le_rpow (Real.exp_pos _).le hJL hα.le
  have hinv : (2 * q ^ 2)⁻¹ ≤ (q ^ 2)⁻¹ :=
    (inv_le_inv₀ hα (by positivity)).2 (by nlinarith [sq_nonneg q])
  have hLe : L ^ (-q) * L ^ (2 * q ^ 2) = L ^ (q * (2 * q - 1)) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hLq0 : 0 ≤ L ^ (-q) := Real.rpow_nonneg hL.le _
  calc K * ((4 * Real.exp 2) ^ q * (L ^ (-q)
          * ∑ j ∈ Finset.Icc 1 J, Real.exp (((J : ℝ) - j) * (2 * q ^ 2))))
      ≤ K * ((4 * Real.exp 2) * (L ^ (-q) * (L ^ (2 * q ^ 2) * (1 + (q ^ 2)⁻¹)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul h4
          (mul_le_mul_of_nonneg_left ?_ hLq0) (mul_nonneg hLq0 (Finset.sum_nonneg fun j _ =>
            (Real.exp_pos _).le)) (by positivity)) hK
        exact hsum.trans (mul_le_mul hexpJ (by linarith) (by positivity)
          (Real.rpow_nonneg hL.le _))
    _ = 4 * Real.exp 2 * K * (1 + (q ^ 2)⁻¹) * (L ^ (-q) * L ^ (2 * q ^ 2)) := by ring
    _ = 4 * Real.exp 2 * K * (1 + (q ^ 2)⁻¹) * L ^ (q * (2 * q - 1)) := by rw [hLe]

/-- The tail's contribution: `(8σ)^q(C/1)^q ≤ max(1, 8C)·L^{q(2q-1)}` at `σ = L⁻¹`, `L ≥ 1`. -/
lemma lineAbs_tail_le {L q C : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (hC : 0 < C) :
    (8 * L⁻¹) ^ q * (C / 1) ^ q ≤ max 1 (8 * C) * L ^ (q * (2 * q - 1)) := by
  have hL0 : 0 < L := by linarith
  rw [div_one, ← Real.mul_rpow (by positivity) hC.le,
    show 8 * L⁻¹ * C = 8 * C * L⁻¹ by ring, Real.mul_rpow (by positivity) (by positivity),
    Real.inv_rpow hL0.le, ← Real.rpow_neg hL0.le]
  exact mul_le_mul (rpow_le_max_one (by positivity) hq0.le (by linarith))
    (Real.rpow_le_rpow_of_exponent_le hL (by nlinarith)) (Real.rpow_nonneg hL0.le _)
    (le_trans zero_le_one (le_max_left _ _))

/-- `av + buv + cv ≤ (a + b + c)uv` for `a, c, v ≥ 0` and `u ≥ 1`. -/
lemma add_three_le_mul {a b c u v : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hu : 1 ≤ u) (hv : 0 ≤ v) :
    a * v + b * u * v + c * v ≤ (a + b + c) * u * v := by
  nlinarith [mul_nonneg (mul_nonneg ha hv) (sub_nonneg.2 hu),
    mul_nonneg (mul_nonneg hc hv) (sub_nonneg.2 hu)]

/-! ### The line integral -/

/-- **The weighted line integral of `|F|`.**  With `C` independent of `X`, `μ`, `x` and `q`, for
`x ≥ 8` and `0 < q ≤ ½`, at `σ = 1/log x`,
`E[((log x)⁻¹∫_ℝ(σ²+t²)⁻¹|F_{⌊x⌋+1}(½+σ+it)|dt)^{2q}] ≤ C(1 + q⁻²)(log x)^{q(2q-1)}`:
`RMF.integral_rpow_lineAbs_le_of_pieces` at `J` from `RMF.exists_mesoRange_index`, with the
central window, the windows and the tail bounded by
`RMF.exists_const_integral_rpow_centralRange_le_rademacher`, `RMF.mesoBlock_weighted_le_trivial`
and `RMF.exists_integral_rpow_eulerProductLine_tail_le`. -/
theorem exists_const_integral_rpow_lineAbs_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ x q : ℝ, 8 ≤ x → 0 < q → q ≤ 1 / 2 →
          (∫ ω, ((Real.log x)⁻¹ * ∫ t : ℝ, ((Real.log x)⁻¹ ^ 2 + t ^ 2)⁻¹
              * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
                  (shiftLine (Real.log x)⁻¹ t) ω‖) ^ (2 * q) ∂μ)
            ≤ C * (1 + (q ^ 2)⁻¹) * Real.log x ^ (q * (2 * q - 1)) := by
  obtain ⟨A, hA, HA⟩ := exists_const_integral_rpow_centralRange_le_rademacher (Ω := Ω)
  obtain ⟨Ct, hCt, HT⟩ := exists_integral_rpow_eulerProductLine_tail_le
  refine ⟨16 * Real.pi * A
      + 4 * Real.exp 2 * (3 * Real.exp 2 * (Real.exp 143800 * Real.exp 7 * Real.exp 21))
      + max 1 (8 * Ct), by positivity, ?_⟩
  intro X μ hX x q hx8 hq0 hq1
  obtain ⟨J, -, hJw, hJle, -⟩ := exists_mesoRange_index hx8
  have hx3 : (3 : ℝ) ≤ x := by linarith
  have hL1 : 1 < Real.log x := one_lt_log_of_three_le hx3
  have hL0 : 0 < Real.log x := by linarith
  have hy3 : 3 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx3)
  have hy3R : (3 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hy3
  have hℓ0 : 0 < Real.log ⌊x⌋₊ := by linarith [one_lt_log_of_three_le hy3R]
  have hℓL : Real.log ⌊x⌋₊ ≤ Real.log x :=
    Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have hσ : 0 < (Real.log x)⁻¹ := inv_pos.2 hL0
  have hσℓ : (Real.log x)⁻¹ ≤ (Real.log ⌊x⌋₊)⁻¹ := inv_anti₀ hℓ0 hℓL
  have hσy : (Real.log x)⁻¹ * Real.log ⌊x⌋₊ ≤ 1 := by
    rw [inv_mul_le_iff₀ hL0, mul_one]
    exact hℓL
  have hw : Real.exp (-(J : ℝ)) * Real.log ((⌊x⌋₊ : ℝ) + 1) ≤ 2 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) hJw
    exact Real.log_le_log (by positivity)
      (by linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ x)])
  have hJexp : Real.exp ((J : ℝ) - 1) ≤ Real.log x := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpos : 0 < Real.log x - Real.log 2 := by
      have := Real.log_two_lt_d9
      linarith
    calc Real.exp ((J : ℝ) - 1) ≤ Real.exp (Real.log (Real.log x - Real.log 2)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = Real.log x - Real.log 2 := Real.exp_log hpos
      _ ≤ Real.log x := by linarith
  refine (integral_rpow_lineAbs_le_of_pieces hX ⌊x⌋₊ hσ hσℓ hq0 hq1 J
    (HA X μ hX (Real.log x)⁻¹ q (Real.exp (-(J : ℝ))) ⌊x⌋₊ (by omega) hσ hσy (Real.exp_pos _)
      hw hq0.le (by linarith))
    (fun j hj => mesoBlock_weighted_le_trivial hX hx3 hσ.le
      (by rw [inv_mul_cancel₀ hL0.ne']) hq0.le hq1 (Finset.mem_Icc.1 hj).1
      (Finset.mem_Icc.1 hj).2 hJle)
    (HT Ω X μ hX q hq0 (by linarith) ⌊x⌋₊ (by omega) (Real.log x)⁻¹ 1 hσ one_pos)).trans ?_
  have h1 := lineAbs_central_le hℓ0 hℓL (log_le_two_mul_log_floor hx3) hq0 hq1 hA.le
  have h2 := lineAbs_windows_le hL0 hJexp hq0 hq1
    (K := 3 * Real.exp 2 * (Real.exp 143800 * Real.exp 7 * Real.exp 21)) (by positivity)
  have h3 := lineAbs_tail_le hL1.le hq0 hq1 hCt
  refine le_trans (add_le_add (add_le_add h1 h2) h3) ?_
  exact add_three_le_mul (by positivity) (le_trans zero_le_one (le_max_left _ _))
    (le_add_of_nonneg_right (by positivity)) (Real.rpow_nonneg hL0.le _)

end RMF
