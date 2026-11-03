/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.LowerWindow
import RMF.Weighted.EulerLine
import RMF.Weighted.FarRange

/-!
# The weighted sum's lower bound in terms of random Euler products

Gerspach's Proposition 6 (Gerspach, *Low pseudomoments of the Riemann zeta function and its
powers*, arXiv:1909.10224), for the Rademacher weighted sum `S(x) = ∑_{n≤x} f(n)/√n` — the case
`α = 1` of his `d_α`-weighted pseudomoments, with the Rademacher function in place of the
Steinhaus one:

`E|S(x)|^{2q} ≥ c (log x)^{-q} E[(∫_{|t|<1} |F(½ + 2V/log x + it)|² dt)^q]`
`    - C e^{-Vq} (log x)^{-q} E[(∫_ℝ |F(½ + V/log x + it)|² / |V/log x + it|² dt)^q]`
`    - C (log x)^{-q}`,

for `0 < q ≤ ½`, any `V > 0` and `x ≥ x₀` with `log x ≥ 3V + 3`, with `F` the Euler product over
the primes up to `x` and `c`, `C`, `x₀` independent of `V`, `x` and `q`.

## The deviation from Gerspach's statement

Gerspach's statement ends in `- O(1)` and is for `0 < q < 2(α-1)/α²`, a range that is empty at
`α = 1`.  At `α = 1` an `O(1)` loss would make the bound say nothing: the main term is itself
`O(1)`, since by Jensen `E[(∫_{|t|<1} |F|²)^q] ≤ (E ∫_{|t|<1} |F|²)^q ≪ (log x)^q`.  So the error
is kept explicit.  It is `C (log x)^{-q}`, the smoothing error at window width `1/log x`, whose
mean is at most `16/log x` (`RMF.integral_sum_discrepancy_le_weighted`).

## The chain

* Steps L1–L3, `RMF.khintchine_rough_weighted`: symmetrisation and Khintchine,
  `E|S|^{2q} ≥ 2^{2q-1}3^{-(1-q)} E[(∑_{√x<p≤x} p^{-1}|S(x/p)|²)^q]`;
* steps L4–L9, `RMF.meanSquare_le_sum_weighted`: smoothing and the prime windows, down to
  `(8 log x)^{-q} E[M^q] - (16/log x)^q` with `M = ∫_1^{√x/(1+1/log x)} |S(z)|² dz/z`;
* Parseval, `RMF.weightedMeanSquare_ge_line`: `M ≥ (4π)⁻¹ (main window) - π⁻¹ e^{-V} (damped)`.
  The shift `u^{-2·2V/log x}` costs nothing on `(1, √x]` (`RMF.setIntegral_Ioc_div_rpow_le`), and
  the tail of the Parseval integral past `w = √x/(1+1/log x)` is at most `w^{-2V/log x} ≤ 2e^{-V}`
  times the Parseval integral at the smaller shift `V/log x`
  (`RMF.setIntegral_Ioi_le_Ioc_add_mul`, `RMF.rpow_neg_sqrt_div_le`).  The main window is read
  off the line integral where `|σ + it|² ≤ 2` (`RMF.half_setIntegral_Ioo_le_integral_div`), so no
  translation in law is used — the Rademacher law has none.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The smooth sum up to `⌊x⌋` -/

omit [MeasurableSpace Ω] in
/-- Up to `N`, every number is `(N+1)`-smooth, so the smooth sum is the whole weighted sum. -/
lemma smoothWeightedSum_eq_weightedRademacherSum_of_le (f : Ω → ArithmeticFunction ℂ)
    {N : ℕ} {t : ℝ} (ht : t ≤ N) (ω : Ω) :
    smoothWeightedSum f N t ω = weightedRademacherSum f t ω := by
  rw [smoothWeightedSum, weightedRademacherSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
  have hkt : k ≤ ⌊t⌋₊ := (Finset.mem_Icc.1 hk).2
  have htN : ⌊t⌋₊ ≤ N := by
    rcases le_or_gt t 0 with h | h
    · rw [Nat.floor_of_nonpos h]
      exact Nat.zero_le _
    · exact Nat.floor_le_of_le ht
  rw [if_pos (Nat.mem_smoothNumbers_of_lt (by omega) (by omega))]

/-- `1 ≤ √x/(1+1/log x)` for `x ≥ 4`. -/
lemma one_le_sqrt_div {x : ℝ} (hx4 : 4 ≤ x) : 1 ≤ Real.sqrt x / (1 + 1 / Real.log x) := by
  obtain ⟨-, -, hsq, hr2, hr1⟩ := log_scale_facts hx4
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- `√x/(1+1/log x) ≤ √x ≤ x/2 ≤ ⌊x⌋` for `x ≥ 4`. -/
lemma sqrt_div_le_floor {x : ℝ} (hx4 : 4 ≤ x) :
    Real.sqrt x / (1 + 1 / Real.log x) ≤ (⌊x⌋₊ : ℝ) := by
  obtain ⟨hx0, -, hsq, -, hr1⟩ := log_scale_facts hx4
  have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have h2 := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg x)
  have hfl := Nat.lt_floor_add_one x
  have hw := div_le_self (Real.sqrt_nonneg x) hr1
  linarith

omit [MeasurableSpace Ω] in
/-- **`M` is an integral of the smooth sum.**  Up to `√x/(1+1/log x) ≤ ⌊x⌋`, the weighted sum is
its own `⌊x⌋`-smooth part, which is what Parseval is stated for. -/
lemma weightedMeanSquare_eq_setIntegral_smooth (f : Ω → ArithmeticFunction ℂ) {x : ℝ}
    (hx4 : 4 ≤ x) (ω : Ω) :
    weightedMeanSquare f x ω = ∫ u in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
      ‖smoothWeightedSum f ⌊x⌋₊ u ω‖ ^ 2 / u := by
  have hwN := sqrt_div_le_floor hx4
  rw [weightedMeanSquare]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  simp only [smoothWeightedSum_eq_weightedRademacherSum_of_le f (le_trans hu.2 hwN) ω]

/-! ### Parseval, cut at `1` and `w` -/

/-- **The shift costs nothing on `(1, w]`.**  There `u^{1+2σ} ≥ u`, so the Parseval integrand is
at most `|A(u)|²/u`; the latter is integrable on `(1, w]` because `u^{2σ} ≤ w^{2σ}` there. -/
lemma setIntegral_Ioc_div_rpow_le {A : ℝ → ℂ} (hA : Measurable A) {w σ : ℝ} (hσ : 0 ≤ σ)
    (hI : IntegrableOn (fun u => ‖A u‖ ^ 2 / u ^ (1 + 2 * σ)) (Set.Ioc 1 w)) :
    (∫ u in Set.Ioc 1 w, ‖A u‖ ^ 2 / u ^ (1 + 2 * σ)) ≤ ∫ u in Set.Ioc 1 w, ‖A u‖ ^ 2 / u := by
  have hIu : IntegrableOn (fun u => ‖A u‖ ^ 2 / u) (Set.Ioc 1 w) := by
    refine Integrable.mono' (hI.const_mul (w ^ (2 * σ)))
      ((hA.norm.pow_const 2).div measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 < u := lt_trans one_pos hu.1
    have hpos : 0 < u ^ (2 * σ) := Real.rpow_pos_of_pos hu0 _
    have hmono : u ^ (2 * σ) ≤ w ^ (2 * σ) := Real.rpow_le_rpow hu0.le hu.2 (by linarith)
    have hsplit : u ^ (1 + 2 * σ) = u ^ (2 * σ) * u := by
      rw [Real.rpow_add hu0, Real.rpow_one, mul_comm]
    have hB : 0 ≤ ‖A u‖ ^ 2 / u ^ (1 + 2 * σ) :=
      div_nonneg (sq_nonneg _) (Real.rpow_nonneg hu0.le _)
    have heq : ‖A u‖ ^ 2 / u = u ^ (2 * σ) * (‖A u‖ ^ 2 / u ^ (1 + 2 * σ)) := by
      rw [hsplit, mul_div_assoc', mul_div_mul_left _ _ hpos.ne']
    change ‖‖A u‖ ^ 2 / u‖ ≤ w ^ (2 * σ) * (‖A u‖ ^ 2 / u ^ (1 + 2 * σ))
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hu0.le), heq]
    exact mul_le_mul_of_nonneg_right hmono hB
  refine setIntegral_mono_on hI hIu measurableSet_Ioc fun u hu => ?_
  have hu0 : 0 < u := lt_trans one_pos hu.1
  have hpow : u ≤ u ^ (1 + 2 * σ) := by
    calc u = u ^ (1 : ℝ) := (Real.rpow_one u).symm
      _ ≤ u ^ (1 + 2 * σ) := Real.rpow_le_rpow_of_exponent_le hu.1.le (by linarith)
  exact div_le_div_of_nonneg_left (sq_nonneg _) hu0 hpow

/-- **The damping, pointwise.**  For `u ≥ w > 0` and `σ₂ ≤ σ₁`,
`a/u^{1+2σ₁} ≤ w^{-2(σ₁-σ₂)} · a/u^{1+2σ₂}`. -/
lemma div_rpow_le_mul_div_rpow {a u w σ₁ σ₂ : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hwu : w ≤ u)
    (hσ : σ₂ ≤ σ₁) :
    a / u ^ (1 + 2 * σ₁) ≤ w ^ (-(2 * (σ₁ - σ₂))) * (a / u ^ (1 + 2 * σ₂)) := by
  have hu : 0 < u := lt_of_lt_of_le hw hwu
  have hsplit : u ^ (1 + 2 * σ₁) = u ^ (1 + 2 * σ₂) * u ^ (2 * (σ₁ - σ₂)) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  have hmono : w ^ (2 * (σ₁ - σ₂)) ≤ u ^ (2 * (σ₁ - σ₂)) :=
    Real.rpow_le_rpow hw.le hwu (by linarith)
  have hw0 : 0 < w ^ (2 * (σ₁ - σ₂)) := Real.rpow_pos_of_pos hw _
  rw [hsplit, ← div_div, div_eq_inv_mul _ (u ^ (2 * (σ₁ - σ₂))), Real.rpow_neg hw.le]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hw0 hmono)
    (div_nonneg ha (Real.rpow_nonneg hu.le _))

/-- **Parseval's integral at `σ₁`, cut at `w`.**  `A` vanishes below `1`, and past `w` the weight
`u^{-(1+2σ₁)}` is at most `w^{-2(σ₁-σ₂)}` times `u^{-(1+2σ₂)}`:

`∫_0^∞ |A|²/u^{1+2σ₁} ≤ ∫_1^w |A|²/u^{1+2σ₁} + w^{-2(σ₁-σ₂)} ∫_0^∞ |A|²/u^{1+2σ₂}`. -/
lemma setIntegral_Ioi_le_Ioc_add_mul {A : ℝ → ℂ} (hA1 : ∀ u, u < 1 → A u = 0) {w σ₁ σ₂ : ℝ}
    (hw1 : 1 ≤ w) (hσ : σ₂ ≤ σ₁)
    (hI₁ : IntegrableOn (fun u => ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₁)) (Set.Ioi 0))
    (hI₂ : IntegrableOn (fun u => ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₂)) (Set.Ioi 0)) :
    (∫ u in Set.Ioi (0 : ℝ), ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₁))
      ≤ (∫ u in Set.Ioc 1 w, ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₁))
        + w ^ (-(2 * (σ₁ - σ₂))) * ∫ u in Set.Ioi (0 : ℝ), ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₂) := by
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw1
  have hIa : IntegrableOn (fun u => ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₁)) (Set.Ioc 0 1) :=
    hI₁.mono_set Set.Ioc_subset_Ioi_self
  have hIb : IntegrableOn (fun u => ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₁)) (Set.Ioi 1) :=
    hI₁.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have hIc : IntegrableOn (fun u => ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₁)) (Set.Ioc 1 w) :=
    hIb.mono_set Set.Ioc_subset_Ioi_self
  have hId : IntegrableOn (fun u => ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₁)) (Set.Ioi w) :=
    hIb.mono_set (Set.Ioi_subset_Ioi hw1)
  have hIw : IntegrableOn (fun u => ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₂)) (Set.Ioi w) :=
    hI₂.mono_set (Set.Ioi_subset_Ioi hw0.le)
  -- `∫_{(0,∞)} = ∫_{(0,1]} + ∫_{(1,w]} + ∫_{(w,∞)}`, the first vanishing
  have h01 := setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIa hIb
  have h1w := setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIc hId
  rw [Set.Ioc_union_Ioi_eq_Ioi zero_le_one] at h01
  rw [Set.Ioc_union_Ioi_eq_Ioi hw1] at h1w
  have hae : (Set.Ioo (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] Set.Ioc 0 1 := Ioo_ae_eq_Ioc
  have hzero : (∫ u in Set.Ioc (0 : ℝ) 1, ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₁)) = 0 := by
    rw [setIntegral_congr_set hae.symm]
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    simp [hA1 u hu.2]
  -- the tail
  have htail : (∫ u in Set.Ioi w, ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₁))
      ≤ w ^ (-(2 * (σ₁ - σ₂))) * ∫ u in Set.Ioi (0 : ℝ), ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₂) := by
    calc (∫ u in Set.Ioi w, ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₁))
        ≤ ∫ u in Set.Ioi w, w ^ (-(2 * (σ₁ - σ₂))) * (‖A u‖ ^ 2 / u ^ (1 + 2 * σ₂)) :=
          setIntegral_mono_on hId (hIw.const_mul _) measurableSet_Ioi fun u hu =>
            div_rpow_le_mul_div_rpow (sq_nonneg _) hw0 (le_of_lt hu) hσ
      _ = w ^ (-(2 * (σ₁ - σ₂))) * ∫ u in Set.Ioi w, ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₂) :=
          integral_const_mul _ _
      _ ≤ w ^ (-(2 * (σ₁ - σ₂))) * ∫ u in Set.Ioi (0 : ℝ), ‖A u‖ ^ 2 / u ^ (1 + 2 * σ₂) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hw0.le _)
          exact setIntegral_mono_set hI₂
            (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu =>
              div_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hu) _))
            (Filter.Eventually.of_forall fun u hu => lt_trans hw0 hu)
  rw [h01, hzero, zero_add, h1w]
  linarith

/-- **The main window.**  On `|t| < 1` and for `0 < σ ≤ 1`, `|σ + it|² ≤ 2`, so the line integral
against `|σ + it|⁻²` is at least half the unweighted integral over the window. -/
lemma half_setIntegral_Ioo_le_integral_div {F : ℝ → ℂ} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hint : Integrable fun t : ℝ => ‖F t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) :
    (1 / 2 : ℝ) * (∫ t in Set.Ioo (-1 : ℝ) 1, ‖F t‖ ^ 2)
      ≤ ∫ t : ℝ, ‖F t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  rw [← integral_const_mul]
  refine le_trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun t => by positivity) hint.integrableOn ?_)
    (setIntegral_le_integral hint (Filter.Eventually.of_forall fun t => by positivity))
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hz : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have hz0 : 0 < σ ^ 2 + t ^ 2 := by positivity
  have ht2 : t ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one t).2 (abs_le.2 ⟨ht.1.le, ht.2.le⟩)
  have hs2 : σ ^ 2 ≤ 1 := pow_le_one₀ hσ0.le hσ1
  rw [norm_div, div_pow, hz]
  calc 1 / 2 * ‖F t‖ ^ 2 = ‖F t‖ ^ 2 / 2 := by ring
    _ ≤ ‖F t‖ ^ 2 / (σ ^ 2 + t ^ 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hz0 (by linarith)

omit [MeasurableSpace Ω] in
/-- `RMF.integrable_line_div_sq` with the abscissa written `½ + σ`, as Parseval produces it. -/
lemma integrable_line_div_sq_half_add {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} {σ : ℝ} (hσ : 0 < σ)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    Integrable fun t : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  have hc : ∀ t : ℝ, (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I := fun t => by push_cast; ring
  have h := integrable_line_div_sq (X := X) (N := N) (c := 1 / 2 + σ) (by linarith) hσ hω
  simp_rw [hc] at h
  exact h

/-- **The damping factor.**  With `w = √x/(1+1/log x)` and `log x ≥ 3V + 3`,
`w^{-2V/log x} ≤ 2e^{-V}`. -/
lemma rpow_neg_sqrt_div_le {x V : ℝ} (hV : 0 < V) (hx0 : 0 < x)
    (hx : 3 * V + 3 ≤ Real.log x) :
    (Real.sqrt x / (1 + 1 / Real.log x)) ^ (-(2 * (2 * V / Real.log x - V / Real.log x)))
      ≤ 2 * Real.exp (-V) := by
  have hlog0 : 0 < Real.log x := by linarith
  have hr0 : 0 < 1 + 1 / Real.log x := by positivity
  have hsq0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hw0 : 0 < Real.sqrt x / (1 + 1 / Real.log x) := div_pos hsq0 hr0
  have hexp : -(2 * (2 * V / Real.log x - V / Real.log x)) = -(2 * V / Real.log x) := by ring
  rw [hexp, Real.rpow_def_of_pos hw0]
  have hlogw : Real.log (Real.sqrt x / (1 + 1 / Real.log x))
      = Real.log x / 2 - Real.log (1 + 1 / Real.log x) := by
    rw [Real.log_div hsq0.ne' hr0.ne', Real.log_sqrt hx0.le]
  have hlog1p : Real.log (1 + 1 / Real.log x) ≤ 1 / Real.log x := by
    have := Real.log_le_sub_one_of_pos hr0
    linarith
  have hcoef : 0 ≤ 2 * V / Real.log x := by positivity
  have hbound : Real.log (Real.sqrt x / (1 + 1 / Real.log x)) * -(2 * V / Real.log x)
      ≤ -V + Real.log 2 := by
    rw [hlogw]
    have h1 : (Real.log x / 2 - Real.log (1 + 1 / Real.log x)) * -(2 * V / Real.log x)
        ≤ (Real.log x / 2 - 1 / Real.log x) * -(2 * V / Real.log x) := by
      have := mul_le_mul_of_nonneg_right hlog1p hcoef
      nlinarith
    have h2 : (Real.log x / 2 - 1 / Real.log x) * -(2 * V / Real.log x)
        = -V + 2 * V / Real.log x ^ 2 := by
      field_simp
      ring
    have h3 : 2 * V / Real.log x ^ 2 ≤ Real.log 2 := by
      have hl2 : (0.69 : ℝ) < Real.log 2 := by
        have := Real.log_two_gt_d9
        linarith
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  calc Real.exp (Real.log (Real.sqrt x / (1 + 1 / Real.log x)) * -(2 * V / Real.log x))
      ≤ Real.exp (-V + Real.log 2) := Real.exp_le_exp.2 hbound
    _ = 2 * Real.exp (-V) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
      ring

/-- The arithmetic of the Parseval step, main term kept whole: from `I ≤ M`,
`(2π)⁻¹J₁ ≤ I + d·(2π)⁻¹J₂` and `d ≤ 2e^{-V}`, `(2π)⁻¹ J₁ - π⁻¹e^{-V} J₂ ≤ M`. -/
lemma parseval_assembly_full {M I J₁ J₂ d V : ℝ} (hb : I ≤ M)
    (hsplit : (2 * Real.pi)⁻¹ * J₁ ≤ I + d * ((2 * Real.pi)⁻¹ * J₂))
    (hd : d ≤ 2 * Real.exp (-V)) (hJ₂ : 0 ≤ J₂) :
    (2 * Real.pi)⁻¹ * J₁ - Real.pi⁻¹ * Real.exp (-V) * J₂ ≤ M := by
  have hπ : 0 < (2 * Real.pi)⁻¹ := inv_pos.2 (by positivity)
  have h2 : d * ((2 * Real.pi)⁻¹ * J₂) ≤ 2 * Real.exp (-V) * ((2 * Real.pi)⁻¹ * J₂) :=
    mul_le_mul_of_nonneg_right hd (mul_nonneg hπ.le hJ₂)
  have e2 : 2 * Real.exp (-V) * ((2 * Real.pi)⁻¹ * J₂) = Real.pi⁻¹ * Real.exp (-V) * J₂ := by
    field_simp
  linarith

/-- Halving a main term that is at most `2J₁`: from `(2π)⁻¹J₁ - E ≤ M` and `W/2 ≤ J₁`,
`(4π)⁻¹W - E ≤ M`. -/
lemma quarter_sub_le_of_half_sub_le {M W J₁ E : ℝ}
    (hfull : (2 * Real.pi)⁻¹ * J₁ - E ≤ M) (hwin : 1 / 2 * W ≤ J₁) :
    (4 * Real.pi)⁻¹ * W - E ≤ M := by
  have hπ : 0 < (2 * Real.pi)⁻¹ := inv_pos.2 (by positivity)
  have h1 := mul_le_mul_of_nonneg_left hwin hπ.le
  have e1 : (2 * Real.pi)⁻¹ * (1 / 2 * W) = (4 * Real.pi)⁻¹ * W := by ring
  linarith

/-- A nonnegative main term may always be weakened from `(2π)⁻¹` to `(4π)⁻¹`. -/
lemma quarter_sub_le_half_sub {J E : ℝ} (hJ : 0 ≤ J) :
    (4 * Real.pi)⁻¹ * J - E ≤ (2 * Real.pi)⁻¹ * J - E := by
  have h : (4 * Real.pi)⁻¹ ≤ (2 * Real.pi)⁻¹ :=
    inv_anti₀ (by positivity) (by linarith [Real.pi_pos])
  nlinarith

omit [MeasurableSpace Ω] in
/-- **Parseval for the weighted mean square, the weight kept.**  For `V > 0`, `x ≥ 4` and
`log x ≥ 3V + 3`, at every `ω`, `M ≥ (2π)⁻¹ ∫_ℝ |F(½+2V/log x+it)|²/|2V/log x+it|² dt
- π⁻¹ e^{-V} ∫_ℝ |F(½+V/log x+it)|²/|V/log x+it|² dt`, `M = RMF.weightedMeanSquare`, `F` over the
primes up to `x`: the main term of Proposition 4.3 of the paper, whose weight `|σ+it|^{-2}` lets
every scale `|t| ≍ T` contribute.  `RMF.weightedMeanSquare_ge_line` keeps only the window
`|t| < 1`. -/
theorem weightedMeanSquare_ge_line_full {X : ℕ → Ω → ℂ} {x V : ℝ} (hV : 0 < V)
    (hx : 3 * V + 3 ≤ Real.log x) (hx4 : 4 ≤ x) (ω : Ω) :
    (2 * Real.pi)⁻¹ * (∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
            ((1 / 2 : ℂ) + ((2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
          / (((2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      - Real.pi⁻¹ * Real.exp (-V) * (∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
            ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
          / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ weightedMeanSquare (fun ω => squarefreeExtension fun p => X p ω) x ω := by
  obtain ⟨hx0, hlog, -, -, -⟩ := log_scale_facts hx4
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hσ₁0 : 0 < 2 * V / Real.log x := div_pos (by linarith) hlog0
  have hσ₂0 : 0 < V / Real.log x := div_pos hV hlog0
  have hσ₂₁ : V / Real.log x ≤ 2 * V / Real.log x :=
    div_le_div_of_nonneg_right (by linarith) hlog0.le
  have hM := weightedMeanSquare_eq_setIntegral_smooth
    (fun ω => squarefreeExtension fun p => X p ω) hx4 ω
  have hb := setIntegral_Ioc_div_rpow_le (w := Real.sqrt x / (1 + 1 / Real.log x))
    (measurable_smoothWeightedSum_truncation (fun ω => squarefreeExtension fun p => X p ω)
      ⌊x⌋₊ ω) hσ₁0.le
    ((integrableOn_normSq_smoothWeightedSum (X := X) ⌊x⌋₊ hσ₁0 ω).mono_set
      (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi zero_le_one)))
  have hsplit := setIntegral_Ioi_le_Ioc_add_mul
    (fun u hu => smoothWeightedSum_eq_zero_of_lt_one
      (fun ω => squarefreeExtension fun p => X p ω) ⌊x⌋₊ hu ω)
    (one_le_sqrt_div hx4) hσ₂₁
    (integrableOn_normSq_smoothWeightedSum (X := X) ⌊x⌋₊ hσ₁0 ω)
    (integrableOn_normSq_smoothWeightedSum (X := X) ⌊x⌋₊ hσ₂0 ω)
  rw [integral_normSq_smoothWeightedSum_eq_line ⌊x⌋₊ hσ₁0 ω,
    integral_normSq_smoothWeightedSum_eq_line ⌊x⌋₊ hσ₂0 ω] at hsplit
  exact parseval_assembly_full (hb.trans_eq hM.symm) hsplit (rpow_neg_sqrt_div_le hV hx0 hx)
    (integral_nonneg fun t => sq_nonneg _)

omit [MeasurableSpace Ω] in
/-- **Parseval for the weighted mean square, with the two shifts.**  Wherever the values at the
primes up to `x` are bounded by one, for `V > 0`, `x ≥ 4` and `log x ≥ 3V + 3`,
`M ≥ (4π)⁻¹ ∫_{|t|<1} |F(½+2V/log x+it)|² dt - π⁻¹ e^{-V} ∫_ℝ |F(½+V/log x+it)|²/|V/log x+it|² dt`,
with `M = RMF.weightedMeanSquare` and `F` the Euler product over the primes up to `x`.
`RMF.weightedMeanSquare_ge_line_full` with the line integral cut down to the window. -/
theorem weightedMeanSquare_ge_line {X : ℕ → Ω → ℂ} {x V : ℝ} (hV : 0 < V)
    (hx : 3 * V + 3 ≤ Real.log x) (hx4 : 4 ≤ x) {ω : Ω}
    (hω : ∀ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), ‖X p ω‖ ≤ 1) :
    (4 * Real.pi)⁻¹ * (∫ t in Set.Ioo (-1 : ℝ) 1,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
          ((1 / 2 : ℂ) + ((2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2)
      - Real.pi⁻¹ * Real.exp (-V) * (∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
            ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
          / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ weightedMeanSquare (fun ω => squarefreeExtension fun p => X p ω) x ω := by
  obtain ⟨-, hlog, -, -, -⟩ := log_scale_facts hx4
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hσ₁0 : 0 < 2 * V / Real.log x := div_pos (by linarith) hlog0
  have hσ₁1 : 2 * V / Real.log x ≤ 1 := (div_le_one hlog0).2 (by linarith)
  exact quarter_sub_le_of_half_sub_le (weightedMeanSquare_ge_line_full hV hx hx4 ω)
    (half_setIntegral_Ioo_le_integral_div hσ₁0 hσ₁1
      (integrable_line_div_sq_half_add (X := X) (N := ⌊x⌋₊ + 1) hσ₁0 hω))

/-! ### Integrability of the three moments -/

/-- **`M` is integrable**: its `z`-integrand is bounded on `Ω × (1, w]`. -/
lemma integrable_weightedMeanSquare {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsRademacherPrimeValues X μ) (x : ℝ) :
    Integrable (fun ω =>
      weightedMeanSquare (fun ω => squarefreeExtension fun p => X p ω) x ω) μ := by
  refine (integrable_weightedMeanSquare_prod hX
    (Real.sqrt x / (1 + 1 / Real.log x))).integral_prod_left.congr
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Function.uncurry_apply_pair, weightedMeanSquare, weightedRademacherSum_eq_randomSum]

/-- **`J^q` is integrable**, `J` the damped line integral: `RMF.integrable_rpow_eulerProductLine`
without its normalisation `(log y)⁻¹`, which is harmless once `y ≥ 2`. -/
lemma integrable_rpow_eulerProductLine_of_two_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {y : ℕ} (hy : 2 ≤ y) {σ : ℝ}
    (hσ : 0 < σ) {q : ℝ} (hq0 : 0 ≤ q) :
    Integrable (fun ω => (∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q) μ := by
  have hlog : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have key : ∀ J : ℝ, 0 ≤ J → Real.log y ^ q * ((Real.log y)⁻¹ * J) ^ q = J ^ q :=
    fun J hJ => by
      rw [Real.mul_rpow (inv_nonneg.2 hlog.le) hJ, Real.inv_rpow hlog.le,
        mul_inv_cancel_left₀ (Real.rpow_pos_of_pos hlog q).ne']
  exact ((integrable_rpow_eulerProductLine hX y hσ hq0).const_mul (Real.log y ^ q)).congr
    (Filter.Eventually.of_forall fun ω => key _ (integral_nonneg fun t => sq_nonneg _))

/-- **Integrating a lower bound at the `q`-th power.**  From `aW - bJ ≤ M` almost surely,
`a^q E[W^q] - b^q E[J^q] ≤ E[M^q]`, for nonnegative `a, b, W, J, M` and `0 ≤ q ≤ 1`.  No
integrability of `W^q` is needed: without it `E[W^q] = 0` and the bound is trivial. -/
lemma integral_rpow_sub_le_of_ae {μ : Measure Ω} {W J M : Ω → ℝ} {a b q : ℝ}
    (h : ∀ᵐ ω ∂μ, a * W ω - b * J ω ≤ M ω) (ha : 0 ≤ a) (hb : 0 ≤ b) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hW0 : ∀ ω, 0 ≤ W ω) (hJ0 : ∀ ω, 0 ≤ J ω) (hM0 : ∀ ω, 0 ≤ M ω)
    (hJi : Integrable (fun ω => J ω ^ q) μ) (hMi : Integrable (fun ω => M ω ^ q) μ) :
    a ^ q * (∫ ω, W ω ^ q ∂μ) - b ^ q * (∫ ω, J ω ^ q ∂μ) ≤ ∫ ω, M ω ^ q ∂μ := by
  by_cases hWi : Integrable (fun ω => W ω ^ q) μ
  · have hpt : ∀ᵐ ω ∂μ, a ^ q * W ω ^ q - b ^ q * J ω ^ q ≤ M ω ^ q := by
      filter_upwards [h] with ω hω
      have := rpow_sub_rpow_le_of_sub_le (mul_nonneg ha (hW0 ω)) (mul_nonneg hb (hJ0 ω))
        (hM0 ω) hω hq0 hq1
      rwa [Real.mul_rpow ha (hW0 ω), Real.mul_rpow hb (hJ0 ω)] at this
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub (hWi.const_mul _) (hJi.const_mul _)]
    exact integral_mono_ae ((hWi.const_mul _).sub (hJi.const_mul _)) hMi hpt
  · rw [integral_undef hWi, mul_zero, zero_sub]
    have h1 : 0 ≤ b ^ q * ∫ ω, J ω ^ q ∂μ :=
      mul_nonneg (Real.rpow_nonneg hb _) (integral_nonneg fun ω => Real.rpow_nonneg (hJ0 ω) _)
    have h2 : 0 ≤ ∫ ω, M ω ^ q ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (hM0 ω) _
    linarith

/-! ### The assembly -/

/-- `⌊x⌋ < (⌊√x⌋ + 1)²`: the range condition of `RMF.khintchine_rough_weighted` at `y = ⌊√x⌋`. -/
lemma floor_lt_floor_sqrt_add_one_sq {x : ℝ} (hx0 : 0 ≤ x) :
    ⌊x⌋₊ < (⌊Real.sqrt x⌋₊ + 1) ^ 2 := by
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  have hs : Real.sqrt x < (⌊Real.sqrt x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlt : x < ((⌊Real.sqrt x⌋₊ : ℝ) + 1) ^ 2 := by nlinarith [Real.sqrt_nonneg x]
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hcast : (⌊x⌋₊ : ℝ) < (((⌊Real.sqrt x⌋₊ + 1) ^ 2 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hcast

/-- The constants of the assembly.  `ES, ER, EM, EW, EJ` are the five expectations of the chain
— the moment, the rough prime sum, the mean square, the window and the damped line — and
`L = log x`.  Khintchine's factor `3^{-(1-q)}/2^{1-2q}` lies in `[1/6, 1]` for `0 < q ≤ ½`,
`(8L)^{-q}(4π)^{-q} ≥ (32π)⁻¹ L^{-q}`, `16^q ≤ 16`, and every other factor is at most one. -/
lemma weighted_euler_lower_arith {ES ER EM EW EJ L V q : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q)
    (hq12 : q ≤ 1 / 2) (hEW : 0 ≤ EW) (hEJ : 0 ≤ EJ)
    (hkh : (3 : ℝ) ^ (-(1 - q)) * ER ≤ 2 ^ (1 - 2 * q) * ES)
    (h9 : (8 * L)⁻¹ ^ q * EM - (16 / L) ^ q ≤ ER)
    (hPar : (4 * Real.pi)⁻¹ ^ q * EW - (Real.pi⁻¹ * Real.exp (-V)) ^ q * EJ ≤ EM) :
    (192 * Real.pi)⁻¹ * L ^ (-q) * EW - 16 * Real.exp (-(V * q)) * L ^ (-q) * EJ
      - 16 * L ^ (-q) ≤ ES := by
  have hL0 : 0 < L := by linarith
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have hπ1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hl0 : 0 < L ^ (-q) := Real.rpow_pos_of_pos hL0 _
  -- the factors, split
  have hLq : L⁻¹ ^ q = L ^ (-q) := by rw [Real.inv_rpow hL0.le, ← Real.rpow_neg hL0.le]
  have h8 : (8 * L)⁻¹ ^ q = (8 : ℝ)⁻¹ ^ q * L ^ (-q) := by
    rw [mul_inv, Real.mul_rpow (by norm_num) (inv_nonneg.2 hL0.le), hLq]
  have h16 : (16 / L) ^ q = (16 : ℝ) ^ q * L ^ (-q) := by
    rw [div_eq_mul_inv, Real.mul_rpow (by norm_num) (inv_nonneg.2 hL0.le), hLq]
  have hpe : (Real.pi⁻¹ * Real.exp (-V)) ^ q = Real.pi⁻¹ ^ q * Real.exp (-(V * q)) := by
    rw [Real.mul_rpow (inv_nonneg.2 hπ0.le) (Real.exp_pos _).le, ← Real.exp_mul, neg_mul]
  rw [h8, h16] at h9
  rw [hpe] at hPar
  -- the bounds on them
  have ht : (0 : ℝ) < 2 ^ (1 - 2 * q) := Real.rpow_pos_of_pos two_pos _
  have hk16 : (1 / 6 : ℝ) ≤ (3 : ℝ) ^ (-(1 - q)) / 2 ^ (1 - 2 * q) := by
    have h3 : (3 : ℝ)⁻¹ ≤ (3 : ℝ) ^ (-(1 - q)) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (1 - 2 * q) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - 2 * q) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    rw [le_div_iff₀ ht]
    linarith
  have hk1 : (3 : ℝ) ^ (-(1 - q)) / 2 ^ (1 - 2 * q) ≤ 1 := by
    have h3 : (3 : ℝ) ^ (-(1 - q)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have h2 : (1 : ℝ) ≤ 2 ^ (1 - 2 * q) := Real.one_le_rpow (by norm_num) (by linarith)
    rw [div_le_one ht]
    linarith
  have hk0 : 0 ≤ (3 : ℝ) ^ (-(1 - q)) / 2 ^ (1 - 2 * q) := by linarith
  have hmain : (32 * Real.pi)⁻¹ ≤ (8 : ℝ)⁻¹ ^ q * (4 * Real.pi)⁻¹ ^ q := by
    rw [← Real.mul_rpow (by norm_num) (inv_nonneg.2 (by positivity)), ← mul_inv,
      show (8 : ℝ) * (4 * Real.pi) = 32 * Real.pi by ring]
    calc (32 * Real.pi)⁻¹ = (32 * Real.pi)⁻¹ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (32 * Real.pi)⁻¹ ^ q := Real.rpow_le_rpow_of_exponent_ge (by positivity)
          (inv_le_one_of_one_le₀ (by linarith)) (by linarith)
  have ha8 : 0 ≤ (8 : ℝ)⁻¹ ^ q := Real.rpow_nonneg (by norm_num) _
  have h8le : (8 : ℝ)⁻¹ ^ q ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) hq0.le
  have haπ : 0 ≤ Real.pi⁻¹ ^ q := Real.rpow_nonneg (inv_nonneg.2 hπ0.le) _
  have hπle : Real.pi⁻¹ ^ q ≤ 1 :=
    Real.rpow_le_one (inv_nonneg.2 hπ0.le) (inv_le_one_of_one_le₀ hπ1) hq0.le
  have hs16 : 0 ≤ (16 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
  have h16le : (16 : ℝ) ^ q ≤ 16 := by
    calc (16 : ℝ) ^ q ≤ 16 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 16 := Real.rpow_one 16
  have he0 : 0 ≤ Real.exp (-(V * q)) := (Real.exp_pos _).le
  -- the chain, with every product it needs
  have hkES : (3 : ℝ) ^ (-(1 - q)) / 2 ^ (1 - 2 * q) * ER ≤ ES := by
    rw [div_mul_eq_mul_div, div_le_iff₀ ht]
    linarith
  have p1 := mul_le_mul_of_nonneg_left h9 hk0
  have p2 := mul_le_mul_of_nonneg_left hPar (mul_nonneg hk0 (mul_nonneg ha8 hl0.le))
  have p3 : 1 / 6 * ((32 * Real.pi)⁻¹ * (L ^ (-q) * EW))
      ≤ (3 : ℝ) ^ (-(1 - q)) / 2 ^ (1 - 2 * q)
        * ((8 : ℝ)⁻¹ ^ q * (4 * Real.pi)⁻¹ ^ q * (L ^ (-q) * EW)) :=
    mul_le_mul hk16 (mul_le_mul_of_nonneg_right hmain (mul_nonneg hl0.le hEW))
      (mul_nonneg (inv_nonneg.2 (by positivity)) (mul_nonneg hl0.le hEW)) hk0
  have p4 : (3 : ℝ) ^ (-(1 - q)) / 2 ^ (1 - 2 * q) * ((8 : ℝ)⁻¹ ^ q * Real.pi⁻¹ ^ q)
        * (Real.exp (-(V * q)) * L ^ (-q) * EJ)
      ≤ 1 * (Real.exp (-(V * q)) * L ^ (-q) * EJ) :=
    mul_le_mul_of_nonneg_right (mul_le_one₀ hk1 (mul_nonneg ha8 haπ) (mul_le_one₀ h8le haπ hπle))
      (mul_nonneg (mul_nonneg he0 hl0.le) hEJ)
  have p5 : (3 : ℝ) ^ (-(1 - q)) / 2 ^ (1 - 2 * q) * (16 : ℝ) ^ q * L ^ (-q)
      ≤ 1 * 16 * L ^ (-q) :=
    mul_le_mul_of_nonneg_right (mul_le_mul hk1 h16le hs16 zero_le_one) hl0.le
  have hEJl : 0 ≤ Real.exp (-(V * q)) * L ^ (-q) * EJ := mul_nonneg (mul_nonneg he0 hl0.le) hEJ
  have e192 : (192 * Real.pi)⁻¹ = 1 / 6 * (32 * Real.pi)⁻¹ := by
    rw [show (192 : ℝ) * Real.pi = 6 * (32 * Real.pi) by ring, mul_inv]
    norm_num
  rw [e192]
  linarith

/-- **Gerspach's Proposition 6 at `α = 1`, for any main term the Parseval step bounds.**
There are `c, C > 0` and `x₀`, independent of `V`, `x`, `q` and `W`, such that for `V > 0`,
`x ≥ x₀` with `log x ≥ 3V + 3`, `0 < q ≤ ½`, and every nonnegative `W` with

`(4π)⁻¹ W - π⁻¹ e^{-V} ∫_ℝ |F(½+V/log x+it)|²/|V/log x+it|² dt ≤ M`   almost surely

(`M = RMF.weightedMeanSquare`),

`c (log x)^{-q} E[W^q] - C e^{-Vq} (log x)^{-q} E[(∫_ℝ |F(½+V/log x+it)|²/|V/log x+it|²)^q]`
`  - C (log x)^{-q} ≤ E|S(x)|^{2q}`.

The two instances are `RMF.exists_le_integral_rpow_weightedRademacherSum_euler` (`W` the window
`|t| < 1`, as for `q < ½`) and `RMF.exists_le_integral_rpow_weightedRademacherSum_euler_full`
(`W` the whole weighted line, as `q = ½` needs).  No measurability of `W` is asked: a
non-integrable `W^q` makes the bound trivial (`RMF.integral_rpow_sub_le_of_ae`). -/
theorem exists_le_integral_rpow_weightedRademacherSum_of_parseval :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ V x q : ℝ, 0 < V → x₀ ≤ x → 3 * V + 3 ≤ Real.log x → 0 < q → q ≤ 1 / 2 →
        ∀ W : Ω → ℝ, (∀ ω, 0 ≤ W ω) →
          (∀ᵐ ω ∂μ, (4 * Real.pi)⁻¹ * W ω - Real.pi⁻¹ * Real.exp (-V) * (∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
                  ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
                / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
            ≤ weightedMeanSquare (fun ω => squarefreeExtension fun p => X p ω) x ω) →
          c * Real.log x ^ (-q) * (∫ ω, W ω ^ q ∂μ)
            - C * Real.exp (-(V * q)) * Real.log x ^ (-q) * (∫ ω, (∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
                  ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
                / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
            - C * Real.log x ^ (-q)
          ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ := by
  obtain ⟨x₁, hL9⟩ := meanSquare_le_sum_weighted (Ω := Ω)
  refine ⟨(192 * Real.pi)⁻¹, 16, max x₁ 4, by positivity, by norm_num,
    fun X μ hX V x q hV hx hlogV hq0 hq12 W hW0 hae => ?_⟩
  haveI := hX.isProbabilityMeasure
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hx0, hlog, -, -, -⟩ := log_scale_facts hx4
  have hq1 : q ≤ 1 := by linarith
  have hσ₂0 : 0 < V / Real.log x := div_pos hV (by linarith)
  have hy2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (2 : ℝ) ≤ x))
  -- steps L1–L3 and L4–L9, on the primes of `(√x, x]`
  obtain ⟨hSp, hSx, hScov⟩ := primesIoc_sqrt_spec hx0.le
  have hkh := khintchine_rough_weighted hX (by linarith) (floor_lt_floor_sqrt_add_one_sq hx0.le)
    hq0 (by linarith)
  have h9 := hL9 X μ hX x q hxx₁ hq0.le hq1 (largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊) hSp hSx hScov
  -- Parseval, at the `q`-th power
  have hPar := integral_rpow_sub_le_of_ae hae (by positivity) (by positivity) hq0.le hq1 hW0
    (fun ω => integral_nonneg fun t => sq_nonneg _)
    (fun ω => weightedMeanSquare_nonneg _ x ω)
    (integrable_rpow_eulerProductLine_of_two_le hX hy2 hσ₂0 hq0.le)
    (integrable_rpow_of_integrable (integrable_weightedMeanSquare hX x)
      (Filter.Eventually.of_forall fun ω => weightedMeanSquare_nonneg _ x ω) hq0.le hq1)
  refine weighted_euler_lower_arith hlog hq0 hq12 ?_ ?_ hkh h9 hPar
  · exact integral_nonneg fun ω => Real.rpow_nonneg (hW0 ω) _
  · exact integral_nonneg fun ω => Real.rpow_nonneg (integral_nonneg fun t => sq_nonneg _) _

/-- **Gerspach's Proposition 6 at `α = 1`, for the Rademacher weighted sum, errors explicit.**
There are `c, C > 0` and `x₀`, independent of `V`, `x` and `q`, such that for every `V > 0`,
every `x ≥ x₀` with `log x ≥ 3V + 3`, and `0 < q ≤ ½`,

`c (log x)^{-q} E[(∫_{|t|<1} |F(½ + 2V/log x + it)|² dt)^q]`
`  - C e^{-Vq} (log x)^{-q} E[(∫_ℝ |F(½ + V/log x + it)|²/|V/log x + it|² dt)^q]`
`  - C (log x)^{-q} ≤ E|S(x)|^{2q}`,

with `S(x) = ∑_{n≤x} f(n)/√n` and `F` the Euler product over the primes up to `x`.  Gerspach's
`- O(1)` is `- C (log x)^{-q}` here; see the module docstring for why it has to be.
The only link between `V` and `x` is `log x ≥ 3V + 3`, so `V` may be a constant or grow with `x`.
`RMF.exists_le_integral_rpow_weightedRademacherSum_of_parseval` at the window. -/
theorem exists_le_integral_rpow_weightedRademacherSum_euler :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ V x q : ℝ, 0 < V → x₀ ≤ x → 3 * V + 3 ≤ Real.log x → 0 < q → q ≤ 1 / 2 →
          c * Real.log x ^ (-q) * (∫ ω, (∫ t in Set.Ioo (-1 : ℝ) 1,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
                ((1 / 2 : ℂ) + ((2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2)
                ^ q ∂μ)
            - C * Real.exp (-(V * q)) * Real.log x ^ (-q) * (∫ ω, (∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
                  ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
                / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
            - C * Real.log x ^ (-q)
          ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ := by
  obtain ⟨c, C, x₀, hc, hC, H⟩ := exists_le_integral_rpow_weightedRademacherSum_of_parseval
    (Ω := Ω)
  refine ⟨c, C, max x₀ 4, hc, hC, fun X μ hX V x q hV hx hlogV hq0 hq12 => ?_⟩
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  refine H X μ hX V x q hV (le_trans (le_max_left _ _) hx) hlogV hq0 hq12 _
    (fun ω => setIntegral_nonneg measurableSet_Ioo fun t _ => sq_nonneg _) ?_
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw 0
    (⌊x⌋₊ + 1)] with ω hω
  rw [primesIco_zero] at hω
  exact weightedMeanSquare_ge_line hV hlogV hx4 hω

/-- **Gerspach's Proposition 6 at `α = 1`, with the weight `|σ+it|^{-2}` kept.**  There are
`c, C > 0` and `x₀`, independent of `V`, `x` and `q`, such that for every `V > 0`, every `x ≥ x₀`
with `log x ≥ 3V + 3`, and `0 < q ≤ ½`,

`c (log x)^{-q} E[(∫_ℝ |F(½+2V/log x+it)|²/|2V/log x+it|² dt)^q]`
`  - C e^{-Vq} (log x)^{-q} E[(∫_ℝ |F(½+V/log x+it)|²/|V/log x+it|² dt)^q]`
`  - C (log x)^{-q} ≤ E|S(x)|^{2q}`.

The counterpart of Proposition 4.3 of the paper (stated there for `0 < q ≤ 1`, with `F_{t̃}` and
the window `|h| ≤ ½`), with the whole weighted line as main term: at `q = ½` every scale
`|t| ≍ T` contributes to it, so the weight must be kept.
`RMF.exists_le_integral_rpow_weightedRademacherSum_of_parseval` at the whole weighted line,
through `RMF.weightedMeanSquare_ge_line_full`. -/
theorem exists_le_integral_rpow_weightedRademacherSum_euler_full :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ V x q : ℝ, 0 < V → x₀ ≤ x → 3 * V + 3 ≤ Real.log x → 0 < q → q ≤ 1 / 2 →
          c * Real.log x ^ (-q) * (∫ ω, (∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
                  ((1 / 2 : ℂ) + ((2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
                / (((2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
            - C * Real.exp (-(V * q)) * Real.log x ^ (-q) * (∫ ω, (∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
                  ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
                / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
            - C * Real.log x ^ (-q)
          ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ := by
  obtain ⟨c, C, x₀, hc, hC, H⟩ := exists_le_integral_rpow_weightedRademacherSum_of_parseval
    (Ω := Ω)
  refine ⟨c, C, max x₀ 4, hc, hC, fun X μ hX V x q hV hx hlogV hq0 hq12 => ?_⟩
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  exact H X μ hX V x q hV (le_trans (le_max_left _ _) hx) hlogV hq0 hq12 _
    (fun ω => integral_nonneg fun t => sq_nonneg _)
    (Filter.Eventually.of_forall fun ω =>
      (quarter_sub_le_half_sub (integral_nonneg fun t => sq_nonneg _)).trans
        (weightedMeanSquare_ge_line_full hV hlogV hx4 ω))

end RMF
