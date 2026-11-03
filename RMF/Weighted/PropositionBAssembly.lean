/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.PropositionB

/-!
# Proposition B, assembled

Proposition B (`RMF/Weighted/PropositionB.lean`), here for `½ < q ≤ 1`,

`E[((log z)⁻¹∫_ℝ |F_{y,z}(½-c+it)|²/|c+it|² dt)^q] ≪ κ^{q(2q-1)}·b(min{1/(2q-1), log κ})`,

`c = 1/(2 log z)`, for a band `2 ≤ y < z` with `κ = log z/log y ≥ e`
(`RMF.exists_const_integral_rpow_lineDiv_band_le_rademacher`) and for the bottom band `y = 1`
with `κ = log z ≥ e` (`RMF.exists_const_integral_rpow_lineDiv_primesBelow_le_rademacher`).

The main case is a band with `y ≥ 3`, `κ ≥ 4e` and `z` large: the line is cut at `|t| = e^{-J}` and
`|t| = e^{J_b - J}`, with `J` from `RMF.exists_mesoRange_index` and `J_b ≈ J - log log y`
(`RMF.exists_band_depth`), and the three ranges are the central window, the mesoscopic range and
the far range.  Every other band with `y ≥ 3` is bounded crudely by `2πe^{45}κ`, which is `O(1)`
there, against `b ≥ ½`.  The band `y = 2` and the bottom band are dominated by the band `y = 3`:
the primes below `5` contribute a factor at most `2` (resp. `16`) to the modulus, almost surely,
and the right side is increasing in `κ`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Domination of a damped line integral -/

/-- **Domination of a damped line integral.**  If `F(ω, t)` is jointly measurable and bounded by
`U` almost surely uniformly in `t`, and `|G(ω, t)| ≤ K|F(ω, t)|` almost surely at every height,
then for `L > 0` and `q ≥ 0`

`E[(L⁻¹∫_ℝ |G|²/|σ+it|²)^q] ≤ (K²)^q·E[(L⁻¹∫_ℝ |F|²/|σ+it|²)^q]`. -/
theorem integral_rpow_lineDiv_le_of_norm_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F G : Ω → ℝ → ℂ} {σ U L q K : ℝ} (hσ : 0 < σ) (hL : 0 < L) (hq0 : 0 ≤ q)
    (hF : Measurable (Function.uncurry F)) (hU : ∀ᵐ ω ∂μ, ∀ t, ‖F ω t‖ ≤ U)
    (hGF : ∀ᵐ ω ∂μ, ∀ t, ‖G ω t‖ ≤ K * ‖F ω t‖) :
    (∫ ω, (L⁻¹ * ∫ t : ℝ, ‖G ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ (K ^ 2) ^ q
        * ∫ ω, (L⁻¹ * ∫ t : ℝ, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ := by
  have hpos : ∀ t : ℝ, 0 < σ ^ 2 + t ^ 2 := fun t => by positivity
  have hpt : ∀ (H : Ω → ℝ → ℂ) ω t, ‖H ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      = ‖H ω t‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹ := fun H ω t => by
    rw [norm_div, div_pow, Complex.sq_norm ((σ : ℂ) + (t : ℂ) * Complex.I),
      Complex.normSq_add_mul_I, div_eq_mul_inv]
  have hρ := integrable_inv_sq_add_sq hσ.ne'
  have hL0 : (0 : ℝ) ≤ L⁻¹ := inv_nonneg.2 hL.le
  have hI := integrable_rpow_setIntegral_lineDiv_of_bound (S := Set.univ) (q := q) hσ hL hq0 hF hU
  simp only [Measure.restrict_univ] at hI
  have hpt2 : ∀ᵐ ω ∂μ, (L⁻¹ * ∫ t : ℝ, ‖G ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q
      ≤ (K ^ 2) ^ q * (L⁻¹ * ∫ t : ℝ, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q := by
    filter_upwards [hU, hGF] with ω hωU hωG
    -- the dominating path is integrable on the line
    have hmeas : Measurable fun t : ℝ => ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
      have h1 : Measurable fun t : ℝ => F ω t := hF.comp (measurable_const.prodMk measurable_id)
      have h2 : Measurable fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I :=
        (Complex.measurable_ofReal.mul_const Complex.I).const_add _
      exact (h1.div h2).norm.pow_const 2
    have hFi : Integrable fun t : ℝ => ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
      refine Integrable.mono' (hρ.const_mul (U ^ 2)) hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => ?_)
      change ‖‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2‖ ≤ U ^ 2 * (σ ^ 2 + t ^ 2)⁻¹
      rw [Real.norm_of_nonneg (sq_nonneg _), hpt F ω t]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hωU t) 2)
        (inv_nonneg.2 (hpos t).le)
    have hle : (∫ t : ℝ, ‖G ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        ≤ K ^ 2 * ∫ t : ℝ, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => sq_nonneg _)
        (hFi.const_mul _) (Filter.Eventually.of_forall fun t => ?_)
      dsimp only
      rw [hpt G ω t, hpt F ω t, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (hpos t).le)
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hωG t) 2
    have h0 : (0 : ℝ) ≤ L⁻¹ * ∫ t : ℝ, ‖G ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
      mul_nonneg hL0 (integral_nonneg fun t => sq_nonneg _)
    have h0F : (0 : ℝ) ≤ L⁻¹ * ∫ t : ℝ, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
      mul_nonneg hL0 (integral_nonneg fun t => sq_nonneg _)
    rw [← Real.mul_rpow (sq_nonneg K) h0F]
    refine Real.rpow_le_rpow h0 ?_ hq0
    calc L⁻¹ * ∫ t : ℝ, ‖G ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        ≤ L⁻¹ * (K ^ 2 * ∫ t : ℝ, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hle hL0
      _ = K ^ 2 * (L⁻¹ * ∫ t : ℝ, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by ring
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
    Real.rpow_nonneg (mul_nonneg hL0 (integral_nonneg fun t => sq_nonneg _)) _)
    (hI.const_mul _) hpt2) (le_of_eq ?_)
  exact integral_const_mul _ _

/-- **A short block along `Re s = ½ - c` is at most `2^{y₁-y₀}`**, almost surely at every height,
for `c < ½`: each of its at most `y₁ - y₀` local factors has modulus at most `2`. -/
lemma ae_forall_norm_randomEulerProductIco_line_le_two_pow {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {c : ℝ} (hc : c < 1 / 2) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ 2 ^ (y₁ - y₀) := by
  have hprod : ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 + -c))) ≤ 2 ^ (y₁ - y₀) := by
    calc ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 + -c)))
        ≤ ∏ _p ∈ primesIco y₀ y₁, (2 : ℝ) := by
          refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_primesIco hp).one_lt.le
          have := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith : -(1 / 2 + -c) ≤ 0)
          linarith
      _ = 2 ^ (primesIco y₀ y₁).card := Finset.prod_const 2
      _ ≤ 2 ^ (y₁ - y₀) := by
          refine pow_le_pow_right₀ (by norm_num) ?_
          calc (primesIco y₀ y₁).card ≤ (Finset.Ico y₀ y₁).card := by
                refine Finset.card_le_card fun p hp => ?_
                obtain ⟨-, h0, h1⟩ := mem_primesIco.1 hp
                exact Finset.mem_Ico.2 ⟨h0, h1⟩
            _ = y₁ - y₀ := by simp
  filter_upwards [ae_forall_norm_randomEulerProductIco_line_le hX y₀ y₁ hc] with ω hω
  exact fun t => (hω t).trans hprod

/-! ### The right side of Proposition B -/

/-- **The right side of Proposition B is at least `½`**, for `½ < q ≤ 1` and `κ ≥ e`: `κ^γ ≥ 1`,
and the argument of `b` is at least `1`. -/
lemma half_le_rpow_mul_ballotFactor {q κ : ℝ} (hq2 : 1 / 2 < q) (hq1 : q ≤ 1)
    (hκ : Real.exp 1 ≤ κ) :
    1 / 2 ≤ κ ^ (q * (2 * q - 1)) * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log κ)) := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hκ1 : (1 : ℝ) ≤ κ := le_trans (by linarith [Real.add_one_le_exp 1]) hκ
  have hlog1 : (1 : ℝ) ≤ Real.log κ := by
    have h := Real.log_le_log (Real.exp_pos 1) hκ
    rwa [Real.log_exp] at h
  have hd1 : (1 : ℝ) ≤ (2 * q - 1)⁻¹ := (one_le_inv₀ (by linarith)).2 (by linarith)
  have hb := half_le_ballotFactor hq0 hq1 (le_min hd1 hlog1)
  have hκγ : (1 : ℝ) ≤ κ ^ (q * (2 * q - 1)) := Real.one_le_rpow hκ1 (mul_nonneg hq0 (by linarith))
  calc (1 : ℝ) / 2 = 1 * (1 / 2) := by ring
    _ ≤ κ ^ (q * (2 * q - 1)) * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log κ)) :=
        mul_le_mul hκγ hb (by norm_num) (by linarith)

/-- **The right side of Proposition B is increasing in `κ`** on `κ ≥ e`, for `½ < q ≤ 1`. -/
lemma rpow_mul_ballotFactor_le_of_le {q κ₁ κ₂ : ℝ} (hq2 : 1 / 2 < q) (hq1 : q ≤ 1)
    (hκ₁ : Real.exp 1 ≤ κ₁) (hκ : κ₁ ≤ κ₂) :
    κ₁ ^ (q * (2 * q - 1)) * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log κ₁))
      ≤ κ₂ ^ (q * (2 * q - 1)) * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log κ₂)) := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hκ₁0 : (0 : ℝ) < κ₁ := lt_of_lt_of_le (Real.exp_pos 1) hκ₁
  have hlog1 : (1 : ℝ) ≤ Real.log κ₁ := by
    have h := Real.log_le_log (Real.exp_pos 1) hκ₁
    rwa [Real.log_exp] at h
  have hd1 : (1 : ℝ) ≤ (2 * q - 1)⁻¹ := (one_le_inv₀ (by linarith)).2 (by linarith)
  have hm : min (2 * q - 1)⁻¹ (Real.log κ₁) ≤ min (2 * q - 1)⁻¹ (Real.log κ₂) :=
    le_min (min_le_left _ _) ((min_le_right _ _).trans (Real.log_le_log hκ₁0 hκ))
  have hb1 := half_le_ballotFactor hq0 hq1 (le_min hd1 hlog1)
  exact mul_le_mul (Real.rpow_le_rpow hκ₁0.le hκ (mul_nonneg hq0 (by linarith)))
    (ballotFactor_le_ballotFactor hq0 hq1 (lt_of_lt_of_le one_pos (le_min hd1 hlog1)) hm)
    (by linarith) (Real.rpow_nonneg (hκ₁0.le.trans hκ) _)

/-! ### The main case: a band with `y ≥ 3`, `κ ≥ 4e`, `z` large -/

/-- **The depth of a band's mesoscopic range.**  For a band with `3 ≤ y`, `8 ≤ z` and
`κ = log z/log y ≥ 4e`, and `J` as `RMF.exists_mesoRange_index` gives it at `z`, some `J_b ≥ 1`
has `J_b + log log(y+1) ≤ J ≤ J_b + log log y + 2` (the window of
`RMF.exists_const_integral_rpow_mesoRange_band_le_rademacher`), `J_b ≤ log κ + 1` (that of
`RMF.exp_mul_ballotFactor_le`), and `e²·e^{J_b-J}·log y ≥ 1`, so that the far range starts at a
height `≍ 1/log y`.  It is `J_b = ⌊J - log log(y+1)⌋`. -/
lemma exists_band_depth {y z J : ℕ} (hy : 3 ≤ y) (hz : 8 ≤ z)
    (hκ : 4 * Real.exp 1 ≤ Real.log z / Real.log y)
    (hJup : (J : ℝ) ≤ Real.log (Real.log z - Real.log 2) + 1)
    (hJlo : Real.log (Real.log z / 2) ≤ (J : ℝ)) :
    ∃ Jb : ℕ, 1 ≤ Jb ∧ (Jb : ℝ) + Real.log (Real.log ((y : ℝ) + 1)) ≤ J
      ∧ (J : ℝ) ≤ Jb + Real.log (Real.log y) + 2
      ∧ (Jb : ℝ) ≤ Real.log (Real.log z / Real.log y) + 1
      ∧ 1 ≤ Real.exp 2 * (Real.exp ((Jb : ℝ) - J) * Real.log y) := by
  have hy3 : (3 : ℝ) ≤ y := by exact_mod_cast hy
  have hz8 : (8 : ℝ) ≤ z := by exact_mod_cast hz
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogy1 : 0 < Real.log ((y : ℝ) + 1) := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have he := Real.exp_one_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hl20 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- `log(y+1) ≤ 2 log y`
  have hy1 : Real.log ((y : ℝ) + 1) ≤ 2 * Real.log y := by
    have h2 : Real.log ((y : ℝ) ^ 2) = 2 * Real.log y := by
      rw [Real.log_pow]
      norm_num
    rw [← h2]
    exact Real.log_le_log (by linarith) (by nlinarith)
  -- `J - log log(y+1) ≥ 1`
  have hzy : 4 * Real.exp 1 * Real.log y ≤ Real.log z := (le_div_iff₀ hlogy).1 hκ
  have hA : Real.exp 1 * Real.log ((y : ℝ) + 1) ≤ Real.log z / 2 := by
    have := mul_le_mul_of_nonneg_left hy1 (Real.exp_pos 1).le
    linarith
  have hB : 1 + Real.log (Real.log ((y : ℝ) + 1)) ≤ Real.log (Real.log z / 2) := by
    have h := Real.log_le_log (mul_pos (Real.exp_pos 1) hlogy1) hA
    rwa [Real.log_mul (Real.exp_pos 1).ne' hlogy1.ne', Real.log_exp] at h
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (J : ℝ) - Real.log (Real.log ((y : ℝ) + 1)) := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by linarith
  have hfl : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le (by linarith)
  have hlt : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  refine ⟨⌊a⌋₊, Nat.le_floor (by rw [Nat.cast_one]; exact ha1), by linarith, ?_, ?_, ?_⟩
  · -- `log log(y+1) ≤ log 2 + log log y`
    have hC : Real.log (Real.log ((y : ℝ) + 1)) ≤ Real.log 2 + Real.log (Real.log y) := by
      rw [← Real.log_mul two_ne_zero hlogy.ne']
      exact Real.log_le_log hlogy1 hy1
    linarith
  · have hz2 : Real.log 2 < Real.log z := Real.log_lt_log two_pos (by linarith)
    have hD : Real.log (Real.log z - Real.log 2) ≤ Real.log (Real.log z) :=
      Real.log_le_log (by linarith) (by linarith)
    have hE : Real.log (Real.log y) ≤ Real.log (Real.log ((y : ℝ) + 1)) :=
      Real.log_le_log hlogy (Real.log_le_log (by linarith) (by linarith))
    rw [Real.log_div hlogz.ne' hlogy.ne']
    linarith
  · have hF : Real.exp (1 - Real.log (Real.log ((y : ℝ) + 1)))
        ≤ Real.exp 2 * Real.exp ((⌊a⌋₊ : ℝ) - J) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_sub 1 (Real.log (Real.log ((y : ℝ) + 1))), Real.exp_log hlogy1] at hF
    have hG : 1 ≤ Real.exp 1 / Real.log ((y : ℝ) + 1) * Real.log y := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlogy1, one_mul]
      have := mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ Real.exp 1) hlogy.le
      linarith
    calc (1 : ℝ) ≤ Real.exp 1 / Real.log ((y : ℝ) + 1) * Real.log y := hG
      _ ≤ Real.exp 2 * Real.exp ((⌊a⌋₊ : ℝ) - J) * Real.log y :=
          mul_le_mul_of_nonneg_right hF hlogy.le
      _ = Real.exp 2 * (Real.exp ((⌊a⌋₊ : ℝ) - J) * Real.log y) := by ring

/-- **A band's damped line integral at `c = 1/(2 log z)`, crudely**: at most `2πe^{45}·κ`, for
`0 ≤ q ≤ 1` and `2 ≤ y ≤ z` with `z ≥ 3`.  `RMF.integral_rpow_lineDiv_primesIco_le` at that `c`,
where `πe^{45}/(c·log y) = 2πe^{45}κ ≥ 1`, so that its `q`-th power is at most itself. -/
lemma integral_rpow_lineDiv_band_le_crude {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q c : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {y z : ℕ}
    (hy : 2 ≤ y) (hyz : y ≤ z) (hz : 3 ≤ z) (hc : 2 * c * Real.log z = 1) :
    (∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
            ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
          / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ 2 * Real.pi * Real.exp 45 * (Real.log z / Real.log y) := by
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hz3 : (3 : ℝ) ≤ z := by exact_mod_cast hz
  have hyzR : (y : ℝ) ≤ z := by exact_mod_cast hyz
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogz1 : 1 < Real.log z := by
    have h := Real.log_lt_log (Real.exp_pos 1)
      (by linarith [Real.exp_one_lt_d9] : Real.exp 1 < z)
    rwa [Real.log_exp] at h
  have hc0 : 0 < c := by nlinarith
  have hc2 : c < 1 / 2 := by nlinarith
  refine le_trans (integral_rpow_lineDiv_primesIco_le hX hq0 hq1 hy hyz hc0 hc2 hc.le) ?_
  have hbase : Real.pi * Real.exp 45 / (c * Real.log y)
      = 2 * Real.pi * Real.exp 45 * (Real.log z / Real.log y) := by
    calc Real.pi * Real.exp 45 / (c * Real.log y)
        = Real.pi * Real.exp 45 * (2 * c * Real.log z) / (c * Real.log y) := by rw [hc, mul_one]
      _ = 2 * Real.pi * Real.exp 45 * (Real.log z / Real.log y) * (c / c) := by ring
      _ = 2 * Real.pi * Real.exp 45 * (Real.log z / Real.log y) := by
          rw [div_self hc0.ne', mul_one]
  rw [hbase]
  have hκ1 : (1 : ℝ) ≤ Real.log z / Real.log y :=
    (one_le_div hlogy).2 (Real.log_le_log (by linarith) hyzR)
  have hK1 : (1 : ℝ) ≤ 2 * Real.pi * Real.exp 45 := by
    nlinarith [Real.pi_gt_three, Real.add_one_le_exp 45]
  have h1 := one_le_mul_of_one_le_of_one_le hK1 hκ1
  calc (2 * Real.pi * Real.exp 45 * (Real.log z / Real.log y)) ^ q
      ≤ (2 * Real.pi * Real.exp 45 * (Real.log z / Real.log y)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 hq1
    _ = 2 * Real.pi * Real.exp 45 * (Real.log z / Real.log y) := Real.rpow_one _

/-- **Proposition B for a band, the main case**: `y ≥ 3`, `κ = log z/log y ≥ 4e` and `z ≥ z₁`,
for `½ < q ≤ 1` and `c = 1/(2 log z)`.  The line is cut at `|t| = e^{-J}` and `|t| = e^{J_b-J}`
(`RMF.exists_mesoRange_index`, `RMF.exists_band_depth`); the central window
(`RMF.integral_rpow_centralWindow_primesIco_le`), the mesoscopic range (through
`RMF.exp_mul_ballotFactor_le`) and the far range (`≤ 2e^{47}`) are each `≪ κ^γ b(m)` against
`κ^γ b(m) ≥ ½`, where `m = min{1/(2q-1), log κ}` and `γ = q(2q-1)`. -/
theorem exists_const_integral_rpow_lineDiv_band_le_rademacher_of_large :
    ∃ (z₁ C : ℝ), 0 < C ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (q c : ℝ) (y z : ℕ), 1 / 2 < q → q ≤ 1 → 3 ≤ y → z₁ ≤ (z : ℝ) →
          4 * Real.exp 1 ≤ Real.log z / Real.log y → 2 * c * Real.log z = 1 →
            (∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
                    (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
                  / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
              ≤ C * ((Real.log z / Real.log y) ^ (q * (2 * q - 1))
                * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log z / Real.log y)))) := by
  obtain ⟨z₀, A, hA, hmeso⟩ := exists_const_integral_rpow_mesoRange_band_le_rademacher (Ω := Ω)
  refine ⟨max (max z₀ (Real.exp 6)) 8,
    4 * (Real.pi * Real.exp (143800 * Real.exp 1) * Real.exp 48) + 3 * Real.exp 1 * A
      + 4 * Real.exp 47, by positivity, ?_⟩
  intro Y ν hY q c y z hq2 hq1 hy hz hκ hc
  haveI := hY.isProbabilityMeasure
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hz0 : z₀ ≤ (z : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hz
  have hz6 : Real.exp 6 ≤ (z : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hz
  have hz8 : (8 : ℝ) ≤ z := le_trans (le_max_right _ _) hz
  have hy3 : (3 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogz6 : 6 ≤ Real.log z := by
    have h := Real.log_le_log (Real.exp_pos 6) hz6
    rwa [Real.log_exp] at h
  have hlogz : 0 < Real.log z := by linarith
  have hc0 : 0 < c := by nlinarith
  have hc12 : c ≤ 1 / 12 := by nlinarith
  have hcl : (c * Real.log z)⁻¹ = 2 := by
    rw [show c * Real.log z = 1 / 2 by linarith]
    norm_num
  -- the band's order
  have he1 : (1 : ℝ) ≤ 4 * Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hlyz : Real.log y ≤ Real.log z := by
    have := (le_div_iff₀ hlogy).1 (le_trans he1 hκ)
    linarith
  have hyz : y ≤ z := by
    have := (Real.log_le_log_iff (by linarith) (by linarith)).1 hlyz
    exact_mod_cast this
  have hy2 : 2 ≤ y := by omega
  have hz3 : 3 ≤ z := le_trans hy hyz
  -- the cuts
  obtain ⟨J, -, hJw, hJup, hJlo⟩ := exists_mesoRange_index hz8
  obtain ⟨Jb, hJb1, hJbJ, hJJb, hJbκ, hT⟩ :=
    exists_band_depth (z := z) hy (by exact_mod_cast hz8) hκ hJup hJlo
  have hwT : Real.exp (-(J : ℝ)) ≤ Real.exp ((Jb : ℝ) - J) :=
    Real.exp_le_exp.2 (by linarith [(Nat.cast_nonneg Jb : (0 : ℝ) ≤ Jb)])
  -- the three ranges
  have h1 := integral_rpow_centralWindow_primesIco_le hY (by linarith : (1 : ℝ) / 2 ≤ q) hq1
    hy2 hyz hz3 hc0 hc12 hc.le (Real.exp_pos _) hJw
  have h2 := hmeso Y ν hY c q y z J Jb hz0 hy hc0 hc12 hc.le hq2 hq1 hJb1 hJup hJbJ hJJb
  have h3 := integral_rpow_farRange_primesIco_le hY hq0 hq1 hy2 hyz hc0 hc12 hc.le
    (Real.exp_pos ((Jb : ℝ) - J))
  refine le_trans (integral_rpow_lineDiv_le_of_three_ranges (μ := ν)
    (F := fun ω t => randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
      (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω)
    (σ := c) (L := Real.log z) hc0 hlogz hq0 hq1 hwT
    (measurable_uncurry_randomEulerProductIco_line hY (y + 1) (z + 1) c)
    (ae_forall_norm_randomEulerProductIco_line_le hY (y + 1) (z + 1) (by linarith)) h1 h2 h3) ?_
  clear h1 h2 h3 hmeso
  -- the arithmetic, against `R = κ^γ b(m) ≥ ½`
  have hκe : Real.exp 1 ≤ Real.log z / Real.log y := le_trans (by linarith [Real.exp_pos 1]) hκ
  have hE := exp_mul_ballotFactor_le hq2 hq1 hκe hJb1 hJbκ
  have hR := half_le_rpow_mul_ballotFactor hq2 hq1 hκe
  have hκγ : (Real.log z / Real.log y) ^ (q * (2 * q - 1))
      ≤ 2 * ((Real.log z / Real.log y) ^ (q * (2 * q - 1))
        * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log z / Real.log y)))) := by
    have hd1 : (1 : ℝ) ≤ (2 * q - 1)⁻¹ := (one_le_inv₀ (by linarith)).2 (by linarith)
    have hlog1 : (1 : ℝ) ≤ Real.log (Real.log z / Real.log y) := by
      have h := Real.log_le_log (Real.exp_pos 1) hκe
      rwa [Real.log_exp] at h
    have hb := half_le_ballotFactor hq0 hq1 (le_min hd1 hlog1)
    have := mul_le_mul_of_nonneg_left hb
      (Real.rpow_nonneg (div_pos hlogz hlogy).le (q * (2 * q - 1)))
    linarith
  set R := (Real.log z / Real.log y) ^ (q * (2 * q - 1))
    * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log z / Real.log y))) with hRdef
  have hB1 : Real.pi * Real.exp (143800 * Real.exp 1) * Real.exp 48 * ((c * Real.log z)⁻¹) ^ q
      * (Real.log z / Real.log y) ^ (q * (2 * q - 1))
      ≤ 4 * (Real.pi * Real.exp (143800 * Real.exp 1) * Real.exp 48) * R := by
    rw [hcl]
    have h2q : (2 : ℝ) ^ q ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hq1
      rwa [Real.rpow_one] at h
    have hK : 0 ≤ Real.pi * Real.exp (143800 * Real.exp 1) * Real.exp 48 := by positivity
    calc Real.pi * Real.exp (143800 * Real.exp 1) * Real.exp 48 * 2 ^ q
          * (Real.log z / Real.log y) ^ (q * (2 * q - 1))
        ≤ Real.pi * Real.exp (143800 * Real.exp 1) * Real.exp 48 * 2 * (2 * R) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2q hK) hκγ
            (Real.rpow_nonneg (div_pos hlogz hlogy).le _) (by positivity)
      _ = 4 * (Real.pi * Real.exp (143800 * Real.exp 1) * Real.exp 48) * R := by ring
  have hB2 := mul_le_mul_of_nonneg_left hE hA.le
  have hB3 : (2 * Real.exp 45 / (Real.exp ((Jb : ℝ) - J) * Real.log y)) ^ q
      ≤ 4 * Real.exp 47 * R := by
    have hTy : 0 < Real.exp ((Jb : ℝ) - J) * Real.log y := mul_pos (Real.exp_pos _) hlogy
    have hbase : 2 * Real.exp 45 / (Real.exp ((Jb : ℝ) - J) * Real.log y)
        ≤ 2 * Real.exp 47 := by
      rw [div_le_iff₀ hTy]
      have h47 : Real.exp 47 = Real.exp 45 * Real.exp 2 := by
        rw [← Real.exp_add]
        norm_num
      rw [h47]
      have := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ 2 * Real.exp 45)
      linarith
    have h1le : (1 : ℝ) ≤ 2 * Real.exp 47 := by linarith [Real.add_one_le_exp 47]
    calc (2 * Real.exp 45 / (Real.exp ((Jb : ℝ) - J) * Real.log y)) ^ q
        ≤ (2 * Real.exp 47) ^ q := Real.rpow_le_rpow (div_pos (by positivity) hTy).le hbase hq0
      _ ≤ (2 * Real.exp 47) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1le hq1
      _ = 2 * Real.exp 47 := Real.rpow_one _
      _ ≤ 4 * Real.exp 47 * R := by
          have := mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ) ≤ 4 * Real.exp 47)
          linarith
  linarith [hB1, hB2, hB3]

/-! ### Every band -/

/-- **Proposition B for a band with `y ≥ 3`, against any `κ` above the band's own.**  For
`½ < q ≤ 1`, `3 ≤ y ≤ z`, `c = 1/(2 log z)` and `κ ≥ max{e, log z/log y}`, with `γ = q(2q-1)`,
`E[((log z)⁻¹∫_ℝ‖F_{y,z}(½-c+it)/(c+it)‖²dt)^q] ≤ C·κ^γ·b(min{1/(2q-1), log κ})`.  In the main
case, `RMF.exists_const_integral_rpow_lineDiv_band_le_rademacher_of_large`, the right side grows
with `κ`; otherwise `log z/log y ≤ 4e + log z₁` and the crude bound is `O(1)` against a right side
`≥ ½`.  The freedom in `κ` lets the bands `y = 2` and `y = 1` be dominated by the band `y = 3`. -/
theorem exists_const_integral_rpow_lineDiv_band_le_rademacher_of_three_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (q c κ : ℝ) (y z : ℕ), 1 / 2 < q → q ≤ 1 → 3 ≤ y → y ≤ z →
          Real.exp 1 ≤ κ → Real.log z / Real.log y ≤ κ → 2 * c * Real.log z = 1 →
            (∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
                    (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
                  / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
              ≤ C * (κ ^ (q * (2 * q - 1)) * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log κ))) := by
  obtain ⟨z₁, C₁, hC₁, hlarge⟩ :=
    exists_const_integral_rpow_lineDiv_band_le_rademacher_of_large (Ω := Ω)
  have hM0 : (0 : ℝ) ≤ max (Real.log z₁) 0 := le_max_right _ _
  refine ⟨C₁ + 2 * (2 * Real.pi * Real.exp 45 * (4 * Real.exp 1 + max (Real.log z₁) 0)),
    by positivity, ?_⟩
  intro Y ν hY q c κ y z hq2 hq1 hy hyz hκe hκ hc
  haveI := hY.isProbabilityMeasure
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hy3 : (3 : ℝ) ≤ y := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ z := by exact_mod_cast hyz
  have hlogy1 : (1 : ℝ) ≤ Real.log y := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ y)
    rwa [Real.log_exp] at h
  have hlogz : 0 < Real.log z := by
    have := Real.log_le_log (by linarith) hyzR
    linarith
  have hR := half_le_rpow_mul_ballotFactor hq2 hq1 hκe
  have hR0 : (0 : ℝ)
      ≤ κ ^ (q * (2 * q - 1)) * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log κ)) := by
    linarith
  have hK : (0 : ℝ) ≤ 2 * Real.pi * Real.exp 45 * (4 * Real.exp 1 + max (Real.log z₁) 0) := by
    positivity
  by_cases hbig : z₁ ≤ (z : ℝ) ∧ 4 * Real.exp 1 ≤ Real.log z / Real.log y
  · have he4 : Real.exp 1 ≤ Real.log z / Real.log y :=
      le_trans (by linarith [Real.exp_pos 1]) hbig.2
    refine le_trans (hlarge Y ν hY q c y z hq2 hq1 hy hbig.1 hbig.2 hc) ?_
    have hmono := rpow_mul_ballotFactor_le_of_le hq2 hq1 he4 hκ
    calc C₁ * ((Real.log z / Real.log y) ^ (q * (2 * q - 1))
          * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log z / Real.log y))))
        ≤ C₁ * (κ ^ (q * (2 * q - 1)) * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log κ))) :=
          mul_le_mul_of_nonneg_left hmono hC₁.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hR0
  · refine le_trans (integral_rpow_lineDiv_band_le_crude hY hq0 hq1 (by omega) hyz
      (le_trans hy hyz) hc) ?_
    have hκM : Real.log z / Real.log y ≤ 4 * Real.exp 1 + max (Real.log z₁) 0 := by
      rcases not_and_or.1 hbig with h | h
      · have hz1 : (z : ℝ) < z₁ := lt_of_not_ge h
        have h1 : Real.log z / Real.log y ≤ Real.log z := div_le_self hlogz.le hlogy1
        have h2 : Real.log z < Real.log z₁ := Real.log_lt_log (by linarith) hz1
        have h3 := le_max_left (Real.log z₁) 0
        have h4 := Real.exp_pos 1
        linarith
      · have h1 := lt_of_not_ge h
        linarith
    have hA := mul_le_mul_of_nonneg_left hκM
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi * Real.exp 45)
    have hB := mul_le_mul_of_nonneg_left hR hK
    have hC := mul_nonneg hC₁.le hR0
    linarith

/-- **Proposition B for a band**, for `½ < q ≤ 1`: a constant `C` such that for `2 ≤ y < z` with
`κ = log z/log y ≥ e` and `c = 1/(2 log z)`,

`E[((log z)⁻¹∫_ℝ |F_{y,z}(½-c+it)|²/|c+it|² dt)^q] ≤ C·κ^{q(2q-1)}·b(min{1/(2q-1), log κ})`,

`F_{y,z} = randomEulerProductIco f (y+1) (z+1)` the product over the primes `y < p ≤ z` and
`b = RMF.ballotFactor q`.  `q = ½` is not covered.
For `y ≥ 3` it is `RMF.exists_const_integral_rpow_lineDiv_band_le_rademacher_of_three_le`
at the band's own `κ`.  For `y = 2`, `F_{2,z} = (1 + f(3)·3^{-s})·F_{3,z}` with the first factor at
most `2` almost surely (`RMF.ae_forall_norm_randomEulerProductIco_line_le_two_pow`), so the moment
is at most `4` times that of the band `(3, z]` (`RMF.integral_rpow_lineDiv_le_of_norm_le`), which is
bounded at `κ ≥ log z/log 3`. -/
theorem exists_const_integral_rpow_lineDiv_band_le_rademacher :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (q c : ℝ) (y z : ℕ), 1 / 2 < q → q ≤ 1 → 2 ≤ y →
          Real.exp 1 ≤ Real.log z / Real.log y → 2 * c * Real.log z = 1 →
            (∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
                    (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
                  / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
              ≤ C * ((Real.log z / Real.log y) ^ (q * (2 * q - 1))
                * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log z / Real.log y)))) := by
  obtain ⟨C₃, hC₃, h3⟩ :=
    exists_const_integral_rpow_lineDiv_band_le_rademacher_of_three_le (Ω := Ω)
  refine ⟨4 * C₃, by positivity, ?_⟩
  intro Y ν hY q c y z hq2 hq1 hy hκ hc
  haveI := hY.isProbabilityMeasure
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hR := half_le_rpow_mul_ballotFactor hq2 hq1 hκ
  rcases Nat.lt_or_ge y 3 with hy3 | hy3
  · -- the band `y = 2`, dominated by the band `y = 3`
    obtain rfl : y = 2 := by omega
    have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
    have hκ' : Real.exp 1 * Real.log 2 ≤ Real.log z := by
      have := (le_div_iff₀ hlogy).1 hκ
      exact_mod_cast this
    have hlt : 2 * Real.log 2 < Real.log z := by
      have := mul_lt_mul_of_pos_right (by linarith [Real.exp_one_gt_d9] : (2 : ℝ) < Real.exp 1) hl2
      linarith
    have hlogz1 : 1 < Real.log z := by linarith [Real.log_two_gt_d9]
    have hz0 : (0 : ℝ) < z := by
      rcases Nat.eq_zero_or_pos z with h | h
      · rw [h, Nat.cast_zero, Real.log_zero] at hlogz1
        linarith
      · exact_mod_cast h
    have hz4 : (4 : ℝ) < z := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      exact (Real.log_lt_log_iff (by norm_num) hz0).1 (by rw [h4]; exact hlt)
    have hz3 : 3 ≤ z := by
      have : (3 : ℝ) ≤ z := by linarith
      exact_mod_cast this
    have hc0 : 0 < c := by nlinarith
    have hc2 : c < 1 / 2 := by nlinarith
    have hGF : ∀ᵐ ω ∂ν, ∀ t : ℝ,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (2 + 1) (z + 1)
            ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω‖
          ≤ 2 * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (3 + 1)
            (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω‖ := by
      filter_upwards [ae_forall_norm_randomEulerProductIco_line_le_two_pow hY (2 + 1) (3 + 1) hc2]
        with ω hω
      intro t
      rw [← randomEulerProductIco_mul _ (by norm_num : 2 + 1 ≤ 3 + 1) (by omega : 3 + 1 ≤ z + 1),
        norm_mul]
      exact mul_le_mul_of_nonneg_right (by simpa using hω t) (norm_nonneg _)
    have hdom := integral_rpow_lineDiv_le_of_norm_le (μ := ν)
      (F := fun ω t => randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (3 + 1)
        (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω)
      (G := fun ω t => randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (2 + 1)
        (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω)
      (L := Real.log z) hc0 (by linarith) hq0
      (measurable_uncurry_randomEulerProductIco_line hY (3 + 1) (z + 1) c)
      (ae_forall_norm_randomEulerProductIco_line_le hY (3 + 1) (z + 1) hc2) hGF
    have hκ32 : Real.log z / Real.log ((3 : ℕ) : ℝ) ≤ Real.log z / Real.log ((2 : ℕ) : ℝ) := by
      refine div_le_div_of_nonneg_left (by linarith) hlogy ?_
      push_cast
      exact Real.log_le_log (by norm_num) (by norm_num)
    have hZ3 := h3 Y ν hY q c (Real.log z / Real.log ((2 : ℕ) : ℝ)) 3 z hq2 hq1 le_rfl hz3 hκ
      hκ32 hc
    have h4q : ((2 : ℝ) ^ 2) ^ q ≤ 4 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2 ^ 2) hq1
      rw [Real.rpow_one] at h
      linarith
    have hEZ3 : (0 : ℝ) ≤ ∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (3 + 1) (z + 1)
            ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
          / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν :=
      integral_nonneg fun ω => Real.rpow_nonneg
        (mul_nonneg (inv_nonneg.2 (by linarith)) (integral_nonneg fun t => sq_nonneg _)) _
    refine le_trans hdom (le_trans (mul_le_mul h4q hZ3 hEZ3 (by norm_num)) (le_of_eq ?_))
    ring
  · -- the bands `y ≥ 3`
    have hlyz : Real.log y ≤ Real.log z := by
      have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      have := (le_div_iff₀ hlogy).1 (le_trans he1 hκ)
      linarith
    have hz0 : (0 : ℝ) < z := by
      rcases Nat.eq_zero_or_pos z with h | h
      · rw [h, Nat.cast_zero, Real.log_zero] at hlyz
        linarith
      · exact_mod_cast h
    have hyz : y ≤ z := by
      have := (Real.log_le_log_iff (by linarith) hz0).1 hlyz
      exact_mod_cast this
    refine le_trans (h3 Y ν hY q c _ y z hq2 hq1 hy3 hyz hκ le_rfl hc) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)

/-- **Proposition B for the bottom band** (`y = 1`, `κ = log z`), for `½ < q ≤ 1`: a constant `C`
such that for `log z ≥ e` and `c = 1/(2 log z)`,

`E[((log z)⁻¹∫_ℝ |F_z(½-c+it)|²/|c+it|² dt)^q] ≤ C·(log z)^{q(2q-1)}·b(min{1/(2q-1), log log z})`,

`F_z = randomEulerProduct f (z+1)` the product over the primes `p ≤ z`.  As for the band `y = 2`:
`F_z = F_{[0,4)}·F_{3,z}` with the first factor at most `16` almost surely, so the moment is at
most `256` times that of the band `(3, z]`, bounded at `κ = log z ≥ log z/log 3`. -/
theorem exists_const_integral_rpow_lineDiv_primesBelow_le_rademacher :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (q c : ℝ) (z : ℕ), 1 / 2 < q → q ≤ 1 → Real.exp 1 ≤ Real.log z →
          2 * c * Real.log z = 1 →
            (∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
                ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (z + 1)
                    ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
                  / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
              ≤ C * ((Real.log z) ^ (q * (2 * q - 1))
                * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log z)))) := by
  obtain ⟨C₃, hC₃, h3⟩ :=
    exists_const_integral_rpow_lineDiv_band_le_rademacher_of_three_le (Ω := Ω)
  refine ⟨256 * C₃, by positivity, ?_⟩
  intro Y ν hY q c z hq2 hq1 hκ hc
  haveI := hY.isProbabilityMeasure
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have he := Real.exp_one_gt_d9
  have hlogz1 : 1 < Real.log z := by linarith
  have hlog3 : (1 : ℝ) ≤ Real.log ((3 : ℕ) : ℝ) := by
    push_cast
    have h := Real.log_le_log (Real.exp_pos 1)
      (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 3)
    rwa [Real.log_exp] at h
  have hz0 : (0 : ℝ) < z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hlogz1
      linarith
    · exact_mod_cast h
  have hz3 : 3 ≤ z := by
    have h3z : Real.log ((3 : ℕ) : ℝ) < Real.log z := by
      push_cast
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have := (Real.log_lt_log_iff (by norm_num) hz0).1 h3z
    exact_mod_cast this.le
  have hc0 : 0 < c := by nlinarith
  have hc2 : c < 1 / 2 := by nlinarith
  have hGF : ∀ᵐ ω ∂ν, ∀ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (z + 1)
          ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω‖
        ≤ 16 * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (3 + 1)
          (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω‖ := by
    filter_upwards [ae_forall_norm_randomEulerProductIco_line_le_two_pow hY 0 (3 + 1) hc2]
      with ω hω
    intro t
    rw [← randomEulerProductIco_zero, ← randomEulerProductIco_mul _ (Nat.zero_le (3 + 1))
      (by omega : 3 + 1 ≤ z + 1), norm_mul]
    exact mul_le_mul_of_nonneg_right (by have h := hω t; norm_num at h ⊢; exact h)
      (norm_nonneg _)
  have hdom := integral_rpow_lineDiv_le_of_norm_le (μ := ν)
    (F := fun ω t => randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (3 + 1)
      (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω)
    (G := fun ω t => randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (z + 1)
      ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω)
    (L := Real.log z) hc0 (by linarith) hq0
    (measurable_uncurry_randomEulerProductIco_line hY (3 + 1) (z + 1) c)
    (ae_forall_norm_randomEulerProductIco_line_le hY (3 + 1) (z + 1) hc2) hGF
  have hκ3 : Real.log z / Real.log ((3 : ℕ) : ℝ) ≤ Real.log z :=
    div_le_self (by linarith) hlog3
  have hZ3 := h3 Y ν hY q c (Real.log z) 3 z hq2 hq1 le_rfl hz3 hκ hκ3 hc
  have h256 : ((16 : ℝ) ^ 2) ^ q ≤ 256 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16 ^ 2) hq1
    rw [Real.rpow_one] at h
    linarith
  have hEZ3 : (0 : ℝ) ≤ ∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (3 + 1) (z + 1)
          ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
        / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν :=
    integral_nonneg fun ω => Real.rpow_nonneg
      (mul_nonneg (inv_nonneg.2 (by linarith)) (integral_nonneg fun t => sq_nonneg _)) _
  refine le_trans hdom (le_trans (mul_le_mul h256 hZ3 hEZ3 (by norm_num)) (le_of_eq ?_))
  ring

end RMF
