/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.StepsSharp
import RMF.Reduction.SieveLevel

/-!
# The reduction at the sieve constant `1.001·e^{-γ}`

The constant `1.001·e^{-γ}` of `RMF.roughCount_sub_le_sieveConst` holds only for large `y` and
long windows, so here the core takes the sieve bound on the windows it uses, `(x/(r+1), x/r]` for
`r ≤ R` at the one `y` in play, rather than for every `y` and every window
`H ≥ 5y(1 + log y)³ log y`.  The large range is charged `C_s/2π`, with the fibre weights of
`RMF.sum_normSq_div_mul_succ_eq`.

* `RMF.reduction_core_window` is the reduction, given the parameters, with that hypothesis;
* `RMF.reduction_upper_window` is the reduction at its constants, with it, at `R = ⌊x^{1/4}⌋`;
* `RMF.reduction_upper_sieve` discharges it by `RMF.roughCount_sub_le_sieveConst` at level
  `D = x^{1/4}`, since every window has length `≥ √x/2` (`RMF.half_sqrt_le_window`).
-/

open MeasureTheory Filter Set
open scoped Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The large range, with the sieve on the windows -/

/-- **The fibre count from the sieve on its window**: `#{m ≤ x : m rough, ⌊x/m⌋ = r}` is at most
the rough count of `(x/(r+1), x/r]`. -/
lemma card_fibre_le_of_window {Cs : ℝ} {y : ℕ} {x : ℝ} (hx : 0 ≤ x) {r : ℕ} (hr : 0 < r)
    (hwin : (roughCount y (x / r) : ℝ) - (roughCount y (x / ((r : ℝ) + 1)) : ℝ)
      ≤ Cs * (x / r - x / ((r : ℝ) + 1)) / Real.log y) :
    (({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r}).card : ℝ)
      ≤ Cs * (x / r - x / ((r : ℝ) + 1)) / Real.log y := by
  have hcast : (({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r}).card : ℝ)
      + (roughCount y (x / ((r : ℝ) + 1)) : ℝ) ≤ (roughCount y (x / r) : ℝ) := by
    exact_mod_cast card_fibre_add_roughCount_le (y := y) hx hr
  linarith

omit [MeasurableSpace Ω] in
/-- **Step (j1) at the fibre weights, with the sieve on the windows**: if every window
`(x/(r+1), x/r]`, `r ≤ R`, holds at most `C_s (x/r - x/(r+1))/log y` rough numbers (`hwin`),
then `∑_{m ∈ s} m⁻¹|S_{x/m,y}|² ≤ (C_s/log y)∫_1^{R+1} |A(t)|²/t² dt`. -/
lemma sum_roughTerm_large_le_window {Cs : ℝ}
    {f : Ω → ArithmeticFunction ℂ} {y : ℕ} (hy : 2 ≤ y) {x : ℝ} (hx : 0 < x) {R : ℕ}
    {s : Finset ℕ} (hs0 : ∀ m ∈ s, 0 < m)
    (hmaps : ∀ m ∈ s, ⌊x / (m : ℝ)⌋₊ ∈ Finset.Icc 1 R)
    (hwin : ∀ r ∈ Finset.Icc 1 R,
      (roughCount y (x / r) : ℝ) - (roughCount y (x / ((r : ℝ) + 1)) : ℝ)
        ≤ Cs * (x / r - x / ((r : ℝ) + 1)) / Real.log y)
    (hfib : ∀ r ∈ Finset.Icc 1 R,
      s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)
        ⊆ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r})
    (ω : Ω) :
    ∑ m ∈ s, roughTerm f y x ω m
      ≤ (Cs / Real.log y)
          * ∫ t in (1 : ℝ)..((R : ℝ) + 1), ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2 := by
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  rw [sum_roughTerm_fiberwise y hx hs0 hmaps ω]
  have hterm : ∀ r ∈ Finset.Icc 1 R,
      ((s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)).card : ℝ)
          * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / x)
        ≤ Cs / Real.log y
            * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / ((r : ℝ) * ((r : ℝ) + 1))) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.1 hr).1
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
    have hcard : ((s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)).card : ℝ)
        ≤ Cs * (x / r - x / ((r : ℝ) + 1)) / Real.log y := by
      refine le_trans ?_ (card_fibre_le_of_window hx.le (by omega) (hwin r hr))
      exact_mod_cast Finset.card_le_card (hfib r hr)
    have hr0 : (r : ℝ) ≠ 0 := hrR.ne'
    have hr10 : ((r : ℝ) + 1) ≠ 0 := by positivity
    have hx0 : x ≠ 0 := hx.ne'
    have hL0 : Real.log y ≠ 0 := hL.ne'
    calc ((s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)).card : ℝ)
            * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / x)
        ≤ Cs * (x / r - x / ((r : ℝ) + 1)) / Real.log y
            * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / x) := by
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = Cs / Real.log y
            * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / ((r : ℝ) * ((r : ℝ) + 1))) := by
          field_simp
          ring
  calc ∑ r ∈ Finset.Icc 1 R,
        ((s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)).card : ℝ)
          * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / x)
      ≤ ∑ r ∈ Finset.Icc 1 R, Cs / Real.log y
          * (‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / ((r : ℝ) * ((r : ℝ) + 1))) :=
        Finset.sum_le_sum hterm
    _ = Cs / Real.log y * ∑ r ∈ Finset.Icc 1 R,
          ‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / ((r : ℝ) * ((r : ℝ) + 1)) :=
        (Finset.mul_sum _ _ _).symm
    _ = (Cs / Real.log y)
          * ∫ t in (1 : ℝ)..((R : ℝ) + 1), ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2 := by
        rw [sum_normSq_div_mul_succ_eq y R ω]

/-- **The large range at `C_s/2π`, with the sieve on the windows**: almost surely
`∑_{m large} m⁻¹|S_{x/m,y}|² ≤ (C_s/2π)·eulerLineIntegral`. -/
lemma sum_roughTerm_large_le_euler_window {Cs : ℝ} (hCs : 0 ≤ Cs)
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsBoundedRMF f μ)
    {y : ℕ} (hy : 2 ≤ y)
    (hdir : ∀ᵐ ω ∂μ, ∀ z : ℂ, 0 < z.re →
      dirichletSeries (smoothCoeff f y ω) z = randomEulerProduct f (y + 1) z ω)
    {x : ℝ} (hx : 0 < x) {R : ℕ} {s : Finset ℕ}
    (hs0 : ∀ m ∈ s, 0 < m) (hmaps : ∀ m ∈ s, ⌊x / (m : ℝ)⌋₊ ∈ Finset.Icc 1 R)
    (hwin : ∀ r ∈ Finset.Icc 1 R,
      (roughCount y (x / r) : ℝ) - (roughCount y (x / ((r : ℝ) + 1)) : ℝ)
        ≤ Cs * (x / r - x / ((r : ℝ) + 1)) / Real.log y)
    (hfib : ∀ r ∈ Finset.Icc 1 R,
      s.filter (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)
        ⊆ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r}) :
    ∀ᵐ ω ∂μ, ∑ m ∈ s, roughTerm f y x ω m
      ≤ (Cs / (2 * π)) * eulerLineIntegral f (y : ℝ) ω := by
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  filter_upwards [integral_normSq_smoothPartial_eq hf y,
    integral_Ioi_eq_eulerLineIntegral hf hy hdir] with ω h1 h2
  have hchain : ∑ m ∈ s, roughTerm f y x ω m
      ≤ (Cs / Real.log y) * ∫ u in Ioi (0 : ℝ), ‖smoothPartial f y u ω‖ ^ 2 / u ^ 2 :=
    le_trans (sum_roughTerm_large_le_window hy hx hs0 hmaps hwin hfib ω)
      (mul_le_mul_of_nonneg_left (integral_unit_le_integral_Ioi y R ω h1.1) (by positivity))
  rw [h2] at hchain
  refine hchain.trans (le_of_eq ?_)
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ### The reduction -/

/-- **The reduction, given the parameters, with the sieve on the windows**:
`E|S_x|^{2q} ≤ (Rankin bound)^q + (C_s/2π)^q E[(eulerLineIntegral)^q]`, with the hypothesis `hwin`
on `(x/(r+1), x/r]`, `r ≤ R`, in place of the sieve bound for every `y` and its side conditions. -/
theorem reduction_core_window {A cR CR Cs : ℝ}
    (hR : ∀ (y : ℕ) (x : ℝ), 2 ≤ y → 2 ≤ x →
      (smoothCount y x : ℝ)
        ≤ CR * x * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y))
    (hCR : 0 ≤ CR) (hCs : 0 ≤ Cs)
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ)
    {y : ℕ} (hy : 2 ≤ y) {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {N R : ℕ}
    (hsmall2 : ∀ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N}, 2 ≤ x / m)
    (hsmallsub : {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N} ⊆ Finset.Icc 1 N)
    (hmaps : ∀ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
      ⌊x / (m : ℝ)⌋₊ ∈ Finset.Icc 1 R)
    (hwin : ∀ r ∈ Finset.Icc 1 R,
      (roughCount y (x / r) : ℝ) - (roughCount y (x / ((r : ℝ) + 1)) : ℝ)
        ≤ Cs * (x / r - x / ((r : ℝ) + 1)) / Real.log y)
    (hfib : ∀ r ∈ Finset.Icc 1 R,
      {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N}.filter
          (fun m : ℕ => ⌊x / (m : ℝ)⌋₊ = r)
        ⊆ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ⌊x / (m : ℝ)⌋₊ = r})
    (hβ0 : 0 < cR / Real.log y) (hβ1 : cR / Real.log y ≤ 1) :
    ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
      ≤ (CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
            * (1 + (N : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))) ^ q
        + (Cs / (2 * π)) ^ q * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ := by
  obtain ⟨X, hX, hfX⟩ := hf.exists_primeValues
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hfr : IsSteinhausRMF f μ := isSteinhausRMF_iff_exists.2 ⟨X, hX, hfX⟩
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hx0 : (0 : ℝ) < x := by linarith
  have hCsπ : (0 : ℝ) ≤ Cs / (2 * π) := by positivity
  -- the large branch, integrated
  have hlarge : ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
        roughTerm f y x ω m) ^ q ∂μ
      ≤ (Cs / (2 * π)) ^ q * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ := by
    have hfun : (fun ω => ((Cs / (2 * π)) * eulerLineIntegral f (y : ℝ) ω) ^ q)
        = fun ω => (Cs / (2 * π)) ^ q * eulerLineIntegral f (y : ℝ) ω ^ q := by
      funext ω
      exact Real.mul_rpow hCsπ (eulerLineIntegral_nonneg hyR ω)
    have hint : Integrable
        (fun ω => ((Cs / (2 * π)) * eulerLineIntegral f (y : ℝ) ω) ^ q) μ := by
      rw [hfun]
      exact (integrable_eulerLineIntegral_rpow hfr (y := (y : ℝ)) hyR hq0).const_mul _
    have hbd := sum_roughTerm_large_le_euler_window hCs hfr.isBoundedRMF hy
      (dirichletSeries_smoothCoeff_eq hfr y) hx0
      (fun m hm => (rough_mem_facts (P := fun m => IsRough y m ∧ ¬ m ≤ N) hx hm).1)
      hmaps hwin hfib
    calc ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
            roughTerm f y x ω m) ^ q ∂μ
        ≤ ∫ ω, ((Cs / (2 * π)) * eulerLineIntegral f (y : ℝ) ω) ^ q ∂μ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
            Real.rpow_nonneg (Finset.sum_nonneg fun m _ => roughTerm_nonneg _ _ _ _ _) q)
            hint ?_
          filter_upwards [hbd] with ω hω
          exact Real.rpow_le_rpow
            (Finset.sum_nonneg fun m _ => roughTerm_nonneg _ _ _ _ _) hω hq0
      _ = (Cs / (2 * π)) ^ q * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ := by
          rw [hfun, integral_const_mul]
  calc ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
          roughTerm f y x ω m) ^ q ∂μ :=
        integral_rpow_le_integral_rough_sum hX hfX (y := y) hx hq0 hq1
    _ ≤ (∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ m ≤ N},
            roughTerm f y x ω m) ^ q ∂μ)
          + ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ ¬ m ≤ N},
            roughTerm f y x ω m) ^ q ∂μ :=
        integral_rpow_split hfr.isBoundedRMF y hx hq0 hq1 N
    _ ≤ (CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
            * (1 + (N : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))) ^ q
          + (Cs / (2 * π)) ^ q * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ :=
        add_le_add (integral_rpow_sum_small_le hR hCR hfr hy hx hq0 hq1 hsmallsub
          (fun m hm => ⟨(rough_mem_facts (P := fun m => IsRough y m ∧ m ≤ N) hx hm).1,
            hsmall2 m hm⟩) hβ0 hβ1) hlarge

/-- **The reduction at its constants, with the sieve on the windows**: for `q ∈ [0,1]`,
`y ≥ RMF.reductionUpperStart` with `5y(1+log y)³ log y ≤ √x/2`, and a sieve constant `C_s` given
on the windows `(x/(r+1), x/r]`, `r ≤ ⌊x^{1/4}⌋`,
`E|S_x|^{2q} ≤ (C_s/2π)^q E[(eulerLineIntegral)^q] + C((log y)^K e^{-c log x/log y})^q`, with the
constants `C`, `K`, `c` of `RMF/Reduction/StepsExplicit.lean`. -/
theorem reduction_upper_window :
    0 < reductionUpperConst ∧ 0 ≤ reductionUpperExponent ∧
      0 < reductionUpperDecay ∧ 2 ≤ reductionUpperStart ∧
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ (x : ℝ) (y : ℕ) (q Cs : ℝ), reductionUpperStart ≤ y →
          5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ Real.sqrt x / 2 → 0 ≤ q → q ≤ 1 →
          0 ≤ Cs →
          (∀ r ∈ Finset.Icc 1 ⌊x ^ (1 / 4 : ℝ)⌋₊,
            (roughCount y (x / r) : ℝ) - (roughCount y (x / ((r : ℝ) + 1)) : ℝ)
              ≤ Cs * (x / r - x / ((r : ℝ) + 1)) / Real.log y) →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ (Cs / (2 * π)) ^ q * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ
              + reductionUpperConst * (Real.log y ^ reductionUpperExponent * Real.exp
                  (-reductionUpperDecay * Real.log x / Real.log y)) ^ q := by
  obtain ⟨hA, hcR, hCR, hRank⟩ := exists_smoothCount_le_explicit
  set A := smoothCountExponent with hA_expl
  set cR := smoothCountDecay with hcR_expl
  set CR := smoothCountConst with hCR_expl
  rw [show reductionUpperConst = max 1 (max (CR + CR / cR) (roughCountConst / π)) from rfl,
    show reductionUpperExponent = A + 1 from rfl,
    show reductionUpperDecay = cR / 4 from rfl,
    show reductionUpperStart = max 4 ⌈Real.exp cR⌉₊ from rfl]
  refine ⟨lt_of_lt_of_le one_pos (le_max_left _ _), by linarith, by positivity,
    le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro f μ hf x y q Cs hy0 habs hq0 hq1 hCs hwin
  have hy4 : 4 ≤ y := le_trans (le_max_left _ _) hy0
  have hyR : (4 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy4
  have hy2N : 2 ≤ y := by omega
  have hexp1 : Real.exp 1 ≤ (y : ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  have hLy1 : (1 : ℝ) ≤ Real.log y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) hexp1
  have hcube : (8 : ℝ) ≤ (1 + Real.log y) ^ 3 * Real.log y := by
    have h2 : (2 : ℝ) ≤ 1 + Real.log y := by linarith
    have h := mul_le_mul (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 3) hLy1
      (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ (1 + Real.log y) ^ 3)
    norm_num at h
    linarith
  have hyx : 2 * (y : ℝ) ≤ Real.sqrt x := by
    have h := mul_le_mul_of_nonneg_left hcube (show (0 : ℝ) ≤ 5 * (y : ℝ) by linarith)
    linarith [habs, h]
  have hexpc : Real.exp cR ≤ (y : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right 4 _) hy0)
  have hLy : cR ≤ Real.log y := by
    rw [← Real.log_exp cR]
    exact Real.log_le_log (Real.exp_pos _) hexpc
  have hLy0 : (0 : ℝ) < Real.log y := lt_of_lt_of_le hcR hLy
  have hx64 : (64 : ℝ) ≤ x := by
    have h8 : (8 : ℝ) ≤ Real.sqrt x := by linarith
    have hx0 : (0 : ℝ) ≤ x := by
      by_contra hneg
      push Not at hneg
      rw [Real.sqrt_eq_zero_of_nonpos hneg.le] at h8
      linarith
    nlinarith [Real.sq_sqrt hx0, Real.sqrt_nonneg x]
  have hx16 : (16 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hβ0 : (0 : ℝ) < cR / Real.log y := by positivity
  have hβ1 : cR / Real.log y ≤ 1 := (div_le_one hLy0).2 hLy
  have hcore := reduction_core_window hRank hCR.le hCs hf hy2N hx1 hq0 hq1
    (N := ⌊x ^ (3 / 4 : ℝ)⌋₊) (R := ⌊x ^ (1 / 4 : ℝ)⌋₊)
    (fun m hm => two_le_div_of_le_split hx16
      (rough_mem_facts (P := fun m => IsRough y m ∧ m ≤ ⌊x ^ (3 / 4 : ℝ)⌋₊) hx1 hm).1
      (by rw [Finset.mem_filter] at hm; exact hm.2.2))
    (by
      intro m hm
      rw [Finset.mem_filter, Finset.mem_Icc] at hm
      rw [Finset.mem_Icc]
      exact ⟨hm.1.1, hm.2.2⟩)
    (fun m hm => floor_div_mem_of_split hx16
      (rough_mem_facts (P := fun m => IsRough y m ∧ ¬ m ≤ ⌊x ^ (3 / 4 : ℝ)⌋₊) hx1 hm).1
      (rough_mem_facts (P := fun m => IsRough y m ∧ ¬ m ≤ ⌊x ^ (3 / 4 : ℝ)⌋₊) hx1 hm).2
      (by rw [Finset.mem_filter] at hm; exact hm.2.2))
    hwin
    (fun r _ m hm => by
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hm
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hm.1.1.1, hm.1.1.2⟩, hm.1.2.1, hm.2⟩)
    hβ0 hβ1
  -- fold the Rankin term into `RMF.reductionUpperConst`
  set Z : ℝ := Real.log y ^ (A + 1) * Real.exp (-(cR / 4) * Real.log x / Real.log y) with hZ
  have hZ0 : (0 : ℝ) < Z := by
    rw [hZ]
    exact mul_pos (Real.rpow_pos_of_pos hLy0 _) (Real.exp_pos _)
  have hRT0 : (0 : ℝ) ≤ CR * Real.log y ^ A
      * Real.exp (-cR * Real.log x / Real.log y)
      * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (cR / Real.log y) / (cR / Real.log y)) := by
    have h1 : (0 : ℝ) < Real.log y ^ A := Real.rpow_pos_of_pos hLy0 _
    have h2 : (0 : ℝ) ≤ (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (cR / Real.log y) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  have hsmallq : (CR * Real.log y ^ A * Real.exp (-cR * Real.log x / Real.log y)
      * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (cR / Real.log y) / (cR / Real.log y))) ^ q
      ≤ max 1 (max (CR + CR / cR) (roughCountConst / π)) * Z ^ q := by
    have hrk := rankin_term_le (A := A) hcR hCR hx16 (y := y) hexp1
    calc _ ≤ ((CR + CR / cR) * Z) ^ q := by
          refine Real.rpow_le_rpow hRT0 ?_ hq0
          rw [hZ]
          linarith [hrk]
      _ = (CR + CR / cR) ^ q * Z ^ q := Real.mul_rpow (by positivity) hZ0.le
      _ ≤ max 1 (max (CR + CR / cR) (roughCountConst / π)) * Z ^ q := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hZ0.le _)
          exact le_trans (rpow_le_max_one (by positivity) hq0 hq1)
            (max_le_max_left 1 (le_max_left _ _))
  linarith

/-! ### The windows are long, and the sieve constant -/

/-- **Every window is at least `√x/2` long**: `x/r - x/(r+1) ≥ √x/2` for `1 ≤ r ≤ x^{1/4}` and
`x ≥ 16`.  With `s = x^{1/4}`, `x/(r(r+1)) ≥ s³/(s+1) ≥ s²/2`. -/
lemma half_sqrt_le_window {x : ℝ} (hx : 16 ≤ x) {r : ℕ} (hr1 : 1 ≤ r)
    (hrs : (r : ℝ) ≤ x ^ (1 / 4 : ℝ)) :
    Real.sqrt x / 2 ≤ x / r - x / ((r : ℝ) + 1) := by
  have hx0 : (0 : ℝ) < x := by linarith
  set s : ℝ := x ^ (1 / 4 : ℝ) with hsdef
  have hs0 : (0 : ℝ) < s := Real.rpow_pos_of_pos hx0 _
  have hs4 : s ^ 4 = x := by
    rw [hsdef, ← Real.rpow_natCast (x ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul hx0.le]
    norm_num
  have hs2 : s ^ 2 = Real.sqrt x := by
    rw [← hs4, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sqrt_sq (by positivity)]
  have hsge : (1 : ℝ) ≤ s := Real.one_le_rpow (by linarith) (by norm_num)
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hdiff : x / r - x / ((r : ℝ) + 1) = x / ((r : ℝ) * ((r : ℝ) + 1)) := by
    field_simp
    ring
  have hrs1 : (r : ℝ) + 1 ≤ s + 1 := by linarith
  have hprod : (r : ℝ) * ((r : ℝ) + 1) ≤ s * (s + 1) :=
    mul_le_mul hrs hrs1 (by linarith) (by linarith)
  rw [hdiff, le_div_iff₀ (by positivity), ← hs2, ← hs4]
  have h1 : s ^ 2 / 2 * ((r : ℝ) * ((r : ℝ) + 1)) ≤ s ^ 2 / 2 * (s * (s + 1)) :=
    mul_le_mul_of_nonneg_left hprod (by positivity)
  nlinarith [h1, mul_nonneg (pow_nonneg hs0.le 3) (sub_nonneg.2 hsge)]

/-- **The reduction at the sieve constant `1.001·e^{-γ}`**: `RMF.reduction_upper_window` with the
windows bounded by `RMF.roughCount_sub_le_sieveConst` at level `D = x^{1/4}`, once
`log y ≥ 10⁶`, `D^{1/(2 log y)} ≥ 40000 log² y` and `5D(1 + log D)³·20000 log y ≤ √x/2`. -/
theorem reduction_upper_sieve :
    0 < reductionUpperConst ∧ 0 ≤ reductionUpperExponent ∧
      0 < reductionUpperDecay ∧ 2 ≤ reductionUpperStart ∧
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
        ∀ (x : ℝ) (y : ℕ) (q : ℝ), reductionUpperStart ≤ y →
          5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ Real.sqrt x / 2 →
          1000000 ≤ Real.log y →
          40000 * Real.log y ^ 2 ≤ (x ^ (1 / 4 : ℝ)) ^ (1 / (2 * Real.log y)) →
          5 * x ^ (1 / 4 : ℝ) * (1 + Real.log (x ^ (1 / 4 : ℝ))) ^ 3 * (20000 * Real.log y)
            ≤ Real.sqrt x / 2 →
          0 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
            ≤ (sieveConst / (2 * π)) ^ q * ∫ ω, eulerLineIntegral f (y : ℝ) ω ^ q ∂μ
              + reductionUpperConst * (Real.log y ^ reductionUpperExponent * Real.exp
                  (-reductionUpperDecay * Real.log x / Real.log y)) ^ q := by
  obtain ⟨hC, hK, hc, hy₀, hred⟩ := reduction_upper_window (Ω := Ω)
  refine ⟨hC, hK, hc, hy₀, ?_⟩
  intro f μ hf x y q hy habs hℓ hθ herr hq0 hq1
  have hy2 : 2 ≤ y := le_trans hy₀ hy
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2
  have hℓ0 : (0 : ℝ) < Real.log y := by linarith
  -- `x ≥ 400`, from `habs`
  have hx400 : (400 : ℝ) ≤ x := by
    have h1 : (1 : ℝ) ≤ (1 + Real.log y) ^ 3 := one_le_pow₀ (by linarith)
    have h2 : (10 : ℝ) ≤ 5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y := by
      have h3 : (10 : ℝ) ≤ 5 * (y : ℝ) := by linarith
      have h4 : (1 : ℝ) ≤ (1 + Real.log y) ^ 3 * Real.log y := by nlinarith
      nlinarith
    have h20 : (20 : ℝ) ≤ Real.sqrt x := by linarith
    have hx0 : (0 : ℝ) ≤ x := by
      by_contra hneg
      push Not at hneg
      rw [Real.sqrt_eq_zero_of_nonpos hneg.le] at h20
      linarith
    nlinarith [Real.sq_sqrt hx0, Real.sqrt_nonneg x]
  have hx0 : (0 : ℝ) < x := by linarith
  have hD : (1 : ℝ) ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  refine hred f μ hf x y q sieveConst hy habs hq0 hq1 sieveConst_pos.le fun r hr => ?_
  obtain ⟨hr1, hrR⟩ := Finset.mem_Icc.1 hr
  have hrR' : (r : ℝ) ≤ x ^ (1 / 4 : ℝ) :=
    le_trans (by exact_mod_cast hrR) (Nat.floor_le (Real.rpow_pos_of_pos hx0 _).le)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hwin := half_sqrt_le_window (by linarith) hr1 hrR'
  have hH : 0 < x / r - x / ((r : ℝ) + 1) := by
    have : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
    linarith
  have h := roughCount_sub_le_sieveConst hy2 (u := x / ((r : ℝ) + 1))
    (H := x / r - x / ((r : ℝ) + 1)) (D := x ^ (1 / 4 : ℝ)) (by positivity) hH hD hℓ hθ
    (herr.trans hwin)
  rwa [show x / ((r : ℝ) + 1) + (x / r - x / ((r : ℝ) + 1)) = x / r by ring] at h

end RMF
