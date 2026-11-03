/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan

Adapted from the PrimeNumberTheoremAnd project
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, Apache 2.0, by its contributors): most
results below are explicit-constant twins of results in its files `MediumPNT`, `ZetaBounds`,
`MellinCalculus` and `SmoothExistence`, with the same proofs and the witnesses named.  Written
against commit 7715064f690d0689f30889846f4e2c5e7ec0c47e, on which this repository depends.
-/
import Architect
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.LSeries.SumCoeff
import PrimeNumberTheoremAnd.IEANTN.Mertens
import PrimeNumberTheoremAnd.MediumPNT

/-!
# The Medium PNT with explicit constants

`MediumPNT` proves `∃ c > 0, (ψ - id) =O[atTop] fun x ↦ x * exp (-c * (log x) ^ (1 / 10))`, and
the lemmas it rests on in `ZetaBounds`, `MellinCalculus` and `SmoothExistence` state their
constants existentially.  This file names every one of those constants and proves the chain
again against the names, down to the two constants of the effective PNT: the rate
`mediumPNTRate ≥ 1 / 200` and the implied constant `mediumPNTConst ≤ 10 ^ 39`.  The bound
`|ψ x - x| ≤ mediumPNTConst * (x * exp (-mediumPNTRate * (log x) ^ (1 / 10)))` past an explicit
threshold is `RMF.MediumPNTBoundExplicit`.

Nothing in the four files it complements is changed.  Most results here are `Explicit` or `_of`
twins of results there: the same proof, with the witnesses named or taken as parameters.  Where
an original proof obtains a constant from a limit or by compactness, the twin replaces that step
with a quantitative one: the smoothing function (`bumpNu`), `ζ` near `s = 1`
(`ZetaNear1BndAdd`), the zero-free box `|t| ≤ 3` (`ZetaNoZerosInBoxThree`), and `ζ'/ζ` on the
segment that `I5Bound` bounds by compactness (`logDeriv_zeta_le_smallT`).

## Main results

* `mediumPNTRate`: the exponent constant `zetaBndHoloA ^ (1 / 10) / 4 ≈ 6.8 · 10⁻³`, and
  `mediumPNTRate_ge : 1 / 200 ≤ mediumPNTRate`.
* `mediumPNTConst`: the implied constant, about `6 · 10³⁷`, and
  `mediumPNTConst_le : mediumPNTConst ≤ 10 ^ 39`.

The four sections below follow the files they complement, in dependency order.
-/

-- PNT+'s style settings (its lakefile), which this file follows.
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.longFile 0

set_option lang.lemmaCmd true

section SmoothExistenceExplicit

open MeasureTheory Set Real

open scoped ContDiff

/-! ## An explicit smoothing function

`SmoothExistence` hands over a bump function with no formula, so every constant downstream is an
unknown functional of it.  Everything that consumes it asks only for `ContDiff ℝ 1`, and a
piecewise polynomial supplies that, so here is a concrete one.

Writing `ν` through `max _ 0` rather than an `if` means the smoothness argument has a single bad
point instead of two, and `hasDerivAt_of_hasDerivAt_of_ne` handles it in one step. -/

noncomputable section ExplicitBump

/-! ### Step 0: the positive-part square is `C¹` -/

/-- `s ↦ (s⁺)²` has derivative `2 t⁺` at every `t`.  This is the only gluing in the file. -/
theorem hasDerivAt_posPart_sq (t : ℝ) :
    HasDerivAt (fun s : ℝ => (max s 0) ^ 2) (2 * max t 0) t := by
  have key : ∀ y : ℝ, y ≠ 0 → HasDerivAt (fun s : ℝ => (max s 0) ^ 2) (2 * max y 0) y := by
    intro y hy
    rcases lt_trichotomy y 0 with h | h | h
    · rw [max_eq_right h.le, mul_zero]
      refine (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [eventually_lt_nhds h] with s hs
      simp [max_eq_right hs.le]
    · exact absurd h hy
    · rw [max_eq_left h.le]
      refine ((hasDerivAt_pow 2 y).congr_deriv (by push_cast; ring)).congr_of_eventuallyEq ?_
      filter_upwards [eventually_gt_nhds h] with s hs
      simp [max_eq_left hs.le]
  rcases eq_or_ne t 0 with rfl | ht
  · exact hasDerivAt_of_hasDerivAt_of_ne (f := fun s : ℝ => (max s 0) ^ 2)
      (g := fun s : ℝ => 2 * max s 0) key (by fun_prop) (by fun_prop)
  · exact key t ht

/-! ### The bump -/

/-- The normalising constant `(log 4 - 75/64)⁻¹ ≈ 4.6637579`. -/
def bumpC : ℝ := (Real.log 4 - 75 / 64)⁻¹

/-- `ν x = C · ((x - 1/2)(2 - x))₊²`, i.e. `C (x-1/2)²(2-x)²` on `[1/2,2]` and `0` elsewhere. -/
def bumpNu (x : ℝ) : ℝ := bumpC * (max ((x - 1 / 2) * (2 - x)) 0) ^ 2

theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

theorem bumpDen_pos : 0 < Real.log 4 - 75 / 64 := by
  have h := Real.log_two_gt_d9
  rw [log_four]
  norm_num at h ⊢
  linarith

theorem bumpC_pos : 0 < bumpC := inv_pos.2 bumpDen_pos

/-- `bumpC ≤ 5`, from `log 4 > 1.3862`.  Crude; the true value is `≈ 4.664`. -/
theorem bumpC_le : bumpC ≤ 5 := by
  have h := Real.log_two_gt_d9
  have hd : (1 : ℝ) / 5 ≤ Real.log 4 - 75 / 64 := by
    rw [log_four]; norm_num at h ⊢; linarith
  rw [bumpC, inv_le_comm₀ bumpDen_pos (by norm_num)]
  linarith

/-! ### Property 1: nonnegativity -/

theorem bumpNu_nonneg (x : ℝ) : 0 ≤ bumpNu x :=
  mul_nonneg bumpC_pos.le (sq_nonneg _)

/-! ### Property 2: support -/

theorem bumpNu_eq_zero_of_nonpos {x : ℝ} (h : (x - 1 / 2) * (2 - x) ≤ 0) : bumpNu x = 0 := by
  simp only [bumpNu, max_eq_right h]; ring

theorem bumpNu_support : Function.support bumpNu ⊆ Icc (1 / 2 : ℝ) 2 := by
  intro x hx
  simp only [Function.mem_support] at hx
  by_contra hmem
  refine hx (bumpNu_eq_zero_of_nonpos ?_)
  simp only [mem_Icc, not_and_or, not_le] at hmem
  rcases hmem with h | h
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

/-! ### Property 3: `C¹` -/

theorem hasDerivAt_bumpNu (x : ℝ) :
    HasDerivAt bumpNu (bumpC * (2 * max ((x - 1 / 2) * (2 - x)) 0 * (5 / 2 - 2 * x))) x := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' x
  have hg : HasDerivAt (fun y : ℝ => (y - 1 / 2) * (2 - y)) (5 / 2 - 2 * x) x :=
    ((hid.sub_const (1 / 2 : ℝ)).mul
      ((hasDerivAt_const x (2 : ℝ)).sub hid)).congr_deriv (by simp only [Pi.sub_apply]; ring)
  exact (((hasDerivAt_posPart_sq _).comp x hg).const_mul bumpC)

/-- `‖bumpNu'‖ ≤ 27 bumpC / 4 ≈ 31.5` on the support.  Crude -- the true maximum is about
`3.03` -- but explicit, which is the point: this is the quantity `MellinOfPsi` takes a
maximum of. -/
theorem bumpNu_deriv_le {x : ℝ} (hx : x ∈ Icc (1 / 2 : ℝ) 2) :
    ‖deriv bumpNu x‖ ≤ 27 * bumpC / 4 := by
  rw [(hasDerivAt_bumpNu x).deriv, Real.norm_eq_abs]
  obtain ⟨h1, h2⟩ := hx
  have hc : 0 < bumpC := bumpC_pos
  have hm0 : (0 : ℝ) ≤ max ((x - 1 / 2) * (2 - x)) 0 := le_max_right _ _
  have hm : max ((x - 1 / 2) * (2 - x)) 0 ≤ 9 / 4 := by
    refine max_le ?_ (by norm_num)
    nlinarith
  have hb : |5 / 2 - 2 * x| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc |bumpC * (2 * max ((x - 1 / 2) * (2 - x)) 0 * (5 / 2 - 2 * x))|
      = bumpC * (2 * max ((x - 1 / 2) * (2 - x)) 0) * |5 / 2 - 2 * x| := by
        rw [abs_mul, abs_of_pos hc, abs_mul, abs_of_nonneg (by positivity)]
        ring
    _ ≤ bumpC * (2 * (9 / 4)) * (3 / 2) := by gcongr
    _ = 27 * bumpC / 4 := by ring

theorem bumpNu_contDiff : ContDiff ℝ 1 bumpNu := by
  refine contDiff_one_iff_deriv.2 ⟨fun x => (hasDerivAt_bumpNu x).differentiableAt, ?_⟩
  have hd : deriv bumpNu =
      fun x : ℝ => bumpC * (2 * max ((x - 1 / 2) * (2 - x)) 0 * (5 / 2 - 2 * x)) :=
    funext fun x => (hasDerivAt_bumpNu x).deriv
  rw [hd]
  fun_prop

/-! ### Property 4: total mass -/

theorem bumpNu_integral : ∫ x in Ici (0 : ℝ), bumpNu x / x = 1 := by
  have h12 : (1 / 2 : ℝ) ≤ 2 := by norm_num
  -- restrict to `Ioc (1/2) 2`
  have hset : ∫ x in Ici (0 : ℝ), bumpNu x / x = ∫ x in Ioc (1 / 2 : ℝ) 2, bumpNu x / x := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici ?_ ?_
    · intro x hx; exact le_of_lt (by linarith [hx.1] : (0:ℝ) < x)
    · rintro x ⟨-, hx⟩
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
      rw [bumpNu_eq_zero_of_nonpos ?_, zero_div]
      rcases hx with h | h
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  rw [hset, ← intervalIntegral.integral_of_le h12]
  -- replace the bump by its polynomial form on `[1/2, 2]`
  have hcongr : ∫ x in (1 / 2 : ℝ)..2, bumpNu x / x
      = ∫ x in (1 / 2 : ℝ)..2, bumpC * (x ^ 3 - 5 * x ^ 2 + 33 / 4 * x - 5 + 1 / x) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [uIcc_of_le h12, mem_Icc] at hx
    have hx0 : x ≠ 0 := by intro h; rw [h] at hx; linarith [hx.1]
    have hmax : max ((x - 1 / 2) * (2 - x)) 0 = (x - 1 / 2) * (2 - x) :=
      max_eq_left (mul_nonneg (by linarith [hx.1]) (by linarith [hx.2]))
    simp only [bumpNu, hmax]
    field_simp
    ring
  rw [hcongr]
  -- fundamental theorem of calculus with the explicit antiderivative
  have hFTC : ∫ x in (1 / 2 : ℝ)..2, bumpC * (x ^ 3 - 5 * x ^ 2 + 33 / 4 * x - 5 + 1 / x)
      = bumpC * ((2:ℝ) ^ 4 / 4 - 5 * 2 ^ 3 / 3 + 33 / 8 * 2 ^ 2 - 5 * 2 + Real.log 2)
        - bumpC * ((1/2:ℝ) ^ 4 / 4 - 5 * (1/2) ^ 3 / 3 + 33 / 8 * (1/2) ^ 2 - 5 * (1/2)
            + Real.log (1/2)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => bumpC * (y ^ 4 / 4 - 5 * y ^ 3 / 3 + 33 / 8 * y ^ 2 - 5 * y + Real.log y))
      (fun x hx => ?_) ?_
    · rw [uIcc_of_le h12, mem_Icc] at hx
      have hx0 : x ≠ 0 := by intro h; rw [h] at hx; linarith [hx.1]
      have h1 : HasDerivAt (fun y : ℝ => y ^ 4 / 4) (x ^ 3) x :=
        ((hasDerivAt_pow 4 x).div_const 4).congr_deriv (by push_cast; ring)
      have h2 : HasDerivAt (fun y : ℝ => 5 * y ^ 3 / 3) (5 * x ^ 2) x :=
        (((hasDerivAt_pow 3 x).const_mul (5:ℝ)).div_const 3).congr_deriv (by push_cast; ring)
      have h3 : HasDerivAt (fun y : ℝ => 33 / 8 * y ^ 2) (33 / 4 * x) x :=
        ((hasDerivAt_pow 2 x).const_mul (33 / 8 : ℝ)).congr_deriv (by push_cast; ring)
      have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' x
      have h4 : HasDerivAt (fun y : ℝ => 5 * y) (5 : ℝ) x :=
        (hid.const_mul (5 : ℝ)).congr_deriv (by ring)
      have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
      exact ((((h1.sub h2).add h3).sub h4).add hlog).congr_deriv (by
        rw [one_div]) |>.const_mul bumpC
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le h12]
      intro x hx
      have hx0 : x ≠ 0 := by simp only [mem_Icc] at hx; intro h; rw [h] at hx; linarith [hx.1]
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := exact hx0))
  rw [hFTC]
  have hlog2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [hlog2]
  have hkey : bumpC * (2 * Real.log 2 - 75 / 64) = 1 := by
    rw [bumpC, ← log_four]; exact inv_mul_cancel₀ bumpDen_pos.ne'
  linear_combination hkey

end ExplicitBump

end SmoothExistenceExplicit

/-! ## Mellin bounds with their constants supplied (complements `MellinCalculus`) -/

section MellinCalculusExplicit

open scoped ContDiff

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

local notation "𝓜" => mellin

/-- `MellinOfPsi` with the maximum of `‖ν'‖` supplied rather than obtained from compactness.
The `C` of `MellinOfPsi` is the `D` here at the argmax, so nothing is lost; what is gained is
that a caller who knows `ν` can pass a numeral. -/
lemma MellinOfPsiExplicit {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) {D : ℝ}
    (hD : ∀ x ∈ Icc (1 / 2 : ℝ) 2, ‖deriv ν x‖ ≤ D) :
    ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
    ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ (D * 2 ^ (2 : ℝ) * (3 / 2)) * ‖s‖⁻¹ := by
  have hD0 : (0 : ℝ) ≤ D := le_trans (norm_nonneg _) (hD 1 (by norm_num))
  let f := fun (x : ℝ) ↦ ‖deriv ν x‖
  let σ₂ : ℝ := 2
  intro σ₁ σ₁pos s hs₁ hs₂
  have s_ne_zero: s ≠ 0 := fun h ↦ by linarith [zero_re ▸ h ▸ hs₁]
  simp only [mellin, MellinOfPsi_aux diffν suppν s_ne_zero, norm_mul, smul_eq_mul, mul_comm]
  gcongr
  · simp
  calc
    _ ≤ ∫ (x : ℝ) in Ioi 0, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
    _ = ∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
    _ ≤ ‖∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖‖ :=
        le_abs_self _
    _ ≤ _ := ?_
  · simp_rw [norm_integral_le_integral_norm]
  · apply SetIntegral.integral_eq_integral_inter_of_support_subset_Icc
    · simp only [Function.support_abs, Function.support_mul, Function.support_ofReal]
      apply subset_trans (by apply inter_subset_left) <| Function.support_deriv_subset_Icc suppν
    · exact (Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num)
  · have := intervalIntegral.norm_integral_le_of_norm_le_const' (C := D * 2 ^ σ₂)
      (f := fun x ↦ f x * ‖(x : ℂ) ^ s‖) (a := (1 / 2 : ℝ)) ( b := 2) (by norm_num) ?_
    · simp only [Real.norm_eq_abs, norm_real, norm_mul] at this ⊢
      rwa [(by norm_num: |(2 : ℝ) - 1 / 2| = 3 / 2),
          intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at this
    · intro x hx;
      have f_bound : f x ≤ D := hD x hx
      have pow_bound : ‖(x : ℂ) ^ s‖ ≤ 2 ^ σ₂ := by
        rw [norm_cpow_eq_rpow_re_of_pos (by linarith [mem_Icc.mp hx])]
        have xpos : 0 ≤ x := by linarith [(mem_Icc.mp hx).1]
        have h := rpow_le_rpow xpos (mem_Icc.mp hx).2 (by linarith : 0 ≤ s.re)
        exact le_trans h <| rpow_le_rpow_of_exponent_le (by norm_num) hs₂
      convert! mul_le_mul f_bound pow_bound (norm_nonneg _) hD0 using 1; simp [f]

/-- The content of `MellinOfSmooth1b`, abstracted over the bound on `𝓜 ν` so that both the
existential and the explicit form can use it. -/
lemma MellinOfSmooth1b_of {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) {C : ℝ}
    (hC : ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
      ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹) :
    ∀ (σ₁ : ℝ) (_ : 0 < σ₁)
    (s) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
    ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹ := by
  intro σ₁ σ₁pos s hs1 hs2 ε εpos ε_lt_one
  rw [MellinOfSmooth1a diffν suppν εpos <| lt_of_le_of_lt' hs1 σ₁pos]
  have hh1 : ε * σ₁ ≤ (ε * s).re := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  have hh2 : (ε * s).re ≤ 2 := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  calc
    ‖s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ =
        ‖s⁻¹‖ * ‖𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ := by simp
    _                        ≤ ‖s⁻¹‖ * (C * (ε * ‖s‖)⁻¹) := by
      gcongr
      convert! hC (ε * σ₁) (by positivity) (ε * s) hh1 hh2
      simp [abs_eq_self.mpr εpos.le]
    _                        = C * (ε * ‖s‖ ^ 2)⁻¹ := by
      simp only [norm_inv, mul_inv_rev]
      ring

/-- `MellinOfSmooth1b` with the maximum of `‖ν'‖` supplied. -/
lemma MellinOfSmooth1bExplicit {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) {D : ℝ}
    (hD : ∀ x ∈ Icc (1 / 2 : ℝ) 2, ‖deriv ν x‖ ≤ D) :
    ∀ (σ₁ : ℝ) (_ : 0 < σ₁)
    (s) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
    ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖
      ≤ (D * 2 ^ (2 : ℝ) * (3 / 2)) * (ε * ‖s‖ ^ 2)⁻¹ :=
  MellinOfSmooth1b_of diffν suppν (MellinOfPsiExplicit diffν suppν hD)

/-- `|x^ε - 1| ≤ 2 log 2 · ε` on the support `[1/2, 2]`, for `0 < ε ≤ 1`. -/
lemma abs_rpow_sub_one_le {x ε : ℝ} (hx : x ∈ Icc (1 / 2 : ℝ) 2) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |x ^ ε - 1| ≤ 2 * Real.log 2 * ε := by
  obtain ⟨h1, h2⟩ := hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : |Real.log x| ≤ Real.log 2 := by
    rw [abs_le]
    constructor
    · have := Real.log_le_log (by norm_num) h1
      rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv] at this
      linarith
    · have := Real.log_le_log hx0 h2
      linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hu : |ε * Real.log x| ≤ 1 := by
    rw [abs_mul, abs_of_pos hε]
    nlinarith [abs_nonneg (Real.log x)]
  have hexp : x ^ ε = Real.exp (ε * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0, mul_comm]
  rw [hexp]
  have h := Real.abs_exp_sub_one_le hu
  rw [abs_mul, abs_of_pos hε] at h
  nlinarith [abs_nonneg (Real.log x)]

/-- `‖𝓜 ν ε - 1‖ ≤ 2 log 2 · ε` for `0 < ε ≤ 1`, for any nonnegative `ν` supported in
`[1/2, 2]` with `∫ ν(x)/x = 1`.  This is the explicit form of `MellinOfDeltaSpikeAt1_asymp`,
proved exactly as its blueprint says: `𝓜ν(ε) - 1 = ∫ (x^ε - 1) ν(x)/x`. -/
lemma mellin_sub_one_le {ν : ℝ → ℝ}
    (suppν : ν.support ⊆ Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖𝓜 (fun x ↦ (ν x : ℂ)) ε - 1‖ ≤ 2 * Real.log 2 * ε := by
  -- the mass integrand is integrable, because its integral is `1 ≠ 0`
  have hB : IntegrableOn (fun t : ℝ ↦ ν t / t) (Ioi 0) := by
    by_contra h
    rw [MeasureTheory.integral_undef h] at mass_one
    norm_num at mass_one
  -- the pointwise bound, valid on all of `Ioi 0` because `ν` vanishes off `[1/2,2]`
  have key : ∀ t ∈ Ioi (0 : ℝ),
      |(t ^ ε - 1) * (ν t / t)| ≤ 2 * Real.log 2 * ε * |ν t / t| := by
    intro t ht
    by_cases hmem : t ∈ Icc (1 / 2 : ℝ) 2
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_rpow_sub_one_le hmem hε hε1) (abs_nonneg _)
    · have : ν t = 0 := by
        by_contra hne
        exact hmem (suppν (Function.mem_support.mpr hne))
      simp [this]
  have hA : IntegrableOn (fun t : ℝ ↦ (t ^ ε - 1) * (ν t / t)) (Ioi 0) := by
    refine Integrable.mono' (hB.abs.const_mul (2 * Real.log 2 * ε)) ?_ ?_
    · refine (AEStronglyMeasurable.mul ?_ hB.aestronglyMeasurable)
      exact ((Real.continuous_rpow_const hε.le).sub continuous_const).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs]
      exact key t ht
  -- the identity
  have main : 𝓜 (fun x ↦ (ν x : ℂ)) ε - 1
      = (((∫ t in Ioi 0, (t ^ ε - 1) * (ν t / t)) : ℝ) : ℂ) := by
    unfold mellin
    have hpt : ∀ t ∈ Ioi (0 : ℝ), ((t : ℂ) ^ ((ε : ℂ) - 1)) • ((ν t : ℝ) : ℂ)
        = ((((t ^ ε - 1) * (ν t / t) : ℝ)) : ℂ) + (((ν t / t : ℝ)) : ℂ) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := ht
      have : ((t : ℂ) ^ ((ε : ℂ) - 1)) = (((t ^ (ε - 1) : ℝ)) : ℂ) := by
        rw [Complex.ofReal_cpow ht0.le]
        push_cast
        ring_nf
      rw [this, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
      congr 1
      rw [Real.rpow_sub ht0, Real.rpow_one]
      field_simp
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      integral_add hA.ofReal hB.ofReal, integral_complex_ofReal,
      integral_complex_ofReal, mass_one]
    push_cast
    ring
  rw [main, Complex.norm_real, Real.norm_eq_abs]
  calc |∫ t in Ioi 0, (t ^ ε - 1) * (ν t / t)|
      ≤ ∫ t in Ioi 0, |(t ^ ε - 1) * (ν t / t)| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0:ℝ)))
            (fun t => (t ^ ε - 1) * (ν t / t))
    _ ≤ ∫ t in Ioi 0, 2 * Real.log 2 * ε * |ν t / t| := by
        refine setIntegral_mono_on hA.abs (hB.abs.const_mul _) measurableSet_Ioi key
    _ = 2 * Real.log 2 * ε * ∫ t in Ioi 0, |ν t / t| := by
        rw [integral_const_mul]
    _ = 2 * Real.log 2 * ε := by
        rw [setIntegral_congr_fun measurableSet_Ioi
          (fun t ht => abs_of_nonneg (div_nonneg (νnonneg t ht) (le_of_lt ht))), mass_one,
          mul_one]

/-- The explicit form of `MellinOfSmooth1c`: `‖𝓜(ν_ε)(1) - 1‖ ≤ 2 log 2 · ε` for `0 < ε ≤ 1`,
with no threshold below `1` and the constant `2 log 2 ≈ 1.386`. -/
lemma MellinOfSmooth1cBound {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1‖ ≤ 2 * Real.log 2 * ε := by
  rw [MellinOfSmooth1a diffν suppν hε (s := 1) (by norm_num)]
  simp only [inv_one, one_mul, mul_one]
  exact mellin_sub_one_le suppν νnonneg mass_one hε hε1

end MellinCalculusExplicit

/-! ## The zeta bounds with named constants (complements `ZetaBounds`) -/

section ZetaBoundsExplicit

open Complex Topology Filter Interval Set Asymptotics

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv riemannZeta

local notation "ζ₀" => riemannZeta0

/-! ### Named witnesses

`ZetaBounds` states its bounds from `ZetaUpperBnd` to `ZetaZeroFree` as `∃ A, ∃ C, …`, with the
witnesses written out inside the proofs.  Here each witness is a `def`, and each bound has an
`Explicit` twin proved for it by the original argument, with one exception: `ZetaNear1BndExact`
takes its constant from an `IsBigO` near `1` and compactness, and its twin `ZetaNear1BndExplicit`
is read off the identity for `ζ₀` instead (`ZetaNear1BndAdd`).  No estimate changes; the
constants simply stop being existentially quantified. -/

/-- The strip width in `ZetaUpperBnd`, `ZetaDerivUpperBnd` and `Zeta_diff_Bnd`. -/
noncomputable def zetaStripA : ℝ := 1 / 2

lemma zetaStripA_mem : zetaStripA ∈ Ioc 0 (1 / 2) := by
  constructor <;> norm_num [zetaStripA]

/-- The constant in `ZetaUpperBnd`; the `2` comes from `ZetaBnd_aux1`. -/
noncomputable def zetaUpperC : ℝ := Real.exp zetaStripA * (5 + 8 * 2)

lemma zetaUpperC_pos : 0 < zetaUpperC := by
  unfold zetaUpperC; positivity

@[blueprint
  (title := "ZetaUpperBndExplicit")
  (statement := /--
  For $3 < |t|$ and $1 - \frac{1}{2\log|t|} \le \sigma \le 2$,
  $$
  |\zeta(\sigma+tI)| \le e^{1/2}\cdot 21\cdot \log |t|.
  $$
  -/)
  (proof := /-- The proof of Lemma \ref{ZetaUpperBnd}, with its two witnesses named. -/)
  (latexEnv := "lemma")]
lemma ZetaUpperBndExplicit (σ : ℝ) (t : ℝ) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - zetaStripA / Real.log |t|) 2) :
    ‖ζ (σ + t * I)‖ ≤ zetaUpperC * Real.log |t| := by
  obtain ⟨σ_ge, σ_le⟩ := hσ
  obtain ⟨Npos, _, _, _, σPos, neOne⟩ := UpperBnd_aux zetaStripA_mem t_gt σ_ge
  rw [← Zeta0EqZeta Npos (by simp [σPos]) neOne]
  apply le_trans (by apply norm_add₄_le) ?_
  convert! ZetaUpperBnd' zetaStripA_mem t_gt ⟨σ_ge, σ_le⟩ using 1; simp

/-- The constant in `ZetaDerivUpperBnd`. -/
noncomputable def zetaDerivUpperC : ℝ := Real.exp zetaStripA * 59

lemma zetaDerivUpperC_pos : 0 < zetaDerivUpperC := by
  unfold zetaDerivUpperC; positivity

@[blueprint
  (title := "ZetaDerivUpperBndExplicit")
  (statement := /--
  For $3 < |t|$ and $1 - \frac{1}{2\log|t|} \le \sigma \le 2$,
  $$
  |\zeta'(\sigma+tI)| \le e^{1/2}\cdot 59\cdot (\log |t|)^2.
  $$
  -/)
  (proof := /-- The proof of Lemma \ref{ZetaDerivUpperBnd}, with its two witnesses named. -/)
  (latexEnv := "lemma")]
lemma ZetaDerivUpperBndExplicit (σ : ℝ) (t : ℝ) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - zetaStripA / Real.log |t|) 2) :
    ‖ζ' (σ + t * I)‖ ≤ zetaDerivUpperC * Real.log |t| ^ 2 := by
  unfold zetaDerivUpperC
  obtain ⟨σ_ge, σ_le⟩ := hσ
  obtain ⟨Npos, N_le_t, _, _, σPos, neOne⟩ := UpperBnd_aux zetaStripA_mem t_gt σ_ge
  rw [← DerivZeta0EqDerivZeta Npos (by simp [σPos]) neOne]
  set N : ℕ := ⌊|t|⌋₊
  rw [(HasDerivAtZeta0 Npos (s := σ + t * I) (by simp [σPos]) neOne).deriv]
  dsimp only [ζ₀']
  rw [← add_assoc]
  set aa := ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)
  set bb := -(N : ℂ) ^ (1 - (σ + t * I)) / (1 - (σ + t * I)) ^ 2
  set cc := (Real.log N) * (N : ℂ) ^ (1 - (σ + t * I)) / (1 - (σ + t * I))
  set dd := (Real.log N) * (N : ℂ) ^ (-(σ + t * I)) / 2
  set ee := 1 * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(σ + t * I) - 1)
  set ff := (σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(σ + t * I) - 1) * -(Real.log x)
  rw [(by ring : aa + (bb + cc) + dd + ee + ff = aa + bb + cc + dd + ee + ff)]
  apply le_trans (by apply norm_add₆_le) ?_
  convert ZetaDerivUpperBnd' zetaStripA_mem t_gt ⟨σ_ge, σ_le⟩

@[blueprint
  (title := "ZetaNear1BndAdd")
  (statement := /--
  For all $\sigma > 1$,
  $$
  |\zeta(\sigma)| \le \frac{3}{2} + \frac{1}{\sigma-1}.
  $$
  -/)
  (proof := /--
  Take $N=1$ in Lemma \ref{Zeta0EqZeta}.  The sum contributes $1$, the term $-N^{1-s}/(1-s)$
  is $1/(\sigma-1)$, the term $-N^{-s}/2$ is $-1/2$, and Lemma \ref{ZetaBnd_aux1b} bounds the
  remaining integral by $1/\sigma$, so that $\sigma$ times it is at most $1$.
  -/)
  (latexEnv := "lemma")]
lemma ZetaNear1BndAdd {σ : ℝ} (hσ : 1 < σ) : ‖ζ σ‖ ≤ 3 / 2 + 1 / (σ - 1) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hsne0 : (σ : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
  have hs1 : (σ : ℂ) ≠ 1 := by
    simp only [ne_eq, Complex.ofReal_eq_one]; linarith
  have hre : 0 < ((σ : ℂ)).re := by simpa using hσ0
  have hsub : (1 : ℂ) - (σ : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hsub' : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hs1
  -- the tail integral, bounded by `ZetaBnd_aux1b` at `N = 1`, `t = 0`
  have hJbnd :
      ‖∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ ((σ : ℂ) + 1)‖ ≤ 1 / σ := by
    have h := ZetaBnd_aux1b 1 le_rfl (σ := σ) (t := 0) hσ0
    simpa using h
  have hcongr : (1 : ℂ) + -1 / (1 - (σ : ℂ)) + -1 / 2 = 1 / 2 + 1 / ((σ : ℂ) - 1) := by
    field_simp
    ring
  rw [← Zeta0EqZeta (N := 1) Nat.one_pos hre hs1]
  simp only [riemannZeta0, Nat.cast_one, Nat.cast_zero, Finset.sum_range_succ,
    Finset.sum_range_zero, Complex.one_cpow, Complex.zero_cpow hsne0, div_zero, zero_add,
    div_one]
  rw [hcongr]
  refine norm_add₃_le.trans ?_
  have e1 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have e2 : ‖1 / ((σ : ℂ) - 1)‖ = 1 / (σ - 1) := by
    rw [show ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, norm_div, norm_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < σ - 1)]
  have e3 : ‖(σ : ℂ) * ∫ x in Ioi (1 : ℝ),
      ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ ((σ : ℂ) + 1)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ0]
    calc σ * ‖∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ ((σ : ℂ) + 1)‖
        ≤ σ * (1 / σ) := by gcongr
      _ = 1 := by field_simp
  rw [e1, e2]
  linarith

@[blueprint
  (title := "ZetaNear1BndExplicit")
  (statement := /--
  For all $1 < \sigma \le 2$,
  $$
  |\zeta(\sigma)| \le \frac{5}{2(\sigma-1)}.
  $$
  -/)
  (proof := /--
  On $(1,2]$ one has $\frac32(\sigma-1) + 1 \le \frac52$, so this is Lemma
  \ref{ZetaNear1BndAdd} multiplied through by $\sigma-1$.
  -/)
  (latexEnv := "lemma")]
lemma ZetaNear1BndExplicit (σ : ℝ) (hσ : σ ∈ Ioc 1 2) : ‖ζ σ‖ ≤ 5 / 2 / (σ - 1) := by
  obtain ⟨h1, h2⟩ := hσ
  have hpos : (0 : ℝ) < σ - 1 := by linarith
  rw [le_div_iff₀ hpos]
  calc ‖ζ (σ : ℂ)‖ * (σ - 1) ≤ (3 / 2 + 1 / (σ - 1)) * (σ - 1) := by
        gcongr
        exact ZetaNear1BndAdd h1
    _ = 3 / 2 * (σ - 1) + 1 := by field_simp
    _ ≤ 5 / 2 := by linarith

/-! ### Off the real axis: the pole disc

`ZetaNear1BndAdd` bounds `ζ` on the real axis to the right of 1.  The same `ζ₀(1, s)` identity
gives the complex statement, because `ZetaBnd_aux1b`'s tail bound carries no condition on
`Im s`; and that immediately produces an explicit disc around the pole in which `ζ` cannot
vanish.  This is the `|t|` small end of a zero-free box, and unlike the `3 < |t|` chain above
it needs no logarithm to be large. -/

/-- **`ζ(s) - 1/(s-1)` is explicitly bounded on `Re s > 0`.**

The complex form of `ZetaNear1BndAdd`, read off `ζ₀(1, s)`: the sum contributes `1`, the pole
term is `1/(s-1)`, the half-term is `-1/2`, and `ZetaBnd_aux1b` — which carries no condition on
`Im s` — bounds the remaining integral by `1/Re s`. -/
lemma ZetaSubPole_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖ζ s - 1 / (s - 1)‖ ≤ 1 / 2 + ‖s‖ / s.re := by
  have hsne0 : s ≠ 0 := fun h => by simp [h] at hs
  set J : ℂ := ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1) with hJdef
  have hJ : ‖J‖ ≤ 1 / s.re := by
    have h := ZetaBnd_aux1b 1 le_rfl (σ := s.re) (t := s.im) hs
    rw [Complex.re_add_im s] at h
    simpa [hJdef] using h
  rw [← Zeta0EqZeta (N := 1) Nat.one_pos hs hs1]
  simp only [riemannZeta0, Nat.cast_one, Nat.cast_zero, Finset.sum_range_succ,
    Finset.sum_range_zero, Complex.one_cpow, Complex.zero_cpow hsne0, div_zero, zero_add,
    div_one, ← hJdef]
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hrw : (1 : ℂ) + -1 / (1 - s) + -1 / 2 + s * J - 1 / (s - 1) = 1 / 2 + s * J := by
    field_simp
    ring
  rw [hrw]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  have hmul := mul_le_mul_of_nonneg_left hJ (norm_nonneg s)
  have hdiv : ‖s‖ / s.re = ‖s‖ * (1 / s.re) := by ring
  rw [hdiv]
  linarith

/-- If `ζ s = 0` then the pole term must be dominated by the rest. -/
lemma zeta_ne_zero_of_near_one {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (h : ‖s - 1‖ * (1 / 2 + ‖s‖ / s.re) < 1) : ζ s ≠ 0 := by
  intro hz
  have h0 := ZetaSubPole_le hs hs1
  rw [hz, zero_sub, norm_neg, norm_div, norm_one] at h0
  have hpos : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
  rw [div_le_iff₀ hpos] at h0
  nlinarith [h0, h]

/-- **`ζ` has no zero within `1/3` of the pole.** -/
lemma zeta_ne_zero_of_dist_le_third {s : ℂ} (hs1 : s ≠ 1) (h : ‖s - 1‖ ≤ 1 / 3) :
    ζ s ≠ 0 := by
  have hre : |s.re - 1| ≤ 1 / 3 := by
    have := Complex.abs_re_le_norm (s - 1)
    simpa using this.trans h
  have hs : 0 < s.re := by
    rw [abs_le] at hre; linarith
  have hsn : ‖s‖ ≤ 4 / 3 := by
    have := norm_sub_norm_le s 1
    simp only [norm_one] at this
    linarith
  refine zeta_ne_zero_of_near_one hs hs1 ?_
  have hre23 : 2 / 3 ≤ s.re := by rw [abs_le] at hre; linarith
  have hM : 1 / 2 + ‖s‖ / s.re ≤ 5 / 2 := by
    have : ‖s‖ / s.re ≤ (4 / 3) / (2 / 3) :=
      div_le_div₀ (by norm_num) hsn (by norm_num) hre23
    linarith
  have hnn : (0 : ℝ) ≤ ‖s - 1‖ := norm_nonneg _
  nlinarith [hnn, h, hM]

/-- The constant in `ZetaLowerBound3`. -/
noncomputable def zetaLowerBound3c : ℝ :=
  1 / ((5 / 2 : ℝ) ^ ((3 : ℝ) / 4) * (2 * zetaUpperC) ^ ((1 : ℝ) / 4))

lemma zetaLowerBound3c_pos : 0 < zetaLowerBound3c := by
  have := zetaUpperC_pos
  unfold zetaLowerBound3c
  positivity

@[blueprint
  (title := "ZetaLowerBound3Explicit")
  (statement := /--
  For $1 < \sigma \le 2$ and $3 < |t|$, with
  $c = \left((5/2)^{3/4}\,(2e^{1/2}\cdot 21)^{1/4}\right)^{-1}$,
  $$
  \frac{c\,(\sigma-1)^{3/4}}{(\log|t|)^{1/4}} \le |\zeta(\sigma+tI)|.
  $$
  -/)
  (proof := /-- The proof of Lemma \ref{ZetaLowerBound3}, with its witness named. -/)
  (latexEnv := "lemma")]
lemma ZetaLowerBound3Explicit {σ : ℝ} (hσ : σ ∈ Ioc 1 2) (t : ℝ) (ht : 3 < |t|) :
    zetaLowerBound3c * (σ - 1) ^ ((3 : ℝ) / 4) / (Real.log |t|) ^ ((1 : ℝ) / 4)
      ≤ ‖ζ (σ + t * I)‖ := by
  have ha : zetaStripA ∈ Ioc 0 (1 / 2) := zetaStripA_mem
  have hC : 0 < zetaUpperC := zetaUpperC_pos
  have h_upper := ZetaUpperBndExplicit
  have hc_near : (0 : ℝ) < 5 / 2 := by norm_num
  have h_near := ZetaNear1BndExplicit
  unfold zetaLowerBound3c
  set A := zetaStripA
  set C := zetaUpperC
  set c_near : ℝ := 5 / 2
  obtain ⟨σ_gt, σ_le⟩ := hσ

  -- Use ZetaLowerBound2
  have lower := ZetaLowerBound2 (t := t) σ_gt
  apply le_trans _ lower

  -- Now we need to bound the denominator from above
  -- This will give us a lower bound on the whole expression

  -- Upper bound on ‖ζ σ‖ from ZetaNear1BndExact
  have ζ_σ_bound : ‖ζ σ‖ ≤ c_near / (σ - 1) := by
    exact h_near σ ⟨σ_gt, σ_le⟩

  have ht_2 : 3 < |2 * t| := by simp only [abs_mul, Nat.abs_ofNat]; linarith

  -- Upper bound on ‖ζ (σ + 2*t * I)‖ from ZetaUpperBnd

  have σ_in_range : σ ∈ Icc (1 - A / Real.log |2 * t|) 2 := by
    constructor
    · -- σ ≥ 1 - A / Real.log |2*t|
      have : 0 < A / Real.log |2 * t| := by
        exact ZetaLowerBound3_aux1 A ha t ht_2
      nlinarith
    · exact σ_le

  have ζ_2t_bound := h_upper σ (2 * t) ht_2 σ_in_range

  -- Combine the bounds
  have denom_bound : ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) ≤
      (c_near / (σ - 1)) ^ ((3 : ℝ) / 4) * (C * Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    apply mul_le_mul
    · apply Real.rpow_le_rpow (norm_nonneg _) ζ_σ_bound (by norm_num)
    · apply ZetaLowerBound3_aux2
      convert ζ_2t_bound
      norm_cast
    · apply Real.rpow_nonneg (norm_nonneg _)
    · apply Real.rpow_nonneg (div_nonneg (by linarith) (by linarith))

  -- Simplify the bound
  have : (c_near / (σ - 1)) ^ ((3 : ℝ) / 4) * (C * Real.log |2 * t|) ^ ((1 : ℝ) / 4) =
         c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * (Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    rw [Real.div_rpow (by linarith) (by linarith), Real.mul_rpow (by linarith) (Real.log_nonneg (by linarith))]
    ring_nf
    exact ZetaLowerBound3_aux3 _ _ _ σ_gt
  rw [this] at denom_bound

  -- Take reciprocal (flipping inequality)
  have pos_left : 0 < c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * (Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    apply ZetaLowerBound3_aux4 C hC c_near hc_near t ht σ_gt

  have pos_right : 0 < ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := by
    -- This follows from ZetaLowerBound1 - if either factor were zero, we'd get 0 ≥ 1
    apply ZetaLowerBound3_aux5 _ <| ZetaLowerBound1 (t := t) σ_gt

  use (div_le_div_of_nonneg_left zero_le_one pos_right denom_bound).trans' ?_
  simp_rw [abs_mul, abs_two, neg_div, Real.rpow_neg (sub_pos.2 σ_gt).le] at *
  have hlog : 0 < Real.log |t| := Real.log_pos <| ht.trans' <| by norm_num
  have : 0 < Real.log |t| ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hlog _
  have hlog2 : 0 < Real.log (2 * |t|) := Real.log_pos <| ht_2.trans' <| by norm_num
  have : 0 < Real.log (2 * |t|) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hlog2 (1 / 4)
  field_simp
  rw [Real.mul_rpow two_pos.le hC.le]
  move_mul [C ^ (1 / 4)]
  rw [mul_le_mul_iff_left₀]
  swap
  · positivity
  rw [← Real.mul_rpow two_pos.le hlog.le]
  apply Real.rpow_le_rpow hlog2.le ?_ (by norm_num)
  rw [← Real.log_rpow (ht.trans' (by norm_num))]
  apply Real.log_le_log (ht_2.trans' (by norm_num))
  rw [Real.rpow_two, sq]
  gcongr
  exact ht.trans' (by norm_num) |>.le

/-- The constant in `ZetaInvBound2`, the reciprocal of `zetaLowerBound3c`. -/
noncomputable def zetaInvBound2C : ℝ :=
  (2 * zetaUpperC) ^ ((1 : ℝ) / 4) * (5 / 2 : ℝ) ^ ((3 : ℝ) / 4)

lemma zetaInvBound2C_pos : 0 < zetaInvBound2C := by
  have := zetaUpperC_pos
  unfold zetaInvBound2C
  positivity

@[blueprint
  (title := "ZetaInvBound2Explicit")
  (statement := /--
  For $1 < \sigma \le 2$ and $3 < |t|$, with $C = (2e^{1/2}\cdot 21)^{1/4}(5/2)^{3/4}$,
  $$
  \frac{1}{|\zeta(\sigma+tI)|} \le C\,(\sigma-1)^{-3/4}(\log|t|)^{1/4}.
  $$
  -/)
  (proof := /-- The proof of Lemma \ref{ZetaInvBound2}, with its witness named. -/)
  (latexEnv := "lemma")]
lemma ZetaInvBound2Explicit {σ : ℝ} (hσ : σ ∈ Ioc 1 2) (t : ℝ) (t_gt : 3 < |t|) :
    1 / ‖ζ (σ + t * I)‖
      ≤ zetaInvBound2C * (σ - 1) ^ (-(3 : ℝ) / 4) * (Real.log |t|) ^ ((1 : ℝ) / 4) := by
  have ha : zetaStripA ∈ Ioc 0 (1 / 2) := zetaStripA_mem
  have hC : 0 < zetaUpperC := zetaUpperC_pos
  have h := ZetaUpperBndExplicit
  have hc : (0 : ℝ) < 5 / 2 := by norm_num
  have h_inv := ZetaNear1BndExplicit
  unfold zetaInvBound2C
  set A := zetaStripA
  set C := zetaUpperC
  set c : ℝ := 5 / 2
  obtain ⟨σ_gt, σ_le⟩ := hσ
  have ht' : 3 < |2 * t| := by simp only [abs_mul, Nat.abs_ofNat]; linarith
  have hnezero: ((σ - 1) / c) ^ (-3 / 4 : ℝ) ≠ 0 := by
    have : (σ - 1) / c ≠ 0 := ne_of_gt <| div_pos (by linarith) hc
    contrapose! this
    rwa [Real.rpow_eq_zero (div_nonneg (by linarith) hc.le) (by norm_num)] at this
  calc
    _ ≤ ‖‖ζ σ‖ ^ (3 / 4 : ℝ) * ‖ζ (↑σ + 2 * ↑t * I)‖ ^ (1 / 4 : ℝ)‖ := ?_
    _ ≤ ‖((σ - 1) / c) ^ (-3 / 4 : ℝ) * ‖ζ (↑σ + 2 * ↑t * I)‖ ^ (1 / 4 : ℝ)‖ := ?_
    _ ≤ ‖((σ - 1) / c) ^ (-3 / 4 : ℝ) * C ^ (1 / 4 : ℝ) * (Real.log |2 * t|) ^ (1 / 4 : ℝ)‖ := ?_
    _ ≤ ‖((σ - 1) / c) ^ (-3 / 4 : ℝ) * C ^ (1 / 4 : ℝ) * (Real.log (|t| ^ 2)) ^ (1 / 4 : ℝ)‖ := ?_
    _ = ‖((σ - 1)) ^ (-3 / 4 : ℝ) * c ^ (3 / 4 : ℝ) * (C ^ (1 / 4 : ℝ) * (Real.log (|t| ^ 2)) ^ (1 / 4 : ℝ))‖ := ?_
    _ = ‖((σ - 1)) ^ (-3 / 4 : ℝ) * c ^ (3 / 4 : ℝ) * ((2 * C) ^ (1 / 4 : ℝ) * Real.log |t| ^ (1 / 4 : ℝ))‖ := ?_
    _ = _ := ?_
  · simp only [norm_mul]
    convert ZetaInvBound1 σ_gt using 2
    <;> exact abs_eq_self.mpr <| Real.rpow_nonneg (norm_nonneg _) _
  · have bnd1: ‖ζ σ‖ ^ (3 / 4 : ℝ) ≤ ((σ - 1) / c) ^ (-(3 : ℝ) / 4) := by
      have : ((σ - 1) / c) ^ (-(3 : ℝ) / 4) = (((σ - 1) / c) ^ (-1 : ℝ)) ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_mul ?_]
        · ring_nf
        · exact div_nonneg (by linarith) hc.le
      rw [this]
      apply Real.rpow_le_rpow (by simp [norm_nonneg]) ?_ (by norm_num)
      convert! h_inv σ ⟨σ_gt, σ_le⟩ using 1; simp [Real.rpow_neg_one, inv_div]
    simp only [norm_mul]
    apply (mul_le_mul_iff_left₀ ?_).mpr
    · convert! bnd1 using 1
      · exact abs_eq_self.mpr <| Real.rpow_nonneg (norm_nonneg _) _
      · exact abs_eq_self.mpr <| Real.rpow_nonneg (div_nonneg (by linarith) hc.le) _
    · apply lt_iff_le_and_ne.mpr ⟨(by simp), ?_⟩
      have : ζ (↑σ + 2 * ↑t * I) ≠ 0 := by
        apply riemannZeta_ne_zero_of_one_le_re (by simp [σ_gt.le])
      symm; exact fun h2 ↦ this (by simpa using h2)
  · replace h := h σ (2 * t) (by simpa using ht') ⟨?_, σ_le⟩
    · have : 0 ≤ Real.log |2 * t| := Real.log_nonneg (by linarith)
      conv => rhs; rw [mul_assoc, ← Real.mul_rpow hC.le this]
      rw [norm_mul, norm_mul]
      conv => rhs; rhs; rw [Real.norm_rpow_of_nonneg <| mul_nonneg hC.le this]
      conv => lhs; rhs; rw [Real.norm_rpow_of_nonneg <| norm_nonneg _]
      apply (mul_le_mul_iff_right₀ ?_).mpr
      · apply Real.rpow_le_rpow (norm_nonneg _) ?_ (by norm_num)
        convert h using 1
        · simp
        · rw [Real.norm_eq_abs, abs_eq_self.mpr <| mul_nonneg hC.le this]
      · simpa only [Real.norm_eq_abs, abs_pos]
    · linarith [(div_nonneg ha.1.le (Real.log_nonneg (by linarith)) : 0 ≤ A / Real.log |2 * t|)]
  · simp only [Real.log_abs, norm_mul]
    apply (mul_le_mul_iff_right₀ ?_).mpr
    · rw [← Real.log_abs, Real.norm_rpow_of_nonneg <| Real.log_nonneg (by linarith)]
      have : 1 ≤ |(|t| ^ 2)| := by
        simp only [_root_.sq_abs, _root_.abs_pow, one_le_sq_iff_one_le_abs]
        linarith
      conv => rhs; rw [← Real.log_abs, Real.norm_rpow_of_nonneg <| Real.log_nonneg this]
      apply Real.rpow_le_rpow (abs_nonneg _) ?_ (by norm_num)
      · rw [Real.norm_eq_abs, abs_eq_self.mpr <| Real.log_nonneg (by linarith)]
        rw [abs_eq_self.mpr <| Real.log_nonneg this, abs_mul, Real.log_abs, Nat.abs_ofNat]
        apply Real.log_le_log (mul_pos (by norm_num) (by linarith)) (by nlinarith)
    · apply mul_pos (abs_pos.mpr hnezero) (abs_pos.mpr ?_)
      have : C ≠ 0 := ne_of_gt hC
      contrapose! this; rwa [Real.rpow_eq_zero (by linarith) (by norm_num)] at this
  · have : (-3 : ℝ) / 4 = -((3 : ℝ)/ 4) := by norm_num
    simp only [norm_mul, mul_eq_mul_right_iff, this, ← mul_assoc]; left; left
    conv => lhs; rw [Real.div_rpow (by linarith) hc.le, Real.rpow_neg hc.le, div_inv_eq_mul, norm_mul]
  · simp only [Real.log_pow, Nat.cast_ofNat, norm_mul, Real.norm_eq_abs]
    congr! 1
    rw [Real.mul_rpow (by norm_num) hC.le, Real.mul_rpow (by norm_num) <|
        Real.log_nonneg (by linarith), abs_mul, abs_mul, ← mul_assoc, mul_comm _ |2 ^ (1 / 4)|]
  · simp only [norm_mul, Real.norm_eq_abs]
    have : (2 * C) ^ ((1 : ℝ)/ 4) * c ^ ((3 : ℝ)/ 4) =
      |(2 * C) ^ ((1 : ℝ)/ 4) * c ^ ((3 : ℝ)/ 4)| := by
      rw [abs_eq_self.mpr (by apply mul_nonneg <;> (apply Real.rpow_nonneg; linarith))]
    rw [this, abs_mul, abs_eq_self.mpr (by apply Real.rpow_nonneg; linarith), abs_eq_self.mpr (by positivity),
      abs_eq_self.mpr (by positivity), abs_eq_self.mpr (by apply Real.rpow_nonneg (Real.log_nonneg (by linarith)))]
    ring_nf

@[blueprint
  (title := "Zeta-diff-BndExplicit")
  (statement := /--
  For $3 < |t|$, $1 - \frac{1}{2\log|t|} \le \sigma_1 < \sigma_2 \le 2$,
  $$
  |\zeta(\sigma_2+tI) - \zeta(\sigma_1+tI)| \le e^{1/2}\cdot 59\cdot(\log|t|)^2(\sigma_2-\sigma_1).
  $$
  -/)
  (proof := /-- The proof of Lemma \ref{Zeta_diff_Bnd}, with its two witnesses named. -/)
  (latexEnv := "lemma")]
lemma Zeta_diff_BndExplicit (σ₁ σ₂ : ℝ) (t : ℝ) (t_gt : 3 < |t|)
    (σ₁_ge : 1 - zetaStripA / Real.log |t| ≤ σ₁) (σ₂_le : σ₂ ≤ 2) (σ₁_lt_σ₂ : σ₁ < σ₂) :
    ‖ζ (σ₂ + t * I) - ζ (σ₁ + t * I)‖ ≤ zetaDerivUpperC * Real.log |t| ^ 2 * (σ₂ - σ₁) := by
  have hA : zetaStripA ∈ Ioc 0 (1 / 2) := zetaStripA_mem
  have Cpos : 0 < zetaDerivUpperC := zetaDerivUpperC_pos
  have hC := ZetaDerivUpperBndExplicit
  set A := zetaStripA
  set C := zetaDerivUpperC
  have t_ne_zero : t ≠ 0 := by contrapose! t_gt; simp only [t_gt, abs_zero, Nat.ofNat_nonneg]
  rw [← Zeta_eq_int_derivZeta t_ne_zero]
  convert intervalIntegral.norm_integral_le_of_norm_le_const ?_ using 1
  · congr; rw [_root_.abs_of_nonneg (by linarith)]
  · intro σ hσ; rw [uIoc_of_le σ₁_lt_σ₂.le, mem_Ioc] at hσ
    exact hC σ t t_gt ⟨le_trans σ₁_ge hσ.1.le, le_trans hσ.2 σ₂_le⟩

/-- `1 / zetaInvBound2C`, the constant called `C₁` in the proof of `ZetaInvBnd`. -/
noncomputable def zetaInvBndC₁ : ℝ := 1 / zetaInvBound2C

/-- The strip width in `ZetaInvBnd`, `ZetaLowerBnd` and `ZetaZeroFree`. -/
noncomputable def zetaInvBndA : ℝ :=
  min zetaStripA ((1 / 2 : ℝ) * (zetaInvBndC₁ / (zetaDerivUpperC * 2)) ^ (4 : ℝ))

/-- The constant in `ZetaInvBnd`. -/
noncomputable def zetaInvBndC : ℝ :=
  (zetaInvBndC₁ * zetaInvBndA ^ (3 / 4 : ℝ) - zetaDerivUpperC * 2 * zetaInvBndA)⁻¹

lemma zetaInvBndC₁_pos : 0 < zetaInvBndC₁ := by
  have := zetaInvBound2C_pos
  unfold zetaInvBndC₁
  positivity

lemma zetaInvBndA_pos : 0 < zetaInvBndA := by
  have := zetaInvBndC₁_pos
  have := zetaDerivUpperC_pos
  have := zetaStripA_mem.1
  unfold zetaInvBndA
  positivity

lemma zetaInvBndA_le : zetaInvBndA ≤ 1 / 2 :=
  le_trans (min_le_left _ _) zetaStripA_mem.2

lemma zetaInvBndA_mem : zetaInvBndA ∈ Ioc 0 (1 / 2) := ⟨zetaInvBndA_pos, zetaInvBndA_le⟩

lemma zetaInvBndC_pos : 0 < zetaInvBndC := by
  have h1 := zetaInvBndC₁_pos
  have h2 := zetaDerivUpperC_pos
  have h3 := zetaInvBndA_pos
  unfold zetaInvBndC
  refine ZetaInvBnd_aux2 (by positivity) (by positivity) (by positivity) ?_
  unfold zetaInvBndA
  apply min_le_right

@[blueprint
  (title := "ZetaInvBndExplicit")
  (statement := /--
  With $A = \min\left(\tfrac12, \tfrac12 (C_1/2C_2)^4\right)$,
  $C_1 = \left((2e^{1/2}\cdot 21)^{1/4}(5/2)^{3/4}\right)^{-1}$, $C_2 = e^{1/2}\cdot 59$ and
  $C = (C_1A^{3/4} - 2C_2A)^{-1}$, for $3<|t|$ and
  $|\sigma - 1| < A/(\log|t|)^9$,
  $$
  \frac{1}{|\zeta(\sigma+tI)|} \le C (\log |t|)^7.
  $$
  -/)
  (proof := /-- The proof of Lemma \ref{ZetaInvBnd}, with its two witnesses named. -/)
  (latexEnv := "lemma")]
lemma ZetaInvBndExplicit (σ : ℝ) (t : ℝ) (t_gt : 3 < |t|)
    (hσ : σ ∈ Ico (1 - zetaInvBndA / (Real.log |t|) ^ 9)
      (1 + zetaInvBndA / (Real.log |t|) ^ 9)) :
    1 / ‖ζ (σ + t * I)‖ ≤ zetaInvBndC * (Real.log |t|) ^ (7 : ℝ) := by
  have C'pos : 0 < zetaInvBound2C := zetaInvBound2C_pos
  have hC₁ : ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|), 1 / ‖ζ (σ + t * I)‖
      ≤ zetaInvBound2C * (σ - 1) ^ (-(3 : ℝ) / 4) * (Real.log |t|) ^ ((1 : ℝ) / 4) :=
    fun hσ t ht => ZetaInvBound2Explicit hσ t ht
  have hA' : zetaStripA ∈ Ioc 0 (1 / 2) := zetaStripA_mem
  have C₂pos : 0 < zetaDerivUpperC := zetaDerivUpperC_pos
  have hC₂ := Zeta_diff_BndExplicit
  have Apos : 0 < zetaInvBndA := zetaInvBndA_pos
  have Ale : zetaInvBndA ≤ 1 / 2 := zetaInvBndA_le
  have Cpos : 0 < zetaInvBndC := zetaInvBndC_pos
  unfold zetaInvBndC zetaInvBndA zetaInvBndC₁ at *
  set C' := zetaInvBound2C
  set A' := zetaStripA
  set C₂ := zetaDerivUpperC
  set C₁ := 1 / C'
  set A := min A' ((1 / 2 : ℝ) * (C₁ / (C₂ * 2)) ^ (4 : ℝ)) with hA_def
  set C := (C₁ * A ^ (3 / 4 : ℝ) - C₂ * 2 * A)⁻¹
  have logt_gt_one := logt_gt_one t_gt.le
  have σ_ge : 1 - A / Real.log |t| ≤ σ := by
    apply le_trans ?_ hσ.1
    suffices A / Real.log |t| ^ 9 ≤ A / Real.log |t| by linarith
    exact div_le_div₀ Apos.le (by rfl) (by positivity) <| ZetaInvBnd_aux logt_gt_one
  obtain ⟨_, _, neOne⟩ := UpperBnd_aux ⟨Apos, Ale⟩ t_gt σ_ge
  set σ' := 1 + A / Real.log |t| ^ 9
  have σ'_gt : 1 < σ' := by simp only [σ', lt_add_iff_pos_right]; positivity
  have σ'_le : σ' ≤ 2 := by
    simp only [σ']
    suffices A / Real.log |t| ^ 9 < 1 by linarith
    apply div_lt_one (by positivity) |>.mpr
    exact lt_trans₄ (by linarith) logt_gt_one <| ZetaInvBnd_aux' logt_gt_one
  set s := σ + t * I
  set s' := σ' + t * I
  by_cases h0 : ‖ζ s‖ ≠ 0
  swap
  · simp only [ne_eq, not_not] at h0; simp only [h0, div_zero]; positivity
  apply div_le_iff₀ (by positivity) |>.mpr <| div_le_iff₀' (by positivity) |>.mp ?_
  have pos_aux : 0 < (σ' - 1) := by linarith
  calc
    _ ≥ ‖ζ s'‖ - ‖ζ s - ζ s'‖ := ?_
    _ ≥ C₁ * (σ' - 1) ^ ((3 : ℝ)/ 4) * Real.log |t|  ^ ((-1 : ℝ)/ 4) - C₂ * Real.log |t| ^ 2 * (σ' - σ) := ?_
    _ ≥ C₁ * (A / Real.log |t| ^ (9 : ℝ)) ^ ((3 : ℝ)/ 4) * Real.log |t| ^ ((-1 : ℝ)/ 4) - C₂ * Real.log |t| ^ (2 : ℝ) * 2 * A / Real.log |t| ^ (9 : ℝ) := ?_
    _ ≥ C₁ * A ^ ((3 : ℝ)/ 4) * Real.log |t| ^ (-7 : ℝ) - C₂ * 2 * A * Real.log |t| ^ (-7 : ℝ) := ?_
    _ = (C₁ * A ^ ((3 : ℝ)/ 4) - C₂ * 2 * A) * Real.log |t| ^ (-7 : ℝ) := by ring
    _ ≥ _ := ?_
  · apply ge_iff_le.mpr
    convert norm_sub_norm_le (a := ζ s') (b := ζ s' - ζ s) using 1
    · rw [(by simp : ζ s' - ζ s = -(ζ s - ζ s'))]; simp only [norm_neg]
    · simp
  · apply sub_le_sub
    · have := one_div_le ?_ (by positivity) |>.mp <| hC₁ ⟨σ'_gt, σ'_le⟩ t t_gt
      · convert this using 1
        rw [one_div, mul_inv_rev, mul_comm, mul_inv_rev, mul_comm _ C'⁻¹]
        simp only [one_div C', C₁]
        congr <;> (rw [← Real.rpow_neg (by linarith), neg_div]); rw [neg_neg]
      · apply norm_pos_iff.mpr <| riemannZeta_ne_zero_of_one_lt_re (by simp [σ'_gt])
    · rw [(by simp : ζ s - ζ s' = -(ζ s' - ζ s)), norm_neg]
      refine hC₂ σ σ' t t_gt ?_ σ'_le <| by rw [Set.mem_Ico] at hσ; exact hσ.2
      apply le_trans ?_ hσ.1
      rw [tsub_le_iff_right, ← add_sub_right_comm, le_sub_iff_add_le, add_le_add_iff_left]
      exact div_le_div₀ hA'.1.le (by simp [A]) (by positivity) <| ZetaInvBnd_aux logt_gt_one
  · apply sub_le_sub (by simp only [add_sub_cancel_left, σ']; exact_mod_cast le_rfl) ?_
    rw [mul_div_assoc, mul_assoc _ 2 _]
    apply mul_le_mul (by exact_mod_cast le_rfl) ?_ (by linarith [hσ.2]) (by positivity)
    suffices h : σ' + (1 - A / Real.log |t| ^ 9) ≤ (1 + A / Real.log |t| ^ 9) + σ by
      simp only [tsub_le_iff_right]
      convert! le_sub_right_of_add_le h using 1; ring_nf; norm_cast; simp
    exact add_le_add (by linarith) (by linarith [hσ.1])
  · simp_rw [tsub_le_iff_right, div_eq_mul_inv _ (Real.log |t| ^ (9 : ℝ))]
    rw [← Real.rpow_neg (by positivity), Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_mul (by positivity)]
    ring_nf
    conv => rhs; lhs; rw [mul_assoc, ← Real.rpow_add (by positivity)]
    rw [(by ring : C₂ * Real.log |t| ^ (2 : ℝ) * A * Real.log |t| ^ (-9 : ℝ) * 2 = C₂ * (Real.log |t| ^ (2 : ℝ) * Real.log |t| ^ (-9 : ℝ) ) * A * 2)]
    rw [← Real.rpow_add (by positivity)]; norm_num; group; exact le_rfl
  · apply div_le_iff₀ (by positivity) |>.mpr
    conv => rw [mul_assoc]; rhs; rhs; rw [mul_comm C, ← mul_assoc, ← Real.rpow_add (by positivity)]
    have := inv_inv C ▸ mul_inv_cancel₀ (a := C⁻¹) (by positivity) |>.symm.le
    simpa [C] using this

/-- The strip width in `ZetaLowerBnd`. -/
noncomputable def zetaLowerBndA : ℝ :=
  min zetaStripA ((zetaLowerBound3c / (4 * zetaDerivUpperC)) ^ 4)

/-- The constant in `ZetaLowerBnd`. -/
noncomputable def zetaLowerBndc : ℝ :=
  zetaLowerBound3c * zetaLowerBndA ^ ((3 : ℝ) / 4) - 2 * zetaDerivUpperC * zetaLowerBndA

lemma zetaLowerBndA_mem : zetaLowerBndA ∈ Ioc 0 (1 / 2) := by
  have C₁pos : 0 < zetaLowerBound3c := zetaLowerBound3c_pos
  have C₂pos : 0 < zetaDerivUpperC := zetaDerivUpperC_pos
  have hA' : zetaStripA ∈ Ioc 0 (1 / 2) := zetaStripA_mem
  unfold zetaLowerBndA
  exact ⟨lt_min hA'.1 (by positivity), (min_le_left _ _).trans hA'.2⟩

lemma zetaLowerBndc_pos : 0 < zetaLowerBndc := by
  have C₁pos : 0 < zetaLowerBound3c := zetaLowerBound3c_pos
  have C₂pos : 0 < zetaDerivUpperC := zetaDerivUpperC_pos
  have hA : zetaLowerBndA ∈ Ioc 0 (1 / 2) := zetaLowerBndA_mem
  unfold zetaLowerBndc zetaLowerBndA at hA ⊢
  set C₁ := zetaLowerBound3c
  set A' := zetaStripA
  set C₂ := zetaDerivUpperC
  set A := min A' ((C₁ / (4 * C₂)) ^ 4)
  set C := C₁ * A ^ ((3:ℝ) /4) - 2 * C₂ * A
  have:= A.rpow_le_rpow hA.1.le (min_le_right _ _) (inv_pos.mpr four_pos).le
  erw [Real.pow_rpow_inv_natCast (div_pos C₁pos (mul_pos four_pos C₂pos)).le four_ne_zero,
    le_div_iff₀ (mul_pos four_pos C₂pos)] at this
  norm_num [mul_assoc, C, mul_left_comm, C₂pos, hA.1,
    (mul_le_mul_of_nonneg_right this (A.rpow_nonneg hA.1.le _)).trans_lt', ←A.rpow_add]

@[blueprint
  (title := "ZetaLowerBndExplicit")
  (statement := /--
  With $A = \min\left(\tfrac12, (c_1/4C_2)^4\right)$,
  $c_1 = \left((5/2)^{3/4}(2e^{1/2}\cdot 21)^{1/4}\right)^{-1}$, $C_2 = e^{1/2}\cdot 59$ and
  $c = c_1A^{3/4} - 2C_2A$, for $3 < |t|$ and $1 - A/(\log|t|)^9 \le \sigma < 1$,
  $$
  \frac{c}{(\log|t|)^7} \le |\zeta(\sigma+tI)|.
  $$
  -/)
  (proof := /-- The proof of Lemma \ref{ZetaLowerBnd}, with its two witnesses named. -/)
  (latexEnv := "lemma")]
lemma ZetaLowerBndExplicit (σ : ℝ) (t : ℝ) (L : 3 < |t|)
    (hσ : σ ∈ Ico (1 - zetaLowerBndA / (Real.log |t|) ^ 9) 1) :
    zetaLowerBndc / (Real.log |t|) ^ (7 : ℝ) ≤ ‖ζ (σ + t * I)‖ := by
  have C₁pos : 0 < zetaLowerBound3c := zetaLowerBound3c_pos
  have hC₁ : ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
      zetaLowerBound3c * (σ - 1) ^ ((3 : ℝ) / 4) / (Real.log |t|) ^ ((1 : ℝ) / 4)
        ≤ ‖ζ (σ + t * I)‖ := fun hσ t ht => ZetaLowerBound3Explicit hσ t ht
  have hA' : zetaStripA ∈ Ioc 0 (1 / 2) := zetaStripA_mem
  have C₂pos : 0 < zetaDerivUpperC := zetaDerivUpperC_pos
  have hC₂ := Zeta_diff_BndExplicit
  have hA : zetaLowerBndA ∈ Ioc 0 (1 / 2) := zetaLowerBndA_mem
  have hc_pos : 0 < zetaLowerBndc := zetaLowerBndc_pos
  unfold zetaLowerBndc zetaLowerBndA at hc_pos ⊢
  unfold zetaLowerBndA at hA hσ
  set C₁ := zetaLowerBound3c
  set A' := zetaStripA
  set C₂ := zetaDerivUpperC
  set A := min A' ((C₁ / (4 * C₂)) ^ 4)
  set C := C₁ * A ^ ((3:ℝ) /4) - 2 * C₂ * A
  obtain ⟨σ_low_bound, σ_le_one⟩ := hσ

  -- From here on, the proof follows the blueprint.
  let σ' := 1 + A / Real.log |t| ^  (9 : ℝ)

  have triangular :  ‖ζ (σ + t * I)‖ ≥  ‖ζ (σ' + t * I)‖ -  ‖ζ (σ + t * I) - ζ (σ' + t * I)‖ := by
    apply sub_le_iff_le_add.mpr.comp (sub_sub_self @_ (@_ : ℂ)▸norm_sub_le _ _).trans
      (by rw [add_comm])

  have one_leLogT : 1 ≤ Real.log |t| := (logt_gt_one L.le).le
  have one_half_le_log_pow : 1 / 2 ≤ Real.log |t| ^ 9 :=
    one_half_lt_one.le.trans <| one_le_pow₀ one_leLogT

  have σ'_ge : 1 ≤ σ' := by
    simp_all only [mem_Ioc, Real.log_abs, one_div, and_imp, tsub_le_iff_right,
      lt_inf_iff, div_pos_iff_of_pos_left, Nat.ofNat_pos, mul_pos_iff_of_pos_left, pow_pos,
      and_self, inf_le_iff, true_or, sub_pos, ofReal_add, ofReal_one,
      ofReal_div, ge_iff_le, le_add_iff_nonneg_right, A, C, σ']
    apply div_nonneg
    · apply le_min
      · linarith
      · have : (C₁ / (4 * C₂)) ^ 4 = ((C₁ / (4 * C₂)) ^ 2) ^ 2 := by ring
        rw [this]
        apply sq_nonneg
    · positivity

  have right_sub :  -‖ζ (σ + t * I) -  ζ (σ' + t * I)‖ ≥ - C₂ * Real.log |t| ^ 2 * (σ' - σ) := by
    change - C₂ * Real.log |t| ^ 2 * (σ' - σ) ≤ -‖ζ (σ + t * I) -  ζ (σ' + t * I)‖
    have := hC₂ σ σ' t L ?_ ?_ ?_
    · convert! neg_le_neg this using 1
      · ring
      · congr! 1
        have : ζ (↑σ + ↑t * I) - ζ (↑σ' + ↑t * I) =
            - (ζ (↑σ' + ↑t * I) - ζ (↑σ + ↑t * I)) := by ring
        rw [this, norm_neg]
    · have : 1 - A' / Real.log |t| ≤ 1 - A / (Real.log |t|) ^ 9 := by
        gcongr
        · exact hA'.1.le
        · bound
        · bound
      linarith
    · have : σ' ≤ 1 + A := by
        simp_all only [mem_Ioc, Real.log_abs, one_div, and_imp, tsub_le_iff_right,
          lt_inf_iff, div_pos_iff_of_pos_left, Nat.ofNat_pos, mul_pos_iff_of_pos_left, pow_pos,
          and_self, inf_le_iff, true_or, sub_pos, ofReal_add, ofReal_one,
          ofReal_div, ge_iff_le, le_add_iff_nonneg_right, add_le_add_iff_left, le_inf_iff,
          σ', A, C]
        have : 1 ≤ Real.log t ^ (9 : ℕ) := by
          bound
        have : 1 ≤ Real.log t ^ (9 : ℝ) := by
          exact_mod_cast this
        refine ⟨?_, ?_⟩
        · rw [← min_div_div_right]
          · rw [min_le_iff]
            left
            bound
          · exact le_trans (zero_le_one) this
        · rw [← min_div_div_right]
          · rw [min_le_iff]
            right
            bound
          · exact le_trans (zero_le_one) this
      · bound [hA.2]
    · linarith

  have right' : -‖ζ (σ + t * I) -  ζ (σ' + t * I)‖   ≥ - C₂ * 2 * A / Real.log |t| ^ 7 := by
    have := (abs t).log_pos (by bound)
    refine right_sub.trans' ((div_le_iff₀ (pow_pos this 7)).2 @?_|>.trans
      (mul_le_mul_of_nonpos_left (sub_le_sub_left σ_low_bound (1+_) )
        (by ·linear_combination C₂*this*(.log |t|))))
    exact (mod_cast (by linear_combination (2 *_* A) *div_self ↑(pow_pos this 09).ne'))

  have left_sub : ‖ζ (σ' + t * I)‖ ≥ C₁ * (σ' - 1) ^ ((3:ℝ) /4) / Real.log |t| ^ 4 := by
    use (hC₁ ⟨lt_add_of_pos_right (1) (by bound[hA.1]),
      add_le_of_le_sub_left ((div_le_iff₀ (by bound)).2 (hA.2.trans (?_)))⟩ t L).trans' ?_
    · norm_num only [one_mul, Real.rpow_ofNat, one_half_le_log_pow]
    · simp_all only [mem_Ioc, lt_inf_iff, div_pos_iff_of_pos_left, Nat.ofNat_pos,
        mul_pos_iff_of_pos_left, pow_pos, and_self, inf_le_iff, true_or, sub_pos,
        ofReal_add, ofReal_one, ofReal_div, ge_iff_le, le_add_iff_nonneg_right, neg_mul,
        neg_le_neg_iff, add_sub_cancel_left, σ', A, C]
      gcongr
      have :  Real.log |t| ^ ((1 : ℝ) / 4) ≤ Real.log |t| ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_leLogT (by norm_num)
      exact_mod_cast this

  have left' : ‖ζ (σ' + t * I)‖ ≥ C₁ * A ^ ((3:ℝ) /4) / Real.log |t| ^ 7 := by
    contrapose! hC₁
    use σ', ⟨lt_add_of_pos_right 1<|by bound[hA'.1],
      add_le_of_le_sub_left ((div_le_iff₀ (by bound)).2 (hA.2.trans ?_))⟩, t, L, hC₁.trans_le ?_
    · norm_num only [one_mul, Real.rpow_ofNat, one_half_le_log_pow]
    · norm_num only [σ', add_sub_cancel_left, A.div_rpow hA.1.le, mul_div, pow_pos, L.trans',
        ←Real.rpow_natCast, ←Real.rpow_mul, le_of_lt, Real.log_pos, refl, div_div, ←Real.rpow_sub]
      rw [Real.div_rpow hA.1.le, ← Real.rpow_mul (by linarith), ← mul_div_assoc, div_div, ← Real.rpow_add (by linarith)]
      · norm_num
      · apply Real.rpow_nonneg (by linarith)
  have ineq : ‖ζ (σ + t * I)‖ ≥ (C₁ * A ^ ((3:ℝ) /4) - C₂ * 2 * A) / Real.log |t| ^ 7 := by
    linear_combination left'+triangular+right'

  rw [mul_comm C₂] at ineq
  exact_mod_cast ineq

@[blueprint
  (title := "ZetaZeroFreeExplicit")
  (statement := /--
  With $A = \min\left(\tfrac12, (c_1/4C_2)^4\right)$ as in Lemma
  \ref{ZetaLowerBndExplicit}, $\zeta(\sigma+tI) \ne 0$ whenever $3 < |t|$ and
  $1 - A/(\log|t|)^9 \le \sigma < 1$.
  -/)
  (proof := /-- The proof of Lemma \ref{ZetaZeroFree}, with its witness named. -/)
  (latexEnv := "lemma")]
lemma ZetaZeroFreeExplicit (σ : ℝ) (t : ℝ) (ht : 3 < |t|)
    (hσ : σ ∈ Ico (1 - zetaLowerBndA / (Real.log |t|) ^ 9) 1) :
    ζ (σ + t * I) ≠ 0 := by
  have hc : 0 < zetaLowerBndc := zetaLowerBndc_pos
  have h_lower := ZetaLowerBndExplicit
  set c := zetaLowerBndc
  intro h_zero

  have := h_lower σ t ht hσ

  rw [h_zero, norm_zero] at this

  have pos_bound : 0 < c / (Real.log |t|) ^ (7 : ℝ) := by
    apply div_pos hc
    apply Real.rpow_pos_of_pos
    apply Real.log_pos
    linarith

  linarith

/-- The strip width in `LogDerivZetaBnd`. -/
noncomputable def zetaLogDerivA : ℝ := min zetaInvBndA zetaStripA

/-- The constant in `LogDerivZetaBnd`. -/
noncomputable def zetaLogDerivC : ℝ := zetaInvBndC * zetaDerivUpperC

lemma zetaLogDerivA_mem : zetaLogDerivA ∈ Ioc 0 (1 / 2) :=
  ⟨lt_min zetaInvBndA_mem.1 zetaStripA_mem.1, min_le_of_right_le zetaStripA_mem.2⟩

lemma zetaLogDerivC_pos : 0 < zetaLogDerivC := mul_pos zetaInvBndC_pos zetaDerivUpperC_pos

@[blueprint
  (title := "LogDerivZetaBndExplicit")
  (statement := /--
  With $A = \min(A_{\mathrm{inv}}, \tfrac12)$ and $C = C_{\mathrm{inv}}\cdot e^{1/2}\cdot 59$,
  for $3 < |t|$ and $|\sigma - 1| < A/(\log|t|)^9$,
  $$
  \left|\frac{\zeta'}{\zeta}(\sigma+tI)\right| \le C (\log|t|)^9 .
  $$
  -/)
  (proof := /-- The proof of Lemma \ref{LogDerivZetaBnd}, with its two witnesses named. -/)
  (latexEnv := "lemma")]
lemma LogDerivZetaBndExplicit (σ : ℝ) (t : ℝ) (t_gt : 3 < |t|)
    (hσ : σ ∈ Ico (1 - zetaLogDerivA / Real.log |t| ^ 9)
      (1 + zetaLogDerivA / Real.log |t| ^ 9)) :
    ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ zetaLogDerivC * Real.log |t| ^ 9 := by
  have hA : zetaInvBndA ∈ Ioc 0 (1 / 2) := zetaInvBndA_mem
  have hC : 0 < zetaInvBndC := zetaInvBndC_pos
  have h := ZetaInvBndExplicit
  have hA' : zetaStripA ∈ Ioc 0 (1 / 2) := zetaStripA_mem
  have hC' : 0 < zetaDerivUpperC := zetaDerivUpperC_pos
  have h' := ZetaDerivUpperBndExplicit
  unfold zetaLogDerivA at hσ
  unfold zetaLogDerivC
  set A := zetaInvBndA
  set C := zetaInvBndC
  set A' := zetaStripA
  set C' := zetaDerivUpperC
  obtain ⟨σ_ge, σ_lt⟩ := hσ
  have logt_gt : (1 : ℝ) < Real.log |t| := logt_gt_one t_gt.le
  have σ_ge' : 1 - A / Real.log |t| ^ 9 ≤ σ := by
    apply le_trans (tsub_le_tsub_left ?_ 1) σ_ge
    apply div_le_div_of_nonneg_right (min_le_left A A')
    exact pow_nonneg (zero_le_one.trans logt_gt.le) _
  have σ_ge'' : 1 - A' / Real.log |t| ≤ σ := by
    apply le_trans (tsub_le_tsub_left ?_ 1) σ_ge
    apply div_le_div₀ hA'.1.le (min_le_right A A') (lt_trans (by norm_num) logt_gt) ?_
    exact le_self_pow₀ logt_gt.le (by norm_num)
  replace h := h σ t t_gt ⟨σ_ge', by calc
    σ < 1 + min A A' / Real.log |t| ^ 9 := σ_lt
    _ ≤ 1 + A / Real.log |t| ^ 9 := by gcongr; simp⟩
  replace h' := h' σ t t_gt ⟨σ_ge'', by
   calc
    σ ≤ 1 + min A A' / Real.log |t| ^ 9 := by linarith [σ_lt]

    _ ≤ 1 + (1/2) / Real.log |t| ^ 9 := by gcongr; simp [Set.mem_Ioc] at hA' hA ⊢ ; simp [hA.2]

    _ ≤ 1 + (1/2) / 1 := by
          gcongr
          calc
            1 ≤ Real.log |t| := by linarith
            _ ≤ (Real.log |t|)^9 := Real.self_le_rpow_of_one_le (by linarith) (by linarith)
          norm_cast

    _ ≤ 2 := by linarith
    ⟩
  simp only [norm_div]
  convert! mul_le_mul h h' (by simp) ?_ using 1 <;> (norm_cast; ring_nf); positivity

/-! ### An explicit `ζ'` bound away from the pole, by Cauchy's estimate -/

lemma zeta_deriv_le_of_box {s : ℂ} (hre : 3 / 4 ≤ s.re) (hs : ‖s‖ ≤ 5)
    (hpole : 1 / 4 ≤ ‖s - 1‖) : ‖ζ' s‖ ≤ 136 := by
  have hR : (0 : ℝ) < 1 / 8 := by norm_num
  have hsub : Metric.closedBall s (1 / 8) ⊆ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro z hz
    simp only [Metric.mem_closedBall, Complex.dist_eq] at hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    rw [h, show (1 : ℂ) - s = -(s - 1) by ring, norm_neg] at hz
    linarith
  have hd : DiffContOnCl ℂ ζ (Metric.ball s (1 / 8)) := by
    refine DifferentiableOn.diffContOnCl_ball (U := ({(1 : ℂ)}ᶜ : Set ℂ)) ?_ hsub
    intro z hz
    exact (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hC : ∀ z ∈ Metric.sphere s (1 / 8), ‖ζ z‖ ≤ 17 := by
    intro z hz
    simp only [Metric.mem_sphere, Complex.dist_eq] at hz
    have hzs : ‖s - z‖ = 1 / 8 := by rw [show s - z = -(z - s) by ring, norm_neg]; exact hz
    have hz1 : 1 / 8 ≤ ‖z - 1‖ := by
      have h := norm_sub_norm_le (s - 1) (s - z)
      rw [show (s - 1) - (s - z) = z - 1 by ring, hzs] at h
      linarith
    have hz1ne : z ≠ 1 := by
      intro h; rw [h] at hz1; simp at hz1; linarith
    have hzre : 5 / 8 ≤ z.re := by
      have h := Complex.abs_re_le_norm (z - s)
      rw [hz] at h
      simp only [Complex.sub_re] at h
      rw [abs_le] at h
      linarith
    have hzn : ‖z‖ ≤ 5 + 1 / 8 := by
      have h := norm_sub_norm_le z s
      rw [hz] at h
      linarith
    have hsp := ZetaSubPole_le (by linarith : (0:ℝ) < z.re) hz1ne
    have hinv : ‖1 / (z - 1)‖ ≤ 8 := by
      rw [norm_div, norm_one]
      rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖z - 1‖)]
      linarith
    have hfrac : ‖z‖ / z.re ≤ (5 + 1 / 8) / (5 / 8) :=
      div_le_div₀ (by norm_num) hzn (by norm_num) hzre
    have := norm_sub_norm_le (ζ z) (1 / (z - 1))
    have hnorm : ‖ζ z‖ ≤ ‖ζ z - 1 / (z - 1)‖ + ‖1 / (z - 1)‖ := by
      have h2 := norm_add_le (ζ z - 1 / (z - 1)) (1 / (z - 1))
      simpa using h2
    have : ‖ζ z - 1 / (z - 1)‖ ≤ 1 / 2 + (5 + 1 / 8) / (5 / 8) := by linarith
    norm_num at this ⊢
    linarith
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd hC
  norm_num at hcauchy
  linarith

/-! ### 3-4-1 on the annulus -/

/-- `‖ζ(σ + 2it)‖ ≤ 16` for `1 < σ ≤ 2` and `1/4 ≤ |t| ≤ 3`, from the pole bound. -/
lemma zeta_double_le {σ t : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) (ht : 1 / 4 ≤ |t|) (ht3 : |t| ≤ 3) :
    ‖ζ ((σ : ℂ) + 2 * t * I)‖ ≤ 16 := by
  set s : ℂ := (σ : ℂ) + 2 * t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = 2 * t := by simp [hsdef]
  have hre0 : 0 < s.re := by rw [hsre]; linarith
  have hs1 : s ≠ 1 := by
    intro h
    have : s.im = 0 := by rw [h]; simp
    rw [hsim] at this
    have : |t| = 0 := by
      have : t = 0 := by linarith
      simp [this]
    linarith
  have hpole : 1 / 2 ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero, hsim] at h
    rw [abs_mul] at h
    simp only [abs_two] at h
    linarith
  have hsn : ‖s‖ ≤ 8 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [hsre, hsim, abs_mul, abs_two] at h
    rw [abs_of_pos (by linarith : (0:ℝ) < σ)] at h
    linarith
  have hsp := ZetaSubPole_le hre0 hs1
  have hinv : ‖1 / (s - 1)‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ (by linarith : (0:ℝ) < ‖s - 1‖)]
    linarith
  have hfrac : ‖s‖ / s.re ≤ 8 := by
    rw [hsre]
    calc ‖s‖ / σ ≤ 8 / 1 := div_le_div₀ (by norm_num) hsn (by norm_num) (by linarith)
      _ = 8 := by norm_num
  have hnorm : ‖ζ s‖ ≤ ‖ζ s - 1 / (s - 1)‖ + ‖1 / (s - 1)‖ := by
    simpa using norm_add_le (ζ s - 1 / (s - 1)) (1 / (s - 1))
  linarith

/-- **The 3-4-1 lower bound just right of `σ = 1`, on the annulus.** -/
lemma zeta_lower_annulus {δ t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ht : 1 / 4 ≤ |t|) (ht3 : |t| ≤ 3) :
    δ ^ ((3 : ℝ) / 4) / 8 ≤ ‖ζ (((1 + δ : ℝ) : ℂ) + t * I)‖ := by
  have hσ : (1 : ℝ) < 1 + δ := by linarith
  have hlow := ZetaLowerBound2 (σ := 1 + δ) (t := t) hσ
  have hA : ‖ζ ((1 + δ : ℝ) : ℂ)‖ ≤ 4 / δ := by
    have h := ZetaNear1BndAdd hσ
    have : (1 : ℝ) + δ - 1 = δ := by ring
    rw [this] at h
    have h2 : (3 : ℝ) / 2 ≤ 3 / δ := by
      rw [div_le_div_iff₀ (by norm_num) hδ]; linarith
    have h3 : (3 : ℝ) / δ + 1 / δ = 4 / δ := by field_simp; norm_num
    linarith
  have hB : ‖ζ (((1 + δ : ℝ) : ℂ) + 2 * t * I)‖ ≤ 16 :=
    zeta_double_le hσ (by linarith) ht ht3
  have hArp : ‖ζ ((1 + δ : ℝ) : ℂ)‖ ^ ((3 : ℝ) / 4) ≤ 4 / δ ^ ((3 : ℝ) / 4) := by
    calc ‖ζ ((1 + δ : ℝ) : ℂ)‖ ^ ((3 : ℝ) / 4) ≤ (4 / δ) ^ ((3 : ℝ) / 4) :=
          Real.rpow_le_rpow (norm_nonneg _) hA (by norm_num)
      _ = 4 ^ ((3 : ℝ) / 4) / δ ^ ((3 : ℝ) / 4) := Real.div_rpow (by norm_num) hδ.le _
      _ ≤ 4 / δ ^ ((3 : ℝ) / 4) := by
          have hpos : (0 : ℝ) < δ ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hδ _
          have h4 : (4 : ℝ) ^ ((3 : ℝ) / 4) ≤ 4 := by
            calc (4:ℝ) ^ ((3 : ℝ) / 4) ≤ 4 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 4 := Real.rpow_one 4
          gcongr
  have hBrp : ‖ζ (((1 + δ : ℝ) : ℂ) + 2 * t * I)‖ ^ ((1 : ℝ) / 4) ≤ 2 := by
    calc ‖ζ (((1 + δ : ℝ) : ℂ) + 2 * t * I)‖ ^ ((1 : ℝ) / 4) ≤ (16 : ℝ) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (norm_nonneg _) hB (by norm_num)
      _ = 2 := by
          rw [show (16:ℝ) = 2 ^ (4:ℕ) by norm_num, ← Real.rpow_natCast 2 4,
            ← Real.rpow_mul (by norm_num)]
          norm_num
  have hAne : ζ ((1 + δ : ℝ) : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ)
  have hBne : ζ (((1 + δ : ℝ) : ℂ) + 2 * t * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ)
  have hApos : 0 < ‖ζ ((1 + δ : ℝ) : ℂ)‖ ^ ((3 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr hAne) _
  have hBpos : 0 < ‖ζ (((1 + δ : ℝ) : ℂ) + 2 * t * I)‖ ^ ((1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr hBne) _
  have hdpos : (0 : ℝ) < δ ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hδ _
  refine le_trans ?_ hlow
  rw [le_div_iff₀ (mul_pos hApos hBpos)]
  calc δ ^ ((3 : ℝ) / 4) / 8 *
        (‖ζ ((1 + δ : ℝ) : ℂ)‖ ^ ((3 : ℝ) / 4) *
          ‖ζ (((1 + δ : ℝ) : ℂ) + 2 * t * I)‖ ^ ((1 : ℝ) / 4))
      ≤ δ ^ ((3 : ℝ) / 4) / 8 * (4 / δ ^ ((3 : ℝ) / 4) * 2) := by
        gcongr
    _ = 1 := by field_simp; norm_num

/-! ### Down past `σ = 1`, and the annulus -/

/-- **`‖ζ‖ ≥ 10⁻¹⁴` on the annulus `1 - 10⁻¹⁶ ≤ σ ≤ 1`, `1/4 ≤ |t| ≤ 3`.**

The 3-4-1 bound at `σ = 1 + δ` minus the Lipschitz cost of coming back down; with
`δ = 10⁻¹⁶` that is `10⁻¹²/8 - 272·10⁻¹⁶ ≈ 9.8·10⁻¹⁴`, rounded down to `10⁻¹⁴`. -/
lemma zeta_lower_annulus_quant {σ t : ℝ} (hσ : 1 - (1 / 10 : ℝ) ^ (16 : ℕ) ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 1 / 4 ≤ |t|) (ht3 : |t| ≤ 3) :
    (1 / 10 : ℝ) ^ (14 : ℕ) ≤ ‖ζ ((σ : ℂ) + t * I)‖ := by
  set d : ℝ := (1 / 10) ^ (16 : ℕ) with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have hd1 : d ≤ 1 := by rw [hd]; norm_num
  have hd4 : d ≤ 1 / 4 := by rw [hd]; norm_num
  have hrp : d ^ ((3 : ℝ) / 4) = (1 / 10 : ℝ) ^ (12 : ℕ) := by
    rw [hd, ← Real.rpow_natCast (1 / 10 : ℝ) 16, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (1 / 10 : ℝ) 12]
    norm_num
  have hlow := zeta_lower_annulus hd0 hd1 ht ht3
  rw [hrp] at hlow
  clear_value d
  have htne : t ≠ 0 := by
    intro h; rw [h] at ht; simp at ht; linarith
  have hσ34 : (3 : ℝ) / 4 ≤ σ := by
    have hdd : d ≤ 1 / 4 := hd4
    have : (1 : ℝ) - d ≤ σ := hσ
    linarith
  have hderiv : ∀ u ∈ Set.uIoc σ (1 + d), ‖ζ' ((u : ℂ) + t * I)‖ ≤ 136 := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hu
    refine zeta_deriv_le_of_box ?_ ?_ ?_
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
      linarith [hu.1, hσ34]
    · have h := Complex.norm_le_abs_re_add_abs_im ((u : ℂ) + t * I)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_self, add_zero,
        Complex.add_im, Complex.mul_im, zero_add] at h
      have hu1 : |u| ≤ 2 := abs_le.mpr ⟨by linarith [hu.1, hσ34], by linarith [hu.2]⟩
      linarith
    · have h := Complex.abs_im_le_norm (((u : ℂ) + t * I) - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, mul_zero, mul_one,
        zero_add, add_zero] at h
      linarith
  have hint : ‖ζ (((1 + d : ℝ) : ℂ) + t * I) - ζ ((σ : ℂ) + t * I)‖ ≤ 136 * (1 + d - σ) := by
    rw [← Zeta_eq_int_derivZeta (σ₁ := σ) (σ₂ := 1 + d) htne]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hderiv
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + d - σ)] at h
  have hrev := norm_sub_norm_le (ζ (((1 + d : ℝ) : ℂ) + t * I)) (ζ ((σ : ℂ) + t * I))
  have hle : 1 + d - σ ≤ 2 * d := by linarith
  have hgap : (1 / 10 : ℝ) ^ (14 : ℕ) ≤ (1 / 10 : ℝ) ^ (12 : ℕ) / 8 - 136 * (2 * d) := by
    rw [hd]; norm_num
  linarith [hlow, hint, hrev, hgap, hle]

/-- **`ζ` has no zero on the annulus.** -/
lemma zeta_ne_zero_annulus {σ t : ℝ} (hσ : 1 - (1 / 10 : ℝ) ^ (16 : ℕ) ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 1 / 4 ≤ |t|) (ht3 : |t| ≤ 3) : ζ ((σ : ℂ) + t * I) ≠ 0 := by
  intro h
  have hq := zeta_lower_annulus_quant hσ hσ1 ht ht3
  rw [h, norm_zero] at hq
  norm_num at hq

/-- **`‖ζ‖ ≥ 1/2` within `1/3` of the pole** -- the quantitative form of
`zeta_ne_zero_of_dist_le_third`. -/
lemma zeta_lower_pole_disc {s : ℂ} (hs1 : s ≠ 1) (h : ‖s - 1‖ ≤ 1 / 3) :
    (1 / 2 : ℝ) ≤ ‖ζ s‖ := by
  have hre : |s.re - 1| ≤ 1 / 3 := by
    have := Complex.abs_re_le_norm (s - 1)
    simpa using this.trans h
  have hs : 0 < s.re := by rw [abs_le] at hre; linarith
  have hre23 : 2 / 3 ≤ s.re := by rw [abs_le] at hre; linarith
  have hsn : ‖s‖ ≤ 4 / 3 := by
    have := norm_sub_norm_le s 1
    simp only [norm_one] at this
    linarith
  have hpos : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
  have hM : 1 / 2 + ‖s‖ / s.re ≤ 5 / 2 := by
    have : ‖s‖ / s.re ≤ (4 / 3) / (2 / 3) :=
      div_le_div₀ (by norm_num) hsn (by norm_num) hre23
    linarith
  have hsp := ZetaSubPole_le hs hs1
  have hinv : (3 : ℝ) ≤ ‖1 / (s - 1)‖ := by
    rw [norm_div, norm_one, le_div_iff₀ hpos]
    linarith
  have hrev : ‖1 / (s - 1)‖ - ‖ζ s‖ ≤ ‖1 / (s - 1) - ζ s‖ := norm_sub_norm_le _ _
  rw [show (1 : ℂ) / (s - 1) - ζ s = -(ζ s - 1 / (s - 1)) by ring, norm_neg] at hrev
  linarith

/-- **`‖ζ'/ζ‖ ≤ 136·10¹⁴` on the annulus part of the box**, `1 - 10⁻¹⁶ ≤ σ ≤ 1`,
`1/4 ≤ |t| ≤ 3`.  This is what `I4Bound`'s `sSup` over the segment at `Im s = -3` needs;
the segment reaches `σ = 1`, which is why the hypothesis is `σ ≤ 1` and not `σ < 1`. -/
lemma logDeriv_zeta_le_annulus {σ t : ℝ} (hσ : 1 - (1 / 10 : ℝ) ^ (16 : ℕ) ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 1 / 4 ≤ |t|) (ht3 : |t| ≤ 3) :
    ‖ζ' ((σ : ℂ) + t * I) / ζ ((σ : ℂ) + t * I)‖ ≤ 136 * 10 ^ (14 : ℕ) := by
  have hlow := zeta_lower_annulus_quant hσ hσ1 ht ht3
  have hpos : (0 : ℝ) < ‖ζ ((σ : ℂ) + t * I)‖ := by
    have : (0 : ℝ) < (1 / 10 : ℝ) ^ (14 : ℕ) := by norm_num
    linarith
  have hσ34 : (3 : ℝ) / 4 ≤ σ := by
    have hd4 : (1 / 10 : ℝ) ^ (16 : ℕ) ≤ 1 / 4 := by norm_num
    linarith
  have hderiv : ‖ζ' ((σ : ℂ) + t * I)‖ ≤ 136 := by
    refine zeta_deriv_le_of_box ?_ ?_ ?_
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
      linarith
    · have h := Complex.norm_le_abs_re_add_abs_im ((σ : ℂ) + t * I)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_self, add_zero,
        Complex.add_im, Complex.mul_im, zero_add] at h
      have : |σ| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    · have h := Complex.abs_im_le_norm (((σ : ℂ) + t * I) - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, mul_zero, mul_one,
        zero_add, add_zero] at h
      linarith
  rw [norm_div, div_le_iff₀ hpos]
  have h14 : (1 : ℝ) ≤ 10 ^ (14 : ℕ) * (1 / 10 : ℝ) ^ (14 : ℕ) := by norm_num
  nlinarith [hderiv, hlow, hpos]

/-- `‖ζ(s) - 1/(s-1)‖ ≤ 1/2 + ‖s‖/Re s`, stated for Mathlib's entire completion
`riemannZeta₀` so that it also covers `s = 1`, where the value is `γ < 2/3`. -/
lemma norm_riemannZeta₀_le {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₀ s‖ ≤ 1 / 2 + ‖s‖ / s.re := by
  rcases eq_or_ne s 1 with rfl | h
  · rw [riemannZeta₀_one]
    have h1 : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
    have h2 : (1 : ℝ) / 2 < Real.eulerMascheroniConstant := Real.one_half_lt_eulerMascheroniConstant
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    norm_num
    linarith
  · have hz : riemannZeta₀ s = ζ s - 1 / (s - 1) := by
      simp only [riemannZeta₀, h, ↓reduceIte, one_div]
    rw [hz]
    exact ZetaSubPole_le hs h

/-- **A Cauchy estimate that works across the pole.**  `riemannZeta₀` is entire, so the disc
may contain `s = 1`; this is what `zeta_deriv_le_of_box` cannot do. -/
lemma riemannZeta₀_deriv_le {s : ℂ} (hre : 3 / 4 ≤ s.re) (hs : ‖s‖ ≤ 5) :
    ‖deriv riemannZeta₀ s‖ ≤ 72 := by
  have hR : (0 : ℝ) < 1 / 8 := by norm_num
  have hd : DiffContOnCl ℂ riemannZeta₀ (Metric.ball s (1 / 8)) :=
    differentiable_riemannZeta₀.diffContOnCl
  have hC : ∀ z ∈ Metric.sphere s (1 / 8), ‖riemannZeta₀ z‖ ≤ 9 := by
    intro z hz
    simp only [Metric.mem_sphere, Complex.dist_eq] at hz
    have hzre : 5 / 8 ≤ z.re := by
      have h := Complex.abs_re_le_norm (z - s)
      rw [hz] at h
      simp only [Complex.sub_re] at h
      rw [abs_le] at h
      linarith
    have hzn : ‖z‖ ≤ 5 + 1 / 8 := by
      have h := norm_sub_norm_le z s
      rw [hz] at h
      linarith
    have hb := norm_riemannZeta₀_le (show (0 : ℝ) < z.re by linarith)
    have hfrac : ‖z‖ / z.re ≤ (5 + 1 / 8) / (5 / 8) :=
      div_le_div₀ (by norm_num) hzn (by norm_num) hzre
    norm_num at hb hfrac ⊢
    linarith
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd hC
  norm_num at hcauchy
  linarith

/-- `‖ζ'(s)‖ ≤ 72 + ‖s-1‖⁻²`, valid arbitrarily close to the pole. -/
lemma zeta_deriv_le_near_pole {s : ℂ} (hre : 3 / 4 ≤ s.re) (hs : ‖s‖ ≤ 5) (h1 : s ≠ 1) :
    ‖ζ' s‖ ≤ 72 + (1 / ‖s - 1‖) ^ 2 := by
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_add h1]
  have hg := riemannZeta₀_deriv_le hre hs
  have hnorm : ‖(-((s - 1)⁻¹) ^ 2 : ℂ)‖ = (1 / ‖s - 1‖) ^ 2 := by
    rw [norm_neg, norm_pow, norm_inv, one_div]
  calc ‖-((s - 1)⁻¹) ^ 2 + deriv riemannZeta₀ s‖
      ≤ ‖(-((s - 1)⁻¹) ^ 2 : ℂ)‖ + ‖deriv riemannZeta₀ s‖ := norm_add_le _ _
    _ ≤ (1 / ‖s - 1‖) ^ 2 + 72 := by rw [hnorm]; linarith
    _ = 72 + (1 / ‖s - 1‖) ^ 2 := by ring

/-! ### The explicit box -/

@[blueprint
  (title := "ZetaNoZerosInBoxThree")
  (statement := /--
  For $|t| \le 3$ and $\sigma \ge 1 - 10^{-16}$ one has $\zeta(\sigma+tI) \ne 0$.
  -/)
  (proof := /--
  Three regimes.  For $\sigma \ge 1$ this is the classical non-vanishing on the line.
  For $|t| \le 1/4$ the pole term dominates: $|\zeta(s) - 1/(s-1)| \le 1/2 + |s|/\Re s$
  on $\Re s > 0$, so $\zeta$ cannot vanish within $1/3$ of $s=1$.  On the annulus
  $1/4 \le |t| \le 3$ it is the $3+4\cos+\cos 2$ inequality, fed with
  \ref{ZetaNear1BndAdd} for $|\zeta(\sigma)|$ and the same pole bound for
  $|\zeta(\sigma+2it)| \le 16$, giving $|\zeta(1+\delta+it)| \ge \delta^{3/4}/8$; a
  Cauchy estimate on a disc of radius $1/8$ bounds $|\zeta'|$ by $136$ there, and
  $\delta = 10^{-16}$ then pushes the bound below $\sigma = 1$.  The regimes are needed
  separately because the $3$-$4$-$1$ argument degrades as $t \to 0$, where
  $\zeta(\sigma+2it)$ approaches the pole.
  -/)
  (latexEnv := "theorem")]
theorem ZetaNoZerosInBoxThree (t : ℝ) (ht : |t| ≤ 3) (σ : ℝ)
    (hσ : σ ≥ 1 - (1 / 10 : ℝ) ^ (16 : ℕ)) : ζ ((σ : ℂ) + t * I) ≠ 0 := by
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  rcases le_or_gt 1 σ with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re (by rw [hre]; exact h1)
  rcases le_or_gt (1 / 4 : ℝ) |t| with h2 | h2
  · exact zeta_ne_zero_annulus hσ h1.le h2 ht
  · refine zeta_ne_zero_of_dist_le_third ?_ ?_
    · intro h
      have : ((σ : ℂ) + t * I).re = (1 : ℂ).re := by rw [h]
      rw [hre] at this
      simp at this
      linarith
    · have h := Complex.norm_le_abs_re_add_abs_im ((σ : ℂ) + t * I - 1)
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero,
        Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, mul_zero, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
        zero_add] at h
      have hd16 : (1 / 10 : ℝ) ^ (16 : ℕ) ≤ 1 / 12 := by norm_num
      have hab : |σ - 1| ≤ 1 / 12 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith

/-- The strip width in `LogDerivZetaHolcSmallT`, from the explicit box. -/
noncomputable def zetaSmallTσ : ℝ := 1 - (1 / 10 : ℝ) ^ (16 : ℕ)

lemma zetaSmallTσ_lt_one : zetaSmallTσ < 1 := by unfold zetaSmallTσ; norm_num

/-- **`‖ζ'/ζ‖ ≤ 3·10³²` on the vertical segment `{1 - 10⁻¹⁶} × [-3,3]`** — the segment
`I5Bound` bounds by compactness.  Near `t = 0` this needs the estimate above, since `ζ'`
itself is of size `10³²` there. -/
lemma logDeriv_zeta_le_smallT {t : ℝ} (ht : |t| ≤ 3) :
    ‖ζ' ((zetaSmallTσ : ℂ) + t * I) / ζ ((zetaSmallTσ : ℂ) + t * I)‖ ≤ 3 * 10 ^ (32 : ℕ) := by
  have hσv : zetaSmallTσ = 1 - (1 / 10 : ℝ) ^ (16 : ℕ) := rfl
  have hσ1 : zetaSmallTσ < 1 := zetaSmallTσ_lt_one
  have hσ34 : (3 : ℝ) / 4 ≤ zetaSmallTσ := by rw [hσv]; norm_num
  have hre : ((zetaSmallTσ : ℂ) + t * I).re = zetaSmallTσ := by simp
  have hne : ((zetaSmallTσ : ℂ) + t * I) ≠ 1 := by
    intro hh
    have : ((zetaSmallTσ : ℂ) + t * I).re = (1 : ℂ).re := by rw [hh]
    rw [hre] at this
    simp at this
    linarith
  rcases le_or_gt (1 / 4 : ℝ) |t| with h | h
  · have hb := logDeriv_zeta_le_annulus (by rw [hσv]) hσ1.le h ht
    have : (136 : ℝ) * 10 ^ (14 : ℕ) ≤ 3 * 10 ^ (32 : ℕ) := by norm_num
    linarith
  · have hsn : ‖((zetaSmallTσ : ℂ) + t * I)‖ ≤ 5 := by
      have hh := Complex.norm_le_abs_re_add_abs_im ((zetaSmallTσ : ℂ) + t * I)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_self, add_zero,
        Complex.add_im, Complex.mul_im, zero_add] at hh
      have : |zetaSmallTσ| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have hdist : ‖((zetaSmallTσ : ℂ) + t * I) - 1‖ ≤ 1 / 3 := by
      have hh := Complex.norm_le_abs_re_add_abs_im ((zetaSmallTσ : ℂ) + t * I - 1)
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero,
        Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, mul_zero, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
        zero_add] at hh
      have hd16 : (1 / 10 : ℝ) ^ (16 : ℕ) ≤ 1 / 12 := by norm_num
      have hab : |zetaSmallTσ - 1| ≤ 1 / 12 := by
        rw [hσv]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩
      linarith
    have hlow : (1 / 2 : ℝ) ≤ ‖ζ ((zetaSmallTσ : ℂ) + t * I)‖ := zeta_lower_pole_disc hne hdist
    have hrlow : (1 / 10 : ℝ) ^ (16 : ℕ) ≤ ‖((zetaSmallTσ : ℂ) + t * I) - 1‖ := by
      have hh := Complex.abs_re_le_norm ((zetaSmallTσ : ℂ) + t * I - 1)
      simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, mul_one,
        sub_self, add_zero] at hh
      rw [hσv] at hh ⊢
      rw [abs_of_nonpos (by norm_num)] at hh
      linarith
    have hrpos : (0 : ℝ) < ‖((zetaSmallTσ : ℂ) + t * I) - 1‖ := by
      have : (0 : ℝ) < (1 / 10 : ℝ) ^ (16 : ℕ) := by norm_num
      linarith
    have hsq : (1 / ‖((zetaSmallTσ : ℂ) + t * I) - 1‖) ^ 2 ≤ 10 ^ (32 : ℕ) := by
      have h1 : 1 / ‖((zetaSmallTσ : ℂ) + t * I) - 1‖ ≤ 10 ^ (16 : ℕ) := by
        rw [div_le_iff₀ hrpos]
        have : (1 : ℝ) = 10 ^ (16 : ℕ) * (1 / 10 : ℝ) ^ (16 : ℕ) := by norm_num
        nlinarith [hrlow]
      have h0 : (0 : ℝ) ≤ 1 / ‖((zetaSmallTσ : ℂ) + t * I) - 1‖ := by positivity
      nlinarith [h1, h0]
    have hd := zeta_deriv_le_near_pole (by rw [hre]; exact hσ34) hsn hne
    rw [norm_div, div_le_iff₀ (by linarith)]
    nlinarith [hd, hsq, hlow]

@[blueprint
  (title := "LogDerivZetaHolcSmallTExplicit")
  (statement := /--
  With $\sigma_2 = 1 - 10^{-16}$, $\zeta'/\zeta$ is holomorphic on
  $[\sigma_2, 2] \times [-3,3] \setminus \{1\}$.
  -/)
  (proof := /-- The proof of Lemma \ref{LogDerivZetaHolcSmallT}, with its witness named -- the
  zero-free input is \ref{ZetaNoZerosInBoxThree} in place of the compactness argument. -/)
  (latexEnv := "lemma")]
theorem LogDerivZetaHolcSmallTExplicit :
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( [[ zetaSmallTσ, 2 ]] ×ℂ [[ -3, 3 ]]) \ {1}) := by
  have hσ₂_lt_one : zetaSmallTσ < 1 := zetaSmallTσ_lt_one
  have hζ_ne_zero : ∀ (t : ℝ) (_ : |t| ≤ 3) (σ' : ℝ) (_ : σ' ≥ zetaSmallTσ),
      ζ ((σ' : ℂ) + t * I) ≠ 0 := fun t ht σ' hσ' => ZetaNoZerosInBoxThree t ht σ' hσ'
  set σ₂ := zetaSmallTσ
  let U := ([[σ₂, 2]] ×ℂ [[-3, 3]]) \ {1}
  have s_in_U_im_le3 : ∀ s ∈ U, |s.im| ≤ 3 := by
    intro s hs
    rw [Set.mem_sdiff_singleton] at hs
    rcases hs with ⟨hbox, _hne⟩
    rcases hbox with ⟨hre, him⟩
    simp only [Set.mem_preimage] at him
    obtain ⟨him_lower, him_upper⟩ := him
    apply abs_le.2
    simp only [neg_le_self_iff, Nat.ofNat_nonneg, inf_of_le_left] at him_lower
    simp only [neg_le_self_iff, Nat.ofNat_nonneg, sup_of_le_right] at him_upper
    exact ⟨him_lower, him_upper⟩

  have s_in_U_re_ges2 : ∀ s ∈ U, σ₂ ≤ s.re := by
    intro s hs
    rw [Set.mem_sdiff_singleton] at hs
    rcases hs with ⟨hbox, _hne⟩
    rcases hbox with ⟨hre, _him⟩
    simp only [Set.mem_preimage] at hre
    obtain ⟨hre_lower, hre_upper⟩ := hre
    have : min σ₂ 2 = σ₂ := by
      apply min_eq_left
      linarith [hσ₂_lt_one]
    rwa [← this]

  apply LogDerivZetaHoloOn
  · exact Set.notMem_sdiff_of_mem rfl
  · intro s hs
    rw[← re_add_im s]
    apply hζ_ne_zero
    · apply s_in_U_im_le3 _ hs
    · apply s_in_U_re_ges2 _ hs

/-- The strip width in `LogDerivZetaHolcLargeT`. -/
noncomputable def zetaHolcLargeTA : ℝ :=
  min zetaLowerBndA ((1 - zetaSmallTσ) * Real.log 3 ^ 9)

lemma zetaHolcLargeTA_mem : zetaHolcLargeTA ∈ Ioc 0 (1 / 2) := by
  have A_inter : zetaLowerBndA ∈ Ioc 0 (1 / 2) := zetaLowerBndA_mem
  have σ₁_lt_one : zetaSmallTσ < 1 := zetaSmallTσ_lt_one
  unfold zetaHolcLargeTA
  constructor
  · apply lt_min A_inter.1
    bound
  · exact le_trans (min_le_left _ _) A_inter.2

@[blueprint
  (title := "LogDerivZetaHolcLargeTExplicit")
  (statement := /--
  With $A_0 = \min(A, 10^{-16}(\log 3)^9)$, where $A$ is the zero-free strip of
  \ref{ZetaLowerBndExplicit}, $\zeta'/\zeta$ is holomorphic on
  $[1 - A_0/(\log T)^9, 2] \times [-T,T] \setminus \{1\}$ for every $T \ge 3$.
  -/)
  (proof := /-- The proof of Lemma \ref{LogDerivZetaHolcLargeT}, with its witness named. -/)
  (latexEnv := "lemma")]
theorem LogDerivZetaHolcLargeTExplicit : ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( (Icc ((1 : ℝ) - zetaHolcLargeTA / Real.log T ^ 9) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by
  have A_inter : zetaLowerBndA ∈ Ioc 0 (1 / 2) := zetaLowerBndA_mem
  have restOfZetaZeroFree := ZetaZeroFreeExplicit
  have σ₁_lt_one : zetaSmallTσ < 1 := zetaSmallTσ_lt_one
  have noZerosInBox : ∀ (t : ℝ) (_ : |t| ≤ 3) (σ' : ℝ) (_ : σ' ≥ zetaSmallTσ),
      ζ ((σ' : ℂ) + t * I) ≠ 0 := fun t ht σ' hσ' => ZetaNoZerosInBoxThree t ht σ' hσ'
  intro T hT
  unfold zetaHolcLargeTA
  set A := zetaLowerBndA
  set σ₁ := zetaSmallTσ
  set A₀ := min A ((1 - σ₁) * Real.log 3 ^ 9) with hA₀
  apply LogDerivZetaHoloOn
  · exact Set.notMem_sdiff_of_mem rfl
  intro s hs
  rcases le_or_gt 1 s.re with one_le|lt_one
  · exact riemannZeta_ne_zero_of_one_le_re one_le
  rw [← re_add_im s]
  have := Complex.mem_reProdIm.mp hs.1
  rcases lt_or_ge 3 |s.im| with gt3|le3
  · apply restOfZetaZeroFree _ _ gt3
    refine ⟨?_, lt_one⟩
    calc
      _ ≤ 1 - A₀ / Real.log T ^ 9 := by
        gcongr
        · exact A_inter.1.le
        · bound
        · bound
        · bound
        · exact abs_le.mpr ⟨this.2.1, this.2.2⟩
      _ ≤ _:= by exact this.1.1

  · apply noZerosInBox _ le3
    calc
      _ ≥ 1 - A₀ / Real.log T ^ 9 := by exact this.1.1
      _ ≥ 1 - A₀ / Real.log 3 ^ 9 := by
        gcongr
        apply le_min A_inter.1.le
        bound
      _ ≥ 1 - (((1 - σ₁) * Real.log 3 ^ 9)) / Real.log 3 ^ 9:= by
        gcongr
        apply min_le_right
      _ = _ := by field_simp; simp

open ArithmeticFunction (vonMangoldt)

local notation "Λ" => vonMangoldt

section TrivBoundExplicit

open MeasureTheory

lemma mertens_Icc {x : ℝ} (hx : 1 ≤ x) :
    ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt k) / k ≤ Real.log x + (Real.log 4 + 4) := by
  have h := Mertens.E₁Λ.le hx
  unfold Mertens.E₁Λ at h
  rw [show Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ from (Finset.Ioc_eq_Icc _ _).symm]
  linarith

lemma sum_vonMangoldt_div_nonneg (n : ℕ) : 0 ≤ ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt k) / k :=
  Finset.sum_nonneg fun k _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)

lemma sum_vonMangoldt_div_isBigO {r : ℝ} (hr : 0 < r) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt k) / k) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ r := by
  have hlog : (fun n : ℕ ↦ Real.log n) =o[atTop] fun n : ℕ ↦ (n : ℝ) ^ r :=
    (isLittleO_log_rpow_atTop hr).comp_tendsto tendsto_natCast_atTop_atTop
  have hconst : (fun _ : ℕ ↦ (Real.log 4 + 4)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ r := by
    refine Asymptotics.IsBigO.of_bound (Real.log 4 + 4) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hge : (1 : ℝ) ≤ (n : ℝ) ^ r := by
      simpa using Real.rpow_le_rpow (by norm_num) h1 hr.le
    have hK : (0 : ℝ) < Real.log 4 + 4 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hK.le,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) ^ r)]
    nlinarith
  refine Asymptotics.IsBigO.trans ?_ (hlog.isBigO.add hconst)
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hle := mertens_Icc h1
  rw [Nat.floor_natCast n] at hle
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sum_vonMangoldt_div_nonneg n),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.log (n : ℝ) + (Real.log 4 + 4))]
  linarith

lemma LSeries_vonMangoldt_shift (σ : ℝ) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)
      = LSeries (fun n => (((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) : ℝ) : ℂ)) (((σ - 1 : ℝ)) : ℂ) := by
  unfold LSeries
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [show ((σ : ℝ) : ℂ) = (((σ - 1 : ℝ)) : ℂ) + 1 by push_cast; ring,
      Complex.cpow_add _ _ hn0, Complex.cpow_one]
    push_cast
    field_simp

/-! ### The integral bound -/

/-- The pointwise norm of the Abel-summation integrand. -/
lemma abel_integrand_norm (σ : ℝ) {t : ℝ} (ht : 1 < t) :
    ‖(∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (((ArithmeticFunction.vonMangoldt k : ℝ) / (k : ℝ) : ℝ) : ℂ)) *
        (t : ℂ) ^ (-((((σ - 1 : ℝ)) : ℂ) + 1))‖
      = (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k) / k) * t ^ (-σ) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hsum : (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (((ArithmeticFunction.vonMangoldt k : ℝ) / (k : ℝ) : ℝ) : ℂ))
      = ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k) / k : ℝ) : ℂ) := by push_cast; ring
  rw [hsum, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sum_vonMangoldt_div_nonneg _), norm_cpow_eq_rpow_re_of_pos ht0]
  congr 1
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
  ring_nf

/-- The dominating integral. -/
lemma abel_dominating_integral {σ : ℝ} (hσ : 1 < σ) :
    ∫ t in Ioi (1:ℝ), (Real.log t + (Real.log 4 + 4)) * t ^ (-σ)
      = 1 / (σ - 1) ^ 2 + (Real.log 4 + 4) / (σ - 1) := by
  have hδ : (0 : ℝ) < σ - 1 := by linarith
  have hexp : -(σ - 1) - 1 = -σ := by ring
  have hint1 : IntegrableOn (fun t : ℝ => Real.log t * t ^ (-σ)) (Ioi 1) volume := by
    have h := DerivUpperBnd_aux7_4 (a := 1) (σ := σ - 1) hδ le_rfl
    rw [hexp] at h
    simpa [mul_comm] using h
  have hint2 : IntegrableOn (fun t : ℝ => (Real.log 4 + 4) * t ^ (-σ)) (Ioi 1) volume :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  have h1 : ∫ t in Ioi (1:ℝ), Real.log t * t ^ (-σ) = 1 / (σ - 1) ^ 2 := by
    have h := DerivUpperBnd_aux7_integral_eq (a := 1) (σ := σ - 1) le_rfl hδ
    rw [hexp] at h
    simp only [Real.one_rpow, Real.log_one, mul_zero, add_zero, mul_one] at h
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)
  have h2 : ∫ t in Ioi (1:ℝ), t ^ (-σ) = 1 / (σ - 1) := by
    have h := integral_Ioi_rpow_of_lt (a := -σ) (by linarith) (c := 1) one_pos
    rw [h]
    rw [show -σ + 1 = -(σ - 1) by ring]
    simp only [Real.one_rpow]
    field_simp
  rw [show (fun t : ℝ => (Real.log t + (Real.log 4 + 4)) * t ^ (-σ))
      = fun t : ℝ => Real.log t * t ^ (-σ) + (Real.log 4 + 4) * t ^ (-σ) from
        funext fun t => by ring]
  rw [integral_add hint1 hint2, h1, integral_const_mul, h2]
  field_simp

/-! ### The key bound, and `triv_bound_zeta` with a numeral -/

/-- `∑ Λ(n) n^{-σ} ≤ 1/(σ-1) + (log 4 + 4)` for `σ > 1`. -/
lemma LSeries_vonMangoldt_norm_le {σ : ℝ} (hσ : 1 < σ) :
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)‖ ≤ (σ - 1)⁻¹ + (Real.log 4 + 4) := by
  have hδ : (0 : ℝ) < σ - 1 := by linarith
  have hint : IntegrableOn
      (fun t : ℝ => (Real.log t + (Real.log 4 + 4)) * t ^ (-σ)) (Ioi 1) volume := by
    have hint1 : IntegrableOn (fun t : ℝ => Real.log t * t ^ (-σ)) (Ioi 1) volume := by
      have h := DerivUpperBnd_aux7_4 (a := 1) (σ := σ - 1) hδ le_rfl
      rw [show -(σ - 1) - 1 = -σ by ring] at h
      simpa [mul_comm] using h
    have hint2 : IntegrableOn (fun t : ℝ => (Real.log 4 + 4) * t ^ (-σ)) (Ioi 1) volume :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
    exact (hint1.add hint2).congr_fun (fun t _ => by simp only [Pi.add_apply]; ring)
      measurableSet_Ioi
  rw [LSeries_vonMangoldt_shift σ,
    LSeries_eq_mul_integral_of_nonneg (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) / n) (r := (σ - 1) / 2)
      (by positivity) (s := (((σ - 1 : ℝ)) : ℂ)) (by simpa using (by linarith : (σ-1)/2 < σ-1))
      (sum_vonMangoldt_div_isBigO (by positivity))
      (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)),
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ.le]
  have hbound : ‖∫ t in Ioi (1:ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (((ArithmeticFunction.vonMangoldt k : ℝ) / (k : ℝ) : ℝ) : ℂ)) *
      (t : ℂ) ^ (-((((σ - 1 : ℝ)) : ℂ) + 1))‖ ≤ 1 / (σ - 1) ^ 2 + (Real.log 4 + 4) / (σ - 1) := by
    calc _ ≤ ∫ t in Ioi (1:ℝ), ‖(∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (((ArithmeticFunction.vonMangoldt k : ℝ) / (k : ℝ) : ℝ) : ℂ)) *
              (t : ℂ) ^ (-((((σ - 1 : ℝ)) : ℂ) + 1))‖ := norm_integral_le_integral_norm _
      _ = ∫ t in Ioi (1:ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k) / k) * t ^ (-σ) :=
          setIntegral_congr_fun measurableSet_Ioi (fun t ht => abel_integrand_norm σ ht)
      _ ≤ ∫ t in Ioi (1:ℝ), (Real.log t + (Real.log 4 + 4)) * t ^ (-σ) := by
          refine integral_mono_of_nonneg ?_ hint ?_
          · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
            have : (0:ℝ) < t := lt_trans one_pos ht
            exact mul_nonneg (sum_vonMangoldt_div_nonneg _) (Real.rpow_nonneg this.le _)
          · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
            have ht1 : (1:ℝ) ≤ t := le_of_lt ht
            have h0 : (0:ℝ) ≤ t ^ (-σ) := Real.rpow_nonneg (by linarith) _
            exact mul_le_mul_of_nonneg_right (mertens_Icc ht1) h0
      _ = _ := abel_dominating_integral hσ
  calc (σ - 1) * ‖∫ t in Ioi (1:ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (((ArithmeticFunction.vonMangoldt k : ℝ) / (k : ℝ) : ℝ) : ℂ)) *
        (t : ℂ) ^ (-((((σ - 1 : ℝ)) : ℂ) + 1))‖
      ≤ (σ - 1) * (1 / (σ - 1) ^ 2 + (Real.log 4 + 4) / (σ - 1)) := by
        exact mul_le_mul_of_nonneg_left hbound hδ.le
    _ = (σ - 1)⁻¹ + (Real.log 4 + 4) := by field_simp

/-- **`triv_bound_zeta` with a numeral**: `C = log 4 + 4`. -/
theorem triv_bound_zeta_explicit (σ₀ t : ℝ) (hσ₀ : 1 < σ₀) :
    ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ (σ₀ - 1)⁻¹ + (Real.log 4 + 4) := by
  refine le_trans (dlog_riemannZeta_bdd_on_vertical_lines_generalized σ₀ σ₀ t hσ₀ le_rfl) ?_
  have hre : (1 : ℝ) < ((σ₀ : ℂ)).re := by simpa using hσ₀
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  have hnorm : ‖ζ' (σ₀ : ℂ) / ζ (σ₀ : ℂ)‖ = ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ₀ : ℂ)‖ := by
    rw [h, neg_div, norm_neg]
  rw [hnorm]
  exact LSeries_vonMangoldt_norm_le hσ₀

end TrivBoundExplicit

/-- The constant of `triv_bound_zeta`, as a numeral. -/
noncomputable def zetaTrivC : ℝ := Real.log 4 + 4

lemma zetaTrivC_nonneg : 0 ≤ zetaTrivC := by
  unfold zetaTrivC; positivity

lemma zetaTrivC_bound (σ₀ t : ℝ) (hσ₀ : 1 < σ₀) :
    ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ (σ₀ - 1)⁻¹ + zetaTrivC :=
  triv_bound_zeta_explicit σ₀ t hσ₀

/-- The constant in `LogDerivZetaBndUnif`. -/
noncomputable def zetaLogDerivUnifC : ℝ :=
  (1 + zetaLogDerivC + zetaTrivC) * zetaLogDerivA⁻¹

lemma zetaLogDerivUnifC_pos : 0 < zetaLogDerivUnifC := by
  have h1 := zetaLogDerivC_pos
  have h2 := zetaTrivC_nonneg
  have h3 := zetaLogDerivA_mem.1
  unfold zetaLogDerivUnifC
  positivity

@[blueprint
  (title := "LogDerivZetaBndUnifExplicit")
  (statement := /--
  With $A$ as in Lemma \ref{LogDerivZetaBndExplicit} and
  $C = (1 + C_{\mathrm{logderiv}} + C_{\mathrm{triv}})A^{-1}$,
  $$
  \left|\frac{\zeta'}{\zeta}(\sigma+tI)\right| \le C(\log|t|)^9
  $$
  whenever $|t| > 3$ and $\sigma \ge 1 - A/(\log|t|)^9$.  Here $C_{\mathrm{triv}}$ is the
  constant in the trivial bound $|\zeta'/\zeta(\sigma+it)| \le (\sigma-1)^{-1} + C_{\mathrm{triv}}$
  for $\sigma > 1$.
  -/)
  (proof := /-- The proof of Lemma \ref{LogDerivZetaBndUnif}, with its two witnesses named. -/)
  (latexEnv := "lemma")]
lemma LogDerivZetaBndUnifExplicit (σ : ℝ) (t : ℝ) (hyp_t : 3 < |t|)
    (hyp_σ : σ ∈ Ici (1 - zetaLogDerivA / Real.log |t| ^ 9)) :
    ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ zetaLogDerivUnifC * Real.log |t| ^ 9 := by
  have pf_A : zetaLogDerivA ∈ Ioc 0 (1 / 2) := zetaLogDerivA_mem
  have C_pos : 0 < zetaLogDerivC := zetaLogDerivC_pos
  have ζbd_in := LogDerivZetaBndExplicit
  have pf_C_triv : 0 ≤ zetaTrivC := zetaTrivC_nonneg
  have ζbd_out := zetaTrivC_bound
  unfold zetaLogDerivUnifC
  set A := zetaLogDerivA
  set C := zetaLogDerivC
  set C_triv := zetaTrivC
  have T0 : A > 0 := pf_A.1

  have ha : 1 ≤ A⁻¹ := by
    simp only [one_div, mem_Ioc, true_and, T0] at pf_A
    have U := (inv_le_inv₀ (by positivity) (by positivity)).mpr pf_A
    simp only [inv_inv] at U
    linarith

  have logt_gt' : (1 : ℝ) < Real.log |t| ^ 9 := by
    calc
      1 < Real.log |t| := logt_gt_one hyp_t.le
      _ ≤ (Real.log |t|) ^ 9 := ZetaInvBnd_aux (logt_gt_one hyp_t.le)

  have logt_gt'' : (1 : ℝ) < 1 + A / Real.log |t| ^ 9 := by
    simp only [lt_add_iff_pos_right, div_pos_iff_of_pos_left, T0]
    positivity

  have T1 : ∀⦃σ : ℝ⦄, 1 + A / Real.log |t| ^ 9 ≤ σ → 1 < σ := by
    intros
    linarith

  have T2 : ∀⦃σ : ℝ⦄, 1 + A / Real.log |t| ^ 9 ≤ σ → A / Real.log |t| ^ 9 ≤ σ - 1 := by
    intro σ' hyp_σ'
    calc
      A / Real.log |t| ^ 9 = (1 + A / Real.log |t| ^ 9) - 1 := by ring_nf
      _ ≤ σ' - 1 := by gcongr

  by_cases h : σ ∈ Ico (1 - A / Real.log |t| ^ 9) (1 + A / Real.log |t| ^ 9)
  · calc
      ‖ζ' (↑σ + ↑t * I) / ζ (↑σ + ↑t * I)‖ ≤ C * Real.log |t| ^ 9 := ζbd_in σ t hyp_t h
      _ ≤ ((1 + C + C_triv) * A⁻¹) * Real.log |t| ^ 9 := by
          gcongr
          · calc
              C ≤ 1 + C := by simp only [le_add_iff_nonneg_left, zero_le_one]
              _ ≤ (1 + C + C_triv) * 1 := by simp only [mul_one, le_add_iff_nonneg_right]; positivity
              _ ≤ (1 + C + C_triv) * A⁻¹ := by gcongr

  · simp only [mem_Ico, tsub_le_iff_right, not_and, not_lt, mem_Ici] at h hyp_σ
    replace h := h hyp_σ
    calc
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ = ‖-ζ' (σ + t * I) / ζ (σ + t * I)‖ := by simp only [Complex.norm_div,
        norm_neg]

      _ ≤ (σ - 1)⁻¹ + C_triv := ζbd_out σ t (by exact T1 h)

      _ ≤ (A / Real.log |t| ^ 9)⁻¹ + C_triv := by
          gcongr
          · exact T2 h

      _ ≤ (A / Real.log |t| ^ 9)⁻¹ + C_triv * A⁻¹ := by
          gcongr
          exact le_mul_of_one_le_right pf_C_triv ha

      _ ≤ (1 + C_triv) * A⁻¹ * Real.log |t| ^ 9 := by
          simp only [inv_div]
          ring_nf
          gcongr
          · simp only [inv_pos, le_mul_iff_one_le_left, T0]
            linarith

      _ ≤ (1 + C + C_triv) * A⁻¹ * Real.log |t| ^ 9 := by gcongr; simp only [le_add_iff_nonneg_right]; positivity

/-!
### Numerical bounds on the constants above

Everything from `zetaStripA` down is a closed form in `exp (1/2)`, fourth roots and `log 2`.
This section collapses the two the rest of the chain actually reads -- `zetaLogDerivUnifC`
from above and `zetaHolcLargeTA` from below -- to decimal powers of ten.  The bounds are
deliberately loose (`10^28` against a true value of `2.6·10^25`, `10^-16` against
`2.3·10^-16`); what matters is that they are numerals.

The one step that needs care is `zetaInvBndC`, whose denominator
`C₁·A^{3/4} - 2C₂·A` is a difference of two nearly equal quantities: at `A = r⁴/2` with
`r = C₁/(2C₂)` the ratio of the two terms is exactly `2^{1/4} = 1.189`, so no interval
bound on `A` survives.  `zetaInvBnd_gap_ge` uses the identity
`A^{3/4} = 2^{-3/4} r³` instead, which turns the difference into `r³ C₁ (2^{-3/4} - 1/2)`.
-/

/-! ### rpow helpers: turn a quarter-power into a fourth power -/

lemma rpow_pow_four {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    (x ^ a) ^ (4 : ℕ) = x ^ (4 * a) := by
  rw [← Real.rpow_natCast (x ^ a) 4, ← Real.rpow_mul hx]
  norm_num
  ring_nf

lemma rpow_quarter_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ≤ c ^ 4) :
    x ^ ((1 : ℝ) / 4) ≤ c := by
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hc ?_
  rw [rpow_pow_four hx]
  norm_num
  exact h

lemma le_rpow_quarter {x c : ℝ} (hx : 0 ≤ x) (_hc : 0 ≤ c) (h : c ^ 4 ≤ x) :
    c ≤ x ^ ((1 : ℝ) / 4) := by
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (Real.rpow_nonneg hx _) ?_
  rw [rpow_pow_four hx]
  norm_num
  exact h

lemma rpow_three_quarter_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ^ 3 ≤ c ^ 4) :
    x ^ ((3 : ℝ) / 4) ≤ c := by
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hc ?_
  rw [rpow_pow_four hx, show (4 : ℝ) * ((3 : ℝ) / 4) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  exact h

lemma le_rpow_tenth {x c : ℝ} (hx : 0 ≤ x) (h : c ^ 10 ≤ x) : c ≤ x ^ ((1 : ℝ) / 10) := by
  refine le_of_pow_le_pow_left₀ (n := 10) (by norm_num) (Real.rpow_nonneg hx _) ?_
  rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 10)) 10, ← Real.rpow_mul hx]
  norm_num
  exact h

lemma le_rpow_three_quarter {x c : ℝ} (hx : 0 ≤ x) (_hc : 0 ≤ c) (h : c ^ 4 ≤ x ^ 3) :
    c ≤ x ^ ((3 : ℝ) / 4) := by
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (Real.rpow_nonneg hx _) ?_
  rw [rpow_pow_four hx, show (4 : ℝ) * ((3 : ℝ) / 4) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  exact h

/-! ### `exp (1/2)` -/

lemma exp_half_sq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
  rw [pow_two, ← Real.exp_add]; norm_num

lemma exp_half_le : Real.exp (1 / 2) ≤ 1.65 := by
  have h := Real.exp_one_lt_d9
  have hp := Real.exp_pos (1 / 2 : ℝ)
  have hs := exp_half_sq
  nlinarith

lemma exp_half_ge : (1 : ℝ) ≤ Real.exp (1 / 2) := Real.one_le_exp (by norm_num)

/-! ### the two upper constants -/

lemma zetaUpperC_le : zetaUpperC ≤ 34.65 := by
  have h := exp_half_le
  unfold zetaUpperC zetaStripA
  linarith

lemma zetaUpperC_ge : (21 : ℝ) ≤ zetaUpperC := by
  have h := exp_half_ge
  unfold zetaUpperC zetaStripA
  linarith

lemma zetaDerivUpperC_le : zetaDerivUpperC ≤ 97.35 := by
  have h := exp_half_le
  unfold zetaDerivUpperC zetaStripA
  linarith

lemma zetaDerivUpperC_ge : (59 : ℝ) ≤ zetaDerivUpperC := by
  have h := exp_half_ge
  unfold zetaDerivUpperC zetaStripA
  linarith

/-! ### `zetaInvBound2C` and its reciprocal -/

lemma two_zetaUpperC_nonneg : (0 : ℝ) ≤ 2 * zetaUpperC := by
  have := zetaUpperC_ge; linarith

lemma quarter_le_three : (2 * zetaUpperC) ^ ((1 : ℝ) / 4) ≤ 3 :=
  rpow_quarter_le two_zetaUpperC_nonneg (by norm_num) (by linarith [zetaUpperC_le])

lemma two_le_quarter : (2 : ℝ) ≤ (2 * zetaUpperC) ^ ((1 : ℝ) / 4) :=
  le_rpow_quarter two_zetaUpperC_nonneg (by norm_num) (by linarith [zetaUpperC_ge])

lemma three_quarter_le_two : (5 / 2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 :=
  rpow_three_quarter_le (by norm_num) (by norm_num) (by norm_num)

lemma one_le_three_quarter : (1 : ℝ) ≤ (5 / 2 : ℝ) ^ ((3 : ℝ) / 4) :=
  Real.one_le_rpow (by norm_num) (by norm_num)

lemma zetaInvBound2C_le : zetaInvBound2C ≤ 6 := by
  have h1 := quarter_le_three
  have h2 := three_quarter_le_two
  have h3 := two_le_quarter
  have h4 := one_le_three_quarter
  unfold zetaInvBound2C
  nlinarith

lemma zetaInvBound2C_ge : (2 : ℝ) ≤ zetaInvBound2C := by
  have h3 := two_le_quarter
  have h4 := one_le_three_quarter
  unfold zetaInvBound2C
  nlinarith

lemma zetaInvBound2C_pos' : 0 < zetaInvBound2C := by
  have := zetaInvBound2C_ge; linarith

lemma zetaInvBndC₁_ge : (1 : ℝ) / 6 ≤ zetaInvBndC₁ := by
  unfold zetaInvBndC₁
  rw [le_div_iff₀ zetaInvBound2C_pos']
  linarith [zetaInvBound2C_le]

lemma zetaInvBndC₁_le : zetaInvBndC₁ ≤ 1 := by
  unfold zetaInvBndC₁
  rw [div_le_one zetaInvBound2C_pos']
  linarith [zetaInvBound2C_ge]

/-- `zetaLowerBound3c` and `zetaInvBndC₁` are the same number. -/
lemma zetaLowerBound3c_eq : zetaLowerBound3c = zetaInvBndC₁ := by
  unfold zetaLowerBound3c zetaInvBndC₁ zetaInvBound2C
  ring

/-! ### `zetaInvBndA`: the `min` resolves, and the ratio is pinned -/

lemma zetaDerivUpperC_pos' : (0 : ℝ) < zetaDerivUpperC := by
  have := zetaDerivUpperC_ge; linarith

lemma zetaInvR_le : zetaInvBndC₁ / (zetaDerivUpperC * 2) ≤ 1 / 118 := by
  rw [div_le_div_iff₀ (by linarith [zetaDerivUpperC_pos']) (by norm_num)]
  linarith [zetaInvBndC₁_le, zetaDerivUpperC_ge]

lemma zetaInvR_ge : (1 : ℝ) / 1200 ≤ zetaInvBndC₁ / (zetaDerivUpperC * 2) := by
  rw [div_le_div_iff₀ (by norm_num) (by linarith [zetaDerivUpperC_pos'])]
  linarith [zetaInvBndC₁_ge, zetaDerivUpperC_le]

lemma zetaInvR_pos : (0 : ℝ) < zetaInvBndC₁ / (zetaDerivUpperC * 2) := by
  have := zetaInvR_ge; linarith

/-- The `min` in `zetaInvBndA` is attained by the second argument. -/
lemma zetaInvBndA_eq :
    zetaInvBndA = (1 / 2 : ℝ) * (zetaInvBndC₁ / (zetaDerivUpperC * 2)) ^ (4 : ℝ) := by
  unfold zetaInvBndA zetaStripA
  refine min_eq_right ?_
  have h1 : (zetaInvBndC₁ / (zetaDerivUpperC * 2)) ^ (4 : ℝ) ≤ 1 := by
    refine Real.rpow_le_one zetaInvR_pos.le ?_ (by norm_num)
    linarith [zetaInvR_le]
  linarith

lemma zetaInvBndA_ge : (1 / 10 : ℝ) ^ (13 : ℕ) ≤ zetaInvBndA := by
  rw [zetaInvBndA_eq, show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  have h := zetaInvR_ge
  have h0 := zetaInvR_pos
  have : ((1 : ℝ) / 1200) ^ (4 : ℕ) ≤ (zetaInvBndC₁ / (zetaDerivUpperC * 2)) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h 4
  nlinarith

/-! ### `zetaInvBndC`: the difference does not collapse -/

lemma half_three_quarter_ge : (7 : ℝ) / 12 ≤ (1 / 2 : ℝ) ^ ((3 : ℝ) / 4) :=
  le_rpow_three_quarter (by norm_num) (by norm_num) (by norm_num)

lemma zetaInvBnd_gap_ge :
    (8 : ℝ) * (1 / 10) ^ (12 : ℕ) ≤
      zetaInvBndC₁ * zetaInvBndA ^ (3 / 4 : ℝ) - zetaDerivUpperC * 2 * zetaInvBndA := by
  set r : ℝ := zetaInvBndC₁ / (zetaDerivUpperC * 2) with hr
  have hr0 : 0 < r := zetaInvR_pos
  have hrge : (1 : ℝ) / 1200 ≤ r := zetaInvR_ge
  have hnat : ∀ n : ℕ, r ^ ((n : ℕ) : ℝ) = r ^ n := fun n => Real.rpow_natCast r n
  have h4 : r ^ (4 : ℝ) = r ^ (4 : ℕ) := by
    rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num]; exact hnat 4
  -- the fractional power of `A` is exact
  have hApow : zetaInvBndA ^ (3 / 4 : ℝ) = (1 / 2 : ℝ) ^ ((3 : ℝ) / 4) * r ^ (3 : ℕ) := by
    rw [zetaInvBndA_eq, ← hr, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hr0.le _),
      ← Real.rpow_mul hr0.le, show ((4 : ℝ) * (3 / 4 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  -- `C₂ r = C₁ / 2`, which is what makes the difference a positive multiple of `r³`
  have hne : zetaDerivUpperC ≠ 0 := zetaDerivUpperC_pos'.ne'
  have hC₂r : zetaDerivUpperC * r = zetaInvBndC₁ / 2 := by
    rw [hr]; field_simp
  have hAv : zetaInvBndA = (1 / 2 : ℝ) * r ^ (3 : ℕ) * r := by
    rw [zetaInvBndA_eq, ← hr, h4]; ring
  have hgap : zetaInvBndC₁ * zetaInvBndA ^ (3 / 4 : ℝ) - zetaDerivUpperC * 2 * zetaInvBndA
      = r ^ (3 : ℕ) * zetaInvBndC₁ * ((1 / 2 : ℝ) ^ ((3 : ℝ) / 4) - 1 / 2) := by
    rw [hApow, hAv]
    have : zetaDerivUpperC * 2 * ((1 / 2 : ℝ) * r ^ (3 : ℕ) * r)
        = (zetaDerivUpperC * r) * r ^ (3 : ℕ) := by ring
    rw [this, hC₂r]
    ring
  rw [hgap]
  have hr3 : ((1 : ℝ) / 1200) ^ (3 : ℕ) ≤ r ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) hrge 3
  have hC1 : (1 : ℝ) / 6 ≤ zetaInvBndC₁ := zetaInvBndC₁_ge
  have hh := half_three_quarter_ge
  have hr3pos : (0 : ℝ) < r ^ (3 : ℕ) := pow_pos hr0 3
  have hA : ((1 : ℝ) / 1200) ^ (3 : ℕ) * (1 / 6) ≤ r ^ (3 : ℕ) * zetaInvBndC₁ :=
    mul_le_mul hr3 hC1 (by norm_num) hr3pos.le
  have hB : (1 : ℝ) / 12 ≤ (1 / 2 : ℝ) ^ ((3 : ℝ) / 4) - 1 / 2 := by linarith
  have hAB := mul_le_mul hA hB (by norm_num)
    (mul_nonneg hr3pos.le (by linarith : (0:ℝ) ≤ zetaInvBndC₁))
  have hnum : (8 : ℝ) * (1 / 10) ^ (12 : ℕ)
      ≤ ((1 : ℝ) / 1200) ^ (3 : ℕ) * (1 / 6) * (1 / 12) := by norm_num
  linarith

lemma zetaInvBndC_le : zetaInvBndC ≤ (10 : ℝ) ^ (12 : ℕ) := by
  unfold zetaInvBndC
  have h := zetaInvBnd_gap_ge
  have hpos : (0 : ℝ) <
      zetaInvBndC₁ * zetaInvBndA ^ (3 / 4 : ℝ) - zetaDerivUpperC * 2 * zetaInvBndA := by
    have : (0 : ℝ) < 8 * (1 / 10 : ℝ) ^ (12 : ℕ) := by norm_num
    linarith
  rw [inv_le_comm₀ hpos (by norm_num)]
  have : ((10 : ℝ) ^ (12 : ℕ))⁻¹ ≤ 8 * (1 / 10 : ℝ) ^ (12 : ℕ) := by norm_num
  linarith

/-! ### the two constants the rest of the chain reads off -/

lemma zetaInvBndC_pos' : 0 < zetaInvBndC := by
  unfold zetaInvBndC
  refine inv_pos.mpr ?_
  have h := zetaInvBnd_gap_ge
  have : (0 : ℝ) < 8 * (1 / 10 : ℝ) ^ (12 : ℕ) := by norm_num
  linarith

lemma zetaLogDerivA_eq : zetaLogDerivA = zetaInvBndA :=
  min_eq_left (le_trans zetaInvBndA_le (by unfold zetaStripA; norm_num))

lemma zetaLogDerivA_ge : (1 / 10 : ℝ) ^ (13 : ℕ) ≤ zetaLogDerivA := by
  rw [zetaLogDerivA_eq]; exact zetaInvBndA_ge

lemma zetaLogDerivC_le : zetaLogDerivC ≤ (10 : ℝ) ^ (14 : ℕ) := by
  unfold zetaLogDerivC
  have h1 := zetaInvBndC_le
  have h2 := zetaDerivUpperC_le
  have h3 := zetaInvBndC_pos'
  have h4 : (0 : ℝ) < zetaDerivUpperC := zetaDerivUpperC_pos'
  nlinarith

lemma zetaTrivC_le : zetaTrivC ≤ 6 := by
  have h : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  unfold zetaTrivC
  rw [h4]; linarith

lemma zetaLogDerivUnifC_le : zetaLogDerivUnifC ≤ (10 : ℝ) ^ (28 : ℕ) := by
  unfold zetaLogDerivUnifC
  have hA := zetaLogDerivA_ge
  have hA0 : (0 : ℝ) < zetaLogDerivA := zetaLogDerivA_mem.1
  have hinv : zetaLogDerivA⁻¹ ≤ (10 : ℝ) ^ (13 : ℕ) := by
    rw [inv_le_comm₀ hA0 (by norm_num)]
    have : ((10 : ℝ) ^ (13 : ℕ))⁻¹ = (1 / 10 : ℝ) ^ (13 : ℕ) := by norm_num
    linarith [this ▸ hA]
  have hnum : 1 + zetaLogDerivC + zetaTrivC ≤ 2 * (10 : ℝ) ^ (14 : ℕ) := by
    have := zetaLogDerivC_le
    have := zetaTrivC_le
    norm_num
    linarith
  have h0 : (0 : ℝ) ≤ 1 + zetaLogDerivC + zetaTrivC := by
    have h1 : (0 : ℝ) < zetaLogDerivC := by
      unfold zetaLogDerivC
      exact mul_pos zetaInvBndC_pos' zetaDerivUpperC_pos'
    have h2 : (0 : ℝ) ≤ zetaTrivC := zetaTrivC_nonneg
    linarith
  have hinv0 : (0 : ℝ) ≤ zetaLogDerivA⁻¹ := le_of_lt (inv_pos.mpr hA0)
  calc (1 + zetaLogDerivC + zetaTrivC) * zetaLogDerivA⁻¹
      ≤ (2 * (10 : ℝ) ^ (14 : ℕ)) * ((10 : ℝ) ^ (13 : ℕ)) := mul_le_mul hnum hinv hinv0 (by norm_num)
    _ ≤ (10 : ℝ) ^ (28 : ℕ) := by norm_num

/-! ### the strip width `zetaHolcLargeTA` -/

lemma one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  linarith [Real.exp_one_lt_d9]

lemma zetaLowerBndA_ge : (1 / 10 : ℝ) ^ (14 : ℕ) ≤ zetaLowerBndA := by
  unfold zetaLowerBndA
  refine le_min (by unfold zetaStripA; norm_num) ?_
  have hc : (1 : ℝ) / 6 ≤ zetaLowerBound3c := by
    rw [zetaLowerBound3c_eq]; exact zetaInvBndC₁_ge
  have hd : 4 * zetaDerivUpperC ≤ 4 * 97.35 := by linarith [zetaDerivUpperC_le]
  have hd0 : (0 : ℝ) < 4 * zetaDerivUpperC := by linarith [zetaDerivUpperC_pos']
  have hr : (1 : ℝ) / 2400 ≤ zetaLowerBound3c / (4 * zetaDerivUpperC) := by
    rw [div_le_div_iff₀ (by norm_num) hd0]
    linarith
  have := pow_le_pow_left₀ (show (0:ℝ) ≤ 1 / 2400 by norm_num) hr 4
  have hnum : (1 / 10 : ℝ) ^ (14 : ℕ) ≤ ((1 : ℝ) / 2400) ^ 4 := by norm_num
  linarith

lemma zetaHolcLargeTA_ge : (1 / 10 : ℝ) ^ (16 : ℕ) ≤ zetaHolcLargeTA := by
  unfold zetaHolcLargeTA zetaSmallTσ
  refine le_min (le_trans (by norm_num) zetaLowerBndA_ge) ?_
  have h1 : (1 : ℝ) ≤ Real.log 3 ^ 9 := one_le_pow₀ one_le_log_three
  have h2 : (1 : ℝ) - (1 - (1 / 10 : ℝ) ^ (16 : ℕ)) = (1 / 10 : ℝ) ^ (16 : ℕ) := by ring
  rw [h2]
  nlinarith [pow_pos (show (0:ℝ) < 1/10 by norm_num) 16]

end ZetaBoundsExplicit

/-! ## The `I`-bounds and the assembly (complements `MediumPNT`) -/

section MediumPNTExplicit

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)

open scoped Chebyshev

local notation "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

open ComplexConjugate

open MeasureTheory

/-- `SmoothedChebyshevClose` with its constant named: `6(3c₁ + c₂)` where `c₁ = log 2` and
`c₂ = 2 log 2` are pinned by `Smooth1Properties_below`/`_above`, i.e. `30 log 2 ≈ 20.79`. -/
theorem SmoothedChebyshevCloseExplicit {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ψ X‖ ≤ (30 * Real.log 2) * ε * X * Real.log X := by
  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ := Smooth1Properties_below suppSmoothingF mass_one

  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ := Smooth1Properties_above suppSmoothingF

  have c₁_lt : c₁ < 1 := by
    rw[c₁_eq]
    exact lt_trans (Real.log_two_lt_d9) (by norm_num)

  have c₂_lt : c₂ < 2 := by
    rw[c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    · rfl
    · exact lt_trans (Real.log_two_lt_d9) (by norm_num)
    · exact Real.log_nonneg (by norm_num)
    · positivity

  let C : ℝ := 6 * (3 * c₁ + c₂)
  have C_eq : C = 6 * (3 * c₁ + c₂) := rfl

  clear_value C

  have Cpos : 0 < C := by
    rw [C_eq]
    positivity

  have hCval : C = 30 * Real.log 2 := by rw [C_eq, c₁_eq, c₂_eq]; ring
  rw [← hCval]
  refine fun X X_ge_C ε εpos ε_lt_one ↦ ?_

  have X_gt_zero : (0 : ℝ) < X := by linarith

  have n_on_X_pos {n : ℕ} (npos : 0 < n) :
      0 < n / X := by
    have : (0 : ℝ) < n := by exact_mod_cast npos
    positivity

  have smooth1BddAbove (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≤ 1 :=
    Smooth1LeOne SmoothingFnonneg mass_one εpos (n_on_X_pos npos)

  have smooth1BddBelow (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≥ 0 :=
    Smooth1Nonneg SmoothingFnonneg (n_on_X_pos npos) εpos

  have smoothIs1 (n : ℕ) (npos : 0 < n) (n_le : n ≤ X * (1 - c₁ * ε)) :
      Smooth1 SmoothingF ε (↑n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) εpos (n_on_X_pos npos)
    exact (div_le_iff₀' X_gt_zero).mpr n_le

  have smoothIs0 (n : ℕ) (n_le : (1 + c₂ * ε) ≤ n / X) :=
    hc₂ (ε := ε) (n / X) ⟨εpos, ε_lt_one⟩ n_le

  have ε_pos: ε > 0 := by linarith
  have X_pos: X > 0 := by linarith
  have X_gt_three : 3 < X := by linarith

  intro X_bound

  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw[c₁_eq, ← div_le_iff₀]
    · have : 1 / Real.log 2 < 2 := by
        nth_rewrite 2 [← one_div_one_div 2]
        rw[one_div_lt_one_div]
        · exact lt_of_le_of_lt (by norm_num) (Real.log_two_gt_d9)
        · exact Real.log_pos (by norm_num)
        norm_num
      exact le_of_lt (gt_trans X_bound this)
    exact Real.log_pos (by norm_num)

  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    rw[c₂_eq, ← div_le_iff₀]
    · have : 1 / (2 * Real.log 2) < 2 := by
        nth_rewrite 3 [← one_div_one_div 2]
        · rw[one_div_lt_one_div, ← one_mul (1 / 2)]
          · apply mul_lt_mul
            · norm_num
            · apply le_of_lt
              exact lt_trans (by norm_num) (Real.log_two_gt_d9)
            repeat norm_num
          · norm_num
            exact Real.log_pos (by norm_num)
          · norm_num
      exact le_of_lt (gt_trans X_bound this)
    norm_num
    exact Real.log_pos (by norm_num)

  rw [SmoothedChebyshevDirichlet diffSmoothingF SmoothingFnonneg suppSmoothingF
    mass_one (by linarith) εpos ε_lt_one]

  convert SmoothedChebyshevClose_aux SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂ C C_eq ε
    ε_pos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2 smooth1BddAbove smooth1BddBelow
    smoothIs1 smoothIs0

/-- `(log X)^9 ≤ 48000·X` for `X ≥ 1`.  The sharp constant is `(9/e)^9 ≈ 47812`, attained at
`X = e^9`: writing `log X = 9 log (X^{1/9})` and using `log y ≤ y/e` gives it away. -/
lemma log_pow_nine_le {X : ℝ} (hX : 1 ≤ X) : Real.log X ^ 9 ≤ 48000 * X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  set y : ℝ := X ^ ((1 : ℝ) / 9) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hX0 _
  have hlogy : Real.log y ≤ y / Real.exp 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < y / Real.exp 1 by positivity)
    rw [Real.log_div hy0.ne' (Real.exp_ne_zero 1), Real.log_exp] at h
    linarith
  have hlogX : Real.log X = 9 * Real.log y := by
    rw [hy, Real.log_rpow hX0]; ring
  have hy9 : y ^ (9 : ℕ) = X := by
    rw [hy, ← Real.rpow_natCast (X ^ ((1 : ℝ) / 9)) 9, ← Real.rpow_mul hX0.le]
    norm_num
  have h1 : Real.log X ≤ 9 * (y / Real.exp 1) := by rw [hlogX]; linarith
  have h0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have hb : (9 : ℝ) / Real.exp 1 ≤ 3.311308 := by
    rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith [he]
  have hb0 : (0 : ℝ) ≤ 9 / Real.exp 1 := by positivity
  have hb9 : (9 / Real.exp 1) ^ 9 ≤ (3.311308 : ℝ) ^ 9 := pow_le_pow_left₀ hb0 hb 9
  have hnum : (3.311308 : ℝ) ^ 9 ≤ 48000 := by norm_num
  calc Real.log X ^ 9 ≤ (9 * (y / Real.exp 1)) ^ 9 := pow_le_pow_left₀ h0 h1 9
    _ = (9 / Real.exp 1) ^ 9 * y ^ (9 : ℕ) := by ring
    _ = (9 / Real.exp 1) ^ 9 * X := by rw [hy9]
    _ ≤ 48000 * X := by nlinarith [hb9, hnum, hX0]

/-- `IBound_aux1 3 _ 9` with its constant named. -/
lemma IBound_aux1_nine : ∀ X ≥ (3 : ℝ), Real.log X ^ 9 ≤ 48000 * X :=
  fun _ hX => log_pow_nine_le (by linarith)

/-- From a bound of the shape of `triv_bound_zeta`, `‖ζ'/ζ‖ ≤ 2(K'+1)·(σ-1)⁻¹` on the strip
`1 < σ < 2`.  This is `I1Bound`'s `G0`, pulled out so that an explicit `K'` can be supplied. -/
lemma logDeriv_zeta_le_strip_of {K' : ℝ} (K'_pos : 0 ≤ K')
    (K'_bounds_zeta : ∀ (σ₀ t : ℝ), 1 < σ₀ →
      ‖-ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ (σ₀ - 1)⁻¹ + K') :
    ∀ (t σ : ℝ), 1 < σ → σ < 2 →
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ (2 * (K' + 1)) * (σ - 1)⁻¹ := by
  intro t σ cond cond2

  have T0 : 0 < K' + 1 := by positivity
  have T1 : 1 ≤ (σ - 1)⁻¹ := by
    have U : σ - 1 ≤ 1 := by linarith
    have U1 := (inv_le_inv₀ (by positivity) (by exact sub_pos.mpr cond)).mpr U
    simp_all only [Complex.norm_div, norm_neg, tsub_le_iff_right, inv_one]

  have T : (K' + 1) * 1 ≤ (K' + 1) * (σ - 1)⁻¹ :=
    by
      exact (mul_le_mul_iff_right₀ T0).mpr T1
  have U := calc
    ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ = ‖-ζ' (σ + t * I) / ζ (σ + t * I)‖ := by
      rw [← norm_neg _, mul_comm, neg_div' _ _]
    _ ≤ (σ - 1)⁻¹ + K' := K'_bounds_zeta σ t cond
    _ ≤ (σ - 1)⁻¹ + (K' + 1) := by aesop
    _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) := by aesop
    _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) * (σ - 1)⁻¹ := by linarith
    _ = 2 * (K' + 1) * (σ - 1)⁻¹ := by
      ring_nf

  exact U

/-- `‖ζ'/ζ‖ ≤ 2(zetaTrivC + 1)·(σ-1)⁻¹ ≈ 12.77·(σ-1)⁻¹` on `1 < σ < 2`. -/
lemma logDeriv_zeta_le_strip :
    ∀ (t σ : ℝ), 1 < σ → σ < 2 →
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ (2 * (zetaTrivC + 1)) * (σ - 1)⁻¹ :=
  logDeriv_zeta_le_strip_of zetaTrivC_nonneg (fun σ₀ t h => zetaTrivC_bound σ₀ t h)

/-- The content of `I1Bound`, with the Mellin constant and the strip bound named. -/
theorem I1Bound_of
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    {M : ℝ} (M_is_pos : 0 < M)
    (M_bounds_mellin_hard : ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2)
      (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ M * (ε * ‖s‖ ^ 2)⁻¹)
    {K : ℝ} (K_is_pos : 0 < K)
    (K_bounds_zeta_at_any_t' : ∀ (t σ : ℝ), 1 < σ → σ < 2 →
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ K * (σ - 1)⁻¹) :
    ∀(ε : ℝ) (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₁ SmoothingF ε X T‖
      ≤ (|π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M)) * X * Real.log X / (ε * T) := by
  have C_final_pos : |π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M) > 0 := by
    positivity
  intro eps eps_pos eps_less_one X X_large T T_large

  let pts_re := 1 + (Real.log X)⁻¹
  let pts := fun (t : ℝ) ↦ (pts_re + t * I)

  have pts_re_triv : ∀(t : ℝ), (pts t).re = pts_re := by
    intro t
    unfold pts
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]

  have pts_re_ge_one : 1 < pts_re := by
    unfold pts_re
    simp only [lt_add_iff_pos_right, inv_pos]
    have U : 1 < X := by linarith
    exact Real.log_pos U

  have pts_re_le_one : pts_re < 2 := by
    unfold pts_re
    have Z : Real.log 3 < Real.log X :=
      by
        refine log_lt_log ?_ X_large
        simp only [Nat.ofNat_pos]

    have Z01 : 1 < Real.log 3 := logt_gt_one le_rfl
    have Zpos0 : 0 < Real.log 3 := by positivity
    have Zpos1 : 0 < Real.log X := by calc
      0 < Real.log 3 := Zpos0
      _ < Real.log X := Z

    have Z1 : (Real.log X)⁻¹ < (Real.log 3)⁻¹ := (inv_lt_inv₀ Zpos1 Zpos0).mpr Z

    have Z02 : (Real.log 3)⁻¹ < 1 := by
      have T01 := (inv_lt_inv₀ ?_ ?_).mpr Z01
      · simp only [inv_one] at T01
        exact T01
      · exact Zpos0
      simp only [zero_lt_one]

    have Z2 : 1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := by
      exact (add_lt_add_iff_left 1).mpr Z1

    have Z3 : 1 + (Real.log 3)⁻¹ < 2 := by
      calc
        1 + (Real.log 3)⁻¹ < 1 + 1 := by linarith
        _ = 2 := by ring_nf

    calc
      1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := Z2
      _ < 2 := Z3

  have inve : (pts_re - 1)⁻¹ = Real.log X := by
    unfold pts_re
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, add_sub_cancel_left, inv_inv]

  have K_bounds_zeta_at_any_t :
      ∀(t : ℝ), ‖ζ' (pts t) / ζ (pts t)‖ ≤ K * Real.log X := by
    intro t
    rw [←inve]
    exact K_bounds_zeta_at_any_t' t pts_re pts_re_ge_one pts_re_le_one

  have pts_re_pos : pts_re > 0 := by
    unfold pts_re
    positivity

  have triv_pts_lo_bound : ∀(t : ℝ), pts_re ≤ (pts t).re := by
    intro t
    unfold pts_re
    exact Eq.ge (pts_re_triv t)

  have triv_pts_up_bound : ∀(t : ℝ), (pts t).re ≤ 2 := by
    intro t
    unfold pts
    refine EReal.coe_le_coe_iff.mp ?_
    · simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, le_refl, implies_true, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero, EReal.coe_le_coe_iff]
      exact le_of_lt pts_re_le_one

  have pts_re_ge_1 : pts_re > 1 := by
    unfold pts_re
    exact pts_re_ge_one

  have X_pos_triv : 0 < X := by positivity

  let f := fun (t : ℝ) ↦ SmoothedChebyshevIntegrand SmoothingF eps X (pts t)

  /- Main pointwise bound -/

  have G : ∀(t : ℝ), ‖f t‖ ≤ (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by

    intro t

    let M_bounds_mellin_easy := fun (t : ℝ) ↦
      M_bounds_mellin_hard pts_re pts_re_pos (pts t) (triv_pts_lo_bound t) (triv_pts_up_bound t)
        eps eps_pos eps_less_one

    let zeta_part := (fun (t : ℝ) ↦ -ζ' (pts t) / ζ (pts t))
    let mellin_part := (fun (t : ℝ) ↦ 𝓜 (fun x ↦ (Smooth1 SmoothingF eps x : ℂ)) (pts t))
    let X_part := (fun (t : ℝ) ↦ (↑X : ℂ) ^ (pts t))

    let g := fun (t : ℝ) ↦ (zeta_part t) * (mellin_part t) * (X_part t)

    have X_part_eq : ∀(t : ℝ), ‖X_part t‖ = X^pts_re := by
      intro t
      have U := Complex.norm_cpow_eq_rpow_re_of_pos (X_pos_triv) (pts t)
      rw [pts_re_triv t] at U
      exact U

    have X_part_bound : ∀(t : ℝ), ‖X_part t‖ ≤ X^pts_re := by
      intro t
      rw [←X_part_eq]

    have mellin_bound : ∀(t : ℝ), ‖mellin_part t‖ ≤ M * (eps * ‖pts t‖ ^ 2)⁻¹ := by
      intro t
      exact M_bounds_mellin_easy t

    have X_part_and_mellin_bound :
        ∀(t : ℝ), ‖mellin_part t * X_part t‖ ≤ M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by
      intro t
      exact norm_mul_le_of_le (mellin_bound t) (X_part_bound t)

    have T2 : ∀(t : ℝ), ‖zeta_part t‖ = ‖ζ' (pts t) / ζ (pts t)‖ := by
      intro t
      unfold zeta_part
      simp only [Complex.norm_div, norm_neg]

    have zeta_bound : ∀(t : ℝ), ‖zeta_part t‖ ≤ K * Real.log X := by
      intro t
      unfold zeta_part
      rw [T2]
      exact K_bounds_zeta_at_any_t t

    have g_bound : ∀(t : ℝ), ‖zeta_part t * (mellin_part t * X_part t)‖ ≤
        (K * Real.log X) * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      intro t
      exact norm_mul_le_of_le (zeta_bound t) (X_part_and_mellin_bound t)

    have T1 : f = g := rfl

    have final_bound_pointwise :
        ‖f t‖ ≤ K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      rw [T1]
      unfold g
      rw [mul_assoc]
      exact g_bound t

    have trivialize :
        K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) =
          (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by ring_nf

    rw [trivialize] at final_bound_pointwise
    exact final_bound_pointwise

  have σ₀_gt : 1 < pts_re := pts_re_ge_1
  have σ₀_le_2 : pts_re ≤ 2 := by
    unfold pts_re
    exact
      Preorder.le_trans (1 + (Real.log X)⁻¹) (pts (SmoothingF (SmoothingF M))).re 2
        (triv_pts_lo_bound (SmoothingF (SmoothingF M)))
        (triv_pts_up_bound (SmoothingF (SmoothingF M)))

  have f_integrable := SmoothedChebyshevPull1_aux_integrable eps_pos eps_less_one X_large σ₀_gt
    σ₀_le_2 suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF

  have S : X^pts_re = rexp 1 * X := by
    unfold pts_re

    calc
      X ^ (1 + (Real.log X)⁻¹) = X * X ^ ((Real.log X)⁻¹) := by
        refine rpow_one_add' ?_ ?_
        · positivity
        · exact Ne.symm (ne_of_lt pts_re_pos)
      _ = X * rexp 1 := by
        refine (mul_right_inj' ?_).mpr ?_
        · exact Ne.symm (ne_of_lt X_pos_triv)
        · refine rpow_inv_log X_pos_triv ?_
          · by_contra h
            simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
              Complex.norm_div, Nat.not_ofNat_lt_one]
      _ = rexp 1 * X := by ring_nf

  have pts_re_neq_zero : pts_re ≠ 0 := by
    by_contra h
    rw [h] at pts_re_ge_1
    simp only [gt_iff_lt] at pts_re_ge_1
    norm_cast at pts_re_ge_1

  have Z :=
    by
      calc
        ‖∫ (t : ℝ) in Iic (-T), f t‖ ≤ ∫ (t : ℝ) in Iic (-T), ‖f t‖ := MeasureTheory.norm_integral_le_integral_norm f
        _ ≤ ∫ (t : ℝ) in Iic (-T), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re := by
            refine integral_mono ?_ ?_ (fun t ↦ G t)
            · refine Integrable.norm ?_
              · unfold f
                exact MeasureTheory.Integrable.restrict f_integrable
            · have equ : ∀(t : ℝ), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re = (K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹ := by
                   intro t; ring_nf
              have fun_equ : (fun (t : ℝ) ↦ ((K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re)) = (fun (t : ℝ) ↦ ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹)) := by
                   funext t
                   exact equ t

              rw [fun_equ]
              have simple_int : MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
                := by
                   unfold pts
                   exact poisson_kernel_integrable pts_re (pts_re_neq_zero)

              have U := MeasureTheory.Integrable.const_mul simple_int
                ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re)
              refine MeasureTheory.Integrable.restrict ?_
              exact U
        _ = (K * M) * Real.log X * X ^ pts_re * eps⁻¹ *
              ∫ (t : ℝ) in Iic (-T), (‖pts t‖ ^ 2)⁻¹ := by
              have simpli_fun :
                  (fun (t : ℝ) ↦ (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re) =
                    (fun (t : ℝ) ↦ ((K * M) * Real.log X * X ^ pts_re * eps⁻¹ * (‖pts t‖^2)⁻¹)) :=
                by funext t; ring_nf
              rw [simpli_fun]
              exact MeasureTheory.integral_const_mul ((K * M) * Real.log X * X ^ pts_re * eps⁻¹)
                (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
        _ ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * T⁻¹ := by
              have U := integral_evaluation (pts_re) T (T_large)
              unfold pts
              simp only [ge_iff_le]
              have U2 : 0 ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ := by
                simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
                  Complex.norm_div, le_refl, implies_true, inv_pos, mul_nonneg_iff_of_pos_right]
                refine Left.mul_nonneg ?_ ?_
                · refine Left.mul_nonneg ?_ ?_
                  · exact Left.mul_nonneg (by positivity) (by positivity)
                  · refine log_nonneg ?_
                    · linarith
                · refine Left.mul_nonneg ?_ ?_
                  · exact exp_nonneg 1
                  · exact le_of_lt X_pos_triv
              exact mul_le_mul_of_nonneg_left U U2
        _ = (Real.exp 1 * K * M) * Real.log X * X * eps⁻¹ * T⁻¹ := by
          rw [S]
          ring_nf
        _ = (Real.exp 1 * K * M) * X * Real.log X / (eps * T) := by ring_nf

  unfold I₁
  unfold f at Z
  unfold pts at Z
  have Z3 : (↑pts_re : ℂ) = 1 + (Real.log X)⁻¹ := by unfold pts_re; norm_cast
  rw [Z3] at Z
  rw [Complex.norm_mul (1 / (2 * ↑π * I)) _]
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ofReal_inv, ge_iff_le]
  have Z2 : 0 ≤ |π|⁻¹ * 2⁻¹ := by positivity
  simp only [ofReal_inv] at Z
  simp only [ge_iff_le]
  have Z4 := mul_le_mul_of_nonneg_left Z Z2
  ring_nf
  ring_nf at Z4
  exact Z4

/-- The content of `I2Bound`, with the Mellin constant `C₁` and the `log^9 ≤ C₃·X` constant
named. -/
lemma I2Bound_of {SmoothingF : ℝ → ℝ}
    {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound A C₂) (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2))
    {C₁ : ℝ} (C₁pos : 0 < C₁)
    (Mbd : ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2)
      (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ C₁ * (ε * ‖s‖ ^ 2)⁻¹)
    {C₃ : ℝ} (C₃_gt : C₃ ≥ 1) (hC₃ : ∀ X ≥ (3 : ℝ), Real.log X ^ 9 ≤ C₃ * X) :
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₂ SmoothingF ε T X σ₁‖
      ≤ (‖1/(2*π*I)‖ * (2 * (C₁ * C₂ * C₃ * rexp 1))) * X / (ε * T) := by
  set C' : ℝ := C₁ * C₂ * C₃ * rexp 1 with hC'
  have : C' > 0 := by positivity
  intro X X_gt ε ε_pos ε_lt_one T T_gt σ₁
  have Xpos : 0 < X := lt_trans (by simp only [Nat.ofNat_pos]) X_gt
  have Tpos : 0 < T := lt_trans (by norm_num) T_gt
  unfold I₂
  rw[norm_mul, mul_assoc (c := X), ← mul_div]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have interval_length_nonneg : σ₁ ≤ 1 + (Real.log X)⁻¹ := by
    dsimp[σ₁]
    rw[sub_le_iff_le_add]
    nth_rw 1 [← add_zero 1]
    rw[add_assoc]
    apply add_le_add_right
    refine Left.add_nonneg ?_ ?_
    · rw[inv_nonneg, log_nonneg_iff Xpos]
      exact le_trans (by norm_num) (le_of_lt X_gt)
    · refine div_nonneg ?_ ?_
      · exact A_in.1.le
      apply pow_nonneg
      rw[log_nonneg_iff Tpos]
      exact le_trans (by norm_num) (le_of_lt T_gt)
  have σ₁pos : 0 < σ₁ := by
    rw[sub_pos]
    calc
      A / Real.log T ^ 9 ≤ 1 / 2 / Real.log T ^ 9 := by
        refine div_le_div_of_nonneg_right (A_in.2) ?_
        apply pow_nonneg
        rw[log_nonneg_iff Tpos]
        exact le_trans (by norm_num) (le_of_lt T_gt)
      _ ≤ 1 / 2 / 1 := by
        refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
        exact one_le_pow₀ (logt_gt_one T_gt.le).le
      _ < 1 := by norm_num
  suffices ∀ σ ∈ Ioc σ₁ (1 + (Real.log X)⁻¹),
      ‖SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤ C' * X / (ε * T) by
    calc
      ‖∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
          SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤
          C' * X / (ε * T) * |1 + (Real.log X)⁻¹ - σ₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        convert this using 3
        apply uIoc_of_le
        exact interval_length_nonneg
      _ ≤ C' * X / (ε * T) * 2 := by
        apply mul_le_mul_of_nonneg_left
        · rw[abs_of_nonneg (sub_nonneg.mpr interval_length_nonneg)]
          calc
            1 + (Real.log X)⁻¹ - σ₁ ≤ 1 + (Real.log X)⁻¹ := by linarith
            _ ≤ 2 := (one_add_inv_log X_gt.le).le
        positivity
      _ = 2 * C' * X / (ε * T) := by ring
  -- Now bound the integrand
  intro σ hσ
  unfold SmoothedChebyshevIntegrand
  have log_deriv_zeta_bound : ‖ζ' (σ - T * I) / ζ (σ - T * I)‖ ≤ C₂ * (C₃ * T) := by
    calc
      ‖ζ' (σ - (T : ℝ) * I) / ζ (σ - (T : ℝ) * I)‖ = ‖ζ' (σ + (-T : ℝ) * I) / ζ (σ + (-T : ℝ) * I)‖ := by
        have Z : σ - (T : ℝ) * I = σ + (- T : ℝ) * I := by simp; ring_nf
        simp [Z]
      _ ≤ C₂ * Real.log |-T| ^ 9 := has_bound σ (-T)
          (by simp only [abs_neg]; rw [abs_of_pos Tpos]; exact T_gt)
          (by unfold σ₁ at hσ; simp only [mem_Ioc, abs_neg, log_abs, mem_Ici,
            tsub_le_iff_right] at hσ ⊢; replace hσ := hσ.1; linarith)
      _ ≤ C₂ * Real.log T ^ 9 := by simp
      _ ≤ C₂ * (C₃ * T) := by gcongr; exact hC₃ T (by linarith)

  -- Then estimate the remaining factors.
  calc
    ‖-ζ' (σ - T * I) / ζ (σ - T * I) * 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))
        (σ - T * I) * X ^ (σ - T * I)‖ =
        ‖-ζ' (σ - T * I) / ζ (σ - T * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))
        (σ - T * I)‖ * ‖(X : ℂ) ^ (σ - T * I)‖ := by
      repeat rw[norm_mul]
    _ ≤ C₂ * (C₃ * T) * (C₁ * (ε * ‖σ - T * I‖ ^ 2)⁻¹) * (rexp 1 * X) := by
      apply mul_le_mul₃
      · rw[neg_div, norm_neg]
        exact log_deriv_zeta_bound
      · refine Mbd σ₁ σ₁pos _ ?_ ?_ ε ε_pos ε_lt_one
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero, σ₁] at hσ ⊢
          linarith
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero, σ₁] at hσ ⊢
          linarith[one_add_inv_log X_gt.le]
      · rw[cpow_def_of_ne_zero]
        · rw[norm_exp,← ofReal_log, re_ofReal_mul]
          · simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
              sub_zero]
            rw [← le_log_iff_exp_le, Real.log_mul (exp_ne_zero 1), Real.log_exp, ← le_div_iff₀', add_comm, add_div, div_self, one_div]
            · exact hσ.2
            · refine (Real.log_pos ?_).ne.symm
              linarith
            · apply Real.log_pos
              linarith
            · linarith
            · positivity
          · positivity
        · exact_mod_cast Xpos.ne.symm
      · positivity
      · positivity
      · positivity
    _ = (C' * X * T) / (ε * ‖σ - T * I‖ ^ 2) := by ring
    _ ≤ C' * X / (ε * T) := by
      have : ‖σ - T * I‖ ^ 2 ≥ T ^ 2 := by
        calc
          ‖σ - T * I‖ ^ 2 = ‖σ + (-T : ℝ) * I‖ ^ 2 := by
            congr 2
            push_cast
            ring
          _ = normSq (σ + (-T : ℝ) * I) := (normSq_eq_norm_sq _).symm
          _ = σ^2 + (-T)^2 := by
            rw[Complex.normSq_add_mul_I]
          _ ≥ T^2 := by
            rw[neg_sq]
            exact le_add_of_nonneg_left (sq_nonneg _)
      calc
        C' * X * T / (ε * ‖↑σ - ↑T * I‖ ^ 2) ≤ C' * X * T / (ε * T ^ 2) := by
          rw[div_le_div_iff_of_pos_left, mul_le_mul_iff_right₀]
          · exact this
          · exact ε_pos
          · positivity
          · apply mul_pos ε_pos
            exact lt_of_lt_of_le (pow_pos Tpos 2) this
          · positivity
        _ = C' * X / (ε * T) := by
          field_simp

/-- The constant in `log_pow_over_xsq_integral_bounded`, from the integration-by-parts
recursion: `C₀ = 1` and `C_{d+1} = (log 3)^{d+1}/3 + (d+1)·C_d`.  At `n = 9`, which is the
only value used, this is `≈ 6.05·10⁵`. -/
noncomputable def logIntC : ℕ → ℝ
  | 0 => 1
  | (d + 1) => Real.log 3 ^ (d + 1) / 3 + ((d : ℝ) + 1) * logIntC d

lemma log_pow_over_xsq_integral_bounded_explicit :
  ∀ n : ℕ, 0 < logIntC n ∧ ∀ T >3, ∫ x in Ioo 3 T, (Real.log x)^n / x^2 < logIntC n := by
  have log3gt1: 1 < Real.log 3 := logt_gt_one le_rfl
  intro n
  induction n with
  | zero =>
    rw [show logIntC 0 = 1 from rfl]
    constructor
    · norm_num
    · intro T hT
      simp only [pow_zero]
      have h1 :(0 ≤ (-2) ∨ (-2) ≠ (-1) ∧ 0 ∉ Set.uIcc 3 T) := by
        right
        constructor
        · linarith
        · refine notMem_uIcc_of_lt ?_ ?_
          · exact three_pos
          · linarith
      have integral := integral_zpow h1
      ring_nf at integral

      have swap_int_kind : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), 1 / x ^ 2 = ∫ (x : ℝ) in Ioo 3 T, 1 / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo
      rw [← swap_int_kind]
      have change_int_power : ∫ (x : ℝ) in (3 : ℝ)..T, (1 : ℝ) / x ^ (↑ 2)
                            = ∫ (x : ℝ) in (3 : ℝ).. T, x ^ (-2 : ℤ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp
        rfl
      rw [change_int_power, integral]
      have : T ^ (-1 : ℤ) > 0 := by
        refine zpow_pos ?_ (-1)
        linarith
      linarith
  | succ d ih =>
    obtain ⟨Cdpos, IH⟩ := ih
    set Cd := logIntC d with hCd
    rw [show logIntC (d + 1) = Real.log 3 ^ (d + 1) / 3 + ((d : ℝ) + 1) * Cd from rfl]
    constructor
    · have logpowpos : (Real.log 3) ^ (d + 1) > 0 := by
        refine pow_pos ?_ (d + 1)
        linarith
      have : Real.log 3 ^ (d + 1) / 3 + (↑d + 1) * Cd > 0 / 3 + 0 := by
        have term2_pos : 0 < (↑d + 1) * Cd := by
          refine (mul_pos_iff_of_pos_right Cdpos).mpr ?_
          exact Nat.cast_add_one_pos d
        refine add_lt_add ?_ term2_pos
        refine div_lt_div₀ logpowpos ?_ ?_ ?_
        · linarith
        · linarith
        · linarith
      ring_nf at this
      ring_nf
      exact this
    · intro T Tgt3
      let u := fun x : ℝ ↦ (Real.log x) ^ (d + 1)
      let v := fun x : ℝ ↦ -1 / x
      let u' := fun x : ℝ ↦ (d + 1 : ℝ) * (Real.log x)^d / x
      let v' := fun x : ℝ ↦ 1 / x^2

      have swap_int_type : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) / x ^ 2
                          = ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ (d + 1) / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo

      rw [← swap_int_type]

      have uIcc_is_Icc : Set.uIcc 3 T = Set.Icc 3 T := by
        exact uIcc_of_lt Tgt3

      have cont_u : ContinuousOn u (Set.uIcc 3 T) := by
        unfold u
        rw[uIcc_is_Icc]
        refine ContinuousOn.pow ?_ (d + 1)
        refine continuousOn_of_forall_continuousAt ?_
        intro x hx
        refine continuousAt_log ?_
        linarith [hx.1]

      have cont_v : ContinuousOn v (Set.uIcc 3 T) := by
        unfold v
        rw[uIcc_is_Icc]
        refine continuousOn_of_forall_continuousAt ?_
        intro x hx
        have cont2 : ContinuousAt (fun (x : ℝ) ↦ 1 / x) (-x) := by
          refine ContinuousAt.div₀ ?_ (fun ⦃U⦄ a ↦ a) ?_
          · exact continuousAt_const
          · linarith [hx.1]
        have fun1 : (fun (x : ℝ) ↦ -1 / x) = (fun (x : ℝ) ↦ 1 / (-x)) := by
          ext x
          ring_nf
        rw [fun1]
        exact ContinuousAt.comp cont2 (HasDerivAt.neg (hasDerivAt_id x)).continuousAt

      have deriv_u :
          (∀ x ∈ Set.Ioo (3 ⊓ T) (3 ⊔ T), HasDerivAt u (u' x) x) := by
        intro x hx
        have min3t : min 3 T = 3 := by
          exact min_eq_left_of_lt Tgt3
        have max3t : max 3 T = T := by
          exact max_eq_right_of_lt Tgt3
        rw[min3t, max3t] at hx
        unfold u u'
        have xne0 : x ≠ 0 := by linarith [hx.1]
        have deriv2 := (Real.hasDerivAt_log xne0).pow (d + 1)
        have fun2 : (↑d + 1) * Real.log x ^ d / x =  (↑d + 1) * Real.log x ^ d * x⁻¹:= by
          exact rfl
        rw [fun2]
        convert! deriv2 using 1
        rw [Nat.add_sub_cancel,
          Nat.cast_add, Nat.cast_one]

      have deriv_v : (∀ x ∈ Set.Ioo (3 ⊓ T) (3 ⊔ T), HasDerivAt v (v' x) x) := by
        intro x hx
        have min3t : min 3 T = 3 := by
          exact min_eq_left_of_lt Tgt3
        have max3t : max 3 T = T := by
          exact max_eq_right_of_lt Tgt3
        rw[min3t, max3t] at hx
        have xne0 : x ≠ 0 := by linarith [hx.1]
        unfold v v'
        have deriv1 := hasDerivAt_inv xne0
        have fun1 : (fun (x : ℝ) ↦ x⁻¹) = (fun (x : ℝ) ↦ 1 / x) := by
          ext x
          exact inv_eq_one_div x
        rw [fun1] at deriv1
        have fun2 : -(x ^ 2)⁻¹ = - 1 / x ^ 2 := by
          field_simp
        rw [fun2] at deriv1
        convert! HasDerivAt.neg deriv1 using 1
        · ext x
          rw [neg_eq_neg_one_mul]
          field_simp
          simp
        · field_simp

      have cont_u' : ContinuousOn u' (Set.uIcc 3 T) := by
        rw[uIcc_is_Icc]
        unfold u'
        refine ContinuousOn.div₀ ?_ ?_ ?_
        · refine ContinuousOn.mul ?_ ?_
          · exact continuousOn_const
          · refine ContinuousOn.pow ?_ d
            refine continuousOn_of_forall_continuousAt ?_
            intro x hx
            refine continuousAt_log ?_
            linarith [hx.1]
        · exact continuousOn_id' (Icc 3 T)
        · intro x hx
          linarith [hx.1]

      have cont_v' : ContinuousOn v' (Set.uIcc 3 T) := by
        rw[uIcc_is_Icc]
        unfold v'
        refine ContinuousOn.div₀ ?_ ?_ ?_
        · exact continuousOn_const
        · exact continuousOn_pow 2
        · intro x hx
          refine pow_ne_zero 2 ?_
          linarith [hx.1]

      have int_u': IntervalIntegrable u' MeasureTheory.volume 3 T := by
        exact ContinuousOn.intervalIntegrable cont_u'

      have int_v': IntervalIntegrable v' MeasureTheory.volume 3 T := by
        exact ContinuousOn.intervalIntegrable cont_v'

      have IBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt cont_u cont_v deriv_u deriv_v int_u' int_v'

      unfold u u' v v' at IBP

      have int1 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) * (1 / x ^ 2)
                = ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) / x ^ 2 := by
          refine intervalIntegral.integral_congr ?_
          intro x hx
          field_simp

      rw[int1] at IBP
      rw[IBP]

      have int2 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), (↑d + 1) * Real.log x ^ d / x * (-1 / x)
                = -(↑d + 1) * ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ d / x ^ 2 := by
        have : ∀ x, (↑d + 1) * Real.log x ^ d / x * (-1 / x)
         = -((↑d + 1) * Real.log x ^ d / x ^ 2) := by
          intro x
          field_simp
        have : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), (↑d + 1) * Real.log x ^ d / x * (-1 / x)
                = ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), -((↑d + 1) * Real.log x ^ d / x ^ 2) := by
          exact intervalIntegral.integral_congr fun ⦃x⦄ a ↦ this x
        rw [this,
          ←intervalIntegral.integral_const_mul]

        ring_nf

      rw[int2]

      have int3 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ d / x ^ 2
                = ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo

      rw[int3]

      have IHbound : ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d / x ^ 2 < Cd := by
        exact IH T Tgt3

      ring_nf
      have bound2 : (Real.log T * Real.log T ^ d * T⁻¹) ≥ 0 := by
        have logTpos : Real.log T ≥ 0 := by
          refine log_nonneg ?_
          linarith
        apply mul_nonneg
        · apply mul_nonneg
          · exact logTpos
          · exact pow_nonneg logTpos d
        · field_simp
          simp
      let S := Real.log T * Real.log T ^ d * T⁻¹
      have : (-(Real.log T * Real.log T ^ d * T⁻¹) + Real.log 3 * Real.log 3 ^ d * (1 / 3) +
                ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2) +
              ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 = (-S + Real.log 3 * Real.log 3 ^ d * (1 / 3) +
                ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2) +
              ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 := by
        unfold S
        rfl
      rw [this]

      have GetRidOfS : (-S + Real.log 3 * Real.log 3 ^ d * (1 / 3)
                      + ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2)
                      + ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2
                      ≤ ( Real.log 3 * Real.log 3 ^ d * (1 / 3)
                      + ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2)
                      + ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 := by
        linarith
      apply lt_of_le_of_lt GetRidOfS
      rw [add_assoc]

      have bound4 : ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 < Cd := IHbound

      have bound5 : ↑d * ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 ≤ ↑d * Cd := by
        apply (mul_le_mul_of_nonneg_left bound4.le)
        exact Nat.cast_nonneg d

      rw[add_assoc]
      apply add_lt_add_right
      field_simp
      linarith

set_option maxHeartbeats 400000 in
-- Slow

lemma logIntC_succ (d : ℕ) :
    logIntC (d + 1) = Real.log 3 ^ (d + 1) / 3 + ((d : ℝ) + 1) * logIntC d := rfl

/-- **`logIntC 9 ≤ 10⁷`**, from `log 3 < 2`.  Crude: the true value is `≈ 6.05·10⁵`. -/
lemma logIntC_nine_le : logIntC 9 ≤ 10 ^ (7 : ℕ) := by
  have hL0 : (0 : ℝ) < Real.log 3 := by
    have := logt_gt_one (le_refl (3 : ℝ)); linarith
  have hL2 : Real.log 3 ≤ 2 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3) (by norm_num)
    linarith
  have step : ∀ (d : ℕ) (b : ℝ), logIntC d ≤ b →
      logIntC (d + 1) ≤ 2 ^ (d + 1) / 3 + ((d : ℝ) + 1) * b := by
    intro d b hb
    rw [logIntC_succ]
    have h1 : Real.log 3 ^ (d + 1) ≤ 2 ^ (d + 1) := pow_le_pow_left₀ hL0.le hL2 (d + 1)
    have h2 : ((d : ℝ) + 1) * logIntC d ≤ ((d : ℝ) + 1) * b :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    linarith
  have b0 : logIntC 0 ≤ 1 := le_of_eq rfl
  have b1 : logIntC 1 ≤ 2 := by have h := step 0 1 b0; norm_num at h; linarith
  have b2 : logIntC 2 ≤ 6 := by have h := step 1 2 b1; norm_num at h; linarith
  have b3 : logIntC 3 ≤ 21 := by have h := step 2 6 b2; norm_num at h; linarith
  have b4 : logIntC 4 ≤ 90 := by have h := step 3 21 b3; norm_num at h; linarith
  have b5 : logIntC 5 ≤ 461 := by have h := step 4 90 b4; norm_num at h; linarith
  have b6 : logIntC 6 ≤ 2788 := by have h := step 5 461 b5; norm_num at h; linarith
  have b7 : logIntC 7 ≤ 19559 := by have h := step 6 2788 b6; norm_num at h; linarith
  have b8 : logIntC 8 ≤ 156558 := by have h := step 7 19559 b7; norm_num at h; linarith
  have h := step 8 156558 b8; norm_num at h; linarith

/-- The content of `I3Bound`, with the Mellin constant named and the integral constant
replaced by its closed form `logIntC 9`. -/
theorem I3Bound_of {SmoothingF : ℝ → ℝ}
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2))
    {CM : ℝ} (CMpos : 0 < CM)
    (CMhyp : ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2)
      (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ CM * (ε * ‖s‖ ^ 2)⁻¹) :
      ∀ (X : ℝ) (_ : 3 < X)
        {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
        {T : ℝ} (_ : 3 < T),
        let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
        ‖I₃ SmoothingF ε T X σ₁‖
          ≤ (logIntC 9 * CM * Cζ) * X * X ^ (- A / (Real.log T ^ 9)) / ε := by
  obtain ⟨Cintpos, Cinthyp⟩ := log_pow_over_xsq_integral_bounded_explicit 9
  set Cint := logIntC 9 with hCint
  have : Cint * CM > 0 := mul_pos Cintpos CMpos
  have : Cint * CM * Cζ > 0 := mul_pos this Cζpos
  intro X Xgt3 ε εgt0 εlt1 T Tgt3 σ₁
  unfold I₃
  unfold SmoothedChebyshevIntegrand

  have Xpos := zero_lt_three.trans Xgt3
  have Tgt3' : -T < -3 := neg_lt_neg_iff.mpr Tgt3

  have t_bounds : ∀ t ∈ Ioo (-T) (-3), 3 < |t| ∧ |t| < T := by
    intro t ht
    have : |t| = -t := by
      refine abs_of_neg ?_
      exact ht.2.trans (by norm_num)
    rw [← Set.neg_mem_Ioo_iff, mem_Ioo] at ht
    rwa [this]

  have logt9gt1_bounds :
      ∀ t, t ∈ Set.Icc (-T) (-3) → Real.log |t| ^ 9 > 1 := by
    intro t ht
    refine one_lt_pow₀ (logt_gt_one ?_) ?_
    · have : |t| = -t := by
        refine abs_of_neg ?_
        exact ht.2.trans_lt (by norm_num)
      rw [this, le_neg]
      exact ht.2
    · norm_num

  have Aoverlogt9gtAoverlogT9_bounds : ∀ t, 3 < |t| ∧ |t| < T →
        A / Real.log |t| ^ 9 > A / Real.log T ^ 9 := by
    intro t ht
    have h9 : 9 ≠ 0 := by norm_num
    refine div_lt_div_of_pos_left hA.1 ?_ ?_
    · exact zero_lt_one.trans <| one_lt_pow₀ (logt_gt_one ht.1.le) h9
    · have h1 := log_lt_log (zero_lt_three.trans ht.1) ht.2
      have h2 := logt_gt_one ht.1.le
      have h3 : 0 ≤ Real.log |t| := zero_le_one.trans h2.le
      exact pow_lt_pow_left₀ h1 h3 h9

  have AoverlogT9in0half: A / Real.log T ^ 9 ∈ Ioo 0 (1/2) := by
    have logT9gt1 : 1 < Real.log T ^ 9 := by
      have logt_gt_one : 1 < Real.log T := logt_gt_one Tgt3.le
      refine (one_lt_pow_iff_of_nonneg ?_ ?_).mpr logt_gt_one
      · exact zero_le_one.trans logt_gt_one.le
      · norm_num
    have logT9pos := zero_lt_one.trans logT9gt1
    constructor
    · exact div_pos hA.1 logT9pos
    · rw [div_lt_comm₀ logT9pos one_half_pos, div_lt_iff₀' one_half_pos]
      apply hA.2.trans_lt
      rwa [lt_mul_iff_one_lt_right one_half_pos]

  have σ₁lt1 : σ₁ < 1 := by
    unfold σ₁
    linarith[AoverlogT9in0half.1]

  have σ₁pos : 0 < σ₁ := by
    unfold σ₁
    linarith[AoverlogT9in0half.2]

  have quotient_bound :
      ∀ t ∈ Ioo (-T) (-3), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2) ≤ Real.log |t| ^ 9 / t ^ 2 := by
    intro t ht
    have loght := logt9gt1_bounds t (Ioo_subset_Icc_self ht)
    have logpos : Real.log |t| ^ 9 > 0 := zero_lt_one.trans loght
    have denom_le : t ^ 2 ≤ σ₁ ^ 2 + t ^ 2 := (le_add_iff_nonneg_left _).mpr <| sq_nonneg σ₁
    have denom_pos : 0 < t ^ 2 := by
      apply sq_pos_of_ne_zero
      rintro rfl
      norm_num [mem_Ioo] at ht
    have denom2_pos : 0 < σ₁ ^ 2 + t ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) denom_pos
    exact (div_le_div_iff_of_pos_left logpos denom2_pos denom_pos).mpr denom_le

  have MellinBound : ∀ (t : ℝ),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ₁ + t * I)‖ ≤
        CM * (ε * ‖(σ₁ + t * I)‖ ^ 2)⁻¹ := by
    intro t
    refine CMhyp σ₁ σ₁pos _ ?_ ?_ _ εgt0 εlt1 <;> simp [σ₁lt1.le.trans one_le_two]

  have logzetabnd : ∀ t : ℝ, 3 < |t| ∧ |t| < T → ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ ≤ Cζ * Real.log (|t| : ℝ) ^ 9 := by
    intro t tbounds
    apply hCζ
    · exact tbounds.1
    · unfold σ₁
      rw [mem_Ici, sub_le_sub_iff_left]
      exact (Aoverlogt9gtAoverlogT9_bounds t tbounds).le

  let f t := (-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑X ^ (↑σ₁ + ↑t * I)

  let g t := Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * X ^ σ₁

  have bound_integral : ∀ t ∈ Ioo (-T) (-3), ‖f t‖ ≤ g t := by
    intro t ht
    unfold f

    have : ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ ≤ ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑(X : ℝ) : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
      simp [norm_neg]

    have : ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ ≤ (Cζ * Real.log |t| ^ 9) *
            (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁:= by
      have Xσ_bound : ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := by
        simp [norm_cpow_eq_rpow_re_of_pos Xpos]
      obtain ⟨ht_gt3, ht_ltT⟩ := t_bounds _ ht
      have logtgt1 : 1 < Real.log |t| := logt_gt_one ht_gt3.le
      have hζ := logzetabnd t ⟨ht_gt3, ht_ltT⟩
      have h𝓜 := MellinBound t
      rw[Xσ_bound]
      gcongr

    have : (Cζ * Real.log |t| ^ 9) * (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁ = g t := by
      unfold g
      ring_nf
    linarith

  have int_with_f :
      ∫ (t : ℝ) in (-T)..(-3),
        -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
          𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
          ↑X ^ (↑σ₁ + ↑t * I) =
      ∫ (t : ℝ) in (-T)..(-3), f t := by
    simp only [f]
  rw[int_with_f]

  apply (norm_mul_le _ _).trans
  rw [Complex.norm_mul, Complex.norm_I, one_mul]

  have : ‖1 / (2 * ↑π * I)‖ * ‖∫ (t : ℝ) in (-T)..(-3), f ↑t‖ ≤ ‖∫ (t : ℝ) in (-T)..(-3), f ↑t‖ := by
    apply mul_le_of_le_one_left
    · apply norm_nonneg
    · simp only [one_div, norm_inv]
      apply inv_le_one_of_one_le₀
      simp only [Complex.norm_mul, Complex.norm_ofNat, norm_real, norm_eq_abs, pi_nonneg,
        abs_of_nonneg, norm_I, mul_one]
      apply one_le_mul_of_one_le_of_one_le one_le_two
      exact le_trans (by norm_num) pi_gt_three.le
  apply le_trans this

  apply le_trans (intervalIntegral.norm_integral_le_integral_norm Tgt3'.le)

  have ne_zero_of_mem_uIcc (x) (hx : x ∈ uIcc (-T) (-3)) : x ≠ 0 := by
    rintro rfl
    norm_num [mem_uIcc] at hx
    linarith

  have cont1 : ContinuousOn (fun t ↦ Real.log |t| ^ 9) (uIcc (-T) (-3)) :=
    _root_.continuous_abs.continuousOn.log
      (fun x hx => abs_ne_zero.mpr <| ne_zero_of_mem_uIcc x hx) |>.pow 9

  have g_cont : ContinuousOn g (uIcc (-T) (-3)) := by
    unfold g
    refine .mul ?_ continuousOn_const
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_const.mul cont1
    · fun_prop
    · intro x hx
      apply mul_ne_zero εgt0.ne'
      have : 0 < σ₁ ^ 2 + x ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos σ₁pos) (sq_nonneg x)
      simp only [Complex.sq_norm, normSq_add_mul_I, ne_eq, this.ne', not_false_eq_true]

  have int_normf_le_int_g: ∫ (t : ℝ) in (-T)..(-3), ‖f ↑t‖
                        ≤ ∫ (t : ℝ) in (-T)..(-3), g ↑t := by
    by_cases h_int : IntervalIntegrable (fun t : ℝ ↦ ‖f t‖) volume (-T) (-3)
    · exact intervalIntegral.integral_mono_on_of_le_Ioo
        Tgt3'.le h_int g_cont.intervalIntegrable bound_integral
    · rw [intervalIntegral.integral_undef h_int]
      apply intervalIntegral.integral_nonneg Tgt3'.le
      intro t ht
      unfold g
      have := logt9gt1_bounds t ht
      positivity

  apply le_trans int_normf_le_int_g
  unfold g

  simp only [σ₁]

  have : X ^ (1 - A / Real.log T ^ 9) = X * X ^ (- A / Real.log T ^ 9) := by
    rw [sub_eq_add_neg, Real.rpow_add Xpos, Real.rpow_one, neg_div]

  rw[this]

  have Bound_of_log_int: ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) ≤ Cint / ε := by
    have : ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        = (1 / ε) * ∫ t in (-T)..(-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      congr with t
      field_simp [εgt0]
    rw[this]

    have bound : ∫ t in (-T)..(-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 ≤ Cint := by
      simp_rw [Complex.sq_norm, normSq_add_mul_I]

      have : ∫ t in (-T)..(-3), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)
            ≤ ∫ t in (-T)..(-3), Real.log |t| ^ 9 /  t ^ 2 := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo Tgt3'.le ?_ ?_ ?_
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Set.uIcc (-T) (-3)) := by
            refine ContinuousOn.div cont1 ?_ ?_
            · refine ContinuousOn.add ?_ ?_
              · exact continuousOn_const
              · refine ContinuousOn.pow ?_ 2
                exact continuousOn_id' _
            · intro t ht
              have h1 : 0 < t ^ 2 := pow_two_pos_of_ne_zero (ne_zero_of_mem_uIcc t ht)
              have h2 : 0 < σ₁ ^ 2 := sq_pos_of_pos σ₁pos
              exact (add_pos_of_pos_of_nonneg h2 h1.le).ne'
          apply cont.intervalIntegrable
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Set.uIcc (-T) (-3)) := by
            refine ContinuousOn.div cont1 ?_ ?_
            · refine ContinuousOn.pow ?_ 2
              exact continuousOn_id' _
            · intro t ht
              exact pow_ne_zero 2 (ne_zero_of_mem_uIcc t ht)
          apply cont.intervalIntegrable
        · intro x hx
          exact quotient_bound x hx
      apply le_trans this
      rw [← intervalIntegral.integral_comp_neg]
      simp only [abs_neg, log_abs, even_two, Even.neg_pow]
      rw [intervalIntegral.integral_of_le Tgt3.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact (Cinthyp T Tgt3).le
    rw [mul_comm,
      ← mul_div_assoc, mul_one]

    exact (div_le_div_iff_of_pos_right εgt0).mpr bound

  have factor_out_constants :
  ∫ (t : ℝ) in (-T)..(-3), Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * (X * X ^ (-A / Real.log T ^ 9))
  = Cζ * CM * (X * X ^ (-A / Real.log T ^ 9)) * ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) := by
     rw [mul_assoc, ← mul_assoc (Cζ * CM), ← mul_assoc]
     field_simp
     simp only [log_abs]
     rw [← intervalIntegral.integral_const_mul]
     apply intervalIntegral.integral_congr
     intro t ht
     ring_nf

  rw [factor_out_constants]

  have : Cζ * CM * (X * X ^ (-A / Real.log T ^ 9)) * ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        ≤ Cζ * CM * ((X : ℝ) * X ^ (-A / Real.log T ^ 9)) * (Cint / ε) := by
    apply mul_le_mul_of_nonneg_left
    · exact Bound_of_log_int
    · positivity

  apply le_trans this
  ring_nf
  field_simp
  simp

/-- The values of `‖ζ'/ζ‖` on the horizontal segment `I4Bound` integrates over: the points
`σ₂ + t(1-σ₂) - 3i` for `t ∈ [0,1]`, i.e. height `-3`, real part from `σ₂` up to `1`. -/
noncomputable def I4Seg (σ₂ : ℝ) : Set ℝ := (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1

/-- The `sInf` of `‖s‖²` over the same segment.  At least `9`, since `Im s = -3` there. -/
noncomputable def I4SegInf (σ₂ : ℝ) : NNReal := sInf ((fun t => ‖ σ₂ + (t : ℝ) * (1 - σ₂) - 3 * I ‖₊ ^ 2) '' Set.Icc 0 1)

/-- `I4Bound`'s constant, once the Mellin constant `D` is supplied. -/
noncomputable def I4C (σ₂ D : ℝ) : ℝ := sSup (I4Seg σ₂) * D / (I4SegInf σ₂ : ℝ)

/-- `I4Bound`'s lower bound on `T`. -/
noncomputable def I4Tlb (A σ₂ : ℝ) : ℝ := max 4 (max (rexp (A ^ (9 : ℝ)⁻¹)) (rexp ((A / (1 - σ₂)) ^ (9 : ℝ)⁻¹)))

/-- The content of `I4Bound`, with the Mellin constant named, so that the constant and the
threshold are closed forms rather than existential witnesses. -/
lemma I4Bound_of {SmoothingF : ℝ → ℝ}
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    {D : ℝ} (Dpos : 0 < D)
    (MellinSmooth1bBound : ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2)
      (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ D * (ε * ‖s‖ ^ 2)⁻¹) :
    0 ≤ I4C σ₂ D ∧ 3 < I4Tlb A σ₂ ∧
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : I4Tlb A σ₂ < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ I4C σ₂ D * X * X ^ (- A / (Real.log T ^ 9)) / ε := by
  unfold I4C I4Seg I4SegInf I4Tlb

  have reOne : re 1 = 1 := rfl
  have imOne : im 1 = 0 := rfl
  have reThree : re 3 = 3 := rfl
  have imThree : im 3 = 0 := rfl

  unfold I₄ SmoothedChebyshevIntegrand

  set S : Set ℝ := (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1 with hS
  set C' : ℝ := sSup S with hC'
  have bddAboveS : BddAbove S := by
    refine IsCompact.bddAbove ?_
    unfold S
    refine IsCompact.image_of_continuousOn ?_ ?_
    · exact isCompact_Icc
    · refine ContinuousOn.norm ?_
      have : (fun (t : ℝ) ↦ -ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        (fun (t : ℝ) ↦ -(ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := by
        apply funext
        intro x
        apply neg_div
      rw[this]
      refine ContinuousOn.neg ?_
      have : (fun (t : ℝ) ↦ ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        ((ζ' / ζ) ∘ (fun (t : ℝ) ↦ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := rfl
      rw[this]
      apply h_logDeriv_holo.continuousOn.comp' (by fun_prop)
      unfold MapsTo
      intro x xInIcc
      simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, Set.mem_sdiff, mem_singleton_iff]
      have : ¬↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I = 1 := by
        by_contra h
        rw[Complex.ext_iff, sub_re, add_re, sub_im, add_im] at h
        repeat rw[mul_im] at h
        repeat rw[mul_re] at h
        rw[sub_im, sub_re, reOne, imOne, reThree, imThree, I_im, I_re] at h
        repeat rw[ofReal_re] at h
        repeat rw[ofReal_im] at h
        ring_nf at h
        obtain ⟨_, ripGoal⟩ := h
        linarith
      refine ⟨?_, this⟩
      rw [mem_reProdIm]
      simp only [sub_re, add_re, ofReal_re, mul_re, one_re, ofReal_im, sub_im, one_im, sub_self,
        mul_zero, sub_zero, re_ofNat, I_re, im_ofNat, I_im, mul_one, add_im, mul_im, zero_mul,
        add_zero, zero_sub, mem_Icc, le_refl, neg_le_self_iff, Nat.ofNat_nonneg, and_self, and_true]
      rw [Set.uIcc_of_le]
      · rw [mem_Icc]
        constructor
        · simp only [le_add_iff_nonneg_right]
          apply mul_nonneg
          · exact xInIcc.1
          · linarith [hσ₂.2]
        · have : σ₂ + x * (1 - σ₂) = σ₂ * (1 - x) + x := by ring
          rw [this]
          clear this
          have : (2 : ℝ) = 1 * 1 + 1 := by norm_num
          rw [this]
          clear this
          gcongr
          · linarith [xInIcc.2]
          · exact hσ₂.2.le
          · linarith [xInIcc.1]
          · exact xInIcc.2
      · linarith [hσ₂.2]

  have CPrimeNonneg : 0 ≤ C' := by
    apply Real.sSup_nonneg
    intro x x_in_S
    obtain ⟨t, ht, rfl⟩ := x_in_S
    exact NNReal.coe_nonneg _

  set C : ℝ := C' * D / sInf ((fun t => ‖ σ₂ + (t : ℝ) * (1 - σ₂) - 3 * I ‖₊ ^ 2) '' Set.Icc 0 1) with hC
  have sInfPos : 0 < sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1) := by
    refine (IsCompact.lt_sInf_iff_of_continuous ?_ ?_ ?_ 0).mpr ?_
    · exact isCompact_Icc
    · exact Nonempty.of_subtype
    · have : (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) =
        (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ * ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) := by
        apply funext
        intro x
        rw[pow_two]
      rw[this]
      have : ContinuousOn (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) (Icc 0 1) := by
        refine ContinuousOn.nnnorm ?_
        refine ContinuousOn.sub ?_ (by exact continuousOn_const)
        refine ContinuousOn.add (by exact continuousOn_const) ?_
        exact ContinuousOn.mul (by exact Complex.continuous_ofReal.continuousOn) (by exact continuousOn_const)
      exact ContinuousOn.mul (by exact this) (by exact this)
    · intro x xLoc
      apply pow_pos
      have temp : |(↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I).im| ≤
        ‖↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I‖₊ := by apply Complex.abs_im_le_norm
      rw[sub_im, add_im, mul_im, mul_im, I_re, I_im, sub_im, sub_re] at temp
      repeat rw[ofReal_re] at temp
      repeat rw[ofReal_im] at temp
      rw[reThree, imOne] at temp
      ring_nf at temp ⊢
      rw[(by ring : σ₂ - σ₂ * x + x - I * 3 = σ₂ - σ₂ * x + (x - I * 3))] at temp ⊢
      rw[abs_of_neg, neg_neg] at temp
      · have : (3 : NNReal) ≤ ‖↑σ₂ - ↑σ₂ * ↑x + (↑x - I * 3)‖₊ := temp
        positivity
      · rw[neg_lt_zero]
        norm_num
  have CNonneg : 0 ≤ C := by
    unfold C
    apply mul_nonneg
    · exact mul_nonneg (by exact CPrimeNonneg) (by exact Dpos.le)
    · rw[inv_nonneg]
      norm_cast
      convert sInfPos.le using 5
      norm_cast

  set Tlb : ℝ := max 4 (max (rexp (A ^ (9 : ℝ)⁻¹)) (rexp ((A / (1 - σ₂)) ^ (9 : ℝ)⁻¹))) with hTlb

  have hTlb3 : 3 < Tlb := by
    unfold Tlb
    rw[lt_max_iff]
    refine Or.inl ?_
    norm_num
  refine ⟨CNonneg, hTlb3, ?_⟩

  intro X X_gt_three ε ε_pos ε_lt_one T T_gt_Tlb σ₁
  have σ₂_le_σ₁ : σ₂ ≤ σ₁ := by
    have logTlb_pos : 0 < Real.log Tlb := by
      rw[← Real.log_one]
      exact log_lt_log (by norm_num) (by linarith)
    have logTlb_nonneg : 0 ≤ Real.log Tlb := le_of_lt (by exact logTlb_pos)
    have expr_nonneg : 0 ≤ A / (1 - σ₂) := by
      apply div_nonneg
      · linarith [hA.1]
      · rw[sub_nonneg]
        exact le_of_lt hσ₂.2
    have temp : σ₂ ≤ 1 - A / Real.log Tlb ^ 9 := by
      have : rexp ((A / (1 - σ₂)) ^ (9 : ℝ)⁻¹) ≤ Tlb := by
        unfold Tlb
        nth_rewrite 2 [max_comm]
        rw[max_left_comm]
        apply le_max_of_le_left (by rfl)
      rw[← Real.le_log_iff_exp_le] at this
      · have h1 : 0 ≤ (A / (1 - σ₂)) ^ (9 : ℝ)⁻¹ := by apply Real.rpow_nonneg (by exact expr_nonneg)
        have h2 : 0 < (9 : ℝ) := Nat.ofNat_pos'
        rw[← Real.rpow_le_rpow_iff h1 logTlb_nonneg h2] at this
        have h: ((A / (1 - σ₂)) ^ (9 : ℝ)⁻¹) ^ (9 : ℝ) = A / (1 - σ₂) := rpow_inv_rpow (by exact expr_nonneg) (by exact Ne.symm (OfNat.zero_ne_ofNat 9))
        rw[h, div_le_iff₀, mul_comm, ← div_le_iff₀] at this
        · have temp : Real.log Tlb ^ (9 : ℕ) = Real.log Tlb ^ (9 : ℝ) := Eq.symm (rpow_ofNat (Real.log Tlb) 9)
          rw[temp]
          linarith
        · exact rpow_pos_of_pos (by exact logTlb_pos) 9
        · rw[sub_pos]
          exact hσ₂.2
      · positivity
    have : 1 - A / Real.log Tlb ^ 9 ≤ 1 - A / Real.log T ^ 9 := by
      apply sub_le_sub (by rfl)
      apply div_le_div₀
      · exact le_of_lt (by exact hA.1)
      · rfl
      · apply pow_pos (by exact logTlb_pos)
      · apply pow_le_pow_left₀ (by exact logTlb_nonneg)
        apply log_le_log (by positivity)
        exact le_of_lt (by exact T_gt_Tlb)
    exact le_trans temp this
  have minσ₂σ₁ : min σ₂ σ₁ = σ₂ := min_eq_left (by exact σ₂_le_σ₁)
  have maxσ₂σ₁ : max σ₂ σ₁ = σ₁ := max_eq_right (by exact σ₂_le_σ₁)
  have σ₁_lt_one : σ₁ < 1 := by
    rw[← sub_zero 1]
    unfold σ₁
    apply sub_lt_sub_left
    apply div_pos (by exact hA.1)
    apply pow_pos
    rw[← Real.log_one]
    exact log_lt_log (by norm_num) (by linarith)

  rw[norm_mul, ← one_mul C]
  have : 1 * C * X * X ^ (-A / Real.log T ^ 9) / ε = 1 * (C * X * X ^ (-A / Real.log T ^ 9) / ε) := by ring
  rw[this]
  apply mul_le_mul
  · rw[norm_div, norm_one]
    repeat rw[norm_mul]
    rw[Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg pi_nonneg, Complex.norm_I, mul_one]
    have : 1 / (2 * π) < 1 / 6 := by
      rw[one_div_lt_one_div]
      · refine (div_lt_iff₀' ?_).mp ?_
        · norm_num
        ring_nf
        refine gt_iff_lt.mpr ?_
        exact Real.pi_gt_three
      · positivity
      · norm_num
    exact le_of_lt (lt_trans this (by norm_num))
  · let f : ℝ → ℂ := fun σ ↦ (-ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I))
    have temp : ‖∫ (σ : ℝ) in σ₂..σ₁, -ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I)‖ ≤
      C * X * X ^ (-A / Real.log T ^ 9) / ε * |σ₁ - σ₂| := by
      have : ∀ x ∈ Set.uIoc σ₂ σ₁, ‖f x‖ ≤ C * X * X ^ (-A / Real.log T ^ 9) / ε := by
        intro x xInIoc
        let t : ℝ := (x - σ₂) / (1 - σ₂)
        have tInIcc : t ∈ Icc 0 1 := by
          unfold t
          constructor
          · apply div_nonneg
            · rw[sub_nonneg]
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact le_of_lt (by exact xInIoc.1)
            · rw[sub_nonneg]
              apply le_of_lt (by exact hσ₂.2)
          · rw[div_le_one]
            · refine sub_le_sub ?_ (by rfl)
              unfold uIoc at xInIoc
              rw[maxσ₂σ₁] at xInIoc
              apply le_trans xInIoc.2
              exact le_of_lt (by exact σ₁_lt_one)
            · rw[sub_pos]
              exact hσ₂.2
        have tExpr : (↑σ₂ + t * (1 - ↑σ₂) - 3 * I) = (↑x - 3 * I) := by
          unfold t
          simp only [ofReal_div, ofReal_sub, ofReal_one, sub_left_inj]
          rw[div_mul_comm, div_self]
          · simp only [one_mul, add_sub_cancel]
          · refine sub_ne_zero_of_ne ?_
            apply Ne.symm
            rw[Complex.ofReal_ne_one]
            exact ne_of_lt (by exact hσ₂.2)
        unfold f
        simp only [Complex.norm_mul]
        have : C * X * X ^ (-A / Real.log T ^ 9) / ε =
          (C / ε) * (X * X ^ (-A / Real.log T ^ 9)) := by ring
        rw[this]
        have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)‖ ≤
          C / ε := by
          unfold C
          rw[div_div]
          nth_rewrite 2 [div_eq_mul_inv]
          have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ≤ C' := by
            unfold C'
            have : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ∈
              (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1 := by
              rw[Set.mem_image]
              use t
              constructor
              · exact tInIcc
              · rw[tExpr]
                rfl
            exact le_csSup (by exact bddAboveS) (by exact this)
          have : ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)‖ ≤
            D * ((sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)) * ε)⁻¹ := by
            nth_rewrite 3 [mul_comm]
            let s : ℂ := x - 3 * I
            have : 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I) =
              𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s := rfl
            rw[this]
            have temp : σ₂ ≤ s.re := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              apply le_of_lt
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact xInIoc.1
            have : s.re ≤ 2 := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              have : x < 1 := by
                unfold uIoc at xInIoc
                rw[maxσ₂σ₁] at xInIoc
                exact lt_of_le_of_lt xInIoc.2 σ₁_lt_one
              linarith
            have temp : ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ D * (ε * ‖s‖ ^ 2)⁻¹ := by
              exact MellinSmooth1bBound σ₂ hσ₂.1 s temp this ε ε_pos ε_lt_one
            have : D * (ε * ‖s‖ ^ 2)⁻¹ ≤ D * (ε * ↑(sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)))⁻¹ := by
              refine mul_le_mul (by rfl) ?_ ?_ (by exact le_of_lt (by exact Dpos))
              · rw[inv_le_inv₀]
                · apply mul_le_mul (by rfl)
                  · rw[NNReal.coe_sInf]
                    apply csInf_le
                    · apply NNReal.bddBelow_coe
                    · unfold s
                      rw[Set.mem_image]
                      let xNorm : NNReal := ‖x - 3 * I‖₊ ^ 2
                      use xNorm
                      constructor
                      · rw[Set.mem_image]
                        use t
                        exact ⟨tInIcc, by rw[tExpr]⟩
                      · rfl
                  · exact le_of_lt (by exact sInfPos)
                  · exact le_of_lt (by exact ε_pos)
                · apply mul_pos (ε_pos)
                  refine sq_pos_of_pos ?_
                  refine norm_pos_iff.mpr ?_
                  refine ne_zero_of_re_pos ?_
                  unfold s
                  rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
                  ring_nf
                  unfold uIoc at xInIoc
                  rw[minσ₂σ₁] at xInIoc
                  exact lt_trans hσ₂.1 xInIoc.1
                · exact mul_pos (ε_pos) (sInfPos)
              · rw[inv_nonneg]
                apply mul_nonneg (by exact le_of_lt (by exact ε_pos))
                exact sq_nonneg ‖s‖
            exact le_trans temp this
          rw[mul_assoc]
          apply mul_le_mul (by exact temp) (by exact this)
          · have this : 0 ≤ |(𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)).re| := by
              apply abs_nonneg
            exact le_trans this (by refine Complex.abs_re_le_norm ?_)
          · exact CPrimeNonneg
        have : ‖(X : ℂ) ^ (↑x - 3 * I)‖ ≤
          X * X ^ (-A / Real.log T ^ 9) := by
          nth_rewrite 2 [← Real.rpow_one X]
          rw[← Real.rpow_add]
          · rw[Complex.norm_cpow_of_ne_zero]
            · rw[sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, reThree, imThree]
              ring_nf
              rw[Complex.norm_of_nonneg]
              · rw[Complex.arg_ofReal_of_nonneg]
                · rw[zero_mul, neg_zero, Real.exp_zero]
                  simp only [inv_one, mul_one, inv_pow]
                  refine rpow_le_rpow_of_exponent_le ?_ ?_
                  · linarith
                  · unfold uIoc at xInIoc
                    rw[maxσ₂σ₁] at xInIoc
                    unfold σ₁ at xInIoc
                    ring_nf at xInIoc ⊢
                    exact xInIoc.2
                · positivity
              · positivity
            · refine ne_zero_of_re_pos ?_
              rw[ofReal_re]
              positivity
          · positivity
        apply mul_le_mul
        · exact temp
        · exact this
        · rw[Complex.norm_cpow_eq_rpow_re_of_pos]
          · rw[sub_re, mul_re, ofReal_re, I_re, I_im, reThree, imThree]
            ring_nf
            apply Real.rpow_nonneg
            positivity
          · positivity
        · exact div_nonneg CNonneg (le_of_lt ε_pos)
      exact intervalIntegral.norm_integral_le_of_norm_le_const this
    have : C * X * X ^ (-A / Real.log T ^ 9) / ε * |σ₁ - σ₂| ≤
      C * X * X ^ (-A / Real.log T ^ 9) / ε := by
      have : |σ₁ - σ₂| ≤ 1 := by
        rw[abs_of_nonneg]
        · rw[← sub_zero 1]
          exact sub_le_sub σ₁_lt_one.le hσ₂.1.le
        · rw[sub_nonneg]
          exact σ₂_le_σ₁
      bound
    exact le_trans temp this
  · simp only [norm_nonneg]
  norm_num

/-- The content of `I5Bound`, abstracted over the two bounds it obtains existentially: the
sup of `‖ζ'/ζ‖` on the segment `{σ₂} × [-3,3]`, and the Mellin bound.  Naming them lets a
caller with numerals for both read off the constant. -/
lemma I5Bound_of {SmoothingF : ℝ → ℝ}
    {σ₂ : ℝ} (hσ₂ : σ₂ ∈ Ioo 0 1)
    {zeta_bound : ℝ}
    (zeta_prop : ∀ s ∈ ({σ₂} ×ℂ uIcc (-3 : ℝ) 3), ‖ζ' s / ζ s‖ ≤ zeta_bound)
    {M : ℝ} (M_is_pos : 0 < M)
    (M_bounds_mellin_hard : ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2)
      (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ M * (ε * ‖s‖ ^ 2)⁻¹) :
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1),
    ‖I₅ SmoothingF ε X σ₂‖
      ≤ (|π|⁻¹ * 2⁻¹ * 6 * (1 + (σ₂ ^ 2)⁻¹ * |zeta_bound| * M)) * X ^ σ₂ / ε := by
  unfold I₅
  unfold SmoothedChebyshevIntegrand

  let mellin_prop : ∀ (t ε : ℝ),
  0 < ε → ε < 1 → ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ ≤ M * (ε * ‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹  :=
    fun (t : ℝ) ↦ (M_bounds_mellin_hard σ₂ (by linarith[hσ₂.1]) (σ₂ + t * I) (by simp only [add_re,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, le_refl]) (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith[hσ₂.2]))

  simp only [mul_inv_rev] at mellin_prop

  set Const := 1 + (σ₂ ^ 2)⁻¹ * |zeta_bound| * M

  set C := |π|⁻¹ * 2⁻¹ * 6 * Const

  intros X X_gt ε ε_pos ε_lt_one

  have mellin_bound := fun (t : ℝ) ↦ mellin_prop t ε ε_pos ε_lt_one

  have U: 0 < σ₂^2 := by
    exact sq_pos_of_pos (by linarith[hσ₂.1])

  have easy_bound : ∀(t : ℝ), (‖↑σ₂ + ↑t * I‖^2)⁻¹ ≤ (σ₂^2)⁻¹ :=
    by
      intro t
      rw [inv_le_inv₀]
      · rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, add_im, mul_im, zero_add]
        ring_nf
        simp only [le_add_iff_nonneg_right]
        exact zpow_two_nonneg t
      · rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, add_im, mul_im, zero_add]
        ring_nf
        positivity
      positivity

  have T1 : ∀(t : ℝ), t ∈ uIoc (-3) (3 : ℝ) → ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I) *
          (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ ≤ Const * ε⁻¹ * X ^ σ₂ := by
    intro t hyp_t
    have Z := by
      calc
        ‖(-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)) * (𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)) *
        (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ = ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by simp only [Complex.norm_mul,
          Complex.norm_div, norm_neg]
        _ ≤ ‖ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ := by simp only [Complex.norm_div,
          norm_neg, le_refl]
        _ ≤ zeta_bound *  ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  :=
          by
            have U := zeta_prop (↑σ₂ + t * I) (by
                simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
                simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
                  mul_one, sub_self, add_zero, mem_singleton_iff, add_im, mul_im, zero_add, mem_Icc]
                constructor
                · trivial
                · refine mem_Icc.mp ?_
                  · refine mem_Icc_of_Ioc ?_
                    · have T : (-3 : ℝ) ≤ 3 := by simp only [neg_le_self_iff, Nat.ofNat_nonneg]
                      rw [←Set.uIoc_of_le T]
                      exact hyp_t)
            simp only [Complex.norm_div] at U
            simp only [Complex.norm_div, ge_iff_le]
            linear_combination U * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U : zeta_bound ≤ abs zeta_bound := by simp only [le_abs_self]
          linear_combination (U * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  )
        _ ≤ abs zeta_bound * M * ((‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹ * ε⁻¹) * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U := mellin_bound t
          linear_combination (abs zeta_bound) * U * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          linear_combination (abs zeta_bound * M * easy_bound t * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖)
        _ = abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * X ^ (σ₂) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos]
          · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero]
          positivity
        _ ≤ Const * ε⁻¹ * X ^ σ₂ := by
          unfold Const
          ring_nf
          simp only [inv_pow, le_add_iff_nonneg_right, inv_pos, mul_nonneg_iff_of_pos_left, ε_pos]
          positivity

    exact Z

  -- Now want to apply the triangle inequality
  -- and bound everything trivially
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ge_iff_le]
  have Z :=
    intervalIntegral.norm_integral_le_of_norm_le_const T1
  simp only [ge_iff_le]

  have S : |π|⁻¹ * 2⁻¹ * (Const * ε⁻¹ * X ^ σ₂ * |3 + 3|) = C * X ^ σ₂ / ε := by
    unfold C
    ring_nf

  simp only [sub_neg_eq_add] at Z
  simp only [← S, ge_iff_le]
  linear_combination (|π|⁻¹ * 2⁻¹ * Z)

/-- `I5Bound`'s constant at the explicit inputs, as a closed form: `σ₂ = 1 - 10⁻¹⁶`, the segment
bound `3·10³²` from `logDeriv_zeta_le_smallT`, and the bump's Mellin constant.  About
`5.4·10³⁴`; `I5const_le` rounds it to `10³⁶`. -/
noncomputable def I5const : ℝ :=
  |π|⁻¹ * 2⁻¹ * 6 * (1 + (zetaSmallTσ ^ 2)⁻¹ * |(3 : ℝ) * 10 ^ (32 : ℕ)| *
    (27 * bumpC / 4 * 2 ^ (2 : ℝ) * (3 / 2)))

/-- `I5Bound` at the explicit inputs, against the closed-form constant `I5const`. -/
lemma I5BoundNamed :
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1),
    ‖I₅ bumpNu ε X zetaSmallTσ‖ ≤ I5const * X ^ zetaSmallTσ / ε := by
  have hσ0 : (0 : ℝ) < zetaSmallTσ := by unfold zetaSmallTσ; norm_num
  have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num]
    rw [Real.rpow_natCast]
    norm_num
  have hMval : 27 * bumpC / 4 * 2 ^ (2 : ℝ) * (3 / 2) = 81 * bumpC / 2 := by
    rw [h4]; ring
  have hM0 : (0 : ℝ) < 27 * bumpC / 4 * 2 ^ (2 : ℝ) * (3 / 2) := by
    rw [hMval]; linarith [bumpC_pos]
  -- the segment bound
  have hseg : ∀ s ∈ ({zetaSmallTσ} ×ℂ uIcc (-3 : ℝ) 3), ‖ζ' s / ζ s‖ ≤ 3 * 10 ^ (32 : ℕ) := by
    intro s hs
    simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, mem_reProdIm, mem_singleton_iff,
      mem_Icc] at hs
    have hs' : s = (zetaSmallTσ : ℂ) + (s.im : ℝ) * I := by
      apply Complex.ext <;> simp [hs.1]
    rw [hs']
    exact logDeriv_zeta_le_smallT (abs_le.mpr hs.2)
  exact I5Bound_of (SmoothingF := bumpNu) ⟨hσ0, zetaSmallTσ_lt_one⟩ hseg hM0
    (MellinOfSmooth1bExplicit bumpNu_contDiff bumpNu_support (fun _ hx => bumpNu_deriv_le hx))

/-- `I5const ≤ 10³⁶`. -/
lemma I5const_le : I5const ≤ 10 ^ (36 : ℕ) := by
  have hσ0 : (0 : ℝ) < zetaSmallTσ := by unfold zetaSmallTσ; norm_num
  have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num]
    rw [Real.rpow_natCast]
    norm_num
  have hMval : 27 * bumpC / 4 * 2 ^ (2 : ℝ) * (3 / 2) = 81 * bumpC / 2 := by
    rw [h4]; ring
  have hM0 : (0 : ℝ) < 27 * bumpC / 4 * 2 ^ (2 : ℝ) * (3 / 2) := by
    rw [hMval]; linarith [bumpC_pos]
  have hpi : |π|⁻¹ * 2⁻¹ * 6 ≤ 1 := by
    rw [abs_of_pos Real.pi_pos]
    have : π⁻¹ ≤ 1 / 3 := by
      rw [inv_le_comm₀ Real.pi_pos (by norm_num)]
      linarith [Real.pi_gt_three]
    linarith
  have hσsq : (zetaSmallTσ ^ 2)⁻¹ ≤ 2 := by
    have h1 : (3 : ℝ) / 4 ≤ zetaSmallTσ := by unfold zetaSmallTσ; norm_num
    have h2 : (1 : ℝ) / 2 ≤ zetaSmallTσ ^ 2 := by nlinarith
    rw [inv_le_comm₀ (pow_pos hσ0 2) (by norm_num)]
    linarith
  have habs : |(3 : ℝ) * 10 ^ (32 : ℕ)| = 3 * 10 ^ (32 : ℕ) := abs_of_pos (by norm_num)
  have hbump : 27 * bumpC / 4 * 2 ^ (2 : ℝ) * (3 / 2) ≤ 405 / 2 := by
    rw [hMval]; linarith [bumpC_le]
  have hprod : (zetaSmallTσ ^ 2)⁻¹ * |(3 : ℝ) * 10 ^ (32 : ℕ)| *
      (27 * bumpC / 4 * 2 ^ (2 : ℝ) * (3 / 2)) ≤ 2 * (3 * 10 ^ (32 : ℕ)) * (405 / 2) := by
    rw [habs]
    refine mul_le_mul (mul_le_mul_of_nonneg_right hσsq (by norm_num)) hbump hM0.le (by norm_num)
  have hK : (0 : ℝ) ≤ (zetaSmallTσ ^ 2)⁻¹ * |(3 : ℝ) * 10 ^ (32 : ℕ)| *
      (27 * bumpC / 4 * 2 ^ (2 : ℝ) * (3 / 2)) :=
    mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) hM0.le
  unfold I5const
  calc |π|⁻¹ * 2⁻¹ * 6 * (1 + (zetaSmallTσ ^ 2)⁻¹ * |(3 : ℝ) * 10 ^ (32 : ℕ)| *
        (27 * bumpC / 4 * 2 ^ (2 : ℝ) * (3 / 2)))
      ≤ 1 * (1 + (zetaSmallTσ ^ 2)⁻¹ * |(3 : ℝ) * 10 ^ (32 : ℕ)| *
        (27 * bumpC / 4 * 2 ^ (2 : ℝ) * (3 / 2))) :=
        mul_le_mul_of_nonneg_right hpi (by linarith)
    _ ≤ 1 * (1 + 2 * (3 * 10 ^ (32 : ℕ)) * (405 / 2)) := by linarith
    _ ≤ 10 ^ (36 : ℕ) := by norm_num

/-- The content of `LogDerivZetaBoundedAndHolo`, with the two strip widths named.  The
combined width is the smaller of the two: `A₁` from the `ζ'/ζ` bound, `A₂` from holomorphy. -/
lemma LogDerivZetaBoundedAndHolo_of {A₁ A₂ C : ℝ} (A₁_in : A₁ ∈ Ioc 0 (1 / 2))
    (A₂_in : A₂ ∈ Ioc 0 (1 / 2)) (C_pos : 0 < C) (zeta_bnd : LogDerivZetaHasBound A₁ C)
    (holo : ∀ (T : ℝ) (_ : 3 ≤ T), HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (((Icc ((1 : ℝ) - A₂ / Real.log T ^ 9) 2) ×ℂ (Icc (-T) T)) \ {1})) :
    0 < C ∧ min A₁ A₂ ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound (min A₁ A₂) C
    ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (((Icc ((1 : ℝ) - min A₁ A₂ / Real.log T ^ 9) 2) ×ℂ (Icc (-T) T)) \ {1}) := by
  refine ⟨C_pos, ?_, ?_, ?_⟩
  · exact ⟨lt_min A₁_in.1 A₂_in.1, le_trans (min_le_left _ _) A₁_in.2⟩
  · intro σ T hT hσ
    apply zeta_bnd _ _ hT
    apply mem_Ici.mpr (le_trans _ hσ)
    gcongr
    · bound
    · apply min_le_left
  · intro T hT
    apply (holo _ hT).mono
    intro s hs
    simp only [Set.mem_sdiff, mem_singleton_iff, mem_reProdIm] at hs ⊢
    refine ⟨?_, hs.2⟩
    refine ⟨?_, hs.1.2⟩
    refine ⟨?_, hs.1.1.2⟩
    apply le_trans _ hs.1.1.1
    gcongr
    · bound
    · apply min_le_right

/-- The strip width in `LogDerivZetaBoundedAndHolo`: `min(3.2·10⁻¹³, 2.331·10⁻¹⁶)`, so
`≈ 2.331·10⁻¹⁶`.  This is the `A` that fixes the exponent constant `c = A^{1/10}/4 ≈ 0.0068`
of `MediumPNT`. -/
noncomputable def zetaBndHoloA : ℝ := min zetaLogDerivA zetaHolcLargeTA

/-- `zetaBndHoloA ≥ 10⁻¹⁶` -- the numeral behind `MediumPNT`'s exponent constant. -/
lemma zetaBndHoloA_ge : (1 / 10 : ℝ) ^ (16 : ℕ) ≤ zetaBndHoloA := by
  unfold zetaBndHoloA
  exact le_min (le_trans (by norm_num) zetaLogDerivA_ge) zetaHolcLargeTA_ge

/-- **`MediumPNT`'s exponent constant is at least `1/200`.**  It is `A^{1/10}/4` with
`A = zetaBndHoloA ≈ 2.33·10⁻¹⁶`, so the true value is `≈ 6.8·10⁻³`. -/
lemma zetaBndHoloA_rpow_ge : (1 : ℝ) / 200 ≤ zetaBndHoloA ^ ((1 : ℝ) / 10) / 4 := by
  have hg := zetaBndHoloA_ge
  have h : ((1 : ℝ) / 50) ^ 10 ≤ zetaBndHoloA := by
    have hnum : ((1 : ℝ) / 50) ^ 10 ≤ (1 / 10 : ℝ) ^ (16 : ℕ) := by norm_num
    linarith
  have h0 : (0 : ℝ) ≤ zetaBndHoloA := le_trans (by positivity) hg
  have := le_rpow_tenth h0 h
  linarith

/-- `LogDerivZetaBoundedAndHolo` with both witnesses named. -/
lemma LogDerivZetaBoundedAndHoloExplicit :
    0 < zetaLogDerivUnifC ∧ zetaBndHoloA ∈ Ioc 0 (1 / 2) ∧
    LogDerivZetaHasBound zetaBndHoloA zetaLogDerivUnifC
    ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (((Icc ((1 : ℝ) - zetaBndHoloA / Real.log T ^ 9) 2) ×ℂ (Icc (-T) T)) \ {1}) :=
  LogDerivZetaBoundedAndHolo_of zetaLogDerivA_mem zetaHolcLargeTA_mem zetaLogDerivUnifC_pos
    LogDerivZetaBndUnifExplicit LogDerivZetaHolcLargeTExplicit

open Filter Topology

/-! ### numerals for the `I`-bound constants -/

lemma I4_pt_eq {t : ℝ} :
    ((zetaSmallTσ : ℂ) + (t : ℂ) * (1 - (zetaSmallTσ : ℂ)) - 3 * I)
      = (((zetaSmallTσ + t * (1 - zetaSmallTσ) : ℝ)) : ℂ) + ((-3 : ℝ) : ℂ) * I := by
  push_cast; ring

lemma I4_re_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 - (1 / 10 : ℝ) ^ (16 : ℕ) ≤ zetaSmallTσ + t * (1 - zetaSmallTσ) ∧
      zetaSmallTσ + t * (1 - zetaSmallTσ) ≤ 1 := by
  obtain ⟨h0, h1⟩ := ht
  have hlt : zetaSmallTσ < 1 := zetaSmallTσ_lt_one
  have hv : zetaSmallTσ = 1 - (1 / 10 : ℝ) ^ (16 : ℕ) := rfl
  constructor
  · rw [← hv]; nlinarith
  · nlinarith

/-- Every value of `‖ζ'/ζ‖` on `I4Bound`'s segment is at most `136·10¹⁴`. -/
lemma I4Seg_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ((‖-ζ' ((zetaSmallTσ : ℂ) + (t : ℂ) * (1 - (zetaSmallTσ : ℂ)) - 3 * I) /
      ζ ((zetaSmallTσ : ℂ) + (t : ℂ) * (1 - (zetaSmallTσ : ℂ)) - 3 * I)‖₊ : ℝ))
      ≤ 136 * 10 ^ (14 : ℕ) := by
  obtain ⟨hge, hle⟩ := I4_re_bounds ht
  rw [coe_nnnorm, neg_div, norm_neg, I4_pt_eq]
  refine logDeriv_zeta_le_annulus hge hle ?_ ?_
  · rw [abs_of_nonpos (by norm_num : (-3 : ℝ) ≤ 0)]; norm_num
  · rw [abs_of_nonpos (by norm_num : (-3 : ℝ) ≤ 0)]; norm_num

lemma I4Seg_nonempty : (I4Seg zetaSmallTσ).Nonempty := by
  refine ⟨_, ⟨0, by norm_num, rfl⟩⟩

lemma I4SegSup_le : sSup (I4Seg zetaSmallTσ) ≤ 136 * 10 ^ (14 : ℕ) := by
  refine csSup_le I4Seg_nonempty ?_
  rintro x ⟨t, ht, rfl⟩
  exact I4Seg_le ht

/-- The segment sits at height `-3`, so `‖s‖² ≥ 9` on it. -/
lemma I4SegInf_ge : (9 : NNReal) ≤ I4SegInf zetaSmallTσ := by
  unfold I4SegInf
  refine le_csInf ⟨_, ⟨0, by norm_num, rfl⟩⟩ ?_
  rintro x ⟨t, ht, rfl⟩
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [I4_pt_eq]
  set s : ℂ := (((zetaSmallTσ + t * (1 - zetaSmallTσ) : ℝ)) : ℂ) + ((-3 : ℝ) : ℂ) * I with hs
  have him : s.im = -3 := by rw [hs]; simp
  have hh : (3 : ℝ) ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    rw [him, abs_of_nonpos (by norm_num : (-3 : ℝ) ≤ 0)] at h
    linarith
  nlinarith [norm_nonneg s]

/-! ### the four delegating `I`-bounds, with their constants named -/

lemma I6Bound_of {SmoothingF : ℝ → ℝ} {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂)
    (hσ₂ : σ₂ ∈ Ioo 0 1) {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) {D : ℝ} (Dpos : 0 < D)
    (MellinSmooth1bBound : ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2)
      (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ D * (ε * ‖s‖ ^ 2)⁻¹) :
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1) {T : ℝ} (_ : I4Tlb A σ₂ < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₆ SmoothingF ε X σ₁ σ₂‖ ≤ I4C σ₂ D * X * X ^ (- A / (Real.log T ^ 9)) / ε := by
  have bound := (I4Bound_of h_logDeriv_holo hσ₂ hA Dpos MellinSmooth1bBound).2.2
  refine fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I6I4 (by linarith), norm_neg, norm_conj]

lemma I7Bound_of {SmoothingF : ℝ → ℝ} {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ)
    (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) {CM : ℝ} (CMpos : 0 < CM)
    (CMhyp : ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2)
      (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ CM * (ε * ‖s‖ ^ 2)⁻¹) :
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₇ SmoothingF ε T X σ₁‖ ≤ (logIntC 9 * CM * Cζ) * X * X ^ (- A / (Real.log T ^ 9)) / ε := by
  have bound := I3Bound_of hCζ Cζpos hA CMpos CMhyp
  refine fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I7I3 (by linarith), norm_conj]

lemma I8Bound_of {SmoothingF : ℝ → ℝ} {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound A C₂)
    (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) {C₁ : ℝ} (C₁pos : 0 < C₁)
    (Mbd : ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2)
      (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ C₁ * (ε * ‖s‖ ^ 2)⁻¹)
    {C₃ : ℝ} (C₃_gt : C₃ ≥ 1) (hC₃ : ∀ X ≥ (3 : ℝ), Real.log X ^ 9 ≤ C₃ * X) :
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₈ SmoothingF ε T X σ₁‖
      ≤ (‖1/(2*π*I)‖ * (2 * (C₁ * C₂ * C₃ * rexp 1))) * X / (ε * T) := by
  have i2Bound := I2Bound_of has_bound C₂pos A_in C₁pos Mbd C₃_gt hC₃
  intro X hX ε hε0 hε1 T hT σ₁
  let i2Bound := i2Bound X hX hε0 hε1 hT
  rw [I8I2 hX, norm_neg, norm_conj]
  exact i2Bound

theorem I9Bound_of {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    {M : ℝ} (M_is_pos : 0 < M)
    (M_bounds_mellin_hard : ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2)
      (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ M * (ε * ‖s‖ ^ 2)⁻¹)
    {K : ℝ} (K_is_pos : 0 < K)
    (K_bounds : ∀ (t σ : ℝ), 1 < σ → σ < 2 →
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ K * (σ - 1)⁻¹) :
    ∀ {ε : ℝ} (_ : 0 < ε) (_ : ε < 1) (X : ℝ) (_ : 3 < X) {T : ℝ} (_ : 3 < T),
    ‖I₉ SmoothingF ε X T‖
      ≤ (|π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M)) * X * Real.log X / (ε * T) := by
  have bound := I1Bound_of suppSmoothingF ContDiffSmoothingF SmoothingFnonneg mass_one
    M_is_pos M_bounds_mellin_hard K_is_pos K_bounds
  intro ε εpos ε_lt_one X X_gt T T_gt
  specialize bound ε εpos ε_lt_one X X_gt T_gt
  rwa [I9I1 (by linarith), norm_conj]

/-!
### The implied constant

Everything `RMF.MediumPNT_bound_explicit` asks for, at the explicit witnesses, and the resulting
numeral.  The eleven constants come out as `30 log 2`, `2 log 2`, and the nine `I`-bound constants;
the sum is about `6·10³⁷`, dominated by `c₃ = c₇ = logIntC 9 · M · zetaLogDerivUnifC`.
-/

/-! ### the explicit bump's Mellin constant -/

noncomputable def bumpMellinC : ℝ := 27 * bumpC / 4 * 2 ^ (2 : ℝ) * (3 / 2)

lemma bumpMellinC_eq : bumpMellinC = 81 * bumpC / 2 := by
  have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]; norm_num
  unfold bumpMellinC; rw [h4]; ring

lemma bumpMellinC_pos : (0 : ℝ) < bumpMellinC := by
  rw [bumpMellinC_eq]; linarith [bumpC_pos]

lemma bumpMellinC_le : bumpMellinC ≤ 405 / 2 := by
  rw [bumpMellinC_eq]; linarith [bumpC_le]

lemma bumpMellin_hyp : ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2)
    (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
    ‖𝓜 (fun x ↦ (Smooth1 bumpNu ε x : ℂ)) s‖ ≤ bumpMellinC * (ε * ‖s‖ ^ 2)⁻¹ :=
  MellinOfSmooth1bExplicit bumpNu_contDiff bumpNu_support (fun _ hx => bumpNu_deriv_le hx)

/-! ### the pieces `RMF.MediumPNT_bound_explicit` asks for -/

lemma bump_nonneg : ∀ x > 0, 0 ≤ bumpNu x := fun x _ ↦ bumpNu_nonneg x

lemma bump_massOne : ∫ x in Ioi 0, bumpNu x / x = 1 := by
  rw [← integral_Ici_eq_integral_Ioi]; exact bumpNu_integral

lemma zetaSmallTσ_pos : (0 : ℝ) < zetaSmallTσ := by unfold zetaSmallTσ; norm_num

lemma holo2E : HolomorphicOn (fun s ↦ ζ' s / ζ s)
    (uIcc zetaSmallTσ 2 ×ℂ uIcc (-3) 3 \ {1}) := LogDerivZetaHolcSmallTExplicit

lemma zetaTrivK_pos : (0 : ℝ) < 2 * (zetaTrivC + 1) := by
  have := zetaTrivC_nonneg; linarith

lemma I4SegSup_nonneg : 0 ≤ sSup (I4Seg zetaSmallTσ) := by
  refine Real.sSup_nonneg ?_
  rintro x ⟨t, ht, rfl⟩
  exact NNReal.coe_nonneg _

lemma I4C_le : I4C zetaSmallTσ bumpMellinC ≤ 10 ^ (18 : ℕ) := by
  unfold I4C
  have h1 := I4SegSup_le
  have h0 := I4SegSup_nonneg
  have h2 := bumpMellinC_le
  have h20 := bumpMellinC_pos
  have h3 : (9 : ℝ) ≤ (I4SegInf zetaSmallTσ : ℝ) := by
    have := I4SegInf_ge
    exact_mod_cast this
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma norm_inv_two_pi_I_le : ‖(1 : ℂ) / (2 * (π : ℂ) * I)‖ ≤ 1 / 6 := by
  rw [norm_div, norm_one, norm_mul, norm_mul, norm_I, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
  rw [div_le_div_iff₀ (by linarith [Real.pi_gt_three]) (by norm_num)]
  linarith [Real.pi_gt_three]

lemma abs_pi_inv_half_le : |π|⁻¹ * 2⁻¹ ≤ 1 / 6 := by
  rw [abs_of_pos Real.pi_pos]
  have h : π⁻¹ ≤ 1 / 3 := by
    rw [inv_le_comm₀ Real.pi_pos (by norm_num)]
    linarith [Real.pi_gt_three]
  linarith

/-- **The exponent constant of the effective PNT**: `zetaBndHoloA^{1/10}/4 ≈ 6.8·10⁻³`.
`mediumPNTRate_ge` gives the round numeral `1/200`. -/
noncomputable def mediumPNTRate : ℝ := zetaBndHoloA ^ ((1 : ℝ) / 10) / 4

lemma mediumPNTRate_ge : (1 / 200 : ℝ) ≤ mediumPNTRate := zetaBndHoloA_rpow_ge

/-- `I5const > 0`. -/
lemma I5const_pos : 0 < I5const := by
  have hM : (0 : ℝ) < 27 * bumpC / 4 * 2 ^ (2 : ℝ) * (3 / 2) := bumpMellinC_pos
  have hs2 : (0 : ℝ) ≤ (zetaSmallTσ ^ 2)⁻¹ := by positivity
  have hK : (0 : ℝ) ≤ (zetaSmallTσ ^ 2)⁻¹ * |(3 : ℝ) * 10 ^ (32 : ℕ)| *
      (27 * bumpC / 4 * 2 ^ (2 : ℝ) * (3 / 2)) :=
    mul_nonneg (mul_nonneg hs2 (abs_nonneg _)) hM.le
  have hπ : (0 : ℝ) < |π|⁻¹ * 2⁻¹ * 6 := by
    have : (0 : ℝ) < |π| := abs_pos.mpr Real.pi_ne_zero
    positivity
  unfold I5const
  exact mul_pos hπ (by linarith)

/-- **The implied constant of the effective PNT**, as the closed form
`RMF.MediumPNT_bound_explicit` produces at the explicit witnesses: the smoothing constants
`30 log 2` and `2 log 2`, then `c₁ = c₉`, `c₂ = c₈`, `c₃ = c₇`, `c₄ = c₆` and `c₅`.  About
`6·10³⁷`, dominated by `c₃ = logIntC 9 · M · zetaLogDerivUnifC`; `mediumPNTConst_le` rounds it
to `10³⁹`. -/
noncomputable def mediumPNTConst : ℝ :=
  (30 * Real.log 2 + 2 * Real.log 2)
    + (|π|⁻¹ * 2⁻¹ * (Real.exp 1 * (2 * (zetaTrivC + 1)) * bumpMellinC)
      + ‖1/(2*π*I)‖ * (2 * (bumpMellinC * zetaLogDerivUnifC * 48000 * rexp 1))
      + ‖1/(2*π*I)‖ * (2 * (bumpMellinC * zetaLogDerivUnifC * 48000 * rexp 1))
      + |π|⁻¹ * 2⁻¹ * (Real.exp 1 * (2 * (zetaTrivC + 1)) * bumpMellinC))
    + (logIntC 9 * bumpMellinC * zetaLogDerivUnifC + I4C zetaSmallTσ bumpMellinC
      + I4C zetaSmallTσ bumpMellinC + logIntC 9 * bumpMellinC * zetaLogDerivUnifC)
    + I5const

/-- `mediumPNTConst ≤ 10³⁹`. -/
lemma mediumPNTConst_le : mediumPNTConst ≤ 10 ^ (39 : ℕ) := by
  have hM0 := bumpMellinC_pos
  have hM := bumpMellinC_le
  have hU0 := zetaLogDerivUnifC_pos
  have hU := zetaLogDerivUnifC_le
  have hL0 := (log_pow_over_xsq_integral_bounded_explicit 9).1
  have hLn := logIntC_nine_le
  have he : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hk : 2 * (zetaTrivC + 1) ≤ 14 := by linarith [zetaTrivC_le]
  have hk0 : (0 : ℝ) ≤ 2 * (zetaTrivC + 1) := by linarith [zetaTrivC_nonneg]
  have hnorm := norm_inv_two_pi_I_le
  have hnorm0 : (0 : ℝ) ≤ ‖(1 : ℂ) / (2 * (π : ℂ) * I)‖ := norm_nonneg _
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  -- the four constant groups
  have h1 : |π|⁻¹ * 2⁻¹ * (Real.exp 1 * (2 * (zetaTrivC + 1)) * bumpMellinC) ≤ 1300 := by
    have hin : Real.exp 1 * (2 * (zetaTrivC + 1)) * bumpMellinC ≤ 2.72 * 14 * (405 / 2) :=
      mul_le_mul (mul_le_mul he hk hk0 (by norm_num)) hM hM0.le (by norm_num)
    have := mul_le_mul abs_pi_inv_half_le hin
      (by positivity) (by norm_num : (0:ℝ) ≤ 1 / 6)
    linarith
  have h2 : ‖(1 : ℂ) / (2 * (π : ℂ) * I)‖ *
      (2 * (bumpMellinC * zetaLogDerivUnifC * 48000 * rexp 1)) ≤ 10 ^ (35 : ℕ) := by
    have hp1 : bumpMellinC * zetaLogDerivUnifC ≤ (405 / 2) * 10 ^ (28 : ℕ) :=
      mul_le_mul hM hU hU0.le (by norm_num)
    have hp2 : bumpMellinC * zetaLogDerivUnifC * 48000 ≤ (405 / 2) * 10 ^ (28 : ℕ) * 48000 := by
      gcongr
    have hp3 : bumpMellinC * zetaLogDerivUnifC * 48000 * rexp 1
        ≤ (405 / 2) * 10 ^ (28 : ℕ) * 48000 * 2.72 :=
      mul_le_mul hp2 he he0.le (by norm_num)
    have hin : 2 * (bumpMellinC * zetaLogDerivUnifC * 48000 * rexp 1)
        ≤ 2 * ((405 / 2) * 10 ^ (28 : ℕ) * 48000 * 2.72) := by linarith
    have := mul_le_mul hnorm hin (by positivity) (by norm_num : (0:ℝ) ≤ 1 / 6)
    calc ‖(1 : ℂ) / (2 * (π : ℂ) * I)‖ * (2 * (bumpMellinC * zetaLogDerivUnifC * 48000 * rexp 1))
        ≤ (1 / 6) * (2 * ((405 / 2) * 10 ^ (28 : ℕ) * 48000 * 2.72)) := this
      _ ≤ 10 ^ (35 : ℕ) := by norm_num
  have h3 : logIntC 9 * bumpMellinC * zetaLogDerivUnifC ≤ 3 * 10 ^ (37 : ℕ) := by
    have hp1 : logIntC 9 * bumpMellinC ≤ 10 ^ (7 : ℕ) * (405 / 2) :=
      mul_le_mul hLn hM hM0.le (by norm_num)
    have := mul_le_mul hp1 hU hU0.le (by norm_num : (0:ℝ) ≤ 10 ^ (7 : ℕ) * (405 / 2))
    calc logIntC 9 * bumpMellinC * zetaLogDerivUnifC
        ≤ 10 ^ (7 : ℕ) * (405 / 2) * 10 ^ (28 : ℕ) := this
      _ ≤ 3 * 10 ^ (37 : ℕ) := by norm_num
  have h4 := I4C_le
  have h5 := I5const_le
  unfold mediumPNTConst
  linarith

end MediumPNTExplicit
