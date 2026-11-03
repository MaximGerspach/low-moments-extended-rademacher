/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.CentralWindowExplicit

/-!
# The two-point ratio above `q = ½`

The sharp two-point ratio of the central window and the block split
(`Weighted/CentralWindowExplicit.lean`, for `q ≤ ½`), at every `0 ≤ q ≤ 1`,

`E[‖F(½+σ)‖^{2q-2}‖F(½+σ+it)‖²] ≤ exp(2(1-q)t²S₂)·E‖F(½+σ)‖^{2q}`,
`S₂ = (log y₁)²/2 + 15.003 log y₁ + 34`

(`RMF.integral_mixed_norm_shiftLine_primesIco_le_exp_sharp_of_le_one`).  In the `q ≤ ½` version
only the bracket of one atom uses `q ≤ ½`, through the tilted bias `tanh(2q artanh u) ≥ 2qu`,
which reverses above `½`.  The bracket itself does not: with `1 ± u = e^{(m ± d)/2}` it reads
`sinh((1-q)d) ≤ (1-q)sinh(d)cosh(qd)`, true for every `q ≤ 1`
(`RMF.rpow_sub_rpow_le_sharp_of_le_one`).  The other three lemmas are the `q ≤ ½` ones with that
bracket.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `sinh(θx) ≤ θ·sinh x` for `0 ≤ θ ≤ 1` and `x ≥ 0`: the series `∑ x^{2k+1}/(2k+1)!` termwise. -/
lemma sinh_mul_le_mul_sinh {θ x : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hx : 0 ≤ x) :
    Real.sinh (θ * x) ≤ θ * Real.sinh x := by
  have h1 := Real.hasSum_sinh (θ * x)
  have h2 := (Real.hasSum_sinh x).mul_left θ
  refine hasSum_le (fun k => ?_) h1 h2
  have hpow : (θ * x) ^ (2 * k + 1) ≤ θ * x ^ (2 * k + 1) := by
    rw [mul_pow]
    have : θ ^ (2 * k + 1) ≤ θ := by
      calc θ ^ (2 * k + 1) = θ ^ (2 * k) * θ := pow_succ θ (2 * k)
        _ ≤ 1 * θ := by
          gcongr
          exact pow_le_one₀ hθ0 hθ1
        _ = θ := one_mul θ
    exact mul_le_mul_of_nonneg_right this (pow_nonneg hx _)
  have hf : (0 : ℝ) ≤ ((2 * k + 1).factorial : ℝ)⁻¹ := by positivity
  calc (θ * x) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)
      = (θ * x) ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ)⁻¹ := div_eq_mul_inv _ _
    _ ≤ θ * x ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hpow hf
    _ = θ * (x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) := by ring

/-- **The two-point bracket, sharp, for every `0 ≤ q ≤ 1`**:
`(1-u)^{2q-2} - (1+u)^{2q-2} ≤ 2(1-q)u((1+u)^{2q} + (1-u)^{2q})/(1-u²)²` for `0 ≤ u < 1`.

`RMF.rpow_sub_rpow_le_sharp` proves it for `q ≤ ½` from the tilted bias of one atom, which reverses
above `½`.  Here with `1 ± u = e^{(m ± d)/2}` both sides are exact: the left numerator is
`2e^{(q+1)m}sinh((1-q)d)` and the right `2(1-q)e^{(q+1)m}sinh(d)cosh(qd)`, and
`sinh((1-q)d) ≤ (1-q)sinh d` (`RMF.sinh_mul_le_mul_sinh`), `cosh ≥ 1`. -/
theorem rpow_sub_rpow_le_sharp_of_le_one {u q : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    (1 - u) ^ (2 * q - 2) - (1 + u) ^ (2 * q - 2)
      ≤ 2 * (1 - q) * u / (1 - u ^ 2) ^ 2 * ((1 + u) ^ (2 * q) + (1 - u) ^ (2 * q)) := by
  have hp : 0 < 1 + u := by linarith
  have hm : 0 < 1 - u := by linarith
  set A := (1 + u) ^ (2 * q) with hAdef
  set B := (1 - u) ^ (2 * q) with hBdef
  have hsubA : (1 + u) ^ (2 * q - 2) = A / (1 + u) ^ 2 := by
    rw [Real.rpow_sub hp, hAdef]
    norm_cast
  have hsubB : (1 - u) ^ (2 * q - 2) = B / (1 - u) ^ 2 := by
    rw [Real.rpow_sub hm, hBdef]
    norm_cast
  rw [hsubA, hsubB]
  have hsq : (1 - u ^ 2) ^ 2 = (1 - u) ^ 2 * (1 + u) ^ 2 := by ring
  have hD : 0 < (1 - u ^ 2) ^ 2 := by rw [hsq]; positivity
  -- the exponential form
  set α := Real.log (1 + u) with hα
  set β := Real.log (1 - u) with hβ
  have hea : Real.exp α = 1 + u := Real.exp_log hp
  have heb : Real.exp β = 1 - u := Real.exp_log hm
  have hA' : A = Real.exp (q * ((α + β) + (α - β))) := by
    rw [hAdef, Real.rpow_def_of_pos hp, ← hα]
    ring_nf
  have hB' : B = Real.exp (q * ((α + β) - (α - β))) := by
    rw [hBdef, Real.rpow_def_of_pos hm, ← hβ]
    ring_nf
  have ha2 : (1 + u) ^ 2 = Real.exp ((α + β) + (α - β)) := by
    rw [← hea, ← Real.exp_nat_mul]
    ring_nf
  have hb2 : (1 - u) ^ 2 = Real.exp ((α + β) - (α - β)) := by
    rw [← heb, ← Real.exp_nat_mul]
    ring_nf
  set m := α + β with hmdef
  set d := α - β with hddef
  have hd0 : 0 ≤ d := by
    rw [hddef, hα, hβ]
    linarith [Real.log_le_log hm (by linarith : 1 - u ≤ 1 + u)]
  have hu : u = Real.sinh d * Real.exp m / 2 := by
    rw [Real.sinh_eq, hmdef, hddef]
    have e1 : Real.exp (α - β) * Real.exp (α + β) = (1 + u) ^ 2 := by
      rw [← Real.exp_add, ← hea, ← Real.exp_nat_mul]
      ring_nf
    have e2 : Real.exp (-(α - β)) * Real.exp (α + β) = (1 - u) ^ 2 := by
      rw [← Real.exp_add, ← heb, ← Real.exp_nat_mul]
      ring_nf
    have : (Real.exp (α - β) - Real.exp (-(α - β))) / 2 * Real.exp (α + β) / 2
        = (Real.exp (α - β) * Real.exp (α + β) - Real.exp (-(α - β)) * Real.exp (α + β)) / 4 := by
      ring
    rw [this, e1, e2]
    ring
  -- the two sides
  have hL : B * (1 + u) ^ 2 - A * (1 - u) ^ 2
      = 2 * Real.exp ((q + 1) * m) * Real.sinh ((1 - q) * d) := by
    rw [hA', hB', ha2, hb2, Real.sinh_eq, ← Real.exp_add, ← Real.exp_add]
    have e1 : q * (m - d) + (m + d) = (q + 1) * m + (1 - q) * d := by ring
    have e2 : q * (m + d) + (m - d) = (q + 1) * m + -((1 - q) * d) := by ring
    rw [e1, e2, Real.exp_add, Real.exp_add]
    ring
  have hR : 2 * (1 - q) * u * (A + B)
      = 2 * (1 - q) * Real.exp ((q + 1) * m) * Real.sinh d * Real.cosh (q * d) := by
    rw [hu, hA', hB', Real.cosh_eq]
    have e1 : q * (m + d) = q * m + q * d := by ring
    have e2 : q * (m - d) = q * m + -(q * d) := by ring
    have e3 : (q + 1) * m = q * m + m := by ring
    rw [e1, e2, e3, Real.exp_add (q * m) (q * d), Real.exp_add (q * m) (-(q * d)),
      Real.exp_add (q * m) m]
    ring
  have hkey : Real.sinh ((1 - q) * d) ≤ (1 - q) * Real.sinh d * Real.cosh (q * d) := by
    have h1 := sinh_mul_le_mul_sinh (by linarith : 0 ≤ 1 - q) (by linarith) hd0
    have hs0 : 0 ≤ Real.sinh d := Real.sinh_nonneg_iff.2 hd0
    have hc1 : 1 ≤ Real.cosh (q * d) := Real.one_le_cosh _
    have : (1 - q) * Real.sinh d ≤ (1 - q) * Real.sinh d * Real.cosh (q * d) := by
      have h0 : 0 ≤ (1 - q) * Real.sinh d := mul_nonneg (by linarith) hs0
      nlinarith
    linarith
  have hnum : B * (1 + u) ^ 2 - A * (1 - u) ^ 2 ≤ 2 * (1 - q) * u * (A + B) := by
    rw [hL, hR]
    have he : 0 < Real.exp ((q + 1) * m) := Real.exp_pos _
    have := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ 2 * Real.exp ((q + 1) * m))
    linarith
  have hlhs : B / (1 - u) ^ 2 - A / (1 + u) ^ 2
      = (B * (1 + u) ^ 2 - A * (1 - u) ^ 2) / (1 - u ^ 2) ^ 2 := by
    rw [hsq]
    field_simp
  rw [hlhs, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hD]
  exact hnum

/-- **The two-point local ratio, sharp, for `q ≤ 1`**: `RMF.two_point_local_ratio_le_sharp` with
the bracket of `RMF.rpow_sub_rpow_le_sharp_of_le_one`.  For `0 ≤ a < 1`, `v ≤ a` and
`0 ≤ q ≤ 1`, the mixed moment is at most `(1 + 4(1-q)a(a-v)/(1-a²)²)` times the plain one. -/
theorem two_point_local_ratio_le_sharp_of_le_one {a v q : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hav : v ≤ a) (hq0 : 0 ≤ q) (hq : q ≤ 1) :
    ((1 + a) ^ (2 * q - 2) * (1 + 2 * v + a ^ 2)
        + (1 - a) ^ (2 * q - 2) * (1 - 2 * v + a ^ 2)) / 2
      ≤ ((1 + a) ^ (2 * q) + (1 - a) ^ (2 * q)) / 2
        * (1 + 4 * (1 - q) * (a * (a - v)) / (1 - a ^ 2) ^ 2) := by
  have hB : (0 : ℝ) < 1 - a := by linarith
  have hA : (0 : ℝ) < 1 + a := by linarith
  have hav0 : (0 : ℝ) ≤ a - v := by linarith
  have e1 : (1 + a) ^ (2 * q - 2) * ((1 + a) ^ 2) = (1 + a) ^ (2 * q) := by
    rw [← Real.rpow_natCast (1 + a) 2, ← Real.rpow_add hA]
    norm_num
  have e2 : (1 - a) ^ (2 * q - 2) * ((1 - a) ^ 2) = (1 - a) ^ (2 * q) := by
    rw [← Real.rpow_natCast (1 - a) 2, ← Real.rpow_add hB]
    norm_num
  have hid : ((1 + a) ^ (2 * q - 2) * (1 + 2 * v + a ^ 2)
        + (1 - a) ^ (2 * q - 2) * (1 - 2 * v + a ^ 2)) / 2
      = ((1 + a) ^ (2 * q) + (1 - a) ^ (2 * q)) / 2
        + (a - v) * ((1 - a) ^ (2 * q - 2) - (1 + a) ^ (2 * q - 2)) := by
    rw [← e1, ← e2]
    ring
  rw [hid]
  have hbr' := rpow_sub_rpow_le_sharp_of_le_one ha0 ha1 hq0 hq
  have hstep := mul_le_mul_of_nonneg_left hbr' hav0
  have hfin : (a - v) * (2 * (1 - q) * a / (1 - a ^ 2) ^ 2
        * ((1 + a) ^ (2 * q) + (1 - a) ^ (2 * q)))
      = ((1 + a) ^ (2 * q) + (1 - a) ^ (2 * q)) / 2
        * (4 * (1 - q) * (a * (a - v)) / (1 - a ^ 2) ^ 2) := by ring
  linarith

/-- **The local ratio at one prime, sharp.**  For `w` a nonnegative real with `‖w‖ < 1`, `w'` of
the same modulus and `0 ≤ q ≤ 1`,
`E[‖1+Xw‖^{2q-2}‖1+Xw'‖²] ≤ (1 + 4(1-q)‖w‖(‖w‖ - Re w')/(1-‖w‖²)²)·E‖1+Xw‖^{2q}`. -/
lemma integral_two_point_rademacherLaw_le_sharp_of_le_one {w w' : ℂ} {q : ℝ}
    (hre : w.re = ‖w‖) (hw : ‖w‖ < 1) (hw' : ‖w'‖ = ‖w‖) (hq0 : 0 ≤ q) (hq : q ≤ 1) :
    (∫ z, ‖1 + z * w‖ ^ (2 * (q - 1)) * ‖1 + z * w'‖ ^ (2 * (1 : ℝ)) ∂rademacherLaw)
      ≤ (1 + 4 * (1 - q) * (‖w‖ * (‖w‖ - w'.re)) / (1 - ‖w‖ ^ 2) ^ 2)
          * ∫ z, ‖1 + z * w‖ ^ (2 * q) ∂rademacherLaw := by
  set a : ℝ := ‖w‖ with hadef
  have ha0 : (0 : ℝ) ≤ a := norm_nonneg w
  have hav : w'.re ≤ a := hw' ▸ Complex.re_le_norm w'
  have hpos : (0 : ℝ) < 1 + a := by linarith
  have hneg : (0 : ℝ) < 1 - a := by linarith
  have hp1 : ∀ c : ℝ, ((1 + a) ^ 2 : ℝ) ^ c = (1 + a) ^ (2 * c) := fun c => by
    rw [← Real.rpow_natCast (1 + a) 2, ← Real.rpow_mul hpos.le]
    norm_num
  have hp2 : ∀ c : ℝ, ((1 - a) ^ 2 : ℝ) ^ c = (1 - a) ^ (2 * c) := fun c => by
    rw [← Real.rpow_natCast (1 - a) 2, ← Real.rpow_mul hneg.le]
    norm_num
  have hsq1 : (1 : ℝ) + 2 * a + a ^ 2 = (1 + a) ^ 2 := by ring
  have hsq2 : (1 : ℝ) - 2 * a + a ^ 2 = (1 - a) ^ 2 := by ring
  have he1 : (2 : ℝ) * (q - 1) = 2 * q - 2 := by ring
  rw [integral_norm_one_add_mul_rpow_mul_rademacherLaw,
    integral_norm_one_add_mul_rpow_rademacherLaw, hre, hw', hsq1, hsq2, hp1, hp2, hp1, hp2,
    Real.rpow_one, Real.rpow_one, he1]
  have hkey := two_point_local_ratio_le_sharp_of_le_one (a := a) (v := w'.re) (q := q) ha0 hw hav
    hq0 hq
  linarith

/-- **The mixed moment against the plain one, for a block of primes, sharp.**  For a real
`c ≥ ½`, any `s₁` with `Re s₁ = c` and `0 ≤ q ≤ 1`,
`E[‖F(c)‖^{2q-2}‖F(s₁)‖²] ≤ ∏_p(1 + 4(1-q)p^{-c}(p^{-c} - Re p^{-s₁})/(1-p^{-2c})²)·E‖F(c)‖^{2q}`.
The factorisation of `RMF.integral_mixed_norm_randomEulerProductIco_le`, with the sharp local
ratio. -/
theorem integral_mixed_norm_randomEulerProductIco_le_sharp_of_le_one {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {c q : ℝ} {s₁ : ℂ}
    (hc : 1 / 2 ≤ c) (hre : s₁.re = c) (hq0 : 0 ≤ q) (hq : q ≤ 1) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ (c : ℂ) ω‖
          ^ (2 * (q - 1))
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₁ ω‖
          ^ (2 * (1 : ℝ)) ∂μ)
      ≤ (∏ p ∈ primesIco y₀ y₁,
            (1 + 4 * (1 - q) * ((p : ℝ) ^ (-c) * ((p : ℝ) ^ (-c) - ((p : ℂ) ^ (-s₁)).re))
              / (1 - ((p : ℝ) ^ (-c)) ^ 2) ^ 2))
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (c : ℂ) ω‖ ^ (2 * q) ∂μ := by
  have hsvec : ∀ j ∈ (Finset.univ : Finset (Fin 2)), 0 < (![(c : ℂ), s₁] j).re := by
    intro j _
    fin_cases j <;> simp [hre] <;> linarith
  have hL : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (c : ℂ) ω‖ ^ (2 * (q - 1))
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₁ ω‖
          ^ (2 * (1 : ℝ)) ∂μ)
      = ∏ p ∈ primesIco y₀ y₁, ∫ z, ‖1 + z * (p : ℂ) ^ (-(c : ℂ))‖ ^ (2 * (q - 1))
          * ‖1 + z * (p : ℂ) ^ (-s₁)‖ ^ (2 * (1 : ℝ)) ∂rademacherLaw := by
    have h := integral_prod_norm_randomEulerProductIco_rpow_sqfree hX norm_le_one_rademacherLaw
      y₀ y₁ (Finset.univ : Finset (Fin 2)) hsvec (q := ![q - 1, 1])
    simpa [Fin.prod_univ_two] using h
  have hR : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        (c : ℂ) ω‖ ^ (2 * q) ∂μ)
      = ∏ p ∈ primesIco y₀ y₁,
          ∫ z, ‖1 + z * (p : ℂ) ^ (-(c : ℂ))‖ ^ (2 * q) ∂rademacherLaw := by
    have h := integral_prod_norm_randomEulerProductIco_rpow_sqfree hX norm_le_one_rademacherLaw
      y₀ y₁ (Finset.univ : Finset (Fin 1)) (s := ![(c : ℂ)])
      (fun j _ => by fin_cases j; simp; linarith) (q := ![q])
    simpa [Fin.prod_univ_one] using h
  rw [hL, hR, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p _ => integral_nonneg fun z => ?_) ?_
  · exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)
  intro p hp
  have hp2 := prime_of_mem_primesIco hp
  have hnorm : ‖(p : ℂ) ^ (-(c : ℂ))‖ = (p : ℝ) ^ (-c) := by
    rw [Complex.norm_natCast_cpow_of_pos hp2.pos]
    norm_num
  have hnorm' : ‖(p : ℂ) ^ (-s₁)‖ = (p : ℝ) ^ (-c) := by
    rw [Complex.norm_natCast_cpow_of_pos hp2.pos, Complex.neg_re, hre]
  have hb := integral_two_point_rademacherLaw_le_sharp_of_le_one (w := (p : ℂ) ^ (-(c : ℂ)))
    (w' := (p : ℂ) ^ (-s₁)) (q := q) (by rw [hnorm, re_natCast_cpow_neg_ofReal])
    (by rw [hnorm]; exact prime_rpow_neg_lt_one hp2 (by linarith))
    (by rw [hnorm, hnorm']) hq0 hq
  rwa [hnorm] at hb

/-- **The two-point ratio at one height, sharp.**  For `0 ≤ q ≤ 1`, `σ ≥ 0` and every real `t`,
with `F` the product over `y₀ ≤ p < y₁`,
`E[‖F(½+σ)‖^{2q-2}‖F(½+σ+it)‖²] ≤ exp(2(1-q)t²S₂)·E‖F(½+σ)‖^{2q}`,
`S₂ = (log y₁)²/2 + 15.003 log y₁ + 34`.  No restriction on `t`. -/
theorem integral_mixed_norm_shiftLine_primesIco_le_exp_sharp_of_le_one {X : ℕ → Ω → ℂ}
    {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 0 ≤ q)
    (hq : q ≤ 1) (t : ℝ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ (2 * (q - 1))
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ t) ω‖ ^ (2 * (1 : ℝ)) ∂μ)
      ≤ Real.exp (2 * (1 - q) * t ^ 2
          * (Real.log y₁ ^ 2 / 2 + 15.003 * Real.log y₁ + 34))
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ := by
  have hbase : shiftLine σ 0 = (((1 / 2 + σ : ℝ)) : ℂ) := by simp [shiftLine]
  have hc : (1 : ℝ) / 2 ≤ 1 / 2 + σ := by linarith
  have hmix := integral_mixed_norm_randomEulerProductIco_le_sharp_of_le_one hX y₀ y₁ hc
    (re_shiftLine σ t) hq0 hq
  rw [← hbase] at hmix
  refine le_trans hmix (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun ω => by positivity))
  refine le_trans (prod_one_add_two_point_le_sharp (fun p hp => prime_of_mem_primesIco hp) hc
    (re_shiftLine σ t) (by linarith)) (Real.exp_le_exp.2 ?_)
  rw [im_shiftLine]
  have hS := sum_log_sq_mul_primesIco_le (y₀ := y₀) (y₁ := y₁)
  have hc0 : 0 ≤ 2 * (1 - q) * t ^ 2 := by
    have : 0 ≤ 1 - q := by linarith
    positivity
  exact mul_le_mul_of_nonneg_left hS hc0

end RMF
