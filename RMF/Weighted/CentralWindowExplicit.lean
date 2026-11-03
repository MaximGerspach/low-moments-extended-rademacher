/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.CentralWindow
import RMF.Weighted.EulerMomentSmallQExplicit

/-!
# The central window with its constant

For `0 ≤ q ≤ ½` the tilted two-point ratio
`R(t) = E[‖F(½+σ)‖^{2q-2}‖F(½+σ+it)‖²]/E‖F(½+σ)‖^{2q}` is at most `exp(β t²)` with
`β = 2(1-q)((log y)²/2 + O(log y))`, against the `e^{143800}` that
`RMF.integral_mixed_norm_randomEulerProductIco_le_exp` gives on `|t| log y ≤ 2`.  Three
refinements of `Weighted/CentralWindow.lean`:

* **The bracket, sharp.**  Per prime the ratio is `1 + (a - v)B(a)/D(a)` with
  `B = (1-a)^{2q-2} - (1+a)^{2q-2}` and `D` the plain moment; `B ≤ 4(1-q)aD/(1-a²)²`
  (`RMF.rpow_sub_rpow_le_sharp`), because the tilted bias `w₊ - w₋` of the atom is at least `2qa`
  (`RMF.two_mul_mul_le_rpow_sub_rpow`, from the convexity of `log((1+v)/(1-v))`).
  `RMF.two_point_local_ratio_le` drops the `1 - q` and pays `8192` for `(1-a)^{-5}`.
* **`∑_{p ≤ y}(log p)²/p ≤ (log y)²/2 + 9.003 log y + 1`**
  (`RMF.sum_log_sq_div_primesBelow_le_sharp`), by summation by parts from both sides of Mertens'
  first theorem, against `(log y)² + 5.39 log y`.
* **The ratio kept inside the window integral**, so the window's weight meets `exp(βt²)` rather
  than its supremum (`RMF.integral_rpow_setIntegral_weight_normSq_shiftLine_primesIco_le_sharp`):
  the central window costs `π/σ + 2(e^{βw²} - 1)/w`, not `(π/σ)·e^{143800}`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The tilted bias of one atom -/

/-- `log((1+λu)/(1-λu)) ≤ λ log((1+u)/(1-u))` for `0 ≤ λ ≤ 1`, `0 ≤ u < 1`: the series
`2∑ v^{2k+1}/(2k+1)` termwise. -/
lemma log_ratio_scale_le {u l : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    Real.log (1 + l * u) - Real.log (1 - l * u)
      ≤ l * (Real.log (1 + u) - Real.log (1 - u)) := by
  have hlu0 : 0 ≤ l * u := mul_nonneg hl0 hu0
  have hlu1 : l * u < 1 := lt_of_le_of_lt (mul_le_of_le_one_left hu0 hl1) hu1
  have h1 := Real.hasSum_log_sub_log_of_abs_lt_one (x := l * u)
    (by rw [abs_of_nonneg hlu0]; exact hlu1)
  have h2 := (Real.hasSum_log_sub_log_of_abs_lt_one (x := u)
    (by rw [abs_of_nonneg hu0]; exact hu1)).mul_left l
  refine hasSum_le (fun k => ?_) h1 h2
  have hk : (0 : ℝ) ≤ 2 * (1 / (2 * (k : ℝ) + 1)) := by positivity
  have hpow : (l * u) ^ (2 * k + 1) ≤ l * u ^ (2 * k + 1) := by
    rw [mul_pow]
    have : l ^ (2 * k + 1) ≤ l := by
      calc l ^ (2 * k + 1) = l ^ (2 * k) * l := pow_succ l (2 * k)
        _ ≤ 1 * l := by
          gcongr
          exact pow_le_one₀ hl0 hl1
        _ = l := one_mul l
    exact mul_le_mul_of_nonneg_right this (pow_nonneg hu0 _)
  calc 2 * (1 / (2 * (k : ℝ) + 1)) * (l * u) ^ (2 * k + 1)
      ≤ 2 * (1 / (2 * (k : ℝ) + 1)) * (l * u ^ (2 * k + 1)) :=
        mul_le_mul_of_nonneg_left hpow hk
    _ = l * (2 * (1 / (2 * (k : ℝ) + 1)) * u ^ (2 * k + 1)) := by ring

/-- **The tilted bias of one atom**: `(1+u)^{2q} - (1-u)^{2q} ≥ 2qu((1+u)^{2q} + (1-u)^{2q})` for
`0 ≤ q ≤ ½`, `0 ≤ u < 1`; i.e. `tanh(2q artanh u) ≥ 2qu`. -/
lemma two_mul_mul_le_rpow_sub_rpow {u q : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2) :
    2 * q * u * ((1 + u) ^ (2 * q) + (1 - u) ^ (2 * q))
      ≤ (1 + u) ^ (2 * q) - (1 - u) ^ (2 * q) := by
  have hA : 0 < (1 + u) ^ (2 * q) := Real.rpow_pos_of_pos (by linarith) _
  have hB : 0 < (1 - u) ^ (2 * q) := Real.rpow_pos_of_pos (by linarith) _
  have hl0 : 0 ≤ 2 * q := by linarith
  have hl1 : 2 * q ≤ 1 := by linarith
  have hqu1 : 2 * q * u < 1 := lt_of_le_of_lt (mul_le_of_le_one_left hu0 hl1) hu1
  have hqu0 : 0 ≤ 2 * q * u := mul_nonneg hl0 hu0
  have hkey := log_ratio_scale_le hu0 hu1 hl0 hl1
  have hlogA : Real.log ((1 + u) ^ (2 * q)) = 2 * q * Real.log (1 + u) :=
    Real.log_rpow (by linarith) _
  have hlogB : Real.log ((1 - u) ^ (2 * q)) = 2 * q * Real.log (1 - u) :=
    Real.log_rpow (by linarith) _
  have hlog : Real.log ((1 + 2 * q * u) * (1 - u) ^ (2 * q))
      ≤ Real.log ((1 - 2 * q * u) * (1 + u) ^ (2 * q)) := by
    rw [Real.log_mul (by linarith) hB.ne', Real.log_mul (by linarith) hA.ne', hlogA, hlogB]
    linarith
  have hle := (Real.log_le_log_iff (by positivity) (mul_pos (by linarith) hA)).1 hlog
  nlinarith [hle]

/-! ### The two-point bracket -/

/-- **The two-point bracket, sharp.**  For `0 ≤ q ≤ ½`, `0 ≤ u < 1`:
`(1-u)^{2q-2} - (1+u)^{2q-2} ≤ 2(1-q)u/(1-u²)² · ((1+u)^{2q} + (1-u)^{2q})`, against the
`2(2-2q)u/(1-u)³` of `RMF.rpow_sub_rpow_le`.  With `A, B = (1±u)^{2q}` the left side is
`(B(1+u)² - A(1-u)²)/(1-u²)²`, and `B(1+u)² - A(1-u)² = 2u(A+B) - (A-B)(1+u²) ≤ 2(1-q)u(A+B)`
by the bias. -/
lemma rpow_sub_rpow_le_sharp {u q : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2) :
    (1 - u) ^ (2 * q - 2) - (1 + u) ^ (2 * q - 2)
      ≤ 2 * (1 - q) * u / (1 - u ^ 2) ^ 2 * ((1 + u) ^ (2 * q) + (1 - u) ^ (2 * q)) := by
  have hp : 0 < 1 + u := by linarith
  have hm : 0 < 1 - u := by linarith
  set A := (1 + u) ^ (2 * q) with hAdef
  set B := (1 - u) ^ (2 * q) with hBdef
  have hA : 0 < A := Real.rpow_pos_of_pos hp _
  have hB : 0 < B := Real.rpow_pos_of_pos hm _
  have hbias := two_mul_mul_le_rpow_sub_rpow hu0 hu1 hq0 hq
  rw [← hAdef, ← hBdef] at hbias
  have hsubA : (1 + u) ^ (2 * q - 2) = A / (1 + u) ^ 2 := by
    rw [Real.rpow_sub hp, hAdef]
    norm_cast
  have hsubB : (1 - u) ^ (2 * q - 2) = B / (1 - u) ^ 2 := by
    rw [Real.rpow_sub hm, hBdef]
    norm_cast
  rw [hsubA, hsubB]
  have hsq : (1 - u ^ 2) ^ 2 = (1 - u) ^ 2 * (1 + u) ^ 2 := by ring
  have hD : 0 < (1 - u ^ 2) ^ 2 := by rw [hsq]; positivity
  have hnum : B * (1 + u) ^ 2 - A * (1 - u) ^ 2 ≤ 2 * (1 - q) * u * (A + B) := by
    have h1 : B * (1 + u) ^ 2 - A * (1 - u) ^ 2 = 2 * u * (A + B) - (A - B) * (1 + u ^ 2) := by
      ring
    rw [h1]
    have h2 : 2 * q * u * (A + B) ≤ (A - B) * (1 + u ^ 2) := by
      have hAB : 0 ≤ A - B := le_trans (by positivity) hbias
      calc 2 * q * u * (A + B) ≤ A - B := hbias
        _ = (A - B) * 1 := (mul_one _).symm
        _ ≤ (A - B) * (1 + u ^ 2) := by
          gcongr
          nlinarith [sq_nonneg u]
    linarith
  have hlhs : B / (1 - u) ^ 2 - A / (1 + u) ^ 2
      = (B * (1 + u) ^ 2 - A * (1 - u) ^ 2) / (1 - u ^ 2) ^ 2 := by
    rw [hsq]
    field_simp
  rw [hlhs, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hD]
  calc B * (1 + u) ^ 2 - A * (1 - u) ^ 2
      ≤ 2 * (1 - q) * u * (A + B) := hnum
    _ = 2 * (1 - q) * u * (A + B) := rfl

/-- **The two-point local ratio, sharp.**  For `0 ≤ a < 1`, `v ≤ a` and `0 ≤ q ≤ ½`, the mixed
moment is at most `(1 + 4(1-q)a(a-v)/(1-a²)²)` times the plain one.  The identity of
`RMF.two_point_local_ratio_le` and the sharp bracket `RMF.rpow_sub_rpow_le_sharp`. -/
theorem two_point_local_ratio_le_sharp {a v q : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hav : v ≤ a) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
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
  have hbr' := rpow_sub_rpow_le_sharp ha0 ha1 hq0 hq
  have hstep := mul_le_mul_of_nonneg_left hbr' hav0
  have hfin : (a - v) * (2 * (1 - q) * a / (1 - a ^ 2) ^ 2
        * ((1 + a) ^ (2 * q) + (1 - a) ^ (2 * q)))
      = ((1 + a) ^ (2 * q) + (1 - a) ^ (2 * q)) / 2
        * (4 * (1 - q) * (a * (a - v)) / (1 - a ^ 2) ^ 2) := by ring
  linarith

/-! ### The local ratio, at the law -/

/-- **The local ratio at one prime, sharp.**  For `w` a nonnegative real with `‖w‖ < 1`, `w'` of
the same modulus and `0 ≤ q ≤ ½`,
`E[‖1+Xw‖^{2q-2}‖1+Xw'‖²] ≤ (1 + 4(1-q)‖w‖(‖w‖ - Re w')/(1-‖w‖²)²)·E‖1+Xw‖^{2q}`. -/
lemma integral_two_point_rademacherLaw_le_sharp {w w' : ℂ} {q : ℝ}
    (hre : w.re = ‖w‖) (hw : ‖w‖ < 1) (hw' : ‖w'‖ = ‖w‖) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
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
  have hkey := two_point_local_ratio_le_sharp (a := a) (v := w'.re) (q := q) ha0 hw hav hq0 hq
  linarith

/-- `p^{-c} < 1` at every prime, for `c > 0`. -/
lemma prime_rpow_neg_lt_one {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : 0 < c) :
    (p : ℝ) ^ (-c) < 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

/-- **The mixed moment against the plain one, for a block of primes, sharp.**  For a real
`c ≥ ½`, any `s₁` with `Re s₁ = c` and `0 ≤ q ≤ ½`,
`E[‖F(c)‖^{2q-2}‖F(s₁)‖²] ≤ ∏_p(1 + 4(1-q)p^{-c}(p^{-c} - Re p^{-s₁})/(1-p^{-2c})²)·E‖F(c)‖^{2q}`.
The factorisation of `RMF.integral_mixed_norm_randomEulerProductIco_le`, with the sharp local
ratio. -/
theorem integral_mixed_norm_randomEulerProductIco_le_sharp {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {c q : ℝ} {s₁ : ℂ}
    (hc : 1 / 2 ≤ c) (hre : s₁.re = c) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
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
  have hb := integral_two_point_rademacherLaw_le_sharp (w := (p : ℂ) ^ (-(c : ℂ)))
    (w' := (p : ℂ) ^ (-s₁)) (q := q) (by rw [hnorm, re_natCast_cpow_neg_ofReal])
    (by rw [hnorm]; exact prime_rpow_neg_lt_one hp2 (by linarith))
    (by rw [hnorm, hnorm']) hq0 hq
  rwa [hnorm] at hb

/-! ### The product of the local ratios -/

/-- `x/(1-x)² ≤ x + 6x²` on `[0, ½]`: the chord of `(1-x)^{-2}`. -/
lemma div_one_sub_sq_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    x / (1 - x) ^ 2 ≤ x + 6 * x ^ 2 := by
  have hpos : 0 < (1 - x) ^ 2 := by
    have : 0 < 1 - x := by linarith
    positivity
  rw [div_le_iff₀ hpos]
  have hkey : 0 ≤ x * ((2 * x - 1) * (3 * x - 4)) := by
    apply mul_nonneg hx0
    nlinarith
  nlinarith [hkey]

/-- **The product of the sharp local ratios, over any set of primes**, at `c ≥ ½`, `Re s₁ = c`:
`∏_{p∈S}(1 + 4(1-q)p^{-c}(p^{-c} - Re p^{-s₁})/(1-p^{-2c})²)` is at most
`exp(2(1-q)t²∑_{p∈S}(log p)²(1/p + 6/p²))`, `t = Im s₁`, by `1 - cos θ ≤ θ²/2`,
`p^{-2c}/(1-p^{-2c})² ≤ 1/p + 6/p²` and `1 + u ≤ e^u`. -/
theorem prod_one_add_two_point_le_sharp {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {c q : ℝ}
    {s₁ : ℂ} (hc : 1 / 2 ≤ c) (hre : s₁.re = c) (hq1 : q ≤ 1) :
    (∏ p ∈ S, (1 + 4 * (1 - q) * ((p : ℝ) ^ (-c) * ((p : ℝ) ^ (-c) - ((p : ℂ) ^ (-s₁)).re))
        / (1 - ((p : ℝ) ^ (-c)) ^ 2) ^ 2))
      ≤ Real.exp (2 * (1 - q) * s₁.im ^ 2
          * ∑ p ∈ S, Real.log p ^ 2 * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2)) := by
  set f : ℕ → ℝ := fun p =>
    4 * (1 - q) * ((p : ℝ) ^ (-c) * ((p : ℝ) ^ (-c) - ((p : ℂ) ^ (-s₁)).re))
      / (1 - ((p : ℝ) ^ (-c)) ^ 2) ^ 2 with hfdef
  have hq1' : 0 ≤ 1 - q := by linarith
  have hkey : ∀ p ∈ S, 0 ≤ f p ∧ f p ≤ 2 * (1 - q) * s₁.im ^ 2
      * (Real.log p ^ 2 * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2)) := by
    intro p hp
    have hp2 := hS p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp2.pos
    have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2.two_le
    set x : ℝ := ((p : ℝ) ^ (-c)) ^ 2 with hxdef
    have hx0 : 0 ≤ x := by positivity
    have hxp : x ≤ 1 / (p : ℝ) := by
      have h := prime_rpow_neg_mul_self_le_inv hp2 hc
      rw [one_mul] at h
      rw [hxdef, sq, one_div]
      exact h
    have hx2 : x ≤ 1 / 2 := le_trans hxp (one_div_le_one_div_of_le (by norm_num) hp2r)
    have hC0 : (0 : ℝ) ≤ 1 - Real.cos (s₁.im * Real.log p) := by
      linarith [Real.cos_le_one (s₁.im * Real.log p)]
    have hC1 : 1 - Real.cos (s₁.im * Real.log p) ≤ (s₁.im * Real.log p) ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := s₁.im * Real.log p)]
    have hfeq : f p = 4 * (1 - q) * (x / (1 - x) ^ 2) * (1 - Real.cos (s₁.im * Real.log p)) := by
      rw [hfdef]
      simp only
      rw [re_natCast_cpow_neg hp2.pos, hre, hxdef]
      ring
    have hw : x / (1 - x) ^ 2 ≤ 1 / (p : ℝ) + 6 / (p : ℝ) ^ 2 := by
      refine le_trans (div_one_sub_sq_le hx0 hx2) ?_
      have h6 : 6 * x ^ 2 ≤ 6 / (p : ℝ) ^ 2 := by
        have : x ^ 2 ≤ (1 / (p : ℝ)) ^ 2 := pow_le_pow_left₀ hx0 hxp 2
        calc 6 * x ^ 2 ≤ 6 * (1 / (p : ℝ)) ^ 2 := by linarith
          _ = 6 / (p : ℝ) ^ 2 := by ring
      linarith
    have hw0 : 0 ≤ x / (1 - x) ^ 2 := by
      have : 0 < 1 - x := by linarith
      positivity
    refine ⟨by rw [hfeq]; positivity, ?_⟩
    rw [hfeq]
    have hmul : (x / (1 - x) ^ 2) * (1 - Real.cos (s₁.im * Real.log p))
        ≤ (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2) * ((s₁.im * Real.log p) ^ 2 / 2) :=
      mul_le_mul hw hC1 hC0 (by positivity)
    have := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ 4 * (1 - q))
    nlinarith [this]
  have hsum : ∑ p ∈ S, f p ≤ 2 * (1 - q) * s₁.im ^ 2
      * ∑ p ∈ S, Real.log p ^ 2 * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => (hkey p hp).2
  calc ∏ p ∈ S, (1 + f p)
      ≤ ∏ p ∈ S, Real.exp (f p) :=
        Finset.prod_le_prod (fun p hp => by linarith [(hkey p hp).1])
          (fun p _ => (add_comm 1 (f p)).le.trans (Real.add_one_le_exp _))
    _ = Real.exp (∑ p ∈ S, f p) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.2 hsum

/-! ### The prime sum, with its main term -/

/-- **Mertens' first theorem from below**: `∑_{p ≤ y} (log p)/p ≥ log y - 3.6165` for `y ≥ 1`,
from `Mertens.E₁p.ge` and `Mertens.E₁.le`. -/
lemma sum_log_div_primesBelow_ge {y : ℕ} (hy : 1 ≤ y) :
    Real.log y - 3.6165 ≤ ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p := by
  classical
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have heq := Mertens.sum_log_prime_div_eq (y : ℝ)
  have hge := Mertens.E₁p.ge hy1
  have hE := Mertens.E₁.le
  rw [Nat.floor_natCast] at heq
  have hset : Finset.filter (fun p => Nat.Prime p) (Finset.Ioc 0 y) = Nat.primesBelow (y + 1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesBelow]
    exact ⟨fun hp => ⟨by omega, hp.2⟩, fun hp => ⟨⟨hp.2.pos, by omega⟩, hp.2⟩⟩
  rw [hset] at heq
  rw [heq]
  linarith [Real.log_two_lt_d9]

/-- **`∑_{p ≤ N} (log p)²/p ≤ (log N)²/2 + 9.003 log N + 1`.**  Summation by parts:
`∑_{p≤N}(log p)²/p = C(N) log N - ∑_{n<N} C(n)Δ_n`, `C(n) = ∑_{p≤n}(log p)/p`,
`Δ_n = log(n+1) - log n`, with `log n - 3.6165 ≤ C(n) ≤ log n + log 4 + 4`, `∑_{n<N}Δ_n = log N` and
`∑_{n<N}(log n)Δ_n = (log N)²/2 - ∑Δ_n²/2 ≥ (log N)²/2 - 1`. -/
theorem sum_log_sq_div_primesBelow_le_sharp (N : ℕ) :
    ∑ p ∈ Nat.primesBelow (N + 1), Real.log p ^ 2 / p
      ≤ Real.log N ^ 2 / 2 + 9.003 * Real.log N + 1 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun n => if n.Prime then Real.log n / n else 0 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ → ℝ, C = fun n => ∑ k ∈ Finset.range (n + 1), c k := ⟨_, rfl⟩
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℕ → ℝ, Δ = fun n => Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) :=
    ⟨_, rfl⟩
  -- the sums over primes, as sums over `range`
  have hCp : ∀ n, C n = ∑ p ∈ Nat.primesBelow (n + 1), Real.log p / p := by
    intro n
    rw [hC, Nat.primesBelow, Finset.sum_filter]
    exact Finset.sum_congr rfl fun k _ => by rw [hc]
  have hT : ∑ p ∈ Nat.primesBelow (N + 1), Real.log p ^ 2 / p
      = ∑ k ∈ Finset.range (N + 1), c k * Real.log k := by
    rw [Nat.primesBelow, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k.Prime
    · simp only [hc, hk, if_true]
      ring
    · simp [hc, hk]
  -- the Abel identity
  have habel : ∀ M : ℕ, ∑ k ∈ Finset.range (M + 1), c k * Real.log k
      = C M * Real.log M - ∑ n ∈ Finset.range M, C n * Δ n := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun n => C n * Δ n)]
      have hCs : C (M + 1) = C M + c (M + 1) := by
        rw [hC]
        exact Finset.sum_range_succ c (M + 1)
      rw [hCs, hΔ]
      simp only
      ring
  -- the two sides of Mertens' first theorem, for every `n`
  have hCup : ∀ n : ℕ, C n ≤ Real.log n + Real.log 4 + 4 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      rw [hC]
      simp [hc]
      linarith
    · rw [hCp]
      exact sum_log_div_primesBelow_le hn
  have hClow : ∀ n : ℕ, Real.log n - 3.6165 ≤ C n := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [hC]
      simp [hc]
      norm_num
    · rw [hCp]
      exact sum_log_div_primesBelow_ge hn
  -- the increments
  have hΔ0 : ∀ n : ℕ, 0 ≤ Δ n := by
    intro n
    rw [hΔ]
    simp only
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h2 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      linarith [Real.log_le_log h1 h2]
  have hΔsq : ∑ n ∈ Finset.range N, Δ n ^ 2 ≤ 2 := by
    have hsplit : ∑ n ∈ Finset.range N, Δ n ^ 2
        ≤ ∑ n ∈ Finset.Ioo 0 N, ((n : ℝ) ^ 2)⁻¹ := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        simp
      have hr : Finset.range N = insert 0 (Finset.Ioo 0 N) := by
        ext n
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
        omega
      rw [hr, Finset.sum_insert (by simp)]
      have hz : Δ 0 = 0 := by rw [hΔ]; simp
      rw [hz, zero_pow two_ne_zero, zero_add]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Ioo.1 hn).1
      have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hle : Δ n ≤ 1 / (n : ℝ) := by
        rw [hΔ]
        simp only
        have hlog := Real.log_le_sub_one_of_pos
          (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / n)
        rw [Real.log_div (by positivity) hpos.ne'] at hlog
        have : ((n + 1 : ℕ) : ℝ) / n - 1 = 1 / (n : ℝ) := by
          push_cast
          field_simp
          ring
        linarith
      have h0 := hΔ0 n
      have : Δ n ^ 2 ≤ (1 / (n : ℝ)) ^ 2 := pow_le_pow_left₀ h0 hle 2
      rw [one_div, inv_pow] at this
      exact this
    have h2 := sum_Ioo_inv_sq_le (α := ℝ) 0 N
    norm_num at h2
    exact hsplit.trans h2
  -- telescoping
  have hΔsum : ∑ n ∈ Finset.range N, Δ n = Real.log N := by
    rw [hΔ]
    have := Finset.sum_range_sub (fun n : ℕ => Real.log (n : ℝ)) N
    simpa using this
  have hlogΔ : ∑ n ∈ Finset.range N, Real.log n * Δ n
      = Real.log N ^ 2 / 2 - ∑ n ∈ Finset.range N, Δ n ^ 2 / 2 := by
    have hpt : ∀ n : ℕ, Real.log n * Δ n
        = (Real.log ((n + 1 : ℕ) : ℝ) ^ 2 - Real.log (n : ℝ) ^ 2) / 2 - Δ n ^ 2 / 2 := by
      intro n
      rw [hΔ]
      ring
    rw [Finset.sum_congr rfl fun n _ => hpt n, Finset.sum_sub_distrib, ← Finset.sum_div]
    have := Finset.sum_range_sub (fun n : ℕ => Real.log (n : ℝ) ^ 2) N
    simp only [Nat.cast_zero, Real.log_zero] at this
    rw [this]
    ring
  -- assemble
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hlow : ∑ n ∈ Finset.range N, (Real.log n - 3.6165) * Δ n
      ≤ ∑ n ∈ Finset.range N, C n * Δ n :=
    Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (hClow n) (hΔ0 n)
  have hexp : ∑ n ∈ Finset.range N, (Real.log n - 3.6165) * Δ n
      = ∑ n ∈ Finset.range N, Real.log n * Δ n - 3.6165 * ∑ n ∈ Finset.range N, Δ n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hsqdiv : ∑ n ∈ Finset.range N, Δ n ^ 2 / 2 ≤ 1 := by
    rw [← Finset.sum_div]
    linarith
  have hup := mul_le_mul_of_nonneg_right (hCup N) hlogN
  rw [hT, habel N]
  rw [hexp, hlogΔ, hΔsum] at hlow
  have h4 : Real.log 4 ≤ 1.3863 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h2]
    linarith [Real.log_two_lt_d9]
  have h4N := mul_le_mul_of_nonneg_right h4 hlogN
  nlinarith [hup, hlow, hsqdiv, hlogN, h4N]

/-- **The weighted prime sum of the sharp two-point ratio**:
`∑_{y₀≤p<y₁}(log p)²(1/p + 6/p²) ≤ (log y₁)²/2 + 15.003 log y₁ + 34`, using
`(log p)²/p² ≤ (log p)/p` for the second part. -/
theorem sum_log_sq_mul_primesIco_le {y₀ y₁ : ℕ} :
    ∑ p ∈ primesIco y₀ y₁, Real.log p ^ 2 * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2)
      ≤ Real.log y₁ ^ 2 / 2 + 15.003 * Real.log y₁ + 34 := by
  classical
  rcases Nat.lt_or_ge y₁ 2 with hy | hy
  · -- no primes below `2`
    have hempty : primesIco y₀ y₁ = ∅ := by
      ext p
      simp only [Finset.notMem_empty, iff_false]
      intro hp
      obtain ⟨hprime, -, hlt⟩ := mem_primesIco.1 hp
      have := hprime.two_le
      omega
    rw [hempty, Finset.sum_empty]
    have := Real.log_natCast_nonneg y₁
    positivity
  obtain ⟨N, rfl⟩ : ∃ N, y₁ = N + 1 := ⟨y₁ - 1, by omega⟩
  have hN1 : 1 ≤ N := by omega
  have hsub : primesIco y₀ (N + 1) ⊆ Nat.primesBelow (N + 1) := by
    intro p hp
    obtain ⟨hprime, -, hlt⟩ := mem_primesIco.1 hp
    exact Nat.mem_primesBelow.2 ⟨hlt, hprime⟩
  have hnn : ∀ p ∈ Nat.primesBelow (N + 1), p ∉ primesIco y₀ (N + 1) →
      (0 : ℝ) ≤ Real.log p ^ 2 * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2) := fun p _ _ => by positivity
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn) ?_
  have hsplit : ∑ p ∈ Nat.primesBelow (N + 1), Real.log p ^ 2 * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2)
      = ∑ p ∈ Nat.primesBelow (N + 1), Real.log p ^ 2 / p
        + 6 * ∑ p ∈ Nat.primesBelow (N + 1), Real.log p ^ 2 / (p : ℝ) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hsq : ∑ p ∈ Nat.primesBelow (N + 1), Real.log p ^ 2 / (p : ℝ) ^ 2
      ≤ ∑ p ∈ Nat.primesBelow (N + 1), Real.log p / p := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hprime := Nat.prime_of_mem_primesBelow hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hl0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hlp : Real.log p ≤ p := by linarith [Real.log_le_sub_one_of_pos hp0]
    rw [div_le_div_iff₀ (by positivity) hp0]
    nlinarith [mul_le_mul_of_nonneg_left hlp (mul_nonneg hl0 hp0.le)]
  have h1 := sum_log_sq_div_primesBelow_le_sharp N
  have h2 := sum_log_div_primesBelow_le hN1
  have hmono : Real.log N ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hN1) (by exact_mod_cast Nat.le_succ N)
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have h4 : Real.log 4 ≤ 1.3863 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h2]
    linarith [Real.log_two_lt_d9]
  rw [hsplit]
  nlinarith [h1, h2, hsq, hmono, hlogN, h4]

/-! ### The window, with the ratio kept inside -/

/-- **The two-point ratio at one height, sharp.**  For `0 ≤ q ≤ ½`, `σ ≥ 0` and every real `t`,
with `F` the product over `y₀ ≤ p < y₁`,
`E[‖F(½+σ)‖^{2q-2}‖F(½+σ+it)‖²] ≤ exp(2(1-q)t²S₂)·E‖F(½+σ)‖^{2q}`,
`S₂ = (log y₁)²/2 + 15.003 log y₁ + 34`.  No restriction on `t`. -/
theorem integral_mixed_norm_shiftLine_primesIco_le_exp_sharp {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2) (t : ℝ) :
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
  have hmix := integral_mixed_norm_randomEulerProductIco_le_sharp hX y₀ y₁ hc
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

/-- **The central window for a block of primes, with a weight in `t`, sharp.**  For `0 ≤ q ≤ ½`,
`y₁ ≥ 2`, `σ ≥ 0`, any `w`, and a nonnegative bounded measurable `ρ` with `0 < ∫_{|t|≤w}ρ`:
if `∫_{|t|≤w} ρ(t)e^{βt²}dt ≤ R` with `β ≥ 2(1-q)S₂`, `S₂ = (log y₁)²/2 + 15.003 log y₁ + 34`, then
`E[(∫_{|t|≤w}ρ(t)‖F(½+σ+it)‖²dt)^q] ≤ R^q·E‖F(½+σ)‖^{2q}`, `F` over `y₀ ≤ p < y₁`.
`RMF.integral_rpow_setIntegral_weight_normSq_shiftLine_primesIco_le` with the two-point ratio
kept at each height (`RMF.integral_mixed_norm_shiftLine_primesIco_le_exp_sharp`) instead of its
supremum over `|t| log y₁ ≤ 2`. -/
theorem integral_rpow_setIntegral_weight_normSq_shiftLine_primesIco_le_sharp {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {y₀ y₁ : ℕ} (hy : 2 ≤ y₁)
    {σ w q R Bd β : ℝ} {ρ : ℝ → ℝ} (hσ : 0 ≤ σ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2)
    (hβ : 2 * (1 - q) * (Real.log y₁ ^ 2 / 2 + 15.003 * Real.log y₁ + 34) ≤ β)
    (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρb : ∀ t, ρ t ≤ Bd)
    (hρpos : 0 < ∫ t in Set.Icc (-w) w, ρ t)
    (hρR : (∫ t in Set.Icc (-w) w, ρ t * Real.exp (β * t ^ 2)) ≤ R) :
    (∫ ω, (∫ t in Set.Icc (-w) w, ρ t *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ R ^ q
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (-w) w)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hq1 : q ≤ 1 := by linarith
  have hc0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hlogy : (0 : ℝ) ≤ Real.log y₁ :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y₁))
  have hβ0 : 0 ≤ β := by
    have : 0 ≤ 2 * (1 - q) * (Real.log y₁ ^ 2 / 2 + 15.003 * Real.log y₁ + 34) := by
      have : 0 ≤ 1 - q := by linarith
      positivity
    linarith
  have henvall := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y₁ hc0
  set V : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) with hVdef
  set U : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) with hUdef
  have hV : (0 : ℝ) < V := prod_one_sub_prime_rpow_primesIco_pos_of_pos hc0
  have hUpos : (0 : ℝ) < U := Finset.prod_pos fun p _ => by positivity
  -- the weight, and the weight against the ratio, are integrable on the window
  have hρint : Integrable ρ (volume.restrict (Set.Icc (-w) w)) := by
    refine (memLp_top_of_bound hρm.aestronglyMeasurable Bd ?_).integrable le_top
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
    exact hρb t
  have hρEint : Integrable (fun t => ρ t * Real.exp (β * t ^ 2))
      (volume.restrict (Set.Icc (-w) w)) := by
    refine (memLp_top_of_bound (hρm.mul (by fun_prop)).aestronglyMeasurable
      (Bd * Real.exp (β * w ^ 2)) ?_).integrable le_top
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have hsq : t ^ 2 ≤ w ^ 2 := by
      have habs : |t| ≤ w := abs_le.2 ⟨ht.1, ht.2⟩
      have h0 : 0 ≤ |t| := abs_nonneg t
      calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
        _ ≤ w ^ 2 := pow_le_pow_left₀ h0 habs 2
    change ‖ρ t * Real.exp (β * t ^ 2)‖ ≤ Bd * Real.exp (β * w ^ 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ0 t) (Real.exp_pos _).le)]
    exact mul_le_mul (hρb t) (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hsq hβ0))
      (Real.exp_pos _).le (le_trans (hρ0 t) (hρb t))
  have hR0 : 0 ≤ R :=
    le_trans (integral_nonneg fun t => mul_nonneg (hρ0 t) (Real.exp_pos _).le) hρR
  -- the window integral, and its two-sided bound
  have hslice := integrable_uncurry_weight_normSq_shiftLine_primesIco hX y₀ y₁ (w := w) hc0 hρm
    hρ0 hρb
  have hWint : Integrable (fun ω => ∫ t in Set.Icc (-w) w, ρ t *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        (shiftLine σ t) ω‖ ^ 2) μ := hslice.integral_prod_left
  have hWnn : ∀ ω : Ω, (0 : ℝ) ≤ ∫ t in Set.Icc (-w) w, ρ t *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        (shiftLine σ t) ω‖ ^ 2 :=
    fun ω => integral_nonneg fun t => mul_nonneg (hρ0 t) (by positivity)
  have hcm : ∀ C : ℝ, (∫ t in Set.Icc (-w) w, ρ t * C)
      = (∫ t in Set.Icc (-w) w, ρ t) * C := fun C => integral_mul_const C ρ
  have hWbd : ∀ᵐ ω ∂μ, (V ^ 2 * (∫ t in Set.Icc (-w) w, ρ t)
        ≤ ∫ t in Set.Icc (-w) w, ρ t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2)
      ∧ (∫ t in Set.Icc (-w) w, ρ t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2) ≤ U ^ 2 * (∫ t in Set.Icc (-w) w, ρ t) := by
    filter_upwards [henvall, hslice.prod_right_ae] with ω hω hint
    constructor
    · rw [show V ^ 2 * (∫ t in Set.Icc (-w) w, ρ t)
          = (∫ t in Set.Icc (-w) w, ρ t) * V ^ 2 by ring, ← hcm]
      refine integral_mono (hρint.mul_const _) hint fun t => ?_
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hV.le (hω (shiftLine σ t) (re_shiftLine σ t)).1 2) (hρ0 t)
    · rw [show U ^ 2 * (∫ t in Set.Icc (-w) w, ρ t)
          = (∫ t in Set.Icc (-w) w, ρ t) * U ^ 2 by ring, ← hcm]
      refine integral_mono hint (hρint.mul_const _) fun t => ?_
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hω (shiftLine σ t) (re_shiftLine σ t)).2 2) (hρ0 t)
  -- the plain moment, read as `N^q`
  have hnorm : ∀ (r : ℝ) (ω : Ω),
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ (2 * r)
        = (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ 2) ^ r := fun r ω => norm_rpow_two_mul _ r
  rw [integral_congr_ae (Filter.Eventually.of_forall (hnorm q))]
  refine integral_rpow_le_of_mixed_le hq0 hq1 ?_ (.of_forall hWnn) ?_ ?_ ?_ ?_ ?_ hR0 ?_
  -- `0 < N`
  · filter_upwards [henvall] with ω hω
    exact pow_pos (lt_of_lt_of_le hV (hω (shiftLine σ 0) (re_shiftLine σ 0)).1) 2
  -- `N^q` integrable
  · exact (integrable_norm_randomEulerProductIco_rpow hX y₀ y₁ hc0 (re_shiftLine σ 0)
      (2 * q)).congr (Filter.Eventually.of_forall (hnorm q))
  -- `N^{q-1}·W` integrable
  · refine Integrable.bdd_mul (c := (V ^ 2) ^ (q - 1)) hWint
      (((integrable_norm_randomEulerProductIco_rpow hX y₀ y₁ hc0 (re_shiftLine σ 0)
        (2 * (q - 1))).congr (Filter.Eventually.of_forall (hnorm (q - 1)))).1) ?_
    filter_upwards [henvall] with ω hω
    have h1 := (hω (shiftLine σ 0) (re_shiftLine σ 0)).1
    have h2 : (0 : ℝ) < V ^ 2 := by positivity
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (le_of_lt (pow_pos (lt_of_lt_of_le hV h1) 2)) _)]
    exact Real.rpow_le_rpow_of_nonpos h2 (pow_le_pow_left₀ hV.le h1 2) (by linarith)
  -- `W^q` integrable
  · refine (memLp_top_of_bound
      ((Real.continuous_rpow_const hq0).comp_aestronglyMeasurable hWint.1)
      ((U ^ 2 * (∫ t in Set.Icc (-w) w, ρ t)) ^ q) ?_).integrable le_top
    filter_upwards [hWbd] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hWnn ω) _)]
    exact Real.rpow_le_rpow (hWnn ω) hω.2 hq0
  -- `0 < ∫ N^q`
  · have h := integral_norm_randomEulerProductIco_rpow_pos hX y₀ y₁ hc0 (re_shiftLine σ 0)
      (2 * q)
    rwa [integral_congr_ae (Filter.Eventually.of_forall (hnorm q))] at h
  -- `0 < ∫ N^{q-1}·W`
  · have hlow : ∀ᵐ ω ∂μ, (U ^ 2) ^ (q - 1) * (V ^ 2 * (∫ t in Set.Icc (-w) w, ρ t))
        ≤ (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
          * ∫ t in Set.Icc (-w) w, ρ t *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
                (shiftLine σ t) ω‖ ^ 2 := by
      filter_upwards [henvall, hWbd] with ω hω hWω
      have h1 := (hω (shiftLine σ 0) (re_shiftLine σ 0)).1
      have h2 := (hω (shiftLine σ 0) (re_shiftLine σ 0)).2
      have hpos : (0 : ℝ) < ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          y₀ y₁ (shiftLine σ 0) ω‖ ^ 2 := pow_pos (lt_of_lt_of_le hV h1) 2
      refine mul_le_mul (Real.rpow_le_rpow_of_nonpos hpos
        (pow_le_pow_left₀ (norm_nonneg _) h2 2) (by linarith)) hWω.1
        (by positivity) (Real.rpow_nonneg (le_of_lt hpos) _)
    have hcpos : (0 : ℝ) < (U ^ 2) ^ (q - 1) * (V ^ 2 * (∫ t in Set.Icc (-w) w, ρ t)) :=
      mul_pos (Real.rpow_pos_of_pos (pow_pos hUpos 2) (q - 1)) (mul_pos (pow_pos hV 2) hρpos)
    refine lt_of_lt_of_le hcpos ?_
    calc (U ^ 2) ^ (q - 1) * (V ^ 2 * (∫ t in Set.Icc (-w) w, ρ t))
        = ∫ _ω, (U ^ 2) ^ (q - 1) * (V ^ 2 * (∫ t in Set.Icc (-w) w, ρ t)) ∂μ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _)
          (by
            refine Integrable.bdd_mul (c := (V ^ 2) ^ (q - 1)) hWint
              (((integrable_norm_randomEulerProductIco_rpow hX y₀ y₁ hc0 (re_shiftLine σ 0)
                (2 * (q - 1))).congr (Filter.Eventually.of_forall (hnorm (q - 1)))).1) ?_
            filter_upwards [henvall] with ω hω
            have h1 := (hω (shiftLine σ 0) (re_shiftLine σ 0)).1
            have h2 : (0 : ℝ) < V ^ 2 := by positivity
            rw [Real.norm_eq_abs,
              abs_of_nonneg
                (Real.rpow_nonneg (le_of_lt (pow_pos (lt_of_lt_of_le hV h1) 2)) _)]
            exact Real.rpow_le_rpow_of_nonpos h2 (pow_le_pow_left₀ hV.le h1 2) (by linarith))
          hlow
  -- the mixed bound, via Fubini, with the ratio at each height
  · have hswap := integral_rpow_mul_setIntegral_weight_normSq_swap_primesIco hX y₀ y₁
      (r := 2 * (q - 1)) (w := w) hc0 hρm hρ0 hρb
    have he : (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
        * (∫ t in Set.Icc (-w) w, ρ t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2) ∂μ)
        = ∫ t in Set.Icc (-w) w, ∫ ω,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
                (shiftLine σ 0) ω‖ ^ (2 * (q - 1))
              * (ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
                (shiftLine σ t) ω‖ ^ 2) ∂μ := by
      rw [← hswap]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      dsimp only
      rw [hnorm (q - 1) ω]
    rw [he]
    have hMnn : (0 : ℝ) ≤ ∫ ω,
        (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ 2) ^ q ∂μ :=
      integral_nonneg fun ω => Real.rpow_nonneg (by positivity) _
    have hpt : ∀ t ∈ Set.Icc (-w) w,
        (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ (2 * (q - 1))
            * (ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2) ∂μ)
          ≤ ρ t * Real.exp (β * t ^ 2) * ∫ ω,
              (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
                (shiftLine σ 0) ω‖ ^ 2) ^ q ∂μ := by
      intro t _
      have hmix := integral_mixed_norm_shiftLine_primesIco_le_exp_sharp hX y₀ y₁ hσ hq0 hq t
      have hone : ∀ v : ℂ, ‖v‖ ^ (2 * (1 : ℝ)) = ‖v‖ ^ 2 := fun v => by
        rw [norm_rpow_two_mul v 1, Real.rpow_one]
      simp only [hone] at hmix
      rw [integral_congr_ae (Filter.Eventually.of_forall (hnorm q))] at hmix
      have hexp : Real.exp (2 * (1 - q) * t ^ 2
          * (Real.log y₁ ^ 2 / 2 + 15.003 * Real.log y₁ + 34)) ≤ Real.exp (β * t ^ 2) := by
        refine Real.exp_le_exp.2 ?_
        have := mul_le_mul_of_nonneg_right hβ (sq_nonneg t)
        linarith
      have hmix' := le_trans hmix (mul_le_mul_of_nonneg_right hexp hMnn)
      have hpull : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ (2 * (q - 1))
            * (ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2) ∂μ)
          = ρ t * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ (2 * (q - 1))
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2 ∂μ := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
      rw [hpull, mul_assoc]
      exact mul_le_mul_of_nonneg_left hmix' (hρ0 t)
    have hIint : Integrable (fun t => ∫ ω,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ 0) ω‖ ^ (2 * (q - 1))
          * (ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ t) ω‖ ^ 2) ∂μ) (volume.restrict (Set.Icc (-w) w)) :=
      (integrable_uncurry_rpow_mul_weight_normSq_primesIco hX y₀ y₁
        (r := 2 * (q - 1)) (w := w) hc0 hρm hρ0 hρb).integral_prod_right
    calc (∫ t in Set.Icc (-w) w, ∫ ω,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ (2 * (q - 1))
            * (ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ t) ω‖ ^ 2) ∂μ)
        ≤ ∫ t in Set.Icc (-w) w, ρ t * Real.exp (β * t ^ 2) * ∫ ω,
            (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ 2) ^ q ∂μ :=
          setIntegral_mono_on hIint (by exact hρEint.mul_const _) measurableSet_Icc hpt
      _ = (∫ t in Set.Icc (-w) w, ρ t * Real.exp (β * t ^ 2)) * ∫ ω,
            (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ 2) ^ q ∂μ := integral_mul_const _ _
      _ ≤ R * ∫ ω,
            (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
              (shiftLine σ 0) ω‖ ^ 2) ^ q ∂μ := mul_le_mul_of_nonneg_right hρR hMnn

/-! ### The central window -/

/-- `e^{λx} ≤ 1 + λ(e^x - 1)` for `0 ≤ λ ≤ 1`: the convexity of `exp`. -/
lemma exp_mul_le_one_add_mul {l x : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    Real.exp (l * x) ≤ 1 + l * (Real.exp x - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ 0) hl0 (by linarith : 0 ≤ 1 - l)
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  linarith

/-- **The central window's weight against the two-point ratio**:
`∫_{|t|≤w} e^{βt²}dt/(σ²+t²) ≤ π/σ + 2(e^{βw²} - 1)/w` for `σ, w > 0`, `β ≥ 0`.  On the window
`e^{βt²} ≤ 1 + (t/w)²(e^{βw²} - 1)` and `t²/(σ²+t²) ≤ 1`; the first term is
`RMF.setIntegral_inv_sq_add_sq_le`. -/
lemma setIntegral_inv_sq_add_sq_mul_exp_le {σ w β : ℝ} (hσ : 0 < σ) (hw : 0 < w)
    (hβ : 0 ≤ β) :
    (∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2))
      ≤ Real.pi / σ + 2 * (Real.exp (β * w ^ 2) - 1) / w := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (-w) w)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hpos : ∀ t : ℝ, (0 : ℝ) < σ ^ 2 + t ^ 2 := fun t => by positivity
  have hcont : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun t => (hpos t).ne'
  have hw2 : (0 : ℝ) < w ^ 2 := by positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (Real.exp (β * w ^ 2) - 1) / w ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact div_nonneg (by linarith [Real.one_le_exp (mul_nonneg hβ hw2.le)]) hw2.le
  have hpt : ∀ t ∈ Set.Icc (-w) w,
      (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2) ≤ (σ ^ 2 + t ^ 2)⁻¹ + K := by
    intro t ht
    have hsq : t ^ 2 ≤ w ^ 2 := by
      have habs : |t| ≤ w := abs_le.2 ⟨ht.1, ht.2⟩
      calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
        _ ≤ w ^ 2 := pow_le_pow_left₀ (abs_nonneg t) habs 2
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = t ^ 2 / w ^ 2 := ⟨_, rfl⟩
    have hl0 : 0 ≤ l := by rw [hl]; positivity
    have hl1 : l ≤ 1 := by rw [hl, div_le_one hw2]; exact hsq
    have hexp : Real.exp (β * t ^ 2) ≤ 1 + l * (Real.exp (β * w ^ 2) - 1) := by
      have : β * t ^ 2 = l * (β * w ^ 2) := by
        rw [hl]
        field_simp
      rw [this]
      exact exp_mul_le_one_add_mul hl0 hl1
    have hfrac : (σ ^ 2 + t ^ 2)⁻¹ * t ^ 2 ≤ 1 := by
      rw [inv_mul_le_iff₀ (hpos t)]
      nlinarith [sq_nonneg σ]
    calc (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2)
        ≤ (σ ^ 2 + t ^ 2)⁻¹ * (1 + l * (Real.exp (β * w ^ 2) - 1)) :=
          mul_le_mul_of_nonneg_left hexp (inv_nonneg.2 (hpos t).le)
      _ = (σ ^ 2 + t ^ 2)⁻¹ + ((σ ^ 2 + t ^ 2)⁻¹ * t ^ 2) * K := by
          rw [hl, hK]
          field_simp
      _ ≤ (σ ^ 2 + t ^ 2)⁻¹ + 1 * K := by gcongr
      _ = (σ ^ 2 + t ^ 2)⁻¹ + K := by ring
  have hint1 : IntegrableOn (fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2))
      (Set.Icc (-w) w) := (hcont.mul (by fun_prop)).integrableOn_Icc
  have hint2 : IntegrableOn (fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ + K) (Set.Icc (-w) w) :=
    (hcont.add continuous_const).integrableOn_Icc
  calc (∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (β * t ^ 2))
      ≤ ∫ t in Set.Icc (-w) w, ((σ ^ 2 + t ^ 2)⁻¹ + K) :=
        setIntegral_mono_on hint1 hint2 measurableSet_Icc hpt
    _ = (∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹) + ∫ _t in Set.Icc (-w) w, K :=
        integral_add hcont.integrableOn_Icc (integrable_const K)
    _ ≤ Real.pi / σ + 2 * w * K := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        have := setIntegral_inv_sq_add_sq_le hσ hw.le
        have h2 : (w - -w) * K = 2 * w * K := by ring
        linarith
    _ = Real.pi / σ + 2 * (Real.exp (β * w ^ 2) - 1) / w := by
        rw [hK]
        field_simp

/-- **`Z_c`'s window for a block, sharp.**  For `c > 0`, `σ ≥ 0`, `0 < w`, `y₁ ≥ 2`,
`0 ≤ q ≤ ½` and `β ≥ 2(1-q)((log y₁)²/2 + 15.003 log y₁ + 34)`, `F` the product over `y₀ ≤ p < y₁`,
`E[(∫_{|t|≤w}‖F(½+σ+it)/(c+it)‖²dt)^q] ≤ (π/c + 2(e^{βw²} - 1)/w)^q·E‖F(½+σ)‖^{2q}`.  No
restriction on `w`. -/
theorem integral_rpow_setIntegral_normSq_div_shiftLine_primesIco_le_sharp {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {y₀ y₁ : ℕ} (hy : 2 ≤ y₁)
    {σ c w q β : ℝ} (hσ : 0 ≤ σ) (hc : 0 < c) (hw : 0 < w) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2)
    (hβ : 2 * (1 - q) * (Real.log y₁ ^ 2 / 2 + 15.003 * Real.log y₁ + 34) ≤ β) :
    (∫ ω, (∫ t in Set.Icc (-w) w,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ t) ω / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ (Real.pi / c + 2 * (Real.exp (β * w ^ 2) - 1) / w) ^ q
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (-w) w)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hβ0 : 0 ≤ β := by
    have hlogy : (0 : ℝ) ≤ Real.log y₁ :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y₁))
    have : 0 ≤ 2 * (1 - q) * (Real.log y₁ ^ 2 / 2 + 15.003 * Real.log y₁ + 34) := by
      have : 0 ≤ 1 - q := by linarith
      positivity
    linarith
  have hpos : ∀ t : ℝ, (0 : ℝ) < c ^ 2 + t ^ 2 := fun t => by positivity
  have hcont : Continuous fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun t => (hpos t).ne'
  have hden : ∀ t : ℝ, ‖((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = c ^ 2 + t ^ 2 := by
    intro t
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hpt : ∀ (t : ℝ) (ω : Ω),
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (shiftLine σ t) ω / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        = (c ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (shiftLine σ t) ω‖ ^ 2 := by
    intro t ω
    rw [norm_div, div_pow, hden t]
    ring
  simp only [hpt]
  refine integral_rpow_setIntegral_weight_normSq_shiftLine_primesIco_le_sharp (Bd := (c ^ 2)⁻¹)
    (R := Real.pi / c + 2 * (Real.exp (β * w ^ 2) - 1) / w) hX hy hσ hq0 hq hβ
    hcont.measurable (fun t => by positivity) (fun t => ?_) ?_
    (setIntegral_inv_sq_add_sq_mul_exp_le hc hw hβ0)
  · exact (inv_le_inv₀ (hpos t) (by positivity)).2 (by nlinarith [sq_nonneg t])
  · have hb : ∀ t ∈ Set.Icc (-w) w, (c ^ 2 + w ^ 2)⁻¹ ≤ (c ^ 2 + t ^ 2)⁻¹ := by
      intro t ht
      have habs : |t| ≤ w := abs_le.2 ⟨ht.1, ht.2⟩
      have : t ^ 2 ≤ w ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
      exact (inv_le_inv₀ (by positivity) (hpos t)).2 (by linarith)
    calc (0 : ℝ) < 2 * w * (c ^ 2 + w ^ 2)⁻¹ := by positivity
      _ = ∫ _t in Set.Icc (-w) w, (c ^ 2 + w ^ 2)⁻¹ := by
          rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
          ring
      _ ≤ _ := setIntegral_mono_on (by exact integrable_const _)
          (hcont.integrableOn_Icc) measurableSet_Icc hb

/-- **`Z_c`, sharp.**  For `0 ≤ q ≤ ½`, `y ≥ 2`, `σ > 0` and `0 < w`,
`E[(∫_{|t|≤w}‖F_y(½+σ+it)/(σ+it)‖²dt)^q]
  ≤ (π/σ + 2(e^{2(1-q)S₂w²} - 1)/w)^q·E‖F_y(½+σ)‖^{2q}`,
`S₂ = (log y)²/2 + 15.003 log y + 34`: the block `[0, y)`, `c = σ` case of
`RMF.integral_rpow_setIntegral_normSq_div_shiftLine_primesIco_le_sharp`. -/
theorem integral_rpow_setIntegral_normSq_div_shiftLine_le_sharp {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {y : ℕ} (hy : 2 ≤ y) {σ w q : ℝ}
    (hσ : 0 < σ) (hw : 0 < w) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    (∫ ω, (∫ t in Set.Icc (-w) w,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
            (shiftLine σ t) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ (Real.pi / σ + 2 * (Real.exp (2 * (1 - q)
            * (Real.log y ^ 2 / 2 + 15.003 * Real.log y + 34) * w ^ 2) - 1) / w) ^ q
        * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ := by
  have h := integral_rpow_setIntegral_normSq_div_shiftLine_primesIco_le_sharp hX (y₀ := 0) hy
    (σ := σ) (c := σ) hσ.le hσ hw hq0 hq le_rfl
  simpa only [randomEulerProductIco_zero] using h

/-- **The central window with its constant.**  For `0 ≤ q ≤ ½`, `y ≥ 2`, `σ > 0` and
`0 < w`, with `F_{y+1}` the Euler product over `p ≤ y`,

`E[((log y)⁻¹∫_{|t|≤w}‖F_{y+1}(½+σ+it)/(σ+it)‖²dt)^q]
  ≤ ((π/σ + 2(e^{2(1-q)S₂w²} - 1)/w)/log y)^q
    · exp(q(1-2q)(9.0028/log y + 2σ(log y + log 4 + 4) - 3/20))·(log y)^{q(2q-1)}`,

`S₂ = (log(y+1))²/2 + 15.003 log(y+1) + 34`.  At `σ = c/log x`, `x = y^U`, the first factor is
`(πU/c + K₂)^q` with `K₂ = 2(e^{κs₀²} - 1)/s₀`, `s₀ = w log y`, `κ = 2(1-q)S₂/(log y)²`
(`κ → 1 - q` as `y → ∞`).  The second is the sharp moment bound
`RMF.IsRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_log_sharp`. -/
theorem integral_rpow_centralRange_le_sharp {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {σ q w : ℝ} {y : ℕ} (hy : 2 ≤ y) (hσ : 0 < σ)
    (hw : 0 < w) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    (∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Icc (-w) w,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
      ≤ ((Real.pi / σ + 2 * (Real.exp (2 * (1 - q)
            * (Real.log ((y : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((y : ℝ) + 1) + 34)
            * w ^ 2) - 1) / w) / Real.log y) ^ q
        * (Real.exp (q * (1 - 2 * q)
            * (9.0028 / Real.log y + 2 * σ * (Real.log y + Real.log 4 + 4) - 3 / 20))
          * (Real.log y) ^ (q * (2 * q - 1))) := by
  haveI := hY.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hcast : (((y + 1 : ℕ)) : ℝ) = (y : ℝ) + 1 := by push_cast; ring
  have habs : ∀ t : ℝ, ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) = shiftLine σ t := by
    intro t
    rw [shiftLine]
    push_cast
    ring
  simp only [habs]
  have hInn : ∀ ω : Ω, (0 : ℝ) ≤ ∫ t in Set.Icc (-w) w,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
        (shiftLine σ t) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := fun ω =>
    setIntegral_nonneg measurableSet_Icc fun t _ => by positivity
  have hsplit : ∀ ω : Ω, ((Real.log y)⁻¹ * ∫ t in Set.Icc (-w) w,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q
      = ((Real.log y)⁻¹) ^ q * (∫ t in Set.Icc (-w) w,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q := fun ω =>
    Real.mul_rpow (by positivity) (hInn ω)
  simp only [hsplit]
  rw [integral_const_mul]
  have hctr := integral_rpow_setIntegral_normSq_div_shiftLine_le_sharp hY (y := y + 1)
    (by omega) hσ hw hq0 hq
  rw [hcast] at hctr
  have hz : shiftLine σ 0 = (((1 / 2 + σ : ℝ)) : ℂ) := by
    rw [shiftLine]
    norm_num
  rw [hz] at hctr
  have hpf := hRa.integral_norm_randomEulerProduct_shift_rpow_le_log_sharp hσ.le hq0 hq hy
  set W : ℝ := Real.pi / σ + 2 * (Real.exp (2 * (1 - q)
      * (Real.log ((y : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((y : ℝ) + 1) + 34)
      * w ^ 2) - 1) / w with hWdef
  have hW0 : 0 ≤ W := by
    rw [hWdef]
    have hexp : 1 ≤ Real.exp (2 * (1 - q)
        * (Real.log ((y : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((y : ℝ) + 1) + 34) * w ^ 2) := by
      refine Real.one_le_exp ?_
      have h1 : 0 ≤ 1 - q := by linarith
      have h2 : 0 ≤ Real.log ((y : ℝ) + 1) := Real.log_nonneg (by linarith)
      positivity
    have : 0 ≤ 2 * (Real.exp (2 * (1 - q)
        * (Real.log ((y : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((y : ℝ) + 1) + 34) * w ^ 2) - 1)
        / w := div_nonneg (by linarith) hw.le
    positivity
  have hWq : (0 : ℝ) ≤ W ^ q := Real.rpow_nonneg hW0 _
  have hNq : (0 : ℝ) ≤ ((Real.log y)⁻¹) ^ q := Real.rpow_nonneg (by positivity) _
  have hstep := mul_le_mul_of_nonneg_left
    (hctr.trans (mul_le_mul_of_nonneg_left hpf hWq)) hNq
  refine hstep.trans (le_of_eq ?_)
  rw [← mul_assoc, ← Real.mul_rpow (by positivity) hW0, div_eq_mul_inv W, mul_comm W]

end RMF
