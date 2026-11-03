/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.Moments

/-!
# Joint moments of random Euler products

A joint moment `E ∏_{j ∈ J} ‖F_y(s_j)‖ ^ (2 q_j)` factors into local moments (over a range of
primes, `RMF.integral_prod_norm_randomEulerProductIco_rpow_compMult`).  This file expands a local
moment.

## The multi-factor expansion

Each local factor is `(1 - W_j) ^ (-q_j)` with `W_j` small, so the local moment is the
expectation of a product of such powers.  Expanding each factor to second order and
multiplying gives, with

`S = ∑_{j ∈ J} α_j a_j` and `V = ∑_{j ∈ J} α_j a_j ^ 2`,

`∏_{j ∈ J} (1 - a_j) ^ (-α_j) = 1 + S + S ^ 2 / 2 + V / 2 + O((max_j |a_j|) ^ 3)`

(`RMF.taylorPoly`, `RMF.exists_taylor_bound_prod`).  The cross terms `∑_{j < k} α_j α_k a_j a_k`
collapse into `(S ^ 2 - ∑_j α_j ^ 2 a_j ^ 2) / 2`, and the rest of the diagonal is `V / 2`.
The point of this symmetric form is that it needs no ordering of the index type, so `J` may be
an arbitrary `Finset ι`.
-/

open Finset MeasureTheory

namespace RMF

variable {ι : Type*}

/-- The degree-two Taylor polynomial of `∏_{j ∈ J} (1 - a_j) ^ (-α_j)`, in the symmetric form
`1 + S + S ^ 2 / 2 + V / 2` with `S = ∑_{j ∈ J} α_j a_j` and `V = ∑_{j ∈ J} α_j a_j ^ 2`. -/
noncomputable def taylorPoly (J : Finset ι) (α a : ι → ℝ) : ℝ :=
  1 + (∑ j ∈ J, α j * a j) + (∑ j ∈ J, α j * a j) ^ 2 / 2 + (∑ j ∈ J, α j * a j ^ 2) / 2

@[simp] lemma taylorPoly_empty (α a : ι → ℝ) : taylorPoly (∅ : Finset ι) α a = 1 := by
  simp [taylorPoly]

/-! ### The product as an exponential

Rather than inducting on `J`, note that each factor is `exp (α_j L(a_j))` with
`L a = -log (1 - a)`, so the whole product is `exp (∑_j α_j L(a_j))`.  Feeding the Taylor
expansion of `L` into that of `exp` — both already proved for one variable — gives the
multi-factor bound directly, with `Finset.abs_sum_le_sum_abs` doing all the work of the
induction.
-/

/-- Each factor is an exponential. -/
lemma one_sub_rpow_neg_eq_exp {α a : ℝ} (ha : |a| ≤ 1 / 2) :
    (1 - a) ^ (-α) = Real.exp (α * (-Real.log (1 - a))) := by
  obtain ⟨h1, h2⟩ := abs_le.mp ha
  rw [Real.rpow_def_of_pos (by linarith)]
  congr 1
  ring

/-- Hence the product is the exponential of a sum. -/
lemma prod_one_sub_rpow_neg_eq_exp (J : Finset ι) {α a : ι → ℝ}
    (ha : ∀ j ∈ J, |a j| ≤ 1 / 2) :
    ∏ j ∈ J, (1 - a j) ^ (-α j) = Real.exp (∑ j ∈ J, α j * (-Real.log (1 - a j))) := by
  rw [Real.exp_sum]
  exact Finset.prod_congr rfl fun j hj => one_sub_rpow_neg_eq_exp (ha j hj)

/-- The exponent `u = ∑_j α_j L(a_j)` is within `O(δ ^ 3)` of `S + V / 2`. -/
lemma abs_sum_mul_negLog_sub_le {Q : ℝ} (hQ : 0 ≤ Q) (J : Finset ι) {α a : ι → ℝ}
    (hα : ∀ j ∈ J, |α j| ≤ Q) {δ : ℝ} (hδ2 : δ ≤ 1 / 2) (ha : ∀ j ∈ J, |a j| ≤ δ) :
    |(∑ j ∈ J, α j * (-Real.log (1 - a j)))
        - ((∑ j ∈ J, α j * a j) + (∑ j ∈ J, α j * a j ^ 2) / 2)|
      ≤ 2 * Q * J.card * δ ^ 3 := by
  have hterm : ∀ j ∈ J,
      |α j * (-Real.log (1 - a j)) - (α j * a j + α j * a j ^ 2 / 2)| ≤ 2 * Q * δ ^ 3 := by
    intro j hj
    have haj : |a j| ≤ 1 / 2 := (ha j hj).trans hδ2
    have hL := abs_neg_log_one_sub_sub_le haj
    have hcube : |a j| ^ 3 ≤ δ ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) (ha j hj) 3
    have hrw : α j * (-Real.log (1 - a j)) - (α j * a j + α j * a j ^ 2 / 2)
        = α j * ((-Real.log (1 - a j)) - (a j + a j ^ 2 / 2)) := by ring
    rw [hrw, abs_mul]
    calc |α j| * |(-Real.log (1 - a j)) - (a j + a j ^ 2 / 2)|
        ≤ Q * (2 * |a j| ^ 3) := mul_le_mul (hα j hj) hL (abs_nonneg _) hQ
      _ ≤ Q * (2 * δ ^ 3) := by
          have : (0:ℝ) ≤ Q := hQ
          nlinarith
      _ = 2 * Q * δ ^ 3 := by ring
  have hsplit : (∑ j ∈ J, α j * (-Real.log (1 - a j)))
      - ((∑ j ∈ J, α j * a j) + (∑ j ∈ J, α j * a j ^ 2) / 2)
      = ∑ j ∈ J, (α j * (-Real.log (1 - a j)) - (α j * a j + α j * a j ^ 2 / 2)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [hsplit]
  calc |∑ j ∈ J, (α j * (-Real.log (1 - a j)) - (α j * a j + α j * a j ^ 2 / 2))|
      ≤ ∑ j ∈ J, |α j * (-Real.log (1 - a j)) - (α j * a j + α j * a j ^ 2 / 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ J, 2 * Q * δ ^ 3 := Finset.sum_le_sum hterm
    _ = 2 * Q * J.card * δ ^ 3 := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- A crude bound on the exponent. -/
lemma abs_sum_mul_negLog_le {Q : ℝ} (hQ : 0 ≤ Q) (J : Finset ι) {α a : ι → ℝ}
    (hα : ∀ j ∈ J, |α j| ≤ Q) {δ : ℝ} (hδ2 : δ ≤ 1 / 2) (ha : ∀ j ∈ J, |a j| ≤ δ) :
    |∑ j ∈ J, α j * (-Real.log (1 - a j))| ≤ 2 * Q * J.card * δ := by
  have hterm : ∀ j ∈ J, |α j * (-Real.log (1 - a j))| ≤ 2 * Q * δ := by
    intro j hj
    have haj : |a j| ≤ 1 / 2 := (ha j hj).trans hδ2
    have hL := abs_neg_log_one_sub_sub_le haj
    have h1 : |(-Real.log (1 - a j))| ≤ 2 * |a j| := by
      have h2 : |a j + a j ^ 2 / 2| ≤ |a j| + |a j| ^ 2 / 2 := by
        refine (abs_add_le _ _).trans_eq ?_
        rw [abs_div, abs_pow, abs_two]
      have h3 := (abs_sub_abs_le_abs_sub (-Real.log (1 - a j)) (a j + a j ^ 2 / 2)).trans hL
      have h4 : |a j| ^ 2 ≤ |a j| / 2 := by nlinarith [abs_nonneg (a j), haj]
      have h5 : |a j| ^ 3 ≤ |a j| / 4 := by nlinarith [abs_nonneg (a j), haj]
      linarith [abs_nonneg (a j)]
    rw [abs_mul]
    calc |α j| * |(-Real.log (1 - a j))| ≤ Q * (2 * |a j|) :=
          mul_le_mul (hα j hj) h1 (abs_nonneg _) hQ
      _ ≤ Q * (2 * δ) := by nlinarith [ha j hj]
      _ = 2 * Q * δ := by ring
  calc |∑ j ∈ J, α j * (-Real.log (1 - a j))|
      ≤ ∑ j ∈ J, |α j * (-Real.log (1 - a j))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ J, 2 * Q * δ := Finset.sum_le_sum hterm
    _ = 2 * Q * J.card * δ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- And a crude bound on `S`, needed to compare `u ^ 2` with `S ^ 2`. -/
lemma abs_sum_mul_le {Q : ℝ} (hQ : 0 ≤ Q) (J : Finset ι) {α a : ι → ℝ}
    (hα : ∀ j ∈ J, |α j| ≤ Q) {δ : ℝ} (ha : ∀ j ∈ J, |a j| ≤ δ) :
    |∑ j ∈ J, α j * a j| ≤ Q * J.card * δ := by
  have hterm : ∀ j ∈ J, |α j * a j| ≤ Q * δ := by
    intro j hj
    rw [abs_mul]
    exact mul_le_mul (hα j hj) (ha j hj) (abs_nonneg _) hQ
  calc |∑ j ∈ J, α j * a j| ≤ ∑ j ∈ J, |α j * a j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ J, Q * δ := Finset.sum_le_sum hterm
    _ = Q * J.card * δ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

lemma abs_sum_mul_sq_le {Q : ℝ} (hQ : 0 ≤ Q) (J : Finset ι) {α a : ι → ℝ}
    (hα : ∀ j ∈ J, |α j| ≤ Q) {δ : ℝ} (ha : ∀ j ∈ J, |a j| ≤ δ) :
    |∑ j ∈ J, α j * a j ^ 2| ≤ Q * J.card * δ ^ 2 := by
  have hterm : ∀ j ∈ J, |α j * a j ^ 2| ≤ Q * δ ^ 2 := by
    intro j hj
    rw [abs_mul, abs_pow]
    exact mul_le_mul (hα j hj) (pow_le_pow_left₀ (abs_nonneg _) (ha j hj) 2)
      (by positivity) hQ
  calc |∑ j ∈ J, α j * a j ^ 2| ≤ ∑ j ∈ J, |α j * a j ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ J, Q * δ ^ 2 := Finset.sum_le_sum hterm
    _ = Q * J.card * δ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- A crude bound on the quadratic `1 + S + S ^ 2 / 2 + V / 2`, proved in a small context so
that `linarith` stays fast. -/
lemma abs_one_add_add_sq_add_le {M S V : ℝ} (hM : 0 ≤ M) (hS : |S| ≤ M / 2) (hV : |V| ≤ M / 4) :
    |1 + S + S ^ 2 / 2 + V / 2| ≤ 1 + M / 2 + M ^ 2 / 8 + M / 8 := by
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  obtain ⟨hV1, hV2⟩ := abs_le.mp hV
  have hsq : S ^ 2 ≤ M ^ 2 / 4 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg S]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg S]

/-- The coarse regime of `RMF.exists_taylor_bound_prod`: once `2 M δ > 1`, the quantity
`δ ^ 3` is bounded below, so the crude bounds on `exp u` and on the quadratic suffice.
Stated separately so that it is proved in a small context. -/
lemma abs_exp_sub_quadratic_le {M u S V δ : ℝ} (hM : 0 ≤ M) (hδ2 : δ ≤ 1 / 2)
    (hu : |u| ≤ 2 * M * δ) (hS : |S| ≤ M * δ) (hV : |V| ≤ M * δ ^ 2)
    (hbig : 1 < 2 * M * δ) :
    |Real.exp u - (1 + S + S ^ 2 / 2 + V / 2)|
      ≤ (Real.exp M + (1 + M / 2 + M ^ 2 / 8 + M / 8)) * (2 * M) ^ 3 * δ ^ 3 := by
  have hMδ : 0 < 2 * M * δ := lt_trans zero_lt_one hbig
  have hδpos : 0 < δ := by nlinarith
  have hSb : |S| ≤ M / 2 := by nlinarith [abs_nonneg S]
  have hVb : |V| ≤ M / 4 := by nlinarith [abs_nonneg V, sq_nonneg δ]
  have hexpb : |Real.exp u| ≤ Real.exp M := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self u).trans (hu.trans (by nlinarith)))
  have hquad := abs_one_add_add_sq_add_le hM hSb hVb
  have hsum : |Real.exp u - (1 + S + S ^ 2 / 2 + V / 2)|
      ≤ Real.exp M + (1 + M / 2 + M ^ 2 / 8 + M / 8) := by
    linarith [abs_sub (Real.exp u) (1 + S + S ^ 2 / 2 + V / 2)]
  have hone : (1:ℝ) ≤ (2 * M * δ) ^ 3 := one_le_pow₀ hbig.le
  have hpos : (0:ℝ) < Real.exp M + (1 + M / 2 + M ^ 2 / 8 + M / 8) := by positivity
  calc |Real.exp u - (1 + S + S ^ 2 / 2 + V / 2)|
      ≤ Real.exp M + (1 + M / 2 + M ^ 2 / 8 + M / 8) := hsum
    _ = (Real.exp M + (1 + M / 2 + M ^ 2 / 8 + M / 8)) * 1 := (mul_one _).symm
    _ ≤ (Real.exp M + (1 + M / 2 + M ^ 2 / 8 + M / 8)) * (2 * M * δ) ^ 3 :=
        mul_le_mul_of_nonneg_left hone hpos.le
    _ = (Real.exp M + (1 + M / 2 + M ^ 2 / 8 + M / 8)) * (2 * M) ^ 3 * δ ^ 3 := by ring

/-- **The multi-factor expansion.**  For `|α j| ≤ Q` and `|a j| ≤ δ ≤ 1/2`,
`∏_{j ∈ J} (1 - a j) ^ (-α j) = taylorPoly J α a + O(δ ^ 3)`, with a constant depending only on
`Q` and `J`.  The proof feeds the Taylor expansion of `-log (1 - a)` into that of `exp`, with the
sum over `J` handled by the triangle inequality. -/
theorem exists_taylor_bound_prod {Q : ℝ} (hQ : 0 ≤ Q) (J : Finset ι) :
    ∃ C > 0, ∀ (α a : ι → ℝ) (δ : ℝ), (∀ j ∈ J, |α j| ≤ Q) → 0 ≤ δ → δ ≤ 1 / 2 →
      (∀ j ∈ J, |a j| ≤ δ) →
      |∏ j ∈ J, (1 - a j) ^ (-α j) - taylorPoly J α a| ≤ C * δ ^ 3 := by
  set n : ℝ := (J.card : ℝ) with hn
  have hn0 : 0 ≤ n := by positivity
  have hQn : 0 ≤ Q * n := mul_nonneg hQ hn0
  set B : ℝ := 1 + Q * n / 2 + (Q * n) ^ 2 / 8 + Q * n / 8 with hB
  have hB0 : 0 < B := by rw [hB]; positivity
  refine ⟨1 + 2 * Q * n + (2 * Q * n) ^ 3 + 9 / 4 * (Q * n) ^ 2
    + (Real.exp (Q * n) + B) * (2 * Q * n) ^ 3, by positivity, ?_⟩
  intro α a δ hα hδ0 hδ2 ha
  have hahalf : ∀ j ∈ J, |a j| ≤ 1 / 2 := fun j hj => (ha j hj).trans hδ2
  set u : ℝ := ∑ j ∈ J, α j * (-Real.log (1 - a j)) with hu
  set S : ℝ := ∑ j ∈ J, α j * a j with hS
  set V : ℝ := ∑ j ∈ J, α j * a j ^ 2 with hV
  have hprod : ∏ j ∈ J, (1 - a j) ^ (-α j) = Real.exp u :=
    prod_one_sub_rpow_neg_eq_exp J hahalf
  have hT : taylorPoly J α a = 1 + S + S ^ 2 / 2 + V / 2 := rfl
  have huSV : |u - (S + V / 2)| ≤ 2 * Q * n * δ ^ 3 :=
    abs_sum_mul_negLog_sub_le hQ J hα hδ2 ha
  have huK : |u| ≤ 2 * Q * n * δ := abs_sum_mul_negLog_le hQ J hα hδ2 ha
  have hSb : |S| ≤ Q * n * δ := abs_sum_mul_le hQ J hα ha
  have hVb : |V| ≤ Q * n * δ ^ 2 := abs_sum_mul_sq_le hQ J hα ha
  have hcube : (0:ℝ) ≤ δ ^ 3 := by positivity
  rw [hprod, hT]
  by_cases hsmall : 2 * Q * n * δ ≤ 1
  · -- the exponent is at most `1`, so the two expansions compose
    have hexp : |Real.exp u - (1 + u + u ^ 2 / 2)| ≤ |u| ^ 3 :=
      abs_exp_sub_taylor_le (huK.trans hsmall)
    have hexp' : |Real.exp u - (1 + u + u ^ 2 / 2)| ≤ (2 * Q * n) ^ 3 * δ ^ 3 := by
      refine hexp.trans ?_
      calc |u| ^ 3 ≤ (2 * Q * n * δ) ^ 3 := pow_le_pow_left₀ (abs_nonneg u) huK 3
        _ = (2 * Q * n) ^ 3 * δ ^ 3 := by ring
    have huS : |u - S| ≤ 3 / 2 * (Q * n) * δ ^ 2 := by
      have h2 : |u - S| ≤ |u - (S + V / 2)| + |V| / 2 := by
        have h1 : u - S = (u - (S + V / 2)) + V / 2 := by ring
        rw [h1]
        refine (abs_add_le _ _).trans_eq ?_
        rw [abs_div, abs_two]
      have h3 : 2 * Q * n * δ ^ 3 ≤ Q * n * δ ^ 2 := by
        have h := mul_nonneg (mul_nonneg hQn (sq_nonneg δ)) (by linarith : (0:ℝ) ≤ 1 - 2 * δ)
        nlinarith [h]
      linarith
    have huplusS : |u + S| ≤ 3 * (Q * n) * δ := by
      have h := abs_add_le u S
      linarith
    have hsq : |u ^ 2 - S ^ 2| ≤ 9 / 2 * (Q * n) ^ 2 * δ ^ 3 := by
      have h1 : u ^ 2 - S ^ 2 = (u - S) * (u + S) := by ring
      rw [h1, abs_mul]
      calc |u - S| * |u + S| ≤ (3 / 2 * (Q * n) * δ ^ 2) * (3 * (Q * n) * δ) :=
            mul_le_mul huS huplusS (abs_nonneg _) (by positivity)
        _ = 9 / 2 * (Q * n) ^ 2 * δ ^ 3 := by ring
    have hquad : |(1 + u + u ^ 2 / 2) - (1 + S + S ^ 2 / 2 + V / 2)|
        ≤ 2 * Q * n * δ ^ 3 + 9 / 4 * (Q * n) ^ 2 * δ ^ 3 := by
      have h1 : (1 + u + u ^ 2 / 2) - (1 + S + S ^ 2 / 2 + V / 2)
          = (u - (S + V / 2)) + (u ^ 2 - S ^ 2) / 2 := by ring
      rw [h1]
      have h2 : |(u - (S + V / 2)) + (u ^ 2 - S ^ 2) / 2|
          ≤ |u - (S + V / 2)| + |u ^ 2 - S ^ 2| / 2 := by
        refine (abs_add_le _ _).trans_eq ?_
        rw [abs_div, abs_two]
      linarith
    have htri : |Real.exp u - (1 + S + S ^ 2 / 2 + V / 2)|
        ≤ |Real.exp u - (1 + u + u ^ 2 / 2)|
          + |(1 + u + u ^ 2 / 2) - (1 + S + S ^ 2 / 2 + V / 2)| := by
      exact abs_sub_le _ (1 + u + u ^ 2 / 2) _
    have hrest : 0 ≤ (1 + (Real.exp (Q * n) + B) * (2 * Q * n) ^ 3) * δ ^ 3 := by positivity
    linarith [htri, hexp', hquad, hrest]
  · -- `δ` is bounded below, so the crude bounds suffice
    rw [not_le] at hsmall
    have huK' : |u| ≤ 2 * (Q * n) * δ := by rw [← mul_assoc]; exact huK
    have hsmall' : 1 < 2 * (Q * n) * δ := by rw [← mul_assoc]; exact hsmall
    have hcrude := abs_exp_sub_quadratic_le hQn hδ2 huK' hSb hVb hsmall'
    have hrest : 0 ≤ (1 + 2 * Q * n + (2 * Q * n) ^ 3 + 9 / 4 * (Q * n) ^ 2) * δ ^ 3 := by
      positivity
    rw [hB]
    linarith [hcrude, hrest]

/-! ### The expectation of the expansion

The linear part of the expansion aggregates: `∑_j q_j W(w_j) = W(Ω) + (‖Ω‖ ^ 2 - P)` where
`Ω = ∑_j q_j w_j` and `P = ∑_j q_j ‖w_j‖ ^ 2`.  So the whole polynomial integrates in terms of
the two one-point moments, and the answer is `1 + ‖Ω‖ ^ 2` up to fourth-order terms.
-/

/-- Real coefficients pull out of a real part. -/
lemma sum_re_mul (J : Finset ι) (q : ι → ℝ) (w : ι → ℂ) (z : ℂ) :
    ∑ j ∈ J, q j * (z * w j).re = (z * ∑ j ∈ J, (q j : ℂ) * w j).re := by
  rw [Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show z * ((q j : ℂ) * w j) = (q j : ℂ) * (z * w j) by ring]
  simp [Complex.mul_re]

/-- The linear part of the expansion is again a local variable, at the aggregated point. -/
lemma sum_mul_localW (J : Finset ι) (q : ι → ℝ) (w : ι → ℂ) (z : ℂ) :
    ∑ j ∈ J, q j * localW (w j) z
      = localW (∑ j ∈ J, (q j : ℂ) * w j) z
        + (‖∑ j ∈ J, (q j : ℂ) * w j‖ ^ 2 - ∑ j ∈ J, q j * ‖w j‖ ^ 2) := by
  simp only [localW]
  have h : ∑ j ∈ J, q j * (2 * (z * w j).re - ‖w j‖ ^ 2)
      = 2 * (∑ j ∈ J, q j * (z * w j).re) - ∑ j ∈ J, q j * ‖w j‖ ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h, sum_re_mul]
  ring

/-- **The expectation of the expansion.**  `E taylorPoly = 1 + ‖Ω‖ ^ 2 + P ^ 2 / 2 + R / 2`, where
`Ω = ∑_j q_j w_j`, `P = ∑_j q_j ‖w_j‖ ^ 2` and `R = ∑_j q_j ‖w_j‖ ^ 4`; the last two terms are
fourth order in the `w`'s. -/
theorem integral_taylorPoly_localW (J : Finset ι) (q : ι → ℝ) (w : ι → ℂ) :
    (∫ z, taylorPoly J q (fun j => localW (w j) z) ∂steinhausLaw)
      = 1 + ‖∑ j ∈ J, (q j : ℂ) * w j‖ ^ 2
        + (∑ j ∈ J, q j * ‖w j‖ ^ 2) ^ 2 / 2 + (∑ j ∈ J, q j * ‖w j‖ ^ 4) / 2 := by
  set Ω : ℂ := ∑ j ∈ J, (q j : ℂ) * w j with hΩ
  set P : ℝ := ∑ j ∈ J, q j * ‖w j‖ ^ 2 with hP
  set c : ℝ := ‖Ω‖ ^ 2 - P with hc
  -- rewrite the integrand in terms of the aggregated local variable
  have hS : ∀ z, ∑ j ∈ J, q j * localW (w j) z = localW Ω z + c := fun z => sum_mul_localW J q w z
  have hV : ∀ z, ∑ j ∈ J, q j * (localW (w j) z) ^ 2
      = ∑ j ∈ J, q j * (localW (w j) z) ^ 2 := fun _ => rfl
  have hpt : ∀ z, taylorPoly J q (fun j => localW (w j) z)
      = 1 + (localW Ω z + c) + (localW Ω z + c) ^ 2 / 2
        + (∑ j ∈ J, q j * (localW (w j) z) ^ 2) / 2 := by
    intro z
    rw [taylorPoly, hS z]
  simp_rw [hpt]
  -- integrability of the three pieces
  have hI1 : Integrable (fun z : ℂ => 1 + (localW Ω z + c)) steinhausLaw :=
    (integrable_const _).add ((integrable_localW Ω).add (integrable_const _))
  have hI2 : Integrable (fun z : ℂ => (localW Ω z + c) ^ 2 / 2) steinhausLaw := by
    have h : ∀ z : ℂ, (localW Ω z + c) ^ 2 / 2
        = (localW Ω z ^ 2 + 2 * c * localW Ω z + c ^ 2) / 2 := fun z => by ring
    simp_rw [h]
    exact ((((integrable_localW_sq Ω).add ((integrable_localW Ω).const_mul (2 * c))).add
      (integrable_const _)).div_const 2)
  have hI3 : Integrable
      (fun z : ℂ => (∑ j ∈ J, q j * (localW (w j) z) ^ 2) / 2) steinhausLaw :=
    (integrable_finsetSum _ fun j _ => (integrable_localW_sq (w j)).const_mul (q j)).div_const 2
  have hI12 : Integrable
      (fun z : ℂ => 1 + (localW Ω z + c) + (localW Ω z + c) ^ 2 / 2) steinhausLaw := hI1.add hI2
  rw [integral_add hI12 hI3, integral_add hI1 hI2]
  -- the three integrals
  have e1 : (∫ z, (1 + (localW Ω z + c)) ∂steinhausLaw) = 1 + (-‖Ω‖ ^ 2 + c) := by
    have hA : Integrable (fun z : ℂ => localW Ω z + c) steinhausLaw :=
      (integrable_localW Ω).add (integrable_const _)
    rw [integral_add (integrable_const _) hA,
      integral_add (integrable_localW Ω) (integrable_const _), integral_localW, integral_const,
      integral_const]
    simp
  have e2 : (∫ z, (localW Ω z + c) ^ 2 / 2 ∂steinhausLaw)
      = ((2 * ‖Ω‖ ^ 2 + ‖Ω‖ ^ 4) + 2 * c * (-‖Ω‖ ^ 2) + c ^ 2) / 2 := by
    have h : ∀ z : ℂ, (localW Ω z + c) ^ 2 / 2
        = (localW Ω z ^ 2 + 2 * c * localW Ω z + c ^ 2) / 2 := fun z => by ring
    simp_rw [h]
    have hB : Integrable (fun z : ℂ => localW Ω z ^ 2 + 2 * c * localW Ω z) steinhausLaw :=
      (integrable_localW_sq Ω).add ((integrable_localW Ω).const_mul (2 * c))
    rw [integral_div, integral_add hB (integrable_const _),
      integral_add (integrable_localW_sq Ω) ((integrable_localW Ω).const_mul (2 * c)),
      integral_const_mul, integral_localW_sq, integral_localW, integral_const]
    simp
  have e3 : (∫ z, (∑ j ∈ J, q j * (localW (w j) z) ^ 2) / 2 ∂steinhausLaw)
      = (∑ j ∈ J, q j * (2 * ‖w j‖ ^ 2 + ‖w j‖ ^ 4)) / 2 := by
    rw [integral_div, integral_finsetSum _ fun j _ => (integrable_localW_sq (w j)).const_mul (q j)]
    simp_rw [integral_const_mul, integral_localW_sq]
  rw [e1, e2, e3, hc]
  have hsplit : ∑ j ∈ J, q j * (2 * ‖w j‖ ^ 2 + ‖w j‖ ^ 4)
      = 2 * P + ∑ j ∈ J, q j * ‖w j‖ ^ 4 := by
    rw [hP, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  ring

lemma integrable_taylorPoly_localW (J : Finset ι) (q : ι → ℝ) (w : ι → ℂ) :
    Integrable (fun z => taylorPoly J q (fun j => localW (w j) z)) steinhausLaw := by
  set Ω : ℂ := ∑ j ∈ J, (q j : ℂ) * w j with hΩ
  set c : ℝ := ‖Ω‖ ^ 2 - ∑ j ∈ J, q j * ‖w j‖ ^ 2 with hc
  have hpt : ∀ z, taylorPoly J q (fun j => localW (w j) z)
      = 1 + (localW Ω z + c) + (localW Ω z + c) ^ 2 / 2
        + (∑ j ∈ J, q j * (localW (w j) z) ^ 2) / 2 := by
    intro z
    rw [taylorPoly, sum_mul_localW J q w z]
  simp_rw [hpt]
  have hI1 : Integrable (fun z : ℂ => 1 + (localW Ω z + c)) steinhausLaw :=
    (integrable_const _).add ((integrable_localW Ω).add (integrable_const _))
  have hI2 : Integrable (fun z : ℂ => (localW Ω z + c) ^ 2 / 2) steinhausLaw := by
    have h : ∀ z : ℂ, (localW Ω z + c) ^ 2 / 2
        = (localW Ω z ^ 2 + 2 * c * localW Ω z + c ^ 2) / 2 := fun z => by ring
    simp_rw [h]
    exact ((((integrable_localW_sq Ω).add ((integrable_localW Ω).const_mul (2 * c))).add
      (integrable_const _)).div_const 2)
  have hI3 : Integrable
      (fun z : ℂ => (∑ j ∈ J, q j * (localW (w j) z) ^ 2) / 2) steinhausLaw :=
    (integrable_finsetSum _ fun j _ => (integrable_localW_sq (w j)).const_mul (q j)).div_const 2
  have hI12 : Integrable
      (fun z : ℂ => 1 + (localW Ω z + c) + (localW Ω z + c) ^ 2 / 2) steinhausLaw := hI1.add hI2
  exact hI12.add hI3

/-- **The joint local expansion for the Steinhaus law.**  For `0 ≤ q_j ≤ Q` and `‖w_j‖ ≤ δ ≤ 1/5`,
`E ∏_j ‖(1 - z w_j)⁻¹‖ ^ (2 q_j) = 1 + ‖∑_j q_j w_j‖ ^ 2 + O(δ ^ 3)`, with a constant depending
only on `Q` and `J`.  The quadratic form is a perfect square (the field is Gaussian to leading
order), and its polarization `∑_{j,k} q_j q_k Re (w_j conj w_k)` becomes the log-correlated kernel
after summing over the primes. -/
theorem exists_local_expansion_prod_steinhausLaw {Q : ℝ} (hQ : 0 ≤ Q) (J : Finset ι) :
    ∃ C > 0, ∀ (q : ι → ℝ) (w : ι → ℂ) (δ : ℝ), (∀ j ∈ J, q j ∈ Set.Icc 0 Q) →
      0 ≤ δ → δ ≤ 1 / 5 → (∀ j ∈ J, ‖w j‖ ≤ δ) →
      |(∫ z, ∏ j ∈ J, ‖(1 - z * w j)⁻¹‖ ^ (2 * q j) ∂steinhausLaw)
        - (1 + ‖∑ j ∈ J, (q j : ℂ) * w j‖ ^ 2)| ≤ C * δ ^ 3 := by
  obtain ⟨C₀, hC₀, htaylor⟩ := exists_taylor_bound_prod hQ J
  set n : ℝ := (J.card : ℝ) with hn
  have hn0 : 0 ≤ n := by positivity
  refine ⟨11 * C₀ + (Q * n) ^ 2 / 10 + Q * n / 10, by positivity, ?_⟩
  intro q w δ hq hδ0 hδ5 hw
  have hqQ : ∀ j ∈ J, |q j| ≤ Q := fun j hj => by
    rw [abs_of_nonneg (hq j hj).1]; exact (hq j hj).2
  have hw1 : ∀ j ∈ J, ‖w j‖ < 1 := fun j hj => lt_of_le_of_lt (hw j hj) (by linarith)
  set δ' : ℝ := 11 * δ / 5 with hδ'
  have hδ'0 : 0 ≤ δ' := by rw [hδ']; positivity
  have hδ'2 : δ' ≤ 1 / 2 := by rw [hδ']; linarith
  -- the integrand equals a product of powers, and the expansion applies to it
  have hae : ∀ᵐ z ∂steinhausLaw,
      |(∏ j ∈ J, ‖(1 - z * w j)⁻¹‖ ^ (2 * q j))
        - taylorPoly J q (fun j => localW (w j) z)| ≤ C₀ * δ' ^ 3 := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    have heq : (∏ j ∈ J, ‖(1 - z * w j)⁻¹‖ ^ (2 * q j))
        = ∏ j ∈ J, (1 - localW (w j) z) ^ (-q j) :=
      Finset.prod_congr rfl fun j hj => norm_inv_one_sub_rpow_eq (q j) hz (hw1 j hj)
    have hWb : ∀ j ∈ J, |localW (w j) z| ≤ δ' := by
      intro j hj
      have hre : |(z * w j).re| ≤ ‖w j‖ :=
        (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul])
      have h2 : |localW (w j) z| ≤ 2 * ‖w j‖ + ‖w j‖ ^ 2 := by
        rw [localW]
        have := abs_add_le (2 * (z * w j).re) (-‖w j‖ ^ 2)
        rw [abs_mul, abs_neg, abs_two, abs_pow, abs_of_nonneg (norm_nonneg (w j))] at this
        simpa [sub_eq_add_neg] using this.trans (by linarith)
      have hwj := hw j hj
      have hsq : ‖w j‖ ^ 2 ≤ δ / 5 := by nlinarith [norm_nonneg (w j)]
      rw [hδ']; linarith
    rw [heq]
    exact htaylor q (fun j => localW (w j) z) δ' hqQ hδ'0 hδ'2 hWb
  -- integrability
  have hTint := integrable_taylorPoly_localW J q w
  have hmeas : AEStronglyMeasurable
      (fun z => ∏ j ∈ J, ‖(1 - z * w j)⁻¹‖ ^ (2 * q j)) steinhausLaw := by
    refine Finset.aestronglyMeasurable_fun_prod _ fun j hj => ?_
    have h2q : (0:ℝ) ≤ 2 * q j := by linarith [(hq j hj).1]
    exact aestronglyMeasurable_localIntegrand (hw1 j hj) (2 * q j)
  have hdiff : Integrable
      (fun z => (∏ j ∈ J, ‖(1 - z * w j)⁻¹‖ ^ (2 * q j))
        - taylorPoly J q (fun j => localW (w j) z)) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw (hmeas.sub hTint.1) (C₀ * δ' ^ 3) <| by
      filter_upwards [hae] with z hz
      rwa [Real.norm_eq_abs]
  have hPint : Integrable (fun z => ∏ j ∈ J, ‖(1 - z * w j)⁻¹‖ ^ (2 * q j)) steinhausLaw := by
    have h := hdiff.add hTint
    simpa only [Pi.add_def, sub_add_cancel] using h
  -- the two halves of the error
  have h1 : |(∫ z, ∏ j ∈ J, ‖(1 - z * w j)⁻¹‖ ^ (2 * q j) ∂steinhausLaw)
      - ∫ z, taylorPoly J q (fun j => localW (w j) z) ∂steinhausLaw| ≤ C₀ * δ' ^ 3 := by
    rw [← integral_sub hPint hTint]
    have key := norm_integral_le_of_norm_le_const (μ := steinhausLaw) (C := C₀ * δ' ^ 3)
      (f := fun z => (∏ j ∈ J, ‖(1 - z * w j)⁻¹‖ ^ (2 * q j))
        - taylorPoly J q (fun j => localW (w j) z))
      (by filter_upwards [hae] with z hz; rwa [Real.norm_eq_abs])
    rw [Real.norm_eq_abs] at key
    simpa using key
  have hP : |∑ j ∈ J, q j * ‖w j‖ ^ 2| ≤ Q * n * δ ^ 2 := by
    have hterm : ∀ j ∈ J, |q j * ‖w j‖ ^ 2| ≤ Q * δ ^ 2 := by
      intro j hj
      rw [abs_mul, abs_pow, abs_of_nonneg (norm_nonneg _)]
      exact mul_le_mul (hqQ j hj) (pow_le_pow_left₀ (norm_nonneg _) (hw j hj) 2)
        (by positivity) hQ
    calc |∑ j ∈ J, q j * ‖w j‖ ^ 2| ≤ ∑ j ∈ J, |q j * ‖w j‖ ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ J, Q * δ ^ 2 := Finset.sum_le_sum hterm
      _ = Q * n * δ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hR : |∑ j ∈ J, q j * ‖w j‖ ^ 4| ≤ Q * n * δ ^ 4 := by
    have hterm : ∀ j ∈ J, |q j * ‖w j‖ ^ 4| ≤ Q * δ ^ 4 := by
      intro j hj
      rw [abs_mul, abs_pow, abs_of_nonneg (norm_nonneg _)]
      exact mul_le_mul (hqQ j hj) (pow_le_pow_left₀ (norm_nonneg _) (hw j hj) 4)
        (by positivity) hQ
    calc |∑ j ∈ J, q j * ‖w j‖ ^ 4| ≤ ∑ j ∈ J, |q j * ‖w j‖ ^ 4| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ J, Q * δ ^ 4 := Finset.sum_le_sum hterm
      _ = Q * n * δ ^ 4 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have h2 : |(∫ z, taylorPoly J q (fun j => localW (w j) z) ∂steinhausLaw)
      - (1 + ‖∑ j ∈ J, (q j : ℂ) * w j‖ ^ 2)|
      ≤ ((Q * n) ^ 2 / 10 + Q * n / 10) * δ ^ 3 := by
    rw [integral_taylorPoly_localW]
    have hrw : 1 + ‖∑ j ∈ J, (q j : ℂ) * w j‖ ^ 2 + (∑ j ∈ J, q j * ‖w j‖ ^ 2) ^ 2 / 2
        + (∑ j ∈ J, q j * ‖w j‖ ^ 4) / 2 - (1 + ‖∑ j ∈ J, (q j : ℂ) * w j‖ ^ 2)
        = (∑ j ∈ J, q j * ‖w j‖ ^ 2) ^ 2 / 2 + (∑ j ∈ J, q j * ‖w j‖ ^ 4) / 2 := by ring
    rw [hrw]
    have hPsq : (∑ j ∈ J, q j * ‖w j‖ ^ 2) ^ 2 ≤ (Q * n) ^ 2 * δ ^ 4 := by
      rw [← sq_abs]
      calc |∑ j ∈ J, q j * ‖w j‖ ^ 2| ^ 2 ≤ (Q * n * δ ^ 2) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hP 2
        _ = (Q * n) ^ 2 * δ ^ 4 := by ring
    have hδ4 : δ ^ 4 ≤ δ ^ 3 / 5 := by nlinarith [pow_nonneg hδ0 3]
    have hRle : ∑ j ∈ J, q j * ‖w j‖ ^ 4 ≤ Q * n * δ ^ 4 := (le_abs_self _).trans hR
    have hRge : -(Q * n * δ ^ 4) ≤ ∑ j ∈ J, q j * ‖w j‖ ^ 4 := neg_le_of_abs_le hR
    have hQn : 0 ≤ Q * n := mul_nonneg hQ hn0
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (∑ j ∈ J, q j * ‖w j‖ ^ 2), pow_nonneg hδ0 3]
  -- combine
  have htri : |(∫ z, ∏ j ∈ J, ‖(1 - z * w j)⁻¹‖ ^ (2 * q j) ∂steinhausLaw)
      - (1 + ‖∑ j ∈ J, (q j : ℂ) * w j‖ ^ 2)|
      ≤ |(∫ z, ∏ j ∈ J, ‖(1 - z * w j)⁻¹‖ ^ (2 * q j) ∂steinhausLaw)
          - ∫ z, taylorPoly J q (fun j => localW (w j) z) ∂steinhausLaw|
        + |(∫ z, taylorPoly J q (fun j => localW (w j) z) ∂steinhausLaw)
          - (1 + ‖∑ j ∈ J, (q j : ℂ) * w j‖ ^ 2)| := by
    exact abs_sub_le _ (∫ z, taylorPoly J q (fun j => localW (w j) z) ∂steinhausLaw) _
  have hδ'cube : C₀ * δ' ^ 3 ≤ 11 * C₀ * δ ^ 3 := by
    rw [hδ']
    nlinarith [pow_nonneg hδ0 3, hC₀.le]
  linarith [htri, h1, h2, hδ'cube]

end RMF
