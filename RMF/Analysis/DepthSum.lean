/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The sum over depths

The mesoscopic range is covered by `e`-adic blocks indexed by their depth `j = 1, …, J`, and once
the weight `|σ+ih|^{-2} ≍ T_j^{-2}` has cancelled the `T_j²` of the block bound, each block
contributes `(1 + β√j)^{-q}`.  The sum

`∑_{j=1}^{J} (1 + β√j)^{-q}`

is `≍ J·(1 + β√J)^{-q}` — the *last* block's factor times the number of blocks, not the first's
(`RMF.sum_one_add_mul_sqrt_rpow_neg_le`).  This turns the mesoscopic sum into
`(log log x)^{-q/2}·log log x` rather than `log log x`.

## The one inequality underneath

`(1 + β√J)·√j ≤ (1 + β√j)·√J` for `j ≤ J`: the `β√(jJ)` cancels, leaving `√j ≤ √J`.
So the ratio of the two factors is at most `√(J/j)`, and the sum reduces to the partial sum of a
`p`-series at `p = q/2 ≤ ½`.

`RMF.sum_rpow_neg_le` is that partial sum, `∑_{j≤J} j^{-s} ≤ 2·J^{1-s}`, proved by induction with
**no integral comparison**.  The step needs `(J+1)^{1-s} - J^{1-s} ≥ (1-s)(J+1)^{-s}` — concavity
of `t ↦ t^{1-s}` — and that is weighted AM–GM (`Real.geom_mean_le_arith_mean2_weighted`) read at
`u = J/(J+1)`.  The constant `2` is what `1/(1-s) ≤ 2` buys, and `s ≤ ½` is where it comes from.

## Above `q = ½`, the geometric factor runs the other way

The block's gain is `(log w_j)^{q(2q-1)} ≍ e^{(j-J)α}` with `α = q(1-2q)`, and **`α` changes sign at
`q = ½`**.  Below `½` it is positive, the sum is carried by the *deepest* block `j = J`, and the
barrier factor is read at depth `J` (`RMF.sum_exp_mul_one_add_mul_sqrt_rpow_neg_le_geom`).  Above
`½`, with `γ = q(2q-1) ≥ 0`, the factor is `e^{(J-j)γ}` and the *shallowest* blocks carry the sum:

`∑_{j=1}^{J} e^{(J-j)γ}(1+β√j)^{-q} ≪ e^{Jγ}·m·(1+β√m)^{-q}`,  `m = min{J, ⌈γ^{-1}⌉}`,

`RMF.sum_exp_mul_one_add_mul_sqrt_rpow_neg_le_above_min`: the barrier saving survives above `½`,
read at the *effective* depth `m`.  At `β = 1-q` that is `min{log log x, (q(2q-1))^{-1}}^{3/4}`
where a triangle inequality over the same blocks pays the power `1`, and `e^{Jγ}` is
`(log x)^{q(2q-1)}`.  At `γ → 0` it is `J·(1+β√J)^{-q}`, the `q = ½` answer; at `q = 1` the barrier
factor is `1` and `m = 1`, leaving `e^{J}` alone.
-/

namespace RMF

/-! ### The partial sum of a `p`-series -/

/-- **Concavity of `t ↦ t^{1-s}`, in the one form the induction needs.**

`(1-s)·(J+1)^{-s} ≤ (J+1)^{1-s} - J^{1-s}`.

Weighted AM–GM at `u = J/(J+1)` with weights `1-s` and `s`: `u^{1-s} ≤ (1-s)u + s`. -/
lemma rpow_succ_sub_rpow_ge {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (J : ℕ) (hJ : 1 ≤ J) :
    (1 - s) * ((J : ℝ) + 1) ^ (-s) ≤ ((J : ℝ) + 1) ^ (1 - s) - (J : ℝ) ^ (1 - s) := by
  have hJ0 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by linarith
  set r : ℝ := 1 - s with hr
  have hr0 : (0 : ℝ) ≤ r := by rw [hr]; linarith
  have hr1 : (0 : ℝ) ≤ 1 - r := by rw [hr]; linarith
  set u : ℝ := (J : ℝ) / ((J : ℝ) + 1) with hu
  have hu0 : (0 : ℝ) ≤ u := by positivity
  have hpr : (0 : ℝ) < ((J : ℝ) + 1) ^ r := Real.rpow_pos_of_pos hJ1 r
  -- weighted AM–GM
  have hgm : (J : ℝ) ^ r ≤ (r * u + (1 - r)) * ((J : ℝ) + 1) ^ r := by
    have h := Real.geom_mean_le_arith_mean2_weighted hr0 hr1 hu0 zero_le_one (by ring)
    rw [Real.one_rpow, mul_one, mul_one] at h
    rw [hu, Real.div_rpow hJ0.le hJ1.le] at h
    rw [← div_le_iff₀ hpr]
    exact h
  have h1u : (1 : ℝ) - u = 1 / ((J : ℝ) + 1) := by
    rw [hu]; field_simp; ring
  have hid : ((J : ℝ) + 1) ^ r - (r * u + (1 - r)) * ((J : ℝ) + 1) ^ r
      = ((J : ℝ) + 1) ^ r * (r * (1 - u)) := by ring
  have hid2 : ((J : ℝ) + 1) ^ r * (r * (1 - u)) = r * (((J : ℝ) + 1) ^ r / ((J : ℝ) + 1)) := by
    rw [h1u]; field_simp
  have hpow : ((J : ℝ) + 1) ^ r / ((J : ℝ) + 1) = ((J : ℝ) + 1) ^ (-s) := by
    nth_rewrite 2 [show ((J : ℝ) + 1) = ((J : ℝ) + 1) ^ (1 : ℝ) from (Real.rpow_one _).symm]
    rw [← Real.rpow_sub hJ1]
    congr 1
    rw [hr]; ring
  rw [← hpow]
  linarith [hgm, hid, hid2]

/-- **The partial sum of a `p`-series**, `∑_{j=1}^{J} j^{-s} ≤ 2·J^{1-s}` for `0 ≤ s ≤ ½`.

The constant is `1/(1-s) ≤ 2`, and `s ≤ ½` is where that comes from. -/
theorem sum_rpow_neg_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ∀ J : ℕ, 1 ≤ J → ∑ j ∈ Finset.Icc 1 J, ((j : ℝ)) ^ (-s) ≤ 2 * (J : ℝ) ^ (1 - s) := by
  intro J hJ
  induction J, hJ using Nat.le_induction with
  | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, Real.one_rpow]
      norm_num
  | succ J hJ ih =>
      have hJ0 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
      have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by linarith
      have hstep := rpow_succ_sub_rpow_ge hs0 (by linarith) J hJ
      have hcast : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ J + 1), hcast]
      have hpos : (0 : ℝ) < ((J : ℝ) + 1) ^ (-s) := Real.rpow_pos_of_pos hJ1 _
      nlinarith [ih, hstep, hpos]

/-! ### The depth sum -/

/-- **The depth sum is carried by its last term.**
`∑_{j=1}^{J} (1 + β√j)^{-q} ≤ 2·J·(1 + β√J)^{-q}` for `β ≥ 0`, `0 ≤ q ≤ 1` and `J ≥ 1`.

Without the `(1+β√J)^{-q}` on the right this would be the trivial `J`; the content is that the
*average* of the `J` terms is comparable to the *smallest*, which is what makes the mesoscopic sum
give `(log log x)^{-q/2}·log log x` and not `log log x`. -/
theorem sum_one_add_mul_sqrt_rpow_neg_le {β q : ℝ} (hβ : 0 ≤ β) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.Icc 1 J, (1 + β * Real.sqrt j) ^ (-q)
      ≤ 2 * (J : ℝ) * (1 + β * Real.sqrt J) ^ (-q) := by
  have hJ0 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hsJ0 : (0 : ℝ) < Real.sqrt J := Real.sqrt_pos.2 hJ0
  set B : ℝ := 1 + β * Real.sqrt J with hB
  have hB0 : (0 : ℝ) < B := by rw [hB]; positivity
  -- each term against the last one
  have hterm : ∀ j ∈ Finset.Icc 1 J,
      (1 + β * Real.sqrt j) ^ (-q)
        ≤ B ^ (-q) * ((J : ℝ) ^ (q / 2) * ((j : ℝ)) ^ (-(q / 2))) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj.1
    have hsj0 : (0 : ℝ) < Real.sqrt j := Real.sqrt_pos.2 hj0
    have hjJ : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hj.2
    set A : ℝ := 1 + β * Real.sqrt j with hA
    have hA0 : (0 : ℝ) < A := by rw [hA]; positivity
    have hsj : Real.sqrt j ≤ Real.sqrt J := Real.sqrt_le_sqrt hjJ
    -- `B·√j ≤ A·√J`, which is `√j ≤ √J` after the common term cancels
    have hcross : B * Real.sqrt j ≤ A * Real.sqrt J := by
      have h1 : B * Real.sqrt j = Real.sqrt j + β * (Real.sqrt J * Real.sqrt j) := by
        rw [hB]; ring
      have h2 : A * Real.sqrt J = Real.sqrt J + β * (Real.sqrt J * Real.sqrt j) := by
        rw [hA]; ring
      rw [h1, h2]
      linarith
    have hratio : B / A ≤ Real.sqrt J / Real.sqrt j := by
      rw [div_le_div_iff₀ hA0 hsj0]
      linarith
    have hpow : (B / A) ^ q ≤ (Real.sqrt J / Real.sqrt j) ^ q :=
      Real.rpow_le_rpow (by positivity) hratio hq0
    -- the right-hand side, rewritten
    have hRHS : (Real.sqrt J / Real.sqrt j) ^ q
        = (J : ℝ) ^ (q / 2) * ((j : ℝ)) ^ (-(q / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        Real.div_rpow (Real.rpow_nonneg hJ0.le _) (Real.rpow_nonneg hj0.le _),
        ← Real.rpow_mul hJ0.le, ← Real.rpow_mul hj0.le,
        show (1 : ℝ) / 2 * q = q / 2 from by ring,
        Real.rpow_neg hj0.le, div_eq_mul_inv]
    have hdiv : (B / A) ^ q = B ^ q * A ^ (-q) := by
      rw [Real.div_rpow hB0.le hA0.le, Real.rpow_neg hA0.le, div_eq_mul_inv]
    have hfin : B ^ q * A ^ (-q) ≤ (J : ℝ) ^ (q / 2) * ((j : ℝ)) ^ (-(q / 2)) := by
      rw [← hdiv, ← hRHS]; exact hpow
    have hBinv : B ^ (-q) * B ^ q = 1 := by
      rw [← Real.rpow_add hB0]; simp
    calc A ^ (-q) = B ^ (-q) * (B ^ q * A ^ (-q)) := by rw [← mul_assoc, hBinv, one_mul]
      _ ≤ B ^ (-q) * ((J : ℝ) ^ (q / 2) * ((j : ℝ)) ^ (-(q / 2))) :=
          mul_le_mul_of_nonneg_left hfin (Real.rpow_nonneg hB0.le _)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- pull the two constants out and apply the `p`-series bound
  have hpull : (∑ j ∈ Finset.Icc 1 J,
        B ^ (-q) * ((J : ℝ) ^ (q / 2) * ((j : ℝ)) ^ (-(q / 2))))
      = B ^ (-q) * (J : ℝ) ^ (q / 2) * ∑ j ∈ Finset.Icc 1 J, ((j : ℝ)) ^ (-(q / 2)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hpull]
  have hps := sum_rpow_neg_le (s := q / 2) (by linarith) (by linarith) J hJ
  have hc0 : (0 : ℝ) ≤ B ^ (-q) * (J : ℝ) ^ (q / 2) :=
    mul_nonneg (Real.rpow_nonneg hB0.le _) (Real.rpow_nonneg hJ0.le _)
  refine le_trans (mul_le_mul_of_nonneg_left hps hc0) (le_of_eq ?_)
  have hJsum : (J : ℝ) ^ (q / 2) * (J : ℝ) ^ (1 - q / 2) = (J : ℝ) := by
    rw [← Real.rpow_add hJ0]
    norm_num
  calc B ^ (-q) * (J : ℝ) ^ (q / 2) * (2 * (J : ℝ) ^ (1 - q / 2))
      = 2 * ((J : ℝ) ^ (q / 2) * (J : ℝ) ^ (1 - q / 2)) * B ^ (-q) := by ring
    _ = 2 * (J : ℝ) * B ^ (-q) := by rw [hJsum]
    _ = 2 * (J : ℝ) * B ^ (-q) := rfl

/-- **The depth sum with the geometric factor dropped.**  For `α, β ≥ 0`, `0 ≤ q ≤ 1`, `J ≥ 1`,
`∑_{j=1}^{J} e^{(j-J)α}(1 + β√j)^{-q} ≤ 2·J·(1 + β√J)^{-q}`, since `e^{(j-J)α} ≤ 1`.  In the block
assembly `α = q(1-2q)`, from `(log w_j)^{q(2q-1)} = L^{q(2q-1)}·e^{jα}` and `e^{Jα} = L^{α}`.
Keeping the factor gives `6(1+α⁻¹)(1+β√J)^{-q}` for `α > 0` and `q ≤ ½`
(`RMF.sum_exp_mul_one_add_mul_sqrt_rpow_neg_le_geom`); at `q = ½` (`α = 0`) nothing is lost. -/
theorem sum_exp_mul_one_add_mul_sqrt_rpow_neg_le {α β q : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.Icc 1 J, Real.exp (((j : ℝ) - (J : ℝ)) * α) * (1 + β * Real.sqrt j) ^ (-q)
      ≤ 2 * (J : ℝ) * (1 + β * Real.sqrt J) ^ (-q) := by
  refine le_trans (Finset.sum_le_sum ?_) (sum_one_add_mul_sqrt_rpow_neg_le hβ hq0 hq1 hJ)
  intro j hj
  rw [Finset.mem_Icc] at hj
  have hjJ : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hj.2
  have hexp : Real.exp (((j : ℝ) - (J : ℝ)) * α) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hα
  have hg0 : (0 : ℝ) ≤ (1 + β * Real.sqrt j) ^ (-q) :=
    Real.rpow_nonneg (by positivity) _
  nlinarith [hexp, hg0]

/-! ### The depth sum with the geometric factor kept

`RMF.sum_exp_mul_one_add_mul_sqrt_rpow_neg_le` discards `e^{(j-J)α}` and pays the factor `J`.
Kept, the geometric factor concentrates the sum on the top `1/α` blocks:
`∑_{j=1}^{J} e^{(j-J)α}(1+β√j)^{-q} ≤ 6(1+α^{-1})(1+β√J)^{-q}`.  Together the two give
`min{J, 1+α^{-1}}` up to a constant; at `α = q(1-2q)` that is `min{(1-2q)^{-1}, log log x}`.

The termwise ratio `(1+β√j)^{-q} ≤ (1+β√J)^{-q}(J/j)^{q/2}` reduces everything to
`∑_j e^{(j-J)α}j^{-q/2}`, which splits at `j = ⌊J/2⌋`:

* above it, `j^{-q/2} ≤ 2·J^{-q/2}` and the geometric sum is at most `1+α^{-1}`;
* below it, `e^{(j-J)α} ≤ e^{-Jα/2}` and the `p`-series is at most `2J^{1-q/2}`, so the block
  contributes `2J·e^{-Jα/2}·J^{-q/2} ≤ 4α^{-1}·J^{-q/2}`, by `u e^{-u} ≤ 1`. -/

/-- **The termwise ratio**, extracted from `RMF.sum_one_add_mul_sqrt_rpow_neg_le`. -/
lemma one_add_mul_sqrt_rpow_neg_le_ratio {β q : ℝ} (hβ : 0 ≤ β) (hq0 : 0 ≤ q)
    {J j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J) :
    (1 + β * Real.sqrt j) ^ (-q)
      ≤ (1 + β * Real.sqrt J) ^ (-q) * ((J : ℝ) ^ (q / 2) * ((j : ℝ)) ^ (-(q / 2))) := by
  have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have hJ0 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast (by omega : 1 ≤ J)
  have hsj0 : (0 : ℝ) < Real.sqrt j := Real.sqrt_pos.2 hj0
  have hjJR : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hjJ
  set A : ℝ := 1 + β * Real.sqrt j with hA
  set B : ℝ := 1 + β * Real.sqrt J with hB
  have hA0 : (0 : ℝ) < A := by rw [hA]; positivity
  have hB0 : (0 : ℝ) < B := by rw [hB]; positivity
  have hsj : Real.sqrt j ≤ Real.sqrt J := Real.sqrt_le_sqrt hjJR
  have hcross : B * Real.sqrt j ≤ A * Real.sqrt J := by
    have h1 : B * Real.sqrt j = Real.sqrt j + β * (Real.sqrt J * Real.sqrt j) := by rw [hB]; ring
    have h2 : A * Real.sqrt J = Real.sqrt J + β * (Real.sqrt J * Real.sqrt j) := by rw [hA]; ring
    rw [h1, h2]
    linarith
  have hratio : B / A ≤ Real.sqrt J / Real.sqrt j := by
    rw [div_le_div_iff₀ hA0 hsj0]
    linarith
  have hpow : (B / A) ^ q ≤ (Real.sqrt J / Real.sqrt j) ^ q :=
    Real.rpow_le_rpow (by positivity) hratio hq0
  have hRHS : (Real.sqrt J / Real.sqrt j) ^ q
      = (J : ℝ) ^ (q / 2) * ((j : ℝ)) ^ (-(q / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      Real.div_rpow (Real.rpow_nonneg hJ0.le _) (Real.rpow_nonneg hj0.le _),
      ← Real.rpow_mul hJ0.le, ← Real.rpow_mul hj0.le,
      show (1 : ℝ) / 2 * q = q / 2 from by ring,
      Real.rpow_neg hj0.le, div_eq_mul_inv]
  have hdiv : (B / A) ^ q = B ^ q * A ^ (-q) := by
    rw [Real.div_rpow hB0.le hA0.le, Real.rpow_neg hA0.le, div_eq_mul_inv]
  have hfin : B ^ q * A ^ (-q) ≤ (J : ℝ) ^ (q / 2) * ((j : ℝ)) ^ (-(q / 2)) := by
    rw [← hdiv, ← hRHS]
    exact hpow
  have hBinv : B ^ (-q) * B ^ q = 1 := by
    rw [← Real.rpow_add hB0]
    simp
  calc A ^ (-q) = B ^ (-q) * (B ^ q * A ^ (-q)) := by rw [← mul_assoc, hBinv, one_mul]
    _ ≤ B ^ (-q) * ((J : ℝ) ^ (q / 2) * ((j : ℝ)) ^ (-(q / 2))) :=
        mul_le_mul_of_nonneg_left hfin (Real.rpow_nonneg hB0.le _)

/-- **The geometric sum.**  `∑_{j=1}^{J} e^{(j-J)α} ≤ 1 + α^{-1}`, uniformly in `J`. -/
lemma sum_exp_sub_mul_le {α : ℝ} (hα : 0 < α) (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, Real.exp (((j : ℝ) - (J : ℝ)) * α) ≤ 1 + α⁻¹ := by
  have hαinv : (0 : ℝ) < α⁻¹ := by positivity
  induction J with
  | zero =>
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      linarith
  | succ J ih =>
      have hcast : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
      have hrec : ∑ j ∈ Finset.Icc 1 (J + 1), Real.exp (((j : ℝ) - ((J + 1 : ℕ) : ℝ)) * α)
          = Real.exp (-α) * ∑ j ∈ Finset.Icc 1 J, Real.exp (((j : ℝ) - (J : ℝ)) * α) + 1 := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ J + 1), Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Real.exp_add, hcast]
          congr 1
          ring
        · rw [hcast]
          norm_num
      rw [hrec]
      have hexp : Real.exp (-α) * (1 + α⁻¹) ≤ α⁻¹ := by
        have h1 : α + 1 ≤ Real.exp α := by linarith [Real.add_one_le_exp α]
        have h2 : Real.exp (-α) * Real.exp α = 1 := by
          rw [← Real.exp_add]
          simp
        have h3 : (0 : ℝ) < Real.exp (-α) := Real.exp_pos _
        have h4 : α * α⁻¹ = 1 := mul_inv_cancel₀ hα.ne'
        nlinarith [h1, h2, h3, h4]
      have hnn : (0 : ℝ) ≤ Real.exp (-α) := (Real.exp_pos _).le
      nlinarith [ih, hnn, hexp]

/-- `α·J·e^{-Jα/2} ≤ 2`, i.e. `J·e^{-Jα/2} ≤ 2/α`.  This is `u·e^{-u} ≤ 1` at `u = Jα/2`. -/
lemma mul_exp_neg_half_le (α : ℝ) (J : ℕ) :
    α * ((J : ℝ) * Real.exp (-((J : ℝ) * α / 2))) ≤ 2 := by
  have hE : (0 : ℝ) < Real.exp (-((J : ℝ) * α / 2)) := Real.exp_pos _
  have hid : Real.exp (-((J : ℝ) * α / 2)) * Real.exp ((J : ℝ) * α / 2) = 1 := by
    rw [← Real.exp_add]
    simp
  have he : (J : ℝ) * α / 2 + 1 ≤ Real.exp ((J : ℝ) * α / 2) := Real.add_one_le_exp _
  nlinarith [hid, he, hE]

/-- **The depth sum, with the geometric factor kept.**  For `α > 0`, `β ≥ 0` and `0 ≤ q ≤ ½`,
`∑_{j=1}^{J} e^{(j-J)α}(1+β√j)^{-q} ≤ 6(1+α^{-1})(1+β√J)^{-q}`. -/
theorem sum_exp_mul_one_add_mul_sqrt_rpow_neg_le_geom {α β q : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) {J : ℕ} (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.Icc 1 J, Real.exp (((j : ℝ) - (J : ℝ)) * α) * (1 + β * Real.sqrt j) ^ (-q)
      ≤ 6 * (1 + α⁻¹) * (1 + β * Real.sqrt J) ^ (-q) := by
  have hJ0 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hαinv : (0 : ℝ) < α⁻¹ := by positivity
  set B : ℝ := 1 + β * Real.sqrt J with hB
  have hB0 : (0 : ℝ) < B := by rw [hB]; positivity
  have hBq : (0 : ℝ) < B ^ (-q) := Real.rpow_pos_of_pos hB0 _
  have hJq : (0 : ℝ) < (J : ℝ) ^ (q / 2) := Real.rpow_pos_of_pos hJ0 _
  have hJqn : (0 : ℝ) < (J : ℝ) ^ (-(q / 2)) := Real.rpow_pos_of_pos hJ0 _
  -- the core sum, with the barrier factor already traded for `j^{-q/2}`
  have hcore : ∑ j ∈ Finset.Icc 1 J,
        Real.exp (((j : ℝ) - (J : ℝ)) * α) * ((j : ℝ)) ^ (-(q / 2))
      ≤ 6 * (1 + α⁻¹) * (J : ℝ) ^ (-(q / 2)) := by
    have hIoc : Finset.Icc 1 J = Finset.Ioc 0 J := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hmJ : J / 2 ≤ J := Nat.div_le_self _ _
    have hnn : ∀ j : ℕ, (0 : ℝ) ≤ Real.exp (((j : ℝ) - (J : ℝ)) * α) * ((j : ℝ)) ^ (-(q / 2)) :=
      fun j => mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (Nat.cast_nonneg j) _)
    rw [hIoc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (J / 2)) hmJ]
    -- the top half: `j ≥ J/2`, so `j^{-q/2} ≤ 2 J^{-q/2}`
    have htop : ∑ j ∈ Finset.Ioc (J / 2) J,
          Real.exp (((j : ℝ) - (J : ℝ)) * α) * ((j : ℝ)) ^ (-(q / 2))
        ≤ 2 * (J : ℝ) ^ (-(q / 2)) * (1 + α⁻¹) := by
      have hb : ∀ j ∈ Finset.Ioc (J / 2) J,
          Real.exp (((j : ℝ) - (J : ℝ)) * α) * ((j : ℝ)) ^ (-(q / 2))
            ≤ 2 * (J : ℝ) ^ (-(q / 2)) * Real.exp (((j : ℝ) - (J : ℝ)) * α) := by
        intro j hj
        rw [Finset.mem_Ioc] at hj
        have hj0 : (0 : ℝ) < (j : ℝ) := by
          have : 1 ≤ j := by omega
          exact_mod_cast this
        have hhalf : (J : ℝ) / 2 ≤ (j : ℝ) := by
          have : J ≤ 2 * j := by omega
          have h2 : (J : ℝ) ≤ 2 * (j : ℝ) := by exact_mod_cast this
          linarith
        have hstep : ((j : ℝ)) ^ (-(q / 2)) ≤ ((J : ℝ) / 2) ^ (-(q / 2)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by linarith)
        have hsplit : ((J : ℝ) / 2) ^ (-(q / 2))
            = (J : ℝ) ^ (-(q / 2)) * (2 : ℝ) ^ (q / 2) := by
          rw [Real.div_rpow hJ0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
            div_eq_mul_inv, inv_inv]
        have h2q : (2 : ℝ) ^ (q / 2) ≤ 2 := by
          calc (2 : ℝ) ^ (q / 2) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one _
        rw [hsplit] at hstep
        have hex : (0 : ℝ) < Real.exp (((j : ℝ) - (J : ℝ)) * α) := Real.exp_pos _
        have hj2 : ((j : ℝ)) ^ (-(q / 2)) ≤ 2 * (J : ℝ) ^ (-(q / 2)) := by
          nlinarith [hstep, h2q, hJqn]
        calc Real.exp (((j : ℝ) - (J : ℝ)) * α) * ((j : ℝ)) ^ (-(q / 2))
            ≤ Real.exp (((j : ℝ) - (J : ℝ)) * α) * (2 * (J : ℝ) ^ (-(q / 2))) :=
              mul_le_mul_of_nonneg_left hj2 hex.le
          _ = 2 * (J : ℝ) ^ (-(q / 2)) * Real.exp (((j : ℝ) - (J : ℝ)) * α) := by ring
      refine le_trans (Finset.sum_le_sum hb) ?_
      rw [← Finset.mul_sum]
      have hsub : ∑ j ∈ Finset.Ioc (J / 2) J, Real.exp (((j : ℝ) - (J : ℝ)) * α)
          ≤ ∑ j ∈ Finset.Icc 1 J, Real.exp (((j : ℝ) - (J : ℝ)) * α) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => (Real.exp_pos _).le)
        rw [hIoc]
        exact Finset.Ioc_subset_Ioc_left (Nat.zero_le _)
      exact mul_le_mul_of_nonneg_left (le_trans hsub (sum_exp_sub_mul_le hα J)) (by positivity)
    -- the bottom half: `j ≤ J/2`, so `e^{(j-J)α} ≤ e^{-Jα/2}`
    have hbot : ∑ j ∈ Finset.Ioc 0 (J / 2),
          Real.exp (((j : ℝ) - (J : ℝ)) * α) * ((j : ℝ)) ^ (-(q / 2))
        ≤ 4 * α⁻¹ * (J : ℝ) ^ (-(q / 2)) := by
      have hb : ∀ j ∈ Finset.Ioc 0 (J / 2),
          Real.exp (((j : ℝ) - (J : ℝ)) * α) * ((j : ℝ)) ^ (-(q / 2))
            ≤ Real.exp (-((J : ℝ) * α / 2)) * ((j : ℝ)) ^ (-(q / 2)) := by
        intro j hj
        rw [Finset.mem_Ioc] at hj
        have hjh : 2 * j ≤ J := by omega
        have hjhR : 2 * (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hjh
        have hexp : Real.exp (((j : ℝ) - (J : ℝ)) * α) ≤ Real.exp (-((J : ℝ) * α / 2)) := by
          refine Real.exp_le_exp.2 ?_
          nlinarith
        exact mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg (Nat.cast_nonneg j) _)
      refine le_trans (Finset.sum_le_sum hb) ?_
      rw [← Finset.mul_sum]
      have hsub : ∑ j ∈ Finset.Ioc 0 (J / 2), ((j : ℝ)) ^ (-(q / 2))
          ≤ ∑ j ∈ Finset.Icc 1 J, ((j : ℝ)) ^ (-(q / 2)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun j _ _ => Real.rpow_nonneg (Nat.cast_nonneg j) _)
        rw [hIoc]
        exact Finset.Ioc_subset_Ioc_right hmJ
      have hps := sum_rpow_neg_le (s := q / 2) (by linarith) (by linarith) J hJ
      have hE : (0 : ℝ) < Real.exp (-((J : ℝ) * α / 2)) := Real.exp_pos _
      have hstep := mul_le_mul_of_nonneg_left (le_trans hsub hps) hE.le
      refine le_trans hstep ?_
      have hJsplit : (J : ℝ) ^ (1 - q / 2) = (J : ℝ) * (J : ℝ) ^ (-(q / 2)) := by
        have h : (J : ℝ) ^ (1 : ℝ) * (J : ℝ) ^ (-(q / 2)) = (J : ℝ) ^ (1 - q / 2) := by
          rw [← Real.rpow_add hJ0, show (1 : ℝ) + -(q / 2) = 1 - q / 2 from by ring]
        rw [← h, Real.rpow_one]
      rw [hJsplit]
      have hkey := mul_exp_neg_half_le α J
      have hJE : (J : ℝ) * Real.exp (-((J : ℝ) * α / 2)) ≤ 2 * α⁻¹ := by
        have h4 : α * α⁻¹ = 1 := mul_inv_cancel₀ hα.ne'
        nlinarith [hkey, hαinv, mul_nonneg (Nat.cast_nonneg J : (0:ℝ) ≤ (J:ℝ)) hE.le]
      nlinarith [hJE, hJqn, hE]
    linarith
  -- termwise, then the core sum
  have hterm : ∀ j ∈ Finset.Icc 1 J,
      Real.exp (((j : ℝ) - (J : ℝ)) * α) * (1 + β * Real.sqrt j) ^ (-q)
        ≤ B ^ (-q) * (J : ℝ) ^ (q / 2)
          * (Real.exp (((j : ℝ) - (J : ℝ)) * α) * ((j : ℝ)) ^ (-(q / 2))) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have h := one_add_mul_sqrt_rpow_neg_le_ratio hβ hq0 hj.1 hj.2
    have hex : (0 : ℝ) < Real.exp (((j : ℝ) - (J : ℝ)) * α) := Real.exp_pos _
    calc Real.exp (((j : ℝ) - (J : ℝ)) * α) * (1 + β * Real.sqrt j) ^ (-q)
        ≤ Real.exp (((j : ℝ) - (J : ℝ)) * α)
            * (B ^ (-q) * ((J : ℝ) ^ (q / 2) * ((j : ℝ)) ^ (-(q / 2)))) :=
          mul_le_mul_of_nonneg_left h hex.le
      _ = B ^ (-q) * (J : ℝ) ^ (q / 2)
            * (Real.exp (((j : ℝ) - (J : ℝ)) * α) * ((j : ℝ)) ^ (-(q / 2))) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hc0 : (0 : ℝ) ≤ B ^ (-q) * (J : ℝ) ^ (q / 2) := by positivity
  have hstep := mul_le_mul_of_nonneg_left hcore hc0
  refine le_trans hstep (le_of_eq ?_)
  have hcancel : (J : ℝ) ^ (q / 2) * (J : ℝ) ^ (-(q / 2)) = 1 := by
    rw [← Real.rpow_add hJ0]
    simp
  calc B ^ (-q) * (J : ℝ) ^ (q / 2) * (6 * (1 + α⁻¹) * (J : ℝ) ^ (-(q / 2)))
      = 6 * (1 + α⁻¹) * ((J : ℝ) ^ (q / 2) * (J : ℝ) ^ (-(q / 2))) * B ^ (-q) := by ring
    _ = 6 * (1 + α⁻¹) * B ^ (-q) := by rw [hcancel]; ring

/-! ### The depth sum above the critical exponent

`RMF.sum_exp_mul_one_add_mul_sqrt_rpow_neg_le_geom` is the sum with `e^{(j-J)α}`, `α > 0`.  What
follows is the same sum with the sign of the exponent reversed, `e^{(J-j)γ}` with `γ > 0`, which
is what the mesoscopic blocks produce once `q` passes `½`.  The split is at a free index `m`:

* `j ≤ m`: drop the geometric factor (`e^{(J-j)γ} ≤ e^{Jγ}`) and use
  `RMF.sum_one_add_mul_sqrt_rpow_neg_le`, which is the statement that the average of the first `m`
  barrier factors is comparable to the `m`-th;
* `j > m`: drop the barrier factor to its value at `m` (it is antitone) and sum the geometric
  factor, `∑_{j>m} e^{-jγ} ≤ γ^{-1}(e^{-mγ} - e^{-Jγ})`.

The second bound is kept *sharp* rather than bounded by `γ^{-1}`, because the corollary needs it
to vanish when `m = J`. -/

/-- **A geometric tail, sharply.**  `∑_{j=m+1}^{J} e^{-jγ} ≤ γ^{-1}(e^{-mγ} - e^{-Jγ})`.

Induction on `J` from `m`; the step is `γ + 1 ≤ e^{γ}`.  It is an equality in the limit `γ → 0`
after dividing by `γ`, so nothing is lost here. -/
lemma sum_Icc_exp_neg_mul_le {γ : ℝ} (hγ : 0 < γ) {m : ℕ} :
    ∀ J : ℕ, m ≤ J → ∑ j ∈ Finset.Icc (m + 1) J, Real.exp (-((j : ℝ) * γ))
      ≤ γ⁻¹ * (Real.exp (-((m : ℝ) * γ)) - Real.exp (-((J : ℝ) * γ))) := by
  intro J hJ
  induction J, hJ using Nat.le_induction with
  | base => simp
  | succ J hJ ih =>
      have hA0 : (0 : ℝ) < Real.exp (-(((J : ℝ) + 1) * γ)) := Real.exp_pos _
      have hAB : Real.exp (-((J : ℝ) * γ))
          = Real.exp (-(((J : ℝ) + 1) * γ)) * Real.exp γ := by
        rw [← Real.exp_add]
        congr 1
        ring
      have he : γ + 1 ≤ Real.exp γ := Real.add_one_le_exp γ
      have key : γ * Real.exp (-(((J : ℝ) + 1) * γ))
          ≤ Real.exp (-((J : ℝ) * γ)) - Real.exp (-(((J : ℝ) + 1) * γ)) := by
        rw [hAB]
        nlinarith [hA0, he]
      have hstep : Real.exp (-(((J : ℝ) + 1) * γ))
          ≤ γ⁻¹ * (Real.exp (-((J : ℝ) * γ)) - Real.exp (-(((J : ℝ) + 1) * γ))) := by
        calc Real.exp (-(((J : ℝ) + 1) * γ))
            = γ⁻¹ * (γ * Real.exp (-(((J : ℝ) + 1) * γ))) := by
              field_simp
          _ ≤ γ⁻¹ * (Real.exp (-((J : ℝ) * γ)) - Real.exp (-(((J : ℝ) + 1) * γ))) :=
              mul_le_mul_of_nonneg_left key (by positivity)
      rw [Finset.sum_Icc_succ_top (by omega : m + 1 ≤ J + 1)]
      push_cast
      linarith [ih, hstep]

/-- **The depth sum above `½`, split at a free index `m`.**  For `γ > 0`, `β ≥ 0`, `0 ≤ q ≤ 1` and
`1 ≤ m ≤ J`,
`∑_{j=1}^{J} e^{(J-j)γ}(1+β√j)^{-q} ≤ e^{Jγ}·(2m + γ^{-1}(e^{-mγ}-e^{-Jγ}))·(1+β√m)^{-q}`.
`m` is left free because the caller knows which of `J` and `γ^{-1}` binds; the choice
`m = min{J, ⌈γ^{-1}⌉}` is `RMF.sum_exp_mul_one_add_mul_sqrt_rpow_neg_le_above_min`. -/
theorem sum_exp_mul_one_add_mul_sqrt_rpow_neg_le_above {γ β q : ℝ} (hγ : 0 < γ) (hβ : 0 ≤ β)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {J m : ℕ} (hm1 : 1 ≤ m) (hmJ : m ≤ J) :
    ∑ j ∈ Finset.Icc 1 J, Real.exp (((J : ℝ) - j) * γ) * (1 + β * Real.sqrt j) ^ (-q)
      ≤ Real.exp ((J : ℝ) * γ)
          * (2 * (m : ℝ) + γ⁻¹ * (Real.exp (-((m : ℝ) * γ)) - Real.exp (-((J : ℝ) * γ))))
          * (1 + β * Real.sqrt m) ^ (-q) := by
  have hBm0 : (0 : ℝ) < 1 + β * Real.sqrt m := by positivity
  have hBmq : (0 : ℝ) < (1 + β * Real.sqrt m) ^ (-q) := Real.rpow_pos_of_pos hBm0 _
  have hE0 : (0 : ℝ) < Real.exp ((J : ℝ) * γ) := Real.exp_pos _
  -- the head: drop the geometric factor
  have hhead : ∑ j ∈ Finset.Icc 1 m,
        Real.exp (((J : ℝ) - j) * γ) * (1 + β * Real.sqrt j) ^ (-q)
      ≤ Real.exp ((J : ℝ) * γ) * (2 * (m : ℝ) * (1 + β * Real.sqrt m) ^ (-q)) := by
    have hterm : ∀ j ∈ Finset.Icc 1 m,
        Real.exp (((J : ℝ) - j) * γ) * (1 + β * Real.sqrt j) ^ (-q)
          ≤ Real.exp ((J : ℝ) * γ) * (1 + β * Real.sqrt j) ^ (-q) := by
      intro j hj
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hj).1
      have hex : Real.exp (((J : ℝ) - j) * γ) ≤ Real.exp ((J : ℝ) * γ) :=
        Real.exp_le_exp.2 (by nlinarith)
      exact mul_le_mul_of_nonneg_right hex (Real.rpow_nonneg (by positivity) _)
    calc ∑ j ∈ Finset.Icc 1 m,
          Real.exp (((J : ℝ) - j) * γ) * (1 + β * Real.sqrt j) ^ (-q)
        ≤ ∑ j ∈ Finset.Icc 1 m,
            Real.exp ((J : ℝ) * γ) * (1 + β * Real.sqrt j) ^ (-q) := Finset.sum_le_sum hterm
      _ = Real.exp ((J : ℝ) * γ) * ∑ j ∈ Finset.Icc 1 m, (1 + β * Real.sqrt j) ^ (-q) := by
          rw [Finset.mul_sum]
      _ ≤ Real.exp ((J : ℝ) * γ) * (2 * (m : ℝ) * (1 + β * Real.sqrt m) ^ (-q)) :=
          mul_le_mul_of_nonneg_left (sum_one_add_mul_sqrt_rpow_neg_le hβ hq0 hq1 hm1) hE0.le
  -- the tail: drop the barrier factor to its value at `m`
  have htail : ∑ j ∈ Finset.Icc (m + 1) J,
        Real.exp (((J : ℝ) - j) * γ) * (1 + β * Real.sqrt j) ^ (-q)
      ≤ Real.exp ((J : ℝ) * γ)
          * (γ⁻¹ * (Real.exp (-((m : ℝ) * γ)) - Real.exp (-((J : ℝ) * γ)))
            * (1 + β * Real.sqrt m) ^ (-q)) := by
    have hterm : ∀ j ∈ Finset.Icc (m + 1) J,
        Real.exp (((J : ℝ) - j) * γ) * (1 + β * Real.sqrt j) ^ (-q)
          ≤ Real.exp ((J : ℝ) * γ) * (1 + β * Real.sqrt m) ^ (-q)
              * Real.exp (-((j : ℝ) * γ)) := by
      intro j hj
      have hmj : (m : ℝ) ≤ (j : ℝ) := by
        have : m ≤ j := le_trans (Nat.le_succ m) (Finset.mem_Icc.1 hj).1
        exact_mod_cast this
      have hsq : Real.sqrt m ≤ Real.sqrt j := Real.sqrt_le_sqrt hmj
      have hmono : (1 + β * Real.sqrt j) ^ (-q) ≤ (1 + β * Real.sqrt m) ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos hBm0 (by nlinarith) (by linarith)
      have heq : Real.exp (((J : ℝ) - j) * γ)
          = Real.exp ((J : ℝ) * γ) * Real.exp (-((j : ℝ) * γ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [heq]
      calc Real.exp ((J : ℝ) * γ) * Real.exp (-((j : ℝ) * γ))
            * (1 + β * Real.sqrt j) ^ (-q)
          ≤ Real.exp ((J : ℝ) * γ) * Real.exp (-((j : ℝ) * γ))
              * (1 + β * Real.sqrt m) ^ (-q) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
        _ = Real.exp ((J : ℝ) * γ) * (1 + β * Real.sqrt m) ^ (-q)
              * Real.exp (-((j : ℝ) * γ)) := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hgeom := sum_Icc_exp_neg_mul_le hγ (m := m) J hmJ
    have hc0 : (0 : ℝ) ≤ Real.exp ((J : ℝ) * γ) * (1 + β * Real.sqrt m) ^ (-q) := by positivity
    calc Real.exp ((J : ℝ) * γ) * (1 + β * Real.sqrt m) ^ (-q)
          * ∑ j ∈ Finset.Icc (m + 1) J, Real.exp (-((j : ℝ) * γ))
        ≤ Real.exp ((J : ℝ) * γ) * (1 + β * Real.sqrt m) ^ (-q)
            * (γ⁻¹ * (Real.exp (-((m : ℝ) * γ)) - Real.exp (-((J : ℝ) * γ)))) :=
          mul_le_mul_of_nonneg_left hgeom hc0
      _ = Real.exp ((J : ℝ) * γ)
            * (γ⁻¹ * (Real.exp (-((m : ℝ) * γ)) - Real.exp (-((J : ℝ) * γ)))
              * (1 + β * Real.sqrt m) ^ (-q)) := by ring
  -- and the two halves are the whole sum
  have hIoc1 : Finset.Icc 1 J = Finset.Ioc 0 J := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hIoc2 : Finset.Icc 1 m = Finset.Ioc 0 m := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hIoc3 : Finset.Icc (m + 1) J = Finset.Ioc m J := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIoc1, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le m) hmJ, ← hIoc2, ← hIoc3]
  have hring : Real.exp ((J : ℝ) * γ) * (2 * (m : ℝ) * (1 + β * Real.sqrt m) ^ (-q))
        + Real.exp ((J : ℝ) * γ)
          * (γ⁻¹ * (Real.exp (-((m : ℝ) * γ)) - Real.exp (-((J : ℝ) * γ)))
            * (1 + β * Real.sqrt m) ^ (-q))
      = Real.exp ((J : ℝ) * γ)
          * (2 * (m : ℝ) + γ⁻¹ * (Real.exp (-((m : ℝ) * γ)) - Real.exp (-((J : ℝ) * γ))))
          * (1 + β * Real.sqrt m) ^ (-q) := by ring
  linarith [hhead, htail]

/-- **The depth sum above `½`, at the effective depth.**  For `γ > 0`, `β ≥ 0`, `0 ≤ q ≤ 1` and
`J ≥ 1`, `∑_{j=1}^{J} e^{(J-j)γ}(1+β√j)^{-q} ≤ 3·e^{Jγ}·m·(1+β√m)^{-q}` with `m = min{J, ⌈γ^{-1}⌉}`.

The above-`½` twin of `RMF.sum_exp_mul_one_add_mul_sqrt_rpow_neg_le_geom`: the barrier saving is
read at the effective depth `m` rather than at `J`.  Both branches of the `min` occur: `m = J` at
the `q ↓ ½` end, and `m = ⌈γ^{-1}⌉`, a constant, for fixed `q > ½` (with `γ = q(2q-1)`). -/
theorem sum_exp_mul_one_add_mul_sqrt_rpow_neg_le_above_min {γ β q : ℝ} (hγ : 0 < γ) (hβ : 0 ≤ β)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.Icc 1 J, Real.exp (((J : ℝ) - j) * γ) * (1 + β * Real.sqrt j) ^ (-q)
      ≤ 3 * Real.exp ((J : ℝ) * γ) * ((min J ⌈γ⁻¹⌉₊ : ℕ) : ℝ)
          * (1 + β * Real.sqrt ((min J ⌈γ⁻¹⌉₊ : ℕ) : ℝ)) ^ (-q) := by
  have hceil1 : 1 ≤ ⌈γ⁻¹⌉₊ := Nat.one_le_ceil_iff.2 (by positivity)
  have hm1 : 1 ≤ min J ⌈γ⁻¹⌉₊ := le_min hJ hceil1
  have hmJ : min J ⌈γ⁻¹⌉₊ ≤ J := min_le_left _ _
  have hbase := sum_exp_mul_one_add_mul_sqrt_rpow_neg_le_above hγ hβ hq0 hq1 hm1 hmJ
  have hE0 : (0 : ℝ) < Real.exp ((J : ℝ) * γ) := Real.exp_pos _
  have hBq : (0 : ℝ) < (1 + β * Real.sqrt ((min J ⌈γ⁻¹⌉₊ : ℕ) : ℝ)) ^ (-q) :=
    Real.rpow_pos_of_pos (by positivity) _
  -- the tail term is at most the head's `m`
  have hextra : γ⁻¹ * (Real.exp (-(((min J ⌈γ⁻¹⌉₊ : ℕ) : ℝ) * γ)) - Real.exp (-((J : ℝ) * γ)))
      ≤ ((min J ⌈γ⁻¹⌉₊ : ℕ) : ℝ) := by
    rcases le_total J ⌈γ⁻¹⌉₊ with h | h
    · -- `m = J`: the tail is empty
      rw [min_eq_left h]
      have : γ⁻¹ * (Real.exp (-((J : ℝ) * γ)) - Real.exp (-((J : ℝ) * γ))) = 0 := by ring
      rw [this]
      exact Nat.cast_nonneg _
    · -- `m = ⌈γ^{-1}⌉ ≥ γ^{-1}`, and the bracket is at most `1`
      rw [min_eq_right h]
      have hce : γ⁻¹ ≤ (⌈γ⁻¹⌉₊ : ℝ) := Nat.le_ceil _
      have h1 : Real.exp (-((⌈γ⁻¹⌉₊ : ℝ) * γ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : (0 : ℝ) ≤ (⌈γ⁻¹⌉₊ : ℝ) * γ := by positivity
        linarith
      have h2 : (0 : ℝ) < Real.exp (-((J : ℝ) * γ)) := Real.exp_pos _
      have hγi : (0 : ℝ) < γ⁻¹ := by positivity
      nlinarith [h1, h2, hγi, hce]
  refine le_trans hbase ?_
  have hstep : Real.exp ((J : ℝ) * γ)
      * (2 * ((min J ⌈γ⁻¹⌉₊ : ℕ) : ℝ)
        + γ⁻¹ * (Real.exp (-(((min J ⌈γ⁻¹⌉₊ : ℕ) : ℝ) * γ)) - Real.exp (-((J : ℝ) * γ))))
      ≤ 3 * Real.exp ((J : ℝ) * γ) * ((min J ⌈γ⁻¹⌉₊ : ℕ) : ℝ) := by
    nlinarith [hextra, hE0]
  exact mul_le_mul_of_nonneg_right hstep hBq.le

end RMF
