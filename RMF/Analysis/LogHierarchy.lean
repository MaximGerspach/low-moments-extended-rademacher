/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Analysis.IteratedLog
import RMF.Analysis.DepthSum

/-!
# The hierarchy of scales above `q = ½`: its bracket is bounded

The sharp bound for `½ < q ≤ 1` (`RMF.exists_integral_rpow_norm_weightedRademacherSum_le_sharp`)
applies the truncation bound at the levels `z_ℓ = x^{1/V_ℓ}` and bounds `‖S(x)‖_{2q}` by
`(log x)^{(2q-1)/2}·b(m)^{1/2q}`, `b` the ballot factor `RMF.ballotFactor`, times the bracket

`1 + ∑_{ℓ=1}^{L} V_ℓ^{-(2q-1)/2}·(min{(2q-1)^{-1}, log κ_ℓ}/m)^{1/4}`,
`m = min{(2q-1)^{-1}, log log x}`.

This file proves the two sums that bound it by an absolute constant.

## The levels are `RMF.iterLog`, scaled

The levels are `V_ℓ = C₀·log_ℓ Λ` with `Λ = log log x` and `log_ℓ = RMF.iterLog ℓ`, the iterated
logarithm the Probability Lemma 1 induction already uses.  The truncation bound's two hypotheses
at level `ℓ` hold for it: `κ_ℓ = log_{ℓ-1}Λ/log_ℓΛ ≥ e` is `RMF.exp_one_mul_iterLog_succ_le`, and
`C₀ log κ_ℓ = C₀(log_ℓΛ − log log_ℓΛ) ≤ V_ℓ` because `log log_ℓΛ ≥ 0` in the good range.  And the
choice comes with the two facts the sums run on: geometric decay, `e·log_{ℓ+1} ≤ log_ℓ`, and the
tower, `log_ℓ = exp(log_{ℓ+1})`, which is the definition read backwards.

## The two sums

With `μ_ℓ ≤ log_ℓΛ` (from `log κ_ℓ ≤ log log_{ℓ-1}Λ`) and `V_ℓ ≥ log_ℓΛ`, each term of the
bracket is at most `(log_ℓΛ)^{-δ/2}·(min{1/δ, log_ℓΛ}/m)^{1/4}` with `δ = 2q-1`, and the two
branches of `m` are the two theorems:

* `m = Λ`: the term is at most `(log_ℓΛ/Λ)^{1/4}`, a geometric sum of fourth roots whose first term
  is `(log Λ/Λ)^{1/4} ≤ 1` — `RMF.sum_iterLog_div_quarter_le`.
* `m = 1/δ`: the term is at most `(log_ℓΛ)^{-δ/2}·min{1, δ log_ℓΛ}^{1/4}` —
  `RMF.sum_iterLog_damped_le`.  Split at `ℓ_B`, the last level with `δ log_ℓΛ > 1`.  Above it (in
  `ℓ`) the `min` is its second argument and decays geometrically from at most `1`.  Below it the
  damping does the work, and **the tower is what makes it enough**: for `ℓ < ℓ_B`,
  `(log_ℓΛ)^{-δ/2} = exp(-(δ/2) log_{ℓ+1}Λ)` and `δ log_{ℓ+1}Λ ≥ e^{ℓ_B-ℓ-1} ≥ ℓ_B − ℓ`, so the
  terms are at most `e^{(ℓ−ℓ_B)/2}`, which is `RMF.sum_exp_sub_mul_le`'s shape.  Geometric decay
  alone gives `∑ e^{-kδ/2} ≍ 1/δ` there, which is not bounded.
-/

open Real

namespace RMF

/-! ### A geometric sum of fourth roots -/

/-- **Geometric decrease, iterated.**  If each step from `i₀` to `L` divides by at least `e`, then
`a_ℓ ≤ e^{-(ℓ-i₀)}·a_{i₀}`. -/
lemma le_exp_neg_mul_of_geom {a : ℕ → ℝ} {i₀ L : ℕ}
    (hgeo : ∀ ℓ, i₀ ≤ ℓ → ℓ < L → Real.exp 1 * a (ℓ + 1) ≤ a ℓ) :
    ∀ ℓ, i₀ ≤ ℓ → ℓ ≤ L → a ℓ ≤ Real.exp (-((ℓ : ℝ) - i₀)) * a i₀ := by
  intro ℓ hℓ
  induction ℓ, hℓ using Nat.le_induction with
  | base => intro _; simp
  | succ ℓ hℓ ih =>
      intro hL
      have h1 := hgeo ℓ hℓ (by omega)
      have h2 := ih (by omega)
      have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
      have h3 : a (ℓ + 1) ≤ Real.exp (-1) * a ℓ := by
        calc a (ℓ + 1) = Real.exp (-1) * (Real.exp 1 * a (ℓ + 1)) := by
              rw [← mul_assoc, he, one_mul]
          _ ≤ Real.exp (-1) * a ℓ := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      have hE : Real.exp (-1) * Real.exp (-((ℓ : ℝ) - i₀))
          = Real.exp (-(((ℓ + 1 : ℕ) : ℝ) - i₀)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      calc a (ℓ + 1) ≤ Real.exp (-1) * a ℓ := h3
        _ ≤ Real.exp (-1) * (Real.exp (-((ℓ : ℝ) - i₀)) * a i₀) :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ = Real.exp (-1) * Real.exp (-((ℓ : ℝ) - i₀)) * a i₀ := by ring
        _ = Real.exp (-(((ℓ + 1 : ℕ) : ℝ) - i₀)) * a i₀ := by rw [hE]

/-- **A geometric sum of fourth roots.**  If each step from `i₀` to `L` divides by at least `e`,
then `∑_{ℓ=i₀}^{L} a_ℓ^{1/4} ≤ 4e^{1/4}·a_{i₀}^{1/4}`.

The geometric tail is `RMF.sum_Icc_exp_neg_mul_le` at `γ = 1/4`. -/
theorem sum_rpow_quarter_le_of_geom {a : ℕ → ℝ} {i₀ L : ℕ} (hi₀ : 1 ≤ i₀) (hi₀L : i₀ ≤ L)
    (hnn : ∀ ℓ, i₀ ≤ ℓ → ℓ ≤ L → 0 ≤ a ℓ)
    (hgeo : ∀ ℓ, i₀ ≤ ℓ → ℓ < L → Real.exp 1 * a (ℓ + 1) ≤ a ℓ) :
    ∑ ℓ ∈ Finset.Icc i₀ L, a ℓ ^ (1 / 4 : ℝ) ≤ 4 * Real.exp (1 / 4) * a i₀ ^ (1 / 4 : ℝ) := by
  have ha0 : 0 ≤ a i₀ := hnn i₀ le_rfl hi₀L
  have hc0 : (0 : ℝ) ≤ a i₀ ^ (1 / 4 : ℝ) := Real.rpow_nonneg ha0 _
  -- each term against the first
  have hterm : ∀ ℓ ∈ Finset.Icc i₀ L,
      a ℓ ^ (1 / 4 : ℝ) ≤ a i₀ ^ (1 / 4 : ℝ) * (Real.exp ((i₀ : ℝ) * (1 / 4))
        * Real.exp (-((ℓ : ℝ) * (1 / 4)))) := by
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    have hle := le_exp_neg_mul_of_geom hgeo ℓ hℓ.1 hℓ.2
    have hpow := Real.rpow_le_rpow (hnn ℓ hℓ.1 hℓ.2) hle (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [Real.mul_rpow (Real.exp_pos _).le ha0, Real.rpow_def_of_pos (Real.exp_pos _),
      Real.log_exp] at hpow
    refine le_trans hpow (le_of_eq ?_)
    rw [← Real.exp_add, mul_comm]
    congr 2
    ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  -- the geometric tail at `γ = 1/4`, `m = i₀ - 1`
  have hsplit : Finset.Icc i₀ L = Finset.Icc (i₀ - 1 + 1) L := by rw [Nat.sub_add_cancel hi₀]
  have hgeom := sum_Icc_exp_neg_mul_le (γ := 1 / 4) (by norm_num) (m := i₀ - 1) L (by omega)
  rw [← hsplit] at hgeom
  have hcast : ((i₀ - 1 : ℕ) : ℝ) = (i₀ : ℝ) - 1 := by
    rw [Nat.cast_sub hi₀]
    norm_num
  rw [hcast] at hgeom
  have h4 : (1 / 4 : ℝ)⁻¹ = 4 := by norm_num
  rw [h4] at hgeom
  have hdrop : 4 * (Real.exp (-(((i₀ : ℝ) - 1) * (1 / 4))) - Real.exp (-((L : ℝ) * (1 / 4))))
      ≤ 4 * Real.exp (-(((i₀ : ℝ) - 1) * (1 / 4))) := by
    linarith [Real.exp_pos (-((L : ℝ) * (1 / 4)))]
  have hE0 : (0 : ℝ) < Real.exp ((i₀ : ℝ) * (1 / 4)) := Real.exp_pos _
  have hbound : Real.exp ((i₀ : ℝ) * (1 / 4))
        * ∑ ℓ ∈ Finset.Icc i₀ L, Real.exp (-((ℓ : ℝ) * (1 / 4)))
      ≤ 4 * Real.exp (1 / 4) := by
    calc Real.exp ((i₀ : ℝ) * (1 / 4)) * ∑ ℓ ∈ Finset.Icc i₀ L, Real.exp (-((ℓ : ℝ) * (1 / 4)))
        ≤ Real.exp ((i₀ : ℝ) * (1 / 4)) * (4 * Real.exp (-(((i₀ : ℝ) - 1) * (1 / 4)))) :=
          mul_le_mul_of_nonneg_left (le_trans hgeom hdrop) hE0.le
      _ = 4 * (Real.exp ((i₀ : ℝ) * (1 / 4)) * Real.exp (-(((i₀ : ℝ) - 1) * (1 / 4)))) := by ring
      _ = 4 * Real.exp (1 / 4) := by
          rw [← Real.exp_add]
          congr 2
          ring
  calc a i₀ ^ (1 / 4 : ℝ) * (Real.exp ((i₀ : ℝ) * (1 / 4))
        * ∑ ℓ ∈ Finset.Icc i₀ L, Real.exp (-((ℓ : ℝ) * (1 / 4))))
      ≤ a i₀ ^ (1 / 4 : ℝ) * (4 * Real.exp (1 / 4)) := mul_le_mul_of_nonneg_left hbound hc0
    _ = 4 * Real.exp (1 / 4) * a i₀ ^ (1 / 4 : ℝ) := by ring

/-! ### The first branch: `m = log log x` -/

/-- **The bracket at `m = Λ`.**  In the good range, `∑_{ℓ=1}^{L} (log_ℓΛ/Λ)^{1/4} ≤ 4e^{1/4}`.

A geometric sum of fourth roots from `RMF.exp_one_mul_iterLog_succ_le`, whose first term
`(log Λ/Λ)^{1/4}` is at most `1`. -/
theorem sum_iterLog_div_quarter_le {L : ℕ} {Λ : ℝ} (h : IterLogGood L Λ) :
    ∑ ℓ ∈ Finset.Icc 1 L, (iterLog ℓ Λ / Λ) ^ (1 / 4 : ℝ) ≤ 4 * Real.exp (1 / 4) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
    positivity
  have hΛ1 : (1 : ℝ) ≤ Λ := by simpa using h.one_le (Nat.zero_le L)
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hgeo := sum_rpow_quarter_le_of_geom (a := fun ℓ => iterLog ℓ Λ / Λ) (i₀ := 1) (L := L)
    le_rfl hL (fun ℓ _ hℓL => div_nonneg (h.pos hℓL).le hΛ0.le)
    (fun ℓ hℓ hℓL => by
      have hstep := exp_one_mul_iterLog_succ_le (h.mono (by omega : ℓ + 1 ≤ L))
      change Real.exp 1 * (iterLog (ℓ + 1) Λ / Λ) ≤ iterLog ℓ Λ / Λ
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right hstep hΛ0.le)
  refine le_trans hgeo ?_
  have h1 : iterLog 1 Λ / Λ ≤ 1 := by
    rw [div_le_one hΛ0, iterLog_one]
    linarith [Real.log_le_sub_one_of_pos hΛ0]
  have h0 : 0 ≤ iterLog 1 Λ / Λ := div_nonneg (h.pos hL).le hΛ0.le
  have hq : (iterLog 1 Λ / Λ) ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one h0 h1 (by norm_num)
  have hE : (0 : ℝ) ≤ 4 * Real.exp (1 / 4) := by positivity
  change 4 * Real.exp (1 / 4) * (iterLog 1 Λ / Λ) ^ (1 / 4 : ℝ) ≤ 4 * Real.exp (1 / 4)
  calc 4 * Real.exp (1 / 4) * (iterLog 1 Λ / Λ) ^ (1 / 4 : ℝ)
      ≤ 4 * Real.exp (1 / 4) * 1 := mul_le_mul_of_nonneg_left hq hE
    _ = 4 * Real.exp (1 / 4) := mul_one _

/-! ### The second branch: `m = 1/(2q-1)` -/

/-- **The bracket at `m = 1/δ`.**  If `RMF.IterLogGood L Λ` and `δ > 0`, then
`∑_{ℓ=1}^{L} (log_ℓΛ)^{-δ/2}·min{1, δ·log_ℓΛ}^{1/4} ≤ 4e^{1/4} + 3`.  Split at `ℓ_B`, the last level
with `δ·log_ℓΛ > 1`: at and below it each term is at most `e^{(ℓ-ℓ_B)/2}` by the tower
(`RMF.pow_exp_one_mul_iterLog_le`, `log_ℓ = exp(log_{ℓ+1})`), which `RMF.sum_exp_sub_mul_le` sums to
`3`; above it the `min` is at most `1` at `ℓ_B + 1`, and `RMF.sum_rpow_quarter_le_of_geom` sums it
to `4e^{1/4}`. -/
theorem sum_iterLog_damped_le {L : ℕ} {Λ δ : ℝ} (h : IterLogGood L Λ) (hδ0 : 0 < δ) :
    ∑ ℓ ∈ Finset.Icc 1 L, iterLog ℓ Λ ^ (-(δ / 2)) * min 1 (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ)
      ≤ 4 * Real.exp (1 / 4) + 3 := by
  classical
  obtain ⟨ℓB, hℓBdef⟩ : ∃ n : ℕ,
      n = ((Finset.Icc 1 L).filter (fun ℓ => 1 < δ * iterLog ℓ Λ)).sup id := ⟨_, rfl⟩
  have hℓBL : ℓB ≤ L := by
    rw [hℓBdef]
    exact Finset.sup_le fun b hb => (Finset.mem_Icc.1 (Finset.mem_filter.1 hb).1).2
  -- above `ℓB`, `δ·log_ℓΛ ≤ 1`
  have habove : ∀ ℓ, ℓB < ℓ → ℓ ≤ L → δ * iterLog ℓ Λ ≤ 1 := by
    intro ℓ hlt hle
    by_contra hcon
    push Not at hcon
    have hmem : ℓ ∈ (Finset.Icc 1 L).filter (fun ℓ => 1 < δ * iterLog ℓ Λ) :=
      Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, hle⟩, hcon⟩
    have hsup := Finset.le_sup (f := id) hmem
    rw [← hℓBdef] at hsup
    simp only [id] at hsup
    omega
  -- at `ℓB`, when it is a level, `δ·log_ℓΛ > 1`
  have hat : 1 ≤ ℓB → 1 < δ * iterLog ℓB Λ := by
    intro h1
    have hne : ((Finset.Icc 1 L).filter (fun ℓ => 1 < δ * iterLog ℓ Λ)).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.sup_empty] at hℓBdef
      have : ℓB = 0 := hℓBdef
      omega
    obtain ⟨b, hb, hbeq⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [← hℓBdef] at hbeq
    simp only [id] at hbeq
    rw [hbeq]
    exact (Finset.mem_filter.1 hb).2
  -- at and below `ℓB`: the damping, through the tower
  have hlow : ∑ ℓ ∈ Finset.Icc 1 ℓB,
      iterLog ℓ Λ ^ (-(δ / 2)) * min 1 (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ) ≤ 3 := by
    have hbnd : ∀ ℓ ∈ Finset.Icc 1 ℓB,
        iterLog ℓ Λ ^ (-(δ / 2)) * min 1 (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ)
          ≤ Real.exp (((ℓ : ℝ) - (ℓB : ℝ)) * (1 / 2)) := by
      intro ℓ hℓ
      rw [Finset.mem_Icc] at hℓ
      have hℓL : ℓ ≤ L := le_trans hℓ.2 hℓBL
      have hpos : 0 < iterLog ℓ Λ := h.pos hℓL
      have hone : 1 ≤ iterLog ℓ Λ := h.one_le hℓL
      have hx0 : 0 ≤ δ * iterLog ℓ Λ := mul_nonneg hδ0.le hpos.le
      have hmin0 : 0 ≤ min 1 (δ * iterLog ℓ Λ) := le_min zero_le_one hx0
      have hmin1 : min 1 (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ) ≤ 1 :=
        Real.rpow_le_one hmin0 (min_le_left _ _) (by norm_num)
      have hdamp0 : 0 ≤ iterLog ℓ Λ ^ (-(δ / 2)) := Real.rpow_nonneg hpos.le _
      have hprod : iterLog ℓ Λ ^ (-(δ / 2)) * min 1 (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ)
          ≤ iterLog ℓ Λ ^ (-(δ / 2)) := by
        calc iterLog ℓ Λ ^ (-(δ / 2)) * min 1 (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ)
            ≤ iterLog ℓ Λ ^ (-(δ / 2)) * 1 := mul_le_mul_of_nonneg_left hmin1 hdamp0
          _ = iterLog ℓ Λ ^ (-(δ / 2)) := mul_one _
      refine le_trans hprod ?_
      rcases Nat.lt_or_ge ℓ ℓB with hlt | hge
      · -- strictly below `ℓB`
        have hgoodB : IterLogGood ℓB Λ := h.mono hℓBL
        have hdec := pow_exp_one_mul_iterLog_le hgoodB (ℓB - (ℓ + 1)) (by omega)
        rw [show ℓB - (ℓB - (ℓ + 1)) = ℓ + 1 by omega] at hdec
        have hδB := hat (by omega)
        -- `e^{ℓB-ℓ-1} ≥ ℓB - ℓ`
        have hexp : (ℓB : ℝ) - ℓ ≤ Real.exp 1 ^ (ℓB - (ℓ + 1)) := by
          have h1 : Real.exp 1 ^ (ℓB - (ℓ + 1)) = Real.exp ((ℓB - (ℓ + 1) : ℕ) : ℝ) := by
            rw [← Real.exp_nat_mul, mul_one]
          have h3 : (((ℓB - (ℓ + 1) : ℕ) : ℝ)) = (ℓB : ℝ) - ℓ - 1 := by
            rw [Nat.cast_sub (by omega)]
            push_cast
            ring
          rw [h1]
          have h2 := Real.add_one_le_exp (((ℓB - (ℓ + 1) : ℕ) : ℝ))
          rw [h3] at h2 ⊢
          linarith
        -- so `δ·log_{ℓ+1}Λ ≥ ℓB - ℓ`
        have hkey : (ℓB : ℝ) - ℓ ≤ δ * iterLog (ℓ + 1) Λ := by
          have hE0 : (0 : ℝ) ≤ Real.exp 1 ^ (ℓB - (ℓ + 1)) := by positivity
          calc (ℓB : ℝ) - ℓ ≤ Real.exp 1 ^ (ℓB - (ℓ + 1)) := hexp
            _ ≤ Real.exp 1 ^ (ℓB - (ℓ + 1)) * (δ * iterLog ℓB Λ) :=
                le_mul_of_one_le_right hE0 hδB.le
            _ = δ * (Real.exp 1 ^ (ℓB - (ℓ + 1)) * iterLog ℓB Λ) := by ring
            _ ≤ δ * iterLog (ℓ + 1) Λ := mul_le_mul_of_nonneg_left hdec hδ0.le
        -- the tower: `(log_ℓΛ)^{-δ/2} = exp(-(δ/2)·log_{ℓ+1}Λ)`
        rw [Real.rpow_def_of_pos hpos, show Real.log (iterLog ℓ Λ) = iterLog (ℓ + 1) Λ from rfl]
        refine Real.exp_le_exp.2 ?_
        have hlin : iterLog (ℓ + 1) Λ * (-(δ / 2)) = -(1 / 2) * (δ * iterLog (ℓ + 1) Λ) := by ring
        rw [hlin]
        linarith
      · -- at `ℓB`, where the bound is `exp 0 = 1`
        have heq : ℓ = ℓB := le_antisymm hℓ.2 hge
        subst heq
        rw [sub_self, zero_mul, Real.exp_zero]
        exact Real.rpow_le_one_of_one_le_of_nonpos hone (by linarith)
    refine le_trans (Finset.sum_le_sum hbnd) ?_
    have hs := sum_exp_sub_mul_le (α := 1 / 2) (by norm_num) ℓB
    have h2 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
    rw [h2] at hs
    linarith
  -- above `ℓB`: the geometric part
  have hhigh : ∑ ℓ ∈ Finset.Icc (ℓB + 1) L,
      iterLog ℓ Λ ^ (-(δ / 2)) * min 1 (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ)
        ≤ 4 * Real.exp (1 / 4) := by
    rcases Nat.lt_or_ge ℓB L with hlt | hge
    · have hbnd : ∀ ℓ ∈ Finset.Icc (ℓB + 1) L,
          iterLog ℓ Λ ^ (-(δ / 2)) * min 1 (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ)
            ≤ (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ) := by
        intro ℓ hℓ
        rw [Finset.mem_Icc] at hℓ
        have hpos : 0 < iterLog ℓ Λ := h.pos hℓ.2
        have hone : 1 ≤ iterLog ℓ Λ := h.one_le hℓ.2
        have hx0 : 0 ≤ δ * iterLog ℓ Λ := mul_nonneg hδ0.le hpos.le
        have hdamp : iterLog ℓ Λ ^ (-(δ / 2)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hone (by linarith)
        have hmin : min 1 (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ) ≤ (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (le_min zero_le_one hx0) (min_le_right _ _) (by norm_num)
        have hmin0 : 0 ≤ min 1 (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ) :=
          Real.rpow_nonneg (le_min zero_le_one hx0) _
        calc iterLog ℓ Λ ^ (-(δ / 2)) * min 1 (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ)
            ≤ 1 * min 1 (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_right hdamp hmin0
          _ ≤ (δ * iterLog ℓ Λ) ^ (1 / 4 : ℝ) := by rw [one_mul]; exact hmin
      refine le_trans (Finset.sum_le_sum hbnd) ?_
      have hgeo := sum_rpow_quarter_le_of_geom (a := fun ℓ => δ * iterLog ℓ Λ) (i₀ := ℓB + 1)
        (L := L) (by omega) (by omega)
        (fun ℓ _ hℓL => mul_nonneg hδ0.le (h.pos hℓL).le)
        (fun ℓ hℓ hℓL => by
          have hstep := exp_one_mul_iterLog_succ_le (h.mono (by omega : ℓ + 1 ≤ L))
          change Real.exp 1 * (δ * iterLog (ℓ + 1) Λ) ≤ δ * iterLog ℓ Λ
          calc Real.exp 1 * (δ * iterLog (ℓ + 1) Λ) = δ * (Real.exp 1 * iterLog (ℓ + 1) Λ) := by
                ring
            _ ≤ δ * iterLog ℓ Λ := mul_le_mul_of_nonneg_left hstep hδ0.le)
      refine le_trans hgeo ?_
      have hfirst : δ * iterLog (ℓB + 1) Λ ≤ 1 := habove (ℓB + 1) (by omega) (by omega)
      have hq : (δ * iterLog (ℓB + 1) Λ) ^ (1 / 4 : ℝ) ≤ 1 :=
        Real.rpow_le_one (mul_nonneg hδ0.le (h.pos (by omega : ℓB + 1 ≤ L)).le) hfirst
          (by norm_num)
      have hE : (0 : ℝ) ≤ 4 * Real.exp (1 / 4) := by positivity
      change 4 * Real.exp (1 / 4) * (δ * iterLog (ℓB + 1) Λ) ^ (1 / 4 : ℝ) ≤ 4 * Real.exp (1 / 4)
      calc 4 * Real.exp (1 / 4) * (δ * iterLog (ℓB + 1) Λ) ^ (1 / 4 : ℝ)
          ≤ 4 * Real.exp (1 / 4) * 1 := mul_le_mul_of_nonneg_left hq hE
        _ = 4 * Real.exp (1 / 4) := mul_one _
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      positivity
  -- the two halves are the whole sum
  have hIoc1 : Finset.Icc 1 L = Finset.Ioc 0 L := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hIoc2 : Finset.Icc 1 ℓB = Finset.Ioc 0 ℓB := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hIoc3 : Finset.Icc (ℓB + 1) L = Finset.Ioc ℓB L := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIoc1, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ℓB) hℓBL, ← hIoc2, ← hIoc3]
  linarith

end RMF
