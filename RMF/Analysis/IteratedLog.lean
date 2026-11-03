/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The iterated logarithm

Harper's Probability Lemma 1 is an induction over the *iterated* logarithm: the barrier
`a + 10 log j` is frozen at time `(log_k n)^20`, and the induction proceeds by increasing `k`.
The error at level `k` is `1/(√n log_k² n)`, so the total error is `∑_{i ≤ k} 1/log_i² n`, which is
dominated by its last term — the point being that the number of levels is `log* n` rather than
`log n`, so the accumulated error is genuinely negligible.

Following Harper we set `log₀ x = x` and `log_{k+1} x = log (log_k x)`, so that `log₀ n = n` and
the condition defining the range of the induction is `log_k n ≥ a/1000`.

## Positivity has to be carried, not derived

The tempting shortcut is to assume only `1 ≤ log_k n` and recover the earlier iterates from it.
**That is false.**  Mathlib's `Real.log` is *even* — `Real.log_eq_zero` reads
`log x = 0 ↔ x = 0 ∨ x = 1 ∨ x = -1` — so `log (-e) = 1`, and from `1 ≤ log t` one may conclude
only `e ≤ |t|`.  The sign is genuinely lost.

So the good range is carried as a hypothesis, `RMF.IterLogGood k x`, saying that *every* iterate up
to level `k` is at least `1`.  In Harper's setting this is automatic — `n` is enormous and the
condition of the induction is `log_k n ≥ a/1000` with `a` large — but it is a hypothesis of the
lemmas, not a consequence of the last iterate alone.
-/

open Real

namespace RMF

/-- The `k`-fold iterated logarithm, with Harper's convention `log₀ x = x`. -/
noncomputable def iterLog : ℕ → ℝ → ℝ
  | 0, x => x
  | (k + 1), x => Real.log (iterLog k x)

@[simp] lemma iterLog_zero (x : ℝ) : iterLog 0 x = x := rfl

@[simp] lemma iterLog_succ (k : ℕ) (x : ℝ) : iterLog (k + 1) x = Real.log (iterLog k x) := rfl

lemma iterLog_one (x : ℝ) : iterLog 1 x = Real.log x := rfl

/-- The range in which the iterated logarithm is meaningful: every iterate up to level `k` is at
least `1`.  Carried as a hypothesis because it cannot be recovered from the last iterate — see the
module docstring. -/
def IterLogGood (k : ℕ) (x : ℝ) : Prop := ∀ i ≤ k, 1 ≤ iterLog i x

lemma IterLogGood.mono {k i : ℕ} {x : ℝ} (hik : i ≤ k) (h : IterLogGood k x) :
    IterLogGood i x := fun j hj => h j (hj.trans hik)

lemma IterLogGood.one_le {k i : ℕ} {x : ℝ} (h : IterLogGood k x) (hik : i ≤ k) :
    1 ≤ iterLog i x := h i hik

lemma IterLogGood.pos {k i : ℕ} {x : ℝ} (h : IterLogGood k x) (hik : i ≤ k) :
    0 < iterLog i x := lt_of_lt_of_le one_pos (h i hik)

/-- The iterated logarithm is non-increasing in `k`, within the good range. -/
lemma iterLog_succ_le {k : ℕ} {x : ℝ} (h : IterLogGood (k + 1) x) :
    iterLog (k + 1) x ≤ iterLog k x := by
  rw [iterLog_succ]
  linarith [Real.log_le_sub_one_of_pos (h.pos (Nat.le_succ k))]

/-- The iterated logarithm is antitone in `k`, within the good range.  This is what makes the
error `∑_{i ≤ k} 1/log_i² n` dominated by its last term. -/
lemma iterLog_le_iterLog {k i : ℕ} {x : ℝ} (hik : i ≤ k) (h : IterLogGood k x) :
    iterLog k x ≤ iterLog i x := by
  induction k with
  | zero => rw [Nat.le_zero.1 hik]
  | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hik) with hlt | heq
      · exact le_trans (iterLog_succ_le h)
          (ih (Nat.lt_succ_iff.1 hlt) (h.mono (Nat.le_succ k)))
      · rw [heq]

/-! ### Geometric decay, and the telescope

Harper needs `∑_{i≤k} 1/log_i² n ≪ 1`, the sum being dominated by its last term.  Geometric decay
is enough: `t_i = exp(t_{i+1})` by definition, and `exp y ≥ e·y`, so each step down multiplies by
at least `e`. -/

/-- **A numeral lower bound for `e^k`.**  If `N ≤ c^k` for a rational `c ≤ e`, then `N ≤ e^k`. -/
lemma le_exp_natCast_of_le_pow {N c : ℝ} {k : ℕ} (hc0 : 0 ≤ c) (hc : c ≤ Real.exp 1)
    (h : N ≤ c ^ k) : N ≤ Real.exp (k : ℝ) := by
  refine h.trans ((pow_le_pow_left₀ hc0 hc k).trans (le_of_eq ?_))
  rw [← Real.exp_nat_mul]
  ring_nf

/-- The upper companion: if `c^k ≤ N` for a rational `c ≥ e`, then `e^k ≤ N`. -/
lemma exp_natCast_le_of_pow_le {N c : ℝ} {k : ℕ} (hc : Real.exp 1 ≤ c) (h : c ^ k ≤ N) :
    Real.exp (k : ℝ) ≤ N := by
  refine le_trans (le_of_eq ?_) ((pow_le_pow_left₀ (Real.exp_pos 1).le hc k).trans h)
  rw [← Real.exp_nat_mul]
  ring_nf

/-- `e·y ≤ exp y`, for every real `y`.  Immediate from `y ≤ exp (y - 1)`. -/
lemma exp_one_mul_le_exp (y : ℝ) : Real.exp 1 * y ≤ Real.exp y := by
  have h : y ≤ Real.exp (y - 1) := by linarith [Real.add_one_le_exp (y - 1)]
  calc Real.exp 1 * y ≤ Real.exp 1 * Real.exp (y - 1) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos 1).le
    _ = Real.exp y := by rw [← Real.exp_add]; ring_nf

/-- **One step of the decay.**  Going down one level multiplies by at least `e`. -/
lemma exp_one_mul_iterLog_succ_le {k : ℕ} {x : ℝ} (h : IterLogGood (k + 1) x) :
    Real.exp 1 * iterLog (k + 1) x ≤ iterLog k x := by
  have hpos : 0 < iterLog k x := h.pos (Nat.le_succ k)
  calc Real.exp 1 * iterLog (k + 1) x ≤ Real.exp (iterLog (k + 1) x) := exp_one_mul_le_exp _
    _ = iterLog k x := by rw [iterLog_succ, Real.exp_log hpos]

/-- **Geometric decay.**  `log_{k-m} n ≥ e^m · log_k n`. -/
lemma pow_exp_one_mul_iterLog_le {k : ℕ} {x : ℝ} (h : IterLogGood k x) :
    ∀ m ≤ k, Real.exp 1 ^ m * iterLog k x ≤ iterLog (k - m) x := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
      intro hm
      have hstep := ih (by omega)
      have hidx : k - m = (k - (m + 1)) + 1 := by omega
      have hgood : IterLogGood ((k - (m + 1)) + 1) x := by
        rw [← hidx]; exact h.mono (by omega)
      have hone := exp_one_mul_iterLog_succ_le hgood
      rw [← hidx] at hone
      calc Real.exp 1 ^ (m + 1) * iterLog k x
          = Real.exp 1 * (Real.exp 1 ^ m * iterLog k x) := by ring
        _ ≤ Real.exp 1 * iterLog (k - m) x :=
            mul_le_mul_of_nonneg_left hstep (Real.exp_pos 1).le
        _ ≤ iterLog (k - (m + 1)) x := hone

/-- The convergence factor of the telescope is positive: `e² > 1`. -/
lemma one_sub_inv_exp_sq_pos : (0 : ℝ) < 1 - (Real.exp 1 ^ 2)⁻¹ := by
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hlt : (Real.exp 1 ^ 2)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]; right; exact one_lt_pow₀ he1 (by norm_num)
  linarith

/-- **The telescope converges.**  The accumulated error of Harper’s induction,
`∑_{i≤k} 1/log_i² n`, is at most a constant times its last term.  With `log_k n ≥ a/1000` at the
terminal level this is `≪ (1000/a)²`, which is what the endgame of Probability Result 1 needs. -/
lemma sum_inv_sq_iterLog_le {k : ℕ} {x : ℝ} (h : IterLogGood k x) :
    ∑ i ∈ Finset.range (k + 1), 1 / iterLog i x ^ 2
      ≤ (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ / iterLog k x ^ 2 := by
  have hr0 : (0 : ℝ) < (Real.exp 1 ^ 2)⁻¹ := by positivity
  have hr1 : (Real.exp 1 ^ 2)⁻¹ < 1 := by linarith [one_sub_inv_exp_sq_pos]
  have htk : 1 ≤ iterLog k x := h.one_le le_rfl
  have htkpos : (0 : ℝ) < iterLog k x := by linarith
  set r : ℝ := (Real.exp 1 ^ 2)⁻¹ with hrdef
  -- termwise: `1/t_i² ≤ r^{k-i}/t_k²`
  have hterm : ∀ i ∈ Finset.range (k + 1),
      1 / iterLog i x ^ 2 ≤ r ^ (k - i) / iterLog k x ^ 2 := by
    intro i hi
    have hik : i ≤ k := by simpa using Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hdec := pow_exp_one_mul_iterLog_le h (k - i) (by omega)
    rw [show k - (k - i) = i from by omega] at hdec
    have hlow : (0 : ℝ) < Real.exp 1 ^ (k - i) * iterLog k x := by positivity
    have hipos : (0 : ℝ) < iterLog i x := lt_of_lt_of_le hlow hdec
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (Real.exp 1 ^ (k - i) * iterLog k x) ^ 2 ≤ iterLog i x ^ 2 := by
      exact pow_le_pow_left₀ hlow.le hdec 2
    have hrpow : r ^ (k - i) * (Real.exp 1 ^ (k - i)) ^ 2 = 1 := by
      have h2 : (Real.exp 1 ^ (k - i)) ^ 2 = (Real.exp 1 ^ 2) ^ (k - i) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [hrdef, h2, ← mul_pow, inv_mul_cancel₀ (by positivity), one_pow]
    have hmul : r ^ (k - i) * ((Real.exp 1 ^ (k - i) * iterLog k x) ^ 2)
        ≤ r ^ (k - i) * iterLog i x ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    have hexpand : r ^ (k - i) * ((Real.exp 1 ^ (k - i) * iterLog k x) ^ 2)
        = (r ^ (k - i) * (Real.exp 1 ^ (k - i)) ^ 2) * iterLog k x ^ 2 := by ring
    rw [hexpand, hrpow, one_mul] at hmul
    linarith
  calc ∑ i ∈ Finset.range (k + 1), 1 / iterLog i x ^ 2
      ≤ ∑ i ∈ Finset.range (k + 1), r ^ (k - i) / iterLog k x ^ 2 := Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (k + 1), r ^ (k - i)) / iterLog k x ^ 2 := by
        simp [div_eq_mul_inv, ← Finset.sum_mul]
    _ = (∑ i ∈ Finset.range (k + 1), r ^ i) / iterLog k x ^ 2 := by
        congr 1
        simpa using Finset.sum_range_reflect (fun i => r ^ i) (k + 1)
    _ ≤ (1 - r)⁻¹ / iterLog k x ^ 2 := by
        have h1r : (0 : ℝ) < 1 - r := by linarith
        have hgeo : ∑ i ∈ Finset.range (k + 1), r ^ i = (1 - r ^ (k + 1)) / (1 - r) := by
          rw [geom_sum_eq (by linarith : r ≠ 1),
            div_eq_div_iff (ne_of_lt (by linarith : r - 1 < 0)) (ne_of_gt h1r)]
          ring
        have hle : ∑ i ∈ Finset.range (k + 1), r ^ i ≤ (1 - r)⁻¹ := by
          rw [hgeo, inv_eq_one_div, div_le_div_iff_of_pos_right h1r]
          linarith [pow_nonneg hr0.le (k + 1)]
        exact div_le_div_of_nonneg_right hle (by positivity)

/-! ### The terminal level

Harper’s endgame chooses `k` as large as possible with `log_k n ≥ a/1000`.  That such a `k` exists
is not quite formal: the levels have to run out.  They do, and the reason is
`RMF.pow_exp_one_mul_iterLog_le` — inside the good range `x ≥ e^k · log_k x ≥ e^k`, so no more than
`log x` levels can be good. -/

/-- **The terminal level of the induction.**  For `1 ≤ b ≤ x` there is a largest `k` with every
iterate down to level `k` at least `b`.  Maximality gives `log_{k+1} x < b`, which is what collapses
Harper’s frozen barrier to a constant one.

The hypothesis is on *every* iterate, not just the `k`-th: `Real.log` is even, so `b ≤ log_k x`
alone does not propagate downwards. -/
lemma exists_maximal_iterLog_ge {x b : ℝ} (hb : 1 ≤ b) (hx : b ≤ x) :
    ∃ k : ℕ, (∀ i ≤ k, b ≤ iterLog i x) ∧ iterLog (k + 1) x < b := by
  classical
  set P : ℕ → Prop := fun K => ∀ i ≤ K, b ≤ iterLog i x with hPdef
  have hP0 : P 0 := by
    intro i hi
    rw [Nat.le_zero.1 hi, iterLog_zero]
    exact hx
  -- inside the good range the levels run out: `K + 1 ≤ e^K · log_K x ≤ x`
  have hbound : ∀ K, P K → (K : ℝ) < x := by
    intro K hK
    have hgood : IterLogGood K x := fun i hi => le_trans hb (hK i hi)
    have hstep := pow_exp_one_mul_iterLog_le hgood K le_rfl
    rw [Nat.sub_self, iterLog_zero] at hstep
    have h1 : (1 : ℝ) ≤ iterLog K x := hgood.one_le le_rfl
    have h2 : Real.exp 1 ^ K ≤ Real.exp 1 ^ K * iterLog K x :=
      le_mul_of_one_le_right (by positivity) h1
    have h3 : (K : ℝ) + 1 ≤ Real.exp 1 ^ K := by
      have hE : Real.exp ((K : ℝ)) = Real.exp 1 ^ K := by
        rw [← Real.exp_nat_mul, mul_one]
      calc (K : ℝ) + 1 ≤ Real.exp ((K : ℝ)) := Real.add_one_le_exp _
        _ = Real.exp 1 ^ K := hE
    linarith
  set B : ℕ := ⌈x⌉₊ with hBdef
  refine ⟨Nat.findGreatest P B, ?_, ?_⟩
  · exact Nat.findGreatest_spec (Nat.zero_le B) hP0
  · have hPk : P (Nat.findGreatest P B) := Nat.findGreatest_spec (Nat.zero_le B) hP0
    have hkB : Nat.findGreatest P B < B := by
      have h1 := hbound _ hPk
      have h2 : x ≤ (B : ℝ) := Nat.le_ceil x
      exact_mod_cast lt_of_lt_of_le h1 h2
    have hnot : ¬P (Nat.findGreatest P B + 1) :=
      Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hkB
    have hnot2 : ¬ ∀ i ≤ Nat.findGreatest P B + 1, b ≤ iterLog i x := hnot
    push Not at hnot2
    obtain ⟨i, hi, hlt⟩ := hnot2
    rcases Nat.lt_or_ge i (Nat.findGreatest P B + 1) with hcase | hcase
    · exact absurd (hPk i (by omega)) (not_le.2 hlt)
    · rwa [show i = Nat.findGreatest P B + 1 from by omega] at hlt

end RMF
