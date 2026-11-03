/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ExtendedEulerRatio
import RMF.Weighted.LowerDamped
import RMF.Analysis.FracMellinExplicit
import RMF.Reduction.Periodisation
import RMF.Probability.RestrictedFirstMoment
import RMF.EulerProduct.Block
import RMF.NumberTheory.LogPrimeSum
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import LeanCert.Tactic.IntervalAuto

/-!
# The extended sum's explicit lower bound: the kernel `ζ(2s)/s`

For Rademacher `X`, almost surely
`|F^e_N(s)|² = |F_N(s)|²∏_{p<N}|1 - p^{-2s}|^{-2}` (`RMF.ae_normSq_randomEulerProduct_compMult_eq`),
so on the line `s = ½ + σ + it` the extended sum's line integrand is the weighted sum's Euler
product against the deterministic kernel `K_N(σ, t) = ∏_{p<N}|1 - p^{-2s}|^{-2}/|s|²`
(`RMF.zetaKernel`): `lineDivSq (½ + σ) X N ω t = |F_N(s)|²K_N(σ, t)`
(`RMF.ae_lineDivSq_eq_mul_zetaKernel`).  The weighted sum's kernel is `(σ² + t²)⁻¹`.

* **The Euler tail**: `∑_{N≤p<M} p^{-1-2σ} ≤ 2(1 + 2σ log 2)e^{-2σ log N}/(σ log N)` for `σ > 0`,
  `N ≥ 2`, by dyadic blocks and `θ(y) ≤ y log 4` (`RMF.sum_primesIco_rpow_le_of_pos`); so
  `≤ (2/A + 4)e^{-2A}` for `σ log N ≥ A > 0` (`RMF.sum_primesIco_rpow_le_of_le_mul_log`).
* **Against `ζ(2s)`**: `∏_{p<N}(1 - p^{-2s})⁻¹ = ζ(2s)∏_{p≥N}(1 - p^{-2s})` (Mathlib's Euler
  product as a limit), so `e^{-2τ}|ζ(2s)| ≤ |∏_{p<N}(1 - p^{-2s})⁻¹| ≤ e^{τ}|ζ(2s)|`, `τ` the tail
  (`RMF.norm_prod_inv_bounds`).
* **On the windows**: with `ζ(2s)/s = 1/(s - ½) - φ̂(s)` (`RMF.fracMellin_eq_zeta`) and
  `|φ̂| ≤ 0.8456`, `(1 - 10⁻⁶)(σ² + t²)⁻¹ ≤ K_N(σ, t)` for `σ log N ≥ 16` and
  `σ² + t² ≤ 10⁻¹⁶` (`RMF.le_zetaKernel_of_window`).
* **Everywhere**: `K_N(σ, t) ≤ 2.01((σ² + t²)⁻¹ + |φ̂(s)|²)` for `σ log N ≥ 4`
  (`RMF.zetaKernel_le_decomp`).
* **In mean**: `∫_ℝ K_N(σ, t) dt ≤ π/σ`, the weighted sum's `∫(σ² + t²)⁻¹`, for `σ > 0`
  (`RMF.integral_zetaKernel_le`): Parseval (`RMF.integral_normSq_partialSum_eq_line`) for the
  `N`-smooth numbers at the abscissa `1 + 2σ`, whose count up to `u` is at most `u`.
-/

open MeasureTheory

namespace RMF

/-! ### The Euler tail -/

/-- A sum over the primes of `[a, c)` splits at `b`, for `a ≤ b ≤ c`. -/
lemma sum_primesIco_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (f : ℕ → ℝ) :
    ∑ p ∈ primesIco a c, f p = ∑ p ∈ primesIco a b, f p + ∑ p ∈ primesIco b c, f p := by
  have hsub : ∀ {u v : ℕ}, u ≤ v → ∑ p ∈ primesIco u v, f p
      = ∑ p ∈ Nat.primesBelow v, f p - ∑ p ∈ Nat.primesBelow u, f p := fun huv =>
    Finset.sum_sdiff_eq_sub (primesBelow_mono huv)
  rw [hsub (hab.trans hbc), hsub hab, hsub hbc]
  ring

/-- **A dyadic block of the Euler tail**: for `A ≥ 2` and `σ ≥ 0`,
`∑_{A≤p<2A} p^{-1-2σ} ≤ 2 log 4·A^{-2σ}/log A`, from `θ(2A) ≤ 2A log 4` and `log p ≥ log A`. -/
lemma sum_primesIco_two_mul_rpow_le {A : ℕ} (hA : 2 ≤ A) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∑ p ∈ primesIco A (2 * A), (p : ℝ) ^ (-(1 + 2 * σ))
      ≤ 2 * Real.log 4 * (A : ℝ) ^ (-(2 * σ)) / Real.log A := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hA1 : (1 : ℝ) < A := by exact_mod_cast (by omega : 1 < A)
  have hlogA : 0 < Real.log A := Real.log_pos hA1
  set c : ℝ := (A : ℝ) ^ (-(1 + 2 * σ)) / Real.log A with hcdef
  have hc0 : 0 ≤ c := div_nonneg (Real.rpow_nonneg hA0.le _) hlogA.le
  -- termwise: `p^{-1-2σ} ≤ log p·A^{-1-2σ}/log A`
  have hterm : ∀ p ∈ primesIco A (2 * A), (p : ℝ) ^ (-(1 + 2 * σ)) ≤ Real.log p * c := by
    intro p hp
    obtain ⟨-, hAp, -⟩ := mem_primesIco.1 hp
    have hAp' : (A : ℝ) ≤ p := by exact_mod_cast hAp
    have h1 : (p : ℝ) ^ (-(1 + 2 * σ)) ≤ (A : ℝ) ^ (-(1 + 2 * σ)) :=
      Real.rpow_le_rpow_of_nonpos hA0 hAp' (by linarith)
    have h2 : Real.log A ≤ Real.log p := Real.log_le_log hA0 hAp'
    have h3 : 1 ≤ Real.log p / Real.log A := by
      rw [le_div_iff₀ hlogA]
      linarith
    have h0 : 0 ≤ (A : ℝ) ^ (-(1 + 2 * σ)) := Real.rpow_nonneg hA0.le _
    calc (p : ℝ) ^ (-(1 + 2 * σ)) ≤ (A : ℝ) ^ (-(1 + 2 * σ)) := h1
      _ ≤ Real.log p / Real.log A * (A : ℝ) ^ (-(1 + 2 * σ)) := le_mul_of_one_le_left h0 h3
      _ = Real.log p * c := by rw [hcdef]; ring
  -- `∑_{A≤p<2A} log p ≤ θ(2A) ≤ 2A log 4`
  have hθ : ∑ p ∈ primesIco A (2 * A), Real.log p ≤ Real.log 4 * (2 * A) := by
    have h := sum_log_prime_le (x := ((2 * A : ℕ) : ℝ)) (Nat.cast_nonneg _)
    rw [Nat.floor_natCast] at h
    have hsub : primesIco A (2 * A) ⊆ {p ∈ Finset.Ioc 0 (2 * A) | p.Prime} := by
      intro p hp
      obtain ⟨hpr, -, hp2⟩ := mem_primesIco.1 hp
      exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hpr.pos, hp2.le⟩, hpr⟩
    have h2 := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
      Real.log_natCast_nonneg p) h
    push_cast at h2
    exact h2
  have hAA : (A : ℝ) ^ (-(1 + 2 * σ)) * A = (A : ℝ) ^ (-(2 * σ)) := by
    rw [show -(1 + 2 * σ) = -(2 * σ) + -1 by ring, Real.rpow_add hA0, Real.rpow_neg_one,
      mul_assoc, inv_mul_cancel₀ hA0.ne', mul_one]
  calc ∑ p ∈ primesIco A (2 * A), (p : ℝ) ^ (-(1 + 2 * σ))
      ≤ ∑ p ∈ primesIco A (2 * A), Real.log p * c := Finset.sum_le_sum hterm
    _ = (∑ p ∈ primesIco A (2 * A), Real.log p) * c := by rw [Finset.sum_mul]
    _ ≤ Real.log 4 * (2 * A) * c := mul_le_mul_of_nonneg_right hθ hc0
    _ = 2 * Real.log 4 * ((A : ℝ) ^ (-(1 + 2 * σ)) * A) / Real.log A := by rw [hcdef]; ring
    _ = 2 * Real.log 4 * (A : ℝ) ^ (-(2 * σ)) / Real.log A := by rw [hAA]

/-- The Euler tail up to `2^J N`, block by block:
`∑_{N≤p<2^J N} p^{-1-2σ} ≤ (2 log 4/log N)∑_{j<J}(2^j N)^{-2σ}`. -/
lemma sum_primesIco_pow_two_mul_rpow_le {N : ℕ} (hN : 2 ≤ N) {σ : ℝ} (hσ : 0 ≤ σ) (J : ℕ) :
    ∑ p ∈ primesIco N (2 ^ J * N), (p : ℝ) ^ (-(1 + 2 * σ))
      ≤ 2 * Real.log 4 / Real.log N
          * ∑ j ∈ Finset.range J, ((2 ^ j * N : ℕ) : ℝ) ^ (-(2 * σ)) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  induction J with
  | zero =>
    rw [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero]
    refine le_of_eq (Finset.sum_eq_zero fun p hp => ?_)
    obtain ⟨-, h1, h2⟩ := mem_primesIco.1 hp
    omega
  | succ J ih =>
    have hNJ : N ≤ 2 ^ J * N := Nat.le_mul_of_pos_left N (by positivity)
    have hA : 2 ≤ 2 ^ J * N := le_trans hN hNJ
    have h2 : 2 ^ (J + 1) * N = 2 * (2 ^ J * N) := by ring
    have hsplit := sum_primesIco_split (f := fun p : ℕ => (p : ℝ) ^ (-(1 + 2 * σ))) hNJ
      (by omega : 2 ^ J * N ≤ 2 * (2 ^ J * N))
    have hblock := sum_primesIco_two_mul_rpow_le hA hσ
    have hlog : Real.log N ≤ Real.log ((2 ^ J * N : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (by exact_mod_cast hNJ)
    have hA0 : (0 : ℝ) < ((2 ^ J * N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 ^ J * N)
    have hpow0 : 0 ≤ ((2 ^ J * N : ℕ) : ℝ) ^ (-(2 * σ)) := Real.rpow_nonneg hA0.le _
    have hblock' : 2 * Real.log 4 * ((2 ^ J * N : ℕ) : ℝ) ^ (-(2 * σ))
          / Real.log ((2 ^ J * N : ℕ) : ℝ)
        ≤ 2 * Real.log 4 / Real.log N * ((2 ^ J * N : ℕ) : ℝ) ^ (-(2 * σ)) := by
      have hl4 : 0 ≤ 2 * Real.log 4 := by positivity
      calc 2 * Real.log 4 * ((2 ^ J * N : ℕ) : ℝ) ^ (-(2 * σ)) / Real.log ((2 ^ J * N : ℕ) : ℝ)
          ≤ 2 * Real.log 4 * ((2 ^ J * N : ℕ) : ℝ) ^ (-(2 * σ)) / Real.log N :=
            div_le_div_of_nonneg_left (mul_nonneg hl4 hpow0) hlogN hlog
        _ = 2 * Real.log 4 / Real.log N * ((2 ^ J * N : ℕ) : ℝ) ^ (-(2 * σ)) := by ring
    rw [h2, hsplit, Finset.sum_range_succ, mul_add]
    linarith

/-- The geometric sum: `∑_{j<J}(2^j N)^{-2σ} ≤ N^{-2σ}(1 + u)/u`, `u = 2σ log 2`, for `σ > 0`. -/
lemma sum_range_two_pow_mul_rpow_le {N : ℕ} (hN : 1 ≤ N) {σ : ℝ} (hσ : 0 < σ) (J : ℕ) :
    ∑ j ∈ Finset.range J, ((2 ^ j * N : ℕ) : ℝ) ^ (-(2 * σ))
      ≤ (N : ℝ) ^ (-(2 * σ)) * ((1 + 2 * σ * Real.log 2) / (2 * σ * Real.log 2)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set r : ℝ := (2 : ℝ) ^ (-(2 * σ)) with hrdef
  set u : ℝ := 2 * σ * Real.log 2 with hudef
  have hu : 0 < u := by rw [hudef]; have := Real.log_pos one_lt_two; positivity
  have hr : r = Real.exp (-u) := by
    rw [hrdef, hudef, Real.rpow_def_of_pos two_pos]
    congr 1
    ring
  have hr0 : 0 ≤ r := by rw [hr]; exact (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hr]; exact Real.exp_lt_one_iff.2 (by linarith)
  -- each term is `N^{-2σ} r^j`
  have hterm : ∀ j : ℕ, ((2 ^ j * N : ℕ) : ℝ) ^ (-(2 * σ)) = (N : ℝ) ^ (-(2 * σ)) * r ^ j := by
    intro j
    have hc : ((2 ^ j * N : ℕ) : ℝ) = (2 : ℝ) ^ j * N := by push_cast; ring
    rw [hc, Real.mul_rpow (by positivity) hN0.le, mul_comm]
    congr 1
    rw [hrdef, ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num),
      mul_comm (j : ℝ), Real.rpow_mul (by norm_num), Real.rpow_natCast]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hN0.le _)
  have hgeom : ∑ j ∈ Finset.range J, r ^ j ≤ 1 / (1 - r) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hr0 hr1
    rwa [pow_zero, ← Finset.range_eq_Ico] at h
  refine le_trans hgeom ?_
  -- `1 - e^{-u} ≥ u/(1+u)`
  have hexp : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have h1r : 0 < 1 - r := by linarith
  rw [div_le_div_iff₀ h1r hu, one_mul]
  have hmul : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [hr]
  have he0 : 0 < Real.exp (-u) := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_left hexp he0.le]

/-- **The Euler tail**: for `N ≥ 2`, `σ > 0` and every `M`,
`∑_{N≤p<M} p^{-1-2σ} ≤ 2(1 + 2σ log 2)e^{-2σ log N}/(σ log N)`: dyadic blocks
(`RMF.sum_primesIco_two_mul_rpow_le`, Chebyshev) and the geometric sum. -/
theorem sum_primesIco_rpow_le_of_pos {N : ℕ} (hN : 2 ≤ N) {σ : ℝ} (hσ : 0 < σ) (M : ℕ) :
    ∑ p ∈ primesIco N M, (p : ℝ) ^ (-(1 + 2 * σ))
      ≤ 2 * (1 + 2 * σ * Real.log 2) * Real.exp (-2 * σ * Real.log N) / (σ * Real.log N) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hMle : M ≤ 2 ^ M * N :=
    le_trans Nat.lt_two_pow_self.le (Nat.le_mul_of_pos_right _ (by omega))
  have hsub : primesIco N M ⊆ primesIco N (2 ^ M * N) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_primesIco.1 hp
    exact mem_primesIco.2 ⟨h1, h2, by omega⟩
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => Real.rpow_nonneg (Nat.cast_nonneg p) (-(1 + 2 * σ)))
  have h2 := sum_primesIco_pow_two_mul_rpow_le hN hσ.le M
  have h3 := sum_range_two_pow_mul_rpow_le (by omega : 1 ≤ N) hσ M
  have hNσ : (N : ℝ) ^ (-(2 * σ)) = Real.exp (-2 * σ * Real.log N) := by
    rw [Real.rpow_def_of_pos hN0]
    congr 1
    ring
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hc0 : 0 ≤ 2 * Real.log 4 / Real.log N := by positivity
  have h4 := mul_le_mul_of_nonneg_left h3 hc0
  have heq : 2 * Real.log 4 / Real.log N * ((N : ℝ) ^ (-(2 * σ))
        * ((1 + 2 * σ * Real.log 2) / (2 * σ * Real.log 2)))
      = 2 * (1 + 2 * σ * Real.log 2) * Real.exp (-2 * σ * Real.log N) / (σ * Real.log N) := by
    rw [hNσ, hl4]
    field_simp
  linarith

/-- `A ≤ σ log N` with `A > 0` forces `σ > 0` and `N ≥ 2`. -/
lemma pos_and_two_le_of_le_mul_log {N : ℕ} {σ A : ℝ} (hA : 0 < A)
    (h : A ≤ σ * Real.log N) : 0 < σ ∧ 2 ≤ N := by
  have hN : 2 ≤ N := by
    by_contra hN
    replace hN : N < 2 := not_le.1 hN
    have hlog : Real.log N = 0 := by
      interval_cases N <;> simp
    rw [hlog, mul_zero] at h
    linarith
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  refine ⟨?_, hN⟩
  by_contra hσ
  replace hσ : σ ≤ 0 := not_lt.1 hσ
  nlinarith

/-- **The Euler tail in terms of `σ log N`**: for `0 < A ≤ σ log N` and every `M`,
`∑_{N≤p<M} p^{-1-2σ} ≤ (2/A + 4)e^{-2A}` (`σ log 2 ≤ σ log N`). -/
theorem sum_primesIco_rpow_le_of_le_mul_log {N : ℕ} {σ A : ℝ} (hA : 0 < A)
    (hσN : A ≤ σ * Real.log N) (M : ℕ) :
    ∑ p ∈ primesIco N M, (p : ℝ) ^ (-(1 + 2 * σ)) ≤ (2 / A + 4) * Real.exp (-(2 * A)) := by
  obtain ⟨hσ, hN⟩ := pos_and_two_le_of_le_mul_log hA hσN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hB : 0 < σ * Real.log N := by positivity
  have hlog2 : Real.log 2 ≤ Real.log N :=
    Real.log_le_log two_pos (by exact_mod_cast hN)
  have h1 := sum_primesIco_rpow_le_of_pos hN hσ M
  -- `2(1 + 2σ log 2)/B ≤ 2/B + 4 ≤ 2/A + 4` and `e^{-2B} ≤ e^{-2A}`
  have h2 : 2 * (1 + 2 * σ * Real.log 2) / (σ * Real.log N) ≤ 2 / A + 4 := by
    have h3 : 2 * σ * Real.log 2 ≤ 2 * (σ * Real.log N) := by nlinarith
    have h4 : 2 / (σ * Real.log N) ≤ 2 / A := div_le_div_of_nonneg_left (by norm_num) hA hσN
    have h5 : 2 * (1 + 2 * σ * Real.log 2) / (σ * Real.log N)
        ≤ 2 / (σ * Real.log N) + 4 := by
      rw [div_add' _ _ _ hB.ne', div_le_div_iff_of_pos_right hB]
      linarith
    linarith
  have h6 : Real.exp (-2 * σ * Real.log N) ≤ Real.exp (-(2 * A)) :=
    Real.exp_le_exp.2 (by linarith)
  have h7 : 2 * (1 + 2 * σ * Real.log 2) * Real.exp (-2 * σ * Real.log N) / (σ * Real.log N)
      = 2 * (1 + 2 * σ * Real.log 2) / (σ * Real.log N) * Real.exp (-2 * σ * Real.log N) := by
    ring
  have h8 : 0 ≤ 2 * (1 + 2 * σ * Real.log 2) / (σ * Real.log N) := by positivity
  rw [h7] at h1
  calc _ ≤ _ := h1
    _ ≤ (2 / A + 4) * Real.exp (-2 * σ * Real.log N) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ ≤ (2 / A + 4) * Real.exp (-(2 * A)) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)

/-! ### The truncated product against `ζ(2s)` -/

/-- `(p^{-s})² = p^{-2s}`. -/
lemma cpow_neg_sq (p : ℕ) (s : ℂ) : ((p : ℂ) ^ (-s)) ^ 2 = (p : ℂ) ^ (-(2 * s)) := by
  rw [← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

/-- `|p^{-2s}| = p^{-1-2σ}` on the line `s = ½ + σ + it`. -/
lemma norm_cpow_neg_two_mul_shiftLine {p : ℕ} (hp : p.Prime) (σ t : ℝ) :
    ‖(p : ℂ) ^ (-(2 * shiftLine σ t))‖ = (p : ℝ) ^ (-(1 + 2 * σ)) := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, re_shiftLine]
  simp [shiftLine]
  ring

/-- `p^{-1-2σ} ≤ ½` for a prime `p` and `σ ≥ 0`. -/
lemma prime_rpow_neg_le_half {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 ≤ σ) :
    (p : ℝ) ^ (-(1 + 2 * σ)) ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : (p : ℝ) ^ (-(1 + 2 * σ)) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  rw [Real.rpow_neg_one] at h1
  have h2 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le two_pos hp2
  linarith

/-- **The truncated Euler product against `ζ(2s)`.**  For `σ > 0` and `τ` bounding every
`∑_{N≤p<M} p^{-1-2σ}`, `e^{-2τ}|ζ(2s)| ≤ |∏_{p<N}(1 - p^{-2s})⁻¹| ≤ e^{τ}|ζ(2s)|`,
`s = ½ + σ + it`: the Euler product to `M` tends to `ζ(2s)` (`riemannZeta_eulerProduct`), and the
factors from `N` to `M` have norms in `[1 - p^{-1-2σ}, 1 + p^{-1-2σ}]`. -/
theorem norm_prod_inv_bounds {N : ℕ} {σ τ : ℝ} (hσ : 0 < σ) (t : ℝ)
    (hτ : ∀ M : ℕ, ∑ p ∈ primesIco N M, (p : ℝ) ^ (-(1 + 2 * σ)) ≤ τ) :
    Real.exp (-(2 * τ)) * ‖riemannZeta (2 * shiftLine σ t)‖
        ≤ ‖∏ p ∈ Nat.primesBelow N, (1 - ((p : ℂ) ^ (-shiftLine σ t)) ^ 2)⁻¹‖
      ∧ ‖∏ p ∈ Nat.primesBelow N, (1 - ((p : ℂ) ^ (-shiftLine σ t)) ^ 2)⁻¹‖
        ≤ Real.exp τ * ‖riemannZeta (2 * shiftLine σ t)‖ := by
  set s : ℂ := shiftLine σ t with hsdef
  have hre1 : 1 < (2 * s).re := by
    have : (2 * s).re = 1 + 2 * σ := by
      rw [hsdef]
      simp [shiftLine]
      ring
    rw [this]
    linarith
  have hlim := riemannZeta_eulerProduct hre1
  -- the factors
  set z : ℕ → ℂ := fun p => (p : ℂ) ^ (-(2 * s)) with hzdef
  have hz : ∀ p : ℕ, p.Prime → ‖z p‖ = (p : ℝ) ^ (-(1 + 2 * σ)) := fun p hp =>
    norm_cpow_neg_two_mul_shiftLine hp σ t
  have hz1 : ∀ p : ℕ, p.Prime → 1 - z p ≠ 0 := by
    intro p hp h
    have h1 : ‖z p‖ = 1 := by rw [← sub_eq_zero.1 h, norm_one]
    have h2 := prime_rpow_neg_le_half hp hσ.le
    rw [hz p hp] at h1
    linarith
  have hP : ∏ p ∈ Nat.primesBelow N, (1 - ((p : ℂ) ^ (-s)) ^ 2)⁻¹
      = ∏ p ∈ Nat.primesBelow N, (1 - z p)⁻¹ :=
    Finset.prod_congr rfl fun p _ => by rw [cpow_neg_sq]
  rw [hP]
  set P : ℂ := ∏ p ∈ Nat.primesBelow N, (1 - z p)⁻¹ with hPdef
  -- `‖P‖ = ‖a_M‖·∏_{N≤p<M}‖1 - z p‖` for `M ≥ N`
  have hkey : ∀ M : ℕ, N ≤ M → ‖P‖ = ‖∏ p ∈ Nat.primesBelow M, (1 - z p)⁻¹‖
      * ∏ p ∈ primesIco N M, ‖1 - z p‖ := by
    intro M hM
    have hsplit : ∏ p ∈ Nat.primesBelow M, (1 - z p)⁻¹
        = (∏ p ∈ primesIco N M, (1 - z p)⁻¹) * P :=
      (Finset.prod_sdiff (primesBelow_mono hM)).symm
    have hc : ‖∏ p ∈ primesIco N M, (1 - z p)⁻¹‖ * ∏ p ∈ primesIco N M, ‖1 - z p‖ = 1 := by
      rw [norm_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun p hp => ?_
      rw [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hz1 p (prime_of_mem_primesIco hp)))]
    rw [hsplit, norm_mul]
    calc ‖P‖ = ‖P‖ * (‖∏ p ∈ primesIco N M, (1 - z p)⁻¹‖ * ∏ p ∈ primesIco N M, ‖1 - z p‖) := by
          rw [hc, mul_one]
      _ = _ := by ring
  -- the factors from `N` to `M`
  have hup : ∀ M : ℕ, ∏ p ∈ primesIco N M, ‖1 - z p‖ ≤ Real.exp τ := by
    intro M
    calc ∏ p ∈ primesIco N M, ‖1 - z p‖
        ≤ ∏ p ∈ primesIco N M, Real.exp ((p : ℝ) ^ (-(1 + 2 * σ))) := by
          refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp => ?_
          have hp' := prime_of_mem_primesIco hp
          calc ‖1 - z p‖ ≤ ‖(1 : ℂ)‖ + ‖z p‖ := norm_sub_le _ _
            _ = (p : ℝ) ^ (-(1 + 2 * σ)) + 1 := by rw [norm_one, hz p hp']; ring
            _ ≤ Real.exp ((p : ℝ) ^ (-(1 + 2 * σ))) := Real.add_one_le_exp _
      _ = Real.exp (∑ p ∈ primesIco N M, (p : ℝ) ^ (-(1 + 2 * σ))) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp τ := Real.exp_le_exp.2 (hτ M)
  have hlow : ∀ M : ℕ, Real.exp (-(2 * τ)) ≤ ∏ p ∈ primesIco N M, ‖1 - z p‖ := by
    intro M
    calc Real.exp (-(2 * τ))
        ≤ Real.exp (∑ p ∈ primesIco N M, -(2 * (p : ℝ) ^ (-(1 + 2 * σ)))) := by
          refine Real.exp_le_exp.2 ?_
          rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
          linarith [hτ M]
      _ = ∏ p ∈ primesIco N M, Real.exp (-(2 * (p : ℝ) ^ (-(1 + 2 * σ)))) := Real.exp_sum _ _
      _ ≤ ∏ p ∈ primesIco N M, ‖1 - z p‖ := by
          refine Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) fun p hp => ?_
          have hp' := prime_of_mem_primesIco hp
          have hu0 : 0 ≤ (p : ℝ) ^ (-(1 + 2 * σ)) := Real.rpow_nonneg (Nat.cast_nonneg p) _
          calc Real.exp (-(2 * (p : ℝ) ^ (-(1 + 2 * σ))))
              ≤ 1 - (p : ℝ) ^ (-(1 + 2 * σ)) :=
                exp_neg_two_mul_le_one_sub hu0 (prime_rpow_neg_le_half hp' hσ.le)
            _ = ‖(1 : ℂ)‖ - ‖z p‖ := by rw [norm_one, hz p hp']
            _ ≤ ‖1 - z p‖ := norm_sub_norm_le _ _
  have hnorm := hlim.norm
  constructor
  · refine le_of_tendsto (hnorm.const_mul (Real.exp (-(2 * τ))))
      ((Filter.eventually_ge_atTop N).mono fun M hM => ?_)
    rw [hkey M hM]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hlow M) (norm_nonneg _)
  · refine ge_of_tendsto (hnorm.const_mul (Real.exp τ))
      ((Filter.eventually_ge_atTop N).mono fun M hM => ?_)
    rw [hkey M hM, mul_comm (Real.exp τ)]
    exact mul_le_mul_of_nonneg_left (hup M) (norm_nonneg _)

/-! ### The kernel -/

/-- **The kernel of the extended sum** on the line `s = ½ + σ + it` (`RMF.shiftLine σ t`):
`K_N(σ, t) = ∏_{p<N}|1 - (p^{-s})²|^{-2}/|s|²`, which is `|ζ_N(2s)/s|²` with
`ζ_N(w) = ∏_{p<N}(1 - p^{-w})⁻¹`.  For Rademacher `X`, `lineDivSq (½ + σ) X N ω t` is
`|F_N(s)|²K_N(σ, t)` almost surely (`RMF.ae_lineDivSq_eq_mul_zetaKernel`). -/
noncomputable def zetaKernel (N : ℕ) (σ t : ℝ) : ℝ :=
  (∏ p ∈ Nat.primesBelow N, (‖1 - ((p : ℂ) ^ (-shiftLine σ t)) ^ 2‖ ^ 2)⁻¹)
    / ‖shiftLine σ t‖ ^ 2

/-- `K_N(σ, t) = |∏_{p<N}(1 - (p^{-s})²)⁻¹|²/|s|²`. -/
lemma zetaKernel_eq (N : ℕ) (σ t : ℝ) :
    zetaKernel N σ t
      = ‖∏ p ∈ Nat.primesBelow N, (1 - ((p : ℂ) ^ (-shiftLine σ t)) ^ 2)⁻¹‖ ^ 2
        / ‖shiftLine σ t‖ ^ 2 := by
  rw [zetaKernel, norm_prod, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [norm_inv, inv_pow]

lemma zetaKernel_nonneg (N : ℕ) (σ t : ℝ) : 0 ≤ zetaKernel N σ t := by
  rw [zetaKernel_eq]
  positivity

/-- `|s|² = (½ + σ)² + t²` on the line. -/
lemma normSq_shiftLine (σ t : ℝ) : ‖shiftLine σ t‖ ^ 2 = (1 / 2 + σ) ^ 2 + t ^ 2 := by
  rw [shiftLine, Complex.sq_norm, Complex.normSq_add_mul_I]

/-- `|s - ½|² = σ² + t²` on the line. -/
lemma normSq_shiftLine_sub_half (σ t : ℝ) :
    ‖shiftLine σ t - 1 / 2‖ ^ 2 = σ ^ 2 + t ^ 2 := by
  have h : shiftLine σ t - 1 / 2 = (σ : ℂ) + (t : ℂ) * Complex.I := by
    rw [shiftLine]
    push_cast
    ring
  rw [h, Complex.sq_norm, Complex.normSq_add_mul_I]

/-- `|1 - (p^{-s})²| ≥ 1 - p^{-1-2σ}` on the line. -/
lemma one_sub_rpow_le_norm_one_sub_sq {p : ℕ} (hp : p.Prime) (σ t : ℝ) :
    1 - (p : ℝ) ^ (-(1 + 2 * σ)) ≤ ‖1 - ((p : ℂ) ^ (-shiftLine σ t)) ^ 2‖ := by
  have h := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-(2 * shiftLine σ t)))
  rw [norm_one, norm_cpow_neg_two_mul_shiftLine hp] at h
  rw [cpow_neg_sq]
  exact h

/-! ### The kernel on the windows and everywhere -/

/-- **The arithmetic of the window bound**: if `b ≥ 10⁸`, `φ ≤ 0.8456`, `a ≥ b - φ`,
`E ≥ 1 - 2·10⁻¹³` and `K ≥ E²a²`, then `K ≥ (1 - 10⁻⁶)b²`. -/
lemma window_kernel_arith {a b φ E K : ℝ} (hb : 10 ^ 8 ≤ b) (hφ : φ ≤ 0.8456)
    (ha : b - φ ≤ a) (hE : 1 - 2 / 10 ^ 13 ≤ E) (hK : E ^ 2 * a ^ 2 ≤ K) :
    (1 - 1 / 10 ^ 6) * b ^ 2 ≤ K := by
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb
  have h1 : b * (1 - 0.8456 / 10 ^ 8) ≤ a := by
    have : 0.8456 ≤ 0.8456 / 10 ^ 8 * b := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
      nlinarith
    linarith
  have h2 : 0 ≤ b * (1 - 0.8456 / 10 ^ 8) := mul_nonneg hb0 (by norm_num)
  have h3 : (b * (1 - 0.8456 / 10 ^ 8)) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ h2 h1 2
  have hE0 : (0 : ℝ) ≤ 1 - 2 / 10 ^ 13 := by norm_num
  have h4 : (1 - 2 / 10 ^ 13 : ℝ) ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ hE0 hE 2
  have h5 : (1 - 2 / 10 ^ 13 : ℝ) ^ 2 * (b * (1 - 0.8456 / 10 ^ 8)) ^ 2 ≤ E ^ 2 * a ^ 2 :=
    mul_le_mul h4 h3 (sq_nonneg _) (sq_nonneg _)
  have h6 : (1 - 1 / 10 ^ 6 : ℝ) ≤ (1 - 2 / 10 ^ 13) ^ 2 * (1 - 0.8456 / 10 ^ 8) ^ 2 := by
    norm_num
  have h7 : (1 - 1 / 10 ^ 6) * b ^ 2
      ≤ (1 - 2 / 10 ^ 13 : ℝ) ^ 2 * (b * (1 - 0.8456 / 10 ^ 8)) ^ 2 := by
    have := mul_le_mul_of_nonneg_right h6 (sq_nonneg b)
    nlinarith
  linarith

/-- **The kernel on the windows**: for `σ log N ≥ 16` and `σ² + t² ≤ 10⁻¹⁶`,
`(1 - 10⁻⁶)(σ² + t²)⁻¹ ≤ K_N(σ, t)`: `|∏_{p<N}(1 - p^{-2s})⁻¹| ≥ e^{-2τ}|ζ(2s)|` with
`τ ≤ 10⁻¹³` (`RMF.norm_prod_inv_bounds`), and `|ζ(2s)/s| ≥ |s - ½|⁻¹ - 0.8456`
(`RMF.fracMellin_eq_zeta`, `RMF.norm_fracMellin_le_numeral`). -/
theorem le_zetaKernel_of_window {N : ℕ} {σ t : ℝ} (hσN : 16 ≤ σ * Real.log N)
    (hst : σ ^ 2 + t ^ 2 ≤ 1 / 10 ^ 16) :
    (1 - 1 / 10 ^ 6) * (σ ^ 2 + t ^ 2)⁻¹ ≤ zetaKernel N σ t := by
  obtain ⟨hσ, -⟩ := pos_and_two_le_of_le_mul_log (by norm_num : (0 : ℝ) < 16) hσN
  -- the tail is at most `10⁻¹³`
  have hnum : (2 / 16 + 4) * Real.exp (-(2 * 16)) ≤ (1 / 10 ^ 13 : ℝ) := by
    interval_decide (trust := kernel)
  have hτ : ∀ M : ℕ, ∑ p ∈ primesIco N M, (p : ℝ) ^ (-(1 + 2 * σ)) ≤ 1 / 10 ^ 13 := fun M =>
    le_trans (sum_primesIco_rpow_le_of_le_mul_log (by norm_num) hσN M) hnum
  obtain ⟨hlow, -⟩ := norm_prod_inv_bounds hσ t hτ
  set s : ℂ := shiftLine σ t with hsdef
  have hR0 : 0 < σ ^ 2 + t ^ 2 := by positivity
  have hsre : 1 / 2 < s.re := by rw [hsdef, re_shiftLine]; linarith
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hsre; linarith
  have hs12 : s - 1 / 2 ≠ 0 := by
    intro h
    have := normSq_shiftLine_sub_half σ t
    rw [← hsdef, h, norm_zero] at this
    linarith
  -- `ζ(2s)/s = 1/(s - ½) - φ̂(s)`
  have hz : riemannZeta (2 * s) / s = 1 / (s - 1 / 2) - fracMellin s := by
    rw [fracMellin_eq_zeta hsre]
    ring
  have hφ := norm_fracMellin_le_numeral hsre.le
  -- `b = |1/(s - ½)|`, `b² = (σ² + t²)⁻¹`, `b ≥ 10⁸`
  have hb2 : ‖1 / (s - 1 / 2)‖ ^ 2 = (σ ^ 2 + t ^ 2)⁻¹ := by
    rw [norm_div, norm_one, div_pow, one_pow, hsdef, normSq_shiftLine_sub_half, one_div]
  have hb : (10 : ℝ) ^ 8 ≤ ‖1 / (s - 1 / 2)‖ := by
    have h1 : (10 : ℝ) ^ 16 ≤ ‖1 / (s - 1 / 2)‖ ^ 2 := by
      rw [hb2]
      rw [le_inv_comm₀ (by positivity) hR0]
      calc σ ^ 2 + t ^ 2 ≤ 1 / 10 ^ 16 := hst
        _ = ((10 : ℝ) ^ 16)⁻¹ := one_div _
    by_contra hc
    replace hc : ‖1 / (s - 1 / 2)‖ < (10 : ℝ) ^ 8 := not_le.1 hc
    have h2 : ‖1 / (s - 1 / 2)‖ ^ 2 < ((10 : ℝ) ^ 8) ^ 2 :=
      pow_lt_pow_left₀ hc (norm_nonneg _) two_ne_zero
    have h3 : ((10 : ℝ) ^ 8) ^ 2 = 10 ^ 16 := by norm_num
    rw [h3] at h2
    linarith
  -- `a = |ζ(2s)/s| ≥ b - |φ̂|`
  have ha : ‖1 / (s - 1 / 2)‖ - ‖fracMellin s‖ ≤ ‖riemannZeta (2 * s)‖ / ‖s‖ := by
    rw [← norm_div, hz]
    exact norm_sub_norm_le _ _
  -- `E = e^{-2τ} ≥ 1 - 2·10⁻¹³`
  have hE : 1 - 2 / 10 ^ 13 ≤ Real.exp (-(2 * (1 / 10 ^ 13))) := by
    have := Real.add_one_le_exp (-(2 * (1 / 10 ^ 13 : ℝ)))
    linarith
  -- `K = |P|²/|s|² ≥ E²|ζ(2s)|²/|s|²`
  have hK : Real.exp (-(2 * (1 / 10 ^ 13))) ^ 2 * (‖riemannZeta (2 * s)‖ / ‖s‖) ^ 2
      ≤ zetaKernel N σ t := by
    rw [zetaKernel_eq, ← hsdef]
    have hns : 0 < ‖s‖ ^ 2 := by positivity
    rw [div_pow, ← mul_div_assoc, div_le_div_iff_of_pos_right hns, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlow 2
  rw [← hb2]
  exact window_kernel_arith hb hφ ha hE hK

/-- **The arithmetic of the decomposition**: if `0 ≤ a ≤ b + φ`, `2E² ≤ 2.01` and `K ≤ E²a²`,
then `K ≤ 2.01(b² + φ²)`. -/
lemma decomp_kernel_arith {a b φ E K : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ b + φ)
    (hE : 2 * E ^ 2 ≤ 2.01) (hK : K ≤ E ^ 2 * a ^ 2) :
    K ≤ 2.01 * (b ^ 2 + φ ^ 2) := by
  have h1 : a ^ 2 ≤ (b + φ) ^ 2 := pow_le_pow_left₀ ha0 ha 2
  have h2 : (b + φ) ^ 2 ≤ 2 * (b ^ 2 + φ ^ 2) := by nlinarith [sq_nonneg (b - φ)]
  have hE0 : 0 ≤ E ^ 2 := sq_nonneg E
  have h3 : E ^ 2 * a ^ 2 ≤ E ^ 2 * (2 * (b ^ 2 + φ ^ 2)) :=
    mul_le_mul_of_nonneg_left (h1.trans h2) hE0
  have h4 : E ^ 2 * (2 * (b ^ 2 + φ ^ 2)) ≤ 2.01 * (b ^ 2 + φ ^ 2) := by
    have := mul_le_mul_of_nonneg_right hE (by positivity : (0 : ℝ) ≤ b ^ 2 + φ ^ 2)
    nlinarith
  linarith

/-- **The kernel everywhere**: for `σ log N ≥ 4` and every `t`,
`K_N(σ, t) ≤ 2.01((σ² + t²)⁻¹ + |φ̂(s)|²)`: `|∏_{p<N}(1 - p^{-2s})⁻¹| ≤ e^{τ}|ζ(2s)|` with
`τ ≤ 4.5e^{-8}` (`RMF.norm_prod_inv_bounds`), `ζ(2s)/s = 1/(s - ½) - φ̂(s)` and
`|u + v|² ≤ 2|u|² + 2|v|²`. -/
theorem zetaKernel_le_decomp {N : ℕ} {σ : ℝ} (hσN : 4 ≤ σ * Real.log N) (t : ℝ) :
    zetaKernel N σ t ≤ 2.01 * ((σ ^ 2 + t ^ 2)⁻¹ + ‖fracMellin (shiftLine σ t)‖ ^ 2) := by
  obtain ⟨hσ, -⟩ := pos_and_two_le_of_le_mul_log (by norm_num : (0 : ℝ) < 4) hσN
  have hτ : ∀ M : ℕ, ∑ p ∈ primesIco N M, (p : ℝ) ^ (-(1 + 2 * σ))
      ≤ (2 / 4 + 4) * Real.exp (-(2 * 4)) := fun M =>
    sum_primesIco_rpow_le_of_le_mul_log (by norm_num) hσN M
  obtain ⟨-, hup⟩ := norm_prod_inv_bounds hσ t hτ
  set s : ℂ := shiftLine σ t with hsdef
  have hR0 : 0 < σ ^ 2 + t ^ 2 := by positivity
  have hsre : 1 / 2 < s.re := by rw [hsdef, re_shiftLine]; linarith
  have hz : riemannZeta (2 * s) / s = 1 / (s - 1 / 2) - fracMellin s := by
    rw [fracMellin_eq_zeta hsre]
    ring
  have hb2 : ‖1 / (s - 1 / 2)‖ ^ 2 = (σ ^ 2 + t ^ 2)⁻¹ := by
    rw [norm_div, norm_one, div_pow, one_pow, hsdef, normSq_shiftLine_sub_half, one_div]
  have ha : ‖riemannZeta (2 * s)‖ / ‖s‖ ≤ ‖1 / (s - 1 / 2)‖ + ‖fracMellin s‖ := by
    rw [← norm_div, hz]
    exact norm_sub_le _ _
  -- `2E² ≤ 2.01`, `E = e^{τ}`
  have hnum : Real.exp (2 * ((2 / 4 + 4) * Real.exp (-(2 * 4)))) ≤ (1.005 : ℝ) := by
    interval_decide (trust := kernel)
  have hE : 2 * Real.exp ((2 / 4 + 4) * Real.exp (-(2 * 4))) ^ 2 ≤ 2.01 := by
    rw [← Real.exp_nat_mul]
    push_cast
    linarith
  have hK : zetaKernel N σ t
      ≤ Real.exp ((2 / 4 + 4) * Real.exp (-(2 * 4))) ^ 2 * (‖riemannZeta (2 * s)‖ / ‖s‖) ^ 2 := by
    rw [zetaKernel_eq, ← hsdef]
    have hns : 0 < ‖s‖ ^ 2 := by
      have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hsre; linarith
      positivity
    rw [div_pow, ← mul_div_assoc, div_le_div_iff_of_pos_right hns, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hup 2
  rw [← hb2]
  exact decomp_kernel_arith (by positivity) ha hE hK

/-! ### The kernel in mean -/

/-- **The kernel is continuous** in the height, for `σ > -½`. -/
lemma continuous_zetaKernel (N : ℕ) {σ : ℝ} (hσ : -(1 / 2) < σ) :
    Continuous (zetaKernel N σ) := by
  have hden : ∀ t : ℝ, ‖shiftLine σ t‖ ^ 2 ≠ 0 := by
    intro t
    rw [normSq_shiftLine]
    have : 0 < 1 / 2 + σ := by linarith
    positivity
  have hfac : ∀ p ∈ Nat.primesBelow N, Continuous fun t : ℝ =>
      (‖1 - ((p : ℂ) ^ (-shiftLine σ t)) ^ 2‖ ^ 2)⁻¹ := by
    intro p hp
    have hp' := Nat.prime_of_mem_primesBelow hp
    refine Continuous.inv₀ ((((continuous_const.sub
      ((continuous_cpow_neg_shiftLine hp'.pos σ).pow 2)).norm).pow 2)) fun t => ?_
    have h1 := one_sub_rpow_le_norm_one_sub_sq hp' σ t
    have h2 : (p : ℝ) ^ (-(1 + 2 * σ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp'.one_lt) (by linarith)
    have h3 : 0 < ‖1 - ((p : ℂ) ^ (-shiftLine σ t)) ^ 2‖ := by linarith
    positivity
  exact (continuous_finsetProd _ hfac).div (((continuous_shiftLine σ).norm).pow 2) hden

/-- **The kernel is integrable** in the height, for `σ > -½`: it is at most
`∏_{p<N}(1 - p^{-1-2σ})^{-2}·((½ + σ)² + t²)⁻¹`. -/
theorem integrable_zetaKernel (N : ℕ) {σ : ℝ} (hσ : -(1 / 2) < σ) :
    Integrable (zetaKernel N σ) := by
  set C : ℝ := ∏ p ∈ Nat.primesBelow N, ((1 - (p : ℝ) ^ (-(1 + 2 * σ))) ^ 2)⁻¹ with hCdef
  have hbound : ∀ t : ℝ, zetaKernel N σ t ≤ C * ((1 / 2 + σ) ^ 2 + t ^ 2)⁻¹ := by
    intro t
    rw [zetaKernel, normSq_shiftLine, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
    have hp' := Nat.prime_of_mem_primesBelow hp
    have h1 := one_sub_rpow_le_norm_one_sub_sq hp' σ t
    have h2 : (p : ℝ) ^ (-(1 + 2 * σ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp'.one_lt) (by linarith)
    have h3 : 0 < 1 - (p : ℝ) ^ (-(1 + 2 * σ)) := by linarith
    exact inv_anti₀ (pow_pos h3 2) (pow_le_pow_left₀ h3.le h1 2)
  refine Integrable.mono' ((integrable_inv_sq_add_sq (σ := 1 / 2 + σ) (by linarith)).const_mul C)
    (continuous_zetaKernel N hσ).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (zetaKernel_nonneg N σ t)]
  exact hbound t

/-- **The Euler product over the smooth numbers**: `∑_{n N-smooth} n^{-w} = ∏_{p<N}(1 - p^{-w})⁻¹`
for `Re w > 0` (`EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric`). -/
lemma tsum_smooth_div_cpow_eq_prod (N : ℕ) {w : ℂ} (hw : 0 < w.re) :
    ∑' n : ℕ, (if n ∈ Nat.smoothNumbers N then (1 : ℂ) else 0) / (n : ℂ) ^ w
      = ∏ p ∈ Nat.primesBelow N, (1 - (p : ℂ) ^ (-w))⁻¹ := by
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw; exact lt_irrefl 0 hw
  set f : ℕ →* ℂ := (riemannZetaSummandHom hw0 : ℕ →* ℂ) with hfdef
  have hf : ∀ n : ℕ, f n = (n : ℂ) ^ (-w) := fun n => rfl
  have hlt : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1 := fun hp => by
    rw [hf]
    exact norm_prime_cpow_neg_lt_one hp hw
  have hprod := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    hlt N).2
  have hds : ∑' n : ℕ, (if n ∈ Nat.smoothNumbers N then (1 : ℂ) else 0) / (n : ℂ) ^ w
      = ∑' m : Nat.smoothNumbers N, f m := by
    rw [tsum_subtype]
    refine tsum_congr fun n => ?_
    by_cases hn : n ∈ Nat.smoothNumbers N
    · rw [Set.indicator_of_mem hn, if_pos hn, hf, Complex.cpow_neg, one_div]
    · rw [Set.indicator_of_notMem hn, if_neg hn, zero_div]
  rw [hds, hprod.tsum_eq]
  exact Finset.prod_congr rfl fun p _ => by rw [hf]

/-- **The kernel in mean**: `∫_ℝ K_N(σ, t) dt ≤ π/σ` for `σ > 0`, the weighted sum's
`∫_ℝ(σ² + t²)⁻¹dt`.  Parseval (`RMF.integral_normSq_partialSum_eq_line`) at the abscissa `1 + 2σ`
for the indicator of the `N`-smooth numbers, whose Dirichlet series at `2s` is
`∏_{p<N}(1 - p^{-2s})⁻¹` and whose count up to `u` is at most `u`:
`∫_ℝ K_N = 4π∫_1^∞(count)²u^{-3-4σ}du ≤ 4π∫_1^∞u^{-1-4σ}du = π/σ`. -/
theorem integral_zetaKernel_le (N : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∫ t : ℝ, zetaKernel N σ t ≤ Real.pi / σ := by
  set σ₂ : ℝ := 1 + 2 * σ with hσ₂def
  have hσ₂ : 0 < σ₂ := by linarith
  have hσ₂1 : 1 < σ₂ := by linarith
  set a : ℕ → ℂ := fun n => if n ∈ Nat.smoothNumbers N then 1 else 0 with hadef
  have ha1 : ∀ n, ‖a n‖ ≤ 1 := fun n => by
    simp only [hadef]
    split_ifs <;> simp
  have haw : Summable (coeffWeight σ₂ a) := by
    refine Summable.of_nonneg_of_le (fun n => coeffWeight_nonneg σ₂ a n) (fun n => ?_)
      (Real.summable_nat_rpow_inv.2 hσ₂1)
    rw [coeffWeight]
    calc ‖a n‖ / (n : ℝ) ^ σ₂ ≤ 1 / (n : ℝ) ^ σ₂ :=
          div_le_div_of_nonneg_right (ha1 n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = ((n : ℝ) ^ σ₂)⁻¹ := one_div _
  have hP := integral_normSq_partialSum_eq_line σ₂ a hσ₂ haw
  -- the left side is at most `1/(4σ)`
  have hL : (∫ u in Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ₂))
      ≤ 1 / (4 * σ) := by
    have hexp : -(1 + 4 * σ) < -1 := by linarith
    have hIoi : IntegrableOn (fun u : ℝ => u ^ (-(1 + 4 * σ))) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt hexp one_pos
    have hIci : IntegrableOn (fun u : ℝ => u ^ (-(1 + 4 * σ))) (Set.Ici 1) :=
      hIoi.congr_set_ae Ioi_ae_eq_Ici.symm
    have hg : IntegrableOn ((Set.Ici (1 : ℝ)).indicator fun u : ℝ => u ^ (-(1 + 4 * σ)))
        (Set.Ioi 0) := (hIci.integrable_indicator measurableSet_Ici).integrableOn
    have hf := integrableOn_normSq_partialSum σ₂ a hσ₂ haw
    have hpt : ∀ u ∈ Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ₂)
        ≤ (Set.Ici (1 : ℝ)).indicator (fun u : ℝ => u ^ (-(1 + 4 * σ))) u := by
      intro u hu
      have hu0 : (0 : ℝ) < u := hu
      rcases lt_or_ge u 1 with hu1 | hu1
      · have hfl : ⌊u⌋₊ = 0 := Nat.floor_eq_zero.2 hu1
        rw [hfl, Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, norm_zero,
          Set.indicator_of_notMem (by simpa using hu1)]
        simp
      · rw [Set.indicator_of_mem (Set.mem_Ici.2 hu1)]
        have hnorm : ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ≤ u := by
          calc ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ‖a n‖ :=
                norm_sum_le _ _
            _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊u⌋₊, (1 : ℝ) := Finset.sum_le_sum fun n _ => ha1 n
            _ = (⌊u⌋₊ : ℝ) := by simp
            _ ≤ u := Nat.floor_le hu0.le
        have hpow : u ^ (2 : ℝ) / u ^ (1 + 2 * σ₂) = u ^ (-(1 + 4 * σ)) := by
          rw [← Real.rpow_sub hu0]
          congr 1
          rw [hσ₂def]
          ring
        calc ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ₂)
            ≤ u ^ 2 / u ^ (1 + 2 * σ₂) :=
              div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
                (Real.rpow_nonneg hu0.le _)
          _ = u ^ (-(1 + 4 * σ)) := by rw [← hpow, Real.rpow_two]
    have hset : Set.Ioi (0 : ℝ) ∩ Set.Ici 1 = Set.Ici 1 :=
      Set.inter_eq_right.2 fun u hu => lt_of_lt_of_le one_pos (Set.mem_Ici.1 hu)
    refine le_trans (setIntegral_mono_on hf hg measurableSet_Ioi hpt) (le_of_eq ?_)
    rw [setIntegral_indicator measurableSet_Ici, hset,
      setIntegral_congr_set Ioi_ae_eq_Ici.symm, integral_Ioi_rpow_of_lt hexp one_pos,
      Real.one_rpow]
    field_simp
    ring
  -- the right side's integrand at `2t` is `K_N(σ, t)/4`
  have hG : ∀ t : ℝ, ‖(∑' n : ℕ, a n / (n : ℂ) ^ ((σ₂ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I))
        / ((σ₂ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖ ^ 2 = zetaKernel N σ t / 4 := by
    intro t
    have hw : (σ₂ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I = 2 * shiftLine σ t := by
      rw [hσ₂def, shiftLine]
      push_cast
      ring
    have hre : 0 < (2 * shiftLine σ t).re := by
      have : (2 * shiftLine σ t).re = 1 + 2 * σ := by
        simp [shiftLine]
        ring
      rw [this]
      linarith
    rw [hw, tsum_smooth_div_cpow_eq_prod N hre, zetaKernel_eq]
    have hPP : ∏ p ∈ Nat.primesBelow N, (1 - (p : ℂ) ^ (-(2 * shiftLine σ t)))⁻¹
        = ∏ p ∈ Nat.primesBelow N, (1 - ((p : ℂ) ^ (-shiftLine σ t)) ^ 2)⁻¹ :=
      Finset.prod_congr rfl fun p _ => by rw [cpow_neg_sq]
    rw [hPP, norm_div, div_pow, norm_mul, mul_pow]
    have h2 : ‖(2 : ℂ)‖ ^ 2 = 4 := by norm_num
    rw [h2]
    ring
  have hcomp := Measure.integral_comp_mul_left (fun τ : ℝ =>
    ‖(∑' n : ℕ, a n / (n : ℂ) ^ ((σ₂ : ℂ) + (τ : ℂ) * Complex.I))
      / ((σ₂ : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) 2
  simp only [hG] at hcomp
  rw [integral_div] at hcomp
  -- assemble
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcomp' : ∫ t : ℝ, zetaKernel N σ t
      = 2 * ∫ τ : ℝ, ‖(∑' n : ℕ, a n / (n : ℂ) ^ ((σ₂ : ℂ) + (τ : ℂ) * Complex.I))
          / ((σ₂ : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), smul_eq_mul] at hcomp
    linarith
  rw [hcomp']
  have hG' : ∫ τ : ℝ, ‖(∑' n : ℕ, a n / (n : ℂ) ^ ((σ₂ : ℂ) + (τ : ℂ) * Complex.I))
        / ((σ₂ : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
      = 2 * Real.pi * ∫ u in Set.Ioi (0 : ℝ),
          ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ₂) := by
    rw [hP, ← mul_assoc, mul_inv_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_mul]
  rw [hG']
  have h := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 2 * (2 * Real.pi))
  calc 2 * (2 * Real.pi * ∫ u in Set.Ioi (0 : ℝ),
        ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ₂))
      ≤ 2 * (2 * Real.pi) * (1 / (4 * σ)) := by linarith
    _ = Real.pi / σ := by field_simp; ring

/-! ### The link to the random Euler products -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The extended line integrand through the kernel**: for Rademacher `X`, almost surely, for
every `σ > -½` and every `t`, `lineDivSq (½ + σ) X N ω t = |F_N(s)|²K_N(σ, t)`, `s = ½ + σ + it`,
`F_N` the Euler product of the squarefree extension
(`RMF.ae_normSq_randomEulerProduct_compMult_eq`). -/
theorem ae_lineDivSq_eq_mul_zetaKernel {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (N : ℕ) :
    ∀ᵐ ω ∂μ, ∀ σ : ℝ, -(1 / 2) < σ → ∀ t : ℝ,
      lineDivSq (1 / 2 + σ) X N ω t
        = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
            (shiftLine σ t) ω‖ ^ 2 * zetaKernel N σ t := by
  filter_upwards [ae_normSq_randomEulerProduct_compMult_eq hX N] with ω hω
  intro σ hσ t
  have hre : 0 < (shiftLine σ t).re := by rw [re_shiftLine]; linarith
  have h := hω (shiftLine σ t) hre
  change ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N (shiftLine σ t) ω
      / shiftLine σ t‖ ^ 2 = _
  rw [norm_div, div_pow, h, zetaKernel, mul_div_assoc]

/-- `|F/(σ + it)|² = |F|²(σ² + t²)⁻¹`. -/
lemma normSq_div_line (F : ℂ) (σ t : ℝ) :
    ‖F / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = ‖F‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹ := by
  rw [norm_div, div_pow, Complex.sq_norm ((σ : ℂ) + (t : ℂ) * Complex.I),
    Complex.normSq_add_mul_I, div_eq_mul_inv]

/-- **The extended line integrand on the windows**: for Rademacher `X`, almost surely, for
`σ log N ≥ 16` and `σ² + t² ≤ 10⁻¹⁶`, the weighted sum's integrand `|F_N(s)/(σ + it)|²` is at most
`(1 - 10⁻⁶)⁻¹` times `lineDivSq (½ + σ) X N ω t` (`RMF.le_zetaKernel_of_window`). -/
theorem ae_lineDiv_le_lineDivSq_of_window {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (N : ℕ) :
    ∀ᵐ ω ∂μ, ∀ σ t : ℝ, 16 ≤ σ * Real.log N → σ ^ 2 + t ^ 2 ≤ 1 / 10 ^ 16 →
      (1 - 1 / 10 ^ 6) * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          (shiftLine σ t) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        ≤ lineDivSq (1 / 2 + σ) X N ω t := by
  filter_upwards [ae_lineDivSq_eq_mul_zetaKernel hX N] with ω hω
  intro σ t hσN hst
  obtain ⟨hσ, -⟩ := pos_and_two_le_of_le_mul_log (by norm_num : (0 : ℝ) < 16) hσN
  rw [hω σ (by linarith) t, normSq_div_line]
  have hK := le_zetaKernel_of_window hσN hst
  have hF0 : 0 ≤ ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
      (shiftLine σ t) ω‖ ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_left hK hF0
  linarith

/-- **The extended line integrand, decomposed**: for Rademacher `X`, almost surely, for
`σ log N ≥ 4` and every `t`,
`lineDivSq (½ + σ) X N ω t ≤ 2.01(|F_N(s)/(σ + it)|² + |F_N(s)|²|φ̂(s)|²)`
(`RMF.zetaKernel_le_decomp`): the weighted sum's integrand plus the fractional-part kernel's. -/
theorem ae_lineDivSq_le_decomp {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (N : ℕ) :
    ∀ᵐ ω ∂μ, ∀ σ : ℝ, 4 ≤ σ * Real.log N → ∀ t : ℝ,
      lineDivSq (1 / 2 + σ) X N ω t
        ≤ 2.01 * (‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              (shiftLine σ t) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
            + ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              (shiftLine σ t) ω‖ ^ 2 * ‖fracMellin (shiftLine σ t)‖ ^ 2) := by
  filter_upwards [ae_lineDivSq_eq_mul_zetaKernel hX N] with ω hω
  intro σ hσN t
  obtain ⟨hσ, -⟩ := pos_and_two_le_of_le_mul_log (by norm_num : (0 : ℝ) < 4) hσN
  rw [hω σ (by linarith) t, normSq_div_line]
  have hK := zetaKernel_le_decomp hσN t
  have hF0 : 0 ≤ ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
      (shiftLine σ t) ω‖ ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_left hK hF0
  linarith

end RMF
