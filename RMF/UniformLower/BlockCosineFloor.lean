/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.MertensBlockCosine
import RMF.UniformLower.WindowBlockDataDecay

/-!
# The block cosine sums below the PNT floor, telescoped

The block cosine sums `C_m(τ) = ∑_{p ∈ primeBlockSub θ m} cos(τ log p)p^{-1-2σ}` over a run of
blocks, in two regimes: explicit Mertens below the explicit PNT's floor `104`, the PNT bound at and
above it.  `K = RMF.mertensErrConst`.  The per-block bounds are upstream, where the window's block
data use them: explicit Mertens per block and telescoped
(`RMF.abs_sum_blockCosSum_sub_integral_le_mertens`), the flat two-regime error `RMF.blockCosErr`
and its numeral `7.43·10⁻⁸` in `RMF/UniformLower/WindowBlockData.lean`, the decaying one
`RMF.blockCosErrDecay` in `RMF/UniformLower/WindowBlockDataDecay.lean`.  The pair's block data
(`RMF/UniformLower/PairWindowData.lean`) build on this file.

* **Over a run of blocks**: `RMF.blockCosTelErr`, Mertens telescoped below `104` (one Abel
  summation over the union, so the `e^{-(m₁+θ)}` term is paid once) and the summed PNT errors
  above.
* **Numerals**: at the floor `20` with `τ ≤ 2e^{-20}`, `3.16·10⁻⁶` over any run (at most `84`
  blocks lie in `[20, 104)`); from `θ ≥ 104`, the summed PNT errors `1.59(τ+1)e^{-m₁}/10²⁸`.
-/

namespace RMF

/-! ### Two regimes, telescoped over a run of blocks -/

/-- The damped integrand `cos(τu)e^{-2σu}/u` is integrable on `[a, b]` for `0 < a ≤ b`. -/
lemma intervalIntegrable_cos_mul_exp_div {τ σ a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
      MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div (by fun_prop) continuousOn_id fun u hu => ?_
  rw [Set.uIcc_of_le hab] at hu
  exact (ha.trans_le hu.1).ne'

/-- **The telescoped PNT errors from any block past the floor**: for `N + θ ≥ 104`, `τ, σ ≥ 0` and
`N ≤ M`, `∑_{N≤m<M} C_m(τ)` is within `1.59(τ+1)e^{104-(N+θ)}/10²⁸` of
`∫_{e^{N+θ}}^{e^{M+θ}} cos(τu)e^{-2σu}/u du`: the per-block PNT bound
(`RMF.abs_sum_cos_primeBlockSub_sub_integral_le_decay`) summed over the run, which needs the
condition `≥ 104` only at its first block. -/
theorem abs_sum_blockCosSum_sub_integral_le_of_floor {τ σ θ : ℝ} {N M : ℕ} (hNM : N ≤ M)
    (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (hN : 104 ≤ (N : ℝ) + θ) :
    |∑ m ∈ Finset.Ico N M, blockCosSum θ σ τ m
        - ∫ u in Real.exp ((N : ℝ) + θ)..Real.exp ((M : ℝ) + θ),
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
      ≤ 1.59 * (τ + 1) * Real.exp (104 - ((N : ℝ) + θ)) / 10 ^ 28 := by
  have hint : ∀ k ∈ Set.Ico N M, IntervalIntegrable
      (fun u : ℝ => Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u) MeasureTheory.volume
      ((fun j : ℕ => Real.exp ((j : ℝ) + θ)) k)
      ((fun j : ℕ => Real.exp ((j : ℝ) + θ)) (k + 1)) := fun k _ =>
    intervalIntegrable_cos_mul_exp_div (Real.exp_pos _)
      (Real.exp_le_exp.2 (by push_cast; linarith))
  rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico hNM hint, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k ∈ Finset.Ico N M,
      |blockCosSum θ σ τ k - ∫ u in (fun j : ℕ => Real.exp ((j : ℝ) + θ)) k..
          (fun j : ℕ => Real.exp ((j : ℝ) + θ)) (k + 1),
          Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
        ≤ (τ + 1) * Real.exp (104 - θ) / 10 ^ 28 * Real.exp (-(k : ℝ))
          * (1 + 0 * (2 * (k : ℝ) + 1)) := by
    intro k hk
    have hNk : (N : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.1 hk).1
    have hk' : 104 ≤ (k : ℝ) + θ := by linarith
    have h := abs_sum_cos_primeBlockSub_sub_integral_le_decay τ σ θ k hτ hσ hk'
    have hk1 : Real.exp (((k + 1 : ℕ) : ℝ) + θ) = Real.exp ((k : ℝ) + θ + 1) := by
      push_cast
      ring_nf
    simp only [hk1]
    refine h.trans (le_of_eq ?_)
    rw [show (104 : ℝ) - ((k : ℝ) + θ) = (104 - θ) + -(k : ℝ) by ring, Real.exp_add]
    ring
  refine (Finset.sum_le_sum hterm).trans ?_
  have h := sum_mul_exp_neg_mul_le_numeral_of_le (c := (τ + 1) * Real.exp (104 - θ) / 10 ^ 28)
    (K := 1) (B := 0) (by positivity) zero_le_one le_rfl (n := N) (s := Finset.Ico N M)
    (fun m hm => (Finset.mem_Ico.1 hm).1)
  refine h.trans (le_of_eq ?_)
  rw [show (104 : ℝ) - ((N : ℝ) + θ) = (104 - θ) + -(N : ℝ) by ring, Real.exp_add]
  ring

/-- **A run of blocks split at a block `N` past the floor**: for `m₁ ≤ N ≤ M`, `m₁ + θ ≥ 0`,
`N + θ ≥ 104` and `τ, σ ≥ 0`, `∑_{m₁≤m<M} C_m(τ)` is within
`2Ke^{-(m₁+θ)} + Kτ(N - m₁) + 1.59(τ+1)e^{104-(N+θ)}/10²⁸` of
`∫_{e^{m₁+θ}}^{e^{M+θ}} cos(τu)e^{-2σu}/u du`: Mertens telescoped on `[m₁, N)`, the PNT on
`[N, M)`. -/
theorem abs_sum_blockCosSum_sub_integral_le_split {τ σ θ : ℝ} {m₁ N M : ℕ} (h₁ : m₁ ≤ N)
    (h₂ : N ≤ M) (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (hm₁ : 0 ≤ (m₁ : ℝ) + θ)
    (hN : 104 ≤ (N : ℝ) + θ) :
    |∑ m ∈ Finset.Ico m₁ M, blockCosSum θ σ τ m
        - ∫ u in Real.exp ((m₁ : ℝ) + θ)..Real.exp ((M : ℝ) + θ),
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
      ≤ 2 * mertensErrConst * Real.exp (-((m₁ : ℝ) + θ)) + mertensErrConst * τ * ((N : ℝ) - m₁)
        + 1.59 * (τ + 1) * Real.exp (104 - ((N : ℝ) + θ)) / 10 ^ 28 := by
  have hA := abs_sum_blockCosSum_sub_integral_le_mertens (σ := σ) h₁ hτ hσ hm₁
  have hB := abs_sum_blockCosSum_sub_integral_le_of_floor (σ := σ) h₂ hτ hσ hN
  have h₁' : (m₁ : ℝ) ≤ N := by exact_mod_cast h₁
  have h₂' : (N : ℝ) ≤ M := by exact_mod_cast h₂
  have hi₁ : IntervalIntegrable
      (fun u : ℝ => Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u) MeasureTheory.volume
      (Real.exp ((m₁ : ℝ) + θ)) (Real.exp ((N : ℝ) + θ)) :=
    intervalIntegrable_cos_mul_exp_div (Real.exp_pos _) (Real.exp_le_exp.2 (by linarith))
  have hi₂ : IntervalIntegrable
      (fun u : ℝ => Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u) MeasureTheory.volume
      (Real.exp ((N : ℝ) + θ)) (Real.exp ((M : ℝ) + θ)) :=
    intervalIntegrable_cos_mul_exp_div (Real.exp_pos _) (Real.exp_le_exp.2 (by linarith))
  rw [← Finset.sum_Ico_consecutive _ h₁ h₂,
    ← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂]
  have htri := abs_add_le
    (∑ m ∈ Finset.Ico m₁ N, blockCosSum θ σ τ m
      - ∫ u in Real.exp ((m₁ : ℝ) + θ)..Real.exp ((N : ℝ) + θ),
          Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
    (∑ m ∈ Finset.Ico N M, blockCosSum θ σ τ m
      - ∫ u in Real.exp ((N : ℝ) + θ)..Real.exp ((M : ℝ) + θ),
          Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
  have heq : (∑ m ∈ Finset.Ico m₁ N, blockCosSum θ σ τ m
        + ∑ m ∈ Finset.Ico N M, blockCosSum θ σ τ m)
      - ((∫ u in Real.exp ((m₁ : ℝ) + θ)..Real.exp ((N : ℝ) + θ),
          Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
        + ∫ u in Real.exp ((N : ℝ) + θ)..Real.exp ((M : ℝ) + θ),
          Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
      = (∑ m ∈ Finset.Ico m₁ N, blockCosSum θ σ τ m
          - ∫ u in Real.exp ((m₁ : ℝ) + θ)..Real.exp ((N : ℝ) + θ),
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
        + (∑ m ∈ Finset.Ico N M, blockCosSum θ σ τ m
          - ∫ u in Real.exp ((N : ℝ) + θ)..Real.exp ((M : ℝ) + θ),
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u) := by ring
  rw [heq]
  linarith

/-- **The telescoped error of a run of blocks, two regimes**: from a first block with
`m₁ + θ ≥ 104`, the summed PNT errors `1.59(τ+1)e^{104-(m₁+θ)}/10²⁸`; from below, Mertens
telescoped over the `⌈104 - (m₁+θ)⌉₊` blocks below `104` plus the PNT errors above,
`2Ke^{-(m₁+θ)} + Kτ⌈104 - (m₁+θ)⌉₊ + 1.59(τ+1)/10²⁸`. -/
noncomputable def blockCosTelErr (θ : ℝ) (m₁ : ℕ) (τ : ℝ) : ℝ :=
  if 104 ≤ (m₁ : ℝ) + θ then 1.59 * (τ + 1) * Real.exp (104 - ((m₁ : ℝ) + θ)) / 10 ^ 28
  else 2 * mertensErrConst * Real.exp (-((m₁ : ℝ) + θ))
    + mertensErrConst * τ * ⌈104 - ((m₁ : ℝ) + θ)⌉₊ + 1.59 * (τ + 1) / 10 ^ 28

/-- **The telescoped block cosine sums, two regimes**: for `m₁ ≤ M`, `τ, σ ≥ 0` and `m₁ + θ ≥ 0`,
`∑_{m₁≤m<M} C_m(τ)` is within `blockCosTelErr θ m₁ τ` of
`∫_{e^{m₁+θ}}^{e^{M+θ}} cos(τu)e^{-2σu}/u du`, however long the run. -/
theorem abs_sum_blockCosSum_sub_integral_le_two_regime {τ σ θ : ℝ} {m₁ M : ℕ} (hmM : m₁ ≤ M)
    (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (hm₁ : 0 ≤ (m₁ : ℝ) + θ) :
    |∑ m ∈ Finset.Ico m₁ M, blockCosSum θ σ τ m
        - ∫ u in Real.exp ((m₁ : ℝ) + θ)..Real.exp ((M : ℝ) + θ),
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
      ≤ blockCosTelErr θ m₁ τ := by
  unfold blockCosTelErr
  split_ifs with h
  · exact abs_sum_blockCosSum_sub_integral_le_of_floor hmM hτ hσ h
  · have hK := mertensErrConst_nonneg
    have hP : (0 : ℝ) ≤ 1.59 * (τ + 1) / 10 ^ 28 := by positivity
    have hn : 104 - ((m₁ : ℝ) + θ) ≤ (⌈104 - ((m₁ : ℝ) + θ)⌉₊ : ℝ) := Nat.le_ceil _
    rcases le_or_gt (m₁ + ⌈104 - ((m₁ : ℝ) + θ)⌉₊) M with hNM | hMN
    · -- the run reaches the floor: split at the first block past it
      have hN : 104 ≤ ((m₁ + ⌈104 - ((m₁ : ℝ) + θ)⌉₊ : ℕ) : ℝ) + θ := by
        push_cast
        linarith
      refine (abs_sum_blockCosSum_sub_integral_le_split (σ := σ) (Nat.le_add_right _ _) hNM hτ
        hσ hm₁ hN).trans ?_
      have he : Real.exp (104 - (((m₁ + ⌈104 - ((m₁ : ℝ) + θ)⌉₊ : ℕ) : ℝ) + θ)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by linarith)
      have hτ1 : (0 : ℝ) ≤ τ + 1 := by linarith
      have hP' : 1.59 * (τ + 1) * Real.exp (104 - (((m₁ + ⌈104 - ((m₁ : ℝ) + θ)⌉₊ : ℕ) : ℝ) + θ))
          / 10 ^ 28 ≤ 1.59 * (τ + 1) / 10 ^ 28 :=
        div_le_div_of_nonneg_right (mul_le_of_le_one_right (by positivity) he) (by positivity)
      have hcnt : (((m₁ + ⌈104 - ((m₁ : ℝ) + θ)⌉₊ : ℕ) : ℝ) - m₁)
          = (⌈104 - ((m₁ : ℝ) + θ)⌉₊ : ℝ) := by
        push_cast
        ring
      rw [hcnt]
      linarith
    · -- the run ends below the floor: Mertens throughout
      refine (abs_sum_blockCosSum_sub_integral_le_mertens (σ := σ) hmM hτ hσ hm₁).trans ?_
      have hcnt : (M : ℝ) - m₁ ≤ (⌈104 - ((m₁ : ℝ) + θ)⌉₊ : ℝ) := by
        have h' : (M : ℝ) < m₁ + (⌈104 - ((m₁ : ℝ) + θ)⌉₊ : ℝ) := by exact_mod_cast hMN
        linarith
      have h2 : mertensErrConst * τ * ((M : ℝ) - m₁)
          ≤ mertensErrConst * τ * (⌈104 - ((m₁ : ℝ) + θ)⌉₊ : ℝ) :=
        mul_le_mul_of_nonneg_left hcnt (mul_nonneg hK hτ)
      linarith

/-! ### Numerals at the floor `20` -/

/-- **The telescoped error at the floor `20`**: `blockCosTelErr θ m₁ τ ≤ 3.16·10⁻⁶` for
`m₁ + θ ≥ 20` and `0 ≤ τ ≤ 2e^{-20}` — at most `84` blocks lie below `104`, so Mertens gives
`2Ke^{-20} + 84·2Ke^{-20}`. -/
theorem blockCosTelErr_le_numeral {θ τ : ℝ} {m₁ : ℕ} (hm : 20 ≤ (m₁ : ℝ) + θ) (hτ : 0 ≤ τ)
    (hτ2 : τ ≤ 2 * Real.exp (-20)) : blockCosTelErr θ m₁ τ ≤ 3.16 / 10 ^ 6 := by
  have hK := mertensErrConst_le
  have hK0 := mertensErrConst_nonneg
  have he := exp_neg_twenty_le_numeral
  have he0 : 0 ≤ Real.exp (-20) := (Real.exp_pos _).le
  have hτ1 : τ ≤ 1 := by linarith
  unfold blockCosTelErr
  split_ifs with h
  · have he1 : Real.exp (104 - ((m₁ : ℝ) + θ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hτe : (τ + 1) * Real.exp (104 - ((m₁ : ℝ) + θ)) ≤ τ + 1 :=
      mul_le_of_le_one_right (by linarith) he1
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  · have hn : (⌈104 - ((m₁ : ℝ) + θ)⌉₊ : ℝ) ≤ 84 := by
      have h84 : ⌈104 - ((m₁ : ℝ) + θ)⌉₊ ≤ 84 :=
        Nat.ceil_le.2 (by push_cast; linarith)
      exact_mod_cast h84
    have hem : Real.exp (-((m₁ : ℝ) + θ)) ≤ Real.exp (-20) := Real.exp_le_exp.2 (by linarith)
    have h1 : mertensErrConst * Real.exp (-((m₁ : ℝ) + θ)) ≤ mertensErrConst * Real.exp (-20) :=
      mul_le_mul_of_nonneg_left hem hK0
    have h2 : mertensErrConst * τ ≤ mertensErrConst * (2 * Real.exp (-20)) :=
      mul_le_mul_of_nonneg_left hτ2 hK0
    have h3 : mertensErrConst * Real.exp (-20) ≤ 9.0028 * (1 / 485000000) :=
      mul_le_mul hK he he0 (by norm_num)
    have h4 : mertensErrConst * τ * (⌈104 - ((m₁ : ℝ) + θ)⌉₊ : ℝ) ≤ mertensErrConst * τ * 84 :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg hK0 hτ)
    linarith

end RMF
