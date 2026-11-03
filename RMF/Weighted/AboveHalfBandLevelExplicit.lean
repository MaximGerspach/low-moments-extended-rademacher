/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfPiecesExplicit

/-!
# A band's level above `q = ½`, fully explicit

The bound of `RMF.integral_rpow_norm_blockTruncationTail_le_split` with every piece in closed form,
at the parameters `σ = η = (log x)^{-2}`, `c_L = 1/log x`, the sieve level `z' = ⌊z/(log x)^7⌋`,
the central window `|t| ≤ θ/log z`, windows up to `T = (θ/log z)e^J ≥ 1/log y`
(`J = ⌈log(log z/(θ log y))⌉`), each window the better of no split and the split at
`⌊exp(c_s/T)⌋` clamped to `[y, z]`:

`E|𝒯_{y,z}(x)|^{2q} ≤ RMF.bandLevel q θ η' ε c_s x y z`

(`RMF.integral_rpow_norm_blockTruncationTail_le_bandLevel`), and for the bottom, the full product
up to `z` with windows up to a height `T_m`,
`E|𝒯_z(x)|^{2q} ≤ RMF.bottomLevel q θ η' ε c_s T_m x z`
(`RMF.integral_rpow_norm_truncationTail_le_bottomLevel`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The pieces -/

/-- (PF) of the band `(y, z]` at exponent `q`. -/
noncomputable def pfBand (q : ℝ) (y z : ℕ) : ℝ :=
  (Real.log z / Real.log y) ^ (q * (2 * q - 1))
    * Real.exp (q * (2 * q - 1)
      * (9.0028 / Real.log y + 9.0028 / Real.log z + (2 - 2 * q) / (3 * y)))

/-- Mertens' bound on the band `(y, z]`'s second moment: `(log z/log y)e^{9.0028/log y
+ 9.0028/log z}`. -/
noncomputable def mBand (y z : ℕ) : ℝ :=
  Real.log z / Real.log y * Real.exp (9.0028 / Real.log y + 9.0028 / Real.log z)

/-- The central window's closed form for the band `(y, z]`, over `|t| ≤ τ`, normalised by
`L = 2π log z` (`RMF.setIntegral_inv_mul_diffQ_le` with the prime sums bounded). -/
noncomputable def cenBand (q σ τ : ℝ) (z : ℕ) : ℝ :=
  (2 * Real.pi * Real.log z)⁻¹
    * (2 * τ * (((2 * q - 1) * ((1 + (2 - 2 * q) / 3)
          * (Real.log ((z + 1 : ℕ) : ℝ) + Real.log 4 + 4))) ^ 2
        * (1 + Real.exp ((2 * q - 1) * ((1 + (2 - 2 * q) / 3)
          * (Real.log ((z + 1 : ℕ) : ℝ) + Real.log 4 + 4)) * (τ + σ))) ^ 2 / 4)
      + (Real.log ((z + 1 : ℕ) : ℝ) ^ 2 / 2 + 15.003 * Real.log ((z + 1 : ℕ) : ℝ) + 34)
        * Real.exp (4 * (1 - q) * σ * (4 * (Real.log ((z + 1 : ℕ) : ℝ) + Real.log 4 + 4)))
        * (2 * τ + 2 * τ / 3 * (Real.exp (2 * (1 - q)
          * (Real.log ((z + 1 : ℕ) : ℝ) ^ 2 / 2 + 15.003 * Real.log ((z + 1 : ℕ) : ℝ) + 34)
          * τ ^ 2) - 1)))

/-- The split point of the window at height `T` of the band `(y, z]`: `⌊exp(c/T)⌋`, clamped to
`[y, z]`. -/
noncomputable def splitPt (c T : ℝ) (y z : ℕ) : ℕ := min z (max y ⌊Real.exp (c / T)⌋₊)

lemma le_splitPt {c T : ℝ} {y z : ℕ} (hyz : y ≤ z) : y ≤ splitPt c T y z :=
  le_min hyz (le_max_left _ _)

lemma splitPt_le (c T : ℝ) (y z : ℕ) : splitPt c T y z ≤ z := min_le_left _ _

/-- A band window's bound without a split (`RMF.window_band_le_nosplit_explicit`). -/
noncomputable def winNoSplit (q T : ℝ) (y z : ℕ) : ℝ :=
  ((Real.exp 1 - 1) * mBand y z / (Real.pi * T * Real.log z)) ^ q

/-- A band window's bound by the split at `z₁` and Jensen (`RMF.window_band_le_split_explicit`). -/
noncomputable def winSplit (q T : ℝ) (y z₁ z : ℕ) : ℝ :=
  pfBand q y z₁
    * (taylorWindowW (2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2)
      * mBand z₁ z / (Real.pi * T * Real.log z)) ^ q

/-- The number of windows of the band `(y, z]` at the central cut `θ`. -/
noncomputable def bandJ (θ : ℝ) (y z : ℕ) : ℕ :=
  ⌈Real.log (Real.log z / (θ * Real.log y))⌉₊

/-- The height of the `k`-th window of the band `(y, z]`: `(θ/log z)e^{J-k}`. -/
noncomputable def bandT (θ : ℝ) (y z k : ℕ) : ℝ :=
  Real.exp (Real.log (θ / Real.log z) + bandJ θ y z - k)

/-- The sieve level of the truncation bound at `x`: `⌊z/(log x)^7⌋`. -/
noncomputable def sieveLevel (x : ℝ) (z : ℕ) : ℕ := ⌊(z : ℝ) / Real.log x ^ 7⌋₊

/-- **The explicit bound on a band's level** at exponent `q`, central cut `θ`, coherent split
`η'`, smoothing `ε` and split constant `c_s`. -/
noncomputable def bandLevel (q θ η' ε cs x : ℝ) (y z : ℕ) : ℝ :=
  (Real.exp (-(Real.log x / Real.log z)) * mBand y z ^ Real.exp 1) ^ q
  + (lemmaTConst z (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε
      * ((Real.log x ^ 2)⁻¹ / Real.log z)) ^ q * pfBand q y z
  + (lemmaTConst z (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε * Real.exp (2 * (Real.log x)⁻¹)) ^ q
    * (cenBand q (Real.log x ^ 2)⁻¹ (θ / Real.log z) z ^ q * pfBand q y z
      + ((1 + 1 / η') / (Real.pi * θ)) ^ q * pfBand q y z
      + (1 + η') ^ q * (∑ k ∈ Finset.range (bandJ θ y z),
          min (winNoSplit q (bandT θ y z k) y z)
            (winSplit q (bandT θ y z k) y (splitPt cs (bandT θ y z k) y z) z)
        + (mBand y z / (Real.pi * θ * Real.exp (bandJ θ y z))) ^ q))
  + smallQReductionErr x (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε ^ q

/-- **A band's level with supplied window bounds** `w k`: `RMF.bandLevel` with the windows' sum
`∑_{k<J} w k` (`RMF.bandLevel_eq_bandLevelW`). -/
noncomputable def bandLevelW (q θ η' ε x : ℝ) (y z : ℕ) (w : ℕ → ℝ) : ℝ :=
  (Real.exp (-(Real.log x / Real.log z)) * mBand y z ^ Real.exp 1) ^ q
  + (lemmaTConst z (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε
      * ((Real.log x ^ 2)⁻¹ / Real.log z)) ^ q * pfBand q y z
  + (lemmaTConst z (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε * Real.exp (2 * (Real.log x)⁻¹)) ^ q
    * (cenBand q (Real.log x ^ 2)⁻¹ (θ / Real.log z) z ^ q * pfBand q y z
      + ((1 + 1 / η') / (Real.pi * θ)) ^ q * pfBand q y z
      + (1 + η') ^ q * (∑ k ∈ Finset.range (bandJ θ y z), w k
        + (mBand y z / (Real.pi * θ * Real.exp (bandJ θ y z))) ^ q))
  + smallQReductionErr x (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε ^ q

lemma bandLevel_eq_bandLevelW (q θ η' ε cs x : ℝ) (y z : ℕ) :
    bandLevel q θ η' ε cs x y z = bandLevelW q θ η' ε x y z fun k =>
      min (winNoSplit q (bandT θ y z k) y z)
        (winSplit q (bandT θ y z k) y (splitPt cs (bandT θ y z k) y z) z) := rfl

lemma bandT_pos {θ : ℝ} {y z : ℕ} (k : ℕ) : 0 < bandT θ y z k := Real.exp_pos _

/-! ### The level -/

/-- The band's second moment on the shifted line, by Mertens: `E‖F(½+σ+it)‖² ≤ RMF.mBand y z`. -/
lemma integral_normSq_line_le_mBand {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y z : ℕ} (hy : 2 ≤ y) (hyz : y ≤ z) {σ : ℝ}
    (hσ : 0 ≤ σ) (t : ℝ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ) ≤ mBand y z := by
  have h := integral_normSq_Ico_shiftLine_le_mertens_ratio hX (z := y) (y := z) hy hyz hσ t
  have hs : shiftLine σ t = (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I := by
    rw [shiftLine]
    push_cast
    ring
  rw [hs] at h
  refine le_trans h (le_of_eq ?_)
  rw [mBand, add_comm (9.0028 / Real.log z)]

/-- **A band's level above `½` with supplied window bounds.**  For `½ ≤ q ≤ 1`, `θ, η', ε > 0`,
`2 ≤ y ≤ z ≤ x` with `log x > 1`, the sieve level `z' = ⌊z/(log x)^7⌋ ≥ 2` and bounds `w k` on the
windows' moments at `σ = (log x)^{-2}`, heights `RMF.bandT`:

`E|𝒯_{y,z}(x)|^{2q} ≤ RMF.bandLevelW q θ η' ε x y z w`,

`RMF.integral_rpow_norm_blockTruncationTail_le_split` at `σ = η = (log x)^{-2}`, `c_L = 1/log x`,
the atom by Jensen and every other piece in closed form. -/
theorem integral_rpow_norm_blockTruncationTail_le_bandLevelW {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q θ η' ε x : ℝ} {y z : ℕ} {w : ℕ → ℝ} (hq0 : 1 / 2 ≤ q)
    (hq1 : q ≤ 1) (hθ : 0 < θ) (hη' : 0 < η') (hε : 0 < ε) (hy : 2 ≤ y) (hyz : y ≤ z)
    (hzx : (z : ℝ) ≤ x) (hx : 1 < Real.log x) (hz' : 2 ≤ sieveLevel x z)
    (hw : ∀ k < bandJ θ y z, (2 / (2 * Real.pi * Real.log z)) ^ q
      * (∫ ω, (∫ t in Set.Icc (bandT θ y z k / Real.exp 1) (bandT θ y z k),
        (((Real.log x ^ 2)⁻¹) ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
            (shiftLine (Real.log x ^ 2)⁻¹ t) ω‖ ^ 2) ^ q ∂μ) ≤ w k) :
    (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
        ^ (2 * q) ∂μ)
      ≤ bandLevelW q θ η' ε x y z w := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast le_trans hy hyz
  have hz2' : (2 : ℕ) ≤ z := le_trans hy hyz
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hx0 : 0 < x := lt_of_lt_of_le (by linarith) hzx
  have hlx : 0 < Real.log x := by linarith
  set lx := Real.log x with hlxdef
  set σ := (lx ^ 2)⁻¹ with hσdef
  have hσ : 0 < σ := by positivity
  have hσ1 : σ < 1 := by
    rw [hσdef]
    exact inv_lt_one_of_one_lt₀ (by nlinarith)
  -- the sieve level
  set z' := sieveLevel x z with hz'def
  have hz'z : z' ≤ z := by
    rw [hz'def, sieveLevel]
    refine Nat.floor_le_of_le ?_
    exact div_le_self (by positivity) (one_le_pow₀ hx.le)
  -- the side conditions of the truncation bound
  have hσlog : σ * Real.log (x / z) ≤ lx⁻¹ := by
    have hlog : Real.log (x / z) ≤ lx := by
      rw [Real.log_div hx0.ne' (by positivity), hlxdef]
      linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ z)]
    have hlog0 : 0 ≤ Real.log (x / z) :=
      Real.log_nonneg ((one_le_div (by positivity)).2 hzx)
    calc σ * Real.log (x / z) ≤ σ * lx := mul_le_mul_of_nonneg_left hlog hσ.le
      _ = lx⁻¹ := by rw [hσdef]; field_simp
  have hzη : 1 + σ < z := by linarith
  -- the windows' parameters
  set J := bandJ θ y z with hJdef
  set c := Real.log (θ / Real.log z) + (J : ℝ) with hcdef
  have hT : ∀ k : ℕ, bandT θ y z k = Real.exp (c - k) := fun k => by
    rw [bandT, hcdef]
  have hM := fun t => integral_normSq_line_le_mBand hX hy hyz hσ.le t
  -- each window
  have hw' : ∀ k ∈ Finset.Ico 0 J, (2 / (2 * Real.pi * Real.log z)) ^ q
      * (∫ ω, (∫ t in Set.Icc (Real.exp (c - k) / Real.exp 1) (Real.exp (c - k)),
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1) (shiftLine σ t)
            ω‖ ^ 2) ^ q ∂μ) ≤ w k := by
    intro k hk
    rw [← hT k]
    exact hw k (Finset.mem_Ico.1 hk).2
  have hLT := integral_rpow_norm_blockTruncationTail_le_split hX hyz hz' hz'z hzx hσ hσlog hσ hzη
    hε hq0 hq1 hη' (Nat.zero_le J) (c := c) (M := mBand y z) hM hw'
  -- the atom, by Jensen
  have hatom : (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
      ^ (2 * q) ∂μ) ≤ (Real.exp (-(lx / Real.log z)) * mBand y z ^ Real.exp 1) ^ q := by
    have hmeas : Measurable fun ω =>
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ 2 :=
      ((measurable_smoothAlgebra_blockTailSum y z x).mono (smoothAlgebra_le hX z)
        le_rfl).norm.pow_const 2
    have hint : Integrable (fun ω =>
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ 2) μ := by
      refine (memLp_top_of_bound hmeas.aestronglyMeasurable ((primorial z : ℝ) ^ 2)
        ?_).integrable le_top
      filter_upwards [ae_norm_blockTailSum_le hRa y z x] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hω 2
    have hB : (∫ ω,
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ 2 ∂μ)
        ≤ Real.exp (-(lx / Real.log z)) * mBand y z ^ Real.exp 1 := by
      refine le_trans (integral_normSq_blockTailSum_le_exp_sum hX y hz2' hx0) ?_
      have hxV : x ^ (-(Real.log z)⁻¹) = Real.exp (-(lx / Real.log z)) := by
        rw [Real.rpow_def_of_pos hx0, hlxdef]
        congr 1
        ring
      rw [hxV]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have hsum := sum_primesIco_inv_le hy hyz
      have hmB : 0 < mBand y z := by rw [mBand]; positivity
      rw [Real.rpow_def_of_pos hmB]
      refine Real.exp_le_exp.2 ?_
      have hlog : Real.log (mBand y z)
          = Real.log (Real.log z) - Real.log (Real.log y) + (9.0028 / Real.log y
            + 9.0028 / Real.log z) := by
        rw [mBand, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
          Real.log_div hlz.ne' hly.ne']
      rw [hlog]
      have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      nlinarith [mul_le_mul_of_nonneg_left hsum he]
    have hpow : ∀ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
          ^ (2 * q)
        = (‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ 2) ^ q := by
      intro ω
      rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two]
    simp_rw [hpow]
    exact integral_rpow_le_rpow_of_integral_le (by linarith) hq1
      (Filter.Eventually.of_forall fun ω => sq_nonneg _) hint hB
  -- (PF) at the critical point
  have hP : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
      (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ) ≤ pfBand q y z := by
    have h := hRa.integral_norm_randomEulerProductIco_shift_rpow_le_above_half (σ := 0) le_rfl
      hq0 hq1 hy hyz
    have hs : (((1 / 2 + 0 : ℝ)) : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [hs] at h
    exact h
  have hP0 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (y + 1) (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  -- the central window
  have hτ : Real.exp (c - J) = θ / Real.log z := by
    rw [hcdef, show Real.log (θ / Real.log z) + (J : ℝ) - J = Real.log (θ / Real.log z) by ring,
      Real.exp_log (by positivity)]
  have hτ0 : 0 < θ / Real.log z := by positivity
  have hCen : (∫ t in Set.Icc (-Real.exp (c - J)) (Real.exp (c - J)),
      (2 * Real.pi * Real.log z)⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ (y + 1) (z + 1) q σ t)
      ≤ cenBand q σ (θ / Real.log z) z := by
    rw [hτ]
    have hK₁ := diffK₁_le (y + 1) (z + 1) hq1
    have ha : (2 * q - 1) * diffK₁ (y + 1) (z + 1) q ≤ (2 * q - 1) * ((1 + (2 - 2 * q) / 3)
        * (Real.log ((z + 1 : ℕ) : ℝ) + Real.log 4 + 4)) :=
      mul_le_mul_of_nonneg_left hK₁ (by linarith)
    have hK₂ : diffK₂ (y + 1) (z + 1) ≤ Real.log ((z + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((z + 1 : ℕ) : ℝ) + 34 := sum_log_sq_mul_primesIco_le
    have h := setIntegral_inv_mul_diffQ_le (y + 1) (z + 1) hq0 hq1 hσ hτ0 ha hK₂
      (diffK₃_le (y + 1) (z + 1))
    have hpull : (∫ t in Set.Icc (-(θ / Real.log z)) (θ / Real.log z),
        (2 * Real.pi * Real.log z)⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ (y + 1) (z + 1) q σ t)
        = (2 * Real.pi * Real.log z)⁻¹ * ∫ t in Set.Icc (-(θ / Real.log z)) (θ / Real.log z),
          (σ ^ 2 + t ^ 2)⁻¹ * diffQ (y + 1) (z + 1) q σ t := by
      rw [← integral_const_mul]
      congr 1
      funext t
      ring
    rw [hpull, cenBand]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hCen0 : 0 ≤ ∫ t in Set.Icc (-Real.exp (c - J)) (Real.exp (c - J)),
      (2 * Real.pi * Real.log z)⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ (y + 1) (z + 1) q σ t :=
    setIntegral_nonneg measurableSet_Icc fun t _ =>
      mul_nonneg (mul_nonneg (by positivity) (inv_nonneg.2 (by positivity)))
        (diffQ_nonneg _ _ _ _ _)
  -- the coherent part and the far range
  have hCoh : (1 + 1 / η') * (2 / Real.exp (c - J)) * (2 * Real.pi * Real.log z)⁻¹
      = (1 + 1 / η') / (Real.pi * θ) := by
    rw [hτ]
    field_simp
  have hFar : (2 * Real.pi * Real.log z)⁻¹ * ((2 / Real.exp (c - ((0 : ℕ) : ℝ))) * mBand y z)
      = mBand y z / (Real.pi * θ * Real.exp J) := by
    have he : Real.exp (c - ((0 : ℕ) : ℝ)) = θ / Real.log z * Real.exp J := by
      rw [Nat.cast_zero, sub_zero, hcdef, Real.exp_add, Real.exp_log (by positivity)]
    rw [he]
    field_simp
  have hsum : ∑ k ∈ Finset.Ico 0 J, w k = ∑ k ∈ Finset.range J, w k := by
    rw [Finset.range_eq_Ico]
  -- assemble
  have hK : 0 < lemmaTConst z z' σ ε := lemmaTConst_pos hz' hz'z hσ hε
  have hKq : 0 ≤ (lemmaTConst z z' σ ε * Real.exp (2 * lx⁻¹)) ^ q :=
    Real.rpow_nonneg (mul_nonneg hK.le (Real.exp_pos _).le) _
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have hin1 : (∫ t in Set.Icc (-Real.exp (c - J)) (Real.exp (c - J)),
        (2 * Real.pi * Real.log z)⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ (y + 1) (z + 1) q σ t) ^ q
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (y + 1) (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ cenBand q σ (θ / Real.log z) z ^ q * pfBand q y z :=
    mul_le_mul (Real.rpow_le_rpow hCen0 hCen hq0') hP hP0
      (Real.rpow_nonneg (le_trans hCen0 hCen) _)
  have hin2 : ((1 + 1 / η') * (2 / Real.exp (c - J)) * (2 * Real.pi * Real.log z)⁻¹) ^ q
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (y + 1) (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ ((1 + 1 / η') / (Real.pi * θ)) ^ q * pfBand q y z := by
    rw [hCoh]
    exact mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by positivity) _)
  have hin3 : (1 + η') ^ q * (∑ k ∈ Finset.Ico 0 J, w k
        + ((2 * Real.pi * Real.log z)⁻¹ * ((2 / Real.exp (c - ((0 : ℕ) : ℝ))) * mBand y z)) ^ q)
      = (1 + η') ^ q * (∑ k ∈ Finset.range J, w k
        + (mBand y z / (Real.pi * θ * Real.exp J)) ^ q) := by
    rw [hsum, hFar]
  have hinner := add_le_add (add_le_add hin1 hin2) (le_of_eq hin3)
  have hmain := mul_le_mul_of_nonneg_left hinner hKq
  have hcoh2 : (lemmaTConst z z' σ ε * (σ / Real.log z)) ^ q
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (y + 1) (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ (lemmaTConst z z' σ ε * (σ / Real.log z)) ^ q * pfBand q y z :=
    mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by positivity) _)
  rw [bandLevelW, ← hlxdef, ← hσdef, ← hz'def]
  linarith [hLT, hatom, hcoh2, hmain]

/-- **A band's level above `½`, explicit.**  For `½ ≤ q ≤ 1`, `θ, η', ε > 0`, any
`c_s`, `2 ≤ y ≤ z ≤ x` with `log x > 1` and the sieve level `z' = ⌊z/(log x)^7⌋ ≥ 2`:

`E|𝒯_{y,z}(x)|^{2q} ≤ RMF.bandLevel q θ η' ε c_s x y z`,

`RMF.integral_rpow_norm_blockTruncationTail_le_bandLevelW` with each window the better of no split
and the split at `RMF.splitPt`. -/
theorem integral_rpow_norm_blockTruncationTail_le_bandLevel {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q θ η' ε cs x : ℝ} {y z : ℕ} (hq0 : 1 / 2 ≤ q)
    (hq1 : q ≤ 1) (hθ : 0 < θ) (hη' : 0 < η') (hε : 0 < ε) (hy : 2 ≤ y) (hyz : y ≤ z)
    (hzx : (z : ℝ) ≤ x) (hx : 1 < Real.log x) (hz' : 2 ≤ sieveLevel x z) :
    (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
        ^ (2 * q) ∂μ)
      ≤ bandLevel q θ η' ε cs x y z := by
  have hz2' : (2 : ℕ) ≤ z := le_trans hy hyz
  have hσ : 0 < (Real.log x ^ 2)⁻¹ := by
    have : 0 < Real.log x := by linarith
    positivity
  have hM := fun t => integral_normSq_line_le_mBand hX hy hyz hσ.le t
  rw [bandLevel_eq_bandLevelW]
  refine integral_rpow_norm_blockTruncationTail_le_bandLevelW hX hq0 hq1 hθ hη' hε hy hyz hzx hx
    hz' fun k _ => le_min ?_ ?_
  · exact window_band_le_nosplit_explicit hX y z hz2' hσ (by linarith) hq1 (bandT_pos k) hM
  · have h := window_band_le_split_explicit hX hy (le_splitPt hyz) (splitPt_le _ _ y z) hσ hq0
      hq1 (bandT_pos (θ := θ) (y := y) (z := z) k) (β := 2 * (1 - q)
        * (Real.log ((splitPt cs (bandT θ y z k) y z + 1 : ℕ) : ℝ) ^ 2 / 2
          + 15.003 * Real.log ((splitPt cs (bandT θ y z k) y z + 1 : ℕ) : ℝ) + 34)) le_rfl
    refine le_trans h (le_of_eq ?_)
    rw [winSplit, pfBand, mBand, add_comm (9.0028 / Real.log z)]

/-! ### The bottom level -/

/-- (PF) of the full product up to `z` at exponent `q`. -/
noncomputable def pfFull (q : ℝ) (z : ℕ) : ℝ :=
  Real.log z ^ (q * (2 * q - 1))
    * Real.exp (q * (2 * q - 1) * (0.2641 + 9.0028 / Real.log z + (2 - 2 * q) / 3))

/-- Mertens' bound on the full product's second moment: `log z·e^{0.2641 + 9.0028/log z}`. -/
noncomputable def mFull (z : ℕ) : ℝ := Real.log z * Real.exp (0.2641 + 9.0028 / Real.log z)

/-- `∑_{p ≤ z} 1/p ≤ log log z + 0.2641 + 9.0028/log z`. -/
lemma sum_primesIco_one_inv_le {z : ℕ} (hz : 2 ≤ z) :
    ∑ p ∈ primesIco 1 (z + 1), ((p : ℝ))⁻¹
      ≤ Real.log (Real.log z) + 0.2641 + 9.0028 / Real.log z := by
  rw [primesIco_one]
  linarith [sum_primesBelow_inv_le_log_log_add_mertens hz, mertens_const_le]

/-- The full product's second moment on the shifted line: `E‖F_z(½+σ+it)‖² ≤ RMF.mFull z`. -/
lemma integral_normSq_line_le_mFull {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {z : ℕ} (hz : 2 ≤ z) {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 1 (z + 1)
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ) ≤ mFull z := by
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  refine le_trans (integral_normSq_randomEulerProductIco_line_le_exp hX 1 (z + 1) hσ t) ?_
  refine le_trans (Real.exp_le_exp.2 (sum_primesIco_one_inv_le hz)) (le_of_eq ?_)
  rw [mFull, show Real.log (Real.log z) + 0.2641 + 9.0028 / Real.log z
      = Real.log (Real.log z) + (0.2641 + 9.0028 / Real.log z) by ring, Real.exp_add,
    Real.exp_log hlz]

/-- **The bottom's window by the split and Jensen, explicit**: as
`RMF.window_band_le_split_explicit` for the full product up to `z`, split at `2 ≤ z₁ ≤ z`, the
lower block's (PF) that of the full product (`RMF.pfFull`). -/
theorem window_bottom_le_split_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {z₁ z : ℕ} (hz₁ : 2 ≤ z₁) (hz₁z : z₁ ≤ z)
    {σ q T β : ℝ} (hσ : 0 < σ) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hT : 0 < T)
    (hβ : 2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) ≤ β) :
    (2 / (2 * Real.pi * Real.log z)) ^ q
        * (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 1 (z + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ pfFull q z₁
        * (taylorWindowW (β * T ^ 2) * mBand z₁ z / (Real.pi * T * Real.log z)) ^ q := by
  have hz₁2 : (2 : ℝ) ≤ z₁ := by exact_mod_cast hz₁
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast le_trans hz₁ hz₁z
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlz₁ : 0 < Real.log z₁ := Real.log_pos (by linarith)
  have hβ0 : 0 ≤ β := by
    have h2 : (0 : ℝ) ≤ Real.log ((z₁ + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have : (0 : ℝ) ≤ 2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) := by
      have : (0 : ℝ) ≤ 1 - q := by linarith
      positivity
    linarith
  have hR := setIntegral_inv_sq_add_sq_mul_exp_window_le_taylor σ hT hβ0
  have hMup := integral_normSq_Ico_shiftLine_le_mertens_ratio hX (z := z₁) (y := z) hz₁ hz₁z
    hσ.le 0
  have hV7 := integral_rpow_window_band_le_split_jensen_of_weight hX (y₀ := 1) (z₁ := z₁ + 1)
    (y := z + 1) (by omega) (by omega) hσ (by linarith) hq1 hT hβ0 hβ hR hMup
  have hs0 : shiftLine σ 0 = (((1 / 2 + σ : ℝ)) : ℂ) := by simp [shiftLine]
  rw [hs0] at hV7
  simp only [randomEulerProductIco_one] at hV7
  have hPF := hX.isRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_above_half
    hσ.le hq0 hq1 hz₁
  set P := ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (z₁ + 1)
    (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂μ with hPdef
  set R := taylorWindowW (β * T ^ 2) / T with hRdef
  set M := Real.log z / Real.log z₁ * Real.exp (9.0028 / Real.log z + 9.0028 / Real.log z₁)
    with hMdef
  have hW0 : 0 ≤ taylorWindowW (β * T ^ 2) := taylorWindowW_nonneg (mul_nonneg hβ0 (sq_nonneg T))
  have hc : (0 : ℝ) ≤ (2 / (2 * Real.pi * Real.log z)) ^ q := Real.rpow_nonneg (by positivity) _
  have hRM : (0 : ℝ) ≤ (2 / (2 * Real.pi * Real.log z) * (R * M)) ^ q :=
    Real.rpow_nonneg (by positivity) _
  have hV7' : (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 1 (z + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ) ≤ P * (R * M) ^ q := by
    simpa only [randomEulerProductIco_one] using hV7
  calc (2 / (2 * Real.pi * Real.log z)) ^ q
        * (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 1 (z + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ (2 / (2 * Real.pi * Real.log z)) ^ q * (P * (R * M) ^ q) :=
        mul_le_mul_of_nonneg_left hV7' hc
    _ = P * (2 / (2 * Real.pi * Real.log z) * (R * M)) ^ q := by
        rw [Real.mul_rpow (x := 2 / (2 * Real.pi * Real.log z)) (y := R * M) (by positivity)
          (by positivity)]
        ring
    _ ≤ pfFull q z₁ * (2 / (2 * Real.pi * Real.log z) * (R * M)) ^ q :=
        mul_le_mul_of_nonneg_right hPF hRM
    _ = _ := by
        congr 2
        rw [hRdef, hMdef, mBand, add_comm (9.0028 / Real.log z)]
        field_simp

/-- The bottom's window bound without a split. -/
noncomputable def winNoSplitFull (q T : ℝ) (z : ℕ) : ℝ :=
  ((Real.exp 1 - 1) * mFull z / (Real.pi * T * Real.log z)) ^ q

/-- The bottom's window bound by the split at `z₁` and Jensen. -/
noncomputable def winSplitFull (q T : ℝ) (z₁ z : ℕ) : ℝ :=
  pfFull q z₁
    * (taylorWindowW (2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2)
      * mBand z₁ z / (Real.pi * T * Real.log z)) ^ q

/-- The number of the bottom's windows at the central cut `θ`, up to the height `T_m`. -/
noncomputable def bottomJ (θ Tm : ℝ) (z : ℕ) : ℕ := ⌈Real.log (Tm * Real.log z / θ)⌉₊

/-- The height of the bottom's `k`-th window: `(θ/log z)e^{J-k}`. -/
noncomputable def bottomT (θ Tm : ℝ) (z k : ℕ) : ℝ :=
  Real.exp (Real.log (θ / Real.log z) + bottomJ θ Tm z - k)

/-- **The explicit bound on the bottom level** (the full product up to `z`), windows up to the
height `T_m`. -/
noncomputable def bottomLevel (q θ η' ε cs Tm x : ℝ) (z : ℕ) : ℝ :=
  (Real.exp (-(Real.log x / Real.log z)) * mFull z ^ Real.exp 1) ^ q
  + (lemmaTConst z (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε
      * ((Real.log x ^ 2)⁻¹ / Real.log z)) ^ q * pfFull q z
  + (lemmaTConst z (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε * Real.exp (2 * (Real.log x)⁻¹)) ^ q
    * (cenBand q (Real.log x ^ 2)⁻¹ (θ / Real.log z) z ^ q * pfFull q z
      + ((1 + 1 / η') / (Real.pi * θ)) ^ q * pfFull q z
      + (1 + η') ^ q * (∑ k ∈ Finset.range (bottomJ θ Tm z),
          min (winNoSplitFull q (bottomT θ Tm z k) z)
            (winSplitFull q (bottomT θ Tm z k) (splitPt cs (bottomT θ Tm z k) 2 z) z)
        + (mFull z / (Real.pi * θ * Real.exp (bottomJ θ Tm z))) ^ q))
  + smallQReductionErr x (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε ^ q

/-- **The bottom level with supplied window bounds** `w k`: `RMF.bottomLevel` with the windows'
sum `∑_{k<J} w k` (`RMF.bottomLevel_eq_bottomLevelW`). -/
noncomputable def bottomLevelW (q θ η' ε Tm x : ℝ) (z : ℕ) (w : ℕ → ℝ) : ℝ :=
  (Real.exp (-(Real.log x / Real.log z)) * mFull z ^ Real.exp 1) ^ q
  + (lemmaTConst z (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε
      * ((Real.log x ^ 2)⁻¹ / Real.log z)) ^ q * pfFull q z
  + (lemmaTConst z (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε * Real.exp (2 * (Real.log x)⁻¹)) ^ q
    * (cenBand q (Real.log x ^ 2)⁻¹ (θ / Real.log z) z ^ q * pfFull q z
      + ((1 + 1 / η') / (Real.pi * θ)) ^ q * pfFull q z
      + (1 + η') ^ q * (∑ k ∈ Finset.range (bottomJ θ Tm z), w k
        + (mFull z / (Real.pi * θ * Real.exp (bottomJ θ Tm z))) ^ q))
  + smallQReductionErr x (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε ^ q

lemma bottomLevel_eq_bottomLevelW (q θ η' ε cs Tm x : ℝ) (z : ℕ) :
    bottomLevel q θ η' ε cs Tm x z = bottomLevelW q θ η' ε Tm x z fun k =>
      min (winNoSplitFull q (bottomT θ Tm z k) z)
        (winSplitFull q (bottomT θ Tm z k) (splitPt cs (bottomT θ Tm z k) 2 z) z) := rfl

/-- **The bottom level above `½` with supplied window bounds.**  For `½ ≤ q ≤ 1`,
`θ, η', ε > 0`, any `T_m`, `2 ≤ z ≤ x` with `log x > 1`, the sieve level `⌊z/(log x)^7⌋ ≥ 2` and
bounds `w k` on the windows' moments at `σ = (log x)^{-2}`, heights `RMF.bottomT`:

`E|𝒯_z(x)|^{2q} ≤ RMF.bottomLevelW q θ η' ε T_m x z w`,

the band `(0, z]` of `RMF.integral_rpow_norm_blockTruncationTail_le_split`
(`RMF.blockTruncationTail_zero`), with the full product's (PF) and Mertens. -/
theorem integral_rpow_norm_truncationTail_le_bottomLevelW {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q θ η' ε Tm x : ℝ} {z : ℕ} {w : ℕ → ℝ} (hq0 : 1 / 2 ≤ q)
    (hq1 : q ≤ 1) (hθ : 0 < θ) (hη' : 0 < η') (hε : 0 < ε) (hz : 2 ≤ z)
    (hzx : (z : ℝ) ≤ x) (hx : 1 < Real.log x) (hz' : 2 ≤ sieveLevel x z)
    (hw : ∀ k < bottomJ θ Tm z, (2 / (2 * Real.pi * Real.log z)) ^ q
      * (∫ ω, (∫ t in Set.Icc (bottomT θ Tm z k / Real.exp 1) (bottomT θ Tm z k),
        (((Real.log x ^ 2)⁻¹) ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) 1 (z + 1)
            (shiftLine (Real.log x ^ 2)⁻¹ t) ω‖ ^ 2) ^ q ∂μ) ≤ w k) :
    (∫ ω, ‖truncationTail (fun ω => squarefreeExtension fun p => X p ω) z x ω‖ ^ (2 * q) ∂μ)
      ≤ bottomLevelW q θ η' ε Tm x z w := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  simp_rw [← blockTruncationTail_zero]
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hx0 : 0 < x := lt_of_lt_of_le (by linarith) hzx
  have hlx : 0 < Real.log x := by linarith
  set lx := Real.log x with hlxdef
  set σ := (lx ^ 2)⁻¹ with hσdef
  have hσ : 0 < σ := by positivity
  have hσ1 : σ < 1 := by
    rw [hσdef]
    exact inv_lt_one_of_one_lt₀ (by nlinarith)
  set z' := sieveLevel x z with hz'def
  have hz'z : z' ≤ z := by
    rw [hz'def, sieveLevel]
    refine Nat.floor_le_of_le ?_
    exact div_le_self (by positivity) (one_le_pow₀ hx.le)
  have hσlog : σ * Real.log (x / z) ≤ lx⁻¹ := by
    have hlog : Real.log (x / z) ≤ lx := by
      rw [Real.log_div hx0.ne' (by positivity), hlxdef]
      linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ z)]
    calc σ * Real.log (x / z) ≤ σ * lx := mul_le_mul_of_nonneg_left hlog hσ.le
      _ = lx⁻¹ := by rw [hσdef]; field_simp
  have hzη : 1 + σ < z := by linarith
  set J := bottomJ θ Tm z with hJdef
  set c := Real.log (θ / Real.log z) + (J : ℝ) with hcdef
  have hT : ∀ k : ℕ, bottomT θ Tm z k = Real.exp (c - k) := fun k => by
    rw [bottomT, hcdef]
  have hM : ∀ t : ℝ, (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (0 + 1) (z + 1) ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ) ≤ mFull z :=
    fun t => integral_normSq_line_le_mFull hX hz hσ.le t
  have hw' : ∀ k ∈ Finset.Ico 0 J, (2 / (2 * Real.pi * Real.log z)) ^ q
      * (∫ ω, (∫ t in Set.Icc (Real.exp (c - k) / Real.exp 1) (Real.exp (c - k)),
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (0 + 1) (z + 1) (shiftLine σ t)
            ω‖ ^ 2) ^ q ∂μ) ≤ w k := by
    intro k hk
    rw [← hT k]
    exact hw k (Finset.mem_Ico.1 hk).2
  have hLT := integral_rpow_norm_blockTruncationTail_le_split hX (Nat.zero_le z) hz' hz'z hzx hσ
    hσlog hσ hzη hε hq0 hq1 hη' (Nat.zero_le J) (c := c) (M := mFull z) hM hw'
  -- the atom, by Jensen
  have hatom : (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) 0 z x ω‖
      ^ (2 * q) ∂μ) ≤ (Real.exp (-(lx / Real.log z)) * mFull z ^ Real.exp 1) ^ q := by
    have hmeas : Measurable fun ω =>
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) 0 z x ω‖ ^ 2 :=
      ((measurable_smoothAlgebra_blockTailSum 0 z x).mono (smoothAlgebra_le hX z)
        le_rfl).norm.pow_const 2
    have hint : Integrable (fun ω =>
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) 0 z x ω‖ ^ 2) μ := by
      refine (memLp_top_of_bound hmeas.aestronglyMeasurable ((primorial z : ℝ) ^ 2)
        ?_).integrable le_top
      filter_upwards [ae_norm_blockTailSum_le hRa 0 z x] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hω 2
    have hB : (∫ ω,
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) 0 z x ω‖ ^ 2 ∂μ)
        ≤ Real.exp (-(lx / Real.log z)) * mFull z ^ Real.exp 1 := by
      refine le_trans (integral_normSq_blockTailSum_le_exp_sum hX 0 hz hx0) ?_
      have hxV : x ^ (-(Real.log z)⁻¹) = Real.exp (-(lx / Real.log z)) := by
        rw [Real.rpow_def_of_pos hx0, hlxdef]
        congr 1
        ring
      rw [hxV]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have hsum := sum_primesIco_one_inv_le hz
      have hmF : 0 < mFull z := by rw [mFull]; positivity
      rw [Real.rpow_def_of_pos hmF]
      refine Real.exp_le_exp.2 ?_
      have hlog : Real.log (mFull z) = Real.log (Real.log z) + (0.2641 + 9.0028 / Real.log z) := by
        rw [mFull, Real.log_mul hlz.ne' (Real.exp_pos _).ne', Real.log_exp]
      rw [hlog]
      have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      have hsum' : ∑ p ∈ primesIco (0 + 1) (z + 1), ((p : ℝ))⁻¹
          ≤ Real.log (Real.log z) + 0.2641 + 9.0028 / Real.log z := hsum
      nlinarith [mul_le_mul_of_nonneg_left hsum' he]
    have hpow : ∀ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) 0 z x ω‖
          ^ (2 * q)
        = (‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) 0 z x ω‖ ^ 2) ^ q := by
      intro ω
      rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two]
    simp_rw [hpow]
    exact integral_rpow_le_rpow_of_integral_le (by linarith) hq1
      (Filter.Eventually.of_forall fun ω => sq_nonneg _) hint hB
  -- (PF) at the critical point
  have hP : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (0 + 1)
      (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ) ≤ pfFull q z := by
    have h := hRa.integral_norm_randomEulerProduct_shift_rpow_le_above_half (σ := 0) le_rfl
      hq0 hq1 hz
    have hs : (((1 / 2 + 0 : ℝ)) : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [hs] at h
    simp only [zero_add, randomEulerProductIco_one]
    exact h
  have hP0 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (0 + 1) (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  -- the central window
  have hτ : Real.exp (c - J) = θ / Real.log z := by
    rw [hcdef, show Real.log (θ / Real.log z) + (J : ℝ) - J = Real.log (θ / Real.log z) by ring,
      Real.exp_log (by positivity)]
  have hτ0 : 0 < θ / Real.log z := by positivity
  have hCen : (∫ t in Set.Icc (-Real.exp (c - J)) (Real.exp (c - J)),
      (2 * Real.pi * Real.log z)⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ (0 + 1) (z + 1) q σ t)
      ≤ cenBand q σ (θ / Real.log z) z := by
    rw [hτ]
    have hK₁ := diffK₁_le (0 + 1) (z + 1) hq1
    have ha : (2 * q - 1) * diffK₁ (0 + 1) (z + 1) q ≤ (2 * q - 1) * ((1 + (2 - 2 * q) / 3)
        * (Real.log ((z + 1 : ℕ) : ℝ) + Real.log 4 + 4)) :=
      mul_le_mul_of_nonneg_left hK₁ (by linarith)
    have hK₂ : diffK₂ (0 + 1) (z + 1) ≤ Real.log ((z + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((z + 1 : ℕ) : ℝ) + 34 := sum_log_sq_mul_primesIco_le
    have h := setIntegral_inv_mul_diffQ_le (0 + 1) (z + 1) hq0 hq1 hσ hτ0 ha hK₂
      (diffK₃_le (0 + 1) (z + 1))
    have hpull : (∫ t in Set.Icc (-(θ / Real.log z)) (θ / Real.log z),
        (2 * Real.pi * Real.log z)⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ (0 + 1) (z + 1) q σ t)
        = (2 * Real.pi * Real.log z)⁻¹ * ∫ t in Set.Icc (-(θ / Real.log z)) (θ / Real.log z),
          (σ ^ 2 + t ^ 2)⁻¹ * diffQ (0 + 1) (z + 1) q σ t := by
      rw [← integral_const_mul]
      congr 1
      funext t
      ring
    rw [hpull, cenBand]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hCen0 : 0 ≤ ∫ t in Set.Icc (-Real.exp (c - J)) (Real.exp (c - J)),
      (2 * Real.pi * Real.log z)⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ (0 + 1) (z + 1) q σ t :=
    setIntegral_nonneg measurableSet_Icc fun t _ =>
      mul_nonneg (mul_nonneg (by positivity) (inv_nonneg.2 (by positivity)))
        (diffQ_nonneg _ _ _ _ _)
  have hCoh : (1 + 1 / η') * (2 / Real.exp (c - J)) * (2 * Real.pi * Real.log z)⁻¹
      = (1 + 1 / η') / (Real.pi * θ) := by
    rw [hτ]
    field_simp
  have hFar : (2 * Real.pi * Real.log z)⁻¹ * ((2 / Real.exp (c - ((0 : ℕ) : ℝ))) * mFull z)
      = mFull z / (Real.pi * θ * Real.exp J) := by
    have he : Real.exp (c - ((0 : ℕ) : ℝ)) = θ / Real.log z * Real.exp J := by
      rw [Nat.cast_zero, sub_zero, hcdef, Real.exp_add, Real.exp_log (by positivity)]
    rw [he]
    field_simp
  have hsum : ∑ k ∈ Finset.Ico 0 J, w k = ∑ k ∈ Finset.range J, w k := by
    rw [Finset.range_eq_Ico]
  have hK : 0 < lemmaTConst z z' σ ε := lemmaTConst_pos hz' hz'z hσ hε
  have hKq : 0 ≤ (lemmaTConst z z' σ ε * Real.exp (2 * lx⁻¹)) ^ q :=
    Real.rpow_nonneg (mul_nonneg hK.le (Real.exp_pos _).le) _
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have hin1 : (∫ t in Set.Icc (-Real.exp (c - J)) (Real.exp (c - J)),
        (2 * Real.pi * Real.log z)⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ (0 + 1) (z + 1) q σ t) ^ q
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (0 + 1) (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ cenBand q σ (θ / Real.log z) z ^ q * pfFull q z :=
    mul_le_mul (Real.rpow_le_rpow hCen0 hCen hq0') hP hP0
      (Real.rpow_nonneg (le_trans hCen0 hCen) _)
  have hin2 : ((1 + 1 / η') * (2 / Real.exp (c - J)) * (2 * Real.pi * Real.log z)⁻¹) ^ q
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (0 + 1) (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ ((1 + 1 / η') / (Real.pi * θ)) ^ q * pfFull q z := by
    rw [hCoh]
    exact mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by positivity) _)
  have hin3 : (1 + η') ^ q * (∑ k ∈ Finset.Ico 0 J, w k
        + ((2 * Real.pi * Real.log z)⁻¹ * ((2 / Real.exp (c - ((0 : ℕ) : ℝ))) * mFull z)) ^ q)
      = (1 + η') ^ q * (∑ k ∈ Finset.range J, w k
        + (mFull z / (Real.pi * θ * Real.exp J)) ^ q) := by
    rw [hsum, hFar]
  have hinner := add_le_add (add_le_add hin1 hin2) (le_of_eq hin3)
  have hmain := mul_le_mul_of_nonneg_left hinner hKq
  have hcoh2 : (lemmaTConst z z' σ ε * (σ / Real.log z)) ^ q
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (0 + 1) (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ (lemmaTConst z z' σ ε * (σ / Real.log z)) ^ q * pfFull q z :=
    mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by positivity) _)
  rw [bottomLevelW, ← hlxdef, ← hσdef, ← hz'def]
  linarith [hLT, hatom, hcoh2, hmain]

/-- **The bottom level above `½`, explicit.**  For `½ ≤ q ≤ 1`, `θ, η', ε > 0`, any
`c_s` and `T_m`, `2 ≤ z ≤ x` with `log x > 1` and the sieve level `⌊z/(log x)^7⌋ ≥ 2`:

`E|𝒯_z(x)|^{2q} ≤ RMF.bottomLevel q θ η' ε c_s T_m x z`,

`RMF.integral_rpow_norm_truncationTail_le_bottomLevelW` with each window the better of no split
and the split at `RMF.splitPt`. -/
theorem integral_rpow_norm_truncationTail_le_bottomLevel {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q θ η' ε cs Tm x : ℝ} {z : ℕ} (hq0 : 1 / 2 ≤ q)
    (hq1 : q ≤ 1) (hθ : 0 < θ) (hη' : 0 < η') (hε : 0 < ε) (hz : 2 ≤ z)
    (hzx : (z : ℝ) ≤ x) (hx : 1 < Real.log x) (hz' : 2 ≤ sieveLevel x z) :
    (∫ ω, ‖truncationTail (fun ω => squarefreeExtension fun p => X p ω) z x ω‖ ^ (2 * q) ∂μ)
      ≤ bottomLevel q θ η' ε cs Tm x z := by
  have hσ : 0 < (Real.log x ^ 2)⁻¹ := by
    have : 0 < Real.log x := by linarith
    positivity
  have hM : ∀ t : ℝ, (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (0 + 1) (z + 1) ((1 / 2 : ℂ) + (((Real.log x ^ 2)⁻¹ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        ∂μ) ≤ mFull z :=
    fun t => integral_normSq_line_le_mFull hX hz hσ.le t
  rw [bottomLevel_eq_bottomLevelW]
  refine integral_rpow_norm_truncationTail_le_bottomLevelW hX hq0 hq1 hθ hη' hε hz hzx hx hz'
    fun k _ => le_min ?_ ?_
  · exact window_band_le_nosplit_explicit hX 0 z hz hσ (by linarith) hq1 (Real.exp_pos _) hM
  · exact window_bottom_le_split_explicit hX (le_splitPt hz) (splitPt_le _ _ 2 z) hσ hq0 hq1
      (Real.exp_pos _) le_rfl

end RMF
