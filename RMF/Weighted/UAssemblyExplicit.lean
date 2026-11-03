/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UFarExplicit
import RMF.Weighted.TenNumeralExplicit
import RMF.Weighted.MidNumeralExplicit

/-!
# The first moment below `q = ½`: the assemblies at exponent `q`

`E|S(x)|^{2q}` for `0 < q ≤ ½` from its pieces, with the parameters of the first moment at
`q = ½` (`RMF/Weighted/TenAssemblyExplicit.lean` for `x ≥ exp(e^{110})`,
`RMF/Weighted/MidAssemblyExplicit.lean` for `x ≥ exp(e⁷)`).  (PF) is the bound on the moment
`E‖F(s)‖^{2q}` of the Euler product at a point, of size `(log y)^{-q(1-2q)}` for the product up
to `y` (`RMF.uPFyAt`).

* **the windows at exponent `q`** (`RMF.uWindowBound`): (PF) at the split point times the window's
  constant, times the weighted chaos's factor when the window has room, capped at `1` (Jensen);
  the chaos's free parameters are passed per window (`RMF.WinChaos`), at the offset
  `max(k + 8, 105)` (`RMF.uOffset`);
* **the far range** (`RMF.uFarBound`): Jensen, or the chaos windows of
  `RMF.integral_rpow_farRange_le_chaos` at `r = 2/3` when every far window has room
  (`RMF.FarChaos`);
* **the assemblies**: `RMF.integral_rpow_weightedRademacherSum_le_u_assembly` (large range) and
  `RMF.integral_rpow_weightedRademacherSum_le_u_mid_assembly` (middle range, every window by
  Jensen).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The chaos's free parameters -/

/-- The free parameters of one mesoscopic window's weighted chaos: level `A`, `λ`, `T`, `κ` and
room `N` (the tilt `β = 11/20` and `δ = 1/50` are fixed). -/
structure WinChaos where
  /-- the level -/
  A : ℝ
  /-- the decoupling parameter `λ` -/
  lam : ℝ
  /-- the averaged barrier's `T` -/
  Tr : ℝ
  /-- the averaged barrier's `κ` -/
  kap : ℝ
  /-- the room: the number of blocks above the window -/
  N : ℕ

/-- The side conditions on a window's chaos parameters. -/
structure WinChaos.Valid (c : WinChaos) : Prop where
  Tr : 4 < c.Tr
  kap : 1 ≤ c.kap
  A : 20 ≤ c.A
  lam : 1 ≤ c.lam
  N : 2000 ≤ c.N
  room : c.A / 4 + 3 * Real.sqrt (c.N : ℝ) / 4 + 1 ≤ 1 / 50 * c.N

/-- A window's chaos constant at the tilt `E₀`, exponent `q` and level shift `K`. -/
noncomputable def WinChaos.const (c : WinChaos) (E₀ q K : ℝ) : ℝ :=
  shiftMomentConst 1 (radAveragedConst E₀ (11 / 20) c.Tr c.kap)
    (radBlockBadConst E₀ (11 / 20) * K) c.A (radAveragedShift E₀ (11 / 20) c.Tr c.kap) c.lam
    (1 / 50) q

/-- The free parameters of the far windows' chaos: `λ`, `T`, `κ` shared, a level and a room for
each far window. -/
structure FarChaos where
  /-- the decoupling parameter `λ` -/
  lam : ℝ
  /-- the averaged barrier's `T` -/
  Tr : ℝ
  /-- the averaged barrier's `κ` -/
  kap : ℝ
  /-- the level of far window `j` -/
  A : ℕ → ℝ
  /-- the room of far window `j` -/
  N : ℕ → ℕ

/-- The side conditions on the far windows' chaos parameters. -/
structure FarChaos.Valid (c : FarChaos) : Prop where
  Tr : 4 < c.Tr
  kap : 1 ≤ c.kap
  lam : 1 ≤ c.lam
  A : ∀ j, 20 ≤ c.A j
  N : ∀ j, 2000 ≤ c.N j
  room : ∀ j, c.A j / 4 + 3 * Real.sqrt (c.N j : ℝ) / 4 + 1 ≤ 1 / 50 * c.N j

/-- The far window `j`'s chaos constant at the tilt `E₀` (exponent `2/3`, level shift
`e^{2j+102}`). -/
noncomputable def FarChaos.const (c : FarChaos) (E₀ : ℝ) (j : ℕ) : ℝ :=
  shiftMomentConst 1 (radAveragedConst E₀ (11 / 20) c.Tr c.kap)
    (radBlockBadConst E₀ (11 / 20) * Real.exp (2 * (j : ℝ) + 102)) (c.A j)
    (radAveragedShift E₀ (11 / 20) c.Tr c.kap) c.lam (1 / 50) (2 / 3)

/-- `3 ≤ 8δ√N` at `δ = 1/50` once `N ≥ 2000`. -/
lemma mono_of_room {N : ℕ} (hN : 2000 ≤ N) : (3 : ℝ) ≤ 8 * (1 / 50) * Real.sqrt (N : ℝ) := by
  refine le_trans half_mono (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  exact Real.sqrt_le_sqrt (by exact_mod_cast hN)

/-! ### The windows at exponent `q` -/

lemma thetaWindowConstQ_nonneg {θ q : ℝ} (hθ : 0 < θ) (hq : q ≤ 1) (k y : ℕ) :
    0 ≤ thetaWindowConstQ θ q k y := by
  unfold thetaWindowConstQ
  have h1 : 0 ≤ 2 * (1 - q) * thetaWindowExp θ k :=
    mul_nonneg (by linarith) (thetaWindowExp_nonneg hθ.le k)
  have h2 := taylorWindowW_nonneg h1
  positivity

/-- The offset of the `k`-th window: at least `k + 8`, and at least the prime number theorem's
floor `105`. -/
def uOffset (k : ℕ) : ℕ := max (k + 8) 105

/-- The `k`-th window's bound at exponent `q`: (PF) times `G_k(q)^{2q}` times the chaos factor
when the window has room, capped at `1` (Jensen). -/
noncomputable def uWindowBound (P : ℕ → WinChaos) (q x : ℝ) (k : ℕ) : ℝ :=
  thetaPF (halfSigma x) (3 / 2) q k * thetaWindowConstQ (3 / 2) q k (halfY x) ^ q
    * (if (P k).N ≤ harperBlockCount (uOffset k) (halfY x) then
        min 1 ((P k).const (1 / (16 * Real.log (Real.log x))) q
            (Real.exp ((uOffset k : ℝ) - k))
          * (1 + (1 - q) * Real.sqrt (harperBlockCount (uOffset k) (halfY x) : ℝ)) ^ (-q))
      else 1)

set_option maxHeartbeats 1000000 in
-- the chaos window's hypotheses, discharged one by one
/-- **The `k`-th window at exponent `q`**: by Jensen, and by the weighted chaos when it has room
(`RMF.window_theta_le_chaos_q` at the offset `max(k + 8, 105)`). -/
lemma uWindow_le {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 110) ≤ x) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) {P : ℕ → WinChaos}
    (hP : ∀ k, (P k).Valid) {k : ℕ} (hk : k ∈ Finset.Ico 4 (tenJ x)) :
    (2 / Real.log (halfY x)) ^ q * ∫ ω, (∫ t in Set.Icc
        (Real.exp (-(k : ℝ)) / Real.exp 1) (Real.exp (-(k : ℝ))), (halfSigma x ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
          (shiftLine (halfSigma x) t) ω‖ ^ 2) ^ q ∂μ ≤ uWindowBound P q x k := by
  obtain ⟨-, hL, hΛ, -, -, haL⟩ := half_params hx
  obtain ⟨hy2, -, hlogy_le, -, -, -⟩ := halfY_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hσ : 0 < halfSigma x := by rw [halfSigma]; positivity
  have hy2R : (2 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast hy2
  have hlogy : 0 < Real.log (halfY x) := Real.log_pos (by linarith)
  have hLLy : Real.log (Real.log (halfY x)) ≤ Real.log (Real.log x) :=
    Real.log_le_log hlogy (le_trans hlogy_le haL)
  rw [Finset.mem_Ico] at hk
  have hky := tenJ_window hlogy (by omega : k ≠ 0) (by rw [tenJ] at hk; exact hk.2)
  have hJ := window_theta_le_jensen_q hX (θ := 3 / 2) (by norm_num) hq0 hq hσ (by omega) hky
  have hG0 : 0 ≤ thetaPF (halfSigma x) (3 / 2) q k * thetaWindowConstQ (3 / 2) q k (halfY x) ^ q :=
    mul_nonneg (thetaPF_nonneg _ _ _ _ (by norm_num))
      (Real.rpow_nonneg (thetaWindowConstQ_nonneg (by norm_num) (by linarith) k (halfY x)) _)
  rw [uWindowBound]
  split_ifs with hc
  · have hPk := hP k
    have hkD : k + 8 ≤ uOffset k := le_max_left _ _
    have hD105 : 105 ≤ uOffset k := le_max_right _ _
    have hNpos : 2000 ≤ harperBlockCount (uOffset k) (halfY x) := le_trans hPk.N hc
    have hDy : uOffset k ≤ ⌊Real.log (Real.log (halfY x : ℝ))⌋₊ := by
      rw [harperBlockCount] at hNpos
      omega
    have hΛbig : 2105 ≤ Real.log (Real.log x) := by
      have hfl : uOffset k + 2000 ≤ ⌊Real.log (Real.log (halfY x : ℝ))⌋₊ := by
        rw [harperBlockCount] at hNpos
        omega
      have h1 : ((uOffset k + 2000 : ℕ) : ℝ) ≤ Real.log (Real.log (halfY x)) :=
        (Nat.le_floor_iff' (by omega)).1 hfl
      push_cast at h1
      have : (105 : ℝ) ≤ (uOffset k : ℝ) := by exact_mod_cast hD105
      linarith
    have hC := window_theta_le_chaos_q (1 / (16 * Real.log (Real.log x))) (11 / 20)
      (by positivity) (half_tilt_le hΛ) (by norm_num) (by norm_num) (Tr := (P k).Tr)
      (κ := (P k).kap) (Amax := (P k).A) (δ := 1 / 50) (N := (P k).N) hPk.Tr hPk.kap
      (by norm_num) (by norm_num) hPk.room (mono_of_room hPk.N) hX (θ := 3 / 2) (by norm_num)
      (by norm_num) hq0 hq (k := k) (y := halfY x) (D := uOffset k) (σ := halfSigma x)
      (A := (P k).A) (lam := (P k).lam) hσ (by omega) hkD hD105 hDy (halfSigma_mul_log_le hx) hc
      (le_trans (half_level_le hΛbig) hPk.A) le_rfl hPk.lam
    rw [mul_min_of_nonneg _ _ hG0, mul_one]
    exact le_min hJ hC
  · rw [mul_one]
    exact hJ

/-! ### The far range at exponent `q` -/

/-- The far range's bound at exponent `q`: by Jensen, or by the chaos windows up to `e^{n-4}`
(`RMF.integral_rpow_farRange_le_chaos` at `r = 2/3`) when every far window has room. -/
noncomputable def uFarBound (Pf : FarChaos) (n : ℕ) (q x : ℝ) : ℝ :=
  if 105 + n ≤ ⌊Real.log (Real.log (halfY x : ℝ))⌋₊
      ∧ ∀ j < n, Pf.N j ≤ harperBlockCount (105 + j) (halfY x) then
    min ((2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ q)
      ((∑ j ∈ Finset.range n, Pf.const (1 / (16 * Real.log (Real.log x))) j
          * (2 * 1.195 * (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ))) ^ (2 / 3 : ℝ)
          * (1 + (1 - 2 / 3) * Real.sqrt (harperBlockCount (105 + j) (halfY x) : ℝ))
            ^ (-(2 / 3 : ℝ))
        + (2 * 1.195 / Real.exp ((n : ℝ) - 4)) ^ (2 / 3 : ℝ)) ^ (q / (2 / 3)))
  else (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ q

/-- **The far range at exponent `q`**: by Jensen, and by the chaos windows when they have room. -/
lemma uFar_le {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 110) ≤ x) (hq0 : 0 < q) (hq : q ≤ 1 / 2) {Pf : FarChaos}
    (hPf : Pf.Valid) (n : ℕ) :
    (∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t in {t : ℝ | Real.exp (-((4 : ℕ) : ℝ)) < |t|},
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
            ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
          / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ) ≤ uFarBound Pf n q x := by
  obtain ⟨-, hL, hΛ, -, -, haL⟩ := half_params hx
  obtain ⟨hy2, -, hlogy_le, -, hy99, -⟩ := halfY_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hσ : 0 < halfSigma x := by rw [halfSigma]; positivity
  have hy2R : (2 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast hy2
  have hlogy : 0 < Real.log (halfY x) := Real.log_pos (by linarith)
  have hLLy : Real.log (Real.log (halfY x)) ≤ Real.log (Real.log x) :=
    Real.log_le_log hlogy (le_trans hlogy_le haL)
  have hJ := integral_rpow_eulerProductLine_tail_le_explicit hX (q := q) hq0 (by linarith) hy99
    hσ (T := Real.exp (-((4 : ℕ) : ℝ))) (Real.exp_pos _)
  rw [uFarBound]
  split_ifs with hc
  · refine le_min hJ ?_
    have h4 : Real.exp (-((4 : ℕ) : ℝ)) = Real.exp (-4) := by norm_num
    rw [h4]
    obtain ⟨hDy, hroom⟩ := hc
    have hlev : ∀ j < n, radBlockBadLevel (1 / (16 * Real.log (Real.log x))) ≤ Pf.A j := by
      intro j hj
      have hN0 := le_trans (hPf.N j) (hroom j hj)
      have hfl : 105 + j + 2000 ≤ ⌊Real.log (Real.log (halfY x : ℝ))⌋₊ := by
        rw [harperBlockCount] at hN0
        omega
      have h1 : ((105 + j + 2000 : ℕ) : ℝ) ≤ Real.log (Real.log (halfY x)) :=
        (Nat.le_floor_iff' (by omega)).1 hfl
      push_cast at h1
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      exact le_trans (half_level_le (by linarith)) (hPf.A j)
    exact integral_rpow_farRange_le_chaos (1 / (16 * Real.log (Real.log x))) (11 / 20)
      (by positivity) (half_tilt_le hΛ) (by norm_num) (by norm_num) (Tr := Pf.Tr) (κ := Pf.kap)
      (δ := 1 / 50) (lam := Pf.lam) hPf.Tr hPf.kap (by norm_num) (by norm_num) hPf.lam
      (N := Pf.N) (A := Pf.A) hX (r := 2 / 3) hσ hy99 (halfSigma_mul_log_le hx) hq0
      (by linarith) (by norm_num) hDy fun j hj => ⟨hPf.room j, mono_of_room (hPf.N j),
        hroom j (Finset.mem_range.1 hj), hlev j (Finset.mem_range.1 hj)⟩
  · exact hJ

/-! ### The assembly at exponent `q` -/

/-- (PF) at `y` at exponent `q`: `e^{q(1-2q)(9.0028/log y - 3/20)}(log y)^{-q(1-2q)}`. -/
noncomputable def uPFyAt (q : ℝ) (y : ℕ) : ℝ :=
  Real.exp (q * (1 - 2 * q) * (9.0028 / Real.log y - 3 / 20)) * Real.log y ^ (q * (2 * q - 1))

/-- The central window's constant at exponent `q`, tilt `σ`, level `y` and width `e^{-J}`
(`RMF.tenCen` at `q = ½`). -/
noncomputable def uCenAt (q σ : ℝ) (y J : ℕ) : ℝ :=
  (Real.pi / σ + 2 * (Real.exp (2 * (1 - q)
      * (Real.log ((y : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((y : ℝ) + 1) + 34)
      * Real.exp (-(J : ℝ)) ^ 2) - 1) / Real.exp (-(J : ℝ))) / Real.log y

/-- The central window's (PF) factor at exponent `q`, tilt `σ` and level `y`. -/
noncomputable def uPFcAt (q σ : ℝ) (y : ℕ) : ℝ :=
  Real.exp (q * (1 - 2 * q) * (9.0028 / Real.log y + 2 * σ * (Real.log y + Real.log 4 + 4)
      - 3 / 20)) * Real.log y ^ (q * (2 * q - 1))

set_option maxHeartbeats 1000000 in
-- the reduction, three ranges and five bounds in one proof
/-- **`E|S(x)|^{2q}` from its pieces, at exponent `0 < q ≤ ½`**.  For `x ≥ exp(e^{110})`, any
window chaos parameters `P` and far chaos parameters `P_f` (valid), and any number `n` of far
windows:

`E|S(x)|^{2q} ≤ PF_q(y) + T^q + C_R^q·(C_c(q)^q·PF_c(q) + b_far + ∑_{4≤k<J₀} b_k) + E_err^q`,

`PF_q(y) = RMF.uPFyAt`, `C_c = RMF.uCenAt`, `PF_c = RMF.uPFcAt`, `b_far = RMF.uFarBound`,
`b_k = RMF.uWindowBound`: `RMF.integral_norm_weightedRademacherSum_le_ten_assembly` at exponent
`q`. -/
theorem integral_rpow_weightedRademacherSum_le_u_assembly {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hq0 : 0 < q) (hq : q ≤ 1 / 2) {P : ℕ → WinChaos} (hP : ∀ k, (P k).Valid) {Pf : FarChaos}
    (hPf : Pf.Valid) (n : ℕ) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ uPFyAt q (halfY x) + halfTail x ^ q
        + smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32) ^ q
          * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x)
            + uFarBound Pf n q x
            + ∑ k ∈ Finset.Ico 4 (tenJ x), uWindowBound P q x k)
        + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  obtain ⟨hx0, hL, hΛ, hexpΛ, -, haL⟩ := half_params hx
  obtain ⟨hy2, hyx, hlogy_le, hlogy_ge, hy99, -⟩ := halfY_facts hx
  obtain ⟨hz2, hzy, -⟩ := halfZ_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  set y := halfY x with hydef
  set σ := halfSigma x with hσdef
  have hσ : 0 < σ := by rw [hσdef, halfSigma]; positivity
  have hy2R : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have ha := halfA_ge hx
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hlogy_big : 99 ≤ Real.log y := by linarith
  -- the reduction's hypotheses
  have hσlog : σ * Real.log (x / y) ≤ 1 / 32 := by
    rw [Real.log_div hx0.ne' (by positivity), hσdef, halfSigma]
    rw [div_mul_eq_mul_div, div_le_iff₀ hLpos]
    have : 0 ≤ Real.log y := hlogy.le
    nlinarith
  have hη : 0 < halfEta x := by rw [halfEta]; positivity
  have hyη : 1 + halfEta x < y := by
    have hηle : halfEta x ≤ 1 := by
      rw [halfEta]
      have h1 : (1 : ℝ) ≤ Real.log x ^ 3 := by
        have : (1 : ℝ) ≤ Real.log x := le_trans (by linarith [Real.add_one_le_exp (110 : ℝ)]) hL
        exact one_le_pow₀ this
      exact inv_le_one_of_one_le₀ h1
    have : (100 : ℝ) ≤ Real.exp 99 := by linarith [Real.add_one_le_exp (99 : ℝ)]
    linarith
  have hε : 0 < halfEps x := by rw [halfEps]; positivity
  have hred := integral_rpow_weightedRademacherSum_le_reduction_explicit hX hz2 hzy
    (σ := σ) (x := x) (η := halfEta x) (ε := halfEps x) (c := 1 / 32) (q := q)
    hyx (floor_le_primorial_halfY hx) hσ hσlog hη hyη hε hq0 (by linarith)
  -- (PF) at `y`
  have hPF : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
      (1 / 2) ω‖ ^ (2 * q) ∂μ) ≤ uPFyAt q y :=
    hRa.integral_norm_randomEulerProduct_half_rpow_le_log_sharp (q := q) hq0.le hq hy2
  -- `Z` in three ranges
  have hJ4 : 4 ≤ tenJ x := by
    rw [tenJ, ← hydef]
    have h1 : (3 : ℝ) ≤ Real.log (2 / 3 * Real.log y) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have h2 : Real.exp 3 ≤ 21 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
        have := Real.exp_one_lt_d9
        have h4 : Real.exp 1 ^ 3 ≤ (2.72 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 3
        linarith [show (2.72 : ℝ) ^ 3 ≤ 21 by norm_num]
      linarith
    have : 3 ≤ ⌊Real.log (2 / 3 * Real.log y)⌋₊ := Nat.le_floor (by exact_mod_cast h1)
    omega
  have hJ4R : (4 : ℝ) ≤ ((tenJ x : ℕ) : ℝ) := by exact_mod_cast hJ4
  have hwv : Real.exp (-((tenJ x : ℕ) : ℝ)) ≤ Real.exp (-((4 : ℕ) : ℝ)) :=
    Real.exp_le_exp.2 (by push_cast; linarith)
  -- the central window
  have hb1 : (∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Icc (-Real.exp (-((tenJ x : ℕ) : ℝ)))
        (Real.exp (-((tenJ x : ℕ) : ℝ))),
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
        ≤ uCenAt q σ y (tenJ x) ^ q * uPFcAt q σ y :=
    integral_rpow_centralRange_le_sharp hX (σ := σ) (q := q)
      (w := Real.exp (-((tenJ x : ℕ) : ℝ))) hy2 hσ (Real.exp_pos _) hq0.le hq
  -- the windows
  have hb2 : (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-((tenJ x : ℕ) : ℝ)) < |t|
          ∧ |t| ≤ Real.exp (-((4 : ℕ) : ℝ))},
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ ∑ k ∈ Finset.Ico 4 (tenJ x), uWindowBound P q x k := by
    refine le_trans (integral_rpow_mesoRange_le_sum_windows hX hy2 hσ hq0 (by linarith)
      hJ4) ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk => uWindow_le hX hx hq0.le hq hP hk
  -- the far range
  have hb3 := uFar_le hX hx hq0 hq hPf n
  have hZ := integral_rpow_eulerLineDiv_le_of_three_ranges hX (σ := σ) (q := q)
    (w := Real.exp (-((tenJ x : ℕ) : ℝ))) (v := Real.exp (-((4 : ℕ) : ℝ))) hy2 hσ hq0.le
    (by linarith) hwv hb1 hb2 hb3
  have hCR0 : 0 ≤ smallQReductionConst y (halfZ x) (halfEta x) (halfEps x) (1 / 32) ^ q :=
    Real.rpow_nonneg (smallQReductionConst_pos hz2 hzy hη hε).le _
  have hmul := mul_le_mul_of_nonneg_left hZ hCR0
  have htail : (∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial y)
      | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m}, (m : ℝ)⁻¹) = halfTail x := by
    rw [halfTail, ← hydef]
  rw [htail] at hred
  linarith

set_option maxHeartbeats 1000000 in
-- the reduction, three ranges and five bounds in one proof
/-- **`E|S(x)|^{2q}` from its pieces in the middle range**, every window by Jensen.  For
`x ≥ exp(e⁷)`, with the parameters of `RMF.integral_norm_weightedRademacherSum_le_mid_assembly`:

`E|S(x)|^{2q} ≤ PF_q(y) + T^q + C_R^q·(C_c(q)^q·PF_c(q) + (2·1.195e⁴)^q + ∑_{4≤k<J₀} b_k)
  + E_err^q`,

`b_k = RMF.thetaPF σ (3/2) q k·(RMF.thetaWindowConstQ (3/2) q k y)^q`. -/
theorem integral_rpow_weightedRademacherSum_le_u_mid_assembly {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 7) ≤ x) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ uPFyAt q (midY x) + midTail x ^ q
        + smallQReductionConst (midY x) (midZ x) (halfEta x) (halfEps x) (1 / 32) ^ q
          * (uCenAt q (halfSigma x) (midY x) (midJ x) ^ q * uPFcAt q (halfSigma x) (midY x)
            + (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ q
            + ∑ k ∈ Finset.Ico 4 (midJ x), thetaPF (halfSigma x) (3 / 2) q k
                * thetaWindowConstQ (3 / 2) q k (midY x) ^ q)
        + smallQReductionErr x (midZ x) (halfEta x) (halfEps x) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  obtain ⟨hx0, hL, hΛ, hexpΛ, -, haL⟩ := mid_params hx
  obtain ⟨hy2, hyx, hlogy_le, hlogy_ge, hy99, -⟩ := midY_facts hx
  obtain ⟨hz2, hzy, -⟩ := midZ_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  set y := midY x with hydef
  set σ := halfSigma x with hσdef
  have hσ : 0 < σ := by rw [hσdef, halfSigma]; positivity
  have hy2R : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogy_big : 99 ≤ Real.log y := by
    have h := Real.log_le_log (Real.exp_pos 99) hy99
    rwa [Real.log_exp] at h
  -- the reduction's hypotheses
  have hσlog : σ * Real.log (x / y) ≤ 1 / 32 :=
    halfSigma_mul_log_div_le hx0 hLpos (by linarith) hlogy.le
  have hη : 0 < halfEta x := by rw [halfEta]; positivity
  have hyη : 1 + halfEta x < y := by
    have hηle : halfEta x ≤ 1 := by
      rw [halfEta]
      have h1 : (1 : ℝ) ≤ Real.log x ^ 3 := by
        have : (1 : ℝ) ≤ Real.log x := le_trans (by linarith [Real.add_one_le_exp (7 : ℝ)]) hL
        exact one_le_pow₀ this
      exact inv_le_one_of_one_le₀ h1
    have : (100 : ℝ) ≤ Real.exp 99 := by linarith [Real.add_one_le_exp (99 : ℝ)]
    linarith
  have hε : 0 < halfEps x := by rw [halfEps]; positivity
  have hred := integral_rpow_weightedRademacherSum_le_reduction_explicit hX hz2 hzy
    (σ := σ) (x := x) (η := halfEta x) (ε := halfEps x) (c := 1 / 32) (q := q)
    hyx (floor_le_primorial_midY hx) hσ hσlog hη hyη hε hq0 (by linarith)
  -- (PF) at `y`
  have hPF : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
      (1 / 2) ω‖ ^ (2 * q) ∂μ) ≤ uPFyAt q y :=
    hRa.integral_norm_randomEulerProduct_half_rpow_le_log_sharp (q := q) hq0.le hq hy2
  -- `Z` in three ranges
  have hJ4 : 4 ≤ midJ x := by
    rw [midJ, ← hydef]
    have h1 : (3 : ℝ) ≤ Real.log (2 / 3 * Real.log y) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have h2 : Real.exp 3 ≤ 21 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
        have := Real.exp_one_lt_d9
        have h4 : Real.exp 1 ^ 3 ≤ (2.72 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 3
        linarith [show (2.72 : ℝ) ^ 3 ≤ 21 by norm_num]
      linarith
    have : 3 ≤ ⌊Real.log (2 / 3 * Real.log y)⌋₊ := Nat.le_floor (by exact_mod_cast h1)
    omega
  have hJ4R : (4 : ℝ) ≤ ((midJ x : ℕ) : ℝ) := by exact_mod_cast hJ4
  have hwv : Real.exp (-((midJ x : ℕ) : ℝ)) ≤ Real.exp (-((4 : ℕ) : ℝ)) :=
    Real.exp_le_exp.2 (by push_cast; linarith)
  -- the central window
  have hb1 : (∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Icc (-Real.exp (-((midJ x : ℕ) : ℝ)))
        (Real.exp (-((midJ x : ℕ) : ℝ))),
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
        ≤ uCenAt q σ y (midJ x) ^ q * uPFcAt q σ y :=
    integral_rpow_centralRange_le_sharp hX (σ := σ) (q := q)
      (w := Real.exp (-((midJ x : ℕ) : ℝ))) hy2 hσ (Real.exp_pos _) hq0.le hq
  -- the windows, every one by Jensen
  have hb2 : (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-((midJ x : ℕ) : ℝ)) < |t|
          ∧ |t| ≤ Real.exp (-((4 : ℕ) : ℝ))},
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ ∑ k ∈ Finset.Ico 4 (midJ x), thetaPF σ (3 / 2) q k
          * thetaWindowConstQ (3 / 2) q k y ^ q := by
    refine le_trans (integral_rpow_mesoRange_le_sum_windows hX hy2 hσ hq0 (by linarith)
      hJ4) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    have hky := tenJ_window hlogy (by omega : k ≠ 0) (by rw [midJ, ← hydef] at hk; exact hk.2)
    exact window_theta_le_jensen_q hX (θ := 3 / 2) (by norm_num) hq0.le hq hσ (by omega) hky
  -- the far range
  have hb3 := integral_rpow_eulerProductLine_tail_le_explicit hX (q := q) hq0 (by linarith)
    hy99 hσ (T := Real.exp (-((4 : ℕ) : ℝ))) (Real.exp_pos _)
  have hZ := integral_rpow_eulerLineDiv_le_of_three_ranges hX (σ := σ) (q := q)
    (w := Real.exp (-((midJ x : ℕ) : ℝ))) (v := Real.exp (-((4 : ℕ) : ℝ))) hy2 hσ hq0.le
    (by linarith) hwv hb1 hb2 hb3
  have hCR0 : 0 ≤ smallQReductionConst y (midZ x) (halfEta x) (halfEps x) (1 / 32) ^ q :=
    Real.rpow_nonneg (smallQReductionConst_pos hz2 hzy hη hε).le _
  have hmul := mul_le_mul_of_nonneg_left hZ hCR0
  have htail : (∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial y)
      | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m}, (m : ℝ)⁻¹) = midTail x := by
    rw [midTail, ← hydef]
  rw [htail] at hred
  linarith

end RMF
