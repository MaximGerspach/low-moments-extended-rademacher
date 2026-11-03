/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import PrimeNumberTheoremAnd.MediumPNT
import PrimeNumberTheoremAnd.IEANTN.SecondaryDefinitions
import RMF.NumberTheory.CosinePrimeSum

/-!
# The prime number theorem with the medium error term, for `θ`

`RS_prime.pnt` is `|θ x − x| ≤ C x / log²x`, and it is *derived from* `MediumPNT` by throwing
away the stronger error: `RS_prime.pntBigO` obtains `(ψ − id) =O(x·e^{−c(log x)^{1/10}})` and
immediately weakens it.  This file keeps it.

The stronger error sets the height range of the block cosine estimate.
`RMF.exists_abs_cos_prime_sum_block_le'` trades `τ ≤ 1` for `τ² ≤ log y₁`, an exponent set by the
PNT error it uses: in the application `log y₁ = e^{m+θ}`, so the condition reads
`D ≳ 2·log(1+|t|)` on the block offset `D`.  With `e^{−c(log x)^{1/10}}` it becomes
`D ≳ 10·log log(1+|t|)`, the shape of Harper's Proposition 6 (Harper, arXiv:1703.06654).

## Main statement

`RMF.theta_sub_id_isBigO_exp` — `(θ − id) =O(x·e^{−c(log x)^{1/10}})` for some `c > 0`.

The `ψ → θ` bridge is `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`: `|ψ x − θ x| ≤ 2√x·log x`,
which is `O(x·e^{−(log x)/3})` and so absorbed, since `log x ≤ 6·x^{1/6}` gives
`2√x·log x ≤ 12·x^{2/3} = 12·x·e^{−(log x)/3}`.
-/

open Filter Asymptotics Real Chebyshev

namespace RMF

/-- `L ^ (1/10) ≤ L` for `L ≥ 1`: the tenth root is at most the whole, which is what lets one
exponential rate be traded for another. -/
lemma rpow_tenth_le_self {L : ℝ} (hL : 1 ≤ L) : L ^ ((1 : ℝ) / 10) ≤ L := by
  calc L ^ ((1 : ℝ) / 10) ≤ L ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    _ = L := Real.rpow_one L

/-- **`2√x·log x` is `O(x·e^{−c(log x)^{1/10}})`** for any `0 < c ≤ 1/3`.

`log x ≤ 6x^{1/6}` gives `2√x log x ≤ 12x^{2/3}`, which is `12·x·e^{−(log x)/3}`; and
`(log x)^{1/10} ≤ log x` past `e`, so `e^{−(log x)/3} ≤ e^{−c(log x)^{1/10}}` when `c ≤ 1/3`. -/
lemma sqrt_mul_log_isBigO_exp {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 3) :
    (fun x : ℝ => 2 * Real.sqrt x * Real.log x) =O[atTop]
      fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) := by
  refine isBigO_iff.2 ⟨12, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by linarith [Real.exp_one_gt_d9]) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) ≤ Real.log x := by linarith
  -- `log x ≤ 6 x^{1/6}`
  have hlog6 : Real.log x ≤ 6 * x ^ ((1 : ℝ) / 6) := by
    calc Real.log x ≤ x ^ ((1 : ℝ) / 6) / (1 / 6) := by
          simpa using Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 6)
      _ = 6 * x ^ ((1 : ℝ) / 6) := by ring
  -- `2√x log x ≤ 12 x^{2/3}`
  have hsqrt : Real.sqrt x = x ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow x
  have hprod : 2 * Real.sqrt x * Real.log x ≤ 12 * x ^ ((2 : ℝ) / 3) := by
    have h1 : (0 : ℝ) ≤ 2 * Real.sqrt x := by positivity
    have h2 := mul_le_mul_of_nonneg_left hlog6 h1
    have hxx : x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 6) = x ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_add hx0]
      norm_num
    calc 2 * Real.sqrt x * Real.log x ≤ 2 * Real.sqrt x * (6 * x ^ ((1 : ℝ) / 6)) := h2
      _ = 12 * (x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 6)) := by rw [hsqrt]; ring
      _ = 12 * x ^ ((2 : ℝ) / 3) := by rw [hxx]
  -- `x^{2/3} = x · e^{-(log x)/3} ≤ x · e^{-c (log x)^{1/10}}`
  have hxe : x ^ ((2 : ℝ) / 3) = x * Real.exp (-(Real.log x / 3)) := by
    rw [Real.rpow_def_of_pos hx0, ← Real.exp_log hx0]
    rw [← Real.exp_add]
    · congr 1
      rw [Real.log_exp]
      ring
  have hexp : Real.exp (-(Real.log x / 3)) ≤ Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) := by
    refine Real.exp_le_exp.2 ?_
    have h1 : Real.log x ^ ((1 : ℝ) / 10) ≤ Real.log x := rpow_tenth_le_self hL1
    have h2 : c * Real.log x ^ ((1 : ℝ) / 10) ≤ (1 / 3) * Real.log x := by
      have h3 : c * Real.log x ^ ((1 : ℝ) / 10) ≤ c * Real.log x :=
        mul_le_mul_of_nonneg_left h1 hc0.le
      nlinarith [Real.rpow_nonneg hL0 ((1 : ℝ) / 10)]
    linarith
  have hfin : 2 * Real.sqrt x * Real.log x
      ≤ 12 * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
    calc 2 * Real.sqrt x * Real.log x ≤ 12 * x ^ ((2 : ℝ) / 3) := hprod
      _ = 12 * (x * Real.exp (-(Real.log x / 3))) := by rw [hxe]
      _ ≤ 12 * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
          have := mul_le_mul_of_nonneg_left hexp hx0.le
          linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt x * Real.log x),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)))]
  linarith

/-- **The prime number theorem for `θ`, with the medium error term kept.**

`RS_prime.pntBigO` obtains this for `ψ` and then weakens `e^{−c(log x)^{1/10}}` to `1/log²x`
before stating `RS_prime.pnt`.  The stronger form is what
`RMF.exists_abs_cos_prime_sum_block_le_wide` needs in order to reach `τ` past `√(log y₁)`. -/
theorem theta_sub_id_isBigO_exp :
    ∃ c > 0, (θ - id) =O[atTop]
      fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c, hc0, hc⟩ := MediumPNT
  refine ⟨min c (1 / 3), lt_min hc0 (by norm_num), ?_⟩
  have hmin0 : (0 : ℝ) < min c (1 / 3) := lt_min hc0 (by norm_num)
  have hmin3 : min c (1 / 3) ≤ 1 / 3 := min_le_right _ _
  have hminc : min c (1 / 3) ≤ c := min_le_left _ _
  -- the `ψ` half, at the smaller rate
  have hψ : (ψ - id) =O[atTop]
      fun x : ℝ => x * Real.exp (-(min c (1 / 3)) * Real.log x ^ ((1 : ℝ) / 10)) := by
    refine hc.trans (isBigO_iff.2 ⟨1, ?_⟩)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hL0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
    have hr0 : (0 : ℝ) ≤ Real.log x ^ ((1 : ℝ) / 10) := Real.rpow_nonneg hL0 _
    have hle : Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))
        ≤ Real.exp (-(min c (1 / 3)) * Real.log x ^ ((1 : ℝ) / 10)) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))),
      abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ x * Real.exp (-(min c (1 / 3)) * Real.log x ^ ((1 : ℝ) / 10)))]
    nlinarith [mul_le_mul_of_nonneg_left hle hx0.le]
  -- the `θ − ψ` half, absorbed
  have hθψ : (θ - ψ) =O[atTop]
      fun x : ℝ => x * Real.exp (-(min c (1 / 3)) * Real.log x ^ ((1 : ℝ) / 10)) := by
    refine IsBigO.trans (isBigO_iff.2 ⟨1, ?_⟩) (sqrt_mul_log_isBigO_exp hmin0 hmin3)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have h := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
    have hL0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
    have hnn : (0 : ℝ) ≤ 2 * Real.sqrt x * Real.log x :=
      mul_nonneg (by positivity) hL0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
    simp only [Pi.sub_apply]
    rw [← neg_sub, abs_neg]
    linarith
  have hsplit : θ - id = (ψ - id) + (θ - ψ) := by ring
  exact hsplit ▸ hψ.add hθψ

/-! ### The explicit form, and the decay the packaging needs -/

/-- `y ^ 10 ≤ 10 ^ 10 · e^y` on `y ≥ 0`, from `e^{y/10} ≥ y/10` raised to the tenth.

This is what makes `L·e^{-aL^{1/10}}` bounded: the tenth root in the exponent is met by the tenth
power on the other side. -/
lemma pow_ten_le_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 10 ≤ 10 ^ 10 * Real.exp y := by
  have h1 : y / 10 ≤ Real.exp (y / 10) := by
    linarith [Real.add_one_le_exp (y / 10)]
  have h2 : (y / 10) ^ 10 ≤ Real.exp (y / 10) ^ 10 :=
    pow_le_pow_left₀ (by linarith) h1 10
  have h3 : Real.exp (y / 10) ^ 10 = Real.exp y := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h3] at h2
  calc y ^ 10 = 10 ^ 10 * (y / 10) ^ 10 := by ring
    _ ≤ 10 ^ 10 * Real.exp y := by linarith

/-- **`L·e^{-aL^{1/10}}` is bounded**, by `(10/a)^{10}`.

This is the fact that lets the block estimate's error terms be absorbed: the surviving power of
`log y₁` is beaten by the exponential in its tenth root. -/
lemma mul_exp_neg_rpow_le {a L : ℝ} (ha : 0 < a) (hL : 1 ≤ L) :
    L * Real.exp (-a * L ^ ((1 : ℝ) / 10)) ≤ (10 / a) ^ 10 := by
  set u : ℝ := L ^ ((1 : ℝ) / 10) with hudef
  have hu0 : (0 : ℝ) < u := Real.rpow_pos_of_pos (by linarith) _
  have huL : u ^ (10 : ℕ) = L := by
    rw [hudef, ← Real.rpow_natCast (L ^ ((1 : ℝ) / 10)) 10, ← Real.rpow_mul (by linarith)]
    norm_num
  have hau : (0 : ℝ) ≤ a * u := by positivity
  have hpow := pow_ten_le_exp hau
  have hexp0 : (0 : ℝ) < Real.exp (-a * u) := Real.exp_pos _
  have hcancel : Real.exp (a * u) * Real.exp (-a * u) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hkey : L * Real.exp (-a * u) ≤ (10 / a) ^ 10 := by
    have h1 : a ^ 10 * L = (a * u) ^ 10 := by rw [← huL]; ring
    have h2 : a ^ 10 * L ≤ 10 ^ 10 * Real.exp (a * u) := by rw [h1]; exact hpow
    have h3 : a ^ 10 * (L * Real.exp (-a * u))
        ≤ 10 ^ 10 * (Real.exp (a * u) * Real.exp (-a * u)) := by
      have := mul_le_mul_of_nonneg_right h2 hexp0.le
      nlinarith
    rw [hcancel, mul_one] at h3
    have ha10 : (0 : ℝ) < a ^ 10 := by positivity
    rw [div_pow]
    rw [le_div_iff₀ ha10]
    nlinarith
  exact hkey

/-- **The prime number theorem for `θ`, in the explicit form the block estimate consumes.**

The `=O` of `RMF.theta_sub_id_isBigO_exp` read past a threshold.  The threshold is harmless: the
blocks this is applied to are `RMF.blockScale`s, which grow doubly exponentially. -/
theorem exists_abs_theta_sub_le_exp :
    ∃ c > 0, ∃ C ≥ 0, ∃ x₀ ≥ 2, ∀ x ≥ x₀,
      |θ x - x| ≤ C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c, hc0, hbig⟩ := theta_sub_id_isBigO_exp
  obtain ⟨C, hC0, hev⟩ := isBigO_iff'.1 hbig
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨c, hc0, C, hC0.le, max N 2, le_max_right _ _, fun x hx => ?_⟩
  have hxN : N ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have h := hN x hxN
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at h
  rwa [abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)))] at h

/-! ### The packaging step, against the exponential error

`RMF.exists_abs_cos_prime_sum_block_le'` reaches `τ² ≤ log y₁`.  This reaches
`τ² ≤ e^{(c/2)(log y₁)^{1/10}}` — exponentially further, and Harper's shape.

Both rest on `RMF.abs_cos_prime_sum_block_le`, whose PNT constant may depend on the block: its
hypothesis is localised to `[y₁, y₂]`.  Taking `C = 9C₀·e^{-c L^{1/10}}·L²` there, `L = log y₁`,
converts the exponential error into the shape that lemma consumes, at the cost of
`log y₂ ≤ 3·log y₁` (the `9` is `3²`) — satisfied by any block of bounded ratio past `e`. -/

set_option maxHeartbeats 800000 in
-- the block estimate is re-packaged against an exponential error; the arithmetic is wide
/-- **The block decorrelation estimate, packaged, past `τ² ≤ log y₁`.**  For `0 < τ` with
`τ² ≤ e^{(c/2)(log y₁)^{1/10}}`, `y₀ ≤ y₁ ≤ y₂` and `log y₂ ≤ 3 log y₁`,
`|∑_{y₁ < p ≤ y₂} cos (τ log p) / p| ≤ K / (τ log y₁)`, with `K`, `c`, `y₀` absolute.  In the
application `log y₁ = e^{m+θ}`, so the condition reads `2 log τ ≤ (c/2)e^{(m+θ)/10}`, i.e.
`D ≳ 10·log log(1+|t|)`, the `log log` branch of Harper's Proposition 6. -/
theorem exists_abs_cos_prime_sum_block_le_wide :
    ∃ K c y₀ : ℝ, 0 < K ∧ 0 < c ∧ 2 ≤ y₀ ∧
      ∀ τ : ℝ, 0 < τ → ∀ y₁ y₂ : ℝ, y₀ ≤ y₁ → y₁ ≤ y₂ →
        Real.log y₂ ≤ 3 * Real.log y₁ →
        τ ^ 2 ≤ Real.exp (c / 2 * Real.log y₁ ^ ((1 : ℝ) / 10)) →
        |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p|
          ≤ K / (τ * Real.log y₁) := by
  obtain ⟨c, hc0, C₀, hC₀, x₀, hx₀2, hE⟩ := exists_abs_theta_sub_le_exp
  refine ⟨3 + 36 * C₀ + 9 / 2 * C₀ * (4 * (20 / c) ^ 10 + 3 * (10 / c) ^ 10), c,
    max x₀ (Real.exp 1), by positivity, hc0, le_trans hx₀2 (le_max_left _ _), ?_⟩
  intro τ hτ y₁ y₂ hy₁ hy hlog2 hτ2
  have hy₁x₀ : x₀ ≤ y₁ := le_trans (le_max_left _ _) hy₁
  have hy₁e : Real.exp 1 ≤ y₁ := le_trans (le_max_right _ _) hy₁
  have hy₁2 : (2 : ℝ) ≤ y₁ := le_trans hx₀2 hy₁x₀
  set L : ℝ := Real.log y₁ with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    have h := Real.log_le_log (Real.exp_pos 1) hy₁e
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) < L := by linarith
  have hr0 : (0 : ℝ) ≤ L ^ ((1 : ℝ) / 10) := Real.rpow_nonneg hL0.le _
  set E : ℝ := Real.exp (-c * L ^ ((1 : ℝ) / 10)) with hEdef
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  set Cy : ℝ := 9 * C₀ * E * L ^ 2 with hCydef
  have hCy0 : (0 : ℝ) ≤ Cy := by positivity
  -- the exponential error, in the shape the block estimate consumes
  have hEy : ∀ t : ℝ, y₁ ≤ t → t ≤ y₂ →
      |Chebyshev.theta t - t| ≤ Cy * t / Real.log t ^ 2 := by
    intro s hs1 hs2
    have hs0 : (0 : ℝ) < s := by linarith
    have hLs : L ≤ Real.log s := Real.log_le_log (by linarith) hs1
    have hLs0 : (0 : ℝ) < Real.log s := by linarith
    have hLs2 : Real.log s ≤ 3 * L := le_trans (Real.log_le_log (by linarith) hs2) hlog2
    have h1 := hE s (le_trans hy₁x₀ hs1)
    have h2 : Real.exp (-c * Real.log s ^ ((1 : ℝ) / 10)) ≤ E := by
      refine Real.exp_le_exp.2 ?_
      have h3 : L ^ ((1 : ℝ) / 10) ≤ Real.log s ^ ((1 : ℝ) / 10) :=
        Real.rpow_le_rpow hL0.le hLs (by norm_num)
      nlinarith
    have h4 : |Chebyshev.theta s - s| ≤ C₀ * s * E := by
      have h5 : C₀ * (s * Real.exp (-c * Real.log s ^ ((1 : ℝ) / 10))) ≤ C₀ * (s * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hs0.le) hC₀
      nlinarith
    have h6 : C₀ * s * E ≤ Cy * s / Real.log s ^ 2 := by
      rw [hCydef, le_div_iff₀ (by positivity)]
      have h7 : Real.log s ^ 2 ≤ 9 * L ^ 2 := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg hC₀ hs0.le) hE0.le]
    linarith
  refine (abs_cos_prime_sum_block_le hτ hCy0 hEy hy₁2 hy).trans ?_
  -- the arithmetic: multiply through by `τ L`
  set S : ℝ := Real.exp (c / 2 * L ^ ((1 : ℝ) / 10)) with hSdef
  have hS0 : (0 : ℝ) < S := Real.exp_pos _
  have hES : E * S = Real.exp (-(c / 2) * L ^ ((1 : ℝ) / 10)) := by
    rw [hEdef, hSdef, ← Real.exp_add]
    congr 1
    ring
  have hEL : L * E ≤ (10 / c) ^ 10 := mul_exp_neg_rpow_le hc0 hL1
  have hELS : L * (E * S) ≤ (20 / c) ^ 10 := by
    rw [hES]
    have h := mul_exp_neg_rpow_le (by linarith : (0 : ℝ) < c / 2) hL1
    calc L * Real.exp (-(c / 2) * L ^ ((1 : ℝ) / 10)) ≤ (10 / (c / 2)) ^ 10 := h
      _ = (20 / c) ^ 10 := by rw [show (10 : ℝ) / (c / 2) = 20 / c by field_simp; norm_num]
  have hτS : τ ≤ 1 + S := by nlinarith [sq_nonneg (τ - 1)]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < τ * L), add_mul, add_mul]
  have e1 : 3 / (τ * L) * (τ * L) = 3 := by field_simp
  have e2 : 2 * Cy / L ^ 3 * (τ * L) = 18 * C₀ * (E * τ) := by
    rw [hCydef]
    field_simp
    ring
  have e3 : Cy * (|τ| + 3) / (2 * L ^ 2) * (τ * L)
      = 9 / 2 * C₀ * (E * L * (τ ^ 2 + 3 * τ)) := by
    rw [abs_of_pos hτ, hCydef]
    field_simp
  rw [e1, e2, e3]
  have hbound1 : 18 * C₀ * (E * τ) ≤ 36 * C₀ := by
    have h1 : E * τ ≤ E * (1 + S) := mul_le_mul_of_nonneg_left hτS hE0.le
    have h2 : E * (1 + S) = E + E * S := by ring
    have h3 : E * S ≤ 1 := by
      rw [hES]
      exact Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith
  have hbound2 : 9 / 2 * C₀ * (E * L * (τ ^ 2 + 3 * τ))
      ≤ 9 / 2 * C₀ * (4 * (20 / c) ^ 10 + 3 * (10 / c) ^ 10) := by
    have h1 : τ ^ 2 + 3 * τ ≤ 4 * S + 3 := by nlinarith
    have h2 : E * L * (τ ^ 2 + 3 * τ) ≤ E * L * (4 * S + 3) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : E * L * (4 * S + 3) = 4 * (L * (E * S)) + 3 * (L * E) := by ring
    nlinarith
  linarith

end RMF
