/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Properties

/-!
# Second solutions `fe_n`, `ge_n` (DLMF §28.5)

`fe_n(z, q) = mathieuFe n z q` and `ge_n(z, q) = mathieuGe n z q` (real `q`) are defined in
`DLMF.Mathieu.Basic` as the odd solution for `a = a_n(q)` and the even solution for
`a = b_n(q)`, normalized by 28.5.5 with `fe_n'(0, q) > 0`, `ge_n(0, q) > 0` (equivalent to DLMF's
sign rule `C_n f_n → sin nz`, `S_n g_n → cos nz` as `q → 0`), together with the factors
`C_n(q) = mathieuFeC n q`, `S_n(q) = mathieuGeS n q` and the periodic parts
`f_n = mathieuFeF n z q`, `g_n = mathieuGeG n z q`.

**Correction (28.5.6, second relation).** With DLMF's own sign rule for `C_n`, `S_n`, the
relation is `C_{2m+1}(-q) = -S_{2m+1}(q)`, not `C_{2m+1}(-q) = S_{2m+1}(q)`: numerically
(direct integration of 28.2.1) `C_1(-1) = -0.95506…`, `S_1(1) = 0.95506…`,
`C_3(-1) = -0.0051465…`, `S_3(1) = 0.0051465…`; analytically, `ge_{2m+1}(π/2 - z, q)` is an odd
multiple `c fe_{2m+1}(z, -q)` plus a multiple of `ce_{2m+1}(z, -q)` with
`sign c = -sign ge'_{2m+1}(π/2, q) = (-1)^m`, which gives `C_{2m+1}(-q) S_{2m+1}(q) < 0`.

**Remark (`n = 0`).** For `n = 0` the normalization 28.5.5 makes `fe_0'(0, q) ≈ 2/|q|` blow up as
`q → 0` (numerically `fe_0'(0, 0.01) = 201.0…`), so 28.5.5 and `fe_0(z, 0) = z` (28.5.7) are not
connected by continuity; `mathieuFe 0 z 0 = z` by definition.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Mathieu

/-- The Wronskian of two solutions of the same Mathieu equation is constant. -/
theorem IsMathieuSolution.wronskian_eq {a q : ℂ} {u v : ℂ → ℂ} (hu : IsMathieuSolution a q u)
    (hv : IsMathieuSolution a q v) (z w : ℂ) :
    u z * deriv v z - deriv u z * v z = u w * deriv v w - deriv u w * v w := by
  have hW : ∀ z, HasDerivAt (fun z => u z * deriv v z - deriv u z * v z) 0 z := by
    intro z
    have := ((hu.differentiable z).hasDerivAt.mul (hv.hasDerivAt_deriv z)).sub
      ((hu.hasDerivAt_deriv z).mul (hv.differentiable z).hasDerivAt)
    convert this using 1; ring
  exact is_const_of_deriv_eq_zero (fun z => (hW z).differentiableAt) (fun z => (hW z).deriv) z w

/-- **Theorem of Ince** (DLMF §28.5(i)): for `q ≠ 0`, if a nontrivial solution has period `π` or
`2π`, any solution with period `2π` (in particular with period `π`) is a multiple of it. -/
@[dlmf 28.5.i]
theorem mathieu_ince {a q : ℂ} (hq : q ≠ 0) {w v : ℂ → ℂ} (hw : IsMathieuSolution a q w)
    (hw0 : w ≠ 0) (hwp : ∀ z, w (z + 2 * π) = w z) (hv : IsMathieuSolution a q v)
    (hvp : ∀ z, v (z + 2 * π) = v z) : ∃ c : ℂ, v = fun z => c * w z := by
  sorry

/-- **DLMF 28.5.1**: `fe_n(z, q) = C_n(q)(z ce_n(z, q) + f_n(z, q))` whenever `C_n(q) ≠ 0`
(which holds for `q ≠ 0`, `mathieuFeC_ne_zero`, and for `(n, q) = (0, 0)`). -/
@[dlmf 28.5.E1]
theorem mathieuFe_eq {n : ℕ} {q : ℝ} (hC : mathieuFeC n q ≠ 0) (z : ℂ) :
    mathieuFe n z q = mathieuFeC n q * (z * mathieuCe n z q + mathieuFeF n z q) := by
  rw [mathieuFeF]; field_simp; ring

/-- **DLMF 28.5.2**: `ge_n(z, q) = S_n(q)(z se_n(z, q) + g_n(z, q))` whenever `S_n(q) ≠ 0`. -/
@[dlmf 28.5.E2]
theorem mathieuGe_eq {n : ℕ} {q : ℝ} (hS : mathieuGeS n q ≠ 0) (z : ℂ) :
    mathieuGe n z q = mathieuGeS n q * (z * mathieuSe n z q + mathieuGeG n z q) := by
  rw [mathieuGeG]; field_simp; ring

/-- `C_n(q) ≠ 0` for real `q ≠ 0` (a consequence of Ince's theorem, DLMF §28.5(i)). -/
@[dlmf 28.5.i]
theorem mathieuFeC_ne_zero (n : ℕ) {q : ℝ} (hq : q ≠ 0) : mathieuFeC n q ≠ 0 := by
  sorry

/-- `S_n(q) ≠ 0` for real `q ≠ 0` and `n ≥ 1` (Ince's theorem, DLMF §28.5(i)). -/
@[dlmf 28.5.i]
theorem mathieuGeS_ne_zero {n : ℕ} (hn : n ≠ 0) {q : ℝ} (hq : q ≠ 0) : mathieuGeS n q ≠ 0 := by
  sorry

/-- **DLMF 28.5.3**: `f_{2m}(z, q)` is `π`-periodic and odd, `f_{2m+1}(z, q)` is
`π`-antiperiodic and odd (real `q ≠ 0`). -/
@[dlmf 28.5.E3]
theorem mathieuFeF_periodicity (m : ℕ) {q : ℝ} (hq : q ≠ 0) (z : ℂ) :
    mathieuFeF (2 * m) (z + π) q = mathieuFeF (2 * m) z q ∧
      mathieuFeF (2 * m) (-z) q = -mathieuFeF (2 * m) z q ∧
      mathieuFeF (2 * m + 1) (z + π) q = -mathieuFeF (2 * m + 1) z q ∧
      mathieuFeF (2 * m + 1) (-z) q = -mathieuFeF (2 * m + 1) z q := by
  sorry

/-- **DLMF 28.5.4**: `g_{2m+1}(z, q)` is `π`-antiperiodic and even, `g_{2m+2}(z, q)` is
`π`-periodic and even (real `q ≠ 0`). -/
@[dlmf 28.5.E4]
theorem mathieuGeG_periodicity (m : ℕ) {q : ℝ} (hq : q ≠ 0) (z : ℂ) :
    mathieuGeG (2 * m + 1) (z + π) q = -mathieuGeG (2 * m + 1) z q ∧
      mathieuGeG (2 * m + 1) (-z) q = mathieuGeG (2 * m + 1) z q ∧
      mathieuGeG (2 * m + 2) (z + π) q = mathieuGeG (2 * m + 2) z q ∧
      mathieuGeG (2 * m + 2) (-z) q = mathieuGeG (2 * m + 2) z q := by
  sorry

/-- **Uniqueness of `f_n`** (DLMF §28.5(i)): for real `q ≠ 0`, if
`fe_n = c (z ce_n + h)` with `h` odd and `π`-periodic (`n` even) or `π`-antiperiodic (`n` odd),
then `c = C_n(q)` and `h = f_n(·, q)`. -/
@[dlmf 28.5.i]
theorem mathieuFeF_unique {n : ℕ} {q : ℝ} (hq : q ≠ 0) {c : ℂ} {h : ℂ → ℂ}
    (hh : ∀ z, h (z + π) = (-1) ^ n * h z) (hodd : ∀ z, h (-z) = -h z)
    (he : ∀ z, mathieuFe n z q = c * (z * mathieuCe n z q + h z)) :
    c = mathieuFeC n q ∧ h = fun z => mathieuFeF n z q := by
  sorry

/-- **Uniqueness of `g_n`** (DLMF §28.5(i)): for real `q ≠ 0`, `n ≥ 1`, if
`ge_n = c (z se_n + h)` with `h` even and `π`-(anti)periodic like `se_n`, then `c = S_n(q)` and
`h = g_n(·, q)`. -/
@[dlmf 28.5.i]
theorem mathieuGeG_unique {n : ℕ} (hn : n ≠ 0) {q : ℝ} (hq : q ≠ 0) {c : ℂ} {h : ℂ → ℂ}
    (hh : ∀ z, h (z + π) = (-1) ^ n * h z) (heven : ∀ z, h (-z) = h z)
    (he : ∀ z, mathieuGe n z q = c * (z * mathieuSe n z q + h z)) :
    c = mathieuGeS n q ∧ h = fun z => mathieuGeG n z q := by
  sorry

/-- **DLMF 28.5.5**: `C_n(q)² ∫₀^{2π} f_n(x, q)² dx = S_n(q)² ∫₀^{2π} g_n(x, q)² dx = π`
(real `q ≠ 0`, `n ≥ 1` for the second). -/
@[dlmf 28.5.E5]
theorem mathieuFe_mathieuGe_normalization {n : ℕ} {q : ℝ} (hq : q ≠ 0) :
    mathieuFeC n q ^ 2 * ∫ x in (0 : ℝ)..2 * π, mathieuFeF n x q ^ 2 = π ∧
      (n ≠ 0 → mathieuGeS n q ^ 2 * ∫ x in (0 : ℝ)..2 * π, mathieuGeG n x q ^ 2 = π) := by
  sorry

/-- **Limits as `q → 0`** (DLMF §28.5(i)): for `n ≠ 0`, `C_n(q) → 0`, `S_n(q) → 0`,
`C_n(q) f_n(z, q) → sin nz` and `S_n(q) g_n(z, q) → cos nz`. -/
@[dlmf 28.5.i]
theorem mathieuFeC_mathieuGeS_tendsto {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    Tendsto (fun q : ℝ => mathieuFeC n q) (𝓝[≠] 0) (𝓝 0) ∧
      Tendsto (fun q : ℝ => mathieuGeS n q) (𝓝[≠] 0) (𝓝 0) ∧
      Tendsto (fun q : ℝ => mathieuFeC n q * mathieuFeF n z q) (𝓝[≠] 0)
        (𝓝 (Complex.sin (n * z))) ∧
      Tendsto (fun q : ℝ => mathieuGeS n q * mathieuGeG n z q) (𝓝[≠] 0)
        (𝓝 (Complex.cos (n * z))) := by
  sorry

/-- **DLMF 28.5.6** (first relation): `C_{2m}(-q) = C_{2m}(q)`. -/
@[dlmf 28.5.E6]
theorem mathieuFeC_even_neg (m : ℕ) (q : ℝ) : mathieuFeC (2 * m) (-q) = mathieuFeC (2 * m) q := by
  sorry

/-- **DLMF 28.5.6** (second relation, **corrected sign**): `C_{2m+1}(-q) = -S_{2m+1}(q)`
(DLMF prints `C_{2m+1}(-q) = S_{2m+1}(q)`, which contradicts its own sign rule; see the module
docstring). -/
@[dlmf 28.5.E6]
theorem mathieuFeC_odd_neg (m : ℕ) (q : ℝ) :
    mathieuFeC (2 * m + 1) (-q) = -mathieuGeS (2 * m + 1) q := by
  sorry

/-- **DLMF 28.5.6** (third relation): `S_{2m+2}(-q) = S_{2m+2}(q)`. -/
@[dlmf 28.5.E6]
theorem mathieuGeS_even_neg (m : ℕ) (q : ℝ) :
    mathieuGeS (2 * m + 2) (-q) = mathieuGeS (2 * m + 2) q := by
  sorry

/-- **DLMF 28.5.7**: `fe_0(z, 0) = z`. -/
@[dlmf 28.5.E7]
theorem mathieuFe_zero_zero (z : ℂ) : mathieuFe 0 z 0 = z := by
  simp [mathieuFe]

/-- **DLMF 28.5.7**: `fe_n(z, 0) = sin nz`, `n = 1, 2, 3, …`. -/
@[dlmf 28.5.E7]
theorem mathieuFe_q_zero {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    mathieuFe n z 0 = Complex.sin (n * z) := by
  sorry

/-- **DLMF 28.5.7**: `ge_n(z, 0) = cos nz`, `n = 1, 2, 3, …`. -/
@[dlmf 28.5.E7]
theorem mathieuGe_q_zero {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    mathieuGe n z 0 = Complex.cos (n * z) := by
  sorry

/-- **Unboundedness** (DLMF §28.5(i)): for real `q ≠ 0`, every real-axis solution of Mathieu's
equation with `a = a_n(q)` that is not a multiple of `ce_n` is unbounded as `z → +∞` and as
`z → -∞` on `ℝ`; likewise for `a = b_n(q)`, `n ≥ 1`, and `se_n`. -/
@[dlmf 28.5.i]
theorem mathieu_secular_unbounded {n : ℕ} {q : ℝ} (hq : q ≠ 0) {w : ℂ → ℂ}
    (hw : IsMathieuSolution (mathieuA n q) q w)
    (hind : ∀ c : ℂ, w ≠ fun z => c * mathieuCe n z q) :
    ¬ BddAbove (Set.range fun x : Ici (0 : ℝ) => ‖w (x : ℝ)‖) ∧
      ¬ BddAbove (Set.range fun x : Iic (0 : ℝ) => ‖w (x : ℝ)‖) := by
  sorry

/-- **DLMF 28.5.8**: `𝒲{ce_n, fe_n} = ce_n(0, q) fe_n'(0, q)` (real `q`, `(n, q) ≠ (0, 0)`). -/
@[dlmf 28.5.E8]
theorem mathieuCe_mathieuFe_wronskian {n : ℕ} {q : ℝ} (h : ¬ (n = 0 ∧ q = 0)) (z : ℂ) :
    mathieuCe n z q * deriv (fun z => mathieuFe n z q) z -
        deriv (fun z => mathieuCe n z q) z * mathieuFe n z q =
      mathieuCe n 0 q * deriv (fun z => mathieuFe n z q) 0 := by
  rw [(isMathieuSolution_mathieuCe n q).wronskian_eq (isMathieuSolution_mathieuFe h) z 0]
  have h0 : deriv (fun z => mathieuCe n z q) 0 = 0 := by
    simp only [mathieuCe]
    rw [show deriv (fun z => (mathieuCeZero n q : ℂ) * mathieuWI (mathieuA n q) q z) 0 =
        (mathieuCeZero n q : ℂ) * deriv (mathieuWI (mathieuA n q) q) 0 from
      (((isMathieuSolution_mathieuWI _ _).differentiable 0).hasDerivAt.const_mul _).deriv,
      (mathieuWI_spec _ _).2.2, mul_zero]
  rw [h0, zero_mul, sub_zero]

/-- **DLMF 28.5.9**: `𝒲{se_n, ge_n} = -se_n'(0, q) ge_n(0, q)` (real `q`). -/
@[dlmf 28.5.E9]
theorem mathieuSe_mathieuGe_wronskian (n : ℕ) (q : ℝ) (z : ℂ) :
    mathieuSe n z q * deriv (fun z => mathieuGe n z q) z -
        deriv (fun z => mathieuSe n z q) z * mathieuGe n z q =
      -(deriv (fun z => mathieuSe n z q) 0 * mathieuGe n 0 q) := by
  rw [(isMathieuSolution_mathieuSe n q).wronskian_eq (isMathieuSolution_mathieuGe n q) z 0]
  have h0 : mathieuSe n 0 q = 0 := by simp [mathieuSe, (mathieuWII_spec _ _).2.1]
  rw [h0, zero_mul, zero_sub]

end DLMF.Mathieu
