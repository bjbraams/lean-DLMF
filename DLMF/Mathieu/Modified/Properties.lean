/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.BesselSeries
public import DLMF.Mathieu.Noninteger.Properties

/-!
# Modified Mathieu functions: basic properties (DLMF §28.20)

* 28.20.1–28.20.2: the modified Mathieu equation, obtained from 28.2.1 by `z ↦ iz` (proved),
  and its algebraic form.
* 28.20.3–28.20.7: `Ce_ν`, `Se_ν`, `Me_ν`, `Fe_n`, `Ge_n` solve the modified equation (proved
  for integer order from DLMF.Mathieu.Basic; for `Me_ν` from ACQ28B's Floquet theorem).
* §28.20(iii): `M^{(j)}_ν` solve 28.20.1 and have the asymptotics 28.20.9–28.20.12, which
  characterize them; 28.20.13–28.20.14 (proved from the convergence theorem 28.24.1).
* 28.20.21 Wronskians, 28.20.22–28.20.25 shifts of the variable; the shift `z ↦ z + sπi` of
  `M^{(1)}_ν` is proved directly from the cross-product series.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-! ### §28.20(i) The modified Mathieu equation -/

/-- If `w` solves Mathieu's equation 28.2.1 then `z ↦ w(cz)` with `c² = -1` (`c = ±i`) solves
the modified Mathieu equation 28.20.1 (DLMF §28.20(i): "when `z` is replaced by `±iz`"). -/
@[dlmf 28.20.E1]
theorem IsMathieuSolution.isModMathieuSolution_comp {a q : ℂ} {w : ℂ → ℂ}
    (hw : IsMathieuSolution a q w) {c : ℂ} (hc : c ^ 2 = -1) :
    IsModMathieuSolution a q (fun z => w (c * z)) := by
  have hd : ∀ z, HasDerivAt (fun z => w (c * z)) (deriv w (c * z) * c) z := fun z => by
    have := ((hw.differentiable (c * z)).hasDerivAt).comp z ((hasDerivAt_id z).const_mul c)
    convert this using 1 <;> first | rfl | simp
  refine ⟨fun z => (hd z).differentiableAt, fun z => ?_⟩
  have he : deriv (fun z => w (c * z)) = fun z => deriv w (c * z) * c :=
    funext fun z => (hd z).deriv
  rw [he]
  have h2 := ((hw.hasDerivAt_deriv (c * z)).comp z ((hasDerivAt_id z).const_mul c)).mul_const c
  have hc' : c = I ∨ c = -I := by
    have : (c - I) * (c + I) = 0 := by ring_nf; rw [hc, I_sq]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hcos : Complex.cos (2 * (c * z)) = Complex.cosh (2 * z) := by
    rcases hc' with rfl | rfl
    · rw [show 2 * (I * z) = (2 * z) * I by ring, Complex.cos_mul_I]
    · rw [show 2 * (-I * z) = -((2 * z) * I) by ring, Complex.cos_neg, Complex.cos_mul_I]
  convert h2 using 1
  · rfl
  rw [hcos]
  linear_combination (-(2 * q * Complex.cosh (2 * z) - a) * w (c * z)) * hc

/-- The **algebraic form** of the modified Mathieu equation (DLMF 28.20.2): if `W` is twice
differentiable and satisfies `(ζ² - 1) W'' + ζ W' + (4qζ² - 2q - a) W = 0` on `ℂ`, then
`w(z) = W(cosh z)` solves 28.20.1. -/
@[dlmf 28.20.E2]
theorem isModMathieuSolution_comp_cosh {a q : ℂ} {W : ℂ → ℂ} (hW : Differentiable ℂ W)
    (hW' : Differentiable ℂ (deriv W))
    (hode : ∀ ζ, (ζ ^ 2 - 1) * deriv (deriv W) ζ + ζ * deriv W ζ +
      (4 * q * ζ ^ 2 - 2 * q - a) * W ζ = 0) :
    IsModMathieuSolution a q (fun z => W (Complex.cosh z)) := by
  sorry

/-! ### §28.20(ii) `Ce_ν`, `Se_ν`, `Me_ν`, `Fe_n`, `Ge_n` -/

/-- `Ce_n(z, q) = ce_n(iz, q)` for `n ∈ ℕ` and real `q` (DLMF 28.20.3). -/
@[dlmf 28.20.E3]
theorem modMathieuCe_natCast (n : ℕ) (z : ℂ) (q : ℝ) :
    modMathieuCe n z q = mathieuCe n (I * z) q := by
  have h : ∃ k : ℕ, (k : ℂ) = n := ⟨n, rfl⟩
  have hk : h.choose = n := by exact_mod_cast h.choose_spec
  rw [modMathieuCe, dite_eq_left_of_eq_true (eq_true h), hk]
  simp

/-- `Se_n(z, q) = -i se_n(iz, q)` for `n ≥ 1` and real `q` (DLMF 28.20.4). -/
@[dlmf 28.20.E4]
theorem modMathieuSe_natCast {n : ℕ} (hn : n ≠ 0) (z : ℂ) (q : ℝ) :
    modMathieuSe n z q = -I * mathieuSe n (I * z) q := by
  have h : ∃ k : ℕ, k ≠ 0 ∧ (k : ℂ) = n := ⟨n, hn, rfl⟩
  have hk : h.choose = n := by exact_mod_cast h.choose_spec.2
  rw [modMathieuSe, dite_eq_left_of_eq_true (eq_true h), hk]
  simp

/-- `Ce_n(·, q)` solves the modified Mathieu equation with `a = a_n(q)` (DLMF 28.20.3). -/
@[dlmf 28.20.E3]
theorem isModMathieuSolution_modMathieuCe (n : ℕ) (q : ℝ) :
    IsModMathieuSolution (mathieuA n q) q (fun z => modMathieuCe n z q) := by
  simp only [modMathieuCe_natCast]
  exact (isMathieuSolution_mathieuCe n q).isModMathieuSolution_comp (by simp)

/-- `Se_n(·, q)` solves the modified Mathieu equation with `a = b_n(q)`, `n ≥ 1`
(DLMF 28.20.4). -/
@[dlmf 28.20.E4]
theorem isModMathieuSolution_modMathieuSe {n : ℕ} (hn : n ≠ 0) (q : ℝ) :
    IsModMathieuSolution (mathieuB n q) q (fun z => modMathieuSe n z q) := by
  simp only [modMathieuSe_natCast hn]
  have h := (isMathieuSolution_mathieuSe n q).isModMathieuSolution_comp (c := I) (by simp)
  refine ⟨fun z => ((h.differentiable z).const_mul (-I)), fun z => ?_⟩
  have he : deriv (fun z => -I * mathieuSe n (I * z) q) =
      fun z => -I * deriv (fun z => mathieuSe n (I * z) q) z :=
    funext fun z => deriv_const_mul _ (h.differentiable z)
  rw [he]
  convert (h.hasDerivAt_deriv z).const_mul (-I) using 1
  ring

/-- `Me_ν(·, q)` solves the modified Mathieu equation with `a = λ_ν(q)` (DLMF 28.20.5),
`ν ∉ ℤ`, `q` normal along `[0, q]`. -/
@[dlmf 28.20.E5]
theorem isModMathieuSolution_modMathieuMe {ν q : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν)
    (hq : MathieuNormalSegment ν q) :
    IsModMathieuSolution (mathieuLambda ν q) q (fun z => modMathieuMe ν z q) :=
  (isFloquetSolution_mathieuMe hν hq).1.1.isModMathieuSolution_comp (by simp)

/-- `Fe_n(·, q)` solves the modified Mathieu equation with `a = a_n(q)` (DLMF 28.20.6),
`(n, q) ≠ (0, 0)`. -/
@[dlmf 28.20.E6]
theorem isModMathieuSolution_modMathieuFe {n : ℕ} {q : ℝ} (hnq : ¬ (n = 0 ∧ q = 0)) :
    IsModMathieuSolution (mathieuA n q) q (fun z => modMathieuFe n z q) := by
  have h := (isMathieuSolution_mathieuFe hnq).isModMathieuSolution_comp (c := I) (by simp)
  refine ⟨fun z => ((h.differentiable z).const_mul (-I)), fun z => ?_⟩
  have he : deriv (fun z => modMathieuFe n z q) =
      fun z => -I * deriv (fun z => mathieuFe n (I * z) q) z :=
    funext fun z => deriv_const_mul _ (h.differentiable z)
  rw [he]
  convert (h.hasDerivAt_deriv z).const_mul (-I) using 1
  simp only [modMathieuFe]
  ring

/-- `Ge_n(·, q)` solves the modified Mathieu equation with `a = b_n(q)` (DLMF 28.20.7). -/
@[dlmf 28.20.E7]
theorem isModMathieuSolution_modMathieuGe (n : ℕ) (q : ℝ) :
    IsModMathieuSolution (mathieuB n q) q (fun z => modMathieuGe n z q) :=
  (isMathieuSolution_mathieuGe n q).isModMathieuSolution_comp (by simp)

/-! ### §28.20(iii) The solutions `M^{(j)}_ν` -/

/-- `M^{(j)}_ν(·, h)` solves the modified Mathieu equation 28.20.1 with `q = h²`,
`a = λ_ν(h²)` (DLMF §28.20(iii)), `j = 1, 2, 3, 4`, `h ≠ 0`, admissible `(ν, h)`. -/
@[dlmf 28.20.iii]
theorem isModMathieuSolution_modMathieuM (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν h : ℂ}
    (hν : ModMathieuAdmissible ν h) (hh : h ≠ 0) :
    IsModMathieuSolution (mathieuLambda ν (h ^ 2)) (h ^ 2) (fun z => modMathieuM j ν z h) := by
  sorry

/-- **Asymptotics of `M^{(3)}_ν`** (DLMF 28.20.9): for real `ν`, `h > 0` and `δ > 0`,
`M^{(3)}_ν(z, h) = H^{(1)}_ν(2h cosh z)(1 + O(sech z))` as `Re z → +∞` with
`-π + δ ≤ Im z ≤ 2π - δ` (`H^{(1)}_ν(2h cosh z)` continued in `z`: `mathieuCylCosh 3`).
The parameter is `h = √q > 0` (DLMF 28.20.8). -/
@[dlmf 28.20.E9, dlmf 28.20.E8]
theorem modMathieuM_three_isBigO {ν h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    (fun z => modMathieuM 3 ν z h - mathieuCylCosh 3 ν h z) =O[m28c_strip (-π + δ) (2 * π - δ)]
      (fun z => mathieuCylCosh 3 ν h z * (Complex.cosh z)⁻¹) := by
  sorry

/-- **Asymptotics of `M^{(4)}_ν`** (DLMF 28.20.10): `M^{(4)}_ν(z, h) =
H^{(2)}_ν(2h cosh z)(1 + O(sech z))` as `Re z → +∞` with `-2π + δ ≤ Im z ≤ π - δ`. -/
@[dlmf 28.20.E10]
theorem modMathieuM_four_isBigO {ν h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    (fun z => modMathieuM 4 ν z h - mathieuCylCosh 4 ν h z) =O[m28c_strip (-2 * π + δ) (π - δ)]
      (fun z => mathieuCylCosh 4 ν h z * (Complex.cosh z)⁻¹) := by
  sorry

/-- **Asymptotics of `M^{(1)}_ν`** (DLMF 28.20.11): `M^{(1)}_ν(z, h) = J_ν(2h cosh z) +
e^{|Im(2h cosh z)|} O((sech z)^{3/2})` as `Re z → +∞` with `|Im z| ≤ π - δ`. -/
@[dlmf 28.20.E11]
theorem modMathieuM_one_isBigO {ν h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    (fun z => modMathieuM 1 ν z h - mathieuCylCosh 1 ν h z) =O[m28c_strip (-π + δ) (π - δ)]
      (fun z => Real.exp |(2 * h * Complex.cosh z).im| *
        ‖(Complex.cosh z)⁻¹‖ ^ (3 / 2 : ℝ)) := by
  sorry

/-- **Asymptotics of `M^{(2)}_ν`** (DLMF 28.20.12): `M^{(2)}_ν(z, h) = Y_ν(2h cosh z) +
e^{|Im(2h cosh z)|} O((sech z)^{3/2})` as `Re z → +∞` with `|Im z| ≤ π - δ`. -/
@[dlmf 28.20.E12]
theorem modMathieuM_two_isBigO {ν h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    (fun z => modMathieuM 2 ν z h - mathieuCylCosh 2 ν h z) =O[m28c_strip (-π + δ) (π - δ)]
      (fun z => Real.exp |(2 * h * Complex.cosh z).im| *
        ‖(Complex.cosh z)⁻¹‖ ^ (3 / 2 : ℝ)) := by
  sorry

/-- **Uniqueness** in §28.20(iii): for real `ν`, `h > 0`, `δ > 0`, a solution of 28.20.1 with
`a = λ_ν(h²)` and the asymptotics 28.20.9 is `M^{(3)}_ν(·, h)` (DLMF: "independent and unique
solutions"); similarly for `M^{(4)}_ν` with 28.20.10. -/
@[dlmf 28.20.iii]
theorem eq_modMathieuM_three_of_isBigO {ν h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) {w : ℂ → ℂ}
    (hw : IsModMathieuSolution (mathieuLambda ν ((h : ℂ) ^ 2)) ((h : ℂ) ^ 2) w)
    (has : (fun z => w z - mathieuCylCosh 3 ν h z) =O[m28c_strip (-π + δ) (2 * π - δ)]
      (fun z => mathieuCylCosh 3 ν h z * (Complex.cosh z)⁻¹)) :
    w = fun z => modMathieuM 3 ν z h := by
  sorry

/-- **Uniqueness** of `M^{(4)}_ν` from 28.20.10 (DLMF §28.20(iii)). -/
@[dlmf 28.20.iii]
theorem eq_modMathieuM_four_of_isBigO {ν h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) {w : ℂ → ℂ}
    (hw : IsModMathieuSolution (mathieuLambda ν ((h : ℂ) ^ 2)) ((h : ℂ) ^ 2) w)
    (has : (fun z => w z - mathieuCylCosh 4 ν h z) =O[m28c_strip (-2 * π + δ) (π - δ)]
      (fun z => mathieuCylCosh 4 ν h z * (Complex.cosh z)⁻¹)) :
    w = fun z => modMathieuM 4 ν z h := by
  sorry

/-- `M^{(1)}_ν` and `M^{(2)}_ν` are **real on the real axis** for real `ν` and `h > 0`
(DLMF §28.20(iii)). -/
@[dlmf 28.20.iii]
theorem modMathieuM_one_two_real {ν h : ℝ} (hh : 0 < h) (x : ℝ) :
    (modMathieuM 1 ν x h).im = 0 ∧ (modMathieuM 2 ν x h).im = 0 := by
  sorry

/-- Pointwise, the third cross-product term is the first plus `i` times the second. -/
theorem modMathieuTerm_three (ν z h : ℂ) (n ℓ : ℤ) :
    modMathieuTerm 3 ν z h n ℓ = modMathieuTerm 1 ν z h n ℓ + I * modMathieuTerm 2 ν z h n ℓ := by
  simp only [modMathieuTerm, mathieuCylExp]
  ring

/-- Pointwise, the fourth cross-product term is the first minus `i` times the second. -/
theorem modMathieuTerm_four (ν z h : ℂ) (n ℓ : ℤ) :
    modMathieuTerm 4 ν z h n ℓ = modMathieuTerm 1 ν z h n ℓ - I * modMathieuTerm 2 ν z h n ℓ := by
  simp only [modMathieuTerm, mathieuCylExp]
  ring

/-- `M^{(3)}_ν = M^{(1)}_ν + i M^{(2)}_ν` (DLMF 28.20.13), `h ≠ 0`, admissible `(ν, h)`. -/
@[dlmf 28.20.E13]
theorem modMathieuM_three {ν h : ℂ} (hν : ModMathieuAdmissible ν h) (hh : h ≠ 0) (z : ℂ) :
    modMathieuM 3 ν z h = modMathieuM 1 ν z h + I * modMathieuM 2 ν z h := by
  have h1 := summable_modMathieuTerm 1 le_rfl (by norm_num) hν hh (modMathieuIndex ν h) z
  have h2 := summable_modMathieuTerm 2 (by norm_num) (by norm_num) hν hh (modMathieuIndex ν h) z
  simp only [modMathieuM, modMathieuTerm_three]
  rw [h1.tsum_add (h2.mul_left I), tsum_mul_left]
  ring

/-- `M^{(4)}_ν = M^{(1)}_ν - i M^{(2)}_ν` (DLMF 28.20.14), `h ≠ 0`, admissible `(ν, h)`. -/
@[dlmf 28.20.E14]
theorem modMathieuM_four {ν h : ℂ} (hν : ModMathieuAdmissible ν h) (hh : h ≠ 0) (z : ℂ) :
    modMathieuM 4 ν z h = modMathieuM 1 ν z h - I * modMathieuM 2 ν z h := by
  have h1 := summable_modMathieuTerm 1 le_rfl (by norm_num) hν hh (modMathieuIndex ν h) z
  have h2 := summable_modMathieuTerm 2 (by norm_num) (by norm_num) hν hh (modMathieuIndex ν h) z
  simp only [modMathieuM, modMathieuTerm_four]
  rw [h1.tsum_sub (h2.mul_left I), tsum_mul_left]
  ring

/-! ### §28.20(vi) Wronskians -/

/-- **Wronskians** (DLMF 28.20.21, first line), real `ν`, `h > 0`, all `z`:
`𝒲{M^{(1)}_ν, M^{(2)}_ν} = -𝒲{M^{(2)}_ν, M^{(3)}_ν} = -𝒲{M^{(2)}_ν, M^{(4)}_ν} = 2/π`. -/
@[dlmf 28.20.E21]
theorem modMathieuM_wronskian_two {ν h : ℝ} (hh : 0 < h) (z : ℂ) :
    m28c_wronskian (fun z => modMathieuM 1 ν z h) (fun z => modMathieuM 2 ν z h) z = 2 / π ∧
      m28c_wronskian (fun z => modMathieuM 2 ν z h) (fun z => modMathieuM 3 ν z h) z =
        -(2 / π) ∧
      m28c_wronskian (fun z => modMathieuM 2 ν z h) (fun z => modMathieuM 4 ν z h) z =
        -(2 / π) := by
  sorry

/-- **Wronskians** (DLMF 28.20.21, second line), real `ν`, `h > 0`, all `z`:
`𝒲{M^{(1)}_ν, M^{(3)}_ν} = -𝒲{M^{(1)}_ν, M^{(4)}_ν} = -½ 𝒲{M^{(3)}_ν, M^{(4)}_ν} = 2i/π`. -/
@[dlmf 28.20.E21]
theorem modMathieuM_wronskian_three {ν h : ℝ} (hh : 0 < h) (z : ℂ) :
    m28c_wronskian (fun z => modMathieuM 1 ν z h) (fun z => modMathieuM 3 ν z h) z =
        2 * I / π ∧
      m28c_wronskian (fun z => modMathieuM 1 ν z h) (fun z => modMathieuM 4 ν z h) z =
        -(2 * I / π) ∧
      m28c_wronskian (fun z => modMathieuM 3 ν z h) (fun z => modMathieuM 4 ν z h) z =
        -2 * (2 * I / π) := by
  sorry

/-! ### §28.20(vii) Shift of variable -/

/-- **Shift by `±πi/2`** (DLMF 28.20.22), `ν` real, `ν ∉ ℤ`, `h > 0`, `σ = ±1`,
`j = 1, 2, 3, 4`: `M^{(j)}_ν(z ± πi/2, h) = M^{(j)}_ν(z, ±ih)`. -/
@[dlmf 28.20.E22]
theorem modMathieuM_add_pi_div_two (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν : ℝ}
    (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ} (hh : 0 < h) {σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (z : ℂ) :
    modMathieuM j ν (z + σ * π * I / 2) h = modMathieuM j ν z (σ * I * h) := by
  sorry

/-- **Shift by `±πi/2`** for integer order (DLMF 28.20.23), `n = 0, 1, …`, `h > 0`, `σ = ±1`:
`Mc^{(j)}_{2n}(z ± πi/2, h) = Mc^{(j)}_{2n}(z, ±ih)` and
`Ms^{(j)}_{2n+1}(z ± πi/2, h) = Mc^{(j)}_{2n+1}(z, ±ih)`. -/
@[dlmf 28.20.E23]
theorem radialMathieu_add_pi_div_two_even (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (n : ℕ)
    {h : ℝ} (hh : 0 < h) {σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (z : ℂ) :
    radialMathieuMc j (2 * n) (z + σ * π * I / 2) h = radialMathieuMc j (2 * n) z (σ * I * h) ∧
      radialMathieuMs j (2 * n + 1) (z + σ * π * I / 2) h =
        radialMathieuMc j (2 * n + 1) z (σ * I * h) := by
  sorry

/-- **Shift by `±πi/2`** for integer order (DLMF 28.20.24), `n = 0, 1, …`, `h > 0`, `σ = ±1`:
`Mc^{(j)}_{2n+1}(z ± πi/2, h) = Ms^{(j)}_{2n+1}(z, ±ih)` and
`Ms^{(j)}_{2n+2}(z ± πi/2, h) = Ms^{(j)}_{2n+2}(z, ±ih)`. -/
@[dlmf 28.20.E24]
theorem radialMathieu_add_pi_div_two_odd (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (n : ℕ)
    {h : ℝ} (hh : 0 < h) {σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (z : ℂ) :
    radialMathieuMc j (2 * n + 1) (z + σ * π * I / 2) h =
        radialMathieuMs j (2 * n + 1) z (σ * I * h) ∧
      radialMathieuMs j (2 * n + 2) (z + σ * π * I / 2) h =
        radialMathieuMs j (2 * n + 2) z (σ * I * h) := by
  sorry

/-- Shifting `z` by `c` with `e^{2c} = 1` multiplies `J_μ(h e^z)` (continued) by `e^{μc}`. -/
theorem m28c_besselJExp_add (μ h z c : ℂ) (hc : Complex.exp (2 * c) = 1) :
    besselJExp μ h (z + c) = Complex.exp (μ * c) * besselJExp μ h z := by
  have e : (h * Complex.exp (z + c)) ^ 2 = (h * Complex.exp z) ^ 2 := by
    rw [Complex.exp_add, mul_pow, mul_pow, mul_pow, ← Complex.exp_nat_mul c 2]
    push_cast; rw [hc]; ring
  rw [besselJExp, besselJExp, e, mul_add, Complex.exp_add]; ring

/-- `e^{2sπi} = 1` for `s ∈ ℤ`. -/
theorem m28c_exp_two_int_pi_I (s : ℤ) : Complex.exp (2 * (s * π * I)) = 1 := by
  rw [Complex.exp_eq_one_iff]; exact ⟨s, by ring⟩

/-- **Shift by `sπi`** of `M^{(1)}_ν` (DLMF 28.20.25, first line), every `ν`, `h`, `z` and
`s ∈ ℤ`: `M^{(1)}_ν(z + sπi, h) = e^{isπν} M^{(1)}_ν(z, h)`. -/
@[dlmf 28.20.E25]
theorem modMathieuM_one_add_int_mul_pi_I (ν z h : ℂ) (s : ℤ) :
    modMathieuM 1 ν (z + s * π * I) h = Complex.exp (I * s * π * ν) * modMathieuM 1 ν z h := by
  set n := modMathieuIndex ν h
  have key : ∀ ℓ : ℤ, modMathieuTerm 1 ν (z + s * π * I) h n ℓ =
      Complex.exp (I * s * π * ν) * modMathieuTerm 1 ν z h n ℓ := by
    intro ℓ
    have h1 := m28c_besselJExp_add ((ℓ - n : ℤ) : ℂ) h (-z) (-(s * π * I))
      (by rw [show 2 * -((s : ℂ) * π * I) = 2 * (((-s : ℤ) : ℂ) * π * I) by push_cast; ring]
          exact m28c_exp_two_int_pi_I _)
    have h2 := m28c_besselJExp_add (ν + n + ℓ) h z (s * π * I) (m28c_exp_two_int_pi_I s)
    simp only [modMathieuTerm, mathieuCylExp]
    rw [show -(z + s * π * I) = -z + -(s * π * I) by ring, h1, h2]
    have e : Complex.exp (((ℓ - n : ℤ) : ℂ) * -(s * π * I)) *
        Complex.exp ((ν + n + ℓ) * (s * π * I)) = Complex.exp (I * s * π * ν) := by
      rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
      exact ⟨s * n, by push_cast; ring⟩
    linear_combination (-1 : ℂ) ^ ℓ * mathieuMeCoeff ν (h ^ 2) ℓ *
      besselJExp ((ℓ - n : ℤ) : ℂ) h (-z) *
      besselJExp (ν + n + ℓ) h z * e
  rw [modMathieuM, modMathieuM, tsum_congr key, tsum_mul_left]; ring

/-- **Shift by `sπi`** of `M^{(2)}_ν` (DLMF 28.20.25, second line), `ν ∉ ℤ` real, `h > 0`:
`M^{(2)}_ν(z + sπi) = e^{-isπν} M^{(2)}_ν(z) + 2i cot(πν) sin(sπν) M^{(1)}_ν(z)`. -/
@[dlmf 28.20.E25]
theorem modMathieuM_two_add_int_mul_pi_I {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ}
    (hh : 0 < h) (z : ℂ) (s : ℤ) :
    modMathieuM 2 ν (z + s * π * I) h = Complex.exp (-(I * s * π * ν)) * modMathieuM 2 ν z h +
      2 * I * Complex.cot (π * ν) * Complex.sin (s * π * ν) * modMathieuM 1 ν z h := by
  sorry

/-- **Shift by `sπi`** of `M^{(3)}_ν` (DLMF 28.20.25, third line), `ν ∉ ℤ` real, `h > 0`:
`M^{(3)}_ν(z + sπi) = -(sin((s-1)πν)/sin(πν)) M^{(3)}_ν(z) - e^{-iπν}(sin(sπν)/sin(πν))
M^{(4)}_ν(z)`. -/
@[dlmf 28.20.E25]
theorem modMathieuM_three_add_int_mul_pi_I {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ}
    (hh : 0 < h) (z : ℂ) (s : ℤ) :
    modMathieuM 3 ν (z + s * π * I) h =
      -(Complex.sin ((s - 1) * π * ν) / Complex.sin (π * ν)) * modMathieuM 3 ν z h -
        Complex.exp (-(I * π * ν)) * (Complex.sin (s * π * ν) / Complex.sin (π * ν)) *
          modMathieuM 4 ν z h := by
  sorry

/-- **Shift by `sπi`** of `M^{(4)}_ν` (DLMF 28.20.25, fourth line), `ν ∉ ℤ` real, `h > 0`:
`M^{(4)}_ν(z + sπi) = e^{iπν}(sin(sπν)/sin(πν)) M^{(3)}_ν(z) + (sin((s+1)πν)/sin(πν))
M^{(4)}_ν(z)`. -/
@[dlmf 28.20.E25]
theorem modMathieuM_four_add_int_mul_pi_I {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ}
    (hh : 0 < h) (z : ℂ) (s : ℤ) :
    modMathieuM 4 ν (z + s * π * I) h =
      Complex.exp (I * π * ν) * (Complex.sin (s * π * ν) / Complex.sin (π * ν)) *
          modMathieuM 3 ν z h +
        Complex.sin ((s + 1) * π * ν) / Complex.sin (π * ν) * modMathieuM 4 ν z h := by
  sorry

end DLMF.Mathieu
