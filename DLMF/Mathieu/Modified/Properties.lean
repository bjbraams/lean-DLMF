/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.P3mWronskian
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

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

open Complex Set Filter Asymptotics MeasureTheory
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
  have hd : ∀ z, HasDerivAt (fun z => W (Complex.cosh z))
      (deriv W (Complex.cosh z) * Complex.sinh z) z := fun z =>
    (hW _).hasDerivAt.comp z (Complex.hasDerivAt_cosh z)
  refine ⟨fun z => (hd z).differentiableAt, fun z => ?_⟩
  have he : deriv (fun z => W (Complex.cosh z)) =
      fun z => deriv W (Complex.cosh z) * Complex.sinh z := funext fun z => (hd z).deriv
  rw [he]
  have h2 := ((hW' _).hasDerivAt.comp z (Complex.hasDerivAt_cosh z)).mul
    (Complex.hasDerivAt_sinh z)
  convert h2 using 1
  · rfl
  simp only [Function.comp_apply]
  have hs : Complex.sinh z ^ 2 = Complex.cosh z ^ 2 - 1 := by
    rw [← Complex.cosh_sq_sub_sinh_sq z]; ring
  have hc : Complex.cosh (2 * z) = 2 * Complex.cosh z ^ 2 - 1 := by
    rw [Complex.cosh_two_mul, hs]; ring
  rw [hc]
  linear_combination (-1 : ℂ) * hode (Complex.cosh z) - deriv (deriv W) (Complex.cosh z) * hs

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
    IsModMathieuSolution (mathieuLambda ν (h ^ 2)) (h ^ 2) (fun z => modMathieuM j ν z h) :=
  p2m_isModMathieuSolution_modMathieuM j hj₁ hj₄ hν hh

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

section p2mReality

open scoped ComplexConjugate

/-- The continued `J_μ(h e^x)` is real for real `μ`, `x` and `h > 0`. -/
lemma p2m_conj_besselJExp (μ x : ℝ) {h : ℝ} (hh : 0 < h) :
    conj (besselJExp μ h x) = besselJExp μ h x := by
  rw [p1c_besselJExp_eq μ hh (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]),
    show (h : ℂ) * Complex.exp x = ((h * Real.exp x : ℝ) : ℂ) by push_cast; rfl,
    DLMF.Bessel.besselJ_ofReal_eq_re μ _ (by positivity), Complex.conj_ofReal]

/-- The continued `Y_μ(h e^x)` is real for real `μ ∉ ℤ`. -/
lemma p2m_conj_besselYExp_of_not_int {μ : ℝ} (hμ : ∀ k : ℤ, (μ : ℂ) ≠ k) (x : ℝ) {h : ℝ}
    (hh : 0 < h) : conj (besselYExp μ h x) = besselYExp μ h x := by
  rw [p2m_besselYExp_of_not_int hμ, p2m_besselDExp,
    show -(μ : ℂ) = ((-μ : ℝ) : ℂ) by push_cast; rfl,
    show (μ : ℂ) * π = ((μ * π : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  simp only [map_div₀, map_sub, map_mul, Complex.conj_ofReal, p2m_conj_besselJExp _ _ hh]

/-- The continued `Y_μ(h e^x)` is real for every real `μ` (integer orders by continuity). -/
lemma p2m_conj_besselYExp (μ x : ℝ) {h : ℝ} (hh : 0 < h) :
    conj (besselYExp μ h x) = besselYExp μ h x := by
  by_cases hμ : ∀ k : ℤ, (μ : ℂ) ≠ k
  · exact p2m_conj_besselYExp_of_not_int hμ x hh
  push Not at hμ
  obtain ⟨k, hk⟩ := hμ
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set s : ℕ → ℝ := fun n => μ + 1 / ((n : ℝ) + 2)
  have hs : Tendsto s atTop (𝓝 μ) := by
    have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1) |>.congr
        (fun n => by simp; ring_nf)
    simpa [s] using this.const_add μ
  have hF : Continuous fun t : ℝ => besselYExp (t : ℂ) h x :=
    continuous_iff_continuousAt.mpr fun t =>
      (p2m_continuousAt_besselYExp_order hh' x t).comp Complex.continuous_ofReal.continuousAt
  have hns : ∀ n, ∀ m : ℤ, ((s n : ℝ) : ℂ) ≠ m := by
    intro n m hm
    have hm' : s n = m := by exact_mod_cast hm
    have hμk : μ = k := by exact_mod_cast hk
    simp only [s, hμk] at hm'
    have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have h2 : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have h3 : (1 / ((n : ℝ) + 2)) = ((m - k : ℤ) : ℝ) := by push_cast; linarith
    rw [h3] at h1 h2
    have : (0 : ℤ) < m - k := by exact_mod_cast h1
    have : m - k < (1 : ℤ) := by exact_mod_cast h2
    omega
  have t1 := (hF.tendsto μ).comp hs
  have t2 := (Complex.continuous_conj.tendsto _).comp t1
  refine tendsto_nhds_unique t2 (t1.congr fun n => ?_)
  simp only [Function.comp_apply]
  exact (p2m_conj_besselYExp_of_not_int (hns n) x hh).symm

/-- `me_k(π - x) = (-1)^k conj(me_k(x))` for integer `k`, real `q` and real `x`. -/
lemma p2m_mathieuMeInt_reflect (k : ℤ) (q x : ℝ) :
    mathieuMeInt k (π - x) q = (-1 : ℂ) ^ k * conj (mathieuMeInt k x q) := by
  have hper := (p2m_mathieuMeInt_floquet k q).2 ((x : ℂ) - π)
  rw [sub_add_cancel] at hper
  have hsq : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := m28b_negOnePow_mul_self k
  have hshift : mathieuMeInt k ((x : ℂ) - π) q = (-1 : ℂ) ^ k * mathieuMeInt k x q := by
    rw [hper, ← mul_assoc, hsq, one_mul]
  by_cases hk : 0 ≤ k
  · have hc : ∀ z, mathieuMeInt k z q = (Real.sqrt 2 : ℂ) * mathieuCe k.toNat z q := by
      intro z; simp [mathieuMeInt, hk]
    have hreal : conj (mathieuMeInt k x q) = mathieuMeInt k x q := by
      rw [hc]
      simp only [mathieuCe, map_mul, Complex.conj_ofReal, p1a1_mathieuWI_real]
    rw [hreal, ← hshift, show (π : ℂ) - x = -((x : ℂ) - π) by ring, hc, hc, mathieuCe_neg]
  · have hc : ∀ z, mathieuMeInt k z q = -((Real.sqrt 2 : ℂ) * I) * mathieuSe k.natAbs z q := by
      intro z; simp [mathieuMeInt, hk]
    have hreal : conj (mathieuMeInt k x q) = -mathieuMeInt k x q := by
      rw [hc, map_mul, mathieuSe, map_mul, Complex.conj_ofReal, p1a1_mathieuWII_real]
      simp
    rw [hreal, mul_neg, ← hshift, show (π : ℂ) - x = -((x : ℂ) - π) by ring, hc, hc,
      mathieuSe_neg]
    ring

/-- The coefficients `c^ν_{2m}(h²)` are real for real `ν` and real `h`. -/
lemma p2m_conj_mathieuMeCoeff (ν h : ℝ) (m : ℤ) :
    conj (mathieuMeCoeff ν ((h : ℂ) ^ 2) m) = mathieuMeCoeff ν ((h : ℂ) ^ 2) m := by
  by_cases hν : ∀ k : ℤ, (k : ℂ) ≠ ν
  · rw [mathieuMeCoeff_of_not_int hν]
    have := congrArg (fun p => p.2 m) (m28b_data_conj (ν : ℂ) ((h : ℂ) ^ 2))
    simp only [Complex.conj_ofReal, map_pow] at this
    exact this.symm
  push Not at hν
  obtain ⟨k₀, hk₀⟩ := hν
  rw [← hk₀, show (h : ℂ) ^ 2 = ((h ^ 2 : ℝ) : ℂ) by push_cast; rfl]
  set q : ℝ := h ^ 2
  have hex : ∃ k : ℤ, (k : ℂ) = (k₀ : ℂ) := ⟨k₀, rfl⟩
  simp only [mathieuMeCoeff, hex, ite_true, mathieuMe_intCast]
  set K : ℤ := k₀ + 2 * m
  have hK : ((k₀ : ℂ) + 2 * m) = (K : ℂ) := by push_cast [K]; ring
  rw [hK]
  set g : ℝ → ℂ := fun x => mathieuMeInt k₀ x q * Complex.exp (-(I * (K : ℂ) * x))
  have hg : ∀ x : ℝ, g (π - x) = conj (g x) := by
    intro x
    simp only [g]
    push_cast
    rw [p2m_mathieuMeInt_reflect, map_mul, ← Complex.exp_conj]
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
    rw [show -(I * (K : ℂ) * (π - x)) = -(I * K * π) + -(-I * K * x) by ring, Complex.exp_add,
      show -(I * (K : ℂ) * π) = ((-K : ℤ) : ℂ) * (π * I) by push_cast; ring,
      Complex.exp_int_mul, Complex.exp_pi_mul_I]
    have : (-1 : ℂ) ^ k₀ * (-1 : ℂ) ^ (-K) = 1 := by
      rw [← zpow_add₀ (by norm_num), show k₀ + -K = 2 * (-m) by simp [K], zpow_mul]
      simp
    linear_combination (conj (mathieuMeInt k₀ x q) * Complex.exp (-(-I * K * x))) * this
  have hint : ∫ x in (0 : ℝ)..π, g x = conj (∫ x in (0 : ℝ)..π, g x) := by
    calc ∫ x in (0 : ℝ)..π, g x = ∫ x in (0 : ℝ)..π, g (π - x) := by
          rw [intervalIntegral.integral_comp_sub_left]; simp
      _ = ∫ x in (0 : ℝ)..π, conj (g x) := by simp only [hg]
      _ = _ := by
          rw [intervalIntegral.integral_of_le Real.pi_pos.le,
            intervalIntegral.integral_of_le Real.pi_pos.le, integral_conj]
  rw [map_mul]
  simp only [g] at hint
  rw [← hint]
  congr 1
  simp

/-- **Reality** (DLMF §28.20(iii)): proof of `modMathieuM_one_two_real`. -/
lemma p2m_modMathieuM_real {j : ℕ} (hj : j = 1 ∨ j = 2) {ν h : ℝ} (hh : 0 < h) (x : ℝ) :
    (modMathieuM j ν x h).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  have hterm : ∀ n ℓ : ℤ, conj (modMathieuTerm j ν x h n ℓ) = modMathieuTerm j ν x h n ℓ := by
    intro n ℓ
    have hJ : conj (besselJExp ((ℓ - n : ℤ) : ℂ) h (-x)) = besselJExp ((ℓ - n : ℤ) : ℂ) h (-x) := by
      have := p2m_conj_besselJExp ((ℓ - n : ℤ) : ℝ) (-x) hh
      push_cast at this ⊢
      exact this
    have hC : conj (mathieuCylExp j (ν + n + ℓ) h x) = mathieuCylExp j (ν + n + ℓ) h x := by
      have e : (ν : ℂ) + n + ℓ = ((ν + n + ℓ : ℝ) : ℂ) := by push_cast; ring
      rw [e]
      rcases hj with rfl | rfl
      · exact p2m_conj_besselJExp _ _ hh
      · exact p2m_conj_besselYExp _ _ hh
    simp only [modMathieuTerm, map_mul, map_zpow₀, map_neg, map_one, hJ, hC,
      p2m_conj_mathieuMeCoeff]
  simp only [modMathieuM, map_mul, map_inv₀, Complex.conj_tsum, hterm, p2m_conj_mathieuMeCoeff]

end p2mReality

/-- `M^{(1)}_ν` and `M^{(2)}_ν` are **real on the real axis** for real `ν` and `h > 0`
(DLMF §28.20(iii)). -/
@[dlmf 28.20.iii]
theorem modMathieuM_one_two_real {ν h : ℝ} (hh : 0 < h) (x : ℝ) :
    (modMathieuM 1 ν x h).im = 0 ∧ (modMathieuM 2 ν x h).im = 0 :=
  ⟨p2m_modMathieuM_real (Or.inl rfl) hh x, p2m_modMathieuM_real (Or.inr rfl) hh x⟩

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
  have hadm := p1c_admissible_real' ν h
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hW := p3m_wronskian_one_two (ν := ν) hh z
  have d1 := (isModMathieuSolution_modMathieuM 1 le_rfl (by norm_num) hadm hh').differentiable z
  have d2 :=
    (isModMathieuSolution_modMathieuM 2 (by norm_num) (by norm_num) hadm hh').differentiable z
  have e3 : (fun z => modMathieuM 3 ν z h) =
      fun z => modMathieuM 1 ν z h + I * modMathieuM 2 ν z h :=
    funext fun z => modMathieuM_three hadm hh' z
  have e4 : (fun z => modMathieuM 4 ν z h) =
      fun z => modMathieuM 1 ν z h - I * modMathieuM 2 ν z h :=
    funext fun z => modMathieuM_four hadm hh' z
  have D3 : deriv (fun z => modMathieuM 1 ν z h + I * modMathieuM 2 ν z h) z =
      deriv (fun z => modMathieuM 1 ν z h) z + I * deriv (fun z => modMathieuM 2 ν z h) z :=
    (d1.hasDerivAt.add (d2.hasDerivAt.const_mul I)).deriv
  have D4 : deriv (fun z => modMathieuM 1 ν z h - I * modMathieuM 2 ν z h) z =
      deriv (fun z => modMathieuM 1 ν z h) z - I * deriv (fun z => modMathieuM 2 ν z h) z :=
    (d1.hasDerivAt.sub (d2.hasDerivAt.const_mul I)).deriv
  refine ⟨hW, ?_, ?_⟩
  · simp only [m28c_wronskian] at hW ⊢
    rw [e3, D3, modMathieuM_three hadm hh' z]
    linear_combination -hW
  · simp only [m28c_wronskian] at hW ⊢
    rw [e4, D4, modMathieuM_four hadm hh' z]
    linear_combination -hW

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
  have hadm := p1c_admissible_real' ν h
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hW := (modMathieuM_wronskian_two (ν := ν) hh z).1
  have d1 := (isModMathieuSolution_modMathieuM 1 le_rfl (by norm_num) hadm hh').differentiable z
  have d2 :=
    (isModMathieuSolution_modMathieuM 2 (by norm_num) (by norm_num) hadm hh').differentiable z
  have e3 : (fun z => modMathieuM 3 ν z h) =
      fun z => modMathieuM 1 ν z h + I * modMathieuM 2 ν z h :=
    funext fun z => modMathieuM_three hadm hh' z
  have e4 : (fun z => modMathieuM 4 ν z h) =
      fun z => modMathieuM 1 ν z h - I * modMathieuM 2 ν z h :=
    funext fun z => modMathieuM_four hadm hh' z
  have D3 : deriv (fun z => modMathieuM 1 ν z h + I * modMathieuM 2 ν z h) z =
      deriv (fun z => modMathieuM 1 ν z h) z + I * deriv (fun z => modMathieuM 2 ν z h) z :=
    (d1.hasDerivAt.add (d2.hasDerivAt.const_mul I)).deriv
  have D4 : deriv (fun z => modMathieuM 1 ν z h - I * modMathieuM 2 ν z h) z =
      deriv (fun z => modMathieuM 1 ν z h) z - I * deriv (fun z => modMathieuM 2 ν z h) z :=
    (d1.hasDerivAt.sub (d2.hasDerivAt.const_mul I)).deriv
  simp only [m28c_wronskian] at hW ⊢
  rw [e3, e4, D3, D4, modMathieuM_three hadm hh' z, modMathieuM_four hadm hh' z]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination I * hW
  · linear_combination -I * hW
  · linear_combination (-2 * I) * hW

/-! ### §28.20(vii) Shift of variable -/

/-- Term-wise form of 28.20.22: the shift `z ↦ z ± πi/2` against `h ↦ ±ih`. -/
lemma p1c_modMathieuTerm_add_pi_div_two (j : ℕ) {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν)
    {h : ℝ} (hh : 0 < h) {σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (z : ℂ) (n ℓ : ℤ) :
    modMathieuTerm j ν (z + σ * π * I / 2) h n ℓ =
      (-1 : ℂ) ^ n * modMathieuTerm j ν z (σ * I * h) n ℓ := by
  have hσ' : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> simp
  have hJ := p1c_besselJExp_add_pi_div_two ((ℓ - n : ℤ) : ℂ) hh hσ' (-z)
  rw [show -z + -σ * π * I / 2 = -(z + σ * π * I / 2) by ring,
    show -σ * I * (h : ℂ) = -(σ * I * h) by ring, p1c_besselJExp_neg_h_intCast] at hJ
  have hq : (σ * I * (h : ℂ)) ^ 2 = -((h : ℂ) ^ 2) := by
    rcases hσ with rfl | rfl <;> ring_nf <;> rw [I_sq] <;> ring
  simp only [modMathieuTerm]
  rw [hJ, p1c_mathieuCylExp_add_pi_div_two j _ hh hσ z, hq,
    mathieuMeCoeff_neg_q (p1c_not_int_cast hν)]
  have e : (-1 : ℂ) ^ (ℓ - n) = (-1 : ℂ) ^ n * (-1 : ℂ) ^ ℓ := by
    rw [zpow_sub₀ (by norm_num)]
    have h2 : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
      rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; simp
    field_simp
    linear_combination -h2
  rw [e]
  ring


/-- **Shift by `±πi/2`** (DLMF 28.20.22), `ν` real, `ν ∉ ℤ`, `h > 0`, `σ = ±1`,
`j = 1, 2, 3, 4`: `M^{(j)}_ν(z ± πi/2, h) = M^{(j)}_ν(z, ±ih)`. -/
@[dlmf 28.20.E22]
theorem modMathieuM_add_pi_div_two (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν : ℝ}
    (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ} (hh : 0 < h) {σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (z : ℂ) :
    modMathieuM j ν (z + σ * π * I / 2) h = modMathieuM j ν z (σ * I * h) := by
  have hq : (σ * I * (h : ℂ)) ^ 2 = ((-(h ^ 2) : ℝ) : ℂ) := by
    push_cast
    rcases hσ with rfl | rfl <;> ring_nf <;> rw [I_sq] <;> ring
  have hadm : ModMathieuAdmissible ν (σ * I * h) := by
    refine Or.inl ⟨p1c_not_int_cast hν, ?_⟩
    rw [hq]
    exact (mathieuNormalSegment_real (ν := ν) (q := -(h ^ 2)) (p1c_not_int_cast hν)).1
  have hne : σ * I * (h : ℂ) ≠ 0 := by
    have : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    rcases hσ with rfl | rfl <;> simp [this]
  have hc := p1c_coeff_index_ne_zero hν h
  set n := modMathieuIndex ν h
  have hR := hasSum_modMathieuTerm j hj₁ hj₄ hadm hne n z
  have hq' : (σ * I * (h : ℂ)) ^ 2 = -((h : ℂ) ^ 2) := by rw [hq]; push_cast; ring
  rw [hq', mathieuMeCoeff_neg_q (p1c_not_int_cast hν)] at hR
  have hL := hR.mul_left ((-1 : ℂ) ^ n)
  have e : (fun ℓ => (-1 : ℂ) ^ n * modMathieuTerm j ν z (σ * I * h) n ℓ) =
      modMathieuTerm j ν (z + σ * π * I / 2) h n := by
    funext ℓ; rw [p1c_modMathieuTerm_add_pi_div_two j hν hh hσ]
  rw [e] at hL
  have eL : modMathieuM j ν (z + σ * π * I / 2) h = (mathieuMeCoeff ν ((h : ℂ) ^ 2) n)⁻¹ *
      ∑' ℓ, modMathieuTerm j ν (z + σ * π * I / 2) h n ℓ := rfl
  rw [eL, hL.tsum_eq]
  have h2 : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; simp
  rw [show ∀ a b d : ℂ, a⁻¹ * (b * (b * a * d)) = (b * b) * (a⁻¹ * a) * d by intros; ring,
    h2, inv_mul_cancel₀ hc]
  ring

/-- `(-1)^n (-1)^n = 1` for `n ∈ ℤ`. -/
lemma p1c_neg_one_zpow_mul_self (n : ℤ) : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
  rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; simp

/-- The integer-order coefficients as Fourier integrals. -/
lemma p1c_mathieuMeCoeff_intCast (k ℓ : ℤ) (q : ℂ) :
    mathieuMeCoeff k q ℓ = (1 / π : ℂ) * ∫ x in (0 : ℝ)..π,
      mathieuMe k x q * Complex.exp (-(I * (k + 2 * ℓ) * x)) := by
  simp only [mathieuMeCoeff, show (∃ j : ℤ, (j : ℂ) = k) from ⟨k, rfl⟩, ↓reduceIte]

/-- `e^{-iNπ} = (-1)^N`. -/
theorem p1c_exp_neg_I_int_mul_pi (N : ℤ) : Complex.exp (-(I * N * π)) = (-1 : ℂ) ^ N := by
  rw [show -(I * N * π) = N * (-(π * I)) by ring, Complex.exp_int_mul, Complex.exp_neg,
    Complex.exp_pi_mul_I]; simp

/-- Coefficients after a quarter-period shift: if `me_k(x, q') = ε me_{k'}(x - π/2, q)` and
`me_{k'}(·, q)` has multiplier `(-1)^{k'}` under `x ↦ x + π`, then
`c^k_{2ℓ}(q') = ε e^{-i(k+2ℓ)π/2} c^{k'}_{2ℓ'}(q)` whenever `k' + 2ℓ' = k + 2ℓ`. -/
lemma p1c_mathieuMeCoeff_shift {k k' ℓ ℓ' : ℤ} (hkl : k' + 2 * ℓ' = k + 2 * ℓ) {q q' ε : ℂ}
    (hme : ∀ x : ℝ, mathieuMe k x q' = ε * mathieuMe k' ((x : ℂ) - π / 2) q)
    (hper : ∀ y : ℝ, mathieuMe k' ((y : ℂ) + π) q = (-1 : ℂ) ^ k' * mathieuMe k' y q) :
    mathieuMeCoeff k q' ℓ =
      ε * Complex.exp (-(I * (k + 2 * ℓ) * (π / 2))) * mathieuMeCoeff k' q ℓ' := by
  have hN : ((k' : ℂ) + 2 * ℓ') = k + 2 * ℓ := by exact_mod_cast hkl
  set g : ℝ → ℂ := fun y => mathieuMe k' y q * Complex.exp (-(I * (k + 2 * ℓ) * y))
  have hg : Function.Periodic g π := by
    intro y
    simp only [g]
    push_cast
    rw [hper y, show -(I * (k + 2 * ℓ) * ((y : ℂ) + π)) =
      -(I * (k + 2 * ℓ) * y) + -(I * ((k' + 2 * ℓ' : ℤ) : ℂ) * π) by push_cast; rw [hN]; ring,
      Complex.exp_add, p1c_exp_neg_I_int_mul_pi]
    have : (-1 : ℂ) ^ k' * (-1 : ℂ) ^ (k' + 2 * ℓ') = 1 := by
      rw [zpow_add₀ (by norm_num), zpow_mul]; simp [p1c_neg_one_zpow_mul_self]
    linear_combination mathieuMe k' y q * Complex.exp (-(I * (k + 2 * ℓ) * y)) * this
  rw [p1c_mathieuMeCoeff_intCast, p1c_mathieuMeCoeff_intCast]
  have e1 : (fun x : ℝ => mathieuMe k x q' * Complex.exp (-(I * (k + 2 * ℓ) * x))) =
      fun x : ℝ => ε * Complex.exp (-(I * (k + 2 * ℓ) * (π / 2))) * g (x - π / 2) := by
    funext x
    simp only [g]
    rw [hme x]
    push_cast
    rw [show -(I * (k + 2 * ℓ) * (x : ℂ)) = -(I * (k + 2 * ℓ) * (π / 2)) +
      -(I * (k + 2 * ℓ) * ((x : ℂ) - π / 2)) by ring, Complex.exp_add]
    ring
  rw [e1, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right,
    show (0 : ℝ) - π / 2 = -(π / 2) by ring, show π - π / 2 = -(π / 2) + π by ring,
    hg.intervalIntegral_add_eq (-(π / 2)) 0, zero_add]
  simp only [g]
  rw [← hN]
  ring


/-- `me_N = √2 ce_N` for `N ≥ 0` (DLMF 28.12.11). -/
lemma p1c_mathieuMe_natCast (N : ℕ) (z : ℂ) (Q : ℝ) :
    mathieuMe ((N : ℤ) : ℂ) z Q = (Real.sqrt 2 : ℂ) * mathieuCe N z Q := by
  rw [mathieuMe_intCast, mathieuMeInt, ite_eq_left (by positivity)]; simp

/-- `me_{-N} = -√2 i se_N` for `N ≥ 1` (DLMF 28.12.11). -/
lemma p1c_mathieuMe_negNatCast {N : ℕ} (hN : N ≠ 0) (z : ℂ) (Q : ℝ) :
    mathieuMe ((-(N : ℤ) : ℤ) : ℂ) z Q = -((Real.sqrt 2 : ℂ) * I) * mathieuSe N z Q := by
  rw [mathieuMe_intCast, mathieuMeInt, ite_eq_right (by omega)]; simp

/-- `e^{-i(2M)π/2} = (-1)^M`. -/
lemma p1c_exp_half_even (M : ℤ) : Complex.exp (-(I * (2 * M) * (π / 2))) = (-1 : ℂ) ^ M := by
  rw [show -(I * (2 * (M : ℂ)) * (π / 2)) = -(I * M * π) by ring, p1c_exp_neg_I_int_mul_pi]

/-- `e^{-i(2M+1)π/2} = -i (-1)^M`. -/
lemma p1c_exp_half_odd (M : ℤ) :
    Complex.exp (-(I * (2 * M + 1) * (π / 2))) = (-1 : ℂ) ^ M * (-I) := by
  rw [show -(I * (2 * (M : ℂ) + 1) * (π / 2)) = -(I * M * π) + -(π / 2 * I) by ring,
    Complex.exp_add, p1c_exp_neg_I_int_mul_pi, Complex.exp_neg, Complex.exp_mul_I]
  simp [← Complex.ofReal_ofNat, ← Complex.ofReal_div, ← Complex.ofReal_cos, ← Complex.ofReal_sin]


/-- `(-1)^{2n} = 1`. -/
lemma p1c_neg_one_zpow_two_mul (n : ℤ) : (-1 : ℂ) ^ (2 * n) = 1 := by
  rw [zpow_mul]; simp

/-- `c^{2n}_{2ℓ}(-Q) = (-1)^ℓ c^{2n}_{2ℓ}(Q)` (from 28.2.34). -/
lemma p1c_coeff_even_neg (n : ℕ) (Q : ℝ) (ℓ : ℤ) :
    mathieuMeCoeff (((2 * n : ℕ) : ℤ) : ℂ) ((-Q : ℝ) : ℂ) ℓ =
      (-1 : ℂ) ^ ℓ * mathieuMeCoeff (((2 * n : ℕ) : ℤ) : ℂ) (Q : ℂ) ℓ := by
  rw [p1c_mathieuMeCoeff_shift (k := ((2 * n : ℕ) : ℤ)) (k' := ((2 * n : ℕ) : ℤ)) (ℓ' := ℓ) rfl
    (ε := (-1 : ℂ) ^ n)]
  · rw [show ((((2 * n : ℕ) : ℤ) : ℂ) + 2 * ℓ) = 2 * ((n + ℓ : ℤ) : ℂ) by push_cast; ring,
      p1c_exp_half_even, zpow_add₀ (by norm_num), zpow_natCast]
    have := p1c_neg_one_zpow_mul_self n
    simp only [zpow_natCast] at this
    linear_combination (-1 : ℂ) ^ ℓ * mathieuMeCoeff (((2 * n : ℕ) : ℤ) : ℂ) (Q : ℂ) ℓ * this
  · intro x
    rw [p1c_mathieuMe_natCast, p1c_mathieuMe_natCast, mathieuCe_even_neg_q,
      show (π / 2 : ℂ) - x = -((x : ℂ) - π / 2) by ring, mathieuCe_neg]
    ring
  · intro y
    rw [p1c_mathieuMe_natCast, p1c_mathieuMe_natCast, mathieuCe_even_add_pi]
    push_cast; rw [p1c_neg_one_zpow_two_mul]; ring


/-- `(-1)^n (-1)^n = 1` for `n ∈ ℕ`. -/
lemma p1c_neg_one_pow_mul_self (n : ℕ) : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; simp

/-- `(-1)^{a-b} = (-1)^a (-1)^b`. -/
lemma p1c_neg_one_zpow_sub (a b : ℤ) : (-1 : ℂ) ^ (a - b) = (-1 : ℂ) ^ a * (-1 : ℂ) ^ b := by
  rw [zpow_sub₀ (by norm_num), div_eq_mul_inv,
    inv_eq_of_mul_eq_one_right (p1c_neg_one_zpow_mul_self b)]

/-- `c^{-(2n+2)}_{2ℓ}(-Q) = (-1)^ℓ c^{-(2n+2)}_{2ℓ}(Q)` (from 28.2.37). -/
lemma p1c_coeff_negEven_neg (n : ℕ) (Q : ℝ) (ℓ : ℤ) :
    mathieuMeCoeff ((-((2 * n + 2 : ℕ) : ℤ) : ℤ) : ℂ) ((-Q : ℝ) : ℂ) ℓ =
      (-1 : ℂ) ^ ℓ * mathieuMeCoeff ((-((2 * n + 2 : ℕ) : ℤ) : ℤ) : ℂ) (Q : ℂ) ℓ := by
  have hN : (2 * n + 2 : ℕ) ≠ 0 := by omega
  rw [p1c_mathieuMeCoeff_shift (k := -((2 * n + 2 : ℕ) : ℤ)) (k' := -((2 * n + 2 : ℕ) : ℤ))
    (ℓ' := ℓ) rfl (ε := -(-1 : ℂ) ^ n)]
  · rw [show (((-((2 * n + 2 : ℕ) : ℤ) : ℤ) : ℂ) + 2 * ℓ) = 2 * ((ℓ - n - 1 : ℤ) : ℂ) by
      push_cast; ring, p1c_exp_half_even, p1c_neg_one_zpow_sub, p1c_neg_one_zpow_sub]
    have := p1c_neg_one_pow_mul_self n
    simp only [zpow_natCast, zpow_one]
    linear_combination (-1 : ℂ) ^ ℓ * mathieuMeCoeff ((-((2 * n + 2 : ℕ) : ℤ) : ℤ) : ℂ) (Q : ℂ) ℓ *
      this
  · intro x
    rw [p1c_mathieuMe_negNatCast hN, p1c_mathieuMe_negNatCast hN,
      mathieuSe_even_neg_q,
      show (π / 2 : ℂ) - x = -((x : ℂ) - π / 2) by ring, mathieuSe_neg]
    ring
  · intro y
    rw [p1c_mathieuMe_negNatCast hN, p1c_mathieuMe_negNatCast hN, mathieuSe_even_add_pi,
      show (-((2 * n + 2 : ℕ) : ℤ)) = 2 * (-(n + 1 : ℤ)) by push_cast; ring,
      p1c_neg_one_zpow_two_mul]
    ring

/-- `c^{2n+1}_{2ℓ}(-Q) = -(-1)^ℓ c^{-(2n+1)}_{2(ℓ+2n+1)}(Q)` (from 28.2.35). -/
lemma p1c_coeff_odd_neg (n : ℕ) (Q : ℝ) (ℓ : ℤ) :
    mathieuMeCoeff (((2 * n + 1 : ℕ) : ℤ) : ℂ) ((-Q : ℝ) : ℂ) ℓ =
      -1 * (-1 : ℂ) ^ ℓ *
        mathieuMeCoeff ((-((2 * n + 1 : ℕ) : ℤ) : ℤ) : ℂ) (Q : ℂ) (ℓ + ((2 * n + 1 : ℕ) : ℤ)) := by
  have hN : (2 * n + 1 : ℕ) ≠ 0 := by omega
  rw [p1c_mathieuMeCoeff_shift (k := ((2 * n + 1 : ℕ) : ℤ)) (k' := -((2 * n + 1 : ℕ) : ℤ))
    (ℓ' := ℓ + ((2 * n + 1 : ℕ) : ℤ)) (by ring) (ε := (-1 : ℂ) ^ (n + 1) * I)]
  · rw [show ((((2 * n + 1 : ℕ) : ℤ) : ℂ) + 2 * ℓ) = 2 * ((n + ℓ : ℤ) : ℂ) + 1 by
      push_cast; ring, p1c_exp_half_odd, zpow_add₀ (by norm_num)]
    have := p1c_neg_one_pow_mul_self n
    simp only [zpow_natCast]
    linear_combination (-1 : ℂ) ^ ℓ *
      mathieuMeCoeff ((-((2 * n + 1 : ℕ) : ℤ) : ℤ) : ℂ) (Q : ℂ) (ℓ + ((2 * n + 1 : ℕ) : ℤ)) *
      (-this + (-1 : ℂ) ^ n * (-1 : ℂ) ^ n * I_sq)
  · intro x
    rw [p1c_mathieuMe_natCast, p1c_mathieuMe_negNatCast hN, mathieuCe_odd_neg_q,
      show (π / 2 : ℂ) - x = -((x : ℂ) - π / 2) by ring, mathieuSe_neg]
    linear_combination -(-1 : ℂ) ^ n * (Real.sqrt 2 : ℂ) *
      mathieuSe (2 * n + 1) ((x : ℂ) - π / 2) Q * I_sq
  · intro y
    rw [p1c_mathieuMe_negNatCast hN, p1c_mathieuMe_negNatCast hN, mathieuSe_odd_add_pi,
      show (-((2 * n + 1 : ℕ) : ℤ)) = 2 * (-(n + 1 : ℤ)) + 1 by push_cast; ring,
      zpow_add₀ (by norm_num), p1c_neg_one_zpow_two_mul]
    ring

/-- `c^{-(2n+1)}_{2ℓ}(-Q) = (-1)^ℓ c^{2n+1}_{2(ℓ-2n-1)}(Q)` (from 28.2.36). -/
lemma p1c_coeff_negOdd_neg (n : ℕ) (Q : ℝ) (ℓ : ℤ) :
    mathieuMeCoeff ((-((2 * n + 1 : ℕ) : ℤ) : ℤ) : ℂ) ((-Q : ℝ) : ℂ) ℓ =
      1 * (-1 : ℂ) ^ ℓ *
        mathieuMeCoeff (((2 * n + 1 : ℕ) : ℤ) : ℂ) (Q : ℂ) (ℓ + -((2 * n + 1 : ℕ) : ℤ)) := by
  have hN : (2 * n + 1 : ℕ) ≠ 0 := by omega
  rw [p1c_mathieuMeCoeff_shift (k := -((2 * n + 1 : ℕ) : ℤ)) (k' := ((2 * n + 1 : ℕ) : ℤ))
    (ℓ' := ℓ + -((2 * n + 1 : ℕ) : ℤ)) (by ring) (ε := -I * (-1 : ℂ) ^ n)]
  · rw [show (((-((2 * n + 1 : ℕ) : ℤ) : ℤ) : ℂ) + 2 * ℓ) = 2 * ((ℓ - n - 1 : ℤ) : ℂ) + 1 by
      push_cast; ring, p1c_exp_half_odd, p1c_neg_one_zpow_sub, p1c_neg_one_zpow_sub]
    have := p1c_neg_one_pow_mul_self n
    simp only [zpow_natCast, zpow_one]
    linear_combination (-1 : ℂ) ^ ℓ *
      mathieuMeCoeff (((2 * n + 1 : ℕ) : ℤ) : ℂ) (Q : ℂ) (ℓ + -((2 * n + 1 : ℕ) : ℤ)) *
      (this - (-1 : ℂ) ^ n * (-1 : ℂ) ^ n * I_sq)
  · intro x
    rw [p1c_mathieuMe_natCast, p1c_mathieuMe_negNatCast hN, mathieuSe_odd_neg_q,
      show (π / 2 : ℂ) - x = -((x : ℂ) - π / 2) by ring, mathieuCe_neg]
    ring
  · intro y
    rw [p1c_mathieuMe_natCast, p1c_mathieuMe_natCast, mathieuCe_odd_add_pi,
      show (((2 * n + 1 : ℕ) : ℤ)) = 2 * (n : ℤ) + 1 by push_cast; ring,
      zpow_add₀ (by norm_num), p1c_neg_one_zpow_two_mul]
    ring

/-- The shift `z ↦ z ± πi/2` of a cross-product term, any order. -/
lemma p1c_modMathieuTerm_add_pi_div_two_gen (j : ℕ) (ν : ℂ) {h : ℝ} (hh : 0 < h) {σ : ℂ}
    (hσ : σ = 1 ∨ σ = -1) (z : ℂ) (n ℓ : ℤ) :
    modMathieuTerm j ν (z + σ * π * I / 2) h n ℓ =
      (-1 : ℂ) ^ (ℓ - n) * ((-1 : ℂ) ^ ℓ * mathieuMeCoeff ν ((h : ℂ) ^ 2) ℓ *
        besselJExp ((ℓ - n : ℤ) : ℂ) (σ * I * h) (-z) *
          mathieuCylExp j (ν + n + ℓ) (σ * I * h) z) := by
  have hσ' : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> simp
  have hJ := p1c_besselJExp_add_pi_div_two ((ℓ - n : ℤ) : ℂ) hh hσ' (-z)
  rw [show -z + -σ * π * I / 2 = -(z + σ * π * I / 2) by ring,
    show -σ * I * (h : ℂ) = -(σ * I * h) by ring, p1c_besselJExp_neg_h_intCast] at hJ
  simp only [modMathieuTerm]
  rw [hJ, p1c_mathieuCylExp_add_pi_div_two j _ hh hσ z]
  ring

/-- **General shift by `±πi/2`**: if the coefficients of order `ν₁ = ν₀ + 2d` at `(±ih)²` are
`κ (-1)^ℓ c^{ν₀}_{2(ℓ+d)}(h²)`, then `M^{(j)}_{ν₀}(z ± πi/2, h) = (-1)^d M^{(j)}_{ν₁}(z, ±ih)`. -/
lemma p1c_modMathieuM_add_pi_div_two_gen (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν₀ ν₁ : ℂ}
    (d : ℤ) (hν : ν₁ = ν₀ + 2 * d) {h : ℝ} (hh : 0 < h) {σ : ℂ} (hσ : σ = 1 ∨ σ = -1)
    {κ : ℂ} (hκ : κ ≠ 0) (hadm : ModMathieuAdmissible ν₁ (σ * I * h))
    (hc : ∀ ℓ : ℤ, mathieuMeCoeff ν₁ ((σ * I * h) ^ 2) ℓ =
      κ * (-1 : ℂ) ^ ℓ * mathieuMeCoeff ν₀ ((h : ℂ) ^ 2) (ℓ + d)) (z : ℂ) :
    modMathieuM j ν₀ (z + σ * π * I / 2) h = (-1 : ℂ) ^ d * modMathieuM j ν₁ z (σ * I * h) := by
  have hne : σ * I * (h : ℂ) ≠ 0 := by
    have : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    rcases hσ with rfl | rfl <;> simp [this]
  set n0 := modMathieuIndex ν₀ h
  by_cases h0 : mathieuMeCoeff ν₀ ((h : ℂ) ^ 2) n0 = 0
  · -- all coefficients vanish
    have hall : ∀ ℓ, mathieuMeCoeff ν₀ ((h : ℂ) ^ 2) ℓ = 0 := by
      intro ℓ
      by_contra hl
      have hex : ∃ n : ℤ, mathieuMeCoeff ν₀ ((h : ℂ) ^ 2) n ≠ 0 := ⟨ℓ, hl⟩
      apply hex.choose_spec
      have : n0 = hex.choose := by simp only [n0, modMathieuIndex, dite_eq_left hex]
      rw [← this]; exact h0
    have e1 : modMathieuM j ν₀ (z + σ * π * I / 2) h = 0 := by
      simp only [modMathieuM]; rw [h0, inv_zero, zero_mul]
    have e2 : modMathieuM j ν₁ z (σ * I * h) = 0 := by
      simp only [modMathieuM, modMathieuTerm, hc, hall]; simp
    rw [e1, e2, mul_zero]
  · set k := n0 - d
    have hR := hasSum_modMathieuTerm j hj₁ hj₄ hadm hne k z
    rw [← (Equiv.addRight (-d)).hasSum_iff] at hR
    have hL := hR.mul_left ((-1 : ℂ) ^ n0 * κ⁻¹)
    have e : (fun ℓ => (-1 : ℂ) ^ n0 * κ⁻¹ *
        (modMathieuTerm j ν₁ z (σ * I * h) k ∘ (Equiv.addRight (-d))) ℓ) =
        modMathieuTerm j ν₀ (z + σ * π * I / 2) h n0 := by
      funext ℓ
      rw [p1c_modMathieuTerm_add_pi_div_two_gen j ν₀ hh hσ]
      simp only [Function.comp_apply, Equiv.coe_addRight, modMathieuTerm, hc]
      rw [show ℓ + -d + d = ℓ by ring, show ℓ + -d - k = ℓ - n0 by ring,
        show ν₁ + ((k : ℤ) : ℂ) + ((ℓ + -d : ℤ) : ℂ) = ν₀ + n0 + ℓ by
          rw [hν]; simp only [k]; push_cast; ring]
      have h1 : (-1 : ℂ) ^ (ℓ - n0) = (-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ n0 := by
        rw [zpow_sub₀ (by norm_num), div_eq_mul_inv,
          inv_eq_of_mul_eq_one_right (p1c_neg_one_zpow_mul_self n0)]
      have h2 := p1c_neg_one_zpow_mul_self (ℓ + -d)
      have h3 := p1c_neg_one_zpow_mul_self ℓ
      have hκ' : κ⁻¹ * κ = 1 := inv_mul_cancel₀ hκ
      rw [h1]
      linear_combination (-1 : ℂ) ^ n0 * mathieuMeCoeff ν₀ ((h : ℂ) ^ 2) ℓ *
        besselJExp ((ℓ - n0 : ℤ) : ℂ) (σ * I * h) (-z) *
        mathieuCylExp j (ν₀ + n0 + ℓ) (σ * I * h) z *
        ((-1 : ℂ) ^ (ℓ + -d) * (-1 : ℂ) ^ (ℓ + -d) * hκ' + h2 - h3)
    rw [e] at hL
    have eL : modMathieuM j ν₀ (z + σ * π * I / 2) h = (mathieuMeCoeff ν₀ ((h : ℂ) ^ 2) n0)⁻¹ *
        ∑' ℓ, modMathieuTerm j ν₀ (z + σ * π * I / 2) h n0 ℓ := rfl
    rw [eL, hL.tsum_eq, hc, show k + d = n0 by ring]
    have hk : (-1 : ℂ) ^ k = (-1 : ℂ) ^ n0 * (-1 : ℂ) ^ d := by
      simp only [k]
      rw [zpow_sub₀ (by norm_num), div_eq_mul_inv,
        inv_eq_of_mul_eq_one_right (p1c_neg_one_zpow_mul_self d)]
    have hκ' : κ⁻¹ * κ = 1 := inv_mul_cancel₀ hκ
    have h0' : (mathieuMeCoeff ν₀ ((h : ℂ) ^ 2) n0)⁻¹ * mathieuMeCoeff ν₀ ((h : ℂ) ^ 2) n0 = 1 :=
      inv_mul_cancel₀ h0
    rw [hk]
    linear_combination (-1 : ℂ) ^ d * modMathieuM j ν₁ z (σ * I * h) *
      ((-1 : ℂ) ^ n0 * (-1 : ℂ) ^ n0 * (mathieuMeCoeff ν₀ ((h : ℂ) ^ 2) n0)⁻¹ *
        mathieuMeCoeff ν₀ ((h : ℂ) ^ 2) n0 * hκ' +
        (-1 : ℂ) ^ n0 * (-1 : ℂ) ^ n0 * h0' + p1c_neg_one_zpow_mul_self n0)


/-- `(±ih)² = -h²`. -/
lemma p1c_sq_sigma {σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (h : ℝ) :
    (σ * I * (h : ℂ)) ^ 2 = ((-(h ^ 2) : ℝ) : ℂ) := by
  push_cast
  rcases hσ with rfl | rfl <;> ring_nf <;> rw [I_sq] <;> ring

/-- Integer orders are admissible at `±ih` for real `h`. -/
lemma p1c_admissible_int (k : ℤ) {σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (h : ℝ) :
    ModMathieuAdmissible (k : ℂ) (σ * I * h) :=
  Or.inr ⟨⟨k, rfl⟩, by rw [p1c_sq_sigma hσ]; exact ofReal_im _⟩

/-- `(h : ℂ)² = ((h² : ℝ) : ℂ)`. -/
lemma p1c_hsq (h : ℝ) : (h : ℂ) ^ 2 = ((h ^ 2 : ℝ) : ℂ) := by push_cast; ring

/-- **Shift by `±πi/2`** for integer order (DLMF 28.20.23), `n = 0, 1, …`, `h > 0`, `σ = ±1`:
`Mc^{(j)}_{2n}(z ± πi/2, h) = Mc^{(j)}_{2n}(z, ±ih)` and
`Ms^{(j)}_{2n+1}(z ± πi/2, h) = Mc^{(j)}_{2n+1}(z, ±ih)`. -/
@[dlmf 28.20.E23]
theorem radialMathieu_add_pi_div_two_even (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (n : ℕ)
    {h : ℝ} (hh : 0 < h) {σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (z : ℂ) :
    radialMathieuMc j (2 * n) (z + σ * π * I / 2) h = radialMathieuMc j (2 * n) z (σ * I * h) ∧
      radialMathieuMs j (2 * n + 1) (z + σ * π * I / 2) h =
        radialMathieuMc j (2 * n + 1) z (σ * I * h) := by
  constructor
  · have key := p1c_modMathieuM_add_pi_div_two_gen j hj₁ hj₄ (ν₀ := (((2 * n : ℕ) : ℤ) : ℂ))
      (ν₁ := (((2 * n : ℕ) : ℤ) : ℂ)) 0 (by simp) hh hσ (κ := 1) one_ne_zero
      (p1c_admissible_int _ hσ h) (fun ℓ => by
        rw [p1c_sq_sigma hσ, p1c_hsq, p1c_coeff_even_neg, add_zero, one_mul]) z
    rw [Int.cast_natCast, zpow_zero, one_mul] at key
    exact key
  · have key := p1c_modMathieuM_add_pi_div_two_gen j hj₁ hj₄
      (ν₀ := ((-((2 * n + 1 : ℕ) : ℤ) : ℤ) : ℂ)) (ν₁ := (((2 * n + 1 : ℕ) : ℤ) : ℂ))
      ((2 * n + 1 : ℕ) : ℤ) (by push_cast; ring) hh hσ (κ := -1) (by norm_num)
      (p1c_admissible_int _ hσ h) (fun ℓ => by
        rw [p1c_sq_sigma hσ, p1c_hsq, p1c_coeff_odd_neg]) z
    simp only [Int.cast_neg, Int.cast_natCast] at key
    rw [radialMathieuMs, radialMathieuMc, key, zpow_natCast, ← mul_assoc,
      p1c_neg_one_pow_mul_self, one_mul]

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
  constructor
  · have key := p1c_modMathieuM_add_pi_div_two_gen j hj₁ hj₄
      (ν₀ := (((2 * n + 1 : ℕ) : ℤ) : ℂ)) (ν₁ := ((-((2 * n + 1 : ℕ) : ℤ) : ℤ) : ℂ))
      (-((2 * n + 1 : ℕ) : ℤ)) (by push_cast; ring) hh hσ (κ := 1) one_ne_zero
      (p1c_admissible_int _ hσ h) (fun ℓ => by
        rw [p1c_sq_sigma hσ, p1c_hsq, p1c_coeff_negOdd_neg]) z
    simp only [Int.cast_neg, Int.cast_natCast] at key
    rw [radialMathieuMs, radialMathieuMc, key, zpow_neg, zpow_natCast,
      inv_eq_of_mul_eq_one_right (p1c_neg_one_pow_mul_self _)]
  · have key := p1c_modMathieuM_add_pi_div_two_gen j hj₁ hj₄
      (ν₀ := ((-((2 * n + 2 : ℕ) : ℤ) : ℤ) : ℂ)) (ν₁ := ((-((2 * n + 2 : ℕ) : ℤ) : ℤ) : ℂ))
      0 (by simp) hh hσ (κ := 1) one_ne_zero
      (p1c_admissible_int _ hσ h) (fun ℓ => by
        rw [p1c_sq_sigma hσ, p1c_hsq, p1c_coeff_negEven_neg, add_zero, one_mul]) z
    simp only [Int.cast_neg, Int.cast_natCast, zpow_zero, one_mul] at key
    rw [radialMathieuMs, radialMathieuMs, key]

/-- Shifting `z` by `c` with `e^{2c} = 1` multiplies `J_μ(h e^z)` (continued) by `e^{μc}`. -/
theorem m28c_besselJExp_add (μ h z c : ℂ) (hc : Complex.exp (2 * c) = 1) :
    besselJExp μ h (z + c) = Complex.exp (μ * c) * besselJExp μ h z := by
  have e : (h * Complex.exp (z + c)) ^ 2 = (h * Complex.exp z) ^ 2 := by
    rw [Complex.exp_add, mul_pow, mul_pow, mul_pow, ← Complex.exp_nat_mul c 2]
    push_cast; rw [hc]; ring
  rw [besselJExp, besselJExp, e, mul_add, Complex.exp_add]; ring

/-- `e^{2sπi} = 1` for `s ∈ ℤ`. -/
lemma m28c_exp_two_int_pi_I (s : ℤ) : Complex.exp (2 * (s * π * I)) = 1 := by
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

/-- Term-wise form of 28.20.25 for `M^{(2)}_ν`. -/
lemma p1c_modMathieuTerm_two_add_int_mul_pi_I {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν)
    (z h : ℂ) (s n ℓ : ℤ) :
    modMathieuTerm 2 ν (z + s * π * I) h n ℓ =
      Complex.exp (-(I * s * π * ν)) * modMathieuTerm 2 ν z h n ℓ +
        2 * I * Complex.cot (π * ν) * Complex.sin (s * π * ν) * modMathieuTerm 1 ν z h n ℓ := by
  have hk := p1c_not_int_add hν (n + ℓ)
  have hk' : ¬ ∃ j : ℤ, (ν : ℂ) + n + ℓ = j := by
    rw [show (ν : ℂ) + n + ℓ = ν + ((n + ℓ : ℤ) : ℂ) by push_cast; ring]; exact hk
  have hs := p1c_sin_ne_zero hν (n + ℓ)
  have hs0 := p1c_sin_ne_zero hν 0
  simp only [Int.cast_zero, add_zero] at hs0
  have h1 := m28c_besselJExp_add ((ℓ - n : ℤ) : ℂ) h (-z) (-(s * π * I))
    (by rw [show 2 * -((s : ℂ) * π * I) = 2 * (((-s : ℤ) : ℂ) * π * I) by push_cast; ring]
        exact m28c_exp_two_int_pi_I _)
  have h2 := m28c_besselJExp_add (ν + n + ℓ) h z (s * π * I) (m28c_exp_two_int_pi_I s)
  have h3 := m28c_besselJExp_add (-(ν + n + ℓ)) h z (s * π * I) (m28c_exp_two_int_pi_I s)
  simp only [modMathieuTerm, mathieuCylExp]
  rw [p1c_besselYExp_of_not_int hk', p1c_besselYExp_of_not_int hk',
    show -(z + s * π * I) = -z + -(s * π * I) by ring, h1, h2, h3]
  have e1 : Complex.exp (((ℓ - n : ℤ) : ℂ) * -(s * π * I)) *
      Complex.exp ((ν + n + ℓ) * (s * π * I)) = Complex.exp (I * s * π * ν) := by
    rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨s * n, by push_cast; ring⟩
  have e2 : Complex.exp (((ℓ - n : ℤ) : ℂ) * -(s * π * I)) *
      Complex.exp (-(ν + n + ℓ) * (s * π * I)) = Complex.exp (-(I * s * π * ν)) := by
    rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨-(s * ℓ), by push_cast; ring⟩
  have ecos : Complex.cos ((ν + n + ℓ) * π) =
      ((n + ℓ : ℤ).negOnePow : ℂ) * Complex.cos (ν * π) := by
    rw [show ((ν : ℂ) + n + ℓ) * π = ν * π + ((n + ℓ : ℤ) : ℂ) * π by push_cast; ring]
    exact Complex.cos_antiperiodic.add_int_mul_eq _
  have esin : Complex.sin ((ν + n + ℓ) * π) =
      ((n + ℓ : ℤ).negOnePow : ℂ) * Complex.sin (ν * π) := by
    rw [show ((ν : ℂ) + n + ℓ) * π = ν * π + ((n + ℓ : ℤ) : ℂ) * π by push_cast; ring]
    exact Complex.sin_antiperiodic.add_int_mul_eq _
  have hsin2 : 2 * I * Complex.sin (s * π * ν) =
      Complex.exp (I * s * π * ν) - Complex.exp (-(I * s * π * ν)) := by
    rw [Complex.sin]; ring_nf; rw [I_sq]; ring_nf
  have hP : (((n + ℓ : ℤ).negOnePow : ℤ) : ℂ) ^ 2 = 1 := by
    rw [← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]; simp
  rw [Complex.cot_eq_cos_div_sin, show (π : ℂ) * ν = ν * π by ring]
  push_cast at hs
  rw [esin, ecos] at *
  have hPne : (((n + ℓ : ℤ).negOnePow : ℤ) : ℂ) ≠ 0 := by intro h0; rw [h0] at hP; simp at hP
  have hs1 : Complex.sin (π * ν) ≠ 0 := by rwa [mul_comm]
  have hsin3 : 2 * I * Complex.sin (ν * π * s) =
      Complex.exp (I * s * π * ν) - Complex.exp (-(I * s * π * ν)) := by
    rw [show (ν : ℂ) * π * s = s * π * ν by ring]; exact hsin2
  generalize Complex.exp (((ℓ - n : ℤ) : ℂ) * -(s * π * I)) = A at *
  generalize Complex.exp ((ν + n + ℓ) * (s * π * I)) = B at *
  generalize Complex.exp (-(ν + n + ℓ) * (s * π * I)) = B' at *
  generalize Complex.exp (I * s * π * ν) = Ep at *
  generalize Complex.exp (-(I * s * π * ν)) = Em at *
  generalize (((n + ℓ : ℤ).negOnePow : ℤ) : ℂ) = P at *
  field_simp
  linear_combination mathieuMeCoeff ν (h ^ 2) ℓ * besselJExp ((ℓ - n : ℤ) : ℂ) h (-z) *
    besselJExp (ν + n + ℓ) h z * P * Complex.cos (ν * π) * (e1 - hsin3) -
    mathieuMeCoeff ν (h ^ 2) ℓ * besselJExp ((ℓ - n : ℤ) : ℂ) h (-z) *
      besselJExp (-(ν + n + ℓ)) h z * e2

/-- **Shift by `sπi`** of `M^{(2)}_ν` (DLMF 28.20.25, second line), `ν ∉ ℤ` real, `h > 0`:
`M^{(2)}_ν(z + sπi) = e^{-isπν} M^{(2)}_ν(z) + 2i cot(πν) sin(sπν) M^{(1)}_ν(z)`. -/
@[dlmf 28.20.E25]
theorem modMathieuM_two_add_int_mul_pi_I {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ}
    (hh : 0 < h) (z : ℂ) (s : ℤ) :
    modMathieuM 2 ν (z + s * π * I) h = Complex.exp (-(I * s * π * ν)) * modMathieuM 2 ν z h +
      2 * I * Complex.cot (π * ν) * Complex.sin (s * π * ν) * modMathieuM 1 ν z h := by
  have hadm := p1c_admissible_real hν h
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set n := modMathieuIndex ν h
  have h1 := summable_modMathieuTerm 1 le_rfl (by norm_num) hadm hh' n z
  have h2 := summable_modMathieuTerm 2 (by norm_num) (by norm_num) hadm hh' n z
  simp only [modMathieuM]
  rw [tsum_congr (p1c_modMathieuTerm_two_add_int_mul_pi_I hν z h s n),
    (h2.mul_left _).tsum_add (h1.mul_left _), tsum_mul_left, tsum_mul_left]
  ring

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
  have hadm := p1c_admissible_real hν h
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hs0 := p1c_sin_ne_zero hν 0
  simp only [Int.cast_zero, add_zero] at hs0
  have hs1 : Complex.sin (π * ν) ≠ 0 := by rwa [mul_comm]
  rw [modMathieuM_three hadm hh', modMathieuM_three hadm hh', modMathieuM_four hadm hh',
    modMathieuM_one_add_int_mul_pi_I, modMathieuM_two_add_int_mul_pi_I hν hh,
    Complex.cot_eq_cos_div_sin, show ((s : ℂ) - 1) * π * ν = s * π * ν - π * ν by ring,
    Complex.sin_sub, show -(I * s * π * ν) = I * (-(s * π * ν)) by ring,
    show I * s * π * ν = I * (s * π * ν) by ring, show -(I * π * ν) = I * (-(π * ν)) by ring,
    p1c_exp_I_mul, p1c_exp_I_mul, p1c_exp_I_mul]
  simp only [Complex.cos_neg, Complex.sin_neg]
  field_simp
  ring_nf
  rw [I_sq]
  ring

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
  have hadm := p1c_admissible_real hν h
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hs0 := p1c_sin_ne_zero hν 0
  simp only [Int.cast_zero, add_zero] at hs0
  have hs1 : Complex.sin (π * ν) ≠ 0 := by rwa [mul_comm]
  rw [modMathieuM_four hadm hh', modMathieuM_three hadm hh', modMathieuM_four hadm hh',
    modMathieuM_one_add_int_mul_pi_I, modMathieuM_two_add_int_mul_pi_I hν hh,
    Complex.cot_eq_cos_div_sin, show ((s : ℂ) + 1) * π * ν = s * π * ν + π * ν by ring,
    Complex.sin_add, show -(I * s * π * ν) = I * (-(s * π * ν)) by ring,
    show I * s * π * ν = I * (s * π * ν) by ring, show I * π * ν = I * (π * ν) by ring,
    p1c_exp_I_mul, p1c_exp_I_mul, p1c_exp_I_mul]
  simp only [Complex.cos_neg, Complex.sin_neg]
  field_simp
  ring_nf
  rw [I_sq]
  ring

end DLMF.Mathieu
