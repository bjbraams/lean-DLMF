/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import DLMFMathlib.Analysis.ODE.P2sOscillation
public import DLMF.Mathieu.Properties

/-!
# Zeros of the Mathieu functions (DLMF §28.9)

For real `q`, each of `ce_{2n}`, `se_{2n+1}`, `ce_{2n+1}`, `se_{2n+2}` has exactly `n` zeros in
`0 < z < π/2`, depending continuously on `q`; as `q → ∞` they approach the zeros of
`He_{2n}(q^{1/4}(π - 2z))` (resp. `He_{2n+1}`). For `q > 0` there are also purely imaginary
zeros, and none in the strip `|ℜz| < π/2` off the two axes.

DLMF's further remark that the purely imaginary zeros "correspond uniquely" to those of
`J_m(2√q cos z)` and are "asymptotically equal as `q → 0` and `|ℑz| → ∞`" is too imprecise to
be stated faithfully and is not acquired; the existence of infinitely many purely imaginary
zeros is.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Mathieu

/-- **Number of zeros** (DLMF §28.9): for real `q`, `ce_{2n}(·, q)`, `se_{2n+1}(·, q)`,
`ce_{2n+1}(·, q)` and `se_{2n+2}(·, q)` each have exactly `n` zeros in `(0, π/2)`. -/
@[dlmf 28.9]
theorem mathieu_zeros_count (n : ℕ) (q : ℝ) :
    {x ∈ Ioo 0 (π / 2) | mathieuCe (2 * n) x q = 0}.encard = n ∧
      {x ∈ Ioo 0 (π / 2) | mathieuSe (2 * n + 1) x q = 0}.encard = n ∧
      {x ∈ Ioo 0 (π / 2) | mathieuCe (2 * n + 1) x q = 0}.encard = n ∧
      {x ∈ Ioo 0 (π / 2) | mathieuSe (2 * n + 2) x q = 0}.encard = n := by
  have hce : ∀ m (x : ℝ), mathieuCe m x q = 0 ↔ mathieuWI (mathieuA m q) q x = 0 := by
    intro m x; simp [mathieuCe, (mathieuCeZero_pos m q).ne']
  have hse : ∀ m (x : ℝ), mathieuSe m x q = 0 ↔ mathieuWII (mathieuB m q) q x = 0 := by
    intro m x; simp [mathieuSe, (mathieuSeDerivZero_pos m q).ne']
  have e1 := p2s_zeros_A (2 * n) q
  have e2 := p2s_zeros_B (n := 2 * n + 1) (by omega) q
  have e3 := p2s_zeros_A (2 * n + 1) q
  have e4 := p2s_zeros_B (n := 2 * n + 2) (by omega) q
  rw [show 2 * n / 2 = n by omega] at e1
  rw [show (2 * n + 1 - 1) / 2 = n by omega] at e2
  rw [show (2 * n + 1) / 2 = n by omega] at e3
  rw [show (2 * n + 2 - 1) / 2 = n by omega] at e4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e1]; congr 1; ext x; exact and_congr_right fun _ => hce _ x
  · rw [← e2]; congr 1; ext x; exact and_congr_right fun _ => hse _ x
  · rw [← e3]; congr 1; ext x; exact and_congr_right fun _ => hce _ x
  · rw [← e4]; congr 1; ext x; exact and_congr_right fun _ => hse _ x

/-- **Continuity of the zeros** (DLMF §28.9): the zeros of `ce_{2n}(·, q)` in `(0, π/2)` are
`n` continuous functions of real `q`. -/
@[dlmf 28.9]
theorem mathieuCe_even_zeros_continuous (n : ℕ) :
    ∃ Z : Fin n → ℝ → ℝ, (∀ k, Continuous (Z k)) ∧
      ∀ q, {x ∈ Ioo 0 (π / 2) | mathieuCe (2 * n) x q = 0} = Set.range fun k => Z k q := by
  sorry

/-- **Continuity of the zeros** (DLMF §28.9) of `se_{2n+1}(·, q)` in `(0, π/2)`. -/
@[dlmf 28.9]
theorem mathieuSe_odd_zeros_continuous (n : ℕ) :
    ∃ Z : Fin n → ℝ → ℝ, (∀ k, Continuous (Z k)) ∧
      ∀ q, {x ∈ Ioo 0 (π / 2) | mathieuSe (2 * n + 1) x q = 0} = Set.range fun k => Z k q := by
  sorry

/-- **Continuity of the zeros** (DLMF §28.9) of `ce_{2n+1}(·, q)` in `(0, π/2)`. -/
@[dlmf 28.9]
theorem mathieuCe_odd_zeros_continuous (n : ℕ) :
    ∃ Z : Fin n → ℝ → ℝ, (∀ k, Continuous (Z k)) ∧
      ∀ q, {x ∈ Ioo 0 (π / 2) | mathieuCe (2 * n + 1) x q = 0} = Set.range fun k => Z k q := by
  sorry

/-- **Continuity of the zeros** (DLMF §28.9) of `se_{2n+2}(·, q)` in `(0, π/2)`. -/
@[dlmf 28.9]
theorem mathieuSe_even_zeros_continuous (n : ℕ) :
    ∃ Z : Fin n → ℝ → ℝ, (∀ k, Continuous (Z k)) ∧
      ∀ q, {x ∈ Ioo 0 (π / 2) | mathieuSe (2 * n + 2) x q = 0} = Set.range fun k => Z k q := by
  sorry

/-- **Zeros for large `q`** (DLMF §28.9): as `q → ∞`, the zeros of `ce_{2n}(·, q)` and
`se_{2n+1}(·, q)` in `(0, π/2)` approach those of `He_{2n}(q^{1/4}(π - 2z))`: for every
positive zero `t` of `He_{2n}` there are zeros `z(q)` with `q^{1/4}(π - 2z(q)) → t`. -/
@[dlmf 28.9]
theorem mathieu_zeros_large_q_even (n : ℕ) {t : ℝ} (ht : 0 < t)
    (hHe : Polynomial.aeval t (Polynomial.hermite (2 * n)) = 0) :
    (∃ Z : ℝ → ℝ, (∀ᶠ q in atTop, Z q ∈ Ioo 0 (π / 2) ∧ mathieuCe (2 * n) (Z q) q = 0) ∧
      Tendsto (fun q => q ^ (1 / 4 : ℝ) * (π - 2 * Z q)) atTop (𝓝 t)) ∧
    (∃ Z : ℝ → ℝ, (∀ᶠ q in atTop, Z q ∈ Ioo 0 (π / 2) ∧ mathieuSe (2 * n + 1) (Z q) q = 0) ∧
      Tendsto (fun q => q ^ (1 / 4 : ℝ) * (π - 2 * Z q)) atTop (𝓝 t)) := by
  sorry

/-- **Zeros for large `q`** (DLMF §28.9): the zeros of `ce_{2n+1}(·, q)` and `se_{2n+2}(·, q)`
in `(0, π/2)` approach those of `He_{2n+1}(q^{1/4}(π - 2z))`. -/
@[dlmf 28.9]
theorem mathieu_zeros_large_q_odd (n : ℕ) {t : ℝ} (ht : 0 < t)
    (hHe : Polynomial.aeval t (Polynomial.hermite (2 * n + 1)) = 0) :
    (∃ Z : ℝ → ℝ, (∀ᶠ q in atTop, Z q ∈ Ioo 0 (π / 2) ∧ mathieuCe (2 * n + 1) (Z q) q = 0) ∧
      Tendsto (fun q => q ^ (1 / 4 : ℝ) * (π - 2 * Z q)) atTop (𝓝 t)) ∧
    (∃ Z : ℝ → ℝ, (∀ᶠ q in atTop, Z q ∈ Ioo 0 (π / 2) ∧ mathieuSe (2 * n + 2) (Z q) q = 0) ∧
      Tendsto (fun q => q ^ (1 / 4 : ℝ) * (π - 2 * Z q)) atTop (𝓝 t)) := by
  sorry

/-- Along the imaginary axis a solution of Mathieu's equation solves the modified equation:
`f(y) = c w(iy)` has `f'(y) = i c w'(iy)` and `f'' = -(2q cosh 2y - a) f`. -/
lemma p2s_hasDerivAt_imag {a q : ℂ} {w : ℂ → ℂ} (h : IsMathieuSolution a q w) (c : ℂ)
    (y : ℝ) :
    HasDerivAt (fun y : ℝ => c * w (y * I)) (c * (I * deriv w (y * I))) y ∧
      HasDerivAt (fun y : ℝ => c * (I * deriv w (y * I)))
        (-(2 * q * Complex.cosh (2 * y) - a) * (c * w (y * I))) y := by
  have hI : HasDerivAt (fun y : ℝ => (y : ℂ) * I) I y := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
  refine ⟨?_, ?_⟩
  · have := ((h.differentiable (y * I)).hasDerivAt.comp y hI).const_mul c
    exact this.congr_deriv (by ring)
  · have := (((h.hasDerivAt_deriv (y * I)).comp y hI).const_mul I).const_mul c
    refine this.congr_deriv ?_
    rw [show 2 * ((y : ℂ) * I) = (2 * y) * I by ring, Complex.cos_mul_I]
    have : I * I = -1 := Complex.I_mul_I
    linear_combination (c * (2 * q * Complex.cosh (2 * y) - a) * w (y * I)) * this

/-- For real `a`, `q`, a solution with `f = c w(i·)` real data at `0` (`f(0)`, `f'(0)` real) is
real on `ℝ` and has infinitely many positive zeros when `q > 0`. -/
lemma p2s_infinite_imag_zeros {a q : ℝ} (hq : 0 < q) {w : ℂ → ℂ}
    (h : IsMathieuSolution a q w) (c : ℂ) (h0 : (starRingEnd ℂ) (c * w 0) = c * w 0)
    (h1 : (starRingEnd ℂ) (c * (I * deriv w 0)) = c * (I * deriv w 0)) :
    {y : ℝ | 0 < y ∧ c * w (y * I) = 0}.Infinite := by
  set P : ℝ → ℝ := fun y => 2 * q * Real.cosh (2 * y) - a
  have hPc : ∀ y : ℝ, (2 * (q : ℂ) * Complex.cosh (2 * y) - a) = ((P y : ℝ) : ℂ) := by
    intro y; simp only [P]; push_cast; rfl
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => c * w (y * I)) (c * (I * deriv w (y * I))) y ∧
      HasDerivAt (fun y : ℝ => c * (I * deriv w (y * I))) (((-P y : ℝ) : ℂ) * (c * w (y * I))) y :=
    fun y => by
      obtain ⟨k1, k2⟩ := p2s_hasDerivAt_imag h c y
      refine ⟨k1, k2.congr_deriv ?_⟩
      rw [hPc]; push_cast; ring
  have hPcont : Continuous fun y => -P y := by simp only [P]; fun_prop
  have hreal := ODE.p2s_conj_eq_of_linear_ode hPcont hd (t₀ := 0) (by simpa using h0)
    (by simpa using h1)
  have hre : ∀ y : ℝ, c * w (y * I) = ((c * w (y * I)).re : ℂ) := fun y =>
    (Complex.conj_eq_iff_re.mp (hreal y).1).symm
  have hv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => (c * w (y * I)).re)
      (c * (I * deriv w (y * I))).re y := fun y =>
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hd y).1
  have hv' : ∀ y : ℝ, HasDerivAt (fun y : ℝ => (c * (I * deriv w (y * I))).re)
      (-(P y * (c * w (y * I)).re)) y := fun y => by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hd y).2
    simp only [Complex.reCLM_apply, Complex.re_ofReal_mul] at this
    exact this.congr_deriv (by ring)
  have hPt : Tendsto P atTop atTop := by
    have h2 : Tendsto (fun y : ℝ => q * Real.exp (2 * y) - a) atTop atTop :=
      tendsto_atTop_add_const_right _ _ ((Real.tendsto_exp_atTop.comp
        (tendsto_id.const_mul_atTop' two_pos)).const_mul_atTop hq)
    refine tendsto_atTop_mono (fun y => ?_) h2
    simp only [P, Real.cosh_eq]
    nlinarith [Real.exp_pos (-(2 * y))]
  refine (ODE.p2s_infinite_zeros_of_tendsto_atTop hPt hv hv').mono ?_
  intro y hy
  exact ⟨hy.1, by rw [hre y, hy.2, Complex.ofReal_zero]⟩

/-- **Purely imaginary zeros** (DLMF §28.9): for `q > 0`, `ce_m(·, q)` and `se_m(·, q)`
(`m ≥ 1` for `se`) have infinitely many purely imaginary zeros. Proved: on the imaginary axis
they solve `v'' + (2q cosh 2y - a) v = 0` with real data, and the coefficient tends to `+∞`
(Sturm comparison, `ODE.p2s_infinite_zeros_of_tendsto_atTop`). -/
@[dlmf 28.9]
theorem mathieu_imaginary_zeros (m : ℕ) {q : ℝ} (hq : 0 < q) :
    {y : ℝ | 0 < y ∧ mathieuCe m (y * I) q = 0}.Infinite ∧
      (m ≠ 0 → {y : ℝ | 0 < y ∧ mathieuSe m (y * I) q = 0}.Infinite) := by
  refine ⟨?_, fun _ => ?_⟩
  · obtain ⟨hs, h0, h1⟩ := mathieuWI_spec (mathieuA m q) q
    exact p2s_infinite_imag_zeros hq hs (mathieuCeZero m q) (by simp [h0, Complex.conj_ofReal])
      (by simp [h1])
  · obtain ⟨hs, h0, h1⟩ := mathieuWII_spec (mathieuB m q) q
    set d : ℂ := (mathieuSeDerivZero m q : ℂ)
    have hinf := p2s_infinite_imag_zeros hq hs (d * -I) (by simp [h0])
      (by rw [h1, show d * -I * (I * 1) = d by linear_combination (-d) * Complex.I_sq]
          simp [d, Complex.conj_ofReal])
    refine hinf.mono ?_
    intro y hy
    refine ⟨hy.1, ?_⟩
    show d * mathieuWII (mathieuB m q) q (y * I) = 0
    linear_combination I * hy.2 + d * mathieuWII (mathieuB m q) q (y * I) * Complex.I_sq


/-- **No other zeros in the strip** (DLMF §28.9): for `q > 0`, the zeros of `ce_m(·, q)` and
`se_m(·, q)` (`m ≥ 1`) in the strip `|ℜz| < π/2` lie on the real or the imaginary axis. -/
@[dlmf 28.9]
theorem mathieu_zeros_strip (m : ℕ) {q : ℝ} (hq : 0 < q) {z : ℂ} (hz : |z.re| < π / 2) :
    (mathieuCe m z q = 0 → z.re = 0 ∨ z.im = 0) ∧
      (m ≠ 0 → mathieuSe m z q = 0 → z.re = 0 ∨ z.im = 0) := by
  sorry

end DLMF.Mathieu
