/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.Connection

/-!
# Modified Mathieu functions: integrals and integral equations (DLMF §28.28)

* §28.28(i): integral equations with the kernel `e^{2ihw}` (28.28.1–28.28.9, along the paths
  `𝓛_j` of 28.28.6 realized as polygonal paths with vertical rays), Laplace-type integrals over
  `(0, ∞)` (28.28.10–28.28.14) and the cosine and sine transforms 28.28.15–28.28.16.
* §28.28(ii): integrals of products with Bessel functions (28.28.17–28.28.23), with the analytic
  functions `R(z, t)`, `φ(z, t)` of 28.28.18–28.28.19 (their characterizing identities are
  proved).
* §28.28(iii)–(iv): integrals of products of Mathieu functions, in terms of cross-products of
  `M^{(3)}`, `M^{(4)}` (28.28.24–28.28.49).

## Corrections to DLMF

* **28.28.11**: the factor `e^{iνπ}` must be `e^{iνπ/2}`. Numerically (`h = 1.2`,
  `z = 1 + i`): the ratio of the integral to `½πi ce_ν(0, h²) M^{(3)}_ν(z, h)` is
  `0.8910065 + 0.4539905i = e^{0.15πi}` for `ν = 0.3`, `e^{πi/4}` for `ν = 0.5` and `i` for
  `ν = 1` (agreement to `10⁻¹²`), not `e^{iνπ}`. The neighbouring formulas 28.28.12–28.28.14
  (`e^{iνπ/2}`, `i^m`, `i^{m+1}`) are confirmed numerically, and 28.28.15–28.28.16 follow from the
  corrected 28.28.11 at `z = iy`.
* **28.28.16**: the overall sign is wrong; the correct right-hand side is
  `+π A^{2n}_0(h²) / (2 ce_{2n}(π/2, h²)) · (ce_{2n}(y, h²) ∓ 2 fe_{2n}(y, h²)/(π C_{2n}(h²)))`.
  Direct numerical integration (`h = 1.2`, `n = 0, 1`, `y = 0.6, 2.0`) gives `0.11236`,
  `-0.05205`, `1.10503`, `-1.41558` against `+0.11239`, `-0.05204`, `1.10489`, `-1.41562` for
  the corrected right-hand side (truncation error `~10⁻⁴`), and the corrected form also follows
  from the corrected 28.28.11 at `z = iy`, as does 28.28.15 (which is correct as printed).
  Moreover the lower sign belongs to `-π ≤ y ≤ 0`, not to `π ≤ y ≤ 2π` as printed: the left
  side is even in `y` and `fe_{2n}` is odd (independent check: at `y = -0.3` the lower sign
  gives `0.4211` against `0.4207`, while at `y = π + 0.3` the printed range gives `±2.05`
  against `-0.4207`).

All other formulas of this section were checked numerically (`h = 1.2`, `ν = 0.3`, small `m`,
`n`, `z = 0.7 + 0.3i` or `0.5 + 0.3i`); the path integrals 28.28.7–28.28.9 at three parameter
points with the vertical rays in the valleys described below.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory intervalIntegral
open scoped Topology Real

namespace DLMF.Mathieu

/-! ### §28.28(i) Equations with elementary kernels -/

/-- **Integral equation** (DLMF 28.28.2), real `h`, complex `z`, `α`, `n = 0, 1, …`:
`(2π)⁻¹ ∫₀^{2π} e^{2ihw} ce_n(t, h²) dt = i^n ce_n(α, h²) Mc^{(1)}_n(z, h)`,
`w = cosh z cos t cos α + sinh z sin t sin α`. -/
@[dlmf 28.28.E2]
theorem integral_exp_mathieuCe (n : ℕ) (h : ℝ) (z α : ℂ) :
    (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuCe n t (h ^ 2) =
      I ^ n * mathieuCe n α (h ^ 2) * radialMathieuMc 1 n z h := by
  sorry

/-- **Integral equation** (DLMF 28.28.3), `n = 1, 2, …`:
`(2π)⁻¹ ∫₀^{2π} e^{2ihw} se_n(t, h²) dt = i^n se_n(α, h²) Ms^{(1)}_n(z, h)`. -/
@[dlmf 28.28.E3]
theorem integral_exp_mathieuSe {n : ℕ} (hn : n ≠ 0) (h : ℝ) (z α : ℂ) :
    (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuSe n t (h ^ 2) =
      I ^ n * mathieuSe n α (h ^ 2) * radialMathieuMs 1 n z h := by
  sorry

/-- `∂w/∂α` for the kernel `w` of 28.28.1. -/
theorem p1c_hasDerivAt_mathieuKernelW (z t α : ℂ) :
    HasDerivAt (fun β => mathieuKernelW z t β)
      (-(Complex.cosh z * Complex.cos t * Complex.sin α) +
        Complex.sinh z * Complex.sin t * Complex.cos α) α := by
  have h1 := ((Complex.hasDerivAt_cos α).const_mul (Complex.cosh z * Complex.cos t)).add
    ((Complex.hasDerivAt_sin α).const_mul (Complex.sinh z * Complex.sin t))
  convert h1 using 1
  · funext β; simp [mathieuKernelW]
  · ring

/-- Differentiation in `α` under the integral sign for the kernel `e^{2ihw}`. -/
theorem p1c_hasDerivAt_integral_kernel (h : ℝ) (z : ℂ) {g : ℝ → ℂ} (hg : Continuous g)
    (α : ℂ) :
    HasDerivAt (fun β => ∫ t in (0 : ℝ)..2 * π,
        Complex.exp (2 * I * h * mathieuKernelW z t β) * g t)
      (∫ t in (0 : ℝ)..2 * π, 2 * I * h * deriv (fun β => mathieuKernelW z t β) α *
        Complex.exp (2 * I * h * mathieuKernelW z t α) * g t) α := by
  set W' : ℂ → ℝ → ℂ := fun β t => -(Complex.cosh z * Complex.cos t * Complex.sin β) +
    Complex.sinh z * Complex.sin t * Complex.cos β
  set F' : ℂ → ℝ → ℂ := fun β t => 2 * I * h * W' β t *
    Complex.exp (2 * I * h * mathieuKernelW z t β) * g t
  have hcontW : Continuous (fun p : ℂ × ℝ => mathieuKernelW z p.2 p.1) := by
    unfold mathieuKernelW; fun_prop
  have hcont : Continuous (fun p : ℂ × ℝ => F' p.1 p.2) := by
    simp only [F', W']
    have := hg.comp (continuous_snd : Continuous (fun p : ℂ × ℝ => p.2))
    fun_prop
  have hFc : ∀ β : ℂ, Continuous (fun t : ℝ =>
      Complex.exp (2 * I * h * mathieuKernelW z t β) * g t) := fun β => by
    have : Continuous (fun t : ℝ => mathieuKernelW z t β) := by unfold mathieuKernelW; fun_prop
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_closedBall α 1 |>.prod (isCompact_Icc (a := (0 : ℝ))
    (b := 2 * π))).exists_bound_of_continuousOn hcont.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := 0) (b := 2 * π)
    (F := fun β t => Complex.exp (2 * I * h * mathieuKernelW z t β) * g t) (F' := F')
    (x₀ := α) (s := Metric.closedBall α 1) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds α one_pos)
    (Eventually.of_forall fun β => (hFc β).aestronglyMeasurable)
    ((hFc α).intervalIntegrable _ _)
    ((hcont.comp (Continuous.prodMk_right α)).aestronglyMeasurable)
    (ae_of_all _ fun t ht β hβ => by
      have ht' : t ∈ Icc 0 (2 * π) := by
        rw [uIoc_of_le (by positivity)] at ht; exact ⟨ht.1.le, ht.2⟩
      exact hC (β, t) ⟨hβ, ht'⟩)
    intervalIntegrable_const
    (ae_of_all _ fun t _ β _ => by
      have := (((p1c_hasDerivAt_mathieuKernelW z t β).const_mul (2 * I * h)).cexp).mul_const (g t)
      convert this using 1
      simp only [F', W']; ring)
  convert key.2 using 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only [F', W']
  rw [(p1c_hasDerivAt_mathieuKernelW z t α).deriv]


/-- 28.28.4/28.28.5 from 28.28.2/28.28.3: differentiate in `α`. -/
theorem p1c_integral_dw_of_integral (h : ℝ) (z : ℂ) {g : ℝ → ℂ} (hg : Continuous g)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hint : ∀ β : ℂ, (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        Complex.exp (2 * I * h * mathieuKernelW z t β) * g t = f β) (α : ℂ) :
    I * h / π * ∫ t in (0 : ℝ)..2 * π, deriv (fun β => mathieuKernelW z t β) α *
        Complex.exp (2 * I * h * mathieuKernelW z t α) * g t = deriv f α := by
  have hD := p1c_hasDerivAt_integral_kernel h z hg α
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfun : (fun β => ∫ t in (0 : ℝ)..2 * π,
      Complex.exp (2 * I * h * mathieuKernelW z t β) * g t) = fun β => 2 * π * f β := by
    funext β; rw [← hint β]; field_simp
  rw [hfun] at hD
  have hD' := ((hf α).hasDerivAt.const_mul (2 * π : ℂ))
  have hu := hD.unique hD'
  have e : (∫ t in (0 : ℝ)..2 * π, 2 * I * h * deriv (fun β => mathieuKernelW z t β) α *
      Complex.exp (2 * I * h * mathieuKernelW z t α) * g t) =
      2 * I * h * ∫ t in (0 : ℝ)..2 * π, deriv (fun β => mathieuKernelW z t β) α *
        Complex.exp (2 * I * h * mathieuKernelW z t α) * g t := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
  rw [e] at hu
  rw [div_mul_eq_mul_div, div_eq_iff hπ]
  linear_combination hu / 2

/-- **Integral equation** (DLMF 28.28.4):
`(ih/π) ∫₀^{2π} (∂w/∂α) e^{2ihw} ce_n(t, h²) dt = i^n ce'_n(α, h²) Mc^{(1)}_n(z, h)`. -/
@[dlmf 28.28.E4]
theorem integral_dw_exp_mathieuCe (n : ℕ) (h : ℝ) (z α : ℂ) :
    I * h / π * ∫ t in (0 : ℝ)..2 * π, deriv (fun β => mathieuKernelW z t β) α *
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuCe n t (h ^ 2) =
      I ^ n * deriv (fun x => mathieuCe n x (h ^ 2)) α * radialMathieuMc 1 n z h := by
  have hd := (isMathieuSolution_mathieuCe n (h ^ 2)).differentiable
  rw [p1c_integral_dw_of_integral h z (g := fun t : ℝ => mathieuCe n t (h ^ 2))
    (hd.continuous.comp continuous_ofReal)
    (f := fun β => I ^ n * mathieuCe n β (h ^ 2) * radialMathieuMc 1 n z h)
    (by fun_prop) (fun β => integral_exp_mathieuCe n h z β) α]
  rw [deriv_mul_const (by fun_prop), deriv_const_mul _ (hd α)]

/-- **Integral equation** (DLMF 28.28.5), `n ≥ 1`:
`(ih/π) ∫₀^{2π} (∂w/∂α) e^{2ihw} se_n(t, h²) dt = i^n se'_n(α, h²) Ms^{(1)}_n(z, h)`. -/
@[dlmf 28.28.E5]
theorem integral_dw_exp_mathieuSe {n : ℕ} (hn : n ≠ 0) (h : ℝ) (z α : ℂ) :
    I * h / π * ∫ t in (0 : ℝ)..2 * π, deriv (fun β => mathieuKernelW z t β) α *
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuSe n t (h ^ 2) =
      I ^ n * deriv (fun x => mathieuSe n x (h ^ 2)) α * radialMathieuMs 1 n z h := by
  have hd := (isMathieuSolution_mathieuSe n (h ^ 2)).differentiable
  rw [p1c_integral_dw_of_integral h z (g := fun t : ℝ => mathieuSe n t (h ^ 2))
    (hd.continuous.comp continuous_ofReal)
    (f := fun β => I ^ n * mathieuSe n β (h ^ 2) * radialMathieuMs 1 n z h)
    (by fun_prop) (fun β => integral_exp_mathieuSe hn h z β) α]
  rw [deriv_mul_const (by fun_prop), deriv_const_mul _ (hd α)]

/-- **Integral representation along `𝓛_j`** (DLMF 28.28.7), `j = 3, 4`, `h > 0`, `α` real,
admissible `(ν, h)`, `η₁`, `η₂` in the valleys (`MathieuPathValley`):
`π⁻¹ ∫_{𝓛_j} e^{2ihw} me_ν(t, h²) dt = e^{iνπ/2} me_ν(α, h²) M^{(j)}_ν(z, h)`. -/
@[dlmf 28.28.E7, dlmf 28.28.E6]
theorem pathIntegral_exp_mathieuMe {j : ℕ} (hj : j = 3 ∨ j = 4) {ν : ℂ} {h : ℝ} (hh : 0 < h)
    (hν : ModMathieuAdmissible ν h) (z : ℂ) (α : ℝ) {η₁ η₂ : ℝ}
    (hη : MathieuPathValley z α η₁ η₂) :
    (π : ℂ)⁻¹ * mathieuPathIntegral j η₁ η₂ (fun t =>
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuMe ν t ((h : ℂ) ^ 2)) =
      Complex.exp (I * ν * π / 2) * mathieuMe ν α ((h : ℂ) ^ 2) * modMathieuM j ν z h := by
  sorry

/-- **Integral representation along `𝓛_j`** (DLMF 28.28.8), hypotheses as for 28.28.7:
`π⁻¹ ∫_{𝓛_j} 2ih (∂w/∂α) e^{2ihw} me_ν(t, h²) dt = e^{iνπ/2} me'_ν(α, h²) M^{(j)}_ν(z, h)`. -/
@[dlmf 28.28.E8]
theorem pathIntegral_dw_exp_mathieuMe {j : ℕ} (hj : j = 3 ∨ j = 4) {ν : ℂ} {h : ℝ}
    (hh : 0 < h) (hν : ModMathieuAdmissible ν h) (z : ℂ) (α : ℝ) {η₁ η₂ : ℝ}
    (hη : MathieuPathValley z α η₁ η₂) :
    (π : ℂ)⁻¹ * mathieuPathIntegral j η₁ η₂ (fun t => 2 * I * h *
        deriv (fun β => mathieuKernelW z t β) α *
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuMe ν t ((h : ℂ) ^ 2)) =
      Complex.exp (I * ν * π / 2) * deriv (fun x => mathieuMe ν x ((h : ℂ) ^ 2)) α *
        modMathieuM j ν z h := by
  sorry

/-- **Integral representation along `𝓛_1`** (DLMF 28.28.9), `h > 0`, `α` real, admissible
`(ν, h)`, `η₁` in the upper valley (the `η₂` part of `MathieuPathValley` is not used by `𝓛_1`):
`(2π)⁻¹ ∫_{𝓛_1} e^{2ihw} me_ν(t, h²) dt = e^{iνπ/2} me_ν(α, h²) M^{(1)}_ν(z, h)`. -/
@[dlmf 28.28.E9]
theorem pathIntegral_one_exp_mathieuMe {ν : ℂ} {h : ℝ} (hh : 0 < h)
    (hν : ModMathieuAdmissible ν h) (z : ℂ) (α : ℝ) {η₁ η₂ : ℝ}
    (hη : MathieuPathValley z α η₁ η₂) :
    (2 * π : ℂ)⁻¹ * mathieuPathIntegral 1 η₁ η₂ (fun t =>
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuMe ν t ((h : ℂ) ^ 2)) =
      Complex.exp (I * ν * π / 2) * mathieuMe ν α ((h : ℂ) ^ 2) * modMathieuM 1 ν z h := by
  sorry

/-- **Laplace-type integral** (DLMF 28.28.11, **corrected**), `h > 0`, real `ν` with
`ν ≠ -1, -2, …`, `z` with `0 < ph(h(cosh z ± 1)) < π` (28.28.10):
`∫₀^∞ e^{2ih cosh z cosh t} Ce_ν(t, h²) dt = ½πi e^{iνπ/2} ce_ν(0, h²) M^{(3)}_ν(z, h)`.
DLMF prints `e^{iνπ}`; see the module docstring. -/
@[dlmf 28.28.E11, dlmf 28.28.E10]
theorem integral_exp_cosh_modMathieuCe {ν : ℝ} (hν : ∀ k : ℕ, ν ≠ -(k + 1 : ℝ)) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz₁ : 0 < ((h : ℂ) * (Complex.cosh z + 1)).im)
    (hz₂ : 0 < ((h : ℂ) * (Complex.cosh z - 1)).im) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (2 * I * h * Complex.cosh z * Real.cosh t) *
        modMathieuCe ν t ((h : ℂ) ^ 2) =
      π * I / 2 * Complex.exp (I * ν * π / 2) * modMathieuCe ν 0 ((h : ℂ) ^ 2) *
        modMathieuM 3 ν z h := by
  sorry

/-- **Laplace-type integral** (DLMF 28.28.12), `h > 0`, real `ν ≠ 0, -1, -2, …`, 28.28.10:
`∫₀^∞ e^{2ih cosh z cosh t} sinh z sinh t Se_ν(t, h²) dt =
-(π/(4h)) e^{iνπ/2} se'_ν(0, h²) M^{(3)}_ν(z, h)` (`se'_ν(0, h²) = Se'_ν(0, h²)`). -/
@[dlmf 28.28.E12, dlmf 28.28.E10]
theorem integral_exp_cosh_modMathieuSe {ν : ℝ} (hν : ∀ k : ℕ, ν ≠ -(k : ℝ)) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz₁ : 0 < ((h : ℂ) * (Complex.cosh z + 1)).im)
    (hz₂ : 0 < ((h : ℂ) * (Complex.cosh z - 1)).im) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (2 * I * h * Complex.cosh z * Real.cosh t) *
        Complex.sinh z * Real.sinh t * modMathieuSe ν t ((h : ℂ) ^ 2) =
      -(π / (4 * h)) * Complex.exp (I * ν * π / 2) *
        deriv (fun x => modMathieuSe ν x ((h : ℂ) ^ 2)) 0 * modMathieuM 3 ν z h := by
  sorry

/-- **Laplace-type integral** (DLMF 28.28.13), `h > 0`, `m = 0, 1, …`, 28.28.10:
`∫₀^∞ e^{2ih cosh z cosh t} sinh z sinh t Fe_m(t, h²) dt =
-(π/(4h)) i^m fe'_m(0, h²) Mc^{(3)}_m(z, h)`. -/
@[dlmf 28.28.E13, dlmf 28.28.E10]
theorem integral_exp_cosh_modMathieuFe (m : ℕ) {h : ℝ} (hh : 0 < h) {z : ℂ}
    (hz₁ : 0 < ((h : ℂ) * (Complex.cosh z + 1)).im)
    (hz₂ : 0 < ((h : ℂ) * (Complex.cosh z - 1)).im) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (2 * I * h * Complex.cosh z * Real.cosh t) *
        Complex.sinh z * Real.sinh t * modMathieuFe m t (h ^ 2) =
      -(π / (4 * h)) * I ^ m * deriv (fun x => mathieuFe m x (h ^ 2)) 0 *
        radialMathieuMc 3 m z h := by
  sorry

/-- **Laplace-type integral** (DLMF 28.28.14), `h > 0`, `m = 1, 2, …`, 28.28.10:
`∫₀^∞ e^{2ih cosh z cosh t} Ge_m(t, h²) dt = ½π i^{m+1} ge_m(0, h²) Ms^{(3)}_m(z, h)`. -/
@[dlmf 28.28.E14, dlmf 28.28.E10]
theorem integral_exp_cosh_modMathieuGe {m : ℕ} (hm : m ≠ 0) {h : ℝ} (hh : 0 < h) {z : ℂ}
    (hz₁ : 0 < ((h : ℂ) * (Complex.cosh z + 1)).im)
    (hz₂ : 0 < ((h : ℂ) * (Complex.cosh z - 1)).im) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (2 * I * h * Complex.cosh z * Real.cosh t) *
        modMathieuGe m t (h ^ 2) =
      π / 2 * I ^ (m + 1) * mathieuGe m 0 (h ^ 2) * radialMathieuMs 3 m z h := by
  sorry

/-- **Absolute convergence** (DLMF §28.28(i), after 28.28.14): for `h > 0` the integrals
28.28.11 and 28.28.14 converge absolutely in the half strip `Re z ≥ 0`, `0 ≤ Im z ≤ π` (stated
for each `z`; real `ν ≠ -1, -2, …`, `m ≥ 1`). -/
@[dlmf 28.28.i]
theorem integrableOn_exp_cosh_modMathieu {ν : ℝ} (hν : ∀ k : ℕ, ν ≠ -(k + 1 : ℝ)) {m : ℕ}
    (hm : m ≠ 0) {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 ≤ z.re) (hz₁ : 0 ≤ z.im)
    (hz₂ : z.im ≤ π) :
    IntegrableOn (fun t : ℝ => Complex.exp (2 * I * h * Complex.cosh z * Real.cosh t) *
        modMathieuCe ν t ((h : ℂ) ^ 2)) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => Complex.exp (2 * I * h * Complex.cosh z * Real.cosh t) *
        modMathieuGe m t (h ^ 2)) (Ioi 0) := by
  sorry

/-- **Cosine transform** (DLMF 28.28.15), `h > 0`, `n = 0, 1, …`, real `y`:
`∫₀^∞ cos(2h cos y cosh t) Ce_{2n}(t, h²) dt = (-1)^{n+1} ½π Mc^{(2)}_{2n}(0, h) ce_{2n}(y, h²)`. -/
@[dlmf 28.28.E15]
theorem integral_cos_cosh_modMathieuCe (n : ℕ) {h : ℝ} (hh : 0 < h) (y : ℝ) :
    ∫ t in Ioi (0 : ℝ), Real.cos (2 * h * Real.cos y * Real.cosh t) *
        modMathieuCe (2 * n : ℕ) t ((h ^ 2 : ℝ) : ℂ) =
      (-1 : ℂ) ^ (n + 1) * (π / 2) * radialMathieuMc 2 (2 * n) 0 h *
        mathieuCe (2 * n) y (h ^ 2) := by
  sorry

/-- **Sine transform** (DLMF 28.28.16, **corrected sign**), `h > 0`, `n = 0, 1, …`,
`-π ≤ y ≤ π`, `σ = 1` for `0 ≤ y ≤ π` and `σ = -1` for `-π ≤ y ≤ 0` (**corrected range**;
DLMF prints `π ≤ y ≤ 2π` for the lower sign):
`∫₀^∞ sin(2h cos y cosh t) Ce_{2n}(t, h²) dt = (π A^{2n}_0(h²) / (2 ce_{2n}(π/2, h²)))
(ce_{2n}(y, h²) - σ (2/(π C_{2n}(h²))) fe_{2n}(y, h²))`. DLMF prints the right-hand side with
the opposite overall sign; see the module docstring. -/
@[dlmf 28.28.E16]
theorem integral_sin_cosh_modMathieuCe (n : ℕ) {h : ℝ} (hh : 0 < h) {y : ℝ} {σ : ℂ}
    (hσ : (σ = 1 ∧ 0 ≤ y ∧ y ≤ π) ∨ (σ = -1 ∧ -π ≤ y ∧ y ≤ 0)) :
    ∫ t in Ioi (0 : ℝ), Real.sin (2 * h * Real.cos y * Real.cosh t) *
        modMathieuCe (2 * n : ℕ) t ((h ^ 2 : ℝ) : ℂ) =
      π * mathieuFourierA (2 * n) 0 (h ^ 2) / (2 * mathieuCe (2 * n) (π / 2) (h ^ 2)) *
        (mathieuCe (2 * n) y (h ^ 2) -
          σ * (2 / (π * mathieuFeC (2 * n) (h ^ 2))) * mathieuFe (2 * n) y (h ^ 2)) := by
  sorry

/-! ### §28.28(ii) Integrals of products with Bessel functions -/

/-- `1 + e^{-2w} ≠ 0` for `Re w > 0` (helper for 28.28.18–28.28.19). -/
theorem m28c_one_add_exp_ne_zero {w : ℂ} (hw : 0 < w.re) : 1 + Complex.exp (-2 * w) ≠ 0 := by
  intro h0
  have h1 : Complex.exp (-2 * w) = -1 := by linear_combination h0
  have h2 := congrArg norm h1
  rw [Complex.norm_exp] at h2
  simp at h2
  have : Real.exp (-(2 * w.re)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

/-- `R(z, t)² = ½(cosh 2z + cos 2t)` (DLMF 28.28.18), `Re z > 0`, real `t`. -/
@[dlmf 28.28.E18]
theorem mathieuKernelR_sq {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    mathieuKernelR z t ^ 2 = (Complex.cosh (2 * z) + Complex.cos (2 * t)) / 2 := by
  have hA := m28c_one_add_exp_ne_zero (w := z - I * t) (by simpa using hz)
  have hB := m28c_one_add_exp_ne_zero (w := z + I * t) (by simpa using hz)
  rw [mathieuKernelR, mathieuKernelLogR, div_pow, ← Complex.exp_nat_mul]
  have : ((2 : ℕ) : ℂ) * (z + (Complex.log (1 + Complex.exp (-2 * (z - I * t))) +
      Complex.log (1 + Complex.exp (-2 * (z + I * t)))) / 2) =
      2 * z + Complex.log (1 + Complex.exp (-2 * (z - I * t))) +
      Complex.log (1 + Complex.exp (-2 * (z + I * t))) := by push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_log hA, Complex.exp_log hB,
    Complex.cosh, Complex.cos]
  have ha := Complex.exp_ne_zero z
  have hb := Complex.exp_ne_zero (I * t)
  have e1 : Complex.exp (-2 * (z - I * t)) = Complex.exp (I * t) ^ 2 / Complex.exp z ^ 2 := by
    rw [show -2 * (z - I * t) = (I * t + I * t) - (z + z) by ring, Complex.exp_sub,
      Complex.exp_add, Complex.exp_add]; ring
  have e2 : Complex.exp (-2 * (z + I * t)) = 1 / (Complex.exp (I * t) ^ 2 * Complex.exp z ^ 2) := by
    rw [show -2 * (z + I * t) = 0 - ((I * t + I * t) + (z + z)) by ring, Complex.exp_sub,
      Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_zero]; ring
  have e3 : Complex.exp (2 * z) = Complex.exp z ^ 2 := by rw [two_mul, Complex.exp_add]; ring
  have e4 : Complex.exp (-(2 * z)) = 1 / Complex.exp z ^ 2 := by
    rw [Complex.exp_neg, e3]; ring
  have e5 : Complex.exp (2 * (t : ℂ) * I) = Complex.exp (I * t) ^ 2 := by
    rw [show 2 * (t : ℂ) * I = I * t + I * t by ring, Complex.exp_add]; ring
  have e6 : Complex.exp (-(2 * (t : ℂ)) * I) = 1 / Complex.exp (I * t) ^ 2 := by
    rw [show -(2 * (t : ℂ)) * I = 0 - (I * t + I * t) by ring, Complex.exp_sub,
      Complex.exp_add, Complex.exp_zero]; ring
  rw [e1, e2, e3, e4, e5, e6]
  field_simp
  ring

/-- `R(z, 0) = cosh z` (DLMF 28.28.18), `Re z > 0`. -/
@[dlmf 28.28.E18]
theorem mathieuKernelR_zero {z : ℂ} (hz : 0 < z.re) : mathieuKernelR z 0 = Complex.cosh z := by
  have hB := m28c_one_add_exp_ne_zero hz
  rw [mathieuKernelR, mathieuKernelLogR]
  simp only [mul_zero, sub_zero, add_zero]
  rw [show z + (Complex.log (1 + Complex.exp (-2 * z)) + Complex.log (1 + Complex.exp (-2 * z))) / 2
    = z + Complex.log (1 + Complex.exp (-2 * z)) by ring, Complex.exp_add, Complex.exp_log hB,
    Complex.cosh]
  have e : Complex.exp (-2 * z) = Complex.exp (-z) / Complex.exp z := by
    rw [show -2 * z = -z - z by ring, Complex.exp_sub]
  rw [e]
  field_simp [Complex.exp_ne_zero z]

/-- `e^{2iφ} = cosh(z + it) / cosh(z - it)` (DLMF 28.28.19), `Re z > 0`, real `t`. -/
@[dlmf 28.28.E19]
theorem exp_two_I_mathieuKernelPhi {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    Complex.exp (2 * I * mathieuKernelPhi z t) =
      Complex.cosh (z + I * t) / Complex.cosh (z - I * t) := by
  have hA := m28c_one_add_exp_ne_zero (w := z - I * t) (by simpa using hz)
  have hB := m28c_one_add_exp_ne_zero (w := z + I * t) (by simpa using hz)
  rw [mathieuKernelPhi]
  have : 2 * I * ((t : ℂ) + (Complex.log (1 + Complex.exp (-2 * (z + I * t))) -
      Complex.log (1 + Complex.exp (-2 * (z - I * t)))) / (2 * I)) =
      2 * I * t + Complex.log (1 + Complex.exp (-2 * (z + I * t))) -
      Complex.log (1 + Complex.exp (-2 * (z - I * t))) := by field_simp; ring
  rw [this, Complex.exp_sub, Complex.exp_add, Complex.exp_log hA, Complex.exp_log hB,
    Complex.cosh, Complex.cosh]
  have ha := Complex.exp_ne_zero z
  have hb := Complex.exp_ne_zero (I * t)
  have e1 : Complex.exp (-2 * (z - I * t)) = Complex.exp (I * t) ^ 2 / Complex.exp z ^ 2 := by
    rw [show -2 * (z - I * t) = (I * t + I * t) - (z + z) by ring, Complex.exp_sub,
      Complex.exp_add, Complex.exp_add]; ring
  have e2 : Complex.exp (-2 * (z + I * t)) = 1 / (Complex.exp (I * t) ^ 2 * Complex.exp z ^ 2) := by
    rw [show -2 * (z + I * t) = 0 - ((I * t + I * t) + (z + z)) by ring, Complex.exp_sub,
      Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_zero]; ring
  have e3 : Complex.exp (2 * I * t) = Complex.exp (I * t) ^ 2 := by
    rw [show 2 * I * (t : ℂ) = I * t + I * t by ring, Complex.exp_add]; ring
  rw [e1, e2, e3]
  have e4 : Complex.exp (-(z + I * t)) = 1 / (Complex.exp z * Complex.exp (I * t)) := by
    rw [Complex.exp_neg, Complex.exp_add]; ring
  have e5 : Complex.exp (-(z - I * t)) = Complex.exp (I * t) / Complex.exp z := by
    rw [Complex.exp_neg, Complex.exp_sub]; field_simp
  have e6 : Complex.exp (z - I * t) = Complex.exp z / Complex.exp (I * t) := Complex.exp_sub _ _
  rw [e4, e5, e6, Complex.exp_add]
  have hd : Complex.exp z ^ 2 + Complex.exp (I * t) ^ 2 ≠ 0 := by
    intro h0; apply hA; rw [e1]; field_simp; linear_combination h0
  field_simp

/-- `φ(z, 0) = 0` (DLMF 28.28.19). -/
@[dlmf 28.28.E19]
theorem mathieuKernelPhi_zero (z : ℂ) : mathieuKernelPhi z 0 = 0 := by
  simp [mathieuKernelPhi]

/-- **Integral of a product with a Bessel function** (DLMF 28.28.17), `j = 1, 2, 3, 4`,
`h > 0`, real `ν ∉ ℤ`, `s ∈ ℤ`, `Re z > 0`:
`π⁻¹ ∫₀^π 𝒞^{(j)}_{ν+2s}(2hR) e^{-i(ν+2s)φ} me_ν(t, h²) dt = (-1)^s c^ν_{2s}(h²) M^{(j)}_ν(z, h)`.
-/
@[dlmf 28.28.E17]
theorem integral_cyl_mathieuMe (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν : ℝ}
    (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ} (hh : 0 < h) (s : ℤ) {z : ℂ} (hz : 0 < z.re) :
    (π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..π, mathieuCylR j (ν + 2 * s) h z t *
        Complex.exp (-(I * (ν + 2 * s) * mathieuKernelPhi z t)) * mathieuMe ν t ((h : ℂ) ^ 2) =
      (-1 : ℂ) ^ s * mathieuMeCoeff ν ((h : ℂ) ^ 2) s * modMathieuM j ν z h := by
  sorry

/-- **Integer order** (DLMF 28.28.20), `j = 1, 2, 3, 4`, `h > 0`, `ℓ, m = 0, 1, …`, `Re z > 0`:
`(2/π) ∫₀^π 𝒞^{(j)}_{2ℓ}(2hR) cos(2ℓφ) ce_{2m}(t, h²) dt =
ε_ℓ (-1)^{ℓ+m} A^{2m}_{2ℓ}(h²) Mc^{(j)}_{2m}(z, h)`. -/
@[dlmf 28.28.E20]
theorem integral_cyl_mathieuCe_even (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (ℓ m : ℕ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    2 / π * ∫ t in (0 : ℝ)..π, mathieuCylR j (2 * ℓ : ℕ) h z t *
        Complex.cos (2 * ℓ * mathieuKernelPhi z t) * mathieuCe (2 * m) t (h ^ 2) =
      mathieuEpsilon ℓ * (-1 : ℂ) ^ (ℓ + m) * mathieuFourierA (2 * m) (2 * ℓ) (h ^ 2) *
        radialMathieuMc j (2 * m) z h := by
  sorry

/-- **Integer order** (DLMF 28.28.21; the `4/π ∫₀^{π/2}` form of the 1.0.11 erratum):
`(4/π) ∫₀^{π/2} 𝒞^{(j)}_{2ℓ+1}(2hR) cos((2ℓ+1)φ) ce_{2m+1}(t, h²) dt =
(-1)^{ℓ+m} A^{2m+1}_{2ℓ+1}(h²) Mc^{(j)}_{2m+1}(z, h)`. -/
@[dlmf 28.28.E21]
theorem integral_cyl_mathieuCe_odd (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (ℓ m : ℕ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    4 / π * ∫ t in (0 : ℝ)..π / 2, mathieuCylR j (2 * ℓ + 1 : ℕ) h z t *
        Complex.cos ((2 * ℓ + 1) * mathieuKernelPhi z t) * mathieuCe (2 * m + 1) t (h ^ 2) =
      (-1 : ℂ) ^ (ℓ + m) * mathieuFourierA (2 * m + 1) (2 * ℓ + 1) (h ^ 2) *
        radialMathieuMc j (2 * m + 1) z h := by
  sorry

/-- **Integer order** (DLMF 28.28.22):
`(4/π) ∫₀^{π/2} 𝒞^{(j)}_{2ℓ+1}(2hR) sin((2ℓ+1)φ) se_{2m+1}(t, h²) dt =
(-1)^{ℓ+m} B^{2m+1}_{2ℓ+1}(h²) Ms^{(j)}_{2m+1}(z, h)`. -/
@[dlmf 28.28.E22]
theorem integral_cyl_mathieuSe_odd (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (ℓ m : ℕ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    4 / π * ∫ t in (0 : ℝ)..π / 2, mathieuCylR j (2 * ℓ + 1 : ℕ) h z t *
        Complex.sin ((2 * ℓ + 1) * mathieuKernelPhi z t) * mathieuSe (2 * m + 1) t (h ^ 2) =
      (-1 : ℂ) ^ (ℓ + m) * mathieuFourierB (2 * m + 1) (2 * ℓ + 1) (h ^ 2) *
        radialMathieuMs j (2 * m + 1) z h := by
  sorry

/-- **Integer order** (DLMF 28.28.23):
`(2/π) ∫₀^π 𝒞^{(j)}_{2ℓ+2}(2hR) sin((2ℓ+2)φ) se_{2m+2}(t, h²) dt =
(-1)^{ℓ+m} B^{2m+2}_{2ℓ+2}(h²) Ms^{(j)}_{2m+2}(z, h)`. -/
@[dlmf 28.28.E23]
theorem integral_cyl_mathieuSe_even (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (ℓ m : ℕ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    2 / π * ∫ t in (0 : ℝ)..π, mathieuCylR j (2 * ℓ + 2 : ℕ) h z t *
        Complex.sin ((2 * ℓ + 2) * mathieuKernelPhi z t) * mathieuSe (2 * m + 2) t (h ^ 2) =
      (-1 : ℂ) ^ (ℓ + m) * mathieuFourierB (2 * m + 2) (2 * ℓ + 2) (h ^ 2) *
        radialMathieuMs j (2 * m + 2) z h := by
  sorry

/-! ### §28.28(iii) Products of Mathieu functions of noninteger order

Throughout: `h > 0`, real `ν ∉ ℤ`, `m ∈ ℤ`, `Re z > 0` (so that `sinh² z + sin² t ≠ 0`);
`me_ν = me_ν(·, h²)`. -/

/-- DLMF 28.28.25:
`(sinh z/π²) ∫₀^{2π} cos t me_ν(t) me_{-ν-2m-1}(t) / (sinh² z + sin² t) dt =
(-1)^{m+1} i h α^{(0)}_{ν,m} D_0(ν, ν+2m+1, z)`. -/
@[dlmf 28.28.E25]
theorem integral_cos_mathieuMe_mul {ν : ℝ} (hν : ∀ k : ℤ, (k : ℝ) ≠ ν) (m : ℤ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    Complex.sinh z / π ^ 2 * ∫ t in (0 : ℝ)..2 * π, Complex.cos t * mathieuMe ν t ((h : ℂ) ^ 2) *
        mathieuMe (-ν - 2 * m - 1) t ((h : ℂ) ^ 2) / m28c_den z t =
      (-1 : ℂ) ^ (m + 1) * I * h * mathieuAlpha0 ν m h * modMathieuD0 ν (ν + 2 * m + 1) z h := by
  sorry

/-- DLMF 28.28.26:
`(cosh z/π²) ∫₀^{2π} sin t me_ν(t) me_{-ν-2m-1}(t) / (sinh² z + sin² t) dt =
(-1)^{m+1} i h α^{(1)}_{ν,m} D_0(ν, ν+2m+1, z)`. -/
@[dlmf 28.28.E26]
theorem integral_sin_mathieuMe_mul {ν : ℝ} (hν : ∀ k : ℤ, (k : ℝ) ≠ ν) (m : ℤ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    Complex.cosh z / π ^ 2 * ∫ t in (0 : ℝ)..2 * π, Complex.sin t * mathieuMe ν t ((h : ℂ) ^ 2) *
        mathieuMe (-ν - 2 * m - 1) t ((h : ℂ) ^ 2) / m28c_den z t =
      (-1 : ℂ) ^ (m + 1) * I * h * mathieuAlpha1 ν m h * modMathieuD0 ν (ν + 2 * m + 1) z h := by
  sorry

/-- DLMF 28.28.27 (second equality), `D_0(ν, ν+2m+1, 0) ≠ 0`:
`α^{(0)}_{ν,m} = (-1)^m (2i/π) me_ν(0) me_{-ν-2m-1}(0) / (h D_0(ν, ν+2m+1, 0))`. -/
@[dlmf 28.28.E27]
theorem mathieuAlpha0_eq {ν : ℝ} (hν : ∀ k : ℤ, (k : ℝ) ≠ ν) (m : ℤ) {h : ℝ} (hh : 0 < h)
    (hD : modMathieuD0 ν (ν + 2 * m + 1) 0 h ≠ 0) :
    mathieuAlpha0 ν m h = (-1 : ℂ) ^ m * (2 * I / π) * mathieuMe ν 0 ((h : ℂ) ^ 2) *
      mathieuMe (-ν - 2 * m - 1) 0 ((h : ℂ) ^ 2) / (h * modMathieuD0 ν (ν + 2 * m + 1) 0 h) := by
  sorry

/-- DLMF 28.28.28 (second equality), `D_1(ν, ν+2m+1, 0) ≠ 0`:
`α^{(1)}_{ν,m} = (-1)^{m+1} (2i/π) me'_ν(0) me_{-ν-2m-1}(0) / (h D_1(ν, ν+2m+1, 0))`. -/
@[dlmf 28.28.E28]
theorem mathieuAlpha1_eq {ν : ℝ} (hν : ∀ k : ℤ, (k : ℝ) ≠ ν) (m : ℤ) {h : ℝ} (hh : 0 < h)
    (hD : modMathieuD1 ν (ν + 2 * m + 1) 0 h ≠ 0) :
    mathieuAlpha1 ν m h = (-1 : ℂ) ^ (m + 1) * (2 * I / π) *
      deriv (fun x => mathieuMe ν x ((h : ℂ) ^ 2)) 0 *
      mathieuMe (-ν - 2 * m - 1) 0 ((h : ℂ) ^ 2) / (h * modMathieuD1 ν (ν + 2 * m + 1) 0 h) := by
  sorry

/-- DLMF 28.28.29:
`(cosh z/π²) ∫₀^{2π} sin t me'_ν(t) me_{-ν-2m-1}(t) / (sinh² z + sin² t) dt =
(-1)^{m+1} i h α^{(0)}_{ν,m} D_1(ν, ν+2m+1, z)`. -/
@[dlmf 28.28.E29]
theorem integral_sin_deriv_mathieuMe_mul {ν : ℝ} (hν : ∀ k : ℤ, (k : ℝ) ≠ ν) (m : ℤ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    Complex.cosh z / π ^ 2 * ∫ t in (0 : ℝ)..2 * π, Complex.sin t *
        deriv (fun x => mathieuMe ν x ((h : ℂ) ^ 2)) t *
        mathieuMe (-ν - 2 * m - 1) t ((h : ℂ) ^ 2) / m28c_den z t =
      (-1 : ℂ) ^ (m + 1) * I * h * mathieuAlpha0 ν m h * modMathieuD1 ν (ν + 2 * m + 1) z h := by
  sorry

/-- DLMF 28.28.30:
`(sinh z/π²) ∫₀^{2π} cos t me'_ν(t) me_{-ν-2m-1}(t) / (sinh² z + sin² t) dt =
(-1)^m i h α^{(1)}_{ν,m} D_1(ν, ν+2m+1, z)`. -/
@[dlmf 28.28.E30]
theorem integral_cos_deriv_mathieuMe_mul {ν : ℝ} (hν : ∀ k : ℤ, (k : ℝ) ≠ ν) (m : ℤ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    Complex.sinh z / π ^ 2 * ∫ t in (0 : ℝ)..2 * π, Complex.cos t *
        deriv (fun x => mathieuMe ν x ((h : ℂ) ^ 2)) t *
        mathieuMe (-ν - 2 * m - 1) t ((h : ℂ) ^ 2) / m28c_den z t =
      (-1 : ℂ) ^ m * I * h * mathieuAlpha1 ν m h * modMathieuD1 ν (ν + 2 * m + 1) z h := by
  sorry

/-- DLMF 28.28.31:
`(2/π²) ∫₀^{2π} cos t sin t me_ν(t) me_{-ν-2m}(t) / (sinh² z + sin² t) dt =
(-1)^m i γ_{ν,m} D_0(ν, ν+2m, z)`. -/
@[dlmf 28.28.E31]
theorem integral_cos_sin_mathieuMe_mul {ν : ℝ} (hν : ∀ k : ℤ, (k : ℝ) ≠ ν) (m : ℤ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    2 / π ^ 2 * ∫ t in (0 : ℝ)..2 * π, Complex.cos t * Complex.sin t *
        mathieuMe ν t ((h : ℂ) ^ 2) * mathieuMe (-ν - 2 * m) t ((h : ℂ) ^ 2) / m28c_den z t =
      (-1 : ℂ) ^ m * I * mathieuGammaInt ν m h * modMathieuD0 ν (ν + 2 * m) z h := by
  sorry

/-- DLMF 28.28.32:
`(sinh 2z/π²) ∫₀^{2π} me'_ν(t) me_{-ν-2m}(t) / (sinh² z + sin² t) dt =
(-1)^{m+1} i γ_{ν,m} D_1(ν, ν+2m, z)`. -/
@[dlmf 28.28.E32]
theorem integral_deriv_mathieuMe_mul {ν : ℝ} (hν : ∀ k : ℤ, (k : ℝ) ≠ ν) (m : ℤ) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    Complex.sinh (2 * z) / π ^ 2 * ∫ t in (0 : ℝ)..2 * π,
        deriv (fun x => mathieuMe ν x ((h : ℂ) ^ 2)) t *
        mathieuMe (-ν - 2 * m) t ((h : ℂ) ^ 2) / m28c_den z t =
      (-1 : ℂ) ^ (m + 1) * I * mathieuGammaInt ν m h * modMathieuD1 ν (ν + 2 * m) z h := by
  sorry

/-- DLMF 28.28.33 (second equality), `D_1(ν, ν+2m, 0) ≠ 0`:
`γ_{ν,m} = (-1)^m (4i/π) me'_ν(0) me_{-ν-2m}(0) / D_1(ν, ν+2m, 0)`. -/
@[dlmf 28.28.E33]
theorem mathieuGammaInt_eq {ν : ℝ} (hν : ∀ k : ℤ, (k : ℝ) ≠ ν) (m : ℤ) {h : ℝ} (hh : 0 < h)
    (hD : modMathieuD1 ν (ν + 2 * m) 0 h ≠ 0) :
    mathieuGammaInt ν m h = (-1 : ℂ) ^ m * (4 * I / π) *
      deriv (fun x => mathieuMe ν x ((h : ℂ) ^ 2)) 0 * mathieuMe (-ν - 2 * m) 0 ((h : ℂ) ^ 2) /
        modMathieuD1 ν (ν + 2 * m) 0 h := by
  sorry

/-- DLMF 28.28.34 (Cauchy principal value at the zeros `0, π, 2π` of `sin t`; the integrand is
`2π`-periodic, so the excluded set `{|sin t| ≤ ε}` is symmetric about each singularity):
`π⁻² ⨍₀^{2π} me'_ν(t) me_{-ν-2m-1}(t) / sin t dt = (-1)^{m+1} i h α^{(0)}_{ν,m} D_1(ν, ν+2m+1,
0)`. -/
@[dlmf 28.28.E34]
theorem pv_integral_deriv_mathieuMe_div_sin {ν : ℝ} (hν : ∀ k : ℤ, (k : ℝ) ≠ ν) (m : ℤ)
    {h : ℝ} (hh : 0 < h) :
    Tendsto (fun ε : ℝ => (π : ℂ)⁻¹ ^ 2 * ∫ t in {t : ℝ | t ∈ Ioc 0 (2 * π) ∧ ε < |Real.sin t|},
        deriv (fun x => mathieuMe ν x ((h : ℂ) ^ 2)) t *
          mathieuMe (-ν - 2 * m - 1) t ((h : ℂ) ^ 2) / Real.sin t) (𝓝[>] 0)
      (𝓝 ((-1 : ℂ) ^ (m + 1) * I * h * mathieuAlpha0 ν m h *
        modMathieuD1 ν (ν + 2 * m + 1) 0 h)) := by
  sorry

/-! ### §28.28(iv) Products of Mathieu functions of integer order

Throughout: `h > 0`, `Re z > 0`, `ce_n = ce_n(·, h²)`, `se_n = se_n(·, h²)`. -/

/-- DLMF 28.28.36, `m, n ≥ 1`, `m - n = 2p + 1`:
`(sinh z/π²) ∫₀^{2π} cos t se_n(t) se_m(t) / (sinh² z + sin² t) dt =
(-1)^{p+1} i h α̂^{(s)}_{n,m} Ds_0(n, m, z)`. -/
@[dlmf 28.28.E36]
theorem integral_cos_mathieuSe_mul {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) {p : ℤ}
    (hp : (m : ℤ) - n = 2 * p + 1) {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    Complex.sinh z / π ^ 2 * ∫ t in (0 : ℝ)..2 * π, Complex.cos t * mathieuSe n t (h ^ 2) *
        mathieuSe m t (h ^ 2) / m28c_den z t =
      (-1 : ℂ) ^ (p + 1) * I * h * mathieuAlphaHatS n m h * radialMathieuDs0 n m z h := by
  sorry

/-- DLMF 28.28.37, `m, n ≥ 1`, `m - n = 2p + 1`:
`(cosh z/π²) ∫₀^{2π} sin t se'_n(t) se_m(t) / (sinh² z + sin² t) dt =
(-1)^{p+1} i h α̂^{(s)}_{n,m} Ds_1(n, m, z)`. -/
@[dlmf 28.28.E37]
theorem integral_sin_deriv_mathieuSe_mul {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) {p : ℤ}
    (hp : (m : ℤ) - n = 2 * p + 1) {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    Complex.cosh z / π ^ 2 * ∫ t in (0 : ℝ)..2 * π, Complex.sin t *
        deriv (fun x => mathieuSe n x (h ^ 2)) t * mathieuSe m t (h ^ 2) / m28c_den z t =
      (-1 : ℂ) ^ (p + 1) * I * h * mathieuAlphaHatS n m h * radialMathieuDs1 n m z h := by
  sorry

/-- DLMF 28.28.38 (second equality), `m, n ≥ 1`, `m - n = 2p + 1`, `Ds_2(n, m, 0) ≠ 0`:
`α̂^{(s)}_{n,m} = (-1)^p (2/(iπ)) se'_n(0) se'_m(0) / (h Ds_2(n, m, 0))`. -/
@[dlmf 28.28.E38]
theorem mathieuAlphaHatS_eq {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) {p : ℤ}
    (hp : (m : ℤ) - n = 2 * p + 1) {h : ℝ} (hh : 0 < h) (hD : radialMathieuDs2 n m 0 h ≠ 0) :
    mathieuAlphaHatS n m h = (-1 : ℂ) ^ p * (2 / (I * π)) *
      deriv (fun x => mathieuSe n x (h ^ 2)) 0 * deriv (fun x => mathieuSe m x (h ^ 2)) 0 /
        (h * radialMathieuDs2 n m 0 h) := by
  sorry

/-- DLMF 28.28.41, `m ≥ 0`, `n ≥ 1`, `m - n = 2p + 1`:
`(cosh z/π²) ∫₀^{2π} sin t se_n(t) ce_m(t) / (sinh² z + sin² t) dt =
(-1)^{p+1} i h β̂_{n,m} Dsc_0(n, m, z)`. -/
@[dlmf 28.28.E41]
theorem integral_sin_mathieuSe_mul_mathieuCe {n m : ℕ} (hn : n ≠ 0) {p : ℤ}
    (hp : (m : ℤ) - n = 2 * p + 1) {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    Complex.cosh z / π ^ 2 * ∫ t in (0 : ℝ)..2 * π, Complex.sin t * mathieuSe n t (h ^ 2) *
        mathieuCe m t (h ^ 2) / m28c_den z t =
      (-1 : ℂ) ^ (p + 1) * I * h * mathieuBetaHat n m h * radialMathieuDsc0 n m z h := by
  sorry

/-- DLMF 28.28.42, `m ≥ 0`, `n ≥ 1`, `m - n = 2p + 1`:
`(sinh z/π²) ∫₀^{2π} cos t se'_n(t) ce_m(t) / (sinh² z + sin² t) dt =
(-1)^p i h β̂_{n,m} Dsc_1(n, m, z)`. -/
@[dlmf 28.28.E42]
theorem integral_cos_deriv_mathieuSe_mul_mathieuCe {n m : ℕ} (hn : n ≠ 0) {p : ℤ}
    (hp : (m : ℤ) - n = 2 * p + 1) {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    Complex.sinh z / π ^ 2 * ∫ t in (0 : ℝ)..2 * π, Complex.cos t *
        deriv (fun x => mathieuSe n x (h ^ 2)) t * mathieuCe m t (h ^ 2) / m28c_den z t =
      (-1 : ℂ) ^ p * I * h * mathieuBetaHat n m h * radialMathieuDsc1 n m z h := by
  sorry

/-- DLMF 28.28.43 (second equality), `m ≥ 0`, `n ≥ 1`, `m - n = 2p + 1`,
`Dsc_1(n, m, 0) ≠ 0`: `β̂_{n,m} = (-1)^p (2/(iπ)) se'_n(0) ce_m(0) / (h Dsc_1(n, m, 0))`. -/
@[dlmf 28.28.E43]
theorem mathieuBetaHat_eq {n m : ℕ} (hn : n ≠ 0) {p : ℤ} (hp : (m : ℤ) - n = 2 * p + 1)
    {h : ℝ} (hh : 0 < h) (hD : radialMathieuDsc1 n m 0 h ≠ 0) :
    mathieuBetaHat n m h = (-1 : ℂ) ^ p * (2 / (I * π)) *
      deriv (fun x => mathieuSe n x (h ^ 2)) 0 * mathieuCe m 0 (h ^ 2) /
        (h * radialMathieuDsc1 n m 0 h) := by
  sorry

/-- DLMF 28.28.44, `m ≥ 0`, `n ≥ 1`, `n - m = 2p`:
`π⁻² ∫₀^{2π} sin 2t se_n(t) ce_m(t) / (sinh² z + sin² t) dt = (-1)^p i γ̂_{n,m} Dsc_0(n, m, z)`. -/
@[dlmf 28.28.E44]
theorem integral_sin_two_mathieuSe_mul_mathieuCe {n m : ℕ} (hn : n ≠ 0) {p : ℤ}
    (hp : (n : ℤ) - m = 2 * p) {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    (π : ℂ)⁻¹ ^ 2 * ∫ t in (0 : ℝ)..2 * π, Complex.sin (2 * t) * mathieuSe n t (h ^ 2) *
        mathieuCe m t (h ^ 2) / m28c_den z t =
      (-1 : ℂ) ^ p * I * mathieuGammaHat n m h * radialMathieuDsc0 n m z h := by
  sorry

/-- DLMF 28.28.45, `m ≥ 0`, `n ≥ 1`, `n - m = 2p`:
`(sinh 2z/π²) ∫₀^{2π} se'_n(t) ce_m(t) / (sinh² z + sin² t) dt =
(-1)^{p+1} i γ̂_{n,m} Dsc_1(n, m, z)`. -/
@[dlmf 28.28.E45]
theorem integral_deriv_mathieuSe_mul_mathieuCe {n m : ℕ} (hn : n ≠ 0) {p : ℤ}
    (hp : (n : ℤ) - m = 2 * p) {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    Complex.sinh (2 * z) / π ^ 2 * ∫ t in (0 : ℝ)..2 * π,
        deriv (fun x => mathieuSe n x (h ^ 2)) t * mathieuCe m t (h ^ 2) / m28c_den z t =
      (-1 : ℂ) ^ (p + 1) * I * mathieuGammaHat n m h * radialMathieuDsc1 n m z h := by
  sorry

/-- DLMF 28.28.46 (second equality), `m ≥ 0`, `n ≥ 1`, `n - m = 2p`, `Dsc_1(n, m, 0) ≠ 0`:
`γ̂_{n,m} = (-1)^{p+1} (4/(iπ)) se'_n(0) ce_m(0) / Dsc_1(n, m, 0)`. -/
@[dlmf 28.28.E46]
theorem mathieuGammaHat_eq {n m : ℕ} (hn : n ≠ 0) {p : ℤ} (hp : (n : ℤ) - m = 2 * p)
    {h : ℝ} (hh : 0 < h) (hD : radialMathieuDsc1 n m 0 h ≠ 0) :
    mathieuGammaHat n m h = (-1 : ℂ) ^ (p + 1) * (4 / (I * π)) *
      deriv (fun x => mathieuSe n x (h ^ 2)) 0 * mathieuCe m 0 (h ^ 2) /
        radialMathieuDsc1 n m 0 h := by
  sorry

/-- DLMF 28.28.47, `m, n ≥ 0`, `m - n = 2p + 1`:
`(sinh z/π²) ∫₀^{2π} cos t ce_n(t) ce_m(t) / (sinh² z + sin² t) dt =
(-1)^{p+1} i h α̂^{(c)}_{n,m} Dc_0(n, m, z)`. -/
@[dlmf 28.28.E47]
theorem integral_cos_mathieuCe_mul {n m : ℕ} {p : ℤ} (hp : (m : ℤ) - n = 2 * p + 1) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    Complex.sinh z / π ^ 2 * ∫ t in (0 : ℝ)..2 * π, Complex.cos t * mathieuCe n t (h ^ 2) *
        mathieuCe m t (h ^ 2) / m28c_den z t =
      (-1 : ℂ) ^ (p + 1) * I * h * mathieuAlphaHatC n m h * radialMathieuDc0 n m z h := by
  sorry

/-- DLMF 28.28.48, `m, n ≥ 0`, `m - n = 2p + 1`:
`(cosh z/π²) ∫₀^{2π} sin t ce'_n(t) ce_m(t) / (sinh² z + sin² t) dt =
(-1)^{p+1} i h α̂^{(c)}_{n,m} Dc_1(n, m, z)`. -/
@[dlmf 28.28.E48]
theorem integral_sin_deriv_mathieuCe_mul {n m : ℕ} {p : ℤ} (hp : (m : ℤ) - n = 2 * p + 1)
    {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    Complex.cosh z / π ^ 2 * ∫ t in (0 : ℝ)..2 * π, Complex.sin t *
        deriv (fun x => mathieuCe n x (h ^ 2)) t * mathieuCe m t (h ^ 2) / m28c_den z t =
      (-1 : ℂ) ^ (p + 1) * I * h * mathieuAlphaHatC n m h * radialMathieuDc1 n m z h := by
  sorry

/-- DLMF 28.28.49 (second equality), `m, n ≥ 0`, `m - n = 2p + 1`, `Dc_0(n, m, 0) ≠ 0`:
`α̂^{(c)}_{n,m} = (-1)^{p+1} (2/(iπ)) ce_n(0) ce_m(0) / (h Dc_0(n, m, 0))`. -/
@[dlmf 28.28.E49]
theorem mathieuAlphaHatC_eq {n m : ℕ} {p : ℤ} (hp : (m : ℤ) - n = 2 * p + 1) {h : ℝ}
    (hh : 0 < h) (hD : radialMathieuDc0 n m 0 h ≠ 0) :
    mathieuAlphaHatC n m h = (-1 : ℂ) ^ (p + 1) * (2 / (I * π)) * mathieuCe n 0 (h ^ 2) *
      mathieuCe m 0 (h ^ 2) / (h * radialMathieuDc0 n m 0 h) := by
  sorry

end DLMF.Mathieu
