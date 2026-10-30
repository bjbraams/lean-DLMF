/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.Basic.Functions

/-!
# Kernels, contours and cross-products for modified Mathieu integrals
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Topology Real Classical

namespace DLMF.Mathieu

/-! ### Kernels and paths of §28.28 -/

/-- `w = cosh z cos t cos α + sinh z sin t sin α` (DLMF 28.28.1). -/
@[dlmf 28.28.E1]
def mathieuKernelW (z t α : ℂ) : ℂ :=
  Complex.cosh z * Complex.cos t * Complex.cos α + Complex.sinh z * Complex.sin t * Complex.sin α

/-- The integral along the path `𝓛_j` of DLMF 28.28.6, realized as a polygonal path with
vertical rays: `𝓛_1` from `-η₁ + i∞` down to `-η₁`, along `[-η₁, 2π - η₁]` and up to
`2π - η₁ + i∞`; `𝓛_3` from `-η₁ + i∞` down to `-η₁`, along `[-η₁, η₂]` and down to
`η₂ - i∞`; `𝓛_4` from `η₂ - i∞` up to `η₂`, along `[η₂, 2π - η₁]` and up to
`2π - η₁ + i∞`. Junk `0` for other `j`. -/
@[dlmf 28.28.E6]
def mathieuPathIntegral (j : ℕ) (η₁ η₂ : ℝ) (f : ℂ → ℂ) : ℂ :=
  match j with
  | 1 => -I * (∫ s in Ioi (0 : ℝ), f (-η₁ + I * s)) +
      (∫ x in (-η₁)..(2 * π - η₁), f x) + I * ∫ s in Ioi (0 : ℝ), f (2 * π - η₁ + I * s)
  | 3 => -I * (∫ s in Ioi (0 : ℝ), f (-η₁ + I * s)) +
      (∫ x in (-η₁)..η₂, f x) - I * ∫ s in Ioi (0 : ℝ), f (η₂ - I * s)
  | 4 => I * (∫ s in Ioi (0 : ℝ), f (η₂ - I * s)) +
      (∫ x in η₂..(2 * π - η₁), f x) + I * ∫ s in Ioi (0 : ℝ), f (2 * π - η₁ + I * s)
  | _ => 0

/-- `log (2R(z, t) e^{-z}) = ½ (log(1 + e^{-2(z - it)}) + log(1 + e^{-2(z + it)}))`, analytic
for `Re z > 0` (principal logarithms of numbers with positive real part). -/
def mathieuKernelLogR (z t : ℂ) : ℂ :=
  (Complex.log (1 + Complex.exp (-2 * (z - I * t))) +
    Complex.log (1 + Complex.exp (-2 * (z + I * t)))) / 2

/-- `R(z, t)` of DLMF 28.28.18: the analytic function on `Re z > 0` (real `t`) with
`R² = ½(cosh 2z + cos 2t)` and `R(z, 0) = cosh z`, written as `R = e^{z + log(2R e^{-z})} / 2`. -/
@[dlmf 28.28.E18]
def mathieuKernelR (z t : ℂ) : ℂ :=
  Complex.exp (z + mathieuKernelLogR z t) / 2

/-- `φ(z, t)` of DLMF 28.28.19: the analytic function on `Re z > 0` (real `t`) with
`e^{2iφ} = cosh(z + it) / cosh(z - it)` and `φ(z, 0) = 0`:
`φ = t + (log(1 + e^{-2(z+it)}) - log(1 + e^{-2(z-it)})) / (2i)`. -/
@[dlmf 28.28.E19]
def mathieuKernelPhi (z t : ℂ) : ℂ :=
  t + (Complex.log (1 + Complex.exp (-2 * (z + I * t))) -
    Complex.log (1 + Complex.exp (-2 * (z - I * t)))) / (2 * I)

/-- `𝒞^{(j)}_μ(2hR(z, t))` continued analytically from real `z > 0` through `Re z > 0`
(DLMF 28.28.17): `𝒞^{(j)}_μ(h e^{z'})` with `z' = z + log(2R e^{-z})`. -/
def mathieuCylR (j : ℕ) (μ h z t : ℂ) : ℂ :=
  mathieuCylExp j μ h (z + mathieuKernelLogR z t)

/-! ### Cross-products and integrals of §28.28(iii)–(iv) -/

/-- `D_0(ν, μ, z) = M^{(3)}_ν(z) M^{(4)}_μ(z) - M^{(4)}_ν(z) M^{(3)}_μ(z)` (DLMF 28.28.24). -/
@[dlmf 28.28.E24]
def modMathieuD0 (ν μ z h : ℂ) : ℂ :=
  modMathieuM 3 ν z h * modMathieuM 4 μ z h - modMathieuM 4 ν z h * modMathieuM 3 μ z h

/-- `D_1(ν, μ, z) = M^{(3)'}_ν(z) M^{(4)}_μ(z) - M^{(4)'}_ν(z) M^{(3)}_μ(z)` (DLMF 28.28.24). -/
@[dlmf 28.28.E24]
def modMathieuD1 (ν μ z h : ℂ) : ℂ :=
  deriv (fun z => modMathieuM 3 ν z h) z * modMathieuM 4 μ z h -
    deriv (fun z => modMathieuM 4 ν z h) z * modMathieuM 3 μ z h

/-- `α^{(0)}_{ν,m} = (2π)⁻¹ ∫₀^{2π} cos t me_ν(t, h²) me_{-ν-2m-1}(t, h²) dt`
(DLMF 28.28.27, first equality). -/
@[dlmf 28.28.E27]
def mathieuAlpha0 (ν : ℂ) (m : ℤ) (h : ℂ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
    Complex.cos t * mathieuMe ν t (h ^ 2) * mathieuMe (-ν - 2 * m - 1) t (h ^ 2)

/-- `α^{(1)}_{ν,m} = (2π)⁻¹ ∫₀^{2π} sin t me_ν(t, h²) me_{-ν-2m-1}(t, h²) dt`
(DLMF 28.28.28, first equality). -/
@[dlmf 28.28.E28]
def mathieuAlpha1 (ν : ℂ) (m : ℤ) (h : ℂ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
    Complex.sin t * mathieuMe ν t (h ^ 2) * mathieuMe (-ν - 2 * m - 1) t (h ^ 2)

/-- `γ_{ν,m} = (2π)⁻¹ ∫₀^{2π} me'_ν(t, h²) me_{-ν-2m}(t, h²) dt` (DLMF 28.28.33, first
equality). -/
@[dlmf 28.28.E33]
def mathieuGammaInt (ν : ℂ) (m : ℤ) (h : ℂ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
    deriv (fun x => mathieuMe ν x (h ^ 2)) t * mathieuMe (-ν - 2 * m) t (h ^ 2)

/-- `Ds_0(n, m, z) = Ms^{(3)}_n Ms^{(4)}_m - Ms^{(4)}_n Ms^{(3)}_m` (DLMF 28.28.35). -/
@[dlmf 28.28.E35]
def radialMathieuDs0 (n m : ℕ) (z h : ℂ) : ℂ :=
  radialMathieuMs 3 n z h * radialMathieuMs 4 m z h -
    radialMathieuMs 4 n z h * radialMathieuMs 3 m z h

/-- `Ds_1(n, m, z) = Ms^{(3)'}_n Ms^{(4)}_m - Ms^{(4)'}_n Ms^{(3)}_m` (DLMF 28.28.35). -/
@[dlmf 28.28.E35]
def radialMathieuDs1 (n m : ℕ) (z h : ℂ) : ℂ :=
  deriv (fun z => radialMathieuMs 3 n z h) z * radialMathieuMs 4 m z h -
    deriv (fun z => radialMathieuMs 4 n z h) z * radialMathieuMs 3 m z h

/-- `Ds_2(n, m, z) = Ms^{(3)'}_n Ms^{(4)'}_m - Ms^{(4)'}_n Ms^{(3)'}_m` (DLMF 28.28.35). -/
@[dlmf 28.28.E35]
def radialMathieuDs2 (n m : ℕ) (z h : ℂ) : ℂ :=
  deriv (fun z => radialMathieuMs 3 n z h) z * deriv (fun z => radialMathieuMs 4 m z h) z -
    deriv (fun z => radialMathieuMs 4 n z h) z * deriv (fun z => radialMathieuMs 3 m z h) z

/-- `Dc_0(n, m, z) = Mc^{(3)}_n Mc^{(4)}_m - Mc^{(4)}_n Mc^{(3)}_m` (DLMF 28.28.39). -/
@[dlmf 28.28.E39]
def radialMathieuDc0 (n m : ℕ) (z h : ℂ) : ℂ :=
  radialMathieuMc 3 n z h * radialMathieuMc 4 m z h -
    radialMathieuMc 4 n z h * radialMathieuMc 3 m z h

/-- `Dc_1(n, m, z) = Mc^{(3)'}_n Mc^{(4)}_m - Mc^{(4)'}_n Mc^{(3)}_m` (DLMF 28.28.39). -/
@[dlmf 28.28.E39]
def radialMathieuDc1 (n m : ℕ) (z h : ℂ) : ℂ :=
  deriv (fun z => radialMathieuMc 3 n z h) z * radialMathieuMc 4 m z h -
    deriv (fun z => radialMathieuMc 4 n z h) z * radialMathieuMc 3 m z h

/-- `Dsc_0(n, m, z) = Ms^{(3)}_n Mc^{(4)}_m - Ms^{(4)}_n Mc^{(3)}_m` (DLMF 28.28.40). -/
@[dlmf 28.28.E40]
def radialMathieuDsc0 (n m : ℕ) (z h : ℂ) : ℂ :=
  radialMathieuMs 3 n z h * radialMathieuMc 4 m z h -
    radialMathieuMs 4 n z h * radialMathieuMc 3 m z h

/-- `Dsc_1(n, m, z) = Ms^{(3)'}_n Mc^{(4)}_m - Ms^{(4)'}_n Mc^{(3)}_m` (DLMF 28.28.40). -/
@[dlmf 28.28.E40]
def radialMathieuDsc1 (n m : ℕ) (z h : ℂ) : ℂ :=
  deriv (fun z => radialMathieuMs 3 n z h) z * radialMathieuMc 4 m z h -
    deriv (fun z => radialMathieuMs 4 n z h) z * radialMathieuMc 3 m z h

/-- `α̂^{(s)}_{n,m} = (2π)⁻¹ ∫₀^{2π} cos t se_n(t, h²) se_m(t, h²) dt` (DLMF 28.28.38, first
equality), real `h`. -/
@[dlmf 28.28.E38]
def mathieuAlphaHatS (n m : ℕ) (h : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
    Complex.cos t * mathieuSe n t (h ^ 2) * mathieuSe m t (h ^ 2)

/-- `β̂_{n,m} = (2π)⁻¹ ∫₀^{2π} sin t se_n(t, h²) ce_m(t, h²) dt` (DLMF 28.28.43, first
equality), real `h`. -/
@[dlmf 28.28.E43]
def mathieuBetaHat (n m : ℕ) (h : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
    Complex.sin t * mathieuSe n t (h ^ 2) * mathieuCe m t (h ^ 2)

/-- `γ̂_{n,m} = (2π)⁻¹ ∫₀^{2π} se'_n(t, h²) ce_m(t, h²) dt` (DLMF 28.28.46, first equality),
real `h`. -/
@[dlmf 28.28.E46]
def mathieuGammaHat (n m : ℕ) (h : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
    deriv (fun x => mathieuSe n x (h ^ 2)) t * mathieuCe m t (h ^ 2)

/-- `α̂^{(c)}_{n,m} = (2π)⁻¹ ∫₀^{2π} cos t ce_n(t, h²) ce_m(t, h²) dt` (DLMF 28.28.49, first
equality), real `h`. -/
@[dlmf 28.28.E49]
def mathieuAlphaHatC (n m : ℕ) (h : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
    Complex.cos t * mathieuCe n t (h ^ 2) * mathieuCe m t (h ^ 2)

/-- The **valley conditions** for the paths `𝓛_j` (DLMF 28.28.6, made explicit): with
`C₊ = cosh(z + iα)`, `C₋ = cosh(z - iα)` the integrand `e^{2ihw} me_ν(t)` decays
double-exponentially on the upper rays `Re t = -η₁` (and `2π - η₁`) when
`arg(C₊ + i) - π < -η₁ < arg(C₊ - i)`, and on the lower ray `Re t = η₂` when
`-arg(C₋ - i) < η₂ < π - arg(C₋ + i)` (`h > 0`; principal arguments). DLMF only says
"`η₁`, `η₂` real constants"; the formulas fail for other choices (the rays must lie in
these valleys, and shifting `η₂` by `2π` changes the value). -/
def MathieuPathValley (z α : ℂ) (η₁ η₂ : ℝ) : Prop :=
  (Complex.arg (Complex.cosh (z + I * α) + I) - π < -η₁ ∧
      -η₁ < Complex.arg (Complex.cosh (z + I * α) - I)) ∧
    (-Complex.arg (Complex.cosh (z - I * α) - I) < η₂ ∧
      η₂ < π - Complex.arg (Complex.cosh (z - I * α) + I))

/-- The common denominator `sinh² z + sin² t` of §28.28(iii)–(iv). -/
abbrev m28c_den (z : ℂ) (t : ℝ) : ℂ := Complex.sinh z ^ 2 + Complex.sin t ^ 2

end DLMF.Mathieu
