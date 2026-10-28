/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Classical
public import DLMF.SphericalHarmonics.Basic
public import DLMF.SphericalHarmonics.ZonalTools
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Three
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.WeightedSumSquares
public import TauCeti.Analysis.PDE.PoissonIntegral.Ball

/-!
# Addition theorems, Funk–Hecke, Poisson, and `SU(2)` (AAR §§9.6–9.16)

Mathlib has the Poisson kernel of the *disk* (`poissonKernel`) and `Matrix.specialUnitaryGroup`,
but not the spherical addition theorem, Funk–Hecke, or the identification of Jacobi polynomials
with matrix coefficients of `SU(2)`.
The ball Poisson representation uses the Tau Ceti contributors’ Poisson kernel,
boundary convergence and Dirichlet uniqueness. The continuous extension argument
is adapted from their unit-ball Dirichlet theorem. The `SU(2)` double cover transports
their compact Spin cover through their Spin–unitary and coordinate equivalences.
Gegenbauer's addition theorem is proved by induction on the degree: both sides have the same
derivative in `cos ψ` (by the derivative formula and the induction hypothesis at `λ + 1`), and the
constant term is fixed by integrating against `sin^{2λ-1} ψ`, using the proved product formula
(DLMF 18.17.5) and the vanishing of the integrals of `C_j^{λ-1/2}(cos ψ)`, `j ≥ 1`.
-/

@[expose] public section

open Complex Matrix MeasureTheory intervalIntegral Metric Set Filter InnerProductSpace
open scoped Real Topology
open DLMF.OrthogonalPolynomials

noncomputable section

namespace DLMF.SphericalHarmonics

/-- AAR Theorem 9.6.3, (9.6.6), p. 456, specialized to three dimensions:
`(2k+1)/(4π) P_k(x·y) = ∑_m S_m(x) S_m(y)` for an orthonormal family of `2k+1`
real spherical harmonics of degree `k`. The inner product uses surface measure as in
(9.4.4), p. 452. -/
theorem spherical_addition {k : ℕ}
    (S : Fin (2 * k + 1) → MvPolynomial (Fin 3) ℝ)
    (hS : ∀ m, IsHarmonicHomogeneous k (S m))
    (horth : ∀ i j, sphericalHarmonicInner (S i) (S j) = if i = j then 1 else 0)
    (x y : Fin 3 → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) (hy : ∑ i, y i ^ 2 = 1) :
    (2 * k + 1 : ℂ) / (4 * π) * legendrePolyP k (∑ i, x i * y i : ℝ) =
      ∑ m : Fin (2 * k + 1),
        (MvPolynomial.eval x (S m) : ℂ) * (MvPolynomial.eval y (S m) : ℂ) := by
  exact zonal_spherical_addition S hS horth x y hx hy

/-- Funk–Hecke formula (AAR Theorem 9.7.1), in three dimensions. -/
theorem funk_hecke {k : ℕ} {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (-1) 1))
    (S : MvPolynomial (Fin 3) ℝ) (hS : IsHarmonicHomogeneous k S)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (∫ y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      f (∑ i, x.val i * y.val i) * (MvPolynomial.eval (fun i => y.val i) S : ℂ)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) =
      (2 * π : ℂ) * (∫ t : ℝ in (-1 : ℝ)..1, f t * legendrePolyP k t) *
        (MvPolynomial.eval (fun i => x.val i) S : ℂ) := by
  exact zonal_funk_hecke hf S hS x

/-- The coefficient in Gegenbauer's addition theorem (AAR (9.8.5')). -/
private noncomputable def gegAdd_coef (lam : ℝ) (n j : ℕ) : ℂ :=
  Gamma (2 * lam - 1) * 4 ^ j * (n - j).factorial *
    Gamma (j + (lam : ℂ)) ^ 2 * (2 * j + 2 * (lam : ℂ) - 1) /
      (Gamma (lam : ℂ) ^ 2 * Gamma (j + n + 2 * (lam : ℂ)))

/-- Raising the degree and the order together scales the coefficient by `2λ/(2λ-1)`. -/
private lemma gegAdd_coef_succ {lam : ℝ} (hlam : 1 / 2 < lam) (n i : ℕ) :
    gegAdd_coef lam (n + 1) (i + 1) * (2 * lam - 1) = 2 * lam * gegAdd_coef (lam + 1) n i := by
  simp only [gegAdd_coef]
  have h1 : Gamma (2 * ((lam + 1 : ℝ) : ℂ) - 1) = 2 * lam * (2 * lam - 1) * Gamma (2 * lam - 1) := by
    rw [show 2 * ((lam + 1 : ℝ) : ℂ) - 1 = (2 * lam - 1 + 1) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ (by
        intro h; have := congrArg Complex.re h; simp at this; linarith),
      Complex.Gamma_add_one _ (by
        intro h; have := congrArg Complex.re h; simp at this; linarith)]
    ring
  have h2 : Gamma ((lam + 1 : ℝ) : ℂ) = lam * Gamma lam := by
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.Gamma_add_one _ (by
      intro h; have := congrArg Complex.re h; simp at this; linarith)]
  have h3 : Gamma (((i + 1 : ℕ) : ℂ) + lam) = Gamma ((i : ℂ) + ((lam + 1 : ℝ) : ℂ)) := by
    congr 1; push_cast; ring
  have h4 : Gamma (((i + 1 : ℕ) : ℂ) + ((n + 1 : ℕ) : ℂ) + 2 * lam) =
      Gamma ((i : ℂ) + n + 2 * ((lam + 1 : ℝ) : ℂ)) := by
    congr 1; push_cast; ring
  rw [h1, h2, h3, h4, show n + 1 - (i + 1) = n - i by omega]
  have hG : Gamma (lam : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hG2 : Gamma ((i : ℂ) + n + 2 * ((lam + 1 : ℝ) : ℂ)) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; positivity)
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast (by linarith : lam ≠ 0)
  field_simp
  push_cast
  ring

/-- `Γ(k + 2λ) = (2λ)_k Γ(2λ)`. -/
private lemma gegAdd_Gamma_poch {lam : ℝ} (hlam : 0 < lam) (k : ℕ) :
    Gamma ((k : ℂ) + 2 * lam) = DLMF.Hypergeometric.poch (2 * lam) k * Gamma (2 * lam) := by
  induction k with
  | zero => simp [DLMF.Hypergeometric.poch_zero]
  | succ k ih =>
    rw [DLMF.Hypergeometric.poch_succ, show ((k + 1 : ℕ) : ℂ) + 2 * lam = ((k : ℂ) + 2 * lam) + 1 by
      push_cast; ring, Complex.Gamma_add_one _ (by
        intro h; have := congrArg Complex.re h; simp at this
        have : (0 : ℝ) ≤ k := k.cast_nonneg
        linarith), ih]
    ring

/-- The constant coefficient is the reciprocal of `C_n^λ(1)`. -/
private lemma gegAdd_coef_zero {lam : ℝ} (hlam : 1 / 2 < lam) (n : ℕ) :
    gegAdd_coef lam n 0 * ultrasphPoly lam n 1 = 1 := by
  have hlre : -1 / 2 < (lam : ℂ).re := by simp; linarith
  simp only [gegAdd_coef, Nat.cast_zero, zero_add, pow_zero, mul_one, Nat.sub_zero, mul_zero]
  rw [ultrasphPoly_at_one hlre, gegAdd_Gamma_poch (by linarith),
    show (2 * (lam : ℂ)) = (2 * lam - 1) + 1 by ring, Complex.Gamma_add_one _ (by
      intro h; have := congrArg Complex.re h; simp at this; linarith)]
  rw [show (2 * (lam : ℂ) - 1) + 1 = 2 * lam by ring]
  have hG : Gamma (lam : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hG1 : Gamma (2 * (lam : ℂ) - 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hP : DLMF.Hypergeometric.poch (2 * (lam : ℂ)) n ≠ 0 :=
    poch_ne_zero_of_re_pos (by simp; linarith) n
  have hl : (2 * lam - 1 : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- Gegenbauer polynomials are continuous. -/
private lemma gegAdd_continuous (lam : ℂ) (n : ℕ) : Continuous (ultrasphPoly lam n) :=
  continuousOn_univ.1 (analyticOnNhd_ultrasphPoly lam n).continuousOn

/-- For `λ > 1/2`, the Gegenbauer polynomials `C_{j+1}^{λ-1/2}(cos s)` integrate to zero against
`sin^{2λ-1} s` on `[0, π]`. -/
private lemma gegAdd_integral_vanish {lam : ℝ} (hlam : 1 / 2 < lam) (j : ℕ) :
    ∫ s : ℝ in (0 : ℝ)..π, ultrasphPoly ((lam : ℂ) - 1 / 2) (j + 1) (Real.cos s) *
      ((Real.sin s ^ (2 * lam - 1) : ℝ) : ℂ) = 0 := by
  set μ : ℂ := (lam : ℂ) - 1 / 2 with hμ
  have hLre : 1 / 2 < (μ + 1).re := by simp [hμ]; linarith
  have hμre : -1 / 2 < μ.re := by simp [hμ]; linarith
  have hW := fun x => ultrasphPoly_weighted_identity hLre j x
  have hsplit : ∀ x : ℝ, 0 ≤ x → x ^ (2 * lam) = x * x ^ (2 * lam - 1) := by
    intro x hx
    rcases hx.eq_or_lt with h | h
    · subst h; rw [Real.zero_rpow (by positivity), zero_mul]
    · rw [← Real.rpow_one_add' h.le (by linarith)]; ring_nf
  set κ : ℂ := (j + 1) * (j + 2 * lam) / (2 * lam - 1) with hκ
  have hκ0 : κ ≠ 0 := by
    have h1 : (j + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have h2 : (j + 2 * lam : ℂ) ≠ 0 := by
      have : (j + 2 * lam : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    have h3 : (2 * lam - 1 : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    exact div_ne_zero (mul_ne_zero h1 h2) h3
  have hD : ∀ s ∈ Ioo (0 : ℝ) π, HasDerivAt (fun s : ℝ => ((Real.sin s ^ (2 * lam) : ℝ) : ℂ) *
      ultrasphPoly (μ + 1) j (Real.cos s))
      (κ * (ultrasphPoly μ (j + 1) (Real.cos s) * ((Real.sin s ^ (2 * lam - 1) : ℝ) : ℂ))) s := by
    intro s hs
    have hst : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs.1 hs.2
    have hr := ((Real.hasDerivAt_sin s).rpow_const (p := 2 * lam) (Or.inl hst.ne')).ofReal_comp
    have hc : HasDerivAt (fun s : ℝ => ultrasphPoly (μ + 1) j (Real.cos s))
        (deriv (ultrasphPoly (μ + 1) j) (Real.cos s) * ((-Real.sin s : ℝ) : ℂ)) s :=
      ((analyticAt_ultrasphPoly _ _ _).differentiableAt.hasDerivAt).comp s
        (Real.hasDerivAt_cos s).ofReal_comp
    refine (hr.mul hc).congr_deriv ?_
    have hw := hW (Real.cos s)
    rw [show μ + 1 - 1 = μ by ring] at hw
    have htrig : (Real.sin s : ℂ) ^ 2 = 1 - (Real.cos s : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, Real.sin_sq]; push_cast; ring
    have h3 : (2 * lam - 1 : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [hκ, div_mul_eq_mul_div, eq_div_iff h3, hsplit _ hst.le]
    simp only [hμ] at hw
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
    generalize ((Real.sin s ^ (2 * lam - 1) : ℝ) : ℂ) = r
    linear_combination (-r) * hw + (-(2 * (lam : ℂ) - 1) * r *
      deriv (ultrasphPoly ((lam : ℂ) - 1 / 2 + 1) j) (Real.cos s)) * htrig
  have hρc : Continuous fun s : ℝ => ((Real.sin s ^ (2 * lam - 1) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((Real.continuous_rpow_const (by linarith)).comp
      Real.continuous_sin)
  have hCc : ∀ (ν : ℂ) (k : ℕ), Continuous fun s : ℝ => ultrasphPoly ν k (Real.cos s) :=
    fun ν k => (gegAdd_continuous ν k).comp
      (Complex.continuous_ofReal.comp Real.continuous_cos)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le
    ((Complex.continuous_ofReal.comp ((Real.continuous_rpow_const (by positivity)).comp
      Real.continuous_sin)).mul (hCc _ _)).continuousOn hD
    ((continuous_const.mul ((hCc _ _).mul hρc)).intervalIntegrable 0 π)
  simp only [Pi.mul_apply, Function.comp_apply, Real.sin_pi, Real.sin_zero,
    Real.zero_rpow (by positivity : 2 * lam ≠ 0),
    Complex.ofReal_zero, zero_mul, sub_zero, intervalIntegral.integral_const_mul] at hFTC
  exact (mul_eq_zero.1 hFTC).resolve_left hκ0

/-- The coefficient of `C_j^{λ-1/2}(cos ψ)` in Gegenbauer's addition theorem. -/
private noncomputable def gegAdd_term (lam : ℝ) (n j : ℕ) (θ φ : ℝ) : ℂ :=
  gegAdd_coef lam n j * (Real.sin θ : ℂ) ^ j * ultrasphPoly (j + (lam : ℂ)) (n - j) (Real.cos θ) *
    (Real.sin φ : ℂ) ^ j * ultrasphPoly (j + (lam : ℂ)) (n - j) (Real.cos φ)

/-- For `λ > 1/2`, the Gegenbauer addition-theorem terms satisfy `T_λ(n+1, i+1) (2λ - 1) = 2λ sin θ
sin φ T_{λ+1}(n, i)`. -/
private lemma gegAdd_term_succ {lam : ℝ} (hlam : 1 / 2 < lam) (n i : ℕ) (θ φ : ℝ) :
    gegAdd_term lam (n + 1) (i + 1) θ φ * (2 * lam - 1) =
      2 * lam * ((Real.sin θ * Real.sin φ : ℝ) : ℂ) * gegAdd_term (lam + 1) n i θ φ := by
  have hc := gegAdd_coef_succ hlam n i
  have hp : ((i + 1 : ℕ) : ℂ) + lam = (i : ℂ) + ((lam + 1 : ℝ) : ℂ) := by push_cast; ring
  simp only [gegAdd_term]
  rw [hp, show n + 1 - (i + 1) = n - i by omega, Complex.ofReal_mul, pow_succ, pow_succ]
  linear_combination (Real.sin θ : ℂ) ^ i * (Real.sin θ : ℂ) *
    ultrasphPoly ((i : ℂ) + ((lam + 1 : ℝ) : ℂ)) (n - i) (Real.cos θ) * (Real.sin φ : ℂ) ^ i *
    (Real.sin φ : ℂ) * ultrasphPoly ((i : ℂ) + ((lam + 1 : ℝ) : ℂ)) (n - i) (Real.cos φ) * hc

/-- The constant `∫₀^π sin^{2λ-1} s ds = √π Γ(λ)/Γ(λ+1/2)` is nonzero for `λ > 0`. -/
private lemma gegAdd_weight_ne_zero {lam : ℝ} (hlam0 : 0 < lam) :
    ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) ≠ 0 := by
  have hG1 : 0 < Real.Gamma (lam + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : 0 < Real.Gamma lam := Real.Gamma_pos_of_pos hlam0
  have hsq : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  exact_mod_cast (by positivity : Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) ≠ 0)

/-- Product formula in integrated form: for `λ > 1/2`,
`∫₀^π C^λ_m(cos θ cos φ + sin θ sin φ cos s) sin^{2λ-1} s ds =
√π Γ(λ)/Γ(λ+1/2) · C^λ_m(cos θ) C^λ_m(cos φ) / C^λ_m(1)` (from DLMF 18.17.5). -/
private lemma gegAdd_integral_L {lam : ℝ} (hlam : 1 / 2 < lam) (m : ℕ) (θ φ : ℝ) :
    ∫ s : ℝ in (0 : ℝ)..π,
      ultrasphPoly lam m ((Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ * Real.cos s : ℝ)) *
        ((Real.sin s ^ (2 * lam - 1) : ℝ) : ℂ) =
      ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) *
        ultrasphPoly lam m (Real.cos θ) * ultrasphPoly lam m (Real.cos φ) /
        ultrasphPoly lam m 1 := by
  have hlam0 : 0 < lam := by linarith
  have hlre : -1 / 2 < (lam : ℂ).re := by simp; linarith
  set A : ℝ := Real.cos θ * Real.cos φ with hA
  set B : ℝ := Real.sin θ * Real.sin φ with hB
  set L : ℝ → ℂ := fun t => ultrasphPoly lam m ((A + B * t : ℝ)) with hL
  set ρ : ℝ → ℂ := fun s => ((Real.sin s ^ (2 * lam - 1) : ℝ) : ℂ) with hρ
  set mC : ℂ := ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) with hmC
  show ∫ s : ℝ in (0 : ℝ)..π, L (Real.cos s) * ρ s = _
  have hG1 : 0 < Real.Gamma (lam + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : 0 < Real.Gamma lam := Real.Gamma_pos_of_pos hlam0
  have hsq : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hGG : Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) = mC⁻¹ := by
    rw [hmC, show (lam + 1 / 2 : ℂ) = ((lam + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal]
    push_cast
    field_simp
  have h1 : ultrasphPoly lam m 1 ≠ 0 := by
    rw [ultrasphPoly_at_one hlre]
    exact div_ne_zero (poch_ne_zero_of_re_pos (by simp; linarith) _)
      (by exact_mod_cast m.factorial_ne_zero)
  have hPF := ultrasphPoly_product_integral hlam0 m θ φ
  have hint : (∫ phi : ℝ in (0 : ℝ)..Real.pi, ultrasphPoly lam m
        (Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ * Real.cos phi) /
          ultrasphPoly lam m 1 * (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ)) =
      (ultrasphPoly lam m 1)⁻¹ * ∫ s : ℝ in (0 : ℝ)..π, L (Real.cos s) * ρ s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hL, hρ, hA, hB, Real.rpow_eq_pow]
    push_cast
    ring
  rw [hGG, hint] at hPF
  have hm0 : mC ≠ 0 := gegAdd_weight_ne_zero hlam0
  rw [eq_div_iff h1]
  field_simp at hPF
  linear_combination -hPF

/-- Gegenbauer's addition theorem with `cos ψ` replaced by an arbitrary real `t`. -/
private lemma gegAdd_main (n : ℕ) : ∀ lam : ℝ, 1 / 2 < lam → ∀ θ φ t : ℝ,
    ultrasphPoly lam n ((Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ * t : ℝ)) =
      ∑ j ∈ Finset.range (n + 1), gegAdd_term lam n j θ φ * ultrasphPoly ((lam : ℂ) - 1 / 2) j t := by
  induction n with
  | zero =>
    intro lam hlam θ φ t
    have h := gegAdd_coef_zero hlam 0
    simp only [ultrasphPoly_zero, mul_one] at h
    simp [gegAdd_term, ultrasphPoly_zero, h]
  | succ n ih =>
  intro lam hlam θ φ t
  set A : ℝ := Real.cos θ * Real.cos φ with hA
  set B : ℝ := Real.sin θ * Real.sin φ with hB
  set μ : ℂ := (lam : ℂ) - 1 / 2 with hμ
  have hlre : -1 / 2 < (lam : ℂ).re := by simp; linarith
  have hμre : -1 / 2 < μ.re := by simp [hμ]; linarith
  have IH := ih (lam + 1) (by linarith) θ φ
  rw [show ((lam + 1 : ℝ) : ℂ) = (lam : ℂ) + 1 by push_cast; ring,
    show (lam : ℂ) + 1 - 1 / 2 = μ + 1 by simp only [hμ]; ring] at IH
  set L : ℝ → ℂ := fun t => ultrasphPoly lam (n + 1) ((A + B * t : ℝ)) with hL
  set R : ℝ → ℂ := fun t => ∑ j ∈ Finset.range (n + 1 + 1),
    gegAdd_term lam (n + 1) j θ φ * ultrasphPoly μ j t with hR
  -- derivatives
  have hLd : ∀ t : ℝ, HasDerivAt L (2 * lam * ultrasphPoly ((lam : ℂ) + 1) n ((A + B * t : ℝ)) * B)
      t := by
    intro t
    have h1 : HasDerivAt (ultrasphPoly lam (n + 1))
        (2 * lam * ultrasphPoly ((lam : ℂ) + 1) n ((A + B * t : ℝ))) ((A + B * t : ℝ)) := by
      rw [← ultrasphPoly_derivative hlre n]
      exact (analyticAt_ultrasphPoly _ _ _).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => ((A + B * t : ℝ) : ℂ)) (B : ℂ) t := by
      have := ((hasDerivAt_id t).const_mul B).const_add A
      simpa using this.ofReal_comp
    exact HasDerivAt.comp (h₂ := ultrasphPoly (lam : ℂ) (n + 1))
      (h := fun t : ℝ => ((A + B * t : ℝ) : ℂ)) t h1 h2
  have hRd : ∀ t : ℝ, HasDerivAt R (∑ j ∈ Finset.range (n + 1 + 1),
      gegAdd_term lam (n + 1) j θ φ * deriv (ultrasphPoly μ j) t) t := by
    intro t
    refine HasDerivAt.fun_sum fun j _ => ?_
    exact ((analyticAt_ultrasphPoly _ _ _).differentiableAt.hasDerivAt.comp_ofReal).const_mul _
  have hderiv : ∀ t : ℝ, 2 * lam * ultrasphPoly ((lam : ℂ) + 1) n ((A + B * t : ℝ)) * B =
      ∑ j ∈ Finset.range (n + 1 + 1), gegAdd_term lam (n + 1) j θ φ * deriv (ultrasphPoly μ j) t := by
    intro t
    have h0 : deriv (ultrasphPoly μ 0) (t : ℂ) = 0 := by
      rw [show ultrasphPoly μ 0 = fun _ => 1 from funext fun x => ultrasphPoly_zero μ x]
      exact deriv_const _ _
    rw [Finset.sum_range_succ', h0, mul_zero, add_zero, IH t, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ultrasphPoly_derivative hμre i]
    have hts := gegAdd_term_succ hlam n i θ φ
    have h3 : (2 * lam - 1 : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [← hB] at hts
    have h2μ : 2 * μ = 2 * lam - 1 := by simp only [hμ]; ring
    rw [h2μ]
    linear_combination (-ultrasphPoly (μ + 1) i t) * hts
  -- `L - R` is constant
  have hconst : ∀ t : ℝ, L t - R t = L 0 - R 0 := by
    have hd : ∀ t, HasDerivAt (fun t => L t - R t) 0 t := fun t => by
      have := (hLd t).sub (hRd t)
      rwa [hderiv t, sub_self] at this
    intro t
    exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) t 0
  -- integrate `L - R` against the weight
  have hlam0 : 0 < lam := by linarith
  set ρ : ℝ → ℂ := fun s => ((Real.sin s ^ (2 * lam - 1) : ℝ) : ℂ) with hρ
  set mC : ℂ := ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) with hmC
  have hρc : Continuous ρ := Complex.continuous_ofReal.comp
    ((Real.continuous_rpow_const (by linarith)).comp Real.continuous_sin)
  have hmρ : ∫ s : ℝ in (0 : ℝ)..π, ρ s = mC := by
    rw [intervalIntegral.integral_ofReal, (integral_sin_rpow_aux hlam0).2]
  have h1 : ultrasphPoly lam (n + 1) 1 ≠ 0 := by
    rw [ultrasphPoly_at_one hlre]
    exact div_ne_zero (poch_ne_zero_of_re_pos (by simp; linarith) _)
      (by exact_mod_cast (n + 1).factorial_ne_zero)
  have hm0 : mC ≠ 0 := gegAdd_weight_ne_zero hlam0
  have hLint : ∫ s : ℝ in (0 : ℝ)..π, L (Real.cos s) * ρ s =
      mC * ultrasphPoly lam (n + 1) (Real.cos θ) * ultrasphPoly lam (n + 1) (Real.cos φ) /
        ultrasphPoly lam (n + 1) 1 := gegAdd_integral_L hlam (n + 1) θ φ
  have hRint : ∫ s : ℝ in (0 : ℝ)..π, R (Real.cos s) * ρ s = gegAdd_term lam (n + 1) 0 θ φ * mC := by
    simp only [hR, Finset.sum_mul]
    rw [intervalIntegral.integral_finsetSum (f := fun j s => gegAdd_term lam (n + 1) j θ φ *
        ultrasphPoly μ j (Real.cos s) * ρ s) fun j _ =>
      Continuous.intervalIntegrable ((continuous_const.mul ((gegAdd_continuous μ j).comp
        (Complex.continuous_ofReal.comp Real.continuous_cos))).mul hρc) 0 π]
    rw [Finset.sum_range_succ']
    simp only [mul_assoc, intervalIntegral.integral_const_mul]
    rw [Finset.sum_eq_zero fun i _ => by
      rw [gegAdd_integral_vanish hlam i, mul_zero]]
    simp only [ultrasphPoly_zero, one_mul, hmρ, zero_add]
  have hDint : ∫ s : ℝ in (0 : ℝ)..π, (L (Real.cos s) - R (Real.cos s)) * ρ s =
      (L 0 - R 0) * mC := by
    simp only [hconst, intervalIntegral.integral_const_mul, hmρ]
  have hsplit : ∫ s : ℝ in (0 : ℝ)..π, (L (Real.cos s) - R (Real.cos s)) * ρ s =
      (∫ s : ℝ in (0 : ℝ)..π, L (Real.cos s) * ρ s) - ∫ s : ℝ in (0 : ℝ)..π, R (Real.cos s) * ρ s := by
    rw [← intervalIntegral.integral_sub]
    · exact intervalIntegral.integral_congr fun s _ => by ring
    · exact (((gegAdd_continuous _ _).comp (Complex.continuous_ofReal.comp
        (continuous_const.add (continuous_const.mul Real.continuous_cos)))).mul hρc).intervalIntegrable _ _
    · exact ((continuous_finsetSum _ fun j _ => continuous_const.mul ((gegAdd_continuous _ _).comp
        (Complex.continuous_ofReal.comp Real.continuous_cos))).mul hρc).intervalIntegrable _ _
  have h0 : gegAdd_term lam (n + 1) 0 θ φ = ultrasphPoly lam (n + 1) (Real.cos θ) *
      ultrasphPoly lam (n + 1) (Real.cos φ) / ultrasphPoly lam (n + 1) 1 := by
    have hc := gegAdd_coef_zero hlam (n + 1)
    simp only [gegAdd_term, Nat.cast_zero, zero_add, pow_zero, mul_one, Nat.sub_zero]
    rw [eq_div_iff h1]
    linear_combination ultrasphPoly lam (n + 1) (Real.cos θ) *
      ultrasphPoly lam (n + 1) (Real.cos φ) * hc
  rw [hDint, hLint, hRint, h0] at hsplit
  have hzero : (L 0 - R 0) * mC = 0 := by rw [hsplit]; ring
  have := hconst t
  rw [(mul_eq_zero.1 hzero).resolve_right hm0] at this
  exact sub_eq_zero.1 this

/-- Gegenbauer addition theorem, AAR (9.8.5'), for `λ > 1/2`. -/
theorem ultrasphPoly_addition {lam : ℝ} (hlam : 1 / 2 < lam)
    (n : ℕ) (theta phi psi : ℝ) :
    ultrasphPoly lam n
        (Real.cos theta * Real.cos phi +
          Real.sin theta * Real.sin phi * Real.cos psi) =
      ∑ j ∈ Finset.range (n + 1),
        (Gamma (2 * lam - 1) * 4 ^ j * (n - j).factorial *
          Gamma (j + (lam : ℂ)) ^ 2 * (2 * j + 2 * (lam : ℂ) - 1) /
            (Gamma (lam : ℂ) ^ 2 * Gamma (j + n + 2 * (lam : ℂ)))) *
        (Real.sin theta : ℂ) ^ j * ultrasphPoly (j + (lam : ℂ)) (n - j) (Real.cos theta) *
        (Real.sin phi : ℂ) ^ j * ultrasphPoly (j + (lam : ℂ)) (n - j) (Real.cos phi) *
        ultrasphPoly ((lam : ℂ) - 1 / 2) j (Real.cos psi) := by
  have h := gegAdd_main n lam hlam theta phi (Real.cos psi)
  rw [show ((Real.cos theta * Real.cos phi + Real.sin theta * Real.sin phi * Real.cos psi : ℝ) : ℂ)
    = (Real.cos theta : ℂ) * Real.cos phi + Real.sin theta * Real.sin phi * Real.cos psi by
    push_cast; ring] at h
  exact h

/-- Poisson kernel of the unit ball in `ℝⁿ` (AAR §9.9), before division by sphere area.
In the supplied printing, (9.9.2) and Theorem 9.9.1 put an extra `cos` around the
Euclidean inner product. The denominator intended there is `1 - 2r(α·η) + r²`. -/
def poissonKernelBall {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (1 - ∑ i, x i ^ 2) / (∑ i, (x i - y i) ^ 2) ^ (n / 2 : ℝ)

/-- The Poisson extension of existing harmonic boundary data is the original function. -/
theorem ballPoissonIntegral_reproduces {n : ℕ} (hn : n ≠ 0)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : HarmonicOnNhd f (ball 0 1)) (hcont : ContinuousOn f (closedBall 0 1))
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1) :
    TauCeti.ballPoissonIntegral (fun y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => f y) x = f x := by
  exact zonal_poisson hn hf hcont hx

/-- The unnormalized AAR kernel is sphere area times the Tau Ceti kernel. -/
theorem poissonKernelBall_eq_area_mul {n : ℕ} (hn : n ≠ 0) (x y : EuclideanSpace ℝ (Fin n)) :
    poissonKernelBall (fun i => x i) (fun i => y i) =
      volume.toSphere.real (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) *
        TauCeti.ballPoissonKernel n x y := by
  rw [poissonKernelBall, ← EuclideanSpace.real_norm_sq_eq x]
  have hsq : ∑ i, (x i - y i) ^ 2 = ‖x - y‖ ^ 2 :=
    (EuclideanSpace.real_norm_sq_eq (x - y)).symm
  rw [hsq]
  have hpow : (‖x - y‖ ^ 2) ^ (n / 2 : ℝ) = ‖x - y‖ ^ n := by
    rw [← Real.rpow_natCast (‖x - y‖) 2]
    change (‖x - y‖ ^ (2 : ℝ)) ^ (n / 2 : ℝ) = _
    rw [← Real.rpow_mul (norm_nonneg _)]
    rw [show (2 : ℝ) * (n / 2 : ℝ) = n by ring, Real.rpow_natCast]
  rw [hpow]
  rw [Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin, TauCeti.ballPoissonKernel_def]
  have hp := TauCeti.volume_real_unitBall_pos n
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

/-- Poisson representation of a harmonic function continuous on the closed unit ball. -/
theorem poissonKernelBall_reproduces {n : ℕ} (hn : 2 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : HarmonicOnNhd f (ball 0 1)) (hcont : ContinuousOn f (closedBall 0 1))
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ < 1) :
    (∫ y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      poissonKernelBall (fun i => x i) (fun i => y.val i) * f y.val ∂volume.toSphere) =
      volume.toSphere.real (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) * f x := by
  have hn0 : n ≠ 0 := by omega
  simp_rw [poissonKernelBall_eq_area_mul hn0 x, mul_assoc]
  rw [MeasureTheory.integral_const_mul, ← TauCeti.ballPoissonIntegral_def, ballPoissonIntegral_reproduces hn0 hf hcont hx]

/-- Special unitary group `SU(2)`. -/
abbrev SU2 := specialUnitaryGroup (Fin 2) ℂ

/-! The Jacobi-polynomial interpretation as matrix coefficients of irreducible
`SU(2)` representations (AAR §9.14) remains to be formulated using a representation
and a specified basis. The former reflexive placeholder has been removed: it
provided no representation-theoretic content. -/

open CliffordAlgebra TauCeti

/-- The Tau Ceti Clifford-form special orthogonal group in matrix coordinates. -/
def compactSO3EquivMatrix :
    QuadraticMap.specialOrthogonalGroup (realCliffordForm 3 0) ≃*
      Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one]
  exact (TauCeti.QuadraticMap.matrixSpecialOrthogonalEquivWeightedSumSquaresOne (Fin 3)).symm

/-- The distinguished negative Spin scalar has special unitary matrix `-1`. -/
theorem realSpinThreeEquivSpecialUnitary_negOne :
    (realSpinThreeEquivSpecialUnitary
      (spinGroup.negOne (realCliffordForm 3 0) (nondegenerate_realCliffordForm 3 0).ne_zero) :
        Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  rw [coe_realSpinThreeEquivSpecialUnitary_apply, coe_realSpinThreeEquivQuaternionUnitary_apply]
  have he : evenUnitaryGroupEvenPart (realCliffordForm 3 0)
      (spinGroupToEvenUnitary (realCliffordForm 3 0)
        (spinGroup.negOne (realCliffordForm 3 0) (nondegenerate_realCliffordForm 3 0).ne_zero)) = -1 := by
    apply Subtype.ext
    simp
  rw [he, map_neg, map_one, map_neg, map_one]


/-- The double cover `SU(2) → SO(3)` (AAR §9.16). -/
lemma su2_covers_so3 :
    ∃ Φ : SU2 →* specialOrthogonalGroup (Fin 3) ℝ, Function.Surjective Φ ∧
      (∀ g, Φ g = 1 ↔ g = 1 ∨ g.1 = (-1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  let E := realSpinThreeEquivSpecialUnitary
  let C := compactSO3EquivMatrix
  let P := spinToSpecialOrthogonal (realCliffordForm 3 0)
  let Φ := C.toMonoidHom.comp (P.comp E.symm.toMonoidHom)
  refine ⟨Φ, C.surjective.comp
    ((spinToSpecialOrthogonal_surjective_of_posDef _ (posDef_realCliffordForm_zero 3)).comp
      E.symm.surjective), ?_⟩
  intro g
  have hker : Φ g = 1 ↔ E.symm g = 1 ∨ E.symm g =
      spinGroup.negOne (realCliffordForm 3 0) (nondegenerate_realCliffordForm 3 0).ne_zero := by
    change C (P (E.symm g)) = 1 ↔ _
    rw [← C.map_one, C.injective.eq_iff]
    exact mem_ker_spinToSpecialOrthogonal_iff _ (nondegenerate_realCliffordForm 3 0) _
  rw [hker]
  constructor
  · rintro (hg | hg)
    · left
      have hh := congrArg E hg
      simpa using hh
    · right
      have hh := congrArg (fun s => (E s : Matrix (Fin 2) (Fin 2) ℂ)) hg
      simpa only [MulEquiv.apply_symm_apply, E, realSpinThreeEquivSpecialUnitary_negOne] using hh
  · rintro (rfl | hg)
    · left
      exact E.symm.map_one
    · right
      apply E.injective
      apply Subtype.ext
      simpa only [MulEquiv.apply_symm_apply, E, realSpinThreeEquivSpecialUnitary_negOne] using hg

end DLMF.SphericalHarmonics
