/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.Basic
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenExpansion
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenFinite
public import DLMF.Bessel.Basic.SecondKind
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Differential equations with a parameter (DLMF §2.8)

Uniform asymptotic solutions of `w'' = (u² f(z) + g(z)) w` (2.8.1) for large `u`.

## Main results

* `liouville_transformation`: the Liouville transformation (DLMF 2.8.2–2.8.4).
* `liouville_caseI`, `liouville_caseII`, `liouville_caseIII`: the normalizations of the three
  cases (DLMF 2.8.5–2.8.8).
* `bessel_approximating_equation`: the Case III approximating equation (DLMF 2.8.9).
* `caseI_dominant_expansion`, `caseI_recessive_expansion`: Case I, no transition points
  (DLMF 2.8.10–2.8.13).
* `caseII_airy_expansion`, `caseII_airy_envelope`: Case II, a simple turning point, with Airy
  functions (DLMF 2.8.14–2.8.18, 2.8.22–2.8.23).
* `caseIII_bessel_expansion_pos`, `caseIII_bessel_expansion_neg`, `caseIII_bessel_envelope`:
  Case III, a simple pole, with Bessel functions (DLMF 2.8.24–2.8.31, 2.8.35–2.8.36).

## Implementation notes

The Case I expansions are stated for real `ξ` and follow from DLMFMathlib's Liouville–Green
expansions with error bounds
(`LiouvilleGreen.exists_solution_expansion_dominant_exp_finite_endpoint` and
`LiouvilleGreen.exists_solution_expansion_exp`, Olver Ch. 10, Thm. 3.1) with amplitude `1`;
they are stronger than DLMF in that the error bounds are explicit.

The approximants are DLMF's `Ai`, `Bi` (`DLMF.Airy.airyAi`, …), `I_ν`, `K_ν`
(`DLMF.Bessel.besselI`, `DLMF.Bessel.besselK`), `J_ν` (Mathlib's `Complex.besselJ`) and `Y_ν`
(`DLMF.Bessel.besselY`), evaluated at real arguments. "As `u → ∞`, uniformly in `ξ`" is
expressed by explicit constants: `∃ C U₀, ∀ u ≥ U₀, ∀ ξ, |error| ≤ C u^{-k}`. The uniform
expansions are also differentiable in `ξ` (DLMF); differentiability is not formalized.
-/

@[expose] public noncomputable section

open Set Filter Asymptotics MeasureTheory
open scoped Topology

namespace DLMF.AsymptoticApproximations

open LiouvilleGreen

/-! ### §2.8(i) Liouville transformation and classification of cases -/

/-- DLMF 2.8.2–2.8.4 (the Liouville transformation, real form): let `z = Z(ξ)` with `Z' > 0`,
and let `w` solve `w'' = (u² f + g) w` (2.8.1) near `Z(ξ)`. Then `W = ż^{-1/2} w` satisfies
`W'' = (u² ż² f(z) + ψ(ξ)) W` with `ψ = ż² g(z) + ż^{1/2} (ż^{-1/2})''` (dots are
`d/dξ`). Here `A = ż^{-1/2}`, `A'` and `A''` are its first two derivatives, so
`ż^{1/2} (ż^{-1/2})'' = A''/A`. -/
@[dlmf 2.8.E1, dlmf 2.8.E2, dlmf 2.8.E3, dlmf 2.8.E4]
theorem liouville_transformation {u : ℝ} {f g w w' Z Z' Z'' A' A'' : ℝ → ℝ} {S : Set ℝ}
    (hZ : ∀ ξ ∈ S, HasDerivAt Z (Z' ξ) ξ) (hZ' : ∀ ξ ∈ S, HasDerivAt Z' (Z'' ξ) ξ)
    (hpos : ∀ ξ ∈ S, 0 < Z' ξ)
    (hA' : ∀ ξ ∈ S, A' ξ = -(1 / 2) * Z' ξ ^ (-(3 / 2) : ℝ) * Z'' ξ)
    (hA'' : ∀ ξ ∈ S, HasDerivAt A' (A'' ξ) ξ)
    (hw : ∀ ξ ∈ S, HasDerivAt w (w' (Z ξ)) (Z ξ))
    (hw' : ∀ ξ ∈ S, HasDerivAt w' ((u ^ 2 * f (Z ξ) + g (Z ξ)) * w (Z ξ)) (Z ξ)) :
    ∃ W' : ℝ → ℝ, ∀ ξ ∈ S,
      HasDerivAt (fun ξ => Z' ξ ^ (-(1 / 2) : ℝ) * w (Z ξ)) (W' ξ) ξ ∧
      HasDerivAt W' ((u ^ 2 * Z' ξ ^ 2 * f (Z ξ) +
          (Z' ξ ^ 2 * g (Z ξ) + A'' ξ / Z' ξ ^ (-(1 / 2) : ℝ))) *
        (Z' ξ ^ (-(1 / 2) : ℝ) * w (Z ξ))) ξ := by
  refine ⟨fun ξ => A' ξ * w (Z ξ) + Z' ξ ^ (1 / 2 : ℝ) * w' (Z ξ), fun ξ hξ => ⟨?_, ?_⟩⟩
  · have hp := hpos ξ hξ
    have h1 := ((hZ' ξ hξ).rpow_const (p := -(1 / 2)) (Or.inl hp.ne')).mul
      ((hw ξ hξ).comp ξ (hZ ξ hξ))
    refine h1.congr_deriv ?_
    simp only [Function.comp]
    rw [hA' ξ hξ]
    have e1 : Z' ξ ^ (-(1 / 2 : ℝ) - 1) = Z' ξ ^ (-(3 / 2) : ℝ) := by norm_num
    have e2 : Z' ξ ^ (-(1 / 2) : ℝ) * Z' ξ = Z' ξ ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add_one hp.ne']; norm_num
    rw [e1, ← e2]
    ring
  · have hp := hpos ξ hξ
    have h1 := (hA'' ξ hξ).mul ((hw ξ hξ).comp ξ (hZ ξ hξ))
    have h2 := ((hZ' ξ hξ).rpow_const (p := 1 / 2) (Or.inl hp.ne')).mul
      ((hw' ξ hξ).comp ξ (hZ ξ hξ))
    refine (h1.add h2).congr_deriv ?_
    rw [hA' ξ hξ]
    have hm : Z' ξ ^ (-(1 / 2) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
    have e3 : Z' ξ ^ (-(3 / 2) : ℝ) * Z' ξ = Z' ξ ^ (1 / 2 - 1 : ℝ) := by
      rw [← Real.rpow_add_one hp.ne']; norm_num
    have e4 : Z' ξ ^ (1 / 2 : ℝ) = Z' ξ ^ (-(1 / 2) : ℝ) * Z' ξ := by
      rw [← Real.rpow_add_one hp.ne']; norm_num
    simp only [Function.comp]
    rw [← e3, e4]
    field_simp
    ring

/-- DLMF 2.8.5 (Case I): if `ξ = ∫ f^{1/2} dz`, that is, `ξ` has derivative `f^{1/2}` in `z`,
and `ξ'(z) = d`, then `ż² f(z) = 1` with `ż = 1/d`; the transformed equation is 2.8.8 with
`m = 0`. -/
@[dlmf 2.8.E5, dlmf 2.8.E8, dlmf 2.8.i]
theorem liouville_caseI {f ξ : ℝ → ℝ} {z d : ℝ} (hf : 0 < f z) (hξ : HasDerivAt ξ d z)
    (hF : HasDerivAt ξ (√(f z)) z) :
    d⁻¹ ^ 2 * f z = 1 := by
  rw [hξ.unique hF, inv_pow, Real.sq_sqrt hf.le, inv_mul_cancel₀ hf.ne']

/-- DLMF 2.8.6 (Case II): if `(2/3) ξ^{3/2} = ∫_{z₀}^z f^{1/2}`, that is, `(2/3) ξ^{3/2}` has
derivative `f^{1/2}` in `z`, and `ξ > 0` with `ξ'(z) = d`, then `ż² f(z) = ξ` with
`ż = 1/d`; the transformed equation is 2.8.8 with `m = 1`. -/
@[dlmf 2.8.E6, dlmf 2.8.E8]
theorem liouville_caseII {f ξ : ℝ → ℝ} {z d : ℝ} (hf : 0 < f z) (hξp : 0 < ξ z)
    (hξ : HasDerivAt ξ d z)
    (hF : HasDerivAt (fun z => 2 / 3 * ξ z ^ (3 / 2 : ℝ)) (√(f z)) z) :
    d⁻¹ ^ 2 * f z = ξ z := by
  have h1 := (hξ.rpow_const (p := 3 / 2) (Or.inl hξp.ne')).const_mul (2 / 3)
  have h2 := hF.unique h1
  have e : ξ z ^ ((3 / 2 : ℝ) - 1) = √(ξ z) := by
    rw [Real.sqrt_eq_rpow]; norm_num
  rw [e] at h2
  have hs : 0 < √(ξ z) := Real.sqrt_pos.2 hξp
  have hd : d = √(f z) / √(ξ z) := by
    field_simp
    linarith
  have hfs : 0 < √(f z) := Real.sqrt_pos.2 hf
  rw [hd, inv_div, div_pow, Real.sq_sqrt hf.le, Real.sq_sqrt hξp.le]
  field_simp

/-- DLMF 2.8.7 (Case III): if `2 ξ^{1/2} = ∫_{z₀}^z f^{1/2}`, that is, `2 ξ^{1/2}` has
derivative `f^{1/2}` in `z`, and `ξ > 0` with `ξ'(z) = d`, then `ż² f(z) = 1/ξ` with `ż = 1/d`;
the transformed equation is 2.8.8 with `m = -1`. -/
@[dlmf 2.8.E7, dlmf 2.8.E8]
theorem liouville_caseIII {f ξ : ℝ → ℝ} {z d : ℝ} (hf : 0 < f z) (hξp : 0 < ξ z)
    (hξ : HasDerivAt ξ d z)
    (hF : HasDerivAt (fun z => 2 * ξ z ^ (1 / 2 : ℝ)) (√(f z)) z) :
    d⁻¹ ^ 2 * f z = 1 / ξ z := by
  have h1 := (hξ.rpow_const (p := 1 / 2) (Or.inl hξp.ne')).const_mul 2
  have h2 := hF.unique h1
  have e : ξ z ^ ((1 / 2 : ℝ) - 1) = (√(ξ z))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hξp.le]; norm_num
  rw [e] at h2
  have hs : 0 < √(ξ z) := Real.sqrt_pos.2 hξp
  have hd : d = √(f z) * √(ξ z) := by
    field_simp at h2
    linarith
  rw [hd, inv_pow, mul_pow, Real.sq_sqrt hf.le, Real.sq_sqrt hξp.le]
  field_simp

section BesselApproximation

open scoped _root_.Real
open DLMF.Bessel

/-- `I_ν(-y) = e^{iπν} I_ν(y)` for `y > 0`, with the principal branch on the cut. -/
private lemma besselI_neg_ofReal (ν : ℂ) {y : ℝ} (hy : 0 < y) :
    besselI ν (-(y : ℂ)) = Complex.exp (π * Complex.I * ν) * besselI ν y := by
  unfold besselI
  have h : -(y : ℂ) / 2 = ((-(y / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.ofReal_cpow_of_nonpos (by linarith) ν]
  push_cast
  ring_nf

/-- `K_ν(-y) = e^{-iπν} K_ν(y) - iπ I_ν(y)` for `y > 0` and `ν ∉ ℤ` (DLMF 10.34.2). -/
private lemma besselK_neg_ofReal_of_not_int {ν : ℂ} (hν : ∀ k : ℤ, ν ≠ k) {y : ℝ}
    (hy : 0 < y) :
    besselK ν (-(y : ℂ)) =
      Complex.exp (-(π * Complex.I * ν)) * besselK ν y - π * Complex.I * besselI ν y := by
  have hs : Complex.sin (ν * π) ≠ 0 := sin_mul_pi_ne_zero hν
  rw [besselK_eq_of_not_int hν, besselK_eq_of_not_int hν, besselE, besselE,
    besselI_neg_ofReal ν hy, besselI_neg_ofReal (-ν) hy]
  have hsin : Complex.sin (ν * π) =
      (Complex.exp (-(π * Complex.I * ν)) - Complex.exp (π * Complex.I * ν)) * Complex.I / 2 := by
    rw [Complex.sin]; ring_nf
  have he : Complex.exp (π * Complex.I * -ν) = Complex.exp (-(π * Complex.I * ν)) := by
    ring_nf
  have hd : Complex.exp (-(π * Complex.I * ν)) - Complex.exp (π * Complex.I * ν) ≠ 0 := by
    intro h; apply hs; rw [hsin, h]; ring
  rw [he, hsin]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `K_ν(-y) = e^{-iπν} K_ν(y) - iπ I_ν(y)` for `y > 0` and every order (DLMF 10.34.2). -/
private lemma besselK_neg_ofReal (ν : ℂ) {y : ℝ} (hy : 0 < y) :
    besselK ν (-(y : ℂ)) =
      Complex.exp (-(π * Complex.I * ν)) * besselK ν y - π * Complex.I * besselI ν y := by
  by_cases hν : ∃ k : ℤ, ν = k
  · obtain ⟨n, rfl⟩ := hν
    have hy' : (y : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hy
    have hg : ContinuousAt (fun μ : ℂ => Complex.exp (-(π * Complex.I * μ)) * besselK μ y -
        π * Complex.I * besselI μ y) n :=
      ((by fun_prop : Continuous fun μ : ℂ => Complex.exp (-(π * Complex.I * μ))).continuousAt.mul
        (continuousAt_besselK_order id continuous_id n hy')).sub
        (continuousAt_const.mul (continuousAt_besselI_order id continuous_id n hy'))
    have ht : Tendsto (fun μ => π / 2 * (besselI (-μ) (-(y : ℂ)) - besselI μ (-(y : ℂ))) /
        Complex.sin (μ * π)) (𝓝[≠] (n : ℂ)) (𝓝 (Complex.exp (-(π * Complex.I * n)) *
          besselK n y - π * Complex.I * besselI n y)) := by
      refine (hg.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (n : ℂ)
        (by norm_num : (0 : ℝ) < 1 / 2))] with μ hμ hμb
      have hμ' := not_int_of_mem_ball hμb hμ
      rw [← besselK_neg_ofReal_of_not_int hμ' hy, besselK_eq_of_not_int hμ', besselE]
    have hex : ∃ k : ℤ, (n : ℂ) = k := ⟨n, rfl⟩
    simp only [besselK, hex, ite_true] at ht ⊢
    exact ht.limUnder_eq
  · push Not at hν
    exact besselK_neg_ofReal_of_not_int hν hy

/-- If `G` solves the modified Bessel equation `z²G'' + zG' - (z² + c)G = 0` on the slit
plane, then `W(ξ) = ξ^{1/2} G(2vξ^{1/2})`, `v > 0`, solves `W'' = (v²/ξ + ρ/ξ²) W` for `ξ > 0`,
where `c = 1 + 4ρ`. -/
private lemma hasDerivAt_sqrt_mul_modifiedBessel {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G Complex.slitPlane) {c : ℂ}
    (hode : ∀ z ∈ Complex.slitPlane,
      z ^ 2 * iteratedDeriv 2 G z + z * deriv G z - (z ^ 2 + c) * G z = 0)
    {v ρ : ℝ} (hv : 0 < v) (hc : c = 1 + 4 * ρ) :
    ∃ W' : ℝ → ℂ, ∀ ξ : ℝ, 0 < ξ →
      HasDerivAt (fun ξ : ℝ => ((√ξ : ℝ) : ℂ) * G (2 * v * √ξ)) (W' ξ) ξ ∧
      HasDerivAt W' ((v ^ 2 / ξ + ρ / ξ ^ 2 : ℝ) * (((√ξ : ℝ) : ℂ) * G (2 * v * √ξ))) ξ := by
  have hGa : AnalyticOnNhd ℂ G Complex.slitPlane := hG.analyticOnNhd Complex.isOpen_slitPlane
  have hmem : ∀ ξ : ℝ, 0 < ξ → (2 * (v : ℂ) * ((√ξ : ℝ) : ℂ)) ∈ Complex.slitPlane := by
    intro ξ hξ
    have : (2 * (v : ℂ) * ((√ξ : ℝ) : ℂ)) = ((2 * v * √ξ : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact Complex.ofReal_mem_slitPlane.2 (by have := Real.sqrt_pos.2 hξ; positivity)
  refine ⟨fun ξ => (2 * ((√ξ : ℝ) : ℂ))⁻¹ *
    (G (2 * v * √ξ) + 2 * v * √ξ * deriv G (2 * v * √ξ)), fun ξ hξ => ?_⟩
  have hs : 0 < √ξ := Real.sqrt_pos.2 hξ
  have hs0 : ((√ξ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have hsq : ((√ξ : ℝ) : ℂ) ^ 2 = (ξ : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hξ.le]
  have hS : HasDerivAt (fun ξ : ℝ => ((√ξ : ℝ) : ℂ)) ((2 * ((√ξ : ℝ) : ℂ))⁻¹) ξ := by
    have := (Real.hasDerivAt_sqrt hξ.ne').ofReal_comp
    convert this using 1
    push_cast; ring
  have hX : HasDerivAt (fun ξ : ℝ => 2 * (v : ℂ) * ((√ξ : ℝ) : ℂ))
      (2 * v * (2 * ((√ξ : ℝ) : ℂ))⁻¹) ξ := hS.const_mul _
  have hx := hmem ξ hξ
  have hG1 := (hGa _ hx).differentiableAt.hasDerivAt
  have hdG := ((hGa.deriv _ hx).differentiableAt).hasDerivAt
  have hGc := hG1.comp ξ hX
  have hdGc := hdG.comp ξ hX
  have hode' := hode _ hx
  rw [iteratedDeriv_succ, iteratedDeriv_one] at hode'
  constructor
  · convert hS.mul hGc using 1
    · rfl
    simp only [Function.comp_apply]
    generalize deriv G (2 * (v : ℂ) * ((√ξ : ℝ) : ℂ)) = b
    generalize G (2 * (v : ℂ) * ((√ξ : ℝ) : ℂ)) = b0
    field_simp
  · have hinv : HasDerivAt (fun ξ : ℝ => (2 * ((√ξ : ℝ) : ℂ))⁻¹)
        (-(2 * (2 * ((√ξ : ℝ) : ℂ))⁻¹) / (2 * ((√ξ : ℝ) : ℂ)) ^ 2) ξ :=
      (hS.const_mul 2).inv (mul_ne_zero two_ne_zero hs0)
    have h := hinv.mul (hGc.add (hX.mul hdGc))
    convert h using 1
    · funext t; simp only [Function.comp_def, Pi.mul_apply, Pi.add_apply]
    simp only [Function.comp_def, Pi.mul_apply, Pi.add_apply]
    rw [hc] at hode'
    push_cast
    rw [← hsq]
    generalize deriv (deriv G) (2 * (v : ℂ) * ((√ξ : ℝ) : ℂ)) = b2 at hode' ⊢
    generalize deriv G (2 * (v : ℂ) * ((√ξ : ℝ) : ℂ)) = b1 at hode' ⊢
    generalize G (2 * (v : ℂ) * ((√ξ : ℝ) : ℂ)) = b0 at hode' ⊢
    field_simp
    linear_combination (-1 : ℂ) * hode'

/-- Linear combinations of solutions of `W'' = q W` on `ξ > 0` are solutions. -/
private lemma hasDerivAt_linear_combination {W₁ W₂ W W₁' W₂' : ℝ → ℂ} {q : ℝ → ℂ} (a b : ℂ)
    (h₁ : ∀ ξ : ℝ, 0 < ξ → HasDerivAt W₁ (W₁' ξ) ξ ∧ HasDerivAt W₁' (q ξ * W₁ ξ) ξ)
    (h₂ : ∀ ξ : ℝ, 0 < ξ → HasDerivAt W₂ (W₂' ξ) ξ ∧ HasDerivAt W₂' (q ξ * W₂ ξ) ξ)
    (hW : ∀ ξ : ℝ, 0 < ξ → W ξ = a * W₁ ξ + b * W₂ ξ) :
    ∃ W' : ℝ → ℂ, ∀ ξ : ℝ, 0 < ξ → HasDerivAt W (W' ξ) ξ ∧ HasDerivAt W' (q ξ * W ξ) ξ := by
  refine ⟨fun ξ => a * W₁' ξ + b * W₂' ξ, fun ξ hξ => ⟨?_, ?_⟩⟩
  · have h := ((h₁ ξ hξ).1.const_mul a).add ((h₂ ξ hξ).1.const_mul b)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hξ] with t ht using hW t ht
  · have h := ((h₁ ξ hξ).2.const_mul a).add ((h₂ ξ hξ).2.const_mul b)
    convert h using 1
    rw [hW ξ hξ]
    ring

/-- `W(ξ) = ξ^{1/2} C` solves `W'' = (ρ/ξ²) W` when `(1 + 4ρ) C = 0`. -/
private lemma hasDerivAt_sqrt_mul_const {C : ℂ} {ρ : ℝ} (hC : (1 + 4 * (ρ : ℂ)) * C = 0) :
    ∃ W' : ℝ → ℂ, ∀ ξ : ℝ, 0 < ξ →
      HasDerivAt (fun ξ : ℝ => ((√ξ : ℝ) : ℂ) * C) (W' ξ) ξ ∧
      HasDerivAt W' ((ρ / ξ ^ 2 : ℝ) * (((√ξ : ℝ) : ℂ) * C)) ξ := by
  refine ⟨fun ξ => (2 * ((√ξ : ℝ) : ℂ))⁻¹ * C, fun ξ hξ => ?_⟩
  have hs : 0 < √ξ := Real.sqrt_pos.2 hξ
  have hs0 : ((√ξ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have hsq : ((√ξ : ℝ) : ℂ) ^ 2 = (ξ : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hξ.le]
  have hS : HasDerivAt (fun ξ : ℝ => ((√ξ : ℝ) : ℂ)) ((2 * ((√ξ : ℝ) : ℂ))⁻¹) ξ := by
    have := (Real.hasDerivAt_sqrt hξ.ne').ofReal_comp
    convert this using 1
    push_cast; ring
  refine ⟨by simpa [mul_comm] using hS.mul_const C, ?_⟩
  have h := ((hS.const_mul 2).inv (mul_ne_zero two_ne_zero hs0)).mul_const C
  convert h using 1
  have hρ : (ρ : ℂ) * C = -C / 4 := by linear_combination hC / 4
  push_cast
  rw [← hsq]
  field_simp
  linear_combination (4 : ℂ) * hρ

/-- `K_ν(0) = 0` (Lean's value at the singular point) for `ν ≠ 0`. -/
private lemma besselK_apply_zero {ν : ℂ} (hν : ν ≠ 0) : besselK ν 0 = 0 := by
  by_cases hint : ∃ k : ℤ, ν = k
  · have ht : Tendsto (fun μ => π / 2 * (besselI (-μ) 0 - besselI μ 0) / Complex.sin (μ * π))
        (𝓝[≠] ν) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (eventually_ne_nhds hν)] with μ hμ
      rw [besselI_apply_zero hμ, besselI_apply_zero (neg_ne_zero.2 hμ)]
      simp
    simp only [besselK, hint, ite_true]
    exact ht.limUnder_eq
  · push Not at hint
    rw [besselK_eq_of_not_int hint, besselE, besselI_apply_zero hν,
      besselI_apply_zero (neg_ne_zero.2 hν)]
    simp

/-- DLMF 2.8.9: the Case III approximating equation `W'' = (u²/ξ + ρ/ξ²) W` has the solutions
`ξ^{1/2} I_ν(2uξ^{1/2})` and `ξ^{1/2} K_ν(2uξ^{1/2})` for `ξ > 0`, with `ν = (1 + 4ρ)^{1/2}`
(equivalently `ν² = 1 + 4ρ`). -/
@[dlmf 2.8.E9]
theorem bessel_approximating_equation {u ρ ν : ℝ} (hν : ν ^ 2 = 1 + 4 * ρ) :
    (∃ W' : ℝ → ℂ, ∀ ξ : ℝ, 0 < ξ →
      HasDerivAt (fun ξ : ℝ => ((√ξ : ℝ) : ℂ) * DLMF.Bessel.besselI ν (2 * u * √ξ)) (W' ξ) ξ ∧
      HasDerivAt W' ((u ^ 2 / ξ + ρ / ξ ^ 2 : ℝ) *
        (((√ξ : ℝ) : ℂ) * DLMF.Bessel.besselI ν (2 * u * √ξ))) ξ) ∧
    (∃ W' : ℝ → ℂ, ∀ ξ : ℝ, 0 < ξ →
      HasDerivAt (fun ξ : ℝ => ((√ξ : ℝ) : ℂ) * DLMF.Bessel.besselK ν (2 * u * √ξ)) (W' ξ) ξ ∧
      HasDerivAt W' ((u ^ 2 / ξ + ρ / ξ ^ 2 : ℝ) *
        (((√ξ : ℝ) : ℂ) * DLMF.Bessel.besselK ν (2 * u * √ξ))) ξ) := by
  have hc : ((ν : ℂ)) ^ 2 = 1 + 4 * (ρ : ℂ) := by exact_mod_cast hν
  have hIdiff : DifferentiableOn ℂ (besselI ν) Complex.slitPlane := fun z hz =>
    (hasDerivAt_besselI hz).differentiableAt.differentiableWithinAt
  have hKdiff : DifferentiableOn ℂ (besselK ν) Complex.slitPlane := fun z hz =>
    (hasDerivAt_besselK (ν : ℂ) hz).differentiableAt.differentiableWithinAt
  have hIode : ∀ z ∈ Complex.slitPlane, z ^ 2 * iteratedDeriv 2 (besselI ν) z +
      z * deriv (besselI ν) z - (z ^ 2 + (ν : ℂ) ^ 2) * besselI ν z = 0 := fun z hz =>
    besselI_ode hz
  have hKode : ∀ z ∈ Complex.slitPlane, z ^ 2 * iteratedDeriv 2 (besselK ν) z +
      z * deriv (besselK ν) z - (z ^ 2 + (ν : ℂ) ^ 2) * besselK ν z = 0 := fun z hz =>
    besselK_ode_all (ν : ℂ) hz
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have hv : 0 < -u := neg_pos.2 hu
    obtain ⟨WI, hWI⟩ := hasDerivAt_sqrt_mul_modifiedBessel hIdiff hIode hv hc
    obtain ⟨WK, hWK⟩ := hasDerivAt_sqrt_mul_modifiedBessel hKdiff hKode hv hc
    simp only [neg_sq] at hWI hWK
    have harg : ∀ ξ : ℝ, 0 < ξ → (2 * (u : ℂ) * ((√ξ : ℝ) : ℂ)) =
        -(((2 * (-u) * √ξ : ℝ)) : ℂ) := fun ξ _ => by push_cast; ring
    have hpos : ∀ ξ : ℝ, 0 < ξ → 0 < 2 * (-u) * √ξ := fun ξ hξ => by
      have := Real.sqrt_pos.2 hξ; positivity
    have hcast : ∀ ξ : ℝ, (((2 * (-u) * √ξ : ℝ)) : ℂ) = 2 * ((-u : ℝ) : ℂ) * ((√ξ : ℝ) : ℂ) :=
      fun ξ => by push_cast; ring
    refine ⟨hasDerivAt_linear_combination (Complex.exp (π * Complex.I * ν)) 0 hWI hWI
      fun ξ hξ => ?_, hasDerivAt_linear_combination (Complex.exp (-(π * Complex.I * ν)))
        (-(π * Complex.I)) hWK hWI fun ξ hξ => ?_⟩
    · rw [harg ξ hξ, besselI_neg_ofReal _ (hpos ξ hξ), hcast]
      ring
    · rw [harg ξ hξ, besselK_neg_ofReal _ (hpos ξ hξ), hcast]
      ring
  · have hsimp : ∀ ξ : ℝ, (2 * ((0 : ℝ) : ℂ) * ((√ξ : ℝ) : ℂ)) = 0 := fun ξ => by simp
    have hq : ∀ ξ : ℝ, ((0 : ℝ) ^ 2 / ξ + ρ / ξ ^ 2 : ℝ) = (ρ / ξ ^ 2 : ℝ) := fun ξ => by simp
    simp only [hsimp, hq]
    by_cases hν0 : ν = 0
    · have hρ : (1 + 4 * (ρ : ℂ)) = 0 := by
        rw [← hc, hν0]; simp
      exact ⟨hasDerivAt_sqrt_mul_const (by rw [hρ, zero_mul]),
        hasDerivAt_sqrt_mul_const (by rw [hρ, zero_mul])⟩
    · have hν0' : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hν0
      have hI0 : besselI ν 0 = 0 := besselI_apply_zero hν0'
      have hK0 : besselK ν 0 = 0 := besselK_apply_zero hν0'
      exact ⟨hasDerivAt_sqrt_mul_const (by rw [hI0, mul_zero]),
        hasDerivAt_sqrt_mul_const (by rw [hK0, mul_zero])⟩
  · exact ⟨hasDerivAt_sqrt_mul_modifiedBessel hIdiff hIode hu hc,
      hasDerivAt_sqrt_mul_modifiedBessel hKdiff hKode hu hc⟩

end BesselApproximation

/-! ### §2.8(ii) Case I: no transition points -/

/-- `lgSeries (-u)` is the series `∑_{s<n} A_s/u^s` of DLMF 2.8.11. -/
private lemma lgSeries_neg_eq_sum (u : ℝ) (As : ℕ → ℝ → ℝ) (n : ℕ) (y : ℝ) :
    lgSeries (-u) As n y = ∑ s ∈ Finset.range n, As s y / u ^ s := by
  unfold lgSeries
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [neg_pow u, mul_div_mul_left _ _ (pow_ne_zero s (by norm_num : (-1 : ℝ) ≠ 0))]

/-- `lgSeries u` is the series `∑_{s<n} (-1)^s A_s/u^s` of DLMF 2.8.12. -/
private lemma lgSeries_eq_sum_neg_one_pow (u : ℝ) (As : ℕ → ℝ → ℝ) (n : ℕ) (y : ℝ) :
    lgSeries u As n y = ∑ s ∈ Finset.range n, (-1) ^ s * As s y / u ^ s := rfl

/-- DLMF 2.8.10–2.8.11 with 2.8.13 (Case I, `j = 1`, real `ξ`): let `S` be an open interval
containing the reference point `α₁`, `ψ` continuous on `S`, and let `A_0 = 1`, `A_1, …, A_n`
satisfy `A_{s+1}' = -½ A_s'' + ½ ψ A_s` (2.8.13 differentiated). Then for `u > 0` the equation
`W'' = (u² + ψ) W` has a solution
`W_{n,1}(u, ξ) = e^{uξ} (∑_{s<n} A_s(ξ)/u^s + ε(u, ξ))` on `S ∩ (α₁, ∞)` with
`|ε| ≤ u^{-n} 𝒱_{α₁,ξ}(A_n) exp(𝒱_{α₁,ξ}(ψ)/(2u))`; in particular `ε = O(u^{-n})` uniformly
where the variations are bounded. Stronger than DLMF (explicit error bound). -/
@[dlmf 2.8.E10, dlmf 2.8.E11, dlmf 2.8.E13, dlmf 2.8.ii]
theorem caseI_dominant_expansion {S : Set ℝ} {α₁ u : ℝ} (hS : IsOpen S) (hSc : S.OrdConnected)
    (ha : α₁ ∈ S) (hu : 0 < u) {ψ : ℝ → ℝ} (hψ : ContinuousOn ψ S) {n : ℕ}
    {As Ad Ad2 : ℕ → ℝ → ℝ}
    (hAs : ∀ s < n, ∀ x ∈ S, HasDerivAt (As s) (Ad s x) x)
    (hAd : ∀ s < n, ∀ x ∈ S, HasDerivAt (Ad s) (Ad2 s x) x)
    (hAd2c : ∀ s < n, ContinuousOn (Ad2 s) S) (h0 : ∀ x ∈ S, Ad 0 x = 0)
    (hrec : ∀ s < n, ∀ x ∈ S, Ad (s + 1) x = -(1 / 2) * Ad2 s x + 1 / 2 * ψ x * As s x) :
    ∃ ε ε' W' : ℝ → ℝ, ∀ x ∈ S, α₁ < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => Real.exp (u * y) *
        (∑ s ∈ Finset.range n, As s y / u ^ s + ε y)) (W' x) x ∧
      HasDerivAt W' ((u ^ 2 + ψ x) *
        (Real.exp (u * x) * (∑ s ∈ Finset.range n, As s x / u ^ s + ε x))) x ∧
      |ε x| ≤ (∫ t in α₁..x, |Ad n t|) / u ^ n * Real.exp ((∫ t in α₁..x, |ψ t|) / (2 * u)) := by
  obtain ⟨ε, ε', W', H⟩ := exists_solution_expansion_dominant_exp_finite_endpoint hS hSc ha hu
    (A := fun _ => 1) (A' := fun _ => 0) (A'' := fun _ => 0) (ξ := id) (g := ψ)
    (fun _ _ => one_ne_zero) (fun x _ => hasDerivAt_const x 1) (fun x _ => hasDerivAt_const x 0)
    continuousOn_const hψ (fun x _ => by simpa using hasDerivAt_id x) hAs hAd hAd2c h0
    (fun s hs x hx => by rw [hrec s hs x hx]; ring)
  refine ⟨ε, ε', W', fun x hx hax => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := H x hx hax
  have hsum : ∀ y, lgSeries (-u) As n y = ∑ s ∈ Finset.range n, As s y / u ^ s :=
    lgSeries_neg_eq_sum u As n
  simp only [hsum, one_mul, id, one_pow, inv_one, mul_one] at h2 h3
  refine ⟨h1, h2, h3, ?_⟩
  have hV : (∫ t in α₁..x, |(1 : ℝ) * 0 - ψ t * 1 ^ 2|) = ∫ t in α₁..x, |ψ t| := by
    congr 1; funext t; simp
  rw [hV] at h4
  exact h4

/-- DLMF 2.8.12 with 2.8.13 (Case I, `j = 2`, real `ξ`, reference point `α₂ = +∞`): for `u > 0`
the equation `W'' = (u² + ψ) W` on `(a, ∞)` has a solution
`W_{n,2}(u, ξ) = e^{-uξ} (∑_{s<n} (-1)^s A_s(ξ)/u^s + ε(u, ξ))` with
`|ε| ≤ u^{-n} 𝒱_{ξ,∞}(A_n) exp(𝒱_{ξ,∞}(ψ)/(2u))`. Stronger than DLMF (explicit bound). -/
@[dlmf 2.8.E12, dlmf 2.8.E13, dlmf 2.8.ii]
theorem caseI_recessive_expansion {a u : ℝ} (hu : 0 < u) {ψ : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Ioi a)) (hψi : ∀ c, a < c → IntegrableOn (fun t => |ψ t|) (Ioi c))
    {n : ℕ} {As Ad Ad2 : ℕ → ℝ → ℝ}
    (hAs : ∀ s < n, ∀ x, a < x → HasDerivAt (As s) (Ad s x) x)
    (hAd : ∀ s < n, ∀ x, a < x → HasDerivAt (Ad s) (Ad2 s x) x)
    (hAd2c : ∀ s < n, ContinuousOn (Ad2 s) (Ioi a)) (h0 : ∀ x, a < x → Ad 0 x = 0)
    (hrec : ∀ s < n, ∀ x, a < x → Ad (s + 1) x = -(1 / 2) * Ad2 s x + 1 / 2 * ψ x * As s x)
    (hAni : ∀ c, a < c → IntegrableOn (fun t => |Ad n t|) (Ioi c)) :
    ∃ ε ε' W' : ℝ → ℝ, ∀ x, a < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => Real.exp (-(u * y)) *
        (∑ s ∈ Finset.range n, (-1) ^ s * As s y / u ^ s + ε y)) (W' x) x ∧
      HasDerivAt W' ((u ^ 2 + ψ x) * (Real.exp (-(u * x)) *
        (∑ s ∈ Finset.range n, (-1) ^ s * As s x / u ^ s + ε x))) x ∧
      |ε x| ≤ (∫ t in Ioi x, |Ad n t|) / u ^ n *
        Real.exp ((∫ t in Ioi x, |ψ t|) / (2 * u)) := by
  obtain ⟨ε, ε', W', H⟩ := exists_solution_expansion_exp (a := a) hu
    (A := fun _ => 1) (A' := fun _ => 0) (A'' := fun _ => 0) (ξ := id) (g := ψ)
    (fun _ _ => one_ne_zero) (fun x _ => hasDerivAt_const x 1) (fun x _ => hasDerivAt_const x 0)
    continuousOn_const hψ (fun x _ => by simpa using hasDerivAt_id x)
    (fun c hc => by simpa using hψi c hc) hAs hAd hAd2c h0
    (fun s hs x hx => by rw [hrec s hs x hx]; ring) hAni
  refine ⟨ε, ε', W', fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := H x hx
  simp only [lgSeries_eq_sum_neg_one_pow, one_mul, id, one_pow, inv_one, mul_one] at h2 h3
  refine ⟨h1, h2, h3, ?_⟩
  have hV : (∫ t in Ioi x, |(1 : ℝ) * 0 - ψ t * 1 ^ 2|) = ∫ t in Ioi x, |ψ t| := by
    congr 1; funext t; simp
  rw [hV] at h4
  exact h4

/-! ### §2.8(iii) Case II: simple turning point -/

/-- DLMF 2.8.14–2.8.18 (Case II, simple turning point): for `W'' = (u²ξ + ψ(ξ)) W` on
`(α₁, α₂)`, `α₁ < 0 < α₂`, `ψ` smooth, with coefficients as in 2.8.17–2.8.18 and finite
variations `𝒱(|ξ|^{1/2} B_0)`, `𝒱(|ξ|^{1/2} B_{n-1})`, there are solutions
`W_{n,1} = Ai(u^{2/3}ξ)(∑_{s<n} A_s u^{-2s} + O(u^{1-2n}))
  + Ai'(u^{2/3}ξ)(∑_{s<n-1} B_s u^{-2s-4/3} + O(u^{1-2n}))`
and the same with `Bi` (`W_{n,2}`), uniformly in `ξ`. -/
@[dlmf 2.8.E14, dlmf 2.8.E15, dlmf 2.8.E16, dlmf 2.8.E17, dlmf 2.8.E18, dlmf 2.8.iii]
theorem caseII_airy_expansion {α₁ α₂ : ℝ} (h₁ : α₁ < 0) (h₂ : 0 < α₂) {ψ : ℝ → ℝ}
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ (Ioo α₁ α₂)) {A Ad Ad2 B Bd Bd2 : ℕ → ℝ → ℝ}
    (hc : IsAiryCoeffs ψ α₁ α₂ A Ad Ad2 B Bd Bd2) {n : ℕ} (hn : 1 ≤ n)
    (hV : ∀ s ∈ ({0, n - 1} : Finset ℕ), IntegrableOn
      (fun ξ => |deriv (fun v => √|v| * B s v) ξ|) (Ioo α₁ α₂)) :
    ∃ W₁ W₂ : ℝ → ℝ → ℂ, ∃ e₁ e₂ e₃ e₄ : ℝ → ℝ → ℂ,
      (∀ u, 0 < u → ∃ W₁' W₂' : ℝ → ℂ, ∀ ξ ∈ Ioo α₁ α₂,
        HasDerivAt (W₁ u) (W₁' ξ) ξ ∧ HasDerivAt W₁' ((u ^ 2 * ξ + ψ ξ : ℝ) * W₁ u ξ) ξ ∧
        HasDerivAt (W₂ u) (W₂' ξ) ξ ∧ HasDerivAt W₂' ((u ^ 2 * ξ + ψ ξ : ℝ) * W₂ u ξ) ξ) ∧
      (∀ u, 0 < u → ∀ ξ ∈ Ioo α₁ α₂,
        W₁ u ξ = DLMF.Airy.airyAi ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            ((∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) + e₁ u ξ) +
          DLMF.Airy.airyAiDeriv ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            ((∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 4 / 3 : ℝ) : ℝ) + e₂ u ξ) ∧
        W₂ u ξ = DLMF.Airy.airyBi ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            ((∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) + e₃ u ξ) +
          DLMF.Airy.airyBiDeriv ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            ((∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 4 / 3 : ℝ) : ℝ) + e₄ u ξ)) ∧
      ∃ C U₀ : ℝ, ∀ u, U₀ ≤ u → ∀ ξ ∈ Ioo α₁ α₂,
        ‖e₁ u ξ‖ ≤ C / u ^ (2 * n - 1) ∧ ‖e₂ u ξ‖ ≤ C / u ^ (2 * n - 1) ∧
        ‖e₃ u ξ‖ ≤ C / u ^ (2 * n - 1) ∧ ‖e₄ u ξ‖ ≤ C / u ^ (2 * n - 1) := by
  sorry

/-- DLMF 2.8.22–2.8.23 (Case II with envelope functions): with the solutions of
`caseII_airy_expansion`, as `u → ∞` uniformly in `ξ ∈ (α₁, α₂)`,
`W_{n,1} = Ai(u^{2/3}ξ) ∑_{s<n} A_s u^{-2s} + Ai'(u^{2/3}ξ) ∑_{s<n-1} B_s u^{-2s-4/3}
  + envelopeAi(u^{2/3}ξ) O(u^{1-2n})`, and the same with `Bi`, `envelopeBi`. -/
@[dlmf 2.8.E22, dlmf 2.8.E23]
theorem caseII_airy_envelope {α₁ α₂ : ℝ} (h₁ : α₁ < 0) (h₂ : 0 < α₂) {ψ : ℝ → ℝ}
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ (Ioo α₁ α₂)) {A Ad Ad2 B Bd Bd2 : ℕ → ℝ → ℝ}
    (hc : IsAiryCoeffs ψ α₁ α₂ A Ad Ad2 B Bd Bd2) {n : ℕ} (hn : 1 ≤ n)
    (hV : ∀ s ∈ ({0, n - 1} : Finset ℕ), IntegrableOn
      (fun ξ => |deriv (fun v => √|v| * B s v) ξ|) (Ioo α₁ α₂)) :
    ∃ W₁ W₂ : ℝ → ℝ → ℂ,
      (∀ u, 0 < u → ∃ W₁' W₂' : ℝ → ℂ, ∀ ξ ∈ Ioo α₁ α₂,
        HasDerivAt (W₁ u) (W₁' ξ) ξ ∧ HasDerivAt W₁' ((u ^ 2 * ξ + ψ ξ : ℝ) * W₁ u ξ) ξ ∧
        HasDerivAt (W₂ u) (W₂' ξ) ξ ∧ HasDerivAt W₂' ((u ^ 2 * ξ + ψ ξ : ℝ) * W₂ u ξ) ξ) ∧
      ∃ C U₀ : ℝ, ∀ u, U₀ ≤ u → ∀ ξ ∈ Ioo α₁ α₂,
        ‖W₁ u ξ - (DLMF.Airy.airyAi ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            (∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) +
          DLMF.Airy.airyAiDeriv ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            (∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 4 / 3 : ℝ) : ℝ))‖ ≤
          envelopeAi (u ^ (2 / 3 : ℝ) * ξ) * (C / u ^ (2 * n - 1)) ∧
        ‖W₂ u ξ - (DLMF.Airy.airyBi ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            (∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) +
          DLMF.Airy.airyBiDeriv ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            (∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 4 / 3 : ℝ) : ℝ))‖ ≤
          envelopeBi (u ^ (2 / 3 : ℝ) * ξ) * (C / u ^ (2 * n - 1)) := by
  sorry

/-! ### §2.8(iv) Case III: simple pole -/

/-- DLMF 2.8.24–2.8.28 (Case III, `ξ ∈ (0, α₂)`): for
`W'' = (u²/(4ξ) + (ν²-1)/(4ξ²) + ψ(ξ)/ξ) W`, `ν ≥ 0`, with coefficients as in 2.8.27–2.8.28
and finite variations `𝒱_{0,α₂}(ξ^{1/2} B_0)`, `𝒱_{0,α₂}(ξ^{1/2} B_{n-1})`, there are solutions
`W_{n,1} = ξ^{1/2} I_ν(uξ^{1/2}) ∑_{s<n} A_s u^{-2s} + ξ I_{ν+1}(uξ^{1/2}) ∑_{s<n-1} B_s u^{-2s-1}
  + ξ^{1/2} I_ν(uξ^{1/2}) O(u^{1-2n})` and
`W_{n,2} = ξ^{1/2} K_ν(uξ^{1/2}) ∑ A_s u^{-2s} - ξ K_{ν+1}(uξ^{1/2}) ∑ B_s u^{-2s-1}
  + ξ^{1/2} K_ν(uξ^{1/2}) O(u^{1-2n})`, uniformly in `ξ ∈ (0, α₂)`. -/
@[dlmf 2.8.E24, dlmf 2.8.E25, dlmf 2.8.E26, dlmf 2.8.E27, dlmf 2.8.E28, dlmf 2.8.iv]
theorem caseIII_bessel_expansion_pos {α₁ α₂ ν : ℝ} (h₁ : α₁ < 0) (h₂ : 0 < α₂) (hν : 0 ≤ ν)
    {ψ : ℝ → ℝ} (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ (Ioo α₁ α₂)) {A Ad B Bd Bd2 : ℕ → ℝ → ℝ}
    (hc : IsBesselCoeffs ψ ν α₁ α₂ A Ad B Bd Bd2) {n : ℕ} (hn : 1 ≤ n)
    (hV : ∀ s ∈ ({0, n - 1} : Finset ℕ), IntegrableOn
      (fun ξ => |deriv (fun v => √v * B s v) ξ|) (Ioo 0 α₂)) :
    ∃ W₁ W₂ : ℝ → ℝ → ℂ,
      (∀ u, 0 < u → ∃ W₁' W₂' : ℝ → ℂ, ∀ ξ ∈ Ioo 0 α₂,
        HasDerivAt (W₁ u) (W₁' ξ) ξ ∧ HasDerivAt W₁'
          ((u ^ 2 / (4 * ξ) + (ν ^ 2 - 1) / (4 * ξ ^ 2) + ψ ξ / ξ : ℝ) * W₁ u ξ) ξ ∧
        HasDerivAt (W₂ u) (W₂' ξ) ξ ∧ HasDerivAt W₂'
          ((u ^ 2 / (4 * ξ) + (ν ^ 2 - 1) / (4 * ξ ^ 2) + ψ ξ / ξ : ℝ) * W₂ u ξ) ξ) ∧
      ∃ C U₀ : ℝ, ∀ u, U₀ ≤ u → ∀ ξ ∈ Ioo 0 α₂,
        ‖W₁ u ξ - ((√ξ : ℝ) * DLMF.Bessel.besselI ν (u * √ξ : ℝ) *
            (∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) +
          (ξ : ℂ) * DLMF.Bessel.besselI (ν + 1) (u * √ξ : ℝ) *
            (∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 1) : ℝ))‖ ≤
          ‖(√ξ : ℝ) * DLMF.Bessel.besselI ν (u * √ξ : ℝ)‖ * (C / u ^ (2 * n - 1)) ∧
        ‖W₂ u ξ - ((√ξ : ℝ) * DLMF.Bessel.besselK ν (u * √ξ : ℝ) *
            (∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) -
          (ξ : ℂ) * DLMF.Bessel.besselK (ν + 1) (u * √ξ : ℝ) *
            (∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 1) : ℝ))‖ ≤
          ‖(√ξ : ℝ) * DLMF.Bessel.besselK ν (u * √ξ : ℝ)‖ * (C / u ^ (2 * n - 1)) := by
  sorry

/-- DLMF 2.8.29–2.8.31 (Case III, `ξ ∈ (α₁, 0)`): with coefficients as in 2.8.31 and 2.8.28 and
finite variations `𝒱_{α₁,0}(|ξ|^{1/2} B_0)`, `𝒱_{α₁,0}(|ξ|^{1/2} B_{n-1})`, there are solutions
`W_{n,3} = |ξ|^{1/2} J_ν(u|ξ|^{1/2}) (∑_{s<n} A_s u^{-2s} + O(u^{1-2n}))
  - |ξ| J_{ν+1}(u|ξ|^{1/2}) (∑_{s<n-1} B_s u^{-2s-1} + O(u^{2-2n}))`
and the same with `Y_ν`, `Y_{ν+1}` (`W_{n,4}`), uniformly in `ξ ∈ (α₁, 0)`. -/
@[dlmf 2.8.E29, dlmf 2.8.E30, dlmf 2.8.E31]
theorem caseIII_bessel_expansion_neg {α₁ α₂ ν : ℝ} (h₁ : α₁ < 0) (h₂ : 0 < α₂) (hν : 0 ≤ ν)
    {ψ : ℝ → ℝ} (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ (Ioo α₁ α₂)) {A Ad B Bd Bd2 : ℕ → ℝ → ℝ}
    (hc : IsBesselCoeffs ψ ν α₁ α₂ A Ad B Bd Bd2) {n : ℕ} (hn : 1 ≤ n)
    (hV : ∀ s ∈ ({0, n - 1} : Finset ℕ), IntegrableOn
      (fun ξ => |deriv (fun v => √|v| * B s v) ξ|) (Ioo α₁ 0)) :
    ∃ W₃ W₄ : ℝ → ℝ → ℂ, ∃ e₁ e₂ e₃ e₄ : ℝ → ℝ → ℂ,
      (∀ u, 0 < u → ∃ W₃' W₄' : ℝ → ℂ, ∀ ξ ∈ Ioo α₁ 0,
        HasDerivAt (W₃ u) (W₃' ξ) ξ ∧ HasDerivAt W₃'
          ((u ^ 2 / (4 * ξ) + (ν ^ 2 - 1) / (4 * ξ ^ 2) + ψ ξ / ξ : ℝ) * W₃ u ξ) ξ ∧
        HasDerivAt (W₄ u) (W₄' ξ) ξ ∧ HasDerivAt W₄'
          ((u ^ 2 / (4 * ξ) + (ν ^ 2 - 1) / (4 * ξ ^ 2) + ψ ξ / ξ : ℝ) * W₄ u ξ) ξ) ∧
      (∀ u, 0 < u → ∀ ξ ∈ Ioo α₁ 0,
        W₃ u ξ = (√|ξ| : ℝ) * Complex.besselJ ν (u * √|ξ| : ℝ) *
            ((∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) + e₁ u ξ) -
          ((|ξ| : ℝ) : ℂ) * Complex.besselJ (ν + 1) (u * √|ξ| : ℝ) *
            ((∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 1) : ℝ) + e₂ u ξ) ∧
        W₄ u ξ = (√|ξ| : ℝ) * DLMF.Bessel.besselY ν (u * √|ξ| : ℝ) *
            ((∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) + e₃ u ξ) -
          ((|ξ| : ℝ) : ℂ) * DLMF.Bessel.besselY (ν + 1) (u * √|ξ| : ℝ) *
            ((∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 1) : ℝ) + e₄ u ξ)) ∧
      ∃ C U₀ : ℝ, ∀ u, U₀ ≤ u → ∀ ξ ∈ Ioo α₁ 0,
        ‖e₁ u ξ‖ ≤ C / u ^ (2 * n - 1) ∧ ‖e₂ u ξ‖ ≤ C / u ^ (2 * n - 2) ∧
        ‖e₃ u ξ‖ ≤ C / u ^ (2 * n - 1) ∧ ‖e₄ u ξ‖ ≤ C / u ^ (2 * n - 2) := by
  sorry

/-- DLMF 2.8.35–2.8.36 (Case III, `ξ ∈ (α₁, 0)`, with envelope functions): with the solutions of
`caseIII_bessel_expansion_neg`, uniformly in `ξ ∈ (α₁, 0)` as `u → ∞`,
`W_{n,3} = |ξ|^{1/2} J_ν(u|ξ|^{1/2}) ∑ A_s u^{-2s} - |ξ| J_{ν+1}(u|ξ|^{1/2}) ∑ B_s u^{-2s-1}
  + |ξ|^{1/2} env J_ν(u|ξ|^{1/2}) O(u^{1-2n})`, and the same with `Y`, `env Y_ν`. -/
@[dlmf 2.8.E35, dlmf 2.8.E36]
theorem caseIII_bessel_envelope {α₁ α₂ ν : ℝ} (h₁ : α₁ < 0) (h₂ : 0 < α₂) (hν : 0 ≤ ν)
    {ψ : ℝ → ℝ} (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ (Ioo α₁ α₂)) {A Ad B Bd Bd2 : ℕ → ℝ → ℝ}
    (hc : IsBesselCoeffs ψ ν α₁ α₂ A Ad B Bd Bd2) {n : ℕ} (hn : 1 ≤ n)
    (hV : ∀ s ∈ ({0, n - 1} : Finset ℕ), IntegrableOn
      (fun ξ => |deriv (fun v => √|v| * B s v) ξ|) (Ioo α₁ 0)) :
    ∃ W₃ W₄ : ℝ → ℝ → ℂ,
      (∀ u, 0 < u → ∃ W₃' W₄' : ℝ → ℂ, ∀ ξ ∈ Ioo α₁ 0,
        HasDerivAt (W₃ u) (W₃' ξ) ξ ∧ HasDerivAt W₃'
          ((u ^ 2 / (4 * ξ) + (ν ^ 2 - 1) / (4 * ξ ^ 2) + ψ ξ / ξ : ℝ) * W₃ u ξ) ξ ∧
        HasDerivAt (W₄ u) (W₄' ξ) ξ ∧ HasDerivAt W₄'
          ((u ^ 2 / (4 * ξ) + (ν ^ 2 - 1) / (4 * ξ ^ 2) + ψ ξ / ξ : ℝ) * W₄ u ξ) ξ) ∧
      ∃ C U₀ : ℝ, ∀ u, U₀ ≤ u → ∀ ξ ∈ Ioo α₁ 0,
        ‖W₃ u ξ - ((√|ξ| : ℝ) * Complex.besselJ ν (u * √|ξ| : ℝ) *
            (∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) -
          ((|ξ| : ℝ) : ℂ) * Complex.besselJ (ν + 1) (u * √|ξ| : ℝ) *
            (∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 1) : ℝ))‖ ≤
          √|ξ| * envelopeJ ν (u * √|ξ|) * (C / u ^ (2 * n - 1)) ∧
        ‖W₄ u ξ - ((√|ξ| : ℝ) * DLMF.Bessel.besselY ν (u * √|ξ| : ℝ) *
            (∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) -
          ((|ξ| : ℝ) : ℂ) * DLMF.Bessel.besselY (ν + 1) (u * √|ξ| : ℝ) *
            (∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 1) : ℝ))‖ ≤
          √|ξ| * envelopeY ν (u * √|ξ|) * (C / u ^ (2 * n - 1)) := by
  sorry

end DLMF.AsymptoticApproximations
