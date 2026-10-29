/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Mellin.Defs
public import DLMF.AlgebraicAnalytic.Complex.Defs
public import DLMF.Gamma.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Bessel

/-!
# The Mellin-transform example of DLMF §2.5(i): `∫₀^∞ J_ν²(xt)/(1 + t) dt`

For `ν > -½` and `x > 0` let `I(x) = ∫₀^∞ J_ν²(xt)/(1 + t) dt` (2.5.8), a Mellin convolution
with `f(t) = 1/(1 + t)` and `h(t) = J_ν²(t)`. With `A = besselSqMellinKernel ν`,
`aₙ = A(n)` and `bₙ = -A'(n)` (`Mellin.Defs`):

* 2.5.9: `𝓜f(1 - z) = π/sin(πz)` (proved);
* 2.5.10: `𝓜h(z) = A(z) π/sin(πz)`, here in the equivalent form
  `2^{z-1}Γ(ν + z/2)Γ(1 - z)/(Γ²(1 - z/2)Γ(1 + ν - z/2))`, valid also at `z = 0`, where the
  printed form is `0 · ∞` (the DLMF form is derived for `sin(πz) ≠ 0`);
* 2.5.11–2.5.13: residues at the double poles `z = n`;
* 2.5.14: `|Γ(x + iy)| ∼ √(2π) e^{-π|y|/2} |y|^{x-1/2}` (pointwise forms proved from 5.11.9);
* 2.5.15–2.5.16: the expansion of `I(x)` as `x → ∞`; `aₛ = bₛ = 0` for even `s ≥ 2` (proved).

**Erratum (signs in 2.5.11, 2.5.15, 2.5.16).** The residue of
`x^{-z} 𝓜f(1 - z) 𝓜h(z) = x^{-z} A(z) π²/sin²(πz)` at `z = n` is
`d/dz[x^{-z} A(z)]_{z=n} = -(aₙ ln x + bₙ) x^{-n}`, not `+(aₙ ln x + bₙ) x^{-n}` as printed in
2.5.11. Shifting the contour to the right (2.5.35) then gives
`I(x) = +∑_{s=1}^{2n} (aₛ ln x + bₛ) x^{-s} + O(x^{-2n-1+ε})`, and in 2.5.16 `cₛ = a_{2s+1}`,
`dₛ = b_{2s+1}`. Numerical check (`ν = 0`, `x = 20`): `I(x) = 0.089945`, while
`(a₁ ln x + b₁)/x = (ln 20 + 3 ln 2 + γ)/(20π) = 0.089961`; the printed sign gives `-0.089961`.
The sum in 2.5.15 is taken over `1 ≤ s ≤ 2n` here: the term `s = 0` of DLMF lies outside the
strip crossed by the contour (and `b₀ = -A'(0)` is not zero in general; it is `-1/(2ν)` for
`ν > 0`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology Real

namespace DLMF.AsymptoticApproximations

/-- DLMF 2.5.9: for `f(t) = 1/(1 + t)`, `𝓜f(1 - z) = π/sin(πz)`, `0 < ℜz < 1`. -/
@[dlmf 2.5.E9]
theorem mellin_inv_one_add_one_sub {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    mellin (fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) (1 - z) = π / Complex.sin (π * z) := by
  have hs : 0 < (1 - z).re := by simp; linarith
  have hsa : (1 - z).re < (1 : ℂ).re := by simp; linarith
  have h := DLMF.Gamma.mellin_one_add_cpow_neg hs hsa
  simp only [cpow_neg_one, Complex.Gamma_one, div_one, sub_sub_cancel] at h
  rw [h, mul_comm (Complex.Gamma (1 - z)), Complex.Gamma_mul_Gamma_one_sub]

/-- DLMF 2.5.10: for `ν > -½` and `-2ν < ℜz < 1`, the Mellin transform of `h(t) = J_ν²(t)` is
`2^{z-1}Γ(ν + z/2)Γ(1 - z)/(Γ²(1 - z/2)Γ(1 + ν - z/2))`. This equals DLMF's
`2^{z-1}Γ(ν + z/2)/(Γ²(1 - z/2)Γ(1 + ν - z/2)Γ(z)) · π/sin(πz)` where `sin(πz) ≠ 0`
(`mellin_besselJ_sq_eq_kernel`) and is the continuous extension of it to `z = 0`. -/
@[dlmf 2.5.E10]
theorem mellin_besselJ_sq {ν : ℝ} (hν : -1 / 2 < ν) {z : ℂ} (h0 : -2 * ν < z.re)
    (h1 : z.re < 1) :
    mellin (fun t : ℝ => Complex.besselJ ν t ^ 2) z =
      2 ^ (z - 1) * Complex.Gamma (ν + z / 2) * Complex.Gamma (1 - z) /
        (Complex.Gamma (1 - z / 2) ^ 2 * Complex.Gamma (1 + ν - z / 2)) := by
  sorry

/-- DLMF 2.5.10 in the printed form: `𝓜h(z) = A(z) π/sin(πz)` for `-2ν < ℜz < 1`,
`sin(πz) ≠ 0`, with `A = besselSqMellinKernel ν`. -/
@[dlmf 2.5.E10]
theorem mellin_besselJ_sq_eq_kernel {ν : ℝ} (hν : -1 / 2 < ν) {z : ℂ} (h0 : -2 * ν < z.re)
    (h1 : z.re < 1) (hs : Complex.sin (π * z) ≠ 0) :
    mellin (fun t : ℝ => Complex.besselJ ν t ^ 2) z =
      besselSqMellinKernel ν z * (π / Complex.sin (π * z)) := by
  have hpi : (π : ℂ) / Complex.sin (π * z) ≠ 0 :=
    div_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero) hs
  have hG : Complex.Gamma z ≠ 0 := fun h => by
    have := Complex.Gamma_mul_Gamma_one_sub z
    rw [h, zero_mul] at this
    exact hpi this.symm
  have hΓ1 : Complex.Gamma (1 - z) = π / Complex.sin (π * z) / Complex.Gamma z := by
    rw [← Complex.Gamma_mul_Gamma_one_sub z]
    field_simp
  rw [mellin_besselJ_sq hν h0 h1, hΓ1, besselSqMellinKernel]
  simp only [div_eq_mul_inv, mul_inv, inv_pow]
  ring

/-- DLMF 2.5.11 (corrected sign; see the module docstring): for `ν > -½`, `x > 0` and
`n ≥ 1`, the residue of `x^{-z} 𝓜f(1 - z) 𝓜h(z) = x^{-z} (π/sin(πz)) A(z) (π/sin(πz))` at the
double pole `z = n` is `-(aₙ ln x + bₙ) x^{-n}`; DLMF prints `+(aₙ ln x + bₙ) x^{-n}`. -/
@[dlmf 2.5.E11]
theorem residueAt_besselSq {ν : ℝ} (hν : -1 / 2 < ν) {x : ℝ} (hx : 0 < x) {n : ℕ}
    (hn : 1 ≤ n) :
    DLMF.AlgebraicAnalytic.residueAt (fun z => (x : ℂ) ^ (-z) *
        ((π / Complex.sin (π * z)) * (besselSqMellinKernel ν z * (π / Complex.sin (π * z))))) n =
      -(besselSqMellinA ν n * Real.log x + besselSqMellinB ν n) * ((x : ℂ) ^ n)⁻¹ := by
  sorry

/-- Differentiating the Mellin kernel away from Gamma poles gives its value times
the sum of the logarithmic derivatives of its five factors. -/
lemma hasDerivAt_besselSqMellinKernel (ν : ℝ) {z : ℂ}
    (h₁ : ∀ m : ℕ, (ν + z / 2 : ℂ) ≠ -m)
    (h₂ : ∀ m : ℕ, (1 - z / 2 : ℂ) ≠ -m)
    (h₃ : ∀ m : ℕ, (1 + ν - z / 2 : ℂ) ≠ -m)
    (h₄ : ∀ m : ℕ, z ≠ -m) :
    HasDerivAt (besselSqMellinKernel ν)
      (besselSqMellinKernel ν z * ((Real.log 2 : ℂ) + digamma (ν + z / 2) / 2 +
        digamma (1 - z / 2) + digamma (1 + ν - z / 2) / 2 - digamma z)) z := by
  have hd := (hasDerivAt_id z).div_const (2 : ℂ)
  have hG₁ := (Complex.differentiableAt_Gamma _ h₁).hasDerivAt.comp z
    (hd.const_add (ν : ℂ))
  have hG₂ := (Complex.differentiableAt_Gamma _ h₂).hasDerivAt.comp z
    ((hasDerivAt_const z (1 : ℂ)).sub hd)
  have hG₃ := (Complex.differentiableAt_Gamma _ h₃).hasDerivAt.comp z
    ((hasDerivAt_const z (1 + ν : ℂ)).sub hd)
  have hp := ((hasDerivAt_id z).sub_const 1).const_cpow (c := (2 : ℂ))
    (Or.inl (by norm_num))
  have hΓ₂ := Complex.Gamma_ne_zero h₂
  have hΓ₃ := Complex.Gamma_ne_zero h₃
  have hΓ₄ := Complex.Gamma_ne_zero h₄
  have hD := (((hp.mul hG₁).mul ((hG₂.inv hΓ₂).pow 2)).mul (hG₃.inv hΓ₃)).mul
    ((Complex.differentiableAt_Gamma _ h₄).hasDerivAt.inv hΓ₄)
  apply hD.congr_deriv
  dsimp only [besselSqMellinKernel, Function.comp_def, id_eq, Pi.mul_apply,
    Pi.inv_apply, Pi.pow_apply, Pi.sub_apply]
  simp only [Complex.digamma_def, logDeriv_apply, inv_eq_one_div]
  rw [show Complex.log 2 = (Real.log 2 : ℂ) from (Complex.ofReal_log (by norm_num)).symm]
  have hΓ₁ := Complex.Gamma_ne_zero h₁
  generalize Gamma (ν + z / 2) = A at hΓ₁ ⊢
  generalize Gamma (1 - z / 2) = B at hΓ₂ ⊢
  generalize Gamma (1 + ν - z / 2) = C at hΓ₃ ⊢
  generalize Gamma z = D at hΓ₄ ⊢
  field_simp
  ring_nf
  field_simp
  ring

/-- DLMF 2.5.13 in DLMF's form: if `n` is odd and `1 + ν - n/2` is not a pole of `Γ`, then
`bₙ = -aₙ(ln 2 + ½ψ(ν + n/2) + ψ(1 - n/2) + ½ψ(1 + ν - n/2) - ψ(n))`. -/
@[dlmf 2.5.E13]
theorem besselSqMellinB_eq_digamma {ν : ℝ} (hν : -1 / 2 < ν) {n : ℕ} (hn : Odd n)
    (hpole : ∀ m : ℕ, (1 + ν - n / 2 : ℂ) ≠ -m) :
    besselSqMellinB ν n = -besselSqMellinA ν n * (Real.log 2 + digamma (ν + n / 2) / 2 +
      digamma (1 - n / 2) + digamma (1 + ν - n / 2) / 2 - digamma n) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn.pos
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn.pos
  have hreg (z : ℂ) (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -m := by
    intro m hm
    have he := congrArg Complex.re hm
    simp only [neg_re, natCast_re] at he
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have h₁ : ∀ m : ℕ, (ν + n / 2 : ℂ) ≠ -m := hreg _ (by
    norm_num
    linarith)
  have h₂ : ∀ m : ℕ, (1 - n / 2 : ℂ) ≠ -m := by
    intro m hm
    have he := congrArg Complex.re hm
    norm_num at he
    have hn2 : n = 2 + 2 * m := by
      exact_mod_cast (show (n : ℝ) = 2 + 2 * m by linarith)
    obtain ⟨k, hk⟩ := hn
    omega
  have h₄ : ∀ m : ℕ, (n : ℂ) ≠ -m := hreg _ (by simpa using hn0)
  rw [besselSqMellinB, (hasDerivAt_besselSqMellinKernel ν h₁ h₂ hpole h₄).deriv,
    besselSqMellinA]
  ring

/-- DLMF §2.5(i), after 2.5.15: `aₛ = 0` for even `s` (`1/Γ(1 - s/2) = 0` for even `s ≥ 2` and
`1/Γ(s) = 0` for `s = 0`). -/
@[dlmf 2.5.E12, dlmf 2.5.i]
theorem besselSqMellinA_two_mul (ν : ℝ) (k : ℕ) : besselSqMellinA ν (2 * k) = 0 := by
  unfold besselSqMellinA besselSqMellinKernel
  rcases k with _ | k
  · simp [Complex.Gamma_zero]
  · have h : (1 : ℂ) - ((2 * (k + 1) : ℕ) : ℂ) / 2 = -(k : ℂ) := by push_cast; ring
    rw [h, Complex.Gamma_neg_nat_eq_zero]
    simp

/-- Helper: `z ↦ 1/Γ(w(z))` is differentiable when `w` is. -/
private lemma g2a_differentiable_inv_Gamma {w : ℂ → ℂ} (hw : Differentiable ℂ w) :
    Differentiable ℂ fun z => (Complex.Gamma (w z))⁻¹ :=
  Complex.differentiable_one_div_Gamma.comp hw

/-- DLMF §2.5(i), after 2.5.15: `bₛ = -A'(s) = 0` for even `s ≥ 2`, since `A` has the factor
`(1/Γ(1 - z/2))²` with a double zero at `z = s`. -/
@[dlmf 2.5.E13, dlmf 2.5.i]
theorem besselSqMellinB_two_mul {ν : ℝ} (hν : -1 / 2 < ν) (k : ℕ) :
    besselSqMellinB ν (2 * (k + 1)) = 0 := by
  set p : ℂ := ((2 * (k + 1) : ℕ) : ℂ) with hp
  set u : ℂ → ℂ := fun z => (Complex.Gamma (1 - z / 2))⁻¹ with hu
  set G : ℂ → ℂ := fun z => (2 : ℂ) ^ (z - 1) * Complex.Gamma (ν + z / 2) *
    (Complex.Gamma (1 + ν - z / 2))⁻¹ * (Complex.Gamma z)⁻¹ with hGdef
  have hk : besselSqMellinKernel ν = fun z => u z ^ 2 * G z := by
    funext z
    simp only [besselSqMellinKernel, hu, hGdef]
    ring
  have hu0 : u p = 0 := by
    have h : (1 : ℂ) - p / 2 = -(k : ℂ) := by rw [hp]; push_cast; ring
    simp only [hu, h, Complex.Gamma_neg_nat_eq_zero, inv_zero]
  have hud : DifferentiableAt ℂ u p :=
    (g2a_differentiable_inv_Gamma (by fun_prop)) p
  have hΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (ν + z / 2)) p := by
    refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).comp p (by fun_prop)
    have hre := congrArg Complex.re hm
    simp [hp] at hre
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hGd : DifferentiableAt ℂ G p := by
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (z - 1)) p :=
      (differentiableAt_id.sub_const 1).const_cpow (Or.inl two_ne_zero)
    exact ((h2.mul hΓ).mul ((g2a_differentiable_inv_Gamma (by fun_prop)) p)).mul
      ((g2a_differentiable_inv_Gamma differentiable_id) p)
  have hd := ((hud.hasDerivAt.pow 2).mul hGd.hasDerivAt).deriv
  unfold besselSqMellinB
  rw [hk]
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hd ⊢
  rw [show ((2 : ℂ) * ((k + 1 : ℕ) : ℂ)) = p by rw [hp]; push_cast; ring,
    show (fun z => u z ^ 2 * G z) = u ^ 2 * G from rfl, hd]
  simp [Pi.pow_apply, hu0]

/-- DLMF 2.5.14 as `y → +∞` (pointwise in `x`): `|Γ(x + iy)| ∼ √(2π) |y|^{x-1/2} e^{-π|y|/2}`;
this is DLMF 5.11.9 (`DLMF.Gamma.norm_Gamma_imag_large`). -/
@[dlmf 2.5.E14]
theorem norm_Gamma_vertical_atTop (x : ℝ) :
    (fun y : ℝ => ‖Complex.Gamma (x + I * y)‖) ~[atTop]
      fun y => Real.sqrt (2 * π) * |y| ^ (x - 1 / 2) * Real.exp (-π * |y| / 2) :=
  DLMF.Gamma.norm_Gamma_imag_large

/-- DLMF 2.5.14 as `y → -∞` (pointwise in `x`), from the case `y → +∞` and
`Γ(z̄) = conj Γ(z)`. -/
@[dlmf 2.5.E14]
theorem norm_Gamma_vertical_atBot (x : ℝ) :
    (fun y : ℝ => ‖Complex.Gamma (x + I * y)‖) ~[atBot]
      fun y => Real.sqrt (2 * π) * |y| ^ (x - 1 / 2) * Real.exp (-π * |y| / 2) := by
  have h := (norm_Gamma_vertical_atTop x).comp_tendsto tendsto_neg_atBot_atTop
  refine (h.congr_left (Eventually.of_forall fun y => ?_)).congr_right
    (Eventually.of_forall fun y => ?_)
  · simp only [Function.comp_apply]
    rw [show (x : ℂ) + I * ((-y : ℝ) : ℂ) = (starRingEnd ℂ) ((x : ℂ) + I * y) by
      apply Complex.ext <;> simp, Complex.Gamma_conj, Complex.norm_conj]
  · simp [abs_neg]

/-- DLMF 2.5.14 (uniform form): `|Γ(x + iy)| = √(2π) e^{-π|y|/2} |y|^{x-1/2}(1 + o(1))` as
`y → ±∞`, uniformly for `x` in a bounded interval `[a, b]`. -/
@[dlmf 2.5.E14]
theorem norm_Gamma_vertical_uniform (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in cocompact ℝ, ∀ x ∈ Icc a b,
      |‖Complex.Gamma (x + I * y)‖ /
        (Real.sqrt (2 * π) * |y| ^ (x - 1 / 2) * Real.exp (-π * |y| / 2)) - 1| < ε := by
  sorry

/-- DLMF 2.5.8 and 2.5.15 (corrected sign; see the module docstring): for `ν > -½`,
`I(x) = ∫₀^∞ J_ν²(xt)/(1 + t) dt` satisfies, for `n = 0, 1, 2, …` and `0 < ε < 1`,
`I(x) = ∑_{s=1}^{2n} (aₛ ln x + bₛ) x^{-s} + O(x^{-2n-1+ε})` as `x → ∞`. -/
@[dlmf 2.5.E8, dlmf 2.5.E15]
theorem besselSq_integral_expansion {ν : ℝ} (hν : -1 / 2 < ν) (n : ℕ) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    (fun x : ℝ => (∫ t in Ioi 0, Complex.besselJ ν ((x * t : ℝ) : ℂ) ^ 2 / ((1 + t : ℝ) : ℂ)) -
        ∑ s ∈ range (2 * n), (besselSqMellinA ν (s + 1) * Real.log x +
          besselSqMellinB ν (s + 1)) * ((x : ℂ) ^ (s + 1))⁻¹)
      =O[atTop] fun x => x ^ (-(2 * n + 1 : ℝ) + ε) := by
  sorry

/-- Helper for 2.5.16: a sum over `1 ≤ s ≤ 2n` whose even terms vanish is a sum over the odd
indices. -/
private lemma g2a_sum_range_two_mul (g : ℕ → ℂ) (hg : ∀ k : ℕ, g (2 * k + 2) = 0) (n : ℕ) :
    ∑ s ∈ range (2 * n), g (s + 1) = ∑ j ∈ range n, g (2 * j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    have h0 : g (2 * n + 1 + 1) = 0 := hg n
    rw [h0, add_zero]

/-- DLMF 2.5.16 (corrected sign): since `aₛ = bₛ = 0` for even `s ≥ 2`,
`I(x) = ∑_{s=0}^{n-1} (cₛ ln x + dₛ) x^{-2s-1} + O(x^{-2n-1+ε})` with `cₛ = a_{2s+1}`,
`dₛ = b_{2s+1}` (DLMF prints `cₛ = -a_{2s+1}`, `dₛ = -b_{2s+1}`). -/
@[dlmf 2.5.E16]
theorem besselSq_integral_expansion_odd {ν : ℝ} (hν : -1 / 2 < ν) (n : ℕ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (fun x : ℝ => (∫ t in Ioi 0, Complex.besselJ ν ((x * t : ℝ) : ℂ) ^ 2 / ((1 + t : ℝ) : ℂ)) -
        ∑ s ∈ range n, (besselSqMellinA ν (2 * s + 1) * Real.log x +
          besselSqMellinB ν (2 * s + 1)) * ((x : ℂ) ^ (2 * s + 1))⁻¹)
      =O[atTop] fun x => x ^ (-(2 * n + 1 : ℝ) + ε) := by
  refine (besselSq_integral_expansion hν n hε0 hε1).congr_left fun x => ?_
  congr 1
  refine g2a_sum_range_two_mul (fun s => (besselSqMellinA ν s * Real.log x +
    besselSqMellinB ν s) * ((x : ℂ) ^ s)⁻¹) (fun k => ?_) n
  have ha := besselSqMellinA_two_mul ν (k + 1)
  have hb := besselSqMellinB_two_mul hν k
  rw [show 2 * k + 2 = 2 * (k + 1) by ring, ha, hb]
  simp

end DLMF.AsymptoticApproximations
