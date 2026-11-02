/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Mellin.Basic
public import DLMF.AsymptoticApproximations.Mellin.Residues
public import DLMF.AlgebraicAnalytic.Complex.Basic
public import DLMF.Gamma.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Bessel

/-!
# The Mellin-transform example of DLMF §2.5(i): `∫₀^∞ J_ν²(xt)/(1 + t) dt`

For `ν > -½` and `x > 0` let `I(x) = ∫₀^∞ J_ν²(xt)/(1 + t) dt` (2.5.8), a Mellin convolution
with `f(t) = 1/(1 + t)` and `h(t) = J_ν²(t)`, with `A = besselSqMellinKernel ν`, `aₙ = A(n)` and
`bₙ = -A'(n)` (`Mellin.Basic`).

## Main results

* `mellin_inv_one_add_one_sub`: `𝓜f(1 - z) = π/sin(πz)` (DLMF 2.5.9).
* `mellin_besselJ_sq`, `mellin_besselJ_sq_eq_kernel`: `𝓜h(z) = A(z) π/sin(πz)` (DLMF 2.5.10).
* `residueAt_besselSq`: residues at the double poles `z = n` (DLMF 2.5.11, corrected sign).
* `besselSqMellinB_eq_digamma`: DLMF 2.5.13 in DLMF's form.
* `besselSqMellinA_two_mul`, `besselSqMellinB_two_mul`: `aₛ = bₛ = 0` for even `s ≥ 2`.
* `norm_Gamma_vertical_atTop`, `norm_Gamma_vertical_atBot`, `norm_Gamma_vertical_uniform`:
  `|Γ(x + iy)| ∼ √(2π) e^{-π|y|/2} |y|^{x-1/2}` (DLMF 2.5.14, from 5.11.9).
* `besselSq_integral_expansion`, `besselSq_integral_expansion_odd`: the expansion of `I(x)` as
  `x → ∞` (DLMF 2.5.15–2.5.16, corrected sign).

## Implementation notes

`mellin_besselJ_sq` uses the equivalent form
`2^{z-1}Γ(ν + z/2)Γ(1 - z)/(Γ²(1 - z/2)Γ(1 + ν - z/2))`, valid also at `z = 0`, where the
printed form is `0 · ∞` (the DLMF form is derived for `sin(πz) ≠ 0`).

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

open MeasureTheory Set Filter Finset Asymptotics Complex Metric
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

/-- `Γ` is holomorphic at points of positive real part. -/
private lemma differentiableAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gamma s :=
  Complex.differentiableAt_Gamma s fun m h => by
    rw [h] at hs; simp at hs; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

/-- The kernel `A(z)` is holomorphic where `ℜ(ν + z/2) > 0`. -/
private lemma besselSqMellinKernel_differentiableAt (ν : ℝ) {z : ℂ}
    (hz : 0 < (ν + z / 2 : ℂ).re) : DifferentiableAt ℂ (besselSqMellinKernel ν) z := by
  unfold besselSqMellinKernel
  have h1 : DifferentiableAt ℂ (fun z : ℂ => Gamma (ν + z / 2)) z :=
    (differentiableAt_Gamma_of_re_pos hz).comp z (by fun_prop)
  have hi : ∀ w : ℂ → ℂ, DifferentiableAt ℂ w z →
      DifferentiableAt ℂ (fun z => (Gamma (w z))⁻¹) z := fun w hw =>
    (differentiable_one_div_Gamma (w z)).comp z hw |>.congr_of_eventuallyEq
      (Eventually.of_forall fun _ => by simp)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (z - 1)) z :=
    ((differentiableAt_id.sub_const 1).const_cpow (Or.inl (by norm_num)))
  exact (((h2.mul h1).mul ((hi _ (by fun_prop)).pow 2)).mul (hi _ (by fun_prop))).mul
    (hi _ differentiableAt_id)

/-- DLMF 2.5.11 (corrected sign; see the module docstring): for `ν > -½`, `x > 0` and
`n ≥ 1`, the residue of `x^{-z} 𝓜f(1 - z) 𝓜h(z) = x^{-z} (π/sin(πz)) A(z) (π/sin(πz))` at the
double pole `z = n` is `-(aₙ ln x + bₙ) x^{-n}`; DLMF prints `+(aₙ ln x + bₙ) x^{-n}`. -/
@[dlmf 2.5.E11]
theorem residueAt_besselSq {ν : ℝ} (hν : -1 / 2 < ν) {x : ℝ} (hx : 0 < x) {n : ℕ}
    (hn : 1 ≤ n) :
    DLMF.AlgebraicAnalytic.residueAt (fun z => (x : ℂ) ^ (-z) *
        ((π / Complex.sin (π * z)) * (besselSqMellinKernel ν z * (π / Complex.sin (π * z))))) n =
      -(besselSqMellinA ν n * Real.log x + besselSqMellinB ν n) * ((x : ℂ) ^ n)⁻¹ := by
  set R : ℝ := ν + 1 / 2 with hR
  have hR0 : 0 < R := by rw [hR]; linarith
  have hxne : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hA : ∀ z ∈ ball ((n : ℤ) : ℂ) R, DifferentiableAt ℂ (besselSqMellinKernel ν) z := by
    intro z hz
    apply besselSqMellinKernel_differentiableAt
    rw [mem_ball, dist_eq_norm] at hz
    have hre : |(z - ((n : ℤ) : ℂ)).re| < R := (abs_re_le_norm _).trans_lt hz
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [add_re, ofReal_re, div_ofNat_re]
    simp only [sub_re, Int.cast_natCast, natCast_re] at hre
    rw [abs_lt] at hre
    linarith
  have hu : DifferentiableOn ℂ (fun z => (x : ℂ) ^ (-z) * besselSqMellinKernel ν z)
      (ball ((n : ℤ) : ℂ) R) := fun z hz =>
    ((differentiableAt_id.neg.const_cpow (Or.inl hxne)).mul (hA z hz)).differentiableWithinAt
  have h := residueAt_mul_pi_div_sin_sq_add (f := fun z => (x : ℂ) ^ (-z) *
        ((π / Complex.sin (π * z)) * (besselSqMellinKernel ν z * (π / Complex.sin (π * z)))))
    (v := fun _ => 0) hR0 hu (differentiableOn_const 0) fun z _ _ => by
      simp only [zero_div, add_zero]; ring
  simp only [Int.cast_natCast, add_zero] at h
  rw [h]
  have hAn := hA _ (mem_ball_self hR0)
  simp only [Int.cast_natCast] at hAn
  have hd : HasDerivAt (fun z => (x : ℂ) ^ (-z) * besselSqMellinKernel ν z)
      ((x : ℂ) ^ (-(n : ℂ)) * Complex.log x * (-1) * besselSqMellinKernel ν n +
        (x : ℂ) ^ (-(n : ℂ)) * deriv (besselSqMellinKernel ν) n) n :=
    ((hasDerivAt_neg' (n : ℂ)).const_cpow (Or.inl hxne)).mul hAn.hasDerivAt
  rw [hd.deriv, besselSqMellinA, besselSqMellinB, ← ofReal_log hx.le, cpow_neg, cpow_natCast]
  ring

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
private lemma differentiable_inv_Gamma_comp {w : ℂ → ℂ} (hw : Differentiable ℂ w) :
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
    (differentiable_inv_Gamma_comp (by fun_prop)) p
  have hΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (ν + z / 2)) p := by
    refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).comp p (by fun_prop)
    have hre := congrArg Complex.re hm
    simp [hp] at hre
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hGd : DifferentiableAt ℂ G p := by
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (z - 1)) p :=
      (differentiableAt_id.sub_const 1).const_cpow (Or.inl two_ne_zero)
    exact ((h2.mul hΓ).mul ((differentiable_inv_Gamma_comp (by fun_prop)) p)).mul
      ((differentiable_inv_Gamma_comp differentiable_id) p)
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

/-- The Stirling ratio on a vertical line as one exponential (Binet's formula), `y > 0`. -/
private lemma norm_Gamma_vertical_ratio_eq (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖Complex.Gamma (x + I * y)‖ /
        (Real.sqrt (2 * π) * |y| ^ (x - 1 / 2) * Real.exp (-π * |y| / 2)) =
      Real.exp ((x - 1 / 2) * Real.log (‖(x : ℂ) + I * y‖ / y) +
        (π * y / 2 - x - y * arg ((x : ℂ) + I * y)) +
        (DLMF.Gamma.binetMu ((x : ℂ) + I * y)).re) := by
  set z : ℂ := (x : ℂ) + I * y with hz
  have hre : z.re = x := by simp [hz]
  have him : z.im = y := by simp [hz]
  have hzs : z ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr (by rw [him]; exact hy.ne'))
  have hr : 0 < ‖z‖ := norm_pos_iff.2 (slitPlane_ne_zero hzs)
  rw [DLMF.Gamma.norm_Gamma_eq_binet hzs, hre, him, abs_of_pos hy,
    Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hy, Real.log_div hr.ne' hy.ne']
  have hs : 0 < Real.sqrt (2 * π) := by positivity
  rw [div_eq_iff (by positivity)]
  simp only [mul_assoc, ← Real.exp_add]
  rw [mul_left_comm, ← Real.exp_add]
  congr 1
  ring_nf

/-- DLMF 2.5.14 (uniform form): `|Γ(x + iy)| = √(2π) e^{-π|y|/2} |y|^{x-1/2}(1 + o(1))` as
`y → ±∞`, uniformly for `x` in a bounded interval `[a, b]`. -/
@[dlmf 2.5.E14]
theorem norm_Gamma_vertical_uniform (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in cocompact ℝ, ∀ x ∈ Icc a b,
      |‖Complex.Gamma (x + I * y)‖ /
        (Real.sqrt (2 * π) * |y| ^ (x - 1 / 2) * Real.exp (-π * |y| / 2)) - 1| < ε := by
  set M : ℝ := |a| + |b| + 1 with hM
  have hM0 : 0 < M := by positivity
  have hxM : ∀ x ∈ Icc a b, |x| ≤ M := fun x hx => by
    rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;>
      linarith [hx.1, hx.2, abs_nonneg a, abs_nonneg b]
  set δ0 : ℝ := min 1 (ε / 2) with hδ0
  have hδ0p : 0 < δ0 := lt_min one_pos (by positivity)
  -- the `arcsin` estimate
  have hd : HasDerivAt Real.arcsin 1 0 := by
    simpa using Real.hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)
  have ho := hasDerivAt_iff_isLittleO_nhds_zero.1 hd
  simp only [zero_add, Real.arcsin_zero, sub_zero, smul_eq_mul, mul_one] at ho
  set δ' : ℝ := δ0 / (4 * M) with hδ'
  have hδ'p : 0 < δ' := by positivity
  obtain ⟨η, hη, hηs⟩ := Metric.eventually_nhds_iff.1 (ho.def hδ'p)
  -- the bound for `y → +∞`
  have hpos : ∀ᶠ y : ℝ in atTop, ∀ x ∈ Icc a b,
      |‖Complex.Gamma (x + I * y)‖ /
        (Real.sqrt (2 * π) * |y| ^ (x - 1 / 2) * Real.exp (-π * |y| / 2)) - 1| < ε := by
    have t1 : Tendsto (fun y : ℝ => (M + 1) * M ^ 2 / y ^ 2 + M ^ 3 / y ^ 2) atTop (𝓝 0) := by
      have h2 : Tendsto (fun y : ℝ => y ^ 2) atTop atTop :=
        tendsto_pow_atTop (by norm_num)
      simpa using (tendsto_const_nhds.div_atTop h2).add (tendsto_const_nhds.div_atTop h2)
    have t2 : Tendsto (fun y : ℝ => 1 / (6 * (y - M))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop (by norm_num)
        (tendsto_atTop_add_const_right _ _ tendsto_id))
    have t3 : Tendsto (fun y : ℝ => M / y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    filter_upwards [eventually_gt_atTop (M + 1), t1.eventually (gt_mem_nhds (by positivity :
      (0 : ℝ) < δ0 / 2)), t2.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ0 / 4)),
      t3.eventually (gt_mem_nhds hη)] with y hyM h1 h2 h3 x hx
    have hy : 0 < y := by linarith
    have hx' := hxM x hx
    set z : ℂ := (x : ℂ) + I * y with hz
    set r : ℝ := ‖z‖ with hr
    have hre : z.re = x := by simp [hz]
    have him : z.im = y := by simp [hz]
    have hr2 : r ^ 2 = x ^ 2 + y ^ 2 := by
      rw [hr, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]; ring
    have hry : y ≤ r := by
      have := abs_im_le_norm z; rw [him, abs_of_pos hy] at this; exact this
    have hrp : 0 < r := hy.trans_le hry
    have hrmy : r - y = x ^ 2 / (r + y) := by
      field_simp; nlinarith [hr2]
    have hx2 : x ^ 2 ≤ M ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
    have hrmy' : r - y ≤ M ^ 2 / y := by
      rw [hrmy]
      calc x ^ 2 / (r + y) ≤ M ^ 2 / (r + y) := by gcongr
        _ ≤ M ^ 2 / y := by gcongr; linarith
    rw [norm_Gamma_vertical_ratio_eq x hy]
    set T := (x - 1 / 2) * Real.log (r / y) + (π * y / 2 - x - y * arg z) +
      (DLMF.Gamma.binetMu z).re with hT
    -- the three pieces
    have hlog0 : 0 ≤ Real.log (r / y) := Real.log_nonneg ((one_le_div hy).2 hry)
    have hlog1 : Real.log (r / y) ≤ M ^ 2 / y ^ 2 := by
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
      rw [div_sub_one hy.ne', show M ^ 2 / y ^ 2 = (M ^ 2 / y) / y by ring]
      gcongr
    have hA : |(x - 1 / 2) * Real.log (r / y)| ≤ (M + 1) * M ^ 2 / y ^ 2 := by
      rw [abs_mul, abs_of_nonneg hlog0, mul_div_assoc]
      have : |x - 1 / 2| ≤ M + 1 := by
        refine (abs_sub _ _).trans ?_; norm_num; linarith
      exact mul_le_mul this hlog1 hlog0 (by positivity)
    set u : ℝ := x / r with hu
    have hu1 : |u| ≤ M / y := by
      rw [hu, abs_div, abs_of_pos hrp]
      calc |x| / r ≤ M / r := by gcongr
        _ ≤ M / y := by gcongr
    have heq : π * y / 2 - x - y * arg z = y * (Real.arcsin u - u) + x * (y / r - 1) := by
      rw [arg_of_im_pos (by rw [him]; exact hy), Real.arccos_eq_pi_div_two_sub_arcsin, hre]
      simp only [hu]
      field_simp
      ring
    have hB1 : |y * (Real.arcsin u - u)| ≤ δ0 / 4 := by
      have hs := hηs (show dist u 0 < η by rw [dist_zero_right]; exact lt_of_le_of_lt hu1 h3)
      simp only [Real.norm_eq_abs] at hs
      rw [abs_mul, abs_of_pos hy]
      calc y * |Real.arcsin u - u| ≤ y * (δ' * |u|) := by gcongr
        _ = δ' * (y * |u|) := by ring
        _ ≤ δ' * M := by
          gcongr
          rw [hu, abs_div, abs_of_pos hrp, mul_div_assoc']
          rw [div_le_iff₀ hrp]; nlinarith [abs_nonneg x]
        _ = δ0 / 4 := by rw [hδ']; field_simp
    have hB2 : |x * (y / r - 1)| ≤ M ^ 3 / y ^ 2 := by
      have hyr : |y / r - 1| = (r - y) / r := by
        rw [abs_sub_comm, show 1 - y / r = (r - y) / r by field_simp,
          abs_of_nonneg (div_nonneg (by linarith) hrp.le)]
      rw [abs_mul, hyr]
      calc |x| * ((r - y) / r) ≤ M * ((M ^ 2 / y) / y) := by
            gcongr
          _ = M ^ 3 / y ^ 2 := by ring
    have hC : |(DLMF.Gamma.binetMu z).re| ≤ 1 / (6 * (y - M)) := by
      have hzs : z ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr (by rw [him]; exact hy.ne'))
      refine (abs_re_le_norm _).trans ((DLMF.Gamma.norm_binetMu_le hzs).trans ?_)
      rw [hre]
      have : y - M ≤ r + x := by linarith [neg_abs_le x]
      gcongr
      linarith
    have hTb : |T| < δ0 := by
      rw [hT, heq]
      calc |(x - 1 / 2) * Real.log (r / y) + (y * (Real.arcsin u - u) + x * (y / r - 1)) +
            (DLMF.Gamma.binetMu z).re|
          ≤ |(x - 1 / 2) * Real.log (r / y)| + (|y * (Real.arcsin u - u)| +
            |x * (y / r - 1)|) + |(DLMF.Gamma.binetMu z).re| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_add_le _ _
        _ < δ0 := by linarith
    have hT1 : |T| ≤ 1 := hTb.le.trans (min_le_left _ _)
    calc |Real.exp T - 1| ≤ 2 * |T| := Real.abs_exp_sub_one_le hT1
      _ < 2 * δ0 := by linarith
      _ ≤ ε := by have := min_le_right 1 (ε / 2); linarith
  rw [cocompact_eq_atBot_atTop, eventually_sup]
  refine ⟨?_, hpos⟩
  have hneg := tendsto_neg_atBot_atTop.eventually hpos
  filter_upwards [hneg] with y hy x hx
  have h := hy x hx
  rw [show (x : ℂ) + I * ((-y : ℝ) : ℂ) = (starRingEnd ℂ) ((x : ℂ) + I * y) by
    apply Complex.ext <;> simp, Complex.Gamma_conj, Complex.norm_conj, abs_neg] at h
  exact h

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
private lemma sum_range_two_mul_eq_sum_odd (g : ℕ → ℂ) (hg : ∀ k : ℕ, g (2 * k + 2) = 0) (n : ℕ) :
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
  refine sum_range_two_mul_eq_sum_odd (fun s => (besselSqMellinA ν s * Real.log x +
    besselSqMellinB ν s) * ((x : ℂ) ^ s)⁻¹) (fun k => ?_) n
  have ha := besselSqMellinA_two_mul ν (k + 1)
  have hb := besselSqMellinB_two_mul hν k
  rw [show 2 * k + 2 = 2 * (k + 1) by ring, ha, hb]
  simp

end DLMF.AsymptoticApproximations
