/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Mellin.Transforms
public import DLMF.AlgebraicAnalytic.Transforms.Defs
public import DLMF.ExpIntegrals.Expansions

/-!
# Laplace transforms with small parameters (DLMF §2.5(iii))

For `h` satisfying 2.5.18 and 2.5.20 with `c > -1`, the Laplace transform
`𝓛h(ζ) = ∫₀^∞ h(t) e^{-ζt} dt` (2.5.37; `DLMF.AlgebraicAnalytic.laplaceTransform`) is expanded
as `ζ → 0⁺` by writing `ζ𝓛h(ζ) = I₁(1/ζ) + I₂(1/ζ)` (2.5.38–2.5.39) and applying the Mellin
method with `𝓜(e^{-t})(z) = Γ(z)`.

* 2.5.38–2.5.40 (proved, 2.5.40 modulo the convolution theorem 2.5.4);
* 2.5.41–2.5.44: contour shifts and the expansion 2.5.44;
* the remainder estimate after 2.5.43, `O(ζ^{l-δ-1})` (proved);
* the example `h(t) = 1/(1 + t)`: 2.5.45–2.5.49, with 2.5.49 for real `ζ > 0` and the convergent
  form of 2.5.48 proved from DLMF 6.2.2 and 6.6.3.

Parameters: `ζ` is real and positive except in `laplace_inv_one_add_eq_complex` (`ℜζ > 0`).
The extended transform `𝓜h(z)` for `ℜz > 1` in 2.5.43–2.5.44 is `𝓜h₁(z) + H(z)`, `H` the
continuation of `𝓜h₂` (2.5.27–2.5.28).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology Real Nat

namespace DLMF.AsymptoticApproximations

open DLMF.AlgebraicAnalytic (laplaceTransform)

/-- DLMF 2.5.37–2.5.39: for `ζ > 0` and `x = 1/ζ`, `ζ𝓛h(ζ) = I₁(x) + I₂(x)` with
`I_j(x) = ∫₀^∞ e^{-t} h_j(xt) dt`, provided both integrals converge. -/
@[dlmf 2.5.E37, dlmf 2.5.E38, dlmf 2.5.E39]
theorem laplace_eq_trunc_add {h : ℝ → ℂ} {ζ : ℝ} (hζ : 0 < ζ)
    (h1 : IntegrableOn (fun t => (Real.exp (-t) : ℂ) * mellinTruncLow h (ζ⁻¹ * t)) (Ioi 0))
    (h2 : IntegrableOn (fun t => (Real.exp (-t) : ℂ) * mellinTruncHigh h (ζ⁻¹ * t)) (Ioi 0)) :
    (ζ : ℂ) * laplaceTransform h ζ =
      (∫ t in Ioi 0, (Real.exp (-t) : ℂ) * mellinTruncLow h (ζ⁻¹ * t)) +
        ∫ t in Ioi 0, (Real.exp (-t) : ℂ) * mellinTruncHigh h (ζ⁻¹ * t) := by
  rw [← integral_add h1 h2]
  have hsplit : (fun t => (Real.exp (-t) : ℂ) * mellinTruncLow h (ζ⁻¹ * t) +
      (Real.exp (-t) : ℂ) * mellinTruncHigh h (ζ⁻¹ * t)) =
      fun t => (fun u : ℝ => Complex.exp (-(ζ : ℂ) * u) * h u) (ζ⁻¹ * t) := by
    funext t
    simp only [mellinTruncHigh, Pi.sub_apply, ofReal_exp]
    have hζ0 : (ζ : ℂ) ≠ 0 := by exact_mod_cast hζ.ne'
    rw [show -(ζ : ℂ) * ((ζ⁻¹ * t : ℝ) : ℂ) = ((-t : ℝ) : ℂ) by
      push_cast; field_simp]
    ring
  rw [hsplit, integral_comp_mul_left_Ioi (fun u : ℝ => Complex.exp (-(ζ : ℂ) * u) * h u) 0
    (inv_pos.2 hζ), mul_zero, inv_inv,
    laplaceTransform, Complex.real_smul]

/-- `𝓜(e^{-t})(s) = Γ(s)` for `ℜs > 0` (DLMF 5.2.1), used in 2.5.40. -/
theorem mellin_exp_neg {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => (Real.exp (-t) : ℂ)) s = Complex.Gamma s := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral_eq_mellin]

/-- DLMF 2.5.40: if `𝓜h(z)` converges absolutely on the line `ℜz = p < 1`,
`Γ(1 - z)𝓜h(z)` is integrable along it, and `I(x) = ∫₀^∞ e^{-t} h(xt) dt` is continuous at
`x > 0`, then `I(x) = (2πi)⁻¹ ∫_{p-i∞}^{p+i∞} x^{-z} Γ(1 - z) 𝓜h(z) dz` (applied to `h = h_j`). -/
@[dlmf 2.5.E40]
theorem laplace_trunc_eq_mellinInv {h : ℝ → ℂ} {p x : ℝ} (hp : p < 1) (hx : 0 < x)
    (hconv : ∀ z : ℂ, z.re = p → MellinConvergent h z)
    (hint : VerticalIntegrable (fun z => Complex.Gamma (1 - z) * mellin h z) p)
    (hcont : ContinuousAt (fun x => ∫ t in Ioi 0, (Real.exp (-t) : ℂ) * h (x * t)) x) :
    (∫ t in Ioi 0, (Real.exp (-t) : ℂ) * h (x * t)) =
      mellinInv p (fun z => Complex.Gamma (1 - z) * mellin h z) x := by
  have hre : ∀ y : ℝ, 0 < (1 - ((p : ℂ) + y * I)).re := fun y => by simp; linarith
  have hline : ∀ y : ℝ, mellin (fun t : ℝ => (Real.exp (-t) : ℂ)) (1 - ((p : ℂ) + y * I)) =
      Complex.Gamma (1 - ((p : ℂ) + y * I)) := fun y => mellin_exp_neg (hre y)
  have hconv' : ∀ z : ℂ, z.re = p →
      MellinConvergent (fun t : ℝ => (Real.exp (-t) : ℂ)) (1 - z) ∧ MellinConvergent h z := by
    intro z hz
    refine ⟨?_, hconv z hz⟩
    have hs : 0 < (1 - z).re := by simp; linarith
    refine (Complex.GammaIntegral_convergent hs).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [smul_eq_mul, mul_comm, ofReal_exp]
  have hint' : VerticalIntegrable
      (fun z => mellin (fun t : ℝ => (Real.exp (-t) : ℂ)) (1 - z) * mellin h z) p := by
    unfold VerticalIntegrable at hint ⊢
    simp only [hline]
    exact hint
  rw [mellin_convolution_eq_mellinInv hx hconv' hint' hcont]
  unfold mellinInv
  simp only [hline]

/-- DLMF 2.5.41: let `h` be locally integrable on `(0, ∞)` with `h(t) = O(t^c)` as `t → 0⁺`,
`c > -1` (2.5.20). Then for `1 < ρ < 2` and `x > 0`,
`I₁(x) = 𝓜h₁(1) x^{-1} + (2πi)⁻¹ ∫_{ρ-i∞}^{ρ+i∞} x^{-z} Γ(1 - z) 𝓜h₁(z) dz`. -/
@[dlmf 2.5.E41, dlmf 2.5.iii]
theorem laplace_truncLow_shift {h : ℝ → ℂ} {c ρ x : ℝ} (hc : -1 < c) (hρ1 : 1 < ρ)
    (hρ2 : ρ < 2) (hx : 0 < x) (hhc : LocallyIntegrableOn h (Ioi 0))
    (h0 : h =O[𝓝[>] 0] fun t => t ^ c) :
    (∫ t in Ioi 0, (Real.exp (-t) : ℂ) * mellinTruncLow h (x * t)) =
      mellin (mellinTruncLow h) 1 * (x : ℂ)⁻¹ +
        mellinInv ρ (fun z => Complex.Gamma (1 - z) * mellin (mellinTruncLow h) z) x := by
  sorry

/-- DLMF 2.5.42: let `h` satisfy 2.5.18 and 2.5.20, `p₂ < min(1, ℜβ₀)` as in 2.5.40, and let `H`
be the continuation of `𝓜h₂` (2.5.27, or entire if `κ ≠ 0`), so that `Γ(1 - z)H(z)` is
analytic in `p₂ ≤ ℜz ≤ ρ` (`1 < ρ < 2`) except at the finite set `P` of poles with
`ℜβ₀ ≤ ℜz ≤ 1`, and decays as `ℑz → ±∞` uniformly in the strip. Then
`I₂(x) = ∑_{q ∈ P} Res_{z=q}[-x^{-z} Γ(1 - z) H(z)] + (2πi)⁻¹ ∫_{(ρ)} x^{-z} Γ(1 - z) H(z) dz`. -/
@[dlmf 2.5.E42, dlmf 2.5.iii]
theorem laplace_truncHigh_shift {h : ℝ → ℂ} {H : ℂ → ℂ} {p ρ x : ℝ} (P : Finset ℂ)
    (hρ1 : 1 < ρ) (hρ2 : ρ < 2) (hp : p < 1) (hx : 0 < x)
    (hconv : ∀ z : ℂ, z.re = p → MellinConvergent (mellinTruncHigh h) z)
    (hH : ∀ z : ℂ, z.re ≤ p → H z = mellin (mellinTruncHigh h) z)
    (hP : ∀ q ∈ P, p < q.re ∧ q.re ≤ 1)
    (hHd : DifferentiableOn ℂ (fun z => Complex.Gamma (1 - z) * H z)
      ({z : ℂ | p ≤ z.re ∧ z.re ≤ ρ} \ (P : Set ℂ)))
    (hdecay : Tendsto (fun y : ℝ => ⨆ σ : Icc p ρ, ‖Complex.Gamma (1 - (σ + y * I)) *
      H (σ + y * I)‖) (cocompact ℝ) (𝓝 0))
    (hp_int : VerticalIntegrable (fun z => Complex.Gamma (1 - z) * H z) p)
    (hρ_int : VerticalIntegrable (fun z => Complex.Gamma (1 - z) * H z) ρ)
    (hcont : ContinuousAt (fun x => ∫ t in Ioi 0,
      (Real.exp (-t) : ℂ) * mellinTruncHigh h (x * t)) x) :
    (∫ t in Ioi 0, (Real.exp (-t) : ℂ) * mellinTruncHigh h (x * t)) =
      ∑ q ∈ P, DLMF.AlgebraicAnalytic.residueAt
        (fun z => -((x : ℂ) ^ (-z) * Complex.Gamma (1 - z) * H z)) q +
        mellinInv ρ (fun z => Complex.Gamma (1 - z) * H z) x := by
  sorry

/-- Bound for the inverse Mellin integral: `|(2πi)⁻¹ ∫_{(σ)} x^{-z} G(z) dz| ≤ x^{-σ} C` with
`C = (2π)⁻¹ ∫ |G(σ + iy)| dy`, for `x > 0`. -/
theorem norm_mellinInv_le (σ : ℝ) (G : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    ‖mellinInv σ G x‖ ≤ x ^ (-σ) * ((1 / (2 * π)) * ∫ y : ℝ, ‖G (σ + y * I)‖) := by
  unfold mellinInv
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖∫ y : ℝ, (x : ℂ) ^ (-((σ : ℂ) + y * I)) • G (σ + y * I)‖ ≤
      x ^ (-σ) * ∫ y : ℝ, ‖G (σ + y * I)‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  calc 1 / (2 * π) * ‖∫ y : ℝ, (x : ℂ) ^ (-((σ : ℂ) + y * I)) • G (σ + y * I)‖
      ≤ 1 / (2 * π) * (x ^ (-σ) * ∫ y : ℝ, ‖G (σ + y * I)‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/-- DLMF §2.5(iii), after 2.5.43: the last term of 2.5.43,
`(2πi)⁻¹ ∫_{l-δ-i∞}^{l-δ+i∞} ζ^{z-1} G(z) dz = ζ⁻¹ · (2πi)⁻¹ ∫ (1/ζ)^{-z} G(z) dz`, is
`O(ζ^{l-δ-1})` as `ζ → 0⁺` (here `σ = l - δ`). Stronger than DLMF: no hypothesis on `G`. -/
@[dlmf 2.5.E43, dlmf 2.5.iii]
theorem laplace_remainder_isBigO (σ : ℝ) (G : ℂ → ℂ) :
    (fun ζ : ℝ => (ζ : ℂ)⁻¹ * mellinInv σ G ζ⁻¹) =O[𝓝[>] 0] fun ζ => ζ ^ (σ - 1) := by
  set C : ℝ := (1 / (2 * π)) * ∫ y : ℝ, ‖G (σ + y * I)‖
  refine IsBigO.of_bound C ?_
  filter_upwards [self_mem_nhdsWithin] with ζ (hζ : 0 < ζ)
  have hb := norm_mellinInv_le σ G (inv_pos.2 hζ)
  rw [Real.inv_rpow hζ.le, Real.rpow_neg hζ.le, inv_inv] at hb
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hζ.le,
    Real.norm_of_nonneg (Real.rpow_nonneg hζ.le _), Real.rpow_sub_one hζ.ne']
  calc ζ⁻¹ * ‖mellinInv σ G ζ⁻¹‖ ≤ ζ⁻¹ * (ζ ^ σ * C) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hζ.le)
    _ = C * (ζ ^ σ / ζ) := by ring

/-- DLMF 2.5.43: under the hypotheses of 2.5.41–2.5.42, with `H` the continuation of `𝓜h₂`,
`P₂` the poles of `Γ(1 - z)H(z)` in `ℜβ₀ ≤ ℜz ≤ 1`, `P` the poles of `Γ(1 - z)𝓜h(z)`
(`𝓜h = 𝓜h₁ + H`) in `1 < ℜz < l` (`l ≥ 2` an integer, `0 < δ` small, no poles on
`ℜz = l - δ`), and decay of these products along vertical lines uniformly in strips,
`𝓛h(ζ) = 𝓜h₁(1) + ∑_{P₂} Res[-ζ^{z-1}Γ(1 - z)H(z)] + ∑_{P} Res[-ζ^{z-1}Γ(1 - z)𝓜h(z)]
+ (2πi)⁻¹ ∫_{(l-δ)} ζ^{z-1}Γ(1 - z)𝓜h(z) dz` for `ζ > 0`. -/
@[dlmf 2.5.E43]
theorem laplace_expansion_residues {h : ℝ → ℂ} {H : ℂ → ℂ} {c p : ℝ} {l : ℕ} {δ ζ : ℝ}
    (P₂ P : Finset ℂ) (hc : -1 < c) (hl : 2 ≤ l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hζ : 0 < ζ)
    (hp : p < 1) (hhc : LocallyIntegrableOn h (Ioi 0)) (h0 : h =O[𝓝[>] 0] fun t => t ^ c)
    (hconv : ∀ z : ℂ, z.re = p → MellinConvergent (mellinTruncHigh h) z)
    (hH : ∀ z : ℂ, z.re ≤ p → H z = mellin (mellinTruncHigh h) z)
    (hP₂ : ∀ q ∈ P₂, p < q.re ∧ q.re ≤ 1) (hP : ∀ q ∈ P, 1 < q.re ∧ q.re < l - δ)
    (hHd : DifferentiableOn ℂ (fun z => Complex.Gamma (1 - z) *
        (mellin (mellinTruncLow h) z + H z))
      ({z : ℂ | p ≤ z.re ∧ z.re ≤ l - δ} \ ((P₂ : Set ℂ) ∪ P ∪ {1})))
    (hdecay : Tendsto (fun y : ℝ => ⨆ σ : Icc p (l - δ), ‖Complex.Gamma (1 - (σ + y * I)) *
      (mellin (mellinTruncLow h) (σ + y * I) + H (σ + y * I))‖) (cocompact ℝ) (𝓝 0)) :
    laplaceTransform h ζ = mellin (mellinTruncLow h) 1 +
      ∑ q ∈ P₂, DLMF.AlgebraicAnalytic.residueAt
        (fun z => -((ζ : ℂ) ^ (z - 1) * Complex.Gamma (1 - z) * H z)) q +
      ∑ q ∈ P, DLMF.AlgebraicAnalytic.residueAt
        (fun z => -((ζ : ℂ) ^ (z - 1) * Complex.Gamma (1 - z) *
          (mellin (mellinTruncLow h) z + H z))) q +
      (ζ : ℂ)⁻¹ * mellinInv (l - δ) (fun z => Complex.Gamma (1 - z) *
        (mellin (mellinTruncLow h) z + H z)) ζ⁻¹ := by
  sorry

/-- DLMF 2.5.44: let `h` be locally integrable on `(0, ∞)` with `h(t) = O(t^c)` as `t → 0⁺`,
`c > -1`, and `h(t) ∼ ∑ bₙ t^{-βₙ}` as `t → ∞` (2.5.18 with `κ = 0`), `ℜβₙ` strictly
increasing to `∞` and no `βₙ` a positive integer. Let `H` be the continuation of `𝓜h₂`
(2.5.27) and `𝓜h(z) = 𝓜h₁(z) + H(z)` (2.5.28). Then as `ζ → 0⁺`
`𝓛h(ζ) ∼ ∑ bₙ Γ(1 - βₙ) ζ^{βₙ-1} + ∑ (-ζ)ⁿ/n! 𝓜h(n + 1)`, the two series interpreted
separately: the remainder after `N` and `M` terms is `O(ζ^{ℜβ_N - 1}) + O(ζ^M)`. -/
@[dlmf 2.5.E44, dlmf 2.5.iii]
theorem laplace_small_parameter {h : ℝ → ℂ} {b β : ℕ → ℂ} {c : ℝ} {H : ℂ → ℂ} (hc : -1 < c)
    (hhc : LocallyIntegrableOn h (Ioi 0)) (h0 : h =O[𝓝[>] 0] fun t => t ^ c)
    (hβ : StrictMono fun s => (β s).re) (hβinf : Tendsto (fun s => (β s).re) atTop atTop)
    (hβint : ∀ s (n : ℕ), β s ≠ n + 1)
    (hh : HasAsymptoticExpansion atTop (fun s (t : ℝ) => (t : ℂ) ^ (-β s)) b h)
    (hH : ∀ z : ℂ, z.re < (β 0).re → H z = mellin (mellinTruncHigh h) z)
    (hHd : ∀ N : ℕ, DifferentiableOn ℂ (fun z => H z + ∑ s ∈ range N, b s / (z - β s))
      {z : ℂ | z.re < (β N).re}) (N M : ℕ) :
    (fun ζ : ℝ => laplaceTransform h ζ -
        ∑ n ∈ range N, b n * Complex.Gamma (1 - β n) * (ζ : ℂ) ^ (β n - 1) -
        ∑ n ∈ range M, (-(ζ : ℂ)) ^ n / n ! *
          (mellin (mellinTruncLow h) (n + 1) + H (n + 1)))
      =O[𝓝[>] 0] fun ζ => ζ ^ ((β N).re - 1) + ζ ^ M := by
  sorry

/-- DLMF 2.5.46: for `ζ > 0` and `k ≥ 1`,
`Res_{z=k}[-ζ^{z-1} Γ(1 - z) π csc(πz)] = (-ln ζ + ψ(k)) ζ^{k-1}/(k-1)!`; here
`h(t) = 1/(1 + t)` (2.5.45), `𝓜h(z) = π csc(πz)`, `κ = 0`, `βₛ = s + 1`, `c = 0`. -/
@[dlmf 2.5.E45, dlmf 2.5.E46]
theorem residueAt_laplace_inv_one_add {ζ : ℝ} (hζ : 0 < ζ) {k : ℕ} (hk : 1 ≤ k) :
    DLMF.AlgebraicAnalytic.residueAt (fun z => -((ζ : ℂ) ^ (z - 1) * Complex.Gamma (1 - z) *
        (π / Complex.sin (π * z)))) k =
      (-Real.log ζ + digamma k) * (ζ : ℂ) ^ (k - 1) / (k - 1)! := by
  sorry

/-- DLMF 2.5.47: for `ζ > 0`, with `h(t) = 1/(1 + t)` and the continuation
`𝓜h₂(z) = π csc(πz) - 𝓜h₁(z)` (2.5.28),
`Res_{z=1}[-ζ^{z-1} Γ(1 - z) 𝓜h₂(z)] = (-ln ζ - γ) - 𝓜h₁(1)`. -/
@[dlmf 2.5.E47]
theorem residueAt_laplace_inv_one_add_truncHigh {ζ : ℝ} (hζ : 0 < ζ) :
    DLMF.AlgebraicAnalytic.residueAt (fun z => -((ζ : ℂ) ^ (z - 1) * Complex.Gamma (1 - z) *
        (π / Complex.sin (π * z) -
          mellin (mellinTruncLow fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) z))) 1 =
      (-Real.log ζ - Real.eulerMascheroniConstant) -
        mellin (mellinTruncLow fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) 1 := by
  sorry

/-- DLMF 2.5.45 and 2.5.49 for real `ζ > 0`: `𝓛h(ζ) = ∫₀^∞ e^{-ζt}/(1 + t) dt = e^ζ E₁(ζ)`,
from the Stieltjes form 6.2.2 of `E₁` (`DLMF.Confluent.expIntE1_stieltjes`). -/
@[dlmf 2.5.E45, dlmf 2.5.E49]
theorem laplace_inv_one_add_eq {ζ : ℝ} (hζ : 0 < ζ) :
    laplaceTransform (fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) ζ =
      Complex.exp ζ * DLMF.Confluent.genExpIntE 1 ζ := by
  have hS : (ζ : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hζ
  rw [DLMF.Confluent.expIntE1_stieltjes hS, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, one_mul]
  have h := integral_comp_mul_left_Ioi
    (fun t : ℝ => Complex.exp (-(t : ℂ)) / ((t : ℂ) + ζ)) 0 hζ
  rw [mul_zero] at h
  have h' : (∫ t in Ioi (0 : ℝ), Complex.exp (-(t : ℂ)) / ((t : ℂ) + ζ)) =
      ζ • ∫ x in Ioi (0 : ℝ), Complex.exp (-((ζ * x : ℝ) : ℂ)) / (((ζ * x : ℝ) : ℂ) + ζ) := by
    rw [h, smul_inv_smul₀ hζ.ne']
  rw [h', ← integral_smul, laplaceTransform]
  refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
  have hx1 : ((1 + x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 + x : ℝ) ≠ 0)
  have hζ0 : (ζ : ℂ) ≠ 0 := by exact_mod_cast hζ.ne'
  have hd : ((ζ * x : ℝ) : ℂ) + ζ = ζ * ((1 + x : ℝ) : ℂ) := by push_cast; ring
  simp only [Complex.real_smul, hd]
  rw [show -((ζ * x : ℝ) : ℂ) = -(ζ : ℂ) * x by push_cast; ring]
  field_simp

/-- DLMF 2.5.49: `𝓛h(ζ) = e^ζ E₁(ζ)` for `ℜζ > 0`, `h(t) = 1/(1 + t)`. -/
@[dlmf 2.5.E49]
theorem laplace_inv_one_add_eq_complex {ζ : ℂ} (hζ : 0 < ζ.re) :
    laplaceTransform (fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) ζ =
      Complex.exp ζ * DLMF.Confluent.genExpIntE 1 ζ := by
  sorry

/-- DLMF 2.5.48 (convergent form, stronger than DLMF): for `ζ > 0`,
`𝓛h(ζ) = (-ln ζ) ∑ ζᵏ/k! + ∑ ψ(k + 1) ζᵏ/k!` with both series convergent, for
`h(t) = 1/(1 + t)`; from 2.5.49 and DLMF 6.6.3. -/
@[dlmf 2.5.E48]
theorem hasSum_laplace_inv_one_add {ζ : ℝ} (hζ : 0 < ζ) :
    HasSum (fun k : ℕ => (-(Real.log ζ : ℂ) + digamma (k + 1)) * (ζ : ℂ) ^ k / k !)
      (laplaceTransform (fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) ζ) := by
  have hζ0 : (ζ : ℂ) ≠ 0 := by exact_mod_cast hζ.ne'
  have h1 := DLMF.Confluent.expIntE1_digamma_series hζ0
  have h2 : HasSum (fun k : ℕ => (ζ : ℂ) ^ k / k !) (Complex.exp ζ) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp (ζ : ℂ)
  have h3 := (h2.mul_left (-(Real.log ζ : ℂ))).add h1
  rw [laplace_inv_one_add_eq hζ]
  convert h3 using 1
  · funext k
    ring
  · rw [← ofReal_log hζ.le]
    ring

/-- DLMF 2.5.48 (asymptotic form): for `h(t) = 1/(1 + t)`, as `ζ → 0⁺`,
`𝓛h(ζ) - ∑_{k<N} (-ln ζ + ψ(k + 1)) ζᵏ/k! = O(ζᴺ ln(1/ζ))` for every `N`. -/
@[dlmf 2.5.E48]
theorem laplace_inv_one_add_isBigO (N : ℕ) :
    (fun ζ : ℝ => laplaceTransform (fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) ζ -
        ∑ k ∈ range N, (-(Real.log ζ : ℂ) + digamma (k + 1)) * (ζ : ℂ) ^ k / k !)
      =O[𝓝[>] 0] fun ζ => ζ ^ N * (1 + |Real.log ζ|) := by
  sorry

end DLMF.AsymptoticApproximations
