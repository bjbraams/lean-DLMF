/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Second derivatives along curves

For a `C²` function `F` on a normed space and a curve `c` with velocity `c'` and acceleration
`c''`, the second derivative of `F ∘ c` is `D²F(c)(c', c') + DF(c) c''`. On `ℂ × ℂ × ℂ` this gives
the second derivative of `σ ↦ 𝒦(X σ, Y σ, Z σ)` in terms of the first and (symmetric) second
partial derivatives of `𝒦`, which are themselves expressed as Fréchet derivatives on the
coordinate vectors.

## Main results

* `ContDiffAt.deriv_comp_curve`: the first and second derivatives of `F ∘ c`.
* `Complex.deriv_comp_three`: the second-order chain rule for `σ ↦ 𝒦(X σ, Y σ, Z σ)`.
* `Complex.deriv_coord_three`: the coordinate partial derivatives of `𝒦` as Fréchet derivatives.
-/

@[expose] public section

open Filter
open scoped Topology

/-- Second derivative of `F ∘ c` along a curve. -/
theorem ContDiffAt.deriv_comp_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → ℂ} {c c' : ℂ → E} {τ : ℂ} {c'' : E} (hF : ContDiffAt ℂ 2 F (c τ))
    (hc : ∀ᶠ σ in 𝓝 τ, HasDerivAt c (c' σ) σ) (hc' : HasDerivAt c' c'' τ) :
    deriv (fun σ => F (c σ)) τ = fderiv ℂ F (c τ) (c' τ) ∧
      deriv (deriv fun σ => F (c σ)) τ =
        fderiv ℂ (fderiv ℂ F) (c τ) (c' τ) (c' τ) + fderiv ℂ F (c τ) c'' := by
  have hFd : ∀ᶠ x in 𝓝 (c τ), DifferentiableAt ℂ F x :=
    (hF.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have hcont : ContinuousAt c τ := hc.self_of_nhds.continuousAt
  have hFd' : ∀ᶠ σ in 𝓝 τ, DifferentiableAt ℂ F (c σ) := hcont.tendsto.eventually hFd
  have hev : ∀ᶠ σ in 𝓝 τ, deriv (fun σ => F (c σ)) σ = fderiv ℂ F (c σ) (c' σ) := by
    filter_upwards [hFd', hc] with σ h1 h2
    exact (h1.hasFDerivAt.comp_hasDerivAt σ h2).deriv
  refine ⟨hev.self_of_nhds, ?_⟩
  have hD : DifferentiableAt ℂ (fderiv ℂ F) (c τ) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : HasDerivAt (fun σ => fderiv ℂ F (c σ))
      (fderiv ℂ (fderiv ℂ F) (c τ) (c' τ)) τ :=
    hD.hasFDerivAt.comp_hasDerivAt τ hc.self_of_nhds
  exact ((h1.clm_apply hc').congr_of_eventuallyEq
    hev).deriv

namespace Complex

/-- Second derivative of `σ ↦ 𝒦(X σ, Y σ, Z σ)` in terms of the first and second Fréchet
derivatives of `(u, v, w) ↦ 𝒦 u v w` on the coordinate vectors. -/
theorem deriv_comp_three {𝒦 : ℂ → ℂ → ℂ → ℂ} {X Y Z X' Y' Z' : ℂ → ℂ} {X'' Y'' Z'' s : ℂ}
    (hF : ContDiffAt ℂ 2 (fun x : ℂ × ℂ × ℂ => 𝒦 x.1 x.2.1 x.2.2) (X s, Y s, Z s))
    (hX : ∀ᶠ σ in 𝓝 s, HasDerivAt X (X' σ) σ) (hY : ∀ᶠ σ in 𝓝 s, HasDerivAt Y (Y' σ) σ)
    (hZ : ∀ᶠ σ in 𝓝 s, HasDerivAt Z (Z' σ) σ) (hX' : HasDerivAt X' X'' s)
    (hY' : HasDerivAt Y' Y'' s) (hZ' : HasDerivAt Z' Z'' s) :
    let D := fderiv ℂ (fun x : ℂ × ℂ × ℂ => 𝒦 x.1 x.2.1 x.2.2) (X s, Y s, Z s)
    let D2 := fderiv ℂ (fderiv ℂ (fun x : ℂ × ℂ × ℂ => 𝒦 x.1 x.2.1 x.2.2)) (X s, Y s, Z s)
    deriv (fun σ => 𝒦 (X σ) (Y σ) (Z σ)) s =
        X' s * D (1, 0, 0) + Y' s * D (0, 1, 0) + Z' s * D (0, 0, 1) ∧
      deriv (deriv fun σ => 𝒦 (X σ) (Y σ) (Z σ)) s =
        X' s ^ 2 * D2 (1, 0, 0) (1, 0, 0) + Y' s ^ 2 * D2 (0, 1, 0) (0, 1, 0) +
          Z' s ^ 2 * D2 (0, 0, 1) (0, 0, 1) + 2 * X' s * Y' s * D2 (1, 0, 0) (0, 1, 0) +
          2 * X' s * Z' s * D2 (1, 0, 0) (0, 0, 1) + 2 * Y' s * Z' s * D2 (0, 1, 0) (0, 0, 1) +
          X'' * D (1, 0, 0) + Y'' * D (0, 1, 0) + Z'' * D (0, 0, 1) := by
  intro D D2
  have hc : ∀ᶠ σ in 𝓝 s, HasDerivAt (fun σ => (X σ, Y σ, Z σ)) (X' σ, Y' σ, Z' σ) σ := by
    filter_upwards [hX, hY, hZ] with σ h1 h2 h3
    exact h1.prodMk (h2.prodMk h3)
  have h := ContDiffAt.deriv_comp_curve (F := fun x : ℂ × ℂ × ℂ => 𝒦 x.1 x.2.1 x.2.2) hF hc
    (hX'.prodMk (hY'.prodMk hZ'))
  have hsym := hF.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hv : ∀ x y w : ℂ, ((x, y, w) : ℂ × ℂ × ℂ) =
      x • ((1 : ℂ), (0 : ℂ), (0 : ℂ)) + y • ((0 : ℂ), (1 : ℂ), (0 : ℂ)) +
        w • ((0 : ℂ), (0 : ℂ), (1 : ℂ)) := fun x y w => by
    ext <;> simp
  refine ⟨?_, ?_⟩
  · rw [h.1, hv (X' s)]
    simp only [D, map_add, map_smul, smul_eq_mul]
  · rw [h.2, hv (X' s), hv X'']
    simp only [map_add, map_smul, smul_eq_mul, D, D2, add_apply,
      smul_apply]
    rw [hsym (0, 1, 0) (1, 0, 0), hsym (0, 0, 1) (1, 0, 0), hsym (0, 0, 1) (0, 1, 0)]
    ring

/-- The coordinate partial derivatives of `𝒦` at `(u, v, w)` as Fréchet derivatives. -/
theorem deriv_coord_three {𝒦 : ℂ → ℂ → ℂ → ℂ} {u v w : ℂ}
    (hF : ContDiffAt ℂ 2 (fun x : ℂ × ℂ × ℂ => 𝒦 x.1 x.2.1 x.2.2) (u, v, w)) :
    let D := fderiv ℂ (fun x : ℂ × ℂ × ℂ => 𝒦 x.1 x.2.1 x.2.2) (u, v, w)
    let D2 := fderiv ℂ (fderiv ℂ (fun x : ℂ × ℂ × ℂ => 𝒦 x.1 x.2.1 x.2.2)) (u, v, w)
    deriv (fun u' => 𝒦 u' v w) u = D (1, 0, 0) ∧
      deriv (deriv fun u' => 𝒦 u' v w) u = D2 (1, 0, 0) (1, 0, 0) ∧
      deriv (fun v' => 𝒦 u v' w) v = D (0, 1, 0) ∧
      deriv (deriv fun v' => 𝒦 u v' w) v = D2 (0, 1, 0) (0, 1, 0) ∧
      deriv (𝒦 u v) w = D (0, 0, 1) ∧
      deriv (deriv (𝒦 u v)) w = D2 (0, 0, 1) (0, 0, 1) := by
  intro D D2
  have hid : ∀ x : ℂ, ∀ᶠ σ in 𝓝 x, HasDerivAt (fun σ : ℂ => σ) ((fun _ => (1 : ℂ)) σ) σ :=
    fun x => Eventually.of_forall fun σ => hasDerivAt_id σ
  have hcst : ∀ x c : ℂ, ∀ᶠ σ in 𝓝 x, HasDerivAt (fun _ : ℂ => c) ((fun _ => (0 : ℂ)) σ) σ :=
    fun x c => Eventually.of_forall fun σ => hasDerivAt_const σ c
  have h1 := Complex.deriv_comp_three (𝒦 := 𝒦) (s := u) hF (hid u) (hcst u v) (hcst u w)
    (hasDerivAt_const u 1) (hasDerivAt_const u 0) (hasDerivAt_const u 0)
  have h2 := Complex.deriv_comp_three (𝒦 := 𝒦) (s := v) hF (hcst v u) (hid v) (hcst v w)
    (hasDerivAt_const v 0) (hasDerivAt_const v 1) (hasDerivAt_const v 0)
  have h3 := Complex.deriv_comp_three (𝒦 := 𝒦) (s := w) hF (hcst w u) (hcst w v) (hid w)
    (hasDerivAt_const w 0) (hasDerivAt_const w 0) (hasDerivAt_const w 1)
  simp only [one_mul, zero_mul, add_zero, zero_add, mul_zero, one_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one] at h1 h2 h3
  exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2⟩

end Complex
