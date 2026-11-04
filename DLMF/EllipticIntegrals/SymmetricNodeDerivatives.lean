/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import Carlson.R.SlitDeriv

/-!
# Node derivatives of symmetric elliptic integrals

DLMF 19.18.1 and 19.18.3–19.18.4, from the node derivative of Carlson's continued
`R`-function on the product slit plane. These are the common calculus facts used by the
addition theorems and the differential equations.

## Main results

* `hasDerivAt_symmetricEllipticR_update`: `∂ⱼ R_{-a}(𝐛; 𝐳) = -a wⱼ R_{-a-1}(𝐛 + 𝐞ⱼ; 𝐳)`,
  `wⱼ = bⱼ/∑ bₖ` (DLMF 19.18.3, 19.18.4).
* `hasDerivAt_symmetricEllipticRF_right`: `∂R_F(x, y, z)/∂z = -(1/6) R_D(x, y, z)` (DLMF 19.18.1).
* `symmetricEllipticR_eventuallyEq_carlsonR`: near a slit-plane node, `symmetricEllipticR a b`
  agrees with `Carlson.carlsonR (-a) b`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Real Topology

namespace DLMF.EllipticIntegrals

variable {ι : Type*} [Fintype ι]

/-- Identity under the stated parameter and domain assumptions: `symmetricEllipticR a b =ᶠ[𝓝 z]
Carlson.carlsonR (-a) b`. -/
lemma symmetricEllipticR_eventuallyEq_carlsonR (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) :
    symmetricEllipticR a b =ᶠ[𝓝 z] Carlson.carlsonR (-a) b := by
  filter_upwards [Carlson.isOpen_carlsonRSlitDomain.mem_nhds hz] with w hw
  exact symmetricEllipticR_of_mem _ _ hw

open scoped Classical in
/-- At `(z j)`, the function `(fun w => symmetricEllipticR a b (Function.update z j w))` has
derivative `(Gamma (∑ i, b i) * (-a * b j * Carlson.regCarlsonR (-a - 1) (Dirichlet.addDirichletUnit
b j) z))`. -/
lemma hasDerivAt_symmetricEllipticR_update_regCarlsonR (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (j : ι) :
    HasDerivAt (fun w => symmetricEllipticR a b (Function.update z j w))
      (Gamma (∑ i, b i) * (-a * b j *
        Carlson.regCarlsonR (-a - 1) (Dirichlet.addDirichletUnit b j) z)) (z j) := by
  have hc : Tendsto (Function.update z j) (𝓝 (z j)) (𝓝 z) := by
    have := ((continuous_const (y := z)).update j continuous_id).tendsto (z j)
    simpa using this
  have hev := hc.eventually (symmetricEllipticR_eventuallyEq_carlsonR a b hz)
  have h := (Carlson.hasDerivAt_regCarlsonR_update (-a) b hz j).const_mul (Gamma (∑ i, b i))
  exact h.congr_of_eventuallyEq hev

open scoped Classical in
/-- DLMF 19.18.4: `∂ⱼ R_{-a}(𝐛; 𝐳) = -a wⱼ R_{-a-1}(𝐛 + 𝐞ⱼ; 𝐳)`, `wⱼ = bⱼ/∑ bₖ` (19.18.3),
for slit-plane nodes and `∑ bₖ ≠ 0`. -/
@[dlmf 19.18.E4, dlmf 19.18.E3]
theorem hasDerivAt_symmetricEllipticR_update (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (j : ι) (hb : ∑ i, b i ≠ 0) :
    HasDerivAt (fun w => symmetricEllipticR a b (Function.update z j w))
      (-a * (b j / ∑ i, b i) *
          symmetricEllipticR (a + 1) (Dirichlet.addDirichletUnit b j) z) (z j) := by
  refine (hasDerivAt_symmetricEllipticR_update_regCarlsonR a b hz j).congr_deriv ?_
  rw [symmetricEllipticR_of_mem _ _ hz]
  unfold Carlson.carlsonR
  rw [Dirichlet.sum_addDirichletUnit, Complex.Gamma_add_one _ hb, show -(a + 1) = -a - 1 by ring]
  field_simp

/-- DLMF 19.18.1: `∂R_F(x, y, z)/∂z = -(1/6) R_D(x, y, z)` (slit-plane variables). -/
@[dlmf 19.18.E1]
theorem hasDerivAt_symmetricEllipticRF_right {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => symmetricEllipticRF x y w) (-(1 / 6) * symmetricEllipticRD x y z) z := by
  have h := hasDerivAt_symmetricEllipticR_update (1 / 2) (fun _ : Fin 3 => 1 / 2)
      (vec3_mem_carlsonRSlitDomain hx hy hz) 2
    (by simp)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    rw [symmetricEllipticRF_eq_symmetricEllipticR hx hy hw]
    congr 1; funext i; fin_cases i <;> simp [Function.update]
  · have hb : Dirichlet.addDirichletUnit (fun _ : Fin 3 => (1 / 2 : ℂ)) 2 =
        ![1 / 2, 1 / 2, 3 / 2] := by
      unfold Dirichlet.addDirichletUnit
      funext i; fin_cases i <;> simp [Function.update]; norm_num
    rw [hb, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num,
                                              ← symmetricEllipticRD_eq_symmetricEllipticR hx hy hz]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

end DLMF.EllipticIntegrals
