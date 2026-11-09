/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Mellin.Transforms

/-!
# Residue remainders in the Handelsman–Lew method

After shifting a Mellin inversion contour to the right, the remaining inverse Mellin
integral is little-o of the new line's power. Applied to the four truncated convolutions,
this gives the residue expansion and remainder in DLMF 2.5.33–2.5.36.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-- DLMF 2.5.35–2.5.36: shifting a Parseval line from `p` to `q > p` leaves
a remainder `o(x⁻q)` after subtracting the residues, with the orientation of a right shift. -/
@[dlmf 2.5.E35, dlmf 2.5.E36]
theorem mellinInv_add_residues_isLittleO {G : ℂ → ℂ} {p q : ℝ} (hpq : p < q)
    (P : Finset ℂ) (hP : ∀ z ∈ P, p < z.re ∧ z.re < q)
    (hG : DifferentiableOn ℂ G ({z : ℂ | p ≤ z.re ∧ z.re ≤ q} \ (P : Set ℂ)))
    (hdecay : Tendsto (fun y : ℝ => ⨆ σ : Icc p q, ‖G (σ + y * I)‖)
      (cocompact ℝ) (𝓝 0))
    (hp : VerticalIntegrable G p) (hq : VerticalIntegrable G q) :
    (fun x : ℝ => mellinInv p G x + ∑ z ∈ P,
      DLMF.AlgebraicAnalytic.residueAt (fun w => (x : ℂ) ^ (-w) * G w) z)
      =o[atTop] fun x : ℝ => ((x ^ (-q) : ℝ) : ℂ) := by
  refine (mellinInv_isLittleO G q).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [mellinInv_shift hpq hx P hP hG hdecay hq hp]
  ring

/-- The Handelsman–Lew remainder for any convolution with the stated Parseval representation. -/
@[dlmf 2.5.E33, dlmf 2.5.E35, dlmf 2.5.E36]
theorem convolution_add_residues_isLittleO {J : ℝ → ℂ} {G : ℂ → ℂ} {p q : ℝ}
    (hJ : ∀ x : ℝ, 0 < x → J x = mellinInv p G x) (hpq : p < q)
    (P : Finset ℂ) (hP : ∀ z ∈ P, p < z.re ∧ z.re < q)
    (hG : DifferentiableOn ℂ G ({z : ℂ | p ≤ z.re ∧ z.re ≤ q} \ (P : Set ℂ)))
    (hdecay : Tendsto (fun y : ℝ => ⨆ σ : Icc p q, ‖G (σ + y * I)‖)
      (cocompact ℝ) (𝓝 0))
    (hp : VerticalIntegrable G p) (hq : VerticalIntegrable G q) :
    (fun x : ℝ => J x + ∑ z ∈ P,
      DLMF.AlgebraicAnalytic.residueAt (fun w => (x : ℂ) ^ (-w) * G w) z)
      =o[atTop] fun x : ℝ => ((x ^ (-q) : ℝ) : ℂ) := by
  refine (mellinInv_add_residues_isLittleO hpq P hP hG hdecay hp hq).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [hJ x hx]

end DLMF.AsymptoticApproximations
