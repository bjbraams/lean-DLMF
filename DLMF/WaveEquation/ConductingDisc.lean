/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The potential of a conducting unit disc

Temme, *Special Functions* (1996), Exercise 10.3, pp. 273–274,
synopsis TEM-10-08. The Cartesian potential is continuous at the rim;
its normal flux is asserted only on the open disc.
-/

@[expose] public noncomputable section
open Filter Set Laplacian
open scoped Topology
namespace DLMF.WaveEquation.Real

/-- The oblate radial coordinate associated with the unit conducting disc,
Temme Exercise 10.3, synopsis TEM-10-08. -/
def conductingDiscCoordinate (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  let s := 1 + (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2
  Real.sqrt ((s + Real.sqrt (s ^ 2 - 4 * ((p 0) ^ 2 + (p 1) ^ 2))) / 2 - 1)

/-- The unit-voltage potential outside the unit disc in `z=0`, continued continuously
onto the disc. Temme Exercise 10.3, synopsis TEM-10-08. -/
def conductingDiscPotential (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  1 - 2 / _root_.Real.pi * _root_.Real.arctan (conductingDiscCoordinate p)

/-- The defining oblate coordinate, Temme Exercise 10.3. -/
theorem conductingDiscCoordinate_def (p : EuclideanSpace ℝ (Fin 3)) :
    conductingDiscCoordinate p =
      let s := 1 + (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2
      Real.sqrt ((s + Real.sqrt (s ^ 2 - 4 * ((p 0) ^ 2 + (p 1) ^ 2))) / 2 - 1) := rfl

/-- The potential in oblate radius, Temme Exercise 10.3. -/
theorem conductingDiscPotential_def (p : EuclideanSpace ℝ (Fin 3)) :
    conductingDiscPotential p =
      1 - 2 / _root_.Real.pi * _root_.Real.arctan (conductingDiscCoordinate p) := rfl

/-- The conducting-disc potential is globally continuous, including the rim,
Temme Exercise 10.3, synopsis TEM-10-08. -/
theorem continuous_conductingDiscPotential : Continuous conductingDiscPotential := by
  sorry

/-- Harmonicity away from the closed conducting disc, Temme Exercise 10.3,
synopsis TEM-10-08. -/
theorem laplacian_conductingDiscPotential {p : EuclideanSpace ℝ (Fin 3)}
    (hp : p 2 ≠ 0 ∨ 1 < (p 0) ^ 2 + (p 1) ^ 2) :
    laplacian conductingDiscPotential p = 0 := by
  sorry

/-- The potential has value one on the entire closed disc, Temme Exercise 10.3,
synopsis TEM-10-08. -/
theorem conductingDiscPotential_eq_one {p : EuclideanSpace ℝ (Fin 3)}
    (hz : p 2 = 0) (hr : (p 0) ^ 2 + (p 1) ^ 2 ≤ 1) :
    conductingDiscPotential p = 1 := by
  sorry

/-- The potential vanishes at spatial infinity, Temme Exercise 10.3,
synopsis TEM-10-08. -/
theorem tendsto_conductingDiscPotential :
    Tendsto conductingDiscPotential (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0) := by
  sorry

/-- The exterior equatorial value of the potential, Temme Exercise 10.3,
synopsis TEM-10-08. -/
theorem conductingDiscPotential_plane {r : ℝ} (hr : 1 < r) :
    conductingDiscPotential (WithLp.toLp 2 ![r, 0, 0]) =
      2 / _root_.Real.pi * _root_.Real.arcsin (1 / r) := by
  sorry

/-- The upper one-sided normal flux on the open disc,
Temme Exercise 10.3, synopsis TEM-10-08. -/
theorem hasDerivWithinAt_conductingDiscPotential_normal {x y : ℝ}
    (h : x ^ 2 + y ^ 2 < 1) :
    HasDerivWithinAt (fun z : ℝ => conductingDiscPotential (WithLp.toLp 2 ![x, y, z]))
      (-2 / (_root_.Real.pi * _root_.Real.sqrt (1 - x ^ 2 - y ^ 2))) (Ici 0) 0 := by
  sorry

end DLMF.WaveEquation.Real
