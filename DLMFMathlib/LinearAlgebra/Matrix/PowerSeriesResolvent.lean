/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Formal matrix resolvents and vertex deletion

Andrews, Askey and Roy, *Special Functions*, §5.8, pp. 266–269.
A finite weighted adjacency matrix may have arbitrary commutative-ring entries.
The statements are formal: every coefficient is a finite walk sum.
-/

@[expose] public noncomputable section

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The formal sum of matrix powers, entry by entry. Andrews–Askey–Roy,
*Special Functions*, §5.8 (synopsis AAR-5.8.1–5.8.2). -/
def powerSeriesResolvent (A : Matrix ι ι R) : Matrix ι ι (PowerSeries R) :=
  fun i j => PowerSeries.mk fun k => (A ^ k) i j

/-- Every resolvent coefficient is the corresponding matrix-power entry. -/
@[simp] theorem coeff_powerSeriesResolvent (A : Matrix ι ι R) (i j : ι) (k : ℕ) :
    (powerSeriesResolvent A i j).coeff k = (A ^ k) i j := by
  simp [powerSeriesResolvent]

/-- The generating series of weighted walks is the two-sided inverse of `I - tA`.
Andrews–Askey–Roy, *Special Functions*, §5.8, pp. 266–269
(synopsis AAR-5.8.1–5.8.2). -/
theorem mul_powerSeriesResolvent (A : Matrix ι ι R) :
    (1 - (PowerSeries.X : PowerSeries R) • A.map (fun r => PowerSeries.C r)) *
        powerSeriesResolvent A = 1 ∧
      powerSeriesResolvent A *
        (1 - (PowerSeries.X : PowerSeries R) • A.map (fun r => PowerSeries.C r)) = 1 := by
  sorry

/-- Deleting a vertex gives the diagonal formal resolvent as a determinant quotient,
written without division. Andrews–Askey–Roy, *Special Functions*, §5.8, pp. 266–269
(synopsis AAR-5.8.1–5.8.2). The denominator has constant coefficient one. -/
theorem powerSeriesResolvent_diagonal_mul_det (A : Matrix ι ι R) (i : ι) :
    powerSeriesResolvent A i i *
        (1 - (PowerSeries.X : PowerSeries R) • A.map (fun r => PowerSeries.C r)).det =
      ((1 - (PowerSeries.X : PowerSeries R) • A.map (fun r => PowerSeries.C r)).submatrix
        (fun j : {j : ι // j ≠ i} => j.val) (fun j : {j : ι // j ≠ i} => j.val)).det := by
  sorry

end Matrix
