/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.SphericalHarmonics.Basic.SymmetricPowerMatrix
public import DLMF.OrthogonalPolynomials.Basic.PolynomialContinuation
public import TauCeti.RepresentationTheory.SU2.Exhaustion
public import TauCeti.RepresentationTheory.SU2.Adjoint
public import TauCeti.RingTheory.MvPolynomial.Harmonic.Orthogonal

/-!
# Binary-polynomial realization of the irreducible representations of SU(2)

Andrews, Askey and Roy, *Special Functions*, §§9.13–9.15. The classification itself
is supplied by pinned TauCeti; this module connects it to the book's exact normalized
binomial and Jacobi coefficients, retaining the real-rotation phase convention.
-/

@[expose] public section

noncomputable section

open scoped Matrix TensorProduct

namespace DLMF.SphericalHarmonics

/-- The explicit binary-polynomial matrix is a representation of the matrix monoid.
Andrews–Askey–Roy, *Special Functions*, §9.15 (synopsis AAR-9.11–9.16). -/
theorem suTwoPolynomialMatrix_mul (N : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℂ) :
    suTwoPolynomialMatrix N (g * h) = suTwoPolynomialMatrix N g * suTwoPolynomialMatrix N h :=
  by sorry

/-- The identity acts trivially on normalized binary polynomials.
Andrews–Askey–Roy, *Special Functions*, §9.14 (synopsis AAR-9.11–9.16). -/
theorem suTwoPolynomialMatrix_one (N : ℕ) : suTwoPolynomialMatrix N 1 = 1 := by
  sorry

/-- The binary-polynomial representation is equivalent to the canonical symmetric power.
Andrews–Askey–Roy, *Special Functions*, §§9.13–9.14 (synopsis AAR-9.11–9.16).
The target basis is the normalized monomial basis; no equivalence of unnormalized
weight-basis coordinates is asserted. -/
theorem exists_equiv_suTwoPolynomialMatrix (N : ℕ) :
    ∃ e : Sym[ℂ]^N(Fin 2 → ℂ) ≃ₗ[ℂ] (Fin (N + 1) → ℂ),
      ∀ (g : TauCeti.SU2) (v : Sym[ℂ]^N(Fin 2 → ℂ)),
        e (TauCeti.SU2.symPower N g v) =
          (suTwoPolynomialMatrix N (g : Matrix (Fin 2) (Fin 2) ℂ)).mulVec (e v) := by
  sorry

/-- Normalized monomials give a unitary matrix on SU(2).
Andrews–Askey–Roy, *Special Functions*, Lemma 9.13.1 and §9.15
(synopsis AAR-9.11–9.16). -/
theorem suTwoPolynomialMatrix_conjTranspose_mul (N : ℕ) (g : TauCeti.SU2) :
    (suTwoPolynomialMatrix N (g : Matrix (Fin 2) (Fin 2) ℂ)).conjTranspose *
        suTwoPolynomialMatrix N (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  sorry

/-- Jacobi-polynomial entries for the real rotation convention.
Andrews–Askey–Roy, *Special Functions*, §9.14 (synopsis AAR-9.11–9.16).
Integer powers may be negative, so endpoints are excluded; `jacobiExtended` retains
the polynomial continuation at negative integer parameters. -/
theorem suTwoPolynomialMatrix_rotation (N : ℕ) (j k : Fin (N + 1))
    {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    suTwoPolynomialMatrix N
        !![(Real.cos (θ / 2) : ℂ), -(Real.sin (θ / 2) : ℂ);
           (Real.sin (θ / 2) : ℂ), (Real.cos (θ / 2) : ℂ)] j k =
      (-1 : ℂ) ^ ((k.val : ℤ) - j.val) *
        (Real.sqrt (((N - j.val).factorial : ℝ) * j.val.factorial /
          ((N - k.val).factorial * k.val.factorial)) : ℂ) *
        (Real.sin (θ / 2) : ℂ) ^ ((k.val : ℤ) - j.val) *
        (Real.cos (θ / 2) : ℂ) ^ ((N : ℤ) - j.val - k.val) *
        DLMF.OrthogonalPolynomials.jacobiExtended ((k.val : ℂ) - j.val)
          ((N : ℂ) - j.val - k.val) j.val (Real.cos θ : ℂ) := by
  sorry

/-- The central sign is the parity of the homogeneous degree; this is the criterion
for descent through SU(2) → SO(3). Andrews–Askey–Roy, *Special Functions*, §9.16
(synopsis AAR-9.11–9.16). -/
theorem suTwoPolynomialMatrix_neg_one (N : ℕ) :
    suTwoPolynomialMatrix N (-1) = (-1 : ℂ) ^ N • (1 : Matrix _ _ ℂ) := by
  sorry

/-- A symmetric-power representation descends to SO(3) precisely in even degree.
Andrews–Askey–Roy, *Special Functions*, §9.16, pp. 476–478
(synopsis AAR-9.11–9.16). The quotient map is TauCeti's canonical adjoint cover. -/
theorem exists_representation_soThree_comp_toSO3_iff_even (N : ℕ) :
    (∃ ρ : Representation ℂ (Matrix.specialOrthogonalGroup (Fin 3) ℝ)
      (Sym[ℂ]^N(Fin 2 → ℂ)),
      ∀ g : TauCeti.SU2, ρ (TauCeti.SU2.toSO3 g) = TauCeti.SU2.symPower N g) ↔ Even N := by
  sorry

/-- The even binary representation is the degree-k complex spherical-harmonic model.
Andrews–Askey–Roy, *Special Functions*, §9.16, pp. 476–478
(synopsis AAR-9.11–9.16). The action on a harmonic polynomial is pullback by the
inverse real rotation; the identity is given by evaluation at every real point. -/
theorem exists_equiv_symPower_harmonicSubmodule (k : ℕ) :
    ∃ e : Sym[ℂ]^(2 * k)(Fin 2 → ℂ) ≃ₗ[ℂ]
      MvPolynomial.harmonicSubmodule (Fin 3) ℂ k,
      ∀ (g : TauCeti.SU2) (v : Sym[ℂ]^(2 * k)(Fin 2 → ℂ)) (x : Fin 3 → ℝ),
        MvPolynomial.eval (fun i => (x i : ℂ))
          (e (TauCeti.SU2.symPower (2 * k) g v) : MvPolynomial (Fin 3) ℂ) =
        MvPolynomial.eval (fun i =>
          (((TauCeti.SU2.toSO3 g)⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ).val.mulVec
            x i : ℂ)) (e v : MvPolynomial (Fin 3) ℂ) := by
  sorry

end DLMF.SphericalHarmonics
