/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Selberg.Applications

/-!
# The finite-field Selberg recurrence

Andrews, Askey and Roy, *Special Functions*, Theorem 8.11.2 and its induction,
pp. 435–439. Character powers use `MulChar`'s zero-extension convention.
-/

@[expose] public noncomputable section

namespace DLMF.Selberg

/-- The monic-polynomial finite-field Selberg sum. Andrews–Askey–Roy,
*Special Functions*, equation (8.11.7), pp. 435–439
(synopsis AAR-8.10.4–8.11.2). -/
def finiteFieldSelbergSum {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (n a b c : ℕ) : ℂ :=
  ∑ v : Fin n → F,
    let f := selbergMonicPolynomial v
    χ ((-1 : F) ^ (n * a) * f.eval 0 ^ a * f.eval 1 ^ b * f.discr ^ c) *
      (χ ^ ((Fintype.card F - 1) / 2)) f.discr

/-- The defining finite monic-polynomial sum. -/
theorem finiteFieldSelbergSum_def {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (n a b c : ℕ) :
    finiteFieldSelbergSum χ n a b c =
      ∑ v : Fin n → F,
        let f := selbergMonicPolynomial v
        χ ((-1 : F) ^ (n * a) * f.eval 0 ^ a * f.eval 1 ^ b * f.discr ^ c) *
          (χ ^ ((Fintype.card F - 1) / 2)) f.discr := rfl

/-- The dimension-lowering recurrence for the finite-field Selberg sum.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.11.2, pp. 435–439
(synopsis AAR-8.10.4–8.11.2). All exponent regularity conditions are retained. -/
theorem finiteFieldSelbergSum_succ {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : orderOf χ = Fintype.card F - 1) (hψ : ψ.IsPrimitive)
    (hodd : Odd (Fintype.card F)) (n a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hparams : ∀ j : Fin (n + 1),
      ¬(Fintype.card F - 1) ∣ (a + j.val * c) ∧
      ¬(Fintype.card F - 1) ∣ (b + j.val * c) ∧
      ¬(Fintype.card F - 1) ∣ ((j.val + 1) * c)) :
    let gstar := fun m : ℕ => (Fintype.card F : ℂ) / gaussSum ((χ ^ m)⁻¹) ψ
    finiteFieldSelbergSum χ (n + 1) a b c =
      gstar a * gstar b * gstar ((n + 1) * c) /
        (gstar (a + b + n * c) * gstar c) *
          finiteFieldSelbergSum χ n (a + c) (b + c) c := by
  sorry

end DLMF.Selberg
