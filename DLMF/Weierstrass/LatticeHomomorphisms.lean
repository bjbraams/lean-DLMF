/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Torsion

/-!
# Lattice homomorphisms and division points

A scalar `α` with `αΛ ⊆ Μ` induces a homomorphism of the lattice curves, sending
the point of `z` to the point of `αz`. For nonzero `α` it is surjective, with kernel
given by `αz ∈ Μ`. Composition corresponds to multiplication of scalars.
Multiplication by a positive integer has exactly its square many points in its kernel.

Sources: Lang, *Elliptic Functions*, Chapter 1, §4 and Chapter 2, §§1–2;
Koecher–Krieg, *Elliptic Functions and Modular Forms*, Chapter I, §5.
The uniformization and explicit torsion coordinates are reused from TauCeti's
`PeriodPair.weierstrassPointEquiv` and `PeriodPair.torsionEquivCoordinates`.
TauCeti uses `y = ℘'/2`, so the curve is `y² = x³ - g₂x/4 - g₃/4`.
-/

@[expose] public noncomputable section

open Complex

namespace DLMF.Weierstrass

/-- The homomorphism induced by `z ↦ αz` when `α` takes the first lattice into the
second. The zero scalar gives the zero map. -/
def latticeCurveHom (L M : PeriodPair) (α : ℂ)
    (hα : ∀ z ∈ L.lattice, α * z ∈ M.lattice) :
    L.weierstrassCurve.toAffine.Point →+ M.weierstrassCurve.toAffine.Point :=
  M.weierstrassPointEquiv.toAddMonoidHom.comp
    ((QuotientAddGroup.map L.lattice.toAddSubgroup M.lattice.toAddSubgroup
      (LinearMap.mulLeft ℤ α).toAddMonoidHom hα).comp
        L.weierstrassPointEquiv.symm.toAddMonoidHom)

/-- On uniformizing points the induced map multiplies the argument by its scalar. -/
@[simp]
theorem latticeCurveHom_weierstrassPoint (L M : PeriodPair) (α : ℂ)
    (hα : ∀ z ∈ L.lattice, α * z ∈ M.lattice) (z : ℂ) :
    latticeCurveHom L M α hα (L.weierstrassPoint z) = M.weierstrassPoint (α * z) := by
  dsimp only [latticeCurveHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [L.weierstrassPointEquiv_symm_weierstrassPoint]
  have hm := QuotientAddGroup.map_mk L.lattice.toAddSubgroup M.lattice.toAddSubgroup
    (LinearMap.mulLeft ℤ α).toAddMonoidHom hα z
  rw [hm]
  exact M.weierstrassPointEquiv_mk (α * z)

/-- The induced curve homomorphism is uniquely characterized by its action on
uniformizing points. This gives an introduction and elimination rule without unfolding it. -/
theorem eq_latticeCurveHom_iff (L M : PeriodPair) (α : ℂ)
    (hα : ∀ z ∈ L.lattice, α * z ∈ M.lattice)
    (f : L.weierstrassCurve.toAffine.Point →+ M.weierstrassCurve.toAffine.Point) :
    f = latticeCurveHom L M α hα ↔
      ∀ z, f (L.weierstrassPoint z) = M.weierstrassPoint (α * z) := by
  constructor
  · rintro rfl
    exact latticeCurveHom_weierstrassPoint L M α hα
  · intro h
    ext P
    obtain ⟨z, rfl⟩ := L.weierstrassPoint_surjective P
    rw [h, latticeCurveHom_weierstrassPoint]

/-- A point lies in the kernel precisely when its scaled argument is in the target lattice. -/
theorem latticeCurveHom_weierstrassPoint_eq_zero_iff (L M : PeriodPair) (α : ℂ)
    (hα : ∀ z ∈ L.lattice, α * z ∈ M.lattice) (z : ℂ) :
    latticeCurveHom L M α hα (L.weierstrassPoint z) = 0 ↔ α * z ∈ M.lattice := by
  rw [latticeCurveHom_weierstrassPoint, M.weierstrassPoint_eq_zero_iff]

/-- Every nonzero scalar preserving the lattices induces a surjective curve homomorphism. -/
theorem surjective_latticeCurveHom (L M : PeriodPair) {α : ℂ}
    (hα : ∀ z ∈ L.lattice, α * z ∈ M.lattice) (hα₀ : α ≠ 0) :
    Function.Surjective (latticeCurveHom L M α hα) := by
  intro P
  obtain ⟨z, rfl⟩ := M.weierstrassPoint_surjective P
  refine ⟨L.weierstrassPoint (z / α), ?_⟩
  rw [latticeCurveHom_weierstrassPoint, mul_div_cancel₀ _ hα₀]

/-- Injectivity means that scaling introduces no extra points above the target lattice. -/
theorem injective_latticeCurveHom_iff (L M : PeriodPair) (α : ℂ)
    (hα : ∀ z ∈ L.lattice, α * z ∈ M.lattice) :
    Function.Injective (latticeCurveHom L M α hα) ↔
      ∀ z, α * z ∈ M.lattice → z ∈ L.lattice := by
  rw [← AddMonoidHom.ker_eq_bot_iff]
  constructor
  · intro h z hz
    have hp : L.weierstrassPoint z ∈ (latticeCurveHom L M α hα).ker := by
      simpa using (latticeCurveHom_weierstrassPoint_eq_zero_iff L M α hα z).mpr hz
    rw [h, AddSubgroup.mem_bot] at hp
    exact L.weierstrassPoint_eq_zero_iff.mp hp
  · intro h
    refine le_antisymm ?_ bot_le
    intro P hP
    obtain ⟨z, rfl⟩ := L.weierstrassPoint_surjective P
    apply AddSubgroup.mem_bot.mpr
    apply L.weierstrassPoint_eq_zero_iff.mpr
    exact h z ((latticeCurveHom_weierstrassPoint_eq_zero_iff L M α hα z).mp hP)

/-- Composition of induced homomorphisms corresponds to multiplication of their scalars. -/
theorem latticeCurveHom_comp (L M N : PeriodPair) (α β : ℂ)
    (hα : ∀ z ∈ L.lattice, α * z ∈ M.lattice)
    (hβ : ∀ z ∈ M.lattice, β * z ∈ N.lattice) :
    (latticeCurveHom M N β hβ).comp (latticeCurveHom L M α hα) =
      latticeCurveHom L N (β * α) (fun z hz => by
        simpa [mul_assoc] using hβ _ (hα z hz)) := by
  ext P
  obtain ⟨z, rfl⟩ := L.weierstrassPoint_surjective P
  simp [mul_assoc]

/-- Integer scalar multiplication of arguments is integer multiplication on the curve. -/
theorem latticeCurveHom_natCast (L : PeriodPair) (n : ℕ) :
    latticeCurveHom L L (n : ℂ) (fun z hz => by
      simpa only [zsmul_eq_mul, Int.cast_natCast] using L.lattice.smul_mem (n : ℤ) hz) =
        n • AddMonoidHom.id L.weierstrassCurve.toAffine.Point := by
  ext P
  obtain ⟨z, rfl⟩ := L.weierstrassPoint_surjective P
  simp [← L.weierstrassPoint_nsmul, nsmul_eq_mul]

/-- There are `N²` division points killed by a nonzero natural number `N`,
including the identity. This derives the count from TauCeti's actual torsion coordinates. -/
theorem natCard_torsionBy_latticeCurve (L : PeriodPair) (N : ℕ) [NeZero N] :
    Nat.card (AddSubgroup.torsionBy L.weierstrassCurve.toAffine.Point (N : ℤ)) = N ^ 2 := by
  rw [Nat.card_congr (L.torsionEquivCoordinates N).toEquiv]
  simp [Nat.card_eq_fintype_card]

end DLMF.Weierstrass
