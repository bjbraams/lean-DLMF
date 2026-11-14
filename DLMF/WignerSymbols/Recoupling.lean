/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.NineJ
public import DLMF.WignerSymbols.SixJ

/-!
# Clebsch–Gordan overlaps and recoupling normalizations

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
§§5.4, 6.1 and 7.2. Fixed magnetic labels give explicit finite overlaps
with the canonical real Clebsch–Gordan phase convention.
-/

@[expose] public noncomputable section
open Finset
namespace DLMF.WignerSymbols

/-- The three-spin recoupling overlap at a fixed total magnetic label,
Rao–Lakshminarayanan (6.1)–(6.16), synopses RL-6.01–02. -/
theorem sum_four_clebschGordan_eq_wigner6j (j₁ j₂ j₃ J e f M : ℚ)
    (h₁ : IsTriad j₁ j₂ e) (h₂ : IsTriad e j₃ J)
    (h₃ : IsTriad j₂ j₃ f) (h₄ : IsTriad j₁ f J) (hM : IsProjection J M) :
    (∑ m₁ ∈ projections j₁, ∑ m₂ ∈ projections j₂,
      clebschGordan j₁ m₁ j₂ m₂ e (m₁ + m₂) *
        clebschGordan e (m₁ + m₂) j₃ (M - m₁ - m₂) J M *
        clebschGordan j₂ m₂ j₃ (M - m₁ - m₂) f (M - m₁) *
        clebschGordan j₁ m₁ f (M - m₁) J M) =
      signPow (j₁ + j₂ + j₃ + J) * Real.sqrt ((2 * e + 1) * (2 * f + 1) : ℚ) *
        wigner6j j₁ j₂ e j₃ J f := by
  sorry

/-- The four-spin recoupling overlap is independent of the chosen total projection,
Rao–Lakshminarayanan (7.19)–(7.36), synopsis RL-7.04. -/
theorem sum_six_clebschGordan_eq_wigner9j (a b c d e f g h i M : ℚ)
    (hab : IsTriad a b c) (hde : IsTriad d e f) (hcf : IsTriad c f i)
    (had : IsTriad a d g) (hbe : IsTriad b e h) (hgh : IsTriad g h i)
    (hM : IsProjection i M) :
    (∑ ma ∈ projections a, ∑ mb ∈ projections b, ∑ md ∈ projections d,
      ∑ me ∈ projections e,
        if ma + mb + md + me = M then
          clebschGordan a ma b mb c (ma + mb) *
          clebschGordan d md e me f (md + me) *
          clebschGordan c (ma + mb) f (md + me) i M *
          clebschGordan a ma d md g (ma + md) *
          clebschGordan b mb e me h (mb + me) *
          clebschGordan g (ma + md) h (mb + me) i M else 0) =
      Real.sqrt ((2 * c + 1) * (2 * f + 1) * (2 * g + 1) * (2 * h + 1) : ℚ) *
        wigner9j a b c d e f g h i := by
  sorry

end DLMF.WignerSymbols
