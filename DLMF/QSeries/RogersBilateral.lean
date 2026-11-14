/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic.Series

/-!
# Bilateral Rogers–Ramanujan numerators

Andrews, Askey and Roy, *Special Functions*, §12.1, equations preceding
Lemma 12.1.1 (synopsis AAR-12.1.1). Integer exponents avoid a square-root
branch and retain the value at zero base.
-/

@[expose] public noncomputable section
namespace DLMF.QSeries

/-- The bilateral numerator for the first Rogers–Ramanujan identity.
Andrews–Askey–Roy, §12.1 (synopsis AAR-12.1.1). -/
theorem hasSum_rogersRamanujan_first_bilateral {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun k : ℤ => (-1 : ℂ) ^ k * q ^ (k * (5 * k - 1) / 2))
      (qPochhammerInf q q * DLMF.QHypergeometric.rogersG q) := by
  sorry

/-- The bilateral numerator for the second Rogers–Ramanujan identity.
Andrews–Askey–Roy, §12.1 (synopsis AAR-12.1.1). -/
theorem hasSum_rogersRamanujan_second_bilateral {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun k : ℤ => (-1 : ℂ) ^ k * q ^ (k * (5 * k - 3) / 2))
      (qPochhammerInf q q * DLMF.QHypergeometric.rogersH q) := by
  sorry

end DLMF.QSeries
