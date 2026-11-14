/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.Partitions
public import DLMF.QSeries.Basic

/-!
# Ramanujan's seven-dissection and congruence modulo eleven

The remaining identities in Andrews, Askey and Roy, *Special Functions*, §11.7.
The congruences modulo five and seven and the five-dissection are already present.
-/

@[expose] public section

namespace DLMF.NumberTheory

open DLMF.Partitions PowerSeries

/-- Ramanujan's exact seven-dissection. Andrews–Askey–Roy,
*Special Functions*, §11.7 (synopsis AAR-11.5.1–11.7). -/
theorem hasSum_partitionFunction_seven {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (partitionFunction (7 * n + 5) : ℂ) * q ^ n)
      (7 * DLMF.QSeries.qPochhammerInf (q ^ 7) (q ^ 7) ^ 3 /
          DLMF.QSeries.qPochhammerInf q q ^ 4 +
        49 * q * DLMF.QSeries.qPochhammerInf (q ^ 7) (q ^ 7) ^ 7 /
          DLMF.QSeries.qPochhammerInf q q ^ 8) := by
  sorry

/-- The formal seven-dissection after multiplying by the eighth power of Euler's
product. Andrews–Askey–Roy, *Special Functions*, §11.7
(synopsis AAR-11.5.1–11.7). -/
theorem partitionPowerSeries_seven_dissection :
    (PowerSeries.mk (fun n : ℕ => (partitionFunction (7 * n + 5) : ℤ))) *
        pentagonalSeries ℤ ^ 8 =
      7 * (PowerSeries.expand 7 (by decide) (pentagonalSeries ℤ)) ^ 3 * pentagonalSeries ℤ ^ 4 +
        49 * PowerSeries.X * (PowerSeries.expand 7 (by decide) (pentagonalSeries ℤ)) ^ 7 := by
  sorry

/-- Ramanujan's partition congruence modulo eleven. Andrews–Askey–Roy,
*Special Functions*, §11.7 (synopsis AAR-11.5.1–11.7). -/
theorem eleven_dvd_card_partition (n : ℕ) :
    11 ∣ Fintype.card (Nat.Partition (11 * n + 6)) := by
  sorry

/-- The exact formal five-dissection after clearing Euler-product denominators.
Andrews–Askey–Roy, §11.7, synopsis AAR-11.5.1–11.7. -/
theorem partitionPowerSeries_five_dissection :
    (PowerSeries.mk (fun n : ℕ => (partitionFunction (5 * n + 4) : ℤ))) *
      pentagonalSeries ℤ ^ 6 =
        5 * (PowerSeries.expand 5 (by decide) (pentagonalSeries ℤ)) ^ 5 := by
  sorry

end DLMF.NumberTheory
