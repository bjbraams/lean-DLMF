/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Linear coordinates of the nine-j factorial summand

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
(7.44)–(7.59), pp. 7-10–7-12, synopsis RL-7.08–RL-7.09.
Only the exact linear coordinate identities are asserted here; they do not
assert the conjectural identification of the factorial sum with the nine-j symbol.
The nine spins are ordered row by row as `a,b,c,d,e,f,g,h,i`.
-/

@[expose] public section

namespace DLMF.WignerSymbols.NineJFactorialCoordinates

/-- The five first-index factorial coordinates of RL-7.08. -/
def xParameters (v : Fin 9 → ℚ) : Fin 5 → ℚ :=
  ![2 * v 5, v 3 + v 4 - v 5, v 2 - v 5 + v 8,
    -v 3 + v 4 + v 5, v 2 + v 5 - v 8]

/-- The five second-index factorial coordinates of RL-7.08. -/
def yParameters (v : Fin 9 → ℚ) : Fin 5 → ℚ :=
  ![-v 1 + v 4 + v 7, v 6 + v 7 - v 8, 2 * v 7 + 1,
    v 1 + v 4 - v 7, v 6 - v 7 + v 8]

/-- The five third-index factorial coordinates of RL-7.08. -/
def zParameters (v : Fin 9 → ℚ) : Fin 5 → ℚ :=
  ![2 * v 0, -v 0 + v 1 + v 2, v 0 + v 3 + v 6 + 1,
    v 0 + v 3 - v 6, v 0 - v 1 + v 2]

/-- The three coupled-index factorial coordinates of RL-7.08. -/
def pairParameters (v : Fin 9 → ℚ) : Fin 3 → ℚ :=
  ![v 0 + v 3 - v 7 + v 8, -v 1 + v 3 - v 5 + v 7, -v 0 + v 1 - v 5 + v 8]

/-- The first-index coordinate formula. -/
theorem xParameters_def (v : Fin 9 → ℚ) : xParameters v =
    ![2 * v 5, v 3 + v 4 - v 5, v 2 - v 5 + v 8,
      -v 3 + v 4 + v 5, v 2 + v 5 - v 8] := rfl

/-- The second-index coordinate formula. -/
theorem yParameters_def (v : Fin 9 → ℚ) : yParameters v =
    ![-v 1 + v 4 + v 7, v 6 + v 7 - v 8, 2 * v 7 + 1,
      v 1 + v 4 - v 7, v 6 - v 7 + v 8] := rfl

/-- The third-index coordinate formula. -/
theorem zParameters_def (v : Fin 9 → ℚ) : zParameters v =
    ![2 * v 0, -v 0 + v 1 + v 2, v 0 + v 3 + v 6 + 1,
      v 0 + v 3 - v 6, v 0 - v 1 + v 2] := rfl

/-- The pairwise-index coordinate formula. -/
theorem pairParameters_def (v : Fin 9 → ℚ) : pairParameters v =
    ![v 0 + v 3 - v 7 + v 8, -v 1 + v 3 - v 5 + v 7, -v 0 + v 1 - v 5 + v 8] := rfl

/-- All eight linear identities among the factorial coordinates, without any
admissibility or sign assumptions. Rao–Lakshminarayanan (7.55)–(7.59), synopsis RL-7.09. -/
theorem parameter_relations (v : Fin 9 → ℚ) :
    let X := xParameters v
    let Y := yParameters v
    let Z := zParameters v
    let P := pairParameters v
    ![X 1 + X 3, X 2 + X 4, Y 1 + Y 4 + 1, X 1, X 2, Y 0, P 0, P 2] =
      ![Y 0 + Y 3, Z 1 + Z 4, Z 2 - Z 3, Y 3 + P 1, P 2 + Z 4,
        X 3 + P 1, Y 4 + Z 3, Z 1 - X 4] := by
  funext i
  fin_cases i <;> norm_num [xParameters, yParameters, zParameters, pairParameters] <;> ring

end DLMF.WignerSymbols.NineJFactorialCoordinates
