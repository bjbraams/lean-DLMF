/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.SmallQSpectrum

/-!
# The expansion DLMF 28.6.14 of `a_m(q)`, `b_m(q)` for general `m`

For `m ≥ 7` the eigenvalues have the common expansion
`m² + q²/(2(m²-1)) + (5m²+7)q⁴/(32(m²-1)³(m²-4)) + (9m⁴+58m²+29)q⁶/(64(m²-1)⁵(m²-4)(m²-9))`
up to `O(q^{min(m,8)})` (DLMF 28.6.14). It is proved with the eigenvalue estimates
`mathieuA_even_sub_isBigO_of_trial`, …, `mathieuB_odd_sub_isBigO_of_trial` of
`DLMF.Mathieu.SmallQSpectrum` (instances of `eigenvalue_sub_isBigO_of_trial` of
`DLMF.Mathieu.SmallQJacobi`), applied to a trial vector
`v_i = T_{i-n}(m, q)` whose components are rational in `m` (obtained by Rayleigh–Schrödinger
perturbation theory). The rows of the recurrence applied to `T` are the explicit multiples
`q^{8-|j|} genericEigenResidual m q j` of `q`-powers. For `m ≥ 8` all four recurrences
28.4.5–28.4.8 agree with the generic diagonal `(m + 2j)²` on the support of `T`, so the
remainder is `O(q⁸)`. At `m = 7` the boundary term `±q` of 28.4.6–28.4.7 meets the support and
the remainder is `O(q⁷)`.

## Main definitions

* `genericEigenvaluePoly`: the polynomial of DLMF 28.6.14, with `m`, `q` complex.
* `genericEigenTrialVector`: the trial vector `T_j(m, q)`, `|j| ≤ 3`, with components
  `genericEigenTrialNegThree`, …, `genericEigenTrialThree`.
* `genericEigenResidual`: the residual quotients, with components `genericEigenResidualNegFour`,
  …, `genericEigenResidualFour`.
* `IsGenericOrder`: nonvanishing of the denominators of the trial vector and residuals.

## Main results

* `mathieuA_sub_isBigO_of_eight_le`, `mathieuB_sub_isBigO_of_eight_le`: DLMF 28.6.14 for
  `m ≥ 8`, with remainder `O(q⁸)`.
* `mathieuA_seven_sub_isBigO`, `mathieuB_seven_sub_isBigO`: DLMF 28.6.14 at `m = 7`, with
  remainder `O(q⁷)`.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-- The DLMF 28.6.14 polynomial `m² + q²/(2(m²-1)) + ⋯`, with `m`, `q` complex. -/
def genericEigenvaluePoly (m q : ℂ) : ℂ :=
  m ^ 2 + q ^ 2 / (2 * (m ^ 2 - 1)) +
    (5 * m ^ 2 + 7) * q ^ 4 / (32 * (m ^ 2 - 1) ^ 3 * (m ^ 2 - 4)) +
    (9 * m ^ 4 + 58 * m ^ 2 + 29) * q ^ 6 /
      (64 * (m ^ 2 - 1) ^ 5 * (m ^ 2 - 4) * (m ^ 2 - 9))

/-- The component `j = -3` of `genericEigenTrialVector` (a polynomial in `q`). -/
def genericEigenTrialNegThree (m q : ℂ) : ℂ :=
  (1/(384*(m - 3)*(m - 2)*(m - 1))) * q ^ 3

/-- The component `j = -2` of `genericEigenTrialVector` (a polynomial in `q`). -/
def genericEigenTrialNegTwo (m q : ℂ) : ℂ :=
  (1/(32*(m - 2)*(m - 1))) * q ^ 2 + ((m^2 - 5*m + 10)/(768*(m - 3)*(m - 2)*(m - 1)^3*(m + 1))) *
    q ^ 4

/-- The component `j = -1` of `genericEigenTrialVector` (a polynomial in `q`). -/
def genericEigenTrialNegOne (m q : ℂ) : ℂ :=
  (1/(4*(m - 1))) * q ^ 1 + ((m^2 - 4*m + 7)/(128*(m - 2)*(m - 1)^3*(m + 1))) * q ^ 3 + ((m^6 -
    5*m^5 + 8*m^4 - 8*m^3 + 47*m^2 + 13*m + 232)/(3072*(m - 3)*(m - 2)*(m - 1)^5*(m + 1)^3*(m +
    2))) * q ^ 5

/-- The component `j = 0` of `genericEigenTrialVector` (a polynomial in `q`). -/
def genericEigenTrialZero (_m _q : ℂ) : ℂ :=
  (1)

/-- The component `j = 1` of `genericEigenTrialVector` (a polynomial in `q`). -/
def genericEigenTrialOne (m q : ℂ) : ℂ :=
  (-1/(4*(m + 1))) * q ^ 1 + (-(m^2 + 4*m + 7)/(128*(m - 1)*(m + 1)^3*(m + 2))) * q ^ 3 + (-(m^6 +
    5*m^5 + 8*m^4 + 8*m^3 + 47*m^2 - 13*m + 232)/(3072*(m - 2)*(m - 1)^3*(m + 1)^5*(m + 2)*(m +
    3))) * q ^ 5

/-- The component `j = 2` of `genericEigenTrialVector` (a polynomial in `q`). -/
def genericEigenTrialTwo (m q : ℂ) : ℂ :=
  (1/(32*(m + 1)*(m + 2))) * q ^ 2 + ((m^2 + 5*m + 10)/(768*(m - 1)*(m + 1)^3*(m + 2)*(m + 3))) *
    q ^ 4

/-- The component `j = 3` of `genericEigenTrialVector` (a polynomial in `q`). -/
def genericEigenTrialThree (m q : ℂ) : ℂ :=
  (-1/(384*(m + 1)*(m + 2)*(m + 3))) * q ^ 3

/-- The generic trial vector `T_j(m, q)`, `|j| ≤ 3`, of the perturbation series of
`a_m(q)`, `b_m(q)` (DLMF 28.6.14): `T_0 = 1`, `T_j = O(q^{|j|})`, and `T_j = 0` for `|j| ≥ 4`. -/
def genericEigenTrialVector (m q : ℂ) (j : ℤ) : ℂ :=
  if j = -3 then genericEigenTrialNegThree m q
  else if j = -2 then genericEigenTrialNegTwo m q
  else if j = -1 then genericEigenTrialNegOne m q
  else if j = 0 then genericEigenTrialZero m q
  else if j = 1 then genericEigenTrialOne m q
  else if j = 2 then genericEigenTrialTwo m q
  else if j = 3 then genericEigenTrialThree m q
  else 0

/-- The component `j = -4` of `genericEigenResidual` (the residual quotient). -/
def genericEigenResidualNegFour (m _q : ℂ) : ℂ :=
  (1/(384*(m - 3)*(m - 2)*(m - 1)))

/-- The component `j = -3` of `genericEigenResidual` (the residual quotient). -/
def genericEigenResidualNegThree (m q : ℂ) : ℂ :=
  ((m^2 - 6*m + 11)/(768*(m - 3)*(m - 2)*(m - 1)^3*(m + 1))) + (-(5*m^2 + 7)/(12288*(m - 3)*(m -
    2)^2*(m - 1)^4*(m + 1)^3*(m + 2))) * q ^ 2 + (-(9*m^4 + 58*m^2 + 29)/(24576*(m - 3)^2*(m -
    2)^2*(m - 1)^6*(m + 1)^5*(m + 2)*(m + 3))) * q ^ 4

/-- The component `j = -2` of `genericEigenResidual` (the residual quotient). -/
def genericEigenResidualNegTwo (m q : ℂ) : ℂ :=
  ((m^7 - 9*m^6 + 28*m^5 - 49*m^4 + 73*m^3 - 55*m^2 + 330*m - 607)/(3072*(m - 3)*(m - 2)^2*(m -
    1)^5*(m + 1)^3*(m + 2))) + (-(5*m^6 - 5*m^5 + 80*m^4 + 118*m^3 + 797*m^2 + 175*m +
    558)/(24576*(m - 3)*(m - 2)^2*(m - 1)^6*(m + 1)^5*(m + 2)*(m + 3))) * q ^ 2 + (-(m^2 - 5*m +
    10)*(9*m^4 + 58*m^2 + 29)/(49152*(m - 3)^2*(m - 2)^2*(m - 1)^8*(m + 1)^6*(m + 2)*(m + 3))) * q
    ^ 4

/-- The component `j = -1` of `genericEigenResidual` (the residual quotient). -/
def genericEigenResidualNegOne (m q : ℂ) : ℂ :=
  (-(2*m^9 - 6*m^8 + m^7 + 9*m^6 + 405*m^5 - 219*m^4 + 2395*m^3 - 5565*m^2 - 1651*m -
    6891)/(12288*(m - 3)*(m - 2)^2*(m - 1)^6*(m + 1)^5*(m + 2)*(m + 3))) + (-(5*m^9 - 10*m^8 +
    80*m^7 - 150*m^6 + 654*m^5 + 1002*m^4 + 1168*m^3 + 13606*m^2 + 1549*m + 9744)/(98304*(m -
    3)*(m - 2)^2*(m - 1)^8*(m + 1)^6*(m + 2)^2*(m + 3))) * q ^ 2 + (-(9*m^4 + 58*m^2 + 29)*(m^6 -
    5*m^5 + 8*m^4 - 8*m^3 + 47*m^2 + 13*m + 232)/(196608*(m - 3)^2*(m - 2)^2*(m - 1)^10*(m +
    1)^8*(m + 2)^2*(m + 3))) * q ^ 4

/-- The component `j = 0` of `genericEigenResidual` (the residual quotient). -/
def genericEigenResidualZero (_m _q : ℂ) : ℂ :=
  0

/-- The component `j = 1` of `genericEigenResidual` (the residual quotient). -/
def genericEigenResidualOne (m q : ℂ) : ℂ :=
  ((2*m^9 + 6*m^8 + m^7 - 9*m^6 + 405*m^5 + 219*m^4 + 2395*m^3 + 5565*m^2 - 1651*m +
    6891)/(12288*(m - 3)*(m - 2)*(m - 1)^5*(m + 1)^6*(m + 2)^2*(m + 3))) + ((5*m^9 + 10*m^8 +
    80*m^7 + 150*m^6 + 654*m^5 - 1002*m^4 + 1168*m^3 - 13606*m^2 + 1549*m - 9744)/(98304*(m -
    3)*(m - 2)^2*(m - 1)^6*(m + 1)^8*(m + 2)^2*(m + 3))) * q ^ 2 + ((9*m^4 + 58*m^2 + 29)*(m^6 +
    5*m^5 + 8*m^4 + 8*m^3 + 47*m^2 - 13*m + 232)/(196608*(m - 3)*(m - 2)^2*(m - 1)^8*(m + 1)^10*(m
    + 2)^2*(m + 3)^2)) * q ^ 4

/-- The component `j = 2` of `genericEigenResidual` (the residual quotient). -/
def genericEigenResidualTwo (m q : ℂ) : ℂ :=
  (-(m^7 + 9*m^6 + 28*m^5 + 49*m^4 + 73*m^3 + 55*m^2 + 330*m + 607)/(3072*(m - 2)*(m - 1)^3*(m +
    1)^5*(m + 2)^2*(m + 3))) + (-(5*m^6 + 5*m^5 + 80*m^4 - 118*m^3 + 797*m^2 - 175*m +
    558)/(24576*(m - 3)*(m - 2)*(m - 1)^5*(m + 1)^6*(m + 2)^2*(m + 3))) * q ^ 2 + (-(m^2 + 5*m +
    10)*(9*m^4 + 58*m^2 + 29)/(49152*(m - 3)*(m - 2)*(m - 1)^6*(m + 1)^8*(m + 2)^2*(m + 3)^2)) * q
    ^ 4

/-- The component `j = 3` of `genericEigenResidual` (the residual quotient). -/
def genericEigenResidualThree (m q : ℂ) : ℂ :=
  ((m^2 + 6*m + 11)/(768*(m - 1)*(m + 1)^3*(m + 2)*(m + 3))) + ((5*m^2 + 7)/(12288*(m - 2)*(m -
    1)^3*(m + 1)^4*(m + 2)^2*(m + 3))) * q ^ 2 + ((9*m^4 + 58*m^2 + 29)/(24576*(m - 3)*(m - 2)*(m
    - 1)^5*(m + 1)^6*(m + 2)^2*(m + 3)^2)) * q ^ 4

/-- The component `j = 4` of `genericEigenResidual` (the residual quotient). -/
def genericEigenResidualFour (m _q : ℂ) : ℂ :=
  (-1/(384*(m + 1)*(m + 2)*(m + 3)))

/-- The residual quotient: row `j` of the generic recurrence applied to `genericEigenTrialVector`
equals `q^{8-|j|} genericEigenResidual m q j` (`genericEigenTrial_row`). -/
def genericEigenResidual (m q : ℂ) (j : ℤ) : ℂ :=
  if j = -4 then genericEigenResidualNegFour m q
  else if j = -3 then genericEigenResidualNegThree m q
  else if j = -2 then genericEigenResidualNegTwo m q
  else if j = -1 then genericEigenResidualNegOne m q
  else if j = 0 then genericEigenResidualZero m q
  else if j = 1 then genericEigenResidualOne m q
  else if j = 2 then genericEigenResidualTwo m q
  else if j = 3 then genericEigenResidualThree m q
  else if j = 4 then genericEigenResidualFour m q
  else 0

/-- Nonvanishing of the denominators of `genericEigenTrialVector`, `genericEigenResidual`. -/
structure IsGenericOrder (m : ℂ) : Prop where
  /-- `m - 1 ≠ 0`. -/
  h1 : m - 1 ≠ 0
  /-- `m - 2 ≠ 0`. -/
  h2 : m - 2 ≠ 0
  /-- `m - 3 ≠ 0`. -/
  h3 : m - 3 ≠ 0
  /-- `m + 1 ≠ 0`. -/
  h1' : m + 1 ≠ 0
  /-- `m + 2 ≠ 0`. -/
  h2' : m + 2 ≠ 0
  /-- `m + 3 ≠ 0`. -/
  h3' : m + 3 ≠ 0

/-- Under `IsGenericOrder m`, `m² - 1 ≠ 0`. -/
theorem IsGenericOrder.sq1 {m : ℂ} (h : IsGenericOrder m) : m ^ 2 - 1 ≠ 0 := by
  rw [show m ^ 2 - 1 = (m - 1) * (m + 1) by ring]; exact mul_ne_zero h.h1 h.h1'

/-- Under `IsGenericOrder m`, `m² - 4 ≠ 0`. -/
lemma IsGenericOrder.sq4 {m : ℂ} (h : IsGenericOrder m) : m ^ 2 - 4 ≠ 0 := by
  rw [show m ^ 2 - 4 = (m - 2) * (m + 2) by ring]; exact mul_ne_zero h.h2 h.h2'

/-- Under `IsGenericOrder m`, `m² - 9 ≠ 0`. -/
lemma IsGenericOrder.sq9 {m : ℂ} (h : IsGenericOrder m) : m ^ 2 - 9 ≠ 0 := by
  rw [show m ^ 2 - 9 = (m - 3) * (m + 3) by ring]; exact mul_ne_zero h.h3 h.h3'

/-- Row `j = -4` of the generic row identity `genericEigenTrial_row`. -/
private lemma genericEigenTrial_row_negFour {m : ℂ} (hm : IsGenericOrder m) (q : ℂ) :
    ((m + 2 * ((-4 : ℤ) : ℂ)) ^ 2 - genericEigenvaluePoly m q) *
        genericEigenTrialVector m q (-4 : ℤ) +
      q * (genericEigenTrialVector m q ((-4 : ℤ) - 1) +
          genericEigenTrialVector m q ((-4 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (-4 : ℤ)) * genericEigenResidual m q (-4 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [genericEigenTrialVector, genericEigenResidual]
  simp only [genericEigenTrialNegThree, genericEigenResidualNegFour]
  field_simp

/-- Row `j = -3` of the generic row identity `genericEigenTrial_row`. -/
private lemma genericEigenTrial_row_negThree {m : ℂ} (hm : IsGenericOrder m) (q : ℂ) :
    ((m + 2 * ((-3 : ℤ) : ℂ)) ^ 2 - genericEigenvaluePoly m q) *
        genericEigenTrialVector m q (-3 : ℤ) +
      q * (genericEigenTrialVector m q ((-3 : ℤ) - 1) +
          genericEigenTrialVector m q ((-3 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (-3 : ℤ)) * genericEigenResidual m q (-3 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [genericEigenTrialVector, genericEigenResidual]
  simp only [genericEigenTrialNegThree, genericEigenTrialNegTwo, genericEigenResidualNegThree,
      genericEigenvaluePoly]
  field_simp
  ring

/-- Row `j = -2` of the generic row identity `genericEigenTrial_row`. -/
private lemma genericEigenTrial_row_negTwo {m : ℂ} (hm : IsGenericOrder m) (q : ℂ) :
    ((m + 2 * ((-2 : ℤ) : ℂ)) ^ 2 - genericEigenvaluePoly m q) *
        genericEigenTrialVector m q (-2 : ℤ) +
      q * (genericEigenTrialVector m q ((-2 : ℤ) - 1) +
          genericEigenTrialVector m q ((-2 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (-2 : ℤ)) * genericEigenResidual m q (-2 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [genericEigenTrialVector, genericEigenResidual]
  simp only [genericEigenTrialNegThree, genericEigenTrialNegTwo, genericEigenTrialNegOne,
      genericEigenResidualNegTwo, genericEigenvaluePoly]
  field_simp
  ring

/-- Row `j = -1` of the generic row identity `genericEigenTrial_row`. -/
private lemma genericEigenTrial_row_negOne {m : ℂ} (hm : IsGenericOrder m) (q : ℂ) :
    ((m + 2 * ((-1 : ℤ) : ℂ)) ^ 2 - genericEigenvaluePoly m q) *
        genericEigenTrialVector m q (-1 : ℤ) +
      q * (genericEigenTrialVector m q ((-1 : ℤ) - 1) +
          genericEigenTrialVector m q ((-1 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (-1 : ℤ)) * genericEigenResidual m q (-1 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [genericEigenTrialVector, genericEigenResidual]
  simp only [genericEigenTrialNegTwo, genericEigenTrialNegOne, genericEigenTrialZero,
      genericEigenResidualNegOne, genericEigenvaluePoly]
  field_simp
  ring

/-- Row `j = 0` of the generic row identity `genericEigenTrial_row`. -/
private lemma genericEigenTrial_row_zero {m : ℂ} (hm : IsGenericOrder m) (q : ℂ) :
    ((m + 2 * ((0 : ℤ) : ℂ)) ^ 2 - genericEigenvaluePoly m q) *
        genericEigenTrialVector m q (0 : ℤ) +
      q * (genericEigenTrialVector m q ((0 : ℤ) - 1) + genericEigenTrialVector m q ((0 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (0 : ℤ)) * genericEigenResidual m q (0 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [genericEigenTrialVector, genericEigenResidual]
  simp only [genericEigenTrialNegOne, genericEigenTrialZero, genericEigenTrialOne,
      genericEigenResidualZero, genericEigenvaluePoly]
  field_simp
  ring

/-- Row `j = 1` of the generic row identity `genericEigenTrial_row`. -/
private lemma genericEigenTrial_row_one {m : ℂ} (hm : IsGenericOrder m) (q : ℂ) :
    ((m + 2 * ((1 : ℤ) : ℂ)) ^ 2 - genericEigenvaluePoly m q) *
        genericEigenTrialVector m q (1 : ℤ) +
      q * (genericEigenTrialVector m q ((1 : ℤ) - 1) + genericEigenTrialVector m q ((1 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (1 : ℤ)) * genericEigenResidual m q (1 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [genericEigenTrialVector, genericEigenResidual]
  simp only [genericEigenTrialZero, genericEigenTrialOne, genericEigenTrialTwo,
      genericEigenResidualOne, genericEigenvaluePoly]
  field_simp
  ring

/-- Row `j = 2` of the generic row identity `genericEigenTrial_row`. -/
private lemma genericEigenTrial_row_two {m : ℂ} (hm : IsGenericOrder m) (q : ℂ) :
    ((m + 2 * ((2 : ℤ) : ℂ)) ^ 2 - genericEigenvaluePoly m q) *
        genericEigenTrialVector m q (2 : ℤ) +
      q * (genericEigenTrialVector m q ((2 : ℤ) - 1) + genericEigenTrialVector m q ((2 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (2 : ℤ)) * genericEigenResidual m q (2 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [genericEigenTrialVector, genericEigenResidual]
  simp only [genericEigenTrialOne, genericEigenTrialTwo, genericEigenTrialThree,
      genericEigenResidualTwo, genericEigenvaluePoly]
  field_simp
  ring

/-- Row `j = 3` of the generic row identity `genericEigenTrial_row`. -/
private lemma genericEigenTrial_row_three {m : ℂ} (hm : IsGenericOrder m) (q : ℂ) :
    ((m + 2 * ((3 : ℤ) : ℂ)) ^ 2 - genericEigenvaluePoly m q) *
        genericEigenTrialVector m q (3 : ℤ) +
      q * (genericEigenTrialVector m q ((3 : ℤ) - 1) + genericEigenTrialVector m q ((3 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (3 : ℤ)) * genericEigenResidual m q (3 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [genericEigenTrialVector, genericEigenResidual]
  simp only [genericEigenTrialTwo, genericEigenTrialThree, genericEigenResidualThree,
      genericEigenvaluePoly]
  field_simp
  ring

/-- Row `j = 4` of the generic row identity `genericEigenTrial_row`. -/
private lemma genericEigenTrial_row_four {m : ℂ} (hm : IsGenericOrder m) (q : ℂ) :
    ((m + 2 * ((4 : ℤ) : ℂ)) ^ 2 - genericEigenvaluePoly m q) *
        genericEigenTrialVector m q (4 : ℤ) +
      q * (genericEigenTrialVector m q ((4 : ℤ) - 1) + genericEigenTrialVector m q ((4 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (4 : ℤ)) * genericEigenResidual m q (4 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [genericEigenTrialVector, genericEigenResidual]
  simp only [genericEigenTrialThree, genericEigenResidualFour]
  field_simp

/-- The trial vector vanishes outside its support: `T_j = 0` for `|j| ≥ 4`. -/
private lemma genericEigenTrial_eq_zero_of_four_le_natAbs (m q : ℂ) {j : ℤ} (hj : 4 ≤ j.natAbs) :
    genericEigenTrialVector m q j = 0 := by
  unfold genericEigenTrialVector
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The residual quotient vanishes for `|j| ≥ 5`. -/
private lemma genericEigenResidual_eq_zero_of_five_le_natAbs (m q : ℂ) {j : ℤ} (hj : 5 ≤ j.natAbs) :
    genericEigenResidual m q j = 0 := by
  unfold genericEigenResidual
  split_ifs <;> first | rfl | (exfalso; omega)

/-- **Generic row identity.** Row `j` of the recurrence
`((m + 2j)² - P) T_j + q (T_{j-1} + T_{j+1})` with the DLMF 28.6.14 polynomial
`P = genericEigenvaluePoly m q` is `q^{8-|j|} genericEigenResidual m q j`. -/
private lemma genericEigenTrial_row {m : ℂ} (hm : IsGenericOrder m) (q : ℂ) (j : ℤ) :
    ((m + 2 * (j : ℂ)) ^ 2 - genericEigenvaluePoly m q) * genericEigenTrialVector m q j +
      q * (genericEigenTrialVector m q (j - 1) + genericEigenTrialVector m q (j + 1)) =
      q ^ (8 - Int.natAbs j) * genericEigenResidual m q j := by
  by_cases hj : j.natAbs ≤ 4
  · have h1 : -4 ≤ j := by omega
    have h2 : j ≤ 4 := by omega
    interval_cases j
    · exact genericEigenTrial_row_negFour hm q
    · exact genericEigenTrial_row_negThree hm q
    · exact genericEigenTrial_row_negTwo hm q
    · exact genericEigenTrial_row_negOne hm q
    · exact genericEigenTrial_row_zero hm q
    · exact genericEigenTrial_row_one hm q
    · exact genericEigenTrial_row_two hm q
    · exact genericEigenTrial_row_three hm q
    · exact genericEigenTrial_row_four hm q
  · rw [genericEigenTrial_eq_zero_of_four_le_natAbs m q (by omega),
        genericEigenTrial_eq_zero_of_four_le_natAbs m q (by omega),
      genericEigenTrial_eq_zero_of_four_le_natAbs m q (by omega),
          genericEigenResidual_eq_zero_of_five_le_natAbs m q (by omega)]
    ring

/-- Each component `T_j(m, q)` is continuous in real `q`. -/
private lemma continuous_genericEigenTrial (m : ℂ) (j : ℤ) : Continuous fun q : ℝ =>
    genericEigenTrialVector m q j := by
  unfold genericEigenTrialVector
  split_ifs <;>
    (try simp only [genericEigenTrialNegThree, genericEigenTrialNegTwo, genericEigenTrialNegOne,
        genericEigenTrialZero, genericEigenTrialOne, genericEigenTrialTwo,
        genericEigenTrialThree]) <;>
    fun_prop

/-- Each residual quotient `genericEigenResidual m q j` is continuous in real `q`. -/
private lemma continuous_genericEigenResidual (m : ℂ) (j : ℤ) : Continuous fun q : ℝ =>
    genericEigenResidual m q j := by
  unfold genericEigenResidual
  split_ifs <;>
    (try simp only [genericEigenResidualNegFour, genericEigenResidualNegThree,
        genericEigenResidualNegTwo, genericEigenResidualNegOne, genericEigenResidualZero,
        genericEigenResidualOne, genericEigenResidualTwo, genericEigenResidualThree,
      genericEigenResidualFour]) <;>
    fun_prop

/-- For a natural number `k ≥ 4`, the denominators `k ± 1, k ± 2, k ± 3` are nonzero. -/
theorem isGenericOrder_natCast {k : ℕ} (hk : 4 ≤ k) : IsGenericOrder (k : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith [show (4 : ℝ) ≤ k by exact_mod_cast hk]

/-- The residual rows of the generic trial vector `v_i = T_{i-n}` in a recurrence whose diagonal
agrees with `(m + 2(i - n))²` for `|i - n| ≤ 3`. -/
private lemma genericEigenTrial_residual_isBigO {D : ℝ → ℕ → ℂ} {β : ℂ} {n : ℕ} {m : ℂ}
    (hm : IsGenericOrder m) (hn : 3 ≤ n)
    (hβ : n = 3 → β = 1)
    (hD : ∀ q i, n ≤ i + 3 → i ≤ n + 3 → D q i = (m + 2 * ((i : ℂ) - n)) ^ 2) (i : ℕ) :
    (fun q : ℝ => recurrenceOperator (D q) β q
        (fun i => genericEigenTrialVector m q ((i : ℤ) - n)) i -
      genericEigenvaluePoly m q *
          genericEigenTrialVector m q ((i : ℤ) - n)) =O[𝓝 0]
          (fun q : ℝ => q ^ (8 - Nat.dist i n)) := by
  have hdist : Nat.dist i n = ((i : ℤ) - n).natAbs := by
    unfold Nat.dist; omega
  refine isBigO_pow_of_eq_pow_mul (e := 8 - ((i : ℤ) - n).natAbs) (by omega)
    (s := fun q : ℝ => genericEigenResidual m q ((i : ℤ) - n)) (fun q => ?_)
        (continuous_genericEigenResidual m _)
  rw [← genericEigenTrial_row hm]
  have hdiag : D q i * genericEigenTrialVector m q ((i : ℤ) - n) =
      (m + 2 * ((((i : ℤ) - n : ℤ)) : ℂ)) ^ 2 * genericEigenTrialVector m q ((i : ℤ) - n) := by
    by_cases h : n ≤ i + 3 ∧ i ≤ n + 3
    · rw [hD q i h.1 h.2]; push_cast; ring
    · rw [genericEigenTrial_eq_zero_of_four_le_natAbs m q (by omega)]; ring
  have hlo : recurrenceLower β (fun i => genericEigenTrialVector m q ((i : ℤ) - n)) i =
      genericEigenTrialVector m q ((i : ℤ) - n - 1) := by
    match i with
    | 0 => simp only [recurrenceLower];
           rw [genericEigenTrial_eq_zero_of_four_le_natAbs m q (by omega)]
    | 1 =>
      simp only [recurrenceLower]
      rcases eq_or_lt_of_le hn with h3 | h4
      · subst h3; rw [hβ rfl, one_mul]; congr 1
      · rw [genericEigenTrial_eq_zero_of_four_le_natAbs m q (by omega),
            genericEigenTrial_eq_zero_of_four_le_natAbs m q (by omega), mul_zero]
    | k + 2 => simp only [recurrenceLower]; congr 1; push_cast; ring
  simp only [recurrenceOperator, hdiag, hlo]
  rw [show (((i + 1 : ℕ) : ℤ) - n) = ((i : ℤ) - n) + 1 by push_cast; ring]
  ring

/-- The trial vector components `T_{i-n}(m, q)` are `O(1)` as `q → 0`. -/
private lemma genericEigenTrial_isBigO_one (m : ℂ) (n : ℕ) (i : ℕ) :
    (fun q : ℝ => genericEigenTrialVector m q ((i : ℤ) - n)) =O[𝓝 0] (fun _ => (1 : ℝ)) :=
  isBigO_one_of_continuous (continuous_genericEigenTrial m _)

/-- The shifted trial vector vanishes at `i = n + 4`. -/
private lemma genericEigenTrial_shift_four (m q : ℂ) (n : ℕ) : genericEigenTrialVector m q
    (((n + 4 : ℕ) : ℤ) - n) = 0 :=
  genericEigenTrial_eq_zero_of_four_le_natAbs m q (by omega)

/-- The shifted trial vector vanishes at `i = n + 5`. -/
private lemma genericEigenTrial_shift_five (m q : ℂ) (n : ℕ) : genericEigenTrialVector m q
    (((n + 4 + 1 : ℕ) : ℤ) - n) = 0 :=
  genericEigenTrial_eq_zero_of_four_le_natAbs m q (by omega)

/-- The shifted trial vector equals `1` at `i = n`. -/
private lemma genericEigenTrial_shift_self (m q : ℂ) (n : ℕ) : genericEigenTrialVector m q
    ((n : ℤ) - n) = 1 := by
  simp [genericEigenTrialVector, genericEigenTrialZero]


/-- DLMF 28.6.14 for `a_m`, `m = 2 * n`, from the generic trial vector `genericEigenTrialVector`. -/
private lemma mathieuA_even_sub_generalPoly_isBigO (n : ℕ) (hn : 4 ≤ n) :
    (fun q : ℝ => (mathieuA (2 * n) q : ℂ) - genericEigenvaluePoly ((2 * n : ℕ) : ℂ) q) =O[𝓝 0]
      (fun q : ℝ => q ^ 8) :=
  mathieuA_even_sub_isBigO_of_trial n (N := n + 4) (K := 8)
      (p := fun q => genericEigenvaluePoly ((2 * n : ℕ) : ℂ) q)
    (v := fun q i => genericEigenTrialVector ((2 * n : ℕ) : ℂ) q ((i : ℤ) - n)) (by omega)
    (fun q => genericEigenTrial_shift_four _ _ n) (fun q => genericEigenTrial_shift_five _ _ n)
        (fun q => genericEigenTrial_shift_self _ _ n)
    (fun i _ => genericEigenTrial_isBigO_one _ n i)
    (fun i _ => genericEigenTrial_residual_isBigO (isGenericOrder_natCast (by omega)) (by omega)
        (fun h => absurd h (by omega))
      (fun q i h1 _ => by push_cast; ring) i)

/-- DLMF 28.6.14 for `a_m`, `m = 2 * n + 1`, from the generic trial vector
`genericEigenTrialVector`. -/
private lemma mathieuA_odd_sub_generalPoly_isBigO (n : ℕ) (hn : 4 ≤ n) :
    (fun q : ℝ => (mathieuA (2 * n + 1) q : ℂ) -
        genericEigenvaluePoly ((2 * n + 1 : ℕ) : ℂ) q) =O[𝓝 0]
      (fun q : ℝ => q ^ 8) :=
  mathieuA_odd_sub_isBigO_of_trial n (N := n + 4) (K := 8)
      (p := fun q => genericEigenvaluePoly ((2 * n + 1 : ℕ) : ℂ) q)
    (v := fun q i => genericEigenTrialVector ((2 * n + 1 : ℕ) : ℂ) q ((i : ℤ) - n)) (by omega)
    (fun q => genericEigenTrial_shift_four _ _ n) (fun q => genericEigenTrial_shift_five _ _ n)
        (fun q => genericEigenTrial_shift_self _ _ n)
    (fun i _ => genericEigenTrial_isBigO_one _ n i)
    (fun i _ => genericEigenTrial_residual_isBigO (isGenericOrder_natCast (by omega)) (by omega)
        (fun h => absurd h (by omega))
      (fun q i h1 _ => by
        simp only [show i ≠ 0 by omega, ↓reduceIte]; push_cast; ring) i)

/-- DLMF 28.6.14 for `b_m`, `m = 2 * n + 1`, from the generic trial vector
`genericEigenTrialVector`. -/
private lemma mathieuB_odd_sub_generalPoly_isBigO (n : ℕ) (hn : 4 ≤ n) :
    (fun q : ℝ => (mathieuB (2 * n + 1) q : ℂ) -
        genericEigenvaluePoly ((2 * n + 1 : ℕ) : ℂ) q) =O[𝓝 0]
      (fun q : ℝ => q ^ 8) :=
  mathieuB_odd_sub_isBigO_of_trial n (N := n + 4) (K := 8)
      (p := fun q => genericEigenvaluePoly ((2 * n + 1 : ℕ) : ℂ) q)
    (v := fun q i => genericEigenTrialVector ((2 * n + 1 : ℕ) : ℂ) q ((i : ℤ) - n)) (by omega)
    (fun q => genericEigenTrial_shift_four _ _ n) (fun q => genericEigenTrial_shift_five _ _ n)
        (fun q => genericEigenTrial_shift_self _ _ n)
    (fun i _ => genericEigenTrial_isBigO_one _ n i)
    (fun i _ => genericEigenTrial_residual_isBigO (isGenericOrder_natCast (by omega)) (by omega)
        (fun h => absurd h (by omega))
      (fun q i h1 _ => by
        simp only [show i ≠ 0 by omega, ↓reduceIte]; push_cast; ring) i)

/-- DLMF 28.6.14 for `b_m`, `m = 2 * n + 2`, from the generic trial vector
`genericEigenTrialVector`. -/
private lemma mathieuB_even_sub_generalPoly_isBigO (n : ℕ) (hn : 3 ≤ n) :
    (fun q : ℝ => (mathieuB (2 * n + 2) q : ℂ) -
        genericEigenvaluePoly ((2 * n + 2 : ℕ) : ℂ) q) =O[𝓝 0]
      (fun q : ℝ => q ^ 8) :=
  mathieuB_even_sub_isBigO_of_trial n (N := n + 4) (K := 8)
      (p := fun q => genericEigenvaluePoly ((2 * n + 2 : ℕ) : ℂ) q)
    (v := fun q i => genericEigenTrialVector ((2 * n + 2 : ℕ) : ℂ) q ((i : ℤ) - n)) (by omega)
    (fun q => genericEigenTrial_shift_four _ _ n) (fun q => genericEigenTrial_shift_five _ _ n)
        (fun q => genericEigenTrial_shift_self _ _ n)
    (fun i _ => genericEigenTrial_isBigO_one _ n i)
    (fun i _ => genericEigenTrial_residual_isBigO (isGenericOrder_natCast (by omega))
        (by omega) (fun _ => rfl)
      (fun q i h1 _ => by push_cast; ring) i)

/-- DLMF 28.6.14 for `a_m`, `m ≥ 8`, with remainder `O(q⁸)`. -/
theorem mathieuA_sub_isBigO_of_eight_le {m : ℕ} (hm : 8 ≤ m) :
    (fun q : ℝ => mathieuA m q - ((m : ℝ) ^ 2 + q ^ 2 / (2 * ((m : ℝ) ^ 2 - 1)) +
      (5 * (m : ℝ) ^ 2 + 7) * q ^ 4 / (32 * ((m : ℝ) ^ 2 - 1) ^ 3 * ((m : ℝ) ^ 2 - 4)) +
      (9 * (m : ℝ) ^ 4 + 58 * (m : ℝ) ^ 2 + 29) * q ^ 6 /
        (64 * ((m : ℝ) ^ 2 - 1) ^ 5 * ((m : ℝ) ^ 2 - 4) * ((m : ℝ) ^ 2 - 9)))) =O[𝓝 0]
      (fun q => q ^ 8) := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · exact isBigO_of_ofReal_isBigO (mathieuA_even_sub_generalPoly_isBigO n (by omega)) fun q => by
      simp only [genericEigenvaluePoly]; push_cast; ring
  · exact isBigO_of_ofReal_isBigO (mathieuA_odd_sub_generalPoly_isBigO n (by omega)) fun q => by
      simp only [genericEigenvaluePoly]; push_cast; ring

/-- DLMF 28.6.14 for `b_m`, `m ≥ 8`, with remainder `O(q⁸)`. -/
theorem mathieuB_sub_isBigO_of_eight_le {m : ℕ} (hm : 8 ≤ m) :
    (fun q : ℝ => mathieuB m q - ((m : ℝ) ^ 2 + q ^ 2 / (2 * ((m : ℝ) ^ 2 - 1)) +
      (5 * (m : ℝ) ^ 2 + 7) * q ^ 4 / (32 * ((m : ℝ) ^ 2 - 1) ^ 3 * ((m : ℝ) ^ 2 - 4)) +
      (9 * (m : ℝ) ^ 4 + 58 * (m : ℝ) ^ 2 + 29) * q ^ 6 /
        (64 * ((m : ℝ) ^ 2 - 1) ^ 5 * ((m : ℝ) ^ 2 - 4) * ((m : ℝ) ^ 2 - 9)))) =O[𝓝 0]
      (fun q => q ^ 8) := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [show 2 * (k + 1) = 2 * k + 2 by ring]
    exact isBigO_of_ofReal_isBigO (mathieuB_even_sub_generalPoly_isBigO k (by omega)) fun q => by
      simp only [genericEigenvaluePoly]; push_cast; ring
  · exact isBigO_of_ofReal_isBigO (mathieuB_odd_sub_generalPoly_isBigO n (by omega)) fun q => by
      simp only [genericEigenvaluePoly]; push_cast; ring

/-- DLMF 28.6.14 at `m = 7` (`a_7`), remainder `O(q⁷)`. -/
theorem mathieuA_seven_sub_isBigO :
    (fun q : ℝ => mathieuA 7 q - (49 + 1 / 96 * q ^ 2 + 7 / 4423680 * q ^ 4 +
      17 / 20384317440 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 7) := by
  refine isBigO_of_ofReal_isBigO (mathieuA_odd_sub_isBigO_of_trial 3 (N := 10) (K := 7)
    (p := fun q : ℝ => (49 : ℂ) + ((1 : ℂ) / 96) * (q : ℂ) ^ 2 + ((7 : ℂ) / 4423680) * (q : ℂ) ^ 4
      + ((17 : ℂ) / 20384317440) * (q : ℂ) ^ 6)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 46080) * (q : ℂ) ^ 3
      | 1 => ((1 : ℂ) / 960) * (q : ℂ) ^ 2 + ((1 : ℂ) / 1105920) * (q : ℂ) ^ 4
      | 2 => ((1 : ℂ) / 24) * (q : ℂ) + ((7 : ℂ) / 276480) * (q : ℂ) ^ 3
          + ((61 : ℂ) / 2548039680) * (q : ℂ) ^ 5
      | 3 => (1 : ℂ)
      | 4 => -((1 : ℂ) / 32) * (q : ℂ) - ((7 : ℂ) / 294912) * (q : ℂ) ^ 3
          - ((157 : ℂ) / 6794772480) * (q : ℂ) ^ 5
      | 5 => ((1 : ℂ) / 2304) * (q : ℂ) ^ 2 + ((47 : ℂ) / 106168320) * (q : ℂ) ^ 4
      | 6 => -((1 : ℂ) / 276480) * (q : ℂ) ^ 3
      | 7 => 0
      | 8 => 0
      | 9 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact isBigO_one_of_continuous (by fun_prop)
  · intro i hi
    interval_cases i
    · exact isBigO_pow_of_eq_pow_mul (e := 4) (by decide)
        (s := fun q : ℝ => ((1 : ℂ) / 46080) + ((1 : ℂ) / 1474560) * (q : ℂ)
          - ((7 : ℂ) / 203843174400) * (q : ℂ) ^ 3 - ((17 : ℂ) / 939309347635200) * (q : ℂ) ^ 5)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 6) (by decide)
        (s := fun q : ℝ => ((41 : ℂ) / 3185049600) - ((1 : ℂ) / 434865438720) * (q : ℂ) ^ 2
          - ((17 : ℂ) / 22543424343244800) * (q : ℂ) ^ 4)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 7) (by decide)
        (s := fun q : ℝ => -((793 : ℂ) / 2446118092800)
          - ((133 : ℂ) / 2254342434324480) * (q : ℂ) ^ 2
          - ((1037 : ℂ) / 51940049686836019200) * (q : ℂ) ^ 4)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 7) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 7) (by decide)
        (s := fun q : ℝ => ((397 : ℂ) / 1304596316160)
          + ((847 : ℂ) / 15028949562163200) * (q : ℂ) ^ 2
          + ((2669 : ℂ) / 138506799164896051200) * (q : ℂ) ^ 4)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 6) (by decide)
        (s := fun q : ℝ => -((193 : ℂ) / 6794772480) - ((499 : ℂ) / 469654673817600) * (q : ℂ) ^ 2
          - ((799 : ℂ) / 2164168736951500800) * (q : ℂ) ^ 4)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 5) (by decide)
        (s := fun q : ℝ => ((17 : ℂ) / 35389440) + ((7 : ℂ) / 1223059046400) * (q : ℂ) ^ 2
          + ((17 : ℂ) / 5635856085811200) * (q : ℂ) ^ 4)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 4) (by decide)
        (s := fun q : ℝ => -((1 : ℂ) / 276480))
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 2) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 1) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 0) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
  · intro q; push_cast; ring_nf

/-- DLMF 28.6.14 at `m = 7` (`b_7`), remainder `O(q⁷)`. -/
theorem mathieuB_seven_sub_isBigO :
    (fun q : ℝ => mathieuB 7 q - (49 + 1 / 96 * q ^ 2 + 7 / 4423680 * q ^ 4 +
      17 / 20384317440 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 7) := by
  refine isBigO_of_ofReal_isBigO (mathieuB_odd_sub_isBigO_of_trial 3 (N := 10) (K := 7)
    (p := fun q : ℝ => (49 : ℂ) + ((1 : ℂ) / 96) * (q : ℂ) ^ 2 + ((7 : ℂ) / 4423680) * (q : ℂ) ^ 4
      + ((17 : ℂ) / 20384317440) * (q : ℂ) ^ 6)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 46080) * (q : ℂ) ^ 3
      | 1 => ((1 : ℂ) / 960) * (q : ℂ) ^ 2 + ((1 : ℂ) / 1105920) * (q : ℂ) ^ 4
      | 2 => ((1 : ℂ) / 24) * (q : ℂ) + ((7 : ℂ) / 276480) * (q : ℂ) ^ 3
          + ((61 : ℂ) / 2548039680) * (q : ℂ) ^ 5
      | 3 => (1 : ℂ)
      | 4 => -((1 : ℂ) / 32) * (q : ℂ) - ((7 : ℂ) / 294912) * (q : ℂ) ^ 3
          - ((157 : ℂ) / 6794772480) * (q : ℂ) ^ 5
      | 5 => ((1 : ℂ) / 2304) * (q : ℂ) ^ 2 + ((47 : ℂ) / 106168320) * (q : ℂ) ^ 4
      | 6 => -((1 : ℂ) / 276480) * (q : ℂ) ^ 3
      | 7 => 0
      | 8 => 0
      | 9 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact isBigO_one_of_continuous (by fun_prop)
  · intro i hi
    interval_cases i
    · exact isBigO_pow_of_eq_pow_mul (e := 4) (by decide)
        (s := fun q : ℝ => -((1 : ℂ) / 46080) + ((1 : ℂ) / 1474560) * (q : ℂ)
          - ((7 : ℂ) / 203843174400) * (q : ℂ) ^ 3 - ((17 : ℂ) / 939309347635200) * (q : ℂ) ^ 5)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 6) (by decide)
        (s := fun q : ℝ => ((41 : ℂ) / 3185049600) - ((1 : ℂ) / 434865438720) * (q : ℂ) ^ 2
          - ((17 : ℂ) / 22543424343244800) * (q : ℂ) ^ 4)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 7) (by decide)
        (s := fun q : ℝ => -((793 : ℂ) / 2446118092800)
          - ((133 : ℂ) / 2254342434324480) * (q : ℂ) ^ 2
          - ((1037 : ℂ) / 51940049686836019200) * (q : ℂ) ^ 4)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 7) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 7) (by decide)
        (s := fun q : ℝ => ((397 : ℂ) / 1304596316160)
          + ((847 : ℂ) / 15028949562163200) * (q : ℂ) ^ 2
          + ((2669 : ℂ) / 138506799164896051200) * (q : ℂ) ^ 4)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 6) (by decide)
        (s := fun q : ℝ => -((193 : ℂ) / 6794772480) - ((499 : ℂ) / 469654673817600) * (q : ℂ) ^ 2
          - ((799 : ℂ) / 2164168736951500800) * (q : ℂ) ^ 4)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 5) (by decide)
        (s := fun q : ℝ => ((17 : ℂ) / 35389440) + ((7 : ℂ) / 1223059046400) * (q : ℂ) ^ 2
          + ((17 : ℂ) / 5635856085811200) * (q : ℂ) ^ 4)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 4) (by decide)
        (s := fun q : ℝ => -((1 : ℂ) / 276480))
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 2) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 1) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
    · exact isBigO_pow_of_eq_pow_mul (e := 0) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [recurrenceOperator, recurrenceLower, Nat.reduceAdd];
                     push_cast; ring)
        (by fun_prop)
  · intro q; push_cast; ring_nf

end DLMF.Mathieu
