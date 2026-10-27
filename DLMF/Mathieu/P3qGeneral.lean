/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.P3qSpectrum

/-!
# The expansion DLMF 28.6.14 of `a_m(q)`, `b_m(q)` for general `m`

For `m ≥ 7` the eigenvalues have the common expansion
`m² + q²/(2(m²-1)) + (5m²+7)q⁴/(32(m²-1)³(m²-4)) + (9m⁴+58m²+29)q⁶/(64(m²-1)⁵(m²-4)(m²-9))`
up to `O(q^{min(m,8)})`. We prove it with the eigenvalue estimate `p3q_eig_isBigO` of
`DLMF.Mathieu.P3qJacobi`, applied to a trial vector `v_i = T_{i-n}(m, q)` whose components
`p3qGT` are rational in `m` (obtained by Rayleigh–Schrödinger perturbation theory). The rows of
the recurrence applied to `T` are the explicit multiples `q^{8-|j|} p3qGS m q j` of `q`-powers
(`p3q_gen_row`). For `m ≥ 8` all four recurrences 28.4.5–28.4.8 agree with the generic
diagonal `(m + 2j)²` on the support of `T`, so the remainder is `O(q⁸)`
(`p3q_mathieuA_ge8`, `p3q_mathieuB_ge8`). At `m = 7` the boundary term `±q` of 28.4.6–28.4.7
meets the support and the remainder is `O(q⁷)` (`p3q_mathieuA_seven`, `p3q_mathieuB_seven`).
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-- The DLMF 28.6.14 polynomial `m² + q²/(2(m²-1)) + ⋯`, with `m`, `q` complex. -/
def p3qGP (m q : ℂ) : ℂ :=
  m ^ 2 + q ^ 2 / (2 * (m ^ 2 - 1)) +
    (5 * m ^ 2 + 7) * q ^ 4 / (32 * (m ^ 2 - 1) ^ 3 * (m ^ 2 - 4)) +
    (9 * m ^ 4 + 58 * m ^ 2 + 29) * q ^ 6 /
      (64 * (m ^ 2 - 1) ^ 5 * (m ^ 2 - 4) * (m ^ 2 - 9))

/-- The component `j = -3` of `p3qGT` (a polynomial in `q`). -/
def p3qGT_m3 (m q : ℂ) : ℂ :=
  (1/(384*(m - 3)*(m - 2)*(m - 1))) * q ^ 3

/-- The component `j = -2` of `p3qGT` (a polynomial in `q`). -/
def p3qGT_m2 (m q : ℂ) : ℂ :=
  (1/(32*(m - 2)*(m - 1))) * q ^ 2 + ((m^2 - 5*m + 10)/(768*(m - 3)*(m - 2)*(m - 1)^3*(m + 1))) *
    q ^ 4

/-- The component `j = -1` of `p3qGT` (a polynomial in `q`). -/
def p3qGT_m1 (m q : ℂ) : ℂ :=
  (1/(4*(m - 1))) * q ^ 1 + ((m^2 - 4*m + 7)/(128*(m - 2)*(m - 1)^3*(m + 1))) * q ^ 3 + ((m^6 -
    5*m^5 + 8*m^4 - 8*m^3 + 47*m^2 + 13*m + 232)/(3072*(m - 3)*(m - 2)*(m - 1)^5*(m + 1)^3*(m +
    2))) * q ^ 5

/-- The component `j = 0` of `p3qGT` (a polynomial in `q`). -/
def p3qGT_p0 (_m _q : ℂ) : ℂ :=
  (1)

/-- The component `j = 1` of `p3qGT` (a polynomial in `q`). -/
def p3qGT_p1 (m q : ℂ) : ℂ :=
  (-1/(4*(m + 1))) * q ^ 1 + (-(m^2 + 4*m + 7)/(128*(m - 1)*(m + 1)^3*(m + 2))) * q ^ 3 + (-(m^6 +
    5*m^5 + 8*m^4 + 8*m^3 + 47*m^2 - 13*m + 232)/(3072*(m - 2)*(m - 1)^3*(m + 1)^5*(m + 2)*(m +
    3))) * q ^ 5

/-- The component `j = 2` of `p3qGT` (a polynomial in `q`). -/
def p3qGT_p2 (m q : ℂ) : ℂ :=
  (1/(32*(m + 1)*(m + 2))) * q ^ 2 + ((m^2 + 5*m + 10)/(768*(m - 1)*(m + 1)^3*(m + 2)*(m + 3))) *
    q ^ 4

/-- The component `j = 3` of `p3qGT` (a polynomial in `q`). -/
def p3qGT_p3 (m q : ℂ) : ℂ :=
  (-1/(384*(m + 1)*(m + 2)*(m + 3))) * q ^ 3

/-- The generic trial vector `T_j(m, q)`, `|j| ≤ 3`, of the perturbation series of
`a_m(q)`, `b_m(q)` (DLMF 28.6.14): `T_0 = 1`, `T_j = O(q^{|j|})`, and `T_j = 0` for `|j| ≥ 4`. -/
def p3qGT (m q : ℂ) (j : ℤ) : ℂ :=
  if j = -3 then p3qGT_m3 m q
  else if j = -2 then p3qGT_m2 m q
  else if j = -1 then p3qGT_m1 m q
  else if j = 0 then p3qGT_p0 m q
  else if j = 1 then p3qGT_p1 m q
  else if j = 2 then p3qGT_p2 m q
  else if j = 3 then p3qGT_p3 m q
  else 0

/-- The component `j = -4` of `p3qGS` (the residual quotient). -/
def p3qGS_m4 (m _q : ℂ) : ℂ :=
  (1/(384*(m - 3)*(m - 2)*(m - 1)))

/-- The component `j = -3` of `p3qGS` (the residual quotient). -/
def p3qGS_m3 (m q : ℂ) : ℂ :=
  ((m^2 - 6*m + 11)/(768*(m - 3)*(m - 2)*(m - 1)^3*(m + 1))) + (-(5*m^2 + 7)/(12288*(m - 3)*(m -
    2)^2*(m - 1)^4*(m + 1)^3*(m + 2))) * q ^ 2 + (-(9*m^4 + 58*m^2 + 29)/(24576*(m - 3)^2*(m -
    2)^2*(m - 1)^6*(m + 1)^5*(m + 2)*(m + 3))) * q ^ 4

/-- The component `j = -2` of `p3qGS` (the residual quotient). -/
def p3qGS_m2 (m q : ℂ) : ℂ :=
  ((m^7 - 9*m^6 + 28*m^5 - 49*m^4 + 73*m^3 - 55*m^2 + 330*m - 607)/(3072*(m - 3)*(m - 2)^2*(m -
    1)^5*(m + 1)^3*(m + 2))) + (-(5*m^6 - 5*m^5 + 80*m^4 + 118*m^3 + 797*m^2 + 175*m +
    558)/(24576*(m - 3)*(m - 2)^2*(m - 1)^6*(m + 1)^5*(m + 2)*(m + 3))) * q ^ 2 + (-(m^2 - 5*m +
    10)*(9*m^4 + 58*m^2 + 29)/(49152*(m - 3)^2*(m - 2)^2*(m - 1)^8*(m + 1)^6*(m + 2)*(m + 3))) * q
    ^ 4

/-- The component `j = -1` of `p3qGS` (the residual quotient). -/
def p3qGS_m1 (m q : ℂ) : ℂ :=
  (-(2*m^9 - 6*m^8 + m^7 + 9*m^6 + 405*m^5 - 219*m^4 + 2395*m^3 - 5565*m^2 - 1651*m -
    6891)/(12288*(m - 3)*(m - 2)^2*(m - 1)^6*(m + 1)^5*(m + 2)*(m + 3))) + (-(5*m^9 - 10*m^8 +
    80*m^7 - 150*m^6 + 654*m^5 + 1002*m^4 + 1168*m^3 + 13606*m^2 + 1549*m + 9744)/(98304*(m -
    3)*(m - 2)^2*(m - 1)^8*(m + 1)^6*(m + 2)^2*(m + 3))) * q ^ 2 + (-(9*m^4 + 58*m^2 + 29)*(m^6 -
    5*m^5 + 8*m^4 - 8*m^3 + 47*m^2 + 13*m + 232)/(196608*(m - 3)^2*(m - 2)^2*(m - 1)^10*(m +
    1)^8*(m + 2)^2*(m + 3))) * q ^ 4

/-- The component `j = 0` of `p3qGS` (the residual quotient). -/
def p3qGS_p0 (_m _q : ℂ) : ℂ :=
  0

/-- The component `j = 1` of `p3qGS` (the residual quotient). -/
def p3qGS_p1 (m q : ℂ) : ℂ :=
  ((2*m^9 + 6*m^8 + m^7 - 9*m^6 + 405*m^5 + 219*m^4 + 2395*m^3 + 5565*m^2 - 1651*m +
    6891)/(12288*(m - 3)*(m - 2)*(m - 1)^5*(m + 1)^6*(m + 2)^2*(m + 3))) + ((5*m^9 + 10*m^8 +
    80*m^7 + 150*m^6 + 654*m^5 - 1002*m^4 + 1168*m^3 - 13606*m^2 + 1549*m - 9744)/(98304*(m -
    3)*(m - 2)^2*(m - 1)^6*(m + 1)^8*(m + 2)^2*(m + 3))) * q ^ 2 + ((9*m^4 + 58*m^2 + 29)*(m^6 +
    5*m^5 + 8*m^4 + 8*m^3 + 47*m^2 - 13*m + 232)/(196608*(m - 3)*(m - 2)^2*(m - 1)^8*(m + 1)^10*(m
    + 2)^2*(m + 3)^2)) * q ^ 4

/-- The component `j = 2` of `p3qGS` (the residual quotient). -/
def p3qGS_p2 (m q : ℂ) : ℂ :=
  (-(m^7 + 9*m^6 + 28*m^5 + 49*m^4 + 73*m^3 + 55*m^2 + 330*m + 607)/(3072*(m - 2)*(m - 1)^3*(m +
    1)^5*(m + 2)^2*(m + 3))) + (-(5*m^6 + 5*m^5 + 80*m^4 - 118*m^3 + 797*m^2 - 175*m +
    558)/(24576*(m - 3)*(m - 2)*(m - 1)^5*(m + 1)^6*(m + 2)^2*(m + 3))) * q ^ 2 + (-(m^2 + 5*m +
    10)*(9*m^4 + 58*m^2 + 29)/(49152*(m - 3)*(m - 2)*(m - 1)^6*(m + 1)^8*(m + 2)^2*(m + 3)^2)) * q
    ^ 4

/-- The component `j = 3` of `p3qGS` (the residual quotient). -/
def p3qGS_p3 (m q : ℂ) : ℂ :=
  ((m^2 + 6*m + 11)/(768*(m - 1)*(m + 1)^3*(m + 2)*(m + 3))) + ((5*m^2 + 7)/(12288*(m - 2)*(m -
    1)^3*(m + 1)^4*(m + 2)^2*(m + 3))) * q ^ 2 + ((9*m^4 + 58*m^2 + 29)/(24576*(m - 3)*(m - 2)*(m
    - 1)^5*(m + 1)^6*(m + 2)^2*(m + 3)^2)) * q ^ 4

/-- The component `j = 4` of `p3qGS` (the residual quotient). -/
def p3qGS_p4 (m _q : ℂ) : ℂ :=
  (-1/(384*(m + 1)*(m + 2)*(m + 3)))

/-- The residual quotient: row `j` of the generic recurrence applied to `p3qGT` equals
`q^{8-|j|} p3qGS m q j` (`p3q_gen_row`). -/
def p3qGS (m q : ℂ) (j : ℤ) : ℂ :=
  if j = -4 then p3qGS_m4 m q
  else if j = -3 then p3qGS_m3 m q
  else if j = -2 then p3qGS_m2 m q
  else if j = -1 then p3qGS_m1 m q
  else if j = 0 then p3qGS_p0 m q
  else if j = 1 then p3qGS_p1 m q
  else if j = 2 then p3qGS_p2 m q
  else if j = 3 then p3qGS_p3 m q
  else if j = 4 then p3qGS_p4 m q
  else 0

/-- Nonvanishing of the denominators of `p3qGT`, `p3qGS`. -/
structure p3qGood (m : ℂ) : Prop where
  h1 : m - 1 ≠ 0
  h2 : m - 2 ≠ 0
  h3 : m - 3 ≠ 0
  h1' : m + 1 ≠ 0
  h2' : m + 2 ≠ 0
  h3' : m + 3 ≠ 0

theorem p3qGood.sq1 {m : ℂ} (h : p3qGood m) : m ^ 2 - 1 ≠ 0 := by
  rw [show m ^ 2 - 1 = (m - 1) * (m + 1) by ring]; exact mul_ne_zero h.h1 h.h1'

lemma p3qGood.sq4 {m : ℂ} (h : p3qGood m) : m ^ 2 - 4 ≠ 0 := by
  rw [show m ^ 2 - 4 = (m - 2) * (m + 2) by ring]; exact mul_ne_zero h.h2 h.h2'

lemma p3qGood.sq9 {m : ℂ} (h : p3qGood m) : m ^ 2 - 9 ≠ 0 := by
  rw [show m ^ 2 - 9 = (m - 3) * (m + 3) by ring]; exact mul_ne_zero h.h3 h.h3'

lemma p3q_gen_row_m4 {m : ℂ} (hm : p3qGood m) (q : ℂ) :
    ((m + 2 * ((-4 : ℤ) : ℂ)) ^ 2 - p3qGP m q) * p3qGT m q (-4 : ℤ) +
      q * (p3qGT m q ((-4 : ℤ) - 1) + p3qGT m q ((-4 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (-4 : ℤ)) * p3qGS m q (-4 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [p3qGT, p3qGS]
  simp only [p3qGT_m3, p3qGS_m4]
  field_simp

lemma p3q_gen_row_m3 {m : ℂ} (hm : p3qGood m) (q : ℂ) :
    ((m + 2 * ((-3 : ℤ) : ℂ)) ^ 2 - p3qGP m q) * p3qGT m q (-3 : ℤ) +
      q * (p3qGT m q ((-3 : ℤ) - 1) + p3qGT m q ((-3 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (-3 : ℤ)) * p3qGS m q (-3 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [p3qGT, p3qGS]
  simp only [p3qGT_m3, p3qGT_m2, p3qGS_m3, p3qGP]
  field_simp
  ring

lemma p3q_gen_row_m2 {m : ℂ} (hm : p3qGood m) (q : ℂ) :
    ((m + 2 * ((-2 : ℤ) : ℂ)) ^ 2 - p3qGP m q) * p3qGT m q (-2 : ℤ) +
      q * (p3qGT m q ((-2 : ℤ) - 1) + p3qGT m q ((-2 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (-2 : ℤ)) * p3qGS m q (-2 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [p3qGT, p3qGS]
  simp only [p3qGT_m3, p3qGT_m2, p3qGT_m1, p3qGS_m2, p3qGP]
  field_simp
  ring

lemma p3q_gen_row_m1 {m : ℂ} (hm : p3qGood m) (q : ℂ) :
    ((m + 2 * ((-1 : ℤ) : ℂ)) ^ 2 - p3qGP m q) * p3qGT m q (-1 : ℤ) +
      q * (p3qGT m q ((-1 : ℤ) - 1) + p3qGT m q ((-1 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (-1 : ℤ)) * p3qGS m q (-1 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [p3qGT, p3qGS]
  simp only [p3qGT_m2, p3qGT_m1, p3qGT_p0, p3qGS_m1, p3qGP]
  field_simp
  ring

lemma p3q_gen_row_p0 {m : ℂ} (hm : p3qGood m) (q : ℂ) :
    ((m + 2 * ((0 : ℤ) : ℂ)) ^ 2 - p3qGP m q) * p3qGT m q (0 : ℤ) +
      q * (p3qGT m q ((0 : ℤ) - 1) + p3qGT m q ((0 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (0 : ℤ)) * p3qGS m q (0 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [p3qGT, p3qGS]
  simp only [p3qGT_m1, p3qGT_p0, p3qGT_p1, p3qGS_p0, p3qGP]
  field_simp
  ring

lemma p3q_gen_row_p1 {m : ℂ} (hm : p3qGood m) (q : ℂ) :
    ((m + 2 * ((1 : ℤ) : ℂ)) ^ 2 - p3qGP m q) * p3qGT m q (1 : ℤ) +
      q * (p3qGT m q ((1 : ℤ) - 1) + p3qGT m q ((1 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (1 : ℤ)) * p3qGS m q (1 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [p3qGT, p3qGS]
  simp only [p3qGT_p0, p3qGT_p1, p3qGT_p2, p3qGS_p1, p3qGP]
  field_simp
  ring

lemma p3q_gen_row_p2 {m : ℂ} (hm : p3qGood m) (q : ℂ) :
    ((m + 2 * ((2 : ℤ) : ℂ)) ^ 2 - p3qGP m q) * p3qGT m q (2 : ℤ) +
      q * (p3qGT m q ((2 : ℤ) - 1) + p3qGT m q ((2 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (2 : ℤ)) * p3qGS m q (2 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [p3qGT, p3qGS]
  simp only [p3qGT_p1, p3qGT_p2, p3qGT_p3, p3qGS_p2, p3qGP]
  field_simp
  ring

lemma p3q_gen_row_p3 {m : ℂ} (hm : p3qGood m) (q : ℂ) :
    ((m + 2 * ((3 : ℤ) : ℂ)) ^ 2 - p3qGP m q) * p3qGT m q (3 : ℤ) +
      q * (p3qGT m q ((3 : ℤ) - 1) + p3qGT m q ((3 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (3 : ℤ)) * p3qGS m q (3 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [p3qGT, p3qGS]
  simp only [p3qGT_p2, p3qGT_p3, p3qGS_p3, p3qGP]
  field_simp
  ring

lemma p3q_gen_row_p4 {m : ℂ} (hm : p3qGood m) (q : ℂ) :
    ((m + 2 * ((4 : ℤ) : ℂ)) ^ 2 - p3qGP m q) * p3qGT m q (4 : ℤ) +
      q * (p3qGT m q ((4 : ℤ) - 1) + p3qGT m q ((4 : ℤ) + 1)) =
      q ^ (8 - Int.natAbs (4 : ℤ)) * p3qGS m q (4 : ℤ) := by
  have := hm.h1; have := hm.h2; have := hm.h3; have := hm.h1'; have := hm.h2'; have := hm.h3'
  have := hm.sq1; have := hm.sq4; have := hm.sq9
  norm_num [p3qGT, p3qGS]
  simp only [p3qGT_p3, p3qGS_p4]
  field_simp

lemma p3qGT_eq_zero (m q : ℂ) {j : ℤ} (hj : 4 ≤ j.natAbs) : p3qGT m q j = 0 := by
  unfold p3qGT
  split_ifs <;> first | rfl | (exfalso; omega)

lemma p3qGS_eq_zero (m q : ℂ) {j : ℤ} (hj : 5 ≤ j.natAbs) : p3qGS m q j = 0 := by
  unfold p3qGS
  split_ifs <;> first | rfl | (exfalso; omega)

/-- **Generic row identity.** Row `j` of the recurrence
`((m + 2j)² - P) T_j + q (T_{j-1} + T_{j+1})` with the DLMF 28.6.14 polynomial
`P = p3qGP m q` is `q^{8-|j|} p3qGS m q j`. -/
lemma p3q_gen_row {m : ℂ} (hm : p3qGood m) (q : ℂ) (j : ℤ) :
    ((m + 2 * (j : ℂ)) ^ 2 - p3qGP m q) * p3qGT m q j +
      q * (p3qGT m q (j - 1) + p3qGT m q (j + 1)) =
      q ^ (8 - Int.natAbs j) * p3qGS m q j := by
  by_cases hj : j.natAbs ≤ 4
  · have h1 : -4 ≤ j := by omega
    have h2 : j ≤ 4 := by omega
    interval_cases j
    · exact p3q_gen_row_m4 hm q
    · exact p3q_gen_row_m3 hm q
    · exact p3q_gen_row_m2 hm q
    · exact p3q_gen_row_m1 hm q
    · exact p3q_gen_row_p0 hm q
    · exact p3q_gen_row_p1 hm q
    · exact p3q_gen_row_p2 hm q
    · exact p3q_gen_row_p3 hm q
    · exact p3q_gen_row_p4 hm q
  · rw [p3qGT_eq_zero m q (by omega), p3qGT_eq_zero m q (by omega),
      p3qGT_eq_zero m q (by omega), p3qGS_eq_zero m q (by omega)]
    ring

lemma p3qGT_continuous (m : ℂ) (j : ℤ) : Continuous fun q : ℝ => p3qGT m q j := by
  unfold p3qGT
  split_ifs <;>
    (try simp only [p3qGT_m3, p3qGT_m2, p3qGT_m1, p3qGT_p0, p3qGT_p1, p3qGT_p2, p3qGT_p3]) <;>
    fun_prop

lemma p3qGS_continuous (m : ℂ) (j : ℤ) : Continuous fun q : ℝ => p3qGS m q j := by
  unfold p3qGS
  split_ifs <;>
    (try simp only [p3qGS_m4, p3qGS_m3, p3qGS_m2, p3qGS_m1, p3qGS_p0, p3qGS_p1, p3qGS_p2, p3qGS_p3,
      p3qGS_p4]) <;>
    fun_prop

theorem p3qGood_natCast {k : ℕ} (hk : 4 ≤ k) : p3qGood (k : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith [show (4 : ℝ) ≤ k by exact_mod_cast hk]

/-- The residual rows of the generic trial vector `v_i = T_{i-n}` in a recurrence whose diagonal
agrees with `(m + 2(i - n))²` for `|i - n| ≤ 3`. -/
lemma p3q_gen_hr {D : ℝ → ℕ → ℂ} {β : ℂ} {n : ℕ} {m : ℂ} (hm : p3qGood m) (hn : 3 ≤ n)
    (hβ : n = 3 → β = 1)
    (hD : ∀ q i, n ≤ i + 3 → i ≤ n + 3 → D q i = (m + 2 * ((i : ℂ) - n)) ^ 2) (i : ℕ) :
    (fun q : ℝ => p3qL (D q) β q (fun i => p3qGT m q ((i : ℤ) - n)) i -
      p3qGP m q * p3qGT m q ((i : ℤ) - n)) =O[𝓝 0] (fun q : ℝ => q ^ (8 - Nat.dist i n)) := by
  have hdist : Nat.dist i n = ((i : ℤ) - n).natAbs := by
    unfold Nat.dist; omega
  refine p3q_isBigO_of_eq (e := 8 - ((i : ℤ) - n).natAbs) (by omega)
    (s := fun q : ℝ => p3qGS m q ((i : ℤ) - n)) (fun q => ?_) (p3qGS_continuous m _)
  rw [← p3q_gen_row hm]
  have hdiag : D q i * p3qGT m q ((i : ℤ) - n) =
      (m + 2 * ((((i : ℤ) - n : ℤ)) : ℂ)) ^ 2 * p3qGT m q ((i : ℤ) - n) := by
    by_cases h : n ≤ i + 3 ∧ i ≤ n + 3
    · rw [hD q i h.1 h.2]; push_cast; ring
    · rw [p3qGT_eq_zero m q (by omega)]; ring
  have hlo : p3qLo β (fun i => p3qGT m q ((i : ℤ) - n)) i = p3qGT m q ((i : ℤ) - n - 1) := by
    match i with
    | 0 => simp only [p3qLo]; rw [p3qGT_eq_zero m q (by omega)]
    | 1 =>
      simp only [p3qLo]
      rcases eq_or_lt_of_le hn with h3 | h4
      · subst h3; rw [hβ rfl, one_mul]; congr 1
      · rw [p3qGT_eq_zero m q (by omega), p3qGT_eq_zero m q (by omega), mul_zero]
    | k + 2 => simp only [p3qLo]; congr 1; push_cast; ring
  simp only [p3qL, hdiag, hlo]
  rw [show (((i + 1 : ℕ) : ℤ) - n) = ((i : ℤ) - n) + 1 by push_cast; ring]
  ring

lemma p3q_gen_hv (m : ℂ) (n : ℕ) (i : ℕ) :
    (fun q : ℝ => p3qGT m q ((i : ℤ) - n)) =O[𝓝 0] (fun _ => (1 : ℝ)) :=
  p3q_cont_isBigO_one (p3qGT_continuous m _)

lemma p3q_gen_vN (m q : ℂ) (n : ℕ) : p3qGT m q (((n + 4 : ℕ) : ℤ) - n) = 0 :=
  p3qGT_eq_zero m q (by omega)

lemma p3q_gen_vN1 (m q : ℂ) (n : ℕ) : p3qGT m q (((n + 4 + 1 : ℕ) : ℤ) - n) = 0 :=
  p3qGT_eq_zero m q (by omega)

lemma p3q_gen_vn (m q : ℂ) (n : ℕ) : p3qGT m q ((n : ℤ) - n) = 1 := by
  simp [p3qGT, p3qGT_p0]


/-- DLMF 28.6.14 for `a_m`, `m = 2 * n`, from the generic trial vector `p3qGT`. -/
lemma p3q_gen_AE (n : ℕ) (hn : 4 ≤ n) :
    (fun q : ℝ => (mathieuA (2 * n) q : ℂ) - p3qGP ((2 * n : ℕ) : ℂ) q) =O[𝓝 0]
      (fun q : ℝ => q ^ 8) :=
  p3q_eig_AE n (N := n + 4) (K := 8) (p := fun q => p3qGP ((2 * n : ℕ) : ℂ) q)
    (v := fun q i => p3qGT ((2 * n : ℕ) : ℂ) q ((i : ℤ) - n)) (by omega)
    (fun q => p3q_gen_vN _ _ n) (fun q => p3q_gen_vN1 _ _ n) (fun q => p3q_gen_vn _ _ n)
    (fun i _ => p3q_gen_hv _ n i)
    (fun i _ => p3q_gen_hr (p3qGood_natCast (by omega)) (by omega) (fun h => absurd h (by omega))
      (fun q i h1 _ => by push_cast; ring) i)

/-- DLMF 28.6.14 for `a_m`, `m = 2 * n + 1`, from the generic trial vector `p3qGT`. -/
lemma p3q_gen_AO (n : ℕ) (hn : 4 ≤ n) :
    (fun q : ℝ => (mathieuA (2 * n + 1) q : ℂ) - p3qGP ((2 * n + 1 : ℕ) : ℂ) q) =O[𝓝 0]
      (fun q : ℝ => q ^ 8) :=
  p3q_eig_AO n (N := n + 4) (K := 8) (p := fun q => p3qGP ((2 * n + 1 : ℕ) : ℂ) q)
    (v := fun q i => p3qGT ((2 * n + 1 : ℕ) : ℂ) q ((i : ℤ) - n)) (by omega)
    (fun q => p3q_gen_vN _ _ n) (fun q => p3q_gen_vN1 _ _ n) (fun q => p3q_gen_vn _ _ n)
    (fun i _ => p3q_gen_hv _ n i)
    (fun i _ => p3q_gen_hr (p3qGood_natCast (by omega)) (by omega) (fun h => absurd h (by omega))
      (fun q i h1 _ => by
        simp only [show i ≠ 0 by omega, ↓reduceIte]; push_cast; ring) i)

/-- DLMF 28.6.14 for `b_m`, `m = 2 * n + 1`, from the generic trial vector `p3qGT`. -/
lemma p3q_gen_BO (n : ℕ) (hn : 4 ≤ n) :
    (fun q : ℝ => (mathieuB (2 * n + 1) q : ℂ) - p3qGP ((2 * n + 1 : ℕ) : ℂ) q) =O[𝓝 0]
      (fun q : ℝ => q ^ 8) :=
  p3q_eig_BO n (N := n + 4) (K := 8) (p := fun q => p3qGP ((2 * n + 1 : ℕ) : ℂ) q)
    (v := fun q i => p3qGT ((2 * n + 1 : ℕ) : ℂ) q ((i : ℤ) - n)) (by omega)
    (fun q => p3q_gen_vN _ _ n) (fun q => p3q_gen_vN1 _ _ n) (fun q => p3q_gen_vn _ _ n)
    (fun i _ => p3q_gen_hv _ n i)
    (fun i _ => p3q_gen_hr (p3qGood_natCast (by omega)) (by omega) (fun h => absurd h (by omega))
      (fun q i h1 _ => by
        simp only [show i ≠ 0 by omega, ↓reduceIte]; push_cast; ring) i)

/-- DLMF 28.6.14 for `b_m`, `m = 2 * n + 2`, from the generic trial vector `p3qGT`. -/
lemma p3q_gen_BE (n : ℕ) (hn : 3 ≤ n) :
    (fun q : ℝ => (mathieuB (2 * n + 2) q : ℂ) - p3qGP ((2 * n + 2 : ℕ) : ℂ) q) =O[𝓝 0]
      (fun q : ℝ => q ^ 8) :=
  p3q_eig_BE n (N := n + 4) (K := 8) (p := fun q => p3qGP ((2 * n + 2 : ℕ) : ℂ) q)
    (v := fun q i => p3qGT ((2 * n + 2 : ℕ) : ℂ) q ((i : ℤ) - n)) (by omega)
    (fun q => p3q_gen_vN _ _ n) (fun q => p3q_gen_vN1 _ _ n) (fun q => p3q_gen_vn _ _ n)
    (fun i _ => p3q_gen_hv _ n i)
    (fun i _ => p3q_gen_hr (p3qGood_natCast (by omega)) (by omega) (fun _ => rfl)
      (fun q i h1 _ => by push_cast; ring) i)

/-- DLMF 28.6.14 for `a_m`, `m ≥ 8`, with remainder `O(q⁸)`. -/
theorem p3q_mathieuA_ge8 {m : ℕ} (hm : 8 ≤ m) :
    (fun q : ℝ => mathieuA m q - ((m : ℝ) ^ 2 + q ^ 2 / (2 * ((m : ℝ) ^ 2 - 1)) +
      (5 * (m : ℝ) ^ 2 + 7) * q ^ 4 / (32 * ((m : ℝ) ^ 2 - 1) ^ 3 * ((m : ℝ) ^ 2 - 4)) +
      (9 * (m : ℝ) ^ 4 + 58 * (m : ℝ) ^ 2 + 29) * q ^ 6 /
        (64 * ((m : ℝ) ^ 2 - 1) ^ 5 * ((m : ℝ) ^ 2 - 4) * ((m : ℝ) ^ 2 - 9)))) =O[𝓝 0]
      (fun q => q ^ 8) := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · exact p3q_real_of_complex (p3q_gen_AE n (by omega)) fun q => by
      simp only [p3qGP]; push_cast; ring
  · exact p3q_real_of_complex (p3q_gen_AO n (by omega)) fun q => by
      simp only [p3qGP]; push_cast; ring

/-- DLMF 28.6.14 for `b_m`, `m ≥ 8`, with remainder `O(q⁸)`. -/
theorem p3q_mathieuB_ge8 {m : ℕ} (hm : 8 ≤ m) :
    (fun q : ℝ => mathieuB m q - ((m : ℝ) ^ 2 + q ^ 2 / (2 * ((m : ℝ) ^ 2 - 1)) +
      (5 * (m : ℝ) ^ 2 + 7) * q ^ 4 / (32 * ((m : ℝ) ^ 2 - 1) ^ 3 * ((m : ℝ) ^ 2 - 4)) +
      (9 * (m : ℝ) ^ 4 + 58 * (m : ℝ) ^ 2 + 29) * q ^ 6 /
        (64 * ((m : ℝ) ^ 2 - 1) ^ 5 * ((m : ℝ) ^ 2 - 4) * ((m : ℝ) ^ 2 - 9)))) =O[𝓝 0]
      (fun q => q ^ 8) := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [show 2 * (k + 1) = 2 * k + 2 by ring]
    exact p3q_real_of_complex (p3q_gen_BE k (by omega)) fun q => by
      simp only [p3qGP]; push_cast; ring
  · exact p3q_real_of_complex (p3q_gen_BO n (by omega)) fun q => by
      simp only [p3qGP]; push_cast; ring

/-- DLMF 28.6.14 at `m = 7` (`a_7`), remainder `O(q⁷)`. -/
theorem p3q_mathieuA_seven :
    (fun q : ℝ => mathieuA 7 q - (49 + 1 / 96 * q ^ 2 + 7 / 4423680 * q ^ 4 +
      17 / 20384317440 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 7) := by
  refine p3q_real_of_complex (p3q_eig_AO 3 (N := 10) (K := 7)
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
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    interval_cases i
    · exact p3q_isBigO_of_eq (e := 4) (by decide)
        (s := fun q : ℝ => ((1 : ℂ) / 46080) + ((1 : ℂ) / 1474560) * (q : ℂ)
          - ((7 : ℂ) / 203843174400) * (q : ℂ) ^ 3 - ((17 : ℂ) / 939309347635200) * (q : ℂ) ^ 5)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 6) (by decide)
        (s := fun q : ℝ => ((41 : ℂ) / 3185049600) - ((1 : ℂ) / 434865438720) * (q : ℂ) ^ 2
          - ((17 : ℂ) / 22543424343244800) * (q : ℂ) ^ 4)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 7) (by decide)
        (s := fun q : ℝ => -((793 : ℂ) / 2446118092800)
          - ((133 : ℂ) / 2254342434324480) * (q : ℂ) ^ 2
          - ((1037 : ℂ) / 51940049686836019200) * (q : ℂ) ^ 4)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 7) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 7) (by decide)
        (s := fun q : ℝ => ((397 : ℂ) / 1304596316160)
          + ((847 : ℂ) / 15028949562163200) * (q : ℂ) ^ 2
          + ((2669 : ℂ) / 138506799164896051200) * (q : ℂ) ^ 4)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 6) (by decide)
        (s := fun q : ℝ => -((193 : ℂ) / 6794772480) - ((499 : ℂ) / 469654673817600) * (q : ℂ) ^ 2
          - ((799 : ℂ) / 2164168736951500800) * (q : ℂ) ^ 4)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 5) (by decide)
        (s := fun q : ℝ => ((17 : ℂ) / 35389440) + ((7 : ℂ) / 1223059046400) * (q : ℂ) ^ 2
          + ((17 : ℂ) / 5635856085811200) * (q : ℂ) ^ 4)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 4) (by decide)
        (s := fun q : ℝ => -((1 : ℂ) / 276480))
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 2) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 1) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 0) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
  · intro q; push_cast; ring_nf

/-- DLMF 28.6.14 at `m = 7` (`b_7`), remainder `O(q⁷)`. -/
theorem p3q_mathieuB_seven :
    (fun q : ℝ => mathieuB 7 q - (49 + 1 / 96 * q ^ 2 + 7 / 4423680 * q ^ 4 +
      17 / 20384317440 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 7) := by
  refine p3q_real_of_complex (p3q_eig_BO 3 (N := 10) (K := 7)
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
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    interval_cases i
    · exact p3q_isBigO_of_eq (e := 4) (by decide)
        (s := fun q : ℝ => -((1 : ℂ) / 46080) + ((1 : ℂ) / 1474560) * (q : ℂ)
          - ((7 : ℂ) / 203843174400) * (q : ℂ) ^ 3 - ((17 : ℂ) / 939309347635200) * (q : ℂ) ^ 5)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 6) (by decide)
        (s := fun q : ℝ => ((41 : ℂ) / 3185049600) - ((1 : ℂ) / 434865438720) * (q : ℂ) ^ 2
          - ((17 : ℂ) / 22543424343244800) * (q : ℂ) ^ 4)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 7) (by decide)
        (s := fun q : ℝ => -((793 : ℂ) / 2446118092800)
          - ((133 : ℂ) / 2254342434324480) * (q : ℂ) ^ 2
          - ((1037 : ℂ) / 51940049686836019200) * (q : ℂ) ^ 4)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 7) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 7) (by decide)
        (s := fun q : ℝ => ((397 : ℂ) / 1304596316160)
          + ((847 : ℂ) / 15028949562163200) * (q : ℂ) ^ 2
          + ((2669 : ℂ) / 138506799164896051200) * (q : ℂ) ^ 4)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 6) (by decide)
        (s := fun q : ℝ => -((193 : ℂ) / 6794772480) - ((499 : ℂ) / 469654673817600) * (q : ℂ) ^ 2
          - ((799 : ℂ) / 2164168736951500800) * (q : ℂ) ^ 4)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 5) (by decide)
        (s := fun q : ℝ => ((17 : ℂ) / 35389440) + ((7 : ℂ) / 1223059046400) * (q : ℂ) ^ 2
          + ((17 : ℂ) / 5635856085811200) * (q : ℂ) ^ 4)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 4) (by decide)
        (s := fun q : ℝ => -((1 : ℂ) / 276480))
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 2) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 1) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
    · exact p3q_isBigO_of_eq (e := 0) (by decide)
        (s := fun q : ℝ => 0)
        (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
        (by fun_prop)
  · intro q; push_cast; ring_nf

end DLMF.Mathieu
