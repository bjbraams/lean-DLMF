/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic.EquationAndSolutions

/-!
# Characteristic values of Mathieu's equation

The eigenvalues `a_n(q)` and `b_n(q)` of Mathieu's equation for real `q` (DLMF §28.2(v),
Table 28.2.1, DLMF 28.2.21–28.2.22), as ordered roots of the boundary conditions of
Table 28.2.1.

## Main definitions

* `nthLeast`: the `n`-th smallest element (counting from `0`) of a set of reals.
* `mathieuSpecA`, `mathieuSpecB`: the sets of real `a` satisfying the boundary condition of
  Table 28.2.1 for `a_n(q)` and `b_n(q)`.
* `mathieuA n q`, `mathieuB n q`: the eigenvalues `a_n(q)` and `b_n(q)`, the `⌊n/2⌋`-th and
  `⌊(n-1)/2⌋`-th smallest real roots of these boundary conditions.

## Implementation notes

* The eigenvalues are defined for real `q` only (DLMF §28.2(v)); the analytic continuation to
  complex `q` of DLMF §28.7 is stated as theorems. For real `q` the four boundary-value
  problems of Table 28.2.1 are regular Sturm–Liouville problems with simple real eigenvalues, so
  the `k`-th smallest root is DLMF's `a_{2k}`, `a_{2k+1}`, `b_{2k+1}`, `b_{2k+2}`.
* The existence of these roots is `mathieuSpecA_exists`, `mathieuSpecB_exists` in
  `DLMF.Mathieu.SpectralExistence`, proved by Sturm–Liouville arguments
  (`DLMFMathlib/Analysis/ODE/SturmSpectrum.lean`).
* `b_0` is not defined by DLMF; `mathieuB 0 q = 0` is a junk value.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real Classical

namespace DLMF.Mathieu

/-- The `n`-th smallest element (counting from `0`) of a set `S ⊆ ℝ`: the element `x ∈ S` with
exactly `n` elements of `S` below it (junk `0` if there is none). Used for the ordered
spectra of Table 28.2.1. -/
def nthLeast (S : Set ℝ) (n : ℕ) : ℝ :=
  if h : ∃ x ∈ S, (S ∩ Iio x).encard = n then h.choose else 0

/-! ### Eigenvalues `a_n(q)`, `b_n(q)` (§28.2(v)) -/

/-- The spectrum containing `a_n(q)` (Table 28.2.1, DLMF 28.2.21), for real `q`: for even `n` the
real `a` with `w_I'(π/2; a, q) = 0` (`w'(0) = w'(π/2) = 0`), for odd `n` the real `a` with
`w_I(π/2; a, q) = 0` (`w'(0) = w(π/2) = 0`). -/
@[dlmf 28.2.T1]
def mathieuSpecA (n : ℕ) (q : ℝ) : Set ℝ :=
  if Even n then {a | deriv (mathieuWI a q) (π / 2) = 0} else {a | mathieuWI a q (π / 2) = 0}

/-- The spectrum containing `b_n(q)` (Table 28.2.1, DLMF 28.2.22), for real `q`: for odd `n` the
real `a` with `w_II'(π/2; a, q) = 0` (`w(0) = w'(π/2) = 0`), for even `n` the real `a` with
`w_II(π/2; a, q) = 0` (`w(0) = w(π/2) = 0`). -/
@[dlmf 28.2.T1]
def mathieuSpecB (n : ℕ) (q : ℝ) : Set ℝ :=
  if Even n then {a | mathieuWII a q (π / 2) = 0} else {a | deriv (mathieuWII a q) (π / 2) = 0}

/-- The **eigenvalue** `a_n(q)` of Mathieu's equation for real `q`, `n = 0, 1, 2, …` (DLMF
§28.2(v), Table 28.2.1): `a_{2k}(q)` (resp. `a_{2k+1}(q)`) is the `k`-th smallest real root of
`w_I'(π/2; a, q) = 0` (resp. `w_I(π/2; a, q) = 0`). -/
@[dlmf 28.2.T1]
def mathieuA (n : ℕ) (q : ℝ) : ℝ :=
  nthLeast (mathieuSpecA n q) (n / 2)

/-- The **eigenvalue** `b_n(q)` of Mathieu's equation for real `q`, `n = 1, 2, …` (DLMF
§28.2(v), Table 28.2.1): `b_{2k+1}(q)` (resp. `b_{2k+2}(q)`) is the `k`-th smallest real root of
`w_II'(π/2; a, q) = 0` (resp. `w_II(π/2; a, q) = 0`). `b_0` is junk (`0`). -/
@[dlmf 28.2.T1]
def mathieuB (n : ℕ) (q : ℝ) : ℝ :=
  if n = 0 then 0 else nthLeast (mathieuSpecB n q) ((n - 1) / 2)

end DLMF.Mathieu
