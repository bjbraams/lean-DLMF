/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Addition
public import DLMF.JacobiElliptic.Basic
public import DLMF.JacobiElliptic.Cyclic
public import DLMF.JacobiElliptic.Derivatives
public import DLMF.JacobiElliptic.ElementaryIdentities
public import DLMF.JacobiElliptic.FourierSeries
public import DLMF.JacobiElliptic.Integrals
public import DLMF.JacobiElliptic.Inverse
public import DLMF.JacobiElliptic.Landen
public import DLMF.JacobiElliptic.Maclaurin
public import DLMF.JacobiElliptic.MathlibCoverage
public import DLMF.JacobiElliptic.OutsideModuli
public import DLMF.JacobiElliptic.PartialFractions
public import DLMF.JacobiElliptic.PeriodsPolesZeros
public import DLMF.JacobiElliptic.Related
public import DLMF.JacobiElliptic.SpecialValues

/-!
# Jacobian elliptic functions (DLMF Chapter 22)

Mathlib has no Jacobian elliptic functions. This area defines the twelve functions `pq(z, k)`
(Glaisher's notation, `p, q ∈ {s, c, d, n}`) as theta quotients, following DLMF §22.2:

* `Basic`: Glaisher letters, normalized theta functions, the lattice form `jacobiPQTau p q z τ`
  (`k = θ₂²/θ₃²`, `K = (π/2)θ₃²`, `K' = -iτK`) and DLMF's literal modulus form
  `jacobiPQk p q z k` with the principal complex `K(k)`, `K'(k)`, `τ = iK'/K`, nome
  `q = e^{-πK'/K}`; the twelve named functions `jacobiSnk … jacobiCsk` and `jacobiSnTau …
  jacobiCsTau`; theta-constant nonvanishing (triple product), Glaisher's relations, parity,
  meromorphy, and the inversion 22.2.2 with `Im τ > 0` (proved 2026-10-25).
* `PeriodsPolesZeros` (§22.4): the full Table 22.4.3 (proved), periods (Tables 22.4.1–2), and
  the admitted zero/pole structure.
* `SpecialValues` (§22.5): Tables 22.5.1–22.5.4 (values, derivatives/residues, quarter-period
  values, limiting forms), the limits of `K`, `K'`, and the real bridges `jacobiSnk_ofReal` etc.,
  all proved.
* `Addition` (§22.8), `ElementaryIdentities` (§22.6), `Landen` (§22.7), `Cyclic` (§22.9).
* `MathlibCoverage`: upstream pointers.

Results in the modulus form hold on `jacobiModulusDomain` (`Re k > 0`, `k ∉ [1, ∞)`); those
proved from theta identities use the inversion `jacobi_inversion_k` and `jacobiTauk_im_pos`
(both proved).
-/
