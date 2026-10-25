/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Upstream
public import Mathlib.RingTheory.Polynomial.Vieta

/-!
# DLMF §§19.15–19.22 results already in Mathlib or TauCeti

Checked pointers for the symmetric-integral sections. Mathlib and the pinned TauCeti have no
Carlson symmetric integrals and no `R`-function; the only upstream counterpart found is the
Vieta expansion behind the elementary symmetric functions (19.19.4). The `lean-codes`
Carlson library is not upstream: its results are used through the bridge theorems of
`DLMF.EllipticIntegrals.Symmetric` and tagged at the local declarations.
-/

dlmf_upstream 19.19.E4 Multiset.prod_X_add_C_eq_sum_esymm
  "polynomial (Vieta) form ∏ (X + r) = ∑ⱼ esymm j · X^(n-j); DLMF's ∏(1 + t zⱼ) = ∑ tˢ Eₛ after reversal"

dlmf_upstream 19.19.E4 MvPolynomial.prod_C_add_X_eq_sum_esymm
  "multivariate-polynomial form of the same generating function"
