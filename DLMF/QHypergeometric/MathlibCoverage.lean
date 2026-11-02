/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.Data.Nat.Choose.Sum
public import DLMF.QSeries.Heine
public import DLMF.QSeries.QExponential
public import DLMF.QSeries.QCalculus
public import DLMF.QSeries.Saalschutz

/-!
# DLMF Chapter 17 results already in Mathlib or in `DLMF.QSeries`

The `dlmf_upstream` commands below are checked pointers to Mathlib declarations (for example
the complex modular transformation of the Dedekind eta function) and to proved `q`-series
identities of `DLMF.QSeries`, recorded through precise pointers or small notation adapters.
Results whose hypotheses are stronger than DLMF's are marked partial and do not replace the
full-domain statements.
-/

dlmf_upstream 17.2.E6_1 ModularForm.eta_comp_eq_csqrt_I_inv
  "equivalent: complex modular transformation after tau=i*t/(2*pi), Re(t)>0; compatible principal \
      square root"
dlmf_upstream 17.2.i ModularForm.eta
  "exact product definition of Dedekind eta underlying the unnumbered f(q) identity"
dlmf_upstream 17.2.E28 Nat.choose_eq_factorial_div_factorial
  "exact factorial quotient for m<=n"
dlmf_upstream 17.2.E36 add_pow
  "exact: ordinary binomial theorem specialized to -z and1; no duplicate local admission"
