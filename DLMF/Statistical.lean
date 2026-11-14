/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Statistical.MarcumProbability

public import DLMF.Statistical.MarcumVariableOrder

public import DLMF.Statistical.MarcumFixedOrder

public import DLMF.Statistical.MarcumContours

public import DLMF.Statistical.VonMises
public import DLMF.Statistical.ContinuedFraction
public import DLMF.Statistical.IncompleteBeta
public import DLMF.Statistical.IncompleteGamma
public import DLMF.Statistical.MarcumQ

/-!
# Statistical distribution functions (Temme Chapter 11; DLMF §§8.2–8.17)

This area treats the complex regularized incomplete Gamma functions `P(a,z)`, `Q(a,z)` and
Tricomi's `γ*(a,z)` (`DLMF.Statistical.IncompleteGamma`), the convergence of Legendre's
continued fraction for `Γ(a,x)` (`DLMF.Statistical.ContinuedFraction`), the incomplete Beta
functions `B_x(a,b)`, `I_x(a,b)` (`DLMF.Statistical.IncompleteBeta`), and the noncentral
chi-squared distribution `P_μ(x,y)`, `Q_μ(x,y)` of Temme §11.4 (`DLMF.Statistical.MarcumQ`).
TauCeti provides the real error function, the real regularized incomplete Gamma and Beta
functions and closed-form distribution functions for the standard laws.
-/
