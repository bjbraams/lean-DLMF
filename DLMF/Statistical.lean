/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Statistical.ContinuedFraction
public import DLMF.Statistical.IncompleteBeta
public import DLMF.Statistical.IncompleteGamma
public import DLMF.Statistical.MarcumQ

/-!
# Statistical distribution functions (Temme Chapter 11; DLMF §§8.2–8.17)

TauCeti provides the real error function, the real regularized incomplete Gamma and Beta
functions and closed-form distribution functions for the standard laws; the project's
`DLMF.Confluent` area provides complex `erf`, `erfc`, `γ(a,z)` and `Γ(a,z)`. This area adds:

* `DLMF.Statistical.IncompleteGamma`: the complex regularized functions `P(a,z)`, `Q(a,z)`, their
  recurrences, the Poisson tail `Q(n+1,z)`, the series DLMF 8.7.1 and the derivative 8.8.13, and
  Tricomi's entire function `γ*(a,z)` (DLMF 8.2.6–8.2.7, 8.4.12).
* `DLMF.Statistical.ContinuedFraction`: convergence of Legendre's continued fraction for `Γ(a,x)`
  (DLMF 8.9.2) for real `a < 1`, `x > 0`, from a general convergence theorem for continued
  fractions with positive elements and a positive backward solution (Pincherle-type invariants
  and Seidel–Stern growth).
* `DLMF.Statistical.IncompleteBeta`: `B_x(a,b)` and `I_x(a,b)` for complex parameters with
  positive real parts: symmetry, the recurrences DLMF 8.17.20–21, the binomial sum 8.17.5 and the
  bridge to TauCeti.
* `DLMF.Statistical.MarcumQ`: the noncentral chi-squared distribution `P_μ(x,y)`, `Q_μ(x,y)` of
  Temme §11.4, with its Bessel recurrences (11.64)–(11.65) and the Bessel integral (11.63).
-/
