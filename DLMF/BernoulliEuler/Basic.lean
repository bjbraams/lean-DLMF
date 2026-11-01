/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic.Polynomials
public import DLMF.BernoulliEuler.Basic.GeneratingFunctions
public import DLMF.BernoulliEuler.Basic.HigherOrder
public import DLMF.BernoulliEuler.Basic.RelatedNumbers

/-!
# Bernoulli and Euler polynomials: the foundational layer

This umbrella collects the foundational definitions and basic properties of DLMF Chapter 24.

* `DLMF.BernoulliEuler.Basic.Polynomials`: complex evaluation `bernoulliPolyB`, `eulerPolyE` of
  the Bernoulli and Euler polynomials, the Appell property and derivatives.
* `DLMF.BernoulliEuler.Basic.GeneratingFunctions`: the basic results of §24.2 (generating
  function of `Bₙ(x)`, signs, explicit sums, periodic functions, tables).
* `DLMF.BernoulliEuler.Basic.HigherOrder`: the polynomials of order `ℓ` and the Nörlund
  polynomials of §24.16(i).
* `DLMF.BernoulliEuler.Basic.RelatedNumbers`: the Genocchi and tangent numbers of
  §24.15(i)–(ii).

The other results of Chapter 24 are in the theorem modules of `DLMF.BernoulliEuler`.
-/
