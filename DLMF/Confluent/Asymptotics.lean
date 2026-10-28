/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Confluent.Asymptotics.LargeArgument
public import DLMF.Confluent.Asymptotics.LargeParameter

/-!
# Asymptotic expansions (DLMF §§13.7, 13.8, 13.19)

Poincaré expansions are stated along the positive real axis. The two-sided expansion of
regularized M on closed upper-half-plane sectors (13.7.2) and the limits 13.2.6, 13.2.23 are in
`DLMF.Confluent.AsymptoticConsequences`, which follows the rotated-sector expansions. Tricomi remainder
statements include an error bound or an asymptotic order, rather than an arbitrary
additive error. Remainder-region machinery 13.7.5–13.7.9 and 13.7.11–13.7.13, uniform
parabolic-cylinder/Bessel approximations 13.8.4–13.8.16, and the uniform
turning-point expansions of §§13.20–13.21 (Airy/Bessel with `envAi`/`envJ`)
are deferred.

Following Temme, *Special Functions*, §§7.1–7.2, the positive-axis expansions are derived
from Watson's lemma (`DLMFMathlib.Analysis.Asymptotics.Watson`):

* `hasAsymptoticExpansion_kummerU`: `U(a,b,x) ~ ∑ (-1)^s (a)_s (a-b+1)_s / s! · x^{-a-s}`
  for all complex `a, b`, from the Laplace integral for `re a > 0` and the contiguous
  relation 13.3.10;
* `kummerU_poincare_finite`: for real `a > 0`, `b ≤ a + 1` the remainder is bounded by the
  first omitted term;
* `hasAsymptoticExpansion_kummerU_sector`: the same expansion for complex `z → ∞` in every
  sector `δ |z| ≤ re z`, from Watson's lemma in a sector;
* `hasAsymptoticExpansion_regularizedConfluent`: `𝐌(a,b,x) ~ eˣ x^{a-b}/Γ(a) ·
  ∑ (1-a)_s (b-a)_s / s! · x^{-s}` for all complex `a, b`, from the Euler integral and the
  regularized contiguous relations;
* `kummerM_large_b_poincare` (13.8.2) for all complex `a`: Watson's lemma for `re a > 0`, then
  uniqueness of asymptotic expansions against 13.8.1 and the identity theorem in `a`.
-/
