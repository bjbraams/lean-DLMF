/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.IncompleteGamma.Asymptotics.LargeArgument
public import DLMF.IncompleteGamma.Asymptotics.PartialSums
public import DLMF.IncompleteGamma.Asymptotics.Central

/-!
# Large argument and large parameter expansions, DLMF §8.11

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.

Proof methods (helper prefix `igAsy_`): 8.11.5 combines 8.11.4 with Binet's form of Stirling's
formula (`DLMF.Gamma.Gamma_eq_exp_binetExponent`, `DLMF.Gamma.norm_binetMu_le`); 8.11.6 and
8.11.18 (hence 8.11.17) use repeated integration by parts in `∫₀¹ t^{a-1} e^{λa(1-t)} dt`, whose
boundary terms produce the polynomials `b_k` of 8.11.9; 8.11.13 at `x = 1` uses the
finite-interval Laplace method of `ToMathlib/Analysis/Integral/Laplace.lean` and Stirling's
formula from Mathlib.
-/
