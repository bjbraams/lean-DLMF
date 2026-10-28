/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Hypergeometric.Identities.CarlsonTools
public import DLMF.Hypergeometric.Identities.Dougall
public import DLMF.Hypergeometric.Identities.Dixon
public import DLMF.Hypergeometric.Identities.Whipple

/-!
# Summation identities and Chapter 3 transformations (AAR §§2.7–2.8, 3.3–3.5)

Kummer's theorem, Dixon's theorem, Whipple's `₇F₆` transformation, and Dougall's bilateral
sum are the main closed-form identities of AAR Chapter 3 that are absent from Mathlib.
The terminating Whipple transformation is proved from the rational Watson transformation
in `DLMF.Bailey`, taking finite q-Pochhammer limits with complex exponential parameters.
-/
