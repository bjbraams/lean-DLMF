/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic.LatticesAndSigma
public import TauCeti.Analysis.SpecialFunctions.Elliptic.WeierstrassZeta

/-!
# Meromorphy and upstream bridge for the Weierstrass zeta function

The DLMF and TauCeti lattice series for `ζ` agree, including their assigned regular
parts at lattice points. The bridge permits direct use of TauCeti's additive
quasi-period map in finite zeta sums. The analytic and singular-part APIs are those
of `DLMF.Weierstrass.Basic.LatticesAndSigma`.

See Lang, *Elliptic Functions*, Chapter 18, §1, and Chandrasekharan,
*Elliptic Functions*, Chapter IV, §1.
-/

@[expose] public noncomputable section

namespace DLMF.Weierstrass

/-- The DLMF zeta series agrees with TauCeti's series, with the same totalization. -/
theorem weierstrassZeta_eq_periodPair_weierstrassZeta (L : PeriodPair) :
    weierstrassZeta L = L.weierstrassZeta := by
  funext z
  exact ((hasSumLocallyUniformly_weierstrassZeta L).hasSum (x := z)).unique
    (L.hasSum_weierstrassZeta z)

/-- The lattice zeta series is meromorphic on the whole complex plane. -/
theorem meromorphic_weierstrassZeta (L : PeriodPair) : Meromorphic (weierstrassZeta L) := by
  intro a
  by_cases ha : a ∈ L.lattice
  · have h := (analyticAt_weierstrassZeta_sub L ha).meromorphicAt.add
      ((MeromorphicAt.id a).sub (MeromorphicAt.const a a)).inv
    convert h using 1
    funext z
    simp
  · exact (analyticOnNhd_weierstrassZeta L a ha).meromorphicAt

end DLMF.Weierstrass
