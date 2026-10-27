/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic

/-!
# Bilateral basic summations and continuation (DLMF §17.8)

The actual series are asserted only on their convergence annuli. Analytic continuation is
recorded for their germs using TauCeti's proved `ContinuesInside` API, so a divergent
`tsum` value is never confused with the continued value. Cancelled product forms retain
upper-parameter cases where the displayed quotient has a removable0/0.

For17.8.8 the actual annulus additionally requires |c/b²|<1. The weaker printed inequality
|cq²/b²|<1 describes a larger continuation region, not convergence of the bilateral sum.
The native Jacobi triple-product declaration is `DLMF.QSeries.jacobi_triple_product`.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory DLMF.QSeries
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- Ramanujan's product quotient, giving continuation of one-psi-one. -/
def qRamanujanValue (a b q z : ℂ) : ℂ :=
  qPochhammerListInf [q,b/a,a*z,q/(a*z)] q/qPochhammerListInf [b,q/a,z,b/(a*z)] q
/-- The product quotient in the bilateral two-psi-two sum. -/
def qBilateralTwoValue (a b c q : ℂ) : ℂ :=
  qPochhammerInf (a*q/(b*c)) q*qPochhammerListInf [a*q^2/b^2,a*q^2/c^2,q^2,a*q,q/a] (q^2)/
    qPochhammerListInf [a*q/b,a*q/c,q/b,q/c,-a*q/(b*c)] q
/-- The product quotient in the bilateral three-psi-three sum. -/
def qBilateralThreeValue (b c d q : ℂ) : ℂ :=
  qPochhammerListInf [q,q/(b*c),q/(b*d),q/(c*d)] q/qPochhammerListInf [q/b,q/c,q/d,q/(b*c*d)] q
/-- Four-psi-four products with both removable square-root quotient factors cancelled. -/
def qBilateralFourValue (a b c d q : ℂ) : ℂ :=
  let r := Complex.sqrt a
  let t := Complex.sqrt q
  qPochhammerListInf [r*t,-r*t,-r*q,t/r,-t/r,-q/r,a*q/(b*c),a*q/(b*d),a*q/(c*d),q*r/b,q*r/c,q*r/d,q] q/
    qPochhammerListInf [a*q/b,a*q/c,a*q/d,q/b,q/c,q/d,q*a*r/(b*c*d)] q
/-- Bailey's six-psi-six product quotient. -/
def qBilateralSixValue (a b c d e q : ℂ) : ℂ :=
  qPochhammerListInf [a*q,a*q/(b*c),a*q/(b*d),a*q/(b*e),a*q/(c*d),a*q/(c*e),a*q/(d*e),q,q/a] q/
    qPochhammerListInf [a*q/b,a*q/c,a*q/d,a*q/e,q/b,q/c,q/d,q/e,q*a^2/(b*c*d*e)] q
/-- The even-base two-psi-two product, with the b√q denominator factors cancelled. -/
def qBilateralEvenValue (b c q : ℂ) : ℂ :=
  qPochhammerListInf [q^2,q/b^2,c*q/b^2] (q^2)/
    (2*qPochhammerListInf [c*q,c*q^2/b^2,q^2/b^2,c/b^2] (q^2))*
      (qPochhammerInf (-b*Complex.sqrt q) q*qPochhammerInf (c*Complex.sqrt q/b) q+
       qPochhammerInf (b*Complex.sqrt q) q*qPochhammerInf (-c*Complex.sqrt q/b) q)
/-- The integer triangular exponent in the quintuple product. -/
def qQuintupleExponent (n : ℤ) : ℤ := n*(3*n-1)/2
/-- ramanujan one psi one. -/
@[dlmf 17.8.E2]
theorem ramanujan_one_psi_one {a b q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0)
    (hab : qBilateralRegular [a] [b] q) (hz : ‖b/a‖<‖z‖ ∧ ‖z‖<1) :
    qPsi [a] [b] q z=qRamanujanValue a b q z := by
  sorry

/-- quintuple product. -/
@[dlmf 17.8.E3]
theorem quintuple_product {q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : z≠0) :
    HasSum (fun n : ℤ => (-1:ℂ)^n*q^qQuintupleExponent n*z^(3*n)*(1+z*q^n))
      (qPochhammerListInf [q,-z,-q/z] q*qPochhammerListInf [q*z^2,q/z^2] (q^2)) := by
  sorry

/-- bilateral two sum. -/
@[dlmf 17.8.E4]
theorem bilateral_two_sum {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0) (hz : ‖q*a‖<‖b*c‖)
    (hreg : qBilateralRegular [b,c] [a*q/b,a*q/c] q) :
    qPsi [b,c] [a*q/b,a*q/c] q (-a*q/(b*c))=qBilateralTwoValue a b c q := by
  sorry

/-- bilateral three sum. -/
@[dlmf 17.8.E5]
theorem bilateral_three_sum {b c d q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖q‖<‖b*c*d‖)
    (hreg : qBilateralRegular [b,c,d] [q/b,q/c,q/d] q) :
    qPsi [b,c,d] [q/b,q/c,q/d] q (q/(b*c*d))=qBilateralThreeValue b c d q := by
  sorry

/-- bilateral four sum. -/
@[dlmf 17.8.E6]
theorem bilateral_four_sum {a b c d q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0)
    (hz : ‖q*a*Complex.sqrt a‖<‖b*c*d‖)
    (hreg : qBilateralRegular [-q*Complex.sqrt a,b,c,d] [-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q) :
    qPsi [-q*Complex.sqrt a,b,c,d] [-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q
      (q*a*Complex.sqrt a/(b*c*d))=qBilateralFourValue a b c d q := by
  sorry

/-- bilateral six sum. -/
@[dlmf 17.8.E7]
theorem bilateral_six_sum {a b c d e q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0)
    (hz : ‖q*a^2‖<‖b*c*d*e‖)
    (hreg : qBilateralRegular [q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e] q) :
    qPsi [q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e] q
      (q*a^2/(b*c*d*e))=qBilateralSixValue a b c d e q := by
  sorry

/-- The actual series identity uses the full bilateral annulus; the continuation below covers the larger printed region. -/
@[dlmf 17.8.E8]
theorem bilateral_even_sum {b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hb : b≠0) (hc : c≠0)
    (hz : ‖c/b^2‖<1)
    (hreg : qBilateralRegular [b^2,b^2/c] [q,c*q] (q^2)) :
    qPsi [b^2,b^2/c] [q,c*q] (q^2) (c*q^2/b^2)=qBilateralEvenValue b c q := by
  sorry

/-- ramanujan continues. -/
theorem ramanujan_continues {a b q z₀ : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0)
    (hreg : qBilateralRegular [a] [b] q) (hz : ‖b/a‖<‖z₀‖ ∧ ‖z₀‖<1) :
    let U : Set ℂ := {z | z≠0 ∧ qPochhammerListInf [b,q/a,z,b/(a*z)] q≠0}
    AnalyticOnNhd ℂ (qRamanujanValue a b q) U ∧
    (qPsi [a] [b] q=ᶠ[𝓝 z₀] qRamanujanValue a b q) ∧
    TauCeti.ContinuesInside (qPsi [a] [b] q) U z₀ := by
  sorry

/-- bilateral two continues. -/
theorem bilateral_two_continues {a₀ b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a₀≠0)
    (hz : ‖q*a₀‖<‖b*c‖) (hreg : qBilateralRegular [b,c] [a₀*q/b,a₀*q/c] q) :
    let U : Set ℂ := {a | a≠0 ∧ qPochhammerListInf [a*q/b,a*q/c,q/b,q/c,-a*q/(b*c)] q≠0}
    AnalyticOnNhd ℂ (fun a => qBilateralTwoValue a b c q) U ∧
    ((fun a => qPsi [b,c] [a*q/b,a*q/c] q (-a*q/(b*c)))=ᶠ[𝓝 a₀] (fun a => qBilateralTwoValue a b c q)) ∧
    TauCeti.ContinuesInside (fun a => qPsi [b,c] [a*q/b,a*q/c] q (-a*q/(b*c))) U a₀ := by
  sorry

/-- bilateral three continues. -/
theorem bilateral_three_continues {b c d₀ q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hz : ‖q‖<‖b*c*d₀‖) (hreg : qBilateralRegular [b,c,d₀] [q/b,q/c,q/d₀] q) :
    let U : Set ℂ := {d | d≠0 ∧ qPochhammerListInf [q/b,q/c,q/d,q/(b*c*d)] q≠0}
    AnalyticOnNhd ℂ (fun d => qBilateralThreeValue b c d q) U ∧
    ((fun d => qPsi [b,c,d] [q/b,q/c,q/d] q (q/(b*c*d)))=ᶠ[𝓝 d₀] (fun d => qBilateralThreeValue b c d q)) ∧
    TauCeti.ContinuesInside (fun d => qPsi [b,c,d] [q/b,q/c,q/d] q (q/(b*c*d))) U d₀ := by
  sorry

/-- bilateral four continues. -/
theorem bilateral_four_continues {a b c d₀ q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0)
    (hz : ‖q*a*Complex.sqrt a‖<‖b*c*d₀‖)
    (hreg : qBilateralRegular [-q*Complex.sqrt a,b,c,d₀] [-Complex.sqrt a,a*q/b,a*q/c,a*q/d₀] q) :
    let U : Set ℂ := {d | d≠0 ∧ qPochhammerListInf [a*q/b,a*q/c,a*q/d,q/b,q/c,q/d,q*a*Complex.sqrt a/(b*c*d)] q≠0}
    AnalyticOnNhd ℂ (fun d => qBilateralFourValue a b c d q) U ∧
    ((fun d => qPsi [-q*Complex.sqrt a,b,c,d] [-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q (q*a*Complex.sqrt a/(b*c*d)))=ᶠ[𝓝 d₀] (fun d => qBilateralFourValue a b c d q)) ∧
    TauCeti.ContinuesInside (fun d => qPsi [-q*Complex.sqrt a,b,c,d] [-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q (q*a*Complex.sqrt a/(b*c*d))) U d₀ := by
  sorry

/-- bilateral six continues. -/
theorem bilateral_six_continues {a b c d e₀ q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0)
    (hz : ‖q*a^2‖<‖b*c*d*e₀‖)
    (hreg : qBilateralRegular [q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e₀]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e₀] q) :
    let U : Set ℂ := {e | e≠0 ∧ qPochhammerListInf [a*q/b,a*q/c,a*q/d,a*q/e,q/b,q/c,q/d,q/e,q*a^2/(b*c*d*e)] q≠0}
    AnalyticOnNhd ℂ (fun e => qBilateralSixValue a b c d e q) U ∧
    ((fun e => qPsi [q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e] [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e] q (q*a^2/(b*c*d*e)))=ᶠ[𝓝 e₀] (fun e => qBilateralSixValue a b c d e q)) ∧
    TauCeti.ContinuesInside (fun e => qPsi [q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e] [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e] q (q*a^2/(b*c*d*e))) U e₀ := by
  sorry

/-- bilateral even continues. -/
theorem bilateral_even_continues {b c₀ q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hb : b≠0) (hc : c₀≠0)
    (hz : ‖c₀/b^2‖<1) (hreg : qBilateralRegular [b^2,b^2/c₀] [q,c₀*q] (q^2)) :
    let U : Set ℂ := {c | qPochhammerListInf [c*q,c*q^2/b^2,q^2/b^2,c/b^2] (q^2)≠0}
    AnalyticOnNhd ℂ (fun c => qBilateralEvenValue b c q) U ∧
    ((fun c => qPsi [b^2,b^2/c] [q,c*q] (q^2) (c*q^2/b^2))=ᶠ[𝓝 c₀] (fun c => qBilateralEvenValue b c q)) ∧
    TauCeti.ContinuesInside (fun c => qPsi [b^2,b^2/c] [q,c*q] (q^2) (c*q^2/b^2)) U c₀ := by
  sorry

end DLMF.QHypergeometric
