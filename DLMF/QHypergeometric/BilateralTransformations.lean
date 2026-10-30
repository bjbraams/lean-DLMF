/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Transformations

/-!
# Bilateral q-hypergeometric transformations (DLMF §17.10)

The bilateral series are the actual unconditionally summable series, with their
annuli stated. The terminating transformation has both finite tails. Denominator
conditions include the infinite-product prefactors and every transformed series.
The `idem` notation is expanded into its two or three explicit summands.
-/

@[expose] public noncomputable section
open Complex
namespace DLMF.QHypergeometric

/-- DLMF 17.10.1: qPsi2 transformation one. -/
@[dlmf 17.10.E1]
theorem qPsi2_transformation_one (a b c d q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x∈[a,b,d,z], x≠0)
    (hden : QDenominatorRegular [z,d,q/b,c*d/(a*b*z)] q)
    (hB : QBilateralRegular [a,b] [c,d] q ∧ QBilateralRegular [a,a*b*z/d] [a*z,c] q)
    (hz : ‖c*d/(a*b)‖<‖z‖ ∧ ‖z‖<1)
    (hd : ‖c*d/(a*b)‖<‖d/a‖ ∧ ‖d/a‖<1) :
    qPsi [a,b] [c,d] q (z) =
      qProductRatioInf [a*z,d/a,c/b,d*q/(a*b*z)] [z,d,q/b,c*d/(a*b*z)] q * qPsi [a,a*b*z/d] [a*z,c] q (d/a) := by
  sorry

/-- DLMF 17.10.2: qPsi2 transformation two. -/
@[dlmf 17.10.E2]
theorem qPsi2_transformation_two (a b c d q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x∈[a,b,c,d,z], x≠0)
    (hden : QDenominatorRegular [q/a,q/b,c,d] q)
    (hB : QBilateralRegular [a,b] [c,d] q ∧ QBilateralRegular [a*b*z/c,a*b*z/d] [a*z,b*z] q)
    (hz : ‖c*d/(a*b)‖<‖z‖ ∧ ‖z‖<1) :
    qPsi [a,b] [c,d] q (z) =
      qProductRatioInf [a*z,b*z,c*q/(a*b*z),d*q/(a*b*z)] [q/a,q/b,c,d] q * qPsi [a*b*z/c,a*b*z/d] [a*z,b*z] q (c*d/(a*b*z)) := by
  sorry

/-- DLMF 17.10.3: qPsi8 terminating to qPsi4. -/
@[dlmf 17.10.E3]
theorem qPsi8_terminating_to_qPsi4 (n : ℕ) (a c d e f q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x∈[a,c,d,e,f], x≠0)
    (hden : QDenominatorRegular [q/c,q/d,a*q/e,a*q/f] q)
    (hB : QBilateralRegular [q*a^(1/2:ℂ),-q*a^(1/2:ℂ),c,d,e,f,a*q^(-(n:ℤ)),q^(-(n:ℤ))] [a^(1/2:ℂ),-a^(1/2:ℂ),a*q/c,a*q/d,a*q/e,a*q/f,q^(n+1),a*q^(n+1)] q ∧ QBilateralRegular [e,f,a*q^(n+1)/(c*d),q^(-(n:ℤ))] [a*q/c,a*q/d,q^(n+1),e*f/(a*q^n)] q) :
    qPsi [q*a^(1/2:ℂ),-q*a^(1/2:ℂ),c,d,e,f,a*q^(-(n:ℤ)),q^(-(n:ℤ))] [a^(1/2:ℂ),-a^(1/2:ℂ),a*q/c,a*q/d,a*q/e,a*q/f,q^(n+1),a*q^(n+1)] q (a^2*q^(2*n+2)/(c*d*e*f)) =
      qProductRatio n [a*q,q/a,a*q/(c*d),a*q/(e*f)] [q/c,q/d,a*q/e,a*q/f] q * qPsi [e,f,a*q^(n+1)/(c*d),q^(-(n:ℤ))] [a*q/c,a*q/d,q^(n+1),e*f/(a*q^n)] q (q) := by
  sorry

/-- DLMF 17.10.4: qPsi2 gaussian bilateral. -/
@[dlmf 17.10.E4]
theorem qPsi2_gaussian_bilateral (a c d e f q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x∈[a,c,d,e,f], x≠0)
    (hden : QDenominatorRegular [a*q,q/a,a*q/(c*d),a*q/(e*f)] q)
    (hB : QBilateralRegular [e,f] [a*q/c,a*q/d] q ∧ QBilateralRegular [c,d,e,f] [a*q/c,a*q/d,a*q/e,a*q/f] q)
    (ha : a≠1)
    (hcd : ‖a*q/(c*d)‖<1)
    (hef : ‖a*q/(e*f)‖<1) :
    qPsi [e,f] [a*q/c,a*q/d] q (a*q/(e*f)) =
      qProductRatioInf [q/c,q/d,a*q/e,a*q/f] [a*q,q/a,a*q/(c*d),a*q/(e*f)] q * (∑' n : ℤ, (1-a*q^(2*n))/(1-a) * qPochhammerListInt [c,d,e,f] q n / qPochhammerListInt [a*q/c,a*q/d,a*q/e,a*q/f] q n * (q*a^3/(c*d*e*f))^n * q^(n*n)) := by
  sorry

/-- DLMF 17.10.5: qPsi8 connection. -/
@[dlmf 17.10.E5]
theorem qPsi8_connection (a b c d e f g q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x∈[a,b,c,d,e,f,g], x≠0)
    (hden : QDenominatorRegular [f*a,g*a,f/a,g/a,q*a^2,q/a^2,q/(f*a),a*q/f,g/f,f*g,q*f^2,f,-f,f*q/b,f*q/c,f*q/d,f*q/e,f*q/g,q/(g*a),a*q/g,f/g,g*f,q*g^2,g,-g,g*q/b,g*q/c,g*q/d,g*q/e,g*q/f] q)
    (hB : QBilateralRegular [q*a,-q*a,b*a,c*a,d*a,e*a,f*a,g*a] [a,-a,a*q/b,a*q/c,a*q/d,a*q/e,a*q/f,a*q/g] q)
    (hz : ‖q^2/(b*c*d*e*f*g)‖<1) :
    qProductRatioInf [a*q/b,a*q/c,a*q/d,a*q/e,q/(a*b),q/(a*c),q/(a*d),q/(a*e)] [f*a,g*a,f/a,g/a,q*a^2,q/a^2] q * qPsi [q*a,-q*a,b*a,c*a,d*a,e*a,f*a,g*a] [a,-a,a*q/b,a*q/c,a*q/d,a*q/e,a*q/f,a*q/g] q (q^2/(b*c*d*e*f*g)) =
      qProductRatioInf [q,q/(b*f),q/(c*f),q/(d*f),q/(e*f),q*f/b,q*f/c,q*f/d,q*f/e] [f*a,q/(f*a),a*q/f,f/a,g/f,f*g,q*f^2] q * qPhi [f^2,q*f,-q*f,f*b,f*c,f*d,f*e,f*g] [f,-f,f*q/b,f*q/c,f*q/d,f*q/e,f*q/g] q (q^2/(b*c*d*e*f*g)) + qProductRatioInf [q,q/(b*g),q/(c*g),q/(d*g),q/(e*g),q*g/b,q*g/c,q*g/d,q*g/e] [g*a,q/(g*a),a*q/g,g/a,f/g,g*f,q*g^2] q * qPhi [g^2,q*g,-q*g,g*b,g*c,g*d,g*e,g*f] [g,-g,g*q/b,g*q/c,g*q/d,g*q/e,g*q/f] q (q^2/(b*c*d*e*f*g)) := by
  sorry

/-- DLMF 17.10.6: qPsi10 connection. -/
@[dlmf 17.10.E6]
theorem qPsi10_connection (a b c d e f g h k q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x∈[a,b,c,d,e,f,g,h,k], x≠0)
    (hden : QDenominatorRegular [a*g,a*h,a*k,g/a,h/a,k/a,q*a^2,q/a^2,g*h,g*k,h/g,k/g,q/(a*g),a*q/g,q*g^2,g,-g,q*g/b,q*g/c,q*g/d,q*g/e,q*g/f,q*g/h,q*g/k,h*g,h*k,g/h,k/h,q/(a*h),a*q/h,q*h^2,h,-h,q*h/b,q*h/c,q*h/d,q*h/e,q*h/f,q*h/g,q*h/k,k*h,k*g,h/k,g/k,q/(a*k),a*q/k,q*k^2,k,-k,q*k/b,q*k/c,q*k/d,q*k/e,q*k/f,q*k/h,q*k/g] q)
    (hB : QBilateralRegular [q*a,-q*a,b*a,c*a,d*a,e*a,f*a,g*a,h*a,k*a] [a,-a,a*q/b,a*q/c,a*q/d,a*q/e,a*q/f,a*q/g,a*q/h,a*q/k] q)
    (hz : ‖q^3/(b*c*d*e*f*g*h*k)‖<1) :
    qProductRatioInf [a*q/b,a*q/c,a*q/d,a*q/e,a*q/f,q/(a*b),q/(a*c),q/(a*d),q/(a*e),q/(a*f)] [a*g,a*h,a*k,g/a,h/a,k/a,q*a^2,q/a^2] q * qPsi [q*a,-q*a,b*a,c*a,d*a,e*a,f*a,g*a,h*a,k*a] [a,-a,a*q/b,a*q/c,a*q/d,a*q/e,a*q/f,a*q/g,a*q/h,a*q/k] q (q^3/(b*c*d*e*f*g*h*k)) =
      qProductRatioInf [q,q/(b*g),q/(c*g),q/(d*g),q/(e*g),q/(f*g),q*g/b,q*g/c,q*g/d,q*g/e,q*g/f] [g*h,g*k,h/g,k/g,a*g,q/(a*g),g/a,a*q/g,q*g^2] q * qPhi [g^2,q*g,-q*g,g*b,g*c,g*d,g*e,g*f,g*h,g*k] [g,-g,q*g/b,q*g/c,q*g/d,q*g/e,q*g/f,q*g/h,q*g/k] q (q^3/(b*c*d*e*f*g*h*k)) + qProductRatioInf [q,q/(b*h),q/(c*h),q/(d*h),q/(e*h),q/(f*h),q*h/b,q*h/c,q*h/d,q*h/e,q*h/f] [h*g,h*k,g/h,k/h,a*h,q/(a*h),h/a,a*q/h,q*h^2] q * qPhi [h^2,q*h,-q*h,h*b,h*c,h*d,h*e,h*f,h*g,h*k] [h,-h,q*h/b,q*h/c,q*h/d,q*h/e,q*h/f,q*h/g,q*h/k] q (q^3/(b*c*d*e*f*g*h*k)) + qProductRatioInf [q,q/(b*k),q/(c*k),q/(d*k),q/(e*k),q/(f*k),q*k/b,q*k/c,q*k/d,q*k/e,q*k/f] [k*h,k*g,h/k,g/k,a*k,q/(a*k),k/a,a*q/k,q*k^2] q * qPhi [k^2,q*k,-q*k,k*b,k*c,k*d,k*e,k*f,k*h,k*g] [k,-k,q*k/b,q*k/c,q*k/d,q*k/e,q*k/f,q*k/h,q*k/g] q (q^3/(b*c*d*e*f*g*h*k)) := by
  sorry

end DLMF.QHypergeometric
