/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic.Definitions
public import DLMF.Elliptic.Basic.Integrals
public import DLMF.Weierstrass.Basic.Functions
import DLMF.Weierstrass.Relations.JacobiIdentities
import DLMF.Weierstrass.Series
import DLMF.JacobiElliptic.Basic.EpsilonProperties
import DLMF.JacobiElliptic.SpecialValues.RealAndHalfPeriods
import DLMF.Elliptic.Complete
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Hyperbolic series for the square of Jacobi's sine

The Weierstrass cosecant-square series with rotated half-periods yields the hyperbolic series
in DLMF 22.11.14. The constant term follows from integrating the shifted Weierstrass identity
over a real period and applying the elliptic and Weierstrass Legendre relations.
-/

public section

set_option maxHeartbeats 0

open Complex Filter DLMF.Elliptic DLMF.EllipticIntegrals DLMF.Weierstrass DLMF.Theta
open scoped Real Topology

namespace DLMF.JacobiElliptic.SquaredSnHyperbolic

/-- For half-periods `K` and `iK′`, the constant `η₁/K + e₃` equals `E/K - 1`. -/
lemma eta_one_div_add_e_three_eq {κ : ℝ} (hk0 : 0 < κ) (hk1 : κ < 1)
    (H : HalfPeriods) (h1 : H.ω₁ = completeEllipticK (κ : ℂ))
    (h3 : H.ω₃ = I * completeEllipticKPrime (κ : ℂ)) :
    H.eta 1 / H.ω₁ + H.e 3 =
      (Real.completeEllipticEOfParameter (κ ^ 2) : ℂ) / completeEllipticK κ - 1 := by
  have hm : κ ^ 2 < 1 := by nlinarith [hk0, hk1]
  have hm0 : 0 < κ ^ 2 := sq_pos_of_pos hk0
  have hk := ofReal_mem_jacobiModulusDomain hk0 hk1
  have hτ : H.tau = jacobiTau κ := by rw [HalfPeriods.tau, h1, h3]; rfl
  have hK : H.quarterK = completeEllipticK κ := by
    rw [HalfPeriods.quarterK, hτ]
    exact (jacobi_inversion_k hk).2.2
  have hmod : H.modulus = (κ : ℂ) := by
    rw [HalfPeriods.modulus, hτ]
    exact (jacobi_inversion_k hk).1
  have hKne := completeEllipticK_ne_zero_of_mem_jacobiModulusDomain hk
  have hP (u : ℂ) (hu : u + H.ω₃ ∉ H.lattice) :
      H.weierstrassP (u + H.ω₃) = H.e 3 + (κ : ℂ) ^ 2 * jacobiSn u κ ^ 2 := by
    have hp := H.weierstrassP_add_ω₃_sub_e_three_eq_sn hu
    rw [hK, hmod, h1, hτ] at hp
    rw [mul_div_cancel_left₀ _ hKne] at hp
    have hs : jacobiSnOfTau u (jacobiTau κ) = jacobiSn u κ :=
      (jacobiPQ_eq_jacobiPQOfTau hk .s .n u).symm
    rw [mul_div_cancel_left₀ u hKne, hs] at hp
    field_simp [hKne] at hp
    linear_combination hp
  have hn (u : ℝ) : (u : ℂ) + H.ω₃ ∉ H.lattice := by
    rw [H.mem_lattice_iff]
    rintro ⟨m, n, he⟩
    rw [h1, h3, completeEllipticK_ofReal hm, completeEllipticKPrime_ofReal hm0] at he
    have hi := congrArg Complex.im he
    simp at hi
    have hpos := Real.completeEllipticKOfParameter_pos (by linarith : 1 - κ ^ 2 < 1)
    have he' : (2 : ℝ) * (n : ℝ) - 1 = 0 := by
      have heq : (1 : ℝ) * Real.completeEllipticKOfParameter (1 - κ ^ 2) =
          (2 * (n : ℝ)) * Real.completeEllipticKOfParameter (1 - κ ^ 2) := by
        linear_combination hi
      have hc := mul_right_cancel₀ (ne_of_gt hpos) heq
      linarith
    have he'' : (2 : ℤ) * n - 1 = 0 := by exact_mod_cast he'
    omega
  let F : ℝ → ℂ := fun u => H.weierstrassZeta ((u : ℂ) + H.ω₃) -
    (Real.jacobiEpsilon u κ : ℂ) + (H.e 3 + 1) * (u : ℂ)
  have hdF (u : ℝ) : HasDerivAt F 0 u := by
    have hz' := ((DLMF.Weierstrass.hasDerivAt_weierstrassZeta H.periodPair (hn u)).comp u
      ((hasDerivAt_id u).ofReal_comp.add_const H.ω₃))
    have he := (Real.hasDerivAt_jacobiEpsilon hm u).ofReal_comp
    have hl := ((hasDerivAt_id u).ofReal_comp).const_mul (H.e 3 + 1)
    have h := (hz'.sub he).add hl
    refine h.congr_deriv ?_
    have hp := hP (u : ℂ) (hn u)
    change H.periodPair.weierstrassP ((u : ℂ) + H.ω₃) = _ at hp
    rw [hp, jacobiSn_ofReal hk0 hk1]
    have hh := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm u
    have hh' : (κ : ℂ) ^ 2 * (Real.jacobiSnOfParameter u (κ ^ 2) : ℂ) ^ 2 +
        (Real.jacobiDnOfParameter u (κ ^ 2) : ℂ) ^ 2 = 1 := by exact_mod_cast hh
    push_cast
    linear_combination -hh'
  let K := Real.completeEllipticKOfParameter (κ ^ 2)
  have hv := is_const_of_deriv_eq_zero (fun u => (hdF u).differentiableAt)
    (fun u => (hdF u).deriv) (2 * K) 0
  dsimp only [F] at hv
  have hperiod := H.weierstrassZeta_add_two_mul_halfPeriod (hn 0) (j := 1) (by simp)
  simp only [ofReal_zero, zero_add, HalfPeriods.halfPeriod_one] at hperiod
  have hε := Real.jacobiEpsilon_add_two_completeEllipticKOfParameter hm 0
  simp only [zero_add, Real.jacobiEpsilon_zero] at hε
  have ha : ((2 * K : ℝ) : ℂ) + H.ω₃ = H.ω₃ + 2 * H.ω₁ := by
    rw [h1, completeEllipticK_ofReal hm]
    dsimp only [K]
    push_cast
    ring_nf
  rw [ha, hperiod, hε, Real.jacobiEpsilon_zero] at hv
  simp only [ofReal_zero, zero_add, mul_zero, sub_zero] at hv
  rw [h1, completeEllipticK_ofReal hm]
  have hKr : (Real.completeEllipticKOfParameter (κ ^ 2) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (ne_of_gt (Real.completeEllipticKOfParameter_pos hm))
  dsimp only [K] at hv
  push_cast at hv
  field_simp [hKr]
  linear_combination hv / 2


end DLMF.JacobiElliptic.SquaredSnHyperbolic

namespace DLMF.JacobiElliptic

/-- DLMF 22.11.14: the hyperbolic series
`k² sn²(z,k) = E'/K' - (π/(2K'))² ∑_{n ∈ ℤ} sech²(π(z - 2nK)/(2K'))`, for real `0 < k < 1`,
`E' = E(k')`, `K' = K(k')`, and `z` not a pole of `sn`.  -/
@[dlmf 22.11.E14 "special case: real 0 < k < 1, z not a pole"]
theorem jacobiSn_sq_hasSum_sech {κ : ℝ} (hk0 : 0 < κ) (hk1 : κ < 1) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiThetaArgument z κ) (jacobiTau κ) ≠ 0) :
    HasSum (fun n : ℤ => (π / (2 * completeEllipticKPrime κ)) ^ 2 *
        (1 / cosh (π / (2 * completeEllipticKPrime κ) * (z - 2 * n * completeEllipticK κ))) ^ 2)
      ((DLMF.Elliptic.Real.completeEllipticEOfParameter (1 - κ ^ 2) : ℂ) /
          completeEllipticKPrime κ -
        (κ : ℂ) ^ 2 * jacobiSn z κ ^ 2) := by
  have hm : κ ^ 2 < 1 := by nlinarith [hk0, hk1]
  have hm0 : 0 < κ ^ 2 := sq_pos_of_pos hk0
  have hk := ofReal_mem_jacobiModulusDomain hk0 hk1
  let K := Real.completeEllipticKOfParameter (κ ^ 2)
  let Kp := Real.completeEllipticKOfParameter (1 - κ ^ 2)
  have hKpos : 0 < K := Real.completeEllipticKOfParameter_pos hm
  have hKppos : 0 < Kp := Real.completeEllipticKOfParameter_pos (by linarith)
  have hKr : completeEllipticK (κ : ℂ) = (K : ℂ) := completeEllipticK_ofReal hm
  have hKpr : completeEllipticKPrime (κ : ℂ) = (Kp : ℂ) := completeEllipticKPrime_ofReal hm0
  have hKne : (K : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hKpos)
  have hKpne : (Kp : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hKppos)
  let H : HalfPeriods :=
    { ω₁ := K
      ω₃ := I * Kp
      ω₁_ne_zero := hKne
      im_div_pos := by
        have hτ := jacobiTau_im_pos hk
        simpa only [jacobiTau, hKr, hKpr] using hτ }
  have h1 : H.ω₁ = completeEllipticK (κ : ℂ) := hKr.symm
  have h3 : H.ω₃ = I * completeEllipticKPrime (κ : ℂ) := by rw [hKpr]
  let J : HalfPeriods :=
    { ω₁ := I * Kp
      ω₃ := -(K : ℂ)
      ω₁_ne_zero := mul_ne_zero I_ne_zero hKpne
      im_div_pos := by
        have he : -(K : ℂ) / (I * Kp) = I * ((K / Kp : ℝ) : ℂ) := by
          push_cast
          field_simp [hKpne]
          exact I_sq.symm
        rw [he]
        simpa using (div_pos hKpos hKppos) }
  have hlat : J.lattice = H.lattice := by
    ext w
    rw [J.mem_lattice_iff, H.mem_lattice_iff]
    constructor
    · rintro ⟨m, n, he⟩
      refine ⟨-n, m, ?_⟩
      dsimp only [J, H] at he ⊢
      push_cast
      linear_combination he
    · rintro ⟨m, n, he⟩
      refine ⟨n, -m, ?_⟩
      dsimp only [J, H] at he ⊢
      push_cast
      linear_combination he
  have hn : z + H.ω₃ ∉ H.lattice := by
    rw [H.mem_lattice_iff]
    rintro ⟨m, n, he⟩
    have heq : jacobiThetaArgument z κ =
        ((m : ℂ) + (((n - 1 : ℤ) : ℂ) + 1 / 2) * jacobiTau κ) * π := by
      rw [jacobiThetaArgument, jacobiTau, hKr, hKpr]
      dsimp only [H] at he
      field_simp [hKne]
      push_cast
      linear_combination he
    have hzero : jacobiThetaFourTau (jacobiThetaArgument z κ) (jacobiTau κ) = 0 :=
      (jacobiThetaTau_eq_zero_iff (jacobiTau_im_pos hk) _).2.2.2.mpr ⟨m, n - 1, heq⟩
    apply hz
    simp only [jacobiLetterTheta, hzero, zero_div]
  have hnJ : z + H.ω₃ ∉ J.lattice := by simpa only [hlat] using hn
  have hsum := J.weierstrassP_csc_series hnJ
  have hP : H.weierstrassP (z + H.ω₃) = H.e 3 + (κ : ℂ) ^ 2 * jacobiSn z κ ^ 2 := by
    have hp := H.weierstrassP_add_ω₃_sub_e_three_eq_sn hn
    have hτ : H.tau = jacobiTau κ := by rw [HalfPeriods.tau, h1, h3]; rfl
    have hquarter : H.quarterK = completeEllipticK κ := by
      rw [HalfPeriods.quarterK, hτ]
      exact (jacobi_inversion_k hk).2.2
    have hmod : H.modulus = (κ : ℂ) := by
      rw [HalfPeriods.modulus, hτ]
      exact (jacobi_inversion_k hk).1
    rw [hquarter, hmod, h1, hτ, hKr] at hp
    simp only [mul_div_cancel_left₀ (κ : ℂ) hKne, mul_div_cancel_left₀ z hKne] at hp
    have hs : jacobiSnOfTau z (jacobiTau κ) = jacobiSn z κ :=
      (jacobiPQ_eq_jacobiPQOfTau hk .s .n z).symm
    rw [hs] at hp
    linear_combination hp
  have hPJ (u : ℂ) : J.weierstrassP u = H.weierstrassP u :=
    DLMF.Weierstrass.weierstrassP_eq_of_lattice_eq J.periodPair H.periodPair hlat u
  have hη : J.eta 1 = H.eta 3 := by
    change DLMF.Weierstrass.weierstrassZeta J.periodPair (I * Kp) =
      DLMF.Weierstrass.weierstrassZeta H.periodPair (I * Kp)
    exact DLMF.Weierstrass.weierstrassZeta_eq_of_lattice_eq _ _ hlat _
  have hconst : -H.e 3 - J.eta 1 / J.ω₁ =
      (Real.completeEllipticEOfParameter (1 - κ ^ 2) : ℂ) / completeEllipticKPrime κ := by
    have hη1 := SquaredSnHyperbolic.eta_one_div_add_e_three_eq hk0 hk1 H h1 h3
    have hleg := H.legendre_relation.2.2
    have hE := DLMF.Elliptic.legendre_relation hm0 hm
    have hEC : (Real.completeEllipticEOfParameter (κ ^ 2) : ℂ) * (Kp : ℂ) +
        (Real.completeEllipticEOfParameter (1 - κ ^ 2) : ℂ) * (K : ℂ) -
          (K : ℂ) * (Kp : ℂ) = π / 2 := by exact_mod_cast hE
    rw [hη, hKpr]
    rw [h1, hKr] at hη1
    dsimp only [H, J] at hleg hη1 ⊢
    field_simp [hKne] at hη1
    have hzero : (K : ℂ) * (-H.e 3 * I * Kp - H.eta 3 -
        I * (Real.completeEllipticEOfParameter (1 - κ ^ 2) : ℂ)) = 0 := by
      linear_combination hleg - I * Kp * hη1 - I * hEC
    have hzero' := (mul_eq_zero.mp hzero).resolve_left hKne
    field_simp [hKpne]
    linear_combination hzero'
  have htrig (n : ℤ) :
      sin (π * (z + H.ω₃ + 2 * n * J.ω₃) / (2 * J.ω₁)) =
        cosh (π / (2 * (Kp : ℂ)) * (z - 2 * n * (K : ℂ))) := by
    have he : π * (z + H.ω₃ + 2 * n * J.ω₃) / (2 * J.ω₁) =
        π / 2 + (-(π / (2 * (Kp : ℂ)) * (z - 2 * n * (K : ℂ)))) * I := by
      dsimp only [H, J]
      field_simp [hKpne]
      linear_combination (z - 2 * n * (K : ℂ)) * I_sq
    rw [he, add_comm (π / 2 : ℂ), Complex.sin_add_pi_div_two, cos_mul_I, cosh_neg]
  convert hsum.neg using 1
  · funext n
    rw [hKr, hKpr, htrig]
    dsimp only [J]
    field_simp [hKpne]
    rw [I_sq]
    ring_nf
  · rw [hPJ, hP]
    linear_combination -hconst

end DLMF.JacobiElliptic
