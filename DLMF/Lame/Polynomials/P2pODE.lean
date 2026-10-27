/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Polynomials.P2pBase
public import DLMF.Elliptic.JacobiIdentities
public import DLMF.JacobiElliptic.Derivatives

/-!
# Lamé polynomials solve Lamé's equation (DLMF §§29.12, 29.15)

The Lamé polynomial `lamePolyEk t n m` of type `t` (Chebyshev series 29.15.43–29.15.50 in
`sn(z, k)` with the eigenvector coefficients of the matrix 29.15.2) solves Lamé's equation
29.2.1 with `ν = t.order n` and `h = ½(H_m + ν(ν+1)k²)` at every point that is not a pole of
`sn` (`p2p_lamePolyEk_isLameSolution`).

The proof writes `E = F(z) G(sn z)` with prefactor `F ∈ {1, cn, dn, cn dn}`. Lamé's equation
becomes a polynomial identity `(1-s²)(1-k²s²)G'' - sMG' + (N + h - ν(ν+1)k²s²)G = 0`
(`p2p_opVal`), and on each Chebyshev basis polynomial the operator acts by a three-term
relation (`p2p_kind_T1`, `p2p_kind_Td`, `p2p_kind_Uc`, `p2p_kind_Ucd`). Regrouping, the
coefficient of each basis polynomial is a row of the eigenvalue problem `M v = H v` of 29.15.2
(all rows hold, `p2p_coeff_rows`, the top one because `γ_{n+1} = 0` at `ν = t.order n`).

The file also provides the Green identity for two solutions along a line segment
(`p2p_green_split`), the vanishing of Wronskians at points of reflection symmetry
(`p2p_wronskian_sym`) and the regularity of the real axis and of the line `K + iℝ`
(`p2p_regular_real`, `p2p_regular_vert`), used for the orthogonality 29.14 in
`DLMF.Lame.Polynomials.Orthogonality`.
-/

@[expose] public section

open Polynomial Complex DLMF.JacobiElliptic DLMF.Elliptic Filter Set
open scoped Topology

noncomputable section

namespace DLMF.Lame

/-- The value at `s` of the operator `(1-s²)(1-k²s²)G'' - s M G' + (N + h - λk²s²) G`. -/
def p2p_opVal (k h lam M N : ℂ) (G : ℂ[X]) (s : ℂ) : ℂ :=
  (1 - s ^ 2) * (1 - k ^ 2 * s ^ 2) * (derivative (derivative G)).eval s -
    s * M * (derivative G).eval s + (N + h - lam * k ^ 2 * s ^ 2) * G.eval s

/-- Evaluated Chebyshev identities used for the operator. -/
lemma p2p_chebT_facts (j : ℤ) (s : ℂ) :
    (1 - s ^ 2) * (derivative (derivative (Chebyshev.T ℂ j))).eval s =
        s * (derivative (Chebyshev.T ℂ j)).eval s - (j : ℂ) ^ 2 * (Chebyshev.T ℂ j).eval s ∧
      (1 - s ^ 2) * (derivative (Chebyshev.T ℂ j)).eval s =
        (j : ℂ) * ((Chebyshev.T ℂ (j - 1)).eval s - s * (Chebyshev.T ℂ j).eval s) ∧
      ∀ m : ℤ, (Chebyshev.T ℂ (m + 2)).eval s =
        2 * s * (Chebyshev.T ℂ (m + 1)).eval s - (Chebyshev.T ℂ m).eval s := by
  refine ⟨?_, ?_, fun m => ?_⟩
  · have h := congrArg (eval s)
      (Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := ℂ) j)
    simp only [Function.iterate_succ, Function.comp_apply] at h
    simpa [eval_mul, eval_sub, eval_pow, eval_X] using h
  · have h := congrArg (eval s)
      (Chebyshev.one_sub_X_sq_mul_derivative_T_eq_poly_in_T (R := ℂ) (j - 1))
    simp only [sub_add_cancel] at h
    simpa [eval_mul, eval_sub, eval_pow, eval_X] using h
  · simp [eval_mul, eval_sub, eval_X]

/-- Evaluated Chebyshev identities for `U_j`. -/
lemma p2p_chebU_facts (j : ℤ) (s : ℂ) :
    (1 - s ^ 2) * (derivative (derivative (Chebyshev.U ℂ j))).eval s =
        3 * s * (derivative (Chebyshev.U ℂ j)).eval s -
          ((j : ℂ) + 2) * j * (Chebyshev.U ℂ j).eval s ∧
      ((j : ℂ) + 1) * (Chebyshev.T ℂ (j + 1)).eval s =
        s * (Chebyshev.U ℂ j).eval s - (1 - s ^ 2) * (derivative (Chebyshev.U ℂ j)).eval s ∧
      (Chebyshev.T ℂ (j + 1)).eval s =
        (Chebyshev.U ℂ (j + 1)).eval s - s * (Chebyshev.U ℂ j).eval s ∧
      ∀ m : ℤ, (Chebyshev.U ℂ (m + 2)).eval s =
        2 * s * (Chebyshev.U ℂ (m + 1)).eval s - (Chebyshev.U ℂ m).eval s := by
  refine ⟨?_, ?_, ?_, fun m => ?_⟩
  · have h := congrArg (eval s)
      (Chebyshev.one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U (R := ℂ) j)
    simp only [Function.iterate_succ, Function.comp_apply] at h
    simpa [eval_mul, eval_sub, eval_pow, eval_X] using h
  · have h := congrArg (eval s) (Chebyshev.add_one_mul_T_eq_poly_in_U (R := ℂ) j)
    simpa [eval_mul, eval_sub, eval_pow, eval_X] using h
  · have h := congrArg (eval s) (Chebyshev.T_eq_U_sub_X_mul_U ℂ (j + 1))
    simpa [eval_mul, eval_sub, eval_X] using h
  · simp [eval_mul, eval_sub, eval_X]

/-- Operator identity for `T_j` with prefactor `1`. -/
lemma p2p_kind_T1 (k h lam s : ℂ) (j : ℤ) :
    p2p_opVal k h lam (1 + k ^ 2 - 2 * k ^ 2 * s ^ 2) 0 (Chebyshev.T ℂ j) s =
      k ^ 2 * (j ^ 2 + j - lam) / 4 * (Chebyshev.T ℂ (j + 2)).eval s +
        (2 * h + j ^ 2 * k ^ 2 - 2 * j ^ 2 - k ^ 2 * lam) / 2 * (Chebyshev.T ℂ j).eval s +
        k ^ 2 * (j ^ 2 - j - lam) / 4 * (Chebyshev.T ℂ (j - 2)).eval s := by
  obtain ⟨H0, H1, R⟩ := p2p_chebT_facts j s
  have r0 := R (j - 2)
  have r1 := R (j - 1)
  have r2 := R j
  rw [show j - 2 + 2 = j by ring, show j - 2 + 1 = j - 1 by ring] at r0
  rw [show j - 1 + 2 = j + 1 by ring, show j - 1 + 1 = j by ring] at r1
  unfold p2p_opVal
  linear_combination (1 - k ^ 2 * s ^ 2) * H0 + (-s * k ^ 2) * H1 +
    (-k ^ 2 * (j ^ 2 - j - lam) / 4) * r0 + (-s * k ^ 2 * (j ^ 2 + j - lam) / 2) * r1 +
    (-k ^ 2 * (j ^ 2 + j - lam) / 4) * r2

/-- Operator identity for `T_j` with prefactor `dn`. -/
lemma p2p_kind_Td (k h lam s : ℂ) (j : ℤ) :
    p2p_opVal k h lam (1 + k ^ 2 - 2 * k ^ 2 * s ^ 2 + 2 * k ^ 2 * (1 - s ^ 2))
        (-k ^ 2 * (1 - 2 * s ^ 2)) (Chebyshev.T ℂ j) s =
      k ^ 2 * (j ^ 2 + 3 * j - lam + 2) / 4 * (Chebyshev.T ℂ (j + 2)).eval s +
        (2 * h + j ^ 2 * k ^ 2 - 2 * j ^ 2 - k ^ 2 * lam) / 2 * (Chebyshev.T ℂ j).eval s +
        k ^ 2 * (j ^ 2 - 3 * j - lam + 2) / 4 * (Chebyshev.T ℂ (j - 2)).eval s := by
  obtain ⟨H0, H1, R⟩ := p2p_chebT_facts j s
  have r0 := R (j - 2)
  have r1 := R (j - 1)
  have r2 := R j
  rw [show j - 2 + 2 = j by ring, show j - 2 + 1 = j - 1 by ring] at r0
  rw [show j - 1 + 2 = j + 1 by ring, show j - 1 + 1 = j by ring] at r1
  unfold p2p_opVal
  linear_combination (1 - k ^ 2 * s ^ 2) * H0 + (-3 * s * k ^ 2) * H1 +
    (-k ^ 2 * (j ^ 2 - 3 * j - lam + 2) / 4) * r0 +
    (-s * k ^ 2 * (j ^ 2 + 3 * j - lam + 2) / 2) * r1 +
    (-k ^ 2 * (j ^ 2 + 3 * j - lam + 2) / 4) * r2

/-- Operator identity for `U_j` with prefactor `cn`. -/
lemma p2p_kind_Uc (k h lam s : ℂ) (j : ℤ) :
    p2p_opVal k h lam (1 + k ^ 2 - 2 * k ^ 2 * s ^ 2 + 2 * (1 - k ^ 2 * s ^ 2))
        (2 * k ^ 2 * s ^ 2 - 1) (Chebyshev.U ℂ j) s =
      k ^ 2 * (j ^ 2 + 3 * j - lam + 2) / 4 * (Chebyshev.U ℂ (j + 2)).eval s +
        (2 * h + j ^ 2 * k ^ 2 - 2 * j ^ 2 + 2 * j * k ^ 2 - 4 * j - k ^ 2 * lam + k ^ 2 - 2) / 2 *
          (Chebyshev.U ℂ j).eval s +
        k ^ 2 * (j ^ 2 + j - lam) / 4 * (Chebyshev.U ℂ (j - 2)).eval s := by
  obtain ⟨H0, H1, H2, R⟩ := p2p_chebU_facts j s
  have r0 := R (j - 2)
  have r1 := R (j - 1)
  have r2 := R j
  rw [show j - 2 + 2 = j by ring, show j - 2 + 1 = j - 1 by ring] at r0
  rw [show j - 1 + 2 = j + 1 by ring, show j - 1 + 1 = j by ring] at r1
  unfold p2p_opVal
  linear_combination (1 - k ^ 2 * s ^ 2) * H0 + (-s * k ^ 2) * H1 + (s * k ^ 2 * (j + 1)) * H2 +
    (-k ^ 2 * (j ^ 2 + j - lam) / 4) * r0 + (-s * k ^ 2 * (j ^ 2 + j - lam) / 2) * r1 +
    (-k ^ 2 * (j ^ 2 + 3 * j - lam + 2) / 4) * r2

/-- Operator identity for `U_j` with prefactor `cn dn`. -/
lemma p2p_kind_Ucd (k h lam s : ℂ) (j : ℤ) :
    p2p_opVal k h lam (3 * (1 + k ^ 2 - 2 * k ^ 2 * s ^ 2))
        (4 * k ^ 2 * s ^ 2 - (1 + k ^ 2 - 2 * k ^ 2 * s ^ 2)) (Chebyshev.U ℂ j) s =
      k ^ 2 * (j ^ 2 + 5 * j - lam + 6) / 4 * (Chebyshev.U ℂ (j + 2)).eval s +
        (2 * h + j ^ 2 * k ^ 2 - 2 * j ^ 2 + 2 * j * k ^ 2 - 4 * j - k ^ 2 * lam + k ^ 2 - 2) / 2 *
          (Chebyshev.U ℂ j).eval s +
        k ^ 2 * (j ^ 2 - j - lam) / 4 * (Chebyshev.U ℂ (j - 2)).eval s := by
  obtain ⟨H0, H1, H2, R⟩ := p2p_chebU_facts j s
  have r0 := R (j - 2)
  have r1 := R (j - 1)
  have r2 := R j
  rw [show j - 2 + 2 = j by ring, show j - 2 + 1 = j - 1 by ring] at r0
  rw [show j - 1 + 2 = j + 1 by ring, show j - 1 + 1 = j by ring] at r1
  unfold p2p_opVal
  linear_combination (1 - k ^ 2 * s ^ 2) * H0 + (-3 * s * k ^ 2) * H1 +
    (3 * s * k ^ 2 * (j + 1)) * H2 +
    (-k ^ 2 * (j ^ 2 - j - lam) / 4) * r0 + (-s * k ^ 2 * (j ^ 2 - j - lam) / 2) * r1 +
    (-k ^ 2 * (j ^ 2 + 5 * j - lam + 6) / 4) * r2

/-- First and second derivatives of `F(z) G(sn z)` at a regular point. -/
lemma p2p_E_deriv2 {k : ℂ} (hk : k ∈ jacobiModulusDomain) (F F1 : ℂ → ℂ) (F2 : ℂ) (G : ℂ[X])
    {z : ℂ} (hz : jacobiRegulark .n z k)
    (hF : ∀ y, jacobiRegulark .n y k → HasDerivAt F (F1 y) y) (hF1 : HasDerivAt F1 F2 z) :
    HasDerivAt (deriv fun z => F z * G.eval (jacobiSnk z k))
      (F2 * G.eval (jacobiSnk z k) +
        2 * F1 z * ((derivative G).eval (jacobiSnk z k) * (jacobiCnk z k * jacobiDnk z k)) +
        F z * ((derivative (derivative G)).eval (jacobiSnk z k) *
            (jacobiCnk z k * jacobiDnk z k) ^ 2 +
          (derivative G).eval (jacobiSnk z k) *
            (-(jacobiSnk z k * jacobiDnk z k) * jacobiDnk z k +
              jacobiCnk z k * -(k ^ 2 * jacobiSnk z k * jacobiCnk z k)))) z := by
  have hE1 : ∀ y, jacobiRegulark .n y k → HasDerivAt (fun z => F z * G.eval (jacobiSnk z k))
      (F1 y * G.eval (jacobiSnk y k) +
        F y * ((derivative G).eval (jacobiSnk y k) * (jacobiCnk y k * jacobiDnk y k))) y :=
    fun y hy => (hF y hy).mul ((G.hasDerivAt _).comp y (hasDerivAt_jacobiSnk hk hy))
  have hev : ∀ᶠ y in 𝓝 z, jacobiRegulark .n y k := p22R1_eventually_ne hk hz
  have hd : deriv (fun z => F z * G.eval (jacobiSnk z k)) =ᶠ[𝓝 z] fun y =>
      F1 y * G.eval (jacobiSnk y k) +
        F y * ((derivative G).eval (jacobiSnk y k) * (jacobiCnk y k * jacobiDnk y k)) :=
    hev.mono fun y hy => (hE1 y hy).deriv
  have hs := hasDerivAt_jacobiSnk hk hz
  have hc := hasDerivAt_jacobiCnk hk hz
  have hdn := hasDerivAt_jacobiDnk hk hz
  have hG := (G.hasDerivAt _).comp z hs
  have hG' := ((derivative G).hasDerivAt _).comp z hs
  have h := (hF1.mul hG).add ((hF z hz).mul (hG'.mul (hc.mul hdn)))
  refine (h.congr_of_eventuallyEq hd).congr_deriv ?_
  simp only [Function.comp_apply, Pi.mul_apply]
  ring

/-- Lamé's equation for `F(z) G(sn z)` from the pointwise identity for its second derivative. -/
lemma p2p_solution_of {k : ℂ} (hk : k ∈ jacobiModulusDomain) (F F1 F2 : ℂ → ℂ) (G : ℂ[X])
    (h ν : ℂ) (hF : ∀ y, jacobiRegulark .n y k → HasDerivAt F (F1 y) y)
    (hF1 : ∀ y, jacobiRegulark .n y k → HasDerivAt F1 (F2 y) y)
    (hval : ∀ y, jacobiRegulark .n y k →
      F2 y * G.eval (jacobiSnk y k) +
        2 * F1 y * ((derivative G).eval (jacobiSnk y k) * (jacobiCnk y k * jacobiDnk y k)) +
        F y * ((derivative (derivative G)).eval (jacobiSnk y k) *
            (jacobiCnk y k * jacobiDnk y k) ^ 2 +
          (derivative G).eval (jacobiSnk y k) *
            (-(jacobiSnk y k * jacobiDnk y k) * jacobiDnk y k +
              jacobiCnk y k * -(k ^ 2 * jacobiSnk y k * jacobiCnk y k))) =
        -(h - ν * (ν + 1) * k ^ 2 * jacobiSnk y k ^ 2) * (F y * G.eval (jacobiSnk y k))) :
    IsLameSolutionOn h ν k (fun z => F z * G.eval (jacobiSnk z k))
      {z | jacobiRegulark .n z k} := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · exact ((hF z hz).mul ((G.hasDerivAt _).comp z (hasDerivAt_jacobiSnk hk hz))).differentiableAt
  · exact (p2p_E_deriv2 hk F F1 (F2 z) G hz hF (hF1 z hz)).congr_deriv (hval z hz)

/-- The case of prefactor `1`. -/
lemma p2p_solution_one {k : ℂ} (hk : k ∈ jacobiModulusDomain) (G : ℂ[X]) (h ν : ℂ)
    (hop : ∀ s, p2p_opVal k h (ν * (ν + 1)) (1 + k ^ 2 - 2 * k ^ 2 * s ^ 2) 0 G s = 0) :
    IsLameSolutionOn h ν k (fun z => 1 * G.eval (jacobiSnk z k)) {z | jacobiRegulark .n z k} := by
  refine p2p_solution_of hk (fun _ => 1) (fun _ => 0) (fun _ => 0) G h ν
    (fun y _ => hasDerivAt_const y 1) (fun y _ => hasDerivAt_const y 0) fun y hy => ?_
  obtain ⟨e1, e2⟩ := jacobi_sq_sum hk hy
  have := hop (jacobiSnk y k)
  unfold p2p_opVal at this
  set s := jacobiSnk y k; set c := jacobiCnk y k; set d := jacobiDnk y k
  set G0 := G.eval s; set G1 := (derivative G).eval s
  set G2 := (derivative (derivative G)).eval s
  linear_combination this + (-G1 * k ^ 2 * s + G2 * d ^ 2) * e1 + (-G1 * s - G2 * s ^ 2 + G2) * e2

/-- The case of prefactor `cn`. -/
lemma p2p_solution_c {k : ℂ} (hk : k ∈ jacobiModulusDomain) (G : ℂ[X]) (h ν : ℂ)
    (hop : ∀ s, p2p_opVal k h (ν * (ν + 1))
      (1 + k ^ 2 - 2 * k ^ 2 * s ^ 2 + 2 * (1 - k ^ 2 * s ^ 2))
      (2 * k ^ 2 * s ^ 2 - 1) G s = 0) :
    IsLameSolutionOn h ν k (fun z => jacobiCnk z k * G.eval (jacobiSnk z k))
      {z | jacobiRegulark .n z k} := by
  refine p2p_solution_of hk (fun y => jacobiCnk y k) (fun y => -(jacobiSnk y k * jacobiDnk y k))
    (fun y => -(jacobiCnk y k * jacobiDnk y k * jacobiDnk y k +
      jacobiSnk y k * -(k ^ 2 * jacobiSnk y k * jacobiCnk y k))) G h ν
    (fun y hy => hasDerivAt_jacobiCnk hk hy)
    (fun y hy => ((hasDerivAt_jacobiSnk hk hy).mul (hasDerivAt_jacobiDnk hk hy)).neg)
    fun y hy => ?_
  obtain ⟨e1, e2⟩ := jacobi_sq_sum hk hy
  have := hop (jacobiSnk y k)
  unfold p2p_opVal at this
  set s := jacobiSnk y k; set c := jacobiCnk y k; set d := jacobiDnk y k
  set G0 := G.eval s; set G1 := (derivative G).eval s
  set G2 := (derivative (derivative G)).eval s
  linear_combination c * this + (-c * (G1 * k ^ 2 * s - G2 * d ^ 2)) * e1 +
    (-c * (G0 + 3 * G1 * s + G2 * s ^ 2 - G2)) * e2

/-- The case of prefactor `dn`. -/
lemma p2p_solution_d {k : ℂ} (hk : k ∈ jacobiModulusDomain) (G : ℂ[X]) (h ν : ℂ)
    (hop : ∀ s, p2p_opVal k h (ν * (ν + 1))
      (1 + k ^ 2 - 2 * k ^ 2 * s ^ 2 + 2 * k ^ 2 * (1 - s ^ 2)) (-k ^ 2 * (1 - 2 * s ^ 2)) G s =
        0) :
    IsLameSolutionOn h ν k (fun z => jacobiDnk z k * G.eval (jacobiSnk z k))
      {z | jacobiRegulark .n z k} := by
  refine p2p_solution_of hk (fun y => jacobiDnk y k)
    (fun y => -(k ^ 2 * jacobiSnk y k * jacobiCnk y k))
    (fun y => -(k ^ 2 * (jacobiCnk y k * jacobiDnk y k) * jacobiCnk y k +
      k ^ 2 * jacobiSnk y k * -(jacobiSnk y k * jacobiDnk y k))) G h ν
    (fun y hy => hasDerivAt_jacobiDnk hk hy)
    (fun y hy => (((hasDerivAt_jacobiSnk hk hy).const_mul (k ^ 2)).mul
      (hasDerivAt_jacobiCnk hk hy)).neg.congr_deriv (by ring))
    fun y hy => ?_
  obtain ⟨e1, e2⟩ := jacobi_sq_sum hk hy
  have := hop (jacobiSnk y k)
  unfold p2p_opVal at this
  set s := jacobiSnk y k; set c := jacobiCnk y k; set d := jacobiDnk y k
  set G0 := G.eval s; set G1 := (derivative G).eval s
  set G2 := (derivative (derivative G)).eval s
  linear_combination d * this + (-d * (G0 * k ^ 2 + 3 * G1 * k ^ 2 * s - G2 * d ^ 2)) * e1 +
    (-d * (G1 * s + G2 * s ^ 2 - G2)) * e2

/-- The case of prefactor `cn dn`. -/
lemma p2p_solution_cd {k : ℂ} (hk : k ∈ jacobiModulusDomain) (G : ℂ[X]) (h ν : ℂ)
    (hop : ∀ s, p2p_opVal k h (ν * (ν + 1)) (3 * (1 + k ^ 2 - 2 * k ^ 2 * s ^ 2))
      (4 * k ^ 2 * s ^ 2 - (1 + k ^ 2 - 2 * k ^ 2 * s ^ 2)) G s = 0) :
    IsLameSolutionOn h ν k (fun z => jacobiCnk z k * jacobiDnk z k * G.eval (jacobiSnk z k))
      {z | jacobiRegulark .n z k} := by
  refine p2p_solution_of hk (fun y => jacobiCnk y k * jacobiDnk y k)
    (fun y => -(jacobiSnk y k * jacobiDnk y k) * jacobiDnk y k +
      jacobiCnk y k * -(k ^ 2 * jacobiSnk y k * jacobiCnk y k))
    (fun y => -(jacobiCnk y k * jacobiDnk y k * jacobiDnk y k +
        jacobiSnk y k * -(k ^ 2 * jacobiSnk y k * jacobiCnk y k)) * jacobiDnk y k +
      -(jacobiSnk y k * jacobiDnk y k) * -(k ^ 2 * jacobiSnk y k * jacobiCnk y k) +
      (-(jacobiSnk y k * jacobiDnk y k) * -(k ^ 2 * jacobiSnk y k * jacobiCnk y k) +
        jacobiCnk y k * -(k ^ 2 * (jacobiCnk y k * jacobiDnk y k * jacobiCnk y k +
          jacobiSnk y k * -(jacobiSnk y k * jacobiDnk y k))))) G h ν
    (fun y hy => (hasDerivAt_jacobiCnk hk hy).mul (hasDerivAt_jacobiDnk hk hy))
    (fun y hy => by
      have hs := hasDerivAt_jacobiSnk hk hy
      have hc := hasDerivAt_jacobiCnk hk hy
      have hd := hasDerivAt_jacobiDnk hk hy
      exact ((hs.mul hd).neg.mul hd).add (hc.mul (((hs.const_mul (k ^ 2)).mul hc).neg))
        |>.congr_deriv
        (by simp only [Pi.neg_apply, Pi.mul_apply]; ring))
    fun y hy => ?_
  obtain ⟨e1, e2⟩ := jacobi_sq_sum hk hy
  have := hop (jacobiSnk y k)
  unfold p2p_opVal at this
  set s := jacobiSnk y k; set c := jacobiCnk y k; set d := jacobiDnk y k
  set G0 := G.eval s; set G1 := (derivative G).eval s
  set G2 := (derivative (derivative G)).eval s
  linear_combination c * d * this +
    (-c * d * (G0 * k ^ 2 + 3 * G1 * k ^ 2 * s - G2 * d ^ 2)) * e1 +
    (-c * d * (G0 + 3 * G1 * s + G2 * s ^ 2 - G2)) * e2

/-- The operator value is linear in the polynomial. -/
lemma p2p_opVal_sum (k h lam M N s : ℂ) (S : Finset ℕ) (c : ℕ → ℂ) (P : ℕ → ℂ[X]) :
    p2p_opVal k h lam M N (∑ p ∈ S, C (c p) * P p) s =
      ∑ p ∈ S, c p * p2p_opVal k h lam M N (P p) s := by
  unfold p2p_opVal
  simp only [derivative_sum, derivative_C_mul, eval_finsetSum, eval_mul, eval_C,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- Regrouping a three-term action by basis index. -/
lemma p2p_regroup (N : ℕ) (c A B E Y : ℕ → ℂ) (Yn : ℂ) (hN : c N = 0) (hN1 : c (N + 1) = 0) :
    ∑ p ∈ Finset.range (N + 1),
        c p * (A p * Y (p + 1) + B p * Y p + E p * (if p = 0 then Yn else Y (p - 1))) =
      c 0 * E 0 * Yn + ∑ q ∈ Finset.range (N + 1),
        ((if q = 0 then 0 else c (q - 1) * A (q - 1)) + c q * B q + c (q + 1) * E (q + 1)) *
          Y q := by
  have e1 : ∑ p ∈ Finset.range (N + 1), c p * A p * Y (p + 1) =
      ∑ q ∈ Finset.range (N + 1), (if q = 0 then 0 else c (q - 1) * A (q - 1)) * Y q := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ' _ N, hN]
    simp
  have e3 : ∑ p ∈ Finset.range (N + 1), c p * E p * (if p = 0 then Yn else Y (p - 1)) =
      c 0 * E 0 * Yn + ∑ q ∈ Finset.range (N + 1), c (q + 1) * E (q + 1) * Y q := by
    rw [Finset.sum_range_succ' _ N, Finset.sum_range_succ _ N, hN1]
    simp [add_comm]
  have : ∀ p, c p * (A p * Y (p + 1) + B p * Y p + E p * (if p = 0 then Yn else Y (p - 1))) =
      c p * A p * Y (p + 1) + c p * B p * Y p +
        c p * E p * (if p = 0 then Yn else Y (p - 1)) := fun p => by ring
  simp only [this, Finset.sum_add_distrib, e1, e3, add_mul]
  ring

/-- The operator applied to a Chebyshev series `∑ c_p P_{2p+δ}`. -/
lemma p2p_master (k h lam M N s : ℂ) (P : ℤ → ℂ[X]) (δ : ℕ) (a b e : ℂ → ℂ)
    (hkind : ∀ j : ℤ, p2p_opVal k h lam M N (P j) s =
      a j * (P (j + 2)).eval s + b j * (P j).eval s + e j * (P (j - 2)).eval s)
    (n : ℕ) (c : ℕ → ℂ) (hc : ∀ p, n < p → c p = 0) :
    p2p_opVal k h lam M N (∑ p ∈ Finset.range (n + 1), C (c p) * P ((2 * p + δ : ℕ) : ℤ)) s =
      c 0 * e δ * (P ((δ : ℤ) - 2)).eval s + ∑ q ∈ Finset.range (n + 2),
        ((if q = 0 then 0 else c (q - 1) * a ((2 * (q - 1) + δ : ℕ) : ℂ)) +
          c q * b ((2 * q + δ : ℕ) : ℂ) + c (q + 1) * e ((2 * (q + 1) + δ : ℕ) : ℂ)) *
          (P ((2 * q + δ : ℕ) : ℤ)).eval s := by
  rw [p2p_opVal_sum]
  have hext : ∑ p ∈ Finset.range (n + 1), c p * p2p_opVal k h lam M N
      (P ((2 * p + δ : ℕ) : ℤ)) s = ∑ p ∈ Finset.range (n + 1 + 1), c p *
        (a ((2 * p + δ : ℕ) : ℂ) * (P ((2 * (p + 1) + δ : ℕ) : ℤ)).eval s +
          b ((2 * p + δ : ℕ) : ℂ) * (P ((2 * p + δ : ℕ) : ℤ)).eval s +
          e ((2 * p + δ : ℕ) : ℂ) * (if p = 0 then (P ((δ : ℤ) - 2)).eval s
            else (P ((2 * (p - 1) + δ : ℕ) : ℤ)).eval s)) := by
    rw [Finset.sum_range_succ _ (n + 1), hc (n + 1) (by omega), zero_mul, add_zero]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hkind]
    congr 1
    have h1 : (((2 * p + δ : ℕ) : ℤ) : ℂ) = ((2 * p + δ : ℕ) : ℂ) := by push_cast; ring
    have h2 : ((2 * p + δ : ℕ) : ℤ) + 2 = ((2 * (p + 1) + δ : ℕ) : ℤ) := by push_cast; ring
    rw [h1, h2]
    congr 2
    rcases p with _ | p
    · simp
    · simp only [show p + 1 ≠ 0 by omega, ite_false, show p + 1 - 1 = p by omega]
      congr 3; push_cast; ring
  rw [hext, p2p_regroup (n + 1) c _ _ _ (fun q => (P ((2 * q + δ : ℕ) : ℤ)).eval s) _
    (hc (n + 1) (by omega)) (hc (n + 2) (by omega))]
  simp

/-- Vanishing of a regrouped sum from its first two coefficients and the rest. -/
lemma p2p_vanish (n : ℕ) (r Y : ℕ → ℂ) (X0 : ℂ) (h01 : X0 + r 0 * Y 0 + r 1 * Y 1 = 0)
    (hq : ∀ q, r (q + 2) = 0) : X0 + ∑ q ∈ Finset.range (n + 2), r q * Y q = 0 := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [hq, zero_mul, Finset.sum_const_zero, zero_add]
  linear_combination h01

section p2pRows

open Matrix

/-- The last row `γ_n v_{n-1} + β_n v_n = H v_n` of `M v = H v` for the forward-recursion vector
`v`, when `H` is an eigenvalue of the matrix 29.15.2. -/
lemma p2p_lameRecVec_lastRow {r : LameRecurrence} {ν k H : ℝ} {n : ℕ}
    (hpos : ∀ p < n, 0 < r.alpha ν k p * r.gamma ν k (p + 1))
    (hH : (lameMatrix r ν k n).charpoly.eval H = 0) :
    (if n = 0 then 0 else r.gamma ν k n * lameRecVec r ν k H (n - 1)) +
      (r.beta ν k n - H) * lameRecVec r ν k H n = 0 := by
  rw [eval_charpoly, ← exists_mulVec_eq_zero_iff] at hH
  obtain ⟨u, hu0, hu⟩ := hH
  have hMu : lameMatrix r ν k n *ᵥ u = H • u := by
    rw [sub_mulVec, sub_eq_zero, scalar_apply] at hu
    rw [← hu]; funext i; simp [mulVec_diagonal]
  set U := p2p_ext u with hU
  have hα : ∀ p < n, r.alpha ν k p ≠ 0 := fun p hp h0 => by
    have := hpos p hp; rw [h0, zero_mul] at this; exact lt_irrefl _ this
  have hrow : ∀ p ≤ n, r.alpha ν k p * U (p + 1) + r.beta ν k p * U p +
      (if p = 0 then 0 else r.gamma ν k p * U (p - 1)) = H * U p := by
    intro p hp
    have h1 := congrFun hMu ⟨p, by omega⟩
    have h2 := p2p_row (r.alpha ν k) (r.beta ν k) (r.gamma ν k) u (p := p) (by omega)
    rw [show lameMatrix r ν k n = p2p_tridiag (r.alpha ν k) (r.beta ν k) (r.gamma ν k) n
      from rfl, h2] at h1
    rw [h1]
    simp [hU, p2p_ext, show p < n + 1 by omega]
  have hU0 : U 0 ≠ 0 := by
    intro h0
    refine hu0 (p2p_eigvec_zero_of_head (A := lameMatrix r ν k n) (μ := H) ?_ ?_ hMu ?_)
    · intro i j hij
      simp [lameMatrix, show ¬ (j : ℕ) = i + 1 by omega, show ¬ (j : ℕ) = i by omega,
        show ¬ (j : ℕ) + 1 = i by omega]
    · intro i j hij
      simp only [lameMatrix, of_apply, hij, ite_true]
      exact hα i (by omega)
    · simpa [hU, p2p_ext] using h0
  have hfw : ∀ p ≤ n, U p = U 0 * lameRecVec r ν k H p := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp
      rcases p with _ | p
      · rw [p2p_lameRecVec_zero, mul_one]
      · have hr := hrow p (by omega)
        rw [p2p_lameRecVec_succ]
        rw [ih p (by omega) (by omega)] at hr
        have hap := hα p (by omega)
        rw [eq_comm, mul_div_assoc', div_eq_iff hap]
        rcases p with _ | p
        · simp only [ite_true] at hr ⊢
          linear_combination -hr
        · simp only [show p + 1 ≠ 0 by omega, ite_false, show p + 1 - 1 = p by omega] at hr ⊢
          rw [ih p (by omega) (by omega)] at hr
          linear_combination -hr
  have hr := hrow n le_rfl
  have hn1 : U (n + 1) = 0 := by simp [hU, p2p_ext]
  rw [hn1, hfw n le_rfl] at hr
  refine (mul_eq_zero.mp (?_ : U 0 * _ = 0)).resolve_left hU0
  rcases n with _ | n
  · simp only [ite_true] at hr ⊢
    linear_combination hr
  · simp only [show n + 1 ≠ 0 by omega, ite_false, show n + 1 - 1 = n by omega] at hr ⊢
    rw [hfw n (by omega)] at hr
    linear_combination hr

/-- The interior rows of `M v = H v` for the forward-recursion vector. -/
lemma p2p_lameRecVec_row (r : LameRecurrence) (ν k H : ℝ) {q : ℕ} (hα : r.alpha ν k q ≠ 0) :
    (if q = 0 then 0 else r.gamma ν k q * lameRecVec r ν k H (q - 1)) +
      (r.beta ν k q - H) * lameRecVec r ν k H q +
      r.alpha ν k q * lameRecVec r ν k H (q + 1) = 0 := by
  rw [p2p_lameRecVec_succ, mul_div_cancel₀ _ hα]
  split_ifs <;> ring

/-- `γ_{n+1} = 0` at the order `ν = t.order n`. -/
lemma p2p_gamma_top (t : LamePolyType) (n : ℕ) (k : ℝ) :
    t.recurrence.gamma (t.order n) k (n + 1) = 0 := by
  cases t <;> simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.gamma] <;>
    push_cast <;> ring

/-- The coefficients `c_p` (extended by `0`) satisfy every row
`γ_q c_{q-1} + (β_q - H) c_q + α_q c_{q+1} = 0` of the recurrence, `q ≥ 0`. -/
lemma p2p_coeff_rows {k : ℝ} (hk0 : 0 < k) (t : LamePolyType) {n m : ℕ} (hm : m ≤ n) (q : ℕ) :
    (if q = 0 then 0 else t.recurrence.gamma (t.order n) k q * lamePolyCoeff t n m k (q - 1)) +
      (t.recurrence.beta (t.order n) k q - lamePolyH t n m k) * lamePolyCoeff t n m k q +
      t.recurrence.alpha (t.order n) k q * lamePolyCoeff t n m k (q + 1) = 0 := by
  set v := lameRecVec t.recurrence (t.order n) k (lamePolyH t n m k)
  set κ := (if t.signForm n v < 0 then -1 else 1) / Real.sqrt (t.normForm k n v)
  have hc : ∀ p, lamePolyCoeff t n m k p = if p ≤ n then κ * v p else 0 := fun p => by
    simp only [lamePolyCoeff, κ, v]
    split_ifs <;> ring
  have hpos := p2p_alpha_gamma_pos hk0 t n
  rcases lt_trichotomy q n with hq | hq | hq
  · have hα : t.recurrence.alpha (t.order n) k q ≠ 0 := fun h0 => by
      have := hpos q hq; rw [h0, zero_mul] at this; exact lt_irrefl _ this
    have := p2p_lameRecVec_row t.recurrence (t.order n) k (lamePolyH t n m k) hα
    rw [hc, hc, hc]
    simp only [show q ≤ n by omega, show q + 1 ≤ n by omega, show q - 1 ≤ n by omega, ite_true]
    split_ifs at this ⊢ <;> linear_combination κ * this
  · subst hq
    have := p2p_lameRecVec_lastRow hpos (p2p_lamePolyH_eval hk0 t hm)
    rw [hc, hc, hc]
    simp only [le_refl, show q - 1 ≤ q by omega, show ¬ q + 1 ≤ q by omega, ite_true,
      ite_false, mul_zero, add_zero]
    split_ifs at this ⊢ <;> linear_combination κ * this
  · rw [hc, hc, hc]
    simp only [show ¬ q ≤ n by omega, show ¬ q + 1 ≤ n by omega, ite_false, mul_zero,
      add_zero]
    rcases eq_or_lt_of_le (show n + 1 ≤ q by omega) with h | h
    · subst h
      simp [p2p_gamma_top]
    · simp [show ¬ q - 1 ≤ n by omega]

end p2pRows

/-- Composition of `p2p_master` and `p2p_vanish`. -/
lemma p2p_series_zero (k h lam M N s : ℂ) (P : ℤ → ℂ[X]) (δ : ℕ) (a b e : ℂ → ℂ)
    (hkind : ∀ j : ℤ, p2p_opVal k h lam M N (P j) s =
      a j * (P (j + 2)).eval s + b j * (P j).eval s + e j * (P (j - 2)).eval s)
    (n : ℕ) (c : ℕ → ℂ) (hc : ∀ p, n < p → c p = 0)
    (h01 : c 0 * e δ * (P ((δ : ℤ) - 2)).eval s +
      (c 0 * b δ + c 1 * e (2 + δ)) * (P δ).eval s +
      (c 0 * a δ + c 1 * b (2 + δ) + c 2 * e (4 + δ)) * (P ((2 + δ : ℕ) : ℤ)).eval s = 0)
    (hq : ∀ q : ℕ, c (q + 1) * a ((2 * (q + 1) + δ : ℕ) : ℂ) +
      c (q + 2) * b ((2 * (q + 2) + δ : ℕ) : ℂ) + c (q + 3) * e ((2 * (q + 3) + δ : ℕ) : ℂ) = 0) :
    p2p_opVal k h lam M N (∑ p ∈ Finset.range (n + 1), C (c p) * P ((2 * p + δ : ℕ) : ℤ)) s =
      0 := by
  rw [p2p_master k h lam M N s P δ a b e hkind n c hc]
  refine p2p_vanish n _ (fun q => (P ((2 * q + δ : ℕ) : ℤ)).eval s) _ ?_ fun q => ?_
  · simp only [ite_true, mul_zero, zero_add, Nat.cast_add, one_ne_zero, ite_false,
      Nat.sub_self]
    convert h01 using 3; push_cast; ring_nf
  · simp only [show q + 2 ≠ 0 by omega, ite_false, show q + 2 - 1 = q + 1 by omega,
      show q + 2 + 1 = q + 3 by omega]
    exact hq q

/-- The operator annihilates the Chebyshev series of type `uE`. -/
lemma p2p_ode_uE {k : ℝ} (hk0 : 0 < k) {n m : ℕ} (hm : m ≤ n) (s : ℂ) :
    p2p_opVal k ((lamePolyH .uE n m k + LamePolyType.order .uE n *
        (LamePolyType.order .uE n + 1) * k ^ 2) / 2)
      ((LamePolyType.order .uE n : ℂ) * ((LamePolyType.order .uE n : ℂ) + 1))
      (1 + (k : ℂ) ^ 2 - 2 * k ^ 2 * s ^ 2) 0
      (∑ p ∈ Finset.range (n + 1), C ((lamePolyCoeff .uE n m k p : ℂ) *
        (if p = 0 then 1 / 2 else 1)) * Chebyshev.T ℂ ((2 * p + 0 : ℕ) : ℤ)) s = 0 := by
  have R : ∀ q, _ := fun q => congrArg (fun x : ℝ => (x : ℂ)) (p2p_coeff_rows hk0 .uE hm q)
  have hc : ∀ p, n < p → lamePolyCoeff .uE n m k p = 0 := fun p hp => by
    simp [lamePolyCoeff, show ¬ p ≤ n by omega]
  refine p2p_series_zero _ _ _ _ _ s _ 0 (fun j => (k : ℂ) ^ 2 * (j ^ 2 + j - _) / 4)
    (fun j => (2 * _ + j ^ 2 * (k : ℂ) ^ 2 - 2 * j ^ 2 - k ^ 2 * _) / 2)
    (fun j => (k : ℂ) ^ 2 * (j ^ 2 - j - _) / 4) (fun j => p2p_kind_T1 k _ _ s j) n _
    (fun p hp => by simp [hc p hp]) ?_ fun q => ?_
  · have R0 := R 0
    have R1 := R 1
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma] at R0 R1
    simp only [LamePolyType.order]
    push_cast at R0 R1 ⊢
    try simp at R0 R1 ⊢
    linear_combination (-1/4 : ℂ) * R0 +
      (-1/2 * (Chebyshev.T ℂ 2).eval s) * R1
  · have R2 := R (q + 2)
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma, show q + 2 + 1 = q + 3 by omega] at R2
    simp only [LamePolyType.order]
    push_cast at R2 ⊢
    try simp at R2 ⊢
    linear_combination (-1/2) * R2

/-- The operator annihilates the Chebyshev series of type `sE`. -/
lemma p2p_ode_sE {k : ℝ} (hk0 : 0 < k) {n m : ℕ} (hm : m ≤ n) (s : ℂ) :
    p2p_opVal k ((lamePolyH .sE n m k + LamePolyType.order .sE n *
        (LamePolyType.order .sE n + 1) * k ^ 2) / 2)
      ((LamePolyType.order .sE n : ℂ) * ((LamePolyType.order .sE n : ℂ) + 1))
      (1 + (k : ℂ) ^ 2 - 2 * k ^ 2 * s ^ 2) 0
      (∑ p ∈ Finset.range (n + 1), C (lamePolyCoeff .sE n m k p : ℂ) *
        Chebyshev.T ℂ ((2 * p + 1 : ℕ) : ℤ)) s = 0 := by
  have R : ∀ q, _ := fun q => congrArg (fun x : ℝ => (x : ℂ)) (p2p_coeff_rows hk0 .sE hm q)
  have hc : ∀ p, n < p → lamePolyCoeff .sE n m k p = 0 := fun p hp => by
    simp [lamePolyCoeff, show ¬ p ≤ n by omega]
  refine p2p_series_zero _ _ _ _ _ s _ 1 (fun j => (k : ℂ) ^ 2 * (j ^ 2 + j - _) / 4)
    (fun j => (2 * _ + j ^ 2 * (k : ℂ) ^ 2 - 2 * j ^ 2 - k ^ 2 * _) / 2)
    (fun j => (k : ℂ) ^ 2 * (j ^ 2 - j - _) / 4) (fun j => p2p_kind_T1 k _ _ s j) n _
    (fun p hp => by simp [hc p hp]) ?_ fun q => ?_
  · have R0 := R 0
    have R1 := R 1
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma] at R0 R1
    simp only [LamePolyType.order]
    push_cast at R0 R1 ⊢
    try simp at R0 R1 ⊢
    linear_combination (-1/2 * s) * R0 + (-1/2 * (Chebyshev.T ℂ 3).eval s) * R1
  · have R2 := R (q + 2)
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma, show q + 2 + 1 = q + 3 by omega] at R2
    simp only [LamePolyType.order]
    push_cast at R2 ⊢
    linear_combination (-1/2) * R2

/-- The operator annihilates the Chebyshev series of type `cE`. -/
lemma p2p_ode_cE {k : ℝ} (hk0 : 0 < k) {n m : ℕ} (hm : m ≤ n) (s : ℂ) :
    p2p_opVal k ((lamePolyH .cE n m k + LamePolyType.order .cE n *
        (LamePolyType.order .cE n + 1) * k ^ 2) / 2)
      ((LamePolyType.order .cE n : ℂ) * ((LamePolyType.order .cE n : ℂ) + 1))
      (1 + (k : ℂ) ^ 2 - 2 * k ^ 2 * s ^ 2 + 2 * (1 - k ^ 2 * s ^ 2)) (2 * (k : ℂ) ^ 2 * s ^ 2 - 1)
      (∑ p ∈ Finset.range (n + 1), C (lamePolyCoeff .cE n m k p : ℂ) *
        Chebyshev.U ℂ ((2 * p + 0 : ℕ) : ℤ)) s = 0 := by
  have R : ∀ q, _ := fun q => congrArg (fun x : ℝ => (x : ℂ)) (p2p_coeff_rows hk0 .cE hm q)
  have hc : ∀ p, n < p → lamePolyCoeff .cE n m k p = 0 := fun p hp => by
    simp [lamePolyCoeff, show ¬ p ≤ n by omega]
  refine p2p_series_zero _ _ _ _ _ s _ 0 (fun j => (k : ℂ) ^ 2 * (j ^ 2 + 3 * j - _ + 2) / 4)
    (fun j => (2 * _ + j ^ 2 * (k : ℂ) ^ 2 - 2 * j ^ 2 + 2 * j * k ^ 2 - 4 * j - k ^ 2 * _ +
      k ^ 2 - 2) / 2)
    (fun j => (k : ℂ) ^ 2 * (j ^ 2 + j - _) / 4) (fun j => p2p_kind_Uc k _ _ s j) n _
    (fun p hp => by simp [hc p hp]) ?_ fun q => ?_
  · have R0 := R 0
    have R1 := R 1
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma] at R0 R1
    simp only [LamePolyType.order]
    push_cast at R0 R1 ⊢
    try simp at R0 R1 ⊢
    linear_combination (-1/2 : ℂ) * R0 + (-1/2 * (Chebyshev.U ℂ 2).eval s) * R1
  · have R2 := R (q + 2)
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma, show q + 2 + 1 = q + 3 by omega] at R2
    simp only [LamePolyType.order]
    push_cast at R2 ⊢
    try simp at R2 ⊢
    linear_combination (-1/2) * R2

/-- The operator annihilates the Chebyshev series of type `dE`. -/
lemma p2p_ode_dE {k : ℝ} (hk0 : 0 < k) {n m : ℕ} (hm : m ≤ n) (s : ℂ) :
    p2p_opVal k ((lamePolyH .dE n m k + LamePolyType.order .dE n *
        (LamePolyType.order .dE n + 1) * k ^ 2) / 2)
      ((LamePolyType.order .dE n : ℂ) * ((LamePolyType.order .dE n : ℂ) + 1))
      (1 + (k : ℂ) ^ 2 - 2 * k ^ 2 * s ^ 2 + 2 * k ^ 2 * (1 - s ^ 2))
      (-(k : ℂ) ^ 2 * (1 - 2 * s ^ 2))
      (∑ p ∈ Finset.range (n + 1), C ((lamePolyCoeff .dE n m k p : ℂ) *
        (if p = 0 then 1 / 2 else 1)) * Chebyshev.T ℂ ((2 * p + 0 : ℕ) : ℤ)) s = 0 := by
  have R : ∀ q, _ := fun q => congrArg (fun x : ℝ => (x : ℂ)) (p2p_coeff_rows hk0 .dE hm q)
  have hc : ∀ p, n < p → lamePolyCoeff .dE n m k p = 0 := fun p hp => by
    simp [lamePolyCoeff, show ¬ p ≤ n by omega]
  refine p2p_series_zero _ _ _ _ _ s _ 0 (fun j => (k : ℂ) ^ 2 * (j ^ 2 + 3 * j - _ + 2) / 4)
    (fun j => (2 * _ + j ^ 2 * (k : ℂ) ^ 2 - 2 * j ^ 2 - k ^ 2 * _) / 2)
    (fun j => (k : ℂ) ^ 2 * (j ^ 2 - 3 * j - _ + 2) / 4) (fun j => p2p_kind_Td k _ _ s j) n _
    (fun p hp => by simp [hc p hp]) ?_ fun q => ?_
  · have R0 := R 0
    have R1 := R 1
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma] at R0 R1
    simp only [LamePolyType.order]
    push_cast at R0 R1 ⊢
    try simp at R0 R1 ⊢
    linear_combination (-1/4 : ℂ) * R0 + (-1/2 * (Chebyshev.T ℂ 2).eval s) * R1
  · have R2 := R (q + 2)
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma, show q + 2 + 1 = q + 3 by omega] at R2
    simp only [LamePolyType.order]
    push_cast at R2 ⊢
    try simp at R2 ⊢
    linear_combination (-1/2) * R2

/-- The operator annihilates the Chebyshev series of type `scE`. -/
lemma p2p_ode_scE {k : ℝ} (hk0 : 0 < k) {n m : ℕ} (hm : m ≤ n) (s : ℂ) :
    p2p_opVal k ((lamePolyH .scE n m k + LamePolyType.order .scE n *
        (LamePolyType.order .scE n + 1) * k ^ 2) / 2)
      ((LamePolyType.order .scE n : ℂ) * ((LamePolyType.order .scE n : ℂ) + 1))
      (1 + (k : ℂ) ^ 2 - 2 * k ^ 2 * s ^ 2 + 2 * (1 - k ^ 2 * s ^ 2)) (2 * (k : ℂ) ^ 2 * s ^ 2 - 1)
      (∑ p ∈ Finset.range (n + 1), C (lamePolyCoeff .scE n m k p : ℂ) *
        Chebyshev.U ℂ ((2 * p + 1 : ℕ) : ℤ)) s = 0 := by
  have R : ∀ q, _ := fun q => congrArg (fun x : ℝ => (x : ℂ)) (p2p_coeff_rows hk0 .scE hm q)
  have hc : ∀ p, n < p → lamePolyCoeff .scE n m k p = 0 := fun p hp => by
    simp [lamePolyCoeff, show ¬ p ≤ n by omega]
  refine p2p_series_zero _ _ _ _ _ s _ 1 (fun j => (k : ℂ) ^ 2 * (j ^ 2 + 3 * j - _ + 2) / 4)
    (fun j => (2 * _ + j ^ 2 * (k : ℂ) ^ 2 - 2 * j ^ 2 + 2 * j * k ^ 2 - 4 * j - k ^ 2 * _ +
      k ^ 2 - 2) / 2)
    (fun j => (k : ℂ) ^ 2 * (j ^ 2 + j - _) / 4) (fun j => p2p_kind_Uc k _ _ s j) n _
    (fun p hp => by simp [hc p hp]) ?_ fun q => ?_
  · have R0 := R 0
    have R1 := R 1
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma] at R0 R1
    simp only [LamePolyType.order]
    push_cast at R0 R1 ⊢
    try simp at R0 R1 ⊢
    linear_combination (-1/2 * (2 * s)) * R0 + (-1/2 * (Chebyshev.U ℂ 3).eval s) * R1
  · have R2 := R (q + 2)
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma, show q + 2 + 1 = q + 3 by omega] at R2
    simp only [LamePolyType.order]
    push_cast at R2 ⊢
    linear_combination (-1/2) * R2

/-- The operator annihilates the Chebyshev series of type `sdE`. -/
lemma p2p_ode_sdE {k : ℝ} (hk0 : 0 < k) {n m : ℕ} (hm : m ≤ n) (s : ℂ) :
    p2p_opVal k ((lamePolyH .sdE n m k + LamePolyType.order .sdE n *
        (LamePolyType.order .sdE n + 1) * k ^ 2) / 2)
      ((LamePolyType.order .sdE n : ℂ) * ((LamePolyType.order .sdE n : ℂ) + 1))
      (1 + (k : ℂ) ^ 2 - 2 * k ^ 2 * s ^ 2 + 2 * k ^ 2 * (1 - s ^ 2))
      (-(k : ℂ) ^ 2 * (1 - 2 * s ^ 2))
      (∑ p ∈ Finset.range (n + 1), C (lamePolyCoeff .sdE n m k p : ℂ) *
        Chebyshev.T ℂ ((2 * p + 1 : ℕ) : ℤ)) s = 0 := by
  have R : ∀ q, _ := fun q => congrArg (fun x : ℝ => (x : ℂ)) (p2p_coeff_rows hk0 .sdE hm q)
  have hc : ∀ p, n < p → lamePolyCoeff .sdE n m k p = 0 := fun p hp => by
    simp [lamePolyCoeff, show ¬ p ≤ n by omega]
  refine p2p_series_zero _ _ _ _ _ s _ 1 (fun j => (k : ℂ) ^ 2 * (j ^ 2 + 3 * j - _ + 2) / 4)
    (fun j => (2 * _ + j ^ 2 * (k : ℂ) ^ 2 - 2 * j ^ 2 - k ^ 2 * _) / 2)
    (fun j => (k : ℂ) ^ 2 * (j ^ 2 - 3 * j - _ + 2) / 4) (fun j => p2p_kind_Td k _ _ s j) n _
    (fun p hp => by simp [hc p hp]) ?_ fun q => ?_
  · have R0 := R 0
    have R1 := R 1
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma] at R0 R1
    simp only [LamePolyType.order]
    push_cast at R0 R1 ⊢
    try simp at R0 R1 ⊢
    linear_combination (-1/2 * s) * R0 + (-1/2 * (Chebyshev.T ℂ 3).eval s) * R1
  · have R2 := R (q + 2)
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma, show q + 2 + 1 = q + 3 by omega] at R2
    simp only [LamePolyType.order]
    push_cast at R2 ⊢
    linear_combination (-1/2) * R2

/-- The operator annihilates the Chebyshev series of type `cdE`. -/
lemma p2p_ode_cdE {k : ℝ} (hk0 : 0 < k) {n m : ℕ} (hm : m ≤ n) (s : ℂ) :
    p2p_opVal k ((lamePolyH .cdE n m k + LamePolyType.order .cdE n *
        (LamePolyType.order .cdE n + 1) * k ^ 2) / 2)
      ((LamePolyType.order .cdE n : ℂ) * ((LamePolyType.order .cdE n : ℂ) + 1))
      (3 * (1 + (k : ℂ) ^ 2 - 2 * k ^ 2 * s ^ 2))
      (4 * (k : ℂ) ^ 2 * s ^ 2 - (1 + k ^ 2 - 2 * k ^ 2 * s ^ 2))
      (∑ p ∈ Finset.range (n + 1), C (lamePolyCoeff .cdE n m k p : ℂ) *
        Chebyshev.U ℂ ((2 * p + 0 : ℕ) : ℤ)) s = 0 := by
  have R : ∀ q, _ := fun q => congrArg (fun x : ℝ => (x : ℂ)) (p2p_coeff_rows hk0 .cdE hm q)
  have hc : ∀ p, n < p → lamePolyCoeff .cdE n m k p = 0 := fun p hp => by
    simp [lamePolyCoeff, show ¬ p ≤ n by omega]
  refine p2p_series_zero _ _ _ _ _ s _ 0 (fun j => (k : ℂ) ^ 2 * (j ^ 2 + 5 * j - _ + 6) / 4)
    (fun j => (2 * _ + j ^ 2 * (k : ℂ) ^ 2 - 2 * j ^ 2 + 2 * j * k ^ 2 - 4 * j - k ^ 2 * _ +
      k ^ 2 - 2) / 2)
    (fun j => (k : ℂ) ^ 2 * (j ^ 2 - j - _) / 4) (fun j => p2p_kind_Ucd k _ _ s j) n _
    (fun p hp => by simp [hc p hp]) ?_ fun q => ?_
  · have R0 := R 0
    have R1 := R 1
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma] at R0 R1
    simp only [LamePolyType.order]
    push_cast at R0 R1 ⊢
    try simp at R0 R1 ⊢
    linear_combination (-1/2 : ℂ) * R0 + (-1/2 * (Chebyshev.U ℂ 2).eval s) * R1
  · have R2 := R (q + 2)
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma, show q + 2 + 1 = q + 3 by omega] at R2
    simp only [LamePolyType.order]
    push_cast at R2 ⊢
    try simp at R2 ⊢
    linear_combination (-1/2) * R2

/-- The operator annihilates the Chebyshev series of type `scdE`. -/
lemma p2p_ode_scdE {k : ℝ} (hk0 : 0 < k) {n m : ℕ} (hm : m ≤ n) (s : ℂ) :
    p2p_opVal k ((lamePolyH .scdE n m k + LamePolyType.order .scdE n *
        (LamePolyType.order .scdE n + 1) * k ^ 2) / 2)
      ((LamePolyType.order .scdE n : ℂ) * ((LamePolyType.order .scdE n : ℂ) + 1))
      (3 * (1 + (k : ℂ) ^ 2 - 2 * k ^ 2 * s ^ 2))
      (4 * (k : ℂ) ^ 2 * s ^ 2 - (1 + k ^ 2 - 2 * k ^ 2 * s ^ 2))
      (∑ p ∈ Finset.range (n + 1), C (lamePolyCoeff .scdE n m k p : ℂ) *
        Chebyshev.U ℂ ((2 * p + 1 : ℕ) : ℤ)) s = 0 := by
  have R : ∀ q, _ := fun q => congrArg (fun x : ℝ => (x : ℂ)) (p2p_coeff_rows hk0 .scdE hm q)
  have hc : ∀ p, n < p → lamePolyCoeff .scdE n m k p = 0 := fun p hp => by
    simp [lamePolyCoeff, show ¬ p ≤ n by omega]
  refine p2p_series_zero _ _ _ _ _ s _ 1 (fun j => (k : ℂ) ^ 2 * (j ^ 2 + 5 * j - _ + 6) / 4)
    (fun j => (2 * _ + j ^ 2 * (k : ℂ) ^ 2 - 2 * j ^ 2 + 2 * j * k ^ 2 - 4 * j - k ^ 2 * _ +
      k ^ 2 - 2) / 2)
    (fun j => (k : ℂ) ^ 2 * (j ^ 2 - j - _) / 4) (fun j => p2p_kind_Ucd k _ _ s j) n _
    (fun p hp => by simp [hc p hp]) ?_ fun q => ?_
  · have R0 := R 0
    have R1 := R 1
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma] at R0 R1
    simp only [LamePolyType.order]
    push_cast at R0 R1 ⊢
    try simp at R0 R1 ⊢
    linear_combination (-1/2 * (2 * s)) * R0 + (-1/2 * (Chebyshev.U ℂ 3).eval s) * R1
  · have R2 := R (q + 2)
    simp only [LamePolyType.recurrence, LamePolyType.order, LameRecurrence.alpha,
      LameRecurrence.beta, LameRecurrence.gamma, show q + 2 + 1 = q + 3 by omega] at R2
    simp only [LamePolyType.order]
    push_cast at R2 ⊢
    linear_combination (-1/2) * R2

/-- Rewrites `lamePolyEk` as prefactor times a polynomial in `sn`. -/
macro "p2p_eq_tac" : tactic => `(tactic| (
  simp only [lamePolyEk, LamePolyType.prefactor, LamePolyType.basis, eval_finsetSum, eval_mul,
    eval_C, add_zero]
  try (congr 1; exact Finset.sum_congr rfl fun p _ => by ring)))

/-- The Lamé polynomials solve Lamé's equation 29.2.1 with `ν = t.order n` and
`h = ½(H_m + ν(ν+1)k²)`, at every point where `sn` is regular. -/
theorem p2p_lamePolyEk_isLameSolution {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType)
    {n m : ℕ} (hm : m ≤ n) :
    IsLameSolutionOn ((lamePolyH t n m k + t.order n * (t.order n + 1) * k ^ 2) / 2)
      (t.order n) k (fun z => lamePolyEk t n m z k) {z | jacobiRegulark .n z k} := by
  have hk := p22R1_ofReal_mem hk0 hk1
  cases t
  · convert p2p_solution_one hk _ _ _ (p2p_ode_uE hk0 hm) using 2 with z
    p2p_eq_tac
  · convert p2p_solution_one hk _ _ _ (p2p_ode_sE hk0 hm) using 2 with z
    p2p_eq_tac
  · convert p2p_solution_c hk _ _ _ (p2p_ode_cE hk0 hm) using 2 with z
    p2p_eq_tac
  · convert p2p_solution_d hk _ _ _ (p2p_ode_dE hk0 hm) using 2 with z
    p2p_eq_tac
  · convert p2p_solution_c hk _ _ _ (p2p_ode_scE hk0 hm) using 2 with z
    p2p_eq_tac
  · convert p2p_solution_d hk _ _ _ (p2p_ode_sdE hk0 hm) using 2 with z
    p2p_eq_tac
  · convert p2p_solution_cd hk _ _ _ (p2p_ode_cdE hk0 hm) using 2 with z
    p2p_eq_tac
  · convert p2p_solution_cd hk _ _ _ (p2p_ode_scdE hk0 hm) using 2 with z
    p2p_eq_tac

/-- For real `0 < k < 1`, a point other than `2pK + (2q+1)iK'` is not a pole of `sn, cn, dn`. -/
lemma p2p_regular {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) {z : ℂ}
    (hz : ∀ p q : ℤ,
      z ≠ 2 * p * Real.compEllIntKm (k ^ 2) + (2 * q + 1) * I * Real.compEllIntKm (1 - k ^ 2)) :
    jacobiRegulark .n z k := by
  have hkD : (k : ℂ) ∈ jacobiModulusDomain := p22R1_ofReal_mem hk0 hk1
  have hτ := jacobiTauk_im_pos hkD
  have hK : compEllIntKk (k : ℂ) = (Real.compEllIntKm (k ^ 2) : ℂ) :=
    compEllIntKk_ofReal (by nlinarith)
  have hK' : compEllIntKpk (k : ℂ) = (Real.compEllIntKm (1 - k ^ 2) : ℂ) :=
    compEllIntKpk_ofReal (by positivity)
  have hK0 := compEllIntKk_ne_zero hkD
  intro h0
  have h4 : jacobiThetaFourTau (jacobiZetak z k) (jacobiTauk k) = 0 := by
    simp only [jacobiLetterTheta, div_eq_zero_iff] at h0
    exact h0.resolve_right (je22a_thetaFour_zero_ne_zero hτ)
  obtain ⟨m, n, hmn⟩ := ((DLMF.Theta.jacobiThetaTau_eq_zero_iff hτ _).2.2.2).1 h4
  apply hz m n
  rw [jacobiZetak, jacobiTauk, hK', hK] at hmn
  rw [hK] at hK0
  field_simp at hmn
  linear_combination hmn

/-- Real points are regular. -/
theorem p2p_regular_real {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    jacobiRegulark .n (x : ℂ) k := by
  refine p2p_regular hk0 hk1 fun p q h => ?_
  have hK' : 0 < Real.compEllIntKm (1 - k ^ 2) := Real.compEllIntKm_pos (by nlinarith)
  have := congrArg Complex.im h
  simp at this
  have hq : (2 * (q : ℝ) + 1) ≠ 0 := by
    intro h2
    have : (2 * q + 1 : ℤ) = 0 := by exact_mod_cast h2
    omega
  rcases this with h1 | h1
  · exact hq (by linarith)
  · linarith

/-- The points `K + iτ`, `τ` real, are regular. -/
theorem p2p_regular_vert {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (τ : ℝ) :
    jacobiRegulark .n ((Real.compEllIntKm (k ^ 2) : ℂ) + I * τ) k := by
  refine p2p_regular hk0 hk1 fun p q h => ?_
  have hK : 0 < Real.compEllIntKm (k ^ 2) := Real.compEllIntKm_pos (by nlinarith)
  have hK' : 0 < Real.compEllIntKm (1 - k ^ 2) := Real.compEllIntKm_pos (by nlinarith)
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  have hp : (1 : ℝ) = 2 * p := by
    have := mul_right_cancel₀ hK.ne' (show 1 * Real.compEllIntKm (k ^ 2) =
      (2 * p) * Real.compEllIntKm (k ^ 2) by linarith)
    exact this
  have : (1 : ℤ) = 2 * p := by exact_mod_cast hp
  omega

/-- Green's identity for two solutions of Lamé's equation along the segment `x ↦ p₀ + u x`. -/
lemma p2p_green {k : ℂ} (hk : k ∈ jacobiModulusDomain) {h1 h2 ν1 ν2 : ℂ} {E1 E2 : ℂ → ℂ}
    (hE1 : IsLameSolutionOn h1 ν1 k E1 {z | jacobiRegulark .n z k})
    (hE2 : IsLameSolutionOn h2 ν2 k E2 {z | jacobiRegulark .n z k}) (p0 u : ℂ) (a b : ℝ)
    (hreg : ∀ x : ℝ, jacobiRegulark .n (p0 + u * x) k) :
    ∫ x in a..b, u * ((h2 - h1) - (ν2 * (ν2 + 1) - ν1 * (ν1 + 1)) * k ^ 2 *
        jacobiSnk (p0 + u * x) k ^ 2) * E1 (p0 + u * x) * E2 (p0 + u * x) =
      (deriv E1 (p0 + u * b) * E2 (p0 + u * b) - E1 (p0 + u * b) * deriv E2 (p0 + u * b)) -
      (deriv E1 (p0 + u * a) * E2 (p0 + u * a) - E1 (p0 + u * a) * deriv E2 (p0 + u * a)) := by
  set γ : ℝ → ℂ := fun x => p0 + u * x with hγdef
  have hγ : ∀ x : ℝ, HasDerivAt γ u x := fun x => by
    have := ((hasDerivAt_id x).ofReal_comp.const_mul u).const_add p0
    simpa [hγdef] using this
  have hγc : Continuous γ := by rw [hγdef]; fun_prop
  have hD : ∀ x : ℝ, HasDerivAt (fun x => deriv E1 (γ x) * E2 (γ x) - E1 (γ x) * deriv E2 (γ x))
      (u * ((h2 - h1) - (ν2 * (ν2 + 1) - ν1 * (ν1 + 1)) * k ^ 2 * jacobiSnk (γ x) k ^ 2) *
        E1 (γ x) * E2 (γ x)) x := fun x => by
    have r := hreg x
    have d1 := (hE1.hasDerivAt_deriv _ r).comp x (hγ x)
    have d2 := (hE2.hasDerivAt_deriv _ r).comp x (hγ x)
    have e1 := (hE1.differentiableAt _ r).hasDerivAt.comp x (hγ x)
    have e2 := (hE2.differentiableAt _ r).hasDerivAt.comp x (hγ x)
    convert (d1.mul e2).sub (e1.mul d2) using 1
    · rfl
    · simp only [Function.comp_apply, hγdef]; ring
  have hcont : Continuous fun x => u * ((h2 - h1) - (ν2 * (ν2 + 1) - ν1 * (ν1 + 1)) * k ^ 2 *
      jacobiSnk (γ x) k ^ 2) * E1 (γ x) * E2 (γ x) := by
    have hs : Continuous fun x => jacobiSnk (γ x) k := continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_jacobiSnk hk (hreg x)).continuousAt.comp (f := γ) hγc.continuousAt
    have c1 : Continuous fun x => E1 (γ x) := continuous_iff_continuousAt.2 fun x =>
      (hE1.differentiableAt _ (hreg x)).continuousAt.comp (f := γ) hγc.continuousAt
    have c2 : Continuous fun x => E2 (γ x) := continuous_iff_continuousAt.2 fun x =>
      (hE2.differentiableAt _ (hreg x)).continuousAt.comp (f := γ) hγc.continuousAt
    exact ((continuous_const.mul (continuous_const.sub (continuous_const.mul (hs.pow 2)))).mul
      c1).mul c2
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hD x)
    (hcont.intervalIntegrable _ _)

/-- The Wronskian of two functions with the same reflection symmetry about `p` vanishes at
`p`. -/
lemma p2p_wronskian_sym {E1 E2 : ℂ → ℂ} {p σ : ℂ} (hσ : σ = 1 ∨ σ = -1)
    (h1 : ∀ z, E1 (p - z) = σ * E1 (p + z)) (h2 : ∀ z, E2 (p - z) = σ * E2 (p + z))
    (hd1 : DifferentiableAt ℂ E1 p) (hd2 : DifferentiableAt ℂ E2 p) :
    deriv E1 p * E2 p - E1 p * deriv E2 p = 0 := by
  rcases hσ with rfl | rfl
  · have hz : ∀ {E : ℂ → ℂ}, DifferentiableAt ℂ E p → (∀ z, E (p - z) = 1 * E (p + z)) →
        deriv E p = 0 := fun {E} hd hE => by
      have a1 : HasDerivAt (fun z => E (p + z)) (deriv E p) 0 :=
        HasDerivAt.comp_const_add p 0 (by simpa using hd.hasDerivAt)
      have a2 : HasDerivAt (fun z => E (p - z)) (-deriv E p) 0 :=
        HasDerivAt.comp_const_sub p 0 (by simpa using hd.hasDerivAt)
      have e : (fun z => E (p - z)) = fun z => E (p + z) := funext fun z => by simp [hE z]
      rw [e] at a2
      have := a1.unique a2
      linear_combination this / 2
    rw [hz hd1 h1, hz hd2 h2]; ring
  · have hz : ∀ {E : ℂ → ℂ}, (∀ z, E (p - z) = -1 * E (p + z)) → E p = 0 := fun {E} hE => by
      have := hE 0
      simp only [sub_zero, add_zero] at this
      linear_combination this / 2
    rw [hz h1, hz h2]; ring

/-- Green's identity, split. -/
lemma p2p_green_split {k : ℂ} (hk : k ∈ jacobiModulusDomain) {h1 h2 ν1 ν2 : ℂ} {E1 E2 : ℂ → ℂ}
    (hE1 : IsLameSolutionOn h1 ν1 k E1 {z | jacobiRegulark .n z k})
    (hE2 : IsLameSolutionOn h2 ν2 k E2 {z | jacobiRegulark .n z k}) (p0 u : ℂ) (a b : ℝ)
    (hreg : ∀ x : ℝ, jacobiRegulark .n (p0 + u * x) k) :
    u * ((h2 - h1) * ∫ x in a..b, E1 (p0 + u * x) * E2 (p0 + u * x)) -
      u * ((ν2 * (ν2 + 1) - ν1 * (ν1 + 1)) * k ^ 2 *
        ∫ x in a..b, jacobiSnk (p0 + u * x) k ^ 2 * (E1 (p0 + u * x) * E2 (p0 + u * x))) =
      (deriv E1 (p0 + u * b) * E2 (p0 + u * b) - E1 (p0 + u * b) * deriv E2 (p0 + u * b)) -
      (deriv E1 (p0 + u * a) * E2 (p0 + u * a) - E1 (p0 + u * a) * deriv E2 (p0 + u * a)) := by
  rw [← p2p_green hk hE1 hE2 p0 u a b hreg]
  have hγc : Continuous fun x : ℝ => p0 + u * x := by fun_prop
  have hs : Continuous fun x : ℝ => jacobiSnk (p0 + u * x) k :=
    continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_jacobiSnk hk (hreg x)).continuousAt.comp (f := fun x : ℝ => p0 + u * x)
        hγc.continuousAt
  have c1 : Continuous fun x : ℝ => E1 (p0 + u * x) := continuous_iff_continuousAt.2 fun x =>
    (hE1.differentiableAt _ (hreg x)).continuousAt.comp (f := fun x : ℝ => p0 + u * x)
      hγc.continuousAt
  have c2 : Continuous fun x : ℝ => E2 (p0 + u * x) := continuous_iff_continuousAt.2 fun x =>
    (hE2.differentiableAt _ (hreg x)).continuousAt.comp (f := fun x : ℝ => p0 + u * x)
      hγc.continuousAt
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub]
  · exact intervalIntegral.integral_congr fun x _ => by ring
  · exact (continuous_const.mul (continuous_const.mul (c1.mul c2))).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_const.mul
      ((hs.pow 2).mul (c1.mul c2)))).intervalIntegrable _ _

/-- `H_m < H_{m'}` for `m < m' ≤ n` (29.15.3). -/
theorem p2p_lamePolyH_lt {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) {n m m' : ℕ}
    (h : m < m') (hm' : m' ≤ n) : lamePolyH t n m k < lamePolyH t n m' k := by
  have hs := (lamePolyH_strictMono hk0 hk1 t n).2.2
  induction m', h using Nat.le_induction with
  | base => exact hs m (by omega)
  | succ j hj ih => exact (ih (by omega)).trans (hs j (by omega))

/-- Continuity along a line of a solution of Lamé's equation and of `sn`. -/
lemma p2p_path_cont {k : ℂ} (hk : k ∈ jacobiModulusDomain) {h ν : ℂ} {E : ℂ → ℂ}
    (hE : IsLameSolutionOn h ν k E {z | jacobiRegulark .n z k}) (p0 u : ℂ)
    (hreg : ∀ x : ℝ, jacobiRegulark .n (p0 + u * x) k) :
    Continuous (fun x : ℝ => E (p0 + u * x)) ∧
      Continuous (fun x : ℝ => jacobiSnk (p0 + u * x) k) := by
  have hγc : Continuous fun x : ℝ => p0 + u * x := by fun_prop
  exact ⟨continuous_iff_continuousAt.2 fun x =>
    (hE.differentiableAt _ (hreg x)).continuousAt.comp (f := fun x : ℝ => p0 + u * x)
      hγc.continuousAt, continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_jacobiSnk hk (hreg x)).continuousAt.comp (f := fun x : ℝ => p0 + u * x)
      hγc.continuousAt⟩

/-- The integral over a period of a periodic function odd about `c` vanishes. -/
lemma p2p_integral_odd_periodic (f : ℝ → ℂ) (T c : ℝ) (hper : ∀ x, f (x + T) = f x)
    (hodd : ∀ x, f (c - x) = -f (c + x)) : ∫ x in (0 : ℝ)..T, f x = 0 := by
  have h1 : ∫ x in (0 : ℝ)..T, f x = ∫ x in (c - T / 2)..(c - T / 2 + T), f x := by
    simpa using (Function.Periodic.intervalIntegral_add_eq (f := f) hper 0 (c - T / 2))
  have h2 : ∫ x in (c - T / 2)..(c - T / 2 + T), f x = ∫ y in (-(T / 2))..(T / 2), f (c + y) := by
    rw [intervalIntegral.integral_comp_add_left]; congr 1; ring
  have h3 : ∫ y in (-(T / 2))..(T / 2), f (c + -y) = ∫ y in (-(T / 2))..(T / 2), f (c + y) := by
    rw [intervalIntegral.integral_comp_neg (fun y => f (c + y))]; simp
  have h4 : ∫ y in (-(T / 2))..(T / 2), f (c + -y) = -∫ y in (-(T / 2))..(T / 2), f (c + y) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun y _ => by
      simp only [← sub_eq_add_neg]; exact hodd y
  rw [h1, h2]
  linear_combination (h3.symm.trans h4) / 2

/-- The inner product 29.14.2 of two products `E(s)E(K + iτ)` on `[0, a] × [0, b]` in terms of
one-dimensional integrals. -/
theorem p2p_inner_split {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) {t t' : LamePolyType}
    {n m n' m' : ℕ} (hm : m ≤ n) (hm' : m' ≤ n') (a b : ℝ) :
    lameInner k a b (lameProduct t n m k) (lameProduct t' n' m' k) =
      (∫ x in (0 : ℝ)..a, lamePolyEk t n m x k * lamePolyEk t' n' m' x k) *
        (∫ x in (0 : ℝ)..b, jacobiSnk (Real.compEllIntKm (k ^ 2) + I * x) k ^ 2 *
          (lamePolyEk t n m (Real.compEllIntKm (k ^ 2) + I * x) k *
            lamePolyEk t' n' m' (Real.compEllIntKm (k ^ 2) + I * x) k)) -
      (∫ x in (0 : ℝ)..a, jacobiSnk x k ^ 2 * (lamePolyEk t n m x k * lamePolyEk t' n' m' x k)) *
        (∫ x in (0 : ℝ)..b, lamePolyEk t n m (Real.compEllIntKm (k ^ 2) + I * x) k *
            lamePolyEk t' n' m' (Real.compEllIntKm (k ^ 2) + I * x) k) := by
  set K := Real.compEllIntKm (k ^ 2)
  have hk := p22R1_ofReal_mem hk0 hk1
  have S1 := p2p_lamePolyEk_isLameSolution hk0 hk1 t hm
  have S2 := p2p_lamePolyEk_isLameSolution hk0 hk1 t' hm'
  have rr : ∀ x : ℝ, jacobiRegulark .n (0 + 1 * x) k := fun x => by
    simpa using p2p_regular_real hk0 hk1 x
  have rv : ∀ x : ℝ, jacobiRegulark .n ((K : ℂ) + I * x) k := p2p_regular_vert hk0 hk1
  obtain ⟨cf1, cs⟩ := p2p_path_cont hk S1 0 1 rr
  obtain ⟨cf2, -⟩ := p2p_path_cont hk S2 0 1 rr
  obtain ⟨cg1, csv⟩ := p2p_path_cont hk S1 (K : ℂ) I rv
  obtain ⟨cg2, -⟩ := p2p_path_cont hk S2 (K : ℂ) I rv
  simp only [zero_add, one_mul] at cf1 cs cf2
  have hin : ∀ s : ℝ, ∫ τ in (0 : ℝ)..b, lameOrthWeight k s τ * lameProduct t n m k s τ *
      lameProduct t' n' m' k s τ =
      lamePolyEk t n m s k * lamePolyEk t' n' m' s k *
        (∫ x in (0 : ℝ)..b, jacobiSnk (K + I * x) k ^ 2 *
          (lamePolyEk t n m (K + I * x) k * lamePolyEk t' n' m' (K + I * x) k)) -
      jacobiSnk s k ^ 2 * (lamePolyEk t n m s k * lamePolyEk t' n' m' s k) *
        (∫ x in (0 : ℝ)..b,
          lamePolyEk t n m (K + I * x) k * lamePolyEk t' n' m' (K + I * x) k) := by
    intro s
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub]
    · exact intervalIntegral.integral_congr fun τ _ => by
        simp only [lameOrthWeight, lameProduct]; ring
    · exact (continuous_const.mul ((csv.pow 2).mul (cg1.mul cg2))).intervalIntegrable _ _
    · exact (continuous_const.mul (cg1.mul cg2)).intervalIntegrable _ _
  rw [lameInner, intervalIntegral.integral_congr fun s _ => hin s,
    intervalIntegral.integral_sub, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const]
  · exact ((cf1.mul cf2).mul continuous_const).intervalIntegrable _ _
  · exact (((cs.pow 2).mul (cf1.mul cf2)).mul continuous_const).intervalIntegrable _ _

/-- Orthogonality from Green's identity: if the Wronskians vanish at the ends of `[0, a]` and of
`K + i[0, b]` and the eigenvalue pairs differ, the inner product vanishes. -/
theorem p2p_inner_zero_green {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) {t t' : LamePolyType}
    {n m n' m' : ℕ} (hm : m ≤ n) (hm' : m' ≤ n') (a b : ℝ)
    (hW : ∀ z ∈ ({0, (a : ℂ), (Real.compEllIntKm (k ^ 2) : ℂ),
        (Real.compEllIntKm (k ^ 2) : ℂ) + I * b} : Set ℂ),
      deriv (fun z => lamePolyEk t n m z k) z * lamePolyEk t' n' m' z k -
        lamePolyEk t n m z k * deriv (fun z => lamePolyEk t' n' m' z k) z = 0)
    (hD : (lamePolyH t' n' m' k + t'.order n' * (t'.order n' + 1) * k ^ 2 : ℂ) / 2 -
        (lamePolyH t n m k + t.order n * (t.order n + 1) * k ^ 2) / 2 ≠ 0 ∨
      ((t'.order n' : ℂ) * (t'.order n' + 1) - t.order n * (t.order n + 1)) * k ^ 2 ≠ 0) :
    lameInner k a b (lameProduct t n m k) (lameProduct t' n' m' k) = 0 := by
  set K := Real.compEllIntKm (k ^ 2) with hKdef
  have hk := p22R1_ofReal_mem hk0 hk1
  have S1 := p2p_lamePolyEk_isLameSolution hk0 hk1 t hm
  have S2 := p2p_lamePolyEk_isLameSolution hk0 hk1 t' hm'
  have rr : ∀ x : ℝ, jacobiRegulark .n (0 + 1 * x) k := fun x => by
    simpa using p2p_regular_real hk0 hk1 x
  have rv : ∀ x : ℝ, jacobiRegulark .n ((K : ℂ) + I * x) k := p2p_regular_vert hk0 hk1
  have G1 := p2p_green_split hk S1 S2 0 1 0 a rr
  have G2 := p2p_green_split hk S1 S2 (K : ℂ) I 0 b rv
  simp only [Complex.ofReal_zero, mul_zero, add_zero, zero_add, one_mul] at G1 G2
  rw [hW _ (by simp), hW _ (by simp), sub_zero] at G1
  rw [hW _ (by simp), hW _ (by simp), sub_zero] at G2
  rw [p2p_inner_split hk0 hk1 hm hm']
  set I0 := ∫ x in (0 : ℝ)..a, lamePolyEk t n m x k * lamePolyEk t' n' m' x k
  set I1 := ∫ x in (0 : ℝ)..a, jacobiSnk x k ^ 2 * (lamePolyEk t n m x k * lamePolyEk t' n' m' x k)
  set J0 := ∫ x in (0 : ℝ)..b, lamePolyEk t n m (K + I * x) k * lamePolyEk t' n' m' (K + I * x) k
  set J1 := ∫ x in (0 : ℝ)..b, jacobiSnk (K + I * x) k ^ 2 *
    (lamePolyEk t n m (K + I * x) k * lamePolyEk t' n' m' (K + I * x) k)
  set Dh : ℂ := (lamePolyH t' n' m' k + t'.order n' * (t'.order n' + 1) * k ^ 2) / 2 -
    (lamePolyH t n m k + t.order n * (t.order n + 1) * k ^ 2) / 2
  set Dl : ℂ := ((t'.order n' : ℂ) * (t'.order n' + 1) - t.order n * (t.order n + 1)) * k ^ 2
  have e1 : Dh * I0 = Dl * I1 := by linear_combination G1
  have e2 : Dh * J0 = Dl * J1 := by
    have : I * (Dh * J0 - Dl * J1) = 0 := by linear_combination G2
    linear_combination (mul_eq_zero.mp this).resolve_left I_ne_zero
  rcases hD with hD | hD
  · exact (mul_eq_zero.mp (show Dh * (I0 * J1 - I1 * J0) = 0 by
      linear_combination J1 * e1 - I1 * e2)).resolve_left hD
  · exact (mul_eq_zero.mp (show Dl * (I0 * J1 - I1 * J0) = 0 by
      linear_combination J0 * e1 - I0 * e2)).resolve_left hD

/-- The reflection signs of Table 29.12.1 about `0` (factor `sn`). -/
def p2p_sgnS (t : LamePolyType) : ℂ := if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then -1 else 1

/-- The reflection signs of Table 29.12.1 about `K` (factor `cn`). -/
def p2p_sgnC (t : LamePolyType) : ℂ := if t = .cE ∨ t = .scE ∨ t = .cdE ∨ t = .scdE then -1 else 1

/-- The reflection signs of Table 29.12.1 about `K + iK'` (factor `dn`). -/
def p2p_sgnD (t : LamePolyType) : ℂ := if t = .dE ∨ t = .sdE ∨ t = .cdE ∨ t = .scdE then -1 else 1

/-- The reflection signs are `±1`. -/
theorem p2p_sgn_cases (t : LamePolyType) :
    (p2p_sgnS t = 1 ∨ p2p_sgnS t = -1) ∧ (p2p_sgnC t = 1 ∨ p2p_sgnC t = -1) ∧
      (p2p_sgnD t = 1 ∨ p2p_sgnD t = -1) := by
  cases t <;> simp [p2p_sgnS, p2p_sgnC, p2p_sgnD]

/-- Reflection symmetries and periods of a Lamé polynomial used for the boundary terms. -/
theorem p2p_lamePolyEk_sym {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) (n m : ℕ) :
    let K : ℂ := Real.compEllIntKm (k ^ 2)
    let K' : ℂ := Real.compEllIntKm (1 - k ^ 2)
    let E := fun z => lamePolyEk t n m z k
    (∀ z, E (0 - z) = p2p_sgnS t * E (0 + z)) ∧ (∀ z, E (K - z) = p2p_sgnC t * E (K + z)) ∧
      (∀ z, E (K + I * K' - z) = p2p_sgnD t * E (K + I * K' + z)) ∧
      (∀ z, E (z + 4 * K) = E z) ∧ (∀ z, E (4 * K - z) = p2p_sgnS t * E (4 * K + z)) ∧
      (∀ z, E (K + I * (2 * K') - z) = p2p_sgnC t * E (K + I * (2 * K') + z)) := by
  intro K K' E
  have par := lamePolyEk_parities hk0 hk1 t n m
  have per := lamePolyEk_periods hk0 hk1 t n m
  have h2i : ∀ w, E (w + I * (2 * K')) = p2p_sgnC t * p2p_sgnD t * E w := fun w => by
    have := p1l_lamePolyEk_transform t n m (z' := w + 2 * I * K') (z := w) (ε := 1) (a := -1)
      (b := -1) (Or.inl rfl) (by rw [(p1l_shifts hk0 hk1 w).2.1.1]; ring)
      (by rw [(p1l_shifts hk0 hk1 w).2.1.2.1]; ring)
      (by rw [(p1l_shifts hk0 hk1 w).2.1.2.2]; ring)
    simp only [E, show w + I * (2 * K') = w + 2 * I * K' by ring, this, p2p_sgnC, p2p_sgnD]
    cases t <;> simp
  have h4 : ∀ z, E (z + 4 * K) = E z := fun z => by
    have h := (per z).1
    by_cases ht : t = .uE ∨ t = .dE ∨ t = .scE
    · have h' := (per (z + 2 * K)).1
      simp only [ht, ite_true] at h h'
      simp only [E]
      rw [show z + 4 * K = z + 2 * K + 2 * K by ring, h', h]
    · simpa [ht] using h
  refine ⟨fun z => by simpa [E, p2p_sgnS] using (par z).1, fun z => (par z).2.1,
    fun z => (par z).2.2, h4, fun z => ?_, fun z => ?_⟩
  · rw [show 4 * K - z = -z + 4 * K by ring, h4, show 4 * K + z = z + 4 * K by ring, h4]
    simpa [E, p2p_sgnS] using (par z).1
  · rw [show K + I * (2 * K') - z = (K - z) + I * (2 * K') by ring, h2i,
      show K + I * (2 * K') + z = (K + z) + I * (2 * K') by ring, h2i]
    have hK : E (K - z) = p2p_sgnC t * E (K + z) := (par z).2.1
    rw [hK]
    ring

/-- The Wronskian of two Lamé polynomials vanishes at a regular point of common reflection
symmetry. -/
theorem p2p_W_zero {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) {t t' : LamePolyType} {n m n' m' : ℕ}
    (hm : m ≤ n) (hm' : m' ≤ n') {p σ : ℂ} (hreg : jacobiRegulark .n p k)
    (hσ : σ = 1 ∨ σ = -1)
    (h1 : ∀ z, lamePolyEk t n m (p - z) k = σ * lamePolyEk t n m (p + z) k)
    (h2 : ∀ z, lamePolyEk t' n' m' (p - z) k = σ * lamePolyEk t' n' m' (p + z) k) :
    deriv (fun z => lamePolyEk t n m z k) p * lamePolyEk t' n' m' p k -
      lamePolyEk t n m p k * deriv (fun z => lamePolyEk t' n' m' z k) p = 0 :=
  p2p_wronskian_sym (E1 := fun z => lamePolyEk t n m z k)
    (E2 := fun z => lamePolyEk t' n' m' z k) hσ h1 h2
    ((p2p_lamePolyEk_isLameSolution hk0 hk1 t hm).differentiableAt _ hreg)
    ((p2p_lamePolyEk_isLameSolution hk0 hk1 t' hm').differentiableAt _ hreg)

/-- Types with the same reflection signs about `0` and `K` and equal orders coincide. -/
lemma p2p_type_eq {t t' : LamePolyType} {n n' : ℕ} (hs : p2p_sgnS t = p2p_sgnS t')
    (hc : p2p_sgnC t = p2p_sgnC t') (hν : t'.order n' = t.order n) : t' = t ∧ n' = n := by
  revert hs hc hν
  cases t <;> cases t' <;> norm_num [p2p_sgnS, p2p_sgnC, LamePolyType.order] <;> omega

/-- The eigenvalue pairs of distinct Lamé polynomials of the same reflection type about `0` and
`K` differ. -/
theorem p2p_eigen_ne {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) {t t' : LamePolyType}
    {n m n' m' : ℕ} (hm : m ≤ n) (hm' : m' ≤ n') (hne : (t, n, m) ≠ (t', n', m'))
    (hs : p2p_sgnS t = p2p_sgnS t') (hc : p2p_sgnC t = p2p_sgnC t') :
    (lamePolyH t' n' m' k + t'.order n' * (t'.order n' + 1) * k ^ 2 : ℂ) / 2 -
        (lamePolyH t n m k + t.order n * (t.order n + 1) * k ^ 2) / 2 ≠ 0 ∨
      ((t'.order n' : ℂ) * (t'.order n' + 1) - t.order n * (t.order n + 1)) * k ^ 2 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hk2 : (k : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hk0.ne')
  have hl : (t'.order n' : ℂ) * (t'.order n' + 1) = t.order n * (t.order n + 1) := by
    have := (mul_eq_zero.mp h2).resolve_right hk2
    linear_combination this
  have hl' : t'.order n' * (t'.order n' + 1) = t.order n * (t.order n + 1) := by
    exact_mod_cast hl
  have hν : t'.order n' = t.order n := by
    rcases lt_trichotomy (t'.order n') (t.order n) with h | h | h
    · exfalso; have : t'.order n' * (t'.order n' + 1) < t.order n * (t.order n + 1) :=
        Nat.mul_lt_mul'' h (by omega)
      omega
    · exact h
    · exfalso; have : t.order n * (t.order n + 1) < t'.order n' * (t'.order n' + 1) :=
        Nat.mul_lt_mul'' h (by omega)
      omega
  have htn : t' = t ∧ n' = n := p2p_type_eq hs hc hν
  obtain ⟨rfl, rfl⟩ := htn
  have hH : (lamePolyH t' n' m' k : ℂ) = lamePolyH t' n' m k := by
    linear_combination 2 * h1
  have hH' : lamePolyH t' n' m' k = lamePolyH t' n' m k := by exact_mod_cast hH
  rcases lt_trichotomy m m' with h | h | h
  · exact (p2p_lamePolyH_lt hk0 hk1 t' h hm').ne' hH'
  · exact hne (by rw [h])
  · exact (p2p_lamePolyH_lt hk0 hk1 t' h hm).ne hH'

/-- The product of two distinct signs `±1` is `-1`. -/
theorem p2p_sgn_mul {σ σ' : ℂ} (h : σ = 1 ∨ σ = -1) (h' : σ' = 1 ∨ σ' = -1) (hne : σ ≠ σ') :
    σ * σ' = -1 := by
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl <;> first | (exfalso; exact hne rfl) | ring

/-- If the product of two Lamé polynomials is odd about `c ∈ {0, K}` on the real line, its
integrals over `[0, 4K]` against `1` and `sn²` vanish. -/
theorem p2p_real_integrals_zero {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) {t t' : LamePolyType}
    {n m n' m' : ℕ} (c : ℝ) (hc : c = 0 ∨ c = Real.compEllIntKm (k ^ 2))
    (hodd : ∀ z : ℂ, lamePolyEk t n m (c - z) k * lamePolyEk t' n' m' (c - z) k =
      -(lamePolyEk t n m (c + z) k * lamePolyEk t' n' m' (c + z) k)) :
    (∫ x in (0 : ℝ)..4 * Real.compEllIntKm (k ^ 2),
        lamePolyEk t n m x k * lamePolyEk t' n' m' x k) = 0 ∧
      (∫ x in (0 : ℝ)..4 * Real.compEllIntKm (k ^ 2),
        jacobiSnk x k ^ 2 * (lamePolyEk t n m x k * lamePolyEk t' n' m' x k)) = 0 := by
  set K := Real.compEllIntKm (k ^ 2)
  obtain ⟨-, -, -, p1, -, -⟩ := p2p_lamePolyEk_sym hk0 hk1 t n m
  obtain ⟨-, -, -, p2, -, -⟩ := p2p_lamePolyEk_sym hk0 hk1 t' n' m'
  have sh := p1l_shifts hk0 hk1
  have sper : ∀ z : ℂ, jacobiSnk (z + 4 * K) k = jacobiSnk z k := fun z => by
    rw [show z + 4 * (K : ℂ) = z + 2 * K + 2 * K by ring, (sh _).1.1, (sh _).1.1, neg_neg]
  have ssym : ∀ z : ℂ, jacobiSnk ((c : ℂ) - z) k ^ 2 = jacobiSnk ((c : ℂ) + z) k ^ 2 := fun z => by
    rcases hc with rfl | rfl
    · simp only [Complex.ofReal_zero, zero_sub, zero_add, (sh z).2.2.1.1, neg_sq]
    · rw [(sh z).2.2.2.1.1]
  constructor
  · refine p2p_integral_odd_periodic _ _ c (fun x => ?_) (fun x => ?_)
    · push_cast; exact congrArg₂ (· * ·) (p1 _) (p2 _)
    · push_cast; exact hodd x
  · refine p2p_integral_odd_periodic _ _ c (fun x => ?_) (fun x => ?_)
    · push_cast; rw [sper]; exact congrArg _ (congrArg₂ (· * ·) (p1 _) (p2 _))
    · push_cast; rw [ssym, hodd]; ring

end DLMF.Lame
