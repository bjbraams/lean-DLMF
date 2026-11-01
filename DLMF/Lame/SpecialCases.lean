/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Jacobi
public import DLMF.Lame.Basic
public import DLMF.Mathieu.SpectralExistence
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

/-!
# Lamé functions: special cases and limiting forms (DLMF §29.5)

The eigenvalues and Lamé functions at `k = 0`, their limits as `k → 1⁻`, and the Mathieu limits
as `k → 0⁺`, `ν → ∞` with `k²ν(ν+1) = 4θ` (DLMF §29.5).

## Main definitions

* `IsZeroModulusSolution`: the equation `w'' = -h w` on `ℝ` (Lamé's equation at `k = 0`).
* `zeroModulusEigenfunction`: the eigenfunctions `cos(N(π/2 - x))`, `sin(N(π/2 - x))` at `k = 0`.

## Main results

* `Real.lameAk_zero`, `Real.lameBk_zero`: `a^m_ν(0) = b^m_ν(0) = m²` (DLMF 29.5.1).
* `Real.lameEck_zero_zero`, `Real.lameEck_modulus_zero`, `Real.lameEsk_modulus_zero`:
  `Ec^0_ν(x, 0) = 2^{-1/2}`, `Ec^m_ν(x, 0) = cos(m(π/2 - x))`, `Es^m_ν(x, 0) = sin(m(π/2 - x))`
  (DLMF 29.5.2–29.5.3).
* `Real.tendsto_lameAk_one`, `Real.tendsto_lameBk_one`: the eigenvalue limits DLMF 29.5.4.
* `Real.tendsto_lameEck_div_one`, `Real.tendsto_lameEsk_div_one`,
  `Real.tendsto_lameEck_div_deriv_one`, `Real.tendsto_lameEsk_div_deriv_one`: the limits
  DLMF 29.5.5–29.5.6 of normalized Lamé functions.
* `Real.tendsto_lameEck_mathieuCe`, `Real.tendsto_lameEsk_mathieuSe`: the Mathieu limits
  DLMF 29.5.7.

## Implementation notes

The definitions of `DLMF.Lame.Basic` make sense at `k = 0` (then `K = π/2` and `sn = sin`), so
29.5.1–29.5.3 are statements about the same functions; they are proved by solving
`w'' + h w = 0` explicitly (ODE uniqueness, `ODE.eq_of_linear_ode`). In 29.5.5–29.5.6 the Gauss
function `F` is Mathlib's `ordinaryHypergeometric`; the series converges since `tanh² x < 1`.
The Mathieu functions `ce_m`, `se_m` are those of `DLMF.Mathieu.Basic`.
-/

@[expose] public section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Filter Set
open scoped Real Topology

noncomputable section

namespace DLMF.Lame

/-! ### The case `k = 0` -/

/-- `w'' = -h w` on `ℝ` (Lamé's equation at `k = 0`). -/
def IsZeroModulusSolution (h : ℝ) (w : ℝ → ℝ) : Prop :=
  Differentiable ℝ w ∧ ∀ x, HasDerivAt (deriv w) (-h * w x) x

/-- At `k = 0` Lamé's equation is `w'' + h w = 0`. -/
private lemma isLameSolution_modulus_zero_iff {h ν : ℝ} {w : ℝ → ℝ} :
    Real.IsLameSolution h ν 0 w ↔ IsZeroModulusSolution h w := by
  constructor
  · intro hw
    exact ⟨hw.differentiable, fun x => (hw.hasDerivAt_deriv x).congr_deriv (by simp)⟩
  · intro hw
    exact ⟨hw.1, fun x => (hw.2 x).congr_deriv (by simp)⟩

/-- Uniqueness for `w'' = -h w`: a solution is determined by `w 0` and `w' 0`. -/
private lemma isZeroModulusSolution_unique {h : ℝ} {w g g' : ℝ → ℝ} (hw : IsZeroModulusSolution h w)
    (hg : ∀ t, HasDerivAt g (g' t) t ∧ HasDerivAt g' (-h * g t) t) (h0 : w 0 = g 0)
    (h1 : deriv w 0 = g' 0) : w = g ∧ deriv w = g' := by
  have := ODE.eq_of_linear_ode (p := fun _ => (0 : ℝ)) (q := fun _ => -h) (t₀ := 0)
    (f := w) (f' := deriv w) (g := g) (g' := g') continuous_const continuous_const
    (fun t => ⟨(hw.1 t).hasDerivAt, (hw.2 t).congr_deriv (by simp [smul_eq_mul])⟩)
    (fun t => ⟨(hg t).1, (hg t).2.congr_deriv (by simp [smul_eq_mul])⟩) h0 h1
  exact this

/-- A nonzero solution with `w' 0 = 0` has `w 0 ≠ 0`, and one with `w 0 = 0` has `w' 0 ≠ 0`. -/
private lemma isZeroModulusSolution_init_ne_zero {h : ℝ} {w : ℝ → ℝ} (hw : IsZeroModulusSolution h w) (hne : w ≠ 0) :
    ¬ (w 0 = 0 ∧ deriv w 0 = 0) := by
  rintro ⟨h0, h1⟩
  refine hne (isZeroModulusSolution_unique hw (g := 0) (g' := 0) (fun t => ⟨?_, ?_⟩) h0 h1).1
  · exact hasDerivAt_const t (0 : ℝ)
  · simp

/-- For `h > 0` a solution of `w'' = -h w` is
`w(x) = w(0) cos(√h x) + w'(0)/√h · sin(√h x)`, together with the formula for `w'`. -/
private lemma isZeroModulusSolution_eq_of_pos {h : ℝ} {w : ℝ → ℝ} (hh : 0 < h) (hw : IsZeroModulusSolution h w) (x : ℝ) :
    w x = w 0 * Real.cos (√h * x) + deriv w 0 / √h * Real.sin (√h * x) ∧
      deriv w x = -(w 0 * √h * Real.sin (√h * x)) + deriv w 0 * Real.cos (√h * x) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ h = s ^ 2 :=
    ⟨√h, Real.sqrt_pos.mpr hh, (Real.sq_sqrt hh.le).symm⟩
  rw [Real.sqrt_sq hs.le]
  have := isZeroModulusSolution_unique hw
    (g := fun t => w 0 * Real.cos (s * t) + deriv w 0 / s * Real.sin (s * t))
    (g' := fun t => -(w 0 * s * Real.sin (s * t)) + deriv w 0 * Real.cos (s * t))
    (fun t => by
      have hc := (Real.hasDerivAt_cos (s * t)).comp t ((hasDerivAt_id t).const_mul s)
      have hsn := (Real.hasDerivAt_sin (s * t)).comp t ((hasDerivAt_id t).const_mul s)
      refine ⟨((hc.const_mul (w 0)).add (hsn.const_mul (deriv w 0 / s))).congr_deriv ?_,
        (((hsn.const_mul (w 0 * s)).neg).add (hc.const_mul (deriv w 0))).congr_deriv ?_⟩
      · field_simp
      · field_simp; ring)
    (by simp) (by simp)
  exact ⟨congrFun this.1 x, congrFun this.2 x⟩

/-- For `h = 0` a solution of `w'' = 0` is `w(x) = w(0) + w'(0) x`, with `w' ≡ w'(0)`. -/
private lemma isZeroModulusSolution_zero_eq {w : ℝ → ℝ} (hw : IsZeroModulusSolution 0 w) (x : ℝ) :
    w x = w 0 + deriv w 0 * x ∧ deriv w x = deriv w 0 := by
  have := isZeroModulusSolution_unique hw (g := fun t => w 0 + deriv w 0 * t) (g' := fun _ => deriv w 0)
    (fun t => ⟨by simpa using ((hasDerivAt_id t).const_mul (deriv w 0)).const_add (w 0),
      by simpa using hasDerivAt_const t (deriv w 0)⟩) (by simp) (by simp)
  exact ⟨congrFun this.1 x, congrFun this.2 x⟩

/-- For `h < 0` a solution of `w'' = -h w` is
`w(x) = w(0) cosh(√(-h) x) + w'(0)/√(-h) · sinh(√(-h) x)`, together with the formula for `w'`. -/
private lemma isZeroModulusSolution_eq_of_neg {h : ℝ} {w : ℝ → ℝ} (hh : h < 0) (hw : IsZeroModulusSolution h w) (x : ℝ) :
    w x = w 0 * Real.cosh (√(-h) * x) + deriv w 0 / √(-h) * Real.sinh (√(-h) * x) ∧
      deriv w x = w 0 * √(-h) * Real.sinh (√(-h) * x) + deriv w 0 * Real.cosh (√(-h) * x) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ h = -s ^ 2 :=
    ⟨√(-h), Real.sqrt_pos.mpr (by linarith), by rw [Real.sq_sqrt (by linarith)]; ring⟩
  rw [neg_neg, Real.sqrt_sq hs.le]
  have := isZeroModulusSolution_unique hw
    (g := fun t => w 0 * Real.cosh (s * t) + deriv w 0 / s * Real.sinh (s * t))
    (g' := fun t => w 0 * s * Real.sinh (s * t) + deriv w 0 * Real.cosh (s * t))
    (fun t => by
      have hc := (Real.hasDerivAt_cosh (s * t)).comp t ((hasDerivAt_id t).const_mul s)
      have hsn := (Real.hasDerivAt_sinh (s * t)).comp t ((hasDerivAt_id t).const_mul s)
      refine ⟨((hc.const_mul (w 0)).add (hsn.const_mul (deriv w 0 / s))).congr_deriv ?_,
        ((hsn.const_mul (w 0 * s)).add (hc.const_mul (deriv w 0))).congr_deriv ?_⟩
      · field_simp
      · field_simp)
    (by simp) (by simp)
  exact ⟨congrFun this.1 x, congrFun this.2 x⟩

/-- If `s > 0` and `sin(sπ/2) = 0`, then `s = 2n` for some natural `n > 0`. -/
private lemma exists_eq_two_mul_of_sin_mul_pi_div_two_eq_zero {s : ℝ} (hs : 0 < s) (h : Real.sin (s * (π / 2)) = 0) :
    ∃ n : ℕ, 0 < n ∧ s = 2 * n := by
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
  have hs' : s = 2 * n := by
    have := Real.pi_pos
    field_simp at hn
    nlinarith
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  refine ⟨n.toNat, by omega, ?_⟩
  rw [hs']
  have : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    have := Int.toNat_of_nonneg hn0.le
    exact_mod_cast this
  rw [this]

/-- If `s > 0` and `cos(sπ/2) = 0`, then `s = 2n + 1` for some natural `n`. -/
private lemma exists_eq_two_mul_add_one_of_cos_mul_pi_div_two_eq_zero {s : ℝ} (hs : 0 < s) (h : Real.cos (s * (π / 2)) = 0) :
    ∃ n : ℕ, s = 2 * n + 1 := by
  obtain ⟨n, hn⟩ := Real.cos_eq_zero_iff.mp h
  have hs' : s = 2 * n + 1 := by
    have := Real.pi_pos
    field_simp at hn
    nlinarith
  have hn0 : 0 ≤ n := by
    have : (-1 : ℝ) < n := by linarith
    have : (-1 : ℤ) < n := by exact_mod_cast this
    omega
  refine ⟨n.toNat, ?_⟩
  rw [hs']
  have : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    have := Int.toNat_of_nonneg hn0
    exact_mod_cast this
  rw [this]

/-- The eigenfunction `cos(N(π/2 - x))` (`oddK = false`) or `sin(N(π/2 - x))` at `k = 0`. -/
def zeroModulusEigenfunction (N : ℕ) (oddK : Bool) (x : ℝ) : ℝ :=
  if oddK then Real.sin (N * (π / 2 - x)) else Real.cos (N * (π / 2 - x))

/-- The derivative of `zeroModulusEigenfunction`. -/
def zeroModulusEigenfunctionDeriv (N : ℕ) (oddK : Bool) (x : ℝ) : ℝ :=
  if oddK then -(N * Real.cos (N * (π / 2 - x))) else N * Real.sin (N * (π / 2 - x))

/-- `zeroModulusEigenfunction N oddK` has derivative `zeroModulusEigenfunctionDeriv N oddK`, whose derivative is `-N² zeroModulusEigenfunction`. -/
private lemma hasDerivAt_zeroModulusEigenfunction (N : ℕ) (oddK : Bool) (x : ℝ) :
    HasDerivAt (zeroModulusEigenfunction N oddK) (zeroModulusEigenfunctionDeriv N oddK x) x ∧
      HasDerivAt (zeroModulusEigenfunctionDeriv N oddK) (-(N : ℝ) ^ 2 * zeroModulusEigenfunction N oddK x) x := by
  have hin : HasDerivAt (fun x : ℝ => (N : ℝ) * (π / 2 - x)) (-(N : ℝ)) x := by
    simpa using ((hasDerivAt_id x).const_sub (π / 2)).const_mul (N : ℝ)
  have hc := (Real.hasDerivAt_cos _).comp x hin
  have hs := (Real.hasDerivAt_sin _).comp x hin
  cases oddK
  · refine ⟨?_, ?_⟩
    · simp only [zeroModulusEigenfunctionDeriv, Bool.false_eq_true, ite_false]
      exact hc.congr_deriv (by ring)
    · simp only [zeroModulusEigenfunction, Bool.false_eq_true, ite_false]
      exact (hs.const_mul (N : ℝ)).congr_deriv (by ring)
  · refine ⟨?_, ?_⟩
    · simp only [zeroModulusEigenfunctionDeriv, ite_true]
      exact hs.congr_deriv (by ring)
    · simp only [zeroModulusEigenfunction, ite_true]
      exact (hc.const_mul (N : ℝ)).neg.congr_deriv (by ring)

/-- The derivative of `zeroModulusEigenfunction N oddK` is `zeroModulusEigenfunctionDeriv N oddK`. -/
private lemma deriv_zeroModulusEigenfunction (N : ℕ) (oddK : Bool) : deriv (zeroModulusEigenfunction N oddK) = zeroModulusEigenfunctionDeriv N oddK :=
  funext fun x => (hasDerivAt_zeroModulusEigenfunction N oddK x).1.deriv

/-- `zeroModulusEigenfunction N oddK` solves `w'' + N² w = 0`. -/
private lemma isZeroModulusSolution_zeroModulusEigenfunction (N : ℕ) (oddK : Bool) : IsZeroModulusSolution ((N : ℝ) ^ 2) (zeroModulusEigenfunction N oddK) :=
  ⟨fun x => (hasDerivAt_zeroModulusEigenfunction N oddK x).1.differentiableAt, fun x => by
    rw [deriv_zeroModulusEigenfunction]; exact (hasDerivAt_zeroModulusEigenfunction N oddK x).2.congr_deriv (by ring)⟩

/-- `sin(2q · π/2) = 0`. -/
private lemma sin_two_mul_nat_mul_pi_div_two (q : ℕ) : Real.sin (((2 * q : ℕ) : ℝ) * (π / 2)) = 0 := by
  rw [show ((2 * q : ℕ) : ℝ) * (π / 2) = q * π by push_cast; ring]
  exact Real.sin_nat_mul_pi q

/-- `cos((2q + 1) · π/2) = 0`. -/
private lemma cos_two_mul_nat_add_one_mul_pi_div_two (q : ℕ) : Real.cos (((2 * q + 1 : ℕ) : ℝ) * (π / 2)) = 0 := by
  rw [show ((2 * q + 1 : ℕ) : ℝ) * (π / 2) = q * π + π / 2 by push_cast; ring,
    Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]

/-- At `k = 0` the complete elliptic integral is `K(0) = π/2`. -/
private lemma compEllIntKm_modulus_zero : Real.compEllIntKm ((0 : ℝ) ^ 2) = π / 2 := by
  simp [Real.compEllIntKm_zero]

/-- `zeroModulusEigenfunction (2j + [odd0] + [oddK]) oddK` is an eigenfunction at `k = 0`. -/
private lemma isLameEigenfunction_zeroModulusEigenfunction (ν : ℝ) (odd0 oddK : Bool) (j : ℕ) :
    Real.IsLameEigenfunction (((2 * j + odd0.toNat + oddK.toNat : ℕ) : ℝ) ^ 2) ν 0 odd0 oddK
      (zeroModulusEigenfunction (2 * j + odd0.toNat + oddK.toNat) oddK) := by
  simp only [Real.IsLameEigenfunction, Real.LameBoundary, compEllIntKm_modulus_zero,
    isLameSolution_modulus_zero_iff]
  refine ⟨isZeroModulusSolution_zeroModulusEigenfunction _ _, ?_, ?_⟩
  · rw [deriv_zeroModulusEigenfunction]
    have e1 := sin_two_mul_nat_mul_pi_div_two j
    have e2 := cos_two_mul_nat_add_one_mul_pi_div_two j
    have e3 := sin_two_mul_nat_mul_pi_div_two (j + 1)
    push_cast at e1 e2 e3
    cases odd0 <;> cases oddK <;> simp [zeroModulusEigenfunction, zeroModulusEigenfunctionDeriv]
    · exact Or.inr e1
    · exact Or.inr e2
    · exact e2
    · rw [show (2 * (j : ℝ) + 1 + 1) = 2 * (j + 1) by ring]; exact e3
  · intro h0
    cases oddK
    · have := congrFun h0 (π / 2)
      simp [zeroModulusEigenfunction] at this
    · have := congrFun (deriv_zeroModulusEigenfunction (2 * j + odd0.toNat + true.toNat) true) (π / 2)
      rw [h0] at this
      simp [zeroModulusEigenfunctionDeriv] at this
      have h1 : (0 : ℝ) ≤ odd0.toNat := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      linarith

/-- The `k = 0` spectra: `{(2j + [odd0] + [oddK])² : j ∈ ℕ}`. -/
private lemma lameSpectrum_modulus_zero (ν : ℝ) (odd0 oddK : Bool) :
    Real.lameSpectrum ν 0 odd0 oddK =
      range fun j : ℕ => (((2 * j + odd0.toNat + oddK.toNat : ℕ) : ℝ)) ^ 2 := by
  ext h
  simp only [Real.lameSpectrum, Real.IsLameEigenfunction, Real.LameBoundary, compEllIntKm_modulus_zero,
    isLameSolution_modulus_zero_iff, mem_ofPred_eq, mem_range]
  constructor
  · rintro ⟨w, hw, ⟨hb0, hbK⟩, hne⟩
    have hi := isZeroModulusSolution_init_ne_zero hw hne
    rcases lt_trichotomy h 0 with hh | rfl | hh
    · exfalso
      obtain ⟨e1, e2⟩ := isZeroModulusSolution_eq_of_neg hh hw (π / 2)
      have hμ : 0 < √(-h) := Real.sqrt_pos.mpr (by linarith)
      have hsh : 0 < Real.sinh (√(-h) * (π / 2)) := Real.sinh_pos_iff.mpr (by positivity)
      have hch := Real.cosh_pos (√(-h) * (π / 2))
      cases odd0 <;> cases oddK <;>
        simp only [Bool.false_eq_true, ite_false, ite_true] at hb0 hbK <;>
        simp only [hb0, zero_mul, zero_div, add_zero, zero_add] at e1 e2
      · rw [e2] at hbK
        exact hi ⟨by simpa [hμ.ne', hsh.ne'] using hbK, hb0⟩
      · rw [e1] at hbK
        exact hi ⟨by simpa [hch.ne'] using hbK, hb0⟩
      · rw [e2] at hbK
        exact hi ⟨hb0, by simpa [hch.ne'] using hbK⟩
      · rw [e1] at hbK
        exact hi ⟨hb0, by simpa [hμ.ne', hsh.ne'] using hbK⟩
    · obtain ⟨e1, e2⟩ := isZeroModulusSolution_zero_eq hw (π / 2)
      cases odd0 <;> cases oddK <;>
        simp only [Bool.false_eq_true, ite_false, ite_true] at hb0 hbK <;>
        simp only [hb0, zero_mul, add_zero, zero_add] at e1 e2
      · exact ⟨0, by simp⟩
      · exfalso; rw [e1] at hbK; exact hi ⟨hbK, hb0⟩
      · exfalso; rw [e2] at hbK; exact hi ⟨hb0, hbK⟩
      · exfalso; rw [e1] at hbK
        exact hi ⟨hb0, (mul_eq_zero.mp hbK).resolve_right (by positivity)⟩
    · obtain ⟨e1, e2⟩ := isZeroModulusSolution_eq_of_pos hh hw (π / 2)
      have hs : 0 < √h := Real.sqrt_pos.mpr hh
      have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
      cases odd0 <;> cases oddK <;>
        simp only [Bool.false_eq_true, ite_false, ite_true] at hb0 hbK <;>
        simp only [hb0, zero_mul, zero_div, add_zero, zero_add, neg_zero] at e1 e2
      · rw [e2, neg_eq_zero] at hbK
        have hsin : Real.sin (√h * (π / 2)) = 0 := by
          by_contra hc
          exact hi ⟨by simpa [hs.ne', hc] using hbK, hb0⟩
        obtain ⟨n, -, hn⟩ := exists_eq_two_mul_of_sin_mul_pi_div_two_eq_zero hs hsin
        exact ⟨n, by push_cast [Bool.toNat_false]; rw [← hs2, hn]; ring⟩
      · rw [e1] at hbK
        have hcos : Real.cos (√h * (π / 2)) = 0 := by
          by_contra hc
          exact hi ⟨by simpa [hc] using hbK, hb0⟩
        obtain ⟨n, hn⟩ := exists_eq_two_mul_add_one_of_cos_mul_pi_div_two_eq_zero hs hcos
        exact ⟨n, by push_cast [Bool.toNat_false, Bool.toNat_true]; rw [← hs2, hn]; ring⟩
      · rw [e2] at hbK
        have hcos : Real.cos (√h * (π / 2)) = 0 := by
          by_contra hc
          exact hi ⟨hb0, by simpa [hc] using hbK⟩
        obtain ⟨n, hn⟩ := exists_eq_two_mul_add_one_of_cos_mul_pi_div_two_eq_zero hs hcos
        exact ⟨n, by push_cast [Bool.toNat_false, Bool.toNat_true]; rw [← hs2, hn]; ring⟩
      · rw [e1] at hbK
        have hsin : Real.sin (√h * (π / 2)) = 0 := by
          by_contra hc
          exact hi ⟨hb0, by simpa [hs.ne', hc] using hbK⟩
        obtain ⟨n, hn0, hn⟩ := exists_eq_two_mul_of_sin_mul_pi_div_two_eq_zero hs hsin
        refine ⟨n - 1, ?_⟩
        rw [← hs2, hn, show 2 * (n - 1) + true.toNat + true.toNat = 2 * n by
          simp only [Bool.toNat_true]; omega]
        push_cast; ring
  · rintro ⟨j, rfl⟩
    have := isLameEigenfunction_zeroModulusEigenfunction ν odd0 oddK j
    simp only [Real.IsLameEigenfunction, Real.LameBoundary, compEllIntKm_modulus_zero,
      isLameSolution_modulus_zero_iff] at this
    exact ⟨_, this⟩

/-- For strictly increasing `f : ℕ → ℝ`, `range f ∩ (-∞, f a) = f '' {b < a}`. -/
private lemma range_inter_Iio_of_strictMono {f : ℕ → ℝ} (hf : StrictMono f) (a : ℕ) :
    range f ∩ Iio (f a) = f '' Iio a := by
  ext x
  constructor
  · rintro ⟨⟨b, rfl⟩, hb⟩
    exact ⟨b, hf.lt_iff_lt.mp hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, rfl⟩, hf hb⟩

/-- For strictly increasing `f : ℕ → ℝ`, `range f ∩ (-∞, f a)` is finite with `a` elements. -/
private lemma ncard_range_inter_Iio_of_strictMono {f : ℕ → ℝ} (hf : StrictMono f) (a : ℕ) :
    (range f ∩ Iio (f a)).Finite ∧ (range f ∩ Iio (f a)).ncard = a := by
  rw [range_inter_Iio_of_strictMono hf]
  refine ⟨(Set.finite_Iio a).image f, ?_⟩
  rw [Set.ncard_image_of_injective _ hf.injective, ← Finset.coe_range, Set.ncard_coe_finset,
    Finset.card_range]

/-- The `j`th eigenvalue at `k = 0` is `(2j + [odd0] + [oddK])²`. -/
private lemma lameEigenvalue_modulus_zero (ν : ℝ) (odd0 oddK : Bool) (j : ℕ) :
    Real.lameEigenvalue ν 0 odd0 oddK j = (((2 * j + odd0.toNat + oddK.toNat : ℕ) : ℝ)) ^ 2 := by
  set f : ℕ → ℝ := fun j : ℕ => (((2 * j + odd0.toNat + oddK.toNat : ℕ) : ℝ)) ^ 2 with hf_def
  have hf : StrictMono f := fun a b hab => by
    simp only [hf_def]
    have : ((2 * a + odd0.toNat + oddK.toNat : ℕ) : ℝ) <
        ((2 * b + odd0.toNat + oddK.toNat : ℕ) : ℝ) := by
      exact_mod_cast (by omega)
    exact pow_lt_pow_left₀ this (Nat.cast_nonneg _) two_ne_zero
  have hS := lameSpectrum_modulus_zero ν odd0 oddK
  have hiff : ∀ h, Real.IsNthLameEigenvalue ν 0 odd0 oddK j h ↔ h = f j := by
    intro h
    simp only [Real.IsNthLameEigenvalue, hS]
    constructor
    · rintro ⟨⟨a, rfl⟩, -, hc⟩
      rw [(ncard_range_inter_Iio_of_strictMono hf a).2] at hc
      rw [hc]
    · rintro rfl
      exact ⟨⟨j, rfl⟩, ncard_range_inter_Iio_of_strictMono hf j⟩
  have hex : ∃! h, Real.IsNthLameEigenvalue ν 0 odd0 oddK j h :=
    ⟨f j, (hiff _).mpr rfl, fun y hy => (hiff y).mp hy⟩
  rw [Real.lameEigenvalue, dite_eq_left hex]
  exact (hiff _).mp hex.exists.choose_spec

/-- Two solutions of `w'' = -h w` with the same boundary condition at `0`, the second nonzero,
are proportional. -/
private lemma isZeroModulusSolution_eq_const_mul {h : ℝ} {odd0 : Bool} {w ψ : ℝ → ℝ} (hw : IsZeroModulusSolution h w) (hψ : IsZeroModulusSolution h ψ)
    (hψ0 : ψ ≠ 0) (hbw : if odd0 then w 0 = 0 else deriv w 0 = 0)
    (hbψ : if odd0 then ψ 0 = 0 else deriv ψ 0 = 0) : ∃ c, w = fun x => c * ψ x := by
  have hi := isZeroModulusSolution_init_ne_zero hψ hψ0
  have hg : ∀ c : ℝ, ∀ t, HasDerivAt (fun x => c * ψ x) (c * deriv ψ t) t ∧
      HasDerivAt (fun x => c * deriv ψ x) (-h * (c * ψ t)) t := fun c t =>
    ⟨((hψ.1 t).hasDerivAt).const_mul c, ((hψ.2 t).const_mul c).congr_deriv (by ring)⟩
  cases odd0
  · simp only [Bool.false_eq_true, ite_false] at hbw hbψ
    have hψ1 : ψ 0 ≠ 0 := fun h0 => hi ⟨h0, hbψ⟩
    refine ⟨w 0 / ψ 0, (isZeroModulusSolution_unique hw (hg _) ?_ ?_).1⟩
    · field_simp
    · rw [hbw, hbψ, mul_zero]
  · simp only [ite_true] at hbw hbψ
    have hψ1 : deriv ψ 0 ≠ 0 := fun h0 => hi ⟨hbψ, h0⟩
    refine ⟨deriv w 0 / deriv ψ 0, (isZeroModulusSolution_unique hw (hg _) ?_ ?_).1⟩
    · rw [hbw, hbψ, mul_zero]
    · field_simp

/-- At `k = 0`, `dn(x, 0) = 1`. -/
private lemma jacobiDnm_modulus_zero (x : ℝ) : Real.jacobiDnm x ((0 : ℝ) ^ 2) = 1 := by
  rw [show ((0 : ℝ) ^ 2) = 0 by norm_num]
  exact (jacobi_zero_param x).2.2

/-- At `k = 0` a normalized eigenfunction is the normalized eigenfunction. -/
private lemma lameEigenfunction_modulus_zero_eq {ν : ℝ} {odd0 oddK : Bool} {j : ℕ} {ψ : ℝ → ℝ}
    (hψ : Real.IsNormalizedLameEigenfunction ν 0 odd0 oddK j ψ) :
    Real.lameEigenfunction ν 0 odd0 oddK j = ψ := by
  have key : ∀ w, Real.IsNormalizedLameEigenfunction ν 0 odd0 oddK j w → w = ψ := by
    intro w hw
    obtain ⟨⟨hws, ⟨hw0, hwK⟩, hwne⟩, hwi, hwsg⟩ := hw
    obtain ⟨⟨hψs, ⟨hψ0, hψK⟩, hψne⟩, hψi, hψsg⟩ := hψ
    rw [isLameSolution_modulus_zero_iff] at hws hψs
    obtain ⟨c, rfl⟩ := isZeroModulusSolution_eq_const_mul hws hψs hψne hw0 hψ0
    simp only [jacobiDnm_modulus_zero, one_mul] at hwi hψi
    have hc2 : c ^ 2 = 1 := by
      have : ∫ x in (0 : ℝ)..Real.compEllIntKm ((0 : ℝ) ^ 2), (c * ψ x) ^ 2 =
          c ^ 2 * ∫ x in (0 : ℝ)..Real.compEllIntKm ((0 : ℝ) ^ 2), ψ x ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1; funext x; ring
      rw [this, hψi] at hwi
      have := Real.pi_pos
      nlinarith
    have hcpos : 0 < c := by
      cases oddK
      · simp only [Bool.false_eq_true, ite_false] at hwsg hψsg
        exact pos_of_mul_pos_left hwsg hψsg.le
      · simp only [ite_true] at hwsg hψsg
        rw [deriv_const_mul _ (hψs.1 _)] at hwsg
        exact pos_of_mul_neg_left hwsg hψsg.le
    have hc : c = 1 := by nlinarith
    subst hc
    funext x; ring
  have hex : ∃! w, Real.IsNormalizedLameEigenfunction ν 0 odd0 oddK j w := ⟨ψ, hψ, key⟩
  rw [Real.lameEigenfunction, dite_eq_left hex]
  exact key _ hex.exists.choose_spec

/-- For `N ≠ 0`, `∫₀^{π/2} zeroModulusEigenfunction N oddK (x)² dx = π/4`. -/
private lemma integral_zeroModulusEigenfunction_sq {N : ℕ} (hN : N ≠ 0) (oddK : Bool) :
    ∫ x in (0 : ℝ)..π / 2, zeroModulusEigenfunction N oddK x ^ 2 = π / 4 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hsc : Real.sin (N * (π / 2)) * Real.cos (N * (π / 2)) = 0 := by
    have := Real.sin_two_mul (N * (π / 2))
    rw [show 2 * (N * (π / 2)) = N * π by ring, Real.sin_nat_mul_pi] at this
    linarith
  have hsc' : Real.sin (N * π / 2) * Real.cos (N * π / 2) = 0 := by rw [mul_div_assoc]; exact hsc
  cases oddK
  · simp only [zeroModulusEigenfunction, Bool.false_eq_true, ite_false]
    have := intervalIntegral.integral_comp_sub_mul (fun y => Real.cos y ^ 2) (a := 0)
      (b := π / 2) hN' (N * (π / 2))
    rw [show (fun x : ℝ => Real.cos (N * (π / 2 - x)) ^ 2) =
      fun x => Real.cos (N * (π / 2) - N * x) ^ 2 by funext x; ring_nf, this, integral_cos_sq]
    simp only [mul_zero, sub_zero, sub_self, Real.cos_zero, Real.sin_zero, smul_eq_mul]
    field_simp
    linear_combination 8 * hsc'
  · simp only [zeroModulusEigenfunction, ite_true]
    have := intervalIntegral.integral_comp_sub_mul (fun y => Real.sin y ^ 2) (a := 0)
      (b := π / 2) hN' (N * (π / 2))
    rw [show (fun x : ℝ => Real.sin (N * (π / 2 - x)) ^ 2) =
      fun x => Real.sin (N * (π / 2) - N * x) ^ 2 by funext x; ring_nf, this, integral_sin_sq]
    simp only [mul_zero, sub_zero, sub_self, Real.cos_zero, Real.sin_zero, smul_eq_mul]
    field_simp
    linear_combination (-8) * hsc'

/-- `2 ⌊m/2⌋ + [m odd] = m`. -/
private lemma two_mul_div_two_add_bodd_toNat (m : ℕ) : 2 * (m / 2) + m.bodd.toNat = m := by
  rcases Nat.even_or_odd' m with ⟨q, rfl | rfl⟩
  · simp [Nat.bodd_mul]
  · simp [Nat.bodd_mul]; omega

/-- At `k = 0`, for `N = 2j + [odd0] + [oddK] ≠ 0`, `zeroModulusEigenfunction N oddK` is the `j`th normalized
Lamé eigenfunction of boundary type `(odd0, oddK)`. -/
private lemma isNormalizedLameEigenfunction_zeroModulusEigenfunction (ν : ℝ) (odd0 oddK : Bool) (j : ℕ)
    (hN : 2 * j + odd0.toNat + oddK.toNat ≠ 0) :
    Real.IsNormalizedLameEigenfunction ν 0 odd0 oddK j
      (zeroModulusEigenfunction (2 * j + odd0.toNat + oddK.toNat) oddK) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lameEigenvalue_modulus_zero]; exact isLameEigenfunction_zeroModulusEigenfunction ν odd0 oddK j
  · simp only [jacobiDnm_modulus_zero, one_mul, compEllIntKm_modulus_zero]
    exact integral_zeroModulusEigenfunction_sq hN oddK
  · rw [compEllIntKm_modulus_zero, deriv_zeroModulusEigenfunction]
    have : (0 : ℝ) < ((2 * j + odd0.toNat + oddK.toNat : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hN
    cases oddK
    · simp [zeroModulusEigenfunction]
    · simp [zeroModulusEigenfunctionDeriv]; linarith

/-- At `k = 0` the constant `1/√2` is the normalized Lamé eigenfunction `j = 0` of type
`(even, even)`. -/
private lemma isNormalizedLameEigenfunction_const_modulus_zero (ν : ℝ) :
    Real.IsNormalizedLameEigenfunction ν 0 false false 0 (fun _ => 1 / √2) := by
  have h2 : (0 : ℝ) < √2 := by positivity
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [lameEigenvalue_modulus_zero, isLameSolution_modulus_zero_iff]
    refine ⟨differentiable_const _, fun x => ?_⟩
    simp only [deriv_const']
    simpa using hasDerivAt_const x (0 : ℝ)
  · simp [Real.LameBoundary]
  · intro h0
    have := congrFun h0 0
    simp [h2.ne'] at this
  · simp only [jacobiDnm_modulus_zero, one_mul, compEllIntKm_modulus_zero, intervalIntegral.integral_const, smul_eq_mul]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  · simp [h2]

/-- 29.5.1: `a^m_ν(0) = m²`. Proved: at `k = 0` Lamé's equation is
`w'' + h w = 0` on `[0, π/2]`. -/
@[dlmf 29.5.E1]
theorem Real.lameAk_zero {ν : ℝ} (hν : -1 / 2 ≤ ν) (m : ℕ) : Real.lameAk ν m 0 = m ^ 2 := by
  have _ := hν
  rw [Real.lameAk, lameEigenvalue_modulus_zero, Bool.toNat_false, add_zero, two_mul_div_two_add_bodd_toNat]

/-- 29.5.1: `b^m_ν(0) = m²`, `m ≥ 1`. Proved: at `k = 0` Lamé's equation is
`w'' + h w = 0` on `[0, π/2]`. -/
@[dlmf 29.5.E1]
theorem Real.lameBk_zero {ν : ℝ} (hν : -1 / 2 ≤ ν) {m : ℕ} (hm : 1 ≤ m) :
    Real.lameBk ν m 0 = m ^ 2 := by
  have _ := hν
  rw [Real.lameBk, lameEigenvalue_modulus_zero, Bool.toNat_true]
  congr 2
  rcases Nat.even_or_odd' m with ⟨q, rfl | rfl⟩
  · obtain ⟨q, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp [Nat.bodd_mul]; omega
  · simp [Nat.bodd_mul]

/-- 29.5.2: `Ec^0_ν(x, 0) = 2^{-1/2}`. Proved: at `k = 0` Lamé's equation is
`w'' + h w = 0` on `[0, π/2]`. -/
@[dlmf 29.5.E2]
theorem Real.lameEck_zero_zero {ν : ℝ} (hν : -1 / 2 ≤ ν) (x : ℝ) :
    Real.lameEck ν 0 x 0 = 1 / Real.sqrt 2 := by
  have _ := hν
  rw [Real.lameEck, show (0 : ℕ).bodd = false from rfl, show (0 : ℕ) / 2 = 0 from rfl,
    lameEigenfunction_modulus_zero_eq (isNormalizedLameEigenfunction_const_modulus_zero ν)]

/-- 29.5.3: `Ec^m_ν(x, 0) = cos(m(π/2 - x))`, `m ≥ 1`. Proved: at `k = 0` Lamé's equation is
`w'' + h w = 0` on `[0, π/2]`. -/
@[dlmf 29.5.E3]
theorem Real.lameEck_modulus_zero {ν : ℝ} (hν : -1 / 2 ≤ ν) {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    Real.lameEck ν m x 0 = Real.cos (m * (π / 2 - x)) := by
  have _ := hν
  have hN : 2 * (m / 2) + m.bodd.toNat + false.toNat = m := by
    rw [Bool.toNat_false, add_zero, two_mul_div_two_add_bodd_toNat]
  rw [Real.lameEck, lameEigenfunction_modulus_zero_eq (isNormalizedLameEigenfunction_zeroModulusEigenfunction ν _ _ _ (by omega)), hN]
  simp [zeroModulusEigenfunction]

/-- 29.5.3: `Es^m_ν(x, 0) = sin(m(π/2 - x))`, `m ≥ 1`. Proved: at `k = 0` Lamé's equation is
`w'' + h w = 0` on `[0, π/2]`. -/
@[dlmf 29.5.E3]
theorem Real.lameEsk_modulus_zero {ν : ℝ} (hν : -1 / 2 ≤ ν) {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    Real.lameEsk ν m x 0 = Real.sin (m * (π / 2 - x)) := by
  have _ := hν
  have hN : 2 * ((m - 1) / 2) + (!m.bodd).toNat + true.toNat = m := by
    rcases Nat.even_or_odd' m with ⟨q, rfl | rfl⟩
    · obtain ⟨q, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      simp [Nat.bodd_mul]; omega
    · simp [Nat.bodd_mul]
  rw [Real.lameEsk, lameEigenfunction_modulus_zero_eq (isNormalizedLameEigenfunction_zeroModulusEigenfunction ν _ _ _ (by omega)), hN]
  simp [zeroModulusEigenfunction]

/-- 29.5.4: `lim_{k→1⁻} a^m_ν(k²) = ν(ν+1) - μ²` with `μ = max(ν - m, 0)`. Admitted. -/
@[dlmf 29.5.E4]
theorem Real.tendsto_lameAk_one {ν : ℝ} (hν : -1 / 2 ≤ ν) (m : ℕ) :
    Tendsto (fun k => Real.lameAk ν m k) (𝓝[<] 1) (𝓝 (ν * (ν + 1) - max (ν - m) 0 ^ 2)) := by
  sorry

/-- 29.5.4: `lim_{k→1⁻} b^{m+1}_ν(k²) = ν(ν+1) - μ²` with `μ = max(ν - m, 0)`. Admitted. -/
@[dlmf 29.5.E4]
theorem Real.tendsto_lameBk_one {ν : ℝ} (hν : -1 / 2 ≤ ν) (m : ℕ) :
    Tendsto (fun k => Real.lameBk ν (m + 1) k) (𝓝[<] 1)
      (𝓝 (ν * (ν + 1) - max (ν - m) 0 ^ 2)) := by
  sorry

/-- 29.5.5, `Ec`: for even `m`,
`lim_{k→1⁻} Ec^m_ν(x, k²)/Ec^m_ν(0, k²) = (cosh x)^{-μ} F(½μ - ½ν, ½μ + ½ν + ½; ½; tanh² x)`,
`μ = max(ν - m, 0)`, real `x`. Admitted. -/
@[dlmf 29.5.E5]
theorem Real.tendsto_lameEck_div_one {ν : ℝ} (hν : -1 / 2 ≤ ν) {m : ℕ} (hm : Even m) (x : ℝ) :
    Tendsto (fun k => Real.lameEck ν m x k / Real.lameEck ν m 0 k) (𝓝[<] 1)
      (𝓝 (Real.cosh x ^ (-max (ν - m) 0) *
        ordinaryHypergeometric (max (ν - m) 0 / 2 - ν / 2) (max (ν - m) 0 / 2 + ν / 2 + 1 / 2)
          (1 / 2 : ℝ) (Real.tanh x ^ 2))) := by
  sorry

/-- 29.5.5, `Es`: for even `m`, `lim_{k→1⁻} Es^{m+1}_ν(x, k²)/Es^{m+1}_ν(0, k²)` is the same
limit as in `Real.tendsto_lameEck_div_one`. Admitted. -/
@[dlmf 29.5.E5]
theorem Real.tendsto_lameEsk_div_one {ν : ℝ} (hν : -1 / 2 ≤ ν) {m : ℕ} (hm : Even m) (x : ℝ) :
    Tendsto (fun k => Real.lameEsk ν (m + 1) x k / Real.lameEsk ν (m + 1) 0 k) (𝓝[<] 1)
      (𝓝 (Real.cosh x ^ (-max (ν - m) 0) *
        ordinaryHypergeometric (max (ν - m) 0 / 2 - ν / 2) (max (ν - m) 0 / 2 + ν / 2 + 1 / 2)
          (1 / 2 : ℝ) (Real.tanh x ^ 2))) := by
  sorry

/-- 29.5.6, `Ec`: for odd `m`, `lim_{k→1⁻} Ec^m_ν(x, k²)/(dEc^m_ν/dz)(0, k²) =
tanh x (cosh x)^{-μ} F(½μ - ½ν + ½, ½μ + ½ν + 1; 3/2; tanh² x)`, `μ = max(ν - m, 0)`.
Admitted. -/
@[dlmf 29.5.E6]
theorem Real.tendsto_lameEck_div_deriv_one {ν : ℝ} (hν : -1 / 2 ≤ ν) {m : ℕ} (hm : Odd m)
    (x : ℝ) :
    Tendsto (fun k => Real.lameEck ν m x k / deriv (fun z => Real.lameEck ν m z k) 0) (𝓝[<] 1)
      (𝓝 (Real.tanh x * Real.cosh x ^ (-max (ν - m) 0) *
        ordinaryHypergeometric (max (ν - m) 0 / 2 - ν / 2 + 1 / 2) (max (ν - m) 0 / 2 + ν / 2 + 1)
          (3 / 2 : ℝ) (Real.tanh x ^ 2))) := by
  sorry

/-- 29.5.6, `Es`: for odd `m`, `lim_{k→1⁻} Es^{m+1}_ν(x, k²)/(dEs^{m+1}_ν/dz)(0, k²)` is the
same limit as in `Real.tendsto_lameEck_div_deriv_one`. Admitted. -/
@[dlmf 29.5.E6]
theorem Real.tendsto_lameEsk_div_deriv_one {ν : ℝ} (hν : -1 / 2 ≤ ν) {m : ℕ} (hm : Odd m)
    (x : ℝ) :
    Tendsto (fun k => Real.lameEsk ν (m + 1) x k / deriv (fun z => Real.lameEsk ν (m + 1) z k) 0)
      (𝓝[<] 1)
      (𝓝 (Real.tanh x * Real.cosh x ^ (-max (ν - m) 0) *
        ordinaryHypergeometric (max (ν - m) 0 / 2 - ν / 2 + 1 / 2) (max (ν - m) 0 / 2 + ν / 2 + 1)
          (3 / 2 : ℝ) (Real.tanh x ^ 2))) := by
  sorry

/-- 29.5.7, `Ec`: if `k → 0⁺` and `ν → ∞` with `k²ν(ν+1) = 4θ` (`θ > 0`), then
`Ec^m_ν(x, k²) → ce_m(π/2 - x, θ)` (Mathieu function, §28.2(vi)), real `x`. Stated along
sequences `(νⱼ, kⱼ)`. Admitted. -/
@[dlmf 29.5.E7]
theorem Real.tendsto_lameEck_mathieuCe {θ : ℝ} (hθ : 0 < θ) (m : ℕ) (x : ℝ) {ν k : ℕ → ℝ}
    (hν : Tendsto ν atTop atTop) (hk : Tendsto k atTop (𝓝[>] 0))
    (hνk : ∀ j, k j ^ 2 * (ν j * (ν j + 1)) = 4 * θ) :
    Tendsto (fun j => (Real.lameEck (ν j) m x (k j) : ℂ)) atTop
      (𝓝 (DLMF.Mathieu.mathieuCe m (π / 2 - x) θ)) := by
  sorry

/-- 29.5.7, `Es`: under the same limit, `Es^m_ν(x, k²) → se_m(π/2 - x, θ)`, `m ≥ 1`.
Admitted. -/
@[dlmf 29.5.E7]
theorem Real.tendsto_lameEsk_mathieuSe {θ : ℝ} (hθ : 0 < θ) {m : ℕ} (hm : 1 ≤ m) (x : ℝ)
    {ν k : ℕ → ℝ} (hν : Tendsto ν atTop atTop) (hk : Tendsto k atTop (𝓝[>] 0))
    (hνk : ∀ j, k j ^ 2 * (ν j * (ν j + 1)) = 4 * θ) :
    Tendsto (fun j => (Real.lameEsk (ν j) m x (k j) : ℂ)) atTop
      (𝓝 (DLMF.Mathieu.mathieuSe m (π / 2 - x) θ)) := by
  sorry

end DLMF.Lame
