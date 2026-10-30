/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Framework

/-!
# Generalized Airy equations and normalizations, DLMF §9.13(i)

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent
open scoped Real Topology
namespace DLMF.Airy

/-- The fractional Bessel order p=1/(n+2). -/
@[dlmf 9.13.E3]
def generalizedAiryOrder (n : ℕ) : ℝ := 1 / (n + 2 : ℝ)
/-- The generalized Airy argument. -/
@[dlmf 9.13.E3]
def generalizedAiryZeta (n : ℕ) (z : ℂ) : ℂ := 2 / (n + 2 : ℂ) * z ^ (((n : ℂ) + 2) / 2)
/-- The even-at-zero generalized fundamental function. -/
def generalizedAiryF (n : ℕ) (z : ℂ) : ℂ :=
  regularizedHGFun ∅ {1 - (generalizedAiryOrder n : ℂ)} (z ^ (n + 2) / (n + 2 : ℂ) ^ 2)
/-- The odd-at-zero generalized fundamental function, including its factor z. -/
def generalizedAiryG (n : ℕ) (z : ℂ) : ℂ :=
  z * regularizedHGFun ∅ {1 + (generalizedAiryOrder n : ℂ)} (z ^ (n + 2) / (n + 2 : ℂ) ^ 2)
/-- Swanson–Headley's entire generalized A_n. -/
def generalizedAiryA (n : ℕ) (z : ℂ) : ℂ :=
  let p : ℂ := generalizedAiryOrder n
  p ^ (1 - p) * generalizedAiryF n z - p ^ (p + 1) * generalizedAiryG n z
/-- Swanson–Headley's entire generalized B_n. -/
def generalizedAiryB (n : ℕ) (z : ℂ) : ℂ :=
  let p : ℂ := generalizedAiryOrder n
  p ^ (-1 / 2 : ℂ) * (p ^ (1 - p) * generalizedAiryF n z + p ^ (p + 1) * generalizedAiryG n z)
/-- The scaled independent variable t in Olver's normalization. -/
@[dlmf 9.13.E14]
def olverAiryVariable (m : ℕ) (z : ℂ) : ℂ := ((m : ℂ) / 2) ^ (-2 / (m : ℂ)) * z
/-- Olver's U_m (even m) or V_m (odd m), with one entire formula. -/
def olverAiryU (m : ℕ) (t : ℂ) : ℂ :=
  (2 * π : ℂ) ^ (1 / 2 : ℂ) * ((m : ℂ) / 2) ^ (((m : ℂ) - 1) / m) / sin (π / m) *
    generalizedAiryA (m - 2) (((m : ℂ) / 2) ^ (2 / (m : ℂ)) * t)
/-- The separately normalized second solution; for odd m its bar is not complex conjugation. -/
def olverAiryVBar (m : ℕ) (t : ℂ) : ℂ :=
  (π : ℂ) ^ (1 / 2 : ℂ) * ((m : ℂ) / 2) ^ (((m : ℂ) - 2) / (2 * m)) / sin (π / m) *
    generalizedAiryB (m - 2) (((m : ℂ) / 2) ^ (2 / (m : ℂ)) * t)
/-- Smirnov's normalized first solution on the positive real axis. -/
@[dlmf 9.13.E20]
def smirnovAiryU1 (x α : ℝ) : ℂ :=
  ((α + 2 : ℝ) : ℂ) ^ (-1 / ((α : ℂ) + 2)) * Gamma (((α : ℂ) + 1) / (α + 2)) *
    (x : ℂ) ^ (1 / 2 : ℂ) * besselJ (-1 / ((α : ℂ) + 2))
      (2 / ((α : ℂ) + 2) * (x : ℂ) ^ (((α : ℂ) + 2) / 2))
/-- Smirnov's normalized second solution on the positive real axis. -/
@[dlmf 9.13.E21]
def smirnovAiryU2 (x α : ℝ) : ℂ :=
  ((α + 2 : ℝ) : ℂ) ^ (1 / ((α : ℂ) + 2)) * Gamma (((α : ℂ) + 3) / (α + 2)) *
    (x : ℂ) ^ (1 / 2 : ℂ) * besselJ (1 / ((α : ℂ) + 2))
      (2 / ((α : ℂ) + 2) * (x : ℂ) ^ (((α : ℂ) + 2) / 2))
/-- The normalized oscillatory W_m, specified by its two entire initial-data solutions. -/
def olverAiryW (m : ℕ) (t : ℂ) : ℂ :=
  let p : ℂ := (m : ℂ)⁻¹
  let z := ((m : ℂ) / 2) ^ (2 * p) * t
  let F := Gamma (1 - p) * regularizedHGFun ∅ {1 - p} (-z ^ m / (m : ℂ) ^ 2)
  let G := z * Gamma (1 + p) * regularizedHGFun ∅ {1 + p} (-z ^ m / (m : ℂ) ^ 2)
  (2 : ℂ) ^ (((m : ℂ) + 2) / (2 * m)) / (2 * (π : ℂ) ^ (1 / 2 : ℂ)) *
    (Gamma p * F + Gamma (-p) / (m : ℂ) ^ (2 * p) * G)

/-- All generalized Airy solutions are entire, DLMF §9.13(i). -/
theorem generalizedAiryA_entire (n : ℕ) :
    Differentiable ℂ (generalizedAiryA n) := by
  have hF : Differentiable ℂ (generalizedAiryF n) := by
    intro z
    exact ((DLMF.Bessel.hasDerivAt_regularized0F1 _ _).comp z
      ((hasDerivAt_pow (n + 2) z).div_const _)).differentiableAt
  have hG : Differentiable ℂ (generalizedAiryG n) := by
    intro z
    exact ((hasDerivAt_id z).mul ((DLMF.Bessel.hasDerivAt_regularized0F1 _ _).comp z
      ((hasDerivAt_pow (n + 2) z).div_const _))).differentiableAt
  unfold generalizedAiryA
  fun_prop

/-- Derivative of `₀F̃₁(;c; s z^{n+2}/(n+2)²)`. -/
theorem hasDerivAt_reg0F1_pow (n : ℕ) (s : ℂ) {c c' : ℂ} (hc : c + 1 = c') (z : ℂ) :
    HasDerivAt (fun z : ℂ => regularizedHGFun (∅ : Multiset ℂ) {c} (s * z ^ (n + 2) / ((n : ℂ) + 2) ^ 2))
      (s * z ^ (n + 1) / ((n : ℂ) + 2) *
        regularizedHGFun (∅ : Multiset ℂ) {c'} (s * z ^ (n + 2) / ((n : ℂ) + 2) ^ 2)) z := by
  subst hc
  have hn : (n : ℂ) + 2 ≠ 0 := by norm_cast
  have h := (DLMF.Bessel.hasDerivAt_regularized0F1 c (s * z ^ (n + 2) / ((n : ℂ) + 2) ^ 2)).comp z
    (((hasDerivAt_pow (n + 2) z).const_mul s).div_const (((n : ℂ) + 2) ^ 2))
  refine h.congr_deriv ?_
  push_cast
  field_simp

/-- A solution pair of `w'' = s z^n w`. -/
def IsGenAirySol (n : ℕ) (s : ℂ) (w w' : ℂ → ℂ) : Prop :=
  ∀ z, HasDerivAt w (w' z) z ∧ HasDerivAt w' (s * z ^ n * w z) z

/-- Sum of two solutions. -/
theorem IsGenAirySol.add {n : ℕ} {s : ℂ} {f f' g g' : ℂ → ℂ} (hf : IsGenAirySol n s f f')
    (hg : IsGenAirySol n s g g') :
    IsGenAirySol n s (fun z => f z + g z) (fun z => f' z + g' z) := fun z =>
  ⟨(hf z).1.add (hg z).1, ((hf z).2.add (hg z).2).congr_deriv (by ring)⟩

/-- Constant multiple of a solution. -/
theorem IsGenAirySol.const_mul {n : ℕ} {s : ℂ} (a : ℂ) {f f' : ℂ → ℂ} (hf : IsGenAirySol n s f f') :
    IsGenAirySol n s (fun z => a * f z) (fun z => a * f' z) := fun z =>
  ⟨(hf z).1.const_mul a, ((hf z).2.const_mul a).congr_deriv (by ring)⟩

/-- The even fundamental solution `₀F̃₁(;1-p; s z^{n+2}/(n+2)²)`. -/
theorem isGenAirySol_F (n : ℕ) (s : ℂ) :
    IsGenAirySol n s
      (fun z => regularizedHGFun ∅ {1 - (generalizedAiryOrder n : ℂ)} (s * z ^ (n + 2) / ((n : ℂ) + 2) ^ 2))
      (fun z => s * z ^ (n + 1) / ((n : ℂ) + 2) *
        regularizedHGFun ∅ {2 - (generalizedAiryOrder n : ℂ)} (s * z ^ (n + 2) / ((n : ℂ) + 2) ^ 2)) := by
  intro z
  have hn : (n : ℂ) + 2 ≠ 0 := by norm_cast
  have hp : (generalizedAiryOrder n : ℂ) = 1 / ((n : ℂ) + 2) := by
    simp [generalizedAiryOrder]
  refine ⟨hasDerivAt_reg0F1_pow n s (by ring) z, ?_⟩
  have h1 := hasDerivAt_reg0F1_pow n s (c := 2 - (generalizedAiryOrder n : ℂ))
    (c' := 3 - (generalizedAiryOrder n : ℂ)) (by ring) z
  have h2 := ((hasDerivAt_pow (n + 1) z).const_mul s).div_const ((n : ℂ) + 2)
  refine (h2.mul h1).congr_deriv ?_
  have hc := reg0F1_contiguous' (c := 1 - (generalizedAiryOrder n : ℂ))
    (c₁ := 2 - (generalizedAiryOrder n : ℂ)) (c₂ := 3 - (generalizedAiryOrder n : ℂ)) (by ring)
    (by ring) (s * z ^ (n + 2) / ((n : ℂ) + 2) ^ 2)
  simp only [hc]
  generalize regularizedHGFun ∅ {2 - (generalizedAiryOrder n : ℂ)} (s * z ^ (n + 2) / ((n : ℂ) + 2) ^ 2) = A
  generalize regularizedHGFun ∅ {3 - (generalizedAiryOrder n : ℂ)} (s * z ^ (n + 2) / ((n : ℂ) + 2) ^ 2) = B
  rw [hp]
  push_cast
  field_simp
  ring

/-- The odd fundamental solution `z ₀F̃₁(;1+p; s z^{n+2}/(n+2)²)`. -/
theorem isGenAirySol_G (n : ℕ) (s : ℂ) :
    IsGenAirySol n s
      (fun z => z * regularizedHGFun ∅ {1 + (generalizedAiryOrder n : ℂ)} (s * z ^ (n + 2) / ((n : ℂ) + 2) ^ 2))
      (fun z => regularizedHGFun ∅ {1 + (generalizedAiryOrder n : ℂ)} (s * z ^ (n + 2) / ((n : ℂ) + 2) ^ 2) +
        s * z ^ (n + 2) / ((n : ℂ) + 2) *
        regularizedHGFun ∅ {2 + (generalizedAiryOrder n : ℂ)} (s * z ^ (n + 2) / ((n : ℂ) + 2) ^ 2)) := by
  intro z
  have hn : (n : ℂ) + 2 ≠ 0 := by norm_cast
  have hp : (generalizedAiryOrder n : ℂ) = 1 / ((n : ℂ) + 2) := by
    simp [generalizedAiryOrder]
  have h1 := hasDerivAt_reg0F1_pow n s (c := 1 + (generalizedAiryOrder n : ℂ))
    (c' := 2 + (generalizedAiryOrder n : ℂ)) (by ring) z
  have h2 := hasDerivAt_reg0F1_pow n s (c := 2 + (generalizedAiryOrder n : ℂ))
    (c' := 3 + (generalizedAiryOrder n : ℂ)) (by ring) z
  refine ⟨((hasDerivAt_id z).mul h1).congr_deriv (by simp only [id]; ring), ?_⟩
  have h3 := ((hasDerivAt_pow (n + 2) z).const_mul s).div_const ((n : ℂ) + 2)
  refine (h1.add (h3.mul h2)).congr_deriv ?_
  have hc := reg0F1_contiguous' (c := 1 + (generalizedAiryOrder n : ℂ))
    (c₁ := 2 + (generalizedAiryOrder n : ℂ)) (c₂ := 3 + (generalizedAiryOrder n : ℂ)) (by ring)
    (by ring) (s * z ^ (n + 2) / ((n : ℂ) + 2) ^ 2)
  simp only [hc]
  generalize regularizedHGFun ∅ {2 + (generalizedAiryOrder n : ℂ)} (s * z ^ (n + 2) / ((n : ℂ) + 2) ^ 2) = A
  generalize regularizedHGFun ∅ {3 + (generalizedAiryOrder n : ℂ)} (s * z ^ (n + 2) / ((n : ℂ) + 2) ^ 2) = B
  rw [hp]
  push_cast
  field_simp
  ring

/-- Transport of a solution along pointwise equalities. -/
theorem IsGenAirySol.congr {n : ℕ} {s : ℂ} {f f' g g' : ℂ → ℂ} (hf : IsGenAirySol n s f f')
    (h1 : ∀ z, f z = g z) (h2 : ∀ z, f' z = g' z) : IsGenAirySol n s g g' := by
  rw [← funext h1, ← funext h2]; exact hf

/-- The derivative of `F_n`. -/
def generalizedAiryFDeriv (n : ℕ) (z : ℂ) : ℂ :=
  z ^ (n + 1) / ((n : ℂ) + 2) *
    regularizedHGFun ∅ {2 - (generalizedAiryOrder n : ℂ)} (z ^ (n + 2) / ((n : ℂ) + 2) ^ 2)

/-- The derivative of `G_n`. -/
def generalizedAiryGDeriv (n : ℕ) (z : ℂ) : ℂ :=
  regularizedHGFun ∅ {1 + (generalizedAiryOrder n : ℂ)} (z ^ (n + 2) / ((n : ℂ) + 2) ^ 2) +
    z ^ (n + 2) / ((n : ℂ) + 2) *
      regularizedHGFun ∅ {2 + (generalizedAiryOrder n : ℂ)} (z ^ (n + 2) / ((n : ℂ) + 2) ^ 2)

/-- `F_n` solves `w = z^n w`. -/
theorem isGenAirySol_generalizedAiryF (n : ℕ) :
    IsGenAirySol n 1 (generalizedAiryF n) (generalizedAiryFDeriv n) :=
  (isGenAirySol_F n 1).congr (fun z => by simp [generalizedAiryF])
    (fun z => by simp [generalizedAiryFDeriv])

/-- `G_n` solves `w = z^n w`. -/
theorem isGenAirySol_generalizedAiryG (n : ℕ) :
    IsGenAirySol n 1 (generalizedAiryG n) (generalizedAiryGDeriv n) :=
  (isGenAirySol_G n 1).congr (fun z => by simp [generalizedAiryG])
    (fun z => by simp [generalizedAiryGDeriv])

/-- The derivative of `A_n`. -/
def generalizedAiryADeriv (n : ℕ) (z : ℂ) : ℂ :=
  (generalizedAiryOrder n : ℂ) ^ (1 - (generalizedAiryOrder n : ℂ)) * generalizedAiryFDeriv n z -
    (generalizedAiryOrder n : ℂ) ^ ((generalizedAiryOrder n : ℂ) + 1) * generalizedAiryGDeriv n z

/-- The derivative of `B_n`. -/
def generalizedAiryBDeriv (n : ℕ) (z : ℂ) : ℂ :=
  (generalizedAiryOrder n : ℂ) ^ (-1 / 2 : ℂ) *
    ((generalizedAiryOrder n : ℂ) ^ (1 - (generalizedAiryOrder n : ℂ)) * generalizedAiryFDeriv n z +
      (generalizedAiryOrder n : ℂ) ^ ((generalizedAiryOrder n : ℂ) + 1) * generalizedAiryGDeriv n z)

/-- `A_n` solves `w = z^n w`. -/
theorem isGenAirySol_generalizedAiryA (n : ℕ) :
    IsGenAirySol n 1 (generalizedAiryA n) (generalizedAiryADeriv n) := by
  set p : ℂ := (generalizedAiryOrder n : ℂ)
  refine (((isGenAirySol_generalizedAiryF n).const_mul (p ^ (1 - p))).add
    ((isGenAirySol_generalizedAiryG n).const_mul (-p ^ (p + 1)))).congr ?_ ?_
  · intro z; simp only [generalizedAiryA, p]; ring
  · intro z; simp only [generalizedAiryADeriv, p]; ring

/-- `B_n` solves `w = z^n w`. -/
theorem isGenAirySol_generalizedAiryB (n : ℕ) :
    IsGenAirySol n 1 (generalizedAiryB n) (generalizedAiryBDeriv n) := by
  set p : ℂ := (generalizedAiryOrder n : ℂ)
  refine ((((isGenAirySol_generalizedAiryF n).const_mul (p ^ (1 - p))).add
    ((isGenAirySol_generalizedAiryG n).const_mul (p ^ (p + 1)))).const_mul
      (p ^ (-1 / 2 : ℂ))).congr ?_ ?_
  · intro z; simp only [generalizedAiryB, p]
  · intro z; simp only [generalizedAiryBDeriv, p]

/-- The derivative of `A_n`. -/
theorem deriv_generalizedAiryA (n : ℕ) : deriv (generalizedAiryA n) = generalizedAiryADeriv n :=
  funext fun z => ((isGenAirySol_generalizedAiryA n) z).1.deriv

/-- The derivative of `B_n`. -/
theorem deriv_generalizedAiryB (n : ℕ) : deriv (generalizedAiryB n) = generalizedAiryBDeriv n :=
  funext fun z => ((isGenAirySol_generalizedAiryB n) z).1.deriv

/-- `A_n` solves the generalized Airy equation `w'' = zⁿ w` (DLMF 9.13.1). -/
@[dlmf 9.13.E1]
theorem generalizedAiryA_ode {n : ℕ} (z : ℂ) :
    deriv (deriv (generalizedAiryA n)) z = z ^ n * generalizedAiryA n z := by
  rw [deriv_generalizedAiryA, ((isGenAirySol_generalizedAiryA n) z).2.deriv, one_mul]

/-- All generalized Airy solutions are entire, DLMF §9.13(i). -/
theorem generalizedAiryB_entire (n : ℕ) :
    Differentiable ℂ (generalizedAiryB n) := by
  have hF : Differentiable ℂ (generalizedAiryF n) := by
    intro z
    exact ((DLMF.Bessel.hasDerivAt_regularized0F1 _ _).comp z
      ((hasDerivAt_pow (n + 2) z).div_const _)).differentiableAt
  have hG : Differentiable ℂ (generalizedAiryG n) := by
    intro z
    exact ((hasDerivAt_id z).mul ((DLMF.Bessel.hasDerivAt_regularized0F1 _ _).comp z
      ((hasDerivAt_pow (n + 2) z).div_const _))).differentiableAt
  unfold generalizedAiryB
  fun_prop

/-- `B_n` solves the generalized Airy equation `w'' = zⁿ w` (DLMF 9.13.1). -/
@[dlmf 9.13.E1]
theorem generalizedAiryB_ode {n : ℕ} (z : ℂ) :
    deriv (deriv (generalizedAiryB n)) z = z ^ n * generalizedAiryB n z := by
  rw [deriv_generalizedAiryB, ((isGenAirySol_generalizedAiryB n) z).2.deriv, one_mul]

/-! ### Bessel forms on the real axis -/

/-- The order `p = 1/(n+2)` is positive. -/
theorem generalizedAiryOrder_pos (n : ℕ) : 0 < generalizedAiryOrder n := by
  unfold generalizedAiryOrder; positivity

/-- The order `p = 1/(n+2)` is less than one. -/
theorem generalizedAiryOrder_lt_one (n : ℕ) : generalizedAiryOrder n < 1 := by
  unfold generalizedAiryOrder; rw [div_lt_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]

/-- Complex powers of the positive real order `p` are real. -/
theorem generalizedAiryOrder_cpow (n : ℕ) (a : ℝ) :
    (generalizedAiryOrder n : ℂ) ^ (a : ℂ) = ((generalizedAiryOrder n ^ a : ℝ) : ℂ) :=
  (ofReal_cpow (generalizedAiryOrder_pos n).le a).symm

/-- On the positive axis, `ζ = 2p x^{1/(2p)}` is real. -/
theorem generalizedAiryZeta_ofReal (n : ℕ) {x : ℝ} (hx : 0 < x) :
    generalizedAiryZeta n x =
      ((2 * generalizedAiryOrder n * x ^ (((n : ℝ) + 2) / 2)) : ℝ) := by
  rw [generalizedAiryZeta, show ((n : ℂ) + 2) / 2 = (((n : ℝ) + 2) / 2 : ℝ) by push_cast; ring,
    ← ofReal_cpow hx.le]
  simp only [generalizedAiryOrder]; push_cast; ring

/-- `ζ²/4 = x^{n+2}/(n+2)²` on the positive axis. -/
theorem generalizedAiryZeta_sq_div_four (n : ℕ) {x : ℝ} (hx : 0 < x) :
    generalizedAiryZeta n x ^ 2 / 4 = (x : ℂ) ^ (n + 2) / ((n : ℂ) + 2) ^ 2 := by
  rw [generalizedAiryZeta_ofReal n hx]
  have h : (2 * generalizedAiryOrder n * x ^ (((n : ℝ) + 2) / 2)) ^ 2 / 4 =
      x ^ (n + 2) / ((n : ℝ) + 2) ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast (x ^ _), ← Real.rpow_mul hx.le, generalizedAiryOrder,
      show ((n : ℝ) + 2) / 2 * ((2 : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    have : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp; ring
  exact_mod_cast h

/-- `(ζ/2)^{±p} = p^{±p} x^{±1/2}` on the positive axis. -/
theorem generalizedAiryZeta_half_cpow (n : ℕ) {x : ℝ} (hx : 0 < x) (s : ℝ) :
    (generalizedAiryZeta n x / 2) ^ ((s * generalizedAiryOrder n : ℝ) : ℂ) =
      ((generalizedAiryOrder n ^ (s * generalizedAiryOrder n) * x ^ (s / 2) : ℝ) : ℂ) := by
  have hp := generalizedAiryOrder_pos n
  rw [generalizedAiryZeta_ofReal n hx,
    show ((2 * generalizedAiryOrder n * x ^ (((n : ℝ) + 2) / 2) : ℝ) : ℂ) / 2 =
      ((generalizedAiryOrder n * x ^ (((n : ℝ) + 2) / 2) : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by positivity), Real.mul_rpow hp.le (by positivity), ← Real.rpow_mul hx.le]
  congr 3
  simp only [generalizedAiryOrder]
  have : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp

/-- `I_p(ζ) = p^p x^{1/2} ₀F̃₁(;1+p;x^{n+2}/(n+2)²)` for `x > 0`. -/
theorem besselI_generalizedAiryZeta (n : ℕ) {x : ℝ} (hx : 0 < x) :
    DLMF.Bessel.besselI (generalizedAiryOrder n : ℂ) (generalizedAiryZeta n x) =
      ((generalizedAiryOrder n ^ generalizedAiryOrder n * x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        regularizedHGFun ∅ {1 + (generalizedAiryOrder n : ℂ)}
          ((x : ℂ) ^ (n + 2) / ((n : ℂ) + 2) ^ 2) := by
  have h := generalizedAiryZeta_half_cpow n hx 1
  simp only [one_mul] at h
  rw [DLMF.Bessel.besselI, h, generalizedAiryZeta_sq_div_four n hx, add_comm]

/-- `I_{-p}(ζ) = p^{-p} x^{-1/2} ₀F̃₁(;1-p;x^{n+2}/(n+2)²)` for `x > 0`. -/
theorem besselI_neg_generalizedAiryZeta (n : ℕ) {x : ℝ} (hx : 0 < x) :
    DLMF.Bessel.besselI (-(generalizedAiryOrder n : ℂ)) (generalizedAiryZeta n x) =
      ((generalizedAiryOrder n ^ (-generalizedAiryOrder n) * x ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        regularizedHGFun ∅ {1 - (generalizedAiryOrder n : ℂ)}
          ((x : ℂ) ^ (n + 2) / ((n : ℂ) + 2) ^ 2) := by
  have h := generalizedAiryZeta_half_cpow n hx (-1)
  simp only [neg_one_mul, ofReal_neg] at h
  rw [DLMF.Bessel.besselI, h, generalizedAiryZeta_sq_div_four n hx, neg_add_eq_sub]

/-- `J_p(ζ) = p^p x^{1/2} ₀F̃₁(;1+p;-x^{n+2}/(n+2)²)` for `x > 0`. -/
theorem besselJ_generalizedAiryZeta (n : ℕ) {x : ℝ} (hx : 0 < x) :
    besselJ (generalizedAiryOrder n : ℂ) (generalizedAiryZeta n x) =
      ((generalizedAiryOrder n ^ generalizedAiryOrder n * x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        regularizedHGFun ∅ {1 + (generalizedAiryOrder n : ℂ)}
          (-((x : ℂ) ^ (n + 2) / ((n : ℂ) + 2) ^ 2)) := by
  have h := generalizedAiryZeta_half_cpow n hx 1
  simp only [one_mul] at h
  rw [DLMF.Bessel.besselJ_eq_regularized, h, generalizedAiryZeta_sq_div_four n hx, add_comm]

/-- `J_{-p}(ζ) = p^{-p} x^{-1/2} ₀F̃₁(;1-p;-x^{n+2}/(n+2)²)` for `x > 0`. -/
theorem besselJ_neg_generalizedAiryZeta (n : ℕ) {x : ℝ} (hx : 0 < x) :
    besselJ (-(generalizedAiryOrder n : ℂ)) (generalizedAiryZeta n x) =
      ((generalizedAiryOrder n ^ (-generalizedAiryOrder n) * x ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        regularizedHGFun ∅ {1 - (generalizedAiryOrder n : ℂ)}
          (-((x : ℂ) ^ (n + 2) / ((n : ℂ) + 2) ^ 2)) := by
  have h := generalizedAiryZeta_half_cpow n hx (-1)
  simp only [neg_one_mul, ofReal_neg] at h
  rw [DLMF.Bessel.besselJ_eq_regularized, h, generalizedAiryZeta_sq_div_four n hx, neg_add_eq_sub]

/-- The complex-power constants of `A_n`, `B_n` at real `x > 0`, written as real powers. -/
theorem generalizedAiry_cpow_consts (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (generalizedAiryOrder n : ℂ) ^ (1 - (generalizedAiryOrder n : ℂ)) =
        ((generalizedAiryOrder n ^ (1 - generalizedAiryOrder n) : ℝ) : ℂ) ∧
      (generalizedAiryOrder n : ℂ) ^ ((generalizedAiryOrder n : ℂ) + 1) =
        ((generalizedAiryOrder n ^ (generalizedAiryOrder n + 1) : ℝ) : ℂ) ∧
      (generalizedAiryOrder n : ℂ) ^ (-1 / 2 : ℂ) =
        ((generalizedAiryOrder n ^ (-1 / 2 : ℝ) : ℝ) : ℂ) ∧
      (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) =
        ((generalizedAiryOrder n ^ (1 / 2 : ℝ) : ℝ) : ℂ) ∧
      (x : ℂ) ^ (1 / 2 : ℂ) = ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) ∧
      ((generalizedAiryOrder n : ℂ) * x) ^ (1 / 2 : ℂ) =
        ((generalizedAiryOrder n ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  have hp := (generalizedAiryOrder_pos n).le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← generalizedAiryOrder_cpow]; push_cast; rfl
  · rw [← generalizedAiryOrder_cpow]; push_cast; rfl
  · rw [← generalizedAiryOrder_cpow]; push_cast; ring_nf
  · rw [← generalizedAiryOrder_cpow]; push_cast; ring_nf
  · rw [ofReal_cpow hx.le]; push_cast; ring_nf
  · rw [← Real.mul_rpow hp hx.le, ofReal_cpow (by positivity)]; push_cast; ring_nf

/-- `sin(pπ) ≠ 0`, since `0 < p < 1`. -/
theorem generalizedAiryOrder_sin_ne_zero (n : ℕ) :
    sin ((generalizedAiryOrder n : ℂ) * π) ≠ 0 := by
  rw [← ofReal_mul, ← ofReal_sin, ofReal_ne_zero]
  exact (Real.sin_pos_of_pos_of_lt_pi (by have := generalizedAiryOrder_pos n; positivity)
    (by nlinarith [generalizedAiryOrder_lt_one n, Real.pi_pos])).ne'

/-- The order `p = 1/(n+2)` is not an integer. -/
theorem generalizedAiryOrder_not_int (n : ℕ) : ∀ k : ℤ, (generalizedAiryOrder n : ℂ) ≠ k := by
  intro k hk
  have h : generalizedAiryOrder n = k := by exact_mod_cast hk
  have h0 := generalizedAiryOrder_pos n
  have h1 := generalizedAiryOrder_lt_one n
  rw [h] at h0 h1
  have : (0 : ℤ) < k := by exact_mod_cast h0
  have : k < (1 : ℤ) := by exact_mod_cast h1
  omega

/-- The order `p = 1/(n+2)` is nonzero. -/
theorem generalizedAiryOrder_ne_zero (n : ℕ) : (generalizedAiryOrder n : ℂ) ≠ 0 := by
  simp only [generalizedAiryOrder]; push_cast
  exact one_div_ne_zero (by norm_cast)

/-- `(ζ/2)^{s p} = p^{s p} z^{s/2}` for `z` in the sector `|arg z| < π/(n+2)`. -/
theorem generalizedAiryZeta_half_cpow_sector (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (harg : |arg z| < π / ((n : ℝ) + 2)) (s : ℂ) :
    (generalizedAiryZeta n z / 2) ^ (s * (generalizedAiryOrder n : ℂ)) =
      (generalizedAiryOrder n : ℂ) ^ (s * (generalizedAiryOrder n : ℂ)) * z ^ (s / 2) := by
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hnc : (n : ℂ) + 2 ≠ 0 := by norm_cast
  have hp := generalizedAiryOrder_pos n
  set L := ((n : ℂ) + 2) / 2 * log z
  have hL : L.im = ((n : ℝ) + 2) / 2 * arg z := by
    simp only [L]
    rw [show ((n : ℂ) + 2) / 2 = (((n : ℝ) + 2) / 2 : ℝ) by push_cast; ring, im_ofReal_mul, log_im]
  have hb : |L.im| < π / 2 := by
    rw [hL, abs_mul, abs_of_pos (by positivity)]
    calc ((n : ℝ) + 2) / 2 * |arg z| < ((n : ℝ) + 2) / 2 * (π / ((n : ℝ) + 2)) :=
          mul_lt_mul_of_pos_left harg (by positivity)
      _ = π / 2 := by field_simp
  have hζ : generalizedAiryZeta n z / 2 = ((generalizedAiryOrder n : ℝ) : ℂ) * exp L := by
    rw [generalizedAiryZeta, cpow_def_of_ne_zero hz]
    simp only [generalizedAiryOrder, L]; push_cast; field_simp
  have hpL : ((generalizedAiryOrder n : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  rw [hζ, cpow_def_of_ne_zero (mul_ne_zero hpL (exp_ne_zero _)), log_ofReal_mul hp (exp_ne_zero _),
    log_exp (by linarith [(abs_lt.mp hb).1, Real.pi_pos]) (by linarith [(abs_lt.mp hb).2, Real.pi_pos]),
    cpow_def_of_ne_zero hpL, cpow_def_of_ne_zero hz, ← exp_add, ofReal_log hp.le]
  congr 1
  simp only [L, generalizedAiryOrder]; push_cast; field_simp

/-- `ζ²/4 = z^{n+2}/(n+2)²` for all `z`. -/
theorem generalizedAiryZeta_sq_div_four' (n : ℕ) (z : ℂ) :
    generalizedAiryZeta n z ^ 2 / 4 = z ^ (n + 2) / ((n : ℂ) + 2) ^ 2 := by
  have hnc : (n : ℂ) + 2 ≠ 0 := by norm_cast
  rw [generalizedAiryZeta, mul_pow, ← cpow_nat_mul,
    show ((2 : ℕ) : ℂ) * (((n : ℂ) + 2) / 2) = ((n + 2 : ℕ) : ℂ) by push_cast; ring, cpow_natCast]
  field_simp; ring

/-- `z^{1/2} I_p(ζ) = p^p G_n(z)` in the sector `|arg z| < π/(n+2)`. -/
theorem cpow_half_mul_besselI_generalizedAiryZeta (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (harg : |arg z| < π / ((n : ℝ) + 2)) :
    z ^ (1 / 2 : ℂ) * DLMF.Bessel.besselI (generalizedAiryOrder n) (generalizedAiryZeta n z) =
      (generalizedAiryOrder n : ℂ) ^ (generalizedAiryOrder n : ℂ) * generalizedAiryG n z := by
  have h := generalizedAiryZeta_half_cpow_sector n hz harg 1
  rw [one_mul] at h
  rw [DLMF.Bessel.besselI, h, generalizedAiryZeta_sq_div_four', generalizedAiryG, add_comm _ (1 : ℂ)]
  have hzz : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz]; norm_num
  linear_combination ((generalizedAiryOrder n : ℂ) ^ (generalizedAiryOrder n : ℂ) *
    regularizedHGFun ∅ {1 + (generalizedAiryOrder n : ℂ)} (z ^ (n + 2) / ((n : ℂ) + 2) ^ 2)) * hzz

/-- `z^{1/2} I_{-p}(ζ) = p^{-p} F_n(z)` in the sector `|arg z| < π/(n+2)`. -/
theorem cpow_half_mul_besselI_neg_generalizedAiryZeta (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (harg : |arg z| < π / ((n : ℝ) + 2)) :
    z ^ (1 / 2 : ℂ) * DLMF.Bessel.besselI (-(generalizedAiryOrder n : ℂ)) (generalizedAiryZeta n z) =
      (generalizedAiryOrder n : ℂ) ^ (-(generalizedAiryOrder n : ℂ)) * generalizedAiryF n z := by
  have h := generalizedAiryZeta_half_cpow_sector n hz harg (-1)
  rw [neg_one_mul] at h
  rw [DLMF.Bessel.besselI, h, generalizedAiryZeta_sq_div_four', generalizedAiryF, neg_add_eq_sub]
  have hzz : z ^ (1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ) = 1 := by
    rw [← cpow_add _ _ hz]; norm_num
  linear_combination ((generalizedAiryOrder n : ℂ) ^ (-(generalizedAiryOrder n : ℂ)) *
    regularizedHGFun ∅ {1 - (generalizedAiryOrder n : ℂ)} (z ^ (n + 2) / ((n : ℂ) + 2) ^ 2)) * hzz

/-- For `x > 0`, `z^{1/2} (a I_p(ζ) + b K_p(ζ))`, with `p = 1/(n+2)` and
`ζ = 2p z^{(n+2)/2}`, satisfies `w'' = xⁿ w` at `x` (DLMF 9.13.2). -/
@[dlmf 9.13.E2]
theorem generalizedAiry_bessel_basis {n : ℕ} (hn : 1 ≤ n) (a b : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv (fun z : ℂ => z ^ (1 / 2 : ℂ) *
      (a * DLMF.Bessel.besselI (generalizedAiryOrder n) (generalizedAiryZeta n z) +
        b * DLMF.Bessel.besselK (generalizedAiryOrder n) (generalizedAiryZeta n z))))
      ((x : ℂ) ^ n * (x : ℂ) ^ (1 / 2 : ℂ) *
        (a * DLMF.Bessel.besselI (generalizedAiryOrder n) (generalizedAiryZeta n x) +
          b * DLMF.Bessel.besselK (generalizedAiryOrder n) (generalizedAiryZeta n x))) x := by
  set p : ℂ := (generalizedAiryOrder n : ℂ)
  set K : ℂ := b * (π / 2 / sin (p * π))
  have hC := ((isGenAirySol_generalizedAiryF n).const_mul (K * p ^ (-p))).add
    ((isGenAirySol_generalizedAiryG n).const_mul ((a - K) * p ^ p))
  have hev : ∀ᶠ z in 𝓝 (x : ℂ), z ≠ 0 ∧ |arg z| < π / ((n : ℝ) + 2) := by
    have hc : 0 < π / ((n : ℝ) + 2) := by positivity
    have hs : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hx
    have h1 := (continuousAt_arg hs).eventually (Ioo_mem_nhds (a := -(π / ((n : ℝ) + 2)))
      (b := π / ((n : ℝ) + 2)) (by rw [arg_ofReal_of_nonneg hx.le]; linarith)
      (by rw [arg_ofReal_of_nonneg hx.le]; exact hc))
    filter_upwards [h1, isOpen_ne.mem_nhds (ofReal_ne_zero.mpr hx.ne')] with z hz1 hz2
    exact ⟨hz2, abs_lt.mpr hz1⟩
  have heq : (fun z : ℂ => z ^ (1 / 2 : ℂ) *
      (a * DLMF.Bessel.besselI (generalizedAiryOrder n) (generalizedAiryZeta n z) +
        b * DLMF.Bessel.besselK (generalizedAiryOrder n) (generalizedAiryZeta n z))) =ᶠ[𝓝 (x : ℂ)]
      (fun z => K * p ^ (-p) * generalizedAiryF n z + (a - K) * p ^ p * generalizedAiryG n z) := by
    filter_upwards [hev] with z ⟨hz, harg⟩
    have h1 := cpow_half_mul_besselI_generalizedAiryZeta n hz harg
    have h2 := cpow_half_mul_besselI_neg_generalizedAiryZeta n hz harg
    rw [DLMF.Bessel.besselK_eq_of_not_int (generalizedAiryOrder_not_int n), DLMF.Bessel.besselE]
    have hs := generalizedAiryOrder_sin_ne_zero n
    simp only [K]
    linear_combination (a - K) * h1 + K * h2
  have hd := heq.deriv
  have hval := heq.eq_of_nhds
  refine ((hC x).2.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hd] with z hz
    rw [hz]; exact ((hC z).1.deriv)
  · beta_reduce; rw [mul_assoc ((x : ℂ) ^ n), hval]; ring

/-- For even `n`, `A_n(-z) = p^{1/2} B_n(z)` on all of `ℂ`. -/
theorem generalizedAiryA_neg_of_even {n : ℕ} (hn : Even n) (z : ℂ) :
    generalizedAiryA n (-z) = (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) * generalizedAiryB n z := by
  have hpow : (-z) ^ (n + 2) = z ^ (n + 2) := (hn.add even_two).neg_pow z
  have hp := generalizedAiryOrder_ne_zero n
  simp only [generalizedAiryA, generalizedAiryB, generalizedAiryF, generalizedAiryG, hpow]
  have h1 : (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) * (generalizedAiryOrder n : ℂ) ^ (-1 / 2 : ℂ)
      = 1 := by
    rw [← cpow_add _ _ hp, show (1 / 2 : ℂ) + -1 / 2 = 0 by ring, cpow_zero]
  set p := (generalizedAiryOrder n : ℂ)
  set w := z ^ (n + 2) / ((n : ℂ) + 2) ^ 2
  linear_combination (-(p ^ (1 - p) * regularizedHGFun ∅ {1 - p} w +
    p ^ (p + 1) * (z * regularizedHGFun ∅ {1 + p} w))) * h1

/-- For even `n`, `B_n(-z) = p^{-1/2} A_n(z)` on all of `ℂ`. -/
theorem generalizedAiryB_neg_of_even {n : ℕ} (hn : Even n) (z : ℂ) :
    generalizedAiryB n (-z) = (generalizedAiryOrder n : ℂ) ^ (-1 / 2 : ℂ) * generalizedAiryA n z := by
  have hp := generalizedAiryOrder_ne_zero n
  rw [show generalizedAiryA n z = generalizedAiryA n (-(-z)) by rw [neg_neg],
    generalizedAiryA_neg_of_even hn, ← mul_assoc, ← cpow_add _ _ hp,
    show (-1 / 2 : ℂ) + 1 / 2 = 0 by ring, cpow_zero, one_mul]

/-- `A_n(x) = (2p/π) sin(pπ) x^{1/2} K_p(ζ)` for `x > 0` (DLMF 9.13.4). -/
@[dlmf 9.13.E4]
theorem generalizedAiryA_bessel {n : ℕ} {x : ℝ} (hx : 0 < x) :
    generalizedAiryA n x = 2 * (generalizedAiryOrder n : ℂ) / π * sin ((generalizedAiryOrder n : ℂ) * π) * (x : ℂ) ^ (1 / 2 : ℂ) * DLMF.Bessel.besselK (generalizedAiryOrder n : ℂ) (generalizedAiryZeta n x) := by
  obtain ⟨c1, c2, -, -, c5, -⟩ := generalizedAiry_cpow_consts n hx
  have hp := generalizedAiryOrder_pos n
  have hs := generalizedAiryOrder_sin_ne_zero n
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [DLMF.Bessel.besselK_eq_of_not_int (generalizedAiryOrder_not_int n), DLMF.Bessel.besselE,
    show 2 * (generalizedAiryOrder n : ℂ) / π * sin ((generalizedAiryOrder n : ℂ) * π) *
        (x : ℂ) ^ (1 / 2 : ℂ) * (π / 2 * (DLMF.Bessel.besselI (-(generalizedAiryOrder n : ℂ))
          (generalizedAiryZeta n x) - DLMF.Bessel.besselI (generalizedAiryOrder n : ℂ)
          (generalizedAiryZeta n x)) / sin ((generalizedAiryOrder n : ℂ) * π)) =
      (generalizedAiryOrder n : ℂ) * (x : ℂ) ^ (1 / 2 : ℂ) *
        (DLMF.Bessel.besselI (-(generalizedAiryOrder n : ℂ)) (generalizedAiryZeta n x) -
          DLMF.Bessel.besselI (generalizedAiryOrder n : ℂ) (generalizedAiryZeta n x)) by
      field_simp,
    besselI_generalizedAiryZeta n hx, besselI_neg_generalizedAiryZeta n hx, c5]
  simp only [generalizedAiryA, generalizedAiryF, generalizedAiryG]
  rw [c1, c2]
  set p := generalizedAiryOrder n
  have r1 : p * x ^ (1 / 2 : ℝ) * (p ^ (-p) * x ^ (-1 / 2 : ℝ)) = p ^ (1 - p) := by
    rw [mul_mul_mul_comm, ← Real.rpow_add hx, show (1 / 2 : ℝ) + -1 / 2 = 0 by norm_num,
      Real.rpow_zero, mul_one, sub_eq_add_neg, Real.rpow_add hp, Real.rpow_one]
  have r2 : p * x ^ (1 / 2 : ℝ) * (p ^ p * x ^ (1 / 2 : ℝ)) = p ^ (p + 1) * x := by
    rw [mul_mul_mul_comm, ← Real.rpow_add hx, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
      Real.rpow_one, Real.rpow_add hp, Real.rpow_one]
    ring
  have r1' := congrArg (fun r : ℝ => (r : ℂ)) r1
  have r2' := congrArg (fun r : ℝ => (r : ℂ)) r2
  push_cast at r1' r2' ⊢
  set w := (x : ℂ) ^ (n + 2) / ((n : ℂ) + 2) ^ 2
  linear_combination (-regularizedHGFun ∅ {1 - (p : ℂ)} w) * r1' +
    regularizedHGFun ∅ {1 + (p : ℂ)} w * r2'

/-- `B_n(x) = (p x)^{1/2} (I_{-p}(ζ) + I_p(ζ))` for `x > 0` (DLMF 9.13.4). -/
@[dlmf 9.13.E4]
theorem generalizedAiryB_bessel {n : ℕ} {x : ℝ} (hx : 0 < x) :
    generalizedAiryB n x = ((generalizedAiryOrder n : ℂ) * x) ^ (1 / 2 : ℂ) * (DLMF.Bessel.besselI (-(generalizedAiryOrder n : ℂ)) (generalizedAiryZeta n x) + DLMF.Bessel.besselI (generalizedAiryOrder n : ℂ) (generalizedAiryZeta n x)) := by
  obtain ⟨c1, c2, c3, -, -, c6⟩ := generalizedAiry_cpow_consts n hx
  have hp := generalizedAiryOrder_pos n
  rw [besselI_generalizedAiryZeta n hx, besselI_neg_generalizedAiryZeta n hx, c6]
  simp only [generalizedAiryB, generalizedAiryF, generalizedAiryG]
  rw [c1, c2, c3]
  set p := generalizedAiryOrder n
  have r1 : p ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * (p ^ (-p) * x ^ (-1 / 2 : ℝ)) =
      p ^ (-1 / 2 : ℝ) * p ^ (1 - p) := by
    rw [mul_mul_mul_comm, ← Real.rpow_add hp, ← Real.rpow_add hx, ← Real.rpow_add hp]
    norm_num; ring_nf
  have r2 : p ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * (p ^ p * x ^ (1 / 2 : ℝ)) =
      p ^ (-1 / 2 : ℝ) * p ^ (p + 1) * x := by
    rw [mul_mul_mul_comm, ← Real.rpow_add hp, ← Real.rpow_add hx, ← Real.rpow_add hp,
      show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
    congr 2; ring
  have r1' := congrArg (fun r : ℝ => (r : ℂ)) r1
  have r2' := congrArg (fun r : ℝ => (r : ℂ)) r2
  push_cast at r1' r2' ⊢
  set w := (x : ℂ) ^ (n + 2) / ((n : ℂ) + 2) ^ 2
  linear_combination (-regularizedHGFun ∅ {1 - (p : ℂ)} w) * r1' -
    regularizedHGFun ∅ {1 + (p : ℂ)} w * r2'

/-- The Wronskian of two solutions of `w'' = s z^n w` is constant. -/
theorem IsGenAirySol.wronskian_eq {n : ℕ} {s : ℂ} {f f' g g' : ℂ → ℂ} (hf : IsGenAirySol n s f f')
    (hg : IsGenAirySol n s g g') (z : ℂ) :
    f z * g' z - f' z * g z = f 0 * g' 0 - f' 0 * g 0 := by
  have hd : ∀ z, HasDerivAt (fun z => f z * g' z - f' z * g z) 0 z := fun z =>
    (((hf z).1.mul (hg z).2).sub ((hf z).2.mul (hg z).1)).congr_deriv (by ring)
  exact is_const_of_deriv_eq_zero (fun z => (hd z).differentiableAt) (fun z => (hd z).deriv) z 0

/-- A solution is a combination of two solutions with nonzero Wronskian. -/
theorem IsGenAirySol.eq_combination {n : ℕ} {s : ℂ} {f f' g g' w w' : ℂ → ℂ}
    (hf : IsGenAirySol n s f f') (hg : IsGenAirySol n s g g') (hw : IsGenAirySol n s w w')
    (hW : f 0 * g' 0 - f' 0 * g 0 ≠ 0) :
    ∃ a b : ℂ, ∀ z, w z = a * f z + b * g z := by
  refine ⟨(w 0 * g' 0 - w' 0 * g 0) / (f 0 * g' 0 - f' 0 * g 0),
    -(w 0 * f' 0 - w' 0 * f 0) / (f 0 * g' 0 - f' 0 * g 0), fun z => ?_⟩
  have h1 := hw.wronskian_eq hf z
  have h2 := hw.wronskian_eq hg z
  have h3 := hf.wronskian_eq hg z
  generalize f 0 * g' 0 - f' 0 * g 0 = D at hW h3 ⊢
  field_simp
  linear_combination (-g z) * h1 + f z * h2 - w z * h3

/-- `F_n(0) = 1/Γ(1-p)`. -/
theorem generalizedAiryF_zero (n : ℕ) :
    generalizedAiryF n 0 = (Gamma (1 - (generalizedAiryOrder n : ℂ)))⁻¹ := by
  rw [generalizedAiryF, show (0 : ℂ) ^ (n + 2) / ((n : ℂ) + 2) ^ 2 = 0 by simp, reg0F1_zero]

/-- `G_n(0) = 0`. -/
theorem generalizedAiryG_zero (n : ℕ) : generalizedAiryG n 0 = 0 := by
  simp [generalizedAiryG]

/-- `F_n′(0) = 0`. -/
theorem generalizedAiryFDeriv_zero (n : ℕ) : generalizedAiryFDeriv n 0 = 0 := by
  simp [generalizedAiryFDeriv]

/-- `G_n′(0) = 1/Γ(1+p)`. -/
theorem generalizedAiryGDeriv_zero (n : ℕ) :
    generalizedAiryGDeriv n 0 = (Gamma (1 + (generalizedAiryOrder n : ℂ)))⁻¹ := by
  rw [generalizedAiryGDeriv, show (0 : ℂ) ^ (n + 2) / ((n : ℂ) + 2) ^ 2 = 0 by simp, reg0F1_zero]
  simp

/-- Initial values: `A_n(0) = p^{1/2} B_n(0) = p^{1-p}/Γ(1-p)` and
`-A_n'(0) = p^{1/2} B_n'(0) = p^p/Γ(p)` (DLMF 9.13.5). -/
@[dlmf 9.13.E5]
theorem generalizedAiry_initial_values {n : ℕ} :
    generalizedAiryA n 0 = (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) * generalizedAiryB n 0 ∧
      generalizedAiryA n 0 = (generalizedAiryOrder n : ℂ) ^ (1 - (generalizedAiryOrder n : ℂ)) / Gamma (1 - (generalizedAiryOrder n : ℂ)) ∧
      -deriv (generalizedAiryA n) 0 = (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) * deriv (generalizedAiryB n) 0 ∧
      -deriv (generalizedAiryA n) 0 = (generalizedAiryOrder n : ℂ) ^ (generalizedAiryOrder n : ℂ) / Gamma (generalizedAiryOrder n) := by
  have hp := generalizedAiryOrder_ne_zero n
  have h1 : (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) * (generalizedAiryOrder n : ℂ) ^ (-1 / 2 : ℂ)
      = 1 := by
    rw [← cpow_add _ _ hp, show (1 / 2 : ℂ) + -1 / 2 = 0 by ring, cpow_zero]
  rw [deriv_generalizedAiryA, deriv_generalizedAiryB]
  simp only [generalizedAiryA, generalizedAiryB, generalizedAiryADeriv, generalizedAiryBDeriv,
    generalizedAiryF_zero, generalizedAiryG_zero, generalizedAiryFDeriv_zero,
    generalizedAiryGDeriv_zero]
  set p := (generalizedAiryOrder n : ℂ)
  have hG : Gamma (1 + p) = p * Gamma p := by rw [add_comm, Gamma_add_one _ hp]
  have hpp : p ^ (p + 1) = p ^ p * p := by rw [cpow_add _ _ hp, cpow_one]
  refine ⟨?_, by ring, ?_, ?_⟩
  · linear_combination (-(p ^ (1 - p) * (Gamma (1 - p))⁻¹)) * h1
  · linear_combination (-(p ^ (p + 1) * (Gamma (1 + p))⁻¹)) * h1
  · rw [hG, hpp]
    have : Gamma p ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa [p] using generalizedAiryOrder_pos n)
    field_simp
    ring

/-- `A_n(-x)` for `x > 0`: `p x^{1/2} (J_{-p}(ζ) + J_p(ζ))` for odd `n`, and
`p^{1/2} B_n(x)` for even `n` (DLMF 9.13.6). -/
@[dlmf 9.13.E6]
theorem generalizedAiryA_negative {n : ℕ} {x : ℝ} (hx : 0 < x) :
    generalizedAiryA n (-x) = if Odd n then (generalizedAiryOrder n : ℂ) * (x : ℂ) ^ (1 / 2 : ℂ) * (besselJ (-(generalizedAiryOrder n : ℂ)) (generalizedAiryZeta n x) + besselJ (generalizedAiryOrder n : ℂ) (generalizedAiryZeta n x)) else (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) * generalizedAiryB n x := by
  split_ifs with hodd
  · obtain ⟨c1, c2, -, -, c5, -⟩ := generalizedAiry_cpow_consts n hx
    have hp := generalizedAiryOrder_pos n
    have hpow : (-(x : ℂ)) ^ (n + 2) = -((x : ℂ) ^ (n + 2)) := (hodd.add_even even_two).neg_pow _
    rw [besselJ_generalizedAiryZeta n hx, besselJ_neg_generalizedAiryZeta n hx, c5]
    simp only [generalizedAiryA, generalizedAiryF, generalizedAiryG]
    rw [c1, c2]
    push_cast
    rw [hpow, neg_div _ ((x : ℂ) ^ (n + 2))]
    set p := generalizedAiryOrder n
    have r1 : p * x ^ (1 / 2 : ℝ) * (p ^ (-p) * x ^ (-1 / 2 : ℝ)) = p ^ (1 - p) := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hx, show (1 / 2 : ℝ) + -1 / 2 = 0 by norm_num,
        Real.rpow_zero, mul_one, sub_eq_add_neg, Real.rpow_add hp, Real.rpow_one]
    have r2 : p * x ^ (1 / 2 : ℝ) * (p ^ p * x ^ (1 / 2 : ℝ)) = p ^ (p + 1) * x := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hx, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
        Real.rpow_one, Real.rpow_add hp, Real.rpow_one]
      ring
    have r1' := congrArg (fun r : ℝ => (r : ℂ)) r1
    have r2' := congrArg (fun r : ℝ => (r : ℂ)) r2
    push_cast at r1' r2' ⊢
    set w := -((x : ℂ) ^ (n + 2) / ((n : ℂ) + 2) ^ 2)
    linear_combination (-regularizedHGFun ∅ {1 - (p : ℂ)} w) * r1' -
      regularizedHGFun ∅ {1 + (p : ℂ)} w * r2'
  · exact generalizedAiryA_neg_of_even (Nat.not_odd_iff_even.mp hodd) _

/-- `B_n(-x)` for `x > 0`: `(p x)^{1/2} (J_{-p}(ζ) - J_p(ζ))` for odd `n`, and
`p^{-1/2} A_n(x)` for even `n` (DLMF 9.13.7). -/
@[dlmf 9.13.E7]
theorem generalizedAiryB_negative {n : ℕ} {x : ℝ} (hx : 0 < x) :
    generalizedAiryB n (-x) = if Odd n then ((generalizedAiryOrder n : ℂ) * x) ^ (1 / 2 : ℂ) * (besselJ (-(generalizedAiryOrder n : ℂ)) (generalizedAiryZeta n x) - besselJ (generalizedAiryOrder n : ℂ) (generalizedAiryZeta n x)) else (generalizedAiryOrder n : ℂ) ^ (-1 / 2 : ℂ) * generalizedAiryA n x := by
  split_ifs with hodd
  · obtain ⟨c1, c2, c3, -, -, c6⟩ := generalizedAiry_cpow_consts n hx
    have hp := generalizedAiryOrder_pos n
    have hpow : (-(x : ℂ)) ^ (n + 2) = -((x : ℂ) ^ (n + 2)) := (hodd.add_even even_two).neg_pow _
    rw [besselJ_generalizedAiryZeta n hx, besselJ_neg_generalizedAiryZeta n hx, c6]
    simp only [generalizedAiryB, generalizedAiryF, generalizedAiryG]
    rw [c1, c2, c3]
    push_cast
    rw [hpow, neg_div _ ((x : ℂ) ^ (n + 2))]
    set p := generalizedAiryOrder n
    have r1 : p ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * (p ^ (-p) * x ^ (-1 / 2 : ℝ)) =
        p ^ (-1 / 2 : ℝ) * p ^ (1 - p) := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hp, ← Real.rpow_add hx, ← Real.rpow_add hp]
      norm_num; ring_nf
    have r2 : p ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * (p ^ p * x ^ (1 / 2 : ℝ)) =
        p ^ (-1 / 2 : ℝ) * p ^ (p + 1) * x := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hp, ← Real.rpow_add hx, ← Real.rpow_add hp,
        show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
      congr 2; ring
    have r1' := congrArg (fun r : ℝ => (r : ℂ)) r1
    have r2' := congrArg (fun r : ℝ => (r : ℂ)) r2
    push_cast at r1' r2' ⊢
    set w := -((x : ℂ) ^ (n + 2) / ((n : ℂ) + 2) ^ 2)
    linear_combination (-regularizedHGFun ∅ {1 - (p : ℂ)} w) * r1' +
      regularizedHGFun ∅ {1 + (p : ℂ)} w * r2'
  · exact generalizedAiryB_neg_of_even (Nat.not_odd_iff_even.mp hodd) _

/-- `𝒲{A_n, B_n} = (2/π) p^{1/2} sin(pπ)` (DLMF 9.13.8). -/
@[dlmf 9.13.E8]
theorem generalizedAiry_wronskian {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    generalizedAiryA n z * deriv (generalizedAiryB n) z - deriv (generalizedAiryA n) z * generalizedAiryB n z =
      2 / π * (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) * sin ((generalizedAiryOrder n : ℂ) * π) := by
  rw [deriv_generalizedAiryA, deriv_generalizedAiryB,
    (isGenAirySol_generalizedAiryA n).wronskian_eq (isGenAirySol_generalizedAiryB n) z]
  simp only [generalizedAiryA, generalizedAiryB, generalizedAiryADeriv, generalizedAiryBDeriv,
    generalizedAiryF_zero, generalizedAiryG_zero, generalizedAiryFDeriv_zero,
    generalizedAiryGDeriv_zero]
  have hp := generalizedAiryOrder_ne_zero n
  set p := (generalizedAiryOrder n : ℂ)
  have hG : Gamma (1 + p) = p * Gamma p := by rw [add_comm, Gamma_add_one _ hp]
  have hrefl := Gamma_mul_Gamma_one_sub p
  have hs : sin (π * p) ≠ 0 := by rw [mul_comm]; exact generalizedAiryOrder_sin_ne_zero n
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΓ : Gamma p ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa [p] using generalizedAiryOrder_pos n)
  have hΓ' : Gamma (1 - p) ≠ 0 := by
    intro h; rw [h, mul_zero] at hrefl; exact div_ne_zero hpi hs hrefl.symm
  have hpow : p ^ (1 - p) * p ^ (p + 1) = p ^ (3 / 2 : ℂ) * p ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hp, ← cpow_add _ _ hp]; ring_nf
  have hpow2 : p ^ (-1 / 2 : ℂ) * p ^ (3 / 2 : ℂ) = p := by
    rw [← cpow_add _ _ hp]; norm_num
  rw [hG, mul_comm p (π : ℂ)]
  have hrefl' : Gamma p * Gamma (1 - p) * sin (π * p) = π := by
    rw [hrefl]; field_simp
  field_simp
  simp only [mul_zero, zero_mul, sub_zero, add_zero, zero_add]
  rw [show (-(1 / 2) : ℂ) = -1 / 2 by ring, mul_comm p (π : ℂ)]
  linear_combination (2 * π * p ^ (-1 / 2 : ℂ)) * hpow + (2 * π * p ^ (1 / 2 : ℂ)) * hpow2 -
    (2 * p * p ^ (1 / 2 : ℂ)) * hrefl'

/-- `(1/3)^a = 3^{-a}` as complex powers of reals. -/
theorem third_cpow (a : ℝ) : ((1 / 3 : ℂ)) ^ (a : ℂ) = (((3 : ℝ) ^ (-a) : ℝ) : ℂ) := by
  rw [show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by norm_num),
    one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]

/-- For `n = 1` the order is `1/3`. -/
theorem generalizedAiryOrder_one : (generalizedAiryOrder 1 : ℂ) = 1 / 3 := by
  simp only [generalizedAiryOrder]; push_cast; norm_num

/-- For `n = 1`, `generalizedAiryF` is `airyF`. -/
theorem generalizedAiryF_one (z : ℂ) : generalizedAiryF 1 z = airyF z := by
  simp only [generalizedAiryF, airyF, generalizedAiryOrder_one]; norm_num

/-- For `n = 1`, `generalizedAiryG` is `airyG`. -/
theorem generalizedAiryG_one (z : ℂ) : generalizedAiryG 1 z = airyG z := by
  simp only [generalizedAiryG, airyG, generalizedAiryOrder_one]; norm_num

/-- The n=1 specialization, DLMF §9.13(i). -/
theorem generalizedAiryA_one (z : ℂ) :
    generalizedAiryA 1 z = airyAi z := by
  simp only [generalizedAiryA, generalizedAiryF_one, generalizedAiryG_one,
    generalizedAiryOrder_one, airyAi]
  rw [show (1 : ℂ) - 1 / 3 = ((2 / 3 : ℝ) : ℂ) by push_cast; norm_num,
    show (1 / 3 : ℂ) + 1 = ((4 / 3 : ℝ) : ℂ) by push_cast; norm_num, third_cpow, third_cpow]

/-- The n=1 specialization, DLMF §9.13(i). -/
theorem generalizedAiryB_one (z : ℂ) :
    generalizedAiryB 1 z = airyBi z := by
  simp only [generalizedAiryB, generalizedAiryF_one, generalizedAiryG_one,
    generalizedAiryOrder_one, airyBi]
  rw [show (1 : ℂ) - 1 / 3 = ((2 / 3 : ℝ) : ℂ) by push_cast; norm_num,
    show (1 / 3 : ℂ) + 1 = ((4 / 3 : ℝ) : ℂ) by push_cast; norm_num, third_cpow, third_cpow,
    show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring, third_cpow,
    show -(-1 / 2 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]

/-- `A_n(z) ~ (p/π)^{1/2} sin(pπ) z^{-n/4} e^{-ζ}` with relative error `O(1/ζ)` as
`z → ∞` in `|ph z| ≤ 3pπ - δ` (DLMF 9.13.9). -/
@[dlmf 9.13.E9]
theorem generalizedAiryA_asymptotic {n : ℕ} (hn : 1 ≤ n)  {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 3 * generalizedAiryOrder n * π) :
    IsBigO (airySector (3 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryA n z - ((((generalizedAiryOrder n : ℂ) / π) ^ (1 / 2 : ℂ) * sin ((generalizedAiryOrder n : ℂ) * π)) * z ^ (-(n : ℂ) / 4) * exp (-generalizedAiryZeta n z))) (fun z => ‖z ^ (-(n : ℂ) / 4) * exp (-generalizedAiryZeta n z) / (generalizedAiryZeta n z)‖) := by
  sorry

/-- For odd `n`, `A_n(-z) ~ 2 (p/π)^{1/2} cos(pπ/2) z^{-n/4} cos(ζ - π/4)` as
`z → ∞` in `|ph z| ≤ 2pπ - δ`, error `O(|z^{-n/4}/ζ| e^{|ℑζ|})` (DLMF 9.13.10). -/
@[dlmf 9.13.E10]
theorem generalizedAiryA_negative_odd_asymptotic {n : ℕ} (hn : 1 ≤ n)  (hodd : Odd n) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * generalizedAiryOrder n * π) :
    IsBigO (airySector (2 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryA n (-z) - (2 * ((generalizedAiryOrder n : ℂ) / π) ^ (1 / 2 : ℂ) * cos ((generalizedAiryOrder n : ℂ) * π / 2) * z ^ (-(n : ℂ) / 4) * cos (generalizedAiryZeta n z - π / 4))) (fun z => ‖z ^ (-(n : ℂ) / 4) / (generalizedAiryZeta n z)‖ * Real.exp |(generalizedAiryZeta n z).im|) := by
  sorry

/-- For even `n`, `A_n(-z) ~ (p/π)^{1/2} z^{-n/4} e^{ζ}` with relative error `O(1/ζ)`
as `z → ∞` in `|ph z| ≤ pπ - δ` (DLMF 9.13.10). -/
@[dlmf 9.13.E10]
theorem generalizedAiryA_negative_even_asymptotic {n : ℕ} (hn : 1 ≤ n)  (heven : Even n) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 * generalizedAiryOrder n * π) :
    IsBigO (airySector (1 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryA n (-z) - ((((generalizedAiryOrder n : ℂ) / π) ^ (1 / 2 : ℂ)) * z ^ (-(n : ℂ) / 4) * exp (generalizedAiryZeta n z))) (fun z => ‖z ^ (-(n : ℂ) / 4) * exp (generalizedAiryZeta n z) / (generalizedAiryZeta n z)‖) := by
  sorry

/-- `B_n(z) ~ π^{-1/2} z^{-n/4} e^{ζ}` with relative error `O(1/ζ)` as `z → ∞` in
`|ph z| ≤ pπ - δ` (DLMF 9.13.11). -/
@[dlmf 9.13.E11]
theorem generalizedAiryB_asymptotic {n : ℕ} (hn : 1 ≤ n)  {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 * generalizedAiryOrder n * π) :
    IsBigO (airySector (1 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryB n z - ((1 / (π : ℂ) ^ (1 / 2 : ℂ)) * z ^ (-(n : ℂ) / 4) * exp (generalizedAiryZeta n z))) (fun z => ‖z ^ (-(n : ℂ) / 4) * exp (generalizedAiryZeta n z) / (generalizedAiryZeta n z)‖) := by
  sorry

/-- For odd `n`, `B_n(-z) ~ -2 π^{-1/2} sin(pπ/2) z^{-n/4} sin(ζ - π/4)` as `z → ∞`
in `|ph z| ≤ 2pπ - δ`, error `O(|z^{-n/4}/ζ| e^{|ℑζ|})` (DLMF 9.13.12). -/
@[dlmf 9.13.E12]
theorem generalizedAiryB_negative_odd_asymptotic {n : ℕ} (hn : 1 ≤ n)  (hodd : Odd n) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * generalizedAiryOrder n * π) :
    IsBigO (airySector (2 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryB n (-z) - (-2 / (π : ℂ) ^ (1 / 2 : ℂ) * sin ((generalizedAiryOrder n : ℂ) * π / 2) * z ^ (-(n : ℂ) / 4) * sin (generalizedAiryZeta n z - π / 4))) (fun z => ‖z ^ (-(n : ℂ) / 4) / (generalizedAiryZeta n z)‖ * Real.exp |(generalizedAiryZeta n z).im|) := by
  sorry

/-- For even `n`, `B_n(-z) ~ π^{-1/2} sin(pπ) z^{-n/4} e^{-ζ}` with relative error
`O(1/ζ)` as `z → ∞` in `|ph z| ≤ 3pπ - δ` (DLMF 9.13.12). -/
@[dlmf 9.13.E12]
theorem generalizedAiryB_negative_even_asymptotic {n : ℕ} (hn : 1 ≤ n)  (heven : Even n) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 3 * generalizedAiryOrder n * π) :
    IsBigO (airySector (3 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryB n (-z) - ((1 / (π : ℂ) ^ (1 / 2 : ℂ) * sin ((generalizedAiryOrder n : ℂ) * π)) * z ^ (-(n : ℂ) / 4) * exp (-generalizedAiryZeta n z))) (fun z => ‖z ^ (-(n : ℂ) / 4) * exp (-generalizedAiryZeta n z) / (generalizedAiryZeta n z)‖) := by
  sorry

/-- Scaling the variable of a solution of `w'' = s z^n w`. -/
theorem IsGenAirySol.comp_mul {n : ℕ} {s : ℂ} {f f' : ℂ → ℂ} (hf : IsGenAirySol n s f f') (c : ℂ) :
    IsGenAirySol n (s * c ^ (n + 2)) (fun t => f (c * t)) (fun t => c * f' (c * t)) := fun t =>
  ⟨((hf (c * t)).1.comp t ((hasDerivAt_id t).const_mul c)).congr_deriv (by simp; ring),
    (((hf (c * t)).2.comp t ((hasDerivAt_id t).const_mul c)).const_mul c).congr_deriv
      (by simp; ring)⟩

/-- The second derivative of a solution. -/
theorem IsGenAirySol.deriv_deriv {n : ℕ} {s : ℂ} {f f' : ℂ → ℂ} (hf : IsGenAirySol n s f f')
    (z : ℂ) : deriv (deriv f) z = s * z ^ n * f z := by
  rw [show deriv f = f' from funext fun z => (hf z).1.deriv, (hf z).2.deriv]

/-- `((m/2)^{2/m})^m = m²/4`. -/
theorem olver_scale_pow (n : ℕ) :
    (((((n + 2 : ℕ) : ℂ)) / 2) ^ (2 / (((n + 2 : ℕ) : ℂ)))) ^ (n + 2) =
      ((n + 2 : ℕ) : ℂ) ^ 2 / 4 := by
  have hm : (((n + 2 : ℕ) : ℂ)) ≠ 0 := by norm_cast
  rw [← cpow_nat_mul, show (((n + 2 : ℕ) : ℂ)) * (2 / (((n + 2 : ℕ) : ℂ))) = (2 : ℕ) by
    field_simp; norm_num, cpow_natCast]
  ring

/-- Olver's `U_m` solves `w'' = (m²/4) t^{m-2} w`. -/
theorem isGenAirySol_olverAiryU (n : ℕ) :
    IsGenAirySol n (((n + 2 : ℕ) : ℂ) ^ 2 / 4) (olverAiryU (n + 2))
      (fun t => (2 * π : ℂ) ^ (1 / 2 : ℂ) * ((((n + 2 : ℕ) : ℂ)) / 2) ^
        ((((n + 2 : ℕ) : ℂ) - 1) / ((n + 2 : ℕ) : ℂ)) / sin (π / ((n + 2 : ℕ) : ℂ)) *
        (((((n + 2 : ℕ) : ℂ)) / 2) ^ (2 / (((n + 2 : ℕ) : ℂ))) *
          generalizedAiryADeriv n (((((n + 2 : ℕ) : ℂ)) / 2) ^ (2 / (((n + 2 : ℕ) : ℂ))) * t))) := by
  have h := ((isGenAirySol_generalizedAiryA n).comp_mul
    (((((n + 2 : ℕ) : ℂ)) / 2) ^ (2 / (((n + 2 : ℕ) : ℂ))))).const_mul
    ((2 * π : ℂ) ^ (1 / 2 : ℂ) * ((((n + 2 : ℕ) : ℂ)) / 2) ^
        ((((n + 2 : ℕ) : ℂ) - 1) / ((n + 2 : ℕ) : ℂ)) / sin (π / ((n + 2 : ℕ) : ℂ)))
  rw [olver_scale_pow, one_mul] at h
  exact h.congr (fun t => by simp [olverAiryU]) (fun t => rfl)

/-- Olver's `V̄_m` solves `w'' = (m²/4) t^{m-2} w`. -/
theorem isGenAirySol_olverAiryVBar (n : ℕ) :
    IsGenAirySol n (((n + 2 : ℕ) : ℂ) ^ 2 / 4) (olverAiryVBar (n + 2))
      (fun t => (π : ℂ) ^ (1 / 2 : ℂ) * ((((n + 2 : ℕ) : ℂ)) / 2) ^
        ((((n + 2 : ℕ) : ℂ) - 2) / (2 * ((n + 2 : ℕ) : ℂ))) / sin (π / ((n + 2 : ℕ) : ℂ)) *
        (((((n + 2 : ℕ) : ℂ)) / 2) ^ (2 / (((n + 2 : ℕ) : ℂ))) *
          generalizedAiryBDeriv n (((((n + 2 : ℕ) : ℂ)) / 2) ^ (2 / (((n + 2 : ℕ) : ℂ))) * t))) := by
  have h := ((isGenAirySol_generalizedAiryB n).comp_mul
    (((((n + 2 : ℕ) : ℂ)) / 2) ^ (2 / (((n + 2 : ℕ) : ℂ))))).const_mul
    ((π : ℂ) ^ (1 / 2 : ℂ) * ((((n + 2 : ℕ) : ℂ)) / 2) ^
        ((((n + 2 : ℕ) : ℂ) - 2) / (2 * ((n + 2 : ℕ) : ℂ))) / sin (π / ((n + 2 : ℕ) : ℂ)))
  rw [olver_scale_pow, one_mul] at h
  exact h.congr (fun t => by simp [olverAiryVBar]) (fun t => rfl)

/-- Olver's `U_m` (`V_m` for odd `m`) solves `w'' = (m²/4) t^{m-2} w` (DLMF 9.13.13). -/
@[dlmf 9.13.E13]
theorem olverAiryU_ode {m : ℕ} (hm : 3 ≤ m) (t : ℂ) :
    deriv (deriv (olverAiryU m)) t = (m : ℂ) ^ 2 / 4 * t ^ (m - 2) * olverAiryU m t := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rw [(isGenAirySol_olverAiryU n).deriv_deriv, Nat.add_sub_cancel]

/-- Olver's second solution `V̄_m` solves `w'' = (m²/4) t^{m-2} w` (DLMF 9.13.13). -/
@[dlmf 9.13.E13]
theorem olverAiryVBar_ode {m : ℕ} (hm : 3 ≤ m) (t : ℂ) :
    deriv (deriv (olverAiryVBar m)) t = (m : ℂ) ^ 2 / 4 * t ^ (m - 2) * olverAiryVBar m t := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rw [(isGenAirySol_olverAiryVBar n).deriv_deriv, Nat.add_sub_cancel]

/-- Olver's variable scaling `(m/2)^{2/m} (m/2)^{-2/m} z = z`. -/
theorem olver_scale_cancel (n : ℕ) (z : ℂ) :
    (((n : ℂ) + 2) / 2) ^ (2 / ((n : ℂ) + 2)) * ((((n : ℂ) + 2) / 2) ^ (-2 / ((n : ℂ) + 2)) * z)
      = z := by
  have hc : ((n : ℂ) + 2) / 2 ≠ 0 := by
    have : (n : ℂ) + 2 ≠ 0 := by norm_cast
    exact div_ne_zero this two_ne_zero
  rw [← mul_assoc, ← cpow_add _ _ hc, show 2 / ((n : ℂ) + 2) + -2 / ((n : ℂ) + 2) = 0 by ring,
    cpow_zero, one_mul]

/-- Olver's `U_m` is the rescaled Swanson–Headley `A_{m-2}`:
`(2π)^{1/2} (m/2)^{(m-1)/m} A_n(z)/sin(π/m) = U_m(t)`, `m = n + 2` (DLMF 9.13.15). -/
@[dlmf 9.13.E15]
theorem olverAiry_normalization_first {n : ℕ} (z : ℂ) :
    (2 * π : ℂ) ^ (1 / 2 : ℂ) * ((n + 2 : ℂ) / 2) ^ ((n + 1 : ℂ) / (n + 2 : ℂ)) /
      sin (π / (n + 2 : ℂ)) * generalizedAiryA n z = olverAiryU (n + 2) (olverAiryVariable (n + 2) z) := by
  simp only [olverAiryU, olverAiryVariable, Nat.add_sub_cancel]
  push_cast
  rw [olver_scale_cancel]
  congr 4
  ring

/-- Olver's `V̄_m` is the rescaled `B_{m-2}`:
`π^{1/2} (m/2)^{(m-2)/(2m)} B_n(z)/sin(π/m) = V̄_m(t)`, `m = n + 2` (DLMF 9.13.16). -/
@[dlmf 9.13.E16]
theorem olverAiry_normalization_second {n : ℕ} (z : ℂ) :
    (π : ℂ) ^ (1 / 2 : ℂ) * ((n + 2 : ℂ) / 2) ^ ((n : ℂ) / (2 * (n + 2 : ℂ))) /
      sin (π / (n + 2 : ℂ)) * generalizedAiryB n z = olverAiryVBar (n + 2) (olverAiryVariable (n + 2) z) := by
  simp only [olverAiryVBar, olverAiryVariable, Nat.add_sub_cancel]
  push_cast
  rw [olver_scale_cancel]
  congr 4
  ring

/-- For even `m`, `V̄_m(t) = U_m(-t)` (DLMF 9.13.16). -/
@[dlmf 9.13.E16]
theorem olverAiry_even_second {m : ℕ} (hm : 3 ≤ m) (heven : Even m) (t : ℂ) :
    olverAiryVBar m t = olverAiryU m (-t) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hne : Even n := by simpa [Nat.even_add] using heven
  simp only [olverAiryVBar, olverAiryU, Nat.add_sub_cancel, mul_neg,
    generalizedAiryA_neg_of_even hne]
  have hm0 : (0 : ℝ) < n + 2 := by positivity
  have e1 : ((((n + 2 : ℕ) : ℂ)) / 2) = (((n + 2 : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (generalizedAiryOrder n : ℂ) = (((1 / (n + 2 : ℝ)) : ℝ) : ℂ) := by
    simp [generalizedAiryOrder]
  have e3 : (2 * π : ℂ) = ((2 : ℝ) : ℂ) * ((π : ℝ) : ℂ) := by push_cast; ring
  have hsplit : (((n + 2 : ℕ) : ℂ) - 1) / ((n + 2 : ℕ) : ℂ) =
      (((n + 2 : ℕ) : ℂ) - 2) / (2 * ((n + 2 : ℕ) : ℂ)) + 1 / 2 := by
    have : ((n + 2 : ℕ) : ℂ) ≠ 0 := by norm_cast
    field_simp; ring
  have hc : (((n + 2 : ℝ) / 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (n + 2 : ℝ) / 2 ≠ 0 by positivity)
  rw [hsplit, e1, e2, e3, cpow_add _ _ hc, mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le]
  have key : ((2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) * (((n + 2 : ℝ) / 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      (((1 / (n + 2 : ℝ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) = 1 := by
    rw [← mul_cpow_ofReal_nonneg (by norm_num) (by positivity),
      ← Complex.ofReal_mul, ← mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      ← Complex.ofReal_mul]
    rw [show (2 * ((n + 2 : ℝ) / 2) * (1 / (n + 2 : ℝ))) = 1 by field_simp]
    simp
  linear_combination (-(((π : ℝ) : ℂ) ^ (1 / 2 : ℂ) * (((n + 2 : ℝ) / 2 : ℝ) : ℂ) ^
    ((((n + 2 : ℕ) : ℂ) - 2) / (2 * ((n + 2 : ℕ) : ℂ))) / sin (π / ((n + 2 : ℕ) : ℂ)) *
    generalizedAiryB n ((((n + 2 : ℝ) / 2 : ℝ) : ℂ) ^ (2 / ((n + 2 : ℕ) : ℂ)) * t))) * key

/-- The order `p` as `1/m` with `m = n+2`. -/
theorem generalizedAiryOrder_cast (n : ℕ) :
    (generalizedAiryOrder n : ℂ) = (((n + 2 : ℕ) : ℂ))⁻¹ := by
  simp [generalizedAiryOrder]

/-- Olver's oscillatory `W_m` solves `w'' = -(m²/4) t^{m-2} w` (DLMF 9.13.17). -/
@[dlmf 9.13.E17]
theorem olverAiryW_ode {m : ℕ} (hm : 3 ≤ m) (t : ℂ) :
    deriv (deriv (olverAiryW m)) t = -(m : ℂ) ^ 2 / 4 * t ^ (m - 2) * olverAiryW m t := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  set c : ℂ := ((((n + 2 : ℕ) : ℂ)) / 2) ^ (2 / (((n + 2 : ℕ) : ℂ)))
  have hF := (isGenAirySol_F n (-1)).comp_mul c
  have hG := (isGenAirySol_G n (-1)).comp_mul c
  rw [olver_scale_pow, generalizedAiryOrder_cast] at hF hG
  set p : ℂ := (((n + 2 : ℕ) : ℂ))⁻¹
  have h := ((hF.const_mul (Gamma p * Gamma (1 - p))).add
    (hG.const_mul (Gamma (-p) / (((n + 2 : ℕ) : ℂ)) ^ (2 * p) * Gamma (1 + p)))).const_mul
      ((2 : ℂ) ^ ((((n + 2 : ℕ) : ℂ) + 2) / (2 * ((n + 2 : ℕ) : ℂ))) / (2 * (π : ℂ) ^ (1 / 2 : ℂ)))
  have hc : c = ((((n + 2 : ℕ) : ℂ)) / 2) ^ (2 * p) := by simp only [c, p]; ring_nf
  have harg : ∀ t : ℂ, -(c * t) ^ (n + 2) / (((n + 2 : ℕ) : ℂ)) ^ 2 =
      -1 * (c * t) ^ (n + 2) / ((n : ℂ) + 2) ^ 2 := fun t => by push_cast; ring
  have h' := h.congr (g := olverAiryW (n + 2)) (fun t => by
    simp only [olverAiryW]
    rw [← hc, harg]
    ring) (fun t => rfl)
  rw [h'.deriv_deriv, Nat.add_sub_cancel]
  ring

/-- Each rotation `t ↦ U_m(t e^{-2jπi/m})` also solves `w'' = (m²/4) t^{m-2} w`
(DLMF 9.13.18). -/
@[dlmf 9.13.E18]
theorem olverAiry_rotated_solution {m : ℕ} (hm : 3 ≤ m) (j : ℤ) (z : ℂ) :
    deriv (deriv (fun t => olverAiryU m (t * exp (-2 * j * π * I / m)))) z =
      (m : ℂ) ^ 2 / 4 * z ^ (m - 2) * olverAiryU m (z * exp (-2 * j * π * I / m)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hm : (((n + 2 : ℕ) : ℂ)) ≠ 0 := by norm_cast
  have hω : exp (-2 * j * π * I / ((n + 2 : ℕ) : ℂ)) ^ (n + 2) = 1 := by
    rw [← exp_nat_mul, show (((n + 2 : ℕ) : ℕ) : ℂ) * (-2 * j * π * I / ((n + 2 : ℕ) : ℂ)) =
      (-j : ℤ) * (2 * π * I) by
        have : (n : ℂ) + 2 ≠ 0 := by norm_cast
        push_cast; field_simp, exp_int_mul_two_pi_mul_I]
  have h := (isGenAirySol_olverAiryU n).comp_mul (exp (-2 * j * π * I / ((n + 2 : ℕ) : ℂ)))
  rw [hω, mul_one] at h
  have h' := h.congr (g := fun t => olverAiryU (n + 2) (t * exp (-2 * j * π * I / ((n + 2 : ℕ) : ℂ))))
    (fun t => by simp only [mul_comm]) (fun t => rfl)
  rw [h'.deriv_deriv, Nat.add_sub_cancel]

/-- The Smirnov argument `w(t) = -t^m/m²` as a complex number. -/
def smirnovArg (m t : ℝ) : ℂ := ((-(t ^ m / m ^ 2) : ℝ) : ℂ)

/-- Derivative of `₀F̃₁(;c; -t^m/m²)` on `t > 0`. -/
theorem hasDerivAt_smirnovF (m : ℝ) (c : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => regularizedHGFun (∅ : Multiset ℂ) {c} (smirnovArg m t))
      (((-(t ^ (m - 1) / m)) : ℝ) * regularizedHGFun (∅ : Multiset ℂ) {c + 1} (smirnovArg m t)) t := by
  have hw : HasDerivAt (fun t : ℝ => -(t ^ m / m ^ 2)) (-(m * t ^ (m - 1) / m ^ 2)) t :=
    ((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).div_const _).neg
  have h := (DLMF.Bessel.hasDerivAt_regularized0F1 c (smirnovArg m t)).comp t hw.ofReal_comp
  refine h.congr_deriv ?_
  rw [mul_comm]
  congr 1
  push_cast
  field_simp

/-- The even Smirnov solution `₀F̃₁(;1-1/m;-t^m/m²)` of `y'' + t^{m-2} y = 0` on `t > 0`. -/
theorem smirnov_even_ode {m : ℝ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => regularizedHGFun (∅ : Multiset ℂ) {1 - 1 / (m : ℂ)} (smirnovArg m t))
        (((-(t ^ (m - 1) / m)) : ℝ) *
          regularizedHGFun (∅ : Multiset ℂ) {2 - 1 / (m : ℂ)} (smirnovArg m t)) t ∧
      HasDerivAt (fun t : ℝ => (((-(t ^ (m - 1) / m)) : ℝ) : ℂ) *
          regularizedHGFun (∅ : Multiset ℂ) {2 - 1 / (m : ℂ)} (smirnovArg m t))
        (-((t ^ (m - 2) : ℝ) : ℂ) *
          regularizedHGFun (∅ : Multiset ℂ) {1 - 1 / (m : ℂ)} (smirnovArg m t)) t := by
  have hm0 : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
  refine ⟨(hasDerivAt_smirnovF m _ ht).congr_deriv (by ring_nf), ?_⟩
  have h1 : HasDerivAt (fun t : ℝ => -(t ^ (m - 1) / m)) (-((m - 1) * t ^ (m - 1 - 1) / m)) t :=
    ((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).div_const _).neg
  have h2 := hasDerivAt_smirnovF m (2 - 1 / (m : ℂ)) ht
  refine (h1.ofReal_comp.mul h2).congr_deriv ?_
  have hc := reg0F1_contiguous' (c := 1 - 1 / (m : ℂ)) (c₁ := 2 - 1 / (m : ℂ))
    (c₂ := 2 - 1 / (m : ℂ) + 1) (by ring) (by ring) (smirnovArg m t)
  rw [hc]
  have e1 : t ^ (m - 1) * t ^ (m - 1) = t ^ (m - 2) * t ^ m := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]; ring_nf
  have e1c : ((t ^ (m - 1) : ℝ) : ℂ) * ((t ^ (m - 1) : ℝ) : ℂ) =
      ((t ^ (m - 2) : ℝ) : ℂ) * ((t ^ m : ℝ) : ℂ) := by exact_mod_cast e1
  generalize regularizedHGFun (∅ : Multiset ℂ) {2 - 1 / (m : ℂ)} (smirnovArg m t) = A
  generalize regularizedHGFun (∅ : Multiset ℂ) {2 - 1 / (m : ℂ) + 1} (smirnovArg m t) = B
  simp only [smirnovArg, show m - 1 - 1 = m - 2 by ring]
  push_cast
  field_simp
  linear_combination B * e1c

/-- The odd Smirnov solution `t ₀F̃₁(;1+1/m;-t^m/m²)` of `y'' + t^{m-2} y = 0` on `t > 0`. -/
theorem smirnov_odd_ode {m : ℝ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => (t : ℂ) *
          regularizedHGFun (∅ : Multiset ℂ) {1 + 1 / (m : ℂ)} (smirnovArg m t))
        (regularizedHGFun (∅ : Multiset ℂ) {1 + 1 / (m : ℂ)} (smirnovArg m t) +
          (((-(t ^ m / m)) : ℝ) : ℂ) *
            regularizedHGFun (∅ : Multiset ℂ) {1 + 1 / (m : ℂ) + 1} (smirnovArg m t)) t ∧
      HasDerivAt (fun t : ℝ => regularizedHGFun (∅ : Multiset ℂ) {1 + 1 / (m : ℂ)} (smirnovArg m t) +
          (((-(t ^ m / m)) : ℝ) : ℂ) *
            regularizedHGFun (∅ : Multiset ℂ) {1 + 1 / (m : ℂ) + 1} (smirnovArg m t))
        (-((t ^ (m - 2) : ℝ) : ℂ) * ((t : ℂ) *
          regularizedHGFun (∅ : Multiset ℂ) {1 + 1 / (m : ℂ)} (smirnovArg m t))) t := by
  have hm0 : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hF1 := hasDerivAt_smirnovF m (1 + 1 / (m : ℂ)) ht
  have hF2 := hasDerivAt_smirnovF m (1 + 1 / (m : ℂ) + 1) ht
  have e0 : t * t ^ (m - 1) = t ^ m := by
    rw [mul_comm, ← Real.rpow_add_one ht.ne']; ring_nf
  have e0c : (t : ℂ) * ((t ^ (m - 1) : ℝ) : ℂ) = ((t ^ m : ℝ) : ℂ) := by exact_mod_cast e0
  constructor
  · refine ((hasDerivAt_id t).ofReal_comp.mul hF1).congr_deriv ?_
    simp only [id]
    push_cast
    linear_combination (-(1 / (m : ℂ)) *
      regularizedHGFun (∅ : Multiset ℂ) {1 + 1 / (m : ℂ) + 1} (smirnovArg m t)) * e0c
  · have h1 : HasDerivAt (fun t : ℝ => -(t ^ m / m)) (-(m * t ^ (m - 1) / m)) t :=
      ((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).div_const _).neg
    refine (hF1.add (h1.ofReal_comp.mul hF2)).congr_deriv ?_
    have hc := reg0F1_contiguous' (c := 1 + 1 / (m : ℂ)) (c₁ := 1 + 1 / (m : ℂ) + 1)
      (c₂ := 1 + 1 / (m : ℂ) + 1 + 1) (by ring) (by ring) (smirnovArg m t)
    rw [hc]
    have e1 : t ^ (m - 2) * t = t ^ (m - 1) := by
      rw [← Real.rpow_add_one ht.ne']; ring_nf
    have e1c : ((t ^ (m - 2) : ℝ) : ℂ) * (t : ℂ) = ((t ^ (m - 1) : ℝ) : ℂ) := by exact_mod_cast e1
    generalize regularizedHGFun (∅ : Multiset ℂ) {1 + 1 / (m : ℂ) + 1} (smirnovArg m t) = A
    generalize regularizedHGFun (∅ : Multiset ℂ) {1 + 1 / (m : ℂ) + 1 + 1} (smirnovArg m t) = B
    simp only [smirnovArg]
    push_cast
    field_simp
    linear_combination (-(-((m : ℂ) * ((m : ℂ) + 1) * A) + ((t ^ m : ℝ) : ℂ) * B)) * e1c

/-- On `t > 0`, `t^{1/2} J_ν((2/m) t^{m/2})` is `m^{-ν} t^{1/2+mν/2} ₀F̃₁(;ν+1;-t^m/m²)`. -/
theorem cpow_half_mul_besselJ_smirnov {m : ℝ} (hm : 0 < m) (ν : ℝ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (1 / 2 : ℂ) * besselJ (ν : ℂ) (2 / (m : ℂ) * (t : ℂ) ^ ((m : ℂ) / 2)) =
      ((m ^ (-ν) * t ^ (1 / 2 + m * ν / 2) : ℝ) : ℂ) *
        regularizedHGFun (∅ : Multiset ℂ) {(ν : ℂ) + 1} (smirnovArg m t) := by
  have hz : 2 / (m : ℂ) * (t : ℂ) ^ ((m : ℂ) / 2) = ((2 / m * t ^ (m / 2) : ℝ) : ℂ) := by
    rw [ofReal_mul, ofReal_cpow ht.le]; push_cast; ring
  rw [hz, DLMF.Bessel.besselJ_eq_regularized]
  have hw : -((((2 / m * t ^ (m / 2) : ℝ) : ℂ)) ^ 2 / 4) = smirnovArg m t := by
    rw [smirnovArg]
    have : (2 / m * t ^ (m / 2)) ^ 2 / 4 = t ^ m / m ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast (t ^ (m / 2)), ← Real.rpow_mul ht.le]
      field_simp
      norm_num
    rw [← this]; push_cast; ring
  rw [hw]
  have h2 : ((2 / m * t ^ (m / 2) : ℝ) : ℂ) / 2 = ((t ^ (m / 2) / m : ℝ) : ℂ) := by
    push_cast; ring
  rw [h2, ← ofReal_cpow (by positivity), show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow ht.le, ← mul_assoc, ← ofReal_mul]
  congr 2
  rw [Real.div_rpow (by positivity) hm.le, ← Real.rpow_mul ht.le, Real.rpow_neg hm.le,
    Real.rpow_add ht]
  field_simp

/-- From a local representation `f = K Y` on `t > 0` with `Y'' = -t^{m-2} Y`, the ODE for `f`. -/
theorem smirnov_ode_of_eq {f Y Y' : ℝ → ℂ} {m x : ℝ} (hx : 0 < x) (K : ℂ)
    (hf : ∀ t, 0 < t → f t = K * Y t)
    (hY : ∀ t, 0 < t → HasDerivAt Y (Y' t) t ∧
      HasDerivAt Y' (-((t ^ (m - 2) : ℝ) : ℂ) * Y t) t) :
    deriv (deriv f) x + (x ^ (m - 2) : ℝ) • f x = 0 := by
  have hev2 : deriv f =ᶠ[𝓝 x] fun t => K * Y' t := by
    filter_upwards [Ioi_mem_nhds hx] with t (ht : 0 < t)
    have hev : f =ᶠ[𝓝 t] fun t => K * Y t := by
      filter_upwards [Ioi_mem_nhds ht] with u (hu : 0 < u) using hf u hu
    rw [hev.deriv_eq]
    exact ((hY t ht).1.const_mul K).deriv
  rw [hev2.deriv_eq, ((hY x hx).2.const_mul K).deriv, hf x hx, Complex.real_smul]
  ring

/-- Smirnov's `U₁(x, α)` solves `w'' + x^α w = 0` on `x > 0`, for `α > -2` (DLMF 9.13.19). -/
@[dlmf 9.13.E19]
theorem smirnovAiryU1_ode {α x : ℝ} (hα : -2 < α) (hx : 0 < x) :
    deriv (deriv (fun t : ℝ => smirnovAiryU1 t α)) x + (x ^ α : ℝ) • smirnovAiryU1 x α = 0 := by
  set m : ℝ := α + 2 with hmdef
  have hm : 0 < m := by linarith
  have hαm : α = m - 2 := by ring
  have hmc : (α : ℂ) + 2 = (m : ℂ) := by push_cast [hmdef]; ring
  have key := smirnov_ode_of_eq (m := m) (f := fun t : ℝ => smirnovAiryU1 t α) hx
    (((α + 2 : ℝ) : ℂ) ^ (-1 / ((α : ℂ) + 2)) * Gamma (((α : ℂ) + 1) / (α + 2)) *
      ((m ^ (-(-1 / m)) * 1 : ℝ) : ℂ))
    (Y := fun t => regularizedHGFun (∅ : Multiset ℂ) {1 - 1 / (m : ℂ)} (smirnovArg m t))
    (fun t ht => by
      have h := cpow_half_mul_besselJ_smirnov hm (-1 / m) ht
      rw [show 1 / 2 + m * (-1 / m) / 2 = 0 by field_simp; ring, Real.rpow_zero,
        show ((-1 / m : ℝ) : ℂ) + 1 = 1 - 1 / (m : ℂ) by push_cast; ring] at h
      simp only [smirnovAiryU1]
      rw [hmc, mul_assoc _ ((t : ℂ) ^ (1 / 2 : ℂ)),
        show (-1 / (m : ℂ)) = ((-1 / m : ℝ) : ℂ) by push_cast; ring, h]
      ring)
    (fun t ht => smirnov_even_ode hm ht)
  rw [← hαm] at key
  exact key

/-- Smirnov's `U₂(x, α)` solves `w'' + x^α w = 0` on `x > 0`, for `α > -2` (DLMF 9.13.19). -/
@[dlmf 9.13.E19]
theorem smirnovAiryU2_ode {α x : ℝ} (hα : -2 < α) (hx : 0 < x) :
    deriv (deriv (fun t : ℝ => smirnovAiryU2 t α)) x + (x ^ α : ℝ) • smirnovAiryU2 x α = 0 := by
  set m : ℝ := α + 2 with hmdef
  have hm : 0 < m := by linarith
  have hαm : α = m - 2 := by ring
  have hmc : (α : ℂ) + 2 = (m : ℂ) := by push_cast [hmdef]; ring
  have key := smirnov_ode_of_eq (m := m) (f := fun t : ℝ => smirnovAiryU2 t α) hx
    (((α + 2 : ℝ) : ℂ) ^ (1 / ((α : ℂ) + 2)) * Gamma (((α : ℂ) + 3) / (α + 2)) *
      ((m ^ (-(1 / m)) : ℝ) : ℂ))
    (Y := fun t => (t : ℂ) * regularizedHGFun (∅ : Multiset ℂ) {1 + 1 / (m : ℂ)} (smirnovArg m t))
    (fun t ht => by
      have h := cpow_half_mul_besselJ_smirnov hm (1 / m) ht
      rw [show 1 / 2 + m * (1 / m) / 2 = 1 by field_simp; ring, Real.rpow_one,
        show ((1 / m : ℝ) : ℂ) + 1 = 1 + 1 / (m : ℂ) by push_cast; ring] at h
      simp only [smirnovAiryU2]
      rw [hmc, mul_assoc _ ((t : ℂ) ^ (1 / 2 : ℂ)),
        show (1 / (m : ℂ)) = ((1 / m : ℝ) : ℂ) by push_cast; ring, h]
      push_cast
      ring)
    (fun t ht => smirnov_odd_ode hm ht)
  rw [← hαm] at key
  exact key

/-- Smirnov's `U₁` as a regularized `₀F₁` on `x > 0`. -/
lemma smirnovAiryU1_eq {α x : ℝ} (hα : -2 < α) (hx : 0 < x) :
    smirnovAiryU1 x α = Gamma (1 - 1 / ((α + 2 : ℝ) : ℂ)) *
      regularizedHGFun (∅ : Multiset ℂ) {1 - 1 / ((α + 2 : ℝ) : ℂ)} (smirnovArg (α + 2) x) := by
  have hm : 0 < α + 2 := by linarith
  have h := cpow_half_mul_besselJ_smirnov hm (-1 / (α + 2)) hx
  rw [show 1 / 2 + (α + 2) * (-1 / (α + 2)) / 2 = 0 by field_simp; ring, Real.rpow_zero,
    show ((-1 / (α + 2) : ℝ) : ℂ) + 1 = 1 - 1 / ((α + 2 : ℝ) : ℂ) by push_cast; ring] at h
  have hmc : (α : ℂ) + 2 = ((α + 2 : ℝ) : ℂ) := by push_cast; ring
  have hm0 : ((α + 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
  have hg : ((α : ℂ) + 1) / ((α + 2 : ℝ) : ℂ) = 1 - 1 / ((α + 2 : ℝ) : ℂ) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hm0]; push_cast; ring
  simp only [smirnovAiryU1]
  rw [hmc, mul_assoc _ ((x : ℂ) ^ (1 / 2 : ℂ)),
    show (-1 / ((α + 2 : ℝ) : ℂ)) = ((-1 / (α + 2) : ℝ) : ℂ) by push_cast; ring, h,
    ← ofReal_cpow hm.le, hg]
  rw [mul_comm _ (Gamma _), mul_assoc, ← mul_assoc (((α + 2) ^ (-1 / (α + 2)) : ℝ) : ℂ),
    ← ofReal_mul, Real.rpow_neg hm.le, neg_div, Real.rpow_neg hm.le, inv_inv, mul_one,
    inv_mul_cancel₀ (by positivity), ofReal_one, one_mul]

/-- Smirnov's `U₂` as `x` times a regularized `₀F₁` on `x > 0`. -/
lemma smirnovAiryU2_eq {α x : ℝ} (hα : -2 < α) (hx : 0 < x) :
    smirnovAiryU2 x α = Gamma (1 + 1 / ((α + 2 : ℝ) : ℂ)) * ((x : ℂ) *
      regularizedHGFun (∅ : Multiset ℂ) {1 + 1 / ((α + 2 : ℝ) : ℂ)} (smirnovArg (α + 2) x)) := by
  have hm : 0 < α + 2 := by linarith
  have h := cpow_half_mul_besselJ_smirnov hm (1 / (α + 2)) hx
  rw [show 1 / 2 + (α + 2) * (1 / (α + 2)) / 2 = 1 by field_simp; ring, Real.rpow_one,
    show ((1 / (α + 2) : ℝ) : ℂ) + 1 = 1 + 1 / ((α + 2 : ℝ) : ℂ) by push_cast; ring] at h
  have hmc : (α : ℂ) + 2 = ((α + 2 : ℝ) : ℂ) := by push_cast; ring
  have hm0 : ((α + 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
  have hg : ((α : ℂ) + 3) / ((α + 2 : ℝ) : ℂ) = 1 + 1 / ((α + 2 : ℝ) : ℂ) := by
    rw [← sub_eq_iff_eq_add, ← sub_div, div_eq_one_iff_eq hm0]; push_cast; ring
  simp only [smirnovAiryU2]
  rw [hmc, mul_assoc _ ((x : ℂ) ^ (1 / 2 : ℂ)),
    show (1 / ((α + 2 : ℝ) : ℂ)) = ((1 / (α + 2) : ℝ) : ℂ) by push_cast; ring, h,
    ← ofReal_cpow hm.le, hg]
  have hr : (α + 2) ^ (1 / (α + 2)) * ((α + 2) ^ (-(1 / (α + 2))) * x) = x := by
    rw [Real.rpow_neg hm.le, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  rw [mul_comm _ (Gamma _), mul_assoc, ← mul_assoc (((α + 2) ^ (1 / (α + 2)) : ℝ) : ℂ),
    ← ofReal_mul, hr]
  push_cast
  rfl

/-- For even `m`, `W_m(t) + W_m(-t)` isolates the even fundamental solution. -/
theorem olverAiryW_add_neg {m : ℕ} (hme : Even m) (t : ℂ) :
    olverAiryW m t + olverAiryW m (-t) =
      2 * ((2 : ℂ) ^ (((m : ℂ) + 2) / (2 * m)) / (2 * (π : ℂ) ^ (1 / 2 : ℂ))) *
        (Gamma (m : ℂ)⁻¹ * Gamma (1 - (m : ℂ)⁻¹)) *
          regularizedHGFun ∅ {1 - (m : ℂ)⁻¹}
            (-(((m : ℂ) / 2) ^ (2 * (m : ℂ)⁻¹) * t) ^ m / (m : ℂ) ^ 2) := by
  simp only [olverAiryW]
  rw [mul_neg, hme.neg_pow]
  ring

/-- For even `m`, `W_m(t) - W_m(-t)` isolates the odd fundamental solution. -/
theorem olverAiryW_sub_neg {m : ℕ} (hme : Even m) (t : ℂ) :
    olverAiryW m t - olverAiryW m (-t) =
      2 * ((2 : ℂ) ^ (((m : ℂ) + 2) / (2 * m)) / (2 * (π : ℂ) ^ (1 / 2 : ℂ))) *
        (Gamma (-(m : ℂ)⁻¹) / (m : ℂ) ^ (2 * (m : ℂ)⁻¹) * Gamma (1 + (m : ℂ)⁻¹)) *
          ((((m : ℂ) / 2) ^ (2 * (m : ℂ)⁻¹) * t) * regularizedHGFun ∅ {1 + (m : ℂ)⁻¹}
            (-(((m : ℂ) / 2) ^ (2 * (m : ℂ)⁻¹) * t) ^ m / (m : ℂ) ^ 2)) := by
  simp only [olverAiryW]
  rw [mul_neg, hme.neg_pow]
  ring

/-- The Olver variable `((m/2)^{2/m} t)` as a complex number, and its Smirnov argument. -/
theorem smirnovAiryVariable_ofReal (m : ℕ) (hm : 0 < m) (t : ℝ) :
    ((((m : ℝ) / 2) ^ (2 / (m : ℝ)) * t : ℝ) : ℂ) = ((m : ℂ) / 2) ^ (2 * (m : ℂ)⁻¹) * t ∧
      smirnovArg (m : ℝ) (((m : ℝ) / 2) ^ (2 / (m : ℝ)) * t) =
        -(((m : ℂ) / 2) ^ (2 * (m : ℂ)⁻¹) * t) ^ m / (m : ℂ) ^ 2 := by
  have h1 : ((((m : ℝ) / 2) ^ (2 / (m : ℝ)) * t : ℝ) : ℂ) = ((m : ℂ) / 2) ^ (2 * (m : ℂ)⁻¹) * t := by
    rw [ofReal_mul, ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  refine ⟨h1, ?_⟩
  rw [smirnovArg, ← h1, Real.rpow_natCast]
  push_cast
  ring

/-- smirnovAiryU1 olver (DLMF 9.13.23). DLMF defines `W_m(±t)` for even `m` (9.13.17);
the evenness hypothesis was added on 2026-10-20, since for odd `m` the term of order
`t^m` in `W_m(-t)` does not cancel. -/
@[dlmf 9.13.E23]
theorem smirnovAiryU1_olver {m : ℕ} (hm : 3 ≤ m) (hme : Even m) {t : ℝ} (ht : 0 < t) :
    smirnovAiryU1 (((m : ℝ) / 2) ^ (2 / (m : ℝ)) * t) (m - 2 : ℝ) =
      ((π : ℂ) ^ (1 / 2 : ℂ) / ((2 : ℂ) ^ (((m : ℂ) + 2) / (2 * m)) * Gamma (1 / (m : ℂ)))) * (olverAiryW m t + olverAiryW m (-t)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hx : 0 < ((m : ℝ) / 2) ^ (2 / (m : ℝ)) * t := by positivity
  rw [smirnovAiryU1_eq (by linarith) hx, show (m : ℝ) - 2 + 2 = m by ring,
    (smirnovAiryVariable_ofReal m (by omega) t).2, olverAiryW_add_neg hme]
  have hmc : (((m : ℕ) : ℝ) : ℂ) = (m : ℂ) := ofReal_natCast m
  rw [hmc, one_div]
  have hG : Gamma (m : ℂ)⁻¹ ≠ 0 := by
    refine Gamma_ne_zero fun k hk => ?_
    have := congrArg Complex.re hk
    simp at this
    have : (0 : ℝ) < (m : ℝ)⁻¹ := by positivity
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h2 : (2 : ℂ) ^ (((m : ℂ) + 2) / (2 * m)) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hpi : (π : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  field_simp
  exact (mul_div_cancel_right₀ _ (by rwa [one_div])).symm

/-- smirnovAiryU2 olver (DLMF 9.13.24). DLMF defines `W_m(±t)` for even `m` (9.13.17);
the evenness hypothesis was added on 2026-10-20, since for odd `m` the term of order
`t^m` in `W_m(-t)` does not cancel. -/
@[dlmf 9.13.E24]
theorem smirnovAiryU2_olver {m : ℕ} (hm : 3 ≤ m) (hme : Even m) {t : ℝ} (ht : 0 < t) :
    smirnovAiryU2 (((m : ℝ) / 2) ^ (2 / (m : ℝ)) * t) (m - 2 : ℝ) =
      ((π : ℂ) ^ (1 / 2 : ℂ) * (m : ℂ) ^ (2 / (m : ℂ)) / ((2 : ℂ) ^ (((m : ℂ) + 2) / (2 * m)) * Gamma (-1 / (m : ℂ)))) * (olverAiryW m t - olverAiryW m (-t)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hx : 0 < ((m : ℝ) / 2) ^ (2 / (m : ℝ)) * t := by positivity
  rw [smirnovAiryU2_eq (by linarith) hx, show (m : ℝ) - 2 + 2 = m by ring,
    (smirnovAiryVariable_ofReal m (by omega) t).2, (smirnovAiryVariable_ofReal m (by omega) t).1,
    olverAiryW_sub_neg hme]
  have hmc : (((m : ℕ) : ℝ) : ℂ) = (m : ℂ) := ofReal_natCast m
  rw [hmc, one_div, neg_div, one_div, div_eq_mul_inv (2 : ℂ)]
  have hG : Gamma (-(m : ℂ)⁻¹) ≠ 0 := by
    refine Gamma_ne_zero fun k hk => ?_
    have := congrArg Complex.re hk
    simp at this
    have h1 : (m : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < m))
    have h0 : (0 : ℝ) < (m : ℝ)⁻¹ := by positivity
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at this; linarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
  have h2 : (2 : ℂ) ^ (((m : ℂ) + 2) / (2 * m)) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hpi : (π : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hmm : (m : ℂ) ^ (2 * (m : ℂ)⁻¹) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (by omega : m ≠ 0)))
  field_simp
  exact (mul_div_cancel_right₀ _ (by rwa [one_div])).symm

/-- Smirnov/Olver variable conversion, DLMF 9.13.22. -/
@[dlmf 9.13.E22]
def smirnovAiryVariable (m : ℕ) (t : ℝ) : ℝ := ((m : ℝ) / 2) ^ (2 / (m : ℝ)) * t

/-- The generalized equation's global initial-data solution space. -/
@[dlmf 9.13.E2]
theorem generalizedAiry_general_solution {n : ℕ} (hn : 1 ≤ n) {w w' : ℂ → ℂ}
    (hw : ∀ z, HasDerivAt w (w' z) z ∧ HasDerivAt w' (z ^ n * w z) z) :
    ∃ a b : ℂ, ∀ z, w z = a * generalizedAiryA n z + b * generalizedAiryB n z := by
  have hW := generalizedAiry_wronskian hn 0
  rw [deriv_generalizedAiryA, deriv_generalizedAiryB] at hW
  refine (isGenAirySol_generalizedAiryA n).eq_combination (isGenAirySol_generalizedAiryB n)
    (w' := w') (fun z => ⟨(hw z).1, by simpa using (hw z).2⟩) ?_
  rw [hW]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp := generalizedAiryOrder_ne_zero n
  exact mul_ne_zero (mul_ne_zero (div_ne_zero two_ne_zero hpi) (by
    rw [Ne, cpow_eq_zero_iff]; tauto)) (generalizedAiryOrder_sin_ne_zero n)

/-- Olver's rotated solution is recessive relative to its dominant companion in every
closed subsector of its stated recessive sector, DLMF §9.13(i). -/
@[dlmf 9.13.E18]
theorem olverAiry_rotated_recessive {m : ℕ} (hm : 3 ≤ m) (j : ℤ)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / m) :
    IsLittleO (comap (fun z : ℂ => z * exp (-2 * j * π * I / m)) (airySector (π / m - δ)))
      (fun z => olverAiryU m (z * exp (-2 * j * π * I / m)))
      (fun z => olverAiryVBar m (z * exp (-2 * j * π * I / m))) := by
  sorry

end DLMF.Airy
