/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Weber
public import DLMF.ParabolicCylinder.Hermite
public import DLMF.OrthogonalPolynomials.ClassicalInstances
public import DLMFMathlib.Analysis.ODE.SturmDeformation

/-!
# Cylinder asymptotic sectors and real and complex zeros

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- pcfUTerm. -/
def pcfUTerm (a z : ℂ) (s : ℕ) : ℂ :=
  (-1)^s*poch (1/2+a) (2*s)/((s.factorial:ℂ)*(2*z^2)^s)

/-- pcfVTerm. -/
def pcfVTerm (a z : ℂ) (s : ℕ) : ℂ :=
  poch (1/2-a) (2*s)/((s.factorial:ℂ)*(2*z^2)^s)

/-- pcfU sector asymptotic. -/
@[dlmf 12.9.E1]
theorem pcfU_sector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < 3*π/4) (N : ℕ) :
    (fun z : ℂ => exp (z^2/4)*z^(a+1/2)*pcfU a z-∑ s ∈ Finset.range N, pcfUTerm a z s) =O[sector (3*π/4-δ)] (fun z : ℂ => z^(-(2*N:ℤ))) := by
  exact pcfSect_U_sector a hδ N

/-- pcfV sector asymptotic. -/
@[dlmf 12.9.E2]
theorem pcfV_sector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/4) (N : ℕ) :
    (fun z : ℂ => (Real.sqrt (π/2):ℂ)*exp (-z^2/4)*z^(-a+1/2)*pcfV a z-∑ s ∈ Finset.range N, pcfVTerm a z s) =O[sector (π/4-δ)] (fun z : ℂ => z^(-(2*N:ℤ))) := by
  exact pcfSect_V_sector a hδ hδπ N

/-- pcfLogWedge. -/
def pcfLogWedge (lo hi : ℝ) : Filter ℂ :=
  comap (fun w : ℂ => Real.exp w.re) atTop ⊓ 𝓟 {w : ℂ | lo ≤ w.im ∧ w.im ≤ hi}

/-- Two-exponential expansion with an absolute sum-of-envelopes remainder and inherited powers. -/
@[dlmf 12.9.E3]
theorem pcfU_adjacent_asymptotic_pos (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun w : ℂ => pcfU a (exp w)-(exp (-exp (2*w)/4-(a+1/2)*w)*(∑ j ∈ Finset.range N, pcfUTerm a (exp w) j)+(1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(1:ℂ)*I*π*a)*exp (exp (2*w)/4+(a-1/2)*w)*(∑ j ∈ Finset.range N, pcfVTerm a (exp w) j))) =O[pcfLogWedge (π/4+δ) (5*π/4-δ)] (fun w : ℂ => ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ)) := by
  have h1 := pcfSect_U_logWedge a hδ (-π) (lo := π/4+δ) (hi := 5*π/4-δ) (by linarith) (by linarith) N
  have h2 := pcfSect_U_logWedge (-a) hδ (-(π/2)) (lo := π/4+δ) (hi := 5*π/4-δ) (by linarith) (by linarith) N
  set C1 : ℂ := (-1:ℂ)*I*exp ((-1:ℂ)*I*π*a)
  set C2 : ℂ := (Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp ((-1:ℂ)*I*π*(a/2-1/4))
  have e2a : ∀ w : ℂ, exp (2 * (w + ((-π : ℝ) : ℂ) * I)) = exp (2 * w) := fun w => by
    rw [pcfSect_exp_two_mul_add]
    rw [show (((2 * -π : ℝ)) : ℂ) * I = ((-1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have e2b : ∀ w : ℂ, exp (2 * (w + ((-(π/2) : ℝ) : ℂ) * I)) = -exp (2 * w) := fun w => by
    rw [pcfSect_exp_two_mul_add]
    rw [show (((2 * -(π/2) : ℝ)) : ℂ) * I = -(π * I) by push_cast; ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]; ring
  have hIexp : I = exp (π / 2 * I) := Complex.exp_pi_div_two_mul_I.symm
  have hm1 : (-1 : ℂ) = exp (π * I) := Complex.exp_pi_mul_I.symm
  have hA : ∀ w, C1 * exp (-exp (2 * (w + ((-π : ℝ) : ℂ) * I)) / 4 -
      (a + 1 / 2) * (w + ((-π : ℝ) : ℂ) * I)) = exp (-exp (2*w)/4-(a+1/2)*w) := fun w => by
    have hC1 : C1 = exp (π * I + π / 2 * I + (-1:ℂ) * I * π * a) := by
      rw [Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
    rw [hC1, e2a, ← Complex.exp_add]
    exact pcfSect_exp_eq_of_eq_add 1 (by push_cast; ring)
  have hB : ∀ w, C2 * exp (-exp (2 * (w + ((-(π/2) : ℝ) : ℂ) * I)) / 4 -
      (-a + 1 / 2) * (w + ((-(π/2) : ℝ) : ℂ) * I)) = (1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(1:ℂ)*I*π*a) * exp (exp (2*w)/4+(a-1/2)*w) := fun w => by
    have h1 : C2 * exp (-exp (2 * (w + ((-(π/2) : ℝ) : ℂ) * I)) / 4 -
        (-a + 1 / 2) * (w + ((-(π/2) : ℝ) : ℂ) * I)) = (Real.sqrt (2*π):ℂ)/Gamma (1/2+a) *
        exp ((-1:ℂ)*I*π*(a/2-1/4) + (-exp (2 * (w + ((-(π/2) : ℝ) : ℂ) * I)) / 4 -
        (-a + 1 / 2) * (w + ((-(π/2) : ℝ) : ℂ) * I))) := by
      simp only [C2]; rw [Complex.exp_add]; ring
    have h2 : (1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(1:ℂ)*I*π*a) * exp (exp (2*w)/4+(a-1/2)*w) = (Real.sqrt (2*π):ℂ)/Gamma (1/2+a) *
        exp (π / 2 * I + (-(1:ℂ)*I*π*a) + (exp (2*w)/4+(a-1/2)*w)) := by
      rw [Complex.exp_add (π / 2 * I + (-(1:ℂ)*I*π*a)), Complex.exp_add (π / 2 * I),
        Complex.exp_pi_div_two_mul_I]; ring
    rw [h1, h2, e2b]
    congr 1
    exact pcfSect_exp_eq_of_eq_add 0 (by push_cast; ring)
  have he : ∀ w : ℂ, 0 ≤ Real.exp (-2 * N * w.re) := fun w => (Real.exp_pos _).le
  have g1 := pcfSect_isBigO_const_mul_envelope C1 zero_le_one h1 he (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by rw [hA w]; nlinarith [norm_nonneg (exp (exp (2*w)/4+(a-1/2)*w)), he w])
  have g2 := pcfSect_isBigO_const_mul_envelope C2
    (norm_nonneg ((1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(1:ℂ)*I*π*a))) h2 he
    (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by
      rw [hB w, norm_mul, mul_assoc]
      gcongr
      nlinarith [norm_nonneg (exp (-exp (2*w)/4-(a+1/2)*w)), he w])
  refine (g1.add g2).congr' (Eventually.of_forall fun w => ?_) EventuallyEq.rfl
  have z1 : exp (w + ((-π:ℝ):ℂ)*I) = -exp w := by
    rw [Complex.exp_add, show ((-π:ℝ):ℂ)*I = -(π*I) by push_cast; ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]; ring
  have z2 : exp (w + ((-(π/2):ℝ):ℂ)*I) = (-1:ℂ)*I*exp w := by
    rw [Complex.exp_add, show ((-(π/2):ℝ):ℂ)*I = -(π/2*I) by push_cast; ring, Complex.exp_neg,
      Complex.exp_pi_div_two_mul_I, Complex.inv_I]; ring
  have s1 : ∑ s ∈ Finset.range N, pcfSect_uTerm a (exp (w + ((-π:ℝ):ℂ)*I)) s =
      ∑ j ∈ Finset.range N, pcfUTerm a (exp w) j :=
    Finset.sum_congr rfl fun s _ => by rw [z1]; exact pcfSect_uTerm_congr_sq a (by ring) s
  have s2 : ∑ s ∈ Finset.range N, pcfSect_uTerm (-a) (exp (w + ((-(π/2):ℝ):ℂ)*I)) s =
      ∑ j ∈ Finset.range N, pcfVTerm a (exp w) j :=
    Finset.sum_congr rfl fun s _ => by
      rw [z2]; exact pcfSect_uTerm_neg_eq_vTerm a (by ring_nf; rw [I_sq]; ring) s
  dsimp only
  rw [s1, s2, pcfU_rotated_connection_entire_neg a (exp w), ← z1, ← z2]
  linear_combination (-(∑ j ∈ Finset.range N, pcfUTerm a (exp w) j)) * hA w -
    (∑ j ∈ Finset.range N, pcfVTerm a (exp w) j) * hB w

/-- Two-exponential expansion with an absolute sum-of-envelopes remainder and inherited powers. -/
@[dlmf 12.9.E3]
theorem pcfU_adjacent_asymptotic_neg (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun w : ℂ => pcfU a (exp w)-(exp (-exp (2*w)/4-(a+1/2)*w)*(∑ j ∈ Finset.range N, pcfUTerm a (exp w) j)+(-1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(-1:ℂ)*I*π*a)*exp (exp (2*w)/4+(a-1/2)*w)*(∑ j ∈ Finset.range N, pcfVTerm a (exp w) j))) =O[pcfLogWedge (-(5*π/4-δ)) (-(π/4+δ))] (fun w : ℂ => ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ)) := by
  have h1 := pcfSect_U_logWedge a hδ π (lo := -(5*π/4-δ)) (hi := -(π/4+δ)) (by linarith) (by linarith) N
  have h2 := pcfSect_U_logWedge (-a) hδ (π/2) (lo := -(5*π/4-δ)) (hi := -(π/4+δ)) (by linarith) (by linarith) N
  set C1 : ℂ := (1:ℂ)*I*exp ((1:ℂ)*I*π*a)
  set C2 : ℂ := (Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp ((1:ℂ)*I*π*(a/2-1/4))
  have e2a : ∀ w : ℂ, exp (2 * (w + ((π : ℝ) : ℂ) * I)) = exp (2 * w) := fun w => by
    rw [pcfSect_exp_two_mul_add]
    rw [show (((2 * π : ℝ)) : ℂ) * I = ((1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have e2b : ∀ w : ℂ, exp (2 * (w + ((π/2 : ℝ) : ℂ) * I)) = -exp (2 * w) := fun w => by
    rw [pcfSect_exp_two_mul_add]
    rw [show (((2 * (π/2) : ℝ)) : ℂ) * I = π * I by push_cast; ring,
      Complex.exp_pi_mul_I]; ring
  have hIexp : I = exp (π / 2 * I) := Complex.exp_pi_div_two_mul_I.symm
  have hm1 : (-1 : ℂ) = exp (π * I) := Complex.exp_pi_mul_I.symm
  have hA : ∀ w, C1 * exp (-exp (2 * (w + ((π : ℝ) : ℂ) * I)) / 4 -
      (a + 1 / 2) * (w + ((π : ℝ) : ℂ) * I)) = exp (-exp (2*w)/4-(a+1/2)*w) := fun w => by
    have hC1 : C1 = exp (π / 2 * I + (1:ℂ) * I * π * a) := by
      rw [Complex.exp_add, Complex.exp_pi_div_two_mul_I]; simp only [C1]; ring
    rw [hC1, e2a, ← Complex.exp_add]
    exact pcfSect_exp_eq_of_eq_add 0 (by push_cast; ring)
  have hB : ∀ w, C2 * exp (-exp (2 * (w + ((π/2 : ℝ) : ℂ) * I)) / 4 -
      (-a + 1 / 2) * (w + ((π/2 : ℝ) : ℂ) * I)) = (-1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(-1:ℂ)*I*π*a) * exp (exp (2*w)/4+(a-1/2)*w) := fun w => by
    have h1 : C2 * exp (-exp (2 * (w + ((π/2 : ℝ) : ℂ) * I)) / 4 -
        (-a + 1 / 2) * (w + ((π/2 : ℝ) : ℂ) * I)) = (Real.sqrt (2*π):ℂ)/Gamma (1/2+a) *
        exp ((1:ℂ)*I*π*(a/2-1/4) + (-exp (2 * (w + ((π/2 : ℝ) : ℂ) * I)) / 4 -
        (-a + 1 / 2) * (w + ((π/2 : ℝ) : ℂ) * I))) := by
      simp only [C2]; rw [Complex.exp_add]; ring
    have h2 : (-1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(-1:ℂ)*I*π*a) * exp (exp (2*w)/4+(a-1/2)*w) = (Real.sqrt (2*π):ℂ)/Gamma (1/2+a) *
        exp (-(π / 2 * I) + (-(-1:ℂ)*I*π*a) + (exp (2*w)/4+(a-1/2)*w)) := by
      rw [Complex.exp_add (-(π / 2 * I) + (-(-1:ℂ)*I*π*a)), Complex.exp_add (-(π / 2 * I)),
        Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]; ring
    rw [h1, h2, e2b]
    congr 1
    exact pcfSect_exp_eq_of_eq_add 0 (by push_cast; ring)
  have he : ∀ w : ℂ, 0 ≤ Real.exp (-2 * N * w.re) := fun w => (Real.exp_pos _).le
  have g1 := pcfSect_isBigO_const_mul_envelope C1 zero_le_one h1 he (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by rw [hA w]; nlinarith [norm_nonneg (exp (exp (2*w)/4+(a-1/2)*w)), he w])
  have g2 := pcfSect_isBigO_const_mul_envelope C2
    (norm_nonneg ((-1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(-1:ℂ)*I*π*a))) h2 he
    (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by
      rw [hB w, norm_mul, mul_assoc]
      gcongr
      nlinarith [norm_nonneg (exp (-exp (2*w)/4-(a+1/2)*w)), he w])
  refine (g1.add g2).congr' (Eventually.of_forall fun w => ?_) EventuallyEq.rfl
  have z1 : exp (w + ((π:ℝ):ℂ)*I) = -exp w := by
    rw [Complex.exp_add, show ((π:ℝ):ℂ)*I = π*I by push_cast; ring,
      Complex.exp_pi_mul_I]; ring
  have z2 : exp (w + ((π/2:ℝ):ℂ)*I) = (1:ℂ)*I*exp w := by
    rw [Complex.exp_add, show ((π/2:ℝ):ℂ)*I = π/2*I by push_cast; ring,
      Complex.exp_pi_div_two_mul_I]; ring
  have s1 : ∑ s ∈ Finset.range N, pcfSect_uTerm a (exp (w + ((π:ℝ):ℂ)*I)) s =
      ∑ j ∈ Finset.range N, pcfUTerm a (exp w) j :=
    Finset.sum_congr rfl fun s _ => by rw [z1]; exact pcfSect_uTerm_congr_sq a (by ring) s
  have s2 : ∑ s ∈ Finset.range N, pcfSect_uTerm (-a) (exp (w + ((π/2:ℝ):ℂ)*I)) s =
      ∑ j ∈ Finset.range N, pcfVTerm a (exp w) j :=
    Finset.sum_congr rfl fun s _ => by
      rw [z2]; exact pcfSect_uTerm_neg_eq_vTerm a (by ring_nf; rw [I_sq]; ring) s
  dsimp only
  rw [s1, s2, pcfU_rotated_connection_entire_pos a (exp w), ← z1, ← z2]
  linear_combination (-(∑ j ∈ Finset.range N, pcfUTerm a (exp w) j)) * hA w -
    (∑ j ∈ Finset.range N, pcfVTerm a (exp w) j) * hB w

/-- Two-exponential expansion with an absolute sum-of-envelopes remainder and inherited powers. -/
@[dlmf 12.9.E4]
theorem pcfV_adjacent_asymptotic_pos (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun w : ℂ => pcfV a (exp w)-((Real.sqrt (2/π):ℂ)*exp (exp (2*w)/4+(a-1/2)*w)*(∑ j ∈ Finset.range N, pcfVTerm a (exp w) j)+(1:ℂ)*I/Gamma (1/2-a)*exp (-exp (2*w)/4-(a+1/2)*w)*(∑ j ∈ Finset.range N, pcfUTerm a (exp w) j))) =O[pcfLogWedge (-π/4+δ) (3*π/4-δ)] (fun w : ℂ => ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ)) := by
  have h1 := pcfSect_U_logWedge a hδ 0 (lo := -π/4+δ) (hi := 3*π/4-δ) (by linarith) (by linarith) N
  have h2 := pcfSect_U_logWedge (-a) hδ (-(π/2)) (lo := -π/4+δ) (hi := 3*π/4-δ) (by linarith) (by linarith) N
  set C1 : ℂ := (1:ℂ)*I/Gamma (1/2-a)
  set C2 : ℂ := (Real.sqrt (2/π):ℂ)*exp (I*π*(a/2-1/4))
  have z1 : ∀ w : ℂ, w + ((0:ℝ):ℂ)*I = w := fun w => by simp
  have e2b : ∀ w : ℂ, exp (2 * (w + ((-(π/2) : ℝ) : ℂ) * I)) = -exp (2 * w) := fun w => by
    rw [pcfSect_exp_two_mul_add]
    rw [show (((2 * -(π/2) : ℝ)) : ℂ) * I = -(π * I) by push_cast; ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]; ring
  have hA : ∀ w, C1 * exp (-exp (2 * (w + ((0 : ℝ) : ℂ) * I)) / 4 -
      (a + 1 / 2) * (w + ((0 : ℝ) : ℂ) * I)) = C1 * exp (-exp (2*w)/4-(a+1/2)*w) := fun w => by
    rw [z1]
  have hB : ∀ w, C2 * exp (-exp (2 * (w + ((-(π/2) : ℝ) : ℂ) * I)) / 4 -
      (-a + 1 / 2) * (w + ((-(π/2) : ℝ) : ℂ) * I)) =
      (Real.sqrt (2/π):ℂ) * exp (exp (2*w)/4+(a-1/2)*w) := fun w => by
    simp only [C2]
    rw [e2b, mul_assoc, ← Complex.exp_add]
    congr 1
    exact pcfSect_exp_eq_of_eq_add 0 (by push_cast; ring)
  have he : ∀ w : ℂ, 0 ≤ Real.exp (-2 * N * w.re) := fun w => (Real.exp_pos _).le
  have g1 := pcfSect_isBigO_const_mul_envelope C1 (norm_nonneg C1) h1 he (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by
      rw [hA w, norm_mul, mul_assoc]
      gcongr
      nlinarith [norm_nonneg (exp (exp (2*w)/4+(a-1/2)*w)), he w])
  have g2 := pcfSect_isBigO_const_mul_envelope C2
    (norm_nonneg (Real.sqrt (2/π):ℂ)) h2 he
    (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by
      rw [hB w, norm_mul, mul_assoc]
      gcongr
      nlinarith [norm_nonneg (exp (-exp (2*w)/4-(a+1/2)*w)), he w])
  refine (g1.add g2).congr' (Eventually.of_forall fun w => ?_) EventuallyEq.rfl
  have z2 : exp (w + ((-(π/2):ℝ):ℂ)*I) = -I*exp w := by
    rw [Complex.exp_add, show ((-(π/2):ℝ):ℂ)*I = -(π/2*I) by push_cast; ring, Complex.exp_neg,
      Complex.exp_pi_div_two_mul_I, Complex.inv_I]; ring
  have s2 : ∑ s ∈ Finset.range N, pcfSect_uTerm (-a) (exp (w + ((-(π/2):ℝ):ℂ)*I)) s =
      ∑ j ∈ Finset.range N, pcfVTerm a (exp w) j :=
    Finset.sum_congr rfl fun s _ => by
      rw [z2]; exact pcfSect_uTerm_neg_eq_vTerm a (by ring_nf; rw [I_sq]; ring) s
  dsimp only
  rw [z1, s2, pcfV_eq_mul_neg_I a (exp w), ← z2]
  simp only [C1, C2]
  have hu : ∑ s ∈ Finset.range N, pcfSect_uTerm a (exp w) s =
      ∑ j ∈ Finset.range N, pcfUTerm a (exp w) j := rfl
  rw [hu]
  linear_combination (-(∑ j ∈ Finset.range N, pcfVTerm a (exp w) j)) * hB w

/-- Two-exponential expansion with an absolute sum-of-envelopes remainder and inherited powers. -/
@[dlmf 12.9.E4]
theorem pcfV_adjacent_asymptotic_neg (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun w : ℂ => pcfV a (exp w)-((Real.sqrt (2/π):ℂ)*exp (exp (2*w)/4+(a-1/2)*w)*(∑ j ∈ Finset.range N, pcfVTerm a (exp w) j)+(-1:ℂ)*I/Gamma (1/2-a)*exp (-exp (2*w)/4-(a+1/2)*w)*(∑ j ∈ Finset.range N, pcfUTerm a (exp w) j))) =O[pcfLogWedge (-(3*π/4-δ)) (-(-π/4+δ))] (fun w : ℂ => ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ)) := by
  have h1 := pcfSect_U_logWedge a hδ 0 (lo := -(3*π/4-δ)) (hi := -(-π/4+δ)) (by linarith) (by linarith) N
  have h2 := pcfSect_U_logWedge (-a) hδ (π/2) (lo := -(3*π/4-δ)) (hi := -(-π/4+δ)) (by linarith) (by linarith) N
  set C1 : ℂ := (-1:ℂ)*I/Gamma (1/2-a)
  set C2 : ℂ := (Real.sqrt (2/π):ℂ)*exp (-I*π*(a/2-1/4))
  have z1 : ∀ w : ℂ, w + ((0:ℝ):ℂ)*I = w := fun w => by simp
  have e2b : ∀ w : ℂ, exp (2 * (w + ((π/2 : ℝ) : ℂ) * I)) = -exp (2 * w) := fun w => by
    rw [pcfSect_exp_two_mul_add]
    rw [show (((2 * (π/2) : ℝ)) : ℂ) * I = π * I by push_cast; ring,
      Complex.exp_pi_mul_I]; ring
  have hA : ∀ w, C1 * exp (-exp (2 * (w + ((0 : ℝ) : ℂ) * I)) / 4 -
      (a + 1 / 2) * (w + ((0 : ℝ) : ℂ) * I)) = C1 * exp (-exp (2*w)/4-(a+1/2)*w) := fun w => by
    rw [z1]
  have hB : ∀ w, C2 * exp (-exp (2 * (w + ((π/2 : ℝ) : ℂ) * I)) / 4 -
      (-a + 1 / 2) * (w + ((π/2 : ℝ) : ℂ) * I)) =
      (Real.sqrt (2/π):ℂ) * exp (exp (2*w)/4+(a-1/2)*w) := fun w => by
    simp only [C2]
    rw [e2b, mul_assoc, ← Complex.exp_add]
    congr 1
    exact pcfSect_exp_eq_of_eq_add 0 (by push_cast; ring)
  have he : ∀ w : ℂ, 0 ≤ Real.exp (-2 * N * w.re) := fun w => (Real.exp_pos _).le
  have g1 := pcfSect_isBigO_const_mul_envelope C1 (norm_nonneg C1) h1 he (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by
      rw [hA w, norm_mul, mul_assoc]
      gcongr
      nlinarith [norm_nonneg (exp (exp (2*w)/4+(a-1/2)*w)), he w])
  have g2 := pcfSect_isBigO_const_mul_envelope C2
    (norm_nonneg (Real.sqrt (2/π):ℂ)) h2 he
    (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by
      rw [hB w, norm_mul, mul_assoc]
      gcongr
      nlinarith [norm_nonneg (exp (-exp (2*w)/4-(a+1/2)*w)), he w])
  refine (g1.add g2).congr' (Eventually.of_forall fun w => ?_) EventuallyEq.rfl
  have z2 : exp (w + ((π/2:ℝ):ℂ)*I) = I*exp w := by
    rw [Complex.exp_add, show ((π/2:ℝ):ℂ)*I = π/2*I by push_cast; ring,
      Complex.exp_pi_div_two_mul_I]; ring
  have s2 : ∑ s ∈ Finset.range N, pcfSect_uTerm (-a) (exp (w + ((π/2:ℝ):ℂ)*I)) s =
      ∑ j ∈ Finset.range N, pcfVTerm a (exp w) j :=
    Finset.sum_congr rfl fun s _ => by
      rw [z2]; exact pcfSect_uTerm_neg_eq_vTerm a (by ring_nf; rw [I_sq]; ring) s
  dsimp only
  rw [z1, s2, pcfV_eq_mul_I a (exp w), ← z2]
  simp only [C1, C2]
  have hu : ∑ s ∈ Finset.range N, pcfSect_uTerm a (exp w) s =
      ∑ j ∈ Finset.range N, pcfUTerm a (exp w) j := rfl
  rw [hu]
  linear_combination (-(∑ j ∈ Finset.range N, pcfVTerm a (exp w) j)) * hB w

/-- The integral over `(0,∞)` of a positive real function, viewed in `ℂ`, is nonzero. -/
lemma integral_Ioi_ofReal_ne_zero {g : ℝ → ℝ} (hpos : ∀ t ∈ Ioi (0:ℝ), 0 < g t)
    (hint : IntegrableOn (fun t => (g t : ℂ)) (Ioi 0)) : (∫ t in Ioi (0:ℝ), (g t : ℂ)) ≠ 0 := by
  have hg : IntegrableOn g (Ioi 0) := by simpa using hint.re
  rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
  refine (ne_of_gt ((setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hpos t ht).le) hg).2 ?_))
  refine lt_of_lt_of_le (by simp [Real.volume_Ioi]) (measure_mono (s := Ioi (0:ℝ)) fun t ht => ⟨(hpos t ht).ne', ht⟩)

/-- DLMF 12.11(i): absence of real zeros. -/
theorem pcfU_no_real_zero {a : ℝ} (ha : -1/2 ≤ a) (x : ℝ) :
    pcfU a x ≠ 0 := by
  rcases ha.eq_or_lt with h | h
  · rw [← h, show ((-1/2:ℝ):ℂ) = -1/2 by push_cast; ring, pcfU_neg_half]; exact Complex.exp_ne_zero _
  · rw [pcfU_eq_integral (by simpa using h)]
    refine mul_ne_zero (div_ne_zero (Complex.exp_ne_zero _)
      (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))) ?_
    have hc : -1 < ((a:ℂ) - 1/2).re := by simp; linarith
    have heq : ∀ t ∈ Ioi (0:ℝ), (t:ℂ)^((a:ℂ) - 1/2) * exp (-(t:ℂ)^2/2 - x*t) =
        ((t^(a-1/2) * Real.exp (-t^2/2 - x*t) : ℝ) : ℂ) := fun t ht => by
      rw [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt ht), Complex.ofReal_exp]; push_cast; ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi heq]
    refine integral_Ioi_ofReal_ne_zero (fun t ht => mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)) ?_
    exact (integrableOn_pcfIntegrand hc x).congr_fun heq measurableSet_Ioi

/-- DLMF 12.11(i): the first real zero lies on the negative axis. -/
theorem pcfU_no_positive_zero {a : ℝ} (h0 : -3/2 < a) (h1 : a < -1/2) {x : ℝ} (hx : 0 < x) :
    pcfU a x ≠ 0 := by
  have hz : 0 < ((x:ℂ)^2/2).re := by
    rw [show (x:ℂ)^2/2 = ((x^2/2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]; positivity
  have hα : 0 < ((a:ℂ)/2+3/4).re := by simp; linarith
  rw [pcfU_kummerU_odd (a:ℂ) (by simpa using hx), kummerU_laplace hα hz]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (by exact_mod_cast hx.ne'))
    (Complex.exp_ne_zero _)) (mul_ne_zero (one_div_ne_zero (Complex.Gamma_ne_zero_of_re_pos hα)) ?_)
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  · have heq : ∀ t ∈ Ioi (0:ℝ), exp (-((x:ℂ)^2/2) * t) * (t:ℂ)^((a:ℂ)/2+3/4-1) *
        (1+(t:ℂ))^((3/2:ℂ)-((a:ℂ)/2+3/4)-1) =
        ((Real.exp (-(x^2/2)*t) * t^((a/2+3/4)-1) * (1+t)^(3/2-(a/2+3/4)-1) : ℝ) : ℂ) := fun t ht => by
      have ht0 : (0:ℝ) ≤ 1 + t := by linarith [show (0:ℝ) < t from ht]
      rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt ht),
        Complex.ofReal_cpow ht0, Complex.ofReal_exp]
      push_cast; ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi heq]
    refine integral_Ioi_ofReal_ne_zero (fun t ht => mul_pos (mul_pos (Real.exp_pos _)
      (Real.rpow_pos_of_pos ht _)) (Real.rpow_pos_of_pos (by linarith [show (0:ℝ) < t from ht]) _)) ?_
    exact (kummerU_laplace_integrable (b := 3/2) hα hz).congr_fun heq measurableSet_Ioi

/-- Hermite specialization and enclosure of all real zeros. -/
theorem pcfU_hermite_zero_count (n : ℕ) :
    Set.Finite {x : ℝ | pcfU (-n-1/2) x=0} ∧ ({x : ℝ | pcfU (-n-1/2) x=0}:Set ℝ).ncard=n ∧ ∀ x : ℝ, pcfU (-n-1/2) x=0 → |x| ≤ 2*Real.sqrt (n+1/2) := by
  obtain ⟨r, hr, hb, hz⟩ := DLMF.OrthogonalPolynomials.hermitePolyH_zeros_bound n
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hset : {x : ℝ | pcfU (-n-1/2) x=0} = Set.range (fun i => Real.sqrt 2 * r i) := by
    ext x
    simp only [mem_ofPred_eq, mem_range, pcfU_physicists_hermite]
    have h2 : (2 : ℂ) ^ (-(n : ℂ) / 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
    rw [mul_eq_zero, or_iff_right (mul_ne_zero h2 (exp_ne_zero _)), hz]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have : (x : ℂ) = Real.sqrt 2 * r i := by rw [← hi]; field_simp
      exact_mod_cast this.symm
    · rintro ⟨i, rfl⟩
      exact ⟨i, by push_cast; field_simp⟩
  have hinj : Function.Injective (fun i => Real.sqrt 2 * r i) := fun i j h =>
    hr.injective (mul_left_cancel₀ hs.ne' h)
  refine ⟨hset ▸ Set.finite_range _, ?_, ?_⟩
  · rw [hset, ← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  · intro x hx
    have hx' : x ∈ {x : ℝ | pcfU (-n-1/2) x=0} := hx
    rw [hset] at hx'
    obtain ⟨i, rfl⟩ := hx'
    have e : 2 * Real.sqrt (n + 1/2) = Real.sqrt 2 * Real.sqrt (2 * n + 1) := by
      rw [← Real.sqrt_mul (by norm_num), show (2:ℝ) * (2 * n + 1) = 2^2 * (n + 1/2) by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [e, abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left (hb i).le hs.le

/-! ### Positive zeros of `U(a,x)` by parameter deformation -/

/-- Joint continuity of Kummer's `M` in the first parameter and the argument. -/
lemma pcfPZ_kummerM_continuous {c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) :
    Continuous (fun p : ℂ × ℂ => kummerM p.1 c p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a₀, z₀⟩
  set α : ℝ := ‖a₀‖ + 1
  set R : ℝ := ‖z₀‖ + 1
  have hsum : Summable fun n => ‖kummerMCoeff (α : ℂ) c n * (R : ℂ) ^ n‖ :=
    summable_norm_iff.mpr (hasSum_kummerM hc (R : ℂ)).summable
  set s : Set (ℂ × ℂ) := {p | ‖p.1‖ < α ∧ ‖p.2‖ < R}
  have hs : IsOpen s := (isOpen_lt (continuous_fst.norm) continuous_const).inter
    (isOpen_lt (continuous_snd.norm) continuous_const)
  have hmem : (a₀, z₀) ∈ s := ⟨by simp [α], by simp [R]⟩
  have hc' : ContinuousOn (fun p : ℂ × ℂ => ∑' n : ℕ, poch p.1 n / (poch c n * n !) * p.2 ^ n) s := by
    refine continuousOn_tsum (fun n => ?_) hsum ?_
    · have : Continuous fun p : ℂ × ℂ => poch p.1 n :=
        (Polynomial.continuous _).comp continuous_fst
      exact ((this.div_const _).mul (continuous_snd.pow n)).continuousOn
    · intro n p hp
      rw [norm_mul, norm_mul, norm_div, norm_div, norm_pow, norm_pow]
      have h1 := norm_ascPochhammer_eval_le hp.1.le n
      have h2 : ‖p.2‖ ^ n ≤ ‖(R : ℂ)‖ ^ n := by
        gcongr
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        exact hp.2.le
      gcongr
  exact (hc'.continuousAt (hs.mem_nhds hmem))

/-- Composition form of `pcfPZ_kummerM_continuous`. -/
lemma pcfPZ_kummerM_comp {c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) {f g : ℂ × ℂ → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p => kummerM (f p) c (g p)) :=
  (pcfPZ_kummerM_continuous hc).comp (hf.prodMk hg)

/-- Continuity of `1/Γ` along a continuous map. -/
lemma pcfPZ_recipGamma_comp {f : ℂ × ℂ → ℂ} (hf : Continuous f) :
    Continuous (fun p => (Gamma (f p))⁻¹) :=
  differentiable_one_div_Gamma.continuous.comp hf |>.congr fun p => by simp

/-- `U(a,z)` is jointly continuous in `(a,z)`. -/
lemma pcfPZ_pcfU_continuous : Continuous (fun p : ℂ × ℂ => pcfU p.1 p.2) := by
  have hb1 : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -k := half_ne_neg_nat
  have hb3 : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -k := three_half_ne_neg_nat
  unfold pcfU pcfEven pcfOdd
  have k1 := pcfPZ_kummerM_comp hb1 (f := fun p : ℂ × ℂ => p.1 / 2 + 1 / 4)
    (g := fun p => p.2 ^ 2 / 2) (by fun_prop) (by fun_prop)
  have k3 := pcfPZ_kummerM_comp hb3 (f := fun p : ℂ × ℂ => p.1 / 2 + 3 / 4)
    (g := fun p => p.2 ^ 2 / 2) (by fun_prop) (by fun_prop)
  have g1 := pcfPZ_recipGamma_comp (f := fun p : ℂ × ℂ => 3 / 4 + p.1 / 2) (by fun_prop)
  have g2 := pcfPZ_recipGamma_comp (f := fun p : ℂ × ℂ => 1 / 4 + p.1 / 2) (by fun_prop)
  have c1 : Continuous fun p : ℂ × ℂ => (2 : ℂ) ^ (-(p.1 / 2 + 1 / 4)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl two_ne_zero)
  have c2 : Continuous fun p : ℂ × ℂ => (2 : ℂ) ^ (-(p.1 / 2 - 1 / 4)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl two_ne_zero)
  fun_prop

/-- `U'(a,z)` is jointly continuous in `(a,z)`. -/
lemma pcfPZ_pcfUDeriv_continuous : Continuous (fun p : ℂ × ℂ => pcfUDeriv p.1 p.2) := by
  have hb1 : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -k := half_ne_neg_nat
  have hb3 : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -k := three_half_ne_neg_nat
  have hb3' : ∀ k : ℕ, (1 / 2 + 1 : ℂ) ≠ -k := by norm_num; exact three_half_ne_neg_nat
  have hb5 : ∀ k : ℕ, (3 / 2 + 1 : ℂ) ≠ -k := by norm_num; exact five_halves_ne_neg_nat
  unfold pcfUDeriv pcfEvenDeriv pcfOddDeriv
  have k1 := pcfPZ_kummerM_comp hb1 (f := fun p : ℂ × ℂ => p.1 / 2 + 1 / 4)
    (g := fun p => p.2 ^ 2 / 2) (by fun_prop) (by fun_prop)
  have k3 := pcfPZ_kummerM_comp hb3 (f := fun p : ℂ × ℂ => p.1 / 2 + 3 / 4)
    (g := fun p => p.2 ^ 2 / 2) (by fun_prop) (by fun_prop)
  have k1' := pcfPZ_kummerM_comp hb3' (f := fun p : ℂ × ℂ => p.1 / 2 + 1 / 4 + 1)
    (g := fun p => p.2 ^ 2 / 2) (by fun_prop) (by fun_prop)
  have k3' := pcfPZ_kummerM_comp hb5 (f := fun p : ℂ × ℂ => p.1 / 2 + 3 / 4 + 1)
    (g := fun p => p.2 ^ 2 / 2) (by fun_prop) (by fun_prop)
  have g1 := pcfPZ_recipGamma_comp (f := fun p : ℂ × ℂ => 3 / 4 + p.1 / 2) (by fun_prop)
  have g2 := pcfPZ_recipGamma_comp (f := fun p : ℂ × ℂ => 1 / 4 + p.1 / 2) (by fun_prop)
  have c1 : Continuous fun p : ℂ × ℂ => (2 : ℂ) ^ (-(p.1 / 2 + 1 / 4)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl two_ne_zero)
  have c2 : Continuous fun p : ℂ × ℂ => (2 : ℂ) ^ (-(p.1 / 2 - 1 / 4)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl two_ne_zero)
  fun_prop

/-- A solution of `f'' = q f` with `q ≥ 0` on `[X, ∞)` that decays at infinity and has only
simple zeros has no zero in `[X, ∞)`. -/
lemma pcfPZ_no_zero_of_decay {f f' q : ℝ → ℝ} {X : ℝ}
    (hf : ∀ x, X ≤ x → HasDerivAt f (f' x) x)
    (hf' : ∀ x, X ≤ x → HasDerivAt f' (q x * f x) x) (hq : ∀ x, X ≤ x → 0 ≤ q x)
    (hlim : Tendsto f atTop (𝓝 0)) (hs : ∀ x, X ≤ x → f x = 0 → f' x ≠ 0) :
    ∀ x, X ≤ x → f x ≠ 0 := by
  intro x₀ hx₀ h0
  -- `g = f f'` is monotone on `[X, ∞)`.
  have hg : ∀ x, X ≤ x → HasDerivAt (fun t => f t * f' t)
      (f' x * f' x + f x * (q x * f x)) x := fun x hx => (hf x hx).mul (hf' x hx)
  have hgmono : MonotoneOn (fun t => f t * f' t) (Ici x₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici x₀) ?_ ?_ ?_
    · exact fun x hx => (hg x (hx₀.trans hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hg x (hx₀.trans hx.le)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hg x (hx₀.trans hx.le)).deriv]
      have := hq x (hx₀.trans hx.le)
      nlinarith [mul_self_nonneg (f' x), mul_self_nonneg (f x)]
  have hgnn : ∀ x, x₀ ≤ x → 0 ≤ f x * f' x := fun x hx => by
    have := hgmono (self_mem_Ici) hx hx
    simpa [h0] using this
  -- hence `f²` is monotone on `[x₀, ∞)`
  have hsq : ∀ x, X ≤ x → HasDerivAt (fun t => f t * f t) (f' x * f x + f x * f' x) x :=
    fun x hx => (hf x hx).mul (hf x hx)
  have hsqmono : MonotoneOn (fun t => f t * f t) (Ici x₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici x₀) ?_ ?_ ?_
    · exact fun x hx => (hsq x (hx₀.trans hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hsq x (hx₀.trans hx.le)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hsq x (hx₀.trans hx.le)).deriv]
      linarith [hgnn x hx.le]
  have hlim2 : Tendsto (fun t => f t * f t) atTop (𝓝 0) := by
    simpa using hlim.mul hlim
  have hz : ∀ x, x₀ ≤ x → f x = 0 := by
    intro x hx
    have hle : f x * f x ≤ 0 := by
      refine ge_of_tendsto hlim2 ?_
      filter_upwards [eventually_ge_atTop x] with y hy
      exact hsqmono hx (hx.trans hy) hy
    exact mul_self_eq_zero.mp (le_antisymm hle (mul_self_nonneg _))
  -- so the right derivative at `x₀` vanishes
  have hsl := (hasDerivAt_iff_tendsto_slope.mp (hf x₀ hx₀)).mono_left (nhdsGT_le_nhdsNE x₀)
  have hc : Tendsto (slope f x₀) (𝓝[>] x₀) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [slope_def_field, hz x (le_of_lt hx), h0]
    simp
  exact hs x₀ hx₀ h0 (tendsto_nhds_unique hsl hc)

/-- `U(a,x) → 0` as `x → +∞` for real `a`. -/
lemma pcfPZ_tendsto_pcfU (a : ℝ) : Tendsto (fun x : ℝ => pcfU a x) atTop (𝓝 0) := by
  have h0 := hasAsymptoticExpansion_pcfU (a : ℂ) 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, CharP.cast_eq_zero, mul_zero,
    sub_zero] at h0
  refine h0.trans_tendsto ?_
  set s : ℝ := -a - 1 / 2
  have hreal : Tendsto (fun x : ℝ => (x ^ 2) ^ (s / 2) * Real.exp (-(1 / 4) * x ^ 2)) atTop
      (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / 2) (1 / 4) (by norm_num)).comp
      (tendsto_pow_atTop two_ne_zero)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine hreal.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (-(x : ℂ) ^ 2 / 4).re = -(1 / 4) * x ^ 2 := by
    rw [show -(x : ℂ) ^ 2 / 4 = ((-(1 / 4) * x ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have hre2 : (-(a : ℂ) - 1 / 2).re = s := by simp [s]
  rw [hre, hre2, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num
  ring_nf

/-- The real derivative family of `U` along real arguments. -/
lemma pcfPZ_hasDerivAt_re (t x : ℝ) :
    HasDerivAt (fun y : ℝ => (pcfU t y).re) (pcfUDeriv t x).re x :=
  (hasDerivAt_pcfU t x).real_of_complex

/-- Weber's equation for the real parts. -/
lemma pcfPZ_hasDerivAt_deriv_re (t x : ℝ) :
    HasDerivAt (fun y : ℝ => (pcfUDeriv t y).re) ((x ^ 2 / 4 + t) * (pcfU t x).re) x := by
  have h := (hasDerivAt_pcfUDeriv t x).real_of_complex
  rwa [show ((x : ℂ) ^ 2 / 4 + t) = ((x ^ 2 / 4 + t : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul] at h

/-- `U(t,x)` is real for real `t, x`. -/
lemma pcfPZ_eq_re (t x : ℝ) : pcfU t x = ((pcfU t x).re : ℂ) :=
  Complex.ext (by simp) (by simp [pcfU_real])

/-- `U'(t,x)` is real for real `t, x`. -/
lemma pcfPZ_deriv_eq_re (t x : ℝ) : pcfUDeriv t x = ((pcfUDeriv t x).re : ℂ) := by
  have h1 : HasDerivAt (fun y : ℝ => pcfU t y) (pcfUDeriv t x) x := (hasDerivAt_pcfU t x).comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => (((pcfU t y).re : ℝ) : ℂ)) ((pcfUDeriv t x).re : ℂ) x :=
    (pcfPZ_hasDerivAt_re t x).ofReal_comp
  have he : (fun y : ℝ => (((pcfU t y).re : ℝ) : ℂ)) = fun y : ℝ => pcfU t y :=
    funext fun y => (pcfPZ_eq_re t y).symm
  rw [he] at h2
  exact h1.unique h2

/-- Real zeros of `U(t,·)` are simple (Wronskian with `V`). -/
lemma pcfPZ_simple (t x : ℝ) (h : (pcfU t x).re = 0) : (pcfUDeriv t x).re ≠ 0 := by
  intro h'
  have hU : pcfU t x = 0 := by rw [pcfPZ_eq_re, h, Complex.ofReal_zero]
  have hU' : pcfUDeriv t x = 0 := by rw [pcfPZ_deriv_eq_re, h', Complex.ofReal_zero]
  have hW := pcfV_wronskian (t : ℂ) (x : ℂ)
  rw [deriv_pcfU, hU, hU'] at hW
  have : (0 : ℝ) < Real.sqrt (2 / π) := Real.sqrt_pos.mpr (by positivity)
  have h0 : ((Real.sqrt (2 / π) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
  exact h0 (by rw [← hW]; ring)

/-- `U(t,0) ≠ 0` away from the poles of `Γ(3/4 + t/2)`. -/
lemma pcfPZ_zero_ne {t : ℝ} (h : ∀ m : ℕ, (3 / 4 + t / 2 : ℂ) ≠ -m) : pcfU t 0 ≠ 0 := by
  rw [pcfU_zero]
  refine div_ne_zero ?_ (mul_ne_zero ?_ (Complex.Gamma_ne_zero h))
  · exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  · exact (Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero))

/-- No zeros of `U(t,x)` where `x²/4 + t ≥ 0` beyond `X`. -/
lemma pcfPZ_far {t : ℝ} {X : ℝ} (hX : ∀ x, X ≤ x → 0 ≤ x ^ 2 / 4 + t) :
    ∀ x, X ≤ x → (pcfU t x).re ≠ 0 :=
  pcfPZ_no_zero_of_decay (f := fun y : ℝ => (pcfU t y).re) (f' := fun y : ℝ => (pcfUDeriv t y).re)
    (q := fun y => y ^ 2 / 4 + t) (fun x _ => pcfPZ_hasDerivAt_re t x)
    (fun x _ => pcfPZ_hasDerivAt_deriv_re t x) hX
    (by have h := (Complex.continuous_re.tendsto 0).comp (pcfPZ_tendsto_pcfU t); rw [Complex.zero_re] at h; exact h)
    (fun x _ h => pcfPZ_simple t x h)

/-- Vanishing of `U(t,x)` through its real part. -/
lemma pcfPZ_re_eq_zero_iff (t x : ℝ) : (pcfU t x).re = 0 ↔ pcfU t x = 0 := by
  constructor
  · intro h; rw [pcfPZ_eq_re, h, Complex.ofReal_zero]
  · intro h; rw [h, Complex.zero_re]

/-- Base count: `U(-2n-1/2, x)` has exactly `n` positive zeros. -/
lemma pcfPZ_base (n : ℕ) :
    {x : ℝ | x ∈ Ici 0 ∧ (pcfU ((-2 * n - 1 / 2 : ℝ) : ℂ) x).re = 0}.ncard = n := by
  obtain ⟨hfin, hcard, -⟩ := pcfU_hermite_zero_count (2 * n)
  have hc : ((-2 * n - 1 / 2 : ℝ) : ℂ) = -((2 * n : ℕ) : ℂ) - 1 / 2 := by push_cast; ring
  set Z := {x : ℝ | pcfU (-((2 * n : ℕ) : ℂ) - 1 / 2) x = 0} with hZ
  have h0 : (0 : ℝ) ∉ Z := by
    have := pcfPZ_zero_ne (t := -2 * n - 1 / 2) (fun m h => by
      have h' := congrArg Complex.re h
      simp at h'
      have h2 : ((1 : ℤ) : ℝ) = ((2 * ((n : ℤ) - m) : ℤ) : ℝ) := by push_cast; linarith
      have := Int.cast_injective (α := ℝ) h2
      omega)
    rw [hc] at this
    simpa [hZ] using this
  have hsymm : ∀ x, x ∈ Z ↔ -x ∈ Z := by
    intro x
    simp only [hZ, mem_ofPred_eq, Complex.ofReal_neg]
    rw [pcfU_neg_nat_sub_half_neg (2 * n) (x : ℂ), pow_mul]
    simp
  set P := {x : ℝ | 0 < x ∧ x ∈ Z}
  have hset : {x : ℝ | x ∈ Ici 0 ∧ (pcfU ((-2 * n - 1 / 2 : ℝ) : ℂ) x).re = 0} = P := by
    ext x
    simp only [mem_ofPred_eq, mem_Ici, P]
    rw [show (((-2 * n - 1 / 2 : ℝ) : ℂ)) = (((-2 * n - 1 / 2 : ℝ) : ℝ) : ℂ) from rfl,
      pcfPZ_re_eq_zero_iff, hc]
    constructor
    · rintro ⟨hx, hz⟩
      refine ⟨lt_of_le_of_ne hx ?_, hz⟩
      rintro rfl
      exact h0 hz
    · rintro ⟨hx, hz⟩
      exact ⟨hx.le, hz⟩
  rw [hset]
  have hZu : Z = P ∪ (-P) := by
    ext x
    simp only [P, mem_union, mem_ofPred_eq, Set.mem_neg]
    constructor
    · intro hx
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inr ⟨by linarith, (hsymm x).mp hx⟩
      · exact absurd (h ▸ hx) h0
      · exact Or.inl ⟨h, hx⟩
    · rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact h
      · exact (hsymm x).mpr h
  have hdisj : Disjoint P (-P) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [P, Set.mem_neg, mem_ofPred_eq] at hx hx'
    linarith [hx.1, hx'.1]
  have hPf : P.Finite := hfin.subset fun x hx => hx.2
  have hnP : (-P).ncard = P.ncard := by
    rw [← Set.image_neg_eq_neg, Set.ncard_image_of_injective _ neg_injective]
  rw [hZu, Set.ncard_union_eq hdisj hPf hPf.neg, hnP] at hcard
  omega

/-- Exact positive real zero count in DLMF 12.11(i). -/
theorem pcfU_positive_zero_count {a : ℝ} (n : ℕ) (hn : 0 < n) (h0 : -2*n-3/2 < a) (h1 : a < -2*n+1/2) :
    Set.Finite {x : ℝ | 0 < x ∧ pcfU a x=0} ∧ ({x : ℝ | 0 < x ∧ pcfU a x=0}:Set ℝ).ncard=n := by
  set S : Set ℝ := Ioo (-2 * n - 3 / 2) (-2 * n + 1 / 2) with hS
  set Y : ℝ → ℝ → ℝ := fun t x => (pcfU t x).re with hY
  set Y' : ℝ → ℝ → ℝ := fun t x => (pcfUDeriv t x).re with hY'
  have hcR : Continuous (fun p : ℝ × ℝ => ((p.1 : ℂ), (p.2 : ℂ))) := by fun_prop
  have hcY : ContinuousOn (Function.uncurry Y) (S ×ˢ univ) :=
    (Complex.continuous_re.comp (pcfPZ_pcfU_continuous.comp hcR)).continuousOn
  have hcY' : ContinuousOn (Function.uncurry Y') (S ×ˢ univ) :=
    (Complex.continuous_re.comp (pcfPZ_pcfUDeriv_continuous.comp hcR)).continuousOn
  have hY0 : ∀ t ∈ S, Y t 0 ≠ 0 := by
    intro t ht h
    have h' : pcfU t 0 = 0 := by
      have := (pcfPZ_re_eq_zero_iff t 0).mp h
      simpa using this
    refine pcfPZ_zero_ne (t := t) (fun m hm => ?_) h'
    have hre := congrArg Complex.re hm
    simp at hre
    have hm1 : (m : ℝ) < n := by linarith [ht.1]
    have hm2 : (n : ℝ) < m + 1 := by linarith [ht.2]
    have e1 : m < n := by exact_mod_cast hm1
    have e2 : n < m + 1 := by exact_mod_cast hm2
    omega
  have hfar : ∀ t ∈ S, ∀ x, (4 * n + 4 : ℝ) ≤ x → Y t x ≠ 0 := by
    intro t ht
    refine pcfPZ_far (fun x hx => ?_)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [ht.1]
  have hmem : (-2 * n - 1 / 2 : ℝ) ∈ S := ⟨by linarith, by linarith⟩
  have heq := ODE.sturmDef_ncard_Ici_eq_of_isPreconnected (Y := Y) (Y' := Y') (Λ := S)
    (U := univ) (a := 0) (b := 4 * n + 4) isOpen_Ioo isOpen_univ (subset_univ _) hcY hcY'
    (fun t _ x _ => pcfPZ_hasDerivAt_re t x) (fun t _ x _ h => pcfPZ_simple t x h)
    isPreconnected_Ioo subset_rfl hY0 hfar (t₁ := a) (t₂ := -2 * n - 1 / 2) ⟨h0, h1⟩ hmem
  have hbase := pcfPZ_base n
  have hset : {x : ℝ | 0 < x ∧ pcfU a x = 0} = {x | x ∈ Ici 0 ∧ Y a x = 0} := by
    ext x
    simp only [mem_ofPred_eq, mem_Ici, hY, pcfPZ_re_eq_zero_iff]
    constructor
    · rintro ⟨hx, hz⟩; exact ⟨hx.le, hz⟩
    · rintro ⟨hx, hz⟩
      refine ⟨lt_of_le_of_ne hx ?_, hz⟩
      rintro rfl
      exact hY0 a ⟨h0, h1⟩ ((pcfPZ_re_eq_zero_iff a 0).mpr (by simpa using hz))
  have hcard : ({x : ℝ | 0 < x ∧ pcfU a x = 0} : Set ℝ).ncard = n := by
    rw [hset, heq]
    exact hbase
  exact ⟨Set.finite_of_ncard_ne_zero (by omega), hcard⟩

/-- DLMF 12.11(i): absence of positive real zeros of V. -/
theorem pcfV_no_positive_zero {a : ℝ} (ha : -1/2 < a) {x : ℝ} (hx : 0 < x) :
    pcfV a x ≠ 0 := by
  have hn : ∀ n : ℕ, 1 / 2 + (a : ℂ) ≠ -n := fun n h => by
    have := congrArg re h
    simp at this
    linarith [n.cast_nonneg (α := ℝ)]
  have ha' : -1 / 2 < (a : ℂ).re := by simpa using ha
  have hΓ : Gamma (1 / 2 + (a : ℂ)) ≠ 0 := Complex.Gamma_ne_zero hn
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : -1 < ((a : ℂ) - 1 / 2).re := by simp; linarith
  rw [pcfV_eq hn, pcfU_eq_integral ha', pcfU_eq_integral ha', neg_sq]
  set E := exp (-(x : ℂ) ^ 2 / 4)
  set f1 := fun t : ℝ => (t : ℂ) ^ ((a : ℂ) - 1 / 2) * exp (-(t : ℂ) ^ 2 / 2 - (x : ℂ) * t)
  set f2 := fun t : ℝ => (t : ℂ) ^ ((a : ℂ) - 1 / 2) * exp (-(t : ℂ) ^ 2 / 2 - (-(x : ℂ)) * t)
  have h1 : IntegrableOn f1 (Ioi 0) := integrableOn_pcfIntegrand hc _
  have h2 : IntegrableOn f2 (Ioi 0) := integrableOn_pcfIntegrand hc _
  have key : Gamma (1 / 2 + (a : ℂ)) / π * (Complex.sin (π * a) * (E / Gamma (1 / 2 + (a : ℂ)) *
      ∫ t in Ioi (0 : ℝ), f1 t) + E / Gamma (1 / 2 + (a : ℂ)) * ∫ t in Ioi (0 : ℝ), f2 t) =
      E / π * ∫ t in Ioi (0 : ℝ), (Complex.sin (π * a) * f1 t + f2 t) := by
    rw [integral_add (h1.const_mul _) h2, integral_const_mul]
    field_simp
    have hΓ' : Gamma ((1 + 2 * (a : ℂ)) / 2) ≠ 0 := by convert hΓ using 2; ring
    rw [mul_assoc, mul_div_cancel_left₀ _ hΓ']
  rw [key]
  refine mul_ne_zero (div_ne_zero (exp_ne_zero _) hπ) ?_
  set g : ℝ → ℝ := fun t => t ^ (a - 1 / 2) * Real.exp (-t ^ 2 / 2) *
    (Real.sin (π * a) * Real.exp (-x * t) + Real.exp (x * t))
  have heq : ∀ t ∈ Ioi (0 : ℝ), Complex.sin (π * a) * f1 t + f2 t = (g t : ℂ) := by
    intro t ht
    simp only [f1, f2, g]
    rw [ofReal_mul, ofReal_mul, ofReal_cpow (le_of_lt ht)]
    push_cast
    rw [show -(t : ℂ) ^ 2 / 2 - x * t = -(t : ℂ) ^ 2 / 2 + -x * t by ring,
      show -(t : ℂ) ^ 2 / 2 - -x * t = -(t : ℂ) ^ 2 / 2 + x * t by ring, exp_add, exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq]
  refine integral_Ioi_ofReal_ne_zero (fun t ht => ?_) ?_
  · have ht : (0 : ℝ) < t := ht
    have hlt : Real.exp (-x * t) < Real.exp (x * t) := Real.exp_lt_exp.mpr (by nlinarith)
    have hs : -1 ≤ Real.sin (π * a) := Real.neg_one_le_sin _
    have : 0 < Real.sin (π * a) * Real.exp (-x * t) + Real.exp (x * t) := by
      nlinarith [Real.exp_pos (-x * t)]
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)) this
  · exact IntegrableOn.congr_fun ((h1.const_mul _).add h2) heq measurableSet_Ioi

/-- DLMF 12.11(i): zeros of V at the origin. -/
theorem pcfV_integer_zero (n : ℤ) :
    pcfV (3/2-2*n) 0=0 := by
  rw [pcfV_zero', pcfVZero]
  rcases le_or_gt 1 n with hn | hn
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨(n-1).toNat, by omega⟩
    rw [show (1/4:ℂ) + (3/2 - 2*((m+1:ℤ):ℂ))/2 = -(m:ℂ) by push_cast; ring, Complex.Gamma_neg_nat_eq_zero]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -m := ⟨(-n).toNat, by omega⟩
    rw [show (3/4:ℂ) - (3/2 - 2*((-(m:ℤ):ℤ):ℂ))/2 = -(m:ℂ) by push_cast; ring, Complex.Gamma_neg_nat_eq_zero]
    simp

/-- pcfZeroTau. -/
@[dlmf 12.11.E2]
def pcfZeroTau (a : ℝ) (s : ℕ) : ℂ :=
  (2*s+1/2-a:ℂ)*π+I*log ((π:ℂ)^(-1/2:ℂ)*2^(-a-1/2:ℂ)*Gamma (1/2+a))

/-- pcfZeroLambda. -/
@[dlmf 12.11.E3]
def pcfZeroLambda (a : ℝ) (s : ℕ) : ℂ :=
  log (pcfZeroTau a s)-π*I/2

/-- pcfU complex zero strings. -/
@[dlmf 12.11.E1]
theorem pcfU_complex_zero_strings {a : ℝ} (ha : -1/2 < a) :
    ∃ Z : ℕ → ℂ, (∀ᶠ s in atTop, pcfU a (Z s)=0 ∧ pcfU a (star (Z s))=0 ∧ 0 < (Z s).im) ∧ (fun s => Z s/(exp (3*π*I/4)*(2*pcfZeroTau a s)^(1/2:ℂ))-1+I*a*pcfZeroLambda a s/(2*pcfZeroTau a s)-(2*a^2*(pcfZeroLambda a s)^2-8*a^2*pcfZeroLambda a s+4*a^2+3)/(16*(pcfZeroTau a s)^2)) =O[atTop] (fun s => (pcfZeroLambda a s)^3/(pcfZeroTau a s)^3) := by
  sorry

end DLMF.Confluent
