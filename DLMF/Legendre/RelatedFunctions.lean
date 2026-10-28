/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Hypergeometric
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Gegenbauer and Jacobi representations and degree derivatives

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- Gegenbauer function at regular parameters; gamma singularities of representations are handled by limits of the complete expression. -/
def gegenbauerFunction (α β z : ℂ) : ℂ :=
  Gamma (α+2*β)*Gamma (β+1/2)/(Gamma (2*β)*Gamma (α+1))*regularizedGaussHG (-α) (α+2*β) (β+1/2) ((1-z)/2)

/-- Jacobi function at regular alpha, with Gauss continuation. -/
def jacobiFunction (α β lam t : ℂ) : ℂ :=
  Gamma (α+1)*regularizedGaussHG ((α+β+1+I*lam)/2) ((α+β+1-I*lam)/2) (α+1) (-(sinh t)^2)

/-- Removable exceptional parameters use the limit of the whole representation. -/
@[dlmf 14.3.E21]
theorem ferrersP_gegenbauer (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun m : ℂ => 2^m*Gamma (1-2*m)*Gamma (ν+m+1)/(Gamma (ν-m+1)*Gamma (1-m)*(1-x^2:ℂ)^(m/2))*gegenbauerFunction (ν+m) (1/2-m) x) (𝓝[≠] μ) (𝓝 (ferrersP ν μ x)) := by
  have hne := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have ht : ((1:ℂ)-x)/2 ∈ cutPlane := by
    rw [mem_cutPlane, show (1:ℂ) - (1-(x:ℂ))/2 = (((1+x)/2 : ℝ) : ℂ) by push_cast; ring]
    exact Or.inl (by simp only [ofReal_re]; linarith [hx.1])
  set g : ℂ → ℂ := fun m => 2^m*((1-(x:ℂ)^2)^(m/2))⁻¹*regularizedGaussHG (-(ν+m)) (ν-m+1) (1-m) ((1-(x:ℂ))/2)
  have hg : Continuous g := by
    have h1 : Continuous fun m : ℂ => (2:ℂ)^m := continuous_const_cpow' (by norm_num)
    have h2 : Continuous fun m : ℂ => ((1-(x:ℂ)^2)^(m/2))⁻¹ :=
      ((continuous_const_cpow' hne).comp (by fun_prop)).inv₀ (fun m => cpow_ne_zero_iff.mpr (Or.inl hne))
    have h3 := (differentiable_regularizedGaussHG_comp (A := fun m => -(ν+m)) (B := fun m => ν-m+1)
      (C := fun m => 1-m) (by fun_prop) (by fun_prop) (by fun_prop) ht).continuous
    exact (h1.mul h2).mul h3
  have hgμ : g μ = ferrersP ν μ x := by
    simp only [g, ferrersP]
    rw [regularizedGaussHG_euler _ _ _ ht, show (1:ℂ)-μ-(-(ν+μ))-(ν-μ+1) = μ by ring,
      show (1:ℂ)-μ-(-(ν+μ)) = ν+1 by ring, show (1:ℂ)-μ-(ν-μ+1) = -ν by ring,
      show (1:ℂ)-(1-(x:ℂ))/2 = (1+x)/2 by ring]
    have hq := ferrers_quadratic_gauge μ hx
    have hp : (1+(x:ℂ))/2 ≠ 0 := by
      rw [show (1+(x:ℂ))/2 = (((1+x)/2:ℝ):ℂ) by push_cast; ring]
      exact_mod_cast (by linarith [hx.1] : (1+x)/2 ≠ 0)
    have hpp : ((1+(x:ℂ))/2)^(-μ)*((1+(x:ℂ))/2)^μ = 1 := by
      rw [cpow_neg]; exact inv_mul_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl hp))
    rw [← cpow_neg, show -(μ/2) = -μ/2 by ring, ← hq]
    linear_combination (((((1+x)/(1-x)):ℝ):ℂ)^(μ/2)*regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-(x:ℂ))/2))*hpp
  rw [← hgμ]
  refine (hg.tendsto μ).mono_left nhdsWithin_le_nhds |>.congr' ?_
  filter_upwards [eventually_affine_ne_neg_nat (a := -2) (by norm_num) 1 μ,
    eventually_affine_ne_neg_nat (a := 1) one_ne_zero (ν+1) μ,
    eventually_affine_ne_neg_nat (a := -1) (by norm_num) (ν+1) μ,
    eventually_affine_ne_neg_nat (a := -1) (by norm_num) 1 μ] with m h1 h2 h3 h4
  have g1 := Complex.Gamma_ne_zero (s := 1-2*m) (fun k hk => h1 k (by linear_combination hk))
  have g2 := Complex.Gamma_ne_zero (s := ν+m+1) (fun k hk => h2 k (by linear_combination hk))
  have g3 := Complex.Gamma_ne_zero (s := ν-m+1) (fun k hk => h3 k (by linear_combination hk))
  have g4 := Complex.Gamma_ne_zero (s := 1-m) (fun k hk => h4 k (by linear_combination hk))
  have hw : (1-(x:ℂ)^2)^(m/2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hne)
  simp only [g, gegenbauerFunction]
  rw [show ν+m+2*(1/2-m) = ν-m+1 by ring, show (1:ℂ)/2-m+1/2 = 1-m by ring,
    show 2*((1:ℂ)/2-m) = 1-2*m by ring]
  have g1' : Gamma (1 - m*2) ≠ 0 := by rw [mul_comm]; exact g1
  field_simp

/-- Removable exceptional parameters use the limit of the whole representation. -/
@[dlmf 14.3.E22]
theorem associatedP_gegenbauer (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (hre : 0 < z.re) :
    Tendsto (fun m : ℂ => 2^m*Gamma (1-2*m)*Gamma (ν+m+1)/(Gamma (ν-m+1)*Gamma (1-m)*legendreBranchPower m z)*gegenbauerFunction (ν+m) (1/2-m) z) (𝓝[≠] μ) (𝓝 (associatedP ν μ z)) := by
  have hz' := one_add_mem_slitPlane_of_sub_one hz
  have ht := mem_cutPlane_of_one_add hz'
  set g : ℂ → ℂ := fun m => 2^m*(legendreBranchPower m z)⁻¹*regularizedGaussHG (-(ν+m)) (ν-m+1) (1-m) ((1-z)/2)
  have hg : Continuous g := by
    have h1 : Continuous fun m : ℂ => (2:ℂ)^m := continuous_const_cpow' (by norm_num)
    have h2 : Continuous fun m : ℂ => (legendreBranchPower m z)⁻¹ :=
      (by unfold legendreBranchPower; fun_prop : Continuous fun m : ℂ => legendreBranchPower m z).inv₀
        (fun m => exp_ne_zero _)
    have h3 := (differentiable_regularizedGaussHG_comp (A := fun m => -(ν+m)) (B := fun m => ν-m+1)
      (C := fun m => 1-m) (by fun_prop) (by fun_prop) (by fun_prop) ht).continuous
    exact (h1.mul h2).mul h3
  have hgμ : g μ = associatedP ν μ z := by
    simp only [g, associatedP]
    rw [regularizedGaussHG_euler _ _ _ ht, show (1:ℂ)-μ-(-(ν+μ))-(ν-μ+1) = μ by ring,
      show (1:ℂ)-μ-(-(ν+μ)) = ν+1 by ring, show (1:ℂ)-μ-(ν-μ+1) = -ν by ring,
      show (1:ℂ)-(1-z)/2 = (z+1)*(((1/2:ℝ)):ℂ) by push_cast; ring]
    have hp : z+1 ≠ 0 := by rw [add_comm]; exact slitPlane_ne_zero hz'
    rw [cpow_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0),
      cpow_def_of_ne_zero (mul_ne_zero hp (by norm_num)), log_mul_ofReal _ (by norm_num) _ hp,
      legendreBranchPower, ← exp_neg, show Real.log (1/2) = -Real.log 2 by
        rw [one_div, Real.log_inv], show Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) by
        rw [← ofReal_ofNat, ofReal_log (by norm_num)]]
    rw [← mul_assoc, ← exp_add]
    congr 1
    rw [← exp_add]
    congr 1
    push_cast; ring
  rw [← hgμ]
  refine (hg.tendsto μ).mono_left nhdsWithin_le_nhds |>.congr' ?_
  filter_upwards [eventually_affine_ne_neg_nat (a := -2) (by norm_num) 1 μ,
    eventually_affine_ne_neg_nat (a := 1) one_ne_zero (ν+1) μ,
    eventually_affine_ne_neg_nat (a := -1) (by norm_num) (ν+1) μ,
    eventually_affine_ne_neg_nat (a := -1) (by norm_num) 1 μ] with m h1 h2 h3 h4
  have g1 := Complex.Gamma_ne_zero (s := 1-2*m) (fun k hk => h1 k (by linear_combination hk))
  have g2 := Complex.Gamma_ne_zero (s := ν+m+1) (fun k hk => h2 k (by linear_combination hk))
  have g3 := Complex.Gamma_ne_zero (s := ν-m+1) (fun k hk => h3 k (by linear_combination hk))
  have g4 := Complex.Gamma_ne_zero (s := 1-m) (fun k hk => h4 k (by linear_combination hk))
  have hw : legendreBranchPower m z ≠ 0 := exp_ne_zero _
  simp only [g, gegenbauerFunction]
  rw [show ν+m+2*(1/2-m) = ν-m+1 by ring, show (1:ℂ)/2-m+1/2 = 1-m by ring,
    show 2*((1:ℂ)/2-m) = 1-2*m by ring]
  have g1' : Gamma (1 - m*2) ≠ 0 := by rw [mul_comm]; exact g1
  field_simp

/-- DLMF 14.3.23: for `x > 1`, `P^μ_ν(x)` is the limit as `m → μ` (`m ≠ μ`) of `(1/Γ(1-m))
((x+1)/(x-1))^{m/2} φ^{(-m,m)}_{-i(2ν+1)}(arcsinh(((x-1)/2)^{1/2}))`, with `φ` the Jacobi function;
the limit removes the poles of `1/Γ(1-m)` at positive integers. -/
@[dlmf 14.3.E23]
theorem associatedP_jacobi (ν μ : ℂ) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun m : ℂ => 1/Gamma (1-m)*((x+1)/(x-1):ℂ)^(m/2)*jacobiFunction (-m) m (-I*(2*ν+1)) (Real.arsinh (Real.sqrt (x/2-1/2)))) (𝓝[≠] μ) (𝓝 (associatedP ν μ x)) := by
  have hsh : -(sinh ((Real.arsinh (Real.sqrt (x/2-1/2)) : ℝ) : ℂ))^2 = (1-(x:ℂ))/2 := by
    rw [← ofReal_sinh, Real.sinh_arsinh, ← ofReal_pow, Real.sq_sqrt (by linarith)]
    push_cast; ring
  have ht : (1-(x:ℂ))/2 ∈ cutPlane := by
    rw [mem_cutPlane, show (1:ℂ) - (1-(x:ℂ))/2 = (((1+x)/2 : ℝ) : ℂ) by push_cast; ring]
    exact Or.inl (by simp only [ofReal_re]; linarith)
  have hR : ((x+1)/(x-1):ℂ) ≠ 0 := by
    rw [show ((x+1)/(x-1):ℂ) = (((x+1)/(x-1):ℝ):ℂ) by push_cast; ring]
    exact_mod_cast (div_pos (by linarith) (by linarith)).ne'
  set g : ℂ → ℂ := fun m => ((x+1)/(x-1):ℂ)^(m/2)*regularizedGaussHG (ν+1) (-ν) (1-m) ((1-(x:ℂ))/2)
  have hg : Continuous g := by
    have h3 := (differentiable_regularizedGaussHG_comp (A := fun _ => ν+1) (B := fun _ => -ν)
      (C := fun m => 1-m) (by fun_prop) (by fun_prop) (by fun_prop) ht).continuous
    exact ((continuous_const_cpow' hR).comp (by fun_prop)).mul h3
  have hgμ : g μ = associatedP ν μ x := by
    simp only [g, associatedP]
    congr 1
    rw [cpow_def_of_ne_zero hR]
    congr 1
    have h1 : (0:ℝ) < x+1 := by linarith
    have h2 : (0:ℝ) < x-1 := by linarith
    rw [show ((x+1)/(x-1):ℂ) = (((x+1)/(x-1):ℝ):ℂ) by push_cast; ring, ← ofReal_log (div_pos h1 h2).le,
      Real.log_div h1.ne' h2.ne', show (x:ℂ)+1 = ((x+1:ℝ):ℂ) by push_cast; ring,
      show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; ring, ← ofReal_log h1.le, ← ofReal_log h2.le]
    push_cast; ring
  rw [← hgμ]
  refine (hg.tendsto μ).mono_left nhdsWithin_le_nhds |>.congr' ?_
  filter_upwards [eventually_affine_ne_neg_nat (a := -1) (by norm_num) 1 μ] with m h4
  have g4 := Complex.Gamma_ne_zero (s := 1-m) (fun k hk => h4 k (by linear_combination hk))
  simp only [g, jacobiFunction]
  rw [hsh, show (-m+m+1+I*(-I*(2*ν+1)))/2 = ν+1 by ring_nf; rw [I_sq]; ring,
    show (-m+m+1-I*(-I*(2*ν+1)))/2 = -ν by ring_nf; rw [I_sq]; ring, show -m+1 = 1-m by ring]
  field_simp

/-- The outside-interval degree-derivative series, convergent when abs(1-z) is less than two. -/
def associatedDegreeA (ν μ z : ℂ) : ℂ :=
  sin (ν*π)*exp (μ/2*(log (z+1)-log (z-1)))*∑' k : ℕ, ((1-z)/2)^k*Gamma (k-ν)*Gamma (k+ν+1)/((k.factorial:ℂ)*Gamma (k-μ+1))*(digamma (k+ν+1)-digamma (k-ν))

/-- DLMF 14.11.1 (associated case): for non-integer `ν`, `z ∉ (-∞, 1]` and `|1-z| < 2`,
`∂P^μ_ν(z)/∂ν = π cot(νπ) P^μ_ν(z) - (1/π) A^μ_ν(z)`, with `A^μ_ν` the series 14.11.3 continued to
complex `z`. -/
@[dlmf 14.11.E1]
theorem associatedP_degree_deriv {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (hdisk : ‖1-z‖ < 2) :
    HasDerivAt (fun ν => associatedP ν μ z) (π*cos (ν*π)/sin (ν*π)*associatedP ν μ z-associatedDegreeA ν μ z/π) ν := by
  have hw : ‖(1-z)/2‖ < 1 := by
    rw [norm_div, norm_ofNat]
    exact (div_lt_one (by norm_num)).mpr hdisk
  set F : ℂ → ℂ := fun ν' => regularizedGaussHGFun (ν'+1) (-ν') (1-μ) ((1-z)/2)
  set pref : ℂ := exp (μ/2*(log (z+1)-log (z-1)))
  have hP : ∀ ν', associatedP ν' μ z = pref * F ν' := fun ν' => by
    simp only [associatedP, pref, F]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw]
  have hFd : Differentiable ℂ F :=
    differentiable_regularizedGaussHGFun_of_differentiable (differentiable_id.add_const 1)
      differentiable_neg (differentiable_const _) hw
  have hd : HasDerivAt (fun ν' => associatedP ν' μ z) (pref * deriv F ν) ν := by
    simp only [hP]; exact ((hFd ν).hasDerivAt).const_mul pref
  refine hd.congr_deriv ?_
  have hR := legHyp_hasSum_A_complex hν μ hw
  unfold associatedDegreeA
  rw [hR.tsum_eq, hP ν, mul_comm (ν:ℂ) π]
  have hs := DLMF.Hypergeometric.sin_pi_mul_ne_zero_of_not_int hν
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  dsimp only [pref, F]
  generalize sin (π*ν) = s at hs ⊢
  field_simp
  ring

/- DLMF 14.27’s unqualified left-cut zero rule is not admitted: for
ν=1, μ=-1/2 the first-kind function has its only algebraic zero at x=-1/2,
whereas the first listed case predicts one zero in (-∞,-1). This source
claim requires correction or additional hypotheses; see the acquisition ledger. -/

end DLMF.Legendre
