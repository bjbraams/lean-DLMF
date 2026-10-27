/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Associated

/-!
# Degree and order recurrences and integer derivatives

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- The balanced upper-parameter contiguous relation, including zero upper parameters. -/
theorem regularizedGaussHG_balanced_ab (a c : ℂ) {w : ℂ} (hw : w ∈ cutPlane) :
    2*regularizedGaussHG (-a) a c w-regularizedGaussHG (1-a) a c w-
      regularizedGaussHG (-a) (a+1) c w=0 := by
  by_cases ha : a=0
  · subst a
    have h := regularizedGaussHG_contiguous_shift_b 0 0 c hw
    have hs := regularizedGaussHG_symm 1 0 c hw
    norm_num at h ⊢
    linear_combination 2*h-hs
  · have h := regularizedGaussHG_contiguous_ab (-a) a c hw
    rw [show -a+1=1-a by ring] at h
    apply (mul_left_cancel₀ ha)
    linear_combination h

/-- The degree recurrence before multiplying by the associated or Ferrers gauge. -/
theorem regularizedGaussHG_legendre_degree (ν c : ℂ) {w : ℂ} (hw : w ∈ cutPlane) :
    (ν+c)*regularizedGaussHG (-ν-1) (ν+2) c w-
      (2*ν+1)*(1-2*w)*regularizedGaussHG (-ν) (ν+1) c w+
      (ν+1-c)*regularizedGaussHG (-ν+1) ν c w=0 := by
  have E1 := regularizedGaussHG_contiguous_ab (-ν-1) (ν+1) c hw
  have E2 := regularizedGaussHG_contiguous_ab (-ν) ν c hw
  have E3 := regularizedGaussHG_contiguous_a (-ν) (ν+1) c hw
  have E4 := regularizedGaussHG_contiguous_a_b_pred (-ν) (ν+1) c hw
  have B1 := regularizedGaussHG_balanced_ab (ν+1) c hw
  have B2 := regularizedGaussHG_balanced_ab ν c hw
  rw [show -ν-1+1= -ν by ring,show ν+1+1=ν+2 by ring] at E1
  rw [show ν+1-1=ν by ring] at E4
  rw [show -(ν+1)= -ν-1 by ring,show 1-(ν+1)= -ν by ring,
    show ν+1+1=ν+2 by ring] at B1
  rw [show 1-ν= -ν+1 by ring] at B2
  linear_combination -E1-E2+2*E3+2*E4-(c-1)*(B1-B2)

/-- The derivative recurrence before multiplying by its gauge. -/
theorem regularizedGaussHG_legendre_derivative (ν c : ℂ) {w : ℂ} (hw : w ∈ cutPlane) :
    (1-c)*regularizedGaussHG (-ν) (ν+1) c w+
      2*w*(1-w)*ν*(ν+1)*regularizedGaussHG (-ν+1) (ν+2) (c+1) w-
      (ν+1-c)*regularizedGaussHG (-ν+1) ν c w+
      ν*(1-2*w)*regularizedGaussHG (-ν) (ν+1) c w=0 := by
  have R1 := regularizedGaussHG_contiguous_c_succ_deriv (-ν) (ν+1) c hw
  have R2 := regularizedGaussHG_contiguous_a_c_succ (-ν) (ν+1) c hw
  have E2 := regularizedGaussHG_contiguous_ab (-ν) ν c hw
  have E4 := regularizedGaussHG_contiguous_a_b_pred (-ν) (ν+1) c hw
  have B2 := regularizedGaussHG_balanced_ab ν c hw
  rw [show ν+1-1=ν by ring] at E4
  rw [show 1-ν= -ν+1 by ring] at B2
  rw [show ν+1+1=ν+2 by ring] at R1
  linear_combination (-2*w)*R1-2*R2+E2-2*E4-(c-1)*B2

/-- The simultaneous degree/order contiguous relation before applying either gauge. -/
theorem regularizedGaussHG_legendre_order (ν c : ℂ) {w : ℂ} (hw : w∈cutPlane) :
    (2-2*w)*regularizedGaussHG (ν+1) (-ν) (c-1) w-
      (ν+c)*regularizedGaussHG (ν+2) (-ν-1) c w+
      (ν+2-c)*(1-2*w)*regularizedGaussHG (ν+1) (-ν) c w=0 := by
  have he := regularizedGaussHG_contiguous_a_pred_c_pred (-ν) (ν+1) c hw
  have hb := regularizedGaussHG_balanced_ab (ν+1) c hw
  rw [show -(ν+1)= -ν-1 by ring,show 1-(ν+1)= -ν by ring,
    show ν+1+1=ν+2 by ring] at hb
  rw [regularizedGaussHG_symm (ν+1) (-ν) (c-1) hw,
    regularizedGaussHG_symm (ν+2) (-ν-1) c hw,regularizedGaussHG_symm (ν+1) (-ν) c hw]
  linear_combination -2*he+(ν+c)*hb

/-- The three-order relation retains all reciprocal-Gamma exceptional values. -/
theorem regularizedGaussHG_legendre_orders (ν c : ℂ) {w : ℂ} (hw : w∈cutPlane) :
    (2-2*w)*regularizedGaussHG (ν+1) (-ν) (c-2) w+
      2*(2-c)*(1-2*w)*regularizedGaussHG (ν+1) (-ν) (c-1) w+
      (ν+c-1)*(ν+2-c)*(2*w)*regularizedGaussHG (ν+1) (-ν) c w=0 := by
  have he := regularizedGaussHG_contiguous_c_three (ν+1) (-ν) (c-1) hw
  rw [show c-1-1=c-2 by ring,show c-1+1=c by ring] at he
  linear_combination -2*he

/-- The positive real Ferrers gauge has compatible square roots at consecutive orders. -/
theorem ferrers_gauge_shifts (μ : ℂ) {x : ℝ} (hx : x∈Ioo (-1:ℝ) 1) :
    let r : ℂ := ((1+x)/(1-x):ℝ)
    (1-x^2:ℂ)^(1/2:ℂ)*r^((μ+1)/2)=(1+x)*r^(μ/2) ∧
    (1-x^2:ℂ)^(-1/2:ℂ)*r^((μ+1)/2)=r^(μ/2)/(1-x) ∧
    r^((μ+2)/2)=r*r^(μ/2) := by
  dsimp only
  let r : ℝ := (1+x)/(1-x)
  have hp : 0<1+x := by linarith [hx.1]
  have hm : 0<1-x := by linarith [hx.2]
  have ht : 0<1-x^2 := by nlinarith [hx.1,hx.2]
  have hr : 0<r := div_pos hp hm
  have ht0 : (1-x^2:ℂ)≠0 := by exact_mod_cast ht.ne'
  have hr0 : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have he : (1-x^2)*r=(1+x)^2 := by dsimp [r]; field_simp; ring
  have hs : Real.sqrt (1-x^2)*Real.sqrt r=1+x := by
    rw [← Real.sqrt_mul ht.le,he,Real.sqrt_sq hp.le]
  have hpow : (1-x^2:ℂ)^(1/2:ℂ)*(r:ℂ)^(1/2:ℂ)=1+x := by
    have h := congrArg (fun t : ℝ=>(t:ℂ)) hs
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,Complex.ofReal_mul,
      Complex.ofReal_cpow ht.le,Complex.ofReal_cpow hr.le] at h
    norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at h
    convert h using 1 <;> push_cast <;> ring
  have hsq : ((1-x^2:ℂ)^(1/2:ℂ))^2=1-x^2 := by
    rw [← cpow_nat_mul]
    norm_num
  have hhalf : (r:ℂ)^(1/2:ℂ)*(1-x)=(1-x^2:ℂ)^(1/2:ℂ) := by
    apply mul_left_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl ht0) : (1-x^2:ℂ)^(1/2:ℂ)≠0)
    rw [← mul_assoc,hpow]
    linear_combination -hsq
  have hi : (1-x^2:ℂ)^(-1/2:ℂ)*(r:ℂ)^(1/2:ℂ)=1/(1-x) := by
    rw [show (-1:ℂ)/2= -(1/2) by ring,cpow_neg]
    have hm0 : (1-x:ℂ)≠0 := by exact_mod_cast hm.ne'
    field_simp [cpow_ne_zero_iff.mpr (Or.inl ht0),hm0]
    linear_combination hhalf
  have h1 : (r:ℂ)^((μ+1)/2)=(r:ℂ)^(μ/2)*(r:ℂ)^(1/2:ℂ) := by
    rw [← cpow_add _ _ hr0]; congr 1; ring
  have h2 : (r:ℂ)^((μ+2)/2)=(r:ℂ)*(r:ℂ)^(μ/2) := by
    calc
      (r:ℂ)^((μ+2)/2)=(r:ℂ)^(1+μ/2) := by congr 1; ring
      _ = _ := by rw [cpow_add _ _ hr0,cpow_one]
  change _ ∧ _ ∧ _
  constructor
  · rw [h1]
    linear_combination (r:ℂ)^(μ/2)*hpow
  · constructor
    · rw [h1]
      linear_combination (r:ℂ)^(μ/2)*hi
    · exact h2

/-- The logarithmic associated-P gauge retains its inherited product branches under order shifts. -/
theorem associated_gauge_shifts (μ : ℂ) {z : ℂ} (hz : z-1∈slitPlane) :
    let E := exp (μ/2*(log (z+1)-log (z-1)))
    exp ((μ+2)/2*(log (z+1)-log (z-1)))=E*(z+1)/(z-1) ∧
    legendreBranchPower (-1) z*exp ((μ+1)/2*(log (z+1)-log (z-1)))=E/(z-1) ∧
    legendreBranchPower 1 z*exp ((μ+1)/2*(log (z+1)-log (z-1)))=E*(z+1) := by
  dsimp only
  have hm := slitPlane_ne_zero hz
  have hp : z+1≠0 := by simpa [add_comm] using slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hz)
  constructor
  · rw [show (μ+2)/2*(log (z+1)-log (z-1))=
      μ/2*(log (z+1)-log (z-1))+(log (z+1)-log (z-1)) by ring,
      Complex.exp_add,Complex.exp_sub,Complex.exp_log hp,Complex.exp_log hm]
    ring
  · constructor
    · unfold legendreBranchPower
      rw [← Complex.exp_add,show (-1:ℂ)/2*(log (z-1)+log (z+1))+
        (μ+1)/2*(log (z+1)-log (z-1))=μ/2*(log (z+1)-log (z-1))-log (z-1) by ring,
        Complex.exp_sub,Complex.exp_log hm]
    · unfold legendreBranchPower
      rw [← Complex.exp_add,show (1:ℂ)/2*(log (z-1)+log (z+1))+
        (μ+1)/2*(log (z+1)-log (z-1))=μ/2*(log (z+1)-log (z-1))+log (z+1) by ring,
        Complex.exp_add,Complex.exp_log hp]

/-- ferrersP recurrence 1. -/
@[dlmf 14.10.E1]
theorem ferrersP_recurrence_1 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν (μ+2) x+2*(μ+1)*x*(1-x^2:ℂ)^(-1/2:ℂ)*ferrersP ν (μ+1) x+(ν-μ)*(ν+μ+1)*ferrersP ν μ x=0 := by
  have hs : 1+(x:ℂ)∈slitPlane := Or.inl (by simp; linarith [hx.1])
  have hw := mem_cutPlane_of_one_add hs
  have hg := ferrers_gauge_shifts μ hx
  have he := regularizedGaussHG_legendre_orders ν (1-μ) hw
  dsimp only at hg
  simp only [ferrersP]
  rw [show (1:ℂ)-(μ+1)=1-μ-1 by ring,show (1:ℂ)-(μ+2)=1-μ-2 by ring]
  have hm : (1-x:ℂ)≠0 := by exact_mod_cast (show (1-x:ℝ)≠0 by linarith [hx.2])
  have hr : (((1+x)/(1-x):ℝ):ℂ)=(1+x)/(1-x) := by push_cast; rfl
  rw [hg.2.2]
  linear_combination (norm := (field_simp [hm]; ring))
    (((((1+x)/(1-x):ℝ):ℂ)^(μ/2))/(1-x))*he+
    2*(μ+1)*x*regularizedGaussHG (ν+1) (-ν) (1-μ-1) ((1-(x:ℂ))/2)*hg.2.1+
    ((((1+x)/(1-x):ℝ):ℂ)^(μ/2))*regularizedGaussHG (ν+1) (-ν) (1-μ-2) ((1-(x:ℂ))/2)*hr

/-- ferrersP recurrence 2. -/
@[dlmf 14.10.E2]
theorem ferrersP_recurrence_2 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)^(1/2:ℂ)*ferrersP ν (μ+1) x-(ν-μ+1)*ferrersP (ν+1) μ x+(ν+μ+1)*x*ferrersP ν μ x=0 := by
  have hs : 1+(x:ℂ)∈slitPlane := Or.inl (by simp; linarith [hx.1])
  have hw := mem_cutPlane_of_one_add hs
  have hg := ferrers_gauge_shifts μ hx
  have he := regularizedGaussHG_legendre_order ν (1-μ) hw
  dsimp only at hg
  simp only [ferrersP]
  rw [show (1:ℂ)-(μ+1)=1-μ-1 by ring,
    show ν+1+1=ν+2 by ring,show -(ν+1)= -ν-1 by ring]
  linear_combination ((((1+x)/(1-x):ℝ):ℂ)^(μ/2))*he+
    regularizedGaussHG (ν+1) (-ν) (1-μ-1) ((1-(x:ℂ))/2)*hg.1

/-- ferrersP recurrence 3. -/
@[dlmf 14.10.E3]
theorem ferrersP_recurrence_3 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (ν-μ+2)*ferrersP (ν+2) μ x-(2*ν+3)*x*ferrersP (ν+1) μ x+(ν+μ+1)*ferrersP ν μ x=0 := by
  have hs : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  have hw := mem_cutPlane_of_one_add hs
  have he := regularizedGaussHG_legendre_degree (ν+1) (1-μ) hw
  simp only [ferrersP]
  rw [regularizedGaussHG_symm (ν+2+1) (-(ν+2)) (1-μ) hw,
    regularizedGaussHG_symm (ν+1+1) (-(ν+1)) (1-μ) hw,
    regularizedGaussHG_symm (ν+1) (-ν) (1-μ) hw]
  rw [show -(ν+2)= -(ν+1)-1 by ring,show ν+2+1=(ν+1)+2 by ring,
    show -ν= -(ν+1)+1 by ring,show ν+1+1=ν+2 by ring] at *
  linear_combination ((((1+x)/(1-x):ℝ):ℂ)^(μ/2))*he

/-- ferrersP recurrence 5. -/
@[dlmf 14.10.E5]
theorem ferrersP_recurrence_5 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)*deriv (ferrersP ν μ) x=(ν+μ)*ferrersP (ν-1) μ x-ν*x*ferrersP ν μ x := by
  have hs : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  have hw := mem_cutPlane_of_one_add hs
  have hd : HasDerivAt (ferrersP ν μ) _ x :=
    hasDerivAt_ferrers_aux (ν+1) (-ν) (1-μ) (μ/2) hx
  rw [hd.deriv]
  have he := regularizedGaussHG_legendre_derivative ν (1-μ) hw
  have hn : 1-(x:ℂ)^2≠0 := by
    rw [show 1-(x:ℂ)^2=((1-x^2:ℝ):ℂ) by push_cast; ring,ofReal_ne_zero]
    nlinarith [hx.1,hx.2]
  simp only [ferrersP]
  rw [regularizedGaussHG_symm (ν+1) (-ν) (1-μ) hw,
    regularizedGaussHG_symm (ν-1+1) (-(ν-1)) (1-μ) hw,
    regularizedGaussHG_symm (ν+1+1) (-ν+1) (1-μ+1) hw]
  rw [show -(ν-1)= -ν+1 by ring,show ν-1+1=ν by ring]
  rw [show ν+1+1=ν+2 by ring] at *
  generalize (((1+x)/(1-x):ℝ):ℂ)^(μ/2)=A
  field_simp [hn]
  linear_combination (2*A)*he
/-- ferrersP recurrence 4. -/
@[dlmf 14.10.E4]
theorem ferrersP_recurrence_4 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)*deriv (ferrersP ν μ) x=(μ-ν-1)*ferrersP (ν+1) μ x+(ν+1)*x*ferrersP ν μ x := by
  have hd := ferrersP_recurrence_5 ν μ hx
  have hr := ferrersP_recurrence_3 (ν-1) μ hx
  rw [show ν-1+2=ν+1 by ring,show ν-1+1=ν by ring] at hr
  linear_combination hd+hr


/-! ### Ferrers-Q recurrences by continuity in the degree

For non-real `ν+μ`, `𝖰` is a combination of `𝖯(±x)`; the recurrences then extend to all
regular parameters by continuity along `ν + i t`, `t → 0⁺`. -/

/-- A non-real `ν+μ` is a regular parameter pair. -/
theorem legendreQRegular_of_im_ne_zero {ν μ : ℂ} (h : (ν+μ).im ≠ 0) : LegendreQRegular ν μ := by
  intro n hn; apply h; rw [hn]; simp

/-- A non-real `z` is not a zero of `sin (z π)`. -/
theorem sin_mul_pi_ne_zero_of_im_ne_zero {z : ℂ} (h : z.im ≠ 0) : sin (z*π) ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h0
  have := mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) hk
  apply h; rw [this]; simp

/-- Limits along `ν₀ + i t`: an identity valid for non-real `ν+μ` extends to a point of
continuity. -/
theorem eq_zero_of_im_ne_zero {G : ℂ → ℂ} {ν₀ μ : ℂ} (hG : ContinuousAt G ν₀)
    (h : ∀ ν, (ν+μ).im ≠ 0 → G ν = 0) : G ν₀ = 0 := by
  set a := (ν₀+μ).im
  have hp : Tendsto (fun t : ℝ => ν₀+I*t) (𝓝[>] 0) (𝓝 ν₀) := by
    have : Tendsto (fun t : ℝ => ν₀+I*t) (𝓝 0) (𝓝 (ν₀+I*((0:ℝ):ℂ))) :=
      ((continuous_const.add (continuous_const.mul continuous_ofReal)).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, G (ν₀+I*t) = 0 := by
    have hne : ∀ᶠ t : ℝ in 𝓝[>] 0, a+t ≠ 0 := by
      rcases le_or_gt 0 a with ha | ha
      · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t); linarith
      · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < -a by linarith)] with t ht
        linarith [ht.2]
    filter_upwards [hne] with t ht
    exact h _ (by simpa [a, add_comm, add_left_comm, add_assoc] using ht)
  have h1 : Tendsto (fun t : ℝ => G (ν₀+I*t)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm)
  exact tendsto_nhds_unique (hG.tendsto.comp hp) h1

/-- Explicit derivative of the even quadratic solution. -/
theorem hasDerivAt_ferrersEven (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (ferrersEven ν μ) ((1-(x:ℂ)^2)^(-μ/2)*(μ*x/(1-(x:ℂ)^2)*
      regularizedGaussHG (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) ((x:ℂ)^2)+2*x*((-(ν+μ)/2)*((ν-μ+1)/2)*
      regularizedGaussHG (-(ν+μ)/2+1) ((ν-μ+1)/2+1) (1/2+1) ((x:ℂ)^2)))) x := by
  have h := (quadratic_gauss_gauge_jets (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) μ
    (ferrers_one_sub_sq_mem_slitPlane hx)).1.comp_ofReal
  beta_reduce at h
  rw [deriv_regularizedGaussHG _ _ _ (ferrers_sq_mem_cutPlane hx)] at h
  exact h

/-- Explicit derivative of the odd quadratic solution. -/
theorem hasDerivAt_ferrersOdd (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (ferrersOdd ν μ) ((1-(x:ℂ)^2)^(-μ/2)*regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) ((x:ℂ)^2)+
      x*((1-(x:ℂ)^2)^(-μ/2)*(μ*x/(1-(x:ℂ)^2)*
      regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) ((x:ℂ)^2)+2*x*(((1-ν-μ)/2)*((ν-μ+2)/2)*
      regularizedGaussHG ((1-ν-μ)/2+1) ((ν-μ+2)/2+1) (3/2+1) ((x:ℂ)^2))))) x := by
  have h := (quadratic_gauss_gauge_jets ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) μ
    (ferrers_one_sub_sq_mem_slitPlane hx)).1.comp_ofReal
  beta_reduce at h
  rw [deriv_regularizedGaussHG _ _ _ (ferrers_sq_mem_cutPlane hx)] at h
  exact ((hasDerivAt_id x).ofReal_comp.mul h).congr_deriv (by simp)

/-- The two Gamma numerators of `𝖰^μ_ν` are continuous at a regular degree. -/
theorem continuousAt_Gamma_ferrersQ {ν₀ μ : ℂ} (h : LegendreQRegular ν₀ μ) :
    ContinuousAt (fun ν => Gamma ((ν+μ+1)/2)) ν₀ ∧ ContinuousAt (fun ν => Gamma ((ν+μ+2)/2)) ν₀ := by
  have h1 : ∀ m : ℕ, (ν₀+μ+1)/2 ≠ -m := fun m hm => h (2*m) (by push_cast; linear_combination 2*hm)
  have h2 : ∀ m : ℕ, (ν₀+μ+2)/2 ≠ -m := fun m hm => h (2*m+1) (by push_cast; linear_combination 2*hm)
  exact ⟨ContinuousAt.comp (g := Gamma) (differentiableAt_Gamma _ h1).continuousAt (by fun_prop),
    ContinuousAt.comp (g := Gamma) (differentiableAt_Gamma _ h2).continuousAt (by fun_prop)⟩

/-- `𝖰^μ_ν(x)` is continuous in the degree at a regular parameter. -/
theorem continuousAt_ferrersQ_degree {ν₀ μ : ℂ} (h : LegendreQRegular ν₀ μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ContinuousAt (fun ν => ferrersQ ν μ x) ν₀ := by
  obtain ⟨c1, c2⟩ := continuousAt_Gamma_ferrersQ h
  have hr1 := (continuous_recip_Gamma.comp (by fun_prop : Continuous fun ν : ℂ => (ν-μ+1)/2)).continuousAt (x := ν₀)
  have hr2 := (continuous_recip_Gamma.comp (by fun_prop : Continuous fun ν : ℂ => (ν-μ+2)/2)).continuousAt (x := ν₀)
  have hE : Continuous fun ν => ferrersEven ν μ x := continuous_const.mul
    (continuous_regularizedGaussHG_sq (by fun_prop) (by fun_prop) (by fun_prop) hx)
  have hO : Continuous fun ν => ferrersOdd ν μ x := continuous_const.mul (continuous_const.mul
    (continuous_regularizedGaussHG_sq (by fun_prop) (by fun_prop) (by fun_prop) hx))
  have hs : Continuous fun ν : ℂ => sin ((ν+μ)*π/2) := by fun_prop
  have hc : Continuous fun ν : ℂ => cos ((ν+μ)*π/2) := by fun_prop
  simp only [ferrersQ_even_odd]
  exact continuousAt_const.mul ((((hs.continuousAt.neg.mul c1).mul hr2).mul hE.continuousAt).add
    (((hc.continuousAt.mul c2).mul hr1).mul hO.continuousAt))

/-- `d𝖰^μ_ν/dx` is continuous in the degree at a regular parameter. -/
theorem continuousAt_deriv_ferrersQ_degree {ν₀ μ : ℂ} (h : LegendreQRegular ν₀ μ) {x : ℝ}
    (hx : x ∈ Ioo (-1:ℝ) 1) :
    ContinuousAt (fun ν => deriv (ferrersQ ν μ) x) ν₀ := by
  obtain ⟨c1, c2⟩ := continuousAt_Gamma_ferrersQ h
  have hr1 := (continuous_recip_Gamma.comp (by fun_prop : Continuous fun ν : ℂ => (ν-μ+1)/2)).continuousAt (x := ν₀)
  have hr2 := (continuous_recip_Gamma.comp (by fun_prop : Continuous fun ν : ℂ => (ν-μ+2)/2)).continuousAt (x := ν₀)
  have hd : ∀ ν, deriv (ferrersQ ν μ) x = 2^μ*π/2*(-sin ((ν+μ)*π/2)*Gamma ((ν+μ+1)/2)*(Gamma ((ν-μ+2)/2))⁻¹)*
      deriv (ferrersEven ν μ) x + 2^μ*π/2*(cos ((ν+μ)*π/2)*Gamma ((ν+μ+2)/2)*(Gamma ((ν-μ+1)/2))⁻¹)*
      deriv (ferrersOdd ν μ) x := by
    intro ν
    have hev := (ferrersQ_eqOn_even_odd ν μ).eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx)
    rw [hev.deriv_eq]
    exact ((((hasDerivAt_ferrersEven ν μ hx).const_mul _).add
      ((hasDerivAt_ferrersOdd ν μ hx).const_mul _))).deriv.trans
      (by rw [(hasDerivAt_ferrersEven ν μ hx).deriv, (hasDerivAt_ferrersOdd ν μ hx).deriv])
  simp only [hd, (hasDerivAt_ferrersEven _ μ hx).deriv, (hasDerivAt_ferrersOdd _ μ hx).deriv]
  have hF := fun (A B C : ℂ → ℂ) (hA : Differentiable ℂ A) (hB : Differentiable ℂ B) (hC : Differentiable ℂ C) =>
    (continuous_regularizedGaussHG_sq hA hB hC hx).continuousAt (x := ν₀)
  have hs : Continuous fun ν : ℂ => sin ((ν+μ)*π/2) := by fun_prop
  have hc : Continuous fun ν : ℂ => cos ((ν+μ)*π/2) := by fun_prop
  refine (continuousAt_const.mul (((hs.continuousAt.neg.mul c1).mul hr2))).mul ?_ |>.add
    ((continuousAt_const.mul ((hc.continuousAt.mul c2).mul hr1)).mul ?_)
  · exact continuousAt_const.mul ((continuousAt_const.mul (hF _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))).add
      (continuousAt_const.mul ((by fun_prop : Continuous fun ν : ℂ => (-(ν+μ)/2)*((ν-μ+1)/2)).continuousAt.mul
        (hF _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)))))
  · exact (continuousAt_const.mul (hF _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))).add
      (continuousAt_const.mul (continuousAt_const.mul ((continuousAt_const.mul
        (hF _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))).add
      (continuousAt_const.mul ((by fun_prop : Continuous fun ν : ℂ => ((1-ν-μ)/2)*((ν-μ+2)/2)).continuousAt.mul
        (hF _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)))))))

/-- `𝖰^μ_ν` through `𝖯^μ_ν(±x)` (DLMF 14.9.10 with `μ ↦ -μ`), needing only regular `ν+μ`. -/
theorem ferrersQ_reflection {ν μ : ℂ} (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    2/π*sin ((ν+μ)*π)*ferrersQ ν μ x = cos ((ν+μ)*π)*ferrersP ν μ x-ferrersP ν μ (-x) := by
  have pyth := sin_sq_add_cos_sq ((ν+μ)*π/2)
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersQ_even_odd, ferrersP_regular h hx, ferrersP_regular h (ferrers_neg_mem_Ioo hx), ferrersEven_neg,
    ferrersOdd_neg, legendre_sin_two_mul_half, legendre_cos_two_mul_half]
  generalize sin ((ν+μ)*π/2) = sb at pyth
  generalize cos ((ν+μ)*π/2) = cb at pyth
  field_simp
  linear_combination (-(2*cb*Gamma ((ν+μ+1)/2)*ferrersEven ν μ x*(Gamma ((ν-μ+2)/2))⁻¹))*pyth

/-- The reflection formula differentiated in `x`. -/
theorem ferrersQ_reflection_deriv {ν μ : ℂ} (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    2/π*sin ((ν+μ)*π)*deriv (ferrersQ ν μ) x =
      cos ((ν+μ)*π)*deriv (ferrersP ν μ) x+deriv (ferrersP ν μ) (-x) := by
  have hPd : ∀ y ∈ Ioo (-1:ℝ) 1, HasDerivAt (ferrersP ν μ) (deriv (ferrersP ν μ) y) y := fun y hy =>
    (hasDerivAt_ferrers_aux (ν+1) (-ν) (1-μ) (μ/2) hy).differentiableAt.hasDerivAt
  have hev : (fun y => 2/π*sin ((ν+μ)*π)*ferrersQ ν μ y) =ᶠ[𝓝 x]
      (fun y => cos ((ν+μ)*π)*ferrersP ν μ y-ferrersP ν μ (-y)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using ferrersQ_reflection h hy
  have hR : HasDerivAt (fun y => cos ((ν+μ)*π)*ferrersP ν μ y-ferrersP ν μ (-y))
      (cos ((ν+μ)*π)*deriv (ferrersP ν μ) x+deriv (ferrersP ν μ) (-x)) x := by
    have h2 := (hPd (-x) (ferrers_neg_mem_Ioo hx)).scomp x (hasDerivAt_neg x)
    refine (((hPd x hx).const_mul _).sub h2).congr_deriv ?_
    simp
  rw [← deriv_const_mul_field, hev.deriv_eq, hR.deriv]


/-- ferrersQ recurrence 1. -/
@[dlmf 14.10.E1]
theorem ferrersQ_recurrence_1 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν (μ+2) x+2*(μ+1)*x*(1-x^2:ℂ)^(-1/2:ℂ)*ferrersQ ν (μ+1) x+(ν-μ)*(ν+μ+1)*ferrersQ ν μ x=0 := by
  have h1 : LegendreQRegular ν (μ+1) := fun n hn => h (n+1) (by push_cast; linear_combination hn)
  have h2 : LegendreQRegular ν (μ+2) := fun n hn => h (n+2) (by push_cast; linear_combination hn)
  refine eq_zero_of_im_ne_zero (G := fun ν => ferrersQ ν (μ+2) x+2*(μ+1)*x*(1-x^2:ℂ)^(-1/2:ℂ)*
    ferrersQ ν (μ+1) x+(ν-μ)*(ν+μ+1)*ferrersQ ν μ x) (μ := μ) ?_ ?_
  · exact ((continuousAt_ferrersQ_degree h2 hx).add (continuousAt_const.mul
      (continuousAt_ferrersQ_degree h1 hx))).add
      ((by fun_prop : Continuous fun ν : ℂ => (ν-μ)*(ν+μ+1)).continuousAt.mul
        (continuousAt_ferrersQ_degree h hx))
  intro ν hν
  have hs := sin_mul_pi_ne_zero_of_im_ne_zero hν
  have r0 := ferrersQ_reflection (legendreQRegular_of_im_ne_zero hν) hx
  have r1 := ferrersQ_reflection (μ := μ+1) (legendreQRegular_of_im_ne_zero (by simpa [← add_assoc] using hν)) hx
  have r2 := ferrersQ_reflection (μ := μ+2) (legendreQRegular_of_im_ne_zero (by simpa [← add_assoc] using hν)) hx
  rw [show (ν+(μ+1))*π = (ν+μ)*π+π by ring, sin_add_pi, cos_add_pi] at r1
  rw [show (ν+(μ+2))*π = (ν+μ)*π+2*π by ring, sin_add_two_pi, cos_add_two_pi] at r2
  have pa := ferrersP_recurrence_1 ν μ hx
  have pb := ferrersP_recurrence_1 ν μ (ferrers_neg_mem_Ioo hx)
  push_cast at pb
  rw [neg_sq] at pb
  have hk : (2/π*sin ((ν+μ)*π)) ≠ 0 := mul_ne_zero (div_ne_zero two_ne_zero
    (ofReal_ne_zero.mpr Real.pi_ne_zero)) hs
  refine (mul_eq_zero.mp (?_ : (2/π*sin ((ν+μ)*π))*_ = 0)).resolve_left hk
  linear_combination r2 - 2*(μ+1)*x*(1-x^2:ℂ)^(-1/2:ℂ)*r1 + (ν-μ)*(ν+μ+1)*r0 +
    cos ((ν+μ)*π)*pa - pb

/-- ferrersQ recurrence 2. -/
@[dlmf 14.10.E2]
theorem ferrersQ_recurrence_2 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)^(1/2:ℂ)*ferrersQ ν (μ+1) x-(ν-μ+1)*ferrersQ (ν+1) μ x+(ν+μ+1)*x*ferrersQ ν μ x=0 := by
  have h1 : LegendreQRegular ν (μ+1) := fun n hn => h (n+1) (by push_cast; linear_combination hn)
  have h1' : LegendreQRegular (ν+1) μ := fun n hn => h (n+1) (by push_cast; linear_combination hn)
  refine eq_zero_of_im_ne_zero (G := fun ν => (1-x^2:ℂ)^(1/2:ℂ)*ferrersQ ν (μ+1) x-(ν-μ+1)*ferrersQ (ν+1) μ x+
    (ν+μ+1)*x*ferrersQ ν μ x) (μ := μ) ?_ ?_
  · have c1 : ContinuousAt (fun ν => ferrersQ (ν+1) μ x) ν :=
      (continuousAt_ferrersQ_degree h1' hx).comp (f := fun ν => ν+1) (by fun_prop)
    exact ((continuousAt_const.mul (continuousAt_ferrersQ_degree h1 hx)).sub
      ((by fun_prop : Continuous fun ν : ℂ => ν-μ+1).continuousAt.mul c1)).add
      ((by fun_prop : Continuous fun ν : ℂ => (ν+μ+1)*x).continuousAt.mul (continuousAt_ferrersQ_degree h hx))
  intro ν hν
  have hs := sin_mul_pi_ne_zero_of_im_ne_zero hν
  have r0 := ferrersQ_reflection (legendreQRegular_of_im_ne_zero hν) hx
  have ra := ferrersQ_reflection (μ := μ+1) (legendreQRegular_of_im_ne_zero (by simpa [← add_assoc] using hν)) hx
  have rb := ferrersQ_reflection (ν := ν+1) (legendreQRegular_of_im_ne_zero (by simpa [add_right_comm] using hν)) hx
  rw [show (ν+(μ+1))*π = (ν+μ)*π+π by ring, sin_add_pi, cos_add_pi] at ra
  rw [show (ν+1+μ)*π = (ν+μ)*π+π by ring, sin_add_pi, cos_add_pi] at rb
  have pa := ferrersP_recurrence_2 ν μ hx
  have pb := ferrersP_recurrence_2 ν μ (ferrers_neg_mem_Ioo hx)
  push_cast at pb
  rw [neg_sq] at pb
  have hk : (2/π*sin ((ν+μ)*π)) ≠ 0 := mul_ne_zero (div_ne_zero two_ne_zero
    (ofReal_ne_zero.mpr Real.pi_ne_zero)) hs
  refine (mul_eq_zero.mp (?_ : (2/π*sin ((ν+μ)*π))*_ = 0)).resolve_left hk
  linear_combination -(1-x^2:ℂ)^(1/2:ℂ)*ra + (ν-μ+1)*rb + (ν+μ+1)*x*r0 + cos ((ν+μ)*π)*pa + pb

/-- ferrersQ recurrence 3. -/
@[dlmf 14.10.E3]
theorem ferrersQ_recurrence_3 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (ν-μ+2)*ferrersQ (ν+2) μ x-(2*ν+3)*x*ferrersQ (ν+1) μ x+(ν+μ+1)*ferrersQ ν μ x=0 := by
  have h1 : LegendreQRegular (ν+1) μ := fun n hn => h (n+1) (by push_cast; linear_combination hn)
  have h2 : LegendreQRegular (ν+2) μ := fun n hn => h (n+2) (by push_cast; linear_combination hn)
  refine eq_zero_of_im_ne_zero (G := fun ν => (ν-μ+2)*ferrersQ (ν+2) μ x-(2*ν+3)*x*ferrersQ (ν+1) μ x+
    (ν+μ+1)*ferrersQ ν μ x) (μ := μ) ?_ ?_
  · have c2 : ContinuousAt (fun ν => ferrersQ (ν+2) μ x) ν :=
      (continuousAt_ferrersQ_degree h2 hx).comp (f := fun ν => ν+2) (by fun_prop)
    have c1 : ContinuousAt (fun ν => ferrersQ (ν+1) μ x) ν :=
      (continuousAt_ferrersQ_degree h1 hx).comp (f := fun ν => ν+1) (by fun_prop)
    exact (((by fun_prop : Continuous fun ν : ℂ => ν-μ+2).continuousAt.mul c2).sub
      ((by fun_prop : Continuous fun ν : ℂ => (2*ν+3)*x).continuousAt.mul c1)).add
      ((by fun_prop : Continuous fun ν : ℂ => ν+μ+1).continuousAt.mul (continuousAt_ferrersQ_degree h hx))
  intro ν hν
  have hs := sin_mul_pi_ne_zero_of_im_ne_zero hν
  have r0 := ferrersQ_reflection (legendreQRegular_of_im_ne_zero hν) hx
  have r1 := ferrersQ_reflection (ν := ν+1) (legendreQRegular_of_im_ne_zero (by simpa [add_right_comm] using hν)) hx
  have r2 := ferrersQ_reflection (ν := ν+2) (legendreQRegular_of_im_ne_zero (by simpa [add_right_comm] using hν)) hx
  rw [show (ν+1+μ)*π = (ν+μ)*π+π by ring, sin_add_pi, cos_add_pi] at r1
  rw [show (ν+2+μ)*π = (ν+μ)*π+2*π by ring, sin_add_two_pi, cos_add_two_pi] at r2
  have pa := ferrersP_recurrence_3 ν μ hx
  have pb := ferrersP_recurrence_3 ν μ (ferrers_neg_mem_Ioo hx)
  push_cast at pb
  have hk : (2/π*sin ((ν+μ)*π)) ≠ 0 := mul_ne_zero (div_ne_zero two_ne_zero
    (ofReal_ne_zero.mpr Real.pi_ne_zero)) hs
  refine (mul_eq_zero.mp (?_ : (2/π*sin ((ν+μ)*π))*_ = 0)).resolve_left hk
  linear_combination (ν-μ+2)*r2 + (2*ν+3)*x*r1 + (ν+μ+1)*r0 + cos ((ν+μ)*π)*pa - pb

/-- ferrersQ recurrence 4. -/
@[dlmf 14.10.E4]
theorem ferrersQ_recurrence_4 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)*deriv (ferrersQ ν μ) x=(μ-ν-1)*ferrersQ (ν+1) μ x+(ν+1)*x*ferrersQ ν μ x := by
  have h1' : LegendreQRegular (ν+1) μ := fun n hn => h (n+1) (by push_cast; linear_combination hn)
  rw [← sub_eq_zero]
  refine eq_zero_of_im_ne_zero (G := fun ν => (1-x^2:ℂ)*deriv (ferrersQ ν μ) x-((μ-ν-1)*ferrersQ (ν+1) μ x+
    (ν+1)*x*ferrersQ ν μ x)) (μ := μ) ?_ ?_
  · have c1 : ContinuousAt (fun ν => ferrersQ (ν+1) μ x) ν :=
      (continuousAt_ferrersQ_degree h1' hx).comp (f := fun ν => ν+1) (by fun_prop)
    exact (continuousAt_const.mul (continuousAt_deriv_ferrersQ_degree h hx)).sub
      (((by fun_prop : Continuous fun ν : ℂ => μ-ν-1).continuousAt.mul c1).add
      ((by fun_prop : Continuous fun ν : ℂ => (ν+1)*x).continuousAt.mul (continuousAt_ferrersQ_degree h hx)))
  intro ν hν
  have hs := sin_mul_pi_ne_zero_of_im_ne_zero hν
  have hr := legendreQRegular_of_im_ne_zero hν
  have r0 := ferrersQ_reflection hr hx
  have rd := ferrersQ_reflection_deriv hr hx
  have r1 := ferrersQ_reflection (ν := ν+1) (legendreQRegular_of_im_ne_zero (by simpa [add_right_comm] using hν)) hx
  rw [show (ν+1+μ)*π = (ν+μ)*π+π by ring, sin_add_pi, cos_add_pi] at r1
  have pa := ferrersP_recurrence_4 ν μ hx
  have pb := ferrersP_recurrence_4 ν μ (ferrers_neg_mem_Ioo hx)
  push_cast at pb
  rw [neg_sq] at pb
  have hk : (2/π*sin ((ν+μ)*π)) ≠ 0 := mul_ne_zero (div_ne_zero two_ne_zero
    (ofReal_ne_zero.mpr Real.pi_ne_zero)) hs
  refine (mul_eq_zero.mp (?_ : (2/π*sin ((ν+μ)*π))*_ = 0)).resolve_left hk
  linear_combination (1-x^2:ℂ)*rd + (μ-ν-1)*r1 - (ν+1)*x*r0 + cos ((ν+μ)*π)*pa + pb

/-- ferrersQ recurrence 5. -/
@[dlmf 14.10.E5]
theorem ferrersQ_recurrence_5 (ν μ : ℂ) (h : LegendreQRegular (ν-1) μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)*deriv (ferrersQ ν μ) x=(ν+μ)*ferrersQ (ν-1) μ x-ν*x*ferrersQ ν μ x := by
  have h0 : LegendreQRegular ν μ := fun n hn => h (n+1) (by push_cast; linear_combination hn)
  rw [← sub_eq_zero]
  refine eq_zero_of_im_ne_zero (G := fun ν => (1-x^2:ℂ)*deriv (ferrersQ ν μ) x-((ν+μ)*ferrersQ (ν-1) μ x-
    ν*x*ferrersQ ν μ x)) (μ := μ) ?_ ?_
  · have c1 : ContinuousAt (fun ν => ferrersQ (ν-1) μ x) ν :=
      (continuousAt_ferrersQ_degree h hx).comp (f := fun ν => ν-1) (by fun_prop)
    exact (continuousAt_const.mul (continuousAt_deriv_ferrersQ_degree h0 hx)).sub
      (((by fun_prop : Continuous fun ν : ℂ => ν+μ).continuousAt.mul c1).sub
      ((by fun_prop : Continuous fun ν : ℂ => ν*x).continuousAt.mul (continuousAt_ferrersQ_degree h0 hx)))
  intro ν hν
  have hs := sin_mul_pi_ne_zero_of_im_ne_zero hν
  have hr := legendreQRegular_of_im_ne_zero hν
  have r0 := ferrersQ_reflection hr hx
  have rd := ferrersQ_reflection_deriv hr hx
  have r1 := ferrersQ_reflection (ν := ν-1) (legendreQRegular_of_im_ne_zero (by simpa [sub_add_eq_add_sub] using hν)) hx
  rw [show (ν-1+μ)*π = (ν+μ)*π-π by ring, sin_sub_pi, cos_sub_pi] at r1
  have pa := ferrersP_recurrence_5 ν μ hx
  have pb := ferrersP_recurrence_5 ν μ (ferrers_neg_mem_Ioo hx)
  push_cast at pb
  rw [neg_sq] at pb
  have hk : (2/π*sin ((ν+μ)*π)) ≠ 0 := mul_ne_zero (div_ne_zero two_ne_zero
    (ofReal_ne_zero.mpr Real.pi_ne_zero)) hs
  refine (mul_eq_zero.mp (?_ : (2/π*sin ((ν+μ)*π))*_ = 0)).resolve_left hk
  linear_combination (1-x^2:ℂ)*rd + (ν+μ)*r1 + ν*x*r0 + cos ((ν+μ)*π)*pa + pb

/-- The Casoratian identity away from the exceptional value `μ = ν+1`. -/
theorem ferrers_wronskian_5_generic (ν μ : ℂ) (h : LegendreQRegular ν μ) (hd : ν-μ+1 ≠ 0) {x : ℝ}
    (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP (ν+1) μ x*ferrersQ ν μ x-ferrersP ν μ x*ferrersQ (ν+1) μ x=Gamma (ν+μ+1)/Gamma (ν-μ+2) := by
  have hP := ferrersP_recurrence_4 ν μ hx
  have hQ := ferrersQ_recurrence_4 ν μ h hx
  have hW := ferrers_wronskian_4 ν μ h hx
  have hne := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  unfold ferrersWronskian at hW
  rw [show ν-μ+2 = (ν-μ+1)+1 by ring, Gamma_add_one _ hd]
  have key : (ν-μ+1)*(ferrersP (ν+1) μ x*ferrersQ ν μ x-ferrersP ν μ x*ferrersQ (ν+1) μ x) =
      Gamma (ν+μ+1)/Gamma (ν-μ+1) := by
    have : (1-(x:ℂ)^2)*(Gamma (ν+μ+1)/(Gamma (ν-μ+1)*(1-(x:ℂ)^2))) = Gamma (ν+μ+1)/Gamma (ν-μ+1) := by
      field_simp
    rw [← this, ← hW]
    linear_combination ferrersQ ν μ x*hP - ferrersP ν μ x*hQ
  rw [show Gamma (ν+μ+1)/((ν-μ+1)*Gamma (ν-μ+1)) = (Gamma (ν+μ+1)/Gamma (ν-μ+1))/(ν-μ+1) by
    rw [div_div, mul_comm], ← key]
  field_simp

/-- ferrers wronskian 5. -/
@[dlmf 14.2.E5]
theorem ferrers_wronskian_5 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP (ν+1) μ x*ferrersQ ν μ x-ferrersP ν μ x*ferrersQ (ν+1) μ x=Gamma (ν+μ+1)/Gamma (ν-μ+2) := by
  by_cases hd : ν-μ+1 = 0
  swap
  · exact ferrers_wronskian_5_generic ν μ h hd hx
  have ht : ((1:ℂ)-x)/2 ∈ cutPlane := by
    rw [mem_cutPlane, show (1:ℂ) - (1-(x:ℂ))/2 = (((1+x)/2 : ℝ) : ℂ) by push_cast; ring]
    exact Or.inl (by simp only [ofReal_re]; linarith [hx.1])
  have hPc : Continuous fun v : ℂ => ferrersP v μ x := by
    unfold ferrersP
    exact continuous_const.mul (differentiable_regularizedGaussHG_comp (A := fun v => v+1) (B := fun v => -v)
      (C := fun _ => 1-μ) (by fun_prop) (by fun_prop) (by fun_prop) ht).continuous
  have h1 : LegendreQRegular (ν+1) μ := fun n hn => h (n+1) (by push_cast; linear_combination hn)
  have hQ0 := continuousAt_ferrersQ_degree h hx
  have hQ1 : ContinuousAt (fun v : ℂ => ferrersQ (v+1) μ x) ν :=
    ContinuousAt.comp (g := fun v => ferrersQ v μ x) (continuousAt_ferrersQ_degree h1 hx) (by fun_prop)
  have hG1 : ContinuousAt (fun v : ℂ => Gamma (v+μ+1)) ν :=
    ContinuousAt.comp (g := Gamma) (differentiableAt_Gamma _ (fun k hk => h k (by linear_combination hk))).continuousAt
      (by fun_prop)
  have hG2 : ContinuousAt (fun v : ℂ => (Gamma (v-μ+2))⁻¹) ν :=
    (continuous_recip_Gamma.comp (by fun_prop : Continuous fun v : ℂ => v-μ+2)).continuousAt
  set G : ℂ → ℂ := fun v => ferrersP (v+1) μ x*ferrersQ v μ x-ferrersP v μ x*ferrersQ (v+1) μ x
    - Gamma (v+μ+1)*(Gamma (v-μ+2))⁻¹
  have hGc : ContinuousAt G ν :=
    ((((hPc.comp (by fun_prop : Continuous fun v : ℂ => v+1)).continuousAt.mul hQ0).sub
      (hPc.continuousAt.mul hQ1)).sub (hG1.mul hG2))
  have hev : G =ᶠ[𝓝[≠] ν] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin, eventually_affine_ne_neg_nat one_ne_zero (μ+1) ν] with v hv hr
    have hreg : LegendreQRegular v μ := fun n hn => hr n (by linear_combination hn)
    have hdv : v-μ+1 ≠ 0 := by
      intro h0; apply hv; show v = ν; linear_combination h0 - hd
    simp only [G]
    rw [ferrers_wronskian_5_generic v μ hreg hdv hx, div_eq_mul_inv, sub_self]
  have h0 : G ν = 0 := tendsto_nhds_unique (hGc.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' hev.symm)
  simp only [G] at h0
  rw [div_eq_mul_inv]
  linear_combination h0

/-- associatedP recurrence 6. -/
@[dlmf 14.10.E6]
theorem associatedP_recurrence_6 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (μ+2) z+2*(μ+1)*z*legendreBranchPower (-1) z*associatedP ν (μ+1) z-(ν-μ)*(ν+μ+1)*associatedP ν μ z=0 := by
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have hg := associated_gauge_shifts μ hz
  have he := regularizedGaussHG_legendre_orders ν (1-μ) hw
  dsimp only at hg
  simp only [associatedP]
  rw [show (1:ℂ)-(μ+1)=1-μ-1 by ring,show (1:ℂ)-(μ+2)=1-μ-2 by ring]
  have hm := slitPlane_ne_zero hz
  rw [hg.1]
  linear_combination (norm := (field_simp [hm]; ring))
    ((exp (μ/2*(log (z+1)-log (z-1))))/(z-1))*he+
    2*(μ+1)*z*regularizedGaussHG (ν+1) (-ν) (1-μ-1) ((1-z)/2)*hg.2.1

/-- associatedP recurrence 7. -/
@[dlmf 14.10.E7]
theorem associatedP_recurrence_7 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    legendreBranchPower 1 z*associatedP ν (μ+1) z-(ν-μ+1)*associatedP (ν+1) μ z+(ν+μ+1)*z*associatedP ν μ z=0 := by
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have hg := associated_gauge_shifts μ hz
  have he := regularizedGaussHG_legendre_order ν (1-μ) hw
  dsimp only at hg
  simp only [associatedP]
  rw [show (1:ℂ)-(μ+1)=1-μ-1 by ring,
    show ν+1+1=ν+2 by ring,show -(ν+1)= -ν-1 by ring]
  linear_combination (exp (μ/2*(log (z+1)-log (z-1))))*he+
    regularizedGaussHG (ν+1) (-ν) (1-μ-1) ((1-z)/2)*hg.2.2

/-- associatedP recurrence 3. -/
@[dlmf 14.10.E3]
theorem associatedP_recurrence_3 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (ν-μ+2)*associatedP (ν+2) μ z-(2*ν+3)*z*associatedP (ν+1) μ z+(ν+μ+1)*associatedP ν μ z=0 := by
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have he := regularizedGaussHG_legendre_degree (ν+1) (1-μ) hw
  simp only [associatedP]
  rw [regularizedGaussHG_symm (ν+2+1) (-(ν+2)) (1-μ) hw,
    regularizedGaussHG_symm (ν+1+1) (-(ν+1)) (1-μ) hw,
    regularizedGaussHG_symm (ν+1) (-ν) (1-μ) hw]
  rw [show -(ν+2)= -(ν+1)-1 by ring,show ν+2+1=(ν+1)+2 by ring,
    show -ν= -(ν+1)+1 by ring,show ν+1+1=ν+2 by ring] at *
  linear_combination (exp (μ/2*(log (z+1)-log (z-1))))*he

/-- associatedP recurrence 5. -/
@[dlmf 14.10.E5]
theorem associatedP_recurrence_5 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2:ℂ)*deriv (associatedP ν μ) z=(ν+μ)*associatedP (ν-1) μ z-ν*z*associatedP ν μ z := by
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have hd : HasDerivAt (associatedP ν μ) _ z :=
    hasDerivAt_associatedP_aux (ν+1) (-ν) (1-μ) μ hz
  rw [hd.deriv]
  have he := regularizedGaussHG_legendre_derivative ν (1-μ) hw
  have hm := slitPlane_ne_zero hz
  have hp := slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hz)
  have hn : 1-z^2≠0 := by
    intro h; apply mul_ne_zero hm hp; linear_combination -h
  simp only [associatedP]
  rw [regularizedGaussHG_symm (ν+1) (-ν) (1-μ) hw,
    regularizedGaussHG_symm (ν-1+1) (-(ν-1)) (1-μ) hw,
    regularizedGaussHG_symm (ν+1+1) (-ν+1) (1-μ+1) hw]
  rw [show -(ν-1)= -ν+1 by ring,show ν-1+1=ν by ring]
  rw [show ν+1+1=ν+2 by ring] at *
  generalize exp (μ/2*(log (z+1)-log (z-1)))=A
  field_simp [hn]
  linear_combination (2*A)*he
/-- associatedP recurrence 4. -/
@[dlmf 14.10.E4]
theorem associatedP_recurrence_4 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2:ℂ)*deriv (associatedP ν μ) z=(μ-ν-1)*associatedP (ν+1) μ z+(ν+1)*z*associatedP ν μ z := by
  have hd := associatedP_recurrence_5 ν μ hz
  have hr := associatedP_recurrence_3 (ν-1) μ hz
  rw [show ν-1+2=ν+1 by ring,show ν-1+1=ν by ring] at hr
  linear_combination hd+hr


/-- `1/Γ(s) = s/Γ(s+1)`, also at the poles of `Γ`. -/
theorem legendre_recip_Gamma_succ (s : ℂ) : (Gamma s)⁻¹ = s*(Gamma (s+1))⁻¹ := by
  by_cases h : s = 0
  · simp [h, Complex.Gamma_zero]
  · rw [Complex.Gamma_add_one s h, mul_inv, ← mul_assoc, mul_inv_cancel₀ h, one_mul]

theorem olverQ_eq_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ ν μ z = π/(2*sin (μ*π))*(associatedP ν μ z*(Gamma (ν+μ+1))⁻¹-
      associatedP ν (-μ) z*(Gamma (ν-μ+1))⁻¹) :=
  (olverQ_eventuallyEq_nonint ν μ hμ hz).eq_of_nhds

theorem legendre_nonint_add_one {μ : ℂ} (hμ : ∀ n : ℤ, μ ≠ n) : ∀ n : ℤ, μ+1 ≠ n :=
  fun n hn => hμ (n-1) (by push_cast; linear_combination hn)

theorem legendre_sin_add_one_mul_pi (μ : ℂ) : sin ((μ+1)*π) = -sin (μ*π) := by
  rw [show (μ+1)*(π:ℂ) = μ*π+π by ring, sin_add_pi]

theorem legendre_exp_add_one_mul_pi_I (μ : ℂ) : exp ((μ+1)*π*I) = -exp (μ*π*I) := by
  rw [show (μ+1)*(π:ℂ)*I = μ*π*I+π*I by ring, exp_add, exp_pi_mul_I]; ring

theorem legendreBranchPower_one_mul_neg_one (z : ℂ) :
    legendreBranchPower 1 z*legendreBranchPower (-1) z = 1 := by
  unfold legendreBranchPower
  rw [← exp_add]
  convert exp_zero using 2
  ring

/-- Degree recurrence for `𝑸^μ_ν`, non-integer order. -/
theorem olverQ_recurrence_3_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (ν+μ+2)*(ν-μ+2)*olverQ (ν+2) μ z-(2*ν+3)*z*olverQ (ν+1) μ z+olverQ ν μ z=0 := by
  have R1 := associatedP_recurrence_3 ν μ hz
  have R2 := associatedP_recurrence_3 ν (-μ) hz
  rw [olverQ_eq_nonint (ν+2) μ hμ hz, olverQ_eq_nonint (ν+1) μ hμ hz, olverQ_eq_nonint ν μ hμ hz]
  rw [show ν+2+μ+1 = ν+μ+3 by ring, show ν+1+μ+1 = ν+μ+2 by ring, show ν+2-μ+1 = ν-μ+3 by ring,
    show ν+1-μ+1 = ν-μ+2 by ring]
  rw [legendre_recip_Gamma_succ (ν+μ+1), show ν+μ+1+1 = ν+μ+2 by ring, legendre_recip_Gamma_succ (ν+μ+2),
    show ν+μ+2+1 = ν+μ+3 by ring, legendre_recip_Gamma_succ (ν-μ+1), show ν-μ+1+1 = ν-μ+2 by ring,
    legendre_recip_Gamma_succ (ν-μ+2), show ν-μ+2+1 = ν-μ+3 by ring]
  generalize (Gamma (ν+μ+3))⁻¹ = a0
  generalize (Gamma (ν-μ+3))⁻¹ = b0
  linear_combination (π/(2*sin (μ*π))*a0*(ν+μ+2))*R1 - (π/(2*sin (μ*π))*b0*(ν-μ+2))*R2

theorem olverQ_recurrence_3 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (ν+μ+2)*(ν-μ+2)*olverQ (ν+2) μ z-(2*ν+3)*z*olverQ (ν+1) μ z+olverQ ν μ z=0 := by
  have h0 := (olverQ_entire_order ν z hz).continuous
  have h1 := (olverQ_entire_order (ν+1) z hz).continuous
  have h2 := (olverQ_entire_order (ν+2) z hz).continuous
  exact legendre_eq_of_continuous_nonint (g := fun _ => 0) (by fun_prop) continuous_const
    (fun μ hμ => olverQ_recurrence_3_nonint ν μ hμ hz) μ

/-- associatedQ recurrence 3. -/
@[dlmf 14.10.E3]
theorem associatedQ_recurrence_3 (ν μ : ℂ) (h : LegendreQRegular ν μ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (ν-μ+2)*associatedQ (ν+2) μ z-(2*ν+3)*z*associatedQ (ν+1) μ z+(ν+μ+1)*associatedQ ν μ z=0 := by
  have R := olverQ_recurrence_3 ν μ hz
  have h1 : ν+μ+1 ≠ 0 := fun he => h 0 (by push_cast; linear_combination he)
  have h2 : ν+μ+1+1 ≠ 0 := fun he => h 1 (by push_cast; linear_combination he)
  have e1 : Gamma (ν+1+μ+1) = (ν+μ+1)*Gamma (ν+μ+1) := by
    rw [show ν+1+μ+1 = (ν+μ+1)+1 by ring, Gamma_add_one _ h1]
  have e2 : Gamma (ν+2+μ+1) = (ν+μ+2)*(ν+μ+1)*Gamma (ν+μ+1) := by
    rw [show ν+2+μ+1 = (ν+μ+1+1)+1 by ring, Gamma_add_one _ h2, Gamma_add_one _ h1]; ring
  simp only [associatedQ]
  rw [e1, e2]
  linear_combination (exp (μ*π*I)*Gamma (ν+μ+1)*(ν+μ+1))*R

/-- Order recurrence for `𝑸^μ_ν`, non-integer order. -/
theorem olverQ_recurrence_6_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (ν+μ+2)*olverQ ν (μ+2) z-2*(μ+1)*z*legendreBranchPower (-1) z*olverQ ν (μ+1) z-(ν-μ)*olverQ ν μ z=0 := by
  have hμ1 := legendre_nonint_add_one hμ
  have hμ2 : ∀ n : ℤ, μ+2 ≠ n := fun n hn => hμ (n-2) (by push_cast; linear_combination hn)
  have R1 := associatedP_recurrence_6 ν μ hz
  have R2 := associatedP_recurrence_6 ν (-μ-2) hz
  rw [show -μ-2+2 = -μ by ring, show -μ-2+1 = -(μ+1) by ring, show -μ-2 = -(μ+2) by ring] at R2
  rw [olverQ_eq_nonint ν (μ+2) hμ2 hz, olverQ_eq_nonint ν (μ+1) hμ1 hz, olverQ_eq_nonint ν μ hμ hz]
  rw [show (μ+2)*(π:ℂ) = μ*π+2*π by ring, sin_add_two_pi, legendre_sin_add_one_mul_pi]
  rw [show ν+(μ+2)+1 = ν+μ+3 by ring, show ν+(μ+1)+1 = ν+μ+2 by ring,
    legendre_recip_Gamma_succ (ν+μ+1), show ν+μ+1+1 = ν+μ+2 by ring, legendre_recip_Gamma_succ (ν+μ+2),
    show ν+μ+2+1 = ν+μ+3 by ring]
  rw [show ν-(μ+2)+1 = ν-μ-1 by ring, legendre_recip_Gamma_succ (ν-μ-1), show ν-μ-1+1 = ν-μ by ring,
    show ν-(μ+1)+1 = ν-μ by ring, legendre_recip_Gamma_succ (ν-μ)]
  generalize (Gamma (ν+μ+3))⁻¹ = a0
  generalize (Gamma (ν-μ+1))⁻¹ = b0
  linear_combination (π/(2*sin (μ*π))*a0*(ν+μ+2))*R1 + (π/(2*sin (μ*π))*b0*(ν-μ))*R2

theorem olverQ_recurrence_6 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (ν+μ+2)*olverQ ν (μ+2) z-2*(μ+1)*z*legendreBranchPower (-1) z*olverQ ν (μ+1) z-(ν-μ)*olverQ ν μ z=0 := by
  have h0 := (olverQ_entire_order ν z hz).continuous
  have h1 : Continuous fun μ => olverQ ν (μ+1) z := h0.comp (by fun_prop : Continuous fun μ : ℂ => μ+1)
  have h2 : Continuous fun μ => olverQ ν (μ+2) z := h0.comp (by fun_prop : Continuous fun μ : ℂ => μ+2)
  exact legendre_eq_of_continuous_nonint (g := fun _ => 0) (by fun_prop) continuous_const
    (fun μ hμ => olverQ_recurrence_6_nonint ν μ hμ hz) μ

/-- associatedQ recurrence 6. -/
@[dlmf 14.10.E6]
theorem associatedQ_recurrence_6 (ν μ : ℂ) (h : LegendreQRegular ν μ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedQ ν (μ+2) z+2*(μ+1)*z*legendreBranchPower (-1) z*associatedQ ν (μ+1) z-(ν-μ)*(ν+μ+1)*associatedQ ν μ z=0 := by
  have R := olverQ_recurrence_6 ν μ hz
  have h1 : ν+μ+1 ≠ 0 := fun he => h 0 (by push_cast; linear_combination he)
  have h2 : ν+μ+1+1 ≠ 0 := fun he => h 1 (by push_cast; linear_combination he)
  have e1 : Gamma (ν+(μ+1)+1) = (ν+μ+1)*Gamma (ν+μ+1) := by
    rw [show ν+(μ+1)+1 = (ν+μ+1)+1 by ring, Gamma_add_one _ h1]
  have e2 : Gamma (ν+(μ+2)+1) = (ν+μ+2)*(ν+μ+1)*Gamma (ν+μ+1) := by
    rw [show ν+(μ+2)+1 = (ν+μ+1+1)+1 by ring, Gamma_add_one _ h2, Gamma_add_one _ h1]; ring
  have x2 : exp ((μ+2)*π*I) = exp (μ*π*I) := by
    rw [show (μ+2)*(π:ℂ)*I = μ*π*I+2*π*I by ring, exp_add, exp_two_pi_mul_I, mul_one]
  simp only [associatedQ]
  rw [e1, e2, x2, legendre_exp_add_one_mul_pi_I]
  linear_combination (exp (μ*π*I)*Gamma (ν+μ+1)*(ν+μ+1))*R

/-- A mixed recurrence for `P^μ_ν`: `P^{μ+1}_{ν+1} - z P^{μ+1}_ν = (ν+μ+1)(z²-1)^{1/2} P^μ_ν`. -/
theorem associatedP_mixed_recurrence (ν l : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP (ν+1) (l+1) z-z*associatedP ν (l+1) z-(ν+l+1)*legendreBranchPower 1 z*associatedP ν l z=0 := by
  have hc0 := (associatedP_entire_order ν z hz).continuous
  have hc1 := (associatedP_entire_order (ν+1) z hz).continuous
  have hd0 : Continuous fun l => associatedP ν (l+1) z := hc0.comp (by fun_prop : Continuous fun μ : ℂ => μ+1)
  have hd1 : Continuous fun l => associatedP (ν+1) (l+1) z := hc1.comp (by fun_prop : Continuous fun μ : ℂ => μ+1)
  refine legendre_eq_of_continuous_off_countable (f := fun l => associatedP (ν+1) (l+1) z-z*associatedP ν (l+1) z-(ν+l+1)*legendreBranchPower 1 z*associatedP ν l z) (g := fun _ => 0) (by fun_prop) continuous_const
    (countable_singleton ν) (fun l hl => ?_) l
  have hne : ν-l ≠ 0 := sub_ne_zero.mpr (fun h => hl (by simp [h]))
  have R6 := associatedP_recurrence_6 ν l hz
  have R7 := associatedP_recurrence_7 ν (l+1) hz
  rw [show l+1+1 = l+2 by ring] at R7
  have hBB := legendreBranchPower_one_mul_neg_one z
  have : (ν-l)*(associatedP (ν+1) (l+1) z-z*associatedP ν (l+1) z-
      (ν+l+1)*legendreBranchPower 1 z*associatedP ν l z) = 0 := by
    linear_combination legendreBranchPower 1 z*R6 - R7 - (2*(l+1)*z*associatedP ν (l+1) z)*hBB
  exact (mul_eq_zero.mp this).resolve_left hne

/-- Mixed recurrence for `𝑸^μ_ν`, non-integer order. -/
theorem olverQ_recurrence_7_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    -legendreBranchPower 1 z*olverQ ν (μ+1) z-(ν-μ+1)*olverQ (ν+1) μ z+z*olverQ ν μ z=0 := by
  have hμ1 := legendre_nonint_add_one hμ
  have R1 := associatedP_recurrence_7 ν μ hz
  have R2 := associatedP_mixed_recurrence ν (-μ-1) hz
  rw [show -μ-1+1 = -μ by ring, show -μ-1 = -(μ+1) by ring] at R2
  rw [olverQ_eq_nonint ν (μ+1) hμ1 hz, olverQ_eq_nonint (ν+1) μ hμ hz, olverQ_eq_nonint ν μ hμ hz]
  rw [legendre_sin_add_one_mul_pi]
  rw [show ν+(μ+1)+1 = ν+μ+2 by ring, show ν+1+μ+1 = ν+μ+2 by ring,
    legendre_recip_Gamma_succ (ν+μ+1), show ν+μ+1+1 = ν+μ+2 by ring]
  rw [show ν-(μ+1)+1 = ν-μ by ring, show ν+1-μ+1 = ν-μ+2 by ring, legendre_recip_Gamma_succ (ν-μ),
    legendre_recip_Gamma_succ (ν-μ+1), show ν-μ+1+1 = ν-μ+2 by ring]
  generalize (Gamma (ν+μ+2))⁻¹ = a0
  generalize (Gamma (ν-μ+2))⁻¹ = b0
  linear_combination (π/(2*sin (μ*π))*a0)*R1 + (π/(2*sin (μ*π))*b0*(ν-μ+1))*R2

theorem olverQ_recurrence_7 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    -legendreBranchPower 1 z*olverQ ν (μ+1) z-(ν-μ+1)*olverQ (ν+1) μ z+z*olverQ ν μ z=0 := by
  have h0 := (olverQ_entire_order ν z hz).continuous
  have h1 : Continuous fun μ => olverQ ν (μ+1) z := h0.comp (by fun_prop : Continuous fun μ : ℂ => μ+1)
  have h2 := (olverQ_entire_order (ν+1) z hz).continuous
  exact legendre_eq_of_continuous_nonint (g := fun _ => 0) (by fun_prop) continuous_const
    (fun μ hμ => olverQ_recurrence_7_nonint ν μ hμ hz) μ

/-- associatedQ recurrence 7. -/
@[dlmf 14.10.E7]
theorem associatedQ_recurrence_7 (ν μ : ℂ) (h : LegendreQRegular ν μ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    legendreBranchPower 1 z*associatedQ ν (μ+1) z-(ν-μ+1)*associatedQ (ν+1) μ z+(ν+μ+1)*z*associatedQ ν μ z=0 := by
  have R := olverQ_recurrence_7 ν μ hz
  have h1 : ν+μ+1 ≠ 0 := fun he => h 0 (by push_cast; linear_combination he)
  have e1 : Gamma (ν+(μ+1)+1) = (ν+μ+1)*Gamma (ν+μ+1) := by
    rw [show ν+(μ+1)+1 = (ν+μ+1)+1 by ring, Gamma_add_one _ h1]
  have e1' : Gamma (ν+1+μ+1) = (ν+μ+1)*Gamma (ν+μ+1) := by
    rw [show ν+1+μ+1 = (ν+μ+1)+1 by ring, Gamma_add_one _ h1]
  simp only [associatedQ]
  rw [e1, e1', legendre_exp_add_one_mul_pi_I]
  linear_combination (exp (μ*π*I)*Gamma (ν+μ+1)*(ν+μ+1))*R

theorem deriv_associatedQ (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    deriv (associatedQ ν μ) z = exp (μ*π*I)*Gamma (ν+μ+1)*deriv (olverQ ν μ) z :=
  deriv_const_mul _ (olverQ_analytic ν μ z hz).differentiableAt

theorem olverQ_recurrence_4_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2)*deriv (olverQ ν μ) z=(μ-ν-1)*(ν+μ+1)*olverQ (ν+1) μ z+(ν+1)*z*olverQ ν μ z := by
  have R1 := associatedP_recurrence_4 ν μ hz
  have R2 := associatedP_recurrence_4 ν (-μ) hz
  rw [deriv_olverQ_nonint ν μ hμ hz, olverQ_eq_nonint (ν+1) μ hμ hz, olverQ_eq_nonint ν μ hμ hz]
  rw [show ν+1+μ+1 = ν+μ+2 by ring, show ν+1-μ+1 = ν-μ+2 by ring,
    legendre_recip_Gamma_succ (ν+μ+1), show ν+μ+1+1 = ν+μ+2 by ring,
    legendre_recip_Gamma_succ (ν-μ+1), show ν-μ+1+1 = ν-μ+2 by ring]
  generalize (Gamma (ν+μ+2))⁻¹ = a0
  generalize (Gamma (ν-μ+2))⁻¹ = b0
  linear_combination (π/(2*sin (μ*π))*(ν+μ+1)*a0)*R1 - (π/(2*sin (μ*π))*(ν-μ+1)*b0)*R2

theorem olverQ_recurrence_4 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2)*deriv (olverQ ν μ) z=(μ-ν-1)*(ν+μ+1)*olverQ (ν+1) μ z+(ν+1)*z*olverQ ν μ z := by
  have h0 := (olverQ_entire_order ν z hz).continuous
  have h1 := (olverQ_entire_order (ν+1) z hz).continuous
  have hd := continuous_deriv_olverQ_order ν hz
  exact legendre_eq_of_continuous_nonint (by fun_prop) (by fun_prop)
    (fun μ hμ => olverQ_recurrence_4_nonint ν μ hμ hz) μ

/-- associatedQ recurrence 4. -/
@[dlmf 14.10.E4]
theorem associatedQ_recurrence_4 (ν μ : ℂ) (h : LegendreQRegular ν μ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2:ℂ)*deriv (associatedQ ν μ) z=(μ-ν-1)*associatedQ (ν+1) μ z+(ν+1)*z*associatedQ ν μ z := by
  have R := olverQ_recurrence_4 ν μ hz
  have h1 : ν+μ+1 ≠ 0 := fun he => h 0 (by push_cast; linear_combination he)
  have e1' : Gamma (ν+1+μ+1) = (ν+μ+1)*Gamma (ν+μ+1) := by
    rw [show ν+1+μ+1 = (ν+μ+1)+1 by ring, Gamma_add_one _ h1]
  rw [deriv_associatedQ ν μ hz]
  simp only [associatedQ]
  rw [e1']
  linear_combination (exp (μ*π*I)*Gamma (ν+μ+1))*R

theorem olverQ_recurrence_5_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2)*deriv (olverQ ν μ) z=olverQ (ν-1) μ z-ν*z*olverQ ν μ z := by
  have R1 := associatedP_recurrence_5 ν μ hz
  have R2 := associatedP_recurrence_5 ν (-μ) hz
  rw [deriv_olverQ_nonint ν μ hμ hz, olverQ_eq_nonint (ν-1) μ hμ hz, olverQ_eq_nonint ν μ hμ hz]
  rw [show ν-1+μ+1 = ν+μ by ring, show ν-1-μ+1 = ν-μ by ring,
    legendre_recip_Gamma_succ (ν+μ), legendre_recip_Gamma_succ (ν-μ)]
  generalize (Gamma (ν+μ+1))⁻¹ = a0
  generalize (Gamma (ν-μ+1))⁻¹ = b0
  linear_combination (π/(2*sin (μ*π))*a0)*R1 - (π/(2*sin (μ*π))*b0)*R2

theorem olverQ_recurrence_5 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2)*deriv (olverQ ν μ) z=olverQ (ν-1) μ z-ν*z*olverQ ν μ z := by
  have h0 := (olverQ_entire_order ν z hz).continuous
  have h1 := (olverQ_entire_order (ν-1) z hz).continuous
  have hd := continuous_deriv_olverQ_order ν hz
  exact legendre_eq_of_continuous_nonint (by fun_prop) (by fun_prop)
    (fun μ hμ => olverQ_recurrence_5_nonint ν μ hμ hz) μ

/-- associatedQ recurrence 5. -/
@[dlmf 14.10.E5]
theorem associatedQ_recurrence_5 (ν μ : ℂ) (h : LegendreQRegular (ν-1) μ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2:ℂ)*deriv (associatedQ ν μ) z=(ν+μ)*associatedQ (ν-1) μ z-ν*z*associatedQ ν μ z := by
  have R := olverQ_recurrence_5 ν μ hz
  have h1 : ν+μ ≠ 0 := fun he => h 0 (by push_cast; linear_combination he)
  have e1 : Gamma (ν+μ+1) = (ν+μ)*Gamma (ν+μ) := Gamma_add_one _ h1
  rw [deriv_associatedQ ν μ hz]
  simp only [associatedQ]
  rw [e1, show ν-1+μ+1 = ν+μ by ring]
  linear_combination (exp (μ*π*I)*(ν+μ)*Gamma (ν+μ))*R

/-- Casoratian of `P^μ` and `𝑸^μ` in the degree, non-integer order. -/
theorem olverQ_casoratian_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP (ν+1) μ z*olverQ ν μ z-(ν+μ+1)*associatedP ν μ z*olverQ (ν+1) μ z=(Gamma (ν-μ+2))⁻¹ := by
  have h7 := associated_wronskian_7 ν μ hz
  unfold LegendreWronskian at h7
  have R1 := associatedP_recurrence_4 ν μ hz
  have R2 := associatedP_recurrence_4 ν (-μ) hz
  rw [olverQ_eq_nonint (ν+1) μ hμ hz, olverQ_eq_nonint ν μ hμ hz]
  rw [show ν+1+μ+1 = ν+μ+2 by ring, show ν+1-μ+1 = ν-μ+2 by ring,
    legendre_recip_Gamma_succ (ν+μ+1), show ν+μ+1+1 = ν+μ+2 by ring,
    legendre_recip_Gamma_succ (ν-μ+1), show ν-μ+1+1 = ν-μ+2 by ring]
  generalize (Gamma (ν+μ+2))⁻¹ = a0
  generalize (Gamma (ν-μ+2))⁻¹ = b0
  have hs := legendre_sin_ne_zero hμ
  have hs' : sin (π*μ) ≠ 0 := by rwa [mul_comm]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz2 := legendre_sq_sub_one_ne_zero hz
  have hz2' : 1-z^2 ≠ 0 := fun h => hz2 (by linear_combination -h)
  linear_combination (norm := skip) (π/(2*sin (μ*π))*b0*(1-z^2))*h7 -
    (π/(2*sin (μ*π))*b0*associatedP ν (-μ) z)*R1 + (π/(2*sin (μ*π))*b0*associatedP ν μ z)*R2
  field_simp
  ring

theorem olverQ_casoratian (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP (ν+1) μ z*olverQ ν μ z-(ν+μ+1)*associatedP ν μ z*olverQ (ν+1) μ z=(Gamma (ν-μ+2))⁻¹ := by
  have h0 := (olverQ_entire_order ν z hz).continuous
  have h1 := (olverQ_entire_order (ν+1) z hz).continuous
  have p0 := (associatedP_entire_order ν z hz).continuous
  have p1 := (associatedP_entire_order (ν+1) z hz).continuous
  have g := continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => ν-μ+2)
  exact legendre_eq_of_continuous_nonint (by fun_prop) g
    (fun μ hμ => olverQ_casoratian_nonint ν μ hμ hz) μ

/-- associated wronskian 11. -/
@[dlmf 14.2.E11]
theorem associated_wronskian_11 (ν μ : ℂ) (h : LegendreQRegular ν μ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP (ν+1) μ z*associatedQ ν μ z-associatedP ν μ z*associatedQ (ν+1) μ z=exp (μ*π*I)*Gamma (ν+μ+1)/Gamma (ν-μ+2) := by
  have R := olverQ_casoratian ν μ hz
  have h1 : ν+μ+1 ≠ 0 := fun he => h 0 (by push_cast; linear_combination he)
  have e1' : Gamma (ν+1+μ+1) = (ν+μ+1)*Gamma (ν+μ+1) := by
    rw [show ν+1+μ+1 = (ν+μ+1)+1 by ring, Gamma_add_one _ h1]
  simp only [associatedQ]
  rw [e1', div_eq_mul_inv]
  linear_combination (exp (μ*π*I)*Gamma (ν+μ+1))*R






/-- `𝖰^μ_ν` is differentiable on `(-1,1)`. -/
theorem differentiableAt_ferrersQ (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    DifferentiableAt ℝ (ferrersQ ν μ) x :=
  (((hasDerivAt_ferrersEven ν μ hx).const_mul _).add ((hasDerivAt_ferrersOdd ν μ hx).const_mul _)
    ).differentiableAt.congr_of_eventuallyEq
    ((ferrersQ_eqOn_even_odd ν μ).eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx))

/-- Order raising: `(1-x²)^{1/2} 𝖰^{μ+1} = -(1-x²) d𝖰^μ/dx - μ x 𝖰^μ`. -/
theorem ferrersQ_order_raise (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)^(1/2:ℂ)*ferrersQ ν (μ+1) x = -(1-x^2:ℂ)*deriv (ferrersQ ν μ) x-μ*x*ferrersQ ν μ x := by
  have h2 := ferrersQ_recurrence_2 ν μ h hx
  have h4 := ferrersQ_recurrence_4 ν μ h hx
  linear_combination h2 + h4

/-- Derivative of `(1-x²)^{1/2}` on `(-1,1)`. -/
theorem hasDerivAt_one_sub_sq_sqrt {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun y : ℝ => (1-(y:ℂ)^2)^(1/2:ℂ)) (-(x:ℂ)/(1-(x:ℂ)^2)^(1/2:ℂ)) x := by
  have hs := ferrers_one_sub_sq_mem_slitPlane hx
  have hne := slitPlane_ne_zero hs
  have h := ((hasStrictDerivAt_cpow_const (c := (1/2:ℂ)) hs).hasDerivAt.comp (x:ℂ)
    ((hasDerivAt_pow 2 (x:ℂ)).const_sub 1)).comp_ofReal
  refine h.congr_deriv ?_
  have hu : (1-(x:ℂ)^2)^(1/2:ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hne)
  have hsq : (1-(x:ℂ)^2)^(1/2:ℂ)*(1-(x:ℂ)^2)^(1/2:ℂ) = 1-(x:ℂ)^2 := by
    rw [← cpow_add _ _ hne]; norm_num
  rw [show (1/2:ℂ)-1 = -(1/2) by norm_num, cpow_neg]
  field_simp
  ring


/-- ferrersQ nat order derivative. -/
@[dlmf 14.6.E2, dlmf 14.7.E9]
theorem ferrersQ_nat_order_derivative (ν : ℂ) (m : ℕ) (h : LegendreQRegular ν 0) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν m x=(-1)^m*(1-x^2:ℂ)^((m:ℂ)/2)*iteratedDeriv m (ferrersQ ν 0) x := by
  set u : ℝ → ℂ := fun y => (1-(y:ℂ)^2)^(1/2:ℂ) with hu
  have hu0 : ∀ y ∈ Ioo (-1:ℝ) 1, u y ≠ 0 := fun y hy =>
    cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hy)))
  have husq : ∀ y ∈ Ioo (-1:ℝ) 1, u y ^ 2 = 1-(y:ℂ)^2 := fun y hy => by
    simp only [hu]
    rw [sq, ← cpow_add _ _ (slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hy))]; norm_num
  have hreg : ∀ k : ℕ, LegendreQRegular ν k := fun k n hn => h (n+k) (by push_cast; linear_combination hn)
  have key : ∀ k : ℕ, ∀ y ∈ Ioo (-1:ℝ) 1,
      ferrersQ ν k y = (-1)^k*u y^k*iteratedDeriv k (ferrersQ ν 0) y := by
    intro k
    induction k with
    | zero => intro y _; simp
    | succ k ih =>
      intro y hy
      have hD : iteratedDeriv k (ferrersQ ν 0) =ᶠ[𝓝 y]
          fun z => (-1)^k*((u z)^k)⁻¹*ferrersQ ν k z := by
        filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
        rw [ih z hz]
        have := hu0 z hz
        have hsq : ((-1:ℂ)^k)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        field_simp
        linear_combination (-(iteratedDeriv k (ferrersQ ν 0) z))*hsq
      have hQd := (differentiableAt_ferrersQ ν k hy).hasDerivAt
      have hud := hasDerivAt_one_sub_sq_sqrt hy
      have hf : HasDerivAt (fun z => (-1:ℂ)^k*(u z^k)⁻¹*ferrersQ ν k z) _ y :=
        ((hud.pow k).inv (pow_ne_zero _ (hu0 y hy))).const_mul ((-1:ℂ)^k) |>.mul hQd
      rw [iteratedDeriv_succ, hD.deriv_eq, hf.deriv]
      have hr := ferrersQ_order_raise ν k (hreg k) hy
      have h1 := hu0 y hy
      have h2 := husq y hy
      push_cast
      simp only [hu, Pi.pow_apply, Pi.inv_apply] at h1 h2 hr ⊢
      generalize (1-(y:ℂ)^2)^(1/2:ℂ) = U at h1 h2 hr ⊢
      rw [← h2] at hr
      rcases k with _ | j
      · simp at hr ⊢
        apply mul_left_cancel₀ h1
        linear_combination hr
      · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at hr ⊢
        generalize ferrersQ ν ((j:ℂ)+1+1) y = A at hr ⊢
        generalize deriv (ferrersQ ν ((j:ℂ)+1)) y = D at hr ⊢
        generalize ferrersQ ν ((j:ℂ)+1) y = B at hr ⊢
        rw [show (-1:ℂ)^(j+1+1) = -(-1)^(j+1) by ring]
        have hs : ((-1:ℂ)^(j+1))^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        generalize (-1:ℂ)^(j+1) = s at hs ⊢
        field_simp
        linear_combination U^2*U^(j*2)*hr + U^2*U^(j*2)*(((j:ℂ)+1)*y*B + U^2*D)*hs
  rw [key m x hx, show (m:ℂ)/2 = m*(1/2) by ring, cpow_nat_mul]

/-- associatedP nat order derivative. -/
@[dlmf 14.6.E3, dlmf 14.7.E11]
theorem associatedP_nat_order_derivative (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν m z=legendreBranchPower m z*iteratedDeriv m (associatedP ν 0) z := by
  have hz' := one_add_mem_slitPlane_of_sub_one hz
  have hw := mem_cutPlane_of_one_add hz'
  have hev : associatedP ν 0 =ᶠ[𝓝 z] legendreP ν := by
    filter_upwards [(isOpen_slitPlane.preimage (by fun_prop : Continuous fun w : ℂ => w-1)).mem_nhds hz]
      with w hw using associatedP_zero_order ν hw
  rw [hev.iteratedDeriv_eq, iteratedDeriv_legendreP ν m hz']
  rcases m with _ | k
  · simp [associatedP, legendreBranchPower, poch_zero, regularizedGaussHG_symm _ _ _ hw]
  have hg := associated_gauge_nat (k+1) hz
  have hsq : (-1:ℂ)^(k+1)*(-1)^(k+1) = 1 := by rw [← mul_pow]; norm_num
  unfold associatedP
  rw [show 1-((k+1:ℕ):ℂ) = -(k:ℂ) by push_cast; ring, regularizedGaussHG_neg_nat _ _ _ hw,
    regularizedGaussHG_symm (-ν+((k+1:ℕ):ℂ)) _ _ hw,
    show ν+1+k+1 = ν+1+((k+1:ℕ):ℂ) by push_cast; ring,
    show -ν+k+1 = -ν+((k+1:ℕ):ℂ) by push_cast; ring,
    show (k:ℂ)+2 = 1+((k+1:ℕ):ℂ) by push_cast; ring, div_pow (-1:ℂ) 2]
  set G := regularizedGaussHG (ν+1+((k+1:ℕ):ℂ)) (-ν+((k+1:ℕ):ℂ)) (1+((k+1:ℕ):ℂ)) ((1-z)/2)
  set E := exp (((k+1:ℕ):ℂ)/2*(log (z+1)-log (z-1)))
  linear_combination (poch (ν+1) (k+1) * poch (-ν) (k+1) * G) * ((-1)^(k+1) * hg -
    E * ((1-z)/2)^(k+1) * hsq)

theorem hasDerivAt_legendreBranchPower (c : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasDerivAt (legendreBranchPower c) (c*z/(z^2-1)*legendreBranchPower c z) z := by
  have hp' : z+1 ∈ slitPlane := by simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hz
  have hm := slitPlane_ne_zero hz
  have hp := slitPlane_ne_zero hp'
  have hz2 := legendre_sq_sub_one_ne_zero hz
  have h := ((((hasDerivAt_id z).sub_const 1).clog hz).add
    (((hasDerivAt_id z).add_const 1).clog hp')).const_mul (c/2) |>.cexp
  refine h.congr_deriv ?_
  simp only [id_eq, Pi.add_apply]
  unfold legendreBranchPower
  field_simp
  ring

theorem legendreBranchPower_mul (a b z : ℂ) :
    legendreBranchPower a z*legendreBranchPower b z = legendreBranchPower (a+b) z := by
  unfold legendreBranchPower
  rw [← exp_add]; congr 1; ring

theorem legendreBranchPower_two {z : ℂ} (hz : z-1 ∈ slitPlane) : legendreBranchPower 2 z = z^2-1 := by
  have hp' : z+1 ∈ slitPlane := by simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hz
  unfold legendreBranchPower
  rw [show (2:ℂ)/2*(log (z-1)+log (z+1)) = log (z-1)+log (z+1) by ring, exp_add,
    exp_log (slitPlane_ne_zero hz), exp_log (slitPlane_ne_zero hp')]
  ring

/-- olverQ nat order derivative. -/
@[dlmf 14.6.E5]
theorem olverQ_nat_order_derivative (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    poch (ν+1) m*olverQ ν m z=(-1)^m*legendreBranchPower m z*iteratedDeriv m (olverQ ν 0) z := by
  set R : ℕ → ℂ → ℂ := fun k w => poch (ν+1) k*olverQ ν k w with hR
  have hRd : ∀ (k : ℕ) w, w-1 ∈ slitPlane → HasDerivAt (R k) (poch (ν+1) k*deriv (olverQ ν k) w) w :=
    fun k w hw => (olverQ_analytic ν k w hw).differentiableAt.hasDerivAt.const_mul _
  have hraise : ∀ (k : ℕ) w, w-1 ∈ slitPlane →
      legendreBranchPower 1 w*R (k+1) w = (1-w^2)*(poch (ν+1) k*deriv (olverQ ν k) w)+k*w*R k w := by
    intro k w hw
    have h7 := olverQ_recurrence_7 ν k hw
    have h4 := olverQ_recurrence_4 ν k hw
    simp only [hR]
    rw [show poch (ν+1) (k+1) = poch (ν+1) k*(ν+1+k) by simp only [poch, ascPochhammer_succ_eval]]
    push_cast
    linear_combination (-(poch (ν+1) k)*(ν+k+1))*h7 - poch (ν+1) k*h4
  have key : ∀ k : ℕ, ∀ w, w-1 ∈ slitPlane →
      R k w = (-1)^k*legendreBranchPower k w*iteratedDeriv k (olverQ ν 0) w := by
    intro k
    induction k with
    | zero => intro w _; simp [hR, poch, legendreBranchPower]
    | succ k ih =>
      intro w hw
      have hs : (-1:ℂ)^k*(-1)^k = 1 := by rw [← mul_pow]; norm_num
      have hD : iteratedDeriv k (olverQ ν 0) =ᶠ[𝓝 w]
          fun y => (-1)^k*legendreBranchPower (-(k:ℂ)) y*R k y := by
        filter_upwards [isOpen_sub_one_mem_slitPlane.mem_nhds hw] with y hy
        rw [ih y hy]
        have hbb := legendreBranchPower_mul (-(k:ℂ)) k y
        rw [neg_add_cancel] at hbb
        have h0 : legendreBranchPower 0 y = 1 := by simp [legendreBranchPower]
        rw [h0] at hbb
        linear_combination (-(legendreBranchPower (-(k:ℂ)) y*legendreBranchPower k y*
          iteratedDeriv k (olverQ ν 0) y))*hs - iteratedDeriv k (olverQ ν 0) y*hbb
      have hf : HasDerivAt (fun y => (-1:ℂ)^k*legendreBranchPower (-(k:ℂ)) y*R k y) _ w :=
        ((hasDerivAt_legendreBranchPower (-(k:ℂ)) hw).const_mul ((-1:ℂ)^k)).mul (hRd k w hw)
      rw [iteratedDeriv_succ, hD.deriv_eq, hf.deriv]
      have hr := hraise k w hw
      have e1 := legendreBranchPower_mul ((k+1:ℕ):ℂ) (-(k:ℂ)) w
      rw [show ((k+1:ℕ):ℂ)+-(k:ℂ) = 1 by push_cast; ring] at e1
      have e2 := legendreBranchPower_mul 1 1 w
      rw [show (1:ℂ)+1 = 2 by norm_num, legendreBranchPower_two hw] at e2
      have hz2 := legendre_sq_sub_one_ne_zero hw
      rw [pow_succ]
      generalize legendreBranchPower ((k+1:ℕ):ℂ) w = Bk1 at e1 ⊢
      generalize legendreBranchPower (-(k:ℂ)) w = Bmk at e1 ⊢
      generalize legendreBranchPower 1 w = B1 at e1 e2 hr ⊢
      generalize (-1:ℂ)^k = s at hs ⊢
      generalize poch (ν+1) k*deriv (olverQ ν k) w = Dp at hr ⊢
      generalize R (k+1) w = Rk1 at hr ⊢
      generalize R k w = Rk at hr ⊢
      linear_combination (norm := (field_simp; ring)) (Bk1*Bmk*(Dp-k*w*Rk/(w^2-1)))*hs +
        (Dp-k*w*Rk/(w^2-1))*e1 + (B1/(w^2-1))*hr - (Rk1/(w^2-1))*e2
  exact key m z hz

/-- associatedQ nat order derivative. -/
@[dlmf 14.6.E4, dlmf 14.7.E12]
theorem associatedQ_nat_order_derivative (ν : ℂ) (m : ℕ) (h : LegendreQRegular ν 0) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedQ ν m z=legendreBranchPower m z*iteratedDeriv m (associatedQ ν 0) z := by
  have hO := olverQ_nat_order_derivative ν m hz
  have h' : ∀ k : ℕ, ν+1 ≠ -k := fun k hk => h k (by linear_combination hk)
  have hG := Gamma_add_nat_div_Gamma_eq (n := m) (ν+1) h'
  rw [div_eq_iff (Gamma_ne_zero h')] at hG
  have hQ0 : associatedQ ν 0 = fun w => (exp ((0:ℂ)*π*I)*Gamma (ν+0+1))*olverQ ν 0 w := rfl
  rw [hQ0, iteratedDeriv_const_mul_field]
  simp only [associatedQ]
  rw [show (m:ℂ)*π*I = m*(π*I) by ring, exp_nat_mul, exp_pi_mul_I, show ν+m+1 = ν+1+m by ring, hG]
  simp only [zero_mul, Complex.exp_zero, one_mul, add_zero]
  have hs : (-1:ℂ)^m*(-1)^m = 1 := by rw [← mul_pow]; norm_num
  linear_combination ((-1)^m*Gamma (ν+1))*hO + (Gamma (ν+1)*legendreBranchPower m z*
    iteratedDeriv m (olverQ ν 0) z)*hs


end DLMF.Legendre
