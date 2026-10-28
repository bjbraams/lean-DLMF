/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Associated.ConjugationAndValues

/-!
# Ferrers fundamental pairs and their Wronskians

Abel identities and connection coefficients determine the Wronskians of Ferrers fundamental
pairs.

Source references and common attribution are retained in
`DLMF.Legendre.Associated`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat ComplexConjugate

namespace DLMF.Legendre

/-! ### Ferrers solutions and Abel's identity -/

/-- `f` solves the associated Legendre equation with degree `ν` and order `μ` on `(-1,1)`,
with a second derivative of `f` in the strong sense. -/
def IsFerrersSolution (ν μ : ℂ) (f : ℝ → ℂ) : Prop :=
  ∀ y ∈ Ioo (-1:ℝ) 1, DifferentiableAt ℝ f y ∧ ∃ f2, HasDerivAt (deriv f) f2 y ∧
    (1-(y:ℂ)^2)*f2-2*y*deriv f y+(ν*(ν+1)-μ^2/(1-(y:ℂ)^2))*f y = 0

/-- Abel's identity: `(1-x²)` times the Wronskian of two Ferrers solutions is constant. -/
theorem IsFerrersSolution.wronskian_const {ν μ : ℂ} {f g : ℝ → ℂ} (hf : IsFerrersSolution ν μ f)
    (hg : IsFerrersSolution ν μ g) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-(x:ℂ)^2)*(f x*deriv g x-g x*deriv f x) = f 0*deriv g 0-g 0*deriv f 0 := by
  set F : ℝ → ℂ := fun y => (1-(y:ℂ)^2)*(f y*deriv g y-g y*deriv f y) with hFdef
  have hF : ∀ y ∈ Ioo (-1:ℝ) 1, HasDerivAt F 0 y := by
    intro y hy
    obtain ⟨hf1, f2, hf2, ef⟩ := hf y hy
    obtain ⟨hg1, g2, hg2, eg⟩ := hg y hy
    have hsq : HasDerivAt (fun y : ℝ => 1-(y:ℂ)^2) (-(2*(y:ℂ))) y := by
      have := ((hasDerivAt_id y).ofReal_comp.pow 2).const_sub 1
      simpa using this
    refine (hsq.mul ((hf1.hasDerivAt.mul hg2).sub (hg1.hasDerivAt.mul hf2))).congr_deriv ?_
    simp only [Pi.mul_apply, Pi.sub_apply]
    linear_combination (f y)*eg-(g y)*ef
  have h0 : (0:ℝ) ∈ Ioo (-1:ℝ) 1 := by norm_num
  have := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun y hy => (hF y hy).differentiableAt.differentiableWithinAt) (fun y hy => (hF y hy).deriv) hx h0
  simpa [F] using this

/-- Linear combinations of Ferrers solutions are Ferrers solutions. -/
theorem IsFerrersSolution.add_smul {ν μ : ℂ} {f g : ℝ → ℂ} (hf : IsFerrersSolution ν μ f)
    (hg : IsFerrersSolution ν μ g) (a b : ℂ) :
    IsFerrersSolution ν μ (fun y => a*f y+b*g y) := by
  intro y hy
  obtain ⟨hf1, f2, hf2, ef⟩ := hf y hy
  obtain ⟨hg1, g2, hg2, eg⟩ := hg y hy
  have hd : ∀ z ∈ Ioo (-1:ℝ) 1, deriv (fun y => a*f y+b*g y) z = a*deriv f z+b*deriv g z := by
    intro z hz
    exact (((hf z hz).1.hasDerivAt.const_mul a).add ((hg z hz).1.hasDerivAt.const_mul b)).deriv
  refine ⟨((hf1.const_mul a).add (hg1.const_mul b)), a*f2+b*g2, ?_, ?_⟩
  · refine ((hf2.const_mul a).add (hg2.const_mul b)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz using hd z hz
  · rw [hd y hy]
    linear_combination a*ef+b*eg

/-- Ferrers solutions are determined on `(-1,1)`. -/
theorem IsFerrersSolution.congr {ν μ : ℂ} {f g : ℝ → ℂ} (hf : IsFerrersSolution ν μ f)
    (h : EqOn f g (Ioo (-1:ℝ) 1)) : IsFerrersSolution ν μ g := by
  intro y hy
  have hev : ∀ z ∈ Ioo (-1:ℝ) 1, f =ᶠ[𝓝 z] g := fun z hz => by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with w hw using h hw
  obtain ⟨hf1, f2, hf2, ef⟩ := hf y hy
  have hd : deriv f =ᶠ[𝓝 y] deriv g := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with w hw using (hev w hw).deriv_eq
  refine ⟨hf1.congr_of_eventuallyEq (hev y hy).symm, f2, hf2.congr_of_eventuallyEq hd.symm, ?_⟩
  rw [← hd.eq_of_nhds, ← h hy]
  exact ef

/-- Reflection `x ↦ -x` preserves Ferrers solutions. -/
theorem IsFerrersSolution.comp_neg {ν μ : ℂ} {f : ℝ → ℂ} (hf : IsFerrersSolution ν μ f) :
    IsFerrersSolution ν μ (fun y => f (-y)) := by
  have hm : ∀ y ∈ Ioo (-1:ℝ) 1, -y ∈ Ioo (-1:ℝ) 1 := fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hd : ∀ y ∈ Ioo (-1:ℝ) 1, HasDerivAt (fun y => f (-y)) (-deriv f (-y)) y := fun y hy => by
    exact ((hf (-y) (hm y hy)).1.hasDerivAt.scomp y (hasDerivAt_neg y)).congr_deriv (by simp)
  intro y hy
  obtain ⟨hf1, f2, hf2, ef⟩ := hf (-y) (hm y hy)
  refine ⟨(hd y hy).differentiableAt, f2, ?_, ?_⟩
  · have := (hf2.scomp y (hasDerivAt_neg y)).neg
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv (by simp)
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
    simp [(hd z hz).deriv]
  · rw [(hd y hy).deriv]
    push_cast at ef ⊢
    linear_combination ef

/-- The Gauss equation for `𝐅(α,β;γ;·)` at `x²`, `x ∈ (-1,1)`. -/
theorem regularizedGaussHG_ode_sq (α β γ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (x:ℂ)^2*(1-(x:ℂ)^2)*deriv (deriv (regularizedGaussHG α β γ)) ((x:ℂ)^2)+
      (γ-(α+β+1)*(x:ℂ)^2)*deriv (regularizedGaussHG α β γ) ((x:ℂ)^2)-
      α*β*regularizedGaussHG α β γ ((x:ℂ)^2)=0 := by
  have hs := ferrers_one_sub_sq_mem_slitPlane hx
  rw [←show iteratedDeriv 2 (regularizedGaussHG α β γ)=deriv (deriv (regularizedGaussHG α β γ)) by
    rw [iteratedDeriv_succ,iteratedDeriv_one],iteratedDeriv_regularizedGaussHG α β γ 2 hs,
    deriv_regularizedGaussHG α β γ hs]
  exact regularizedGaussHG_ode α β γ hs

/-- The even quadratic solution solves the associated Legendre equation. -/
theorem ferrersEven_isFerrersSolution (ν μ : ℂ) : IsFerrersSolution ν μ (ferrersEven ν μ) := by
  let a : ℂ := -(ν+μ)/2
  let b : ℂ := (ν-μ+1)/2
  let F := regularizedGaussHG a b (1/2)
  let g : ℂ→ℂ := fun z=>(1-z^2)^(-μ/2)
  let q : ℂ→ℂ := fun z=>μ*z/(1-z^2)
  let E1 : ℝ→ℂ := fun y=>g y*(q y*F ((y:ℂ)^2)+2*y*deriv F ((y:ℂ)^2))
  have hE (y : ℝ) (hy : y∈Ioo (-1:ℝ) 1) : HasDerivAt (ferrersEven ν μ) (E1 y) y :=
    (quadratic_gauss_gauge_jets a b (1/2) μ (ferrers_one_sub_sq_mem_slitPlane hy)).1.comp_ofReal
  intro x hx
  have heq : deriv (ferrersEven ν μ)=ᶠ[𝓝 x] E1 := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (hE y hy).deriv
  have hE2 := (quadratic_gauss_gauge_jets a b (1/2) μ (ferrers_one_sub_sq_mem_slitPlane hx)).2.comp_ofReal
  refine ⟨(hE x hx).differentiableAt, _, hE2.congr_of_eventuallyEq heq, ?_⟩
  have he := regularizedGaussHG_ode_sq a b (1/2) hx
  rw [(hE x hx).deriv]
  simp only [ferrersEven]
  dsimp only [E1,g,q,F,a,b] at he ⊢
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  linear_combination (norm := (field_simp [hne]; ring)) (4*(1-(x:ℂ)^2)^(-μ/2))*he

/-- The odd quadratic solution solves the associated Legendre equation. -/
theorem ferrersOdd_isFerrersSolution (ν μ : ℂ) : IsFerrersSolution ν μ (ferrersOdd ν μ) := by
  let A : ℂ := (1-ν-μ)/2
  let B : ℂ := (ν-μ+2)/2
  let G := regularizedGaussHG A B (3/2)
  let g : ℂ→ℂ := fun z=>(1-z^2)^(-μ/2)
  let q : ℂ→ℂ := fun z=>μ*z/(1-z^2)
  let O : ℝ→ℂ := fun y=>g y*G ((y:ℂ)^2)
  let O1 : ℝ→ℂ := fun y=>g y*(q y*G ((y:ℂ)^2)+2*y*deriv G ((y:ℂ)^2))
  have hO (y : ℝ) (hy : y∈Ioo (-1:ℝ) 1) : HasDerivAt O (O1 y) y :=
    (quadratic_gauss_gauge_jets A B (3/2) μ (ferrers_one_sub_sq_mem_slitPlane hy)).1.comp_ofReal
  have hd (y : ℝ) (hy : y∈Ioo (-1:ℝ) 1) :
      HasDerivAt (ferrersOdd ν μ) (O y+y*O1 y) y := by
    have hh := (hasDerivAt_id y).ofReal_comp.mul (hO y hy)
    exact hh.congr_deriv (by simp)
  intro x hx
  have heq : deriv (ferrersOdd ν μ)=ᶠ[𝓝 x] fun y=>O y+y*O1 y := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (hd y hy).deriv
  have hO2 := (quadratic_gauss_gauge_jets A B (3/2) μ (ferrers_one_sub_sq_mem_slitPlane hx)).2.comp_ofReal
  have hsecond := (hO x hx).add ((hasDerivAt_id x).ofReal_comp.mul hO2)
  refine ⟨(hd x hx).differentiableAt, _, hsecond.congr_of_eventuallyEq heq, ?_⟩
  have ho := regularizedGaussHG_ode_sq A B (3/2) hx
  rw [(hd x hx).deriv]
  simp only [ferrersOdd, id_eq, ofReal_one]
  dsimp only [O1,O,g,q,G,A,B] at ho ⊢
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  linear_combination (norm := (field_simp [hne]; ring)) (4*x*(1-(x:ℂ)^2)^(-μ/2))*ho

/-- The Wronskian of the even and odd quadratic solutions, `𝒲{E,O} = 2/(π(1-x²))`. -/
theorem ferrers_even_odd_wronskian (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersEven ν μ x*deriv (ferrersOdd ν μ) x-ferrersOdd ν μ x*deriv (ferrersEven ν μ) x =
      2/(π*(1-(x:ℂ)^2)) := by
  have hw := (ferrersEven_isFerrersSolution ν μ).wronskian_const (ferrersOdd_isFerrersSolution ν μ) hx
  have hE0 : ferrersEven ν μ 0 = 1/(Real.sqrt π:ℂ) := by
    unfold ferrersEven
    rw [ofReal_zero, show (0:ℂ)^2 = 0 by norm_num, regularizedGaussHG_zero_of_regular half_ne_neg_nat,
      legendre_Gamma_one_half]
    simp
  have hO0 : ferrersOdd ν μ 0 = 0 := by simp [ferrersOdd]
  have hO1 : deriv (ferrersOdd ν μ) 0 = 2/(Real.sqrt π:ℂ) := by
    have h := (hasDerivAt_quadratic_odd ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) μ).comp_ofReal (z := 0)
    rw [show ferrersOdd ν μ = fun y:ℝ => (y:ℂ)*((1-(y:ℂ)^2)^(-μ/2)*
      regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) ((y:ℂ)^2)) from rfl, h.deriv,
      regularizedGaussHG_zero_of_regular DLMF.Hypergeometric.three_halves_not_neg_nat,
          legendre_Gamma_three_halves]
    field_simp
  rw [hE0, hO0, hO1] at hw
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have hs2 : (Real.sqrt π:ℂ)^2 = π := by rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hs : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [eq_div_iff (mul_ne_zero hP hne)]
  rw [← hs2]
  field_simp at hw ⊢
  linear_combination hw

/-- For real `ν, μ` and `-1 < x < 1`, `𝖯^μ_ν(x)` is real. -/
theorem ferrersP_real (ν μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (ferrersP ν μ x).im=0 := by
  rw [← conj_eq_iff_im, ferrersP_conj _ _ hx]; simp

/-- For real `ν, μ` with `ν+μ ∉ {-1,-2,…}` and `-1 < x < 1`, `𝖰^μ_ν(x)` is real. -/
theorem ferrersQ_real (ν μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (h : LegendreQRegular ν μ) :
    (ferrersQ ν μ x).im=0 := by
  rw [← conj_eq_iff_im, ferrersQ_conj _ _ hx]; simp

/-- For real `τ, μ` and `-1 < x < 1`, the conical Ferrers function `𝖯^μ_{-1/2+iτ}(x)` is real (DLMF
§14.20). -/
theorem ferrersP_conical_real (τ μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (ferrersP (-1/2+I*τ) μ x).im=0 := by
  have hp : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  rw [← conj_eq_iff_im, ferrersP_conj _ _ hx, conj_ofReal,
    show conj (-1/2+I*(τ:ℂ)) = -(-1/2+I*τ)-1 by simp [map_div₀, map_ofNat]; ring]
  unfold ferrersP
  rw [show -(-(-1/2+I*(τ:ℂ))-1) = (-1/2+I*τ)+1 by ring, show -(-1/2+I*(τ:ℂ))-1+1 = -(-1/2+I*τ) by ring,
    regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add hp)]

/-- Complex Wronskian. -/
def LegendreWronskian (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z*deriv g z-g z*deriv f z

/-- The Wronskian `f(x) g'(x) - g(x) f'(x)` of two functions `ℝ → ℂ`. -/
def ferrersWronskian (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  f x*deriv g x-g x*deriv f x

/-- The Wronskian of two combinations of the even and odd solutions. -/
theorem ferrersWronskian_of_even_odd {ν μ a b c d : ℂ} {f g : ℝ → ℂ}
    (hf : EqOn f (fun y => a*ferrersEven ν μ y+b*ferrersOdd ν μ y) (Ioo (-1:ℝ) 1))
    (hg : EqOn g (fun y => c*ferrersEven ν μ y+d*ferrersOdd ν μ y) (Ioo (-1:ℝ) 1))
    {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian f g x = (a*d-b*c)*(2/(π*(1-(x:ℂ)^2))) := by
  have hE := ((ferrersEven_isFerrersSolution ν μ) x hx).1.hasDerivAt
  have hO := ((ferrersOdd_isFerrersSolution ν μ) x hx).1.hasDerivAt
  have hev : ∀ {h : ℝ → ℂ} {p q : ℂ},
      EqOn h (fun y => p*ferrersEven ν μ y+q*ferrersOdd ν μ y) (Ioo (-1:ℝ) 1) →
      deriv h x = p*deriv (ferrersEven ν μ) x+q*deriv (ferrersOdd ν μ) x := by
    intro h p q hh
    have : h =ᶠ[𝓝 x] fun y => p*ferrersEven ν μ y+q*ferrersOdd ν μ y := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using hh hy
    rw [this.deriv_eq]
    exact ((hE.const_mul p).add (hO.const_mul q)).deriv
  unfold ferrersWronskian
  rw [hev hf, hev hg, hf hx, hg hx, ← ferrers_even_odd_wronskian ν μ hx]
  ring

/-- `𝖯^μ_ν` as a combination of the even and odd solutions on `(-1,1)`. -/
theorem ferrersP_eqOn_even_odd (ν μ : ℂ) : EqOn (ferrersP ν μ) (fun y =>
    2^μ*π*((Gamma ((1-ν-μ)/2))⁻¹*(Gamma ((ν-μ+2)/2))⁻¹)*ferrersEven ν μ y+
      -(2^μ*π*((Gamma (-(ν+μ)/2))⁻¹*(Gamma ((ν-μ+1)/2))⁻¹))*ferrersOdd ν μ y) (Ioo (-1:ℝ) 1) :=
  fun y hy => by rw [ferrersP_even_odd ν μ hy]; ring

/-- `𝖯^{-μ}_ν` as a combination of the even and odd solutions on `(-1,1)`. -/
theorem ferrersP_neg_eqOn_even_odd (ν μ : ℂ) : EqOn (ferrersP ν (-μ)) (fun y =>
    2^(-μ)*π*((Gamma ((1-ν+μ)/2))⁻¹*(Gamma ((ν+μ+2)/2))⁻¹)*ferrersEven ν μ y+
      -(2^(-μ)*π*((Gamma ((μ-ν)/2))⁻¹*(Gamma ((ν+μ+1)/2))⁻¹))*ferrersOdd ν μ y) (Ioo (-1:ℝ) 1) :=
  fun y hy => by rw [ferrersP_neg_even_odd ν μ hy]; ring

/-- `𝖯^{-μ}_ν(-x)` as a combination of the even and odd solutions on `(-1,1)`. -/
theorem ferrersP_neg_reflect_eqOn_even_odd (ν μ : ℂ) : EqOn (fun x => ferrersP ν (-μ) (-x)) (fun y =>
    2^(-μ)*π*((Gamma ((1-ν+μ)/2))⁻¹*(Gamma ((ν+μ+2)/2))⁻¹)*ferrersEven ν μ y+
      2^(-μ)*π*((Gamma ((μ-ν)/2))⁻¹*(Gamma ((ν+μ+1)/2))⁻¹)*ferrersOdd ν μ y) (Ioo (-1:ℝ) 1) :=
  fun y hy => by
    simp only
    rw [ferrersP_neg_even_odd ν μ (ferrers_neg_mem_Ioo hy), ferrersEven_neg, ferrersOdd_neg]; ring

/-- `𝖰^μ_ν` as a combination of the even and odd solutions on `(-1,1)`. -/
theorem ferrersQ_eqOn_even_odd (ν μ : ℂ) : EqOn (ferrersQ ν μ) (fun y =>
    2^μ*π/2*(-sin ((ν+μ)*π/2)*Gamma ((ν+μ+1)/2)*(Gamma ((ν-μ+2)/2))⁻¹)*ferrersEven ν μ y+
      2^μ*π/2*(cos ((ν+μ)*π/2)*Gamma ((ν+μ+2)/2)*(Gamma ((ν-μ+1)/2))⁻¹)*ferrersOdd ν μ y)
    (Ioo (-1:ℝ) 1) :=
  fun y _ => by rw [ferrersQ_even_odd]; ring

/-- `𝖯^μ_ν` solves the associated Legendre equation on `(-1,1)`, for all complex `ν, μ`. -/
theorem ferrersP_isFerrersSolution (ν μ : ℂ) : IsFerrersSolution ν μ (ferrersP ν μ) :=
  ((ferrersEven_isFerrersSolution ν μ).add_smul (ferrersOdd_isFerrersSolution ν μ) _ _).congr
    (ferrersP_eqOn_even_odd ν μ).symm

/-- `𝖰^μ_ν` solves the associated Legendre equation on `(-1,1)`, for all complex `ν, μ`. -/
theorem ferrersQ_isFerrersSolution (ν μ : ℂ) : IsFerrersSolution ν μ (ferrersQ ν μ) :=
  ((ferrersEven_isFerrersSolution ν μ).add_smul (ferrersOdd_isFerrersSolution ν μ) _ _).congr
    (ferrersQ_eqOn_even_odd ν μ).symm

/-- `𝖯^μ_ν` with regular-parameter coefficients, on `(-1,1)`. -/
theorem ferrersP_regular_eqOn {ν μ : ℂ} (h : LegendreQRegular ν μ) : EqOn (ferrersP ν μ) (fun y =>
    2^μ*(cos ((ν+μ)*π/2)*Gamma ((ν+μ+1)/2)*(Gamma ((ν-μ+2)/2))⁻¹)*ferrersEven ν μ y+
      2^μ*(sin ((ν+μ)*π/2)*Gamma ((ν+μ+2)/2)*(Gamma ((ν-μ+1)/2))⁻¹)*ferrersOdd ν μ y)
    (Ioo (-1:ℝ) 1) :=
  fun y hy => by rw [ferrersP_regular h hy]; simp only [div_eq_mul_inv]; ring

/-- DLMF 14.2.3: for `-1 < x < 1`, `𝒲{𝖯^{-μ}_ν(x), 𝖯^{-μ}_ν(-x)} = 2/(Γ(μ-ν) Γ(ν+μ+1) (1-x²))`, with
`𝒲{f,g} = f g' - g f'`. -/
@[dlmf 14.2.E3]
theorem ferrers_wronskian_3 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian (ferrersP ν (-μ)) (fun x => ferrersP ν (-μ) (-x)) x=2/(Gamma (μ-ν)*Gamma (ν+μ+1)*(1-x^2:ℂ)) := by
  rw [ferrersWronskian_of_even_odd (ferrersP_neg_eqOn_even_odd ν μ)
    (ferrersP_neg_reflect_eqOn_even_odd ν μ) hx,
    show (2:ℂ)/(Gamma (μ-ν)*Gamma (ν+μ+1)*(1-x^2:ℂ)) =
      (Gamma (μ-ν))⁻¹*(Gamma (ν+μ+1))⁻¹*(2/(1-x^2:ℂ)) by rw [div_eq_mul_inv, mul_inv, mul_inv]; ring,
    legendre_recip_Gamma_sub, legendre_recip_duplication (ν+μ), cpow_neg, cpow_neg, cpow_add _ _ two_ne_zero]
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have hs2 : (Real.sqrt π:ℂ)^2 = π := by rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hN : (2:ℂ)^ν ≠ 0 := by simp
  rw [← hs2]
  field_simp
  ring

/-- DLMF 14.2.4: when `ν+μ ∉ {-1,-2,…}` and for `-1 < x < 1`, `𝒲{𝖯^μ_ν(x), 𝖰^μ_ν(x)} =
Γ(ν+μ+1)/(Γ(ν-μ+1) (1-x²))`. -/
@[dlmf 14.2.E4]
theorem ferrers_wronskian_4 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian (ferrersP ν μ) (ferrersQ ν μ) x=Gamma (ν+μ+1)/(Gamma (ν-μ+1)*(1-x^2:ℂ)) := by
  rw [ferrersWronskian_of_even_odd (ferrersP_regular_eqOn h) (ferrersQ_eqOn_even_odd ν μ) hx,
    show Gamma (ν+μ+1)/(Gamma (ν-μ+1)*(1-x^2:ℂ)) = Gamma (ν+μ+1)/Gamma (ν-μ+1)/(1-x^2:ℂ) from
      (div_div _ _ _).symm, legendre_Gamma_ratio]
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have pyth := sin_sq_add_cos_sq ((ν+μ)*π/2)
  field_simp
  linear_combination (Gamma ((ν+μ+1)/2)*Gamma ((ν+μ+2)/2)*(Gamma ((ν-μ+2)/2))⁻¹*
    (Gamma ((ν-μ+1)/2))⁻¹)*pyth

/-- DLMF 14.2.6: when `ν+μ ∉ {-1,-2,…}` and for `-1 < x < 1`, `𝒲{𝖯^{-μ}_ν(x), 𝖰^μ_ν(x)} =
cos(μπ)/(1-x²)`. -/
@[dlmf 14.2.E6]
theorem ferrers_wronskian_6 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian (ferrersP ν (-μ)) (ferrersQ ν μ) x=cos (μ*π)/(1-x^2:ℂ) := by
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersWronskian_of_even_odd (ferrersP_neg_eqOn_even_odd ν μ) (ferrersQ_eqOn_even_odd ν μ) hx,
    show cos (μ*π)/(1-x^2:ℂ) = (π/2*cos (μ*π))*(2/(π*(1-x^2:ℂ))) by field_simp]
  congr 1
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero h
  obtain ⟨-, -, e2, o2⟩ := legendre_reflections ν μ
  have kT : (2:ℂ)^μ*((2:ℂ)^μ)⁻¹ = 1 := mul_inv_cancel₀ (by simp)
  have k1 : Gamma ((ν+μ+1)/2)*(Gamma ((ν+μ+1)/2))⁻¹ = 1 := mul_inv_cancel₀ hg1
  have k2 : Gamma ((ν+μ+2)/2)*(Gamma ((ν+μ+2)/2))⁻¹ = 1 := mul_inv_cancel₀ hg2
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [cpow_neg, show μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 by ring, cos_sub]
  generalize (Gamma ((1-ν+μ)/2))⁻¹ = A2 at e2
  generalize (Gamma ((μ-ν)/2))⁻¹ = B2 at o2
  generalize (Gamma ((ν-μ+1)/2))⁻¹ = r1 at e2
  generalize (Gamma ((ν-μ+2)/2))⁻¹ = r2 at o2
  generalize (Gamma ((ν+μ+1)/2))⁻¹ = R1 at k1
  generalize (Gamma ((ν+μ+2)/2))⁻¹ = R2 at k2
  generalize Gamma ((ν+μ+1)/2) = g1 at k1
  generalize Gamma ((ν+μ+2)/2) = g2 at k2
  generalize ((2:ℂ)^μ)⁻¹ = Ti at kT
  generalize (2:ℂ)^μ = T at kT
  generalize sin ((ν+μ)*π/2) = sb
  generalize cos ((ν+μ)*π/2) = cb
  generalize sin ((ν-μ)*π/2) = sa at o2
  generalize cos ((ν-μ)*π/2) = ca at e2
  linear_combination (π/2:ℂ)*((Ti*T*R2*g2*cb)*e2 - (Ti*T*R1*g1*sb)*o2 + cb*ca*(R2*g2*kT + k2) +
    sb*sa*(R1*g1*kT + k1))

/-- DLMF 14.2.7 (Ferrers form): for `-1 < x < 1`, `𝒲{𝖯^{-μ}_ν(x), 𝖯^μ_ν(x)} = 2 sin(μπ)/(π
(1-x²))`. -/
@[dlmf 14.2.E7]
theorem ferrers_wronskian_7 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian (ferrersP ν (-μ)) (ferrersP ν μ) x=2*sin (μ*π)/(π*(1-x^2:ℂ)) := by
  rw [ferrersWronskian_of_even_odd (ferrersP_neg_eqOn_even_odd ν μ) (ferrersP_eqOn_even_odd ν μ) hx,
    show 2*sin (μ*π)/(π*(1-x^2:ℂ)) = sin (μ*π)*(2/(π*(1-x^2:ℂ))) by ring]
  congr 1
  obtain ⟨e1, o1, e2, o2⟩ := legendre_reflections ν μ
  have kT : (2:ℂ)^μ*((2:ℂ)^μ)⁻¹ = 1 := mul_inv_cancel₀ (by simp)
  rw [cpow_neg, show μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 by ring, sin_sub]
  generalize (Gamma ((1-ν-μ)/2))⁻¹ = A1 at e1
  generalize (Gamma (-(ν+μ)/2))⁻¹ = B1 at o1
  generalize (Gamma ((1-ν+μ)/2))⁻¹ = A2 at e2
  generalize (Gamma ((μ-ν)/2))⁻¹ = B2 at o2
  generalize (Gamma ((ν-μ+1)/2))⁻¹ = r1 at e2
  generalize (Gamma ((ν-μ+2)/2))⁻¹ = r2 at o2
  generalize (Gamma ((ν+μ+1)/2))⁻¹ = R1 at e1
  generalize (Gamma ((ν+μ+2)/2))⁻¹ = R2 at o1
  generalize ((2:ℂ)^μ)⁻¹ = Ti at kT
  generalize (2:ℂ)^μ = T at kT
  generalize sin ((ν+μ)*π/2) = sb at o1
  generalize cos ((ν+μ)*π/2) = cb at e1
  generalize sin ((ν-μ)*π/2) = sa at o2
  generalize cos ((ν-μ)*π/2) = ca at e2
  generalize (π:ℂ) = P at e1 o1 e2 o2
  linear_combination (sb*ca-cb*sa)*kT + T*Ti*(-(P*B1*R2)*e2 - ca*o1 + (P*A1*R1)*o2 - sa*e1)

end DLMF.Legendre
end
