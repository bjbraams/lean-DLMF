/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Relations
public import DLMF.Bessel.SphericalSeriesTools

/-!
# Power and spherical Bessel series, DLMF §7.6

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- The series with terms `(fun n : ℕ => 2/Real.sqrt π*(-1 : ℂ)^n*z^(2*n+1)/((n.factorial :
ℂ)*(2*n+1)))` converges to `(erf z)`. -/
@[dlmf 7.6.E1]
theorem hasSum_erf_complex (z : ℂ) :
    HasSum (fun n : ℕ => 2/Real.sqrt π*(-1 : ℂ)^n*z^(2*n+1)/((n.factorial : ℂ)*(2*n+1))) (erf z) := by
  have hs (w : ℂ) : HasSum (fun n : ℕ => ((-1:ℂ)^n/n.factorial)*w^(2*n)) (exp (-w^2)) := by
    have he := NormedSpace.expSeries_div_hasSum_exp (-w^2)
    rw [← Complex.exp_eq_exp_ℂ] at he
    convert he using 1
    funext n
    rw [neg_pow, pow_mul]
    ring
  have hb (R : ℝ) (_ : 0 ≤ R) : Summable (fun n : ℕ => ‖(-1:ℂ)^n/n.factorial‖*R^(2*n)) := by
    convert Real.summable_pow_div_factorial (R^2) using 1
    funext n
    simp [pow_mul]
    ring
  have h := (hasSum_primitive_monomials _ (fun n => 2*n) hs hb z).mul_left (2/(Real.sqrt π:ℂ))
  rw [← erf_complex_segment_integral] at h
  refine h.congr_fun fun n => ?_
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The rising factorial `(3/2)_n` times `2^n` is the odd product `1·3···(2n+1)`. -/
theorem poch_three_half_mul_two_pow (n : ℕ) : poch (3/2) n*(2:ℂ)^n = oddProduct n := by
  induction n with
  | zero => simp [oddProduct, poch_zero]
  | succ n ih =>
    rw [poch_succ, oddProduct, Finset.prod_range_succ, ← oddProduct, ← ih, pow_succ]
    push_cast
    ring

/-- The series with terms `(fun n : ℕ => 2/Real.sqrt π*exp (-z^2)*(2 : ℂ)^n*z^(2*n+1)/oddProduct
n)` converges to `(erf z)`. -/
@[dlmf 7.6.E2]
theorem hasSum_erf_scaled (z : ℂ) :
    HasSum (fun n : ℕ => 2/Real.sqrt π*exp (-z^2)*(2 : ℂ)^n*z^(2*n+1)/oddProduct n) (erf z) := by
  have h := (hasSum_kummerM (a:=1) three_half_ne_neg_nat (z^2)).mul_left
    (2*z/Real.sqrt π*exp (-z^2))
  rw [← (erf_kummerM_pair z).2] at h
  refine h.congr_fun fun n => ?_
  have hp : poch (3/2:ℂ) n ≠ 0 := by
    intro h0
    have := poch_three_half_mul_two_pow n
    rw [h0, zero_mul] at this
    have hne : oddProduct n ≠ 0 := by
      unfold oddProduct
      rw [Finset.prod_ne_zero_iff]
      intro j _
      exact_mod_cast (show (2*j+1 : ℕ) ≠ 0 by omega)
    exact hne this.symm
  rw [← poch_three_half_mul_two_pow, kummerMCoeff, poch_nat_one]
  have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  ring

/-- Half-integer Gamma values: `Γ(m+3/2)·2^m = (√π/2)·1·3···(2m+1)`. -/
theorem Gamma_nat_add_three_half_mul_two_pow (m : ℕ) :
    Gamma ((m:ℂ)+3/2)*(2:ℂ)^m = Real.sqrt π/2*oddProduct m := by
  induction m with
  | zero =>
    have h := Complex.Gamma_add_one (1/2:ℂ) (by norm_num)
    rw [Gamma_one_half_eq_sqrt] at h
    norm_num [oddProduct] at h ⊢
    rw [h]; ring
  | succ m ih =>
    have hne : (m:ℂ)+3/2 ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    rw [show ((m+1:ℕ):ℂ)+3/2 = ((m:ℂ)+3/2)+1 by push_cast; ring, Complex.Gamma_add_one _ hne,
      oddProduct, Finset.prod_range_succ, ← oddProduct, pow_succ]
    rw [show ((m:ℂ)+3/2)*Gamma ((m:ℂ)+3/2)*((2:ℂ)^m*2) =
      (Gamma ((m:ℂ)+3/2)*(2:ℂ)^m)*(2*m+3) by ring, ih]
    push_cast
    ring

/-- The series with terms `(fun n : ℕ => (I*z)^n/Gamma ((n : ℂ)/2+1))` converges to `(faddeevaW
z)`. -/
@[dlmf 7.6.E3]
theorem hasSum_faddeevaW (z : ℂ) :
    HasSum (fun n : ℕ => (I*z)^n/Gamma ((n : ℂ)/2+1)) (faddeevaW z) := by
  obtain ⟨u, hu⟩ : ∃ u, u = I*z := ⟨_, rfl⟩
  simp_rw [← hu]
  have hz : -z^2 = u^2 := by rw [hu, mul_pow, I_sq]; ring
  have hev : HasSum (fun m : ℕ => u^(2*m)/Gamma (((2*m:ℕ) : ℂ)/2+1)) (exp (u^2)) := by
    have he := NormedSpace.expSeries_div_hasSum_exp (u^2)
    rw [← Complex.exp_eq_exp_ℂ] at he
    refine he.congr_fun fun m => ?_
    rw [show (((2*m:ℕ) : ℂ)/2+1) = (m:ℂ)+1 by push_cast; ring, Complex.Gamma_nat_eq_factorial,
      pow_mul]
  have h1 : exp (u^2)*exp (-u^2) = 1 := by rw [← Complex.exp_add]; simp
  have hπ : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hod : HasSum (fun m : ℕ => u^(2*m+1)/Gamma (((2*m+1:ℕ) : ℂ)/2+1)) (exp (u^2)*erf u) := by
    have h := (hasSum_erf_scaled u).mul_left (exp (u^2))
    refine h.congr_fun fun m => ?_
    have hG := Gamma_nat_add_three_half_mul_two_pow m
    have hG0 : Gamma ((m:ℂ)+3/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
      simp; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
    have hO : oddProduct m = 2*(Gamma ((m:ℂ)+3/2)*(2:ℂ)^m)/Real.sqrt π := by
      rw [hG]; field_simp
    have hr : exp (u^2)*(2/Real.sqrt π*exp (-u^2)*(2:ℂ)^m*u^(2*m+1)/oddProduct m) =
        (exp (u^2)*exp (-u^2))*(2/Real.sqrt π*(2:ℂ)^m*u^(2*m+1)/oddProduct m) := by ring
    rw [show (((2*m+1:ℕ) : ℂ)/2+1) = (m:ℂ)+3/2 by push_cast; ring, hr, h1, one_mul, hO]
    have h2 : (2:ℂ)^m ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp
  have h := HasSum.even_add_odd (f := fun n : ℕ => u^n/Gamma ((n:ℂ)/2+1)) hev hod
  convert h using 1
  rw [faddeevaW, hz, erfc, show -I*z = -u by rw [hu]; ring,
    show erf (-u) = -erf u by simp [erf]]
  ring

/-- Convergent auxiliary series of DLMF 7.6.5 and 7.6.7. -/
def fresnelAlternateSeries (odd : Bool) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ)^n*π^(2*n+if odd then 1 else 0)*z^(4*n+if odd then 3 else 1)/oddProduct (2*n+if odd then 1 else 0)

/-- The odd product dominates the factorial: `k! ≤ 1·3···(2k+1)`. -/
theorem factorial_le_norm_oddProduct (k : ℕ) : (k ! : ℝ) ≤ ‖oddProduct k‖ := by
  have he : oddProduct k = ((∏ j ∈ Finset.range (k+1), (2*j+1) : ℕ) : ℂ) := by
    simp [oddProduct]
  rw [he, Complex.norm_natCast]
  have h : k ! ≤ ∏ j ∈ Finset.range (k+1), (2*j+1) := by
    rw [Finset.prod_range_succ, ← Finset.prod_range_add_one_eq_factorial]
    calc ∏ x ∈ Finset.range k, (x+1) ≤ ∏ j ∈ Finset.range k, (2*j+1) := by
          exact Finset.prod_le_prod fun j _ => by omega
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  exact_mod_cast h

/-- The series with terms `(fun n : ℕ => (-1 : ℂ)^n*π^(2*n+if odd then 1 else 0)*z^(4*n+if odd
then 3 else 1)/oddProduct (2*n+if odd then 1 else 0))` is summable. -/
theorem fresnelAlternateSeries_summable (odd : Bool) (z : ℂ) :
    Summable (fun n : ℕ => (-1 : ℂ)^n*π^(2*n+if odd then 1 else 0)*z^(4*n+if odd then 3 else 1)/oddProduct (2*n+if odd then 1 else 0)) := by
  set e : ℕ := if odd then 1 else 0 with he
  have h4 : (4*· + if odd then 3 else 1) = fun n : ℕ => 2*(2*n+e)+1 := by
    funext n; cases odd <;> simp [he] <;> ring
  have hinj : Function.Injective (fun n : ℕ => 2*n+e) := by intro a b h; simp at h; omega
  have hs := ((Real.summable_pow_div_factorial (π*‖z‖^2)).comp_injective hinj).mul_left ‖z‖
  refine Summable.of_norm_bounded hs fun n => ?_
  have hk := factorial_le_norm_oddProduct (2*n+e)
  have hpos : (0:ℝ) < ((2*n+e) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hz : z^(4*n+if odd then 3 else 1) = z^(2*(2*n+e)+1) := by
    congr 1; cases odd <;> simp [he] <;> ring
  rw [hz]
  simp only [Function.comp_apply, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [mul_pow, ← pow_mul, pow_succ, show 2*(2*n+e) = (2*n+e)*2 by ring]
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hk)]
  calc π^(2*n+e)*(‖z‖^((2*n+e)*2)*‖z‖) = ‖z‖*(π^(2*n+e)*‖z‖^((2*n+e)*2)/((2*n+e) ! : ℝ))*((2*n+e) ! : ℝ) := by
        field_simp
    _ ≤ _ := by gcongr

/-- Signed combination of the Fresnel integrals as a modulated series:
`C(z) + iε S(z) = e^{iεπz²/2} (A(z) - iε B(z))` with `A`, `B` the alternate series. -/
theorem fresnel_signed_alternate (z : ℂ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    fresnelCosInt z+ε*I*fresnelSinInt z = exp (ε*I*(π*z^2/2))*
      (fresnelAlternateSeries false z-ε*I*fresnelAlternateSeries true z) := by
  have hε2 : (ε:ℂ)^2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hπ : (Real.sqrt π:ℂ)^2 = π := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hπ0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [fresnel_signed_erf z hε]
  set ζ := fresnelZetaComplex ε z with hζdef
  have hζ : ζ = Real.sqrt π/2*(1-ε*I)*z := rfl
  have hζ2 : ζ^2 = -(ε*π*I*z^2/2) := by
    rw [hζ, mul_pow, mul_pow, div_pow, hπ, sub_sq, mul_pow, I_sq, hε2]; ring
  set X : ℂ := -(ε*π*I)*z^2 with hX
  set c : ℕ → ℂ := fun n => (-(ε*π*I))^n*z^(2*n+1)/oddProduct n with hc
  set K : ℂ := exp (-(ε*I*(π*z^2/2)))*((1+ε*I)/2) with hK
  have hfull : HasSum c (K*erf ζ) := by
    have h := (hasSum_erf_scaled ζ).mul_left K
    refine h.congr_fun fun n => ?_
    have hE : exp (-(ε*I*(π*z^2/2)))*exp (-ζ^2) = 1 := by
      rw [← Complex.exp_add, hζ2]; ring_nf; simp
    have hz1 : (1+ε*I)/2*(2/Real.sqrt π)*ζ = z := by
      rw [hζ]; field_simp
      rw [show (1+ε*I)*(1-ε*I) = 1 - (ε:ℂ)^2*I^2 by ring, hε2, I_sq]; ring
    have hp : (2:ℂ)^n*ζ^(2*n+1) = ζ*X^n := by
      rw [pow_succ, pow_mul, hX, show -((ε:ℂ)*π*I)*z^2 = 2*ζ^2 by rw [hζ2]; ring, mul_pow]; ring
    have hr : c n = z*X^n/oddProduct n := by
      simp only [hc, hX]; rw [mul_pow, pow_succ, pow_mul]; ring
    rw [hr]
    simp only [hK]
    rw [show 2/(Real.sqrt π:ℂ)*exp (-ζ^2)*(2:ℂ)^n*ζ^(2*n+1)/oddProduct n =
      2/(Real.sqrt π:ℂ)*exp (-ζ^2)*((2:ℂ)^n*ζ^(2*n+1))/oddProduct n by ring, hp]
    linear_combination (-((1+ε*I)/2*(2/Real.sqrt π)*ζ*X^n/oddProduct n))*hE - (X^n/oddProduct n)*hz1
  have hA := (fresnelAlternateSeries_summable false z).hasSum
  have hB := ((fresnelAlternateSeries_summable true z).hasSum).mul_left (-(ε*I))
  have hsplit : HasSum c (fresnelAlternateSeries false z + -(ε*I)*fresnelAlternateSeries true z) := by
    refine HasSum.even_add_odd (f := c) ?_ ?_
    · refine hA.congr_fun fun m => ?_
      simp only [hc, Bool.false_eq_true, ite_false, add_zero]
      rw [pow_mul, show (-((ε:ℂ)*π*I))^2 = -(π^2) by
        rw [neg_sq, mul_pow, mul_pow, hε2, I_sq]; ring, neg_pow, pow_mul]
      congr 2; ring_nf
    · refine hB.congr_fun fun m => ?_
      simp only [hc, ite_true]
      rw [pow_succ, pow_mul, show (-((ε:ℂ)*π*I))^2 = -(π^2) by
        rw [neg_sq, mul_pow, mul_pow, hε2, I_sq]; ring, neg_pow, ← pow_mul]
      rw [show 2*(2*m+1)+1 = 4*m+3 by ring, show 2*m+1 = 2*m+1 from rfl]
      ring
  have heq := hfull.unique hsplit
  have hK0 : exp (ε*I*(π*z^2/2))*exp (-(ε*I*(π*z^2/2))) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [show fresnelAlternateSeries false z - ε*I*fresnelAlternateSeries true z =
    fresnelAlternateSeries false z + -(ε*I)*fresnelAlternateSeries true z by ring, ← heq]
  simp only [hK]
  linear_combination (-((1+ε*I)/2*erf ζ))*hK0

/-- Identity under the stated parameter and domain assumptions: `fresnelCosInt z=cos
(π*z^2/2)*fresnelAlternateSeries false z+sin (π*z^2/2)*fresnelAlternateSeries true z`. -/
@[dlmf 7.6.E5]
theorem fresnelCosInt_alternate_series (z : ℂ) :
    fresnelCosInt z=cos (π*z^2/2)*fresnelAlternateSeries false z+sin (π*z^2/2)*fresnelAlternateSeries true z := by
  have h1 := fresnel_signed_alternate z (Or.inl rfl)
  have h2 := fresnel_signed_alternate z (Or.inr rfl)
  push_cast at h1 h2
  rw [Complex.cos, Complex.sin]
  rw [show (-1:ℂ)*I*(π*z^2/2) = -((π:ℂ)*z^2/2)*I by ring] at h2
  rw [show (1:ℂ)*I*(π*z^2/2) = (π:ℂ)*z^2/2*I by ring] at h1
  linear_combination h1/2 + h2/2

/-- Identity under the stated parameter and domain assumptions: `fresnelSinInt z = -cos
(π*z^2/2)*fresnelAlternateSeries true z+sin (π*z^2/2)*fresnelAlternateSeries false z`. -/
@[dlmf 7.6.E7]
theorem fresnelSinInt_alternate_series (z : ℂ) :
    fresnelSinInt z = -cos (π*z^2/2)*fresnelAlternateSeries true z+sin (π*z^2/2)*fresnelAlternateSeries false z := by
  have h1 := fresnel_signed_alternate z (Or.inl rfl)
  have h2 := fresnel_signed_alternate z (Or.inr rfl)
  push_cast at h1 h2
  rw [Complex.cos, Complex.sin]
  rw [show (-1:ℂ)*I*(π*z^2/2) = -((π:ℂ)*z^2/2)*I by ring] at h2
  rw [show (1:ℂ)*I*(π*z^2/2) = (π:ℂ)*z^2/2*I by ring] at h1
  linear_combination (-I/2)*h1 + (I/2)*h2 + (fresnelSinInt z + (exp ((π:ℂ)*z^2/2*I) +
    exp (-((π:ℂ)*z^2/2)*I))*fresnelAlternateSeries true z/2)*I_sq

/-- The series with terms `(fun n : ℕ => 2*z/Real.sqrt π*(-1 : ℂ)^n*(sphericalI (2*n)
(z^2)-sphericalI (2*n+1) (z^2)))` converges to `(erf z)`. -/
@[dlmf 7.6.E8]
theorem erf_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => 2*z/Real.sqrt π*(-1 : ℂ)^n*(sphericalI (2*n) (z^2)-sphericalI (2*n+1) (z^2))) (erf z) := by
  set K : ℂ := 2/Real.sqrt π with hK
  have hA0 (w : ℂ) : HasDerivAt (fun w => w * sphericalI 0 (w^2))
      (cosh (w^2) + w^2 * sphericalI 1 (w^2)) w := by
    simpa using sphSeries_hasDerivAt_mul_sphericalI_zero_sq 1 w
  have hA (m : ℕ) (w : ℂ) : HasDerivAt (fun w => w * sphericalI (m+1) (w^2))
      (w^2 * (sphericalI m (w^2) + sphericalI (m+2) (w^2))) w := by
    simpa using sphSeries_hasDerivAt_mul_sphericalI_succ_sq 1 m w
  refine sphSeries_hasSum_of_hasDerivAt
    (f := fun n w => 2*w/Real.sqrt π*(-1 : ℂ)^n*(sphericalI (2*n) (w^2)-sphericalI (2*n+1) (w^2)))
    (g := fun n w => if n = 0 then K * exp (-w^2) else
      K * (-1)^n * (w^2 * (sphericalI (2*n-1) (w^2) - sphericalI (2*n) (w^2)))) (F := erf)
    (fun n w => ?_) (fun w => ?_) (fun R => ?_) (fun w => ?_) ?_ z
  · rcases n with _ | m
    · have h := ((hA0 w).sub (hA 0 w)).const_mul K
      have e : (fun w : ℂ => 2*w/Real.sqrt π*(-1 : ℂ)^0*(sphericalI (2*0) (w^2) -
          sphericalI (2*0+1) (w^2))) = fun w => K * (w * sphericalI 0 (w^2) -
          w * sphericalI (0+1) (w^2)) := by
        funext v; rw [hK]; simp only [pow_zero, mul_one, mul_zero, zero_add]; ring
      rw [e]
      refine h.congr_deriv ?_
      have hs := sphSeries_mul_sphericalI_zero (w^2)
      have hexp : exp (-w^2) = cosh (w^2) - sinh (w^2) := by
        rw [Complex.cosh, Complex.sinh]; ring
      simp only [ite_true]
      norm_num
      rw [hexp, ← hs]
      ring
    · have h := ((hA (2*m+1) w).sub (hA (2*m+2) w)).const_mul (K * (-1)^(m+1))
      have e : (fun w : ℂ => 2*w/Real.sqrt π*(-1 : ℂ)^(m+1)*(sphericalI (2*(m+1)) (w^2) -
          sphericalI (2*(m+1)+1) (w^2))) = fun w => K * (-1)^(m+1) *
          (w * sphericalI (2*m+1+1) (w^2) - w * sphericalI (2*m+2+1) (w^2)) := by
        funext v; rw [hK, show 2*(m+1) = 2*m+1+1 by ring, show 2*m+1+1+1 = 2*m+2+1 by ring]; ring
      rw [e]
      refine h.congr_deriv ?_
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
      rw [show 2*(m+1)-1 = 2*m+1 by omega, show 2*(m+1+1)-1 = 2*m+1+2 by omega,
        show 2*(m+1) = 2*m+2 by ring, show 2*(m+1+1) = 2*m+2+2 by ring]
      ring
  · rw [← tendsto_add_atTop_iff_nat 1]
    have hx : Tendsto (fun n : ℕ => K * (w^2 * (sphericalI (2*n+1) (w^2) -
        sphericalI (2*n+2) (w^2)))) atTop (𝓝 0) := by
      have h1 := (sphSeries_tendsto_sphericalI (w^2)).comp
        (tendsto_atTop_mono (fun n => (by omega : n ≤ 2*n+1)) tendsto_id)
      have h2 := (sphSeries_tendsto_sphericalI (w^2)).comp
        (tendsto_atTop_mono (fun n => (by omega : n ≤ 2*n+2)) tendsto_id)
      simpa using ((h1.sub h2).const_mul (w^2)).const_mul K
    refine squeeze_zero_norm (fun n => le_of_eq ?_) (tendsto_norm_zero.comp hx)
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Function.comp_apply,
      show 2*(n+1) = 2*n+2 by ring, show 2*n+2-1 = 2*n+1 by omega]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
  · obtain ⟨u, hu, h1⟩ := sphSeries_bound_mul_sphericalI_sq 1 (σ := fun n => 2*n)
      (fun a b h => by simp only at h; omega) R
    obtain ⟨v, hv, h2⟩ := sphSeries_bound_mul_sphericalI_sq 1 (σ := fun n => 2*n+1)
      (fun a b h => by simp only at h; omega) R
    refine ⟨fun n => ‖K‖ * (u n + v n), (hu.add hv).mul_left _, fun n w hw => ?_⟩
    have e : 2*w/Real.sqrt π*(-1 : ℂ)^n*(sphericalI (2*n) (w^2) - sphericalI (2*n+1) (w^2)) =
        K * (-1)^n * (w * sphericalI (2*n) (1*w^2) - w * sphericalI (2*n+1) (1*w^2)) := by
      rw [hK]; simp only [one_mul]; ring
    simp only
    rw [e, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
    gcongr
    exact (norm_sub_le _ _).trans (add_le_add (h1 n w hw) (h2 n w hw))
  · simpa [hK] using hasDerivAt_erf_complex w
  · simp [erf_zero]

open Polynomial.Chebyshev in
/-- Crude growth bound for Chebyshev polynomials of the first kind:
`‖Tₘ(b)‖ ≤ (2‖b‖+1)^m`. -/
theorem erfCheb_norm_T_le (m : ℕ) (b : ℂ) :
    ‖(T ℂ m).eval b‖ ≤ (2*‖b‖+1)^m := by
  have key : ∀ m : ℕ, ‖(T ℂ m).eval b‖ ≤ (2*‖b‖+1)^m ∧
      ‖(T ℂ (m+1 : ℕ)).eval b‖ ≤ (2*‖b‖+1)^(m+1) := by
    intro m
    induction m with
    | zero => simp; linarith [norm_nonneg b]
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have h := T_add_two ℂ (m : ℤ)
      have e : ((m+1+1 : ℕ) : ℤ) = (m:ℤ) + 2 := by push_cast; ring
      have e1 : ((m+1 : ℕ) : ℤ) = (m:ℤ) + 1 := by push_cast; ring
      rw [e, h]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      have h1 := ih.1
      have h2 := ih.2
      rw [e1] at h2
      have hc : 1 ≤ 2*‖b‖+1 := by linarith [norm_nonneg b]
      calc ‖2*b*(T ℂ ((m:ℤ)+1)).eval b - (T ℂ (m:ℤ)).eval b‖
          ≤ 2*‖b‖*‖(T ℂ ((m:ℤ)+1)).eval b‖ + ‖(T ℂ (m:ℤ)).eval b‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul]; norm_num
        _ ≤ 2*‖b‖*(2*‖b‖+1)^(m+1) + (2*‖b‖+1)^(m+1) := by
            gcongr
            exact h1.trans (pow_le_pow_right₀ hc (Nat.le_succ m))
        _ = _ := by ring
  exact (key m).1

open Polynomial.Chebyshev in
/-- Crude growth bound for Chebyshev polynomials of the second kind:
`‖Uₘ(b)‖ ≤ (2‖b‖+1)^m`. -/
theorem erfCheb_norm_U_le (m : ℕ) (b : ℂ) :
    ‖(U ℂ m).eval b‖ ≤ (2*‖b‖+1)^m := by
  have key : ∀ m : ℕ, ‖(U ℂ m).eval b‖ ≤ (2*‖b‖+1)^m ∧
      ‖(U ℂ (m+1 : ℕ)).eval b‖ ≤ (2*‖b‖+1)^(m+1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have h := U_add_two ℂ (m : ℤ)
      have e : ((m+1+1 : ℕ) : ℤ) = (m:ℤ) + 2 := by push_cast; ring
      have e1 : ((m+1 : ℕ) : ℤ) = (m:ℤ) + 1 := by push_cast; ring
      rw [e, h]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      have h1 := ih.1
      have h2 := ih.2
      rw [e1] at h2
      have hc : 1 ≤ 2*‖b‖+1 := by linarith [norm_nonneg b]
      calc ‖2*b*(U ℂ ((m:ℤ)+1)).eval b - (U ℂ (m:ℤ)).eval b‖
          ≤ 2*‖b‖*‖(U ℂ ((m:ℤ)+1)).eval b‖ + ‖(U ℂ (m:ℤ)).eval b‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul]; norm_num
        _ ≤ 2*‖b‖*(2*‖b‖+1)^(m+1) + (2*‖b‖+1)^(m+1) := by
            gcongr
            exact h1.trans (pow_le_pow_right₀ hc (Nat.le_succ m))
        _ = _ := by ring
  exact (key m).1

/-- `ρᵏ ‖iₖ(w)‖` is summable for every `ρ ≥ 0`. -/
theorem erfCheb_summable_pow_mul_sphericalI {ρ : ℝ} (hρ : 0 ≤ ρ) (w : ℂ) :
    Summable (fun k : ℕ => ρ^k * ‖sphericalI k w‖) := by
  have hs := (sphSeries_summable_bound (mul_nonneg hρ (norm_nonneg w))).mul_left
    (Real.exp (‖w‖^2/4) / Real.exp ((ρ*‖w‖)^2/4))
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs
  have hG : 0 < Real.Gamma ((k:ℝ) + 3/2) := Real.Gamma_pos_of_pos (by positivity)
  refine (mul_le_mul_of_nonneg_left (sphSeries_norm_sphericalI_le k w) (by positivity)).trans
    (le_of_eq ?_)
  have he : (0:ℝ) < Real.exp ((ρ*‖w‖)^2/4) := Real.exp_pos _
  field_simp
  ring

open Polynomial.Chebyshev in
/-- DLMF 7.6.9 for every complex `b`, with the Chebyshev polynomials evaluated at `b`.
Stronger than DLMF: valid for all complex `b`, not only `-1 ≤ b ≤ 1`. The termwise derivative in
`b` telescopes by `T'_{2n+1} = (2n+1) U_{2n}`, `U_{2n+4} - U_{2n} = 4b T_{2n+3}` and the
recurrence of `iₙ`. -/
@[dlmf 7.6.E9]
theorem erfCheb_hasSum (z b : ℂ) :
    HasSum (fun n : ℕ => 2*z/Real.sqrt π*exp ((1/2-b^2)*z^2)*(T ℂ (2*n+1 : ℤ)).eval b*
      sphericalI n (z^2/2)) (erf (b*z)) := by
  set w : ℂ := z^2/2 with hw
  set K : ℂ := 2*z/Real.sqrt π with hK
  have hz2 : z^2 = 2*w := by rw [hw]; ring
  set g : ℕ → ℂ → ℂ := fun n c => K*exp ((1/2-c^2)*z^2)*
    (if n = 0 then exp (-w) else
      w*(sphericalI (n-1) w*(U ℂ (2*n : ℤ)).eval c + sphericalI n w*(U ℂ (2*n-2 : ℤ)).eval c))
    with hg
  have hE : ∀ c : ℂ, HasDerivAt (fun c => exp ((1/2-c^2)*z^2))
      (exp ((1/2-c^2)*z^2)*(-(2*c)*z^2)) c := by
    intro c
    have h := (((hasDerivAt_pow 2 c).const_sub (1/2:ℂ)).mul_const (z^2)).cexp
    convert h using 1
    simp
  refine sphSeries_hasSum_of_hasDerivAt (g := g)
    (f := fun n c => K*exp ((1/2-c^2)*z^2)*(T ℂ (2*n+1 : ℤ)).eval c*sphericalI n w)
    (F := fun c => erf (c*z)) (fun n c => ?_) (fun c => ?_) (fun R => ?_)
    (fun c => ?_) ?_ b
  · -- termwise derivative telescopes
    have hT := Polynomial.hasDerivAt (T ℂ (2*n+1 : ℤ)) c
    rw [T_derivative_eq_U] at hT
    have h := ((hE c).const_mul K).mul hT
    have h2 := h.mul_const (sphericalI n w)
    refine h2.congr_deriv ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_intCast, hg]
    have hU : (U ℂ ((2*n+1 : ℤ) - 1)) = U ℂ (2*n : ℤ) := congrArg (U ℂ) (by ring)
    rw [hU]
    generalize exp ((1/2-c^2)*z^2) = E
    rcases n with _ | m
    · simp only [↓reduceIte, Nat.add_one_ne_zero]
      have h0 := sphSeries_mul_sphericalI_zero w
      have h1 := sphSeries_sphericalI_zero_add w
      have hc : exp (-w) = cosh w - sinh w := by
        rw [Complex.cosh, Complex.sinh]; ring
      simp only [Nat.cast_zero, Nat.cast_one, mul_zero, zero_add, mul_one,
        sub_self, Int.cast_one, T_one, U_zero, U_two, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat, Nat.sub_self]
      rw [hz2, hc]
      linear_combination (-K*E)*(h0 + w*h1 - h1) + z^3*(Real.sqrt π:ℂ)⁻¹*E*h1
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      have hr := sphSeries_sphericalI_recurrence m w
      have hp : (U ℂ (2*(m:ℤ)+2+2)).eval c - (U ℂ (2*(m:ℤ))).eval c =
          4*c*(T ℂ (2*(m:ℤ)+2+1)).eval c := by
        have e1' := congrArg (Polynomial.eval c) (two_mul_T_eq_U_sub_U ℂ (2*(m:ℤ)+2))
        have e2' := congrArg (Polynomial.eval c) (two_mul_T_eq_U_sub_U ℂ (2*(m:ℤ)))
        have e3' := congrArg (Polynomial.eval c) (T_add_two ℂ (2*(m:ℤ)+2))
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_ofNat] at e1' e2' e3'
        linear_combination -e1' - e2' + 2*e3'
      push_cast
      have r1 : U ℂ (2*((m:ℤ)+1+1)) = U ℂ (2*(m:ℤ)+2+2) :=
        congrArg (U ℂ) (by ring)
      have r2 : U ℂ (2*((m:ℤ)+1+1)-2) = U ℂ (2*(m:ℤ)+2) :=
        congrArg (U ℂ) (by ring)
      have r3 : U ℂ (2*((m:ℤ)+1)-2) = U ℂ (2*(m:ℤ)) :=
        congrArg (U ℂ) (by ring)
      have r4 : U ℂ (2*((m:ℤ)+1)) = U ℂ (2*(m:ℤ)+2) :=
        congrArg (U ℂ) (by ring)
      have r5 : T ℂ (2*((m:ℤ)+1)+1) = T ℂ (2*(m:ℤ)+2+1) :=
        congrArg (T ℂ) (by ring)
      rw [r1, r2, r3, r4, r5]
      rw [hz2]
      linear_combination (K*E)*(-(U ℂ (2*(m:ℤ)+2)).eval c*hr + w*sphericalI (m+1) w*hp)
  · -- `gₙ → 0`
    set ρ : ℝ := (2*‖c‖+1)^2 with hρ
    have hρ1 : 1 ≤ ρ := one_le_pow₀ (by linarith [norm_nonneg c])
    have ha := (erfCheb_summable_pow_mul_sphericalI (by positivity : (0:ℝ) ≤ ρ) w).tendsto_atTop_zero
    have ha1 := ha.comp (tendsto_add_atTop_nat 1)
    rw [← tendsto_add_atTop_iff_nat 1]
    have hlim : Tendsto (fun n : ℕ => ‖K*exp ((1/2-c^2)*z^2)*w‖ *
        (ρ*(ρ^n*‖sphericalI n w‖) + ρ^(n+1)*‖sphericalI (n+1) w‖)) atTop (𝓝 0) := by
      simpa using ((ha.const_mul ρ).add ha1).const_mul ‖K*exp ((1/2-c^2)*z^2)*w‖
    refine squeeze_zero_norm (fun n => ?_) hlim
    simp only [hg, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
    have e1 : (2*((n+1:ℕ):ℤ) : ℤ) = ((2*n+2 : ℕ) : ℤ) := by push_cast; ring
    have e2 : (2*((n+1:ℕ):ℤ) - 2 : ℤ) = ((2*n : ℕ) : ℤ) := by push_cast; ring
    rw [e2, e1]
    have hU1 := erfCheb_norm_U_le (2*n+2) c
    have hU2 := erfCheb_norm_U_le (2*n) c
    have p1 : (2*‖c‖+1)^(2*n+2) = ρ*ρ^n := by rw [hρ, ← pow_mul, ← pow_add]; ring_nf
    have p2 : (2*‖c‖+1)^(2*n) = ρ^n := by rw [hρ, ← pow_mul]
    have p3 : ρ^n ≤ ρ^(n+1) := pow_le_pow_right₀ hρ1 (Nat.le_succ n)
    rw [p1] at hU1
    rw [p2] at hU2
    rw [show K*exp ((1/2-c^2)*z^2)*(w*(sphericalI n w*(U ℂ ((2*n+2:ℕ):ℤ)).eval c +
        sphericalI (n+1) w*(U ℂ ((2*n:ℕ):ℤ)).eval c)) = K*exp ((1/2-c^2)*z^2)*w*
        (sphericalI n w*(U ℂ ((2*n+2:ℕ):ℤ)).eval c +
        sphericalI (n+1) w*(U ℂ ((2*n:ℕ):ℤ)).eval c) by ring, norm_mul _ (_ + _)]
    gcongr
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      calc ‖sphericalI n w‖*‖(U ℂ ((2*n+2:ℕ):ℤ)).eval c‖ ≤ ‖sphericalI n w‖*(ρ*ρ^n) := by gcongr
        _ = _ := by ring
    · rw [norm_mul]
      calc ‖sphericalI (n+1) w‖*‖(U ℂ ((2*n:ℕ):ℤ)).eval c‖ ≤ ‖sphericalI (n+1) w‖*ρ^(n+1) := by
            gcongr; exact hU2.trans p3
        _ = _ := by ring
  · -- uniform bounds on balls
    set r : ℝ := 2*|R|+1 with hr
    have hr1 : 1 ≤ r := by linarith [abs_nonneg R]
    refine ⟨fun n => ‖K‖*Real.exp ((1/2+R^2)*‖z‖^2)*r*((r^2)^n*‖sphericalI n w‖),
      ((erfCheb_summable_pow_mul_sphericalI (by positivity : (0:ℝ) ≤ r^2) w).mul_left _),
      fun n c hc => ?_⟩
    have hcR : ‖c‖ ≤ |R| := hc.le.trans (le_abs_self R)
    have hT := erfCheb_norm_T_le (2*n+1) c
    have e : ((2*n+1 : ℕ) : ℤ) = (2*n+1 : ℤ) := by push_cast; ring
    rw [e] at hT
    have hT' : ‖(T ℂ (2*n+1 : ℤ)).eval c‖ ≤ r*(r^2)^n := by
      refine hT.trans ?_
      rw [← pow_mul, ← pow_succ']
      gcongr
      rw [hr]; linarith
    have hE : ‖exp ((1/2-c^2)*z^2)‖ ≤ Real.exp ((1/2+R^2)*‖z‖^2) := by
      refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, norm_pow]
      gcongr
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow]
      have : ‖c‖^2 ≤ R^2 := by
        rw [← sq_abs R]; exact pow_le_pow_left₀ (norm_nonneg c) hcR 2
      norm_num; linarith
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖K‖*‖exp ((1/2-c^2)*z^2)‖*‖(T ℂ (2*n+1 : ℤ)).eval c‖*‖sphericalI n w‖
        ≤ ‖K‖*Real.exp ((1/2+R^2)*‖z‖^2)*(r*(r^2)^n)*‖sphericalI n w‖ := by gcongr
      _ = _ := by ring
  · -- derivative of `erf (b z)`
    have h := ((hasDerivAt_erf_complex (c*z)).comp c ((hasDerivAt_id c).mul_const z))
    convert h using 1
    · funext c; simp
    rw [hg]
    simp only [↓reduceIte]
    rw [mul_assoc, ← Complex.exp_add, hK, hw]
    ring_nf
  · -- value at the origin
    have h0 : ∀ n : ℕ, (T ℂ (2*n+1 : ℤ)).eval 0 = 0 := fun n =>
      T_eval_zero_of_odd ℂ ⟨n, rfl⟩
    simp only [h0, mul_zero, zero_mul, erf_zero]
    exact hasSum_zero

/-- The series with terms `(fun n : ℕ => 2*z/Real.sqrt π*exp ((1/2-(a :
ℂ)^2)*z^2)*(Polynomial.Chebyshev.T ℝ (2*n+1 : ℤ)).eval a*sphericalI n (z^2/2))` converges to
`(erf (a*z))`. -/
@[dlmf 7.6.E9]
theorem erf_chebyshev_spherical_series {a : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1) (z : ℂ) :
    HasSum (fun n : ℕ => 2*z/Real.sqrt π*exp ((1/2-(a : ℂ)^2)*z^2)*(Polynomial.Chebyshev.T ℝ (2*n+1 : ℤ)).eval a*sphericalI n (z^2/2)) (erf (a*z)) := by
  have hT : ∀ m : ℤ, (((Polynomial.Chebyshev.T ℝ m).eval a : ℝ) : ℂ) =
      (Polynomial.Chebyshev.T ℂ m).eval (a:ℂ) := by
    intro m
    rw [← Polynomial.Chebyshev.map_T Complex.ofRealHom m, Polynomial.eval_map,
      show (a:ℂ) = Complex.ofRealHom a from rfl, Polynomial.eval₂_at_apply]
    rfl
  simpa only [hT] using erfCheb_hasSum z a

/-- The series with terms `(fun n : ℕ => z*sphericalJ (2*n+0) (π*z^2/2))` converges to
`(fresnelCosInt z)`. -/
@[dlmf 7.6.E10]
theorem fresnelCosInt_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => z*sphericalJ (2*n+0) (π*z^2/2)) (fresnelCosInt z) := by
  obtain ⟨p, hp⟩ : ∃ p : ℂ, p = π/2 := ⟨_, rfl⟩
  have key := sphSeries_hasSum_of_hasDerivAt
    (f := fun n w => w * sphericalJ (2*n) (p*w^2))
    (g := fun n w => if n = 0 then cos (p*w^2) else p*w^2 * sphericalJ (2*n-1) (p*w^2))
    (F := fresnelCosInt)
    (fun n w => by
      rcases n with _ | n
      · simpa using sphSeries_hasDerivAt_mul_sphericalJ_zero_sq p w
      · have h := sphSeries_hasDerivAt_mul_sphericalJ_succ_sq p (2*n+1) w
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
        rw [show 2*(n+1) = 2*n+1+1 by ring, show 2*n+1+1-1 = 2*n+1 by omega,
          show 2*(n+1+1)-1 = 2*n+1+2 by omega, ← mul_sub]
        exact h)
    (fun w => by
      rw [← tendsto_add_atTop_iff_nat 1]
      have h := ((sphSeries_tendsto_sphericalJ (p*w^2)).comp
        (tendsto_atTop_mono (fun n => (by omega : n ≤ 2*n+1)) tendsto_id)).const_mul (p*w^2)
      simpa [Function.comp_def, show ∀ n : ℕ, 2*(n+1)-1 = 2*n+1 from fun n => by omega] using h)
    (fun R => sphSeries_bound_mul_sphericalJ_sq p (σ := fun n => 2*n)
      (fun a b h => by simp only at h; omega) R)
    (fun w => by
      have h := hasDerivAt_primitive (f := fun t => cos (π*t^2/2)) (by fun_prop) w
      simp only [ite_true]
      rw [show fresnelCosInt = primitive (fun t => cos (π*t^2/2)) from rfl]
      convert h using 2
      rw [hp]; ring)
    (by simp [fresnelCosInt, primitive, segmentIntegral]) z
  convert key using 3 with n
  · rw [hp]; congr 1; ring

/-- The series with terms `(fun n : ℕ => z*sphericalJ (2*n+1) (π*z^2/2))` converges to
`(fresnelSinInt z)`. -/
@[dlmf 7.6.E11]
theorem fresnelSinInt_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => z*sphericalJ (2*n+1) (π*z^2/2)) (fresnelSinInt z) := by
  obtain ⟨p, hp⟩ : ∃ p : ℂ, p = π/2 := ⟨_, rfl⟩
  have key := sphSeries_hasSum_of_hasDerivAt
    (f := fun n w => w * sphericalJ (2*n+1) (p*w^2))
    (g := fun n w => p*w^2 * sphericalJ (2*n) (p*w^2)) (F := fresnelSinInt)
    (fun n w => by
      have h := sphSeries_hasDerivAt_mul_sphericalJ_succ_sq p (2*n) w
      rwa [show 2*n+2 = 2*(n+1) by ring, mul_sub] at h)
    (fun w => by
      have h := ((sphSeries_tendsto_sphericalJ (p*w^2)).comp
        (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))).const_mul (p*w^2)
      simpa [Function.comp_def] using h)
    (fun R => sphSeries_bound_mul_sphericalJ_sq p (σ := fun n => 2*n+1)
      (fun a b h => by simp only at h; omega) R)
    (fun w => by
      have h := hasDerivAt_primitive (f := fun t => sin (π*t^2/2)) (by fun_prop) w
      simp only [mul_zero, sphSeries_mul_sphericalJ_zero]
      rw [show fresnelSinInt = primitive (fun t => sin (π*t^2/2)) from rfl]
      convert h using 2
      rw [hp]; ring)
    (by simp [fresnelSinInt, primitive, segmentIntegral]) z
  convert key using 3 with n
  · rw [hp]; congr 1; ring

end DLMF.Confluent
