/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Recurrences
public import DLMF.Hypergeometric.AnalyticProperties

/-!
# Ferrers functions (Temme §8.7; DLMF §§14.2, 14.3, 14.6)

The Ferrers function `𝖯^μ_ν(x) = ((1+x)/(1-x))^{μ/2} 𝐅(ν+1, -ν; 1-μ; (1-x)/2)` on `(-1, 1)`
(DLMF 14.3.1) satisfies the associated Legendre equation for all complex `ν, μ`. At integer order
`m` it is `(-1)ᵐ (1-x²)^{m/2} P_ν⁽ᵐ⁾(x)` (DLMF 14.6.1), from DLMF 15.2.3_5 for `𝐅` at `c = 1-m`,
lifted here to the cut plane.
-/

@[expose] public section

open Complex Filter Set DLMF.Hypergeometric
open scoped Topology Real

noncomputable section

namespace DLMF.Hypergeometric

/-- DLMF 15.2.3_5 on the cut plane: `𝐅(a,b;-n;z) = (a)ₙ₊₁ (b)ₙ₊₁ zⁿ⁺¹ 𝐅(a+n+1,b+n+1;n+2;z)`. -/
@[dlmf 15.2.E3_5]
theorem regularizedGaussHG_neg_nat (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHG a b (-n) z = poch a (n + 1) * poch b (n + 1) * z ^ (n + 1) *
      regularizedGaussHG (a + n + 1) (b + n + 1) (n + 2) z := by
  refine eqOn_cutPlane_of_eqOn_disk (f := regularizedGaussHG a b (-n))
    (g := fun z => poch a (n + 1) * poch b (n + 1) * z ^ (n + 1) *
      regularizedGaussHG (a + n + 1) (b + n + 1) (n + 2) z)
    (analyticOnNhd_regularizedGaussHG _ _ _)
    (by intro z hz; fun_prop (disch := assumption)) (fun z hz => ?_) hz
  have hc : ∀ k : ℕ, ((n : ℂ) + 2) ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz,
      regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz,
    regularized_at_neg_nat a b n hz, regularizedGaussHGFun_eq_div_Gamma hc,
    show (n : ℂ) + 2 = ((n + 1 : ℕ) : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  push_cast
  ring

end DLMF.Hypergeometric

namespace DLMF.Legendre

/-- At `μ = 0` the Ferrers function is `P_ν` on `(-1, 1)`. -/
theorem ferrersP_zero (ν : ℂ) {x : ℝ} (hx : -1 < x) : ferrersP ν 0 x = legendreP ν x := by
  have hs : 1 + (x : ℂ) ∈ slitPlane := Or.inl (by simp; linarith)
  rw [ferrersP, legendreP, zero_div, cpow_zero, one_mul, sub_zero,
    regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add hs)]

/-- For integer order, `𝖯^m_ν(x) = (-1)ᵐ (1-x²)^{m/2} dᵐP_ν(x)/dxᵐ` (DLMF 14.6.1). -/
@[dlmf 14.6.E1]
theorem ferrersP_nat (ν : ℂ) (m : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ferrersP ν m x = (-1) ^ m * (((1 - x ^ 2) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
      iteratedDeriv m (legendreP ν) x := by
  have hs : 1 + (x : ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  have hw := mem_cutPlane_of_one_add hs
  rw [iteratedDeriv_legendreP ν m hs]
  rcases m with _ | m
  · simp [ferrersP_zero ν hx.1, legendreP, poch_zero]
  have h1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
  have h2 : (0 : ℝ) < 1 - x := by linarith [hx.2]
  set k : ℕ := m + 1 with hk
  have hreal : ((1 + x) / (1 - x)) ^ ((k : ℝ) / 2) * ((1 - x) / 2) ^ k =
      (1 - x ^ 2) ^ ((k : ℝ) / 2) / 2 ^ k := by
    rw [Real.div_rpow h1.le h2.le, show 1 - x ^ 2 = (1 + x) * (1 - x) by ring,
      Real.mul_rpow h1.le h2.le, div_pow]
    have hsq : (1 - x) ^ k = (1 - x) ^ ((k : ℝ) / 2) * (1 - x) ^ ((k : ℝ) / 2) := by
      rw [← Real.rpow_add h2, add_halves, Real.rpow_natCast]
    have hpos : 0 < (1 - x) ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos h2 _
    rw [hsq]
    field_simp
  have hwc : ((((1 - x) / 2 : ℝ)) : ℂ) ∈ cutPlane := by push_cast; exact hw
  rw [ferrersP, show (1 : ℂ) - (k : ℕ) = -(m : ℂ) by rw [hk]; push_cast; ring,
    regularizedGaussHG_neg_nat _ _ _ hw, regularizedGaussHG_symm (-ν + (k : ℕ)) _ _ hw]
  have hc : (((1 + x) / (1 - x) : ℝ) : ℂ) ^ (((k : ℕ) : ℂ) / 2) =
      (((1 + x) / (1 - x)) ^ ((k : ℝ) / 2) : ℝ) := by
    rw [ofReal_cpow (by positivity)]; push_cast; ring_nf
  have hreal' := congrArg (fun r : ℝ => (r : ℂ)) hreal
  push_cast at hreal'
  rw [hc]
  have hkc : ((k : ℕ) : ℂ) = (m : ℂ) + 1 := by rw [hk]; push_cast; ring
  rw [hkc, show ν + 1 + ((m : ℂ) + 1) = ν + 1 + m + 1 by ring,
    show -ν + ((m : ℂ) + 1) = -ν + m + 1 by ring, show (1 : ℂ) + ((m : ℂ) + 1) = m + 2 by ring]
  rw [← hk]
  have hneg : ((-1 : ℂ)) ^ k * (-1 / 2) ^ k = 1 / 2 ^ k := by
    rw [← mul_pow, one_div, ← inv_pow]; norm_num
  linear_combination (poch (ν + 1) k * poch (-ν) k *
    regularizedGaussHG (ν + 1 + m + 1) (-ν + m + 1) (m + 2) ((1 - (x : ℂ)) / 2)) * hreal' -
    (((1 - x ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * poch (ν + 1) k * poch (-ν) k *
    regularizedGaussHG (ν + 1 + m + 1) (-ν + m + 1) (m + 2) ((1 - (x : ℂ)) / 2) * hneg

/-- Chain rule for `x ↦ ((1+x)/(1-x))^p 𝐅(a,b;c;(1-x)/2)` on `(-1, 1)`. -/
theorem hasDerivAt_ferrers_aux (a b c p : ℂ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => (((1 + x) / (1 - x) : ℝ) : ℂ) ^ p *
        regularizedGaussHG a b c ((1 - (x : ℂ)) / 2))
      ((((1 + x) / (1 - x) : ℝ) : ℂ) ^ p *
        (p * (2 / (1 - (x : ℂ) ^ 2)) * regularizedGaussHG a b c ((1 - (x : ℂ)) / 2) -
          1 / 2 * (a * b * regularizedGaussHG (a + 1) (b + 1) (c + 1) ((1 - (x : ℂ)) / 2)))) x := by
  have h1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
  have h2 : (0 : ℝ) < 1 - x := by linarith [hx.2]
  have hs : 1 + (x : ℂ) ∈ slitPlane := Or.inl (by simp; linarith)
  have hr0 : HasDerivAt (fun x : ℝ => (1 + x) / (1 - x)) _ x :=
    ((hasDerivAt_id x).const_add 1).div ((hasDerivAt_id x).const_sub 1) h2.ne'
  have hr : HasDerivAt (fun x : ℝ => (1 + x) / (1 - x)) (2 / (1 - x) ^ 2) x :=
    hr0.congr_deriv (by simp; ring)
  have hpos : 0 < (1 + x) / (1 - x) := div_pos h1 h2
  have hφ := (hasStrictDerivAt_cpow_const (c := p)
    (show (((1 + x) / (1 - x) : ℝ) : ℂ) ∈ slitPlane from
      Or.inl (by rw [ofReal_re]; exact hpos))).hasDerivAt.comp x hr.ofReal_comp
  have hG := (hasDerivAt_regularizedGaussHG_half a b c hs).comp_ofReal
  refine (hφ.mul hG).congr_deriv ?_
  have hne : (((1 + x) / (1 - x) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpos.ne'
  rw [cpow_sub _ _ hne, cpow_one]
  have h1' : (1 + (x : ℂ)) ≠ 0 := by exact_mod_cast h1.ne'
  have h2' : (1 - (x : ℂ)) ≠ 0 := by exact_mod_cast h2.ne'
  have h3 : (1 - (x : ℂ) ^ 2) ≠ 0 := by
    rw [show (1 - (x : ℂ) ^ 2) = (1 + x) * (1 - x) by ring]; exact mul_ne_zero h1' h2'
  simp only [Function.comp]
  generalize (((1 + x) / (1 - x) : ℝ) : ℂ) ^ p = A
  generalize regularizedGaussHG a b c ((1 - (x : ℂ)) / 2) = G0
  generalize regularizedGaussHG (a + 1) (b + 1) (c + 1) ((1 - (x : ℂ)) / 2) = G1
  push_cast
  field_simp
  ring

/-- The associated Legendre equation for the Ferrers function on `(-1, 1)` (DLMF 14.2.1). -/
@[dlmf 14.2.E1]
theorem ferrersP_ode (ν μ : ℂ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 - (x : ℂ) ^ 2) * iteratedDeriv 2 (ferrersP ν μ) x - 2 * x * deriv (ferrersP ν μ) x +
      (ν * (ν + 1) - μ ^ 2 / (1 - (x : ℂ) ^ 2)) * ferrersP ν μ x = 0 := by
  set a := ν + 1
  set b := -ν
  set c := 1 - μ
  set s := μ / 2
  have hO : IsOpen (Set.Ioo (-1 : ℝ) 1) := isOpen_Ioo
  have hq (y : ℝ) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
      HasDerivAt (fun y : ℝ => 2 * s * (1 - (y : ℂ) ^ 2)⁻¹)
        (2 * s * (2 * y / (1 - (y : ℂ) ^ 2) ^ 2)) y := by
    have hne : (1 - (y : ℂ) ^ 2) ≠ 0 := by
      rw [show (1 - (y : ℂ) ^ 2) = ((1 - y ^ 2 : ℝ) : ℂ) by push_cast; ring, ofReal_ne_zero]
      nlinarith [hy.1, hy.2]
    have h := (((hasDerivAt_id y).ofReal_comp.pow 2).const_sub 1).inv hne
    refine (h.const_mul (2 * s)).congr_deriv ?_
    simp
  have hev : deriv (ferrersP ν μ) =ᶠ[𝓝 x] fun y =>
      2 * s * (1 - (y : ℂ) ^ 2)⁻¹ *
          ((((1 + y) / (1 - y) : ℝ) : ℂ) ^ s * regularizedGaussHG a b c ((1 - (y : ℂ)) / 2)) -
        a * b / 2 * ((((1 + y) / (1 - y) : ℝ) : ℂ) ^ s *
          regularizedGaussHG (a + 1) (b + 1) (c + 1) ((1 - (y : ℂ)) / 2)) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    have hy' : HasDerivAt (ferrersP ν μ) _ y := hasDerivAt_ferrers_aux a b c s hy
    rw [hy'.deriv]
    ring
  have h2 := ((hq x hx).mul (hasDerivAt_ferrers_aux a b c s hx)).sub
    ((hasDerivAt_ferrers_aux (a + 1) (b + 1) (c + 1) s hx).const_mul (a * b / 2))
  have h2' : HasDerivAt (fun y : ℝ =>
      2 * s * (1 - (y : ℂ) ^ 2)⁻¹ *
          ((((1 + y) / (1 - y) : ℝ) : ℂ) ^ s * regularizedGaussHG a b c ((1 - (y : ℂ)) / 2)) -
        a * b / 2 * ((((1 + y) / (1 - y) : ℝ) : ℂ) ^ s *
          regularizedGaussHG (a + 1) (b + 1) (c + 1) ((1 - (y : ℂ)) / 2))) _ x := h2
  have hf : ferrersP ν μ x = (((1 + x) / (1 - x) : ℝ) : ℂ) ^ s *
      regularizedGaussHG a b c ((1 - (x : ℂ)) / 2) := rfl
  have hx' : HasDerivAt (ferrersP ν μ) _ x := hasDerivAt_ferrers_aux a b c s hx
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, h2'.deriv, hx'.deriv, hf]
  have hs : 1 + (x : ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  have hode := regularizedGaussHG_ode a b c (mem_cutPlane_of_one_add hs)
  simp only [poch, ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one] at hode
  rw [show a + 1 + 1 = a + 2 by ring, show b + 1 + 1 = b + 2 by ring,
    show c + 1 + 1 = c + 2 by ring]
  generalize (((1 + x) / (1 - x) : ℝ) : ℂ) ^ s = A
  generalize regularizedGaussHG a b c ((1 - (x : ℂ)) / 2) = G0 at *
  generalize regularizedGaussHG (a + 1) (b + 1) (c + 1) ((1 - (x : ℂ)) / 2) = G1 at *
  generalize regularizedGaussHG (a + 2) (b + 2) (c + 2) ((1 - (x : ℂ)) / 2) = G2 at *
  have hne : (1 - (x : ℂ) ^ 2) ≠ 0 := by
    rw [show (1 - (x : ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring, ofReal_ne_zero]
    nlinarith [hx.1, hx.2]
  push_cast at hode ⊢
  simp only [a, b, c, s] at hode ⊢
  field_simp
  linear_combination (4 * (1 - (x : ℂ) ^ 2) * A) * hode

end DLMF.Legendre

end
