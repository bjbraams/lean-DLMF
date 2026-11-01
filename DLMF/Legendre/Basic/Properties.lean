/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Basic.Functions
public import DLMF.Hypergeometric.Basic.CutPlane

/-!
# Basic properties of `P_ν`, `Q_ν` and `𝖯^μ_ν` (DLMF §§14.2, 14.3)

`P_ν(z) = F(-ν, ν+1; 1; (1-z)/2)` and the Ferrers function `𝖯^μ_ν` are defined in
`DLMF.Legendre.Basic.Functions` through the continuation `regularizedGaussHG` of `₂F₁` to the
cut plane, so that `P_ν` is analytic on `ℂ ∖ (-∞, -1]` for every complex `ν`.

## Main results

* `legendreP_one`: `P_ν(1) = 1`.
* `legendreP_neg_sub_one`: `P_{-ν-1} = P_ν` (DLMF 14.9.5).
* `deriv_legendreP`, `iteratedDeriv_two_legendreP`: the first two derivatives through Gauss
  functions.
* `legendreP_ode`: Legendre's equation (DLMF 14.2.2 with `μ = 0`).
* `ferrersP_zero`: at `μ = 0` the Ferrers function is `P_ν` on `(-1, 1)`.
* `ferrersP_ode`: the associated Legendre equation DLMF 14.2.1 for the Ferrers function.
* `legendreQ_ode`: Legendre's equation for `Q_ν` (DLMF 14.2.2 with `μ = 0`).
* `analyticAt_legendreQ`: `Q_ν` is analytic on `ℂ ∖ (-∞, 1]`.

## Implementation notes

Both equations follow from the hypergeometric equation on the cut plane,
`DLMF.Hypergeometric.regularizedGaussHG_ode`. The bridge to the Legendre polynomials is in
`DLMF.Legendre.FirstKindProperties`, the value `Q₀` in `DLMF.Legendre.SecondKind`, and the
Wronskians in `DLMF.Legendre.Associated`.
-/

@[expose] public section

open Complex Filter Set DLMF.Hypergeometric
open scoped Topology Real

noncomputable section

namespace DLMF.Legendre

/-- For `z ∉ (-∞, -1]`, the argument `(1-z)/2` lies in the cut plane. -/
theorem mem_cutPlane_of_one_add {z : ℂ} (hz : 1 + z ∈ slitPlane) : (1 - z) / 2 ∈ cutPlane := by
  rw [mem_cutPlane, show 1 - (1 - z) / 2 = (1 + z) / 2 by ring]
  rw [mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left; simp at h ⊢; linarith
  · right; simpa using h

/-- `P_ν(1) = 1`. -/
theorem legendreP_one (ν : ℂ) : legendreP ν 1 = 1 := by
  rw [legendreP, sub_self, zero_div, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by simp),
    regularizedGaussHGFun_eq_div_Gamma (fun k h => by
      have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])]
  simp

/-- `P_{-ν-1} = P_ν` (DLMF 14.9.5, Temme (8.6)). -/
@[dlmf 14.9.E5]
theorem legendreP_neg_sub_one (ν : ℂ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    legendreP (-ν - 1) z = legendreP ν z := by
  rw [legendreP, legendreP, regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add hz)]
  congr 1 <;> ring

/-- The domain `ℂ ∖ (-∞, -1]` is open. -/
theorem isOpen_one_add_mem_slitPlane : IsOpen {z : ℂ | 1 + z ∈ slitPlane} :=
  isOpen_slitPlane.preimage (by fun_prop)

/-- Chain rule for `z ↦ 𝐅(a,b;c;(1-z)/2)`. -/
theorem hasDerivAt_regularizedGaussHG_half (a b c : ℂ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    HasDerivAt (fun z => regularizedGaussHG a b c ((1 - z) / 2))
      (-(1 / 2) * (a * b * regularizedGaussHG (a + 1) (b + 1) (c + 1) ((1 - z) / 2))) z := by
  have hw := mem_cutPlane_of_one_add hz
  have h := (differentiableAt_regularizedGaussHG a b c hw).hasDerivAt
  rw [deriv_regularizedGaussHG _ _ _ hw] at h
  have hl : HasDerivAt (fun z : ℂ => (1 - z) / 2) (-1 / 2) z := by
    simpa using ((hasDerivAt_id z).const_sub 1).div_const 2
  exact (h.comp z hl).congr_deriv (by ring)

/-- `P_ν'` through `𝐅(1-ν, ν+2; 2; (1-z)/2)`. -/
theorem deriv_legendreP (ν : ℂ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    deriv (legendreP ν) z =
      -(1 / 2) * (-ν * (ν + 1) * regularizedGaussHG (-ν + 1) (ν + 1 + 1) 2 ((1 - z) / 2)) := by
  have h := (hasDerivAt_regularizedGaussHG_half (-ν) (ν + 1) 1 hz).deriv
  rw [show (1 : ℂ) + 1 = 2 by norm_num] at h
  exact h

/-- `P_ν''` through `𝐅(2-ν, ν+3; 3; (1-z)/2)`. -/
theorem iteratedDeriv_two_legendreP (ν : ℂ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    iteratedDeriv 2 (legendreP ν) z =
      (1 / 4) * (-ν * (-ν + 1) * ((ν + 1) * (ν + 2)) *
        regularizedGaussHG (-ν + 2) (ν + 3) 3 ((1 - z) / 2)) := by
  have hev : deriv (legendreP ν) =ᶠ[𝓝 z] fun z =>
      -(1 / 2) * (-ν * (ν + 1) * regularizedGaussHG (-ν + 1) (ν + 1 + 1) 2 ((1 - z) / 2)) := by
    filter_upwards [isOpen_one_add_mem_slitPlane.mem_nhds hz] with w hw
    exact deriv_legendreP ν hw
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
  have h := ((hasDerivAt_regularizedGaussHG_half (-ν + 1) (ν + 1 + 1) 2 hz).const_mul
    (-ν * (ν + 1))).const_mul (-(1 / 2) : ℂ)
  rw [h.deriv]
  rw [show -ν + 1 + 1 = -ν + 2 by ring, show ν + 1 + 1 + 1 = ν + 3 by ring,
    show (2 : ℂ) + 1 = 3 by norm_num]
  ring

/-- Legendre's equation `(1-z²) w'' - 2z w' + ν(ν+1) w = 0` (DLMF 14.2.2 with `μ = 0`). -/
@[dlmf 14.2.E2]
theorem legendreP_ode (ν : ℂ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    (1 - z ^ 2) * iteratedDeriv 2 (legendreP ν) z - 2 * z * deriv (legendreP ν) z +
      ν * (ν + 1) * legendreP ν z = 0 := by
  have h := regularizedGaussHG_ode (-ν) (ν + 1) 1 (mem_cutPlane_of_one_add hz)
  rw [iteratedDeriv_two_legendreP ν hz, deriv_legendreP ν hz, legendreP]
  simp only [poch, ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one] at h
  rw [show (1 : ℂ) + 1 = 2 by norm_num, show (1 : ℂ) + 2 = 3 by norm_num,
    show ν + 1 + 2 = ν + 3 by ring] at h
  push_cast at h
  linear_combination h

/-- At `μ = 0` the Ferrers function is `P_ν` on `(-1, 1)`. -/
theorem ferrersP_zero (ν : ℂ) {x : ℝ} (hx : -1 < x) : ferrersP ν 0 x = legendreP ν x := by
  have hs : 1 + (x : ℂ) ∈ slitPlane := Or.inl (by simp; linarith)
  rw [ferrersP, legendreP, zero_div, cpow_zero, one_mul, sub_zero,
    regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add hs)]

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

/-- For `z ∉ (-∞, 1]`, `1/z²` lies in the cut plane. -/
theorem recip_sq_mem_cutPlane {z : ℂ} (hz : z - 1 ∈ slitPlane) : 1 / z ^ 2 ∈ cutPlane := by
  rw [mem_cutPlane, mem_slitPlane_iff]
  rw [mem_slitPlane_iff] at hz
  by_contra h
  push Not at h
  obtain ⟨hre, him⟩ := h
  have hz0 : z ≠ 0 := by
    rintro rfl; simp at hz; norm_num at hz
  set u := z ^ 2 with hu
  have hu0 : u ≠ 0 := pow_ne_zero 2 hz0
  have hn : 0 < normSq u := normSq_pos.mpr hu0
  simp only [sub_re, one_re, sub_im, one_im, one_div, inv_re, inv_im] at hre him
  have huim : u.im = 0 := by
    have : -u.im / normSq u = 0 := by linarith
    rw [neg_div, neg_eq_zero, div_eq_zero_iff] at this
    exact this.resolve_right hn.ne'
  have hure : normSq u ≤ u.re := by
    have : 1 ≤ u.re / normSq u := by linarith
    rwa [le_div_iff₀ hn, one_mul] at this
  have hnsq : normSq u = u.re * u.re := by rw [normSq_apply, huim]; ring
  have hx : u.re = z.re ^ 2 - z.im ^ 2 := by rw [hu]; simp [pow_two]
  have hy : u.im = 2 * z.re * z.im := by rw [hu]; simp [pow_two]; ring
  have hpos : 0 < u.re := by nlinarith
  have hle : u.re ≤ 1 := by nlinarith
  have hyz : z.im = 0 := by
    rcases mul_eq_zero.mp (show 2 * z.re * z.im = 0 by linarith) with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · rw [h] at hx; nlinarith [sq_nonneg z.im]
    · exact h
  rw [hyz] at hx
  have : z.re ≤ 1 := by nlinarith
  rcases hz with h | h
  · simp at h; linarith
  · simp [hyz] at h

/-- `z ∉ (-∞, 1]` implies `z ∉ (-∞, 0]`. -/
theorem mem_slitPlane_of_sub_one {z : ℂ} (hz : z - 1 ∈ slitPlane) : z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left; simp at h; linarith
  · right; simpa using h

/-- The domain `ℂ ∖ (-∞, 1]` of `Q_ν` is open. -/
theorem isOpen_sub_one_mem_slitPlane : IsOpen {z : ℂ | z - 1 ∈ slitPlane} :=
  isOpen_slitPlane.preimage (by fun_prop)

/-- Chain rule for `z ↦ z^p 𝐅(a,b;c;1/z²)`. -/
theorem hasDerivAt_cpow_mul_regularizedGaussHG_recip_sq (a b c p : ℂ) {z : ℂ}
    (hz : z - 1 ∈ slitPlane) :
    HasDerivAt (fun z => z ^ p * regularizedGaussHG a b c (1 / z ^ 2))
      (p * z ^ (p - 1) * regularizedGaussHG a b c (1 / z ^ 2) -
        2 * z ^ (p - 3) * (a * b * regularizedGaussHG (a + 1) (b + 1) (c + 1) (1 / z ^ 2))) z := by
  have hs := mem_slitPlane_of_sub_one hz
  have hz0 := slitPlane_ne_zero hs
  have hu := recip_sq_mem_cutPlane hz
  have hG := (differentiableAt_regularizedGaussHG a b c hu).hasDerivAt
  rw [deriv_regularizedGaussHG _ _ _ hu] at hG
  have hinv : HasDerivAt (fun z : ℂ => 1 / z ^ 2) (-2 / z ^ 3) z := by
    have h := (hasDerivAt_pow 2 z).inv (pow_ne_zero 2 hz0)
    simp only [one_div]
    convert h using 1
    field_simp
    ring
  have hp : HasDerivAt (fun z : ℂ => z ^ p) (p * z ^ (p - 1)) z :=
    (hasDerivAt_id z).cpow_const hs |>.congr_deriv (by simp)
  have h := hp.mul (hG.comp z hinv)
  refine h.congr_deriv ?_
  have h3 : z ^ (p - 3) = z ^ (p - 1) / z ^ 2 := by
    rw [show p - 3 = (p - 1) - ((2 : ℕ) : ℂ) by push_cast; ring, cpow_sub _ _ hz0, cpow_natCast]
  rw [h3, show p - 1 = p - 1 by rfl]
  simp only [Function.comp]
  rw [cpow_sub _ _ hz0, cpow_one]
  field_simp
  ring

/-- Legendre's equation for `Q_ν` (DLMF 14.2.2 with `μ = 0`). -/
@[dlmf 14.2.E2]
theorem legendreQ_ode (ν : ℂ) {z : ℂ}
    (hz : z - 1 ∈ slitPlane) :
    (1 - z ^ 2) * iteratedDeriv 2 (legendreQ ν) z - 2 * z * deriv (legendreQ ν) z +
      ν * (ν + 1) * legendreQ ν z = 0 := by
  set K : ℂ := Real.sqrt π * Gamma (ν + 1) * 2 ^ (-(ν + 1))
  set a := (ν + 2) / 2
  set b := (ν + 1) / 2
  set c := ν + 3 / 2
  set p := -(ν + 1)
  have hz0 := slitPlane_ne_zero (mem_slitPlane_of_sub_one hz)
  have hd (w : ℂ) (hw : w - 1 ∈ slitPlane) : HasDerivAt (legendreQ ν)
      (K * (p * w ^ (p - 1) * regularizedGaussHG a b c (1 / w ^ 2) -
        2 * w ^ (p - 3) * (a * b * regularizedGaussHG (a + 1) (b + 1) (c + 1) (1 / w ^ 2)))) w :=
    (hasDerivAt_cpow_mul_regularizedGaussHG_recip_sq a b c p hw).const_mul K
  have hev : deriv (legendreQ ν) =ᶠ[𝓝 z] fun w =>
      K * (p * (w ^ (p - 1) * regularizedGaussHG a b c (1 / w ^ 2)) -
        2 * (a * b) * (w ^ (p - 3) * regularizedGaussHG (a + 1) (b + 1) (c + 1) (1 / w ^ 2))) := by
    filter_upwards [isOpen_sub_one_mem_slitPlane.mem_nhds hz] with w hw
    rw [(hd w hw).deriv]; ring
  have h2 := (((hasDerivAt_cpow_mul_regularizedGaussHG_recip_sq a b c (p - 1) hz).const_mul p).sub
    ((hasDerivAt_cpow_mul_regularizedGaussHG_recip_sq (a + 1) (b + 1) (c + 1) (p - 3) hz).const_mul
      (2 * (a * b)))).const_mul K
  have h2' : HasDerivAt (fun w =>
      K * (p * (w ^ (p - 1) * regularizedGaussHG a b c (1 / w ^ 2)) -
        2 * (a * b) * (w ^ (p - 3) * regularizedGaussHG (a + 1) (b + 1) (c + 1) (1 / w ^ 2)))) _ z
            := h2
  have hQ : legendreQ ν z = K * (z ^ p * regularizedGaussHG a b c (1 / z ^ 2)) := rfl
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, h2'.deriv, (hd z hz).deriv, hQ]
  have hode := regularizedGaussHG_ode a b c (recip_sq_mem_cutPlane hz)
  have hpow (k : ℕ) : z ^ (p - k) = z ^ p / z ^ k := by
    rw [cpow_sub _ _ hz0, cpow_natCast]
  rw [show p - 1 - 1 = p - (2 : ℕ) by push_cast; ring,
    show p - 1 - 3 = p - (4 : ℕ) by push_cast; ring,
    show p - 3 - 1 = p - (4 : ℕ) by push_cast; ring,
    show p - 3 - 3 = p - (6 : ℕ) by push_cast; ring,
    show p - 1 = p - (1 : ℕ) by push_cast; ring, show p - 3 = p - (3 : ℕ) by push_cast; ring,
    hpow, hpow, hpow, hpow, hpow]
  simp only [poch, ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one] at hode
  rw [show a + 1 + 1 = a + 2 by ring, show b + 1 + 1 = b + 2 by ring,
    show c + 1 + 1 = c + 2 by ring]
  generalize regularizedGaussHG a b c (1 / z ^ 2) = G0 at *
  generalize regularizedGaussHG (a + 1) (b + 1) (c + 1) (1 / z ^ 2) = G1 at *
  generalize regularizedGaussHG (a + 2) (b + 2) (c + 2) (1 / z ^ 2) = G2 at *
  generalize z ^ p = Zp at *
  push_cast at hode ⊢
  field_simp at hode ⊢
  simp only [a, b, c, p] at hode ⊢
  linear_combination (-4 * K * Zp) * hode

/-- `w ∈ slitPlane → w⁻¹ ∈ slitPlane`. -/
theorem recip_mem_slitPlane' {w : ℂ} (hw : w ∈ slitPlane) : w⁻¹ ∈ slitPlane := by
  have hn : 0 < normSq w := normSq_pos.mpr (slitPlane_ne_zero hw)
  rw [mem_slitPlane_iff] at hw ⊢
  rcases hw with h | h
  · left; rw [inv_re]; positivity
  · right; rw [inv_im]; exact div_ne_zero (neg_ne_zero.mpr h) hn.ne'

/-- For `z ∉ (-∞, 1]`, `(z+1)/(z-1)` lies in the slit plane. -/
theorem div_mem_slitPlane {z : ℂ} (hz : z - 1 ∈ slitPlane) : (z + 1) / (z - 1) ∈ slitPlane := by
  have hz1 : z - 1 ≠ 0 := slitPlane_ne_zero hz
  have hi := recip_mem_slitPlane' hz
  rw [show (z + 1) / (z - 1) = 1 + 2 * (z - 1)⁻¹ by field_simp; ring]
  rw [mem_slitPlane_iff] at hi ⊢
  rcases hi with h | h
  · left; simp at h ⊢; linarith
  · right; simpa using h

/-- The domain `ℂ ∖ (-∞, 1]` is connected. -/
theorem isPreconnected_sub_one_mem_slitPlane : IsPreconnected {z : ℂ | z - 1 ∈ slitPlane} := by
  have h := ((StarConvex.isPathConnected starConvex_one_slitPlane
    (by simp)).isConnected.isPreconnected).image (fun w : ℂ => w + 1)
    (by fun_prop : Continuous fun w : ℂ => w + 1).continuousOn
  convert h using 1
  ext z
  simp only [mem_ofPred_eq, mem_image]
  exact ⟨fun h => ⟨z - 1, h, by ring⟩, fun ⟨w, hw, hwz⟩ => by rw [← hwz]; simpa using hw⟩

/-- `Q_ν` is analytic on `ℂ ∖ (-∞, 1]`. -/
theorem analyticAt_legendreQ (ν : ℂ) {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    AnalyticAt ℂ (legendreQ ν) z := by
  have hs := mem_slitPlane_of_sub_one hz
  have hz0 := slitPlane_ne_zero hs
  have hu := recip_sq_mem_cutPlane hz
  have hG : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG ((ν + 2) / 2) ((ν + 1) / 2) (ν + 3 / 2)
      (1 / w ^ 2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ hu).comp_of_eq
      (by fun_prop (disch := exact pow_ne_zero 2 hz0)) rfl
  unfold legendreQ
  exact analyticAt_const.mul ((analyticAt_id.cpow analyticAt_const hs).mul hG)

end DLMF.Legendre
