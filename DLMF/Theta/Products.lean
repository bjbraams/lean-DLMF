/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic
public import DLMF.QSeries.Identities
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn

/-!
# Theta functions: infinite products and related results (DLMF §20.5)

Single products (20.5.1–20.5.8), Jacobi's triple product in theta form (20.5.9), the
logarithmic derivatives (20.5.10–20.5.13) and the Eisenstein-ordered double products
(20.5.14–20.5.17). Throughout `q = e^{iπτ}`, `q^{1/4} = e^{iπτ/4}` and `Im τ > 0`.
Products over `n ≥ 1` are `HasProd` statements over `k : ℕ` with `n = k + 1`.

The triple product `DLMF.QSeries.jacobi_triple_product` (DLMF 17.8.1) is the source of the
product formulas.

In 20.5.10 and 20.5.11 the left-hand sides are meromorphic with removable singularities at the
real zeros of `θ₁`, resp. `θ₂`; with Lean's conventions `x / 0 = 0` both sides vanish there, so
the statements hold on the whole strip.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic DLMF.QSeries

/-! ### Helpers -/

/-- `HasProd` form of `(a;Q)_∞` for `‖Q‖ < 1`. -/
lemma th20_hasProd_qPochhammerInf (a : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun k : ℕ => 1 - a * q ^ k) (qPochhammerInf a q) :=
  (multipliable_one_sub_mul_pow hq).hasProd

/-- The triple product for `θ₃` as one `HasProd` over `k : ℕ`. -/
lemma th20_three_hasProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasProd (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + cexp (π * I * τ) ^ (2 * k + 1) * cexp (2 * I * z)) *
        (1 + cexp (π * I * τ) ^ (2 * k + 1) * (cexp (2 * I * z))⁻¹))
      (jacobiThetaThreeTau z τ) := by
  have hQn : ‖cexp (π * I * τ) ^ 2‖ < 1 := by
    rw [norm_pow]
    have h := th20_norm_nome_lt_one hτ
    nlinarith [norm_nonneg (cexp (π * I * τ))]
  rw [th20_three_eq_qPochhammer z hτ]
  convert ((th20_hasProd_qPochhammerInf _ hQn).mul (th20_hasProd_qPochhammerInf _ hQn)).mul
    (th20_hasProd_qPochhammerInf _ hQn) using 1
  funext k
  ring

/-- `a ↦ (a;q)_∞` is entire for `‖q‖ < 1` (helper). -/
theorem p20R1_differentiable_qPochhammerInf {q : ℂ} (hq : ‖q‖ < 1) :
    Differentiable ℂ (fun a => qPochhammerInf a q) := by
  intro a₀
  have hU : IsOpen (Metric.ball (0 : ℂ) (‖a₀‖ + 1)) := Metric.isOpen_ball
  have hloc : HasProdLocallyUniformlyOn (fun k a => 1 + -(a * q ^ k))
      (fun a => ∏' k, (1 + -(a * q ^ k))) (Metric.ball (0 : ℂ) (‖a₀‖ + 1)) := by
    apply hasProdLocallyUniformlyOn_of_forall_compact hU
    intro K hK hcK
    refine ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left
      (‖a₀‖ + 1)).hasProdUniformlyOn_nat_one_add hcK (.of_forall fun n x hx => ?_)
      (fun _ => by fun_prop)
    have hx' : ‖x‖ < ‖a₀‖ + 1 := by simpa [Metric.mem_ball, dist_zero_right] using hK hx
    rw [norm_neg, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right hx'.le (pow_nonneg (norm_nonneg _) _)
  have hd := hloc.differentiableOn (.of_forall fun s => by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun _ _ => by fun_prop)) hU
  have hmem : a₀ ∈ Metric.ball (0 : ℂ) (‖a₀‖ + 1) := by simp
  have := (hd a₀ hmem).differentiableAt (hU.mem_nhds hmem)
  simpa only [qPochhammerInf, sub_eq_add_neg] using this


/-- `θ₁(z|τ) = 2 q^{1/4} sin z (Q;Q)_∞ (Q e^{2iz};Q)_∞ (Q e^{-2iz};Q)_∞`, `Q = q²` (helper). -/
theorem p20R1_one_eq_qPochhammer (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiThetaOneTau z τ = 2 * cexp (π * I * τ / 4) * sin z *
      (qPochhammerInf (cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2) *
        qPochhammerInf (cexp (π * I * τ) ^ 2 * cexp (2 * I * z)) (cexp (π * I * τ) ^ 2) *
        qPochhammerInf (cexp (π * I * τ) ^ 2 * (cexp (2 * I * z))⁻¹) (cexp (π * I * τ) ^ 2)) := by
  have hQn := th20_norm_nome_sq_lt_one hτ
  rw [(jacobiThetaOneTau_half_periods z τ).2.2, th20_three_eq_qPochhammer _ hτ, thetaMultiplierM]
  set E := cexp (π * I * τ) with hE
  set w := cexp (2 * I * z) with hw
  have hE0 : E ≠ 0 := exp_ne_zero _
  have hw0 : w ≠ 0 := exp_ne_zero _
  have hw' : cexp (2 * I * (z + π / 2 + π * τ / 2)) = -(E * w) := by
    rw [hE, hw, ← exp_add, show 2 * I * (z + π / 2 + π * τ / 2) =
      (π * I * τ + 2 * I * z) + π * I by ring, exp_add, exp_pi_mul_I]; ring
  rw [hw', show -(E * -(E * w)) = E ^ 2 * w by ring,
    show -(E * (-(E * w))⁻¹) = w⁻¹ by field_simp, qPochhammerInf_shift (a := w⁻¹) hQn]
  have hs : cexp (I * z) * (1 - w⁻¹) = 2 * I * sin z := by
    rw [hw, ← exp_neg, sin, show -(2 * I * z) = -(I * z) + -(I * z) by ring, exp_add]
    have h1 : cexp (I * z) * cexp (-(I * z)) = 1 := by rw [← exp_add]; simp
    rw [show -z * I = -(I * z) by ring, show z * I = I * z by ring]
    field_simp
    linear_combination (-cexp (-(I * z))) * h1 + (cexp (I * z) - cexp (-(I * z))) * I_sq
  have hM : cexp (I * z + π * I * τ / 4) = cexp (I * z) * cexp (π * I * τ / 4) := by
    rw [← exp_add]
  rw [hM, mul_comm w⁻¹ (E ^ 2)]
  linear_combination (-I * cexp (π * I * τ / 4) * qPochhammerInf (E ^ 2) (E ^ 2) *
    qPochhammerInf (E ^ 2 * w) (E ^ 2) * qPochhammerInf (E ^ 2 * w⁻¹) (E ^ 2)) * hs +
    (-2 * cexp (π * I * τ / 4) * sin z * qPochhammerInf (E ^ 2) (E ^ 2) *
    qPochhammerInf (E ^ 2 * w) (E ^ 2) * qPochhammerInf (E ^ 2 * w⁻¹) (E ^ 2)) * I_sq


/-- `θ₁'(0|τ) = 2 q^{1/4} (Q;Q)_∞³` (helper for 20.4.2). -/
theorem p20R1_oneDeriv_qPochhammer {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiThetaOneDerivNullTau τ = 2 * cexp (π * I * τ / 4) *
      qPochhammerInf (cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2) ^ 3 := by
  have hQn := th20_norm_nome_sq_lt_one hτ
  set Q := cexp (π * I * τ) ^ 2 with hQ
  set G : ℂ → ℂ := fun z => qPochhammerInf Q Q * qPochhammerInf (Q * cexp (2 * I * z)) Q *
    qPochhammerInf (Q * (cexp (2 * I * z))⁻¹) Q with hG
  have hf : (fun z => jacobiThetaOneTau z τ) = fun z => 2 * cexp (π * I * τ / 4) * sin z * G z := by
    funext z; rw [p20R1_one_eq_qPochhammer z hτ]
  have hd := p20R1_differentiable_qPochhammerInf hQn
  have hGd : DifferentiableAt ℂ G 0 := by
    have h1 : DifferentiableAt ℂ (fun z : ℂ => qPochhammerInf (Q * cexp (2 * I * z)) Q) 0 :=
      (hd _).comp 0 (by fun_prop)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => qPochhammerInf (Q * (cexp (2 * I * z))⁻¹) Q) 0 :=
      (hd _).comp 0 (((differentiableAt_const _).mul ((by fun_prop :
        DifferentiableAt ℂ (fun z : ℂ => cexp (2 * I * z)) 0).inv (exp_ne_zero _))))
    exact ((differentiableAt_const _).mul h1).mul h2
  have hD := (((hasDerivAt_sin 0).const_mul (2 * cexp (π * I * τ / 4))).mul hGd.hasDerivAt)
  rw [jacobiThetaOneDerivNullTau, hf]
  rw [show (fun z => 2 * cexp (π * I * τ / 4) * sin z * G z) =
    (fun y => 2 * cexp (π * I * τ / 4) * sin y) * G from rfl, hD.deriv]
  simp only [cos_zero, sin_zero, mul_zero, zero_mul, add_zero, mul_one, hG, exp_zero, inv_one]
  ring

/-- `θ₁'(0|τ) = 2 q^{1/4} ∏_{n≥1} (1 - q^{2n})³`, with multipliability (helper for 20.4.2, 20.5.5). -/
theorem p20R1_oneDeriv_tprod {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => 1 - cexp (π * I * τ) ^ (2 * (k + 1))) ∧
      qPochhammerInf (cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2) =
        ∏' k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) ∧
      jacobiThetaOneDerivNullTau τ = 2 * cexp (π * I * τ / 4) *
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) ^ 3) := by
  have hQn := th20_norm_nome_sq_lt_one hτ
  have hm := multipliable_one_sub_mul_pow (w := cexp (π * I * τ) ^ 2) hQn
  have key : ∀ k : ℕ, 1 - cexp (π * I * τ) ^ 2 * (cexp (π * I * τ) ^ 2) ^ k =
      1 - cexp (π * I * τ) ^ (2 * (k + 1)) := fun k => by ring
  have hm' : Multipliable (fun k : ℕ => 1 - cexp (π * I * τ) ^ (2 * (k + 1))) := hm.congr key
  have hP : qPochhammerInf (cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2) =
      ∏' k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) := by
    rw [qPochhammerInf]; exact tprod_congr key
  refine ⟨hm', hP, ?_⟩
  rw [p20R1_oneDeriv_qPochhammer hτ, hP, hm'.tprod_pow]

/-- `sin(a+z) sin(a-z)/sin²a = (1 - 2x cos 2z + x²)/(1 - x)²`, `x = e^{2ia}` (helper). -/
lemma p20R1_sin_ratio (a z : ℂ) (hx : 1 - cexp (2 * I * a) ≠ 0) :
    sin (a + z) * sin (a - z) / sin a ^ 2 =
      (1 - 2 * cexp (2 * I * a) * cos (2 * z) + cexp (2 * I * a) ^ 2) /
        (1 - cexp (2 * I * a)) ^ 2 := by
  set x := cexp (2 * I * a) with hxdef
  have hx0 : x ≠ 0 := exp_ne_zero _
  have hc := th20_exp_add_inv a
  rw [← hxdef] at hc
  have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hs1 := cos_sub_cos (2 * a) (2 * z)
  have hs2 := cos_sub_cos (2 * a) 0
  rw [show (2 * a + 2 * z) / 2 = a + z by ring, show (2 * a - 2 * z) / 2 = a - z by ring] at hs1
  rw [show (2 * a + 0) / 2 = a by ring, show (2 * a - 0) / 2 = a by ring, cos_zero] at hs2
  have h1 : 1 - 2 * x * cos (2 * z) + x ^ 2 = -4 * x * (sin (a + z) * sin (a - z)) := by
    linear_combination x * hc - hxx + 2 * x * hs1
  have h2 : (1 - x) ^ 2 = -4 * x * sin a ^ 2 := by
    linear_combination x * hc - hxx + 2 * x * hs2
  have hsa : sin a ^ 2 ≠ 0 := by
    intro h; rw [h, mul_zero] at h2; exact hx (pow_eq_zero_iff two_ne_zero |>.mp h2)
  rw [h1, h2]
  field_simp

/-- `cos(a+z) cos(a-z)/cos²a = (1 + 2x cos 2z + x²)/(1 + x)²`, `x = e^{2ia}` (helper). -/
lemma p20R1_cos_ratio (a z : ℂ) (hx : 1 + cexp (2 * I * a) ≠ 0) :
    cos (a + z) * cos (a - z) / cos a ^ 2 =
      (1 + 2 * cexp (2 * I * a) * cos (2 * z) + cexp (2 * I * a) ^ 2) /
        (1 + cexp (2 * I * a)) ^ 2 := by
  set x := cexp (2 * I * a) with hxdef
  have hx0 : x ≠ 0 := exp_ne_zero _
  have hc := th20_exp_add_inv a
  rw [← hxdef] at hc
  have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hs1 := cos_add_cos (2 * a) (2 * z)
  have hs2 := cos_add_cos (2 * a) 0
  rw [show (2 * a + 2 * z) / 2 = a + z by ring, show (2 * a - 2 * z) / 2 = a - z by ring] at hs1
  rw [show (2 * a + 0) / 2 = a by ring, show (2 * a - 0) / 2 = a by ring, cos_zero] at hs2
  have h1 : 1 + 2 * x * cos (2 * z) + x ^ 2 = 4 * x * (cos (a + z) * cos (a - z)) := by
    linear_combination x * hc - hxx + 2 * x * hs1
  have h2 : (1 + x) ^ 2 = 4 * x * cos a ^ 2 := by
    linear_combination x * hc - hxx + 2 * x * hs2
  have hsa : cos a ^ 2 ≠ 0 := by
    intro h; rw [h, mul_zero] at h2; exact hx (pow_eq_zero_iff two_ne_zero |>.mp h2)
  rw [h1, h2]
  field_simp

/-- Quotient of two convergent products (helper). -/
lemma p20R1_ratio_prod {f g r : ℕ → ℂ} {F G : ℂ} (hf : HasProd f F) (hg : HasProd g G)
    (hG : G ≠ 0) (hr : ∀ k, r k = f k / g k) : Multipliable r ∧ ∏' k, r k = F / G := by
  have h := hf.div₀ hg hG
  have h' : HasProd r (F / G) := by
    convert h using 1; funext k; exact hr k
  exact ⟨h'.multipliable, h'.tprod_eq⟩

/-- `‖e^{iπτ}^m‖ < 1` for `m ≥ 1` (helper). -/
lemma p20R1_norm_nome_pow_lt_one {τ : ℂ} (hτ : 0 < τ.im) {m : ℕ} (hm : m ≠ 0) :
    ‖cexp (π * I * τ) ^ m‖ < 1 := by
  rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (th20_norm_nome_lt_one hτ) hm

/-- `e^{iπτ}^m = e^{2i (m/2) π τ}` (helper). -/
lemma p20R1_nome_pow (τ : ℂ) (m : ℕ) :
    cexp (π * I * τ) ^ m = cexp (2 * I * ((m / 2 : ℂ) * π * τ)) := by
  rw [← exp_nat_mul]; congr 1; ring

/-! ### §20.5(i) Single products -/

/-- DLMF 20.5.2: `θ₂(z,q) = 2q^{1/4} cos z ∏_{n≥1} (1 - q^{2n})(1 + 2q^{2n} cos 2z + q^{4n})`. -/
@[dlmf 20.5.E2]
theorem jacobiThetaTwoTau_hasProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))) ∧
      jacobiThetaTwoTau z τ = 2 * cexp (π * I * τ / 4) * cos z *
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))) := by
  have hQn := th20_norm_nome_sq_lt_one hτ
  have hw1 : cexp (2 * I * z) * (cexp (2 * I * z))⁻¹ = 1 := mul_inv_cancel₀ (exp_ne_zero _)
  have hcos := th20_exp_add_inv z
  set E := cexp (π * I * τ) with hE
  set w := cexp (2 * I * z) with hw
  have hP := ((th20_hasProd_qPochhammerInf (E ^ 2) hQn).mul
    (th20_hasProd_qPochhammerInf (-(E ^ 2 * w)) hQn)).mul
    (th20_hasProd_qPochhammerInf (-(w⁻¹ * E ^ 2)) hQn)
  have key : ∀ k : ℕ, (1 - E ^ 2 * (E ^ 2) ^ k) * (1 - -(E ^ 2 * w) * (E ^ 2) ^ k) *
      (1 - -(w⁻¹ * E ^ 2) * (E ^ 2) ^ k) =
      (1 - E ^ (2 * (k + 1))) * (1 + 2 * E ^ (2 * (k + 1)) * cos (2 * z) + E ^ (4 * (k + 1))) :=
    fun k => by
      linear_combination (1 - E ^ (2 * (k + 1))) * E ^ (2 * (k + 1)) * hcos +
        (1 - E ^ (2 * (k + 1))) * (E ^ (2 * (k + 1))) ^ 2 * hw1
  have hP' := th20_hasProd_congr hP key
  have hw' : cexp (2 * I * (z + π * τ / 2)) = E * w := by
    rw [hE, hw, ← exp_add]; congr 1; ring
  have hEw : E * (E * w)⁻¹ = w⁻¹ := by
    have hE0 : E ≠ 0 := exp_ne_zero _
    field_simp
  have h3 : jacobiThetaThreeTau (z + π * τ / 2) τ = (1 + w⁻¹) * (qPochhammerInf (E ^ 2) (E ^ 2) *
      qPochhammerInf (-(E ^ 2 * w)) (E ^ 2) * qPochhammerInf (-(w⁻¹ * E ^ 2)) (E ^ 2)) := by
    rw [th20_three_eq_qPochhammer _ hτ, ← hE, hw', qPochhammerInf_shift (a := -(E * (E * w)⁻¹)) hQn,
      hEw, show -(E * (E * w)) = -(E ^ 2 * w) by ring, show -w⁻¹ * E ^ 2 = -(w⁻¹ * E ^ 2) by ring]
    ring
  have hcz : cexp (I * z) * (1 + w⁻¹) = 2 * cos z := by
    rw [hw, ← exp_neg, mul_add, mul_one, ← exp_add, cos, show I * z + -(2 * I * z) = -z * I by ring,
      show I * z = z * I by ring]
    ring
  refine ⟨hP'.multipliable, ?_⟩
  rw [jacobiThetaTwoTau, exp_add, h3, hP'.tprod_eq,
    show ∀ a b c d : ℂ, a * b * (c * d) = a * (b * c) * d from fun a b c d => by ring, hcz]
  ring

/-- DLMF 20.5.1: `θ₁(z,q) = 2q^{1/4} sin z ∏_{n≥1} (1 - q^{2n})(1 - 2q^{2n} cos 2z + q^{4n})`. -/
@[dlmf 20.5.E1]
theorem jacobiThetaOneTau_hasProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))) ∧
      jacobiThetaOneTau z τ = 2 * cexp (π * I * τ / 4) * sin z *
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))) := by
  obtain ⟨hm, he⟩ := jacobiThetaTwoTau_hasProd (z + π / 2) hτ
  have hc : cos (2 * (z + π / 2)) = -cos (2 * z) := by
    rw [show 2 * (z + π / 2) = 2 * z + π by ring, cos_add_pi]
  have key : ∀ k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
      (1 + 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * (z + π / 2)) +
        cexp (π * I * τ) ^ (4 * (k + 1))) =
      (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1))) := fun k => by rw [hc]; ring
  refine ⟨hm.congr key, ?_⟩
  rw [jacobiThetaOneTau, he, cos_add_pi_div_two, tprod_congr key]
  ring

/-- DLMF 20.5.3: `θ₃(z,q) = ∏_{n≥1} (1 - q^{2n})(1 + 2q^{2n-1} cos 2z + q^{4n-2})`. -/
@[dlmf 20.5.E3]
theorem jacobiThetaThreeTau_hasProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))) ∧
      jacobiThetaThreeTau z τ =
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))) := by
  have h := th20_three_hasProd z hτ
  have hw1 : cexp (2 * I * z) * (cexp (2 * I * z))⁻¹ = 1 := mul_inv_cancel₀ (exp_ne_zero _)
  have hcos := th20_exp_add_inv z
  have key : ∀ k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
      (1 + cexp (π * I * τ) ^ (2 * k + 1) * cexp (2 * I * z)) *
      (1 + cexp (π * I * τ) ^ (2 * k + 1) * (cexp (2 * I * z))⁻¹) =
      (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2)) := fun k => by
    linear_combination (1 - cexp (π * I * τ) ^ (2 * (k + 1))) * cexp (π * I * τ) ^ (2 * k + 1) *
      hcos + (1 - cexp (π * I * τ) ^ (2 * (k + 1))) * (cexp (π * I * τ) ^ (2 * k + 1)) ^ 2 * hw1
  have h' := th20_hasProd_congr h key
  exact ⟨h'.multipliable, h'.tprod_eq.symm⟩

/-- DLMF 20.5.4: `θ₄(z,q) = ∏_{n≥1} (1 - q^{2n})(1 - 2q^{2n-1} cos 2z + q^{4n-2})`. -/
@[dlmf 20.5.E4]
theorem jacobiThetaFourTau_hasProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))) ∧
      jacobiThetaFourTau z τ =
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))) := by
  obtain ⟨hm, he⟩ := jacobiThetaThreeTau_hasProd (z + π / 2) hτ
  have hc : cos (2 * (z + π / 2)) = -cos (2 * z) := by
    rw [show 2 * (z + π / 2) = 2 * z + π by ring, cos_add_pi]
  have key : ∀ k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
      (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * (z + π / 2)) +
        cexp (π * I * τ) ^ (4 * k + 2)) =
      (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2)) := fun k => by rw [hc]; ring
  exact ⟨hm.congr key, by rw [jacobiThetaFourTau, he]; exact tprod_congr key⟩

/-- DLMF 20.5.5: `θ₁(z|τ) = θ₁'(0|τ) sin z ∏_{n≥1} sin(nπτ + z) sin(nπτ - z)/sin²(nπτ)`. -/
@[dlmf 20.5.E5]
theorem jacobiThetaOneTau_hasProd_sin (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => sin ((k + 1) * π * τ + z) * sin ((k + 1) * π * τ - z) /
        sin ((k + 1) * π * τ) ^ 2) ∧
      jacobiThetaOneTau z τ = jacobiThetaOneDerivNullTau τ * sin z *
        ∏' k : ℕ, (sin ((k + 1) * π * τ + z) * sin ((k + 1) * π * τ - z) /
        sin ((k + 1) * π * τ) ^ 2) := by
  obtain ⟨hm1, he1⟩ := jacobiThetaOneTau_hasProd z hτ
  obtain ⟨hmd, hPd, hd⟩ := p20R1_oneDeriv_tprod hτ
  have hQn := th20_norm_nome_sq_lt_one hτ
  set E := cexp (π * I * τ) with hE
  have hG : ∏' k : ℕ, (1 - E ^ (2 * (k + 1))) ^ 3 ≠ 0 := by
    rw [hmd.tprod_pow, ← hPd]
    exact pow_ne_zero 3 (qPochhammerInf_ne_zero_of_norm_lt_one hQn hQn)
  have hx : ∀ k : ℕ, 1 - E ^ (2 * (k + 1)) ≠ 0 := fun k =>
    one_sub_ne_zero_of_norm_lt_one (p20R1_norm_nome_pow_lt_one hτ (by omega))
  have hxk : ∀ k : ℕ, cexp (2 * I * ((k + 1) * π * τ)) = E ^ (2 * (k + 1)) := fun k => by
    rw [hE, ← exp_nat_mul]; congr 1; push_cast; ring
  have hr : ∀ k : ℕ, sin ((k + 1) * π * τ + z) * sin ((k + 1) * π * τ - z) /
      sin ((k + 1) * π * τ) ^ 2 =
      ((1 - E ^ (2 * (k + 1))) * (1 - 2 * E ^ (2 * (k + 1)) * cos (2 * z) + E ^ (4 * (k + 1)))) /
        (1 - E ^ (2 * (k + 1))) ^ 3 := fun k => by
    rw [p20R1_sin_ratio _ _ (by rw [hxk]; exact hx k), hxk,
      show E ^ (4 * (k + 1)) = (E ^ (2 * (k + 1))) ^ 2 by rw [← pow_mul]; ring_nf]
    have := hx k
    field_simp
  obtain ⟨hmr, hpr⟩ := p20R1_ratio_prod hm1.hasProd (hmd.pow 3).hasProd hG hr
  refine ⟨hmr, ?_⟩
  rw [he1, hd, hpr, show ∀ c s G F : ℂ, c * G * s * (F / G) = c * s * (G * (F / G)) from
    fun _ _ _ _ => by ring, mul_div_cancel₀ _ hG]

/-- DLMF 20.5.6: `θ₂(z|τ) = θ₂(0|τ) cos z ∏_{n≥1} cos(nπτ + z) cos(nπτ - z)/cos²(nπτ)`. -/
@[dlmf 20.5.E6]
theorem jacobiThetaTwoTau_hasProd_cos (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => cos ((k + 1) * π * τ + z) * cos ((k + 1) * π * τ - z) /
        cos ((k + 1) * π * τ) ^ 2) ∧
      jacobiThetaTwoTau z τ = jacobiThetaTwoNullTau τ * cos z *
        ∏' k : ℕ, (cos ((k + 1) * π * τ + z) * cos ((k + 1) * π * τ - z) /
        cos ((k + 1) * π * τ) ^ 2) := by
  obtain ⟨hm1, he1⟩ := jacobiThetaTwoTau_hasProd z hτ
  obtain ⟨hm0, he0⟩ := jacobiThetaTwoTau_hasProd 0 hτ
  set E := cexp (π * I * τ) with hE
  have h2 := (jacobiThetaNullTau_ne_zero hτ).1
  have hG : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
      (1 + 2 * E ^ (2 * (k + 1)) * cos (2 * 0) + E ^ (4 * (k + 1)))) ≠ 0 := by
    intro h; apply h2; rw [jacobiThetaTwoNullTau, he0, h, mul_zero]
  have hx : ∀ k : ℕ, 1 - E ^ (2 * (k + 1)) ≠ 0 := fun k =>
    one_sub_ne_zero_of_norm_lt_one (p20R1_norm_nome_pow_lt_one hτ (by omega))
  have hx' : ∀ k : ℕ, 1 + E ^ (2 * (k + 1)) ≠ 0 := fun k => by
    rw [← sub_neg_eq_add]
    exact one_sub_ne_zero_of_norm_lt_one (by rw [norm_neg]; exact p20R1_norm_nome_pow_lt_one hτ (by omega))
  have hxk : ∀ k : ℕ, cexp (2 * I * ((k + 1) * π * τ)) = E ^ (2 * (k + 1)) := fun k => by
    rw [hE, ← exp_nat_mul]; congr 1; push_cast; ring
  have hr : ∀ k : ℕ, cos ((k + 1) * π * τ + z) * cos ((k + 1) * π * τ - z) /
      cos ((k + 1) * π * τ) ^ 2 =
      ((1 - E ^ (2 * (k + 1))) * (1 + 2 * E ^ (2 * (k + 1)) * cos (2 * z) + E ^ (4 * (k + 1)))) /
        ((1 - E ^ (2 * (k + 1))) * (1 + 2 * E ^ (2 * (k + 1)) * cos (2 * 0) + E ^ (4 * (k + 1))))
      := fun k => by
    rw [p20R1_cos_ratio _ _ (by rw [hxk]; exact hx' k), hxk,
      show E ^ (4 * (k + 1)) = (E ^ (2 * (k + 1))) ^ 2 by rw [← pow_mul]; ring_nf, mul_zero,
      cos_zero, show 1 + 2 * E ^ (2 * (k + 1)) * 1 + (E ^ (2 * (k + 1))) ^ 2 =
        (1 + E ^ (2 * (k + 1))) ^ 2 by ring]
    have := hx k
    have := hx' k
    field_simp
  obtain ⟨hmr, hpr⟩ := p20R1_ratio_prod hm1.hasProd hm0.hasProd hG hr
  refine ⟨hmr, ?_⟩
  rw [he1, jacobiThetaTwoNullTau, he0, hpr, cos_zero,
    show ∀ c s G F : ℂ, c * 1 * G * s * (F / G) = c * s * (G * (F / G)) from
    fun _ _ _ _ => by ring, mul_div_cancel₀ _ hG]

/-- DLMF 20.5.7: `θ₃(z|τ) = θ₃(0|τ) ∏_{n≥1} cos((n-½)πτ + z) cos((n-½)πτ - z)/cos²((n-½)πτ)`. -/
@[dlmf 20.5.E7]
theorem jacobiThetaThreeTau_hasProd_cos (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => cos ((k + 1 / 2) * π * τ + z) * cos ((k + 1 / 2) * π * τ - z) /
        cos ((k + 1 / 2) * π * τ) ^ 2) ∧
      jacobiThetaThreeTau z τ = jacobiThetaThreeNullTau τ *
        ∏' k : ℕ, (cos ((k + 1 / 2) * π * τ + z) * cos ((k + 1 / 2) * π * τ - z) /
        cos ((k + 1 / 2) * π * τ) ^ 2) := by
  obtain ⟨hm1, he1⟩ := jacobiThetaThreeTau_hasProd z hτ
  obtain ⟨hm0, he0⟩ := jacobiThetaThreeTau_hasProd 0 hτ
  set E := cexp (π * I * τ) with hE
  have h3 := (jacobiThetaNullTau_ne_zero hτ).2.1
  have hG : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
      (1 + 2 * E ^ (2 * k + 1) * cos (2 * 0) + E ^ (4 * k + 2))) ≠ 0 := by
    intro h; apply h3; rw [jacobiThetaThreeNullTau, he0, h]
  have hx : ∀ k : ℕ, 1 - E ^ (2 * (k + 1)) ≠ 0 := fun k =>
    one_sub_ne_zero_of_norm_lt_one (p20R1_norm_nome_pow_lt_one hτ (by omega))
  have hy' : ∀ k : ℕ, 1 + E ^ (2 * k + 1) ≠ 0 := fun k => by
    rw [← sub_neg_eq_add]
    exact one_sub_ne_zero_of_norm_lt_one (by rw [norm_neg]; exact p20R1_norm_nome_pow_lt_one hτ (by omega))
  have hyk : ∀ k : ℕ, cexp (2 * I * ((k + 1 / 2) * π * τ)) = E ^ (2 * k + 1) := fun k => by
    rw [hE, ← exp_nat_mul]; congr 1; push_cast; ring
  have hr : ∀ k : ℕ, cos ((k + 1 / 2) * π * τ + z) * cos ((k + 1 / 2) * π * τ - z) /
      cos ((k + 1 / 2) * π * τ) ^ 2 =
      ((1 - E ^ (2 * (k + 1))) * (1 + 2 * E ^ (2 * k + 1) * cos (2 * z) + E ^ (4 * k + 2))) /
        ((1 - E ^ (2 * (k + 1))) * (1 + 2 * E ^ (2 * k + 1) * cos (2 * 0) + E ^ (4 * k + 2)))
      := fun k => by
    rw [p20R1_cos_ratio _ _ (by rw [hyk]; exact hy' k), hyk,
      show E ^ (4 * k + 2) = (E ^ (2 * k + 1)) ^ 2 by rw [← pow_mul]; ring_nf, mul_zero,
      cos_zero, show 1 + 2 * E ^ (2 * k + 1) * 1 + (E ^ (2 * k + 1)) ^ 2 =
        (1 + E ^ (2 * k + 1)) ^ 2 by ring]
    have := hx k
    have := hy' k
    field_simp
  obtain ⟨hmr, hpr⟩ := p20R1_ratio_prod hm1.hasProd hm0.hasProd hG hr
  refine ⟨hmr, ?_⟩
  rw [he1, jacobiThetaThreeNullTau, he0, hpr, mul_div_cancel₀ _ hG]

/-- DLMF 20.5.8: `θ₄(z|τ) = θ₄(0|τ) ∏_{n≥1} sin((n-½)πτ + z) sin((n-½)πτ - z)/sin²((n-½)πτ)`. -/
@[dlmf 20.5.E8]
theorem jacobiThetaFourTau_hasProd_sin (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => sin ((k + 1 / 2) * π * τ + z) * sin ((k + 1 / 2) * π * τ - z) /
        sin ((k + 1 / 2) * π * τ) ^ 2) ∧
      jacobiThetaFourTau z τ = jacobiThetaFourNullTau τ *
        ∏' k : ℕ, (sin ((k + 1 / 2) * π * τ + z) * sin ((k + 1 / 2) * π * τ - z) /
        sin ((k + 1 / 2) * π * τ) ^ 2) := by
  obtain ⟨hm1, he1⟩ := jacobiThetaFourTau_hasProd z hτ
  obtain ⟨hm0, he0⟩ := jacobiThetaFourTau_hasProd 0 hτ
  set E := cexp (π * I * τ) with hE
  have h4 := (jacobiThetaNullTau_ne_zero hτ).2.2
  have hG : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
      (1 - 2 * E ^ (2 * k + 1) * cos (2 * 0) + E ^ (4 * k + 2))) ≠ 0 := by
    intro h; apply h4; rw [jacobiThetaFourNullTau, he0, h]
  have hx : ∀ k : ℕ, 1 - E ^ (2 * (k + 1)) ≠ 0 := fun k =>
    one_sub_ne_zero_of_norm_lt_one (p20R1_norm_nome_pow_lt_one hτ (by omega))
  have hy : ∀ k : ℕ, 1 - E ^ (2 * k + 1) ≠ 0 := fun k =>
    one_sub_ne_zero_of_norm_lt_one (p20R1_norm_nome_pow_lt_one hτ (by omega))
  have hyk : ∀ k : ℕ, cexp (2 * I * ((k + 1 / 2) * π * τ)) = E ^ (2 * k + 1) := fun k => by
    rw [hE, ← exp_nat_mul]; congr 1; push_cast; ring
  have hr : ∀ k : ℕ, sin ((k + 1 / 2) * π * τ + z) * sin ((k + 1 / 2) * π * τ - z) /
      sin ((k + 1 / 2) * π * τ) ^ 2 =
      ((1 - E ^ (2 * (k + 1))) * (1 - 2 * E ^ (2 * k + 1) * cos (2 * z) + E ^ (4 * k + 2))) /
        ((1 - E ^ (2 * (k + 1))) * (1 - 2 * E ^ (2 * k + 1) * cos (2 * 0) + E ^ (4 * k + 2)))
      := fun k => by
    rw [p20R1_sin_ratio _ _ (by rw [hyk]; exact hy k), hyk,
      show E ^ (4 * k + 2) = (E ^ (2 * k + 1)) ^ 2 by rw [← pow_mul]; ring_nf, mul_zero,
      cos_zero, show 1 - 2 * E ^ (2 * k + 1) * 1 + (E ^ (2 * k + 1)) ^ 2 =
        (1 - E ^ (2 * k + 1)) ^ 2 by ring]
    have := hx k
    have := hy k
    field_simp
  obtain ⟨hmr, hpr⟩ := p20R1_ratio_prod hm1.hasProd hm0.hasProd hG hr
  refine ⟨hmr, ?_⟩
  rw [he1, jacobiThetaFourNullTau, he0, hpr, mul_div_cancel₀ _ hG]

/-- DLMF 20.5.9 (Jacobi's triple product): with `p = e^{iπz}`, `q = e^{iπτ}`,
`θ₃(πz|τ) = ∑_{n∈ℤ} p^{2n} q^{n²} = ∏_{n≥1} (1 - q^{2n})(1 + q^{2n-1}p²)(1 + q^{2n-1}p^{-2})`. -/
@[dlmf 20.5.E9]
theorem jacobiThetaThreeTau_triple_product (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => cexp (π * I * z) ^ (2 * n) * cexp (π * I * τ) ^ (n ^ 2))
        (jacobiThetaThreeTau (π * z) τ) ∧
      Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
          (1 + cexp (π * I * τ) ^ (2 * k + 1) * cexp (π * I * z) ^ 2) *
          (1 + cexp (π * I * τ) ^ (2 * k + 1) * (cexp (π * I * z) ^ 2)⁻¹)) ∧
      jacobiThetaThreeTau (π * z) τ =
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
          (1 + cexp (π * I * τ) ^ (2 * k + 1) * cexp (π * I * z) ^ 2) *
          (1 + cexp (π * I * τ) ^ (2 * k + 1) * (cexp (π * I * z) ^ 2)⁻¹)) := by
  have hp : cexp (π * I * z) ^ 2 = cexp (2 * I * (π * z)) := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  have hP := th20_three_hasProd (π * z) hτ
  rw [← hp] at hP
  refine ⟨?_, hP.multipliable, hP.tprod_eq.symm⟩
  convert th20_hasSum_three (π * z) hτ using 1
  funext n
  rw [th20_exp_zpow, th20_exp_zpow, ← exp_add]
  congr 1; push_cast; ring

/-- `‖sin w‖ ≤ e^{|Im w|}` (helper). -/
lemma p20R1_norm_sin_le (w : ℂ) : ‖sin w‖ ≤ Real.exp |w.im| := by
  rw [sin]
  have h1 : ‖cexp (-w * I)‖ = Real.exp w.im := by rw [norm_exp]; simp
  have h2 : ‖cexp (w * I)‖ = Real.exp (-w.im) := by rw [norm_exp]; simp
  have e1 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have e2 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  calc ‖(cexp (-w * I) - cexp (w * I)) * I / 2‖ = ‖cexp (-w * I) - cexp (w * I)‖ / 2 := by
        rw [norm_div, norm_mul, norm_I, mul_one]; simp
    _ ≤ (‖cexp (-w * I)‖ + ‖cexp (w * I)‖) / 2 := by gcongr; exact norm_sub_le _ _
    _ ≤ Real.exp |w.im| := by rw [h1, h2]; linarith

/-- `1 - 2x cos 2z + x² = (1 - x e^{2iz})(1 - x e^{-2iz})` (helper). -/
lemma p20R1_factor (x z : ℂ) :
    1 - 2 * x * cos (2 * z) + x ^ 2 = (1 - x * cexp (2 * I * z)) * (1 - x * (cexp (2 * I * z))⁻¹) := by
  have hc := th20_exp_add_inv z
  have h1 : cexp (2 * I * z) * (cexp (2 * I * z))⁻¹ = 1 := mul_inv_cancel₀ (exp_ne_zero _)
  linear_combination x * hc - x ^ 2 * h1

/-- Lower bound for the norm of a quotient by `(1 - a)(1 - b)` (helper). -/
lemma p20R1_norm_div_le {x a b : ℂ} {ρ : ℝ} (hρ : ρ < 1) (ha : ‖a‖ ≤ ρ) (hb : ‖b‖ ≤ ρ) :
    ‖x / ((1 - a) * (1 - b))‖ ≤ ‖x‖ / (1 - ρ) ^ 2 := by
  have h1 : 1 - ρ ≤ ‖1 - a‖ := by
    have := norm_sub_norm_le (1 : ℂ) a; rw [norm_one] at this; linarith
  have h2 : 1 - ρ ≤ ‖1 - b‖ := by
    have := norm_sub_norm_le (1 : ℂ) b; rw [norm_one] at this; linarith
  have hp : 0 < 1 - ρ := by linarith
  rw [norm_div, norm_mul]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
  rw [sq]; exact mul_le_mul h1 h2 hp.le (by linarith)

/-- `‖e^{±2iz}‖ ≤ e^{2|Im z|}` (helper). -/
lemma p20R1_norm_exp_two_I (z : ℂ) :
    ‖cexp (2 * I * z)‖ ≤ Real.exp (2 * |z.im|) ∧ ‖(cexp (2 * I * z))⁻¹‖ ≤ Real.exp (2 * |z.im|) := by
  rw [norm_inv, norm_exp]
  simp only [mul_re, re_ofNat, I_re, mul_zero, im_ofNat, I_im, zero_mul, sub_zero, mul_im,
    zero_sub]
  constructor
  · exact Real.exp_le_exp.mpr (by linarith [neg_abs_le z.im])
  · rw [← Real.exp_neg]; exact Real.exp_le_exp.mpr (by linarith [le_abs_self z.im])


/-- Bounds for `x/(1 ∓ 2x cos 2z + x²)` (helper). -/
lemma p20R1_bound_quot {x z : ℂ} {R ρ : ℝ} (hx : ‖x‖ ≤ R) (hR : R * Real.exp (2 * |z.im|) ≤ ρ)
    (hρ : ρ < 1) :
    ‖x / (1 - 2 * x * cos (2 * z) + x ^ 2)‖ ≤ ‖x‖ / (1 - ρ) ^ 2 ∧
      ‖x / (1 + 2 * x * cos (2 * z) + x ^ 2)‖ ≤ ‖x‖ / (1 - ρ) ^ 2 := by
  obtain ⟨e1, e2⟩ := p20R1_norm_exp_two_I z
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hx
  have b1 : ‖x * cexp (2 * I * z)‖ ≤ ρ := by
    rw [norm_mul]; exact (mul_le_mul hx e1 (norm_nonneg _) hR0).trans hR
  have b2 : ‖x * (cexp (2 * I * z))⁻¹‖ ≤ ρ := by
    rw [norm_mul]; exact (mul_le_mul hx e2 (norm_nonneg _) hR0).trans hR
  have b3 : ‖-x * cexp (2 * I * z)‖ ≤ ρ := by rwa [neg_mul, norm_neg]
  have b4 : ‖-x * (cexp (2 * I * z))⁻¹‖ ≤ ρ := by rwa [neg_mul, norm_neg]
  refine ⟨?_, ?_⟩
  · rw [p20R1_factor]; exact p20R1_norm_div_le hρ b1 b2
  · rw [show 1 + 2 * x * cos (2 * z) + x ^ 2 = 1 - 2 * (-x) * cos (2 * z) + (-x) ^ 2 by ring,
      p20R1_factor]
    exact p20R1_norm_div_le hρ b3 b4

/-- Bound for `x/(1 - y) sin(2(m+1)z)` (helper). -/
lemma p20R1_bound_sin {x y z : ℂ} (m : ℕ) (hy : ‖y‖ < 1) :
    ‖x / (1 - y) * sin (2 * ((m : ℂ) + 1) * z)‖ ≤
      ‖x‖ / (1 - ‖y‖) * Real.exp (2 * |z.im|) ^ (m + 1) := by
  have h1 : 1 - ‖y‖ ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y; rw [norm_one] at this; linarith
  have hs := p20R1_norm_sin_le (2 * ((m : ℂ) + 1) * z)
  have him : (2 * ((m : ℂ) + 1) * z).im = 2 * ((m : ℝ) + 1) * z.im := by simp
  rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ((m : ℝ) + 1)),
    show 2 * ((m : ℝ) + 1) * |z.im| = ((m + 1 : ℕ) : ℝ) * (2 * |z.im|) by push_cast; ring,
    Real.exp_nat_mul] at hs
  rw [norm_mul, norm_div]
  gcongr


/-- `sin (2(m+1)z) = (u^{m+1} - u^{-(m+1)})/(2i)` with `u = e^{2iz}` (helper). -/
lemma p20R1_sin_pow (z : ℂ) (m : ℕ) :
    sin (2 * ((m : ℂ) + 1) * z) =
      (cexp (2 * I * z) ^ (m + 1) - (cexp (2 * I * z))⁻¹ ^ (m + 1)) / (2 * I) := by
  rw [inv_pow, ← exp_nat_mul, ← exp_neg, sin]
  have hI : (2 * I) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  rw [eq_div_iff hI]
  have e1 : -(2 * ((m : ℂ) + 1) * z) * I = ((m + 1 : ℕ) : ℂ) * -(2 * I * z) := by push_cast; ring
  have e2 : 2 * ((m : ℂ) + 1) * z * I = ((m + 1 : ℕ) : ℂ) * (2 * I * z) := by push_cast; ring
  rw [e1, e2, mul_neg]
  linear_combination (cexp (-(↑(m + 1) * (2 * I * z))) - cexp (↑(m + 1) * (2 * I * z))) * I_sq

/-- Fourier expansion of `4a sin 2z/(1 - 2a cos 2z + a²)` (helper). -/
lemma p20R1_term_hasSum {a z : ℂ} (h1 : ‖a * cexp (2 * I * z)‖ < 1)
    (h2 : ‖a * (cexp (2 * I * z))⁻¹‖ < 1) :
    HasSum (fun m : ℕ => 4 * a ^ (m + 1) * sin (2 * ((m : ℂ) + 1) * z))
      (4 * a * sin (2 * z) / (1 - 2 * a * cos (2 * z) + a ^ 2)) := by
  set u := cexp (2 * I * z) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  have n1 := one_sub_ne_zero_of_norm_lt_one h1
  have n2 := one_sub_ne_zero_of_norm_lt_one h2
  have g1 := (hasSum_geometric_of_norm_lt_one h1).mul_left (a * u)
  have g2 := (hasSum_geometric_of_norm_lt_one h2).mul_left (a * u⁻¹)
  have hI : (2 * I) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  have hg := (g1.sub g2).mul_left (4 / (2 * I))
  convert hg using 1
  · funext m
    rw [p20R1_sin_pow]
    simp only [mul_pow]
    ring
  · have hs : sin (2 * z) = (u - u⁻¹) / (2 * I) := by
      have := p20R1_sin_pow z 0; simpa using this
    rw [p20R1_factor, ← hu, hs]
    have n2' : u - a ≠ 0 := by
      intro h; apply n2; field_simp; linear_combination h
    field_simp
    ring


/-- The product `∏ (1 - 2bQ^k cos 2w + (bQ^k)²)` (helper for 20.5.10–20.5.13). -/
def p20R1_F (b Q w : ℂ) : ℂ := ∏' k : ℕ, (1 - 2 * (b * Q ^ k) * cos (2 * w) + (b * Q ^ k) ^ 2)

/-- Logarithmic derivative of `p20R1_F` and its Fourier expansion (helper for 20.5.10–20.5.13). -/
lemma p20R1_logDeriv_core {b Q z : ℂ} (hQ : ‖Q‖ < 1) (hb : ‖b‖ * Real.exp (2 * |z.im|) < 1) :
    p20R1_F b Q z ≠ 0 ∧ DifferentiableAt ℂ (p20R1_F b Q) z ∧
    HasSum (fun k : ℕ => 4 * (b * Q ^ k) * sin (2 * z) /
        (1 - 2 * (b * Q ^ k) * cos (2 * z) + (b * Q ^ k) ^ 2)) (logDeriv (p20R1_F b Q) z) ∧
    HasSum (fun m : ℕ => 4 * (b ^ (m + 1) / (1 - Q ^ (m + 1))) * sin (2 * ((m : ℂ) + 1) * z))
      (logDeriv (p20R1_F b Q) z) := by
  set s := ‖b‖ * Real.exp (2 * |z.im|) with hs
  have hs0 : 0 ≤ s := by positivity
  set c := |z.im| + Real.log (2 / (1 + s)) / 2 with hc
  have hlog : 0 < Real.log (2 / (1 + s)) :=
    Real.log_pos (by rw [lt_div_iff₀ (by linarith)]; linarith)
  have hzc : |z.im| < c := by rw [hc]; linarith
  have hbc : ‖b‖ * Real.exp (2 * c) < 1 := by
    have : Real.exp (2 * c) = Real.exp (2 * |z.im|) * (2 / (1 + s)) := by
      rw [hc, show 2 * (|z.im| + Real.log (2 / (1 + s)) / 2) =
        2 * |z.im| + Real.log (2 / (1 + s)) by ring, Real.exp_add, Real.exp_log (by positivity)]
    rw [this, ← mul_assoc, ← hs, mul_div_assoc', div_lt_one (by linarith)]; linarith
  set t := ‖b‖ * Real.exp (2 * c) with ht
  set U : Set ℂ := {w | |w.im| < c} with hUdef
  have hU : IsOpen U := isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  have hzU : z ∈ U := hzc
  have hQ0 : 0 ≤ ‖Q‖ := norm_nonneg _
  have hak1 : ∀ k : ℕ, ‖b * Q ^ k‖ ≤ ‖b‖ := fun k => by
    rw [norm_mul, norm_pow]; exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hQ0 hQ.le)
  have hexpU : ∀ w ∈ U, Real.exp (2 * |w.im|) ≤ Real.exp (2 * c) := fun w hw =>
    Real.exp_le_exp.mpr (by have : |w.im| < c := hw; linarith)
  have hfac : ∀ k : ℕ, ∀ w ∈ U, ‖b * Q ^ k * cexp (2 * I * w)‖ ≤ ‖b * Q ^ k‖ * Real.exp (2 * c) ∧
      ‖b * Q ^ k * (cexp (2 * I * w))⁻¹‖ ≤ ‖b * Q ^ k‖ * Real.exp (2 * c) := by
    intro k w hw
    obtain ⟨e1, e2⟩ := p20R1_norm_exp_two_I w
    rw [norm_mul (b * Q ^ k), norm_mul (b * Q ^ k)]
    exact ⟨mul_le_mul_of_nonneg_left (e1.trans (hexpU w hw)) (norm_nonneg _),
      mul_le_mul_of_nonneg_left (e2.trans (hexpU w hw)) (norm_nonneg _)⟩
  have hlt : ∀ k : ℕ, ‖b * Q ^ k‖ * Real.exp (2 * c) < 1 := fun k =>
    (mul_le_mul_of_nonneg_right (hak1 k) (Real.exp_pos _).le).trans_lt hbc
  have hne : ∀ k : ℕ, ∀ w ∈ U, 1 + (-2 * (b * Q ^ k) * cos (2 * w) + (b * Q ^ k) ^ 2) ≠ 0 := by
    intro k w hw
    rw [← add_assoc, show (1 : ℂ) + -2 * (b * Q ^ k) * cos (2 * w) =
      1 - 2 * (b * Q ^ k) * cos (2 * w) by ring, p20R1_factor]
    obtain ⟨e1, e2⟩ := hfac k w hw
    exact mul_ne_zero (one_sub_ne_zero_of_norm_lt_one (e1.trans_lt (hlt k)))
      (one_sub_ne_zero_of_norm_lt_one (e2.trans_lt (hlt k)))
  -- uniform bound for the factors minus one
  set g : ℕ → ℂ → ℂ := fun k w => -2 * (b * Q ^ k) * cos (2 * w) + (b * Q ^ k) ^ 2 with hg
  have hgb : ∀ k : ℕ, ∀ w ∈ U, ‖g k w‖ ≤ (2 * Real.exp (2 * c) + ‖b‖) * ‖b‖ * ‖Q‖ ^ k := by
    intro k w hw
    obtain ⟨e1, e2⟩ := hfac k w hw
    have hcos : -2 * (b * Q ^ k) * cos (2 * w) =
        -(b * Q ^ k * cexp (2 * I * w)) - b * Q ^ k * (cexp (2 * I * w))⁻¹ := by
      linear_combination (b * Q ^ k) * th20_exp_add_inv w
    have hn : ‖b * Q ^ k‖ = ‖b‖ * ‖Q‖ ^ k := by rw [norm_mul, norm_pow]
    calc ‖g k w‖ ≤ ‖b * Q ^ k * cexp (2 * I * w)‖ + ‖b * Q ^ k * (cexp (2 * I * w))⁻¹‖ +
          ‖b * Q ^ k‖ * ‖b * Q ^ k‖ := by
          simp only [hg, hcos]
          refine (norm_add_le _ _).trans ?_
          rw [norm_pow, sq]
          gcongr
          refine (norm_sub_le _ _).trans ?_
          rw [norm_neg]
      _ ≤ ‖b * Q ^ k‖ * Real.exp (2 * c) + ‖b * Q ^ k‖ * Real.exp (2 * c) +
          ‖b * Q ^ k‖ * ‖b‖ := by gcongr; exact hak1 k
      _ = (2 * Real.exp (2 * c) + ‖b‖) * ‖b‖ * ‖Q‖ ^ k := by rw [hn]; ring
  have hsumu : Summable (fun k : ℕ => (2 * Real.exp (2 * c) + ‖b‖) * ‖b‖ * ‖Q‖ ^ k) :=
    (summable_geometric_of_lt_one hQ0 hQ).mul_left _
  have hfun : (fun k w => 1 - 2 * (b * Q ^ k) * cos (2 * w) + (b * Q ^ k) ^ 2) =
      fun k w => 1 + g k w := by funext k w; simp only [hg]; ring
  have hFdef : p20R1_F b Q = fun w => ∏' k : ℕ, (1 + g k w) := by
    funext w; simp only [p20R1_F, hg]; congr 1; funext k; ring
  have hloc : HasProdLocallyUniformlyOn (fun k w => 1 + g k w) (fun w => ∏' k, (1 + g k w)) U :=
    hsumu.hasProdLocallyUniformlyOn_nat_one_add hU (.of_forall fun k w hw => hgb k w hw)
      (fun k => by simp only [hg]; fun_prop)
  have hdiff : DifferentiableOn ℂ (fun w => ∏' k, (1 + g k w)) U :=
    hloc.differentiableOn (.of_forall fun s => by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun _ _ => by
        simp only [hg]; fun_prop)) hU
  have hFz : p20R1_F b Q z ≠ 0 := by
    rw [hFdef]
    exact tprod_one_add_ne_zero_of_summable (f := fun k => g k z) (fun k => hne k z hzU)
      (hsumu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hgb k z hzU))
  -- the double series
  obtain ⟨G, hG⟩ : ∃ G : ℕ × ℕ → ℂ,
      G = fun p => 4 * (b * Q ^ p.1) ^ (p.2 + 1) * sin (2 * ((p.2 : ℂ) + 1) * z) := ⟨_, rfl⟩
  have hGs : Summable G := by
    have hsm : Summable (fun p : ℕ × ℕ => ‖Q‖ ^ p.1 * (4 * s ^ (p.2 + 1))) :=
      (summable_geometric_of_lt_one hQ0 hQ).mul_of_nonneg
        ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hs0 hb) |>.mul_left 4)
        (fun _ => by positivity) (fun _ => by positivity)
    refine Summable.of_norm_bounded hsm (fun p => ?_)
    obtain ⟨k, m⟩ := p
    rw [hG]
    have hsin := p20R1_norm_sin_le (2 * ((m : ℂ) + 1) * z)
    have him : (2 * ((m : ℂ) + 1) * z).im = 2 * ((m : ℝ) + 1) * z.im := by simp
    rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ((m : ℝ) + 1)),
      show 2 * ((m : ℝ) + 1) * |z.im| = ((m + 1 : ℕ) : ℝ) * (2 * |z.im|) by push_cast; ring,
      Real.exp_nat_mul] at hsin
    have hq : ‖Q‖ ^ (k * (m + 1)) ≤ ‖Q‖ ^ k :=
      pow_le_pow_of_le_one hQ0 hQ.le (Nat.le_mul_of_pos_right _ (by omega))
    rw [norm_mul, norm_mul, norm_pow, norm_mul, norm_pow, mul_pow, ← pow_mul]
    have : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [this, hs, mul_pow]
    calc 4 * (‖b‖ ^ (m + 1) * ‖Q‖ ^ (k * (m + 1))) * ‖sin (2 * ((m : ℂ) + 1) * z)‖
        ≤ 4 * (‖b‖ ^ (m + 1) * ‖Q‖ ^ k) * Real.exp (2 * |z.im|) ^ (m + 1) := by gcongr
      _ = ‖Q‖ ^ k * (4 * (‖b‖ ^ (m + 1) * Real.exp (2 * |z.im|) ^ (m + 1))) := by ring
  have hT := hGs.hasSum
  -- fibres over k
  have hk : HasSum (fun k : ℕ => 4 * (b * Q ^ k) * sin (2 * z) /
      (1 - 2 * (b * Q ^ k) * cos (2 * z) + (b * Q ^ k) ^ 2)) (∑' p, G p) := by
    refine hT.prod_fiberwise (fun k => ?_)
    obtain ⟨e1, e2⟩ := hfac k z hzU
    have := p20R1_term_hasSum (e1.trans_lt (hlt k)) (e2.trans_lt (hlt k))
    rw [hG]; exact this
  -- fibres over m
  have hm : HasSum (fun m : ℕ => 4 * (b ^ (m + 1) / (1 - Q ^ (m + 1))) *
      sin (2 * ((m : ℂ) + 1) * z)) (∑' p, G p) := by
    have hT' : HasSum (G ∘ Prod.swap) (∑' p, G p) := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hT
    refine hT'.prod_fiberwise (fun m => ?_)
    have hQm : ‖Q ^ (m + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ hQ0 hQ (by omega)
    convert ((hasSum_geometric_of_norm_lt_one hQm).mul_left
      (4 * b ^ (m + 1) * sin (2 * ((m : ℂ) + 1) * z))) using 1
    · funext k; rw [hG]; simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
      rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
    · ring
  -- logarithmic derivative of each factor
  have hlk : ∀ k : ℕ, logDeriv (fun w => 1 + g k w) z = 4 * (b * Q ^ k) * sin (2 * z) /
      (1 - 2 * (b * Q ^ k) * cos (2 * z) + (b * Q ^ k) ^ 2) := by
    intro k
    have hd : HasDerivAt (fun w => 1 + g k w) (4 * (b * Q ^ k) * sin (2 * z)) z := by
      have h0 : HasDerivAt (fun w : ℂ => 2 * w) 2 z := by
        simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
      have h1 := h0.ccos
      have h2 := ((h1.const_mul (-2 * (b * Q ^ k))).add_const ((b * Q ^ k) ^ 2)).const_add 1
      rw [hg]
      convert h2 using 1
      ring
    rw [logDeriv_apply, hd.deriv, hg]
    congr 1; ring
  have hL : logDeriv (p20R1_F b Q) z = ∑' k, logDeriv (fun w => 1 + g k w) z := by
    rw [hFdef]
    refine logDeriv_tprod_eq_tsum hU hzU (fun k => hne k z hzU)
      (fun k => by simp only [hg]; fun_prop) ?_ hloc.multipliableLocallyUniformlyOn ?_
    · simp only [hlk]; exact hk.summable
    · have := hFz; rw [hFdef] at this; exact this
  have hLT : logDeriv (p20R1_F b Q) z = ∑' p, G p := by
    rw [hL]; simp only [hlk]; exact hk.tsum_eq
  refine ⟨hFz, ?_, hLT ▸ hk, hLT ▸ hm⟩
  rw [hFdef]; exact (hdiff z hzU).differentiableAt (hU.mem_nhds hzU)

/-- Multipliability of the factors of `p20R1_F` (helper). -/
lemma p20R1_F_mult (b Q w : ℂ) (hQ : ‖Q‖ < 1) :
    Multipliable (fun k : ℕ => 1 - 2 * (b * Q ^ k) * cos (2 * w) + (b * Q ^ k) ^ 2) := by
  have hs : Summable (fun k : ℕ => ‖-2 * (b * Q ^ k) * cos (2 * w) + (b * Q ^ k) ^ 2‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one (norm_nonneg _) hQ).mul_left
        (2 * ‖b‖ * ‖cos (2 * w)‖ + ‖b‖ ^ 2))
    have hq : ‖Q‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hQ.le
    have hq2 : (‖Q‖ ^ k) ^ 2 ≤ ‖Q‖ ^ k := by
      rw [sq]; exact mul_le_of_le_one_left (by positivity) hq
    calc ‖-2 * (b * Q ^ k) * cos (2 * w) + (b * Q ^ k) ^ 2‖
        ≤ ‖-2 * (b * Q ^ k) * cos (2 * w)‖ + ‖(b * Q ^ k) ^ 2‖ := norm_add_le _ _
      _ = 2 * ‖b‖ * ‖cos (2 * w)‖ * ‖Q‖ ^ k + ‖b‖ ^ 2 * (‖Q‖ ^ k) ^ 2 := by
          simp only [norm_mul, norm_pow, norm_neg]; norm_num; ring
      _ ≤ 2 * ‖b‖ * ‖cos (2 * w)‖ * ‖Q‖ ^ k + ‖b‖ ^ 2 * ‖Q‖ ^ k := by gcongr
      _ = (2 * ‖b‖ * ‖cos (2 * w)‖ + ‖b‖ ^ 2) * ‖Q‖ ^ k := by ring
  have := multipliable_one_add_of_summable hs
  convert this using 2 with k; ring

/-- `∏ (1 - q^{2n})` is multipliable and nonzero (helper). -/
lemma p20R1_P_mult_ne {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => 1 - cexp (π * I * τ) ^ (2 * (k + 1))) ∧
      ∏' k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) ≠ 0 := by
  have hs : Summable (fun k : ℕ => ‖-(cexp (π * I * τ) ^ (2 * (k + 1)))‖) := by
    have h := th20_norm_nome_sq_lt_one hτ
    simp only [norm_neg, pow_mul, norm_pow] at h ⊢
    exact (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by positivity) h)
  have hne : ∀ k : ℕ, 1 + -(cexp (π * I * τ) ^ (2 * (k + 1))) ≠ 0 := fun k => by
    rw [← sub_eq_add_neg]; exact one_sub_ne_zero_of_norm_lt_one
      (p20R1_norm_nome_pow_lt_one hτ (by omega))
  have h1 := multipliable_one_add_of_summable hs
  have h2 := tprod_one_add_ne_zero_of_summable hne hs
  simp only [← sub_eq_add_neg] at h1 h2
  exact ⟨h1, h2⟩

/-- `(K h F)'/(K h F) = h'/h + F'/F` (helper). -/
lemma p20R1_logDeriv_shape {K h' z : ℂ} {h F : ℂ → ℂ} (hK : K ≠ 0) (hh : HasDerivAt h h' z)
    (hF : DifferentiableAt ℂ F z) (hhz : h z ≠ 0) (hFz : F z ≠ 0) :
    deriv (fun w => K * h w * F w) z / (K * h z * F z) = h' / h z + logDeriv F z := by
  have hd : HasDerivAt (fun w => K * h w * F w) (K * h' * F z + K * h z * deriv F z) z :=
    (hh.const_mul K).mul hF.hasDerivAt
  rw [hd.deriv, logDeriv_apply]
  field_simp

/-! ### §20.5(ii) Logarithmic derivatives -/

/-- DLMF 20.5.10: for `|Im z| < π Im τ`,
`θ₁'/θ₁ - cot z = 4 sin 2z ∑ q^{2n}/(1 - 2q^{2n} cos 2z + q^{4n})
  = 4 ∑ q^{2n}/(1 - q^{2n}) sin 2nz`. -/
@[dlmf 20.5.E10]
theorem jacobiThetaOneTau_logDeriv {z τ : ℂ} (hτ : 0 < τ.im) (hz : |z.im| < π * τ.im) :
    HasSum (fun k : ℕ => 4 * sin (2 * z) * (cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))))
      (deriv (fun w => jacobiThetaOneTau w τ) z / jacobiThetaOneTau z τ - cot z) ∧
    HasSum (fun k : ℕ => 4 * (cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * sin (2 * (k + 1) * z))
      (deriv (fun w => jacobiThetaOneTau w τ) z / jacobiThetaOneTau z τ - cot z) := by
  set E := cexp (π * I * τ) with hE
  have hEn : ‖E‖ = Real.exp (-(π * τ.im)) := by rw [hE, norm_exp]; simp
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  have hb : ‖E ^ 2‖ * Real.exp (2 * |z.im|) < 1 := by
    rw [norm_pow, hEn, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by push_cast; linarith)
  obtain ⟨hFz, hFd, hS1, hS2⟩ := p20R1_logDeriv_core hQ hb
  obtain ⟨hPm, hPne⟩ := p20R1_P_mult_ne hτ
  have hpow : ∀ k : ℕ, E ^ 2 * (E ^ 2) ^ k = E ^ (2 * (k + 1)) := fun k => by
    rw [← pow_mul, ← pow_add]; ring_nf
  have hpow4 : ∀ k : ℕ, E ^ (4 * (k + 1)) = (E ^ (2 * (k + 1))) ^ 2 := fun k => by
    rw [← pow_mul]; ring_nf
  set P := ∏' k : ℕ, (1 - E ^ (2 * (k + 1))) with hP
  set K := 2 * cexp (π * I * τ / 4) with hK
  have hK0 : K ≠ 0 := mul_ne_zero two_ne_zero (exp_ne_zero _)
  have hfun : (fun w => jacobiThetaOneTau w τ) =
      fun w => (K * P) * sin w * p20R1_F (E ^ 2) (E ^ 2) w := by
    funext w
    rw [(jacobiThetaOneTau_hasProd w hτ).2]
    have hc : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
        (1 - 2 * E ^ (2 * (k + 1)) * cos (2 * w) + E ^ (4 * (k + 1)))) =
        ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
          (1 - 2 * (E ^ 2 * (E ^ 2) ^ k) * cos (2 * w) + (E ^ 2 * (E ^ 2) ^ k) ^ 2)) :=
      tprod_congr fun k => by rw [hpow, hpow4]
    rw [hc, hPm.tprod_mul (p20R1_F_mult _ _ w hQ), p20R1_F]
    ring
  have hL : deriv (fun w => jacobiThetaOneTau w τ) z / jacobiThetaOneTau z τ - cot z =
      logDeriv (p20R1_F (E ^ 2) (E ^ 2)) z := by
    by_cases hs : sin z = 0
    · have h2 : sin (2 * z) = 0 := by rw [sin_two_mul, hs]; ring
      have h0 : logDeriv (p20R1_F (E ^ 2) (E ^ 2)) z = 0 :=
        hS1.unique (by simp [h2])
      rw [h0, show jacobiThetaOneTau z τ = K * P * sin z * p20R1_F (E ^ 2) (E ^ 2) z from
        congrFun hfun z, hs, cot_eq_cos_div_sin, hs]
      simp
    · rw [show jacobiThetaOneTau z τ = K * P * sin z * p20R1_F (E ^ 2) (E ^ 2) z from
        congrFun hfun z, hfun, p20R1_logDeriv_shape (mul_ne_zero hK0 hPne) (hasDerivAt_sin z) hFd hs hFz,
        cot_eq_cos_div_sin]
      ring
  rw [hL]
  constructor
  · convert hS1 using 1; funext k; rw [hpow, hpow4]; ring
  · convert hS2 using 1; funext k; simp only [← pow_mul]

/-- DLMF 20.5.11: for `|Im z| < π Im τ`,
`θ₂'/θ₂ + tan z = -4 sin 2z ∑ q^{2n}/(1 + 2q^{2n} cos 2z + q^{4n})
  = 4 ∑ (-1)ⁿ q^{2n}/(1 - q^{2n}) sin 2nz`. -/
@[dlmf 20.5.E11]
theorem jacobiThetaTwoTau_logDeriv {z τ : ℂ} (hτ : 0 < τ.im) (hz : |z.im| < π * τ.im) :
    HasSum (fun k : ℕ => -4 * sin (2 * z) * (cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 + 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))))
      (deriv (fun w => jacobiThetaTwoTau w τ) z / jacobiThetaTwoTau z τ + tan z) ∧
    HasSum (fun k : ℕ => 4 * (-1 : ℂ) ^ (k + 1) * (cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * sin (2 * (k + 1) * z))
      (deriv (fun w => jacobiThetaTwoTau w τ) z / jacobiThetaTwoTau z τ + tan z) := by
  set E := cexp (π * I * τ) with hE
  have hEn : ‖E‖ = Real.exp (-(π * τ.im)) := by rw [hE, norm_exp]; simp
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  have hb : ‖-E ^ 2‖ * Real.exp (2 * |z.im|) < 1 := by
    rw [norm_neg, norm_pow, hEn, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by push_cast; linarith)
  obtain ⟨hFz, hFd, hS1, hS2⟩ := p20R1_logDeriv_core hQ hb
  obtain ⟨hPm, hPne⟩ := p20R1_P_mult_ne hτ
  have hpow : ∀ k : ℕ, -E ^ 2 * (E ^ 2) ^ k = -E ^ (2 * (k + 1)) := fun k => by
    rw [neg_mul, ← pow_mul, ← pow_add]; ring_nf
  have hpow4 : ∀ k : ℕ, E ^ (4 * (k + 1)) = (E ^ (2 * (k + 1))) ^ 2 := fun k => by
    rw [← pow_mul]; ring_nf
  set P := ∏' k : ℕ, (1 - E ^ (2 * (k + 1))) with hP
  set K := 2 * cexp (π * I * τ / 4) with hK
  have hK0 : K ≠ 0 := mul_ne_zero two_ne_zero (exp_ne_zero _)
  have hfun : (fun w => jacobiThetaTwoTau w τ) =
      fun w => (K * P) * cos w * p20R1_F (-E ^ 2) (E ^ 2) w := by
    funext w
    rw [(jacobiThetaTwoTau_hasProd w hτ).2]
    have hc : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
        (1 + 2 * E ^ (2 * (k + 1)) * cos (2 * w) + E ^ (4 * (k + 1)))) =
        ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
          (1 - 2 * (-E ^ 2 * (E ^ 2) ^ k) * cos (2 * w) + (-E ^ 2 * (E ^ 2) ^ k) ^ 2)) :=
      tprod_congr fun k => by rw [hpow, hpow4]; ring
    rw [hc, hPm.tprod_mul (p20R1_F_mult _ _ w hQ), p20R1_F]
    ring
  have hL : deriv (fun w => jacobiThetaTwoTau w τ) z / jacobiThetaTwoTau z τ + tan z =
      logDeriv (p20R1_F (-E ^ 2) (E ^ 2)) z := by
    by_cases hs : cos z = 0
    · have h2 : sin (2 * z) = 0 := by rw [sin_two_mul, hs]; ring
      have h0 : logDeriv (p20R1_F (-E ^ 2) (E ^ 2)) z = 0 := hS1.unique (by simp [h2])
      rw [h0, show jacobiThetaTwoTau z τ = K * P * cos z * p20R1_F (-E ^ 2) (E ^ 2) z from
        congrFun hfun z, hs, tan_eq_sin_div_cos, hs]
      simp
    · rw [show jacobiThetaTwoTau z τ = K * P * cos z * p20R1_F (-E ^ 2) (E ^ 2) z from
        congrFun hfun z, hfun, p20R1_logDeriv_shape (mul_ne_zero hK0 hPne) (hasDerivAt_cos z)
        hFd hs hFz, tan_eq_sin_div_cos]
      ring
  rw [hL]
  constructor
  · convert hS1 using 1; funext k; rw [hpow, hpow4]; ring
  · convert hS2 using 1; funext k; rw [neg_pow (E ^ 2), ← pow_mul]; ring

/-- DLMF 20.5.12: for `|Im z| < π Im τ / 2`,
`θ₃'/θ₃ = -4 sin 2z ∑ q^{2n-1}/(1 + 2q^{2n-1} cos 2z + q^{4n-2})
  = 4 ∑ (-1)ⁿ qⁿ/(1 - q^{2n}) sin 2nz`. -/
@[dlmf 20.5.E12]
theorem jacobiThetaThreeTau_logDeriv {z τ : ℂ} (hτ : 0 < τ.im) (hz : |z.im| < π * τ.im / 2) :
    HasSum (fun k : ℕ => -4 * sin (2 * z) * (cexp (π * I * τ) ^ (2 * k + 1) /
        (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))))
      (deriv (fun w => jacobiThetaThreeTau w τ) z / jacobiThetaThreeTau z τ) ∧
    HasSum (fun k : ℕ => 4 * (-1 : ℂ) ^ (k + 1) * (cexp (π * I * τ) ^ (k + 1) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * sin (2 * (k + 1) * z))
      (deriv (fun w => jacobiThetaThreeTau w τ) z / jacobiThetaThreeTau z τ) := by
  set E := cexp (π * I * τ) with hE
  have hEn : ‖E‖ = Real.exp (-(π * τ.im)) := by rw [hE, norm_exp]; simp
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  have hb : ‖-E‖ * Real.exp (2 * |z.im|) < 1 := by
    rw [norm_neg, hEn, ← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  obtain ⟨hFz, hFd, hS1, hS2⟩ := p20R1_logDeriv_core hQ hb
  obtain ⟨hPm, hPne⟩ := p20R1_P_mult_ne hτ
  have hpow : ∀ k : ℕ, -E * (E ^ 2) ^ k = -E ^ (2 * k + 1) := fun k => by
    rw [neg_mul, ← pow_mul, ← pow_succ']
  have hpow4 : ∀ k : ℕ, E ^ (4 * k + 2) = (E ^ (2 * k + 1)) ^ 2 := fun k => by
    rw [← pow_mul]; ring_nf
  set P := ∏' k : ℕ, (1 - E ^ (2 * (k + 1))) with hP
  have hfun : (fun w => jacobiThetaThreeTau w τ) =
      fun w => P * (fun _ => (1 : ℂ)) w * p20R1_F (-E) (E ^ 2) w := by
    funext w
    rw [(jacobiThetaThreeTau_hasProd w hτ).2]
    have hc : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
        (1 + 2 * E ^ (2 * k + 1) * cos (2 * w) + E ^ (4 * k + 2))) =
        ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
          (1 - 2 * (-E * (E ^ 2) ^ k) * cos (2 * w) + (-E * (E ^ 2) ^ k) ^ 2)) :=
      tprod_congr fun k => by rw [hpow, hpow4]; ring
    rw [hc, hPm.tprod_mul (p20R1_F_mult _ _ w hQ), p20R1_F]
    ring
  have hL : deriv (fun w => jacobiThetaThreeTau w τ) z / jacobiThetaThreeTau z τ =
      logDeriv (p20R1_F (-E) (E ^ 2)) z := by
    rw [show jacobiThetaThreeTau z τ = P * (fun _ => (1 : ℂ)) z * p20R1_F (-E) (E ^ 2) z from
      congrFun hfun z, hfun, p20R1_logDeriv_shape hPne (hasDerivAt_const z (1 : ℂ))
      hFd one_ne_zero hFz]
    ring
  rw [hL]
  constructor
  · convert hS1 using 1; funext k; rw [hpow, hpow4]; ring
  · convert hS2 using 1; funext k; rw [neg_pow E, ← pow_mul]; ring

/-- DLMF 20.5.13: for `|Im z| < π Im τ / 2`,
`θ₄'/θ₄ = 4 sin 2z ∑ q^{2n-1}/(1 - 2q^{2n-1} cos 2z + q^{4n-2}) = 4 ∑ qⁿ/(1 - q^{2n}) sin 2nz`. -/
@[dlmf 20.5.E13]
theorem jacobiThetaFourTau_logDeriv {z τ : ℂ} (hτ : 0 < τ.im) (hz : |z.im| < π * τ.im / 2) :
    HasSum (fun k : ℕ => 4 * sin (2 * z) * (cexp (π * I * τ) ^ (2 * k + 1) /
        (1 - 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))))
      (deriv (fun w => jacobiThetaFourTau w τ) z / jacobiThetaFourTau z τ) ∧
    HasSum (fun k : ℕ => 4 * (cexp (π * I * τ) ^ (k + 1) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * sin (2 * (k + 1) * z))
      (deriv (fun w => jacobiThetaFourTau w τ) z / jacobiThetaFourTau z τ) := by
  set E := cexp (π * I * τ) with hE
  have hEn : ‖E‖ = Real.exp (-(π * τ.im)) := by rw [hE, norm_exp]; simp
  have hQ : ‖E ^ 2‖ < 1 := th20_norm_nome_sq_lt_one hτ
  have hb : ‖E‖ * Real.exp (2 * |z.im|) < 1 := by
    rw [hEn, ← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  obtain ⟨hFz, hFd, hS1, hS2⟩ := p20R1_logDeriv_core hQ hb
  obtain ⟨hPm, hPne⟩ := p20R1_P_mult_ne hτ
  have hpow : ∀ k : ℕ, E * (E ^ 2) ^ k = E ^ (2 * k + 1) := fun k => by
    rw [← pow_mul, ← pow_succ']
  have hpow4 : ∀ k : ℕ, E ^ (4 * k + 2) = (E ^ (2 * k + 1)) ^ 2 := fun k => by
    rw [← pow_mul]; ring_nf
  set P := ∏' k : ℕ, (1 - E ^ (2 * (k + 1))) with hP
  have hfun : (fun w => jacobiThetaFourTau w τ) =
      fun w => P * (fun _ => (1 : ℂ)) w * p20R1_F E (E ^ 2) w := by
    funext w
    rw [(jacobiThetaFourTau_hasProd w hτ).2]
    have hc : ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
        (1 - 2 * E ^ (2 * k + 1) * cos (2 * w) + E ^ (4 * k + 2))) =
        ∏' k : ℕ, ((1 - E ^ (2 * (k + 1))) *
          (1 - 2 * (E * (E ^ 2) ^ k) * cos (2 * w) + (E * (E ^ 2) ^ k) ^ 2)) :=
      tprod_congr fun k => by rw [hpow, hpow4]
    rw [hc, hPm.tprod_mul (p20R1_F_mult _ _ w hQ), p20R1_F]
    ring
  have hL : deriv (fun w => jacobiThetaFourTau w τ) z / jacobiThetaFourTau z τ =
      logDeriv (p20R1_F E (E ^ 2)) z := by
    rw [show jacobiThetaFourTau z τ = P * (fun _ => (1 : ℂ)) z * p20R1_F E (E ^ 2) z from
      congrFun hfun z, hfun, p20R1_logDeriv_shape hPne (hasDerivAt_const z (1 : ℂ))
      hFd one_ne_zero hFz]
    ring
  rw [hL]
  constructor
  · convert hS1 using 1; funext k; rw [hpow, hpow4]; ring
  · convert hS2 using 1; funext k; rw [← pow_mul]

/-- DLMF §20.5(ii): under the conditions of 20.5.10–20.5.13 the series converge absolutely and
uniformly on compact subsets. Stated for the Fourier series of 20.5.10/20.5.11 on compact subsets
of the strip `|Im z| < π Im τ` and of 20.5.12/20.5.13 on compact subsets of `|Im z| < π Im τ/2`,
in Weierstrass M-test form: there is a summable majorant. -/
@[dlmf 20.5.ii]
theorem jacobiTheta_logDeriv_series_uniform {τ : ℂ} (hτ : 0 < τ.im) (K : Set ℂ)
    (hK : IsCompact K) :
    ((∀ z ∈ K, |z.im| < π * τ.im) → ∃ u : ℕ → ℝ, Summable u ∧ ∀ k : ℕ, ∀ z ∈ K,
      ‖cexp (π * I * τ) ^ (2 * (k + 1)) / (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        sin (2 * (k + 1) * z)‖ ≤ u k ∧
      ‖cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))‖ ≤ u k ∧
      ‖cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 + 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))‖ ≤ u k) ∧
    ((∀ z ∈ K, |z.im| < π * τ.im / 2) → ∃ u : ℕ → ℝ, Summable u ∧ ∀ k : ℕ, ∀ z ∈ K,
      ‖cexp (π * I * τ) ^ (k + 1) / (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        sin (2 * (k + 1) * z)‖ ≤ u k ∧
      ‖cexp (π * I * τ) ^ (2 * k + 1) /
        (1 - 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))‖ ≤ u k ∧
      ‖cexp (π * I * τ) ^ (2 * k + 1) /
        (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))‖ ≤ u k) := by
  set E := cexp (π * I * τ) with hE
  have hEn : ‖E‖ = Real.exp (-(π * τ.im)) := by rw [hE, norm_exp]; simp
  have hs1 : ‖E‖ < 1 := th20_norm_nome_lt_one hτ
  have hs0 : 0 ≤ ‖E‖ := norm_nonneg _
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · exact ⟨fun _ => ⟨fun _ => 0, summable_zero, fun k z hz => by simp [hKe] at hz⟩,
      fun _ => ⟨fun _ => 0, summable_zero, fun k z hz => by simp [hKe] at hz⟩⟩
  obtain ⟨z0, hz0K, hmax⟩ := hK.exists_isMaxOn hKn
    ((continuous_abs.comp continuous_im).continuousOn (s := K))
  set c := |z0.im| with hcdef
  have hc : ∀ z ∈ K, |z.im| ≤ c := fun z hz => hmax hz
  have hex : ∀ z ∈ K, Real.exp (2 * |z.im|) ≤ Real.exp (2 * c) := fun z hz =>
    Real.exp_le_exp.mpr (by linarith [hc z hz])
  have hpos : 0 < Real.exp (2 * c) := Real.exp_pos _
  refine ⟨fun hK1 => ?_, fun hK2 => ?_⟩
  · have hcl : c < π * τ.im := hK1 z0 hz0K
    set r := ‖E‖ ^ 2 with hr
    set ρ := r * Real.exp (2 * c) with hρdef
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := by rw [hr]; nlinarith
    have hρ0 : 0 ≤ ρ := by positivity
    have hρ1 : ρ < 1 := by
      rw [hρdef, hr, hEn, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by push_cast; linarith)
    refine ⟨fun k => ρ ^ (k + 1) / (1 - r) + r ^ (k + 1) / (1 - ρ) ^ 2, ?_, fun k z hz => ?_⟩
    · exact (((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hρ0 hρ1)).div_const _).add
        (((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)).div_const _)
    have hxn : ‖E ^ (2 * (k + 1))‖ = r ^ (k + 1) := by rw [norm_pow, pow_mul]
    have hxr : r ^ (k + 1) ≤ r := pow_le_of_le_one hr0 hr1.le (by omega)
    have hA : ρ ^ (k + 1) / (1 - r) ≥ 0 := div_nonneg (by positivity) (by linarith)
    have hB : r ^ (k + 1) / (1 - ρ) ^ 2 ≥ 0 := by positivity
    have hq := p20R1_bound_quot (x := E ^ (2 * (k + 1))) (z := z) (R := r) (ρ := ρ)
      (by rw [hxn]; exact hxr)
      (mul_le_mul_of_nonneg_left (hex z hz) hr0) hρ1
    rw [show E ^ (4 * (k + 1)) = (E ^ (2 * (k + 1))) ^ 2 by rw [← pow_mul]; ring_nf]
    rw [hxn] at hq
    refine ⟨?_, by linarith [hq.1], by linarith [hq.2]⟩
    have hb := p20R1_bound_sin (x := E ^ (2 * (k + 1))) (y := E ^ (2 * (k + 1))) (z := z) k
      (by rw [hxn]; linarith)
    rw [hxn] at hb
    refine hb.trans ?_
    have : r ^ (k + 1) / (1 - r ^ (k + 1)) * Real.exp (2 * |z.im|) ^ (k + 1) ≤
        ρ ^ (k + 1) / (1 - r) := by
      rw [hρdef, mul_pow, div_mul_eq_mul_div]
      gcongr
      exact hc z hz
    linarith
  · have hcl : c < π * τ.im / 2 := hK2 z0 hz0K
    set s := ‖E‖ with hsdef
    set σ := s * Real.exp (2 * c) with hσdef
    have hσ0 : 0 ≤ σ := by positivity
    have hσ1 : σ < 1 := by
      rw [hσdef, hEn, ← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hs2 : s ^ 2 < 1 := by nlinarith
    refine ⟨fun k => σ ^ (k + 1) / (1 - s ^ 2) + s * (s ^ 2) ^ k / (1 - σ) ^ 2, ?_,
      fun k z hz => ?_⟩
    · exact (((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hσ0 hσ1)).div_const _).add
        (((summable_geometric_of_lt_one (by positivity) hs2).mul_left s).div_const _)
    have hyn : ‖E ^ (2 * k + 1)‖ = s * (s ^ 2) ^ k := by rw [norm_pow, ← pow_mul]; ring
    have hys : s * (s ^ 2) ^ k ≤ s := mul_le_of_le_one_right hs0 (pow_le_one₀ (by positivity) hs2.le)
    have hA : σ ^ (k + 1) / (1 - s ^ 2) ≥ 0 := div_nonneg (by positivity) (by linarith)
    have hB : s * (s ^ 2) ^ k / (1 - σ) ^ 2 ≥ 0 := by positivity
    have hq := p20R1_bound_quot (x := E ^ (2 * k + 1)) (z := z) (R := s) (ρ := σ)
      (by rw [hyn]; exact hys)
      (mul_le_mul_of_nonneg_left (hex z hz) hs0) hσ1
    rw [show E ^ (4 * k + 2) = (E ^ (2 * k + 1)) ^ 2 by rw [← pow_mul]; ring_nf]
    rw [hyn] at hq
    refine ⟨?_, by linarith [hq.1], by linarith [hq.2]⟩
    have hxn : ‖E ^ (2 * (k + 1))‖ = (s ^ 2) ^ (k + 1) := by rw [norm_pow, pow_mul]
    have hb := p20R1_bound_sin (x := E ^ (k + 1)) (y := E ^ (2 * (k + 1))) (z := z) k
      (by rw [hxn]; exact pow_lt_one₀ (by positivity) hs2 (by omega))
    rw [hxn, norm_pow] at hb
    refine hb.trans ?_
    have h1 : (s ^ 2) ^ (k + 1) ≤ s ^ 2 := pow_le_of_le_one (by positivity) hs2.le (by omega)
    have : s ^ (k + 1) / (1 - (s ^ 2) ^ (k + 1)) * Real.exp (2 * |z.im|) ^ (k + 1) ≤
        σ ^ (k + 1) / (1 - s ^ 2) := by
      rw [hσdef, mul_pow, div_mul_eq_mul_div]
      gcongr
      exact hc z hz
    linarith

/-! ### §20.5(iii) Double products -/

/-- DLMF 20.5.14: `θ₁(z|τ) = z θ₁'(0|τ) lim_{N→∞} ∏_{n=-N}^{N} lim_{M→∞} ∏_{m=-M, |m|+|n|≠0}^{M}
(1 + z/((m + nτ)π))`, in this (Eisenstein) order of limits. -/
@[dlmf 20.5.E14]
theorem jacobiThetaOneTau_doubleProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ L : ℤ → ℂ,
      (∀ n : ℤ, Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (-(M : ℤ)) M,
          if m = 0 ∧ n = 0 then (1 : ℂ) else 1 + z / ((m + n * τ) * π)) atTop (𝓝 (L n))) ∧
      Tendsto (fun N : ℕ => z * jacobiThetaOneDerivNullTau τ * ∏ n ∈ Finset.Icc (-(N : ℤ)) N, L n)
        atTop (𝓝 (jacobiThetaOneTau z τ)) := by
  sorry

/-- DLMF 20.5.15: `θ₂(z|τ) = θ₂(0|τ) lim_{N→∞} ∏_{n=-N}^{N} lim_{M→∞} ∏_{m=1-M}^{M}
(1 + z/((m - 1/2 + nτ)π))`. -/
@[dlmf 20.5.E15]
theorem jacobiThetaTwoTau_doubleProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ L : ℤ → ℂ,
      (∀ n : ℤ, Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (1 - (M : ℤ)) M,
          (1 + z / ((m - 1 / 2 + n * τ) * π))) atTop (𝓝 (L n))) ∧
      Tendsto (fun N : ℕ => jacobiThetaTwoNullTau τ * ∏ n ∈ Finset.Icc (-(N : ℤ)) N, L n)
        atTop (𝓝 (jacobiThetaTwoTau z τ)) := by
  sorry

/-- DLMF 20.5.16: `θ₃(z|τ) = θ₃(0|τ) lim_{N→∞} ∏_{n=1-N}^{N} lim_{M→∞} ∏_{m=1-M}^{M}
(1 + z/((m - 1/2 + (n - 1/2)τ)π))`. -/
@[dlmf 20.5.E16]
theorem jacobiThetaThreeTau_doubleProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ L : ℤ → ℂ,
      (∀ n : ℤ, Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (1 - (M : ℤ)) M,
          (1 + z / ((m - 1 / 2 + (n - 1 / 2) * τ) * π))) atTop (𝓝 (L n))) ∧
      Tendsto (fun N : ℕ => jacobiThetaThreeNullTau τ * ∏ n ∈ Finset.Icc (1 - (N : ℤ)) N, L n)
        atTop (𝓝 (jacobiThetaThreeTau z τ)) := by
  sorry

/-- DLMF 20.5.17: `θ₄(z|τ) = θ₄(0|τ) lim_{N→∞} ∏_{n=1-N}^{N} lim_{M→∞} ∏_{m=-M}^{M}
(1 + z/((m + (n - 1/2)τ)π))`. -/
@[dlmf 20.5.E17]
theorem jacobiThetaFourTau_doubleProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ L : ℤ → ℂ,
      (∀ n : ℤ, Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (-(M : ℤ)) M,
          (1 + z / ((m + (n - 1 / 2) * τ) * π))) atTop (𝓝 (L n))) ∧
      Tendsto (fun N : ℕ => jacobiThetaFourNullTau τ * ∏ n ∈ Finset.Icc (1 - (N : ℤ)) N, L n)
        atTop (𝓝 (jacobiThetaFourTau z τ)) := by
  sorry

/-- DLMF §20.5(iii): the double products are not absolutely convergent: for `z ≠ 0` the terms
`z/((m + nτ)π)` are not absolutely summable over the lattice. -/
@[dlmf 20.5.iii]
theorem jacobiTheta_doubleProd_not_absolutely_convergent {z τ : ℂ} (hz : z ≠ 0) (hτ : 0 < τ.im) :
    ¬ Summable (fun p : ℤ × ℤ => ‖z / ((p.1 + p.2 * τ) * π)‖) := by
  intro hs
  have hinj : Function.Injective (fun n : ℕ => (((n : ℤ) + 1), (0 : ℤ))) := by
    intro a b h; simp only [Prod.mk.injEq] at h; omega
  have h1 := hs.comp_injective hinj
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h2 : Summable (fun n : ℕ => (π / ‖z‖) * ‖z / ((((((n : ℤ) + 1 : ℤ)) : ℂ) +
      (((0 : ℤ)) : ℂ) * τ) * π)‖) := h1.mul_left _
  have h3 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    refine h2.congr fun n => ?_
    push_cast
    rw [zero_mul, add_zero, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    field_simp
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp (by exact_mod_cast h3))

end DLMF.Theta

end
