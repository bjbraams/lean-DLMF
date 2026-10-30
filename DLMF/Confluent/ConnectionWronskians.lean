/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Recurrence

/-!
# Wronskians from the connection formula 13.2.41

Write `F(w) = e^w U(b-a, b, -w)` for the second solution `e^z U(b-a,b,z e^{±πi})` on the
principal branch. On either side of the real axis, the regularized connection formula
`regularizedHGFun_eq_kummerU_connection` (DLMF 13.2.41) reads `𝐌 = c₁ U + c₂ F` near `z`, so
`W{𝐌, F} = c₁ W{U, F}` and, when `1/Γ(a) ≠ 0`, `W{U, F} = -W{𝐌, U}/c₂`. Continuity in `a`
covers the poles of `Γ(a)`. The statements were moved here from `DLMF.Confluent.BasicProperties`
unchanged, since the derivative of `U` is proved in `DLMF.Confluent.Recurrence`. Hypotheses that the
proofs do not need are kept with underscore names.

## Main results

* `wronskian_kummerU_kummerUReflected`: DLMF 13.2.38.
* `wronskian_regularizedHGFun_kummerUReflected`: DLMF 13.2.35.
* `wronskian_shifted_regularized_kummerUReflected`: DLMF 13.2.37, using also Kummer's transformation
  13.2.40 for both `U` functions.
* `wronskian_kummerU_kummer_neg`, `wronskian_kummerU_kummer_pos`: DLMF 13.2.24–13.2.25.
* `whittakerM_eq_whittakerW_connection`, `wronskian_whittakerM_W_neg`,
  `wronskian_whittakerW_pair`: the Whittaker forms 13.14.32, 13.14.27 and 13.14.30, with the
  prefactor `e^{-z/2} z^{1/2+μ}` and `(-z)^{1/2+μ} = z^{1/2+μ} e^{±πi(1/2+μ)}`.
-/

@[expose] public section

open Complex Filter Set
open scoped Real Topology

noncomputable section

namespace DLMF.Confluent

/-- `exp(±πi) = -1`. -/
theorem exp_sign_mul_pi_mul_I (sign : Bool) : exp ((if sign then 1 else -1) * π * I) = -1 := by
  cases sign
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (-1 : ℂ) * π * I = -(π * I) by ring, exp_neg, exp_pi_mul_I]; norm_num
  · simp [exp_pi_mul_I]

/-- The reflected solution `eʷ U(b-a, b, e^{±πi} w)` equals `eʷ U(b-a, b, -w)`. -/
theorem kummerU_reflected_eq (a b : ℂ) (sign : Bool) :
    (fun w => exp w * kummerU (b - a) b (exp ((if sign then 1 else -1) * π * I) * w)) =
      fun w => exp w * kummerU (b - a) b (-w) := by
  funext w; rw [exp_sign_mul_pi_mul_I, neg_one_mul]

/-- The derivative of `F(w) = e^w U(b-a,b,-w)`. -/
theorem hasDerivAt_kummerU_reflected (a b : ℂ) {z : ℂ} (hz' : -z ∈ slitPlane) :
    HasDerivAt (fun w => exp w * kummerU (b - a) b (-w))
      (exp z * kummerU (b - a) b (-z) +
        exp z * ((b - a) * kummerU (b - a + 1) (b + 1) (-z))) z := by
  have h := (hasDerivAt_exp z).mul ((hasDerivAt_kummerU (b - a) b hz').comp z (hasDerivAt_neg z))
  convert h using 1
  · funext w; simp [Function.comp_apply]
  · simp only [Function.comp_apply]; ring

/-- If `z` lies in the slit plane off the positive real axis, then so does `-z`. -/
theorem neg_mem_slitPlane_of_arg_ne_zero {z : ℂ} (hz : z ∈ slitPlane) (h : z.arg ≠ 0) :
    -z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  right
  rcases hz with hz | hz
  · intro him
    have : z.im = 0 := by simpa using him
    exact h (arg_eq_zero_iff.mpr ⟨hz.le, this⟩)
  · simpa using hz

/-- The explicit Wronskian `W{U(a,b,·), F}` at `z`. -/
theorem wronskian_kummerU_reflected_eq (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hz' : -z ∈ slitPlane) :
    ODE.wronskian (kummerU a b) (fun w => exp w * kummerU (b - a) b (-w)) z =
      kummerU a b z * (exp z * kummerU (b - a) b (-z) +
        exp z * ((b - a) * kummerU (b - a + 1) (b + 1) (-z))) -
      exp z * kummerU (b - a) b (-z) * (-a * kummerU (a + 1) (b + 1) z) := by
  rw [ODE.wronskian, (hasDerivAt_kummerU_reflected a b hz').deriv, (hasDerivAt_kummerU a b hz).deriv]

/-- The connection formula in a neighborhood of a point off the real axis. -/
theorem eventually_regularizedHGFun_eq_connection (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (sign : Bool) (hsign : if sign then z.arg < 0 else 0 < z.arg) :
    ∀ᶠ w in 𝓝 z, regularizedHGFun {a} {b} w =
      exp (-(if sign then 1 else -1) * a * π * I) / Gamma (b - a) * kummerU a b w +
        exp ((if sign then 1 else -1) * (b - a) * π * I) / Gamma a *
          (exp w * kummerU (b - a) b (-w)) := by
  have hs : ∀ᶠ w in 𝓝 z, w ∈ slitPlane := isOpen_slitPlane.mem_nhds hz
  have ha : ∀ᶠ w in 𝓝 z, if sign then w.arg < 0 else 0 < w.arg := by
    cases sign
    · simp only [Bool.false_eq_true, ↓reduceIte] at hsign ⊢
      exact (continuousAt_arg hz).eventually (lt_mem_nhds hsign)
    · simp only [↓reduceIte] at hsign ⊢
      exact (continuousAt_arg hz).eventually (gt_mem_nhds hsign)
  filter_upwards [hs, ha] with w hw hwa
  have hwa' : if sign then w.arg ≤ 0 else 0 < w.arg := by
    cases sign <;> simp_all [le_of_lt]
  rw [regularizedHGFun_eq_kummerU_connection a b hw sign hwa', exp_sign_mul_pi_mul_I,
    neg_one_mul]
  ring

/-- The core identities: `W{𝐌, F} = c₁ W{U, F}`, and `c₂ W{U, F} = -W{𝐌, U}`. -/
theorem wronskian_connection_core (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) (hz' : -z ∈ slitPlane)
    (sign : Bool) (hsign : if sign then z.arg < 0 else 0 < z.arg) :
    ODE.wronskian (regularizedHGFun {a} {b}) (fun w => exp w * kummerU (b - a) b (-w)) z =
        exp (-(if sign then 1 else -1) * a * π * I) / Gamma (b - a) *
          ODE.wronskian (kummerU a b) (fun w => exp w * kummerU (b - a) b (-w)) z ∧
      exp ((if sign then 1 else -1) * (b - a) * π * I) / Gamma a *
          ODE.wronskian (kummerU a b) (fun w => exp w * kummerU (b - a) b (-w)) z =
        z ^ (-b) * exp z / Gamma a := by
  set c1 := exp (-(if sign then 1 else -1) * a * π * I) / Gamma (b - a)
  set c2 := exp ((if sign then 1 else -1) * (b - a) * π * I) / Gamma a
  set F := fun w => exp w * kummerU (b - a) b (-w) with hF
  have heq := eventually_regularizedHGFun_eq_connection a b hz sign hsign
  have hU := hasDerivAt_kummerU a b hz
  have hFd := hasDerivAt_kummerU_reflected a b hz'
  have hG := (hU.const_mul c1).add (hFd.const_mul c2)
  have hM : HasDerivAt (regularizedHGFun {a} {b}) _ z := hG.congr_of_eventuallyEq heq
  have hMz := heq.self_of_nhds
  have hW := wronskian_regularizedHGFun_kummerU_all a b hz
  rw [ODE.wronskian, hM.deriv, hU.deriv] at hW
  rw [ODE.wronskian, ODE.wronskian, hM.deriv, hFd.deriv, hU.deriv, hMz]
  simp only [hF] at hW hMz ⊢
  rw [hMz] at hW
  constructor
  · ring
  · linear_combination -hW

/-- DLMF's `U(b-a,b,z e^{±πi})` is represented by the principal value at `-z`, which is the
`e^{+πi}` continuation for `ph z < 0` and the `e^{-πi}` continuation for `ph z > 0`. -/
@[dlmf 13.2.E38]
theorem wronskian_kummerU_kummerUReflected (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (sign : Bool) (hsign : if sign then z.arg < 0 else 0 < z.arg) :
    ODE.wronskian (kummerU a b)
      (fun w => exp w * kummerU (b - a) b (exp ((if sign then 1 else -1) * π * I) * w)) z =
      exp ((if sign then 1 else -1) * (a - b) * π * I) * z ^ (-b) * exp z := by
  have hz0 := slitPlane_ne_zero hz
  have harg : z.arg ≠ 0 := by split_ifs at hsign <;> [exact hsign.ne; exact hsign.ne']
  have hz' := neg_mem_slitPlane_of_arg_ne_zero hz harg
  rw [kummerU_reflected_eq]
  set ε : ℂ := if sign then 1 else -1 with hε
  have hnz : -z ≠ 0 := neg_ne_zero.mpr hz0
  refine eq_of_continuousAt_of_integerComplement
    (f := fun c => ODE.wronskian (kummerU c b) (fun w => exp w * kummerU (b - c) b (-w)) z)
    (g := fun c => exp (ε * (c - b) * π * I) * z ^ (-b) * exp z) ?_ (by fun_prop) ?_
  · simp only [wronskian_kummerU_reflected_eq _ b hz hz']
    have h1 := continuousAt_kummerU_comp (A := fun c => c) (B := fun _ => b) (b := a)
      continuousAt_id
      continuousAt_const hz0
    have h2 := continuousAt_kummerU_comp (A := fun c => b - c) (B := fun _ => b) (b := a)
      (by fun_prop) continuousAt_const hnz
    have h3 := continuousAt_kummerU_comp (A := fun c => b - c + 1) (B := fun _ => b + 1) (b := a)
      (by fun_prop) continuousAt_const hnz
    have h4 := continuousAt_kummerU_comp (A := fun c => c + 1) (B := fun _ => b + 1) (b := a)
      (by fun_prop) continuousAt_const hz0
    exact (h1.mul (continuousAt_const.mul h2 |>.add (continuousAt_const.mul
      ((continuousAt_id.const_sub b).mul h3)))).sub ((continuousAt_const.mul h2).mul
      (continuousAt_id.neg.mul h4))
  · intro c hc
    have hcn := not_neg_nat_of_mem_integerComplement hc
    have hG : Gamma c ≠ 0 := Gamma_ne_zero hcn
    have h := (wronskian_connection_core c b hz hz' sign hsign).2
    have he : exp (ε * (b - c) * π * I) ≠ 0 := exp_ne_zero _
    rw [← hε, div_mul_eq_mul_div, div_left_inj' hG] at h
    rw [show ε * (c - b) * π * I = -(ε * (b - c) * π * I) by ring, mul_assoc, ← h, ← mul_assoc,
      ← exp_add, neg_add_cancel, exp_zero, one_mul]

/-- The Wronskian of `U(a,b,z)` and `eᶻ U(b-a,b,-z)` is `e^{±(a-b)πi} z^{-b} eᶻ`, with the sign
fixed by the half-plane of `z` (DLMF 13.2.36). -/
theorem wronskian_kummerU_reflected (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (sign : Bool) (hsign : if sign then z.arg < 0 else 0 < z.arg) :
    ODE.wronskian (kummerU a b) (fun w => exp w * kummerU (b - a) b (-w)) z =
      exp ((if sign then 1 else -1) * (a - b) * π * I) * z ^ (-b) * exp z := by
  have h := wronskian_kummerU_kummerUReflected a b hz sign hsign
  rwa [kummerU_reflected_eq] at h

/-- DLMF's `U(b-a,b,z e^{±πi})` is represented by the principal value at `-z`, which is the
`e^{+πi}` continuation for `ph z < 0` and the `e^{-πi}` continuation for `ph z > 0`. -/
@[dlmf 13.2.E35]
theorem wronskian_regularizedHGFun_kummerUReflected (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (sign : Bool) (hsign : if sign then z.arg < 0 else 0 < z.arg)
    (_hba : ∀ k : ℕ, b - a ≠ -k) :
    ODE.wronskian (regularizedHGFun {a} {b})
      (fun w => exp w * kummerU (b - a) b (exp ((if sign then 1 else -1) * π * I) * w)) z =
      exp (-(if sign then 1 else -1) * b * π * I) * z ^ (-b) * exp z / Gamma (b - a) := by
  have harg : z.arg ≠ 0 := by split_ifs at hsign <;> [exact hsign.ne; exact hsign.ne']
  have hz' := neg_mem_slitPlane_of_arg_ne_zero hz harg
  rw [kummerU_reflected_eq, (wronskian_connection_core a b hz hz' sign hsign).1,
    wronskian_kummerU_reflected a b hz sign hsign]
  have he : exp (-(if sign then 1 else -1) * a * π * I) *
      exp ((if sign then 1 else -1) * (a - b) * π * I) =
      exp (-(if sign then 1 else -1) * b * π * I) := by
    rw [← exp_add]; ring_nf
  rw [div_eq_mul_inv, div_eq_mul_inv]
  linear_combination (z ^ (-b) * exp z * (Gamma (b - a))⁻¹) * he

/-- The Wronskian of `U(a,b,z)` and `eᶻ U(b-a,b,-z)` is nonzero when `z` and `-z` lie in the slit
plane. -/
theorem wronskian_kummerU_reflected_ne_zero (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hz' : -z ∈ slitPlane) :
    ODE.wronskian (kummerU a b) (fun w => exp w * kummerU (b - a) b (-w)) z ≠ 0 := by
  have hz0 := slitPlane_ne_zero hz
  have him : z.im ≠ 0 := by
    intro h
    rw [mem_slitPlane_iff] at hz hz'
    simp [h] at hz hz'
    linarith
  have hcp : z ^ (-b) ≠ 0 := by rw [cpow_def_of_ne_zero hz0]; exact exp_ne_zero _
  rcases lt_or_gt_of_ne him with h | h
  · rw [wronskian_kummerU_reflected a b hz true (by simpa using arg_neg_iff.mpr h)]
    exact mul_ne_zero (mul_ne_zero (exp_ne_zero _) (hcp)) (exp_ne_zero _)
  · rw [wronskian_kummerU_reflected a b hz false (by
      simpa using lt_of_le_of_ne (arg_nonneg_iff.mpr h.le)
        fun h0 => him (arg_eq_zero_iff.mp h0.symm).2)]
    exact mul_ne_zero (mul_ne_zero (exp_ne_zero _) (hcp)) (exp_ne_zero _)

/-- Numerically satisfactory pair on `-π/2 ≤ ph z ≤ 3π/2`. The second function is taken on
the principal branch, so `-z` must avoid the cut for it to be differentiable at `z`. -/
@[dlmf 13.2.E24]
theorem wronskian_kummerU_kummer_neg (a b : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) (hz' : -z ∈ slitPlane) (_harg : -(π / 2) ≤ z.arg)
    (_harg' : z.arg ≤ 3 * π / 2) (_hb : ∀ n : ℤ, b ≠ n) :
    ODE.wronskian (kummerU a b)
      (fun w => exp w * kummerU (b - a) b (exp (-π * I) * w)) z ≠ 0 := by
  have h := kummerU_reflected_eq a b false
  simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul] at h
  rw [show -(π : ℂ) * I = -(π * I) by ring] at h ⊢
  rw [h]
  exact wronskian_kummerU_reflected_ne_zero a b hz hz'

/-- Numerically satisfactory pair on `-3π/2 ≤ ph z ≤ π/2`. The second function is taken on
the principal branch, so `-z` must avoid the cut for it to be differentiable at `z`. -/
@[dlmf 13.2.E25]
theorem wronskian_kummerU_kummer_pos (a b : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) (hz' : -z ∈ slitPlane) (_harg : -(3 * π / 2) ≤ z.arg)
    (_harg' : z.arg ≤ π / 2) (_hb : ∀ n : ℤ, b ≠ n) :
    ODE.wronskian (kummerU a b)
      (fun w => exp w * kummerU (b - a) b (exp (π * I) * w)) z ≠ 0 := by
  have h := kummerU_reflected_eq a b true
  simp only [↓reduceIte, one_mul] at h
  rw [h]
  exact wronskian_kummerU_reflected_ne_zero a b hz hz'

/-- The value does not depend on the branch; `-z` must avoid the cut so that the second
function is differentiable at `z`. -/
@[dlmf 13.2.E37]
theorem wronskian_shifted_regularized_kummerUReflected (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hz' : -z ∈ slitPlane) (sign : Bool) (_ha : ∀ k : ℕ, 1 - a ≠ -k) :
    ODE.wronskian (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w)
      (fun w => exp w * kummerU (b - a) b (exp ((if sign then 1 else -1) * π * I) * w)) z =
      -(z ^ (-b) * exp z) / Gamma (1 - a) := by
  have hz0 := slitPlane_ne_zero hz
  have him : z.im ≠ 0 := by
    intro h
    rw [mem_slitPlane_iff] at hz hz'
    simp [h] at hz hz'
    linarith
  rw [kummerU_reflected_eq]
  obtain ⟨s, hs⟩ : ∃ s : Bool, if s then z.arg < 0 else 0 < z.arg := by
    rcases lt_or_gt_of_ne him with h | h
    · exact ⟨true, by simpa using arg_neg_iff.mpr h⟩
    · exact ⟨false, by simpa using (lt_of_le_of_ne (arg_nonneg_iff.mpr h.le)
        fun h0 => him (arg_eq_zero_iff.mp h0.symm).2)⟩
  set ε : ℂ := if s then 1 else -1 with hε
  have hε1 : ε = 1 ∨ ε = -1 := by cases s <;> simp [hε]
  set F := fun w => exp w * kummerU (b - a) b (-w) with hF
  set c1 := exp (-ε * (a - b + 1) * π * I) / Gamma (1 - a)
  set c3 := exp (ε * (1 - a) * π * I) / Gamma (a - b + 1) * (exp (ε * π * I * (1 - b)))⁻¹
  -- the connection formula near `z`
  have hs' : ∀ᶠ w in 𝓝 z, w ∈ slitPlane := isOpen_slitPlane.mem_nhds hz
  have ha' : ∀ᶠ w in 𝓝 z, if s then w.arg < 0 else 0 < w.arg := by
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte] at hs ⊢
      exact (continuousAt_arg hz).eventually (lt_mem_nhds hs)
    · simp only [↓reduceIte] at hs ⊢
      exact (continuousAt_arg hz).eventually (gt_mem_nhds hs)
  have heq : (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w) =ᶠ[𝓝 z]
      fun w => c1 * kummerU a b w + c3 * F w := by
    filter_upwards [hs', ha'] with w hw hwa
    have hw0 := slitPlane_ne_zero hw
    have hwa' : if s then w.arg ≤ 0 else 0 < w.arg := by cases s <;> simp_all [le_of_lt]
    have hc : ∀ v : ℂ, (-w) ^ v = w ^ v * exp (ε * π * I * v) := by
      have h1 := arg_le_pi w
      have h2 := neg_pi_lt_arg w
      refine neg_cpow_of_arg hw0 ε hε1 ?_ ?_ <;> cases s <;> simp_all <;> linarith
    have hK := kummerU_kummer_transform_all (b - a) b (neg_ne_zero.mpr hw0)
    rw [show b - a - b + 1 = 1 - a by ring, hc] at hK
    rw [regularizedHGFun_eq_kummerU_connection (a - b + 1) (2 - b) hw s hwa',
      exp_sign_mul_pi_mul_I, neg_one_mul, kummerU_kummer_transform_all a b hw0, hF]
    simp only [← hε, show 2 - b - (a - b + 1) = 1 - a by ring, hK, c1, c3]
    have hE := exp_ne_zero (ε * π * I * (1 - b))
    generalize exp (ε * π * I * (1 - b)) = E at *
    generalize exp (ε * (1 - a) * π * I) = E2
    generalize exp (-ε * (a - b + 1) * π * I) = E3
    field_simp
  have hU := hasDerivAt_kummerU a b hz
  have hFd := hasDerivAt_kummerU_reflected a b hz'
  have hG := ((hU.const_mul c1).add (hFd.const_mul c3)).congr_of_eventuallyEq heq
  have hGz := heq.self_of_nhds
  have hW := wronskian_kummerU_reflected a b hz s hs
  rw [ODE.wronskian, hU.deriv, hFd.deriv] at hW
  rw [ODE.wronskian, hG.deriv, hFd.deriv]
  simp only at hGz ⊢
  rw [hGz]
  have he : c1 * exp ((if s then 1 else -1) * (a - b) * π * I) = -(Gamma (1 - a))⁻¹ := by
    simp only [c1]
    rw [← hε, div_eq_mul_inv, mul_comm, ← mul_assoc, ← exp_add,
      show ε * (a - b) * π * I + -ε * (a - b + 1) * π * I = -(ε * π * I) by ring, exp_neg]
    rcases hε1 with h | h <;> rw [h]
    · rw [one_mul, exp_pi_mul_I]; ring
    · rw [show (-1 : ℂ) * π * I = -(π * I) by ring, exp_neg, exp_pi_mul_I]; ring
  simp only [F]
  linear_combination c1 * hW + z ^ (-b) * exp z * he

/-! ### Whittaker functions -/

/-- The Wronskian at `z` depends only on the germ at `z` of its second function. -/
theorem wronskian_congr_right {f g h : ℂ → ℂ} {z : ℂ} (hgh : g =ᶠ[𝓝 z] h) :
    ODE.wronskian f g z = ODE.wronskian f h z := by
  unfold ODE.wronskian; rw [hgh.eq_of_nhds, hgh.deriv_eq]

/-- The Wronskian is linear in its second function: `W(f, c g) = c W(f, g)`. -/
theorem wronskian_const_mul_right {f g : ℂ → ℂ} {z : ℂ} (c : ℂ) (hg : DifferentiableAt ℂ g z) :
    ODE.wronskian f (fun w => c * g w) z = c * ODE.wronskian f g z := by
  unfold ODE.wronskian; rw [deriv_const_mul _ hg]; ring

/-- The Wronskian is linear in its first function: `W(c f, g) = c W(f, g)`. -/
theorem wronskian_const_mul_left {f g : ℂ → ℂ} {z : ℂ} (c : ℂ) (hf : DifferentiableAt ℂ f z) :
    ODE.wronskian (fun w => c * f w) g z = c * ODE.wronskian f g z := by
  unfold ODE.wronskian; rw [deriv_const_mul _ hf]; ring

/-- `(-w)^s = w^s e^{επis}` near a point `z` off the real axis, with `ε = ±1` from `sign`. -/
theorem eventually_neg_cpow (s : ℂ) {z : ℂ} (hz : z ∈ slitPlane) (sign : Bool)
    (hsign : if sign then z.arg < 0 else 0 < z.arg) :
    ∀ᶠ w in 𝓝 z, w ∈ slitPlane ∧
      (-w) ^ s = w ^ s * exp ((if sign then 1 else -1) * π * I * s) := by
  have hs : ∀ᶠ w in 𝓝 z, w ∈ slitPlane := isOpen_slitPlane.mem_nhds hz
  have ha : ∀ᶠ w in 𝓝 z, if sign then w.arg < 0 else 0 < w.arg := by
    cases sign
    · simp only [Bool.false_eq_true, ↓reduceIte] at hsign ⊢
      exact (continuousAt_arg hz).eventually (lt_mem_nhds hsign)
    · simp only [↓reduceIte] at hsign ⊢
      exact (continuousAt_arg hz).eventually (gt_mem_nhds hsign)
  filter_upwards [hs, ha] with w hw hwa
  refine ⟨hw, ?_⟩
  have h1 := arg_le_pi w
  have h2 := neg_pi_lt_arg w
  have hw0 := slitPlane_ne_zero hw
  cases sign
  · simp only [Bool.false_eq_true, ↓reduceIte] at hwa ⊢
    refine neg_cpow_of_arg hw0 (-1) (Or.inr rfl) ?_ ?_ s <;>
      simp only [neg_re, one_re] <;> linarith
  · simp only [↓reduceIte] at hwa ⊢
    refine neg_cpow_of_arg hw0 1 (Or.inl rfl) ?_ ?_ s <;> simp only [one_re] <;> linarith

/-- Near a point off the real axis, `W_{-κ,μ}(z e^{±πi}) = e^{±πi(1/2+μ)} g(z) F(z)` with the
Whittaker prefactor `g(z) = e^{-z/2} z^{1/2+μ}` and `F(z) = e^z U(1/2+μ+κ, 1+2μ, -z)`. -/
theorem eventually_whittakerW_reflected (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) (sign : Bool)
    (hsign : if sign then z.arg < 0 else 0 < z.arg) :
    (fun w => whittakerW (-κ) μ (exp ((if sign then 1 else -1) * π * I) * w)) =ᶠ[𝓝 z]
      fun w => exp ((if sign then 1 else -1) * π * I * (1 / 2 + μ)) *
        ((exp (-w / 2) * w ^ (1 / 2 + μ)) *
          (exp w * kummerU (1 / 2 + μ + κ) (1 + 2 * μ) (-w))) := by
  filter_upwards [eventually_neg_cpow (1 / 2 + μ) hz sign hsign] with w hw
  rw [exp_sign_mul_pi_mul_I, neg_one_mul, whittakerW, hw.2, show 1 / 2 + μ - -κ = 1 / 2 + μ + κ by
    ring]
  have he : exp (-(-w) / 2) = exp (-w / 2) * exp w := by rw [← exp_add]; ring_nf
  rw [he]
  ring

/-- The Whittaker prefactor `e^{-w/2} w^r` is complex differentiable on the slit plane. -/
theorem differentiableAt_whittakerPrefactor (r : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    DifferentiableAt ℂ (fun w : ℂ => exp (-w / 2) * w ^ r) z :=
  (hasDerivAt_whittakerPrefactor r hz).differentiableAt

/-- The square of the Whittaker prefactor. -/
theorem whittakerPrefactor_sq (μ : ℂ) (z : ℂ) :
    (exp (-z / 2) * z ^ (1 / 2 + μ)) ^ 2 = exp (-z) * z ^ (1 + 2 * μ) := by
  rw [mul_pow, ← exp_nat_mul, ← cpow_nat_mul]
  congr 2 <;> push_cast <;> ring

/-- DLMF's `W_{-κ,μ}(z e^{±πi})` is represented by the principal value at `-z`, which is the
`e^{+πi}` continuation for `ph z ≤ 0` and the `e^{-πi}` continuation for `ph z > 0`. -/
@[dlmf 13.14.E32]
theorem whittakerM_eq_whittakerW_connection {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (sign : Bool)
    (hsign : if sign then z.arg ≤ 0 else 0 < z.arg) :
    whittakerM κ μ z / Gamma (1 + 2 * μ) =
      exp ((if sign then 1 else -1) * (κ - μ - 1 / 2) * π * I) /
          Gamma (1 / 2 + μ + κ) * whittakerW κ μ z +
        exp ((if sign then 1 else -1) * κ * π * I) / Gamma (1 / 2 + μ - κ) *
          whittakerW (-κ) μ (exp ((if sign then 1 else -1) * π * I) * z) := by
  have hz0 := slitPlane_ne_zero hz
  have hconn := regularizedHGFun_eq_kummerU_connection (μ - κ + 1 / 2) (1 + 2 * μ) hz sign hsign
  rw [regularizedConfluent_eq_div_Gamma hμ, exp_sign_mul_pi_mul_I, neg_one_mul,
    show 1 + 2 * μ - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring] at hconn
  set ε : ℂ := if sign then 1 else -1 with hεdef
  have hε : ε = 1 ∨ ε = -1 := by cases sign <;> simp [hεdef]
  have hc : (-z) ^ (1 / 2 + μ) = z ^ (1 / 2 + μ) * exp (ε * π * I * (1 / 2 + μ)) := by
    have h1 := arg_le_pi z
    have h2 := neg_pi_lt_arg z
    refine neg_cpow_of_arg hz0 ε hε ?_ ?_ _ <;> cases sign <;> simp_all <;> linarith
  rw [exp_sign_mul_pi_mul_I, neg_one_mul, whittakerM, whittakerW, whittakerW, hc,
    show 1 / 2 + μ - -κ = 1 / 2 + μ + κ by ring, show 1 / 2 + μ - κ = μ - κ + 1 / 2 by ring,
    show μ + 1 / 2 = 1 / 2 + μ by ring, mul_div_assoc, hconn]
  have e1 : exp (ε * (κ - μ - 1 / 2) * π * I) = exp (-ε * (μ - κ + 1 / 2) * π * I) := by
    congr 1; ring
  have e2 : exp (-(-z) / 2) * exp (ε * π * I * (1 / 2 + μ)) * exp (ε * κ * π * I) =
      exp (-z / 2) * exp (ε * (1 / 2 + μ + κ) * π * I) * exp z := by
    rw [← exp_add, ← exp_add, ← exp_add, ← exp_add]; congr 1; ring
  rw [e1]
  linear_combination (-(z ^ (1 / 2 + μ) * kummerU (1 / 2 + μ + κ) (1 + 2 * μ) (-z) /
    Gamma (μ - κ + 1 / 2))) * e2

/-- The Wronskians of `W_{κ,μ}` and `𝐌` against the reflected Whittaker function, reduced to the
Tricomi Wronskians. -/
theorem whittaker_wronskian_setup (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) (sign : Bool)
    (hsign : if sign then z.arg < 0 else 0 < z.arg) (f : ℂ → ℂ) (hf : DifferentiableAt ℂ f z) :
    ODE.wronskian (fun w => (exp (-w / 2) * w ^ (1 / 2 + μ)) * f w)
      (fun w => whittakerW (-κ) μ (exp ((if sign then 1 else -1) * π * I) * w)) z =
      exp ((if sign then 1 else -1) * π * I * (1 / 2 + μ)) * (exp (-z) * z ^ (1 + 2 * μ)) *
        ODE.wronskian f (fun w => exp w * kummerU (1 / 2 + μ + κ) (1 + 2 * μ) (-w)) z := by
  have harg : z.arg ≠ 0 := by split_ifs at hsign <;> [exact hsign.ne; exact hsign.ne']
  have hz' := neg_mem_slitPlane_of_arg_ne_zero hz harg
  have hF := (hasDerivAt_kummerU_reflected (1 / 2 + μ - κ) (1 + 2 * μ) hz').differentiableAt
  rw [show 1 + 2 * μ - (1 / 2 + μ - κ) = 1 / 2 + μ + κ by ring] at hF
  rw [wronskian_congr_right (eventually_whittakerW_reflected κ μ hz sign hsign)]
  set c := exp ((if sign then 1 else -1) * π * I * (1 / 2 + μ))
  rw [show (fun w => c * ((exp (-w / 2) * w ^ (1 / 2 + μ)) *
      (exp w * kummerU (1 / 2 + μ + κ) (1 + 2 * μ) (-w)))) =
      fun w => (exp (-w / 2) * w ^ (1 / 2 + μ)) *
        (c * (exp w * kummerU (1 / 2 + μ + κ) (1 + 2 * μ) (-w))) from
      funext fun w => by ring,
    wronskian_mul_left (differentiableAt_whittakerPrefactor _ hz) hf (hF.const_mul c),
    wronskian_const_mul_right c hF, whittakerPrefactor_sq]
  ring

/-- `W{U(a,b,·), F}` in Whittaker parameters. -/
theorem wronskian_kummerU_reflected_whittaker (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (sign : Bool) (hsign : if sign then z.arg < 0 else 0 < z.arg) :
    ODE.wronskian (kummerU (1 / 2 + μ - κ) (1 + 2 * μ))
      (fun w => exp w * kummerU (1 / 2 + μ + κ) (1 + 2 * μ) (-w)) z =
      exp ((if sign then 1 else -1) * (1 / 2 + μ - κ - (1 + 2 * μ)) * π * I) *
        z ^ (-(1 + 2 * μ)) * exp z := by
  have h := wronskian_kummerU_reflected (1 / 2 + μ - κ) (1 + 2 * μ) hz sign hsign
  rwa [show 1 + 2 * μ - (1 / 2 + μ - κ) = 1 / 2 + μ + κ by ring] at h

/-- `z^s z^{-s} = 1` for `z ≠ 0`. -/
theorem cpow_mul_cpow_neg_self {z : ℂ} (hz0 : z ≠ 0) (s : ℂ) : z ^ s * z ^ (-s) = 1 := by
  rw [← cpow_add _ _ hz0, add_neg_cancel, cpow_zero]

/-- DLMF's `W_{-κ,μ}(z e^{±πi})` is represented by the principal value at `-z`, which is the
`e^{+πi}` continuation for `ph z < 0` and the `e^{-πi}` continuation for `ph z > 0`. -/
@[dlmf 13.14.E30]
theorem wronskian_whittakerW_pair {κ μ z : ℂ} (hz : z ∈ slitPlane) (sign : Bool)
    (hsign : if sign then z.arg < 0 else 0 < z.arg) :
    ODE.wronskian (whittakerW κ μ)
      (fun w => whittakerW (-κ) μ (exp ((if sign then 1 else -1) * π * I) * w)) z =
      exp (-(if sign then 1 else -1) * κ * π * I) := by
  have hz0 := slitPlane_ne_zero hz
  have hW : whittakerW κ μ = fun w => (exp (-w / 2) * w ^ (1 / 2 + μ)) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w := funext fun w => rfl
  rw [hW, whittaker_wronskian_setup κ μ hz sign hsign _
    (hasDerivAt_kummerU _ _ hz).differentiableAt,
    wronskian_kummerU_reflected_whittaker κ μ hz sign hsign]
  have hp := cpow_mul_cpow_neg_self hz0 (1 + 2 * μ)
  have he : exp (-z) * exp z = 1 := by rw [← exp_add]; simp
  have hx : exp ((if sign then 1 else -1) * π * I * (1 / 2 + μ)) *
      exp ((if sign then 1 else -1) * (1 / 2 + μ - κ - (1 + 2 * μ)) * π * I) =
      exp (-(if sign then 1 else -1) * κ * π * I) := by
    rw [← exp_add]; congr 1; ring
  linear_combination (exp (-z) * exp z) * (z ^ (1 + 2 * μ) * z ^ (-(1 + 2 * μ))) * hx +
    exp (-(if sign then 1 else -1) * κ * π * I) * (exp (-z) * exp z) * hp +
    exp (-(if sign then 1 else -1) * κ * π * I) * he

/-- DLMF's `W_{-κ,μ}(z e^{±πi})` is represented by the principal value at `-z`, which is the
`e^{+πi}` continuation for `ph z < 0` and the `e^{-πi}` continuation for `ph z > 0`. -/
@[dlmf 13.14.E27]
theorem wronskian_whittakerM_W_neg {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (sign : Bool)
    (hsign : if sign then z.arg < 0 else 0 < z.arg) :
    ODE.wronskian (whittakerM κ μ)
      (fun w => whittakerW (-κ) μ (exp ((if sign then 1 else -1) * π * I) * w)) z =
      Gamma (1 + 2 * μ) / Gamma (1 / 2 + μ + κ) *
        exp (-(if sign then 1 else -1) * (1 / 2 + μ) * π * I) := by
  have hz0 := slitPlane_ne_zero hz
  have harg : z.arg ≠ 0 := by split_ifs at hsign <;> [exact hsign.ne; exact hsign.ne']
  have hz' := neg_mem_slitPlane_of_arg_ne_zero hz harg
  have hM : whittakerM κ μ = fun w => (exp (-w / 2) * w ^ (1 / 2 + μ)) *
      (Gamma (1 + 2 * μ) * regularizedHGFun {1 / 2 + μ - κ} {1 + 2 * μ} w) := funext fun w => by
    rw [whittakerM, kummerM_eq_mul_regularizedHGFun hμ, show μ + 1 / 2 = 1 / 2 + μ by ring,
      show μ - κ + 1 / 2 = 1 / 2 + μ - κ by ring]
  have hcore := (wronskian_connection_core (1 / 2 + μ - κ) (1 + 2 * μ) hz hz' sign hsign).1
  rw [show 1 + 2 * μ - (1 / 2 + μ - κ) = 1 / 2 + μ + κ by ring,
    wronskian_kummerU_reflected_whittaker κ μ hz sign hsign] at hcore
  rw [hM, whittaker_wronskian_setup κ μ hz sign hsign _
    ((differentiableAt_regularizedConfluent _ _ z).const_mul _),
    wronskian_const_mul_left _ (differentiableAt_regularizedConfluent _ _ z), hcore]
  have hp := cpow_mul_cpow_neg_self hz0 (1 + 2 * μ)
  have he : exp (-z) * exp z = 1 := by rw [← exp_add]; simp
  have hx : exp ((if sign then 1 else -1) * π * I * (1 / 2 + μ)) *
      (exp (-(if sign then 1 else -1) * (1 / 2 + μ - κ) * π * I) *
        exp ((if sign then 1 else -1) * (1 / 2 + μ - κ - (1 + 2 * μ)) * π * I)) =
      exp (-(if sign then 1 else -1) * (1 / 2 + μ) * π * I) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  linear_combination (Gamma (1 + 2 * μ) / Gamma (1 / 2 + μ + κ)) *
    ((exp (-z) * exp z) * (z ^ (1 + 2 * μ) * z ^ (-(1 + 2 * μ))) * hx +
    exp (-(if sign then 1 else -1) * (1 / 2 + μ) * π * I) * (exp (-z) * exp z) * hp +
    exp (-(if sign then 1 else -1) * (1 / 2 + μ) * π * I) * he)

end DLMF.Confluent
