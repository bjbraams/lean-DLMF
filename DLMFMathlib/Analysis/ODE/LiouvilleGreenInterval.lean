/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LiouvilleGreenIntervalVolterra
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenReal

/-!
# Liouville–Green solutions controlled from a singular finite endpoint

The amplitude-form Volterra construction and its exponential specialization on `(a,b)`,
following Olver, *Asymptotics and Special Functions*, Chapter 6, Theorem 2.1 and §10.
No regularity at either endpoint is assumed; the error density is integrable up to `b`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace LiouvilleGreen.Interval

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Liouville–Green approximation with error bounds**, general form.
Let `A ≠ 0` be twice differentiable on `(a, b)` and let `E` solve `E' = -k A⁻² E`, so that
`A E` is the Liouville–Green approximation `f^{-1/4} exp (-k ∫ f^{1/2})` with `f = A⁻⁴`.
Put `F' = A A'' - g A²` (the derivative of Olver's error-control function). If `‖E‖` is
nonincreasing, `‖(1 - E(t)²/E(x)²)/(2k)‖ ≤ κ` for `a < x < t < b` and `‖F'‖` is
integrable up to `b`, then `w'' = (k² A⁻⁴ + g) w` has a solution
`w = A E (1 + ε)` on `(a, b)` with
`‖ε x‖ ≤ exp (κ V x) - 1` and `‖A² ε'‖ ≤ (exp (κ V x) - 1)/κ`, where
`V x = ∫_{(x,b)} ‖F'‖` is the variation of the error-control function on `(x, b)`
(Olver, *Asymptotics and Special Functions*, Ch. 6, Thm. 2.1 and Ch. 10, Thm. 3.1). -/
theorem exists_solution_of_kernel_bound {a b κ : ℝ} {k : 𝕜} {A A' A'' E g : ℝ → 𝕜}
    (hk : k ≠ 0) (hκ : 0 < κ)
    (hA : ∀ x, x ∈ Ioo a b → A x ≠ 0)
    (hA' : ∀ x, x ∈ Ioo a b → HasDerivAt A (A' x) x)
    (hA'' : ∀ x, x ∈ Ioo a b → HasDerivAt A' (A'' x) x)
    (hA''c : ContinuousOn A'' (Ioo a b)) (hgc : ContinuousOn g (Ioo a b))
    (hE0 : ∀ x, x ∈ Ioo a b → E x ≠ 0)
    (hE : ∀ x, x ∈ Ioo a b → HasDerivAt E (-(k * (A x ^ 2)⁻¹ * E x)) x)
    (hEle : ∀ x t, x ∈ Ioo a b → t ∈ Ioo x b → ‖E t‖ ≤ ‖E x‖)
    (hK : ∀ x t, x ∈ Ioo a b → t ∈ Ioo x b → ‖(1 - E t ^ 2 / E x ^ 2) / (2 * k)‖ ≤ κ)
    (hFi : ∀ c, c ∈ Ioo a b → IntegrableOn (fun t => ‖A t * A'' t - g t * A t ^ 2‖) (Ioo c b)) :
    ∃ ε ε' w' : ℝ → 𝕜, ∀ x, x ∈ Ioo a b →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => A y * E y * (1 + ε y)) (w' x) x ∧
      HasDerivAt w' ((k ^ 2 * (A x ^ 4)⁻¹ + g x) * (A x * E x * (1 + ε x))) x ∧
      ‖ε x‖ ≤ Real.exp (κ * ∫ t in Ioo x b, ‖A t * A'' t - g t * A t ^ 2‖) - 1 ∧
      ‖A x ^ 2 * ε' x‖ ≤
        (Real.exp (κ * ∫ t in Ioo x b, ‖A t * A'' t - g t * A t ^ 2‖) - 1) / κ := by
  set F' : ℝ → 𝕜 := fun t => A t * A'' t - g t * A t ^ 2 with hF'
  have hAc : ContinuousOn A (Ioo a b) := fun x hx =>
    (hA' x hx).continuousAt.continuousWithinAt
  have hEc : ContinuousOn E (Ioo a b) := fun x hx =>
    (hE x hx).continuousAt.continuousWithinAt
  have hF'c : ContinuousOn F' (Ioo a b) := (hAc.mul hA''c).sub (hgc.mul (hAc.pow 2))
  have hF'i : ∀ c, c ∈ Ioo a b → IntegrableOn F' (Ioo c b) := fun c hc =>
    (integrable_norm_iff ((hF'c.mono (Ioo_subset_Ioo hc.1.le le_rfl)).aestronglyMeasurable
      measurableSet_Ioo)).1 (hFi c hc)
  set ρ : ℝ → ℝ := fun t => κ * ‖F' t‖ with hρ
  have hρc : ContinuousOn ρ (Ioo a b) := continuousOn_const.mul hF'c.norm
  have hρi : ∀ c, c ∈ Ioo a b → IntegrableOn ρ (Ioo c b) := fun c hc => (hFi c hc).const_mul κ
  have hρ0 : ∀ t, t ∈ Ioo a b → 0 ≤ ρ t := fun t _ => by positivity
  have hq₂ : ∀ c, c ∈ Ioo a b → IntegrableOn (fun t => E t ^ 2 * F' t) (Ioo c b) := by
    intro c hc
    refine Integrable.mono' ((hFi c hc).const_mul (‖E c‖ ^ 2))
      (((hEc.pow 2).mul hF'c).mono (Ioo_subset_Ioo hc.1.le le_rfl) |>.aestronglyMeasurable
        measurableSet_Ioo)
      (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_)
    rw [norm_mul, norm_pow]
    gcongr
    exact hEle c t hc ht
  have hp₂c : ContinuousOn (fun x => (2 * k)⁻¹ * (E x ^ 2)⁻¹) (Ioo a b) :=
    continuousOn_const.mul ((hEc.pow 2).inv₀ fun x hx => pow_ne_zero 2 (hE0 x hx))
  obtain ⟨h, hhm, hhb, hheq⟩ := IntervalVolterra.exists_volterra_solution (𝕜 := 𝕜)
    (p₁ := fun _ => -(2 * k)⁻¹) (q₁ := fun _ => 1)
    (p₂ := fun x => (2 * k)⁻¹ * (E x ^ 2)⁻¹) (q₂ := fun t => E t ^ 2) (ψ := F')
    (J := fun _ => 1) (ρ := ρ) (a := a) (b := b)
    aestronglyMeasurable_const (hp₂c.aestronglyMeasurable measurableSet_Ioo)
    (fun c hc => by simpa using hF'i c hc) hq₂ aestronglyMeasurable_const
    (fun _ _ => by simp) hρc hρi (fun x t hx hxt => by
      have heq : (-(2 * k)⁻¹ * 1 + (2 * k)⁻¹ * (E x ^ 2)⁻¹ * E t ^ 2) =
          -((1 - E t ^ 2 / E x ^ 2) / (2 * k)) := by ring
      rw [heq, norm_mul, norm_neg]
      exact mul_le_mul_of_nonneg_right (hK x t hx hxt) (norm_nonneg _))
  set R : ℝ → ℝ := fun t => ∫ s in Ioo t b, ρ s with hR
  have hRx : ∀ x, R x = κ * ∫ t in Ioo x b, ‖F' t‖ := fun x => integral_const_mul _ _
  have hub : ∀ t, t ∈ Ioo a b → ‖1 + h t‖ ≤ Real.exp (R t) := fun t ht =>
    (norm_add_le _ _).trans (by have := hhb t ht; simp only [norm_one]; linarith)
  have hum : AEStronglyMeasurable (fun t => 1 + h t) (volume.restrict (Ioo a b)) :=
    aestronglyMeasurable_const.add hhm
  have hub' : ∀ x, x ∈ Ioo a b → ∀ t ∈ Ioo x b, ‖1 + h t‖ ≤ Real.exp (R x) := fun x hx t ht =>
    (hub t ⟨hx.1.trans ht.1, ht.2⟩).trans (Real.exp_le_exp.2
      (IntervalVolterra.tail_anti hρ0 hρi hx ht.1.le))
  have hmulb : ∀ {q : ℝ → 𝕜}, (∀ c, c ∈ Ioo a b → IntegrableOn (fun t => q t * F' t) (Ioo c b)) →
      ∀ c, c ∈ Ioo a b → IntegrableOn (fun t => q t * F' t * (1 + h t)) (Ioo c b) := by
    intro q hq c hc
    exact (hq c hc).mul_bdd (hum.mono_measure (Measure.restrict_mono
      (Ioo_subset_Ioo hc.1.le le_rfl) le_rfl))
      (ae_restrict_of_forall_mem measurableSet_Ioo (hub' c hc))
  have hI₁i := hmulb (q := fun _ => 1) (fun c hc => by simpa using hF'i c hc)
  have hI₂i := hmulb hq₂
  set I₁ : ℝ → 𝕜 := fun x => ∫ t in Ioo x b, 1 * F' t * (1 + h t) with hI₁
  set I₂ : ℝ → 𝕜 := fun x => ∫ t in Ioo x b, E t ^ 2 * F' t * (1 + h t) with hI₂
  have hheq' : ∀ x, x ∈ Ioo a b → h x = -(2 * k)⁻¹ * I₁ x + (2 * k)⁻¹ * (E x ^ 2)⁻¹ * I₂ x :=
    fun x hx => hheq x hx
  have hhc : ContinuousOn h (Ioo a b) :=
    ((continuousOn_const.mul (IntervalVolterra.continuousOn_integral_Ioo hI₁i)).add
      (hp₂c.mul (IntervalVolterra.continuousOn_integral_Ioo hI₂i))).congr fun x hx => hheq' x hx
  have hI₁d : ∀ x, x ∈ Ioo a b → HasDerivAt I₁ (-(1 * F' x * (1 + h x))) x := fun x hx =>
    IntervalVolterra.hasDerivAt_integral_Ioo hI₁i hx ((continuousOn_const.mul hF'c).mul
      (continuousOn_const.add hhc) |>.continuousAt (Ioo_mem_nhds hx.1 hx.2))
  have hI₂d : ∀ x, x ∈ Ioo a b → HasDerivAt I₂ (-(E x ^ 2 * F' x * (1 + h x))) x := fun x hx =>
    IntervalVolterra.hasDerivAt_integral_Ioo hI₂i hx (((hEc.pow 2).mul hF'c).mul
      (continuousOn_const.add hhc) |>.continuousAt (Ioo_mem_nhds hx.1 hx.2))
  have hEinv : ∀ x, x ∈ Ioo a b → HasDerivAt (fun y => (E y ^ 2)⁻¹)
      (-((2 : ℕ) * E x ^ (2 - 1) * -(k * (A x ^ 2)⁻¹ * E x)) / (E x ^ 2) ^ 2) x :=
    fun x hx => ((hE x hx).pow 2).inv (pow_ne_zero 2 (hE0 x hx))
  obtain ⟨ε', hε'def⟩ : ∃ ε' : ℝ → 𝕜, ε' = fun x => (A x ^ 2)⁻¹ * (E x ^ 2)⁻¹ * I₂ x :=
    ⟨_, rfl⟩
  have hεd : ∀ x, x ∈ Ioo a b → HasDerivAt h (ε' x) x := by
    intro x hx
    have := ((hasDerivAt_const x (-(2 * k)⁻¹)).mul (hI₁d x hx)).add
      (((hasDerivAt_const x (2 * k)⁻¹).mul (hEinv x hx)).mul (hI₂d x hx))
    refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
    · have := hA x hx
      have := hE0 x hx
      rw [hε'def]
      simp only [Pi.mul_apply]
      field_simp
      ring
    · filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy using hheq' y hy
  have hε'd : ∀ x, x ∈ Ioo a b → HasDerivAt ε'
      (-(2 * (A x * A' x - k)) * ε' x / A x ^ 2 - F' x * (1 + h x) / A x ^ 2) x := by
    intro x hx
    have := ((((hA' x hx).pow 2).inv (pow_ne_zero 2 (hA x hx))).mul (hEinv x hx)).mul
      (hI₂d x hx)
    rw [hε'def]
    refine this.congr_deriv ?_
    have := hA x hx
    have := hE0 x hx
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
    field_simp
    ring
  refine ⟨h, ε', fun y => E y * ((A' y - k * (A y)⁻¹) * (1 + h y) + A y * ε' y),
    fun x hx => ⟨hεd x hx, ?_, ?_, ?_, ?_⟩⟩
  · refine (((hA' x hx).mul (hE x hx)).mul ((hεd x hx).const_add 1)).congr_deriv ?_
    have := hA x hx
    simp only [Pi.mul_apply]
    field_simp
    ring
  · refine ((hE x hx).mul ((((hA'' x hx).sub (((hA' x hx).inv (hA x hx)).const_mul k)).mul
      ((hεd x hx).const_add 1)).add ((hA' x hx).mul (hε'd x hx)))).congr_deriv ?_
    have := hA x hx
    rw [hF']
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.inv_apply]
    field_simp
    ring
  · rw [← hRx]
    exact hhb x hx
  · rw [← hRx]
    have hεx : A x ^ 2 * ε' x = ∫ t in Ioo x b, (E x ^ 2)⁻¹ * (E t ^ 2 * F' t * (1 + h t)) := by
      have := hA x hx
      rw [integral_const_mul, hε'def]
      field_simp
      rfl
    have hexpt := IntervalVolterra.integral_Ioo_mul_exp_tail hρc hρ0 hρi hx
    have hEx : 0 < ‖E x‖ ^ 2 := by have := hE0 x hx; positivity
    calc ‖A x ^ 2 * ε' x‖
        = ‖∫ t in Ioo x b, (E x ^ 2)⁻¹ * (E t ^ 2 * F' t * (1 + h t))‖ := by rw [hεx]
      _ ≤ ∫ t in Ioo x b, κ⁻¹ * (ρ t * Real.exp (R t)) := by
          refine norm_integral_le_of_norm_le (hexpt.1.const_mul κ⁻¹)
            (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_)
          have hle : ‖E t‖ ^ 2 ≤ ‖E x‖ ^ 2 := by
            have := hEle x t hx ht
            gcongr
          rw [norm_mul, norm_inv, norm_mul, norm_mul, norm_pow, norm_pow]
          calc (‖E x‖ ^ 2)⁻¹ * (‖E t‖ ^ 2 * ‖F' t‖ * ‖1 + h t‖)
              ≤ (‖E x‖ ^ 2)⁻¹ * (‖E x‖ ^ 2 * ‖F' t‖ * Real.exp (R t)) := by
                gcongr
                exact hub t ⟨hx.1.trans ht.1, ht.2⟩
            _ = κ⁻¹ * (ρ t * Real.exp (R t)) := by
                have : ‖E x‖ ≠ 0 := norm_ne_zero_iff.2 (hE0 x hx)
                simp only [hρ]
                field_simp
      _ = (Real.exp (R x) - 1) / κ := by
          rw [integral_const_mul, hexpt.2, div_eq_inv_mul]

/-- The exponential Liouville–Green kernel: for `ξ' = A⁻²` and `u > 0`, `E = exp (-u ξ)` solves
`E' = -u A⁻² E`, `|E|` is nonincreasing and `|(1 - E(t)²/E(x)²)/(2u)| ≤ 1/(2u)` for `x < t`. -/
theorem exp_kernel {a b u : ℝ} (hu : 0 < u) {A ξ : ℝ → ℝ}
    (hξ : ∀ x, x ∈ Ioo a b → HasDerivAt ξ ((A x ^ 2)⁻¹) x) :
    (∀ x, x ∈ Ioo a b → Real.exp (-(u * ξ x)) ≠ 0) ∧
    (∀ x, x ∈ Ioo a b → HasDerivAt (fun y => Real.exp (-(u * ξ y)))
      (-(u * (A x ^ 2)⁻¹ * Real.exp (-(u * ξ x)))) x) ∧
    (∀ x t, x ∈ Ioo a b → t ∈ Ioo x b → ‖Real.exp (-(u * ξ t))‖ ≤ ‖Real.exp (-(u * ξ x))‖) ∧
    (∀ x t, x ∈ Ioo a b → t ∈ Ioo x b →
      ‖(1 - Real.exp (-(u * ξ t)) ^ 2 / Real.exp (-(u * ξ x)) ^ 2) / (2 * u)‖ ≤ 1 / (2 * u)) := by
  set E : ℝ → ℝ := fun y => Real.exp (-(u * ξ y)) with hEdef
  have hmono : MonotoneOn ξ (Ioo a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo a b)
      (fun y hy => (hξ y hy).continuousAt.continuousWithinAt)
      (fun y hy =>
        (hξ y (by simpa only [interior_Ioo] using hy)).differentiableAt.differentiableWithinAt)
      (fun y hy => ?_)
    rw [interior_Ioo] at hy
    rw [(hξ y hy).deriv]
    positivity
  have hξle : ∀ x t, x ∈ Ioo a b → t ∈ Ico x b → ξ x ≤ ξ t :=
    fun x t hx ht => hmono hx ⟨hx.1.trans_le ht.1, ht.2⟩ ht.1
  have hEle' : ∀ x t, x ∈ Ioo a b → t ∈ Ico x b → E t ≤ E x := fun x t hx hxt => by
    simp only [hEdef]
    gcongr
    exact hξle x t hx hxt
  have hEpos : ∀ y, 0 < E y := fun y => Real.exp_pos _
  refine ⟨fun x _ => (hEpos x).ne', fun x hx => ?_, fun x t hx hxt => ?_,
    fun x t hx hxt => ?_⟩
  · exact ((hξ x hx).const_mul u).neg.exp.congr_deriv (by simp only [Pi.neg_apply]; ring)
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hEpos t), abs_of_pos (hEpos x)]
    exact hEle' x t hx ⟨hxt.1.le, hxt.2⟩
  · have h1 : E t ^ 2 / E x ^ 2 ≤ 1 := by
      rw [div_le_one (by have := hEpos x; positivity)]
      have := hEle' x t hx ⟨hxt.1.le, hxt.2⟩
      have := hEpos t
      gcongr
    have h0 : 0 < E t ^ 2 / E x ^ 2 := by have := hEpos x; have := hEpos t; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) (by positivity))]
    gcongr
    linarith


/-- **Liouville–Green approximation, exponential case with a large parameter** (Olver,
*Asymptotics and Special Functions*, Ch. 6, Thm. 2.1 for `u = 1`, and Ch. 10, Thm. 3.1).
Let `A ≠ 0` be twice differentiable on `(a, b)` and `ξ' = A⁻²` (for `A = f^{-1/4}` this is
`ξ = ∫ f^{1/2}`). For `u > 0`, the equation `w'' = (u² A⁻⁴ + g) w` has a solution
`w = A exp (-u ξ) (1 + ε)` with

`|ε x| ≤ exp (V x / (2u)) - 1`,   `|A(x)² ε'(x)| ≤ 2u (exp (V x / (2u)) - 1)`,

where `V x = ∫_{(x,b)} |A A'' - g A²|` is the variation of the error-control function on
`(x, b)`. The errors are controlled from the finite right endpoint `b`. -/
theorem exists_solution_exp {a b u : ℝ} (hu : 0 < u) {A A' A'' ξ g : ℝ → ℝ}
    (hA : ∀ x, x ∈ Ioo a b → A x ≠ 0)
    (hA' : ∀ x, x ∈ Ioo a b → HasDerivAt A (A' x) x)
    (hA'' : ∀ x, x ∈ Ioo a b → HasDerivAt A' (A'' x) x)
    (hA''c : ContinuousOn A'' (Ioo a b)) (hgc : ContinuousOn g (Ioo a b))
    (hξ : ∀ x, x ∈ Ioo a b → HasDerivAt ξ ((A x ^ 2)⁻¹) x)
    (hFi : ∀ c, c ∈ Ioo a b → IntegrableOn (fun t => |A t * A'' t - g t * A t ^ 2|) (Ioo c b)) :
    ∃ ε ε' w' : ℝ → ℝ, ∀ x, x ∈ Ioo a b →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => A y * Real.exp (-(u * ξ y)) * (1 + ε y)) (w' x) x ∧
      HasDerivAt w'
        ((u ^ 2 * (A x ^ 4)⁻¹ + g x) * (A x * Real.exp (-(u * ξ x)) * (1 + ε x))) x ∧
      |ε x| ≤ Real.exp ((∫ t in Ioo x b, |A t * A'' t - g t * A t ^ 2|) / (2 * u)) - 1 ∧
      |A x ^ 2 * ε' x| ≤
        2 * u * (Real.exp ((∫ t in Ioo x b, |A t * A'' t - g t * A t ^ 2|) / (2 * u)) - 1) := by
  obtain ⟨hE0, hE, hEle, hK⟩ := exp_kernel (a := a) (b := b) hu hξ
  obtain ⟨ε, ε', w', H⟩ := exists_solution_of_kernel_bound (𝕜 := ℝ) (a := a) (b := b)
    (κ := 1 / (2 * u)) (k := u) (A := A) (A' := A') (A'' := A'')
    (E := fun y => Real.exp (-(u * ξ y))) (g := g)
    hu.ne' (by positivity) hA hA' hA'' hA''c hgc hE0 hE hEle hK
    (fun c hc => by simpa only [Real.norm_eq_abs] using hFi c hc)
  refine ⟨ε, ε', w', fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := H x hx
  simp only [Real.norm_eq_abs] at h4 h5
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · convert h4 using 3
    ring
  · convert h5 using 1
    rw [show 1 / (2 * u) * ∫ t in Ioo x b, |A t * A'' t - g t * A t ^ 2| =
      (∫ t in Ioo x b, |A t * A'' t - g t * A t ^ 2|) / (2 * u) by ring]
    field_simp


/-- The amplitude `A = f^{-1/4}`: its first two derivatives, `A⁻² = f^{1/2}`, `A⁻⁴ = f`, and
`A A'' - g A² = errorDensity f f' f'' g`. -/
theorem amplitude {a b : ℝ} {f f' f'' g : ℝ → ℝ} (hf : ∀ x, x ∈ Ioo a b → 0 < f x)
    (hf' : ∀ x, x ∈ Ioo a b → HasDerivAt f (f' x) x)
    (hf'' : ∀ x, x ∈ Ioo a b → HasDerivAt f' (f'' x) x)
    (hf''c : ContinuousOn f'' (Ioo a b)) {x : ℝ} (hx : x ∈ Ioo a b) :
    f x ^ (-(1 / 4) : ℝ) ≠ 0 ∧
    HasDerivAt (fun y => f y ^ (-(1 / 4) : ℝ)) (-(1 / 4) * f' x * f x ^ (-(5 / 4) : ℝ)) x ∧
    HasDerivAt (fun y => -(1 / 4) * f' y * f y ^ (-(5 / 4) : ℝ))
      (-(1 / 4) * f'' x * f x ^ (-(5 / 4) : ℝ) + 5 / 16 * f' x ^ 2 * f x ^ (-(9 / 4) : ℝ)) x ∧
    ContinuousOn (fun y => -(1 / 4) * f'' y * f y ^ (-(5 / 4) : ℝ) +
      5 / 16 * f' y ^ 2 * f y ^ (-(9 / 4) : ℝ)) (Ioo a b) ∧
    ((f x ^ (-(1 / 4) : ℝ)) ^ 2)⁻¹ = √(f x) ∧
    ((f x ^ (-(1 / 4) : ℝ)) ^ 4)⁻¹ = f x ∧
    (f x ^ (-(1 / 4) : ℝ)) ^ 2 = (√(f x))⁻¹ ∧
    f x ^ (-(1 / 4) : ℝ) * (-(1 / 4) * f'' x * f x ^ (-(5 / 4) : ℝ) +
      5 / 16 * f' x ^ 2 * f x ^ (-(9 / 4) : ℝ)) - g x * (f x ^ (-(1 / 4) : ℝ)) ^ 2 =
      errorDensity f f' f'' g x := by
  have hfx := hf x hx
  have hpow : ∀ (p : ℝ) (n : ℕ), (f x ^ p) ^ n = f x ^ (p * n) := fun p n => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hfx.le]
  have hmul : ∀ p q : ℝ, f x ^ p * f x ^ q = f x ^ (p + q) := fun p q =>
    (Real.rpow_add hfx p q).symm
  have hsq : (f x ^ (-(1 / 4) : ℝ)) ^ 2 = (√(f x))⁻¹ := by
    rw [hpow, Real.sqrt_eq_rpow, ← Real.rpow_neg hfx.le]
    norm_num
  refine ⟨(Real.rpow_pos_of_pos hfx _).ne', ?_, ?_, ?_, ?_, ?_, hsq, ?_⟩
  · refine ((hf' x hx).rpow_const (p := -(1 / 4)) (Or.inl hfx.ne')).congr_deriv ?_
    rw [show (-(1 / 4 : ℝ)) - 1 = -(5 / 4) by norm_num]
    ring
  · refine (((hf'' x hx).const_mul (-(1 / 4))).mul
      ((hf' x hx).rpow_const (p := -(5 / 4)) (Or.inl hfx.ne'))).congr_deriv ?_
    rw [show (-(5 / 4 : ℝ)) - 1 = -(9 / 4) by norm_num]
    ring
  · have hfc : ContinuousOn f (Ioo a b) := fun y hy => (hf' y hy).continuousAt.continuousWithinAt
    have hf'c : ContinuousOn f' (Ioo a b) := fun y hy =>
      (hf'' y hy).continuousAt.continuousWithinAt
    exact ((continuousOn_const.mul hf''c).mul
        (hfc.rpow_const fun y hy => Or.inl (hf y hy).ne')).add
      ((continuousOn_const.mul (hf'c.pow 2)).mul
        (hfc.rpow_const fun y hy => Or.inl (hf y hy).ne'))
  · rw [hsq, inv_inv]
  · rw [hpow, ← Real.rpow_neg hfx.le]
    norm_num
  · have h1 : f x ^ (-(1 / 4) : ℝ) * (-(1 / 4) * f'' x * f x ^ (-(5 / 4) : ℝ)) =
        -(1 / 4) * f'' x * f x ^ (-(3 / 2) : ℝ) := by
      rw [show (-(3 / 2) : ℝ) = -(1 / 4) + -(5 / 4) by norm_num, ← hmul]
      ring
    have h2 : f x ^ (-(1 / 4) : ℝ) * (5 / 16 * f' x ^ 2 * f x ^ (-(9 / 4) : ℝ)) =
        5 / 16 * f' x ^ 2 * f x ^ (-(5 / 2) : ℝ) := by
      rw [show (-(5 / 2) : ℝ) = -(1 / 4) + -(9 / 4) by norm_num, ← hmul]
      ring
    rw [hsq, errorDensity, mul_add, h1, h2, Real.sqrt_eq_rpow, ← Real.rpow_neg hfx.le]
    ring


/-- **Olver's Liouville–Green theorem, exponential case** (Olver, *Asymptotics and Special
Functions*, Ch. 6, Thm. 2.1 for `u = 1`; Ch. 10, Thm. 3.1). Let `f > 0` be twice differentiable
with continuous `f''` and `g` continuous on `(a, b)`, and let `ξ' = f^{1/2}`. If the error-control
function `F = ∫ (f^{-1/4} (f^{-1/4})'' - g f^{-1/2})` has finite variation `V x` on `(x, b)`,
then for `u > 0` the equation `w'' = (u² f + g) w` has the solution
`w = f^{-1/4} exp (-u ξ) (1 + ε)` with

`|ε x| ≤ exp (V x / (2u)) - 1`,   `|ε' x| ≤ 2u f(x)^{1/2} (exp (V x / (2u)) - 1)`.

In particular `ε = O(1/u)` uniformly in `x` when `V` is bounded (`Real.exp_sub_one_le_mul_exp`). -/
theorem exists_solution_exp_of_pos {a b u : ℝ} (hab : a < b) (hu : 0 < u) {f f' f'' g ξ : ℝ → ℝ}
    (hf : ∀ x, x ∈ Ioo a b → 0 < f x)
    (hf' : ∀ x, x ∈ Ioo a b → HasDerivAt f (f' x) x)
    (hf'' : ∀ x, x ∈ Ioo a b → HasDerivAt f' (f'' x) x)
    (hf''c : ContinuousOn f'' (Ioo a b)) (hgc : ContinuousOn g (Ioo a b))
    (hξ : ∀ x, x ∈ Ioo a b → HasDerivAt ξ (√(f x)) x)
    (hFi : ∀ c, c ∈ Ioo a b → IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ioo c b)) :
    ∃ ε ε' w' : ℝ → ℝ, ∀ x, x ∈ Ioo a b →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => f y ^ (-(1 / 4) : ℝ) * Real.exp (-(u * ξ y)) * (1 + ε y)) (w' x) x ∧
      HasDerivAt w' ((u ^ 2 * f x + g x) *
        (f x ^ (-(1 / 4) : ℝ) * Real.exp (-(u * ξ x)) * (1 + ε x))) x ∧
      |ε x| ≤ Real.exp ((∫ t in Ioo x b, |errorDensity f f' f'' g t|) / (2 * u)) - 1 ∧
      |ε' x| ≤
        2 * u * √(f x) *
          (Real.exp ((∫ t in Ioo x b, |errorDensity f f' f'' g t|) / (2 * u)) - 1) := by
  have H := fun x (hx : x ∈ Ioo a b) => amplitude (g := g) hf hf' hf'' hf''c hx
  obtain ⟨ε, ε', w', H'⟩ := exists_solution_exp hu (fun x hx => (H x hx).1)
    (fun x hx => (H x hx).2.1) (fun x hx => (H x hx).2.2.1)
    (H ((a + b) / 2) (by constructor <;> linarith)).2.2.2.1 hgc
    (fun x hx => by rw [(H x hx).2.2.2.2.1]; exact hξ x hx)
    (fun c hc => (hFi c hc).congr_fun
      (fun t ht => congrArg abs (H t ⟨hc.1.trans ht.1, ht.2⟩).2.2.2.2.2.2.2.symm)
      measurableSet_Ioo)
  refine ⟨ε, ε', w', fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := H' x hx
  have hV := setIntegral_congr_fun (μ := volume) measurableSet_Ioo
    (fun t ht => congrArg abs (H t ⟨hx.1.trans ht.1, ht.2⟩).2.2.2.2.2.2.2)
  rw [hV] at h4 h5
  refine ⟨h1, h2, ?_, h4, ?_⟩
  · rwa [(H x hx).2.2.2.2.2.1] at h3
  · rw [abs_mul, (H x hx).2.2.2.2.2.2.1, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)] at h5
    have hs : 0 < √(f x) := Real.sqrt_pos.2 (hf x hx)
    rw [inv_mul_le_iff₀ hs] at h5
    linarith


end LiouvilleGreen.Interval
