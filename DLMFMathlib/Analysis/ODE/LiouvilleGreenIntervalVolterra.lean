/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LiouvilleGreenVolterra

/-!
# Volterra equations with an integrable singular finite endpoint

The Liouville–Neumann construction for rank-two kernels on `(a,b)`, with integration over
`(x,b)`. The upper endpoint need not be a regular point of the coefficient functions.
The estimates follow Olver, *Asymptotics and Special Functions*, Chapter 6, §§2 and 10.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace LiouvilleGreen.IntervalVolterra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite tail equals the corresponding interval integral. -/
theorem integral_Ioo_eq_intervalIntegral {f : ℝ → E} {x b : ℝ} (hx : x ≤ b) :
    ∫ t in Ioo x b, f t = ∫ t in x..b, f t := by
  rw [intervalIntegral.integral_of_le hx, integral_Ioc_eq_integral_Ioo]

/-- Finite tail integrals are continuous at every interior point. -/
theorem continuousOn_integral_Ioo {f : ℝ → E} {a b : ℝ}
    (hf : ∀ c ∈ Ioo a b, IntegrableOn f (Ioo c b)) :
    ContinuousOn (fun x => ∫ t in Ioo x b, f t) (Ioo a b) := by
  intro x hx
  let c := (a + x) / 2
  have hac : a < c := by dsimp [c]; linarith [hx.1]
  have hcx : c < x := by dsimp [c]; linarith [hx.1]
  have hcb : c < b := hcx.trans hx.2
  have hi : IntegrableOn f (uIcc c b) := by
    rw [uIcc_of_le hcb.le, integrableOn_Icc_iff_integrableOn_Ioo]
    exact hf c ⟨hac, hcb⟩
  have hc := intervalIntegral.continuousOn_primitive_interval_left hi
  have hca : ContinuousAt (fun y => ∫ t in y..b, f t) x :=
    hc.continuousAt (by rw [uIcc_of_le hcb.le]; exact Icc_mem_nhds hcx hx.2)
  refine (hca.congr ?_).continuousWithinAt
  filter_upwards [Iio_mem_nhds hx.2] with y hy
  exact (integral_Ioo_eq_intervalIntegral hy.le).symm

/-- The derivative of a finite tail at a point of continuity of its integrand. -/
theorem hasDerivAt_integral_Ioo [CompleteSpace E] {f : ℝ → E} {a b x : ℝ}
    (hf : ∀ c ∈ Ioo a b, IntegrableOn f (Ioo c b)) (hx : x ∈ Ioo a b)
    (hfx : ContinuousAt f x) :
    HasDerivAt (fun y => ∫ t in Ioo y b, f t) (-f x) x := by
  let c := (a + x) / 2
  have hcx : c < x := by dsimp [c]; linarith [hx.1]
  have hc : c ∈ Ioo a b := by dsimp [c]; constructor <;> linarith [hx.1, hx.2]
  have hi : IntervalIntegrable f volume x b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.2.le).2 (hf x hx)
  have hd := intervalIntegral.integral_hasDerivAt_left hi
    (AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem (hf c hc).aestronglyMeasurable
      (Ioo_mem_nhds hcx hx.2)) hfx
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hx.2] with y hy
  exact integral_Ioo_eq_intervalIntegral hy.le

/-- An integrable finite tail tends to zero at its upper endpoint. -/
theorem tendsto_integral_Ioo {f : ℝ → E} {c b : ℝ} (hcb : c < b)
    (hf : IntegrableOn f (Ioo c b)) :
    Tendsto (fun y => ∫ t in Ioo y b, f t) (𝓝[<] b) (𝓝 0) := by
  have hi : IntegrableOn f (uIcc c b) := by
    rw [uIcc_of_le hcb.le, integrableOn_Icc_iff_integrableOn_Ioo]
    exact hf
  have hc := intervalIntegral.continuousOn_primitive_interval_left hi
  rw [uIcc_of_le hcb.le] at hc
  have ht : ContinuousWithinAt (fun y => ∫ t in y..b, f t) (Iio b) b :=
    (hc b ⟨hcb.le, le_rfl⟩).mono_of_mem_nhdsWithin (by
      exact mem_nhdsWithin.2 ⟨Ioi c, isOpen_Ioi, hcb, fun y hy => ⟨hy.1.le, hy.2.le⟩⟩)
  have ht' : Tendsto (fun y => ∫ t in y..b, f t) (𝓝[<] b) (𝓝 0) := by
    simpa using ht.tendsto
  refine ht'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (integral_Ioo_eq_intervalIntegral hy.le).symm

section Tail

variable {ρ : ℝ → ℝ} {a b : ℝ}

/-- A nonnegative finite tail is nonnegative. -/
theorem tail_nonneg (hρ0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t) {x : ℝ} (hx : a ≤ x) :
    0 ≤ ∫ t in Ioo x b, ρ t :=
  setIntegral_nonneg measurableSet_Ioo fun t ht => hρ0 t ⟨hx.trans_lt ht.1, ht.2⟩

/-- Finite tails of a nonnegative integrable function are antitone. -/
theorem tail_anti (hρ0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t)
    (hρi : ∀ c ∈ Ioo a b, IntegrableOn ρ (Ioo c b)) {x y : ℝ}
    (hx : x ∈ Ioo a b) (hxy : x ≤ y) :
    ∫ t in Ioo y b, ρ t ≤ ∫ t in Ioo x b, ρ t :=
  setIntegral_mono_set (hρi x hx)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => hρ0 t ⟨hx.1.trans ht.1, ht.2⟩)
    (Ioo_subset_Ioo hxy le_rfl).eventuallyLE

/-- Integrating a continuous function of an integrable finite tail. -/
theorem integral_Ioo_mul_comp_tail (hρc : ContinuousOn ρ (Ioo a b))
    (hρ0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t)
    (hρi : ∀ c ∈ Ioo a b, IntegrableOn ρ (Ioo c b))
    {Φ φ : ℝ → ℝ} (hΦ : ∀ s, HasDerivAt Φ (φ s) s) (hφ : Continuous φ)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    IntegrableOn (fun t => ρ t * φ (∫ s in Ioo t b, ρ s)) (Ioo x b) ∧
      ∫ t in Ioo x b, ρ t * φ (∫ s in Ioo t b, ρ s) =
        Φ (∫ s in Ioo x b, ρ s) - Φ 0 := by
  set R : ℝ → ℝ := fun t => ∫ s in Ioo t b, ρ s
  have hRc : ContinuousOn R (Ioo a b) := continuousOn_integral_Ioo hρi
  have hRd : ∀ t ∈ Ioo a b, HasDerivAt R (-ρ t) t := fun t ht =>
    hasDerivAt_integral_Ioo hρi ht (hρc.continuousAt (Ioo_mem_nhds ht.1 ht.2))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := R x)).exists_bound_of_continuousOn
    hφ.continuousOn
  have hsub : Ioo x b ⊆ Ioo a b := Ioo_subset_Ioo hx.1.le le_rfl
  have hmem : ∀ t ∈ Ioo x b, R t ∈ Icc 0 (R x) := fun t ht =>
    ⟨tail_nonneg hρ0 (hx.1.trans ht.1).le, tail_anti hρ0 hρi hx ht.1.le⟩
  have hint : IntegrableOn (fun t => ρ t * φ (R t)) (Ioo x b) :=
    (hρi x hx).mul_bdd
      ((hφ.comp_continuousOn (hRc.mono hsub)).aestronglyMeasurable measurableSet_Ioo)
      (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => hC _ (hmem t ht))
  refine ⟨hint, ?_⟩
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := fun t => -Φ (R t)) (f' := fun t => ρ t * φ (R t)) hx.2
    (fun t ht => ((hΦ (R t)).comp t (hRd t (hsub ht))).neg.congr_deriv (by ring))
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hx.2.le).2 hint)
    (((hΦ (R x)).continuousAt.comp (hRd x hx).continuousAt).neg.tendsto.mono_left
      nhdsWithin_le_nhds)
    (((hΦ 0).continuousAt.tendsto.comp (tendsto_integral_Ioo hx.2 (hρi x hx))).neg)
  rw [← integral_Ioo_eq_intervalIntegral hx.2.le] at hft
  rw [hft]
  change -Φ 0 - -Φ (R x) = Φ (R x) - Φ 0
  ring

/-- `∫_{(x,b)} ρ R^n / n! = R(x)^{n+1} / (n+1)!` for the tail `R` of `ρ`. -/
theorem integral_Ioo_mul_tail_pow (hρc : ContinuousOn ρ (Ioo a b))
    (hρ0 : ∀ t, t ∈ Ioo a b → 0 ≤ ρ t) (hρi : ∀ c, c ∈ Ioo a b → IntegrableOn ρ (Ioo c b)) (n : ℕ)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    IntegrableOn (fun t => ρ t * ((∫ s in Ioo t b, ρ s) ^ n / n.factorial)) (Ioo x b) ∧
      ∫ t in Ioo x b, ρ t * ((∫ s in Ioo t b, ρ s) ^ n / n.factorial) =
        (∫ s in Ioo x b, ρ s) ^ (n + 1) / (n + 1).factorial := by
  have h := integral_Ioo_mul_comp_tail hρc hρ0 hρi
    (Φ := fun s => s ^ (n + 1) / (n + 1).factorial) (φ := fun s => s ^ n / n.factorial)
    (fun s => by
      convert (hasDerivAt_pow (n + 1) s).div_const ((n + 1).factorial : ℝ) using 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp)
    (by fun_prop) hx
  simpa using h

/-- `∫_{(x,b)} ρ exp(R) = exp(R x) - 1` for the tail `R` of `ρ`. -/
theorem integral_Ioo_mul_exp_tail (hρc : ContinuousOn ρ (Ioo a b))
    (hρ0 : ∀ t, t ∈ Ioo a b → 0 ≤ ρ t) (hρi : ∀ c, c ∈ Ioo a b → IntegrableOn ρ (Ioo c b))
    {x : ℝ} (hx : x ∈ Ioo a b) :
    IntegrableOn (fun t => ρ t * Real.exp (∫ s in Ioo t b, ρ s)) (Ioo x b) ∧
      ∫ t in Ioo x b, ρ t * Real.exp (∫ s in Ioo t b, ρ s) =
        Real.exp (∫ s in Ioo x b, ρ s) - 1 := by
  have h := integral_Ioo_mul_comp_tail hρc hρ0 hρi (Φ := Real.exp) (φ := Real.exp)
    (fun s => Real.hasDerivAt_exp s) Real.continuous_exp hx
  simpa using h

end Tail

section Volterra

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The Volterra operator with the rank-two kernel `K x t = p₁ x q₁ t + p₂ x q₂ t` and weight
`ψ`: `(L φ) x = ∫_{(x,b)} K x t ψ t φ t dt`, written with the two factors separated. -/
noncomputable def volterraOp (b : ℝ) (p₁ p₂ q₁ q₂ ψ : ℝ → 𝕜) (φ : ℝ → 𝕜) (x : ℝ) : 𝕜 :=
  p₁ x * (∫ t in Ioo x b, q₁ t * ψ t * φ t) + p₂ x * ∫ t in Ioo x b, q₂ t * ψ t * φ t

variable {p₁ p₂ q₁ q₂ ψ : ℝ → 𝕜} {ρ : ℝ → ℝ} {a b : ℝ}

/-- One Picard step: if `‖φ t‖ ≤ B t R(t)ⁿ / n!` with `R` the tail of `ρ` and `B ≥ 0`
nonincreasing, then the integrands of `volterraOp` are integrable, `volterraOp φ` is measurable
and `‖volterraOp φ x‖ ≤ B x R(x)ⁿ⁺¹ / (n + 1)!`. -/
theorem volterraOp_step
    (hp₁ : AEStronglyMeasurable p₁ (volume.restrict (Ioo a b)))
    (hp₂ : AEStronglyMeasurable p₂ (volume.restrict (Ioo a b)))
    (hq₁ : ∀ c, c ∈ Ioo a b → IntegrableOn (fun t => q₁ t * ψ t) (Ioo c b))
    (hq₂ : ∀ c, c ∈ Ioo a b → IntegrableOn (fun t => q₂ t * ψ t) (Ioo c b))
    (hρc : ContinuousOn ρ (Ioo a b)) (hρi : ∀ c, c ∈ Ioo a b → IntegrableOn ρ (Ioo c b))
    (hK : ∀ x t, x ∈ Ioo a b → t ∈ Ioo x b → ‖(p₁ x * q₁ t + p₂ x * q₂ t) * ψ t‖ ≤ ρ t)
    {B : ℝ → ℝ} (hB0 : ∀ t, t ∈ Ioo a b → 0 ≤ B t)
    (hBa : ∀ x t, x ∈ Ioo a b → x ≤ t → t < b → B t ≤ B x)
    {φ : ℝ → 𝕜} (hφm : AEStronglyMeasurable φ (volume.restrict (Ioo a b))) (n : ℕ)
    (hφ : ∀ t, t ∈ Ioo a b → ‖φ t‖ ≤ B t * ((∫ s in Ioo t b, ρ s) ^ n / n.factorial)) :
    (∀ x, x ∈ Ioo a b → IntegrableOn (fun t => q₁ t * ψ t * φ t) (Ioo x b)) ∧
    (∀ x, x ∈ Ioo a b → IntegrableOn (fun t => q₂ t * ψ t * φ t) (Ioo x b)) ∧
    AEStronglyMeasurable (volterraOp b p₁ p₂ q₁ q₂ ψ φ) (volume.restrict (Ioo a b)) ∧
    ∀ x, x ∈ Ioo a b → ‖volterraOp b p₁ p₂ q₁ q₂ ψ φ x‖ ≤
      B x * ((∫ s in Ioo x b, ρ s) ^ (n + 1) / (n + 1).factorial) := by
  have hρ0 : ∀ t, t ∈ Ioo a b → 0 ≤ ρ t := fun t ht =>
    (norm_nonneg _).trans (hK ((a + t) / 2) t
      ⟨by linarith [ht.1], by linarith [ht.1, ht.2]⟩ ⟨by linarith [ht.1], ht.2⟩)
  have hRle : ∀ x, x ∈ Ioo a b → ∀ t ∈ Ioo x b,
      (∫ s in Ioo t b, ρ s) ^ n / n.factorial ≤ (∫ s in Ioo x b, ρ s) ^ n / n.factorial :=
    fun x hx t ht => div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (tail_nonneg hρ0 (hx.1.trans ht.1).le)
        (tail_anti hρ0 hρi hx ht.1.le) n) (Nat.cast_nonneg _)
  have hφx : ∀ x, x ∈ Ioo a b → ∀ t ∈ Ioo x b,
      ‖φ t‖ ≤ B x * ((∫ s in Ioo x b, ρ s) ^ n / n.factorial) :=
    fun x hx t ht => (hφ t ⟨hx.1.trans ht.1, ht.2⟩).trans (mul_le_mul (hBa x t hx ht.1.le ht.2)
      (hRle x hx t ht) (by have := tail_nonneg hρ0 (hx.1.trans ht.1).le; positivity)
      (hB0 x hx))
  have hint : ∀ {q : ℝ → 𝕜}, (∀ c, c ∈ Ioo a b → IntegrableOn (fun t => q t * ψ t) (Ioo c b)) →
      ∀ x, x ∈ Ioo a b → IntegrableOn (fun t => q t * ψ t * φ t) (Ioo x b) := by
    intro q hq x hx
    exact (hq x hx).mul_bdd (hφm.mono_measure (Measure.restrict_mono (Ioo_subset_Ioo hx.1.le le_rfl)
      le_rfl)) (ae_restrict_of_forall_mem measurableSet_Ioo (hφx x hx))
  have hi₁ := hint hq₁
  have hi₂ := hint hq₂
  refine ⟨hi₁, hi₂, ?_, ?_⟩
  · exact (hp₁.mul ((continuousOn_integral_Ioo hi₁).aestronglyMeasurable measurableSet_Ioo)).add
      (hp₂.mul ((continuousOn_integral_Ioo hi₂).aestronglyMeasurable measurableSet_Ioo))
  · intro x hx
    have heq : volterraOp b p₁ p₂ q₁ q₂ ψ φ x =
        ∫ t in Ioo x b, (p₁ x * q₁ t + p₂ x * q₂ t) * ψ t * φ t := by
      rw [volterraOp, ← integral_const_mul, ← integral_const_mul, ← integral_add
        ((hi₁ x hx).const_mul _) ((hi₂ x hx).const_mul _)]
      congr 1
      ext t
      ring
    have hb := integral_Ioo_mul_tail_pow hρc hρ0 hρi n hx
    rw [heq, ← hb.2, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hb.1.const_mul (B x))
      (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_)
    rw [norm_mul]
    have hR0 := tail_nonneg hρ0 (hx.1.trans ht.1).le
    calc ‖(p₁ x * q₁ t + p₂ x * q₂ t) * ψ t‖ * ‖φ t‖
        ≤ ρ t * (B t * ((∫ s in Ioo t b, ρ s) ^ n / n.factorial)) :=
          mul_le_mul (hK x t hx ht) (hφ t ⟨hx.1.trans ht.1, ht.2⟩)
            (norm_nonneg _) (hρ0 t ⟨hx.1.trans ht.1, ht.2⟩)
      _ ≤ ρ t * (B x * ((∫ s in Ioo t b, ρ s) ^ n / n.factorial)) := by
          have := hρ0 t ⟨hx.1.trans ht.1, ht.2⟩
          gcongr
          exact hBa x t hx ht.1.le ht.2
      _ = B x * (ρ t * ((∫ s in Ioo t b, ρ s) ^ n / n.factorial)) := by ring

/-- **Existence and bound for inhomogeneous Volterra equations with a rank-two kernel**
(Olver, *Asymptotics and Special Functions*, Ch. 6, Thm. 10.1, for kernels of the form
`K x t = p₁ x q₁ t + p₂ x q₂ t`, which covers every variation-of-constants kernel).
If `‖K x t ψ t‖ ≤ ρ t` for `a < x < t`, `ρ` is continuous and integrable up to `b`, and the
forcing satisfies `‖σ t‖ ≤ B t` with `B ≥ 0` nonincreasing, then the equation
`h x = σ x + ∫_{(x,b)} K x t ψ t h t dt` has a solution on `(a, b)` with
`‖h x - σ x‖ ≤ B x (exp (∫_{(x,b)} ρ) - 1)`. The solution is the sum of the Picard series. -/
theorem exists_volterra_solution_add
    (hp₁ : AEStronglyMeasurable p₁ (volume.restrict (Ioo a b)))
    (hp₂ : AEStronglyMeasurable p₂ (volume.restrict (Ioo a b)))
    (hq₁ : ∀ c, c ∈ Ioo a b → IntegrableOn (fun t => q₁ t * ψ t) (Ioo c b))
    (hq₂ : ∀ c, c ∈ Ioo a b → IntegrableOn (fun t => q₂ t * ψ t) (Ioo c b))
    {σ : ℝ → 𝕜} {B : ℝ → ℝ} (hσm : AEStronglyMeasurable σ (volume.restrict (Ioo a b)))
    (hσ : ∀ t, t ∈ Ioo a b → ‖σ t‖ ≤ B t) (hBa : ∀ x t, x ∈ Ioo a b → x ≤ t → t < b → B t ≤ B x)
    (hρc : ContinuousOn ρ (Ioo a b)) (hρi : ∀ c, c ∈ Ioo a b → IntegrableOn ρ (Ioo c b))
    (hK : ∀ x t, x ∈ Ioo a b → t ∈ Ioo x b → ‖(p₁ x * q₁ t + p₂ x * q₂ t) * ψ t‖ ≤ ρ t) :
    ∃ h : ℝ → 𝕜, AEStronglyMeasurable h (volume.restrict (Ioo a b)) ∧
      (∀ x, x ∈ Ioo a b → ‖h x - σ x‖ ≤ B x * (Real.exp (∫ s in Ioo x b, ρ s) - 1)) ∧
      ∀ x, x ∈ Ioo a b → h x = σ x + volterraOp b p₁ p₂ q₁ q₂ ψ h x := by
  have hB0 : ∀ t, t ∈ Ioo a b → 0 ≤ B t := fun t ht => (norm_nonneg _).trans (hσ t ht)
  set L := volterraOp b p₁ p₂ q₁ q₂ ψ with hL
  set φ : ℕ → ℝ → 𝕜 := fun n => L^[n] σ with hφdef
  set R : ℝ → ℝ := fun t => ∫ s in Ioo t b, ρ s with hR
  have hφ : ∀ n, AEStronglyMeasurable (φ n) (volume.restrict (Ioo a b)) ∧
      ∀ t, t ∈ Ioo a b → ‖φ n t‖ ≤ B t * (R t ^ n / n.factorial) := by
    intro n
    induction n with
    | zero => exact ⟨hσm, fun t ht => by simpa [φ] using hσ t ht⟩
    | succ n ih =>
      have hs := volterraOp_step hp₁ hp₂ hq₁ hq₂ hρc hρi hK hB0 hBa ih.1 n ih.2
      have hφs : φ (n + 1) = L (φ n) := Function.iterate_succ_apply' L n σ
      rw [hφs]
      exact ⟨hs.2.2.1, hs.2.2.2⟩
  have hstep : ∀ n, _ := fun n => volterraOp_step hp₁ hp₂ hq₁ hq₂ hρc hρi hK hB0 hBa
    (hφ n).1 n (hφ n).2
  have hρ0 : ∀ t, t ∈ Ioo a b → 0 ≤ ρ t := fun t ht =>
    (norm_nonneg _).trans (hK ((a + t) / 2) t
      ⟨by linarith [ht.1], by linarith [ht.1, ht.2]⟩ ⟨by linarith [ht.1], ht.2⟩)
  have hexp : ∀ x, HasSum (fun n => R x ^ n / n.factorial) (Real.exp (R x)) := fun x => by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (R x)
  have hsumm : ∀ x, x ∈ Ioo a b → Summable (fun n => φ n x) := fun x hx =>
    Summable.of_norm_bounded ((hexp x).summable.mul_left (B x)) fun n => (hφ n).2 x hx
  set S : ℝ → 𝕜 := fun x => ∑' n, φ n x with hS
  have hSm : AEStronglyMeasurable S (volume.restrict (Ioo a b)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (f := fun N x => ∑ n ∈ Finset.range N, φ n x)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun n _ => (hφ n).1)
      (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx =>
        (hsumm x hx).hasSum.tendsto_sum_nat)
  have hSσ : ∀ x, x ∈ Ioo a b → S x - σ x = ∑' n, φ (n + 1) x := fun x hx => by
    show ∑' n, φ n x - σ x = _
    rw [(hsumm x hx).tsum_eq_zero_add]
    simp [φ]
  refine ⟨S, hSm, ?_, ?_⟩
  · intro x hx
    have hs1 : HasSum (fun n => B x * (R x ^ (n + 1) / (n + 1).factorial))
        (B x * (Real.exp (R x) - 1)) := by
      have := ((hasSum_nat_add_iff' 1).2 (hexp x)).mul_left (B x)
      simpa using this
    have hnb : ∀ n, ‖φ (n + 1) x‖ ≤ B x * (R x ^ (n + 1) / (n + 1).factorial) :=
      fun n => (hφ (n + 1)).2 x hx
    have hns : Summable fun n => ‖φ (n + 1) x‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnb hs1.summable
    rw [hSσ x hx]
    exact (norm_tsum_le_tsum_norm hns).trans (hns.tsum_le_tsum hnb hs1.summable |>.trans_eq
      hs1.tsum_eq)
  · intro x hx
    -- interchange of sum and integral
    have hswap : ∀ {q : ℝ → 𝕜}, (∀ c, c ∈ Ioo a b → IntegrableOn (fun t => q t * ψ t) (Ioo c b)) →
        (∀ n, IntegrableOn (fun t => q t * ψ t * φ n t) (Ioo x b)) →
        Summable (fun n => ∫ t in Ioo x b, q t * ψ t * φ n t) ∧
        ∫ t in Ioo x b, q t * ψ t * S t = ∑' n, ∫ t in Ioo x b, q t * ψ t * φ n t := by
      intro q hq hF
      have hnorm : ∀ n, ∫ t in Ioo x b, ‖q t * ψ t * φ n t‖ ≤
          (∫ t in Ioo x b, ‖q t * ψ t‖) * (B x * (R x ^ n / n.factorial)) := by
        intro n
        rw [← integral_mul_const]
        refine setIntegral_mono_on (hF n).norm ((hq x hx).norm.mul_const _) measurableSet_Ioo
          fun t ht => ?_
        rw [norm_mul]
        gcongr
        have hR0 := tail_nonneg hρ0 (hx.1.trans ht.1).le
        refine ((hφ n).2 t ⟨hx.1.trans ht.1, ht.2⟩).trans (mul_le_mul (hBa x t hx ht.1.le ht.2)
          (div_le_div_of_nonneg_right (pow_le_pow_left₀ hR0
            (tail_anti hρ0 hρi hx ht.1.le) n) (Nat.cast_nonneg _))
          (by positivity) (hB0 x hx))
      have hsI : Summable fun n => ∫ t in Ioo x b, ‖q t * ψ t * φ n t‖ :=
        Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hnorm
          (((hexp x).summable.mul_left (B x)).mul_left _)
      refine ⟨Summable.of_norm_bounded hsI fun n => norm_integral_le_integral_norm _, ?_⟩
      rw [integral_tsum_of_summable_integral_norm hF hsI]
      congr 1
      ext t
      rw [hS, tsum_mul_left]
    have h₁ := hswap hq₁ fun n => (hstep n).1 x hx
    have h₂ := hswap hq₂ fun n => (hstep n).2.1 x hx
    rw [← sub_eq_iff_eq_add', hSσ x hx, hL, volterraOp, h₁.2, h₂.2, ← tsum_mul_left,
      ← tsum_mul_left, ← (h₁.1.mul_left _).tsum_add (h₂.1.mul_left _)]
    congr 1
    ext n
    exact congrFun (Function.iterate_succ_apply' L n σ) x

/-- **Existence and bound for Volterra equations with a rank-two kernel** (Olver,
*Asymptotics and Special Functions*, Ch. 6, Thm. 10.1, specialized to kernels of the form
`K x t = p₁ x q₁ t + p₂ x q₂ t`). If `‖K x t ψ t‖ ≤ ρ t` for `a < x < t`, `‖J‖ ≤ 1` and `ρ` is
continuous and integrable up to `b`, the equation `h x = ∫_{(x,b)} K x t ψ t (J t + h t) dt`
has a solution with `‖h x‖ ≤ exp (∫_{(x,b)} ρ) - 1` on `(a, b)`. -/
theorem exists_volterra_solution
    (hp₁ : AEStronglyMeasurable p₁ (volume.restrict (Ioo a b)))
    (hp₂ : AEStronglyMeasurable p₂ (volume.restrict (Ioo a b)))
    (hq₁ : ∀ c, c ∈ Ioo a b → IntegrableOn (fun t => q₁ t * ψ t) (Ioo c b))
    (hq₂ : ∀ c, c ∈ Ioo a b → IntegrableOn (fun t => q₂ t * ψ t) (Ioo c b))
    {J : ℝ → 𝕜} (hJm : AEStronglyMeasurable J (volume.restrict (Ioo a b)))
    (hJ : ∀ t, t ∈ Ioo a b → ‖J t‖ ≤ 1)
    (hρc : ContinuousOn ρ (Ioo a b)) (hρi : ∀ c, c ∈ Ioo a b → IntegrableOn ρ (Ioo c b))
    (hK : ∀ x t, x ∈ Ioo a b → t ∈ Ioo x b → ‖(p₁ x * q₁ t + p₂ x * q₂ t) * ψ t‖ ≤ ρ t) :
    ∃ h : ℝ → 𝕜, AEStronglyMeasurable h (volume.restrict (Ioo a b)) ∧
      (∀ x, x ∈ Ioo a b → ‖h x‖ ≤ Real.exp (∫ s in Ioo x b, ρ s) - 1) ∧
      ∀ x, x ∈ Ioo a b → h x = volterraOp b p₁ p₂ q₁ q₂ ψ (fun t => J t + h t) x := by
  obtain ⟨S, hSm, hSb, hSeq⟩ := exists_volterra_solution_add hp₁ hp₂ hq₁ hq₂ hJm
    (B := fun _ => 1) hJ (fun _ _ _ _ _ => le_rfl) hρc hρi hK
  refine ⟨fun x => S x - J x, hSm.sub hJm, fun x hx => by simpa using hSb x hx, fun x hx => ?_⟩
  have hJh : (fun t => J t + (S t - J t)) = S := by ext t; ring
  simp only [hJh]
  rw [hSeq x hx]
  ring

end Volterra

end LiouvilleGreen.IntervalVolterra
