/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.BasicProperties.IntegerParametersAndLimits

/-!
# Fundamental pairs of confluent hypergeometric solutions

Analyticity and Wronskian calculations for Kummer and Tricomi fundamental systems.

Source references and common attribution are retained in
`DLMF.Confluent.BasicProperties`.
-/

@[expose] public section

open Complex Filter

open scoped Real Topology

open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-! ### Wronskians -/

/-- For `b` not a nonpositive integer, `M(a,b,·)` is entire. -/
theorem analyticOnNhd_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    AnalyticOnNhd ℂ (kummerM a b) Set.univ := fun z _ =>
  (hasFPowerSeriesOnBall_kummerM (a := a) hb).analyticAt_of_mem (by simp)

/-- The entire part of the Wronskian of Kummer's pair `M(a,b,z)`, `z^{1-b} M(a-b+1,2-b,z)`
equals `(1-b) e^z`. -/
theorem kummer_pair_wronskian_core {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k)
    (hB : ∀ k : ℕ, 2 - b ≠ -k) (z : ℂ) :
    (1 - b) * kummerM a b z * kummerM (a - b + 1) (2 - b) z +
      z * (kummerM a b z * deriv (kummerM (a - b + 1) (2 - b)) z -
        kummerM (a - b + 1) (2 - b) z * deriv (kummerM a b) z) = (1 - b) * exp z := by
  set u := kummerM a b with hu
  set v := kummerM (a - b + 1) (2 - b) with hv
  have hua := analyticOnNhd_kummerM (a := a) hb
  have hva := analyticOnNhd_kummerM (a := a - b + 1) hB
  have hud : Differentiable ℂ u := fun w => (hua w (Set.mem_univ _)).differentiableAt
  have hvd : Differentiable ℂ v := fun w => (hva w (Set.mem_univ _)).differentiableAt
  have hud' : Differentiable ℂ (deriv u) := fun w => (hua.deriv w (Set.mem_univ _)).differentiableAt
  have hvd' : Differentiable ℂ (deriv v) := fun w => (hva.deriv w (Set.mem_univ _)).differentiableAt
  set F : ℂ → ℂ := fun w => (1 - b) * u w * v w + w * (u w * deriv v w - v w * deriv u w) with hF
  have hFd : ∀ w, HasDerivAt F ((1 - b) * deriv u w * v w + (1 - b) * u w * deriv v w +
      (u w * deriv v w - v w * deriv u w) + w * (deriv u w * deriv v w + u w * deriv (deriv v) w -
        (deriv v w * deriv u w + v w * deriv (deriv u) w))) w := by
    intro w
    have h1 := ((hud w).hasDerivAt.const_mul (1 - b)).mul (hvd w).hasDerivAt
    have h2 := ((hud w).hasDerivAt.mul (hvd' w).hasDerivAt).sub
      ((hvd w).hasDerivAt.mul (hud' w).hasDerivAt)
    have h3 := (hasDerivAt_id w).mul h2
    refine ((h1.add h3).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
    · simp only [hF, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, id]
    · simp only [id, Pi.mul_apply, Pi.sub_apply]
      ring
  set E : ℂ → ℂ := fun w => (1 - b) * deriv u w * v w + (1 - b) * u w * deriv v w +
      (u w * deriv v w - v w * deriv u w) + w * (deriv u w * deriv v w + u w * deriv (deriv v) w -
        (deriv v w * deriv u w + v w * deriv (deriv u) w)) with hE
  have hud'' : Continuous (deriv (deriv u)) :=
    continuous_iff_continuousAt.mpr fun w =>
      (hua.deriv.deriv w (Set.mem_univ _)).continuousAt
  have hvd'' : Continuous (deriv (deriv v)) :=
    continuous_iff_continuousAt.mpr fun w =>
      (hva.deriv.deriv w (Set.mem_univ _)).continuousAt
  have hEc : Continuous E := by
    simp only [hE]
    have := hud.continuous; have := hvd.continuous; have := hud'.continuous
    have := hvd'.continuous
    fun_prop
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun w => (hFd w).continuousAt
  have hEF : E = F := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hEc hFc fun w hw => ?_
    have hw' : w ≠ 0 := hw
    have hU := kummerM_ode (a := a) hb hw'
    have hV := kummerM_ode (a := a - b + 1) hB hw'
    rw [iteratedDeriv_succ, iteratedDeriv_one] at hU hV
    rw [← hu] at hU
    rw [← hv] at hV
    simp only [hE, hF]
    linear_combination u w * hV - v w * hU
  have hFF : ∀ w, deriv F w = F w := by
    intro w
    rw [(hFd w).deriv]
    exact congrFun hEF w
  have hG : ∀ w, deriv (fun w => F w * exp (-w)) w = 0 := by
    intro w
    have he : HasDerivAt (fun w : ℂ => exp (-w)) (exp (-w) * -1) w := (hasDerivAt_id w).neg.cexp
    rw [HasDerivAt.deriv (f := fun w => F w * exp (-w)) ((hFd w).mul he), ← (hFd w).deriv, hFF]
    ring
  have hGd : Differentiable ℂ (fun w => F w * exp (-w)) := fun w =>
    ((hFd w).differentiableAt.mul (by fun_prop))
  have hc := is_const_of_deriv_eq_zero hGd hG z 0
  have hF0 : F 0 = 1 - b := by simp [hF, hu, hv, kummerM_zero]
  simp only [neg_zero, exp_zero, mul_one, hF0] at hc
  have hez : exp (-z) * exp z = 1 := by rw [← exp_add]; simp
  change F z = (1 - b) * exp z
  linear_combination exp z * hc - F z * hez

/-- The Wronskian of Kummer's pair `M(a,b,z)`, `z^{1-b} M(a-b+1,2-b,z)`, at regular
denominators. -/
theorem wronskian_kummer_pair_of_nonpole (a b : ℂ) {z : ℂ} (hbk : ∀ k : ℕ, b ≠ -k)
    (hBk : ∀ k : ℕ, 2 - b ≠ -k) (hz : z ∈ slitPlane) :
    wronskian (kummerM a b) (fun w => w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) z =
      (1 - b) * z ^ (-b) * exp z := by
  have hz0 := slitPlane_ne_zero hz
  have hv := ((analyticOnNhd_kummerM (a := a - b + 1) hBk) z (Set.mem_univ _)).differentiableAt
  have hp := (hasDerivAt_id z).cpow_const (c := 1 - b) hz
  have hy := hp.mul hv.hasDerivAt
  simp only [id, mul_one] at hy
  unfold wronskian
  rw [HasDerivAt.deriv (f := fun w => w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) hy]
  have hcore := kummer_pair_wronskian_core (a := a) hbk hBk z
  have e1 : z ^ (1 - b - 1) = z ^ (-b) := by ring_nf
  have e2 : z ^ (1 - b) = z * z ^ (-b) := by
    rw [show (1 : ℂ) - b = 1 + -b by ring, cpow_add _ _ hz0, cpow_one]
  beta_reduce
  rw [e1, e2]
  linear_combination z ^ (-b) * hcore

/-- The Wronskian of Kummer's pair `M(a,b,z)`, `z^{1-b} M(a-b+1,2-b,z)`. -/
theorem wronskian_kummer_pair (a b : ℂ) {z : ℂ} (hb : ∀ n : ℤ, b ≠ n) (hz : z ∈ slitPlane) :
    wronskian (kummerM a b) (fun w => w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) z =
      (1 - b) * z ^ (-b) * exp z :=
  wronskian_kummer_pair_of_nonpole a b (fun k h => hb (-k) (by push_cast; exact h))
    (fun k h => hb (2 + k) (by push_cast; linear_combination -h)) hz

/-- Joint continuity at `(b, x)` gives uniform convergence near `x` as the parameter tends
to `b`. -/
theorem tendstoUniformlyOnFilter_of_continuousAt {F : ℂ → ℂ → ℂ} {b x : ℂ}
    (h : ContinuousAt (fun p : ℂ × ℂ => F p.1 p.2) (b, x)) {l : Filter ℂ} (hl : l ≤ 𝓝 b) :
    TendstoUniformlyOnFilter F (F b) l (𝓝 x) := by
  rw [Metric.tendstoUniformlyOnFilter_iff]
  intro ε hε
  have h1 : ∀ᶠ p : ℂ × ℂ in 𝓝 (b, x), dist (F p.1 p.2) (F b x) < ε / 2 :=
    Metric.tendsto_nhds.mp h (ε / 2) (by positivity)
  have h2 : ∀ᶠ w in 𝓝 x, dist (F b w) (F b x) < ε / 2 := by
    have hc : ContinuousAt (fun w => F b w) x :=
      ContinuousAt.comp (f := fun w => (b, w)) h (by fun_prop)
    exact Metric.tendsto_nhds.mp hc (ε / 2) (by positivity)
  have h1' : ∀ᶠ p : ℂ × ℂ in l ×ˢ 𝓝 x, dist (F p.1 p.2) (F b x) < ε / 2 := by
    rw [nhds_prod_eq] at h1
    exact Filter.Eventually.filter_mono (Filter.prod_mono hl le_rfl) h1
  filter_upwards [h1', h2.prod_inr l] with p hp1 hp2
  calc dist (F b p.2) (F p.1 p.2) ≤ dist (F b p.2) (F b x) + dist (F p.1 p.2) (F b x) :=
        dist_triangle_right _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hp2 hp1
    _ = ε := by ring

/-- At noninteger `c`, `U(a,c,·)` is differentiable on the slit plane. -/
theorem differentiableOn_kummerU_of_mem (a : ℂ) {c : ℂ} (hc : c ∈ integerComplement) :
    DifferentiableOn ℂ (kummerU a c) slitPlane := by
  have hcz := forall_of_mem_integerComplement hc
  have hck := not_neg_nat_of_mem_integerComplement hc
  have h2c : ∀ k : ℕ, 2 - c ≠ -k := fun k h => hcz (2 + k) (by push_cast; linear_combination -h)
  have hfun : kummerU a c = fun w => kummerUConnection a c w :=
    funext fun w => kummerU_eq_connection a c w hcz
  rw [hfun]
  intro w hw
  have hu := ((analyticOnNhd_kummerM (a := a) hck) w (Set.mem_univ _)).differentiableAt
  have hv := ((analyticOnNhd_kummerM (a := a - c + 1) h2c) w (Set.mem_univ _)).differentiableAt
  have hp := ((hasDerivAt_id w).cpow_const (c := 1 - c) hw).differentiableAt
  unfold kummerUConnection
  exact ((hu.const_mul _).add (((hp.const_mul _).mul hv))).differentiableWithinAt

/-- `U(a,c,·) → U(a,b,·)` locally uniformly on the slit plane along noninteger `c → b`. -/
theorem tendstoLocallyUniformlyOn_kummerU (a b : ℂ) :
    TendstoLocallyUniformlyOn (fun c => kummerU a c) (kummerU a b)
      (𝓝[integerComplement] b) slitPlane := by
  rw [tendstoLocallyUniformlyOn_iff_filter]
  intro x hx
  have hc : ContinuousAt (fun p : ℂ × ℂ => kummerU a p.1 p.2) (b, x) := by
    have h := continuousAt_kummerU a b hx
    have hf : ContinuousAt (fun p : ℂ × ℂ => (a, p.1, p.2)) (b, x) := by fun_prop
    exact ContinuousAt.comp (g := fun q : ℂ × ℂ × ℂ => kummerU q.1 q.2.1 q.2.2)
      (f := fun p : ℂ × ℂ => (a, p.1, p.2)) h hf
  exact (tendstoUniformlyOnFilter_of_continuousAt (F := fun c w => kummerU a c w) hc
    nhdsWithin_le_nhds).mono_right nhdsWithin_le_nhds

/-- **`U(a,b,·)` is holomorphic on the slit plane** for every `b`, including integers. -/
theorem differentiableOn_kummerU (a b : ℂ) : DifferentiableOn ℂ (kummerU a b) slitPlane := by
  have := integerComplement_nhdsWithin_neBot b
  exact (tendstoLocallyUniformlyOn_kummerU a b).differentiableOn
    (eventually_nhdsWithin_of_forall fun c hc => differentiableOn_kummerU_of_mem a hc)
    isOpen_slitPlane

/-- The `z`-derivative of `U(a,c,z)` converges along noninteger `c → b`. -/
theorem tendsto_deriv_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun c => deriv (kummerU a c) z) (𝓝[integerComplement] b)
      (𝓝 (deriv (kummerU a b) z)) := by
  have hd : ∀ᶠ c in 𝓝[integerComplement] b, DifferentiableOn ℂ (kummerU a c) slitPlane :=
    eventually_nhdsWithin_of_forall fun c hc => differentiableOn_kummerU_of_mem a hc
  exact ((tendstoLocallyUniformlyOn_kummerU a b).deriv hd isOpen_slitPlane).tendsto_at hz

/-- A nonzero base has nonzero complex powers. -/
private lemma cpow_ne_zero_of_ne_zero' {z : ℂ} (hz : z ≠ 0) (s : ℂ) : z ^ s ≠ 0 := by
  rw [cpow_def_of_ne_zero hz]; exact exp_ne_zero _

/-- `Γ(b) Γ(2-b) = (1-b) π / sin(πb)`. -/
theorem Gamma_mul_Gamma_two_sub (b : ℂ) (hb1 : (1 : ℂ) - b ≠ 0) :
    Gamma b * Gamma (2 - b) = (1 - b) * (π / sin (π * b)) := by
  rw [show (2 : ℂ) - b = (1 - b) + 1 by ring, Gamma_add_one _ hb1, ← Gamma_mul_Gamma_one_sub b]
  ring

/-- The connection formula as an identity of functions, with its derivative. -/
theorem hasDerivAt_kummerU_connection (a : ℂ) {c z : ℂ} (hc : c ∈ integerComplement)
    (hz : z ∈ slitPlane) :
    HasDerivAt (kummerU a c)
      (Gamma (1 - c) / Gamma (a - c + 1) * deriv (kummerM a c) z +
        Gamma (c - 1) / Gamma a *
          deriv (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z) z := by
  have hcz := forall_of_mem_integerComplement hc
  have hck := not_neg_nat_of_mem_integerComplement hc
  have h2c : ∀ k : ℕ, 2 - c ≠ -k := fun k h => hcz (2 + k) (by push_cast; linear_combination -h)
  have hfun : kummerU a c = fun w => Gamma (1 - c) / Gamma (a - c + 1) * kummerM a c w +
      Gamma (c - 1) / Gamma a * (w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) := by
    funext w
    rw [kummerU_eq_connection a c w hcz]
    unfold kummerUConnection
    ring
  have hu := ((analyticOnNhd_kummerM (a := a) hck) z (Set.mem_univ _)).differentiableAt
  have hv := ((analyticOnNhd_kummerM (a := a - c + 1) h2c) z (Set.mem_univ _)).differentiableAt
  have hy : DifferentiableAt ℂ (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z :=
    ((hasDerivAt_id z).cpow_const (c := 1 - c) hz).differentiableAt.mul hv
  rw [hfun]
  exact (hu.hasDerivAt.const_mul _).add (hy.hasDerivAt.const_mul _)

/-- For noninteger `c`, the Wronskian of `M̃(a,c,z) = ₁F̃₁(a;c;z)` and `U(a,c,z)` is `-z^{-c} eᶻ /
Γ(a)` (DLMF 13.2.34). -/
theorem wronskian_regularized_kummerU_of_mem (a : ℂ) {c z : ℂ} (hc : c ∈ integerComplement)
    (hz : z ∈ slitPlane) :
    regularizedHGFun {a} {c} z * deriv (kummerU a c) z -
      kummerU a c z * deriv (regularizedHGFun {a} {c}) z = -(z ^ (-c) * exp z) / Gamma a := by
  have hcz := forall_of_mem_integerComplement hc
  have hck := not_neg_nat_of_mem_integerComplement hc
  have h1 : regularizedHGFun {a} {c} = fun w => (Gamma c)⁻¹ * kummerM a c w := by
    funext w; rw [regularizedConfluent_eq_div_Gamma hck, div_eq_inv_mul]
  have hu := ((analyticOnNhd_kummerM (a := a) hck) z (Set.mem_univ _)).differentiableAt
  have hW := wronskian_kummer_pair a c hcz hz
  unfold wronskian at hW
  rw [(hasDerivAt_kummerU_connection a hc hz).deriv, h1, deriv_const_mul _ hu,
    kummerU_eq_connection a c z hcz]
  unfold kummerUConnection
  have hc1 : c - 1 ≠ 0 := fun h => hcz 1 (by push_cast; linear_combination h)
  have hGc : Gamma c = (c - 1) * Gamma (c - 1) := by
    rw [← Gamma_add_one _ hc1]; ring_nf
  have hGc1 : Gamma (c - 1) ≠ 0 := Gamma_ne_zero fun k h => hcz (-k + 1) (by
    push_cast; linear_combination h)
  rw [hGc]
  calc ((c - 1) * Gamma (c - 1))⁻¹ * kummerM a c z *
        (Gamma (1 - c) / Gamma (a - c + 1) * deriv (kummerM a c) z +
          Gamma (c - 1) / Gamma a *
            deriv (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z) -
      (Gamma (1 - c) / Gamma (a - c + 1) * kummerM a c z +
          Gamma (c - 1) / Gamma a * z ^ (1 - c) * kummerM (a - c + 1) (2 - c) z) *
        (((c - 1) * Gamma (c - 1))⁻¹ * deriv (kummerM a c) z)
      = ((c - 1) * Gamma (c - 1))⁻¹ * (Gamma (c - 1) / Gamma a) *
          (kummerM a c z * deriv (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z -
            z ^ (1 - c) * kummerM (a - c + 1) (2 - c) z * deriv (kummerM a c) z) := by ring
    _ = _ := by
      rw [hW]
      field_simp
      ring

/-- For noninteger `c`, the Wronskian of `z^{1-c} M̃(a-c+1,2-c,z)` and `U(a,c,z)` is `-z^{-c} eᶻ /
Γ(a-c+1)` (DLMF 13.2.35). -/
theorem wronskian_shifted_kummerU_of_mem (a : ℂ) {c z : ℂ} (hc : c ∈ integerComplement)
    (hz : z ∈ slitPlane) :
    z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * deriv (kummerU a c) z -
      kummerU a c z * deriv (fun w => w ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} w) z =
      -(z ^ (-c) * exp z) / Gamma (a - c + 1) := by
  have hcz := forall_of_mem_integerComplement hc
  have hck := not_neg_nat_of_mem_integerComplement hc
  have h2c : ∀ k : ℕ, 2 - c ≠ -k := fun k h => hcz (2 + k) (by push_cast; linear_combination -h)
  have h2 : (fun w => w ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} w) =
      fun w => (Gamma (2 - c))⁻¹ * (w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) := by
    funext w; rw [regularizedConfluent_eq_div_Gamma h2c, div_eq_inv_mul]; ring
  have hv := ((analyticOnNhd_kummerM (a := a - c + 1) h2c) z (Set.mem_univ _)).differentiableAt
  have hy : DifferentiableAt ℂ (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z :=
    ((hasDerivAt_id z).cpow_const (c := 1 - c) hz).differentiableAt.mul hv
  have hW := wronskian_kummer_pair a c hcz hz
  unfold wronskian at hW
  rw [(hasDerivAt_kummerU_connection a hc hz).deriv, h2, deriv_const_mul _ hy,
    regularizedConfluent_eq_div_Gamma h2c, kummerU_eq_connection a c z hcz]
  unfold kummerUConnection
  have hc1 : (1 : ℂ) - c ≠ 0 := fun h => hcz 1 (by push_cast; linear_combination -h)
  have hG2 : Gamma (2 - c) = (1 - c) * Gamma (1 - c) := by
    rw [show (2 : ℂ) - c = (1 - c) + 1 by ring, Gamma_add_one _ hc1]
  have hG1 : Gamma (1 - c) ≠ 0 := Gamma_ne_zero fun k h => hcz (k + 1) (by
    push_cast; linear_combination -h)
  rw [hG2]
  calc z ^ (1 - c) * (kummerM (a - c + 1) (2 - c) z / ((1 - c) * Gamma (1 - c))) *
        (Gamma (1 - c) / Gamma (a - c + 1) * deriv (kummerM a c) z +
          Gamma (c - 1) / Gamma a *
            deriv (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z) -
      (Gamma (1 - c) / Gamma (a - c + 1) * kummerM a c z +
          Gamma (c - 1) / Gamma a * z ^ (1 - c) * kummerM (a - c + 1) (2 - c) z) *
        (((1 - c) * Gamma (1 - c))⁻¹ *
          deriv (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z)
      = -(((1 - c) * Gamma (1 - c))⁻¹ * (Gamma (1 - c) / Gamma (a - c + 1))) *
          (kummerM a c z * deriv (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z -
            z ^ (1 - c) * kummerM (a - c + 1) (2 - c) z * deriv (kummerM a c) z) := by ring
    _ = _ := by
      rw [hW]
      field_simp

/-- The regularized `₁F̃₁(A(c); B(c); z)` is continuous in a parameter `c` entering through
continuous `A` and `B`. -/
theorem tendsto_regularizedConfluent_param (A B : ℂ → ℂ) (hA : Continuous A) (hB : Continuous B)
    (b z : ℂ) (l : Filter ℂ) (hl : l ≤ 𝓝 b) :
    Tendsto (fun c => regularizedHGFun {A c} {B c} z) l (𝓝 (regularizedHGFun {A b} {B b} z)) := by
  have h := continuous_regularizedConfluent.comp
    (f := fun c => (A c, B c, z)) (by fun_prop)
  exact (h.continuousAt.tendsto).mono_left hl

/-- Identity under the stated parameter and domain assumptions: `wronskian (kummerM a b) (fun w =>
w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) z ≠ 0`. -/
@[dlmf 13.2.E26]
theorem wronskian_kummerM_pair {a b z : ℂ} (hb : ∀ n : ℤ, b ≠ n)
    (hz : z ∈ slitPlane) :
    wronskian (kummerM a b)
      (fun w => w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) z ≠ 0 := by
  rw [wronskian_kummer_pair a b hb hz]
  have hb1 : (1 : ℂ) - b ≠ 0 := fun h => hb 1 (by push_cast; linear_combination -h)
  exact mul_ne_zero (mul_ne_zero hb1 (cpow_ne_zero_of_ne_zero' (slitPlane_ne_zero hz) _))
    (exp_ne_zero _)

/-- Identity under the stated parameter and domain assumptions: `wronskian (regularizedHGFun {a}
{b}) (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w) z = sin (π * b) * z ^
(-b) * exp z / π`. -/
@[dlmf 13.2.E33]
theorem wronskian_regularizedHGFun (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hb : ∀ n : ℤ, b ≠ n) :
    wronskian (regularizedHGFun {a} {b})
      (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w) z =
      sin (π * b) * z ^ (-b) * exp z / π := by
  have hbk : ∀ k : ℕ, b ≠ -k := fun k h => hb (-k) (by push_cast; exact h)
  have hBk : ∀ k : ℕ, 2 - b ≠ -k := fun k h => hb (2 + k) (by push_cast; linear_combination -h)
  have hb1 : (1 : ℂ) - b ≠ 0 := fun h => hb 1 (by push_cast; linear_combination -h)
  have hbc : b ∈ integerComplement := mem_integerComplement_of_forall hb
  have hsin := sin_pi_mul_ne_zero_of_mem hbc
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz0 := slitPlane_ne_zero hz
  have h1 : regularizedHGFun {a} {b} = fun w => (Gamma b)⁻¹ * kummerM a b w := by
    funext w; rw [regularizedConfluent_eq_div_Gamma hbk, div_eq_inv_mul]
  have h2 : (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w) =
      fun w => (Gamma (2 - b))⁻¹ * (w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) := by
    funext w; rw [regularizedConfluent_eq_div_Gamma hBk, div_eq_inv_mul]; ring
  have hW := wronskian_kummer_pair a b hb hz
  have hu := ((analyticOnNhd_kummerM (a := a) hbk) z (Set.mem_univ _)).differentiableAt
  have hv := ((analyticOnNhd_kummerM (a := a - b + 1) hBk) z (Set.mem_univ _)).differentiableAt
  have hy : DifferentiableAt ℂ (fun w => w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) z :=
    ((hasDerivAt_id z).cpow_const (c := 1 - b) hz).differentiableAt.mul hv
  unfold wronskian at hW ⊢
  rw [h1, h2, deriv_const_mul _ hu, deriv_const_mul _ hy]
  have hG := Gamma_mul_Gamma_two_sub b hb1
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero hbk
  have hGB : Gamma (2 - b) ≠ 0 := Gamma_ne_zero hBk
  calc (Gamma b)⁻¹ * kummerM a b z * ((Gamma (2 - b))⁻¹ *
        deriv (fun w => w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) z) -
      (Gamma (2 - b))⁻¹ * (z ^ (1 - b) * kummerM (a - b + 1) (2 - b) z) *
        ((Gamma b)⁻¹ * deriv (kummerM a b) z)
      = (Gamma b * Gamma (2 - b))⁻¹ * (kummerM a b z *
          deriv (fun w => w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) z -
        (z ^ (1 - b) * kummerM (a - b + 1) (2 - b) z) * deriv (kummerM a b) z) := by
          rw [mul_inv]; ring
    _ = _ := by
      rw [hW, hG]
      field_simp

/-- 13.2.34 without the hypothesis on `a`. -/
theorem wronskian_regularizedHGFun_kummerU_all (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    wronskian (regularizedHGFun {a} {b}) (kummerU a b) z =
      -(z ^ (-b) * exp z) / Gamma a := by
  have hz0 := slitPlane_ne_zero hz
  have := integerComplement_nhdsWithin_neBot b
  unfold wronskian
  have key : ∀ c, regularizedHGFun {a} {c} z * deriv (kummerU a c) z -
      kummerU a c z * deriv (regularizedHGFun {a} {c}) z =
      regularizedHGFun {a} {c} z * deriv (kummerU a c) z -
        kummerU a c z * (a * regularizedHGFun {a + 1} {c + 1} z) := fun c => by
    rw [deriv_regularizedConfluent]
  rw [key]
  have hL : Tendsto (fun c => regularizedHGFun {a} {c} z * deriv (kummerU a c) z -
      kummerU a c z * (a * regularizedHGFun {a + 1} {c + 1} z)) (𝓝[integerComplement] b)
      (𝓝 (regularizedHGFun {a} {b} z * deriv (kummerU a b) z -
        kummerU a b z * (a * regularizedHGFun {a + 1} {b + 1} z))) := by
    have h1 := tendsto_regularizedConfluent_param (fun _ => a) id continuous_const continuous_id
      b z (𝓝[integerComplement] b) nhdsWithin_le_nhds
    have h2 := tendsto_regularizedConfluent_param (fun _ => a + 1) (fun c => c + 1)
      continuous_const (by fun_prop) b z (𝓝[integerComplement] b) nhdsWithin_le_nhds
    exact (h1.mul (tendsto_deriv_kummerU a b hz)).sub
      ((tendsto_kummerU a b hz0).mul (h2.const_mul a))
  have hR : Tendsto (fun c : ℂ => -(z ^ (-c) * exp z) / Gamma a) (𝓝[integerComplement] b)
      (𝓝 (-(z ^ (-b) * exp z) / Gamma a)) := by
    have hc : ContinuousAt (fun c : ℂ => z ^ (-c)) b :=
      continuousAt_id.neg.const_cpow (Or.inl hz0)
    exact ((((hc.mul continuousAt_const).neg).div_const _).tendsto).mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [← key]
  exact (wronskian_regularized_kummerU_of_mem a hc hz).symm

/-- Identity under the stated parameter and domain assumptions: `wronskian (regularizedHGFun {a}
{b}) (kummerU a b) z = -(z ^ (-b) * exp z) / Gamma a`. -/
@[dlmf 13.2.E34]
theorem wronskian_regularizedHGFun_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (ha : ∀ k : ℕ, a ≠ -k) :
    wronskian (regularizedHGFun {a} {b}) (kummerU a b) z =
      -(z ^ (-b) * exp z) / Gamma a := by
  exact wronskian_regularizedHGFun_kummerU_all a b hz

/-- `(-z)^w = z^w e^{επiw}` when `-z = z e^{επi}` with `arg z + επ ∈ (-π, π]`. -/
theorem neg_cpow_of_arg {z : ℂ} (hz : z ≠ 0) (ε : ℂ) (hε : ε = 1 ∨ ε = -1)
    (h1 : -π < arg z + ε.re * π) (h2 : arg z + ε.re * π ≤ π) (w : ℂ) :
    (-z) ^ w = z ^ w * exp (ε * π * I * w) := by
  have hn : -z = exp (log z + ε * π * I) := by
    rw [exp_add, exp_log hz]
    rcases hε with rfl | rfl
    · rw [one_mul, exp_pi_mul_I]; ring
    · rw [show (-1 : ℂ) * π * I = -(π * I) by ring, exp_neg, exp_pi_mul_I]; ring
  have hre : ε = (ε.re : ℂ) := by rcases hε with rfl | rfl <;> simp
  have hlog : log (-z) = log z + ε * π * I := by
    rw [hn, log_exp]
    · rw [hre]; simp [log_im]; linarith
    · rw [hre]; simp [log_im]; linarith
  rw [cpow_def_of_ne_zero (neg_ne_zero.mpr hz), hlog, cpow_def_of_ne_zero hz, add_mul, exp_add]

/-- The reciprocal reflection formula, valid for all `s` with the totalized `Γ`. -/
theorem recip_Gamma_mul_Gamma_one_sub (s : ℂ) : (Gamma s * Gamma (1 - s))⁻¹ = sin (π * s) / π := by
  rw [Gamma_mul_Gamma_one_sub, inv_div]

/-- The reflection formula in the form `1/Γ(1-z) = Γ(z) sin(πz)/π`, valid whenever
`Γ(z) ≠ 0` (at poles of `Γ(1-z)` both sides vanish). -/
theorem recip_Gamma_one_sub_eq {z : ℂ} (hz : Complex.Gamma z ≠ 0) :
    (Complex.Gamma (1 - z))⁻¹ = Complex.Gamma z * Complex.sin (π * z) / π := by
  rw [mul_div_assoc, ← recip_Gamma_mul_Gamma_one_sub, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ hz, one_mul]

/-- The trigonometric identity behind the `M(a,b,z)` coefficient in DLMF 13.2.41. -/
theorem exp_sin_connection (a b ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    exp (-ε * a * π * I) * sin (π * (b - a)) + exp (ε * (b - a) * π * I) * sin (π * a) =
      sin (π * b) := by
  have hu := exp_ne_zero (a * π * I)
  have hv := exp_ne_zero (b * π * I)
  have e1 : ∀ x : ℂ, sin (π * x) = (exp (-(x * π * I)) - exp (x * π * I)) * I / 2 := fun x => by
    rw [Complex.sin]; ring_nf
  rw [e1, e1, e1]
  rcases hε with rfl | rfl
  · rw [show -1 * a * π * I = -(a * π * I) by ring,
      show (1 : ℂ) * (b - a) * π * I = b * π * I - a * π * I by ring,
      show -((b - a) * π * I) = a * π * I - b * π * I by ring,
      show (b - a) * π * I = b * π * I - a * π * I by ring]
    simp only [exp_neg, exp_sub]
    field_simp
    ring
  · rw [show -(-1) * a * π * I = a * π * I by ring,
      show (-1 : ℂ) * (b - a) * π * I = a * π * I - b * π * I by ring,
      show -((b - a) * π * I) = a * π * I - b * π * I by ring,
      show (b - a) * π * I = b * π * I - a * π * I by ring]
    simp only [exp_neg, exp_sub]
    field_simp
    ring

/-- The cancellation of the `z^{1-b}` terms in DLMF 13.2.41. -/
theorem exp_connection_cancel (a b ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    exp (-ε * a * π * I) + exp (ε * (b - a) * π * I) * exp (ε * π * I * (1 - b)) = 0 := by
  rw [← exp_add, show ε * (b - a) * π * I + ε * π * I * (1 - b) = -ε * a * π * I + ε * π * I by
    ring, exp_add]
  rcases hε with rfl | rfl
  · rw [one_mul, exp_pi_mul_I]; ring
  · rw [show (-1 : ℂ) * π * I = -(π * I) by ring, exp_neg, exp_pi_mul_I]; ring

/-- DLMF 13.2.41 for noninteger `b`, with `-z = z e^{επi}` and `ε = ±1`. -/
theorem kummerM_div_Gamma_connection_of_not_int (a b : ℂ) {z : ℂ} (hb : ∀ k : ℤ, b ≠ k)
    (ε : ℂ) (hε : ε = 1 ∨ ε = -1)
    (hc : (-z) ^ (1 - b) = z ^ (1 - b) * exp (ε * π * I * (1 - b))) :
    kummerM a b z / Gamma b =
      exp (-ε * a * π * I) / Gamma (b - a) * kummerU a b z +
        exp (ε * (b - a) * π * I) / Gamma a * exp z * kummerU (b - a) b (-z) := by
  have hbn : ∀ k : ℕ, b ≠ -k := fun k h => hb (-k) (by simp [h])
  have h2b : ∀ k : ℕ, 2 - b ≠ -k := fun k h => hb (k + 2) (by push_cast; linear_combination -h)
  rw [kummerU_eq_connection _ _ _ hb, kummerU_eq_connection _ _ _ hb, kummerUConnection,
    kummerUConnection, hc, show b - a - b + 1 = 1 - a by ring]
  have hk1 := kummerM_kummer_transform (a := a) (z := z) hbn
  have hk2 := kummerM_kummer_transform (a := a - b + 1) (z := z) h2b
  rw [show 2 - b - (a - b + 1) = 1 - a by ring] at hk2
  rw [hk1, hk2]
  have hG1 := recip_Gamma_mul_Gamma_one_sub (b - a)
  have hG2 := recip_Gamma_mul_Gamma_one_sub a
  have hG3 := recip_Gamma_mul_Gamma_one_sub b
  rw [show 1 - (b - a) = a - b + 1 by ring] at hG1
  have hg : Gamma (1 - b) ≠ 0 :=
    Gamma_ne_zero fun k h => hb (k + 1) (by push_cast; linear_combination -h)
  have hgb : (Gamma b)⁻¹ = Gamma (1 - b) * (sin (π * b) / π) := by
    rw [← hG3, mul_inv, mul_comm, mul_assoc, inv_mul_cancel₀ hg, mul_one]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [div_eq_mul_inv]
  rw [hgb]
  rw [mul_inv] at hG1 hG2
  have hS1 := exp_sin_connection a b ε hε
  have hS2 := exp_connection_cancel a b ε hε
  set E := exp z
  set Mb := kummerM (b - a) b (-z)
  set Mc := kummerM (1 - a) (2 - b) (-z)
  set Z := z ^ (1 - b)
  linear_combination (-(E * Mb * Gamma (1 - b) * exp (-ε * a * π * I))) * hG1 -
    E * Mb * Gamma (1 - b) * exp (ε * (b - a) * π * I) * hG2 -
    E * Mb * Gamma (1 - b) / π * hS1 -
    E * Mc * Z * Gamma (b - 1) * (Gamma a)⁻¹ * (Gamma (b - a))⁻¹ * hS2

/-- 13.2.36 without the hypothesis on `a - b + 1`. -/
theorem wronskian_shifted_regularized_kummerU_all (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    wronskian (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w)
      (kummerU a b) z =
      -(z ^ (-b) * exp z) / Gamma (a - b + 1) := by
  have hz0 := slitPlane_ne_zero hz
  have := integerComplement_nhdsWithin_neBot b
  unfold wronskian
  have hD : ∀ c, HasDerivAt (fun w => w ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} w)
      ((1 - c) * z ^ (-c) * regularizedHGFun {a - c + 1} {2 - c} z +
        z ^ (1 - c) * ((a - c + 1) * regularizedHGFun {a - c + 1 + 1} {2 - c + 1} z)) z := by
    intro c
    have hp := (hasDerivAt_id z).cpow_const (c := 1 - c) hz
    have hm := (differentiableAt_regularizedConfluent (a - c + 1) (2 - c) z).hasDerivAt
    rw [deriv_regularizedConfluent] at hm
    have h := hp.mul hm
    simp only [id, mul_one] at h
    convert h using 2
    ring_nf
  have key : ∀ c, z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * deriv (kummerU a c) z -
      kummerU a c z * deriv (fun w => w ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} w) z =
      z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * deriv (kummerU a c) z -
      kummerU a c z * ((1 - c) * z ^ (-c) * regularizedHGFun {a - c + 1} {2 - c} z +
        z ^ (1 - c) * ((a - c + 1) * regularizedHGFun {a - c + 1 + 1} {2 - c + 1} z)) :=
    fun c => by rw [(hD c).deriv]
  rw [key]
  have hpow : ∀ s : ℂ → ℂ, Continuous s → Tendsto (fun c => z ^ s c) (𝓝[integerComplement] b)
      (𝓝 (z ^ s b)) := fun s hs =>
    ((hs.continuousAt.const_cpow (Or.inl hz0)).tendsto).mono_left nhdsWithin_le_nhds
  have h1 := tendsto_regularizedConfluent_param (fun c => a - c + 1) (fun c => 2 - c)
    (by fun_prop) (by fun_prop) b z (𝓝[integerComplement] b) nhdsWithin_le_nhds
  have h2 := tendsto_regularizedConfluent_param (fun c => a - c + 1 + 1) (fun c => 2 - c + 1)
    (by fun_prop) (by fun_prop) b z (𝓝[integerComplement] b) nhdsWithin_le_nhds
  have hid : Tendsto (fun c : ℂ => c) (𝓝[integerComplement] b) (𝓝 b) := nhdsWithin_le_nhds
  have c1 : Tendsto (fun _ : ℂ => (1 : ℂ)) (𝓝[integerComplement] b) (𝓝 1) := tendsto_const_nhds
  have ca : Tendsto (fun _ : ℂ => a) (𝓝[integerComplement] b) (𝓝 a) := tendsto_const_nhds
  have hL := (((hpow (fun c => 1 - c) (by fun_prop)).mul h1).mul
    (tendsto_deriv_kummerU a b hz)).sub ((tendsto_kummerU a b hz0).mul
      ((((c1.sub hid).mul (hpow (fun c => -c) (by fun_prop))).mul h1).add
        ((hpow (fun c => 1 - c) (by fun_prop)).mul
          (((ca.sub hid).add c1).mul h2))))
  have hR : Tendsto (fun c : ℂ => -(z ^ (-c) * exp z) / Gamma (a - c + 1))
      (𝓝[integerComplement] b) (𝓝 (-(z ^ (-b) * exp z) / Gamma (a - b + 1))) := by
    have hc : ContinuousAt (fun c : ℂ => z ^ (-c)) b :=
      continuousAt_id.neg.const_cpow (Or.inl hz0)
    have hG : ContinuousAt (fun c : ℂ => (Gamma (a - c + 1))⁻¹) b :=
      (differentiable_one_div_Gamma.continuous.comp
        (by fun_prop : Continuous fun c : ℂ => a - c + 1)).continuousAt.congr
        (Eventually.of_forall fun c => by simp)
    have hcc : ContinuousAt (fun c : ℂ => -(z ^ (-c) * exp z)) b :=
      (hc.mul continuousAt_const).neg
    have := (hcc.mul hG).tendsto.mono_left (nhdsWithin_le_nhds (s := integerComplement))
    convert this using 2 <;> simp [div_eq_mul_inv]
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [← key]
  exact (wronskian_shifted_kummerU_of_mem a hc hz).symm

/-- Identity under the stated parameter and domain assumptions: `wronskian (fun w => w ^ (1 - b) *
regularizedHGFun {a - b + 1} {2 - b} w) (kummerU a b) z = -(z ^ (-b) * exp z) / Gamma (a - b +
1)`. -/
@[dlmf 13.2.E36]
theorem wronskian_shifted_regularized_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hab : ∀ k : ℕ, a - b + 1 ≠ -k) :
    wronskian (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w)
      (kummerU a b) z =
      -(z ^ (-b) * exp z) / Gamma (a - b + 1) := by
  exact wronskian_shifted_regularized_kummerU_all a b hz

/-- **DLMF 13.2.41 in regularized form**, valid for every `b`:
`𝐌(a,b,z) = e^{∓πia}/Γ(b-a) U(a,b,z) + e^{±πi(b-a)}/Γ(a) e^z U(b-a,b,z e^{±πi})`. -/
theorem regularizedHGFun_eq_kummerU_connection (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (sign : Bool) (hsign : if sign then z.arg ≤ 0 else 0 < z.arg) :
    regularizedHGFun {a} {b} z =
      exp (-(if sign then 1 else -1) * a * π * I) / Gamma (b - a) * kummerU a b z +
        exp ((if sign then 1 else -1) * (b - a) * π * I) / Gamma a *
          exp z * kummerU (b - a) b (exp ((if sign then 1 else -1) * π * I) * z) := by
  have hz0 := slitPlane_ne_zero hz
  set ε : ℂ := if sign then 1 else -1 with hεdef
  have hε : ε = 1 ∨ ε = -1 := by cases sign <;> simp [hεdef]
  have hw : exp (ε * π * I) * z = -z := by
    rcases hε with h | h <;> rw [h]
    · rw [one_mul, exp_pi_mul_I]; ring
    · rw [show (-1 : ℂ) * π * I = -(π * I) by ring, exp_neg, exp_pi_mul_I]; ring
  have hc : ∀ w : ℂ, (-z) ^ w = z ^ w * exp (ε * π * I * w) := by
    have harg := arg_le_pi z
    have harg' := neg_pi_lt_arg z
    refine neg_cpow_of_arg hz0 ε hε ?_ ?_ <;> cases sign <;> simp_all <;> linarith
  rw [hw]
  have hiG : Continuous fun s : ℂ => (Gamma s)⁻¹ := by
    simpa [one_div] using differentiable_one_div_Gamma.continuous
  have hnz : -z ≠ 0 := neg_ne_zero.mpr hz0
  refine eq_of_continuousAt_of_integerComplement
    (f := fun c => regularizedHGFun {a} {c} z)
    (g := fun c => exp (-ε * a * π * I) / Gamma (c - a) * kummerU a c z +
      exp (ε * (c - a) * π * I) / Gamma a * exp z * kummerU (c - a) c (-z)) ?_ ?_ ?_
  · exact (continuous_regularizedConfluent.comp (by fun_prop :
      Continuous fun c : ℂ => (a, c, z))).continuousAt
  · simp only [div_eq_mul_inv]
    refine ContinuousAt.add (ContinuousAt.mul (continuousAt_const.mul
      (hiG.comp (by fun_prop : Continuous fun c : ℂ => c - a)).continuousAt)
      (continuousAt_kummerU_comp continuousAt_const continuousAt_id hz0)) ?_
    refine ContinuousAt.mul ((ContinuousAt.mul (by fun_prop) continuousAt_const).mul
      continuousAt_const) (continuousAt_kummerU_comp (by fun_prop) continuousAt_id hnz)
  · intro c hc'
    have hcz := forall_of_mem_integerComplement hc'
    have hcn : ∀ k : ℕ, c ≠ -k := fun k h => hcz (-k) (by simp [h])
    rw [regularizedConfluent_eq_div_Gamma hcn]
    exact kummerM_div_Gamma_connection_of_not_int a c hcz ε hε (hc _)

/-- DLMF's `U(b-a,b,z e^{±πi})` is represented by the principal value at `-z`, which is the
`e^{+πi}` continuation for `ph z ≤ 0` and the `e^{-πi}` continuation for `ph z > 0`. -/
@[dlmf 13.2.E41]
theorem kummerM_eq_kummerU_connection (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (sign : Bool) (hsign : if sign then z.arg ≤ 0 else 0 < z.arg) (hb : ∀ k : ℕ, b ≠ -k) :
    kummerM a b z / Gamma b =
      exp (-(if sign then 1 else -1) * a * π * I) / Gamma (b - a) * kummerU a b z +
        exp ((if sign then 1 else -1) * (b - a) * π * I) / Gamma a *
          exp z * kummerU (b - a) b (exp ((if sign then 1 else -1) * π * I) * z) := by
  rw [← regularizedConfluent_eq_div_Gamma hb]
  exact regularizedHGFun_eq_kummerU_connection a b hz sign hsign

/-- Exponential form of a sine jump. -/
theorem exp_sub_exp_neg_mul_I (t : ℂ) :
    exp (t * I) - exp (-t * I) = 2 * I * sin t := by
  rw [sin]
  linear_combination (exp (t * I) - exp (-t * I)) * I_sq

/-- Reciprocal form of Gamma reflection, valid also at integer arguments. -/
theorem sin_pi_mul_eq_recip_Gamma (t : ℂ) :
    sin (π * t) = π / (Gamma t * Gamma (1 - t)) := by
  rw [Gamma_mul_Gamma_one_sub, div_div_eq_mul_div]
  field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- The phase algebra shared by the jump identities. -/
theorem exp_weighted_jump (a b u v : ℂ) :
    exp (a * I) * (u - exp (-b * I) * v) -
      exp (-a * I) * (u - exp (b * I) * v) =
        2 * I * sin a * u - 2 * I * sin (a - b) * v := by
  have hp : exp ((a - b) * I) = exp (a * I) * exp (-b * I) := by
    rw [← exp_add]; congr 1; ring
  have hm : exp (-(a - b) * I) = exp (-a * I) * exp (b * I) := by
    rw [← exp_add]; congr 1; ring
  calc _ = (exp (a * I) - exp (-a * I)) * u -
      (exp ((a - b) * I) - exp (-(a - b) * I)) * v := by rw [hp, hm]; ring
    _ = _ := by simp only [exp_sub_exp_neg_mul_I]

/-- The half-turn of U, with its branch recorded in the logarithmic argument. -/
theorem kummerUOnLog_half_turn (a b : ℂ) {z : ℂ} (hz : z ≠ 0) (sign : Bool) :
    kummerUOnLog a b (log z + (if sign then 1 else -1) * π * I) =
      Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b (-z) -
        Gamma (b - 1) / Gamma a * z ^ (1 - b) *
          exp (-(if sign then 1 else -1) * b * π * I) *
            kummerM (a - b + 1) (2 - b) (-z) := by
  set s : ℂ := if sign then 1 else -1 with hs
  have he : exp (s * π * I) = -1 := by
    cases sign <;> simp [hs, exp_neg, exp_pi_mul_I]
  have hz' : exp (log z + s * π * I) = -z := by
    rw [exp_add, exp_log hz, he]; ring
  have hp : exp ((1 - b) * (log z + s * π * I)) =
      -z ^ (1 - b) * exp (-s * b * π * I) := by
    rw [show (1 - b) * (log z + s * π * I) =
      log z * (1 - b) + (s * π * I + (-s * b * π * I)) by ring,
      exp_add, exp_add, he, cpow_def_of_ne_zero hz]
    ring
  rw [kummerUOnLog, hz', hp]
  ring

/-- The jump of `U` across the negative axis, with both continuations `z e^{±πi}` taken on
the logarithmic argument plane. `kummerUOnLog` represents `U` there for noninteger `b`. -/
@[dlmf 13.2.E43]
theorem kummerM_eq_kummerU_jump (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hbi : ∀ k : ℤ, b ≠ k) (hab : ∀ k : ℕ, a - b + 1 ≠ -k) :
    2 * π * I * exp (-z) / (Gamma b * Gamma (a - b + 1)) * kummerM (b - a) b z =
      exp (b * π * I) * kummerUOnLog a b (log z + π * I) -
        exp (-b * π * I) * kummerUOnLog a b (log z - π * I) := by
  have hz0 := slitPlane_ne_zero hz
  have hb : ∀ k : ℕ, b ≠ -(k : ℂ) := not_neg_nat_of_mem_integerComplement
    (mem_integerComplement_of_forall hbi)
  have hGb := Gamma_ne_zero hb
  have hsin := sin_pi_mul_ne_zero_of_mem (mem_integerComplement_of_forall hbi)
  have hG : Gamma (1 - b) * sin (π * b) = π / Gamma b := by
    have h := Gamma_mul_Gamma_one_sub b
    apply (eq_div_iff hGb).mpr
    linear_combination (eq_div_iff hsin).mp h
  have hp := kummerUOnLog_half_turn a b hz0 true
  have hm := kummerUOnLog_half_turn a b hz0 false
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, neg_neg, neg_mul,
    ← sub_eq_add_neg] at hp hm
  rw [hp, hm]
  have ht := exp_sub_exp_neg_mul_I (π * b)
  rw [show (π : ℂ) * b * I = b * π * I by ring,
    show -(π * b) * I = -b * π * I by ring] at ht
  have hM : kummerM a b (-z) = exp (-z) * kummerM (b - a) b z := by
    rw [kummerM_kummer_transform hb, neg_neg]
  calc _ = 2 * I * (Gamma (1 - b) * sin (π * b)) / Gamma (a - b + 1) *
      kummerM a b (-z) := by rw [hG, hM]; ring
    _ = _ := by
      simp only [neg_mul] at ht ⊢
      linear_combination -(Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b (-z)) * ht

/-- The U jump identity without nonpole assumptions on the first parameter. -/
theorem kummerU_jump_all (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) (hbi : ∀ k : ℤ, b ≠ k) :
    2 * π * I * exp (-z) / (Gamma a * Gamma (a - b + 1)) * kummerU (b - a) b z =
      exp (a * π * I) * kummerUOnLog a b (log z + π * I) -
        exp (-a * π * I) * kummerUOnLog a b (log z - π * I) := by
  have hz0 := slitPlane_ne_zero hz
  have hb : ∀ k : ℕ, b ≠ -(k : ℂ) := not_neg_nat_of_mem_integerComplement
    (mem_integerComplement_of_forall hbi)
  have hB : ∀ k : ℕ, 2 - b ≠ -(k : ℂ) := fun k hk =>
    hbi (2 + k) (by push_cast; linear_combination -hk)
  have hp := kummerUOnLog_half_turn a b hz0 true
  have hm := kummerUOnLog_half_turn a b hz0 false
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, neg_neg, neg_mul,
    ← sub_eq_add_neg] at hp hm
  have hphase := exp_weighted_jump (a * π) (b * π)
    (Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b (-z))
    (Gamma (b - 1) / Gamma a * z ^ (1 - b) * kummerM (a - b + 1) (2 - b) (-z))
  simp only [neg_mul] at hphase
  have hs1 : sin (a * π) = π / (Gamma a * Gamma (1 - a)) := by
    rw [mul_comm a, sin_pi_mul_eq_recip_Gamma]
  have hs2 : sin (a * π - b * π) =
      -π / (Gamma (a - b + 1) * Gamma (b - a)) := by
    have h := sin_pi_mul_eq_recip_Gamma (a - b + 1)
    rw [show (π : ℂ) * (a - b + 1) = (a * π - b * π) + π by ring,
      sin_add_pi, show 1 - (a - b + 1) = b - a by ring] at h
    rw [neg_div]
    linear_combination -h
  have hM : kummerM a b (-z) = exp (-z) * kummerM (b - a) b z := by
    rw [kummerM_kummer_transform hb, neg_neg]
  have hN : kummerM (a - b + 1) (2 - b) (-z) =
      exp (-z) * kummerM (1 - a) (2 - b) z := by
    rw [kummerM_kummer_transform hB, neg_neg]
    congr 2; ring
  rw [hp, hm, kummerU_eq_connection (b - a) b z hbi]
  unfold kummerUConnection
  rw [show b - a - b + 1 = 1 - a by ring]
  symm
  calc
    _ = 2 * I * sin (a * π) *
        (Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b (-z)) -
      2 * I * sin (a * π - b * π) *
        (Gamma (b - 1) / Gamma a * z ^ (1 - b) * kummerM (a - b + 1) (2 - b) (-z)) := by
      simp only [neg_mul] at *
      linear_combination hphase
    _ = _ := by rw [hs1, hs2, hM, hN]; ring

/-- The jump of `U` across the negative axis, with both continuations `z e^{±πi}` taken on
the logarithmic argument plane. `kummerUOnLog` represents `U` there for noninteger `b`. -/
@[dlmf 13.2.E44]
theorem kummerU_jump (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) (hbi : ∀ k : ℤ, b ≠ k)
    (ha : ∀ k : ℕ, a ≠ -k) (hab : ∀ k : ℕ, a - b + 1 ≠ -k) :
    2 * π * I * exp (-z) / (Gamma a * Gamma (a - b + 1)) * kummerU (b - a) b z =
      exp (a * π * I) * kummerUOnLog a b (log z + π * I) -
        exp (-a * π * I) * kummerUOnLog a b (log z - π * I) := by
  exact kummerU_jump_all a b hz hbi

end DLMF.Confluent

end
end
