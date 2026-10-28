/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic
public import DLMF.JacobiElliptic.Basic
public import DLMF.Theta.ZeroValues
public import DLMF.Weierstrass.Addition

/-!
# Weierstrass functions in terms of theta functions

Theta representations of the Weierstrass sigma, zeta and elliptic functions, with the lattice
generators and quasi-period constants retained.

Source references and common attribution are retained in
`DLMF.Weierstrass.Relations`.
-/

@[expose] public section

open Complex PeriodPair DLMF.Elliptic DLMF.Theta DLMF.JacobiElliptic MeasureTheory

open scoped Real

open Filter Topology

noncomputable section

namespace DLMF.Weierstrass

namespace HalfPeriods

variable (H : HalfPeriods)

/-- `θ₁'''(0|τ)`. -/
def thetaOneTripleDerivNull (τ : ℂ) : ℂ := iteratedDeriv 3 (fun z ↦ jacobiThetaOneTau z τ) 0

/-! ### Helpers (p23R1): `σ` in terms of `θ₁`, Legendre's relation, `℘` in theta form -/
/-- A function periodic in `2ω₁` and `2ω₃` is periodic for the whole lattice. -/
lemma p23R1_lattice_periodic {F : Type*} {g : ℂ → F} (h1 : ∀ z, g (z + 2 * H.ω₁) = g z)
    (h3 : ∀ z, g (z + 2 * H.ω₃) = g z) : ∀ z w, w ∈ H.lattice → g (z + w) = g z := by
  intro z w hw
  obtain ⟨m, n, rfl⟩ := H.mem_lattice_iff.mp hw
  have p1 : Function.Periodic g (2 * H.ω₁) := h1
  have p3 : Function.Periodic g (2 * H.ω₃) := h3
  have := ((p1.int_mul m).add_period (p3.int_mul n)) z
  rw [← this]; congr 1; ring

/-- An entire nonvanishing `Q` with `Q(z + 2ω₁) = Q(z)` and
`Q(z + 2ω₃) = e^{2c(z + ω₃)} Q(z)` has `c = 0` and is constant. -/
lemma p23R1_quasi_const {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q) (hne : ∀ z, Q z ≠ 0)
    (h1 : ∀ z, Q (z + 2 * H.ω₁) = Q z) (c : ℂ)
    (h3 : ∀ z, Q (z + 2 * H.ω₃) = cexp (2 * c * (z + H.ω₃)) * Q z) :
    c = 0 ∧ ∀ z, Q z = Q 0 := by
  have hQ' : Differentiable ℂ (deriv Q) := fun z => ((hQ.analyticAt z).deriv).differentiableAt
  set k : ℂ → ℂ := fun z => deriv Q z / Q z with hk
  have hkd : Differentiable ℂ k := hQ'.div hQ hne
  have hd1 : ∀ z, deriv Q (z + 2 * H.ω₁) = deriv Q z := by
    intro z
    have := congrArg (fun F => deriv F z) (funext h1 : (fun z => Q (z + 2 * H.ω₁)) = Q)
    simpa [deriv_comp_add_const] using this
  have hd3 : ∀ z, deriv Q (z + 2 * H.ω₃) =
      cexp (2 * c * (z + H.ω₃)) * (2 * c * Q z + deriv Q z) := by
    intro z
    have hE : HasDerivAt (fun z => cexp (2 * c * (z + H.ω₃)))
        (cexp (2 * c * (z + H.ω₃)) * (2 * c)) z := by
      have := ((hasDerivAt_id z).add_const H.ω₃).const_mul (2 * c)
      simpa using this.cexp
    have h := (hE.mul (hQ z).hasDerivAt)
    have e : (fun z => Q (z + 2 * H.ω₃)) = fun z => cexp (2 * c * (z + H.ω₃)) * Q z := funext h3
    have h' := ((hQ (z + 2 * H.ω₃)).hasDerivAt.comp_add_const z (2 * H.ω₃))
    rw [e] at h'
    rw [h'.unique h]; ring
  have hk1 : ∀ z, k (z + 2 * H.ω₁) = k z := fun z => by simp only [hk, hd1, h1]
  have hk3 : ∀ z, k (z + 2 * H.ω₃) = k z + 2 * c := by
    intro z
    simp only [hk, hd3, h3]
    have := hne z
    field_simp
    ring
  set m := deriv k with hm
  have hmd : Differentiable ℂ m := fun z => ((hkd.analyticAt z).deriv).differentiableAt
  have hm1 : ∀ z, m (z + 2 * H.ω₁) = m z := by
    intro z
    have := congrArg (fun F => deriv F z) (funext hk1 : (fun z => k (z + 2 * H.ω₁)) = k)
    simpa [hm, deriv_comp_add_const] using this
  have hm3 : ∀ z, m (z + 2 * H.ω₃) = m z := by
    intro z
    have e : (fun z => k (z + 2 * H.ω₃)) = fun z => k z + 2 * c := funext hk3
    have := congrArg (fun F => deriv F z) e
    simpa [hm, deriv_comp_add_const] using this
  have hc := IsZLattice.isCompact_range_of_periodic H.periodPair.lattice m hmd.continuous
    (H.p23R1_lattice_periodic hm1 hm3)
  have hmc : ∀ z, m z = m 0 := fun z => hmd.apply_eq_apply_of_bounded hc.isBounded z 0
  -- `k z = m 0 * z + k 0`
  have hlin : ∀ z, k z = m 0 * z + k 0 := by
    have hd : ∀ z, deriv (fun z => k z - m 0 * z) z = 0 := by
      intro z
      have h : HasDerivAt (fun z => k z - m 0 * z) (deriv k z - m 0 * 1) z :=
        (hkd z).hasDerivAt.sub ((hasDerivAt_id' z).const_mul (m 0))
      rw [h.deriv, ← hm, hmc z]; ring
    have hdf : Differentiable ℂ (fun z => k z - m 0 * z) := hkd.sub (by fun_prop)
    intro z
    have := is_const_of_deriv_eq_zero hdf hd z 0
    simp at this
    linear_combination this
  have hα : m 0 = 0 := by
    have := hk1 0
    rw [hlin, hlin 0] at this
    have hω := H.ω₁_ne_zero
    have : m 0 * (2 * H.ω₁) = 0 := by linear_combination this
    simpa [hω] using this
  have hc0 : c = 0 := by
    have := hk3 0
    rw [hlin, hlin 0, hα] at this
    linear_combination -this / 2
  refine ⟨hc0, ?_⟩
  have h3' : ∀ z, Q (z + 2 * H.ω₃) = Q z := fun z => by rw [h3, hc0]; simp
  have hcQ := IsZLattice.isCompact_range_of_periodic H.periodPair.lattice Q hQ.continuous
    (H.p23R1_lattice_periodic h1 h3')
  exact fun z => hQ.apply_eq_apply_of_bounded hcQ.isBounded z 0

open Classical in
/-- Order of an entire function with simple zeros exactly on the lattice. -/
lemma p23R1_order_of_simple {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hz : ∀ x, f x = 0 ↔ x ∈ H.lattice) (hd : ∀ x ∈ H.lattice, deriv f x ≠ 0) (x : ℂ) :
    meromorphicOrderAt f x = if x ∈ H.lattice then 1 else 0 := by
  have ha : AnalyticAt ℂ f x := hf.analyticAt x
  rw [ha.meromorphicOrderAt_eq]
  split_ifs with hx
  · rw [ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero ((hz x).mpr hx) (hd x hx)]
    rfl
  · rw [ha.analyticOrderAt_eq_zero.mpr (fun h => hx ((hz x).mp h))]
    rfl

/-- Characterisation of `σ`: an entire `f` with simple zeros exactly on the lattice,
`f'(0) = 1`, `f(z + 2ω₁) = -e^{2η₁(z+ω₁)} f(z)` and `f(z + 2ω₃) = -e^{2b(z+ω₃)} f(z)` equals `σ`,
and then `b = η₃`. -/
lemma p23R1_sigma_eq_of {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hz : ∀ x, f x = 0 ↔ x ∈ H.lattice) (hd : ∀ x ∈ H.lattice, deriv f x ≠ 0)
    (hd0 : deriv f 0 = 1)
    (h1 : ∀ z, f (z + 2 * H.ω₁) = -cexp (2 * H.eta 1 * (z + H.ω₁)) * f z) (b : ℂ)
    (h3 : ∀ z, f (z + 2 * H.ω₃) = -cexp (2 * b * (z + H.ω₃)) * f z) :
    (∀ z, H.weierstrassSigma z = f z) ∧ b = H.eta 3 := by
  set σ := H.weierstrassSigma with hσ
  have hσd : Differentiable ℂ σ := differentiable_weierstrassSigma H.periodPair
  have hσz : ∀ x, σ x = 0 ↔ x ∈ H.lattice := fun x => weierstrassSigma_eq_zero_iff H.periodPair
  have hσ1 : ∀ z, σ (z + 2 * H.ω₁) = -cexp (2 * H.eta 1 * (z + H.ω₁)) * σ z := fun z =>
    H.weierstrassSigma_add_two_mul_halfPeriod z (j := 1) (by simp)
  have hσ3 : ∀ z, σ (z + 2 * H.ω₃) = -cexp (2 * H.eta 3 * (z + H.ω₃)) * σ z := fun z =>
    H.weierstrassSigma_add_two_mul_halfPeriod z (j := 3) (by simp)
  set g : ℂ → ℂ := fun z => σ z * (f z)⁻¹ with hg
  have hgm : MeromorphicOn g Set.univ := fun x _ =>
    (hσd.analyticAt x).meromorphicAt.mul (hf.analyticAt x).meromorphicAt.inv
  have hord : ∀ x, meromorphicOrderAt g x = 0 := by
    intro x
    show meromorphicOrderAt (σ * f⁻¹) x = 0
    rw [meromorphicOrderAt_mul (hσd.analyticAt x).meromorphicAt
      (hf.analyticAt x).meromorphicAt.inv, meromorphicOrderAt_inv,
      H.p23R1_order_of_simple hf hz hd x,
      H.p23R1_order_of_simple hσd hσz (fun x hx => deriv_weierstrassSigma_ne_zero _ hx) x]
    split_ifs <;> rfl
  set Q := toMeromorphicNFOn g Set.univ with hQ
  have hQnf : ∀ x, MeromorphicNFAt Q x := fun x =>
    meromorphicNFOn_toMeromorphicNFOn g Set.univ (Set.mem_univ x)
  have hQg : ∀ x, Q =ᶠ[𝓝[≠] x] g := fun x => hgm.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ x)
  have hQord : ∀ x, meromorphicOrderAt Q x = 0 := fun x => by
    rw [meromorphicOrderAt_congr (hQg x)]; exact hord x
  have hQan : ∀ x, AnalyticAt ℂ Q x := fun x =>
    (hQnf x).meromorphicOrderAt_nonneg_iff_analyticAt.mp (by rw [hQord x])
  have hQd : Differentiable ℂ Q := fun x => (hQan x).differentiableAt
  have hQne : ∀ x, Q x ≠ 0 := fun x => (hQnf x).meromorphicOrderAt_eq_zero_iff.mp (hQord x)
  -- transfer quasi-periodicity from `g` to `Q`
  have htrans : ∀ (w : ℂ) (E : ℂ → ℂ), Continuous E → (∀ z, g (z + w) = E z * g z) →
      ∀ z, Q (z + w) = E z * Q z := by
    intro w E hE hgw z
    have hmap : Tendsto (fun y => y + w) (𝓝[≠] z) (𝓝[≠] (z + w)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_id.add continuous_const : Continuous fun y : ℂ => y + w).tendsto z
          |>.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy
    have l1 : Tendsto (fun y => Q (y + w)) (𝓝[≠] z) (𝓝 (Q (z + w))) :=
      ((hQd.continuous.comp (continuous_id.add continuous_const :
        Continuous fun y : ℂ => y + w)).tendsto z).mono_left nhdsWithin_le_nhds
    have l2 : Tendsto (fun y => E y * Q y) (𝓝[≠] z) (𝓝 (E z * Q z)) :=
      ((hE.mul hQd.continuous).tendsto z).mono_left nhdsWithin_le_nhds
    have hev : (fun y => Q (y + w)) =ᶠ[𝓝[≠] z] fun y => E y * Q y := by
      filter_upwards [hmap.eventually (hQg (z + w)), hQg z] with y hy1 hy2
      rw [hy1, hy2, hgw y]
    exact tendsto_nhds_unique (l1.congr' hev) l2
  have hg1 : ∀ z, g (z + 2 * H.ω₁) = (fun _ => (1 : ℂ)) z * g z := by
    intro z
    simp only [hg, hσ1, h1, mul_inv, one_mul]
    have := exp_ne_zero (2 * H.eta 1 * (z + H.ω₁))
    field_simp
  have hg3 : ∀ z, g (z + 2 * H.ω₃) =
      (fun z => cexp (2 * (H.eta 3 - b) * (z + H.ω₃))) z * g z := by
    intro z
    simp only [hg, hσ3, h3, mul_inv]
    have e : cexp (2 * (H.eta 3 - b) * (z + H.ω₃)) =
        cexp (2 * H.eta 3 * (z + H.ω₃)) * (cexp (2 * b * (z + H.ω₃)))⁻¹ := by
      rw [← exp_neg, ← exp_add]; ring_nf
    rw [e]
    ring
  have hQ1 := htrans _ _ continuous_const hg1
  have hQ3 := htrans _ _ (by fun_prop) hg3
  obtain ⟨hc, hQc⟩ := H.p23R1_quasi_const hQd hQne (fun z => by simpa using hQ1 z) _ hQ3
  -- the value at `0`
  have hT1 : Tendsto (fun w => σ w / w) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have := (hasDerivAt_iff_tendsto_slope.mp (p23R1_hasDerivAt_weierstrassSigma_zero H.periodPair))
    refine this.congr' (Eventually.of_forall fun w => ?_)
    simp [slope_def_field, hσ, weierstrassSigma_eq_zero_of_mem _ (zero_mem _)]
  have hf0 : f 0 = 0 := (hz 0).mpr (zero_mem _)
  have hT2 : Tendsto (fun w => f w / w) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have := hasDerivAt_iff_tendsto_slope.mp (hd0 ▸ (hf 0).hasDerivAt)
    refine this.congr' (Eventually.of_forall fun w => ?_)
    simp [slope_def_field, hf0]
  have hlim : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (1 / 1)) := by
    refine (hT1.div hT2 one_ne_zero).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw0 : w ≠ 0 := hw
    simp only [hg]
    rw [Pi.div_apply, div_div_div_cancel_right₀ hw0, div_eq_mul_inv]
  have hQ0 : Q 0 = 1 := by
    have := tendsto_nhds_unique ((hQd.continuous.tendsto 0).mono_left nhdsWithin_le_nhds)
      (hlim.congr' (hQg 0).symm)
    simpa using this
  refine ⟨fun z => ?_, by linear_combination -hc / 1⟩
  by_cases hzl : z ∈ H.lattice
  · rw [(hσz z).mpr hzl, (hz z).mpr hzl]
  · have hfz : f z ≠ 0 := fun h => hzl ((hz z).mp h)
    have hgc : ContinuousAt g z := (hσd z).continuousAt.mul ((hf z).continuousAt.inv₀ hfz)
    have := tendsto_nhds_unique ((hQd.continuous.tendsto z).mono_left nhdsWithin_le_nhds)
      ((hgc.tendsto.mono_left nhdsWithin_le_nhds).congr' (hQg z).symm)
    rw [hQc z, hQ0] at this
    simp only [hg] at this
    field_simp at this
    exact this.symm

/-- The theta-function expression of DLMF 23.6.9. -/
noncomputable def p23R1_thetaSigma (z : ℂ) : ℂ :=
  2 * H.ω₁ * cexp (H.eta 1 * z ^ 2 / (2 * H.ω₁)) *
    jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau / (π * jacobiThetaOneDerivNullTau H.tau)

/-- `θ₁'(0|τ) ≠ 0`. -/
lemma p23R1_thetaOneDeriv_ne_zero : jacobiThetaOneDerivNullTau H.tau ≠ 0 := by
  have hτ := H.tau_im_pos
  rw [jacobiThetaOneDerivNullTau_eq_mul hτ]
  obtain ⟨a, b, c⟩ := jacobiThetaNullTau_ne_zero hτ
  exact mul_ne_zero (mul_ne_zero a b) c

/-- `θ₁(·|τ)` is entire. -/
lemma p23R1_differentiable_thetaOne : Differentiable ℂ (fun w => jacobiThetaOneTau w H.tau) := by
  simpa [jacobiThetaTau] using differentiable_jacobiThetaTau 1 H.tau_im_pos

/-- The theta expression of 23.6.9 is entire. -/
lemma p23R1_differentiable_thetaSigma : Differentiable ℂ H.p23R1_thetaSigma := by
  have := H.p23R1_differentiable_thetaOne
  unfold p23R1_thetaSigma
  have h2 : Differentiable ℂ (fun z : ℂ => jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau) :=
    this.comp (by fun_prop)
  fun_prop

/-- Quasi-periodicity of the theta expression over the whole lattice. -/
lemma p23R1_thetaSigma_add_lattice (m n : ℤ) (z : ℂ) :
    H.p23R1_thetaSigma (z + (2 * m * H.ω₁ + 2 * n * H.ω₃)) =
      cexp (H.eta 1 * ((z + (2 * m * H.ω₁ + 2 * n * H.ω₃)) ^ 2 - z ^ 2) / (2 * H.ω₁)) *
        ((-1 : ℂ) ^ (m + n) * cexp (-(π * I * H.tau * n ^ 2)) *
          cexp (-2 * I * n * (π * z / (2 * H.ω₁)))) * H.p23R1_thetaSigma z := by
  have hω := H.ω₁_ne_zero
  unfold p23R1_thetaSigma
  have e : π * (z + (2 * m * H.ω₁ + 2 * n * H.ω₃)) / (2 * H.ω₁) =
      π * z / (2 * H.ω₁) + (m + n * H.tau) * π := by
    rw [HalfPeriods.tau]; field_simp
  rw [e, jacobiThetaOneTau_add_lattice]
  have ee : cexp (H.eta 1 * (z + (2 * m * H.ω₁ + 2 * n * H.ω₃)) ^ 2 / (2 * H.ω₁)) =
      cexp (H.eta 1 * ((z + (2 * m * H.ω₁ + 2 * n * H.ω₃)) ^ 2 - z ^ 2) / (2 * H.ω₁)) *
        cexp (H.eta 1 * z ^ 2 / (2 * H.ω₁)) := by
    rw [← exp_add]; congr 1; ring
  rw [ee]
  ring

/-- Zeros of the theta expression: exactly the lattice. -/
lemma p23R1_thetaSigma_eq_zero_iff (x : ℂ) : H.p23R1_thetaSigma x = 0 ↔ x ∈ H.lattice := by
  have hω := H.ω₁_ne_zero
  have hD := H.p23R1_thetaOneDeriv_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold p23R1_thetaSigma
  rw [div_eq_zero_iff, mul_eq_zero, mul_eq_zero, mul_eq_zero,
    (jacobiThetaTau_eq_zero_iff H.tau_im_pos _).1, H.mem_lattice_iff]
  simp only [two_ne_zero, hω, exp_ne_zero, hπ, hD, false_or, or_false, mul_eq_zero]
  refine exists₂_congr fun m n => ?_
  rw [HalfPeriods.tau]
  constructor
  · intro h
    field_simp at h
    linear_combination h
  · intro h; rw [h]; field_simp

/-- The theta expression has derivative `1` at `0`. -/
lemma p23R1_thetaSigma_hasDerivAt_zero : HasDerivAt H.p23R1_thetaSigma 1 0 := by
  have hω := H.ω₁_ne_zero
  have hD := H.p23R1_thetaOneDeriv_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hθ : HasDerivAt (fun w => jacobiThetaOneTau w H.tau) (jacobiThetaOneDerivNullTau H.tau)
      (π * 0 / (2 * H.ω₁)) := by
    rw [mul_zero, zero_div]; exact (H.p23R1_differentiable_thetaOne 0).hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => π * z / (2 * H.ω₁)) (π * 1 / (2 * H.ω₁)) 0 :=
    ((hasDerivAt_id 0).const_mul (π : ℂ)).div_const _
  have h1 := hθ.comp 0 hlin
  have hE : HasDerivAt (fun z : ℂ => cexp (H.eta 1 * z ^ 2 / (2 * H.ω₁)))
      (cexp (H.eta 1 * 0 ^ 2 / (2 * H.ω₁)) * (H.eta 1 * (2 * 0) / (2 * H.ω₁))) 0 := by
    have := ((hasDerivAt_pow 2 (0 : ℂ)).const_mul (H.eta 1)).div_const (2 * H.ω₁)
    simpa using this.cexp
  have h := ((hE.const_mul (2 * H.ω₁)).mul h1).div_const (π * jacobiThetaOneDerivNullTau H.tau)
  convert h using 1
  · funext x; simp only [p23R1_thetaSigma, Pi.mul_apply, Function.comp_def]
  · simp only [Function.comp_def, mul_zero, zero_div, zero_mul]
    field_simp
    simp

/-- The zeros of the theta expression are simple. -/
lemma p23R1_thetaSigma_deriv_ne_zero (x : ℂ) (hx : x ∈ H.lattice) :
    deriv H.p23R1_thetaSigma x ≠ 0 := by
  obtain ⟨m, n, rfl⟩ := H.mem_lattice_iff.mp hx
  set l := 2 * m * H.ω₁ + 2 * n * H.ω₃
  set U : ℂ → ℂ := fun z => cexp (H.eta 1 * ((z + l) ^ 2 - z ^ 2) / (2 * H.ω₁)) *
    ((-1 : ℂ) ^ (m + n) * cexp (-(π * I * H.tau * n ^ 2)) *
      cexp (-2 * I * n * (π * z / (2 * H.ω₁)))) with hU
  have hUd : Differentiable ℂ U := by rw [hU]; fun_prop
  have e : (fun z => H.p23R1_thetaSigma (z + l)) = fun z => U z * H.p23R1_thetaSigma z :=
    funext fun z => H.p23R1_thetaSigma_add_lattice m n z
  have h0 := H.p23R1_thetaSigma_hasDerivAt_zero
  have hF0 : H.p23R1_thetaSigma 0 = 0 := (H.p23R1_thetaSigma_eq_zero_iff 0).mpr (zero_mem _)
  have hA : HasDerivAt (fun z => H.p23R1_thetaSigma (z + l)) (deriv H.p23R1_thetaSigma l) 0 := by
    have := (H.p23R1_differentiable_thetaSigma (0 + l)).hasDerivAt.comp_add_const 0 l
    simpa using this
  rw [e] at hA
  have hB := (hUd 0).hasDerivAt.mul h0
  rw [hA.unique hB, hF0, mul_zero, zero_add, mul_one, hU]
  have : ((-1 : ℂ) ^ (m + n)) ≠ 0 := zpow_ne_zero _ (by norm_num)
  simp only
  exact mul_ne_zero (exp_ne_zero _) (mul_ne_zero (mul_ne_zero this (exp_ne_zero _))
    (exp_ne_zero _))

/-- DLMF 23.6.9 together with Legendre's relation in the form
`η₃ = η₁ω₃/ω₁ - πi/(2ω₁)`. -/
theorem p23R1_sigma_theta :
    (∀ z, H.weierstrassSigma z = H.p23R1_thetaSigma z) ∧
      H.eta 1 * H.ω₃ / H.ω₁ - π * I / (2 * H.ω₁) = H.eta 3 := by
  have hω := H.ω₁_ne_zero
  refine H.p23R1_sigma_eq_of H.p23R1_differentiable_thetaSigma H.p23R1_thetaSigma_eq_zero_iff
    H.p23R1_thetaSigma_deriv_ne_zero H.p23R1_thetaSigma_hasDerivAt_zero.deriv ?_ _ ?_
  · intro z
    have := H.p23R1_thetaSigma_add_lattice 1 0 z
    simp only [Int.cast_one, Int.cast_zero, mul_one, zero_mul, add_zero, mul_zero,
      exp_zero, zpow_one] at this
    rw [this]
    have e : cexp (H.eta 1 * ((z + 2 * H.ω₁) ^ 2 - z ^ 2) / (2 * H.ω₁)) =
        cexp (2 * H.eta 1 * (z + H.ω₁)) := by congr 1; field_simp; ring
    rw [e]; simp
  · intro z
    have := H.p23R1_thetaSigma_add_lattice 0 1 z
    simp only [Int.cast_one, Int.cast_zero, mul_one, zero_mul, zero_add, mul_zero, one_pow,
      zpow_one] at this
    rw [this]
    have e : cexp (H.eta 1 * ((z + 2 * H.ω₃) ^ 2 - z ^ 2) / (2 * H.ω₁)) *
        (cexp (-(π * I * H.tau)) * cexp (-2 * I * (π * z / (2 * H.ω₁)))) =
        cexp (2 * (H.eta 1 * H.ω₃ / H.ω₁ - π * I / (2 * H.ω₁)) * (z + H.ω₃)) := by
      rw [← exp_add, ← exp_add]; congr 1; rw [HalfPeriods.tau]; field_simp; ring
    rw [← e]; ring

/-- DLMF 23.2.14 (Legendre's relation):
`η₃ω₂ - η₂ω₃ = η₂ω₁ - η₁ω₂ = η₁ω₃ - η₃ω₁ = πi/2`. -/
@[dlmf 23.2.E14]
theorem legendre_relation :
    H.eta 3 * H.ω₂ - H.eta 2 * H.ω₃ = π * I / 2 ∧
      H.eta 2 * H.ω₁ - H.eta 1 * H.ω₂ = π * I / 2 ∧
      H.eta 1 * H.ω₃ - H.eta 3 * H.ω₁ = π * I / 2 := by
  have hω := H.ω₁_ne_zero
  have hL := H.p23R1_sigma_theta.2
  have h3 : H.eta 1 * H.ω₃ - H.eta 3 * H.ω₁ = π * I / 2 := by
    rw [← hL]; field_simp; ring
  have he : H.eta 2 = -H.eta 1 - H.eta 3 := by
    linear_combination H.eta_one_add_eta_two_add_eta_three
  refine ⟨?_, ?_, h3⟩ <;> rw [he, ω₂] <;> linear_combination h3

/-- `σ(z + 2mω_j) = (-1)^m e^{2mη_j(z + mω_j)} σ(z)` for `m ∈ ℤ`. -/
lemma p23R1_sigma_add_int_mul {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) (m : ℤ) :
    ∀ z, H.weierstrassSigma (z + 2 * m * H.halfPeriod j) =
      (-1 : ℂ) ^ m * cexp (2 * m * H.eta j * (z + m * H.halfPeriod j)) *
        H.weierstrassSigma z := by
  have h1 := fun z => H.weierstrassSigma_add_two_mul_halfPeriod z hj
  set ω := H.halfPeriod j
  set η := H.eta j
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  induction m using Int.induction_on with
  | zero => intro z; simp
  | succ m ih =>
    intro z
    push_cast at ih ⊢
    rw [show z + 2 * (m + 1) * ω = (z + 2 * m * ω) + 2 * ω by ring, h1, ih, zpow_add_one₀ hm1]
    have : cexp (2 * η * (z + 2 * m * ω + ω)) * cexp (2 * m * η * (z + m * ω)) =
        cexp (2 * (m + 1) * η * (z + (m + 1) * ω)) := by
      rw [← exp_add]; congr 1; ring
    rw [← this]; ring
  | pred m ih =>
    intro z
    push_cast at ih ⊢
    have key := h1 (z + 2 * (-(m : ℂ) - 1) * ω)
    rw [show z + 2 * (-(m : ℂ) - 1) * ω + 2 * ω = z + 2 * (-(m : ℂ)) * ω by ring, ih] at key
    rw [zpow_sub_one₀ hm1, inv_neg, inv_one]
    have he : cexp (2 * η * (z + 2 * (-(m : ℂ) - 1) * ω + ω)) *
        cexp (2 * (-(m : ℂ) - 1) * η * (z + (-(m : ℂ) - 1) * ω)) =
        cexp (2 * (-(m : ℂ)) * η * (z + (-(m : ℂ)) * ω)) := by
      rw [← exp_add]; congr 1; ring
    have hne : cexp (2 * η * (z + 2 * (-(m : ℂ) - 1) * ω + ω)) ≠ 0 := exp_ne_zero _
    have hpow : ((-1 : ℂ) ^ (-(m : ℤ))) ≠ 0 := zpow_ne_zero _ hm1
    apply mul_left_cancel₀ hne
    rw [mul_comm] at key
    linear_combination key + ((-1 : ℂ) ^ (-(m : ℤ)) * H.weierstrassSigma z) * he

/-- DLMF 23.2.17: for `j ≠ k` in `{1, 2, 3}` and `m, n ∈ ℤ`,
`σ(z + 2mω_j + 2nω_k)/σ(z) = (-1)^{m+n+mn} exp((2mη_j + 2nη_k)(mω_j + nω_k + z))`.
Stated in multiplied-out form, valid for all `z` (both sides vanish on `𝕃`). -/
@[dlmf 23.2.E17]
theorem weierstrassSigma_add_lattice (z : ℂ) {j k : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ))
    (hk : k ∈ ({1, 2, 3} : Finset ℕ)) (hjk : j ≠ k) (m n : ℤ) :
    H.weierstrassSigma (z + 2 * m * H.halfPeriod j + 2 * n * H.halfPeriod k) =
      (-1 : ℂ) ^ (m + n + m * n) *
        cexp ((2 * m * H.eta j + 2 * n * H.eta k) * (m * H.halfPeriod j + n * H.halfPeriod k + z)) *
        H.weierstrassSigma z := by
  have hd : cexp (2 * (H.eta k * H.halfPeriod j - H.eta j * H.halfPeriod k)) = -1 := by
    obtain ⟨l1, l2, l3⟩ := H.legendre_relation
    have hpi : cexp (π * I) = -1 := exp_pi_mul_I
    have hpi' : cexp (-(π * I)) = -1 := by rw [exp_neg, hpi]; norm_num
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj hk
    rcases hj with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl <;>
      simp only [ne_eq, not_true_eq_false] at hjk <;>
      simp only [halfPeriod_one, halfPeriod_two, halfPeriod_three]
    · rw [← hpi]; congr 1; linear_combination (2 : ℂ) * l2
    · rw [← hpi']; congr 1; linear_combination (-2 : ℂ) * l3
    · rw [← hpi']; congr 1; linear_combination (-2 : ℂ) * l2
    · rw [← hpi]; congr 1; linear_combination (2 : ℂ) * l1
    · rw [← hpi]; congr 1; linear_combination (2 : ℂ) * l3
    · rw [← hpi']; congr 1; linear_combination (-2 : ℂ) * l1
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  rw [H.p23R1_sigma_add_int_mul hk n, H.p23R1_sigma_add_int_mul hj m,
    zpow_add₀ hm1, zpow_add₀ hm1]
  have hmn : (-1 : ℂ) ^ (m * n) =
      cexp (((m * n : ℤ) : ℂ) * (2 * (H.eta k * H.halfPeriod j - H.eta j * H.halfPeriod k))) := by
    rw [exp_int_mul, hd]
  rw [hmn]
  have : cexp (2 * n * H.eta k * (z + 2 * m * H.halfPeriod j + n * H.halfPeriod k)) *
      cexp (2 * m * H.eta j * (z + m * H.halfPeriod j)) =
      cexp (((m * n : ℤ) : ℂ) * (2 * (H.eta k * H.halfPeriod j - H.eta j * H.halfPeriod k))) *
      cexp ((2 * m * H.eta j + 2 * n * H.eta k) *
        (m * H.halfPeriod j + n * H.halfPeriod k + z)) := by
    rw [← exp_add, ← exp_add]; congr 1; push_cast; ring
  linear_combination ((-1 : ℂ) ^ m * (-1 : ℂ) ^ n * H.weierstrassSigma z) * this

/-- For an entire `φ` with `φ(0) = 0`, `φ'(0) ≠ 0`, `φ''(0) = 0`:
`(φ'/φ)'(w) + 1/w² → φ'''(0)/(3φ'(0))` as `w → 0`. -/
lemma p23R1_logDeriv_tendsto {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) (h0 : φ 0 = 0)
    (hc : deriv φ 0 ≠ 0) (h2 : iteratedDeriv 2 φ 0 = 0) :
    Tendsto (fun w => deriv (fun z => deriv φ z / φ z) w + 1 / w ^ 2) (𝓝[≠] 0)
      (𝓝 (iteratedDeriv 3 φ 0 / (3 * deriv φ 0))) := by
  set ψ := dslope φ 0 with hψdef
  have hψ : Differentiable ℂ ψ := fun x =>
    (((Complex.differentiableOn_dslope Filter.univ_mem).mpr hφ.differentiableOn) x
      (Set.mem_univ x)).differentiableAt Filter.univ_mem
  have hψ1 : Differentiable ℂ (deriv ψ) := fun z => ((hψ.analyticAt z).deriv).differentiableAt
  have hψ2 : Differentiable ℂ (deriv (deriv ψ)) := fun z =>
    ((hψ1.analyticAt z).deriv).differentiableAt
  have hφψ : φ = fun w => w * ψ w := by
    funext w; have := sub_smul_dslope_of_zero h0 w; simp only [sub_zero, smul_eq_mul] at this
    exact this.symm
  have hψ0 : ψ 0 = deriv φ 0 := dslope_same φ 0
  have hd1 : deriv φ = fun w => ψ w + w * deriv ψ w := by
    funext w; rw [hφψ]
    have h : HasDerivAt (fun w => w * ψ w) (1 * ψ w + w * deriv ψ w) w :=
      (hasDerivAt_id' w).mul (hψ w).hasDerivAt
    rw [h.deriv]; ring
  have hd2 : deriv (deriv φ) = fun w => 2 * deriv ψ w + w * deriv (deriv ψ) w := by
    funext w; rw [hd1]
    have h : HasDerivAt (fun w => ψ w + w * deriv ψ w)
        (deriv ψ w + (1 * deriv ψ w + w * deriv (deriv ψ) w)) w :=
      (hψ w).hasDerivAt.add ((hasDerivAt_id' w).mul (hψ1 w).hasDerivAt)
    rw [h.deriv]; ring
  have hd3 : deriv (deriv (deriv φ)) 0 = 3 * deriv (deriv ψ) 0 := by
    rw [hd2]
    have h : HasDerivAt (fun w => 2 * deriv ψ w + w * deriv (deriv ψ) w)
        (2 * deriv (deriv ψ) 0 + (1 * deriv (deriv ψ) 0 + 0 * deriv (deriv (deriv ψ)) 0)) 0 :=
      ((hψ1 0).hasDerivAt.const_mul 2).add ((hasDerivAt_id' 0).mul (hψ2 0).hasDerivAt)
    rw [h.deriv]; ring
  have hi2 : iteratedDeriv 2 φ 0 = 2 * deriv ψ 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd2]; simp
  have hi3 : iteratedDeriv 3 φ 0 = 3 * deriv (deriv ψ) 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, hd3]
  have hψ'0 : deriv ψ 0 = 0 := by
    have := h2; rw [hi2] at this; simpa using this
  have hψne : ψ 0 ≠ 0 := by rwa [hψ0]
  set U : Set ℂ := {w | ψ w ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun hψ.continuous continuous_const
  have hU0 : U ∈ 𝓝 (0 : ℂ) := hUo.mem_nhds hψne
  set R : ℂ → ℂ := fun w => (deriv (deriv ψ) w * ψ w - deriv ψ w ^ 2) / ψ w ^ 2 with hR
  have hRc : ContinuousAt R 0 := by
    have : ContinuousAt (fun w => (deriv (deriv ψ) w * ψ w - deriv ψ w ^ 2)) 0 :=
      ((hψ2.continuous.mul hψ.continuous).sub (hψ1.continuous.pow 2)).continuousAt
    exact this.div (hψ.continuous.pow 2).continuousAt (pow_ne_zero 2 hψne)
  have hR0 : R 0 = iteratedDeriv 3 φ 0 / (3 * deriv φ 0) := by
    simp only [hR, hψ'0, hi3, ← hψ0]; field_simp; ring
  rw [← hR0]
  refine (hRc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [nhdsWithin_le_nhds hU0, self_mem_nhdsWithin] with w hw hw0
  have hw0' : w ≠ 0 := hw0
  have hψw : ψ w ≠ 0 := hw
  -- `φ'/φ = 1/z + ψ'/ψ` near `w`
  have hev : (fun z => deriv φ z / φ z) =ᶠ[𝓝 w] fun z => z⁻¹ + deriv ψ z / ψ z := by
    filter_upwards [hUo.mem_nhds hw, isOpen_ne.mem_nhds hw0'] with z hz hz0
    have hz' : ψ z ≠ 0 := hz
    have hz0' : z ≠ 0 := hz0
    rw [hd1, hφψ]; field_simp
  rw [hev.deriv_eq]
  have h : HasDerivAt (fun z => z⁻¹ + deriv ψ z / ψ z)
      (-(w ^ 2)⁻¹ + (deriv (deriv ψ) w * ψ w - deriv ψ w * deriv ψ w) / ψ w ^ 2) w :=
    (hasDerivAt_inv hw0').add ((hψ1 w).hasDerivAt.div (hψ w).hasDerivAt hψw)
  rw [h.deriv]
  simp only [hR]
  field_simp
  ring

/-- Derivative of the theta expression of 23.6.9. -/
lemma p23R1_hasDerivAt_thetaSigma (u : ℂ) :
    HasDerivAt H.p23R1_thetaSigma
      (H.p23R1_thetaSigma u * (H.eta 1 / H.ω₁ * u) +
        2 * H.ω₁ * cexp (H.eta 1 * u ^ 2 / (2 * H.ω₁)) *
          (deriv (fun w => jacobiThetaOneTau w H.tau) (π * u / (2 * H.ω₁)) * (π / (2 * H.ω₁))) /
          (π * jacobiThetaOneDerivNullTau H.tau)) u := by
  have hω := H.ω₁_ne_zero
  have hD := H.p23R1_thetaOneDeriv_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hθ := (H.p23R1_differentiable_thetaOne (π * u / (2 * H.ω₁))).hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => π * z / (2 * H.ω₁)) (π * 1 / (2 * H.ω₁)) u :=
    ((hasDerivAt_id u).const_mul (π : ℂ)).div_const _
  have h1 := hθ.comp u hlin
  have hE : HasDerivAt (fun z : ℂ => cexp (H.eta 1 * z ^ 2 / (2 * H.ω₁)))
      (cexp (H.eta 1 * u ^ 2 / (2 * H.ω₁)) * (H.eta 1 * (↑2 * u ^ (2 - 1)) / (2 * H.ω₁))) u := by
    have := ((hasDerivAt_pow 2 u).const_mul (H.eta 1)).div_const (2 * H.ω₁)
    exact this.cexp
  have h := ((hE.const_mul (2 * H.ω₁)).mul h1).div_const (π * jacobiThetaOneDerivNullTau H.tau)
  convert h using 1
  · funext x; simp only [p23R1_thetaSigma, Pi.mul_apply, Function.comp_def]
  · simp only [p23R1_thetaSigma, Function.comp_def]
    field_simp
    ring

/-- DLMF 23.6.13 (helper form). -/
lemma p23R1_zeta_theta {u : ℂ} (hu : u ∉ H.lattice) :
    H.weierstrassZeta u = H.eta 1 / H.ω₁ * u + π / (2 * H.ω₁) *
      (deriv (fun z ↦ jacobiThetaOneTau z H.tau) (π * u / (2 * H.ω₁)) /
        jacobiThetaOneTau (π * u / (2 * H.ω₁)) H.tau) := by
  have hω := H.ω₁_ne_zero
  have hD := H.p23R1_thetaOneDeriv_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hσ : Weierstrass.weierstrassSigma H.periodPair = H.p23R1_thetaSigma :=
    funext H.p23R1_sigma_theta.1
  have hne : H.p23R1_thetaSigma u ≠ 0 := fun h => hu ((H.p23R1_thetaSigma_eq_zero_iff u).mp h)
  have hθ : jacobiThetaOneTau (π * u / (2 * H.ω₁)) H.tau ≠ 0 := by
    intro h; apply hne; simp [p23R1_thetaSigma, h]
  rw [HalfPeriods.weierstrassZeta, weierstrassZeta_eq_deriv_div _ hu, hσ,
    (H.p23R1_hasDerivAt_thetaSigma u).deriv, add_div, mul_div_cancel_left₀ _ hne]
  congr 1
  simp only [p23R1_thetaSigma]
  field_simp

/-- `℘(u) = -η₁/ω₁ - (π/(2ω₁))² (θ₁'/θ₁)'(πu/(2ω₁))` for `u ∉ 𝕃`. -/
lemma p23R1_wp_theta_aux {u : ℂ} (hu : u ∉ H.lattice) :
    H.weierstrassP u = -(H.eta 1 / H.ω₁) - (π / (2 * H.ω₁)) ^ 2 *
      deriv (fun z ↦ deriv (fun w ↦ jacobiThetaOneTau w H.tau) z / jacobiThetaOneTau z H.tau)
        (π * u / (2 * H.ω₁)) := by
  have hω := H.ω₁_ne_zero
  set θ : ℂ → ℂ := fun w => jacobiThetaOneTau w H.tau with hθdef
  have hθd : Differentiable ℂ θ := H.p23R1_differentiable_thetaOne
  have hθ'd : Differentiable ℂ (deriv θ) := fun z => ((hθd.analyticAt z).deriv).differentiableAt
  have hθne : ∀ v, v ∉ H.lattice → θ (π * v / (2 * H.ω₁)) ≠ 0 := by
    intro v hv h
    apply hv
    apply (H.p23R1_thetaSigma_eq_zero_iff v).mp
    simp only [p23R1_thetaSigma, div_eq_zero_iff, mul_eq_zero, exp_ne_zero, or_false]
    exact Or.inl (Or.inr h)
  have hopen : IsOpen (H.latticeᶜ : Set ℂ) := H.periodPair.isClosed_lattice.isOpen_compl
  have hev : Weierstrass.weierstrassZeta H.periodPair =ᶠ[𝓝 u] fun v => H.eta 1 / H.ω₁ * v +
      π / (2 * H.ω₁) * (deriv θ (π * v / (2 * H.ω₁)) / θ (π * v / (2 * H.ω₁))) := by
    filter_upwards [hopen.mem_nhds hu] with v hv using H.p23R1_zeta_theta hv
  have hL : HasDerivAt (fun z => deriv θ z / θ z)
      (deriv (fun z => deriv θ z / θ z) (π * u / (2 * H.ω₁))) (π * u / (2 * H.ω₁)) :=
    (((hθ'd _).div (hθd _) (hθne u hu))).hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => π * z / (2 * H.ω₁)) (π * 1 / (2 * H.ω₁)) u :=
    ((hasDerivAt_id u).const_mul (π : ℂ)).div_const _
  have hR := (((hasDerivAt_id u).const_mul (H.eta 1 / H.ω₁)).add
    ((hL.comp u hlin).const_mul (π / (2 * H.ω₁))))
  have h := ((hasDerivAt_weierstrassZeta H.periodPair hu).congr_of_eventuallyEq hev.symm).unique hR
  simp only [HalfPeriods.weierstrassP]
  linear_combination -h

/-- DLMF 23.6.8 (helper form): `η₁ = -(π²/(12ω₁)) θ₁'''(0)/θ₁'(0)`. -/
lemma p23R1_eta_one_theta :
    H.eta 1 = -(π ^ 2 / (12 * H.ω₁)) *
      (thetaOneTripleDerivNull H.tau / jacobiThetaOneDerivNullTau H.tau) := by
  have hω := H.ω₁_ne_zero
  have hD := H.p23R1_thetaOneDeriv_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  set s : ℂ := π / (2 * H.ω₁) with hs
  have hs0 : s ≠ 0 := by rw [hs]; exact div_ne_zero hπ (mul_ne_zero two_ne_zero hω)
  have hθ0 : jacobiThetaOneTau 0 H.tau = 0 := by
    simpa using jacobiThetaOneTau_lattice_eq_zero H.tau 0 0
  have hlog := p23R1_logDeriv_tendsto H.p23R1_differentiable_thetaOne hθ0 hD
    (jacobiTheta_iteratedDeriv_zero_values H.tau).1
  have hmap : Tendsto (fun u : ℂ => s * u) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun u : ℂ => s * u) (𝓝 0) (𝓝 (s * 0)) := tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at this; exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact mul_ne_zero hs0 hu
  have hA := ((hlog.comp hmap).const_mul (s ^ 2)).const_sub (-(H.eta 1 / H.ω₁))
  have hP : Tendsto (fun u => H.weierstrassP u - 1 / u ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have := (analyticAt_weierstrassP_sub H.periodPair (zero_mem _)).continuousAt.tendsto
    simp only [sub_zero, PeriodPair.weierstrassP_zero] at this
    simpa using this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ u in 𝓝[≠] (0 : ℂ), H.weierstrassP u - 1 / u ^ 2 =
      -(H.eta 1 / H.ω₁) - s ^ 2 * ((fun w => deriv (fun z => deriv (fun w ↦ jacobiThetaOneTau w
        H.tau) z / jacobiThetaOneTau z H.tau) w + 1 / w ^ 2) ∘
        fun u => s * u) u := by
    filter_upwards [nhdsWithin_le_nhds (H.periodPair.compl_lattice_sdiff_singleton_mem_nhds 0),
      self_mem_nhdsWithin] with u h1 h2
    have hu : u ∉ H.lattice := fun h => h1 ⟨h, h2⟩
    have hu0 : u ≠ 0 := h2
    rw [H.p23R1_wp_theta_aux hu]
    simp only [Function.comp_apply]
    rw [show π * u / (2 * H.ω₁) = s * u by rw [hs]; ring]
    have hsu : s * u ≠ 0 := mul_ne_zero hs0 hu0
    field_simp
    rw [hs]
    field_simp
    ring
  have := tendsto_nhds_unique hP (hA.congr' (hev.mono fun u hu => hu.symm))
  rw [thetaOneTripleDerivNull]
  rw [hs, show deriv (fun w => jacobiThetaOneTau w H.tau) 0 = jacobiThetaOneDerivNullTau H.tau
    from rfl] at this
  field_simp at this ⊢
  linear_combination this

/-- `℘(z) - ℘(a) = -(πθ₁'(0))²/(4ω₁²) · θ₁(w+b)θ₁(w-b)/(θ₁(w)²θ₁(b)²)`, `w = πz/(2ω₁)`,
`b = πa/(2ω₁)`, for `z, a ∉ 𝕃`. -/
lemma p23R1_wp_sub_theta {z a : ℂ} (hz : z ∉ H.lattice) (ha : a ∉ H.lattice) :
    H.weierstrassP z - H.weierstrassP a =
      -((π * jacobiThetaOneDerivNullTau H.tau) ^ 2 / (4 * H.ω₁ ^ 2)) *
        (jacobiThetaOneTau (π * z / (2 * H.ω₁) + π * a / (2 * H.ω₁)) H.tau *
          jacobiThetaOneTau (π * z / (2 * H.ω₁) - π * a / (2 * H.ω₁)) H.tau /
          (jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau ^ 2 *
            jacobiThetaOneTau (π * a / (2 * H.ω₁)) H.tau ^ 2)) := by
  have hω := H.ω₁_ne_zero
  have hD := H.p23R1_thetaOneDeriv_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h3 := weierstrassSigma_add_mul_sub H.periodPair hz ha
  have hσ := H.p23R1_sigma_theta.1
  rw [← HalfPeriods.weierstrassSigma, ← HalfPeriods.weierstrassSigma,
    ← HalfPeriods.weierstrassSigma, ← HalfPeriods.weierstrassSigma] at h3
  simp only [hσ, p23R1_thetaSigma] at h3
  have hθz : jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau ≠ 0 := by
    intro h; apply hz; apply (H.p23R1_thetaSigma_eq_zero_iff z).mp
    simp only [p23R1_thetaSigma, h, mul_zero, zero_div]
  have hθa : jacobiThetaOneTau (π * a / (2 * H.ω₁)) H.tau ≠ 0 := by
    intro h; apply ha; apply (H.p23R1_thetaSigma_eq_zero_iff a).mp
    simp only [p23R1_thetaSigma, h, mul_zero, zero_div]
  rw [show π * (z + a) / (2 * H.ω₁) = π * z / (2 * H.ω₁) + π * a / (2 * H.ω₁) by ring,
    show π * (z - a) / (2 * H.ω₁) = π * z / (2 * H.ω₁) - π * a / (2 * H.ω₁) by ring] at h3
  have hE : cexp (H.eta 1 * (z + a) ^ 2 / (2 * H.ω₁)) * cexp (H.eta 1 * (z - a) ^ 2 / (2 * H.ω₁)) =
      cexp (H.eta 1 * z ^ 2 / (2 * H.ω₁)) ^ 2 * cexp (H.eta 1 * a ^ 2 / (2 * H.ω₁)) ^ 2 := by
    rw [← exp_add, ← exp_nat_mul, ← exp_nat_mul, ← exp_add]; congr 1; push_cast; ring
  have hez := exp_ne_zero (H.eta 1 * z ^ 2 / (2 * H.ω₁))
  have hea := exp_ne_zero (H.eta 1 * a ^ 2 / (2 * H.ω₁))
  simp only [HalfPeriods.weierstrassP]
  rw [← neg_sub, ← h3]
  generalize jacobiThetaOneTau (π * z / (2 * H.ω₁) + π * a / (2 * H.ω₁)) H.tau = Tp at *
  generalize jacobiThetaOneTau (π * z / (2 * H.ω₁) - π * a / (2 * H.ω₁)) H.tau = Tm at *
  generalize jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau = Tz at *
  generalize jacobiThetaOneTau (π * a / (2 * H.ω₁)) H.tau = Ta at *
  generalize cexp (H.eta 1 * (z + a) ^ 2 / (2 * H.ω₁)) = Ep at *
  generalize cexp (H.eta 1 * (z - a) ^ 2 / (2 * H.ω₁)) = Em at *
  generalize cexp (H.eta 1 * z ^ 2 / (2 * H.ω₁)) = Ez at *
  generalize cexp (H.eta 1 * a ^ 2 / (2 * H.ω₁)) = Ea at *
  field_simp
  linear_combination (-4 * Tp * Tm) * hE

/-- `θ₁(w ± π/2) = ±θ₂(w)`. -/
lemma p23R1_theta_shift_one (w τ : ℂ) :
    jacobiThetaOneTau (w + π / 2) τ = jacobiThetaTwoTau w τ ∧
      jacobiThetaOneTau (w - π / 2) τ = -jacobiThetaTwoTau w τ := by
  refine ⟨(jacobiThetaTwoTau_half_periods w τ).1.symm, ?_⟩
  have h1 := (jacobiThetaTwoTau_half_periods (w - π) τ).1
  have h2 := jacobiThetaTwoTau_add_lattice (w - π) τ 1 0
  norm_num at h2
  rw [show w - π + π / 2 = w - π / 2 by ring] at h1
  rw [← h1]; linear_combination h2

/-- `e^{iπτ/2} θ₁(w + πτ/2) θ₁(w - πτ/2) = θ₄(w)²`. -/
lemma p23R1_theta_shift_three (w τ : ℂ) :
    cexp (π * I * τ / 2) * (jacobiThetaOneTau (w + π * τ / 2) τ *
      jacobiThetaOneTau (w - π * τ / 2) τ) = jacobiThetaFourTau w τ ^ 2 := by
  have h1 := (jacobiThetaFourTau_half_periods w τ).2.1
  have h2 := (jacobiThetaFourTau_half_periods (-w) τ).2.1
  rw [jacobiThetaFourTau_neg] at h2
  have hodd := jacobiThetaOneTau_neg (w - π * τ / 2) τ
  rw [show -(w - π * τ / 2) = -w + π * τ / 2 by ring] at hodd
  rw [pow_two]
  nth_rewrite 1 [h1]; rw [h2, hodd, thetaMultiplierM, thetaMultiplierM]
  have e : cexp (I * w + π * I * τ / 4) * cexp (I * -w + π * I * τ / 4) = cexp (π * I * τ / 2) := by
    rw [← exp_add]; congr 1; ring
  have hI : I ^ 2 = -1 := I_sq
  linear_combination (jacobiThetaOneTau (w + π * τ / 2) τ * jacobiThetaOneTau (w - π * τ / 2) τ *
    I ^ 2) * e + (cexp (π * I * τ / 2) * jacobiThetaOneTau (w + π * τ / 2) τ *
    jacobiThetaOneTau (w - π * τ / 2) τ) * hI

/-- `e^{iπτ/2} θ₁(w + c) θ₁(w - c) = -θ₃(w)²`, `c = π/2 + πτ/2`. -/
lemma p23R1_theta_shift_two (w τ : ℂ) :
    cexp (π * I * τ / 2) * (jacobiThetaOneTau (w + (π / 2 + π * τ / 2)) τ *
      jacobiThetaOneTau (w - (π / 2 + π * τ / 2)) τ) = -jacobiThetaThreeTau w τ ^ 2 := by
  have h1 := (jacobiThetaThreeTau_half_periods w τ).2.2
  have h2 := (jacobiThetaThreeTau_half_periods (-w) τ).2.2
  rw [jacobiThetaThreeTau_neg] at h2
  have hodd := jacobiThetaOneTau_neg (w - (π / 2 + π * τ / 2)) τ
  rw [show -(w - (π / 2 + π * τ / 2)) = -w + π / 2 + π * τ / 2 by ring] at hodd
  rw [show w + (π / 2 + π * τ / 2) = w + π / 2 + π * τ / 2 by ring, pow_two]
  nth_rewrite 1 [h1]; rw [h2, hodd, thetaMultiplierM, thetaMultiplierM]
  have e : cexp (I * w + π * I * τ / 4) * cexp (I * -w + π * I * τ / 4) = cexp (π * I * τ / 2) := by
    rw [← exp_add]; congr 1; ring
  linear_combination (-(jacobiThetaOneTau (w + π / 2 + π * τ / 2) τ *
    jacobiThetaOneTau (w - (π / 2 + π * τ / 2)) τ)) * e

/-- 23.6.5 (helper form). -/
theorem p23R1_wp_sub_e_one {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 1 =
      (π * jacobiThetaThreeTau 0 H.tau * jacobiThetaFourTau 0 H.tau *
          jacobiThetaTwoTau (π * z / (2 * H.ω₁)) H.tau /
        (2 * H.ω₁ * jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau)) ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have ha : H.ω₁ ∉ H.lattice := H.halfPeriod_notMem (j := 1) (by simp)
  have h := H.p23R1_wp_sub_theta hz ha
  rw [show π * H.ω₁ / (2 * H.ω₁) = π / 2 by field_simp, (p23R1_theta_shift_one _ _).1,
    (p23R1_theta_shift_one _ _).2, show (π : ℂ) / 2 = 0 + π / 2 by ring,
    (p23R1_theta_shift_one _ _).1, jacobiThetaOneDerivNullTau_eq_mul H.tau_im_pos] at h
  have hθz : jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau ≠ 0 := by
    intro h0; apply hz; apply (H.p23R1_thetaSigma_eq_zero_iff z).mp
    simp only [p23R1_thetaSigma, h0, mul_zero, zero_div]
  have h2 := (jacobiThetaNullTau_ne_zero H.tau_im_pos).1
  rw [HalfPeriods.e, halfPeriod_one, h]
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at h2 ⊢
  field_simp
  ring

/-- 23.6.7 (helper form). -/
theorem p23R1_wp_sub_e_three {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 3 =
      (π * jacobiThetaTwoTau 0 H.tau * jacobiThetaThreeTau 0 H.tau *
          jacobiThetaFourTau (π * z / (2 * H.ω₁)) H.tau /
        (2 * H.ω₁ * jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau)) ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have ha : H.ω₃ ∉ H.lattice := H.halfPeriod_notMem (j := 3) (by simp)
  have h := H.p23R1_wp_sub_theta hz ha
  rw [show π * H.ω₃ / (2 * H.ω₁) = π * H.tau / 2 by rw [HalfPeriods.tau]; field_simp,
    jacobiThetaOneDerivNullTau_eq_mul H.tau_im_pos] at h
  have s1 := p23R1_theta_shift_three (π * z / (2 * H.ω₁)) H.tau
  have s0 := p23R1_theta_shift_three 0 H.tau
  rw [zero_add, zero_sub, jacobiThetaOneTau_neg] at s0
  have hθz : jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau ≠ 0 := by
    intro h0; apply hz; apply (H.p23R1_thetaSigma_eq_zero_iff z).mp
    simp only [p23R1_thetaSigma, h0, mul_zero, zero_div]
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4 h
  have hb : jacobiThetaOneTau (π * H.tau / 2) H.tau ≠ 0 := by
    intro h0; rw [h0] at s0; simp at s0; exact n4 (by simpa using s0.symm)
  have hE := exp_ne_zero (π * I * H.tau / 2)
  rw [HalfPeriods.e, halfPeriod_three, h]
  generalize jacobiThetaOneTau (π * z / (2 * H.ω₁) + π * H.tau / 2) H.tau = A at *
  generalize jacobiThetaOneTau (π * z / (2 * H.ω₁) - π * H.tau / 2) H.tau = B at *
  generalize jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau = T at *
  generalize jacobiThetaOneTau (π * H.tau / 2) H.tau = Tb at *
  generalize cexp (π * I * H.tau / 2) = E at *
  generalize jacobiThetaFourTau (π * z / (2 * H.ω₁)) H.tau = F at *
  field_simp
  linear_combination (4 * A * B) * s0 + (4 * Tb ^ 2) * s1

/-- 23.6.6 (helper form). -/
theorem p23R1_wp_sub_e_two {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 2 =
      (π * jacobiThetaTwoTau 0 H.tau * jacobiThetaFourTau 0 H.tau *
          jacobiThetaThreeTau (π * z / (2 * H.ω₁)) H.tau /
        (2 * H.ω₁ * jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau)) ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have ha : H.ω₂ ∉ H.lattice := H.halfPeriod_notMem (j := 2) (by simp)
  have h := H.p23R1_wp_sub_theta hz ha
  rw [show π * H.ω₂ / (2 * H.ω₁) = -(π / 2 + π * H.tau / 2) by
      rw [HalfPeriods.tau, HalfPeriods.ω₂]; field_simp; ring,
    sub_neg_eq_add, ← sub_eq_add_neg, jacobiThetaOneTau_neg,
    jacobiThetaOneDerivNullTau_eq_mul H.tau_im_pos] at h
  have s1 := p23R1_theta_shift_two (π * z / (2 * H.ω₁)) H.tau
  have s0 := p23R1_theta_shift_two 0 H.tau
  rw [zero_add, zero_sub, jacobiThetaOneTau_neg] at s0
  have hθz : jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau ≠ 0 := by
    intro h0; apply hz; apply (H.p23R1_thetaSigma_eq_zero_iff z).mp
    simp only [p23R1_thetaSigma, h0, mul_zero, zero_div]
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4 h
  have hb : jacobiThetaOneTau (π / 2 + π * H.tau / 2) H.tau ≠ 0 := by
    intro h0; rw [h0] at s0
    have : jacobiThetaThreeTau 0 H.tau ^ 2 = 0 := by linear_combination s0
    exact n3 (pow_eq_zero_iff two_ne_zero |>.mp this)
  rw [HalfPeriods.e, halfPeriod_two, h]
  generalize jacobiThetaOneTau (π * z / (2 * H.ω₁) + (π / 2 + π * H.tau / 2)) H.tau = A at *
  generalize jacobiThetaOneTau (π * z / (2 * H.ω₁) - (π / 2 + π * H.tau / 2)) H.tau = B at *
  generalize jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau = T at *
  generalize jacobiThetaOneTau (π / 2 + π * H.tau / 2) H.tau = Tb at *
  generalize cexp (π * I * H.tau / 2) = E at *
  generalize jacobiThetaThreeTau (π * z / (2 * H.ω₁)) H.tau = F at *
  field_simp
  linear_combination (-4 * A * B) * s0 + (-4 * Tb ^ 2) * s1

/-- `e₁ - e₃ = (π/(2ω₁))² θ₃⁴` and `e₁ - e₂ = (π/(2ω₁))² θ₄⁴`. -/
theorem p23R1_e_diff :
    H.e 1 - H.e 3 = (π / (2 * H.ω₁)) ^ 2 * jacobiThetaThreeTau 0 H.tau ^ 4 ∧
      H.e 1 - H.e 2 = (π / (2 * H.ω₁)) ^ 2 * jacobiThetaFourTau 0 H.tau ^ 4 := by
  have hω := H.ω₁_ne_zero
  have ha : H.ω₁ ∉ H.lattice := H.halfPeriod_notMem (j := 1) (by simp)
  have e1 : H.e 1 = H.weierstrassP H.ω₁ := rfl
  have hw : π * H.ω₁ / (2 * H.ω₁) = 0 + π / 2 := by rw [zero_add]; field_simp
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  have t1 : jacobiThetaOneTau (0 + π / 2) H.tau = jacobiThetaTwoTau 0 H.tau :=
    (p23R1_theta_shift_one _ _).1
  have t4 : jacobiThetaFourTau (0 + π / 2) H.tau = jacobiThetaThreeTau 0 H.tau :=
    (jacobiThetaThreeTau_half_periods 0 H.tau).1.symm
  have t3 : jacobiThetaThreeTau (0 + π / 2) H.tau = jacobiThetaFourTau 0 H.tau :=
    (jacobiThetaFourTau_half_periods 0 H.tau).1.symm
  constructor
  · rw [e1, p23R1_wp_sub_e_three H ha, hw, t1, t4]; field_simp
  · rw [e1, p23R1_wp_sub_e_two H ha, hw, t1, t3]; field_simp

/-- 23.6.2 (helper form). -/
lemma p23R1_e_one_theta :
    H.e 1 = π ^ 2 / (12 * H.ω₁ ^ 2) *
      (jacobiThetaTwoTau 0 H.tau ^ 4 + 2 * jacobiThetaFourTau 0 H.tau ^ 4) := by
  obtain ⟨d3, d2⟩ := H.p23R1_e_diff
  have hs := H.e_sum
  have hj := jacobiThetaNull_fourth_power H.tau H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at hj
  have hω := H.ω₁_ne_zero
  field_simp at d3 d2 ⊢
  linear_combination d3 + d2 + 4 * H.ω₁ ^ 2 * hs + π ^ 2 * hj

/-- DLMF 23.6.2: `e₁ = π²/(12ω₁²) (θ₂⁴(0,q) + 2θ₄⁴(0,q))`. -/
@[dlmf 23.6.E2]
theorem e_one_eq_theta :
    H.e 1 = π ^ 2 / (12 * H.ω₁ ^ 2) *
      (jacobiThetaTwoTau 0 H.tau ^ 4 + 2 * jacobiThetaFourTau 0 H.tau ^ 4) := by
  exact H.p23R1_e_one_theta

/-- DLMF 23.6.3: `e₂ = π²/(12ω₁²) (θ₂⁴(0,q) - θ₄⁴(0,q))`. -/
@[dlmf 23.6.E3]
theorem e_two_eq_theta :
    H.e 2 = π ^ 2 / (12 * H.ω₁ ^ 2) *
      (jacobiThetaTwoTau 0 H.tau ^ 4 - jacobiThetaFourTau 0 H.tau ^ 4) := by
  have := H.p23R1_e_one_theta
  have d := H.p23R1_e_diff.2
  have hj := jacobiThetaNull_fourth_power H.tau H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at hj
  have hω := H.ω₁_ne_zero
  field_simp at this d ⊢
  linear_combination this - 3 * d

/-- DLMF 23.6.4: `e₃ = -π²/(12ω₁²) (2θ₂⁴(0,q) + θ₄⁴(0,q))`. -/
@[dlmf 23.6.E4]
theorem e_three_eq_theta :
    H.e 3 = -(π ^ 2 / (12 * H.ω₁ ^ 2)) *
      (2 * jacobiThetaTwoTau 0 H.tau ^ 4 + jacobiThetaFourTau 0 H.tau ^ 4) := by
  have := H.p23R1_e_one_theta
  have d := H.p23R1_e_diff.1
  have hj := jacobiThetaNull_fourth_power H.tau H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at hj
  have hω := H.ω₁_ne_zero
  field_simp at this d ⊢
  linear_combination this - 3 * d - 3 * π ^ 2 * hj

/-- DLMF 23.6.5: `℘(z) - e₁ = (π θ₃(0,q) θ₄(0,q) θ₂(πz/(2ω₁),q) / (2ω₁ θ₁(πz/(2ω₁),q)))²`,
`z ∉ 𝕃`. -/
@[dlmf 23.6.E5]
theorem weierstrassP_sub_e_one_eq_theta {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 1 =
      (π * jacobiThetaThreeTau 0 H.tau * jacobiThetaFourTau 0 H.tau *
          jacobiThetaTwoTau (π * z / (2 * H.ω₁)) H.tau /
        (2 * H.ω₁ * jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau)) ^ 2 := by
  exact H.p23R1_wp_sub_e_one hz

/-- DLMF 23.6.6: `℘(z) - e₂ = (π θ₂(0,q) θ₄(0,q) θ₃(πz/(2ω₁),q) / (2ω₁ θ₁(πz/(2ω₁),q)))²`,
`z ∉ 𝕃`. -/
@[dlmf 23.6.E6]
theorem weierstrassP_sub_e_two_eq_theta {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 2 =
      (π * jacobiThetaTwoTau 0 H.tau * jacobiThetaFourTau 0 H.tau *
          jacobiThetaThreeTau (π * z / (2 * H.ω₁)) H.tau /
        (2 * H.ω₁ * jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau)) ^ 2 := by
  exact H.p23R1_wp_sub_e_two hz

/-- DLMF 23.6.7: `℘(z) - e₃ = (π θ₂(0,q) θ₃(0,q) θ₄(πz/(2ω₁),q) / (2ω₁ θ₁(πz/(2ω₁),q)))²`,
`z ∉ 𝕃`. -/
@[dlmf 23.6.E7]
theorem weierstrassP_sub_e_three_eq_theta {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 3 =
      (π * jacobiThetaTwoTau 0 H.tau * jacobiThetaThreeTau 0 H.tau *
          jacobiThetaFourTau (π * z / (2 * H.ω₁)) H.tau /
        (2 * H.ω₁ * jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau)) ^ 2 := by
  exact H.p23R1_wp_sub_e_three hz

/-- DLMF 23.6.8: `η₁ = -(π²/(12ω₁)) θ₁'''(0,q)/θ₁'(0,q)`. -/
@[dlmf 23.6.E8]
theorem eta_one_eq_theta :
    H.eta 1 = -(π ^ 2 / (12 * H.ω₁)) *
      (thetaOneTripleDerivNull H.tau / jacobiThetaOneDerivNullTau H.tau) := by
  exact H.p23R1_eta_one_theta

/-- DLMF 23.6.9: `σ(z) = 2ω₁ exp(η₁z²/(2ω₁)) θ₁(πz/(2ω₁),q)/(π θ₁'(0,q))`, `z ∈ ℂ`. -/
@[dlmf 23.6.E9]
theorem weierstrassSigma_eq_theta (z : ℂ) :
    H.weierstrassSigma z = 2 * H.ω₁ * cexp (H.eta 1 * z ^ 2 / (2 * H.ω₁)) *
      jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau / (π * jacobiThetaOneDerivNullTau H.tau) := by
  exact H.p23R1_sigma_theta.1 z

/-- DLMF 23.6.10: `σ(ω₁) = 2ω₁ exp(η₁ω₁/2) θ₂(0,q)/(π θ₁'(0,q))`. -/
@[dlmf 23.6.E10]
theorem weierstrassSigma_ω₁_eq_theta :
    H.weierstrassSigma H.ω₁ = 2 * H.ω₁ * cexp (H.eta 1 * H.ω₁ / 2) * jacobiThetaTwoTau 0 H.tau /
      (π * jacobiThetaOneDerivNullTau H.tau) := by
  have hω := H.ω₁_ne_zero
  rw [H.p23R1_sigma_theta.1, p23R1_thetaSigma,
    show π * H.ω₁ / (2 * H.ω₁) = 0 + π / 2 by rw [zero_add]; field_simp,
    (p23R1_theta_shift_one _ _).1,
    show H.eta 1 * H.ω₁ ^ 2 / (2 * H.ω₁) = H.eta 1 * H.ω₁ / 2 by field_simp]

/-- DLMF 23.6.11: `σ(ω₂) = -2ω₁ exp(η₁(ω₁τ² + ω₃ - ω₂)/2) θ₃(0,q)/(π q^{1/4} θ₁'(0,q))`,
with `q^{1/4} = e^{iπτ/4}`. -/
@[dlmf 23.6.E11]
theorem weierstrassSigma_ω₂_eq_theta :
    H.weierstrassSigma H.ω₂ = -(2 * H.ω₁) *
      cexp (H.eta 1 * (H.ω₁ * H.tau ^ 2 + H.ω₃ - H.ω₂) / 2) * jacobiThetaThreeTau 0 H.tau /
        (π * cexp (π * I * H.tau / 4) * jacobiThetaOneDerivNullTau H.tau) := by
  have hω := H.ω₁_ne_zero
  have hD := H.p23R1_thetaOneDeriv_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have a := (jacobiThetaThreeTau_half_periods 0 H.tau).2.2
  rw [H.p23R1_sigma_theta.1, p23R1_thetaSigma,
    show π * H.ω₂ / (2 * H.ω₁) = -(0 + π / 2 + π * H.tau / 2) by
      rw [HalfPeriods.tau, HalfPeriods.ω₂]; field_simp; ring,
    show H.eta 1 * H.ω₂ ^ 2 / (2 * H.ω₁) = H.eta 1 * (H.ω₁ * H.tau ^ 2 + H.ω₃ - H.ω₂) / 2 by
      rw [HalfPeriods.tau, HalfPeriods.ω₂]; field_simp; ring,
    jacobiThetaOneTau_neg, a, thetaMultiplierM, mul_zero, zero_add]
  have he := exp_ne_zero (π * I * H.tau / 4)
  simp only [mul_zero, zero_add]
  field_simp

/-- DLMF 23.6.12: `σ(ω₃) = 2iω₁ exp(η₁ω₁τ²/2) θ₄(0,q)/(π q^{1/4} θ₁'(0,q))`, with
`q^{1/4} = e^{iπτ/4}`. -/
@[dlmf 23.6.E12]
theorem weierstrassSigma_ω₃_eq_theta :
    H.weierstrassSigma H.ω₃ = 2 * I * H.ω₁ * cexp (H.eta 1 * H.ω₁ * H.tau ^ 2 / 2) *
      jacobiThetaFourTau 0 H.tau /
        (π * cexp (π * I * H.tau / 4) * jacobiThetaOneDerivNullTau H.tau) := by
  have hω := H.ω₁_ne_zero
  have hD := H.p23R1_thetaOneDeriv_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have b := (jacobiThetaFourTau_half_periods 0 H.tau).2.1
  rw [H.p23R1_sigma_theta.1, p23R1_thetaSigma,
    show π * H.ω₃ / (2 * H.ω₁) = 0 + π * H.tau / 2 by rw [HalfPeriods.tau, zero_add]; field_simp,
    show H.eta 1 * H.ω₃ ^ 2 / (2 * H.ω₁) = H.eta 1 * H.ω₁ * H.tau ^ 2 / 2 by
      rw [HalfPeriods.tau]; field_simp, b, thetaMultiplierM, mul_zero, zero_add]
  have he := exp_ne_zero (π * I * H.tau / 4)
  simp only [mul_zero, zero_add]
  field_simp
  rw [show (I : ℂ) ^ 2 = -1 from I_sq]
  ring

end HalfPeriods
end DLMF.Weierstrass
end
end
