/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.Basic
public import DLMF.Legendre.ZeroTools

/-!
# The spheroidal differential equation (DLMF §30.2, §30.3(i), §30.12)

Statement acquisition from NIST DLMF (version 1.2.8), checked 2026-10-26. Admitted statements
are not completed proofs; see `DLMF30Acquisition.md`.

* §30.2(i): the singularities of 30.2.1 (regular at `±1` with exponents `±μ/2`, irregular of
  rank 1 at `∞`), stated through the indicial equation at `z = 1`;
* §30.2(ii): the Liouville normal form 30.2.2 under 30.2.3, and the form 30.2.4 in `ζ = γz`;
* §30.2(iii): the special cases `γ = 0` (associated Legendre equation 14.2.2, spherical Bessel
  equation 10.47.1) and `μ² = 1/4` (Mathieu's equation 28.2.1);
* §30.3(i): `(1-z²)^{m/2} g(z)` solves 30.2.1 with `μ = m` iff `g` solves the factor equation;
* §30.12: the generalized equations 30.12.1 and 30.12.2 reduce to 30.2.1 at `α = 0` (proved).
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Spheroidal

/-! ### Calculus helpers (proof round P1, agent S30) -/

/-- Identity under the stated parameter and domain assumptions: `z * ((n : ℂ) * z ^ (n - 1)) = n *
z ^ n`. -/
private lemma p1s_pow_deriv_aux (n : ℕ) (z : ℂ) :
    z * ((n : ℂ) * z ^ (n - 1)) = n * z ^ n := by
  rcases n with _ | n
  · simp
  · simp [pow_succ]; ring

/-- Identity under the stated parameter and domain assumptions: `z ^ 2 * ((n : ℂ) * (((n - 1 : ℕ)
: ℂ) * z ^ (n - 1 - 1))) = n * (n - 1) * z ^ n`. -/
private lemma p1s_pow_deriv2_aux (n : ℕ) (z : ℂ) :
    z ^ 2 * ((n : ℂ) * (((n - 1 : ℕ) : ℂ) * z ^ (n - 1 - 1))) = n * (n - 1) * z ^ n := by
  rcases n with _ | _ | n
  · simp
  · simp
  · simp [pow_succ]; ring

/-- On an open set avoiding `±1`, a solution of 30.2.1 has a differentiable derivative, with
`(1-z²) w'' = 2z w' - (λ + γ²(1-z²) - μ²/(1-z²)) w`. -/
lemma p1s_hasDerivAt_deriv {lam γ2 μ : ℂ} {U : Set ℂ} {w : ℂ → ℂ} (hU : IsOpen U)
    (hU1 : ∀ z ∈ U, 1 - z ^ 2 ≠ 0) (hw : IsSpheroidalSolutionOn lam γ2 μ U w) {z : ℂ}
    (hz : z ∈ U) :
    HasDerivAt (deriv w) ((2 * z * deriv w z -
      (lam + γ2 * (1 - z ^ 2) - μ ^ 2 / (1 - z ^ 2)) * w z) / (1 - z ^ 2)) z := by
  have hq : HasDerivAt (fun t : ℂ => 1 - t ^ 2) (-(2 * z)) z := by
    simpa using ((hasDerivAt_pow 2 z).const_sub 1)
  have h := (hw.hasDerivAt z hz).div hq (hU1 z hz)
  have hev : (fun t => (1 - t ^ 2) * deriv w t / (1 - t ^ 2)) =ᶠ[𝓝 z] deriv w := by
    filter_upwards [hU.mem_nhds hz] with t ht
    field_simp [hU1 t ht]
  refine (h.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  have := hU1 z hz
  field_simp
  ring

/-- Derivative of `(1-x²)^{m/2}` on `(-1, 1)`. -/
theorem p1s_hasDerivAt_weight (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => (1 - x ^ 2) ^ ((m : ℝ) / 2))
      (-((m : ℝ) * x) / (1 - x ^ 2) * (1 - x ^ 2) ^ ((m : ℝ) / 2)) x := by
  have hpos : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hb : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1)
  refine (hb.rpow_const (p := (m : ℝ) / 2) (Or.inl hpos.ne')).congr_deriv ?_
  rw [Real.rpow_sub hpos, Real.rpow_one]
  field_simp

/-- For entire `g`, the real part along `ℝ` has derivative `(g' x).re`. -/
theorem p1s_hasDerivAt_re {g : ℂ → ℂ} (hg : Differentiable ℂ g) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (g t).re) (deriv g x).re x :=
  (hg x).hasDerivAt.real_of_complex

/-- The derivative of an entire function is entire. -/
theorem p1s_differentiable_deriv {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (deriv g) := fun z => ((hg.analyticAt z).deriv).differentiableAt

/-- An entire function real on `ℝ` has real derivative on `ℝ`. -/
lemma p1s_deriv_im_eq_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hreal : ∀ x : ℝ, (g x).im = 0) (x : ℝ) : (deriv g x).im = 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (g t).im) (deriv g x).im x := by
    have := (hg x).hasDerivAt
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (this.comp_ofReal)
    simpa only [Function.comp_def, Complex.imCLM_apply] using h
  have h0 : HasDerivAt (fun t : ℝ => (g t).im) 0 x := by
    simp only [hreal]; exact hasDerivAt_const x 0
  exact h1.unique h0

/-- An entire function vanishing on `(-1, 1)` vanishes identically. -/
theorem p1s_eq_zero_of_Ioo {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h0 : ∀ x ∈ Ioo (-1 : ℝ) 1, F x = 0) : ∀ z, F z = 0 := by
  have hA : AnalyticOnNhd ℂ F univ := fun z _ => hF.analyticAt z
  have hfr : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F z = 0 := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
    refine ht.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num))] with x hx
    exact h0 x hx
  intro z
  exact hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ 0) hfr
    (mem_univ z)

/-- Identity under the stated parameter and domain assumptions: `IsSpheroidalSolutionOn lam γ2 m U
(fun z => h z * g z)`. -/
theorem p1s_isSpheroidalSolutionOn_mul_factor {m : ℕ} {γ2 lam : ℝ} {g : ℂ → ℂ}
    (hF : IsSpheroidalFactor m γ2 lam g) {U : Set ℂ} (hU : IsOpen U)
    (hU1 : ∀ z ∈ U, 1 - z ^ 2 ≠ 0) {h : ℂ → ℂ}
    (hh : ∀ z ∈ U, HasDerivAt h (-((m : ℂ) * z) / (1 - z ^ 2) * h z) z) :
    IsSpheroidalSolutionOn lam γ2 m U (fun z => h z * g z) := by
  have hd := hF.differentiable
  have hd1 : Differentiable ℂ (deriv g) := fun z => ((hd.analyticAt z).deriv).differentiableAt
  have hf : ∀ z ∈ U, HasDerivAt (fun z => h z * g z)
      (-((m : ℂ) * z) / (1 - z ^ 2) * h z * g z + h z * deriv g z) z :=
    fun z hz => (hh z hz).mul (hd z).hasDerivAt
  have hev : ∀ z ∈ U, (fun t => (1 - t ^ 2) * deriv (fun z => h z * g z) t) =ᶠ[𝓝 z]
      fun t => h t * ((1 - t ^ 2) * deriv g t - m * t * g t) := by
    intro z hz
    filter_upwards [hU.mem_nhds hz] with t ht
    rw [(hf t ht).deriv]
    have := hU1 t ht
    field_simp
    ring
  refine ⟨fun z hz => (hf z hz).differentiableAt, fun z hz => ?_⟩
  have hq : HasDerivAt (fun t : ℂ => 1 - t ^ 2) (-(2 * z)) z := by
    simpa using ((hasDerivAt_pow 2 z).const_sub 1)
  have hl : HasDerivAt (fun t : ℂ => (m : ℂ) * t) m z := by
    simpa using (hasDerivAt_id z).const_mul (m : ℂ)
  have := (hh z hz).mul ((hq.mul (hd1 z).hasDerivAt).sub (hl.mul (hd z).hasDerivAt))
  refine ((this.congr_of_eventuallyEq (hev z hz))).congr_deriv ?_
  have h1 := hU1 z hz
  have hode := hF.ode z
  simp only [Pi.mul_apply, Pi.sub_apply]
  field_simp
  linear_combination (1 - z ^ 2) * h z * hode

/-! ### §30.2(i) Singularities -/

/-- **Regular singularity at `z = 1`** (DLMF §30.2(i)): multiplying 30.2.1 by `(1-z²)` gives
`(1-z²)² w'' - 2z(1-z²) w' + (λ(1-z²) + γ²(1-z²)² - μ²) w = 0`, whose indicial equation at
`z = 1` (with `1 - z² = (1-z)(1+z)`, leading factor `4(z-1)²`) is `4ρ² - μ² = 0`, so the exponents
are `±μ/2` (proved: the roots of the indicial polynomial). -/
@[dlmf 30.2.i]
theorem spheroidal_indicial_exponents (μ ρ : ℂ) :
    4 * ρ * (ρ - 1) + 4 * ρ - μ ^ 2 = 0 ↔ ρ = μ / 2 ∨ ρ = -(μ / 2) := by
  constructor
  · intro h
    have h' : (ρ - μ / 2) * (ρ + μ / 2) = 0 := by linear_combination h / 4
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  · rintro (rfl | rfl) <;> ring

/-- **Irregular singularity at infinity** (DLMF §30.2(i)): for `γ ≠ 0`, 30.2.1 has an irregular
singular point of rank 1 at `z = ∞`: every nonzero solution on a neighbourhood of `∞` grows or
decays like `exp(±iγz) z^{ρ}` there, so `w(z) e^{∓iγz}` has at most polynomial behaviour along
suitable rays. Stated (admitted) as the existence of the two formal exponents: there are
solutions on `{|z| > 1} ∖ (-∞, -1]` with `w(z) ∼ e^{±iγz}/z` as `z → +∞` along the reals. -/
@[dlmf 30.2.i]
theorem spheroidal_irregular_infinity (lam μ γ : ℂ) (hγ : γ ≠ 0) :
    ∀ s : ℂ, s = 1 ∨ s = -1 → ∃ w : ℂ → ℂ,
      IsSpheroidalSolutionOn lam (γ ^ 2) μ {z : ℂ | 1 < ‖z‖ ∧ z + 1 ∈ slitPlane} w ∧
      Tendsto (fun x : ℝ => (x : ℂ) * Complex.exp (-(s * I * γ * x)) * w x) atTop (𝓝 1) := by
  sorry

/-! ### §30.2(ii) Other forms -/

/-- **The Liouville normal form** (DLMF 30.2.2, 30.2.3): if `w` solves 30.2.1 on an open set
`U`, then `g(t) = (sin t)^{1/2} w(cos t)` (so `w(z) = (1-z²)^{-1/4} g(t)` with `z = cos t`)
solves 30.2.2 on every open set `T` of `t` with `cos t ∈ U` and `sin t` in the slit plane
(e.g. a neighbourhood of a subinterval of `(0, π)`). -/
@[dlmf 30.2.E2, dlmf 30.2.E3]
theorem isSpheroidalLiouvilleSolution_of_isSpheroidalSolutionOn {lam γ2 μ : ℂ} {U T : Set ℂ}
    {w : ℂ → ℂ} (hU : IsOpen U) (hT : IsOpen T) (hw : IsSpheroidalSolutionOn lam γ2 μ U w)
    (hTU : ∀ t ∈ T, Complex.cos t ∈ U) (hsin : ∀ t ∈ T, Complex.sin t ∈ slitPlane) :
    IsSpheroidalLiouvilleSolution lam γ2 μ T
      (fun t => Complex.sin t ^ (1 / 2 : ℂ) * w (Complex.cos t)) := by
  set U' : Set ℂ := U ∩ {z | 1 - z ^ 2 ≠ 0}
  have hU' : IsOpen U' := hU.inter (isOpen_ne_fun (by fun_prop) (by fun_prop))
  have hU1 : ∀ z ∈ U', 1 - z ^ 2 ≠ 0 := fun z hz => hz.2
  have hw' : IsSpheroidalSolutionOn lam γ2 μ U' w :=
    ⟨fun z hz => hw.differentiableAt z hz.1, fun z hz => hw.hasDerivAt z hz.1⟩
  have hs0 : ∀ t ∈ T, Complex.sin t ≠ 0 := fun t ht => slitPlane_ne_zero (hsin t ht)
  have hTU' : ∀ t ∈ T, Complex.cos t ∈ U' := by
    intro t ht
    refine ⟨hTU t ht, ?_⟩
    show 1 - Complex.cos t ^ 2 ≠ 0
    rw [show 1 - Complex.cos t ^ 2 = Complex.sin t ^ 2 by
      linear_combination -Complex.sin_sq_add_cos_sq t]
    exact pow_ne_zero 2 (hs0 t ht)
  set Sq : ℂ → ℂ := fun t => Complex.sin t ^ (1 / 2 : ℂ)
  have hS : ∀ t ∈ T, HasDerivAt Sq (Sq t * (Complex.cos t / (2 * Complex.sin t))) t := by
    intro t ht
    have h := (Complex.hasDerivAt_sin t).cpow_const (c := (1 / 2 : ℂ)) (hsin t ht)
    refine h.congr_deriv ?_
    rw [Complex.cpow_sub _ _ (hs0 t ht), Complex.cpow_one]
    simp only [Sq]
    field_simp
  have hW : ∀ t ∈ T, HasDerivAt (fun t => w (Complex.cos t))
      (deriv w (Complex.cos t) * -Complex.sin t) t := fun t ht =>
    (hw.differentiableAt _ (hTU t ht)).hasDerivAt.comp t (Complex.hasDerivAt_cos t)
  have hg1 : ∀ t ∈ T, HasDerivAt (fun t => Sq t * w (Complex.cos t))
      (Sq t * (Complex.cos t / (2 * Complex.sin t)) * w (Complex.cos t) +
        Sq t * (deriv w (Complex.cos t) * -Complex.sin t)) t :=
    fun t ht => (hS t ht).mul (hW t ht)
  refine ⟨fun t ht => (hg1 t ht).differentiableAt, fun t ht => ?_⟩
  have hev : deriv (fun t => Sq t * w (Complex.cos t)) =ᶠ[𝓝 t] fun t =>
      Sq t * ((Complex.cos t / (2 * Complex.sin t)) * w (Complex.cos t) +
        deriv w (Complex.cos t) * -Complex.sin t) := by
    filter_upwards [hT.mem_nhds ht] with u hu
    rw [(hg1 u hu).deriv]; ring
  have hq : HasDerivAt (fun t => Complex.cos t / (2 * Complex.sin t))
      ((-Complex.sin t * (2 * Complex.sin t) - Complex.cos t * (2 * Complex.cos t)) /
        (2 * Complex.sin t) ^ 2) t :=
    (Complex.hasDerivAt_cos t).div ((Complex.hasDerivAt_sin t).const_mul 2)
      (mul_ne_zero two_ne_zero (hs0 t ht))
  have hW2 := (p1s_hasDerivAt_deriv hU' hU1 hw' (hTU' t ht)).comp t (Complex.hasDerivAt_cos t)
  have hall := (hS t ht).mul ((hq.mul (hW t ht)).add (hW2.mul (Complex.hasDerivAt_sin t).neg))
  refine (hall.congr_of_eventuallyEq hev).congr_deriv ?_
  have hc : Complex.cos t ^ 2 = 1 - Complex.sin t ^ 2 := by
    linear_combination Complex.sin_sq_add_cos_sq t
  have e1 : 1 - Complex.cos t ^ 2 = Complex.sin t ^ 2 := by rw [hc]; ring
  have := hs0 t ht
  simp only [Pi.mul_apply, Pi.add_apply, Pi.neg_apply, Function.comp_apply, e1, Sq]
  field_simp
  linear_combination (-4 * Complex.sin t ^ (1 / 2 : ℂ) * w (Complex.cos t)) * hc

/-- **The form in `ζ = γz`** (DLMF 30.2.4): if `w` solves 30.2.1 on an open set `U` avoiding
`±1` and `γ ≠ 0`, then `ζ ↦ w(ζ/γ)` solves 30.2.4 (with `γ2 = γ²`) on `γU`. -/
@[dlmf 30.2.E4]
theorem isSpheroidalZetaSolution_of_isSpheroidalSolutionOn {lam μ γ : ℂ} {U : Set ℂ}
    {w : ℂ → ℂ} (hγ : γ ≠ 0) (hU : IsOpen U) (hU1 : ∀ z ∈ U, 1 - z ^ 2 ≠ 0)
    (hw : IsSpheroidalSolutionOn lam (γ ^ 2) μ U w) :
    IsSpheroidalZetaSolution lam (γ ^ 2) μ ((fun z => γ * z) '' U) (fun ζ => w (ζ / γ)) := by
  have hv : (fun ζ => w (ζ / γ)) = fun ζ => w (γ⁻¹ * ζ) := by
    funext ζ; rw [div_eq_inv_mul]
  have hD : deriv (fun ζ => w (ζ / γ)) = fun ζ => γ⁻¹ * deriv w (ζ / γ) := by
    funext ζ; rw [hv, deriv_comp_mul_left, smul_eq_mul, div_eq_inv_mul]
  have hlin : ∀ ζ : ℂ, HasDerivAt (fun ζ : ℂ => ζ / γ) γ⁻¹ ζ := fun ζ => by
    simpa [div_eq_inv_mul] using (hasDerivAt_id ζ).div_const γ
  have hdiff : ∀ ζ ∈ (fun z => γ * z) '' U, HasDerivAt (fun ζ => w (ζ / γ))
      (deriv w (ζ / γ) * γ⁻¹) ζ := by
    rintro ζ ⟨z, hz, rfl⟩
    have : γ * z / γ = z := by field_simp
    have h1 := (hw.differentiableAt z hz).hasDerivAt
    rw [← this] at h1
    exact h1.comp (γ * z) (hlin _)
  have hdiff2 : ∀ ζ ∈ (fun z => γ * z) '' U, HasDerivAt (deriv fun ζ => w (ζ / γ))
      (γ⁻¹ * (((2 * (ζ / γ) * deriv w (ζ / γ) - (lam + γ ^ 2 * (1 - (ζ / γ) ^ 2) -
        μ ^ 2 / (1 - (ζ / γ) ^ 2)) * w (ζ / γ)) / (1 - (ζ / γ) ^ 2)) * γ⁻¹)) ζ := by
    rintro ζ ⟨z, hz, rfl⟩
    have : γ * z / γ = z := by field_simp
    have h1 := p1s_hasDerivAt_deriv hU hU1 hw hz
    rw [← this] at h1
    rw [hD]
    exact (h1.comp (γ * z) (hlin _)).const_mul _
  refine ⟨fun ζ hζ => (hdiff ζ hζ).differentiableAt,
    fun ζ hζ => (hdiff2 ζ hζ).differentiableAt, ?_⟩
  rintro ζ ⟨z, hz, rfl⟩
  rw [(hdiff2 _ ⟨z, hz, rfl⟩).deriv, hD]
  have e : γ * z / γ = z := by field_simp
  simp only [e]
  have h1 := hU1 z hz
  have h2 : (γ * z) ^ 2 - γ ^ 2 ≠ 0 := by
    rw [show (γ * z) ^ 2 - γ ^ 2 = -(γ ^ 2 * (1 - z ^ 2)) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hγ) h1)
  have h3 : z ^ 2 - 1 ≠ 0 := fun h => h1 (by linear_combination -h)
  rw [show (γ * z) ^ 2 - γ ^ 2 = γ ^ 2 * (z ^ 2 - 1) by ring]
  field_simp
  ring

/-! ### §30.2(iii) Special cases -/

/-- **`γ = 0`: the associated Legendre equation** (DLMF §30.2(iii), 14.2.2): the Ferrers function
`𝖯^m_n(x)` solves 30.2.1 on `(-1, 1)` with `γ = 0`, `λ = n(n+1)`, `μ = m`. -/
@[dlmf 30.2.iii]
theorem isSpheroidalSolutionReal_ferrersP (n m : ℕ) :
    IsSpheroidalSolutionReal ((n : ℝ) * (n + 1)) 0 m
      (fun x => (DLMF.Legendre.ferrersP n m x).re) := by
  have key : ∀ x ∈ Ioo (-1 : ℝ) 1, _ := fun x hx =>
    DLMF.Legendre.lzt_ferrersP_sol (n : ℝ) (m : ℝ) hx
  simp only [Complex.ofReal_natCast] at key
  have hd : ∀ x ∈ Ioo (-1 : ℝ) 1, deriv (fun t => (DLMF.Legendre.ferrersP n m t).re) x =
      (deriv (DLMF.Legendre.ferrersP n m) x).re := fun x hx => (key x hx).1.deriv
  refine ⟨fun x hx => (key x hx).1.differentiableAt, fun x hx => ?_⟩
  have h2 := (key x hx).2
  refine (h2.congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  rw [hd t ht]

/-- **`μ² = 1/4`: Mathieu's equation** (DLMF §30.2(iii), 28.2.1): for `μ² = 1/4` the coefficient
of 30.2.2 is `λ + 1/4 + γ² sin²t = a - 2q cos 2t` with `a = λ + 1/4 + γ²/2`, `q = γ²/4`, so
30.2.2 is Mathieu's equation `g'' + (a - 2q cos 2t) g = 0` (proved). -/
@[dlmf 30.2.iii]
theorem spheroidalLiouville_coeff_mathieu (lam γ2 μ t : ℂ) (hμ : μ ^ 2 = 1 / 4) :
    lam + 1 / 4 + γ2 * Complex.sin t ^ 2 - (μ ^ 2 - 1 / 4) / Complex.sin t ^ 2 =
      (lam + 1 / 4 + γ2 / 2) - 2 * (γ2 / 4) * Complex.cos (2 * t) := by
  rw [hμ, sub_self, zero_div, sub_zero, Complex.cos_two_mul]
  linear_combination γ2 * Complex.sin_sq_add_cos_sq t

/-- **`μ² = 1/4`: Mathieu's equation** (DLMF §30.2(iii)): a solution of the Liouville form 30.2.2
with `μ² = 1/4` on `T` satisfies `g'' = (2q cos 2t - a) g` with `a = λ + 1/4 + γ²/2`, `q = γ²/4`
(proved). -/
@[dlmf 30.2.iii]
theorem IsSpheroidalLiouvilleSolution.mathieu {lam γ2 μ : ℂ} {T : Set ℂ} {g : ℂ → ℂ}
    (hg : IsSpheroidalLiouvilleSolution lam γ2 μ T g) (hμ : μ ^ 2 = 1 / 4) :
    ∀ t ∈ T, HasDerivAt (deriv g)
      ((2 * (γ2 / 4) * Complex.cos (2 * t) - (lam + 1 / 4 + γ2 / 2)) * g t) t := by
  intro t ht
  convert hg.hasDerivAt t ht using 1
  rw [spheroidalLiouville_coeff_mathieu lam γ2 μ t hμ]
  ring

/-- **`γ = 0` in 30.2.4: the spherical Bessel equation** (DLMF §30.2(iii), 10.47.1): with `γ = 0`
and `μ` arbitrary, 30.2.4 reads `ζ² w'' + 2ζ w' + (ζ² - λ) w = 0`, which for `λ = n(n+1)` is
satisfied by the spherical Bessel function `j_n` (`DLMF.sphericalJ`). -/
@[dlmf 30.2.iii]
theorem isSpheroidalZetaSolution_sphericalJ (n : ℕ) (μ : ℂ) :
    IsSpheroidalZetaSolution ((n : ℂ) * (n + 1)) 0 μ univ (DLMF.sphericalJ n) := by
  set b : ℂ := (n : ℂ) + 3 / 2
  set c : ℂ := Real.sqrt π / (2 : ℂ) ^ (n + 1)
  let F : ℕ → ℂ → ℂ := fun j => regularizedHGFun (∅ : Multiset ℂ) {b + j}
  have hF : ∀ j w, HasDerivAt (F j) (F (j + 1) w) w := by
    intro j w
    have := DLMF.Bessel.hasDerivAt_regularized0F1 (b + j) w
    simpa [F, add_assoc] using this
  have hu : ∀ z : ℂ, HasDerivAt (fun z : ℂ => -z ^ 2 / 4) (-z / 2) z := by
    intro z
    have := ((hasDerivAt_pow 2 z).neg.div_const 4)
    convert this using 1; push_cast; ring
  have hP : ∀ z : ℂ, HasDerivAt (fun z : ℂ => z ^ n) ((n : ℂ) * z ^ (n - 1)) z := by
    intro z; simpa using hasDerivAt_pow n z
  have hP' : ∀ z : ℂ, HasDerivAt (fun z : ℂ => (n : ℂ) * z ^ (n - 1))
      ((n : ℂ) * (((n - 1 : ℕ) : ℂ) * z ^ (n - 1 - 1))) z := by
    intro z; exact (by simpa using hasDerivAt_pow (n - 1) z : HasDerivAt _ _ z).const_mul _
  have hw : DLMF.sphericalJ n = fun z => c * (z ^ n * F 0 (-z ^ 2 / 4)) := by
    funext z; simp only [DLMF.sphericalJ, F, c, b]; simp; ring_nf
  have hd1 : ∀ z, HasDerivAt (DLMF.sphericalJ n)
      (c * ((n : ℂ) * z ^ (n - 1) * F 0 (-z ^ 2 / 4) +
        z ^ n * (F 1 (-z ^ 2 / 4) * (-z / 2)))) z := by
    intro z; rw [hw]
    exact ((hP z).mul ((hF 0 _).comp z (hu z))).const_mul c
  have hD1 : deriv (DLMF.sphericalJ n) = fun z => c * ((n : ℂ) * z ^ (n - 1) * F 0 (-z ^ 2 / 4) +
        z ^ n * (F 1 (-z ^ 2 / 4) * (-z / 2))) := funext fun z => (hd1 z).deriv
  have hm : ∀ z : ℂ, HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) z := by
    intro z; simpa using ((hasDerivAt_id z).neg.div_const 2)
  have hd2 : ∀ z, HasDerivAt (deriv (DLMF.sphericalJ n))
      (c * (((n : ℂ) * (((n - 1 : ℕ) : ℂ) * z ^ (n - 1 - 1)) * F 0 (-z ^ 2 / 4) +
          (n : ℂ) * z ^ (n - 1) * (F 1 (-z ^ 2 / 4) * (-z / 2))) +
        ((n : ℂ) * z ^ (n - 1) * (F 1 (-z ^ 2 / 4) * (-z / 2)) +
          z ^ n * (F 2 (-z ^ 2 / 4) * (-z / 2) * (-z / 2) + F 1 (-z ^ 2 / 4) * (-1 / 2))))) z := by
    intro z; rw [hD1]
    have h1 := ((hF 0 _).comp z (hu z))
    have h2 := (((hF 1 _).comp z (hu z))).mul (hm z)
    exact (((hP' z).mul h1).add ((hP z).mul h2)).const_mul c
  refine ⟨fun z _ => (hd1 z).differentiableAt, fun z _ => (hd2 z).differentiableAt,
    fun z _ => ?_⟩
  rw [(hd2 z).deriv, hD1, hw]
  have hode := DLMF.Bessel.regularized0F1_ode b (-z ^ 2 / 4)
  have e0 : deriv (regularizedHGFun (∅ : Multiset ℂ) {b}) = F 1 := by
    funext w; rw [DLMF.Bessel.deriv_regularized0F1]; simp [F]
  have e : deriv (F 1) = F 2 := by
    funext w; exact (hF 1 w).deriv
  rw [e0, e] at hode
  have a1 := p1s_pow_deriv_aux n z
  have a2 := p1s_pow_deriv2_aux n z
  have hF0 : regularizedHGFun (∅ : Multiset ℂ) {b} = F 0 := by simp [F]
  rw [hF0] at hode
  simp only [sub_zero, zero_mul, zero_div]
  linear_combination c * F 0 (-z ^ 2 / 4) * a2 - c * z ^ 2 * F 1 (-z ^ 2 / 4) * a1 +
    2 * c * F 0 (-z ^ 2 / 4) * a1 - c * z ^ n * z ^ 2 * hode

/-! ### §30.3(i) The entire factor -/

/-- **Bounded solutions and the factor equation** (DLMF §30.3(i)): on `(-1, 1)`, for real `λ`,
`γ²`, the function `(1-x²)^{m/2} g(x)` with `g` entire and real on `ℝ` solves 30.2.1 with `μ = m`
iff `g` solves `IsSpheroidalFactor` (the equation holds on `ℂ` by analytic continuation). -/
@[dlmf 30.3.i]
theorem isSpheroidalSolutionReal_iff_isSpheroidalFactor {m : ℕ} {γ2 lam : ℝ} {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hreal : ∀ x : ℝ, (g x).im = 0) :
    IsSpheroidalSolutionReal lam γ2 m (fun x => (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g x).re) ↔
      IsSpheroidalFactor m γ2 lam g := by
  have hg1 := p1s_differentiable_deriv hg
  set h : ℝ → ℝ := fun x => (1 - x ^ 2) ^ ((m : ℝ) / 2)
  set G : ℝ → ℝ := fun x => (g x).re
  set G1 : ℝ → ℝ := fun x => (deriv g x).re
  set G2 : ℝ → ℝ := fun x => (deriv (deriv g) x).re
  have hG : ∀ x, HasDerivAt G (G1 x) x := p1s_hasDerivAt_re hg
  have hG1 : ∀ x, HasDerivAt G1 (G2 x) x := p1s_hasDerivAt_re hg1
  have hf : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun x => h x * G x)
      (-((m : ℝ) * x) / (1 - x ^ 2) * h x * G x + h x * G1 x) x :=
    fun x hx => (p1s_hasDerivAt_weight m hx).mul (hG x)
  -- the flux `(1-x²) f'` and its derivative
  have hev : ∀ x ∈ Ioo (-1 : ℝ) 1, (fun t => (1 - t ^ 2) * deriv (fun x => h x * G x) t) =ᶠ[𝓝 x]
      fun t => h t * ((1 - t ^ 2) * G1 t - m * t * G t) := by
    intro x hx
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    rw [(hf t ht).deriv]
    have : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
    field_simp
    ring
  have hflux : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt
      (fun t => (1 - t ^ 2) * deriv (fun x => h x * G x) t)
      (h x * ((1 - x ^ 2) * G2 x - 2 * ((m : ℝ) + 1) * x * G1 x +
          ((m : ℝ) ^ 2 * x ^ 2 / (1 - x ^ 2) - m) * G x)) x := by
    intro x hx
    have hq : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_sub 1)
    have hl : HasDerivAt (fun t : ℝ => (m : ℝ) * t) m x := by
      simpa using (hasDerivAt_id x).const_mul (m : ℝ)
    have := (p1s_hasDerivAt_weight m hx).mul ((hq.mul (hG1 x)).sub (hl.mul (hG x)))
    refine ((this.congr_of_eventuallyEq (hev x hx))).congr_deriv ?_
    have : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
    simp only [Pi.mul_apply, Pi.sub_apply]
    field_simp
    ring
  -- the factor expression along the real axis
  set Φ : ℂ → ℂ := fun z => (1 - z ^ 2) * deriv (deriv g) z - 2 * ((m : ℂ) + 1) * z * deriv g z +
    ((lam : ℂ) - m * ((m : ℂ) + 1) + γ2 * (1 - z ^ 2)) * g z
  have hΦre : ∀ x : ℝ, Φ x = (((1 - x ^ 2) * G2 x - 2 * ((m : ℝ) + 1) * x * G1 x +
      (lam - m * ((m : ℝ) + 1) + γ2 * (1 - x ^ 2)) * G x : ℝ) : ℂ) := by
    intro x
    have e0 : g x = (G x : ℂ) := Complex.ext (by simp [G]) (by simp [hreal])
    have e1 : deriv g x = (G1 x : ℂ) :=
      Complex.ext (by simp [G1]) (by simp [p1s_deriv_im_eq_zero hg hreal])
    have e2 : deriv (deriv g) x = (G2 x : ℂ) :=
      Complex.ext (by simp [G2]) (by simp [p1s_deriv_im_eq_zero hg1
        (p1s_deriv_im_eq_zero hg hreal)])
    simp only [Φ, e0, e1, e2]
    push_cast; ring
  have key : ∀ x ∈ Ioo (-1 : ℝ) 1,
      h x * ((1 - x ^ 2) * G2 x - 2 * ((m : ℝ) + 1) * x * G1 x +
          ((m : ℝ) ^ 2 * x ^ 2 / (1 - x ^ 2) - m) * G x) -
        (-(lam + γ2 * (1 - x ^ 2) - (m : ℝ) ^ 2 / (1 - x ^ 2)) * (h x * G x)) =
      h x * (Φ x).re := by
    intro x hx
    have : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
    rw [hΦre, Complex.ofReal_re]
    field_simp
    ring
  constructor
  · intro hs
    refine ⟨hg, p1s_eq_zero_of_Ioo ?_ fun x hx => ?_⟩
    · exact ((((differentiable_const _).sub (differentiable_id.pow 2)).mul hg1.deriv) |>.sub
        (((differentiable_const _).mul differentiable_id).mul hg1)).add
        (((differentiable_const _).add ((differentiable_const _).mul
          ((differentiable_const _).sub (differentiable_id.pow 2)))).mul hg)
    · have hu := (hflux x hx).unique (hs.hasDerivAt x hx)
      have hk := key x hx
      rw [hu, sub_self] at hk
      have hpos : 0 < h x := Real.rpow_pos_of_pos (by nlinarith [hx.1, hx.2]) _
      rw [hΦre x, Complex.ofReal_re] at hk
      show Φ (x : ℂ) = 0
      rw [hΦre x]
      rcases mul_eq_zero.mp hk.symm with h1 | h1
      · exact absurd h1 hpos.ne'
      · rw [h1, Complex.ofReal_zero]
  · intro hF
    refine ⟨fun x hx => (hf x hx).differentiableAt, fun x hx => ?_⟩
    refine (hflux x hx).congr_deriv ?_
    have hk := key x hx
    have : Φ x = 0 := hF.ode x
    rw [this, Complex.zero_re, mul_zero, sub_eq_zero] at hk
    exact hk

/-- **Bounded solutions** (DLMF §30.3(i)): for real `λ`, 30.2.1 with `μ = m` has a nonzero
solution bounded on `(-1, 1)` iff `λ` lies in the spectrum, i.e. iff it has a nonzero solution
of the form `(1-x²)^{m/2} g(x)` with `g` entire. -/
@[dlmf 30.3.i]
theorem exists_bounded_iff_mem_spheroidalSpectrum (m : ℕ) (γ2 lam : ℝ) :
    (∃ f : ℝ → ℝ, IsSpheroidalSolutionReal lam γ2 m f ∧ (∃ x ∈ Ioo (-1 : ℝ) 1, f x ≠ 0) ∧
      ∃ C, ∀ x ∈ Ioo (-1 : ℝ) 1, |f x| ≤ C) ↔ lam ∈ spheroidalSpectrum m γ2 := by
  sorry

/-! ### §30.12 Generalized and Coulomb spheroidal functions -/

/-- **Reduction of 30.12.1** (DLMF §30.12): for `α = 0` the generalized equation 30.12.1 is 30.2.1
(proved). -/
@[dlmf 30.12.E1]
theorem isGenSpheroidalSolutionOn_zero_iff {lam γ2 μ : ℂ} {U : Set ℂ} {w : ℂ → ℂ} :
    IsGenSpheroidalSolutionOn lam 0 γ2 μ U w ↔ IsSpheroidalSolutionOn lam γ2 μ U w := by
  constructor
  · intro h
    exact ⟨h.differentiableAt, fun z hz => by simpa using h.hasDerivAt z hz⟩
  · intro h
    exact ⟨h.differentiableAt, fun z hz => by simpa using h.hasDerivAt z hz⟩

/-- **Reduction of 30.12.2** (DLMF §30.12): for `α = 0` the equation 30.12.2 is 30.2.1 (proved). -/
@[dlmf 30.12.E2]
theorem isSpheroidalSolutionOn₂_zero_iff {lam γ2 μ : ℂ} {U : Set ℂ} {w : ℂ → ℂ} :
    IsSpheroidalSolutionOn₂ lam 0 γ2 μ U w ↔ IsSpheroidalSolutionOn lam γ2 μ U w := by
  constructor
  · intro h
    exact ⟨h.differentiableAt, fun z hz => by simpa using h.hasDerivAt z hz⟩
  · intro h
    exact ⟨h.differentiableAt, fun z hz => by simpa using h.hasDerivAt z hz⟩

end DLMF.Spheroidal
