/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.Basic
public import DLMF.Legendre.ZeroTools

/-!
# The spheroidal differential equation (DLMF §30.2, §30.3(i))

The irregular singularity of the spheroidal equation 30.2.1 at infinity, its special cases
`γ = 0`, and the bounded solutions.

## Main results

* `spheroidal_irregular_infinity`: the irregular singularity of rank 1 at `∞` (§30.2(i)).
* `isSpheroidalSolutionReal_ferrersP`, `isSpheroidalZetaSolution_sphericalJ`: the case `γ = 0`
  (the associated Legendre equation 14.2.2 and the spherical Bessel equation 10.47.1).
* `exists_bounded_iff_mem_spheroidalSpectrum`: bounded solutions exist exactly on the spectrum
  (§30.3(i)).

## Implementation notes

The transformed forms, the indicial exponents, the Mathieu case, the factor equation and the
generalized equations are in `DLMF.Spheroidal.Basic.Equation`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Spheroidal

/-! ### Calculus helpers -/

/-- Identity under the stated parameter and domain assumptions: `z * ((n : ℂ) * z ^ (n - 1)) = n *
z ^ n`. -/
private lemma mul_natCast_mul_pow_sub_one (n : ℕ) (z : ℂ) :
    z * ((n : ℂ) * z ^ (n - 1)) = n * z ^ n := by
  rcases n with _ | n
  · simp
  · simp [pow_succ]; ring

/-- Identity under the stated parameter and domain assumptions: `z ^ 2 * ((n : ℂ) * (((n - 1 : ℕ)
: ℂ) * z ^ (n - 1 - 1))) = n * (n - 1) * z ^ n`. -/
private lemma sq_mul_natCast_mul_pow_sub_two (n : ℕ) (z : ℂ) :
    z ^ 2 * ((n : ℂ) * (((n - 1 : ℕ) : ℂ) * z ^ (n - 1 - 1))) = n * (n - 1) * z ^ n := by
  rcases n with _ | _ | n
  · simp
  · simp
  · simp [pow_succ]; ring

/-! ### §30.2(i) Singularities -/

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

/-! ### §30.2(iii) Special cases -/

/-- **`γ = 0`: the associated Legendre equation** (DLMF §30.2(iii), 14.2.2): the Ferrers function
`𝖯^m_n(x)` solves 30.2.1 on `(-1, 1)` with `γ = 0`, `λ = n(n+1)`, `μ = m`. -/
@[dlmf 30.2.iii]
theorem isSpheroidalSolutionReal_ferrersP (n m : ℕ) :
    IsSpheroidalSolutionReal ((n : ℝ) * (n + 1)) 0 m
      (fun x => (DLMF.Legendre.ferrersP n m x).re) := by
  have key : ∀ x ∈ Ioo (-1 : ℝ) 1, _ := fun x hx =>
    DLMF.Legendre.LegendreSturm.ferrersP_solution (n : ℝ) (m : ℝ) hx
  simp only [Complex.ofReal_natCast] at key
  have hd : ∀ x ∈ Ioo (-1 : ℝ) 1, deriv (fun t => (DLMF.Legendre.ferrersP n m t).re) x =
      (deriv (DLMF.Legendre.ferrersP n m) x).re := fun x hx => (key x hx).1.deriv
  refine ⟨fun x hx => (key x hx).1.differentiableAt, fun x hx => ?_⟩
  have h2 := (key x hx).2
  refine (h2.congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  rw [hd t ht]

/-- **`γ = 0` in 30.2.4: the spherical Bessel equation** (DLMF §30.2(iii), 10.47.1): with `γ = 0`
and `μ` arbitrary, 30.2.4 reads `ζ² w'' + 2ζ w' + (ζ² - λ) w = 0`, which for `λ = n(n+1)` is
satisfied by the spherical Bessel function `j_n` (`DLMF.Bessel.sphericalJ`). -/
@[dlmf 30.2.iii]
theorem isSpheroidalZetaSolution_sphericalJ (n : ℕ) (μ : ℂ) :
    IsSpheroidalZetaSolution ((n : ℂ) * (n + 1)) 0 μ univ (DLMF.Bessel.sphericalJ n) := by
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
  have hw : DLMF.Bessel.sphericalJ n = fun z => c * (z ^ n * F 0 (-z ^ 2 / 4)) := by
    funext z; simp only [DLMF.Bessel.sphericalJ, F, c, b]; simp; ring_nf
  have hd1 : ∀ z, HasDerivAt (DLMF.Bessel.sphericalJ n)
      (c * ((n : ℂ) * z ^ (n - 1) * F 0 (-z ^ 2 / 4) +
        z ^ n * (F 1 (-z ^ 2 / 4) * (-z / 2)))) z := by
    intro z; rw [hw]
    exact ((hP z).mul ((hF 0 _).comp z (hu z))).const_mul c
  have hD1 : deriv (DLMF.Bessel.sphericalJ n) = fun z => c *
      ((n : ℂ) * z ^ (n - 1) * F 0 (-z ^ 2 / 4) +
        z ^ n * (F 1 (-z ^ 2 / 4) * (-z / 2))) := funext fun z => (hd1 z).deriv
  have hm : ∀ z : ℂ, HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) z := by
    intro z; simpa using ((hasDerivAt_id z).neg.div_const 2)
  have hd2 : ∀ z, HasDerivAt (deriv (DLMF.Bessel.sphericalJ n))
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
  have a1 := mul_natCast_mul_pow_sub_one n z
  have a2 := sq_mul_natCast_mul_pow_sub_two n z
  have hF0 : regularizedHGFun (∅ : Multiset ℂ) {b} = F 0 := by simp [F]
  rw [hF0] at hode
  simp only [sub_zero, zero_mul, zero_div]
  linear_combination c * F 0 (-z ^ 2 / 4) * a2 - c * z ^ 2 * F 1 (-z ^ 2 / 4) * a1 +
    2 * c * F 0 (-z ^ 2 / 4) * a1 - c * z ^ n * z ^ 2 * hode

/-! ### §30.3(i) Bounded solutions -/

/-- **Bounded solutions** (DLMF §30.3(i)): for real `λ`, 30.2.1 with `μ = m` has a nonzero
solution bounded on `(-1, 1)` iff `λ` lies in the spectrum, i.e. iff it has a nonzero solution
of the form `(1-x²)^{m/2} g(x)` with `g` entire. -/
@[dlmf 30.3.i]
theorem exists_bounded_iff_mem_spheroidalSpectrum (m : ℕ) (γ2 lam : ℝ) :
    (∃ f : ℝ → ℝ, IsSpheroidalSolutionReal lam γ2 m f ∧ (∃ x ∈ Ioo (-1 : ℝ) 1, f x ≠ 0) ∧
      ∃ C, ∀ x ∈ Ioo (-1 : ℝ) 1, |f x| ≤ C) ↔ lam ∈ spheroidalSpectrum m γ2 := by
  sorry

end DLMF.Spheroidal
