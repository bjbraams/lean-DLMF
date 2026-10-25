/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.SymmetricSpecialCases
public import Carlson.R.SlitDeriv
public import Carlson.R.EulerPoisson

/-!
# Symmetric elliptic integrals: derivatives and differential equations (DLMF §19.18)

Node derivatives (19.18.4), (19.18.5), the translation and Euler identities (19.18.8), (19.18.11),
the Euler–Poisson system (19.18.12), (19.18.13) of `R_{-a}(𝐛; 𝐳)` on the product slit plane, the
corresponding statements (19.18.1), (19.18.2), (19.18.6), (19.18.7), (19.18.9), (19.18.10) for
`R_F`, `R_G`, and the second-order equations (19.18.14)–(19.18.17) of the complete case
`R_{-a}(½, ½; z₁, z₂)`.

Partial derivatives are `Dirichlet.carlsonPartialDeriv j F z = d/dw F(z with zⱼ := w)` at
`w = zⱼ` (from `lean-codes`); `𝐛 + 𝐞ⱼ` is `Dirichlet.addDirichletUnit b j`. The sum of the three
partial derivatives (19.18.6), (19.18.7) is stated as the derivative along the diagonal
translation `s ↦ (x + s, y + s, z + s)` (equivalent by the chain rule for these holomorphic
functions). Statements for `R_{-a}` hold for all complex `a, 𝐛` (stronger than DLMF), with
`∑ bⱼ ≠ 0` where DLMF divides by it (`wⱼ = bⱼ/∑ bₖ`, 19.18.3).
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Real Topology

namespace DLMF.EllipticIntegrals

variable {ι : Type*} [Fintype ι]

theorem ei19c_eventuallyEq (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) :
    symEllIntR a b =ᶠ[𝓝 z] Carlson.carlsonR (-a) b := by
  filter_upwards [Carlson.isOpen_carlsonRSlitDomain.mem_nhds hz] with w hw
  exact symEllIntR_of_mem _ _ hw

open scoped Classical in
theorem ei19c_hasDerivAt_update (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (j : ι) :
    HasDerivAt (fun w => symEllIntR a b (Function.update z j w))
      (Gamma (∑ i, b i) * (-a * b j *
        Carlson.regCarlsonR (-a - 1) (Dirichlet.addDirichletUnit b j) z)) (z j) := by
  have hc : Tendsto (Function.update z j) (𝓝 (z j)) (𝓝 z) := by
    have := ((continuous_const (y := z)).update j continuous_id).tendsto (z j)
    simpa using this
  have hev := hc.eventually (ei19c_eventuallyEq a b hz)
  have h := (Carlson.hasDerivAt_regCarlsonR_update (-a) b hz j).const_mul (Gamma (∑ i, b i))
  exact h.congr_of_eventuallyEq hev

open scoped Classical in
/-- DLMF 19.18.4: `∂ⱼ R_{-a}(𝐛; 𝐳) = -a wⱼ R_{-a-1}(𝐛 + 𝐞ⱼ; 𝐳)`, `wⱼ = bⱼ/∑ bₖ` (19.18.3),
for slit-plane nodes and `∑ bₖ ≠ 0`. -/
@[dlmf 19.18.E4, dlmf 19.18.E3]
theorem hasDerivAt_symEllIntR_update (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (j : ι) (hb : ∑ i, b i ≠ 0) :
    HasDerivAt (fun w => symEllIntR a b (Function.update z j w))
      (-a * (b j / ∑ i, b i) * symEllIntR (a + 1) (Dirichlet.addDirichletUnit b j) z) (z j) := by
  refine (ei19c_hasDerivAt_update a b hz j).congr_deriv ?_
  rw [symEllIntR_of_mem _ _ hz]
  unfold Carlson.carlsonR
  rw [Dirichlet.sum_addDirichletUnit, Complex.Gamma_add_one _ hb, show -(a + 1) = -a - 1 by ring]
  field_simp

/-- DLMF 19.18.8: `∑ⱼ ∂ⱼ R_{-a}(𝐛; 𝐳) = -a R_{-a-1}(𝐛; 𝐳)`, as the derivative along the diagonal
translation `s ↦ 𝐳 + s𝟏` at `s = x` (slit-plane nodes `x + zⱼ`; all complex `a, 𝐛`). -/
@[dlmf 19.18.E8]
theorem hasDerivAt_symEllIntR_translate (a : ℂ) (b z : ι → ℂ) {x : ℂ}
    (hx : (fun i => x + z i) ∈ Carlson.carlsonRSlitDomain) :
    HasDerivAt (fun s => symEllIntR a b (fun i => s + z i))
      (-a * symEllIntR (a + 1) b (fun i => x + z i)) x := by
  have hc : Tendsto (fun s : ℂ => fun i => s + z i) (𝓝 x) (𝓝 fun i => x + z i) :=
    (continuous_pi fun i => continuous_id.add continuous_const).tendsto x
  have hev := hc.eventually (ei19c_eventuallyEq a b hx)
  have h := (Carlson.hasDerivAt_regCarlsonR_translate (-a) b z hx).const_mul (Gamma (∑ i, b i))
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [symEllIntR_of_mem _ _ hx]
  unfold Carlson.carlsonR
  rw [show -a - 1 = -(a + 1) by ring]
  ring

theorem ei19c_deriv_update (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (j : ι) :
    Dirichlet.carlsonPartialDeriv j (symEllIntR a b) z =
      Gamma (∑ i, b i) * (-a * b j *
        Carlson.regCarlsonR (-a - 1) (Dirichlet.addDirichletUnit b j) z) :=
  (ei19c_hasDerivAt_update a b hz j).deriv

/-- DLMF 19.18.11: Euler's homogeneity relation `∑ⱼ zⱼ ∂ⱼ v = -a v` for
`v = R_{-a}(𝐛; 𝐳)` (slit-plane nodes; all complex `a, 𝐛`). -/
@[dlmf 19.18.E11]
theorem sum_mul_partialDeriv_symEllIntR (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) :
    ∑ j, z j * Dirichlet.carlsonPartialDeriv j (symEllIntR a b) z = -a * symEllIntR a b z := by
  simp_rw [ei19c_deriv_update a b hz]
  have h := Carlson.regCarlsonR_add_one_eq_sum_mul_addDirichletUnit (-a - 1) b hz
  rw [sub_add_cancel] at h
  rw [symEllIntR_of_mem _ _ hz]
  unfold Carlson.carlsonR
  rw [h, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- DLMF 19.18.5: `(zⱼ ∂ⱼ + bⱼ) R_{-a}(𝐛; 𝐳) = wⱼ a' R_{-a}(𝐛 + 𝐞ⱼ; 𝐳)`, `a' = -a + ∑ bₖ`,
`wⱼ = bⱼ / ∑ bₖ` (slit-plane nodes, `∑ bₖ ≠ 0`). -/
@[dlmf 19.18.E5]
theorem mul_partialDeriv_add_symEllIntR (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (j : ι) (hb : ∑ i, b i ≠ 0) :
    z j * Dirichlet.carlsonPartialDeriv j (symEllIntR a b) z + b j * symEllIntR a b z =
      b j / (∑ i, b i) * (-a + ∑ i, b i) *
        symEllIntR a (Dirichlet.addDirichletUnit b j) z := by
  rw [ei19c_deriv_update a b hz, symEllIntR_of_mem _ _ hz, symEllIntR_of_mem _ _ hz]
  have h1 := Carlson.mul_carlsonPartialDeriv_add_mul_regCarlsonR (-a) b hz j
  rw [Carlson.carlsonPartialDeriv_regCarlsonR (-a) b hz j] at h1
  unfold Carlson.carlsonR
  rw [Dirichlet.sum_addDirichletUnit, Complex.Gamma_add_one _ hb]
  have key : b j / (∑ i, b i) * (-a + ∑ i, b i) * ((∑ i, b i) * Gamma (∑ i, b i) *
      Carlson.regCarlsonR (-a) (Dirichlet.addDirichletUnit b j) z) = Gamma (∑ i, b i) *
      (b j * (∑ i, b i + -a) * Carlson.regCarlsonR (-a) (Dirichlet.addDirichletUnit b j) z) := by
    field_simp; ring
  rw [key]
  linear_combination Gamma (∑ i, b i) * h1

open scoped Classical in
theorem ei19c_partialDeriv_congr {F G : (ι → ℂ) → ℂ} {z : ι → ℂ} (h : F =ᶠ[𝓝 z] G) (j : ι) :
    Dirichlet.carlsonPartialDeriv j F z = Dirichlet.carlsonPartialDeriv j G z :=
  SeveralComplexVariables.partialDeriv_congr h j

open scoped Classical in
theorem ei19c_eulerPoisson_congr {F G : (ι → ℂ) → ℂ} {z : ι → ℂ} (h : F =ᶠ[𝓝 z] G)
    (i j : ι) (b : ι → ℂ) :
    Dirichlet.carlsonEulerPoissonOperator i j b z F =
      Dirichlet.carlsonEulerPoissonOperator i j b z G := by
  have h' : Dirichlet.carlsonPartialDeriv j F =ᶠ[𝓝 z] Dirichlet.carlsonPartialDeriv j G :=
    h.eventually_nhds.mono fun w hw => SeveralComplexVariables.partialDeriv_congr hw j
  unfold Dirichlet.carlsonEulerPoissonOperator
  simp only [Dirichlet.carlsonPartialDeriv_eq_partialDeriv] at h' ⊢
  rw [SeveralComplexVariables.partialDeriv_congr h' i, SeveralComplexVariables.partialDeriv_congr h j,
    SeveralComplexVariables.partialDeriv_congr h i]

/-- DLMF 19.18.13: the Euler–Poisson system
`((zⱼ - zₗ) ∂ⱼ ∂ₗ + bⱼ ∂ₗ - bₗ ∂ⱼ) v = 0` for `v = R_{-a}(𝐛; 𝐳)` (slit-plane nodes; all complex
`a, 𝐛`; also for `j = l`). From `Carlson.carlsonEulerPoissonOperator_carlsonR`. -/
@[dlmf 19.18.E13]
theorem eulerPoisson_symEllIntR (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (j l : ι) :
    Dirichlet.carlsonEulerPoissonOperator j l b z (symEllIntR a b) = 0 := by
  rw [ei19c_eulerPoisson_congr (ei19c_eventuallyEq a b hz)]
  exact Carlson.carlsonEulerPoissonOperator_carlsonR (-a) b hz j l

/-- DLMF 19.18.12: `(zⱼ ∂ⱼ + bⱼ) ∂ₗ v = (zₗ ∂ₗ + bₗ) ∂ⱼ v` for `v = R_{-a}(𝐛; 𝐳)` (slit-plane
nodes). -/
@[dlmf 19.18.E12]
theorem eulerPoisson_symEllIntR' (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (j l : ι) :
    z j * Dirichlet.carlsonPartialDeriv j (Dirichlet.carlsonPartialDeriv l (symEllIntR a b)) z +
        b j * Dirichlet.carlsonPartialDeriv l (symEllIntR a b) z =
      z l * Dirichlet.carlsonPartialDeriv l (Dirichlet.carlsonPartialDeriv j (symEllIntR a b)) z +
        b l * Dirichlet.carlsonPartialDeriv j (symEllIntR a b) z := by
  sorry

/-! ### `R_F`, `R_G` as functions of the vector `(x, y, z)` -/

/-- `R_F` as a function on `ℂ³ = Fin 3 → ℂ`. -/
def symEllIntRFVec (v : Fin 3 → ℂ) : ℂ := symEllIntRF (v 0) (v 1) (v 2)

/-- `R_G` as a function on `ℂ³ = Fin 3 → ℂ`. -/
def symEllIntRGVec (v : Fin 3 → ℂ) : ℂ := symEllIntRG (v 0) (v 1) (v 2)

theorem ei19c_vec3 (v : Fin 3 → ℂ) : (![v 0, v 1, v 2] : Fin 3 → ℂ) = v := by
  funext i; fin_cases i <;> rfl

theorem ei19c_RFVec_eventuallyEq {v : Fin 3 → ℂ} (hv : v ∈ Carlson.carlsonRSlitDomain) :
    symEllIntRFVec =ᶠ[𝓝 v] symEllIntR (1 / 2) (fun _ : Fin 3 => 1 / 2) := by
  filter_upwards [Carlson.isOpen_carlsonRSlitDomain.mem_nhds hv] with w hw
  rw [symEllIntRFVec, symEllIntRF_eq_symEllIntR (hw 0) (hw 1) (hw 2), ei19c_vec3]

theorem ei19c_RGVec_eventuallyEq {v : Fin 3 → ℂ} (hv : v ∈ Carlson.carlsonRSlitDomain) :
    symEllIntRGVec =ᶠ[𝓝 v] symEllIntR (-1 / 2) (fun _ : Fin 3 => 1 / 2) := by
  filter_upwards [Carlson.isOpen_carlsonRSlitDomain.mem_nhds hv] with w hw
  rw [symEllIntRGVec, symEllIntRG_eq_symEllIntR (hw 0) (hw 1) (hw 2), ei19c_vec3]

/-- DLMF 19.18.1: `∂R_F(x, y, z)/∂z = -(1/6) R_D(x, y, z)` (slit-plane variables). -/
@[dlmf 19.18.E1]
theorem hasDerivAt_symEllIntRF_right {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => symEllIntRF x y w) (-(1 / 6) * symEllIntRD x y z) z := by
  have h := hasDerivAt_symEllIntR_update (1 / 2) (fun _ : Fin 3 => 1 / 2) (ei19c_slit3 hx hy hz) 2
    (by simp)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    rw [symEllIntRF_eq_symEllIntR hx hy hw]
    congr 1; funext i; fin_cases i <;> simp [Function.update]
  · have hb : Dirichlet.addDirichletUnit (fun _ : Fin 3 => (1 / 2 : ℂ)) 2 = ![1 / 2, 1 / 2, 3 / 2] := by
      unfold Dirichlet.addDirichletUnit
      funext i; fin_cases i <;> simp [Function.update]; norm_num
    rw [hb, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, ← symEllIntRD_eq_symEllIntR hx hy hz]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

/-- DLMF 19.18.2: `d/dx R_G(x + a, x + b, x + c) = (1/2) R_F(x + a, x + b, x + c)`
(`x + a, x + b, x + c ∈ ℂ \ (-∞, 0]`). -/
@[dlmf 19.18.E2]
theorem hasDerivAt_symEllIntRG_translate {a b c x : ℂ} (ha : x + a ∈ slitPlane)
    (hb : x + b ∈ slitPlane) (hc : x + c ∈ slitPlane) :
    HasDerivAt (fun s => symEllIntRG (s + a) (s + b) (s + c))
      ((1 / 2) * symEllIntRF (x + a) (x + b) (x + c)) x := by
  have hv : (fun i => x + (![a, b, c] : Fin 3 → ℂ) i) ∈ Carlson.carlsonRSlitDomain := by
    intro i; fin_cases i <;> assumption
  have h := hasDerivAt_symEllIntR_translate (-1 / 2) (fun _ : Fin 3 => 1 / 2) ![a, b, c] hv
  have hc' : Tendsto (fun s : ℂ => fun i => s + (![a, b, c] : Fin 3 → ℂ) i) (𝓝 x)
      (𝓝 fun i => x + (![a, b, c] : Fin 3 → ℂ) i) :=
    (continuous_pi fun i => continuous_id.add continuous_const).tendsto x
  have hev := hc'.eventually (ei19c_RGVec_eventuallyEq hv)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hev] with s hs
    rw [← hs]; rfl
  · rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num,
      show (fun i => x + (![a, b, c] : Fin 3 → ℂ) i) = ![x + a, x + b, x + c] by
        funext i; fin_cases i <;> rfl, ← symEllIntRF_eq_symEllIntR ha hb hc]
    ring

/-- DLMF 19.18.6: `(∂ₓ + ∂_y + ∂_z) R_F(x, y, z) = -1/(2√x√y√z)`, as the derivative along the
diagonal translation (slit-plane variables). -/
@[dlmf 19.18.E6]
theorem hasDerivAt_symEllIntRF_translate {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    HasDerivAt (fun s => symEllIntRF (x + s) (y + s) (z + s))
      (-1 / (2 * x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ))) 0 := by
  have hv : (fun i => (0 : ℂ) + (![x, y, z] : Fin 3 → ℂ) i) ∈ Carlson.carlsonRSlitDomain := by
    intro i; fin_cases i <;> simpa
  have h := hasDerivAt_symEllIntR_translate (1 / 2) (fun _ : Fin 3 => 1 / 2) ![x, y, z] hv
  have hc' : Tendsto (fun s : ℂ => fun i => s + (![x, y, z] : Fin 3 → ℂ) i) (𝓝 0)
      (𝓝 fun i => 0 + (![x, y, z] : Fin 3 → ℂ) i) :=
    (continuous_pi fun i => continuous_id.add continuous_const).tendsto 0
  have hev := hc'.eventually (ei19c_RFVec_eventuallyEq hv)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hev] with s hs
    rw [← hs]; simp [symEllIntRFVec, add_comm]
  · have h3 : (1 / 2 : ℂ) + 1 = ∑ _i : Fin 3, (1 / 2 : ℂ) := by simp; norm_num
    have hv' : (![x, y, z] : Fin 3 → ℂ) ∈ Carlson.carlsonRSlitDomain := ei19c_slit3 hx hy hz
    simp only [zero_add]
    rw [h3, symEllIntR_sum _ hv' (Complex.Gamma_ne_zero_of_re_pos (by simp))]
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [show -(1 / 2 : ℂ) = -1 / 2 by ring, ← ei19c_inv_cpow_half, ← ei19c_inv_cpow_half,
      ← ei19c_inv_cpow_half]
    have h1 : x ^ (1 / 2 : ℂ) ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr
      (slitPlane_ne_zero hx)
    have h2 : y ^ (1 / 2 : ℂ) ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr
      (slitPlane_ne_zero hy)
    have h4 : z ^ (1 / 2 : ℂ) ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr
      (slitPlane_ne_zero hz)
    field_simp

/-- DLMF 19.18.7: `(∂ₓ + ∂_y + ∂_z) R_G(x, y, z) = (1/2) R_F(x, y, z)`, as the derivative along
the diagonal translation (slit-plane variables). -/
@[dlmf 19.18.E7]
theorem hasDerivAt_symEllIntRG_translate_zero {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    HasDerivAt (fun s => symEllIntRG (x + s) (y + s) (z + s)) ((1 / 2) * symEllIntRF x y z) 0 := by
  have h := hasDerivAt_symEllIntRG_translate (x := 0) (a := x) (b := y) (c := z)
    (by simpa using hx) (by simpa using hy) (by simpa using hz)
  simp only [zero_add] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [add_comm]

open scoped Classical in
/-- DLMF 19.18.9: `(x∂ₓ + y∂_y + z∂_z) R_F(x, y, z) = -(1/2) R_F(x, y, z)` (slit-plane
variables; `v = (x, y, z)`). -/
@[dlmf 19.18.E9]
theorem sum_mul_partialDeriv_symEllIntRF {v : Fin 3 → ℂ} (hv : v ∈ Carlson.carlsonRSlitDomain) :
    ∑ j, v j * Dirichlet.carlsonPartialDeriv j symEllIntRFVec v = -(1 / 2) * symEllIntRFVec v := by
  have h := ei19c_RFVec_eventuallyEq hv
  have hp : ∀ j, Dirichlet.carlsonPartialDeriv j symEllIntRFVec v =
      Dirichlet.carlsonPartialDeriv j (symEllIntR (1 / 2) (fun _ : Fin 3 => 1 / 2)) v := by
    exact fun j => ei19c_partialDeriv_congr h j
  simp_rw [hp, h.eq_of_nhds]
  exact sum_mul_partialDeriv_symEllIntR _ _ hv

/-- DLMF 19.18.10: `((x - y) ∂²/∂x∂y + (1/2)(∂_y - ∂ₓ)) R_F(x, y, z) = 0` (and its permutations:
any pair `j, l` of coordinates), slit-plane variables, `v = (x, y, z)`. -/
@[dlmf 19.18.E10]
theorem eulerPoisson_symEllIntRF {v : Fin 3 → ℂ} (hv : v ∈ Carlson.carlsonRSlitDomain)
    (j l : Fin 3) :
    Dirichlet.carlsonEulerPoissonOperator j l (fun _ => 1 / 2) v symEllIntRFVec = 0 := by
  rw [ei19c_eulerPoisson_congr (ei19c_RFVec_eventuallyEq hv)]
  exact eulerPoisson_symEllIntR _ _ hv j l

/-! ### Second-order equations of the complete case (19.18.14–19.18.17) -/

/-- DLMF 19.18.14: `w = R_{-a}(½, ½; x + y, x - y)` satisfies the Euler–Poisson–Darboux equation
`w_xx = w_yy + (1/y) w_y`, for real `x > |y|`, `y ≠ 0`. -/
@[dlmf 19.18.E14]
theorem eulerPoissonDarboux_symEllIntR (a : ℂ) {x y : ℝ} (hxy : |y| < x) (hy : y ≠ 0) :
    let w : ℝ → ℝ → ℂ := fun x y => symEllIntR a ![1 / 2, 1 / 2] ![(x + y : ℝ), (x - y : ℝ)]
    deriv (fun s => deriv (fun r => w r y) s) x =
      deriv (fun s => deriv (fun r => w x r) s) y + (1 / y : ℂ) * deriv (fun r => w x r) y := by
  sorry

/-- DLMF 19.18.15: `W = R_{-a}(½, ½; t + r, t - r)`, `r = √(x² + y²)`, satisfies the wave
equation `W_tt = W_xx + W_yy`, for real `t > r > 0`. -/
@[dlmf 19.18.E15]
theorem wave_symEllIntR (a : ℂ) {t x y : ℝ} (hr : 0 < x ^ 2 + y ^ 2)
    (ht : Real.sqrt (x ^ 2 + y ^ 2) < t) :
    let W : ℝ → ℝ → ℝ → ℂ := fun t x y =>
      symEllIntR a ![1 / 2, 1 / 2]
        ![(t + Real.sqrt (x ^ 2 + y ^ 2) : ℝ), (t - Real.sqrt (x ^ 2 + y ^ 2) : ℝ)]
    deriv (fun s => deriv (fun r => W r x y) s) t =
      deriv (fun s => deriv (fun r => W t r y) s) x + deriv (fun s => deriv (fun r => W t x r) s) y := by
  sorry

/-- DLMF 19.18.16: `u = R_{-a}(½, ½; x + iy, x - iy)` satisfies the equation of axially
symmetric potential theory `u_xx + u_yy + (1/y) u_y = 0`, for real `x`, `y ≠ 0`. -/
@[dlmf 19.18.E16]
theorem axialPotential_symEllIntR (a : ℂ) {x y : ℝ} (hy : y ≠ 0) :
    let u : ℝ → ℝ → ℂ := fun x y => symEllIntR a ![1 / 2, 1 / 2] ![x + y * I, x - y * I]
    deriv (fun s => deriv (fun r => u r y) s) x + deriv (fun s => deriv (fun r => u x r) s) y +
      (1 / y : ℂ) * deriv (fun r => u x r) y = 0 := by
  sorry

/-- DLMF 19.18.17: `U = R_{-a}(½, ½; z + iρ, z - iρ)`, `ρ = √(x² + y²)`, satisfies Laplace's
equation `U_xx + U_yy + U_zz = 0`, for real `x, y, z` with `ρ > 0`. -/
@[dlmf 19.18.E17]
theorem laplace_symEllIntR (a : ℂ) {x y z : ℝ} (hρ : 0 < x ^ 2 + y ^ 2) :
    let U : ℝ → ℝ → ℝ → ℂ := fun x y z =>
      symEllIntR a ![1 / 2, 1 / 2]
        ![z + Real.sqrt (x ^ 2 + y ^ 2) * I, z - Real.sqrt (x ^ 2 + y ^ 2) * I]
    deriv (fun s => deriv (fun r => U r y z) s) x + deriv (fun s => deriv (fun r => U x r z) s) y +
      deriv (fun s => deriv (fun r => U x y r) s) z = 0 := by
  sorry

end DLMF.EllipticIntegrals
