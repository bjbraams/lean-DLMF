/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.QuarticIntegral
public import DLMF.EllipticIntegrals.Symmetric

/-!
# Reduction of general elliptic integrals (DLMF §19.29)

DLMF §19.29 reduces integrals over a real interval `(y, x)` whose integrands contain the square
root of a quartic or cubic polynomial, written as a product of linear factors
`a_α + b_α t`, to the symmetric integrals `R_F`, `R_D`, `R_J`, `R_C` of
`DLMF.EllipticIntegrals.Symmetric`.

* §19.29(i): the notation (19.29.1)–(19.29.3), (19.29.5), (19.29.9) as definitions
  (`ellRedRoot`, `ellRedDet`, `ellRedS`, `ellRedU`, `ellRedUInf`, `ellRedUNegInf`,
  `ellRedU5Sq`, `ellRedS5`, `ellRedQ5Sq`); the algebraic identities of (19.29.5) and (19.29.9)
  are **proved** for arbitrary complex coefficients; the reduction theorems (19.29.4), (19.29.6),
  (19.29.7), (19.29.8) and the example (19.29.10) are stated for DLMF's complex coefficients.
  The real case of (19.29.4) with four positive linear factors is **proved** from Carlson's
  (9.8-12) in `lean-codes` (`Carlson.integral_quartic_eq_carlsonRF`).
* §19.29(ii): the integrals `I(𝐦)` (19.29.11), the unit vectors (19.29.12), the basic
  integrals (19.29.13), (19.29.14), the partial-fraction relation (19.29.15) and the
  recurrence (19.29.18) (**proved**, under explicit integrability hypotheses that DLMF leaves
  implicit), the cubic recurrence (19.29.16) and the reduction statement of 19.29.ii.p3.
* §19.29(iii): the examples (19.29.19)–(19.29.33). The case `0 < y` of (19.29.19) is
  **proved** from Carlson's Exercise 9.8-3 (`Carlson.integral_quadratic_mul_quadratic`).

## Conventions

**Convergence.** In §19.29(iii) DLMF assumes only that the quadratics are positive on the open
interval; an integrand can then still be non-integrable (a double zero at an endpoint, e.g.
`Q₁ = Q₂ = 1 - t²` on `(0, 1)`, or `t⁴` at `y = 0`). The theorems (19.29.19)–(19.29.21), (19.29.24),
(19.29.26), (19.29.27), (19.29.30) therefore carry an explicit integrability hypothesis
(`IntegrableOn … (Ioo y x)`), which is DLMF's implicit convergence assumption.

The coefficients `a_α`, `b_α` are complex, indexed by `Fin 5` (DLMF's `α = 1, …, 5` is Lean's
`0, …, 4`; the fifth factor occurs only in (19.29.8), (19.29.9)). Square roots are principal.
All integrals over `(y, x)` with `y < x` are Lebesgue integrals over `Ioo y x`; for a
non-integrable integrand the Lean value is `0`, so integrability is either implied by the
hypotheses or assumed explicitly. DLMF's condition that the segment with endpoints
`a_α + b_α y`, `a_α + b_α x` lie in `ℂ \ (-∞, 0)` is `∀ t ∈ [y, x], SymEllIntArg (a_α + b_α t)`.

## References

* NIST DLMF §19.29; B. C. Carlson, *Toward symbolic integration of elliptic integrals*,
  J. Symbolic Comput. 28 (1999); B. C. Carlson, *Special Functions of Applied Mathematics*,
  1977, §9.8 (formalized in `lean-codes`, reused here).
-/

@[expose] public noncomputable section

open Complex Set MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-! ### §19.29(i) Notation -/

/-- DLMF 19.29.1: `X_α = √(a_α + b_α x)` (and `Y_α = √(a_α + b_α y)` is `ellRedRoot a b y α`),
principal square root. -/
@[dlmf 19.29.E1]
def ellRedRoot {ι : Type*} (a b : ι → ℂ) (x : ℝ) (α : ι) : ℂ := (a α + b α * x) ^ (1 / 2 : ℂ)

/-- DLMF 19.29.2: `d_{αβ} = a_α b_β - a_β b_α`. -/
@[dlmf 19.29.E2]
def ellRedDet {ι : Type*} (a b : ι → ℂ) (α β : ι) : ℂ := a α * b β - a β * b α

/-- DLMF 19.29.3: `s(t) = ∏_{α=1}^{4} √(a_α + b_α t)` (Lean indices `0, …, 3`). Cubic cases are
obtained by setting one factor equal to `1` (`a = 1`, `b = 0`). -/
@[dlmf 19.29.E3]
def ellRedS (a b : Fin 5 → ℂ) (t : ℝ) : ℂ :=
  ellRedRoot a b t 0 * ellRedRoot a b t 1 * ellRedRoot a b t 2 * ellRedRoot a b t 3

/-- DLMF 19.29.5: `U_{αβ} = (X_α X_β Y_γ Y_δ + Y_α Y_β X_γ X_δ)/(x - y)`, for a permutation
`α, β, γ, δ` of the four factors (the complementary pair `γ, δ` is given explicitly). -/
@[dlmf 19.29.E5]
def ellRedU (a b : Fin 5 → ℂ) (x y : ℝ) (α β γ δ : Fin 5) : ℂ :=
  (ellRedRoot a b x α * ellRedRoot a b x β * ellRedRoot a b y γ * ellRedRoot a b y δ +
      ellRedRoot a b y α * ellRedRoot a b y β * ellRedRoot a b x γ * ellRedRoot a b x δ) /
    ((x : ℂ) - y)

/-- DLMF 19.29.6, case `x = ∞`:
`U_{αβ} = √b_α √b_β Y_γ Y_δ + Y_α Y_β √b_γ √b_δ`. -/
@[dlmf 19.29.E6]
def ellRedUInf (a b : Fin 5 → ℂ) (y : ℝ) (α β γ δ : Fin 5) : ℂ :=
  b α ^ (1 / 2 : ℂ) * b β ^ (1 / 2 : ℂ) * ellRedRoot a b y γ * ellRedRoot a b y δ +
    ellRedRoot a b y α * ellRedRoot a b y β * b γ ^ (1 / 2 : ℂ) * b δ ^ (1 / 2 : ℂ)

/-- DLMF 19.29.6, case `y = -∞`:
`U_{αβ} = X_α X_β √(-b_γ) √(-b_δ) + √(-b_α) √(-b_β) X_γ X_δ`. -/
@[dlmf 19.29.E6]
def ellRedUNegInf (a b : Fin 5 → ℂ) (x : ℝ) (α β γ δ : Fin 5) : ℂ :=
  ellRedRoot a b x α * ellRedRoot a b x β * (-b γ) ^ (1 / 2 : ℂ) * (-b δ) ^ (1 / 2 : ℂ) +
    (-b α) ^ (1 / 2 : ℂ) * (-b β) ^ (1 / 2 : ℂ) * ellRedRoot a b x γ * ellRedRoot a b x δ

/-- DLMF 19.29.9: `U_{α5}² = U_{αβ}² - d_{αγ} d_{αδ} d_{β5} / d_{α5}` (Lean index `4` for DLMF's
`5`). Only the square `U_{α5}²` enters (19.29.8). -/
@[dlmf 19.29.E9]
def ellRedU5Sq (a b : Fin 5 → ℂ) (x y : ℝ) (α β γ δ : Fin 5) : ℂ :=
  ellRedU a b x y α β γ δ ^ 2 -
    ellRedDet a b α γ * ellRedDet a b α δ * ellRedDet a b β 4 / ellRedDet a b α 4

/-- DLMF 19.29.9: `S_{α5} = (X_β X_γ X_δ Y_5² / X_α + Y_β Y_γ Y_δ X_5² / Y_α)/(x - y)`. -/
@[dlmf 19.29.E9]
def ellRedS5 (a b : Fin 5 → ℂ) (x y : ℝ) (α β γ δ : Fin 5) : ℂ :=
  (ellRedRoot a b x β * ellRedRoot a b x γ * ellRedRoot a b x δ / ellRedRoot a b x α *
        ellRedRoot a b y 4 ^ 2 +
      ellRedRoot a b y β * ellRedRoot a b y γ * ellRedRoot a b y δ / ellRedRoot a b y α *
        ellRedRoot a b x 4 ^ 2) / ((x : ℂ) - y)

/-- DLMF 19.29.9: `Q_{α5}² = (X_5 Y_5 / (X_α Y_α))² U_{α5}²` (DLMF defines
`Q_{α5} = X_5 Y_5 U_{α5} / (X_α Y_α)`; only its square enters (19.29.8)). -/
@[dlmf 19.29.E9]
def ellRedQ5Sq (a b : Fin 5 → ℂ) (x y : ℝ) (α β γ δ : Fin 5) : ℂ :=
  (ellRedRoot a b x 4 * ellRedRoot a b y 4 / (ellRedRoot a b x α * ellRedRoot a b y α)) ^ 2 *
    ellRedU5Sq a b x y α β γ δ

/-- The standing hypotheses of DLMF §19.29(i) for the four factors of `s(t)`: `y < x`,
`d_{αβ} ≠ 0` for distinct `α, β ≤ 4` (19.29.2), and each segment `a_α + b_α [y, x]` in
`ℂ \ (-∞, 0)`. -/
def EllRedHyp (a b : Fin 5 → ℂ) (x y : ℝ) : Prop :=
  y < x ∧ (∀ α β : Fin 5, α ≠ β → α ≠ 4 → β ≠ 4 → ellRedDet a b α β ≠ 0) ∧
    ∀ α : Fin 5, α ≠ 4 → ∀ t ∈ Icc y x, SymEllIntArg (a α + b α * t)

/-- `α, β, γ, δ` is a permutation of DLMF's `1, 2, 3, 4` (Lean `0, 1, 2, 3`). -/
def EllRedPerm (α β γ δ : Fin 5) : Prop :=
  ({α, β, γ, δ} : Finset (Fin 5)) = {0, 1, 2, 3}

/-! ### Algebraic identities (19.29.5), (19.29.9) -/

/-- Identity under the stated parameter and domain assumptions: `ellRedRoot a b x α ^ 2 = a α + b
α * x`. -/
lemma ei19e_root_sq {ι : Type*} (a b : ι → ℂ) (x : ℝ) (α : ι) :
    ellRedRoot a b x α ^ 2 = a α + b α * x := by
  rw [sq, ellRedRoot, ei19c_cpow_half_sq]

/-- DLMF 19.29.5: `U_{αβ} = U_{βα} = U_{γδ} = U_{δγ}` (also independent of the order of the
complementary pair). -/
@[dlmf 19.29.E5]
theorem ellRedU_symm (a b : Fin 5 → ℂ) (x y : ℝ) (α β γ δ : Fin 5) :
    ellRedU a b x y β α γ δ = ellRedU a b x y α β γ δ ∧
      ellRedU a b x y α β δ γ = ellRedU a b x y α β γ δ ∧
      ellRedU a b x y γ δ α β = ellRedU a b x y α β γ δ ∧
      ellRedU a b x y δ γ α β = ellRedU a b x y α β γ δ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [ellRedU] <;> ring

/-- DLMF 19.29.5: `U_{αβ}² - U_{αγ}² = d_{αδ} d_{βγ}`, for all complex coefficients and `x ≠ y`
(stronger than DLMF: no condition on the segments or on the `d`'s). -/
@[dlmf 19.29.E5]
theorem ellRedU_sq_sub_sq (a b : Fin 5 → ℂ) {x y : ℝ} (hxy : x ≠ y) (α β γ δ : Fin 5) :
    ellRedU a b x y α β γ δ ^ 2 - ellRedU a b x y α γ β δ ^ 2 =
      ellRedDet a b α δ * ellRedDet a b β γ := by
  have hd : (x : ℂ) - y ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hxy)
  have hXa := ei19e_root_sq a b x α
  have hXb := ei19e_root_sq a b x β
  have hXc := ei19e_root_sq a b x γ
  have hXd := ei19e_root_sq a b x δ
  have hYa := ei19e_root_sq a b y α
  have hYb := ei19e_root_sq a b y β
  have hYc := ei19e_root_sq a b y γ
  have hYd := ei19e_root_sq a b y δ
  simp only [ellRedU, ellRedDet, div_pow]
  rw [← sub_div, div_eq_iff (pow_ne_zero 2 hd)]
  set Xa := ellRedRoot a b x α; set Xb := ellRedRoot a b x β
  set Xc := ellRedRoot a b x γ; set Xd := ellRedRoot a b x δ
  set Ya := ellRedRoot a b y α; set Yb := ellRedRoot a b y β
  set Yc := ellRedRoot a b y γ; set Yd := ellRedRoot a b y δ
  linear_combination (Yd ^ 2 * (Xb * Yc - Xc * Yb) * (Xb * Yc + Xc * Yb)) * hXa +
    (Yc ^ 2 * (-Xd ^ 2 * Ya ^ 2 + Yd ^ 2 * a α + Yd ^ 2 * b α * x)) * hXb +
    (-Yb ^ 2 * (-Xd ^ 2 * Ya ^ 2 + Yd ^ 2 * a α + Yd ^ 2 * b α * x)) * hXc +
    (Ya ^ 2 * (Yb ^ 2 * a γ + Yb ^ 2 * b γ * x - Yc ^ 2 * a β - Yc ^ 2 * b β * x)) * hXd +
    ((a δ + b δ * x) * (Yb ^ 2 * a γ + Yb ^ 2 * b γ * x - Yc ^ 2 * a β - Yc ^ 2 * b β * x)) * hYa +
    ((a γ + b γ * x) * (-Yd ^ 2 * a α - Yd ^ 2 * b α * x + a α * a δ + a α * b δ * x +
      a δ * b α * y + b α * b δ * x * y)) * hYb +
    (-(a β + b β * x) * (-Yd ^ 2 * a α - Yd ^ 2 * b α * x + a α * a δ + a α * b δ * x +
      a δ * b α * y + b α * b δ * x * y)) * hYc +
    (-(a α + b α * x) * (x - y) * (a β * b γ - a γ * b β)) * hYd

/-- DLMF 19.29.9: the two expressions for `U_{α5}²` agree,
`U_{αβ}² - d_{αγ} d_{αδ} d_{β5}/d_{α5} = U_{βγ}² - d_{αβ} d_{αγ} d_{δ5}/d_{α5}`
(`U_{βγ} = U_{αδ}`), for `x ≠ y` and `d_{α5} ≠ 0`. -/
@[dlmf 19.29.E9]
theorem ellRedU5Sq_eq (a b : Fin 5 → ℂ) {x y : ℝ} (hxy : x ≠ y) (α β γ δ : Fin 5)
    (h5 : ellRedDet a b α 4 ≠ 0) :
    ellRedU5Sq a b x y α β γ δ =
      ellRedU a b x y β γ α δ ^ 2 -
        ellRedDet a b α β * ellRedDet a b α γ * ellRedDet a b δ 4 / ellRedDet a b α 4 := by
  have h1 := ellRedU_sq_sub_sq a b hxy α β δ γ
  have h2 : ellRedU a b x y β γ α δ = ellRedU a b x y α δ β γ := by
    simp only [ellRedU]; ring
  rw [ellRedU5Sq, h2]
  have h3 : ellRedU a b x y α β δ γ = ellRedU a b x y α β γ δ := (ellRedU_symm a b x y α β γ δ).2.1
  rw [h3] at h1
  have key : ellRedDet a b α β * ellRedDet a b α γ * ellRedDet a b δ 4 / ellRedDet a b α 4 -
      ellRedDet a b α γ * ellRedDet a b α δ * ellRedDet a b β 4 / ellRedDet a b α 4 =
      -(ellRedDet a b α γ * ellRedDet a b β δ) := by
    rw [div_sub_div_same, div_eq_iff h5]; simp only [ellRedDet]; ring
  linear_combination h1 + key

/-- Polynomial identity behind (19.29.9) (coefficients found by Gröbner reduction). -/
lemma ei19e_S5_aux (Xa Xb Xc Xd X5 Ya Yb Yc Yd Y5 aa ab ac ad a5 ba bb bc bd b5 x y : ℂ)
    (hxy : x - y ≠ 0) (hXa0 : Xa ≠ 0) (hYa0 : Ya ≠ 0) (h5 : aa * b5 - a5 * ba ≠ 0)
    (hXa : Xa ^ 2 = aa + ba * x) (hYa : Ya ^ 2 = aa + ba * y) (hXb : Xb ^ 2 = ab + bb * x) (hYb : Yb ^ 2 = ab + bb * y) (hXc : Xc ^ 2 = ac + bc * x) (hYc : Yc ^ 2 = ac + bc * y) (hXd : Xd ^ 2 = ad + bd * x) (hYd : Yd ^ 2 = ad + bd * y) (hX5 : X5 ^ 2 = a5 + b5 * x) (hY5 : Y5 ^ 2 = a5 + b5 * y) :
    ((Xb * Xc * Xd / Xa * Y5 ^ 2 + Yb * Yc * Yd / Ya * X5 ^ 2) / (x - y)) ^ 2 -
      (X5 * Y5 / (Xa * Ya)) ^ 2 * (((Xa * Xb * Yc * Yd + Ya * Yb * Xc * Xd) / (x - y)) ^ 2 -
        (aa * bc - ac * ba) * (aa * bd - ad * ba) * (ab * b5 - a5 * bb) / (aa * b5 - a5 * ba)) =
      (ab * b5 - a5 * bb) * (ac * b5 - a5 * bc) * (ad * b5 - a5 * bd) / (aa * b5 - a5 * ba) := by
  have hN : (aa * b5 - a5 * ba) * ((Xb * Xc * Xd * Y5 ^ 2 * Ya + Yb * Yc * Yd * X5 ^ 2 * Xa) ^ 2 -
      X5 ^ 2 * Y5 ^ 2 * (Xa * Xb * Yc * Yd + Ya * Yb * Xc * Xd) ^ 2) +
      X5 ^ 2 * Y5 ^ 2 * (x - y) ^ 2 * ((aa * bc - ac * ba) * (aa * bd - ad * ba) * (ab * b5 - a5 * bb)) -
      Xa ^ 2 * Ya ^ 2 * (x - y) ^ 2 * ((ab * b5 - a5 * bb) * (ac * b5 - a5 * bc) * (ad * b5 - a5 * bd)) = 0 := by
    linear_combination (-X5^4*Yb^2*Yc^2*Yd^2*a5*ba + X5^4*Yb^2*Yc^2*Yd^2*aa*b5 + X5^2*Xb^2*Y5^2*Yc^2*Yd^2*a5*ba - X5^2*Xb^2*Y5^2*Yc^2*Yd^2*aa*b5 + Ya^2*a5^3*bb*bc*bd*x^2 - 2*Ya^2*a5^3*bb*bc*bd*x*y + Ya^2*a5^3*bb*bc*bd*y^2 - Ya^2*a5^2*ab*b5*bc*bd*x^2 + 2*Ya^2*a5^2*ab*b5*bc*bd*x*y - Ya^2*a5^2*ab*b5*bc*bd*y^2 - Ya^2*a5^2*ac*b5*bb*bd*x^2 + 2*Ya^2*a5^2*ac*b5*bb*bd*x*y - Ya^2*a5^2*ac*b5*bb*bd*y^2 - Ya^2*a5^2*ad*b5*bb*bc*x^2 + 2*Ya^2*a5^2*ad*b5*bb*bc*x*y - Ya^2*a5^2*ad*b5*bb*bc*y^2 + Ya^2*a5*ab*ac*b5^2*bd*x^2 - 2*Ya^2*a5*ab*ac*b5^2*bd*x*y + Ya^2*a5*ab*ac*b5^2*bd*y^2 + Ya^2*a5*ab*ad*b5^2*bc*x^2 - 2*Ya^2*a5*ab*ad*b5^2*bc*x*y + Ya^2*a5*ab*ad*b5^2*bc*y^2 + Ya^2*a5*ac*ad*b5^2*bb*x^2 - 2*Ya^2*a5*ac*ad*b5^2*bb*x*y + Ya^2*a5*ac*ad*b5^2*bb*y^2 - Ya^2*ab*ac*ad*b5^3*x^2 + 2*Ya^2*ab*ac*ad*b5^3*x*y - Ya^2*ab*ac*ad*b5^3*y^2) * hXa + (X5^2*Xc^2*Xd^2*Y5^2*Yb^2*a5*ba - X5^2*Xc^2*Xd^2*Y5^2*Yb^2*aa*b5 - Xb^2*Xc^2*Xd^2*Y5^4*a5*ba + Xb^2*Xc^2*Xd^2*Y5^4*aa*b5 + a5^3*aa*bb*bc*bd*x^2 - 2*a5^3*aa*bb*bc*bd*x*y + a5^3*aa*bb*bc*bd*y^2 + a5^3*ba*bb*bc*bd*x^3 - 2*a5^3*ba*bb*bc*bd*x^2*y + a5^3*ba*bb*bc*bd*x*y^2 - a5^2*aa*ab*b5*bc*bd*x^2 + 2*a5^2*aa*ab*b5*bc*bd*x*y - a5^2*aa*ab*b5*bc*bd*y^2 - a5^2*aa*ac*b5*bb*bd*x^2 + 2*a5^2*aa*ac*b5*bb*bd*x*y - a5^2*aa*ac*b5*bb*bd*y^2 - a5^2*aa*ad*b5*bb*bc*x^2 + 2*a5^2*aa*ad*b5*bb*bc*x*y - a5^2*aa*ad*b5*bb*bc*y^2 - a5^2*ab*b5*ba*bc*bd*x^3 + 2*a5^2*ab*b5*ba*bc*bd*x^2*y - a5^2*ab*b5*ba*bc*bd*x*y^2 - a5^2*ac*b5*ba*bb*bd*x^3 + 2*a5^2*ac*b5*ba*bb*bd*x^2*y - a5^2*ac*b5*ba*bb*bd*x*y^2 - a5^2*ad*b5*ba*bb*bc*x^3 + 2*a5^2*ad*b5*ba*bb*bc*x^2*y - a5^2*ad*b5*ba*bb*bc*x*y^2 + a5*aa*ab*ac*b5^2*bd*x^2 - 2*a5*aa*ab*ac*b5^2*bd*x*y + a5*aa*ab*ac*b5^2*bd*y^2 + a5*aa*ab*ad*b5^2*bc*x^2 - 2*a5*aa*ab*ad*b5^2*bc*x*y + a5*aa*ab*ad*b5^2*bc*y^2 + a5*aa*ac*ad*b5^2*bb*x^2 - 2*a5*aa*ac*ad*b5^2*bb*x*y + a5*aa*ac*ad*b5^2*bb*y^2 + a5*ab*ac*b5^2*ba*bd*x^3 - 2*a5*ab*ac*b5^2*ba*bd*x^2*y + a5*ab*ac*b5^2*ba*bd*x*y^2 + a5*ab*ad*b5^2*ba*bc*x^3 - 2*a5*ab*ad*b5^2*ba*bc*x^2*y + a5*ab*ad*b5^2*ba*bc*x*y^2 + a5*ac*ad*b5^2*ba*bb*x^3 - 2*a5*ac*ad*b5^2*ba*bb*x^2*y + a5*ac*ad*b5^2*ba*bb*x*y^2 - aa*ab*ac*ad*b5^3*x^2 + 2*aa*ab*ac*ad*b5^3*x*y - aa*ab*ac*ad*b5^3*y^2 - ab*ac*ad*b5^3*ba*x^3 + 2*ab*ac*ad*b5^3*ba*x^2*y - ab*ac*ad*b5^3*ba*x*y^2) * hYa + (Y5^2*(a5*ba - aa*b5)*(X5^2*Yc^2*Yd^2*aa + X5^2*Yc^2*Yd^2*ba*x - Xc^2*Xd^2*Y5^2*aa - Xc^2*Xd^2*Y5^2*ba*y)) * hXb + (-X5^2*(a5*ba - aa*b5)*(X5^2*Yc^2*Yd^2*aa + X5^2*Yc^2*Yd^2*ba*x - Xc^2*Xd^2*Y5^2*aa - Xc^2*Xd^2*Y5^2*ba*y)) * hYb + (-Xd^2*Y5^2*(aa + ba*y)*(a5*ba - aa*b5)*(-X5^2*ab - X5^2*bb*y + Y5^2*ab + Y5^2*bb*x)) * hXc + (X5^2*Yd^2*(aa + ba*x)*(a5*ba - aa*b5)*(-X5^2*ab - X5^2*bb*y + Y5^2*ab + Y5^2*bb*x)) * hYc + (-Y5^2*(aa + ba*y)*(ac + bc*x)*(a5*ba - aa*b5)*(-X5^2*ab - X5^2*bb*y + Y5^2*ab + Y5^2*bb*x)) * hXd + (X5^2*(aa + ba*x)*(ac + bc*y)*(a5*ba - aa*b5)*(-X5^2*ab - X5^2*bb*y + Y5^2*ab + Y5^2*bb*x)) * hYd + (-X5^2*a5*aa*ab*ac*ad*ba - X5^2*a5*aa*ab*ac*ba*bd*y - X5^2*a5*aa*ab*ad*ba*bc*y - X5^2*a5*aa*ab*ba*bc*bd*y^2 - X5^2*a5*aa*ac*ad*ba*bb*y - X5^2*a5*aa*ac*ba*bb*bd*y^2 - X5^2*a5*aa*ad*ba*bb*bc*y^2 - X5^2*a5*aa*ba*bb*bc*bd*y^3 - X5^2*a5*ab*ac*ad*ba^2*x - X5^2*a5*ab*ac*ba^2*bd*x*y - X5^2*a5*ab*ad*ba^2*bc*x*y - X5^2*a5*ab*ba^2*bc*bd*x*y^2 - X5^2*a5*ac*ad*ba^2*bb*x*y - X5^2*a5*ac*ba^2*bb*bd*x*y^2 - X5^2*a5*ad*ba^2*bb*bc*x*y^2 - X5^2*a5*ba^2*bb*bc*bd*x*y^3 + X5^2*aa^2*ab*ac*ad*b5 + X5^2*aa^2*ab*ac*b5*bd*y + X5^2*aa^2*ab*ad*b5*bc*y + X5^2*aa^2*ab*b5*bc*bd*y^2 + X5^2*aa^2*ac*ad*b5*bb*y + X5^2*aa^2*ac*b5*bb*bd*y^2 + X5^2*aa^2*ad*b5*bb*bc*y^2 + X5^2*aa^2*b5*bb*bc*bd*y^3 + X5^2*aa*ab*ac*ad*b5*ba*x + X5^2*aa*ab*ac*b5*ba*bd*x*y + X5^2*aa*ab*ad*b5*ba*bc*x*y + X5^2*aa*ab*b5*ba*bc*bd*x*y^2 + X5^2*aa*ac*ad*b5*ba*bb*x*y + X5^2*aa*ac*b5*ba*bb*bd*x*y^2 + X5^2*aa*ad*b5*ba*bb*bc*x*y^2 + X5^2*aa*b5*ba*bb*bc*bd*x*y^3 - Y5^2*a5*aa^2*bb*bc*bd*x^2 + 2*Y5^2*a5*aa^2*bb*bc*bd*x*y - Y5^2*a5*aa^2*bb*bc*bd*y^2 + 2*Y5^2*a5*aa*ab*ac*ad*ba + Y5^2*a5*aa*ab*ac*ba*bd*x + Y5^2*a5*aa*ab*ac*ba*bd*y + Y5^2*a5*aa*ab*ad*ba*bc*x + Y5^2*a5*aa*ab*ad*ba*bc*y + Y5^2*a5*aa*ab*ba*bc*bd*x^2 + Y5^2*a5*aa*ab*ba*bc*bd*y^2 + Y5^2*a5*aa*ac*ad*ba*bb*x + Y5^2*a5*aa*ac*ad*ba*bb*y + Y5^2*a5*aa*ac*ba*bb*bd*x^2 + Y5^2*a5*aa*ac*ba*bb*bd*y^2 + Y5^2*a5*aa*ad*ba*bb*bc*x^2 + Y5^2*a5*aa*ad*ba*bb*bc*y^2 + Y5^2*a5*aa*ba*bb*bc*bd*x^2*y + Y5^2*a5*aa*ba*bb*bc*bd*x*y^2 + Y5^2*a5*ab*ac*ad*ba^2*x + Y5^2*a5*ab*ac*ad*ba^2*y + 2*Y5^2*a5*ab*ac*ba^2*bd*x*y + 2*Y5^2*a5*ab*ad*ba^2*bc*x*y + Y5^2*a5*ab*ba^2*bc*bd*x^2*y + Y5^2*a5*ab*ba^2*bc*bd*x*y^2 + 2*Y5^2*a5*ac*ad*ba^2*bb*x*y + Y5^2*a5*ac*ba^2*bb*bd*x^2*y + Y5^2*a5*ac*ba^2*bb*bd*x*y^2 + Y5^2*a5*ad*ba^2*bb*bc*x^2*y + Y5^2*a5*ad*ba^2*bb*bc*x*y^2 + 2*Y5^2*a5*ba^2*bb*bc*bd*x^2*y^2 - 2*Y5^2*aa^2*ab*ac*ad*b5 - Y5^2*aa^2*ab*ac*b5*bd*x - Y5^2*aa^2*ab*ac*b5*bd*y - Y5^2*aa^2*ab*ad*b5*bc*x - Y5^2*aa^2*ab*ad*b5*bc*y - 2*Y5^2*aa^2*ab*b5*bc*bd*x*y - Y5^2*aa^2*ac*ad*b5*bb*x - Y5^2*aa^2*ac*ad*b5*bb*y - 2*Y5^2*aa^2*ac*b5*bb*bd*x*y - 2*Y5^2*aa^2*ad*b5*bb*bc*x*y - Y5^2*aa^2*b5*bb*bc*bd*x^2*y - Y5^2*aa^2*b5*bb*bc*bd*x*y^2 - Y5^2*aa*ab*ac*ad*b5*ba*x - Y5^2*aa*ab*ac*ad*b5*ba*y - Y5^2*aa*ab*ac*b5*ba*bd*x^2 - Y5^2*aa*ab*ac*b5*ba*bd*y^2 - Y5^2*aa*ab*ad*b5*ba*bc*x^2 - Y5^2*aa*ab*ad*b5*ba*bc*y^2 - Y5^2*aa*ab*b5*ba*bc*bd*x^2*y - Y5^2*aa*ab*b5*ba*bc*bd*x*y^2 - Y5^2*aa*ac*ad*b5*ba*bb*x^2 - Y5^2*aa*ac*ad*b5*ba*bb*y^2 - Y5^2*aa*ac*b5*ba*bb*bd*x^2*y - Y5^2*aa*ac*b5*ba*bb*bd*x*y^2 - Y5^2*aa*ad*b5*ba*bb*bc*x^2*y - Y5^2*aa*ad*b5*ba*bb*bc*x*y^2 - 2*Y5^2*aa*b5*ba*bb*bc*bd*x^2*y^2 + Y5^2*ab*ac*ad*b5*ba^2*x^2 - 2*Y5^2*ab*ac*ad*b5*ba^2*x*y + Y5^2*ab*ac*ad*b5*ba^2*y^2 - a5^2*aa*ab*ac*ad*ba - a5^2*aa*ab*ac*ba*bd*y - a5^2*aa*ab*ad*ba*bc*y - a5^2*aa*ab*ba*bc*bd*y^2 - a5^2*aa*ac*ad*ba*bb*y - a5^2*aa*ac*ba*bb*bd*y^2 - a5^2*aa*ad*ba*bb*bc*y^2 - a5^2*aa*ba*bb*bc*bd*y^3 - a5^2*ab*ac*ad*ba^2*x - a5^2*ab*ac*ba^2*bd*x*y - a5^2*ab*ad*ba^2*bc*x*y - a5^2*ab*ba^2*bc*bd*x*y^2 - a5^2*ac*ad*ba^2*bb*x*y - a5^2*ac*ba^2*bb*bd*x*y^2 - a5^2*ad*ba^2*bb*bc*x*y^2 - a5^2*ba^2*bb*bc*bd*x*y^3 + a5*aa^2*ab*ac*ad*b5 + a5*aa^2*ab*ac*b5*bd*y + a5*aa^2*ab*ad*b5*bc*y + a5*aa^2*ab*b5*bc*bd*y^2 + a5*aa^2*ac*ad*b5*bb*y + a5*aa^2*ac*b5*bb*bd*y^2 + a5*aa^2*ad*b5*bb*bc*y^2 + a5*aa^2*b5*bb*bc*bd*y^3 - a5*ab*ac*ad*b5*ba^2*x^2 - a5*ab*ac*b5*ba^2*bd*x^2*y - a5*ab*ad*b5*ba^2*bc*x^2*y - a5*ab*b5*ba^2*bc*bd*x^2*y^2 - a5*ac*ad*b5*ba^2*bb*x^2*y - a5*ac*b5*ba^2*bb*bd*x^2*y^2 - a5*ad*b5*ba^2*bb*bc*x^2*y^2 - a5*b5*ba^2*bb*bc*bd*x^2*y^3 + aa^2*ab*ac*ad*b5^2*x + aa^2*ab*ac*b5^2*bd*x*y + aa^2*ab*ad*b5^2*bc*x*y + aa^2*ab*b5^2*bc*bd*x*y^2 + aa^2*ac*ad*b5^2*bb*x*y + aa^2*ac*b5^2*bb*bd*x*y^2 + aa^2*ad*b5^2*bb*bc*x*y^2 + aa^2*b5^2*bb*bc*bd*x*y^3 + aa*ab*ac*ad*b5^2*ba*x^2 + aa*ab*ac*b5^2*ba*bd*x^2*y + aa*ab*ad*b5^2*ba*bc*x^2*y + aa*ab*b5^2*ba*bc*bd*x^2*y^2 + aa*ac*ad*b5^2*ba*bb*x^2*y + aa*ac*b5^2*ba*bb*bd*x^2*y^2 + aa*ad*b5^2*ba*bb*bc*x^2*y^2 + aa*b5^2*ba*bb*bc*bd*x^2*y^3) * hX5 + (-Y5^2*a5*aa*ab*ac*ad*ba - Y5^2*a5*aa*ab*ac*ba*bd*x - Y5^2*a5*aa*ab*ad*ba*bc*x - Y5^2*a5*aa*ab*ba*bc*bd*x^2 - Y5^2*a5*aa*ac*ad*ba*bb*x - Y5^2*a5*aa*ac*ba*bb*bd*x^2 - Y5^2*a5*aa*ad*ba*bb*bc*x^2 - Y5^2*a5*aa*ba*bb*bc*bd*x^3 - Y5^2*a5*ab*ac*ad*ba^2*y - Y5^2*a5*ab*ac*ba^2*bd*x*y - Y5^2*a5*ab*ad*ba^2*bc*x*y - Y5^2*a5*ab*ba^2*bc*bd*x^2*y - Y5^2*a5*ac*ad*ba^2*bb*x*y - Y5^2*a5*ac*ba^2*bb*bd*x^2*y - Y5^2*a5*ad*ba^2*bb*bc*x^2*y - Y5^2*a5*ba^2*bb*bc*bd*x^3*y + Y5^2*aa^2*ab*ac*ad*b5 + Y5^2*aa^2*ab*ac*b5*bd*x + Y5^2*aa^2*ab*ad*b5*bc*x + Y5^2*aa^2*ab*b5*bc*bd*x^2 + Y5^2*aa^2*ac*ad*b5*bb*x + Y5^2*aa^2*ac*b5*bb*bd*x^2 + Y5^2*aa^2*ad*b5*bb*bc*x^2 + Y5^2*aa^2*b5*bb*bc*bd*x^3 + Y5^2*aa*ab*ac*ad*b5*ba*y + Y5^2*aa*ab*ac*b5*ba*bd*x*y + Y5^2*aa*ab*ad*b5*ba*bc*x*y + Y5^2*aa*ab*b5*ba*bc*bd*x^2*y + Y5^2*aa*ac*ad*b5*ba*bb*x*y + Y5^2*aa*ac*b5*ba*bb*bd*x^2*y + Y5^2*aa*ad*b5*ba*bb*bc*x^2*y + Y5^2*aa*b5*ba*bb*bc*bd*x^3*y - a5^2*aa^2*bb*bc*bd*x^2 + 2*a5^2*aa^2*bb*bc*bd*x*y - a5^2*aa^2*bb*bc*bd*y^2 + a5^2*aa*ab*ac*ad*ba + a5^2*aa*ab*ac*ba*bd*y + a5^2*aa*ab*ad*ba*bc*y + a5^2*aa*ab*ba*bc*bd*y^2 + a5^2*aa*ac*ad*ba*bb*y + a5^2*aa*ac*ba*bb*bd*y^2 + a5^2*aa*ad*ba*bb*bc*y^2 - a5^2*aa*ba*bb*bc*bd*x^3 + a5^2*aa*ba*bb*bc*bd*x^2*y + a5^2*aa*ba*bb*bc*bd*x*y^2 + a5^2*ab*ac*ad*ba^2*x + a5^2*ab*ac*ba^2*bd*x*y + a5^2*ab*ad*ba^2*bc*x*y + a5^2*ab*ba^2*bc*bd*x*y^2 + a5^2*ac*ad*ba^2*bb*x*y + a5^2*ac*ba^2*bb*bd*x*y^2 + a5^2*ad*ba^2*bb*bc*x*y^2 - a5^2*ba^2*bb*bc*bd*x^3*y + 2*a5^2*ba^2*bb*bc*bd*x^2*y^2 - a5*aa^2*ab*ac*ad*b5 - a5*aa^2*ab*ac*b5*bd*y - a5*aa^2*ab*ad*b5*bc*y + a5*aa^2*ab*b5*bc*bd*x^2 - 2*a5*aa^2*ab*b5*bc*bd*x*y - a5*aa^2*ac*ad*b5*bb*y + a5*aa^2*ac*b5*bb*bd*x^2 - 2*a5*aa^2*ac*b5*bb*bd*x*y + a5*aa^2*ad*b5*bb*bc*x^2 - 2*a5*aa^2*ad*b5*bb*bc*x*y + a5*aa^2*b5*bb*bc*bd*x^2*y - 2*a5*aa^2*b5*bb*bc*bd*x*y^2 + a5*aa*ab*ac*ad*b5*ba*x - a5*aa*ab*ac*ad*b5*ba*y + a5*aa*ab*ac*b5*ba*bd*x*y - a5*aa*ab*ac*b5*ba*bd*y^2 + a5*aa*ab*ad*b5*ba*bc*x*y - a5*aa*ab*ad*b5*ba*bc*y^2 + a5*aa*ab*b5*ba*bc*bd*x^3 - a5*aa*ab*b5*ba*bc*bd*x^2*y + a5*aa*ac*ad*b5*ba*bb*x*y - a5*aa*ac*ad*b5*ba*bb*y^2 + a5*aa*ac*b5*ba*bb*bd*x^3 - a5*aa*ac*b5*ba*bb*bd*x^2*y + a5*aa*ad*b5*ba*bb*bc*x^3 - a5*aa*ad*b5*ba*bb*bc*x^2*y + a5*aa*b5*ba*bb*bc*bd*x^3*y - a5*aa*b5*ba*bb*bc*bd*x^2*y^2 + 2*a5*ab*ac*ad*b5*ba^2*x^2 - a5*ab*ac*ad*b5*ba^2*x*y + 2*a5*ab*ac*b5*ba^2*bd*x^2*y - a5*ab*ac*b5*ba^2*bd*x*y^2 + 2*a5*ab*ad*b5*ba^2*bc*x^2*y - a5*ab*ad*b5*ba^2*bc*x*y^2 + a5*ab*b5*ba^2*bc*bd*x^3*y + 2*a5*ac*ad*b5*ba^2*bb*x^2*y - a5*ac*ad*b5*ba^2*bb*x*y^2 + a5*ac*b5*ba^2*bb*bd*x^3*y + a5*ad*b5*ba^2*bb*bc*x^3*y + a5*b5*ba^2*bb*bc*bd*x^3*y^2 - 2*aa^2*ab*ac*ad*b5^2*x + aa^2*ab*ac*ad*b5^2*y - aa^2*ab*ac*b5^2*bd*x^2 - aa^2*ab*ad*b5^2*bc*x^2 - aa^2*ab*b5^2*bc*bd*x^2*y - aa^2*ac*ad*b5^2*bb*x^2 - aa^2*ac*b5^2*bb*bd*x^2*y - aa^2*ad*b5^2*bb*bc*x^2*y - aa^2*b5^2*bb*bc*bd*x^2*y^2 - aa*ab*ac*ad*b5^2*ba*x^2 - aa*ab*ac*ad*b5^2*ba*x*y + aa*ab*ac*ad*b5^2*ba*y^2 - aa*ab*ac*b5^2*ba*bd*x^3 - aa*ab*ad*b5^2*ba*bc*x^3 - aa*ab*b5^2*ba*bc*bd*x^3*y - aa*ac*ad*b5^2*ba*bb*x^3 - aa*ac*b5^2*ba*bb*bd*x^3*y - aa*ad*b5^2*ba*bb*bc*x^3*y - aa*b5^2*ba*bb*bc*bd*x^3*y^2 + ab*ac*ad*b5^2*ba^2*x^3 - 2*ab*ac*ad*b5^2*ba^2*x^2*y + ab*ac*ad*b5^2*ba^2*x*y^2) * hY5
  have hM : Xa ^ 2 * Ya ^ 2 * (x - y) ^ 2 * (aa * b5 - a5 * ba) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hXa0) (pow_ne_zero 2 hYa0)) (pow_ne_zero 2 hxy)) h5
  rw [← sub_eq_zero]
  refine (mul_eq_zero.mp ?_).resolve_right hM
  have h5' : aa * b5 - ba * a5 ≠ 0 := by rwa [mul_comm ba a5]
  rw [← hN]
  field_simp
  ring

/-- DLMF 19.29.9: `S_{α5}² - Q_{α5}² = d_{β5} d_{γ5} d_{δ5} / d_{α5}`, for `x ≠ y`,
`X_α, Y_α ≠ 0` and `d_{α5} ≠ 0`. -/
@[dlmf 19.29.E9]
theorem ellRedS5_sq_sub_Q5Sq (a b : Fin 5 → ℂ) {x y : ℝ} (hxy : x ≠ y) (α β γ δ : Fin 5)
    (hX : ellRedRoot a b x α ≠ 0) (hY : ellRedRoot a b y α ≠ 0)
    (h5 : ellRedDet a b α 4 ≠ 0) :
    ellRedS5 a b x y α β γ δ ^ 2 - ellRedQ5Sq a b x y α β γ δ =
      ellRedDet a b β 4 * ellRedDet a b γ 4 * ellRedDet a b δ 4 / ellRedDet a b α 4 := by
  have hd : (x : ℂ) - y ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hxy)
  have H := ei19e_S5_aux (ellRedRoot a b x α) (ellRedRoot a b x β) (ellRedRoot a b x γ)
    (ellRedRoot a b x δ) (ellRedRoot a b x 4) (ellRedRoot a b y α) (ellRedRoot a b y β)
    (ellRedRoot a b y γ) (ellRedRoot a b y δ) (ellRedRoot a b y 4) (a α) (a β) (a γ) (a δ) (a 4)
    (b α) (b β) (b γ) (b δ) (b 4) x y hd hX hY h5
    (ei19e_root_sq a b x α) (ei19e_root_sq a b y α) (ei19e_root_sq a b x β)
    (ei19e_root_sq a b y β) (ei19e_root_sq a b x γ) (ei19e_root_sq a b y γ)
    (ei19e_root_sq a b x δ) (ei19e_root_sq a b y δ) (ei19e_root_sq a b x 4)
    (ei19e_root_sq a b y 4)
  simp only [ellRedS5, ellRedQ5Sq, ellRedU5Sq, ellRedU, ellRedDet]
  exact H

/-! ### Reduction theorems (19.29.4), (19.29.6)–(19.29.8) -/

/-- DLMF 19.29.4: `∫_y^x dt / s(t) = 2 R_F(U_{12}², U_{13}², U_{23}²)`, under the hypotheses
of §19.29(i) (`EllRedHyp`): complex coefficients, `d_{αβ} ≠ 0`, segments in `ℂ \ (-∞, 0)`. The
cubic case is `a_4 = 1`, `b_4 = 0`. -/
@[dlmf 19.29.E4]
theorem ellRed_integral_inv_s {a b : Fin 5 → ℂ} {x y : ℝ} (h : EllRedHyp a b x y) :
    ∫ t in Ioo y x, (ellRedS a b t)⁻¹ =
      2 * symEllIntRF (ellRedU a b x y 0 1 2 3 ^ 2) (ellRedU a b x y 0 2 1 3 ^ 2)
        (ellRedU a b x y 1 2 0 3 ^ 2) := by
  sorry

/-- DLMF 19.29.6 with (19.29.4), case `x = ∞`:
`∫_y^∞ dt / s(t) = 2 R_F(U_{12}², U_{13}², U_{23}²)` with `U_{αβ}` from (19.29.6)
(`ellRedUInf`); the `d_{αβ}` are nonzero and each ray `a_α + b_α [y, ∞)` lies in
`ℂ \ (-∞, 0)`. -/
@[dlmf 19.29.E6]
theorem ellRed_integral_inv_s_Ioi {a b : Fin 5 → ℂ} {y : ℝ}
    (hd : ∀ α β : Fin 5, α ≠ β → α ≠ 4 → β ≠ 4 → ellRedDet a b α β ≠ 0)
    (hseg : ∀ α : Fin 5, α ≠ 4 → ∀ t ∈ Ici y, SymEllIntArg (a α + b α * t)) :
    ∫ t in Ioi y, (ellRedS a b t)⁻¹ =
      2 * symEllIntRF (ellRedUInf a b y 0 1 2 3 ^ 2) (ellRedUInf a b y 0 2 1 3 ^ 2)
        (ellRedUInf a b y 1 2 0 3 ^ 2) := by
  sorry

/-- DLMF 19.29.6 with (19.29.4), case `y = -∞`:
`∫_{-∞}^x dt / s(t) = 2 R_F(U_{12}², U_{13}², U_{23}²)` with `U_{αβ}` from (19.29.6)
(`ellRedUNegInf`); the `d_{αβ}` are nonzero and each ray `a_α + b_α (-∞, x]` lies in
`ℂ \ (-∞, 0)`. -/
@[dlmf 19.29.E6]
theorem ellRed_integral_inv_s_Iio {a b : Fin 5 → ℂ} {x : ℝ}
    (hd : ∀ α β : Fin 5, α ≠ β → α ≠ 4 → β ≠ 4 → ellRedDet a b α β ≠ 0)
    (hseg : ∀ α : Fin 5, α ≠ 4 → ∀ t ∈ Iic x, SymEllIntArg (a α + b α * t)) :
    ∫ t in Iio x, (ellRedS a b t)⁻¹ =
      2 * symEllIntRF (ellRedUNegInf a b x 0 1 2 3 ^ 2) (ellRedUNegInf a b x 0 2 1 3 ^ 2)
        (ellRedUNegInf a b x 1 2 0 3 ^ 2) := by
  sorry

/-- DLMF 19.29.7: for a permutation `α, β, γ, δ` of the four factors and `U_{αδ} ≠ 0`,
`∫_y^x (a_α + b_α t)/(a_δ + b_δ t) dt / s(t) =
(2/3) d_{αβ} d_{αγ} R_D(U_{αβ}², U_{αγ}², U_{αδ}²) + 2 X_α Y_α / (X_δ Y_δ U_{αδ})`. -/
@[dlmf 19.29.E7]
theorem ellRed_integral_ratio_s {a b : Fin 5 → ℂ} {x y : ℝ} (h : EllRedHyp a b x y)
    {α β γ δ : Fin 5} (hp : EllRedPerm α β γ δ) (hU : ellRedU a b x y α δ β γ ≠ 0) :
    ∫ t in Ioo y x, (a α + b α * t) / (a δ + b δ * t) * (ellRedS a b t)⁻¹ =
      2 / 3 * ellRedDet a b α β * ellRedDet a b α γ *
          symEllIntRD (ellRedU a b x y α β γ δ ^ 2) (ellRedU a b x y α γ β δ ^ 2)
            (ellRedU a b x y α δ β γ ^ 2) +
        2 * ellRedRoot a b x α * ellRedRoot a b y α /
          (ellRedRoot a b x δ * ellRedRoot a b y δ * ellRedU a b x y α δ β γ) := by
  sorry

/-- DLMF 19.29.8: for a permutation `α, β, γ, δ` of the four factors, a fifth factor
`a_5 + b_5 t` (Lean index `4`) with `d_{α5} ≠ 0`, `U_{α5}² ≠ 0`, `Q_{α5}² ≠ 0` and
`S_{α5}² ∈ ℂ \ (-∞, 0)`,
`∫_y^x (a_α + b_α t)/(a_5 + b_5 t) dt / s(t) = (2/3) (d_{αβ} d_{αγ} d_{αδ}/d_{α5})
R_J(U_{12}², U_{13}², U_{23}², U_{α5}²) + 2 R_C(S_{α5}², Q_{α5}²)`.
`R_J` and `R_C` are DLMF's, so the Cauchy principal value is taken when `U_{α5}²` or `Q_{α5}²`
is real and negative, as DLMF prescribes. **Restriction:** the fifth factor is assumed nonzero
on `[y, x]`, so that the left side is an ordinary integral; DLMF's principal-value reading of
the left side when `a_5 + b_5 t` vanishes inside `(y, x)` is not covered. -/
@[dlmf 19.29.E8]
theorem ellRed_integral_ratio5_s {a b : Fin 5 → ℂ} {x y : ℝ} (h : EllRedHyp a b x y)
    {α β γ δ : Fin 5} (hp : EllRedPerm α β γ δ)
    (hd5 : ∀ ε : Fin 5, ε ≠ 4 → ellRedDet a b ε 4 ≠ 0)
    (h5 : ∀ t ∈ Icc y x, a 4 + b 4 * t ≠ 0)
    (hU5 : ellRedU5Sq a b x y α β γ δ ≠ 0) (hQ5 : ellRedQ5Sq a b x y α β γ δ ≠ 0)
    (hS5 : SymEllIntArg (ellRedS5 a b x y α β γ δ ^ 2)) :
    ∫ t in Ioo y x, (a α + b α * t) / (a 4 + b 4 * t) * (ellRedS a b t)⁻¹ =
      2 / 3 * (ellRedDet a b α β * ellRedDet a b α γ * ellRedDet a b α δ / ellRedDet a b α 4) *
          symEllIntRJ (ellRedU a b x y 0 1 2 3 ^ 2) (ellRedU a b x y 0 2 1 3 ^ 2)
            (ellRedU a b x y 1 2 0 3 ^ 2) (ellRedU5Sq a b x y α β γ δ) +
        2 * symEllIntRC (ellRedS5 a b x y α β γ δ ^ 2) (ellRedQ5Sq a b x y α β γ δ) := by
  sorry

/-- DLMF 19.29.10 (Gradshteyn–Ryzhik 3.142(2) as a cubic case of (19.29.7)): for real
`a > b > u > c`,
`∫_u^b √((a - t)/((b - t)(t - c)³)) dt = -(2/3)(a - b)(b - u)^{3/2}
R_D((a - b)(u - c), (b - c)(a - u), (a - b)(b - c)) + (2/(b - c)) √((a - u)(b - u)/(u - c))`. -/
@[dlmf 19.29.E10]
theorem ellRed_example_GR3142 {a b u c : ℝ} (hab : b < a) (hbu : u < b) (huc : c < u) :
    ((∫ t in Ioo u b, √((a - t) / ((b - t) * (t - c) ^ 3)) : ℝ) : ℂ) =
      -(2 / 3) * (a - b) * ((b - u : ℝ) : ℂ) ^ (3 / 2 : ℂ) *
          symEllIntRD ((a - b) * (u - c) : ℝ) ((b - c) * (a - u) : ℝ) ((a - b) * (b - c) : ℝ) +
        ((2 / (b - c) * √((a - u) * (b - u) / (u - c)) : ℝ) : ℂ) := by
  sorry

/-! ### Real positive factors: (19.29.4) from `lean-codes` -/

/-- Identity under the stated parameter and domain assumptions: `(r : ℂ) ^ (1 / 2 : ℂ) = ((√r : ℝ)
: ℂ)`. -/
lemma ei19e_cpow_half_ofReal {r : ℝ} (hr : 0 ≤ r) : (r : ℂ) ^ (1 / 2 : ℂ) = ((√r : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr]
  push_cast; rfl

/-- DLMF 19.29.4 for **real** coefficients with the four linear factors positive on `[y, x]`
(proved): `∫_y^x dt / s(t) = 2 R_F(U_{12}², U_{13}², U_{23}²)`. This is Carlson's (9.8-12),
`Carlson.integral_quartic_eq_carlsonRF` of `lean-codes`, transported to DLMF's notation. -/
@[dlmf 19.29.E4]
theorem ellRed_integral_inv_s_of_pos {a b : Fin 5 → ℝ} {x y : ℝ} (hxy : y < x)
    (hpos : ∀ α : Fin 5, α ≠ 4 → ∀ t ∈ Icc y x, 0 < a α + b α * t) :
    ∫ t in Ioo y x, (ellRedS (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) t)⁻¹ =
      2 * symEllIntRF (ellRedU (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) x y 0 1 2 3 ^ 2)
        (ellRedU (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) x y 0 2 1 3 ^ 2)
        (ellRedU (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) x y 1 2 0 3 ^ 2) := by
  have hp : ∀ i : Fin 5, i ≠ 4 → ∀ t ∈ Icc y x, 0 < a i + b i * t := hpos
  have h0 := hp 0 (by decide)
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have H := Carlson.integral_quartic_eq_carlsonRF (a := a 0) (α := b 0) (b := a 1) (β := b 1)
    (c := a 2) (γ := b 2) (d := a 3) (δ := b 3) hxy
    (fun t ht => ⟨h0 t ht, h1 t ht, h2 t ht, h3 t ht⟩)
  have hroot : ∀ (i : Fin 5) (t : ℝ), 0 ≤ a i + b i * t →
      ellRedRoot (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) t i = ((√(a i + b i * t) : ℝ) : ℂ) := by
    intro i t ht
    simp only [ellRedRoot]
    rw [show (a i : ℂ) + (b i : ℂ) * (t : ℂ) = ((a i + b i * t : ℝ) : ℂ) by push_cast; ring]
    exact ei19e_cpow_half_ofReal ht
  have hx : x ∈ Icc y x := ⟨hxy.le, le_rfl⟩
  have hy : y ∈ Icc y x := ⟨le_rfl, hxy.le⟩
  -- the integrand
  have hint : ∀ t ∈ Ioo y x, (ellRedS (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) t)⁻¹ =
      ((((a 0 + b 0 * t) * (a 1 + b 1 * t) * (a 2 + b 2 * t) * (a 3 + b 3 * t)) ^
        (-1 / 2 : ℝ) : ℝ) : ℂ) := by
    intro t ht
    have ht' : t ∈ Icc y x := Ioo_subset_Icc_self ht
    have q0 := h0 t ht'; have q1 := h1 t ht'; have q2 := h2 t ht'; have q3 := h3 t ht'
    simp only [ellRedS]
    rw [hroot 0 t q0.le, hroot 1 t q1.le, hroot 2 t q2.le, hroot 3 t q3.le,
      show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul q0.le]
    push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioo hint, integral_complex_ofReal, H]
  -- the arguments of `R_F`
  have hU : ∀ (i j k l : Fin 5), 0 < a i + b i * x → 0 < a j + b j * x → 0 < a k + b k * y →
      0 < a l + b l * y → 0 < a i + b i * y → 0 < a j + b j * y → 0 < a k + b k * x →
      0 < a l + b l * x →
      ellRedU (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) x y i j k l =
        (((√((a i + b i * x) * (a j + b j * x) * (a k + b k * y) * (a l + b l * y)) +
          √((a i + b i * y) * (a j + b j * y) * (a k + b k * x) * (a l + b l * x))) / (x - y) :
            ℝ) : ℂ) := by
    intro i j k l p1 p2 p3 p4 q1 q2 q3 q4
    simp only [ellRedU]
    rw [hroot i x p1.le, hroot j x p2.le, hroot k y p3.le, hroot l y p4.le, hroot i y q1.le,
      hroot j y q2.le, hroot k x q3.le, hroot l x q4.le,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul p1.le,
      Real.sqrt_mul (by positivity) (a l + b l * x), Real.sqrt_mul (by positivity),
      Real.sqrt_mul q1.le]
    push_cast; ring
  have hpos' : ∀ (i j k l : Fin 5), 0 < a i + b i * x → 0 < a j + b j * x →
      0 < a k + b k * y → 0 < a l + b l * y →
      0 < ((√((a i + b i * x) * (a j + b j * x) * (a k + b k * y) * (a l + b l * y)) +
          √((a i + b i * y) * (a j + b j * y) * (a k + b k * x) * (a l + b l * x))) / (x - y)) := by
    intro i j k l p1 p2 p3 p4
    have : 0 < x - y := sub_pos.mpr hxy
    have : 0 < √((a i + b i * x) * (a j + b j * x) * (a k + b k * y) * (a l + b l * y)) :=
      Real.sqrt_pos.mpr (by positivity)
    positivity
  rw [hU 0 1 2 3 (h0 x hx) (h1 x hx) (h2 y hy) (h3 y hy) (h0 y hy) (h1 y hy) (h2 x hx) (h3 x hx),
    hU 0 2 1 3 (h0 x hx) (h2 x hx) (h1 y hy) (h3 y hy) (h0 y hy) (h2 y hy) (h1 x hx) (h3 x hx),
    hU 1 2 0 3 (h1 x hx) (h2 x hx) (h0 y hy) (h3 y hy) (h1 y hy) (h2 y hy) (h0 x hx) (h3 x hx)]
  have e1 := hpos' 0 1 2 3 (h0 x hx) (h1 x hx) (h2 y hy) (h3 y hy)
  have e2 := hpos' 0 2 1 3 (h0 x hx) (h2 x hx) (h1 y hy) (h3 y hy)
  have e3 := hpos' 1 2 0 3 (h1 x hx) (h2 x hx) (h0 y hy) (h3 y hy)
  rw [← ofReal_pow, ← ofReal_pow, ← ofReal_pow,
    symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr (by positivity))
      (ofReal_mem_slitPlane.mpr (by positivity)) (ofReal_mem_slitPlane.mpr (by positivity))]
  congr 3 <;> ring_nf

/-! ### §19.29(ii) Reduction to basic integrals -/

/-- The integrand of (19.29.11):
`∏_{α=1}^{h} (a_α + b_α t)^{-1/2} ∏_{j=1}^{n} (a_j + b_j t)^{m_j}` (the first `h` of the `n`
linear factors carry the square roots; Lean indices `0, …, n-1`). -/
def ellRedIntegrand (h : ℕ) {n : ℕ} (a b : Fin n → ℂ) (m : Fin n → ℤ) (t : ℝ) : ℂ :=
  (∏ α ∈ Finset.univ.filter (fun α : Fin n => (α : ℕ) < h), (a α + b α * t) ^ (-1 / 2 : ℂ)) *
    ∏ j, (a j + b j * t) ^ (m j)

/-- DLMF 19.29.11: `I(𝐦) = ∫_y^x ∏_{α=1}^{h} (a_α + b_α t)^{-1/2} ∏_{j=1}^{n} (a_j + b_j t)^{m_j} dt`,
`x > y`, `h = 3` or `4`, `n ≥ h`, integer `m_j` (DLMF's rewriting of (19.2.3)). -/
@[dlmf 19.29.E11]
def ellRedI (h : ℕ) {n : ℕ} (a b : Fin n → ℂ) (x y : ℝ) (m : Fin n → ℤ) : ℂ :=
  ∫ t in Ioo y x, ellRedIntegrand h a b m t

/-- DLMF 19.29.12: the unit vector `𝐞_j` (`1` in the `j`th position, `0` elsewhere). -/
@[dlmf 19.29.E12]
def ellRedE {n : ℕ} (j : Fin n) : Fin n → ℤ := Pi.single j 1

/-- DLMF 19.29.12: `𝐦 = (m_1, …, m_n) = ∑_j m_j 𝐞_j`. -/
@[dlmf 19.29.E12]
theorem ellRedE_sum {n : ℕ} (m : Fin n → ℤ) : m = ∑ j, m j • ellRedE j := by
  funext k
  simp [ellRedE, Finset.sum_apply, Pi.single_apply]

/-- DLMF 19.29.13, 19.29.14: the index vectors of the basic integrals: `I(𝟎)`, `I(-𝐞_j)`
(`1 ≤ j ≤ n`) and, in the quartic case `h = 4`, also `I(𝐞_α)` (`1 ≤ α ≤ 4`). The integrals of
(19.29.4), (19.29.7), (19.29.8) are `I(𝟎)`, `I(𝐞_α - 𝐞_δ)`, `I(𝐞_α - 𝐞_5)` (19.29.ii.p1). -/
@[dlmf 19.29.E13, dlmf 19.29.E14]
def ellRedBasic (h n : ℕ) : Set (Fin n → ℤ) :=
  {0} ∪ Set.range (fun j : Fin n => -ellRedE j) ∪
    (if h = 4 then {m | ∃ α : Fin n, (α : ℕ) < 4 ∧ m = ellRedE α} else ∅)

/-- DLMF 19.29.ii.p3: `I(𝐦)` is a linear combination of basic integrals (19.29.13), (19.29.14)
and algebraic functions; the algebraic part is `[A(t)]_y^x` with `A(t) = s_h(t) P(t)/Q(t)`,
`s_h(t) = ∏_{α ≤ h} √(a_α + b_α t)` and polynomials `P`, `Q`, `Q` nonvanishing on `[y, x]`.
Stated with all `d_{jl} ≠ 0` (19.29.2), the radicands in `ℂ \ (-∞, 0]` and all factors nonzero
on `[y, x]` (so that every `I(𝐦)` is a proper integral). -/
@[dlmf 19.29.ii]
theorem ellRedI_reduction {h n : ℕ} (hh : h = 3 ∨ h = 4) (hn : h ≤ n) {a b : Fin n → ℂ}
    {x y : ℝ} (hxy : y < x) (hd : ∀ j l : Fin n, j ≠ l → ellRedDet a b j l ≠ 0)
    (hslit : ∀ α : Fin n, (α : ℕ) < h → ∀ t ∈ Icc y x, a α + b α * t ∈ slitPlane)
    (hnz : ∀ j : Fin n, ∀ t ∈ Icc y x, a j + b j * t ≠ 0) (m : Fin n → ℤ) :
    ∃ (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) (P Q : Polynomial ℂ),
      (↑S ⊆ ellRedBasic h n) ∧ (∀ t ∈ Icc y x, Q.eval (t : ℂ) ≠ 0) ∧
      ellRedI h a b x y m = ∑ k ∈ S, c k * ellRedI h a b x y k +
        ((∏ α ∈ Finset.univ.filter (fun α : Fin n => (α : ℕ) < h),
            (a α + b α * x) ^ (1 / 2 : ℂ)) * P.eval (x : ℂ) / Q.eval (x : ℂ) -
          (∏ α ∈ Finset.univ.filter (fun α : Fin n => (α : ℕ) < h),
            (a α + b α * y) ^ (1 / 2 : ℂ)) * P.eval (y : ℂ) / Q.eval (y : ℂ)) := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `∏ k, f k ^ ((Pi.single j q : Fin
n → ℤ) k) = f j ^ q`. -/
lemma ei19e_prod_single {n : ℕ} (f : Fin n → ℂ) (j : Fin n) (q : ℤ) :
    ∏ k, f k ^ ((Pi.single j q : Fin n → ℤ) k) = f j ^ q := by
  rw [Finset.prod_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
  simp

/-- Identity under the stated parameter and domain assumptions: `∏ k, f k ^ ((ellRedE l - ellRedE
j) k) = f l * (f j)⁻¹`. -/
lemma ei19e_prod_sub {n : ℕ} (f : Fin n → ℂ) {l j : Fin n} (hlj : l ≠ j) :
    ∏ k, f k ^ ((ellRedE l - ellRedE j) k) = f l * (f j)⁻¹ := by
  rw [← Finset.prod_subset (Finset.subset_univ {l, j}) (fun k _ hk => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [ellRedE, hk.1, hk.2]), Finset.prod_pair hlj]
  simp [ellRedE, hlj, hlj.symm]

/-- DLMF 19.29.15 (Carlson 1999, (2.19)): `b_j I(𝐞_l - 𝐞_j) = d_{lj} I(-𝐞_j) + b_l I(𝟎)`
(proved). DLMF leaves convergence implicit; here `I(-𝐞_j)` and `I(𝟎)` are assumed integrable
and `a_j + b_j t ≠ 0` on `(y, x)` (no other hypothesis, so also for `h` and `n` arbitrary). -/
@[dlmf 19.29.E15]
theorem ellRedI_partial_fraction {h n : ℕ} (a b : Fin n → ℂ) {x y : ℝ} (j l : Fin n)
    (hj : ∀ t ∈ Ioo y x, a j + b j * t ≠ 0)
    (hi1 : IntegrableOn (ellRedIntegrand h a b (-ellRedE j)) (Ioo y x))
    (hi0 : IntegrableOn (ellRedIntegrand h a b 0) (Ioo y x)) :
    b j * ellRedI h a b x y (ellRedE l - ellRedE j) =
      ellRedDet a b l j * ellRedI h a b x y (-ellRedE j) + b l * ellRedI h a b x y 0 := by
  simp only [ellRedI]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi1.const_mul _) (hi0.const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hf := hj t ht
  simp only [ellRedIntegrand]
  have h0 : ∏ k, (a k + b k * t) ^ ((0 : Fin n → ℤ) k) = 1 := by simp
  have h1 : ∏ k, (a k + b k * t) ^ ((-ellRedE j) k) = (a j + b j * t)⁻¹ := by
    rw [show (-ellRedE j : Fin n → ℤ) = Pi.single j (-1) by
      funext k; simp [ellRedE, Pi.single_apply]; split_ifs <;> simp]
    rw [ei19e_prod_single (fun k => a k + b k * t), zpow_neg_one]
  rw [h0, h1]
  by_cases hlj : l = j
  · subst hlj
    simp [ellRedDet]
  · rw [ei19e_prod_sub (fun k => a k + b k * t) hlj]
    set P := ∏ α ∈ Finset.univ.filter (fun α : Fin n => (α : ℕ) < h), (a α + b α * t) ^ (-1 / 2 : ℂ)
    have key : b j * (a l + b l * t) = ellRedDet a b l j + b l * (a j + b j * t) := by
      simp only [ellRedDet]; ring
    have hinv : (a j + b j * t) * (a j + b j * t)⁻¹ = 1 := mul_inv_cancel₀ hf
    linear_combination (P * (a j + b j * t)⁻¹) * key + (b l * P) * hinv

/-- DLMF 19.29.18 (Carlson 1999, (3.11)):
`b_j^q I(q 𝐞_l) = ∑_{r=0}^{q} \binom{q}{r} b_l^r d_{lj}^{q-r} I(r 𝐞_j)` for `q = 0, 1, 2, …`
(proved), assuming each `I(r 𝐞_j)`, `0 ≤ r ≤ q`, integrable (convergence is implicit in
DLMF); no other hypothesis. -/
@[dlmf 19.29.E18]
theorem ellRedI_recurrence {h n : ℕ} (a b : Fin n → ℂ) {x y : ℝ} (j l : Fin n) (q : ℕ)
    (hi : ∀ r ∈ Finset.range (q + 1),
      IntegrableOn (ellRedIntegrand h a b ((r : ℤ) • ellRedE j)) (Ioo y x)) :
    b j ^ q * ellRedI h a b x y ((q : ℤ) • ellRedE l) =
      ∑ r ∈ Finset.range (q + 1), (q.choose r : ℂ) * b l ^ r * ellRedDet a b l j ^ (q - r) *
        ellRedI h a b x y ((r : ℤ) • ellRedE j) := by
  simp only [ellRedI]
  rw [← integral_const_mul]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun r hr => (hi r hr).const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  have hsm : ∀ (i : Fin n) (p : ℕ), ((p : ℤ) • ellRedE i : Fin n → ℤ) = Pi.single i (p : ℤ) := by
    intro i p; funext k; simp [ellRedE, Pi.single_apply]
  simp only [ellRedIntegrand, hsm, ei19e_prod_single (fun k => a k + b k * t), zpow_natCast]
  have key : b j * (a l + b l * t) = b l * (a j + b j * t) + ellRedDet a b l j := by
    simp only [ellRedDet]; ring
  rw [← mul_assoc, mul_comm (b j ^ q), mul_assoc, ← mul_pow, key, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mul_pow]
  ring

/-- DLMF 19.29.17: `s(t) = ∏_{α=1}^{3} √(a_α + b_α t)` (cubic case). -/
@[dlmf 19.29.E17]
def ellRedS3 {n : ℕ} (a b : Fin n → ℂ) (t : ℝ) : ℂ :=
  ∏ α ∈ Finset.univ.filter (fun α : Fin n => (α : ℕ) < 3), (a α + b α * t) ^ (1 / 2 : ℂ)

/-- DLMF 19.29.16 (Carlson 1999, (3.5)), cubic case `h = 3`: for a permutation `α, β, γ` of
the three radicand indices,
`b_β b_γ I(𝐞_α) = d_{αβ} d_{αγ} I(-𝐞_α) + 2 b_α (s(x)/(a_α + b_α x) - s(y)/(a_α + b_α y))`,
with the three radicands in `ℂ \ (-∞, 0]` on `[y, x]`. -/
@[dlmf 19.29.E16]
theorem ellRedI_cubic_recurrence {n : ℕ} (a b : Fin n → ℂ) {x y : ℝ} (hxy : y < x)
    {α β γ : Fin n} (hα : (α : ℕ) < 3) (hβ : (β : ℕ) < 3) (hγ : (γ : ℕ) < 3)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hslit : ∀ ε : Fin n, (ε : ℕ) < 3 → ∀ t ∈ Icc y x, a ε + b ε * t ∈ slitPlane) :
    b β * b γ * ellRedI 3 a b x y (ellRedE α) =
      ellRedDet a b α β * ellRedDet a b α γ * ellRedI 3 a b x y (-ellRedE α) +
        2 * b α * (ellRedS3 a b x / (a α + b α * x) - ellRedS3 a b y / (a α + b α * y)) := by
  -- the three radicands and their square roots
  set r : Fin n → ℝ → ℂ := fun ε t => ellRedRoot a b t ε with hr_def
  have hf : ∀ ε : Fin n, (ε : ℕ) < 3 → ∀ t ∈ Icc y x, a ε + b ε * t ∈ slitPlane := hslit
  have hne : ∀ ε : Fin n, (ε : ℕ) < 3 → ∀ t ∈ Icc y x, r ε t ≠ 0 := by
    intro ε hε t ht h
    exact slitPlane_ne_zero (hf ε hε t ht) ((cpow_eq_zero_iff _ _).mp h).1
  have hsq : ∀ ε : Fin n, ∀ t : ℝ, r ε t ^ 2 = a ε + b ε * t := fun ε t => ei19e_root_sq a b t ε
  have hderiv : ∀ ε : Fin n, (ε : ℕ) < 3 → ∀ t ∈ Icc y x,
      HasDerivAt (r ε) (b ε / (2 * r ε t)) t := by
    intro ε hε t ht
    have hlin : HasDerivAt (fun t : ℝ => a ε + b ε * (t : ℂ)) (b ε) t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.const_mul (b ε)).const_add (a ε)
    have h := (Complex.hasStrictDerivAt_cpow_const (c := 1 / 2) (hf ε hε t ht)).hasDerivAt.comp
      t hlin
    have h0 := hne ε hε t ht
    refine h.congr_deriv ?_
    simp only [hr_def, ellRedRoot] at h0 ⊢
    rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, cpow_neg]
    field_simp
  have hcont : ∀ ε : Fin n, (ε : ℕ) < 3 → ContinuousOn (r ε) (Icc y x) :=
    fun ε hε t ht => (hderiv ε hε t ht).continuousAt.continuousWithinAt
  -- the product over the three radicand indices
  have hfilter : Finset.univ.filter (fun ε : Fin n => (ε : ℕ) < 3) = {α, β, γ} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro ε hε
      simp only [Finset.mem_insert, Finset.mem_singleton] at hε
      rcases hε with rfl | rfl | rfl <;> simpa
    · rw [Finset.card_insert_of_notMem (by simp [hαβ, hαγ]), Finset.card_pair hβγ]
      calc (Finset.univ.filter (fun ε : Fin n => (ε : ℕ) < 3)).card
          ≤ (Finset.range 3).card := Finset.card_le_card_of_injOn (fun ε => (ε : ℕ))
            (fun ε hε => by simpa using hε) (fun _ _ _ _ h => Fin.ext h)
        _ = 3 := Finset.card_range 3
  have hprod : ∀ (g : Fin n → ℂ), ∏ ε ∈ Finset.univ.filter (fun ε : Fin n => (ε : ℕ) < 3), g ε =
      g α * g β * g γ := by
    intro g
    rw [hfilter, Finset.prod_insert (by simp [hαβ, hαγ]), Finset.prod_pair hβγ, mul_assoc]
  -- the antiderivative and its derivative
  set G : ℝ → ℂ := fun t => r β t * r γ t / r α t with hG
  set D : ℝ → ℂ := fun t => ((b β / (2 * r β t)) * r γ t + r β t * (b γ / (2 * r γ t))) / r α t -
    r β t * r γ t * (b α / (2 * r α t)) / r α t ^ 2 with hD
  have hGd : ∀ t ∈ Icc y x, HasDerivAt G (D t) t := by
    intro t ht
    have := ((hderiv β hβ t ht).mul (hderiv γ hγ t ht)).div (hderiv α hα t ht) (hne α hα t ht)
    convert this using 1
    simp only [hD, Pi.mul_apply]
    have := hne α hα t ht
    have := hne β hβ t ht
    have := hne γ hγ t ht
    field_simp
  have hDc : ContinuousOn D (Icc y x) := by
    have hα' := hcont α hα; have hβ' := hcont β hβ; have hγ' := hcont γ hγ
    refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.div ?_ hα' fun t ht => hne α hα t ht
      refine ((continuousOn_const.div (continuousOn_const.mul hβ') fun t ht => ?_).mul hγ').add
        (hβ'.mul (continuousOn_const.div (continuousOn_const.mul hγ') fun t ht => ?_))
      · exact mul_ne_zero two_ne_zero (hne β hβ t ht)
      · exact mul_ne_zero two_ne_zero (hne γ hγ t ht)
    · refine ContinuousOn.div ((hβ'.mul hγ').mul (continuousOn_const.div
        (continuousOn_const.mul hα') fun t ht => mul_ne_zero two_ne_zero (hne α hα t ht)))
        (hα'.pow 2) fun t ht => pow_ne_zero 2 (hne α hα t ht)
  have hFTC : ∫ t in Ioo y x, D t = G x - G y := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hxy.le]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hGd t (by rwa [uIcc_of_le hxy.le] at ht))
      ((hDc.mono (by rw [uIcc_of_le hxy.le])).intervalIntegrable)
  -- the two integrands on `(y, x)`
  have hI1 : ∀ t ∈ Ioo y x, ellRedIntegrand 3 a b (ellRedE α) t =
      r α t ^ 2 * ((r α t)⁻¹ * (r β t)⁻¹ * (r γ t)⁻¹) := by
    intro t ht
    simp only [ellRedIntegrand, ellRedE, ei19e_prod_single (fun k => a k + b k * t), zpow_one]
    rw [hprod, hsq α t]
    simp only [hr_def, ellRedRoot, ei19c_inv_cpow_half]
    ring
  have hI2 : ∀ t ∈ Ioo y x, ellRedIntegrand 3 a b (-ellRedE α) t =
      (r α t ^ 2)⁻¹ * ((r α t)⁻¹ * (r β t)⁻¹ * (r γ t)⁻¹) := by
    intro t ht
    have hneg : (-ellRedE α : Fin n → ℤ) = Pi.single α (-1) := by
      funext k; simp [ellRedE, Pi.single_apply]; split_ifs <;> simp
    simp only [ellRedIntegrand, hneg, ei19e_prod_single (fun k => a k + b k * t), zpow_neg_one]
    rw [hprod, hsq α t]
    simp only [hr_def, ellRedRoot, ei19c_inv_cpow_half]
    ring
  have hinv : ∀ ε : Fin n, (ε : ℕ) < 3 → ContinuousOn (fun t => (r ε t)⁻¹) (Icc y x) :=
    fun ε hε => (hcont ε hε).inv₀ fun t ht => hne ε hε t ht
  have hcI1 : ContinuousOn (fun t => r α t ^ 2 * ((r α t)⁻¹ * (r β t)⁻¹ * (r γ t)⁻¹))
      (Icc y x) :=
    ((hcont α hα).pow 2).mul (((hinv α hα).mul (hinv β hβ)).mul (hinv γ hγ))
  have hcI2 : ContinuousOn (fun t => (r α t ^ 2)⁻¹ * ((r α t)⁻¹ * (r β t)⁻¹ * (r γ t)⁻¹))
      (Icc y x) :=
    (((hcont α hα).pow 2).inv₀ fun t ht => pow_ne_zero 2 (hne α hα t ht)).mul
      (((hinv α hα).mul (hinv β hβ)).mul (hinv γ hγ))
  have hint1 : IntegrableOn (ellRedIntegrand 3 a b (ellRedE α)) (Ioo y x) :=
    (hcI1.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
      (fun t ht => (hI1 t ht).symm) measurableSet_Ioo
  have hint2 : IntegrableOn (ellRedIntegrand 3 a b (-ellRedE α)) (Ioo y x) :=
    (hcI2.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
      (fun t ht => (hI2 t ht).symm) measurableSet_Ioo
  -- the pointwise identity
  have hpt : ∀ t ∈ Ioo y x, b β * b γ * ellRedIntegrand 3 a b (ellRedE α) t -
      ellRedDet a b α β * ellRedDet a b α γ * ellRedIntegrand 3 a b (-ellRedE α) t =
        2 * b α * D t := by
    intro t ht
    have ht' := Ioo_subset_Icc_self ht
    have h1 := hne α hα t ht'; have h2 := hne β hβ t ht'; have h3 := hne γ hγ t ht'
    rw [hI1 t ht, hI2 t ht]
    simp only [hD, ellRedDet]
    have sα := hsq α t; have sβ := hsq β t; have sγ := hsq γ t
    field_simp
    linear_combination (a α * b β * b γ + b α * b β * b γ * t - b α * b β * r γ t ^ 2 -
        b α * b γ * r β t ^ 2 + b β * b γ * r α t ^ 2) * sα +
      (-b α * (a α * b γ + b α * b γ * t - b α * r γ t ^ 2)) * sβ +
      (-b α * (a α * b β - a β * b α)) * sγ
  -- assemble
  have hxα : a α + b α * x ≠ 0 := slitPlane_ne_zero (hf α hα x ⟨hxy.le, le_rfl⟩)
  have hyα : a α + b α * y ≠ 0 := slitPlane_ne_zero (hf α hα y ⟨le_rfl, hxy.le⟩)
  have hGs : ∀ t ∈ Icc y x, ellRedS3 a b t / (a α + b α * t) = G t := by
    intro t ht
    have h1 := hne α hα t ht
    rw [div_eq_iff (slitPlane_ne_zero (hf α hα t ht))]
    conv_rhs => rw [← hsq α t]
    simp only [ellRedS3, hprod, hG]
    simp only [hr_def, ellRedRoot] at h1 ⊢
    field_simp
  rw [hGs x ⟨hxy.le, le_rfl⟩, hGs y ⟨le_rfl, hxy.le⟩, ← hFTC, ← integral_const_mul,
    ← sub_eq_iff_eq_add', ellRedI, ellRedI, ← integral_const_mul,
    ← integral_const_mul, ← integral_sub (hint1.const_mul _) (hint2.const_mul _)]
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => hpt t ht

/-! ### §19.29(iii) Examples -/

/-- DLMF 19.29.22: `U` defined by `(x² - y²) U = x √(Q₁(y) Q₂(y)) + y √(Q₁(x) Q₂(x))`,
`Q_j(t) = a_j + b_j t²`. -/
@[dlmf 19.29.E22]
def ellRedQuadU (a₁ b₁ a₂ b₂ x y : ℝ) : ℝ :=
  (x * √((a₁ + b₁ * y ^ 2) * (a₂ + b₂ * y ^ 2)) + y * √((a₁ + b₁ * x ^ 2) * (a₂ + b₂ * x ^ 2))) /
    (x ^ 2 - y ^ 2)

/-- DLMF 19.29.19: with `Q_j(t) = a_j + b_j t²` positive for `0 ≤ y < t < x`,
`∫_y^x dt / √(Q₁(t) Q₂(t)) = R_F(U² + a₁b₂, U² + a₂b₁, U²)` (replaces (19.14.4)–(19.14.10)). -/
@[dlmf 19.29.E19]
theorem ellRed_quad_first {a₁ b₁ a₂ b₂ x y : ℝ} (hy : 0 ≤ y) (hxy : y < x)
    (hQ : ∀ t ∈ Ioo y x, 0 < a₁ + b₁ * t ^ 2 ∧ 0 < a₂ + b₂ * t ^ 2)
    (hint : IntegrableOn (fun t => 1 / √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2))) (Ioo y x)) :
    ((∫ t in Ioo y x, 1 / √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)) : ℝ) : ℂ) =
      symEllIntRF (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₁ * b₂ : ℝ)
        (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₂ * b₁ : ℝ) (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 : ℝ) := by
  sorry

/-- The algebra behind the positivity of the arguments in (19.29.19): with
`(x² - y²) U = x P₁(y) P₂(y) + y P₁(x) P₂(x)` and `(x² - y²) W = x P₁(x) P₂(y) + y P₁(y) P₂(x)`,
`P_j(t)² = a_j + b_j t²`, one has `W² - U² = a₂ b₁` (`U_{12}² - U_{14}² = d_{13} d_{24}`, 19.29.5). -/
lemma ei19e_quad_sq_sub_sq {a₁ b₁ a₂ b₂ x y p₁ q₁ p₂ q₂ : ℝ} (hxy : x ^ 2 - y ^ 2 ≠ 0)
    (h₁ : p₁ ^ 2 = a₁ + b₁ * x ^ 2) (h₂ : p₂ ^ 2 = a₂ + b₂ * x ^ 2)
    (k₁ : q₁ ^ 2 = a₁ + b₁ * y ^ 2) (k₂ : q₂ ^ 2 = a₂ + b₂ * y ^ 2) :
    ((x * p₁ * q₂ + y * q₁ * p₂) / (x ^ 2 - y ^ 2)) ^ 2 =
      ((x * (q₁ * q₂) + y * (p₁ * p₂)) / (x ^ 2 - y ^ 2)) ^ 2 + a₂ * b₁ := by
  rw [div_pow, div_pow, div_add' _ _ _ (pow_ne_zero 2 hxy), div_left_inj' (pow_ne_zero 2 hxy)]
  linear_combination (x ^ 2 * q₂ ^ 2 - y ^ 2 * p₂ ^ 2) * h₁ - (x ^ 2 * q₂ ^ 2 - y ^ 2 * p₂ ^ 2) * k₁ +
    (-(b₁ * (x ^ 2 - y ^ 2)) * y ^ 2) * h₂ + (b₁ * (x ^ 2 - y ^ 2) * x ^ 2) * k₂

/-- DLMF 19.29.19 for `0 < y` and both `Q_j` positive on `[y, x]` (proved): Carlson's
Exercise 9.8-3, `Carlson.integral_quadratic_mul_quadratic` of `lean-codes`, in DLMF's notation;
the arguments of `R_F` are positive (`ei19e_quad_sq_sub_sq`). -/
@[dlmf 19.29.E19]
theorem ellRed_quad_first_of_pos {a₁ b₁ a₂ b₂ x y : ℝ} (hy : 0 < y) (hxy : y < x)
    (hQ : ∀ t ∈ Icc y x, 0 < a₁ + b₁ * t ^ 2 ∧ 0 < a₂ + b₂ * t ^ 2) :
    ((∫ t in Ioo y x, 1 / √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)) : ℝ) : ℂ) =
      symEllIntRF (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₁ * b₂ : ℝ)
        (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₂ * b₁ : ℝ) (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 : ℝ) := by
  have H := Carlson.integral_quadratic_mul_quadratic (a := b₁) (c := a₁) (α := b₂) (γ := a₂)
    hy hxy (fun t ht => by obtain ⟨h1, h2⟩ := hQ t ht; exact ⟨by linarith, by linarith⟩)
  have e1 : ∀ t : ℝ, (b₁ * t ^ 2 + a₁) * (b₂ * t ^ 2 + a₂) = (a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2) :=
    fun t => by ring
  simp only [e1] at H
  have hx0 : 0 < x := hy.trans hxy
  have hd : 0 < x ^ 2 - y ^ 2 := by nlinarith
  obtain ⟨px1, px2⟩ := hQ x ⟨hxy.le, le_rfl⟩
  obtain ⟨py1, py2⟩ := hQ y ⟨le_rfl, hxy.le⟩
  have hU : 0 < ellRedQuadU a₁ b₁ a₂ b₂ x y := by
    unfold ellRedQuadU
    have : 0 < √((a₁ + b₁ * y ^ 2) * (a₂ + b₂ * y ^ 2)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  -- the two other arguments are squares of positive numbers
  have hsq : ∀ {c₁ d₁ c₂ d₂ : ℝ}, 0 < c₁ + d₁ * x ^ 2 → 0 < c₂ + d₂ * x ^ 2 →
      0 < c₁ + d₁ * y ^ 2 → 0 < c₂ + d₂ * y ^ 2 →
      0 < ellRedQuadU c₁ d₁ c₂ d₂ x y ^ 2 + c₂ * d₁ := by
    intro c₁ d₁ c₂ d₂ g1 g2 g3 g4
    unfold ellRedQuadU
    rw [Real.sqrt_mul g3.le, Real.sqrt_mul g1.le, ← ei19e_quad_sq_sub_sq hd.ne'
      (Real.sq_sqrt g1.le) (Real.sq_sqrt g2.le) (Real.sq_sqrt g3.le) (Real.sq_sqrt g4.le)]
    have := Real.sqrt_pos.mpr g1; have := Real.sqrt_pos.mpr g4
    positivity
  have hB : 0 < ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₂ * b₁ := hsq px1 px2 py1 py2
  have hA : 0 < ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₁ * b₂ := by
    have := hsq (c₁ := a₂) (d₁ := b₂) (c₂ := a₁) (d₂ := b₁) px2 px1 py2 py1
    have e : ellRedQuadU a₂ b₂ a₁ b₁ x y = ellRedQuadU a₁ b₁ a₂ b₂ x y := by
      unfold ellRedQuadU; rw [mul_comm (a₂ + _), mul_comm (a₂ + b₂ * x ^ 2)]
    rwa [e] at this
  have hint : ∀ t ∈ Ioo y x, 1 / √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)) =
      ((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)) ^ (-1 / 2 : ℝ) := by
    intro t ht
    obtain ⟨q1, q2⟩ := hQ t (Ioo_subset_Icc_self ht)
    rw [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num,
      Real.rpow_neg (by positivity), one_div]
  rw [setIntegral_congr_fun measurableSet_Ioo hint, H]
  rw [symEllIntRF_comm_left, symEllIntRF_comm_right, symEllIntRF_comm_left,
    symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr (by positivity))
      (ofReal_mem_slitPlane.mpr hB) (ofReal_mem_slitPlane.mpr hA)]
  unfold ellRedQuadU
  rw [mul_comm a₂ b₁]

/-- DLMF 19.29.20: with the hypotheses of (19.29.19) and `U ≠ 0`,
`∫_y^x t² dt / √(Q₁(t) Q₂(t)) = (1/3) a₁ a₂ R_D(U² + a₁b₂, U² + a₂b₁, U²) + xy/U`. -/
@[dlmf 19.29.E20]
theorem ellRed_quad_second {a₁ b₁ a₂ b₂ x y : ℝ} (hy : 0 ≤ y) (hxy : y < x)
    (hQ : ∀ t ∈ Ioo y x, 0 < a₁ + b₁ * t ^ 2 ∧ 0 < a₂ + b₂ * t ^ 2)
    (hint : IntegrableOn (fun t => t ^ 2 / √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2))) (Ioo y x))
    (hU : ellRedQuadU a₁ b₁ a₂ b₂ x y ≠ 0) :
    ((∫ t in Ioo y x, t ^ 2 / √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)) : ℝ) : ℂ) =
      1 / 3 * a₁ * a₂ * symEllIntRD (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₁ * b₂ : ℝ)
          (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₂ * b₁ : ℝ) (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 : ℝ) +
        ((x * y / ellRedQuadU a₁ b₁ a₂ b₂ x y : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.29.21: with the hypotheses of (19.29.19), `U ≠ 0` and `y > 0` (needed for
convergence at `t = 0`),
`∫_y^x dt / (t² √(Q₁(t) Q₂(t))) = (1/3) b₁ b₂ R_D(U² + a₁b₂, U² + a₂b₁, U²) + (xyU)⁻¹`. -/
@[dlmf 19.29.E21]
theorem ellRed_quad_third {a₁ b₁ a₂ b₂ x y : ℝ} (hy : 0 < y) (hxy : y < x)
    (hQ : ∀ t ∈ Ioo y x, 0 < a₁ + b₁ * t ^ 2 ∧ 0 < a₂ + b₂ * t ^ 2)
    (hint : IntegrableOn (fun t => 1 / (t ^ 2 * √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2))))
      (Ioo y x))
    (hU : ellRedQuadU a₁ b₁ a₂ b₂ x y ≠ 0) :
    ((∫ t in Ioo y x, 1 / (t ^ 2 * √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2))) : ℝ) : ℂ) =
      1 / 3 * b₁ * b₂ * symEllIntRD (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₁ * b₂ : ℝ)
          (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₂ * b₁ : ℝ) (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 : ℝ) +
        (((x * y * ellRedQuadU a₁ b₁ a₂ b₂ x y)⁻¹ : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.29.iii.p1: when both square roots in (19.29.22) vanish (`U = 0`), the integrals of
(19.29.20) and (19.29.21) are `R_G(a₁b₂, a₂b₁, 0)` times `-2/(b₁b₂)` and `-2/(a₁a₂)`, by
(19.27.8). Stated with `0 < y` (for the second integral) and `b₁ b₂ ≠ 0`, `a₁ a₂ ≠ 0`. -/
@[dlmf 19.29.iii]
theorem ellRed_quad_degenerate {a₁ b₁ a₂ b₂ x y : ℝ} (hy : 0 < y) (hxy : y < x)
    (hQ : ∀ t ∈ Ioo y x, 0 < a₁ + b₁ * t ^ 2 ∧ 0 < a₂ + b₂ * t ^ 2)
    (hy0 : (a₁ + b₁ * y ^ 2) * (a₂ + b₂ * y ^ 2) = 0)
    (hx0 : (a₁ + b₁ * x ^ 2) * (a₂ + b₂ * x ^ 2) = 0) (hb : b₁ * b₂ ≠ 0) (ha : a₁ * a₂ ≠ 0)
    (hint₁ : IntegrableOn (fun t => t ^ 2 / √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2))) (Ioo y x))
    (hint₂ : IntegrableOn (fun t => 1 / (t ^ 2 * √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2))))
      (Ioo y x)) :
    ((∫ t in Ioo y x, t ^ 2 / √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)) : ℝ) : ℂ) =
        -2 / (b₁ * b₂) * symEllIntRG (a₁ * b₂ : ℝ) (a₂ * b₁ : ℝ) 0 ∧
      ((∫ t in Ioo y x, 1 / (t ^ 2 * √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2))) : ℝ) : ℂ) =
        -2 / (a₁ * a₂) * symEllIntRG (a₁ * b₂ : ℝ) (a₂ * b₁ : ℝ) 0 := by
  sorry

/-- DLMF 19.29.23 (the case `x = ∞` of (19.29.19), `U` found by taking the limit): for
`0 ≤ b ≤ y`, `0 < y`,
`∫_y^∞ dt / √((t² + a²)(t² - b²)) = R_F(y² + a², y² - b², y²)`. -/
@[dlmf 19.29.E23]
theorem ellRed_quad_infinite {a b y : ℝ} (hb : 0 ≤ b) (hby : b ≤ y) (hy : 0 < y) :
    ((∫ t in Ioi y, 1 / √((t ^ 2 + a ^ 2) * (t ^ 2 - b ^ 2)) : ℝ) : ℂ) =
      symEllIntRF (y ^ 2 + a ^ 2 : ℝ) (y ^ 2 - b ^ 2 : ℝ) (y ^ 2 : ℝ) := by
  sorry

/-- DLMF 19.29.25: `S_j = (√Q_j(x) + √Q_j(y))² - h_j (x - y)²` for
`Q_j(t) = f_j + g_j t + h_j t²`. -/
@[dlmf 19.29.E25]
def ellRedQuadS (f g h x y : ℝ) : ℝ :=
  (√(f + g * x + h * x ^ 2) + √(f + g * y + h * y ^ 2)) ^ 2 - h * (x - y) ^ 2

/-- DLMF 19.29.25: `D_{jl} = 2 f_j h_l + 2 h_j f_l - g_j g_l`. -/
@[dlmf 19.29.E25]
def ellRedQuadD (f₁ g₁ h₁ f₂ g₂ h₂ : ℝ) : ℝ := 2 * f₁ * h₂ + 2 * h₁ * f₂ - g₁ * g₂

/-- DLMF 19.29.24 with 19.29.25: the right side `4 R_F(U, U + D₁₂ + V, U + D₁₂ - V)` with
`(x - y)² U = S₁ S₂` and `V = √(D₁₂² - D₁₁ D₂₂)` (principal complex square root: the
variables of `R_F` are real and nonnegative unless both quadratics have real zeros and those of
`Q₁` interlace those of `Q₂`, 19.29.iii.p2). -/
@[dlmf 19.29.E24, dlmf 19.29.E25]
def ellRedQuadRF (S₁ S₂ D₁₁ D₁₂ D₂₂ x y : ℝ) : ℂ :=
  4 * symEllIntRF (S₁ * S₂ / (x - y) ^ 2 : ℝ)
    ((S₁ * S₂ / (x - y) ^ 2 + D₁₂ : ℝ) + ((D₁₂ ^ 2 - D₁₁ * D₂₂ : ℝ) : ℂ) ^ (1 / 2 : ℂ))
    ((S₁ * S₂ / (x - y) ^ 2 + D₁₂ : ℝ) - ((D₁₂ ^ 2 - D₁₁ * D₂₂ : ℝ) : ℂ) ^ (1 / 2 : ℂ))

/-- DLMF 19.29.24: for `Q_j(t) = f_j + g_j t + h_j t²` both positive on `(y, x)`,
`∫_y^x dt / √(Q₁(t) Q₂(t)) = 4 R_F(U, U + D₁₂ + V, U + D₁₂ - V)` with (19.29.25). -/
@[dlmf 19.29.E24]
theorem ellRed_two_quadratics {f₁ g₁ h₁ f₂ g₂ h₂ x y : ℝ} (hxy : y < x)
    (hQ : ∀ t ∈ Ioo y x, 0 < f₁ + g₁ * t + h₁ * t ^ 2 ∧ 0 < f₂ + g₂ * t + h₂ * t ^ 2)
    (hint : IntegrableOn
      (fun t => 1 / √((f₁ + g₁ * t + h₁ * t ^ 2) * (f₂ + g₂ * t + h₂ * t ^ 2))) (Ioo y x)) :
    ((∫ t in Ioo y x,
        1 / √((f₁ + g₁ * t + h₁ * t ^ 2) * (f₂ + g₂ * t + h₂ * t ^ 2)) : ℝ) : ℂ) =
      ellRedQuadRF (ellRedQuadS f₁ g₁ h₁ x y) (ellRedQuadS f₂ g₂ h₂ x y)
        (ellRedQuadD f₁ g₁ h₁ f₁ g₁ h₁) (ellRedQuadD f₁ g₁ h₁ f₂ g₂ h₂)
        (ellRedQuadD f₂ g₂ h₂ f₂ g₂ h₂) x y := by
  sorry

/-- Estimate under the stated parameter and domain assumptions: `0 ≤ c + d * x ∧ 0 ≤ c + d * y`. -/
lemma ei19e_endpoints_nonneg {c d x y : ℝ} (hxy : y < x) (h : ∀ t ∈ Ioo y x, 0 < c + d * t) :
    0 ≤ c + d * x ∧ 0 ≤ c + d * y := by
  have hc : IsClosed {t : ℝ | 0 ≤ c + d * t} :=
    isClosed_le continuous_const (continuous_const.add (continuous_const.mul continuous_id))
  have hsub : Icc y x ⊆ {t : ℝ | 0 ≤ c + d * t} := by
    rw [← closure_Ioo hxy.ne]
    exact hc.closure_subset_iff.mpr fun t ht => (h t ht).le
  exact ⟨hsub ⟨hxy.le, le_rfl⟩, hsub ⟨le_rfl, hxy.le⟩⟩

/-- DLMF 19.29.26: if `Q₁(t) = (a₁ + b₁ t)(a₂ + b₂ t)` with both linear factors positive on
`(y, x)` (hence on `[y, x]` nonnegative), then `S₁ = (X₁ Y₂ + Y₁ X₂)²`; the algebraic part
(proved): this agrees with `S₁` of (19.29.25) for `Q₁ = a₁a₂ + (a₁b₂ + a₂b₁) t + b₁b₂ t²`. -/
@[dlmf 19.29.E26]
theorem ellRedQuadS_linear_mul {a₁ b₁ a₂ b₂ x y : ℝ} (hx₁ : 0 ≤ a₁ + b₁ * x)
    (hx₂ : 0 ≤ a₂ + b₂ * x) (hy₁ : 0 ≤ a₁ + b₁ * y) (hy₂ : 0 ≤ a₂ + b₂ * y) :
    ellRedQuadS (a₁ * a₂) (a₁ * b₂ + a₂ * b₁) (b₁ * b₂) x y =
      (√(a₁ + b₁ * x) * √(a₂ + b₂ * y) + √(a₁ + b₁ * y) * √(a₂ + b₂ * x)) ^ 2 := by
  have e : ∀ t : ℝ, a₁ * a₂ + (a₁ * b₂ + a₂ * b₁) * t + b₁ * b₂ * t ^ 2 =
      (a₁ + b₁ * t) * (a₂ + b₂ * t) := fun t => by ring
  simp only [ellRedQuadS, e, Real.sqrt_mul hx₁, Real.sqrt_mul hy₁]
  have s1 := Real.sq_sqrt hx₁; have s2 := Real.sq_sqrt hx₂
  have s3 := Real.sq_sqrt hy₁; have s4 := Real.sq_sqrt hy₂
  linear_combination (√(a₂ + b₂ * x) - √(a₂ + b₂ * y)) * (√(a₂ + b₂ * x) + √(a₂ + b₂ * y)) * s1 +
    (-√(a₁ + b₁ * y) ^ 2 + a₁ + b₁ * x) * s2 + (√(a₂ + b₂ * y) ^ 2 - a₂ - b₂ * x) * s3 +
    (-b₁ * (x - y)) * s4

/-- DLMF 19.29.26: for `Q₁(t) = (a₁ + b₁ t)(a₂ + b₂ t)`, both factors positive on `(y, x)`, and
`Q₂(t) = f₂ + g₂ t + h₂ t²` positive on `(y, x)`, (19.29.24) holds with
`S₁ = (X₁Y₂ + Y₁X₂)²`, `D₁₂ = 2a₁a₂h₂ + 2b₁b₂f₂ - (a₁b₂ + a₂b₁)g₂`, `D₁₁ = -(a₁b₂ - a₂b₁)²`.
Derived from (19.29.24). -/
@[dlmf 19.29.E26]
theorem ellRed_linear_linear_quadratic {a₁ b₁ a₂ b₂ f₂ g₂ h₂ x y : ℝ} (hxy : y < x)
    (hQ : ∀ t ∈ Ioo y x, 0 < a₁ + b₁ * t ∧ 0 < a₂ + b₂ * t ∧ 0 < f₂ + g₂ * t + h₂ * t ^ 2)
    (hint : IntegrableOn
      (fun t => 1 / √((a₁ + b₁ * t) * (a₂ + b₂ * t) * (f₂ + g₂ * t + h₂ * t ^ 2))) (Ioo y x)) :
    ((∫ t in Ioo y x,
        1 / √((a₁ + b₁ * t) * (a₂ + b₂ * t) * (f₂ + g₂ * t + h₂ * t ^ 2)) : ℝ) : ℂ) =
      ellRedQuadRF ((√(a₁ + b₁ * x) * √(a₂ + b₂ * y) + √(a₁ + b₁ * y) * √(a₂ + b₂ * x)) ^ 2)
        (ellRedQuadS f₂ g₂ h₂ x y) (-(a₁ * b₂ - a₂ * b₁) ^ 2)
        (2 * a₁ * a₂ * h₂ + 2 * b₁ * b₂ * f₂ - (a₁ * b₂ + a₂ * b₁) * g₂)
        (ellRedQuadD f₂ g₂ h₂ f₂ g₂ h₂) x y := by
  have e : ∀ t : ℝ, a₁ * a₂ + (a₁ * b₂ + a₂ * b₁) * t + b₁ * b₂ * t ^ 2 =
      (a₁ + b₁ * t) * (a₂ + b₂ * t) := fun t => by ring
  obtain ⟨hx₁, hy₁⟩ := ei19e_endpoints_nonneg hxy fun t ht => (hQ t ht).1
  obtain ⟨hx₂, hy₂⟩ := ei19e_endpoints_nonneg hxy fun t ht => (hQ t ht).2.1
  have H := ellRed_two_quadratics (f₁ := a₁ * a₂) (g₁ := a₁ * b₂ + a₂ * b₁) (h₁ := b₁ * b₂)
    (f₂ := f₂) (g₂ := g₂) (h₂ := h₂) hxy
    (fun t ht => ⟨by rw [e]; exact mul_pos (hQ t ht).1 (hQ t ht).2.1, (hQ t ht).2.2⟩)
    (by simpa only [e] using hint)
  rw [ellRedQuadS_linear_mul hx₁ hx₂ hy₁ hy₂] at H
  have eD11 : ellRedQuadD (a₁ * a₂) (a₁ * b₂ + a₂ * b₁) (b₁ * b₂) (a₁ * a₂) (a₁ * b₂ + a₂ * b₁)
      (b₁ * b₂) = -(a₁ * b₂ - a₂ * b₁) ^ 2 := by unfold ellRedQuadD; ring
  have eD12 : ellRedQuadD (a₁ * a₂) (a₁ * b₂ + a₂ * b₁) (b₁ * b₂) f₂ g₂ h₂ =
      2 * a₁ * a₂ * h₂ + 2 * b₁ * b₂ * f₂ - (a₁ * b₂ + a₂ * b₁) * g₂ := by unfold ellRedQuadD; ring
  rw [eD11, eD12] at H
  rw [← H]
  simp only [e]

/-- DLMF 19.29.27, the cubic case `a₂ = 1`, `b₂ = 0` of (19.29.26): for `a₁ + b₁ t` and
`Q₂(t) = f₂ + g₂ t + h₂ t²` positive on `(y, x)`, (19.29.24) holds with `S₁ = (X₁ + Y₁)²`,
`D₁₂ = 2a₁h₂ - b₁g₂`, `D₁₁ = -b₁²`. -/
@[dlmf 19.29.E27]
theorem ellRed_linear_quadratic {a₁ b₁ f₂ g₂ h₂ x y : ℝ} (hxy : y < x)
    (hQ : ∀ t ∈ Ioo y x, 0 < a₁ + b₁ * t ∧ 0 < f₂ + g₂ * t + h₂ * t ^ 2)
    (hint : IntegrableOn (fun t => 1 / √((a₁ + b₁ * t) * (f₂ + g₂ * t + h₂ * t ^ 2))) (Ioo y x)) :
    ((∫ t in Ioo y x, 1 / √((a₁ + b₁ * t) * (f₂ + g₂ * t + h₂ * t ^ 2)) : ℝ) : ℂ) =
      ellRedQuadRF ((√(a₁ + b₁ * x) + √(a₁ + b₁ * y)) ^ 2) (ellRedQuadS f₂ g₂ h₂ x y) (-b₁ ^ 2)
        (2 * a₁ * h₂ - b₁ * g₂) (ellRedQuadD f₂ g₂ h₂ f₂ g₂ h₂) x y := by
  have H := ellRed_linear_linear_quadratic (a₁ := a₁) (b₁ := b₁) (a₂ := 1) (b₂ := 0)
    (f₂ := f₂) (g₂ := g₂) (h₂ := h₂) hxy
    (fun t ht => ⟨(hQ t ht).1, by norm_num, (hQ t ht).2⟩) (by simpa using hint)
  simp only [zero_mul, add_zero, mul_one, Real.sqrt_one, mul_zero, one_mul,
    zero_add] at H
  rw [H]
  congr 1
  ring

/-- DLMF 19.29.28 with 19.29.29: for `0 ≤ a ≤ y < x`,
`∫_y^x dt / √(t³ - a³) = 4 R_F(U, U - 3a + 2√3 a, U - 3a - 2√3 a)`, where
`(x - y)² U = (√(x - a) + √(y - a))² ((ξ + η)² - (x - y)²)`, `ξ = √(x² + ax + a²)`,
`η = √(y² + ay + a²)`. DLMF allows `a = y = 0`, where the integral diverges; `0 < y` is
assumed. -/
@[dlmf 19.29.E28, dlmf 19.29.E29]
theorem ellRed_cube_difference {a x y : ℝ} (ha : 0 ≤ a) (hay : a ≤ y) (hy : 0 < y)
    (hxy : y < x) :
    ((∫ t in Ioo y x, 1 / √(t ^ 3 - a ^ 3) : ℝ) : ℂ) =
      4 * symEllIntRF ((√(x - a) + √(y - a)) ^ 2 *
            ((√(x ^ 2 + a * x + a ^ 2) + √(y ^ 2 + a * y + a ^ 2)) ^ 2 - (x - y) ^ 2) /
              (x - y) ^ 2 : ℝ)
        ((√(x - a) + √(y - a)) ^ 2 *
            ((√(x ^ 2 + a * x + a ^ 2) + √(y ^ 2 + a * y + a ^ 2)) ^ 2 - (x - y) ^ 2) /
              (x - y) ^ 2 - 3 * a + 2 * √3 * a : ℝ)
        ((√(x - a) + √(y - a)) ^ 2 *
            ((√(x ^ 2 + a * x + a ^ 2) + √(y ^ 2 + a * y + a ^ 2)) ^ 2 - (x - y) ^ 2) /
              (x - y) ^ 2 - 3 * a - 2 * √3 * a : ℝ) := by
  sorry

/-- DLMF 19.29.31: `(x - y)² U = (√Q(x²) + √Q(y²))² - h (x² - y²)²`, `Q(s) = f + g s + h s²`. -/
@[dlmf 19.29.E31]
def ellRedBiquadU (f g h x y : ℝ) : ℝ :=
  ((√(f + g * x ^ 2 + h * x ^ 4) + √(f + g * y ^ 2 + h * y ^ 4)) ^ 2 -
    h * (x ^ 2 - y ^ 2) ^ 2) / (x - y) ^ 2

/-- DLMF 19.29.30: if `Q(t²) = f + g t² + h t⁴` is positive and monotonic for `y < t < x`, then
`∫_y^x dt / √Q(t²) = 2 R_F(U, U - g + 2√(fh), U - g - 2√(fh))` with (19.29.31) (`√(fh)` the
principal complex square root). -/
@[dlmf 19.29.E30]
theorem ellRed_biquadratic {f g h x y : ℝ} (hxy : y < x)
    (hQ : ∀ t ∈ Ioo y x, 0 < f + g * t ^ 2 + h * t ^ 4)
    (hmono : MonotoneOn (fun t => f + g * t ^ 2 + h * t ^ 4) (Ioo y x) ∨
      AntitoneOn (fun t => f + g * t ^ 2 + h * t ^ 4) (Ioo y x))
    (hint : IntegrableOn (fun t => 1 / √(f + g * t ^ 2 + h * t ^ 4)) (Ioo y x)) :
    ((∫ t in Ioo y x, 1 / √(f + g * t ^ 2 + h * t ^ 4) : ℝ) : ℂ) =
      2 * symEllIntRF (ellRedBiquadU f g h x y : ℝ)
        ((ellRedBiquadU f g h x y - g : ℝ) + 2 * ((f * h : ℝ) : ℂ) ^ (1 / 2 : ℂ))
        ((ellRedBiquadU f g h x y - g : ℝ) - 2 * ((f * h : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
  sorry

/-- DLMF 19.29.32 with 19.29.33: for `0 ≤ y < x` (DLMF: `0 ≤ y ≤ x`; `x = y` is excluded since
`U` is then undefined) and `a ≠ 0` or `y > 0` (convergence),
`∫_y^x dt / √(t⁴ + a⁴) = 2 R_F(U, U + 2a², U - 2a²)`,
`(x - y)² U = (√(x⁴ + a⁴) + √(y⁴ + a⁴))² - (x² - y²)²`. -/
@[dlmf 19.29.E32, dlmf 19.29.E33]
theorem ellRed_quartic_plus {a x y : ℝ} (hy : 0 ≤ y) (hxy : y < x) (ha : a ≠ 0 ∨ 0 < y) :
    ((∫ t in Ioo y x, 1 / √(t ^ 4 + a ^ 4) : ℝ) : ℂ) =
      2 * symEllIntRF (((√(x ^ 4 + a ^ 4) + √(y ^ 4 + a ^ 4)) ^ 2 - (x ^ 2 - y ^ 2) ^ 2) /
            (x - y) ^ 2 : ℝ)
        (((√(x ^ 4 + a ^ 4) + √(y ^ 4 + a ^ 4)) ^ 2 - (x ^ 2 - y ^ 2) ^ 2) / (x - y) ^ 2 +
          2 * a ^ 2 : ℝ)
        (((√(x ^ 4 + a ^ 4) + √(y ^ 4 + a ^ 4)) ^ 2 - (x ^ 2 - y ^ 2) ^ 2) / (x - y) ^ 2 -
          2 * a ^ 2 : ℝ) := by
  have hpos : ∀ t ∈ Ioo y x, 0 < a ^ 4 + 0 * t ^ 2 + 1 * t ^ 4 := by
    intro t ht
    have : 0 < t := lt_of_le_of_lt hy ht.1
    positivity
  have hmono : MonotoneOn (fun t : ℝ => a ^ 4 + 0 * t ^ 2 + 1 * t ^ 4) (Ioo y x) := by
    intro s hs t _ hst
    have : 0 ≤ s := hy.trans hs.1.le
    simp only [zero_mul, add_zero, one_mul]
    gcongr
  have hcont : ContinuousOn (fun t : ℝ => 1 / √(a ^ 4 + 0 * t ^ 2 + 1 * t ^ 4)) (Icc y x) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => ?_
    have : 0 < a ^ 4 + 0 * t ^ 2 + 1 * t ^ 4 := by
      rcases ha with ha | ha
      · have := pow_pos (pow_pos (abs_pos.mpr ha) 2) 2
        rw [← pow_mul, pow_abs] at this
        have := abs_nonneg (a ^ 4)
        have h4 : |a ^ 4| = a ^ 4 := abs_of_nonneg (by positivity)
        have : 0 ≤ t ^ 4 := by have : 0 ≤ t := hy.trans ht.1; positivity
        nlinarith
      · have : 0 < t := ha.trans_le ht.1
        positivity
    exact (Real.sqrt_pos.mpr this).ne'
  have H := ellRed_biquadratic (f := a ^ 4) (g := 0) (h := 1) hxy hpos (Or.inl hmono)
    ((hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self)
  have hs : ((a ^ 4 * 1 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((a ^ 2 : ℝ) : ℂ) := by
    rw [ei19e_cpow_half_ofReal (by positivity), show a ^ 4 * 1 = (a ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg a)]
  have e' : ∀ t : ℝ, a ^ 4 + 0 * t ^ 2 + t ^ 4 = t ^ 4 + a ^ 4 := fun t => by ring
  simp only [ellRedBiquadU, hs, one_mul, sub_zero, e'] at H
  rw [H]
  push_cast
  ring_nf

end DLMF.EllipticIntegrals
