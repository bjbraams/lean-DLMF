/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Standard
public import Carlson.R.SingleIntegral.PositiveRay
public import Carlson.R.Homogeneity
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetric elliptic integrals: definitions (DLMF §§19.15–19.16)

DLMF's symmetric standard integrals, defined by DLMF's own integrals (19.16.1), (19.16.2),
(19.16.2_5), (19.16.5) and (19.2.17), and DLMF's multivariate hypergeometric `R`-function
`R_{-a}(𝐛; 𝐳)` of §19.16(ii):

* `symEllIntRF x y z = (1/2) ∫₀^∞ dt / s(t)` (19.16.1), `s(t) = √(t+x) √(t+y) √(t+z)` (19.16.4)
  with principal square roots (`symEllIntS`);
* `symEllIntRJ x y z p = (3/2) ∫₀^∞ dt / (s(t) (t + p))` (19.16.2), the **Cauchy principal value**
  (`cauchyPVIoi`) being taken when `p` is real and negative;
* `symEllIntRG x y z = (1/4) ∫₀^∞ s(t)⁻¹ (x/(t+x) + y/(t+y) + z/(t+z)) t dt` (19.16.2_5);
* `symEllIntRD x y z = R_J(x, y, z, z)` (19.16.5);
* `symEllIntRC x y = (1/2) ∫₀^∞ dt / (√(t+x) (t+y))` (19.2.17), with the Cauchy principal value
  when `y < 0`;
* `symEllIntR a b z = R_{-a}(𝐛; 𝐳)` (19.16.8): on the product slit plane it is Carlson's
  `R`-function `Carlson.carlsonR (-a) b z` of the companion library `lean-codes` (note DLMF's
  sign convention for the subscript: DLMF's `R_{-a}` is `carlsonR (-a)`); at the boundary
  (some `z_j = 0`, "without destroying convergence", §19.16(iii)) it is the limit from the
  slit domain.

**Domains.** DLMF 19.16(i): `x, y, z ∈ ℂ \ (-∞, 0]` except that one or more of them may be `0`
when the integral converges; for `R_F` and `R_J` at most one may vanish, for `R_G` any number,
for `R_D` the third argument is nonzero; `p ≠ 0`. These are the predicates `symEllIntArg` and
`symEllIntRFDomain`. Because the definitions are Lean integrals, values outside these domains
are totalized (a divergent integral is `0`). Square roots are principal, so the defining
integrands are those of DLMF on the whole complex domain.

**Bridges** to `lean-codes` (`Carlson.carlsonRF`, `Carlson.carlsonRG`,
`Carlson.TwoVariable.carlsonRC`, `Carlson.carlsonR`) on the slit plane are DLMF's
(19.16.14)–(19.16.18); the normalizations were checked numerically (mpmath `elliprf`, `elliprj`,
`elliprg`, `elliprc`; for `p < 0` mpmath's `elliprj` returns a complex number whose real part is
the principal value used here).

## §19.15 Advantages of symmetry (prose)

The `R`-function reveals the permutation symmetry hidden in Lauricella's `F_D` (19.15.p1).
Symmetry of `R_F`, `R_G`, `R_J` in `x, y, z` (`Carlson.carlsonRF_perm`, …, and
`symEllIntR_comp_perm`) replaces the five Legendre transformations (19.7.2), (19.7.4)–(19.7.7),
unifies Landen and Gauss transformations (§19.22) and the parameter changes of `Π` (19.21.12)
(19.15.p2); it permits the elementary-symmetric expansion (19.19.7) (19.15.p3) and the
reduction theorems of §19.29 (19.15.p4); symmetry in the semiaxes of ellipsoids is preserved
(19.15.p5). These are commentary; the mathematical content is in the cited formulas.

## References

* NIST DLMF §§19.2(iv), 19.15, 19.16.
* B. C. Carlson, *Special Functions of Applied Mathematics*, 1977; formalized in `lean-codes`
  (`Carlson.*`), reused here through bridge theorems.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-! ### Domains and the Cauchy principal value -/

/-- DLMF §19.16(i): an admissible argument of a symmetric integral, `x ∈ ℂ \ (-∞, 0]` or
`x = 0` (that is, `x` is not a negative real number). -/
@[dlmf 19.16.i]
def symEllIntArg (x : ℂ) : Prop := x ∈ slitPlane ∨ x = 0

/-- DLMF §19.16(i): the domain of `R_F(x, y, z)` and of the first three arguments of `R_J`:
admissible arguments, at most one of them zero. -/
@[dlmf 19.16.i]
def symEllIntRFDomain (x y z : ℂ) : Prop :=
  symEllIntArg x ∧ symEllIntArg y ∧ symEllIntArg z ∧
    (x = 0 → y ≠ 0 ∧ z ≠ 0) ∧ (y = 0 → z ≠ 0)

/-- `p` is a negative real number (the case `p < 0` of DLMF, where principal values are
taken). -/
def IsNegReal (p : ℂ) : Prop := p.im = 0 ∧ p.re < 0

/-- The Cauchy principal value of `∫₀^∞ f` about an interior singular point `c > 0`:
`lim_{ε → 0+} ∫_{(0,∞) \ [c-ε, c+ε]} f`. Used for `R_J` with `p < 0` (DLMF §19.16(i)) and
`R_C` with `y < 0` (DLMF 19.2.17). If the limit does not exist the value is junk
(`limUnder`). -/
def cauchyPVIoi (f : ℝ → ℂ) (c : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => ∫ t in Ioi (0 : ℝ) \ Icc (c - ε) (c + ε), f t

/-! ### The symmetric integrals -/

/-- DLMF 19.16.4: `s(t) = √(t + x) √(t + y) √(t + z)`, principal square roots. -/
@[dlmf 19.16.E4]
def symEllIntS (x y z : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) * ((t : ℂ) + z) ^ (1 / 2 : ℂ)

/-- DLMF 19.16.1: Carlson's symmetric integral of the first kind
`R_F(x, y, z) = (1/2) ∫₀^∞ dt / s(t)`, for `x, y, z ∈ ℂ \ (-∞, 0]`, at most one of them `0`
(`symEllIntRFDomain`). Off that domain the Lean integral is totalized. -/
@[dlmf 19.16.E1]
def symEllIntRF (x y z : ℂ) : ℂ :=
  (1 / 2) * ∫ t in Ioi (0 : ℝ), (symEllIntS x y z t)⁻¹

/-- DLMF 19.16.2: Carlson's symmetric integral of the third kind
`R_J(x, y, z, p) = (3/2) ∫₀^∞ dt / (s(t) (t + p))`, `p ≠ 0`, with `x, y, z` as for `R_F`.
**When `p` is real and negative the Cauchy principal value is taken** (about `t = -p`). -/
@[dlmf 19.16.E2]
def symEllIntRJ (x y z p : ℂ) : ℂ := by
  classical
  exact (3 / 2) *
    if IsNegReal p then
      cauchyPVIoi (fun t => (symEllIntS x y z t * ((t : ℂ) + p))⁻¹) (-p.re)
    else ∫ t in Ioi (0 : ℝ), (symEllIntS x y z t * ((t : ℂ) + p))⁻¹

/-- DLMF 19.16.2_5: Carlson's symmetric integral of the second kind
`R_G(x, y, z) = (1/4) ∫₀^∞ s(t)⁻¹ (x/(t+x) + y/(t+y) + z/(t+z)) t dt`, for admissible
`x, y, z` (any number of them may vanish). -/
@[dlmf 19.16.E2_5]
def symEllIntRG (x y z : ℂ) : ℂ :=
  (1 / 4) * ∫ t in Ioi (0 : ℝ),
    (symEllIntS x y z t)⁻¹ * (x / ((t : ℂ) + x) + y / ((t : ℂ) + y) + z / ((t : ℂ) + z)) * t

/-- DLMF 19.16.5: `R_D(x, y, z) = R_J(x, y, z, z)`, symmetric only in `x, y`; `z ≠ 0`. -/
@[dlmf 19.16.E5]
def symEllIntRD (x y z : ℂ) : ℂ := symEllIntRJ x y z z

/-- DLMF 19.2.17: `R_C(x, y) = (1/2) ∫₀^∞ dt / (√(t + x) (t + y))` for `x ∈ ℂ \ (-∞, 0)`,
`y ≠ 0`; **the Cauchy principal value is taken if `y < 0`**. -/
def symEllIntRC (x y : ℂ) : ℂ := by
  classical
  exact (1 / 2) *
    if IsNegReal y then
      cauchyPVIoi (fun t => (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹) (-y.re)
    else ∫ t in Ioi (0 : ℝ), (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹

/-- DLMF 19.16.8: the multivariate hypergeometric function `R_{-a}(𝐛; 𝐳)` (written
`R(a; 𝐛; 𝐳)` before 1969). On the product slit plane it is Carlson's `R`-function
`Carlson.carlsonR (-a) b z` (all complex `a` and `𝐛`; DLMF's (19.16.9) has real `𝐛` with
`∑ bⱼ > a > 0`, and Carlson's continuation in the parameters is used elsewhere in DLMF, e.g.
`R_{1/2}` in (19.16.17)). When some `zⱼ` lies off the slit plane (DLMF allows `zⱼ = 0`
"without destroying convergence", §19.16(iii)), the value is the limit from the slit domain;
where that limit does not exist the value is junk. -/
@[dlmf 19.16.E8]
def symEllIntR {ι : Type*} [Fintype ι] (a : ℂ) (b z : ι → ℂ) : ℂ := by
  classical
  exact if z ∈ Carlson.carlsonRSlitDomain then Carlson.carlsonR (-a) b z
    else limUnder (𝓝[Carlson.carlsonRSlitDomain] z) (Carlson.carlsonR (-a) b)

/-! ### Elementary facts -/

theorem ei19c_inv_cpow_half (w : ℂ) : (w ^ (1 / 2 : ℂ))⁻¹ = w ^ (-1 / 2 : ℂ) := by
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]

theorem ei19c_cpow_half_sq (w : ℂ) : w ^ (1 / 2 : ℂ) * w ^ (1 / 2 : ℂ) = w := by
  rw [← sq, show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num, cpow_nat_inv_pow _ two_ne_zero]

theorem ei19c_not_isNegReal_of_mem_slitPlane {p : ℂ} (hp : p ∈ slitPlane) : ¬ IsNegReal p := by
  rintro ⟨h1, h2⟩
  rcases mem_slitPlane_iff.mp hp with h | h
  · linarith
  · exact h h1

theorem ei19c_add_mem_slitPlane {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : symEllIntArg z) :
    (t : ℂ) + z ∈ slitPlane := by
  rcases hz with hz | rfl
  · rcases mem_slitPlane_iff.mp hz with h | h
    · exact mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
    · exact mem_slitPlane_iff.mpr (Or.inr (by simpa using h))
  · simpa using ofReal_mem_slitPlane.mpr ht

theorem symEllIntR_of_mem {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) : symEllIntR a b z = Carlson.carlsonR (-a) b z := by
  simp [symEllIntR, hz]

theorem ei19c_betaIntegral_inv {a a' : ℂ} (ha : 0 < a.re) (ha' : 0 < a'.re) :
    (betaIntegral a a')⁻¹ = Gamma (a + a') / (Gamma a * Gamma a') := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral ha ha'
  have h1 : Gamma (a + a') ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  rw [h]; field_simp

theorem ei19c_Gamma_three_halves : Gamma (3 / 2 : ℂ) = (1 / 2) * Gamma (1 / 2) := by
  rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]

theorem ei19c_Gamma_five_halves : Gamma (5 / 2 : ℂ) = (3 / 2) * Gamma (3 / 2) := by
  rw [show (5 / 2 : ℂ) = 3 / 2 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]

theorem ei19c_Gamma_half_ne : Gamma (1 / 2 : ℂ) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by norm_num)

theorem ei19c_Gamma_half_sq : Gamma (1 / 2 : ℂ) * Gamma (1 / 2) = π := by
  rw [Complex.Gamma_one_half_eq, ei19c_cpow_half_sq]

/-- DLMF 19.16.9 (first form), **stronger than DLMF**: for complex `a, 𝐛` with `Re a > 0`,
`Re a' > 0`, `a' = -a + ∑ bⱼ` (19.16.10), and nodes in the slit plane,
`R_{-a}(𝐛; 𝐳) = B(a, a')⁻¹ ∫₀^∞ t^{a'-1} ∏ⱼ (t + zⱼ)^{-bⱼ} dt`. DLMF assumes real `bⱼ` and
`∑ bⱼ > a > 0`. From `Carlson.carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR`. -/
@[dlmf 19.16.E9]
theorem symEllIntR_eq_integral {ι : Type*} [Fintype ι] {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hsum : a' = -a + ∑ i, b i)
    (hz : z ∈ Carlson.carlsonRSlitDomain) :
    symEllIntR a b z = (betaIntegral a a')⁻¹ *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a' - 1) * ∏ i, ((t : ℂ) + z i) ^ (-b i) := by
  rw [symEllIntR_of_mem _ _ hz]
  have h := Carlson.carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR (a := a') (a' := a)
    (b := b) ha' ha (by rw [hsum]; ring) hz
  unfold Carlson.carlsonRPositiveRayIntegral at h
  have hint : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a' - 1) * ∏ i, ((t : ℂ) + z i) ^ (-b i)) =
      ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a' - 1) * ∏ i, (z i + (s : ℂ)) ^ (-b i) := by
    congr 1; funext t; simp only [add_comm]
  rw [hint, h, ei19c_betaIntegral_inv ha ha']
  unfold Carlson.carlsonR
  have hS : ∑ i, b i = a + a' := by rw [hsum]; ring
  have h1 : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha
  have h2 : Gamma a' ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha'
  rw [hS]; field_simp

/-- DLMF 19.16.10 (the conjugate exponent `a' = -a + ∑ bⱼ`) as used in (19.16.9). -/
@[dlmf 19.16.E10]
def symEllIntRConj {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ) : ℂ := -a + ∑ i, b i

/-! ### The named integrals as `R`-functions (19.16.14–19.16.18) -/

theorem ei19c_slit3 {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    (![x, y, z] : Fin 3 → ℂ) ∈ Carlson.carlsonRSlitDomain := by
  intro i; fin_cases i <;> assumption

theorem ei19c_slit2 {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    (![x, y] : Fin 2 → ℂ) ∈ Carlson.carlsonRSlitDomain := by
  intro i; fin_cases i <;> assumption

theorem ei19c_slit4 {x y z p : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    (![x, y, z, p] : Fin 4 → ℂ) ∈ Carlson.carlsonRSlitDomain := by
  intro i; fin_cases i <;> assumption

/-- DLMF 19.16.14: `R_F(x, y, z) = R_{-1/2}(1/2, 1/2, 1/2; x, y, z)` on the slit plane. -/
@[dlmf 19.16.E14]
theorem symEllIntRF_eq_symEllIntR {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    symEllIntRF x y z = symEllIntR (1 / 2) (fun _ : Fin 3 => 1 / 2) ![x, y, z] := by
  rw [symEllIntR_eq_integral (a' := 1) (by norm_num) (by norm_num)
    (by simp; try norm_num) (ei19c_slit3 hx hy hz),
    ei19c_betaIntegral_inv (by norm_num) (by norm_num), symEllIntRF]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, sub_self, cpow_zero, one_mul, Gamma_one, mul_one]
  rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, ei19c_Gamma_three_halves,
    mul_div_assoc, div_self ei19c_Gamma_half_ne, mul_one]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [symEllIntS, mul_inv, ei19c_inv_cpow_half, neg_div]

/-- Bridge: on the slit plane DLMF's `R_F` is `Carlson.carlsonRF` of `lean-codes`. -/
theorem symEllIntRF_eq_carlsonRF {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) : symEllIntRF x y z = Carlson.carlsonRF x y z := by
  rw [symEllIntRF_eq_symEllIntR hx hy hz, symEllIntR_of_mem _ _ (ei19c_slit3 hx hy hz),
    Carlson.carlsonRF]
  congr 1; ring

theorem ei19c_Gamma_two : Gamma (2 : ℂ) = 1 := by
  rw [show (2 : ℂ) = 1 + 1 by norm_num, Complex.Gamma_add_one _ one_ne_zero, Complex.Gamma_one]
  ring

theorem ei19c_cpow_neg_three_halves {w : ℂ} (hw : w ≠ 0) :
    w ^ (-(3 / 2) : ℂ) = w ^ (-(1 / 2) : ℂ) * w⁻¹ := by
  rw [show -(3 / 2 : ℂ) = -(1 / 2) + -1 by norm_num, cpow_add _ _ hw, cpow_neg_one]

theorem ei19c_add_ne_zero {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : symEllIntArg z) :
    (t : ℂ) + z ≠ 0 := slitPlane_ne_zero (ei19c_add_mem_slitPlane ht hz)

/-- DLMF 19.16.16: `R_J(x, y, z, p) = R_{-3/2}(1/2, 1/2, 1/2, 1; x, y, z, p)` on the slit plane
(`p ∈ slitPlane`: no principal value). -/
@[dlmf 19.16.E16]
theorem symEllIntRJ_eq_symEllIntR {x y z p : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    symEllIntRJ x y z p = symEllIntR (3 / 2) ![1 / 2, 1 / 2, 1 / 2, 1] ![x, y, z, p] := by
  rw [symEllIntR_eq_integral (a' := 1) (by norm_num) (by norm_num)
    (by simp [Fin.sum_univ_four]; try norm_num) (ei19c_slit4 hx hy hz hp),
    ei19c_betaIntegral_inv (by norm_num) (by norm_num), symEllIntRJ,
    ite_eq_right (ei19c_not_isNegReal_of_mem_slitPlane hp)]
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, sub_self, cpow_zero, one_mul,
    Gamma_one, mul_one, cpow_neg_one]
  rw [show (3 / 2 : ℂ) + 1 = 5 / 2 by norm_num, ei19c_Gamma_five_halves,
    mul_div_assoc, div_self (Complex.Gamma_ne_zero_of_re_pos (by norm_num)), mul_one]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [symEllIntS, mul_inv, ei19c_inv_cpow_half, neg_div]

/-- Bridge: on the slit plane DLMF's `R_J` is Carlson's `R_{-3/2}(1/2, 1/2, 1/2, 1; …)`. -/
theorem symEllIntRJ_eq_carlsonR {x y z p : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    symEllIntRJ x y z p = Carlson.carlsonR (-3 / 2) ![1 / 2, 1 / 2, 1 / 2, 1] ![x, y, z, p] := by
  rw [symEllIntRJ_eq_symEllIntR hx hy hz hp, symEllIntR_of_mem _ _ (ei19c_slit4 hx hy hz hp)]
  congr 1; ring

/-- DLMF 19.16.15: `R_D(x, y, z) = R_{-3/2}(1/2, 1/2, 3/2; x, y, z)` on the slit plane. -/
@[dlmf 19.16.E15]
theorem symEllIntRD_eq_symEllIntR {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    symEllIntRD x y z = symEllIntR (3 / 2) ![1 / 2, 1 / 2, 3 / 2] ![x, y, z] := by
  rw [symEllIntR_eq_integral (a' := 1) (by norm_num) (by norm_num)
    (by simp [Fin.sum_univ_three]; try norm_num) (ei19c_slit3 hx hy hz),
    ei19c_betaIntegral_inv (by norm_num) (by norm_num), symEllIntRD, symEllIntRJ,
    ite_eq_right (ei19c_not_isNegReal_of_mem_slitPlane hz)]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, sub_self, cpow_zero, one_mul, Gamma_one, mul_one]
  rw [show (3 / 2 : ℂ) + 1 = 5 / 2 by norm_num, ei19c_Gamma_five_halves,
    mul_div_assoc, div_self (Complex.Gamma_ne_zero_of_re_pos (by norm_num)), mul_one]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [ei19c_cpow_neg_three_halves (ei19c_add_ne_zero ht (Or.inl hz))]
  simp only [symEllIntS, mul_inv, ei19c_inv_cpow_half, neg_div]
  ring

/-- DLMF 19.16.18: `R_C(x, y) = R_{-1/2}(1/2, 1; x, y)` on the slit plane. -/
@[dlmf 19.16.E18]
theorem symEllIntRC_eq_symEllIntR {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    symEllIntRC x y = symEllIntR (1 / 2) ![1 / 2, 1] ![x, y] := by
  rw [symEllIntR_eq_integral (a' := 1) (by norm_num) (by norm_num)
    (by simp) (ei19c_slit2 hx hy),
    ei19c_betaIntegral_inv (by norm_num) (by norm_num), symEllIntRC,
    ite_eq_right (ei19c_not_isNegReal_of_mem_slitPlane hy)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, cpow_zero, one_mul, Gamma_one, mul_one, cpow_neg_one]
  rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, ei19c_Gamma_three_halves,
    mul_div_assoc, div_self ei19c_Gamma_half_ne, mul_one]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [mul_inv, ei19c_inv_cpow_half, neg_div]

/-- Bridge: on the slit plane DLMF's `R_C` is `Carlson.TwoVariable.carlsonRC` of `lean-codes`. -/
theorem symEllIntRC_eq_carlsonRC {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    symEllIntRC x y = Carlson.TwoVariable.carlsonRC x y := by
  rw [symEllIntRC_eq_symEllIntR hx hy, symEllIntR_of_mem _ _ (ei19c_slit2 hx hy)]
  unfold Carlson.TwoVariable.carlsonRC Carlson.TwoVariable.pair
  congr 1; ring

/-! ### Zero-variable (complete) cases 19.16.20–19.16.22 -/

/-- DLMF 19.16.20: `R_F(0, y, z) = (π/2) R_{-1/2}(1/2, 1/2; y, z)`, `y, z ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.16.E20]
theorem symEllIntRF_zero_left {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symEllIntRF 0 y z = (π / 2) * symEllIntR (1 / 2) ![1 / 2, 1 / 2] ![y, z] := by
  rw [symEllIntR_eq_integral (a' := 1 / 2) (by norm_num) (by norm_num)
    (by simp) (ei19c_slit2 hy hz),
    ei19c_betaIntegral_inv (by norm_num) (by norm_num), symEllIntRF]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Gamma_one, ei19c_Gamma_half_sq,
    show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mul_assoc, show (π : ℂ) / 2 * (1 / π) = 1 / 2 by field_simp]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [symEllIntS, add_zero, mul_inv, ei19c_inv_cpow_half, neg_div]
  ring

/-- DLMF 19.16.21: `R_D(0, y, z) = (3π/4) R_{-3/2}(1/2, 3/2; y, z)`, `y, z ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.16.E21]
theorem symEllIntRD_zero_left {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symEllIntRD 0 y z = (3 * π / 4) * symEllIntR (3 / 2) ![1 / 2, 3 / 2] ![y, z] := by
  rw [symEllIntR_eq_integral (a' := 1 / 2) (by norm_num) (by norm_num)
    (by simp) (ei19c_slit2 hy hz),
    ei19c_betaIntegral_inv (by norm_num) (by norm_num), symEllIntRD, symEllIntRJ,
    ite_eq_right (ei19c_not_isNegReal_of_mem_slitPlane hz)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (3 / 2 : ℂ) + 1 / 2 = 2 by norm_num, ei19c_Gamma_two, ei19c_Gamma_three_halves,
    show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, mul_assoc (1 / 2 : ℂ), ei19c_Gamma_half_sq]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mul_assoc, show 3 * (π : ℂ) / 4 * (1 / (1 / 2 * π)) = 3 / 2 by field_simp; ring]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [ei19c_cpow_neg_three_halves (ei19c_add_ne_zero ht (Or.inl hz))]
  simp only [symEllIntS, add_zero, mul_inv, ei19c_inv_cpow_half, neg_div]
  ring

/-- DLMF 19.16.22: `R_J(0, y, z, p) = (3π/4) R_{-3/2}(1/2, 1/2, 1; y, z, p)`,
`y, z, p ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.16.E22]
theorem symEllIntRJ_zero_left {y z p : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hp : p ∈ slitPlane) :
    symEllIntRJ 0 y z p = (3 * π / 4) * symEllIntR (3 / 2) ![1 / 2, 1 / 2, 1] ![y, z, p] := by
  rw [symEllIntR_eq_integral (a' := 1 / 2) (by norm_num) (by norm_num)
    (by simp [Fin.sum_univ_three]; try norm_num) (ei19c_slit3 hy hz hp),
    ei19c_betaIntegral_inv (by norm_num) (by norm_num), symEllIntRJ,
    ite_eq_right (ei19c_not_isNegReal_of_mem_slitPlane hp)]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, cpow_neg_one]
  rw [show (3 / 2 : ℂ) + 1 / 2 = 2 by norm_num, ei19c_Gamma_two, ei19c_Gamma_three_halves,
    show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, mul_assoc (1 / 2 : ℂ), ei19c_Gamma_half_sq]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mul_assoc, show 3 * (π : ℂ) / 4 * (1 / (1 / 2 * π)) = 3 / 2 by field_simp; ring]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [symEllIntS, add_zero, mul_inv, ei19c_inv_cpow_half, neg_div]
  ring

/-! ### Degenerate cases and the hyperelliptic integral (19.16.5–19.16.7) -/

/-- DLMF 19.16.5: `R_D(x, y, z) = (3/2) ∫₀^∞ dt / (s(t) (t + z))` (for `z` not a negative real;
DLMF: `z ≠ 0`, `z ∈ ℂ \ (-∞, 0]`). -/
@[dlmf 19.16.E5]
theorem symEllIntRD_eq_integral {x y z : ℂ} (hz : ¬ IsNegReal z) :
    symEllIntRD x y z = (3 / 2) * ∫ t in Ioi (0 : ℝ), (symEllIntS x y z t * ((t : ℂ) + z))⁻¹ := by
  simp [symEllIntRD, symEllIntRJ, hz]

/-- DLMF 19.16.6: `R_C(x, y) = R_F(x, y, y)`, **stronger than DLMF**: for every `x` and every
`y` that is not a negative real (for `y < 0` DLMF's `R_C` is a principal value and `R_F(x, y, y)`
is outside DLMF's domain). The integrands agree pointwise. -/
@[dlmf 19.16.E6]
theorem symEllIntRC_eq_symEllIntRF (x : ℂ) {y : ℂ} (hy : ¬ IsNegReal y) :
    symEllIntRC x y = symEllIntRF x y y := by
  simp only [symEllIntRC, symEllIntRF, hy, ↓reduceIte, symEllIntS, mul_assoc, ei19c_cpow_half_sq]

/-- DLMF 19.16.7: `R_J` is the degenerate case `x₄ = x₅ = p` of the hyperelliptic integral
`(3/2) ∫₀^∞ dt / ∏_{j=1}^5 √(t + xⱼ)`; for `p` not a negative real (no principal value). -/
@[dlmf 19.16.E7]
theorem symEllIntRJ_eq_hyperelliptic (x y z : ℂ) {p : ℂ} (hp : ¬ IsNegReal p) :
    symEllIntRJ x y z p =
      (3 / 2) * ∫ t in Ioi (0 : ℝ), (∏ j : Fin 5, ((t : ℂ) + ![x, y, z, p, p] j) ^ (1 / 2 : ℂ))⁻¹ := by
  simp only [symEllIntRJ, hp, ↓reduceIte, Fin.prod_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, symEllIntS, mul_assoc, ei19c_cpow_half_sq]

/-! ### Symmetry, homogeneity and normalization -/

/-- DLMF 19.15.p2 / 19.16.8: `R_F` is symmetric in its first two arguments (all arguments). -/
@[dlmf 19.15]
theorem symEllIntRF_comm_left (x y z : ℂ) : symEllIntRF y x z = symEllIntRF x y z := by
  simp only [symEllIntRF, symEllIntS, mul_comm (((_ : ℂ) + y) ^ (1 / 2 : ℂ))]

/-- `R_F` is symmetric in its last two arguments (all arguments). -/
@[dlmf 19.15]
theorem symEllIntRF_comm_right (x y z : ℂ) : symEllIntRF x z y = symEllIntRF x y z := by
  simp only [symEllIntRF, symEllIntS, mul_assoc, mul_comm (((_ : ℂ) + z) ^ (1 / 2 : ℂ))]

/-- `R_J(x, y, z, p)` is symmetric in its first two arguments (all arguments). -/
@[dlmf 19.15]
theorem symEllIntRJ_comm_left (x y z p : ℂ) : symEllIntRJ y x z p = symEllIntRJ x y z p := by
  simp only [symEllIntRJ, symEllIntS, mul_comm (((_ : ℂ) + y) ^ (1 / 2 : ℂ))]

/-- `R_J(x, y, z, p)` is symmetric in `y, z` (all arguments). -/
@[dlmf 19.15]
theorem symEllIntRJ_comm_right (x y z p : ℂ) : symEllIntRJ x z y p = symEllIntRJ x y z p := by
  simp only [symEllIntRJ, symEllIntS, mul_assoc, mul_comm (((_ : ℂ) + z) ^ (1 / 2 : ℂ))]

/-- `R_D(x, y, z)` is symmetric in `x, y` (DLMF 19.16.5; all arguments). -/
theorem symEllIntRD_comm (x y z : ℂ) : symEllIntRD y x z = symEllIntRD x y z :=
  symEllIntRJ_comm_left x y z z

/-- `R_G` is symmetric in its first two arguments (all arguments). -/
@[dlmf 19.15]
theorem symEllIntRG_comm_left (x y z : ℂ) : symEllIntRG y x z = symEllIntRG x y z := by
  unfold symEllIntRG symEllIntS
  congr 2; funext t; ring

/-- `R_G` is symmetric in its last two arguments (all arguments). -/
@[dlmf 19.15]
theorem symEllIntRG_comm_right (x y z : ℂ) : symEllIntRG x z y = symEllIntRG x y z := by
  unfold symEllIntRG symEllIntS
  congr 2; funext t; ring

/-- DLMF 19.16.8: `R_{-a}(𝐛; 𝐳)` is unchanged when the same permutation is applied to `𝐛` and
`𝐳` (slit-plane nodes). From `Carlson.regCarlsonR_comp_perm`. -/
@[dlmf 19.16.E8]
theorem symEllIntR_comp_perm {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (a : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ Carlson.carlsonRSlitDomain) :
    symEllIntR a (b ∘ σ) (z ∘ σ) = symEllIntR a b z := by
  have hz' : z ∘ σ ∈ Carlson.carlsonRSlitDomain := fun i => hz (σ i)
  rw [symEllIntR_of_mem _ _ hz', symEllIntR_of_mem _ _ hz]
  unfold Carlson.carlsonR
  have h1 : (b ∘ σ) ∘ σ.symm = b := by funext i; simp
  have h2 : ∑ i, (b ∘ σ) i = ∑ i, b i := Equiv.sum_comp σ b
  rw [Carlson.regCarlsonR_comp_perm σ _ hz, h1, h2]

/-- DLMF 19.16.11 (first part): homogeneity `R_{-a}(𝐛; λ𝐳) = λ^{-a} R_{-a}(𝐛; 𝐳)`, with the
branch condition made explicit: `λ` and all `zⱼ` in the slit plane and
`ph λ + ph zⱼ ∈ (-π, π)` (DLMF states no condition; for `λ > 0` it is automatic). From
`Carlson.regCarlsonR_mul_of_arg_add`. -/
@[dlmf 19.16.E11]
theorem symEllIntR_mul {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ) {μ : ℂ} {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (hμ : μ ∈ slitPlane)
    (harg : ∀ i, arg μ + arg (z i) ∈ Ioo (-Real.pi) Real.pi) :
    symEllIntR a b (fun i => μ * z i) = μ ^ (-a) * symEllIntR a b z := by
  have hz' : (fun i => μ * z i) ∈ Carlson.carlsonRSlitDomain := by
    intro i
    have hμ' := mem_slitPlane_iff_arg.mp hμ
    have hw := mem_slitPlane_iff_arg.mp (hz i)
    rw [mem_slitPlane_iff_arg, arg_mul hμ'.2 hw.2 ⟨(harg i).1, (harg i).2.le⟩]
    exact ⟨(harg i).2.ne, mul_ne_zero hμ'.2 hw.2⟩
  rw [symEllIntR_of_mem _ _ hz', symEllIntR_of_mem _ _ hz]
  unfold Carlson.carlsonR
  rw [Carlson.regCarlsonR_mul_of_arg_add _ b hz hμ harg]
  ring

/-- DLMF 19.16.11 (second part): `R_{-a}(𝐛; x𝟏) = x^{-a}` for `x ∈ ℂ \ (-∞, 0]`, when
`Γ(∑ bⱼ) ≠ 0` (Lean's `Γ` vanishes at its poles; DLMF has `∑ bⱼ > a > 0`). -/
@[dlmf 19.16.E11]
theorem symEllIntR_const {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ) {x : ℂ}
    (hx : x ∈ slitPlane) (hb : Gamma (∑ i, b i) ≠ 0) :
    symEllIntR a b (fun _ => x) = x ^ (-a) := by
  rw [symEllIntR_of_mem _ _ (fun _ => hx)]
  unfold Carlson.carlsonR
  rw [Carlson.regCarlsonR_const_node _ _ hx]
  field_simp

/-- DLMF 19.16.i.p1: the normalization `R_F(1, 1, 1) = 1`. -/
@[dlmf 19.16.i]
theorem symEllIntRF_one_one_one : symEllIntRF 1 1 1 = 1 := by
  have h1 : (1 : ℂ) ∈ slitPlane := one_mem_slitPlane
  rw [symEllIntRF_eq_carlsonRF h1 h1 h1, Carlson.carlsonRF_self h1, one_cpow]

/-- DLMF 19.16.i.p1: the normalization `R_J(1, 1, 1, 1) = 1`. -/
@[dlmf 19.16.i]
theorem symEllIntRJ_one_one_one_one : symEllIntRJ 1 1 1 1 = 1 := by
  have h1 : (1 : ℂ) ∈ slitPlane := one_mem_slitPlane
  rw [symEllIntRJ_eq_symEllIntR h1 h1 h1 h1]
  have : (![1, 1, 1, 1] : Fin 4 → ℂ) = fun _ => 1 := by funext i; fin_cases i <;> rfl
  have hG : Gamma (∑ i, (![1 / 2, 1 / 2, 1 / 2, 1] : Fin 4 → ℂ) i) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp [Fin.sum_univ_four]; norm_num)
  rw [this, symEllIntR_const _ _ h1 hG, one_cpow]

/-! ### `R_G` and further representations -/

/-- DLMF 19.16.17: `R_G(x, y, z) = R_{1/2}(1/2, 1/2, 1/2; x, y, z)` on the slit plane
(note `a = -1/2` here, outside the integral (19.16.9); the right side is Carlson's
continuation, `lean-codes`' `Carlson.carlsonRG`). -/
@[dlmf 19.16.E17]
theorem symEllIntRG_eq_symEllIntR {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    symEllIntRG x y z = symEllIntR (-1 / 2) (fun _ : Fin 3 => 1 / 2) ![x, y, z] := by
  sorry

/-- Bridge: on the slit plane DLMF's `R_G` is `Carlson.carlsonRG` of `lean-codes`. -/
theorem symEllIntRG_eq_carlsonRG {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) : symEllIntRG x y z = Carlson.carlsonRG x y z := by
  rw [symEllIntRG_eq_symEllIntR hx hy hz, symEllIntR_of_mem _ _ (ei19c_slit3 hx hy hz),
    Carlson.carlsonRG]
  congr 1; ring

/-- DLMF 19.16.12 with 19.16.13: for `n = 4`, `c = csc² φ`, `a, a' > 0`,
`b₃ = a + a' - b₁ - b₂ - b₄`,
`R_{-a}(b₁, …, b₄; c - 1, c - k², c, c - α²) = 2 (sin² φ)^{1-a'} / B(a, a') ∫₀^φ (sin θ)^{2a-1}
(sin² φ - sin² θ)^{a'-1} (cos θ)^{1-2b₁} (1 - k² sin² θ)^{-b₂} (1 - α² sin² θ)^{-b₄} dθ`.
Real parameters; `0 < φ < π/2` and `k² sin² φ < 1`, `α² sin² φ < 1` keep the nodes positive. -/
@[dlmf 19.16.E12, dlmf 19.16.E13]
theorem symEllIntR_four_eq_integral_sin {a a' b₁ b₂ b₄ φ k α : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (hφ : 0 < φ) (hφ' : φ < π / 2) (hk : k ^ 2 * Real.sin φ ^ 2 < 1)
    (hα : α ^ 2 * Real.sin φ ^ 2 < 1) :
    let c : ℝ := 1 / Real.sin φ ^ 2
    symEllIntR (a : ℂ) ![(b₁ : ℂ), b₂, a + a' - b₁ - b₂ - b₄, b₄]
        ![((c - 1 : ℝ) : ℂ), ((c - k ^ 2 : ℝ) : ℂ), ((c : ℝ) : ℂ), ((c - α ^ 2 : ℝ) : ℂ)] =
      (betaIntegral a a')⁻¹ * (2 * (Real.sin φ ^ 2) ^ (1 - a') *
        ∫ θ in (0 : ℝ)..φ, Real.sin θ ^ (2 * a - 1) * (Real.sin φ ^ 2 - Real.sin θ ^ 2) ^ (a' - 1) *
          Real.cos θ ^ (1 - 2 * b₁) * (1 - k ^ 2 * Real.sin θ ^ 2) ^ (-b₂) *
          (1 - α ^ 2 * Real.sin θ ^ 2) ^ (-b₄) : ℝ) := by
  sorry

/-- DLMF 19.16.19: when one variable is `0` "without destroying convergence",
`R_{-a}(b₁, …, bₙ; 0, z₂, …, zₙ) = B(a, a' - b₁)/B(a, a') · R_{-a}(b₂, …, bₙ; z₂, …, zₙ)`,
for `a + a' > 0`, `a' > b₁`, written with the Beta ratio as the Gamma quotient
`Γ(a' - b₁) Γ(a + a') / (Γ(a') Γ(a + a' - b₁))` (the factor `Γ(a)` cancels, which gives the
meaning for `a ≤ 0`, e.g. `R_G`). Real parameters as in DLMF; the left side is the limit from the
slit domain (`symEllIntR`). We also assume `∑_{j ≥ 2} bⱼ = a + a' - b₁ > 0`, so that the right
side is a genuine (non-totalized) value. -/
@[dlmf 19.16.E19]
theorem symEllIntR_cons_zero {n : ℕ} {a b₁ : ℝ} {b : Fin n → ℝ} {z : Fin n → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain)
    (h₁ : 0 < a + (-a + b₁ + ∑ i, b i)) (h₂ : b₁ < -a + b₁ + ∑ i, b i)
    (h₃ : 0 < ∑ i, b i) :
    let a' : ℝ := -a + b₁ + ∑ i, b i
    symEllIntR (a : ℂ) (Fin.cons (b₁ : ℂ) fun i => (b i : ℂ)) (Fin.cons 0 z) =
      Gamma ((a' - b₁ : ℝ) : ℂ) * Gamma ((a + a' : ℝ) : ℂ) /
          (Gamma (a' : ℂ) * Gamma ((a + a' - b₁ : ℝ) : ℂ)) *
        symEllIntR (a : ℂ) (fun i => (b i : ℂ)) z := by
  sorry

/-- DLMF 19.16.23: `R_G(0, y, z) = (π/4) R_{1/2}(1/2, 1/2; y, z) = (π/4) z R_{-1/2}(-1/2, 3/2; y, z)`,
`y, z ∈ ℂ \ (-∞, 0]` (the last `R`-function has `a = a' = 1/2`). -/
@[dlmf 19.16.E23]
theorem symEllIntRG_zero_left {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symEllIntRG 0 y z = (π / 4) * symEllIntR (-1 / 2) ![1 / 2, 1 / 2] ![y, z] ∧
      symEllIntRG 0 y z = (π / 4) * z * symEllIntR (1 / 2) ![-1 / 2, 3 / 2] ![y, z] := by
  sorry

/-- DLMF 19.16.24: the incomplete integral recovered from the complete one,
`R_{-a}(𝐛; 𝐳) = z₁^{a'-b₁}/B(b₁, a'-b₁) ∫₀^∞ t^{b₁-1} (t + z₁)^{-a'}
R_{-a}(𝐛; 0, t + z₂, …, t + zₙ) dt`, for `a' > b₁`, `a + a' > b₁ > 0`, real parameters and
slit-plane nodes. -/
@[dlmf 19.16.E24]
theorem symEllIntR_eq_integral_complete {n : ℕ} {a b₁ : ℝ} {b : Fin n → ℝ} {z₁ : ℂ}
    {z : Fin n → ℂ} (hz₁ : z₁ ∈ slitPlane) (hz : z ∈ Carlson.carlsonRSlitDomain)
    (h₁ : b₁ < -a + b₁ + ∑ i, b i) (h₂ : b₁ < a + (-a + b₁ + ∑ i, b i)) (h₃ : 0 < b₁) :
    let a' : ℝ := -a + b₁ + ∑ i, b i
    symEllIntR (a : ℂ) (Fin.cons (b₁ : ℂ) fun i => (b i : ℂ)) (Fin.cons z₁ z) =
      z₁ ^ ((a' - b₁ : ℝ) : ℂ) * (betaIntegral b₁ ((a' - b₁ : ℝ) : ℂ))⁻¹ *
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((b₁ - 1 : ℝ) : ℂ) * ((t : ℂ) + z₁) ^ (-(a' : ℂ)) *
          symEllIntR (a : ℂ) (Fin.cons (b₁ : ℂ) fun i => (b i : ℂ))
            (Fin.cons 0 fun i => (t : ℂ) + z i) := by
  sorry

end DLMF.EllipticIntegrals
