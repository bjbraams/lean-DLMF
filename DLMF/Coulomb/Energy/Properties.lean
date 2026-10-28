/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Energy.Defs
public import DLMF.Coulomb.Energy.Q2eRegular
public import DLMF.Confluent.Whittaker
public import DLMF.OrthogonalPolynomials.Classical

/-!
# Coulomb functions `f`, `h`, `s`, `c`: basic properties (DLMF §33.14)

The Coulomb wave equation in the variables `r`, `ε` (33.14.1–33.14.2), the turning point
33.14.3, the Whittaker and Kummer forms of `f(ε,ℓ;r)` (33.14.4–33.14.5) with the immateriality of
the sign of `κ` and the reality of `f`, the alternative product formula 33.14.12 for `A(ε,ℓ)`,
the hydrogenic functions `φ_{n,ℓ}` and their orthonormality (33.14.13–33.14.15), and the
Wronskians 33.14.16.

## Main results

* `coulombfKummer_neg`, `conj_coulombfKummer`, `ofReal_coulombf`: the sign of `κ` is
  immaterial and `f` is real; `(f : ℂ)` is the Kummer expression 33.14.5 (proved).
* `coulombf_eq_whittakerM`: 33.14.4 (proved).
* `turningPointR_spec`: `r_tp` is a zero of `ε + 2/r - ℓ(ℓ+1)/r²` (proved).
* `coulomb_potential_substitution`: the substitution 33.14.2 maps 33.2.1 to 33.14.1 (proved).
* `coulombAProd_eq_Gamma`: 33.14.12 (proved).
* `hydrogenRadial_eq_coulombs`: the first equality of 33.14.14 (proved).
* `coulombs_re_eq_zero_of_neg`: `s`, `c` are imaginary when `B < 0` (proved).
-/

@[expose] public section

open Complex Filter MeasureTheory Set Asymptotics
open scoped Real Nat Topology ComplexConjugate

noncomputable section

namespace DLMF.Coulomb

open DLMF.Confluent DLMF.OrthogonalPolynomials

/-! ### `κ` and the Kummer form of `f` -/

/-- The conjugate of `κ` is `κ` (for `ε ≤ 0`) or `-κ` (for `ε > 0`). -/
theorem conj_coulombKappa (ε r : ℝ) :
    conj (coulombKappa ε r) = coulombKappa ε r ∨ conj (coulombKappa ε r) = -coulombKappa ε r := by
  unfold coulombKappa
  split_ifs
  · exact Or.inl (Complex.conj_ofReal _)
  · exact Or.inl (Complex.conj_ofReal _)
  · right
    simp [map_mul, Complex.conj_I, Complex.conj_ofReal]

/-- Complex conjugation of the Kummer form 33.14.5. -/
theorem conj_coulombfKummer (κ : ℂ) (ℓ : ℕ) (r : ℝ) :
    conj (coulombfKummer κ ℓ r) = coulombfKummer (conj κ) ℓ r := by
  unfold coulombfKummer
  rw [map_div₀, map_mul, map_mul, map_pow, ← Complex.exp_conj, conj_kummerM]
  simp [map_div₀, map_neg, map_sub, map_add, map_mul, Complex.conj_ofReal, map_natCast,
    map_ofNat]

/-- The Kummer expression 33.14.5 at `κ` of 33.14.6 is real. -/
theorem conj_coulombfKummer_kappa (ε : ℝ) (ℓ : ℕ) (r : ℝ) :
    conj (coulombfKummer (coulombKappa ε r) ℓ r) = coulombfKummer (coulombKappa ε r) ℓ r := by
  rw [conj_coulombfKummer]
  rcases conj_coulombKappa ε r with h | h <;> rw [h]
  exact coulombfKummer_neg _ ℓ r

/-- **`f(ε,ℓ;r)` is real and equals the Kummer form 33.14.5** for `ε ≠ 0`,
`f = (2r)^{ℓ+1} e^{-r/κ} M(ℓ+1-κ,2ℓ+2,2r/κ)/(2ℓ+1)!` (DLMF 33.14.5, §33.14(ii)). -/
@[dlmf 33.14.E5]
theorem ofReal_coulombf {ε : ℝ} (hε : ε ≠ 0) (ℓ : ℕ) (r : ℝ) :
    (coulombf ε ℓ r : ℂ) = coulombfKummer (coulombKappa ε r) ℓ r := by
  simp only [coulombf, hε, ↓reduceIte]
  exact Complex.conj_eq_iff_re.mp (conj_coulombfKummer_kappa ε ℓ r)

/-- **DLMF 33.14.4**: `f(ε,ℓ;r) = κ^{ℓ+1} M_{κ,ℓ+1/2}(2r/κ)/(2ℓ+1)!` for `ε ≠ 0`. -/
@[dlmf 33.14.E4]
theorem coulombf_eq_whittakerM {ε : ℝ} (hε : ε ≠ 0) (ℓ : ℕ) (r : ℝ) :
    (coulombf ε ℓ r : ℂ) = coulombKappa ε r ^ (ℓ + 1) *
      whittakerM (coulombKappa ε r) (ℓ + 1 / 2) (2 * r / coulombKappa ε r) / (2 * ℓ + 1)! := by
  rw [ofReal_coulombf hε, coulombfKummer, whittakerM]
  have hk := coulombKappa_ne_zero hε r
  set κ := coulombKappa ε r
  rw [show (ℓ : ℂ) + 1 / 2 + 1 / 2 = ((ℓ + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
    show (ℓ : ℂ) + 1 / 2 - κ + 1 / 2 = ℓ + 1 - κ by ring,
    show 1 + 2 * ((ℓ : ℂ) + 1 / 2) = 2 * ℓ + 2 by ring,
    show -(2 * (r : ℂ) / κ) / 2 = -(r : ℂ) / κ by ring]
  rw [div_pow]
  field_simp

/-- **DLMF §33.14(ii)**: `f(ε,ℓ;r)` is an analytic function of `r ∈ ℝ` and of `ε ∈ ℝ`, including
`ε = 0`. -/
@[dlmf 33.14.ii]
theorem analyticAt_coulombf (ℓ : ℕ) (ε r : ℝ) :
    AnalyticAt ℝ (fun x => coulombf ε ℓ x) r ∧ AnalyticAt ℝ (fun e => coulombf e ℓ r) ε := by
  sorry

/-! ### The differential equation and the turning point -/

/-- **The Coulomb wave equation in `r`, `ε`** (DLMF 33.14.1): `f(ε,ℓ;r)` satisfies
`w'' + (ε + 2/r - ℓ(ℓ+1)/r²) w = 0` at every `r ≠ 0`. -/
@[dlmf 33.14.E1]
theorem coulombf_ode (ε : ℝ) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (coulombf ε ℓ) (deriv (coulombf ε ℓ) r) r ∧
      HasDerivAt (deriv (coulombf ε ℓ))
        (-(ε + 2 / r - ℓ * (ℓ + 1) / r ^ 2) * coulombf ε ℓ r) r := by
  have hf : coulombf ε ℓ = fun x : ℝ => (q2e_Phi ε ℓ x).re :=
    funext (q2e_coulombf_eq_re ε ℓ)
  have hd : ∀ x : ℝ, HasDerivAt (coulombf ε ℓ) (deriv (q2e_Phi ε ℓ) x).re x := by
    intro x
    rw [hf]
    exact ((q2e_Phi_differentiable ε ℓ x).hasDerivAt).real_of_complex
  have hd' : deriv (coulombf ε ℓ) = fun x : ℝ => (deriv (q2e_Phi ε ℓ) x).re :=
    funext fun x => (hd x).deriv
  refine ⟨(hd r).deriv ▸ hd r, ?_⟩
  rw [hd']
  have h := (q2e_Phi_ode ε ℓ (z := (r : ℂ)) (by exact_mod_cast hr)).real_of_complex
  convert h using 1
  rw [q2e_coulombf_eq_re, ← Complex.re_ofReal_mul]
  push_cast
  rfl

/-- **The Coulomb wave equation in `r`, `ε`** (DLMF 33.14.1) for `h(ε,ℓ;r)`, at every `r ≠ 0`. -/
@[dlmf 33.14.E1]
theorem coulombh_ode (ε : ℝ) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (coulombh ε ℓ) (deriv (coulombh ε ℓ) r) r ∧
      HasDerivAt (deriv (coulombh ε ℓ))
        (-(ε + 2 / r - ℓ * (ℓ + 1) / r ^ 2) * coulombh ε ℓ r) r := by
  sorry

/-- **The substitution 33.14.2** `r = -ηρ`, `ε = 1/η²` turns the coefficient of 33.2.1 into that
of 33.14.1: `ε + 2/r - ℓ(ℓ+1)/r² = η^{-2} (1 - 2η/ρ - ℓ(ℓ+1)/ρ²)`, while
`d²/dr² = η^{-2} d²/dρ²` (DLMF 33.14.2). -/
@[dlmf 33.14.E2]
theorem coulomb_potential_substitution {η ρ : ℝ} (hη : η ≠ 0) (hρ : ρ ≠ 0) (ℓ : ℕ) :
    1 / η ^ 2 + 2 / (-η * ρ) - ℓ * (ℓ + 1) / (-η * ρ) ^ 2 =
      1 / η ^ 2 * (1 - 2 * η / ρ - ℓ * (ℓ + 1) / ρ ^ 2) := by
  field_simp
  ring

/-- **The outer turning point** (DLMF 33.14.3): for `ε > 0`, `r_tp(ε,ℓ)` is a root of
`εr² + 2r - ℓ(ℓ+1) = 0`, so (for `ℓ ≥ 1`, when `r_tp > 0`) a zero of the coefficient
`ε + 2/r - ℓ(ℓ+1)/r²` of 33.14.1. -/
@[dlmf 33.14.E3]
theorem turningPointR_spec {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) :
    ε * turningPointR ε ℓ ^ 2 + 2 * turningPointR ε ℓ - ℓ * (ℓ + 1) = 0 := by
  unfold turningPointR
  have h0 : 0 ≤ 1 + ε * (ℓ * (ℓ + 1)) := by positivity
  have hs := Real.sq_sqrt h0
  set s := Real.sqrt (1 + ε * (ℓ * (ℓ + 1)))
  have key : ε * ((s - 1) / ε) ^ 2 + 2 * ((s - 1) / ε) = (s ^ 2 - 1) / ε := by
    field_simp; ring
  rw [key, hs]
  field_simp
  ring

/-- The turning point is positive for `ℓ ≥ 1`. -/
@[dlmf 33.14.E3]
theorem turningPointR_pos {ε : ℝ} (hε : 0 < ε) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 0 < turningPointR ε ℓ := by
  unfold turningPointR
  apply div_pos _ hε
  have : (1 : ℝ) < 1 + ε * (ℓ * (ℓ + 1)) := by
    have : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    have : 0 < ε * (ℓ * (ℓ + 1)) := by positivity
    linarith
  have := Real.lt_sqrt_of_sq_lt (show (1 : ℝ) ^ 2 < 1 + ε * (ℓ * (ℓ + 1)) by simpa using this)
  linarith

/-- **The regular singularity at `r = 0`** (DLMF §33.14(i)): the indices are `ℓ+1` and `-ℓ`;
`f(ε,ℓ;r) ~ (2r)^{ℓ+1}/(2ℓ+1)!` and `h(ε,ℓ;r) ~ (2ℓ)!/(π (2r)^ℓ)` as `r → 0`. -/
@[dlmf 33.14.i]
theorem coulombf_coulombh_isEquivalent_zero (ε : ℝ) (ℓ : ℕ) :
    (fun r => coulombf ε ℓ r) ~[𝓝[≠] 0] (fun r => (2 * r) ^ (ℓ + 1) / (2 * ℓ + 1)!) ∧
      (fun r => coulombh ε ℓ r) ~[𝓝[≠] 0] (fun r => (2 * ℓ)! / (π * (2 * r) ^ ℓ)) := by
  sorry

/-! ### The irregular solution -/

/-- **DLMF 33.14.7 (Whittaker form)**: away from `ε = 0` and from the poles of `Γ(ℓ+1-κ)`,
`h(ε,ℓ;r) = Γ(ℓ+1-κ)/(πκ^ℓ) (W_{κ,ℓ+1/2}(2r/κ) + (-1)^ℓ S(ε,r) Γ(ℓ+1+κ)/(2(2ℓ+1)!)
M_{κ,ℓ+1/2}(2r/κ))`, the right-hand side being real (`r ≠ 0`). -/
@[dlmf 33.14.E7]
theorem ofReal_coulombh {ε : ℝ} (hε : ε ≠ 0) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0)
    (hpole : ∀ m : ℕ, (ℓ : ℂ) + 1 - coulombKappa ε r ≠ -(m : ℂ)) :
    (coulombh ε ℓ r : ℂ) = Gamma (ℓ + 1 - coulombKappa ε r) / (π * coulombKappa ε r ^ ℓ) *
      (whittakerW (coulombKappa ε r) (ℓ + 1 / 2) (2 * r / coulombKappa ε r) +
        (-1) ^ ℓ * coulombSFactor ε r * Gamma (ℓ + 1 + coulombKappa ε r) / (2 * (2 * ℓ + 1)!) *
          whittakerM (coulombKappa ε r) (ℓ + 1 / 2) (2 * r / coulombKappa ε r)) := by
  sorry

/-- **The sign of `κ` is immaterial in 33.14.7** (DLMF §33.14(iii)): for `ε > 0` the bracketed
form with `-κ = -iε^{-1/2}` gives the same value. -/
@[dlmf 33.14.iii]
theorem coulombhKappa_neg {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0) :
    coulombhKappa (-coulombKappa ε r) (coulombSFactor ε r) ℓ r =
      coulombhKappa (coulombKappa ε r) (coulombSFactor ε r) ℓ r := by
  sorry

/-- **DLMF §33.14(iii)**: `h(ε,ℓ;r)` is an analytic function of `r` for `r ≠ 0` and of `ε` for
`ε ≠ 0`; it is continuous in `ε` at `ε = 0` and at the poles of `Γ(ℓ+1-κ)`, so that the limits
in the definition exist. -/
@[dlmf 33.14.iii]
theorem analyticAt_coulombh (ℓ : ℕ) :
    (∀ ε r : ℝ, r ≠ 0 → AnalyticAt ℝ (fun x => coulombh ε ℓ x) r) ∧
      (∀ ε r : ℝ, ε ≠ 0 → r ≠ 0 → AnalyticAt ℝ (fun e => coulombh e ℓ r) ε) ∧
      (∀ ε r : ℝ, r ≠ 0 →
        Tendsto (fun e => (coulombhFormula e ℓ r).re) (𝓝[≠] ε) (𝓝 (coulombh ε ℓ r))) := by
  sorry

/-! ### `A(ε,ℓ)`, `s` and `c` -/

/-- For `z` not a nonpositive integer, `Γ(z+n) = Γ(z) ∏_{j<n} (z+j)`. -/
lemma c33b_Gamma_add_nat {z : ℂ} (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) (n : ℕ) :
    Gamma (z + n) = Gamma z * ∏ j ∈ Finset.range n, (z + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzn : z + n ≠ 0 := by
      intro h
      exact hz n (by linear_combination h)
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hzn, ih, Finset.prod_range_succ]
    ring

/-- `∏_{j=0}^{2ℓ} (κ - ℓ + j) = κ ∏_{k<ℓ} (κ² - (k+1)²)`. -/
lemma c33b_prod_sym (κ : ℂ) (ℓ : ℕ) :
    ∏ j ∈ Finset.range (2 * ℓ + 1), (κ - ℓ + j) =
      κ * ∏ k ∈ Finset.range ℓ, (κ ^ 2 - ((k : ℂ) + 1) ^ 2) := by
  induction ℓ generalizing κ with
  | zero => simp
  | succ n ih =>
    have h1 : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by ring
    rw [h1, Finset.prod_range_succ', Finset.prod_range_succ]
    have := ih κ
    have hsh : ∏ j ∈ Finset.range (2 * n + 1), (κ - ((n + 1 : ℕ) : ℂ) + ((j + 1 : ℕ) : ℂ)) =
        ∏ j ∈ Finset.range (2 * n + 1), (κ - n + j) := by
      apply Finset.prod_congr rfl; intro j _; push_cast; ring
    rw [hsh, this, Finset.prod_range_succ]
    push_cast
    ring

/-- **DLMF 33.14.12**: `A(ε,ℓ) = Γ(1+ℓ+κ)/Γ(κ-ℓ) κ^{-2ℓ-1}` for `ε ≠ 0`, with either sign of
`κ` (`κ` from 33.14.6 at any `r`), away from the poles of `Γ(κ-ℓ)`. -/
@[dlmf 33.14.E12]
theorem coulombAProd_eq_Gamma {ε : ℝ} (hε : ε ≠ 0) (ℓ : ℕ) (r : ℝ)
    (hpole : ∀ m : ℕ, coulombKappa ε r - ℓ ≠ -(m : ℂ)) :
    (coulombAProd ε ℓ : ℂ) = Gamma (1 + ℓ + coulombKappa ε r) / Gamma (coulombKappa ε r - ℓ) *
      coulombKappa ε r ^ (-(2 * ℓ + 1 : ℤ)) := by
  have hk := coulombKappa_ne_zero hε r
  have hsq := coulombKappa_sq hε r
  set κ := coulombKappa ε r
  have hG := c33b_Gamma_add_nat hpole (2 * ℓ + 1)
  rw [show κ - ℓ + ((2 * ℓ + 1 : ℕ) : ℂ) = 1 + ℓ + κ by push_cast; ring] at hG
  have hG0 : Gamma (κ - ℓ) ≠ 0 := Complex.Gamma_ne_zero hpole
  rw [hG, mul_div_cancel_left₀ _ hG0, c33b_prod_sym, coulombAProd, Finset.prod_range_succ']
  push_cast
  have hε' : (ε : ℂ) = -1 / κ ^ 2 := by
    rw [hsq]; field_simp
  rw [hε', show (-(2 * ℓ + 1 : ℤ)) = -((2 * ℓ + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
    zpow_natCast]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    mul_one]
  rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hk)]
  have hp : κ ^ (2 * ℓ + 1) = κ * ∏ _k ∈ Finset.range ℓ, κ ^ 2 := by
    rw [Finset.prod_const, Finset.card_range, ← pow_mul, pow_succ, mul_comm, mul_comm 2 ℓ]
  rw [hp, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  field_simp
  ring

/-- **DLMF §33.14(iv)**: when `B(ε,ℓ) < 0` (possible for `ε < 0`, `ℓ > (-ε)^{-1/2}`), the
functions `s(ε,ℓ;r)` and `c(ε,ℓ;r)` are purely imaginary. -/
@[dlmf 33.14.iv]
theorem coulombs_re_eq_zero_of_neg {ε : ℝ} {ℓ : ℕ} (hB : coulombBFactor ε ℓ < 0) (r : ℝ) :
    (coulombs ε ℓ r).re = 0 ∧ (coulombc ε ℓ r).re = 0 := by
  constructor
  · rw [coulombs, ofReal_cpow_of_nonpos (by linarith : coulombBFactor ε ℓ / 2 ≤ 0),
      ← Complex.ofReal_neg, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ -(coulombBFactor ε ℓ / 2)),
      show (π : ℂ) * I * ((1 / 2 : ℝ) : ℂ) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    simp
  · rw [coulombc, ofReal_cpow_of_nonpos (by linarith : 2 * coulombBFactor ε ℓ ≤ 0),
      ← Complex.ofReal_neg, show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ -(2 * coulombBFactor ε ℓ)),
      show (π : ℂ) * I * ((-(1 / 2) : ℝ) : ℂ) = ((-(π / 2) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp

/-- **DLMF 33.14.13**: `∫₀^∞ s(ε₁,ℓ;r) s(ε₂,ℓ;r) dr = δ(ε₁-ε₂)` for `ε₁, ε₂ > 0`, in the
distributional sense of DLMF §1.17: for every smooth test function `g` with compact support in
`(0,∞)`, `∫ g(ε₁) ∫₀^R s(ε₁,ℓ;r) s(ε₂,ℓ;r) dr dε₁ → g(ε₂)` as `R → ∞`. -/
@[dlmf 33.14.E13]
theorem coulombs_orthogonality_dirac (ℓ : ℕ) {ε₂ : ℝ} (hε₂ : 0 < ε₂) {g : ℝ → ℂ}
    (hg : ContDiff ℝ ⊤ g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ioi 0) :
    Tendsto (fun R : ℝ => ∫ ε₁ in Ioi (0 : ℝ),
        g ε₁ * ∫ r in (0 : ℝ)..R, coulombs ε₁ ℓ r * coulombs ε₂ ℓ r)
      atTop (𝓝 (g ε₂)) := by
  sorry

/-! ### Hydrogenic functions -/

/-- For `ℓ + 1 ≤ n`, `A(-1/n², ℓ) ≥ 0`. -/
lemma c33b_coulombAProd_nonneg {n ℓ : ℕ} (hn : ℓ + 1 ≤ n) :
    0 ≤ coulombAProd (-1 / (n : ℝ) ^ 2) ℓ := by
  unfold coulombAProd
  apply Finset.prod_nonneg
  intro k hk
  have hk' : (k : ℝ) < n := by
    have := Finset.mem_range.mp hk
    exact_mod_cast (by omega : k < n)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsq : (k : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg k) hk'.le 2
  rw [show 1 + -1 / (n : ℝ) ^ 2 * (k : ℝ) ^ 2 = ((n : ℝ) ^ 2 - (k : ℝ) ^ 2) / (n : ℝ) ^ 2 by
    field_simp; ring]
  exact div_nonneg (by linarith) (by positivity)

/-- **DLMF 33.14.14 (first equality)**: for `n ≥ ℓ+1`,
`φ_{n,ℓ}(r) = (-1)^{ℓ+1+n} (2/n³)^{1/2} s(-1/n², ℓ; r)`. -/
@[dlmf 33.14.E14]
theorem hydrogenRadial_eq_coulombs {n ℓ : ℕ} (hn : ℓ + 1 ≤ n) (r : ℝ) :
    (hydrogenRadial n ℓ r : ℂ) =
      (((-1) ^ (ℓ + 1 + n) * Real.sqrt (2 / (n : ℝ) ^ 3) : ℝ) : ℂ) *
        coulombs (-1 / (n : ℝ) ^ 2) ℓ r := by
  have hB : coulombBFactor (-1 / (n : ℝ) ^ 2) ℓ = coulombAProd (-1 / (n : ℝ) ^ 2) ℓ := by
    have : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by positivity
    have h : ¬ (0 < -1 / (n : ℝ) ^ 2) := by rw [neg_div]; linarith
    simp only [coulombBFactor, h, ↓reduceIte]
  have hA := c33b_coulombAProd_nonneg hn
  rw [hydrogenRadial, coulombs, hB, Real.sqrt_eq_rpow (coulombAProd _ ℓ / 2),
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity)]
  push_cast
  ring

/-- `∏_{k=0}^{ℓ} (n² - k²) · N! = n (2ℓ+1+N)!` for `n = ℓ+1+N`. -/
lemma q2e_prod_sq_sub (ℓ N : ℕ) :
    (∏ k ∈ Finset.range (ℓ + 1), (((ℓ + 1 + N : ℕ) : ℝ) ^ 2 - (k : ℝ) ^ 2)) * N ! =
      ((ℓ + 1 + N : ℕ) : ℝ) * (2 * ℓ + 1 + N)! := by
  induction ℓ generalizing N with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.prod_singleton, Nat.cast_zero, mul_zero]
    rw [show 1 + N = N + 1 by ring, Nat.factorial_succ]; push_cast; ring
  | succ ℓ ih =>
    have h := ih (N + 1)
    rw [show ℓ + 1 + (N + 1) = ℓ + 1 + 1 + N by ring,
      show 2 * ℓ + 1 + (N + 1) = 2 * ℓ + 2 + N by ring] at h
    rw [Finset.prod_range_succ, show 2 * (ℓ + 1) + 1 + N = (2 * ℓ + 2 + N) + 1 by ring,
      Nat.factorial_succ (2 * ℓ + 2 + N)]
    rw [Nat.factorial_succ N] at h
    push_cast at h ⊢
    linear_combination ((ℓ : ℝ) + 1 + 1 + N + (ℓ + 1)) * h

/-- `A(-1/n², ℓ) N! n^{2ℓ+1} = (n+ℓ)!` for `n = ℓ+1+N`. -/
lemma q2e_coulombAProd_hydrogen (ℓ N : ℕ) :
    coulombAProd (-1 / ((ℓ + 1 + N : ℕ) : ℝ) ^ 2) ℓ * N ! * ((ℓ + 1 + N : ℕ) : ℝ) ^ (2 * ℓ + 1) =
      (2 * ℓ + 1 + N)! := by
  have hn : ((ℓ + 1 + N : ℕ) : ℝ) ≠ 0 := by positivity
  have h := q2e_prod_sq_sub ℓ N
  have hA : coulombAProd (-1 / ((ℓ + 1 + N : ℕ) : ℝ) ^ 2) ℓ =
      (∏ k ∈ Finset.range (ℓ + 1), (((ℓ + 1 + N : ℕ) : ℝ) ^ 2 - (k : ℝ) ^ 2)) /
        ((ℓ + 1 + N : ℕ) : ℝ) ^ (2 * (ℓ + 1)) := by
    rw [coulombAProd, pow_mul, show (((ℓ + 1 + N : ℕ) : ℝ) ^ 2) ^ (ℓ + 1) =
      ∏ _k ∈ Finset.range (ℓ + 1), ((ℓ + 1 + N : ℕ) : ℝ) ^ 2 by
        rw [Finset.prod_const, Finset.card_range], ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    field_simp
    ring
  rw [hA]
  rw [show 2 * (ℓ + 1) = (2 * ℓ + 1) + 1 by ring, pow_succ]
  field_simp
  linear_combination ((ℓ + 1 + N : ℕ) : ℝ) ^ (2 * ℓ + 1) * h

/-- `κ(-1/n², 1) = n`. -/
lemma q2e_coulombKappa_hydrogen {n : ℕ} (hn : 0 < n) :
    coulombKappa (-1 / (n : ℝ) ^ 2) 1 = n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hε : -1 / (n : ℝ) ^ 2 < 0 := by
    rw [neg_div]; exact neg_neg_of_pos (by positivity)
  simp only [coulombKappa, hε, ↓reduceIte, zero_lt_one]
  congr 1
  rw [neg_div, neg_neg, Real.rpow_neg (by positivity), one_div, Real.inv_rpow (by positivity),
    inv_inv, ← Real.sqrt_eq_rpow, Real.sqrt_sq hpos.le]

/-- **DLMF 33.14.14 (second equality)** and §33.14(iv): for `n ≥ ℓ+1`, `s(-1/n²,ℓ;r)` is
`e^{-r/n}` times a polynomial in `r/n`:
`φ_{n,ℓ}(r) = (-1)^{ℓ+1+n} n^{-ℓ-2} ((n-ℓ-1)!/(n+ℓ)!)^{1/2} (2r)^{ℓ+1} e^{-r/n}
L^{(2ℓ+1)}_{n-ℓ-1}(2r/n)`. -/
@[dlmf 33.14.E14, dlmf 33.14.iv]
theorem hydrogenRadial_eq_laguerre {n ℓ : ℕ} (hn : ℓ + 1 ≤ n) (r : ℝ) :
    (hydrogenRadial n ℓ r : ℂ) =
      (((-1) ^ (ℓ + 1 + n) / (n : ℝ) ^ (ℓ + 2) *
        Real.sqrt ((n - ℓ - 1)! / (n + ℓ)!) * (2 * r) ^ (ℓ + 1) * Real.exp (-r / n) : ℝ) : ℂ) *
        laguerrePolyL (2 * ℓ + 1) (n - ℓ - 1) (2 * r / n) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show ℓ + 1 + N - ℓ - 1 = N by omega, show ℓ + 1 + N + ℓ = 2 * ℓ + 1 + N by ring]
  set n : ℕ := ℓ + 1 + N with hn_def
  have hn0 : (0 : ℝ) < n := by positivity
  set ε := -1 / (n : ℝ) ^ 2 with hε_def
  have hε0 : ε ≠ 0 := by rw [hε_def]; exact div_ne_zero (by norm_num) (by positivity)
  have hB : coulombBFactor ε ℓ = coulombAProd ε ℓ := by
    have : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by positivity
    have h : ¬ (0 < ε) := by rw [hε_def, neg_div]; linarith
    simp only [coulombBFactor, h, ↓reduceIte]
  have hA := c33b_coulombAProd_nonneg (n := n) (ℓ := ℓ) (by omega)
  have hAe := q2e_coulombAProd_hydrogen ℓ N
  rw [← hn_def, ← hε_def] at hAe
  have hf : (coulombf ε ℓ r : ℂ) = coulombfKummer (n : ℂ) ℓ r := by
    rw [ofReal_coulombf hε0]
    rcases q2e_coulombKappa_eq_or ε r with h | h
    · rw [h, hε_def, q2e_coulombKappa_hydrogen (by omega)]
    · rw [h, coulombfKummer_neg, hε_def, q2e_coulombKappa_hydrogen (by omega)]
  have hK : coulombfKummer (n : ℂ) ℓ r = (((2 * r) ^ (ℓ + 1) * Real.exp (-r / n) *
      (N ! / (2 * ℓ + 1 + N)!) : ℝ) : ℂ) * laguerrePolyL (2 * ℓ + 1) N (2 * r / n) := by
    unfold coulombfKummer laguerrePolyL
    have hM : (ℓ : ℂ) + 1 - n = -(N : ℂ) := by rw [hn_def]; push_cast; ring
    rw [hM, show (2 * ℓ + 1 : ℂ) + 1 = 2 * ℓ + 2 by ring]
    have hP : ((2 * ℓ + 1)! : ℂ) * DLMF.Hypergeometric.poch (2 * ℓ + 2) N = (2 * ℓ + 1 + N)! := by
      have := factorial_mul_ascPochhammer ℂ (2 * ℓ + 1) N
      push_cast at this
      rw [show (2 * ℓ + 2 : ℂ) = 2 * ℓ + 1 + 1 by ring]
      exact this
    have h1 : ((2 * ℓ + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : ((2 * ℓ + 1 + N)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h3 : (N ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hp0 : DLMF.Hypergeometric.poch (2 * ℓ + 2) N ≠ 0 := by
      intro h; rw [h, mul_zero] at hP; exact h2 hP.symm
    have hp0' : DLMF.Hypergeometric.poch (2 * ((ℓ : ℂ) + 1)) N ≠ 0 := by
      rw [show 2 * ((ℓ : ℂ) + 1) = 2 * ℓ + 2 by ring]; exact hp0
    push_cast
    rw [← hP]
    field_simp
  have hkey : Real.sqrt (2 / (n : ℝ) ^ 3) * Real.sqrt (coulombAProd ε ℓ / 2) *
      (N ! / (2 * ℓ + 1 + N)!) = Real.sqrt (N ! / (2 * ℓ + 1 + N)!) / (n : ℝ) ^ (ℓ + 2) := by
    have hP : (0 : ℝ) < (2 * ℓ + 1 + N)! := by exact_mod_cast Nat.factorial_pos _
    have hN : (0 : ℝ) < N ! := by exact_mod_cast Nat.factorial_pos _
    have hq : (0 : ℝ) ≤ N ! / (2 * ℓ + 1 + N)! := by positivity
    calc Real.sqrt (2 / (n : ℝ) ^ 3) * Real.sqrt (coulombAProd ε ℓ / 2) *
          (N ! / (2 * ℓ + 1 + N)!)
        = Real.sqrt (2 / (n : ℝ) ^ 3 * (coulombAProd ε ℓ / 2) *
            (N ! / (2 * ℓ + 1 + N)!) ^ 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hq]
      _ = Real.sqrt ((N ! / (2 * ℓ + 1 + N)!) / ((n : ℝ) ^ (ℓ + 2)) ^ 2) := by
          congr 1
          rw [← hAe]
          field_simp
          ring
      _ = _ := by rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  rw [hydrogenRadial, hB]
  push_cast
  rw [hf, hK]
  have hk := congrArg (fun x : ℝ => (x : ℂ)) hkey
  push_cast at hk ⊢
  linear_combination ((-1) ^ (ℓ + 1 + n) * (2 * (r : ℂ)) ^ (ℓ + 1) * Complex.exp (-(r : ℂ) / n) *
    laguerrePolyL (2 * ℓ + 1) N (2 * r / n)) * hk


/-- **DLMF 33.14.15**: `∫₀^∞ φ_{m,ℓ}(r) φ_{n,ℓ}(r) dr = δ_{m,n}` for `m, n ≥ ℓ+1`. -/
@[dlmf 33.14.E15]
theorem hydrogenRadial_orthonormal {m n ℓ : ℕ} (hm : ℓ + 1 ≤ m) (hn : ℓ + 1 ≤ n) :
    ∫ r in Ioi (0 : ℝ), hydrogenRadial m ℓ r * hydrogenRadial n ℓ r = if m = n then 1 else 0 := by
  sorry

/-- **DLMF §33.14(iv)**: the functions `φ_{n,ℓ}`, `n ≥ ℓ+1`, do not form a complete orthonormal
system of `L²(0,∞)`: some nonzero square-integrable function is orthogonal to all of them. -/
@[dlmf 33.14.iv]
theorem hydrogenRadial_not_complete (ℓ : ℕ) :
    ∃ g : ℝ → ℝ, MemLp g 2 (volume.restrict (Ioi 0)) ∧ ¬ (g =ᵐ[volume.restrict (Ioi 0)] 0) ∧
      ∀ n, ℓ + 1 ≤ n → ∫ r in Ioi (0 : ℝ), hydrogenRadial n ℓ r * g r = 0 := by
  sorry

/-! ### Wronskians -/

/-- **DLMF 33.14.16**: `𝒲{h, f} = h f' - h' f = 2/π` for `r ≠ 0`. -/
@[dlmf 33.14.E16]
theorem coulomb_wronskian_hf (ε : ℝ) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0) :
    coulombh ε ℓ r * deriv (coulombf ε ℓ) r - deriv (coulombh ε ℓ) r * coulombf ε ℓ r =
      2 / π := by
  sorry

/-- **DLMF 33.14.16**: `𝒲{c, s} = 1/π` for `r ≠ 0`, whenever `B(ε,ℓ) ≠ 0` (for `B < 0` both
`s` and `c` are imaginary and the principal powers multiply to `1/2`). -/
@[dlmf 33.14.E16]
theorem coulomb_wronskian_cs {ε : ℝ} {ℓ : ℕ} (hB : coulombBFactor ε ℓ ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    coulombc ε ℓ r * deriv (coulombs ε ℓ) r - deriv (coulombc ε ℓ) r * coulombs ε ℓ r =
      1 / π := by
  sorry

end DLMF.Coulomb
