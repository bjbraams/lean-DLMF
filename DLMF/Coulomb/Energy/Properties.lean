/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Energy.Basic
public import DLMF.Coulomb.Energy.RegularSolution
public import DLMF.Confluent.Whittaker
public import DLMF.Confluent.CoulombIrregular
public import DLMF.OrthogonalPolynomials.Classical
public import DLMF.OrthogonalPolynomials.ClassicalInstances

/-!
# Coulomb functions `f`, `h`, `s`, `c`: basic properties (DLMF §33.14)

The Coulomb wave equation in the variables `r`, `ε` (33.14.1–33.14.2), the turning point
33.14.3, the Whittaker and Kummer forms of `f(ε,ℓ;r)` (33.14.4–33.14.5) with the immateriality of
the sign of `κ` and the reality of `f`, the alternative product formula 33.14.12 for `A(ε,ℓ)`,
the hydrogenic functions `φ_{n,ℓ}` and their orthonormality (33.14.13–33.14.15), and the
Wronskians 33.14.16.

## Main results

* `coulombEnergyFKummer_neg`, `conj_coulombEnergyFKummer`, `ofReal_coulombEnergyF`: the sign of `κ`
  is immaterial and `f` is real; `(f : ℂ)` is the Kummer expression 33.14.5 (proved).
* `coulombEnergyF_eq_whittakerM`: 33.14.4 (proved).
* `analyticAt_coulombEnergyF`: `f` is analytic in `r` and in `ε`, including `ε = 0` (§33.14(ii),
  proved).
* `coulombEnergyHKappa_I_mul_neg_eq_coulombG`, `coulombEnergyHKappa_I_mul_eq_coulombG`: for `ε > 0`
  the bracketed form 33.14.7 is a real multiple of `G_ℓ` (proved).
* `ofReal_coulombEnergyH`: the Whittaker form 33.14.7 of `h` away from its removable points
  (proved).
* `coulombEnergyHKappa_neg`: the sign of `κ` is immaterial in 33.14.7 (proved).
* `turningPointR_spec`: `r_tp` is a zero of `ε + 2/r - ℓ(ℓ+1)/r²` (proved).
* `coulomb_potential_substitution`: the substitution 33.14.2 maps 33.2.1 to 33.14.1 (proved).
* `coulombAProd_eq_Gamma`: 33.14.12 (proved).
* `hydrogenRadial_eq_coulombEnergyS`: the first equality of 33.14.14 (proved).
* `hydrogenRadial_orthonormal`: 33.14.15, from the radial equation (off-diagonal) and the
  Laguerre recurrence moment (diagonal) (proved).
* `coulombEnergyS_re_eq_zero_of_neg`: `s`, `c` are imaginary when `B < 0` (proved).
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
theorem conj_coulombEnergyFKummer (κ : ℂ) (ℓ : ℕ) (r : ℝ) :
    conj (coulombEnergyFKummer κ ℓ r) = coulombEnergyFKummer (conj κ) ℓ r := by
  unfold coulombEnergyFKummer
  rw [map_div₀, map_mul, map_mul, map_pow, ← Complex.exp_conj, conj_kummerM]
  simp [map_div₀, map_neg, map_sub, map_add, map_mul, Complex.conj_ofReal, map_natCast,
    map_ofNat]

/-- The Kummer expression 33.14.5 at `κ` of 33.14.6 is real. -/
theorem conj_coulombEnergyFKummer_kappa (ε : ℝ) (ℓ : ℕ) (r : ℝ) :
    conj (coulombEnergyFKummer (coulombKappa ε r) ℓ r) =
        coulombEnergyFKummer (coulombKappa ε r) ℓ r := by
  rw [conj_coulombEnergyFKummer]
  rcases conj_coulombKappa ε r with h | h <;> rw [h]
  exact coulombEnergyFKummer_neg _ ℓ r

/-- **`f(ε,ℓ;r)` is real and equals the Kummer form 33.14.5** for `ε ≠ 0`,
`f = (2r)^{ℓ+1} e^{-r/κ} M(ℓ+1-κ,2ℓ+2,2r/κ)/(2ℓ+1)!` (DLMF 33.14.5, §33.14(ii)). -/
@[dlmf 33.14.E5]
theorem ofReal_coulombEnergyF {ε : ℝ} (hε : ε ≠ 0) (ℓ : ℕ) (r : ℝ) :
    (coulombEnergyF ε ℓ r : ℂ) = coulombEnergyFKummer (coulombKappa ε r) ℓ r := by
  simp only [coulombEnergyF, hε, ↓reduceIte]
  exact Complex.conj_eq_iff_re.mp (conj_coulombEnergyFKummer_kappa ε ℓ r)

/-- **DLMF 33.14.4**: `f(ε,ℓ;r) = κ^{ℓ+1} M_{κ,ℓ+1/2}(2r/κ)/(2ℓ+1)!` for `ε ≠ 0`. -/
@[dlmf 33.14.E4]
theorem coulombEnergyF_eq_whittakerM {ε : ℝ} (hε : ε ≠ 0) (ℓ : ℕ) (r : ℝ) :
    (coulombEnergyF ε ℓ r : ℂ) = coulombKappa ε r ^ (ℓ + 1) *
      whittakerM (coulombKappa ε r) (ℓ + 1 / 2) (2 * r / coulombKappa ε r) / (2 * ℓ + 1)! := by
  rw [ofReal_coulombEnergyF hε, coulombEnergyFKummer, whittakerM]
  have hk := coulombKappa_ne_zero hε r
  set κ := coulombKappa ε r
  rw [show (ℓ : ℂ) + 1 / 2 + 1 / 2 = ((ℓ + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
    show (ℓ : ℂ) + 1 / 2 - κ + 1 / 2 = ℓ + 1 - κ by ring,
    show 1 + 2 * ((ℓ : ℂ) + 1 / 2) = 2 * ℓ + 2 by ring,
    show -(2 * (r : ℂ) / κ) / 2 = -(r : ℂ) / κ by ring]
  rw [div_pow]
  field_simp

/-- The coefficients `α_k` of 33.19.1 for complex `ε`. -/
private def coulombAlphaC (ε : ℂ) (ℓ : ℕ) : ℕ → ℂ
  | 0 => 2 ^ (ℓ + 1) / (2 * ℓ + 1)!
  | 1 => -(2 ^ (ℓ + 1) / (2 * ℓ + 1)!) / (ℓ + 1)
  | k + 2 => -(2 * coulombAlphaC ε ℓ (k + 1) + ε * coulombAlphaC ε ℓ k) /
      (((k : ℂ) + 2) * ((k : ℂ) + 2 + 2 * ℓ + 1))

/-- At real `ε` the complex coefficients are the real ones. -/
private lemma coulombAlphaC_ofReal (ε : ℝ) (ℓ : ℕ) (k : ℕ) :
    coulombAlphaC ε ℓ k = coulombAlpha ε ℓ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [coulombAlphaC, coulombAlpha]
    | 1, _ => simp [coulombAlphaC, coulombAlpha]
    | k + 2, ih =>
      rw [coulombAlphaC, coulombAlpha, ih (k + 1) (by omega), ih k (by omega)]
      push_cast; ring

/-- Each coefficient `α_k` is a polynomial, hence entire, in `ε`. -/
private lemma differentiable_coulombAlphaC (ℓ : ℕ) (k : ℕ) :
    Differentiable ℂ (fun ε => coulombAlphaC ε ℓ k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp only [coulombAlphaC]; exact differentiable_const _
    | 1, _ => simp only [coulombAlphaC]; exact differentiable_const _
    | k + 2, ih =>
      simp only [coulombAlphaC]
      exact (((ih (k + 1) (by omega)).const_mul 2).add
        (differentiable_id.mul (ih k (by omega)))).neg.div_const _

/-- The bound `|α_k(ε)| ≤ α₀ (2+R)^k / k!` for `|ε| ≤ R`. -/
private lemma norm_coulombAlphaC_le (ℓ : ℕ) {R : ℝ} (hR : 0 ≤ R) {ε : ℂ} (hε : ‖ε‖ ≤ R) (k : ℕ) :
    ‖coulombAlphaC ε ℓ k‖ ≤ 2 ^ (ℓ + 1) / (2 * ℓ + 1)! * (2 + R) ^ k / k ! := by
  set A : ℝ := 2 ^ (ℓ + 1) / (2 * ℓ + 1)!
  set B : ℝ := 2 + R
  have hA : 0 ≤ A := by positivity
  have hB : 2 ≤ B := by simp only [B]; linarith
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ =>
      simp only [coulombAlphaC, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      rw [norm_div, norm_pow]; simp [A]
    | 1, _ =>
      simp only [coulombAlphaC, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
      rw [norm_div, norm_neg, norm_div, norm_pow]
      have h1 : ‖((ℓ : ℂ) + 1)‖ = ℓ + 1 := by
        rw [show ((ℓ : ℂ) + 1) = ((ℓ + 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
          Real.norm_of_nonneg (by positivity)]
      rw [h1]
      simp only [norm_ofNat, Complex.norm_natCast]
      have : (1 : ℝ) ≤ ℓ + 1 := by linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
      calc 2 ^ (ℓ + 1) / ((2 * ℓ + 1)! : ℝ) / (ℓ + 1) ≤ A := by
            simp only [A]; exact div_le_self hA this
        _ ≤ A * B := le_mul_of_one_le_right hA (by linarith)
    | k + 2, ih =>
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      simp only [coulombAlphaC]
      have hc : ‖((k : ℂ) + 2) * ((k : ℂ) + 2 + 2 * ℓ + 1)‖ = ((k : ℝ) + 2) * (k + 2 * ℓ + 3) := by
        rw [show ((k : ℂ) + 2) * ((k : ℂ) + 2 + 2 * ℓ + 1) =
          ((((k : ℝ) + 2) * (k + 2 * ℓ + 3) : ℝ) : ℂ) by push_cast; ring, norm_real,
          Real.norm_of_nonneg (by positivity)]
      rw [norm_div, norm_neg, hc]
      have hpos : 0 < ((k : ℝ) + 2) * (k + 2 * ℓ + 3) := by positivity
      rw [div_le_iff₀ hpos]
      calc ‖2 * coulombAlphaC ε ℓ (k + 1) + ε * coulombAlphaC ε ℓ k‖
          ≤ 2 * ‖coulombAlphaC ε ℓ (k + 1)‖ + R * ‖coulombAlphaC ε ℓ k‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_ofNat]
            gcongr
        _ ≤ 2 * (A * B ^ (k + 1) / (k + 1)!) + R * (A * B ^ k / k !) := by gcongr
        _ ≤ A * B ^ (k + 2) / (k + 2)! * (((k : ℝ) + 2) * (k + 2 * ℓ + 3)) := by
            rw [Nat.factorial_succ (k + 1), Nat.factorial_succ k]
            push_cast
            have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
            have hBk : 0 ≤ B ^ k := by positivity
            have hk1 : (0 : ℝ) < (k + 1) * k ! := by positivity
            have eL : 2 * (A * B ^ (k + 1) / ((k + 1) * k !)) + R * (A * B ^ k / k !) =
                A * B ^ k / ((k + 1) * k !) * (2 * B + R * (k + 1)) := by
              field_simp; ring
            have eR : A * B ^ (k + 2) / ((k + 1 + 1) * ((k + 1) * k !)) *
                ((k + 2) * (k + 2 * ℓ + 3)) =
                  A * B ^ k / ((k + 1) * k !) * (B ^ 2 * (k + 2 * ℓ + 3)) := by
              field_simp; ring
            rw [eL, eR]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hl : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
            have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            simp only [B]
            nlinarith [mul_nonneg hk0 hl, mul_nonneg hR hk0, mul_nonneg hR hl, mul_nonneg hR hR,
              mul_nonneg (mul_nonneg hR hR) hk0, mul_nonneg (mul_nonneg hR hR) hl]


/-- `f(ε,ℓ;r)` is analytic in `ε ∈ ℝ`, as the real part of a power series in `ε` with
locally uniformly convergent polynomial terms. -/
private lemma analyticAt_coulombEnergyF_eps (ℓ : ℕ) (ε r : ℝ) :
    AnalyticAt ℝ (fun e => coulombEnergyF e ℓ r) ε := by
  set R : ℝ := |ε| + 1
  have hR : 0 ≤ R := by positivity
  set F : ℕ → ℂ → ℂ := fun k e => coulombAlphaC e ℓ k * (r : ℂ) ^ (k + ℓ + 1)
  set u : ℕ → ℝ := fun k => 2 ^ (ℓ + 1) / (2 * ℓ + 1)! * |r| ^ (ℓ + 1) *
    ((2 + R) * |r|) ^ k / (k ! : ℝ)
  have hu : Summable u := by
    have := (Real.summable_pow_div_factorial ((2 + R) * |r|)).mul_left
      (2 ^ (ℓ + 1) / (2 * ℓ + 1)! * |r| ^ (ℓ + 1))
    refine this.congr fun k => ?_
    simp only [u]; ring
  have hle : ∀ k, ∀ e ∈ Metric.ball (0 : ℂ) R, ‖F k e‖ ≤ u k := by
    intro k e he
    rw [Metric.mem_ball, dist_zero_right] at he
    simp only [F, u, norm_mul, norm_pow, norm_real, Real.norm_eq_abs]
    calc ‖coulombAlphaC e ℓ k‖ * |r| ^ (k + ℓ + 1)
        ≤ 2 ^ (ℓ + 1) / (2 * ℓ + 1)! * (2 + R) ^ k / k ! * |r| ^ (k + ℓ + 1) := by
          gcongr; exact norm_coulombAlphaC_le ℓ hR he.le k
      _ = _ := by rw [mul_pow]; ring
  have hD : DifferentiableOn ℂ (fun e => ∑' k, F k e) (Metric.ball 0 R) :=
    differentiableOn_tsum_of_summable_norm hu
      (fun k => ((differentiable_coulombAlphaC ℓ k).mul_const _).differentiableOn)
      Metric.isOpen_ball hle
  have hmem : (ε : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs]; simp only [R]; linarith
  have hA : AnalyticAt ℂ (fun e => ∑' k, F k e) ε :=
    hD.analyticAt (Metric.isOpen_ball.mem_nhds hmem)
  have heq : (fun e : ℝ => coulombEnergyF e ℓ r) = fun e : ℝ => (∑' k, F k (e : ℂ)).re := by
    funext e
    rw [coulombEnergyF_eq_re_coulombfComplex, ← (hasSum_coulombfComplex e ℓ r).tsum_eq]
    simp only [F, coulombAlphaC_ofReal]
  rw [heq]
  exact (reCLM.analyticAt _).comp ((hA.restrictScalars (𝕜 := ℝ)).comp (ofRealCLM.analyticAt ε))

/-- **DLMF §33.14(ii)**: `f(ε,ℓ;r)` is an analytic function of `r ∈ ℝ` and of `ε ∈ ℝ`, including
`ε = 0`. -/
@[dlmf 33.14.ii]
theorem analyticAt_coulombEnergyF (ℓ : ℕ) (ε r : ℝ) :
    AnalyticAt ℝ (fun x => coulombEnergyF ε ℓ x) r ∧
        AnalyticAt ℝ (fun e => coulombEnergyF e ℓ r) ε := by
  refine ⟨?_, analyticAt_coulombEnergyF_eps ℓ ε r⟩
  have heq : (fun x : ℝ => coulombEnergyF ε ℓ x) = fun x : ℝ => (coulombfComplex ε ℓ x).re :=
    funext (coulombEnergyF_eq_re_coulombfComplex ε ℓ)
  rw [heq]
  exact (reCLM.analyticAt _).comp
    ((((differentiable_coulombfComplex ε ℓ).analyticAt (r : ℂ)).restrictScalars (𝕜 := ℝ)).comp
      (ofRealCLM.analyticAt r))

/-! ### The differential equation and the turning point -/

/-- **The Coulomb wave equation in `r`, `ε`** (DLMF 33.14.1): `f(ε,ℓ;r)` satisfies
`w'' + (ε + 2/r - ℓ(ℓ+1)/r²) w = 0` at every `r ≠ 0`. -/
@[dlmf 33.14.E1]
theorem coulombEnergyF_ode (ε : ℝ) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (coulombEnergyF ε ℓ) (deriv (coulombEnergyF ε ℓ) r) r ∧
      HasDerivAt (deriv (coulombEnergyF ε ℓ))
        (-(ε + 2 / r - ℓ * (ℓ + 1) / r ^ 2) * coulombEnergyF ε ℓ r) r := by
  have hf : coulombEnergyF ε ℓ = fun x : ℝ => (coulombfComplex ε ℓ x).re :=
    funext (coulombEnergyF_eq_re_coulombfComplex ε ℓ)
  have hd : ∀ x : ℝ, HasDerivAt (coulombEnergyF ε ℓ) (deriv (coulombfComplex ε ℓ) x).re x := by
    intro x
    rw [hf]
    exact ((differentiable_coulombfComplex ε ℓ x).hasDerivAt).real_of_complex
  have hd' : deriv (coulombEnergyF ε ℓ) = fun x : ℝ => (deriv (coulombfComplex ε ℓ) x).re :=
    funext fun x => (hd x).deriv
  refine ⟨(hd r).deriv ▸ hd r, ?_⟩
  rw [hd']
  have h := (hasDerivAt_deriv_coulombfComplex ε ℓ (z := (r : ℂ))
      (by exact_mod_cast hr)).real_of_complex
  convert h using 1
  rw [coulombEnergyF_eq_re_coulombfComplex, ← Complex.re_ofReal_mul]
  push_cast
  rfl

/-- **The Coulomb wave equation in `r`, `ε`** (DLMF 33.14.1) for `h(ε,ℓ;r)`, at every `r ≠ 0`. -/
@[dlmf 33.14.E1]
theorem coulombEnergyH_ode (ε : ℝ) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (coulombEnergyH ε ℓ) (deriv (coulombEnergyH ε ℓ) r) r ∧
      HasDerivAt (deriv (coulombEnergyH ε ℓ))
        (-(ε + 2 / r - ℓ * (ℓ + 1) / r ^ 2) * coulombEnergyH ε ℓ r) r := by
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
theorem coulombEnergyF_coulombEnergyH_isEquivalent_zero (ε : ℝ) (ℓ : ℕ) :
    (fun r => coulombEnergyF ε ℓ r) ~[𝓝[≠] 0] (fun r => (2 * r) ^ (ℓ + 1) / (2 * ℓ + 1)!) ∧
      (fun r => coulombEnergyH ε ℓ r) ~[𝓝[≠] 0] (fun r => (2 * ℓ)! / (π * (2 * r) ^ ℓ)) := by
  sorry

/-! ### The irregular solution -/

/-- The bracketed form 33.14.7 at `κ = -iη`, `r = -ηρ` (`η ≠ 0`, `ρ > 0`) in terms of
`H^+_ℓ(η,ρ)` and the (real) Coulomb wave. -/
theorem coulombEnergyHKappa_I_mul_neg_eq (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) (S : ℝ) :
    coulombEnergyHKappa (I * (-η : ℝ)) S ℓ (-η * ρ) =
      (((-1) ^ ℓ * ‖Gamma (ℓ + 1 + I * η)‖ * Real.exp (-π * η / 2) / (π * η ^ ℓ) : ℝ) : ℂ) *
        coulombHPlus ℓ η ρ -
      I * ((S * (‖Gamma (ℓ + 1 + I * η)‖ ^ 2 * (-1) ^ ℓ * 2 ^ ℓ * (coulombWave ℓ η ρ).re /
        ((2 * ℓ + 1)! * π * η ^ ℓ)) : ℝ) : ℂ) := by
  have hη0 : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  have hz : 2 * (((-η * ρ : ℝ)) : ℂ) / (I * ((-η : ℝ) : ℂ)) = -2 * I * ρ := by
    push_cast; field_simp; ring_nf; rw [I_sq]; ring
  have ha : (ℓ : ℂ) + 1 - I * ((-η : ℝ) : ℂ) = ℓ + 1 + I * η := by push_cast; ring
  have hb : (ℓ : ℂ) + 1 + I * ((-η : ℝ) : ℂ) = conj ((ℓ : ℂ) + 1 + I * η) := by
    simp
  have he : exp (-(-2 * I * ρ) / 2) = exp (I * ρ) := by congr 1; ring
  unfold coulombEnergyHKappa
  rw [hz, ha, hb, Gamma_conj, he]
  set g := Gamma ((ℓ : ℂ) + 1 + I * η) with hg
  have hw := coulombWave_eq_conj_form ℓ η ρ
  have hwr : coulombWave ℓ η ρ = ((coulombWave ℓ η ρ).re : ℂ) :=
    (Complex.conj_eq_iff_re.mp (conj_coulombWave ℓ η ρ)).symm
  rw [show -(2 * I * (ρ : ℂ)) = -2 * I * ρ by ring] at hw
  have hH := coulombHPlus_eq ℓ η hρ
  rw [hH, coulombAPlus, show coulombSigma ℓ η = arg g from rfl]
  set U := kummerU ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) (-2 * I * ρ)
  set M := kummerM ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) (-2 * I * ρ)
  set w := (coulombWave ℓ η ρ).re
  have hgN : g = (‖g‖ : ℂ) * exp (arg g * I) := (norm_mul_exp_arg_mul_I g).symm
  have hgc : g * conj g = ((‖g‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_conj, normSq_eq_norm_sq]
  have hM : exp (I * ρ) * (-2 * I * ρ) ^ (ℓ + 1) * M = (-2 * I) ^ (ℓ + 1) * (w : ℂ) := by
    rw [← hwr, hw, mul_pow]; ring
  rw [hM]
  set N := ‖g‖
  set e := exp (arg g * I)
  have hN : (N : ℂ) ≠ 0 := by
    have : g ≠ 0 := Gamma_nat_add_one_add_I_mul_ne_zero ℓ η
    exact_mod_cast norm_ne_zero_iff.mpr this
  have he0 : e ≠ 0 := exp_ne_zero _
  have hcg : conj g = (N : ℂ) ^ 2 / g := by
    rw [eq_div_iff (by rw [hgN]; exact mul_ne_zero hN he0), mul_comm, hgc]; push_cast; ring
  have hI : (-2 * I) ^ (ℓ + 1) = (-2) ^ ℓ * (-2) * I ^ ℓ * I := by
    rw [mul_pow, pow_succ, pow_succ]; ring
  have hIe : (I * ((-η : ℝ) : ℂ)) ^ ℓ = I ^ ℓ * ((-1) ^ ℓ * (η : ℂ) ^ ℓ) := by
    push_cast; rw [mul_pow, neg_eq_neg_one_mul, mul_pow]
  have hIl : I ^ ℓ ≠ 0 := pow_ne_zero _ I_ne_zero
  have hm1 : ((-1 : ℂ) ^ ℓ) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hm2 : ((-2 : ℂ) ^ ℓ) = (-1) ^ ℓ * 2 ^ ℓ := by rw [← mul_pow]; norm_num
  have hexp : (Real.exp (-π * η / 2) : ℂ) * (Real.exp (π * η / 2) : ℂ) = 1 := by
    rw [← ofReal_mul, ← Real.exp_add]; ring_nf; simp
  have hexp' : ∀ x : ℝ, ((x : ℝ) : ℂ) = (x : ℂ) := fun _ => rfl
  have key : g / (π * (I * ((-η : ℝ) : ℂ)) ^ ℓ) * (exp (I * ρ) * (-2 * I * ρ) ^ (ℓ + 1) * U +
      (-1) ^ ℓ * S * conj g / (2 * (2 * ℓ + 1)!) * ((-2 * I) ^ (ℓ + 1) * (w : ℂ))) =
      (((-1) ^ ℓ * N * Real.exp (-π * η / 2) / (π * η ^ ℓ) : ℝ) : ℂ) *
        (e * (Real.exp (π * η / 2) : ℂ) * 2 ^ (ℓ + 1) * (-1) ^ ℓ * (-I) *
          (ρ : ℂ) ^ (ℓ + 1) * exp (I * ρ) * U) +
      I * ((-(N ^ 2 * (-1) ^ ℓ * S * 2 ^ ℓ * w / ((2 * ℓ + 1)! * π * η ^ ℓ)) : ℝ) : ℂ) := by
    rw [hcg, hIe, hI, mul_pow, hI, hm2]
    conv_lhs => rw [hgN]
    rw [ofReal_div, ofReal_mul, ofReal_mul, hexp']
    generalize Real.exp (-π * η / 2) = q at *
    generalize (Real.exp (π * η / 2) : ℂ) = q' at *
    push_cast
    field_simp
    linear_combination (exp (I * ρ) * ρ * (ρ : ℂ) ^ ℓ * U * 2 ^ ℓ * 2 * e) *
      ((-1) ^ (ℓ * 2) * hexp + hm1)
  rw [key]
  push_cast
  ring

/-- The bracketed form 33.14.7 at `κ = iη`, `r = -ηρ` (`η ≠ 0`, `ρ > 0`) in terms of
`H^-_ℓ(η,ρ)` and the (real) Coulomb wave. -/
theorem coulombEnergyHKappa_I_mul_eq (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) (S : ℝ) :
    coulombEnergyHKappa (I * (η : ℝ)) S ℓ (-η * ρ) =
      (((-1) ^ ℓ * ‖Gamma (ℓ + 1 + I * η)‖ * Real.exp (-π * η / 2) / (π * η ^ ℓ) : ℝ) : ℂ) *
        coulombHMinus ℓ η ρ +
      I * ((S * (‖Gamma (ℓ + 1 + I * η)‖ ^ 2 * (-1) ^ ℓ * 2 ^ ℓ * (coulombWave ℓ η ρ).re /
        ((2 * ℓ + 1)! * π * η ^ ℓ)) : ℝ) : ℂ) := by
  have hη0 : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  have hz : 2 * (((-η * ρ : ℝ)) : ℂ) / (I * (η : ℂ)) = 2 * I * ρ := by
    push_cast; field_simp; ring_nf; rw [I_sq]; ring
  have ha : (ℓ : ℂ) + 1 - I * (η : ℂ) = conj ((ℓ : ℂ) + 1 + I * η) := by
    simp; ring
  have he : exp (-(2 * I * ρ) / 2) = exp (-I * ρ) := by congr 1; ring
  unfold coulombEnergyHKappa
  rw [hz, he]
  have hU : kummerU ((ℓ : ℂ) + 1 - I * η) (2 * ℓ + 2) (2 * I * ρ) =
    kummerU ((ℓ : ℂ) + 1 - I * η) (2 * ℓ + 2) (2 * I * ρ) := rfl
  rw [ha, Gamma_conj]
  rw [← ha]
  set g := Gamma ((ℓ : ℂ) + 1 + I * η) with hg
  have hw : coulombWave ℓ η ρ = (ρ : ℂ) ^ (ℓ + 1) * exp (-I * ρ) *
      kummerM ((ℓ : ℂ) + 1 - I * η) (2 * ℓ + 2) (2 * I * ρ) := rfl
  have hwr : coulombWave ℓ η ρ = ((coulombWave ℓ η ρ).re : ℂ) :=
    (Complex.conj_eq_iff_re.mp (conj_coulombWave ℓ η ρ)).symm
  rw [coulombHMinus_eq ℓ η hρ, coulombAPlus, show coulombSigma ℓ η = arg g from rfl]
  set U := kummerU ((ℓ : ℂ) + 1 - I * η) (2 * ℓ + 2) (2 * I * ρ)
  set M := kummerM ((ℓ : ℂ) + 1 - I * η) (2 * ℓ + 2) (2 * I * ρ)
  set w := (coulombWave ℓ η ρ).re
  have hgN : g = (‖g‖ : ℂ) * exp (arg g * I) := (norm_mul_exp_arg_mul_I g).symm
  have hgc : g * conj g = ((‖g‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_conj, normSq_eq_norm_sq]
  have hM : exp (-I * ρ) * (2 * I * ρ) ^ (ℓ + 1) * M = (2 * I) ^ (ℓ + 1) * (w : ℂ) := by
    rw [← hwr, hw, mul_pow]; ring
  rw [hM]
  set N := ‖g‖
  set e := exp (arg g * I)
  have hN : (N : ℂ) ≠ 0 := by
    have : g ≠ 0 := Gamma_nat_add_one_add_I_mul_ne_zero ℓ η
    exact_mod_cast norm_ne_zero_iff.mpr this
  have he0 : e ≠ 0 := exp_ne_zero _
  have hce : conj e = e⁻¹ := by
    simp only [e, ← exp_conj, map_mul, conj_ofReal, conj_I, ← exp_neg]; ring_nf
  have hcg : conj g = (N : ℂ) * e⁻¹ := by
    rw [hgN, map_mul, conj_ofReal, hce]
  have hI : (2 * I) ^ (ℓ + 1) = 2 ^ ℓ * 2 * I ^ ℓ * I := by
    rw [mul_pow, pow_succ, pow_succ]; ring
  have hIe : (I * (η : ℂ)) ^ ℓ = I ^ ℓ * (η : ℂ) ^ ℓ := by rw [mul_pow]
  have hIl : I ^ ℓ ≠ 0 := pow_ne_zero _ I_ne_zero
  have hm1 : ((-1 : ℂ) ^ ℓ) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hexp : (Real.exp (-π * η / 2) : ℂ) * (Real.exp (π * η / 2) : ℂ) = 1 := by
    rw [← ofReal_mul, ← Real.exp_add]; ring_nf; simp
  have hexp' : ∀ x : ℝ, ((x : ℝ) : ℂ) = (x : ℂ) := fun _ => rfl
  have hcA : conj (e * (Real.exp (π * η / 2) : ℂ) * 2 ^ (ℓ + 1) * (-1) ^ ℓ * (-I)) =
      e⁻¹ * (Real.exp (π * η / 2) : ℂ) * 2 ^ (ℓ + 1) * (-1) ^ ℓ * I := by
    simp only [map_mul, map_pow, map_neg, map_one, map_ofNat, conj_ofReal, conj_I, hce, neg_neg]
  rw [hcA]
  have key : conj g / (π * (I * (η : ℂ)) ^ ℓ) * (exp (-I * ρ) * (2 * I * ρ) ^ (ℓ + 1) * U +
      (-1) ^ ℓ * S * g / (2 * (2 * ℓ + 1)!) * ((2 * I) ^ (ℓ + 1) * (w : ℂ))) =
      (((-1) ^ ℓ * N * Real.exp (-π * η / 2) / (π * η ^ ℓ) : ℝ) : ℂ) *
        (e⁻¹ * (Real.exp (π * η / 2) : ℂ) * 2 ^ (ℓ + 1) * (-1) ^ ℓ * I *
          (ρ : ℂ) ^ (ℓ + 1) * exp (-I * ρ) * U) +
      I * ((N ^ 2 * (-1) ^ ℓ * S * 2 ^ ℓ * w / ((2 * ℓ + 1)! * π * η ^ ℓ) : ℝ) : ℂ) := by
    rw [hcg, hIe, mul_pow, hI]
    conv_lhs => rw [hgN]
    rw [ofReal_div, ofReal_mul, ofReal_mul, hexp']
    generalize Real.exp (-π * η / 2) = q at *
    generalize (Real.exp (π * η / 2) : ℂ) = q' at *
    push_cast
    field_simp
    linear_combination (-(exp (-(I * ρ)) * ρ * (ρ : ℂ) ^ ℓ * U * 2 ^ ℓ * 2)) *
      ((-1) ^ (ℓ * 2) * hexp + hm1)
  rw [key]
  push_cast
  ring


/-- The two coefficients of `coulombEnergyHKappa_I_mul_neg_eq` are linked through `F_ℓ`. -/
private lemma coulombEnergyHKappa_coeff_mul_coulombF (ℓ : ℕ) (η ρ : ℝ) :
    (-1) ^ ℓ * ‖Gamma (ℓ + 1 + I * η)‖ * Real.exp (-π * η / 2) / (π * η ^ ℓ) * coulombF ℓ η ρ =
      Real.exp (-π * η) * (‖Gamma (ℓ + 1 + I * η)‖ ^ 2 * (-1) ^ ℓ * 2 ^ ℓ *
        (coulombWave ℓ η ρ).re / ((2 * ℓ + 1)! * π * η ^ ℓ)) := by
  have hF : coulombF ℓ η ρ = coulombC ℓ η * (coulombWave ℓ η ρ).re := by
    rw [coulombF, re_ofReal_mul]
  have he : Real.exp (-π * η) = Real.exp (-π * η / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hF, coulombC, he]
  ring

/-- For `ρ > 0`, `η ≠ 0`, the bracketed form 33.14.7 at `κ = -iη`, `r = -ηρ` and
`S = e^{-πη}` is a real multiple of `G_ℓ(η,ρ)`. -/
theorem coulombEnergyHKappa_I_mul_neg_eq_coulombG (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ) :
    coulombEnergyHKappa (I * (-η : ℝ)) (Real.exp (-π * η)) ℓ (-η * ρ) =
      (((-1) ^ ℓ * ‖Gamma (ℓ + 1 + I * η)‖ * Real.exp (-π * η / 2) / (π * η ^ ℓ) *
        coulombG ℓ η ρ : ℝ) : ℂ) := by
  rw [coulombEnergyHKappa_I_mul_neg_eq ℓ hη hρ, (coulombH_eq_G_add_I_mul_F ℓ η hρ).1,
    ← coulombEnergyHKappa_coeff_mul_coulombF]
  push_cast
  ring

/-- For `ρ > 0`, `η ≠ 0`, the bracketed form 33.14.7 at `κ = iη`, `r = -ηρ` and
`S = e^{-πη}` is a real multiple of `G_ℓ(η,ρ)`. -/
theorem coulombEnergyHKappa_I_mul_eq_coulombG (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombEnergyHKappa (I * (η : ℝ)) (Real.exp (-π * η)) ℓ (-η * ρ) =
      (((-1) ^ ℓ * ‖Gamma (ℓ + 1 + I * η)‖ * Real.exp (-π * η / 2) / (π * η ^ ℓ) *
        coulombG ℓ η ρ : ℝ) : ℂ) := by
  rw [coulombEnergyHKappa_I_mul_eq ℓ hη hρ, (coulombH_eq_G_add_I_mul_F ℓ η hρ).2,
    ← coulombEnergyHKappa_coeff_mul_coulombF]
  push_cast
  ring


/-- For real `k ≠ 0` with `2r/k > 0`, the bracketed form 33.14.7 is real. -/
private lemma conj_coulombEnergyHKappa_ofReal {k S r : ℝ} (ℓ : ℕ) (h : 0 < 2 * r / k) :
    conj (coulombEnergyHKappa (k : ℂ) S ℓ r) = coulombEnergyHKappa (k : ℂ) S ℓ r := by
  have hz : (2 * (r : ℂ) / (k : ℂ)) = ((2 * r / k : ℝ) : ℂ) := by push_cast; ring
  have hs : ((2 * r / k : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr h
  unfold coulombEnergyHKappa
  rw [hz]
  simp only [map_mul, map_div₀, map_add, map_pow, map_neg, map_sub, ← exp_conj,
    conj_kummerU _ _ hs, conj_kummerM, ← Gamma_conj, conj_ofReal, map_natCast, map_one,
    map_ofNat]

/-- The Whittaker form of 33.14.7 is `coulombEnergyHFormula`. -/
private lemma whittaker_form_eq_coulombEnergyHFormula (ε : ℝ) (ℓ : ℕ) (r : ℝ) :
    Gamma (ℓ + 1 - coulombKappa ε r) / (π * coulombKappa ε r ^ ℓ) *
      (whittakerW (coulombKappa ε r) (ℓ + 1 / 2) (2 * r / coulombKappa ε r) +
        (-1) ^ ℓ * coulombSFactor ε r * Gamma (ℓ + 1 + coulombKappa ε r) / (2 * (2 * ℓ + 1)!) *
          whittakerM (coulombKappa ε r) (ℓ + 1 / 2) (2 * r / coulombKappa ε r)) =
      coulombEnergyHFormula ε ℓ r := by
  unfold coulombEnergyHFormula coulombEnergyHKappa whittakerW whittakerM
  set κ := coulombKappa ε r
  rw [show (1 / 2 : ℂ) + (ℓ + 1 / 2) - κ = ℓ + 1 - κ by ring,
    show (ℓ : ℂ) + 1 / 2 - κ + 1 / 2 = ℓ + 1 - κ by ring,
    show (1 : ℂ) + 2 * (ℓ + 1 / 2) = 2 * ℓ + 2 by ring,
    show (1 / 2 : ℂ) + (ℓ + 1 / 2) = ((ℓ + 1 : ℕ) : ℂ) by push_cast; ring,
    show (ℓ : ℂ) + 1 / 2 + 1 / 2 = ((ℓ + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast]

/-- For `ε > 0`, `κ = i ε^{-1/2}`. -/
private lemma coulombKappa_of_pos {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    coulombKappa ε r = I * ((ε ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  simp only [coulombKappa, not_lt.mpr hε.le, ↓reduceIte]

/-- For `ε > 0` and `r ≠ 0`, the bracketed form 33.14.7 is a real multiple of a value of `G_ℓ`:
both for `κ` and for `-κ`, which gives the same value. -/
private lemma coulombEnergyHKappa_pm_eq {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0) :
    ∃ x : ℝ, coulombEnergyHKappa (coulombKappa ε r) (coulombSFactor ε r) ℓ r = x ∧
      coulombEnergyHKappa (-coulombKappa ε r) (coulombSFactor ε r) ℓ r = x := by
  set t := ε ^ (-(1 / 2 : ℝ)) with ht
  have htp : 0 < t := Real.rpow_pos_of_pos hε _
  rw [coulombKappa_of_pos hε]
  rcases hr.lt_or_gt with hneg | hpos
  · -- `η = t`, `ρ = -r/t`
    have hS : coulombSFactor ε r = Real.exp (-π * t) := by
      simp only [coulombSFactor, not_lt.mpr hε.le, not_lt.mpr hneg.le, ↓reduceIte]
      congr 1; ring
    have hρ : 0 < -r / t := div_pos (neg_pos.mpr hneg) htp
    have hrr : r = -t * (-r / t) := by field_simp
    rw [hS, hrr]
    refine ⟨_, coulombEnergyHKappa_I_mul_eq_coulombG ℓ htp.ne' hρ, ?_⟩
    rw [show -(I * (t : ℂ)) = I * ((-t : ℝ) : ℂ) by push_cast; ring]
    exact coulombEnergyHKappa_I_mul_neg_eq_coulombG ℓ htp.ne' hρ
  · -- `η = -t`, `ρ = r/t`
    have hS : coulombSFactor ε r = Real.exp (-π * (-t)) := by
      simp only [coulombSFactor, not_lt.mpr hε.le, hpos, ↓reduceIte]
      congr 1; ring
    have hρ : 0 < r / t := div_pos hpos htp
    have hrr : r = -(-t) * (r / t) := by field_simp
    have ht0 : -t ≠ 0 := by linarith
    rw [hS, hrr]
    have h1 := coulombEnergyHKappa_I_mul_neg_eq_coulombG ℓ ht0 hρ
    rw [show ((-(-t) : ℝ) : ℂ) = (t : ℂ) by push_cast; ring] at h1
    exact ⟨_, h1, by
      rw [show -(I * (t : ℂ)) = I * ((-t : ℝ) : ℂ) by push_cast; ring]
      exact coulombEnergyHKappa_I_mul_eq_coulombG ℓ ht0 hρ⟩

/-- **DLMF 33.14.7 (Whittaker form)**: away from `ε = 0` and from the poles of `Γ(ℓ+1-κ)`,
`h(ε,ℓ;r) = Γ(ℓ+1-κ)/(πκ^ℓ) (W_{κ,ℓ+1/2}(2r/κ) + (-1)^ℓ S(ε,r) Γ(ℓ+1+κ)/(2(2ℓ+1)!)
M_{κ,ℓ+1/2}(2r/κ))`, the right-hand side being real (`r ≠ 0`). -/
@[dlmf 33.14.E7]
theorem ofReal_coulombEnergyH {ε : ℝ} (hε : ε ≠ 0) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0)
    (hpole : ∀ m : ℕ, (ℓ : ℂ) + 1 - coulombKappa ε r ≠ -(m : ℂ)) :
    (coulombEnergyH ε ℓ r : ℂ) = Gamma (ℓ + 1 - coulombKappa ε r) / (π * coulombKappa ε r ^ ℓ) *
      (whittakerW (coulombKappa ε r) (ℓ + 1 / 2) (2 * r / coulombKappa ε r) +
        (-1) ^ ℓ * coulombSFactor ε r * Gamma (ℓ + 1 + coulombKappa ε r) / (2 * (2 * ℓ + 1)!) *
          whittakerM (coulombKappa ε r) (ℓ + 1 / 2) (2 * r / coulombKappa ε r)) := by
  rw [whittaker_form_eq_coulombEnergyHFormula]
  have hre : coulombEnergyH ε ℓ r = (coulombEnergyHFormula ε ℓ r).re := by
    unfold coulombEnergyH
    split_ifs with h
    · exfalso
      rcases h with h | ⟨m, hm⟩
      · exact hε h
      · exact hpole m hm
    · rfl
  rw [hre]
  refine Complex.conj_eq_iff_re.mp ?_
  rcases hε.lt_or_gt with hneg | hpos
  · unfold coulombEnergyHFormula
    set t := (-ε) ^ (-(1 / 2 : ℝ))
    have htp : 0 < t := Real.rpow_pos_of_pos (neg_pos.mpr hneg) _
    rcases hr.lt_or_gt with hr' | hr'
    · have hk : coulombKappa ε r = ((-t : ℝ) : ℂ) := by
        simp only [coulombKappa, hneg, not_lt.mpr hr'.le, ↓reduceIte, t]
      rw [hk]
      exact conj_coulombEnergyHKappa_ofReal ℓ (div_pos_of_neg_of_neg (by linarith) (by linarith))
    · have hk : coulombKappa ε r = ((t : ℝ) : ℂ) := by
        simp only [coulombKappa, hneg, hr', ↓reduceIte, t]
      rw [hk]
      exact conj_coulombEnergyHKappa_ofReal ℓ (by positivity)
  · obtain ⟨x, h1, -⟩ := coulombEnergyHKappa_pm_eq hpos ℓ hr
    rw [coulombEnergyHFormula, h1, conj_ofReal]

/-- **The sign of `κ` is immaterial in 33.14.7** (DLMF §33.14(iii)): for `ε > 0` the bracketed
form with `-κ = -iε^{-1/2}` gives the same value. -/
@[dlmf 33.14.iii]
theorem coulombEnergyHKappa_neg {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0) :
    coulombEnergyHKappa (-coulombKappa ε r) (coulombSFactor ε r) ℓ r =
      coulombEnergyHKappa (coulombKappa ε r) (coulombSFactor ε r) ℓ r := by
  obtain ⟨x, h1, h2⟩ := coulombEnergyHKappa_pm_eq hε ℓ hr
  rw [h1, h2]

/-- **DLMF §33.14(iii)**: `h(ε,ℓ;r)` is an analytic function of `r` for `r ≠ 0` and of `ε` for
`ε ≠ 0`; it is continuous in `ε` at `ε = 0` and at the poles of `Γ(ℓ+1-κ)`, so that the limits
in the definition exist. -/
@[dlmf 33.14.iii]
theorem analyticAt_coulombEnergyH (ℓ : ℕ) :
    (∀ ε r : ℝ, r ≠ 0 → AnalyticAt ℝ (fun x => coulombEnergyH ε ℓ x) r) ∧
      (∀ ε r : ℝ, ε ≠ 0 → r ≠ 0 → AnalyticAt ℝ (fun e => coulombEnergyH e ℓ r) ε) ∧
      (∀ ε r : ℝ, r ≠ 0 →
        Tendsto (fun e => (coulombEnergyHFormula e ℓ r).re) (𝓝[≠] ε)
            (𝓝 (coulombEnergyH ε ℓ r))) := by
  sorry

/-! ### `A(ε,ℓ)`, `s` and `c` -/

/-- For `z` not a nonpositive integer, `Γ(z+n) = Γ(z) ∏_{j<n} (z+j)`. -/
private lemma Gamma_add_nat_eq_mul_prod {z : ℂ} (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) (n : ℕ) :
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
private lemma prod_range_sub_add_eq_mul_prod_sq_sub (κ : ℂ) (ℓ : ℕ) :
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
  have hG := Gamma_add_nat_eq_mul_prod hpole (2 * ℓ + 1)
  rw [show κ - ℓ + ((2 * ℓ + 1 : ℕ) : ℂ) = 1 + ℓ + κ by push_cast; ring] at hG
  have hG0 : Gamma (κ - ℓ) ≠ 0 := Complex.Gamma_ne_zero hpole
  rw [hG, mul_div_cancel_left₀ _ hG0, prod_range_sub_add_eq_mul_prod_sq_sub, coulombAProd,
      Finset.prod_range_succ']
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
theorem coulombEnergyS_re_eq_zero_of_neg {ε : ℝ} {ℓ : ℕ} (hB : coulombBFactor ε ℓ < 0) (r : ℝ) :
    (coulombEnergyS ε ℓ r).re = 0 ∧ (coulombEnergyC ε ℓ r).re = 0 := by
  constructor
  · rw [coulombEnergyS, ofReal_cpow_of_nonpos (by linarith : coulombBFactor ε ℓ / 2 ≤ 0),
      ← Complex.ofReal_neg, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ -(coulombBFactor ε ℓ / 2)),
      show (π : ℂ) * I * ((1 / 2 : ℝ) : ℂ) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    simp
  · rw [coulombEnergyC, ofReal_cpow_of_nonpos (by linarith : 2 * coulombBFactor ε ℓ ≤ 0),
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
theorem coulombEnergyS_orthogonality_dirac (ℓ : ℕ) {ε₂ : ℝ} (hε₂ : 0 < ε₂) {g : ℝ → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ioi 0) :
    Tendsto (fun R : ℝ => ∫ ε₁ in Ioi (0 : ℝ),
        g ε₁ * ∫ r in (0 : ℝ)..R, coulombEnergyS ε₁ ℓ r * coulombEnergyS ε₂ ℓ r)
      atTop (𝓝 (g ε₂)) := by
  sorry

/-! ### Hydrogenic functions -/

/-- For `ℓ + 1 ≤ n`, `A(-1/n², ℓ) ≥ 0`. -/
private lemma coulombAProd_neg_one_div_sq_nonneg {n ℓ : ℕ} (hn : ℓ + 1 ≤ n) :
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
theorem hydrogenRadial_eq_coulombEnergyS {n ℓ : ℕ} (hn : ℓ + 1 ≤ n) (r : ℝ) :
    (hydrogenRadial n ℓ r : ℂ) =
      (((-1) ^ (ℓ + 1 + n) * Real.sqrt (2 / (n : ℝ) ^ 3) : ℝ) : ℂ) *
        coulombEnergyS (-1 / (n : ℝ) ^ 2) ℓ r := by
  have hB : coulombBFactor (-1 / (n : ℝ) ^ 2) ℓ = coulombAProd (-1 / (n : ℝ) ^ 2) ℓ := by
    have : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by positivity
    have h : ¬ (0 < -1 / (n : ℝ) ^ 2) := by rw [neg_div]; linarith
    simp only [coulombBFactor, h, ↓reduceIte]
  have hA := coulombAProd_neg_one_div_sq_nonneg hn
  rw [hydrogenRadial, coulombEnergyS, hB, Real.sqrt_eq_rpow (coulombAProd _ ℓ / 2),
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity)]
  push_cast
  ring

/-- `∏_{k=0}^{ℓ} (n² - k²) · N! = n (2ℓ+1+N)!` for `n = ℓ+1+N`. -/
private lemma prod_range_sq_sub_sq_mul_factorial (ℓ N : ℕ) :
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
private lemma coulombAProd_hydrogen (ℓ N : ℕ) :
    coulombAProd (-1 / ((ℓ + 1 + N : ℕ) : ℝ) ^ 2) ℓ * N ! * ((ℓ + 1 + N : ℕ) : ℝ) ^ (2 * ℓ + 1) =
      (2 * ℓ + 1 + N)! := by
  have hn : ((ℓ + 1 + N : ℕ) : ℝ) ≠ 0 := by positivity
  have h := prod_range_sq_sub_sq_mul_factorial ℓ N
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
private lemma coulombKappa_hydrogen {n : ℕ} (hn : 0 < n) :
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
        laguerrePolynomialL (2 * ℓ + 1) (n - ℓ - 1) (2 * r / n) := by
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
  have hA := coulombAProd_neg_one_div_sq_nonneg (n := n) (ℓ := ℓ) (by omega)
  have hAe := coulombAProd_hydrogen ℓ N
  rw [← hn_def, ← hε_def] at hAe
  have hf : (coulombEnergyF ε ℓ r : ℂ) = coulombEnergyFKummer (n : ℂ) ℓ r := by
    rw [ofReal_coulombEnergyF hε0]
    rcases coulombKappa_eq_or_eq_neg ε r with h | h
    · rw [h, hε_def, coulombKappa_hydrogen (by omega)]
    · rw [h, coulombEnergyFKummer_neg, hε_def, coulombKappa_hydrogen (by omega)]
  have hK : coulombEnergyFKummer (n : ℂ) ℓ r = (((2 * r) ^ (ℓ + 1) * Real.exp (-r / n) *
      (N ! / (2 * ℓ + 1 + N)!) : ℝ) : ℂ) * laguerrePolynomialL (2 * ℓ + 1) N (2 * r / n) := by
    unfold coulombEnergyFKummer laguerrePolynomialL
    have hM : (ℓ : ℂ) + 1 - n = -(N : ℂ) := by rw [hn_def]; push_cast; ring
    rw [hM, show (2 * ℓ + 1 : ℂ) + 1 = 2 * ℓ + 2 by ring]
    have hP : ((2 * ℓ + 1)! : ℂ) * DLMF.Hypergeometric.pochhammer (2 * ℓ + 2) N =
        (2 * ℓ + 1 + N)! := by
      have := factorial_mul_ascPochhammer ℂ (2 * ℓ + 1) N
      push_cast at this
      rw [show (2 * ℓ + 2 : ℂ) = 2 * ℓ + 1 + 1 by ring]
      exact this
    have h1 : ((2 * ℓ + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : ((2 * ℓ + 1 + N)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h3 : (N ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hp0 : DLMF.Hypergeometric.pochhammer (2 * ℓ + 2) N ≠ 0 := by
      intro h; rw [h, mul_zero] at hP; exact h2 hP.symm
    have hp0' : DLMF.Hypergeometric.pochhammer (2 * ((ℓ : ℂ) + 1)) N ≠ 0 := by
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
    laguerrePolynomialL (2 * ℓ + 1) N (2 * r / n)) * hk

/-! ### Orthonormality of the hydrogen radial functions -/

section HydrogenOrthonormality

open Polynomial DLMF.Hypergeometric

/-- `x^k e^{-cx}` is integrable on `(0,∞)` and tends to `0` at `∞`, for `c > 0`. -/
private lemma pow_mul_exp_neg_mul_props (k : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-c * x)) (Ioi 0) ∧
      Tendsto (fun x : ℝ => x ^ k * Real.exp (-c * x)) atTop (𝓝 0) := by
  constructor
  · have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := k) (p := 1) (b := c)
      (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith) one_pos hc
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [Real.rpow_natCast, Real.rpow_one]
  · have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
      (tendsto_id.const_mul_atTop hc)
    have h2 := h.const_mul ((c ^ k)⁻¹)
    rw [mul_zero] at h2
    refine h2.congr fun x => ?_
    simp only [Function.comp_apply, id]
    rw [mul_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hc.ne'), one_mul, neg_mul]

/-- A polynomial times `e^{-cx}` is integrable on `(0,∞)` and tends to `0` at `∞`, for
`c > 0`. -/
private lemma eval_mul_exp_neg_mul_props (Q : ℝ[X]) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => Q.eval x * Real.exp (-c * x)) (Ioi 0) ∧
      Tendsto (fun x : ℝ => Q.eval x * Real.exp (-c * x)) atTop (𝓝 0) := by
  have he : (fun x : ℝ => Q.eval x * Real.exp (-c * x)) = fun x =>
      ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * (x ^ i * Real.exp (-c * x)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [he]
  constructor
  · exact integrable_finsetSum _ fun i _ => ((pow_mul_exp_neg_mul_props i hc).1).const_mul _
  · have := tendsto_finsetSum (Finset.range (Q.natDegree + 1)) fun i _ =>
      ((pow_mul_exp_neg_mul_props i hc).2).const_mul (Q.coeff i)
    simpa using this

/-- The polynomial factor of `φ_{n,ℓ}(r) = Q(r) e^{-r/n}` (from 33.14.14). -/
private def hydrogenPoly (n ℓ : ℕ) : ℝ[X] :=
  C ((-1) ^ (ℓ + 1 + n) / (n : ℝ) ^ (ℓ + 2) * Real.sqrt ((n - ℓ - 1)! / (n + ℓ)!)) *
    (C 2 * X) ^ (ℓ + 1) * (laguerrePolyLR (2 * ℓ + 1) (n - ℓ - 1)).comp (C (2 / (n : ℝ)) * X)

private lemma hydrogenRadial_eq_eval (ℓ : ℕ) {n : ℕ} (hn : ℓ + 1 ≤ n) (r : ℝ) :
    hydrogenRadial n ℓ r = (hydrogenPoly n ℓ).eval r * Real.exp (-r / n) := by
  apply Complex.ofReal_injective
  rw [hydrogenRadial_eq_laguerre hn]
  have hL : laguerrePolynomialL (2 * ℓ + 1) (n - ℓ - 1) (2 * r / n) =
      (((laguerrePolyLR (2 * ℓ + 1) (n - ℓ - 1)).eval (2 * r / n) : ℝ) : ℂ) := by
    have h1 := eval_map_laguerrePolyLR (2 * ℓ + 1) (n - ℓ - 1) ((2 * r / n : ℝ) : ℂ)
    rw [Polynomial.eval_map, show ((2 * r / n : ℝ) : ℂ) = algebraMap ℝ ℂ (2 * r / n) from rfl,
      Polynomial.eval₂_at_apply] at h1
    rw [show (((laguerrePolyLR (2 * ℓ + 1) (n - ℓ - 1)).eval (2 * r / n) : ℝ) : ℂ) =
      algebraMap ℝ ℂ ((laguerrePolyLR (2 * ℓ + 1) (n - ℓ - 1)).eval (2 * r / n)) from rfl, h1]
    push_cast
    rfl
  rw [hL, hydrogenPoly]
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_comp]
  push_cast
  ring_nf

/-- `φ_{n,ℓ}` has the derivative `(Q' - Q/n) e^{-r/n}`. -/
private lemma hasDerivAt_hydrogenRadial (ℓ : ℕ) {n : ℕ} (hn : ℓ + 1 ≤ n) (r : ℝ) :
    HasDerivAt (hydrogenRadial n ℓ)
      (((hydrogenPoly n ℓ).derivative.eval r - (hydrogenPoly n ℓ).eval r / n) *
        Real.exp (-r / n)) r := by
  have he : hydrogenRadial n ℓ = fun r => (hydrogenPoly n ℓ).eval r * Real.exp (-r / n) :=
    funext (hydrogenRadial_eq_eval ℓ hn)
  rw [he]
  have h1 := (hydrogenPoly n ℓ).hasDerivAt r
  have h2 : HasDerivAt (fun r : ℝ => Real.exp (-r / n)) (Real.exp (-r / n) * (-1 / n)) r := by
    have := ((hasDerivAt_id r).neg.div_const (n : ℝ)).exp
    simpa [neg_div] using this
  convert h1.mul h2 using 1
  ring

/-- The radial equation for `φ_{n,ℓ}`: `φ'' = -(ε + 2/r - ℓ(ℓ+1)/r²) φ` with `ε = -1/n²`. -/
private lemma hasDerivAt_deriv_hydrogenRadial (ℓ n : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (deriv (hydrogenRadial n ℓ))
      (-(-1 / (n : ℝ) ^ 2 + 2 / r - ℓ * (ℓ + 1) / r ^ 2) * hydrogenRadial n ℓ r) r := by
  set K := (-1) ^ (ℓ + 1 + n) * Real.sqrt (2 / (n : ℝ) ^ 3) *
    Real.sqrt (coulombBFactor (-1 / (n : ℝ) ^ 2) ℓ / 2)
  have he : hydrogenRadial n ℓ = fun r => K * coulombEnergyF (-1 / (n : ℝ) ^ 2) ℓ r := rfl
  have hd : deriv (hydrogenRadial n ℓ) = fun r => K *
      deriv (coulombEnergyF (-1 / (n : ℝ) ^ 2) ℓ) r := by
    funext x
    rw [he]
    exact deriv_const_mul K (hasDerivAt_coulombEnergyF _ ℓ x).differentiableAt
  rw [hd]
  have h := ((coulombEnergyF_ode (-1 / (n : ℝ) ^ 2) ℓ hr).2).const_mul K
  convert h using 1
  rw [he]
  ring

/-- `Q(0) = 0`: the polynomial factor of `φ_{n,ℓ}` has the factor `r^{ℓ+1}`. -/
private lemma hydrogenPoly_eval_zero (n ℓ : ℕ) : (hydrogenPoly n ℓ).eval 0 = 0 := by
  simp [hydrogenPoly]

/-- Orthogonality of `φ_{m,ℓ}` and `φ_{n,ℓ}` for `m ≠ n`, from the radial equation. -/
private lemma integral_hydrogenRadial_mul_of_ne {m n ℓ : ℕ} (hm : ℓ + 1 ≤ m) (hn : ℓ + 1 ≤ n)
    (hmn : m ≠ n) :
    ∫ r in Ioi (0 : ℝ), hydrogenRadial m ℓ r * hydrogenRadial n ℓ r = 0 := by
  set Qm := hydrogenPoly m ℓ
  set Qn := hydrogenPoly n ℓ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set c : ℝ := 1 / m + 1 / n
  have hc : 0 < c := by positivity
  have hexp : ∀ r : ℝ, Real.exp (-r / m) * Real.exp (-r / n) = Real.exp (-c * r) := by
    intro r; rw [← Real.exp_add]; congr 1; simp only [c]; ring
  set R : ℝ[X] := (Qm.derivative - C (1 / (m : ℝ)) * Qm) * Qn -
    Qm * (Qn.derivative - C (1 / (n : ℝ)) * Qn)
  set W : ℝ → ℝ := fun r => deriv (hydrogenRadial m ℓ) r * hydrogenRadial n ℓ r -
    hydrogenRadial m ℓ r * deriv (hydrogenRadial n ℓ) r
  have hW : W = fun r => R.eval r * Real.exp (-c * r) := by
    funext r
    simp only [W, (hasDerivAt_hydrogenRadial ℓ hm r).deriv,
      (hasDerivAt_hydrogenRadial ℓ hn r).deriv, hydrogenRadial_eq_eval ℓ hm,
          hydrogenRadial_eq_eval ℓ hn, R, eval_sub, eval_mul, eval_C,
      ← hexp]
    ring
  set e : ℝ := -1 / (n : ℝ) ^ 2 - -1 / (m : ℝ) ^ 2
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W
      (e * (hydrogenRadial m ℓ x * hydrogenRadial n ℓ x)) x := by
    intro x hx
    have hx0 : x ≠ 0 := (mem_Ioi.mp hx).ne'
    have h1 := hasDerivAt_deriv_hydrogenRadial ℓ m hx0
    have h2 := (hasDerivAt_hydrogenRadial ℓ hn x)
    rw [← (hasDerivAt_hydrogenRadial ℓ hn x).deriv] at h2
    have h3 := (hasDerivAt_hydrogenRadial ℓ hm x)
    rw [← (hasDerivAt_hydrogenRadial ℓ hm x).deriv] at h3
    have h4 := hasDerivAt_deriv_hydrogenRadial ℓ n hx0
    convert (h1.mul h2).sub (h3.mul h4) using 1
    simp only [e]
    ring
  have hint : IntegrableOn (fun x => e * (hydrogenRadial m ℓ x * hydrogenRadial n ℓ x))
      (Ioi 0) := by
    have : IntegrableOn (fun x => e * ((Qm * Qn).eval x * Real.exp (-c * x))) (Ioi 0) :=
      ((eval_mul_exp_neg_mul_props (Qm * Qn) hc).1).const_mul e
    refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioi
    simp only [hydrogenRadial_eq_eval ℓ hm, hydrogenRadial_eq_eval ℓ hn, eval_mul, ← hexp]
    ring
  have hlim : Tendsto W atTop (𝓝 0) := by
    rw [hW]; exact (eval_mul_exp_neg_mul_props R hc).2
  have hcont : ContinuousWithinAt W (Ici 0) 0 := by
    rw [hW]
    exact (R.continuous.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
      |>.continuousWithinAt
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hW0 : W 0 = 0 := by
    rw [hW]; simp [R, hydrogenPoly_eval_zero, Qm, Qn]
  rw [hW0, sub_zero, integral_const_mul] at hFTC
  have he : e ≠ 0 := by
    simp only [e]
    intro h
    have : (m : ℝ) ^ 2 = (n : ℝ) ^ 2 := by field_simp at h; linarith
    have : (m : ℝ) = n := by
      have := (sq_eq_sq₀ hm0.le hn0.le).mp this; exact this
    exact hmn (by exact_mod_cast this)
  exact (mul_eq_zero.mp hFTC).resolve_left he

/-- `∫₀^∞ (L_N^{(α)})² x^{α+1} e^{-x} dx = (2N+α+1) Γ(N+α+1)/N!`. -/
private lemma integral_laguerrePolynomialL_sq_mul_id {α : ℝ} (hα : -1 < α) (N : ℕ) :
    ∫ x : ℝ in Ioi 0, laguerrePolynomialL α N x * laguerrePolynomialL α N x * (x : ℂ) *
      (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ)) =
      (2 * N + α + 1) * Gamma (N + α + 1) / N ! := by
  set a : ℕ → ℂ := fun j => pochhammer ((α : ℂ) + 1) N / N ! * kummerMCoeff (-(N : ℂ)) (α + 1) j
  have hexp : (fun x : ℝ => laguerrePolynomialL α N x * laguerrePolynomialL α N x * (x : ℂ) *
      (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) = fun x : ℝ => ∑ j ∈ Finset.range (N + 1),
        a j * (laguerrePolynomialL α N x * (x : ℂ) ^ (j + 1) * (x : ℂ) ^ (α : ℂ) *
            exp (-(x : ℂ))) := by
    funext x
    have h := laguerrePolynomialL_eq_sum_coeff (α : ℂ) N x
    calc _ = (laguerrePolynomialL α N x * (x : ℂ) * (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) *
          ∑ j ∈ Finset.range (N + 1), a j * (x : ℂ) ^ j := by
          rw [← h]; ring
      _ = _ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, integral_finsetSum _ (fun j _ =>
    (integrable_laguerrePolynomialL_mul_monomial hα N (j + 1)).const_mul _)]
  simp_rw [integral_const_mul, integral_laguerrePolynomialL_mul_monomial hα]
  have hc : ∀ j : ℕ, (α : ℂ) + 1 ≠ -j := not_neg_nat_of_re_pos (by
    simp only [add_re, ofReal_re, one_re]; linarith)
  have hG : ∀ k : ℕ, (α : ℂ) + k + 1 ≠ 0 := fun k h => by
    have := congrArg Complex.re h
    simp at this
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  rcases N with _ | M
  · simp [a, kummerMCoeff, pochhammer_zero]
    exact Gamma_add_one _ (by simpa using hG 0)
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero (fun j hj => by
      have hj := Finset.mem_range.mp hj
      rw [show ((j + 1 : ℕ) : ℂ) = ((j + 1 : ℕ) : ℂ) from rfl]
      simp only [pochhammer_neg_coe_nat,
          Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : j + 1 < M + 1)]
      simp)]
    have hp := pochhammer_ne_zero_of_not_neg_nat hc M
    have g1 : Gamma ((α : ℂ) + ((M + 1 : ℕ) : ℂ) + 1) = (α + M + 1) * Gamma (α + M + 1) := by
      rw [show (α : ℂ) + ((M + 1 : ℕ) : ℂ) + 1 = (α + M + 1) + 1 by push_cast; ring]
      exact Gamma_add_one _ (hG M)
    have g2 : Gamma ((α : ℂ) + ((M + 1 + 1 : ℕ) : ℂ) + 1) =
        (α + M + 2) * ((α + M + 1) * Gamma (α + M + 1)) := by
      rw [show (α : ℂ) + ((M + 1 + 1 : ℕ) : ℂ) + 1 = (α + ((M + 1 : ℕ) : ℂ) + 1) + 1 by
        push_cast; ring, Gamma_add_one _ (hG (M + 1)), g1]
      push_cast; ring
    have g0 : Gamma (((M + 1 : ℕ) : ℂ) + α + 1) = (α + M + 1) * Gamma (α + M + 1) := by
      rw [← g1]; congr 1; ring
    have d1 : (M + 1).descFactorial M = (M + 1)! := by
      have := Nat.factorial_mul_descFactorial (show M ≤ M + 1 by omega)
      rw [show M + 1 - M = 1 by omega] at this
      simpa using this
    have d2 : (M + 1 + 1).descFactorial (M + 1) = (M + 2)! := by
      have := Nat.factorial_mul_descFactorial (show M + 1 ≤ M + 1 + 1 by omega)
      rw [show M + 1 + 1 - (M + 1) = 1 by omega] at this
      simpa using this
    have p1 : pochhammer (-((M + 1 : ℕ) : ℂ)) M = (-1) ^ M * ((M + 1)! : ℂ) := by
      rw [pochhammer_neg_coe_nat, d1]
    have p2 : pochhammer (-((M + 1 : ℕ) : ℂ)) (M + 1) = (-1) ^ (M + 1) * ((M + 1)! : ℂ) := by
      rw [pochhammer_neg_coe_nat, Nat.descFactorial_self]
    have p3 : pochhammer (-((M + 1 + 1 : ℕ) : ℂ)) (M + 1) = (-1) ^ (M + 1) * ((M + 2)! : ℂ) := by
      rw [pochhammer_neg_coe_nat, d2]
    simp only [a, kummerMCoeff, p1, p2, p3, g1, g2, g0, pochhammer_succ _ M]
    have hpa : (α : ℂ) + 1 + M ≠ 0 := by
      have := hG M; rwa [add_right_comm] at this
    push_cast [Nat.factorial_succ]
    field_simp
    ring_nf
    rw [Even.neg_one_pow ⟨M, by ring⟩]
    ring

/-- `∫₀^∞ φ_{n,ℓ}² = 1`, by the substitution `x = 2r/n` and the Laguerre moment above. -/
private lemma integral_hydrogenRadial_sq {n ℓ : ℕ} (hn : ℓ + 1 ≤ n) :
    ∫ r in Ioi (0 : ℝ), hydrogenRadial n ℓ r * hydrogenRadial n ℓ r = 1 := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hn0 : (0 : ℝ) < ((ℓ + 1 + N : ℕ) : ℝ) := by positivity
  set m : ℝ := ((ℓ + 1 + N : ℕ) : ℝ) with hm
  set K : ℝ := (-1) ^ (ℓ + 1 + (ℓ + 1 + N)) / m ^ (ℓ + 2) *
    Real.sqrt ((ℓ + 1 + N - ℓ - 1)! / (ℓ + 1 + N + ℓ)!) with hK
  clear_value m
  set g : ℝ → ℂ := fun x => laguerrePolynomialL ((2 * ℓ + 1 : ℝ) : ℂ) N x *
    laguerrePolynomialL ((2 * ℓ + 1 : ℝ) : ℂ) N x * (x : ℂ) * (x : ℂ) ^ (((2 * ℓ + 1 : ℝ)) : ℂ) *
      exp (-(x : ℂ)) with hg
  have hpt : ∀ r : ℝ, ((hydrogenRadial (ℓ + 1 + N) ℓ r * hydrogenRadial (ℓ + 1 + N) ℓ r : ℝ) : ℂ) =
      ((K ^ 2 * m ^ (2 * ℓ + 2) : ℝ) : ℂ) * g ((2 / m) * r) := by
    intro r
    have h := hydrogenRadial_eq_laguerre hn r
    rw [← hm, ← hK] at h
    rw [show ℓ + 1 + N - ℓ - 1 = N by omega] at h
    set x := 2 / m * r with hx
    have hL : (2 * (r : ℂ) / ((ℓ + 1 + N : ℕ) : ℂ)) = (x : ℂ) := by
      rw [hx, hm]; push_cast; ring
    have h2r : 2 * r = m * x := by rw [hx]; field_simp
    have hE : Real.exp (-r / m) * Real.exp (-r / m) = Real.exp (-x) := by
      rw [← Real.exp_add, hx]; congr 1; ring
    rw [hL, h2r] at h
    rw [Complex.ofReal_mul, h, hg]
    simp only
    rw [show (((2 * ℓ + 1 : ℝ)) : ℂ) = ((2 * ℓ + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
      ← Complex.ofReal_neg, ← Complex.ofReal_exp, ← hE]
    push_cast
    ring
  have hK2 : K ^ 2 = (N ! : ℝ) / ((2 * ℓ + 1 + N)! : ℝ) / m ^ (2 * ℓ + 4) := by
    rw [hK, show ℓ + 1 + N - ℓ - 1 = N by omega, show ℓ + 1 + N + ℓ = 2 * ℓ + 1 + N by ring,
      mul_pow, div_pow, Real.sq_sqrt (by positivity), ← pow_mul,
      Even.neg_one_pow ⟨ℓ + 1 + (ℓ + 1 + N), by ring⟩, ← pow_mul]
    ring_nf
  have hJ := integral_laguerrePolynomialL_sq_mul_id (α := 2 * ℓ + 1)
    (by have := (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ); linarith) N
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hpt]
  rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 (by positivity : 0 < 2 / m), mul_zero,
    hg, hJ, show (N : ℂ) + (((2 * ℓ + 1 : ℝ)) : ℂ) + 1 = ((2 * ℓ + 1 + N : ℕ) : ℂ) + 1 by
      push_cast; ring, Complex.Gamma_nat_eq_factorial, hK2]
  have hm' : (m : ℂ) = ((ℓ + 1 + N : ℕ) : ℂ) := by rw [hm]; norm_cast
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hf1 : (N ! : ℂ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  have hf2 : ((2 * ℓ + 1 + N)! : ℂ) ≠ 0 := by exact_mod_cast (2 * ℓ + 1 + N).factorial_ne_zero
  simp only [Complex.real_smul]
  push_cast
  field_simp
  rw [hm']
  push_cast
  ring

end HydrogenOrthonormality

/-- **DLMF 33.14.15**: `∫₀^∞ φ_{m,ℓ}(r) φ_{n,ℓ}(r) dr = δ_{m,n}` for `m, n ≥ ℓ+1`. -/
@[dlmf 33.14.E15]
theorem hydrogenRadial_orthonormal {m n ℓ : ℕ} (hm : ℓ + 1 ≤ m) (hn : ℓ + 1 ≤ n) :
    ∫ r in Ioi (0 : ℝ), hydrogenRadial m ℓ r * hydrogenRadial n ℓ r = if m = n then 1 else 0 := by
  split_ifs with h
  · subst h
    exact integral_hydrogenRadial_sq hm
  · exact integral_hydrogenRadial_mul_of_ne hm hn h

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
    coulombEnergyH ε ℓ r * deriv (coulombEnergyF ε ℓ) r - deriv (coulombEnergyH ε ℓ) r *
        coulombEnergyF ε ℓ r =
      2 / π := by
  sorry

/-- **DLMF 33.14.16**: `𝒲{c, s} = 1/π` for `r ≠ 0`, whenever `B(ε,ℓ) ≠ 0` (for `B < 0` both
`s` and `c` are imaginary and the principal powers multiply to `1/2`). -/
@[dlmf 33.14.E16]
theorem coulomb_wronskian_cs {ε : ℝ} {ℓ : ℕ} (hB : coulombBFactor ε ℓ ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    coulombEnergyC ε ℓ r * deriv (coulombEnergyS ε ℓ) r - deriv (coulombEnergyC ε ℓ) r *
        coulombEnergyS ε ℓ r =
      1 / π := by
  sorry

end DLMF.Coulomb
