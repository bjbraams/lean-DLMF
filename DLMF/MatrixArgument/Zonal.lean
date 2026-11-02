/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.MatrixArgument.GammaBeta
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Partitions and zonal polynomials (DLMF §35.4)

The zonal polynomials are defined in `DLMF.MatrixArgument.Basic` by DLMF's own formulas 35.4.2
and 35.4.3, an integral over the orthogonal group `O(m)` against its normalized Haar measure.
This file develops their properties.

## Main definitions

* `HasContinuousCoeffs`: a family of polynomials whose coefficients depend continuously on a
  parameter.
* `diagonalConjPoly`, `zonalIntegrandPoly`: the polynomial matrix `H diag(X₁, …, X_m) Hᵀ` and
  the integrand of DLMF 35.4.3 at a diagonal argument, as a polynomial.

## Main results

* `isProbabilityMeasure_orthogonalHaar`, `isMulRightInvariant_orthogonalHaar`: the Haar
  measure `orthogonalHaar m` is a probability measure and is also right invariant (`O(m)` is
  compact), so integrals over `O(m)` are invariant under `H ↦ H H₀`.
* `multivariateGammaVec_add_div`: `Γ_m(a + κ) / Γ_m(a) = [a]_κ` (DLMF 35.4.1).
* `zonalPolynomial_one`: `Z_κ(I)` is the value `zonalPolynomialAtOne κ` (DLMF 35.4.2).
* `zonalPolynomial_eq_dlmf`: DLMF 35.4.3 in DLMF's form, with the factor `|T|^{k_m}` outside
  the integral.
* `zonalPolynomial_zero`: `Z_κ(0) = 1` for `κ = 0` and `0` otherwise (DLMF 35.4.4).
* `zonalPolynomial_conj`: orthogonal invariance (DLMF 35.4.5).
* `zonalPolynomial_exists_symmetric`: `Z_κ` is a symmetric homogeneous polynomial in the
  eigenvalues (DLMF §35.4(ii)).
* `sum_zonalPolynomial`: `∑_{|κ|=k} Z_κ(T) = (tr T)^k` (DLMF 35.4.6).
* `integral_zonalPolynomial_conj`: the mean-value formula DLMF 35.4.7.
* `hasIntegralOn_zonalPolynomial_laplace`, `hasIntegralOn_zonalPolynomial_beta`: the Laplace
  and beta integrals DLMF 35.4.8 and 35.4.9.
* `zonalPolynomial_smul`, `zonalPolynomial_neg`: homogeneity of `Z_κ`.
* `zonalPolynomial_fin_one`: for `m = 1`, `Z_{(k)}(t) = t^k`.

## Implementation notes

In DLMF 35.4.7 and 35.4.9 DLMF evaluates `Z_κ` at a product of two symmetric matrices, meaning
the function of its eigenvalues; the statements use the symmetric matrix `S^{1/2} M S^{1/2}`
with the same eigenvalues, for positive-definite `S`.
-/

@[expose] public noncomputable section

open MeasureTheory Matrix Finset
open scoped Nat MatrixOrder

namespace DLMF.MatrixArgument

/-! ## The Haar measure on `O(m)` -/

/-- The real orthogonal group inherits second countability from its finite-dimensional matrix
space. -/
instance secondCountableTopology_orthogonalGroup (m : ℕ) :
    SecondCountableTopology (Matrix.orthogonalGroup (Fin m) ℝ) :=
  haveI : SecondCountableTopology (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin m → ℝ))
  TopologicalSpace.Subtype.secondCountableTopology _

/-- The normalized Haar measure on the compact orthogonal group has total mass one. -/
instance isProbabilityMeasure_orthogonalHaar (m : ℕ) :
    IsProbabilityMeasure (orthogonalHaar m) :=
  ⟨by
    have h := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts
      (Matrix.orthogonalGroup (Fin m) ℝ)))
    rw [TopologicalSpace.PositiveCompacts.coe_top] at h
    exact h⟩

/-- The normalized measure on the orthogonal group is a Haar measure. -/
instance isHaarMeasure_orthogonalHaar (m : ℕ) : (orthogonalHaar m).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

/-- The normalized Haar measure of the compact group `O(m)` is also right invariant. -/
instance isMulRightInvariant_orthogonalHaar (m : ℕ) :
    (orthogonalHaar m).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h := Measure.haarMeasure_unique (Measure.map (· * g) (orthogonalHaar m))
    (⊤ : TopologicalSpace.PositiveCompacts (Matrix.orthogonalGroup (Fin m) ℝ))
  rw [h]
  have h1 : Measure.map (· * g) (orthogonalHaar m)
      ((⊤ : TopologicalSpace.PositiveCompacts (Matrix.orthogonalGroup (Fin m) ℝ)) :
        Set (Matrix.orthogonalGroup (Fin m) ℝ)) = 1 := by
    rw [TopologicalSpace.PositiveCompacts.coe_top,
      Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
    exact measure_univ
  rw [h1, one_smul]
  rfl

/-- An orthogonal matrix has determinant `±1`, so `|HTHᵀ| = |T|`. -/
private lemma det_orthogonal_conj {m : ℕ} (H : Matrix.orthogonalGroup (Fin m) ℝ)
    (T : Matrix (Fin m) (Fin m) ℝ) :
    ((H : Matrix (Fin m) (Fin m) ℝ) * T * (H : Matrix (Fin m) (Fin m) ℝ)ᵀ).det = T.det := by
  have hH : (H : Matrix (Fin m) (Fin m) ℝ) * (H : Matrix (Fin m) (Fin m) ℝ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).mp H.2
  have hd : (H : Matrix (Fin m) (Fin m) ℝ).det * (H : Matrix (Fin m) (Fin m) ℝ).det = 1 := by
    have := congrArg Matrix.det hH
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  linear_combination T.det * hd

/-! ## 35.4.1: the partitional shifted factorial as a ratio of gamma functions -/

/-- Identity under the stated parameter and domain assumptions: `Complex.Gamma (z + n) =
(ascPochhammer ℂ n).eval z * Complex.Gamma z`. -/
private lemma Gamma_add_nat_eq_eval_ascPochhammer_mul {z : ℂ} (hz : Complex.Gamma z ≠ 0) (n : ℕ) :
    Complex.Gamma (z + n) = (ascPochhammer ℂ n).eval z * Complex.Gamma z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzn : z + n ≠ 0 := by
      intro h
      have hz' : z = -(n : ℂ) := by linear_combination h
      exact hz (by rw [hz']; exact Complex.Gamma_neg_nat_eq_zero n)
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hzn, ih, ascPochhammer_succ_eval]
    ring

/-- DLMF 35.4.1: `[a]_κ = Γ_m(a + κ) / Γ_m(a)`, where `Γ_m(a + κ) = Γ_m(a + k₁, …, a + k_m)`
(35.3.5), whenever `Γ_m(a) ≠ 0` (no `a - (j-1)/2` is a pole of `Γ`). -/
@[dlmf 35.4.E1]
theorem multivariateGammaVec_add_div {m : ℕ} (a : ℂ) (κ : Fin m → ℕ)
    (ha : multivariateGamma m a ≠ 0) :
    multivariateGammaVec m (fun j => a + κ j) / multivariateGamma m a =
      partitionalShiftedFactorial a κ := by
  unfold multivariateGamma at ha
  have hπ : (Real.pi : ℂ) ^ (((m : ℂ) * ((m : ℂ) - 1)) / 4) ≠ 0 := left_ne_zero_of_mul ha
  have hΓ : ∀ j : Fin m, Complex.Gamma (a - (j : ℂ) / 2) ≠ 0 :=
    fun j => Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul ha) j (Finset.mem_univ _)
  have hprod : ∀ j : Fin m, Complex.Gamma (a + (κ j : ℂ) - (j : ℂ) / 2) =
      (ascPochhammer ℂ (κ j)).eval (a - (j : ℂ) / 2) * Complex.Gamma (a - (j : ℂ) / 2) := by
    intro j
    rw [← Gamma_add_nat_eq_eval_ascPochhammer_mul (hΓ j)]
    ring_nf
  unfold multivariateGammaVec multivariateGamma partitionalShiftedFactorial
  simp_rw [hprod, Finset.prod_mul_distrib]
  rw [mul_div_mul_left _ _ hπ, mul_div_assoc, div_self (Finset.prod_ne_zero_iff.mpr
    fun j _ => hΓ j), mul_one]

/-! ## 35.4.2–35.4.5 -/

/-- DLMF 35.4.2: the value of the zonal polynomial at the identity is `zonalPolynomialAtOne κ`,
`|κ|! 2^{2|κ|} [m/2]_κ ∏_{1≤j<l≤ℓ(κ)} (2k_j - 2k_l - j + l) / ∏_{j=1}^{ℓ(κ)} (2k_j + ℓ(κ) - j)!`.
-/
@[dlmf 35.4.E2]
theorem zonalPolynomial_one {m : ℕ} (κ : Fin m → ℕ) :
    zonalPolynomial κ 1 = zonalPolynomialAtOne κ := by
  unfold zonalPolynomial
  have hint : ∀ H : Matrix.orthogonalGroup (Fin m) ℝ,
      (∏ j : Fin m, leadingMinor ((H : Matrix (Fin m) (Fin m) ℝ) * 1 *
        (H : Matrix (Fin m) (Fin m) ℝ)ᵀ) (j.1 + 1) ^ (κ j - nextPart κ j)) = 1 := by
    intro H
    rw [mul_one, (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).mp H.2]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [leadingMinor, dite_eq_left (by omega : j.1 + 1 ≤ m),
      Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one, one_pow]
  simp_rw [hint]
  simp

/-- DLMF 35.4.3 in DLMF's form: for `m ≥ 1` (written `m + 1`),
`Z_κ(T) = Z_κ(I) |T|^{k_m} ∫_{O(m)} ∏_{j=1}^{m-1} |(HTH⁻¹)_j|^{k_j - k_{j+1}} dH`
(with `H⁻¹ = Hᵀ`). -/
@[dlmf 35.4.E3]
theorem zonalPolynomial_eq_dlmf {m : ℕ} (κ : Fin (m + 1) → ℕ)
    (T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    zonalPolynomial κ T = zonalPolynomialAtOne κ * T.det ^ κ (Fin.last m) *
      ∫ H, ∏ j : Fin m,
        leadingMinor ((H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * T *
          (H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)ᵀ) (j.1 + 1) ^
            (κ j.castSucc - κ j.succ) ∂orthogonalHaar (m + 1) := by
  unfold zonalPolynomial
  have hint : ∀ H : Matrix.orthogonalGroup (Fin (m + 1)) ℝ,
      (∏ j : Fin (m + 1), leadingMinor ((H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * T *
        (H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)ᵀ) (j.1 + 1) ^ (κ j - nextPart κ j)) =
      (∏ j : Fin m, leadingMinor ((H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * T *
        (H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)ᵀ) (j.1 + 1) ^
          (κ j.castSucc - κ j.succ)) * T.det ^ κ (Fin.last m) := by
    intro H
    rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      have hn : nextPart κ j.castSucc = κ j.succ := by
        rw [nextPart, dite_eq_left (by simp)]
        rfl
      rw [hn]
      rfl
    · have hn : nextPart κ (Fin.last m) = 0 := by
        rw [nextPart, dite_eq_right (by simp)]
      rw [hn, Nat.sub_zero, leadingMinor, dite_eq_left (by simp)]
      simp only [Fin.val_last, Fin.castLE_rfl, Matrix.submatrix_id_id]
      rw [det_orthogonal_conj]
  simp_rw [hint]
  rw [integral_mul_const]
  ring

/-- DLMF 35.4.4: `Z_κ(0) = 1` for `κ = (0, …, 0)` and `Z_κ(0) = 0` otherwise. -/
@[dlmf 35.4.E4]
theorem zonalPolynomial_zero {m : ℕ} (κ : Fin m → ℕ) :
    zonalPolynomial κ 0 = if κ = 0 then 1 else 0 := by
  split_ifs with hκ
  · subst hκ
    unfold zonalPolynomial zonalPolynomialAtOne partitionalShiftedFactorial partitionLength
    simp
  · unfold zonalPolynomial
    have hne : (Finset.univ.filter fun j : Fin m => κ j ≠ 0).Nonempty := by
      by_contra h
      apply hκ
      funext j
      by_contra hj
      exact h ⟨j, by simpa using hj⟩
    set j₀ := (Finset.univ.filter fun j : Fin m => κ j ≠ 0).max' hne with hj₀
    have hj₀mem := Finset.max'_mem _ hne
    rw [← hj₀] at hj₀mem
    have hκj₀ : κ j₀ ≠ 0 := (Finset.mem_filter.mp hj₀mem).2
    have hnext : nextPart κ j₀ = 0 := by
      unfold nextPart
      split_ifs with h
      · by_contra hc
        have hle := Finset.le_max' (Finset.univ.filter fun j : Fin m => κ j ≠ 0)
          ⟨j₀.1 + 1, h⟩ (by simp [hc])
        rw [← hj₀] at hle
        exact absurd hle (by rw [not_le, Fin.lt_def]; simp)
      · rfl
    have hint : ∀ H : Matrix.orthogonalGroup (Fin m) ℝ,
        (∏ j : Fin m, leadingMinor ((H : Matrix (Fin m) (Fin m) ℝ) * 0 *
          (H : Matrix (Fin m) (Fin m) ℝ)ᵀ) (j.1 + 1) ^ (κ j - nextPart κ j)) = 0 := by
      intro H
      refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
      rw [hnext, Nat.sub_zero, mul_zero, zero_mul, leadingMinor,
        dite_eq_left (by omega : j₀.1 + 1 ≤ m),
        Matrix.det_eq_zero_of_row_eq_zero (0 : Fin (j₀.1 + 1)) (fun _ => rfl), zero_pow hκj₀]
    simp_rw [hint]
    simp

/-- DLMF 35.4.5: `Z_κ(H T H⁻¹) = Z_κ(T)` for `H ∈ O(m)`. -/
@[dlmf 35.4.E5]
theorem zonalPolynomial_conj {m : ℕ} (κ : Fin m → ℕ) (H₀ : Matrix.orthogonalGroup (Fin m) ℝ)
    (T : Matrix (Fin m) (Fin m) ℝ) :
    zonalPolynomial κ ((H₀ : Matrix (Fin m) (Fin m) ℝ) * T * (H₀ : Matrix (Fin m) (Fin m) ℝ)⁻¹)
      = zonalPolynomial κ T := by
  have hinv : (H₀ : Matrix (Fin m) (Fin m) ℝ)⁻¹ = (H₀ : Matrix (Fin m) (Fin m) ℝ)ᵀ :=
    Matrix.inv_eq_left_inv ((Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).mp H₀.2)
  rw [hinv]
  unfold zonalPolynomial
  congr 1
  have key := integral_mul_right_eq_self (μ := orthogonalHaar m)
    (fun H : Matrix.orthogonalGroup (Fin m) ℝ => ∏ j : Fin m,
      leadingMinor ((H : Matrix (Fin m) (Fin m) ℝ) * T * (H : Matrix (Fin m) (Fin m) ℝ)ᵀ)
        (j.1 + 1) ^ (κ j - nextPart κ j)) H₀
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun H => ?_)
  simp only [Submonoid.coe_mul, Matrix.transpose_mul, Matrix.mul_assoc]

/-! ## 35.4(ii): polynomiality -/

/-- Formula under the stated hypotheses: `∑ n ∈ Finset.range N, (n + 1) * (K n - K (n + 1)) + N *
K N = ∑ n ∈ Finset.range N, K n`. -/
private lemma sum_range_succ_mul_sub_add_eq (K : ℕ → ℕ) (hK : Antitone K) (N : ℕ) :
    ∑ n ∈ Finset.range N, (n + 1) * (K n - K (n + 1)) + N * K N =
      ∑ n ∈ Finset.range N, K n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    have h := hK (Nat.le_succ N)
    have h' : (N + 1) * (K N - K (N + 1)) + (N + 1) * K (N + 1) = (N + 1) * K N := by
      rw [← mul_add, Nat.sub_add_cancel h]
    rw [add_assoc, h']
    ring

/-- For a partition `κ`, `∑_{j=1}^{m} j (k_j - k_{j+1}) = |κ|` (with `k_{m+1} = 0`). -/
private lemma sum_succ_mul_sub_nextPart {m : ℕ} (κ : Fin m → ℕ) (hκ : Antitone κ) :
    ∑ j : Fin m, (j.1 + 1) * (κ j - nextPart κ j) = ∑ j, κ j := by
  set K : ℕ → ℕ := fun n => if h : n < m then κ ⟨n, h⟩ else 0 with hKdef
  have hK : Antitone K := by
    intro a b hab
    simp only [hKdef]
    split_ifs with h1 h2 h2
    all_goals first
      | exact hκ (Fin.mk_le_mk.mpr hab) | exact Nat.zero_le _ | omega
  have h1 : ∀ j : Fin m, κ j = K j := fun j => by simp [hKdef, j.2]
  have h2 : ∀ j : Fin m, nextPart κ j = K (j + 1) := fun j => rfl
  have hKm : K m = 0 := by simp [hKdef]
  have key := sum_range_succ_mul_sub_add_eq K hK m
  rw [hKm, mul_zero, add_zero] at key
  simp_rw [h2, h1]
  rw [Fin.sum_univ_eq_sum_range (fun n => (n + 1) * (K n - K (n + 1))),
    Fin.sum_univ_eq_sum_range K, key]

section ZonalPolynomials
open MvPolynomial

/-- A family of polynomials whose coefficients depend continuously on the parameter. -/
def HasContinuousCoeffs {G σ : Type*} [TopologicalSpace G] (F : G → MvPolynomial σ ℝ) : Prop :=
  ∀ α, Continuous fun g => (F g).coeff α

section CoeffCont
variable {G σ : Type*} [TopologicalSpace G]

/-- Identity under the stated parameter and domain assumptions:
`HasContinuousCoeffs (fun _ : G => p)`. -/
theorem HasContinuousCoeffs.const (p : MvPolynomial σ ℝ) : HasContinuousCoeffs (fun _ : G => p) :=
  fun _ => continuous_const

/-- Identity under the stated parameter and domain assumptions: `HasContinuousCoeffs (fun g =>
(MvPolynomial.C (f g) : MvPolynomial σ ℝ))`. -/
theorem HasContinuousCoeffs.C {f : G → ℝ} (hf : Continuous f) :
    HasContinuousCoeffs (fun g => (MvPolynomial.C (f g) : MvPolynomial σ ℝ)) := by
  intro α
  classical
  simp only [MvPolynomial.coeff_C]
  split_ifs
  · exact hf
  · exact continuous_const

/-- Identity under the stated parameter and domain assumptions:
`HasContinuousCoeffs (fun g => F₁ g + F₂ g)`. -/
theorem HasContinuousCoeffs.add {F₁ F₂ : G → MvPolynomial σ ℝ} (h₁ : HasContinuousCoeffs F₁)
    (h₂ : HasContinuousCoeffs F₂) : HasContinuousCoeffs (fun g => F₁ g + F₂ g) := fun α => by
  have : ∀ g, (F₁ g + F₂ g).coeff α = (F₁ g).coeff α + (F₂ g).coeff α :=
    fun g => (MvPolynomial.lcoeff ℝ α).map_add _ _
  simp only [this]; exact (h₁ α).add (h₂ α)

/-- Identity under the stated parameter and domain assumptions:
`HasContinuousCoeffs (fun g => F₁ g * F₂ g)`. -/
theorem HasContinuousCoeffs.mul {F₁ F₂ : G → MvPolynomial σ ℝ} (h₁ : HasContinuousCoeffs F₁)
    (h₂ : HasContinuousCoeffs F₂) : HasContinuousCoeffs (fun g => F₁ g * F₂ g) := fun α => by
  classical
  simp only [MvPolynomial.coeff_mul]
  exact continuous_finsetSum _ fun x _ => (h₁ x.1).mul (h₂ x.2)

/-- Formula under the stated hypotheses: `HasContinuousCoeffs (fun g => ∑ i ∈ s, F i g)`. -/
theorem HasContinuousCoeffs.sum {ι : Type*} (s : Finset ι) {F : ι → G → MvPolynomial σ ℝ}
    (h : ∀ i ∈ s, HasContinuousCoeffs (F i)) : HasContinuousCoeffs
        (fun g => ∑ i ∈ s, F i g) := fun α => by
  simp only [MvPolynomial.coeff_sum]
  exact continuous_finsetSum _ fun i hi => h i hi α

/-- Formula under the stated hypotheses: `HasContinuousCoeffs (fun g => ∏ i ∈ s, F i g)`. -/
theorem HasContinuousCoeffs.prod {ι : Type*} (s : Finset ι) {F : ι → G → MvPolynomial σ ℝ}
    (h : ∀ i ∈ s, HasContinuousCoeffs (F i)) : HasContinuousCoeffs (fun g => ∏ i ∈ s, F i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasContinuousCoeffs.const (G := G) (1 : MvPolynomial σ ℝ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Identity under the stated parameter and domain assumptions: `HasContinuousCoeffs (fun g => F g ^
n)`. -/
theorem HasContinuousCoeffs.pow {F : G → MvPolynomial σ ℝ} (h : HasContinuousCoeffs F) (n : ℕ) :
    HasContinuousCoeffs (fun g => F g ^ n) := by
  have := HasContinuousCoeffs.prod (Finset.range n) (F := fun _ => F) (fun _ _ => h)
  simpa using this

/-- Identity under the stated parameter and domain assumptions: `HasContinuousCoeffs (fun g => (M
g).det)`. -/
theorem HasContinuousCoeffs.det {n : Type*} [Fintype n] [DecidableEq n]
    {M : G → Matrix n n (MvPolynomial σ ℝ)} (h : ∀ a b, HasContinuousCoeffs fun g => M g a b) :
    HasContinuousCoeffs (fun g => (M g).det) := by
  simp only [Matrix.det_apply']
  exact HasContinuousCoeffs.sum _ fun σ' _ => (HasContinuousCoeffs.const _).mul
    (HasContinuousCoeffs.prod _ fun i _ => h _ _)

/-- Identity under the stated parameter and domain assumptions:
`HasContinuousCoeffs fun g => (A g * B g) a b`. -/
theorem HasContinuousCoeffs.matMul {n : Type*} [Fintype n]
    {A B : G → Matrix n n (MvPolynomial σ ℝ)} (hA : ∀ a b, HasContinuousCoeffs fun g => A g a b)
    (hB : ∀ a b, HasContinuousCoeffs fun g => B g a b) (a b : n) :
    HasContinuousCoeffs fun g => (A g * B g) a b := by
  simp only [Matrix.mul_apply]
  exact HasContinuousCoeffs.sum _ fun k _ => (hA a k).mul (hB k b)

end CoeffCont

/-- Homogeneity of the determinant of a matrix with entries homogeneous of degree `1`. -/
private lemma isHomogeneous_det_of_isHomogeneous_one {σ n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n (MvPolynomial σ ℝ)} (h : ∀ a b, (M a b).IsHomogeneous 1) :
    M.det.IsHomogeneous (Fintype.card n) := by
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ' _ => ?_
  rw [show ((Equiv.Perm.sign σ' : ℤ) : MvPolynomial σ ℝ) =
      MvPolynomial.C ((Equiv.Perm.sign σ' : ℤ) : ℝ) from
        (map_intCast (MvPolynomial.C : ℝ →+* MvPolynomial σ ℝ) _).symm,
    ← zero_add (Fintype.card n)]
  refine (isHomogeneous_C _ _).mul ?_
  have := IsHomogeneous.prod Finset.univ (fun i => M (σ' i) i) (fun _ => 1)
    (fun i _ => h _ _)
  simpa using this

/-- The stated relation follows from the given hypotheses: `((A * B) a b).IsHomogeneous (p + q)`. -/
private lemma isHomogeneous_mul_apply {σ n : Type*} [Fintype n]
    {A B : Matrix n n (MvPolynomial σ ℝ)} {p q : ℕ} (hA : ∀ a b, (A a b).IsHomogeneous p)
    (hB : ∀ a b, (B a b).IsHomogeneous q) (a b : n) : ((A * B) a b).IsHomogeneous (p + q) := by
  simp only [Matrix.mul_apply]
  exact IsHomogeneous.sum _ _ _ fun k _ => (hA a k).mul (hB k b)

/-- The polynomial matrix `H diag(X₁, …, X_m) Hᵀ`. -/
def diagonalConjPoly {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin m) ℝ) :=
  H.map MvPolynomial.C * diagonal (fun i => X i) * (H.map MvPolynomial.C)ᵀ

/-- The integrand of 35.4.3 at `T = diag(X₁, …, X_m)`, as a polynomial. -/
def zonalIntegrandPoly {m : ℕ} (κ : Fin m → ℕ) (H : Matrix (Fin m) (Fin m) ℝ) :
    MvPolynomial (Fin m) ℝ :=
  ∏ j : Fin m, leadingMinor (diagonalConjPoly H) (j.1 + 1) ^ (κ j - nextPart κ j)

/-- Identity under the stated parameter and domain assumptions: `f (leadingMinor M j) =
leadingMinor (M.map f) j`. -/
private lemma map_leadingMinor {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) (j : ℕ) : f (leadingMinor M j) = leadingMinor (M.map f) j := by
  unfold leadingMinor
  split_ifs
  · rw [RingHom.map_det]; rfl
  · exact map_zero f

/-- Identity under the stated parameter and domain assumptions:
`eval t (zonalIntegrandPoly κ H) = ∏ j : Fin m, leadingMinor (H * diagonal t * Hᵀ) (j.1 + 1) ^ (κ j
- nextPart κ j)`. -/
private lemma eval_zonalIntegrandPoly {m : ℕ} (κ : Fin m → ℕ) (H : Matrix (Fin m) (Fin m) ℝ)
    (t : Fin m → ℝ) : eval t (zonalIntegrandPoly κ H) =
      ∏ j : Fin m, leadingMinor (H * diagonal t * Hᵀ) (j.1 + 1) ^ (κ j - nextPart κ j) := by
  unfold zonalIntegrandPoly
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_pow, map_leadingMinor]
  congr 2
  have hH : (H.map MvPolynomial.C).map (eval t) = H := by
    ext a b; simp
  rw [diagonalConjPoly, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hH,
    Matrix.diagonal_map (map_zero _)]
  simp

/-- Identity under the stated parameter and domain assumptions: `HasContinuousCoeffs (fun H :
Matrix.orthogonalGroup (Fin m) ℝ => zonalIntegrandPoly κ (H : Matrix (Fin m) (Fin m) ℝ))`. -/
private lemma coeffCont_zonalIntegrandPoly {m : ℕ} (κ : Fin m → ℕ) :
    HasContinuousCoeffs (fun H : Matrix.orthogonalGroup (Fin m) ℝ =>
      zonalIntegrandPoly κ (H : Matrix (Fin m) (Fin m) ℝ)) := by
  have hent : ∀ a b, HasContinuousCoeffs fun H : Matrix.orthogonalGroup (Fin m) ℝ =>
      diagonalConjPoly (H : Matrix (Fin m) (Fin m) ℝ) a b := by
    intro a b
    have hHc : ∀ a b, HasContinuousCoeffs fun H : Matrix.orthogonalGroup (Fin m) ℝ =>
        ((H : Matrix (Fin m) (Fin m) ℝ).map
          (MvPolynomial.C : ℝ →+* MvPolynomial (Fin m) ℝ)) a b := fun a b =>
      HasContinuousCoeffs.C
          ((continuous_apply b).comp ((continuous_apply a).comp continuous_subtype_val))
    have hHt : ∀ a b, HasContinuousCoeffs fun H : Matrix.orthogonalGroup (Fin m) ℝ =>
        ((H : Matrix (Fin m) (Fin m) ℝ).map
          (MvPolynomial.C : ℝ →+* MvPolynomial (Fin m) ℝ))ᵀ a b := fun a b => hHc b a
    unfold diagonalConjPoly
    refine HasContinuousCoeffs.matMul (fun a b => ?_) hHt a b
    exact HasContinuousCoeffs.matMul (A := fun H : Matrix.orthogonalGroup (Fin m) ℝ =>
      (H : Matrix (Fin m) (Fin m) ℝ).map (MvPolynomial.C : ℝ →+* MvPolynomial (Fin m) ℝ))
      (B := fun _ => diagonal (fun i => (X i : MvPolynomial (Fin m) ℝ))) hHc
      (fun a b => HasContinuousCoeffs.const
          (diagonal (fun i => (X i : MvPolynomial (Fin m) ℝ)) a b))
      a b
  unfold zonalIntegrandPoly
  refine HasContinuousCoeffs.prod _ fun j _ => HasContinuousCoeffs.pow ?_ _
  have hj : j.1 + 1 ≤ m := j.2
  unfold leadingMinor
  simp only [hj, dite_true]
  exact HasContinuousCoeffs.det fun a b => hent _ _

/-- The stated relation follows from the given hypotheses:
`(zonalIntegrandPoly κ H).IsHomogeneous (∑ j, κ j)`. -/
private lemma isHomogeneous_zonalIntegrandPoly {m : ℕ} (κ : Fin m → ℕ) (hκ : Antitone κ)
    (H : Matrix (Fin m) (Fin m) ℝ) : (zonalIntegrandPoly κ H).IsHomogeneous (∑ j, κ j) := by
  have hC : ∀ a b, ((H.map (MvPolynomial.C : ℝ →+* MvPolynomial (Fin m) ℝ)) a b).IsHomogeneous 0 :=
    fun a b => isHomogeneous_C _ _
  have hD : ∀ a b, ((diagonal (fun i => (X i : MvPolynomial (Fin m) ℝ))) a b).IsHomogeneous 1 := by
    intro a b
    by_cases hab : a = b
    · subst hab; simpa using isHomogeneous_X ℝ a
    · simpa [hab] using isHomogeneous_zero (Fin m) ℝ 1
  have hent : ∀ a b, (diagonalConjPoly H a b).IsHomogeneous 1 := by
    intro a b
    have h1 := isHomogeneous_mul_apply hC hD
    have h2 := isHomogeneous_mul_apply
      (B := (H.map (MvPolynomial.C : ℝ →+* MvPolynomial (Fin m) ℝ))ᵀ) h1 (fun a b => hC b a) a b
    rw [diagonalConjPoly]
    simpa using h2
  unfold zonalIntegrandPoly
  rw [← sum_succ_mul_sub_nextPart κ hκ]
  refine IsHomogeneous.prod _ _ _ fun j _ => ?_
  refine IsHomogeneous.pow ?_ _
  have hj : j.1 + 1 ≤ m := j.2
  unfold leadingMinor
  simp only [hj, dite_true]
  have := isHomogeneous_det_of_isHomogeneous_one
      (M := (diagonalConjPoly H).submatrix (Fin.castLE hj) (Fin.castLE hj))
    fun a b => hent _ _
  simpa using this

/-- DLMF 35.4(ii) at diagonal matrices. -/
private lemma exists_zonalPolynomial_diagonal_eq_eval {m : ℕ} (κ : Fin m → ℕ) (hκ : Antitone κ) :
    ∃ P : MvPolynomial (Fin m) ℝ, P.IsHomogeneous (∑ j, κ j) ∧
      ∀ t : Fin m → ℝ, zonalPolynomial κ (diagonal t) = eval t P := by
  classical
  set d := ∑ j, κ j
  set D : Finset (Fin m →₀ ℕ) := Finset.finsuppAntidiag Finset.univ d
  set c : (Fin m →₀ ℕ) → ℝ := fun α => ∫ H, (zonalIntegrandPoly κ
    (H : Matrix (Fin m) (Fin m) ℝ)).coeff α ∂orthogonalHaar m
  have hcont := coeffCont_zonalIntegrandPoly κ
  have hint : ∀ α, Integrable (fun H : Matrix.orthogonalGroup (Fin m) ℝ =>
      (zonalIntegrandPoly κ (H : Matrix (Fin m) (Fin m) ℝ)).coeff α) (orthogonalHaar m) :=
    fun α => (hcont α).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmemD : ∀ α : Fin m →₀ ℕ, α.degree = d ↔ α ∈ D := by
    intro α
    simp only [D, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
    rw [Finsupp.degree_eq_sum]
  refine ⟨MvPolynomial.C (zonalPolynomialAtOne κ) * ∑ α ∈ D, monomial α (c α), ?_, ?_⟩
  · rw [← zero_add d]
    refine (isHomogeneous_C _ _).mul (IsHomogeneous.sum _ _ _ fun α hα => ?_)
    exact isHomogeneous_monomial _ ((hmemD α).mpr hα)
  · intro t
    rw [map_mul, eval_C, zonalPolynomial]
    congr 1
    rw [map_sum]
    simp_rw [eval_monomial]
    have hsupp : ∀ H : Matrix.orthogonalGroup (Fin m) ℝ, eval t (zonalIntegrandPoly κ
        (H : Matrix (Fin m) (Fin m) ℝ)) = ∑ α ∈ D, (zonalIntegrandPoly κ
          (H : Matrix (Fin m) (Fin m) ℝ)).coeff α * α.prod fun i k => t i ^ k := by
      intro H
      rw [eval_eq]
      refine Finset.sum_subset (fun α hα => (hmemD α).mp ?_) fun α _ hα => ?_
      · rw [Finsupp.degree_eq_weight_one]
        exact isHomogeneous_zonalIntegrandPoly κ hκ _ (mem_support_iff.mp hα)
      · rw [notMem_support_iff.mp hα, zero_mul]
    have hlhs : (fun H : Matrix.orthogonalGroup (Fin m) ℝ => ∏ j : Fin m,
        leadingMinor ((H : Matrix (Fin m) (Fin m) ℝ) * diagonal t *
          (H : Matrix (Fin m) (Fin m) ℝ)ᵀ) (j.1 + 1) ^ (κ j - nextPart κ j)) =
        fun H : Matrix.orthogonalGroup (Fin m) ℝ =>
          eval t (zonalIntegrandPoly κ (H : Matrix (Fin m) (Fin m) ℝ)) :=
      funext fun H => (eval_zonalIntegrandPoly κ _ t).symm
    rw [hlhs]
    simp_rw [hsupp]
    rw [integral_finsetSum _ fun α _ => (hint α).mul_const _]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_mul_const]

/-- `Z_κ(diag(t ∘ σ)) = Z_κ(diag t)` for a permutation `σ`. -/
private lemma zonalPolynomial_diagonal_comp_perm {m : ℕ} (κ : Fin m → ℕ) (σ : Equiv.Perm (Fin m))
    (t : Fin m → ℝ) : zonalPolynomial κ (diagonal (t ∘ σ)) = zonalPolynomial κ (diagonal t) := by
  set P : Matrix (Fin m) (Fin m) ℝ := σ.toPEquiv.toMatrix with hP
  have hPt : Pᵀ = σ.symm.toPEquiv.toMatrix := by
    rw [hP, ← PEquiv.toMatrix_symm, Equiv.toPEquiv_symm]
  have hconj : ∀ M : Matrix (Fin m) (Fin m) ℝ, P * M * Pᵀ = M.submatrix σ σ := by
    intro M
    rw [hPt, hP, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    rfl
  have hPP : P * Pᵀ = 1 := by
    have := hconj 1
    rwa [Matrix.mul_one, Matrix.submatrix_one_equiv] at this
  have hmem : P ∈ Matrix.orthogonalGroup (Fin m) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff]
    exact hPP
  have hinv : P⁻¹ = Pᵀ := Matrix.inv_eq_right_inv hPP
  have h := zonalPolynomial_conj κ ⟨P, hmem⟩ (diagonal t)
  simp only at h
  rw [hinv, hconj, Matrix.submatrix_diagonal_equiv] at h
  exact h

/-- Reduction of a symmetric matrix to the diagonal matrix of its eigenvalues. -/
private lemma zonalPolynomial_eq_diagonal_eigenvalues {m : ℕ} (κ : Fin m → ℕ)
    {T : Matrix (Fin m) (Fin m) ℝ}
    (hT : T.IsHermitian) : zonalPolynomial κ T = zonalPolynomial κ (diagonal hT.eigenvalues) := by
  set U := hT.eigenvectorUnitary
  have h := hT.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  have hu : (U : Matrix (Fin m) (Fin m) ℝ) * star (U : Matrix (Fin m) (Fin m) ℝ) = 1 :=
    Unitary.mul_star_self_of_mem U.2
  have hinv : (U : Matrix (Fin m) (Fin m) ℝ)⁻¹ = star (U : Matrix (Fin m) (Fin m) ℝ) :=
    Matrix.inv_eq_right_inv hu
  have hd : (RCLike.ofReal ∘ hT.eigenvalues : Fin m → ℝ) = hT.eigenvalues := by
    funext i; simp
  have h2 := zonalPolynomial_conj κ (U : Matrix.orthogonalGroup (Fin m) ℝ)
    (diagonal hT.eigenvalues)
  rw [hinv, ← hd] at h2
  conv_lhs => rw [h]
  exact h2

end ZonalPolynomials
/-- DLMF 35.4(ii) (after 35.4.5): `Z_κ(T)` is a symmetric polynomial in the eigenvalues
`t₁, …, t_m` of `T ∈ 𝓢`, homogeneous of degree `|κ|`. -/
@[dlmf 35.4.ii]
theorem zonalPolynomial_exists_symmetric {m : ℕ} (κ : Fin m → ℕ) (hκ : Antitone κ) :
    ∃ P : MvPolynomial (Fin m) ℝ, P.IsSymmetric ∧ P.IsHomogeneous (∑ j, κ j) ∧
      ∀ (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.IsHermitian),
        zonalPolynomial κ T = MvPolynomial.eval hT.eigenvalues P := by
  obtain ⟨P, hhom, heval⟩ := exists_zonalPolynomial_diagonal_eq_eval κ hκ
  refine ⟨P, fun σ => ?_, hhom, fun T hT => ?_⟩
  · refine MvPolynomial.funext fun x => ?_
    rw [MvPolynomial.eval_rename, ← heval, ← heval, zonalPolynomial_diagonal_comp_perm]
  · rw [zonalPolynomial_eq_diagonal_eigenvalues κ hT, heval]

/-- DLMF 35.4.6: `∑_{|κ|=k} Z_κ(T) = (tr T)^k` for `T ∈ 𝓢`. -/
@[dlmf 35.4.E6]
theorem sum_zonalPolynomial {m : ℕ} (k : ℕ) (T : Matrix (Fin m) (Fin m) ℝ)
    (hT : T.IsHermitian) :
    ∑ κ ∈ partitions m k, zonalPolynomial κ T = T.trace ^ k := by
  sorry

/-- DLMF 35.4.7 (mean value): `∫_{O(m)} Z_κ(S H T H⁻¹) dH = Z_κ(S) Z_κ(T) / Z_κ(I)`, for a
partition `κ`, `S ∈ Ω` and `T ∈ 𝓢`; `Z_κ(S H T H⁻¹)` is the function of the eigenvalues of
`S H T Hᵀ`, written as `Z_κ(S^{1/2} H T Hᵀ S^{1/2})`. -/
@[dlmf 35.4.E7]
theorem integral_zonalPolynomial_conj {m : ℕ} (κ : Fin m → ℕ) (hκ : Antitone κ)
    {S T : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef) (hT : T.IsHermitian) :
    ∫ H, zonalPolynomial κ (CFC.sqrt S * ((H : Matrix (Fin m) (Fin m) ℝ) * T *
        (H : Matrix (Fin m) (Fin m) ℝ)ᵀ) * CFC.sqrt S) ∂orthogonalHaar m =
      zonalPolynomial κ S * zonalPolynomial κ T / zonalPolynomial κ 1 := by
  sorry

/-! ## 35.4.8: the Laplace integral

The leading-minor product `φ_κ(Y) = ∏_j |(Y)_j|^{k_j - k_{j+1}}` satisfies
`φ_κ(L Z Lᵀ) = φ_κ(L Lᵀ) φ_κ(Z)` for lower-triangular `L`, so the Cholesky substitution gives
`∫_Ω etr(-SY) |Y|^{a-(m+1)/2} φ_κ(Y) dY = Γ_m(a + κ) |S|^{-a} φ_κ(S⁻¹)`; averaging over `O(m)`
(Fubini) gives 35.4.8. -/

section LaplaceTransform
open scoped ENNReal

/-- Identity under the stated parameter and domain assumptions: `(H : Matrix (Fin m) (Fin m) ℝ) *
(H : Matrix (Fin m) (Fin m) ℝ)ᵀ = 1`. -/
private lemma orthogonalGroup_mul_transpose {m : ℕ} (H : Matrix.orthogonalGroup (Fin m) ℝ) :
    (H : Matrix (Fin m) (Fin m) ℝ) * (H : Matrix (Fin m) (Fin m) ℝ)ᵀ = 1 := by
  have := (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).mp H.2
  exact this

/-- Identity under the stated parameter and domain assumptions: `(H : Matrix (Fin m) (Fin m) ℝ)ᵀ *
(H : Matrix (Fin m) (Fin m) ℝ) = 1`. -/
private lemma orthogonalGroup_transpose_mul {m : ℕ} (H : Matrix.orthogonalGroup (Fin m) ℝ) :
    (H : Matrix (Fin m) (Fin m) ℝ)ᵀ * (H : Matrix (Fin m) (Fin m) ℝ) = 1 := by
  have := (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).mp H.2
  exact this

/-- The stated relation follows from the given hypotheses: `((H : Matrix (Fin m) (Fin m) ℝ) * X *
(H : Matrix (Fin m) (Fin m) ℝ)ᵀ).PosDef`. -/
private lemma posDef_orthogonalGroup_conj {m : ℕ} (H : Matrix.orthogonalGroup (Fin m) ℝ)
    {X : Matrix (Fin m) (Fin m) ℝ} (hX : X.PosDef) :
    ((H : Matrix (Fin m) (Fin m) ℝ) * X * (H : Matrix (Fin m) (Fin m) ℝ)ᵀ).PosDef := by
  have hinj : Function.Injective (H : Matrix (Fin m) (Fin m) ℝ)ᵀ.mulVec := by
    refine Function.LeftInverse.injective (g := (H : Matrix (Fin m) (Fin m) ℝ).mulVec) ?_
    intro x
    rw [Matrix.mulVec_mulVec, orthogonalGroup_mul_transpose, Matrix.one_mulVec]
  have := hX.conjTranspose_mul_mul_same hinj
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at this

/-- Measurability of the indicated function: `Measurable fun X : SymMatrix m => (etr (-(T * (X :
Matrix (Fin m) (Fin m) ℝ))) : ℂ) * (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ p)`. -/
private lemma measurable_etr_neg_mul_det_cpow {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) (p : ℂ) :
    Measurable fun X : SymMatrix m => (etr (-(T * (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
      (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ p) := by
  unfold etr
  refine (Complex.measurable_ofReal.comp ?_).mul
    ((Complex.measurable_ofReal.comp continuous_subtype_val.matrix_det.measurable).pow_const _)
  exact Real.measurable_exp.comp
    (continuous_const.matrix_mul continuous_subtype_val).neg.matrix_trace.measurable

/-- The inner integral of 35.4.8 at a fixed `H ∈ O(m)`. -/
private lemma hasIntegralOn_laplace_leadingMinorPowProd_orthogonal_conj {m : ℕ} (κ : Fin m → ℕ)
    (hκ : Antitone κ)
    {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef) {a : ℂ} (ha : ((m : ℝ) - 1) / 2 < a.re)
    (H : Matrix.orthogonalGroup (Fin m) ℝ) :
    HasIntegralOn (posDefCone m) (fun X => (etr (-(T * X)) : ℂ) *
      ((X.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
        (leadingMinorPowProd κ
            ((H : Matrix (Fin m) (Fin m) ℝ) * X * (H : Matrix (Fin m) (Fin m) ℝ)ᵀ) : ℂ))
      (multivariateGammaVec m (fun j => a + κ j) * (T.det : ℂ) ^ (-a) *
        (leadingMinorPowProd κ ((H : Matrix (Fin m) (Fin m) ℝ) * T⁻¹ *
          (H : Matrix (Fin m) (Fin m) ℝ)ᵀ) : ℂ)) := by
  set K : Matrix (Fin m) (Fin m) ℝ := (H : Matrix (Fin m) (Fin m) ℝ) with hK
  have hKK : K * Kᵀ = 1 := orthogonalGroup_mul_transpose H
  have hKtK : Kᵀ * K = 1 := orthogonalGroup_transpose_mul H
  have hS : (K * T * Kᵀ).PosDef := posDef_orthogonalGroup_conj H hT
  have hL := hasIntegralOn_laplace_leadingMinorPowProd κ hκ hS ha
  have hdetK : K.det * K.det = 1 := by
    have := congrArg Matrix.det hKtK
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hdetKt : Kᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; intro h; rw [h, zero_mul] at hdetK; exact zero_ne_one hdetK
  set C := Matrix.GeneralLinearGroup.mkOfDetNeZero Kᵀ hdetKt
  have hC : (C : Matrix (Fin m) (Fin m) ℝ) = Kᵀ := rfl
  have hF : Measurable fun X : SymMatrix m => (etr (-(T * (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
      (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
      (leadingMinorPowProd κ (K * (X : Matrix (Fin m) (Fin m) ℝ) * Kᵀ) : ℂ) :=
    (measurable_etr_neg_mul_det_cpow T _).mul
        (Complex.measurable_ofReal.comp ((continuous_leadingMinorPowProd κ).comp
      ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul
        continuous_const)).measurable)
  have h2 : HasIntegralOn (posDefCone m) (fun Y => (etr (-(T * ((C : Matrix (Fin m) (Fin m) ℝ) *
      Y * (C : Matrix (Fin m) (Fin m) ℝ)ᵀ))) : ℂ) * ((((C : Matrix (Fin m) (Fin m) ℝ) * Y *
        (C : Matrix (Fin m) (Fin m) ℝ)ᵀ).det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
      (leadingMinorPowProd κ
          (K * ((C : Matrix (Fin m) (Fin m) ℝ) * Y * (C : Matrix (Fin m) (Fin m) ℝ)ᵀ) *
        Kᵀ) : ℂ))
      (multivariateGammaVec m (fun j => a + κ j) * ((K * T * Kᵀ).det : ℂ) ^ (-a) *
        (leadingMinorPowProd κ (K * T * Kᵀ)⁻¹ : ℂ)) := by
    refine hasIntegralOn_posDefCone_congr hL fun Y _ => ?_
    rw [hC, Matrix.transpose_transpose]
    have h1 : K * (Kᵀ * (Y : Matrix (Fin m) (Fin m) ℝ) * K) * Kᵀ =
        (Y : Matrix (Fin m) (Fin m) ℝ) := by
      simp only [← Matrix.mul_assoc, hKK, Matrix.one_mul]
      rw [Matrix.mul_assoc, hKK, Matrix.mul_one]
    have htr : (T * (Kᵀ * (Y : Matrix (Fin m) (Fin m) ℝ) * K)).trace =
        (K * T * Kᵀ * (Y : Matrix (Fin m) (Fin m) ℝ)).trace := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc]
    have hdY : (Kᵀ * (Y : Matrix (Fin m) (Fin m) ℝ) * K).det =
        (Y : Matrix (Fin m) (Fin m) ℝ).det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      linear_combination (Y : Matrix (Fin m) (Fin m) ℝ).det * hdetK
    rw [h1, hdY]
    unfold etr
    rw [Matrix.trace_neg, Matrix.trace_neg, htr]
  have h3 := hasIntegralOn_posDefCone_of_congruence (F := fun X => (etr (-(T * X)) : ℂ) *
      ((X.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) * (leadingMinorPowProd κ (K * X * Kᵀ) : ℂ)) C hF h2
  convert h3 using 1
  have habs : |(C : Matrix (Fin m) (Fin m) ℝ).det| ^ (m + 1) = 1 := by
    rw [hC, Matrix.det_transpose]
    have : |K.det| = 1 := by
      have h := abs_mul K.det K.det
      rw [hdetK, abs_one] at h
      nlinarith [abs_nonneg K.det, h]
    rw [this, one_pow]
  have hdetS : (K * T * Kᵀ).det = T.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    linear_combination T.det * hdetK
  have hinvK : K⁻¹ = Kᵀ := Matrix.inv_eq_left_inv hKtK
  have hinvKt : Kᵀ⁻¹ = K := Matrix.inv_eq_left_inv hKK
  have hSinv : (K * T * Kᵀ)⁻¹ = K * T⁻¹ * Kᵀ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hinvK, hinvKt, Matrix.mul_assoc]
  rw [habs, hdetS, hSinv]
  push_cast
  ring

end LaplaceTransform
/-- DLMF 35.4.8 (Laplace integral): for `T ∈ Ω` and `ℜa > (m-1)/2`,
`∫_Ω etr(-TX) |X|^{a-(m+1)/2} Z_κ(X) dX = Γ_m(a + κ) |T|^{-a} Z_κ(T⁻¹)`, with
`Γ_m(a + κ) = Γ_m(a + k₁, …, a + k_m)` (35.3.5). -/
@[dlmf 35.4.E8]
theorem hasIntegralOn_zonalPolynomial_laplace {m : ℕ} (κ : Fin m → ℕ) (hκ : Antitone κ)
    {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef) {a : ℂ} (ha : ((m : ℝ) - 1) / 2 < a.re) :
    HasIntegralOn (posDefCone m)
      (fun X => (etr (-(T * X)) : ℂ) * ((X.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
        (zonalPolynomial κ X : ℂ))
      (multivariateGammaVec m (fun j => a + κ j) * (T.det : ℂ) ^ (-a) *
        (zonalPolynomial κ T⁻¹ : ℂ)) := by
  set μ := orthogonalHaar m
  set ν := (TauCeti.symmetricLebesgue m).restrict (posDefCone m)
  have hmc : MeasurableSet (posDefCone m) := TauCeti.measurableSet_posDefMatrix m
  set p : ℂ := a - ((m : ℂ) + 1) / 2
  set F : Matrix.orthogonalGroup (Fin m) ℝ → SymMatrix m → ℂ := fun H X =>
    (etr (-(T * (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
      (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ p) *
      (leadingMinorPowProd κ ((H : Matrix (Fin m) (Fin m) ℝ) * (X : Matrix (Fin m) (Fin m) ℝ) *
        (H : Matrix (Fin m) (Fin m) ℝ)ᵀ) : ℂ) with hFdef
  have hconj : Continuous fun q : Matrix.orthogonalGroup (Fin m) ℝ × SymMatrix m =>
      (q.1 : Matrix (Fin m) (Fin m) ℝ) * (q.2 : Matrix (Fin m) (Fin m) ℝ) *
        (q.1 : Matrix (Fin m) (Fin m) ℝ)ᵀ :=
    ((continuous_subtype_val.comp continuous_fst).matrix_mul
      (continuous_subtype_val.comp continuous_snd)).matrix_mul
      (continuous_subtype_val.comp continuous_fst).matrix_transpose
  have hFm : Measurable (Function.uncurry F) :=
    ((measurable_etr_neg_mul_det_cpow T p).comp measurable_snd).mul
      (Complex.measurable_ofReal.comp ((continuous_leadingMinorPowProd κ).comp hconj).measurable)
  -- the real version
  set a' : ℂ := (a.re : ℂ)
  have ha' : ((m : ℝ) - 1) / 2 < a'.re := by simpa [a'] using ha
  have hnorm : ∀ H : Matrix.orthogonalGroup (Fin m) ℝ, ∀ X ∈ posDefCone m,
      ((‖F H X‖ : ℝ) : ℂ) = (etr (-(T * (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
        (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a' - ((m : ℂ) + 1) / 2)) *
        (leadingMinorPowProd κ ((H : Matrix (Fin m) (Fin m) ℝ) * (X : Matrix (Fin m) (Fin m) ℝ) *
          (H : Matrix (Fin m) (Fin m) ℝ)ᵀ) : ℂ) := by
    intro H X hX
    have hX : (X : Matrix (Fin m) (Fin m) ℝ).PosDef := hX
    have hd := hX.det_pos
    have hφ := (leadingMinorPowProd_pos κ (posDef_orthogonalGroup_conj H hX)).le
    have he : 0 ≤ etr (-(T * (X : Matrix (Fin m) (Fin m) ℝ))) := (Real.exp_pos _).le
    simp only [hFdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hφ,
      abs_of_nonneg he, Complex.norm_cpow_eq_rpow_re_of_pos hd]
    have : a' - ((m : ℂ) + 1) / 2 = (((a.re - ((m : ℝ) + 1) / 2 : ℝ)) : ℂ) := by
      push_cast; rfl
    rw [this, ← Complex.ofReal_cpow hd.le]
    have hre : p.re = a.re - ((m : ℝ) + 1) / 2 := by
      simp [p]
    rw [hre]
    push_cast
    ring
  have hint_norm : ∀ H : Matrix.orthogonalGroup (Fin m) ℝ, ∫ X, ‖F H X‖ ∂ν =
      (multivariateGammaVec m (fun j => a' + κ j) * (T.det : ℂ) ^ (-a') *
        (leadingMinorPowProd κ ((H : Matrix (Fin m) (Fin m) ℝ) * T⁻¹ *
          (H : Matrix (Fin m) (Fin m) ℝ)ᵀ) : ℂ)).re := by
    intro H
    have h := (hasIntegralOn_laplace_leadingMinorPowProd_orthogonal_conj κ hκ hT ha' H).2
    rw [← setIntegral_congr_fun hmc (hnorm H), integral_complex_ofReal] at h
    rw [← h, Complex.ofReal_re]
  have hfi : Integrable (Function.uncurry F) (μ.prod ν) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun H =>
      (hasIntegralOn_laplace_leadingMinorPowProd_orthogonal_conj κ hκ hT ha H).1, ?_⟩
    simp only [Function.uncurry_apply_pair]
    simp_rw [hint_norm]
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    refine Complex.continuous_re.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_leadingMinorPowProd κ).comp ?_)))
    exact (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
      continuous_subtype_val.matrix_transpose
  set A := zonalPolynomialAtOne κ
  have hZ : ∀ Y : Matrix (Fin m) (Fin m) ℝ, zonalPolynomial κ Y = A * ∫ H, leadingMinorPowProd κ
      ((H : Matrix (Fin m) (Fin m) ℝ) * Y * (H : Matrix (Fin m) (Fin m) ℝ)ᵀ) ∂μ := fun Y => rfl
  have htgt : ∀ X : SymMatrix m, (etr (-(T * (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
      (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ p) *
      (zonalPolynomial κ (X : Matrix (Fin m) (Fin m) ℝ) : ℂ) = (A : ℂ) * ∫ H, F H X ∂μ := by
    intro X
    rw [hFdef]
    simp only
    rw [integral_const_mul, integral_complex_ofReal, hZ]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · have := (hfi.integral_prod_right).const_mul (A : ℂ)
    refine Integrable.congr this (Filter.Eventually.of_forall fun X => ?_)
    exact (htgt X).symm
  · rw [show (∫ X in posDefCone m, (etr (-(T * (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
        (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
        (zonalPolynomial κ (X : Matrix (Fin m) (Fin m) ℝ) : ℂ) ∂TauCeti.symmetricLebesgue m) =
        ∫ X, (A : ℂ) * ∫ H, F H X ∂μ ∂ν from integral_congr_ae
          (Filter.Eventually.of_forall htgt)]
    rw [integral_const_mul, ← integral_integral_swap hfi]
    have hin : ∀ H : Matrix.orthogonalGroup (Fin m) ℝ, ∫ X, F H X ∂ν =
        multivariateGammaVec m (fun j => a + κ j) * (T.det : ℂ) ^ (-a) *
        (leadingMinorPowProd κ ((H : Matrix (Fin m) (Fin m) ℝ) * T⁻¹ *
          (H : Matrix (Fin m) (Fin m) ℝ)ᵀ) : ℂ) :=
      fun H => (hasIntegralOn_laplace_leadingMinorPowProd_orthogonal_conj κ hκ hT ha H).2
    simp_rw [hin]
    rw [integral_const_mul, integral_complex_ofReal, hZ]
    push_cast
    ring

/-- DLMF 35.4.9 (beta integral): for `T ∈ Ω` and `ℜa, ℜb > (m-1)/2`,
`∫_{0<X<I} |X|^{a-(m+1)/2} |I - X|^{b-(m+1)/2} Z_κ(TX) dX = [a]_κ / [a+b]_κ B_m(a, b) Z_κ(T)`,
with `Z_κ(TX)` the function of the eigenvalues of `TX`, written as `Z_κ(X^{1/2} T X^{1/2})`. -/
@[dlmf 35.4.E9]
theorem hasIntegralOn_zonalPolynomial_beta {m : ℕ} (κ : Fin m → ℕ) (hκ : Antitone κ)
    {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef) {a b : ℂ} (ha : ((m : ℝ) - 1) / 2 < a.re)
    (hb : ((m : ℝ) - 1) / 2 < b.re) :
    HasIntegralOn (m := m) (matrixInterval 0 1)
      (fun X => ((X.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
        (((1 - X).det : ℂ) ^ (b - ((m : ℂ) + 1) / 2)) *
        (zonalPolynomial κ (CFC.sqrt X * T * CFC.sqrt X) : ℂ))
      (partitionalShiftedFactorial a κ / partitionalShiftedFactorial (a + b) κ *
        multivariateBeta m a b * (zonalPolynomial κ T : ℂ)) := by
  sorry

/-! ## Homogeneity -/

/-- Homogeneity: `Z_κ(cT) = c^{|κ|} Z_κ(T)` for a partition `κ` and real `c`. -/
theorem zonalPolynomial_smul {m : ℕ} (κ : Fin m → ℕ) (hκ : Antitone κ) (c : ℝ)
    (T : Matrix (Fin m) (Fin m) ℝ) :
    zonalPolynomial κ (c • T) = c ^ (∑ j, κ j) * zonalPolynomial κ T := by
  unfold zonalPolynomial
  have hminor : ∀ (M : Matrix (Fin m) (Fin m) ℝ) (j : Fin m),
      leadingMinor (c • M) (j.1 + 1) = c ^ (j.1 + 1) * leadingMinor M (j.1 + 1) := by
    intro M j
    have hj : j.1 + 1 ≤ m := j.2
    simp only [leadingMinor, hj, dite_true]
    rw [show (c • M).submatrix (Fin.castLE hj) (Fin.castLE hj) =
      c • M.submatrix (Fin.castLE hj) (Fin.castLE hj) from rfl, Matrix.det_smul, Fintype.card_fin]
  have hint : ∀ H : Matrix.orthogonalGroup (Fin m) ℝ,
      (∏ j : Fin m, leadingMinor ((H : Matrix (Fin m) (Fin m) ℝ) * (c • T) *
        (H : Matrix (Fin m) (Fin m) ℝ)ᵀ) (j.1 + 1) ^ (κ j - nextPart κ j)) =
      c ^ (∑ j, κ j) * ∏ j : Fin m, leadingMinor ((H : Matrix (Fin m) (Fin m) ℝ) * T *
        (H : Matrix (Fin m) (Fin m) ℝ)ᵀ) (j.1 + 1) ^ (κ j - nextPart κ j) := by
    intro H
    rw [Matrix.mul_smul, Matrix.smul_mul]
    simp_rw [hminor, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum,
      sum_succ_mul_sub_nextPart κ hκ]
  simp_rw [hint]
  rw [integral_const_mul]
  ring

/-- `Z_κ(-T) = (-1)^{|κ|} Z_κ(T)` for a partition `κ`. -/
theorem zonalPolynomial_neg {m : ℕ} (κ : Fin m → ℕ) (hκ : Antitone κ)
    (T : Matrix (Fin m) (Fin m) ℝ) :
    zonalPolynomial κ (-T) = (-1) ^ (∑ j, κ j) * zonalPolynomial κ T := by
  rw [← zonalPolynomial_smul κ hκ, neg_one_smul]

/-! ## The case `m = 1` -/

/-- `k! 4^k (1/2)_k = (2k)!`. -/
private lemma factorial_mul_four_pow_mul_ascPochhammer_half (k : ℕ) :
    (k ! : ℝ) * 4 ^ k * (ascPochhammer ℝ k).eval (1 / 2) = ((2 * k)! : ℕ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, show 2 * (k + 1) = (2 * k + 1) + 1 by ring,
      Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k), Nat.factorial_succ k]
    push_cast
    rw [← ih]
    ring

/-- For `m = 1` the zonal polynomial of the partition `(k)` is `Z_{(k)}(t) = t^k`. -/
theorem zonalPolynomial_fin_one (k : ℕ) (T : Matrix (Fin 1) (Fin 1) ℝ) :
    zonalPolynomial (fun _ : Fin 1 => k) T = T 0 0 ^ k := by
  have hone : zonalPolynomialAtOne (fun _ : Fin 1 => k) = 1 := by
    unfold zonalPolynomialAtOne partitionalShiftedFactorial partitionLength
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · have hk' : k ≠ 0 := hk.ne'
      simp only [Finset.sum_const, one_smul,
        Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, Fin.val_zero,
        Nat.cast_zero, zero_div, sub_zero, lt_self_iff_false, false_and, ite_false,
        Finset.filter_singleton, ne_eq, hk', not_false_eq_true, ite_true, Finset.card_singleton,
        zero_lt_one, Nat.cast_one, mul_one, Nat.add_sub_cancel, Nat.sub_zero]
      rw [div_eq_one_iff_eq (by positivity), ← factorial_mul_four_pow_mul_ascPochhammer_half k]
      norm_num [pow_mul]
  unfold zonalPolynomial
  rw [hone, one_mul]
  have hint : ∀ H : Matrix.orthogonalGroup (Fin 1) ℝ,
      (∏ j : Fin 1, leadingMinor ((H : Matrix (Fin 1) (Fin 1) ℝ) * T *
        (H : Matrix (Fin 1) (Fin 1) ℝ)ᵀ) (j.1 + 1) ^ (k - nextPart (fun _ : Fin 1 => k) j)) =
      T 0 0 ^ k := by
    intro H
    have hn : nextPart (fun _ : Fin 1 => k) 0 = 0 := by simp [nextPart]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, Fin.val_zero,
      zero_add, hn, Nat.sub_zero, leadingMinor, le_refl, dite_eq_left, Fin.castLE_rfl,
      Matrix.submatrix_id_id]
    rw [det_orthogonal_conj, Matrix.det_fin_one]
  simp_rw [hint]
  simp

end DLMF.MatrixArgument
