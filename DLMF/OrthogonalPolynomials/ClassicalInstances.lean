/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.General
public import DLMF.OrthogonalPolynomials.Integrals
public import DLMF.OrthogonalPolynomials.JacobiDiscriminant

/-!
# The classical families as instances of the general theory

`IsOrthogonalPolynomials μ p` (`General.lean`) is instantiated for the Jacobi, Laguerre and
Hermite polynomials, with `μ` the weight measure `(volume.restrict I).withDensity w`.

* `isOrthogonalPolynomials_weightMeasure`: a weight positive on a set of positive measure that
  integrates every polynomial yields an instance as soon as orthogonality is known.
* `IsOrthogonalPolynomials.lt_of_mem_roots`, `mem_roots_lt`: the zeros lie strictly inside any
  almost-everywhere bounds of the measure; `exists_strictMono_roots` lists them increasingly
  and identifies them with all complex zeros.
* `jacobi_isOrthogonalPolynomials`, `laguerre_isOrthogonalPolynomials`,
  `hermite_isOrthogonalPolynomials`, with the real polynomials `jacobiPolyPR`, `laguerrePolyLR`
  and `hermitePolyHR`.
* Zeros: `jacobiPolyP_zeros_Ioo`, `laguerrePolyL_zeros_pos`, `hermitePolyH_zeros_bound`
  (the last with the bound `|x| < √(2n+1)` from a Gershgorin-type argument on the recurrence).
* Gauss quadrature and Christoffel–Darboux for each family.
* Completeness (`IsOrthogonalPolynomials.ae_eq_zero_of_forall_integral_mul_eq_zero`, from
  TauCeti's moment determinacy under a finite exponential moment): `jacobiPolyP_complete`,
  `laguerrePolyL_complete`, `hermitePolyH_complete`, `ultrasphPoly_complete`.
* Gegenbauer (`ultrasphPolyR`, `λ > -1/2`, `λ ≠ 0`), Legendre and Chebyshev `T` instances, with
  their zeros in `(-1,1)`.
-/

@[expose] public section

open MeasureTheory Polynomial Set
open scoped ENNReal NNReal Nat

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-! ### Weight measures -/

/-- The measure `w(x) dx` on `I`. -/
def weightMeasure (I : Set ℝ) (w : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict I).withDensity fun x => ((w x).toNNReal : ℝ≥0∞)

theorem integral_weightMeasure {I : Set ℝ} (hI : MeasurableSet I) {w : ℝ → ℝ}
    (hw : Measurable w) (hwnn : ∀ x ∈ I, 0 ≤ w x) (g : ℝ → ℝ) :
    ∫ x, g x ∂weightMeasure I w = ∫ x in I, w x * g x := by
  rw [weightMeasure, integral_withDensity_eq_integral_smul hw.real_toNNReal]
  refine setIntegral_congr_fun hI fun x hx => ?_
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hwnn x hx)]

theorem integrable_weightMeasure_iff {I : Set ℝ} (hI : MeasurableSet I) {w : ℝ → ℝ}
    (hw : Measurable w) (hwnn : ∀ x ∈ I, 0 ≤ w x) (g : ℝ → ℝ) :
    Integrable g (weightMeasure I w) ↔ IntegrableOn (fun x => w x * g x) I := by
  rw [weightMeasure, integrable_withDensity_iff_integrable_smul hw.real_toNNReal]
  refine integrableOn_congr_fun (fun x hx => ?_) hI
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hwnn x hx)]

theorem ae_weightMeasure_mem {I : Set ℝ} (hI : MeasurableSet I) (w : ℝ → ℝ) :
    ∀ᵐ x ∂weightMeasure I w, x ∈ I :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hI)

/-- A nonzero polynomial has positive weighted square integral on a set of positive measure. -/
theorem setIntegral_weight_mul_sq_pos {I : Set ℝ} (hI : MeasurableSet I) (hvol : 0 < volume I)
    {w : ℝ → ℝ} (hwpos : ∀ x ∈ I, 0 < w x) {q : ℝ[X]} (hq : q ≠ 0)
    (hint : IntegrableOn (fun x => w x * q.eval x ^ 2) I) :
    0 < ∫ x in I, w x * q.eval x ^ 2 := by
  have hnn : 0 ≤ᵐ[volume.restrict I] fun x => w x * q.eval x ^ 2 :=
    (ae_restrict_iff' hI).2 (Filter.Eventually.of_forall fun x hx =>
      mul_nonneg (hwpos x hx).le (sq_nonneg _))
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have hfin : ((q.roots.toFinset : Finset ℝ) : Set ℝ).Finite := Finset.finite_toSet _
  have hsub : I \ (q.roots.toFinset : Set ℝ) ⊆
      Function.support (fun x => w x * q.eval x ^ 2) ∩ I := by
    rintro x ⟨hxI, hxr⟩
    refine ⟨mul_ne_zero (hwpos x hxI).ne' (pow_ne_zero 2 fun h => hxr ?_), hxI⟩
    simp [Multiset.mem_toFinset, mem_roots hq, h]
  calc (0 : ℝ≥0∞) < volume I := hvol
    _ = volume (I \ (q.roots.toFinset : Set ℝ)) :=
      (measure_sdiff_null (hfin.measure_zero volume)).symm
    _ ≤ _ := measure_mono hsub

/-- The general theory applies to any weight that is positive on a set of positive measure and
integrates every polynomial. -/
theorem isOrthogonalPolynomials_weightMeasure {I : Set ℝ} (hI : MeasurableSet I)
    (hvol : 0 < volume I) {w : ℝ → ℝ} (hw : Measurable w) (hwpos : ∀ x ∈ I, 0 < w x)
    (hint : ∀ q : ℝ[X], IntegrableOn (fun x => q.eval x * w x) I)
    {p : ℕ → ℝ[X]} (hdeg : ∀ n, (p n).natDegree = n) (hne : ∀ n, p n ≠ 0)
    (horth : ∀ m n, m ≠ n → ∫ x in I, (p m).eval x * (p n).eval x * w x = 0) :
    IsOrthogonalPolynomials (weightMeasure I w) p := by
  have hwnn : ∀ x ∈ I, 0 ≤ w x := fun x hx => (hwpos x hx).le
  have hsq (q : ℝ[X]) : IntegrableOn (fun x => w x * q.eval x ^ 2) I :=
    (hint (q * q)).congr_fun (fun x _ => by simp only [eval_mul]; ring) hI
  refine ⟨hdeg, fun n => ?_, fun n => ?_, fun m n hmn => ?_⟩
  · exact (integrable_weightMeasure_iff hI hw hwnn _).2 (hsq (p n))
  · rw [integral_weightMeasure hI hw hwnn]
    exact setIntegral_weight_mul_sq_pos hI hvol hwpos (hne n) (hsq (p n))
  · rw [integral_weightMeasure hI hw hwnn, ← horth m n hmn]
    exact setIntegral_congr_fun hI fun x _ => by ring

/-! ### Zeros lie in the support -/

namespace IsOrthogonalPolynomials

variable {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)

include h

/-- Factoring out a zero of `p n`: the cofactor is nonzero and of degree less than `n`. -/
theorem exists_cofactor {n : ℕ} {x₀ : ℝ} (hx : x₀ ∈ (p n).roots) :
    ∃ q : ℝ[X], q ≠ 0 ∧ q.degree < n ∧ ∀ x, (p n).eval x = (x - x₀) * q.eval x := by
  have hp0 := h.ne_zero n
  have hroot : IsRoot (p n) x₀ := (mem_roots hp0).1 hx
  have hfac : (X - C x₀) * (p n /ₘ (X - C x₀)) = p n := mul_divByMonic_eq_iff_isRoot.2 hroot
  refine ⟨p n /ₘ (X - C x₀), fun h0 => ?_, ?_, fun x => ?_⟩
  · rw [h0, mul_zero] at hfac
    exact hp0 hfac.symm
  · have hlt := degree_divByMonic_lt (p n) (X - C x₀) hp0 (by rw [degree_X_sub_C]; simp)
    rwa [degree_eq_natDegree hp0, h.1 n] at hlt
  · conv_lhs => rw [← hfac]
    simp

/-- If `(x - x₀) q(x)²` integrates to zero against `μ` and `x₀ < x` almost everywhere, then
`q = 0`; the contrapositive drives the support theorems. -/
theorem eq_of_sign {q : ℝ[X]} (hq : q ≠ 0) {N : ℕ} (hd : q.degree < N) {s : ℝ → ℝ}
    (hs : ∀ᵐ x ∂μ, 0 < s x) (hsi : Integrable (fun x => s x * q.eval x ^ 2) μ)
    (h0 : ∫ x, s x * q.eval x ^ 2 ∂μ = 0) : False := by
  have hnn : 0 ≤ᵐ[μ] fun x => s x * q.eval x ^ 2 :=
    hs.mono fun x hx => mul_nonneg hx.le (sq_nonneg _)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hsi).1 h0
  have hq2 : (fun x => q.eval x ^ 2) =ᵐ[μ] 0 := by
    filter_upwards [hz, hs] with x hx hsx
    exact (mul_eq_zero.1 hx).resolve_left hsx.ne'
  have hpos := h.integral_eval_sq_pos hq hd
  rw [integral_congr_ae hq2] at hpos
  simp at hpos

/-- Every zero of `p n` lies to the right of an almost-everywhere lower bound of `μ`. -/
theorem lt_of_mem_roots {a : ℝ} (ha : ∀ᵐ x ∂μ, a < x) {n : ℕ} {x₀ : ℝ}
    (hx : x₀ ∈ (p n).roots) : a < x₀ := by
  by_contra hle
  push Not at hle
  obtain ⟨q, hq, hd, hev⟩ := h.exists_cofactor hx
  have hint : ∫ x, q.eval x * (p n).eval x ∂μ = 0 := h.integral_mul_eq_zero_of_degree_lt hd
  refine h.eq_of_sign hq hd (s := fun x => x - x₀) (ha.mono fun x hx => by linarith)
    ((h.integrable_mul q (p n)).congr (Filter.Eventually.of_forall fun x => ?_)) ?_
  · simp only [hev]; ring
  · rw [← hint]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hev]; ring)

/-- Every zero of `p n` lies to the left of an almost-everywhere upper bound of `μ`. -/
theorem mem_roots_lt {b : ℝ} (hb : ∀ᵐ x ∂μ, x < b) {n : ℕ} {x₀ : ℝ}
    (hx : x₀ ∈ (p n).roots) : x₀ < b := by
  by_contra hle
  push Not at hle
  obtain ⟨q, hq, hd, hev⟩ := h.exists_cofactor hx
  have hint : ∫ x, q.eval x * (p n).eval x ∂μ = 0 := h.integral_mul_eq_zero_of_degree_lt hd
  refine h.eq_of_sign hq hd (s := fun x => x₀ - x) (hb.mono fun x hx => by linarith)
    ((h.integrable_mul q (p n)).neg.congr (Filter.Eventually.of_forall fun x => ?_)) ?_
  · simp only [hev, Pi.neg_apply]; ring
  · rw [show (0 : ℝ) = -0 by simp, ← hint, ← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hev]; ring)

/-- The zeros of `p n`, listed increasingly; they are all the complex zeros. -/
theorem exists_strictMono_roots (n : ℕ) :
    ∃ x : Fin n → ℝ, StrictMono x ∧ (∀ i, x i ∈ (p n).roots) ∧
      ∀ z : ℂ, ((p n).map (algebraMap ℝ ℂ)).eval z = 0 ↔ ∃ i, z = (x i : ℂ) := by
  classical
  obtain ⟨hcard, hnodup⟩ := orthogonal_polynomials_roots h n
  have hs : (p n).roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnodup, hcard]
  let x := (p n).roots.toFinset.orderEmbOfFin hs
  have hmem (i : Fin n) : x i ∈ (p n).roots :=
    Multiset.mem_toFinset.1 (Finset.orderEmbOfFin_mem _ hs i)
  refine ⟨x, x.strictMono, hmem, fun z => ?_⟩
  have hp0 := h.ne_zero n
  have hmap0 : (p n).map (algebraMap ℝ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).2 hp0
  have hroots := roots_map_of_injective_of_card_eq_natDegree (algebraMap ℝ ℂ).injective
    (hcard.trans (h.1 n).symm)
  rw [← IsRoot.def, ← mem_roots hmap0, ← hroots, Multiset.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hrs : r ∈ ((p n).roots.toFinset : Set ℝ) := Multiset.mem_toFinset.2 hr
    rw [← Finset.range_orderEmbOfFin _ hs] at hrs
    obtain ⟨i, rfl⟩ := Set.mem_range.1 hrs
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨x i, hmem i, rfl⟩

end IsOrthogonalPolynomials

/-! ### Hermite polynomials -/

/-- The Hermite weight `e^{-x²}` on `ℝ`. -/
def hermiteMeasure : Measure ℝ := weightMeasure univ fun x => Real.exp (-(x ^ 2))

theorem hermitePolyHR_natDegree (n : ℕ) : (hermitePolyHR n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (hermitePolyHR_natDegree_coeff n).1
    (by rw [(hermitePolyHR_natDegree_coeff n).2]; positivity)

theorem hermitePolyHR_ne_zero (n : ℕ) : hermitePolyHR n ≠ 0 := fun h0 => by
  have := (hermitePolyHR_natDegree_coeff n).2
  rw [h0, coeff_zero] at this
  exact (pow_ne_zero n two_ne_zero) this.symm

/-- The Hermite polynomials are orthogonal for `e^{-x²} dx`. -/
theorem hermite_isOrthogonalPolynomials : IsOrthogonalPolynomials hermiteMeasure hermitePolyHR := by
  refine isOrthogonalPolynomials_weightMeasure MeasurableSet.univ (by simp) (by fun_prop)
    (fun x _ => Real.exp_pos _) (fun q => (integrable_eval_mul_exp_neg_sq q).integrableOn)
    hermitePolyHR_natDegree hermitePolyHR_ne_zero fun m n hmn => ?_
  rw [setIntegral_univ]
  have := hermitePolyH_orthogonality m n
  simp only [aeval_hermitePolyH_eq_eval, hmn, ite_false] at this
  exact this

theorem aeval_hermitePolyH_complex (n : ℕ) (z : ℂ) :
    (aeval z (hermitePolyH n) : ℂ) = ((hermitePolyHR n).map (algebraMap ℝ ℂ)).eval z := by
  rw [aeval_def, eval₂_eq_eval_map, hermitePolyHR, Polynomial.map_map]
  congr 2

/-- The zeros of `H_n` are real and simple: the qualitative part of DLMF 18.16.16. -/
theorem hermitePolyH_zeros_real (n : ℕ) :
    ∃ x : Fin n → ℝ, StrictMono x ∧
      ∀ z : ℂ, (aeval z (hermitePolyH n) : ℂ) = 0 ↔ ∃ i, z = (x i : ℂ) := by
  obtain ⟨x, hx, -, hz⟩ := hermite_isOrthogonalPolynomials.exists_strictMono_roots n
  exact ⟨x, hx, fun z => by rw [aeval_hermitePolyH_complex]; exact hz z⟩

/-! #### The bound `|x| < √(2n+1)` for the zeros of `H_n`

With `c = √(2n+1)` and `u_k = H_k(ξ)/c^k`, the recurrence reads
`ξ u_k = (c/2) u_{k+1} + (k/c) u_{k-1}`. At an index where `|u_k|` is maximal over `k < n`
(using `u_n = 0` at a zero `ξ` of `H_n`), this gives `|ξ| ≤ c/2 + (n-1)/c < c`. -/

theorem eval_hermitePolyHR_succ_succ (k : ℕ) (ξ : ℝ) :
    (hermitePolyHR (k + 2)).eval ξ =
      2 * ξ * (hermitePolyHR (k + 1)).eval ξ - 2 * (k + 1) * (hermitePolyHR k).eval ξ := by
  simp only [hermitePolyHR, hermitePolyH_recurrence, Polynomial.map_sub, Polynomial.map_mul,
    map_X, eval_sub, eval_mul, eval_X, eq_intCast]
  push_cast
  simp

theorem eval_hermitePolyHR_one (ξ : ℝ) : (hermitePolyHR 1).eval ξ = 2 * ξ := by
  simp [hermitePolyHR]

/-- Every zero of `H_n` satisfies `|ξ| < √(2n+1)` (DLMF 18.16.16). -/
theorem abs_lt_sqrt_of_hermitePolyHR_eval_eq_zero {n : ℕ} {ξ : ℝ}
    (hroot : (hermitePolyHR n).eval ξ = 0) : |ξ| < Real.sqrt (2 * n + 1) := by
  set c := Real.sqrt (2 * n + 1) with hcdef
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = 2 * n + 1 := Real.sq_sqrt (by positivity)
  have hn : n ≠ 0 := by
    rintro rfl
    simp [hermitePolyHR] at hroot
  set H : ℕ → ℝ := fun k => (hermitePolyHR k).eval ξ with hH
  set u : ℕ → ℝ := fun k => H k / c ^ k with hu
  have hrec (k : ℕ) (hk : 1 ≤ k) :
      ξ * u k = c / 2 * u (k + 1) + k / c * u (k - 1) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    have h2 := eval_hermitePolyHR_succ_succ j ξ
    simp only [hu, hH, show 1 + j = j + 1 by omega, Nat.add_sub_cancel]
    rw [h2]
    field_simp
    push_cast
    ring
  have hrec0 : ξ * u 0 = c / 2 * u 1 := by
    simp only [hu, hH, eval_hermitePolyHR_one, pow_zero, pow_one]
    simp [hermitePolyHR]
    field_simp
  obtain ⟨k₀, hk₀, hmax⟩ := Finset.exists_max_image (Finset.range n) (fun k => |u k|)
    ⟨0, Finset.mem_range.2 (Nat.pos_of_ne_zero hn)⟩
  have hk₀n : k₀ < n := Finset.mem_range.1 hk₀
  set M := |u k₀|
  have hu0 : u 0 = 1 := by simp [hu, hH, hermitePolyHR]
  have hM : 0 < M := lt_of_lt_of_le (by rw [hu0]; norm_num)
    (hmax 0 (Finset.mem_range.2 (Nat.pos_of_ne_zero hn)))
  have hup : |u (k₀ + 1)| ≤ M := by
    rcases Nat.lt_or_ge (k₀ + 1) n with h | h
    · exact hmax _ (Finset.mem_range.2 h)
    · have : k₀ + 1 = n := by omega
      rw [this]
      simp only [hu, hH, hroot, zero_div, abs_zero]
      exact hM.le
  have hdown : |u (k₀ - 1)| ≤ M := hmax _ (Finset.mem_range.2 (by omega))
  have hbound : |ξ| * M ≤ (c / 2 + (n - 1) / c) * M := by
    have hk₀le : (k₀ : ℝ) ≤ n - 1 := by
      have : (k₀ : ℝ) + 1 ≤ n := by exact_mod_cast hk₀n
      linarith
    rcases Nat.eq_zero_or_pos k₀ with h0 | hpos
    · have hk : k₀ = 0 := h0
      have h1 : |ξ| * M = c / 2 * |u 1| := by
        simp only [M, hk]
        rw [← abs_mul, hrec0, abs_mul, abs_of_pos (half_pos hc)]
      rw [h1]
      have hnn : 0 ≤ (n - 1 : ℝ) / c * M := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
        exact mul_nonneg (div_nonneg (by linarith) hc.le) hM.le
      have := mul_le_mul_of_nonneg_left (show |u 1| ≤ M by simpa [hk] using hup)
        (half_pos hc).le
      nlinarith
    · have h1 : |ξ| * M ≤ c / 2 * |u (k₀ + 1)| + k₀ / c * |u (k₀ - 1)| := by
        rw [show |ξ| * M = |ξ * u k₀| from (abs_mul _ _).symm, hrec k₀ hpos]
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_of_pos (half_pos hc),
          abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hc.le)]
      calc |ξ| * M ≤ c / 2 * |u (k₀ + 1)| + k₀ / c * |u (k₀ - 1)| := h1
        _ ≤ c / 2 * M + (n - 1) / c * M := by
          have h2 := mul_le_mul_of_nonneg_left hup (half_pos hc).le
          have h3 : (k₀ : ℝ) / c * |u (k₀ - 1)| ≤ (n - 1) / c * M :=
            mul_le_mul (div_le_div_of_nonneg_right hk₀le hc.le) hdown (abs_nonneg _)
              (div_nonneg (by linarith [(Nat.cast_nonneg k₀ : (0 : ℝ) ≤ k₀)]) hc.le)
          linarith
        _ = (c / 2 + (n - 1) / c) * M := by ring
  have hξ : |ξ| ≤ c / 2 + (n - 1) / c := le_of_mul_le_mul_right hbound hM
  have hlt : c / 2 + (n - 1) / c < c := by
    rw [div_add_div _ _ (two_ne_zero) hc.ne', div_lt_iff₀ (by positivity)]
    nlinarith
  exact hξ.trans_lt hlt

/-- The zeros of `H_n` are real, simple, and satisfy `|x| < √(2n+1)` (DLMF 18.16.16). -/
theorem hermitePolyH_zeros_bound (n : ℕ) :
    ∃ x : Fin n → ℝ, StrictMono x ∧ (∀ i, |x i| < Real.sqrt (2 * n + 1)) ∧
      ∀ z : ℂ, (aeval z (hermitePolyH n) : ℂ) = 0 ↔ ∃ i, z = (x i : ℂ) := by
  obtain ⟨x, hx, hmem, hz⟩ := hermite_isOrthogonalPolynomials.exists_strictMono_roots n
  refine ⟨x, hx, fun i => abs_lt_sqrt_of_hermitePolyHR_eval_eq_zero ?_, fun z => ?_⟩
  · exact (mem_roots (hermitePolyHR_ne_zero n)).1 (hmem i)
  · rw [aeval_hermitePolyH_complex]
    exact hz z

/-! ### Real forms of complex-defined polynomials -/

open DLMF.Hypergeometric DLMF.Confluent in
theorem poch_ofReal_eq_eval (x : ℝ) (k : ℕ) : poch (x : ℂ) k = ((ascPochhammer ℝ k).eval x : ℝ) := by
  rw [poch, ← ascPochhammer_map (algebraMap ℝ ℂ), eval_map]
  exact eval₂_at_apply (algebraMap ℝ ℂ) x

theorem eval_map_ofReal (q : ℝ[X]) (x : ℝ) :
    (q.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((q.eval x : ℝ) : ℂ) := by
  rw [eval_map]
  exact eval₂_at_apply (algebraMap ℝ ℂ) x

/-! ### Laguerre polynomials -/

/-- The real coefficients of `L_n^{(α)}` in powers of `x`. -/
def laguerreCoeffR (α : ℝ) (n j : ℕ) : ℝ :=
  (ascPochhammer ℝ n).eval (α + 1) / n ! *
    ((ascPochhammer ℝ j).eval (-(n : ℝ)) / ((ascPochhammer ℝ j).eval (α + 1) * j !))

/-- `L_n^{(α)}` as a real polynomial. -/
def laguerrePolyLR (α : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (n + 1), C (laguerreCoeffR α n j) * X ^ j

open DLMF.Hypergeometric DLMF.Confluent in
theorem laguerreCoeffR_ofReal (α : ℝ) (n j : ℕ) :
    ((laguerreCoeffR α n j : ℝ) : ℂ) =
      poch ((α : ℂ) + 1) n / n ! * kummerMCoeff (-(n : ℂ)) ((α : ℂ) + 1) j := by
  rw [show (α : ℂ) + 1 = ((α + 1 : ℝ) : ℂ) by push_cast; ring,
    show -(n : ℂ) = ((-(n : ℝ) : ℝ) : ℂ) by push_cast; ring, kummerMCoeff, poch_ofReal_eq_eval,
    poch_ofReal_eq_eval, poch_ofReal_eq_eval, laguerreCoeffR]
  push_cast
  ring

theorem eval_map_laguerrePolyLR (α : ℝ) (n : ℕ) (z : ℂ) :
    ((laguerrePolyLR α n).map (algebraMap ℝ ℂ)).eval z = laguerrePolyL α n z := by
  rw [laguerrePolyL_eq_sum_coeff, laguerrePolyLR, Polynomial.map_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, eval_mul, eval_C, eval_pow,
    eval_X]
  rw [show algebraMap ℝ ℂ (laguerreCoeffR α n j) = ((laguerreCoeffR α n j : ℝ) : ℂ) from rfl,
    laguerreCoeffR_ofReal]

theorem eval_laguerrePolyLR (α : ℝ) (n : ℕ) (x : ℝ) :
    (((laguerrePolyLR α n).eval x : ℝ) : ℂ) = laguerrePolyL α n x := by
  rw [← eval_map_ofReal, eval_map_laguerrePolyLR]

theorem laguerreCoeffR_self_ne_zero {α : ℝ} (hα : -1 < α) (n : ℕ) : laguerreCoeffR α n n ≠ 0 := by
  have hp : 0 < (ascPochhammer ℝ n).eval (α + 1) := ascPochhammer_pos n _ (by linarith)
  have hneg : (ascPochhammer ℝ n).eval (-(n : ℝ)) ≠ 0 := by
    rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_self]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast n.factorial_ne_zero)
  unfold laguerreCoeffR
  have hf : (n ! : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  exact mul_ne_zero (div_ne_zero hp.ne' hf) (div_ne_zero hneg (mul_ne_zero hp.ne' hf))

theorem laguerrePolyLR_coeff (α : ℝ) (n k : ℕ) :
    (laguerrePolyLR α n).coeff k = if k < n + 1 then laguerreCoeffR α n k else 0 := by
  simp only [laguerrePolyLR, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem laguerrePolyLR_natDegree {α : ℝ} (hα : -1 < α) (n : ℕ) :
    (laguerrePolyLR α n).natDegree = n := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · refine natDegree_le_iff_coeff_eq_zero.2 fun k hk => ?_
    rw [laguerrePolyLR_coeff]
    simp [show ¬ k < n + 1 by omega]
  · rw [laguerrePolyLR_coeff]
    simpa using laguerreCoeffR_self_ne_zero hα n

theorem laguerrePolyLR_ne_zero {α : ℝ} (hα : -1 < α) (n : ℕ) : laguerrePolyLR α n ≠ 0 :=
  fun h0 => laguerreCoeffR_self_ne_zero hα n (by
    have := laguerrePolyLR_coeff α n n
    simp only [h0, coeff_zero, show n < n + 1 by omega, ite_true] at this
    exact this.symm)

/-- The Laguerre weight `x^α e^{-x}`. -/
def laguerreWeight (α : ℝ) (x : ℝ) : ℝ := x ^ α * Real.exp (-x)

/-- The Laguerre measure `x^α e^{-x} dx` on `(0,∞)`. -/
def laguerreMeasure (α : ℝ) : Measure ℝ := weightMeasure (Ioi 0) (laguerreWeight α)

theorem integrableOn_eval_mul_laguerreWeight {α : ℝ} (hα : -1 < α) (q : ℝ[X]) :
    IntegrableOn (fun x => q.eval x * laguerreWeight α x) (Ioi 0) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    refine IntegrableOn.congr_fun (hp.add hq) (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, eval_add]
    ring
  | monomial k c =>
    have hG := Real.GammaIntegral_convergent (s := k + α + 1)
      (by have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith)
    refine IntegrableOn.congr_fun (hG.const_mul c) (fun x hx => ?_) measurableSet_Ioi
    simp only [eval_monomial, laguerreWeight]
    rw [show (k : ℝ) + α + 1 - 1 = k + α by ring, Real.rpow_add hx, Real.rpow_natCast]
    ring

/-- The Laguerre polynomials are orthogonal for `x^α e^{-x} dx`. -/
theorem laguerre_isOrthogonalPolynomials {α : ℝ} (hα : -1 < α) :
    IsOrthogonalPolynomials (laguerreMeasure α) (laguerrePolyLR α) := by
  refine isOrthogonalPolynomials_weightMeasure measurableSet_Ioi (by simp)
    (by fun_prop)
    (fun x hx => mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _))
    (integrableOn_eval_mul_laguerreWeight hα) (laguerrePolyLR_natDegree hα)
    (laguerrePolyLR_ne_zero hα) fun m n hmn => ?_
  have horth := laguerrePolyL_orthogonal (α := α) hα hmn
  have hc : (∫ x in Ioi (0 : ℝ), (((laguerrePolyLR α m).eval x * (laguerrePolyLR α n).eval x *
      laguerreWeight α x : ℝ) : ℂ)) = 0 := by
    rw [← horth]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [laguerreWeight]
    push_cast
    rw [eval_laguerrePolyLR, eval_laguerrePolyLR, Complex.ofReal_cpow (le_of_lt hx)]
    ring
  rw [integral_complex_ofReal] at hc
  exact_mod_cast hc

/-- The zeros of `L_n^{(α)}` are real, simple and positive (DLMF §18.16(iv)). -/
theorem laguerrePolyL_zeros_pos {α : ℝ} (hα : -1 < α) (n : ℕ) :
    ∃ x : Fin n → ℝ, StrictMono x ∧ (∀ i, 0 < x i) ∧
      ∀ z : ℂ, laguerrePolyL α n z = 0 ↔ ∃ i, z = (x i : ℂ) := by
  have h := laguerre_isOrthogonalPolynomials hα
  obtain ⟨x, hx, hmem, hz⟩ := h.exists_strictMono_roots n
  refine ⟨x, hx, fun i => h.lt_of_mem_roots ?_ (hmem i), fun z => ?_⟩
  · exact (ae_weightMeasure_mem measurableSet_Ioi _).mono fun x hx => hx
  · rw [← hz z, eval_map_laguerrePolyLR]

/-! ### Jacobi polynomials -/

/-- The real coefficients of `P_n^{(α,β)}` in powers of `(x - 1)/2`. -/
def jacobiCoeffR (α β : ℝ) (n k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval (n + α + β + 1) * (ascPochhammer ℝ (n - k)).eval (α + k + 1) /
    ((k ! : ℝ) * (n - k)!)

/-- `P_n^{(α,β)}` as a real polynomial. -/
def jacobiPolyPR (α β : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (jacobiCoeffR α β n k) * (C (1 / 2 : ℝ) * (X - C 1)) ^ k

theorem jacobiCoeffR_ofReal (α β : ℝ) (n k : ℕ) :
    ((jacobiCoeffR α β n k : ℝ) : ℂ) = JacobiDisc.coef α β n k := by
  rw [JacobiDisc.coef,
    show (n : ℂ) + α + β + 1 = ((n + α + β + 1 : ℝ) : ℂ) by push_cast; ring,
    show (α : ℂ) + k + 1 = ((α + k + 1 : ℝ) : ℂ) by push_cast; ring,
    poch_ofReal_eq_eval, poch_ofReal_eq_eval,
    jacobiCoeffR]
  push_cast
  ring

theorem map_jacobiPolyPR (α β : ℝ) (n : ℕ) :
    (jacobiPolyPR α β n).map (algebraMap ℝ ℂ) = JacobiDisc.jacPoly α β n := by
  rw [jacobiPolyPR, JacobiDisc.jacPoly, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_C, map_X]
  rw [show algebraMap ℝ ℂ (jacobiCoeffR α β n k) = ((jacobiCoeffR α β n k : ℝ) : ℂ) from rfl,
    jacobiCoeffR_ofReal]
  norm_num

theorem eval_map_jacobiPolyPR {α : ℝ} (hα : -1 < α) (β : ℝ) (n : ℕ) (z : ℂ) :
    ((jacobiPolyPR α β n).map (algebraMap ℝ ℂ)).eval z = jacobiPolyP α β n z := by
  rw [map_jacobiPolyPR, JacobiDisc.eval_jacPoly (by simpa using hα)]

theorem eval_jacobiPolyPR {α : ℝ} (hα : -1 < α) (β : ℝ) (n : ℕ) (x : ℝ) :
    (((jacobiPolyPR α β n).eval x : ℝ) : ℂ) = jacobiPolyP α β n x := by
  rw [← eval_map_ofReal, eval_map_jacobiPolyPR hα]

theorem jacobiCoeffR_self_ne_zero {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    jacobiCoeffR α β n n ≠ 0 := by
  have hp : 0 < (ascPochhammer ℝ n).eval (n + α + β + 1) := by
    rcases n with _ | n
    · simp
    · exact ascPochhammer_pos _ _ (by push_cast; linarith)
  unfold jacobiCoeffR
  simp only [Nat.sub_self, ascPochhammer_zero, eval_one, mul_one, Nat.factorial_zero,
    Nat.cast_one]
  exact div_ne_zero hp.ne' (by exact_mod_cast n.factorial_ne_zero)

theorem jacPoly_ofReal_natDegree_lc {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    (JacobiDisc.jacPoly α β n).natDegree = n ∧
      (JacobiDisc.jacPoly α β n).leadingCoeff = JacobiDisc.coef α β n n * (1 / 2) ^ n :=
  JacobiDisc.jacPoly_natDegree_lc _ _ n (by
    rw [← jacobiCoeffR_ofReal]
    exact_mod_cast jacobiCoeffR_self_ne_zero hα hβ n)

theorem jacobiPolyPR_natDegree {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    (jacobiPolyPR α β n).natDegree = n := by
  rw [← natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective, map_jacobiPolyPR]
  exact (jacPoly_ofReal_natDegree_lc hα hβ n).1

theorem jacobiPolyPR_ne_zero {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    jacobiPolyPR α β n ≠ 0 := fun h0 => by
  have hlc := (jacPoly_ofReal_natDegree_lc hα hβ n).2
  rw [← map_jacobiPolyPR, h0, Polynomial.map_zero, leadingCoeff_zero, ← jacobiCoeffR_ofReal]
    at hlc
  have := jacobiCoeffR_self_ne_zero hα hβ n
  have h2 : ((jacobiCoeffR α β n n : ℝ) : ℂ) * (1 / 2) ^ n ≠ 0 :=
    mul_ne_zero (by exact_mod_cast this) (by norm_num)
  exact h2 hlc.symm

/-- The Jacobi weight `(1-x)^α (1+x)^β`. -/
def jacobiWeight (α β : ℝ) (x : ℝ) : ℝ := (1 - x) ^ α * (1 + x) ^ β

/-- `jacobiMeasure` (`Classical.lean`) is the weight measure of `jacobiWeight`. -/
theorem jacobiMeasure_eq_weightMeasure (α β : ℝ) :
    jacobiMeasure α β = weightMeasure (Ioo (-1) 1) (jacobiWeight α β) := rfl

theorem intervalIntegrable_jacobiWeight {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    IntervalIntegrable (jacobiWeight α β) volume (-1) 1 := by
  have h1 : IntervalIntegrable (fun x : ℝ => (1 + x) ^ β) volume (-1) 0 := by
    have := (intervalIntegral.intervalIntegrable_rpow' hβ (a := 0) (b := 1)).comp_add_right 1
    simpa [add_comm] using this
  have h2 : ContinuousOn (fun x : ℝ => (1 - x) ^ α) (uIcc (-1) 0) := by
    refine ContinuousOn.rpow_const (by fun_prop) fun x hx => Or.inl ?_
    rw [uIcc_of_le (by norm_num)] at hx
    linarith [hx.2]
  have h3 : IntervalIntegrable (fun x : ℝ => (1 - x) ^ α) volume 0 1 := by
    have := (intervalIntegral.intervalIntegrable_rpow' hα (a := 1) (b := 0)).comp_sub_left 1
    simpa using this
  have h4 : ContinuousOn (fun x : ℝ => (1 + x) ^ β) (uIcc 0 1) := by
    refine ContinuousOn.rpow_const (by fun_prop) fun x hx => Or.inl ?_
    rw [uIcc_of_le (by norm_num)] at hx
    linarith [hx.1]
  exact (h1.continuousOn_mul h2).trans (h3.mul_continuousOn h4)

theorem integrableOn_eval_mul_jacobiWeight {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (q : ℝ[X]) :
    IntegrableOn (fun x => q.eval x * jacobiWeight α β x) (Ioo (-1) 1) :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).1
    ((intervalIntegrable_jacobiWeight hα hβ).continuousOn_mul q.continuous.continuousOn)

/-- The Jacobi polynomials are orthogonal for `(1-x)^α (1+x)^β dx`. -/
theorem jacobi_isOrthogonalPolynomials {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    IsOrthogonalPolynomials (jacobiMeasure α β) (jacobiPolyPR α β) := by
  rw [jacobiMeasure_eq_weightMeasure]
  refine isOrthogonalPolynomials_weightMeasure measurableSet_Ioo (by simp) (by fun_prop)
    (fun x hx => mul_pos (Real.rpow_pos_of_pos (by linarith [hx.2]) _)
      (Real.rpow_pos_of_pos (by linarith [hx.1]) _))
    (integrableOn_eval_mul_jacobiWeight hα hβ) (jacobiPolyPR_natDegree hα hβ)
    (jacobiPolyPR_ne_zero hα hβ) fun m n hmn => ?_
  have horth := jacobiPolyP_orthogonal (α := α) (β := β) hα hβ hmn
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo] at horth
  have hc : (∫ x in Ioo (-1 : ℝ) 1, (((jacobiPolyPR α β m).eval x *
      (jacobiPolyPR α β n).eval x * jacobiWeight α β x : ℝ) : ℂ)) = 0 := by
    rw [← horth]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    simp only [jacobiWeight]
    push_cast
    rw [eval_jacobiPolyPR hα, eval_jacobiPolyPR hα,
      Complex.ofReal_cpow (by linarith [hx.2] : (0 : ℝ) ≤ 1 - x),
      Complex.ofReal_cpow (by linarith [hx.1] : (0 : ℝ) ≤ 1 + x)]
    push_cast
    ring
  rw [integral_complex_ofReal] at hc
  exact_mod_cast hc

/-- The zeros of `P_n^{(α,β)}` are real, simple and lie in `(-1,1)` (DLMF §18.16(i)). -/
theorem jacobiPolyP_zeros_Ioo {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    ∃ x : Fin n → ℝ, StrictMono x ∧ (∀ i, x i ∈ Ioo (-1) 1) ∧
      ∀ z : ℂ, jacobiPolyP α β n z = 0 ↔ ∃ i, z = (x i : ℂ) := by
  have h := jacobi_isOrthogonalPolynomials hα hβ
  obtain ⟨x, hx, hmem, hz⟩ := h.exists_strictMono_roots n
  have hae : ∀ᵐ x ∂jacobiMeasure α β, x ∈ Ioo (-1 : ℝ) 1 :=
    ae_weightMeasure_mem measurableSet_Ioo (jacobiWeight α β)
  refine ⟨x, hx, fun i => ⟨h.lt_of_mem_roots (hae.mono fun x hx => hx.1) (hmem i),
    h.mem_roots_lt (hae.mono fun x hx => hx.2) (hmem i)⟩, fun z => ?_⟩
  rw [← hz z, eval_map_jacobiPolyPR hα]

/-! ### Christoffel–Darboux and Gauss quadrature for the classical families -/

/-- Gauss quadrature for the Jacobi weight: `n` positive weights at the zeros of the degree-`n`
polynomial integrate every polynomial of degree below `2n` exactly. -/
theorem jacobi_gauss_quadrature {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : n ≠ 0)
    (x : Fin n → ℝ) (hroot : ∀ i, (jacobiPolyPR α β n).eval (x i) = 0)
    (hinj : Function.Injective x) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ ∀ q : ℝ[X], q.natDegree < 2 * n →
      ∫ t in Ioo (-1) 1, (jacobiWeight α β) t * q.eval t = ∑ i, w i * q.eval (x i) := by
  obtain ⟨w, hw, hq⟩ := gauss_quadrature (jacobi_isOrthogonalPolynomials hα hβ) hn x hroot hinj
  refine ⟨w, hw, fun q hd => ?_⟩
  rw [← hq q hd, jacobiMeasure_eq_weightMeasure,
    integral_weightMeasure (w := jacobiWeight α β) measurableSet_Ioo
      (by unfold jacobiWeight; fun_prop)
      (fun x hx => mul_nonneg (Real.rpow_nonneg (by linarith [hx.2]) _)
        (Real.rpow_nonneg (by linarith [hx.1]) _))]

/-- The Christoffel–Darboux formula for the Jacobi polynomials. -/
theorem jacobi_christoffel_darboux {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : n ≠ 0)
    {x y : ℝ}
    (hxy : x ≠ y) :
    ∑ k ∈ Finset.range n, (jacobiPolyPR α β k).eval x * (jacobiPolyPR α β k).eval y /
        (∫ t, (jacobiPolyPR α β k).eval t ^ 2 ∂jacobiMeasure α β) =
      ((jacobiPolyPR α β (n - 1)).leadingCoeff /
        ((jacobiPolyPR α β n).leadingCoeff *
          ∫ t, (jacobiPolyPR α β (n - 1)).eval t ^ 2 ∂jacobiMeasure α β)) *
        ((jacobiPolyPR α β n).eval x * (jacobiPolyPR α β (n - 1)).eval y -
          (jacobiPolyPR α β (n - 1)).eval x * (jacobiPolyPR α β n).eval y) / (x - y) :=
  christoffel_darboux (jacobi_isOrthogonalPolynomials hα hβ) hn hxy

/-- Gauss quadrature for the Laguerre weight: `n` positive weights at the zeros of the degree-`n`
polynomial integrate every polynomial of degree below `2n` exactly. -/
theorem laguerre_gauss_quadrature {α : ℝ} (hα : -1 < α) {n : ℕ} (hn : n ≠ 0)
    (x : Fin n → ℝ) (hroot : ∀ i, (laguerrePolyLR α n).eval (x i) = 0)
    (hinj : Function.Injective x) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ ∀ q : ℝ[X], q.natDegree < 2 * n →
      ∫ t in Ioi 0, (laguerreWeight α) t * q.eval t = ∑ i, w i * q.eval (x i) := by
  obtain ⟨w, hw, hq⟩ := gauss_quadrature (laguerre_isOrthogonalPolynomials hα) hn x hroot hinj
  refine ⟨w, hw, fun q hd => ?_⟩
  rw [← hq q hd, laguerreMeasure,
    integral_weightMeasure (w := laguerreWeight α) measurableSet_Ioi
      (by unfold laguerreWeight; fun_prop)
      (fun x hx => mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (Real.exp_pos _).le)]

/-- The Christoffel–Darboux formula for the Laguerre polynomials. -/
theorem laguerre_christoffel_darboux {α : ℝ} (hα : -1 < α) {n : ℕ} (hn : n ≠ 0) {x y : ℝ}
    (hxy : x ≠ y) :
    ∑ k ∈ Finset.range n, (laguerrePolyLR α k).eval x * (laguerrePolyLR α k).eval y /
        (∫ t, (laguerrePolyLR α k).eval t ^ 2 ∂laguerreMeasure α) =
      ((laguerrePolyLR α (n - 1)).leadingCoeff /
        ((laguerrePolyLR α n).leadingCoeff *
          ∫ t, (laguerrePolyLR α (n - 1)).eval t ^ 2 ∂laguerreMeasure α)) *
        ((laguerrePolyLR α n).eval x * (laguerrePolyLR α (n - 1)).eval y -
          (laguerrePolyLR α (n - 1)).eval x * (laguerrePolyLR α n).eval y) / (x - y) :=
  christoffel_darboux (laguerre_isOrthogonalPolynomials hα) hn hxy

/-- Gauss quadrature for the Hermite weight: `n` positive weights at the zeros of the degree-`n`
polynomial integrate every polynomial of degree below `2n` exactly. -/
theorem hermite_gauss_quadrature {n : ℕ} (hn : n ≠ 0)
    (x : Fin n → ℝ) (hroot : ∀ i, (hermitePolyHR n).eval (x i) = 0) (hinj : Function.Injective x) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ ∀ q : ℝ[X], q.natDegree < 2 * n →
      ∫ t in univ, (fun x => Real.exp (-(x ^ 2))) t * q.eval t = ∑ i, w i * q.eval (x i) := by
  obtain ⟨w, hw, hq⟩ := gauss_quadrature (hermite_isOrthogonalPolynomials) hn x hroot hinj
  refine ⟨w, hw, fun q hd => ?_⟩
  rw [← hq q hd, hermiteMeasure, integral_weightMeasure MeasurableSet.univ (by fun_prop)
      (fun x _ => (Real.exp_pos _).le)]

/-- The Christoffel–Darboux formula for the Hermite polynomials. -/
theorem hermite_christoffel_darboux {n : ℕ} (hn : n ≠ 0) {x y : ℝ}
    (hxy : x ≠ y) :
    ∑ k ∈ Finset.range n, (hermitePolyHR k).eval x * (hermitePolyHR k).eval y /
        (∫ t, (hermitePolyHR k).eval t ^ 2 ∂hermiteMeasure) =
      ((hermitePolyHR (n - 1)).leadingCoeff /
        ((hermitePolyHR n).leadingCoeff *
          ∫ t, (hermitePolyHR (n - 1)).eval t ^ 2 ∂hermiteMeasure)) *
        ((hermitePolyHR n).eval x * (hermitePolyHR (n - 1)).eval y -
          (hermitePolyHR (n - 1)).eval x * (hermitePolyHR n).eval y) / (x - y) :=
  christoffel_darboux (hermite_isOrthogonalPolynomials) hn hxy


/-! ### Completeness -/

namespace IsOrthogonalPolynomials

variable {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)

include h

/-- An orthogonal family spans all real polynomials. -/
theorem span_range_eq_top : Submodule.span ℝ (Set.range p) = ⊤ :=
  Polynomial.Sequence.span (⟨p, fun n => by
      rw [degree_eq_natDegree (h.ne_zero n), h.1 n]⟩ : Polynomial.Sequence ℝ) fun i =>
    isUnit_iff_ne_zero.mpr <| Polynomial.leadingCoeff_ne_zero.mpr <| h.ne_zero i

/-- **Completeness.** If `μ` has a finite exponential moment, a function in `L²(μ)` orthogonal
to every `p n` vanishes `μ`-almost everywhere (Beals–Wong Thm 4.1.5). -/
theorem ae_eq_zero_of_forall_integral_mul_eq_zero
    (hexp : ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|)) μ)
    {f : ℝ → ℂ} (hf : MemLp f 2 μ)
    (hcoeff : ∀ n, ∫ x, f x * (((p n).eval x : ℝ) : ℂ) ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hint (q : ℝ[X]) : Integrable (fun x => f x * ((q.eval x : ℝ) : ℂ)) μ := by
    simpa [Pi.mul_def] using
      hf.integrable_mul (TauCeti.memLp_two_algebraMap_eval (𝕜 := ℂ) hexp q)
  have hall (q : ℝ[X]) : ∫ x, f x * ((q.eval x : ℝ) : ℂ) ∂μ = 0 := by
    have hq : q ∈ Submodule.span ℝ (Set.range p) := by rw [h.span_range_eq_top]; trivial
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      exact hcoeff n
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [eval_add, Complex.ofReal_add, mul_add]
      rw [integral_add (hint x) (hint y), hx, hy, add_zero]
    | smul c x _ hx =>
      simp only [eval_smul, smul_eq_mul, Complex.ofReal_mul]
      have : (fun a => f a * ((c : ℂ) * ((x.eval a : ℝ) : ℂ))) =
          fun a => (c : ℂ) * (f a * ((x.eval a : ℝ) : ℂ)) := funext fun a => by ring
      rw [this, integral_const_mul, hx, mul_zero]
  refine TauCeti.ae_eq_zero_of_forall_moment_eq_zero_of_exists_integrable_exp hexp hf
    fun n => ?_
  have := hall (X ^ n)
  simpa [mul_comm] using this

end IsOrthogonalPolynomials

/-- An almost-everywhere statement for a weight measure, transferred to Lebesgue measure on the
set where the weight is positive. -/
theorem ae_of_ae_weightMeasure {I : Set ℝ} (hI : MeasurableSet I) {w : ℝ → ℝ} (hw : Measurable w)
    (hwpos : ∀ x ∈ I, 0 < w x) {P : ℝ → Prop} (h : ∀ᵐ x ∂weightMeasure I w, P x) :
    ∀ᵐ x : ℝ, x ∈ I → P x := by
  rw [weightMeasure, ae_withDensity_iff (by fun_prop), ae_restrict_iff' hI] at h
  refine h.mono fun x hx hxI => hx hxI ?_
  simpa using hwpos x hxI

theorem measurable_jacobiWeight (α β : ℝ) : Measurable (jacobiWeight α β) := by
  unfold jacobiWeight
  fun_prop

theorem measurable_laguerreWeight (α : ℝ) : Measurable (laguerreWeight α) := by
  unfold laguerreWeight
  fun_prop

/-- Completeness of the Jacobi polynomials in `L²((-1,1),(1-x)^α(1+x)^β dx)`. -/
@[dlmf 18.18.i]
theorem jacobiPolyP_complete {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {f : ℝ → ℂ}
    (hf : MemLp f 2 (jacobiMeasure α β))
    (hcoeff : ∀ n : ℕ, ∫ x, f x * jacobiPolyP α β n x ∂jacobiMeasure α β = 0) :
    ∀ᵐ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 → f x = 0 := by
  have hwpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < jacobiWeight α β x := fun x hx =>
    mul_pos (Real.rpow_pos_of_pos (by linarith [hx.2]) _)
      (Real.rpow_pos_of_pos (by linarith [hx.1]) _)
  have hexp : ∃ a : ℝ, 0 < a ∧
      Integrable (fun x : ℝ => Real.exp (a * |x|)) (jacobiMeasure α β) := by
    refine ⟨1, one_pos, ?_⟩
    rw [jacobiMeasure_eq_weightMeasure, integrable_weightMeasure_iff measurableSet_Ioo
      (measurable_jacobiWeight α β) fun x hx => (hwpos x hx).le]
    have := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).1
      ((intervalIntegrable_jacobiWeight hα hβ).continuousOn_mul
        (g := fun x : ℝ => Real.exp (1 * |x|)) (by fun_prop))
    exact this.congr_fun (fun x _ => mul_comm _ _) measurableSet_Ioo
  have h0 := (jacobi_isOrthogonalPolynomials hα hβ).ae_eq_zero_of_forall_integral_mul_eq_zero
    hexp hf fun n => by simpa only [eval_jacobiPolyPR hα] using hcoeff n
  rw [jacobiMeasure_eq_weightMeasure] at h0
  exact ae_of_ae_weightMeasure measurableSet_Ioo (measurable_jacobiWeight α β) hwpos h0

/-- Completeness of the Laguerre polynomials in `L²((0,∞), x^α e^{-x} dx)`. -/
theorem laguerrePolyL_complete {α : ℝ} (hα : -1 < α) {f : ℝ → ℂ}
    (hf : MemLp f 2 (laguerreMeasure α))
    (hcoeff : ∀ n : ℕ, ∫ x, f x * laguerrePolyL α n x ∂laguerreMeasure α = 0) :
    ∀ᵐ x : ℝ, x ∈ Ioi (0 : ℝ) → f x = 0 := by
  have hwpos : ∀ x ∈ Ioi (0 : ℝ), 0 < laguerreWeight α x := fun x hx =>
    mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)
  have hexp : ∃ a : ℝ, 0 < a ∧
      Integrable (fun x : ℝ => Real.exp (a * |x|)) (laguerreMeasure α) := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    rw [laguerreMeasure, integrable_weightMeasure_iff measurableSet_Ioi
      (measurable_laguerreWeight α) fun x hx => (hwpos x hx).le]
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow hα one_pos (b := 1 / 2)
      (by norm_num)).congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx : (0 : ℝ) < x := hx
    simp only [laguerreWeight, Real.rpow_one, abs_of_pos hx, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have h0 := (laguerre_isOrthogonalPolynomials hα).ae_eq_zero_of_forall_integral_mul_eq_zero
    hexp hf fun n => by simpa only [eval_laguerrePolyLR] using hcoeff n
  exact ae_of_ae_weightMeasure measurableSet_Ioi (measurable_laguerreWeight α) hwpos h0

/-- Completeness of the Hermite polynomials in `L²(ℝ, e^{-x²} dx)`. -/
theorem hermitePolyH_complete {f : ℝ → ℂ} (hf : MemLp f 2 hermiteMeasure)
    (hcoeff : ∀ n : ℕ, ∫ x, f x * (((hermitePolyHR n).eval x : ℝ) : ℂ) ∂hermiteMeasure = 0) :
    f =ᵐ[volume] 0 := by
  have hwpos : ∀ x ∈ (univ : Set ℝ), 0 < Real.exp (-(x ^ 2)) := fun x _ => Real.exp_pos _
  have hexp : ∃ a : ℝ, 0 < a ∧
      Integrable (fun x : ℝ => Real.exp (a * |x|)) hermiteMeasure := by
    refine ⟨1, one_pos, ?_⟩
    rw [hermiteMeasure, integrable_weightMeasure_iff MeasurableSet.univ (by fun_prop)
      fun x hx => (hwpos x hx).le, integrableOn_univ]
    refine ((integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul
      (Real.exp (1 / 2))).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
  have h0 := hermite_isOrthogonalPolynomials.ae_eq_zero_of_forall_integral_mul_eq_zero
    hexp hf hcoeff
  exact (ae_of_ae_weightMeasure MeasurableSet.univ (by fun_prop) hwpos h0).mono
    fun x hx => hx (mem_univ x)

/-! ### Rescaled families, Gegenbauer, Legendre and Chebyshev -/

/-- Multiplying each member by a nonzero constant preserves orthogonality. -/
theorem IsOrthogonalPolynomials.const_mul {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) {c : ℕ → ℝ} (hc : ∀ n, c n ≠ 0) :
    IsOrthogonalPolynomials μ fun n => C (c n) * p n := by
  refine ⟨fun n => by rw [natDegree_C_mul (hc n), h.1 n], fun n => ?_, fun n => ?_,
    fun m n hmn => ?_⟩
  · simp only [eval_mul, eval_C, mul_pow]
    exact (h.2.1 n).const_mul _
  · simp only [eval_mul, eval_C, mul_pow]
    rw [integral_const_mul]
    exact mul_pos (pow_pos (abs_pos.2 (hc n)) 2 |>.trans_eq (sq_abs _)) (h.2.2.1 n)
  · simp only [eval_mul, eval_C]
    have : (fun x => c m * (p m).eval x * (c n * (p n).eval x)) =
        fun x => (c m * c n) * ((p m).eval x * (p n).eval x) := funext fun x => by ring
    rw [this, integral_const_mul, h.2.2.2 m n hmn, mul_zero]

/-- The constant `(2λ)_n/(λ+1/2)_n` relating Gegenbauer and Jacobi polynomials. -/
def ultrasphCoeffR (lam : ℝ) (n : ℕ) : ℝ :=
  (ascPochhammer ℝ n).eval (2 * lam) / (ascPochhammer ℝ n).eval (lam + 1 / 2)

/-- The Gegenbauer polynomial `C_n^{(λ)}` as a real polynomial (DLMF 18.7.1). -/
def ultrasphPolyR (lam : ℝ) (n : ℕ) : ℝ[X] :=
  C (ultrasphCoeffR lam n) * jacobiPolyPR (lam - 1 / 2) (lam - 1 / 2) n

open DLMF.Hypergeometric in
theorem eval_map_ultrasphPolyR {lam : ℝ} (hlam : -1 / 2 < lam) (n : ℕ) (z : ℂ) :
    ((ultrasphPolyR lam n).map (algebraMap ℝ ℂ)).eval z = ultrasphPoly lam n z := by
  have hden : 0 < (ascPochhammer ℝ n).eval (lam + 1 / 2) := ascPochhammer_pos _ _ (by linarith)
  have hp : poch ((lam : ℂ) + 1 / 2) n ≠ 0 := by
    rw [show (lam : ℂ) + 1 / 2 = ((lam + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      poch_ofReal_eq_eval]
    exact_mod_cast hden.ne'
  rw [ultrasphPoly_eq_jacobiPolyP n z hp, ultrasphPolyR, Polynomial.map_mul, map_C, eval_mul,
    eval_C, eval_map_jacobiPolyPR (by linarith), ultrasphCoeffR,
    show (2 : ℂ) * lam = ((2 * lam : ℝ) : ℂ) by push_cast; ring,
    show (lam : ℂ) + 1 / 2 = ((lam + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
    poch_ofReal_eq_eval, poch_ofReal_eq_eval]
  rw [Complex.coe_algebraMap]
  push_cast
  ring

theorem eval_ultrasphPolyR {lam : ℝ} (hlam : -1 / 2 < lam) (n : ℕ) (x : ℝ) :
    (((ultrasphPolyR lam n).eval x : ℝ) : ℂ) = ultrasphPoly lam n x := by
  rw [← eval_map_ofReal, eval_map_ultrasphPolyR hlam]

theorem ultrasphCoeffR_ne_zero {lam : ℝ} (hlam : -1 / 2 < lam) (hlam0 : lam ≠ 0) (n : ℕ) :
    ultrasphCoeffR lam n ≠ 0 := by
  refine div_ne_zero (fun h0 => ?_) (ascPochhammer_pos _ _ (by linarith)).ne'
  obtain ⟨k, -, hk⟩ := (ascPochhammer_eval_eq_zero_iff n (2 * lam)).1 h0
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact hlam0 (by simpa using hk)
  · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    linarith

/-- The Gegenbauer polynomials are orthogonal for `(1-x²)^{λ-1/2} dx` when `λ > -1/2`,
`λ ≠ 0`. -/
theorem ultrasph_isOrthogonalPolynomials {lam : ℝ} (hlam : -1 / 2 < lam) (hlam0 : lam ≠ 0) :
    IsOrthogonalPolynomials (jacobiMeasure (lam - 1 / 2) (lam - 1 / 2)) (ultrasphPolyR lam) :=
  (jacobi_isOrthogonalPolynomials (by linarith) (by linarith)).const_mul
    (ultrasphCoeffR_ne_zero hlam hlam0)

/-- The zeros of `C_n^{(λ)}`, `λ > -1/2`, `λ ≠ 0`, are real, simple and lie in `(-1,1)`
(DLMF §18.16(i)). -/
theorem ultrasphPoly_zeros_Ioo {lam : ℝ} (hlam : -1 / 2 < lam) (hlam0 : lam ≠ 0) (n : ℕ) :
    ∃ x : Fin n → ℝ, StrictMono x ∧ (∀ i, x i ∈ Ioo (-1) 1) ∧
      ∀ z : ℂ, ultrasphPoly lam n z = 0 ↔ ∃ i, z = (x i : ℂ) := by
  have h := ultrasph_isOrthogonalPolynomials hlam hlam0
  obtain ⟨x, hx, hmem, hz⟩ := h.exists_strictMono_roots n
  have hae : ∀ᵐ x ∂jacobiMeasure (lam - 1 / 2) (lam - 1 / 2), x ∈ Ioo (-1 : ℝ) 1 :=
    ae_weightMeasure_mem measurableSet_Ioo _
  refine ⟨x, hx, fun i => ⟨h.lt_of_mem_roots (hae.mono fun x hx => hx.1) (hmem i),
    h.mem_roots_lt (hae.mono fun x hx => hx.2) (hmem i)⟩, fun z => ?_⟩
  rw [← hz z, eval_map_ultrasphPolyR hlam]

/-- Completeness of the Gegenbauer polynomials in `L²((-1,1),(1-x²)^{λ-1/2} dx)`. -/
theorem ultrasphPoly_complete {lam : ℝ} (hlam : -1 / 2 < lam) (hlam0 : lam ≠ 0) {f : ℝ → ℂ}
    (hf : MemLp f 2 (jacobiMeasure (lam - 1 / 2) (lam - 1 / 2)))
    (hcoeff : ∀ n : ℕ,
      ∫ x, f x * ultrasphPoly lam n x ∂jacobiMeasure (lam - 1 / 2) (lam - 1 / 2) = 0) :
    ∀ᵐ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 → f x = 0 := by
  refine jacobiPolyP_complete (by linarith) (by linarith) hf fun n => ?_
  have hc := ultrasphCoeffR_ne_zero hlam hlam0 n
  have h1 := hcoeff n
  have h2 : ∀ x : ℝ, f x * ultrasphPoly lam n x =
      (ultrasphCoeffR lam n : ℂ) * (f x * jacobiPolyP ((lam - 1 / 2 : ℝ) : ℂ)
        ((lam - 1 / 2 : ℝ) : ℂ) n x) := fun x => by
    rw [← eval_ultrasphPolyR hlam, ultrasphPolyR, eval_mul, eval_C,
      ← eval_jacobiPolyPR (by linarith)]
    push_cast
    ring
  simp_rw [h2, integral_const_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hc)

/-- The Legendre polynomials are orthogonal on `(-1,1)` for Lebesgue measure. -/
theorem legendre_isOrthogonalPolynomials :
    IsOrthogonalPolynomials (jacobiMeasure 0 0) (jacobiPolyPR 0 0) :=
  jacobi_isOrthogonalPolynomials (by norm_num) (by norm_num)

/-- The zeros of `P_n` are real, simple and lie in `(-1,1)`. -/
theorem legendrePolyP_zeros_Ioo (n : ℕ) :
    ∃ x : Fin n → ℝ, StrictMono x ∧ (∀ i, x i ∈ Ioo (-1) 1) ∧
      ∀ z : ℂ, legendrePolyP n z = 0 ↔ ∃ i, z = (x i : ℂ) := by
  simpa [legendrePolyP] using
    jacobiPolyP_zeros_Ioo (α := 0) (β := 0) (by norm_num) (by norm_num) n

/-- The Chebyshev polynomials `T_n` are orthogonal for `(1-x²)^{-1/2} dx`
(Mathlib's `Polynomial.Chebyshev.measureT`). -/
theorem chebyshevT_isOrthogonalPolynomials :
    IsOrthogonalPolynomials Polynomial.Chebyshev.measureT
      fun n : ℕ => Polynomial.Chebyshev.T ℝ n := by
  refine ⟨fun n => by simp [Polynomial.Chebyshev.natDegree_T], fun n => ?_, fun n => ?_,
    fun m n hmn => Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne hmn⟩
  · exact Polynomial.Chebyshev.integrable_measureT (by fun_prop)
  · simp_rw [sq]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [Nat.cast_zero, Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero]
      exact Real.pi_pos
    · rw [Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hn]
      positivity

/-- The zeros of `T_n` are real, simple and lie in `(-1,1)`. -/
theorem chebyshevT_zeros_Ioo (n : ℕ) :
    ∃ x : Fin n → ℝ, StrictMono x ∧ (∀ i, x i ∈ Ioo (-1) 1) ∧
      ∀ z : ℂ, (Polynomial.Chebyshev.T ℂ n).eval z = 0 ↔ ∃ i, z = (x i : ℂ) := by
  have h := chebyshevT_isOrthogonalPolynomials
  obtain ⟨x, hx, hmem, hz⟩ := h.exists_strictMono_roots n
  refine ⟨x, hx, fun i => ?_, fun z => ?_⟩
  · have h0 : (Polynomial.Chebyshev.T ℝ n).eval (x i) = 0 :=
      (mem_roots (h.ne_zero n)).1 (hmem i)
    have hlt : |x i| < 1 := by
      by_contra hge
      push Not at hge
      have := Polynomial.Chebyshev.one_le_abs_eval_T_real (n : ℤ) hge
      rw [h0, abs_zero] at this
      linarith
    exact ⟨(abs_lt.1 hlt).1, (abs_lt.1 hlt).2⟩
  rw [← hz z, Polynomial.Chebyshev.map_T]

end DLMF.OrthogonalPolynomials
