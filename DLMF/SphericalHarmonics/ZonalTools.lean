/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.SphericalHarmonics.Basic
public import DLMF.Legendre.IntegerTheory
public import TauCeti.Analysis.PDE.PoissonIntegral.Ball
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Comparison
public import DLMF.OrthogonalPolynomials.Legendre

/-!
# Zonal harmonics, Funk–Hecke and the spherical addition theorem

Tools for AAR §§9.6–9.7 in three dimensions:

* polynomial evaluation on Euclidean space is smooth, with derivatives given by `pderiv`, so a
  polynomial annihilated by `laplacianMv` is harmonic in Mathlib's sense;
* the Poisson-kernel expansion `(1 - r²)/(1 - 2rt + r²)^{3/2} = ∑ (2j+1) P_j(t) r^j`
  (from the Gegenbauer generating function and DLMF 18.9.7);
* the reproducing property `(2j+1) ∫ P_j(ξ·y) S(y) dσ(y) = 4π δ_{jk} S(ξ)` for harmonic
  homogeneous `S` of degree `k`, from the Poisson representation of the Tau Ceti contributors
  and uniqueness of power-series coefficients;
* the Funk–Hecke formula, by Legendre expansion of polynomials and Weierstrass approximation;
* the addition theorem, by showing that the defect `y ↦ c P_k(ξ·y) - ∑ S_m(ξ) S_m(y)` has
  squared norm `c - ∑ S_m(ξ)²`, whose integral over the sphere vanishes. This avoids a separate
  dimension count for harmonic polynomials.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Metric Set Filter InnerProductSpace
open scoped Real Topology
open DLMF.OrthogonalPolynomials

namespace DLMF.SphericalHarmonics

/-- `(2n+1) P_n = C_n^{(3/2)} - C_{n-2}^{(3/2)}` (DLMF 18.9.7 at `λ = 1/2`). -/
theorem zonal_two_mul_add_one (n : ℕ) (x : ℂ) :
    (2 * n + 1 : ℂ) * legendrePolyP n x =
      ultrasphPoly (3 / 2) n x - (if n < 2 then 0 else ultrasphPoly (3 / 2) (n - 2) x) := by
  rw [legendre_eq_ultrasphPoly]
  rcases n with _ | _ | n
  · simp
  · simp only [show (1 : ℕ) < 2 by norm_num, ite_true, sub_zero]
    rw [ultrasphPoly_one_eq (by norm_num), ultrasphPoly_one_eq (by norm_num)]
    ring
  · have h := ultrasphPoly_raise_parameter (lam := 1 / 2) (by norm_num) n x
    rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num] at h
    simp only [show ¬ (n + 2 < 2) by omega, ite_false, show n + 2 - 2 = n by omega]
    push_cast
    linear_combination 2 * h

/-- The Poisson-kernel expansion `(1 - r²)/(1 - 2rt + r²)^{3/2} = ∑ (2j+1) P_j(t) r^j`. -/
theorem zonal_kernel_hasSum {t : ℝ} (ht : |t| ≤ 1) {r : ℝ} (hr : |r| < 1) :
    HasSum (fun j : ℕ => (2 * j + 1 : ℂ) * legendrePolyP j t * (r : ℂ) ^ j)
      (((1 - r ^ 2) / (1 - 2 * r * t + r ^ 2) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
  have hz : ‖(r : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hG := ultrasphPoly_generating_function (lam := 3 / 2) (by norm_num) ht hz
  have hpos : 0 < 1 - 2 * r * t + r ^ 2 := by
    have h1 : |r * t| < 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg r, abs_nonneg t]
    nlinarith [abs_lt.mp h1, sq_nonneg (r - t), sq_nonneg r, abs_le.mp ht]
  have hval : (1 - 2 * (t : ℂ) * r + (r : ℂ) ^ 2) ^ (-(3 / 2 : ℂ)) =
      (((1 - 2 * r * t + r ^ 2) ^ (3 / 2 : ℝ))⁻¹ : ℝ) := by
    rw [show (1 - 2 * (t : ℂ) * r + (r : ℂ) ^ 2) = ((1 - 2 * r * t + r ^ 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.cpow_neg, ← Real.rpow_neg hpos.le,
      Complex.ofReal_cpow hpos.le]
    push_cast
    rw [Complex.cpow_neg]
  rw [hval] at hG
  -- the shifted series
  have hG2 : HasSum (fun n : ℕ => (if n < 2 then 0 else ultrasphPoly (3 / 2) (n - 2) (t : ℂ)) *
      (r : ℂ) ^ n) ((r : ℂ) ^ 2 * (((1 - 2 * r * t + r ^ 2) ^ (3 / 2 : ℝ))⁻¹ : ℝ)) := by
    rw [← hasSum_nat_add_iff' 2]
    simp only [show ∀ n : ℕ, ¬ (n + 2 < 2) from fun n => by omega, ite_false,
      Nat.add_sub_cancel, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      show (0 : ℕ) < 2 by norm_num, show (1 : ℕ) < 2 by norm_num, ite_true, zero_mul,
      add_zero, sub_zero]
    have := hG.mul_left ((r : ℂ) ^ 2)
    refine this.congr_fun fun n => ?_
    ring
  have h := hG.sub hG2
  convert h using 1
  · funext j
    rw [zonal_two_mul_add_one]; ring
  · push_cast
    rw [div_eq_mul_inv]; ring

/-- Uniqueness of coefficients: a power series with coefficients of linear growth that vanishes
on `(-1/2, 1/2)` has zero coefficients. -/
theorem zonal_coeff_eq_zero (b : ℕ → ℂ) (C : ℝ) (hb : ∀ n, ‖b n‖ ≤ C * (n + 1))
    (h : ∀ r : ℝ, |r| < 1 / 2 → HasSum (fun n => (r : ℂ) ^ n * b n) 0) (n : ℕ) : b n = 0 := by
  let p : FormalMultilinearSeries ℝ ℝ ℂ :=
    fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (b n)
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hb 0); simpa using this
  have hrad : ((1 / 2 : NNReal) : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_bound C fun n => ?_
    simp only [p, ContinuousMultilinearMap.norm_mkPiRing, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat]
    have h2 : ((n : ℝ) + 1) ≤ 2 ^ n := by
      have := Nat.lt_two_pow_self (n := n)
      exact_mod_cast this
    calc ‖b n‖ * (1 / 2 : ℝ) ^ n ≤ C * (n + 1) * (1 / 2) ^ n := by gcongr; exact hb n
      _ ≤ C * 2 ^ n * (1 / 2) ^ n := by gcongr
      _ = C := by rw [mul_assoc, ← mul_pow]; norm_num
  have hpos : 0 < p.radius := lt_of_lt_of_le (by norm_num) hrad
  have hp : HasFPowerSeriesAt p.sum p 0 := (p.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt
  have hzero : p.sum =ᶠ[𝓝 0] 0 := by
    have : Metric.ball (0 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [this] with r hr
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hr
    simp only [FormalMultilinearSeries.sum, p, ContinuousMultilinearMap.mkPiRing_apply,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, Pi.zero_apply]
    have := (h r hr).tsum_eq
    rw [← this]
    congr 1; funext n
    rw [Complex.real_smul]; push_cast; rfl
  have h0 := hp.eq_zero_of_eventually hzero
  have := congrArg (fun q : FormalMultilinearSeries ℝ ℝ ℂ => q n (fun _ => 1)) h0
  simpa [p] using this

section Bridge

open MvPolynomial Laplacian

variable {n : ℕ}

/-- Polynomial evaluation on Euclidean space is smooth. -/
theorem zonal_contDiff (P : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ ⊤ (fun z : EuclideanSpace ℝ (Fin n) => eval (fun i => z i) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).contDiff

/-- The derivative of a polynomial on Euclidean space, in terms of `pderiv`. -/
theorem zonal_hasFDerivAt (P : MvPolynomial (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => eval (fun i => z i) P)
      (∑ j, eval (fun i => y i) (pderiv j P) •
        (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) y := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const a y
  | add p q hp hq =>
    convert hp.add hq using 1
    · funext z; simp
    · simp [add_smul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have h := hp.mul (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt
    convert h using 1
    · funext z; simp
    · ext v
      simp [Pi.single_apply, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb; simp [Ne.symm hb]
        · simp
      · refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- Directional derivatives along coordinate vectors are evaluations of `pderiv`. -/
theorem zonal_fderiv_single (P : MvPolynomial (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n))
    (i : Fin n) :
    fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => eval (fun i => z i) P) y
      (EuclideanSpace.single i 1) = eval (fun i => y i) (pderiv i P) := by
  classical
  rw [(zonal_hasFDerivAt P y).fderiv]
  simp

/-- The Laplacian of a polynomial function is the evaluation of `laplacianMv`. -/
theorem zonal_laplacian_eval (P : MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Δ (fun z : EuclideanSpace ℝ (Fin n) => eval (fun i => z i) P) x =
      eval (fun i => x i) (laplacianMv P) := by
  have hd : DifferentiableAt ℝ
      (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => eval (fun i => z i) P)) x := by
    have : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => eval (fun i => z i) P) = fun y =>
        ∑ j, eval (fun i => y i) (pderiv j P) •
          (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
      funext fun y => (zonal_hasFDerivAt P y).fderiv
    rw [this]
    refine DifferentiableAt.fun_sum fun j _ => ?_
    exact (((zonal_contDiff (pderiv j P)).differentiable (by simp)) x).smul_const _
  rw [TauCeti.laplacian_eq_sum_fderiv_fderiv_apply (EuclideanSpace.basisFun (Fin n) ℝ) hd]
  simp only [EuclideanSpace.basisFun_apply]
  have : ∀ j, (fun y => fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => eval (fun i => z i) P) y
      (EuclideanSpace.single j 1)) = fun z => eval (fun i => z i) (pderiv j P) :=
    fun j => funext fun y => zonal_fderiv_single P y j
  simp only [zonal_fderiv_single, laplacianMv, map_sum]

/-- Harmonic polynomials give harmonic functions on Euclidean space. -/
theorem zonal_harmonicOnNhd {P : MvPolynomial (Fin n) ℝ} (hP : laplacianMv P = 0)
    (s : Set (EuclideanSpace ℝ (Fin n))) :
    HarmonicOnNhd (fun z : EuclideanSpace ℝ (Fin n) => eval (fun i => z i) P) s := by
  intro x _
  refine ⟨((zonal_contDiff P).of_le (by simp)).contDiffAt, Filter.Eventually.of_forall
    fun y => ?_⟩
  rw [zonal_laplacian_eval, hP, map_zero]
  rfl

end Bridge

section Reproduce

open MvPolynomial

/-- Scaling the variables of a homogeneous polynomial; adapted from the Tau Ceti contributors'
`MvPolynomial.IsHomogeneous.eval₂_const_mul`. -/
theorem zonal_eval_smul {n m : ℕ} {P : MvPolynomial (Fin n) ℝ} (hP : P.IsHomogeneous m)
    (r : ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    eval (fun j => (r • u) j) P = r ^ m * eval (fun j => u j) P := by
  exact hP.eval₂_const_mul (RingHom.id ℝ) (fun j => u j) r

/-- The Poisson extension of harmonic boundary data is the original function; adapted from the
Tau Ceti contributors' unit-ball Dirichlet theorem. -/
theorem zonal_poisson {n : ℕ} (hn : n ≠ 0)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : HarmonicOnNhd f (ball 0 1)) (hcont : ContinuousOn f (closedBall 0 1))
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1) :
    TauCeti.ballPoissonIntegral (fun y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => f y) x =
      f x := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  let g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ := fun y => f y
  have hg : Continuous g := (hcont.mono sphere_subset_closedBall).comp_continuous
    continuous_subtype_val (fun y => y.2)
  have hgi : Integrable g volume.toSphere :=
    hg.integrable_of_hasCompactSupport (.of_compactSpace g)
  let u : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
    if hz : z ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 then g ⟨z, hz⟩
    else TauCeti.ballPoissonIntegral g z
  have hball : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, z ∉ sphere 0 1 := fun z hz hs =>
    (mem_ball_zero_iff.mp hz).ne (mem_sphere_zero_iff_norm.mp hs)
  have hu : EqOn u (TauCeti.ballPoissonIntegral g) (ball 0 1) :=
    fun z hz => dite_eq_right (hball z hz)
  have hP : HarmonicOnNhd (TauCeti.ballPoissonIntegral g) (ball 0 1) :=
    (TauCeti.harmonicOnNhd_ballPoissonIntegral hgi).mono hball
  have huP : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      u =ᶠ[𝓝 z] TauCeti.ballPoissonIntegral g :=
    fun z hz => Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) hu
  have hhu : HarmonicOnNhd u (ball 0 1) :=
    fun z hz => (harmonicAt_congr_nhds (huP z hz)).2 (hP z hz)
  have hcu : ContinuousOn u (closedBall 0 1) := by
    rw [← ball_union_sphere]
    intro z hz
    rcases hz with hz | hz
    · exact ((hP z hz).1.continuousAt.congr (huP z hz).symm).continuousWithinAt
    · have huz : u z = g ⟨z, hz⟩ := dite_eq_left hz
      refine continuousWithinAt_union.2 ⟨?_, ?_⟩
      · rw [ContinuousWithinAt, huz]
        exact (TauCeti.tendsto_ballPoissonIntegral hg ⟨z, hz⟩).congr'
          (Filter.eventually_of_mem self_mem_nhdsWithin fun y hy => (hu hy).symm)
      · have hres : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1).domRestrict u = g :=
          funext fun y => dite_eq_left y.2
        exact (continuousOn_iff_continuous_domRestrict.2 (hres ▸ hg)) z hz
  have he : EqOn u f (closedBall 0 1) :=
    TauCeti.eqOn_of_harmonicOnNhd_of_eqOn_frontier (isCompact_closedBall _ _) hcu hcont
      (by simpa only [interior_closedBall _ one_ne_zero] using hhu)
      (by simpa only [interior_closedBall _ one_ne_zero] using hf) (by
        intro z hz
        have hz' : z ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
          simpa only [frontier_closedBall _ one_ne_zero] using hz
        exact dite_eq_left hz')
  exact (hu (mem_ball_zero_iff.mpr hx)).symm.trans
    (he (mem_closedBall_zero_iff.mpr hx.le))

/-- The coordinate dot product is the Euclidean inner product. -/
theorem zonal_inner {n : ℕ} (ξ y : EuclideanSpace ℝ (Fin n)) : ∑ i, ξ i * y i = inner ℝ ξ y := by
  simp [PiLp.inner_apply, mul_comm]

/-- The area of the unit sphere in `ℝ³`. -/
theorem zonal_area :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere.real univ = 4 * π := by
  have := sphericalHarmonicInner_one_three
  simpa [sphericalHarmonicInner] using this

/-- On the unit sphere, `|ξ · y| ≤ 1`. -/
theorem zonal_abs_dot_le (ξ y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    |∑ i, ξ.val i * y.val i| ≤ 1 := by
  rw [zonal_inner]
  have := abs_real_inner_le_norm ξ.val y.val
  rwa [norm_eq_of_mem_sphere ξ, norm_eq_of_mem_sphere y, mul_one] at this

/-- The kernel identity on the sphere: `(1 - r²)/(1 - 2rt + r²)^{3/2}` is the sphere area times the
Tau Ceti Poisson kernel at `r ξ`. -/
theorem zonal_kernel_eq (ξ y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {r : ℝ} (hr : |r| < 1) :
    (1 - r ^ 2) / (1 - 2 * r * (∑ i, ξ.val i * y.val i) + r ^ 2) ^ (3 / 2 : ℝ) =
      (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere.real univ *
        TauCeti.ballPoissonKernel 3 (r • ξ.val) y.val := by
  rw [zonal_inner, Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin,
    TauCeti.ballPoissonKernel_def]
  have hξ := norm_eq_of_mem_sphere ξ
  have hy := norm_eq_of_mem_sphere y
  have hx : ‖r • ξ.val‖ = |r| := by rw [norm_smul, hξ, mul_one, Real.norm_eq_abs]
  have hd : ‖r • ξ.val - y.val‖ ^ 2 = 1 - 2 * r * inner ℝ ξ.val y.val + r ^ 2 := by
    rw [norm_sub_sq_real, hx, hy, real_inner_smul_left, sq_abs]; ring
  have hpow : (1 - 2 * r * inner ℝ ξ.val y.val + r ^ 2) ^ (3 / 2 : ℝ) =
      ‖r • ξ.val - y.val‖ ^ 3 := by
    rw [← hd, ← Real.rpow_natCast (‖r • ξ.val - y.val‖) 2, ← Real.rpow_mul (norm_nonneg _),
      ← Real.rpow_natCast]
    norm_num
  rw [hpow, hx, sq_abs]
  have hp := TauCeti.volume_real_unitBall_pos 3
  have hne : ‖r • ξ.val - y.val‖ ≠ 0 := by
    intro h0
    have : (1 : ℝ) - 2 * r * inner ℝ ξ.val y.val + r ^ 2 = 0 := by rw [← hd, h0]; ring
    have hi : |inner ℝ ξ.val y.val| ≤ 1 := by
      have := abs_real_inner_le_norm ξ.val y.val; rwa [hξ, hy, mul_one] at this
    have h1 : |r * inner ℝ ξ.val y.val| < 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg r, abs_nonneg (inner ℝ ξ.val y.val)]
    nlinarith [abs_lt.mp h1, sq_nonneg (r - inner ℝ ξ.val y.val), sq_nonneg r,
      abs_le.mp hi, abs_lt.mp hr]
  push_cast
  field_simp

/-- **Reproducing property of zonal Legendre kernels** (AAR §9.6): for a harmonic homogeneous
polynomial `S` of degree `k` in three variables,
`(2j+1) ∫ P_j(ξ·y) S(y) dσ(y) = 4π δ_{jk} S(ξ)`. Proved from the Poisson representation and the
expansion of the Poisson kernel in Legendre polynomials. -/
theorem zonal_reproduce {k : ℕ} {S : MvPolynomial (Fin 3) ℝ} (hS : IsHarmonicHomogeneous k S)
    (ξ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (j : ℕ) :
    (2 * j + 1 : ℂ) * (∫ y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      legendrePolyP j (∑ i, ξ.val i * y.val i : ℝ) * (eval (fun i => y.val i) S : ℂ)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) =
      if j = k then 4 * π * (eval (fun i => ξ.val i) S : ℂ) else 0 := by
  set σ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere with hσ
  set ev : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => eval (fun i => z i) S with hev
  set t : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ := fun y => ∑ i, ξ.val i * y.val i
    with htdef
  have ht : ∀ y, |t y| ≤ 1 := fun y => zonal_abs_dot_le ξ y
  set G : ℕ → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℂ :=
    fun j y => legendrePolyP j (t y) * (ev y : ℂ) with hGdef
  have hev_cont : Continuous ev := (zonal_contDiff S).continuous
  have ht_cont : Continuous t := by
    simp only [htdef]; fun_prop
  have hL (j : ℕ) : Continuous fun x : ℝ => legendrePolyP j x := by
    simp_rw [DLMF.Legendre.legendrePolyP_eq_eval]
    exact (Polynomial.continuous _).comp continuous_ofReal
  have hG_cont : ∀ j, Continuous (G j) := fun j =>
    ((hL j).comp ht_cont).mul (continuous_ofReal.comp (hev_cont.comp continuous_subtype_val))
  have hG_int : ∀ j, Integrable (G j) σ := fun j =>
    (hG_cont j).integrable_of_hasCompactSupport (.of_compactSpace _)
  obtain ⟨M, hM⟩ :=
    (isCompact_univ (X := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).exists_bound_of_continuousOn
    (f := fun y => (ev y : ℂ))
    (continuous_ofReal.comp (hev_cont.comp continuous_subtype_val)).continuousOn
  have hGb : ∀ j y, ‖G j y‖ ≤ M := by
    intro j y
    rw [norm_mul]
    calc ‖legendrePolyP j (t y)‖ * ‖(ev y : ℂ)‖ ≤ 1 * M := by
          gcongr
          · exact norm_legendrePolyP_le_one j (ht y)
          · exact hM y (mem_univ _)
      _ = M := one_mul M
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hGb 0 ⟨EuclideanSpace.single 0 1, by simp⟩)
  set A := σ.real univ with hA
  have hA4 : A = 4 * π := zonal_area
  have hA0 : 0 ≤ A := by rw [hA4]; positivity
  have hGi : ∀ j, ∫ y, ‖G j y‖ ∂σ ≤ M * A := by
    intro j
    calc ∫ y, ‖G j y‖ ∂σ ≤ ∫ _y, M ∂σ :=
          integral_mono (hG_int j).norm (integrable_const M) (hGb j)
      _ = M * A := by rw [integral_const, smul_eq_mul, mul_comm]
  set c : ℕ → ℂ := fun j => (2 * j + 1 : ℂ) * ∫ y, G j y ∂σ with hcdef
  have hc : ∀ j, ‖c j‖ ≤ (2 * j + 1) * (M * A) := by
    intro j
    simp only [hcdef, norm_mul]
    have h2 : ‖(2 * j + 1 : ℂ)‖ = 2 * j + 1 := by
      rw [show (2 * j + 1 : ℂ) = ((2 * j + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    rw [h2]
    gcongr
    exact (norm_integral_le_integral_norm _).trans (hGi j)
  -- the generating identity for small `r`
  have key : ∀ r : ℝ, |r| < 1 / 2 →
      HasSum (fun j => (r : ℂ) ^ j * c j) (4 * π * (r : ℂ) ^ k * ev ξ) := by
    intro r hr
    have hr1 : |r| < 1 := by linarith
    set F : ℕ → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℂ :=
      fun j y => ((2 * j + 1 : ℂ) * (r : ℂ) ^ j) * G j y with hF
    have hF_int : ∀ j, Integrable (F j) σ := fun j => (hG_int j).const_mul _
    have hF_norm : ∀ j, ∫ y, ‖F j y‖ ∂σ ≤ (2 * j + 1) * |r| ^ j * (M * A) := by
      intro j
      have : ∀ y, ‖F j y‖ = ((2 * j + 1) * |r| ^ j) * ‖G j y‖ := by
        intro y
        simp only [hF, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        congr 1
        rw [show (2 * j + 1 : ℂ) = ((2 * j + 1 : ℕ) : ℂ) by push_cast; ring,
          Complex.norm_natCast]
        push_cast; ring
      simp_rw [this]
      rw [integral_const_mul]
      have := hGi j
      have h0 : 0 ≤ (2 * (j : ℝ) + 1) * |r| ^ j := by positivity
      calc (2 * (j : ℝ) + 1) * |r| ^ j * ∫ y, ‖G j y‖ ∂σ
          ≤ (2 * j + 1) * |r| ^ j * (M * A) := by gcongr
        _ = _ := rfl
    have hρ0 : 0 ≤ |r| := abs_nonneg r
    have hsumm : Summable fun j : ℕ => (2 * j + 1) * |r| ^ j * (M * A) := by
      have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1
        (by rwa [Real.norm_eq_abs, abs_abs])).mul_left (2 * (M * A))
      have h2 := (summable_geometric_of_lt_one hρ0 hr1).mul_left (M * A)
      refine (h1.add h2).congr fun j => ?_
      simp only [pow_one]; ring
    have hF_sum : Summable fun j => ∫ y, ‖F j y‖ ∂σ :=
      Summable.of_nonneg_of_le (fun j => integral_nonneg fun y => norm_nonneg _) hF_norm hsumm
    have hI := hasSum_integral_of_summable_integral_norm hF_int hF_sum
    -- pointwise sum
    have hpt : ∀ y, ∑' j, F j y =
        (((1 - r ^ 2) / (1 - 2 * r * t y + r ^ 2) ^ (3 / 2 : ℝ) * ev y : ℝ) : ℂ) := by
      intro y
      have h := (zonal_kernel_hasSum (ht y) hr1).mul_right (ev y : ℂ)
      rw [Complex.ofReal_mul, ← h.tsum_eq]
      congr 1; funext j
      simp only [hF, hGdef]; ring
    simp_rw [hpt] at hI
    rw [integral_complex_ofReal] at hI
    have hker : ∀ y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (1 - r ^ 2) / (1 - 2 * r * t y + r ^ 2) ^ (3 / 2 : ℝ) * ev y =
          A * (TauCeti.ballPoissonKernel 3 (r • ξ.val) y.val * ev y) := by
      intro y
      rw [zonal_kernel_eq ξ y hr1, mul_assoc]
    simp_rw [hker] at hI
    rw [integral_const_mul, ← TauCeti.ballPoissonIntegral_def] at hI
    have hrx : ‖r • ξ.val‖ < 1 := by
      rw [norm_smul, norm_eq_of_mem_sphere ξ, mul_one, Real.norm_eq_abs]; exact hr1
    have hpo := zonal_poisson (f := ev) (by norm_num)
      (zonal_harmonicOnNhd hS.2 _) hev_cont.continuousOn hrx
    rw [hpo] at hI
    have hsm : ev (r • ξ.val) = r ^ k * ev ξ := zonal_eval_smul hS.1 r ξ.val
    rw [hsm, hA4] at hI
    convert hI using 1
    · funext j
      simp only [hF, hcdef]
      rw [integral_const_mul]; ring
    · push_cast; ring
  -- coefficient extraction
  set b : ℕ → ℂ := fun j => c j - if j = k then 4 * π * (ev ξ : ℂ) else 0 with hbdef
  have hb := zonal_coeff_eq_zero b (2 * (M * A) + 4 * π * ‖(ev ξ : ℂ)‖) (fun j => by
    simp only [hbdef]
    refine (norm_sub_le _ _).trans ?_
    have h1 := hc j
    have h2 : ‖(if j = k then 4 * π * (ev ξ : ℂ) else 0)‖ ≤ 4 * π * ‖(ev ξ : ℂ)‖ := by
      split_ifs
      · rw [norm_mul, show ‖(4 * π : ℂ)‖ = 4 * π by
          rw [show (4 * π : ℂ) = ((4 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (by positivity)]]
      · simp only [norm_zero]; positivity
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hMA : 0 ≤ M * A := mul_nonneg hM0 hA0
    have he : 0 ≤ 4 * π * ‖(ev ξ : ℂ)‖ := by positivity
    nlinarith) (fun r hr => by
      have h1 := key r hr
      have h2 : HasSum (fun j => (r : ℂ) ^ j * (if j = k then 4 * π * (ev ξ : ℂ) else 0))
          (4 * π * (r : ℂ) ^ k * ev ξ) := by
        have := hasSum_ite_eq k ((r : ℂ) ^ k * (4 * π * (ev ξ : ℂ)))
        convert this using 1
        · funext j; split_ifs with h
          · subst h; rfl
          · simp
        · ring
      have := h1.sub h2
      rw [sub_self] at this
      refine this.congr_fun fun j => ?_
      simp only [hbdef]; ring) j
  simp only [hbdef, sub_eq_zero] at hb
  exact hb

end Reproduce

section FunkHecke

open MvPolynomial

/-- The complexified real Legendre polynomial. -/
theorem zonal_natDegree_legendre (j : ℕ) :
    ((DLMF.Legendre.legendrePolyR j).map Complex.ofRealHom).natDegree = j := by
  rw [Polynomial.natDegree_map, DLMF.Legendre.legendrePolyR, Polynomial.natDegree_comp,
    Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℝ)),
    Polynomial.natDegree_shiftedLegendre]
  have : (Polynomial.C (1 / 2 : ℝ) * (1 - Polynomial.X)).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul (by norm_num),
      show (1 - Polynomial.X : Polynomial ℝ) = -(Polynomial.X - Polynomial.C 1) by simp,
      Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  rw [this, mul_one]

/-- Induction principle: a property of complex polynomials that is additive and holds for all
multiples of Legendre polynomials holds for all polynomials. -/
theorem zonal_legendre_induction (Φ : Polynomial ℂ → Prop)
    (hadd : ∀ p q, Φ p → Φ q → Φ (p + q))
    (hbase : ∀ (a : ℂ) (j : ℕ),
      Φ (Polynomial.C a * (DLMF.Legendre.legendrePolyR j).map Complex.ofRealHom))
    (Q : Polynomial ℂ) : Φ Q := by
  induction h : Q.natDegree using Nat.strong_induction_on generalizing Q with
  | _ d ih =>
    set L := (DLMF.Legendre.legendrePolyR d).map Complex.ofRealHom with hL
    have hLd : L.natDegree = d := zonal_natDegree_legendre d
    have hL0 : L ≠ 0 := by
      intro h0
      have hP := DLMF.Legendre.legendrePolyP_eq_eval d 1
      rw [← hL, h0, Polynomial.eval_zero] at hP
      have : DLMF.OrthogonalPolynomials.legendrePolyP d 1 = 1 := by
        simp [DLMF.OrthogonalPolynomials.legendrePolyP, DLMF.OrthogonalPolynomials.jacobiPolyP,
          Nat.factorial_ne_zero]
      rw [this] at hP; exact one_ne_zero hP
    set c := Q.leadingCoeff / L.leadingCoeff with hc
    set R := Q - Polynomial.C c * L with hR
    have hQ : Q = Polynomial.C c * L + R := by rw [hR]; ring
    rw [hQ]
    refine hadd _ _ (hbase c d) ?_
    by_cases hR0 : R = 0
    · rw [hR0]
      have := hbase 0 0
      simpa using this
    have hlt : R.natDegree < d := by
      by_cases hQ0 : Q = 0
      · exfalso; apply hR0; rw [hR, hQ0]
        have : c = 0 := by rw [hc, hQ0]; simp
        simp [this]
      rcases Nat.eq_zero_or_pos d with hd | hd
      · exfalso; apply hR0
        rw [hR, hc]
        have hQc : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (h ▸ hd)
        have hLc : L = Polynomial.C (L.coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero (hLd ▸ hd)
        have hl0 : L.coeff 0 ≠ 0 := by
          intro h0; apply hL0; rw [hLc, h0, map_zero]
        rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, h, hLd, hd]
        conv_lhs => rw [hQc, hLc]
        simp only [Polynomial.coeff_C_zero]
        rw [← map_mul, ← map_sub, div_mul_cancel₀ _ hl0, sub_self, map_zero]
      have hdeg : (Polynomial.C c * L).degree = Q.degree := by
        rw [Polynomial.degree_C_mul, Polynomial.degree_eq_natDegree hL0,
          Polynomial.degree_eq_natDegree hQ0, hLd, h]
        rw [hc]
        exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hQ0)
          (Polynomial.leadingCoeff_ne_zero.mpr hL0)
      have hlc : (Polynomial.C c * L).leadingCoeff = Q.leadingCoeff := by
        rw [Polynomial.leadingCoeff_C_mul_of_isUnit, hc,
          div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hL0)]
        rw [hc]
        exact (div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hQ0)
          (Polynomial.leadingCoeff_ne_zero.mpr hL0)).isUnit
      have hdlt : R.degree < Q.degree :=
        Polynomial.degree_sub_lt_left hdeg.symm hQ0 hlc.symm
      have := Polynomial.natDegree_lt_natDegree hR0 hdlt
      rwa [h] at this
    exact ih _ hlt R rfl

/-- **Funk–Hecke formula** in three dimensions (AAR Theorem 9.7.1), proved from the reproducing
property of the zonal kernels, the Legendre expansion of polynomials and Weierstrass
approximation. -/
theorem zonal_funk_hecke {k : ℕ} {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (-1) 1))
    (S : MvPolynomial (Fin 3) ℝ) (hS : IsHarmonicHomogeneous k S)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (∫ y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      f (∑ i, x.val i * y.val i) * (MvPolynomial.eval (fun i => y.val i) S : ℂ)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) =
      (2 * π : ℂ) * (∫ t : ℝ in (-1 : ℝ)..1, f t * legendrePolyP k t) *
        (MvPolynomial.eval (fun i => x.val i) S : ℂ) := by
  set σ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere with hσ
  set ev : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => eval (fun i => z i) S with hev
  set t : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ := fun y => ∑ i, x.val i * y.val i
    with htdef
  have ht : ∀ y, t y ∈ Icc (-1 : ℝ) 1 := fun y => abs_le.mp (zonal_abs_dot_le x y)
  have hev_cont : Continuous ev := (zonal_contDiff S).continuous
  have ht_cont : Continuous t := by simp only [htdef]; fun_prop
  have hevc : Continuous fun y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 => (ev y : ℂ) :=
    continuous_ofReal.comp (hev_cont.comp continuous_subtype_val)
  have hL (j : ℕ) : Continuous fun s : ℝ => legendrePolyP j s := by
    simp_rw [DLMF.Legendre.legendrePolyP_eq_eval]
    exact (Polynomial.continuous _).comp continuous_ofReal
  obtain ⟨M, hM⟩ :=
    (isCompact_univ (X := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).exists_bound_of_continuousOn
    (f := fun y => (ev y : ℂ)) hevc.continuousOn
  set D : (ℝ → ℂ) → ℂ := fun g => (∫ y, g (t y) * (ev y : ℂ) ∂σ) -
    (2 * π : ℂ) * (∫ s : ℝ in (-1 : ℝ)..1, g s * legendrePolyP k s) * (ev x : ℂ) with hD
  have hint1 : ∀ g : ℝ → ℂ, ContinuousOn g (Icc (-1) 1) →
      Integrable (fun y => g (t y) * (ev y : ℂ)) σ := by
    intro g hg
    have : Continuous fun y => g (t y) * (ev y : ℂ) :=
      (hg.comp_continuous ht_cont ht).mul hevc
    exact this.integrable_of_hasCompactSupport (.of_compactSpace _)
  have hint2 : ∀ g : ℝ → ℂ, ContinuousOn g (Icc (-1) 1) →
      IntervalIntegrable (fun s => g s * legendrePolyP k s) volume (-1) 1 := by
    intro g hg
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    exact hg.mul (hL k).continuousOn
  have hDsub : ∀ g₁ g₂ : ℝ → ℂ, ContinuousOn g₁ (Icc (-1) 1) → ContinuousOn g₂ (Icc (-1) 1) →
      D (fun s => g₁ s - g₂ s) = D g₁ - D g₂ := by
    intro g₁ g₂ h₁ h₂
    simp only [hD, sub_mul]
    rw [integral_sub (hint1 g₁ h₁) (hint1 g₂ h₂),
      intervalIntegral.integral_sub (hint2 g₁ h₁) (hint2 g₂ h₂)]
    ring
  have hDadd : ∀ g₁ g₂ : ℝ → ℂ, ContinuousOn g₁ (Icc (-1) 1) → ContinuousOn g₂ (Icc (-1) 1) →
      D (fun s => g₁ s + g₂ s) = D g₁ + D g₂ := by
    intro g₁ g₂ h₁ h₂
    simp only [hD, add_mul]
    rw [integral_add (hint1 g₁ h₁) (hint1 g₂ h₂),
      intervalIntegral.integral_add (hint2 g₁ h₁) (hint2 g₂ h₂)]
    ring
  have hDbound : ∀ g : ℝ → ℂ, ∀ ε : ℝ, (∀ s ∈ Icc (-1 : ℝ) 1, ‖g s‖ ≤ ε) →
      ‖D g‖ ≤ ε * M * σ.real univ + 2 * π * (ε * 2) * ‖(ev x : ℂ)‖ := by
    intro g ε hg
    simp only [hD]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => ?_)).trans
        (le_of_eq rfl)
      rw [norm_mul]
      exact mul_le_mul (hg _ (ht y)) (hM y (mem_univ _)) (norm_nonneg _)
        ((norm_nonneg _).trans (hg _ (ht y)))
    · rw [norm_mul, norm_mul]
      have h2pi : ‖(2 * π : ℂ)‖ = 2 * π := by
        rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [h2pi]
      gcongr
      have hb : ∀ s ∈ Set.uIoc (-1 : ℝ) 1, ‖g s * legendrePolyP k s‖ ≤ ε := by
        intro s hs
        rw [uIoc_of_le (by norm_num)] at hs
        have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
        rw [norm_mul]
        calc ‖g s‖ * ‖legendrePolyP k s‖ ≤ ε * 1 := by
              gcongr
              · exact (norm_nonneg _).trans (hg s hs')
              · exact hg s hs'
              · exact norm_legendrePolyP_le_one k (abs_le.mpr hs')
          _ = ε := mul_one ε
      have := intervalIntegral.norm_integral_le_of_norm_le_const hb
      rw [show |(1 : ℝ) - (-1)| = 2 by norm_num] at this
      exact this
  -- `D` vanishes on polynomials
  have hDpoly : ∀ Q : Polynomial ℂ, D (fun s => Q.eval (s : ℂ)) = 0 := by
    intro Q
    refine zonal_legendre_induction (fun Q => D (fun s => Q.eval (s : ℂ)) = 0) ?_ ?_ Q
    · intro p q hp hq
      simp only [Polynomial.eval_add]
      rw [hDadd (fun s : ℝ => p.eval (s : ℂ)) (fun s : ℝ => q.eval (s : ℂ))
        ((Polynomial.continuous p).comp continuous_ofReal).continuousOn
        ((Polynomial.continuous q).comp continuous_ofReal).continuousOn, hp, hq, add_zero]
    · intro a j
      simp only [Polynomial.eval_mul, Polynomial.eval_C, ← DLMF.Legendre.legendrePolyP_eq_eval]
      have hrep := zonal_reproduce hS x j
      have horth := legendre_orthogonality j k
      simp only [hD]
      simp_rw [mul_assoc a]
      rw [integral_const_mul, intervalIntegral.integral_const_mul, horth]
      have hj : (2 * j + 1 : ℂ) ≠ 0 := by
        rw [show (2 * j + 1 : ℂ) = ((2 * j + 1 : ℕ) : ℂ) by push_cast; ring]
        exact Nat.cast_ne_zero.mpr (by omega)
      split_ifs at hrep ⊢ with hjk
      · subst hjk
        have hI : (∫ y, legendrePolyP j (t y) * (ev y : ℂ) ∂σ) =
            4 * π * (ev x : ℂ) / (2 * j + 1) := by
          rw [eq_div_iff hj, mul_comm]; exact hrep
        rw [hI]
        field_simp
        ring
      · have hI : (∫ y, legendrePolyP j (t y) * (ev y : ℂ) ∂σ) = 0 := by
          rcases mul_eq_zero.mp hrep with h | h
          · exact absurd h hj
          · exact h
        rw [hI]; ring
  -- approximation
  have hK : ∀ ε : ℝ, 0 < ε → ‖D f‖ ≤ 2 * ε * M * σ.real univ +
      2 * π * (2 * ε * 2) * ‖(ev x : ℂ)‖ := by
    intro ε hε
    obtain ⟨p₁, hp₁⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (fun s => (f s).re)
      (Complex.continuous_re.comp_continuousOn hf) ε hε
    obtain ⟨p₂, hp₂⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (fun s => (f s).im)
      (Complex.continuous_im.comp_continuousOn hf) ε hε
    set Q : Polynomial ℂ := p₁.map Complex.ofRealHom +
      Polynomial.C Complex.I * p₂.map Complex.ofRealHom with hQ
    have hQe : ∀ s : ℝ,
        Q.eval (s : ℂ) = ((p₁.eval s : ℝ) : ℂ) + Complex.I * ((p₂.eval s : ℝ) : ℂ) := by
      intro s
      simp only [hQ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_map]
      rw [show (s : ℂ) = Complex.ofRealHom s from rfl, Polynomial.eval₂_at_apply,
        Polynomial.eval₂_at_apply]
      rfl
    have hQc : ContinuousOn (fun s : ℝ => Q.eval (s : ℂ)) (Icc (-1) 1) :=
      ((Polynomial.continuous Q).comp continuous_ofReal).continuousOn
    have hfQ := hDsub f (fun s => Q.eval (s : ℂ)) hf hQc
    rw [hDpoly Q, sub_zero] at hfQ
    rw [← hfQ]
    refine hDbound (fun s => f s - Q.eval (s : ℂ)) (2 * ε) fun s hs => ?_
    rw [hQe s]
    have hre := hp₁ s hs
    have him := hp₂ s hs
    have hfs : f s = ((f s).re : ℂ) + Complex.I * ((f s).im : ℂ) := by
      rw [mul_comm]; exact (Complex.re_add_im (f s)).symm
    rw [hfs]
    have : ((f s).re : ℂ) + Complex.I * ((f s).im : ℂ) -
        (((p₁.eval s : ℝ) : ℂ) + Complex.I * ((p₂.eval s : ℝ) : ℂ)) =
        (((f s).re - p₁.eval s : ℝ) : ℂ) + Complex.I * (((f s).im - p₂.eval s : ℝ) : ℂ) := by
      push_cast; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm, abs_sub_comm (f s).im]
    linarith
  have hD0 : D f = 0 := by
    by_contra hne
    have hpos : 0 < ‖D f‖ := norm_pos_iff.mpr hne
    set B := 2 * M * σ.real univ + 2 * π * 4 * ‖(ev x : ℂ)‖ with hB
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_univ _))
    have hB0 : 0 ≤ B := by
      have : 0 ≤ σ.real univ := measureReal_nonneg
      positivity
    have h := hK (‖D f‖ / (2 * (B + 1))) (by positivity)
    have : 2 * (‖D f‖ / (2 * (B + 1))) * M * σ.real univ +
        2 * π * (2 * (‖D f‖ / (2 * (B + 1))) * 2) * ‖(ev x : ℂ)‖ =
        ‖D f‖ / (2 * (B + 1)) * B := by rw [hB]; ring
    rw [this] at h
    have h2 : ‖D f‖ / (2 * (B + 1)) * B < ‖D f‖ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  simp only [hD, sub_eq_zero] at hD0
  exact hD0

end FunkHecke

section Addition

open MvPolynomial

/-- Continuous functions on the unit sphere are integrable. -/
theorem zonal_integrable {g : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ} (hg : Continuous g) :
    Integrable g (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere :=
  hg.integrable_of_hasCompactSupport (.of_compactSpace _)

/-- A continuous nonnegative function on the sphere with zero integral vanishes. -/
theorem zonal_eq_zero_of_integral {g : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ}
    (hg : Continuous g) (h0 : 0 ≤ g)
    (hint : ∫ y, g y ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere = 0) (y) :
    g y = 0 := by
  have h1 := (integral_eq_zero_iff_of_nonneg h0 (zonal_integrable hg)).mp hint
  have h2 := (Continuous.ae_eq_iff_eq (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere
    hg continuous_const).mp h1
  exact congrFun h2 y

/-- `P_k(t)` on the real line is the real polynomial `legendrePolyR k`. -/
theorem zonal_legendre_real (k : ℕ) (t : ℝ) :
    legendrePolyP k t = (((DLMF.Legendre.legendrePolyR k).eval t : ℝ) : ℂ) := by
  rw [DLMF.Legendre.legendrePolyP_eq_eval, Polynomial.eval_map,
    show (t : ℂ) = Complex.ofRealHom t from rfl, Polynomial.eval₂_at_apply]
  rfl

/-- Real orthogonality: `∫_{-1}^1 P_k² = 2/(2k+1)`. -/
theorem zonal_legendre_sq (k : ℕ) :
    ∫ s : ℝ in (-1 : ℝ)..1, (DLMF.Legendre.legendrePolyR k).eval s *
      (DLMF.Legendre.legendrePolyR k).eval s = 2 / (2 * k + 1) := by
  have h := legendre_orthogonality k k
  simp only [ite_true, zonal_legendre_real] at h
  simp_rw [← Complex.ofReal_mul] at h
  rw [intervalIntegral.integral_ofReal] at h
  apply Complex.ofReal_injective
  rw [h]; push_cast; ring

/-- Real form of the Funk–Hecke formula for continuous real profiles. -/
theorem zonal_funk_hecke_real {k : ℕ} {g : ℝ → ℝ} (hg : Continuous g)
    {S : MvPolynomial (Fin 3) ℝ} (hS : IsHarmonicHomogeneous k S)
    (ξ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∫ y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      g (∑ i, ξ.val i * y.val i) * eval (fun i => y.val i) S
        ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere =
      2 * π * (∫ s : ℝ in (-1 : ℝ)..1, g s * (DLMF.Legendre.legendrePolyR k).eval s) *
        eval (fun i => ξ.val i) S := by
  have h := zonal_funk_hecke (f := fun s => (g s : ℂ))
    (continuous_ofReal.comp hg).continuousOn S hS ξ
  simp only [zonal_legendre_real] at h
  simp_rw [← Complex.ofReal_mul] at h
  rw [integral_complex_ofReal, intervalIntegral.integral_ofReal] at h
  exact_mod_cast h

/-- `P_0 = 1` as a real polynomial. -/
theorem zonal_legendreR_zero (s : ℝ) : (DLMF.Legendre.legendrePolyR 0).eval s = 1 := by
  have h := zonal_legendre_real 0 s
  rw [legendrePolyP_zero] at h
  exact_mod_cast h.symm

/-- **Addition theorem on the sphere** (AAR Theorem 9.6.3), for unit vectors. The proof shows
that the defect `y ↦ c P_k(ξ·y) - ∑ S_m(ξ) S_m(y)` has squared norm `c - ∑ S_m(ξ)²`, whose
integral over `ξ` vanishes. -/
theorem zonal_addition_sphere {k : ℕ}
    (S : Fin (2 * k + 1) → MvPolynomial (Fin 3) ℝ)
    (hS : ∀ m, IsHarmonicHomogeneous k (S m))
    (horth : ∀ i j, sphericalHarmonicInner (S i) (S j) = if i = j then 1 else 0)
    (ξ η : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (2 * k + 1) / (4 * π) * (DLMF.Legendre.legendrePolyR k).eval (∑ i, ξ.val i * η.val i) =
      ∑ m, eval (fun i => ξ.val i) (S m) * eval (fun i => η.val i) (S m) := by
  set σ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere with hσ
  set c : ℝ := (2 * k + 1) / (4 * π) with hc
  set p : ℝ → ℝ := fun s => (DLMF.Legendre.legendrePolyR k).eval s with hp
  set a : Fin (2 * k + 1) → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ :=
    fun m y => eval (fun i => y.val i) (S m) with ha
  set t : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ :=
    fun ξ y => ∑ i, ξ.val i * y.val i with ht
  have hp_cont : Continuous p := Polynomial.continuous _
  have ha_cont : ∀ m, Continuous (a m) := fun m =>
    (zonal_contDiff (S m)).continuous.comp continuous_subtype_val
  have ht_cont : ∀ ξ, Continuous (t ξ) := fun ξ => by simp only [ht]; fun_prop
  have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have hcinv : c * (2 * π * (2 / (2 * k + 1))) = 1 := by
    rw [hc]; field_simp; ring
  -- Funk–Hecke inputs
  have h1 : ∀ m ξ, ∫ y, p (t ξ y) * a m y ∂σ = 2 * π * (2 / (2 * k + 1)) * a m ξ := by
    intro m ξ
    have := zonal_funk_hecke_real hp_cont (hS m) ξ
    rw [zonal_legendre_sq] at this
    exact this
  have h0 : ∀ ξ, ∫ y, p (t ξ y) * p (t ξ y) ∂σ = 2 * π * (2 / (2 * k + 1)) := by
    intro ξ
    have := zonal_funk_hecke_real (g := fun s => p s * p s) (hp_cont.mul hp_cont)
      (isHarmonicHomogeneous_C 3 1) ξ
    simp only [MvPolynomial.eval_C, mul_one, zonal_legendreR_zero] at this
    rw [this, zonal_legendre_sq]
  have hinner : ∀ m m', ∫ y, a m y * a m' y ∂σ = if m = m' then 1 else 0 := horth
  -- the squared defect
  set F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ :=
    fun ξ y => c * p (t ξ y) - ∑ m, a m ξ * a m y with hF
  have hF_cont : ∀ ξ, Continuous (F ξ) := fun ξ =>
    (continuous_const.mul (hp_cont.comp (ht_cont ξ))).sub
      (continuous_finsetSum _ fun m _ => continuous_const.mul (ha_cont m))
  have hQ : ∀ ξ, ∫ y, F ξ y ^ 2 ∂σ = c - ∑ m, a m ξ ^ 2 := by
    intro ξ
    have hexp : ∀ y, F ξ y ^ 2 = c ^ 2 * (p (t ξ y) * p (t ξ y)) -
        ∑ m, (2 * c * a m ξ) * (p (t ξ y) * a m y) +
        ∑ m, ∑ m', (a m ξ * a m' ξ) * (a m y * a m' y) := by
      intro y
      simp only [hF]
      rw [sub_sq, sq (∑ m, a m ξ * a m y), Finset.sum_mul_sum, Finset.mul_sum]
      congr 1
      · congr 1
        · ring
        · refine Finset.sum_congr rfl fun m _ => ?_; ring
      · refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_; ring
    simp_rw [hexp]
    have hi1 : Integrable (fun y => c ^ 2 * (p (t ξ y) * p (t ξ y))) σ :=
      zonal_integrable (continuous_const.mul
        ((hp_cont.comp (ht_cont ξ)).mul (hp_cont.comp (ht_cont ξ))))
    have hi2 : ∀ m, Integrable (fun y => (2 * c * a m ξ) * (p (t ξ y) * a m y)) σ :=
      fun m => zonal_integrable (continuous_const.mul
        ((hp_cont.comp (ht_cont ξ)).mul (ha_cont m)))
    have hi3 : ∀ m m', Integrable (fun y => (a m ξ * a m' ξ) * (a m y * a m' y)) σ :=
      fun m m' => zonal_integrable (continuous_const.mul ((ha_cont m).mul (ha_cont m')))
    have hs2 : Integrable (fun y => ∑ m, (2 * c * a m ξ) * (p (t ξ y) * a m y))
        σ :=
      integrable_finsetSum _ fun m _ => hi2 m
    have hs3 : Integrable (fun y => ∑ m, ∑ m', (a m ξ * a m' ξ) * (a m y * a m' y))
        σ :=
      integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun m' _ => hi3 m m'
    have hs12 : Integrable (fun y => c ^ 2 * (p (t ξ y) * p (t ξ y)) -
        ∑ m, (2 * c * a m ξ) * (p (t ξ y) * a m y))
        σ := hi1.sub hs2
    rw [integral_add hs12 hs3, integral_sub hi1 hs2,
      integral_finsetSum _ fun m _ => hi2 m,
      integral_finsetSum _ fun m _ => integrable_finsetSum _ fun m' _ => hi3 m m',
      integral_const_mul, h0]
    simp_rw [integral_finsetSum _ fun m' _ => hi3 _ m', integral_const_mul, h1, hinner]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have : ∀ m, 2 * c * a m ξ * (2 * π * (2 / (2 * k + 1)) * a m ξ) = 2 * a m ξ ^ 2 := by
      intro m
      linear_combination (2 * a m ξ ^ 2) * hcinv
    simp_rw [this]
    rw [← Finset.mul_sum]
    simp only [← sq]
    linear_combination c * hcinv
  -- integrate over `ξ`
  set q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ := fun ξ => c - ∑ m, a m ξ ^ 2 with hq
  have hq_cont : Continuous q :=
    continuous_const.sub (continuous_finsetSum _ fun m _ => (ha_cont m).pow 2)
  have hq0 : 0 ≤ q := fun ξ => by
    show 0 ≤ c - ∑ m, a m ξ ^ 2
    rw [← hQ ξ]; exact integral_nonneg fun y => sq_nonneg _
  have hqint : ∫ ξ, q ξ ∂σ = 0 := by
    have hia : ∀ m, Integrable (fun ξ => a m ξ ^ 2) σ :=
      fun m => zonal_integrable ((ha_cont m).pow 2)
    rw [hq, integral_sub (integrable_const c) (integrable_finsetSum _ fun m _ => hia m),
      integral_finsetSum _ fun m _ => hia m, integral_const, smul_eq_mul, zonal_area]
    have : ∀ m, ∫ ξ, a m ξ ^ 2 ∂σ = 1 := by
      intro m
      have := hinner m m
      rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)] at this
      simpa only [sq] using this
    simp_rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [hc]; push_cast; field_simp; ring
  have hqz := zonal_eq_zero_of_integral hq_cont hq0 hqint ξ
  have hFz : ∫ y, F ξ y ^ 2 ∂σ = 0 := by rw [hQ ξ]; exact hqz
  have hF0 := zonal_eq_zero_of_integral ((hF_cont ξ).pow 2) (fun y => sq_nonneg _) hFz η
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hF0
  simp only [hF, sub_eq_zero] at this
  exact this

/-- A coordinate vector with unit sum of squares, as a point of the unit sphere. -/
theorem zonal_mem_sphere {x : Fin 3 → ℝ} (hx : ∑ i, x i ^ 2 = 1) :
    (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3)) ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs, hx, Real.sqrt_one]

/-- **Addition theorem for spherical harmonics** (AAR Theorem 9.6.3), in coordinates. -/
theorem zonal_spherical_addition {k : ℕ}
    (S : Fin (2 * k + 1) → MvPolynomial (Fin 3) ℝ)
    (hS : ∀ m, IsHarmonicHomogeneous k (S m))
    (horth : ∀ i j, sphericalHarmonicInner (S i) (S j) = if i = j then 1 else 0)
    (x y : Fin 3 → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) (hy : ∑ i, y i ^ 2 = 1) :
    (2 * k + 1 : ℂ) / (4 * π) * legendrePolyP k (∑ i, x i * y i : ℝ) =
      ∑ m : Fin (2 * k + 1),
        (MvPolynomial.eval x (S m) : ℂ) * (MvPolynomial.eval y (S m) : ℂ) := by
  have h := zonal_addition_sphere S hS horth ⟨_, zonal_mem_sphere hx⟩ ⟨_, zonal_mem_sphere hy⟩
  rw [zonal_legendre_real]
  have h' := congrArg (fun r : ℝ => (r : ℂ)) h
  push_cast at h'
  exact h'

end Addition

end DLMF.SphericalHarmonics
