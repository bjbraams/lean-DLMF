/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.BesselIntegral
public import DLMF.Bessel.SecondKind

/-!
# Weber's function at integer order, products and Jacobi–Anger series (Duverney Ch. 7)

* `besselY_neg`, `besselY_neg_int`: `Y_{-ν} = sin(νπ) J_ν + cos(νπ) Y_ν`, hence `Y_{-n} = (-1)ⁿ Y_n`
  (DLMF 10.4.1).
* `besselY_int_eq_deriv`: `Y_n = π⁻¹(∂_ν J_ν|_{ν=n} + (-1)ⁿ ∂_ν J_ν|_{ν=-n})` (DLMF 10.2.4).
* `hasSum_deriv_regularized0F1_param`: termwise differentiation of `₀F̃₁` in its parameter, by
  locally uniform convergence of holomorphic functions.
* `besselY_zero_eq_series`, `besselY_nat_eq_series`: the logarithmic series of `Y₀` and `Y_n` with
  harmonic numbers and digamma values (DLMF 10.8.1–10.8.2, Duverney (7.49)).
* `eq_besselJ_besselY_of_ode`: every solution of Bessel's equation on a connected open subset of the
  slit plane is `A J_ν + B Y_ν` (Duverney Thms 7.1, 7.11), via Abel's identity
  `(z W{g,h})' = 0` and `f W{J,Y} = J W{f,Y} + Y W{J,f}`.
* `besselJ_mul_besselJ`: the product formula DLMF 10.8.3 (Duverney Ex. 7.11), from the Cauchy
  product and `∑_{i+j=n} C(n,i)/(Γ(a+i)Γ(b+j)) = (a+b+n-1)ₙ/(Γ(a+n)Γ(b+n))`.
* `hasSum_besselJ_cos`, `hasSum_besselJ_sin`: the Jacobi–Anger cosine and sine series
  (DLMF 10.12.2–10.12.3, Duverney Ex. 7.10).
-/

@[expose] public section

open Complex Filter Set
open scoped Real Topology Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Bessel

/-- `1/Γ(z) = z/Γ(z+1)` for every `z`. -/
theorem recip_Gamma_succ' (z : ℂ) : (Gamma z)⁻¹ = z * (Gamma (z + 1))⁻¹ := by
  simpa [one_div] using one_div_Gamma_eq_self_mul_one_div_Gamma_add_one z

/-- `Y_{-ν} = sin(νπ) J_ν + cos(νπ) Y_ν` for every order (DLMF §10.4). -/
theorem besselY_neg (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselY (-ν) z = sin (ν * π) * besselJ ν z + cos (ν * π) * besselY ν z := by
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement
    (f := fun μ => besselY (-μ) z)
    (g := fun μ => sin (μ * π) * besselJ μ z + cos (μ * π) * besselY μ z)
    (continuousAt_besselY_order (fun μ => -μ) continuous_neg ν hz)
    (((by fun_prop : Continuous fun μ : ℂ => sin (μ * π)).continuousAt.mul
      (continuousAt_besselJ_order (fun μ => μ) continuous_id ν hz)).add
      ((by fun_prop : Continuous fun μ : ℂ => cos (μ * π)).continuousAt.mul
      (continuousAt_besselY_order (fun μ => μ) continuous_id ν hz)))
    (fun c hc => ?_)
  have hc' := DLMF.Confluent.forall_of_mem_integerComplement hc
  have hcn : ∀ k : ℤ, -c ≠ k := fun k h => hc' (-k) (by push_cast; linear_combination -h)
  have hs := sin_mul_pi_ne_zero hc'
  rw [besselY_eq_of_not_int hcn, besselY_eq_of_not_int hc', besselD, besselD, neg_neg,
    neg_mul, Complex.sin_neg, Complex.cos_neg]
  field_simp
  have := sin_sq_add_cos_sq (c * π)
  linear_combination (-besselJ c z) * this

/-- `Y_{-n} = (-1)ⁿ Y_n` (DLMF 10.4.1). -/
@[dlmf 10.4.E1]
theorem besselY_neg_int (n : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselY (-n) z = (-1) ^ n * besselY n z := by
  rw [besselY_neg _ hz, Complex.sin_int_mul_pi, cos_int_mul_pi_complex]; ring

/-- `Y_n(z) = π⁻¹ (∂J_ν/∂ν |_{ν=n} + (-1)ⁿ ∂J_ν/∂ν |_{ν=-n})` (DLMF 10.2.4, Duverney (7.48)). -/
@[dlmf 10.2.E4]
theorem besselY_int_eq_deriv (n : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselY n z = 1 / π * (deriv (fun ν => besselJ ν z) n +
      (-1) ^ n * deriv (fun ν => besselJ ν z) (-n)) := by
  have hz0 := slitPlane_ne_zero hz
  have hJ := differentiable_besselJ_order hz0
  rw [besselY_eq_dslope n (Metric.mem_ball_self (by norm_num)) hz, dslope_same, dslope_same]
  have hD : HasDerivAt (fun ν => besselD ν z)
      (deriv (fun ν => besselJ ν z) n * cos ((n : ℂ) * π) +
        besselJ n z * (-sin ((n : ℂ) * π) * π) - deriv (fun ν => besselJ ν z) (-n) * (-1)) n := by
    have h1 := (hJ n).hasDerivAt
    have h2 : HasDerivAt (fun ν : ℂ => cos (ν * π)) (-sin ((n : ℂ) * π) * π) n := by
      simpa using ((hasDerivAt_id (n : ℂ)).mul_const (π : ℂ)).ccos
    have h3 : HasDerivAt (fun ν : ℂ => besselJ (-ν) z)
        (deriv (fun ν => besselJ ν z) (-n) * (-1)) n :=
      ((hJ (-n)).hasDerivAt).comp (n : ℂ) (hasDerivAt_neg (n : ℂ))
    exact (h1.mul h2).sub h3
  have hS : HasDerivAt (fun ν : ℂ => sin (ν * π)) (cos ((n : ℂ) * π) * π) n := by
    simpa using ((hasDerivAt_id (n : ℂ)).mul_const (π : ℂ)).csin
  rw [hD.deriv, hS.deriv, Complex.sin_int_mul_pi, cos_int_mul_pi_complex]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hm : ((-1 : ℂ)) ^ n * (-1) ^ n = 1 := by
    rw [← mul_zpow]; norm_num
  have hm0 : ((-1 : ℂ)) ^ n ≠ 0 := zpow_ne_zero _ (by norm_num)
  field_simp
  linear_combination (-(deriv (fun ν => besselJ ν z) (-n))) * hm

/-- Termwise differentiation of `₀F̃₁(;c;w)` in the parameter:
`∂_c ₀F̃₁(;c;w) = ∑ wⁿ/n! · (1/Γ)'(c+n)`. -/
theorem hasSum_deriv_regularized0F1_param (c₀ w : ℂ) :
    HasSum (fun n : ℕ => w ^ n / n ! * deriv (fun y => (Gamma y)⁻¹) (c₀ + n))
      (deriv (fun c => regularizedHGFun (∅ : Multiset ℂ) {c} w) c₀) := by
  set T : ℕ → ℂ → ℂ := fun n c => w ^ n / n ! * (Gamma (c + n))⁻¹ with hT
  have hTd (n : ℕ) : Differentiable ℂ (T n) :=
    (differentiable_const _).mul (differentiable_one_div_Gamma.comp (by fun_prop))
  have hTderiv (n : ℕ) (c : ℂ) : deriv (T n) c = w ^ n / n ! * deriv (fun y => (Gamma y)⁻¹)
      (c + n) := by
    have h := ((differentiable_one_div_Gamma (c + n)).hasDerivAt.comp c
      ((hasDerivAt_id c).add_const (n : ℂ))).const_mul (w ^ n / n !)
    simp only [mul_one] at h
    exact h.deriv
  obtain ⟨V, hV, hc₀, N, u, hu, hle⟩ := exists_regularized0F1_dominated c₀ ‖w‖
  -- the tail
  set G : ℂ → ℂ := fun c => ∑' k : ℕ, T (k + N) c with hG
  have htail := Complex.hasSum_deriv_of_summable_norm (u := fun k => u (k + N))
    (hu.comp_injective (add_left_injective N)) (fun k => (hTd (k + N)).differentiableOn) hV
    (fun k c hc => hle (k + N) (by omega) c hc w le_rfl) hc₀
  -- the whole series
  have hf : (fun c => regularizedHGFun (∅ : Multiset ℂ) {c} w) =
      fun c => (∑ n ∈ Finset.range N, T n c) + G c := by
    funext c
    rw [regularized0F1_eq_tsum, ← (summable_regularized0F1_term c w).sum_add_tsum_nat_add N]
  have hGd : DifferentiableAt ℂ G c₀ := by
    have h1 := differentiable_regularized0F1_param w c₀
    rw [hf] at h1
    have h2 : DifferentiableAt ℂ (fun c => ∑ n ∈ Finset.range N, T n c) c₀ :=
      DifferentiableAt.fun_sum fun n _ => hTd n c₀
    have h3 := h1.sub h2
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun c => ?_)
    simp
  have hderiv : deriv (fun c => regularizedHGFun (∅ : Multiset ℂ) {c} w) c₀ =
      (∑ n ∈ Finset.range N, deriv (T n) c₀) + deriv G c₀ := by
    rw [hf, deriv_fun_add (DifferentiableAt.fun_sum fun n _ => hTd n c₀) hGd,
      deriv_fun_sum (fun n _ => (hTd n) c₀)]
  rw [hderiv]
  simp_rw [← hTderiv]
  exact (hasSum_nat_add_iff' N).mp (by simpa using htail)

/-- `∂J_ν(z)/∂ν = log(z/2) J_ν(z) + (z/2)^ν ∂_c ₀F̃₁(;c;-z²/4)|_{c=ν+1}`. -/
theorem deriv_besselJ_order (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    deriv (fun μ => besselJ μ z) ν = log (z / 2) * besselJ ν z +
      (z / 2) ^ ν * deriv (fun c => regularizedHGFun (∅ : Multiset ℂ) {c} (-(z ^ 2 / 4)))
        (ν + 1) := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have h1 : HasDerivAt (fun μ : ℂ => (z / 2) ^ μ) ((z / 2) ^ ν * log (z / 2)) ν := by
    simpa using (hasDerivAt_id ν).const_cpow (c := z / 2) (Or.inl hz2)
  have h2 : HasDerivAt (fun μ : ℂ => regularizedHGFun (∅ : Multiset ℂ) {μ + 1} (-(z ^ 2 / 4)))
      (deriv (fun c => regularizedHGFun (∅ : Multiset ℂ) {c} (-(z ^ 2 / 4))) (ν + 1)) ν := by
    exact (((differentiable_regularized0F1_param (-(z ^ 2 / 4)) (ν + 1)).hasDerivAt).comp ν
      ((hasDerivAt_id' ν).add_const 1)).congr_deriv (mul_one _)
  have h : HasDerivAt (fun μ : ℂ => (z / 2) ^ μ *
      regularizedHGFun (∅ : Multiset ℂ) {μ + 1} (-(z ^ 2 / 4))) _ ν := h1.mul h2
  rw [show (fun μ => besselJ μ z) = fun μ : ℂ => (z / 2) ^ μ *
      regularizedHGFun (∅ : Multiset ℂ) {μ + 1} (-(z ^ 2 / 4)) from
    funext fun μ => besselJ_eq_regularized μ z, h.deriv, besselJ_eq_regularized]
  ring

/-- **The logarithmic series of `Y₀`** (DLMF 10.8.2, Duverney (7.49) with `n = 0`):
`Y₀(z) = (2/π)((log(z/2) + γ) J₀(z) - ∑ₖ Hₖ (-z²/4)ᵏ/(k!)²)`. -/
@[dlmf 10.8.E2]
theorem besselY_zero_eq_series {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => (harmonic k : ℂ) * (-(z ^ 2 / 4)) ^ k / (k ! : ℂ) ^ 2)
      ((log (z / 2) + Real.eulerMascheroniConstant) * besselJ 0 z - π / 2 * besselY 0 z) := by
  have hz0 := slitPlane_ne_zero hz
  set w : ℂ := -(z ^ 2 / 4)
  have hY := besselY_int_eq_deriv 0 hz
  push_cast at hY
  rw [neg_zero, zpow_zero, one_mul, deriv_besselJ_order 0 hz0, zero_add, cpow_zero, one_mul]
    at hY
  have hd := hasSum_deriv_regularized0F1_param 1 w
  have hJ0 : besselJ 0 z = regularizedHGFun (∅ : Multiset ℂ) {1} w := by
    simp [besselJ_eq_regularized, w]
  -- the γ-part
  have hF : HasSum (fun k : ℕ => w ^ k / (k ! : ℂ) ^ 2) (besselJ 0 z) := by
    rw [hJ0, regularized0F1_eq_tsum]
    refine ((summable_regularized0F1_term 1 w).hasSum).congr_fun fun k => ?_
    rw [show (1 : ℂ) + k = ((k : ℕ) : ℂ) + 1 by ring, Gamma_nat_eq_factorial]
    ring
  have hterm (k : ℕ) : w ^ k / k ! * deriv (fun y => (Gamma y)⁻¹) (1 + k) =
      Real.eulerMascheroniConstant * (w ^ k / (k ! : ℂ) ^ 2) -
        (harmonic k : ℂ) * w ^ k / (k ! : ℂ) ^ 2 := by
    have hk : ∀ m : ℕ, (1 + (k : ℂ)) ≠ -(m : ℂ) := fun m h => by
      have := congrArg re h; simp at this; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
    rw [DLMF.Hypergeometric.deriv_recip_Gamma_eq hk, show (1 : ℂ) + k = (k : ℂ) + 1 by ring,
      digamma_nat_add_one, show ((k : ℂ) + 1) = ((k : ℕ) : ℂ) + 1 by rfl, Gamma_nat_eq_factorial]
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    field_simp
    ring
  simp_rw [hterm] at hd
  have hres := (hF.mul_left (Real.eulerMascheroniConstant : ℂ)).sub hd
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  convert hres using 1
  · funext k; ring
  · rw [hY]; field_simp; ring

/-- **The logarithmic series of `Y_n`** (DLMF 10.8.1, Duverney (7.49)):
`π Y_n(z) = 2 log(z/2) J_n(z) - (z/2)⁻ⁿ ∑_{k<n} (n-k-1)!/k! (z²/4)ᵏ
  - (z/2)ⁿ ∑ₖ (ψ(k+1) + ψ(n+k+1)) (-z²/4)ᵏ/(k!(n+k)!)`. -/
@[dlmf 10.8.E1]
theorem besselY_nat_eq_series (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => (digamma (k + 1) + digamma (n + k + 1)) * (-(z ^ 2 / 4)) ^ k /
        ((k ! : ℂ) * ((n + k) ! : ℂ)))
      ((2 * log (z / 2) * besselJ n z - (z / 2) ^ (-(n : ℂ)) *
          ∑ k ∈ Finset.range n, ((n - k - 1) ! : ℂ) / (k ! : ℂ) * (z ^ 2 / 4) ^ k -
          π * besselY n z) / (z / 2) ^ (n : ℂ)) := by
  have hz0 := slitPlane_ne_zero hz
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz0 two_ne_zero
  set w : ℂ := -(z ^ 2 / 4) with hw
  have hY := besselY_int_eq_deriv n hz
  push_cast at hY
  rw [deriv_besselJ_order _ hz0, deriv_besselJ_order _ hz0] at hY
  have hA := hasSum_deriv_regularized0F1_param ((n : ℂ) + 1) w
  have hB := (hasSum_nat_add_iff' n).mpr (hasSum_deriv_regularized0F1_param (-(n : ℂ) + 1) w)
  have hw0 : w ≠ 0 := by
    rw [hw]; exact neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 2 hz0) (by norm_num))
  have hpos (m : ℕ) : ∀ p : ℕ, ((m : ℂ) + 1) ≠ -(p : ℂ) := fun p h => by
    have := congrArg re h; simp at this; linarith [(p.cast_nonneg : (0:ℝ) ≤ p)]
  have hdpos (m : ℕ) : deriv (fun y => (Gamma y)⁻¹) ((m : ℂ) + 1) =
      -(digamma ((m : ℂ) + 1)) / (m ! : ℂ) := by
    rw [DLMF.Hypergeometric.deriv_recip_Gamma_eq (hpos m), Gamma_nat_eq_factorial]
    ring
  have hres := hA.neg.sub (hB.mul_right (w ^ n)⁻¹)
  have hJn : besselJ (-(n : ℂ)) z = (-1) ^ n * besselJ n z := by
    have := besselJ_neg_int (n : ℤ) z
    push_cast at this; simpa using this
  rw [hJn] at hY
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hneg : (z / 2) ^ (-(n : ℂ)) = ((z / 2) ^ n)⁻¹ := by rw [cpow_neg, cpow_natCast]
  have hww : w ^ n = (-1) ^ n * ((z / 2) ^ n) ^ 2 := by
    rw [hw, show -(z ^ 2 / 4) = -1 * (z / 2) ^ 2 by ring, mul_pow, ← pow_mul, ← pow_mul,
      mul_comm 2 n]
  have hfin : (-1 : ℂ) ^ n * ∑ k ∈ Finset.range n, w ^ k / (k ! : ℂ) *
      deriv (fun y => (Gamma y)⁻¹) (-(n : ℂ) + 1 + k) =
        -∑ k ∈ Finset.range n, ((n - k - 1) ! : ℂ) / (k ! : ℂ) *
          (z ^ 2 / 4) ^ k := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have hcast : -(n : ℂ) + 1 + k = -((n - 1 - k : ℕ) : ℂ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast, DLMF.Hypergeometric.deriv_recip_Gamma_neg_nat, hw, neg_pow (z ^ 2 / 4) k,
      show n - k - 1 = n - 1 - k by omega]
    have hsign : ((-1 : ℂ)) ^ n * ((-1) ^ k * (-1) ^ (n - 1 - k)) = -1 := by
      rw [← pow_add, ← pow_add, show n + (k + (n - 1 - k)) = 2 * (n - 1) + 1 by omega,
        pow_succ, pow_mul]; norm_num
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    field_simp
    linear_combination ((n - 1 - k) ! : ℂ) * hsign
  convert hres using 1
  · funext k
    rw [show ((n : ℂ) + 1 + k) = ((n + k : ℕ) : ℂ) + 1 by push_cast; ring, hdpos,
      show (-(n : ℂ) + 1 + ((k + n : ℕ) : ℂ)) = (k : ℂ) + 1 by push_cast; ring, hdpos, pow_add,
      show k + n = n + k by ring]
    push_cast
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hf' : ((n + k) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n + k).factorial_ne_zero
    have hwn : w ^ n ≠ 0 := pow_ne_zero n hw0
    field_simp
    ring
  · rw [hneg]
    have hzn : (z / 2) ^ (n : ℂ) = (z / 2) ^ n := cpow_natCast _ _
    rw [hzn]
    have hzn0 : (z / 2) ^ n ≠ 0 := pow_ne_zero n hz2
    have hwn : w ^ n ≠ 0 := pow_ne_zero n hw0
    rw [hY, hzn, hneg, zpow_natCast, ← hw]
    generalize deriv (fun c => regularizedHGFun (∅ : Multiset ℂ) {c} w) ((n : ℂ) + 1) = F1
    generalize deriv (fun c => regularizedHGFun (∅ : Multiset ℂ) {c} w) (-(n : ℂ) + 1) = F2
    generalize ∑ i ∈ Finset.range n, w ^ i / (i ! : ℂ) * deriv (fun y => (Gamma y)⁻¹)
      (-(n : ℂ) + 1 + i) = FS at hfin ⊢
    generalize ∑ k ∈ Finset.range n, ((n - k - 1) ! : ℂ) / (k ! : ℂ) * (z ^ 2 / 4) ^ k = S2
      at hfin ⊢
    rw [hww]
    have hm : ((-1 : ℂ)) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
    have hm0 : ((-1 : ℂ)) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    linear_combination (-((-1 : ℂ) ^ n * log (z / 2) * besselJ n z * (z / 2) ^ n) - F2 + FS) * hm -
      (-1 : ℂ) ^ n * hfin

/-- Abel's identity for Bessel's equation: if `g` and `h` solve it on an open set `U ⊆ ℂ ∖ {0}`,
then `z · W{g, h}(z)` has zero derivative on `U`. -/
theorem hasDerivAt_mul_wronskian_bessel (ν : ℂ) {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, z ≠ 0) {g h : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hh : DifferentiableOn ℂ h U)
    (hgo : ∀ z ∈ U, z ^ 2 * iteratedDeriv 2 g z + z * deriv g z + (z ^ 2 - ν ^ 2) * g z = 0)
    (hho : ∀ z ∈ U, z ^ 2 * iteratedDeriv 2 h z + z * deriv h z + (z ^ 2 - ν ^ 2) * h z = 0)
    {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun z => z * (g z * deriv h z - deriv g z * h z)) 0 z := by
  have hga := hg.analyticOnNhd hU z hz
  have hha := hh.analyticOnNhd hU z hz
  have h1 := hga.differentiableAt.hasDerivAt
  have h2 := hha.differentiableAt.hasDerivAt
  have h3 := hga.deriv.differentiableAt.hasDerivAt
  have h4 := hha.deriv.differentiableAt.hasDerivAt
  have H := (hasDerivAt_id' z).mul ((h1.mul h4).sub (h3.mul h2))
  refine H.congr_deriv ?_
  have eg := hgo z hz
  have eh := hho z hz
  rw [iteratedDeriv_succ, iteratedDeriv_one] at eg eh
  have hz0 := h0 z hz
  simp only [Pi.mul_apply, Pi.sub_apply]
  apply mul_left_cancel₀ hz0
  rw [mul_zero]
  linear_combination (g z) * eh - (h z) * eg

/-- **General solution of Bessel's equation** (Duverney Thm 7.1, 7.11): every solution on a
connected open subset of the slit plane is a combination `A J_ν + B Y_ν`. -/
theorem eq_besselJ_besselY_of_ode (ν : ℂ) {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUs : U ⊆ slitPlane) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hfo : ∀ z ∈ U, z ^ 2 * iteratedDeriv 2 f z + z * deriv f z + (z ^ 2 - ν ^ 2) * f z = 0) :
    ∃ A B : ℂ, ∀ z ∈ U, f z = A * besselJ ν z + B * besselY ν z := by
  rcases U.eq_empty_or_nonempty with hE | ⟨z₀, hz₀⟩
  · exact ⟨0, 0, by simp [hE]⟩
  have h0 : ∀ z ∈ U, z ≠ 0 := fun z hz => slitPlane_ne_zero (hUs hz)
  have hJ : DifferentiableOn ℂ (besselJ ν) U := fun z hz =>
    (hasDerivAt_besselJ (ν := ν) (hUs hz)).differentiableAt.differentiableWithinAt
  have hY : DifferentiableOn ℂ (besselY ν) U := fun z hz =>
    (hasDerivAt_besselY ν (hUs hz)).differentiableAt.differentiableWithinAt
  have hJo : ∀ z ∈ U, _ := fun z hz => besselJ_ode (ν := ν) (hUs hz)
  have hYo : ∀ z ∈ U, _ := fun z hz => besselY_ode_all ν (hUs hz)
  have hconst {g h : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hh : DifferentiableOn ℂ h U)
      (hgo : ∀ z ∈ U, z ^ 2 * iteratedDeriv 2 g z + z * deriv g z + (z ^ 2 - ν ^ 2) * g z = 0)
      (hho : ∀ z ∈ U, z ^ 2 * iteratedDeriv 2 h z + z * deriv h z + (z ^ 2 - ν ^ 2) * h z = 0)
      (z : ℂ) (hz : z ∈ U) :
      z * (g z * deriv h z - deriv g z * h z) =
        z₀ * (g z₀ * deriv h z₀ - deriv g z₀ * h z₀) :=
    hU.is_const_of_deriv_eq_zero hUc
      (fun w hw => ((hasDerivAt_mul_wronskian_bessel ν hU h0 hg hh hgo hho
        hw).differentiableAt).differentiableWithinAt)
      (fun w hw => (hasDerivAt_mul_wronskian_bessel ν hU h0 hg hh hgo hho hw).deriv) hz hz₀
  set A := π / 2 * (z₀ * (f z₀ * deriv (besselY ν) z₀ - deriv f z₀ * besselY ν z₀))
  set B := π / 2 * (z₀ * (besselJ ν z₀ * deriv f z₀ - deriv (besselJ ν) z₀ * f z₀))
  refine ⟨A, B, fun z hz => ?_⟩
  have e1 := hconst hf hY hfo hYo z hz
  have e2 := hconst hJ hf hJo hfo z hz
  have e3 := wronskian_besselJ_besselY ν (hUs hz)
  have hz0 := h0 z hz
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [A, B]
  rw [← e1, ← e2]
  field_simp at e3 ⊢
  linear_combination (-f z) * e3

/-- `∑_{i+j=n} C(n,i)/(Γ(a+i) Γ(b+j)) = (a+b+n-1)ₙ/(Γ(a+n) Γ(b+n))`, for all complex `a, b`. -/
theorem sum_antidiagonal_choose_recip_Gamma (n : ℕ) : ∀ a b : ℂ,
    ∑ ij ∈ Finset.antidiagonal n, ((n.choose ij.1 : ℕ) : ℂ) * (Gamma (a + ij.1))⁻¹ *
        (Gamma (b + ij.2))⁻¹ =
      poch (a + b + n - 1) n * (Gamma (a + n))⁻¹ * (Gamma (b + n))⁻¹ := by
  induction n with
  | zero => intro a b; simp [poch_zero]
  | succ n ih =>
    intro a b
    have h := Finset.sum_antidiagonal_choose_succ_mul
      (fun i j => (Gamma (a + i))⁻¹ * (Gamma (b + j))⁻¹) n
    simp only [← mul_assoc] at h
    rw [h]
    have h2 : ∑ ij ∈ Finset.antidiagonal n, ((n.choose ij.2 : ℕ) : ℂ) *
        (Gamma (a + ((ij.1 + 1 : ℕ) : ℂ)))⁻¹ * (Gamma (b + ij.2))⁻¹ =
        ∑ ij ∈ Finset.antidiagonal n, ((n.choose ij.1 : ℕ) : ℂ) *
          (Gamma (a + 1 + ij.1))⁻¹ * (Gamma (b + ij.2))⁻¹ := by
      refine Finset.sum_congr rfl fun ij hij => ?_
      rw [Finset.mem_antidiagonal] at hij
      rw [← hij, Nat.choose_symm_add]; push_cast; ring_nf
    have h1 : ∑ ij ∈ Finset.antidiagonal n, ((n.choose ij.1 : ℕ) : ℂ) *
        (Gamma (a + ij.1))⁻¹ * (Gamma (b + ((ij.2 + 1 : ℕ) : ℂ)))⁻¹ =
        ∑ ij ∈ Finset.antidiagonal n, ((n.choose ij.1 : ℕ) : ℂ) *
          (Gamma (a + ij.1))⁻¹ * (Gamma (b + 1 + ij.2))⁻¹ := by
      refine Finset.sum_congr rfl fun ij _ => ?_
      push_cast; ring_nf
    rw [h1, h2, ih a (b + 1), ih (a + 1) b]
    rw [show (Gamma (a + n))⁻¹ = (a + n) * (Gamma (a + n + 1))⁻¹ from recip_Gamma_succ' _,
      show (Gamma (b + n))⁻¹ = (b + n) * (Gamma (b + n + 1))⁻¹ from recip_Gamma_succ' _,
      poch_succ]
    push_cast
    rw [show a + (b + 1) + n - 1 = a + b + (n + 1) - 1 by ring,
      show a + 1 + b + n - 1 = a + b + (n + 1) - 1 by ring,
      show b + 1 + n = b + (n + 1) by ring, show a + 1 + n = a + (n + 1) by ring,
      show a + n + 1 = a + (n + 1) by ring, show b + n + 1 = b + (n + 1) by ring]
    ring

set_option maxHeartbeats 600000 in
/-- **Product of Bessel functions** (DLMF 10.8.3, Duverney Ex. 7.11):
`J_μ(z) J_ν(z) = (z/2)^{μ+ν} ∑ₖ (μ+ν+k+1)ₖ (-z²/4)ᵏ / (k! Γ(μ+k+1) Γ(ν+k+1))`. -/
@[dlmf 10.8.E3]
theorem besselJ_mul_besselJ (μ ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselJ μ z * besselJ ν z = (z / 2) ^ (μ + ν) *
      ∑' k : ℕ, poch (μ + ν + k + 1) k * (-(z ^ 2 / 4)) ^ k / (k ! : ℂ) *
        (Gamma (μ + k + 1))⁻¹ * (Gamma (ν + k + 1))⁻¹ := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero (slitPlane_ne_zero hz) two_ne_zero
  set w : ℂ := -(z ^ 2 / 4)
  have hs (c : ℂ) := summable_regularized0F1_term c w
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_iff.mpr (hs (μ + 1))) (summable_norm_iff.mpr (hs (ν + 1)))
  rw [besselJ_eq_regularized, besselJ_eq_regularized, mul_mul_mul_comm, ← cpow_add _ _ hz2,
    regularized0F1_eq_tsum, regularized0F1_eq_tsum, hprod]
  refine congrArg ((z / 2) ^ (μ + ν) * ·) (tsum_congr fun n => ?_)
  have hc := sum_antidiagonal_choose_recip_Gamma n (μ + 1) (ν + 1)
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hterm : ∀ ij ∈ Finset.antidiagonal n,
      w ^ ij.1 / (ij.1 ! : ℂ) * (Gamma (μ + 1 + ij.1))⁻¹ *
        (w ^ ij.2 / (ij.2 ! : ℂ) * (Gamma (ν + 1 + ij.2))⁻¹) =
      w ^ n / (n ! : ℂ) * (((n.choose ij.1 : ℕ) : ℂ) * (Gamma (μ + 1 + ij.1))⁻¹ *
        (Gamma (ν + 1 + ij.2))⁻¹) := by
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij
    have hch := Nat.choose_mul_factorial_mul_factorial (show ij.1 ≤ n by omega)
    rw [show n - ij.1 = ij.2 by omega] at hch
    have hch' : ((n.choose ij.1 : ℕ) : ℂ) * (ij.1 ! : ℂ) * (ij.2 ! : ℂ) = (n ! : ℂ) := by
      exact_mod_cast hch
    have h1 : (ij.1 ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (ij.2 ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hn' : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hw : w ^ n = w ^ ij.1 * w ^ ij.2 := by rw [← pow_add, hij]
    rw [hw]
    generalize (Gamma (μ + 1 + ij.1))⁻¹ = A
    generalize (Gamma (ν + 1 + ij.2))⁻¹ = B
    generalize w ^ ij.1 = X
    generalize w ^ ij.2 = Y
    have hC : ((n.choose ij.1 : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    rw [← hch']
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hc]
  rw [show μ + 1 + (ν + 1) + n - 1 = μ + ν + n + 1 by ring,
    show μ + 1 + n = μ + n + 1 by ring, show ν + 1 + n = ν + n + 1 by ring]
  ring

/-- The bilateral cosine and sine series `∑_{m∈ℤ} J_m(z) cos(mθ) = cos(z sin θ)` and
`∑_{m∈ℤ} J_m(z) sin(mθ) = sin(z sin θ)`. -/
theorem hasSum_besselJ_int_cos_sin (z : ℂ) (θ : ℝ) :
    HasSum (fun m : ℤ => besselJ m z * cos (m * θ)) (cos (z * sin θ)) ∧
      HasSum (fun m : ℤ => besselJ m z * sin (m * θ)) (sin (z * sin θ)) := by
  have h1 := hasSum_besselJ_jacobiAnger z θ
  have h2 := hasSum_besselJ_jacobiAnger z (-θ)
  push_cast at h2
  rw [Complex.sin_neg] at h2
  constructor
  · have h := (h1.add h2).div_const 2
    convert h using 1
    · funext m; rw [Complex.cos]; ring_nf
    · rw [Complex.cos]; ring_nf
  · have h := (h1.sub h2).div_const (2 * I)
    convert h using 1
    · funext m; rw [Complex.sin]; field_simp; ring_nf; rw [I_sq]; ring
    · rw [Complex.sin]; field_simp; ring_nf; rw [I_sq]; ring

/-- **Jacobi–Anger, cosine form** (DLMF 10.12.2, Duverney Ex. 7.10):
`cos(z sin θ) = J₀(z) + 2 ∑_{k≥1} J_{2k}(z) cos(2kθ)`. -/
@[dlmf 10.12.E2]
theorem hasSum_besselJ_cos (z : ℂ) (θ : ℝ) :
    HasSum (fun k : ℕ => 2 * besselJ (2 * k + 2 : ℕ) z * cos ((2 * k + 2 : ℕ) * θ))
      (cos (z * sin θ) - besselJ 0 z) := by
  have h := (hasSum_besselJ_int_cos_sin z θ).1.nat_add_neg
  have hterm (n : ℕ) : besselJ ((n : ℤ) : ℂ) z * cos (((n : ℤ) : ℂ) * θ) +
      besselJ ((-(n : ℤ) : ℤ) : ℂ) z * cos (((-(n : ℤ) : ℤ) : ℂ) * θ) =
      (1 + (-1) ^ n) * besselJ n z * cos (n * θ) := by
    have hJ := besselJ_neg_int (n : ℤ) z
    rw [zpow_natCast] at hJ
    push_cast at hJ ⊢
    rw [hJ, neg_mul, Complex.cos_neg]
    ring
  simp_rw [hterm] at h
  simp only [Int.cast_zero, zero_mul, Complex.cos_zero, mul_one] at h
  have hodd : ∀ n ∉ Set.range (fun k : ℕ => 2 * k), (1 + (-1 : ℂ) ^ n) * besselJ n z *
      cos (n * θ) = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact absurd ⟨m, by simp only; omega⟩ hn
      · exact ⟨m, hm⟩
    rw [pow_succ, pow_mul]; norm_num
  have heven := ((mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0)).hasSum_iff hodd).mpr h
  have hs := (hasSum_nat_add_iff' 1).mpr heven
  convert hs using 1
  · funext k
    simp only [Function.comp, mul_add, mul_one]
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]
    norm_num
  · simp
    ring

/-- **Jacobi–Anger, sine form** (DLMF 10.12.3, Duverney Ex. 7.10):
`sin(z sin θ) = 2 ∑_{k≥0} J_{2k+1}(z) sin((2k+1)θ)`. -/
@[dlmf 10.12.E3]
theorem hasSum_besselJ_sin (z : ℂ) (θ : ℝ) :
    HasSum (fun k : ℕ => 2 * besselJ (2 * k + 1 : ℕ) z * sin ((2 * k + 1 : ℕ) * θ))
      (sin (z * sin θ)) := by
  have h := (hasSum_besselJ_int_cos_sin z θ).2.nat_add_neg
  have hterm (n : ℕ) : besselJ ((n : ℤ) : ℂ) z * sin (((n : ℤ) : ℂ) * θ) +
      besselJ ((-(n : ℤ) : ℤ) : ℂ) z * sin (((-(n : ℤ) : ℤ) : ℂ) * θ) =
      (1 - (-1) ^ n) * besselJ n z * sin (n * θ) := by
    have hJ := besselJ_neg_int (n : ℤ) z
    rw [zpow_natCast] at hJ
    push_cast at hJ ⊢
    rw [hJ, neg_mul, Complex.sin_neg]
    ring
  simp_rw [hterm] at h
  simp only [Int.cast_zero, zero_mul, Complex.sin_zero, mul_zero, add_zero] at h
  have heven : ∀ n ∉ Set.range (fun k : ℕ => 2 * k + 1), (1 - (-1 : ℂ) ^ n) * besselJ n z *
      sin (n * θ) = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact ⟨m, by omega⟩
      · exact absurd ⟨m, by simp only; omega⟩ hn
    rw [pow_mul]; norm_num
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b hab => by
    simp only at hab; omega
  have hodd := (hinj.hasSum_iff heven).mpr h
  convert hodd using 1
  funext k
  simp only [Function.comp]
  rw [pow_succ, pow_mul]
  norm_num

end DLMF.Bessel

end
