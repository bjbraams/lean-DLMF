/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Calculus.SeveralVariables
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Vectors and vector-valued functions (DLMF §1.6(i)–(iii))

Vectors of `ℝ³` are `Fin 3 → ℝ`, with Mathlib's `dotProduct` (`⬝ᵥ`) and `crossProduct`
(`⨯₃`); the unit vectors `i, j, k = e₁, e₂, e₃` are `Pi.single 0 1`, `Pi.single 1 1`,
`Pi.single 2 1`. Lengths use `vecNorm` (1.6.3) and angles the unoriented angle of
`EuclideanSpace ℝ (Fin 3)`. The Levi-Civita symbol is `leviCivita` (1.6.14).

For §1.6(iii) the operators `grad`, `divergence`, `curl`, `laplacian`, `vectorLaplacian` are
those of `DLMF.AlgebraicAnalytic.Calculus.Defs`, built from partial derivatives of sections.
The identities 1.6.23–1.6.34 are proved pointwise: first-order identities assume
differentiability at the point, second-order ones `C²` at the point (which gives the symmetry
of mixed partial derivatives, `partialDeriv_comm`).
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology Matrix

namespace DLMF.AlgebraicAnalytic

/-! ### §1.6(i) Vectors -/

/-- DLMF 1.6.2 (and 1.6.12): `a · b = a₁b₁ + a₂b₂ + a₃b₃`. -/
@[dlmf 1.6.E2, dlmf 1.6.E12]
theorem dotProduct_fin_three (a b : Fin 3 → ℝ) :
    a ⬝ᵥ b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [dotProduct, Fin.sum_univ_three]

/-- DLMF 1.6.3: `vecNorm` is the Euclidean norm of `EuclideanSpace ℝ (Fin 3)`. -/
@[dlmf 1.6.E3]
theorem vecNorm_eq_norm (a : Fin 3 → ℝ) :
    vecNorm a = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin 3))‖ := by
  simp [vecNorm, EuclideanSpace.norm_eq, dotProduct, sq]

/-- The Euclidean inner product of `EuclideanSpace ℝ (Fin 3)` is the dot product. -/
lemma g1b_inner_toLp (a b : Fin 3 → ℝ) :
    inner ℝ (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin 3)) (WithLp.toLp 2 b) = a ⬝ᵥ b := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- DLMF 1.6.4: the angle `θ` between `a` and `b` satisfies `cos θ = a · b / (‖a‖ ‖b‖)`. -/
@[dlmf 1.6.E4]
theorem cos_angle_eq_dotProduct_div (a b : Fin 3 → ℝ) :
    Real.cos (InnerProductGeometry.angle (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin 3))
      (WithLp.toLp 2 b)) = a ⬝ᵥ b / (vecNorm a * vecNorm b) := by
  rw [InnerProductGeometry.cos_angle, g1b_inner_toLp, vecNorm_eq_norm, vecNorm_eq_norm]

/-- DLMF 1.6.7: `i × j = k`, `j × k = i`, `k × i = j`. -/
@[dlmf 1.6.E7]
theorem cross_unit_vectors :
    (Pi.single 0 1 : Fin 3 → ℝ) ⨯₃ Pi.single 1 1 = Pi.single 2 1 ∧
      (Pi.single 1 1 : Fin 3 → ℝ) ⨯₃ Pi.single 2 1 = Pi.single 0 1 ∧
      (Pi.single 2 1 : Fin 3 → ℝ) ⨯₃ Pi.single 0 1 = Pi.single 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> simp [cross_apply]

/-- DLMF 1.6.8: `j × i = -k`, `k × j = -i`, `i × k = -j`. -/
@[dlmf 1.6.E8]
theorem cross_unit_vectors_neg :
    (Pi.single 1 1 : Fin 3 → ℝ) ⨯₃ Pi.single 0 1 = -Pi.single 2 1 ∧
      (Pi.single 2 1 : Fin 3 → ℝ) ⨯₃ Pi.single 1 1 = -Pi.single 0 1 ∧
      (Pi.single 0 1 : Fin 3 → ℝ) ⨯₃ Pi.single 2 1 = -Pi.single 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> simp [cross_apply]

/-- DLMF 1.6.9: the components of the cross product,
`a × b = (a₂b₃ - a₃b₂) i + (a₃b₁ - a₁b₃) j + (a₁b₂ - a₂b₁) k`. -/
@[dlmf 1.6.E9]
theorem cross_eq_sum_unit_vectors (a b : Fin 3 → ℝ) :
    a ⨯₃ b = (a 1 * b 2 - a 2 * b 1) • Pi.single 0 1 + (a 2 * b 0 - a 0 * b 2) • Pi.single 1 1 +
      (a 0 * b 1 - a 1 * b 0) • Pi.single 2 1 := by
  ext i
  fin_cases i <;> simp [cross_apply]

/-- DLMF 1.6.9: `‖a × b‖ = ‖a‖ ‖b‖ sin θ`, `θ` the angle between `a` and `b`. -/
@[dlmf 1.6.E9]
theorem vecNorm_cross (a b : Fin 3 → ℝ) :
    vecNorm (a ⨯₃ b) = vecNorm a * vecNorm b *
      Real.sin (InnerProductGeometry.angle (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin 3))
        (WithLp.toLp 2 b)) := by
  rw [mul_comm, vecNorm_eq_norm a, vecNorm_eq_norm b,
    InnerProductGeometry.sin_angle_mul_norm_mul_norm]
  simp only [g1b_inner_toLp, vecNorm, cross_dot_cross, dotProduct_comm b a]

/-- DLMF 1.6.9: `n = (a × b)/‖a × b‖` is normal to `a` and `b`, and `(a, b, a × b)` is
right-handed: `det (a, b, a × b) = ‖a × b‖² ≥ 0`. -/
@[dlmf 1.6.E9]
theorem cross_orthogonal_rightHanded (a b : Fin 3 → ℝ) :
    a ⬝ᵥ (a ⨯₃ b) = 0 ∧ b ⬝ᵥ (a ⨯₃ b) = 0 ∧
      Matrix.det ![a, b, a ⨯₃ b] = vecNorm (a ⨯₃ b) ^ 2 := by
  refine ⟨dot_self_cross a b, dot_cross_self a b, ?_⟩
  rw [← triple_product_eq_det, triple_product_permutation, triple_product_permutation, vecNorm,
    Real.sq_sqrt]
  simp only [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- DLMF §1.6(i): the volume of the parallelepiped with edges `a`, `b`, `c` is
`|a · (b × c)|`. -/
@[dlmf 1.6.i]
theorem volume_parallelepiped_eq_abs_triple_product (a b c : Fin 3 → ℝ) :
    volume (parallelepiped ![a, b, c]) = ENNReal.ofReal |a ⬝ᵥ (b ⨯₃ c)| := by
  rw [← addHaarMeasure_eq_volume_pi, ← Module.Basis.parallelepiped_basisFun,
    ← Module.Basis.addHaar_def, MeasureTheory.Measure.addHaar_parallelepiped, Pi.basisFun_det,
    triple_product_eq_det]
  rfl

/-- DLMF §1.6(i): the area (two-dimensional Hausdorff measure in `EuclideanSpace ℝ (Fin 3)`)
of the parallelogram with sides `a` and `b` is `‖a × b‖`. -/
@[dlmf 1.6.i]
theorem hausdorffMeasure_parallelogram (a b : Fin 3 → ℝ) :
    Measure.hausdorffMeasure 2
        ((fun st : ℝ × ℝ => (WithLp.toLp 2 (st.1 • a + st.2 • b) : EuclideanSpace ℝ (Fin 3))) ''
          (Icc 0 1 ×ˢ Icc 0 1)) =
      ENNReal.ofReal (vecNorm (a ⨯₃ b)) := by
  sorry

/-! ### §1.6(ii) Levi-Civita symbol -/

/-- DLMF 1.6.14: on a permutation `(j, k, ℓ) = (σ 1, σ 2, σ 3)` of `(1, 2, 3)` the Levi-Civita
symbol is the sign of `σ`. -/
@[dlmf 1.6.E14]
theorem leviCivita_perm (σ : Equiv.Perm (Fin 3)) :
    leviCivita (σ 0) (σ 1) (σ 2) = (Equiv.Perm.sign σ : ℤ) := by
  revert σ
  decide

/-- DLMF 1.6.14: the Levi-Civita symbol vanishes when two indices coincide. -/
@[dlmf 1.6.E14]
theorem leviCivita_eq_zero_of_not_injective {j k l : Fin 3} (h : j = k ∨ k = l ∨ l = j) :
    leviCivita j k l = 0 := by
  rcases h with rfl | rfl | rfl <;> simp [leviCivita]

/-- DLMF 1.6.15: `ε₁₂₃ = ε₃₁₂ = 1`, `ε₂₁₃ = ε₃₂₁ = -1`, `ε₂₂₁ = 0`. -/
@[dlmf 1.6.E15]
theorem leviCivita_values :
    leviCivita 0 1 2 = 1 ∧ leviCivita 2 0 1 = 1 ∧ leviCivita 1 0 2 = -1 ∧
      leviCivita 2 1 0 = -1 ∧ leviCivita 1 1 0 = 0 := by
  decide

/-- DLMF 1.6.16: `∑_ℓ ε_{jkℓ} ε_{ℓmn} = δ_{jm} δ_{kn} - δ_{jn} δ_{km}`. -/
@[dlmf 1.6.E16]
theorem sum_leviCivita_mul_leviCivita (j k m n : Fin 3) :
    ∑ l, leviCivita j k l * leviCivita l m n =
      (if j = m then 1 else 0) * (if k = n then 1 else 0) -
        (if j = n then 1 else 0) * (if k = m then 1 else 0) := by
  revert j k m n
  decide

/-- DLMF 1.6.17: `e_j × e_k = ∑_ℓ ε_{jkℓ} e_ℓ`. -/
@[dlmf 1.6.E17]
theorem single_cross_single (j k : Fin 3) :
    (Pi.single j 1 : Fin 3 → ℝ) ⨯₃ Pi.single k 1 =
      ∑ l, (leviCivita j k l : ℝ) • (Pi.single l 1 : Fin 3 → ℝ) := by
  fin_cases j <;> fin_cases k <;> ext i <;> fin_cases i <;>
    simp [cross_apply, Pi.single_apply, leviCivita]

/-- DLMF 1.6.18: `a × b = ∑_{j,k,ℓ} ε_{jkℓ} a_j b_k e_ℓ`, componentwise. -/
@[dlmf 1.6.E18]
theorem cross_apply_eq_sum_leviCivita (a b : Fin 3 → ℝ) (l : Fin 3) :
    (a ⨯₃ b) l = ∑ j, ∑ k, (leviCivita j k l : ℝ) * a j * b k := by
  fin_cases l <;> simp [cross_apply, Fin.sum_univ_three, leviCivita] <;> ring

/-- DLMF §1.6(ii): the triple product is `a · (b × c) = ∑ ε_{jkℓ} a_j b_k c_ℓ`, so the volume of
the parallelepiped with edges `a, b, c` is `|ε_{jkℓ} a_j b_k c_ℓ|`. -/
@[dlmf 1.6.ii]
theorem triple_product_eq_sum_leviCivita (a b c : Fin 3 → ℝ) :
    a ⬝ᵥ (b ⨯₃ c) = ∑ j, ∑ k, ∑ l, (leviCivita j k l : ℝ) * a j * b k * c l := by
  simp [dotProduct, cross_apply, Fin.sum_univ_three, leviCivita]
  ring

/-! ### Calculus of partial derivatives -/

section PartialCalculus

variable {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}

/-- The section of a differentiable function has the partial derivative as derivative. -/
lemma g1b_hasDerivAt_sec (i : Fin n) (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t => f (Function.update x i t)) (partialDeriv i f x) (x i) := by
  rw [partialDeriv_eq_fderiv i hf]
  exact hasDerivAt_partialDeriv i hf

lemma g1b_partialDeriv_add (i : Fin n) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    partialDeriv i (fun y => f y + g y) x = partialDeriv i f x + partialDeriv i g x :=
  ((g1b_hasDerivAt_sec i hf).add (g1b_hasDerivAt_sec i hg)).deriv

lemma g1b_partialDeriv_sub (i : Fin n) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    partialDeriv i (fun y => f y - g y) x = partialDeriv i f x - partialDeriv i g x :=
  ((g1b_hasDerivAt_sec i hf).sub (g1b_hasDerivAt_sec i hg)).deriv

lemma g1b_partialDeriv_mul (i : Fin n) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    partialDeriv i (fun y => f y * g y) x =
      partialDeriv i f x * g x + f x * partialDeriv i g x := by
  have h := (g1b_hasDerivAt_sec i hf).mul (g1b_hasDerivAt_sec i hg)
  rw [Function.update_eq_self] at h
  exact h.deriv

lemma g1b_partialDeriv_div (i : Fin n) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hx : g x ≠ 0) :
    partialDeriv i (fun y => f y / g y) x =
      (partialDeriv i f x * g x - f x * partialDeriv i g x) / g x ^ 2 := by
  have h := (g1b_hasDerivAt_sec i hf).div (g1b_hasDerivAt_sec i hg)
    (by simpa [Function.update_eq_self] using hx)
  rw [Function.update_eq_self] at h
  exact h.deriv

/-- `partialDeriv i` at `x` only depends on the germ at `x`. -/
lemma g1b_partialDeriv_congr (i : Fin n) (h : f =ᶠ[𝓝 x] g) :
    partialDeriv i f x = partialDeriv i g x := by
  have hc : ContinuousAt (Function.update x i) (x i) :=
    (hasDerivAt_update x i (x i)).continuousAt
  have h' : f =ᶠ[𝓝 (Function.update x i (x i))] g := by rwa [Function.update_eq_self]
  have h2 : (fun t => f (Function.update x i t)) =ᶠ[𝓝 (x i)]
      fun t => g (Function.update x i t) := hc.eventually h'
  exact h2.deriv_eq

/-- Partial derivatives of a `C²` function are differentiable. -/
theorem g1b_differentiableAt_partialDeriv (j : Fin n) (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (fun y => partialDeriv j f y) x := by
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  rw [(g1b_partialDeriv_eventuallyEq j hev).differentiableAt_iff]
  exact ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).clm_apply
    (differentiableAt_const _)

/-- Partial derivatives of a `C²` function are `C¹`. -/
lemma g1b_contDiffAt_partialDeriv (j : Fin n) (hf : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 1 (fun y => partialDeriv j f y) x := by
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  exact ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).congr_of_eventuallyEq
    (g1b_partialDeriv_eventuallyEq j hev)

end PartialCalculus

/-! ### §1.6(iii) Vector-valued functions -/

/-- DLMF 1.6.23: `∇(fg) = f ∇g + g ∇f`. -/
@[dlmf 1.6.E23]
theorem grad_mul {f g : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    grad (fun y => f y * g y) x = f x • grad g x + g x • grad f x := by
  ext i
  simp only [grad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, g1b_partialDeriv_mul i hf hg]
  ring

/-- DLMF 1.6.24: `∇(f/g) = (g ∇f - f ∇g)/g²`, where `g ≠ 0`. -/
@[dlmf 1.6.E24]
theorem grad_div {f g : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hx : g x ≠ 0) :
    grad (fun y => f y / g y) x = (g x ^ 2)⁻¹ • (g x • grad f x - f x • grad g x) := by
  ext i
  simp only [grad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, g1b_partialDeriv_div i hf hg hx]
  field_simp

/-- DLMF 1.6.25: `∇ · (fF) = f (∇ · F) + F · ∇f`. -/
@[dlmf 1.6.E25]
theorem divergence_smul {f : (Fin 3 → ℝ) → ℝ} {F : (Fin 3 → ℝ) → Fin 3 → ℝ} {x : Fin 3 → ℝ}
    (hf : DifferentiableAt ℝ f x) (hF : DifferentiableAt ℝ F x) :
    divergence (fun y => f y • F y) x = f x * divergence F x + F x ⬝ᵥ grad f x := by
  have hFi := differentiableAt_pi.mp hF
  simp only [divergence, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, dotProduct, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [g1b_partialDeriv_mul i hf (hFi i)]
  simp only [grad]
  ring

/-- DLMF 1.6.26: `∇ · (F × G) = G · (∇ × F) - F · (∇ × G)`. -/
@[dlmf 1.6.E26]
theorem divergence_cross {F G : (Fin 3 → ℝ) → Fin 3 → ℝ} {x : Fin 3 → ℝ}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun y => F y ⨯₃ G y) x = G x ⬝ᵥ curl F x - F x ⬝ᵥ curl G x := by
  have hFi := differentiableAt_pi.mp hF
  have hGi := differentiableAt_pi.mp hG
  have hm : ∀ i j, DifferentiableAt ℝ (fun y => F y i * G y j) x :=
    fun i j => (hFi i).mul (hGi j)
  simp only [divergence, curl, cross_apply, Fin.sum_univ_three, dotProduct]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [g1b_partialDeriv_sub 0 (hm 1 2) (hm 2 1),
    g1b_partialDeriv_sub 1 (hm 2 0) (hm 0 2),
    g1b_partialDeriv_sub 2 (hm 0 1) (hm 1 0),
    g1b_partialDeriv_mul 0 (hFi 1) (hGi 2), g1b_partialDeriv_mul 0 (hFi 2) (hGi 1),
    g1b_partialDeriv_mul 1 (hFi 2) (hGi 0), g1b_partialDeriv_mul 1 (hFi 0) (hGi 2),
    g1b_partialDeriv_mul 2 (hFi 0) (hGi 1), g1b_partialDeriv_mul 2 (hFi 1) (hGi 0)]
  ring

/-- DLMF 1.6.27: `∇ · (∇ × F) = div curl F = 0` for `F` of class `C²` at `x`. -/
@[dlmf 1.6.E27]
theorem divergence_curl {F : (Fin 3 → ℝ) → Fin 3 → ℝ} {x : Fin 3 → ℝ}
    (hF : ContDiffAt ℝ 2 F x) : divergence (curl F) x = 0 := by
  have hFi := contDiffAt_pi.mp hF
  have hd : ∀ i j, DifferentiableAt ℝ (fun y => partialDeriv j (fun z => F z i) y) x :=
    fun i j => g1b_differentiableAt_partialDeriv j (hFi i)
  simp only [divergence, curl, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [g1b_partialDeriv_sub 0 (hd 2 1) (hd 1 2), g1b_partialDeriv_sub 1 (hd 0 2) (hd 2 0),
    g1b_partialDeriv_sub 2 (hd 1 0) (hd 0 1), partialDeriv_comm 0 1 (hFi 2),
    partialDeriv_comm 0 2 (hFi 1), partialDeriv_comm 1 2 (hFi 0)]
  ring

/-- DLMF 1.6.28: `∇ × (fF) = f (∇ × F) + (∇f) × F`. -/
@[dlmf 1.6.E28]
theorem curl_smul {f : (Fin 3 → ℝ) → ℝ} {F : (Fin 3 → ℝ) → Fin 3 → ℝ} {x : Fin 3 → ℝ}
    (hf : DifferentiableAt ℝ f x) (hF : DifferentiableAt ℝ F x) :
    curl (fun y => f y • F y) x = f x • curl F x + grad f x ⨯₃ F x := by
  have hFi := differentiableAt_pi.mp hF
  ext i
  fin_cases i <;>
  · simp only [curl, grad, Pi.smul_apply, smul_eq_mul, Pi.add_apply, cross_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    rw [g1b_partialDeriv_mul _ hf (hFi _), g1b_partialDeriv_mul _ hf (hFi _)]
    ring

/-- DLMF 1.6.29: `∇ × (∇f) = curl grad f = 0` for `f` of class `C²` at `x`. -/
@[dlmf 1.6.E29]
theorem curl_grad {f : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ} (hf : ContDiffAt ℝ 2 f x) :
    curl (grad f) x = 0 := by
  ext i
  fin_cases i <;>
  · simp only [curl, grad, Pi.zero_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    rw [partialDeriv_comm _ _ hf, sub_self]

/-- DLMF 1.6.30: `∇²f = ∇ · (∇f)`. -/
@[dlmf 1.6.E30]
theorem laplacian_eq_divergence_grad (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    laplacian f x = divergence (grad f) x :=
  rfl

/-- DLMF 1.6.31: `∇²(fg) = f ∇²g + g ∇²f + 2 ∇f · ∇g` for `f`, `g` of class `C²` at `x`. -/
@[dlmf 1.6.E31]
theorem laplacian_mul {f g : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    laplacian (fun y => f y * g y) x =
      f x * laplacian g x + g x * laplacian f x + 2 * (grad f x ⬝ᵥ grad g x) := by
  have hfe := (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hge := (hg.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hf1 := hf.differentiableAt (by simp)
  have hg1 := hg.differentiableAt (by simp)
  have key : ∀ i, partialDeriv i (fun y => partialDeriv i (fun z => f z * g z) y) x =
      partialDeriv i (fun y => partialDeriv i f y) x * g x +
        2 * (partialDeriv i f x * partialDeriv i g x) +
        f x * partialDeriv i (fun y => partialDeriv i g y) x := by
    intro i
    have hev : (fun y => partialDeriv i (fun z => f z * g z) y) =ᶠ[𝓝 x]
        fun y => partialDeriv i f y * g y + f y * partialDeriv i g y := by
      filter_upwards [hfe, hge] with y hfy hgy using g1b_partialDeriv_mul i hfy hgy
    have hA : DifferentiableAt ℝ (fun y => partialDeriv i f y * g y) x :=
      (g1b_differentiableAt_partialDeriv i hf).mul hg1
    have hB : DifferentiableAt ℝ (fun y => f y * partialDeriv i g y) x :=
      hf1.mul (g1b_differentiableAt_partialDeriv i hg)
    rw [g1b_partialDeriv_congr i hev, g1b_partialDeriv_add i hA hB,
      g1b_partialDeriv_mul i (g1b_differentiableAt_partialDeriv i hf) hg1,
      g1b_partialDeriv_mul i hf1 (g1b_differentiableAt_partialDeriv i hg)]
    ring
  simp only [laplacian, grad, dotProduct, key]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- DLMF 1.6.32: `∇ · (∇f × ∇g) = 0` for `f`, `g` of class `C²` at `x`. -/
@[dlmf 1.6.E32]
theorem divergence_grad_cross_grad {f g : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    divergence (fun y => grad f y ⨯₃ grad g y) x = 0 := by
  have hdf : DifferentiableAt ℝ (grad f) x :=
    differentiableAt_pi.mpr fun j => g1b_differentiableAt_partialDeriv j hf
  have hdg : DifferentiableAt ℝ (grad g) x :=
    differentiableAt_pi.mpr fun j => g1b_differentiableAt_partialDeriv j hg
  rw [divergence_cross hdf hdg, curl_grad hf, curl_grad hg]
  simp

/-- The divergence of a difference. -/
lemma g1b_divergence_sub {F G : (Fin 3 → ℝ) → Fin 3 → ℝ} {x : Fin 3 → ℝ}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun y => F y - G y) x = divergence F x - divergence G x := by
  have hFi := differentiableAt_pi.mp hF
  have hGi := differentiableAt_pi.mp hG
  simp only [divergence, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => g1b_partialDeriv_sub i (hFi i) (hGi i)

/-- DLMF 1.6.33: `∇ · (f ∇g - g ∇f) = f ∇²g - g ∇²f` for `f`, `g` of class `C²` at `x`. -/
@[dlmf 1.6.E33]
theorem divergence_smul_grad_sub {f g : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    divergence (fun y => f y • grad g y - g y • grad f y) x =
      f x * laplacian g x - g x * laplacian f x := by
  have hf1 := hf.differentiableAt (by simp)
  have hg1 := hg.differentiableAt (by simp)
  have hdf : DifferentiableAt ℝ (grad f) x :=
    differentiableAt_pi.mpr fun j => g1b_differentiableAt_partialDeriv j hf
  have hdg : DifferentiableAt ℝ (grad g) x :=
    differentiableAt_pi.mpr fun j => g1b_differentiableAt_partialDeriv j hg
  have hA : DifferentiableAt ℝ (fun y => f y • grad g y) x := hf1.smul hdg
  have hB : DifferentiableAt ℝ (fun y => g y • grad f y) x := hg1.smul hdf
  rw [g1b_divergence_sub hA hB, divergence_smul hf1 hdg,
    divergence_smul hg1 hdf, laplacian_eq_divergence_grad, laplacian_eq_divergence_grad,
    dotProduct_comm (grad g x)]
  ring

/-- DLMF 1.6.34: `∇ × (∇ × F) = ∇(∇ · F) - ∇²F` for `F` of class `C²` at `x`. -/
@[dlmf 1.6.E34]
theorem curl_curl {F : (Fin 3 → ℝ) → Fin 3 → ℝ} {x : Fin 3 → ℝ} (hF : ContDiffAt ℝ 2 F x) :
    curl (curl F) x = grad (divergence F) x - vectorLaplacian F x := by
  have hFi := contDiffAt_pi.mp hF
  have hd : ∀ i j, DifferentiableAt ℝ (fun y => partialDeriv j (fun z => F z i) y) x :=
    fun i j => g1b_differentiableAt_partialDeriv j (hFi i)
  have hsub : ∀ k i j i' j', partialDeriv k (fun y => partialDeriv j (fun z => F z i) y -
      partialDeriv j' (fun z => F z i') y) x =
      partialDeriv k (fun y => partialDeriv j (fun z => F z i) y) x -
        partialDeriv k (fun y => partialDeriv j' (fun z => F z i') y) x :=
    fun k i j i' j' => g1b_partialDeriv_sub k (hd i j) (hd i' j')
  have hadd : ∀ k, partialDeriv k (fun y => partialDeriv 0 (fun z => F z 0) y +
      partialDeriv 1 (fun z => F z 1) y + partialDeriv 2 (fun z => F z 2) y) x =
      partialDeriv k (fun y => partialDeriv 0 (fun z => F z 0) y) x +
        partialDeriv k (fun y => partialDeriv 1 (fun z => F z 1) y) x +
        partialDeriv k (fun y => partialDeriv 2 (fun z => F z 2) y) x := fun k => by
    have h01 : DifferentiableAt ℝ (fun y => partialDeriv 0 (fun z => F z 0) y +
        partialDeriv 1 (fun z => F z 1) y) x := (hd 0 0).add (hd 1 1)
    rw [g1b_partialDeriv_add k h01 (hd 2 2),
      g1b_partialDeriv_add k (hd 0 0) (hd 1 1)]
  have hdiv : divergence F = fun y => partialDeriv 0 (fun z => F z 0) y +
      partialDeriv 1 (fun z => F z 1) y + partialDeriv 2 (fun z => F z 2) y :=
    funext fun y => by simp [divergence, Fin.sum_univ_three]
  have hcomm : ∀ i j k, partialDeriv i (fun y => partialDeriv j (fun z => F z k) y) x =
      partialDeriv j (fun y => partialDeriv i (fun z => F z k) y) x :=
    fun i j k => partialDeriv_comm i j (hFi k)
  ext i
  fin_cases i
  · simp only [curl, grad, vectorLaplacian, laplacian, Fin.sum_univ_three,
      Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, hdiv, hsub, hadd]
    rw [hcomm 1 0 1, hcomm 2 0 2]; ring
  · simp only [curl, grad, vectorLaplacian, laplacian, Fin.sum_univ_three,
      Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.mk_one, hdiv, hsub, hadd]
    rw [hcomm 2 1 2, hcomm 0 1 0]; ring
  · simp only [curl, grad, vectorLaplacian, laplacian, Fin.sum_univ_three,
      Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.reduceFinMk, hdiv, hsub, hadd]
    rw [hcomm 0 2 0, hcomm 1 2 1]; ring

end DLMF.AlgebraicAnalytic
