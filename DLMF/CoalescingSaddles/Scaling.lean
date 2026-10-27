/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Scaling relations (DLMF §36.6)

Statements acquired from the NIST DLMF (version 1.2.8), checked 2026-10-26.

The diffraction catastrophes `Ψ(x; k)` (36.2.10, 36.2.11) are expressed through the canonical
integrals at scaled coordinates (36.6.1): with `t = k^{-1/(K+2)} τ`, the phase `kΦ_K(t; x)`
becomes `Φ_K(τ; y(k))`. The proofs are linear changes of variables in the defining contour
integrals (`MeasureTheory.Measure.integral_comp_mul_left`, `integral_comp_smul`,
`setIntegral_comp_smul_of_pos`); the rotated contours are invariant under positive scaling. The
exponents (36.6.3–36.6.5) are defined in `DLMF.CoalescingSaddles.Basic`; their sums and the
special cases of Table 36.6.1 are proved here.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set
open scoped Real Pointwise

namespace DLMF.CoalescingSaddles

/-! ### Scaling of contours and potentials -/

lemma s36a_dir_smul (K : ℕ) {c : ℝ} (hc : 0 < c) (r : ℝ) :
    cuspoidContourDir K (c * r) = cuspoidContourDir K r := by
  unfold cuspoidContourDir
  simp only [mul_nonneg_iff_of_pos_left hc]

lemma s36a_contour_smul (K : ℕ) {c : ℝ} (hc : 0 < c) (r : ℝ) :
    cuspoidContour K (c * r) = (c : ℂ) * cuspoidContour K r := by
  unfold cuspoidContour
  rw [s36a_dir_smul K hc]; push_cast; ring

lemma s36a_rpow_root_pow {k : ℝ} (hk : 0 < k) (n : ℕ) (hn : 0 < n) :
    (k ^ (1 / (n : ℝ))) ^ n = k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hk.le, one_div_mul_cancel (by exact_mod_cast hn.ne'),
    Real.rpow_one]

lemma s36a_rpow_root_pow_mul {k : ℝ} (hk : 0 < k) (n m : ℕ) (hn : 0 < n) :
    (k ^ (1 / (n : ℝ))) ^ m * k ^ (1 - (m : ℝ) / n) = k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hk.le, ← Real.rpow_add hk]
  convert Real.rpow_one k using 2
  field_simp; ring

/-- `k Φ_K(w; x) = Φ_K(k^{1/(K+2)} w; y(k))` (the substitution behind DLMF 36.6.1). -/
lemma s36a_cuspoid_potential_scale (K : ℕ) (x : Fin K → ℝ) {k : ℝ} (hk : 0 < k) (w : ℂ) :
    (k : ℂ) * cuspoidPotential K w x =
      cuspoidPotential K (((k ^ (1 / ((K : ℝ) + 2)) : ℝ) : ℂ) * w)
        (cuspoidScaledCoords K x k) := by
  set c : ℝ := k ^ (1 / ((K : ℝ) + 2)) with hc
  have hc1 : c ^ (K + 2) = k := by
    have := s36a_rpow_root_pow hk (K + 2) (by omega); push_cast at this; exact this
  have hc2 : ∀ m : Fin K, c ^ ((m : ℕ) + 1) * k ^ cuspoidCoordinateIndex ((m : ℕ) + 1) K = k := by
    intro m
    have := s36a_rpow_root_pow_mul hk (K + 2) ((m : ℕ) + 1) (by omega)
    unfold cuspoidCoordinateIndex; push_cast at this ⊢; exact this
  unfold cuspoidPotential cuspoidScaledCoords
  rw [mul_add, Finset.mul_sum, mul_pow, ← ofReal_pow, hc1]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow, ← ofReal_pow, ← (by exact_mod_cast hc2 m :
    ((c ^ ((m : ℕ) + 1) * k ^ cuspoidCoordinateIndex ((m : ℕ) + 1) K : ℝ) : ℂ) = k)]
  push_cast; ring

/-- The scaling law of the cuspoid diffraction catastrophes (DLMF 36.6.1, cuspoids):
`Ψ_K(x; k) = k^{β_K} Ψ_K(y(k))` for `k > 0`, with `β_K = K/(2(K+2))` (36.6.3) and
`y(k) = (x_m k^{γ_{mK}})` (36.6.2, 36.6.4). -/
@[dlmf 36.6.E1]
theorem cuspoidDiffraction_eq_scale (K : ℕ) (x : Fin K → ℝ) {k : ℝ} (hk : 0 < k) :
    cuspoidDiffraction K x k =
      ((k ^ cuspoidSingularityIndex K : ℝ) : ℂ) *
        cuspoidIntegral K (cuspoidScaledCoords K x k) := by
  set c : ℝ := k ^ (1 / ((K : ℝ) + 2)) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos hk _
  have hint : ∫ r : ℝ, cuspoidContourDir K r *
      exp (I * (k : ℂ) * cuspoidPotential K (cuspoidContour K r) x) =
      ∫ r : ℝ, (fun ρ => cuspoidContourDir K ρ * exp (I * cuspoidPotential K (cuspoidContour K ρ)
        (cuspoidScaledCoords K x k))) (c * r) := by
    congr 1; funext r
    simp only
    rw [s36a_dir_smul K hcpos, s36a_contour_smul K hcpos, mul_assoc I,
      s36a_cuspoid_potential_scale K x hk]
  unfold cuspoidDiffraction cuspoidIntegral
  rw [hint, Measure.integral_comp_mul_left (fun ρ => cuspoidContourDir K ρ *
    exp (I * cuspoidPotential K (cuspoidContour K ρ) (cuspoidScaledCoords K x k))) c,
    abs_of_pos (inv_pos.2 hcpos), real_smul, ← mul_assoc]
  congr 1
  rw [← ofReal_mul]
  congr 1
  rw [hc, ← Real.rpow_neg hk.le, Real.sqrt_eq_rpow, ← Real.rpow_add hk]
  unfold cuspoidSingularityIndex
  congr 1
  field_simp; ring

lemma s36a_umbilic_coeffs {k : ℝ} (hk : 0 < k) :
    (k ^ (1 / (3 : ℝ))) ^ 3 = k ∧ k ^ (1 / (3 : ℝ)) * k ^ ((2 : ℝ) / 3) = k ∧
      (k ^ (1 / (3 : ℝ))) ^ 2 * k ^ ((1 : ℝ) / 3) = k := by
  have h1 := s36a_rpow_root_pow hk 3 (by norm_num)
  have h2 := s36a_rpow_root_pow_mul hk 3 1 (by norm_num)
  have h3 := s36a_rpow_root_pow_mul hk 3 2 (by norm_num)
  push_cast at h1 h2 h3
  refine ⟨h1, ?_, ?_⟩
  · rw [pow_one] at h2; convert h2 using 3; norm_num
  · convert h3 using 3; norm_num

/-- `k Φ^{(H)}(s, t; x) = Φ^{(H)}(k^{1/3}s, k^{1/3}t; y^{(U)}(k))`. -/
lemma s36a_hyperbolic_potential_scale (x y z : ℝ) {k : ℝ} (hk : 0 < k) (s t : ℂ) :
    (k : ℂ) * hyperbolicUmbilicPotential s t x y z =
      hyperbolicUmbilicPotential (((k ^ (1 / (3 : ℝ)) : ℝ) : ℂ) * s)
        (((k ^ (1 / (3 : ℝ)) : ℝ) : ℂ) * t) (x * k ^ umbilicCoordinateIndex 0)
        (y * k ^ umbilicCoordinateIndex 1) (z * k ^ umbilicCoordinateIndex 2) := by
  obtain ⟨h1, h2, h3⟩ := s36a_umbilic_coeffs hk
  set c : ℝ := k ^ (1 / (3 : ℝ))
  have e1 : (k : ℂ) = (c : ℂ) ^ 3 := by rw [← ofReal_pow, h1]
  have e2 : (k : ℂ) = (c : ℂ) * ((k ^ ((2 : ℝ) / 3) : ℝ) : ℂ) := by rw [← ofReal_mul, h2]
  have e3 : (k : ℂ) = (c : ℂ) ^ 2 * ((k ^ ((1 : ℝ) / 3) : ℝ) : ℂ) := by
    rw [← ofReal_pow, ← ofReal_mul, h3]
  simp only [umbilicCoordinateIndex, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hyperbolicUmbilicPotential]
  push_cast
  linear_combination (s ^ 3 + t ^ 3) * e1 + (y * t + x * s) * e2 + (z * s * t) * e3

/-- `k Φ^{(E)}(s, t; x) = Φ^{(E)}(k^{1/3}s, k^{1/3}t; y^{(U)}(k))`. -/
lemma s36a_elliptic_potential_scale (x y z : ℝ) {k : ℝ} (hk : 0 < k) (s t : ℂ) :
    (k : ℂ) * ellipticUmbilicPotential s t x y z =
      ellipticUmbilicPotential (((k ^ (1 / (3 : ℝ)) : ℝ) : ℂ) * s)
        (((k ^ (1 / (3 : ℝ)) : ℝ) : ℂ) * t) (x * k ^ umbilicCoordinateIndex 0)
        (y * k ^ umbilicCoordinateIndex 1) (z * k ^ umbilicCoordinateIndex 2) := by
  obtain ⟨h1, h2, h3⟩ := s36a_umbilic_coeffs hk
  set c : ℝ := k ^ (1 / (3 : ℝ))
  have e1 : (k : ℂ) = (c : ℂ) ^ 3 := by rw [← ofReal_pow, h1]
  have e2 : (k : ℂ) = (c : ℂ) * ((k ^ ((2 : ℝ) / 3) : ℝ) : ℂ) := by rw [← ofReal_mul, h2]
  have e3 : (k : ℂ) = (c : ℂ) ^ 2 * ((k ^ ((1 : ℝ) / 3) : ℝ) : ℂ) := by
    rw [← ofReal_pow, ← ofReal_mul, h3]
  simp only [umbilicCoordinateIndex, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ellipticUmbilicPotential]
  push_cast
  linear_combination (s ^ 3 - 3 * s * t ^ 2) * e1 + (y * t + x * s) * e2 +
    (z * (s ^ 2 + t ^ 2)) * e3

lemma s36a_finrank_prod : Module.finrank ℝ (ℝ × ℝ) = 2 := by
  rw [Module.finrank_prod, Module.finrank_self]

lemma s36a_umbilic_prefactor {k : ℝ} (hk : 0 < k) :
    k * ((k ^ (1 / (3 : ℝ))) ^ 2)⁻¹ = k ^ umbilicSingularityIndex := by
  have h : ((k ^ (1 / (3 : ℝ))) ^ 2)⁻¹ = k ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk.le, ← Real.rpow_neg hk.le]; norm_num
  rw [h, umbilicSingularityIndex, show (1 / 3 : ℝ) = 1 + -(2 / 3) by norm_num,
    Real.rpow_add hk, Real.rpow_one]

instance s36a_isAddHaar_prod : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

/-- The scaling law of the hyperbolic umbilic diffraction catastrophe (DLMF 36.6.1, umbilics):
`Ψ^{(H)}(x; k) = k^{β^{(U)}} Ψ^{(H)}(y^{(U)}(k))` for `k > 0`, with `β^{(U)} = 1/3` and
`y^{(U)}(k) = (x k^{2/3}, y k^{2/3}, z k^{1/3})` (36.6.2–36.6.4). -/
@[dlmf 36.6.E1]
theorem hyperbolicUmbilicDiffraction_eq_scale (x y z : ℝ) {k : ℝ} (hk : 0 < k) :
    hyperbolicUmbilicDiffraction x y z k =
      ((k ^ umbilicSingularityIndex : ℝ) : ℂ) *
        hyperbolicUmbilicIntegral (x * k ^ umbilicCoordinateIndex 0)
          (y * k ^ umbilicCoordinateIndex 1) (z * k ^ umbilicCoordinateIndex 2) := by
  set c : ℝ := k ^ (1 / (3 : ℝ)) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos hk _
  set g : ℝ × ℝ → ℂ := fun q => cuspoidContourDir 1 q.1 * cuspoidContourDir 1 q.2 *
    exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 q.1) (cuspoidContour 1 q.2)
      (x * k ^ umbilicCoordinateIndex 0) (y * k ^ umbilicCoordinateIndex 1)
      (z * k ^ umbilicCoordinateIndex 2)) with hg
  have hint : ∫ p : ℝ × ℝ, cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
      exp (I * (k : ℂ) *
        hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y z) =
      ∫ p : ℝ × ℝ, g (c • p) := by
    congr 1; funext p
    simp only [hg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [s36a_dir_smul 1 hcpos, s36a_dir_smul 1 hcpos, s36a_contour_smul 1 hcpos,
      s36a_contour_smul 1 hcpos, mul_assoc I, s36a_hyperbolic_potential_scale x y z hk]
  unfold hyperbolicUmbilicDiffraction hyperbolicUmbilicIntegral
  rw [hint, Measure.integral_comp_smul, s36a_finrank_prod,
    abs_of_pos (inv_pos.2 (pow_pos hcpos 2)), real_smul, ← mul_assoc, ← ofReal_mul,
    s36a_umbilic_prefactor hk]

lemma s36a_smul_quadrant {c : ℝ} (hc : 0 < c) :
    c • (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) = Ioi 0 ×ˢ Ioi 0 := by
  ext p
  rw [mem_smul_set_iff_inv_smul_mem₀ hc.ne']
  simp only [mem_prod, mem_Ioi, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa [hc] using (mul_pos_iff_of_pos_left (inv_pos.2 hc)).1 h1,
      by simpa [hc] using (mul_pos_iff_of_pos_left (inv_pos.2 hc)).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_pos (inv_pos.2 hc) h1, mul_pos (inv_pos.2 hc) h2⟩

lemma s36a_quadrant_scale (x y z : ℝ) {k : ℝ} (hk : 0 < k) (j l : Fin 3) :
    ellipticUmbilicQuadrant k x y z j l =
      (((k ^ (1 / (3 : ℝ))) ^ 2)⁻¹ : ℝ) * ellipticUmbilicQuadrant 1
        (x * k ^ umbilicCoordinateIndex 0) (y * k ^ umbilicCoordinateIndex 1)
        (z * k ^ umbilicCoordinateIndex 2) j l := by
  set c : ℝ := k ^ (1 / (3 : ℝ)) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos hk _
  set g : ℝ × ℝ → ℂ := fun q => ellipticUmbilicRayDir j * ellipticUmbilicRayDir l *
    exp (I * ((1 : ℝ) : ℂ) * ellipticUmbilicPotentialAB ((q.1 : ℂ) * ellipticUmbilicRayDir j)
      ((q.2 : ℂ) * ellipticUmbilicRayDir l) (x * k ^ umbilicCoordinateIndex 0)
      (y * k ^ umbilicCoordinateIndex 1) (z * k ^ umbilicCoordinateIndex 2)) with hg
  unfold ellipticUmbilicQuadrant
  have hint : ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioi 0, ellipticUmbilicRayDir j * ellipticUmbilicRayDir l *
      exp (I * (k : ℂ) * ellipticUmbilicPotentialAB ((p.1 : ℂ) * ellipticUmbilicRayDir j)
        ((p.2 : ℂ) * ellipticUmbilicRayDir l) x y z) =
      ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioi 0, g (c • p) := by
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi) fun p _ => ?_
    simp only [hg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ofReal_one, mul_one]
    congr 2
    rw [mul_assoc I]
    congr 1
    unfold ellipticUmbilicPotentialAB
    rw [s36a_elliptic_potential_scale x y z hk]
    congr 1 <;> push_cast <;> ring
  rw [hint, Measure.setIntegral_comp_smul_of_pos _ _ _ hcpos, s36a_finrank_prod,
    s36a_smul_quadrant hcpos, real_smul]

/-- The scaling law of the elliptic umbilic diffraction catastrophe (DLMF 36.6.1, umbilics):
`Ψ^{(E)}(x; k) = k^{β^{(U)}} Ψ^{(E)}(y^{(U)}(k))` for `k > 0`. -/
@[dlmf 36.6.E1]
theorem ellipticUmbilicDiffraction_eq_scale (x y z : ℝ) {k : ℝ} (hk : 0 < k) :
    ellipticUmbilicDiffraction x y z k =
      ((k ^ umbilicSingularityIndex : ℝ) : ℂ) *
        ellipticUmbilicIntegral (x * k ^ umbilicCoordinateIndex 0)
          (y * k ^ umbilicCoordinateIndex 1) (z * k ^ umbilicCoordinateIndex 2) := by
  unfold ellipticUmbilicDiffraction ellipticUmbilicIntegral
  simp only [s36a_quadrant_scale x y z hk]
  rw [← s36a_umbilic_prefactor hk]
  simp only [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ### Scaling exponents (36.6.3–36.6.5, Table 36.6.1) -/

lemma s36a_sum_Icc_cast (K : ℕ) : ∑ m ∈ Finset.Icc 1 K, (m : ℝ) = K * (K + 1) / 2 := by
  induction K with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- The cuspoid hypervolume scaling index `γ_K = ∑_{m=1}^K γ_{mK} = K(K+3)/(2(K+2))`
(DLMF 36.6.5). -/
@[dlmf 36.6.E5]
theorem cuspoidVolumeIndex_eq (K : ℕ) :
    cuspoidVolumeIndex K = K * (K + 3) / (2 * (K + 2)) := by
  unfold cuspoidVolumeIndex cuspoidCoordinateIndex
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, ← Finset.sum_div,
    s36a_sum_Icc_cast]
  simp only [nsmul_eq_mul, mul_one, Nat.add_sub_cancel]
  field_simp; ring

/-- The umbilic hypervolume scaling index `γ^{(U)} = 2/3 + 2/3 + 1/3 = 5/3` (DLMF 36.6.5). -/
@[dlmf 36.6.E5]
theorem umbilicVolumeIndex_eq : umbilicVolumeIndex = 5 / 3 := by
  simp [umbilicVolumeIndex, umbilicCoordinateIndex, Fin.sum_univ_three]; norm_num

/-- Table 36.6.1: the scaling exponents of the fold (`K = 1`): `β₁ = 1/6`, `γ₁₁ = 2/3`,
`γ₁ = 2/3`. -/
@[dlmf 36.6.T1]
theorem scalingExponents_fold :
    cuspoidSingularityIndex 1 = 1 / 6 ∧ cuspoidCoordinateIndex 1 1 = 2 / 3 ∧
      cuspoidVolumeIndex 1 = 2 / 3 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [cuspoidSingularityIndex]; norm_num
  · simp [cuspoidCoordinateIndex]; norm_num
  · rw [cuspoidVolumeIndex_eq]; norm_num

/-- Table 36.6.1: the scaling exponents of the cusp (`K = 2`): `β₂ = 1/4`, `γ₁₂ = 3/4`,
`γ₂₂ = 1/2`, `γ₂ = 5/4`. -/
@[dlmf 36.6.T1]
theorem scalingExponents_cusp :
    cuspoidSingularityIndex 2 = 1 / 4 ∧ cuspoidCoordinateIndex 1 2 = 3 / 4 ∧
      cuspoidCoordinateIndex 2 2 = 1 / 2 ∧ cuspoidVolumeIndex 2 = 5 / 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [cuspoidSingularityIndex]; norm_num
  · simp [cuspoidCoordinateIndex]; norm_num
  · simp [cuspoidCoordinateIndex]; norm_num
  · rw [cuspoidVolumeIndex_eq]; norm_num

/-- Table 36.6.1: the scaling exponents of the swallowtail (`K = 3`): `β₃ = 3/10`,
`γ₁₃ = 4/5`, `γ₂₃ = 3/5`, `γ₃₃ = 2/5`, `γ₃ = 9/5`. -/
@[dlmf 36.6.T1]
theorem scalingExponents_swallowtail :
    cuspoidSingularityIndex 3 = 3 / 10 ∧ cuspoidCoordinateIndex 1 3 = 4 / 5 ∧
      cuspoidCoordinateIndex 2 3 = 3 / 5 ∧ cuspoidCoordinateIndex 3 3 = 2 / 5 ∧
      cuspoidVolumeIndex 3 = 9 / 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [cuspoidSingularityIndex]; norm_num
  · simp [cuspoidCoordinateIndex]; norm_num
  · simp [cuspoidCoordinateIndex]; norm_num
  · simp [cuspoidCoordinateIndex]; norm_num
  · rw [cuspoidVolumeIndex_eq]; norm_num

end DLMF.CoalescingSaddles
