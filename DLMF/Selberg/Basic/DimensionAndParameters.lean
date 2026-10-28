/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Selberg.Basic.IntegrationByParts

/-!
# Selberg dimension recurrences and parameter continuation

Dimension reduction and holomorphic parameter arguments determine the Selberg normalization.

Source references and common attribution are retained in
`DLMF.Selberg.Basic`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter

open scoped Real Topology

noncomputable section

namespace DLMF.Selberg

/-! ### The recursion in the dimension -/

/-- The cross term in the dimension recursion: for `b = 1`,
`∫ t₀ · 2c/(t₀ - tⱼ₊₁) · Φ = c · S_{n+1}(a, 1, c)`. -/
theorem scaling_cross {n : ℕ} {a c : ℂ} (ha : 0 < a.re) (hc : 1 / 2 ≤ c.re) (j : Fin n) :
    ∫ t in cube (n + 1), (t 0 : ℂ) * (2 * c / ((t 0 : ℂ) - t j.succ) *
        selbergIntegrand (n + 1) a 1 c t) = c * selbergInt (n + 1) a 1 c := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (n + 1)), σ = Equiv.swap 0 j.succ := ⟨_, rfl⟩
  have hsw0 : ∀ t : Fin (n + 1) → ℝ, (t ∘ σ) 0 = t j.succ := fun t => by simp [hσ]
  have hsw1 : ∀ t : Fin (n + 1) → ℝ, (t ∘ σ) j.succ = t 0 := fun t => by simp [hσ]
  have h1 : (0 : ℝ) < (1 : ℂ).re := by simp
  have hI : IntegrableOn (fun t => (t 0 : ℂ) * (2 * c / ((t 0 : ℂ) - t j.succ) *
      selbergIntegrand (n + 1) a 1 c t)) (cube (n + 1)) := by
    refine integrableOn_mul_div_selbergIntegrand ha h1 hc j (M := 1) (by fun_prop) ?_
    intro t ht
    have h0 := zero_mem_Icc_of_mem_cube ht
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith [h0.1, h0.2]
  have h2 := two_mul_integral_eq_of_swap σ hI
    (g := fun t => 2 * c * selbergIntegrand (n + 1) a 1 c t) (by
      filter_upwards [ae_ne_coord (Fin.succ_ne_zero j).symm] with t hne _
      simp only [hsw0, hsw1, selbergIntegrand_comp_perm]
      have hd : (t 0 : ℂ) - t j.succ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
      have hd' : (t j.succ : ℂ) - t 0 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne.symm)
      field_simp
      ring)
  rw [integral_const_mul] at h2
  unfold selbergInt
  linear_combination h2 / 2

/-- **The recursion in the dimension**: `(a + n c) S_{n+1}(a, 1, c) = S_n(a, 1 + 2c, c)`. -/
theorem selbergInt_succ_one {n : ℕ} {a c : ℂ} (ha : 0 < a.re) (hc : 1 / 2 ≤ c.re) :
    (a + n * c) * selbergInt (n + 1) a 1 c = selbergInt n a (1 + 2 * c) c := by
  have h1 : (0 : ℝ) < (1 : ℂ).re := by simp
  have hc0 : (0 : ℝ) ≤ c.re := by linarith
  have hK : IntegrableOn (selbergIntegrand n a 1 c) (cube n) := by
    have := integrableOn_mul_selbergIntegrand ha h1 hc0 (n := n) (h := fun _ => (1 : ℂ))
      (M := 1) measurable_const (fun _ _ => by simp)
    simpa using this
  have h := integral_cube_ibp ha (Or.inr rfl) hc hK
  simp only [↓reduceIte] at h
  have hR : ∫ y in cube n, selbergIntegrand n a 1 c y * vprod y c 1 =
      selbergInt n a (1 + 2 * c) c := by
    refine setIntegral_congr_fun (measurableSet_cube n) fun y hy => ?_
    rw [selbergIntegrand_eq, selbergIntegrand_eq, vprod]
    rw [mul_right_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have hyi := hy i (Set.mem_univ _)
    simp only [weight, sub_self, Complex.cpow_zero, mul_one, add_sub_cancel_left]
    rw [show |1 - y i| = 1 - y i from abs_of_nonneg (by linarith [hyi.2]), one_sub_ofReal]
  have hL : ∫ t in cube (n + 1), selbergIntegrand n a 1 c (Fin.tail t) *
      ibpD (Fin.tail t) a 0 c (t 0) =
      ∫ t in cube (n + 1), (a * selbergIntegrand (n + 1) a 1 c t +
        ∑ j : Fin n, (t 0 : ℂ) * (2 * c / ((t 0 : ℂ) - t j.succ) *
          selbergIntegrand (n + 1) a 1 c t)) := by
    refine setIntegral_congr_ae (measurableSet_cube _) ?_
    filter_upwards [ae_coord_mem_Ioo] with t ht0 ht
    rw [ibpD_zero_eq _ _ _ (ht0 ht), selbergIntegrand_eq_cons_tail, Finset.mul_sum]
    simp only [Fin.tail]
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      ring
  have hI0 : IntegrableOn (fun t => a * selbergIntegrand (n + 1) a 1 c t) (cube (n + 1)) := by
    have := integrableOn_mul_selbergIntegrand ha h1 hc0 (n := n + 1) (h := fun _ => a)
      (M := ‖a‖) measurable_const (fun _ _ => le_rfl)
    simpa using this
  have hIj : ∀ j : Fin n, IntegrableOn (fun t => (t 0 : ℂ) * (2 * c / ((t 0 : ℂ) - t j.succ) *
      selbergIntegrand (n + 1) a 1 c t)) (cube (n + 1)) := by
    intro j
    refine integrableOn_mul_div_selbergIntegrand ha h1 hc j (M := 1) (by fun_prop) ?_
    intro t ht
    have h0 := zero_mem_Icc_of_mem_cube ht
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith [h0.1, h0.2]
  rw [hL, hR, integral_add hI0 (integrable_finsetSum _ fun j _ => hIj j), integral_const_mul,
    integral_finsetSum _ fun j _ => hIj j] at h
  simp only [scaling_cross ha hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  rw [← h]
  unfold selbergInt
  ring

/-! ### The right-hand side -/

/-- The right-hand side of Selberg's formula. -/
def selbergRHS (n : ℕ) (a b c : ℂ) : ℂ :=
  ∏ j : Fin n,
    Gamma (a + (j : ℕ) * c) * Gamma (b + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) /
      (Gamma (a + b + (n + j - 1 : ℕ) * c) * Gamma (1 + c))

/-- The right-hand side of Selberg's formula as a product over `Finset.range n`. -/
theorem selbergRHS_eq_range (n : ℕ) (a b c : ℂ) : selbergRHS n a b c =
    ∏ j ∈ Finset.range n, Gamma (a + j * c) * Gamma (b + j * c) * Gamma (1 + (j + 1) * c) /
      (Gamma (a + b + (n + j - 1 : ℕ) * c) * Gamma (1 + c)) :=
  Fin.prod_univ_eq_prod_range (fun j : ℕ => Gamma (a + j * c) * Gamma (b + j * c) *
    Gamma (1 + (j + 1) * c) / (Gamma (a + b + (n + j - 1 : ℕ) * c) * Gamma (1 + c))) n

/-- The right-hand side of Selberg's formula is symmetric in `a` and `b`. -/
theorem selbergRHS_comm (n : ℕ) (a b c : ℂ) : selbergRHS n a b c = selbergRHS n b a c := by
  unfold selbergRHS
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [add_comm a b]
  ring

/-- If `Re a > 0`, `Re c ≥ 0` and `x ≥ 0`, then `Re (a + x c) > 0`. -/
theorem re_add_nat_mul_pos {a c : ℂ} (ha : 0 < a.re) (hc : 0 ≤ c.re) (x : ℝ) (hx : 0 ≤ x) :
    0 < (a + x * c).re := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  nlinarith

/-- The `a`-shift of the right-hand side. -/
theorem selbergRHS_add_one {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 ≤ c.re) :
    selbergRHS N (a + 1) b c =
      (∏ j ∈ Finset.range N, aomotoFactor N a b c j) * selbergRHS N a b c := by
  rw [selbergRHS_eq_range, selbergRHS_eq_range]
  have hab : 0 < (a + b).re := by simp; linarith
  -- each factor
  have hfac : ∀ j ∈ Finset.range N,
      Gamma (a + 1 + j * c) * Gamma (b + j * c) * Gamma (1 + (j + 1) * c) /
          (Gamma (a + 1 + b + (N + j - 1 : ℕ) * c) * Gamma (1 + c)) =
        (a + j * c) / (a + b + (N + j - 1 : ℕ) * c) *
          (Gamma (a + j * c) * Gamma (b + j * c) * Gamma (1 + (j + 1) * c) /
            (Gamma (a + b + (N + j - 1 : ℕ) * c) * Gamma (1 + c))) := by
    intro j _
    have h1 : 0 < (a + (j : ℂ) * c).re := by
      have := re_add_nat_mul_pos ha hc j (Nat.cast_nonneg j); simpa using this
    have h2 : 0 < (a + b + ((N + j - 1 : ℕ) : ℂ) * c).re := by
      have := re_add_nat_mul_pos hab hc (N + j - 1 : ℕ) (Nat.cast_nonneg _); simpa using this
    have hc1 : 0 < (1 + c).re := by simp; linarith
    rw [show a + 1 + (j : ℂ) * c = (a + j * c) + 1 by ring,
      show a + 1 + b + ((N + j - 1 : ℕ) : ℂ) * c = (a + b + (N + j - 1 : ℕ) * c) + 1 by ring,
      Complex.Gamma_add_one _ (fun h => by simp [h] at h1),
      Complex.Gamma_add_one _ (fun h => by simp [h] at h2)]
    have g1 := Complex.Gamma_ne_zero_of_re_pos h1
    have g2 := Complex.Gamma_ne_zero_of_re_pos h2
    have g3 := Complex.Gamma_ne_zero_of_re_pos hc1
    have n2 : a + b + ((N + j - 1 : ℕ) : ℂ) * c ≠ 0 := fun h => by simp [h] at h2
    field_simp
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_range_reflect (fun j : ℕ => (a + (j : ℂ) * c) /
    (a + b + ((N + j - 1 : ℕ) : ℂ) * c)) N]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  unfold aomotoFactor
  rw [show N + (N - 1 - j) - 1 = 2 * N - 2 - j by omega]

/-- The dimension recursion of the right-hand side. -/
theorem selbergRHS_succ_one {n : ℕ} {a c : ℂ} (ha : 0 < a.re) (hc : 0 ≤ c.re) :
    (a + n * c) * selbergRHS (n + 1) a 1 c = selbergRHS n a (1 + 2 * c) c := by
  rw [selbergRHS_eq_range, selbergRHS_eq_range]
  set u : ℕ → ℂ := fun j => Gamma (a + j * c) with hu
  set v : ℕ → ℂ := fun j => Gamma (1 + j * c) with hv
  set w : ℕ → ℂ := fun j => Gamma (a + 1 + j * c) with hw
  set G := Gamma (1 + c) with hG
  have hL : ∀ j ∈ Finset.range (n + 1),
      Gamma (a + j * c) * Gamma (1 + j * c) * Gamma (1 + (j + 1) * c) /
        (Gamma (a + 1 + ((n + 1 + j - 1 : ℕ) : ℂ) * c) * Gamma (1 + c)) =
      u j * v j * v (j + 1) / (w (n + j) * G) := by
    intro j _
    simp only [hu, hv, hw, hG]
    rw [show n + 1 + j - 1 = n + j by omega]
    push_cast; ring_nf
  have hR : ∀ j ∈ Finset.range n,
      Gamma (a + j * c) * Gamma (1 + 2 * c + j * c) * Gamma (1 + (j + 1) * c) /
        (Gamma (a + (1 + 2 * c) + ((n + j - 1 : ℕ) : ℂ) * c) * Gamma (1 + c)) =
      u j * v (j + 2) * v (j + 1) / (w (n + j + 1) * G) := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [hu, hv, hw, hG]
    rw [Nat.cast_sub (by omega)]
    push_cast; ring_nf
  rw [Finset.prod_congr rfl hL, Finset.prod_congr rfl hR]
  simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range]
  rw [Finset.prod_range_succ u, Finset.prod_range_succ' v, Finset.prod_range_succ
    (fun j => v (j + 1)), Finset.prod_range_succ' (fun j => w (n + j))]
  have hT : (∏ j ∈ Finset.range n, v (j + 2)) * G =
      (∏ j ∈ Finset.range n, v (j + 1)) * v (n + 1) := by
    have h := Finset.prod_range_succ' (fun j => v (j + 1)) n
    rw [Finset.prod_range_succ] at h
    simp only [hv, hG] at h ⊢
    rw [show (((0 : ℕ) + 1 : ℕ) : ℂ) = 1 by simp, one_mul] at h
    rw [h]
  have hv0 : v 0 = 1 := by simp [hv]
  have hc1 : 0 < (1 + c).re := by simp; linarith
  have hGne : G ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hc1
  have hwne : ∀ k : ℕ, w k ≠ 0 := fun k => Complex.Gamma_ne_zero_of_re_pos (by
    have := re_add_nat_mul_pos (a := a + 1) (by simp; linarith) hc k (Nat.cast_nonneg k)
    simpa using this)
  have hW : (∏ j ∈ Finset.range n, w (n + (j + 1))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hwne _
  have hun : (a + n * c) * u n = w n := by
    simp only [hu, hw]
    have h1 : 0 < (a + (n : ℂ) * c).re := by
      have := re_add_nat_mul_pos ha hc n (Nat.cast_nonneg n); simpa using this
    rw [show a + 1 + (n : ℂ) * c = (a + n * c) + 1 by ring,
      Complex.Gamma_add_one _ (fun h => by simp [h] at h1)]
  have hwn : w (n + 0) = w n := by simp
  rw [hwn, hv0]
  simp only [show ∀ j : ℕ, n + j + 1 = n + (j + 1) from fun j => by omega]
  rw [← hun]
  have hT' : ∏ j ∈ Finset.range n, v (j + 2) =
      (∏ j ∈ Finset.range n, v (j + 1)) * v (n + 1) / G := by
    rw [eq_div_iff hGne, hT]
  rw [hT']
  have hun0 : u n ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    have := re_add_nat_mul_pos ha hc n (Nat.cast_nonneg n); simpa using this)
  have han : a + n * c ≠ 0 := fun h => by
    have := re_add_nat_mul_pos ha hc n (Nat.cast_nonneg n); simp [h] at this
  field_simp
  ring

/-! ### Holomorphy in the parameters -/

/-- Almost every point of the cube has all coordinates in `(0,1)`. -/
theorem ae_cube_coords_Ioo (N : ℕ) :
    ∀ᵐ t : Fin N → ℝ, t ∈ cube N → ∀ i, t i ∈ Ioo (0 : ℝ) 1 := by
  have h0 : ∀ᵐ t : Fin N → ℝ, ∀ i, t i ≠ 0 := ae_all_iff.2 fun i => ae_coord_ne i 0
  have h1 : ∀ᵐ t : Fin N → ℝ, ∀ i, t i ≠ 1 := ae_all_iff.2 fun i => ae_coord_ne i 1
  filter_upwards [h0, h1] with t ht0 ht1 ht i
  have := ht i (Set.mem_univ _)
  exact ⟨lt_of_le_of_ne this.1 (Ne.symm (ht0 i)), lt_of_le_of_ne this.2 (ht1 i)⟩

/-- On `(0,1)`, `‖x^{a-1}(1-x)^{b-1}‖` decreases as `Re a` increases. -/
theorem norm_weight_le_of_re_le {a a' b : ℂ} (h : a'.re ≤ a.re) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : ‖weight a b x‖ ≤ ‖weight a' b x‖ := by
  unfold weight
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1,
    Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.le ?_
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- On `(0,1)` and for `Re a ≥ 1`, `‖weight a b x‖ ≤ ‖weight 1 b x‖`. -/
theorem norm_weight_le_one_left {a b : ℂ} (h : 1 ≤ a.re) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖weight a b x‖ ≤ ‖weight 1 b x‖ := by
  exact norm_weight_le_of_re_le (a := a) (a' := 1) (b := b) (by rw [Complex.one_re]; exact h) hx

/-- For `x > 0`, `a ↦ x^{a-1}` is complex differentiable. -/
theorem differentiableAt_ofReal_cpow_sub_one {x : ℝ} (hx : 0 < x) (a : ℂ) :
    DifferentiableAt ℂ (fun a : ℂ => (x : ℂ) ^ (a - 1)) a :=
  ((differentiableAt_id.sub_const 1).const_cpow (Or.inl (by exact_mod_cast hx.ne')))

/-- The Selberg integral is holomorphic in `a` on the right half-plane. -/
theorem differentiableOn_selbergInt_a (N : ℕ) {b c : ℂ} (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    DifferentiableOn ℂ (fun a => selbergInt N a b c) {a | 0 < a.re} := by
  unfold selbergInt
  refine DLMF.Gamma.vb_differentiableOn_integral (isOpen_lt continuous_const Complex.continuous_re)
    (fun a _ => (measurable_selbergIntegrand N a b c).aestronglyMeasurable) ?_ ?_
  · filter_upwards [ae_restrict_mem (measurableSet_cube N),
      (ae_restrict_iff' (measurableSet_cube N)).2 (ae_cube_coords_Ioo N)] with t ht ht'
    intro a _
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold selbergIntegrand
    refine DifferentiableAt.mul (DifferentiableAt.fun_finsetProd fun i _ => ?_)
      (differentiableAt_const _)
    exact (differentiableAt_ofReal_cpow_sub_one (ht' i).1 a).mul (differentiableAt_const _)
  · intro a₀ ha₀
    refine ⟨a₀.re / 2, by simp at ha₀; positivity, fun z hz => ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      have := Complex.abs_re_le_norm (z - a₀)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      simp at ha₀
      have h2 : |(z - a₀).re| ≤ a₀.re / 2 := this.trans hz
      rw [Complex.sub_re, abs_le] at h2
      linarith
    refine ⟨fun t => ‖∏ i, weight ((a₀.re / 2 : ℝ) : ℂ) b (t i)‖, ?_, ?_⟩
    · exact (integrableOn_prod_cube (n := N) (integrableOn_weight (by simp at ha₀ ⊢; positivity)
        hb)).norm
    · filter_upwards [ae_restrict_mem (measurableSet_cube N),
        (ae_restrict_iff' (measurableSet_cube N)).2 (ae_cube_coords_Ioo N)] with t ht ht' z hz
      refine (norm_selbergIntegrand_le hc ht).trans ?_
      rw [norm_prod, norm_prod]
      refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
      refine norm_weight_le_of_re_le ?_ (ht' i)
      have := Complex.abs_re_le_norm (z - a₀)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h2 : |(z - a₀).re| ≤ a₀.re / 2 := this.trans hz
      rw [Complex.sub_re, abs_le] at h2
      simp only [Complex.ofReal_re]
      linarith

/-! ### Carlson's theorem in `a` -/

/-- If `Re a > 0` and `Re c ≥ 0`, then `Re (a + k c) > 0` for every natural `k`. -/
theorem re_pos_add_nat_mul {a c : ℂ} (ha : 0 < a.re) (hc : 0 ≤ c.re) (k : ℕ) :
    0 < (a + (k : ℂ) * c).re := by
  have := re_add_nat_mul_pos ha hc k (Nat.cast_nonneg k); simpa using this

/-- The right-hand side of Selberg's formula is nonzero for `Re a, Re b > 0`, `Re c ≥ 0`. -/
theorem selbergRHS_ne_zero {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    selbergRHS N a b c ≠ 0 := by
  have hab : 0 < (a + b).re := by simp; linarith
  have hc1 : 0 < (1 : ℂ).re := by simp
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  refine div_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) (mul_ne_zero ?_ ?_)
  · exact Complex.Gamma_ne_zero_of_re_pos (re_pos_add_nat_mul ha hc j)
  · exact Complex.Gamma_ne_zero_of_re_pos (re_pos_add_nat_mul hb hc j)
  · have := re_pos_add_nat_mul hc1 hc (j + 1)
    exact Complex.Gamma_ne_zero_of_re_pos (by simpa using this)
  · exact Complex.Gamma_ne_zero_of_re_pos (re_pos_add_nat_mul hab hc _)
  · exact Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)

/-- The factors in Aomoto's formula are nonzero for `Re a, Re b > 0`, `Re c ≥ 0`. -/
theorem aomotoFactor_ne_zero {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 ≤ c.re)
    (j : ℕ) : aomotoFactor N a b c j ≠ 0 := by
  have hab : 0 < (a + b).re := by simp; linarith
  unfold aomotoFactor
  refine div_ne_zero (fun h => ?_) (fun h => ?_)
  · have := re_pos_add_nat_mul ha hc (N - 1 - j); rw [h] at this; simp at this
  · have := re_pos_add_nat_mul hab hc (2 * N - 2 - j); rw [h] at this; simp at this

/-- The right-hand side of Selberg's formula is holomorphic in `a` on `Re a > 0`. -/
theorem differentiableOn_selbergRHS_a (N : ℕ) {b c : ℂ} (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    DifferentiableOn ℂ (fun a => selbergRHS N a b c) {a | 0 < a.re} := by
  intro a ha
  have ha' : 0 < a.re := ha
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold selbergRHS
  refine DifferentiableAt.fun_finsetProd fun j _ => ?_
  have hab : 0 < (a + b).re := by simp; linarith
  refine DifferentiableAt.div (DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_) ?_ ?_
  · exact (Complex.differentiableAt_Gamma _
      (DLMF.Hypergeometric.not_neg_nat_of_re_pos (re_pos_add_nat_mul ha' hc j))).comp a
      (by fun_prop : DifferentiableAt ℂ (fun x : ℂ => x + ((j : ℕ) : ℂ) * c) a)
  · exact differentiableAt_const _
  · exact differentiableAt_const _
  · refine DifferentiableAt.mul ?_ (differentiableAt_const _)
    exact (Complex.differentiableAt_Gamma _
      (DLMF.Hypergeometric.not_neg_nat_of_re_pos (re_pos_add_nat_mul hab hc (N + j - 1)))).comp a
      (by fun_prop : DifferentiableAt ℂ
        (fun x : ℂ => x + b + ((N + (j : ℕ) - 1 : ℕ) : ℂ) * c) a)
  · refine mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (re_pos_add_nat_mul hab hc _))
      (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))

/-- Polynomial growth of `1/R` on the strip `1 ≤ Re a ≤ 2`. -/
theorem exists_norm_recip_selbergRHS_le (N : ℕ) {b c : ℂ} (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ a : ℂ, 1 ≤ a.re → a.re ≤ 2 →
      ‖(selbergRHS N a b c)⁻¹‖ ≤ C * (1 + |a.im|) ^ K := by
  have hp : ∀ j : Fin N, 0 < (b + ((N + j - 1 : ℕ) : ℂ) * c).re :=
    fun j => re_pos_add_nat_mul hb hc _
  have h1 : ∀ j : Fin N, ∃ C : ℝ, ∃ K : ℕ, 0 ≤ C ∧ ∀ d : ℂ,
      1 + (b + ((N + j - 1 : ℕ) : ℂ) * c).re ≤ (d + (b + ((N + j - 1 : ℕ) : ℂ) * c)).re →
      (d + (b + ((N + j - 1 : ℕ) : ℂ) * c)).re ≤ 2 + (b + ((N + j - 1 : ℕ) : ℂ) * c).re →
      ‖Gamma (d + (b + ((N + j - 1 : ℕ) : ℂ) * c))‖ ≤
        C * (1 + |d.im|) ^ K * Real.exp (-(π * |d.im|) / 2) :=
    fun j => DLMF.Hypergeometric.CarlsonAux.exists_norm_Gamma_add_le_strip _ (by linarith [hp j])
  have h2 : ∀ j : Fin N, ∃ C : ℝ, ∃ K : ℕ, 0 ≤ C ∧ ∀ d : ℂ,
      |(d + ((j : ℕ) : ℂ) * c).re| ≤ 2 + |(((j : ℕ) : ℂ) * c).re| →
      ‖(Gamma (d + ((j : ℕ) : ℂ) * c))⁻¹‖ ≤ C * (1 + |d.im|) ^ K * Real.exp (π * |d.im| / 2) :=
    fun j => DLMF.Hypergeometric.CarlsonAux.exists_norm_recip_Gamma_add_le_strip _ _
  choose C1 K1 hC1 hb1 using h1
  choose C2 K2 hC2 hb2 using h2
  set D : Fin N → ℝ := fun j => C1 j * C2 j * ‖Gamma (1 + c)‖ * ‖(Gamma (b + (j : ℕ) * c))⁻¹‖ *
    ‖(Gamma (1 + ((j : ℕ) + 1) * c))⁻¹‖ with hD
  refine ⟨∏ j, D j, ∑ j, (K1 j + K2 j), fun a ha1 ha2 => ?_⟩
  unfold selbergRHS
  rw [← Finset.prod_inv_distrib, norm_prod, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
  have hX : 1 ≤ 1 + |a.im| := by linarith [abs_nonneg a.im]
  have e1 := hb1 j a (by simp only [Complex.add_re]; linarith)
    (by simp only [Complex.add_re]; linarith)
  have e2 := hb2 j a (by
    rw [Complex.add_re]
    have := abs_add_le a.re ((((j : ℕ) : ℂ) * c).re)
    rw [abs_of_pos (by linarith : (0 : ℝ) < a.re)] at this
    linarith)
  have hab : a + b + ((N + j - 1 : ℕ) : ℂ) * c = a + (b + ((N + j - 1 : ℕ) : ℂ) * c) := by ring
  rw [inv_div, hab, norm_div, norm_mul, norm_mul, norm_mul, div_eq_mul_inv, mul_inv, mul_inv,
    ← norm_inv, ← norm_inv, ← norm_inv]
  have hexp : Real.exp (-(π * |a.im|) / 2) * Real.exp (π * |a.im| / 2) = 1 := by
    rw [← Real.exp_add, show -(π * |a.im|) / 2 + π * |a.im| / 2 = 0 by ring, Real.exp_zero]
  calc ‖Gamma (a + (b + ((N + j - 1 : ℕ) : ℂ) * c))‖ * ‖Gamma (1 + c)‖ *
        (‖(Gamma (a + (j : ℕ) * c))⁻¹‖ * ‖(Gamma (b + (j : ℕ) * c))⁻¹‖ *
          ‖(Gamma (1 + ((j : ℕ) + 1) * c))⁻¹‖)
      ≤ (C1 j * (1 + |a.im|) ^ K1 j * Real.exp (-(π * |a.im|) / 2)) * ‖Gamma (1 + c)‖ *
        ((C2 j * (1 + |a.im|) ^ K2 j * Real.exp (π * |a.im| / 2)) *
          ‖(Gamma (b + (j : ℕ) * c))⁻¹‖ * ‖(Gamma (1 + ((j : ℕ) + 1) * c))⁻¹‖) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right e1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e2 (norm_nonneg _))
            (norm_nonneg _)) (by positivity) ?_
        exact mul_nonneg (mul_nonneg (mul_nonneg (hC1 j) (by positivity)) (by positivity))
          (norm_nonneg _)
    _ = D j * (1 + |a.im|) ^ (K1 j + K2 j) *
          (Real.exp (-(π * |a.im|) / 2) * Real.exp (π * |a.im| / 2)) := by
        simp only [hD]; ring
    _ = D j * (1 + |a.im|) ^ (K1 j + K2 j) := by rw [hexp, mul_one]

/-- The Selberg integral is bounded on `Re a ≥ 1`. -/
theorem norm_selbergInt_le {N : ℕ} {a b c : ℂ} (ha : 1 ≤ a.re) (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    ‖selbergInt N a b c‖ ≤ ∫ t in cube N, ‖∏ i, weight 1 b (t i)‖ := by
  unfold selbergInt
  refine norm_integral_le_of_norm_le
    (integrableOn_prod_cube (integrableOn_weight (by simp) hb)).norm ?_
  filter_upwards [ae_restrict_mem (measurableSet_cube N),
    (ae_restrict_iff' (measurableSet_cube N)).2 (ae_cube_coords_Ioo N)] with t ht ht'
  refine (norm_selbergIntegrand_le hc ht).trans ?_
  rw [norm_prod, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ =>
    norm_weight_le_one_left ha (ht' i)

/-- `S/R` is `1`-periodic in `a`. -/
theorem selbergRatio_add_one {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 1 / 2 ≤ c.re) :
    selbergInt N (a + 1) b c / selbergRHS N (a + 1) b c =
      selbergInt N a b c / selbergRHS N a b c := by
  have hc0 : (0 : ℝ) ≤ c.re := by linarith
  rw [selbergInt_add_one ha hb hc, selbergRHS_add_one ha hb hc0]
  have hP : ∏ j ∈ Finset.range N, aomotoFactor N a b c j ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => aomotoFactor_ne_zero ha hb hc0 j
  rw [mul_div_mul_left _ _ hP]

/-- **Carlson's theorem in `a`**: `S/R` does not depend on `a`. -/
theorem selbergRatio_eq_one_left {N : ℕ} {b c : ℂ} (hb : 0 < b.re) (hc : 1 / 2 ≤ c.re)
    {a : ℂ} (ha : 0 < a.re) :
    selbergInt N a b c / selbergRHS N a b c = selbergInt N 1 b c / selbergRHS N 1 b c := by
  have hc0 : (0 : ℝ) ≤ c.re := by linarith
  set F : ℂ → ℂ := fun a => selbergInt N a b c / selbergRHS N a b c with hF
  have hFd : DifferentiableOn ℂ F {a | 0 < a.re} :=
    (differentiableOn_selbergInt_a N hb hc0).div (differentiableOn_selbergRHS_a N hb hc0)
      fun a ha => selbergRHS_ne_zero ha hb hc0
  set f : ℂ → ℂ := fun w => F (w + 1) - F 1 with hf
  obtain ⟨C, K, hC⟩ := exists_norm_recip_selbergRHS_le N hb hc0
  set B := ∫ t in cube N, ‖∏ i, weight 1 b (t i)‖ with hB
  have hB0 : 0 ≤ B := setIntegral_nonneg (measurableSet_cube N) fun _ _ => norm_nonneg _
  have hfz : ∀ w : ℂ, 0 ≤ w.re → f w = 0 := by
    refine DLMF.Hypergeometric.CarlsonAux.eq_zero_of_periodic_of_bound (δ := 1 / 2)
      (by norm_num) ?_ ?_ (C := B * max C 0 + ‖F 1‖) (σ := 0) (K := K) Real.pi_pos ?_ ?_
    · intro w hw
      refine DifferentiableWithinAt.sub ?_ (differentiableWithinAt_const _)
      have hw' : 0 < (w + 1).re := by simp at hw ⊢; linarith
      exact ((hFd (w + 1) hw').differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw')).comp w
        (differentiableAt_id.add_const 1) |>.differentiableWithinAt
    · intro w hw
      simp only [hf, hF]
      have hw' : 0 < (w + 1).re := by simp; linarith
      rw [selbergRatio_add_one hw' hb hc]
    · intro w hw0 hw1
      have h1 : 1 ≤ (w + 1).re := by simp; linarith
      have h2 : (w + 1).re ≤ 2 := by simp; linarith
      have hS := norm_selbergInt_le (N := N) (c := c) h1 hb hc0
      have hR := hC (w + 1) h1 h2
      have hR' : ‖(selbergRHS N (w + 1) b c)⁻¹‖ ≤ max C 0 * (1 + |w.im|) ^ K := by
        refine hR.trans ?_
        simp only [Complex.add_im, Complex.one_im, add_zero]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have hX : 1 ≤ (1 + |w.im|) ^ K := one_le_pow₀ (by linarith [abs_nonneg w.im])
      simp only [hf, hF, zero_mul, Real.exp_zero, mul_one]
      calc ‖selbergInt N (w + 1) b c / selbergRHS N (w + 1) b c -
            selbergInt N 1 b c / selbergRHS N 1 b c‖
          ≤ ‖selbergInt N (w + 1) b c‖ * ‖(selbergRHS N (w + 1) b c)⁻¹‖ +
              ‖selbergInt N 1 b c / selbergRHS N 1 b c‖ := by
            rw [div_eq_mul_inv, ← norm_mul]; exact norm_sub_le _ _
        _ ≤ B * (max C 0 * (1 + |w.im|) ^ K) +
              ‖selbergInt N 1 b c / selbergRHS N 1 b c‖ * (1 + |w.im|) ^ K := by
            gcongr
            · exact le_mul_of_one_le_right (norm_nonneg _) hX
        _ = (B * max C 0 + ‖selbergInt N 1 b c / selbergRHS N 1 b c‖) * (1 + |w.im|) ^ K := by
            ring
    · simp [hf]
  by_cases h1 : 1 ≤ a.re
  · have := hfz (a - 1) (by simp; linarith)
    simp only [hf, sub_add_cancel, sub_eq_zero] at this
    exact this
  · have := hfz a ha.le
    simp only [hf, hF, sub_eq_zero] at this
    rw [← this]
    exact (selbergRatio_add_one ha hb hc).symm

/-- For `Re c ≥ 1/2`, the ratio `S/R` of the Selberg integral to the right-hand side
does not depend on `a` and `b`. -/
theorem selbergRatio_eq_one_one {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 1 / 2 ≤ c.re) :
    selbergInt N a b c / selbergRHS N a b c = selbergInt N 1 1 c / selbergRHS N 1 1 c := by
  have h1 : (0 : ℝ) < (1 : ℂ).re := by simp
  rw [selbergRatio_eq_one_left hb hc ha, selbergInt_comm, selbergRHS_comm,
    selbergRatio_eq_one_left h1 hc hb]

/-- The zero-dimensional Selberg integral is `1`. -/
theorem selbergInt_zero (a b c : ℂ) : selbergInt 0 a b c = 1 := by
  have hcube : cube 0 = Set.univ := Set.eq_univ_of_forall fun t => fun i => i.elim0
  rw [selbergInt, hcube, Measure.restrict_univ]
  simp only [selbergIntegrand, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
    integral_const]
  rw [Measure.real, volume_pi, Measure.pi_univ]
  simp

/-- The zero-dimensional right-hand side of Selberg's formula is `1`. -/
theorem selbergRHS_zero (a b c : ℂ) : selbergRHS 0 a b c = 1 := by
  simp [selbergRHS]

/-- For `Re c ≥ 1/2` and every `N`, `S_N(1, 1, c) = R_N(1, 1, c)`. -/
theorem selbergRatio_one_one_eq_one {c : ℂ} (hc : 1 / 2 ≤ c.re) :
    ∀ N : ℕ, selbergInt N 1 1 c / selbergRHS N 1 1 c = 1 := by
  have h1 : (0 : ℝ) < (1 : ℂ).re := by simp
  have hc0 : (0 : ℝ) ≤ c.re := by linarith
  intro N
  induction N with
  | zero => simp [selbergInt_zero, selbergRHS_zero]
  | succ n ih =>
    have hb2 : 0 < (1 + 2 * c).re := by simp; linarith
    have hS := selbergInt_succ_one (n := n) h1 hc
    have hR := selbergRHS_succ_one (n := n) h1 hc0
    have hK := selbergRatio_eq_one_one (N := n) h1 hb2 hc
    rw [ih] at hK
    have hRn : selbergRHS n 1 (1 + 2 * c) c ≠ 0 := selbergRHS_ne_zero h1 hb2 hc0
    rw [div_eq_one_iff_eq hRn] at hK
    have hR1 : selbergRHS (n + 1) 1 1 c ≠ 0 := selbergRHS_ne_zero h1 h1 hc0
    have hnc : (1 : ℂ) + n * c ≠ 0 := fun h => by
      have := re_pos_add_nat_mul h1 hc0 n; rw [h] at this; simp at this
    rw [div_eq_one_iff_eq hR1]
    apply mul_left_cancel₀ hnc
    rw [hS, hR, hK]

/-- **Selberg's integral** for `Re a, Re b > 0` and `Re c ≥ 1/2`. -/
theorem selbergInt_eq_of_half_le {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 1 / 2 ≤ c.re) : selbergInt N a b c = selbergRHS N a b c := by
  have h := selbergRatio_eq_one_one (N := N) ha hb hc
  rw [selbergRatio_one_one_eq_one hc N,
    div_eq_one_iff_eq (selbergRHS_ne_zero ha hb (by linarith))] at h
  exact h

/-! ### Extension to `Re c > 0` -/

/-- Almost every point of `ℝᴺ` has pairwise distinct coordinates. -/
theorem ae_coords_ne (N : ℕ) : ∀ᵐ t : Fin N → ℝ, ∀ i j, i ≠ j → t i ≠ t j := by
  refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
  by_cases hij : i = j
  · exact Eventually.of_forall fun _ h => absurd hij h
  · filter_upwards [ae_ne_coord hij] with t ht _ using ht

/-- At a point with distinct coordinates, the Selberg integrand is holomorphic in `c`. -/
theorem differentiableAt_selbergIntegrand_c {N : ℕ} (a b : ℂ) {t : Fin N → ℝ}
    (ht : ∀ i j, i ≠ j → t i ≠ t j) (c : ℂ) :
    DifferentiableAt ℂ (fun c => selbergIntegrand N a b c t) c := by
  unfold selbergIntegrand
  refine (differentiableAt_const _).mul (DifferentiableAt.fun_finsetProd fun i _ =>
    DifferentiableAt.fun_finsetProd fun j _ => ?_)
  split_ifs with hij
  · have hne : ((|t i - t j| : ℝ) : ℂ) ≠ 0 := by
      have : t i - t j ≠ 0 := sub_ne_zero.mpr (ht i j (Fin.ne_of_lt hij))
      exact_mod_cast abs_ne_zero.mpr this
    exact (differentiableAt_id.const_mul 2).const_cpow (Or.inl hne)
  · exact differentiableAt_const _

/-- For `Re a, Re b > 0`, the Selberg integral is holomorphic in `c` on `Re c > 0`. -/
theorem differentiableOn_selbergInt_c (N : ℕ) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    DifferentiableOn ℂ (fun c => selbergInt N a b c) {c | 0 < c.re} := by
  unfold selbergInt
  refine DLMF.Gamma.vb_differentiableOn_integral (isOpen_lt continuous_const Complex.continuous_re)
    (fun c _ => (measurable_selbergIntegrand N a b c).aestronglyMeasurable) ?_ ?_
  · filter_upwards [ae_restrict_of_ae (ae_coords_ne N)] with t ht
    exact fun c _ => (differentiableAt_selbergIntegrand_c a b ht c).differentiableWithinAt
  · intro c₀ hc₀
    have hc₀' : 0 < c₀.re := hc₀
    refine ⟨c₀.re / 2, by positivity, fun z hz => ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      have := Complex.abs_re_le_norm (z - c₀)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h2 : |(z - c₀).re| ≤ c₀.re / 2 := this.trans hz
      rw [Complex.sub_re, abs_le] at h2
      linarith
    refine ⟨fun t => ‖∏ i, weight a b (t i)‖,
      (integrableOn_prod_cube (n := N) (integrableOn_weight ha hb)).norm, ?_⟩
    filter_upwards [ae_restrict_mem (measurableSet_cube N)] with t ht z hz
    refine norm_selbergIntegrand_le ?_ ht
    have := Complex.abs_re_le_norm (z - c₀)
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h2 : |(z - c₀).re| ≤ c₀.re / 2 := this.trans hz
    rw [Complex.sub_re, abs_le] at h2
    linarith

/-- The domain of convergence in `c` for fixed `a`, `b`. -/
def cDomain (N : ℕ) (a b : ℂ) : Set ℂ :=
  {c | 0 < 1 + N * c.re ∧ 0 < a.re + ((N - 1 : ℕ) : ℝ) * c.re ∧
    0 < b.re + ((N - 1 : ℕ) : ℝ) * c.re}

/-- The domain of convergence in `c` is open. -/
theorem isOpen_cDomain (N : ℕ) (a b : ℂ) : IsOpen (cDomain N a b) := by
  have h1 : Continuous fun c : ℂ => 1 + (N : ℝ) * c.re := by fun_prop
  have h2 : Continuous fun c : ℂ => a.re + ((N - 1 : ℕ) : ℝ) * c.re := by fun_prop
  have h3 : Continuous fun c : ℂ => b.re + ((N - 1 : ℕ) : ℝ) * c.re := by fun_prop
  have := ((isOpen_lt (continuous_const (y := (0 : ℝ))) h1).inter
    (isOpen_lt (continuous_const (y := (0 : ℝ))) h2)).inter
    (isOpen_lt (continuous_const (y := (0 : ℝ))) h3)
  convert this using 1
  ext c
  simp [cDomain, and_assoc]

/-- The domain of convergence in `c` is convex. -/
theorem convex_cDomain (N : ℕ) (a b : ℂ) : Convex ℝ (cDomain N a b) := by
  unfold cDomain
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.smul_re, smul_eq_mul] at hx hy ⊢
  have key : ∀ {u v : ℝ}, 0 < u → 0 < v → 0 < s * u + t * v := fun hu hv => by
    rcases eq_or_lt_of_le hs with rfl | hs'
    · have : t = 1 := by linarith
      subst this; simpa using hv
    · exact add_pos_of_pos_of_nonneg (mul_pos hs' hu) (mul_nonneg ht hv.le)
  refine ⟨?_, ?_, ?_⟩
  · have e : 1 + N * (s * x.re + t * y.re) = s * (1 + N * x.re) + t * (1 + N * y.re) := by
      linear_combination (-1 : ℝ) * hst
    rw [e]; exact key hx.1 hy.1
  · have e : a.re + ((N - 1 : ℕ) : ℝ) * (s * x.re + t * y.re) =
        s * (a.re + ((N - 1 : ℕ) : ℝ) * x.re) + t * (a.re + ((N - 1 : ℕ) : ℝ) * y.re) := by
      linear_combination (-a.re) * hst
    rw [e]; exact key hx.2.1 hy.2.1
  · have e : b.re + ((N - 1 : ℕ) : ℝ) * (s * x.re + t * y.re) =
        s * (b.re + ((N - 1 : ℕ) : ℝ) * x.re) + t * (b.re + ((N - 1 : ℕ) : ℝ) * y.re) := by
      linear_combination (-b.re) * hst
    rw [e]; exact key hx.2.2 hy.2.2

/-- On the domain of convergence, `Re (a + j c) > 0` for `j ≤ N - 1`. -/
theorem re_pos_of_mem_cDomain {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hc : c ∈ cDomain N a b)
    {j : ℕ} (hj : j ≤ N - 1) : 0 < (a + (j : ℂ) * c).re := by
  obtain ⟨_, h2, _⟩ := hc
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
    sub_zero]
  have hj' : (j : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hj
  rcases le_or_gt 0 c.re with h | h
  · nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  · nlinarith

/-- On the domain of convergence, `Re (1 + j c) > 0` for `j ≤ N`. -/
theorem re_one_add_pos_of_mem_cDomain {N : ℕ} {a b c : ℂ} (hc : c ∈ cDomain N a b)
    {j : ℕ} (hj : j ≤ N) : 0 < (1 + (j : ℂ) * c).re := by
  obtain ⟨h1, _, _⟩ := hc
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero]
  have hj' : (j : ℝ) ≤ N := by exact_mod_cast hj
  rcases le_or_gt 0 c.re with h | h
  · nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  · nlinarith

/-- Every `c` with `Re c > 0` lies in the domain of convergence when `Re a, Re b > 0`. -/
theorem pos_mem_cDomain (N : ℕ) {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) :
    c ∈ cDomain N a b := by
  refine ⟨by positivity, by positivity, by positivity⟩

/-- The right-hand side of Selberg's formula is holomorphic in `c` on the domain
of convergence. -/
theorem differentiableOn_selbergRHS_c {N : ℕ} {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hN : 0 < N) : DifferentiableOn ℂ (fun c => selbergRHS N a b c) (cDomain N a b) := by
  intro c hc
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold selbergRHS
  refine DifferentiableAt.fun_finsetProd fun j _ => ?_
  have hj : (j : ℕ) ≤ N - 1 := by omega
  have hc1 : 0 < (1 + c).re := by
    have := re_one_add_pos_of_mem_cDomain hc (j := 1) (by omega); simpa using this
  refine DifferentiableAt.mul ?_ ?_
  · refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_
    · exact (Complex.differentiableAt_Gamma _
        (DLMF.Hypergeometric.not_neg_nat_of_re_pos (re_pos_of_mem_cDomain ha hc hj))).comp c
        (by fun_prop : DifferentiableAt ℂ (fun x : ℂ => a + ((j : ℕ) : ℂ) * x) c)
    · have hc' : c ∈ cDomain N b a := ⟨hc.1, hc.2.2, hc.2.1⟩
      exact (Complex.differentiableAt_Gamma _
        (DLMF.Hypergeometric.not_neg_nat_of_re_pos (re_pos_of_mem_cDomain hb hc' hj))).comp c
        (by fun_prop : DifferentiableAt ℂ (fun x : ℂ => b + ((j : ℕ) : ℂ) * x) c)
    · have := re_one_add_pos_of_mem_cDomain hc (j := (j : ℕ) + 1) (by omega)
      exact (Complex.differentiableAt_Gamma _
        (DLMF.Hypergeometric.not_neg_nat_of_re_pos (by simpa using this))).comp c
        (by fun_prop : DifferentiableAt ℂ (fun x : ℂ => 1 + (((j : ℕ) : ℂ) + 1) * x) c)
  · have hG : Gamma (1 + c) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hc1
    have h1 : DifferentiableAt ℂ (fun x : ℂ => (Gamma (a + b + ((N + j - 1 : ℕ) : ℂ) * x))⁻¹) c :=
      (Complex.differentiable_one_div_Gamma.differentiableAt.comp c
        (by fun_prop : DifferentiableAt ℂ (fun x : ℂ => a + b + ((N + j - 1 : ℕ) : ℂ) * x) c)
        ).congr_of_eventuallyEq (Eventually.of_forall fun x => by simp)
    have h2 : DifferentiableAt ℂ (fun x : ℂ => (Gamma (1 + x))⁻¹) c :=
      (Complex.differentiable_one_div_Gamma.differentiableAt.comp c
        (by fun_prop : DifferentiableAt ℂ (fun x : ℂ => 1 + x) c)
        ).congr_of_eventuallyEq (Eventually.of_forall fun x => by simp)
    have := h1.mul h2
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, mul_inv]

/-- **Selberg's integral** for `Re a, Re b, Re c > 0`. -/
theorem selbergInt_eq_of_re_pos {N : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) : selbergInt N a b c = selbergRHS N a b c := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [selbergInt_zero, selbergRHS_zero]
  have hV : IsOpen {c : ℂ | 0 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf := (differentiableOn_selbergInt_c N ha hb).analyticOnNhd hV
  have hg := ((differentiableOn_selbergRHS_c ha hb hN).mono
    fun c hc => pos_mem_cDomain N ha hb hc).analyticOnNhd hV
  have hconv : Convex ℝ {c : ℂ | 0 < c.re} := convex_halfSpace_re_gt 0
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg hconv.isPreconnected
    (z₀ := 1) (by simp) ?_ hc
  have hW : IsOpen {c : ℂ | 1 / 2 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hW.mem_nhds (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)] with c hc'
  exact selbergInt_eq_of_half_le ha hb (le_of_lt hc')

end DLMF.Selberg
end
end
