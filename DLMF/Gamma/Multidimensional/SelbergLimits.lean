/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Selberg.Basic
public import Dirichlet.Beta.Complex.Integral
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Laguerre and Hermite limits of Selberg integrals

Scaling, domination and limit arguments derive Laguerre-Selberg and Hermite-Mehta integral
formulas.

Source references and common attribution are retained in
`DLMF.Gamma.Multidimensional`.
-/

@[expose] public section

open Complex MeasureTheory

open scoped Real

noncomputable section

namespace DLMF.Gamma

/-- Vandermonde product, DLMF 5.14.3. -/
@[dlmf 5.14.E3]
def vandermonde {n : ℕ} (t : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i.val < j.val then t i - t j else 1

/-- The open simplex `(0, ∞)ⁿ ∩ {∑ tᵢ ≤ 1}` agrees a.e. with the closed solid simplex. -/
theorem openSimplex_ae_eq_mvBetaSimplex (n : ℕ) :
    ((Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ)) ∩ {t : Fin n → ℝ | ∑ i, t i ≤ 1} :
      Set (Fin n → ℝ)) =ᵐ[volume] Complex.mvBetaSimplex n := by
  have hN : ∀ᵐ x : Fin n → ℝ, ∀ i, x i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    refine measure_mono_null (fun x hx => ?_) ((volume_pi (ι := Fin n) (α := fun _ => ℝ)).symm ▸
      Measure.pi_hyperplane (fun _ : Fin n => (volume : Measure ℝ)) i 0)
    simpa using hx
  filter_upwards [hN] with x hx
  simp only [Complex.mvBetaSimplex, eq_iff_iff]
  change x ∈ (Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ)) ∩ {t | ∑ i, t i ≤ 1} ↔
    (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1
  simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, Set.mem_Ioi, true_implies,
    Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨fun i => (h.1 i).le, h.2⟩,
    fun h => ⟨fun i => lt_of_le_of_ne (h.1 i) (hx i).symm, h.2⟩⟩

/-- DLMF 5.14.1, Dirichlet's integral: `∫_{tᵢ>0, ∑tᵢ≤1} ∏ tᵢ^(zᵢ-1) dt = ∏ Γ(zᵢ) / Γ(1 + ∑ zᵢ)` for
`Re zᵢ > 0`. -/
@[dlmf 5.14.E1]
theorem dirichlet_simplex {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, 0 < (z i).re) :
    ∫ t : Fin n → ℝ in
        (Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ)) ∩ {t | ∑ i, t i ≤ 1},
        ∏ i : Fin n, (t i : ℂ) ^ (z i - 1) =
      (∏ i : Fin n, Complex.Gamma (z i)) / Complex.Gamma (1 + ∑ i, z i) := by
  rw [setIntegral_congr_set (openSimplex_ae_eq_mvBetaSimplex n)]
  have h := Complex.mvBetaIntegralOne_eq_mvBeta hz
  rw [Complex.mvBetaIntegralOne, Complex.mvBeta] at h
  rw [h, Fin.prod_univ_succ, Fin.sum_univ_succ]
  simp

/-- DLMF 5.14.2: `∫_{tᵢ>0, ∑tᵢ≤1} (1 - ∑ tᵢ)^(z_{n+1}-1) ∏ tᵢ^(zᵢ-1) dt = ∏_{i≤n+1} Γ(zᵢ) / Γ(∑ zᵢ)`
for `Re zᵢ > 0`. -/
@[dlmf 5.14.E2]
theorem dirichlet_simplex_full {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hz : ∀ i, 0 < (z i).re) :
    ∫ t : Fin n → ℝ in
        (Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ)) ∩ {t | ∑ i, t i ≤ 1},
        (1 - ∑ i, (t i : ℂ)) ^ (z ⟨n, Nat.lt_succ_self n⟩ - 1) *
          ∏ i : Fin n, (t i : ℂ) ^ (z i.castSucc - 1) =
      (∏ i : Fin (n + 1), Complex.Gamma (z i)) / Complex.Gamma (∑ i, z i) := by
  rw [setIntegral_congr_set (openSimplex_ae_eq_mvBetaSimplex n)]
  have h := Complex.mvBetaIntegral_eq_mvBeta (b₀ := z (Fin.last n))
    (b := fun i => z i.castSucc) (hz _) (fun i => hz _)
  rw [Complex.mvBetaIntegral, Complex.mvBeta] at h
  push_cast at h
  rw [show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n from rfl, h,
    Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring_nf

section LaguerreLimit

/-! ### Laguerre–Selberg integral as a limit of Aomoto's integral

With `b = N + 1` and the substitution `t = x/N`, Aomoto's integral becomes an integral of
`(1 - x/N)^N`-weights over `(0, N]ⁿ`; dominated convergence gives the Laguerre integral, and
the Gamma-ratio asymptotics `Γ(N+p)/Γ(N+q) ~ N^{p-q}` give its value. -/

open Set Filter
open scoped Topology

/-! ### Scaling lemmas -/

/-- Scaling `x = L t` on the box `(0, L]ⁿ`: `∫_{(0,L]ⁿ} g = Lⁿ ∫_{(0,1]ⁿ} g(L t) dt`. -/
theorem integral_pi_Ioc_scale {n : ℕ} (g : (Fin n → ℝ) → ℂ) {L : ℝ} (hL : 0 < L) :
    ∫ x in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) L), g x =
      (L : ℂ) ^ n * ∫ t in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1), g (L • t) := by
  have hmem : ∀ t : Fin n → ℝ, L • t ∈ Set.pi Set.univ (fun _ => Ioc (0 : ℝ) L) ↔
      t ∈ Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1) := by
    intro t
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioc, Pi.smul_apply, smul_eq_mul]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 hL.le, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hL h1, by nlinarith⟩
  have h := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure (Fin n → ℝ)))
    ((Set.pi Set.univ (fun _ => Ioc (0 : ℝ) L)).indicator g) L
  rw [Module.finrank_fin_fun] at h
  have hind : (fun t : Fin n → ℝ => (Set.pi Set.univ (fun _ => Ioc (0 : ℝ) L)).indicator g
      (L • t)) = (Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1)).indicator (fun t => g (L • t)) := by
    ext t
    by_cases ht : t ∈ Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1)
    · rw [Set.indicator_of_mem ((hmem t).mpr ht), Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem (fun h => ht ((hmem t).mp h)), Set.indicator_of_notMem ht]
  rw [hind, integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Ioc),
    integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)] at h
  rw [h, abs_of_pos (inv_pos.mpr (pow_pos hL n)), Complex.real_smul]
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n (by exact_mod_cast hL.ne')), one_mul]

/-! ### Power algebra -/

/-- `(∏ fᵢ)^w = ∏ fᵢ^w` for nonnegative real factors. -/
theorem ofReal_prod_cpow {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (w : ℂ) : ((∏ i ∈ s, f i : ℝ) : ℂ) ^ w = ∏ i ∈ s, ((f i : ℝ) : ℂ) ^ w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Complex.ofReal_mul,
      ← ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]
    exact Complex.mul_cpow_ofReal_nonneg (hf j (Finset.mem_insert_self j s))
      (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)) w

/-- `(x^k)^w = x^(k w)` for `x > 0`. -/
theorem ofReal_pow_cpow {x : ℝ} (hx : 0 < x) (k : ℕ) (w : ℂ) :
    ((x ^ k : ℝ) : ℂ) ^ w = (x : ℂ) ^ ((k : ℂ) * w) := by
  rw [Complex.ofReal_pow, ← Complex.cpow_natCast, ← Complex.cpow_mul]
  · rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_im]; linarith [Real.pi_pos]
  · rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_im]; linarith [Real.pi_pos]

/-- `∏_{i<j} x = x^(n(n-1)/2)`. -/
theorem prod_ite_lt_const {n : ℕ} (x : ℝ) :
    ∏ i : Fin n, ∏ j : Fin n, (if i.val < j.val then x else 1) = x ^ (n * (n - 1) / 2) := by
  have hrow : ∀ i : Fin n, ∏ j : Fin n, (if i.val < j.val then x else 1) = x ^ (n - 1 - i.val) := by
    intro i
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    congr 1
    have h1 := Fin.card_filter_val_lt (n := n) (m := i.val + 1)
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun j : Fin n => i.val < j.val)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    have h3 : (Finset.univ.filter fun j : Fin n => ¬ i.val < j.val) =
        Finset.univ.filter fun j : Fin n => j.val < i.val + 1 := by
      ext j; simp
    rw [h3, h1] at h2
    have := i.isLt
    omega
  rw [Finset.prod_congr rfl fun i _ => hrow i, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n, Finset.sum_range_reflect (fun i => i) n,
    Finset.sum_range_id]

/-- `Δ(L t) = L^(n(n-1)/2) Δ(t)`. -/
theorem vandermonde_smul {n : ℕ} (L : ℝ) (t : Fin n → ℝ) :
    vandermonde (L • t) = L ^ (n * (n - 1) / 2) * vandermonde t := by
  unfold vandermonde
  rw [← prod_ite_lt_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp [Pi.smul_apply, smul_eq_mul, mul_sub]

/-- `2 · (n(n-1)/2) = n(n-1)`. -/
theorem two_mul_pairs (n : ℕ) : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
  rw [← Finset.sum_range_id, mul_comm, Finset.sum_range_id_mul_two]

/-! ### The Laguerre integrand and its approximations -/

/-- The integrand of 5.14.5. -/
def lagIntegrand (n m : ℕ) (hm : m ≤ n) (a c : ℂ) (x : Fin n → ℝ) : ℂ :=
  (∏ i : Fin m, (x (Fin.castLE hm i) : ℂ)) *
    (∏ i : Fin n, (x i : ℂ) ^ (a - 1) * Complex.exp (-(x i : ℂ))) *
    ((|vandermonde x| : ℝ) : ℂ) ^ (2 * c)

/-- Its approximation with `(1 - x/N)^N` in place of `e^{-x}`. -/
def lagApprox (n m : ℕ) (hm : m ≤ n) (a c : ℂ) (N : ℕ) (x : Fin n → ℝ) : ℂ :=
  (∏ i : Fin m, (x (Fin.castLE hm i) : ℂ)) *
    (∏ i : Fin n, (x i : ℂ) ^ (a - 1) * (((1 - x i / N) ^ N : ℝ) : ℂ)) *
    ((|vandermonde x| : ℝ) : ℂ) ^ (2 * c)

/-- `∏_{i<j} |tᵢ - tⱼ|^(2c) = |Δ(t)|^(2c)`. -/
theorem prod_ite_abs_cpow_eq {n : ℕ} (c : ℂ) (t : Fin n → ℝ) :
    (∏ i : Fin n, ∏ j : Fin n,
      if i.val < j.val then ((|t i - t j| : ℝ) : ℂ) ^ (2 * c) else 1) =
      ((|vandermonde t| : ℝ) : ℂ) ^ (2 * c) := by
  unfold vandermonde
  rw [Finset.abs_prod]
  simp_rw [Finset.abs_prod]
  rw [ofReal_prod_cpow _ _ (fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofReal_prod_cpow _ _ (fun j _ => abs_nonneg _)]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- After scaling by `N`, the Laguerre approximant is a power of `N` times Aomoto's integrand with
`b = N + 1`. -/
theorem lagApprox_smul {n m : ℕ} (hm : m ≤ n) (a c : ℂ) {N : ℕ} (hN : 0 < N)
    {t : Fin n → ℝ} (ht : ∀ i, 0 ≤ t i) :
    lagApprox n m hm a c N ((N : ℝ) • t) =
      (N : ℂ) ^ ((m : ℂ) + n * (a - 1) + ((n * (n - 1) : ℕ) : ℂ) * c) *
        (DLMF.Selberg.selbergIntegrand n a ((N : ℂ) + 1) c t *
          ∏ i : Fin m, (t (Fin.castLE hm i) : ℂ)) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold lagApprox DLMF.Selberg.selbergIntegrand
  rw [prod_ite_abs_cpow_eq, vandermonde_smul, abs_mul, abs_pow, abs_of_pos hNpos,
    Complex.ofReal_mul (_ ^ _), Complex.mul_cpow_ofReal_nonneg (by positivity) (abs_nonneg _),
    ofReal_pow_cpow hNpos]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
  have h1 : ∏ i : Fin m, ((N : ℂ) * (t (Fin.castLE hm i) : ℂ)) =
      (N : ℂ) ^ m * ∏ i : Fin m, (t (Fin.castLE hm i) : ℂ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 : ∏ i : Fin n, ((N : ℂ) * (t i : ℂ)) ^ (a - 1) * (((1 - N * t i / N) ^ N : ℝ) : ℂ) =
      ((N : ℂ) ^ (a - 1)) ^ n *
        ∏ i : Fin n, (t i : ℂ) ^ (a - 1) * (1 - (t i : ℂ)) ^ ((N : ℂ) + 1 - 1) := by
    rw [show ((N : ℂ) ^ (a - 1)) ^ n = ∏ _i : Fin n, (N : ℂ) ^ (a - 1) by simp,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hmul : ((N : ℂ) * (t i : ℂ)) ^ (a - 1) = (N : ℂ) ^ (a - 1) * (t i : ℂ) ^ (a - 1) := by
      have := Complex.mul_cpow_ofReal_nonneg hNpos.le (ht i) (a - 1)
      simpa using this
    rw [hmul, mul_div_cancel_left₀ _ hN0, add_sub_cancel_right, Complex.cpow_natCast]
    push_cast
    ring
  rw [h1, h2]
  have hexp : (N : ℂ) ^ m * ((N : ℂ) ^ (a - 1)) ^ n *
      (N : ℂ) ^ (((n * (n - 1) / 2 : ℕ) : ℂ) * (2 * c)) =
      (N : ℂ) ^ ((m : ℂ) + n * (a - 1) + ((n * (n - 1) : ℕ) : ℂ) * c) := by
    rw [Complex.cpow_add _ _ hNC, Complex.cpow_add _ _ hNC, ← Complex.cpow_nat_mul,
      Complex.cpow_natCast]
    congr 2
    rw [show ((n * (n - 1) : ℕ) : ℂ) = 2 * ((n * (n - 1) / 2 : ℕ) : ℂ) by
      have := two_mul_pairs n
      exact_mod_cast this.symm]
    ring
  rw [← hexp]
  ring

/-- Evaluation of the integral of the Laguerre approximant over `(0, N]ⁿ` by Aomoto's integral. -/
theorem integral_lagApprox_eq {n m : ℕ} (hm : m ≤ n) {a c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re)
    {N : ℕ} (hN : 0 < N) :
    ∫ x in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) N), lagApprox n m hm a c N x =
      (N : ℂ) ^ n * (N : ℂ) ^ ((m : ℂ) + n * (a - 1) + ((n * (n - 1) : ℕ) : ℂ) * c) *
        ((∏ j : Fin m, (a + (n - 1 - j : ℕ) * c) / (a + ((N : ℂ) + 1) + (2 * n - 2 - j : ℕ) * c)) *
          ∏ j : Fin n, Gamma (a + (j : ℕ) * c) * Gamma (((N : ℂ) + 1) + (j : ℕ) * c) *
            Gamma (1 + ((j : ℕ) + 1) * c) /
            (Gamma (a + ((N : ℂ) + 1) + (n + j - 1 : ℕ) * c) * Gamma (1 + c))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : 0 < ((N : ℂ) + 1).re := by simp; positivity
  rw [integral_pi_Ioc_scale _ hNpos, mul_assoc,
    ← DLMF.Selberg.aomoto_integral hm ha hb hc, Complex.ofReal_natCast]
  congr 1
  have hae : (Set.pi Set.univ fun _ => Ioc (0 : ℝ) 1 : Set (Fin n → ℝ)) =ᵐ[volume]
      (Set.pi Set.univ fun _ => Icc (0 : ℝ) 1) := by
    rw [volume_pi]
    have := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin n => (volume : Measure ℝ))
      (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ))
    rwa [← Set.pi_univ_Icc] at this
  rw [← setIntegral_congr_set hae, ← integral_const_mul]
  · refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) fun t ht => ?_
    exact lagApprox_smul hm a c hN fun i => (ht i (Set.mem_univ _)).1.le
/-! ### Domination -/

/-- `|Δ(x)| ≤ (∏ (1 + xᵢ))^(2n)` for `xᵢ ≥ 0`. -/
theorem abs_vandermonde_le {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    |vandermonde x| ≤ (∏ i, (1 + x i)) ^ (2 * n) := by
  unfold vandermonde
  rw [Finset.abs_prod]
  have hstep : ∀ i j : Fin n, |if i.val < j.val then x i - x j else 1| ≤ (1 + x i) * (1 + x j) := by
    intro i j
    have hi := hx i
    have hj := hx j
    split_ifs
    · rw [abs_le]; constructor <;> nlinarith
    · simp; nlinarith
  calc ∏ i, |∏ j, if i.val < j.val then x i - x j else 1|
      = ∏ i, ∏ j, |if i.val < j.val then x i - x j else 1| := by simp_rw [Finset.abs_prod]
    _ ≤ ∏ i : Fin n, ∏ j : Fin n, ((1 + x i) * (1 + x j)) := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _)
          fun i _ => Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => hstep i j
    _ = (∏ i, (1 + x i)) ^ (2 * n) := by
        simp_rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [Finset.prod_pow, two_mul, pow_add]

/-- `∏_{i<m} x_i ≤ ∏ (1 + xᵢ)` for `xᵢ ≥ 0`. -/
theorem prod_castLE_le {n m : ℕ} (hm : m ≤ n) {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    ∏ i : Fin m, x (Fin.castLE hm i) ≤ ∏ i, (1 + x i) := by
  calc ∏ i : Fin m, x (Fin.castLE hm i) ≤ ∏ i : Fin m, (1 + x (Fin.castLE hm i)) :=
        Finset.prod_le_prod₀ (fun i _ => hx _) fun i _ => by linarith [hx (Fin.castLE hm i)]
    _ = ∏ i ∈ Finset.univ.map (Fin.castLEEmb hm), (1 + x i) := by rw [Finset.prod_map]; rfl
    _ ≤ ∏ i, (1 + x i) :=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun i _ => by linarith [hx i]) fun i _ _ => by linarith [hx i]

/-- The one-variable majorant `y^{α-1} e^{-y} (1+y)^M`. -/
def lagMajor (α M : ℝ) (y : ℝ) : ℝ := y ^ (α - 1) * Real.exp (-y) * (1 + y) ^ M

/-- `y^(α-1) e^(-y) (1 + y)^M` is integrable on `(0, ∞)` for `α > 0`, `M ≥ 0`. -/
theorem integrableOn_lagMajor {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M) :
    IntegrableOn (lagMajor α M) (Ioi 0) := by
  have h1 := Real.GammaIntegral_convergent hα
  have h2 := Real.GammaIntegral_convergent (show 0 < α + M by linarith)
  refine ((h1.add h2).const_mul (2 ^ M)).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    unfold lagMajor
    refine ContinuousOn.mul (ContinuousOn.mul ?_ (by fun_prop)) ?_
    · exact ContinuousOn.rpow_const continuousOn_id fun y hy => Or.inl (ne_of_gt hy)
    · exact ContinuousOn.rpow_const (by fun_prop) fun y hy =>
        Or.inl (by have : (0 : ℝ) < y := hy; positivity)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun y (hy : 0 < y) => ?_
    unfold lagMajor
    have hb : (1 + y) ^ M ≤ 2 ^ M * (1 + y ^ M) := by
      rcases le_total y 1 with hy1 | hy1
      · calc (1 + y) ^ M ≤ 2 ^ M := Real.rpow_le_rpow (by positivity) (by linarith) hM
          _ ≤ 2 ^ M * (1 + y ^ M) := le_mul_of_one_le_right (by positivity)
              (by linarith [Real.rpow_nonneg hy.le M])
      · calc (1 + y) ^ M ≤ (2 * y) ^ M := Real.rpow_le_rpow (by positivity) (by linarith) hM
          _ = 2 ^ M * y ^ M := Real.mul_rpow (by norm_num) hy.le
          _ ≤ 2 ^ M * (1 + y ^ M) := by gcongr; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc y ^ (α - 1) * Real.exp (-y) * (1 + y) ^ M
        ≤ y ^ (α - 1) * Real.exp (-y) * (2 ^ M * (1 + y ^ M)) := by gcongr
      _ = 2 ^ M * (Real.exp (-y) * y ^ (α - 1) + Real.exp (-y) * y ^ (α + M - 1)) := by
          rw [show α + M - 1 = (α - 1) + M by ring, Real.rpow_add hy]
          ring

/-- The product majorant `∏ y_i^(α-1) e^(-yᵢ) (1 + yᵢ)^M` is integrable on `(0, ∞)ⁿ`. -/
theorem integrableOn_prod_lagMajor {n : ℕ} {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M) :
    IntegrableOn (fun x : Fin n → ℝ => ∏ i, lagMajor α M (x i))
      (Set.pi Set.univ fun _ => Ioi (0 : ℝ)) := by
  rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (fun _ => integrableOn_lagMajor hα hM)

/-- Domination of the Laguerre approximant on `(0, N]ⁿ` by the product majorant. -/
theorem norm_lagApprox_le {n m : ℕ} (hm : m ≤ n) {a c : ℂ} (hc : 0 < c.re) {N : ℕ}
    {x : Fin n → ℝ} (hx : ∀ i, x i ∈ Ioc (0 : ℝ) N) :
    ‖lagApprox n m hm a c N x‖ ≤ ∏ i, lagMajor a.re (1 + 4 * n * c.re) (x i) := by
  have hx0 : ∀ i, 0 ≤ x i := fun i => (hx i).1.le
  set P := ∏ i, (1 + x i) with hP
  have hP1 : 1 ≤ P := Finset.one_le_prod₀ fun i _ => by linarith [hx0 i]
  have hP0 : 0 < P := by linarith
  unfold lagApprox
  rw [norm_mul, norm_mul, norm_prod, norm_prod,
    Complex.norm_cpow_eq_rpow_re_of_nonneg (abs_nonneg _) (by simp; linarith)]
  have h1 : ∏ i : Fin m, ‖(x (Fin.castLE hm i) : ℂ)‖ ≤ P := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hx0 _)]
    exact prod_castLE_le hm hx0
  have h2 : ∏ i : Fin n, ‖(x i : ℂ) ^ (a - 1) * (((1 - x i / N) ^ N : ℝ) : ℂ)‖ ≤
      ∏ i : Fin n, (x i ^ (a.re - 1) * Real.exp (-x i)) := by
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    have hxN : x i ≤ N := (hx i).2
    have hN : (0 : ℝ) < N := lt_of_lt_of_le (hx i).1 hxN
    have hq : 0 ≤ 1 - x i / N := by rw [sub_nonneg, div_le_one hN]; exact hxN
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hx i).1, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq N)]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left (Real.one_sub_div_pow_le_exp_neg hxN)
      (Real.rpow_nonneg (hx0 i) _)
  have h3 : |vandermonde x| ^ (2 * c).re ≤ P ^ (4 * n * c.re) := by
    have hre : (2 * c).re = 2 * c.re := by simp
    rw [hre]
    calc |vandermonde x| ^ (2 * c.re) ≤ (P ^ (2 * n)) ^ (2 * c.re) :=
          Real.rpow_le_rpow (abs_nonneg _) (abs_vandermonde_le hx0) (by linarith)
      _ = P ^ (4 * n * c.re) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; push_cast; ring_nf
  calc (∏ i : Fin m, ‖(x (Fin.castLE hm i) : ℂ)‖) *
        (∏ i : Fin n, ‖(x i : ℂ) ^ (a - 1) * (((1 - x i / N) ^ N : ℝ) : ℂ)‖) *
        |vandermonde x| ^ (2 * c).re
      ≤ P * (∏ i : Fin n, (x i ^ (a.re - 1) * Real.exp (-x i))) * P ^ (4 * n * c.re) := by
        gcongr
        exact mul_nonneg hP0.le (Finset.prod_nonneg fun i _ =>
          mul_nonneg (Real.rpow_nonneg (hx0 i) _) (Real.exp_pos _).le)
    _ = (∏ i : Fin n, (x i ^ (a.re - 1) * Real.exp (-x i))) * P ^ (1 + 4 * n * c.re) := by
        rw [Real.rpow_add hP0, Real.rpow_one]; ring
    _ = ∏ i, lagMajor a.re (1 + 4 * n * c.re) (x i) := by
        rw [hP, ← Real.finsetProd_rpow _ _ fun i _ => by linarith [hx0 i],
          ← Finset.prod_mul_distrib]
        rfl

/-- The Laguerre approximant is measurable. -/
theorem measurable_lagApprox (n m : ℕ) (hm : m ≤ n) (a c : ℂ) (N : ℕ) :
    Measurable (lagApprox n m hm a c N) := by
  unfold lagApprox vandermonde
  fun_prop

/-- The Laguerre approximants converge pointwise to the integrand of 5.14.5. -/
theorem tendsto_lagApprox {n m : ℕ} (hm : m ≤ n) (a c : ℂ) (x : Fin n → ℝ) :
    Tendsto (fun N : ℕ => lagApprox n m hm a c N x) atTop (𝓝 (lagIntegrand n m hm a c x)) := by
  unfold lagApprox lagIntegrand
  refine (tendsto_const_nhds.mul (tendsto_finsetProd _ fun i _ => ?_)).mul tendsto_const_nhds
  refine tendsto_const_nhds.mul ?_
  have h := Real.tendsto_one_add_div_pow_exp (-x i)
  have h2 := (Complex.continuous_ofReal.tendsto _).comp h
  rw [Complex.ofReal_exp, Complex.ofReal_neg] at h2
  refine h2.congr fun N => ?_
  simp [neg_div, sub_eq_add_neg]

/-- The integrals of the Laguerre approximants converge to the integral of 5.14.5 (dominated
convergence). -/
theorem tendsto_integral_lagApprox {n m : ℕ} (hm : m ≤ n) {a c : ℂ} (ha : 0 < a.re)
    (hc : 0 < c.re) :
    Tendsto (fun N : ℕ => ∫ x in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) N),
        lagApprox n m hm a c N x) atTop
      (𝓝 (∫ x in Set.pi Set.univ (fun _ => Ioi (0 : ℝ)), lagIntegrand n m hm a c x)) := by
  have hsub : ∀ N : ℕ, (Set.pi Set.univ (fun _ => Ioc (0 : ℝ) N) : Set (Fin n → ℝ)) ⊆
      Set.pi Set.univ (fun _ => Ioi (0 : ℝ)) :=
    fun N x hx i hi => (hx i hi).1
  have hrw : ∀ N : ℕ, ∫ x in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) N), lagApprox n m hm a c N x =
      ∫ x in Set.pi Set.univ (fun _ => Ioi (0 : ℝ)),
        (Set.pi Set.univ (fun _ => Ioc (0 : ℝ) N)).indicator (lagApprox n m hm a c N) x := by
    intro N
    rw [setIntegral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Ioc),
      Set.inter_eq_right.mpr (hsub N)]
  simp_rw [hrw]
  have hM : (0 : ℝ) ≤ 1 + 4 * n * c.re := by positivity
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ∏ i, lagMajor a.re (1 + 4 * n * c.re) (x i))
    (Eventually.of_forall fun N => ((measurable_lagApprox n m hm a c N).indicator
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)).aestronglyMeasurable)
    (Eventually.of_forall fun N => ?_) (integrableOn_prod_lagMajor ha hM) ?_
  · rw [ae_restrict_iff' (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)]
    refine Eventually.of_forall fun x hx => ?_
    by_cases hxN : x ∈ Set.pi Set.univ (fun _ => Ioc (0 : ℝ) N)
    · rw [Set.indicator_of_mem hxN]
      exact norm_lagApprox_le hm hc fun i => hxN i (Set.mem_univ _)
    · rw [Set.indicator_of_notMem hxN, norm_zero]
      refine Finset.prod_nonneg fun i _ => ?_
      have := hx i (Set.mem_univ _)
      unfold lagMajor
      have : (0 : ℝ) < x i := this
      positivity
  · rw [ae_restrict_iff' (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)]
    refine Eventually.of_forall fun x hx => ?_
    have hev : ∀ᶠ N : ℕ in atTop, x ∈ Set.pi Set.univ (fun _ => Ioc (0 : ℝ) N) := by
      have : ∀ i, ∀ᶠ N : ℕ in atTop, x i ≤ N := fun i =>
        tendsto_natCast_atTop_atTop.eventually_ge_atTop (x i)
      filter_upwards [Filter.eventually_all.2 this] with N hN i _
      exact ⟨hx i (Set.mem_univ _), hN i⟩
    refine (tendsto_lagApprox hm a c x).congr' ?_
    filter_upwards [hev] with N hN
    rw [Set.indicator_of_mem hN]

/-! ### The limit of the right-hand side -/

/-- `N/(N + β) → 1`. -/
theorem tendsto_natCast_div_add (β : ℂ) :
    Tendsto (fun N : ℕ => (N : ℂ) / (N + β)) atTop (𝓝 1) := by
  have h0 : Tendsto (fun N : ℕ => β / (N : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_div, Complex.norm_natCast]
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun N : ℕ => ((N + β) / (N : ℂ))⁻¹) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℂ))).add h0
    rw [add_zero] at this
    have h2 := this.inv₀ one_ne_zero
    rw [inv_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with N hN
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    rw [add_div, div_self this]
  refine h1.congr fun N => ?_
  rw [inv_div]

/-- `Γ(N + p)/Γ(N + q) · N^(q-p) → 1`. -/
theorem tendsto_Gamma_ratio_nat (p q : ℂ) :
    Tendsto (fun N : ℕ => Gamma (N + p) / Gamma (N + q) * (N : ℂ) ^ (q - p)) atTop (𝓝 1) := by
  have h := (Gamma_ratio_power (a := p) (b := q)).comp tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [Function.comp_apply, Complex.ofReal_natCast]
  rw [div_eq_mul_inv _ ((N : ℂ) ^ (p - q)), ← Complex.cpow_neg, neg_sub]

/-- The evaluated right-hand sides of the Laguerre approximation converge to the right-hand side of
5.14.5. -/
theorem tendsto_lag_rhs {n m : ℕ} (hn : 0 < n) {a c : ℂ} :
    Tendsto (fun N : ℕ =>
      (N : ℂ) ^ n * (N : ℂ) ^ ((m : ℂ) + n * (a - 1) + ((n * (n - 1) : ℕ) : ℂ) * c) *
        ((∏ j : Fin m, (a + (n - 1 - j : ℕ) * c) / (a + ((N : ℂ) + 1) + (2 * n - 2 - j : ℕ) * c)) *
          ∏ j : Fin n, Gamma (a + (j : ℕ) * c) * Gamma (((N : ℂ) + 1) + (j : ℕ) * c) *
            Gamma (1 + ((j : ℕ) + 1) * c) /
            (Gamma (a + ((N : ℂ) + 1) + (n + j - 1 : ℕ) * c) * Gamma (1 + c)))) atTop
      (𝓝 ((∏ j : Fin m, (a + (n - 1 - j : ℕ) * c)) *
        ∏ j : Fin n, (Gamma (a + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) /
          Gamma (1 + c)))) := by
  set w : ℂ := a + ((n - 1 : ℕ) : ℂ) * c with hw
  have hlim : Tendsto (fun N : ℕ =>
      (∏ j : Fin m, (a + (n - 1 - j : ℕ) * c) *
        ((N : ℂ) / (N + (a + 1 + (2 * n - 2 - j : ℕ) * c)))) *
      ∏ j : Fin n, (Gamma (a + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) / Gamma (1 + c) *
        (Gamma (N + (1 + (j : ℕ) * c)) / Gamma (N + (a + 1 + (n + j - 1 : ℕ) * c)) *
          (N : ℂ) ^ ((a + 1 + (n + j - 1 : ℕ) * c) - (1 + (j : ℕ) * c))))) atTop
      (𝓝 ((∏ j : Fin m, (a + (n - 1 - j : ℕ) * c)) *
        ∏ j : Fin n, (Gamma (a + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) /
          Gamma (1 + c)))) := by
    refine Tendsto.mul ?_ ?_
    · have := tendsto_finsetProd (Finset.univ : Finset (Fin m)) fun j _ =>
        (tendsto_const_nhds (x := a + ((n - 1 - j : ℕ) : ℂ) * c)).mul
          (tendsto_natCast_div_add (a + 1 + ((2 * n - 2 - j : ℕ) : ℂ) * c))
      simpa using this
    · have := tendsto_finsetProd (Finset.univ : Finset (Fin n)) fun j _ =>
        (tendsto_const_nhds (x := Gamma (a + ((j : ℕ) : ℂ) * c) *
          Gamma (1 + (((j : ℕ) : ℂ) + 1) * c) / Gamma (1 + c))).mul
          (tendsto_Gamma_ratio_nat (1 + ((j : ℕ) : ℂ) * c)
            (a + 1 + ((n + j - 1 : ℕ) : ℂ) * c))
      simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hexp : ∀ j : Fin n, (a + 1 + ((n + j - 1 : ℕ) : ℂ) * c) - (1 + ((j : ℕ) : ℂ) * c) = w := by
    intro j
    rw [hw, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  simp_rw [hexp]
  -- regroup the powers of `N`
  have hpow : (N : ℂ) ^ n * (N : ℂ) ^ ((m : ℂ) + n * (a - 1) + ((n * (n - 1) : ℕ) : ℂ) * c) =
      (∏ _j : Fin m, (N : ℂ)) * ∏ _j : Fin n, (N : ℂ) ^ w := by
    rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.card_univ, Fintype.card_fin, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast,
      ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hN', ← Complex.cpow_add _ _ hN']
    congr 1
    rw [hw, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast; ring
  rw [hpow]
  rw [show ∀ (A B C D : ℂ), A * B * (C * D) = (A * C) * (B * D) from fun A B C D => by ring,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    field_simp
    ring_nf
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [show ((N : ℂ) + 1) + ((j : ℕ) : ℂ) * c = N + (1 + ((j : ℕ) : ℂ) * c) by ring,
      show a + ((N : ℂ) + 1) + ((n + j - 1 : ℕ) : ℂ) * c =
        N + (a + 1 + ((n + j - 1 : ℕ) : ℂ) * c) by ring]
    ring

/-- Laguerre form of the Selberg integral, DLMF 5.14.5: the integral over `(0, ∞)ⁿ` of
`t₁ ⋯ tₘ ∏ tᵢ^(a-1) e^(-tᵢ) |Δ(t)|^(2c)` is an explicit product of Gamma values. -/
@[dlmf 5.14.E5]
theorem selberg_laguerrePolyL {n m : ℕ} {a c : ℂ} (hm : m ≤ n)
    (ha : 0 < a.re) (hc : 0 < c.re) :
    ∫ t : Fin n → ℝ in Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ),
        (∏ i : Fin m, (t (Fin.castLE hm i) : ℂ)) *
          (∏ i : Fin n, (t i : ℂ) ^ (a - 1) * Complex.exp (-(t i : ℂ))) *
          ((|vandermonde t| : ℝ) : ℂ) ^ (2 * c) =
      (∏ k : Fin m, (a + (n - 1 - k : ℕ) * c)) *
        (∏ k : Fin n, Complex.Gamma (a + (n - 1 - k : ℕ) * c) *
          Complex.Gamma (1 + ((k : ℕ) + 1) * c)) /
        Complex.Gamma (1 + c) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : m = 0 := Nat.le_zero.mp hm
    have hset : (Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ) : Set (Fin 0 → ℝ)) = Set.univ :=
      Set.eq_univ_of_forall fun t => fun i => i.elim0
    rw [hset, Measure.restrict_univ]
    simp [vandermonde, Measure.real, volume_pi]
  have hlim := tendsto_integral_lagApprox hm ha hc
  have hrhs := tendsto_lag_rhs (m := m) (a := a) (c := c) hn
  have hrhs' := hrhs.congr' (by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (integral_lagApprox_eq hm ha hc hN).symm)
  have hJ := tendsto_nhds_unique hlim hrhs'
  change ∫ t in _, lagIntegrand n m hm a c t = _
  rw [hJ]
  have hrefl : ∏ k : Fin n, Complex.Gamma (a + (n - 1 - k : ℕ) * c) =
      ∏ k : Fin n, Complex.Gamma (a + (k : ℕ) * c) := by
    rw [Fin.prod_univ_eq_prod_range (fun k => Complex.Gamma (a + (n - 1 - k : ℕ) * c)) n,
      Fin.prod_univ_eq_prod_range (fun k => Complex.Gamma (a + (k : ℕ) * c)) n]
    exact Finset.prod_range_reflect (fun k => Complex.Gamma (a + (k : ℕ) * c)) n
  rw [Finset.prod_mul_distrib, hrefl, Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

end LaguerreLimit

section HermiteLimit

/-! ### Mehta's integral as a limit of Selberg's integral

With `a = b = N + 1` and the affine substitution `x = 2√(2N) t - √(2N)`, Selberg's integral
becomes an integral of `(1 - x²/(2N))^N`-weights over `[-√(2N), √(2N)]ⁿ`. Integrability of the
limit integrand on the full domain `Re c > -1/n` follows from Fatou's lemma, since for real `c`
the approximating integrals are nonnegative and converge; dominated convergence then gives
the value, with the duplication formula for the right-hand side. -/

open Set Filter
open scoped Topology

/-! ### Affine change of variables on a cube -/

/-- Affine change of variables from `[-s, s]ⁿ` to `[0, 1]ⁿ`. -/
theorem integral_pi_Icc_affine {n : ℕ} (g : (Fin n → ℝ) → ℂ) {s : ℝ} (hs : 0 < s) :
    ∫ x in Set.pi Set.univ (fun _ => Icc (-s) s), g x =
      ((2 * s : ℝ) : ℂ) ^ n *
        ∫ t in Set.pi Set.univ (fun _ => Icc (0 : ℝ) 1), g (fun i => 2 * s * t i - s) := by
  set S := (Set.pi Set.univ (fun _ => Icc (-s) s) : Set (Fin n → ℝ)) with hS
  set T := (Set.pi Set.univ (fun _ => Icc (0 : ℝ) 1) : Set (Fin n → ℝ)) with hT
  have hL : (0 : ℝ) < 2 * s := by positivity
  set v : Fin n → ℝ := fun _ => -s with hv
  have hmem : ∀ t : Fin n → ℝ, (2 * s) • t + v ∈ S ↔ t ∈ T := by
    intro t
    simp only [hS, hT, hv, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · nlinarith
      · nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
  set F := S.indicator g with hF
  have h1 := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure (Fin n → ℝ)))
    (fun y => F (y + v)) (2 * s)
  rw [Module.finrank_fin_fun, integral_add_right_eq_self (fun y => F y) v] at h1
  have hind : (fun t : Fin n → ℝ => F ((2 * s) • t + v)) =
      T.indicator (fun t => g (fun i => 2 * s * t i - s)) := by
    ext t
    by_cases ht : t ∈ T
    · rw [hF, Set.indicator_of_mem ((hmem t).mpr ht), Set.indicator_of_mem ht]
      congr 1
    · rw [hF, Set.indicator_of_notMem (fun h => ht ((hmem t).mp h)), Set.indicator_of_notMem ht]
  rw [hind, integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Icc), hF,
    integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Icc)] at h1
  rw [h1, abs_of_pos (inv_pos.mpr (pow_pos hL n)), Complex.real_smul]
  push_cast
  have h2 : (2 : ℂ) * (s : ℂ) ≠ 0 := by
    have : ((2 * s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    simpa using this
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n h2), one_mul]

/-! ### The Hermite integrand and its approximations -/

/-- The integrand of 5.14.6. -/
def hermIntegrand (n : ℕ) (c : ℂ) (x : Fin n → ℝ) : ℂ :=
  ((|vandermonde x| : ℝ) : ℂ) ^ (2 * c) * ∏ k : Fin n, Complex.exp (-(x k : ℂ) ^ 2 / 2)

/-- Its approximation with `(1 - x²/(2N))^N` in place of `e^{-x²/2}`. -/
def hermApprox (n : ℕ) (c : ℂ) (N : ℕ) (x : Fin n → ℝ) : ℂ :=
  ((|vandermonde x| : ℝ) : ℂ) ^ (2 * c) * ∏ k : Fin n, (((1 - x k ^ 2 / (2 * N)) ^ N : ℝ) : ℂ)

/-- `Δ(L t - v) = L^(n(n-1)/2) Δ(t)`. -/
theorem vandermonde_affine {n : ℕ} (L v : ℝ) (t : Fin n → ℝ) :
    vandermonde (fun i => L * t i - v) = L ^ (n * (n - 1) / 2) * vandermonde t := by
  rw [← vandermonde_smul]
  unfold vandermonde
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  split_ifs
  · simp [Pi.smul_apply, smul_eq_mul]
  · rfl

/-- After the affine substitution `x = 2√(2N) t - √(2N)`, the Hermite approximant is a constant
times Selberg's integrand with `a = b = N + 1`. -/
theorem hermApprox_affine {n : ℕ} (c : ℂ) {N : ℕ} (hN : 0 < N) (t : Fin n → ℝ) :
    hermApprox n c N (fun i => 2 * √(2 * N) * t i - √(2 * N)) =
      (4 : ℂ) ^ (n * N) * ((2 * √(2 * N) : ℝ) : ℂ) ^ (((n * (n - 1) : ℕ) : ℂ) * c) *
        DLMF.Selberg.selbergIntegrand n ((N : ℂ) + 1) ((N : ℂ) + 1) c t := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set s := √(2 * N) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hss : s ^ 2 = 2 * N := Real.sq_sqrt (by positivity)
  have hL : (0 : ℝ) < 2 * s := by positivity
  unfold hermApprox DLMF.Selberg.selbergIntegrand
  rw [prod_ite_abs_cpow_eq, vandermonde_affine, abs_mul, abs_pow, abs_of_pos hL,
    Complex.ofReal_mul (_ ^ _), Complex.mul_cpow_ofReal_nonneg (by positivity) (abs_nonneg _),
    ofReal_pow_cpow hL]
  have hfac : ∀ i : Fin n, (((1 - (2 * s * t i - s) ^ 2 / (2 * N)) ^ N : ℝ) : ℂ) =
      4 ^ N * ((t i : ℂ) ^ ((N : ℂ) + 1 - 1) * (1 - (t i : ℂ)) ^ ((N : ℂ) + 1 - 1)) := by
    intro i
    have h1 : 1 - (2 * s * t i - s) ^ 2 / (2 * N) = 4 * (t i * (1 - t i)) := by
      have : (2 * s * t i - s) ^ 2 = s ^ 2 * (2 * t i - 1) ^ 2 := by ring
      rw [this, hss]
      field_simp
      ring
    rw [h1, add_sub_cancel_right, Complex.cpow_natCast, Complex.cpow_natCast, ← mul_pow,
      ← mul_pow]
    push_cast
    ring
  rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hexp : ((2 * s : ℝ) : ℂ) ^ (((n * (n - 1) / 2 : ℕ) : ℂ) * (2 * c)) =
      ((2 * s : ℝ) : ℂ) ^ (((n * (n - 1) : ℕ) : ℂ) * c) := by
    congr 1
    rw [show ((n * (n - 1) : ℕ) : ℂ) = 2 * ((n * (n - 1) / 2 : ℕ) : ℂ) by
      have := two_mul_pairs n
      exact_mod_cast this.symm]
    ring
  rw [hexp]
  ring

/-- Evaluation of the integral of the Hermite approximant over `[-√(2N), √(2N)]ⁿ` by Selberg's
integral. -/
theorem integral_hermApprox_eq {n : ℕ} {c : ℂ} {N : ℕ}
    (hc : c ∈ DLMF.Selberg.cDomain n ((N : ℂ) + 1) ((N : ℂ) + 1)) (hN : 0 < N) :
    ∫ x in Set.pi Set.univ (fun _ => Icc (-√(2 * N)) √(2 * N)), hermApprox n c N x =
      ((2 * √(2 * N) : ℝ) : ℂ) ^ n * ((4 : ℂ) ^ (n * N) *
        ((2 * √(2 * N) : ℝ) : ℂ) ^ (((n * (n - 1) : ℕ) : ℂ) * c) *
          DLMF.Selberg.selbergRHS n ((N : ℂ) + 1) ((N : ℂ) + 1) c) := by
  have hs0 : 0 < √(2 * N) := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < ((N : ℂ) + 1).re := by simp; positivity
  rw [integral_pi_Icc_affine _ hs0]
  congr 1
  simp_rw [hermApprox_affine c hN]
  rw [integral_const_mul]
  congr 1
  exact DLMF.Selberg.selbergInt_eq hb hb hc

/-- The Hermite approximant is measurable. -/
theorem measurable_hermApprox (n : ℕ) (c : ℂ) (N : ℕ) : Measurable (hermApprox n c N) := by
  unfold hermApprox vandermonde
  fun_prop

/-- The Hermite approximants converge pointwise to the integrand of 5.14.6. -/
theorem tendsto_hermApprox {n : ℕ} (c : ℂ) (x : Fin n → ℝ) :
    Tendsto (fun N : ℕ => hermApprox n c N x) atTop (𝓝 (hermIntegrand n c x)) := by
  unfold hermApprox hermIntegrand
  refine tendsto_const_nhds.mul (tendsto_finsetProd _ fun i _ => ?_)
  have h := Real.tendsto_one_add_div_pow_exp (-x i ^ 2 / 2)
  have h2 := (Complex.continuous_ofReal.tendsto _).comp h
  rw [Complex.ofReal_exp] at h2
  refine (h2.congr fun N => ?_).trans (le_of_eq ?_)
  · simp only [Function.comp_apply]
    congr 2
    ring
  · congr 2
    push_cast
    ring

/-! ### The limit of the right-hand side -/

/-- `x^w = exp(w log x)` for `x > 0`. -/
theorem herm_ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    ((x : ℝ) : ℂ) ^ w = Complex.exp (w * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
    mul_comm]

/-- `x = exp(log x)` for `x > 0`. -/
theorem herm_ofReal_eq_exp {x : ℝ} (hx : 0 < x) : ((x : ℝ) : ℂ) = Complex.exp (Real.log x : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log hx]

/-- One factor of the Hermite right-hand side, rewritten via the duplication formula. -/
theorem herm_factor_eq {n : ℕ} (hn : 0 < n) (c : ℂ) (j : ℕ) {N : ℕ} (hN : 0 < N) :
    ((2 * √(2 * N) : ℝ) : ℂ) ^ (1 + ((n - 1 : ℕ) : ℂ) * c) * (4 : ℂ) ^ N *
      (Gamma ((N : ℂ) + 1 + (j : ℂ) * c) * Gamma ((N : ℂ) + 1 + (j : ℂ) * c) *
        Gamma (1 + ((j : ℂ) + 1) * c) /
        (Gamma ((N : ℂ) + 1 + ((N : ℂ) + 1) + ((n + j - 1 : ℕ) : ℂ) * c) * Gamma (1 + c))) =
      ((√(2 * π) : ℝ) : ℂ) *
        Complex.exp (((j : ℂ) - ((n - 1 : ℕ) : ℂ) / 2) * c *
          ((Real.log N - Real.log 2 : ℝ) : ℂ)) *
        (Gamma (N + (1 + (j : ℂ) * c)) / Gamma (N + (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2)) *
          (N : ℂ) ^ ((1 + ((n + j - 1 : ℕ) : ℂ) * c / 2) - (1 + (j : ℂ) * c))) *
        (Gamma (N + (1 + (j : ℂ) * c)) /
          Gamma (N + (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2 + 1 / 2)) *
          (N : ℂ) ^ ((1 + ((n + j - 1 : ℕ) : ℂ) * c / 2 + 1 / 2) - (1 + (j : ℂ) * c))) *
        (Gamma (1 + ((j : ℂ) + 1) * c) / Gamma (1 + c)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set z : ℂ := N + (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2) with hz
  have hdup := Complex.Gamma_mul_Gamma_add_half z
  have h2z : (N : ℂ) + 1 + ((N : ℂ) + 1) + ((n + j - 1 : ℕ) : ℂ) * c = 2 * z := by
    rw [hz]; ring
  have hzh : N + (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2 + 1 / 2) = z + 1 / 2 := by rw [hz]; ring
  rw [h2z, hzh, show (N : ℂ) + 1 + (j : ℂ) * c = N + (1 + (j : ℂ) * c) by ring]
  have hpi : ((√π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h2pow : (2 : ℂ) ^ (1 - 2 * z) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; simp
  -- replace `Γ(2z)`
  have hG2 : Gamma (2 * z) = Gamma z * Gamma (z + 1 / 2) / ((2 : ℂ) ^ (1 - 2 * z) * √π) := by
    rw [hdup]; field_simp
  rw [hG2]
  have hs : (0 : ℝ) < 2 * √(2 * N) := by positivity
  have hl1 : Real.log (2 * √(2 * N)) = Real.log 2 + (Real.log 2 + Real.log N) / 2 := by
    rw [Real.log_mul (by norm_num) (Real.sqrt_pos.mpr (by positivity)).ne', Real.log_sqrt
      (by positivity), Real.log_mul (by norm_num) hNpos.ne']
  have hl2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hl3 : Real.log √(2 * π) = (Real.log 2 + Real.log π) / 2 := by
    rw [Real.log_sqrt (by positivity), Real.log_mul (by norm_num) Real.pi_pos.ne']
  have hl4 : Real.log √π = Real.log π / 2 := Real.log_sqrt Real.pi_pos.le
  have hcast : ((n + j - 1 : ℕ) : ℂ) = n + j - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hcast' : ((n - 1 : ℕ) : ℂ) = n - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  -- the scalar identity
  have hpow : ((2 * √(2 * N) : ℝ) : ℂ) ^ (1 + ((n - 1 : ℕ) : ℂ) * c) * (4 : ℂ) ^ N *
      ((2 : ℂ) ^ (1 - 2 * z) * ((√π : ℝ) : ℂ)) =
      ((√(2 * π) : ℝ) : ℂ) *
        Complex.exp (((j : ℂ) - ((n - 1 : ℕ) : ℂ) / 2) * c *
          ((Real.log N - Real.log 2 : ℝ) : ℂ)) *
        ((N : ℂ) ^ ((1 + ((n + j - 1 : ℕ) : ℂ) * c / 2) - (1 + (j : ℂ) * c)) *
          (N : ℂ) ^ ((1 + ((n + j - 1 : ℕ) : ℂ) * c / 2 + 1 / 2) - (1 + (j : ℂ) * c))) := by
    have hN' : ((N : ℕ) : ℂ) = ((N : ℝ) : ℂ) := (Complex.ofReal_natCast N).symm
    rw [herm_ofReal_cpow_eq_exp hs, hN', herm_ofReal_cpow_eq_exp hNpos,
      herm_ofReal_cpow_eq_exp hNpos,
      show (4 : ℂ) ^ N = Complex.exp ((N : ℂ) * (Real.log 4 : ℂ)) by
        rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, ← Complex.cpow_natCast,
          herm_ofReal_cpow_eq_exp (by norm_num)],
      show (2 : ℂ) ^ (1 - 2 * z) = Complex.exp ((1 - 2 * z) * (Real.log 2 : ℂ)) by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, herm_ofReal_cpow_eq_exp (by norm_num)],
      herm_ofReal_eq_exp (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * π)),
      herm_ofReal_eq_exp (Real.sqrt_pos.mpr Real.pi_pos)]
    simp only [← Complex.exp_add]
    congr 1
    rw [hl1, hl2, hl3, hl4, hz, hcast, hcast']
    push_cast
    ring
  calc ((2 * √(2 * N) : ℝ) : ℂ) ^ (1 + ((n - 1 : ℕ) : ℂ) * c) * (4 : ℂ) ^ N *
        (Gamma (N + (1 + (j : ℂ) * c)) * Gamma (N + (1 + (j : ℂ) * c)) *
          Gamma (1 + ((j : ℂ) + 1) * c) /
          (Gamma z * Gamma (z + 1 / 2) / ((2 : ℂ) ^ (1 - 2 * z) * ((√π : ℝ) : ℂ)) *
            Gamma (1 + c)))
      = (((2 * √(2 * N) : ℝ) : ℂ) ^ (1 + ((n - 1 : ℕ) : ℂ) * c) * (4 : ℂ) ^ N *
          ((2 : ℂ) ^ (1 - 2 * z) * ((√π : ℝ) : ℂ))) *
          (Gamma (N + (1 + (j : ℂ) * c)) * Gamma (N + (1 + (j : ℂ) * c)) *
            Gamma (1 + ((j : ℂ) + 1) * c) / (Gamma z * Gamma (z + 1 / 2) * Gamma (1 + c))) := by
        simp only [div_eq_mul_inv, mul_inv, inv_inv]; ring
    _ = _ := by rw [hpow, hz]; simp only [div_eq_mul_inv, mul_inv]; ring

/-- `∑_{j<n} (j - (n - 1)/2) = 0`. -/
theorem sum_fin_sub_half (n : ℕ) :
    ∑ j : Fin n, ((j : ℕ) - ((n - 1 : ℕ) : ℂ) / 2) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range (fun j => ((j : ℕ) : ℂ)) n, ← Nat.cast_sum]
  have h := Finset.sum_range_id_mul_two n
  have h' : ((∑ i ∈ Finset.range n, i : ℕ) : ℂ) * 2 = n * ((n - 1 : ℕ) : ℂ) := by
    exact_mod_cast h
  rw [nsmul_eq_mul]
  linear_combination h' / 2

/-- The evaluated right-hand sides of the Hermite approximation converge to `∏ⱼ √(2π) Γ(1 + (j +
1)c)/Γ(1 + c)`. -/
theorem tendsto_herm_rhs {n : ℕ} (hn : 0 < n) (c : ℂ) :
    Tendsto (fun N : ℕ => ((2 * √(2 * N) : ℝ) : ℂ) ^ n * ((4 : ℂ) ^ (n * N) *
        ((2 * √(2 * N) : ℝ) : ℂ) ^ (((n * (n - 1) : ℕ) : ℂ) * c) *
          DLMF.Selberg.selbergRHS n ((N : ℂ) + 1) ((N : ℂ) + 1) c)) atTop
      (𝓝 (∏ j : Fin n, (((√(2 * π) : ℝ) : ℂ) *
        (Gamma (1 + (((j : ℕ) : ℂ) + 1) * c) / Gamma (1 + c))))) := by
  have hlim : Tendsto (fun N : ℕ => ∏ j : Fin n, (((√(2 * π) : ℝ) : ℂ) *
      (Gamma (N + (1 + ((j : ℕ) : ℂ) * c)) / Gamma (N + (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2)) *
        (N : ℂ) ^ ((1 + ((n + j - 1 : ℕ) : ℂ) * c / 2) - (1 + ((j : ℕ) : ℂ) * c))) *
      (Gamma (N + (1 + ((j : ℕ) : ℂ) * c)) /
        Gamma (N + (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2 + 1 / 2)) *
        (N : ℂ) ^ ((1 + ((n + j - 1 : ℕ) : ℂ) * c / 2 + 1 / 2) - (1 + ((j : ℕ) : ℂ) * c))) *
      (Gamma (1 + (((j : ℕ) : ℂ) + 1) * c) / Gamma (1 + c)))) atTop
      (𝓝 (∏ j : Fin n, (((√(2 * π) : ℝ) : ℂ) *
        (Gamma (1 + (((j : ℕ) : ℂ) + 1) * c) / Gamma (1 + c))))) := by
    have := tendsto_finsetProd (Finset.univ : Finset (Fin n)) fun j _ =>
      (((tendsto_const_nhds (x := ((√(2 * π) : ℝ) : ℂ))).mul
        (tendsto_Gamma_ratio_nat (1 + ((j : ℕ) : ℂ) * c)
          (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2))).mul
        (tendsto_Gamma_ratio_nat (1 + ((j : ℕ) : ℂ) * c)
          (1 + ((n + j - 1 : ℕ) : ℂ) * c / 2 + 1 / 2))).mul
        (tendsto_const_nhds (x := Gamma (1 + (((j : ℕ) : ℂ) + 1) * c) / Gamma (1 + c)))
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : (0 : ℝ) < 2 * √(2 * N) := by positivity
  have hsC : ((2 * √(2 * N) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  -- rewrite the left side as a product of the factors of `herm_factor_eq`
  have hsplit : ((2 * √(2 * N) : ℝ) : ℂ) ^ n * ((4 : ℂ) ^ (n * N) *
      ((2 * √(2 * N) : ℝ) : ℂ) ^ (((n * (n - 1) : ℕ) : ℂ) * c) *
        DLMF.Selberg.selbergRHS n ((N : ℂ) + 1) ((N : ℂ) + 1) c) =
      ∏ j : Fin n, (((2 * √(2 * N) : ℝ) : ℂ) ^ (1 + ((n - 1 : ℕ) : ℂ) * c) * (4 : ℂ) ^ N *
        (Gamma ((N : ℂ) + 1 + ((j : ℕ) : ℂ) * c) * Gamma ((N : ℂ) + 1 + ((j : ℕ) : ℂ) * c) *
          Gamma (1 + (((j : ℕ) : ℂ) + 1) * c) /
          (Gamma ((N : ℂ) + 1 + ((N : ℂ) + 1) + ((n + j - 1 : ℕ) : ℂ) * c) *
            Gamma (1 + c)))) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, DLMF.Selberg.selbergRHS, pow_mul]
    have hpw : ((2 * √(2 * N) : ℝ) : ℂ) ^ n *
        ((2 * √(2 * N) : ℝ) : ℂ) ^ (((n * (n - 1) : ℕ) : ℂ) * c) =
        (((2 * √(2 * N) : ℝ) : ℂ) ^ (1 + ((n - 1 : ℕ) : ℂ) * c)) ^ n := by
      rw [← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hsC]
      congr 1
      rw [Nat.cast_mul]
      ring
    rw [← hpw]
    ring
  rw [hsplit]
  have hf := fun j : ℕ => herm_factor_eq (n := n) hn c j hN
  simp only [hf]
  -- the exponential factors multiply to one
  have hexp : ∏ j : Fin n, Complex.exp ((((j : ℕ) : ℂ) - ((n - 1 : ℕ) : ℂ) / 2) * c *
      ((Real.log N - Real.log 2 : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_sum, ← Finset.sum_mul, ← Finset.sum_mul, sum_fin_sub_half n]
    simp
  rw [← one_mul (∏ j : Fin n, _), ← hexp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

/-! ### Integrability on the full domain -/

/-- `-1 < nσ` when `-1/n < σ`. -/
theorem neg_one_lt_mul_of_div_lt {n : ℕ} (hn : 0 < n) {σ : ℝ} (hσ : (-1 / n : ℝ) < σ) :
    -1 < n * σ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_iff₀ hn'] at hσ
  linarith

/-- `1 + kσ > 0` for `k ≤ n` when `-1/n < σ`. -/
theorem one_add_mul_pos {n : ℕ} (hn : 0 < n) {σ : ℝ} (hσ : (-1 / n : ℝ) < σ) {k : ℕ}
    (hk : k ≤ n) : 0 < 1 + k * σ := by
  have h := neg_one_lt_mul_of_div_lt hn hσ
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  rcases le_or_gt 0 σ with h0 | h0
  · positivity
  · nlinarith

/-- For `Re c > -1/n`, `c` lies in Selberg's parameter domain with `a = b = N + 1`. -/
theorem mem_cDomain_herm {n : ℕ} (hn : 0 < n) {c : ℂ} (hc : (-1 / n : ℝ) < c.re) (N : ℕ) :
    c ∈ DLMF.Selberg.cDomain n ((N : ℂ) + 1) ((N : ℂ) + 1) := by
  have h1 := neg_one_lt_mul_of_div_lt hn hc
  have h2 := one_add_mul_pos hn hc (Nat.sub_le n 1)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine ⟨by linarith, ?_, ?_⟩ <;> simp <;> linarith

/-- The modulus of the Hermite integrand for a real exponent `σ`. -/
def hermBound (n : ℕ) (σ : ℝ) (x : Fin n → ℝ) : ℝ :=
  |vandermonde x| ^ (2 * σ) * ∏ k : Fin n, Real.exp (-x k ^ 2 / 2)

/-- The Hermite majorant is nonnegative. -/
theorem hermBound_nonneg (n : ℕ) (σ : ℝ) (x : Fin n → ℝ) : 0 ≤ hermBound n σ x := by
  unfold hermBound
  positivity

/-- The Hermite majorant is measurable. -/
theorem measurable_hermBound (n : ℕ) (σ : ℝ) : Measurable (hermBound n σ) := by
  unfold hermBound vandermonde
  fun_prop

/-- `Δ(x) ≠ 0` when the coordinates of `x` are distinct. -/
theorem vandermonde_ne_zero {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i j, i ≠ j → x i ≠ x j) :
    vandermonde x ≠ 0 := by
  unfold vandermonde
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  split_ifs with h
  · exact sub_ne_zero.mpr (hx i j (Fin.ne_of_lt h))
  · exact one_ne_zero

/-- `Δ(x) ≠ 0` for almost every `x`. -/
theorem ae_vandermonde_ne_zero (n : ℕ) : ∀ᵐ x : Fin n → ℝ, vandermonde x ≠ 0 := by
  filter_upwards [DLMF.Selberg.ae_coords_ne n] with x hx using vandermonde_ne_zero hx

/-- `‖|Δ(x)|^(2c)‖ = |Δ(x)|^(2 Re c)` when `Δ(x) ≠ 0`. -/
theorem norm_vandermonde_cpow {n : ℕ} {x : Fin n → ℝ} (hx : vandermonde x ≠ 0) (c : ℂ) :
    ‖((|vandermonde x| : ℝ) : ℂ) ^ (2 * c)‖ = |vandermonde x| ^ (2 * c.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hx)]
  simp

/-- The modulus of the integrand of 5.14.6 is the Hermite majorant with exponent `Re c`. -/
theorem norm_hermIntegrand_eq {n : ℕ} {x : Fin n → ℝ} (hx : vandermonde x ≠ 0) (c : ℂ) :
    ‖hermIntegrand n c x‖ = hermBound n c.re x := by
  unfold hermIntegrand hermBound
  rw [norm_mul, norm_vandermonde_cpow hx, norm_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Complex.norm_exp, show (-(x k : ℂ) ^ 2 / 2) = ((-x k ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

/-- On `[-√(2N), √(2N)]`, `0 ≤ (1 - y²/(2N))^N ≤ e^(-y²/2)`. -/
theorem one_sub_div_pow_mem {N : ℕ} {y : ℝ} (hy : y ∈ Icc (-√(2 * N)) √(2 * N)) :
    0 ≤ (1 - y ^ 2 / (2 * N)) ^ N ∧ (1 - y ^ 2 / (2 * N)) ^ N ≤ Real.exp (-y ^ 2 / 2) := by
  have hsq : y ^ 2 ≤ 2 * N := by
    have h := sq_le_sq' hy.1 hy.2
    rwa [Real.sq_sqrt (by positivity)] at h
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : y ^ 2 = 0 := by simp at hsq; nlinarith [sq_nonneg y]
    simp [this]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 ≤ 1 - y ^ 2 / (2 * N) := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact hsq
  refine ⟨pow_nonneg hq N, ?_⟩
  have hx2 : y ^ 2 / 2 ≤ N := by linarith
  have := Real.one_sub_div_pow_le_exp_neg (n := N) hx2
  rw [show y ^ 2 / 2 / N = y ^ 2 / (2 * N) by ring] at this
  calc (1 - y ^ 2 / (2 * N)) ^ N ≤ Real.exp (-(y ^ 2 / 2)) := this
    _ = Real.exp (-y ^ 2 / 2) := by ring_nf

/-- Domination of the Hermite approximant by the Hermite majorant on the box. -/
theorem norm_hermApprox_le_hermBound {n : ℕ} (c : ℂ) {N : ℕ} {x : Fin n → ℝ}
    (hv : vandermonde x ≠ 0) (hx : ∀ i, x i ∈ Icc (-√(2 * N)) √(2 * N)) :
    ‖hermApprox n c N x‖ ≤ hermBound n c.re x := by
  unfold hermApprox hermBound
  rw [norm_mul, norm_vandermonde_cpow hv, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  obtain ⟨h0, h1⟩ := one_sub_div_pow_mem (hx i)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

/-- The real form of the approximating integrand for a real exponent. -/
def hermApproxR (n : ℕ) (σ : ℝ) (N : ℕ) (x : Fin n → ℝ) : ℝ :=
  |vandermonde x| ^ (2 * σ) * ∏ k : Fin n, (1 - x k ^ 2 / (2 * N)) ^ N

/-- For real exponent, the Hermite approximant is the cast of its real form. -/
theorem hermApprox_ofReal (n : ℕ) (σ : ℝ) (N : ℕ) (x : Fin n → ℝ) :
    hermApprox n σ N x = (hermApproxR n σ N x : ℂ) := by
  unfold hermApprox hermApproxR
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (abs_nonneg _), Complex.ofReal_prod]
  push_cast
  rfl

/-- The box `[-√(2N), √(2N)]ⁿ`. -/
abbrev hermBox (n N : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Icc (-√(2 * (N : ℝ))) √(2 * N))

/-- Every point eventually lies in the box `[-√(2N), √(2N)]ⁿ`. -/
theorem eventually_mem_hermBox {n : ℕ} (x : Fin n → ℝ) : ∀ᶠ N : ℕ in atTop, x ∈ hermBox n N := by
  have hs : Tendsto (fun N : ℕ => √(2 * (N : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
  have : ∀ i, ∀ᶠ N : ℕ in atTop, |x i| ≤ √(2 * (N : ℝ)) := fun i =>
    hs.eventually_ge_atTop |x i|
  filter_upwards [Filter.eventually_all.2 this] with N hN i _
  exact abs_le.mp (hN i)

/-- The right-hand side of 5.14.6 (without normalization) is nonzero for `Re c > -1/n`. -/
theorem herm_rhs_ne_zero {n : ℕ} (hn : 0 < n) {σ : ℝ} (hσ : (-1 / n : ℝ) < σ) :
    ∏ j : Fin n, (((√(2 * π) : ℝ) : ℂ) *
      (Gamma (1 + (((j : ℕ) : ℂ) + 1) * σ) / Gamma (1 + σ))) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun j _ => mul_ne_zero ?_ (div_ne_zero ?_ ?_)
  · exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * π)).ne'
  · refine Complex.Gamma_ne_zero_of_re_pos ?_
    have := one_add_mul_pos hn hσ (k := (j : ℕ) + 1) j.isLt
    simpa using this
  · refine Complex.Gamma_ne_zero_of_re_pos ?_
    have := one_add_mul_pos hn hσ (k := 1) hn
    simpa using this

/-- Integrability of `e^{-|x|²/2} |Δ(x)|^{2σ}` for `σ > -1/n`, by Fatou's lemma applied to the
Selberg approximations. -/
theorem integrable_hermBound {n : ℕ} (hn : 0 < n) {σ : ℝ} (hσ : (-1 / n : ℝ) < σ) :
    Integrable (hermBound n σ) := by
  have hσc : (-1 / n : ℝ) < (σ : ℂ).re := by simpa using hσ
  have hval := (tendsto_herm_rhs hn (σ : ℂ)).congr' (by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (integral_hermApprox_eq (mem_cDomain_herm hn hσc N) hN).symm)
  set L := ∏ j : Fin n, (((√(2 * π) : ℝ) : ℂ) *
      (Gamma (1 + (((j : ℕ) : ℂ) + 1) * σ) / Gamma (1 + σ))) with hL
  have hne : ∀ᶠ N in atTop, ∫ x in hermBox n N, hermApprox n σ N x ≠ 0 :=
    hval.eventually_ne (herm_rhs_ne_zero hn hσ)
  set g : ℕ → (Fin n → ℝ) → ℝ := fun N => (hermBox n N).indicator (hermApproxR n σ N) with hg
  have hbox : ∀ N, MeasurableSet (hermBox n N) := fun N =>
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hR_nonneg : ∀ N, ∀ x ∈ hermBox n N, 0 ≤ hermApproxR n σ N x := fun N x hx => by
    unfold hermApproxR
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ =>
      (one_sub_div_pow_mem (hx i (Set.mem_univ _))).1)
  have hg_nonneg : ∀ N x, 0 ≤ g N x := fun N x => by
    simp only [hg]
    by_cases hx : x ∈ hermBox n N
    · rw [Set.indicator_of_mem hx]; exact hR_nonneg N x hx
    · rw [Set.indicator_of_notMem hx]
  have hg_meas : ∀ N, Measurable (g N) := fun N => by
    refine Measurable.indicator ?_ (hbox N)
    unfold hermApproxR vandermonde
    fun_prop
  -- integrability and the value of `∫ g N`
  have hgval : ∀ᶠ N in atTop, Integrable (g N) ∧
      ∫ x, g N x = ‖∫ x in hermBox n N, hermApprox n σ N x‖ := by
    filter_upwards [hne] with N hN
    have hI : IntegrableOn (hermApprox n σ N) (hermBox n N) := Integrable.of_integral_ne_zero hN
    have hIR : IntegrableOn (hermApproxR n σ N) (hermBox n N) := by
      have hfun : hermApprox n σ N = fun x => (hermApproxR n σ N x : ℂ) :=
        funext (hermApprox_ofReal n σ N)
      have : IntegrableOn (fun x => (hermApproxR n σ N x : ℂ)) (hermBox n N) := by
        rw [← hfun]; exact hI
      exact this.re
    refine ⟨(integrable_indicator_iff (hbox N)).2 hIR, ?_⟩
    simp only [hg]
    rw [integral_indicator (hbox N)]
    simp_rw [hermApprox_ofReal]
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (setIntegral_nonneg (hbox N) (hR_nonneg N))]
  -- pointwise convergence
  have hlim : ∀ᵐ x, Tendsto (fun N => g N x) atTop (𝓝 (hermBound n σ x)) := by
    filter_upwards [ae_vandermonde_ne_zero n] with x hv
    have h := (tendsto_hermApprox (σ : ℂ) x).norm
    rw [norm_hermIntegrand_eq hv, Complex.ofReal_re] at h
    refine h.congr' ?_
    filter_upwards [eventually_mem_hermBox x] with N hN
    simp only [hg]
    rw [Set.indicator_of_mem hN, hermApprox_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hR_nonneg N x hN)]
  -- Fatou
  have hfatou := lintegral_liminf_le' (μ := (volume : Measure (Fin n → ℝ)))
    (f := fun N x => ENNReal.ofReal (g N x)) (u := atTop)
    (fun N => (hg_meas N).ennreal_ofReal.aemeasurable)
  have hleft : ∫⁻ x, ENNReal.ofReal (hermBound n σ x) =
      ∫⁻ x, liminf (fun N => ENNReal.ofReal (g N x)) atTop := by
    refine lintegral_congr_ae ?_
    filter_upwards [hlim] with x hx
    exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
  have hright : liminf (fun N => ∫⁻ x, ENNReal.ofReal (g N x)) atTop = ENNReal.ofReal ‖L‖ := by
    refine Tendsto.liminf_eq ?_
    have h := (ENNReal.continuous_ofReal.tendsto _).comp hval.norm
    refine h.congr' ?_
    filter_upwards [hgval] with N hN
    rw [Function.comp_apply, ← hN.2, ofReal_integral_eq_lintegral_ofReal hN.1
      (Eventually.of_forall (hg_nonneg N))]
  refine ⟨(measurable_hermBound n σ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (hermBound_nonneg n σ)), hleft]
  exact lt_of_le_of_lt (hfatou.trans hright.le) ENNReal.ofReal_lt_top

/-- Convergence of the box integrals on the full domain `Re c > -1/n`. -/
theorem tendsto_integral_hermApprox {n : ℕ} (hn : 0 < n) {c : ℂ} (hc : (-1 / n : ℝ) < c.re) :
    Tendsto (fun N : ℕ => ∫ x in hermBox n N, hermApprox n c N x) atTop
      (𝓝 (∫ x, hermIntegrand n c x)) := by
  simp_rw [← integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Icc)]
  refine tendsto_integral_filter_of_dominated_convergence (hermBound n c.re)
    (Eventually.of_forall fun N => ((measurable_hermApprox n c N).indicator
      (MeasurableSet.univ_pi fun _ => measurableSet_Icc)).aestronglyMeasurable)
    (Eventually.of_forall fun N => ?_) (integrable_hermBound hn hc) ?_
  · filter_upwards [ae_vandermonde_ne_zero n] with x hv
    by_cases hx : x ∈ hermBox n N
    · rw [Set.indicator_of_mem hx]
      exact norm_hermApprox_le_hermBound c hv fun i => hx i (Set.mem_univ _)
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact hermBound_nonneg n c.re x
  · refine Eventually.of_forall fun x => (tendsto_hermApprox c x).congr' ?_
    filter_upwards [eventually_mem_hermBox x] with N hN
    rw [Set.indicator_of_mem hN]

/-- Mehta's integral on the full domain `Re c > -1/n`, as a limit of Selberg's integral. -/
theorem integral_hermIntegrand {n : ℕ} (hn : 0 < n) {c : ℂ} (hc : (-1 / n : ℝ) < c.re) :
    ∫ x, hermIntegrand n c x =
      ∏ j : Fin n, (((√(2 * π) : ℝ) : ℂ) *
        (Gamma (1 + (((j : ℕ) : ℂ) + 1) * c) / Gamma (1 + c))) := by
  have hrhs := (tendsto_herm_rhs hn c).congr' (by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (integral_hermApprox_eq (mem_cDomain_herm hn hc N) hN).symm)
  exact tendsto_nhds_unique (tendsto_integral_hermApprox hn hc) hrhs

/-- `(√(2π))ⁿ = (2π)^(n/2)`. -/
theorem sqrt_two_pi_pow (n : ℕ) :
    ((√(2 * π) : ℝ) : ℂ) ^ n = (2 * π : ℂ) ^ (n / 2 : ℂ) := by
  rw [show (n / 2 : ℂ) = (n : ℂ) * (1 / 2 : ℝ) by push_cast; ring, Complex.cpow_nat_mul,
    show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), Real.sqrt_eq_rpow]

/-- Hermite form of the Selberg integral (Mehta's integral), DLMF 5.14.6: the Gaussian integral of
`|Δ(t)|^(2c)` over `ℝⁿ`, divided by `(2π)^(n/2)`, is `∏ Γ(1 + (k+1)c) / Γ(1 + c)ⁿ`. -/
@[dlmf 5.14.E6]
theorem selberg_hermite {n : ℕ} {c : ℂ} (hc : (-1 / n : ℝ) < c.re) :
    (1 / (2 * π : ℂ) ^ (n / 2 : ℂ)) *
        ∫ t : Fin n → ℝ,
          ((|vandermonde t| : ℝ) : ℂ) ^ (2 * c) *
            ∏ k : Fin n, Complex.exp (-(t k : ℂ) ^ 2 / 2) =
      (∏ k : Fin n, Complex.Gamma (1 + ((k : ℕ) + 1) * c)) /
        Complex.Gamma (1 + c) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [vandermonde, Measure.real, volume_pi]
  change (1 / (2 * π : ℂ) ^ (n / 2 : ℂ)) * ∫ t, hermIntegrand n c t = _
  rw [integral_hermIntegrand hn hc, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, sqrt_two_pi_pow, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h0 : (2 * π : ℂ) ^ (n / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => by simp [Real.pi_ne_zero] at h
  rw [← mul_assoc, one_div, inv_mul_cancel₀ h0, one_mul]

end HermiteLimit

end DLMF.Gamma
end
end
