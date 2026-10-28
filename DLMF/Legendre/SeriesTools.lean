/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Integer
public import DLMF.Legendre.Laplace

/-!
# Tools for Legendre generating functions and the polynomials `W_{n-1}`

* `legSer_legendreP_nat`: the terminating hypergeometric function `P_n(z)` equals the Legendre
  polynomial for every `z ∈ ℂ`, including the cut `(-∞,-1]` of the continuation. The proof shows
  that the continuation recursion at `a = -n` produces a polynomial function of `z`
  (`legSer_aux_poly`) and uses the identity principle for polynomials.
* Formal power series in `ℂ⟦X⟧`: `G = ∑ P_n(z) Xⁿ` satisfies `(1-2zX+X²) G' = (z-X) G`, hence
  `(1-2zX+X²) G² = 1` (`legSer_Q_G_sq`); with the primitive `F` of `G`, the coefficients of `FG`
  obey the recurrence of `W_{n-1}` (`legSer_U_eq`, DLMF 14.7.4).
* `legSer_B_mul`: `G` is the product of the binomial series of `(1-ζ₁X)^{-1/2}` and
  `(1-ζ₂X)^{-1/2}` when `ζ₁+ζ₂ = 2z`, `ζ₁ζ₂ = 1`; this gives the generating function
  (DLMF 14.7.19) for complex `z` by a Cauchy product (`legSer_generating`).

All helper names carry the prefix `legSer_`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric
open scoped Real Topology Nat PowerSeries
namespace DLMF.Legendre


/-- The Euler integral with `a = -m` is a polynomial function of `z` on all of `ℂ`. -/
theorem legSer_integral_poly (m : ℕ) {b c : ℂ} (hb : 0 < b.re) (hcb : 0 < (c-b).re) :
    ∃ p : Polynomial ℂ, ∀ z, regularizedGaussHGIntegral (-(m:ℂ)) b c z = p.eval z := by
  set g : ℝ → ℂ := fun t => (t:ℂ)^(b-1) * (1-(t:ℂ))^(c-b-1) with hg
  have hgI : IntervalIntegrable g volume 0 1 := betaIntegral_convergent hb hcb
  set w : ℕ → ℂ := fun i => (Gamma b * Gamma (c-b))⁻¹ *
    ((-1)^i * (m.choose i : ℂ) * ∫ t in (0:ℝ)..1, g t * (t:ℂ)^i) with hw
  refine ⟨∑ i ∈ Finset.range (m+1), Polynomial.C (w i) * Polynomial.X^i, fun z => ?_⟩
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  have hexp : ∀ t : ℝ, eulerKernel (-(m:ℂ)) b c z t =
      ∑ i ∈ Finset.range (m+1), z^i * ((-1)^i * (m.choose i : ℂ) * (g t * (t:ℂ)^i)) := by
    intro t
    simp only [eulerKernel, neg_neg, cpow_natCast, hg]
    rw [show (1:ℂ) - z*t = -(z*t) + 1 by ring, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [neg_pow, mul_pow, one_pow, mul_one]; ring
  unfold regularizedGaussHGIntegral
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum (fun i _ => by
    refine IntervalIntegrable.const_mul ?_ _
    refine IntervalIntegrable.const_mul ?_ _
    exact hgI.mul_continuousOn (by fun_prop)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [hw]; ring

/-- With `Re b ≥ 1`, the continuation recursion at `a = -m` is a polynomial function of `z`. -/
lemma legSer_aux_poly (k : ℕ) : ∀ (m : ℕ) (b c : ℂ), shiftB b = 0 → shiftC b c ≤ k →
    ∃ p : Polynomial ℂ, ∀ z, regularizedGaussHGAux k (-(m:ℂ)) b c z = p.eval z := by
  induction k with
  | zero =>
    intro m b c hB hC
    obtain ⟨h1, h2⟩ := euler_region_of_shift_eq_zero hB (Nat.le_zero.mp hC)
    obtain ⟨p, hp⟩ := legSer_integral_poly m (b := b) (c := c) (by linarith) (by linarith)
    exact ⟨p, fun z => by rw [regularizedGaussHGAux]; exact hp z⟩
  | succ k ih =>
    intro m b c hB hC
    by_cases hc : 0 < shiftC b c
    · have hlt := shiftC_add_one_lt hc
      obtain ⟨p1, hp1⟩ := ih m b (c+1) hB (by omega)
      rcases m with _ | m
      · refine ⟨Polynomial.C (c - 0) * p1, fun z => ?_⟩
        rw [regularizedGaussHGAux_succ_of_pos_c hc, hp1]; simp
      · obtain ⟨p2, hp2⟩ := ih m b (c+1) hB (by omega)
        refine ⟨Polynomial.C (c - -((m+1:ℕ):ℂ)) * p1 + Polynomial.C (-((m+1:ℕ):ℂ)) * p2,
          fun z => ?_⟩
        rw [regularizedGaussHGAux_succ_of_pos_c hc, hp1,
          show -((m+1:ℕ):ℂ) + 1 = -(m:ℂ) by push_cast; ring, hp2]
        simp
    · have hb : ¬ 0 < shiftB b := by omega
      have hC0 : shiftC b c = 0 := by omega
      obtain ⟨h1, h2⟩ := euler_region_of_shift_eq_zero hB hC0
      obtain ⟨p, hp⟩ := legSer_integral_poly m (b := b) (c := c) (by linarith) (by linarith)
      exact ⟨p, fun z => by rw [regularizedGaussHGAux_succ_of_zero hc hb]; exact hp z⟩

/-- `P_n` is a polynomial function on all of `ℂ`. -/
theorem legSer_legendreP_poly (n : ℕ) : ∃ q : Polynomial ℂ, ∀ z, legendreP n z = q.eval z := by
  have hB : shiftB ((n:ℂ)+1) = 0 := by
    unfold shiftB; rw [Nat.ceil_eq_zero]; simp
  obtain ⟨p, hp⟩ := legSer_aux_poly (shiftMeasure ((n:ℂ)+1) 1) n ((n:ℂ)+1) 1 hB
    (by unfold shiftMeasure; omega)
  refine ⟨p.comp (Polynomial.C (1/2) - Polynomial.C (1/2) * Polynomial.X), fun z => ?_⟩
  rw [legendreP, regularizedGaussHG, hp]
  simp only [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X]
  congr 1; ring

/-- The set `{z | 1 + z ∈ slitPlane}` is infinite. -/
theorem legSer_infinite : {z : ℂ | 1 + z ∈ slitPlane}.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => ((n:ℝ):ℂ)) := fun a b h => by
    simpa using h
  refine Set.infinite_of_injective_forall_mem hinj fun n => ?_
  show 1 + ((n:ℝ):ℂ) ∈ slitPlane
  exact Or.inl (by simp; positivity)

/-- Two polynomial functions agreeing on `{1 + z ∈ slitPlane}` agree everywhere. -/
theorem legSer_poly_ext {p q : Polynomial ℂ} (h : ∀ z : ℂ, 1 + z ∈ slitPlane → p.eval z = q.eval z)
    (z : ℂ) : p.eval z = q.eval z := by
  rw [Polynomial.eq_of_infinite_eval_eq p q (legSer_infinite.mono fun w hw => h w hw)]

/-- The three-term recurrence for `P_n(z)` holds for every `z ∈ ℂ`. -/
theorem legSer_legendreP_rec (n : ℕ) (z : ℂ) :
    ((n:ℂ)+2) * legendreP ((n+2:ℕ):ℂ) z =
      (2*n+3) * z * legendreP ((n+1:ℕ):ℂ) z - ((n:ℂ)+1) * legendreP (n:ℂ) z := by
  obtain ⟨q0, h0⟩ := legSer_legendreP_poly n
  obtain ⟨q1, h1⟩ := legSer_legendreP_poly (n+1)
  obtain ⟨q2, h2⟩ := legSer_legendreP_poly (n+2)
  have key := legSer_poly_ext (p := Polynomial.C ((n:ℂ)+2) * q2)
    (q := Polynomial.C (2*(n:ℂ)+3) * Polynomial.X * q1 - Polynomial.C ((n:ℂ)+1) * q0)
    (fun w hw => by
      have e := legendreP_recurrence ((n:ℂ)+1) hw
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
        ← h0, ← h1, ← h2]
      push_cast
      rw [show (n:ℂ)+1+1 = n+2 by ring, show (n:ℂ)+1-1 = n by ring] at e
      linear_combination e) z
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
    ← h0, ← h1, ← h2] at key
  linear_combination key

/-- `P_0(z) = 1` for every `z`. -/
theorem legSer_legendreP_zero (z : ℂ) : legendreP ((0:ℕ):ℂ) z = 1 := by
  obtain ⟨q, h⟩ := legSer_legendreP_poly 0
  have key := legSer_poly_ext (p := q) (q := 1) (fun w hw => by
    rw [← h, legendreP_nat 0 hw]; simp [DLMF.OrthogonalPolynomials.legendrePolyP_zero]) z
  rw [h, key]; simp

/-- `P_1(z) = z` for every `z`. -/
theorem legSer_legendreP_one (z : ℂ) : legendreP ((1:ℕ):ℂ) z = z := by
  obtain ⟨q, h⟩ := legSer_legendreP_poly 1
  have key := legSer_poly_ext (p := q) (q := Polynomial.X) (fun w hw => by
    rw [← h, legendreP_nat 1 hw]; simp [DLMF.OrthogonalPolynomials.legendrePolyP_one]) z
  rw [h, key]; simp

/-- `P_n(z)` equals the Legendre polynomial for every `z ∈ ℂ` (the hypergeometric
representation terminates). -/
theorem legSer_legendreP_nat (n : ℕ) (z : ℂ) :
    legendreP n z = DLMF.OrthogonalPolynomials.legendrePolyP n z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [legSer_legendreP_zero, DLMF.OrthogonalPolynomials.legendrePolyP_zero]
    | 1, _ => rw [legSer_legendreP_one, DLMF.OrthogonalPolynomials.legendrePolyP_one]
    | n+2, ih =>
      have e1 := legSer_legendreP_rec n z
      have e2 := DLMF.OrthogonalPolynomials.legendrePolyP_recurrence n z
      rw [ih n (by omega), ih (n+1) (by omega)] at e1
      have hn : (n:ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+1)
      exact mul_left_cancel₀ hn (e1.trans e2.symm)


/-- The quadratic `1 - 2zX + X²` as a power series. -/
noncomputable def legSerQ (z : ℂ) : ℂ⟦X⟧ :=
  1 - PowerSeries.C (2*z) * PowerSeries.X + PowerSeries.X^2

/-- The linear factor `z - X` as a power series. -/
noncomputable def legSerL (z : ℂ) : ℂ⟦X⟧ := PowerSeries.C z - PowerSeries.X

/-- Multiplication by `legSerQ z = 1 - 2zX + X²` expands as `S - 2z·X S + X·X S`. -/
theorem legSer_Q_eq (z : ℂ) (S : ℂ⟦X⟧) : legSerQ z * S =
    S - PowerSeries.C (2*z) * (PowerSeries.X * S) + PowerSeries.X * (PowerSeries.X * S) := by
  unfold legSerQ; ring

/-- The constant coefficient of `(1 - 2zX + X²) S` equals that of `S`. -/
theorem legSer_coeff_Q_zero (z : ℂ) (S : ℂ⟦X⟧) :
    PowerSeries.coeff 0 (legSerQ z * S) = PowerSeries.coeff 0 S := by
  rw [legSer_Q_eq]; simp

/-- The coefficient of `X` in `(1 - 2zX + X²) S` is `s₁ - 2z s₀`. -/
theorem legSer_coeff_Q_one (z : ℂ) (S : ℂ⟦X⟧) :
    PowerSeries.coeff 1 (legSerQ z * S) = PowerSeries.coeff 1 S - 2*z*PowerSeries.coeff 0 S := by
  rw [legSer_Q_eq, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_succ_X_mul]
  simp

/-- The coefficient of `X^(n+2)` in `(1 - 2zX + X²) S` is `s_{n+2} - 2z s_{n+1} + s_n`. -/
theorem legSer_coeff_Q_add_two (z : ℂ) (S : ℂ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff (n+2) (legSerQ z * S) = PowerSeries.coeff (n+2) S -
      2*z*PowerSeries.coeff (n+1) S + PowerSeries.coeff n S := by
  rw [legSer_Q_eq, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]

/-- The constant coefficient of `(z - X) S` is `z s₀`. -/
theorem legSer_coeff_L_zero (z : ℂ) (S : ℂ⟦X⟧) :
    PowerSeries.coeff 0 (legSerL z * S) = z * PowerSeries.coeff 0 S := by
  unfold legSerL; rw [sub_mul, map_sub, PowerSeries.coeff_C_mul]; simp

/-- The coefficient of `X^(n+1)` in `(z - X) S` is `z s_{n+1} - s_n`. -/
theorem legSer_coeff_L_succ (z : ℂ) (S : ℂ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff (n+1) (legSerL z * S) = z * PowerSeries.coeff (n+1) S -
      PowerSeries.coeff n S := by
  unfold legSerL; rw [sub_mul, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]

/-- The sequence `n ↦ P_n(z)`. -/
noncomputable def legSerP (z : ℂ) (n : ℕ) : ℂ := legendreP (n:ℂ) z

/-- `P_0(z) = 1`. -/
theorem legSerP_zero (z : ℂ) : legSerP z 0 = 1 := legSer_legendreP_zero z
/-- `P_1(z) = z`. -/
theorem legSerP_one (z : ℂ) : legSerP z 1 = z := legSer_legendreP_one z
/-- Bonnet's recurrence `(n+2) P_{n+2}(z) = (2n+3) z P_{n+1}(z) - (n+1) P_n(z)`. -/
theorem legSerP_rec (z : ℂ) (n : ℕ) :
    ((n:ℂ)+2) * legSerP z (n+2) = (2*n+3) * z * legSerP z (n+1) - ((n:ℂ)+1) * legSerP z n :=
  legSer_legendreP_rec n z

/-- The generating series `∑ P_n(z) Xⁿ`. -/
noncomputable def legSerG (z : ℂ) : ℂ⟦X⟧ := PowerSeries.mk (legSerP z)

/-- Its primitive `∑ P_{n-1}(z) Xⁿ / n`. -/
noncomputable def legSerF (z : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else legSerP z (n-1) / n

/-- The `k`-th coefficient of the formal derivative of `∑ P_n(z) Xⁿ` is `(k+1) P_{k+1}(z)`. -/
theorem legSer_coeff_dG (z : ℂ) (k : ℕ) :
    PowerSeries.coeff k (d⁄dX (legSerG z)) = legSerP z (k+1) * (k+1) := by
  rw [PowerSeries.coeff_derivative, legSerG, PowerSeries.coeff_mk]

/-- `(1 - 2zX + X²) G' = (z - X) G`. -/
theorem legSer_G_ode (z : ℂ) : legSerQ z * d⁄dX (legSerG z) = legSerL z * legSerG z := by
  ext n
  rcases n with _ | _ | n
  · rw [legSer_coeff_Q_zero, legSer_coeff_L_zero, legSer_coeff_dG]
    simp only [legSerG, PowerSeries.coeff_mk, zero_add, legSerP_one, legSerP_zero]; ring
  · rw [legSer_coeff_Q_one, legSer_coeff_L_succ, legSer_coeff_dG, legSer_coeff_dG]
    simp only [legSerG, PowerSeries.coeff_mk]
    have e := legSerP_rec z 0
    simp only [legSerP_one, legSerP_zero, zero_add] at e ⊢
    push_cast at e ⊢
    linear_combination e
  · rw [legSer_coeff_Q_add_two, legSer_coeff_L_succ, legSer_coeff_dG, legSer_coeff_dG,
      legSer_coeff_dG]
    simp only [legSerG, PowerSeries.coeff_mk]
    have e := legSerP_rec z (n+1)
    push_cast at e ⊢
    linear_combination e

/-- The formal derivative of `1 - 2zX + X²` is `-2z + 2X`. -/
theorem legSer_dQ (z : ℂ) : d⁄dX (legSerQ z) = -PowerSeries.C (2*z) + 2 * PowerSeries.X := by
  unfold legSerQ
  rw [map_add, map_sub, Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_C,
    PowerSeries.derivative_X, PowerSeries.derivative_one]
  simp only [smul_eq_mul, mul_zero, mul_one, add_zero, zero_sub]
  push_cast; ring_nf

/-- `(1 - 2zX + X²) G² = 1`. -/
theorem legSer_Q_G_sq (z : ℂ) : legSerQ z * legSerG z ^ 2 = 1 := by
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_one, legSer_dQ]
    simp only [smul_eq_mul]
    have h := legSer_G_ode z
    have : legSerQ z * (((2:ℕ):ℂ⟦X⟧) * legSerG z ^ (2-1) * d⁄dX (legSerG z)) =
        2 * legSerG z * (legSerL z * legSerG z) := by
      rw [← h]; push_cast; ring
    rw [this]; unfold legSerL; simp only [map_mul, map_ofNat]; ring
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      legSer_coeff_Q_zero, pow_two, PowerSeries.coeff_mul]
    simp [legSerG, legSerP_zero]

/-- The formal derivative of `legSerF z = ∑ P_{n-1}(z) Xⁿ/n` is the generating series `legSerG z = ∑
P_n(z) Xⁿ`. -/
theorem legSer_dF (z : ℂ) : d⁄dX (legSerF z) = legSerG z := by
  ext k
  rw [PowerSeries.coeff_derivative, legSerF, PowerSeries.coeff_mk, legSerG, PowerSeries.coeff_mk]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  have : ((k+1:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  push_cast at this ⊢
  field_simp

/-- `(1 - 2zX + X²) (FG)' = 1 + (z - X) FG`. -/
theorem legSer_U_ode (z : ℂ) : legSerQ z * d⁄dX (legSerF z * legSerG z) =
    1 + legSerL z * (legSerF z * legSerG z) := by
  rw [Derivation.leibniz, legSer_dF]
  simp only [smul_eq_mul]
  rw [← legSer_Q_G_sq z, mul_add, show legSerQ z * (legSerF z * d⁄dX (legSerG z)) =
    legSerF z * (legSerQ z * d⁄dX (legSerG z)) by ring, legSer_G_ode]
  ring

/-- The coefficients of `F G` are the convolution sums of DLMF 14.7.4. -/
theorem legSer_coeff_U (z : ℂ) (n : ℕ) : PowerSeries.coeff n (legSerF z * legSerG z) =
    ∑ j ∈ Finset.range n, legSerP z j * legSerP z (n-j-1) / (j+1:ℂ) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ']
  simp only [legSerF, legSerG, PowerSeries.coeff_mk, ↓reduceIte, zero_mul, add_zero,
    Nat.add_one_ne_zero, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [show n - (j+1) = n - j - 1 by omega]
  push_cast; ring

/-- The convolution sums satisfy the recurrence of the polynomials `W_{n-1}`. -/
theorem legSer_U_rec (z : ℂ) (n : ℕ) :
    ((n:ℂ)+2) * PowerSeries.coeff (n+2) (legSerF z * legSerG z) =
      (2*n+3) * z * PowerSeries.coeff (n+1) (legSerF z * legSerG z) -
        ((n:ℂ)+1) * PowerSeries.coeff n (legSerF z * legSerG z) := by
  have h := congrArg (PowerSeries.coeff (n+1)) (legSer_U_ode z)
  set U := legSerF z * legSerG z
  rcases n with _ | n
  · rw [legSer_coeff_Q_one, map_add, legSer_coeff_L_succ, PowerSeries.coeff_derivative,
      PowerSeries.coeff_derivative] at h
    simp only [PowerSeries.coeff_one] at h
    push_cast at h ⊢
    linear_combination h
  · rw [legSer_coeff_Q_add_two, map_add, legSer_coeff_L_succ, PowerSeries.coeff_derivative,
      PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at h
    simp only [PowerSeries.coeff_one] at h
    push_cast at h ⊢
    linear_combination h

/-- The constant coefficient of `legSerF z * legSerG z` is `0`. -/
theorem legSer_U_zero (z : ℂ) : PowerSeries.coeff 0 (legSerF z * legSerG z) = 0 := by
  rw [legSer_coeff_U]; simp

/-- The coefficient of `X` in `legSerF z * legSerG z` is `1`. -/
theorem legSer_U_one (z : ℂ) : PowerSeries.coeff 1 (legSerF z * legSerG z) = 1 := by
  rw [legSer_coeff_U]; simp [legSerP_zero]

/-- The `n`-th coefficient of `legSerF z * legSerG z` equals `R_n(z) = (legendreQPoly n).eval z`,
the polynomial with `Q_n = P_n Q_0 - R_n`. -/
theorem legSer_U_eq (z : ℂ) (n : ℕ) :
    PowerSeries.coeff n (legSerF z * legSerG z) = (legendreQPoly n).eval z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [legSer_U_zero]; simp [legendreQPoly]
    | 1, _ => rw [legSer_U_one]; simp [legendreQPoly]
    | n+2, ih =>
      have e := legSer_U_rec z n
      rw [ih n (by omega), ih (n+1) (by omega)] at e
      have hn : (n:ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+1)
      rw [legendreQPoly]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
      rw [eq_inv_mul_iff_mul_eq₀ hn, e]


/-- The formal binomial series of `(1 - ζX)^{-1/2}`. -/
noncomputable def legSerB (ζ : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun j => poch (1/2) j * ζ^j / (j.factorial : ℂ)

/-- The binomial series `B = legSerB ζ` of `(1 - ζX)^{-1/2}` satisfies `(1 - ζX) B' = (ζ/2) B`. -/
theorem legSer_B_ode (ζ : ℂ) :
    (1 - PowerSeries.C ζ * PowerSeries.X) * d⁄dX (legSerB ζ) = PowerSeries.C (ζ/2) * legSerB ζ := by
  ext n
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_derivative]
  rcases n with _ | n
  · simp [legSerB, PowerSeries.coeff_mk, poch_succ, poch_zero]; ring
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    simp only [legSerB, PowerSeries.coeff_mk]
    rw [poch_succ (1/2) (n+1), poch_succ (1/2) n, Nat.factorial_succ (n+1), Nat.factorial_succ n]
    have h1 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have h2 : (n:ℂ) + 1 + 1 ≠ 0 := by
      have : ((n + 1 + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at this; exact this
    have h3 : (n:ℂ) + 1 ≠ 0 := by
      have : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at this; exact this
    push_cast
    field_simp
    ring

/-- `(1 - ζX) B(ζ)² = 1`. -/
theorem legSer_B_sq (ζ : ℂ) : (1 - PowerSeries.C ζ * PowerSeries.X) * legSerB ζ ^ 2 = 1 := by
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_one, map_sub,
      Derivation.leibniz, PowerSeries.derivative_one, PowerSeries.derivative_C, PowerSeries.derivative_X]
    simp only [smul_eq_mul]
    have h := legSer_B_ode ζ
    have : (1 - PowerSeries.C ζ * PowerSeries.X) * (((2:ℕ):ℂ⟦X⟧) * legSerB ζ ^ (2-1) *
        d⁄dX (legSerB ζ)) = 2 * legSerB ζ * (PowerSeries.C (ζ/2) * legSerB ζ) := by
      rw [← h]; push_cast; ring
    rw [this, show PowerSeries.C (ζ/2) = PowerSeries.C ζ * PowerSeries.C (1/2) by
      rw [← map_mul]; ring_nf]
    have h2 : (2:ℂ⟦X⟧) * PowerSeries.C (1/2) = 1 := by
      rw [← map_ofNat PowerSeries.C 2, ← map_mul]; norm_num
    linear_combination (PowerSeries.C ζ * legSerB ζ ^ 2) * h2
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul,
      pow_two, PowerSeries.coeff_mul]
    simp [legSerB, poch_zero]

/-- Square roots of a power series with the same nonzero constant term coincide. -/
theorem legSer_sq_inj {A B : ℂ⟦X⟧} (h : A^2 = B^2)
    (h0 : PowerSeries.constantCoeff A = PowerSeries.constantCoeff B)
    (h1 : PowerSeries.constantCoeff A ≠ 0) : A = B := by
  have hfac : (A - B) * (A + B) = 0 := by linear_combination h
  have hne : A + B ≠ 0 := by
    intro hab
    have := congrArg PowerSeries.constantCoeff hab
    rw [map_add, ← h0, map_zero] at this
    exact h1 (by linear_combination this/2)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hne)

/-- `B(ζ₁) B(ζ₂) = ∑ P_n(z) Xⁿ` when `ζ₁ + ζ₂ = 2z` and `ζ₁ ζ₂ = 1`. -/
theorem legSer_B_mul (z ζ₁ ζ₂ : ℂ) (hs : ζ₁ + ζ₂ = 2*z) (hp : ζ₁ * ζ₂ = 1) :
    legSerB ζ₁ * legSerB ζ₂ = legSerG z := by
  have hQ : legSerQ z = (1 - PowerSeries.C ζ₁ * PowerSeries.X) * (1 - PowerSeries.C ζ₂ * PowerSeries.X) := by
    unfold legSerQ
    rw [show (2:ℂ)*z = ζ₁ + ζ₂ by rw [hs], map_add]
    have : PowerSeries.C ζ₁ * PowerSeries.C ζ₂ = (1:ℂ⟦X⟧) := by rw [← map_mul, hp, map_one]
    linear_combination -(PowerSeries.X^2 : ℂ⟦X⟧) * this
  have hQ0 : legSerQ z ≠ 0 := by
    intro h0
    have := congrArg PowerSeries.constantCoeff h0
    simp [legSerQ] at this
  refine legSer_sq_inj ?_ ?_ ?_
  · refine mul_left_cancel₀ hQ0 ?_
    rw [legSer_Q_G_sq, hQ]
    linear_combination (legSer_B_sq ζ₂) * ((1 - PowerSeries.C ζ₁ * PowerSeries.X) * legSerB ζ₁ ^ 2) +
      legSer_B_sq ζ₁
  · rw [map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [legSerB, legSerG, poch_zero, legSerP_zero]
  · rw [map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [legSerB, poch_zero]


/-- `‖(1/2)_n‖ ≤ n!`. -/
theorem legSer_norm_poch_le (n : ℕ) : ‖poch (1/2:ℂ) n‖ ≤ n.factorial := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_succ, norm_mul, Nat.factorial_succ, Nat.cast_mul]
    have h : ‖(1/2:ℂ) + n‖ ≤ n + 1 := by
      calc ‖(1/2:ℂ) + n‖ ≤ ‖(1/2:ℂ)‖ + ‖(n:ℂ)‖ := norm_add_le _ _
        _ ≤ n + 1 := by simp; linarith
    calc ‖poch (1/2:ℂ) n‖ * ‖(1/2:ℂ) + n‖ ≤ n.factorial * (n + 1) :=
          mul_le_mul ih h (norm_nonneg _) (by positivity)
      _ = _ := by push_cast; ring

/-- The `j`-th term of the binomial series satisfies `‖b_j h^j‖ ≤ ‖hζ‖^j`. -/
theorem legSer_norm_coeff_B_le (ζ h : ℂ) (j : ℕ) :
    ‖PowerSeries.coeff j (legSerB ζ) * h^j‖ ≤ ‖h*ζ‖^j := by
  simp only [legSerB, PowerSeries.coeff_mk]
  have hf : (0:ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
  rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, norm_mul, mul_pow]
  calc ‖poch (1/2:ℂ) j‖ * ‖ζ‖^j / j.factorial * ‖h‖^j ≤ j.factorial * ‖ζ‖^j / j.factorial * ‖h‖^j := by
        gcongr; exact legSer_norm_poch_le j
    _ = ‖h‖^j * ‖ζ‖^j := by field_simp

/-- For `‖hζ‖ < 1`, the binomial series `∑ b_j h^j` of `legSerB ζ` converges absolutely. -/
theorem legSer_summable_B (ζ h : ℂ) (hl : ‖h*ζ‖ < 1) :
    Summable fun j => ‖PowerSeries.coeff j (legSerB ζ) * h^j‖ :=
  (summable_geometric_of_lt_one (norm_nonneg _) hl).of_nonneg_of_le (fun _ => norm_nonneg _)
    (legSer_norm_coeff_B_le ζ h)

/-- For `‖hζ‖ < 1`, the binomial series `∑ b_j h^j` of `legSerB ζ` sums to `(1 - hζ)^{-1/2}`
(principal branch). -/
theorem legSer_hasSum_B (ζ h : ℂ) (hl : ‖h*ζ‖ < 1) :
    HasSum (fun j => PowerSeries.coeff j (legSerB ζ) * h^j) ((1 - h*ζ)^(-1/2:ℂ)) := by
  have ht : ‖-(h*ζ)‖ < 1 := by rwa [norm_neg]
  have e := hasSum_one_add_cpow (-1/2:ℂ) ht
  rw [show (1:ℂ) + -(h*ζ) = 1 - h*ζ by ring, show -(-1/2:ℂ) = 1/2 by ring] at e
  refine e.congr_fun fun j => ?_
  simp only [legSerB, PowerSeries.coeff_mk, neg_neg]
  ring

/-- Generating function of `P_n(z)` in the product form. -/
theorem legSer_generating (z ζ₁ ζ₂ h : ℂ) (hs : ζ₁ + ζ₂ = 2*z) (hp : ζ₁ * ζ₂ = 1)
    (h1 : ‖h*ζ₁‖ < 1) (h2 : ‖h*ζ₂‖ < 1) :
    HasSum (fun n => legSerP z n * h^n) ((1 - 2*z*h + h^2)^(-1/2:ℂ)) := by
  have hB1 := legSer_hasSum_B ζ₁ h h1
  have hB2 := legSer_hasSum_B ζ₂ h h2
  have hs1 := legSer_summable_B ζ₁ h h1
  have hs2 := legSer_summable_B ζ₂ h h2
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs1 hs2
  rw [hB1.tsum_eq, hB2.tsum_eq] at hprod
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hs1 hs2).of_norm
  have hre : ∀ ζ : ℂ, ‖h*ζ‖ < 1 → 0 < (1 - h*ζ).re := fun ζ hl => by
    have := Complex.re_le_norm (h*ζ)
    simp only [sub_re, one_re]; linarith
  rw [show (1:ℂ) - 2*z*h + h^2 = (1 - h*ζ₁) * (1 - h*ζ₂) by
      rw [show 2*z = ζ₁ + ζ₂ from hs.symm]; linear_combination -h^2 * hp,
    ← DLMF.Hypergeometric.cpow_mul_cpow_of_re_pos (hre ζ₁ h1) (hre ζ₂ h2), hprod]
  refine (hsum.hasSum).congr_fun fun n => ?_
  rw [show legSerP z n = PowerSeries.coeff n (legSerG z) by simp [legSerG],
    ← legSer_B_mul z ζ₁ ζ₂ hs hp, PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; ring


/-- The two roots `z ± √(z²-1)` of `ζ² - 2zζ + 1`, with the exterior square root. -/
theorem legSer_roots {z : ℂ} (hz : z-1 ∈ slitPlane) :
    let s := exp ((log (z-1)+log (z+1))/2)
    (z + s) + (z - s) = 2*z ∧ (z + s) * (z - s) = 1 := by
  intro s
  have hm0 := slitPlane_ne_zero hz
  have hp0 := slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hz)
  have hp0' : z + 1 ≠ 0 := by rwa [add_comm]
  have hs2 : s^2 = (z-1)*(z+1) := by
    simp only [s]
    rw [← Complex.exp_nat_mul, show ((2:ℕ):ℂ) * ((log (z-1)+log (z+1))/2) = log (z-1) + log (z+1) by
      push_cast; ring, Complex.exp_add, Complex.exp_log hm0, Complex.exp_log hp0']
  constructor
  · ring
  · linear_combination -hs2

/-! ### The explicit form of `W_{n-1}` (DLMF 14.7.3) -/

/-- Coefficients `(n+s)!/(2^s (n-s)! s!²)` of `P_n` in powers of `z-1`, extended by zero. -/
noncomputable def legSerA (n s : ℕ) : ℝ :=
  if s ≤ n then ((n+s).factorial : ℝ) / (2^s * ((n-s).factorial : ℝ) * (s.factorial : ℝ)^2) else 0

/-- Coefficients of `W_{n-1}` in powers of `z-1` (DLMF 14.7.3). -/
noncomputable def legSerE (n s : ℕ) : ℝ := legSerA n s * ((harmonic n : ℝ) - harmonic s)

/-- `m! ≠ 0` as a real number. -/
theorem legSer_fact_ne (m : ℕ) : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero

/-- `legSerA n 0 = 1`: the constant coefficient of `P_n` in powers of `z - 1`. -/
theorem legSerA_zero (n : ℕ) : legSerA n 0 = 1 := by
  have := legSer_fact_ne n
  simp [legSerA, this]

/-- Factorial identity behind the three-term recurrence of `P_n` in powers of `z-1`. -/
theorem legSerA_rec (n s : ℕ) :
    ((n:ℝ)+2) * legSerA (n+2) (s+1) = (2*n+3) * (legSerA (n+1) (s+1) + legSerA (n+1) s) -
      ((n:ℝ)+1) * legSerA n (s+1) := by
  rcases Nat.lt_or_ge n (s+1) with h | h
  · rcases Nat.lt_or_ge (n+1) (s+1) with h' | h'
    · rcases Nat.lt_or_ge (n+2) (s+1) with h'' | h''
      · simp [legSerA, show ¬ s+1 ≤ n+2 by omega, show ¬ s+1 ≤ n+1 by omega,
          show ¬ s+1 ≤ n by omega, show ¬ s ≤ n+1 by omega]
      · -- s = n+1
        obtain rfl : s = n+1 := by omega
        simp only [legSerA, show n+1+1 ≤ n+2 by omega, show ¬ n+1+1 ≤ n+1 by omega,
          show ¬ n+1+1 ≤ n by omega, show n+1 ≤ n+1 by omega, ↓reduceIte, Nat.sub_self,
          show n+2-(n+1+1) = 0 by omega]
        rw [show n+2+(n+1+1) = (2*n+1+1+1)+1 by ring, show n+1+(n+1) = 2*n+1+1 by ring,
          Nat.factorial_succ (2*n+1+1+1), Nat.factorial_succ (2*n+1+1), Nat.factorial_succ (n+1)]
        have := legSer_fact_ne (2*n+1+1); have := legSer_fact_ne (n+1)
        push_cast; field_simp; ring
    · -- s = n
      obtain rfl : s = n := by omega
      simp only [legSerA, show s+1 ≤ s+2 by omega, show s+1 ≤ s+1 by omega,
        show ¬ s+1 ≤ s by omega, show s ≤ s+1 by omega, ↓reduceIte, Nat.sub_self,
        show s+2-(s+1) = 1 by omega, show s+1-s = 1 by omega]
      rw [show s+2+(s+1) = (2*s+1+1)+1 by ring, show s+1+(s+1) = 2*s+1+1 by ring,
        show s+1+s = 2*s+1 by ring, Nat.factorial_succ (2*s+1+1), Nat.factorial_succ (2*s+1),
        Nat.factorial_succ s]
      have := legSer_fact_ne (2*s+1); have := legSer_fact_ne s
      push_cast; field_simp; ring
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [legSerA, show s+1 ≤ s+1+d+2 by omega, show s+1 ≤ s+1+d+1 by omega,
      show s+1 ≤ s+1+d by omega, show s ≤ s+1+d+1 by omega, ↓reduceIte,
      show s+1+d+2-(s+1) = d+2 by omega, show s+1+d+1-(s+1) = d+1 by omega,
      show s+1+d-(s+1) = d by omega, show s+1+d+1-s = d+2 by omega]
    rw [show s+1+d+2+(s+1) = (2*s+d+2+1)+1 by ring, show s+1+d+1+(s+1) = 2*s+d+2+1 by ring,
      show s+1+d+(s+1) = 2*s+d+2 by ring, show s+1+d+1+s = 2*s+d+2 by ring,
      Nat.factorial_succ (2*s+d+2+1), Nat.factorial_succ (2*s+d+2), Nat.factorial_succ (d+1),
      Nat.factorial_succ d, Nat.factorial_succ s]
    have := legSer_fact_ne (2*s+d+2); have := legSer_fact_ne d; have := legSer_fact_ne s
    push_cast; field_simp; ring

/-- `A(n+2,s+1) - A(n,s+1) = (2n+3) A(n+1,s)/(s+1)`. -/
theorem legSerA_diff (n s : ℕ) :
    legSerA (n+2) (s+1) - legSerA n (s+1) = (2*n+3) * legSerA (n+1) s / ((s:ℝ)+1) := by
  rcases Nat.lt_or_ge n (s+1) with h | h
  · rcases Nat.lt_or_ge (n+1) s with h' | h'
    · simp [legSerA, show ¬ s+1 ≤ n+2 by omega, show ¬ s+1 ≤ n by omega, show ¬ s ≤ n+1 by omega]
    · rcases Nat.lt_or_ge (n+1) (s+1) with h'' | h''
      · obtain rfl : s = n+1 := by omega
        simp only [legSerA, show n+1+1 ≤ n+2 by omega, show ¬ n+1+1 ≤ n by omega,
          show n+1 ≤ n+1 by omega, ↓reduceIte, Nat.sub_self, show n+2-(n+1+1) = 0 by omega]
        rw [show n+2+(n+1+1) = (2*n+1+1+1)+1 by ring, show n+1+(n+1) = 2*n+1+1 by ring,
          Nat.factorial_succ (2*n+1+1+1), Nat.factorial_succ (2*n+1+1), Nat.factorial_succ (n+1)]
        have := legSer_fact_ne (2*n+1+1); have := legSer_fact_ne (n+1)
        push_cast; field_simp; ring
      · obtain rfl : s = n := by omega
        simp only [legSerA, show s+1 ≤ s+2 by omega, show ¬ s+1 ≤ s by omega,
          show s ≤ s+1 by omega, ↓reduceIte, show s+2-(s+1) = 1 by omega,
          show s+1-s = 1 by omega]
        rw [show s+2+(s+1) = (2*s+1+1)+1 by ring, show s+1+s = 2*s+1 by ring,
          Nat.factorial_succ (2*s+1+1), Nat.factorial_succ (2*s+1), Nat.factorial_succ s]
        have := legSer_fact_ne (2*s+1); have := legSer_fact_ne s
        push_cast; field_simp; ring
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [legSerA, show s+1 ≤ s+1+d+2 by omega, show s+1 ≤ s+1+d by omega,
      show s ≤ s+1+d+1 by omega, ↓reduceIte,
      show s+1+d+2-(s+1) = d+2 by omega, show s+1+d-(s+1) = d by omega,
      show s+1+d+1-s = d+2 by omega]
    rw [show s+1+d+2+(s+1) = (2*s+d+2+1)+1 by ring, show s+1+d+(s+1) = 2*s+d+2 by ring,
      show s+1+d+1+s = 2*s+d+2 by ring,
      Nat.factorial_succ (2*s+d+2+1), Nat.factorial_succ (2*s+d+2), Nat.factorial_succ (d+1),
      Nat.factorial_succ d, Nat.factorial_succ s]
    have := legSer_fact_ne (2*s+d+2); have := legSer_fact_ne d; have := legSer_fact_ne s
    push_cast; field_simp; ring


/-- `legSerE n 0 = H_n`, the `n`-th harmonic number. -/
theorem legSerE_zero_right (n : ℕ) : legSerE n 0 = harmonic n := by
  simp [legSerE, legSerA_zero]

/-- For `n ≤ s`, `legSerE n s = 0`. -/
theorem legSerE_eq_zero {n s : ℕ} (h : n ≤ s) : legSerE n s = 0 := by
  rcases h.lt_or_eq with h | rfl
  · simp [legSerE, legSerA, show ¬ s ≤ n by omega]
  · simp [legSerE]

/-- The coefficients `legSerE n 0 = H_n` satisfy the Legendre recurrence `(n+2)E_{n+2} =
(2n+3)E_{n+1} - (n+1)E_n`. -/
theorem legSerE_rec_zero (n : ℕ) :
    ((n:ℝ)+2) * legSerE (n+2) 0 = (2*n+3) * legSerE (n+1) 0 - ((n:ℝ)+1) * legSerE n 0 := by
  simp only [legSerE_zero_right, harmonic_succ]
  push_cast
  field_simp
  ring

/-- For `s ≥ 0`, `(n+2) E(n+2,s+1) = (2n+3)(E(n+1,s+1) + E(n+1,s)) - (n+1) E(n,s+1)`, the
coefficient form of the Legendre recurrence in powers of `z - 1`. -/
theorem legSerE_rec_succ (n s : ℕ) :
    ((n:ℝ)+2) * legSerE (n+2) (s+1) = (2*n+3) * (legSerE (n+1) (s+1) + legSerE (n+1) s) -
      ((n:ℝ)+1) * legSerE n (s+1) := by
  have R1 := legSerA_rec n s
  have R2 := legSerA_diff n s
  simp only [legSerE]
  have e1 : (harmonic (n+2) : ℝ) = harmonic (n+1) + 1/((n:ℝ)+2) := by
    rw [harmonic_succ]; push_cast; ring
  have e2 : (harmonic n : ℝ) = harmonic (n+1) - 1/((n:ℝ)+1) := by
    rw [harmonic_succ]; push_cast; ring
  have e3 : (harmonic s : ℝ) = harmonic (s+1) - 1/((s:ℝ)+1) := by
    rw [harmonic_succ]; push_cast; ring
  rw [e1, e2, e3]
  have h1 : (n:ℝ)+1 ≠ 0 := by positivity
  have h2 : (n:ℝ)+2 ≠ 0 := by positivity
  have h3 : (s:ℝ)+1 ≠ 0 := by positivity
  rw [eq_div_iff h3] at R2
  have u1 := mul_inv_cancel₀ h1
  have u2 := mul_inv_cancel₀ h2
  have us := mul_inv_cancel₀ h3
  linear_combination ((harmonic (n+1):ℝ) - harmonic (s+1)) * R1 +
    legSerA (n+2) (s+1) * u2 - legSerA n (s+1) * u1 -
    (legSerA (n+2) (s+1) - legSerA n (s+1)) * us + ((s:ℝ)+1)⁻¹ * R2

/-- The explicit polynomial of DLMF 14.7.3 evaluated at `z`. -/
noncomputable def legSerW (n : ℕ) (z : ℂ) : ℂ :=
  ∑ s ∈ Finset.range n, (legSerE n s : ℂ) * (z-1)^s

/-- The sum defining `legSerW n z` may be extended to `s < n + k`, since the extra coefficients
vanish. -/
theorem legSerW_extend (n k : ℕ) (z : ℂ) :
    legSerW n z = ∑ s ∈ Finset.range (n+k), (legSerE n s : ℂ) * (z-1)^s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ih, ← add_assoc, Finset.sum_range_succ, legSerE_eq_zero (by omega)]; simp

/-- The polynomials `legSerW n` satisfy the Legendre recurrence `(n+2)W_{n+2}(z) = (2n+3) z
W_{n+1}(z) - (n+1) W_n(z)`. -/
theorem legSerW_rec (n : ℕ) (z : ℂ) :
    ((n:ℂ)+2) * legSerW (n+2) z = (2*n+3) * z * legSerW (n+1) z - ((n:ℂ)+1) * legSerW n z := by
  obtain ⟨t, rfl⟩ : ∃ t, z = 1 + t := ⟨z-1, by ring⟩
  rw [legSerW_extend (n+2) 1, legSerW_extend (n+1) 2, legSerW_extend n 3]
  simp only [add_sub_cancel_left]
  have htE : t * ∑ s ∈ Finset.range (n+1+1), (legSerE (n+1) s : ℂ) * t^s =
      ∑ s ∈ Finset.range (n+2), (legSerE (n+1) s : ℂ) * t^(s+1) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
  have hE1 : ∑ s ∈ Finset.range (n+1+2), (legSerE (n+1) s : ℂ) * t^s =
      ∑ s ∈ Finset.range (n+1+1), (legSerE (n+1) s : ℂ) * t^s := by
    rw [show n+1+2 = n+1+1+1 by ring, Finset.sum_range_succ, legSerE_eq_zero (by omega)]; simp
  rw [show (2*(n:ℂ)+3) * (1+t) * ∑ s ∈ Finset.range (n+1+2), (legSerE (n+1) s : ℂ) * t^s =
      (2*(n:ℂ)+3) * (∑ s ∈ Finset.range (n+1+2), (legSerE (n+1) s : ℂ) * t^s +
        t * ∑ s ∈ Finset.range (n+1+1), (legSerE (n+1) s : ℂ) * t^s) by rw [hE1]; ring, htE]
  rw [show n+2+1 = n+2+1 by rfl, show n+1+2 = n+2+1 by ring, show n+3 = n+2+1 by ring,
    Finset.sum_range_succ' _ (n+2), Finset.sum_range_succ' _ (n+2), Finset.sum_range_succ' _ (n+2)]
  have key : ∀ s ∈ Finset.range (n+2),
      ((n:ℂ)+2) * ((legSerE (n+2) (s+1) : ℂ) * t^(s+1)) =
        (2*n+3) * ((legSerE (n+1) (s+1) : ℂ) * t^(s+1) + (legSerE (n+1) s : ℂ) * t^(s+1)) -
          ((n:ℂ)+1) * ((legSerE n (s+1) : ℂ) * t^(s+1)) := by
    intro s _
    have := congrArg (fun r : ℝ => (r : ℂ)) (legSerE_rec_succ n s)
    push_cast at this
    linear_combination t^(s+1) * this
  have key0 := congrArg (fun r : ℝ => (r : ℂ)) (legSerE_rec_zero n)
  push_cast at key0
  rw [mul_add ((n:ℂ)+2), Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [pow_zero, mul_one]
  linear_combination key0

/-- The explicit polynomial of DLMF 14.7.3 equals `R_n = legendreQPoly n`: `∑_{s<n} A(n,s)(H_n -
H_s)(z-1)^s = R_n(z)`. -/
theorem legSerW_eq (n : ℕ) (z : ℂ) : legSerW n z = (legendreQPoly n).eval z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [legSerW, legendreQPoly]
    | 1, _ =>
      simp [legSerW, legendreQPoly, legSerE_zero_right]
    | n+2, ih =>
      have e := legSerW_rec n z
      rw [ih n (by omega), ih (n+1) (by omega)] at e
      have hn : (n:ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+1)
      rw [legendreQPoly]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
      rw [eq_inv_mul_iff_mul_eq₀ hn, e]

/-! ### Generating functions of `W_{n-1}` and of `Q_n` (DLMF 14.7.20, 14.7.22) -/

/-- Absolute convergence of `∑ P_n(z) hⁿ` inside the circle of the two roots. -/
theorem legSer_summable_G (z ζ₁ ζ₂ h : ℂ) (hs : ζ₁ + ζ₂ = 2*z) (hp : ζ₁ * ζ₂ = 1)
    (h1 : ‖h*ζ₁‖ < 1) (h2 : ‖h*ζ₂‖ < 1) :
    Summable fun n => ‖legSerP z n * h^n‖ := by
  have hs1 := legSer_summable_B ζ₁ h h1
  have hs2 := legSer_summable_B ζ₂ h h2
  refine (summable_norm_sum_mul_antidiagonal_of_summable_norm hs1 hs2).congr fun n => ?_
  congr 1
  rw [show legSerP z n = PowerSeries.coeff n (legSerG z) by simp [legSerG],
    ← legSer_B_mul z ζ₁ ζ₂ hs hp, PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; ring

/-- The `n`-th term of `legSerF z` satisfies `‖f_n hⁿ‖ ≤ ‖h‖ ‖P_{n-1}(z) h^{n-1}‖`. -/
theorem legSer_norm_coeff_F_le (z h : ℂ) (n : ℕ) :
    ‖PowerSeries.coeff n (legSerF z) * h^n‖ ≤ ‖h‖ * ‖legSerP z (n-1) * h^(n-1)‖ := by
  simp only [legSerF, PowerSeries.coeff_mk]
  rcases n with _ | n
  · simp; positivity
  · simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte, norm_mul, norm_div, norm_pow,
      Complex.norm_natCast, pow_succ]
    have : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
    have h0 : 0 ≤ ‖legSerP z n‖ * (‖h‖^n * ‖h‖) := by positivity
    calc ‖legSerP z n‖ / ((n+1:ℕ):ℝ) * (‖h‖^n * ‖h‖) = (‖legSerP z n‖ * (‖h‖^n * ‖h‖)) / ((n+1:ℕ):ℝ) := by ring
      _ ≤ ‖legSerP z n‖ * (‖h‖^n * ‖h‖) := div_le_self h0 this
      _ = _ := by ring

/-- If `ζ₁ + ζ₂ = 2z`, `ζ₁ζ₂ = 1` and `‖hζ₁‖, ‖hζ₂‖ < 1`, then `∑ f_n hⁿ` for `legSerF z` converges
absolutely. -/
theorem legSer_summable_F (z ζ₁ ζ₂ h : ℂ) (hs : ζ₁ + ζ₂ = 2*z) (hp : ζ₁ * ζ₂ = 1)
    (h1 : ‖h*ζ₁‖ < 1) (h2 : ‖h*ζ₂‖ < 1) :
    Summable fun n => ‖PowerSeries.coeff n (legSerF z) * h^n‖ := by
  have hG := legSer_summable_G z ζ₁ ζ₂ h hs hp h1 h2
  have hG' : Summable fun n => ‖h‖ * ‖legSerP z (n-1) * h^(n-1)‖ := by
    refine Summable.mul_left _ ?_
    rw [← summable_nat_add_iff 1]
    simpa using hG
  exact hG'.of_nonneg_of_le (fun _ => norm_nonneg _) (legSer_norm_coeff_F_le z h)

/-- Cauchy product: `∑ W_{n-1}(z) hⁿ = (∑ F_n hⁿ) (1-2zh+h²)^{-1/2}`. -/
theorem legSer_hasSum_W (z ζ₁ ζ₂ h : ℂ) (hs : ζ₁ + ζ₂ = 2*z) (hp : ζ₁ * ζ₂ = 1)
    (h1 : ‖h*ζ₁‖ < 1) (h2 : ‖h*ζ₂‖ < 1) :
    HasSum (fun n => (legendreQPoly n).eval z * h^n)
      ((∑' n, PowerSeries.coeff n (legSerF z) * h^n) * (1 - 2*z*h + h^2)^(-1/2:ℂ)) := by
  have hF := legSer_summable_F z ζ₁ ζ₂ h hs hp h1 h2
  have hG := legSer_summable_G z ζ₁ ζ₂ h hs hp h1 h2
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hF hG
  rw [(legSer_generating z ζ₁ ζ₂ h hs hp h1 h2).tsum_eq] at hprod
  rw [hprod]
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hF hG).of_norm
  refine (hsum.hasSum).congr_fun fun n => ?_
  rw [← legSer_U_eq z n, PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; simp [legSerG]; ring

/-- Derivative of the closed form `log(1+x) - log(x - t + √(1-2xt+t²))`. -/
theorem legSer_hasDerivAt_phi {x t : ℝ} (hq : 0 < 1-2*x*t+t^2) (hl : 0 < x - t + √(1-2*x*t+t^2)) :
    HasDerivAt (fun s : ℝ => Real.log (1+x) - Real.log (x - s + √(1-2*x*s+s^2)))
      (1 / √(1-2*x*t+t^2)) t := by
  have hQ : HasDerivAt (fun s : ℝ => 1-2*x*s+s^2) (-2*x + 2*t) t := by
    have := (((hasDerivAt_id' t).const_mul (2*x)).const_sub 1).add (hasDerivAt_pow 2 t)
    convert this using 1; push_cast; ring
  have hS := hQ.sqrt hq.ne'
  have hU : HasDerivAt (fun s : ℝ => x - s + √(1-2*x*s+s^2))
      (-1 + (-2*x + 2*t) / (2 * √(1-2*x*t+t^2))) t := by
    exact ((hasDerivAt_id' t).const_sub x).add hS
  have hL := (hU.log hl.ne').const_sub (Real.log (1+x))
  refine hL.congr_deriv ?_
  have hsq : 0 < √(1-2*x*t+t^2) := Real.sqrt_pos.mpr hq
  have hsq2 := Real.sq_sqrt hq.le
  field_simp
  ring

/-- `∑ P_{n-1}(x) tⁿ / n = log(1+x) - log(x - t + √(1-2xt+t²))` for real `t` in a disc where the
binomial factors converge and the logarithm is real. -/
theorem legSer_tsum_F_real {x r : ℝ} (ζ₁ ζ₂ : ℂ) (hs : ζ₁ + ζ₂ = 2*x) (hp : ζ₁ * ζ₂ = 1)
    (h1 : ‖(r:ℂ)*ζ₁‖ < 1) (h2 : ‖(r:ℂ)*ζ₂‖ < 1)
    (hq : ∀ t : ℝ, |t| < r → 0 < 1-2*x*t+t^2)
    (hl : ∀ t : ℝ, |t| < r → 0 < x - t + √(1-2*x*t+t^2)) {t : ℝ} (ht : |t| < r) :
    ∑' n, PowerSeries.coeff n (legSerF x) * (t:ℂ)^n =
      ((Real.log (1+x) - Real.log (x - t + √(1-2*x*t+t^2)) : ℝ) : ℂ) := by
  set c : ℕ → ℂ := fun n => PowerSeries.coeff n (legSerF x) with hc
  have hc0 : c 0 = 0 := by simp [hc, legSerF]
  have hcn : ∀ n : ℕ, c (n+1) * ((n+1:ℕ):ℂ) = legSerP x n := fun n => by
    simp only [hc, legSerF, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    have : ((n+1:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    field_simp
  set S : Set ℝ := Ioo (-r) r
  have hSo : IsOpen S := isOpen_Ioo
  have hSc : IsPreconnected S := isPreconnected_Ioo
  have hmem : ∀ y ∈ S, |y| < r := fun y hy => abs_lt.mpr hy
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg t) ht
  have h0S : (0:ℝ) ∈ S := ⟨by linarith, hr0⟩
  have htS : t ∈ S := abs_lt.mp ht
  have hnorm : ∀ y : ℝ, |y| < r → ∀ ζ : ℂ, ‖(r:ℂ)*ζ‖ < 1 → ‖(y:ℂ)*ζ‖ < 1 := fun y hy ζ hζ => by
    refine lt_of_le_of_lt ?_ hζ
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hr0]
    exact mul_le_mul_of_nonneg_right hy.le (norm_nonneg _)
  -- termwise derivative
  set g : ℕ → ℝ → ℂ := fun n y => c n * (y:ℂ)^n
  set g' : ℕ → ℝ → ℂ := fun n y => c n * ((n:ℂ) * (y:ℂ)^(n-1))
  have hg : ∀ n y, y ∈ S → HasDerivAt (g n) (g' n y) y := fun n y _ =>
    ((hasDerivAt_pow n (y:ℂ)).comp_ofReal).const_mul (c n)
  set u : ℕ → ℝ := fun n => ‖legSerP x (n-1) * (r:ℂ)^(n-1)‖
  have hu : Summable u := by
    rw [← summable_nat_add_iff 1]
    simpa [u] using legSer_summable_G x ζ₁ ζ₂ r hs hp h1 h2
  have hg' : ∀ n y, y ∈ S → ‖g' n y‖ ≤ u n := fun n y hy => by
    rcases n with _ | n
    · simp [g', hc0, u]
    · simp only [g', u, Nat.add_sub_cancel]
      rw [← mul_assoc, hcn, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr0]
      gcongr
      exact (hmem y hy).le
  have hsum0 : Summable fun n => g n 0 := by
    refine (summable_of_ne_finset_zero (s := {0}) fun n hn => ?_)
    rcases n with _ | n
    · simp at hn
    · simp [g]
  have hD : ∀ y ∈ S, HasDerivAt (fun z => ∑' n, g n z) ((1 - 2*(x:ℂ)*y + (y:ℂ)^2)^(-1/2:ℂ)) y := by
    intro y hy
    have := hasDerivAt_tsum_of_isPreconnected hu hSo hSc hg hg' h0S hsum0 hy
    convert this using 1
    have hsg : Summable fun n => g' n y :=
      Summable.of_norm_bounded hu fun n => hg' n y hy
    rw [hsg.tsum_eq_zero_add]
    simp only [g', hc0, zero_mul, zero_add, Nat.add_sub_cancel]
    rw [← (legSer_generating x ζ₁ ζ₂ y hs hp (hnorm y (hmem y hy) ζ₁ h1)
      (hnorm y (hmem y hy) ζ₂ h2)).tsum_eq]
    refine tsum_congr fun n => ?_
    rw [← mul_assoc, hcn]
  set Φf : ℝ → ℂ := fun y => ((Real.log (1+x) - Real.log (x - y + √(1-2*x*y+y^2)) : ℝ) : ℂ)
  have hΦ : ∀ y ∈ S, HasDerivAt Φf ((1 - 2*(x:ℂ)*y + (y:ℂ)^2)^(-1/2:ℂ)) y := by
    intro y hy
    have := (legSer_hasDerivAt_phi (hq y (hmem y hy)) (hl y (hmem y hy))).ofReal_comp
    convert this using 1
    have hq0 := (hq y (hmem y hy)).le
    rw [show (1 - 2*(x:ℂ)*y + (y:ℂ)^2) = ((1-2*x*y+y^2 : ℝ) : ℂ) by push_cast; ring,
      show (-1/2:ℂ) = ((-1/2:ℝ):ℂ) by push_cast; ring, ← Complex.ofReal_cpow hq0,
      Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hq0]
    norm_num
  have heq := hSo.eqOn_of_deriv_eq hSc (f := fun z => ∑' n, g n z) (g := Φf)
    (fun y hy => (hD y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hΦ y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => by simp only [(hD y hy).deriv, (hΦ y hy).deriv]) h0S (by
      have : (fun n => g n 0) = fun _ => 0 := funext fun n => by
        rcases n with _ | n
        · simp [g, hc0]
        · simp [g]
      simp only [this, tsum_zero, Φf]
      norm_num [show x - 0 + √1 = 1 + x by simp; ring]
      rw [add_comm x 1, sub_self])
  exact heq htS

/-- `a^{1/2} = √a` for `a ≥ 0`, as complex numbers. -/
theorem legSer_cpow_half {a : ℝ} (ha : 0 ≤ a) : ((a:ℂ))^(1/2:ℂ) = ((√a : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha]; push_cast; ring_nf

/-- Combination of the generating functions of `P_n` and `W_{n-1}` for real `x` and `h`. -/
theorem legSer_hasSum_Q_real {x h r : ℝ} (ζ₁ ζ₂ : ℂ) (hs : ζ₁ + ζ₂ = 2*x) (hp : ζ₁ * ζ₂ = 1)
    (h1 : ‖(r:ℂ)*ζ₁‖ < 1) (h2 : ‖(r:ℂ)*ζ₂‖ < 1)
    (hq : ∀ t : ℝ, |t| < r → 0 < 1-2*x*t+t^2)
    (hl : ∀ t : ℝ, |t| < r → 0 < x - t + √(1-2*x*t+t^2)) (hh : |h| < r) (c : ℂ) :
    HasSum (fun n : ℕ => (c * legSerP x n - (legendreQPoly n).eval (x:ℂ)) * (h:ℂ)^n)
      ((c - ((Real.log (1+x) - Real.log (x - h + √(1-2*x*h+h^2)) : ℝ) : ℂ)) *
        (1-2*x*h+h^2:ℂ)^(-1/2:ℂ)) := by
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg h) hh
  have hn : ∀ ζ : ℂ, ‖(r:ℂ)*ζ‖ < 1 → ‖(h:ℂ)*ζ‖ < 1 := fun ζ hζ => by
    refine lt_of_le_of_lt ?_ hζ
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hr0]
    exact mul_le_mul_of_nonneg_right hh.le (norm_nonneg _)
  have hP := (legSer_generating x ζ₁ ζ₂ h hs hp (hn ζ₁ h1) (hn ζ₂ h2)).mul_left c
  have hW := legSer_hasSum_W x ζ₁ ζ₂ h hs hp (hn ζ₁ h1) (hn ζ₂ h2)
  rw [legSer_tsum_F_real ζ₁ ζ₂ hs hp h1 h2 hq hl hh] at hW
  convert hP.sub hW using 1
  · funext n; ring
  · ring

end DLMF.Legendre
