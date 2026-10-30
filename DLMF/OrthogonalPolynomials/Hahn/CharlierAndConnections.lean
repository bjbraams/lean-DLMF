/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Hahn.HahnAndMeixner

/-!
# Charlier polynomials and discrete-family connections

Charlier generating functions and connection identities among discrete orthogonal polynomial
families.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.Hahn`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

open DLMF.Confluent

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- `∑ₙ (-n)ₖ wⁿ / n! = (-w)ᵏ eʷ`. -/
theorem hasSum_poch_neg_nat_div_factorial (k : ℕ) (w : ℂ) :
    HasSum (fun n : ℕ => poch (-(n : ℂ)) k / n ! * w ^ n) ((-w) ^ k * exp w) := by
  have he : HasSum (fun n : ℕ => w ^ n / n !) (exp w) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp w
  have h0 : ∑ i ∈ Finset.range k, poch (-(i : ℂ)) k / i ! * w ^ i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [poch_neg_nat_eq_zero (by simpa using hi)]; simp
  have key := (hasSum_nat_add_iff (f := fun n : ℕ => poch (-(n : ℂ)) k / n ! * w ^ n) k
    (g := (-w) ^ k * exp w)).mp ?_
  · rwa [h0, add_zero] at key
  refine (he.mul_left ((-w) ^ k)).congr_fun fun n => ?_
  have hn : ((n + k) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn' : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd : ((n + k).descFactorial k : ℂ) * n ! = (n + k) ! := by
    have := Nat.factorial_mul_descFactorial (show k ≤ n + k by omega)
    rw [show n + k - k = n by omega] at this
    exact_mod_cast (mul_comm _ _).trans this
  rw [poch_neg_coe_nat, neg_pow, pow_add]
  field_simp
  linear_combination (-1) ^ k * w ^ n * w ^ k * hd

/-- The series with terms `(fun n : ℕ => charlier a n x / n.factorial * z ^ n)` converges to `(exp
z * (1 - z / a) ^ x)`. -/
@[dlmf 18.23.E5]
theorem charlier_generating_function (a : ℂ) (x : ℕ) (z : ℂ) :
    HasSum (fun n : ℕ => charlier a n x / n.factorial * z ^ n) (exp z * (1 - z / a) ^ x) := by
  unfold charlier
  simp_rw [terminatingHG_two_neg_nat_swap _ x, terminatingHG, Finset.sum_div, Finset.sum_mul]
  have h := hasSum_sum (s := Finset.range (x + 1)) (fun k _ =>
    (hasSum_poch_neg_nat_div_factorial k z).mul_left (poch (-(x : ℂ)) k * (-a⁻¹) ^ k / k !))
  convert h using 1
  · funext n
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
    ring
  · rw [← sum_poch_neg_nat_div_factorial_mul_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show z / a = (-a⁻¹) * (-z) by ring, mul_pow]
    ring

/-- The Meixner–Pollaczek polynomial of degree zero. -/
theorem meixnerPollaczek_zero (lam phi x : ℂ) : meixnerPollaczek lam phi 0 x = 1 := by
  simp [meixnerPollaczek, terminatingHG, poch_zero]

/-- `e^{iφ} + e^{-iφ} = 2 cos φ` and `e^{-iφ} - e^{iφ} = -2 i sin φ`, in the form used below. -/
theorem exp_I_mul_add_recip (phi : ℂ) :
    exp (I * phi) + (exp (I * phi))⁻¹ = 2 * cos phi ∧
      exp (I * phi) - (exp (I * phi))⁻¹ = 2 * I * sin phi := by
  rw [← Complex.exp_neg, Complex.cos, Complex.sin]
  constructor
  · ring_nf
  · ring_nf; rw [I_sq]; ring

/-- The series with terms `(fun n : ℕ => meixnerPollaczek lam phi n x * z ^ n)` converges to `((1
- exp (I * phi) * z) ^ (-lam + I * x) * (1 - exp (-I * phi) * z) ^ (-lam - I * x))`. -/
@[dlmf 18.23.E7]
theorem meixnerPollaczek_generating_function {lam : ℂ} (hlam : 0 < lam.re) (phi x : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => meixnerPollaczek lam phi n x * z ^ n)
      ((1 - exp (I * phi) * z) ^ (-lam + I * x) * (1 - exp (-I * phi) * z) ^ (-lam - I * x)) := by
  set u := exp (I * phi) with hu
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hu1 : ‖u‖ = 1 := by rw [hu, mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hlam0 : lam ≠ 0 := fun h => by rw [h, Complex.zero_re] at hlam; exact lt_irrefl _ hlam
  obtain ⟨hcos, hsin⟩ := exp_I_mul_add_recip (phi : ℂ)
  have hcoeff : ∀ n, meixnerPollaczek lam phi n x =
      PowerSeries.coeff n (binomProductSeries (lam - I * x) (lam + I * x) u) := by
    refine eq_coeff_binomProductSeries hu0 (meixnerPollaczek_zero _ _ _) ?_ ?_
    · rw [meixnerPollaczek_one hlam0]
      linear_combination (-lam) * hcos + (I * x) * hsin + (2 * x * sin (phi : ℂ)) * I_sq
    · intro n
      rw [meixnerPollaczek_recurrence hlam]
      linear_combination (-(n + 1 + lam : ℂ) * meixnerPollaczek lam phi (n + 1) x) * hcos +
        (I * x * meixnerPollaczek lam phi (n + 1) x) * hsin +
        (2 * x * sin (phi : ℂ) * meixnerPollaczek lam phi (n + 1) x) * I_sq
  have h1 : ‖u * z‖ < 1 := by rwa [norm_mul, hu1, one_mul]
  have h2 : ‖u⁻¹ * z‖ < 1 := by rwa [norm_mul, norm_inv, hu1, inv_one, one_mul]
  have h := hasSum_coeff_binomProductSeries_mul_pow (lam - I * x) (lam + I * x) h1 h2
  rw [show u⁻¹ = exp (-I * phi) by rw [hu, ← Complex.exp_neg]; ring_nf,
    show -(lam - I * x) = -lam + I * x by ring, show -(lam + I * x) = -lam - I * x by ring] at h
  simpa only [hcoeff] using h

/-- Limits propagate through a three-term recurrence whose coefficients converge. -/
theorem tendsto_of_three_term {ι : Type*} {l : Filter ι} {f : ℕ → ι → ℂ} {g : ℕ → ℂ}
    {A B : ℕ → ι → ℂ} {A' B' : ℕ → ℂ}
    (h0 : Tendsto (f 0) l (𝓝 (g 0))) (h1 : Tendsto (f 1) l (𝓝 (g 1)))
    (hA : ∀ n, Tendsto (A n) l (𝓝 (A' n))) (hB : ∀ n, Tendsto (B n) l (𝓝 (B' n)))
    (hf : ∀ n, ∀ᶠ t in l, f (n + 2) t = A n t * f (n + 1) t + B n t * f n t)
    (hg : ∀ n, g (n + 2) = A' n * g (n + 1) + B' n * g n) (n : ℕ) :
    Tendsto (f n) l (𝓝 (g n)) := by
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih0 ih1 =>
    rw [hg n]
    exact (((hA n).mul ih1).add ((hB n).mul ih0)).congr' (by
      filter_upwards [hf n] with t ht
      exact ht.symm)

/-- `c / a → 0` for complex `c` as the real `a → ∞`. -/
theorem tendsto_const_div_ofReal_atTop (c : ℂ) :
    Tendsto (fun a : ℝ => c / (a : ℂ)) atTop (𝓝 0) := by
  have := (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  rw [ofReal_zero] at this
  simpa [div_eq_mul_inv] using this.const_mul c

/-- `(c + s t)_k / t^k → s^k` as the real `t → ∞`. -/
theorem tendsto_poch_add_mul_div_pow (c s : ℂ) (k : ℕ) :
    Tendsto (fun t : ℝ => poch (c + s * t) k / (t : ℂ) ^ k) atTop (𝓝 (s ^ k)) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    have h1 : Tendsto (fun t : ℝ => (c + k) / (t : ℂ) + s) atTop (𝓝 s) := by
      simpa using (tendsto_const_div_ofReal_atTop (c + k)).add_const s
    refine ((ih.mul h1).congr' ?_).trans (by rw [pow_succ])
    filter_upwards [eventually_gt_atTop 0] with t ht
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [poch_succ, pow_succ]
    field_simp
    ring

/-- The map `(fun t : ℝ => hahn (p * t) ((1 - p) * t) N n x)` tends to `(𝓝 (krawtchouk p N n x))`
along `atTop`. -/
@[dlmf 18.21.E3]
theorem hahn_limit_krawtchouk {p : ℝ} (hp : 0 < p) (N n : ℕ) (x : ℂ) :
    Tendsto (fun t : ℝ => hahn (p * t) ((1 - p) * t) N n x) atTop (𝓝 (krawtchouk p N n x)) := by
  unfold hahn krawtchouk terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hpt : Tendsto (fun t : ℝ => p * t) atTop atTop := tendsto_id.const_mul_atTop hp
  have h1 := tendsto_poch_add_div_pow ((n : ℂ) + 1) k
  have h2 := ((tendsto_poch_add_div_pow 1 k).comp hpt).inv₀ one_ne_zero
  rw [inv_one] at h2
  have := (h1.mul h2).const_mul
    (poch (-(n : ℂ)) k * poch (-x) k / poch (-(N : ℂ)) k / k.factorial * ((p : ℂ)⁻¹) ^ k)
  rw [mul_one, mul_one] at this
  rw [show poch (-(n : ℂ)) k * poch (-x) k / poch (-(N : ℂ)) k * (p : ℂ)⁻¹ ^ k /
      (k.factorial : ℂ) = poch (-(n : ℂ)) k * poch (-x) k / poch (-(N : ℂ)) k /
      k.factorial * ((p : ℂ)⁻¹) ^ k by ring]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hp' : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  simp only [Function.comp_apply, ofReal_mul]
  have e1 : (n : ℂ) + (p * t) + ((1 - p) * t) + 1 = (n + 1) + t := by ring
  have e2 : (p : ℂ) * t + 1 = 1 + p * t := by ring
  rw [e1, e2, mul_pow, inv_pow]
  field_simp
  ring

/-- The map `(fun N : ℕ => hahn α β N n (N * x))` tends to `(𝓝 (jacobiPolyP α β n (1 - 2 * x) /
jacobiPolyP α β n 1))` along `atTop`. -/
@[dlmf 18.21.E5]
theorem hahn_limit_jacobi {α β : ℝ} (hα : -1 < α) (n : ℕ) (x : ℂ) :
    Tendsto (fun N : ℕ => hahn α β N n (N * x)) atTop (𝓝 (jacobiPolyP α β n (1 - 2 * x) / jacobiPolyP α β n 1)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hP1 : poch ((α : ℂ) + 1) n / (n ! : ℂ) ≠ 0 :=
    div_ne_zero (poch_ne_zero_of_not_neg_nat hα' n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  have hJ : jacobiPolyP α β n (1 - 2 * x) / jacobiPolyP α β n 1 =
      ∑ k ∈ Finset.range (n + 1), gaussHGCoeff (-(n : ℂ)) (n + α + β + 1) (α + 1) k * x ^ k := by
    unfold jacobiPolyP
    rw [show (1 - (1 - 2 * x)) / 2 = x by ring, sub_self, zero_div,
      ordinaryHypergeometric_zero, mul_one, mul_div_cancel_left₀ _ hP1,
      ordinaryHypergeometric_eq_sum_neg_nat]
  rw [hJ]
  unfold hahn terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have h1 := (tendsto_poch_add_mul_div_pow 0 (-x) k).comp hnat
  have h2 := (tendsto_poch_add_mul_div_pow 0 (-1) k).comp hnat
  have hneg : ((-1 : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 := (h1.div h2 hneg).const_mul (gaussHGCoeff (-(n : ℂ)) (n + α + β + 1) (α + 1) k)
  rw [show (-x) ^ k / (-1 : ℂ) ^ k = x ^ k by rw [neg_pow x, mul_div_cancel_left₀ _ hneg]] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Pi.div_apply, Function.comp_apply, zero_add, ofReal_natCast]
  rw [show -1 * (N : ℂ) = -(N : ℂ) by ring, show -x * (N : ℂ) = -(N * x) by ring]
  have hNk : ((N : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN.ne')
  unfold gaussHGCoeff
  by_cases hp : poch (-(N : ℂ)) k = 0
  · simp [hp]
  · field_simp

/-- The map `(fun N : ℕ => krawtchouk (a / N) N n x)` tends to `(𝓝 (charlier a n x))` along
`atTop`. -/
@[dlmf 18.21.E6]
theorem krawtchouk_limit_charlier {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℂ) :
    Tendsto (fun N : ℕ => krawtchouk (a / N) N n x) atTop (𝓝 (charlier a n x)) := by
  unfold krawtchouk charlier terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hlim := (tendsto_poch_neg_div_pow k).inv₀ one_ne_zero
  rw [inv_one] at hlim
  have := hlim.const_mul (poch (-(n : ℂ)) k * poch (-x) k / k.factorial * (-a⁻¹) ^ k)
  rw [mul_one] at this
  rw [show poch (-(n : ℂ)) k * poch (-x) k / 1 * (-a⁻¹) ^ k / (k.factorial : ℂ) =
      poch (-(n : ℂ)) k * poch (-x) k / k.factorial * (-a⁻¹) ^ k by ring]
  refine this.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [inv_div] at hlim ⊢
  have e : (-a⁻¹) ^ k * (-(N : ℂ)) ^ k = ((N : ℂ) / a) ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  linear_combination (poch (-(n : ℂ)) k * poch (-x) k / k.factorial / poch (-(N : ℂ)) k) * e

/-- The map `(fun b : ℝ => meixner b (a / (a + b)) n x)` tends to `(𝓝 (charlier a n x))` along
`atTop`. -/
@[dlmf 18.21.E7]
theorem meixner_limit_charlier {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℂ) :
    Tendsto (fun b : ℝ => meixner b (a / (a + b)) n x) atTop (𝓝 (charlier a n x)) := by
  unfold meixner charlier terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hlim := (tendsto_poch_add_div_pow 0 k).inv₀ one_ne_zero
  rw [inv_one] at hlim
  simp only [inv_div, zero_add] at hlim
  have := hlim.const_mul (poch (-(n : ℂ)) k * poch (-x) k / k.factorial * (-(a : ℂ)⁻¹) ^ k)
  rw [mul_one] at this
  rw [show poch (-(n : ℂ)) k * poch (-x) k / 1 * (-(a : ℂ)⁻¹) ^ k / (k.factorial : ℂ) =
      poch (-(n : ℂ)) k * poch (-x) k / k.factorial * (-(a : ℂ)⁻¹) ^ k by ring]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hb' : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hab : (a : ℂ) + b ≠ 0 := by exact_mod_cast (add_pos ha hb).ne'
  have e : (-(a : ℂ)⁻¹) ^ k * (b : ℂ) ^ k = (1 - ((a : ℂ) / (a + b))⁻¹) ^ k := by
    rw [← mul_pow]; congr 1; field_simp; ring
  linear_combination (poch (-(n : ℂ)) k * poch (-x) k / k.factorial / poch (b : ℂ) k) * e

/-- Charlier polynomials as polynomials in `x`. -/
def charlierPoly (a : ℂ) (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (poch (-(n : ℂ)) k * (-a⁻¹) ^ k / k.factorial) *
    (ascPochhammer ℂ k).comp (-X)

/-- Evaluation of `charlierPoly` is the Charlier polynomial. -/
theorem eval_charlierPoly (a : ℂ) (n : ℕ) (x : ℂ) : (charlierPoly a n).eval x = charlier a n x := by
  simp only [charlierPoly, charlier, terminatingHG, eval_finsetSum, eval_mul, eval_C, eval_comp,
    eval_neg, eval_X, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [poch]; ring

/-- The three-term recurrence of the Charlier polynomials in the degree. -/
theorem charlier_recurrence {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℂ) :
    a * charlier a (n + 2) x =
      (n + 1 + a - x) * charlier a (n + 1) x - (n + 1) * charlier a n x := by
  -- integer points, from the difference equation and duality
  have hint : ∀ m : ℕ, a * charlier a (n + 2) m =
      (n + 1 + a - m) * charlier a (n + 1) m - (n + 1) * charlier a n m := by
    intro m
    have h := charlier_difference_equation ha m ((n + 1 : ℕ) : ℂ)
    rw [show ((n + 1 : ℕ) : ℂ) + 1 = ((n + 2 : ℕ) : ℂ) by push_cast; ring,
      show ((n + 1 : ℕ) : ℂ) - 1 = ((n : ℕ) : ℂ) by push_cast; ring,
      charlier_duality a m (n + 2), charlier_duality a m (n + 1), charlier_duality a m n] at h
    push_cast at h
    linear_combination h
  -- polynomial identity
  have hpoly : C a * charlierPoly a (n + 2) =
      (C (n + 1 + a) - X) * charlierPoly a (n + 1) - C ((n : ℂ) + 1) * charlierPoly a n := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (m : ℂ))
      Nat.cast_injective fun m => ?_
    simp only [Set.mem_ofPred_eq, eval_mul, eval_sub, eval_C, eval_X, eval_charlierPoly]
    rw [hint m]
  have := congrArg (eval x) hpoly
  simp only [eval_mul, eval_sub, eval_C, eval_X, eval_charlierPoly] at this
  rw [this]

/-- The map `(fun a : ℝ => (Real.sqrt (2 * a) : ℂ) ^ n * charlier a n ((Real.sqrt (2 * a) : ℂ) * x
+ a))` tends to `(𝓝 ((-1 : ℂ) ^ n * aeval x (hermitePolyH n)))` along `atTop`. -/
@[dlmf 18.21.E9]
theorem charlier_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => (Real.sqrt (2 * a) : ℂ) ^ n * charlier a n ((Real.sqrt (2 * a) : ℂ) * x + a)) atTop (𝓝 ((-1 : ℂ) ^ n * aeval x (hermitePolyH n))) := by
  set f : ℕ → ℝ → ℂ := fun n a =>
    (Real.sqrt (2 * a) : ℂ) ^ n * charlier a n ((Real.sqrt (2 * a) : ℂ) * x + a) with hf
  -- the scaled recurrence coefficient `√(2a)/a`
  have hs : Tendsto (fun a : ℝ => ((Real.sqrt (2 * a) / a : ℝ) : ℂ)) atTop (𝓝 0) := by
    have : Tendsto (fun a : ℝ => Real.sqrt 2 * (Real.sqrt a)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop)).const_mul (Real.sqrt 2)
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp]
    refine Complex.continuous_ofReal.continuousAt.tendsto.comp (this.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with a ha
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_div_assoc]
    congr 1
    have hsa : (0 : ℝ) < Real.sqrt a := Real.sqrt_pos.mpr ha
    field_simp
    rw [Real.sq_sqrt ha.le]
  refine tendsto_of_three_term (f := f) (g := fun n => (-1 : ℂ) ^ n * aeval x (hermitePolyH n))
    (A := fun n a => (n + 1 : ℂ) * ((Real.sqrt (2 * a) / a : ℝ) : ℂ) - 2 * x)
    (B := fun n _ => -2 * (n + 1 : ℂ)) (A' := fun _ => -2 * x) (B' := fun n => -2 * (n + 1 : ℂ))
    ?_ ?_ ?_ ?_ ?_ ?_ n
  · simp [hf, charlier, terminatingHG, poch_zero]
  · have h1 : (aeval x (hermitePolyH 1) : ℂ) = 2 * x := by simp [hermitePolyH_succ, map_ofNat]
    simp only [pow_one, h1]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with a ha
    have hsq : ((Real.sqrt (2 * a) : ℝ) : ℂ) ^ 2 = 2 * a := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    simp only [hf, charlier, terminatingHG, Finset.sum_range_succ, Finset.sum_range_zero,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, poch_zero, poch_one, pow_one]
    field_simp
    linear_combination x * hsq
  · intro n
    simpa using (hs.const_mul ((n : ℂ) + 1)).sub_const (2 * x)
  · intro n; exact tendsto_const_nhds
  · intro n
    filter_upwards [eventually_gt_atTop 0] with a ha
    have hsq : ((Real.sqrt (2 * a) : ℝ) : ℂ) ^ 2 = 2 * a := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hrec := charlier_recurrence ha0 n ((Real.sqrt (2 * a) : ℂ) * x + a)
    simp only [hf]
    set S : ℂ := ((Real.sqrt (2 * a) : ℝ) : ℂ)
    push_cast
    rw [show S ^ (n + 2) = S ^ n * S ^ 2 by ring, show S ^ (n + 1) = S ^ n * S by ring]
    field_simp
    linear_combination (S ^ n * S ^ 2) * hrec -
      (S * S ^ n * x * charlier (↑a) (n + 1) (S * x + ↑a) +
        S ^ n * (n + 1) * charlier (↑a) n (S * x + ↑a)) * hsq
  · intro n
    rw [aeval_hermitePolyH_succ_succ]
    ring

/-- The map `(fun N : ℕ => hahn (β - 1) (N * (c⁻¹ - 1)) N n x)` tends to `(𝓝 (meixner β c n x))`
along `atTop`. -/
@[dlmf 18.21.E4]
theorem hahn_limit_meixner {β c : ℝ} (hc : 0 < c) (hc1 : c < 1) (n : ℕ) (x : ℂ) :
    Tendsto (fun N : ℕ => hahn (β - 1) (N * (c⁻¹ - 1)) N n x) atTop (𝓝 (meixner β c n x)) := by
  unfold hahn meixner terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  set d : ℝ := c⁻¹ - 1 with hd
  have hd0 : 0 < d := by rw [hd, sub_pos]; exact one_lt_inv₀ hc |>.mpr hc1
  have hNd : Tendsto (fun N : ℕ => (N : ℝ) * d) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hd0
  have h1 := (tendsto_poch_add_div_pow ((n : ℂ) + β) k).comp hNd
  have h2 := (tendsto_poch_neg_div_pow k).inv₀ one_ne_zero
  rw [inv_one] at h2
  simp only [inv_div] at h2
  have := (h1.mul h2).const_mul
    (poch (-(n : ℂ)) k * poch (-x) k / poch (β : ℂ) k / k.factorial * (-(d : ℂ)) ^ k)
  rw [mul_one, mul_one] at this
  have hz : (1 : ℂ) - ((c : ℂ))⁻¹ = -(d : ℂ) := by rw [hd]; push_cast; ring
  rw [hz, show poch (-(n : ℂ)) k * poch (-x) k / poch (β : ℂ) k * (-(d : ℂ)) ^ k /
      (k.factorial : ℂ) = poch (-(n : ℂ)) k * poch (-x) k / poch (β : ℂ) k /
      k.factorial * (-(d : ℂ)) ^ k by ring]
  refine this.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hd' : (d : ℂ) ≠ 0 := ofReal_ne_zero.mpr hd0.ne'
  simp only [Function.comp_apply, ofReal_mul, ofReal_natCast]
  have e1 : (n : ℂ) + (β - 1) + N * (((c⁻¹ : ℝ) : ℂ) - 1) + 1 = (n + β) + N * d := by
    rw [hd]; push_cast; ring
  have e : (-(d : ℂ)) ^ k * (-(N : ℂ)) ^ k = (N : ℂ) ^ k * d ^ k := by
    rw [← mul_pow, ← mul_pow]; ring_nf
  rw [e1, show (β : ℂ) - 1 + 1 = β by ring, one_pow, mul_pow]
  field_simp
  linear_combination (poch (-(n : ℂ)) k * poch (-x) k * poch ((n : ℂ) + β + d * N) k /
    (poch (β : ℂ) k * k.factorial * poch (-(N : ℂ)) k)) * e

/-- The map `(fun c : ℝ => meixner (α + 1) c n (x / (1 - c : ℂ)))` tends to `(𝓝 (laguerrePolyL α n
x / laguerrePolyL α n 0))` along `(𝓝[<] 1)`. -/
@[dlmf 18.21.E8]
theorem meixner_limit_laguerrePolyL {α : ℝ} (hα : -1 < α) (n : ℕ) (x : ℂ) :
    Tendsto (fun c : ℝ => meixner (α + 1) c n (x / (1 - c : ℂ))) (𝓝[<] 1)
      (𝓝 (laguerrePolyL α n x / laguerrePolyL α n 0)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hp : poch ((α : ℂ) + 1) n / n.factorial ≠ 0 :=
    div_ne_zero (poch_ne_zero_of_not_neg_nat hα' n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  have hL : laguerrePolyL α n x / laguerrePolyL α n 0 = kummerM (-n) (α + 1) x := by
    unfold laguerrePolyL
    rw [kummerM_zero, mul_one, mul_div_cancel_left₀ _ hp]
  have key : ∀ (c : ℝ), c ≠ 0 → c ≠ 1 → ∀ k : ℕ,
      poch (-(x / (1 - c : ℂ))) k * (1 - (c : ℂ)⁻¹) ^ k =
        ∏ i ∈ Finset.range k, ((x - i * (1 - c)) / c) := by
    intro c h0 h1 k
    have h0' : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr h0
    have h1' : (1 - c : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h1.symm)
    induction k with
    | zero => simp [poch_zero]
    | succ k ih =>
      rw [poch_succ, Finset.prod_range_succ, ← ih, pow_succ]
      field_simp
      ring
  rw [hL, kummerM_eq_sum_neg_nat]
  unfold meixner terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hprod : Tendsto (fun c : ℝ => ∏ i ∈ Finset.range k, ((x - i * (1 - c)) / c))
      (𝓝[<] 1) (𝓝 (x ^ k)) := by
    have h : Tendsto (fun c : ℝ => ∏ i ∈ Finset.range k, ((x - i * (1 - c)) / c)) (𝓝 1)
        (𝓝 (∏ i ∈ Finset.range k, ((x - i * (1 - ((1 : ℝ) : ℂ))) / ((1 : ℝ) : ℂ)))) := by
      apply tendsto_finsetProd
      intro i _
      exact (ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)).tendsto
    simp only [ofReal_one, sub_self, mul_zero, sub_zero, div_one, Finset.prod_const,
      Finset.card_range] at h
    exact h.mono_left nhdsWithin_le_nhds
  have := hprod.const_mul (poch (-(n : ℂ)) k / (poch ((α : ℂ) + 1) k * k.factorial))
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (lt_mem_nhds zero_lt_one)]
    with c hc1 hc0
  rw [← key c hc0.ne' hc1.ne]
  ring

/-- The map `(fun phi : ℝ => meixnerPollaczek ((α + 1) / 2) phi n (-x / (2 * (phi : ℂ))))` tends
to `(𝓝 (laguerrePolyL α n x))` along `(𝓝[>] 0)`. -/
@[dlmf 18.21.E12]
theorem meixnerPollaczek_limit_laguerrePolyL {α : ℝ} (n : ℕ) (x : ℂ) :
    Tendsto (fun phi : ℝ => meixnerPollaczek ((α + 1) / 2) phi n (-x / (2 * (phi : ℂ))))
      (𝓝[>] 0) (𝓝 (laguerrePolyL α n x)) := by
  have hE0 : Tendsto (fun t : ℝ => 1 - cexp (-2 * I * t)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => 1 - cexp (-2 * I * t)) (𝓝 0)
        (𝓝 (1 - cexp (-2 * I * ((0 : ℝ) : ℂ)))) := Continuous.tendsto (by fun_prop) 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hE1 : Tendsto (fun t : ℝ => (1 - cexp (-2 * I * t)) / t) (𝓝[>] 0) (𝓝 (2 * I)) := by
    have hd := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (-2 * I)).cexp
    have h := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
      (nhdsWithin_mono (s := Set.Ioi (0 : ℝ)) _ fun t (ht : 0 < t) => ht.ne')
    have h' := h.neg
    simp only [id, ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h'
    rw [show -(-2 * I) = 2 * I by ring] at h'
    refine h'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [slope, sub_zero, vsub_eq_sub, Complex.real_smul, ofReal_inv, ofReal_zero,
      mul_zero, Complex.exp_zero]
    ring
  have hexp : Tendsto (fun t : ℝ => cexp (I * n * t)) (𝓝[>] 0) (𝓝 1) := by
    have h : Tendsto (fun t : ℝ => cexp (I * n * t)) (𝓝 0)
        (𝓝 (cexp (I * n * ((0 : ℝ) : ℂ)))) := Continuous.tendsto (by fun_prop) 0
    simpa using h.mono_left nhdsWithin_le_nhds
  unfold meixnerPollaczek laguerrePolyL terminatingHG
  rw [show 2 * (((α : ℂ) + 1) / 2) = α + 1 by ring, kummerM_eq_sum_neg_nat]
  have hpre : Tendsto (fun t : ℝ => poch ((α : ℂ) + 1) n / n ! * cexp (I * n * t)) (𝓝[>] 0)
      (𝓝 (poch ((α : ℂ) + 1) n / n !)) := by
    simpa using (tendsto_const_nhds (x := poch ((α : ℂ) + 1) n / n !)).mul hexp
  refine hpre.mul (tendsto_finsetSum _ fun k _ => ?_)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hfac : ∀ j : ℕ, Tendsto (fun t : ℝ => (((α : ℂ) + 1) / 2 + j) * (1 - cexp (-2 * I * t)) -
      I * x / 2 * ((1 - cexp (-2 * I * t)) / t)) (𝓝[>] 0) (𝓝 x) := by
    intro j
    have h := (hE0.const_mul (((α : ℂ) + 1) / 2 + j)).sub (hE1.const_mul (I * x / 2))
    convert h using 2
    ring_nf
    rw [I_sq]
    ring
  have hprod := (tendsto_finsetProd (Finset.range k) fun j _ => hfac j).const_mul
    (poch (-(n : ℂ)) k / (poch ((α : ℂ) + 1) k * k !))
  rw [Finset.prod_const, Finset.card_range] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
  rw [Finset.prod_congr rfl (g := fun j : ℕ => ((((α : ℂ) + 1) / 2 + I * (-x / (2 * t))) + j) *
    (1 - cexp (-2 * I * t))) (fun j _ => by field_simp; ring), ← poch_mul_pow]
  ring

/-- The map `(fun lam : ℝ => n.factorial * (Real.sqrt lam : ℂ)⁻¹ ^ n * meixnerPollaczek lam
(Real.pi / 2) n (x * Real.sqrt lam))` tends to `(𝓝 (aeval x (hermitePolyH n)))` along `atTop`. -/
@[dlmf 18.21.E13]
theorem meixnerPollaczek_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun lam : ℝ => n.factorial * (Real.sqrt lam : ℂ)⁻¹ ^ n *
      meixnerPollaczek lam (Real.pi / 2) n (x * Real.sqrt lam)) atTop (𝓝 (aeval x (hermitePolyH n))) := by
  have hsc : sin ((Real.pi : ℂ) / 2) = 1 := Complex.sin_pi_div_two
  have hcc : cos ((Real.pi : ℂ) / 2) = 0 := Complex.cos_pi_div_two
  refine tendsto_of_three_term (f := fun n lam => (n ! : ℂ) * (Real.sqrt lam : ℂ)⁻¹ ^ n *
      meixnerPollaczek lam (Real.pi / 2) n (x * Real.sqrt lam))
    (g := fun n => aeval x (hermitePolyH n))
    (A := fun n _ => 2 * x) (B := fun n lam => -((n + 1) * (2 + n / (lam : ℂ))))
    (A' := fun n => 2 * x) (B' := fun n => -((n + 1) * 2)) ?_ ?_ ?_ ?_ ?_ ?_ n
  · simp [meixnerPollaczek, terminatingHG, poch_zero]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with lam hl
    have hs : (Real.sqrt lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hl).ne'
    have hl' : (lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr hl.ne'
    rw [meixnerPollaczek_one hl', hsc, hcc]
    simp only [hermitePolyH_one, map_mul, aeval_X, map_ofNat, Nat.factorial_one, Nat.cast_one]
    field_simp
    ring
  · intro n; exact tendsto_const_nhds
  · intro n
    simpa only [add_zero] using
      (((tendsto_const_div_ofReal_atTop (n : ℂ)).const_add 2).const_mul ((n : ℂ) + 1)).neg
  · intro n
    filter_upwards [eventually_gt_atTop 0] with lam hl
    have hs : (Real.sqrt lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hl).ne'
    have hs2 : (lam : ℂ) = (Real.sqrt lam : ℂ) ^ 2 := by
      rw [← ofReal_pow, Real.sq_sqrt hl.le]
    have hr := meixnerPollaczek_recurrence (lam := lam) (by simpa using hl)
      ((Real.pi : ℂ) / 2) n (x * Real.sqrt lam)
    rw [hsc, hcc, mul_comm x] at hr
    have hf2 : ((n + 2) ! : ℂ) = (n + 2) * (n + 1) * n ! := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    have hf1 : ((n + 1) ! : ℂ) = (n + 1) * n ! := by
      rw [Nat.factorial_succ]; push_cast; ring
    simp only [hf2, hf1, inv_pow]
    rw [hs2] at hr ⊢
    field_simp
    linear_combination ((n ! : ℂ) * (Real.sqrt lam : ℂ) ^ (2 * n + 3)) * hr
  · intro n
    rw [hermitePolyH_succ (n + 1), hermitePolyH_derivative]
    simp only [map_sub, map_mul, aeval_X, aeval_C, map_ofNat]
    push_cast
    ring

/-- Identity under the stated parameter and domain assumptions: `(x + I * star a) * (x + I * star
b) * (continuousHahn a b (star a) (star b) n (x + I) - continuousHahn a b (star a) (star b) n
x) + (x - I * a) * (x - I * b) * (continuousHahn a b (star a) (star b) n (x - I) -
continuousHahn a b (star a) (star b) n x) + n * (n + a + b + star a + star b - 1) *
continuousHahn a b (star a) (star b) n x = 0`. -/
@[dlmf 18.22.E14]
theorem continuousHahn_difference_equation {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (n : ℕ) (x : ℂ) :
    (x + I * star a) * (x + I * star b) *
      (continuousHahn a b (star a) (star b) n (x + I) - continuousHahn a b (star a) (star b) n x) +
    (x - I * a) * (x - I * b) *
      (continuousHahn a b (star a) (star b) n (x - I) - continuousHahn a b (star a) (star b) n x) +
    n * (n + a + b + star a + star b - 1) * continuousHahn a b (star a) (star b) n x = 0 := by
  set c : ℂ := star a with hcdef
  set d : ℂ := star b with hddef
  have hAre : 0 < (a + c).re := by simp [hcdef]; linarith
  have hDre : 0 < (a + d).re := by simp [hddef]; linarith
  have hpA : ∀ k : ℕ, poch (a + c) k ≠ 0 := fun k => poch_ne_zero_of_re_pos hAre k
  have hpD : ∀ k : ℕ, poch (a + d) k ≠ 0 := fun k => poch_ne_zero_of_re_pos hDre k
  have hAk : ∀ k : ℕ, a + c + k ≠ 0 := fun k h => by
    have := congrArg re h; simp only [add_re, natCast_re, zero_re] at this hAre
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hDk : ∀ k : ℕ, a + d + k ≠ 0 := fun k h => by
    have := congrArg re h; simp only [add_re, natCast_re, zero_re] at this hDre
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  clear_value c d
  set s : ℂ := (n : ℂ) + a + b + c + d - 1 with hs
  set w : ℂ := a + I * x with hw
  set cf : ℕ → ℂ := fun k => poch (-(n : ℂ)) k * poch s k / (poch (a + c) k * poch (a + d) k) /
    k ! with hcf
  set G : ℕ → ℂ := fun k => cf k * ((n - k) * (n + k + a + b + c + d - 1) * poch w k) with hG
  set B : ℕ → ℂ := fun k => -((w - a - c) * (w - a - d)) * (poch (w - 1) k - poch w k) -
      w * (w - a + b) * (poch (w + 1) k - poch w k) +
      n * (n + a + b + c + d - 1) * poch w k with hB
  have hrec : ∀ k : ℕ, cf (k + 1) * ((k + 1) * (a + c + k) * (a + d + k)) =
      cf k * ((k - n) * (s + k)) := by
    intro k
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
    have := hpA k; have := hpD k; have := hAk k; have := hDk k
    simp only [hcf]
    rw [poch_succ, poch_succ s, poch_succ (a + c), poch_succ (a + d), Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have htel : ∀ k : ℕ, cf (k + 1) * B (k + 1) = G (k + 1) - G k := by
    intro k
    simp only [hB, hG]
    rw [ch_basis_succ a b c d w n k]
    have hr := hrec k
    push_cast
    linear_combination (poch w k) * hr
  have hkey : ∑ k ∈ Finset.range (n + 1), cf k * B k = 0 := by
    rw [Finset.sum_range_succ']
    simp_rw [htel]
    rw [Finset.sum_range_sub]
    simp only [hB, hG, hcf, poch_zero, sub_self]
    push_cast
    ring
  unfold continuousHahn terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  rw [show a + I * (x + I) = w - 1 by rw [hw]; linear_combination I_sq,
    show a + I * (x - I) = w + 1 by rw [hw]; linear_combination -I_sq,
    show (x + I * c) * (x + I * d) = -((w - a - c) * (w - a - d)) by
      rw [hw]; linear_combination (x ^ 2 + c * d) * I_sq,
    show (x - I * a) * (x - I * b) = -(w * (w - a + b)) by
      rw [hw]; linear_combination (x ^ 2 + a * b) * I_sq]
  have hfin : ∀ v : ℂ, ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
      (poch ((n : ℂ) + a + b + c + d - 1) k * poch v k) / (poch (a + c) k * poch (a + d) k) /
        (k ! : ℂ) = ∑ k ∈ Finset.range (n + 1), cf k * poch v k := fun v =>
    Finset.sum_congr rfl fun k _ => by simp only [hcf, hs]; ring
  rw [hfin, hfin, hfin, ← hw]
  clear_value B G cf w s
  have hexp : ∑ k ∈ Finset.range (n + 1), cf k * B k =
      -((w - a - c) * (w - a - d)) * (∑ k ∈ Finset.range (n + 1), cf k * poch (w - 1) k -
        ∑ k ∈ Finset.range (n + 1), cf k * poch w k) -
      w * (w - a + b) * (∑ k ∈ Finset.range (n + 1), cf k * poch (w + 1) k -
        ∑ k ∈ Finset.range (n + 1), cf k * poch w k) +
      n * (n + a + b + c + d - 1) * ∑ k ∈ Finset.range (n + 1), cf k * poch w k := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hB]
    ring
  rw [hkey] at hexp
  linear_combination (-(I ^ n * poch (a + c) n * poch (a + d) n / n !)) * hexp +
    (I ^ n * poch (a + c) n * poch (a + d) n / n ! * n *
      ∑ k ∈ Finset.range (n + 1), cf k * poch w k) * hs

/-- Identity under the stated parameter and domain assumptions: `exp (I * phi) * (x + I * lam) *
(meixnerPollaczek lam phi n (x + I) - meixnerPollaczek lam phi n x) + exp (-I * phi) * (x - I
* lam) * (meixnerPollaczek lam phi n (x - I) - meixnerPollaczek lam phi n x) + 2 * n * sin phi
* meixnerPollaczek lam phi n x = 0`. -/
@[dlmf 18.22.E17]
theorem meixnerPollaczek_difference_equation {lam : ℂ} (hlam : 0 < lam.re) (phi : ℂ) (n : ℕ) (x : ℂ) :
    exp (I * phi) * (x + I * lam) * (meixnerPollaczek lam phi n (x + I) - meixnerPollaczek lam phi n x) +
    exp (-I * phi) * (x - I * lam) * (meixnerPollaczek lam phi n (x - I) - meixnerPollaczek lam phi n x) +
    2 * n * sin phi * meixnerPollaczek lam phi n x = 0 := by
  have hp : ∀ k : ℕ, poch (2 * lam) k ≠ 0 := fun k => poch_ne_zero_of_re_pos (by simp; linarith) k
  have h2k : ∀ k : ℕ, 2 * lam + k ≠ 0 := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set z : ℂ := 1 - exp (-2 * I * phi) with hz
  set w : ℂ := lam + I * x with hw
  set c : ℕ → ℂ := fun k => poch (-(n : ℂ)) k / poch (2 * lam) k * z ^ k / k ! with hc
  set G : ℕ → ℂ := fun k => c k * (2 * (n - k) * sin phi * poch w k) with hG
  have hS := exp_mul_one_sub_exp phi
  -- the coefficient recurrence
  have hrec : ∀ k : ℕ, c (k + 1) * ((k + 1) * (k + 2 * lam)) = c k * ((k - n) * z) := by
    intro k
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
    have := hp k; have := h2k k
    simp only [hc]
    rw [poch_succ, poch_succ, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
    ring
  -- the basis action, telescoped
  set B : ℕ → ℂ := fun k => exp (I * phi) * (-I * (w - 2 * lam)) * (poch (w - 1) k - poch w k) +
      exp (-I * phi) * (-I * w) * (poch (w + 1) k - poch w k) + 2 * n * sin phi * poch w k with hB
  have htel : ∀ k : ℕ, c (k + 1) * B (k + 1) = G (k + 1) - G k := by
    intro k
    simp only [hB, hG]
    rw [mp_basis_succ lam phi w n k]
    have hr := hrec k
    have hz' : I * (exp (I * phi) * z) = -2 * sin phi := by
      rw [hz, hS]; linear_combination (2 * sin phi) * I_sq
    push_cast
    linear_combination (-(I * exp (I * phi) * poch w k)) * hr +
      (c k * (n - k) * poch w k) * hz'
  have hkey : ∑ k ∈ Finset.range (n + 1), c k * B k = 0 := by
    rw [Finset.sum_range_succ']
    simp_rw [htel]
    rw [Finset.sum_range_sub]
    simp only [hB, hG, hc, poch_zero, sub_self]
    push_cast
    ring
  unfold meixnerPollaczek terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [show lam + I * (x + I) = w - 1 by rw [hw]; linear_combination I_sq,
    show lam + I * (x - I) = w + 1 by rw [hw]; linear_combination -I_sq,
    show x + I * lam = -I * (w - 2 * lam) by rw [hw]; linear_combination x * I_sq,
    show x - I * lam = -I * w by rw [hw]; linear_combination x * I_sq]
  have hfin : ∀ v : ℂ, ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k * poch v k / poch (2 * lam) k *
      z ^ k / (k ! : ℂ) = ∑ k ∈ Finset.range (n + 1), c k * poch v k := fun v =>
    Finset.sum_congr rfl fun k _ => by simp only [hc]; ring
  rw [hfin, hfin, hfin, ← hw]
  clear_value B G c w z
  have hexp : ∑ k ∈ Finset.range (n + 1), c k * B k =
      exp (I * phi) * (-I * (w - 2 * lam)) * (∑ k ∈ Finset.range (n + 1), c k * poch (w - 1) k -
        ∑ k ∈ Finset.range (n + 1), c k * poch w k) +
      exp (-I * phi) * (-I * w) * (∑ k ∈ Finset.range (n + 1), c k * poch (w + 1) k -
        ∑ k ∈ Finset.range (n + 1), c k * poch w k) +
      2 * n * sin phi * ∑ k ∈ Finset.range (n + 1), c k * poch w k := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hB]
    ring
  rw [hkey] at hexp
  linear_combination (-(poch (2 * lam) n / n ! * exp (I * n * phi))) * hexp

/-- Identity under the stated parameter and domain assumptions: `(continuousHahn a b c d (n + 1)
(x + I / 2) - continuousHahn a b c d (n + 1) (x - I / 2)) / I = (n + a + b + c + d) *
continuousHahn (a + 1 / 2) (b + 1 / 2) (c + 1 / 2) (d + 1 / 2) n x`. -/
@[dlmf 18.22.E27]
theorem continuousHahn_central_difference {a b c d : ℂ} (hac : 0 < (a + c).re) (had : 0 < (a + d).re) (n : ℕ) (x : ℂ) :
    (continuousHahn a b c d (n + 1) (x + I / 2) - continuousHahn a b c d (n + 1) (x - I / 2)) / I =
      (n + a + b + c + d) * continuousHahn (a + 1 / 2) (b + 1 / 2) (c + 1 / 2) (d + 1 / 2) n x := by
  have h0 : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h] at hz; simp at hz
  have hp : ∀ (z : ℂ) (k : ℕ), 0 < z.re → poch (z + 1) k ≠ 0 := fun z k hz =>
    poch_ne_zero_of_re_pos (by simp; linarith) k
  unfold continuousHahn terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [poch_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, sub_self, add_zero]
  rw [show a + I * (x + I / 2) = (a + I * x) - 1 / 2 by linear_combination (1 / 2 : ℂ) * I_sq,
    show a + I * (x - I / 2) = (a + I * x) + 1 / 2 by linear_combination (-1 / 2 : ℂ) * I_sq]
  rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have key := poch_half_sub (a + I * x) k
  rw [← sub_div, ← sub_div, ← mul_sub, ← mul_sub, key]
  rw [poch_succ_left (a + c), poch_succ_left (a + d),
    poch_succ_left (a + c) k, poch_succ_left (a + d) k,
    poch_succ_left (-((n + 1 : ℕ) : ℂ)), poch_succ_left (((n + 1 : ℕ) : ℂ) + a + b + c + d - 1),
    Nat.factorial_succ, Nat.factorial_succ,
    show a + 1 / 2 + (c + 1 / 2) = a + c + 1 by ring, show a + 1 / 2 + (d + 1 / 2) = a + d + 1 by ring,
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring,
    show ((n + 1 : ℕ) : ℂ) + a + b + c + d - 1 + 1 = (n : ℂ) + (a + 1 / 2) + (b + 1 / 2) +
      (c + 1 / 2) + (d + 1 / 2) - 1 by push_cast; ring,
    show a + I * x + 1 / 2 = a + 1 / 2 + I * x by ring, pow_succ]
  have := h0 _ hac; have := h0 _ had
  have := hp _ k hac; have := hp _ k had
  have := hp _ n hac; have := hp _ n had
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  push_cast
  field_simp
  ring

/-- Continuous Hahn coefficients are a convolution of two Kummer coefficient sequences. -/
theorem continuousHahn_coeff_convolution {a b c d : ℂ}
    (hac : 0 < (a + c).re) (had : 0 < (a + d).re) (hbd : 0 < (b + d).re)
    (x : ℂ) (n : ℕ) :
    continuousHahn a b c d n x / (poch (a + c) n * poch (b + d) n) =
      ∑ k ∈ Finset.range (n + 1),
        (kummerMCoeff (a + I * x) (a + c) k * (-I) ^ k) *
        (kummerMCoeff (d - I * x) (b + d) (n - k) * I ^ (n - k)) := by
  have hR := poch_ne_zero_of_re_pos hac
  have hD := poch_ne_zero_of_re_pos had
  have hT := poch_ne_zero_of_re_pos hbd
  have ht := terminating_3F2_convolution (a + I * x) (n + a + b + c + d - 1)
    (a + c) (a + d) hR n
  rw [show a + c - (n + a + b + c + d - 1) = 1 - (b + d) - n by ring,
    show a + d - (a + I * x) = d - I * x by ring] at ht
  have he : continuousHahn a b c d n x / (poch (a + c) n * poch (b + d) n) =
      I ^ n / (poch (b + d) n * n !) *
      ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * n.choose k * poch (a + I * x) k *
        poch (n + a + b + c + d - 1) k / poch (a + c) k * poch (a + d + k) (n - k) := by
    unfold continuousHahn terminatingHG
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
    rw [mul_div_assoc, Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by simpa using hk
    rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
    have hp : poch (a + d) n = poch (a + d) k * poch (a + d + k) (n - k) := by
      rw [← poch_add, Nat.add_sub_cancel' hk']
    rw [hp]
    push_cast
    field_simp [hR n, hR k, hD k, hT n, Nat.cast_ne_zero.mpr k.factorial_ne_zero]
  rw [he, ht, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using hk
  have hp := poch_eq_poch_sub_mul (b + d) hk'
  have hf : (n.choose k : ℂ) * k ! * (n - k)! = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk'
  have hi : I ^ n = I ^ k * I ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hk']
  have hs : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hkf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hnk : ((n - k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  have hpn : poch (1 - (b + d) - n) k = (-1) ^ k * poch (b + d) n / poch (b + d) (n-k) := by
    apply (eq_div_iff (hT (n-k))).2
    rw [hp]
    linear_combination -(poch (b+d) (n-k) * poch (1-(b+d)-n) k) * hs
  dsimp only [kummerMCoeff]
  rw [neg_pow, hi, hpn, ← hf]
  have hc : (n.choose k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hk').ne'
  field_simp [hR k, hT n, hT (n-k), hn, hkf, hnk, hc]

/-- The series with terms `(fun n : ℕ => continuousHahn a b (star a) (star b) n x / (poch (a +
star a) n * poch (b + star b) n) * z ^ n)` converges to `(kummerM (a + I * x) (a + star a) (-I
* z) * kummerM (star b - I * x) (b + star b) (I * z))`. -/
@[dlmf 18.23.E6]
theorem continuousHahn_generating_function {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (x z : ℂ) :
    HasSum (fun n : ℕ => continuousHahn a b (star a) (star b) n x /
      (poch (a + star a) n * poch (b + star b) n) * z ^ n)
      (kummerM (a + I * x) (a + star a) (-I * z) * kummerM (star b - I * x) (b + star b) (I * z)) := by
  have hac : 0 < (a + star a).re := by simp; linarith
  have had : 0 < (a + star b).re := by simp; linarith
  have hbd : 0 < (b + star b).re := by simp; linarith
  have hs1 := hasSum_kummerM (a := a + I * x) (not_neg_nat_of_re_pos hac) (-I * z)
  have hs2 := hasSum_kummerM (a := star b - I * x) (not_neg_nat_of_re_pos hbd) (I * z)
  have h1 : HasSum (fun n => (kummerMCoeff (a + I * x) (a + star a) n * (-I) ^ n) * z ^ n)
      (kummerM (a + I * x) (a + star a) (-I * z)) := by
    simpa only [mul_pow, mul_assoc] using hs1
  have h2 : HasSum (fun n => (kummerMCoeff (star b - I * x) (b + star b) n * I ^ n) * z ^ n)
      (kummerM (star b - I * x) (b + star b) (I * z)) := by
    simpa only [mul_pow, mul_assoc] using hs2
  have h := hasSum_coefficient_convolution h1 h2
  apply h.congr_fun
  intro n
  rw [continuousHahn_coeff_convolution hac had hbd]

end DLMF.OrthogonalPolynomials
end
end
