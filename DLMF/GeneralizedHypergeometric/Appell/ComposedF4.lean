/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Appell.SeriesAndDifferentialEquations

/-!
# The binomially expanded composed Appell F4 series

The substitution `(X,Y) ↦ (X(1-Y),Y(1-X))` produces an absolutely summable four-index
family near the origin. Summing its finite binomial fibers recovers the defining F4
series. The estimates hold at all regular lower parameters, including parameters with
negative real parts.

* `exists_norm_appellF4Coeff_le_geom`: a geometric coefficient bound.
* `summable_appellF4Family`: absolute convergence of the expanded series.
* `hasSum_appellF4Family_fst`: the finite binomial fibers.
-/

public noncomputable section
open Complex Filter Set
open scoped Topology Nat
namespace DLMF.Hypergeometric

/-- A geometric bound for the F4 coefficients at regular lower parameters. -/
lemma exists_norm_appellF4Coeff_le_geom (a b c c' : ℂ) (hc : AppellRegular c)
    (hc' : AppellRegular c') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m n : ℕ, ‖appellF4Coeff a b c c' m n‖ ≤ C * (8 ^ m * 8 ^ n) := by
  obtain ⟨C, hC⟩ := exists_norm_appellF4Coeff_le a b c c' hc hc' (σ := 2) (by norm_num)
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC (0, 0))
    simpa using this
  refine ⟨C, hC0, fun m n => (hC (m, n)).trans ?_⟩
  have h1 : (((m + n).choose m : ℕ) : ℝ) ≤ 2 ^ (m + n) := by
                                                            exact_mod_cast Nat.choose_le_two_pow _ _
  calc C * 2 ^ (m + n) * (((m + n).choose m : ℕ) : ℝ) ^ 2 ≤ C * 2 ^ (m + n) *
         (2 ^ (m + n)) ^ 2 := by
        gcongr
    _ = C * (8 ^ m * 8 ^ n) := by
        have : (8:ℝ) ^ m * 8 ^ n = (2 ^ (m + n)) ^ 3 := by
          rw [← pow_add, show (8:ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
        rw [this]; ring

/-- Summing the four-index family `appellF4Family` over its last two indices gives the `(m, n)`
term `c_{mn} (X(1-Y))ᵐ (Y(1-X))ⁿ` of the `F₄` double series. -/
lemma hasSum_appellF4Family_fst (a b c c' X Y : ℂ) (p : ℕ × ℕ) :
    HasSum (fun q => appellF4Family a b c c' X Y (p, q))
      (appellF4Coeff a b c c' p.1 p.2 * (X * (1 - Y)) ^ p.1 * (Y * (1 - X)) ^ p.2) := by
  obtain ⟨m, n⟩ := p
  have hfin := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
    (s := Finset.range (m + n + 1) ×ˢ Finset.range (m + n + 1))
    (f := fun q => appellF4Family a b c c' X Y ((m, n), q)) (fun q hq => by
      obtain ⟨M, N⟩ := q
      simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hq
      unfold appellF4Family
      simp only
      rcases hq with h | h
      · rw [appellF4BinomialCoeff_eq_zero_of_lt (by omega)]; simp
      · rw [appellF4BinomialCoeff_eq_zero_of_lt (m := n) (n := m) (by omega)]; simp)
  convert hfin using 1
  rw [Finset.sum_product]
  simp only [appellF4Family]
  have h1 := appellF4BinomialCoeff_sum m n X
  have h2 := appellF4BinomialCoeff_sum n m Y
  rw [show n + m + 1 = m + n + 1 by ring] at h2
  have : ∑ x ∈ Finset.range (m + n + 1), ∑ y ∈ Finset.range (m + n + 1),
      appellF4Coeff a b c c' m n * (appellF4BinomialCoeff m n x * X ^ x) *
          (appellF4BinomialCoeff n m y * Y ^ y) =
      appellF4Coeff a b c c' m n *
          ((∑ x ∈ Finset.range (m + n + 1), appellF4BinomialCoeff m n x * X ^ x) *
        (∑ y ∈ Finset.range (m + n + 1), appellF4BinomialCoeff n m y * Y ^ y)) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [this, h1, h2]
  simp only [mul_pow]
  ring

/-- The binomially expanded composed F4 series converges absolutely on a small bidisc. -/
lemma summable_appellF4Family (a b c c' : ℂ) (hc : AppellRegular c)
    (hc' : AppellRegular c') {X Y : ℂ} (hX : ‖X‖ < 1 / 1024) (hY : ‖Y‖ < 1 / 1024) :
    Summable (appellF4Family a b c c' X Y) := by
  obtain ⟨C, hC0, hCb⟩ := exists_norm_appellF4Coeff_le_geom a b c c' hc hc'
  have hsq : ∀ W : ℂ, ‖W‖ < 1 / 1024 → Real.sqrt ‖W‖ < 1 / 32 := by
    intro W hW
    rw [show (1 / 32 : ℝ) = Real.sqrt (1 / 1024) by
      rw [show (1 / 1024 : ℝ) = (1 / 32) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] ]
    exact Real.sqrt_lt_sqrt (norm_nonneg _) hW
  have hX1 : ‖X‖ ≤ 1 := by linarith
  have hY1 : ‖Y‖ ≤ 1 := by linarith
  set sX := Real.sqrt ‖X‖
  set sY := Real.sqrt ‖Y‖
  have hsX0 : 0 ≤ sX := Real.sqrt_nonneg _
  have hsY0 : 0 ≤ sY := Real.sqrt_nonneg _
  have hsXQ : sX < 1 / 32 := hsq X hX
  have hsYQ : sY < 1 / 32 := hsq Y hY
  have hsX1 : sX < 1 := by linarith
  have hsY1 : sY < 1 := by linarith
  set rX := 2 * 8 * sX with hrX
  set rY := 2 * 8 * sY with hrY
  have hrX0 : 0 ≤ rX := by positivity
  have hrY0 : 0 ≤ rY := by positivity
  have hrX1 : rX < 1 := by rw [hrX]; linarith
  have hrY1 : rY < 1 := by rw [hrY]; linarith
  have hgeo : ∀ u v : ℝ, 0 ≤ u → u < 1 → 0 ≤ v → v < 1 →
      Summable fun p : ℕ × ℕ => u ^ p.1 * v ^ p.2 := fun u v hu0 hu1 hv0 hv1 =>
    (summable_geometric_of_lt_one hu0 hu1).mul_of_nonneg (summable_geometric_of_lt_one hv0 hv1)
      (fun _ => by positivity) (fun _ => by positivity)
  have hD : Summable fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      C * ((rX ^ p.1.1 * rY ^ p.1.2) * (sX ^ p.2.1 * sY ^ p.2.2)) :=
    ((hgeo rX rY hrX0 hrX1 hrY0 hrY1).mul_of_nonneg (hgeo sX sY hsX0 hsX1 hsY0 hsY1)
      (fun _ => by positivity) (fun _ => by positivity)).mul_left C
  have hsum : Summable (appellF4Family a b c c' X Y) := by
    refine Summable.of_norm_bounded hD fun p => ?_
    obtain ⟨⟨m, n⟩, ⟨M, N⟩⟩ := p
    unfold appellF4Family
    simp only
    rw [norm_mul, norm_mul]
    have h1 := hCb m n
    have h2 := appellF4BinomialCoeff_norm_le m n M hX1
    have h3 := appellF4BinomialCoeff_norm_le n m N hY1
    calc ‖appellF4Coeff a b c c' m n‖ * ‖appellF4BinomialCoeff m n M * X ^ M‖ *
           ‖appellF4BinomialCoeff n m N * Y ^ N‖
        ≤ (C * (8 ^ m * 8 ^ n)) * (2 ^ n * sX ^ m * sX ^ M) * (2 ^ m * sY ^ n * sY ^ N) := by
          gcongr
      _ = _ := by rw [hrX, hrY]; simp only [mul_pow]; ring
  exact hsum

end DLMF.Hypergeometric
