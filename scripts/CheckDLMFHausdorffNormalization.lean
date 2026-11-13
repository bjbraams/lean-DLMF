/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Calculus.Vectors
public import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Analysis.InnerProductSpace.NormDet
import TauCeti.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Real.Pi.Bounds

open Set MeasureTheory
open scoped Matrix

public section

namespace DLMF.AlgebraicAnalytic

/-- Euclidean Hausdorff measure gives the usual parallelogram area. -/
theorem euclideanHausdorffMeasure_parallelogram (a b : Fin 3 → ℝ) :
    Measure.euclideanHausdorffMeasure 2
        ((fun st : ℝ × ℝ => (WithLp.toLp 2 (st.1 • a + st.2 • b) :
          EuclideanSpace ℝ (Fin 3))) '' (Icc 0 1 ×ˢ Icc 0 1)) =
      ENNReal.ofReal (vecNorm (a ⨯₃ b)) := by
  exact hausdorffMeasure_parallelogram a b

/-- Raw two-dimensional Hausdorff measure differs from the Euclidean area normalization. -/
theorem not_forall_rawHausdorffMeasure_parallelogram :
    ¬ (∀ a b : Fin 3 → ℝ,
      Measure.hausdorffMeasure 2
        ((fun st : ℝ × ℝ => (WithLp.toLp 2 (st.1 • a + st.2 • b) :
          EuclideanSpace ℝ (Fin 3))) '' (Icc 0 1 ×ˢ Icc 0 1)) =
        ENNReal.ofReal (vecNorm (a ⨯₃ b))) := by
  intro hall
  let a : Fin 3 → ℝ := Pi.single 0 1
  let b : Fin 3 → ℝ := Pi.single 1 1
  let P : Set (EuclideanSpace ℝ (Fin 3)) :=
    (fun st : ℝ × ℝ => WithLp.toLp 2 (st.1 • a + st.2 • b)) '' (Icc 0 1 ×ˢ Icc 0 1)
  have hn : ENNReal.ofReal (vecNorm (a ⨯₃ b)) = 1 := by
    norm_num [a, b, vecNorm, dotProduct, cross_apply, Fin.sum_univ_three, Pi.single_apply]
  have hraw : Measure.hausdorffMeasure 2 P = 1 := (hall a b).trans hn
  have harea : Measure.euclideanHausdorffMeasure 2 P = 1 :=
    (euclideanHausdorffMeasure_parallelogram a b).trans hn
  have hc := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 3)) => μ P)
    (TauCeti.euclideanHausdorffMeasure_eq_smul_hausdorffMeasure 2)
  have hball : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) =
      ENNReal.ofReal Real.pi := by
    rw [EuclideanSpace.volume_ball]
    norm_num [Real.sq_sqrt Real.pi_pos.le, Real.Gamma_nat_eq_factorial]
  simp only [smul_apply, smul_eq_mul, Nat.cast_two] at hc
  rw [hraw, harea, hball, mul_one] at hc
  have he := congrArg ENNReal.toReal hc
  norm_num [ENNReal.toReal_div, Real.pi_pos.le] at he
  linarith [Real.pi_lt_four]

#print axioms euclideanHausdorffMeasure_parallelogram
#print axioms not_forall_rawHausdorffMeasure_parallelogram
end DLMF.AlgebraicAnalytic
