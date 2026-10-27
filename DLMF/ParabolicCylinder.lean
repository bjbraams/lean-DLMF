/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.ParabolicCylinder.Weber
public import DLMF.ParabolicCylinder.Integrals
public import DLMF.ParabolicCylinder.AsymptoticsZeros
public import DLMF.ParabolicCylinder.SectorAsymptotics
public import DLMF.ParabolicCylinder.Uniform
public import DLMF.ParabolicCylinder.UniformLG
public import DLMF.ParabolicCylinder.UniformLG2
public import DLMF.ParabolicCylinder.IntegralTools
public import DLMF.ParabolicCylinder.TurningPoint
public import DLMF.ParabolicCylinder.WeberUniform
public import DLMF.ParabolicCylinder.Computation
public import DLMF.ParabolicCylinder.SourceChecks
public import DLMF.ParabolicCylinder.Hermite
public import DLMF.ParabolicCylinder.BarnesContinuation
public import DLMF.ParabolicCylinder.Basic
public import DLMF.ParabolicCylinder.Relations
public import DLMF.ParabolicCylinder.MathlibCoverage
public import DLMF.ParabolicCylinder.ContourTools

/-!
# Parabolic cylinder U/V/D and oscillatory W functions

DLMF statement acquisition and first proofs. The original cylinder theory is
in `DLMF.Confluent.ParabolicCylinder`. Coverage, source qualifications and
remaining admissions are documented in `DLMF111214Acquisition.md`.
-/
