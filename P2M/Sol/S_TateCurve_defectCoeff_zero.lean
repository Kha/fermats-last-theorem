module

public import Definitions.Def_TateCurve_Defect
import P2M.Sol.S_TateCurve_nodal_xfun_yfun
import P2M.Util
public import Mathlib

namespace P2MW.S_TateCurve_defectCoeff_zero
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {u : K} (hu1 : u ≠ 1) : defectCoeff u 0 = 0 := by
  have hnodal := TateCurve.nodal_xfun_yfun (K := K) (w := u) hu1
  simp only [defectCoeff, cauchyMul_zero, xCoeffFull_zero, yCoeffFull_zero, a₄Coeff_zero,
    a₆Coeff_zero, zero_mul, add_zero]
  linear_combination hnodal
end S_TateCurve_defectCoeff_zero
end P2MW

public section
open TateCurve
open scoped NNReal
theorem TateCurve.defectCoeff_zero {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu1 : u ≠ 1) : defectCoeff u 0 = 0 := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_defectCoeff_zero.solution
end
