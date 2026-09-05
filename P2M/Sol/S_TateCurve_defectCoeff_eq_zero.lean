module

import P2M.Sol.S_TateCurve_lineCoeff_eq_zero
import P2M.Util
public import Definitions.Def_TateCurve_Defect

namespace P2MW.S_TateCurve_defectCoeff_eq_zero

open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) {N : ℕ} (hN : 0 < N) :
    defectCoeff u N = 0 :=
  defectCoeff_eq_zero_of_lineCoeff_eq_zero hu0 hu1 hN fun k hk =>
    TateCurve.lineCoeff_eq_zero N k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
end S_TateCurve_defectCoeff_eq_zero
end P2MW

public section
attribute [-simp] TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero

open TateCurve
open scoped NNReal
theorem TateCurve.defectCoeff_eq_zero {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) {N : ℕ} (hN : 0 < N) : defectCoeff u N = 0 := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_defectCoeff_eq_zero.solution
end
