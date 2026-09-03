import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_KeystoneVocab
import P2M.Util
import P2M.Sol.S_TateCurve_symAdd_sum_regional
attribute [-simp] WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero

theorem TateCurve.symAdd_sum_regional {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] {q : K} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    ∀ u' v' : K, TateCurve.ExpansionRegion q u' v' →
      (TateCurve.pointX q (u' * v') + TateCurve.pointX q (u' * v'⁻¹)) * (TateCurve.pointX q u' - TateCurve.pointX q v') ^ 2 =
        TateCurve.symSumNum q (TateCurve.pointX q u') (TateCurve.pointX q v') := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_symAdd_sum_regional.solution
