import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_fullKernelQuotient_j_eq_zero_of_j_eq_zero_of_ringChar
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one

theorem WeierstrassCurve.fullKernelQuotient_j_eq_zero_of_j_eq_zero_of_ringChar
    {K : Type*} [Field K] [DecidableEq K] (hK : ringChar K = 2 ∨ ringChar K = 3)
    {N : ℕ} [NeZero N] (W : WeierstrassCurve K) [W.IsElliptic] (hj : W.j = 0)
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0) :
    @WeierstrassCurve.j K _ (W.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩ = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_fullKernelQuotient_j_eq_zero_of_j_eq_zero_of_ringChar.solution
