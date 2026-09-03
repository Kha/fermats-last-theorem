import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ

set_option autoImplicit false
open scoped MatrixGroups in

theorem ModularForm.levelOne_qExpansion_coeff_mem_of_coeff_le_mem (N : ℕ)
    (F : ModularForm 𝒮ℒ (12 * (N : ℤ))) (R : Subring ℂ)
    (hF : ∀ n ≤ N, (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈ R) (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈ R := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem.solution
