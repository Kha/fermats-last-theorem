import Mathlib
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow
attribute [-simp] ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut

set_option autoImplicit false

open AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [PerfectField K] (Γ : Subgroup SL(2, ℤ))
    (f : ModularCurve.qExpFunctionFieldC K Γ) :
    ModularCurve.qExpFrobeniusModL K Γ p f = ((ModularCurve.qExpArithFrobC p K Γ)⁻¹ • f) ^ p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow.solution
