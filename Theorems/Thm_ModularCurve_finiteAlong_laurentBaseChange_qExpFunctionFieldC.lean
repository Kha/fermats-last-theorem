import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_ModularCurve_finiteAlong_laurentBaseChange_qExpFunctionFieldC

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.finiteAlong_laurentBaseChange_qExpFunctionFieldC (L : Type*) [Field L] [Algebra ℚ L]
    {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} [Γ.FiniteIndex] [Γ'.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) (hT' : ModularGroup.T ∈ Γ')
    (φ : laurentBaseChange L (qExpFunctionFieldC ℚ Γ) →ₐ[L] laurentBaseChange L (qExpFunctionFieldC ℚ Γ')) :
    FiniteAlong L φ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finiteAlong_laurentBaseChange_qExpFunctionFieldC.solution
