import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap
    {k₀ k : Type*} [Field k₀] [Field k] (σ : k₀ →+* k) (Γ : Subgroup SL(2, ℤ)) :
    ∃ ι : ↥(ModularCurve.qExpFunctionFieldC k₀ Γ) →+* ↥(ModularCurve.qExpFunctionFieldC k Γ),
      ∀ x : ↥(ModularCurve.qExpFunctionFieldC k₀ Γ),
        ((ι x : ↥(ModularCurve.qExpFunctionFieldC k Γ)) : LaurentSeries k) = coeffMap σ (x : LaurentSeries k₀) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap.solution
