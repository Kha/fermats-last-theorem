import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_complexPlaceDictionaryOf
attribute [-simp] ModularCurve.jqNModC_one

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_complexPlaceDictionaryOf
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ) :
    Nonempty (ModularCurve.ComplexPlaceDictionaryOf Γ F₀) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_complexPlaceDictionaryOf.solution
