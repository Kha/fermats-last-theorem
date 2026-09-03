import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap
    (K K' : Type*) [Field K] [Field K'] (ι : K →+* K') (Γ : Subgroup SL(2, ℤ)) :
    (∀ x ∈ qExpFunctionFieldC K Γ, coeffMap ι x ∈ qExpFunctionFieldC K' Γ) ∧
    qExpFunctionFieldC K' Γ =
      IntermediateField.adjoin K' (coeffMap ι '' (qExpFunctionFieldC K Γ : Set (LaurentSeries K))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap.solution
