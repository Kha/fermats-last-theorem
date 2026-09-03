import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_of_coeffMap_mem_adjoin_image_of_ringHom

set_option autoImplicit false

theorem ModularCurve.mem_of_coeffMap_mem_adjoin_image_of_ringHom
    {K L : Type*} [Field K] [Field L] (ι : K →+* L) (F : IntermediateField K (LaurentSeries K))
    (x : LaurentSeries K)
    (hx : ModularCurve.coeffMap ι x ∈
      IntermediateField.adjoin L (ModularCurve.coeffMap ι '' (F : Set (LaurentSeries K)))) :
    x ∈ F := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_of_coeffMap_mem_adjoin_image_of_ringHom.solution
