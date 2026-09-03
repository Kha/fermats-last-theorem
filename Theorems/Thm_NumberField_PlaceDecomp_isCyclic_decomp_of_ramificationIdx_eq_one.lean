import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_isCyclic_decomp_of_ramificationIdx_eq_one

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.isCyclic_decomp_of_ramificationIdx_eq_one (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (w : HeightOneSpectrum (𝓞 K))
    (hw : (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1) :
    IsCyclic (NumberField.PlaceDecomp.decomp E K w) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_isCyclic_decomp_of_ramificationIdx_eq_one.solution
