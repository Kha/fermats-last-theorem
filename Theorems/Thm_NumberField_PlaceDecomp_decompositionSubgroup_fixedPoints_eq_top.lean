import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_decompositionSubgroup_fixedPoints_eq_top

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp
theorem NumberField.PlaceDecomp.decompositionSubgroup_fixedPoints_eq_top (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) [Finite (NumberField.PlaceDecomp.decomp E K w)] :
    (w.adicCompletionIntegers K).decompositionSubgroup (FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_decompositionSubgroup_fixedPoints_eq_top.solution
