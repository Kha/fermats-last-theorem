import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le
    (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K]
    (E E' : IntermediateField k (LaurentSeries k)) (hEE' : E ≤ E')
    (hfin : 0 < IntermediateField.relfinrank E E') :
    IntermediateField.relfinrank
        (IntermediateField.adjoin K (⇑(ModularCurve.coeffMap (algebraMap k K)) '' (E : Set (LaurentSeries k))))
        (IntermediateField.adjoin K (⇑(ModularCurve.coeffMap (algebraMap k K)) '' (E' : Set (LaurentSeries k)))) =
      IntermediateField.relfinrank E E' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le.solution
