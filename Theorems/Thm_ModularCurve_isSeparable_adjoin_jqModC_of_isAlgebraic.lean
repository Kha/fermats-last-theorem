import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_isSeparable_adjoin_jqModC_of_isAlgebraic
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.isSeparable_adjoin_jqModC_of_isAlgebraic
    (K : Type*) [Field K] [PerfectField K] (F : IntermediateField K (LaurentSeries K))
    (hj : jqModC K ∈ F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({⟨jqModC K, hj⟩} : Set F)) F] :
    Algebra.IsSeparable (IntermediateField.adjoin K ({⟨jqModC K, hj⟩} : Set F)) F := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isSeparable_adjoin_jqModC_of_isAlgebraic.solution
