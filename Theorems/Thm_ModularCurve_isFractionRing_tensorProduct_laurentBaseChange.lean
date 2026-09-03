import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_GeometricBaseChange
import P2M.Util
import P2M.Sol.S_ModularCurve_isFractionRing_tensorProduct_laurentBaseChange

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.isFractionRing_tensorProduct_laurentBaseChange
    (L : Type*) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) :
    letI := ((ModularCurve.baseChangeHom L F₀).codRestrict (ModularCurve.laurentBaseChange L F₀).toSubalgebra
      (ModularCurve.baseChangeHom_mem L F₀)).toRingHom.toAlgebra
    IsFractionRing (L ⊗[ℚ] ↥F₀) ↥(ModularCurve.laurentBaseChange L F₀) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isFractionRing_tensorProduct_laurentBaseChange.solution
