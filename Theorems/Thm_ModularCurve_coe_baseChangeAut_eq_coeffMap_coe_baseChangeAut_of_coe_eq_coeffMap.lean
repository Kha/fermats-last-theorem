import Mathlib
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_GeometricBaseChange
import P2M.Util
import P2M.Sol.S_ModularCurve_coe_baseChangeAut_eq_coeffMap_coe_baseChangeAut_of_coe_eq_coeffMap

set_option autoImplicit false

theorem ModularCurve.coe_baseChangeAut_eq_coeffMap_coe_baseChangeAut_of_coe_eq_coeffMap
    (L L' : Type) [Field L] [Field L'] [Algebra ℚ L] [Algebra ℚ L'] [Algebra L L'] [IsScalarTower ℚ L L']
    [Algebra.IsAlgebraic ℚ L] [Algebra.IsAlgebraic ℚ L']
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (σ₀ : ↥F₀ ≃ₐ[ℚ] ↥F₀)
    (b : ↥(ModularCurve.laurentBaseChange L F₀)) (b' : ↥(ModularCurve.laurentBaseChange L' F₀))
    (hb : ((b' : ↥(ModularCurve.laurentBaseChange L' F₀)) : LaurentSeries L') =
      ModularCurve.coeffMap (algebraMap L L') ((b : ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L)) :
    ((ModularCurve.baseChangeAut L' σ₀ b' : ↥(ModularCurve.laurentBaseChange L' F₀)) : LaurentSeries L') =
      ModularCurve.coeffMap (algebraMap L L') ((ModularCurve.baseChangeAut L σ₀ b : ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coe_baseChangeAut_eq_coeffMap_coe_baseChangeAut_of_coe_eq_coeffMap.solution
