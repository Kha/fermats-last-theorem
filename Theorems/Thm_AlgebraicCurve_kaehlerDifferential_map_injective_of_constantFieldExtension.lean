import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_kaehlerDifferential_map_injective_of_constantFieldExtension

theorem AlgebraicCurve.kaehlerDifferential_map_injective_of_constantFieldExtension
    {K F E FE : Type*} [Field K] [Field F] [Field E] [Field FE]
    [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE]
    [PerfectField K] [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤) :
    Function.Injective (KaehlerDifferential.map K E F FE) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_kaehlerDifferential_map_injective_of_constantFieldExtension.solution
