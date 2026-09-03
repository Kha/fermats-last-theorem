import Definitions.Def_ModularCurve_SpecializeModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_algebraMap_residueField_charLGeomPlaceOfPoint_surjective

open AlgebraicCurve ModularCurve
theorem ModularCurve.algebraMap_residueField_charLGeomPlaceOfPoint_surjective
    (K : Type*) [Field K] (a : K) :
    Function.Surjective (algebraMap K (ModularCurve.charLGeomPlaceOfPoint K a).ResidueField) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_algebraMap_residueField_charLGeomPlaceOfPoint_surjective.solution
