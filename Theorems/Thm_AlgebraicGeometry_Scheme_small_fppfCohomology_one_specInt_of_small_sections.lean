import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.small_fppfCohomology_one_specInt_of_small_sections
    (F : Sheaf (smallFppfTopology specInt) Ab.{1})
    [∀ U : specInt.Fppf, Small.{0} (F.1.obj (op U))] :
    Small.{0} (fppfCohomology specInt F 1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.solution
