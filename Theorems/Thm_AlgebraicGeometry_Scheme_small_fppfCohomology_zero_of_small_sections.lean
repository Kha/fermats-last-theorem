import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_small_fppfCohomology_zero_of_small_sections

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

theorem AlgebraicGeometry.Scheme.small_fppfCohomology_zero_of_small_sections
    {S : Scheme.{u}} (F : Sheaf (smallFppfTopology S) Ab.{u + 1})
    [Small.{v} (F.1.obj (op (fppfTerminal S)))] :
    Small.{v} (fppfCohomology S F 0) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_zero_of_small_sections.solution
