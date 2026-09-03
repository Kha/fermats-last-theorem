import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_zero_of_small_sections

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

theorem solution
    {S : Scheme.{u}} (F : Sheaf (smallFppfTopology S) Ab.{u + 1})
    [Small.{v} (F.1.obj (op (fppfTerminal S)))] :
    Small.{v} (fppfCohomology S F 0) :=
  small_map (fppfCohomologyZeroAddEquiv S F).toEquiv
