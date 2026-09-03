import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Theorems.Thm_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian
import P2M.Util
namespace P2MW.S_ModularCurve_JZeroNeronIdentityComponent_locallyOfFinitePresentation_schemeNsmul

set_option maxHeartbeats 1600000

open AlgebraicGeometry GoodReductionJacobian ModularCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (N : JZeroNeronIdentityComponent p) (n : ℕ) :
    LocallyOfFinitePresentation (N.L.schemeNsmul n) := by
  haveI : AlgebraicGeometry.LocallyOfFiniteType N.g := N.locallyOfFiniteType
  exact AlgebraicGeometry.locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian N.g N.g (N.L.schemeNsmul n)
    (N.L.schemeNsmul_over n)
