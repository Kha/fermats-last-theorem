import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronIdentityComponent_locallyOfFinitePresentation_schemeNsmul

open AlgebraicGeometry GoodReductionJacobian ModularCurve

theorem ModularCurve.JZeroNeronIdentityComponent.locallyOfFinitePresentation_schemeNsmul
    (p : ℕ) [Fact p.Prime] (N : JZeroNeronIdentityComponent p) (n : ℕ) :
    LocallyOfFinitePresentation (N.L.schemeNsmul n) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronIdentityComponent_locallyOfFinitePresentation_schemeNsmul.solution
