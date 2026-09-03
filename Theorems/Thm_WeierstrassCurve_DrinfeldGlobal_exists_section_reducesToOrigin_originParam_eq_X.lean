import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_section_reducesToOrigin_originParam_eq_X

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_section_reducesToOrigin_originParam_eq_X
    {A : Type} [CommRing A] (W : WeierstrassCurve A) (i : Fin 2) :
    ∃ (P : Section (W.map (algebraMap A (MvPowerSeries (Fin 2) A))))
      (χ : OriginChartRing (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) →+* MvPowerSeries (Fin 2) A),
      ReducesToOrigin P χ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1}) ∧
      originParam χ = MvPowerSeries.X i := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_section_reducesToOrigin_originParam_eq_X.solution
