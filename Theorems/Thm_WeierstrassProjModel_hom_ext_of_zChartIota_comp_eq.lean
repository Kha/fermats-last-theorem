import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_hom_ext_of_zChartIota_comp_eq
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.hom_ext_of_zChartIota_comp_eq
    (T : Type) [CommRing T] (W : WeierstrassCurve T)
    {Y : Scheme} [Y.IsSeparated]
    (f g : projModelCR W.toProjective ⟶ Y)
    (h : zChartι W.toProjective ≫ f = zChartι W.toProjective ≫ g) : f = g := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_hom_ext_of_zChartIota_comp_eq.solution
