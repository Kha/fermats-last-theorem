import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect
    {T : Type u} [CommRing T] (V : WeierstrassCurve T) (G : RelativeGroupLaw T (projModelStrCR V.toProjective)) :
    (∃ χ : OriginChartRing V.toProjective →+* T,
        IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY V.toProjective) = 0 ∧ χ (zOverY V.toProjective) = 0) ↔
      (G.one (𝟙 _)).1 = (kwZeroSect T V).1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect.solution
