import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_originW_eq_evalSeries_formalW_originParam_of_isOriginChartSection

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.originW_eq_evalSeries_formalW_originParam_of_isOriginChartSection
    {T : Type u} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) (P : Section W) (χ : OriginChartRing W →+* T) (hPχ : IsOriginChartSection P χ)
    (hz : originParam χ ∈ maximalIdeal T) (hw : originW χ ∈ maximalIdeal T) :
    originW χ = (letI : WithIdeal T := ⟨maximalIdeal T⟩; FormalGroup.evalSeries W.formalW (originParam χ)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_originW_eq_evalSeries_formalW_originParam_of_isOriginChartSection.solution
