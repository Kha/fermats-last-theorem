import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_comp_projMap_eq_of_isCoefficientHom
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem WeierstrassCurve.DrinfeldGlobal.section_eq_of_comp_projMap_eq_of_isCoefficientHom
    {T : Type u} [CommRing T] {K : Type u} [Field K]
    (W : WeierstrassCurve T) (f : T →+* K)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hφc : IsCoefficientHom W f φ)
    (s₁ s₂ : Section (W.map f))
    (h : s₁.1 ≫ Proj.map φ hφ = s₂.1 ≫ Proj.map φ hφ) :
    s₁ = s₂ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_comp_projMap_eq_of_isCoefficientHom.solution
