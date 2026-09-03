import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_LevelTransport_map_eq_mk_of_comp_projMap_eq
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem WeierstrassCurve.DrinfeldGlobal.LevelTransport.map_eq_mk_of_comp_projMap_eq
    (A : Type u) [CommRing A] (𝒢 : GroupLaws A) (q : ℕ) (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (T : Type u) [CommRing T] [Algebra A T] (K : Type u) [Field K] [Algebra A K] (ι : T →ₐ[A] K)
    (z₀ : RawDrinfeldPair T) (P' Q' : Section (z₀.curve.map ι.toRingHom))
    (φ : projModelGradingCR z₀.curve →+*ᵍ projModelGradingCR (z₀.curve.map ι.toRingHom))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (z₀.curve.map ι.toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR z₀.curve)).map φ)
    (hφc : IsCoefficientHom z₀.curve ι.toRingHom φ)
    (hP : P'.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ z₀.P.1)
    (hQ : Q'.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ z₀.Q.1) :
    𝒯.map ι z₀ = ⟨z₀.curve.map ι.toRingHom, P', Q'⟩ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_LevelTransport_map_eq_mk_of_comp_projMap_eq.solution
