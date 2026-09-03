import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_GroupLaws_one_comp_projMap_eq_of_isCoefficientHom

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem WeierstrassCurve.DrinfeldGlobal.GroupLaws.one_comp_projMap_eq_of_isCoefficientHom
    (A : Type u) [CommRing A] (𝒢 : GroupLaws A) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type u) [CommRing T] [Algebra A T] (K : Type u) [Field K] [Algebra A K] (f : T →ₐ[A] K)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (hΔ' : IsUnit (W.map f.toRingHom).Δ)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hφc : IsCoefficientHom W f.toRingHom φ)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) :
    ((𝒢 K (W.map f.toRingHom) hΔ').one s).1 ≫ Proj.map φ hφ =
      ((𝒢 T W hΔ).one (s ≫ Spec.map (CommRingCat.ofHom f.toRingHom))).1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_GroupLaws_one_comp_projMap_eq_of_isCoefficientHom.solution
