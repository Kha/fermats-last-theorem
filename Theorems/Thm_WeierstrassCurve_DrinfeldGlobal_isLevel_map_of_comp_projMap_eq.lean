import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_isLevel_map_of_comp_projMap_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isLevel_map_of_comp_projMap_eq
    {A : Type u} [CommRing A] (q : ℕ) (𝒢 : GroupLaws A) (h𝒢O : 𝒢.IsOriginIdentity)
    {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (W : WeierstrassCurve T) (x : RawDrinfeldPair T) (y : RawDrinfeldPair T')
    (hy : y.curve = x.curve.map f.toRingHom)
    (hpin : ∀ (φ : projModelGradingCR x.curve →+*ᵍ projModelGradingCR (x.curve.map f.toRingHom))
      (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (x.curve.map f.toRingHom)) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR x.curve)).map φ),
      IsCoefficientHom x.curve f.toRingHom φ →
        y.P.1 ≫ eqToHom (congrArg projModelCR hy) ≫ Proj.map φ hφ =
          Spec.map (CommRingCat.ofHom f.toRingHom) ≫ x.P.1 ∧
        y.Q.1 ≫ eqToHom (congrArg projModelCR hy) ≫ Proj.map φ hφ =
          Spec.map (CommRingCat.ofHom f.toRingHom) ≫ x.Q.1) :
    RawDrinfeldPair.IsLevel 𝒢 q W x → RawDrinfeldPair.IsLevel 𝒢 q (W.map f.toRingHom) y := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_isLevel_map_of_comp_projMap_eq.solution
