import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_comp_projMap_eq_projMap_comp_isPullback_of_isCoefficientHom

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_comp_projMap_eq_projMap_comp_isPullback_of_isCoefficientHom
    {T T' : Type} [CommRing T] [CommRing T'] (f : T →+* T')
    (W₁ W₂ : WeierstrassCurve T)
    (u : projModelCR W₁.toProjective ⟶ projModelCR W₂.toProjective)
    (hu : u ≫ projModelStrCR W₂.toProjective = projModelStrCR W₁.toProjective)
    (φ₁ : projModelGradingCR W₁.toProjective →+*ᵍ projModelGradingCR (W₁.map f).toProjective)
    (hφ₁ : HomogeneousIdeal.irrelevant (projModelGradingCR (W₁.map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W₁.toProjective)).map φ₁)
    (hcoef₁ : IsCoefficientHom W₁.toProjective f φ₁)
    (φ₂ : projModelGradingCR W₂.toProjective →+*ᵍ projModelGradingCR (W₂.map f).toProjective)
    (hφ₂ : HomogeneousIdeal.irrelevant (projModelGradingCR (W₂.map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W₂.toProjective)).map φ₂)
    (hcoef₂ : IsCoefficientHom W₂.toProjective f φ₂) :
    ∃ u' : projModelCR (W₁.map f).toProjective ⟶ projModelCR (W₂.map f).toProjective,
      u' ≫ projModelStrCR (W₂.map f).toProjective = projModelStrCR (W₁.map f).toProjective ∧
      u' ≫ Proj.map φ₂ hφ₂ = Proj.map φ₁ hφ₁ ≫ u ∧
      IsPullback u' (Proj.map φ₁ hφ₁) (Proj.map φ₂ hφ₂) u ∧
      ∀ u'' : projModelCR (W₁.map f).toProjective ⟶ projModelCR (W₂.map f).toProjective,
        u'' ≫ projModelStrCR (W₂.map f).toProjective = projModelStrCR (W₁.map f).toProjective →
        u'' ≫ Proj.map φ₂ hφ₂ = Proj.map φ₁ hφ₁ ≫ u → u'' = u' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_comp_projMap_eq_projMap_comp_isPullback_of_isCoefficientHom.solution
