import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_isChordTangent_isOriginIdentity_one_eq_zeroSect
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_levelTransport_isSectionTransport
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import P2M.Util
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport
attribute [-simp] WeierstrassProjModel.kw_lrThird_substHom_X

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (A : Type) [CommRing A] (q : ℕ) :
    ∃ (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q),
      𝒢.IsChordTangent ∧ 𝒢.IsOriginIdentity ∧ 𝒯.IsSectionTransport ∧
      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
        ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
          (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
            (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
          IsVariableChangeHom W C φ) ∧
      (∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
        (W : WeierstrassCurve.Projective T),
        ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
          (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
            (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
          IsCoefficientHom W f.toRingHom φ) := by
  obtain ⟨𝒢, hCT, hOI, -⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_groupLaws_isChordTangent_isOriginIdentity_one_eq_zeroSect A
  obtain ⟨𝒯, h𝒯⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_levelTransport_isSectionTransport A q 𝒢 hCT hOI
  refine ⟨𝒢, 𝒯, hCT, hOI, h𝒯, ?_, ?_⟩
  · intro T _ _ W C
    obtain ⟨φ, hφ, hvc, -, -⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap W C
    exact ⟨φ, hφ, hvc⟩
  · intro T T' _ _ _ _ f W
    exact WeierstrassProjModel.exists_isCoefficientHom W f.toRingHom
