import Mathlib
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_LevelTransport_exists_act_neg_comp_eqToHom_eq_inv
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve

theorem WeierstrassCurve.DrinfeldGlobal.LevelTransport.exists_act_neg_comp_eqToHom_eq_inv
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (K : Type) [Field K] [Algebra A K] (x : RawDrinfeldPair K) (hΔ : IsUnit x.curve.Δ) :
    ∃ hc : (𝒯.act ⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ x).curve = x.curve,
      (𝒯.act ⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ x).P.1 ≫ eqToHom (congrArg projModelCR hc) =
          ((𝒢 K x.curve hΔ).inv (𝟙 _) x.P).1 ∧
        (𝒯.act ⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ x).Q.1 ≫ eqToHom (congrArg projModelCR hc) =
          ((𝒢 K x.curve hΔ).inv (𝟙 _) x.Q).1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_LevelTransport_exists_act_neg_comp_eqToHom_eq_inv.solution
