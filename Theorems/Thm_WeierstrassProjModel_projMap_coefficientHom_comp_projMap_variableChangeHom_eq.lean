import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_projMap_coefficientHom_comp_projMap_variableChangeHom_eq

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.projMap_coefficientHom_comp_projMap_variableChangeHom_eq
    (T T' : Type) [CommRing T] [CommRing T'] (f : T →+* T')
    (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (hmap : (C • W).map f = C.map f • W.map f)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C • W).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hφC : IsVariableChangeHom W.toProjective C φ)
    (φ' : projModelGradingCR (W.map f).toProjective →+*ᵍ projModelGradingCR (C.map f • W.map f).toProjective)
    (hφ' : HomogeneousIdeal.irrelevant (projModelGradingCR (C.map f • W.map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f).toProjective)).map φ')
    (hφ'C : IsVariableChangeHom (W.map f).toProjective (C.map f) φ')
    (γ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map f).toProjective)
    (hγ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map γ)
    (hγf : IsCoefficientHom W.toProjective f γ)
    (γC : projModelGradingCR (C • W).toProjective →+*ᵍ projModelGradingCR ((C • W).map f).toProjective)
    (hγC : HomogeneousIdeal.irrelevant (projModelGradingCR ((C • W).map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective)).map γC)
    (hγCf : IsCoefficientHom (C • W).toProjective f γC) :
    Proj.map γC hγC ≫ Proj.map φ hφ =
      eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hmap)) ≫ Proj.map φ' hφ' ≫ Proj.map γ hγ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_projMap_coefficientHom_comp_projMap_variableChangeHom_eq.solution
