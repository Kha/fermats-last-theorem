import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_variableChange_eq_one_of_projMap_eq_id

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.variableChange_eq_one_of_projMap_eq_id
    (T : Type) [CommRing T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (C : WeierstrassCurve.VariableChange T) (hC : C • W = W)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C • W).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hφC : IsVariableChangeHom W.toProjective C φ)
    (hid : eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hC)).symm ≫ Proj.map φ hφ = 𝟙 _) :
    C = 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_variableChange_eq_one_of_projMap_eq_id.solution
