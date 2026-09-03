import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap
    {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T) :
    ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
      (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
      IsVariableChangeHom W C φ ∧ IsIso (Proj.map φ hφ) ∧
      Proj.map φ hφ ≫ projModelStrCR W = projModelStrCR (C • W) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap.solution
