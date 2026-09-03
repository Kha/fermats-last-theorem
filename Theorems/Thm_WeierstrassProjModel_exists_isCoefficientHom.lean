import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_isCoefficientHom

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.exists_isCoefficientHom
    {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T') :
    ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
      (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
      IsCoefficientHom W f φ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_isCoefficientHom.solution
