import Definitions.Def_WeierstrassCurve_ProjModel_ThirdLawCharts
import Mathlib.RingTheory.Noetherian.Defs
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_lrThird_nineCoverage_of_isElliptic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

theorem WeierstrassProjModel.kw_lrThird_nineCoverage_of_isElliptic
    [W.IsElliptic] (i j : Fin 3) :
    Ideal.span (Set.range (kw_lrSixU W i j) ∪ Set.range (kw_lrThird_u₃ W i j))
      = (⊤ : Ideal ((𝒜 i) ⊗[R] (𝒜 j))) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_lrThird_nineCoverage_of_isElliptic.solution
