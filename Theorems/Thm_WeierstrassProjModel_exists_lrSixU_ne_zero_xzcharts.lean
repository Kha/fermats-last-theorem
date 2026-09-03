import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_lrSixU_ne_zero_xzcharts

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
theorem WeierstrassProjModel.exists_lrSixU_ne_zero_xzcharts
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (i j : Fin 3) (hi : i ≠ 1) (hj : j ≠ 1) :
    ∃ l, kw_lrSixU W i j l ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_lrSixU_ne_zero_xzcharts.solution
