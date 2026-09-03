import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_lrSixU_ne_zero_ychartR
import Theorems.Thm_WeierstrassProjModel_exists_lrSixU_ne_zero_ychartL
import Theorems.Thm_WeierstrassProjModel_exists_lrSixU_ne_zero_xzcharts
import P2M.Util
namespace P2MW.S_WeierstrassProjModel_exists_lrSixU_ne_zero_of_isElliptic

set_option autoImplicit false

noncomputable section

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

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i j : Fin 3) :
    ∃ l, kw_lrSixU W i j l ≠ 0 := by
  by_cases hj : j = 1
  · exact hj ▸ exists_lrSixU_ne_zero_ychartR W i
  · by_cases hi : i = 1
    · exact hi ▸ exists_lrSixU_ne_zero_ychartL W j
    · exact exists_lrSixU_ne_zero_xzcharts W i j hi hj

end
