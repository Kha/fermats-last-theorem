import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_nontrivial_of_not_isUnit
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit

open ModularCurve ModularCurve.UVCrossingModel

theorem solution {W : Type*} [CommRing W] [IsLocalRing W] {π : W} (hπ : ¬IsUnit π) :
    IsLocalRing (UVCrossingModel W π) :=
  by
  haveI : Nontrivial (UVCrossingModel W π) := ModularCurve.UVCrossingModel.nontrivial_of_not_isUnit hπ
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (uvCrossingIdeal W π))
    Ideal.Quotient.mk_surjective
