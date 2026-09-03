import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_kw_lrSixU_addZ_ne_zero_ychartR
import P2M.Util
namespace P2MW.S_WeierstrassProjModel_exists_lrSixU_ne_zero_ychartR

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i : Fin 3) :
    ∃ l, kw_lrSixU W i 1 l ≠ 0 :=
  ⟨.inl 2, kw_lrSixU_addZ_ne_zero_ychartR W i⟩

end
