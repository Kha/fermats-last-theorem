import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_isDomain_chartTensor_of_isElliptic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.AffineScheme
import P2M.Util
namespace P2MW.S_WeierstrassProjModel_kw_lrSixU_locMap_isSchemeTheoreticallyDominant

set_option autoImplicit false
set_option maxHeartbeats 6400000

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

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (i j : Fin 3) (l : Fin 3 ⊕ Fin 3) (hl : kw_lrSixU W i j l ≠ 0) :
    IsSchemeTheoreticallyDominant (kw_lrSixU_locMap W i j l) := by
  haveI : IsDomain ((𝒜 i) ⊗[R] (𝒜 j)) := isDomain_chartTensor_of_isElliptic W i j

  haveI : IsOpenImmersion (kw_lrSixU_locMap W i j l) := by
    show IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (kw_lrSixU W i j l)))))
    infer_instance

  haveI : Nontrivial (Localization.Away (kw_lrSixU W i j l)) := by
    have hinj : Function.Injective
        (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (kw_lrSixU W i j l))) :=
      IsLocalization.injective _
        (powers_le_nonZeroDivisors_of_noZeroDivisors hl)
    exact Function.Injective.nontrivial hinj
  haveI : Nonempty (Spec (CommRingCat.of (Localization.Away (kw_lrSixU W i j l)))) :=
    inferInstance

  haveI : IsIntegral (Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j)))) := inferInstance

  haveI : IsDominant (kw_lrSixU_locMap W i j l) :=
    ⟨(IsOpenImmersion.isOpen_range (kw_lrSixU_locMap W i j l)).dense
      (Set.range_nonempty (kw_lrSixU_locMap W i j l).base)⟩
  exact IsSchemeTheoreticallyDominant.of_isDominant (kw_lrSixU_locMap W i j l)

end
