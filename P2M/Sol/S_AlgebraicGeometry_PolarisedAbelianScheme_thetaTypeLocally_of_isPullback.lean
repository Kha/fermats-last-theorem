import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_congr_and_id
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_of_isPullback_comp
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_trans
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_thetaTypeLocally_of_isPullback

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem solution
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)]
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g (N + 1) n S) (u' : PolarisedAbelianScheme g (N + 1) n S')
    (h : PolarisedAbelianScheme.IsPullback φ u u') (hu : PolarisedAbelianScheme.ThetaTypeLocally δ S u) :
    PolarisedAbelianScheme.ThetaTypeLocally δ S' u' := by
  intro R _ _ ζ hζ hζ'
  letI : Algebra S R := ((algebraMap S' R).comp φ).toAlgebra
  obtain ⟨R', _, _, hff, het, X', e, hX', had⟩ := hu R ζ hζ hζ'
  refine ⟨R', inferInstance, inferInstance, hff, het, X', e, ?_, had⟩
  exact PolarisedAbelianScheme.IsPullback.of_isPullback_comp φ ((algebraMap R R').comp (algebraMap S' R)) u u'
    X'.toPolarisedAbelianScheme hX' h
