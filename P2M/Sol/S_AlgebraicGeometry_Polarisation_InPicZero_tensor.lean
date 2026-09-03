import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Polarisation_InPicZero_tensor

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) {M N : A.Modules} (hM : InPicZero f L M) (hN : InPicZero f L N) :
    InPicZero f L (M ⊗ N) := by
  refine ⟨Scheme.Modules.IsInvertible.tensor_monoidalV2 hM.1 hN.1, fun x => ?_⟩
  obtain ⟨eM⟩ := hM.2 x
  obtain ⟨eN⟩ := hN.2 x
  exact ⟨Scheme.Modules.pullbackTensorObjIso (L.translate x) M N ≪≫ (eM ⊗ᵢ eN)⟩
