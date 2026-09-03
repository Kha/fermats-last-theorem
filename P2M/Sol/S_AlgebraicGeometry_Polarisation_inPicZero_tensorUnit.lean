import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Polarisation_inPicZero_tensorUnit

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) :
    InPicZero f L (𝟙_ A.Modules) := by
  refine ⟨?_, fun x => ?_⟩
  · show Scheme.Modules.IsInvertible (SheafOfModules.unit A.ringCatSheaf)
    exact Scheme.Modules.isInvertible_unit A
  · exact ⟨Scheme.Modules.pullbackUnitIso (L.translate x)⟩
