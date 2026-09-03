import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry P2MW.S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective IsClosedImmersion.of_isPreimmersion UniversallyClosed QuasiCompact Scheme Flat IsClosedImmersion IsSeparated"
namespace IsSeparatedDescentAux
p2m_open "AlgebraicGeometry"

theorem isSeparated_iff_universallyClosed_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSeparated f ↔ UniversallyClosed (pullback.diagonal f) := by
  refine ⟨fun _ => inferInstance, fun _ => ⟨?_⟩⟩
  exact IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range

theorem isSeparated_eq_diagonal_universallyClosed :
    @IsSeparated = MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme.{u}) := by
  ext X Y f
  rw [MorphismProperty.diagonal_iff]
  exact isSeparated_iff_universallyClosed_diagonal f

end AlgebraicGeometry.IsSeparatedDescentAux

theorem solution :
    DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [AlgebraicGeometry.IsSeparatedDescentAux.isSeparated_eq_diagonal_universallyClosed]
  infer_instance
