import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isClosedImmersion_of_universallyClosed_of_universallyInjective_of_formallyUnramified

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] [UniversallyInjective f] [LocallyOfFiniteType f] [FormallyUnramified f] :
    IsClosedImmersion f := by
  have hsurj : Surjective (pullback.diagonal f) := (UniversallyInjective.iff_diagonal f).mp inferInstance
  have hdiag : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hsurj⟩
  have hmono : Mono f := (pullback.isIso_diagonal_iff f).mp hdiag
  have : IsProper f := {}
  have : LocallyQuasiFinite f := inferInstance
  have : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  exact (IsClosedImmersion.iff_isFinite_and_mono f).mpr ⟨this, hmono⟩
