import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isOpenImmersion_of_etale_of_universallyInjective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [UniversallyInjective f] :
    IsOpenImmersion f := by
  have hsurj : Surjective (Limits.pullback.diagonal f) := (UniversallyInjective.iff_diagonal f).mp ‹_›
  have h1 : IsOpenImmersion (Limits.pullback.diagonal f) := inferInstance
  have h2 : IsIso (Limits.pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨h1, hsurj⟩
  have h3 : Mono f := (Limits.pullback.isIso_diagonal_iff f).mp h2
  exact IsOpenImmersion.of_flat_of_mono f
