import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {Z X Y : Scheme.{u}} (i : Z ⟶ X) (g : X ⟶ Y) [IsClosedImmersion i] [Etale g]
    [Flat (i ≫ g)] [LocallyOfFinitePresentation (i ≫ g)] :
    IsOpenImmersion i ∧ Etale (i ≫ g) := by

  have hmono : Mono i := inferInstance
  have hdiag : IsOpenImmersion (Limits.pullback.diagonal i) := inferInstance
  have hi : FormallyUnramified i := inferInstance
  have hg : FormallyUnramified g := inferInstance
  have hig : FormallyUnramified (i ≫ g) := MorphismProperty.comp_mem _ i g hi hg
  have het : Etale (i ≫ g) := Etale.of_formallyUnramified_of_flat (f := i ≫ g)
  have heti : Etale i := Etale.of_comp i g
  have hflat : Flat i := (Etale.iff_flat_and_formallyUnramified.mp heti).1
  have hlfp : LocallyOfFinitePresentation i := (Etale.iff_flat_and_formallyUnramified.mp heti).2.2
  exact ⟨IsOpenImmersion.of_flat_of_mono i, het⟩
