import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isOpenImmersion_and_isClosedImmersion_of_comp_eq_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CLOPENSECT

theorem hasOfPostcompProperty_isOpenImmersion_unramified :
    MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u}) :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ f hf ↦ by
      obtain ⟨h₁, h₂⟩ := hf
      exact inferInstanceAs (IsOpenImmersion (pullback.diagonal f))

theorem main {S T : Scheme.{u}} (g : T ⟶ S)
    [LocallyOfFiniteType g] [FormallyUnramified g] [IsSeparated g]
    (s : S ⟶ T) (hs : s ≫ g = 𝟙 S) :
    IsOpenImmersion s ∧ IsClosedImmersion s := by
  haveI : IsOpenImmersion (s ≫ g) := by rw [hs]; infer_instance
  haveI : IsClosedImmersion (s ≫ g) := by rw [hs]; infer_instance
  exact ⟨hasOfPostcompProperty_isOpenImmersion_unramified.of_postcomp s g ⟨‹_›, ‹_›⟩ ‹_›,
    MorphismProperty.of_postcomp (W := @IsClosedImmersion) (W' := @IsSeparated) s g ‹_› ‹_›⟩

end CLOPENSECT

theorem solution
    {S T : Scheme.{u}} (g : T ⟶ S) [LocallyOfFiniteType g] [FormallyUnramified g] [IsSeparated g]
    (s : S ⟶ T) (hs : s ≫ g = 𝟙 S) :
    IsOpenImmersion s ∧ IsClosedImmersion s :=
  CLOPENSECT.main g s hs
