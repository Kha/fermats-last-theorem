import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_of_bijective_app_of_le_opensRange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace AlgebraicGeometry.Scheme.Modules

theorem solution
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (M : Y.Modules) (L : X.Modules)
    (π : L ⟶ (Scheme.Modules.pushforward f).obj M)
    (hπ : ∀ U : X.Opens, U ≤ f.opensRange → Function.Bijective (π.app U)) :
    Nonempty ((Scheme.Modules.pullback f).obj L ≅ M) := by
  have happ : ∀ U : Y.Opens, ((restrictFunctor f).map π).app U = π.app (f ''ᵁ U) := fun U => rfl
  haveI : IsIso ((restrictFunctor f).map π) := by
    rw [Hom.isIso_iff_isIso_app]
    intro U
    rw [happ, ConcreteCategory.isIso_iff_bijective]
    exact hπ _ (f.image_le_opensRange U)
  exact ⟨((restrictFunctorIsoPullback f).app L).symm ≪≫ asIso ((restrictFunctor f).map π) ≪≫
    (restrictFunctorAdjCounitIso f).app M⟩
