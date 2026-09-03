import Definitions.Def_AlgebraicGeometry_FGSubalgebra
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    Nonempty (IsColimit (FGSubalgebra.cocone R A)) := by
  have : ReflectsColimit (FGSubalgebra.diagram R A) (CategoryTheory.forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine ⟨isColimitOfReflects (CategoryTheory.forget CommRingCat.{u}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · rintro (x : A)
    exact ⟨⟨Algebra.adjoin R {x}, {x}, by rw [Finset.coe_singleton]⟩,
      (⟨x, Algebra.self_mem_adjoin_singleton R x⟩ : Algebra.adjoin R {x}), rfl⟩
  · rintro A₀ A₁ (x₀ : A₀.1) (x₁ : A₁.1) (h : (x₀ : A) = x₁)
    refine ⟨⟨A₀.1 ⊔ A₁.1, A₀.2.sup A₁.2⟩, homOfLE (le_sup_left : A₀.1 ≤ A₀.1 ⊔ A₁.1),
      homOfLE (le_sup_right : A₁.1 ≤ A₀.1 ⊔ A₁.1), ?_⟩
    change (Subalgebra.inclusion (le_sup_left : A₀.1 ≤ A₀.1 ⊔ A₁.1) x₀ : ↥(A₀.1 ⊔ A₁.1)) =
      Subalgebra.inclusion (le_sup_right : A₁.1 ≤ A₀.1 ⊔ A₁.1) x₁
    exact Subtype.ext h
