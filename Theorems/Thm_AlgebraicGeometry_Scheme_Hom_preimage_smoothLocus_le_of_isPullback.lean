import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_preimage_smoothLocus_le_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.preimage_smoothLocus_le_of_isPullback
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f'] :
    g' ⁻¹ᵁ f.smoothLocus ≤ f'.smoothLocus := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_preimage_smoothLocus_le_of_isPullback.solution
