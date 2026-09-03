import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_epi_specMap_of_injective_of_finite

set_option autoImplicit false

universe u

theorem AlgebraicGeometry.epi_specMap_of_injective_of_finite
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Injective φ) (hfin : φ.Finite) :
    CategoryTheory.Epi (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_epi_specMap_of_injective_of_finite.solution
