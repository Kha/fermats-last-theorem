import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.eq_univ_of_isClopen_of_range_specMap_subset_of_injective
    {R₀ L : Type} [CommRing R₀] [CommRing L] (φ : R₀ →+* L) (hφ : Function.Injective φ)
    (W : Set ↥(Spec (CommRingCat.of R₀))) (hW : IsClopen W)
    (hWL : Set.range (Spec.map (CommRingCat.ofHom φ)).base ⊆ W) : W = Set.univ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective.solution
