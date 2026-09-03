import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq

set_option autoImplicit false

universe v w u

open CategoryTheory CategoryTheory.Limits

theorem AlgebraicGeometry.Scheme.Hom.finrank_pullbackMap_of_comp_eq {X X' S T : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S) (t : T ⟶ S) (π : X' ⟶ X) (hπ : π ≫ f = f')
    [AlgebraicGeometry.Flat π] [AlgebraicGeometry.IsFinite π] (y : ↑(pullback f t)) :
    (pullback.map f' t f t π (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hπ])
        (by rw [Category.comp_id, Category.id_comp])).finrank y =
      π.finrank (pullback.fst f t y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq.solution
