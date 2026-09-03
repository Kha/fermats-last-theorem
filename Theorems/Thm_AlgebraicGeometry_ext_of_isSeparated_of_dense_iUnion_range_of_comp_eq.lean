import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ext_of_isSeparated_of_dense_iUnion_range_of_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.ext_of_isSeparated_of_dense_iUnion_range_of_comp_eq
    {X Y Z : Scheme.{u}} (f g : X ⟶ Y) (s : Y ⟶ Z) [IsSeparated s] (hs : f ≫ s = g ≫ s) [IsReduced X]
    {ι : Type u} (T : ι → Scheme.{u}) (z : ∀ i, T i ⟶ X) (hz : ∀ i, z i ≫ f = z i ≫ g)
    (hdense : Dense (⋃ i, Set.range (z i).base)) :
    f = g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ext_of_isSeparated_of_dense_iUnion_range_of_comp_eq.solution
