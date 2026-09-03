import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsSeparated_of_comp_of_universallyClosed_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsSeparated.of_comp_of_universallyClosed_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsSeparated (f ≫ g)] [UniversallyClosed f]
    [Surjective f] : IsSeparated g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsSeparated_of_comp_of_universallyClosed_of_surjective.solution
