import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.finrank_comp_of_finrank_eq_const
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [Flat f] [IsFinite g] [Flat g]
    (m : ℕ) (hf : ∀ y : Y, f.finrank y = m) (z : Z) :
    (f ≫ g).finrank z = m * g.finrank z := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const.solution
