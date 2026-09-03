import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isFinite_flat_and_finrank_pullback_fst_comp_eq_mul_of_finrank_eq_const

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isFinite_flat_and_finrank_pullback_fst_comp_eq_mul_of_finrank_eq_const
    {X Y Z : Scheme.{u}} (g : X ⟶ Z) (h : Y ⟶ Z)
    [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] [IsFinite h] [Flat h] [LocallyOfFinitePresentation h]
    (m n : ℕ) (hg : ∀ z : Z, g.finrank z = m) (hh : ∀ z : Z, h.finrank z = n) :
    IsFinite (pullback.fst g h ≫ g) ∧ Flat (pullback.fst g h ≫ g) ∧ LocallyOfFinitePresentation (pullback.fst g h ≫ g) ∧
      ∀ z : Z, (pullback.fst g h ≫ g).finrank z = m * n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isFinite_flat_and_finrank_pullback_fst_comp_eq_mul_of_finrank_eq_const.solution
