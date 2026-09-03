import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_of_exists_comp_eq_comp_of_ker_eq_bot

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.exists_comp_eq_of_exists_comp_eq_comp_of_ker_eq_bot
    {T T' A Z : Scheme.{0}} (π : T' ⟶ T) (hπ : π.ker = ⊥) (y : T ⟶ A) (ι : Z ⟶ A) [IsClosedImmersion ι]
    (h : ∃ z' : T' ⟶ Z, z' ≫ ι = π ≫ y) :
    ∃ z : T ⟶ Z, z ≫ ι = y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_of_exists_comp_eq_comp_of_ker_eq_bot.solution
