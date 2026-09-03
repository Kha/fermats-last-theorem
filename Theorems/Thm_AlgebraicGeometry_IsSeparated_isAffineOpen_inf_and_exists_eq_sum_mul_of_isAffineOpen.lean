import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsSeparated_isAffineOpen_inf_and_exists_eq_sum_mul_of_isAffineOpen

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.IsSeparated.isAffineOpen_inf_and_exists_eq_sum_mul_of_isAffineOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [IsAffine Y]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) ∧
    ∀ c : Γ(X, U ⊓ V), ∃ (n : ℕ) (a : Fin n → Γ(X, U)) (b : Fin n → Γ(X, V)),
      c = ∑ i : Fin n, X.presheaf.map (homOfLE inf_le_left).op (a i) * X.presheaf.map (homOfLE inf_le_right).op (b i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsSeparated_isAffineOpen_inf_and_exists_eq_sum_mul_of_isAffineOpen.solution
