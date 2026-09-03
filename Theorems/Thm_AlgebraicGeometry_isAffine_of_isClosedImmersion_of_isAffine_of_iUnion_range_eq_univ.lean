import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isAffine_of_iUnion_range_eq_univ

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry~isAffine_of_isClosedImmersion_of_isAffine_of_range_union_range"

theorem AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isAffine_of_iUnion_range_eq_univ
    (X : Scheme.{0}) (n : ℕ) (Z : Fin n → Scheme.{0}) (i : ∀ j : Fin n, Z j ⟶ X)
    (hci : ∀ j : Fin n, IsClosedImmersion (i j)) (haff : ∀ j : Fin n, IsAffine (Z j))
    (hred : IsReduced X)
    (hcov : ⋃ j : Fin n, Set.range (i j).base = Set.univ) :
    IsAffine X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isAffine_of_iUnion_range_eq_univ.solution
