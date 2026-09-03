import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_existsUnique_eq_one_kroneckerMap_of_forall_commute_kroneckerMap_one

set_option autoImplicit false

theorem Matrix.existsUnique_eq_one_kroneckerMap_of_forall_commute_kroneckerMap_one
    {K : Type} [CommRing K] {m n : Type} [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n]
    (X : Matrix (m × n) (m × n) K)
    (hX : ∀ A : Matrix m m K,
      X * Matrix.kroneckerMap (· * ·) A (1 : Matrix n n K) = Matrix.kroneckerMap (· * ·) A (1 : Matrix n n K) * X) :
    ∃! B : Matrix n n K, X = Matrix.kroneckerMap (· * ·) (1 : Matrix m m K) B := by p2m_exact_reverting @_root_.P2MW.S_Matrix_existsUnique_eq_one_kroneckerMap_of_forall_commute_kroneckerMap_one.solution
