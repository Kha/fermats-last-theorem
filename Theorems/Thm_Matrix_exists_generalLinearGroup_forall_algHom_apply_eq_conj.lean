import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import P2M.Util
import P2M.Sol.S_Matrix_exists_generalLinearGroup_forall_algHom_apply_eq_conj

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.exists_generalLinearGroup_forall_algHom_apply_eq_conj
    (K : Type) [Field K] (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
    (f : Matrix n n K →ₐ[K] Matrix n n K) :
    ∃ u : GL n K, ∀ x : Matrix n n K,
      f x = (u : Matrix n n K) * x * ((u⁻¹ : GL n K) : Matrix n n K) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_generalLinearGroup_forall_algHom_apply_eq_conj.solution
