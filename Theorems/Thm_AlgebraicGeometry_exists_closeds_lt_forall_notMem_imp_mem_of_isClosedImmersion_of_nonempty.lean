import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (T : Closeds X) (hT : Set.range i.base = (T : Set X))
    (U : Z.Opens) (hU : (U : Set Z).Nonempty) :
    ∃ T' : Closeds X, T' < T ∧ ∀ z : Z, z ∉ U → i.base z ∈ T' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty.solution
