import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field

set_option autoImplicit false

universe u

theorem Algebra.isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field
    (κ : Type u) [Field κ] (T : Type u) [CommRing T] [Algebra κ T] [Module.Finite κ T]
    (Q : Ideal T) [Q.IsPrime] :
    Algebra.IsUnramifiedAt κ Q ↔
      ∃ s ∉ Q, ∀ φ : Module.Dual κ T, ∃ x : T, ∀ y : T, φ (s * y) = Algebra.trace κ T (x * y) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field.solution
