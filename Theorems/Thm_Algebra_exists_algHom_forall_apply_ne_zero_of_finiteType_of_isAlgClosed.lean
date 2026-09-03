import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed

set_option autoImplicit false

theorem Algebra.exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed
    {k : Type*} [Field k] [IsAlgClosed k]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    {ι : Type*} [Finite ι] (g : ι → B) (hg : ∀ i, g i ≠ 0) :
    ∃ χ : B →ₐ[k] k, ∀ i, χ (g i) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed.solution
