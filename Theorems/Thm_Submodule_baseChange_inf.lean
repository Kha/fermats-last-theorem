import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_baseChange_inf

set_option autoImplicit false

open scoped TensorProduct

theorem Submodule.baseChange_inf
    {R : Type*} [Field R] (A : Type*) [CommRing A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M] (p q : Submodule R M) :
    (p ⊓ q).baseChange A = p.baseChange A ⊓ q.baseChange A := by p2m_exact_reverting @_root_.P2MW.S_Submodule_baseChange_inf.solution
