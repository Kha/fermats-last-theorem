import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsInvariant_exists_forall_smul_eq_and_sub_mem_of_le_inertia

set_option autoImplicit false

open scoped Pointwise

theorem Algebra.IsInvariant.exists_forall_smul_eq_and_sub_mem_of_le_inertia
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)]
    (H : Subgroup G) (hH : H ≤ Q.inertia G) (b : B) :
    ∃ b' : B, (∀ h ∈ H, h • b' = b') ∧ b - b' ∈ Q := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsInvariant_exists_forall_smul_eq_and_sub_mem_of_le_inertia.solution
