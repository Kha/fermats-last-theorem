import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_forall_exists_sub_algebraMap_mem_of_forall_smul_eq_imp_smul_sub_mem

set_option autoImplicit false

open scoped Pointwise

theorem Ideal.forall_exists_sub_algebraMap_mem_of_forall_smul_eq_imp_smul_sub_mem
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (P : Ideal A) [P.IsMaximal] (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver P] [Finite (B ⧸ Q)]
    (htriv : ∀ g : G, g • Q = Q → ∀ b : B, g • b - b ∈ Q) :
    ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ Q := by p2m_exact_reverting @_root_.P2MW.S_Ideal_forall_exists_sub_algebraMap_mem_of_forall_smul_eq_imp_smul_sub_mem.solution
