import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsInvariant_exists_isLocalRing_maximalIdeal_eq_under_of_forall_isMaximal_exists_smul_eq
set_option autoImplicit false

open Pointwise

theorem Algebra.IsInvariant.exists_isLocalRing_maximalIdeal_eq_under_of_forall_isMaximal_exists_smul_eq
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] [Algebra.IsIntegral A B] [FaithfulSMul A B]
    (𝔓 : Ideal B) [𝔓.IsMaximal]
    (htrans : ∀ Q : Ideal B, Q.IsMaximal → ∃ g : G, Q = g • 𝔓) :
    ∃ _ : IsLocalRing A, IsLocalRing.maximalIdeal A = Ideal.under A 𝔓 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsInvariant_exists_isLocalRing_maximalIdeal_eq_under_of_forall_isMaximal_exists_smul_eq.solution
