import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq

set_option autoImplicit false

theorem Algebra.isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq
    (Ω : Type*) [Field Ω] [IsAlgClosed Ω] (S : Type*) [CommRing S] [Algebra Ω S] [Module.Finite Ω S]
    (h : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → 𝔪 ^ 2 = 𝔪) :
    IsReduced S ∧ Module.finrank Ω S = Nat.card (S →ₐ[Ω] Ω) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq.solution
