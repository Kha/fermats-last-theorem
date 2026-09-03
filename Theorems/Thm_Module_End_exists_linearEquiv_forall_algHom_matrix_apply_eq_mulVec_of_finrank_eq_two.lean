import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_exists_linearEquiv_forall_algHom_matrix_apply_eq_mulVec_of_finrank_eq_two

set_option autoImplicit false

theorem Module.End.exists_linearEquiv_forall_algHom_matrix_apply_eq_mulVec_of_finrank_eq_two
    (k : Type*) [Field k] (W : Type*) [AddCommGroup W] [Module k W] [Module.Finite k W]
    (hW : Module.finrank k W = 2) (ψ : Matrix (Fin 2) (Fin 2) k →ₐ[k] (W →ₗ[k] W)) :
    ∃ e : W ≃ₗ[k] (Fin 2 → k), ∀ (m : Matrix (Fin 2) (Fin 2) k) (w : W), e (ψ m w) = m.mulVec (e w) := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_linearEquiv_forall_algHom_matrix_apply_eq_mulVec_of_finrank_eq_two.solution
