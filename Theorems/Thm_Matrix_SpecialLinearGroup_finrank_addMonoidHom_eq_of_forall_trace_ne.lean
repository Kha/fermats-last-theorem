import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_eq_of_forall_trace_ne

set_option autoImplicit false
theorem Matrix.SpecialLinearGroup.finrank_addMonoidHom_eq_of_forall_trace_ne
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1)
    (K : Type) [Field K] [CharZero K] :
    Module.finrank K (Additive Γ →+ K) = 1 + Γ.index / 6 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_eq_of_forall_trace_ne.solution
