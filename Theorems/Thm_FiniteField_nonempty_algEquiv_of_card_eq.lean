import Mathlib
import P2M.Util
import P2M.Sol.S_FiniteField_nonempty_algEquiv_of_card_eq

set_option autoImplicit false

theorem FiniteField.nonempty_algEquiv_of_card_eq
    (K : Type) [Field K] (L₁ : Type) [Field L₁] [Algebra K L₁] [Finite L₁]
    (L₂ : Type) [Field L₂] [Algebra K L₂] [Finite L₂]
    (h : Nat.card L₁ = Nat.card L₂) :
    Nonempty (L₁ ≃ₐ[K] L₂) := by p2m_exact_reverting @_root_.P2MW.S_FiniteField_nonempty_algEquiv_of_card_eq.solution
