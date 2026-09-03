import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder

set_option autoImplicit false

universe u v

open AddMonoidAlgebra

theorem ValuationSubring.addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder
    {L : Type u} [Field L] (A : ValuationSubring L)
    {G : Type v} [AddMonoid G] (hG : ∀ g : G, IsOfFinAddOrder g)
    (χ : AddMonoidAlgebra A G →ₐ[A] L) :
    (∀ x, χ x ∈ A) ∧ ∃ χA : AddMonoidAlgebra A G →ₐ[A] A, ∀ x, (χA x : L) = χ x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder.solution
