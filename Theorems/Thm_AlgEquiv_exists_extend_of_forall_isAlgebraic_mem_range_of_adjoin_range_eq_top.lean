import Mathlib
import P2M.Util
import P2M.Sol.S_AlgEquiv_exists_extend_of_forall_isAlgebraic_mem_range_of_adjoin_range_eq_top

set_option autoImplicit false

theorem AlgEquiv.exists_extend_of_forall_isAlgebraic_mem_range_of_adjoin_range_eq_top
    {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra κ F]
    {κ' : Type*} [Field κ'] [Algebra κ κ'] [Algebra.IsAlgebraic κ κ'] [Algebra.IsSeparable κ κ']
    {F' : Type*} [Field F'] [Algebra κ' F'] [Algebra F F'] [Algebra κ F']
    [IsScalarTower κ F F'] [IsScalarTower κ κ' F']
    (halg : ∀ x : F, IsAlgebraic κ x → x ∈ Set.range (algebraMap κ F))
    (hgen : Algebra.adjoin F (Set.range (algebraMap κ' F')) = ⊤)
    (σ : F ≃ₐ[κ] F) :
    ∃ σ' : F' ≃ₐ[κ'] F', ∀ f : F, σ' (algebraMap F F' f) = algebraMap F F' (σ f) := by p2m_exact_reverting @_root_.P2MW.S_AlgEquiv_exists_extend_of_forall_isAlgebraic_mem_range_of_adjoin_range_eq_top.solution
