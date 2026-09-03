import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_exists_ringHom_comp_eq_of_closure_range_union_eq_top_of_forall_sum_mul_eq_zero

set_option autoImplicit false

theorem AlgHom.exists_ringHom_comp_eq_of_closure_range_union_eq_top_of_forall_sum_mul_eq_zero
    {k L F E : Type*} [Field k] [Field L] [Field F] [Field E] [Algebra k L] [Algebra k F]
    (α₀ α₁ : L →ₐ[k] F)
    (hgen : Subfield.closure (Set.range α₀ ∪ Set.range α₁) = ⊤)
    (h₀ : (α₀ : L →+* F).IsIntegral)
    (β₀ β₁ : L →+* E)
    (hrel : ∀ (n : ℕ) (x y : Fin n → L),
      (∑ i, α₀ (x i) * α₁ (y i)) = 0 → (∑ i, β₀ (x i) * β₁ (y i)) = 0) :
    ∃ ι : F →+* E, ι.comp (α₀ : L →+* F) = β₀ ∧ ι.comp (α₁ : L →+* F) = β₁ := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_exists_ringHom_comp_eq_of_closure_range_union_eq_top_of_forall_sum_mul_eq_zero.solution
