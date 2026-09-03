import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_exists_pos_forall_nsmul_eq_zero_of_add_eq_zero_of_finite_fixedPoints_comp_self

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AddMonoidHom.exists_pos_forall_nsmul_eq_zero_of_add_eq_zero_of_finite_fixedPoints_comp_self
    {M : Type u} [AddCommGroup M] (F : M →+ M)
    (hfin : (Function.fixedPoints (F ∘ F)).Finite) :
    ∃ c : ℕ, 0 < c ∧ ∀ a₀ a₁ : M, a₀ + F a₁ = 0 → F a₀ + a₁ = 0 → c • a₀ = 0 ∧ c • a₁ = 0 := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_exists_pos_forall_nsmul_eq_zero_of_add_eq_zero_of_finite_fixedPoints_comp_self.solution
