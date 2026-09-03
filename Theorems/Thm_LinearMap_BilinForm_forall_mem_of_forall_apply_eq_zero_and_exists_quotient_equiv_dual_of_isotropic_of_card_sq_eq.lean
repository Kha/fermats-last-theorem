import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_BilinForm_forall_mem_of_forall_apply_eq_zero_and_exists_quotient_equiv_dual_of_isotropic_of_card_sq_eq

set_option autoImplicit false

open scoped TensorProduct

theorem LinearMap.BilinForm.forall_mem_of_forall_apply_eq_zero_and_exists_quotient_equiv_dual_of_isotropic_of_card_sq_eq
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (b : LinearMap.BilinForm (ZMod p) V)
    (hleft : ∀ x : V, (∀ y : V, b x y = 0) → x = 0) (hright : ∀ y : V, (∀ x : V, b x y = 0) → y = 0)
    (A : Submodule (ZMod p) V) (hiso : ∀ x ∈ A, ∀ y ∈ A, b x y = 0)
    (hcard : Nat.card A ^ 2 = Nat.card V) :
    (∀ y : V, (∀ a ∈ A, b a y = 0) → y ∈ A) ∧
    ∃ φ : (V ⧸ A) ≃ₗ[ZMod p] (A →ₗ[ZMod p] ZMod p),
      ∀ (y : V) (a : A), φ (Submodule.Quotient.mk y) a = b a y := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_BilinForm_forall_mem_of_forall_apply_eq_zero_and_exists_quotient_equiv_dual_of_isotropic_of_card_sq_eq.solution
