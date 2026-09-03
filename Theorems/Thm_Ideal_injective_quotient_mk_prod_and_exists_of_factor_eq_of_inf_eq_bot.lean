import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_injective_quotient_mk_prod_and_exists_of_factor_eq_of_inf_eq_bot

set_option autoImplicit false

theorem Ideal.injective_quotient_mk_prod_and_exists_of_factor_eq_of_inf_eq_bot
    (A : Type) [CommRing A] (I₁ I₂ : Ideal A) (h : I₁ ⊓ I₂ = ⊥) :
    Function.Injective (fun a : A => (Ideal.Quotient.mk I₁ a, Ideal.Quotient.mk I₂ a)) ∧
    ∀ (x₁ : A ⧸ I₁) (x₂ : A ⧸ I₂),
      Ideal.Quotient.factor (le_sup_left : I₁ ≤ I₁ ⊔ I₂) x₁ = Ideal.Quotient.factor (le_sup_right : I₂ ≤ I₁ ⊔ I₂) x₂ →
      ∃ a : A, Ideal.Quotient.mk I₁ a = x₁ ∧ Ideal.Quotient.mk I₂ a = x₂ := by p2m_exact_reverting @_root_.P2MW.S_Ideal_injective_quotient_mk_prod_and_exists_of_factor_eq_of_inf_eq_bot.solution
