import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_exists_algEquiv_comp_eq_of_ker_eq_of_forall_exists_mul_eq

set_option autoImplicit false

theorem RingHom.exists_algEquiv_comp_eq_of_ker_eq_of_forall_exists_mul_eq
    {κ B K₁ K₂ : Type} [Field κ] [CommRing B] [Field K₁] [Field K₂] [Algebra κ K₁] [Algebra κ K₂]
    (r₁ : B →+* K₁) (r₂ : B →+* K₂) (hker : RingHom.ker r₁ = RingHom.ker r₂)
    (hfrac₁ : ∀ x : K₁, ∃ g h : B, r₁ h ≠ 0 ∧ x * r₁ h = r₁ g)
    (hfrac₂ : ∀ x : K₂, ∃ g h : B, r₂ h ≠ 0 ∧ x * r₂ h = r₂ g)

    {C : Type} (c : C → B) (cκ : C → κ) (hcκ : Function.Surjective cκ)
    (hc₁ : ∀ t : C, r₁ (c t) = algebraMap κ K₁ (cκ t)) (hc₂ : ∀ t : C, r₂ (c t) = algebraMap κ K₂ (cκ t)) :
    ∃ e : K₁ ≃ₐ[κ] K₂, ∀ b : B, e (r₁ b) = r₂ b := by p2m_exact_reverting @_root_.P2MW.S_RingHom_exists_algEquiv_comp_eq_of_ker_eq_of_forall_exists_mul_eq.solution
