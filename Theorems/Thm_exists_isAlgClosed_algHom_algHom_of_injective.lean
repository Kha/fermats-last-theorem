import Mathlib
import P2M.Util
import P2M.Sol.S_exists_isAlgClosed_algHom_algHom_of_injective

set_option autoImplicit false

theorem exists_isAlgClosed_algHom_algHom_of_injective
    (D : Type) [CommRing D] [IsDomain D]
    (E₁ E₂ : Type) [Field E₁] [Field E₂] [Algebra D E₁] [Algebra D E₂]
    (h₁ : Function.Injective (algebraMap D E₁)) (h₂ : Function.Injective (algebraMap D E₂)) :
    ∃ (Ω' : Type) (_ : Field Ω') (_ : IsAlgClosed Ω') (_ : Algebra D Ω'),
      Nonempty (E₁ →ₐ[D] Ω') ∧ Nonempty (E₂ →ₐ[D] Ω') := by p2m_exact_reverting @_root_.P2MW.S_exists_isAlgClosed_algHom_algHom_of_injective.solution
