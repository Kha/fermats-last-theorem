import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_exists_comp_eq_and_ker_eq_of_isIntegral_of_isAlgClosed

set_option autoImplicit false

theorem RingHom.exists_comp_eq_and_ker_eq_of_isIntegral_of_isAlgClosed
    {B₁ B Ω : Type*} [CommRing B₁] [CommRing B] [Field Ω] [IsAlgClosed Ω]
    (f : B₁ →+* B) (hf : f.IsIntegral)
    (φ₁ : B₁ →+* Ω) (y : Ideal B) [y.IsPrime]
    (hy : y.comap f = RingHom.ker φ₁) :
    ∃ φ : B →+* Ω, φ.comp f = φ₁ ∧ RingHom.ker φ = y := by p2m_exact_reverting @_root_.P2MW.S_RingHom_exists_comp_eq_and_ker_eq_of_isIntegral_of_isAlgClosed.solution
