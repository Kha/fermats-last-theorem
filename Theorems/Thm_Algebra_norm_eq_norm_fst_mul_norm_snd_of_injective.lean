import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_norm_eq_norm_fst_mul_norm_snd_of_injective

set_option autoImplicit false

theorem Algebra.norm_eq_norm_fst_mul_norm_snd_of_injective
    {A B B₀ B₁ : Type*} [CommRing A] [IsDomain A] [CommRing B] [CommRing B₀] [CommRing B₁]
    [Algebra A B] [Algebra A B₀] [Algebra A B₁]
    [Module.Free A B] [Module.Finite A B] [Module.Free A B₀] [Module.Finite A B₀]
    [Module.Free A B₁] [Module.Finite A B₁]
    (φ : B →ₐ[A] B₀ × B₁) (hφ : Function.Injective φ)
    (hrank : Module.finrank A B = Module.finrank A B₀ + Module.finrank A B₁) (b : B) :
    Algebra.norm A b = Algebra.norm A (φ b).1 * Algebra.norm A (φ b).2 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_norm_eq_norm_fst_mul_norm_snd_of_injective.solution
