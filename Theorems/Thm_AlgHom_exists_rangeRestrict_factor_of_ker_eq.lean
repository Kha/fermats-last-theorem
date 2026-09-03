import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_exists_rangeRestrict_factor_of_ker_eq

set_option autoImplicit false

theorem AlgHom.exists_rangeRestrict_factor_of_ker_eq
    {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [CommRing K] [Algebra A K]
    (φ₁ φ₂ : B →ₐ[A] K) (h : RingHom.ker φ₁.toRingHom = RingHom.ker φ₂.toRingHom) :
    ∃ (ψ : B →ₐ[A] ↥φ₁.range) (κ₂ : ↥φ₁.range →ₐ[A] K),
      Function.Surjective ψ ∧ Function.Injective κ₂ ∧
      (∀ b : B, ((ψ b : ↥φ₁.range) : K) = φ₁ b) ∧ (∀ b : B, κ₂ (ψ b) = φ₂ b) := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_exists_rangeRestrict_factor_of_ker_eq.solution
