import Mathlib
import P2M.Util
import P2M.Sol.S_BialgHom_exists_comp_eq_of_natural_of_map_mul

set_option autoImplicit false

universe u v

theorem BialgHom.exists_comp_eq_of_natural_of_map_mul
    {R : Type u} [CommRing R] {H₁ H₂ : Type v} [CommRing H₁] [Bialgebra R H₁] [CommRing H₂] [Bialgebra R H₂]
    (η : ∀ (T : Type v) [CommRing T] [Algebra R T], WithConv (H₁ →ₐ[R] T) → WithConv (H₂ →ₐ[R] T))
    (hη : ∀ (T T' : Type v) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T'] (g : T →ₐ[R] T')
      (φ : WithConv (H₁ →ₐ[R] T)),
      WithConv.ofConv (η T' (WithConv.toConv (g.comp (WithConv.ofConv φ)))) = g.comp (WithConv.ofConv (η T φ)))
    (hmul : ∀ (T : Type v) [CommRing T] [Algebra R T] (φ ψ : WithConv (H₁ →ₐ[R] T)), η T (φ * ψ) = η T φ * η T ψ)
    (hone : ∀ (T : Type v) [CommRing T] [Algebra R T], η T 1 = 1) :
    ∃ r : H₂ →ₐc[R] H₁, ∀ (T : Type v) [CommRing T] [Algebra R T] (φ : WithConv (H₁ →ₐ[R] T)),
      WithConv.ofConv (η T φ) = (WithConv.ofConv φ).comp (r : H₂ →ₐ[R] H₁) := by p2m_exact_reverting @_root_.P2MW.S_BialgHom_exists_comp_eq_of_natural_of_map_mul.solution
