import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_exists_bialgHom_coe_eq_of_comp_convMul

set_option autoImplicit false

universe u v

open IsLocalRing

theorem Bialgebra.exists_bialgHom_coe_eq_of_comp_convMul
    {R : Type u} [CommRing R] {H B : Type u} [CommRing H] [Bialgebra R H] [CommRing B] [Bialgebra R B]
    (ψ : H →ₐ[R] B)
    (hmul : ∀ (T : Type u) [CommRing T] [Algebra R T] (χ χ' : WithConv (B →ₐ[R] T)),
      WithConv.toConv ((χ * χ').ofConv.comp ψ) = WithConv.toConv (χ.ofConv.comp ψ) * WithConv.toConv (χ'.ofConv.comp ψ))
    (hone : ∀ (T : Type u) [CommRing T] [Algebra R T],
      WithConv.toConv ((1 : WithConv (B →ₐ[R] T)).ofConv.comp ψ) = (1 : WithConv (H →ₐ[R] T))) :
    ∃ ψ' : H →ₐc[R] B, (ψ' : H →ₐ[R] B) = ψ := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_exists_bialgHom_coe_eq_of_comp_convMul.solution
