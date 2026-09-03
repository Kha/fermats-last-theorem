import Mathlib
import P2M.Util
import P2M.Sol.S_BialgHom_exists_coe_eq_of_forall_withConv_comp

set_option autoImplicit false

open TensorProduct

universe u

theorem BialgHom.exists_coe_eq_of_forall_withConv_comp
    {R : Type u} [CommRing R] {K : Type u} [CommRing K] [Algebra R K] (hinj : Function.Injective (algebraMap R K))
    {H : Type u} [CommRing H] [Bialgebra R H] {H' : Type u} [CommRing H'] [Bialgebra R H']
    (φ : H →ₐ[R] H')
    (hsep : ∀ x : H' ⊗[R] H', (∀ θ : H' ⊗[R] H' →ₐ[R] K, θ x = 0) → x = 0)
    (hone : (1 : WithConv (H' →ₐ[R] K)).ofConv.comp φ = (1 : WithConv (H →ₐ[R] K)).ofConv)
    (hmul : ∀ χ χ' : WithConv (H' →ₐ[R] K),
      (χ * χ').ofConv.comp φ = (WithConv.toConv (χ.ofConv.comp φ) * WithConv.toConv (χ'.ofConv.comp φ)).ofConv) :
    ∃ ψ : H →ₐc[R] H', (ψ : H →ₐ[R] H') = φ := by p2m_exact_reverting @_root_.P2MW.S_BialgHom_exists_coe_eq_of_forall_withConv_comp.solution
