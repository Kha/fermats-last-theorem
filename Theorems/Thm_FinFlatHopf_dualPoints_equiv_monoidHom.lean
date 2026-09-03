import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_FinFlatHopf_dualPoints_equiv_monoidHom

set_option autoImplicit false
set_option Elab.async false

theorem FinFlatHopf.dualPoints_equiv_monoidHom
    (B : Type) [CommRing B] (H : Type) [CommRing H] [HopfAlgebra B H]
    [Coalgebra.IsCocomm B H] [Module.Finite B H] [Module.Free B H]
    (Ω : Type) [Field Ω] [Algebra B Ω]
    (hcard : Nat.card (WithConv (H →ₐ[B] Ω)) = Module.finrank B H) :
    ∃ e : WithConv (CartierDual B H →ₐ[B] Ω) ≃* (WithConv (H →ₐ[B] Ω) →* Ωˣ),
      (∀ (g : WithConv (CartierDual B H →ₐ[B] Ω)) (f : WithConv (H →ₐ[B] Ω)),
        ((e g f : Ωˣ) : Ω) =
          Algebra.TensorProduct.productMap (WithConv.ofConv g) (AlgHom.id B Ω)
            ((TensorProduct.congr (CartierDual.ofDual B H) (LinearEquiv.refl B Ω))
              ((dualTensorHomEquiv B H Ω).symm (WithConv.ofConv f).toLinearMap))) ∧
      (∀ (τ : Ω ≃ₐ[B] Ω) (g : WithConv (CartierDual B H →ₐ[B] Ω))
          (f : WithConv (H →ₐ[B] Ω)),
        ((e (WithConv.toConv (τ.toAlgHom.comp (WithConv.ofConv g))) f : Ωˣ) : Ω) =
          τ ((e g (WithConv.toConv (τ.symm.toAlgHom.comp (WithConv.ofConv f))) : Ωˣ) : Ω)) := by p2m_exact_reverting @_root_.P2MW.S_FinFlatHopf_dualPoints_equiv_monoidHom.solution
