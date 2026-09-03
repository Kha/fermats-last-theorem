import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_charZero

theorem HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_charZero
    (K : Type) [Field K] [CharZero K] (Kbar : Type) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
    {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂]
    [DistribMulAction (Kbar ≃ₐ[K] Kbar) M₁] [DistribMulAction (Kbar ≃ₐ[K] Kbar) M₂]
    (E₁ : Type) [CommRing E₁] [HopfAlgebra K E₁] [Module.Finite K E₁]
    (e₁ : WithConv (E₁ →ₐ[K] Kbar) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : Kbar ≃ₐ[K] Kbar) (f g : WithConv (E₁ →ₐ[K] Kbar)),
      (∀ x : E₁, g x = σ (f x)) → e₁ g = σ • (e₁ f))
    (E₂ : Type) [CommRing E₂] [HopfAlgebra K E₂] [Module.Finite K E₂]
    (e₂ : WithConv (E₂ →ₐ[K] Kbar) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : Kbar ≃ₐ[K] Kbar) (f g : WithConv (E₂ →ₐ[K] Kbar)),
      (∀ x : E₂, g x = σ (f x)) → e₂ g = σ • (e₂ f))
    (φ : M₁ →+ M₂)
    (hφ : ∀ (σ : Kbar ≃ₐ[K] Kbar) (m : M₁), φ (σ • m) = σ • φ m) :
    ∃! ψ : E₂ →ₐc[K] E₁,
      ∀ f : WithConv (E₁ →ₐ[K] Kbar),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (ψ : E₂ →ₐ[K] E₁))) = φ (e₁ f) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_charZero.solution
