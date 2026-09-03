import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_finiteFlat_model_prod

open scoped TensorProduct

theorem HopfAlgebra.exists_finiteFlat_model_prod
    {R : Type} [CommRing R] {L : Type} [CommRing L] [Algebra R L]
    {Γ : Type} [Group Γ] [MulSemiringAction Γ L] [SMulCommClass Γ R L]
    {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [DistribMulAction Γ M₁] [DistribMulAction Γ M₂]
    (H₁ : Type) [CommRing H₁] [HopfAlgebra R H₁] [Module.Finite R H₁] [Module.Flat R H₁]
    [Coalgebra.IsCocomm R H₁]
    (e₁ : WithConv (H₁ →ₐ[R] L) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : Γ) (f g : WithConv (H₁ →ₐ[R] L)), (∀ x : H₁, g x = σ • (f x)) → e₁ g = σ • (e₁ f))
    (H₂ : Type) [CommRing H₂] [HopfAlgebra R H₂] [Module.Finite R H₂] [Module.Flat R H₂]
    [Coalgebra.IsCocomm R H₂]
    (e₂ : WithConv (H₂ →ₐ[R] L) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : Γ) (f g : WithConv (H₂ →ₐ[R] L)), (∀ x : H₂, g x = σ • (f x)) → e₂ g = σ • (e₂ f)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e : WithConv (H →ₐ[R] L) ≃ M₁ × M₂,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : Γ) (f g : WithConv (H →ₐ[R] L)), (∀ x : H, g x = σ • (f x)) → e g = σ • (e f) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_model_prod.solution
