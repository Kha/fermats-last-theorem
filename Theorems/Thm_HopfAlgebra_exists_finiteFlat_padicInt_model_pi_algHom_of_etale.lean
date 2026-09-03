import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_finiteFlat_padicInt_model_pi_algHom_of_etale

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_finiteFlat_padicInt_model_pi_algHom_of_etale
    (p : ℕ) [Fact p.Prime]
    (G : Type) [CommRing G] [HopfAlgebra ℤ_[p] G] [Module.Finite ℤ_[p] G] [Module.Flat ℤ_[p] G]
    [Coalgebra.IsCocomm ℤ_[p] G]
    {M : Type} [AddCommGroup M] [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M]
    (e : WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
    (B : Type) [CommRing B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] [Module.Free ℤ_[p] B]
    [Algebra.Etale ℤ_[p] B] :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e' : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ((B →ₐ[ℤ_[p]] PadicAlgCl p) → M),
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ x : H, g x = σ (f x)) →
            ∀ τ : B →ₐ[ℤ_[p]] PadicAlgCl p,
              e' g (((σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).restrictScalars ℤ_[p]).comp τ) = σ • (e' f τ) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_padicInt_model_pi_algHom_of_etale.solution
