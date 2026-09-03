import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_nonempty_algEquiv_of_forall_isArtinianRing_algHom_equiv

set_option autoImplicit false

universe u v

open IsLocalRing

theorem IsLocalRing.nonempty_algEquiv_of_forall_isArtinianRing_algHom_equiv
    {Λ : Type u} [CommRing Λ]
    (R₁ : Type v) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [IsAdicComplete (maximalIdeal R₁) R₁] [Algebra Λ R₁]
    (R₂ : Type v) [CommRing R₂] [IsLocalRing R₂] [IsNoetherianRing R₂] [IsAdicComplete (maximalIdeal R₂) R₂] [Algebra Λ R₂]
    (h₁ : Function.Surjective (⇑(residue R₁) ∘ ⇑(algebraMap Λ R₁)))
    (h₂ : Function.Surjective (⇑(residue R₂) ∘ ⇑(algebraMap Λ R₂)))
    (η : ∀ (T : Type v) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra Λ T],
      Function.Surjective (⇑(residue T) ∘ ⇑(algebraMap Λ T)) → ((R₁ →ₐ[Λ] T) ≃ (R₂ →ₐ[Λ] T)))
    (hη : ∀ (T : Type v) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra Λ T]
      (hT : Function.Surjective (⇑(residue T) ∘ ⇑(algebraMap Λ T)))
      (T' : Type v) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [Algebra Λ T']
      (hT' : Function.Surjective (⇑(residue T') ∘ ⇑(algebraMap Λ T')))
      (f : T →ₐ[Λ] T') (g : R₁ →ₐ[Λ] T), η T' hT' (f.comp g) = f.comp (η T hT g)) :
    Nonempty (R₁ ≃ₐ[Λ] R₂) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_nonempty_algEquiv_of_forall_isArtinianRing_algHom_equiv.solution
