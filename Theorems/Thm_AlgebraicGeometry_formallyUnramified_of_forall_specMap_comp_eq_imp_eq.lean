import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_formallyUnramified_of_forall_specMap_comp_eq_imp_eq

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.formallyUnramified_of_forall_specMap_comp_eq_imp_eq
    {S : Type u} [CommRing S] {H : Scheme.{u}} (q : H ⟶ Spec (CommRingCat.of S))
    (huniq : ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S''), Function.Surjective ψ →
      RingHom.ker ψ ^ 2 = ⊥ →
      ∀ (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x₁ x₂ : Spec (CommRingCat.of S') ⟶ H),
        x₁ ≫ q = s → x₂ ≫ q = s →
        Spec.map (CommRingCat.ofHom ψ) ≫ x₁ = Spec.map (CommRingCat.ofHom ψ) ≫ x₂ → x₁ = x₂) :
    FormallyUnramified q := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_formallyUnramified_of_forall_specMap_comp_eq_imp_eq.solution
