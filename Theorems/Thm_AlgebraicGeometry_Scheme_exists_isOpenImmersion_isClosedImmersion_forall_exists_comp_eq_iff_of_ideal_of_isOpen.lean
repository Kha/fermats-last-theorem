import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_forall_exists_comp_eq_iff_of_ideal_of_isOpen

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_isOpenImmersion_isClosedImmersion_forall_exists_comp_eq_iff_of_ideal_of_isOpen
    (E : Scheme.{u})
    (I₁ : ∀ (R : Type u) [CommRing R], (Spec (CommRingCat.of R) ⟶ E) → Ideal R)
    (hI₁ : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R) ⟶ E),
      I₁ R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = (I₁ R s).map ψ)
    (U₂ : ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E), I₁ R s = ⊥ → Set ↥(Spec (CommRingCat.of R)))
    (hU₂open : ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E) (h₁ : I₁ R s = ⊥), IsOpen (U₂ R s h₁))
    (hU₂ : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R) ⟶ E)
      (h₁ : I₁ R s = ⊥) (h₁' : I₁ R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = ⊥),
      U₂ R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) h₁' = (Spec.map (CommRingCat.ofHom ψ)).base ⁻¹' (U₂ R s h₁))
    (I₃ : ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E) (h₁ : I₁ R s = ⊥),
      U₂ R s h₁ = Set.univ → Ideal R)
    (hI₃ : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R) ⟶ E)
      (h₁ : I₁ R s = ⊥) (h₂ : U₂ R s h₁ = Set.univ)
      (h₁' : I₁ R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = ⊥) (h₂' : U₂ R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) h₁' = Set.univ),
      I₃ R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) h₁' h₂' = (I₃ R s h₁ h₂).map ψ)
    (U₄ : ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E) (h₁ : I₁ R s = ⊥) (h₂ : U₂ R s h₁ = Set.univ),
      I₃ R s h₁ h₂ = ⊥ → Set ↥(Spec (CommRingCat.of R)))
    (hU₄open : ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E) (h₁ : I₁ R s = ⊥) (h₂ : U₂ R s h₁ = Set.univ)
      (h₃ : I₃ R s h₁ h₂ = ⊥), IsOpen (U₄ R s h₁ h₂ h₃))
    (hU₄ : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R) ⟶ E)
      (h₁ : I₁ R s = ⊥) (h₂ : U₂ R s h₁ = Set.univ) (h₃ : I₃ R s h₁ h₂ = ⊥)
      (h₁' : I₁ R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = ⊥) (h₂' : U₂ R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) h₁' = Set.univ)
      (h₃' : I₃ R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) h₁' h₂' = ⊥),
      U₄ R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) h₁' h₂' h₃' = (Spec.map (CommRingCat.ofHom ψ)).base ⁻¹' (U₄ R s h₁ h₂ h₃)) :
    ∃ (H C₂ V₁ C₁ : Scheme.{u}) (j₄ : H ⟶ C₂) (j₃ : C₂ ⟶ V₁) (j₂ : V₁ ⟶ C₁) (j₁ : C₁ ⟶ E),
      IsOpenImmersion j₄ ∧ IsClosedImmersion j₃ ∧ IsOpenImmersion j₂ ∧ IsClosedImmersion j₁ ∧
      ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E),
        (∃ h : Spec (CommRingCat.of R) ⟶ H, h ≫ j₄ ≫ j₃ ≫ j₂ ≫ j₁ = s) ↔
          ∃ (h₁ : I₁ R s = ⊥) (h₂ : U₂ R s h₁ = Set.univ) (h₃ : I₃ R s h₁ h₂ = ⊥), U₄ R s h₁ h₂ h₃ = Set.univ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_forall_exists_comp_eq_iff_of_ideal_of_isOpen.solution
