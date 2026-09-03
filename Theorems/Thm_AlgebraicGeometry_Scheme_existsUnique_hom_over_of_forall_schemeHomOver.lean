import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_existsUnique_hom_over_of_forall_schemeHomOver

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem AlgebraicGeometry.Scheme.existsUnique_hom_over_of_forall_schemeHomOver
    {R : Type u} [CommRing R] {Z₁ Z₂ : Scheme.{u}}
    (ζ₁ : Z₁ ⟶ Spec (CommRingCat.of R)) (ζ₂ : Z₂ ⟶ Spec (CommRingCat.of R))
    (e : ∀ (T : Type u) [CommRing T] (φ : R →+* T),
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁ → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₂)
    (he : ∀ (T T' : Type u) [CommRing T] [CommRing T'] (φ : R →+* T) (ψ : T →+* T')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁),
      (e T' (ψ.comp φ) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, by
          rw [Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩).1 =
        Spec.map (CommRingCat.ofHom ψ) ≫ (e T φ x).1) :
    ∃ ε : Z₁ ⟶ Z₂, ε ≫ ζ₂ = ζ₁ ∧
      (∀ (T : Type u) [CommRing T] (φ : R →+* T) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁),
        x.1 ≫ ε = (e T φ x).1) ∧
      ∀ ε' : Z₁ ⟶ Z₂, (∀ (T : Type u) [CommRing T] (φ : R →+* T) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁),
        x.1 ≫ ε' = (e T φ x).1) → ε' = ε := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_existsUnique_hom_over_of_forall_schemeHomOver.solution
