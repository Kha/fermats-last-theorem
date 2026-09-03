import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Spec_exists_forall_map_comp_eq_of_functorial_family_of_span_eq_top

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Spec.exists_forall_map_comp_eq_of_functorial_family_of_span_eq_top
    {S : Type} [CommRing S] {Y : Scheme.{0}}

    (adm : ∀ (S' : Type) [CommRing S'], (S →+* S') → Prop)
    (hadm : ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S →+* S') (χ : S' →+* S''),
      adm S' ψ → adm S'' (χ.comp ψ))

    (z : ∀ (S' : Type) [CommRing S'] (ψ : S →+* S'), adm S' ψ → (Spec (CommRingCat.of S') ⟶ Y))
    (hz : ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S →+* S') (hψ : adm S' ψ) (χ : S' →+* S'')
      (hχ : adm S'' (χ.comp ψ)), z S'' (χ.comp ψ) hχ = Spec.map (CommRingCat.ofHom χ) ≫ z S' ψ hψ)

    (R : Set S) (hR : Ideal.span R = ⊤)
    (hcov : ∀ r ∈ R, adm (Localization.Away r) (algebraMap S (Localization.Away r))) :
    ∃ q : Spec (CommRingCat.of S) ⟶ Y,
      (∀ (S' : Type) [CommRing S'] (ψ : S →+* S') (hψ : adm S' ψ), Spec.map (CommRingCat.ofHom ψ) ≫ q = z S' ψ hψ) ∧
      ∀ q' : Spec (CommRingCat.of S) ⟶ Y,
        (∀ r (hr : r ∈ R), Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))) ≫ q' =
          z (Localization.Away r) (algebraMap S (Localization.Away r)) (hcov r hr)) → q' = q := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Spec_exists_forall_map_comp_eq_of_functorial_family_of_span_eq_top.solution
