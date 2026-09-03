import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (n : ℕ) (c : Fin n → S) (hc : Ideal.span (Set.range c) = ⊤)
    (L : Fin n → Type u) [∀ i, CommRing (L i)] [∀ i, Algebra S (L i)] [∀ i, IsLocalization.Away (c i) (L i)]
    (L₂ : Fin n → Fin n → Type u) [∀ i j, CommRing (L₂ i j)] [∀ i j, Algebra S (L₂ i j)]
    [∀ i j, IsLocalization.Away (c i * c j) (L₂ i j)]
    (l : ∀ i j, L i →+* L₂ i j) (r : ∀ i j, L j →+* L₂ i j)
    (hl : ∀ i j, (l i j).comp (algebraMap S (L i)) = algebraMap S (L₂ i j))
    (hr : ∀ i j, (r i j).comp (algebraMap S (L j)) = algebraMap S (L₂ i j)) :
    (∀ s s' : Spec (CommRingCat.of S) ⟶ A, s ≫ f = 𝟙 _ → s' ≫ f = 𝟙 _ →
        (∀ i, Spec.map (CommRingCat.ofHom (algebraMap S (L i))) ≫ s =
          Spec.map (CommRingCat.ofHom (algebraMap S (L i))) ≫ s') → s = s') ∧
    (∀ s : ∀ i, Spec (CommRingCat.of (L i)) ⟶ A,
        (∀ i, s i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S (L i)))) →
        (∀ i j, Spec.map (CommRingCat.ofHom (l i j)) ≫ s i = Spec.map (CommRingCat.ofHom (r i j)) ≫ s j) →
        ∃ sec : Spec (CommRingCat.of S) ⟶ A, sec ≫ f = 𝟙 _ ∧
          ∀ i, Spec.map (CommRingCat.ofHom (algebraMap S (L i))) ≫ sec = s i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top.solution
