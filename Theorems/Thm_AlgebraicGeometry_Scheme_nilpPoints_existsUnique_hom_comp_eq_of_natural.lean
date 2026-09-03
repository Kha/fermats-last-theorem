import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_of_natural

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega

theorem AlgebraicGeometry.Scheme.nilpPoints.existsUnique_hom_comp_eq_of_natural
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of 𝒪)) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B)
    (hu : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
      u B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y))

    (X' : Scheme.{0}) (a : X' ⟶ X) (n : ℕ) (b : X' ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (hb : b ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = a ≫ f) :
    ∃! s : X' ⟶ T, s ≫ t = a ≫ f ∧
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (p : Spec (CommRingCat.of B) ⟶ X')
        (hp : p ≫ a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))),
        p ≫ s = (u B hB ⟨p ≫ a, hp⟩).1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_of_natural.solution
