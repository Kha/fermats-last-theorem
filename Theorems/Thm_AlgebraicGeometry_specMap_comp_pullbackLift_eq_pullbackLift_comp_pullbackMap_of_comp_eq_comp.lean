import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp
    {G S : Scheme.{u}} (g : G ⟶ S)
    {k L A : Type u} [CommRing k] [CommRing L] [CommRing A]
    (s : Spec (CommRingCat.of k) ⟶ S)
    (ι : Spec (CommRingCat.of L) ⟶ G)
    (E : G ⟶ G) (hE : E ≫ g = g)
    (e : L →+* L) (hι : Spec.map (CommRingCat.ofHom e) ≫ ι = ι ≫ E)
    (a : L →+* A) (c : k →+* A)
    (hsq : (Spec.map (CommRingCat.ofHom a) ≫ ι) ≫ g = Spec.map (CommRingCat.ofHom c) ≫ s)
    (eA : A →+* A) (hea : eA.comp a = a.comp e) (hec : eA.comp c = c) :
    Spec.map (CommRingCat.ofHom eA) ≫ pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq =
      pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq ≫
        pullback.map g s g s E (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact hE.symm) (by rw [Category.comp_id, Category.id_comp]) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp.solution
