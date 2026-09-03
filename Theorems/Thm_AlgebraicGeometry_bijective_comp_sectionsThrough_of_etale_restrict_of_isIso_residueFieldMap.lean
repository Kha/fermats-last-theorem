import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_bijective_comp_sectionsThrough_of_etale_restrict_of_isIso_residueFieldMap

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.bijective_comp_sectionsThrough_of_etale_restrict_of_isIso_residueFieldMap {A : Type u} [CommRing A] [HenselianLocalRing A]
    {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of A)) (fY : Y ⟶ Spec (CommRingCat.of A))
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (x : X)
    (U : X.Opens) (hxU : x ∈ U) [Etale (U.ι ≫ g)]
    (hres : IsIso (g.residueFieldMap x)) :
    Function.Bijective (fun s : {s : Spec (CommRingCat.of A) ⟶ X // s ≫ fX = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint A) = x} =>
      (⟨s.1 ≫ g, ⟨by rw [Category.assoc, hg]; exact s.2.1, by rw [Scheme.Hom.comp_apply, s.2.2]⟩⟩ :
        {t : Spec (CommRingCat.of A) ⟶ Y // t ≫ fY = 𝟙 _ ∧ t.base (IsLocalRing.closedPoint A) = g.base x})) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_bijective_comp_sectionsThrough_of_etale_restrict_of_isIso_residueFieldMap.solution
