import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R')
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) (f' : A' ⟶ Spec (CommRingCat.of R'))
    (π : A' ⟶ A) (hP : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (G : RelativeGroupLaw R f) :
    ∃ G' : RelativeGroupLaw R' f',
      (∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver s f'),
        (G'.mul s x y).1 ≫ π =
          (G.mul (s ≫ Spec.map (CommRingCat.ofHom g))
            ⟨x.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, y.2]⟩).1) ∧
      (∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R')),
        (G'.one s).1 ≫ π = (G.one (s ≫ Spec.map (CommRingCat.ofHom g))).1) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback.solution
