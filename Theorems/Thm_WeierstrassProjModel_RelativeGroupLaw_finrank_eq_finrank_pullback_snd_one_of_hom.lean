import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.RelativeGroupLaw.finrank_eq_finrank_pullback_snd_one_of_hom
    {R : Type} [CommRing R] {A B : Scheme}
    {fA : A ⟶ Spec (CommRingCat.of R)} {fB : B ⟶ Spec (CommRingCat.of R)}
    (LA : RelativeGroupLaw R fA) (LB : RelativeGroupLaw R fB)
    (p : A ⟶ B) (hp : p ≫ fB = fA)
    (p_hom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t fA),
      (⟨(LA.mul t x y).1 ≫ p, by rw [Category.assoc, hp]; exact (LA.mul t x y).2⟩ : SchemeHomOver t fB) =
        LB.mul t ⟨x.1 ≫ p, by rw [Category.assoc, hp]; exact x.2⟩ ⟨y.1 ≫ p, by rw [Category.assoc, hp]; exact y.2⟩)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p] (b : B) :
    p.finrank b = (pullback.snd p (LB.one (𝟙 _)).1).finrank (fB.base b) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom.solution
