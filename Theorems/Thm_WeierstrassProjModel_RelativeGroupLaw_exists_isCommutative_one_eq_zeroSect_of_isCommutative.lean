import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_exists_isCommutative_one_eq_zeroSect_of_isCommutative

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u
theorem WeierstrassProjModel.RelativeGroupLaw.exists_isCommutative_one_eq_zeroSect_of_isCommutative
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    (G₁ : RelativeGroupLaw R (projModelStrCR V))
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (x y : SchemeHomOver t (projModelStrCR V)), G₁.mul t x y = G₁.mul t y x) :
    ∃ G₀ : RelativeGroupLaw R (projModelStrCR V),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t (projModelStrCR V)), G₀.mul t x y = G₀.mul t y x)
      ∧ (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
          (G₀.one t).1 = t ≫ (kwZeroSect R V.toAffine).1) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_isCommutative_one_eq_zeroSect_of_isCommutative.solution
