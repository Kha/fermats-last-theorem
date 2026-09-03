import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isReduced_of_isClosedImmersion_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_of_isReduced_of_isClosedImmersion_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType g] (L : RelativeGroupLaw k g)
    {Z : Scheme.{u}} {z : Z ⟶ Spec (CommRingCat.of k)} (ι : SchemeHomOver z g)
    [IsClosedImmersion ι.1] [IsReduced Z]
    (hone : ∃ o : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
      NeronModelInfra.schemeHomOverComp o ι = L.one (𝟙 (Spec (CommRingCat.of k))))
    (hmul : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
      ∃ w : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
        NeronModelInfra.schemeHomOverComp w ι =
          L.mul (𝟙 (Spec (CommRingCat.of k))) (NeronModelInfra.schemeHomOverComp x ι)
            (NeronModelInfra.schemeHomOverComp y ι))
    (hinv : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
      ∃ w : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
        NeronModelInfra.schemeHomOverComp w ι =
          L.inv (𝟙 (Spec (CommRingCat.of k))) (NeronModelInfra.schemeHomOverComp x ι)) :
    ∃ LZ : RelativeGroupLaw k z,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t z),
        NeronModelInfra.schemeHomOverComp (LZ.mul t x y) ι =
          L.mul t (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isReduced_of_isClosedImmersion_of_isAlgClosed.solution
