import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_mulRight_id_eq_fst_comp_translate

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.mulRight_id_eq_fst_comp_translate
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    L.mulRight (𝟙 (Spec (CommRingCat.of R))) x = pullback.fst f (𝟙 (Spec (CommRingCat.of R))) ≫ L.translate x := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_mulRight_id_eq_fst_comp_translate.solution
