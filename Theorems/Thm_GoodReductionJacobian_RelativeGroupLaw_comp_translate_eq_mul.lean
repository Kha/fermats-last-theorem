import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_comp_translate_eq_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.comp_translate_eq_mul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    z.1 ≫ L.translate x = (L.mul t z (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) x)).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_translate_eq_mul.solution
