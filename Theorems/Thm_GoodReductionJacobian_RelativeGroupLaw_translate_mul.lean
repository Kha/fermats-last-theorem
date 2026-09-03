import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_translate_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.translate_mul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    L.translate (L.mul (𝟙 (Spec (CommRingCat.of R))) x y) = L.translate x ≫ L.translate y := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_translate_mul.solution
