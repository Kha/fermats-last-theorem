import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_lift_one_comp_translate_comp_fst

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.Polarisation.lift_one_comp_translate_comp_fst
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) :
    pullback.lift (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (𝟙 (Spec (CommRingCat.of S))) (by rw [(L.one _).2, Category.comp_id]) ≫
        Polarisation.translate f L (𝟙 (Spec (CommRingCat.of S))) x ≫ pullback.fst f (𝟙 (Spec (CommRingCat.of S))) = x.1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_lift_one_comp_translate_comp_fst.solution
