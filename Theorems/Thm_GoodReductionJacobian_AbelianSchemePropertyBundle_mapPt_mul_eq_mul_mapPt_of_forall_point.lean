import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_mapPt_mul_eq_mul_mapPt_of_forall_point

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry~ext_of_forall_comp_eq_of_isAlgClosed NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM"

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.mapPt_mul_eq_mul_mapPt_of_forall_point
    (k : Type) [Field k] [IsAlgClosed k]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (hA : AbelianSchemePropertyBundle k f)
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of k)) (L' : RelativeGroupLaw k f')
    (hA' : AbelianSchemePropertyBundle k f')
    (u : A ⟶ A') (hu : u ≫ f' = f)
    (h1 : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      mapPt u hu (L.mul (𝟙 (Spec (CommRingCat.of k))) P Q) =
        L'.mul (𝟙 (Spec (CommRingCat.of k))) (mapPt u hu P) (mapPt u hu Q))
    {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver s f) :
    mapPt u hu (L.mul s P Q) = L'.mul s (mapPt u hu P) (mapPt u hu Q) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_mapPt_mul_eq_mul_mapPt_of_forall_point.solution
