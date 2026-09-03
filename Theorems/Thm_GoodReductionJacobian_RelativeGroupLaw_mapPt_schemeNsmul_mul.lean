import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_mapPt_schemeNsmul_mul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.mapPt_schemeNsmul_mul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (m : ℕ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    CerednikDrinfeld.QM.mapPt (L.schemeNsmul m) (L.schemeNsmul_over m) (L.mul t P Q) =
      L.mul t (CerednikDrinfeld.QM.mapPt (L.schemeNsmul m) (L.schemeNsmul_over m) P)
        (CerednikDrinfeld.QM.mapPt (L.schemeNsmul m) (L.schemeNsmul_over m) Q) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_mapPt_schemeNsmul_mul.solution
