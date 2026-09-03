import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_mapPt_negMor_mul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.Polarisation.mapPt_negMor_mul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    CerednikDrinfeld.QM.mapPt (Polarisation.negMor f L) (Polarisation.negMor_over f L) (L.mul t P Q) =
      L.mul t (CerednikDrinfeld.QM.mapPt (Polarisation.negMor f L) (Polarisation.negMor_over f L) P)
        (CerednikDrinfeld.QM.mapPt (Polarisation.negMor f L) (Polarisation.negMor_over f L) Q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_mapPt_negMor_mul.solution
