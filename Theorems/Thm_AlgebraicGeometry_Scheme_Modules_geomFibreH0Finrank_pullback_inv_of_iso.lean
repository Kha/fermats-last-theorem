import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pullback_inv_of_iso

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_pullback_inv_of_iso
    {S : Type u} [CommRing S] {A A' : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of S)) (f' : A' ⟶ Spec (CommRingCat.of S))
    (e : A ≅ A') (he : e.hom ≫ f' = f) (M : A.Modules)
    (k : Type u) [Field k] (sk : S →+* k) :
    Scheme.Modules.geomFibreH0Finrank f' ((Scheme.Modules.pullback e.inv).obj M) k sk =
      Scheme.Modules.geomFibreH0Finrank f M k sk := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pullback_inv_of_iso.solution
