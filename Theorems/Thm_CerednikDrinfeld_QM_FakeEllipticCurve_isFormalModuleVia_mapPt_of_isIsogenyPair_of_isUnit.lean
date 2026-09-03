import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_isFormalModuleVia_mapPt_of_isIsogenyPair_of_isUnit

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isFormalModuleVia_mapPt_of_isIsogenyPair_of_isUnit
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {B : Type} [CommRing B]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (E E' : FakeEllipticCurve Λ N B)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hE : E.IsFormalModuleVia coord X θ)
    (X' : FormalODModule r B) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2) (hE' : E'.IsFormalModuleVia coord X' θ')
    (D : ℕ) (hD : IsUnit ((D : ℕ) : Zp2 r)) (hDΛ : ((D : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f) (q' : E'.A ⟶ E.A) (hq' : q' ≫ E.f = E'.f)
    (hqq' : FakeEllipticCurve.IsIsogenyPair D E E' q q') :
    E'.IsFormalModuleVia coord X (fun (B' : Type) _ _ (s : Fin 2 → B') => mapPt q hq (θ B' s)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isFormalModuleVia_mapPt_of_isIsogenyPair_of_isUnit.solution
