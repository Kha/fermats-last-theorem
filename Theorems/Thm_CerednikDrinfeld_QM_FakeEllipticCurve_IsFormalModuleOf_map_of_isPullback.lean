import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_map_of_isPullback

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.IsFormalModuleOf.map_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q)
    {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B')
    (E : FakeEllipticCurve Λ N B) (E' : FakeEllipticCurve Λ N B') (hE : FakeEllipticCurve.IsPullback φ E E')
    (X : FormalODModule q B) (hX : E.IsFormalModuleOf coord X) :
    E'.IsFormalModuleOf coord (X.map φ) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_map_of_isPullback.solution
