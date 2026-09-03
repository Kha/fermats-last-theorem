import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_isReduced_C_of_natCast_ne_zero

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion
open CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isReduced_C_of_natCast_ne_zero
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k) (hNk : (N : k) ≠ 0) :
    IsReduced E.C := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isReduced_C_of_natCast_ne_zero.solution
