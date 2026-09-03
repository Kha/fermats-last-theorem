import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_factorsThrough_lev_nsmulPt_eq_one_eq_sq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.natCard_factorsThrough_lev_nsmulPt_eq_one_eq_sq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {L : Type u} [CommRing L] (E : FakeEllipticCurve Λ N L)
    (k : Type u) [Field k] [IsAlgClosed k] (sk : L →+* k) (hN : (N : k) ≠ 0) (d : ℕ) (hd : d ∣ N) :
    Nat.card {P : SchemeHomOver (geomPoint k sk) E.f //
      FactorsThrough E.lev P ∧ nsmulPt E.L (geomPoint k sk) d P = E.L.one (geomPoint k sk)} = d ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_factorsThrough_lev_nsmulPt_eq_one_eq_sq.solution
