import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_apply_trace_linearPart_addVia_eq_of_isFormalModuleVia

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.apply_trace_linearPart_addVia_eq_of_isFormalModuleVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (B : Type) [CommRing B]
    (E : FakeEllipticCurve Λ N B) (X : FormalODModule q B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hX : E.IsFormalModuleVia coord X θ)
    (k : Type) [Field k] [IsAlgClosed k] (sk : B →+* k)
    (m : ↥Λ) (n : ℤ) (hm : (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) :
    sk (Matrix.trace (MvFormalGroup.linearPart
        (Series.addVia X.F (X.act (coord m).1) ((X.act (coord m).2).comp X.varpi)))) = (n : k) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_apply_trace_linearPart_addVia_eq_of_isFormalModuleVia.solution
