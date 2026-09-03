import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_equiv_levPoints

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_equiv_levPoints
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type) [Field k] [IsAlgClosed k] (hNk : (N : k) ≠ 0) (E : FakeEllipticCurve Λ N k) :
    ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough E.lev P},
      ∀ x y : ZMod N × ZMod N,
        ((e (x + y) : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough E.lev P}) :
            SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) =
          E.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_equiv_levPoints.solution
