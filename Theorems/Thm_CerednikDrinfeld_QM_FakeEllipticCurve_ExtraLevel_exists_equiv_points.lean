import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_equiv_points

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_equiv_points
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k) (K : E.ExtraLevel ℓ) :
    ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough K.levK P},
      ∀ x y : ZMod ℓ × ZMod ℓ,
        ((e (x + y) : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough K.levK P}) :
            SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) =
          E.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_equiv_points.solution
