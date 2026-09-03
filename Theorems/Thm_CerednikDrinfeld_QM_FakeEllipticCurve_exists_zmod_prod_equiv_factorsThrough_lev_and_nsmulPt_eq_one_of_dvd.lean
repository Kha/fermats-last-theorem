import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_lev_and_nsmulPt_eq_one_of_dvd

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_lev_and_nsmulPt_eq_one_of_dvd
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {M : ℕ}
    (S : Type) [CommRing S] (E : FakeEllipticCurve Λ M S) (n : ℕ) (hn : n ∣ M)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (hk : (M : k) ≠ 0) :
    ∃ e : ZMod n × ZMod n ≃
        {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough E.lev P ∧ nsmulPt E.L (geomPoint k sk) n P = E.L.one (geomPoint k sk)},
      ∀ x y : ZMod n × ZMod n,
        (e (x + y) : SchemeHomOver (geomPoint k sk) E.f) = E.L.mul (geomPoint k sk) (e x) (e y) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_lev_and_nsmulPt_eq_one_of_dvd.solution
