import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_bijective_of_level_one

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_bijective_of_level_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (k : Type) [Field k] (S : Type) [CommRing S] (ρ : S →+* k) (hρ : Function.Bijective ρ)
    (E₀ : FakeEllipticCurve Λ 1 k)
    (E : FakeEllipticCurve Λ 1 S) (g : E₀.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia ρ E E₀ g)
    (E' : FakeEllipticCurve Λ 1 S) (g' : E₀.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia ρ E' E₀ g') :
    ∃ h : E.A ⟶ E'.A, FakeEllipticCurve.IsPullbackVia (RingHom.id S) E' E h ∧ g ≫ h = g' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_bijective_of_level_one.solution
